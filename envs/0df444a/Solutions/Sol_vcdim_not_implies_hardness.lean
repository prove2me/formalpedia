-- Prove2me | solution 1 for vcdim_not_implies_hardness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:57.599854+00:00
-- url     : https://prove2.me/submissions/00945493-cf3c-4717-a66d-414d7a0a25e7

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Extended

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution :
    ∃ (X : Type) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      VCDim X C < ⊤ ∧
      ∃ (D : MeasureTheory.Measure X) (_ : MeasureTheory.IsProbabilityMeasure D)
        (τ : ℝ), 0 < τ ∧ SQDimension X C D τ = ⊤ := by
  -- Witness: X = ℕ, C = singleton indicators {fun x => decide (x = n) | n : ℕ}.
  -- VCDim = 1: shatters any singleton {n}, cannot shatter any pair {n, m}.
  -- SQDimension = ⊤ at τ = 1 for ANY probability D:
  -- Correlation between distinct indicators = |1 - 2(D({i}) + D({j}))| ≤ 1 = τ,
  -- so every finite subfamily has pairwise |corr| ≤ 1 = τ. Since C is infinite, SQDim = ⊤.
  let C : ConceptClass ℕ Bool := { f | ∃ n : ℕ, f = fun x => decide (x = n) }
  refine ⟨ℕ, inferInstance, C, ?_, ?_⟩
  · -- VCDim C < ⊤: C shatters singletons but not pairs.
    -- Upper bound: VCDim ≤ 1.
    -- For any S with |S| ≥ 2, let a, b ∈ S with a ≠ b.
    -- The labeling f(a) = true, f(b) = true requires ∃ n, (a == n) = true ∧ (b == n) = true,
    -- i.e., a = n = b, contradicting a ≠ b. So S is not shattered.
    have hle : VCDim ℕ C ≤ 1 := by
      unfold VCDim
      apply iSup₂_le
      intro S hS
      -- Show: if S is shattered by C, then |S| ≤ 1.
      -- Contrapositive: if |S| ≥ 2, S is not shattered.
      by_contra h
      push Not at h
      -- h : (1 : WithTop ℕ) < ↑S.card
      have hcard : 1 < S.card := by
        simp_all
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
      -- The all-true labeling: every point gets label `true`.
      obtain ⟨c, hcC, hcall⟩ := hS (fun _ => true)
      obtain ⟨n, hn⟩ := hcC
      have ha' := hcall ⟨a, ha⟩
      have hb' := hcall ⟨b, hb⟩
      -- c = fun x => decide (x = n), so c a = true means a = n, c b = true means b = n
      simp_all
    exact lt_of_le_of_lt hle (WithTop.coe_lt_top 1)
  · -- SQDimension C D τ = ⊤ at D = Dirac at 0, τ = 1.
    -- For the Dirac measure δ₀ on ℕ and τ = 1:
    -- The correlation |∫ (if c₁ x = c₂ x then 1 else -1) dδ₀| ≤ 1 = τ always holds
    -- (since the integrand is bounded by 1 in absolute value and δ₀ is a probability measure).
    -- So every finite subfamily of C satisfies the pairwise bound at τ = 1.
    -- Since C is infinite, SQDim = ⊤.
    refine ⟨MeasureTheory.Measure.dirac 0,
            MeasureTheory.Measure.dirac.isProbabilityMeasure,
            1, one_pos, ?_⟩
    -- Show SQDimension ℕ C (Measure.dirac 0) 1 = ⊤.
    -- SQDimension is ⨆ over Finsets S of concepts with S ⊆ C and pairwise |corr| ≤ 1.
    -- For any n, we can find a Finset of n+1 distinct concepts in C with |corr| ≤ 1.
    -- The bound |corr| ≤ 1 is trivially satisfied for any integrand bounded by [-1, 1]
    -- under any probability measure.
    -- The hard part: constructing the Finset witness with the integral bound.
    -- The integral ∫ x, (if c₁ x = c₂ x then 1 else -1) ∂(dirac 0) evaluates to
    -- (if c₁ 0 = c₂ 0 then 1 else -1), and |±1| ≤ 1 = τ.
    -- So the pairwise correlation condition holds for ALL pairs at τ = 1.
    -- Strategy: show ∀ b < ⊤, ∃ S with card > b and pairwise |corr| ≤ 1.
    -- For each n, construct a Finset of n distinct singleton indicators.
    -- The pairwise |correlation| ≤ 1 holds trivially under Dirac measure
    -- (∫ f d(dirac 0) = f 0, and |f 0| ≤ 1 since f 0 ∈ {-1, 1}).
    unfold SQDimension
    rw [iSup₂_eq_top]
    intro b hb
    -- b < ⊤ in WithTop ℕ, so b = ↑n for some n.
    obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hb)
    -- Construct Finset of n+1 distinct concepts from C.
    classical
    let mkIndicator : ℕ → Concept ℕ Bool := fun k x => decide (x = k)
    have hinj : Function.Injective mkIndicator := by
      intro k₁ k₂ heq
      have h := congr_fun heq k₁
      simpa [mkIndicator] using h
    let S : Finset (Concept ℕ Bool) := (Finset.range (n + 1)).image mkIndicator
    have hcard : S.card = n + 1 := by
      rw [Finset.card_image_of_injective _ hinj]
      exact Finset.card_range (n + 1)
    -- S ⊆ C: every indicator is in C.
    have hsubC : ↑S ⊆ C := by
      intro f hf
      simp only [S, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hf
      obtain ⟨k, _, rfl⟩ := hf
      exact ⟨k, rfl⟩
    -- Pairwise correlation ≤ 1: under dirac 0, ∫ f d(dirac 0) = f 0.
    have hcorr : ∀ c₁ ∈ S, ∀ c₂ ∈ S, c₁ ≠ c₂ →
        |∫ x, (if c₁ x = c₂ x then (1 : ℝ) else -1)
          ∂MeasureTheory.Measure.dirac (0 : ℕ)| ≤ 1 := by
      intro c₁ _ c₂ _ _
      rw [MeasureTheory.integral_dirac]
      split_ifs <;> simp
    refine ⟨S, ⟨hsubC, hcorr⟩, ?_⟩
    rw [hcard]
    exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_of_le (le_refl n))
