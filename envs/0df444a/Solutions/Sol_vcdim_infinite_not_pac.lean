-- Prove2me | solution 1 for vcdim_infinite_not_pac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:35:54.272225+00:00
-- url     : https://prove2.me/submissions/d3eb0496-0d30-44ac-b5b5-f229e2dde05f

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Theorems.Thm_nfl_counting_core
public import Theorems.Thm_pac_lower_bound_good_event_le_half


set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (hinf : VCDim X C = ⊤) :
    ¬ PACLearnable X C := by
  -- Assume PACLearnable for contradiction
  intro ⟨L, mf, hpac⟩
  -- Step 1: VCDim = ⊤ → for any n, ∃ shattered T with |T| > n
  have hvcdim_unbounded : ∀ b : WithTop ℕ, b < ⊤ → ∃ T, ∃ _ : Shatters X C T,
      b < (T.card : WithTop ℕ) := by
    have := (iSup₂_eq_top
      (fun (T : Finset X) (_ : Shatters X C T) => (T.card : WithTop ℕ))).mp
    rw [VCDim] at hinf
    exact this hinf
  -- Step 2: Fix ε = 1 / 4, δ = 1 / 4, m = mf(1 / 4)(1 / 4)
  set m := mf (1 / 4 : ℝ) (1 / 4 : ℝ) with hm_def
  -- Step 3: Get shattered T with |T| > 2m
  obtain ⟨T, hTshat, hTcard⟩ := hvcdim_unbounded (2 * m) (WithTop.coe_lt_top _)
  -- hTcard : (2 * ↑m : WithTop ℕ) < (T.card : WithTop ℕ)
  have hTcard_nat : 2 * m < T.card := by exact_mod_cast hTcard
  -- Step 4: From PAC guarantee, L works for ε=1 / 4, δ=1 / 4
  have hpac14 := hpac (1 / 4 : ℝ) (1 / 4 : ℝ) (by norm_num) (by norm_num)
  -- Step 5: T is nonempty (|T| > 2m ≥ 0)
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; simp [h] at hTcard_nat
  -- Step 6: Derive contradiction.
  -- We need: ∃ D (prob measure on X), ∃ c ∈ C, PAC guarantee fails.
  -- hpac14 says: ∀ D prob, ∀ c ∈ C, Pr[err ≤ 1 / 4] ≥ 3 / 4.
  -- We construct D and find c ∈ C where Pr[err ≤ 1 / 4] < 3 / 4.
  suffices ∃ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ∧
      ∃ c ∈ C,
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal (1 / 4 : ℝ) }
          < ENNReal.ofReal (1 - 1 / 4 : ℝ) by
    obtain ⟨D, hDprob, c, hcC, hfail⟩ := this
    exact not_le.mpr hfail (hpac14 D hDprob c hcC)
  classical
  obtain ⟨_, c₀, hc₀C, _, hcount⟩ := nfl_counting_core hTshat hTcard_nat L
  obtain ⟨D, hDprob, hgood_half⟩ :=
    pac_lower_bound_good_event_le_half (X := X) (T := T) hTne L m c₀
      (1 / 4 : ℝ) (by norm_num) (by simpa using hcount)
  refine ⟨D, hDprob, c₀, hc₀C, ?_⟩
  exact lt_of_le_of_lt hgood_half
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mpr (by norm_num))
