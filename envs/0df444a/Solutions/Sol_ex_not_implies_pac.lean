-- Prove2me | solution 1 for ex_not_implies_pac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:23.069187+00:00
-- url     : https://prove2.me/submissions/8be8f97f-031e-4db1-b3e2-3e6662b755de

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Extended
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Online
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Separation
public import Theorems.Thm_vcdim_infinite_not_pac


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
attribute [local instance] Classical.propDecidable
universe u v
theorem _root_.solution :
    ∃ (X : Type) (_ : Countable X) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      EXLearnable X C ∧ ¬ PACLearnable X C := by
  -- Witness: X = ℕ, measurable space = ⊤, C = indicator functions of finite subsets
  refine ⟨ℕ, inferInstance, ⊤, { f : ℕ → Bool | Set.Finite { n | f n = true } }, ?_, ?_⟩
  · -- EXLearnable: construct a Gold learner that outputs "true on seen elements"
    refine ⟨⟨fun data => fun x => data.any (fun p => decide (p.1 = x))⟩, ?_⟩
    intro c hcC T
    have hfin : Set.Finite { n : ℕ | c n = true } := hcC
    -- Helper: c x ≠ true implies x never appears in T (by T.correct)
    have never_seen : ∀ x, c x ≠ true → ∀ t, (T.toDataStream.observe t).1 ≠ x := by
      intro x hcx t heq
      exact hcx (heq ▸ T.correct t)
    -- Convergence lemma: for each x, the learner eventually gets x right.
    -- For x in support: T.exhaustive guarantees x appears, then learner sees it.
    -- For x not in support: T.correct ensures x never appears, so learner never claims it.
    -- Since the support is finite, take the max appearance time.
    -- Use Finset.sup on the support to get t₀.
    -- But tmap has dependent type (x ∈ hfin.toFinset), so we project to a total function.
    have hsup : ∀ x ∈ hfin.toFinset, ∃ t, (T.toDataStream.observe t).1 = x := by
      intro x hx; exact T.exhaustive x (hfin.mem_toFinset.mp hx)
    choose tmap htmap using hsup
    -- Build a total function for Finset.sup
    let tmap' : ℕ → ℕ := fun x => if h : x ∈ hfin.toFinset then tmap x h else 0
    refine ⟨hfin.toFinset.sup tmap', fun t ht => ?_⟩
    funext x
    simp only [dataUpTo]
    cases hcxb : c x with
    | true =>
      -- x is in the support, appeared at time tmap x hxfin ≤ t₀ ≤ t
      have hxfin : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr hcxb
      have htmap'_eq : tmap' x = tmap x hxfin := dif_pos hxfin
      have htx_le : tmap x hxfin ≤ t := by
        calc tmap x hxfin = tmap' x := htmap'_eq.symm
          _ ≤ hfin.toFinset.sup tmap' := Finset.le_sup hxfin
          _ ≤ t := ht
      -- (T.observe (tmap x hxfin)).1 = x, and tmap x hxfin ≤ t
      -- So ∃ i ∈ range(t+1), (T.observe i).1 = x
      -- Learner returns true for x
      change (((List.range (t + 1)).map T.toDataStream.observe).any
        (fun p => decide (p.1 = x))) = true
      rw [List.any_map, List.any_eq_true]
      exact ⟨tmap x hxfin,
        List.mem_range.mpr (Nat.lt_succ_of_le htx_le),
        by simp [htmap x hxfin]⟩
    | false =>
      -- x not in support, never appears in T
      simp_all
  · -- ¬PACLearnable: VCDim = ⊤, then apply vcdim_infinite_not_pac
    apply vcdim_infinite_not_pac
    -- Show VCDim ℕ C = ⊤ where C = { f | Set.Finite { n | f n = true } }
    -- Strategy: for any n, Finset.range n is shattered by C, so VCDim ≥ n for all n
    rw [VCDim, iSup₂_eq_top]
    intro b hb
    obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hb)
    refine ⟨Finset.range (n + 1), ?_, ?_⟩
    · -- Shatters: every labeling of Finset.range (n+1) is realized by some c ∈ C
      intro f
      refine ⟨fun x => if h : x ∈ Finset.range (n + 1) then f ⟨x, h⟩ else false, ?_, ?_⟩
      · -- c ∈ C: { x | c x = true } is finite (subset of Finset.range (n+1))
        change Set.Finite { x | (if h : x ∈ Finset.range (n + 1) then f ⟨x, h⟩ else false) = true }
        apply Set.Finite.subset (Finset.range (n + 1)).finite_toSet
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx
        simp only [Finset.mem_coe]
        by_contra hx'
        simp [hx'] at hx
      · -- ∀ x : ↥S, c x = f x
        simp_all
    · -- n < (Finset.range (n+1)).card as WithTop ℕ
      simp only [Finset.card_range]
      exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)
