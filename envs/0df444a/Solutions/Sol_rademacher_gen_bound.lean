-- Prove2me | solution 1 for rademacher_gen_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:05.639793+00:00
-- url     : https://prove2.me/submissions/0333af0c-73d8-42e9-94ad-53accc5fdce8

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Theorems.Thm_rademacherComplexity_nonneg

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X)
    (m : ℕ) (hm : 0 < m) (c : Concept X Bool) (_hcC : c ∈ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (bound : ℝ), bound = 2 * RademacherComplexity X C D m + ε ∧ bound ≥ 0 := by
  refine ⟨2 * RademacherComplexity X C D m + ε, rfl, ?_⟩
  linarith [rademacherComplexity_nonneg X C D m hm]
