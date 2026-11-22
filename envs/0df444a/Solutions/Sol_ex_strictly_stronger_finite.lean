-- Prove2me | solution 1 for ex_strictly_stronger_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:32.242578+00:00
-- url     : https://prove2.me/submissions/7d20a8a2-ba1f-467e-b367-c95fddb9e252

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

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
attribute [local instance] Classical.propDecidable
universe u v
theorem _root_.solution :
    ∀ (X : Type u) (C : ConceptClass X Bool),
      FiniteLearnable X C → EXLearnable X C := by
  intro X C ⟨L, hL⟩
  exact ⟨L, fun c hcC T => by
    obtain ⟨t₀, ht₀⟩ := hL c hcC T
    exact ⟨t₀, fun t ht => (ht₀ t ht).1⟩⟩
