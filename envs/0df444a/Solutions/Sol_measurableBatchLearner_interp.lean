-- Prove2me | solution 1 for measurableBatchLearner_interp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:58.730654+00:00
-- url     : https://prove2.me/submissions/31fc66a3-3d00-4e2a-a605-c69666443a7f

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure
public import Theorems.Thm_measurableBatchLearner_combine

set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution
    {X : Type u} [MeasurableSpace X]
    (A : Set X) (hA : MeasurableSet A)
    (L₁ L₂ : BatchLearner X Bool)
    (h₁ : MeasurableBatchLearner X L₁)
    (h₂ : MeasurableBatchLearner X L₂) :
    MeasurableBatchLearner X (interpLearner A L₁ L₂) := by
  apply measurableBatchLearner_combine
  · change Measurable (fun p : X × (Fin 2 → Bool) => if p.1 ∈ A then p.2 0 else p.2 1)
    exact Measurable.ite (measurable_fst hA) ((measurable_pi_apply 0).comp measurable_snd)
      ((measurable_pi_apply 1).comp measurable_snd)
  · simp_all
