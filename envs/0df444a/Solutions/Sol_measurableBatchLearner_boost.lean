-- Prove2me | solution 1 for measurableBatchLearner_boost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:54.154907+00:00
-- url     : https://prove2.me/submissions/c4f874a0-4abf-48e4-884e-935149d4c715

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
    (k : ℕ) (L : Fin k → BatchLearner X Bool)
    (hL : ∀ i, MeasurableBatchLearner X (L i)) :
    MeasurableBatchLearner X (boostLearner k L) := by
  apply measurableBatchLearner_combine
  · exact (measurable_of_finite (fun v : Fin k → Bool => majorityVote k v)).comp measurable_snd
  · exact hL
