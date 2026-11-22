-- Prove2me | solution 1 for measurableBatchLearner_concat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:41:37.061499+00:00
-- url     : https://prove2.me/submissions/3a2da421-fcc7-42c3-96e8-0680322bae0c

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure

set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution
    {X : Type u} [MeasurableSpace X]
    (L : ℕ → BatchLearner X Bool)
    [hL : UniformMeasurableBatchFamily L]
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    (hsel : ∀ m, Measurable (fun S : Fin m → X × Bool => @sel m S)) :
    MeasurableBatchLearner X (concatLearner L sel) where
  eval_measurable m := by
    change Measurable (fun p : (Fin m → X × Bool) × X => (L (sel p.1)).learn p.1 p.2)
    -- Factor: (hL.eval_measurable m) ∘ (fun p => (sel p.1, p.1, p.2))
    exact (hL.eval_measurable m).comp
      (Measurable.prodMk ((hsel m).comp measurable_fst)
        (Measurable.prodMk measurable_fst measurable_snd))
