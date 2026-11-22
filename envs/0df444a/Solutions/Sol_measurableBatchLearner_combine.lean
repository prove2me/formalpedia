-- Prove2me | solution 1 for measurableBatchLearner_combine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:37:04.301638+00:00
-- url     : https://prove2.me/submissions/d8f1985b-5703-4a1b-9b42-dfd56732bb78

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
    (k : ℕ) (F : X → (Fin k → Bool) → Bool)
    (hF : Measurable (fun p : X × (Fin k → Bool) => F p.1 p.2))
    (L : Fin k → BatchLearner X Bool)
    (hL : ∀ i, MeasurableBatchLearner X (L i)) :
    MeasurableBatchLearner X (combineLearner k F L) where
  eval_measurable m := by
    change Measurable (fun p : (Fin m → X × Bool) × X => F p.2 (fun i => (L i).learn p.1 p.2))
    have hg : Measurable (fun p : (Fin m → X × Bool) × X =>
        (p.2, fun i => (L i).learn p.1 p.2) : (Fin m → X × Bool) × X → X × (Fin k → Bool)) :=
      Measurable.prodMk measurable_snd
        (measurable_pi_iff.mpr (fun i => (hL i).eval_measurable m))
    exact hF.comp hg
