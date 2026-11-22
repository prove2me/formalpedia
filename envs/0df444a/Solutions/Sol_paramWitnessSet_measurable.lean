-- Prove2me | solution 1 for paramWitnessSet_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:42.438303+00:00
-- url     : https://prove2.me/submissions/d3139cb9-fbf8-4d50-9d38-7e06db1b8817

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
section
@[expose] public section
universe u
open MeasureTheory
private theorem empiricalError_component_measurable
    {X : Type u} [MeasurableSpace X]
    {Θ : Type*} [MeasurableSpace Θ]
    {e : Θ → Concept X Bool}
    (he : Measurable (fun p : Θ × X => e p.1 p.2))
    {c : Concept X Bool} (hc : Measurable c) (m : ℕ)
    (sel : GhostPairs X m → (Fin m → X))
    (hsel : Measurable sel) :
    Measurable fun q : Θ × GhostPairs X m =>
      EmpiricalError X Bool (e q.1) (fun i => (sel q.2 i, c (sel q.2 i))) (zeroOneLoss Bool) := by
  have term_meas : ∀ i : Fin m, Measurable fun q : Θ × GhostPairs X m =>
      zeroOneLoss Bool (e q.1 (sel q.2 i)) (c (sel q.2 i)) := by
    intro i
    simp only [zeroOneLoss]
    refine Measurable.ite (measurableSet_eq_fun ?_ ?_) measurable_const measurable_const
    · exact he.comp (measurable_fst.prodMk
        ((measurable_pi_apply i).comp (hsel.comp measurable_snd)))
    · exact hc.comp ((measurable_pi_apply i).comp (hsel.comp measurable_snd))
  simp only [EmpiricalError]
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, ↓reduceIte]
    exact (Finset.measurable_sum _ (fun i _ => term_meas i)).div_const _
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
theorem _root_.solution
    {X : Type u} [MeasurableSpace X]
    {Θ : Type*} [MeasurableSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2))
    (c : Concept X Bool) (hc : Measurable c)
    (m : ℕ) (ε : ℝ) :
    MeasurableSet (paramWitnessSet e c m ε) := by
  unfold paramWitnessSet
  -- The gap Δ = EmpErr_ghost - EmpErr_train is measurable, then use measurableSet_le.
  exact measurableSet_le measurable_const
    ((empiricalError_component_measurable he hc m _ measurable_snd).sub
      (empiricalError_component_measurable he hc m _ measurable_fst))
