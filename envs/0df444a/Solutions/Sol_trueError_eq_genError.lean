-- Prove2me | solution 1 for trueError_eq_genError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:17.887709+00:00
-- url     : https://prove2.me/submissions/56c0a8b8-07b7-4c83-90ec-823df9f208ca

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X)
    (hmeas : MeasurableSet { x | h x ≠ c x })
    (hcmeas : Measurable c)
    (hhmeas : Measurable h) :
    TrueErrorReal X h c D = GeneralizationError X Bool h
      (D.map (fun x => (x, c x))) (zeroOneLoss Bool) := by
  unfold TrueErrorReal TrueError GeneralizationError
  rw [← MeasureTheory.Measure.real_def, ← MeasureTheory.integral_indicator_one hmeas]
  have integrand_eq : (fun x => Set.indicator {x | h x ≠ c x} (1 : X → ℝ) x) =
      (fun x => zeroOneLoss Bool (h x) (c x)) := by
    ext x
    simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply, zeroOneLoss]
    split_ifs <;> simp_all
  rw [integrand_eq]
  have hphi : Measurable (fun x => (x, c x) : X → X × Bool) :=
    measurable_id.prodMk hcmeas
  have hf_meas : Measurable (fun p : X × Bool => zeroOneLoss Bool (h p.1) p.2) :=
    Measurable.ite (measurableSet_eq_fun (hhmeas.comp measurable_fst) measurable_snd)
      measurable_const measurable_const
  exact (MeasureTheory.integral_map hphi.aemeasurable
    hf_meas.stronglyMeasurable.aestronglyMeasurable).symm
