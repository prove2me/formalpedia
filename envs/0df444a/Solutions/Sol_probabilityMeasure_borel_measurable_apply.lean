-- Prove2me | solution 1 for probabilityMeasure_borel_measurable_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:08:05.089221+00:00
-- url     : https://prove2.me/submissions/7ed666e0-5829-46f6-ae7c-f3c9d25c87bd

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Measure.GiryMonad
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Theorems.Thm_probabilityMeasure_borel_measurable_apply_isClosed

set_option autoImplicit false
open MeasureTheory Topology TopologicalSpace Metric Filter Set
open scoped ENNReal NNReal Classical
noncomputable section
variable {Ω : Type*} [MetricSpace Ω] [SeparableSpace Ω] [CompleteSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
omit [SeparableSpace Ω] [CompleteSpace Ω]
theorem _root_.solution
    {s : Set Ω} (hs : MeasurableSet s) :
    @Measurable (ProbabilityMeasure Ω) ℝ≥0∞
      (borel (ProbabilityMeasure Ω)) inferInstance
      (fun γ => (γ : Measure Ω) s) := by
  letI : MeasurableSpace (ProbabilityMeasure Ω) := borel _
  haveI : BorelSpace (ProbabilityMeasure Ω) := ⟨rfl⟩
  induction s, hs using MeasurableSpace.induction_on_inter
    (m := (inferInstance : MeasurableSpace Ω))
    (s := {t : Set Ω | IsClosed t})
    ((BorelSpace.measurable_eq (α := Ω)).trans borel_eq_generateFrom_isClosed)
    isPiSystem_isClosed with
  | empty =>
    simp only [measure_empty]
    exact measurable_const
  | basic t ht =>
    exact probabilityMeasure_borel_measurable_apply_isClosed ht
  | compl t htm iht =>
    have heq : (fun γ : ProbabilityMeasure Ω => (γ : Measure Ω) tᶜ)
        = fun γ : ProbabilityMeasure Ω => 1 - (γ : Measure Ω) t := by
      funext γ
      rw [prob_compl_eq_one_sub htm]
    rw [heq]
    exact measurable_const.sub iht
  | iUnion f hdisj hfm ihf =>
    have heq : (fun γ : ProbabilityMeasure Ω => (γ : Measure Ω) (⋃ n, f n))
        = fun γ : ProbabilityMeasure Ω => ∑' n, (γ : Measure Ω) (f n) := by
      funext γ
      exact measure_iUnion hdisj hfm
    rw [heq]
    exact Measurable.tsum ihf
