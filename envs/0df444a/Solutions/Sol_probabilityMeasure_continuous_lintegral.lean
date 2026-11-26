-- Prove2me | solution 1 for probabilityMeasure_continuous_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:06:40.045317+00:00
-- url     : https://prove2.me/submissions/d729e15e-f963-4582-b6c3-c974a5a7c02c

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Measure.GiryMonad
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish

set_option autoImplicit false
open MeasureTheory Topology TopologicalSpace Metric Filter Set
open scoped ENNReal NNReal Classical
noncomputable section
variable {Ω : Type*} [MetricSpace Ω] [SeparableSpace Ω] [CompleteSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
omit [SeparableSpace Ω] [CompleteSpace Ω]
theorem _root_.solution (f : BoundedContinuousFunction Ω ℝ≥0) :
    Continuous fun γ : ProbabilityMeasure Ω =>
      ∫⁻ x, (f x : ℝ≥0∞) ∂(γ : Measure Ω) := by
  have heq : (fun γ : ProbabilityMeasure Ω =>
        ∫⁻ x, (f x : ℝ≥0∞) ∂(γ : Measure Ω))
      = fun γ => ((γ.toFiniteMeasure.testAgainstNN f : ℝ≥0) : ℝ≥0∞) := by
    funext γ
    rw [FiniteMeasure.testAgainstNN_coe_eq]
    rfl
  rw [heq]
  exact ENNReal.continuous_coe.comp
    ((FiniteMeasure.continuous_testAgainstNN_eval f).comp
      (ProbabilityMeasure.toFiniteMeasure_isEmbedding Ω).continuous)
