-- Prove2me | solution 1 for probabilityMeasure_borel_measurable_apply_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:07:28.133886+00:00
-- url     : https://prove2.me/submissions/302441b8-200c-4708-8bce-236d63f04d70

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Measure.GiryMonad
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Theorems.Thm_probabilityMeasure_continuous_lintegral

set_option autoImplicit false
open MeasureTheory Topology TopologicalSpace Metric Filter Set
open scoped ENNReal NNReal Classical
noncomputable section
variable {Ω : Type*} [MetricSpace Ω] [SeparableSpace Ω] [CompleteSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
omit [SeparableSpace Ω] [CompleteSpace Ω]
theorem _root_.solution
    {F : Set Ω} (hF : IsClosed F) :
    @Measurable (ProbabilityMeasure Ω) ℝ≥0∞
      (borel (ProbabilityMeasure Ω)) inferInstance
      (fun γ => (γ : Measure Ω) F) := by
  letI : MeasurableSpace (ProbabilityMeasure Ω) := borel _
  haveI : BorelSpace (ProbabilityMeasure Ω) := ⟨rfl⟩
  have hlim : Tendsto
      (fun n => fun γ : ProbabilityMeasure Ω =>
        ∫⁻ x, (hF.apprSeq n x : ℝ≥0∞) ∂(γ : Measure Ω))
      atTop (𝓝 fun γ => (γ : Measure Ω) F) := by
    rw [tendsto_pi_nhds]
    intro γ
    exact HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (γ : Measure Ω)
  exact measurable_of_tendsto_metrizable
    (fun n => (probabilityMeasure_continuous_lintegral (hF.apprSeq n)).measurable)
    hlim
