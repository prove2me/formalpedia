-- Prove2me | solution 1 for probabilityMeasure_borel_measurable_toMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:11:32.91768+00:00
-- url     : https://prove2.me/submissions/72d50eb5-cb1b-48d1-a30a-1075e1862967

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Measure.GiryMonad
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Theorems.Thm_probabilityMeasure_borel_measurable_apply

set_option autoImplicit false
open MeasureTheory Topology TopologicalSpace Metric Filter Set
open scoped ENNReal NNReal Classical
noncomputable section
variable {Ω : Type*} [MetricSpace Ω] [SeparableSpace Ω] [CompleteSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
omit [SeparableSpace Ω] [CompleteSpace Ω]
theorem _root_.solution :
    @Measurable (ProbabilityMeasure Ω) (Measure Ω)
      (borel (ProbabilityMeasure Ω)) inferInstance
      ((↑) : ProbabilityMeasure Ω → Measure Ω) := by
  letI : MeasurableSpace (ProbabilityMeasure Ω) := borel _
  exact Measure.measurable_measure.mpr
    fun s hs => probabilityMeasure_borel_measurable_apply hs
