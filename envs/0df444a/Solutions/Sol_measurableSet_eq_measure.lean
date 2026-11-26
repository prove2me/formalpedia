-- Prove2me | solution 1 for measurableSet_eq_measure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:11:33.839682+00:00
-- url     : https://prove2.me/submissions/430b718a-ee73-4b6c-ba81-9a14c14ac0c1

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Measure.GiryMonad
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Theorems.Thm_countable_generatePiSystem

set_option autoImplicit false
open MeasureTheory Topology TopologicalSpace Metric Filter Set
open scoped ENNReal NNReal Classical
noncomputable section
theorem _root_.solution {α : Type*} [MeasurableSpace α] {W : Type*}
    [TopologicalSpace W] [PolishSpace W] [MeasurableSpace W] [BorelSpace W]
    {F G : α → Measure W} (hF : Measurable F) (hG : Measurable G)
    (hFfin : ∀ a, IsProbabilityMeasure (F a))
    (hGfin : ∀ a, IsProbabilityMeasure (G a)) :
    MeasurableSet {a | F a = G a} := by
  have hCcnt : (generatePiSystem (countableBasis W)).Countable :=
    countable_generatePiSystem (countable_countableBasis W)
  have hCpi : IsPiSystem (generatePiSystem (countableBasis W)) :=
    isPiSystem_generatePiSystem _
  have hCgen : ‹MeasurableSpace W› =
      MeasurableSpace.generateFrom (generatePiSystem (countableBasis W)) := by
    rw [generateFrom_generatePiSystem_eq,
      ← (isBasis_countableBasis W).borel_eq_generateFrom]
    exact ‹BorelSpace W›.measurable_eq
  have hCmeas : ∀ s ∈ generatePiSystem (countableBasis W), MeasurableSet s :=
    fun s hs => generatePiSystem_measurableSet
      (fun _ hu => (isOpen_of_mem_countableBasis hu).measurableSet) s hs
  have hset : {a | F a = G a} =
      ⋂ s ∈ generatePiSystem (countableBasis W), {a | F a s = G a s} := by
    ext a
    simp only [mem_ofPred_eq, mem_iInter]
    refine ⟨fun h s _ => by rw [h], fun h => ?_⟩
    haveI := hFfin a
    exact ext_of_generate_finite _ hCgen hCpi h
      (by rw [(hFfin a).measure_univ, (hGfin a).measure_univ])
  rw [hset]
  exact MeasurableSet.biInter hCcnt fun s hs =>
    measurableSet_eq_fun ((Measure.measurable_coe (hCmeas s hs)).comp hF)
      ((Measure.measurable_coe (hCmeas s hs)).comp hG)
