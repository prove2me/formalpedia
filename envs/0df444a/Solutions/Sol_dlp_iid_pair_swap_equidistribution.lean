-- Prove2me | solution 1 for dlp_iid_pair_swap_equidistribution
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T03:54:36.450286+00:00
-- url     : https://prove2.me/submissions/55b4a7ca-75ee-4005-ae29-533e1175af85

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.Normed.Module.Basic
open MeasureTheory
open scoped ENNReal

theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (P : α → α → Prop) (hP : MeasurableSet {ab : α × α | P ab.1 ab.2}) :
    (μ.prod μ).real {ab : α × α | P ab.1 ab.2}
      = (μ.prod μ).real {ab : α × α | P ab.2 ab.1} := by
  classical
  have hmp : MeasurePreserving (Prod.swap : α × α → α × α) (μ.prod μ) (μ.prod μ) := by
    have := Measure.measurePreserving_swap (μ := μ) (ν := μ)
    simpa using this
  have hpre : (Prod.swap : α × α → α × α) ⁻¹' {ab : α × α | P ab.1 ab.2}
      = {ab : α × α | P ab.2 ab.1} := by
    ext ab; simp [Prod.swap]
  rw [← hpre]
  exact (hmp.measureReal_preimage hP.nullMeasurableSet).symm
