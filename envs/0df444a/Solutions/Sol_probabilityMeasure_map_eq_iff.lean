-- Prove2me | solution 1 for probabilityMeasure_map_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:05:29.188218+00:00
-- url     : https://prove2.me/submissions/54dbb801-19d6-4f00-a09f-1be36ea663e1

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact

set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
theorem _root_.solution (γ : ProbabilityMeasure Ω) (μ : ProbabilityMeasure Ω')
    {f : Ω → Ω'} (hf : Measurable f) :
    γ.map hf.aemeasurable = μ ↔ (γ : Measure Ω).map f = (μ : Measure Ω') := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    exact h
