-- Prove2me | solution 1 for iInf_fiber_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:10:01.604822+00:00
-- url     : https://prove2.me/submissions/eaa05532-8395-41a2-bada-77e9c9d4d136

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection

set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
noncomputable section
variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]
omit [TopologicalSpace H] [TopologicalSpace E]
theorem _root_.solution {Γ : Set (H × E)} {F : H × E → ℝ≥0∞} {h : H}
    {q : ℝ≥0∞} (hlt : (⨅ (e : E) (_ : (h, e) ∈ Γ), F (h, e)) < q) :
    ∃ e : E, (h, e) ∈ Γ ∧ F (h, e) < q := by
  rw [iInf_lt_iff] at hlt
  obtain ⟨e, he⟩ := hlt
  rw [iInf_lt_iff] at he
  obtain ⟨hm, hfc⟩ := he
  exact ⟨e, hm, hfc⟩
