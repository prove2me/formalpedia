-- Prove2me | solution 1 for exists_fallback_selector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:58.280997+00:00
-- url     : https://prove2.me/submissions/d71bde53-8e68-4ef2-b278-9620c04dbdea

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
import Theorems.Thm_jankov_von_neumann


set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
noncomputable section
variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]
theorem _root_.solution [PolishSpace H] [PolishSpace E]
    {Γ : Set (H × E)} (hΓ : AnalyticSet Γ) (hΓne : Γ.Nonempty)
    (hfib : ∀ h : H, ∃ e : E, (h, e) ∈ Γ) :
    ∃ φ : H → E, AnalyticallyMeasurable φ ∧ ∀ h, (h, φ h) ∈ Γ := by
  obtain ⟨φ, hφ, hsel⟩ := jankov_von_neumann Γ hΓ hΓne
  refine ⟨φ, hφ, fun h => ?_⟩
  obtain ⟨e, he⟩ := hfib h
  exact hsel h ⟨(h, e), he, rfl⟩
