-- Prove2me | solution 1 for exists_level_selector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:13:03.092554+00:00
-- url     : https://prove2.me/submissions/3557890c-6e2a-4dc1-ad10-b3f3226957a1

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
import Theorems.Thm_P2M_MeasureTheory_AnalyticSet_inter__f59a23aaf291
import Theorems.Thm_jankov_von_neumann


set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
noncomputable section
variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]
theorem _root_.solution [PolishSpace H] [PolishSpace E]
    {Γ : Set (H × E)} {F : H × E → ℝ≥0∞}
    (hΓ : AnalyticSet Γ) (hF : IsLowerSemianalytic (X := H × E) F)
    {φ' : H → E} (hφ' : AnalyticallyMeasurable φ') (q : ℝ≥0∞) :
    ∃ χ : H → E, AnalyticallyMeasurable χ ∧
      ∀ h : H, (∃ e, (h, e) ∈ Γ ∧ F (h, e) < q) →
        (h, χ h) ∈ Γ ∧ F (h, χ h) < q := by
  have hA : AnalyticSet (Γ ∩ {p | F p < q}) := hΓ.inter' (hF q)
  by_cases hAne : (Γ ∩ {p | F p < q}).Nonempty
  · obtain ⟨χ, hχ, hsel⟩ := jankov_von_neumann _ hA hAne
    refine ⟨χ, hχ, fun h ⟨e, heΓ, heF⟩ => ?_⟩
    exact hsel h ⟨(h, e), ⟨heΓ, heF⟩, rfl⟩
  · exact ⟨φ', hφ', fun h ⟨e, heΓ, heF⟩ => absurd ⟨(h, e), heΓ, heF⟩ hAne⟩
