-- Prove2me | solution 1 for rademacher_vanishing_imp_pac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:23.393739+00:00
-- url     : https://prove2.me/submissions/879bd71e-39eb-42ec-a37c-346b7b200adc

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
public import Theorems.Thm_MeasurableConceptClass_hWB
public import Theorems.Thm_MeasurableConceptClass_hc_meas
public import Theorems.Thm_P2M_vcdim_finite_imp_pac_via_uc__c09ebcf0a1b4
public import Theorems.Thm_rademacher_lower_bound_on_shattered


set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C)
    (hrad : ∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D →
      ∀ m ≥ m₀, RademacherComplexity X C D m < ε) :
    PACLearnable X C := by
  apply vcdim_finite_imp_pac_via_uc' _ _ _ hmeas_C hc_meas hWB
  by_contra hvcdim_inf
  push Not at hvcdim_inf
  have hvcdim_top : VCDim X C = ⊤ := le_antisymm le_top hvcdim_inf
  have h_large_shatter : ∀ n : ℕ, ∃ T : Finset X, Shatters X C T ∧ n ≤ T.card := by
    intro n; by_contra h_neg; push Not at h_neg
    have hle : VCDim X C ≤ ↑n := by
      apply iSup₂_le; intro T hT; exact_mod_cast le_of_lt (h_neg T hT)
    rw [hvcdim_top] at hle; exact absurd hle (by simp)
  obtain ⟨m₀, hm₀⟩ := hrad (1 / 2) (by norm_num)
  set m := max m₀ 1
  obtain ⟨T, hT_shat, hT_card⟩ := h_large_shatter (4 * m ^ 2 + 1)
  obtain ⟨D, hD, hRad_ge⟩ := rademacher_lower_bound_on_shattered X C T hT_shat m (by omega) hT_card
  linarith [hm₀ D hD m (le_max_left m₀ 1)]
