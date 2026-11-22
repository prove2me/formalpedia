-- Prove2me | solution 1 for sample_complexity_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:40.986739+00:00
-- url     : https://prove2.me/submissions/399cfa33-00e2-49bd-a2bd-9aa417580094

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
public import Theorems.Thm_P2M_vcdim_finite_imp_uc__685a2436ce92
public import Theorems.Thm_pac_lower_bound_member
public import Theorems.Thm_uc_imp_pac

section
@[expose] public section
universe u
attribute [local instance] Classical.propDecidable
section UCNotOnline
end UCNotOnline
private theorem pacLearnable_of_vcdim_finite (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hvcdim : VCDim X C < ⊤)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) : PACLearnable X C := by
  by_cases hne : C.Nonempty
  · exact uc_imp_pac X C hne (vcdim_finite_imp_uc' X C hvcdim hmeas_C hc_meas hWB)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨⟨Set.univ, fun _ => fun _ => false, fun _ => Set.mem_univ _⟩,
           fun _ _ => 0, fun _ _ _ _ _ _ c hcC => by simp [hne] at hcC⟩
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (d : ℕ)
    (hd : VCDim X C = d) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ2 : δ ≤ 1 / 7) (hd_pos : 1 ≤ d)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ SampleComplexity X C ε δ := by
  unfold SampleComplexity
  set S := { m : ℕ | ∃ (L : BatchLearner X Bool),
    ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ c ∈ C,
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          ≥ ENNReal.ofReal (1 - δ) } with hS_def
  have hvcdim_fin : VCDim X C < ⊤ := by
    rw [hd]; exact WithTop.coe_lt_top d
  obtain ⟨L, mf, hpac_wit⟩ :=
    pacLearnable_of_vcdim_finite X C hvcdim_fin hmeas_C hc_meas hWB
  have hmem : mf ε δ ∈ S := ⟨L, fun D hD c hcC => hpac_wit ε δ hε hδ D hD c hcC⟩
  exact le_csInf ⟨mf ε δ, hmem⟩ fun m hm =>
    pac_lower_bound_member X C d hd ε δ hε hε1 hδ hδ1 hδ2 hd_pos m hm
