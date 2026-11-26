-- Prove2me | solution 1 for exists_inward_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:21.825861+00:00
-- url     : https://prove2.me/submissions/4873ce04-bf6a-41d0-82a9-4b4683364442

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain)
    (hbounded : Bornology.IsBounded Omega.carrier)
    {c z : ℂ} (hc : c ∈ Omega.carrier) (hz : z ∈ Omega.carrier) :
    ∃ r ∈ Ioc (0 : ℝ) 1, ∃ eta ∈ frontier Omega.carrier,
      smoothJordanInwardPoint c eta r = z := by
  by_cases hzc : z = c
  · refine ⟨1, ⟨zero_lt_one, le_rfl⟩, Omega.boundaryParam 0, ?_, ?_⟩
    · rw [← Omega.boundaryParam_range]
      exact mem_range_self 0
    · rw [hzc]
      simp only [smoothJordanInwardPoint, sub_self, zero_smul, one_smul,
        zero_add]
  let f : ℝ → ℂ := fun t => c + t • (z - c)
  let S : Set ℝ := {t | f t ∈ Omega.carrier}
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hSopen : IsOpen S := Omega.isOpen_carrier.preimage hf
  have h0 : (0 : ℝ) ∈ S := by
    simpa only [S, mem_ofPred_eq, f, zero_smul, add_zero] using hc
  have h1 : (1 : ℝ) ∈ S := by
    simpa only [S, mem_ofPred_eq, f, one_smul, add_sub_cancel] using hz
  have hSne : S.Nonempty := ⟨0, h0⟩
  obtain ⟨R, _hRpos, hR⟩ := hbounded.subset_ball_lt 0 c
  have hvpos : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzc)
  have hSbdd : BddAbove S := by
    refine ⟨R / ‖z - c‖, ?_⟩
    intro t ht
    have hmem := hR ht
    rw [Metric.mem_ball, dist_eq_norm] at hmem
    have heq : f t - c = t • (z - c) := by
      dsimp only [f]
      module
    rw [heq, norm_smul, Real.norm_eq_abs] at hmem
    have habs : |t| < R / ‖z - c‖ :=
      (lt_div_iff₀ hvpos).2 hmem
    exact (le_abs_self t).trans habs.le
  let T := sSup S
  obtain ⟨eps, heps, hepsSub⟩ := Metric.isOpen_iff.mp hSopen 1 h1
  let a := 1 + eps / 2
  have haBall : a ∈ Metric.ball (1 : ℝ) eps := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp only [a]
    rw [add_sub_cancel_left, abs_of_pos (half_pos heps)]
    linarith
  have ha : a ∈ S := hepsSub haBall
  have haT : a ≤ T := le_csSup hSbdd ha
  have hT : 1 < T := by
    apply lt_of_lt_of_le _ haT
    dsimp only [a]
    linarith
  have hTclosure : T ∈ closure S := csSup_mem_closure hSne hSbdd
  have hetaClosure : f T ∈ closure Omega.carrier := by
    have himage : f T ∈ f '' closure S := ⟨T, hTclosure, rfl⟩
    have hclosureImage : f '' closure S ⊆ closure (f '' S) :=
      image_closure_subset_closure_image hf
    apply closure_mono _ (hclosureImage himage)
    rintro _ ⟨t, ht, rfl⟩
    exact ht
  have hTnot : T ∉ S := by
    intro hTS
    obtain ⟨eps, heps, hepsSub⟩ := Metric.isOpen_iff.mp hSopen T hTS
    let b := T + eps / 2
    have hbBall : b ∈ Metric.ball T eps := by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp only [b]
      rw [add_sub_cancel_left, abs_of_pos (half_pos heps)]
      linarith
    have hb : b ∈ S := hepsSub hbBall
    have hbT : b ≤ T := le_csSup hSbdd hb
    dsimp only [b] at hbT
    linarith
  have heta : f T ∈ frontier Omega.carrier := by
    rw [frontier, Omega.isOpen_carrier.interior_eq]
    exact ⟨hetaClosure, hTnot⟩
  let r := 1 - T⁻¹
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hrpos : 0 < r := by
    dsimp only [r]
    rw [sub_pos]
    exact (inv_lt_one₀ hTpos).2 hT
  have hrle : r ≤ 1 := by
    dsimp only [r]
    exact sub_le_self 1 (inv_nonneg.mpr hTpos.le)
  refine ⟨r, ⟨hrpos, hrle⟩, f T, heta, ?_⟩
  unfold smoothJordanInwardPoint
  dsimp only [r, f]
  rw [show 1 - (1 - T⁻¹) = T⁻¹ by ring, smul_add, smul_smul,
    inv_mul_cancel₀ hTpos.ne', one_smul]
  module
