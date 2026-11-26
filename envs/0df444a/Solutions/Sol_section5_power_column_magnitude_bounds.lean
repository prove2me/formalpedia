-- Prove2me | solution 1 for section5_power_column_magnitude_bounds
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:12:52.962155+00:00
-- url     : https://prove2.me/submissions/c7c93d31-a3d0-43cc-831a-a9ca918569c4

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Mathlib
import Theorems.Thm_section5_column_norm_bound
import Theorems.Thm_section5_tomography_power_error
import Theorems.Thm_section5_tomography_rayleigh_lower
import Theorems.Thm_section5_top_eigenpair_exists
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Reconstruction by an explicitly selected column of an operator. This is the
finite arithmetic step used after powering an accurate rank-one estimate. -/



theorem section5_coordinate_ket_norm {n : ℕ} (i : Fin n) :
    ‖section5_coordinate_ket i‖=1 := by simp [section5_coordinate_ket]







end
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Uniform magnitude and output-precision bounds for the powered-column decoder.
They avoid choosing an output precision that depends on an unknown target state. -/

theorem section5_max_column_magnitude_lower {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (j : Fin n) (hmax : ∀ i, ‖A (section5_coordinate_ket i)‖ ≤ ‖A (section5_coordinate_ket j)‖)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖=1)
    (α ρ : ℝ) (hα : 0 ≤ α) (hρ : ρ ≤ α/2)
    (herror : ‖A-(α:ℂ) • rankOne ℂ v v‖ ≤ ρ) :
    α ≤ 2*n*‖A (section5_coordinate_ket j)‖ := by
  have hαv : ((α:ℂ) • rankOne ℂ v v) v=(α:ℂ) • v := by
    simp [rankOne_apply,inner_self_eq_norm_sq_to_K,hv]
  have herr : ‖A v-(α:ℂ) • v‖ ≤ ρ := by
    have hh := (A-(α:ℂ) • rankOne ℂ v v).le_opNorm v
    have he : (A-(α:ℂ) • rankOne ℂ v v) v=A v-(α:ℂ) • v := by rw [sub_apply,hαv]
    rw [he,hv,mul_one] at hh
    exact hh.trans herror
  have hh := norm_sub_norm_le ((α:ℂ) • v) (A v)
  have hnorm : ‖(α:ℂ) • v‖=α := by simp [norm_smul,hv,abs_of_nonneg hα]
  rw [hnorm,norm_sub_rev] at hh
  have hcol := section5_column_norm_bound A j hmax v hv
  linarith









end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (hn : 1 ≤ n)
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hL : IsSelfAdjoint L)
    (w : EuclideanSpace ℂ (Fin n)) (hw : ‖w‖=1)
    (η : ℝ) (hη : 0 ≤ η) (hη' : η ≤ 1/1000) (herror : ‖L-rankOne ℂ w w‖ ≤ η)
    (k : ℕ) (j : Fin n) (hmax : ∀ i, ‖(L^(k+1)) (section5_coordinate_ket i)‖ ≤
      ‖(L^(k+1)) (section5_coordinate_ket j)‖) :
    (1/2:ℝ)^(k+1) ≤ 2*n*‖(L^(k+1)) (section5_coordinate_ket j)‖ ∧
      ‖(L^(k+1)) (section5_coordinate_ket j)‖ ≤ (2:ℝ)^(k+1) := by
  haveI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨v,lam,hv,heigen,hmaxeig⟩ := section5_top_eigenpair_exists L hL
  have hlow := section5_tomography_rayleigh_lower L w hw η lam herror hmaxeig
  have hlam : 1/2 ≤ lam := by linarith
  have hlam0 : 0 < lam := by linarith
  have hratio : 2*(10*η) ≤ lam := by linarith
  have hpow : (2:ℝ)^(k+1)*(10*η)^(k+1) ≤ lam^(k+1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hratio _
  have htwo : (2:ℝ) ≤ (2:ℝ)^(k+1) := by
    rw [pow_succ]
    nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=k)]
  have hrho : (10*η)^(k+1) ≤ lam^(k+1)/2 := by
    have hh := mul_le_mul_of_nonneg_right htwo (pow_nonneg (by positivity : 0 ≤ 10*η) (k+1))
    linarith
  have hE := section5_tomography_power_error L hL w v hw hv η lam hη (by linarith)
    hlam hlow herror heigen k
  have hlower := section5_max_column_magnitude_lower (L^(k+1)) j hmax v hv
    (lam^(k+1)) ((10*η)^(k+1)) (pow_nonneg hlam0.le _) hrho hE
  have hLnorm : ‖L‖ ≤ 2 := by
    have hh := norm_add_le (L-rankOne ℂ w w) (rankOne ℂ w w)
    rw [sub_add_cancel,norm_rankOne,hw,one_mul] at hh
    linarith
  refine ⟨(pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hlam _).trans hlower,?_⟩
  calc
    _ ≤ ‖L^(k+1)‖*‖section5_coordinate_ket j‖ := (L^(k+1)).le_opNorm _
    _ = ‖L^(k+1)‖ := by rw [section5_coordinate_ket_norm,mul_one]
    _ ≤ ‖L‖^(k+1) := norm_pow_le _ _
    _ ≤ (2:ℝ)^(k+1) := pow_le_pow_left₀ (norm_nonneg _) hLnorm _
