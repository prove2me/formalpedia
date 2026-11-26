-- Prove2me | solution 1 for section5_scaled_power_output_bounds
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:53.112287+00:00
-- url     : https://prove2.me/submissions/a653aa8c-b7ac-41cc-a6d4-773bcd934e1b

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
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Mathlib
section
set_option autoImplicit false







theorem section5_parts_norm_sq {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖section5_real_part v‖^2 + ‖section5_imag_part v‖^2 = ‖v‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, section5_real_part, section5_imag_part,
    WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem section5_real_part_contraction {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖section5_real_part v‖ ≤ ‖v‖ := by
  have hh : ‖section5_real_part v‖^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i hi
    change ‖(v i).re‖^2 ≤ ‖v i‖^2
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  nlinarith [norm_nonneg (section5_real_part v), norm_nonneg v]

theorem section5_imag_part_contraction {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    ‖section5_imag_part v‖ ≤ ‖v‖ := by
  have hh : ‖section5_imag_part v‖^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i hi
    change ‖(v i).im‖^2 ≤ ‖v i‖^2
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
  nlinarith [norm_nonneg (section5_imag_part v), norm_nonneg v]



end
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Uniform magnitude and output-precision bounds for the powered-column decoder.
They avoid choosing an output precision that depends on an unknown target state. -/





theorem section5_larger_part_magnitude {n : ℕ} (y : EuclideanSpace ℂ (Fin n)) :
    (2/3)*‖y‖ ≤ ‖section5_larger_real_part y‖ ∧ ‖section5_larger_real_part y‖ ≤ ‖y‖ := by
  have hh := section5_parts_norm_sq y
  unfold section5_larger_real_part
  split_ifs with h
  · refine ⟨?_,section5_real_part_contraction y⟩
    nlinarith [norm_nonneg y,norm_nonneg (section5_real_part y),norm_nonneg (section5_imag_part y)]
  · refine ⟨?_,section5_imag_part_contraction y⟩
    nlinarith [norm_nonneg y,norm_nonneg (section5_real_part y),norm_nonneg (section5_imag_part y)]





end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (hn : 1 ≤ n)
    (y : EuclideanSpace ℂ (Fin n)) (t : ℕ)
    (hlo : (1/2:ℝ)^t ≤ 2*n*‖y‖) (hhi : ‖y‖ ≤ (2:ℝ)^t) :
    let r := ((2:ℝ)^t)⁻¹ • section5_larger_real_part y
    1/(3*n*(4:ℝ)^t) ≤ ‖r‖ ∧ ‖r‖ ≤ 1 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have htwo : (0:ℝ) < 2^t := by positivity
  have hfour : (4:ℝ)^t=((2:ℝ)^t)^2 := by
    calc
      (4:ℝ)^t = ((2:ℝ)^2)^t := by norm_num
      _ = ((2:ℝ)^t)^2 := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
  have hhalf : (1/2:ℝ)^t=((2:ℝ)^t)⁻¹ := by rw [div_pow,one_pow,one_div]
  have hp := section5_larger_part_magnitude y
  change _ ≤ ‖((2:ℝ)^t)⁻¹ • section5_larger_real_part y‖ ∧ _
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr htwo.le)]
  constructor
  · have hnormy : (1/2:ℝ)^t/(2*n) ≤ ‖y‖ :=
      (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hlo)
    have hid : 1/(3*n*(4:ℝ)^t)=((2:ℝ)^t)⁻¹*((2/3)*((1/2:ℝ)^t/(2*n))) := by
      rw [hfour,hhalf]
      field_simp
    rw [hid]
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hnormy (by norm_num)).trans hp.1) (inv_nonneg.mpr htwo.le)
  · have hh := mul_le_mul_of_nonneg_left (hp.2.trans hhi) (inv_nonneg.mpr htwo.le)
    simpa only [inv_mul_cancel₀ htwo.ne'] using hh
