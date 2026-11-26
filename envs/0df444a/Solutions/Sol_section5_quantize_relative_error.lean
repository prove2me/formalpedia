-- Prove2me | solution 1 for section5_quantize_relative_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:01:39.655904+00:00
-- url     : https://prove2.me/submissions/73f7210d-20f7-4804-84b5-7082eedfb66e

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
import Definitions.Def_Section5Verified_Section5FixedPointQuantization
import Mathlib
import Theorems.Thm_section5_coordinate_approximation_norm
import Theorems.Thm_section5_normalize_perturbation
import Theorems.Thm_section5_quantize_decode
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Explicit public fixed-point rounding, with coordinate and normalized-vector
error guarantees. This is an encoding estimate, not an eigensolver circuit. -/









theorem section5_quantize_error (f : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |fpVal (f+2) f (section5_quantize_bits f x)-x| < 1/(2:ℝ)^f := by
  rw [section5_quantize_decode f x hx]
  have hA : (0:ℝ) < 2^f := by positivity
  have hlo := Int.floor_le ((2:ℝ)^f*x)
  have hhi := Int.lt_floor_add_one ((2:ℝ)^f*x)
  have hle : ((⌊(2:ℝ)^f*x⌋:ℤ):ℝ)/(2:ℝ)^f ≤ x :=
    (div_le_iff₀ hA).mpr (by nlinarith)
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hle)]
  apply (lt_div_iff₀ hA).mpr
  have hmul : ((⌊(2:ℝ)^f*x⌋:ℤ):ℝ)/(2:ℝ)^f*(2:ℝ)^f=
      (⌊(2:ℝ)^f*x⌋:ℤ) := div_mul_cancel₀ _ hA.ne'
  nlinarith



theorem section5_quantize_vector_error {n : ℕ} (f : ℕ)
    (r : EuclideanSpace ℝ (Fin n)) (hr : ∀ i, |r i| ≤ 1) :
    ‖section5_quantize_vector f r-r‖ ≤ Real.sqrt n/(2:ℝ)^f := by
  have h := section5_coordinate_approximation_norm (section5_quantize_vector f r) r
    (1/(2:ℝ)^f) (by positivity) (fun i => (section5_quantize_error f (r i) (hr i)).le)
  simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using h





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution {n : ℕ} (hn : 1 ≤ n) (f : ℕ)
    (ε b : ℝ) (hε : 0 < ε) (hε' : ε < 1) (hb : 0 < b)
    (hprec : 48*(n:ℝ)/(b*ε) ≤ (2:ℝ)^f)
    (r : EuclideanSpace ℝ (Fin n)) (hr : ∀ i, |r i| ≤ 1) (hnorm : b ≤ ‖r‖) :
    section5_quantize_vector f r ≠ 0 ∧
      ‖NormedSpace.normalize (section5_quantize_vector f r)-NormedSpace.normalize r‖ ≤ ε/24 := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hA : (0:ℝ) < 2^f := by positivity
  have hsqrt : Real.sqrt n ≤ n := by
    have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ n)
    nlinarith [Real.sqrt_nonneg (n:ℝ)]
  have herr : ‖section5_quantize_vector f r-r‖ ≤ b*ε/48 := by
    have hq := section5_quantize_vector_error f r hr
    have hp := (div_le_iff₀ (mul_pos hb hε)).mp hprec
    have hd : Real.sqrt n/(2:ℝ)^f ≤ b*ε/48 := by
      apply (div_le_iff₀ hA).mpr
      nlinarith
    exact hq.trans hd
  have hr0 : r ≠ 0 := by intro h; rw [h,norm_zero] at hnorm; linarith
  have hq0 : section5_quantize_vector f r ≠ 0 := by
    intro h
    rw [h,zero_sub,norm_neg] at herr
    have hh := mul_lt_mul_of_pos_left hε' hb
    nlinarith
  refine ⟨hq0,?_⟩
  have hh := section5_normalize_perturbation (section5_quantize_vector f r) r hq0 hr0
  apply hh.trans
  apply (div_le_iff₀ (norm_pos_iff.mpr hr0)).mpr
  have hmul := mul_le_mul_of_nonneg_left hnorm hε.le
  nlinarith
