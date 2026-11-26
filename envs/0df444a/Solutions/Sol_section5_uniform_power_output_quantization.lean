-- Prove2me | solution 1 for section5_uniform_power_output_quantization
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:08:34.102824+00:00
-- url     : https://prove2.me/submissions/d1f00a4d-71c4-4add-af7d-8d4069162a31

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
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Mathlib
import Theorems.Thm_section5_quantize_relative_error
import Theorems.Thm_section5_scaled_power_output_bounds
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (hn : 1 ≤ n)
    (y : EuclideanSpace ℂ (Fin n)) (t f : ℕ)
    (hlo : (1/2:ℝ)^t ≤ 2*n*‖y‖) (hhi : ‖y‖ ≤ (2:ℝ)^t)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hprec : 144*(n:ℝ)^2*(4:ℝ)^t/ε ≤ (2:ℝ)^f) :
    let r := ((2:ℝ)^t)⁻¹ • section5_larger_real_part y
    section5_quantize_vector f r ≠ 0 ∧
      ‖NormedSpace.normalize (section5_quantize_vector f r)-NormedSpace.normalize r‖ ≤ ε/24 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨hrlo,hrhi⟩ := section5_scaled_power_output_bounds hn y t hlo hhi
  have hcoord : ∀ i, |(((2:ℝ)^t)⁻¹ • section5_larger_real_part y) i| ≤ 1 := by
    intro i
    have hh := PiLp.norm_apply_le (((2:ℝ)^t)⁻¹ • section5_larger_real_part y) i
    rw [Real.norm_eq_abs] at hh
    exact hh.trans hrhi
  apply section5_quantize_relative_error hn f ε (1/(3*n*(4:ℝ)^t)) hε hε' (by positivity)
    _ _ hcoord hrlo
  convert hprec using 1
  field_simp
  ring
