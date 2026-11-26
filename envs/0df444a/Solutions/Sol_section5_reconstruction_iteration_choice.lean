-- Prove2me | solution 1 for section5_reconstruction_iteration_choice
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:58:23.308387+00:00
-- url     : https://prove2.me/submissions/afd76fe8-54b2-46e2-bd75-300964ec274a

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
import Definitions.Def_Section5Verified_Section5ReconstructionPrecision
import Mathlib
section
set_option autoImplicit false



theorem section5_binary_precision_sufficient (x : ℝ) :
    x ≤ (2:ℝ)^(section5_binary_precision x) := by
  have hceil : x ≤ (⌈x⌉₊:ℝ) := Nat.le_ceil x
  have hpow : (⌈x⌉₊:ℝ) ≤ (2:ℝ)^(section5_binary_precision x) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) ⌈x⌉₊
  exact hceil.trans hpow

theorem section5_binary_precision_polynomial_bound (x : ℝ) (hx : 0 ≤ x) :
    (section5_binary_precision x:ℝ) < x+1 := by
  have hh : section5_binary_precision x ≤ ⌈x⌉₊ :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=⌈x⌉₊)).le
  exact (by exact_mod_cast hh : (section5_binary_precision x:ℝ) ≤ (⌈x⌉₊:ℝ)).trans_lt
    (Nat.ceil_lt_add_one hx)



end
set_option autoImplicit false
theorem solution (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    400*(n:ℝ)/ε ≤ (2:ℝ)^(section5_binary_precision (400*n/ε)+1) ∧
      (section5_binary_precision (400*n/ε):ℝ) < 400*n/ε+1 := by
  constructor
  · have hh := section5_binary_precision_sufficient (400*n/ε)
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (section5_binary_precision (400*n/ε))]
  · exact section5_binary_precision_polynomial_bound _ (by positivity)
