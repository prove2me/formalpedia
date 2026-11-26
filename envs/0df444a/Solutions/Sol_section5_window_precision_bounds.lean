-- Prove2me | solution 1 for section5_window_precision_bounds
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:06:47.095085+00:00
-- url     : https://prove2.me/submissions/282b72ec-01cf-4e14-b37e-8406ec8b7425

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
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    65536*(n:ℝ) ≤ (2:ℝ)^(section5_window_precision n) ∧
      (2:ℝ)^(section5_window_precision n) < 131072*n ∧
      section5_window_precision n ≤ n+16 := by
  have hN : 1 < 65536*n := by omega
  have hB := Nat.clog_pos (by norm_num : 1 < (2:ℕ)) hN
  have hlo := Nat.le_pow_clog (by norm_num : 1 < (2:ℕ)) (65536*n)
  have hpred := Nat.pow_pred_clog_lt_self (by norm_num : 1 < (2:ℕ)) hN
  have hupper : 2^(Nat.clog 2 (65536*n)) < 131072*n := by
    have hp : 2^(Nat.clog 2 (65536*n))=2^(Nat.clog 2 (65536*n)).pred*2 := by
      calc
        _ = 2^((Nat.clog 2 (65536*n)).pred+1) := congrArg (fun k => (2:ℕ)^k)
          (by simpa only [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hB).symm)
        _ = _ := pow_succ _ _
    rw [hp]
    omega
  refine ⟨by exact_mod_cast hlo,by exact_mod_cast hupper,?_⟩
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  norm_num
  nlinarith [Nat.lt_two_pow_self (n:=n)]
