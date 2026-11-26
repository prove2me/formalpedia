-- Prove2me | solution 1 for section5_dyadic_floor
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:10:26.987197+00:00
-- url     : https://prove2.me/submissions/14c431b2-7d6c-40f6-8a08-888234bf590f

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
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution (S f : ℕ) (hf : f ≤ S) (v : ℤ) :
    ⌊(2:ℝ)^f*(((2:ℝ)^S)⁻¹*(v:ℝ))⌋=v/(2:ℤ)^(S-f) := by
  have hpow : (2:ℝ)^S=(2:ℝ)^f*(2:ℝ)^(S-f) := by
    rw [← pow_add,Nat.add_sub_of_le hf]
  have heq : (2:ℝ)^f*(((2:ℝ)^S)⁻¹*(v:ℝ))=(v:ℝ)/((2:ℤ)^(S-f):ℝ) := by
    push_cast
    rw [hpow]
    field_simp
  rw [heq]
  simpa only [Int.cast_pow,Int.cast_ofNat,Int.floor_intCast] using
    (Int.floor_div_cast_of_nonneg (k:=ℝ) (n:=(2:ℤ)^(S-f)) (by positivity) (v:ℝ))
