-- Prove2me | solution 1 for section5_twos_complement_residue
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:02:13.896799+00:00
-- url     : https://prove2.me/submissions/afd06063-7f8b-4b9f-a451-042c04bb36a9

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
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5SignedWindow
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
section
set_option autoImplicit false

open QAlgorithms Thm49Primitives

/-! The bounded-window integer decoder is exactly the standard signed binary
linear form. This connects the window analysis to the signed dot-product circuit. -/



theorem section5_twos_complement_value (b : ℕ) (z : Qubits (b+1)) :
    section5_integer_bit_value (section5_twos_coefficient (b+1)) z=
      (bitsToNatLSB z : ℤ)-(if z (Fin.last b) then (2:ℤ)^(b+1) else 0) := by
  unfold section5_integer_bit_value section5_twos_coefficient bitsToNatLSB
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,Nat.add_left_inj,↓reduceIte]
  push_cast
  have hi (i : Fin b) : i.val ≠ b := by omega
  simp_rw [if_neg (hi _)]
  cases hz : z (Fin.last b) <;> simp [hz,pow_succ] <;> ring











end
set_option autoImplicit false
open QAlgorithms Thm49Primitives
theorem solution (b : ℕ) (z : Qubits (b+1)) :
    section5_integer_bit_value (section5_twos_coefficient (b+1)) z=
      section5_signed_residue ((2:ℤ)^b) (bitsToNatLSB z) := by
  rw [section5_twos_complement_value]
  have hN : (bitsToNatLSB z:ℤ) < 2*(2:ℤ)^b := by
    have hh := bitsToNatLSB_lt (b+1) z
    exact_mod_cast (show bitsToNatLSB z < 2*2^b by simpa [pow_succ,Nat.mul_comm] using hh)
  have hmod : (bitsToNatLSB z:ℤ)%(2*(2:ℤ)^b)=bitsToNatLSB z :=
    Int.emod_eq_of_lt (by positivity) hN
  unfold section5_signed_residue
  rw [hmod]
  have hsmall := bitsToNatLSB_lt b (fun i => z i.castSucc)
  have hval : bitsToNatLSB z=bitsToNatLSB (fun i : Fin b => z i.castSucc)+
      (if z (Fin.last b) then 2^b else 0) := by
    simp only [bitsToNatLSB,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last]
  rw [hval]
  push_cast at *
  cases hz : z (Fin.last b)
  · simp only [hz,Bool.false_eq_true,↓reduceIte,add_zero,sub_zero]
    rw [if_pos (by exact_mod_cast hsmall)]
  · simp only [hz,↓reduceIte]
    have hh : (0:ℤ) ≤ bitsToNatLSB (fun i : Fin b => z i.castSucc) := by positivity
    rw [if_neg (by omega),pow_succ]
    ring
