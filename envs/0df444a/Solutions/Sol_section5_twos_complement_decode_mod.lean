-- Prove2me | solution 1 for section5_twos_complement_decode_mod
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:07:48.859764+00:00
-- url     : https://prove2.me/submissions/7a628ff4-a564-45e2-90f2-c7565dd63f5f

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
import Theorems.Thm_section5_twos_complement_residue
section
set_option autoImplicit false

/-! Signed middle-bit windows. The discarded low bits cause a bounded rounding error;
the omitted high bits are irrelevant inside the represented interval. -/



theorem section5_signed_residue_exact (H z : ℤ) (hH : 0 < H) (hlo : -H ≤ z) (hhi : z < H) :
    section5_signed_residue H z=z := by
  unfold section5_signed_residue
  by_cases hz : 0 ≤ z
  · have hr : z % (2*H)=z := Int.emod_eq_of_lt hz (by omega)
    rw [hr,if_pos hhi]
  · have hr : (z+2*H) % (2*H)=z+2*H := Int.emod_eq_of_lt (by omega) (by omega)
    have hzmod : z % (2*H)=z+2*H := by
      simpa only [Int.add_emod,Int.emod_self,add_zero,Int.emod_emod] using hr
    rw [hzmod,if_neg (by omega)]
    omega











end
set_option autoImplicit false
open QAlgorithms Thm49Primitives
theorem solution (b : ℕ) (z : Qubits (b+1)) (v : ℤ)
    (hmod : (bitsToNatLSB z : ZMod (2^(b+1)))=(v : ZMod (2^(b+1))))
    (hlo : -(2:ℤ)^b ≤ v) (hhi : v < (2:ℤ)^b) :
    section5_integer_bit_value (section5_twos_coefficient (b+1)) z=v := by
  have hm : (bitsToNatLSB z:ℤ)%((2^(b+1):ℕ):ℤ)=v%((2^(b+1):ℕ):ℤ) :=
    (ZMod.intCast_eq_intCast_iff' _ _ _).mp (by simpa only [Int.cast_natCast] using hmod)
  have hp : ((2^(b+1):ℕ):ℤ)=2*(2:ℤ)^b := by push_cast; rw [pow_succ]; ring
  rw [hp] at hm
  rw [section5_twos_complement_residue]
  have heq : section5_signed_residue ((2:ℤ)^b) (bitsToNatLSB z)=
      section5_signed_residue ((2:ℤ)^b) v := by
    simp only [section5_signed_residue,hm]
  rw [heq]
  exact section5_signed_residue_exact _ v (by positivity) hlo hhi
