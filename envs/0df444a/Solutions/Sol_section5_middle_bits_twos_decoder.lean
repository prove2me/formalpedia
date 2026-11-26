-- Prove2me | solution 1 for section5_middle_bits_twos_decoder
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:09.663992+00:00
-- url     : https://prove2.me/submissions/5d978368-47fe-49b5-87fc-28dfa7c3fcaa

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
import Definitions.Def_Section5Verified_Section5IntegerOrientation
import Definitions.Def_Section5Verified_Section5MiddleBits
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5SignedWindow
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_twos_complement_residue
section
set_option autoImplicit false

/-! Signed middle-bit windows. The discarded low bits cause a bounded rounding error;
the omitted high bits are irrelevant inside the represented interval. -/













theorem section5_signed_residue_periodic (H z k : ℤ) :
    section5_signed_residue H (z+k*(2*H))=section5_signed_residue H z := by
  simp [section5_signed_residue,Int.add_emod]

end
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

/-! A bounded signed window of the lattice integer gives a precision-independent
Gaussian coordinate approximation. -/









theorem section5_window_ignores_center_offset (P H z k : ℤ) (hP : P ≠ 0) :
    section5_window_truncate P H (z-k*(2*H)*P)=section5_window_truncate P H z := by
  unfold section5_window_truncate
  rw [Int.sub_mul_ediv_right _ _ hP]
  congr 1
  convert section5_signed_residue_periodic H (z/P) (-k) using 1 <;> ring

end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! A clean reversible accumulator for an arbitrary binary weighted sum. The gate count
is linear in the accumulator width and the number of summands. -/











theorem section5_bitsToNatLSB_mod (w val : ℕ) :
    bitsToNatLSB (natToBitsLSB w val)=val%2^w := by
  have heq : natToBitsLSB w val=natToBitsLSB w (val%2^w) := by
    funext i
    simp [natToBitsLSB,Nat.testBit_mod_two_pow,i.isLt]
  rw [heq]
  exact bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))





end
section
set_option autoImplicit false

open QAlgorithms Thm49Primitives

/-! Exact extraction of a bounded window from the published most-significant-bit-first
register encoding. This only reads the selected wires, regardless of the full precision. -/

theorem section5_reversed_binary_value {q : ℕ} (z : Qubits q) :
    bitsToNatLSB (fun i => z i.rev)=bitsToNat z := by
  unfold bitsToNatLSB bitsToNat
  calc
    _ = ∑ i : Fin q, if z i.rev then 2^(q-1-i.rev.val) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have heq : q-1-i.rev.val=i.val := by simp only [Fin.val_rev]; omega
      rw [heq]
    _ = _ := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin q))
      (fun i : Fin q => if z i then (2:ℕ)^(q-1-i.val) else 0)

theorem section5_read_binary_bit {q : ℕ} (z : Qubits q) (i : Fin q) :
    (bitsToNat z).testBit i.val=z i.rev := by
  have hh := congrFun (natToBitsLSB_bitsToNatLSB (fun i : Fin q => z i.rev)) i
  simpa only [section5_reversed_binary_value,natToBitsLSB] using hh



theorem section5_middle_bits_encoding {q : ℕ} (z : Qubits q) (s b : ℕ) (h : s+b ≤ q) :
    section5_middle_bits z s b h=natToBitsLSB b (bitsToNat z/2^s) := by
  funext i
  have hh := section5_read_binary_bit z ⟨s+i.val,by omega⟩
  simpa only [section5_middle_bits,natToBitsLSB,Nat.testBit_div_two_pow,Nat.add_comm] using hh.symm

theorem section5_middle_bits_value {q : ℕ} (z : Qubits q) (s b : ℕ) (h : s+b ≤ q) :
    bitsToNatLSB (section5_middle_bits z s b h)=(bitsToNat z/2^s)%2^b := by
  rw [section5_middle_bits_encoding,section5_bitsToNatLSB_mod]



theorem section5_middle_bits_centered_window {q : ℕ} (z : Qubits q)
    (s b : ℕ) (h : s+b ≤ q-1) (H : ℤ) (hb : (2:ℤ)^b=2*H) :
    section5_window_truncate ((2:ℤ)^s) H (section5_centered_integer z)=
      section5_window_truncate ((2:ℤ)^s) H (bitsToNat z) := by
  have hpow : ((2^(q-1):ℕ):ℤ)=(2:ℤ)^(q-1-(s+b))*(2*H)*(2:ℤ)^s := by
    rw [Nat.cast_pow,Nat.cast_ofNat,← hb,← pow_add,← pow_add]
    congr 1
    omega
  unfold section5_centered_integer
  rw [hpow]
  exact section5_window_ignores_center_offset ((2:ℤ)^s) H (bitsToNat z)
    ((2:ℤ)^(q-1-(s+b))) (by positivity)





end
set_option autoImplicit false
open QAlgorithms Thm49Primitives
theorem solution {q : ℕ} (z : Qubits q)
    (s b : ℕ) (h : s+(b+1) ≤ q-1) :
    section5_window_truncate ((2:ℤ)^s) ((2:ℤ)^b) (section5_centered_integer z)=
      (2:ℤ)^s*section5_integer_bit_value (section5_twos_coefficient (b+1))
        (section5_middle_bits z s (b+1) (by omega)) := by
  have hpow : (2:ℤ)^(b+1)=2*(2:ℤ)^b := by rw [pow_succ]; ring
  rw [section5_middle_bits_centered_window z s (b+1) h _ hpow,
    section5_twos_complement_residue,section5_middle_bits_value]
  unfold section5_window_truncate section5_signed_residue
  have hm : ((bitsToNat z/2^s%2^(b+1):ℕ):ℤ)=
      ((bitsToNat z:ℤ)/(2:ℤ)^s)%(2*(2:ℤ)^b) := by
    rw [← hpow]
    push_cast
    rfl
  rw [hm]
  simp only [Int.emod_emod]
