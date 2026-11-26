-- Prove2me | solution 1 for section5_quantize_decode
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:55.722803+00:00
-- url     : https://prove2.me/submissions/f287d1da-5558-46ab-9069-4647083c364f

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
import Definitions.Def_Section5Verified_Section5IntegerOrientation
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Explicit public fixed-point rounding, with coordinate and normalized-vector
error guarantees. This is an encoding estimate, not an eigensolver circuit. -/





theorem section5_quantize_integer_range (f : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    0 ≤ section5_quantize_integer f x ∧ section5_quantize_integer f x < (2:ℤ)^(f+2) := by
  have hA : (0:ℝ) < 2^f := by positivity
  have hlo : -(2:ℤ)^f ≤ ⌊(2:ℝ)^f*x⌋ := by
    apply Int.le_floor.mpr
    push_cast
    nlinarith [(abs_le.mp hx).1]
  have hhi : ⌊(2:ℝ)^f*x⌋ ≤ (2:ℤ)^f := by
    have hh := Int.floor_le ((2:ℝ)^f*x)
    have hh' : ((⌊(2:ℝ)^f*x⌋:ℤ):ℝ) ≤ ((2:ℤ)^f:ℝ) := by
      push_cast
      nlinarith [(abs_le.mp hx).2]
    exact_mod_cast hh'
  have hp : (0:ℤ) < 2^f := by positivity
  have h2 : (2:ℤ)^(f+1)=2*2^f := by rw [pow_succ]; ring
  have h4 : (2:ℤ)^(f+2)=4*2^f := by rw [show f+2=f+1+1 by omega,pow_succ,h2]; ring
  unfold section5_quantize_integer
  rw [h2,h4]
  omega













end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Exact integer comparison for orientation: Gaussian grid scaling and fixed-point denominators
are positive and cancel from the sign test. -/



theorem section5_binary_half_power (ℓ : ℕ) (hℓ : 0 < ℓ) :
    (2:ℝ)^ℓ/2=((2^(ℓ-1) : ℕ) : ℝ) := by
  rcases ℓ with _ | ℓ
  · omega
  simp only [Nat.add_sub_cancel,pow_succ,Nat.cast_pow,Nat.cast_ofNat]
  ring

theorem section5_fpVal_centered_integer {ℓ : ℕ} (hℓ : 0 < ℓ) (f : ℕ) (z : Qubits ℓ) :
    fpVal ℓ f z=(section5_centered_integer z : ℝ)/(2:ℝ)^f := by
  unfold fpVal section5_centered_integer
  rw [section5_binary_half_power ℓ hℓ]
  push_cast
  rfl











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

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Widening the output by one bit permits exact sign correction even at the most
negative input endpoint of the published offset-binary fixed-point encoding. -/







theorem section5_msb_binary_value {w : ℕ} (z : Qubits w) :
    bitsToNat (section5_lsb_to_msb z)=bitsToNatLSB z := by
  have hh := section5_reversed_binary_value (section5_lsb_to_msb z)
  simpa only [section5_lsb_to_msb,Fin.rev_rev] using hh.symm

theorem section5_fpVal_nat_lsb (w f N : ℕ) (hw : 0 < w) (hN : N < 2^w) :
    fpVal w f (section5_lsb_to_msb (natToBitsLSB w N))=
      ((N:ℝ)-((2^(w-1):ℕ):ℝ))/(2:ℝ)^f := by
  rw [section5_fpVal_centered_integer hw f]
  unfold section5_centered_integer
  rw [section5_msb_binary_value,section5_bitsToNatLSB_mod,Nat.mod_eq_of_lt hN]
  push_cast
  rfl





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution (f : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    fpVal (f+2) f (section5_quantize_bits f x)=((⌊(2:ℝ)^f*x⌋:ℤ):ℝ)/(2:ℝ)^f := by
  have hr := section5_quantize_integer_range f x hx
  have hn : (section5_quantize_integer f x).toNat < 2^(f+2) := by
    exact_mod_cast (show ((section5_quantize_integer f x).toNat:ℤ)<(2:ℤ)^(f+2) by
      rw [Int.toNat_of_nonneg hr.1]; exact hr.2)
  rw [section5_quantize_bits,section5_fpVal_nat_lsb _ _ _ (by omega) hn]
  have hcast : ((section5_quantize_integer f x).toNat:ℝ)=
      (2:ℝ)^(f+1)+(⌊(2:ℝ)^f*x⌋:ℤ) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg hr.1]
    simp [section5_quantize_integer]
  rw [hcast]
  push_cast
  ring
