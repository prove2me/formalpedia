-- Prove2me | solution 1 for section5_signed_fixed_point_output
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:54.351839+00:00
-- url     : https://prove2.me/submissions/0eaf3a55-32e1-4e9d-9f0a-4dc27188752e

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
import Definitions.Def_Section5Verified_Section5IntegerOrientation
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Mathlib
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



theorem section5_signed_output_range (a N : ℕ) (hN : N < 2^(a+1)) (flip : Bool) :
    section5_signed_output_integer a N flip < 2^(a+2) := by
  have hp : 0 < 2^a := Nat.two_pow_pos a
  rw [pow_succ] at hN
  rw [show a+2=a+1+1 by omega,pow_succ,pow_succ]
  unfold section5_signed_output_integer
  cases flip <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega



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
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution (a f : ℕ) (z : Qubits (a+1)) (flip : Bool) :
    fpVal (a+2) f
      (section5_lsb_to_msb (natToBitsLSB (a+2) (section5_signed_output_integer a (bitsToNat z) flip)))=
        if flip then -fpVal (a+1) f z else fpVal (a+1) f z := by
  have hN : bitsToNat z < 2^(a+1) := by
    rw [← bitsEquivFin_apply]
    exact (bitsEquivFin (a+1) z).isLt
  rw [section5_fpVal_nat_lsb (a+2) f _ (by omega) (section5_signed_output_range a _ hN flip),
    section5_fpVal_centered_integer (by omega) f]
  unfold section5_centered_integer section5_signed_output_integer
  simp only [Nat.add_sub_cancel,Nat.add_sub_cancel_left,Nat.reduceSubDiff,
    Nat.cast_pow,Nat.cast_ofNat]
  have hsub : bitsToNat z ≤ 3*2^a := by rw [pow_succ] at hN; omega
  cases flip
  · simp only [Bool.false_eq_true,↓reduceIte,Nat.cast_add,Int.cast_sub,Int.cast_natCast,
      Nat.cast_pow,Nat.cast_ofNat,pow_succ]
    push_cast
    ring
  · simp only [↓reduceIte,Nat.cast_sub hsub,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
      Int.cast_sub,Int.cast_natCast,pow_succ]
    push_cast
    ring
