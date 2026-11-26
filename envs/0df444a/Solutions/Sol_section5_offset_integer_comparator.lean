-- Prove2me | solution 1 for section5_offset_integer_comparator
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:19:59.306983+00:00
-- url     : https://prove2.me/submissions/b5bdc574-7efa-4e29-bcd7-aea3cca50172

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
import Theorems.Thm_section5_offset_signed_dot_circuit
import Theorems.Thm_section5_twos_complement_decode_mod
import Theorems.Thm_section5_twos_complement_residue
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! A complete signed dot-product comparator with an explicit polynomial gate bound.
The accumulator width below is deliberately generous, to make overflow impossible. -/

theorem section5_signed_residue_range (H z : ℤ) (hH : 0 < H) :
    -H ≤ section5_signed_residue H z ∧ section5_signed_residue H z < H := by
  have hlo := Int.emod_nonneg z (by positivity : 2*H ≠ 0)
  have hhi := Int.emod_lt_of_pos z (by positivity : 0 < 2*H)
  unfold section5_signed_residue
  split_ifs <;> constructor <;> omega

theorem section5_twos_complement_abs (b : ℕ) (z : Qubits (b+1)) :
    |section5_integer_bit_value (section5_twos_coefficient (b+1)) z| ≤ (2:ℤ)^b := by
  rw [section5_twos_complement_residue]
  have hh := section5_signed_residue_range ((2:ℤ)^b) (bitsToNatLSB z) (by positivity)
  exact abs_le.mpr ⟨hh.1,hh.2.le⟩





end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! Offset-binary fixed-point estimates need no physical recoding: accumulate their
ordinary binary value, then subtract the fixed midpoint times the second vector. -/













theorem section5_offset_binary_abs (a : ℕ) (z : Qubits (a+1)) :
    |(bitsToNatLSB z:ℤ)-(2:ℤ)^a| ≤ (2:ℤ)^a := by
  have hN : (bitsToNatLSB z:ℤ) < (2:ℤ)^(a+1) := by
    exact_mod_cast bitsToNatLSB_lt (a+1) z
  have hzero : (0:ℤ) ≤ bitsToNatLSB z := by positivity
  rw [pow_succ] at hN
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem section5_offset_dot_no_overflow {n a b : ℕ}
    (u : Fin n → Qubits (a+1)) (x : Fin n → Qubits (b+1)) :
    |∑ i : Fin n, ((bitsToNatLSB (u i):ℤ)-(2:ℤ)^a)*
      section5_integer_bit_value (section5_twos_coefficient (b+1)) (x i)| < (2:ℤ)^(n+a+b) := by
  calc
    _ ≤ ∑ i : Fin n, |((bitsToNatLSB (u i):ℤ)-(2:ℤ)^a)*
          section5_integer_bit_value (section5_twos_coefficient (b+1)) (x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (2:ℤ)^a*(2:ℤ)^b := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (section5_offset_binary_abs a (u i))
        (section5_twos_complement_abs b (x i)) (abs_nonneg _) (by positivity)
    _ = (n:ℤ)*(2:ℤ)^(a+b) := by simp [pow_add]
    _ < (2:ℤ)^n*(2:ℤ)^(a+b) := by
      apply mul_lt_mul_of_pos_right _ (by positivity)
      exact_mod_cast (Nat.lt_two_pow_self (n:=n))
    _ = _ := by rw [← pow_add]; congr 1; omega



end
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





theorem section5_twos_complement_nonnegative (b : ℕ) (z : Qubits (b+1)) :
    0 ≤ section5_integer_bit_value (section5_twos_coefficient (b+1)) z ↔
      z (Fin.last b)=false := by
  rw [section5_twos_complement_value]
  have hN : (bitsToNatLSB z:ℤ) < (2:ℤ)^(b+1) := by
    exact_mod_cast bitsToNatLSB_lt (b+1) z
  cases hz : z (Fin.last b) <;> simp [hz] <;> omega



theorem section5_integer_dot_sign_bit (b : ℕ) (z : Qubits (b+1)) (v : ℤ)
    (hmod : (bitsToNatLSB z : ZMod (2^(b+1)))=(v : ZMod (2^(b+1))))
    (hlo : -(2:ℤ)^b ≤ v) (hhi : v < (2:ℤ)^b) :
    0 ≤ v ↔ z (Fin.last b)=false := by
  rw [← section5_twos_complement_decode_mod b z v hmod hlo hhi]
  exact section5_twos_complement_nonnegative b z

end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
theorem solution {m n a b : ℕ}
    (u : Fin n → Fin (a+1) → Fin m) (x : Fin n → Fin (b+1) → Fin m)
    (p : Fin (n+a+b+1) ↪ Fin m) (anc : Fin ((n+a+b+1)+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, u i j ≠ t) (hxt : ∀ i j, x i j ≠ t)
    (hup : ∀ i j, u i j ∉ Set.range p) (hxp : ∀ i j, x i j ∉ Set.range p)
    (hxa : ∀ i j k, x i j ≠ anc k) :
    ∃ circ : Circuit gatesRev m, circ.size ≤
        (16*(n+a+b+1)+6)*(n*(a+2)*(b+1)) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i, z (p i)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          (0 ≤ ∑ i : Fin n, ((bitsToNatLSB (z ∘ u i):ℤ)-(2:ℤ)^a)*
            section5_integer_bit_value (section5_twos_coefficient (b+1)) (z ∘ x i) ↔
              z' (p (Fin.last (n+a+b)))=false) := by
  obtain ⟨circ,hcirc,hact⟩ := section5_offset_signed_dot_circuit u x p anc hpa t htp hta hut hxt hup hxp hxa
  refine ⟨circ,hcirc,?_⟩
  intro z hzt hzanc hz0
  obtain ⟨z',hz',hoff,hvalue⟩ := hact z hzt hzanc
  have hzero : bitsToNatLSB (z ∘ p)=0 := by simp [bitsToNatLSB,Function.comp_apply,hz0]
  rw [hzero,Nat.cast_zero,zero_add] at hvalue
  have hbound := section5_offset_dot_no_overflow (fun i => z ∘ u i) (fun i => z ∘ x i)
  exact ⟨z',hz',hoff,section5_integer_dot_sign_bit (n+a+b) (z' ∘ p) _ hvalue
    (abs_lt.mp hbound).1.le (abs_lt.mp hbound).2⟩
