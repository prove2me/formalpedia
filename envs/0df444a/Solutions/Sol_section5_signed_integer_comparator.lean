-- Prove2me | solution 1 for section5_signed_integer_comparator
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:14:11.494702+00:00
-- url     : https://prove2.me/submissions/3b85a80a-54d2-47d9-aa39-936c8ed28865

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
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_signed_dot_no_overflow
import Theorems.Thm_section5_signed_integer_dot_circuit
import Theorems.Thm_section5_twos_complement_decode_mod
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
    (hup : ∀ i j, u i j ∉ Set.range p) (hxp : ∀ i j, x i j ∉ Set.range p) :
    ∃ circ : Circuit gatesRev m, circ.size ≤
        (16*(n+a+b+1)+6)*(n*(a+1)*(b+1)) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i, z (p i)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          (0 ≤ ∑ i : Fin n,
            section5_integer_bit_value (section5_twos_coefficient (a+1)) (z ∘ u i)*
            section5_integer_bit_value (section5_twos_coefficient (b+1)) (z ∘ x i) ↔
              z' (p (Fin.last (n+a+b)))=false) := by
  obtain ⟨circ,hcirc,hact⟩ := section5_signed_integer_dot_circuit
    (section5_twos_coefficient (a+1)) (section5_twos_coefficient (b+1)) u x
    p anc hpa t htp hta hut hxt hup hxp
  refine ⟨circ,hcirc,?_⟩
  intro z hzt hzanc hz0
  obtain ⟨z',hz',hoff,hvalue⟩ := hact z hzt hzanc
  have hzero : bitsToNatLSB (z ∘ p)=0 := by simp [bitsToNatLSB,Function.comp_apply,hz0]
  rw [hzero,Nat.cast_zero,zero_add] at hvalue
  have hbound := section5_signed_dot_no_overflow (fun i => z ∘ u i) (fun i => z ∘ x i)
  refine ⟨z',hz',hoff,?_⟩
  exact section5_integer_dot_sign_bit (n+a+b) (z' ∘ p) _ hvalue
    (abs_lt.mp hbound).1.le (abs_lt.mp hbound).2
