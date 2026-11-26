-- Prove2me | solution 1 for section5_signed_integer_dot_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:11:36.160131+00:00
-- url     : https://prove2.me/submissions/e0f6fa08-dbe4-4731-901a-638b45aa75bd

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5BilinearAccumulator
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Mathlib
import Theorems.Thm_section5_bilinear_accumulator_circuit
import Theorems.Thm_section5_bilinear_accumulator_value
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! A product of two input bits can control the linear-size modular accumulator.
The temporary AND bit and all arithmetic workspace are returned to zero. -/







theorem section5_bilinear_step_off {m w : ℕ} (p : Fin w ↪ Fin m)
    (a b : Fin m) (v : ℕ) (z : Qubits m) (j : Fin m) (hj : j ∉ Set.range p) :
    section5_bilinear_step p a b v z j=z j := by
  unfold section5_bilinear_step
  split_ifs
  · exact updateOn_apply_not_mem p z _ hj
  · rfl







theorem section5_bilinear_eval_off {m w : ℕ} (p : Fin w ↪ Fin m)
    (ops : List (Section5BilinearTerm m)) (z : Qubits m) (j : Fin m) (hj : j ∉ Set.range p) :
    section5_bilinear_eval p ops z j=z j := by
  induction ops generalizing z with
  | nil => rfl
  | cons a ops ih =>
    exact (ih _).trans (section5_bilinear_step_off p a.a a.b a.weight z j hj)









end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! Signed binary dot products are compiled by reducing each signed coefficient modulo
the accumulator modulus. Negative coefficients require no additional circuit gates. -/



theorem section5_residue_coefficient_cast (w : ℕ) (v : ℤ) :
    (section5_residue_coefficient w v : ZMod (2^w))=(v : ZMod (2^w)) := by
  have hnonneg : 0 ≤ v%((2^w:ℕ):ℤ) := Int.emod_nonneg _ (by positivity)
  have hh := congrArg (fun x : ℤ => (x : ZMod (2^w))) (Int.toNat_of_nonneg hnonneg)
  simpa only [section5_residue_coefficient,Int.cast_natCast,ZMod.intCast_mod] using hh



theorem section5_signed_binary_product_expansion {a b : ℕ}
    (c : Fin a → ℤ) (d : Fin b → ℤ) (x : Qubits a) (y : Qubits b) :
    section5_integer_bit_value c x*section5_integer_bit_value d y=
      ∑ i : Fin a, ∑ j : Fin b, if x i && y j then c i*d j else 0 := by
  unfold section5_integer_bit_value
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  cases hx : x i <;> cases hy : y j <;> simp [hx,hy]



theorem section5_signed_dot_terms_length {m n a b : ℕ} (w : ℕ)
    (c : Fin a → ℤ) (d : Fin b → ℤ)
    (u : Fin n → Fin a → Fin m) (x : Fin n → Fin b → Fin m) :
    (section5_signed_dot_terms w c d u x).length=n*a*b := by
  simp [section5_signed_dot_terms,Nat.mul_assoc]

theorem section5_signed_dot_terms_sum {m n a b : ℕ} (w : ℕ)
    (c : Fin a → ℤ) (d : Fin b → ℤ)
    (u : Fin n → Fin a → Fin m) (x : Fin n → Fin b → Fin m) (z : Qubits m) :
    (section5_bilinear_sum (section5_signed_dot_terms w c d u x) z : ZMod (2^w))=
      ((∑ i : Fin n, section5_integer_bit_value c (z ∘ u i)*
        section5_integer_bit_value d (z ∘ x i) : ℤ) : ZMod (2^w)) := by
  simp only [section5_bilinear_sum,section5_signed_dot_terms,List.map_map,
    Finset.sum_map_toList,Function.comp_apply,Fintype.sum_prod_type]
  simp_rw [section5_signed_binary_product_expansion]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Function.comp_apply]
  by_cases hh : (z (u i j) && z (x i k))=true
  · simp only [hh,↓reduceIte]
    simpa only [Int.cast_mul] using section5_residue_coefficient_cast w (c j*d k)
  · simp only [hh,Bool.false_eq_true,↓reduceIte,Nat.cast_zero,Int.cast_zero]



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
theorem solution {m n a b w : ℕ}
    (c : Fin a → ℤ) (d : Fin b → ℤ)
    (u : Fin n → Fin a → Fin m) (x : Fin n → Fin b → Fin m)
    (p : Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, u i j ≠ t) (hxt : ∀ i j, x i j ≠ t)
    (hup : ∀ i j, u i j ∉ Set.range p) (hxp : ∀ i j, x i j ∉ Set.range p) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ (16*w+6)*(n*a*b) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          (bitsToNatLSB (z' ∘ p) : ZMod (2^w))=
            (bitsToNatLSB (z ∘ p) : ZMod (2^w))+
              ((∑ i : Fin n, section5_integer_bit_value c (z ∘ u i)*
                section5_integer_bit_value d (z ∘ x i) : ℤ) : ZMod (2^w)) := by
  classical
  have hctrl : ∀ v ∈ section5_signed_dot_terms w c d u x,
      v.a ≠ t ∧ v.b ≠ t ∧ v.a ∉ Set.range p ∧ v.b ∉ Set.range p := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
    exact ⟨hut _ _,hxt _ _,hup _ _,hxp _ _⟩
  obtain ⟨circ,hcirc,hact⟩ := section5_bilinear_accumulator_circuit p anc hpa t htp hta
    (section5_signed_dot_terms w c d u x) hctrl
  refine ⟨circ,?_,?_⟩
  · rwa [section5_signed_dot_terms_length] at hcirc
  · intro z hzt hzanc
    refine ⟨section5_bilinear_eval p (section5_signed_dot_terms w c d u x) z,
      hact z hzt hzanc,?_,?_⟩
    · exact fun j hj => section5_bilinear_eval_off p _ z j hj
    · rw [section5_bilinear_accumulator_value p _ (fun v hv => (hctrl v hv).2.2) z,
        ZMod.natCast_mod,Nat.cast_add,section5_signed_dot_terms_sum]
