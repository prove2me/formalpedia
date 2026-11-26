-- Prove2me | solution 1 for section5_unsigned_integer_dot_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:11:37.840116+00:00
-- url     : https://prove2.me/submissions/581875eb-4a9a-4116-94f2-9015846d218b

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
import Definitions.Def_Section5Verified_Section5IntegerDotCircuit
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







theorem section5_binary_product_expansion {a b : ℕ} (x : Qubits a) (y : Qubits b) :
    bitsToNatLSB x*bitsToNatLSB y=
      ∑ i : Fin a, ∑ j : Fin b, if x i && y j then 2^(i.val+j.val) else 0 := by
  unfold bitsToNatLSB
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  cases hx : x i <;> cases hy : y j <;> simp [hx,hy]

end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! An actual NOT/CNOT/Toffoli circuit for a binary integer dot product. The input
registers are preserved and the arithmetic and AND workspace is cleaned. -/



theorem section5_dot_terms_length {m n a b : ℕ}
    (u : Fin n → Fin a → Fin m) (x : Fin n → Fin b → Fin m) :
    (section5_dot_terms u x).length=n*a*b := by
  simp [section5_dot_terms,Nat.mul_assoc]

theorem section5_dot_terms_sum {m n a b : ℕ}
    (u : Fin n → Fin a → Fin m) (x : Fin n → Fin b → Fin m) (z : Qubits m) :
    section5_bilinear_sum (section5_dot_terms u x) z=
      ∑ i : Fin n, bitsToNatLSB (z ∘ u i)*bitsToNatLSB (z ∘ x i) := by
  simp only [section5_bilinear_sum,section5_dot_terms,List.map_map,Finset.sum_map_toList,
    Function.comp_apply,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  exact (section5_binary_product_expansion (z ∘ u i) (z ∘ x i)).symm



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
theorem solution {m n a b w : ℕ}
    (u : Fin n → Fin a → Fin m) (x : Fin n → Fin b → Fin m)
    (p : Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, u i j ≠ t) (hxt : ∀ i j, x i j ≠ t)
    (hup : ∀ i j, u i j ∉ Set.range p) (hxp : ∀ i j, x i j ∉ Set.range p) :
    ∃ c : Circuit gatesRev m, c.size ≤ (16*w+6)*(n*a*b) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range p → z' j=z j) ∧
          bitsToNatLSB (z' ∘ p)=
            (bitsToNatLSB (z ∘ p)+
              ∑ i : Fin n, bitsToNatLSB (z ∘ u i)*bitsToNatLSB (z ∘ x i))%2^w := by
  classical
  have hctrl : ∀ v ∈ section5_dot_terms u x,
      v.a ≠ t ∧ v.b ≠ t ∧ v.a ∉ Set.range p ∧ v.b ∉ Set.range p := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
    exact ⟨hut _ _,hxt _ _,hup _ _,hxp _ _⟩
  obtain ⟨c,hc,hact⟩ := section5_bilinear_accumulator_circuit p anc hpa t htp hta
    (section5_dot_terms u x) hctrl
  refine ⟨c,?_,?_⟩
  · rwa [section5_dot_terms_length] at hc
  · intro z hzt hzanc
    refine ⟨section5_bilinear_eval p (section5_dot_terms u x) z,hact z hzt hzanc,?_,?_⟩
    · exact fun j hj => section5_bilinear_eval_off p _ z j hj
    · rw [section5_bilinear_accumulator_value p _ (fun v hv => (hctrl v hv).2.2) z,
        section5_dot_terms_sum]
