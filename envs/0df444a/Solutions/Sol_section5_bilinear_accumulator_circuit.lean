-- Prove2me | solution 1 for section5_bilinear_accumulator_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:08:33.232328+00:00
-- url     : https://prove2.me/submissions/84d0c2a8-f4a5-4c19-b664-3f9f54f86ca7

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
import Mathlib
import Theorems.Thm_section5_bilinear_accumulator_gate
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

















end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/













































theorem section5_boolean_circuit_nil {m : ℕ} (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (Circuit.unitary ([] : Circuit gatesRev m)) ψ=ψ := by
  ext z
  simp [Circuit.unitary,act]

















theorem section5_boolean_circuit_append {m : ℕ} (c d : Circuit gatesRev m)
    (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (Circuit.unitary (c++d)) ψ=act d.unitary (act c.unitary ψ) := by
  classical
  ext z
  simp only [Circuit.unitary,List.map_append,List.reverse_append,List.prod_append]
  exact congrFun (Matrix.mulVec_mulVec ψ _ _).symm z









end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54
theorem solution {m w : ℕ}
    (p : Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (t : Fin m)
    (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (ops : List (Section5BilinearTerm m))
    (hctrl : ∀ a ∈ ops, a.a ≠ t ∧ a.b ≠ t ∧
      a.a ∉ Set.range p ∧ a.b ∉ Set.range p) :
    ∃ c : Circuit gatesRev m, c.size ≤ (16*w+6)*ops.length ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) →
        act c.unitary (ket z)=ket (section5_bilinear_eval p ops z) := by
  induction ops with
  | nil =>
    refine ⟨[],by simp [Circuit.size],?_⟩
    intro z hz hzanc
    exact section5_boolean_circuit_nil (ket z)
  | cons a ops ih =>
    have ha := hctrl a (by simp)
    obtain ⟨d,hd,hdact⟩ := ih (fun b hb => hctrl b (by simp [hb]))
    obtain ⟨c,hc,hact⟩ := section5_bilinear_accumulator_gate p anc hpa t a.a a.b
      htp hta ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 a.weight
    refine ⟨c++d,?_,?_⟩
    · simp only [Circuit.size,List.length_append,List.length_cons] at *
      nlinarith
    · intro z hzt hzanc
      rw [section5_boolean_circuit_append,hact z hzt hzanc,hdact]
      · rfl
      · exact (section5_bilinear_step_off p a.a a.b a.weight z t htp).trans hzt
      · intro j
        rw [section5_bilinear_step_off p a.a a.b a.weight z (anc j) (by
          rintro ⟨i,hi⟩
          exact hpa i j hi),hzanc j]
