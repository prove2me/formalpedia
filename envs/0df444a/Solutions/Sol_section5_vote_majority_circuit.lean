-- Prove2me | solution 1 for section5_vote_majority_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:30.561786+00:00
-- url     : https://prove2.me/submissions/a25b3d7b-a536-4c7a-9cd9-6be674a7ccc0

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
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5MajorityCircuit
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Definitions.Def_Section5Verified_Section5VoteMajorityCircuit
import Mathlib
import Theorems.Thm_section5_embed_classical_gate_action
import Theorems.Thm_section5_majority_circuit_action
import Theorems.Thm_section5_replace_wires_eq_update
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/











theorem section5_cnot_matrix_action (y z : Qubits 2) :
    (Gate.ofMatrix2 cnot).mat y z=if y=section5_cnot_perm z then 1 else 0 := by
  have heq : y=section5_cnot_perm z ↔ y 0=z 0 ∧ y 1=xor (z 1) (z 0) := by
    constructor
    · intro h; exact ⟨congrFun h 0,congrFun h 1⟩
    · intro h; funext i; fin_cases i
      · exact h.1
      · exact h.2
  change (if y 0=z 0 ∧ y 1=xor (z 1) (z 0) then (1:ℂ) else 0)=_
  simp only [heq]



























theorem section5_embedded_cnot_target {m : ℕ} (a t : Fin m) (hat : a ≠ t) (x : Qubits m) :
    act (embedOp (Gate.ofMatrix2 cnot).mat (section5_boolean_wire2 a t hat)) (ket x)=
      ket (Function.update x t (xor (x t) (x a))) := by
  have hact := section5_embed_classical_gate_action (section5_boolean_wire2 a t hat)
    _ _ section5_cnot_matrix_action x
  rw [section5_replace_wires_eq_update _ _ _ 1 (by
    intro i hi
    fin_cases i
    · rfl
    · exact (hi rfl).elim)] at hact
  exact hact



theorem section5_boolean_circuit_cons {m : ℕ} (g : GateApp gatesRev m) (c : Circuit gatesRev m)
    (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (Circuit.unitary (g::c)) ψ=act c.unitary (act (embedOp g.gate.mat g.wires) ψ) := by
  classical
  ext z
  simp only [Circuit.unitary,List.map_cons,List.reverse_cons,List.prod_append,List.prod_singleton]
  exact congrFun (Matrix.mulVec_mulVec ψ _ _).symm z

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
open QAlgorithms QuantumLTF.Membership
theorem solution {m : ℕ} (labels prediction : Fin 3 ↪ Fin m)
    (t : Fin m) (hdisj : ∀ i j, labels i ≠ prediction j) (ht : t ∉ Set.range prediction) :
    ∃ c : Circuit gatesRev m, c.size=6 ∧
      ∀ z : Qubits m, z t=false →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          z' t=section5_majority_bit (xor (z (prediction 0)) (z (labels 0)))
            (xor (z (prediction 1)) (z (labels 1))) (xor (z (prediction 2)) (z (labels 2))) ∧
          ∀ j, j ∉ Set.range prediction → j ≠ t → z' j=z j := by
  let cx := section5_three_vote_xor_circuit labels prediction hdisj
  let cm := section5_majority_circuit prediction t ht
  refine ⟨cx++cm,rfl,?_⟩
  intro z hzt
  let z0 := Function.update z (prediction 0) (xor (z (prediction 0)) (z (labels 0)))
  let z1 := Function.update z0 (prediction 1) (xor (z0 (prediction 1)) (z0 (labels 1)))
  let z2 := Function.update z1 (prediction 2) (xor (z1 (prediction 2)) (z1 (labels 2)))
  have hp01 : prediction 0 ≠ prediction 1 := prediction.injective.ne (by decide)
  have hp02 : prediction 0 ≠ prediction 2 := prediction.injective.ne (by decide)
  have hp12 : prediction 1 ≠ prediction 2 := prediction.injective.ne (by decide)
  have hpred : ∀ i : Fin 3, z2 (prediction i)=xor (z (prediction i)) (z (labels i)) := by
    intro i
    fin_cases i <;>
      simp [z2,z1,z0,hp01,hp02,hp12,Ne.symm hp01,Ne.symm hp02,Ne.symm hp12,hdisj]
  have hoff : ∀ j, j ∉ Set.range prediction → z2 j=z j := by
    intro j hj
    have hj0 : j ≠ prediction 0 := fun h => hj ⟨0,h.symm⟩
    have hj1 : j ≠ prediction 1 := fun h => hj ⟨1,h.symm⟩
    have hj2 : j ≠ prediction 2 := fun h => hj ⟨2,h.symm⟩
    simp only [z2,z1,z0,Function.update_of_ne hj2,Function.update_of_ne hj1,Function.update_of_ne hj0]
  have ht2 : z2 t=false := (hoff t ht).trans hzt
  let out := section5_majority_bit (xor (z (prediction 0)) (z (labels 0)))
    (xor (z (prediction 1)) (z (labels 1))) (xor (z (prediction 2)) (z (labels 2)))
  let z3 := Function.update z2 t out
  refine ⟨z3,?_,Function.update_self _ _ _,?_⟩
  · rw [section5_boolean_circuit_append]
    have hx : act cx.unitary (ket z)=ket z2 := by
      simp only [cx,section5_three_vote_xor_circuit,section5_boolean_circuit_cons,
        section5_rev_cnot,section5_embedded_cnot_target,section5_boolean_circuit_nil]
      rfl
    rw [hx,section5_majority_circuit_action]
    simp only [ht2,hpred,Bool.false_xor]
    rfl
  · intro j hj hjt
    exact (Function.update_of_ne hjt _ _).trans (hoff j hj)
