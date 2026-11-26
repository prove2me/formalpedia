-- Prove2me | solution 1 for section5_boolean_gate_action
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:02:07.648217+00:00
-- url     : https://prove2.me/submissions/d0733936-d600-4ca8-9d30-1a94163bbdcc

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_section5_embed_classical_gate_action
import Theorems.Thm_section5_replace_wires_eq_update
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/









theorem section5_not_matrix_action (y z : Qubits 1) :
    (Gate.ofMatrix1 pauliX).mat y z=if y=section5_bit_flip z then 1 else 0 := by
  have heq : y=section5_bit_flip z ↔ y 0=!(z 0) := by
    constructor
    · intro h; exact congrFun h 0
    · intro h; funext i; fin_cases i; exact h
  change (if y 0=z 0 then (0:ℂ) else 1)=_
  simp only [heq]
  cases hy : y 0 <;> cases hz : z 0 <;> simp [hy,hz]

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



theorem section5_toffoli_matrix_action (y z : Qubits 3) :
    section5_toffoli_gate.mat y z=if y=section5_toffoli_perm z then 1 else 0 := by
  have heq : y=section5_toffoli_perm z ↔ y 0=z 0 ∧ y 1=z 1 ∧ y 2=xor (z 2) (z 0 && z 1) := by
    constructor
    · intro h; exact ⟨congrFun h 0,congrFun h 1,congrFun h 2⟩
    · intro h; funext i; fin_cases i
      · exact h.1
      · exact h.2.1
      · exact h.2.2
  change (if y 0=z 0 ∧ y 1=z 1 ∧ y 2=xor (z 2) (z 0 && z 1) then (1:ℂ) else 0)=_
  simp only [heq]





















theorem section5_embedded_not_target {m : ℕ} (t : Fin m) (x : Qubits m) :
    act (embedOp (Gate.ofMatrix1 pauliX).mat (section5_boolean_wire1 t)) (ket x)=
      ket (Function.update x t (!(x t))) := by
  have hact := section5_embed_classical_gate_action (section5_boolean_wire1 t)
    _ _ section5_not_matrix_action x
  rw [section5_replace_wires_eq_update _ _ _ 0 (by intro i hi; fin_cases i; exact (hi rfl).elim)] at hact
  exact hact

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

theorem section5_embedded_toffoli_target {m : ℕ} (a b t : Fin m)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (x : Qubits m) :
    act (embedOp section5_toffoli_gate.mat (section5_boolean_wire3 a b t hab hat hbt)) (ket x)=
      ket (Function.update x t (xor (x t) (x a && x b))) := by
  have hact := section5_embed_classical_gate_action (section5_boolean_wire3 a b t hab hat hbt)
    _ _ section5_toffoli_matrix_action x
  rw [section5_replace_wires_eq_update _ _ _ 2 (by
    intro i hi
    fin_cases i
    · rfl
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



























end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution {m : ℕ} (op : BoolOp) (a b t : Fin m)
    (hat : a ≠ t) (hbt : b ≠ t) (x : Qubits m) :
    act (section5_boolean_gate_circuit op a b t hat hbt).unitary (ket x)=
      ket (Function.update x t (xor (x t) (section5_bool_value op (x a) (x b)))) := by
  cases op with
  | not =>
    simp only [section5_boolean_gate_circuit,section5_boolean_circuit_cons,section5_rev_not,
      section5_rev_cnot,section5_embedded_not_target,section5_embedded_cnot_target,
      section5_boolean_circuit_nil]
    congr 1
    funext i
    by_cases hit : i=t
    · subst i
      simp only [Function.update_self,Function.update_of_ne hat,section5_bool_value]
      cases x t <;> cases x a <;> rfl
    · simp [hit]
  | and =>
    by_cases hab : a=b
    · subst b
      simp [section5_boolean_gate_circuit,section5_boolean_circuit_cons,section5_rev_cnot,
        section5_embedded_cnot_target,section5_boolean_circuit_nil,section5_bool_value]
    · simp only [section5_boolean_gate_circuit,dif_neg hab,section5_boolean_circuit_cons,
        section5_rev_toffoli,section5_embedded_toffoli_target,section5_boolean_circuit_nil,
        section5_bool_value]
  | or =>
    by_cases hab : a=b
    · subst b
      simp [section5_boolean_gate_circuit,section5_boolean_circuit_cons,section5_rev_cnot,
        section5_embedded_cnot_target,section5_boolean_circuit_nil,section5_bool_value]
    · simp only [section5_boolean_gate_circuit,dif_neg hab,section5_boolean_circuit_cons,
        section5_rev_cnot,section5_rev_toffoli,section5_embedded_cnot_target,
        section5_embedded_toffoli_target,section5_boolean_circuit_nil]
      congr 1
      funext i
      by_cases hit : i=t
      · subst i
        simp only [Function.update_self,Function.update_of_ne hat,Function.update_of_ne hbt,
          section5_bool_value]
        cases x t <;> cases x a <;> cases x b <;> rfl
      · simp [hit]
