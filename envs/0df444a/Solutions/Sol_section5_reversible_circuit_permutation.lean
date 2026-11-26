-- Prove2me | solution 1 for section5_reversible_circuit_permutation
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:24.259876+00:00
-- url     : https://prove2.me/submissions/d6f09495-20b3-4f3a-81f6-6836e143c3b4

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Definitions.Def_Section5Verified_Section5ReversibleCircuitPermutation
import Mathlib
import Theorems.Thm_section5_embed_classical_gate_action
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
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Every circuit over the published NOT/CNOT/Toffoli gate set acts as an exact
permutation of basis strings, including inputs with arbitrary workspace bits. -/



theorem section5_reversible_gate_permutation (g : Gate) (hg : g ∈ gatesRev) :
    ∃ f : Equiv.Perm (Qubits g.arity), ∀ y z, g.mat y z=if y=f z then 1 else 0 := by
  have hcases : g=Gate.ofMatrix1 pauliX ∨ g=Gate.ofMatrix2 cnot ∨ g=section5_toffoli_gate := by
    simpa [gatesRev,section5_toffoli_gate] using hg
  rcases hcases with rfl | rfl | rfl
  · exact ⟨section5_bit_flip,section5_not_matrix_action⟩
  · exact ⟨section5_cnot_perm,section5_cnot_matrix_action⟩
  · exact ⟨section5_toffoli_perm,section5_toffoli_matrix_action⟩

theorem section5_reversible_gate_app_permutation {m : ℕ} (g : GateApp gatesRev m) :
    ∃ f : Equiv.Perm (Qubits m),
      ∀ x, act (embedOp g.gate.mat g.wires) (ket x)=ket (f x) := by
  obtain ⟨f,hf⟩ := section5_reversible_gate_permutation g.gate g.mem
  exact ⟨section5_embedded_basis_perm g.wires f,
    fun x => section5_embed_classical_gate_action g.wires g.gate.mat f hf x⟩





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution {m : ℕ} (c : Circuit gatesRev m) :
    ∃ f : Equiv.Perm (Qubits m), ∀ x, act c.unitary (ket x)=ket (f x) := by
  induction c with
  | nil => exact ⟨Equiv.refl _,fun x => section5_boolean_circuit_nil (ket x)⟩
  | cons g c ih =>
    obtain ⟨f,hf⟩ := section5_reversible_gate_app_permutation g
    obtain ⟨h,hh⟩ := ih
    refine ⟨f.trans h,?_⟩
    intro x
    rw [section5_boolean_circuit_cons,hf,hh]
    rfl
