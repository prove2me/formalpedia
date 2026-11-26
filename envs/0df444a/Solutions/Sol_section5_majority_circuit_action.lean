-- Prove2me | solution 1 for section5_majority_circuit_action
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:08.7991+00:00
-- url     : https://prove2.me/submissions/a602c79b-0574-4a1a-b06d-e0428c06c4ff

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
import Mathlib
import Theorems.Thm_section5_embed_classical_gate_action
import Theorems.Thm_section5_replace_wires_eq_update
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/















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
theorem solution {m : ℕ} (v : Fin 3 ↪ Fin m) (t : Fin m)
    (ht : t ∉ Set.range v) (z : Qubits m) :
    act (section5_majority_circuit v t ht).unitary (ket z)=
      ket (Function.update z t
        (xor (z t) (section5_majority_bit (z (v 0)) (z (v 1)) (z (v 2))))) := by
  have h0 : v 0 ≠ t := fun h => ht ⟨0,h⟩
  have h1 : v 1 ≠ t := fun h => ht ⟨1,h⟩
  have h2 : v 2 ≠ t := fun h => ht ⟨2,h⟩
  simp only [section5_majority_circuit,section5_boolean_circuit_cons,section5_rev_toffoli,
    section5_embedded_toffoli_target,section5_boolean_circuit_nil]
  congr 1
  funext j
  by_cases hj : j=t
  · subst j
    simp only [Function.update_self,Function.update_of_ne h0,
      Function.update_of_ne h1,Function.update_of_ne h2]
    cases z t <;> cases z (v 0) <;> cases z (v 1) <;> cases z (v 2) <;> rfl
  · simp [hj]
