-- Prove2me | solution 1 for section5_boolean_program_action
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:33.998367+00:00
-- url     : https://prove2.me/submissions/ff8cb70a-0ec3-4e91-960e-3c03bfb8bdff

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_section5_boolean_gate_action
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/













































theorem section5_boolean_circuit_nil {m : ℕ} (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (Circuit.unitary ([] : Circuit gatesRev m)) ψ=ψ := by
  ext z
  simp [Circuit.unitary,act]















theorem section5_boolean_instruction_action {m : ℕ} (g : Section5BooleanInstruction m) (x : Qubits m) :
    act g.compile.unitary (ket x)=ket (g.eval x) :=
  section5_boolean_gate_action g.op g.a g.b g.target g.a_ne_target g.b_ne_target x

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
theorem solution {m : ℕ} (l : List (Section5BooleanInstruction m)) (x : Qubits m) :
    act (section5_compile_boolean_program l).unitary (ket x)=ket (section5_eval_boolean_program l x) := by
  induction l generalizing x with
  | nil => exact section5_boolean_circuit_nil (ket x)
  | cons g l ih =>
    change act (Circuit.unitary (g.compile++section5_compile_boolean_program l)) (ket x)=_
    rw [section5_boolean_circuit_append,section5_boolean_instruction_action,ih]
    rfl
