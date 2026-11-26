-- Prove2me | solution 1 for section5_replace_wires_eq_update
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:23.596259+00:00
-- url     : https://prove2.me/submissions/849f5fa7-0311-4372-b946-9f7ece26cc1f

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution {k m : ℕ} (e : Fin k ↪ Fin m)
    (x : Qubits m) (v : Qubits k) (j : Fin k)
    (hkeep : ∀ i, i ≠ j → v i=x (e i)) :
    section5_replace_wires e x v=Function.update x (e j) (v j) := by
  classical
  funext a
  by_cases ha : a ∈ Set.range e
  · obtain ⟨i,rfl⟩ := ha
    rw [section5_replace_wires_on]
    by_cases hij : i=j
    · subst i; simp
    · rw [Function.update_of_ne (e.injective.ne hij)]
      exact hkeep i hij
  · rw [section5_replace_wires_off e x v a ha,Function.update_of_ne]
    intro h
    exact ha ⟨j,h.symm⟩
