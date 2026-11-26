-- Prove2me | solution 1 for section5_boolCircuit_reversible_compile
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:08:10.242552+00:00
-- url     : https://prove2.me/submissions/6d1cc95e-1eec-42ee-acb7-397b5e9d5c9e

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5BooleanCircuitCompilation
import Mathlib
import Theorems.Thm_section5_boolean_list_compile
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution {n r : ℕ} (C : BoolCircuit n r) (hC : C.WellFormed) :
    ∃ (c : Circuit gatesRev (n+C.size)) (out : Fin r → Fin (n+C.size)),
      c.size ≤ 3*C.size ∧
      ∀ x : Qubits n, ∃ z : Qubits (n+C.size),
        act c.unitary (ket (Fin.append x (fun _ : Fin C.size => false)))=ket z ∧
          ∀ j, z (out j)=C.eval x j := by
  have hwf : ∀ k (hk : k < C.gates.length),
      (C.gates[k]).a < n+k ∧ ((C.gates[k]).op=BoolOp.not ∨ (C.gates[k]).b < n+k) := by
    intro k hk
    exact hC.1 ⟨k,hk⟩
  obtain ⟨c,hsize,hact⟩ := section5_boolean_list_compile C.gates (n+C.size) n (le_refl _) hwf
  refine ⟨c,(fun j => ⟨C.outputs j,hC.2 j⟩),hsize,?_⟩
  intro x
  refine ⟨section5_boolean_memory (n+C.size) (C.wireValues x),?_,?_⟩
  · have hh := hact (List.ofFn x) (List.length_ofFn)
    have heq : section5_boolean_memory (n+C.size) (List.ofFn x)=
        Fin.append x (fun _ : Fin C.size => false) := by
      funext i
      by_cases hi : i.val<n
      · have hieq : i=Fin.castAdd C.size ⟨i.val,hi⟩ := Fin.ext rfl
        rw [hieq]
        simp [section5_boolean_memory,Fin.append,Fin.addCases,hi]
        congr 1
      · have hieq : i=Fin.natAdd n ⟨i.val-n,by have := i.isLt; omega⟩ := by apply Fin.ext; simp; omega
        rw [hieq]
        simp only [Fin.append_right,section5_boolean_memory,Fin.val_natAdd]
        exact List.getD_eq_default _ _ (by simp)
    rw [heq] at hh
    exact hh
  · intro j
    rfl
