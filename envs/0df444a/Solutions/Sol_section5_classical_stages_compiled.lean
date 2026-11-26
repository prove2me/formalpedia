-- Prove2me | solution 1 for section5_classical_stages_compiled
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:46:37.734743+00:00
-- url     : https://prove2.me/submissions/240c11e4-e0d0-444f-926b-3ee35cffdca9

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5SequentialClassicalCompiler
import Mathlib
import Theorems.Thm_section5_classical_stage_invariant
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Sequential clean-workspace compilation when each output becomes the next
step's input. Earlier registers are retained, so the entire computation is reversible. -/





theorem section5_classical_stage_size {m K B : ℕ} (c : Fin K → Circuit gatesRev m)
    (hsize : ∀ i, (c i).size ≤ B) (k : ℕ) (hk : k ≤ K) :
    (section5_classical_stage_prefix c k hk).size ≤ B*k := by
  induction k with
  | zero => simp [section5_classical_stage_prefix,Circuit.size]
  | succ k ih =>
    have hc := hsize ⟨k,by omega⟩
    have hi := ih (by omega)
    simp only [section5_classical_stage_prefix,Circuit.size,List.length_append]
    change (c ⟨k,by omega⟩).length ≤ B at hc
    change (section5_classical_stage_prefix c k _).length ≤ B*k at hi
    rw [Nat.mul_succ]
    omega





end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution {m K r a B : ℕ} {V : Type*}
    (c : Fin K → Circuit gatesRev m) (p : Fin (K+1) → Fin r → Fin m)
    (aux : Fin a → Fin m) (decode : Qubits r → V) (F : V → V → V)
    (hsize : ∀ i, (c i).size ≤ B)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (haux : ∀ i j e, aux j ≠ p i e)
    (hact : ∀ i z, (∀ j, z (aux j)=false) → (∀ e, z (p i.succ e)=false) →
      ∃ z' : Qubits m, act (c i).unitary (ket z)=ket z' ∧
        (∀ j, j ∉ Set.range (p i.succ) → z' j=z j) ∧
        decode (z' ∘ p i.succ)=F (decode (z ∘ p i.castSucc)) (decode (z ∘ p 0))) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ B*K ∧
      ∀ z : Qubits m, (∀ j, z (aux j)=false) →
        (∀ j : Fin (K+1), 0 < j.val → ∀ e, z (p j e)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          decode (z' ∘ p (Fin.last K))=section5_left_iteration F (decode (z ∘ p 0)) K ∧
          (∀ j, z' (aux j)=false) ∧
          ∀ j, (∀ i : Fin K, j ∉ Set.range (p i.succ)) → z' j=z j := by
  refine ⟨section5_classical_stage_prefix c K le_rfl,section5_classical_stage_size c hsize K le_rfl,?_⟩
  intro z hza hz0
  obtain ⟨z',hz',hza',hfuture,hval,hoff⟩ :=
    section5_classical_stage_invariant c p aux decode F hpair haux hact z hza hz0 K le_rfl
  exact ⟨z',hz',hval (Fin.last K) (by simp),hza',hoff⟩
