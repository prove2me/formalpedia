-- Prove2me | solution 1 for section5_maximum_record_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:08:15.439937+00:00
-- url     : https://prove2.me/submissions/725c4262-9ea9-466e-a097-da68de863b25

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
import Definitions.Def_Section5Verified_Section5SequentialClassicalCompiler
import Mathlib
import Theorems.Thm_section5_compare_swap_records_circuit
import Theorems.Thm_section5_max_record_prefix
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
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m N R w : ℕ} (score : Fin w ↪ Fin R)
    (p : Fin (N+1) → Fin R ↪ Fin m) (ctrl : Fin N ↪ Fin m) (anc : Fin 1 ↪ Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hctrl : ∀ i j e, ctrl i ≠ p j e)
    (hanc : ∀ i e j, p i e ≠ anc j) (hca : ∀ i j, ctrl i ≠ anc j) :
    ∃ c : Circuit gatesRev m, c.size ≤ (16*w+1+7*R)*N ∧
      ∀ z : Qubits m, (∀ i, z (ctrl i)=false) → (∀ j, z (anc j)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∃ winner : Fin (N+1), z' ∘ p 0=z ∘ p winner ∧
            ∀ i, bitsToNatLSB (z ∘ p i ∘ score) ≤ bitsToNatLSB (z ∘ p winner ∘ score)) ∧
          (∀ j, z' (anc j)=false) ∧
          ∀ j, (∀ i, j ∉ Set.range (p i)) → j ∉ Set.range ctrl → z' j=z j := by
  classical
  have hsteps : ∀ i : Fin N, ∃ c : Circuit gatesRev m, c.size ≤ 16*w+1+7*R ∧
      ∀ z : Qubits m, z (ctrl i)=false → (∀ j, z (anc j)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (z' ∘ p 0=if bitsToNatLSB (z ∘ p 0 ∘ score) < bitsToNatLSB (z ∘ p i.succ ∘ score)
            then z ∘ p i.succ else z ∘ p 0) ∧
          (∀ j, j ∉ Set.range (p 0) → j ∉ Set.range (p i.succ) → j ≠ ctrl i → z' j=z j) ∧
          ∀ j, z' (anc j)=false := by
    intro i
    exact section5_compare_swap_records_circuit score (p 0) (p i.succ) (ctrl i) anc
      (hpair 0 i.succ (by intro h; have := congrArg Fin.val h; simp at this))
      (hctrl i 0) (hctrl i i.succ) (hanc 0) (hanc i.succ) (hca i)
  choose cs hsize hact using hsteps
  refine ⟨section5_classical_stage_prefix cs N le_rfl,section5_classical_stage_size cs hsize N le_rfl,?_⟩
  intro z hzctrl hzanc
  obtain ⟨z',hz',hza,hflags,hfuture,⟨winner,hwinner,hbest,hmax⟩,hoff⟩ :=
    section5_max_record_prefix cs p ctrl anc (fun v => bitsToNatLSB (v ∘ score)) hpair hctrl
      hact z hzctrl hzanc N le_rfl
  exact ⟨z',hz',⟨winner,hbest,fun i => hmax i (by omega)⟩,hza,hoff⟩
