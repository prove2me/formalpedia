-- Prove2me | solution 1 for section5_clean_batch_all
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:42:55.779127+00:00
-- url     : https://prove2.me/submissions/ad85ade2-82bb-43df-b99e-0886d40558a2

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5ClassicalBatch
import Mathlib
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
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Sequential assembly of clean classical blocks with shared read-only inputs
and workspace. Output registers are disjoint; their values retain exact semantics. -/



theorem section5_batch_size {m N B : ℕ} (c : Fin N → Circuit gatesRev m)
    (hsize : ∀ i, (c i).size ≤ B) (ops : List (Fin N)) :
    (section5_batch_circuit c ops).size ≤ B*ops.length := by
  induction ops with
  | nil => simp [section5_batch_circuit,Circuit.size]
  | cons i l ih =>
    have hh := hsize i
    simp only [section5_batch_circuit,List.map_cons,List.flatten_cons,Circuit.size,
      List.length_append,List.length_cons] at *
    rw [Nat.mul_add,Nat.mul_one]
    omega

theorem section5_clean_batch_action {m N w d a : ℕ} {V : Type*}
    (c : Fin N → Circuit gatesRev m) (p : Fin N → Fin w ↪ Fin m)
    (data : Fin d → Fin m) (aux : Fin a → Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ b e, p i b ≠ p j e)
    (hdata : ∀ i j b, data j ≠ p i b) (haux : ∀ i j b, aux j ≠ p i b)
    (decode : Qubits w → V) (F : Fin N → Qubits d → V)
    (hact : ∀ i z, (∀ j, z (aux j)=false) → (∀ b, z (p i b)=false) →
      ∃ z' : Qubits m, act (c i).unitary (ket z)=ket z' ∧
        (∀ j, j ∉ Set.range (p i) → z' j=z j) ∧ decode (z' ∘ p i)=F i (z ∘ data))
    (ops : List (Fin N)) (hnd : ops.Nodup)
    (z : Qubits m) (hza : ∀ j, z (aux j)=false)
    (hz0 : ∀ i ∈ ops, ∀ b, z (p i b)=false) :
    ∃ z' : Qubits m, act (section5_batch_circuit c ops).unitary (ket z)=ket z' ∧
      (∀ j, (∀ i ∈ ops, j ∉ Set.range (p i)) → z' j=z j) ∧
      ∀ i ∈ ops, decode (z' ∘ p i)=F i (z ∘ data) := by
  induction ops generalizing z with
  | nil =>
    refine ⟨z,section5_boolean_circuit_nil (ket z),by intro j hj; rfl,?_⟩
    simp
  | cons i ops ih =>
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨z1,hz1,hz1off,hz1val⟩ := hact i z hza (hz0 i (by simp))
    have hza1 : ∀ j, z1 (aux j)=false := by
      intro j
      exact (hz1off _ (by rintro ⟨b,hb⟩; exact haux i j b hb.symm)).trans (hza j)
    have hz01 : ∀ j ∈ ops, ∀ b, z1 (p j b)=false := by
      intro j hj b
      have hij : i ≠ j := by intro h; subst j; exact hnd'.1 hj
      exact (hz1off _ (by rintro ⟨e,he⟩; exact hpair i j hij e b he)).trans
        (hz0 j (by simp [hj]) b)
    obtain ⟨z2,hz2,hz2off,hz2val⟩ := ih hnd'.2 z1 hza1 hz01
    refine ⟨z2,?_,?_,?_⟩
    · change act (Circuit.unitary (c i++section5_batch_circuit c ops)) (ket z)=_
      rw [section5_boolean_circuit_append,hz1,hz2]
    · intro j hj
      exact (hz2off j (fun k hk => hj k (by simp [hk]))).trans (hz1off j (hj i (by simp)))
    · intro j hj
      rcases List.mem_cons.mp hj with hji | hj
      · subst j
        have hp : z2 ∘ p i=z1 ∘ p i := by
          funext b
          apply hz2off
          intro j hj
          have hij : i ≠ j := by intro h; subst j; exact hnd'.1 hj
          rintro ⟨e,he⟩
          exact hpair i j hij b e he.symm
        rw [hp,hz1val]
      · have hd : z1 ∘ data=z ∘ data := by
          funext e
          exact hz1off _ (by rintro ⟨b,hb⟩; exact hdata i e b hb.symm)
        rw [hz2val j hj,hd]



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution {m N w d a B : ℕ} {V : Type*}
    (c : Fin N → Circuit gatesRev m) (p : Fin N → Fin w ↪ Fin m)
    (data : Fin d → Fin m) (aux : Fin a → Fin m)
    (hsize : ∀ i, (c i).size ≤ B)
    (hpair : ∀ i j, i ≠ j → ∀ b e, p i b ≠ p j e)
    (hdata : ∀ i j b, data j ≠ p i b) (haux : ∀ i j b, aux j ≠ p i b)
    (decode : Qubits w → V) (F : Fin N → Qubits d → V)
    (hact : ∀ i z, (∀ j, z (aux j)=false) → (∀ b, z (p i b)=false) →
      ∃ z' : Qubits m, act (c i).unitary (ket z)=ket z' ∧
        (∀ j, j ∉ Set.range (p i) → z' j=z j) ∧ decode (z' ∘ p i)=F i (z ∘ data)) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ B*N ∧
      ∀ z : Qubits m, (∀ j, z (aux j)=false) → (∀ i b, z (p i b)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          ∀ i, decode (z' ∘ p i)=F i (z ∘ data) := by
  refine ⟨section5_batch_circuit c (List.finRange N),?_,?_⟩
  · simpa using section5_batch_size c hsize (List.finRange N)
  · intro z hza hz0
    obtain ⟨z',hz',hoff,hval⟩ := section5_clean_batch_action c p data aux hpair hdata haux
      decode F hact (List.finRange N) (List.nodup_finRange N) z hza (fun i hi => hz0 i)
    exact ⟨z',hz',fun j hj => hoff j (fun i hi => hj i),fun i => hval i (List.mem_finRange i)⟩
