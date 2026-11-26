-- Prove2me | solution 1 for section5_classical_stage_invariant
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:42:54.221906+00:00
-- url     : https://prove2.me/submissions/4713c82d-b8e2-4638-80c1-b2c603a86f82

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5SequentialClassicalCompiler
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
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution {m K r a : ℕ} {V : Type*}
    (c : Fin K → Circuit gatesRev m) (p : Fin (K+1) → Fin r → Fin m)
    (aux : Fin a → Fin m) (decode : Qubits r → V) (F : V → V → V)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (haux : ∀ i j e, aux j ≠ p i e)
    (hact : ∀ i z, (∀ j, z (aux j)=false) → (∀ e, z (p i.succ e)=false) →
      ∃ z' : Qubits m, act (c i).unitary (ket z)=ket z' ∧
        (∀ j, j ∉ Set.range (p i.succ) → z' j=z j) ∧
        decode (z' ∘ p i.succ)=F (decode (z ∘ p i.castSucc)) (decode (z ∘ p 0)))
    (z : Qubits m) (hza : ∀ j, z (aux j)=false)
    (hz0 : ∀ j : Fin (K+1), 0 < j.val → ∀ e, z (p j e)=false)
    (k : ℕ) (hk : k ≤ K) :
    ∃ z' : Qubits m, act (section5_classical_stage_prefix c k hk).unitary (ket z)=ket z' ∧
      (∀ j, z' (aux j)=false) ∧
      (∀ j : Fin (K+1), k < j.val → ∀ e, z' (p j e)=false) ∧
      (∀ j : Fin (K+1), j.val ≤ k →
        decode (z' ∘ p j)=section5_left_iteration F (decode (z ∘ p 0)) j.val) ∧
      ∀ j, (∀ i : Fin K, j ∉ Set.range (p i.succ)) → z' j=z j := by
  induction k with
  | zero =>
    refine ⟨z,section5_boolean_circuit_nil (ket z),hza,hz0,?_,by intro j hj; rfl⟩
    intro j hj
    have hj0 : j=0 := by
      apply Fin.ext
      simpa only [Fin.val_zero] using Nat.eq_zero_of_le_zero hj
    subst j
    rfl
  | succ k ih =>
    obtain ⟨z1,hz1,hza1,hfuture1,hval1,hoff1⟩ := ih (by omega)
    let i : Fin K := ⟨k,by omega⟩
    have hnext : ∀ e, z1 (p i.succ e)=false := hfuture1 i.succ (by simp [i])
    obtain ⟨z2,hz2,hoff2,hval2⟩ := hact i z1 hza1 hnext
    have hkeep (j : Fin (K+1)) (hj : j ≠ i.succ) : z2 ∘ p j=z1 ∘ p j := by
      funext e
      exact hoff2 _ (by rintro ⟨f,hf⟩; exact hpair j i.succ hj e f hf.symm)
    refine ⟨z2,?_,?_,?_,?_,?_⟩
    · change act (Circuit.unitary (section5_classical_stage_prefix c k _++c i)) (ket z)=_
      rw [section5_boolean_circuit_append,hz1,hz2]
    · intro j
      exact (hoff2 _ (by rintro ⟨e,he⟩; exact haux i.succ j e he.symm)).trans (hza1 j)
    · intro j hj e
      have hjne : j ≠ i.succ := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_succ,i] at this
        omega
      have he := congrFun (hkeep j hjne) e
      exact he.trans (hfuture1 j (by omega) e)
    · intro j hj
      by_cases hjeq : j=i.succ
      · subst j
        rw [hval2,hval1 i.castSucc (by simp [i]),hval1 0 (by simp)]
        rfl
      · have hjold : j.val ≤ k := by
          have hne : j.val ≠ k+1 := by
            intro h
            apply hjeq
            apply Fin.ext
            simpa only [i,Fin.val_succ] using h
          omega
        rw [hkeep j hjeq,hval1 j hjold]
    · intro j hj
      exact (hoff2 j (hj i)).trans (hoff1 j hj)
