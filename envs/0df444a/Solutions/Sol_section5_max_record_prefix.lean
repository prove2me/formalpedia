-- Prove2me | solution 1 for section5_max_record_prefix
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:51.758856+00:00
-- url     : https://prove2.me/submissions/e7c7cc1b-de23-443c-b876-8224685d87a6

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
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m N R : ℕ}
    (cs : Fin N → Circuit gatesRev m) (p : Fin (N+1) → Fin R ↪ Fin m)
    (ctrl : Fin N ↪ Fin m) (anc : Fin 1 ↪ Fin m) (score : Qubits R → ℕ)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hctrl : ∀ i j e, ctrl i ≠ p j e)
    (hact : ∀ i z, z (ctrl i)=false → (∀ j, z (anc j)=false) →
      ∃ z' : Qubits m, act (cs i).unitary (ket z)=ket z' ∧
        (z' ∘ p 0=if score (z ∘ p 0) < score (z ∘ p i.succ) then z ∘ p i.succ else z ∘ p 0) ∧
        (∀ j, j ∉ Set.range (p 0) → j ∉ Set.range (p i.succ) → j ≠ ctrl i → z' j=z j) ∧
        ∀ j, z' (anc j)=false)
    (z : Qubits m) (hzctrl : ∀ i, z (ctrl i)=false) (hzanc : ∀ j, z (anc j)=false)
    (k : ℕ) (hk : k ≤ N) :
    ∃ z' : Qubits m, act (section5_classical_stage_prefix cs k hk).unitary (ket z)=ket z' ∧
      (∀ j, z' (anc j)=false) ∧
      (∀ i : Fin N, k ≤ i.val → z' (ctrl i)=false) ∧
      (∀ j : Fin (N+1), k < j.val → z' ∘ p j=z ∘ p j) ∧
      (∃ winner : Fin (N+1), winner.val ≤ k ∧ z' ∘ p 0=z ∘ p winner ∧
        ∀ i : Fin (N+1), i.val ≤ k → score (z ∘ p i) ≤ score (z ∘ p winner)) ∧
      ∀ j, (∀ i, j ∉ Set.range (p i)) → j ∉ Set.range ctrl → z' j=z j := by
  induction k with
  | zero =>
    refine ⟨z,section5_boolean_circuit_nil (ket z),hzanc,by intro i hi; exact hzctrl i,
      by intro j hj; rfl,?_,by intro j hj hc; rfl⟩
    refine ⟨0,by simp,rfl,?_⟩
    intro i hi
    have hi0 : i=0 := by
      apply Fin.ext
      simpa only [Fin.val_zero] using Nat.eq_zero_of_le_zero hi
    subst i
    rfl
  | succ k ih =>
    obtain ⟨z1,hz1,hza1,hflags1,hfuture1,⟨winner,hwinner,hbest,hmax⟩,hoff1⟩ := ih (by omega)
    let s : Fin N := ⟨k,by omega⟩
    obtain ⟨z2,hz2,hbest2,hoff2,hza2⟩ := hact s z1 (hflags1 s (by simp [s])) hza1
    have hnext : z1 ∘ p s.succ=z ∘ p s.succ := hfuture1 s.succ (by simp [s])
    have hbestout : z2 ∘ p 0=
        if score (z ∘ p winner) < score (z ∘ p s.succ) then z ∘ p s.succ else z ∘ p winner := by
      rw [hbest,hnext] at hbest2
      exact hbest2
    have hkeep (j : Fin (N+1)) (hj0 : j ≠ 0) (hjs : j ≠ s.succ) : z2 ∘ p j=z1 ∘ p j := by
      funext e
      exact hoff2 _
        (by rintro ⟨f,hf⟩; exact hpair j 0 hj0 e f hf.symm)
        (by rintro ⟨f,hf⟩; exact hpair j s.succ hjs e f hf.symm) (hctrl s j e).symm
    refine ⟨z2,?_,hza2,?_,?_,?_,?_⟩
    · change act (Circuit.unitary (section5_classical_stage_prefix cs k _++cs s)) (ket z)=_
      rw [section5_boolean_circuit_append,hz1,hz2]
    · intro i hi
      have his : i ≠ s := by intro h; subst i; simp only [s] at hi; omega
      exact (hoff2 _ (by rintro ⟨e,he⟩; exact hctrl i 0 e he.symm)
        (by rintro ⟨e,he⟩; exact hctrl i s.succ e he.symm) (ctrl.injective.ne his)).trans
          (hflags1 i (by omega))
    · intro j hj
      have hj0 : j ≠ 0 := by intro h; subst j; simp only [Fin.val_zero] at hj; omega
      have hjs : j ≠ s.succ := by
        intro h
        have hh := congrArg Fin.val h
        simp only [s,Fin.val_succ] at hh
        omega
      exact (hkeep j hj0 hjs).trans (hfuture1 j (by omega))
    · by_cases hbetter : score (z ∘ p winner) < score (z ∘ p s.succ)
      · refine ⟨s.succ,by simp [s],?_,?_⟩
        · simpa only [hbetter,↓reduceIte] using hbestout
        · intro i hi
          by_cases his : i=s.succ
          · subst i; rfl
          · have hiold : i.val ≤ k := by
              have hh : i.val ≠ k+1 := by
                intro h
                apply his
                apply Fin.ext
                simpa only [s,Fin.val_succ] using h
              omega
            exact (hmax i hiold).trans hbetter.le
      · refine ⟨winner,by omega,?_,?_⟩
        · simpa only [hbetter,↓reduceIte] using hbestout
        · intro i hi
          by_cases his : i=s.succ
          · subst i; exact Nat.le_of_not_gt hbetter
          · apply hmax i
            have hh : i.val ≠ k+1 := by
              intro h
              apply his
              apply Fin.ext
              simpa only [s,Fin.val_succ] using h
            omega
    · intro j hj hc
      exact (hoff2 j (hj 0) (hj s.succ) (by intro h; exact hc ⟨s,h.symm⟩)).trans (hoff1 j hj hc)
