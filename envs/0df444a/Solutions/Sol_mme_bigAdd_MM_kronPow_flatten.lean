-- Prove2me | solution 1 for mme_bigAdd_MM_kronPow_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:45:10.087909+00:00
-- url     : https://prove2.me/submissions/64ec54c7-918e-4b5e-9c16-e201b3ef692c

import Mathlib.Tactic
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

universe u

theorem solution
    {K : Type u} [Field K]
    {k r : ℕ} (a b c : Fin k → ℕ) :
    ∃ (q : ℕ) (A B C : Fin q → ℕ),
      TensorObj.Isomorphic
        (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (C j)))
        ((TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i))).kronPow r) := by
  classical
  let W := Fin r → Fin k
  let q := Fintype.card W
  let e : Fin q ≃ W := (Fintype.equivFin W).symm
  let A : Fin q → ℕ := fun j ↦ ∏ t, a (e j t)
  let B : Fin q → ℕ := fun j ↦ ∏ t, b (e j t)
  let C : Fin q → ℕ := fun j ↦ ∏ t, c (e j t)
  refine ⟨q, A, B, C, ?_⟩
  apply TensorQ.toQ_eq_iff.mp
  rw [TensorQ.toQ_bigAdd, TensorQ.toQ_kronPow,
    TensorQ.toQ_bigAdd, Fintype.sum_pow]
  calc
    (∑ j : Fin q, TensorQ.toQ (MMObj K (A j) (B j) (C j))) =
        ∑ p : W, TensorQ.toQ
          (MMObj K (∏ t, a (p t)) (∏ t, b (p t)) (∏ t, c (p t))) := by
      simpa only [A, B, C] using
        (Equiv.sum_comp e (fun p : W ↦ TensorQ.toQ
          (MMObj K (∏ t, a (p t)) (∏ t, b (p t)) (∏ t, c (p t)))))
    _ = ∑ p : W, ∏ t, TensorQ.toQ (MMObj K (a (p t)) (b (p t)) (c (p t))) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hiso := mme_kronFin_MMObj_iso (K := K) r
        (fun t ↦ a (p t)) (fun t ↦ b (p t)) (fun t ↦ c (p t))
      calc
        TensorQ.toQ
            (MMObj K (∏ t, a (p t)) (∏ t, b (p t)) (∏ t, c (p t))) =
            TensorQ.toQ (TensorObj.kronFin r
              (fun t ↦ MMObj K (a (p t)) (b (p t)) (c (p t)))) :=
          (TensorQ.toQ_eq_iff.mpr hiso).symm
        _ = ∏ t, TensorQ.toQ (MMObj K (a (p t)) (b (p t)) (c (p t))) :=
          mme_toQ_kronFin _
