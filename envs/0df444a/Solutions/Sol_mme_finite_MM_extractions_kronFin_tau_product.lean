-- Prove2me | solution 1 for mme_finite_MM_extractions_kronFin_tau_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:57:17.284322+00:00
-- url     : https://prove2.me/submissions/180c19b6-cbb8-416c-bd40-9e7af8be9863

import Mathlib.Tactic
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

universe u

private theorem kron_restrict_for_tau_product
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  rw [← TensorQ.le_toQ]
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft :
      P.le (TensorQ.toQ X * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y) :=
    P.mul_right _ _ hx _
  have hright :
      P.le (TensorQ.toQ X' * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y') := by
    simpa only [mul_comm] using P.mul_right _ _ hy (TensorQ.toQ X')
  exact P.le_trans _ _ _ hleft hright

private theorem kronFin_restrict_for_tau_product
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d) :
    ∀ (n : ℕ) (X Y : Fin n → TensorObj K d),
      (∀ i, TensorObj.Restrict (X i) (Y i)) →
      TensorObj.Restrict (TensorObj.kronFin n X) (TensorObj.kronFin n Y) := by
  intro n
  induction n with
  | zero =>
      intro X Y h
      exact TensorObj.Restrict.refl _
  | succ n ih =>
      intro X Y h
      change TensorObj.Restrict
        (TensorObj.kron (X 0)
          (TensorObj.kronFin n (fun i ↦ X i.succ)))
        (TensorObj.kron (Y 0)
          (TensorObj.kronFin n (fun i ↦ Y i.succ)))
      exact kron_restrict_for_tau_product hd (h 0)
        (ih (fun i ↦ X i.succ) (fun i ↦ Y i.succ) (fun i ↦ h i.succ))

theorem solution
    {K : Type u} [Field K] {n : ℕ}
    (Y : Fin n → TensorObj K 3) (tau : ℝ) (lower : Fin n → ℝ)
    (hlower : ∀ i, 0 ≤ lower i)
    (hextract : ∀ i : Fin n,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
          (Y i) ∧
        lower i ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) :
    ∃ (q : ℕ) (A B C : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (C j)))
        (TensorObj.kronFin n Y) ∧
      (∏ i, lower i) ≤
        ∑ j, (((A j * B j * C j : ℕ) : ℝ) ^ tau) := by
  classical
  choose k a b c hdata using hextract
  let X : Fin n → TensorObj K 3 := fun i ↦
    TensorObj.bigAdd (fun j ↦ MMObj K (a i j) (b i j) (c i j))
  let I := ∀ i : Fin n, Fin (k i)
  let q := Fintype.card I
  let e : Fin q ≃ I := (Fintype.equivFin I).symm
  let A : Fin q → ℕ := fun j ↦ ∏ i, a i (e j i)
  let B : Fin q → ℕ := fun j ↦ ∏ i, b i (e j i)
  let C : Fin q → ℕ := fun j ↦ ∏ i, c i (e j i)
  refine ⟨q, A, B, C, ?_, ?_⟩
  · have hflatten : TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (C j)))
        (TensorObj.kronFin n X) :=
      (TensorQ.toQ_eq_iff.mp (by
        rw [TensorQ.toQ_bigAdd]
        calc
          (∑ j : Fin q, TensorQ.toQ (MMObj K (A j) (B j) (C j))) =
              ∑ p : I, TensorQ.toQ
                (MMObj K (∏ i, a i (p i)) (∏ i, b i (p i))
                  (∏ i, c i (p i))) := by
            simpa only [A, B, C] using
              (Equiv.sum_comp e (fun p : I ↦ TensorQ.toQ
                (MMObj K (∏ i, a i (p i)) (∏ i, b i (p i))
                  (∏ i, c i (p i)))))
          _ = ∑ p : I, ∏ i,
              TensorQ.toQ (MMObj K (a i (p i)) (b i (p i)) (c i (p i))) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hiso := mme_kronFin_MMObj_iso (K := K) n
              (fun i ↦ a i (p i)) (fun i ↦ b i (p i))
              (fun i ↦ c i (p i))
            calc
              TensorQ.toQ
                  (MMObj K (∏ i, a i (p i)) (∏ i, b i (p i))
                    (∏ i, c i (p i))) =
                  TensorQ.toQ (TensorObj.kronFin n
                    (fun i ↦ MMObj K (a i (p i)) (b i (p i)) (c i (p i)))) :=
                (TensorQ.toQ_eq_iff.mpr hiso).symm
              _ = ∏ i, TensorQ.toQ
                  (MMObj K (a i (p i)) (b i (p i)) (c i (p i))) :=
                mme_toQ_kronFin _
          _ = ∏ i, ∑ j : Fin (k i),
              TensorQ.toQ (MMObj K (a i j) (b i j) (c i j)) :=
            (Fintype.prod_sum (fun i (j : Fin (k i)) ↦
              TensorQ.toQ (MMObj K (a i j) (b i j) (c i j)))).symm
          _ = ∏ i, TensorQ.toQ (X i) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact (TensorQ.toQ_bigAdd _).symm
          _ = TensorQ.toQ (TensorObj.kronFin n X) :=
            (mme_toQ_kronFin X).symm)).1
    exact TensorObj.Restrict.trans hflatten
      (kronFin_restrict_for_tau_product (K := K) (by norm_num) n X Y
        (fun i ↦ (hdata i).1))
  · have hpoint : ∀ p : I,
        ((((∏ i, a i (p i)) * (∏ i, b i (p i)) *
            (∏ i, c i (p i)) : ℕ) : ℝ) ^ tau) =
          ∏ i, (((a i (p i) * b i (p i) * c i (p i) : ℕ) : ℝ) ^ tau) := by
      intro p
      have hprod :
          (∏ i, a i (p i)) * (∏ i, b i (p i)) * (∏ i, c i (p i)) =
            ∏ i, a i (p i) * b i (p i) * c i (p i) := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      rw [hprod, Nat.cast_prod]
      exact (Real.finsetProd_rpow Finset.univ
        (fun i ↦ ((a i (p i) * b i (p i) * c i (p i) : ℕ) : ℝ))
        (fun i hi ↦ Nat.cast_nonneg _) tau).symm
    calc
      (∏ i, lower i) ≤
          ∏ i, ∑ j : Fin (k i),
            (((a i j * b i j * c i j : ℕ) : ℝ) ^ tau) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact hlower i
        · intro i hi
          exact (hdata i).2
      _ = ∑ p : I, ∏ i,
          (((a i (p i) * b i (p i) * c i (p i) : ℕ) : ℝ) ^ tau) :=
        Fintype.prod_sum (fun i (j : Fin (k i)) ↦
          (((a i j * b i j * c i j : ℕ) : ℝ) ^ tau))
      _ = ∑ p : I,
          ((((∏ i, a i (p i)) * (∏ i, b i (p i)) *
            (∏ i, c i (p i)) : ℕ) : ℝ) ^ tau) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (hpoint p).symm
      _ = ∑ j : Fin q, (((A j * B j * C j : ℕ) : ℝ) ^ tau) := by
        simpa only [A, B, C] using
          (Equiv.sum_comp e (fun p : I ↦
            ((((∏ i, a i (p i)) * (∏ i, b i (p i)) *
              (∏ i, c i (p i)) : ℕ) : ℝ) ^ tau))).symm
