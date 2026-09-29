-- Prove2me | solution 1 for mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:29:33.310165+00:00
-- url     : https://prove2.me/submissions/2f0ec062-b16d-44c5-8820-5e3b2f017c79

import Mathlib.Data.Fintype.Card
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Theorems.Thm_mme_Ctensor_three_one_H_one_direct_behrend_extraction
import Theorems.Thm_mme_Ctensor_outer_triple_distribution
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_bigAdd_fin_mul_isomorphic_nested

open MME BigOperators

universe u

set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {A H volume : ℕ}
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (hH : 0 < H) :
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
        (cyclicSymmetrization T) ∧
      (A : ℝ) ^ 3 *
          ((H : ℝ) ^ 2 *
            Real.exp (-100 * Real.sqrt
              (Real.log (((H + 1 : ℕ) : ℝ))))) ≤
        (k : ℝ) ∧
      (∀ i, a i * b i * c i = volume ^ 3) := by
  classical
  let I := Fin A × Fin A × Fin A
  let n : ℕ := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let block : Fin n → TensorObj K 3 := fun j =>
    let p := e.symm j
    threeStarCyclicProduct
      (stars.star p.1) (stars.star p.2.1) (stars.star p.2.2)
  let L : ℝ :=
    (H : ℝ) ^ 2 *
      Real.exp (-100 * Real.sqrt
        (Real.log (((H + 1 : ℕ) : ℝ))))
  let q : ℕ := Nat.ceil L
  have hL0 : 0 ≤ L := by
    dsimp [L]
    positivity
  have hLq : L ≤ (q : ℝ) := by
    simpa only [q] using Nat.le_ceil L
  have hextract : ∀ j : Fin n,
      ∃ (a b c : Fin q → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
          (block j) ∧
        (∀ i, a i * b i * c i = volume ^ 3) := by
    intro j
    let p := e.symm j
    obtain ⟨k, a, b, c, hrestrict, hk, hvolume⟩ :=
      mme_Ctensor_three_one_H_one_direct_behrend_extraction
        (stars.certificate p.1)
        (stars.certificate p.2.1)
        (stars.certificate p.2.2) hH
    have hqk : q ≤ k := by
      apply Nat.ceil_le.mpr
      simpa only [q, L] using hk
    let a' : Fin q → ℕ := fun i ↦ a (Fin.castLE hqk i)
    let b' : Fin q → ℕ := fun i ↦ b (Fin.castLE hqk i)
    let c' : Fin q → ℕ := fun i ↦ c (Fin.castLE hqk i)
    have hprefix : TensorObj.Restrict
        (TensorObj.bigAdd (fun i ↦ MMObj K (a' i) (b' i) (c' i)))
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i))) := by
      simpa only [a', b', c'] using
        (mme_bigAdd_prefix_restrict (K := K) (d := 3)
          (by omega) hqk (fun i ↦ MMObj K (a i) (b i) (c i)))
    refine ⟨a', b', c', ?_, ?_⟩
    · simpa only [block, p] using
        TensorObj.Restrict.trans hprefix hrestrict
    · intro i
      exact hvolume (Fin.castLE hqk i)
  choose a b c hrestrict hvolume using hextract
  let X : Fin n → Fin q → TensorObj K 3 := fun j i ↦
    MMObj K (a j i) (b j i) (c j i)
  have hnested : TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin n ↦
        TensorObj.bigAdd (fun i : Fin q ↦ X j i)))
      (TensorObj.bigAdd block) := by
    apply mme_bigAdd_mono_restrict
    intro j
    simpa only [X] using hrestrict j
  have hflat : TensorObj.Restrict
      (TensorObj.bigAdd (fun r : Fin (n * q) ↦
        X (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2))
      (TensorObj.bigAdd block) :=
    TensorObj.Restrict.trans
      (mme_bigAdd_fin_mul_isomorphic_nested X).1 hnested
  have hdist : TensorObj.Restrict (TensorObj.bigAdd block)
      (cyclicSymmetrization (TensorObj.bigAdd stars.star)) := by
    simpa only [I, n, e, block] using
      (mme_Ctensor_outer_triple_distribution stars.star)
  have hsource : TensorObj.Restrict (TensorObj.bigAdd block)
      (cyclicSymmetrization T) :=
    TensorObj.Restrict.trans hdist
      (mme_cyclicSymmetrization_mono_restrict stars.restrict)
  let flatA : Fin (n * q) → ℕ := fun r ↦
    a (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2
  let flatB : Fin (n * q) → ℕ := fun r ↦
    b (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2
  let flatC : Fin (n * q) → ℕ := fun r ↦
    c (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2
  refine ⟨n * q, flatA, flatB, flatC, ?_, ?_, ?_⟩
  · exact TensorObj.Restrict.trans
      (by simpa only [X, flatA, flatB, flatC] using hflat) hsource
  · have hn : n = A ^ 3 := by
      dsimp [n, I]
      simp [pow_three]
    have hncast : (n : ℝ) = (A : ℝ) ^ 3 := by
      rw [hn]
      norm_num
    rw [← hncast]
    calc
      (n : ℝ) * L ≤ (n : ℝ) * q :=
        mul_le_mul_of_nonneg_left hLq (Nat.cast_nonneg n)
      _ = ((n * q : ℕ) : ℝ) := by norm_num
  · intro r
    exact hvolume (finProdFinEquiv.symm r).1
      (finProdFinEquiv.symm r).2
