-- Prove2me | solution 1 for mme_sum_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-30T19:22:50.275777+00:00
-- url     : https://prove2.me/submissions/bb141aac-7da1-464f-9162-f6b2f1d84674

import Theorems.Thm_mme_sum_inequality_pos
import Theorems.Thm_mme_bridge_asymptoticRank
import Theorems.Thm_mme_matMulExp_strassen_pos
import Theorems.Thm_mme_MMq_eq_zero_of_not_pos

/-! # Sketch: the concrete sum inequality (zero-dimension reduction)

`mme_sum_inequality` allows zero dimensions, but the asymptotic-spectrum argument
(`mme_sum_inequality_pos`) needs `1 ≤ nᵢ, mᵢ, pᵢ`. When some dimension is `0` the
corresponding `MMObj` is the zero tensor, so its quotient class `MMq` is `0`
(`mme_MMq_eq_zero_of_not_pos`) and it drops out of the abstract sum without changing the
asymptotic rank; correspondingly `(nᵢmᵢpᵢ)^(ω/3) = 0^(ω/3) = 0` (using `ω/3 > 0` from
`mme_matMulExp_strassen_pos`) so the real summand vanishes too. Hence the general case
reduces to the all-positive case applied to the positive subfamily reindexed onto
`Fin S.card`, transporting `h` along bridge A (`mme_bridge_asymptoticRank`). -/

open MME BigOperators

universe u

theorem solution {K : Type u} [Field K] {k : ℕ} (n m p : Fin k → ℕ) (r : ℕ)
    (h : tensorAsymptoticRank (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) ≤ r) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) ≤ r := by
  classical
  -- The positive subfamily `S` and its reindexing `e : Fin S.card ≃ {x // x ∈ S}`.
  set S : Finset (Fin k) := Finset.univ.filter (fun i => 1 ≤ n i ∧ 1 ≤ m i ∧ 1 ≤ p i) with hS
  set e : Fin S.card ≃ {x // x ∈ S} := (S.equivFin).symm with he
  -- Positivity holds on the reindexed family.
  have hmemS : ∀ x : {x // x ∈ S}, 1 ≤ n x.1 ∧ 1 ≤ m x.1 ∧ 1 ≤ p x.1 := by
    intro x
    have hx : x.1 ∈ Finset.univ.filter (fun i => 1 ≤ n i ∧ 1 ≤ m i ∧ 1 ≤ p i) := hS ▸ x.2
    exact (Finset.mem_filter.mp hx).2
  have hn' : ∀ j : Fin S.card, 1 ≤ n (e j).1 := fun j => (hmemS (e j)).1
  have hm' : ∀ j : Fin S.card, 1 ≤ m (e j).1 := fun j => (hmemS (e j)).2.1
  have hp' : ∀ j : Fin S.card, 1 ≤ p (e j).1 := fun j => (hmemS (e j)).2.2
  -- KEY (tensor side): the abstract sum over the positive subfamily equals the abstract
  -- sum over the full family, because the off-`S` `MMq` terms are `0`.
  have hsum_eq :
      (∑ j : Fin S.card, MMq K (n (e j).1) (m (e j).1) (p (e j).1))
        = ∑ i, MMq K (n i) (m i) (p i) := by
    rw [show (∑ j : Fin S.card, MMq K (n (e j).1) (m (e j).1) (p (e j).1))
          = ∑ x : {x // x ∈ S}, MMq K (n x.1) (m x.1) (p x.1) from
        Equiv.sum_comp e (fun x => MMq K (n x.1) (m x.1) (p x.1))]
    rw [Finset.sum_coe_sort S (fun i => MMq K (n i) (m i) (p i))]
    refine Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => ?_)
    rw [hS, Finset.mem_filter] at hi
    exact mme_MMq_eq_zero_of_not_pos (fun hpos => hi ⟨Finset.mem_univ i, hpos⟩)
  -- Transport `h` to the positive subfamily via `mme_bridge_asymptoticRank` (both directions).
  have h' : tensorAsymptoticRank
      (TensorObj.bigAdd (fun j => MMObj K (n (e j).1) (m (e j).1) (p (e j).1))) ≤ r := by
    rw [← mme_bridge_asymptoticRank (fun j => n (e j).1) (fun j => m (e j).1) (fun j => p (e j).1),
        hsum_eq, mme_bridge_asymptoticRank n m p]
    exact h
  -- Run the all-positive case on the reindexed subfamily.
  -- Explicit `MME.` qualification: on the platform, both the imported Theorem node
  -- `_root_.mme_sum_inequality_pos` (from `Thm_mme_sum_inequality_pos`) and
  -- `MME.mme_sum_inequality_pos` (from `Def_mme_tensor_bridge`) are visible under the
  -- `open MME` above, so the unqualified name is ambiguous server-side.
  have hpos := MME.mme_sum_inequality_pos
    (fun j => n (e j).1) (fun j => m (e j).1) (fun j => p (e j).1) hn' hm' hp' r h'
  -- KEY (real side): the subfamily sum equals the full sum (off-`S` summands are `0^(ω/3)`).
  have hexp_ne : matMulExp_strassen K / 3 ≠ 0 := by
    have := mme_matMulExp_strassen_pos (K := K); positivity
  have hreal_eq :
      (∑ j : Fin S.card, ((n (e j).1 * m (e j).1 * p (e j).1 : ℕ) : ℝ) ^ (matMulExp_strassen K / 3))
        = ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) := by
    rw [show (∑ j : Fin S.card,
            ((n (e j).1 * m (e j).1 * p (e j).1 : ℕ) : ℝ) ^ (matMulExp_strassen K / 3))
          = ∑ x : {x // x ∈ S},
            ((n x.1 * m x.1 * p x.1 : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) from
        Equiv.sum_comp e
          (fun x => ((n x.1 * m x.1 * p x.1 : ℕ) : ℝ) ^ (matMulExp_strassen K / 3))]
    rw [Finset.sum_coe_sort S
      (fun i => ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3))]
    refine Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => ?_)
    rw [hS, Finset.mem_filter] at hi
    have hnp : ¬ (1 ≤ n i ∧ 1 ≤ m i ∧ 1 ≤ p i) := fun hpos => hi ⟨Finset.mem_univ i, hpos⟩
    have hzero : n i * m i * p i = 0 := by
      rcases (by omega : n i = 0 ∨ m i = 0 ∨ p i = 0) with h0 | h0 | h0 <;>
        simp [h0]
    rw [hzero, Nat.cast_zero, Real.zero_rpow hexp_ne]
  rwa [hreal_eq] at hpos
