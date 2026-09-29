-- Prove2me | solution 1 for mme_HasTauValueAtLeast_permObj_swapFirstTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:31:12.243527+00:00
-- url     : https://prove2.me/submissions/b28fcf58-8381-4e85-badc-caccd460a4fa

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Theorems.Thm_mme_HasTauValueAtLeast_to_cofinal_finite_extractions
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open MME BigOperators Filter Topology

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem swapped_bigAdd_MM_iso_for_tau
    {K : Type u} [Field K] {k : ℕ}
    (a b c : Fin k → ℕ) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun j ↦ MMObj K (c j) (b j) (a j)))
      (TensorObj.permObj swapFirstTwoPerm
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))) := by
  rw [← TensorQ.toQ_eq_iff]
  rw [TensorQ.toQ_bigAdd]
  calc
    (∑ j : Fin k, TensorQ.toQ (MMObj K (c j) (b j) (a j))) =
        ∑ j : Fin k, TensorQ.toQ
          (TensorObj.permObj swapFirstTwoPerm
            (MMObj K (a j) (b j) (c j))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (TensorQ.toQ_eq_iff.mpr
        (mme_MMObj_permObj_swapFirstTwo
          (K := K) (a j) (b j) (c j))).symm
    _ = ∑ j : Fin k, TensorQ.permAut swapFirstTwoPerm
          (TensorQ.toQ (MMObj K (a j) (b j) (c j))) := by
      rfl
    _ = TensorQ.permAut swapFirstTwoPerm
          (∑ j : Fin k, TensorQ.toQ (MMObj K (a j) (b j) (c j))) := by
      rw [map_sum]
    _ = TensorQ.permAut swapFirstTwoPerm
          (TensorQ.toQ
            (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))) := by
      rw [TensorQ.toQ_bigAdd]
    _ = TensorQ.toQ
          (TensorObj.permObj swapFirstTwoPerm
            (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))) := by
      rw [TensorQ.permAut_toQ]

private theorem permObj_swap_kronPow_iso_for_tau
    {K : Type u} [Field K] (T : TensorObj K 3) (N : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj swapFirstTwoPerm (T.kronPow N))
      ((TensorObj.permObj swapFirstTwoPerm T).kronPow N) := by
  rw [← TensorQ.toQ_eq_iff]
  change TensorQ.permAut swapFirstTwoPerm
      (TensorQ.toQ (T.kronPow N)) =
    TensorQ.toQ ((TensorObj.permObj swapFirstTwoPerm T).kronPow N)
  rw [TensorQ.toQ_kronPow, map_pow, TensorQ.toQ_kronPow,
    TensorQ.permAut_toQ]

theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {tau V : ℝ}
    (h : HasTauValueAtLeast T tau V) :
    HasTauValueAtLeast
      (TensorObj.permObj swapFirstTwoPerm T) tau V := by
  obtain ⟨s, error, hs, herror, _herrorPos, hextract⟩ :=
    mme_HasTauValueAtLeast_to_cofinal_finite_extractions T tau V h
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (TensorObj.permObj swapFirstTwoPerm T) tau V h.1
      s hs error herror
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨k, a, b, c, hrestrict, hweight⟩ := hextract n
  refine ⟨k, c, b, a, ?_, ?_⟩
  · have hperm :=
      TensorObj.permObj_restrict swapFirstTwoPerm hrestrict
    exact TensorObj.Restrict.trans
      (swapped_bigAdd_MM_iso_for_tau a b c).1
      (TensorObj.Restrict.trans hperm
        (permObj_swap_kronPow_iso_for_tau T (s n)).1)
  · simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      hweight
