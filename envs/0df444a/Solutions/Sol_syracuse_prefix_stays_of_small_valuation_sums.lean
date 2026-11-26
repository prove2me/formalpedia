-- Prove2me | solution 1 for syracuse_prefix_stays_of_small_valuation_sums
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T11:14:59.41623+00:00
-- url     : https://prove2.me/submissions/30cdfcd3-c201-492e-beec-8c370862ad59

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.Linarith

/-- A prefix cannot descend below its start while each cumulative dyadic
multiplier is at most the corresponding power of three. -/
theorem solution (n k : ℕ)
    (hsmall : ∀ j ≤ k,
      2^((Finset.range j).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) ≤ 3^j) :
    ∀ j ≤ k, n ≤ syracuseStep^[j] n := by
  let x (j : ℕ) := syracuseStep^[j] n
  let A (j : ℕ) := (Finset.range j).sum fun i => (3*x i+1).factorization 2
  have hproduct (j : ℕ) : 3^j*n ≤ 2^(A j)*x j := by
    induction j with
    | zero => simp [x,A]
    | succ j ih =>
      let a := (3*x j+1).factorization 2
      have hA : A (j+1) = A j+a := Finset.sum_range_succ _ _
      have hrow : 2^a*x (j+1) = 3*x j+1 := by
        have hx : x (j+1) = syracuseStep (x j) := Function.iterate_succ_apply' _ _ _
        rw [hx]
        exact Nat.ordProj_mul_ordCompl_eq_self _ _
      calc
        _ = 3*(3^j*n) := by rw [pow_succ]; ring
        _ ≤ 3*(2^(A j)*x j) := Nat.mul_le_mul_left _ ih
        _ = 2^(A j)*(3*x j) := by ring
        _ ≤ 2^(A j)*(3*x j+1) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
        _ = _ := by rw [hA, pow_add 2 (A j) a, mul_assoc, hrow]
  intro j hj
  have hle : 2^(A j)*n ≤ 3^j*n := Nat.mul_le_mul_right _ (hsmall j hj)
  exact Nat.le_of_mul_le_mul_left (hle.trans (hproduct j)) (Nat.two_pow_pos _)
