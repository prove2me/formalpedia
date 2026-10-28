-- Prove2me | solution 1 for gpy_abel_sum
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T17:11:32.842229+00:00
-- url     : https://prove2.me/submissions/b69d29a1-05ae-449e-a8b6-839bdd77bcea

/-
  Submission file for the Prove2Me problem `gpy_abel_sum`
  (Abel summation by parts for real sequences).

  Self-contained: imports Mathlib only. Top-level `theorem solution`
  is the pure Mathlib statement, proved by the verified induction
  proof. No sorry tactic, no axioms beyond the standard ones, no
  platform imports.
-/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

theorem solution (a f : ℕ → ℝ) : ∀ n : ℕ,
    ∑ i ∈ Finset.range (n + 1), a i * f i
      = (∑ i ∈ Finset.range (n + 1), a i) * f n
        - ∑ i ∈ Finset.range n, (∑ j ∈ Finset.range (i + 1), a j) * (f (i + 1) - f i) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := Finset.sum_range_succ (fun i => a i * f i) (n + 1)
    have h2 := Finset.sum_range_succ (fun i => a i) (n + 1)
    have h3 := Finset.sum_range_succ
      (fun i => (∑ j ∈ Finset.range (i + 1), a j) * (f (i + 1) - f i)) n
    rw [h1, h2, h3, ih]
    ring
