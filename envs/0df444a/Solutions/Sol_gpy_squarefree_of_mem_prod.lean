-- Prove2me | solution 1 for gpy_squarefree_of_mem_prod
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T02:48:21.342975+00:00
-- url     : https://prove2.me/submissions/d1902ed0-03f0-47f2-84c8-c60a0e041332

/- Submission file for `gpy_squarefree_of_mem_prod` (publish2 good-count batch).
Self-contained: imports Mathlib only.
   Top-level `theorem solution` in the problem's exact binder/statement
   form. No sorry tactic, no axioms beyond the standard ones, no platform
   imports. -/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

theorem solution {k : ℕ} {d : Fin k → ℕ} {j : Fin k}
    (hsq : Squarefree (∏ i, d i)) : Squarefree (d j) := by
  apply Nat.squarefree_of_factorization_le_one
  · intro h0
    exact hsq.ne_zero (Finset.prod_eq_zero (Finset.mem_univ j) h0)
  · intro q
    have hall : ∀ i ∈ (Finset.univ : Finset (Fin k)), d i ≠ 0 := by
      intro i _ hi
      exact hsq.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    have hle : (d j).factorization q ≤ (∏ i, d i).factorization q := by
      rw [Nat.factorization_prod_apply hall]
      exact Finset.single_le_sum (f := fun x => (d x).factorization q)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    exact le_trans hle (Squarefree.natFactorization_le_one q hsq)
