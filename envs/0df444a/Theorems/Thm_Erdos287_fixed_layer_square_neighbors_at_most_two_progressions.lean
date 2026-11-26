-- Prove2me | Theorems.Thm_Erdos287_fixed_layer_square_neighbors_at_most_two_progressions
-- name    : Erdos287.fixed_layer_square_neighbors_at_most_two_progressions
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:23:57.963593+00:00
-- url     : https://prove2.me/theorems/c28a0f1e-a825-5025-bdb9-3cfe15ebfcd8
-- title:
--   Square-layer neighbors occupy at most two progression classes
-- statement:
--   Let $p$ be a prime which does not divide $b$, and fix an integer $\epsilon$. In a finite set of natural numbers $Q\subseteq[0,U]$, at most $2(\lfloor U/p\rfloor+1)$ elements $q$ satisfy $p\mid bq^2+\epsilon$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.fixed_layer_square_neighbors_at_most_two_progressions (p b U : ℕ) (e : ℤ) (Q : Finset ℕ) (hp : p.Prime) (hb : ¬ p ∣ b)
    (hQ : ∀ q ∈ Q, q ≤ U) :
    (Q.filter (fun q : ℕ => (p : ℤ) ∣ (b : ℤ) * (q : ℤ) ^ 2 + e)).card ≤
      2 * (U / p + 1) := by sorry
