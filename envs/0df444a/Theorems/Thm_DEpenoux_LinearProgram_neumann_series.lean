-- Prove2me | Theorems.Thm_DEpenoux_LinearProgram_neumann_series
-- name    : DEpenoux.LinearProgram.neumann_series
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:00:51.06352+00:00
-- url     : https://prove2.me/theorems/1852f967-c619-4600-a2ed-29b5156083bd
-- title:
--   Eq. (3) — for a stochastic matrix $P$ and $0<\lambda<1$, $I-\lambda P$ is invertible and $(I-\lambda P)^{-1}=\sum_k \lambda^k P^k$
-- statement:
--   Let $P$ be an $m \times m$ stochastic matrix: all entries are nonnegative and every row sums to $1$. Let $0 < \lambda < 1$. Then the matrix $I - \lambda P$ is invertible, and its inverse is the sum of the Neumann series
--   $$ (I - \lambda P)^{-1} = I + \lambda P + \lambda^2 P^2 + \cdots = \sum_{k=0}^{\infty} \lambda^k P^k , $$
--   the series converging entrywise.
--
--   This is the "known and obvious property of stochastic matrices" from which d'Epenoux derives existence and uniqueness of the cost (2) of a strategy, and the positivity facts (4) and (5).
--
--   **Formalization Note** The matrix is any real square matrix indexed by `Fin m`; the series is a `HasSum` in the product (entrywise) topology on matrices, so no norm appears in the statement. `(1 - lam • P)⁻¹` is Mathlib's matrix inverse, which is the true inverse once `IsUnit` holds.
-- source:
--   d'Epenoux, A Probabilistic Production and Inventory Problem, Management Sci. 10 (1963), p. 100, Section 2, Eq. (3)

import Mathlib

namespace DEpenoux.LinearProgram

theorem neumann_series {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ)
    (hP0 : ∀ i k, 0 ≤ P i k) (hP1 : ∀ i, ∑ k, P i k = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    IsUnit (1 - lam • P) ∧
      HasSum (fun k : ℕ => lam ^ k • P ^ k) (1 - lam • P)⁻¹ := by sorry

end DEpenoux.LinearProgram
