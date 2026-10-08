-- Prove2me | Theorems.Thm_DEpenoux_LinearProgram_sub_lam_mul_nonneg
-- name    : DEpenoux.LinearProgram.sub_lam_mul_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:00:48.535275+00:00
-- url     : https://prove2.me/theorems/e5a78f3c-f027-4ce0-93ca-d14acb57066b
-- title:
--   Eq. (4) — for a stochastic matrix $P$ and $0<\lambda<1$, $u-\lambda Pu\ge 0$ implies $u\ge 0$
-- statement:
--   Let $P$ be an $m \times m$ stochastic matrix (nonnegative entries, unit row sums), let $0 < \lambda < 1$, and let $u \in \mathbb{R}^m$ be any vector. If
--   $$ u - \lambda P u \ge 0 $$
--   componentwise, then $u \ge 0$ componentwise.
--
--   This is d'Epenoux's (4), the comparison principle used in Section 5 to show that every point of the constraint set $A$ lies below every strategy cost, and in Section 3 to compare strategies.
--
--   **Formalization Note** $P u$ is `Matrix.mulVec P u`; both inequalities are stated coordinate by coordinate.
-- source:
--   d'Epenoux, A Probabilistic Production and Inventory Problem, Management Sci. 10 (1963), p. 100, Section 2, Eq. (4)

import Mathlib

namespace DEpenoux.LinearProgram

theorem sub_lam_mul_nonneg {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ)
    (hP0 : ∀ i k, 0 ≤ P i k) (hP1 : ∀ i, ∑ k, P i k = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (u : Fin m → ℝ)
    (h : ∀ i, 0 ≤ u i - lam * Matrix.mulVec P u i) :
    ∀ i, 0 ≤ u i := by sorry

end DEpenoux.LinearProgram
