-- Prove2me | Theorems.Thm_CookSensitivity_ChvatalRank_integerHull_eq_of_bounded_matrix
-- name    : CookSensitivity.ChvatalRank.integerHull_eq_of_bounded_matrix
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:38:18.854807+00:00
-- url     : https://prove2.me/theorems/b26d96de-50bf-425b-861a-4fbf18e23a79
-- title:
--   Theorem 7 — one integral matrix $M$ with entries $\le n^{2n}\Delta(A)^n$ describes every $\{x : Ax\le b\}_I$
-- statement:
--   Let $A$ be an integral $m \times n$ matrix. There exists an integral matrix $M$ (with some finite number $N$ of rows) whose entries satisfy
--   $$|M_{ij}| \le n^{2n}\,\Delta(A)^n,$$
--   such that for every $b \in \mathbb{Q}^m$ for which $Ax \le b$ has an integral solution there is a vector $d_b \in \mathbb{Q}^N$ with
--   $$\{x : Ax\le b\}_I = \{x : Mx \le d_b\}.$$
--
--   The matrix $M$ is chosen once for $A$ and works for every right-hand side; only $d_b$ depends on $b$. The coefficient bound is polynomial in $n$ and the largest entry of $A$ and independent of $m$ (implying a result of Karp and Papadimitriou), and it is what makes the Chvátal rank bound of Theorem 10 independent of $b$.
--
--   **Formalization Note** $M$ and $N$ are quantified before $b$. The right-hand side $b$ is rational, as on the page. No $A \ne 0$ is needed (for $A=0$ take $M$ with no rows when $n \ge 1$).
-- source:
--   Cook, Gerards, Schrijver, Tardos, Sensitivity theorems in integer linear programming, Math. Programming 34 (1986), p. 257, Theorem 7

import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_maxSubdet
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace CookSensitivity.ChvatalRank

open Matrix

theorem integerHull_eq_of_bounded_matrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ (N : ℕ) (M : Matrix (Fin N) (Fin n) ℤ),
      (∀ i j, |M i j| ≤ ((n ^ (2 * n) * maxSubdet A ^ n : ℕ) : ℤ)) ∧
      ∀ b : Fin m → ℚ, (∃ x ∈ polyhedron A b, IsIntegral x) →
        ∃ d : Fin N → ℚ,
          integerHull (polyhedron A b) = {x | (M.map (Int.cast : ℤ → ℚ)) *ᵥ x ≤ d} := by sorry

end CookSensitivity.ChvatalRank
