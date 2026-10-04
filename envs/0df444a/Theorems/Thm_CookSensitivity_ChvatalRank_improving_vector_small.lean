-- Prove2me | Theorems.Thm_CookSensitivity_ChvatalRank_improving_vector_small
-- name    : CookSensitivity.ChvatalRank.improving_vector_small
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:38:07.912807+00:00
-- url     : https://prove2.me/theorems/2b010e22-87e7-44d4-9591-d13dcb33f437
-- title:
--   Theorem 6 — a non-optimal integral solution has an improving integral solution within distance $n\Delta(A)$
-- statement:
--   Let $A$ be a nonzero integral $m\times n$ matrix, $b\in\mathbb{Q}^m$, $w\in\mathbb{Q}^n$, and consider the integer program $\max\{wx : Ax\le b,\ x \text{ integral}\}$. Then for each integral solution $z$ of $Ax\le b$, either $z$ is an optimal solution of the integer program, or there is an integral solution $\bar z$ of $Ax \le b$ with
--
--   $$\|z-\bar z\|_\infty \le n\,\Delta(A) \quad\text{and}\quad w\bar z > wz.$$
--
--   Thus the integral vectors with entries at most $n\Delta(A)$ in absolute value form a test set for every integer program with constraint matrix $A$ (improving on Graver and on Blair–Jeroslow); this is the ingredient that bounds the coefficients in Theorem 7.
--
--   **Formalization Note** No assumption that the integer program has an optimum is made: $w$ is arbitrary. The hypothesis $A\neq0$ is added: for $A=0$, $w \ne 0$ and $b \ge 0$, no $z$ is optimal and no $\bar z$ at distance $0$ improves on $z$.
-- source:
--   Cook, Gerards, Schrijver, Tardos, Sensitivity theorems in integer linear programming, Math. Programming 34 (1986), p. 256, Theorem 6

import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_maxSubdet
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace CookSensitivity.ChvatalRank

open Matrix

theorem improving_vector_small {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : A ≠ 0)
    (b : Fin m → ℚ) (w : Fin n → ℚ)
    (z : Fin n → ℚ) (hz : IsIntegral z) (hzP : z ∈ polyhedron A b) :
    IsIPOptimal A b w z ∨
      ∃ zbar, IsIntegral zbar ∧ zbar ∈ polyhedron A b ∧
        supNorm (z - zbar) ≤ (n : ℚ) * (maxSubdet A : ℚ) ∧ w ⬝ᵥ zbar > w ⬝ᵥ z := by sorry

end CookSensitivity.ChvatalRank
