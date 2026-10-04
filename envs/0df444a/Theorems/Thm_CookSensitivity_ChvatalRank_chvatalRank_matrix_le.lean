-- Prove2me | Theorems.Thm_CookSensitivity_ChvatalRank_chvatalRank_matrix_le
-- name    : CookSensitivity.ChvatalRank.chvatalRank_matrix_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:06:36.529193+00:00
-- url     : https://prove2.me/theorems/168c0e9f-9231-43b7-a292-0577a513b0fc
-- title:
--   Theorem 10 — the Chvátal rank of an integral $m\times n$ matrix is at most $2^{n^3+1}n^{5n}\Delta(A)^{n+1}$
-- statement:
--   Let $A$ be an integral $m\times n$ matrix and $\Delta(A)$ the largest absolute value of a subdeterminant of $A$. For every integral vector $b\in\mathbb{Z}^m$, the Chvátal rank of the polyhedron $\{x \in \mathbb{Q}^n : Ax \le b\}$ (the least $t$ with $P^{(t)} = P_I$) is finite, and the supremum over all integral $b$ satisfies
--
--   $$\operatorname{rank}(A) \;=\; \sup_{b\in\mathbb{Z}^m} \operatorname{rank}\{x : Ax\le b\} \;\le\; 2^{n^3+1}\, n^{5n}\, \Delta(A)^{n+1}.$$
--
--   So every integral matrix has finite Chvátal rank, bounded by a function of $n$ and $\Delta(A)$ alone, independently of $m$ and of the right-hand side.
--
--   **Formalization Note** The rank of a polyhedron is valued in $\mathbb{N}\cup\{\infty\}$ (`ℕ∞`, $\infty$ when no $t$ works) and the rank of $A$ is the supremum in `ℕ∞` over integral $b$, so the inequality asserts finiteness. The bound is computed in `ℕ` (with $0^0 = 1$) and cast. No hypothesis $A \ne 0$ is needed: for $A = 0$ and integral $b$ the polyhedron is $\emptyset$ or $\mathbb{Q}^n$, both of rank $0$.
-- source:
--   Cook, Gerards, Schrijver, Tardos, Sensitivity theorems in integer linear programming, Math. Programming 34 (1986), p. 260, Theorem 10

import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_maxSubdet
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram
import Definitions.Def_CookSensitivity_ChvatalRank_ChvatalClosure

namespace CookSensitivity.ChvatalRank

theorem chvatalRank_matrix_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    chvatalRankMatrix A ≤ ((2 ^ (n ^ 3 + 1) * n ^ (5 * n) * maxSubdet A ^ (n + 1) : ℕ) : ℕ∞) := by sorry

end CookSensitivity.ChvatalRank
