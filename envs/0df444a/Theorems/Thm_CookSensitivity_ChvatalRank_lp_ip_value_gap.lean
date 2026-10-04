-- Prove2me | Theorems.Thm_CookSensitivity_ChvatalRank_lp_ip_value_gap
-- name    : CookSensitivity.ChvatalRank.lp_ip_value_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:37:48.16057+00:00
-- url     : https://prove2.me/theorems/308aa197-679f-4042-9ded-017512ca92bc
-- title:
--   Corollary 2 — the LP–IP optimal value gap is at most $n\Delta(A)\|w\|_1$
-- statement:
--   Let $A$ be an integral $m \times n$ matrix, $b\in\mathbb{Q}^m$ and $w \in \mathbb{Q}^n$ such that $Ax\le b$ has an integral solution and $\max\{wx : Ax \le b\}$ exists, attained at $\bar x$. Then $\max\{wx : Ax\le b,\ x \text{ integral}\}$ is attained at some $\bar z$, and
--
--   $$\max\{wx : Ax \le b\} - \max\{wx : Ax\le b,\ x\text{ integral}\} = w\bar x - w\bar z \le n\,\Delta(A)\,\|w\|_1. \tag{4}$$
--
--   This sharpens results of Blair and Jeroslow on the integrality gap and is the estimate (16) used in the proof of the Chvátal rank bound.
--
--   **Formalization Note** Existence of the integer optimum is part of the conclusion. No hypothesis $A \neq 0$ is needed: for $A = 0$ the LP maximum exists only if $w = 0$.
-- source:
--   Cook, Gerards, Schrijver, Tardos, Sensitivity theorems in integer linear programming, Math. Programming 34 (1986), p. 253, Corollary 2, eq. (4)

import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_maxSubdet
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace CookSensitivity.ChvatalRank

open Matrix

theorem lp_ip_value_gap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) (w : Fin n → ℚ)
    (hint : ∃ x ∈ polyhedron A b, IsIntegral x)
    (xbar : Fin n → ℚ) (hxbar : IsLPOptimal A b w xbar) :
    ∃ zbar, IsIPOptimal A b w zbar ∧
      w ⬝ᵥ xbar - w ⬝ᵥ zbar ≤ (n : ℚ) * (maxSubdet A : ℚ) * l1Norm w := by sorry

end CookSensitivity.ChvatalRank
