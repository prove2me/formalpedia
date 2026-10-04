-- Prove2me | Theorems.Thm_CookSensitivity_ChvatalRank_lp_ip_proximity
-- name    : CookSensitivity.ChvatalRank.lp_ip_proximity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:37:38.628006+00:00
-- url     : https://prove2.me/theorems/2c698f9e-820b-40ea-b392-be7ca1320376
-- title:
--   Theorem 1 — LP and IP optima lie within $\ell_\infty$-distance $n\Delta(A)$ of each other
-- statement:
--   Let $A$ be a nonzero integral $m\times n$ matrix, $b \in \mathbb{Q}^m$, $w \in \mathbb{Q}^n$, and let $\Delta(A)$ be the largest absolute value of a subdeterminant of $A$. Suppose $Ax \le b$ has an integral solution and $\max\{wx : Ax \le b\}$ exists. Then
--
--   1. for each optimal solution $\bar x$ of $\max\{wx : Ax\le b\}$ there is an optimal solution $z^*$ of $\max\{wx : Ax \le b,\ x \text{ integral}\}$ with
--   $$\|\bar x - z^*\|_\infty \le n\,\Delta(A);$$
--   2. for each optimal solution $\bar z$ of $\max\{wx : Ax \le b,\ x \text{ integral}\}$ there is an optimal solution $x^*$ of $\max\{wx : Ax\le b\}$ with $\|\bar z - x^*\|_\infty \le n\,\Delta(A)$.
--
--   In particular the integer program has an optimal solution. The bound depends only on the number of variables and on $A$, not on $b$ or $w$; it is the basis of every other proximity and sensitivity result of the paper.
--
--   **Formalization Note** The hypothesis $A \ne 0$ is added. For $A = 0$ one has $\Delta(A) = 0$, and with $w = 0$, $b \ge 0$ and a non-integral $\bar x$ part 1 would ask for an integral point at distance $0$, which is false; the paper's proof assumes it implicitly (cf. "we may assume $A \neq 0$", p. 257).
-- source:
--   Cook, Gerards, Schrijver, Tardos, Sensitivity theorems in integer linear programming, Math. Programming 34 (1986), p. 252, Theorem 1

import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_maxSubdet
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace CookSensitivity.ChvatalRank

open Matrix

theorem lp_ip_proximity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : A ≠ 0)
    (b : Fin m → ℚ) (w : Fin n → ℚ)
    (hint : ∃ x ∈ polyhedron A b, IsIntegral x)
    (hmax : ∃ x, IsLPOptimal A b w x) :
    (∀ xbar, IsLPOptimal A b w xbar →
      ∃ zstar, IsIPOptimal A b w zstar ∧
        supNorm (xbar - zstar) ≤ (n : ℚ) * (maxSubdet A : ℚ)) ∧
    (∀ zbar, IsIPOptimal A b w zbar →
      ∃ xstar, IsLPOptimal A b w xstar ∧
        supNorm (zbar - xstar) ≤ (n : ℚ) * (maxSubdet A : ℚ)) := by sorry

end CookSensitivity.ChvatalRank
