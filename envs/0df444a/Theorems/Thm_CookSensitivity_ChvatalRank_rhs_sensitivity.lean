-- Prove2me | Theorems.Thm_CookSensitivity_ChvatalRank_rhs_sensitivity
-- name    : CookSensitivity.ChvatalRank.rhs_sensitivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:37:56.980284+00:00
-- url     : https://prove2.me/theorems/b30ee461-5321-4b65-ba77-7f2044e32a71
-- title:
--   Theorem 5 — optimal solutions move by at most $n\Delta(A)\|b-b'\|_\infty$ (LP) and $n\Delta(A)(\|b-b'\|_\infty+2)$ (IP)
-- statement:
--   Let $A$ be an integral $m\times n$ matrix and $b, b' \in \mathbb{Q}^m$, $w\in\mathbb{Q}^n$ such that $\max\{wx : Ax\le b\}$ and $\max\{wx : Ax\le b'\}$ both have optimal solutions. Then
--
--   1. for each optimal solution $\bar x$ of $\max\{wx : Ax \le b\}$ there is an optimal solution $\bar x'$ of $\max\{wx : Ax\le b'\}$ with
--   $$\|\bar x - \bar x'\|_\infty \le n\,\Delta(A)\,\|b-b'\|_\infty;$$
--   2. if $Ax \le b$ and $Ax\le b'$ both have integral solutions, then for each optimal solution $\bar z$ of $\max\{wx : Ax\le b,\ x\text{ integral}\}$ there is an optimal solution $\bar z'$ of $\max\{wx : Ax\le b',\ x\text{ integral}\}$ with
--   $$\|\bar z - \bar z'\|_\infty \le n\,\Delta(A)\,(\|b-b'\|_\infty + 2).$$
--
--   A change of the right-hand side therefore moves optimal solutions, and hence optimal values, by an amount affine in $\|b - b'\|_\infty$, sharpening a result of Blair and Jeroslow.
--
--   **Formalization Note** No hypothesis $A\ne0$ is needed; for $A = 0$ both parts hold with $\bar x' = \bar x$, $\bar z' = \bar z$.
-- source:
--   Cook, Gerards, Schrijver, Tardos, Sensitivity theorems in integer linear programming, Math. Programming 34 (1986), p. 255, Theorem 5

import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_maxSubdet
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace CookSensitivity.ChvatalRank

open Matrix

theorem rhs_sensitivity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b b' : Fin m → ℚ) (w : Fin n → ℚ)
    (hmax : ∃ x, IsLPOptimal A b w x) (hmax' : ∃ x, IsLPOptimal A b' w x) :
    (∀ xbar, IsLPOptimal A b w xbar →
      ∃ xbar', IsLPOptimal A b' w xbar' ∧
        supNorm (xbar - xbar') ≤ (n : ℚ) * (maxSubdet A : ℚ) * supNorm (b - b')) ∧
    ((∃ x ∈ polyhedron A b, IsIntegral x) → (∃ x ∈ polyhedron A b', IsIntegral x) →
      ∀ zbar, IsIPOptimal A b w zbar →
        ∃ zbar', IsIPOptimal A b' w zbar' ∧
          supNorm (zbar - zbar') ≤ (n : ℚ) * (maxSubdet A : ℚ) * (supNorm (b - b') + 2)) := by sorry

end CookSensitivity.ChvatalRank
