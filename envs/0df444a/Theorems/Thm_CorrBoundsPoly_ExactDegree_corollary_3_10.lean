-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_corollary_3_10
-- name    : CorrBoundsPoly.ExactDegree.corollary_3_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:58:53.022202+00:00
-- url     : https://prove2.me/theorems/4ffeae9b-9cb3-4f73-b6e7-1fcfdb24ad72
-- title:
--   Corollary 3.10 — $\eta(m,D)\ge\cos(\pi/(2D))^m\ge\exp(-\pi^2m/(4D^2))$, so $\eta(m,D)=\exp[-\Theta(m/D^2)]$
-- statement:
--   Let $D\ge2$ be dyadic.
--   1. For all $m\ge0$,
--   $$\eta(m,D)\ge\cos\Big(\frac{\pi}{2D}\Big)^m\ge\exp\Big(-\frac{\pi^2m}{4D^2}\Big). \tag{3.14}$$
--   2. Combined with Corollary 3.7, $\eta(m,D)=\exp[-\Theta(m/D^2)]$ uniformly for $m\ge D^2$; explicitly, for every $m\ge D^2$,
--   $$\exp\Big(-\frac{\pi^2m}{4D^2}\Big)\le\eta(m,D)\le\exp\Big(-\frac{m}{2D^2}\Big).$$
--
--   The lower bound is what makes the correlation scale of the exact-degree cores tight (the lower bound in Theorem 4.1).
--
--   Differences from the source:
--   - reading: "$\eta(m,D)=\exp[-\Theta(m/D^2)]$ uniformly for $m\ge D^2$" → the two-sided bound with the explicit constants $\pi^2/4$ (from (3.14)) and $1/2$ (from Corollary 3.7, via $a_D(m)=\eta(m,D)$); reason: these are the constants the sentence combines; they imply the $\Theta$ statement with absolute constants
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 30 (PDF 32), Corollary 3.10, Eq. (3.14)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_ElemSym

namespace CorrBoundsPoly.ExactDegree

/-- **Corollary 3.10** (A matching lower bound for dyadic cores; Xin Li, *More on Correlation Bounds
for Polynomials*, p. 30, PDF 32). For dyadic `D ≥ 2`: (1) for all `m ≥ 0`,
`η(m, D) ≥ cos(π/(2D))^m ≥ exp(−π²m/(4D²))` (Eq. (3.14)); (2) combined with Corollary 3.7,
`η(m, D) = exp[−Θ(m/D²)]` uniformly for `m ≥ D²`, with the explicit constants
`exp(−π²m/(4D²)) ≤ η(m, D) ≤ exp(−m/(2D²))`. -/
theorem corollary_3_10 (D : ℕ) (hD : IsDyadic D) (hD2 : 2 ≤ D) :
    (∀ m : ℕ, Real.cos (Real.pi / (2 * D)) ^ m ≤ eta m D ∧
      Real.exp (-(Real.pi ^ 2 * m) / (4 * (D : ℝ) ^ 2)) ≤ Real.cos (Real.pi / (2 * D)) ^ m) ∧
    (∀ m : ℕ, D ^ 2 ≤ m →
      Real.exp (-(Real.pi ^ 2 * m) / (4 * (D : ℝ) ^ 2)) ≤ eta m D ∧
      eta m D ≤ Real.exp (-(m : ℝ) / (2 * (D : ℝ) ^ 2))) := by sorry

end CorrBoundsPoly.ExactDegree
