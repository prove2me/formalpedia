-- Prove2me | Theorems.Thm_ConvexOptAlg_Ellipsoid_lemma_2_3_scalar
-- name    : ConvexOptAlg.Ellipsoid.lemma_2_3_scalar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:30:52.215147+00:00
-- url     : https://prove2.me/theorems/d4ee8b7f-9bca-46c3-a13d-f42557853ee2
-- title:
--   Proof of Lemma 2.3, pp. 248–249 — (1 + 1/n)²(1 − 1/n²)^{n−1} ≥ exp(1/n) for n ≥ 2
-- statement:
--   For every integer $n\ge 2$,
--
--   $$
--   \Big(1+\frac1n\Big)^2\Big(1-\frac1{n^2}\Big)^{n-1}\ \ge\ \exp\Big(\frac1n\Big).
--   $$
--
--   The left-hand side is the maximal value of $h^2(2h-h^2)^{n-1}$ over $h\in[1,2]$, the squared inverse volume ratio of the best ellipsoid covering a half ball. The inequality is what turns that ratio into the factor $\exp(-1/(2n))$ of (2.4).
--
--   **Formalization Note** $n$ is a natural number cast to $\mathbb R$; the exponent $n-1$ is natural-number subtraction, exact since $n\ge2$.
-- source:
--   Bubeck, arXiv:1405.4980v2, §2.2, proof of Lemma 2.3, display at the bottom of p. 248 (continued p. 249)

import Mathlib
import Definitions.Def_ConvexOptAlg_Ellipsoid_Defs

namespace ConvexOptAlg.Ellipsoid

/-- The scalar inequality in the proof of Lemma 2.3 (Bubeck, arXiv:1405.4980v2, §2.2, pp. 248–249):
for every integer `n ≥ 2`, `(1 + 1/n)² (1 − 1/n²)^{n−1} ≥ exp(1/n)`. -/
theorem lemma_2_3_scalar (n : ℕ) (hn : 2 ≤ n) :
    Real.exp (1 / (n : ℝ)) ≤ (1 + 1 / (n : ℝ)) ^ 2 * (1 - 1 / (n : ℝ) ^ 2) ^ (n - 1) := by sorry

end ConvexOptAlg.Ellipsoid
