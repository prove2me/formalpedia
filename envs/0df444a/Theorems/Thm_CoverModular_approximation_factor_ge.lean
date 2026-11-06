-- Prove2me | Theorems.Thm_CoverModular_approximation_factor_ge
-- name    : CoverModular.approximation_factor_ge
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:32.884974+00:00
-- url     : https://prove2.me/theorems/f65a7923-a51b-4ba4-ba3a-795589133d74
-- title:
--   Proposition 2 — the numerical bound $\frac{1-(1-2/K)^K}{2}\ge\frac{1-e^{-2}}{2}$
-- statement:
--   For every positive integer $K$,
--
--   $$
--   \frac{1-\bigl(1-\frac2K\bigr)^K}{2}\ge\frac{1-e^{-2}}{2}\approx0.432 .
--   $$
--
--   This is the second inequality of the display of Proposition 2: the approximation factor of Algorithm 1 is bounded below by a constant independent of the budget $K$. At $K=1$ the left side is $1$, at $K=2$ it is $1/2$.
--
--   **Formalization Note** The gloss $\approx0.432$ is not part of the formal statement.
--
--   Differences from the source: none.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.2, Proposition 2, p.15, and the last display of its proof, p.16

import Mathlib

namespace CoverModular

/-- **The numerical bound of Proposition 2** (DeValve, Pekeč, Wei, SSRN 3844987, §3.2,
Proposition 2, p.15, and the last display of its proof, p.16): for every positive integer `K`,
`(1 − (1 − 2/K)^K)/2 ≥ (1 − e^{−2})/2`.

**Formalization Note** `2/K` is real division; `K ≥ 1` (at `K = 1` the base is `−1`). -/
theorem approximation_factor_ge (K : ℕ) (hK : 1 ≤ K) :
    (1 - Real.exp (-2)) / 2 ≤ (1 - (1 - 2 / (K : ℝ)) ^ K) / 2 := by sorry

end CoverModular
