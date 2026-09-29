-- Prove2me | Theorems.Thm_BellmanTheoryDP_GoldMining_optimal_return_functional_equation
-- name    : BellmanTheoryDP.GoldMining.optimal_return_functional_equation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T09:50:10.001286+00:00
-- url     : https://prove2.me/theorems/ace4bf03-21e0-4dc5-a513-fd3219a2eab1
-- title:
--   Eq. (8.2) — the gold-mining functional equation
-- statement:
--   In Bellman's gold-mining problem, let $0 < p, q, r, s < 1$ be the success probabilities and mined fractions of Anaconda and Bonanza, and let $f(x, y)$ be the optimal return from amounts $x \ge 0$ in Anaconda and $y \ge 0$ in Bonanza (the supremum of the expected gold mined over all choice sequences). Then
--   $$f(x, y) = \max\Big\{\, p\,\big[r x + f((1-r)x,\ y)\big],\ \ q\,\big[s y + f(x,\ (1-s)y)\big] \,\Big\}.$$
--   The first branch is the value of using Anaconda first and continuing optimally, the second that of using Bonanza first.
--
--   This is the principle of optimality applied to Problem 2, and the instance for this process of the paper's general stochastic functional equation (5.1). It reduces the optimization over infinite sequences to a one-step comparison.
--
--   **Formalization Note** The paper leaves the ranges of the parameters implicit; the statement takes $0 < p, q, r, s < 1$ and $x, y \ge 0$. The function $f$ is the supremum over all choice sequences (`optimalReturn`), not a solution of the equation, so the equation has content.
-- source:
--   Bellman, The theory of dynamic programming, Bull. Amer. Math. Soc. 60 (1954), p. 508, Eq. (8.2)

import Mathlib
import Definitions.Def_BellmanTheoryDP_GoldMining_Model

namespace BellmanTheoryDP.GoldMining

/-- Bellman (1954), Eq. (8.2): the optimal return `f(x, y)` of the two-mine problem satisfies
`f(x, y) = max (p [r x + f((1-r) x, y)]) (q [s y + f(x, (1-s) y)])`. -/
theorem optimal_return_functional_equation (p q r s x y : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    optimalReturn p q r s x y =
      max (p * (r * x + optimalReturn p q r s ((1 - r) * x) y))
          (q * (s * y + optimalReturn p q r s x ((1 - s) * y))) := by sorry

end BellmanTheoryDP.GoldMining
