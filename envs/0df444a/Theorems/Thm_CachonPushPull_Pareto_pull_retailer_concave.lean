-- Prove2me | Theorems.Thm_CachonPushPull_Pareto_pull_retailer_concave
-- name    : CachonPushPull.Pareto.pull_retailer_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:27:54.437878+00:00
-- url     : https://prove2.me/theorems/bbb3ed88-d65e-44df-8d60-dfdb66d0e4f0
-- title:
--   Theorem 2: the retailer's profit with a pull contract, $\pi_r(q)$, is concave
-- statement:
--   Let demand satisfy the standing assumptions and $v < c < p$. The retailer's profit with a pull contract,
--   $$
--   \pi_r(q) = \big(p - w_1(q)\big) S(q), \qquad w_1(q) = \frac{c - vF(q)}{1 - F(q)},
--   $$
--   is strictly concave on $[0, \infty)$.
--
--   Together with $\pi_r(0) = 0$ this makes the retailer's preferred pull contract $q^* = \arg\max \pi_r$ unique and gives the pull Pareto set $[q^*, q^o]$.
--
--   **Formalization Note** The paper states "concave"; its proof shows that $\pi_r'$ is strictly decreasing (via Lemma 1), so strict concavity is stated.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 228, Theorem 2

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Theorem 2, p. 228: the retailer's profit with a pull contract, `π_r(q)`, is concave
in `q` (strictly, as the proof establishes). -/
theorem pull_retailer_concave (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    StrictConcaveOn ℝ (Set.Ici 0) (pullRetailerProfit μ p c v) := by sorry

end CachonPushPull.Pareto
