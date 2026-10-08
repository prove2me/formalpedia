-- Prove2me | Theorems.Thm_CachonPushPull_Pareto_optimal_quantity_prices
-- name    : CachonPushPull.Pareto.optimal_quantity_prices
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:24:37.744763+00:00
-- url     : https://prove2.me/theorems/04889b81-b811-4f60-9e16-cf6d030982c3
-- title:
--   Eqs. (3), (7): the prices $\hat w_1(q)$ and $w_1(q)$ induce the quantity $q$ and are one-to-one in $q$
-- statement:
--   Let demand satisfy the standing assumptions and $v < c < p$. Put $\hat w_1(q) = p - (p - v)F(q)$ and $w_1(q) = \dfrac{c - vF(q)}{1 - F(q)}$. Then
--
--   1. $\hat w_1$ is strictly decreasing and $w_1$ is strictly increasing on $[0, \infty)$;
--   2. for every $q \ge 0$, $q$ is the unique maximizer over $y \ge 0$ of the push retailer's profit at price $\hat w_1(q)$:
--   $$
--   \hat\pi_r(y, \hat w_1(q)) < \hat\pi_r(q, \hat w_1(q)) \quad \text{for all } y \ge 0,\ y \ne q ;
--   $$
--   3. for every $q \ge 0$, $q$ is the unique maximizer over $y \ge 0$ of the pull supplier's profit at price $w_1(q)$:
--   $$
--   \pi_s(y, w_1(q)) < \pi_s(q, w_1(q)) \quad \text{for all } y \ge 0,\ y \ne q .
--   $$
--
--   This justifies describing push and pull contracts by the quantity $q$ they induce rather than by the wholesale price.
--
--   **Formalization Note** The paper states the first-order conditions $F(q) = (p - \hat w_1)/(p - v)$ and $F(q) = (w_1 - c)/(w_1 - v)$; the formal statement asserts what they are used for, that the induced quantity is the unique optimum at the corresponding price.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 227, Eq. (3) and Eqs. (7)-(8)

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Eqs. (3) and (7), p. 227: the wholesale prices `ŵ₁(q)` and `w₁(q)` induce the quantity `q`,
and each is one-to-one in `q`. -/
theorem optimal_quantity_prices (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    StrictAntiOn (pushPrice μ p v) (Set.Ici 0) ∧
    StrictMonoOn (pullPrice μ c v) (Set.Ici 0) ∧
    ∀ q : ℝ, 0 ≤ q →
      (∀ y : ℝ, 0 ≤ y → y ≠ q →
        pushRetailerProfitAt μ p v (pushPrice μ p v q) y <
          pushRetailerProfitAt μ p v (pushPrice μ p v q) q) ∧
      (∀ y : ℝ, 0 ≤ y → y ≠ q →
        pullSupplierProfitAt μ c v (pullPrice μ c v q) y <
          pullSupplierProfitAt μ c v (pullPrice μ c v q) q) := by sorry

end CachonPushPull.Pareto
