-- Prove2me | Theorems.Thm_CachonPushPull_ShippingCost_apd_pareto_improves_pull
-- name    : CachonPushPull.ShippingCost.apd_pareto_improves_pull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:40:29.554447+00:00
-- url     : https://prove2.me/theorems/02eaa906-0c0a-400b-9a56-97f827f7f42c
-- title:
--   Theorem 8 — with at-once shipping costs, an advance-purchase discount Pareto-improves a pull contract
-- statement:
--   Consider the model of §3 with $v < c < p$, in which the supplier pays a shipping and handling cost $\tau > 0$ on every unit of an at-once order (§5.1). Fix the at-once price $w_2 < p$ and suppose the retailer does not prebook under the pull contract $\{w_2, w_2\}$: prebooking nothing is his unique best reply, and the supplier then produces a best response $q_0$ to the prebook $0$.
--
--   Then there is an advance-purchase discount $w_1$ with
--   $$
--   c < w_1 < w_2
--   $$
--   such that the contract $\{w_1, w_2\}$ has an outcome, and every outcome $(y, q)$ of $\{w_1, w_2\}$ is a strict Pareto improvement on the pull outcome:
--   $$
--   \pi_r^{\{w_2,w_2\}}(0, q_0) < \pi_r^{\{w_1,w_2\}}(y, q), \qquad \pi_s^{\{w_2,w_2\}}(0, q_0) < \pi_s^{\{w_1,w_2\}}(y, q),
--   $$
--   for every supplier best response $q_0$ to the prebook $0$ under $\{w_2, w_2\}$.
--
--   So once at-once orders are costly to ship, a pull contract is never in the Pareto set: the supplier can offer a small discount that induces the retailer to take some inventory in advance, saving the shipping cost on it, and both firms gain.
--
--   **Formalization Note** "The retailer does not prebook when $w_1 = w_2$" is read as "$y = 0$ is the retailer's unique best reply" (predicate `PullNoPrebook`); with a tie the conclusion can fail, and this strict reading is the proof's "$w_2$ is sufficiently high". "Profit increases for both" is read as strict increase for both firms, in every outcome of the discounted contract, so no favourable tie-breaking is assumed. The conclusion $c < w_1$ is a strengthening of "advance-purchase discount" ($w_1 < w_2$), which follows from the premise. No positivity of the density at $0$ is assumed. The IGFR assumption is part of the model but is not needed.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 234, Theorem 8

import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-- Theorem 8, p. 234. Let the supplier incur a shipping and handling cost `τ > 0` per at-once
unit (§5.1), and fix the at-once price `w₂ < p`. If the retailer does not prebook under the pull
contract `{w₂, w₂}` (`y = 0` is his unique best reply, `PullNoPrebook`), then there is an
advance-purchase discount `c < w₁ < w₂` such that `{w₁, w₂}` has an outcome, and every outcome
`(y, q)` of `{w₁, w₂}` gives both the retailer and the supplier strictly more profit than the
pull outcome `(0, q₀)`, for every supplier best response `q₀` to the prebook `0` under
`{w₂, w₂}`. -/
theorem apd_pareto_improves_pull (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₂ : ℝ) (hw₂p : w₂ < p)
    (hpull : PullNoPrebook μ p c v τ w₂) :
    ∃ w₁ : ℝ, c < w₁ ∧ w₁ < w₂ ∧
      (∃ y q : ℝ, IsOutcome μ p c v τ w₁ w₂ y q) ∧
      ∀ y q : ℝ, IsOutcome μ p c v τ w₁ w₂ y q →
        ∀ q₀ : ℝ, IsSupplierBestResponse μ c v τ w₂ w₂ 0 q₀ →
          retailerProfit μ p v w₂ w₂ 0 q₀ < retailerProfit μ p v w₁ w₂ y q ∧
          supplierProfit μ c v τ w₂ w₂ 0 q₀ < supplierProfit μ c v τ w₁ w₂ y q := by sorry

end CachonPushPull.ShippingCost
