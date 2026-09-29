-- Prove2me | Theorems.Thm_CachonPushPull_ShippingCost_retailer_never_worse
-- name    : CachonPushPull.ShippingCost.retailer_never_worse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:38:10.293269+00:00
-- url     : https://prove2.me/theorems/e49cacd9-5794-4231-a4cc-f76c18eb28c9
-- title:
--   §5.1 — the retailer is never worse off with an advance-purchase discount than with pull
-- statement:
--   Fix an at-once price $w_2 < p$ and a shipping cost $\tau > 0$, and let $w_1 \le w_2$. For every outcome $(y, q)$ of the contract $\{w_1, w_2\}$ and every outcome $(y_0, q_0)$ of the pull contract $\{w_2, w_2\}$,
--   $$
--   \pi_r^{\{w_2, w_2\}}(y_0, q_0) \le \pi_r^{\{w_1, w_2\}}(y, q),
--   $$
--   where the superscript names the contract under which the retailer's profit is computed.
--
--   So an advance-purchase discount ($w_1 < w_2$) can only help the retailer relative to a pull contract with the same at-once price; the question Theorem 8 answers is whether it can also help the supplier.
--
--   **Formalization Note** "Never worse off" is read as: every outcome of the discounted contract is at least as good for the retailer as every outcome of the pull contract.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 234, Section 5.1

import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-- §5.1, p. 234: "The retailer is clearly never worse off with an advance-purchase discount
(`w₁ < w₂`) relative to a pull contract (`w₁ = w₂`) for a fixed `w₂`." For a fixed `w₂ < p`
and any `w₁ ≤ w₂`, the retailer's profit in every outcome of `{w₁, w₂}` is at least his profit in
every outcome of the pull contract `{w₂, w₂}`. -/
theorem retailer_never_worse (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₁ w₂ : ℝ) (hw₁₂ : w₁ ≤ w₂) (hw₂p : w₂ < p) :
    ∀ y q y₀ q₀ : ℝ, IsOutcome μ p c v τ w₁ w₂ y q → IsOutcome μ p c v τ w₂ w₂ y₀ q₀ →
      retailerProfit μ p v w₂ w₂ y₀ q₀ ≤ retailerProfit μ p v w₁ w₂ y q := by sorry

end CachonPushPull.ShippingCost
