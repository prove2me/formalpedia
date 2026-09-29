-- Prove2me | Theorems.Thm_CachonPushPull_ShippingCost_retailer_prebook_argmax
-- name    : CachonPushPull.ShippingCost.retailer_prebook_argmax
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:37:07.936194+00:00
-- url     : https://prove2.me/theorems/b29f9c76-c104-4ac1-9e39-06c4806434e7
-- title:
--   Eq. (22) — the retailer's optimal prebook $y_r$, $F(y_r) = (w_2 - w_1)/(w_2 - v)$
-- statement:
--   Consider a contract $\{w_1, w_2\}$ with $v < w_1 \le w_2 \le p$, and let $F$ be the demand distribution function of the model. Fix any production quantity $q$. Then the retailer's profit $y \mapsto \pi_r(y, q)$ is concave on $y \ge 0$, there is a prebook $y_r \ge 0$ with
--   $$
--   F(y_r) = \frac{w_2 - w_1}{w_2 - v},
--   $$
--   and every such $y_r$ is the unique maximizer of $\pi_r(\cdot, q)$ over $y \ge 0$: $\pi_r(y, q) < \pi_r(y_r, q)$ for every $y \ge 0$, $y \ne y_r$.
--
--   Since $y_r$ does not depend on $q$, the retailer's optimal prebook is independent of the supplier's production whenever he prebooks less than she produces. The shipping cost does not enter the retailer's profit, so this equation is the same with and without it.
--
--   **Formalization Note** The paper writes "$\pi_r(y,q)$ is concave in $y$, so let $y_r = \arg\max \pi_r(y,q)$"; the statement asserts concavity, existence of $y_r$ and that it is the unique maximizer. The paper's contracts have $c \le w_1$; the weaker hypothesis $v < w_1$ suffices.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 233, Section 4.5, Eq. (22)

import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-- Eq. (22), p. 233: under a contract with `v < w₁ ≤ w₂ ≤ p` and any fixed production `q`, the
retailer's profit `π_r(y, q)` is concave in the prebook `y ≥ 0`, a prebook `y_r ≥ 0` with
`F(y_r) = (w₂ - w₁)/(w₂ - v)` exists, and every such `y_r` is the unique maximizer of
`y ↦ π_r(y, q)` over `y ≥ 0`; in particular `y_r` does not depend on `q`. -/
theorem retailer_prebook_argmax (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w₁ w₂ : ℝ) (hvw₁ : v < w₁) (hw₁₂ : w₁ ≤ w₂) (hw₂p : w₂ ≤ p) (q : ℝ) :
    ConcaveOn ℝ (Set.Ici 0) (fun y : ℝ => retailerProfit μ p v w₁ w₂ y q) ∧
    (∃ yr : ℝ, 0 ≤ yr ∧ cdf μ yr = (w₂ - w₁) / (w₂ - v)) ∧
    ∀ yr : ℝ, 0 ≤ yr → cdf μ yr = (w₂ - w₁) / (w₂ - v) →
      ∀ y : ℝ, 0 ≤ y → y ≠ yr →
        retailerProfit μ p v w₁ w₂ y q < retailerProfit μ p v w₁ w₂ yr q := by sorry

end CachonPushPull.ShippingCost
