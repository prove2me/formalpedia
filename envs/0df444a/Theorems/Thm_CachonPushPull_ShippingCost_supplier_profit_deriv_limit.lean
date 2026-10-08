-- Prove2me | Theorems.Thm_CachonPushPull_ShippingCost_supplier_profit_deriv_limit
-- name    : CachonPushPull.ShippingCost.supplier_profit_deriv_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:39:56.307973+00:00
-- url     : https://prove2.me/theorems/82a1e333-ae86-4abf-a6c7-950a1d8f4638
-- title:
--   Proof of Theorem 8 — $\lim_{w_1 \to w_2} d\pi_s/dw_1 = -\tau/((w_2 - v) f(0)) < 0$
-- statement:
--   Fix $v < w_2 \le p$, a shipping cost $\tau > 0$ and a production quantity $q$, and let $y_r(w_1) \ge 0$ with $F(y_r(w_1)) = (w_2 - w_1)/(w_2 - v)$ for $v < w_1 < w_2$. Then:
--
--   1. $y_r(w_1) \to 0$ as $w_1 \to w_2$ from below;
--   2. if the density has a positive right limit at $0$, $f(0) := \lim_{x \to 0^+} f(x) > 0$, then
--   $$
--   \lim_{w_1 \to w_2^-} \frac{d\pi_s(y_r(w_1), q)}{dw_1} = -\frac{\tau}{(w_2 - v) f(0)} < 0 .
--   $$
--
--   Hence the supplier's profit is decreasing in $w_1$ as $w_1$ approaches $w_2$: a small advance-purchase discount raises her profit.
--
--   **Formalization Note** The paper's display presupposes a finite positive $f(0)$, while the model has a density on $(0,\infty)$ only; the hypothesis that $f$ has a positive right limit at $0$ is the reading of "$f(0)$" and applies to part 2 only. The goal theorem does not use it. Only left limits are taken, since an advance-purchase discount has $w_1 < w_2$. The derivative is Mathlib's `deriv`, which is the genuine derivative near $w_2$ because $f(y_r(w_1)) > 0$ there.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 234, proof of Theorem 8 (limit display)

import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

open Filter Topology

/-- The limit display in the proof of Theorem 8, p. 234. Fix `v < w₂ ≤ p`, `τ > 0`, a production
`q` and the retailer's prebook `y_r(w₁) ≥ 0`, `F(y_r(w₁)) = (w₂ - w₁)/(w₂ - v)`, for
`v < w₁ < w₂`. Then `y_r(w₁) → 0` as `w₁ → w₂⁻`. If moreover the density has a positive right
limit `f(0) := lim_{x → 0⁺} f(x) > 0` (the display's hypothesis), then
`lim_{w₁ → w₂⁻} d π_s(y_r(w₁), q)/d w₁ = -τ/((w₂ - v) f(0)) < 0`. -/
theorem supplier_profit_deriv_limit (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₂ : ℝ) (hvw₂ : v < w₂) (hw₂p : w₂ ≤ p) (yr : ℝ → ℝ)
    (hyr : ∀ w : ℝ, w ∈ Set.Ioo v w₂ → 0 ≤ yr w ∧ cdf μ (yr w) = (w₂ - w) / (w₂ - v))
    (q : ℝ) :
    Tendsto yr (𝓝[<] w₂) (𝓝 0) ∧
    ∀ f₀ : ℝ, 0 < f₀ → Tendsto f (𝓝[>] 0) (𝓝 f₀) →
      Tendsto (fun w₁ : ℝ => deriv (fun w : ℝ => supplierProfit μ c v τ w w₂ (yr w) q) w₁)
          (𝓝[<] w₂) (𝓝 (-τ / ((w₂ - v) * f₀))) ∧
        -τ / ((w₂ - v) * f₀) < 0 := by sorry

end CachonPushPull.ShippingCost
