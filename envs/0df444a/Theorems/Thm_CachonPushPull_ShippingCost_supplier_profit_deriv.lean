-- Prove2me | Theorems.Thm_CachonPushPull_ShippingCost_supplier_profit_deriv
-- name    : CachonPushPull.ShippingCost.supplier_profit_deriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:39:06.996995+00:00
-- url     : https://prove2.me/theorems/6160eba6-3f38-422f-abe7-5ce512234c40
-- title:
--   Proof of Theorem 8 — the derivative $d\pi_s(y_r(w_1), q)/dw_1$
-- statement:
--   Fix $w_2 \le p$, a shipping cost $\tau > 0$ and a production quantity $q$. For $v < w_1 < w_2$ let $y_r(w_1) \ge 0$ be the retailer's prebook of Eq. (22), $F(y_r(w_1)) = (w_2 - w_1)/(w_2 - v)$. At a point $w_1 \in (v, w_2)$ where the density is positive at the prebook, $f(y_r(w_1)) > 0$:
--
--   1. $y_r$ is differentiable at $w_1$ with $\dfrac{\partial y_r(w_1)}{\partial w_1} = -\bigl[(w_2 - v) f(y_r(w_1))\bigr]^{-1}$;
--   2. the supplier's profit along the retailer's prebook is differentiable at $w_1$ with
--   $$
--   \frac{d\pi_s(y_r(w_1), q)}{dw_1} = y_r(w_1) - \frac{(w_1 - v) - (w_2 - \tau - v)\bigl(1 - F(y_r(w_1))\bigr)}{(w_2 - v)\, f(y_r(w_1))}.
--   $$
--
--   This display is how the proof of Theorem 8 measures the supplier's gain from deepening the discount.
--
--   **Formalization Note** The positivity $f(y_r(w_1)) > 0$ is the hypothesis of the paper's implicit-function step, stated here explicitly; the model only gives a density on $(0, \infty)$. The prebook is a function $y_r$ pinned on $(v, w_2)$ by the equation of (22), which determines it uniquely because $F$ is strictly increasing on $[0, \infty)$.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 234, proof of Theorem 8 (derivative display)

import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-- The derivative display in the proof of Theorem 8, p. 234. Fix `w₂ ≤ p`, a production `q` and
the retailer's prebook `y_r(w₁) ≥ 0`, `F(y_r(w₁)) = (w₂ - w₁)/(w₂ - v)` (Eq. (22)), for
`v < w₁ < w₂`. At a point `w₁` of that interval where the density at `y_r(w₁)` is positive
(the hypothesis of the implicit function step), `y_r` is differentiable with
`y_r'(w₁) = -[(w₂ - v) f(y_r(w₁))]⁻¹`, and
`d π_s(y_r(w₁), q)/d w₁ = y_r(w₁) - [(w₁ - v) - (w₂ - τ - v)(1 - F(y_r(w₁)))]/((w₂ - v) f(y_r(w₁)))`. -/
theorem supplier_profit_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₂ : ℝ) (hw₂p : w₂ ≤ p) (yr : ℝ → ℝ)
    (hyr : ∀ w : ℝ, w ∈ Set.Ioo v w₂ → 0 ≤ yr w ∧ cdf μ (yr w) = (w₂ - w) / (w₂ - v))
    (q w₁ : ℝ) (hw₁ : w₁ ∈ Set.Ioo v w₂) (hf : 0 < f (yr w₁)) :
    HasDerivAt yr (-((w₂ - v) * f (yr w₁))⁻¹) w₁ ∧
    HasDerivAt (fun w : ℝ => supplierProfit μ c v τ w w₂ (yr w) q)
      (yr w₁ - ((w₁ - v) - (w₂ - τ - v) * (1 - cdf μ (yr w₁))) / ((w₂ - v) * f (yr w₁)))
      w₁ := by sorry

end CachonPushPull.ShippingCost
