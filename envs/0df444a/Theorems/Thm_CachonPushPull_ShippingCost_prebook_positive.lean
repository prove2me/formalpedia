-- Prove2me | Theorems.Thm_CachonPushPull_ShippingCost_prebook_positive
-- name    : CachonPushPull.ShippingCost.prebook_positive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:38:34.505989+00:00
-- url     : https://prove2.me/theorems/821506dd-fd12-419f-9039-dfcfa31c1e0d
-- title:
--   Proof of Theorem 8 — $y_r(w_1) > 0$ for every $w_1 < w_2$
-- statement:
--   Let $v < w_1 < w_2 \le p$. Every $y_r$ with
--   $$
--   F(y_r) = \frac{w_2 - w_1}{w_2 - v}
--   $$
--   (the retailer's optimal prebook of Eq. (22)) satisfies $y_r > 0$.
--
--   This uses the standing assumption $F(0) = 0$: any advance-purchase discount, however small, makes the retailer prebook a positive quantity. Footnote 5 of the paper notes that Theorem 8 depends on this assumption.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 234, proof of Theorem 8

import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 8, p. 234: "From (22), `y_r(w₁) > 0` for all `w₁ < w₂`, where recall
`F(0) = 0` is assumed." For `v < w₁ < w₂`, every `y_r` with `F(y_r) = (w₂ - w₁)/(w₂ - v)` is
strictly positive. -/
theorem prebook_positive (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w₁ w₂ : ℝ) (hvw₁ : v < w₁) (hw₁₂ : w₁ < w₂) (hw₂p : w₂ ≤ p)
    (yr : ℝ) (hyr : cdf μ yr = (w₂ - w₁) / (w₂ - v)) :
    0 < yr := by sorry

end CachonPushPull.ShippingCost
