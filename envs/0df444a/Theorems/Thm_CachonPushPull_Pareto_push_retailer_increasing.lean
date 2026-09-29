-- Prove2me | Theorems.Thm_CachonPushPull_Pareto_push_retailer_increasing
-- name    : CachonPushPull.Pareto.push_retailer_increasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:25:51.016991+00:00
-- url     : https://prove2.me/theorems/a01a6e6d-26d4-4648-acb2-29bb13b4daee
-- title:
--   Eq. (5): the push retailer's profit is increasing, $\hat\pi_r'(q) = (p-v)f(q)q$
-- statement:
--   Let demand satisfy the standing assumptions and $v < c < p$. The retailer's profit with a push contract, $\hat\pi_r(q)$, satisfies
--   $$
--   \hat\pi_r'(q) = (p - v) f(q)\, q \quad \text{for every } q > 0,
--   $$
--   and $\hat\pi_r$ is strictly increasing on $[0, \infty)$.
--
--   With push, the retailer always wants a larger quantity; this drives the push Pareto set $[\hat q^*, q^o]$.
--
--   **Formalization Note** The paper writes "increasing" with the derivative $\ge 0$; the strictly increasing reading is true because $F$ is strictly increasing.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 227, Eq. (5)

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Eq. (5), p. 227: the push retailer's profit is increasing in `q`, with
`π̂_r'(q) = (p - v) f(q) q`. -/
theorem push_retailer_increasing (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    (∀ q : ℝ, 0 < q → HasDerivAt (pushRetailerProfit μ p v) ((p - v) * f q * q) q) ∧
    StrictMonoOn (pushRetailerProfit μ p v) (Set.Ici 0) := by sorry

end CachonPushPull.Pareto
