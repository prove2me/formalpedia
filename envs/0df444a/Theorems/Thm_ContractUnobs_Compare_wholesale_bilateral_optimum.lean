-- Prove2me | Theorems.Thm_ContractUnobs_Compare_wholesale_bilateral_optimum
-- name    : ContractUnobs.Compare.wholesale_bilateral_optimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:57.179889+00:00
-- url     : https://prove2.me/theorems/4adaa750-78eb-49da-b990-7b9c56a748ba
-- title:
--   §5.2, p. 17 — under unobservable wholesale prices the bilateral optimum is w = (1+θp̃)/(2(1+θ)), with profit (1+θp̃)²/(8(1+θ))
-- statement:
--   Fix $\theta \ge 0$ and a belief $\tilde p \ge 0$ of retailer $i$ about its rival's price, and let $\sigma$ assign to every wholesale-price contract $(0, w)$ with $w \ge 0$ an optimal action of retailer $i$ for that belief (with acceptance on ties). Then the manufacturer's bilateral profit from retailer $i$, $wQ$ if $\sigma(0,w)$ accepts and $0$ otherwise, has maximum
--   $$\max_{w \ge 0} \text{bilateral}\bigl((0,w), \sigma(0,w)\bigr) = \frac{(1 + \theta\tilde p)^2}{8(1+\theta)},$$
--   attained only at the wholesale price
--   $$w = \frac{1 + \theta\tilde p}{2(1+\theta)} .$$
--
--   Since retailer $j$ cannot observe $w_i$, its order does not react to it, and the manufacturer's choice of $w_i$ is a monopoly problem against retailer $i$'s best response alone. This is the bilateral step behind Proposition 2.
--
--   **Formalization Note** The maximum is stated with Mathlib's `IsGreatest` over the image of the wholesale-price class, so it is attained. The page states this in words; the explicit maximizer and value are the ones the bilateral problem yields and are consistent with Proposition 2.
-- source:
--   Li & Liu, Contract Unobservability and Downstream Competition, SSRN 3339702, p. 17, §5.2 ("the manufacturer will cut w_i to boost retailer i's order with no effect on retailer j's order")

import Mathlib
import Definitions.Def_ContractUnobs_Compare_Model

namespace ContractUnobs.Compare

theorem wholesale_bilateral_optimum (θ pt : ℝ) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt)
    (σ : Contract → Action) (hσ : ∀ C ∈ wholesaleClass, RetailerOptimal θ pt C (σ C)) :
    IsGreatest ((fun C => bilateral C (σ C)) '' wholesaleClass)
        ((1 + θ * pt) ^ 2 / (8 * (1 + θ))) ∧
      ∀ C ∈ wholesaleClass, bilateral C (σ C) = (1 + θ * pt) ^ 2 / (8 * (1 + θ)) →
        C = ⟨0, (1 + θ * pt) / (2 * (1 + θ))⟩ := by sorry

end ContractUnobs.Compare
