-- Prove2me | Theorems.Thm_ContractUnobs_Compare_tariff_bilateral_optimum
-- name    : ContractUnobs.Compare.tariff_bilateral_optimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:57.31299+00:00
-- url     : https://prove2.me/theorems/caca8244-c6af-4a2c-a70e-fc3307e23ba2
-- title:
--   §5.1, p. 14 — under unobservable two-part tariffs the manufacturer's bilateral optimum is w = 0, K = (1+θp̃)²/(4(1+θ))
-- statement:
--   Fix $\theta \ge 0$ and a belief $\tilde p \ge 0$ of retailer $i$ about its rival's price, and let $\sigma$ assign to every two-part tariff $(K, w)$ with $w \ge 0$ an optimal action of retailer $i$ for that belief (with acceptance on ties). Then the manufacturer's bilateral profit from retailer $i$, $wQ + K$ if $\sigma(K,w)$ accepts and $0$ otherwise, has maximum
--   $$\max_{(K,w)} \text{bilateral}\bigl((K,w), \sigma(K,w)\bigr) = \frac{(1 + \theta\tilde p)^2}{4(1+\theta)},$$
--   and the only two-part tariff attaining it is
--   $$(K, w) = \Bigl(\frac{(1 + \theta\tilde p)^2}{4(1+\theta)},\ 0\Bigr).$$
--
--   Because the rival retailer does not observe retailer $i$'s contract, its behaviour is unaffected, and the manufacturer optimally sets the marginal wholesale price to zero and extracts retailer $i$'s whole conjectured profit through the fixed fee. This is the bilateral step behind Proposition 1.
--
--   **Formalization Note** The maximum is stated with Mathlib's `IsGreatest` over the image of the tariff class, so it is attained. The statement holds for every optimal strategy $\sigma$, whatever it does at contracts where several actions are optimal.
-- source:
--   Li & Liu, Contract Unobservability and Downstream Competition, SSRN 3339702, p. 14, §5.1 (discussion after Proposition 1: "the manufacturer cannot help but lower wholesale prices to zero")

import Mathlib
import Definitions.Def_ContractUnobs_Compare_Model

namespace ContractUnobs.Compare

theorem tariff_bilateral_optimum (θ pt : ℝ) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt) (σ : Contract → Action)
    (hσ : ∀ C ∈ tariffClass, RetailerOptimal θ pt C (σ C)) :
    IsGreatest ((fun C => bilateral C (σ C)) '' tariffClass)
        ((1 + θ * pt) ^ 2 / (4 * (1 + θ))) ∧
      ∀ C ∈ tariffClass, bilateral C (σ C) = (1 + θ * pt) ^ 2 / (4 * (1 + θ)) →
        C = ⟨(1 + θ * pt) ^ 2 / (4 * (1 + θ)), 0⟩ := by sorry

end ContractUnobs.Compare
