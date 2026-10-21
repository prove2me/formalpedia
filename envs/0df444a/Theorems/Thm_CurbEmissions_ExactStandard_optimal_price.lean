-- Prove2me | Theorems.Thm_CurbEmissions_ExactStandard_optimal_price
-- name    : CurbEmissions.ExactStandard.optimal_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:12.456429+00:00
-- url     : https://prove2.me/theorems/c46bcc27-c761-4056-b366-2cc84fb46724
-- title:
--   §3.1, p. 12 — the firm's optimal price is p∗ = [(c + γ)e + ū]/2
-- statement:
--   Let the standing assumptions of the model hold, and consider a product of efficiency level $e\ge0$ sold in a market of size $m>0$ whose consumers' valuations are uniform on $[0,\bar u]$. The firm's operating profit at price $p$ is $(p-ce)\,m\,\big(1-\frac{p-\gamma e}{\bar u}\big)$, with the buying share clipped to $[0,1]$. Then the price
--   $$p^*=\frac{(c+\gamma)e+\bar u}{2}$$
--   maximizes this profit over all $p\in\mathbb R$. Moreover, whenever the margin $\bar u-(c-\gamma)e$ is positive, $p^*$ is the unique maximizer.
--
--   This justifies evaluating the firm's profits, the sales volumes and the consumer utilities of the base model at $p^*$.
--
--   **Formalization Note** When $\bar u-(c-\gamma)e\le 0$ nobody buys at any price that covers cost, every price with zero share is optimal, and only the optimality of $p^*$ is asserted.
-- source:
--   Han, Hu & Dawande, Curbing Emissions: Environmental Regulations and Product Offerings Across Markets, MSOM (authors' accepted manuscript, 2022-07-28), p. 12, §3.1 (unnumbered claim following eq. (1))

import Mathlib
import Definitions.Def_CurbEmissions_ExactStandard_Model

namespace CurbEmissions.ExactStandard

/-- §3.1, p. 12: for every efficiency level `e ≥ 0` and market size `m > 0`, the price
`p∗ = [(c + γ)e + ū]/2` maximizes the firm's operating profit, and it is the unique maximizer while the
margin `ū − (c − γ)e` is positive. -/
theorem optimal_price (P : Params) (hP : Standing P) (e m : ℝ) (he : 0 ≤ e) (hm : 0 < m) :
    (∀ p, priceObj P e m p ≤ priceObj P e m (pStar P e)) ∧
    ((P.c - P.gam) * e < P.ubar →
      ∀ p, p ≠ pStar P e → priceObj P e m p < priceObj P e m (pStar P e)) := by sorry

end CurbEmissions.ExactStandard
