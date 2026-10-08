-- Prove2me | Theorems.Thm_BoundedNV_Pooling_eq63_standardized_cost
-- name    : BoundedNV.Pooling.eq63_standardized_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:10.696989+00:00
-- url     : https://prove2.me/theorems/0ddc93b3-da0b-401c-81a4-4568b31caffd
-- title:
--   Eq. (63), p. 587 — standardization of Gaussian newsvendor cost
-- statement:
--   Let demand have normal law $N(\mu,\sigma^2)$ with $\sigma>0$. For positive holding and backlog costs $h,b$, write $p=h+b$, $c=h$, and let $\Pi$ be the canonical standard-normal profit. The expected cost $\gamma$ of stocking $\mu+\sigma z$ satisfies
--
--   $$
--   \gamma(\mu+\sigma z)=-\sigma\Pi(z).
--   $$
--
--   This identity transfers each location's cost function to the same canonical scale used in Proposition 7.
--
--   **Formalization Note** The paper prints the standardized profit $\widetilde\pi(z)=\sigma\Pi(z)+b\mu$; the cost identity follows from $\gamma(x)=b\mu-\pi(x)$. The Gaussian cost comes from the published `InventoryControl_newsboy` definition.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 587 (PDF 22), proof of Proposition 7, eq. (63); eqs. (29)–(30), p. 584 (PDF 19)

import Mathlib
import Definitions.Def_BoundedNV_Pooling_Canonical

namespace BoundedNV.Pooling

/-- Equation (63), equivalently in cost form after subtracting the constant `b μ` from profit. -/
theorem eq63_standardized_cost (h b μ σ z : ℝ)
    (hh : 0 < h) (hb : 0 < b) (hσ : 0 < σ) :
    InventoryControl.newsboyCost h b μ σ (μ + σ * z) =
      -(σ * canonProfit (h + b) h z) := by sorry

end BoundedNV.Pooling
