-- Prove2me | Theorems.Thm_AgencyPassThrough_Pricing_slope_fact
-- name    : AgencyPassThrough.Pricing.slope_fact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:28.254187+00:00
-- url     : https://prove2.me/theorems/4d0148e6-9902-45df-be80-dac58c2a5b94
-- title:
--   Proof of Proposition 2(i) — net-price curve is strictly increasing
-- statement:
--   For a demand satisfying A1, A3, and A4 on an open price interval $D$, and for $0\leq\theta\leq1$, the net-price curve
--
--   $$p\longmapsto p-\lambda(p)-\theta\lambda(p)[1-\lambda'(p)]$$
--
--   is strictly increasing on $D$. This is the slope fact used to compare wholesale and agency equilibrium prices.
--
--   **Formalization Note** Strict increase is asserted only on the price domain where the demand assumptions and derivatives hold.
-- source:
--   Hu, Zheng & Pan, Agency or Wholesale? The Role of Retail Pass-Through, SSRN preprint 3724934 (2021 revision, PDF sha256 1ab91ed8…), p. 26, proof of Proposition 2(i), slope claim following Eq. (6)

import Mathlib
import Definitions.Def_AgencyPassThrough_Pricing_Model

namespace AgencyPassThrough.Pricing

/-- Strictly increasing net-price curve from A3; proof of Proposition 2(i), p. 26. -/
theorem slope_fact (q : ℝ → ℝ) (D : Set ℝ) (hq : DemandStanding q D)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    StrictMonoOn (fun p => p - lam q p - θ * lam q p * (1 - deriv (lam q) p)) D := by sorry

end AgencyPassThrough.Pricing
