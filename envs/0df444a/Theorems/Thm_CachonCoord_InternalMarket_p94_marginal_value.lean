-- Prove2me | Theorems.Thm_CachonCoord_InternalMarket_p94_marginal_value
-- name    : CachonCoord.InternalMarket.p94_marginal_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:57:05.679991+00:00
-- url     : https://prove2.me/theorems/945f3044-d838-4bfb-96b3-9a4de085edc4
-- title:
--   §6.9.1, p. 94 — w(α, Q) is the marginal value of production: ∂π(α, Q)/∂Q = w(α, Q)
-- statement:
--   Let $\eta>1$, $\alpha_1,\alpha_2>0$ and $Q>0$. The retailers' revenue under the optimal allocation, $\pi(\alpha,Q)=\pi(\gamma^o(\alpha),\alpha,Q)$, is differentiable in $Q$ with
--   $$
--   \frac{\partial\pi(\alpha,Q)}{\partial Q}=w(\alpha,Q)=\Big(\frac{\eta-1}{\eta}\Big)(\alpha_1^\eta+\alpha_2^\eta)^{1/\eta}Q^{-1/\eta}.
--   $$
--
--   The market price is thus the shadow price of output, which is what the supplier passes on to the production manager in expectation.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.9.1, p. 94, the display ∂π(α, Q)/∂Q = w(α, Q)

import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue

namespace CachonCoord.InternalMarket

/-- §6.9.1, p. 94 (Cachon 2003, 3rd draft): `w(α, Q)` is the marginal value of additional
production, `∂π(α, Q)/∂Q = w(α, Q)`, for `α₁, α₂ > 0`, `η > 1`, `Q > 0`. -/
theorem p94_marginal_value (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hQ : 0 < Q) :
    HasDerivAt (fun Q' => optRevenue η α₁ α₂ Q') (price η α₁ α₂ Q) Q := by sorry

end CachonCoord.InternalMarket
