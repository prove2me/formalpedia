-- Prove2me | Theorems.Thm_CachonCoord_Newsvendor_eq_11_retailer
-- name    : CachonCoord.Newsvendor.eq_11_retailer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:08:41.859131+00:00
-- url     : https://prove2.me/theorems/5b422f3f-041f-407b-9e31-261fe8b6457a
-- title:
--   Eq. (11), p. 24 — quantity-flexibility price makes the chain optimum optimal for the retailer
-- statement:
--   For $\delta\in[0,1]$, the wholesale price $w_q(\delta)$ makes the retailer’s derivative at the channel-optimal order $q^o$ vanish. The retailer’s profit is concave, so $q^o$ is a global optimum under forced compliance.
--
--   $$\frac{\partial\pi_r}{\partial q}(q^o,w_q(\delta),\delta)=0,\qquad q^o\in\operatorname*{argmax}_q\pi_r(q,w_q(\delta),\delta).$$
--
--   **Formalization Note** `ContractData` is the local model with $v<c_s+c_r$, and the standing assumption $\Pi(q^o)>0$ is explicit. The theorem uses the explicit $w_q$ formula.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.2.5, Eq. (11) and concavity argument, p. 24

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.5, Eq. (11) and the concavity argument, p. 24:
the wholesale price `w_q(δ)` makes the retailer's first-order condition zero
at the channel optimum, which maximizes the retailer's profit under forced
compliance. -/
theorem eq_11_retailer (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D] (hD : Integrable (fun x => x) D)
    (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (hPi : 0 < chainProfit P D q0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    HasDerivAt (retailerProfit P D
      (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ)) 0 q0 ∧
    IsMaxOn (retailerProfit P D
      (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ)) Set.univ q0 := by sorry

end CachonCoord.Newsvendor
