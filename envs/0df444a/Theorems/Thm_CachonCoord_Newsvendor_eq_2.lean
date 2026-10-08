-- Prove2me | Theorems.Thm_CachonCoord_Newsvendor_eq_2
-- name    : CachonCoord.Newsvendor.eq_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:08:31.627754+00:00
-- url     : https://prove2.me/theorems/bb08d16b-86b5-4160-b816-6c0fbb1b2eaa
-- title:
--   Eq. (2), p. 11 — the unique chain optimum satisfies the critical fractile
-- statement:
--   For the chain-optimal order $q^o$, Eq. (2) identifies the critical fractile and the strict increase of $F$ makes that optimum unique.
--
--   $$1-F(q^o)=\frac{c-v}{p-v+g_s+g_r}.$$
--
--   **Formalization Note** The local data use $v<c_s+c_r$ as on p. 7, and the standing assumption $\Pi(q^o)>0$ is explicit. The demand law has finite mean and continuous cdf, strictly increasing before it reaches one.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.2.1, Eq. (2), p. 11

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.1, Eq. (2), p. 11: the unique channel-optimal order
quantity has critical fractile `F̄(q°) = (c − v)/(p − v + g)`. -/
theorem eq_2 (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D] (hD : Integrable (fun x => x) D)
    (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (hPi : 0 < chainProfit P D q0) :
    1 - cdf D q0 = (P.c - P.v) / (P.r - P.v + P.p) ∧
      ∀ q : ℝ, IsMaxOn (chainProfit P D) Set.univ q → q = q0 := by sorry

end CachonCoord.Newsvendor
