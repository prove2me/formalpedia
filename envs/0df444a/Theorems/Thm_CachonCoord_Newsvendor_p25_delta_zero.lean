-- Prove2me | Theorems.Thm_CachonCoord_Newsvendor_p25_delta_zero
-- name    : CachonCoord.Newsvendor.p25_delta_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:08:53.531674+00:00
-- url     : https://prove2.me/theorems/7381f451-d6bb-429c-b77c-271e9bd88ff5
-- title:
--   §6.2.5, p. 25 — at δ = 0 the retailer earns π_r(q°, w_q(0), 0) = Π(q°) + g_s(μ − S(q°) + F̄(q°)q°) ≥ Π(q°)
-- statement:
--   Let $q^o$ maximize the supply chain profit $\Pi$. Under the quantity flexibility contract with $\delta = 0$ (no flexibility) and wholesale price $w_q(0)$, the retailer's profit at $q^o$ is
--   $$\pi_r(q^o, w_q(0), 0) = (p - v + g_r)S(q^o) - \frac{p - v + g_r}{p - v + g}(c - v)\,q^o - \mu g_r = \Pi(q^o) + g_s\big(\mu - S(q^o) + \bar F(q^o)q^o\big) \ge \Pi(q^o).$$
--
--   This is one end of the allocation range of the quantity flexibility contract: at $\delta = 0$ the retailer captures at least the whole supply chain profit.
--
--   **Formalization Note** The local `ContractData` has Cachon’s assumptions $v<c_s+c_r$, $c_s+c_r<p$, and nonnegative goodwill costs. It permits negative net salvage and $v\ge c_r$. Demand is a probability law on $[0,\infty)$ with finite mean and a continuous cdf strictly increasing until it reaches one. These are the chapter’s standing assumptions; $\Pi(q^o)>0$ is included wherever a chain optimum is named. Cachon’s differentiable cdf is represented on the interior of its active support by `hFderiv`; derivative claims use `HasDerivAt`. The page writes $S(q)$ in the first line; the quantity is $q^o$ throughout (printed slip), and the Lean states it at $q^o$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.2.5, p. 25 (the δ = 0 display)

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.5, p. 25 (δ = 0): with the quantity flexibility contract `(w_q(0), 0)` the
retailer's profit at `q°` is `(p − v + g_r)S(q°) − ((p − v + g_r)/(p − v + g))(c − v)q° − μg_r
= Π(q°) + g_s(μ − S(q°) + F̄(q°)q°) ≥ Π(q°)`. -/
theorem p25_delta_zero (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (hPi : 0 < chainProfit P D q0) :
    retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 =
        (P.r - P.v + P.pr) * expSales D q0
          - (P.r - P.v + P.pr) / (P.r - P.v + P.p) * (P.c - P.v) * q0 - meanDemand D * P.pr ∧
      retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 =
        chainProfit P D q0 + P.ps * (meanDemand D - expSales D q0 + (1 - cdf D q0) * q0) ∧
      chainProfit P D q0 ≤
        retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 := by sorry

end CachonCoord.Newsvendor
