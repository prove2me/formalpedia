-- Prove2me | Theorems.Thm_CachonCoord_Newsvendor_p25_delta_one
-- name    : CachonCoord.Newsvendor.p25_delta_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:08:42.778733+00:00
-- url     : https://prove2.me/theorems/34e446ba-9018-469a-95f6-7cde85adfd87
-- title:
--   §6.2.5, p. 25 — at δ = 1 the supplier earns π_s(q°, w_q(1), 1) = Π(q°) + μg_r ≥ Π(q°)
-- statement:
--   Let $q^o$ maximize the supply chain profit $\Pi$. Under the quantity flexibility contract with $\delta = 1$ (full flexibility) and wholesale price $w_q(1)$, the supplier's profit at $q^o$ is
--   $$\pi_s(q^o, w_q(1), 1) = g_s S(q^o) + (p + g_r - c)q^o - (p + g_r - v)\int_0^{q^o} F(y)\,dy - \mu g_s = \Pi(q^o) + \mu g_r \ge \Pi(q^o).$$
--
--   This is the other end of the allocation range: at $\delta = 1$ the supplier captures at least the whole supply chain profit.
--
--   **Formalization Note** The local `ContractData` has Cachon’s assumptions $v<c_s+c_r$, $c_s+c_r<p$, and nonnegative goodwill costs. It permits negative net salvage and $v\ge c_r$. Demand is a probability law on $[0,\infty)$ with finite mean and a continuous cdf strictly increasing until it reaches one. These are the chapter’s standing assumptions; $\Pi(q^o)>0$ is included wherever a chain optimum is named. Cachon’s differentiable cdf is represented on the interior of its active support by `hFderiv`; derivative claims use `HasDerivAt`. The page's integral has upper limit $q$; it is $q^o$ (printed slip), and the Lean states it at $q^o$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.2.5, p. 25 (the δ = 1 display)

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.5, p. 25 (δ = 1): with the quantity flexibility contract `(w_q(1), 1)` the
supplier's profit at `q°` is `g_sS(q°) + (p + g_r − c)q° − (p + g_r − v)∫_0^{q°} F(y)dy − μg_s
= Π(q°) + μg_r ≥ Π(q°)`. -/
theorem p25_delta_one (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (hPi : 0 < chainProfit P D q0) :
    supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 =
        P.ps * expSales D q0 + (P.r + P.pr - P.c) * q0
          - (P.r + P.pr - P.v) * (∫ y in (0 : ℝ)..q0, cdf D y) - meanDemand D * P.ps ∧
      supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 =
        chainProfit P D q0 + meanDemand D * P.pr ∧
      chainProfit P D q0 ≤
        supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 := by sorry

end CachonCoord.Newsvendor
