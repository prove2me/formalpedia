-- Prove2me | Theorems.Thm_CachonCoord_Newsvendor_p25_supplier_foc
-- name    : CachonCoord.Newsvendor.p25_supplier_foc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:08:40.107661+00:00
-- url     : https://prove2.me/theorems/af44ddef-7996-4cda-b914-71d8a18b2fec
-- title:
--   §6.2.5, p. 25 — the supplier's first-order condition holds at q° under (w_q(δ), δ): ∂π_s/∂q = g_s(1 − F(q°)) − c + v + (p − v + g_r)(1 − F(q°)) = 0
-- statement:
--   Let $q^o$ maximize the supply chain profit and let $0 \le \delta \le 1$. Under the quantity flexibility contract $(w_q(\delta), \delta)$ the supplier's profit is
--   $$\pi_s(q, w_q(\delta), \delta) = g_s S(q) + (w_q(\delta) - c_s)q - (w_q(\delta) + c_r - v)\int_{(1-\delta)q}^q F(y)\,dy - \mu g_s .$$
--   It is differentiable at $q^o$, and
--   $$\frac{\partial \pi_s(q^o, w_q(\delta), \delta)}{\partial q} = g_s(1 - F(q^o)) - c + v + (p - v + g_r)(1 - F(q^o)) = 0 .$$
--
--   So the supplier, too, has a stationary point at the chain-optimal quantity; Cachon goes on to show that the second-order condition can fail, so coordination needs forced compliance.
--
--   **Formalization Note** The local `ContractData` has Cachon’s assumptions $v<c_s+c_r$, $c_s+c_r<p$, and nonnegative goodwill costs. It permits negative net salvage and $v\ge c_r$. Demand is a probability law on $[0,\infty)$ with finite mean and a continuous cdf strictly increasing until it reaches one. These are the chapter’s standing assumptions; $\Pi(q^o)>0$ is included wherever a chain optimum is named. Cachon’s differentiable cdf is represented on the interior of its active support by `hFderiv`; derivative claims use `HasDerivAt`. The supplier's profit is the local `supplierProfit` with the transfer `quantityFlexTransfer` at the price `quantityFlexPrice`. The derivative is stated as a `HasDerivAt` fact; it needs only continuity of $F$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.2.5, p. 25 (first display)

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.5, p. 25: under the quantity flexibility contract `(w_q(δ), δ)` the
supplier's profit `π_s(q, w_q(δ), δ)` is differentiable at the chain-optimal `q°` with derivative
`g_s(1 − F(q°)) − c + v + (p − v + g_r)(1 − F(q°))`, and this derivative is `0`. -/
theorem p25_supplier_foc (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (hPi : 0 < chainProfit P D q0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    HasDerivAt
        (supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ))
        (P.ps * (1 - cdf D q0) - P.c + P.v + (P.r - P.v + P.pr) * (1 - cdf D q0)) q0 ∧
      P.ps * (1 - cdf D q0) - P.c + P.v + (P.r - P.v + P.pr) * (1 - cdf D q0) = 0 := by sorry

end CachonCoord.Newsvendor
