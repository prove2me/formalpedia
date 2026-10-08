-- Prove2me | Theorems.Thm_CachonCoord_Newsvendor_p25_qf_allocation
-- name    : CachonCoord.Newsvendor.p25_qf_allocation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:09:06.441789+00:00
-- url     : https://prove2.me/theorems/071a9f72-60e1-42a2-a87c-3bee2be692ca
-- title:
--   §6.2.5, p. 25 — the (w_q(δ), δ) quantity flexibility contract gives the retailer ≥ Π(q°) at δ = 0, the supplier ≥ Π(q°) at δ = 1, and every split of Π(q°)
-- statement:
--   Let $q^o$ maximize the supply chain profit $\Pi(q) = (p - v + g)S(q) - (c - v)q - g\mu$, and assume $\Pi(q^o) > 0$. Consider the quantity flexibility contracts $(w_q(\delta), \delta)$, $0 \le \delta \le 1$, with
--   $$w_q(\delta) = \frac{(p - v + g_r)(1 - F(q^o))}{1 - F(q^o) + (1-\delta)F((1-\delta)q^o)} - c_r + v .$$
--   Then:
--
--   1. at $\delta = 0$ the retailer earns at least the supply chain optimal profit:
--   $$\pi_r(q^o, w_q(0), 0) = \Pi(q^o) + g_s\big(\mu - S(q^o) + \bar F(q^o)q^o\big) \ge \Pi(q^o);$$
--   2. at $\delta = 1$ the supplier earns at least the supply chain optimal profit:
--   $$\pi_s(q^o, w_q(1), 1) = \Pi(q^o) + \mu g_r \ge \Pi(q^o);$$
--   3. every allocation of $\Pi(q^o)$ is possible: for every $a$ with $0 \le a \le \Pi(q^o)$ there is $\delta \in [0,1]$ with
--   $$\pi_r(q^o, w_q(\delta), \delta) = a \quad\text{and}\quad \pi_s(q^o, w_q(\delta), \delta) = \Pi(q^o) - a .$$
--
--   Together with the retailer's optimality of $q^o$ under $(w_q(\delta),\delta)$, this shows that the quantity flexibility contract coordinates the newsvendor supply chain (with forced compliance) and can divide its profit arbitrarily.
--
--   **Formalization Note** The local `ContractData` has Cachon’s assumptions $v<c_s+c_r$, $c_s+c_r<p$, and nonnegative goodwill costs. It permits negative net salvage and $v\ge c_r$. Demand is a probability law on $[0,\infty)$ with finite mean and a continuous cdf strictly increasing until it reaches one. These are the chapter’s standing assumptions; $\Pi(q^o)>0$ is included wherever a chain optimum is named. Cachon’s differentiable cdf is represented on the interior of its active support by `hFderiv`; derivative claims use `HasDerivAt`. $\Pi(q^o) > 0$ is the standing assumption of p. 11. The continuity in $\delta$ that the page invokes is not assumed: it is part of what must be proved. The displays of p. 25 mix $q$ and $q^o$ (printed slip); the Lean states them at $q^o$. The profits are the local `retailerProfit`/`supplierProfit` with `quantityFlexTransfer` at `quantityFlexPrice`; they sum to $\Pi$ for every transfer by definition, so the supplier's share in clause 3 is $\Pi(q^o) - a$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.2.5, p. 25 (allocation paragraph: δ = 0 and δ = 1 displays and the sentence "Given that the profit functions are continuous in δ, it follows that all possible allocations of Π(q°) are possible.")

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.5, p. 25 — profit allocation under the quantity flexibility contract
`(w_q(δ), δ)`: at δ = 0 the retailer earns `Π(q°) + g_s(μ − S(q°) + F̄(q°)q°) ≥ Π(q°)`; at δ = 1
the supplier earns `Π(q°) + μg_r ≥ Π(q°)`; and, the profits being continuous in δ, every
allocation of `Π(q°)` (retailer `a`, supplier `Π(q°) − a`, `0 ≤ a ≤ Π(q°)`) arises for some
`δ ∈ [0, 1]`. Standing assumption `Π(q°) > 0` (p. 11). -/
theorem p25_qf_allocation (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0) (hPi : 0 < chainProfit P D q0) :
    (retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 =
        chainProfit P D q0 + P.ps * (meanDemand D - expSales D q0 + (1 - cdf D q0) * q0) ∧
      chainProfit P D q0 ≤
        retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0) ∧
    (supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 =
        chainProfit P D q0 + meanDemand D * P.pr ∧
      chainProfit P D q0 ≤
        supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0) ∧
    ∀ a ∈ Set.Icc 0 (chainProfit P D q0), ∃ δ ∈ Set.Icc (0 : ℝ) 1,
      retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ) q0 = a ∧
      supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ) q0 =
        chainProfit P D q0 - a := by sorry

end CachonCoord.Newsvendor
