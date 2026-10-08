-- Prove2me | Theorems.Thm_CachonCoord_Newsvendor_p24_wq_range
-- name    : CachonCoord.Newsvendor.p24_wq_range
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:08:31.087412+00:00
-- url     : https://prove2.me/theorems/e8d12485-eab7-43d9-b5d6-f2b1bc1c3f6f
-- title:
--   §6.2.5, p. 24 — w_q(0) = (p − v + g_r)F̄(q°) + v − c_r, w_q(1) = p + g_r − c_r, w_q(δ) increasing, so v − c_r ≤ w_q(δ) ≤ p + g_r − c_r
-- statement:
--   Let $q^o$ maximize the supply chain profit $\Pi(q) = (p - v + g)S(q) - (c - v)q - g\mu$. Under the quantity flexibility contract the wholesale price that makes $q^o$ satisfy the retailer's first-order condition (11) is
--   $$w_q(\delta) = \frac{(p - v + g_r)(1 - F(q^o))}{1 - F(q^o) + (1-\delta)F((1-\delta)q^o)} - c_r + v.$$
--   Then
--   $$w_q(0) = (p - v + g_r)\bar F(q^o) + v - c_r, \qquad w_q(1) = p + g_r - c_r,$$
--   $w_q(\delta)$ is strictly increasing on $\delta \in [0,1]$, and consequently $v - c_r \le w_q(\delta) \le p + g_r - c_r$ for every $\delta \in [0,1]$.
--
--   This is the range Cachon uses to conclude that the retailer's profit is concave under $(w_q(\delta), \delta)$, so that $w_q(\delta)$ is indeed a coordinating wholesale price.
--
--   **Formalization Note** The local `ContractData` has Cachon’s assumptions $v<c_s+c_r$, $c_s+c_r<p$, and nonnegative goodwill costs. It permits negative net salvage and $v\ge c_r$. Demand is a probability law on $[0,\infty)$ with finite mean and a continuous cdf strictly increasing until it reaches one. These are the chapter’s standing assumptions; $\Pi(q^o)>0$ is included wherever a chain optimum is named. Cachon’s differentiable cdf is represented on the interior of its active support by `hFderiv`; derivative claims use `HasDerivAt`. $w_q(\delta)$ is the local `quantityFlexPrice` (the explicit formula, not "the solution of (11)"). The page says "increasing"; the Lean states strict monotonicity, which holds because $q^o > 0$ and $F$ is positive on $(0, \infty)$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.2.5, p. 24 (w_q(δ) display after (11); the range sentence and the w_q(0), w_q(1) displays)

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- Cachon (2003), §6.2.5, p. 24: the quantity flexibility wholesale price
`w_q(δ) = (p − v + g_r)(1 − F(q°)) / (1 − F(q°) + (1 − δ)F((1 − δ)q°)) − c_r + v` satisfies
`w_q(0) = (p − v + g_r)F̄(q°) + v − c_r`, `w_q(1) = p + g_r − c_r`, is (strictly) increasing in
`δ ∈ [0, 1]`, and so lies in `[v − c_r, p + g_r − c_r]` for `δ ∈ [0, 1]`. -/
theorem p24_wq_range (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (hPi : 0 < chainProfit P D q0) :
    quantityFlexPrice P D q0 0 = (P.r - P.v + P.pr) * (1 - cdf D q0) + P.v - P.cr ∧
      quantityFlexPrice P D q0 1 = P.r + P.pr - P.cr ∧
      StrictMonoOn (fun δ => quantityFlexPrice P D q0 δ) (Set.Icc 0 1) ∧
      ∀ δ ∈ Set.Icc (0 : ℝ) 1,
        P.v - P.cr ≤ quantityFlexPrice P D q0 δ ∧ quantityFlexPrice P D q0 δ ≤ P.r + P.pr - P.cr := by sorry

end CachonCoord.Newsvendor
