-- Prove2me | Theorems.Thm_ApproxIC_LowerBound_proposition_3
-- name    : ApproxIC.LowerBound.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:13.247571+00:00
-- url     : https://prove2.me/theorems/b62ce03d-02ef-4661-8ba7-838ee9f72b86
-- title:
--   Proposition 3, p. 31 — if x_pd(v) → 1 as v ↑ p⋆ + δ, then v⋆(·|µ,δ) is a best reporting function for m_pd
-- statement:
--   Let $F$ be a value distribution with density on $S=[0,\bar v]$, and let $\varepsilon>0$, $\mu>0$ and $0<\delta<p^\star$ with $\mu\le p^\star-\delta$ and $p^\star+\delta+\mu<\bar v$. Let $x$ solve (ODE)-(DDE) on $[0,p^\star+\delta]$, and let $m_{pd}=(x_{pd},t_{pd})$ be the perturbed delayed mechanism built from it ($x_{pd}=x$ on $[0,p^\star+\delta]$, $x_{pd}=1$ on $(p^\star+\delta,\bar v]$, and $t_{pd}$ as in Proposition 3). If
--   $$\lim_{v\uparrow p^\star+\delta}x(v)=1,$$
--   then $v^\star(\cdot\,|\,\mu,\delta)$ of eq. (13) is a best reporting function for $m_{pd}$: for every $v\in S$, $v^\star(v)\in S$ and
--   $$v\,x_{pd}(w)-t_{pd}(w)\le v\,x_{pd}(v^\star(v))-t_{pd}(v^\star(v))\qquad\forall w\in S.$$
--
--   The proposition turns the choice of a downward-misreporting strategy into a mechanism: the allocation and payments are determined by $v^\star$ through the differential equations.
--
--   **Formalization Note** The price $p^\star$ is a free real; optimality of $p^\star$ is not used. $\mu\le p^\star-\delta$ is a disclosed addition, presumed by the paper's definition of $w$; $\delta<p^\star$ and $p^\star+\delta+\mu<\bar v$ are the paper's assumptions (p. 30). The limit is stated for the solution $x$, which coincides with $x_{pd}$ on $[0,p^\star+\delta]$. "Best reporting function" is eq. (5), p. 14.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 31, Proposition 3; p. 30, eq. (13) and the assumptions below it; p. 14, eq. (5)

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Setting
import Definitions.Def_ApproxIC_LowerBound_Setting
import Definitions.Def_ApproxIC_LowerBound_Delayed

namespace ApproxIC.LowerBound

open ApproxIC.UpperBound Filter Topology

/-- Proposition 3 (p. 31): if the solution `x` of (ODE)-(DDE) tends to `1` as `v ↑ p⋆ + δ`, then
`v⋆(·|μ, δ)` of eq. (13) is a best reporting function for `m_pd = (x_pd, t_pd)`. -/
theorem proposition_3 (M : Model) (hM : M.Standing) (pstar μ δ ε : ℝ) (hε : 0 < ε) (hμ : 0 < μ)
    (hδ : 0 < δ) (hδp : δ < pstar) (hμp : μ ≤ pstar - δ) (hv : pstar + δ + μ < M.vbar)
    (x : ℝ → ℝ) (hx : IsPDSolution pstar μ δ ε x)
    (hlim : Tendsto x (𝓝[<] (pstar + δ)) (𝓝 1)) :
    IsBestReporting M (mPD x pstar μ δ ε) (vstarPD pstar μ δ) := by sorry

end ApproxIC.LowerBound
