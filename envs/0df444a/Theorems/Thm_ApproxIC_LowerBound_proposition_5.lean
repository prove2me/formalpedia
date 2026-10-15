-- Prove2me | Theorems.Thm_ApproxIC_LowerBound_proposition_5
-- name    : ApproxIC.LowerBound.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:23.515261+00:00
-- url     : https://prove2.me/theorems/32e43d73-c2a1-4d66-8b0f-682300845fdb
-- title:
--   Proposition 5, p. 34 — for µ > ε·e there is δ(µ,ε) ∈ [µ²/(4ε) − µ, µ²/(4ε)] with x_pd(v) → 1 at p⋆+δ and m_pd ∈ M(ε)
-- statement:
--   Fix $\varepsilon>0$ and $\mu>\varepsilon e$. Then there is $\delta=\delta(\mu,\varepsilon)>0$ with
--   $$\frac{\mu^2}{4\varepsilon}-\mu\le\delta\le\frac{\mu^2}{4\varepsilon}$$
--   such that the following holds for every value distribution with density on $S=[0,\bar v]$ and every price $p^\star$ with $\delta<p^\star$, $\mu\le p^\star-\delta$ and $p^\star+\delta+\mu<\bar v$: every solution $x$ of (ODE)-(DDE) satisfies $\lim_{v\uparrow p^\star+\delta}x(v)=1$, and the perturbed delayed mechanism is feasible,
--   $$m_{pd}=(x_{pd},t_{pd})\in\mathcal M(\varepsilon).$$
--
--   This produces, for each small $\mu$, an $\varepsilon$-IC and individually rational randomized mechanism that misreports downward in a controlled way.
--
--   **Formalization Note** $\delta$ is chosen before the distribution and the price: the equation that fixes it, $\Gamma(2\delta/\mu)=\frac{\mu}{e\varepsilon}e^{-2\delta/\mu}$ (eq. (27)), involves neither. The paper's "for $\mu$ small such that $(p^\star-\delta,p^\star+\delta+\mu)\subset[0,\bar v]$" is rendered by the explicit hypotheses $\delta<p^\star$ and $p^\star+\delta+\mu<\bar v$ (p. 30), plus the disclosed $\mu\le p^\star-\delta$ presumed by the definition of $w$. The interval for $\delta$ is closed, as printed. Membership in $\mathcal M(\varepsilon)$ includes measurability of $x_{pd}$ and $t_{pd}$, which is a consequence here, not a hypothesis. $p^\star$ is a free real; its optimality is not used.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 34, Proposition 5; p. 30, assumptions below eq. (13)

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Setting
import Definitions.Def_ApproxIC_LowerBound_Setting
import Definitions.Def_ApproxIC_LowerBound_Delayed

namespace ApproxIC.LowerBound

open ApproxIC.UpperBound Filter Topology

/-- Proposition 5 (p. 34): for `ε > 0` and `μ > ε · e` there is `δ = δ(μ, ε) > 0` in
`[μ²/(4ε) − μ, μ²/(4ε)]` such that, for every price `p⋆` with `δ < p⋆`, `μ ≤ p⋆ − δ` and
`p⋆ + δ + μ < v̄`, the solution of (ODE)-(DDE) tends to `1` as `v ↑ p⋆ + δ` and `m_pd ∈ M(ε)`. -/
theorem proposition_5 (ε : ℝ) (hε : 0 < ε) (μ : ℝ) (hμ : ε * Real.exp 1 < μ) :
    ∃ δ > 0, δ ∈ Set.Icc (μ ^ 2 / (4 * ε) - μ) (μ ^ 2 / (4 * ε)) ∧
      ∀ M : Model, M.Standing → ∀ pstar : ℝ, δ < pstar → μ ≤ pstar - δ →
        pstar + δ + μ < M.vbar → ∀ x : ℝ → ℝ, IsPDSolution pstar μ δ ε x →
          Tendsto x (𝓝[<] (pstar + δ)) (𝓝 1) ∧ mPD x pstar μ δ ε ∈ Mset M ε := by sorry

end ApproxIC.LowerBound
