-- Prove2me | Theorems.Thm_ApproxIC_LowerBound_proposition_6
-- name    : ApproxIC.LowerBound.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:30.218202+00:00
-- url     : https://prove2.me/theorems/2528e501-5f7b-4970-b525-f17132c454d6
-- title:
--   Proposition 6, p. 35 — Π(m_pd) = ∫_0^{p⋆+δ} x_pd(v)(v f(v) − F̄(v+µ)ẇ(v))dv + R(p⋆+δ) + ∫_{p⋆+δ}^{p⋆+δ+µ} F̄
-- statement:
--   Let $F$ be a value distribution with density $f$ on $S=[0,\bar v]$, and let $\varepsilon>0$, $\mu>0$, $0<\delta<p^\star$ with $\mu\le p^\star-\delta$ and $p^\star+\delta+\mu<\bar v$. Let $x$ solve (ODE)-(DDE), suppose $\lim_{v\uparrow p^\star+\delta}x(v)=1$ and that the perturbed delayed mechanism is feasible, $m_{pd}\in\mathcal M(\varepsilon)$. Then
--   $$\Pi(m_{pd})=\int_0^{p^\star+\delta}x_{pd}(v)\big(v f(v)-\bar F(v+\mu)\,\dot w(v)\big)\,dv+R(p^\star+\delta)+\int_{p^\star+\delta}^{p^\star+\delta+\mu}\bar F(v)\,dv.$$
--   In the paper's notation the integrand is $x_{pd}(v)\,\psi(v\,|\,w(\cdot))\,f(v)$ with the **delayed virtual value** $\psi(v\,|\,w(\cdot))=v-\frac{\bar F(v+\mu)}{f(v)}\dot w(v)$.
--
--   The formula separates the revenue of $m_{pd}$ into a virtual-value term, the revenue of a posted price at $p^\star+\delta$, and the gain from the soft region above it; Theorem 3 bounds each term from below.
--
--   **Formalization Note** The product form $v f(v)-\bar F(v+\mu)\dot w(v)$ replaces $\psi\cdot f$, because $\psi$ divides by $f(v)$, which may vanish; only the product enters the formula (the proof, p. 62, derives this product). $\dot w$ is `deriv w`; $w$ is piecewise linear with one kink at $p^\star-\delta-\mu$, a null set. "Feasible" is the situation of Proposition 5, posed as the two hypotheses (limit $1$ and $m_{pd}\in\mathcal M(\varepsilon)$). $p^\star$ is a free real, and $\mu\le p^\star-\delta$ is the disclosed addition presumed by the definition of $w$.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 35, Proposition 6; p. 62, proof of Proposition 6

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Setting
import Definitions.Def_ApproxIC_LowerBound_Setting
import Definitions.Def_ApproxIC_LowerBound_Delayed

namespace ApproxIC.LowerBound

open ApproxIC.UpperBound Filter Topology

/-- Proposition 6 (p. 35), with `ψ(v|w) f(v)` written as `v f(v) − F̄(v + μ) ẇ(v)`:
`Π(m_pd) = ∫_0^{p⋆+δ} x_pd(v) (v f(v) − F̄(v + μ) ẇ(v)) dv + R(p⋆ + δ) + ∫_{p⋆+δ}^{p⋆+δ+μ} F̄(v) dv`. -/
theorem proposition_6 (M : Model) (hM : M.Standing) (pstar μ δ ε : ℝ) (hε : 0 < ε) (hμ : 0 < μ)
    (hδ : 0 < δ) (hδp : δ < pstar) (hμp : μ ≤ pstar - δ) (hv : pstar + δ + μ < M.vbar)
    (x : ℝ → ℝ) (hx : IsPDSolution pstar μ δ ε x)
    (hlim : Tendsto x (𝓝[<] (pstar + δ)) (𝓝 1)) (hfeas : mPD x pstar μ δ ε ∈ Mset M ε) :
    revenue M (mPD x pstar μ δ ε) =
      (∫ v in (0)..(pstar + δ),
        xPD x pstar δ v * (v * M.f v - cdfBar M (v + μ) * deriv (wPD pstar μ δ) v)) +
      R M (pstar + δ) + ∫ v in (pstar + δ)..(pstar + δ + μ), cdfBar M v := by sorry

end ApproxIC.LowerBound
