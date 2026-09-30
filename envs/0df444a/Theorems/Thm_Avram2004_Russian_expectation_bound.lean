-- Prove2me | Theorems.Thm_Avram2004_Russian_expectation_bound
-- name    : Avram2004.Russian.expectation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:11:34.823776+00:00
-- url     : https://prove2.me/theorems/3385a576-168b-4de1-92c3-4f8e371b0136
-- title:
--   §6, proof of Theorem 2 (p. 230) — 𝔼¹[e^{−αt+Y_t} Z^(q)(κ* − Y_t)] ≤ e^z Z^(q)(κ* − z)
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F$ on $(\Omega,\mathcal F,\mathbb P)$, satisfying the standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$), with Laplace exponent $\psi$. Let $r\ge0$ with $\psi(1)=r$, let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$, let $\alpha>0$ and $q=\alpha+r$. Write $W^{(q)}$, $Z^{(q)}$ for the scale functions of $(X,\mathbb P)$ and, for $z\ge0$, let $Y$ be the reflected process under $\mathbb P^1_{-z}$ (so $Y_0=z$). Let $\kappa^*$ be given by (30). Then for every $t\ge0$,
--   $$\mathbb E^1_{-z}\big[e^{-\alpha t+Y_t}\,Z^{(q)}(\kappa^*-Y_t)\big]\le e^{z}\,Z^{(q)}(\kappa^*-z).$$
--
--   In terms of $u(y)=e^{y}Z^{(q)}(\kappa^*-y)$ this reads $\mathbb E^1_{-z}[e^{-\alpha t}u(Y_t)]\le u(z)$: the discounted candidate value does not increase in expectation. It is the one-step inequality from which the supermartingale property of $e^{-\alpha t}u(Y_t)$ is obtained.
--
--   **Formalization Note** The paper writes the inequality under $\mathbb P^1_{s,x}$ with right side $e^{(s-x)}Z^{(q)}(\kappa^*-s+x)$; with $z=s-x$ this is the statement above. The left side is the $[0,\infty]$-valued integral of a nonnegative function, so the statement also asserts finiteness. The page derives it in the unbounded-variation case; it is stated here under the standing assumption, covering all three cases of the proof (the paper carries the same argument over to the other cases). The hypotheses are those of Theorem 2: the filtration is right-continuous but not completed, and "$\psi(1)=r$" is Mathlib's cumulant generating function at $1$; integrability of $e^{X_1}$ is not added, since the Esscher relation at $t=1$ already forces $\mathbb E[e^{X_1-r}]=1$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 230, §6, proof of Theorem 2, display after "By the expression (31) for the non-martingale part of d(exp{−αt}u(Y_t)), we deduce that"

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Shared_reflected
import Definitions.Def_Avram2004_Shared_esscher
import Definitions.Def_Avram2004_Russian_russianProblem

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Avram2004.Russian

/-- §6, proof of Theorem 2, p. 230 (display before the supermartingale claim): under `ℙ^1_{-z}`
(`Y = refl 0 (-z) X`, `Y_0 = z = s - x ≥ 0`), with `q = α + r` and `κ*` as in (30), for all `t ≥ 0`,
`𝔼^1[e^{-αt + Y_t} Z^{(q)}(κ* - Y_t)] ≤ e^z Z^{(q)}(κ* - z)`. -/
theorem expectation_bound {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r α q : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (hα : 0 < α) (hq : q = α + r)
    (z : ℝ) (hz : 0 ≤ z) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-α * (t : ℝ) + Shared.refl 0 (-z) X t ω)
        * Shared.Z P X 0 q (kappaStar P X q - Shared.refl 0 (-z) X t ω)) ∂Q
      ≤ ENNReal.ofReal (Real.exp z * Shared.Z P X 0 q (kappaStar P X q - z)) := by sorry

end Avram2004.Russian
