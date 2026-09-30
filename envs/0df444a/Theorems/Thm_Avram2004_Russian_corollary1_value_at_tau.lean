-- Prove2me | Theorems.Thm_Avram2004_Russian_corollary1_value_at_tau
-- name    : Avram2004.Russian.corollary1_value_at_tau
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:07:45.964685+00:00
-- url     : https://prove2.me/theorems/b1e2cdab-b15f-46fd-8239-f424a98d8eb2
-- title:
--   Corollary 1, (29) — the value of stopping at τ_k under ℙ¹
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F$ on $(\Omega,\mathcal F,\mathbb P)$, satisfying the standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$), with Laplace exponent $\psi$. Let $r\ge0$ with $\psi(1)=r$, let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$, let $\alpha>0$ and $q=\alpha+r$. Write $W^{(q)}$, $Z^{(q)}$ for the scale functions of $(X,\mathbb P)$ and, for $z\ge0$, let $Y$ be the reflected process under $\mathbb P^1_{-z}$ (so $Y_0=z$). Then for every $k\ge0$ and $z\ge0$,
--   $$\mathbb E^1_{-z}\big(e^{-\alpha\tau_k+Y_{\tau_k}}\big)=e^{z}\Big(Z^{(q)}(k-z)+\frac{Z^{(q)}(k)-qW^{(q)}(k)}{W^{(q)\prime}(k)-W^{(q)}(k)}\,W^{(q)}(k-z)\Big),$$
--   where $\tau_k=\inf\{t\ge0:Y_t\notin[0,k)\}$ and $W^{(q)\prime}$ is the derivative of $W^{(q)}$.
--
--   This expresses the reward of the threshold rule "stop when $Y$ first reaches level $k$" through scale functions; optimizing it over $k$ leads to the level $\kappa^*$ of (30).
--
--   **Formalization Note** The left side is the $[0,\infty]$-valued integral of the nonnegative payoff, and the identity is stated as its equality with the (nonnegative) right side; this also asserts that the expectation is finite, which is not automatic because $Y_{\tau_k}$ can overshoot $k$ by a jump of $X$. The scale functions are those of $(X,\mathbb P)$, not of $(X,\mathbb P^1)$ (the paper converts by Remark 4). At $k=0$ both sides equal $e^z$: $\tau_0=0$ and $W^{(q)}(k-z)=0$. The hypotheses are those of Theorem 2: the filtration is right-continuous but not completed, and "$\psi(1)=r$" is Mathlib's cumulant generating function at $1$; integrability of $e^{X_1}$ is not added, since the Esscher relation at $t=1$ already forces $\mathbb E[e^{X_1-r}]=1$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 228, Corollary 1, Eq. (29)

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

/-- Corollary 1, (29), p. 228: with `ψ(1) = r`, `ℙ^1` the Esscher measure, `α > 0` and `q = α + r`,
for `k ≥ 0` and `z ≥ 0`,
`𝔼^1_{-z}(e^{-ατ_k + Y_{τ_k}}) = e^z (Z^{(q)}(k - z) + (Z^{(q)}(k) - qW^{(q)}(k)) / (W^{(q)′}(k) - W^{(q)}(k)) W^{(q)}(k - z))`,
with the scale functions of `(X, P)`. -/
theorem corollary1_value_at_tau {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r α q : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (hα : 0 < α) (hq : q = α + r)
    (k z : ℝ) (hk : 0 ≤ k) (hz : 0 ≤ z) :
    ∫⁻ ω, rpayoff α z X (Shared.tau 0 (-z) X k) ω ∂Q =
      ENNReal.ofReal (Real.exp z *
        (Shared.Z P X 0 q (k - z)
          + (Shared.Z P X 0 q k - q * Shared.W P X 0 q k) / (deriv (Shared.W P X 0 q) k - Shared.W P X 0 q k)
            * Shared.W P X 0 q (k - z))) := by sorry

end Avram2004.Russian
