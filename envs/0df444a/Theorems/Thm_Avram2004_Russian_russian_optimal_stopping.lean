-- Prove2me | Theorems.Thm_Avram2004_Russian_russian_optimal_stopping
-- name    : Avram2004.Russian.russian_optimal_stopping
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:12:48.516858+00:00
-- url     : https://prove2.me/theorems/12feb218-e016-45bf-bb39-97151bce0a47
-- title:
--   Theorem 2 — the perpetual Russian option: w^R(z) = e^z Z^(q)(κ* − z), attained at τ_κ*
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F$ on $(\Omega,\mathcal F,\mathbb P)$, satisfying the standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$), with Laplace exponent $\psi$. Let $r\ge0$ with $\psi(1)=r$, let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$, let $\alpha>0$ and $q=\alpha+r$. Write $W^{(q)}$, $Z^{(q)}$ for the scale functions of $(X,\mathbb P)$ and, for $z\ge0$, let $Y$ be the reflected process under $\mathbb P^1_{-z}$ (so $Y_0=z$). Let
--   $$\kappa^*=\inf\{x:\ Z^{(q)}(x)\le qW^{(q)}(x)\}\qquad(30),\qquad u(z)=e^{z}Z^{(q)}(\kappa^*-z),\quad z\ge0 .$$
--   Consider the Russian optimal stopping problem (28),
--   $$w^R(z)=\sup_\tau\ \mathbb E^1_{-z}\big[e^{-\alpha\tau+Y_\tau}\big],$$
--   the supremum over all $\mathbb P^1$-almost surely finite $\mathbf F$-stopping times $\tau$. Then for every $z\ge0$:
--
--   1. $w^R(z)=u(z)$;
--   2. $\tau^*=\tau_{\kappa^*}=\inf\{t\ge0:\ Y_t\notin[0,\kappa^*)\}$ is an $\mathbf F$-stopping time;
--   3. $\tau^*$ is $\mathbb P^1$-almost surely finite;
--   4. $\tau^*$ is optimal: $\mathbb E^1_{-z}\big[e^{-\alpha\tau^*+Y_{\tau^*}}\big]=u(z)$.
--
--   Through $V_r(M_0,S_0)=S_0\,w^R(\log(M_0/S_0))$ this gives the price of the perpetual Russian option in an exponential spectrally negative Lévy market, and the optimal exercise rule: exercise when the ratio of the running maximum to the current price first reaches $e^{\kappa^*}$.
--
--   **Formalization Note** The value function is a supremum in $[0,\infty]$ of $[0,\infty]$-valued integrals of the positive payoff, so no junk value of a real supremum or of a Bochner integral enters. The admissible class is every $\mathbb P^1$-a.s. finite stopping time of the given filtration, not only passage times. That $\tau_{\kappa^*}$ is a stopping time is part of the conclusion, not a hypothesis. When $W^{(q)}(0+)\ge q^{-1}$, $\kappa^*=0$ and $\tau_0=0$ (stop immediately); the paper's $\tau_k$ is defined for $k>0$ and $\tau_0$ is its evident extension. The scale functions are those of $(X,\mathbb P)$. The hypotheses are those of Theorem 2: the filtration is right-continuous but not completed, and "$\psi(1)=r$" is Mathlib's cumulant generating function at $1$; integrability of $e^{X_1}$ is not added, since the Esscher relation at $t=1$ already forces $\mathbb E[e^{X_1-r}]=1$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 229, Theorem 2 (with (28), p. 228, and (30), p. 229)

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

/-- Theorem 2, p. 229: let `X` be a spectrally negative Lévy process for the right-continuous
filtration `𝓕` under `P`, satisfying the standing assumption, with `r ≥ 0`, `ψ(1) = r`, `Q = ℙ^1` the
Esscher measure (3), `α > 0` and `q = α + r`. Let `κ*` be given by (30) and
`u(z) = e^z Z^{(q)}(κ* - z)`. Then for every `z ≥ 0` the value of (28),
`w^R(z) = sup_τ 𝔼^1_{-z}[e^{-ατ + Y_τ}]` over all `Q`-a.s. finite `𝓕`-stopping times, equals `u(z)`, and
`τ* = τ_{κ*}` is a `Q`-a.s. finite `𝓕`-stopping time attaining it. -/
theorem russian_optimal_stopping {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r α q : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (hα : 0 < α) (hq : q = α + r)
    (z : ℝ) (hz : 0 ≤ z) :
    valueR 𝓕 Q X α z = ENNReal.ofReal (uR P X q z) ∧
      IsStoppingTime 𝓕 (Shared.tau 0 (-z) X (kappaStar P X q)) ∧
      (∀ᵐ ω ∂Q, Shared.tau 0 (-z) X (kappaStar P X q) ω ≠ ⊤) ∧
      ∫⁻ ω, rpayoff α z X (Shared.tau 0 (-z) X (kappaStar P X q)) ω ∂Q = ENNReal.ofReal (uR P X q z) := by sorry

end Avram2004.Russian
