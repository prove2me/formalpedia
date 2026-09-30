-- Prove2me | Theorems.Thm_Avram2004_Canadized_canadized_russian_optimal_stopping
-- name    : Avram2004.Canadized.canadized_russian_optimal_stopping
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:57:42.585986+00:00
-- url     : https://prove2.me/theorems/19ac3c9e-d852-4f3e-9cd6-75a70ece0748
-- title:
--   Theorem 3 — the Canadized Russian option: w^CR = h and τ_{κ_*} is optimal
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F=\{\mathcal F_t\}_{t\ge0}$ under $\mathbb P$, satisfying the paper's standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$). Let $r\ge0$ with $\psi(1)=r$, where $\psi(\theta)=\log\mathbb E[e^{\theta X_1}]$ is the Laplace exponent, and let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$. Let $\alpha>0$, let $\eta(\lambda)$ be an exponential random variable of rate $\lambda>0$ which under $\mathbb P^1$ is independent of $\mathcal F_\infty=\bigvee_t\mathcal F_t$, and write $p=\alpha+\lambda+r$. $W^{(p)}$ and $Z^{(p)}(x)=1+p\int_{-\infty}^xW^{(p)}(y)\,dy$ are the scale functions of $(X,\mathbb P)$. For $z\ge0$, under $\mathbb P^1_{-z}$ the reflected process $Y=\overline X-X$ starts at $Y_0=z$. Consider the Canadized Russian optimal stopping problem
--   $$
--   w^{CR}(z)=\sup_\tau\ \mathbb E^1_{-z}\Big[e^{-\alpha(\tau\wedge\eta(\lambda))+Y_{\tau\wedge\eta(\lambda)}}\Big],
--   $$
--   the supremum over all $\mathbb P^1$-almost surely finite $\mathbf F$-stopping times $\tau$. Let
--   $$
--   \kappa_*=\inf\{x\ge0: Z^{(p)}(x)-pW^{(p)}(x)\le-\lambda/(p-\lambda)\},\qquad h(z)=\frac{(p-\lambda)e^zZ^{(p)}(\kappa_*-z)}{p}+\frac{\lambda e^z}{p}.
--   $$
--   Then for every $z\ge0$:
--
--   1. $w^{CR}(z)=h(z)$;
--   2. $\tau^*=\tau_{\kappa_*}=\inf\{t\ge0: Y_t\notin[0,\kappa_*)\}$ is an $\mathbf F$-stopping time which is $\mathbb P^1$-almost surely finite;
--   3. $\tau^*$ attains the supremum: $\mathbb E^1_{-z}[e^{-\alpha(\tau^*\wedge\eta(\lambda))+Y_{\tau^*\wedge\eta(\lambda)}}]=h(z)$.
--
--   This is the main result of §7: it gives a closed form, in terms of scale functions, for the value of a perpetual Russian option that is forcibly exercised at an independent exponential time, and it identifies the optimal exercise rule as the first time the reflected process exceeds the level $\kappa_*$.
--
--   **Formalization Note** The value function is a supremum of lower Lebesgue integrals in $[0,\infty]$, so it has no default values; the equality with the real $h(z)$ also asserts finiteness. "$\tau^*$ is the optimal stopping time" is encoded as admissibility (stopping time, $\mathbb P^1$-a.s. finite) plus attainment; that $\tau_{\kappa_*}$ is a stopping time is a conclusion, not a hypothesis. "The usual conditions" are read as right-continuity of $\mathbf F$ (no completeness, which would conflict with the Esscher relation). The clock $\eta(\lambda)$ has rate $\lambda$ and is, under $\mathbb P^1$, independent of $\mathcal F_\infty$. When $\kappa_*=0$, $\tau_0=0$ (immediate exercise).
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 233, Theorem 3, with Eq. (32) (p. 232) and the definition of κ_* (p. 233)

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Shared_reflected
import Definitions.Def_Avram2004_Shared_esscher
import Definitions.Def_Avram2004_Canadized_canadizedProblem

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Avram2004.Canadized

/-- Theorem 3, p. 233: let `X` be a spectrally negative Lévy process for the right-continuous
filtration `𝓕` under `P`, satisfying the standing assumption, with `r ≥ 0`, `ψ(1) = r`, `Q = ℙ^1` the
Esscher measure (3), `α > 0`, `η = η(λ)` an exponential random variable of rate `λ > 0` independent
of `𝓕_∞` under `Q`, and `p = α + λ + r`. Let
`κ_* = inf {x ≥ 0 : Z^{(p)}(x) - pW^{(p)}(x) ≤ -λ/(p - λ)}` and
`h(z) = (p - λ) e^z Z^{(p)}(κ_* - z)/p + λ e^z/p`. Then for every `z ≥ 0` the value of (32),
`w^{CR}(z) = sup_τ 𝔼^1_{-z}[e^{-α(τ∧η(λ)) + Y_{τ∧η(λ)}}]` over all `Q`-a.s. finite `𝓕`-stopping times,
equals `h(z)`, and `τ* = τ_{κ_*}` is a `Q`-a.s. finite `𝓕`-stopping time attaining it. -/
theorem canadized_russian_optimal_stopping {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (α : ℝ) (hα : 0 < α) (η : Ω → ℝ) (lam : ℝ)
    (hη : IsExpClock 𝓕 Q η lam) (p : ℝ) (hp : p = α + lam + r)
    (z : ℝ) (hz : 0 ≤ z) :
    valueCR 𝓕 Q X η α z = ENNReal.ofReal (hCR P X p lam z) ∧
      IsStoppingTime 𝓕 (Shared.tau 0 (-z) X (kappaLow P X p lam)) ∧
      (∀ᵐ ω ∂Q, Shared.tau 0 (-z) X (kappaLow P X p lam) ω ≠ ⊤) ∧
      ∫⁻ ω, crPayoff α z X η (Shared.tau 0 (-z) X (kappaLow P X p lam)) ω ∂Q =
        ENNReal.ofReal (hCR P X p lam z) := by sorry

end Avram2004.Canadized
