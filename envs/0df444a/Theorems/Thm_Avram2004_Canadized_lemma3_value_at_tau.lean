-- Prove2me | Theorems.Thm_Avram2004_Canadized_lemma3_value_at_tau
-- name    : Avram2004.Canadized.lemma3_value_at_tau
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:25:43.741986+00:00
-- url     : https://prove2.me/theorems/90c424f8-9307-40f6-9368-283e4c947138
-- title:
--   Lemma 3, Eq. (33) — the value of exercising at τ_k ∧ η(λ)
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F=\{\mathcal F_t\}_{t\ge0}$ under $\mathbb P$, satisfying the paper's standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$). Let $r\ge0$ with $\psi(1)=r$, where $\psi(\theta)=\log\mathbb E[e^{\theta X_1}]$ is the Laplace exponent, and let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$. Let $\alpha>0$, let $\eta(\lambda)$ be an exponential random variable of rate $\lambda>0$ which under $\mathbb P^1$ is independent of $\mathcal F_\infty=\bigvee_t\mathcal F_t$, and write $p=\alpha+\lambda+r$. $W^{(p)}$ and $Z^{(p)}(x)=1+p\int_{-\infty}^xW^{(p)}(y)\,dy$ are the scale functions of $(X,\mathbb P)$. Under $\mathbb P^1_{-z}$ ($z\ge0$) the reflected process $Y$ starts at $Y_0=z$, and $\tau_k=\inf\{t\ge0:Y_t\notin[0,k)\}$. For each $k>0$,
--   $$
--   \mathbb E^1_{-z}\Big[e^{-\alpha(\tau_k\wedge\eta(\lambda))+Y_{\tau_k\wedge\eta(\lambda)}}\Big]=\Big(\frac{p-\lambda}{p}\Big)e^zZ^{(p)}(k-z)+\frac{\lambda}{p}e^z+e^z\,\frac{(p-\lambda)\big(Z^{(p)}(k)-pW^{(p)}(k)\big)+\lambda}{p\big(W^{(p)\prime}(k)-W^{(p)}(k)\big)}\,W^{(p)}(k-z).
--   $$
--
--   This is the value of the threshold rule "exercise the Canadized Russian option when $Y$ first reaches $k$". The optimal level $\kappa_*$ of Theorem 3 is the one at which the coefficient of $W^{(p)}(k-z)$ vanishes.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral in $[0,\infty]$; the equality with the real right-hand side also asserts finiteness. $W^{(p)\prime}(k)$ is the derivative at $k$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 232, Lemma 3, Eq. (33)

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

/-- Lemma 3, (33), p. 232: for each `k > 0` and `z ≥ 0`, under `ℙ^1_{-z}` (`Y = refl 0 (-z) X`), with
`p = α + λ + r` and the scale functions of `(X, P)`,
`𝔼^1_{-z}[e^{-α(τ_k∧η(λ)) + Y_{τ_k∧η(λ)}}] = ((p-λ)/p) e^z Z^{(p)}(k-z) + (λ/p) e^z
  + e^z ((p-λ)(Z^{(p)}(k) - pW^{(p)}(k)) + λ) / (p (W^{(p)′}(k) - W^{(p)}(k))) W^{(p)}(k-z)`. -/
theorem lemma3_value_at_tau {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (α : ℝ) (hα : 0 < α) (η : Ω → ℝ) (lam : ℝ)
    (hη : IsExpClock 𝓕 Q η lam) (p : ℝ) (hp : p = α + lam + r)
    (k z : ℝ) (hk : 0 < k) (hz : 0 ≤ z) :
    ∫⁻ ω, crPayoff α z X η (Shared.tau 0 (-z) X k) ω ∂Q =
      ENNReal.ofReal ((p - lam) / p * Real.exp z * Shared.Z P X 0 p (k - z) + lam / p * Real.exp z
        + Real.exp z * ((p - lam) * (Shared.Z P X 0 p k - p * Shared.W P X 0 p k) + lam)
            / (p * (deriv (Shared.W P X 0 p) k - Shared.W P X 0 p k)) * Shared.W P X 0 p (k - z)) := by sorry

end Avram2004.Canadized
