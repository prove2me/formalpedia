-- Prove2me | Theorems.Thm_Avram2004_Canadized_eta_elimination
-- name    : Avram2004.Canadized.eta_elimination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T06:59:53.807979+00:00
-- url     : https://prove2.me/theorems/37810f63-87de-4313-83df-1aeeced682d8
-- title:
--   §7, display after (32) — eliminating the independent exponential clock η(λ)
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F=\{\mathcal F_t\}_{t\ge0}$ under $\mathbb P$, satisfying the paper's standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$). Let $r\ge0$ with $\psi(1)=r$, where $\psi(\theta)=\log\mathbb E[e^{\theta X_1}]$ is the Laplace exponent, and let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$. Let $\alpha>0$, let $\eta(\lambda)$ be an exponential random variable of rate $\lambda>0$ which under $\mathbb P^1$ is independent of $\mathcal F_\infty=\bigvee_t\mathcal F_t$, and write $p=\alpha+\lambda+r$. Under $\mathbb P^1_{-z}$ ($z\ge0$) the reflected process $Y=\overline X-X$ starts at $Y_0=z$. Then for every $\mathbb P^1$-almost surely finite $\mathbf F$-stopping time $\tau$,
--   $$
--   \mathbb E^1_{-z}\Big[e^{-\alpha(\tau\wedge\eta(\lambda))+Y_{\tau\wedge\eta(\lambda)}}\Big]=\mathbb E^1_{-z}\Big[e^{-(\alpha+\lambda)\tau+Y_\tau}+\lambda\int_0^\tau e^{-(\alpha+\lambda)t+Y_t}\,dt\Big].
--   $$
--
--   Taking the supremum over $\tau$ gives the paper's rewriting of the Canadized problem (32) as a problem without the clock: $w^{CR}(z)=\sup_\tau\mathbb E^1_{-z}[e^{-(\alpha+\lambda)\tau+Y_\tau}+\lambda\int_0^\tau e^{-(\alpha+\lambda)t+Y_t}dt]$. The Canadization thus becomes a heavier discount rate $\alpha+\lambda$ plus a running reward.
--
--   **Formalization Note** The page states the identity for the suprema, justified by the independence of $\eta(\lambda)$; we state it for each admissible $\tau$, which implies the page's statement. Both sides are computed in $[0,\infty]$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 232, §7, display after Eq. (32)

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

/-- §7, p. 232, display after (32): elimination of the exponential clock `η = η(λ)`. For every
`Q`-a.s. finite `𝓕`-stopping time `τ` and `z ≥ 0`, under `ℙ^1_{-z}` (`Y = refl 0 (-z) X`),
`𝔼^1_{-z}[e^{-α(τ∧η(λ)) + Y_{τ∧η(λ)}}] = 𝔼^1_{-z}[e^{-(α+λ)τ + Y_τ} + λ ∫_0^τ e^{-(α+λ)t + Y_t} dt]`,
both sides in `[0, ∞]`. Taking the supremum over `τ` gives the page's rewriting of `w^{CR}(z)`. -/
theorem eta_elimination {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (α : ℝ) (hα : 0 < α) (η : Ω → ℝ) (lam : ℝ)
    (hη : IsExpClock 𝓕 Q η lam) (p : ℝ) (hp : p = α + lam + r)
    (τ : Ω → WithTop ℝ≥0) (hτ : τ ∈ Admissible 𝓕 Q) (z : ℝ) (hz : 0 ≤ z) :
    ∫⁻ ω, crPayoff α z X η τ ω ∂Q =
      ∫⁻ ω, (payoffAt (α + lam) (Shared.refl 0 (-z) X) τ ω
        + ENNReal.ofReal lam * runIntegral (α + lam) (Shared.refl 0 (-z) X) τ ω) ∂Q := by sorry

end Avram2004.Canadized
