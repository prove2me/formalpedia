-- Prove2me | Theorems.Thm_ExploreFirst_LargeT_inv_kinf_shift
-- name    : ExploreFirst.LargeT.inv_kinf_shift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:34.559126+00:00
-- url     : https://prove2.me/theorems/a9584e4f-f379-48a5-bec6-2d08cd7af373
-- title:
--   p. 17 display — inverse K_inf under a small increase in the target mean
-- statement:
--   Let $\mathcal D$ be a well-behaved model with witnesses $\varepsilon_{\mathcal D}$ and $\omega_{\mathcal D}$. Let $\underline\nu$ belong to the model and $a$ be suboptimal, with $\mu^*\in E(\mathcal D)$ and $0<\mathcal K_{\inf}(\nu_a,\mu^*,\mathcal D)<\infty$. For $0<\varepsilon<\varepsilon_{\mathcal D}(\mu^*)$,
--   $$
--   \frac{1}{\mathcal K_{\inf}(\nu_a,\mu^*+\varepsilon,\mathcal D)}\ge
--   \frac{1}{\mathcal K_{\inf}(\nu_a,\mu^*,\mathcal D)}
--   \left(1-\frac{\varepsilon\omega_{\mathcal D}(\nu_a,\mu^*)}{\mathcal K_{\inf}(\nu_a,\mu^*,\mathcal D)}\right).
--   $$
--   This converts the perturbed information cost in (17) to the cost at the original optimal mean.
--
--   **Formalization Note** The positivity and finiteness conditions prevent Lean's totalized real reciprocal from giving a junk value. The paper's $\forall\varepsilon<\varepsilon_{\mathcal D}(\mu^*)$ is read in the intended positive range.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 17, display after (17)

import Mathlib
import Definitions.Def_ExploreFirst_LargeT_Setting

namespace ExploreFirst.LargeT

open MeasureTheory BanditAlgorithm

/-- The inverse-information-cost bound displayed after (17) on p. 17. -/
theorem inv_kinf_shift {K : ℕ} (𝒟 : Set (Measure ℝ))
    (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (εD : ℝ → ℝ)
    (ωD : Measure ℝ → ℝ → ℝ)
    (hwell : IsWellBehaved 𝒟 εD ωD)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a : Fin K) (ha : 0 < banditGap ν a)
    (hμ : banditOptimalMean ν ∈ expectationInterior 𝒟)
    (hKpos : 0 < banditDInf 𝒟 (ν.P a) (banditOptimalMean ν))
    (hKfin : banditDInf 𝒟 (ν.P a) (banditOptimalMean ν) ≠ ⊤)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < εD (banditOptimalMean ν)) :
    (let K₀ := banditDInf 𝒟 (ν.P a) (banditOptimalMean ν)
     1 / K₀.toReal * (1 - ε * ωD (ν.P a) (banditOptimalMean ν) / K₀.toReal) ≤
       1 / (banditDInf 𝒟 (ν.P a) (banditOptimalMean ν + ε)).toReal) := by sorry

end ExploreFirst.LargeT
