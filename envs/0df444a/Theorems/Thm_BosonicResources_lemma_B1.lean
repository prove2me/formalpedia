-- Prove2me | Theorems.Thm_BosonicResources_lemma_B1
-- name    : BosonicResources.lemma_B1
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:00:55.336511+00:00
-- url     : https://prove2.me/theorems/4a7d54b6-7fac-5eb9-9586-06f94d701303
-- title:
--   Lemma B.1: $D_{\mathrm{tr}}\ge\frac{\sqrt2}{400}\,\mathrm{TV}$ between Gaussian states and their Wigner distributions
-- statement:
--   Here $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix (quadratures ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$, vacuum covariance $\tfrac12 I$). The Wigner distribution of $\rho(\mu,\Sigma)$ is $W_{\rho(\mu,\Sigma)}=\mathcal N(\mu,\Sigma)$, the Gaussian probability measure on $\mathbb R^{2n}$ with mean $\mu$ and covariance $\Sigma$; $D_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$ is the trace distance and $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ (supremum over measurable sets) is the total variation distance of probability measures.
--
--   Let $\rho=\rho(\mu_1,\Sigma_1)$ and $\sigma=\rho(\mu_2,\Sigma_2)$ be $n$-mode Gaussian states such that $D_{\mathrm{tr}}(\rho,\sigma)\le\dfrac{\sqrt2}{240000}$. Then
--
--   $$
--   D_{\mathrm{tr}}(\rho,\sigma)\ \ge\ \frac{\sqrt2}{400}\,\mathrm{TV}(W_\rho,W_\sigma).
--   $$
--
--   This is the first inequality of Lemma 1 (Theorem S1) with explicit constants, $c_0=\sqrt2/240000$ and $c_1=\sqrt2/400$: two Gaussian states that are close in trace distance have Wigner distributions that are close in total variation distance. The paper remarks that the constants are not fundamental.
--
--   **Formalization Note** The Wigner distribution of $\rho(\mu,\Sigma)$ is the Gaussian measure $\mathcal N(\mu,\Sigma)$ on $\mathbb R^{2n}$ (Sec. 2). $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ over measurable sets is the published `MarkovChainCLT.tvDist`, which for probability measures equals the paper's $\tfrac12\int\lvert p-q\rvert$. The two states are given through `BosonicLearn.IsGaussianState`; no lower bound on $n$ is assumed.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, App. B.1, Lemma B.1, Eq. (S25)

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_TotalVariationDist
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open MarkovChainCLT (tvDist)
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Lemma B.1 (Trace distance is at least a constant times the Wigner TV distance).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Lemma B.1, Eq. (S25) (App. B.1): "For any two n-mode Gaussian states ρ(µ₁,Σ₁) and σ(µ₂,Σ₂), it holds that,
D_tr(ρ,σ) ≥ (√2/400) TV(W_ρ, W_σ), given that D_tr(ρ,σ) ≤ √2/240000."

For Gaussian states `ρ = ρ(µ₁, Σ₁)` and `σ = ρ(µ₂, Σ₂)` on `n` modes with `D_tr(ρ, σ) ≤ √2/240000`,
`D_tr(ρ, σ) ≥ (√2/400) · TV(N(µ₁, Σ₁), N(µ₂, Σ₂))`.

**Formalization Note.** The Wigner distribution of `ρ(µ, Σ)` is the Gaussian measure `N(µ, Σ)` on `ℝ²ⁿ` (§2). `TV(P, Q) = sup_A |P(A) − Q(A)|` over measurable sets (the published
`MarkovChainCLT.tvDist`), which for probability measures equals the paper's `½ ∫ |p − q|`. -/
theorem lemma_B1 {n : ℕ} (ρ σ : State (Occupation (Fin n))) (μ₁ μ₂ : Fin n ⊕ Fin n → ℝ)
    (S₁ S₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hρ : IsGaussianState ρ μ₁ S₁) (hσ : IsGaussianState σ μ₂ S₂)
    (hsmall : traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal (Real.sqrt 2 / 240000)) :
    ENNReal.ofReal (Real.sqrt 2 / 400 * tvDist (multivariateGaussian (WithLp.toLp 2 μ₁) S₁)
        (multivariateGaussian (WithLp.toLp 2 μ₂) S₂)) ≤
      traceDist ρ.coefficients σ.coefficients := by sorry

end BosonicResources
