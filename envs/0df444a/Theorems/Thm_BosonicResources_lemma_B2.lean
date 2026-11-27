-- Prove2me | Theorems.Thm_BosonicResources_lemma_B2
-- name    : BosonicResources.lemma_B2
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:04:07.067872+00:00
-- url     : https://prove2.me/theorems/cf766677-96c7-4e1f-b2c0-6346c39e61f2
-- title:
--   Lemma B.2: $D_{\mathrm{tr}}\le O(\sqrt n)\,\mathrm{TV}$ between Gaussian states and their Wigner distributions
-- statement:
--   Here $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix (quadratures ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$, vacuum covariance $\tfrac12 I$). The Wigner distribution of $\rho(\mu,\Sigma)$ is $W_{\rho(\mu,\Sigma)}=\mathcal N(\mu,\Sigma)$, the Gaussian probability measure on $\mathbb R^{2n}$ with mean $\mu$ and covariance $\Sigma$; $D_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$ is the trace distance and $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ (supremum over measurable sets) is the total variation distance of probability measures.
--
--   Let $\rho=\rho(\mu_1,\Sigma_1)$ and $\sigma=\rho(\mu_2,\Sigma_2)$ be $n$-mode Gaussian states whose Wigner distributions satisfy $\mathrm{TV}(W_\rho,W_\sigma)<\tfrac1{600}$. Then
--
--   $$
--   D_{\mathrm{tr}}(\rho,\sigma)\ \le\ 200\left(\frac{1}{\sqrt2}+\frac{1+\sqrt3}{4}\sqrt{2n}\right)\mathrm{TV}(W_\rho,W_\sigma).
--   $$
--
--   This is the second inequality of Lemma 1 (Theorem S1) with an explicit constant: the trace distance of two Gaussian states exceeds the total variation distance of their Wigner distributions by at most a factor of order $\sqrt n$. The example after Lemma 1 shows that this factor is attained.
--
--   **Formalization Note** The Wigner distribution of $\rho(\mu,\Sigma)$ is the Gaussian measure $\mathcal N(\mu,\Sigma)$ on $\mathbb R^{2n}$ (Sec. 2). $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ over measurable sets is the published `MarkovChainCLT.tvDist`, which for probability measures equals the paper's $\tfrac12\int\lvert p-q\rvert$. The hypothesis is the strict inequality $\mathrm{TV}<1/600$, as printed; no lower bound on $n$ is assumed.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, App. B.1, Lemma B.2, Eq. (S27)

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

/-- **Lemma B.2 (Trace distance is at most `O(√n)` times the Wigner TV distance).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Lemma B.2, Eq. (S27) (App. B.1): "Let ρ and σ be n-mode Gaussian states with Wigner functions satisfying
TV(W_ρ, W_σ) < 1/600. Then, the trace distance between the Gaussian states can be upper bounded in terms of the total
variation distance between the Wigner functions as D_tr(ρ,σ) ≤ 200 (1/√2 + ((1+√3)/4) √(2n)) TV(W_ρ, W_σ)."

For Gaussian states `ρ = ρ(µ₁, Σ₁)` and `σ = ρ(µ₂, Σ₂)` on `n` modes with `TV(N(µ₁, Σ₁), N(µ₂, Σ₂)) < 1/600`,
`D_tr(ρ, σ) ≤ 200 (1/√2 + ((1 + √3)/4) √(2n)) · TV(N(µ₁, Σ₁), N(µ₂, Σ₂))`.

**Formalization Note.** The Wigner distribution of `ρ(µ, Σ)` is the Gaussian measure `N(µ, Σ)` on `ℝ²ⁿ` (§2). `TV(P, Q) = sup_A |P(A) − Q(A)|` over measurable sets (the published
`MarkovChainCLT.tvDist`), which for probability measures equals the paper's `½ ∫ |p − q|`. -/
theorem lemma_B2 {n : ℕ} (ρ σ : State (Occupation (Fin n))) (μ₁ μ₂ : Fin n ⊕ Fin n → ℝ)
    (S₁ S₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hρ : IsGaussianState ρ μ₁ S₁) (hσ : IsGaussianState σ μ₂ S₂)
    (hsmall : tvDist (multivariateGaussian (WithLp.toLp 2 μ₁) S₁)
        (multivariateGaussian (WithLp.toLp 2 μ₂) S₂) < 1 / 600) :
    traceDist ρ.coefficients σ.coefficients ≤
      ENNReal.ofReal (200 * (1 / Real.sqrt 2 + (1 + Real.sqrt 3) / 4 * Real.sqrt (2 * n)) *
        tvDist (multivariateGaussian (WithLp.toLp 2 μ₁) S₁)
          (multivariateGaussian (WithLp.toLp 2 μ₂) S₂)) := by sorry

end BosonicResources
