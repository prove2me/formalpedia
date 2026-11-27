-- Prove2me | Theorems.Thm_BosonicResources_lemma_A3
-- name    : BosonicResources.lemma_A3
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T05:59:37.993847+00:00
-- url     : https://prove2.me/theorems/1db3e6c7-9fd8-5b76-8ba4-dd5a3fac7d25
-- title:
--   Lemma A.3: total variation distance between two Gaussian distributions
-- statement:
--   Let $d$ be a natural number, let $\mu_1,\mu_2\in\mathbb R^{d}$ and let $\Sigma_1,\Sigma_2$ be real symmetric positive definite $d\times d$ matrices. Write $\mathcal N(\mu,\Sigma)$ for the Gaussian probability measure on $\mathbb R^{d}$ with mean $\mu$ and covariance $\Sigma$, and $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ (supremum over measurable sets) for the total variation distance. Define
--
--   $$
--   \Delta=\max\Big\{\big\|\Sigma_2^{-1/2}\Sigma_1\Sigma_2^{-1/2}-I\big\|_{F},\ \big\|\Sigma_2^{-1/2}(\mu_2-\mu_1)\big\|_{2}\Big\},
--   $$
--
--   where $\|\cdot\|_F$ is the Frobenius norm and $\|\cdot\|_2$ the Euclidean norm. If $\mathrm{TV}\big(\mathcal N(\mu_1,\Sigma_1),\mathcal N(\mu_2,\Sigma_2)\big)\le\tfrac1{600}$, then
--
--   $$
--   \frac{1}{200}\,\Delta\ \le\ \mathrm{TV}\big(\mathcal N(\mu_1,\Sigma_1),\mathcal N(\mu_2,\Sigma_2)\big)\ \le\ \frac{1}{\sqrt2}\,\Delta .
--   $$
--
--   This is a known result on classical Gaussian distributions, [AAL23, Theorem 1.8]: at small distance, the total variation distance of two Gaussians is equivalent, up to explicit constants, to the parameter distance $\Delta$. Applied to the Wigner distributions $\mathcal N(\mu,\Sigma)$ of Gaussian states (with $d=2n$), it is the bridge between total variation distance and the means and covariance matrices in Lemmas B.1, B.2 and B.3.
--
--   **Formalization Note** $\|\Sigma_2^{-1/2}\Sigma_1\Sigma_2^{-1/2}-I\|_F^{2}=\operatorname{Tr}\big(\Sigma_2^{-1}(\Sigma_1-\Sigma_2)\Sigma_2^{-1}(\Sigma_1-\Sigma_2)\big)$ and $\|\Sigma_2^{-1/2}v\|_2^{2}=v^{T}\Sigma_2^{-1}v$, so $\Delta$ is written without matrix square roots. $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ over measurable sets is the published `MarkovChainCLT.tvDist`, which for probability measures equals the paper's $\tfrac12\int\lvert p-q\rvert$. Positive definiteness is Mathlib's `Matrix.PosDef` and the Gaussian measure is Mathlib's `multivariateGaussian`; both inequalities are asserted as one conjunction, for every $d$.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, App. A.2, Lemma A.3, Eqs. (S12)–(S13); quoting [AAL23, Theorem 1.8] (Arbas, Ashtiani, Liaw, Polynomial time and private learning of unbounded Gaussian mixture models, ICML 2023)

import Mathlib
import Definitions.Def_TotalVariationDist
open MeasureTheory ProbabilityTheory
open MarkovChainCLT (tvDist)
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Lemma A.3 (Total variation distance between two Gaussian distributions).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Lemma A.3, Eqs. (S12)–(S13) (App. A.2), quoting [AAL23, Theorem 1.8] (Arbas, Ashtiani, Liaw, *Polynomial time
and private learning of unbounded Gaussian mixture models*, ICML 2023): "Let µ₁, µ₂ ∈ ℝ^d and Σ₁, Σ₂ be d×d positive
definite matrices. Suppose TV(N(µ₁,Σ₁), N(µ₂,Σ₂)) ≤ 1/600. Define
Δ := max{‖Σ₂^{-1/2} Σ₁ Σ₂^{-1/2} − I‖_F, ‖Σ₂^{-1/2}(µ₂−µ₁)‖₂}. Then (1/200) Δ ≤ TV(N(µ₁,Σ₁), N(µ₂,Σ₂)) ≤ (1/√2) Δ."

For `µ₁, µ₂ ∈ ℝ^d` and real symmetric positive definite `d × d` matrices `Σ₁, Σ₂` with
`TV(N(µ₁, Σ₁), N(µ₂, Σ₂)) ≤ 1/600`, and `Δ` as above, `Δ/200 ≤ TV(N(µ₁, Σ₁), N(µ₂, Σ₂)) ≤ Δ/√2`.

**Formalization Note.** `‖Σ₂^{-1/2} Σ₁ Σ₂^{-1/2} − I‖_F² = Tr(Σ₂⁻¹(Σ₁−Σ₂) Σ₂⁻¹(Σ₁−Σ₂))` and
`‖Σ₂^{-1/2} v‖₂² = vᵀ Σ₂⁻¹ v`, so `Δ` is written without matrix square roots. `TV(P, Q) = sup_A |P(A) − Q(A)|` over measurable sets (the published
`MarkovChainCLT.tvDist`), which for probability measures equals the paper's `½ ∫ |p − q|`. -/
theorem lemma_A3 {d : ℕ} (μ₁ μ₂ : EuclideanSpace ℝ (Fin d)) (S₁ S₂ : Matrix (Fin d) (Fin d) ℝ)
    (hS₁ : S₁.PosDef) (hS₂ : S₂.PosDef)
    (hsmall : tvDist (multivariateGaussian μ₁ S₁) (multivariateGaussian μ₂ S₂) ≤ 1 / 600) :
    1 / 200 * max (Real.sqrt (S₂⁻¹ * (S₁ - S₂) * S₂⁻¹ * (S₁ - S₂)).trace)
        (Real.sqrt ((WithLp.ofLp μ₂ - WithLp.ofLp μ₁) ⬝ᵥ (S₂⁻¹ *ᵥ (WithLp.ofLp μ₂ - WithLp.ofLp μ₁)))) ≤
        tvDist (multivariateGaussian μ₁ S₁) (multivariateGaussian μ₂ S₂) ∧
      tvDist (multivariateGaussian μ₁ S₁) (multivariateGaussian μ₂ S₂) ≤
        1 / Real.sqrt 2 * max (Real.sqrt (S₂⁻¹ * (S₁ - S₂) * S₂⁻¹ * (S₁ - S₂)).trace)
          (Real.sqrt ((WithLp.ofLp μ₂ - WithLp.ofLp μ₁) ⬝ᵥ
            (S₂⁻¹ *ᵥ (WithLp.ofLp μ₂ - WithLp.ofLp μ₁)))) := by sorry

end BosonicResources
