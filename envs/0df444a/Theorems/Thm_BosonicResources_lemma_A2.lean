-- Prove2me | Theorems.Thm_BosonicResources_lemma_A2
-- name    : BosonicResources.lemma_A2
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T05:59:09.18053+00:00
-- url     : https://prove2.me/theorems/3c805a91-23d4-4df1-aa41-5b468a37b4fe
-- title:
--   Lemma A.2: trace distance between Gaussian states in terms of means and covariances
-- statement:
--   Here $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix (quadratures ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$, vacuum covariance $\tfrac12 I$), and $D_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$ is the trace distance.
--
--   For any two $n$-mode Gaussian states $\rho_1=\rho(\mu_1,\Sigma_1)$ and $\rho_2=\rho(\mu_2,\Sigma_2)$,
--
--   $$
--   D_{\mathrm{tr}}(\rho_1,\rho_2)\ \le\ \frac{1}{\sqrt2}\,\big\|\Sigma_1^{-1/2}(\mu_2-\mu_1)\big\|_2+\frac{1+\sqrt3}{8}\operatorname{Tr}\!\Big(\big(\Sigma_1^{-1}+\Sigma_2^{-1}\big)\,\lvert\Sigma_1-\Sigma_2\rvert\Big),
--   $$
--
--   where $\|\cdot\|_2$ is the Euclidean norm on $\mathbb R^{2n}$ and $\lvert X\rvert=\sqrt{X^{T}X}$ is the matrix absolute value.
--
--   This is a known perturbation bound, quoted from [BMEM25, Theorem 8]: closeness of the means and of the covariance matrices implies closeness of the Gaussian states in trace distance. It is the tool by which estimates of $\mu$ and $\Sigma$ are converted into a trace-distance guarantee for the estimated Gaussian state.
--
--   **Formalization Note** $\|\Sigma_1^{-1/2}v\|_2$ is written as $\sqrt{v^{T}\Sigma_1^{-1}v}$. $\lvert X\rvert=\sqrt{X^{T}X}$ is the positive semidefinite square root (`CFC.sqrt`) of $(\Sigma_1-\Sigma_2)^{T}(\Sigma_1-\Sigma_2)$. Covariances are in the paper's convention (vacuum $\tfrac12 I$), which is the origin of the factor $1/\sqrt2$ in the first term relative to [BMEM25]. The special case of equal means and $\Sigma_2\succeq\Sigma_1$ is the published statement `BosonicLearn.bmem25_theorem_8_cov`. The trace distance takes values in $[0,\infty]$ and the real right-hand side is embedded with `ENNReal.ofReal`; no lower bound on $n$ is assumed.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, App. A.1, Lemma A.2, Eq. (S11); quoting [BMEM25, Theorem 8] (Bittel, Mele, Eisert, Mele, Energy-independent tomography of Gaussian states, 2025)

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix MatrixOrder

namespace BosonicResources

/-- **Lemma A.2 (Trace distance between Gaussian states in terms of means and covariances).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Lemma A.2, Eq. (S11) (App. A.1), quoting [BMEM25, Theorem 8] (Bittel, Mele, Eisert, Mele,
*Energy-independent tomography of Gaussian states*, 2025): "For any two Gaussian states ρ(µ₁,Σ₁) and ρ(µ₂,Σ₂), it
holds that D_tr(ρ(µ₁,Σ₁), ρ(µ₂,Σ₂)) ≤ (1/√2) ‖Σ₁^{-1/2}(µ₂−µ₁)‖₂ + ((1+√3)/8) Tr((Σ₁⁻¹+Σ₂⁻¹)|Σ₁−Σ₂|). Note that the
additional factor of 1/√2 in the first term is due to our different convention of covariance matrices from
[BMEM25]."

For Gaussian states `ρ₁ = ρ(µ₁, Σ₁)`, `ρ₂ = ρ(µ₂, Σ₂)` on `n` modes,
`D_tr(ρ₁, ρ₂) ≤ (1/√2) √((µ₂ − µ₁)ᵀ Σ₁⁻¹ (µ₂ − µ₁)) + ((1 + √3)/8) Tr((Σ₁⁻¹ + Σ₂⁻¹) |Σ₁ − Σ₂|)`.

**Formalization Note.** `‖Σ₁^{-1/2} v‖₂ = √(vᵀ Σ₁⁻¹ v)`. `|X| = √(XᵀX)` is the matrix absolute value, the positive
semidefinite square root (`CFC.sqrt`) of `(Σ₁−Σ₂)ᵀ(Σ₁−Σ₂)`. Covariances are in the paper's convention (vacuum `½I`).
The special case of equal means and `Σ₂ ⪰ Σ₁` is the published statement `BosonicLearn.bmem25_theorem_8_cov`. -/
theorem lemma_A2 {n : ℕ} (ρ₁ ρ₂ : State (Occupation (Fin n))) (μ₁ μ₂ : Fin n ⊕ Fin n → ℝ)
    (S₁ S₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (h₁ : IsGaussianState ρ₁ μ₁ S₁) (h₂ : IsGaussianState ρ₂ μ₂ S₂) :
    traceDist ρ₁.coefficients ρ₂.coefficients ≤
      ENNReal.ofReal (1 / Real.sqrt 2 * Real.sqrt ((μ₂ - μ₁) ⬝ᵥ (S₁⁻¹ *ᵥ (μ₂ - μ₁))) +
        (1 + Real.sqrt 3) / 8 *
          ((S₁⁻¹ + S₂⁻¹) * CFC.sqrt ((S₁ - S₂)ᵀ * (S₁ - S₂))).trace) := by sorry

end BosonicResources
