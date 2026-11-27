-- Prove2me | Theorems.Thm_BosonicResources_lemma_B3
-- name    : BosonicResources.lemma_B3
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:21:28.77315+00:00
-- url     : https://prove2.me/theorems/13793d06-5e27-59b5-af46-5a6b3178742e
-- title:
--   Lemma B.3: for pure Gaussian states, $D_{\mathrm{tr}}\le150\,\mathrm{TV}$ of the Wigner distributions
-- statement:
--   Here $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix (quadratures ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$, vacuum covariance $\tfrac12 I$). A state is *pure* if it is a rank-one projector. Further, $\mathcal N(\mu,\Sigma)$ is the Gaussian probability measure on $\mathbb R^{2n}$ with mean $\mu$ and covariance $\Sigma$ (the Wigner distribution of $\rho(\mu,\Sigma)$), $D_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$ is the trace distance and $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ (supremum over measurable sets) is the total variation distance.
--
--   Let $\rho(\mu_1,\Sigma_1)$ and $\rho(\mu_2,\Sigma_2)$ be two pure $n$-mode Gaussian states such that $\mathrm{TV}\big(\mathcal N(\mu_1,\Sigma_1),\mathcal N(\mu_2,\Sigma_2)\big)<\tfrac1{600}$. Then
--
--   $$
--   D_{\mathrm{tr}}\big(\rho(\mu_1,\Sigma_1),\rho(\mu_2,\Sigma_2)\big)\ \le\ 150\cdot\mathrm{TV}\big(\mathcal N(\mu_1,\Sigma_1),\mathcal N(\mu_2,\Sigma_2)\big).
--   $$
--
--   This is the third inequality of Lemma 1 (Theorem S1) with an explicit constant: for pure Gaussian states the factor $\sqrt n$ of Lemma B.2 disappears. It is the reason why learning the Wigner distribution of a pure Gaussian state in total variation distance suffices for learning the state in trace distance (Theorem 5).
--
--   **Formalization Note** The inequality is stated as $\le$: the printed strict $<$ fails when the two states coincide (both sides are $0$). $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ over measurable sets is the published `MarkovChainCLT.tvDist`, which for probability measures equals the paper's $\tfrac12\int\lvert p-q\rvert$. The hypothesis $\mathrm{TV}<1/600$ is strict, as printed; purity is `IsPure`, and no lower bound on $n$ is assumed.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, App. B.1, Lemma B.3, Eq. (S33)

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicResources_IsPure
import Definitions.Def_TotalVariationDist
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open MarkovChainCLT (tvDist)
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Lemma B.3 (For pure Gaussian states the trace distance is at most a constant times the Wigner TV distance).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Lemma B.3, Eq. (S33) (App. B.1): "For any two n-mode pure Gaussian states ρ(µ₁,Σ₁) and ρ(µ₂,Σ₂),
D_tr(ρ(µ₁,Σ₁), ρ(µ₂,Σ₂)) < 150 · TV(N(µ₁,Σ₁), N(µ₂,Σ₂)), given that TV(N(µ₁,Σ₁), N(µ₂,Σ₂)) < 1/600."

For pure Gaussian states `ρ₁ = ρ(µ₁, Σ₁)` and `ρ₂ = ρ(µ₂, Σ₂)` on `n` modes with
`TV(N(µ₁, Σ₁), N(µ₂, Σ₂)) < 1/600`, `D_tr(ρ₁, ρ₂) ≤ 150 · TV(N(µ₁, Σ₁), N(µ₂, Σ₂))`.

**Formalization Note.** The inequality is stated as `≤`: the printed strict `<` fails when the two states coincide
(both sides are `0`). `TV(P, Q) = sup_A |P(A) − Q(A)|` over measurable sets (the published
`MarkovChainCLT.tvDist`), which for probability measures equals the paper's `½ ∫ |p − q|`. -/
theorem lemma_B3 {n : ℕ} (ρ₁ ρ₂ : State (Occupation (Fin n))) (μ₁ μ₂ : Fin n ⊕ Fin n → ℝ)
    (S₁ S₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (h₁ : IsGaussianState ρ₁ μ₁ S₁) (h₂ : IsGaussianState ρ₂ μ₂ S₂)
    (hp₁ : IsPure ρ₁) (hp₂ : IsPure ρ₂)
    (hsmall : tvDist (multivariateGaussian (WithLp.toLp 2 μ₁) S₁)
        (multivariateGaussian (WithLp.toLp 2 μ₂) S₂) < 1 / 600) :
    traceDist ρ₁.coefficients ρ₂.coefficients ≤
      ENNReal.ofReal (150 * tvDist (multivariateGaussian (WithLp.toLp 2 μ₁) S₁)
        (multivariateGaussian (WithLp.toLp 2 μ₂) S₂)) := by sorry

end BosonicResources
