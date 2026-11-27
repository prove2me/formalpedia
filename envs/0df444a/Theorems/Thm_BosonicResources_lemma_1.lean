-- Prove2me | Theorems.Thm_BosonicResources_lemma_1
-- name    : BosonicResources.lemma_1
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:24:58.480399+00:00
-- url     : https://prove2.me/theorems/5a69e8af-6f6b-5333-830b-9a3d484da876
-- title:
--   Lemma 1: trace distance versus Wigner TV distance for Gaussian states
-- statement:
--   Throughout, $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix; quadratures are ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$ and the vacuum has covariance $\tfrac12 I$. The Wigner distribution of $\rho(\mu,\Sigma)$ is $W_{\rho(\mu,\Sigma)}=\mathcal N(\mu,\Sigma)$, the Gaussian probability measure on $\mathbb R^{2n}$ with mean $\mu$ and covariance $\Sigma$. Let $D_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$ be the trace distance and $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ the total variation distance of probability measures. A state is pure if it is a rank-one projector.
--
--   There exist absolute constants $c_0,c_1,c_2,c_3>0$ such that the following holds for every $n\ge1$. Let $\rho_1=\rho(\mu_1,\Sigma_1)$ and $\rho_2=\rho(\mu_2,\Sigma_2)$ be $n$-mode Gaussian states with $D_{\mathrm{tr}}(\rho_1,\rho_2)\le c_0$. Then
--
--   $$
--   c_1\,\mathrm{TV}(W_{\rho_1},W_{\rho_2})\ \le\ D_{\mathrm{tr}}(\rho_1,\rho_2)\ \le\ c_2\sqrt n\;\mathrm{TV}(W_{\rho_1},W_{\rho_2}).
--   $$
--
--   If, in addition, both $\rho_1$ and $\rho_2$ are pure, then
--
--   $$
--   D_{\mathrm{tr}}(\rho_1,\rho_2)\ \le\ c_3\,\mathrm{TV}(W_{\rho_1},W_{\rho_2}).
--   $$
--
--   The lemma relates the two notions of accuracy used in the paper, trace distance of states and total variation distance of their Wigner distributions. The possible factor $\sqrt n$ between them is the reason why learning a Gaussian state in trace distance is not the same task as learning a classical Gaussian distribution, and its absence for pure states is what the paper uses to learn pure Gaussian states with Gaussian measurements (Theorem 5).
--
--   **Formalization Note** The constants are required to be strictly positive: with the printed "$\ge0$" the statement would hold trivially ($c_0=c_1=0$). The pure-state inequality is asserted under the same hypothesis $D_{\mathrm{tr}}(\rho_1,\rho_2)\le c_0$. The Wigner distribution of $\rho(\mu,\Sigma)$ is the Gaussian measure $\mathcal N(\mu,\Sigma)$ (Sec. 2). $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ over measurable sets is the published `MarkovChainCLT.tvDist`, which for probability measures equals the paper's $\tfrac12\int\lvert p-q\rvert$. The sharpness sentence of the lemma is the separate statement `lemma_1_sharp`; explicit constants are in `lemma_B1`, `lemma_B2`, `lemma_B3`.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 3.1, Lemma 1, Eqs. (2)–(3); App. B.1, Theorem S1

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

/-- **Lemma 1 (Bounds between trace distance and Wigner TV distance for Gaussian states).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Lemma 1, Eqs. (2)–(3) (= Theorem S1, App. B.1): "There exist absolute constants c₀, c₁, c₂, c₃ ≥ 0 such that the
following holds: For any n ∈ ℕ₊, let ρ₁ and ρ₂ be any n-mode Gaussian states such that D_tr(ρ₁,ρ₂) ≤ c₀. Then,
c₁ TV(W_ρ₁, W_ρ₂) ≤ D_tr(ρ₁,ρ₂) ≤ c₂ √n TV(W_ρ₁, W_ρ₂). Furthermore, when both ρ₁ and ρ₂ are pure,
D_tr(ρ₁,ρ₂) ≤ c₃ TV(W_ρ₁, W_ρ₂)."

There are absolute constants `c₀, c₁, c₂, c₃ > 0` such that for every `n ≥ 1` and all `n`-mode Gaussian states
`ρ₁ = ρ(µ₁, Σ₁)`, `ρ₂ = ρ(µ₂, Σ₂)` with `D_tr(ρ₁, ρ₂) ≤ c₀`, writing `TV = TV(N(µ₁, Σ₁), N(µ₂, Σ₂))`:
`c₁ · TV ≤ D_tr(ρ₁, ρ₂) ≤ c₂ √n · TV`, and if both states are pure, `D_tr(ρ₁, ρ₂) ≤ c₃ · TV`.

**Formalization Note.** The constants are required to be strictly positive: with the printed "≥ 0" the statement
would hold trivially (`c₀ = c₁ = 0`). The Wigner distribution of `ρ(µ, Σ)` is the Gaussian measure `N(µ, Σ)` (§2). `TV(P, Q) = sup_A |P(A) − Q(A)|` over measurable sets (the published
`MarkovChainCLT.tvDist`), which for probability measures equals the paper's `½ ∫ |p − q|`.
The sharpness sentence of the lemma is the separate statement `lemma_1_sharp`; explicit constants are in
`lemma_B1`, `lemma_B2`, `lemma_B3`. -/
theorem lemma_1 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ c₃ : ℝ, 0 < c₃ ∧
      ∀ n : ℕ, 1 ≤ n → ∀ (ρ₁ ρ₂ : State (Occupation (Fin n))) (μ₁ μ₂ : Fin n ⊕ Fin n → ℝ)
          (S₁ S₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
        IsGaussianState ρ₁ μ₁ S₁ → IsGaussianState ρ₂ μ₂ S₂ →
        traceDist ρ₁.coefficients ρ₂.coefficients ≤ ENNReal.ofReal c₀ →
        (ENNReal.ofReal (c₁ * tvDist (multivariateGaussian (WithLp.toLp 2 μ₁) S₁)
              (multivariateGaussian (WithLp.toLp 2 μ₂) S₂)) ≤
            traceDist ρ₁.coefficients ρ₂.coefficients ∧
          traceDist ρ₁.coefficients ρ₂.coefficients ≤
            ENNReal.ofReal (c₂ * Real.sqrt n * tvDist (multivariateGaussian (WithLp.toLp 2 μ₁) S₁)
              (multivariateGaussian (WithLp.toLp 2 μ₂) S₂))) ∧
        (IsPure ρ₁ → IsPure ρ₂ →
          traceDist ρ₁.coefficients ρ₂.coefficients ≤
            ENNReal.ofReal (c₃ * tvDist (multivariateGaussian (WithLp.toLp 2 μ₁) S₁)
              (multivariateGaussian (WithLp.toLp 2 μ₂) S₂))) := by sorry

end BosonicResources
