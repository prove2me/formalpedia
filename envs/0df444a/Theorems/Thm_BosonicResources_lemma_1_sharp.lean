-- Prove2me | Theorems.Thm_BosonicResources_lemma_1_sharp
-- name    : BosonicResources.lemma_1_sharp
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:26:16.214881+00:00
-- url     : https://prove2.me/theorems/09a00bfa-a375-40d1-97b9-1e118a33dd2d
-- title:
--   A $\sqrt n$ gap between trace distance and Wigner TV distance: vacuum versus a near-vacuum thermal state
-- statement:
--   Throughout, $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix; quadratures are ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$ and the vacuum has covariance $\tfrac12 I$. The Wigner distribution of $\rho(\mu,\Sigma)$ is $W_{\rho(\mu,\Sigma)}=\mathcal N(\mu,\Sigma)$, the Gaussian probability measure on $\mathbb R^{2n}$ with mean $\mu$ and covariance $\Sigma$; $D_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$ is the trace distance and $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ the total variation distance.
--
--   Let $n\ge1$ and $\varepsilon\in(0,1)$. Let $\rho_0$ be the zero-mean $n$-mode Gaussian state with covariance $\Sigma_0=\tfrac12 I_{2n}$ (the vacuum) and $\rho_1$ the zero-mean $n$-mode Gaussian state with covariance $\Sigma_1=\tfrac12\big(1+\tfrac{\varepsilon}{n}\big)I_{2n}$ (a near-vacuum thermal state). Then:
--
--   1. $\mathrm{TV}(W_{\rho_0},W_{\rho_1})\le\varepsilon/\sqrt n$;
--   2. $D_{\mathrm{tr}}(\rho_0,\rho_1)\ge\varepsilon/4$;
--   3. the trace distance exceeds the Wigner total variation distance by a factor of order $\sqrt n$,
--
--   $$
--   D_{\mathrm{tr}}(\rho_0,\rho_1)\ \ge\ \tfrac14\sqrt n\;\mathrm{TV}(W_{\rho_0},W_{\rho_1}).
--   $$
--
--   This is the example given after Lemma 1 in the paper. It shows that the factor $\sqrt n$ in the upper bound $D_{\mathrm{tr}}\le c_2\sqrt n\,\mathrm{TV}$ of Lemma 1 cannot be improved, so that learning a Gaussian Wigner distribution to total variation distance $\varepsilon$ is in general weaker than learning the state to trace distance $\varepsilon$.
--
--   **Formalization Note** The two states are given through the predicate `IsGaussianState` (any density operators that are the Gaussian states with the stated means and covariances); both exist (vacuum and a thermal state). $\mathrm{TV}(P,Q)=\sup_A\lvert P(A)-Q(A)\rvert$ over measurable sets is the published `MarkovChainCLT.tvDist`, which for probability measures equals the paper's $\tfrac12\int\lvert p-q\rvert$. The three inequalities are asserted together as one conjunction.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 3.1 (example after Lemma 1)

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

/-- **Sharpness example for Lemma 1: vacuum versus a near-vacuum thermal state.**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, §3.1 (after Lemma 1): "Fix any ε ∈ (0,1). Let Σ₀ = ½ I_{2n} and Σ₁ = ½ (1 + ε/n) I_{2n} be the covariance
matrices of two zero-mean Gaussian states ρ₀ and ρ₁, respectively. … The TV distance between their Wigner
distributions can be upper bounded by TV(W_ρ₀, W_ρ₁) ≤ … = ε n^{-1/2}; In contrast, the trace distance satisfy
D_tr(ρ₀,ρ₁) ≥ ε/4. … In conclusion, D_tr(ρ₀,ρ₁) ≥ ¼ √n · TV(W_ρ₀, W_ρ₁)".

For every `n ≥ 1` and `ε ∈ (0, 1)`, if `ρ₀` is the zero-mean Gaussian state with covariance `½ I` (the vacuum) and `ρ₁`
the zero-mean Gaussian state with covariance `½ (1 + ε/n) I`, then
1. `TV(N(0, ½I), N(0, ½(1 + ε/n) I)) ≤ ε/√n`;
2. `D_tr(ρ₀, ρ₁) ≥ ε/4`;
3. `D_tr(ρ₀, ρ₁) ≥ ¼ √n · TV(N(0, ½I), N(0, ½(1 + ε/n) I))`.

**Formalization Note.** The two states are given through `IsGaussianState`; both exist (vacuum and a thermal
state). `TV(P, Q) = sup_A |P(A) − Q(A)|` over measurable sets (the published
`MarkovChainCLT.tvDist`), which for probability measures equals the paper's `½ ∫ |p − q|`. -/
theorem lemma_1_sharp {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (ρ₀ ρ₁ : State (Occupation (Fin n)))
    (h₀ : IsGaussianState ρ₀ 0 ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)))
    (h₁ : IsGaussianState ρ₁ 0
      ((1 / 2 * (1 + ε / n) : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))) :
    tvDist (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n ⊕ Fin n))
          ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)))
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n ⊕ Fin n))
          ((1 / 2 * (1 + ε / n) : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))) ≤ ε / Real.sqrt n ∧
      ENNReal.ofReal (ε / 4) ≤ traceDist ρ₀.coefficients ρ₁.coefficients ∧
      ENNReal.ofReal (1 / 4 * Real.sqrt n *
          tvDist (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n ⊕ Fin n))
              ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)))
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n ⊕ Fin n))
              ((1 / 2 * (1 + ε / n) : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)))) ≤
        traceDist ρ₀.coefficients ρ₁.coefficients := by sorry

end BosonicResources
