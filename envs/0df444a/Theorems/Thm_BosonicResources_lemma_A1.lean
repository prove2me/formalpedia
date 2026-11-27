-- Prove2me | Theorems.Thm_BosonicResources_lemma_A1
-- name    : BosonicResources.lemma_A1
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T05:56:00.016848+00:00
-- url     : https://prove2.me/theorems/7b89fe94-ef04-5a41-8d9b-f54f16c5b461
-- title:
--   Lemma A.1: fidelity between two Gaussian states, one of them pure
-- statement:
--   Here $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix (quadratures ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$, vacuum covariance $\tfrac12 I$). A state is *pure* if it is a rank-one projector.
--
--   Let $\rho_1=\rho(\mu_1,\Sigma_1)$ and $\rho_2=\rho(\mu_2,\Sigma_2)$ be $n$-mode Gaussian states, at least one of which is pure. Then
--
--   $$
--   \operatorname{Tr}(\rho_1\rho_2)=\frac{1}{\sqrt{\det(\Sigma_1+\Sigma_2)}}\exp\!\Big(-\tfrac12(\mu_1-\mu_2)^{T}(\Sigma_1+\Sigma_2)^{-1}(\mu_1-\mu_2)\Big).
--   $$
--
--   The left-hand side is the fidelity $F(\rho_1,\rho_2)$ in the squared convention used throughout the paper. The formula is a known result for bosonic Gaussian states; the paper uses it to evaluate overlaps such as vacuum probabilities of Gaussian states and the fidelity of two pure Gaussian states.
--
--   **Formalization Note** $\operatorname{Tr}(\rho_1\rho_2)$ is the iterated series $\sum_u\sum_v(\rho_1)_{uv}(\rho_2)_{vu}$ in the Fock basis, which converges for density operators. Covariances are in the paper's convention (vacuum $\tfrac12 I$). The right-hand side is a real number, embedded in the complex numbers; no lower bound on $n$ is assumed. Purity is `IsPure` and the hypothesis is the disjunction "$\rho_1$ is pure or $\rho_2$ is pure".
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, App. A.1, Lemma A.1, Eq. (S10); quoting [SWP12] (Spedalieri, Weedbrook, Pirandola, A limit formula for the quantum fidelity, J. Phys. A 46(2):025304, 2012)

import Mathlib
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicResources_IsPure
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Lemma A.1 (Fidelity between two Gaussian states, one of them pure).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Lemma A.1, Eq. (S10) (App. A.1), quoting [SWP12] (Spedalieri, Weedbrook, Pirandola, *A limit formula for the quantum fidelity*, J. Phys. A 46(2):025304, 2012): "For
two n-mode Gaussian states ρ₁ = ρ(µ₁,Σ₁) and ρ₂ = ρ(µ₂,Σ₂), when at least one of them is pure, their fidelity is given
by F(ρ₁,ρ₂) := Tr(ρ₁ρ₂) = (det(Σ₁+Σ₂))^{-1/2} exp(−½ (µ₁−µ₂)ᵀ (Σ₁+Σ₂)⁻¹ (µ₁−µ₂)). Throughout this paper, we use the
squared convention of fidelity."

For Gaussian states `ρ₁ = ρ(µ₁, Σ₁)` and `ρ₂ = ρ(µ₂, Σ₂)` on `n` modes, at least one of which is pure,
`Tr(ρ₁ ρ₂) = (det(Σ₁ + Σ₂))^{-1/2} exp(−½ (µ₁ − µ₂)ᵀ (Σ₁ + Σ₂)⁻¹ (µ₁ − µ₂))`.

**Formalization Note.** `Tr(ρ₁ρ₂)` is the iterated series `∑_u ∑_v (ρ₁)_{uv} (ρ₂)_{vu}` in the Fock basis, which
converges for density operators. Covariances are in the paper's convention (vacuum `½I`). -/
theorem lemma_A1 {n : ℕ} (ρ₁ ρ₂ : State (Occupation (Fin n))) (μ₁ μ₂ : Fin n ⊕ Fin n → ℝ)
    (S₁ S₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (h₁ : IsGaussianState ρ₁ μ₁ S₁) (h₂ : IsGaussianState ρ₂ μ₂ S₂) (hp : IsPure ρ₁ ∨ IsPure ρ₂) :
    ∑' u : Occupation (Fin n), ∑' v : Occupation (Fin n), ρ₁.coefficients u v * ρ₂.coefficients v u =
      ((1 / Real.sqrt (S₁ + S₂).det *
        Real.exp (-(1 / 2) * ((μ₁ - μ₂) ⬝ᵥ ((S₁ + S₂)⁻¹ *ᵥ (μ₁ - μ₂)))) : ℝ) : ℂ) := by sorry

end BosonicResources
