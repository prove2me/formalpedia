-- Prove2me | Theorems.Thm_BosonicLearn_lemma_18
-- name    : BosonicLearn.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:33:00.32419+00:00
-- url     : https://prove2.me/theorems/96b4f76a-d3ad-4681-9653-a60d479c4406
-- title:
--   Lemma 18 — first-moment perturbation $\tfrac12\|\rho(\mu',\Sigma)-\rho(\mu,\Sigma)\|_1\le\tfrac12\|\Sigma^{-1/2}(\mu'-\mu)\|_2$
-- statement:
--   For every valid covariance matrix $\Sigma$ and all $\mu,\mu'\in\mathbb R^{2n}$,
--
--   $$\tfrac12\big\|\rho(\mu',\Sigma)-\rho(\mu,\Sigma)\big\|_1\le\tfrac12\big\|\Sigma^{-1/2}(\mu'-\mu)\big\|_2 .$$
--
--   It controls the error caused by the estimated mean in heterodyne tomography.
--
--   Differences from the source:
--   - encoding: ‖Σ^{-1/2}(µ′ − µ)‖₂ → √((µ′ − µ)ᵀ Σ⁻¹ (µ′ − µ)); reason: equal; a valid covariance matrix is positive definite
--   - encoding: a valid covariance matrix Σ and the states ρ(µ, Σ), ρ(µ′, Σ) → two states with IsGaussianState for (µ, Σ) and (µ′, Σ); reason: valid covariance matrices are exactly those of Gaussian states
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 18, Eq. (204), p. 60

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Lemma 18 (First-moment perturbation).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 18, Eq. (204), p. 60: "For every valid covariance matrix Σ and all µ, µ′ ∈ ℝ^{2n},
½‖ρ(µ′, Σ) − ρ(µ, Σ)‖₁ ≤ ½‖Σ^{−1/2}(µ′ − µ)‖₂."

For Gaussian states `ρ(µ, Σ)` and `ρ(µ′, Σ)` with the same covariance,
`½‖ρ(µ′, Σ) − ρ(µ, Σ)‖₁ ≤ ½ √((µ′ − µ)ᵀ Σ⁻¹ (µ′ − µ))`.

**Formalization Note.** `‖Σ^{−1/2}v‖₂ = √(vᵀΣ⁻¹v)`; a valid covariance matrix (`Σ + iΩ/2 ⪰ 0`) is positive
definite, so `Σ⁻¹` is the true inverse. -/
theorem lemma_18 {n : ℕ} (ρ ρ' : State (Occupation (Fin n))) (μ μ' : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (h : IsGaussianState ρ μ S) (h' : IsGaussianState ρ' μ' S) :
    traceDist ρ'.coefficients ρ.coefficients ≤
      ENNReal.ofReal (1 / 2 * Real.sqrt ((μ' - μ) ⬝ᵥ (S⁻¹ *ᵥ (μ' - μ)))) := by sorry

end BosonicLearn
