-- Prove2me | Theorems.Thm_BoundEntGauss_proposition_1
-- name    : BoundEntGauss.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:23.921425+00:00
-- url     : https://prove2.me/theorems/52b106b4-49a8-4434-92ae-3cdb0f1156cc
-- title:
--   Proposition 1 — separable states satisfy $\gamma\ge\gamma_A\oplus\gamma_B$; conversely for Gaussian states
-- statement:
--   Consider $n$ modes on Alice's side and $m$ on Bob's side, and a real symmetric $\gamma=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$.
--
--   1. If $\gamma$ is the covariance matrix of a separable state $\rho$ with finite second moments (any mean), then there are covariance matrices $\gamma_A$ of Alice and $\gamma_B$ of Bob such that
--   $$
--   \gamma\ \ge\ \begin{pmatrix}\gamma_A&0\\0&\gamma_B\end{pmatrix}. \tag{4}
--   $$
--   2. Conversely, if such $\gamma_A$, $\gamma_B$ exist, then every Gaussian state with covariance $\gamma$ (any mean) is separable.
--
--   Here a covariance matrix $\gamma_A$ is real symmetric with $\gamma_A-i\sigma_A\ge0$, and $\ge$ is the order of positive semidefinite matrices. Proposition 1 turns separability of Gaussian states into a condition on covariance matrices; together with Definition 1 it reduces the goal to linear algebra.
--
--   Differences from the source:
--   - reading: "separable" (no definition in the paper) → trace-norm closed convex hull of product states (Holevo–Shirokov–Werner, published IsSeparable); reason: the standard definition for infinite-dimensional systems; it contains every finite, countable and integral mixture of product states
--   - reading: "a state with finite second moments" with covariance γ (Eq. (2)) → HasCovarianceBlocks: finite mean photon number, mean and covariance given by the first two derivatives of t ↦ tr ρW(tξ), γ symmetric; reason: finite photon number is equivalent to finite second moments for finitely many modes; the derivatives are the mean and second moment of ξ·σ·R
--   - reading: "covariance matrices γ_A and γ_B" → IsCM: real symmetric with γ_A − iσ_A ≥ 0; reason: the conditions the paper uses for γ_A, γ_B on p. 3 ("γ_A ± iσ_A ≥ 0"); equivalent to γ_A + iσ_A ≥ 0 by conjugation
--   - reading: Gaussian state: tr[ρW(ξ)] = exp(imᵀξ − ¼ξᵀγξ), Eq. (3), with W(ξ) = exp(iξ·σ·R) → HasGaussianCovariance: characteristic function exp(−¼ξᵀσᵀγσξ + iξᵀσd) on actual Fock-space densities, every mean d; reason: as printed, (3) is consistent with W(ξ) = exp(iξ·σ·R) only if σγσᵀ = γ; the paper states that γ and m are the covariance and mean of ρ, which the Lean form makes true
--   - encoding: f canonical degrees of freedom, X = X_A ⊕ X_B, canonical coordinates → QuadratureIndex n ⊕ QuadratureIndex m (interleaved (x_j, p_j), Alice = Sum.inl), Fock space indexed by Occupation (Fin n) × Occupation (Fin m), for all n, m; reason: Lean representation of the same objects
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Proposition 1, Eq. (4), p. 2

import Mathlib
import Definitions.Def_BoundEntGauss_HasCovarianceBlocks

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsSeparable)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Intakenext100.P68 (CovarianceBlocks HasGaussianCovariance IsCM DominatesLocalCovariances)

namespace BoundEntGauss

/-- **Proposition 1 (separability and local covariances).**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Proposition 1, Eq. (4), p. 2.

1. Let `γ` be the covariance matrix of a separable state with finite second moments. Then there are
   covariance matrices `γ_A`, `γ_B` with `γ ≥ γ_A ⊕ γ_B`.
2. Conversely, if such `γ_A`, `γ_B` exist, the Gaussian state with covariance `γ` is separable.

**Formalization Note.** Separability is the published trace-norm closed convex hull of product
states (`Dependency50.P33.IsSeparable`), with Alice the first tensor factor. "Covariance matrix
`γ_A`" is `IsCM` (real symmetric, `γ_A − iσ_A ≥ 0`), and `γ ≥ γ_A ⊕ γ_B` is
`DominatesLocalCovariances` (positive semidefinite difference). Part 1 holds for every state with
finite second moments, Gaussian or not; part 2 for every Gaussian state with covariance `γ`, for
every mean. -/
theorem proposition_1 {n m : ℕ} :
    (∀ (g : CovarianceBlocks n m) (ρ : State (Occupation (Fin n) × Occupation (Fin m)))
        (d : QuadratureIndex n ⊕ QuadratureIndex m → ℝ),
        HasCovarianceBlocks ρ g d → IsSeparable ρ.coefficients →
        ∃ (γA : Cov n) (γB : Cov m), IsCM γA ∧ IsCM γB ∧ DominatesLocalCovariances g γA γB) ∧
    (∀ (g : CovarianceBlocks n m) (ρ : State (Occupation (Fin n) × Occupation (Fin m)))
        (d : QuadratureIndex n ⊕ QuadratureIndex m → ℝ),
        HasGaussianCovariance ρ g d →
        (∃ (γA : Cov n) (γB : Cov m), IsCM γA ∧ IsCM γB ∧ DominatesLocalCovariances g γA γB) →
        IsSeparable ρ.coefficients) := by sorry

end BoundEntGauss
