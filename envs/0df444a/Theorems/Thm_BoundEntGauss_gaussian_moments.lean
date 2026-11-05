-- Prove2me | Theorems.Thm_BoundEntGauss_gaussian_moments
-- name    : BoundEntGauss.gaussian_moments
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:27.307348+00:00
-- url     : https://prove2.me/theorems/9e746f04-cfd5-4cac-a92d-b7cb59100a4e
-- title:
--   Section II, Eq. (3) — the coefficients of a Gaussian characteristic function are its covariance and mean
-- statement:
--   Let $\rho$ be a Gaussian state of $n\times m$ modes with covariance $\gamma$ and mean $d$, i.e. its characteristic function is (3) with coefficients $\gamma$ and $d$. Then $\rho$ has finite second moments, its mean is
--
--   $$
--   \operatorname{tr}(\rho R_\alpha)=d_\alpha ,
--   $$
--
--   and its covariance matrix (2) is $\gamma$.
--
--   This is the paper's statement that "the coefficients were chosen such that $\gamma$ and $m$ are indeed covariance and mean of $\rho$". It lets Propositions 1 and 2, whose first halves concern arbitrary states with finite second moments, be applied to Gaussian states.
--
--   Differences from the source:
--   - reading: Gaussian state: tr[ρW(ξ)] = exp(imᵀξ − ¼ξᵀγξ), Eq. (3), with W(ξ) = exp(iξ·σ·R) → HasGaussianCovariance: characteristic function exp(−¼ξᵀσᵀγσξ + iξᵀσd) on actual Fock-space densities, every mean d; reason: as printed, (3) is consistent with W(ξ) = exp(iξ·σ·R) only if σγσᵀ = γ; the paper states that γ and m are the covariance and mean of ρ, which the Lean form makes true
--   - reading: "a state with finite second moments" with covariance γ (Eq. (2)) → HasCovarianceBlocks: finite mean photon number, mean and covariance given by the first two derivatives of t ↦ tr ρW(tξ), γ symmetric; reason: finite photon number is equivalent to finite second moments for finitely many modes; the derivatives are the mean and second moment of ξ·σ·R
--   - encoding: f canonical degrees of freedom, X = X_A ⊕ X_B, canonical coordinates → QuadratureIndex n ⊕ QuadratureIndex m (interleaved (x_j, p_j), Alice = Sum.inl), Fock space indexed by Occupation (Fin n) × Occupation (Fin m), for all n, m; reason: Lean representation of the same objects
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section II, Eq. (3), p. 2

import Mathlib
import Definitions.Def_BoundEntGauss_HasCovarianceBlocks

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Intakenext100.P68 (CovarianceBlocks HasGaussianCovariance)

namespace BoundEntGauss

/-- **The coefficients of a Gaussian characteristic function are its covariance and mean.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section II, p. 2 (unnumbered, after Eq. (3)): "Here the coefficients were chosen such that γ
and m are indeed covariance and mean of ρ, as is readily verified by differentiation."

If `ρ` is the Gaussian state with covariance `γ` and mean `d` (its characteristic function is
(3)), then `ρ` has finite second moments, its mean is `d` and its covariance matrix (2) is `γ`.

**Formalization Note.** "Finite second moments with mean `d` and covariance `γ`" is
`HasCovarianceBlocks` (finite mean photon number plus the Weyl-derivative form of the first and
second moments). Finite photon number is part of the conclusion: it does not follow from the
characteristic function identity by definition. -/
theorem gaussian_moments {n m : ℕ} (g : CovarianceBlocks n m)
    (ρ : State (Occupation (Fin n) × Occupation (Fin m)))
    (d : QuadratureIndex n ⊕ QuadratureIndex m → ℝ) (h : HasGaussianCovariance ρ g d) :
    HasCovarianceBlocks ρ g d := by sorry

end BoundEntGauss
