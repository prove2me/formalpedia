-- Prove2me | Theorems.Thm_BoundEntGauss_minimallyPPT_separable_iff_blockDiagonal
-- name    : BoundEntGauss.minimallyPPT_separable_iff_blockDiagonal
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:51:35.862309+00:00
-- url     : https://prove2.me/theorems/49fac5f1-b069-4374-be65-66d183155c5a
-- title:
--   Note after Definition 1 — a minimally ppt $\gamma$ is separable iff it is a direct sum, iff the state factorizes
-- statement:
--   Let $\gamma=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$ be a minimally ppt covariance of an $n\times m$-mode system (Definition 1). Then $\gamma$ is **separable**, in the sense that there are covariance matrices $\gamma_A$, $\gamma_B$ with
--
--   $$
--   \gamma\ge\gamma_A\oplus\gamma_B ,
--   $$
--
--   if and only if $\gamma$ is a direct sum, i.e. its cross block vanishes: $C=0$. Moreover, for every Gaussian state $\rho$ with covariance $\gamma$ (any mean), $C=0$ if and only if $\rho$ factorizes: $\rho=\rho_A\otimes\rho_B$ for density operators $\rho_A$, $\rho_B$.
--
--   By Proposition 1, the left-hand condition is separability of the Gaussian states with covariance $\gamma$; so a minimally ppt Gaussian state is separable exactly when it factorizes. Combined with Proposition 3, this is how the paper certifies entanglement of the family (11): a minimally ppt covariance that is not block diagonal is entangled.
--
--   Differences from the source:
--   - reading: "a minimally ppt matrix γ is separable" → ∃ γ_A γ_B covariance matrices with γ ≥ γ_A ⊕ γ_B (condition (4)); reason: the paper applies "separable" to a covariance matrix through Proposition 1, which makes (4) equivalent to separability of the Gaussian state
--   - encoding: "it is a direct sum" → the cross block g.C is zero; reason: the assembled matrix is [[A, C], [Cᵀ, B]]; it is a direct sum exactly when C = 0
--   - reading: "covariance matrices γ_A and γ_B" → IsCM: real symmetric with γ_A − iσ_A ≥ 0; reason: the conditions the paper uses for γ_A, γ_B on p. 3 ("γ_A ± iσ_A ≥ 0"); equivalent to γ_A + iσ_A ≥ 0 by conjugation
--   - encoding: "the corresponding state factorizes" → for every ρ with HasGaussianCovariance ρ g d, ρ.coefficients ∈ productStates; reason: the state corresponding to γ is a Gaussian state with covariance γ, and its mean plays no role; productStates is the set of products ρ_A ⊗ ρ_B of density operators
--   - reading: Gaussian state: tr[ρW(ξ)] = exp(imᵀξ − ¼ξᵀγξ), Eq. (3), with W(ξ) = exp(iξ·σ·R) → HasGaussianCovariance: characteristic function exp(−¼ξᵀσᵀγσξ + iξᵀσd) on actual Fock-space densities, every mean d; reason: as printed, (3) is consistent with W(ξ) = exp(iξ·σ·R) only if σγσᵀ = γ; the paper states that γ and m are the covariance and mean of ρ, which the Lean form makes true
--   - encoding: f canonical degrees of freedom, X = X_A ⊕ X_B, canonical coordinates → QuadratureIndex n ⊕ QuadratureIndex m (interleaved (x_j, p_j), Alice = Sum.inl), Fock space indexed by Occupation (Fin n) × Occupation (Fin m), for all n, m; reason: Lean representation of the same objects
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section II, p. 3 (unnumbered, note after Definition 1)

import Mathlib
import Definitions.Def_BoundEntGauss_IsMinimallyPPT

open QAlgorithms.Papers.Independent.Dependency50.P33 (State productStates)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Intakenext100.P68 (CovarianceBlocks HasGaussianCovariance IsCM DominatesLocalCovariances)

namespace BoundEntGauss

/-- **A minimally ppt covariance is separable iff it is block diagonal, iff the state factorizes.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section II, p. 3 (unnumbered, after Definition 1): "Note that a minimally ppt matrix γ is
separable if and only if it is a direct sum, i.e., if the corresponding state factorizes."

For every minimally ppt `γ = [[A, C], [Cᵀ, B]]` of an `n × m`-mode system:

1. there are covariance matrices `γ_A`, `γ_B` with `γ ≥ γ_A ⊕ γ_B` (the separability condition
   (4) of Proposition 1) if and only if the cross block `C` vanishes, i.e. `γ = A ⊕ B`;
2. for every Gaussian state `ρ` with covariance `γ` (and any mean), `C` vanishes if and only if
   `ρ` is a product `ρ_A ⊗ ρ_B` of density operators.

**Formalization Note.** Reading: "`γ` is separable" for a covariance matrix is condition (4),
`∃ γ_A γ_B, IsCM γ_A ∧ IsCM γ_B ∧ γ ≥ γ_A ⊕ γ_B`, which by Proposition 1 is separability of the
Gaussian state with covariance `γ`. "Direct sum" is `g.C = 0`. "The corresponding state" is any
Gaussian state with covariance `γ`, and "factorizes" is membership in the published
`Dependency50.P33.productStates`. -/
theorem minimallyPPT_separable_iff_blockDiagonal {n m : ℕ} (g : CovarianceBlocks n m)
    (hg : IsMinimallyPPT g) :
    ((∃ (γA : Cov n) (γB : Cov m), IsCM γA ∧ IsCM γB ∧ DominatesLocalCovariances g γA γB) ↔
      g.C = 0) ∧
    ∀ (ρ : State (Occupation (Fin n) × Occupation (Fin m)))
        (d : QuadratureIndex n ⊕ QuadratureIndex m → ℝ),
        HasGaussianCovariance ρ g d →
        (g.C = 0 ↔ ρ.coefficients ∈ productStates (Occupation (Fin n)) (Occupation (Fin m))) := by sorry

end BoundEntGauss
