-- Prove2me | Theorems.Thm_BoundEntGauss_proposition_2
-- name    : BoundEntGauss.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:42.593192+00:00
-- url     : https://prove2.me/theorems/60cd5496-22b4-4f61-a647-4c7c93f7b128
-- title:
--   Proposition 2 — ppt states satisfy $\gamma+i\tilde\sigma\ge0$; conversely for Gaussian states
-- statement:
--   Consider an $n\times m$-mode bipartite system and a real symmetric covariance matrix $\gamma$. Let $\tilde\sigma=(-\sigma_A)\oplus\sigma_B$.
--
--   1. If $\gamma$ is the covariance matrix of a state with finite second moments (any mean) that has positive partial transpose, then
--   $$
--   \gamma+i\tilde\sigma\ge0. \tag{7}
--   $$
--   2. Conversely, if $\gamma+i\tilde\sigma\ge0$, then every Gaussian state with covariance $\gamma$ (any mean) has positive partial transpose.
--
--   The partial transpose reverses Alice's momenta, so for a ppt state the covariance of $\rho^{T_A}$ must itself satisfy the uncertainty relation, which is (7). For Gaussian states the condition is also sufficient.
--
--   Differences from the source:
--   - reading: "has positive partial transpose" → IsPPTState: the Fock-basis partial transpose on Alice's factor is a density operator (trace class, positive, trace one); reason: the paper's own phrasing "the partial transpose of ρ is again a density operator" (p. 3)
--   - reading: "a state with finite second moments" with covariance γ (Eq. (2)) → HasCovarianceBlocks: finite mean photon number, mean and covariance given by the first two derivatives of t ↦ tr ρW(tξ), γ symmetric; reason: finite photon number is equivalent to finite second moments for finitely many modes; the derivatives are the mean and second moment of ξ·σ·R
--   - reading: Gaussian state: tr[ρW(ξ)] = exp(imᵀξ − ¼ξᵀγξ), Eq. (3), with W(ξ) = exp(iξ·σ·R) → HasGaussianCovariance: characteristic function exp(−¼ξᵀσᵀγσξ + iξᵀσd) on actual Fock-space densities, every mean d; reason: as printed, (3) is consistent with W(ξ) = exp(iξ·σ·R) only if σγσᵀ = γ; the paper states that γ and m are the covariance and mean of ρ, which the Lean form makes true
--   - encoding: f canonical degrees of freedom, X = X_A ⊕ X_B, canonical coordinates → QuadratureIndex n ⊕ QuadratureIndex m (interleaved (x_j, p_j), Alice = Sum.inl), Fock space indexed by Occupation (Fin n) × Occupation (Fin m), for all n, m; reason: Lean representation of the same objects
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Proposition 2, Eq. (7), p. 3

import Mathlib
import Definitions.Def_BoundEntGauss_HasCovarianceBlocks
import Definitions.Def_BoundEntGauss_IsPPTState
import Definitions.Def_BoundEntGauss_sigmaTilde

open scoped ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Intakenext100.P68 (CovarianceBlocks covarianceBlockMatrix HasGaussianCovariance)

namespace BoundEntGauss

/-- **Proposition 2 (positive partial transpose and covariances).**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Proposition 2, Eq. (7), p. 3.

1. Let `γ` be the covariance matrix of a state with finite second moments which has positive
   partial transpose. Then `γ + iσ̃ ≥ 0`, where `σ̃ = (−σ_A) ⊕ σ_B`.
2. Conversely, if `γ + iσ̃ ≥ 0`, the Gaussian state with covariance `γ` has positive partial
   transpose.

**Formalization Note.** "Positive partial transpose" is `IsPPTState`: the Fock-basis transpose on
Alice's factor is again a density operator. `γ + iσ̃ ≥ 0` is positive semidefiniteness of the
complexified matrix, with `+i` as printed. Part 1 holds for every state with finite second
moments; part 2 for every Gaussian state with covariance `γ` and every mean. -/
theorem proposition_2 {n m : ℕ} :
    (∀ (g : CovarianceBlocks n m) (ρ : State (Occupation (Fin n) × Occupation (Fin m)))
        (d : QuadratureIndex n ⊕ QuadratureIndex m → ℝ),
        HasCovarianceBlocks ρ g d → IsPPTState ρ →
        (complexify (covarianceBlockMatrix g) + Complex.I • complexify (sigmaTilde n m)).PosSemidef) ∧
    (∀ (g : CovarianceBlocks n m) (ρ : State (Occupation (Fin n) × Occupation (Fin m)))
        (d : QuadratureIndex n ⊕ QuadratureIndex m → ℝ),
        HasGaussianCovariance ρ g d →
        (complexify (covarianceBlockMatrix g) + Complex.I • complexify (sigmaTilde n m)).PosSemidef →
        IsPPTState ρ) := by sorry

end BoundEntGauss
