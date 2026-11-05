-- Prove2me | Theorems.Thm_BoundEntGauss_gaussian_state_exists
-- name    : BoundEntGauss.gaussian_state_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:48:28.565351+00:00
-- url     : https://prove2.me/theorems/7af8b31e-8e2b-4dba-b597-44affec01441
-- title:
--   Section II, after Eq. (3) — every $\gamma$ with $\gamma+i\sigma\ge0$ is the covariance of a Gaussian state
-- statement:
--   Consider $n$ oscillator modes on Alice's side and $m$ on Bob's side. Let $\gamma$ be a real symmetric $2(n+m)\times2(n+m)$ matrix satisfying the uncertainty condition
--
--   $$
--   \gamma+i\sigma\ge0
--   $$
--
--   (equivalently $\gamma-i\sigma\ge0$), and let $d\in\mathbb R^{2(n+m)}$ be arbitrary. Then there is a density operator $\rho$ on the Fock space of the $n+m$ modes that is the **Gaussian state with covariance $\gamma$ and mean $d$**: its characteristic function $\xi\mapsto\operatorname{tr}[\rho W(\xi)]$ is the Gaussian (3) with these coefficients.
--
--   This is the sufficiency half of the paper's remark after Eq. (3): the condition $\gamma+i\sigma\ge0$, necessary for any covariance matrix, is also sufficient for (3) to define a positive operator. It is what makes the goal's existence clause, and hence its bound-entanglement clause, non-vacuous.
--
--   Differences from the source:
--   - encoding: γ + iσ ≥ 0 → IsPhysicalCovariance (γ symmetric and γ − iσ ≥ 0); reason: the paper states the equivalence by complex conjugation in the same sentence; same instances
--   - reading: Gaussian state: tr[ρW(ξ)] = exp(imᵀξ − ¼ξᵀγξ), Eq. (3), with W(ξ) = exp(iξ·σ·R) → HasGaussianCovariance: characteristic function exp(−¼ξᵀσᵀγσξ + iξᵀσd) on actual Fock-space densities, every mean d; reason: as printed, (3) is consistent with W(ξ) = exp(iξ·σ·R) only if σγσᵀ = γ; the paper states that γ and m are the covariance and mean of ρ, which the Lean form makes true
--   - encoding: f canonical degrees of freedom, X = X_A ⊕ X_B, canonical coordinates → QuadratureIndex n ⊕ QuadratureIndex m (interleaved (x_j, p_j), Alice = Sum.inl), Fock space indexed by Occupation (Fin n) × Occupation (Fin m), for all n, m; reason: Lean representation of the same objects
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section II, p. 2 (unnumbered, after Eq. (3))

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P68

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Intakenext100.P68 (CovarianceBlocks IsPhysicalCovariance HasGaussianCovariance)

namespace BoundEntGauss

/-- **Every physical covariance is the covariance of a Gaussian state, for every mean.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section II, p. 2 (unnumbered, after Eq. (3)): "The necessary condition γ + iσ ≥ 0, which is
equivalent to γ − iσ ≥ 0 by complex conjugation, is also sufficient for Equation (3) to define a
positive operator ρ."

For all mode numbers `n`, `m`, every real symmetric `γ` of an `n × m`-mode bipartite system with
`γ − iσ ≥ 0` (equivalently `γ + iσ ≥ 0`) and every mean vector `d`, there is a density operator
`ρ` on the full Fock space whose characteristic function is the Gaussian (3) with covariance `γ`
and mean `d`.

**Formalization Note.** `IsPhysicalCovariance` and `HasGaussianCovariance` are the published
`Intakenext100.P68` predicates (interleaved coordinates, vacuum covariance `I`, `ħ = 1`; the
Gaussian is written in the Weyl-argument form `exp(−¼ ξᵀσᵀγσξ + i ξᵀσd)`, which makes `γ` and
`d` the actual covariance and mean, as the paper intends). -/
theorem gaussian_state_exists {n m : ℕ} (g : CovarianceBlocks n m) (hg : IsPhysicalCovariance g)
    (d : QuadratureIndex n ⊕ QuadratureIndex m → ℝ) :
    ∃ ρ : State (Occupation (Fin n) × Occupation (Fin m)), HasGaussianCovariance ρ g d := by sorry

end BoundEntGauss
