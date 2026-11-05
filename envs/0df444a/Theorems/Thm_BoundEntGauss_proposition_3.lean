-- Prove2me | Theorems.Thm_BoundEntGauss_proposition_3
-- name    : BoundEntGauss.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:51:38.298171+00:00
-- url     : https://prove2.me/theorems/ba19b58a-8a76-41e0-8606-990df7bf3be3
-- title:
--   Proposition 3 — $\gamma$ is minimally ppt iff $\Re\mathfrak e\,\mathcal N$ and $\Re\mathfrak e\,\tilde{\mathcal N}$ span $X$
-- statement:
--   Let $\gamma$ be a ppt-covariance of an $n\times m$-mode system, and let $\mathcal N$ and $\tilde{\mathcal N}$ be the null spaces of $\gamma+i\sigma$ and $\gamma+i\tilde\sigma$ in $\mathbb C^{2(n+m)}$. Then
--
--   $$
--   \gamma\ \text{is minimally ppt}\iff \Re\mathfrak e\,\mathcal N+\Re\mathfrak e\,\tilde{\mathcal N}=X=\mathbb R^{2(n+m)} .
--   $$
--
--   Proposition 3 is the paper's effective test for minimal ppt: it replaces the order-theoretic Definition 1 by a finite-dimensional rank condition on two null spaces, which is how the family (11) is certified to be minimally ppt.
--
--   Differences from the source:
--   - encoding: "ℜeN and ℜeÑ together span X" → realPartSpan N ⊔ realPartSpan Ñ = ⊤ in the lattice of real subspaces of ℝ^{2(n+m)}; reason: the supremum of two subspaces is their sum
--   - encoding: f canonical degrees of freedom, X = X_A ⊕ X_B, canonical coordinates → QuadratureIndex n ⊕ QuadratureIndex m (interleaved (x_j, p_j), Alice = Sum.inl), Fock space indexed by Occupation (Fin n) × Occupation (Fin m), for all n, m; reason: Lean representation of the same objects
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Proposition 3, p. 3

import Mathlib
import Definitions.Def_BoundEntGauss_IsMinimallyPPT
import Definitions.Def_BoundEntGauss_nullSpace
import Definitions.Def_BoundEntGauss_realPartSpan

open QAlgorithms.Papers.Independent.Intakenext100.P68 (CovarianceBlocks covarianceBlockMatrix)

namespace BoundEntGauss

/-- **Proposition 3 (null-space criterion for minimal ppt).**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Proposition 3, p. 3.

Let `γ` be a ppt-covariance of an `n × m`-mode system, and let `N` and `Ñ` be the null spaces of
`γ + iσ` and `γ + iσ̃`. Then `γ` is minimally ppt if and only if `ℜe N` and `ℜe Ñ` together span
the phase space `X = ℝ^{2(n+m)}`.

**Formalization Note.** "Together span `X`" is `ℜe N ⊔ ℜe Ñ = ⊤` in the lattice of real subspaces
of `ℝ^{2(n+m)}` (the sup of two subspaces is their sum). -/
theorem proposition_3 {n m : ℕ} (g : CovarianceBlocks n m) (hg : IsPPTCovariance g) :
    IsMinimallyPPT g ↔
      realPartSpan (nullSpace (covarianceBlockMatrix g) (totalSigma n m)) ⊔
        realPartSpan (nullSpace (covarianceBlockMatrix g) (sigmaTilde n m)) = ⊤ := by sorry

end BoundEntGauss
