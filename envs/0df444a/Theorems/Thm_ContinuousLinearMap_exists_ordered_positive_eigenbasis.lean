-- Prove2me | Theorems.Thm_ContinuousLinearMap_exists_ordered_positive_eigenbasis
-- name    : ContinuousLinearMap.exists_ordered_positive_eigenbasis
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T21:45:19.850307+00:00
-- url     : https://prove2.me/theorems/9086237c-8a82-4ebf-8ae7-fe25f47915a0
-- title:
--   Ordered eigenbasis of a strictly positive compact symmetric operator
-- statement:
--   Let E be an infinite-dimensional real Hilbert space and K a compact symmetric bounded operator with strictly positive quadratic form on nonzero vectors. There are an orthonormal Hilbert basis indexed by the natural numbers and positive eigenvalues κₖ, in nonincreasing order, tending to zero. No separability hypothesis is needed: strict positivity implies injectivity, and a compact symmetric injective operator forces separability. This is the ordered positive version of the compact spectral theorem used in Hunter’s Theorem 4.25. A proof can start with the existing AsymptoticOperator.exists_hilbertBasis_eigenvectors_of_isCompactOperator, then order the positive eigenvalues using finiteness above each positive threshold.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, sections 4.8–4.10, pp. 105–109, especially Theorem 4.25. https://math.ucdavis.edu/~hunter/pdes/pde_notes.pdf

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Algebra.Order.Field

open Filter Topology

theorem ContinuousLinearMap.exists_ordered_positive_eigenbasis
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hinf : ¬ FiniteDimensional ℝ E) (K : E →L[ℝ] E) (hc : IsCompactOperator K)
    (hs : (K : E →ₗ[ℝ] E).IsSymmetric)
    (hp : ∀ x : E, x ≠ 0 → 0 < inner ℝ (K x) x) :
    ∃ (κ : ℕ → ℝ) (b : HilbertBasis ℕ ℝ E),
      (∀ k, 0 < κ k) ∧ Antitone κ ∧ Tendsto κ atTop (𝓝 0) ∧
      ∀ k, K (b k) = κ k • b k := by sorry
