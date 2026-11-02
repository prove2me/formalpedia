-- Prove2me | Theorems.Thm_CompactOperators_exists_hilbertBasis_of_compact_symmetric
-- name    : CompactOperators.exists_hilbertBasis_of_compact_symmetric
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T19:34:46.212273+00:00
-- url     : https://prove2.me/theorems/687b7756-750b-41ce-ab17-0fb93a3f9f04
-- title:
--   Eigenbasis of a compact self-adjoint operator on an arbitrary real or complex Hilbert space
-- statement:
--   Let $E$ be a real or complex Hilbert space, and let $T:E\to E$ be a compact self-adjoint bounded linear operator. Then $E$ has a Hilbert basis $(e_i)_{i\in I}$ of eigenvectors of $T$, with real eigenvalues $(\mu_i)_{i\in I}$:
--
--   $$T e_i=\mu_i e_i\qquad(i\in I).$$
--
--   No separability or injectivity is assumed. In particular the basis includes the full kernel, which need not be separable. This is a reusable form of the compact spectral theorem for spectral expansions, trace-class operators, and compact-operator theory.
--
--   **Formalization Note.** The index type is a subset of $E$, so it lies in the same universe as $E$. Mathlib expresses self-adjointness here as symmetry of the underlying linear map.
-- source:
--   Classical spectral theorem for compact self-adjoint operators, as used in the proof of Proposition 5.3, Kubrusly, Trace-Class and Nuclear Operators, arXiv:2204.06954v2, pp. 13–14, https://arxiv.org/html/2204.06954v2#S5. The statement isolates the general compact self-adjoint spectral theorem used there, for real or complex scalars.

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic

universe u v

namespace CompactOperators

theorem exists_hilbertBasis_of_compact_symmetric {𝕜 : Type v} [RCLike 𝕜]
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (T : E →L[𝕜] E) (hT : IsCompactOperator T)
    (hsym : (T : E →ₗ[𝕜] E).IsSymmetric) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (μ : s → ℝ),
      ∀ j, T (b j) = (μ j : 𝕜) • b j := by sorry

end CompactOperators
