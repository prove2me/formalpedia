-- Prove2me | Theorems.Thm_AsymptoticOperator_hasSum_inner_self_of_hilbertBasis_eigenvectors
-- name    : AsymptoticOperator.hasSum_inner_self_of_hilbertBasis_eigenvectors
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T21:59:19.056367+00:00
-- url     : https://prove2.me/theorems/b6073e78-c249-42d0-9a38-0eb1cabe4f8a
-- title:
--   Quadratic form of a symmetric operator in a Hilbert basis of eigenvectors
-- statement:
--   Let $E$ be a real inner product space and let $A$ be a linear operator defined on a subspace $D(A)\subseteq E$ that is symmetric: $\langle Ax,y\rangle=\langle x,Ay\rangle$ for all $x,y\in D(A)$. Let $(b_i)_{i\in I}$ be a Hilbert basis of $E$ consisting of eigenvectors of $A$ in $D(A)$, with $Ab_i=\lambda_i b_i$ for real numbers $\lambda_i$. Then for every $x\in D(A)$ the series $\sum_{i\in I}\lambda_i\langle x,b_i\rangle^2$ converges unconditionally and
--   $$\langle Ax,x\rangle=\sum_{i\in I}\lambda_i\,\langle x,b_i\rangle^2 .$$
--
--   Role: expresses the quadratic form of a symmetric operator with an orthonormal eigenbasis through its eigenvalues. Applies to any such operator, for example the asymptotic operators $A_S=-J_0\partial_t-S$ on $L^2(S^1,\mathbb R^{2n})$.
--
--   Formalization note: `E →ₗ.[ℝ] E` is Mathlib's `LinearPMap` (a linear map on the submodule `A.domain`), `A.IsFormalAdjoint A` is the symmetry condition, `HilbertBasis ι ℝ E` is Mathlib's Hilbert basis, and convergence is `HasSum` (unconditional summation over `ι`). The index type and `E` live in `Type`; no completeness of $E$ is assumed.
-- source:
--   Standard Hilbert-space fact; used for Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, §3.4, Proposition 3.28

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearPMap

namespace AsymptoticOperator

/-- Let `A` be a symmetric partially defined operator on a real inner product space, and let `b`
be a Hilbert basis of eigenvectors of `A` lying in its domain, `A bᵢ = evᵢ bᵢ`. Then for every
`x` in the domain the quadratic form of `A` is `⟨A x, x⟩ = ∑ᵢ evᵢ ⟨x, bᵢ⟩²`. -/
theorem hasSum_inner_self_of_hilbertBasis_eigenvectors {E ι : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) (hA : A.IsFormalAdjoint A)
    (b : HilbertBasis ι ℝ E) (ev : ι → ℝ)
    (hb : ∀ i, ∃ h : b i ∈ A.domain, A ⟨b i, h⟩ = ev i • b i) (x : A.domain) :
    HasSum (fun i => ev i * inner ℝ (x : E) (b i) ^ 2) (inner ℝ (A x) (x : E)) := by sorry

end AsymptoticOperator
