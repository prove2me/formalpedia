-- Prove2me | Theorems.Thm_AsymptoticOperator_exists_not_eigenvalue_of_isFormalAdjoint
-- name    : AsymptoticOperator.exists_not_eigenvalue_of_isFormalAdjoint
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T17:34:44.897301+00:00
-- url     : https://prove2.me/theorems/ada3b71d-e97b-4fa3-938f-186cf8cf1a8b
-- title:
--   A symmetric operator on a separable Hilbert space has a real non-eigenvalue
-- statement:
--   Let $E$ be a separable real inner product space and let $A$ be a linear operator defined on a subspace $D(A)\subseteq E$ (a partially defined linear map $E\to E$). Suppose $A$ is symmetric: $\langle Ax,y\rangle=\langle x,Ay\rangle$ for all $x,y\in D(A)$. Then there is a real number $\mu$ that is not an eigenvalue of $A$: if $f\in D(A)$ and $Af=\mu f$, then $f=0$.
--
--   Role: this supplies a real point $\mu$ with $\ker(A-\mu)=0$, needed to speak of the resolvent $(A-\mu)^{-1}$ of a symmetric differential operator (for example the asymptotic operator $A_S=-J_0\partial_t-S$ on $L^2(S^1,\mathbb R^{2n})$) without leaving the real numbers.
--
--   Formalization note: `E →ₗ.[ℝ] E` is Mathlib's `LinearPMap` (a linear map on the submodule `A.domain`), and `A.IsFormalAdjoint A` is Mathlib's symmetry condition `⟪A x, y⟫ = ⟪x, A y⟫` for `x y : A.domain`. Separability is the typeclass `TopologicalSpace.SeparableSpace E`; completeness is not assumed.
-- source:
--   Standard Hilbert-space fact; used for Hofer-Wysocki-Zehnder (GAFA 1995), §3, p. 285, and Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, §3.2

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Bases
import Mathlib.Analysis.Real.Cardinality

namespace AsymptoticOperator

/-- A symmetric partially defined operator on a separable real inner product space has a real
number that is not an eigenvalue. -/
theorem exists_not_eigenvalue_of_isFormalAdjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [TopologicalSpace.SeparableSpace E] (A : E →ₗ.[ℝ] E)
    (hA : A.IsFormalAdjoint A) :
    ∃ μ : ℝ, ∀ f : A.domain, A f = μ • (f : E) → (f : E) = 0 := by sorry

end AsymptoticOperator
