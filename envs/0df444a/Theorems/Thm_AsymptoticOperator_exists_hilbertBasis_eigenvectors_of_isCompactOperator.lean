-- Prove2me | Theorems.Thm_AsymptoticOperator_exists_hilbertBasis_eigenvectors_of_isCompactOperator
-- name    : AsymptoticOperator.exists_hilbertBasis_eigenvectors_of_isCompactOperator
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T17:42:03.76921+00:00
-- url     : https://prove2.me/theorems/7d27b349-1044-4cdf-bcc4-9e669b06c9cd
-- title:
--   A compact symmetric injective operator on a real Hilbert space has a Hilbert basis of eigenvectors
-- statement:
--   Let $E$ be a real Hilbert space and let $T:E\to E$ be a bounded linear operator that is compact, symmetric ($\langle Tx,y\rangle=\langle x,Ty\rangle$ for all $x,y\in E$) and injective. Then there is a Hilbert basis (complete orthonormal family) $(e_i)_{i\in I}$ of $E$ and real numbers $(\nu_i)_{i\in I}$ such that
--   $$Te_i=\nu_i\,e_i,\qquad \nu_i\neq 0\quad\text{for all }i\in I,$$
--   and $\nu_i\to 0$ along the cofinite filter on $I$: for every $\varepsilon>0$ only finitely many indices satisfy $|\nu_i|\ge\varepsilon$.
--
--   Role: this is the spectral theorem for compact self-adjoint operators in the form of an eigenbasis. Applied to the resolvent $(A-\mu)^{-1}$ of a self-adjoint operator with compact resolvent, such as the asymptotic operator $A_S=-J_0\partial_t-S$ on $L^2(S^1,\mathbb R^{2n})$, it yields an orthonormal eigenbasis of $A$ whose eigenvalues $\mu+\nu_i^{-1}$ accumulate only at $\pm\infty$.
--
--   Formalization note: `IsCompactOperator T` is Mathlib's notion of a compact operator, `(T : E →ₗ[ℝ] E).IsSymmetric` is Mathlib's `LinearMap.IsSymmetric`, `HilbertBasis ι ℝ E` is Mathlib's Hilbert basis, and the index type `ι` lives in `Type` (the statement takes `E : Type`).
-- source:
--   Standard spectral theorem for compact self-adjoint operators; used for Hofer-Wysocki-Zehnder (GAFA 1995), §3, p. 285, and Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, §3.2

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic

open Module End Filter Topology

namespace AsymptoticOperator

/-- A compact, symmetric, injective bounded operator on a real Hilbert space has a Hilbert basis
of eigenvectors; the eigenvalues are nonzero and tend to `0` along the cofinite filter. -/
theorem exists_hilbertBasis_eigenvectors_of_isCompactOperator {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (hsym : (T : E →ₗ[ℝ] E).IsSymmetric) (hinj : Function.Injective T) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ E) (ν : ι → ℝ),
      (∀ i, T (b i) = ν i • b i) ∧ (∀ i, ν i ≠ 0) ∧ Tendsto ν cofinite (𝓝 0) := by sorry

end AsymptoticOperator
