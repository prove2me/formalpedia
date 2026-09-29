-- Prove2me | Theorems.Thm_FamousTheorems_eigenvectors_linear_independent_7b
-- name    : FamousTheorems.eigenvectors_linear_independent_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:34.99679+00:00
-- url     : https://prove2.me/theorems/1ce40eba-7e39-41be-992f-2cd7d73eaf43
-- title:
--   Eigenvectors for distinct eigenvalues are linearly independent
-- statement:
--   **Eigenvectors for distinct eigenvalues are linearly independent.** Let $f$ be a linear endomorphism of a vector space $V$ over a field $K$. Let $S\subseteq K$ be a set of scalars and, for each $\mu\in S$, let $x_\mu$ be an eigenvector of $f$ with eigenvalue $\mu$. Then the family $(x_\mu)_{\mu\in S}$ is linearly independent.
--
--   It follows that an endomorphism of an $n$-dimensional space has at most $n$ eigenvalues, and that it is diagonalizable if it has $n$ distinct eigenvalues. The standard proof takes a shortest linear relation and applies $f-\mu$ to reduce its length.
--
--   **Formalization note.** Mathlib's `Module.End.eigenvectors_linearIndependent`, specialized from integral domains to fields. `f.HasEigenvector μ x` says that $f x=\mu x$ and $x\neq0$. The family is indexed by the elements of $S$ viewed as a type.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Module.End.eigenvectors_linearIndependent`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem eigenvectors_linear_independent_7b {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (f : Module.End K V) (μs : Set K)
    (xs : μs → V) (h : ∀ μ : μs, f.HasEigenvector μ (xs μ)) : LinearIndependent K xs := by sorry

end FamousTheorems
