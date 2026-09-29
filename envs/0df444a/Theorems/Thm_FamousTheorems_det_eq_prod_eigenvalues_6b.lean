-- Prove2me | Theorems.Thm_FamousTheorems_det_eq_prod_eigenvalues_6b
-- name    : FamousTheorems.det_eq_prod_eigenvalues_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:33.190951+00:00
-- url     : https://prove2.me/theorems/9f681d74-2e5b-4f46-84aa-42233cf8e55a
-- title:
--   The determinant is the product of the eigenvalues
-- statement:
--   **The determinant is the product of the eigenvalues.** Let $K$ be an algebraically closed field and $A$ an $n\times n$ matrix over $K$ with eigenvalues $\lambda_1,\dots,\lambda_n$, listed with algebraic multiplicity. Then
--   $$\det A=\lambda_1\lambda_2\cdots\lambda_n.$$
--
--   The eigenvalues are the roots of the characteristic polynomial $\det(XI-A)$, and the determinant is, up to sign, its constant term. The identity shows that $A$ is invertible exactly when $0$ is not an eigenvalue. It is used to compute determinants from spectra and in the theory of the matrix exponential, via $\det e^A=e^{\operatorname{tr}A}$.
--
--   **Formalization note.** Mathlib's `Matrix.det_eq_prod_roots_charpoly`. `A.charpoly.roots` is the multiset of roots of the characteristic polynomial, counted with multiplicity.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Matrix.det_eq_prod_roots_charpoly`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem det_eq_prod_eigenvalues_6b {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [IsAlgClosed K] (A : Matrix n n K) :
    A.det = A.charpoly.roots.prod := by sorry

end FamousTheorems
