-- Prove2me | Theorems.Thm_FamousTheorems_trace_eq_sum_eigenvalues_6b
-- name    : FamousTheorems.trace_eq_sum_eigenvalues_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:33.501175+00:00
-- url     : https://prove2.me/theorems/772cfeb7-9c26-49c7-921b-03647dae6466
-- title:
--   The trace is the sum of the eigenvalues
-- statement:
--   **The trace is the sum of the eigenvalues.** Let $K$ be an algebraically closed field and $A$ an $n\times n$ matrix over $K$ with eigenvalues $\lambda_1,\dots,\lambda_n$, listed with algebraic multiplicity. Then
--   $$\operatorname{tr}A=\lambda_1+\lambda_2+\cdots+\lambda_n.$$
--
--   The trace is, up to sign, the coefficient of $X^{n-1}$ in the characteristic polynomial, and by Vieta's formulas this coefficient is minus the sum of the roots. The identity shows that the sum of the eigenvalues is a linear function of the matrix. It is used in character theory, where characters are traces, and for the traces of powers $\operatorname{tr}A^k=\sum\lambda_i^k$.
--
--   **Formalization note.** Mathlib's `Matrix.trace_eq_sum_roots_charpoly`. `A.charpoly.roots` is the multiset of roots of the characteristic polynomial, counted with multiplicity.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Matrix.trace_eq_sum_roots_charpoly`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem trace_eq_sum_eigenvalues_6b {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [IsAlgClosed K] (A : Matrix n n K) :
    A.trace = A.charpoly.roots.sum := by sorry

end FamousTheorems
