-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_trace_mul_eigen_bounds
-- name    : FatkhullinPolyak.Discrete.trace_mul_eigen_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:36:02.538295+00:00
-- url     : https://prove2.me/theorems/869a51ac-5e4f-43b2-bd08-f653beda67e9
-- title:
--   Lemma A.4 — $\lambda_1(A)\mathrm{Tr}(B)\le\mathrm{Tr}(AB)\le\lambda_n(A)\mathrm{Tr}(B)$ for positive semidefinite $A,B$
-- statement:
--   Let $A,B\in\mathbb R^{n\times n}$ be symmetric positive semidefinite, and let $\lambda_1(A)$, $\lambda_n(A)$ be the smallest and largest eigenvalues of $A$. Then
--   $$\lambda_1(A)\,\mathrm{Tr}(B)\le\mathrm{Tr}(AB)\le\lambda_n(A)\,\mathrm{Tr}(B).$$
--
--   This trace sandwich is the elementary estimate behind every eigenvalue bound on the LQR cost in the paper (Lemma 3.8, Lemma C.1, Lemma C.2).
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 15, Lemma A.4

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix

namespace FatkhullinPolyak.Discrete

/-- Lemma A.4 (p. 15): for positive semidefinite `A`, `B`,
`λ₁(A) Tr(B) ≤ Tr(AB) ≤ λₙ(A) Tr(B)`. -/
theorem trace_mul_eigen_bounds {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    lamMin A * Matrix.trace B ≤ Matrix.trace (A * B) ∧
      Matrix.trace (A * B) ≤ lamMax A * Matrix.trace B := by sorry

end FatkhullinPolyak.Discrete
