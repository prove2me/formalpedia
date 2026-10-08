-- Prove2me | Theorems.Thm_AffinePolicies_Simplex_Qmat_isUnit_det
-- name    : AffinePolicies.Simplex.Qmat_isUnit_det
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:38:06.074911+00:00
-- url     : https://prove2.me/theorems/540fdf47-8d4b-4bc3-b33f-d9f2f47bb66a
-- title:
--   Theorem 1, proof, PDF p. 6 — Q = [(b¹ − b^{m+1}) … (b^m − b^{m+1})] is invertible
-- statement:
--   Let $b^1,\dots,b^{m+1}\in\mathbb R^m$ be affinely independent and let
--   $$Q=\big[(b^1-b^{m+1})\ \cdots\ (b^m-b^{m+1})\big]\in\mathbb R^{m\times m}$$
--   be the matrix whose $j$-th column is $b^j-b^{m+1}$. Then $Q$ is invertible:
--   $$\det Q\neq 0.$$
--
--   This is the first step of the proof of Theorem 1: it makes the barycentric coordinates of a point of the simplex an affine function of the point.
--
--   **Formalization Note** The vertices are `v : Fin (m+1) → Fin m → ℝ` with $b^j$ = `v (j-1)`; invertibility is stated as `IsUnit (Qmat v).det`. For $m=0$, $Q$ is the empty matrix with determinant $1$.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 1, proof, definition of Q, PDF p. 6

import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting

namespace AffinePolicies.Simplex

theorem Qmat_isUnit_det {m : ℕ} (v : Fin (m + 1) → Fin m → ℝ) (hv : AffineIndependent ℝ v) :
    IsUnit (Qmat v).det := by sorry

end AffinePolicies.Simplex
