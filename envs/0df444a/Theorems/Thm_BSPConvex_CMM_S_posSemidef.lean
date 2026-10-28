-- Prove2me | Theorems.Thm_BSPConvex_CMM_S_posSemidef
-- name    : BSPConvex.CMM.S_posSemidef
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:40.786786+00:00
-- url     : https://prove2.me/theorems/4b3ef72a-18a6-4e12-8b96-ddae0a98f7b7
-- title:
--   Proof of Theorem 1, p. 25 — S(x) = Diag(x) − xxᵀ is positive semidefinite on Δm
-- statement:
--   Let $x\in\Delta_m$, that is, $x\ge 0$ and $e^\top x\le 1$. Then the matrix $S(x)=\operatorname{Diag}(x)-xx^\top$ is positive semidefinite:
--   $$S(x)\succeq 0.$$
--
--   The paper observes this in the proof of Theorem 1 (the matrix is diagonally dominant). It guarantees that $T(x)=\Sigma^{1/2}S(x)\Sigma^{1/2}$ is positive semidefinite for every $x\in\Delta_m$ and every positive semidefinite $\Sigma$, so that $T(x)^{1/2}$ and $f(x)=\operatorname{tr}(T(x)^{1/2})$ are well defined on the whole simplex.
--
--   **Formalization Note** Positive semidefiniteness is Mathlib's `Matrix.PosSemidef`, which includes symmetry.
-- source:
--   Li, Sun & Teo, Convex Optimization for Bundle Size Pricing Problem, SSRN 3426933 (version of May 8, 2021), p. 25, proof of Theorem 1 (after (19))

import Mathlib
import Definitions.Def_BSPConvex_CMM_Model

open Matrix
open scoped MatrixOrder

namespace BSPConvex.CMM

theorem S_posSemidef {m : ℕ} (x : Fin m → ℝ) (hx : x ∈ simplex m) :
    (Smat x).PosSemidef := by sorry

end BSPConvex.CMM
