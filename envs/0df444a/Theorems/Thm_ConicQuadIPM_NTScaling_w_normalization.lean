-- Prove2me | Theorems.Thm_ConicQuadIPM_NTScaling_w_normalization
-- name    : ConicQuadIPM.NTScaling.w_normalization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:07.984437+00:00
-- url     : https://prove2.me/theorems/ef27d088-02fc-4139-8eae-185c35d1dabf
-- title:
--   Appendix, proof of Lemma 4.2, p. 38 — WQW = Q for the arrow form of (31) forces w₁² − ‖w_{2:n}‖² = 1
-- statement:
--   Let $d\ge1$ and $Q = \operatorname{diag}(1,-1,\dots,-1)$ be the matrix of the quadratic cone. For $w\in\mathbb R^d$ with $1+w_1>0$ let
--   $$W = \begin{bmatrix} w_1 & w_{2:d}^T\\ w_{2:d} & I + \frac{w_{2:d}w_{2:d}^T}{1+w_1}\end{bmatrix}.$$
--   If $WQW = Q$, then
--   $$w_1^2 - \|w_{2:d}\|^2 = 1.$$
--
--   This normalization is what makes the square of $W$ collapse to the rank-one correction (62).
--
--   **Formalization Note** Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. The hypothesis $1+w_1>0$ is added so that the division by $1+w_1$, which the page performs without comment, is defined.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, p. 38, Appendix, proof of Lemma 4.2 (line after (62))

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix

namespace ConicQuadIPM.NTScaling

/-- Appendix, proof of Lemma 4.2, p. 38: if the arrow-form matrix (31) satisfies `WQW = Q` for
the quadratic cone, then `w₁² − ‖w_{2:n}‖² = 1`. -/
theorem w_normalization (d : ℕ) (hd : 1 ≤ d) (w : Fin d → ℝ) (hw : 0 < 1 + ConicQuadIPM.Complementarity.coord w 0)
    (hWQW : WquadArrow w * Qmat .quad d * WquadArrow w = Qmat .quad d) :
    ConicQuadIPM.Complementarity.coord w 0 ^ 2 - ConicQuadIPM.Complementarity.tailSq w 1 = 1 := by sorry
end ConicQuadIPM.NTScaling
