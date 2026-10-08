-- Prove2me | Theorems.Thm_ConicQuadIPM_NTScaling_eq_62
-- name    : ConicQuadIPM.NTScaling.eq_62
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:27.239416+00:00
-- url     : https://prove2.me/theorems/559169fd-b5b0-483f-9f4a-91f884582636
-- title:
--   (62), Appendix p. 38 — if w₁² − ‖w_{2:n}‖² = 1, the arrow form of (31) squares to −Q + 2wwᵀ
-- statement:
--   Let $d\ge 1$, let $Q = \operatorname{diag}(1,-1,\dots,-1)$, and let $w\in\mathbb R^d$ satisfy $w_1^2 - \|w_{2:d}\|^2 = 1$ and $1+w_1>0$. With
--   $$W = \begin{bmatrix} w_1 & w_{2:d}^T\\ w_{2:d} & I + \frac{w_{2:d}w_{2:d}^T}{1+w_1}\end{bmatrix}$$
--   one has
--   $$W W = -Q + 2ww^T.\qquad(62)$$
--
--   This is the identity (33) for the quadratic cone and the step that lets the NT condition $s = \theta^2W^2x$ be solved for $w$.
--
--   **Formalization Note** Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. The hypothesis $1+w_1>0$ makes the division defined; under the normalization it only excludes $w = -e_1$.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, p. 38, Appendix, proof of Lemma 4.2, (62)

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix

namespace ConicQuadIPM.NTScaling

/-- (62), Appendix, proof of Lemma 4.2, p. 38: if `w₁² − ‖w_{2:n}‖² = 1`, the arrow-form matrix
of (31) squares to `−Q + 2wwᵀ` (quadratic cone). -/
theorem eq_62 (d : ℕ) (hd : 1 ≤ d) (w : Fin d → ℝ)
    (hnorm : ConicQuadIPM.Complementarity.coord w 0 ^ 2 - ConicQuadIPM.Complementarity.tailSq w 1 = 1) (hw : 0 < 1 + ConicQuadIPM.Complementarity.coord w 0) :
    WquadArrow w * WquadArrow w = -Qmat .quad d + (2 : ℝ) • vecMulVec w w := by sorry
end ConicQuadIPM.NTScaling
