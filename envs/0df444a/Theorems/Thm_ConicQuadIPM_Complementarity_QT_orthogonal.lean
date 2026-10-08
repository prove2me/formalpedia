-- Prove2me | Theorems.Thm_ConicQuadIPM_Complementarity_QT_orthogonal
-- name    : ConicQuadIPM.Complementarity.QT_orthogonal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:26.736047+00:00
-- url     : https://prove2.me/theorems/201e1deb-17a9-473e-9b47-53913df70355
-- title:
--   p. 9 — each Qⁱ and Tⁱ is symmetric and orthogonal: QⁱQⁱ = I, TⁱTⁱ = I
-- statement:
--   Let $K^i$ be one of the cones $\mathbb R_+$, $K^q$, $K^r$ of dimension $n^i$ (with $n^i=1$ for $\mathbb R_+$ and $n^i\ge 2$ for $K^r$), and let $T^i$, $Q^i$ be the matrices of Definition 3.2. Then $T^i$ and $Q^i$ are symmetric and orthogonal; in particular
--   $$
--   Q^iQ^i=I\qquad\text{and}\qquad T^iT^i=I .
--   $$
--
--   These identities are used throughout: $T^i$ is an involution that carries the rotated quadratic cone onto the quadratic cone, and $(T^ix^i)^TT^is^i=(x^i)^Ts^i$.
--
--   **Formalization Note.** The statement gives $(Q^i)^T=Q^i$, $(T^i)^T=T^i$, $(Q^i)^TQ^i=I$, $(T^i)^TT^i=I$, $Q^iQ^i=I$, $T^iT^i=I$. The dimension conditions (`BlockWF`) are not written on the page but are needed: for $n^i=1$ the "rotated" $Q$ would be the zero matrix.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 9, first paragraph (after Definition 3.2)

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

open Matrix

namespace ConicQuadIPM.Complementarity

theorem QT_orthogonal (c : ConeKind) (d : ℕ) (hwf : BlockWF c d) :
    (Qmat c d)ᵀ = Qmat c d ∧ (Tmat c d)ᵀ = Tmat c d ∧
    (Qmat c d)ᵀ * Qmat c d = 1 ∧ (Tmat c d)ᵀ * Tmat c d = 1 ∧
    Qmat c d * Qmat c d = 1 ∧ Tmat c d * Tmat c d = 1 := by sorry

end ConicQuadIPM.Complementarity
