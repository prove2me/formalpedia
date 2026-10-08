-- Prove2me | Theorems.Thm_ConicQuadIPM_Complementarity_rot_quad_transform
-- name    : ConicQuadIPM.Complementarity.rot_quad_transform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:35.74362+00:00
-- url     : https://prove2.me/theorems/8055ba7d-fb48-4af1-95e7-76db1156d56a
-- title:
--   p. 9 — for the rotated cone's T: x ∈ Kq ⇔ Tx ∈ Kr
-- statement:
--   Let $n\ge 2$ and let $T$ be the matrix (18) of the rotated quadratic cone. For every $x\in\mathbb R^n$,
--   $$
--   x\in K^q\iff Tx\in K^r .
--   $$
--
--   So the rotated quadratic cone is the image of the quadratic cone under the linear (and, since $TT=I$, involutive) map $T$; results for $K^q$ transfer to $K^r$ through it.
--
--   **Formalization Note.** $n\ge 2$ is the dimension the rotated cone needs and is not written on the page.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 9, third paragraph

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

open Matrix

namespace ConicQuadIPM.Complementarity

theorem rot_quad_transform (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) :
    inQuad v ↔ inRot (Tmat .rot d *ᵥ v) := by sorry

end ConicQuadIPM.Complementarity
