-- Prove2me | Theorems.Thm_ConicQuadIPM_Complementarity_alt_description
-- name    : ConicQuadIPM.Complementarity.alt_description
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:47.253639+00:00
-- url     : https://prove2.me/theorems/8456b064-9bb3-46bc-949e-ad4fe25dbc31
-- title:
--   p. 9 — Kq = {x : xᵀQx ≥ 0, x₁ ≥ 0} and Kr = {x : xᵀQx ≥ 0, x₁, x₂ ≥ 0}
-- statement:
--   The matrices $Q$ of Definition 3.2 give an alternative description of the two quadratic cones. For every $x\in\mathbb R^n$,
--   $$
--   x\in K^q\iff x^TQ^qx\ge 0\ \text{and}\ x_1\ge 0,
--   $$
--   where $Q^q=\operatorname{diag}(1,-1,\dots,-1)$; and if $n\ge 2$,
--   $$
--   x\in K^r\iff x^TQ^rx\ge 0\ \text{and}\ x_1,x_2\ge 0,
--   $$
--   where $Q^r$ is the matrix (19).
--
--   This is the form in which the cone constraints enter the neighbourhood $\mathcal N(\beta)$ and the scaling of §3.2.
--
--   **Formalization Note.** $x_1,x_2$ are indices `0`, `1`. The rotated case carries $n\ge 2$, the dimension the definition of $K^r$ needs.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 9, second paragraph

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

open Matrix

namespace ConicQuadIPM.Complementarity

theorem alt_description (d : ℕ) (v : Fin d → ℝ) :
    (inQuad v ↔ 0 ≤ v ⬝ᵥ (Qmat .quad d *ᵥ v) ∧ 0 ≤ coord v 0) ∧
    (2 ≤ d → (inRot v ↔
      0 ≤ v ⬝ᵥ (Qmat .rot d *ᵥ v) ∧ 0 ≤ coord v 0 ∧ 0 ≤ coord v 1)) := by sorry

end ConicQuadIPM.Complementarity
