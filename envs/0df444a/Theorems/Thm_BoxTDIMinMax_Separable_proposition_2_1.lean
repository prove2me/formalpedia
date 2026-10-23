-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_proposition_2_1
-- name    : BoxTDIMinMax.Separable.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:35.362894+00:00
-- url     : https://prove2.me/theorems/b5752b22-0327-420e-a367-ee07c3ec21af
-- title:
--   Proposition 2.1, p. 8 — a box-TDI system is TDI
-- statement:
--   Let $A\in\mathbb Q^{I\times S}$ and $b\in\mathbb Q^I$. If the system $Ax\ge b$ is box-TDI, then it is TDI.
--
--   The paper cites this from Schrijver's book; it is used for the $2|S|$ sparsity clause of Theorem 3.3.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 8, Proposition 2.1 (citing [26, Theorem 22.7])

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Proposition 2.1, p. 8 ([26, Theorem 22.7]): a box-TDI (rational) system is TDI. -/
theorem proposition_2_1 {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (A : Matrix ι S ℚ) (b : ι → ℚ) (h : IsBoxTDI A b) :
    IsTDI A b := by sorry

end BoxTDIMinMax.Separable
