-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_proposition_2_3
-- name    : BoxTDIMinMax.Separable.proposition_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:31.577221+00:00
-- url     : https://prove2.me/theorems/9d0dd651-a752-4261-b796-5a9ee6604b46
-- title:
--   Proposition 2.3, p. 8 — translating the right-hand side: Qx ≥ p − Qz∗ is box-TDI for rational z∗
-- statement:
--   Let $Q\in\mathbb Z^{I\times S}$ and $p\in\mathbb Z^I$, and suppose $Qx\ge p$ is box-TDI. For a rational vector $z^*\in\mathbb Q^S$ let $p_0:=p-Qz^*$. Then the system
--   $$Qx\ge p_0$$
--   is box-TDI.
--
--   Translating the polyhedron by a rational vector preserves box-TDI-ness; it is the first step of Proposition 2.10.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 8, Proposition 2.3

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Proposition 2.3, p. 8: if `Q x ≥ p` (integral `Q`, `p`) is box-TDI, then for every rational
vector `z*` the system `Q x ≥ p₀` with `p₀ := p - Q z*` is box-TDI. -/
theorem proposition_2_3 {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (zStar : S → ℚ) :
    IsBoxTDI (ratMat Q) (ratVec p - ratMat Q *ᵥ zStar) := by sorry

end BoxTDIMinMax.Separable
