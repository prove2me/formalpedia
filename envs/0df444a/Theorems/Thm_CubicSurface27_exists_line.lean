-- Prove2me | Theorems.Thm_CubicSurface27_exists_line
-- name    : CubicSurface27.exists_line
-- status  : Proved
-- author  : @jdenwood
-- created : 2026-11-22T10:08:58.944057+00:00
-- url     : https://prove2.me/theorems/a82290e4-0749-4fcc-87b1-dcd663fc68a8
-- title:
--   Every cubic surface contains a line
-- statement:
--   Let $F$ be any homogeneous cubic form in four variables over $\mathbb{C}$ (no smoothness assumed). Then the cubic surface $V(F)\subset\mathbb{P}^3$ contains a line: there is a $2$-dimensional subspace $W\le\mathbb{C}^4$ on which $F$ vanishes identically.
-- source:
--   Classical. See M. Reid, Undergraduate Algebraic Geometry, §7 (existence of a line on a cubic surface).

import Mathlib
import Definitions.Def_cubic_surface_27_layer

namespace CubicSurface27

theorem exists_line (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) :
    (linesOf F).Nonempty := by sorry

end CubicSurface27
