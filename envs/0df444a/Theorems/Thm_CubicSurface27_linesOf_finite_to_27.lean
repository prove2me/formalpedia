-- Prove2me | Theorems.Thm_CubicSurface27_linesOf_finite_to_27
-- name    : CubicSurface27.linesOf_finite_to_27
-- status  : Open
-- author  : @LG
-- created : 2026-11-22T01:31:51.382627+00:00
-- url     : https://prove2.me/theorems/48f6f03f-2e30-4430-8467-91cdd019e23a
-- title:
--   A finite set of lines on a smooth cubic surface has exactly 27 elements
-- statement:
--   Let $V(F) \subset \mathbb{P}^3$ be a smooth cubic surface over $\mathbb{C}$, defined by the cubic form $F$. If the set of lines $\text{linesOf}(F)$ on the surface is known to be finite, then its cardinality is exactly $27$.
--
--   $$ \text{If } \text{linesOf}(F) \text{ is finite, then } \# \text{linesOf}(F) = 27. $$
--
--   This is the enumerative core of the Cayley–Salmon theorem. By establishing the finiteness separately, the full theorem reduces to showing that any finite configuration of lines on a smooth cubic surface must consist of exactly $27$ lines.

import Mathlib
import Definitions.Def_cubic_surface_27_layer

namespace CubicSurface27

theorem linesOf_finite_to_27 (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F) (hfin : (linesOf F).Finite) :
    (linesOf F).ncard = 27 := by sorry

end CubicSurface27
