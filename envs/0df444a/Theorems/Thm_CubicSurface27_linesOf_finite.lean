-- Prove2me | Theorems.Thm_CubicSurface27_linesOf_finite
-- name    : CubicSurface27.linesOf_finite
-- status  : Proved
-- author  : @LG
-- created : 2026-11-22T01:31:48.471114+00:00
-- url     : https://prove2.me/theorems/8b2adc14-a278-4659-91bf-cf1b33740f9a
-- title:
--   The set of lines on a smooth cubic surface is finite
-- statement:
--   Let $V(F) \subset \mathbb{P}^3$ be a smooth cubic surface defined by a homogeneous cubic polynomial $F$ over $\mathbb{C}$. A line on $V(F)$ corresponds to a $2$-dimensional linear subspace of $\mathbb{C}^4$ on which $F$ vanishes identically. This theorem asserts that the set of all such lines, denoted $\text{linesOf}(F)$, is finite.
--
--   $$ \text{linesOf}(F) \text{ is a finite set.} $$
--
--   **Formalization Note.** The set of lines is defined as a subset of the Grassmannian of $2$-planes in $\mathbb{C}^4$, which is a projective variety. The finiteness is a basic structural property of the lines on any smooth cubic surface.

import Mathlib
import Definitions.Def_cubic_surface_27_layer

namespace CubicSurface27

theorem linesOf_finite (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F) :
    (linesOf F).Finite := by sorry

end CubicSurface27
