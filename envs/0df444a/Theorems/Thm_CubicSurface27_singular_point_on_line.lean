-- Prove2me | Theorems.Thm_CubicSurface27_singular_point_on_line
-- name    : CubicSurface27.singular_point_on_line
-- status  : Proved
-- author  : @jdenwood
-- created : 2026-11-22T10:08:56.427989+00:00
-- url     : https://prove2.me/theorems/5c500757-fa0e-4123-8ca5-a58fd574d86a
-- title:
--   Every singular point of a cubic surface lies on a line of the surface
-- statement:
--   Let $F\in\mathbb{C}[x_0,\dots,x_3]$ be a homogeneous cubic form and let $x\in\mathbb{C}^4\setminus\{0\}$ be a singular point of the affine cone over $V(F)$, i.e. $F(x)=0$ and $\partial F/\partial x_i(x)=0$ for all $i$. Then there is a $2$-dimensional subspace $W\le\mathbb{C}^4$ with $x\in W$ on which $F$ vanishes identically. Projectively: every singular point of the cubic surface $V(F)\subset\mathbb{P}^3$ lies on a line contained in the surface. (No smoothness or irreducibility is assumed.)
-- source:
--   Classical. See M. Reid, Undergraduate Algebraic Geometry (LMS Student Texts 12), the section on cubic surfaces and the 27 lines (§7): in coordinates centred at a singular point, the lines through it correspond to common zeros of the quadric and cubic parts of F.

import Mathlib
import Definitions.Def_cubic_surface_27_layer

namespace CubicSurface27

theorem singular_point_on_line (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F)
    (x : Fin 4 → ℂ) (hx : x ≠ 0) (hFx : MvPolynomial.eval x F = 0)
    (hsing : ∀ i : Fin 4, MvPolynomial.eval x (MvPolynomial.pderiv i F) = 0) :
    ∃ W ∈ linesOf F, x ∈ W := by sorry

end CubicSurface27
