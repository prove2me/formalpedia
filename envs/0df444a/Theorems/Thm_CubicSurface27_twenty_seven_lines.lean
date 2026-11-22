-- Prove2me | Theorems.Thm_CubicSurface27_twenty_seven_lines
-- name    : CubicSurface27.twenty_seven_lines
-- status  : Proved
-- author  : @LG
-- created : 2026-11-20T13:53:21.55661+00:00
-- url     : https://prove2.me/theorems/39636e19-f7ae-4969-9b7c-1ed62b461814
-- title:
--   Cayley–Salmon: a smooth cubic surface has exactly $27$ lines
-- statement:
--   The Cayley–Salmon theorem, the capstone of the source: every smooth cubic surface over $\mathbb{C}$ contains exactly $27$ lines.
--
--   Precisely, let $F$ be a homogeneous cubic form in four variables over $\mathbb{C}$ whose zero locus $V(F)\subset\mathbb{P}^3$ is smooth (the Jacobian criterion: at every nonzero point of the affine cone over $V(F)$ some partial derivative of $F$ is nonzero). Then the set of lines on $V(F)$ — the $2$-dimensional linear subspaces of $\mathbb{C}^4$ on which $F$ vanishes identically — is finite of cardinality $27$:
--   $$\#\{\text{lines on }V(F)\}=27.$$
--
--   This is the basic discrete invariant of a cubic surface, anchoring its description as the blowup of $\mathbb{P}^2$ at six points and the $E_6$ Weyl-group action on the lines.
--
--   **Formalization Note.** The count is `Set.ncard (linesOf F)`. The theorem quantifies over all smooth cubic forms, with no genericity hypothesis beyond smoothness; it is the source's final Theorem ("If $X$ is smooth, then $s_F$ has transverse zeroes. Therefore $X$ contains exactly 27 lines").
-- source:
--   Jack Huizenga, answer to "In Algebraic Geometry, why are there exactly 27 straight lines on a smooth cubic surface?", Quora. Archived 2026-11-20 at https://perma.cc/38AQ-6ZCM (snapshot of https://suosuo.de/uu0jlKJ). Part II, final Theorem: 'If X is smooth, then s_F has transverse zeroes. Therefore X contains exactly 27 lines.' (Also Part I: 'A general smooth cubic surface contains exactly 27 lines.')

import Mathlib
import Definitions.Def_cubic_surface_27_layer

namespace CubicSurface27

theorem twenty_seven_lines (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F) :
    (linesOf F).ncard = 27 := by sorry

end CubicSurface27
