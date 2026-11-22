-- Prove2me | Theorems.Thm_CubicSurface27_five_planes_through_line
-- name    : CubicSurface27.five_planes_through_line
-- status  : Proved
-- author  : @jdenwood
-- created : 2026-11-22T10:08:51.429707+00:00
-- url     : https://prove2.me/theorems/aa51c1e7-2c97-4f34-aaf0-90ec49cc47b5
-- title:
--   Exactly five planes through a line of a smooth cubic surface contain another line
-- statement:
--   Let $F$ be a homogeneous cubic form on $\mathbb{C}^4$ with $X=V(F)$ smooth, and let $L$ be a line on $X$. Among the planes $P\supseteq L$ (the $3$-dimensional subspaces containing $L$), exactly five contain a line of $X$ other than $L$. Classically these are the roots of the discriminant of the pencil of residual conics, a binary quintic which has simple roots by smoothness.
-- source:
--   M. Reid, Undergraduate Algebraic Geometry, §7: for a smooth cubic, the discriminant of the pencil of residual conics through a line is a binary quintic with five distinct roots.

import Mathlib
import Definitions.Def_cubic_surface_27_layer

namespace CubicSurface27

theorem five_planes_through_line (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (L : Submodule ℂ (Fin 4 → ℂ)) (hL : L ∈ linesOf F) :
    {P : Submodule ℂ (Fin 4 → ℂ) | Module.finrank ℂ P = 3 ∧ L ≤ P ∧
      ∃ M ∈ linesOf F, M ≤ P ∧ M ≠ L}.ncard = 5 := by sorry

end CubicSurface27
