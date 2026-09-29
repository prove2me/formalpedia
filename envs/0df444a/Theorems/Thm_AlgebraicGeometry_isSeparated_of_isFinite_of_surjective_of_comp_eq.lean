-- Prove2me | Theorems.Thm_AlgebraicGeometry_isSeparated_of_isFinite_of_surjective_of_comp_eq
-- name    : AlgebraicGeometry.isSeparated_of_isFinite_of_surjective_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/5975a195-af57-544d-8ad9-5f5f14a51ac5
-- title:
--   Separatedness descends along finite surjective morphisms
-- statement:
--   Let $X$, $Y$, $S$ be schemes (in universe $0$) and let $p : X \to Y$, $f : X \to S$, $g : Y \to S$ be morphisms of schemes with $p$ followed by $g$ equal to $f$. Assume that $p$ is a finite morphism (`IsFinite p`), that $p$ is surjective (`Surjective p`, surjectivity of the underlying map of topological spaces), and that $f$ is separated in the sense of Mathlib's `IsSeparated`, i.e. the diagonal $\Delta_f : X \to X \times_S X$ is a closed immersion. The conclusion is that $g$ is separated in the same sense: the diagonal $\Delta_g : Y \to Y \times_S Y$ is a closed immersion. No hypothesis of finite type, finite presentation or affineness is imposed on $f$ or $g$, and no condition on intersections of affine opens is required.
--
--   This is the standard descent of separatedness along a finite (indeed any universally closed) surjective morphism, as in EGA I 5.5.1. It is used in the construction of the quotient of a flat proper $\pi$-adic tower by a finite group, where separatedness of the levels must be obtained without control over intersections of invariant affine charts; the only user is [`AlgebraicGeometry.nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen`](thm.html#AlgebraicGeometry.nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isSeparated_of_isFinite_of_surjective_of_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isSeparated_of_isFinite_of_surjective_of_comp_eq
    {X Y S : Scheme.{0}} (p : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (h : p ≫ g = f)
    [IsFinite p] [Surjective p] [IsSeparated f] : IsSeparated g := by sorry
