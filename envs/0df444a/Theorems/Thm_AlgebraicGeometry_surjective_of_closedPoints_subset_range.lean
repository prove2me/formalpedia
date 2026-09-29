-- Prove2me | Theorems.Thm_AlgebraicGeometry_surjective_of_closedPoints_subset_range
-- name    : AlgebraicGeometry.surjective_of_closedPoints_subset_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/c2aebc72-808e-5b5c-8885-7c4a01b7cd8c
-- title:
--   Surjectivity detected on closed points over a Jacobson base
-- statement:
--   Let $X$ and $Y$ be schemes and let $f \colon X \to Y$ be a morphism of schemes which is locally of finite presentation and quasi-compact, and assume the underlying topological space of $Y$ is a Jacobson space (every non-empty locally closed subset contains a point closed in $Y$; equivalently, closed points are dense in every closed subset). Suppose that the set $\mathrm{closedPoints}\ Y$ of points of $Y$ that are closed in $Y$ is contained in the range of the continuous map $f.\mathrm{base}$ underlying $f$. The conclusion is that $f$ is surjective in the sense of `AlgebraicGeometry.Surjective`, i.e. the map $f.\mathrm{base}$ on underlying topological spaces is surjective. Thus, for morphisms in this class and with Jacobson target, surjectivity is tested on closed points of the target alone.
--
--   This is the standard criterion (as in EGA IV) that for a quasi-compact morphism locally of finite presentation into a scheme with Jacobson underlying space, surjectivity follows from surjectivity onto closed points. It serves as the topological input to [`AlgebraicGeometry.surjective_of_forall_exists_comp_eq_of_isAlgClosed`](thm.html#AlgebraicGeometry.surjective_of_forall_exists_comp_eq_of_isAlgClosed), where surjectivity is deduced from the existence of liftings of points with values in algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_surjective_of_closedPoints_subset_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

theorem AlgebraicGeometry.surjective_of_closedPoints_subset_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [JacobsonSpace Y]
    (h : closedPoints Y ⊆ Set.range f.base) : Surjective f := by sorry
