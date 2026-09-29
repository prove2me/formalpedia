-- Prove2me | Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_exists_isFinite_morphismRestrict_of_irreducibleSpace
-- name    : AlgebraicGeometry.LocallyQuasiFinite.exists_isFinite_morphismRestrict_of_irreducibleSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/79fc374d-3d15-5f4d-bee3-5070c5e664bf
-- title:
--   Generic finiteness of separated quasi-finite morphisms
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe) and let $f : X \to Y$ be a morphism which is locally of finite type, locally quasi-finite, separated and quasi-compact, and suppose the underlying topological space of $Y$ is irreducible (in particular non-empty). Then there exists an open subscheme $U$ of $Y$ whose underlying set is non-empty such that the restricted morphism $f \mid_U : f^{-1}(U) \to U$ is a finite morphism, i.e. it lies in the class `IsFinite`. Since a non-empty open subset of an irreducible space is dense, the conclusion says that $f$ becomes finite over a dense open subset of the base; no control over $U$ beyond non-emptiness is asserted, and in particular $U$ is not claimed to be affine nor to contain any prescribed point.
--
--   This is the standard generic finiteness statement: a separated, quasi-compact, locally quasi-finite morphism of finite type over an irreducible base is finite over some dense open of the base (EGA IV, 9.6.1-type spreading out). It is used in the construction of the relative group law on Jacobians with good reduction, where it supplies a base point over which a family of quasi-finite morphisms becomes simultaneously finite.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_LocallyQuasiFinite_exists_isFinite_morphismRestrict_of_irreducibleSpace.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.LocallyQuasiFinite.exists_isFinite_morphismRestrict_of_irreducibleSpace
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated f] [QuasiCompact f] [IrreducibleSpace Y] :
    ∃ U : Y.Opens, (U : Set Y).Nonempty ∧ IsFinite (f ∣_ U) := by sorry
