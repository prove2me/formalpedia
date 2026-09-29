-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isRegularRing_stalk_of_forall_isRegularLocalRing_stalk
-- name    : AlgebraicGeometry.Scheme.isRegularRing_stalk_of_forall_isRegularLocalRing_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/15896449-6f88-55a8-b30e-577fe3efc8ca
-- title:
--   Stalks of a scheme with regular local stalks are regular rings
-- statement:
--   Let $X$ be a scheme (in a fixed universe) and suppose that for every point $x$ of $X$ the stalk $\mathcal{O}_{X,x}$ of its structure sheaf at $x$ is a regular local ring. Then for every point $x$ of $X$ the ring $\mathcal{O}_{X,x}$ is a regular ring, that is, for each prime ideal $\mathfrak{q}$ of $\mathcal{O}_{X,x}$ the localisation $(\mathcal{O}_{X,x})_{\mathfrak{q}}$ is a regular local ring. Note that the hypothesis is the corresponding regularity assertion at all points of $X$ simultaneously, while the conclusion concerns the single point $x$ named in the statement; the content is thus the passage from regularity of the local rings of $X$ to regularity, in the global (non-local) sense, of one of them.
--
--   This is the standard fact that a scheme all of whose local rings are regular is a regular scheme, in the form asserting that each such local ring is itself a regular ring. It is used in the study of good reduction of Jacobians, specifically by [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_pullback_iso_of_isDiscreteValuationRing`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_pullback_iso_of_isDiscreteValuationRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_isRegularRing_stalk_of_forall_isRegularLocalRing_stalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.isRegularRing_stalk_of_forall_isRegularLocalRing_stalk
    {X : Scheme.{u}} (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (x : X) :
    IsRegularRing (X.presheaf.stalk x) := by sorry
