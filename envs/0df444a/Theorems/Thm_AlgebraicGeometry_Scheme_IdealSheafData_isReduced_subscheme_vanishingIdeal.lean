-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/fd4c92f6-6e97-53bd-827c-3dabd362f543
-- title:
--   Reduced induced closed subscheme structure is reduced
-- statement:
--   Let $X$ be a scheme (in a fixed universe) and let $Z$ be a closed subset of the underlying topological space of $X$, given as an element of `TopologicalSpace.Closeds X`. Attached to $Z$ is the ideal sheaf datum `Scheme.IdealSheafData.vanishingIdeal Z`, whose component on an affine open $U \subseteq X$ is the vanishing ideal of the closed set $Z \cap U$ in $\Gamma(X, U)$, i.e. the intersection of the primes of $\Gamma(X,U)$ lying in $Z \cap U$ under the identification $U \cong \operatorname{Spec} \Gamma(X,U)$; the associated closed subscheme of $X$ is `(Scheme.IdealSheafData.vanishingIdeal Z).subscheme`, the reduced induced structure on $Z$. The assertion is that this scheme is reduced, i.e. satisfies `IsReduced`: its local rings, equivalently the rings of sections over the members of an affine open cover, have no nonzero nilpotents. No further hypotheses on $X$ or $Z$ are imposed.
--
--   This is the standard fact that the closed subscheme cut out by the ideal sheaf of functions vanishing on a closed subset — the reduced induced subscheme structure on that subset — is a reduced scheme. It is used downstream in the treatment of closed subschemes of schemes, for instance when restricting such a subscheme along an open immersion and comparing smoothness of given relative dimension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
    {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by sorry
