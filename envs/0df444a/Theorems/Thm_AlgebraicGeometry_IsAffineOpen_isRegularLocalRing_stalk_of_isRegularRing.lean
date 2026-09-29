-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing
-- name    : AlgebraicGeometry.IsAffineOpen.isRegularLocalRing_stalk_of_isRegularRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/0273ffe9-cfb5-53ce-b879-db4b1cdd9ef5
-- title:
--   Regular stalks from a regular affine coordinate ring
-- statement:
--   Let $X$ be a scheme (in a fixed universe), let $U$ be an open subset of $X$ which is affine, i.e. satisfies `IsAffineOpen`, and assume that the ring of sections $\Gamma(X, U)$ is a regular ring in the sense of Mathlib's `IsRegularRing` (a commutative Noetherian ring all of whose localisations at prime ideals are regular local rings). Let $x$ be a point of $X$ lying in $U$. Then the stalk of the structure sheaf of $X$ at $x$, `X.presheaf.stalk x`, is a regular local ring, i.e. satisfies `IsRegularLocalRing`. Thus, under the hypothesis that the coordinate ring of an affine chart is regular, every local ring of $X$ at a point of that chart is regular; no hypothesis is imposed on $X$ outside $U$, and no conclusion is drawn about points outside $U$.
--
--   This is the standard passage from ring-level regularity of an affine chart to regularity of the scheme at the points of that chart, regularity of a Noetherian local ring being preserved under isomorphism. It is used when regular models are built by gluing explicit affine charts, for instance the charts occurring in the construction of Deligne–Rapoport type models of modular curves over a discrete valuation ring, where the chart rings are shown regular by direct ring-theoretic computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsAffineOpen.isRegularLocalRing_stalk_of_isRegularRing
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (hreg : IsRegularRing Γ(X, U))
    (x : X) (hx : x ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk x) := by sorry
