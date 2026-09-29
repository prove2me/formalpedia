-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_isRegularLocalRing_stalk_iff
-- name    : AlgebraicGeometry.IsOpenImmersion.isRegularLocalRing_stalk_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/da25aa50-f41f-5ac7-bf3e-dae8b37802a3
-- title:
--   Regularity of stalks is invariant under open immersions
-- statement:
--   Let $U$ and $X$ be schemes (in a fixed universe), let $i \colon U \to X$ be a morphism of schemes which is an open immersion, and let $u$ be a point of $U$. The theorem asserts the equivalence of two statements: the stalk of the structure sheaf of $X$ at the image point $i(u)$ — that is, the local ring $\mathcal{O}_{X, i(u)}$, obtained as the stalk of `X.presheaf` at the point `i.base u` of the underlying topological space of $X$ — is a regular local ring, if and only if the stalk $\mathcal{O}_{U,u}$ of the structure sheaf of $U$ at $u$ is a regular local ring. Here regularity is Mathlib's predicate `IsRegularLocalRing` on commutative rings. The statement is an equivalence in both directions, with no Noetherian or finiteness hypotheses beyond those built into the notion of a regular local ring itself.
--
--   This is the standard fact that regularity of local rings is a local property on a scheme, insensitive to passing to an open subscheme: the stalks of $X$ at points of an open subscheme agree with the stalks of that subscheme. It is used to check regularity of stalks chart by chart, and is cited in the construction of regular models of modular curves over a discrete valuation ring, notably in establishing regularity of stalks away from the crossing points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsOpenImmersion_isRegularLocalRing_stalk_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsOpenImmersion.isRegularLocalRing_stalk_iff
    {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (u : U) :
    IsRegularLocalRing (X.presheaf.stalk (i.base u)) ↔ IsRegularLocalRing (U.presheaf.stalk u) := by sorry
