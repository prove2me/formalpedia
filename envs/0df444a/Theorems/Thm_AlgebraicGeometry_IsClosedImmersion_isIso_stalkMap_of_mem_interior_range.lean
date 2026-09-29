-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_isIso_stalkMap_of_mem_interior_range
-- name    : AlgebraicGeometry.IsClosedImmersion.isIso_stalkMap_of_mem_interior_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/c4b5d477-04fc-58c9-9149-11a7a0f1b41e
-- title:
--   Stalk isomorphism for closed immersions at interior points
-- statement:
--   Let $C$ and $X$ be schemes and let $i \colon C \to X$ be a morphism of schemes which is a closed immersion, with $X$ reduced. Let $c$ be a point of $C$ whose image $i(c)$ lies in the topological interior of the set-theoretic range of $i$ in $X$. Then the induced map on stalks $i^{\#}_c \colon \mathcal{O}_{X, i(c)} \to \mathcal{O}_{C, c}$, written `i.stalkMap c`, is an isomorphism of local rings (more precisely, an isomorphism in the relevant category of commutative rings). No hypothesis is placed on $C$ beyond its being a scheme; reducedness is assumed for the target $X$ only, and the interior condition is the only restriction on the point $c$.
--
--   A closed immersion always induces surjections on stalks; the point of the statement is that over a reduced target the stalk map is moreover injective at points interior to the image, so that locally near such a point $C$ and $X$ are indistinguishable. The typical situation is $X = C \cup C'$ reduced with $C'$ closed and $i(c) \notin C'$. It is used in the project to show that the locus where the stalks of a scheme fail to be regular local rings is finite under a stalk-isomorphism hypothesis, via [`AlgebraicGeometry.finite_setOf_not_isRegularLocalRing_stalk_of_isIso_stalkMap`](thm.html#AlgebraicGeometry.finite_setOf_not_isRegularLocalRing_stalk_of_isIso_stalkMap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_isIso_stalkMap_of_mem_interior_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.IsClosedImmersion.isIso_stalkMap_of_mem_interior_range
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] [IsReduced X]
    (c : C) (hc : i c ∈ interior (Set.range i)) : IsIso (i.stalkMap c) := by sorry
