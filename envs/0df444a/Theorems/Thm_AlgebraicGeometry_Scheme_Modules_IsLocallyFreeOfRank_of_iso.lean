-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso
-- name    : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/9e40b55c-5b78-584c-9a98-0efbdd759978
-- title:
--   Local freeness of rank n transports along isomorphisms
-- statement:
--   Let $X$ be a scheme, $n$ a natural number, and let $M$ and $N$ be objects of the category `X.Modules` of sheaves of $\mathcal O_X$-modules. Suppose given an isomorphism $e : M \cong N$ in that category, and suppose that $M$ satisfies `Scheme.Modules.IsLocallyFreeOfRank n`, that is: for every point $x$ of $X$ there is an open subscheme $U \subseteq X$ with $x \in U$ such that the pullback of $M$ along the inclusion $U \to X$, under the functor `Scheme.Modules.pullback U.ι`, is isomorphic to the free sheaf of modules `SheafOfModules.free` on the index type `ULift (Fin n)` (the predicate asks only that the type of such isomorphisms be nonempty, no compatibility being imposed between the trivializations at different points). The conclusion is that $N$ satisfies the same predicate `Scheme.Modules.IsLocallyFreeOfRank n`: every point of $X$ has an open neighbourhood on which the restriction of $N$ admits an isomorphism with the free sheaf of modules of rank $n$.
--
--   This is the statement that being locally free of rank $n$ depends only on the isomorphism class of a sheaf of modules. It is used throughout the work on the relative Picard functor, where local freeness of a given sheaf is obtained by identifying it up to isomorphism with a sheaf already known to be locally free, for instance in [`AlgebraicGeometry.RelPicard.shortExact_map_pushforward_thickening`](thm.html#AlgebraicGeometry.RelPicard.shortExact_map_pushforward_thickening) and in the statements comparing determinants of pushforwards.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.of_iso
    {X : Scheme.{u}} {n : ℕ} {M N : X.Modules} (e : M ≅ N) (h : Scheme.Modules.IsLocallyFreeOfRank n M) :
    Scheme.Modules.IsLocallyFreeOfRank n N := by sorry
