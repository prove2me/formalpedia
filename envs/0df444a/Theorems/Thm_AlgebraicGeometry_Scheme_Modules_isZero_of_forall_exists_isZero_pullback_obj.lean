-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj
-- name    : AlgebraicGeometry.Scheme.Modules.isZero_of_forall_exists_isZero_pullback_obj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/33f59b0f-73cc-5941-9373-0d86e7292571
-- title:
--   Vanishing of a module sheaf is a local condition
-- statement:
--   Let $X$ be a scheme (in a fixed universe) and let $M$ be an object of the category `X.Modules` of sheaves of modules over the structure sheaf of $X$. Assume that for every point $x$ of $X$ there is an open subset $U$ of $X$ (viewed as an open subscheme) such that $x \in U$ and the pullback of $M$ along the open immersion `U.ι : U ⟶ X`, i.e. $(\mathrm{pullback}\ U.\iota)(M)$ in `U.Modules`, is a zero object in the sense of `IsZero` (its identity morphism factors through, and indeed equals, the zero morphism; equivalently it is both initial and terminal). The conclusion is that $M$ itself is a zero object of `X.Modules`, again in the sense of `IsZero`. Thus a sheaf of modules on a scheme whose restriction to some open neighbourhood of each point vanishes vanishes globally; the hypothesis is exactly the existence, for each point, of one such neighbourhood, not a statement about a given cover.
--
--   This is the standard locality of vanishing for sheaves of modules: the support of a sheaf of modules is closed under the sheaf axiom, so local vanishing implies global vanishing. It is used in this development to deduce the vanishing of exterior powers $\bigwedge^m \mathcal{E}$ of a module sheaf that is locally free of rank less than $m$, via [`AlgebraicGeometry.Scheme.Modules.isZero_exteriorPower_of_isLocallyFreeOfRank`](thm.html#AlgebraicGeometry.Scheme.Modules.isZero_exteriorPower_of_isLocallyFreeOfRank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isZero_of_forall_exists_isZero_pullback_obj.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.isZero_of_forall_exists_isZero_pullback_obj
    {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsZero ((Scheme.Modules.pullback U.ι).obj M)) :
    IsZero M := by sorry
