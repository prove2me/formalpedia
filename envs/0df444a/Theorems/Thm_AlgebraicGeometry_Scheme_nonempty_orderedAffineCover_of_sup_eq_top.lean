-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_sup_eq_top
-- name    : AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_sup_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/5656e836-6717-599a-8505-64b40c7e6e08
-- title:
--   Quasi-compact opens carry finite ordered affine covers
-- statement:
--   Let $X$ be a scheme and let $U,V$ be open subsets of $X$ with $U \sqcup V = \top$, i.e. $U \cup V = X$. Assume given two data of the form `Scheme.OrderedAffineCover`: one, $\mathfrak{X}$, for $X$ itself, and one, $\mathfrak{W}$, for the open subscheme $U \sqcap V$ associated with the intersection $U \cap V$. Here an `OrderedAffineCover` of a scheme $Y$ consists of an index type in the same universe, equipped with a `Fintype` and a `LinearOrder` structure, together with a family of open subsets of $Y$ indexed by it, each of which is an affine open, whose supremum is the whole of $Y$. The conclusion is that the type of such data for the open subscheme attached to $U$ is nonempty: there exist a finite linearly ordered index type and a family of affine open subsets of the scheme $U$ whose supremum is $\top$. Only the existence is asserted; no compatibility with $\mathfrak{X}$ or $\mathfrak{W}$, and no ordering relation between the charts, is claimed.
--
--   This is the point-set input to the alternating Čech machinery: it says that an open subset $U$ of a scheme which together with $V$ covers $X$ is quasi-compact as soon as $X$ and $U \cap V$ are, and hence admits a finite affine open cover with linearly ordered index set. It is used by [`AlgebraicGeometry.OModulePresheaf.forall_subsingleton_HSucc_restrict_of_sup_eq_top`](thm.html#AlgebraicGeometry.OModulePresheaf.forall_subsingleton_HSucc_restrict_of_sup_eq_top) in the Mayer–Vietoris style argument, where such a cover must be produced on $U$ from covers of $X$ and of $U \cap V$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_sup_eq_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.nonempty_orderedAffineCover_of_sup_eq_top
    {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (𝔛 : X.OrderedAffineCover) (𝔚 : ((U ⊓ V : X.Opens) : Scheme.{u}).OrderedAffineCover) :
    Nonempty ((U : Scheme.{u}).OrderedAffineCover) := by sorry
