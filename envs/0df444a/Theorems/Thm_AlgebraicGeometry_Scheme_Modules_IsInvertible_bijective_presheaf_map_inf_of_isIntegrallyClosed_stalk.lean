-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/8ed2593b-9109-5d0d-9117-9b72d781df34
-- title:
--   Hartogs extension for sections of an invertible module
-- statement:
--   Let $X$ be a locally Noetherian scheme and let $V, U$ be open subsets of $X$. Assume that for every point $x$ of $X$ lying in $V$ the local ring $\mathcal{O}_{X,x}$ (the stalk of the structure sheaf) is a domain and is integrally closed, and assume that every point $x \in V$ whose local ring has Krull dimension at most $1$ already lies in $U$. Let $L$ be an $\mathcal{O}_X$-module on $X$ which is invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`: every point of $X$ has an open neighbourhood $W$ such that the pullback of $L$ along the inclusion $W \hookrightarrow X$ is isomorphic to the unit module on $W$, i.e. to $\mathcal{O}_W$ viewed as a module over itself. Then the restriction map on sections of $L$ associated with the inclusion $V \sqcap U \le V$, namely $\Gamma(V, L) \to \Gamma(V \cap U, L)$, is bijective.
--
--   This is the algebraic Hartogs extension principle in its line-bundle form: on a normal locally Noetherian scheme, sections of an invertible module extend uniquely across a closed subset of codimension at least two. It is the engine for extending morphisms and isomorphisms of invertible modules across such a subset, and is cited by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk); the case $L = \mathcal{O}_X$ is [`AlgebraicGeometry.Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk`](thm.html#AlgebraicGeometry.Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
    {X : Scheme.{u}} [IsLocallyNoetherian X] (V U : X.Opens)
    (hV : ∀ x : X, x ∈ V → IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (hU : ∀ x : X, x ∈ V → ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Function.Bijective (L.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op) := by sorry
