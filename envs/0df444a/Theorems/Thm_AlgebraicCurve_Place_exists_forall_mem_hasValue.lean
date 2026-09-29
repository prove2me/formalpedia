-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_forall_mem_hasValue
-- name    : AlgebraicCurve.Place.exists_forall_mem_hasValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/ba06d02a-e1e7-5e8e-99ba-6c5059ed451c
-- title:
--   Prescribed unit values at finitely many places
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra. A place of $F/K$, in the sense used here, is a valuation subring $\mathcal O_e \subseteq F$ containing the image of $K$ under the structure map, distinct from $F$ itself, and whose underlying ring is a principal ideal ring. Given a finite set $E$ of such places and an arbitrary function $c$ assigning to every place of $F/K$ a unit $c_e \in K^\times$ (only the values of $c$ on $E$ enter the conclusion), the theorem asserts the existence of a single element $g \in F$ such that for every $e \in E$ one has $g \in \mathcal O_e$ and the image of $g$ in the residue field $\mathcal O_e/\mathfrak m_e$ equals the image of $c_e \in K$ under the induced map from $K$ to that residue field; this is exactly the predicate `HasValue` for $e$, $g$ and $c_e$. No separability, perfectness, finiteness or residue-degree hypothesis is imposed on $K$ or $F$.
--
--   This is the value form of the Artin–Whaples approximation theorem for the places of an arbitrary field extension: a function regular at each of finitely many places and taking prescribed non-zero constant values there. It supplies the global functions used in the analysis of points and Hecke correspondences on the Néron models attached to modular curves at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_forall_mem_hasValue.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_forall_mem_hasValue
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (E : Finset (Place K F)) (c : Place K F → Kˣ) :
    ∃ g : F, ∀ e ∈ E, e.HasValue g (c e) := by sorry
