-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_isFinite_of_isIso_stalkMap
-- name    : AlgebraicCurve.CurveModel.isFinite_of_isIso_stalkMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/b6459bdc-ccef-579a-b4b8-fc802b6b6da8
-- title:
--   Finiteness of a birational morphism to a proper curve
-- statement:
--   Let $k$ be an algebraically closed field, let $C$ be a scheme over $k$ by a morphism $c : C \to \operatorname{Spec} k$, with $C$ integral and $c$ proper. Let $F$ be a field equipped with a $k$-algebra structure and let $M$ be a `CurveModel` for $F/k$: that is, an integral scheme `M.C` together with a proper morphism `M.toBase` to $\operatorname{Spec} k$ that is smooth of relative dimension $1$, a ring isomorphism of $F$ with the function field of `M.C` compatible with the structure maps from $k$, a bijection from the closed points of `M.C` onto the places of $F$ over $k$ (valuation subrings of $F$ containing the image of $k$, distinct from all of $F$, and principal ideal rings) such that for each closed point $x$ the image of the stalk $\mathcal{O}_{M,x}$ in $F$ is exactly the valuation subring attached to $x$, and the property that every finite set of points of `M.C` lies in an affine open. Let $\nu : M.C \to C$ be a morphism over $\operatorname{Spec} k$, i.e. $\nu$ followed by $c$ equals `M.toBase`, and assume the induced map of stalks at the generic point of `M.C` is an isomorphism. Then $\nu$ is a finite morphism.
--
--   This is the instance of Zariski's main theorem needed for smooth proper models of a function field: a morphism from the model to a proper integral curve which is an isomorphism on stalks at the generic point is finite. It is used to compare sections on $C$ with their integral closures on the model, feeding the comparison of the arithmetic genus of $C$ with the genus of its model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_isFinite_of_isIso_stalkMap.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.isFinite_of_isIso_stalkMap
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C] [IsProper c]
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase)
    (hbir : IsIso (ν.stalkMap (genericPoint M.C))) :
    IsFinite ν := by sorry
