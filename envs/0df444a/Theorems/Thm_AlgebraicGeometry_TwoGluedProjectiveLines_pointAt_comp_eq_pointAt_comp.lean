-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_pointAt_comp_eq_pointAt_comp
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.pointAt_comp_eq_pointAt_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/59c22459-7e20-5049-8b5b-18677f6d4bfa
-- title:
--   Matching places give equal κ-points of the ambient scheme
-- statement:
--   Let $\kappa$ be an algebraically closed field and let $x\colon X\to\operatorname{Spec}\kappa$ be a scheme over $\kappa$. Let $M_1,M_2$ be curve models of $\operatorname{RatFunc}\kappa$ over $\kappa$, that is, integral schemes $M_i.C$ equipped with a proper, smooth of relative dimension $1$ structure morphism $M_i.\mathtt{toBase}\colon M_i.C\to\operatorname{Spec}\kappa$, a ring isomorphism of $\operatorname{RatFunc}\kappa$ with the function field of $M_i.C$ compatible with the map induced by the structure morphism, a bijection $\mathtt{placeOfPoint}$ from the closed points of $M_i.C$ onto the places of $\operatorname{RatFunc}\kappa$ over $\kappa$ (valuation subrings, not the whole field, containing the image of $\kappa$ and principal) matching stalks with valuation subrings, and the property that every finite set of points lies in one affine open. Let $i_1\colon M_1.C\to X$ be a closed immersion and $i_2\colon M_2.C\to X$ any morphism, both over $\kappa$ in the sense $i_1\circ x$-composite $i_1\ggg x=M_1.\mathtt{toBase}$ and $i_2\ggg x=M_2.\mathtt{toBase}$ (diagrammatic order). Let $c,d\in\kappa$ and suppose that the underlying map of $i_1$ sends the closed point of $M_1.C$ corresponding under $\mathtt{placeEquiv}$ to the place of $\operatorname{RatFunc}\kappa$ attached to the irreducible polynomial $X-c$ to the same point of $X$ as the underlying map of $i_2$ sends the closed point of $M_2.C$ corresponding to the place attached to $X-d$. Then the $\kappa$-point $\mathtt{pointAt}\,M_1\,c$, namely the section of $M_1.\mathtt{toBase}$ corresponding under $\mathtt{pointEquivPlace}$ to the place at $X-c$, followed by $i_1$, equals the section $\mathtt{pointAt}\,M_2\,d$ followed by $i_2$, as morphisms $\operatorname{Spec}\kappa\to X$.
--
--   This is the point-theoretic step identifying, inside a scheme obtained by gluing two projective lines at a point, the two $\kappa$-rational points lying at prescribed places $t=c$ and $t=d$ on the two components: agreement of the underlying topological points forces agreement of the morphisms from $\operatorname{Spec}\kappa$. It is used in the construction of node unit modules for two glued projective lines, in [`AlgebraicGeometry.TwoGluedProjectiveLines.exists_isInvertible_isNodeUnitModule`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.exists_isInvertible_isNodeUnitModule) and [`AlgebraicGeometry.TwoGluedProjectiveLines.exists_isNodeUnitModule_pullback_of_pullback_iso_unit`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.exists_isNodeUnitModule_pullback_of_pullback_iso_unit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_pointAt_comp_eq_pointAt_comp.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
  NeronModelInfra AlgebraicGeometry.TwoGluedProjectiveLines

theorem AlgebraicGeometry.TwoGluedProjectiveLines.pointAt_comp_eq_pointAt_comp
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of κ))
    (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X) [IsClosedImmersion i₁]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase) (c d : κ)
    (h : i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ c)).1 =
      i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ d)).1) :
    (pointAt M₁ c).1 ≫ i₁ = (pointAt M₂ d).1 ≫ i₂ := by sorry
