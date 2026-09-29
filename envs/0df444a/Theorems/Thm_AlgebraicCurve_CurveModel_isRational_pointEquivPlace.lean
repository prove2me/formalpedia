-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_isRational_pointEquivPlace
-- name    : AlgebraicCurve.CurveModel.isRational_pointEquivPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/2c1e3e6c-5763-52d9-8fd3-0122ce4a9a9e
-- title:
--   Places of K-points on a curve model are rational
-- statement:
--   Let $K$ be an algebraically closed field, $L$ a field that is a $K$-algebra, and let $M$ be a curve model of $L$ over $K$: a scheme $C = M.C$ over $K$ through a structure morphism $M.\mathrm{toBase} \colon C \to \operatorname{Spec} K$ which is integral, proper and smooth of relative dimension $1$, together with a ring isomorphism $M.\mathrm{ffEquiv} \colon L \cong C$'s function field carrying $\operatorname{algebraMap}_{K,L}(a)$ to the image of $a$ under the germ at the generic point of the structure morphism, a bijection $M.\mathrm{placeOfPoint}$ from the closed points of $C$ onto the places of $L$ over $K$ (a place being a valuation subring of $L$ containing the image of $K$, different from all of $L$, and a principal ideal ring), such that for each closed point the image in $L$, under $M.\mathrm{ffEquiv}^{-1}$, of the stalk of $C$ at that point is exactly the valuation subring of the associated place, and with every finite subset of $C$ contained in an affine open. Let $x$ be a section of the structure morphism, i.e. a morphism $\operatorname{Spec} K \to C$ composing with $M.\mathrm{toBase}$ to the identity. Then the place $M.\mathrm{pointEquivPlace}(x)$ of $L$ over $K$, obtained by passing from $x$ to the corresponding closed point of $C$ and then applying $M.\mathrm{placeOfPoint}$, is rational: the structure map from $K$ to the residue field of its valuation subring is surjective.
--
--   This is the classical statement that on a complete non-singular curve over an algebraically closed field the valuation attached to a rational point has residue field the base field. It is used in the project wherever local parameters and orders of vanishing at $K$-points of modular curve models are read off from the function field, for instance in the comparison of meromorphic orders with valuations at places and in the analysis of stalks of $X_H$-models at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_isRational_pointEquivPlace.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u v

theorem AlgebraicCurve.CurveModel.isRational_pointEquivPlace
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : AlgebraicCurve.CurveModel K L)
    (x : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    (M.pointEquivPlace x).IsRational := by sorry
