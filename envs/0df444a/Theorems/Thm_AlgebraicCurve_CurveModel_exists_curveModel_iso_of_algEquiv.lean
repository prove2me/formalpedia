-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_curveModel_iso_of_algEquiv
-- name    : AlgebraicCurve.CurveModel.exists_curveModel_iso_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/c5a022c2-30cd-5302-9119-991f540d3d00
-- title:
--   Transport of a curve model along a K-algebra isomorphism
-- statement:
--   Let $K$ be a field and let $L$, $L'$ be fields equipped with $K$-algebra structures, and let $e : L \to L'$ be an isomorphism of $K$-algebras. Let $M$ be a `CurveModel K L`, that is: a scheme $C$ over $K$ together with a morphism $\mathrm{toBase} : C \to \operatorname{Spec} K$ such that $C$ is integral, $\mathrm{toBase}$ is proper and smooth of relative dimension $1$; a ring isomorphism $\mathrm{ffEquiv} : L \cong C$'s function field which carries $\mathrm{algebraMap}\,K\,L$ to the map $K \to C$'s function field induced by $\mathrm{toBase}$ (germ at the generic point of the pullback on global sections); a map $\mathrm{placeOfPoint}$ from the closed points of $C$ to the places of $L/K$ (valuation subrings of $L$ containing the image of $K$, proper, and principal ideal rings), required to be bijective and to satisfy, for each closed point $x$, that the image in $L$ under $\mathrm{ffEquiv}^{-1}$ of the stalk $\mathcal{O}_{C,x}$ inside the function field is exactly the valuation subring of $\mathrm{placeOfPoint}(x)$; and the condition that every finite set of points of $C$ lies in an affine open. The conclusion asserts the existence of a `CurveModel K L'` $M'$ and an isomorphism of schemes $f : M'.C \cong M.C$ with $f$ followed by $M.\mathrm{toBase}$ equal to $M'.\mathrm{toBase}$, i.e. an isomorphism over $\operatorname{Spec} K$.
--
--   This is the transport-of-structure step expressing that a smooth proper model of $L/K$ is simultaneously a model of any $K$-isomorphic function field $L'$, recorded with an isomorphism over $\operatorname{Spec} K$ rather than an equality so that it composes with further identifications of models. It is used in the construction of curve models for the Igusa function field of $X_1(p)$, in [`ModularCurve.XOneP.exists_curveModel_igusaFunctionFieldX1C_iso_fst_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_curveModel_igusaFunctionFieldX1C_iso_fst_twoChartModel_x1_mul) and its companion for the second chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_curveModel_iso_of_algEquiv.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.exists_curveModel_iso_of_algEquiv
    {K : Type u} [Field K] {L L' : Type v} [Field L] [Field L'] [Algebra K L] [Algebra K L']
    (e : L ≃ₐ[K] L') (M : AlgebraicCurve.CurveModel K L) :
    ∃ (M' : AlgebraicCurve.CurveModel K L') (f : M'.C ≅ M.C), f.hom ≫ M.toBase = M'.toBase := by sorry
