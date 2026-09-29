-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
-- name    : AlgebraicCurve.CurveModel.ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/00c72afa-5b23-5be1-9b8a-f83b1ed98df8
-- title:
--   Unit sections have order zero at places of the curve model
-- statement:
--   Let $K$ be a field, $L$ a field with a $K$-algebra structure, and let $Mc$ be a curve model of $L$ over $K$: a $K$-scheme $Mc.C$ with structure morphism to $\operatorname{Spec} K$ that is integral, proper and smooth of relative dimension $1$, equipped with a ring isomorphism $Mc.\mathrm{ffEquiv} : L \cong K(Mc.C)$ restricting on $K$ to the canonical map into the function field, a bijection $Mc.\mathrm{placeOfPoint}$ from the closed points of $Mc.C$ onto the places of $L/K$ (valuation subrings of $L$ containing the image of $K$, proper, and principal ideal rings), such that for each closed point $x$ the image in $L$ of the local ring $\mathcal{O}_{Mc.C,x}$, transported along $Mc.\mathrm{ffEquiv}^{-1}$, is exactly the valuation subring of $Mc.\mathrm{placeOfPoint}(x)$, and such that every finite set of points of $Mc.C$ lies in an affine open. Let $U$ be a nonempty open subscheme of $Mc.C$, let $P$ be a closed point with $P \in U$, and let $s \in \Gamma(Mc.C, U)$ be a unit of that ring. Then the order of the element of $L$ obtained from $s$ by taking its germ at the generic point, i.e. its image under $Mc.C$'s map to the function field, and reading it in $L$ via $Mc.\mathrm{ffEquiv}^{-1}$, is $0$ at the place $Mc.\mathrm{placeOfPoint}(P)$; here the order of $f$ is $-\log$ of the value of $f$ under the adic valuation of the place.
--
--   This is the standard fact that a rational function which is invertible on an open set has neither zero nor pole at the points of that set, expressed for the places attached to closed points by a curve model. It is used in the construction of uniformisers on smooth curve models and in the local analysis of models of modular curves at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] (Mc : AlgebraicCurve.CurveModel K L)
    (U : Mc.C.Opens) (P : closedPoints Mc.C) (hP : P.1 ∈ U)
    [Nonempty (Scheme.Opens.toScheme U)] (s : Γ(Mc.C, U)) (hs : IsUnit s) :
    (Mc.placeOfPoint P).ord (Mc.ffEquiv.symm (Mc.C.germToFunctionField U s)) = 0 := by sorry
