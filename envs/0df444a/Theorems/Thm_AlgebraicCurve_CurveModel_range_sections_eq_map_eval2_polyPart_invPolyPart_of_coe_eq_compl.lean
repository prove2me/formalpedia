-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl
-- name    : AlgebraicCurve.CurveModel.range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/4530cd86-8aa1-5ec7-81b4-975668d07672
-- title:
--   Chart rings of a smooth proper model of K(T)
-- statement:
--   Let $K$ be a field and let $M$ be a `CurveModel` for the extension $K \subseteq \mathrm{RatFunc}\,K$: an integral scheme $M.C$ over $\operatorname{Spec} K$ whose structure morphism is proper and smooth of relative dimension $1$, together with a ring isomorphism $M.\mathrm{ffEquiv} : \mathrm{RatFunc}\,K \simeq M.C.\mathrm{functionField}$ over $K$, and a bijection $M.\mathrm{placeEquiv}$ from the closed points of $M.C$ to the places of $\mathrm{RatFunc}\,K$ over $K$ (valuation subrings containing $K$, not all of the field, and principal ideal rings) which matches each stalk, transported into $\mathrm{RatFunc}\,K$ along $M.\mathrm{ffEquiv}^{-1}$, with the corresponding valuation subring; every finite set of points of $M.C$ lies in an affine open. Let $U, V$ be opens of $M.C$ with $U$, $V$ and $U \sqcap V$ affine and nonempty, such that the underlying set of $U$ is the complement of the single point corresponding to the infinite place of $\mathrm{RatFunc}\,K$ and that of $V$ is the complement of the point corresponding to the place attached to the irreducible polynomial $X - 0$. Write $\iota$ for the evaluation homomorphism $K[T;T^{-1}] \to \mathrm{RatFunc}\,K$ given by $K \to \mathrm{RatFunc}\,K$ on coefficients and by the unit $X$ on $T$. Then $\iota$ is injective, and, identifying sections with rational functions via $M.\mathrm{ffEquiv}^{-1}$ composed with the map to the function field, the range of $\Gamma(M.C, U)$ is $\iota$ of [`TwoChartCech.polyPart K`](def/TwoChartCech_GluedLines.html#L19) (Laurent polynomials with only nonnegative exponents), the range of $\Gamma(M.C, V)$ is $\iota$ of [`TwoChartCech.invPolyPart K`](def/TwoChartCech_GluedLines.html#L37) (only nonpositive exponents), and the range of $\Gamma(M.C, U \sqcap V)$ is the whole range of $\iota$.
--
--   This is the statement that on a smooth proper model of the rational function field the standard two-chart cover has section rings $K[T]$, $K[T^{-1}]$ and $K[T,T^{-1}]$, pinned down inside $K(T)$ by the coordinate $X$. It is the dictionary used to compare an abstract pair of transversally glued projective lines with the explicit glued-lines Čech model, and is cited in the construction of the covering and sections isomorphisms and in the Euler-characteristic computation for that model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_TwoChartCech_GluedLines

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

theorem AlgebraicCurve.CurveModel.range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl
    (K : Type u) [Field K] [DecidableEq (RatFunc K)]
    (M : CurveModel K (RatFunc K)) (U V : M.C.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))
    [Nonempty U] [Nonempty V] [Nonempty (U ⊓ V : M.C.Opens)]
    (hUset : ((U : Set M.C)) = {(M.placeEquiv.symm (RationalFunctionField.placeInfty K)).1}ᶜ)
    (hVset : ((V : Set M.C)) = {(M.placeEquiv.symm (RationalFunctionField.placeOfPoint K 0)).1}ᶜ) :
    Function.Injective
        (LaurentPolynomial.eval₂ (algebraMap K (RatFunc K)) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)) ∧
      ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc K).toRingHom.comp
          (algebraMap Γ(M.C, U) M.C.functionField)).range =
        ((TwoChartCech.polyPart K).toSubring).map
          (LaurentPolynomial.eval₂ (algebraMap K (RatFunc K)) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)) ∧
      ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc K).toRingHom.comp
          (algebraMap Γ(M.C, V) M.C.functionField)).range =
        ((TwoChartCech.invPolyPart K).toSubring).map
          (LaurentPolynomial.eval₂ (algebraMap K (RatFunc K)) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)) ∧
      ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc K).toRingHom.comp
          (algebraMap Γ(M.C, U ⊓ V) M.C.functionField)).range =
        (LaurentPolynomial.eval₂ (algebraMap K (RatFunc K))
          (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)).range := by sorry
