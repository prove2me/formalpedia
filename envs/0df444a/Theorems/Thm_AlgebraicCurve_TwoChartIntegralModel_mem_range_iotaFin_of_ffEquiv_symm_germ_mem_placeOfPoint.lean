-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint
-- name    : AlgebraicCurve.TwoChartIntegralModel.mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/3ec1d67c-d0a5-5cb4-be74-f56e8b225103
-- title:
--   Integrality of j at a place forces the finite chart
-- statement:
--   Let $R$ be a commutative ring, $F$ a field carrying an $R$-algebra structure and $j\in F$ a nonzero element, and let $X =$ `TwoChartIntegralModel R F j` be the associated two-chart model, the pushout of the two maps $\operatorname{Spec}$ of the inclusions of the middle chart algebra into the algebras `chartAlgFin R F j` and `chartAlgInf R F j`, where `chartAlgFin R F j` is the subalgebra of elements of $F$ integral over $R[j]=$ `Algebra.adjoin R {j}`. Let $K$ be a field, $L$ a field with a $K$-algebra structure, and $M$ a `CurveModel K L`: an integral scheme $M.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} K$, a ring isomorphism `M.ffEquiv` from $L$ onto the function field of $M.C$ compatible with $K$, and a bijection `M.placeOfPoint` from the closed points of $M.C$ onto the places of $L$ over $K$ (valuation subrings of $L$ containing the image of $K$, not all of $L$, with principal ideals) such that the image in $L$ of the stalk at a closed point $x$ is exactly the valuation subring of `M.placeOfPoint x`, together with the condition that every finite set of points of $M.C$ lies in an affine open. Let $\Phi : M.C \to X$ be a morphism of schemes such that the open subscheme $\Phi^{-1}(U)$ is nonempty, where $U$ is the open image under the open immersion `ιFin R F j` of the whole of the finite chart $\operatorname{Spec}$ `chartAlgFin R F j`. Let $x$ be a closed point of $M.C$, and form the element of $L$ obtained from `jChartFin R F j` (that is, $j$ itself, viewed in `chartAlgFin R F j`) by passing to a global section of the finite chart, transporting it along the open immersion to a section over $U$, pulling it back by $\Phi$ to a section over $\Phi^{-1}(U)$, taking its germ in the function field of $M.C$, and applying `M.ffEquiv.symm`. The assertion is: if this element lies in the valuation subring of `M.placeOfPoint x`, then the image $\Phi(x)$ lies in the set-theoretic range of the underlying map of `ιFin R F j`.
--
--   This is the statement that a closed point at which the pulled-back coordinate $j$ is integral for the corresponding place cannot lie only over the pole chart, the cusp locus where $1/j$ vanishes; equivalently, such a point lies over the $j$-finite chart of the two-chart model. It is used in the construction of integral models of modular curves, in particular by [`ModularCurve.XHDRLevel.exists_snd_pullback_comp_eq_of_mem_ssPlacesQExp`](thm.html#ModularCurve.XHDRLevel.exists_snd_pullback_comp_eq_of_mem_ssPlacesQExp), [`ModularCurve.XHDRModelAtP.crossingPt_mem_preimage_iotaFin`](thm.html#ModularCurve.XHDRModelAtP.crossingPt_mem_preimage_iotaFin) and [`ModularCurve.XOneP.exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.TwoChartIntegralModel.mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] (M : CurveModel K L)
    (Φ : M.C ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    [hMne : Nonempty (Scheme.Opens.toScheme (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)))]
    (x : closedPoints M.C)
    (hj : M.ffEquiv.symm (M.C.germToFunctionField (Φ ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤))
        ((Φ.app ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j))).inv (TwoChartIntegralModel.jChartFin R F j)))))
        ∈ (M.placeOfPoint x).toValuationSubring) :
    Φ.base x.1 ∈ Set.range (TwoChartIntegralModel.ιFin R F j).base := by sorry
