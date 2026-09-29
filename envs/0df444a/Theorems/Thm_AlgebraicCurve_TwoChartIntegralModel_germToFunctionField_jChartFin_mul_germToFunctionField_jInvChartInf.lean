-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_germToFunctionField_jChartFin_mul_germToFunctionField_jInvChartInf
-- name    : AlgebraicCurve.TwoChartIntegralModel.germToFunctionField_jChartFin_mul_germToFunctionField_jInvChartInf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/084149f4-a45a-58b6-8e58-382f862da0f3
-- title:
--   Germs of j and j⁻¹ multiply to 1
-- statement:
--   Let $R$ be a commutative ring, $F$ a field which is an $R$-algebra, and $j \in F$ a nonzero element. Write $A_{\mathrm{fin}} =$ `chartAlgFin R F j` for the $R$-subalgebra of $F$ consisting of the elements of $F$ integral over $R[j]$, and $A_{\infty} =$ `chartAlgInf R F j` for the subalgebra of elements integral over $R[j^{-1}]$; the scheme `TwoChartIntegralModel R F j` is the pushout of the two morphisms $\operatorname{Spec}$ of the inclusions of $A_{\mathrm{fin}}$ and of $A_{\infty}$ into their common overlap algebra, and `ιFin`, `ιInf` are the two chart morphisms from $\operatorname{Spec} A_{\mathrm{fin}}$ and $\operatorname{Spec} A_{\infty}$ into it, each an open immersion (`''ᵁ ⊤` denoting the image of the whole space and `appIso` the resulting isomorphism on sections). Let $Y$ be an integral scheme and $f \colon Y \to$ `TwoChartIntegralModel R F j` a morphism such that the preimages under $f$ of the two chart opens are both nonempty. The element $j \in A_{\mathrm{fin}}$, read as a global section of $\operatorname{Spec} A_{\mathrm{fin}}$ via the inverse of `Scheme.ΓSpecIso`, transported to a section over the finite chart open and pulled back by $f$ to a section over its preimage in $Y$, has a germ at the generic point of $Y$, i.e. an element of the function field of $Y$; similarly for $j^{-1} \in A_{\infty}$ on the other chart. The theorem asserts that the product of these two elements of the function field of $Y$ equals $1$.
--
--   This records that the two tautological chart sections of the two-chart integral model of $(F,j)$ pull back to mutually inverse rational functions on any integral scheme meeting both charts, so that the germ of the finite-chart section is a unit in the function field. It is used in the construction of the Deligne–Rapoport-style model package, in the statement that the evaluation of a polynomial lies in the image of the algebra map on a stalk together with invertibility of its image.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_germToFunctionField_jChartFin_mul_germToFunctionField_jInvChartInf.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
universe u

theorem AlgebraicCurve.TwoChartIntegralModel.germToFunctionField_jChartFin_mul_germToFunctionField_jInvChartInf
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    [hU : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)))]
    [hV : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ ((TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤)))] :
    Y.germToFunctionField (f ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤))
        (((f.app ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)).hom
          (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j))).inv
              (TwoChartIntegralModel.jChartFin R F j))))) *
      Y.germToFunctionField (f ⁻¹ᵁ ((TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤))
        (((f.app ((TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤)).hom
          (((TwoChartIntegralModel.ιInf R F j).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf R F j))).inv
              (TwoChartIntegralModel.jInvChartInf R F j))))) = 1 := by sorry
