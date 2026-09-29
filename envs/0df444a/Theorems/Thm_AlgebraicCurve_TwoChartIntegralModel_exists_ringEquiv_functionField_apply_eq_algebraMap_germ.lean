-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_functionField_apply_eq_algebraMap_germ
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_ringEquiv_functionField_apply_eq_algebraMap_germ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/f1419397-90c2-5af2-be21-126a8673de6b
-- title:
--   Function field of the two-chart integral model is F
-- statement:
--   Let $R$ be a commutative ring, $F$ a field that is an $R$-algebra, and $j \in F$ a nonzero element. Write $A_{\mathrm{fin}} =$ `chartAlgFin R F j` for the $R$-subalgebra of elements of $F$ integral over $R[j]$ and $A_{\infty} =$ `chartAlgInf R F j` for the subalgebra of elements integral over $R[j^{-1}]$, so that `XFin R F j` $= \operatorname{Spec} A_{\mathrm{fin}}$ and `XInf R F j` $= \operatorname{Spec} A_{\infty}$, and let $\mathfrak{X} =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the pushout of the two maps from the middle chart into these, assumed to be an integral scheme, with $\iota_{\mathrm{fin}}, \iota_{\infty}$ the two chart maps into $\mathfrak{X}$ and `toBase R F j : 𝔛 ⟶ Spec R`. Assume $F$ is a fraction ring of $A_{\mathrm{fin}}$. Then there is a ring isomorphism $\varphi : F \xrightarrow{\sim} K(\mathfrak{X})$ onto the function field of $\mathfrak{X}$ such that: for every point $y$ of `XFin R F j` and every $b \in A_{\mathrm{fin}}$, $\varphi(b)$ is the image in $K(\mathfrak{X})$ of the germ at $\iota_{\mathrm{fin}}(y)$ of the section of $\mathcal{O}_{\mathfrak{X}}$ over the open image $\iota_{\mathrm{fin}}(\mathfrak{X}_{\mathrm{fin}})$ corresponding to $b$ under the inverse of $\Gamma(\operatorname{Spec} A_{\mathrm{fin}}) \cong A_{\mathrm{fin}}$ and the inverse of the section isomorphism of the open immersion $\iota_{\mathrm{fin}}$; the same statement for every point $y$ of `XInf R F j` and every $b \in A_{\infty}$ along $\iota_{\infty}$; and $\varphi(\mathrm{algebraMap}_{R,F}(r))$ is the germ at the generic point of the global section of $\mathcal{O}_{\mathfrak{X}}$ pulled back from $r \in R$ along `toBase R F j`, for every $r \in R$.
--
--   This identifies the function field of the two-chart integral model with $F$ in a way compatible with both chart dictionaries and with the constants coming from the base $\operatorname{Spec} R$, which is what makes the local rings of $\mathfrak{X}$ comparable to valuation subrings of $F$. It is used in the analysis of the charts of a smooth model over a discrete valuation ring and in the construction of a normal proper model with prescribed valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_functionField_apply_eq_algebraMap_germ.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_ringEquiv_functionField_apply_eq_algebraMap_germ
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)]
    (hfrac : IsFractionRing ↥(chartAlgFin R F j) F) :
    ∃ φ : F ≃+* (AlgebraicCurve.TwoChartIntegralModel R F j).functionField,
      (∀ (y : ↥(XFin R F j)) (b : ↥(chartAlgFin R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom b)))) ∧
      (∀ (y : ↥(XInf R F j)) (b : ↥(chartAlgInf R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιInf R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) ((ιInf R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιInf R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom b)))) ∧
      (∀ r : R, φ (algebraMap R F r) = SemistableModel.baseToFunctionField (toBase R F j) r) := by sorry
