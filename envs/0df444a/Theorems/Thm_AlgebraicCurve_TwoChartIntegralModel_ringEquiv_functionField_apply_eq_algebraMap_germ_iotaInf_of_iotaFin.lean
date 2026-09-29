-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_ringEquiv_functionField_apply_eq_algebraMap_germ_iotaInf_of_iotaFin
-- name    : AlgebraicCurve.TwoChartIntegralModel.ringEquiv_functionField_apply_eq_algebraMap_germ_iotaInf_of_iotaFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/3247166d-0898-5415-a4e2-65b32c4c236a
-- title:
--   Chart compatibility at j⁻¹ follows from that at j
-- statement:
--   Fix a commutative ring $R$, a field $F$ which is an $R$-algebra, and an element $j \in F$ assumed nonzero (as a `Fact`). Write $A_{\mathrm{fin}} =$ `chartAlgFin R F j` for the $R$-subalgebra of $F$ consisting of the elements of $F$ integral over $R[j] =$ `Algebra.adjoin R {j}`, and $A_\infty =$ `chartAlgInf R F j` for the elements integral over $R[j^{-1}]$; put $X_{\mathrm{fin}} = \operatorname{Spec} A_{\mathrm{fin}}$, $X_\infty = \operatorname{Spec} A_\infty$, and let $\mathfrak X =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the pushout of the two maps `fFin R F j` and `fInf R F j` out of the middle chart, assumed here to be an integral scheme, with $\iota_{\mathrm{fin}} =$ `ιFin R F j` and $\iota_\infty =$ `ιInf R F j` the corresponding chart morphisms into $\mathfrak X$, treated as open immersions. Let $\varphi : F \simeq \Gamma$, where $\Gamma$ is the function field of $\mathfrak X$, be a ring isomorphism. The hypothesis is that for every point $y$ of $X_{\mathrm{fin}}$ and every $b \in A_{\mathrm{fin}}$, $\varphi(b)$ is the image in $\Gamma$, under the canonical map from the stalk of $\mathfrak X$ at $\iota_{\mathrm{fin}}(y)$, of the germ at $\iota_{\mathrm{fin}}(y)$ of the section of $\mathfrak X$ over the open image $\iota_{\mathrm{fin}}(X_{\mathrm{fin}})$ obtained from $b$ by the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism for $A_{\mathrm{fin}}$ followed by the inverse of the isomorphism `(ιFin R F j).appIso ⊤`. The conclusion is the same assertion with $X_{\mathrm{fin}}$, $A_{\mathrm{fin}}$, $\iota_{\mathrm{fin}}$ replaced throughout by $X_\infty$, $A_\infty$, $\iota_\infty$: for every $y$ in $X_\infty$ and $b \in A_\infty$, $\varphi(b)$ is the corresponding germ of the $j^{-1}$-chart section at $\iota_\infty(y)$.
--
--   This is the bookkeeping step which upgrades a function-field identification known to be compatible with the sections coming from the $j$-chart of the two-chart integral model to one compatible with the sections of the $j^{-1}$-chart as well, the two descriptions matching over the overlap by the gluing data defining the pushout. It feeds the construction of such an identification in [`AlgebraicCurve.TwoChartIntegralModel.exists_ringEquiv_functionField_apply_eq_algebraMap_germ`](thm.html#AlgebraicCurve.TwoChartIntegralModel.exists_ringEquiv_functionField_apply_eq_algebraMap_germ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_ringEquiv_functionField_apply_eq_algebraMap_germ_iotaInf_of_iotaFin.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.ringEquiv_functionField_apply_eq_algebraMap_germ_iotaInf_of_iotaFin
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)]
    (φ : F ≃+* (AlgebraicCurve.TwoChartIntegralModel R F j).functionField)
    (hφFin : ∀ (y : ↥(XFin R F j)) (b : ↥(chartAlgFin R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom b)))) :
    ∀ (y : ↥(XInf R F j)) (b : ↥(chartAlgInf R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιInf R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) ((ιInf R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιInf R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom b))) := by sorry
