-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_forall_iff_mem_localRing_and_forall_iff_exists_mem_maximalIdeal
-- name    : AlgebraicCurve.TwoChartIntegralModel.forall_iff_mem_localRing_and_forall_iff_exists_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/f32b67ba-f6aa-5616-8d5a-21312295fec3
-- title:
--   Chart criterion for the local ring and maximal ideal at a point
-- statement:
--   Let $R$ be a commutative ring, $F$ a field with an $R$-algebra structure, and $j \in F$ nonzero. Write $A_{\mathrm{fin}} =$ `chartAlgFin R F j` for the $R$-subalgebra of $F$ of elements integral over $R[j]$, and $A_\infty =$ `chartAlgInf R F j` for the elements integral over $R[j^{-1}]$, with affine charts $X_{\mathrm{fin}} = \operatorname{Spec} A_{\mathrm{fin}}$ and $X_\infty = \operatorname{Spec} A_\infty$ and chart morphisms `ιFin R F j`, `ιInf R F j` into $\mathfrak X =$ `TwoChartIntegralModel R F j`, the pushout defining the two-chart model. Assume $\mathfrak X$ is integral and let $\varphi : F \simeq K(\mathfrak X)$ be a ring isomorphism onto its function field which, on both charts, sends each $b \in A_{\mathrm{fin}}$ (resp. $b \in A_\infty$) to the image in $K(\mathfrak X)$ of the germ at the image point of the section of $\mathfrak X$ over the open image of the chart corresponding to $b$. Fix a point $x$ of $\mathfrak X$ and $f \in F$. The conclusion is a conjunction of two equivalences. First: $f$ can be written chartwise as a quotient, i.e. for every $y \in X_{\mathrm{fin}}$ with image $x$ there are $g, h \in A_{\mathrm{fin}}$ with $h \notin y$ and $f h = g$ in $F$, and likewise for every $y \in X_\infty$ over $x$ with $g, h \in A_\infty$, if and only if $f$ lies in `SemistableModel.localRing`, the subring of $F$ that is the image under $\varphi^{-1}$ of the canonical map $\mathcal O_{\mathfrak X,x} \to K(\mathfrak X)$. Second: the same chartwise conditions with the additional requirement $g \in y$ hold if and only if $f = \varphi^{-1}(s)$ for some $s$ in the image of the maximal ideal of $\mathcal O_{\mathfrak X,x}$ in $K(\mathfrak X)$.
--
--   This is the dictionary translating the affine-chart description of the two-chart integral model into honest stalk data: membership in the local ring at $x$, viewed inside $F$, and in its maximal ideal, both expressed by chartwise conditions of the form $f = g/h$ with $h$ outside the relevant prime. It rests on the identification of the stalks of $\mathfrak X$ at points coming from either chart with the localisation of the chart algebra at the corresponding prime, and it is used in the construction of étale coordinates on the model and in the existence statement for normal proper models with prescribed valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_forall_iff_mem_localRing_and_forall_iff_exists_mem_maximalIdeal.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel IsLocalRing

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.forall_iff_mem_localRing_and_forall_iff_exists_mem_maximalIdeal
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)]
    (φ : F ≃+* (AlgebraicCurve.TwoChartIntegralModel R F j).functionField)
    (hφFin : ∀ (y : ↥(XFin R F j)) (b : ↥(chartAlgFin R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom b))))
    (hφInf : ∀ (y : ↥(XInf R F j)) (b : ↥(chartAlgInf R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιInf R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) ((ιInf R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιInf R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom b))))
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (f : F) :
    (((∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
          ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
       (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
          ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F))) ↔
      f ∈ SemistableModel.localRing (AlgebraicCurve.TwoChartIntegralModel R F j) φ x) ∧
    (((∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
          ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
       (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
          ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F))) ↔
      ∃ s ∈ maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x),
        f = φ.symm (algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField s)) := by sorry
