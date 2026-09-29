-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/07994105-50c9-56bd-a732-b9de7d27847e
-- title:
--   Global sections of the two-chart integral model
-- statement:
--   Let $R$ be a commutative ring, $F$ a field equipped with an $R$-algebra structure, and $j \in F$ an element, assumed nonzero (through the instance `Fact (j ≠ 0)`). For a subset $S \subseteq F$ write $\mathrm{chartAlg}\,R\,F\,S$ for the $R$-subalgebra of $F$ consisting of the elements of $F$ that are integral over the $R$-subalgebra $\mathrm{Algebra.adjoin}\,R\,S$; put $A_{\mathrm{fin}} =$ `chartAlgFin R F j` $= \mathrm{chartAlg}\,R\,F\,\{j\}$ and $A_{\infty} =$ `chartAlgInf R F j` $= \mathrm{chartAlg}\,R\,F\,\{j^{-1}\}$. The scheme [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the pushout of the two morphisms $f_{\mathrm{fin}} : X_{\mathrm{mid}} \to X_{\mathrm{fin}}$ and $f_{\infty} : X_{\mathrm{mid}} \to X_{\infty}$ obtained by applying $\operatorname{Spec}$ to the algebra maps `inclFin` and `inclInf`, and `toBase R F j` is the morphism to $\operatorname{Spec} R$ determined on the two charts by the structure maps $R \to A_{\mathrm{fin}}$ and $R \to A_{\infty}$. The ring $\Gamma(X, \top)$ of global sections is given the $R$-algebra structure induced by `toBase R F j` via `Scheme.TwoAffineOpenCover.algebraOfHom`, that is, by the ring map $R \cong \Gamma(\operatorname{Spec} R, \top) \to \Gamma(X, \top)$. The assertion is that there exists an $R$-algebra isomorphism $e : \Gamma(X, \top) \xrightarrow{\sim} A_{\mathrm{fin}} \sqcap A_{\infty}$ onto the intersection of the two chart subalgebras of $F$, such that for every global section $s$ the element $e(s)$, viewed in $F$, coincides with the image in $F$ of the restriction of $s$ along the chart morphism `ιFin R F j`, under the identification $\Gamma(\operatorname{Spec} A_{\mathrm{fin}}, \top) \cong A_{\mathrm{fin}}$ given by `Scheme.ΓSpecIso`, and likewise coincides with the image in $F$ of the restriction of $s$ along `ιInf R F j` under $\Gamma(\operatorname{Spec} A_{\infty}, \top) \cong A_{\infty}$.
--
--   This is the sheaf property of the two-chart integral model in algebraic form: the global-sections functor turns the defining pushout square of schemes into a fibre product of rings, and since all chart rings sit inside $F$ that fibre product is the intersection $A_{\mathrm{fin}} \cap A_{\infty}$, compatibly with restriction to each chart. It is used to identify global sections concretely, in particular by [`AlgebraicCurve.TwoChartIntegralModel.bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn`](thm.html#AlgebraicCurve.TwoChartIntegralModel.bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn), which characterises when the structure map $R \to \Gamma(X, \top)$ is bijective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_globalSections_chartAlgFin_inf_chartAlgInf
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase R F j) ⊤
    ∃ e : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤) ≃ₐ[R]
        ↥(chartAlgFin R F j ⊓ chartAlgInf R F j),
      (∀ s, ((e s : ↥(chartAlgFin R F j ⊓ chartAlgInf R F j)) : F) =
        ((Scheme.ΓSpecIso (CommRingCat.of (chartAlgFin R F j))).hom ((ιFin R F j).appTop s) :
          chartAlgFin R F j)) ∧
      (∀ s, ((e s : ↥(chartAlgFin R F j ⊓ chartAlgInf R F j)) : F) =
        ((Scheme.ΓSpecIso (CommRingCat.of (chartAlgInf R F j))).hom ((ιInf R F j).appTop s) :
          chartAlgInf R F j)) := by sorry
