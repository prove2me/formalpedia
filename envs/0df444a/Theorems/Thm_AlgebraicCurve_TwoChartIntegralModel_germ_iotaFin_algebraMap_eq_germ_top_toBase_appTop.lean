-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_germ_iotaFin_algebraMap_eq_germ_top_toBase_appTop
-- name    : AlgebraicCurve.TwoChartIntegralModel.germ_iotaFin_algebraMap_eq_germ_top_toBase_appTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/21f58500-af41-59c0-b8d0-ae09e953bddf
-- title:
--   Germs of a constant agree through chart and base
-- statement:
--   Let $R$ be a commutative ring, $F$ a field carrying an $R$-algebra structure and $j \in F$ a nonzero element. Write $C =$ `chartAlgFin R F j` for the $R$-subalgebra of $F$ consisting of those $x \in F$ that are integral over $R[j] =$ `Algebra.adjoin R {j}`, so that `XFin R F j` $= \operatorname{Spec} C$, and let $\mathcal X =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the pushout of the two maps `fFin R F j` and `fInf R F j` out of `XMid R F j`, with `ιFin R F j : XFin R F j ⟶ 𝒳` the corresponding chart and `toBase R F j : 𝒳 ⟶ Spec R` the map induced on the pushout by $\operatorname{Spec}$ of the structure morphisms $R \to C$ and $R \to$ `chartAlgInf R F j`. Given a point $z$ of $\mathcal X$, a point $y$ of $\operatorname{Spec} C$ with $(\iota_{\mathrm{fin}})(y) = z$, and $r \in R$, the theorem asserts an equality in the stalk $\mathcal O_{\mathcal X, z}$: the germ at $z$, taken on the open set $\iota_{\mathrm{fin}} ''^{\mathrm U} \top$ (the point $z$ lying in it via $y$), of the section of $\mathcal O_{\mathcal X}$ over that open set obtained from $\operatorname{algebraMap}_{R \to C}(r)$ by the inverse of `Scheme.ΓSpecIso` and the inverse of the isomorphism `(ιFin R F j).appIso ⊤`, coincides with the germ at $z$ of the global section $(\mathrm{toBase})^{\sharp}$ applied to the image of $r$ under the inverse of `Scheme.ΓSpecIso` for $\operatorname{Spec} R$.
--
--   This reconciles the two ways of writing 'the germ of the constant $r$' at a point of the chart $\operatorname{Spec} C$ of the two-chart integral model: through the chart algebra $C$ and through the structure morphism to $\operatorname{Spec} R$. It is used in the stalk-level comparisons of the modular curve constructions, where local data at a point are described at once in terms of $C$ and in terms of the base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_germ_iotaFin_algebraMap_eq_germ_top_toBase_appTop.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.germ_iotaFin_algebraMap_eq_germ_top_toBase_appTop
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (y : ↥(XFin R F j)) (hy : (ιFin R F j).base y = z) (r : R) :
    ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom
        (((ιFin R F j).appIso ⊤).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom (algebraMap R ↥(chartAlgFin R F j) r))) =
      ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
        (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by sorry
