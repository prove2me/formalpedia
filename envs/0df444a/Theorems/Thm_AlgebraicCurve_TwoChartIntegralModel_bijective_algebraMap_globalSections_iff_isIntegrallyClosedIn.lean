-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn
-- name    : AlgebraicCurve.TwoChartIntegralModel.bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/a26fe0c1-f1e8-549e-bb10-cc7604ddef7b
-- title:
--   Global sections of the two-chart model equal R iff R integrally closed in F
-- statement:
--   Let $R$ be a commutative ring, $F$ a field equipped with an $R$-algebra structure, and $j \in F$ a nonzero element. Let $\mathcal{X} =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the scheme obtained as the pushout of the two morphisms `fFin R F j : XMid R F j ⟶ XFin R F j` and `fInf R F j : XMid R F j ⟶ XInf R F j`, the spectra of the inclusions `inclFin R F j` and `inclInf R F j` attached to the $R$-subalgebras `chartAlgFin R F j = chartAlg R F {j}` and `chartAlgInf R F j = chartAlg R F {j⁻¹}` of $F$, and let `toBase R F j : 𝒳 ⟶ Spec (CommRingCat.of R)` be the morphism to $\operatorname{Spec} R$ obtained from the two structure morphisms $\operatorname{Spec}$ of $R \to$ `chartAlgFin R F j` and $R \to$ `chartAlgInf R F j` by the universal property of the pushout. Give $\Gamma(\mathcal{X}, \top)$ the $R$-algebra structure `Scheme.TwoAffineOpenCover.algebraOfHom (toBase R F j) ⊤`, namely the one determined by the ring map $R \to \Gamma(\mathcal{X}, \top)$ obtained from the inverse of `Scheme.ΓSpecIso` followed by `(toBase R F j).appLE ⊤ ⊤`. The assertion is that the structure map $R \to \Gamma(\mathcal{X}, \top)$ is bijective if and only if `IsIntegrallyClosedIn R F` holds, i.e. $R \to F$ is injective and every element of $F$ integral over $R$ lies in its image.
--
--   This identifies when the two-chart integral model has structure morphism with $c_*\mathcal{O}_{\mathcal{X}} = \mathcal{O}_{\operatorname{Spec} R}$: the global sections of the glued model are exactly $R$ precisely when $R$ is integrally closed in the field $F$. It is used in the construction of a normal proper model from a family of valuation subrings, where the condition that $R$ maps isomorphically onto the global sections of the model is one of the required hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn.lean

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

theorem AlgebraicCurve.TwoChartIntegralModel.bijective_algebraMap_globalSections_iff_isIntegrallyClosedIn
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase R F j) ⊤
    Function.Bijective (algebraMap R Γ(AlgebraicCurve.TwoChartIntegralModel R F j, ⊤)) ↔
      IsIntegrallyClosedIn R F := by sorry
