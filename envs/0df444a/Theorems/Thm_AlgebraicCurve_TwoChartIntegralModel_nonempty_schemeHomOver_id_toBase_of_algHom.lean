-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_nonempty_schemeHomOver_id_toBase_of_algHom
-- name    : AlgebraicCurve.TwoChartIntegralModel.nonempty_schemeHomOver_id_toBase_of_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/1f517d7c-1807-5d7e-ab32-de4c970ec8fc
-- title:
--   Section of the two-chart integral model from an algebra map
-- statement:
--   Let $R$ be a commutative ring, $F$ a field equipped with an $R$-algebra structure, and $j \in F$ with $j \neq 0$. Write $A_{\mathrm{fin}} =$ `chartAlgFin R F j` and $A_\infty =$ `chartAlgInf R F j` for the $R$-subalgebras of $F$ consisting of the elements of $F$ that are integral over $R[j] =$ `Algebra.adjoin R {j}`, respectively over $R[j^{-1}] =$ `Algebra.adjoin R {j⁻¹}`; the scheme $\mathcal X =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the pushout of the two morphisms `fFin` and `fInf` out of `XMid R F j` obtained by applying $\operatorname{Spec}$ to the inclusions `inclFin` and `inclInf`, and `toBase R F j :` $\mathcal X \to \operatorname{Spec} R$ is the morphism induced on the pushout by $\operatorname{Spec}$ of the two structure maps $R \to A_{\mathrm{fin}}$ and $R \to A_\infty$. The assertion is: given an $R$-algebra homomorphism $\varphi \colon A_\infty \to R$, the type of those morphisms of schemes $s \colon \operatorname{Spec} R \to \mathcal X$ satisfying `toBase`$\,\circ\, s = \mathrm{id}_{\operatorname{Spec} R}$ (that is, `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) (toBase R F j)`) is nonempty.
--
--   This is the general form of the statement that an $R$-point of the chart at the pole $j = \infty$ cuts out a section of the two-chart integral model over the base $\operatorname{Spec} R$ — the mechanism by which the cusp at infinity is produced as a section. It is used in the construction of the integral model of $X_1(p)$ and in the production of the data for the Deligne–Rapoport style model package ([`ModularCurve.XOneP.nonempty_schemeHomOver_id_modelTo_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.nonempty_schemeHomOver_id_modelTo_twoChartModel_x1_mul) and [`ModularCurve.exists_dRModelPackage_ffPin`](thm.html#ModularCurve.exists_dRModelPackage_ffPin)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_nonempty_schemeHomOver_id_toBase_of_algHom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicCurve.TwoChartIntegralModel.nonempty_schemeHomOver_id_toBase_of_algHom
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (φ : ↥(chartAlgInf R F j) →ₐ[R] R) :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) (toBase R F j)) := by sorry
