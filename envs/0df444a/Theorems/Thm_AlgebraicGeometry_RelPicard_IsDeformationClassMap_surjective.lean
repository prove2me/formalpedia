-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_surjective
-- name    : AlgebraicGeometry.RelPicard.IsDeformationClassMap.surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/1330399e-1e3b-5f6e-9adc-11d9cef687c2
-- title:
--   Surjectivity of the deformation-class map δ
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, $c : C \to \operatorname{Spec} R$ a morphism, and $\varepsilon$ an element of `SchemeHomOver (𝟙 (Spec (.of R))) c`, that is, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $A$ be a commutative $R$-algebra and let $\mathcal V$ be a two-affine open cover of $C$: a pair of affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Let $\delta$ be any function from `RigKerDualNumber c ε A` — the quotient, by the setoid `RigKerDualNumber.setoid`, of the rigidified line bundles $M$ on the base change of $c$ along $\operatorname{Spec} A[\epsilon] \to \operatorname{Spec} R$ whose pullback along the dual-number reduction has underlying module isomorphic to the unit — to `H1StructureSheaf c A 𝒱`, the first cohomology of the two-chart Čech complex of the structure sheaf for the cover $\mathcal V$ pulled back to $C \times_{\operatorname{Spec} R} \operatorname{Spec} A$, a quotient of $\Gamma(C_A, U_0 \sqcap U_1)$. Assume `IsDeformationClassMap c ε A 𝒱 δ`: for every such $M$, every pair of sections $e_0$ over $U_0$ and $e_1$ over $U_1$ of the pulled-back cover over $A[\epsilon]$ which are frames there (in the sense that multiplication by them on any smaller open is bijective), and every $f \in \Gamma(C_A, U_0 \sqcap U_1)$, if the restrictions to the overlap satisfy $e_1|_{U_0 \cap U_1} = (1 + \epsilon\, \iota f) \cdot e_0|_{U_0 \cap U_1}$, where $1 + \epsilon\, \iota f$ is the unit `oneAddEpsMul A 𝒱 c f`, then $\delta$ of the class of $M$ is the class of $f$. The conclusion is that $\delta$ is surjective.
--
--   This is the surjectivity half of the identification of $\ker\bigl(\operatorname{Pic}_{C/R,\varepsilon}(A[\epsilon]) \to \operatorname{Pic}_{C/R,\varepsilon}(A)\bigr)$ with the Čech group $\check H^1(\mathcal V_A, \mathcal O)$, the coefficient-ring version of the computation of the tangent space of the relative Picard functor; no hypothesis on $A$ beyond being an $R$-algebra is imposed. It feeds the statements [`AlgebraicGeometry.RelPicard.RepresentsRelSubPic.deformationClass_kerPoints_bijective_additive_natural`](thm.html#AlgebraicGeometry.RelPicard.RepresentsRelSubPic.deformationClass_kerPoints_bijective_additive_natural) and [`AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPoints_baseChange_surjective_and_fibre`](thm.html#AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPoints_baseChange_surjective_and_fibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.RelPicard.IsDeformationClassMap.surjective
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
    {A : Type u} [CommRing A] [Algebra R A] {𝒱 : C.TwoAffineOpenCover}
    {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδ : IsDeformationClassMap c ε A 𝒱 δ) :
    Function.Surjective δ := by sorry
