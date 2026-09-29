-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isDeformationClassMap
-- name    : AlgebraicGeometry.RelPicard.exists_isDeformationClassMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/c70a989c-ffc0-5d4f-9ccc-b5e7ec01ebb1
-- title:
--   Existence of the deformation-class map into Čech H¹
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme with a structure morphism $c \colon C \to \operatorname{Spec} R$, and let $\varepsilon$ be an element of `SchemeHomOver (𝟙 (Spec (.of R))) c`, that is, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $A$ be a commutative $R$-algebra and let $\mathcal V$ be a two-affine open cover of $C$: two opens $U_0, U_1$, each affine, with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. The assertion is that there is a map $\delta$ from `RigKerDualNumber c ε A` — the quotient by the relevant setoid of the type of rigidified line bundles $M$ on $C \times_{\operatorname{Spec} R} \operatorname{Spec} A[\epsilon]$ (rigidified along $\varepsilon$) whose pullback along the dual-number reduction $A[\epsilon] \to A$ has underlying module isomorphic to that of the unit rigidified line bundle over $A$ — to `H1StructureSheaf c A 𝒱`, the two-chart Čech $H^1$ of the structure sheaf for the pulled-back cover $\mathcal V_A$ of $C_A = C \times_{\operatorname{Spec} R} \operatorname{Spec} A$, which satisfies `IsDeformationClassMap c ε A 𝒱 δ`: for every such bundle $M$, every $e_0 \in \Gamma(M, U_0^{\epsilon})$ and $e_1 \in \Gamma(M, U_1^{\epsilon})$ that are frames on $U_0^{\epsilon}$, resp. $U_1^{\epsilon}$ (multiplication by a section being bijective from $\Gamma(\mathcal O, W)$ onto $\Gamma(M, W)$ on all smaller opens), and every $f \in \Gamma(\mathcal O_{C_A}, U_0^{A} \sqcap U_1^{A})$ with $e_1 = (1 + \epsilon\, f) \cdot e_0$ after restriction to $U_0^{\epsilon} \sqcap U_1^{\epsilon}$ (the factor being `oneAddEpsMul A 𝒱 c f`, the image of $f$ in the dual-number thickening multiplied by $\epsilon$ and shifted by $1$), one has $\delta([M]) = [f]$ in the Čech $H^1$ quotient. No uniqueness of $\delta$ is asserted.
--
--   This is the well-definedness half of the identification of the tangent space of the rigidified relative Picard functor with $H^1$ of the structure sheaf: the Čech class of the transition function $1 + \epsilon f$ of a line bundle on the dual-number thickening depends neither on the chosen frames nor on the isomorphism class representative. It is used downstream in the comparison of Čech classes with germs and trace maps for normed modules, and in the study of the kernel points of the relative Picard scheme under base change; its proof rests on the base-change isomorphisms for the two-chart Čech cover, [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_isDeformationClassMap.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.RelPicard.exists_isDeformationClassMap
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) :
    ∃ δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱, IsDeformationClassMap c ε A 𝒱 δ := by sorry
