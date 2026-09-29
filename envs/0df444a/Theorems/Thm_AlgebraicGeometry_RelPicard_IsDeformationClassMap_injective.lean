-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_injective
-- name    : AlgebraicGeometry.RelPicard.IsDeformationClassMap.injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/f16b426a-a443-5a0e-be18-fdf19640b07a
-- title:
--   Injectivity of the deformation-class map
-- statement:
--   Fix a commutative ring $R$, a scheme $C$ with a morphism $c : C \to \operatorname{Spec} R$, and a section $\varepsilon$ of $c$, that is a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity. Let $A$ be a commutative $R$-algebra and let $\mathcal V$ be a two-affine open cover of $C$: two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Let $\delta$ be a function from `RigKerDualNumber c ε A`, the quotient of the set of rigidified line bundles $M$ over $C \times_{\operatorname{Spec} R} \operatorname{Spec} A[\epsilon]$ whose pullback along the dual-number reduction has underlying module isomorphic to that of the unit bundle over $A$, to the first cohomology `H1StructureSheaf c A 𝒱` of the two-chart Čech complex of the structure sheaf for the cover $\mathcal V$ pulled back to $C \times_{\operatorname{Spec} R} \operatorname{Spec} A$. Assume `IsDeformationClassMap c ε A 𝒱 δ`: for every such $M$, every section $e_0$ of $M$ over the pullback of $U_0$ and $e_1$ over the pullback of $U_1$ (to the $A[\epsilon]$-base change), and every element $f$ of the overlap ring of the $A$-cover, if $e_0$ and $e_1$ are frames on their respective opens (multiplication by them gives bijections from functions to sections on all smaller opens) and the restriction of $e_1$ to the overlap equals $(1 + \epsilon \cdot f)$ times the restriction of $e_0$, then $\delta$ of the class of $M$ is the class of $f$. The conclusion is that $\delta$ is injective.
--
--   This is the injectivity half of the identification of $\ker\bigl(\operatorname{Pic}_{C/R,\varepsilon}(A[\epsilon]) \to \operatorname{Pic}_{C/R,\varepsilon}(A)\bigr)$ with the first Čech cohomology of the structure sheaf on $C_A$ for a two-chart cover, used in the computation of the tangent space of the relative Picard functor. It feeds the bijectivity and base-change statements for the dual-number kernel in the representability of the relative Picard scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_injective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.RelPicard.IsDeformationClassMap.injective
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
    {A : Type u} [CommRing A] [Algebra R A] {𝒱 : C.TwoAffineOpenCover}
    {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδ : IsDeformationClassMap c ε A 𝒱 δ) :
    Function.Injective δ := by sorry
