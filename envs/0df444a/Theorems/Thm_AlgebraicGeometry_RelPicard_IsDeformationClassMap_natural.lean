-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_natural
-- name    : AlgebraicGeometry.RelPicard.IsDeformationClassMap.natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/d37b3902-f0f7-54b1-8146-9942bad0fe17
-- title:
--   Naturality of the deformation-class map in the coefficient algebra
-- statement:
--   Fix a commutative ring $R$, a scheme $C$ with a structure morphism $c\colon C\to\operatorname{Spec}R$ and a section $\varepsilon$ of $c$ (a morphism $\operatorname{Spec}R\to C$ composing with $c$ to the identity), commutative $R$-algebras $A$ and $B$, and a two-chart cover $\mathcal V$ of $C$ by affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine. Let $\delta_A$ send the quotient set of rigidified invertible sheaves on $C\times_R\operatorname{Spec}A[\epsilon]$ whose restriction along the dual-number reduction is trivial, to the two-chart Čech $H^1$ of the structure sheaf of $C\times_R\operatorname{Spec}A$, and assume `IsDeformationClassMap`: for every such $M$, all sections $e_0$ over $U_0$ and $e_1$ over $U_1$ of $M$'s sheaf that are frames there (multiplication by structure-sheaf sections is bijective on every smaller open), and every $f$ in the overlap ring of the $A$-stage cover, if $e_1=\bigl(1+\epsilon\,\iota(f)\bigr)\cdot e_0$ on $U_0\cap U_1$ then $\delta_A[M]=[f]$; assume the same for $\delta_B$ over $B$. Let $g\colon A\to B$ be an $R$-algebra map, and let $M$, $N$ be such rigidified bundles over $A[\epsilon]$, $B[\epsilon]$ respectively. If the pullback of $M$ along the morphism induced by the $R$-algebra map $A[\epsilon]\to B[\epsilon]$ extending $g$ with $\epsilon\mapsto\epsilon$ has sheaf isomorphic to that of $N$, then $\delta_B[N]=g_*\bigl(\delta_A[M]\bigr)$, where $g_*$ is the $g$-semilinear stage map `H1stageMap` on Čech $H^1$.
--
--   This is the functoriality in the test algebra of the deformation class attached to a point of the rigidified relative Picard functor over dual numbers, i.e. naturality of the identification of the tangent space of $\mathrm{Pic}_{C/R,\varepsilon}$ with $\check H^1(\mathcal V,\mathcal O)$ in the coefficient ring. It is used in establishing that the dual-number kernel points are computed additively and compatibly with base change, and in the surjectivity/fibre analysis of base change on those kernel points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_natural.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.RelPicard.IsDeformationClassMap.natural
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
    {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] {𝒱 : C.TwoAffineOpenCover}
    {δA : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδA : IsDeformationClassMap c ε A 𝒱 δA)
    {δB : RigKerDualNumber c ε B → H1StructureSheaf c B 𝒱} (hδB : IsDeformationClassMap c ε B 𝒱 δB)
    (g : A →ₐ[R] B) (M : RigKerDualNumber.Carrier c ε A) (N : RigKerDualNumber.Carrier c ε B)
    (hMN : Nonempty ((M.1.pullbackAlong (LFP.stageHom R
        (DualNumber.lift ⟨((IsScalarTower.toAlgHom R B (DualNumber B)).comp g, DualNumber.eps),
          DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩))).L ≅ N.1.L)) :
    δB (Quotient.mk _ N) = 𝒱.H1stageMap c g (δA (Quotient.mk _ M)) := by sorry
