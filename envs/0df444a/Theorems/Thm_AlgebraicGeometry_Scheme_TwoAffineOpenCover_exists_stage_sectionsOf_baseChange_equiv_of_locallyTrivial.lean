-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/9f8133d2-f4f4-5e8a-8a94-ccdcadb83b6f
-- title:
--   Stagewise affine base change of chart sections
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme equipped with a two-affine open cover $\mathcal V$ (a pair of affine opens $U_0,U_1$ with $U_0\sqcup U_1$ covering $C$ and $U_0\cap U_1$ affine) and a morphism $c\colon C\to\operatorname{Spec}R$; let $A_0$ and $A'$ be commutative rings which are $R$-algebras, with $A'$ an $A_0$-algebra compatibly with the $R$-actions. Let $M$ be a sheaf of modules on $C_{A_0}=C\times_{\operatorname{Spec}R}\operatorname{Spec}A_0$, assumed locally trivial: every point has an open neighbourhood $V$ such that the pullback of $M$ along $V\hookrightarrow C_{A_0}$ is isomorphic to the unit module of $V$. Write $\sigma\colon C_{A'}\to C_{A_0}$ for the morphism induced by $\operatorname{Spec}(A'\to A_0$'s algebra map$)$ over $C$. The assertion is the existence of $A'$-linear isomorphisms $e_0,e_1,e_{01}$ from $A'\otimes_{A_0}\Gamma(M,U_{k,A_0})$ onto $\Gamma(\sigma^{*}M,U_{k,A'})$ for $k=0,1$ and for $U_0\cap U_1$, where the opens are the preimages of $U_0,U_1$ in the respective base changes and the $A_0$-, $A'$-structures come from the projections to $\operatorname{Spec}A_0$, $\operatorname{Spec}A'$; these isomorphisms intertwine the $A'$-base changes of the two restriction maps to the intersection with the restriction maps for $\sigma^{*}M$, send $1\otimes m$ to the section obtained from the pullback–pushforward adjunction unit at $M$ on the relevant chart, restricted along the identification of $\sigma^{-1}U_{k,A_0}$ with $U_{k,A'}$, and satisfy $e_k(1\otimes(s\cdot m))=\sigma^{\#}(s)\cdot e_k(1\otimes m)$ for $s$ a regular function on the chart of $C_{A_0}$, $\sigma^{\#}$ being the induced map on sections of the structure sheaves.
--
--   This is affine base change of sections of a locally trivial (hence quasi-coherent) module, recorded chart by chart in the two-chart Čech format, for a base change between two $R$-algebra stages $A_0\to A'$ rather than from $R$ itself. It feeds the arguments that the relative Picard presheaf is locally of finite presentation, where an invertible module, or an isomorphism of such, over a filtered colimit of $R$-algebras is descended to a finitely generated stage through its chart modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
    {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))
    (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A'] [IsScalarTower R A₀ A']
    (M : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀)).Modules)
    (htriv : ∀ x, ∃ (V : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀)).Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    ∃ (e0 : A' ⊗[A₀] ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M0 ≃ₗ[A']
          ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M)).M0)
      (e1 : A' ⊗[A₀] ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M1 ≃ₗ[A']
          ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M)).M1)
      (e01 : A' ⊗[A₀] ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M01 ≃ₗ[A']
          ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M)).M01),
      (∀ x, e01 ((((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).r0.baseChange A') x) =
        ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M)).r0 (e0 x)) ∧
      (∀ x, e01 ((((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).r1.baseChange A') x) =
        ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M)).r1 (e1 x)) ∧
      (∀ m, e0 ((1 : A') ⊗ₜ[A₀] m) =
        ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M).presheaf.map
          (homOfLE (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).unit.app M).app
            ((𝒱.pullback c A₀).U0)).hom m)) ∧
      (∀ m, e1 ((1 : A') ⊗ₜ[A₀] m) =
        ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M).presheaf.map
          (homOfLE (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).unit.app M).app
            ((𝒱.pullback c A₀).U1)).hom m)) ∧
      (∀ m, e01 ((1 : A') ⊗ₜ[A₀] m) =
        ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M).presheaf.map
          (homOfLE (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).unit.app M).app
            ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1)).hom m)) ∧

      (∀ (s : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A0)
          (m : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M0),
        e0 ((1 : A') ⊗ₜ[A₀] (s • m)) =
          (show ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A0 from
            ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE ((𝒱.pullback c A₀).U0)
              ((𝒱.pullback c A').U0) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) •
            e0 ((1 : A') ⊗ₜ[A₀] m)) ∧
      (∀ (s : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A1)
          (m : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M1),
        e1 ((1 : A') ⊗ₜ[A₀] (s • m)) =
          (show ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A1 from
            ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE ((𝒱.pullback c A₀).U1)
              ((𝒱.pullback c A').U1) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) •
            e1 ((1 : A') ⊗ₜ[A₀] m)) ∧
      (∀ (s : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A01)
          (m : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M01),
        e01 ((1 : A') ⊗ₜ[A₀] (s • m)) =
          (show ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A01 from
            ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE
              ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1) ((𝒱.pullback c A').U0 ⊓ (𝒱.pullback c A').U1)
              (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) •
            e01 ((1 : A') ⊗ₜ[A₀] m)) := by sorry
