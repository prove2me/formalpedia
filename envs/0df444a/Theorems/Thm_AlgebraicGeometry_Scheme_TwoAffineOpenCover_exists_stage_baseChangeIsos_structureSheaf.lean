-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/f4df509b-4598-5f28-9a01-0f3a5a9653d4
-- title:
--   Base change of two-affine chart rings along a stage map
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, and $\mathcal V$ a two-affine open cover of $C$, i.e. opens $U_0,U_1$ with $U_0\sqcup$-union $U_0\sqcup U_1=\top$, each of $U_0$, $U_1$ and $U_0\cap U_1$ affine; let $c\colon C\to\operatorname{Spec}R$ be a morphism, and let $A_0$, $A'$ be commutative rings which are $R$-algebras, with $A'$ an $A_0$-algebra forming a scalar tower over $R$. For an $R$-algebra $A$, write $C_A=C\times_{\operatorname{Spec}R}\operatorname{Spec}A$ and let $\mathcal V_A$ be the two-affine cover of $C_A$ with charts the preimages of $U_0$, $U_1$ under the first projection; the associated two-chart datum over $A$, formed with respect to the second projection $C_A\to\operatorname{Spec}A$, has chart rings $\Gamma(C_A,U_{0,A})$, $\Gamma(C_A,U_{1,A})$ and $\Gamma(C_A,U_{0,A}\cap U_{1,A})$, with their $A$-algebra structures and the two restriction maps. Let $\sigma\colon C_{A'}\to C_{A_0}$ be the morphism obtained by base change of $\operatorname{Spec}$ of the structure map $A_0\to A'$, viewed as a morphism over $\operatorname{Spec}R$, along $c$ (identity on $C$, identity on $\operatorname{Spec}R$). The assertion is that there exist isomorphisms of $A'$-algebras $$A'\otimes_{A_0}\Gamma(C_{A_0},U_{k,A_0})\;\xrightarrow{\ \sim\ }\;\Gamma(C_{A'},U_{k,A'})\qquad(k=0,1,\ \text{and the intersection}),$$ each sending $1\otimes s$ to the image of $s$ under the map on sections induced by $\sigma$ from $U_{k,A_0}$ to $U_{k,A'}$, the latter being contained in $\sigma^{-1}(U_{k,A_0})$.
--
--   This is affine base change for the coordinate rings of the two charts and of their intersection, $\Gamma(U\times_{\operatorname{Spec}A_0}\operatorname{Spec}A',\mathcal O)\cong A'\otimes_{A_0}\Gamma(U,\mathcal O)$, in the stage-to-stage form where the base is $\operatorname{Spec}A_0$ rather than $\operatorname{Spec}R$. It feeds the limit arguments for the relative Picard presheaf, being cited by [`AlgebraicGeometry.RelPicard.LFP.exists_fg_nonempty_iso_pullbackAlong`](thm.html#AlgebraicGeometry.RelPicard.LFP.exists_fg_nonempty_iso_pullbackAlong), [`AlgebraicGeometry.RelPicard.exists_isDeformationClassMap`](thm.html#AlgebraicGeometry.RelPicard.exists_isDeformationClassMap) and related results, and is deduced from the corresponding statement over $R$ together with the fact that $\sigma$ exhibits $C_{A'}$ as a pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf.lean

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

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf
    {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))
    (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A'] [IsScalarTower R A₀ A'] :
    ∃ (e0 : (A' ⊗[A₀] ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A0) ≃ₐ[A']
          ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A0)
      (e1 : (A' ⊗[A₀] ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A1) ≃ₐ[A']
          ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A1)
      (e01 : (A' ⊗[A₀] ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A01) ≃ₐ[A']
          ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A01),
      (∀ s, e0 ((1 : A') ⊗ₜ[A₀] s) = ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE ((𝒱.pullback c A₀).U0)
          ((𝒱.pullback c A').U0) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) ∧
      (∀ s, e1 ((1 : A') ⊗ₜ[A₀] s) = ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE ((𝒱.pullback c A₀).U1)
          ((𝒱.pullback c A').U1) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) ∧
      (∀ s, e01 ((1 : A') ⊗ₜ[A₀] s) =
        ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1)
          ((𝒱.pullback c A').U0 ⊓ (𝒱.pullback c A').U1) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) := by sorry
