-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_pullback_stageHom_equiv_lineBundle_appLE
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_pullback_stageHom_equiv_lineBundle_appLE
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/15ecd9fe-b671-54c4-b465-642275195165
-- title:
--   Transition function of a pulled-back chart-trivial line bundle
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, $c \colon C \to \operatorname{Spec} R$ a morphism, and $\mathcal V$ a two-chart affine open cover of $C$, i.e. affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Let $A_0$ and $A'$ be commutative $R$-algebras with $A'$ an $A_0$-algebra, the scalars forming a tower over $R$. Write $C_{A_0} = C \times_{\operatorname{Spec} R} \operatorname{Spec} A_0$ and $C_{A'}$ likewise, each equipped with the cover by the preimages of $U_0$, $U_1$ under the first projection and viewed over $A_0$, resp. $A'$, via the second projection; the associated two-chart data consist of the section rings $A_0^{(0)},A_0^{(1)},A_0^{(01)}$ of the structure sheaf on the charts and their intersection with the two restriction maps $\rho_0,\rho_1$. Let $L$ be a module on $C_{A_0}$ that is invertible in the sense that every point has an open neighbourhood $U$ for which the pull-back of $L$ along $U \hookrightarrow C_{A_0}$ is isomorphic to the unit sheaf of modules on $U$. Assume given a unit $t$ of $A_0^{(01)}$ and trivialisations $e_0, e_1, e_{01}$, namely linear equivalences of the section modules of $L$ on the two charts and their intersection with the corresponding section rings, over those rings, satisfying $e_{01}(r_0 x) = \rho_0(e_0 x)$ for all $x$ and $e_{01}(r_1 y) = t \cdot \rho_1(e_1 y)$ for all $y$, where $r_0, r_1$ are the restriction maps on sections of $L$. Let $\sigma \colon C_{A'} \to C_{A_0}$ be the base change of the morphism $\operatorname{Spec} A' \to \operatorname{Spec} A_0$ induced by the structure map $A_0 \to A'$, taken over $C$ (the identity in the $C$-factor). Then the pull-back $\sigma^* L$ admits trivialisations $e_0', e_1', e_{01}'$ of the same shape on $C_{A'}$, linear over the chart rings of $C_{A'}$, with $e_{01}'(r_0 x) = \rho_0(e_0' x)$ for all $x$ and $e_{01}'(r_1 y) = \sigma^\sharp(t) \cdot \rho_1(e_1' y)$ for all $y$, where $\sigma^\sharp$ is the map on sections induced by $\sigma$ from $U_{0,A_0} \sqcap U_{1,A_0}$ to $U_{0,A'} \sqcap U_{1,A'}$, legitimate because the preimage of the former intersection contains the latter.
--
--   This is the compatibility of Čech transition functions with base change: the cocycle of $\sigma^* L$ for the pulled-back two-chart cover is the image under $\sigma^\sharp$ of the cocycle of $L$, so that the map $\check H^1(\mathcal V_{A_0}, \mathcal O^\times) \to \check H^1(\mathcal V_{A'}, \mathcal O^\times)$ computes the base-change map on line bundles. It is used in the construction of the relative Picard functor, in the proof that the maps induced on $H^1$ by the transition morphisms between deformation stages are natural.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_pullback_stageHom_equiv_lineBundle_appLE.lean

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

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_pullback_stageHom_equiv_lineBundle_appLE
    {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))
    (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A'] [IsScalarTower R A₀ A']
    (L : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀)).Modules)
    (hL : Scheme.Modules.IsInvertible L)
    (t : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A01ˣ)
    (e0 : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) L).M0
      ≃ₗ[((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A0]
      ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A0)
    (e1 : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) L).M1
      ≃ₗ[((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A1]
      ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A1)
    (e01 : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) L).M01
      ≃ₗ[((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A01]
      ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A01)
    (he0 : ∀ x, e01 (((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
        (Scheme.TwoAffineOpenCover.specMap R A₀)) L).r0 x) =
      ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).ρ0 (e0 x))
    (he1 : ∀ y, e01 (((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c
        (Scheme.TwoAffineOpenCover.specMap R A₀)) L).r1 y) =
      (t : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A01) *
        ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).ρ1 (e1 y)) :
    ∃ (e0' : ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
          ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj L)).M0
        ≃ₗ[((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A0]
        ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A0)
      (e1' : ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
          ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj L)).M1
        ≃ₗ[((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A1]
        ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A1)
      (e01' : ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
          ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj L)).M01
        ≃ₗ[((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A01]
        ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A01),
      (∀ x, e01' (((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
          ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj L)).r0 x) =
        ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).ρ0 (e0' x)) ∧
      (∀ y, e01' (((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
          ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c
            (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj L)).r1 y) =
        (show ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A01 from
          ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE
            ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1) ((𝒱.pullback c A').U0 ⊓ (𝒱.pullback c A').U1)
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom
          (t : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A01)) *
        ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).ρ1 (e1' y)) := by sorry
