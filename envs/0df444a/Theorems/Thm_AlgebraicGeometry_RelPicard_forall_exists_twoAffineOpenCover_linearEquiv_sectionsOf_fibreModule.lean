-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule
-- name    : AlgebraicGeometry.RelPicard.forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/b7e5b417-155b-5dee-98dd-7ef5263d6a34
-- title:
--   Two-chart Čech cohomology of a fibre module is base-change invariant
-- statement:
--   Let $R$ be a commutative ring, let $c \colon C \to \operatorname{Spec} R$ and $t \colon T \to \operatorname{Spec} R$ be morphisms of schemes, let $k$ be a field, let $s \colon \operatorname{Spec} k \to T$ and $x \colon \operatorname{Spec} k \to \operatorname{Spec} R$ be morphisms with $s$ followed by $t$ equal to $x$, and let $M$ be a sheaf of modules on $C \times_{\operatorname{Spec} R} T$. Two presentations of the fibre are compared: the iterated fibre $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k$, carrying the structure morphism `fibreAt c t s` to $\operatorname{Spec} k$ given by the second projection and the module `fibreModule c t s M` obtained by pulling $M$ back along the first projection, and the base change $C \times_{\operatorname{Spec} R} \operatorname{Spec} k$, carrying its second projection to $\operatorname{Spec} k$ and the pullback of $M$ along the morphism `baseChangeSnd c ⟨s, hx⟩` induced by $s$. For a cover of a scheme by two affine opens with affine intersection (a `TwoAffineOpenCover`: opens $U_0, U_1$, both affine, with affine $U_0 \cap U_1$ and $U_0 \cup U_1$ the whole space) and a module on it, the associated two-chart Čech data have $H^0$ the kernel, and $H^1$ the cokernel, of the difference map $\Gamma(U_0) \times \Gamma(U_1) \to \Gamma(U_0 \cap U_1)$. The assertion is the conjunction of two statements: for every such cover $\mathcal{V}$ of $C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ there is such a cover $\mathcal{W}$ of the iterated fibre, and conversely for every $\mathcal{W}$ there is a $\mathcal{V}$, such that in both cases the $H^0$'s and the $H^1$'s of the two Čech complexes are isomorphic as $k$-modules.
--
--   This is the compatibility, under the canonical identification $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$, of the two-chart Čech cohomology used throughout the relative Picard constructions: properties quantified over all two-affine covers of one model of the geometric fibre (vanishing of $H^1$, prescribed dimensions of $H^0$ and $H^1$) transfer to the other. It is used in the analysis of the zero-cut locus of the relative Picard functor for families of degenerating curves and lines.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.forall_exists_twoAffineOpenCover_linearEquiv_sectionsOf_fibreModule
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hx : s ≫ t = x) (M : (pullback c t).Modules) :
    (∀ 𝒱 : (pullback c x).TwoAffineOpenCover, ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x)
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj M)).H0) ∧
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x)
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj M)).H1)) ∧
    (∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover, ∃ 𝒱 : (pullback c x).TwoAffineOpenCover,
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x)
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj M)).H0) ∧
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x)
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj M)).H1)) := by sorry
