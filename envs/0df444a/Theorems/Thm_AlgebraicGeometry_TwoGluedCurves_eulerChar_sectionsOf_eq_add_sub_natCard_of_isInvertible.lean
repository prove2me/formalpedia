-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible
-- name    : AlgebraicGeometry.TwoGluedCurves.eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/33a5ca4c-5288-5462-a709-e2358d9436fd
-- title:
--   Additivity of Euler characteristics for two glued subschemes
-- statement:
--   Let $k$ be an algebraically closed field, let $x\colon X \to \operatorname{Spec} k$ be a proper morphism with $X$ reduced, and let $c_1\colon C_1 \to \operatorname{Spec} k$, $c_2\colon C_2 \to \operatorname{Spec} k$ be proper. Let $i_1, i_2$ be morphisms $C_1 \to X$, $C_2 \to X$ over $\operatorname{Spec} k$ (that is, $i_\nu$ followed by $x$ equals $c_\nu$) which are closed immersions, such that every point of $X$ lies in the image of $i_1$ or of $i_2$ on underlying spaces, and such that the scheme-theoretic intersection $C_1 \times_X C_2$ is reduced and has finite underlying space with $\operatorname{Nat.card} = n$. Let $M$ be an $\mathcal{O}_X$-module which is invertible in the sense that each point of $X$ has an open neighbourhood $U$ for which the pullback of $M$ along $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Finally let $\mathcal{V}, \mathcal{V}_1, \mathcal{V}_2$ be arbitrary two-chart covers of $X$, $C_1$, $C_2$, each given by two affine opens with affine intersection covering the scheme. For such a cover, $H^0$ is the kernel and $H^1$ the cokernel of the Čech difference $(s_0, s_1) \mapsto -s_0|_{U_0 \cap U_1} + s_1|_{U_0 \cap U_1}$ on sections of the module, both viewed as $k$-vector spaces. The conclusion is the identity of integers $$\dim_k H^0(X, M) - \dim_k H^1(X, M) = \bigl(\dim_k H^0(C_1, i_1^{*}M) - \dim_k H^1(C_1, i_1^{*}M)\bigr) + \bigl(\dim_k H^0(C_2, i_2^{*}M) - \dim_k H^1(C_2, i_2^{*}M)\bigr) - n,$$ all cohomology being the two-chart Čech cohomology of the given covers and $i_\nu^{*}M$ the pullback of $M$ along $i_\nu$.
--
--   This is the Mayer–Vietoris additivity of the Euler characteristic for a reduced proper scheme written as the union of two closed subschemes meeting in a finite reduced subscheme, in the two-chart Čech formulation used throughout this development. It feeds the genus computations for curves with two components and the analysis of relative Picard data for degenerating two-component curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.TwoGluedCurves.eulerChar_sectionsOf_eq_add_sub_natCard_of_isInvertible
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [IsReduced X]
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [IsProper c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (hfin : Finite ↥(pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (𝒱 : X.TwoAffineOpenCover) (𝒱₁ : C₁.TwoAffineOpenCover) (𝒱₂ : C₂.TwoAffineOpenCover) :
    ((Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1) =
      ((Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj M)).H0 : ℤ) -
          Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj M)).H1) +
        ((Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj M)).H0 : ℤ) -
          Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj M)).H1) - n := by sorry
