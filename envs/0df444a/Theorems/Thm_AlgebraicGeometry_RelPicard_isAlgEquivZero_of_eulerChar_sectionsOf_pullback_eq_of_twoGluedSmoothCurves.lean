-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_eulerChar_sectionsOf_pullback_eq_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.isAlgEquivZero_of_eulerChar_sectionsOf_pullback_eq_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/63d9dd01-6681-524f-a235-0726f595af95
-- title:
--   Euler characteristic test for Pic⁰ on two glued curves
-- statement:
--   Let $k$ be an algebraically closed field, and let $X$, $C_1$, $C_2$ be schemes with structure morphisms $x : X \to \operatorname{Spec} k$ proper, $X$ reduced, and $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1$, $i_2$ be morphisms over $\operatorname{Spec} k$, i.e. pairs consisting of $C_\nu \to X$ together with a proof that composing with $x$ gives $c_\nu$, whose underlying scheme morphisms are closed immersions; assume every point of $X$ lies in the image of $i_1$ or of $i_2$, that the fibre product $C_1 \times_X C_2$ is reduced, and that its underlying type has cardinality $s$ with $0 < s$. Let $L$ be a module on $X$ which is invertible, in the sense that every point has an open neighbourhood $U$ on which the pullback of $L$ along $U \hookrightarrow X$ is isomorphic to the unit module, and let $\mathcal V_1$, $\mathcal V_2$ be two-chart affine open covers of $C_1$, $C_2$ (two affine opens with affine intersection covering the curve). Assume, for $\nu = 1, 2$, the equality in $\mathbb Z$ of $\dim_k H^0 - \dim_k H^1$ of the two-chart Čech complex of $i_\nu^* L$ with that of the unit module on $C_\nu$, where $H^0$ is the kernel and $H^1$ the cokernel of the Čech difference map on sections over the two charts and their intersection. The conclusion is `IsAlgEquivZero x L`: there exist a scheme $T'$ with a locally of finite type, geometrically integral morphism $h : T' \to \operatorname{Spec} k$, an invertible module $M$ on $X \times_{\operatorname{Spec} k} T'$ and two sections $t_0$, $t_1$ of $h$ over the identity of $\operatorname{Spec} k$, such that the pullback of $M$ along the base-changed morphism at $t_0$ is isomorphic to the unit module on $X \times_{\operatorname{Spec} k} \operatorname{Spec} k$ and the pullback along the base-changed morphism at $t_1$ is isomorphic to the pullback of $L$ along the first projection.
--
--   This is the Euler-characteristic (Riemann–Roch) criterion for an invertible sheaf on a curve of compact type with two smooth components to be algebraically equivalent to zero: degree zero on each component suffices. It is used in the construction of rigidified line bundles on the two-chart model of $X_1(p)$ whose fibrewise classes are algebraically trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_eulerChar_sectionsOf_pullback_eq_of_twoGluedSmoothCurves.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.isAlgEquivZero_of_eulerChar_sectionsOf_pullback_eq_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (𝒱₁ : C₁.TwoAffineOpenCover) (𝒱₂ : C₂.TwoAffineOpenCover)
    (h₁ : (Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj L)).H0 : ℤ) -
          Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj L)).H1 =
        (Module.finrank k (𝒱₁.sectionsOf c₁ (SheafOfModules.unit C₁.ringCatSheaf : C₁.Modules)).H0 : ℤ) -
          Module.finrank k (𝒱₁.sectionsOf c₁ (SheafOfModules.unit C₁.ringCatSheaf : C₁.Modules)).H1)
    (h₂ : (Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj L)).H0 : ℤ) -
          Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj L)).H1 =
        (Module.finrank k (𝒱₂.sectionsOf c₂ (SheafOfModules.unit C₂.ringCatSheaf : C₂.Modules)).H0 : ℤ) -
          Module.finrank k (𝒱₂.sectionsOf c₂ (SheafOfModules.unit C₂.ringCatSheaf : C₂.Modules)).H1) :
    IsAlgEquivZero x L := by sorry
