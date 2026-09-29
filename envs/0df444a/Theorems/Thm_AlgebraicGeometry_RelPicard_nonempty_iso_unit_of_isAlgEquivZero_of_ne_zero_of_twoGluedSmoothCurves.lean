-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/d4b3e27d-54d6-5851-98a6-43c3833b5b23
-- title:
--   Triviality criterion on two transversally glued smooth proper curves
-- statement:
--   Let $k$ be an algebraically closed field, let $x \colon X \to \operatorname{Spec} k$ be a morphism of schemes with $X$ reduced and $x$ locally of finite type, and let $c_1 \colon C_1 \to \operatorname{Spec} k$ and $c_2 \colon C_2 \to \operatorname{Spec} k$ both be proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be morphisms $C_1 \to X$, $C_2 \to X$ over $\operatorname{Spec} k$ (that is, $i_\nu$ followed by $x$ equals $c_\nu$), each a closed immersion, and assume: every point of $X$ lies in the image of the underlying map of $i_1$ or of $i_2$; the fibre product $C_1 \times_X C_2$ is reduced; and $C_1 \times_X C_2$ has at least one point. Assume further given, for each of $C_1$ and $C_2$, a cover by two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Let $L$ be a module over $X$ which is invertible, in the sense that every point of $X$ has an open neighbourhood $U$ such that the restriction of $L$ to $U$ is isomorphic to the unit module of $U$, and assume $L$ satisfies `IsAlgEquivZero` for $x$: there are a scheme $T'$ and a morphism $h \colon T' \to \operatorname{Spec} k$ which is locally of finite type and geometrically integral, an invertible module $M$ on $X \times_{\operatorname{Spec} k} T'$, and two sections $t_0, t_1$ of $h$ over $\operatorname{Spec} k$, such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the unit module of $X \times_{\operatorname{Spec} k} \operatorname{Spec} k$, while the pullback of $M$ along the base change of $t_1$ is isomorphic to the pullback of $L$ along the first projection. Finally let $\sigma \colon \mathbf{1} \to L$ be a nonzero morphism from the unit module. The conclusion is that the type of isomorphisms $L \cong \mathbf{1}$ is nonempty, i.e. $L$ is trivial.
--
--   This is the two-component case of the classical statement that on a reduced connected curve over an algebraically closed field, glued from two smooth proper geometrically integral components meeting in a nonempty reduced intersection, an invertible sheaf algebraically equivalent to zero admitting a nonzero global section is trivial; it is the rigidity input used in the study of $\operatorname{Pic}^0$ of degenerating curves. It is invoked in the fibrewise triviality statements for the Deligne–Rapoport style models of modular curves, namely [`ModularCurve.DRModelPackageLevel.nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero`](thm.html#ModularCurve.DRModelPackageLevel.nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero), [`ModularCurve.XHDRModelAtP.nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_fibre`](thm.html#ModularCurve.XHDRModelAtP.nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_fibre) and [`ModularCurve.XOneP.nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_of_twoGluedSmoothCurves.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k] {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType x]
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : ↥X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (hne : Nonempty ↥(pullback i₁.1 i₂.1))
    (𝒲₁ : C₁.TwoAffineOpenCover) (𝒲₂ : C₂.TwoAffineOpenCover)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)
    (σ : 𝟙_ X.Modules ⟶ L) (hσ : σ ≠ 0) :
    Nonempty (L ≅ 𝟙_ X.Modules) := by sorry
