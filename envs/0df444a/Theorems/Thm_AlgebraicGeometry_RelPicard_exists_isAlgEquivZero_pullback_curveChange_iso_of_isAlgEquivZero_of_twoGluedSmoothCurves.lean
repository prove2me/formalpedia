-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/be37a515-6bd3-59ea-9c66-89a8ccfbdce0
-- title:
--   Extending an algebraically trivial bundle across a glued component
-- statement:
--   Let $k$ be an algebraically closed field, let $X$, $C_1$, $C_2$ be schemes, let $x : X \to \operatorname{Spec} k$ be proper with $X$ reduced, and let $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be morphisms $C_\nu \to X$ over $\operatorname{Spec} k$ (i.e. $i_\nu$ followed by $x$ equals $c_\nu$) which are closed immersions, such that every point of $X$ lies in the image of $i_1$ or of $i_2$, such that the scheme $C_1 \times_X C_2$ is reduced, and such that its underlying type has cardinality $s$ with $s > 0$. Let $K$ be an algebraically closed field and $\kappa : \operatorname{Spec} K \to \operatorname{Spec} k$ any morphism. Let $L_1$ be a module on $C_1 \times_{\operatorname{Spec} k} \operatorname{Spec} K$ that is invertible, i.e. every point has an open neighbourhood over which $L_1$ restricts to the unit module, and assume $L_1$ satisfies `IsAlgEquivZero` for the projection $C_1 \times_{\operatorname{Spec} k} \operatorname{Spec} K \to \operatorname{Spec} K$: there are a scheme $T'$ over $\operatorname{Spec} K$, locally of finite type and geometrically integral, an invertible module $M$ on $(C_1)_K \times_{\operatorname{Spec} K} T'$ and two sections $t_0, t_1$ of $T' \to \operatorname{Spec} K$ such that the restriction of $M$ along $t_0$ is isomorphic to the unit module and its restriction along $t_1$ is isomorphic to the pullback of $L_1$. The conclusion is that there exists a module $L'$ on $X \times_{\operatorname{Spec} k} \operatorname{Spec} K$ which is invertible, satisfies the same predicate `IsAlgEquivZero` for the projection to $\operatorname{Spec} K$, whose pullback along the base change $i_1 \times \mathrm{id}_{\operatorname{Spec} K}$ (`curveChange`) is isomorphic to $L_1$, and whose pullback along $i_2 \times \mathrm{id}_{\operatorname{Spec} K}$ is isomorphic to the unit module on $C_2 \times_{\operatorname{Spec} k} \operatorname{Spec} K$.
--
--   This is the surjectivity half, for one of the two components, of the description of the algebraically trivial part of the Picard group of a curve obtained by gluing two smooth proper components along a finite set of points: a line bundle algebraically equivalent to zero on the first component extends to an algebraically trivial bundle on the whole curve that is trivial on the second component. It is used by [`AlgebraicGeometry.RelPicard.isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves) in the analysis of relative Picard functors and Jacobians of such curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.exists_isAlgEquivZero_pullback_curveChange_iso_of_isAlgEquivZero_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (K : Type u) [Field K] [IsAlgClosed K] (κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (L₁ : (pullback c₁ κ).Modules) (hL₁ : Scheme.Modules.IsInvertible L₁)
    (h₁ : IsAlgEquivZero (pullback.snd c₁ κ) L₁) :
    ∃ L' : (pullback x κ).Modules, Scheme.Modules.IsInvertible L' ∧ IsAlgEquivZero (pullback.snd x κ) L' ∧
      Nonempty ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 κ)).obj L' ≅ L₁) ∧
      Nonempty ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 κ)).obj L' ≅
        SheafOfModules.unit (pullback c₂ κ).ringCatSheaf) := by sorry
