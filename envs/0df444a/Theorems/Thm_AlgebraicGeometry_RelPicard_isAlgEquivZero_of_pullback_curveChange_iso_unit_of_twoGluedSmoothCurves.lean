-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_pullback_curveChange_iso_unit_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.isAlgEquivZero_of_pullback_curveChange_iso_unit_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/676eda97-e5a0-5d49-b5ba-3d0da604fefb
-- title:
--   Trivial on both glued components implies algebraically equivalent to zero
-- statement:
--   Let $k$ be an algebraically closed field and let $x : X \to \operatorname{Spec} k$ be a proper morphism with $X$ reduced. Let $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $i_\nu$ be morphisms $C_\nu \to X$ over $\operatorname{Spec} k$ (that is, pairs consisting of a morphism $i_\nu$ with $i_\nu$ followed by $x$ equal to $c_\nu$) which are closed immersions, such that every point of $X$ lies in the image of $i_1$ or of $i_2$ on underlying spaces. Assume the scheme $C_1 \times_X C_2$ is reduced and that the cardinality of its set of points equals $s$ with $s > 0$. Let $K$ be an algebraically closed field, $\kappa : \operatorname{Spec} K \to \operatorname{Spec} k$ an arbitrary morphism, and $N$ a module on $X_K = X \times_{\operatorname{Spec} k} \operatorname{Spec} K$ that is invertible, i.e. every point has an open neighbourhood $U$ on which the restriction of $N$ is isomorphic to the unit module of $U$. Assume finally that the pullback of $N$ along the base-changed immersion `curveChange` $(C_\nu)_K \to X_K$ is isomorphic to the unit module of $(C_\nu)_K$ for $\nu = 1, 2$. Then $N$ satisfies `IsAlgEquivZero` for the structure morphism $X_K \to \operatorname{Spec} K$: there exist a scheme $T'$ with a morphism $h : T' \to \operatorname{Spec} K$ which is locally of finite type and geometrically integral, an invertible module $M$ on $X_K \times_{\operatorname{Spec} K} T'$, and two sections $t_0, t_1$ of $h$ over $\operatorname{Spec} K$, such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the unit module, while the pullback of $M$ along the base change of $t_1$ is isomorphic to the pullback of $N$ along the first projection of $X_K \times_{\operatorname{Spec} K} \operatorname{Spec} K$.
--
--   This is the toric part of the description of $\mathrm{Pic}^0$ of a curve obtained by gluing two smooth proper components transversally at $s \ge 1$ points: a line bundle whose restriction to each component is trivial is, after any base change to an algebraically closed field, algebraically equivalent to zero in the one-step sense used in the project's relative Picard formalism. It feeds the comparison results relating algebraic equivalence on $X_K$ with algebraic equivalence on the components, and thence the analysis of the semistable model of the modular curve used in the study of its Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_pullback_curveChange_iso_unit_of_twoGluedSmoothCurves.lean

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

theorem AlgebraicGeometry.RelPicard.isAlgEquivZero_of_pullback_curveChange_iso_unit_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (K : Type u) [Field K] [IsAlgClosed K] (κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (N : (pullback x κ).Modules) (hN : Scheme.Modules.IsInvertible N)
    (h₁ : Nonempty ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 κ)).obj N ≅
      SheafOfModules.unit (pullback c₁ κ).ringCatSheaf))
    (h₂ : Nonempty ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 κ)).obj N ≅
      SheafOfModules.unit (pullback c₂ κ).ringCatSheaf)) :
    IsAlgEquivZero (pullback.snd x κ) N := by sorry
