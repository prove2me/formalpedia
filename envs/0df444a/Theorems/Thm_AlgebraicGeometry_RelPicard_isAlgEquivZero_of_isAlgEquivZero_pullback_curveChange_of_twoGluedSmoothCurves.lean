-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/b2080a89-f352-5cda-a793-8afbfcce980d
-- title:
--   Algebraic equivalence to zero detected on two glued smooth curves
-- statement:
--   Let $k$ be an algebraically closed field and let $x \colon X \to \operatorname{Spec} k$ be a proper morphism with $X$ reduced. Let $c_1 \colon C_1 \to \operatorname{Spec} k$ and $c_2 \colon C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1, i_2$ be morphisms $C_1 \to X$, $C_2 \to X$ over $\operatorname{Spec} k$ (elements of `SchemeHomOver c₁ x`, `SchemeHomOver c₂ x`, i.e. morphisms whose composite with $x$ is $c_1$, resp. $c_2$) which are closed immersions, such that every point of $X$ lies in the image of $i_1$ or of $i_2$, the fibre product $C_1 \times_X C_2$ is reduced, and the cardinality of its underlying set equals a natural number $s$ with $s > 0$. Let $K$ be an algebraically closed field, $\kappa \colon \operatorname{Spec} K \to \operatorname{Spec} k$ a morphism, and $L$ a module on $X_K = X \times_{\operatorname{Spec} k} \operatorname{Spec} K$ which is invertible in the sense that every point has an open neighbourhood over which $L$ restricts to a module isomorphic to the unit module. Assume that the pullback of $L$ along the base change $\operatorname{curveChange}$ of $i_1$ (resp. of $i_2$) to $K$ satisfies `IsAlgEquivZero` relative to $\operatorname{pr}_2 \colon (C_1)_K \to \operatorname{Spec} K$ (resp. $(C_2)_K \to \operatorname{Spec} K$); that is, for each $\nu$ there are a $K$-scheme $T'$ with structure morphism locally of finite type and geometrically integral, an invertible module $M$ on $(C_\nu)_K \times_{\operatorname{Spec} K} T'$, and two $K$-points $t_0, t_1$ of $T'$ (sections of the structure morphism) such that the restriction of $M$ along $t_0$ is isomorphic to the unit module and its restriction along $t_1$ is isomorphic to the pullback of the given bundle along the canonical projection $(C_\nu)_K \times_{\operatorname{Spec} K} \operatorname{Spec} K \to (C_\nu)_K$. Then $L$ itself satisfies `IsAlgEquivZero` relative to $\operatorname{pr}_2 \colon X_K \to \operatorname{Spec} K$, with the same meaning.
--
--   This is the statement that on a reduced proper curve which is the union of two smooth proper geometrically integral components meeting in a non-empty finite reduced scheme, membership in the algebraic-equivalence-to-zero locus of the Picard group may be tested after restriction to the two components. It feeds the surjectivity of the restriction map $\operatorname{Pic}^0_X \to \operatorname{Pic}^0_{C_1} \times \operatorname{Pic}^0_{C_2}$ and the construction of its local sections, and is cited for admissible homomorphisms, for sections over open subsets of the restriction pair, and for the degenerate-fibre variants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves.lean

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

theorem AlgebraicGeometry.RelPicard.isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (K : Type u) [Field K] [IsAlgClosed K] (κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (L : (pullback x κ).Modules) (hL : Scheme.Modules.IsInvertible L)
    (h₁ : IsAlgEquivZero (pullback.snd c₁ κ) ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 κ)).obj L))
    (h₂ : IsAlgEquivZero (pullback.snd c₂ κ) ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 κ)).obj L)) :
    IsAlgEquivZero (pullback.snd x κ) L := by sorry
