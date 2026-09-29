-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_flat_surjective_restrictPair_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.flat_surjective_restrictPair_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/22403d52-8544-56dc-bbca-b4906700463e
-- title:
--   Faithful flatness of restriction to two glued smooth curves
-- statement:
--   Let $k$ be an algebraically closed field, and let $x : X \to \operatorname{Spec} k$ be proper with $X$ reduced, and $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be closed immersions $C_1 \to X$, $C_2 \to X$ compatible with the structure morphisms, jointly surjective on points, with $C_1 \times_X C_2$ reduced and $\operatorname{Nat.card}(C_1\times_X C_2) = s$ for some $s > 0$. Fix sections $\varepsilon$ of $x$, $\varepsilon_1$ of $c_1$ with $\varepsilon_1$ followed by $i_1$ equal to $\varepsilon$, and $\varepsilon_2$ of $c_2$. Let $D$, $D_1$, $D_2$ be pointed $k$-schemes (objects of `RelativePic0Designation`: a scheme with structure morphism to $\operatorname{Spec} k$ and a zero section) together with data `RepresentsRelSubPic` witnessing that each represents, on rigidified line bundles, the condition `algEquivZeroCut` of being fibrewise algebraically equivalent to zero: a Poincaré rigidified bundle in the cut, the universal property classifying such bundles uniquely up to isomorphism, and triviality at the zero section. Let $\nu_1, \nu_2$ be morphisms $D.P \to D_1.P$, $D.P \to D_2.P$ over $\operatorname{Spec} k$, with $\nu_1$ equal to the classifying morphism `RepresentsRelSubPic.pullbackHom` for restriction along $i_1$ (rigidified using $\varepsilon_1$ followed by $i_1 = \varepsilon$), and $\nu_2$ such that for every $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of $D.P$ over $\operatorname{Spec} k$, the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the $\varepsilon_2$-rigidification `Scheme.Modules.rigidify` of the restriction along `curveChange` $i_2$ of the pullback of the Poincaré bundle of $D$ along $a$. Then the induced morphism $(\nu_1,\nu_2) : D.P \to D_1.P \times_{\operatorname{Spec} k} D_2.P$ is flat and surjective.
--
--   This is the surjectivity and flatness half of the dévissage $0 \to \mathbb{G}_m^{s-1} \to \operatorname{Pic}^0_{X/k} \to \operatorname{Pic}^0_{C_1/k} \times \operatorname{Pic}^0_{C_2/k} \to 0$ for a reduced proper curve $X$ obtained by glueing two smooth proper geometrically integral curves at $s$ points. It is used in the construction of the toric part of the Picard scheme of the special fibre of the modular curves occurring in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_flat_surjective_restrictPair_of_twoGluedSmoothCurves.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.flat_surjective_restrictPair_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (ε : SchemeHomOver (𝟙 _) x) (ε₁ : SchemeHomOver (𝟙 _) c₁) (hε : ε₁.1 ≫ i₁.1 = ε.1)
    (ε₂ : SchemeHomOver (𝟙 _) c₂)
    (D : RelativePic0Designation k x) (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (D₁ : RelativePic0Designation k c₁) (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
    (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase)
    (hν₁ : ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
    (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L))) :
    Flat (pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm) : D.P ⟶ pullback D₁.toBase D₂.toBase) ∧
    Surjective (pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm) : D.P ⟶ pullback D₁.toBase D₂.toBase) := by sorry
