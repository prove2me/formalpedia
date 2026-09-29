-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/c5ef002c-c504-59a1-ba5d-922112f8aa26
-- title:
--   Torus G_m^{s-1} closed-immerses as kernel of the restriction pair
-- statement:
--   Let $k$ be an algebraically closed field and let $X$, $C_1$, $C_2$ be $k$-schemes via $x$, $c_1$, $c_2$, with $x$ proper and $X$ reduced, and $c_1$, $c_2$ proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1 : C_1 \to X$ and $i_2 : C_2 \to X$ be closed immersions over $k$ (each a morphism whose composite with $x$ is the structure morphism) such that every point of $X$ lies in the image of $i_1$ or of $i_2$, and suppose the fibre product $C_1 \times_X C_2$ is reduced with exactly $s$ points, $s > 0$. Fix $k$-sections $\varepsilon$ of $x$, $\varepsilon_1$ of $c_1$ with $\varepsilon_1$ followed by $i_1$ equal to $\varepsilon$, and $\varepsilon_2$ of $c_2$. Let $D$, $D_1$, $D_2$ be pointed $k$-schemes (`RelativePic0Designation`: a scheme with a structure morphism to $\operatorname{Spec} k$ and a section of it) together with data $h_D$, $h_{D_1}$, $h_{D_2}$ exhibiting each as representing the functor of rigidified line bundles that are fibrewise algebraically equivalent to zero on $(X,\varepsilon)$, $(C_1,\varepsilon_1)$, $(C_2,\varepsilon_2)$ respectively: each carries a Poincaré rigidified bundle lying in the cut, classifies every such bundle by a unique morphism over $k$ up to isomorphism of pullbacks, and has its zero section classifying the unit. Let $\nu_1 : D \to D_1$ over $k$ be the morphism classifying pullback along $i_1$, and let $\nu_2 : D \to D_2$ be any morphism over $k$ such that for every $k$-scheme $T$ and every $T$-point $a$ of $D$ the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the rigidification along the section $\mathrm{rigSection}\,c_2\,t\,\varepsilon_2$ (that is, tensoring with the pullback of the dual of the restriction to that section) of the pullback along $\mathrm{curveChange}\,i_2$ of the pullback of the Poincaré bundle of $D$ along $a$. Then there exists a morphism $\tau$ over $k$ from the split torus $\operatorname{Spec} k[\mathbb{Z}^{s-1}]$ (the spectrum of the additive monoid algebra of $\mathrm{Fin}(s-1) \to \mathbb{Z}$ over $k$) to $D$ such that: $\tau$ is a closed immersion; $\tau$ is multiplicative on $k$-points, in the sense that for all $\chi$, $\chi'$ in `WithConv (torusCoord k (s-1) →ₐ[k] k)`, whose underlying $k$-algebra homomorphisms $k[\mathbb{Z}^{s-1}] \to k$ give the $k$-points `torusPtId` of the torus, the point $\chi\chi'$ composed with $\tau$ equals the product, under the relative group law supplied by $h_D$, of the points $\chi$ and $\chi'$ composed with $\tau$; and the image of $\tau$ is exactly the common kernel of $\nu_1$ and $\nu_2$, namely for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of $D$, the composites of $a$ with $\nu_1$ and with $\nu_2$ are the identity sections of the group laws on $D_1$ and $D_2$ if and only if $a$ factors as a $T$-point of the torus followed by $\tau$.
--
--   This is the toric part of the dévissage of the generalised Jacobian of two smooth proper curves glued at $s$ points: the kernel of the restriction map $\operatorname{Pic}^0(X) \to \operatorname{Pic}^0(C_1) \times \operatorname{Pic}^0(C_2)$ is the split torus $\mathbb{G}_m^{s-1}$, here realised as a closed subgroup scheme of the representing object $D$. It feeds the analysis of the special fibre of the relative $\operatorname{Pic}^0$ of modular curves at $p$ and, through that, the flatness and surjectivity statement for the restriction pair.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.RelPicard.exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves
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
    ∃ τ : SchemeHomOver (torusStr k (s - 1)) D.toBase,
      IsClosedImmersion τ.1 ∧
      (∀ χ χ' : WithConv (torusCoord k (s - 1) →ₐ[k] k),
        NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) (χ * χ').ofConv) τ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _
            (NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ.ofConv) τ)
            (NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ'.ofConv) τ)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        (NeronModelInfra.schemeHomOverComp a ν₁ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one t ∧
          NeronModelInfra.schemeHomOverComp a ν₂ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one t) ↔
        ∃ y : SchemeHomOver t (torusStr k (s - 1)), NeronModelInfra.schemeHomOverComp y τ = a) := by sorry
