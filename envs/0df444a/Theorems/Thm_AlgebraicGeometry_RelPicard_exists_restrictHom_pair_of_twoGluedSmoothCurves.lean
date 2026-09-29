-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_restrictHom_pair_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.exists_restrictHom_pair_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/922969c7-ba13-53a4-b353-d90790fa65f9
-- title:
--   Restriction morphisms on Pic⁰ for two transversally glued curves
-- statement:
--   Let $k$ be an algebraically closed field and let $x : X \to \operatorname{Spec} k$ be proper with $X$ reduced, and $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be morphisms $C_1 \to X$, $C_2 \to X$ over $\operatorname{Spec} k$ (i.e. $i_j$ followed by $x$ equals $c_j$) which are closed immersions, such that every point of $X$ lies in the image of $i_1$ or of $i_2$, the fibre product $C_1 \times_X C_2$ is reduced, and its underlying type has cardinality $s$ with $s > 0$. Let $\varepsilon$, $\varepsilon_1$, $\varepsilon_2$ be sections of $x$, $c_1$, $c_2$ with $\varepsilon_1$ followed by $i_1$ equal to $\varepsilon$. Let $D$, $D_1$, $D_2$ be designations, each consisting of a scheme over $\operatorname{Spec} k$ with a zero section, together with data $h_D$, $h_{D_1}$, $h_{D_2}$ exhibiting them as representing the functor of rigidified line bundles on $X$, $C_1$, $C_2$ (rigidified along $\varepsilon$, $\varepsilon_1$, $\varepsilon_2$) that are fibrewise algebraically equivalent to zero: each carries a Poincaré rigidified bundle satisfying that condition and universally classifying such bundles, with triviality along the zero section. Then there exist morphisms $\nu_1 : D \to D_1$ and $\nu_2 : D \to D_2$ over $\operatorname{Spec} k$ such that: $\nu_1$ is the classifying morphism `RepresentsRelSubPic.pullbackHom` of the pullback of the Poincaré bundle of $D$ along the base-changed $i_1$ (using $\varepsilon_1$ followed by $i_1$ equal to $\varepsilon$); for every $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of $D$ over $t$, the pullback along $a$ followed by $\nu_2$ of the Poincaré bundle of $D_2$ is isomorphic to $L \otimes q^{*}(\sigma^{*}L)^{\vee}$, where $L$ is the pullback of the bundle classified by $a$ along `curveChange i₂.1 i₂.2 t`, $q$ is the second projection of $C_2 \times_k T$ and $\sigma$ is the section `rigSection c₂ t ε₂`; and both $\nu_1$ and $\nu_2$ are additive, in the sense that composing the product of two $T$-points $a$, $b$ of $D$ under the relative group law attached to $h_D$ with $\nu_j$ equals the product of the composites $a \nu_j$, $b \nu_j$ under the relative group law attached to $h_{D_j}$.
--
--   This provides the two restriction morphisms $\mathrm{Pic}^0(X) \to \mathrm{Pic}^0(C_1)$, $\mathrm{Pic}^0(C_2)$ used in the dévissage of the generalised Jacobian of a curve with two smooth components meeting transversally, the second being restriction followed by re-rigidification along $\varepsilon_2$ (the base point $\varepsilon$ need not lie on $C_2$). It is used in the analysis of the special fibre of the Jacobian of a modular curve, and is cited by the construction of the resulting equivalence and surjectivity statements for the pair $(\nu_1,\nu_2)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_restrictHom_pair_of_twoGluedSmoothCurves.lean

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

theorem AlgebraicGeometry.RelPicard.exists_restrictHom_pair_of_twoGluedSmoothCurves
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
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂) :
    ∃ (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase),
      ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁ ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a b : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul t a b) ν₁ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).mul t
            (NeronModelInfra.schemeHomOverComp a ν₁) (NeronModelInfra.schemeHomOverComp b ν₁)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a b : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul t a b) ν₂ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).mul t
            (NeronModelInfra.schemeHomOverComp a ν₂) (NeronModelInfra.schemeHomOverComp b ν₂)) := by sorry
