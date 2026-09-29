-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_opens_section_restrictPair_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.exists_opens_section_restrictPair_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/21d0b636-96a6-552a-927f-176908eed931
-- title:
--   Local sections of the restriction pair for two glued smooth curves
-- statement:
--   Let $k$ be an algebraically closed field and let $x\colon X\to\operatorname{Spec}k$ be proper with $X$ reduced, and $c_1\colon C_1\to\operatorname{Spec}k$, $c_2\colon C_2\to\operatorname{Spec}k$ proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1,i_2$ be morphisms $C_1\to X$, $C_2\to X$ over $\operatorname{Spec}k$ which are closed immersions and whose images together cover every point of $X$, with $C_1\times_X C_2$ reduced, of cardinality $s$ on points, and $s>0$. Let $\varepsilon$, $\varepsilon_1$, $\varepsilon_2$ be sections of $x$, $c_1$, $c_2$ with $\varepsilon_1$ followed by $i_1$ equal to $\varepsilon$. Let $D$, $D_1$, $D_2$ be $\operatorname{Pic}^0$ designations for $x$, $c_1$, $c_2$ (a scheme with a structure morphism to $\operatorname{Spec}k$ and a zero section) together with data $hD$, $hD_1$, $hD_2$ exhibiting each as representing the functor of rigidified invertible modules on the relevant relative curve whose geometric fibres are algebraically equivalent to zero, so each carries a Poincaré bundle and the universal classifying property. Let $\nu_1,\nu_2$ be morphisms $D.P\to D_1.P$, $D.P\to D_2.P$ over $\operatorname{Spec}k$, where $\nu_1$ is the classifying morphism of the pullback of $D$'s Poincaré bundle along $i_1$, and $\nu_2$ is pinned by the hypothesis that for every $t\colon T\to\operatorname{Spec}k$ and every $a\colon T\to D.P$ over $k$, the pullback of $D_2$'s Poincaré bundle along $a$ followed by $\nu_2$ is isomorphic to the rigidification along $\varepsilon_2$ of the pullback along $i_2$ of the bundle classified by $a$. Then for every point $b$ of $D_1.P\times_{\operatorname{Spec}k}D_2.P$ there are an open subscheme $U$ of that fibre product with $b\in U$ and a morphism $\sigma\colon U\to D.P$ such that $\sigma$ followed by $(\nu_1,\nu_2)\colon D.P\to D_1.P\times_{\operatorname{Spec}k}D_2.P$ is the open immersion $U\hookrightarrow D_1.P\times_{\operatorname{Spec}k}D_2.P$.
--
--   This is the Zariski-local splitting of the restriction map $\operatorname{Pic}^0_X\to\operatorname{Pic}^0_{C_1}\times\operatorname{Pic}^0_{C_2}$ for a curve obtained by gluing two smooth proper geometrically integral curves at finitely many points, the geometric input behind the statement that this map is faithfully flat. It is used to derive flatness and surjectivity of the pair $(\nu_1,\nu_2)$, and through that in the analysis of relative group laws on the special fibre of $X_1(p)$ and the split torus occurring there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_opens_section_restrictPair_of_twoGluedSmoothCurves.lean

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

theorem AlgebraicGeometry.RelPicard.exists_opens_section_restrictPair_of_twoGluedSmoothCurves
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
    ∀ b : ↥(pullback D₁.toBase D₂.toBase), ∃ U : (pullback D₁.toBase D₂.toBase).Opens, b ∈ U ∧
      ∃ σ : (U : Scheme.{u}) ⟶ D.P, σ ≫ pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm) = U.ι := by sorry
