-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_torus_ker_restrictPair_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.exists_torus_ker_restrictPair_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/34cecfbe-bb4d-5dd6-932a-208cb28c4204
-- title:
--   Node-unit torus as kernel of restriction on Pic⁰
-- statement:
--   Let $k$ be an algebraically closed field, $x\colon X\to\operatorname{Spec}k$ a proper morphism with $X$ reduced, and $c_1\colon C_1\to\operatorname{Spec}k$, $c_2\colon C_2\to\operatorname{Spec}k$ proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1,i_2$ be morphisms $C_1\to X$, $C_2\to X$ commuting with the structure morphisms, both closed immersions, such that every point of $X$ lies in the image of $i_1$ or of $i_2$; assume the fibre product $C_1\times_X C_2$ is reduced and has exactly $s$ points with $s>0$. Fix sections $\varepsilon$ of $x$, $\varepsilon_1$ of $c_1$ with $i_1\circ\varepsilon_1=\varepsilon$, and $\varepsilon_2$ of $c_2$. Let $D$, $D_1$, $D_2$ be pointed $k$-schemes (each with a structure morphism to $\operatorname{Spec}k$ and a zero section) together with data $hD$, $hD_1$, $hD_2$ exhibiting them as representing, for $(x,\varepsilon)$, $(c_1,\varepsilon_1)$, $(c_2,\varepsilon_2)$ respectively, the functor of rigidified invertible modules on the base change satisfying `FibrewiseAlgEquivZero`: a Poincaré bundle satisfying that condition, a unique classifying morphism for every such rigidified bundle on every $T$, and an isomorphism of its pullback along the zero section with the unit. Let $\nu_1,\nu_2\colon D\to D_1,D_2$ be morphisms over $\operatorname{Spec}k$; assume $\nu_1$ is the restriction morphism `RepresentsRelSubPic.pullbackHom` attached to $i_1$ (the classifying map of the pullback of the Poincaré bundle of $D$ along $i_1$, rigidified via $\varepsilon_1$), and that $\nu_2$ satisfies the corresponding functorial characterisation: for every $t\colon T\to\operatorname{Spec}k$ and every $T$-point $a$ of $D$ over $t$, the bundle obtained by pulling back the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the `rigidify`-normalisation, with respect to the section `rigSection c₂ t ε₂` and the projection $C_2\times_k T\to T$, of the pullback of $(hD.\mathrm{poincare}.\mathrm{pullbackAlong}\ a).L$ along `curveChange i₂.1 i₂.2 t`. The conclusion asserts the existence of a morphism $\tau\colon\mathbb G_{m,k}^{s-1}=\operatorname{Spec}k[\mathbb Z^{s-1}]\to D$ over $\operatorname{Spec}k$ (the source being `torusStr k (s-1)`, with $s-1$ truncated subtraction) such that: (1) for all $\chi,\chi'$ in the convolution monoid of $k$-algebra homomorphisms $k[\mathbb Z^{s-1}]\to k$, the $k$-point of $D$ obtained from $\chi\chi'$ by composing with $\tau$ is the product, under the relative group law on $D$ coming from $hD$ and `algEquivZeroGroupCut x ε`, of those obtained from $\chi$ and from $\chi'$; (2) for every $k$-scheme $t\colon T\to\operatorname{Spec}k$ and every $T$-point $a$ of $D$ over $t$, the conjunction of $a$ followed by $\nu_1$ being the identity section of the group law on $D_1$ and $a$ followed by $\nu_2$ being the identity section of the group law on $D_2$ holds if and only if $a$ factors as a $T$-point $y$ of $\mathbb G_{m,k}^{s-1}$ followed by $\tau$; and (3) $\tau$ is injective on $k$-points, i.e. two sections of $\mathbb G_{m,k}^{s-1}$ over $\operatorname{Spec}k$ with the same composite with $\tau$ coincide. Thus multiplicativity in (1) is asserted only on $k$-points, not as an identity of group-scheme morphisms, and no assertion is made that $\tau$ is a closed immersion.
--
--   This is the description of the kernel of the restriction pair $(\nu_1,\nu_2)$ on $\mathrm{Pic}^0$ of a curve obtained by gluing two smooth proper curves transversally at $s$ points: the kernel is the torus of node units $\mathbb G_m^{s-1}$, as in the exact sequence $1\to k^\times\to k^\times\times k^\times\to (k^\times)^s\to\operatorname{Pic}X\to\operatorname{Pic}C_1\times\operatorname{Pic}C_2$ of Bosch–Lütkebohmert–Raynaud. It feeds the variant [`AlgebraicGeometry.RelPicard.exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves), where the map $\tau$ is upgraded to a closed immersion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_torus_ker_restrictPair_of_twoGluedSmoothCurves.lean

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

theorem AlgebraicGeometry.RelPicard.exists_torus_ker_restrictPair_of_twoGluedSmoothCurves
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
        ∃ y : SchemeHomOver t (torusStr k (s - 1)), NeronModelInfra.schemeHomOverComp y τ = a) ∧
      (∀ y y' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (torusStr k (s - 1)),
        NeronModelInfra.schemeHomOverComp y τ = NeronModelInfra.schemeHomOverComp y' τ → y = y') := by sorry
