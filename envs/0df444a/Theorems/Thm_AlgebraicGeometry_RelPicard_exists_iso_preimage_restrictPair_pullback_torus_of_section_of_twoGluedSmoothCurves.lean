-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_iso_preimage_restrictPair_pullback_torus_of_section_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.exists_iso_preimage_restrictPair_pullback_torus_of_section_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/7821fc2f-34bd-5ebc-b2b1-e709e8cf14d9
-- title:
--   Local triviality of the Pic⁰ restriction pair as a torus bundle
-- statement:
--   Let $k$ be an algebraically closed field and let $x\colon X\to\operatorname{Spec}k$ be proper with $X$ reduced, and $c_1\colon C_1\to\operatorname{Spec}k$, $c_2\colon C_2\to\operatorname{Spec}k$ proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1,i_2$ be closed immersions $C_1\to X$, $C_2\to X$ commuting with the structure morphisms, whose images cover the points of $X$ set-theoretically, with $C_1\times_X C_2$ reduced and $\operatorname{Nat.card}$ of its underlying space equal to $s>0$. Let $\varepsilon,\varepsilon_1,\varepsilon_2$ be sections of $x,c_1,c_2$ with $\varepsilon_1$ followed by $i_1$ equal to $\varepsilon$. Let $D,D_1,D_2$ be relative $\mathrm{Pic}^0$ designations (a scheme with a structure morphism to $\operatorname{Spec}k$ and a zero section) representing, via `RepresentsRelSubPic`, the condition `algEquivZeroCut` that a rigidified line bundle be fibrewise algebraically equivalent to zero, for $(x,\varepsilon)$, $(c_1,\varepsilon_1)$, $(c_2,\varepsilon_2)$ respectively. Let $\nu_1,\nu_2$ be morphisms $D.\mathrm{toBase}\to D_1.\mathrm{toBase}$, $D_2.\mathrm{toBase}$ over $k$, with $\nu_1$ the restriction morphism `RepresentsRelSubPic.pullbackHom` along $i_1$, and $\nu_2$ characterised by the requirement that for every $k$-scheme $t\colon T\to\operatorname{Spec}k$ and every $T$-point $a$ of $D.\mathrm{toBase}$ over $k$, the Poincaré bundle of $D_2$ pulled back along $a$ followed by $\nu_2$ is isomorphic to the `rigidify`-normalisation, with respect to the section `rigSection` $c_2\,t\,\varepsilon_2$ and the projection $C_2\times_k T\to T$, of the pullback along `curveChange` $i_2$ of the Poincaré bundle of $D$ pulled back along $a$. Assume $\nu_1$ and $\nu_2$ are additive for the relative group laws attached to `algEquivZeroGroupCut` on $T$-points, and let $\tau$ be a closed immersion of the split torus $\mathbb{G}_{m,k}^{\,s-1}$ into $D.\mathrm{toBase}$ over $k$ whose $T$-points are exactly those $a$ with $a\nu_1$ and $a\nu_2$ both the identity section of the respective group law, for every $T$. Finally let $U$ be an open subscheme of $D_1.\mathrm{toBase}\times_{\operatorname{Spec}k}D_2.\mathrm{toBase}$ and $\sigma\colon U\to D.P$ a section over $U$ of $\pi=(\nu_1,\nu_2)$, i.e. $\sigma$ followed by $\pi$ equals the inclusion $U.\iota$. Then there is an isomorphism $e$ from $\pi^{-1}(U)$ to the fibre product of $U$ (with structure morphism $U.\iota$ followed by the first projection and $D_1.\mathrm{toBase}$) and $\mathbb{G}_{m,k}^{\,s-1}$, such that $e$ followed by the first projection is the restriction of $\pi$ to $\pi^{-1}(U)\to U$.
--
--   This is the local triviality step in the description of the relative $\mathrm{Pic}^0$ of a curve obtained by gluing two smooth proper curves along $s$ points: over an open set where the restriction pair $\pi=(\nu_1,\nu_2)$ admits a section, $\pi$ is a trivial torsor under the $(s-1)$-dimensional split torus which is its fibrewise kernel. It is used by [`AlgebraicGeometry.RelPicard.flat_surjective_restrictPair_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.flat_surjective_restrictPair_of_twoGluedSmoothCurves) to deduce flatness and surjectivity of $\pi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_iso_preimage_restrictPair_pullback_torus_of_section_of_twoGluedSmoothCurves.lean

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

theorem AlgebraicGeometry.RelPicard.exists_iso_preimage_restrictPair_pullback_torus_of_section_of_twoGluedSmoothCurves
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
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L)))
    (hν₁mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a b : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul t a b) ν₁ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).mul t
            (NeronModelInfra.schemeHomOverComp a ν₁) (NeronModelInfra.schemeHomOverComp b ν₁))
    (hν₂mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a b : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul t a b) ν₂ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).mul t
            (NeronModelInfra.schemeHomOverComp a ν₂) (NeronModelInfra.schemeHomOverComp b ν₂))
    (τ : SchemeHomOver (torusStr k (s - 1)) D.toBase) (hτ : IsClosedImmersion τ.1)
    (hτker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        (NeronModelInfra.schemeHomOverComp a ν₁ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one t ∧
          NeronModelInfra.schemeHomOverComp a ν₂ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one t) ↔
        ∃ y : SchemeHomOver t (torusStr k (s - 1)), NeronModelInfra.schemeHomOverComp y τ = a)
    (U : (pullback D₁.toBase D₂.toBase).Opens) (σ : (U : Scheme.{u}) ⟶ D.P)
    (hσ : σ ≫ pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm) = U.ι) :
    ∃ e : ((pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm)) ⁻¹ᵁ U : Scheme.{u}) ≅
        pullback (U.ι ≫ pullback.fst D₁.toBase D₂.toBase ≫ D₁.toBase) (torusStr k (s - 1)),
      e.hom ≫ pullback.fst (U.ι ≫ pullback.fst D₁.toBase D₂.toBase ≫ D₁.toBase) (torusStr k (s - 1)) =
        (pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm)) ∣_ U := by sorry
