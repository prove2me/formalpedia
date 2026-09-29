-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_pullbackHom_points_eq_pic0_congr_of_iso
-- name    : AlgebraicGeometry.RelPicard.pullbackHom_points_eq_pic0_congr_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/b1ba48df-6f5c-5ad3-9f41-de2e2515c4f4
-- title:
--   Picard pullback along a curve isomorphism transports divisor classes
-- statement:
--   Fix a commutative ring $R$ and two schemes $C$, $C'$ with structure morphisms $c$, $c'$ to $\operatorname{Spec} R$, each proper, smooth of relative dimension $1$ and geometrically integral, together with sections $\varepsilon$, $\varepsilon'$ of $c$, $c'$ (morphisms $\operatorname{Spec} R \to C$, resp. $C'$, splitting the structure morphism). Let $f : C' \cong C$ be an isomorphism with $f$ followed by $c$ equal to $c'$ and with $\varepsilon'$ followed by $f$ equal to $\varepsilon$. Let $D$, $D'$ be designations (a scheme over $\operatorname{Spec} R$ with a zero section) and $h$, $h'$ data exhibiting them as representing the rigidified relative Picard functors of $(c,\varepsilon)$, $(c',\varepsilon')$ cut out by the condition `algEquivZeroCut` of fibrewise algebraic equivalence to zero: each consists of a Poincaré rigidified line bundle over the representing object satisfying that condition, the universal property classifying all such bundles uniquely, and triviality at the zero section. Let $aj : C \to D$, $aj' : C' \to D'$ be morphisms over $\operatorname{Spec} R$ which are Abel–Jacobi maps in the sense that for every field $K_0$, every $t : \operatorname{Spec} K_0 \to \operatorname{Spec} R$ and every point $x$ of $C$ over $t$, the pullback of the Poincaré bundle along $x$ followed by $aj$ is isomorphic to the line bundle $\mathcal O(\Gamma_x)$ (the dual of the ideal sheaf of the graph of $x$) tensored with the ideal module of the relative divisor given by $t$ followed by $\varepsilon$, and likewise for $aj'$, $\varepsilon'$. Let further $K$ be an algebraically closed field, $i : R \to K$ a ring homomorphism, $F$, $F'$ fields over $K$ each satisfying `IsCurveOver` (existence of principal divisors of degree zero, finite residue extensions at all places, and $\Omega_{F/K}$ free of rank one), $e_F : F \cong F'$ a ring isomorphism fixing $K$, and $M$, $M'$ curve models of $F$, $F'$ whose underlying schemes are identified, by isomorphisms $e$, $e'$ compatible with the structure morphisms, with the base changes of $C$, $C'$ along $\operatorname{Spec} i$. Assume: $f$ transports $K$-points compatibly with places, namely whenever a $K$-point $x$ of $M$ and a $K$-point $y$ of $M'$ have the same image in $C$ (after $e$, projection, and for $y$ additionally $f$), the place attached to $y$ is the image under `Place.congrRingEquiv` along $e_F$ of the place attached to $x$; bijections $pts$, $pts'$ from $\operatorname{Pic}^0 K F$, $\operatorname{Pic}^0 K F'$ to the sets of $\operatorname{Spec} K$-points of $D$, $D'$ which are additive for the relative group laws induced by $h$, $h'$ for the group cuts `algEquivZeroGroupCut`, and which are normalised by $aj$, $aj'$: for $K$-points $x$ and $s$ with $s$ the base point, the class of $[x]-[s]$ is sent to $x$ followed by the projection and $aj$ (respectively $aj'$). Then for every $z \in \operatorname{Pic}^0 K F$ the $K$-point $pts'(\operatorname{congr}_{e_F} z)$ equals $pts(z)$ followed by `RepresentsRelSubPic.pullbackHom` of $f$, the morphism $D \to D'$ over $\operatorname{Spec} R$ classifying the pullback of the Poincaré bundle along $f$.
--
--   This is one leg of the dictionary between the scheme-theoretic relative $\operatorname{Pic}^0$ and divisor class groups of function fields: it identifies, on geometric points, the Picard functoriality morphism attached to an isomorphism of pointed curves with transport of divisor classes along the corresponding isomorphism of function fields. It is the isomorphism case needed when two models of a modular curve are identified, and is used in the comparison of the Néron objects attached to $J_0$ and $J_H$ at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_pullbackHom_points_eq_pic0_congr_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_Pic0Congr

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicCurve
universe u v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem AlgebraicGeometry.RelPicard.pullbackHom_points_eq_pic0_congr_of_iso
    (R : Type u) [CommRing R]
    {C C' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    [IsProper c'] [SmoothOfRelativeDimension 1 c'] [GeometricallyIntegral c']
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c')
    (f : C' ≅ C) (hf : f.hom ≫ c = c') (hε : ε'.1 ≫ f.hom = ε.1)
    (D : RelativePic0Designation R c) (D' : RelativePic0Designation R c')
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (aj : SchemeHomOver c D.toBase) (aj' : SchemeHomOver c' D'.toBase)
    (haj : ∀ (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (haj' : ∀ (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t c'),
        Nonempty ((h'.poincare.pullbackAlong
            ⟨x.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj'.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c' x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c' (t ≫ ε'.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε'.2).trans (Category.comp_id t)))).idealModule))
    (K : Type u) [Field K] [IsAlgClosed K] (i : R →+* K)
    (F F' : Type v) [Field F] [Field F'] [Algebra K F] [Algebra K F'] [IsCurveOver K F] [IsCurveOver K F']
    (eF : F ≃+* F') (heF : ∀ a : K, eF (algebraMap K F a) = algebraMap K F' a)
    (M : CurveModel K F) (M' : CurveModel K F')
    (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e]
    (he : e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase)
    (e' : M'.C ⟶ pullback c' (Spec.map (CommRingCat.ofHom i))) [IsIso e']
    (he' : e' ≫ pullback.snd c' (Spec.map (CommRingCat.ofHom i)) = M'.toBase)

    (hfK : ∀ (y : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
        y.1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) ≫ f.hom →
      M'.pointEquivPlace y = AlgebraicCurve.Place.congrRingEquiv eF heF (M.pointEquivPlace x))
    (pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase)
    (hadd : ∀ x y : Pic0 K F,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
        Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := K) (F := F),
        (Dv : Divisor K F) =
          Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 =
          x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ aj.1)
    (pts' : Pic0 K F' ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D'.toBase)
    (hadd' : ∀ x y : Pic0 K F',
      pts' (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul (Spec.map (CommRingCat.ofHom i)) (pts' x) (pts' y))
    (hnorm' : ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _}),
      s.1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) =
        Spec.map (CommRingCat.ofHom i) ≫ ε'.1 →
      ∃ Dv : Divisor.degZero (K := K) (F := F'),
        (Dv : Divisor K F') =
          Finsupp.single (M'.pointEquivPlace x) 1 - Finsupp.single (M'.pointEquivPlace s) 1 ∧
        (pts' (Pic0.mk Dv)).1 =
          x.1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) ≫ aj'.1) :
    ∀ z : Pic0 K F,
      (pts' (Pic0.congr eF heF z)).1 = (pts z).1 ≫ (RepresentsRelSubPic.pullbackHom f.hom hf hε h h').1 := by sorry
