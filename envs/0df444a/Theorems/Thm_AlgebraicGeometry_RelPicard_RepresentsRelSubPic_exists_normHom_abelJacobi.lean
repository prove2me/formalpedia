-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_normHom_abelJacobi
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_normHom_abelJacobi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/d9d8fb0e-6573-5571-b796-d0361b4bfd62
-- title:
--   Norm homomorphism between representatives of relative Pic⁰
-- statement:
--   Let $K$ be a field and let $c : C \to \operatorname{Spec} K$ be proper and smooth of relative dimension one, with a section $\varepsilon$ (a $K$-point of $C$). Let $D$ consist of a $K$-scheme $D.P$ with structure morphism $D.\mathrm{toBase}$ and a zero section, and let $h$ assert that $D$ represents, via a rigidified Poincaré bundle on $C \times_K D.P$, the subpresheaf of the $\varepsilon$-rigidified relative Picard presheaf of $c$ cut out by the predicate `FibrewiseAlgEquivZero`: the Poincaré bundle satisfies that predicate, every rigidified bundle $M$ over $t : T \to \operatorname{Spec} K$ satisfying it is induced by a unique $K$-morphism $T \to D.P$, and the zero section pulls the Poincaré bundle back to the unit. Let $\mathrm{aj} : C \to D.P$ be a $K$-morphism such that for every $K$-point $x$ of $C$ the pullback of the Poincaré bundle along $x \circ \mathrm{aj}$ is isomorphic to the inverse ideal module of the relative effective Cartier divisor of $x$ tensored with the ideal module of that of $\varepsilon$, i.e. to $\mathcal{O}(x) \otimes \mathcal{O}(-\varepsilon)$. Let $c' : C' \to \operatorname{Spec} K$, $\varepsilon'$, $D'$, $h'$, $\mathrm{aj}'$ be a second such package, and let $\pi : C' \to C$ satisfy $c \circ \pi = c'$, be finite, flat and locally of finite presentation with $\pi$ of constant rank $d$ at every point of $C$. Then there is a $K$-morphism $N : D'.P \to D.P$ such that: composition with $N$ carries the product of any two $T$-points $x,y$ of $D'.P$ over any $t : T \to \operatorname{Spec} K$, for the relative group law furnished by $h'$ for the group cut `algEquivZeroGroupCut`, to the product of $x \circ N$ and $y \circ N$ for the corresponding law furnished by $h$; $N$ takes the zero section of $D'$ to that of $D$; and for every $K$-point $y$ of $C'$ the product, in the group of $K$-points of $D.P$, of $N(\mathrm{aj}'(y))$ with $\mathrm{aj}(\pi(\varepsilon'))$ equals $\mathrm{aj}(\pi(y))$.
--
--   This is the norm (Albanese) homomorphism $\pi_* : \mathrm{Pic}^0_{C'} \to \mathrm{Pic}^0_{C}$ attached to a finite flat morphism $\pi : C' \to C$ of smooth proper curves, obtained by norming line bundles along $\pi$ and read off on the representing schemes, together with the resulting translation formula on the Abel–Jacobi images of points. It is used by [`AlgebraicCurve.Pic0.exists_schemeHomOver_pushforwardAlong_of_representsRelSubPic`](thm.html#AlgebraicCurve.Pic0.exists_schemeHomOver_pushforwardAlong_of_representsRelSubPic) in the construction of the pushforward maps between Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_normHom_abelJacobi.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_normHom_abelJacobi
    {K : Type u} [Field K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : {q : Spec (CommRingCat.of K) ⟶ C // q ≫ c = 𝟙 _})
    (D : RelativePic0Designation K c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (aj : SchemeHomOver c D.toBase)
    (haj : ∀ x : {q : Spec (CommRingCat.of K) ⟶ C // q ≫ c = 𝟙 _},
      Nonempty ((h.poincare.pullbackAlong
          ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (𝟙 (Spec (CommRingCat.of K)) ≫ ε.1)
            ((Category.assoc _ _ _).trans ((congrArg (𝟙 (Spec (CommRingCat.of K)) ≫ ·) ε.2).trans
              (Category.comp_id _)))).idealModule))
    {C' : Scheme.{u}} (c' : C' ⟶ Spec (CommRingCat.of K)) [IsProper c'] [SmoothOfRelativeDimension 1 c']
    (ε' : {q : Spec (CommRingCat.of K) ⟶ C' // q ≫ c' = 𝟙 _})
    (D' : RelativePic0Designation K c')
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (aj' : SchemeHomOver c' D'.toBase)
    (haj' : ∀ x : {q : Spec (CommRingCat.of K) ⟶ C' // q ≫ c' = 𝟙 _},
      Nonempty ((h'.poincare.pullbackAlong
          ⟨x.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj'.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c' x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c' (𝟙 (Spec (CommRingCat.of K)) ≫ ε'.1)
            ((Category.assoc _ _ _).trans ((congrArg (𝟙 (Spec (CommRingCat.of K)) ≫ ·) ε'.2).trans
              (Category.comp_id _)))).idealModule))
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ x : C, π.finrank x = d) :
    ∃ N : SchemeHomOver D'.toBase D.toBase,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t D'.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul t x y) N =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t
            (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N)) ∧
      D'.zeroSection ≫ N.1 = D.zeroSection ∧
      ∀ y : {q : Spec (CommRingCat.of K) ⟶ C' // q ≫ c' = 𝟙 _},
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (𝟙 _)
            ⟨(y.1 ≫ aj'.1) ≫ N.1,
              (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ aj'.1) ≫ ·) N.2).trans
                ((Category.assoc _ _ _).trans ((congrArg (y.1 ≫ ·) aj'.2).trans y.2)))⟩
            ⟨(ε'.1 ≫ π) ≫ aj.1,
              (Category.assoc _ _ _).trans ((congrArg ((ε'.1 ≫ π) ≫ ·) aj.2).trans
                ((Category.assoc _ _ _).trans ((congrArg (ε'.1 ≫ ·) hπ).trans ε'.2)))⟩ =
          ⟨(y.1 ≫ π) ≫ aj.1,
            (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ π) ≫ ·) aj.2).trans
              ((Category.assoc _ _ _).trans ((congrArg (y.1 ≫ ·) hπ).trans y.2)))⟩ := by sorry
