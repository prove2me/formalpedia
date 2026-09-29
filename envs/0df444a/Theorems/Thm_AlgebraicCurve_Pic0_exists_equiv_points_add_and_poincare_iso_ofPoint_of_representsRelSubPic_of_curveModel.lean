-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_equiv_points_add_and_poincare_iso_ofPoint_of_representsRelSubPic_of_curveModel
-- name    : AlgebraicCurve.Pic0.exists_equiv_points_add_and_poincare_iso_ofPoint_of_representsRelSubPic_of_curveModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/f117c987-c924-5bbe-97e5-f221642af5b6
-- title:
--   Abel–Jacobi dictionary for Pic⁰ of a curve
-- statement:
--   Let $k$ be an algebraically closed field and let $c \colon C \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, with $\varepsilon$ a section of $c$ (a $k$-point of $C$). Let $D$ consist of a scheme with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} k$ and a zero section, and let `hD` witness that $D$ represents the relative $\mathrm{Pic}^0$-type functor cut out by `algEquivZeroCut c ε`: there is a rigidified line bundle `hD.poincare` on the pullback of $c$ along $D.\mathrm{toBase}$, all of whose fibres over points with algebraically closed residue field are algebraically equivalent to zero, such that every rigidified line bundle on the pullback of $c$ along any $t \colon T \to \operatorname{Spec} k$ with that fibrewise property is isomorphic to the pullback of `hD.poincare` along a unique $T$-point of $D$, the pullback along the zero section being trivial. Assume $D.\mathrm{toBase}$ is smooth, proper and geometrically connected. Let $F$ be a field extension of $k$ which is a curve over $k$ in the sense that each place has residue field finite over $k$, $\Omega_{F/k}$ is free of rank one, and every nonzero function has a principal divisor of degree zero, and assume that $L(0) \subseteq F$ is the image of $k$. Let $\mathrm{Mdl}$ be a curve model of $F$ over $k$ (a proper, smooth, relative-dimension-one integral scheme with function field identified with $F$ and closed points in bijection with the places of $F/k$) and let $e \colon \mathrm{Mdl}.C \cong C$ be an isomorphism of schemes with $e$ followed by $c$ equal to $\mathrm{Mdl}.\mathrm{toBase}$. Then there is a bijection $\Phi$ from $\mathrm{Pic}^0(F/k)$, the group of degree-zero divisors of $F/k$ modulo principal divisors, onto the set of sections of $D.\mathrm{toBase}$, such that (i) $\Phi(a+b)$ is the product of $\Phi(a)$ and $\Phi(b)$ for the relative group law attached by `RepresentsRelSubPic.relativeGroupLaw` to the group-theoretic refinement `algEquivZeroGroupCut c ε` of the cut, and (ii) for every $k$-point $P$ of $C$ and every degree-zero divisor $Dv$ of $F/k$ which equals the difference of the point masses $1$ at the places corresponding, under the bijection $\mathrm{Mdl}.\mathrm{pointEquivPlace}$ and transport along $e^{-1}$, to $P$ and to $\varepsilon$, the pullback of `hD.poincare` along $\Phi$ of the class of $Dv$ is isomorphic to the tensor product of the dual of the ideal sheaf module of the relative effective Cartier divisor $\mathrm{ofPoint}\,P$ with the ideal sheaf module of $\mathrm{ofPoint}\,\varepsilon$, that is to $\mathcal O(P) \otimes \mathcal O(-\varepsilon)$.
--
--   This is the Abel–Jacobi normalised identification of the degree-zero divisor class group of a one-variable function field $F/k$ with the $k$-points of the Jacobian, stated for a given representing object $(D, \mathcal P)$ of the rigidified $\mathrm{Pic}^0$ functor and its canonical group law. Since the classes $[P]-[\varepsilon]$ generate $\mathrm{Pic}^0$ and $\Phi$ is additive, clause (ii) pins $\Phi$ down; it serves as the points dictionary used downstream, and is applied by the variant of this statement phrased for an algebraically closed base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_equiv_points_add_and_poincare_iso_ofPoint_of_representsRelSubPic_of_curveModel.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_equiv_points_add_and_poincare_iso_ofPoint_of_representsRelSubPic_of_curveModel
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (D : RelativePic0Designation k c) (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (F : Type u) [Field F] [Algebra k F] [IsCurveOver k F] [HasPrincipalDivisors k F] (hCB : ConstantsAreBase k F)
    (Mdl : CurveModel k F) (e : Mdl.C ≅ C) (he : e.hom ≫ c = Mdl.toBase) :
    ∃ Φ : Pic0 k F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,

      (∀ a b, Φ (a + b) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ (Φ a) (Φ b)) ∧

      (∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (Dv : Divisor.degZero (K := k) (F := F)),
        (Dv : Divisor k F) =
          Finsupp.single (Mdl.pointEquivPlace ⟨P.1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact P.2⟩) 1 -
            Finsupp.single (Mdl.pointEquivPlace ⟨ε.1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact ε.2⟩) 1 →
        Nonempty ((hD.poincare.pullbackAlong (Φ (Pic0.mk Dv))).L ≅
          (RelEffCartierDiv.ofPoint c P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c ε.1 ε.2).idealModule)) := by sorry
