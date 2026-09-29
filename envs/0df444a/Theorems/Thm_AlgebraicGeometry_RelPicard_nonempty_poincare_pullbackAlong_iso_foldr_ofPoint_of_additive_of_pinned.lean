-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_poincare_pullbackAlong_iso_foldr_ofPoint_of_additive_of_pinned
-- name    : AlgebraicGeometry.RelPicard.nonempty_poincare_pullbackAlong_iso_foldr_ofPoint_of_additive_of_pinned
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/76aac281-ac1a-5764-8996-c33350a2ecc2
-- title:
--   Reading the Poincaré bundle at every degree-zero class
-- statement:
--   Let $k$ be an algebraically closed field and $c \colon C \to \operatorname{Spec} k$ proper, smooth of relative dimension $1$ and geometrically integral, with a section $\varepsilon$ of $c$. Let $D$ consist of a scheme with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} k$ and a zero section, and let `hD` witness that $D$ represents the functor of rigidified line bundles on the fibre products of $c$ that are fibrewise algebraically equivalent to zero, i.e. it provides a Poincaré rigidified bundle `hD.poincare` over $D.\mathrm{toBase}$ satisfying that condition, together with the universal property and the triviality along the zero section. Let $F$ be a field extension of $k$ in which every nonzero element has a divisor of degree zero recording its order at each place, let $\mathrm{Mdl}$ be a curve model of $F/k$ together with an isomorphism $e \colon \mathrm{Mdl}.C \cong C$ compatible with the structure morphisms, and let $\mathrm{pt}$ assign to each place $v$ of $F/k$ the $k$-point of $C$ obtained from the point of $\mathrm{Mdl}.C$ corresponding to $v$ under $\mathrm{Mdl}.\mathrm{pointEquivPlace}$, composed with $e$. Let $\Phi$ send each degree-zero divisor class of $F/k$ to a $k$-point of $D$, subject to two hypotheses: $\Phi$ is additive for the relative group law on $D.\mathrm{toBase}$ induced by `hD` for the group-theoretic algebraic-equivalence-to-zero condition; and $\Phi$ is pinned on differences of points, in the sense that for every section $P$ of $c$ and every degree-zero divisor whose underlying divisor is the difference of the place of $P$ and the place of $\varepsilon$ (each with coefficient $1$), the pullback of the Poincaré bundle along $\Phi$ of its class is isomorphic to the dual of the ideal module of the relative effective Cartier divisor cut out by the graph of $P$, tensored with the ideal module of the divisor cut out by the graph of $\varepsilon$. Then for every degree-zero divisor $Dv$ of $F/k$ the pullback of the Poincaré bundle along $\Phi(\,[Dv]\,)$ is isomorphic to the iterated tensor product, formed by folding over the support of $Dv$ listed in some order and starting from the unit module, of the dual of the ideal module of $I_{\mathrm{pt}(v)}^{\,(Dv\,v)^{+}}$ tensored with the ideal module of $I_{\mathrm{pt}(v)}^{\,(-Dv\,v)^{+}}$, where $I_{\mathrm{pt}(v)}$ is the ideal sheaf of the graph of the point $\mathrm{pt}(v)$ and $(\cdot)^{+}$ denotes the truncation of an integer to a natural number. All isomorphisms are asserted in the form of nonemptiness of the corresponding type.
--
--   This is the reading lemma for the dictionary between degree-zero divisor classes of a function field and $k$-points of a representing object for the relative $\mathrm{Pic}^0$ functor: additivity together with the pin on the generators $[P]-[\varepsilon]$ determines the Poincaré bundle at every class, the $\varepsilon$-contributions cancelling because the divisor has degree zero. It is used in the identification of the map $\Phi$ with the canonical one, in the construction of admissible morphisms out of two glued smooth curves, and in the corresponding computation on the modular curve $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_poincare_pullbackAlong_iso_foldr_ofPoint_of_additive_of_pinned.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.TwoGluedCurves AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.nonempty_poincare_pullbackAlong_iso_foldr_ofPoint_of_additive_of_pinned
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 _) c)
    (D : RelativePic0Designation k c) (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F]
    (Mdl : CurveModel k F) (e : Mdl.C ≅ C) (he : e.hom ≫ c = Mdl.toBase)
    (pt : Place k F → (Spec (CommRingCat.of k) ⟶ C)) (hpt : ∀ v, pt v ≫ c = 𝟙 _)
    (hpt' : ∀ v, pt v = (Mdl.pointEquivPlace.symm v).1 ≫ e.hom)
    (Φ : Pic0 k F → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase)
    (hΦ_add : ∀ a b, Φ (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ (Φ a) (Φ b))
    (hΦ : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (Dv : Divisor.degZero (K := k) (F := F)),
      (Dv : Divisor k F) =
        Finsupp.single (Mdl.pointEquivPlace ⟨P.1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact P.2⟩) 1 -
          Finsupp.single (Mdl.pointEquivPlace ⟨ε.1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact ε.2⟩) 1 →
      Nonempty ((hD.poincare.pullbackAlong (Φ (Pic0.mk Dv))).L ≅
        (RelEffCartierDiv.ofPoint c P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c ε.1 ε.2).idealModule))
    (Dv : Divisor.degZero (K := k) (F := F)) :
    Nonempty ((hD.poincare.pullbackAlong (Φ (Pic0.mk Dv))).L ≅
          ((((Dv : Divisor k F)).support.toList).foldr
            (fun v M => ((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I ^ (((Dv : Divisor k F)) v).toNat).invModule ⊗
              ((RelEffCartierDiv.ofPoint c (pt v) (hpt v)).I ^ (-(((Dv : Divisor k F)) v)).toNat).module ⊗ M)
            (𝟙_ (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules))) := by sorry
