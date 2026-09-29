-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_equiv_points_add_and_poincare_iso_ofPoint_of_representsRelSubPic_of_curveModel_of_isAlgClosed
-- name    : AlgebraicCurve.Pic0.exists_equiv_points_add_and_poincare_iso_ofPoint_of_representsRelSubPic_of_curveModel_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/38936881-b4b4-5994-b39b-28185e82e826
-- title:
--   Points dictionary for any object representing rigidified Pic⁰
-- statement:
--   Let $k$ be an algebraically closed field and let $c : C \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, with $\varepsilon$ a $k$-point of $C$, i.e. a morphism $\operatorname{Spec} k \to C$ composing with $c$ to the identity. Let $D$ consist of a scheme with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} k$ and a section of it, and let $hD$ assert that $D$ represents the rigidified Picard functor of $(C,\varepsilon)$ cut out by the condition `algEquivZeroCut`, that is: a rigidified line bundle $hD.\mathrm{poincare}$ on $C\times_k D$ satisfying the condition whose pullback along the section is trivial, and such that for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every rigidified line bundle $M$ on $C\times_k T$ satisfying the condition there is a unique $T$-point $g$ of $D$ over $k$ with $(hD.\mathrm{poincare})|_g \cong M$; no smoothness, properness or connectedness of $D$ is assumed. Let $F$ be a field over $k$ with `IsCurveOver k F` (principal divisors of degree zero exist for all nonzero elements, every place has residue field finite over $k$, and $\Omega_{F/k}$ is free of rank one over $F$), together with `HasPrincipalDivisors k F` again as a hypothesis, and with $L(0)$ equal to the image of $k$ in $F$. Let $\mathrm{Mdl}$ be a curve model of $F$ over $k$ (an integral scheme, proper and smooth of relative dimension $1$ over $k$, with function field identified with $F$ over $k$ and closed points in bijection with the places of $F/k$ compatibly with valuation rings), and let $e : \mathrm{Mdl}.C \cong C$ be an isomorphism with $e.\mathrm{hom}$ followed by $c$ equal to $\mathrm{Mdl}.\mathrm{toBase}$. Then there is a bijection $\Phi$ from $\mathrm{Pic}^0(F/k)$, the group of degree-zero divisors modulo principal ones, to the set of $k$-points of $D$ such that: (i) $\Phi(a+b)$ is the product of $\Phi(a)$ and $\Phi(b)$ for the relative group law on points of $D$ obtained from the representability $hD$ for the group condition `algEquivZeroGroupCut`; and (ii) for every $k$-point $P$ of $C$ and every degree-zero divisor $Dv$ of $F/k$ which equals $\delta_{v_P} - \delta_{v_\varepsilon}$, where $v_P$ and $v_\varepsilon$ are the places corresponding under $\mathrm{Mdl}.\mathrm{pointEquivPlace}$ to the $k$-points $P$ followed by $e.\mathrm{inv}$ and $\varepsilon$ followed by $e.\mathrm{inv}$ of $\mathrm{Mdl}.C$, the pullback of $hD.\mathrm{poincare}$ along $\Phi([Dv])$ has underlying module isomorphic to the dual of the ideal module of the graph of $P$ tensored with the ideal module of the graph of $\varepsilon$, both taken as relative effective Cartier divisors of degree $1$ on $C$ over $k$.
--
--   This is the dictionary between the divisor-class group $\mathrm{Pic}^0(F/k)$ of a one-variable function field and the $k$-points of a scheme representing the rigidified relative $\mathrm{Pic}^0$ functor of the corresponding smooth proper curve, with the normalisation that the class $[P]-[\varepsilon]$ goes to the point classifying $\mathcal{O}(P)\otimes\mathcal{O}(\varepsilon)^{-1}$. It differs from its sibling [`AlgebraicCurve.Pic0.exists_equiv_points_add_and_poincare_iso_ofPoint_of_representsRelSubPic_of_curveModel`](thm.html#AlgebraicCurve.Pic0.exists_equiv_points_add_and_poincare_iso_ofPoint_of_representsRelSubPic_of_curveModel) in that the representing object is not required to be smooth, proper or geometrically connected over $k$; it is used in the comparison of the Jacobian of $X_1(p)$ with the geometric special fibre of its Néron model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_equiv_points_add_and_poincare_iso_ofPoint_of_representsRelSubPic_of_curveModel_of_isAlgClosed.lean

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

theorem AlgebraicCurve.Pic0.exists_equiv_points_add_and_poincare_iso_ofPoint_of_representsRelSubPic_of_curveModel_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (D : RelativePic0Designation k c) (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
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
