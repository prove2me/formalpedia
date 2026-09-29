-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_gluedPic0_equiv_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.exists_gluedPic0_equiv_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/1f964aab-aeed-5d2b-a4b3-7b60229326eb
-- title:
--   Raynaud's dictionary for Pic⁰ of a two-component curve
-- statement:
--   Let $k$ be an algebraically closed field, $x : X \to \operatorname{Spec} k$ a proper morphism with $X$ reduced, and $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be closed immersions $C_1 \to X$, $C_2 \to X$ over $\operatorname{Spec} k$ whose images cover $X$ set-theoretically, with $\operatorname{pullback} i_1\, i_2$ reduced, with underlying set of cardinality $s > 0$, and with the two projections agreeing over $\operatorname{Spec} k$ (hypothesis `hc`). Fix sections $\varepsilon$ of $x$, $\varepsilon_1$ of $c_1$ with $\varepsilon_1$ followed by $i_1$ equal to $\varepsilon$, and $\varepsilon_2$ of $c_2$. Let $D, D_1, D_2$ be pointed $k$-schemes together with data $hD, hD_1, hD_2$ exhibiting each as representing, with its Poincaré rigidified line bundle, the functor of rigidified line bundles satisfying `algEquivZeroCut` (fibrewise algebraic equivalence to zero) for $(x,\varepsilon)$, $(c_1,\varepsilon_1)$, $(c_2,\varepsilon_2)$. Let $\nu_1, \nu_2 : D \to D_1, D_2$ over $\operatorname{Spec} k$, with $\nu_1$ the classifying map `RepresentsRelSubPic.pullbackHom` for pullback along $i_1$, and $\nu_2$ characterised by: for every $t : T \to \operatorname{Spec} k$ and every $a : T \to D$ over $\operatorname{Spec} k$, the $D_2$-Poincaré bundle pulled back along $a$ followed by $\nu_2$ is isomorphic to the rigidification at $\varepsilon_2$ of the pullback, along `curveChange` for $i_2$, of the $D$-Poincaré bundle pulled back along $a$. Let $F$ be a field extension of $k$ with `HasPrincipalDivisors` (every nonzero $f \in F$ has a degree-zero divisor recording its orders at all places) and `ConstantsAreBase` (the Riemann–Roch space of $0$ is the image of $k$), and let $\mathrm{Mdl}_1, \mathrm{Mdl}_2$ be curve models of $F/k$ with isomorphisms $e_1 : \mathrm{Mdl}_1.C \cong C_1$, $e_2 : \mathrm{Mdl}_2.C \cong C_2$ compatible with the structure morphisms. Finally let $\Phi_1 : \mathrm{Pic}^0(F/k) \simeq D_1(k)$ and $\Phi_2 : \mathrm{Pic}^0(F/k) \simeq D_2(k)$ be bijections onto the sets of sections of $D_1,D_2$ over $\operatorname{Spec} k$ that are additive for the relative group laws coming from `algEquivZeroGroupCut`, and pinned by: for a $k$-point $P$ of $C_j$ and a degree-zero divisor $Dv$ equal to the place of $P$ minus the place of $\varepsilon_j$ (places computed through $e_j^{-1}$ and $\mathrm{Mdl}_j.pointEquivPlace$), the Poincaré bundle pulled back along $\Phi_j(\mathrm{Pic}^0$-class of $Dv)$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $P$ tensored with the ideal module of that of $\varepsilon_j$. Then there exist a finite set $S$ of pairs of places of $F/k$, a bijection $nd$ from $S$ to the $k$-points of $\operatorname{pullback} i_1\, i_2$ over $\operatorname{Spec} k$, and a bijection $\Phi : \mathrm{GluedPic0}(k,F,S) \simeq D(k)$ — where a gluing datum is a pair of divisors together with a map $S \to$ the additive copy of $k^\times$, admissible when both divisors have degree zero and vanish at the first, resp. second, places of each element of $S$, and $\mathrm{GluedPic0}$ is the quotient of the admissible data by the glued-principal subgroup — such that: each $\sigma \in S$ has as coordinates the places of the images of $nd\,\sigma$ under the first projection and $e_1^{-1}$, resp. the second projection and $e_2^{-1}$; $|S| = s$; $\Phi$ is additive for the relative group law attached to $hD$; post-composition with $\nu_1$, resp. $\nu_2$, carries $\Phi(a)$ to $\Phi_1$, resp. $\Phi_2$, of the two components of $\mathrm{toPic0Pair}(a)$; for every $w : S \to$ the additive copy of $k^\times$, the Poincaré bundle pulled back along $\Phi(\mathrm{nodeUnit}\,w)$ satisfies `IsNodeUnitModule` for the node points obtained from $nd$ by the two projections and for the units $w(\sigma)^{-1}$ transported into the units of the global sections of $\operatorname{Spec} k$; and, for $k$-points $P, Q$ of $C_1$ whose images in $X$ avoid the image of $i_2$ and an admissible datum $a$ whose first divisor is the place of $P$ minus the place of $Q$ and whose remaining two components vanish, the Poincaré bundle pulled back along $\Phi(\mathrm{mk}\,a)$ is isomorphic to the line bundle of the relative effective Cartier divisor on $X$ of the point $P$ followed by $i_1$, tensored with the ideal module of that of $Q$ followed by $i_1$; and symmetrically with the roles of $C_1$ and $C_2$ exchanged.
--
--   This is Raynaud's description of the identity component of the Picard functor of a proper reduced curve that is the union of two smooth proper geometrically integral curves meeting in $s$ points: the glued degree-zero divisor class group, an extension of $\mathrm{Pic}^0(C_1) \times \mathrm{Pic}^0(C_2)$ by the torus of node units, together with the restriction maps, the node-unit description and the Abel–Jacobi normalisations on each component. It is the common input to the special-fibre dictionaries for the models of the modular curves $X_H$ and $X_1$ used later, namely [`ModularCurve.XHDRModelAtP.exists_ptsSp_gluedPic0_dictionary_specialFibre`](thm.html#ModularCurve.XHDRModelAtP.exists_ptsSp_gluedPic0_dictionary_specialFibre) and [`ModularCurve.XOneP.exists_gluedPic0_addEquiv_neronSpecialFibreGeom_toPic0Pair_eq_proj_of_curveModel_igusa_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_gluedPic0_addEquiv_neronSpecialFibreGeom_toPic0Pair_eq_proj_of_curveModel_igusa_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_gluedPic0_equiv_of_twoGluedSmoothCurves.lean

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

theorem AlgebraicGeometry.RelPicard.exists_gluedPic0_equiv_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)

    (hc : pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.fst i₁.1 i₂.1 ≫ c₁)
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

    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F] (hCB : ConstantsAreBase k F)
    (Mdl₁ : CurveModel k F) (e₁ : Mdl₁.C ≅ C₁) (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : CurveModel k F) (e₂ : Mdl₂.C ≅ C₂) (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (Φ₁ : Pic0 k F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (hΦ₁_add : ∀ a b, Φ₁ (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).mul _ (Φ₁ a) (Φ₁ b))
    (hΦ₁ : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (Dv : Divisor.degZero (K := k) (F := F)),
      (Dv : Divisor k F) =
        Finsupp.single (Mdl₁.pointEquivPlace ⟨P.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact P.2⟩) 1 -
          Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 →
      Nonempty ((hD₁.poincare.pullbackAlong (Φ₁ (Pic0.mk Dv))).L ≅
        (RelEffCartierDiv.ofPoint c₁ P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule))
    (Φ₂ : Pic0 k F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hΦ₂_add : ∀ a b, Φ₂ (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).mul _ (Φ₂ a) (Φ₂ b))
    (hΦ₂ : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂) (Dv : Divisor.degZero (K := k) (F := F)),
      (Dv : Divisor k F) =
        Finsupp.single (Mdl₂.pointEquivPlace ⟨P.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact P.2⟩) 1 -
          Finsupp.single (Mdl₂.pointEquivPlace ⟨ε₂.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact ε₂.2⟩) 1 →
      Nonempty ((hD₂.poincare.pullbackAlong (Φ₂ (Pic0.mk Dv))).L ≅
        (RelEffCartierDiv.ofPoint c₂ P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₂ ε₂.1 ε₂.2).idealModule)) :
    ∃ (S : Finset (Place k F × Place k F))
      (nd : ↥S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁))
      (Φ : GluedPic0 k F S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase),

      (∀ σ : ↥S,
        (σ : Place k F × Place k F).1 = Mdl₁.pointEquivPlace ⟨((nd σ).1 ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv,
            by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc, Category.assoc]; exact (nd σ).2⟩ ∧
        (σ : Place k F × Place k F).2 = Mdl₂.pointEquivPlace ⟨((nd σ).1 ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv,
            by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc, Category.assoc, hc]; exact (nd σ).2⟩) ∧
      S.card = s ∧

      (∀ a b, Φ (a + b) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ (Φ a) (Φ b)) ∧

      (∀ a, postComp ν₁ (Φ a) = Φ₁ (GluedPic0.toPic0Pair S a).1 ∧ postComp ν₂ (Φ a) = Φ₂ (GluedPic0.toPic0Pair S a).2) ∧

      (∀ w : ↥S → Additive kˣ,
        IsNodeUnitModule x i₁ i₂
          (fun σ => ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩)
          (fun σ => ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩)
          (𝟙 (Spec (CommRingCat.of k)))
          (fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (Additive.toMul (w σ))⁻¹)
          (hD.poincare.pullbackAlong (Φ (GluedPic0.nodeUnit S w))).L) ∧

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁)
        (_ : (P.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
        (_ : (Q.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
        (a : ↥(GluingData.admissible S))
        (_ : (a : GluingData k F S).1 =
          Finsupp.single (Mdl₁.pointEquivPlace ⟨P.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact P.2⟩) 1 -
            Finsupp.single (Mdl₁.pointEquivPlace ⟨Q.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact Q.2⟩) 1)
        (_ : (a : GluingData k F S).2.1 = 0) (_ : (a : GluingData k F S).2.2 = 0),
        Nonempty ((hD.poincare.pullbackAlong (Φ (GluedPic0.mk S a))).L ≅
          (RelEffCartierDiv.ofPoint x (P.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact P.2)).lineBundle ⊗
            (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact Q.2)).idealModule)) ∧

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
        (_ : (P.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base)
        (_ : (Q.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base)
        (a : ↥(GluingData.admissible S))
        (_ : (a : GluingData k F S).1 = 0)
        (_ : (a : GluingData k F S).2.1 =
          Finsupp.single (Mdl₂.pointEquivPlace ⟨P.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact P.2⟩) 1 -
            Finsupp.single (Mdl₂.pointEquivPlace ⟨Q.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact Q.2⟩) 1)
        (_ : (a : GluingData k F S).2.2 = 0),
        Nonempty ((hD.poincare.pullbackAlong (Φ (GluedPic0.mk S a))).L ≅
          (RelEffCartierDiv.ofPoint x (P.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact P.2)).lineBundle ⊗
            (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact Q.2)).idealModule)) := by sorry
