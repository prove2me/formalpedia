-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_gluedPic0_mk_eq_zero_of_hom_admissible_eq_one_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.gluedPic0_mk_eq_zero_of_hom_admissible_eq_one_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/6643bd2e-36c0-5e2e-9a8c-ed6fec282c65
-- title:
--   Injectivity of the glued Pic⁰ dictionary for two components
-- statement:
--   Let $k$ be an algebraically closed field, $x : X \to \operatorname{Spec} k$ proper with $X$ reduced, and $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be morphisms $C_j \to X$ over $\operatorname{Spec} k$ that are closed immersions and jointly cover $X$ on points, with $C_1 \times_X C_2$ reduced, of cardinality $s > 0$, and with the two projections agreeing over $\operatorname{Spec} k$. Fix $k$-points $\varepsilon$ of $X$, $\varepsilon_1$ of $C_1$ with $\varepsilon_1$ followed by $i_1$ equal to $\varepsilon$, and $\varepsilon_2$ of $C_2$. Let $D, D_1, D_2$ be pointed $k$-schemes together with data $hD, hD_1, hD_2$ exhibiting each as representing the functor of line bundles on the relevant curve, rigidified along the chosen section, whose geometric fibres are algebraically equivalent to zero: a Poincaré rigidified bundle in the class, universal for it, trivial at the zero section. Let $\nu_1, \nu_2 : D \to D_j$ be morphisms over $\operatorname{Spec} k$, $\nu_1$ being the classifying map of the Poincaré bundle of $D$ pulled back along $i_1$, while $\nu_2$ is assumed instead to satisfy, for every $T$-point $a$ of $D$, an isomorphism between the pullback of $D_2$'s Poincaré bundle along $a$ followed by $\nu_2$ and the rigidification at $\varepsilon_2$ of the pullback of $(hD.\text{poincare})$ along $a$ by the base change of $i_2$; both $\nu_1$ and $\nu_2$ are assumed to respect the relative group laws on points. Let $F$ be a field extension of $k$ in which every nonzero element has a degree-zero divisor recording its orders at all places, with $L(0) = k$, and let $\mathrm{Mdl}_1, \mathrm{Mdl}_2$ be curve models of $F/k$ with isomorphisms $e_j : \mathrm{Mdl}_j.C \cong C_j$ compatible with the structure morphisms. Let $\Phi_j : \mathrm{Pic}^0(F/k) \to D_j(k)$ be bijections, additive for the relative group laws, and normalised: if a degree-zero divisor equals the place of a $k$-point $P$ of $C_j$ minus the place of $\varepsilon_j$, then the Poincaré bundle pulled back along its image is isomorphic to the dual of the ideal sheaf of the graph of $P$ tensored with the ideal sheaf of the graph of $\varepsilon_j$. Let $S$ be a finite set of pairs of places of $F$, equipped with a bijection $\mathrm{nd}$ onto the $k$-points of $C_1 \times_X C_2$ such that the two components of each $\sigma \in S$ are the places attached, via $\mathrm{Mdl}_1$ and $\mathrm{Mdl}_2$, to the two projections of $\mathrm{nd}\,\sigma$. Let $\varphi$ be a map from the group of admissible gluing data — triples consisting of two degree-zero divisors, vanishing respectively at the first and second coordinates of every element of $S$, and a family $S \to k^\times$ written additively — to $D(k)$, which is additive, sends every glued-principal datum (the two divisors being those of functions $g_1, g_2$ taking unit values $a_\sigma, b_\sigma$ at the corresponding places, with unit family $a_\sigma/b_\sigma$) to the identity, whose composites with $\nu_1$ and $\nu_2$ are $\Phi_1$ and $\Phi_2$ of the classes of the two divisor components, and which satisfies: for every family $w : S \to k^\times$, the Poincaré bundle of $D$ pulled back along $\varphi(0,0,w)$ is a node-unit module at the points $\mathrm{nd}\,\sigma$ for the units $w(\sigma)^{-1}$, i.e. it is cut out inside the pushforwards of the structure sheaves of $C_1$ and $C_2$ by the node-matching conditions with those scaling factors. Then for every admissible gluing datum $a$ with $\varphi(a)$ the identity of the relative group law on $D$, the class of $a$ in $\mathrm{GluedPic}^0(S)$, the quotient of the admissible data by the glued-principal ones, is zero.
--
--   This is the injectivity half of the Raynaud-style dictionary between glued divisor-and-unit data on two smooth components and $\mathrm{Pic}^0$ of the reduced curve obtained by crossing them, the situation of the special fibre of a semistable model of a modular curve, where the two components are glued at the supersingular points. It feeds the construction of the isomorphism $\mathrm{GluedPic}^0(S) \cong \mathrm{Pic}^0_{X/k}(k)$ in [`AlgebraicGeometry.RelPicard.exists_gluedPic0_equiv_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.exists_gluedPic0_equiv_of_twoGluedSmoothCurves), the vanishing being deduced from the identification of the kernel of the pair of restriction maps with the image of the node-unit homomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_gluedPic0_mk_eq_zero_of_hom_admissible_eq_one_of_twoGluedSmoothCurves.lean

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

theorem AlgebraicGeometry.RelPicard.gluedPic0_mk_eq_zero_of_hom_admissible_eq_one_of_twoGluedSmoothCurves
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
        (RelEffCartierDiv.ofPoint c₂ P.1 P.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₂ ε₂.1 ε₂.2).idealModule))

    (S : Finset (Place k F × Place k F))
    (nd : ↥S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁))
    (hS : ∀ σ : ↥S,
        (σ : Place k F × Place k F).1 = Mdl₁.pointEquivPlace ⟨((nd σ).1 ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv,
            by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc, Category.assoc]; exact (nd σ).2⟩ ∧
        (σ : Place k F × Place k F).2 = Mdl₂.pointEquivPlace ⟨((nd σ).1 ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv,
            by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc, Category.assoc, hc]; exact (nd σ).2⟩)

    (φ : ↥(GluingData.admissible S) → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase)
    (hφ_mul : ∀ a b, φ (a + b) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ (φ a) (φ b))
    (hφ_princ : ∀ a : ↥(GluingData.admissible S), GluingData.IsGluedPrincipal S (a : GluingData k F S) →
        φ a = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).one _)
    (hφ_res : ∀ a : ↥(GluingData.admissible S), postComp ν₁ (φ a) = Φ₁ (Pic0.mk ⟨(a : GluingData k F S).1, a.2.1⟩) ∧
        postComp ν₂ (φ a) = Φ₂ (Pic0.mk ⟨(a : GluingData k F S).2.1, a.2.2.1⟩))
    (hφ_node : ∀ w : ↥S → Additive kˣ,
        IsNodeUnitModule x i₁ i₂
          (fun σ => ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩)
          (fun σ => ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩)
          (𝟙 (Spec (CommRingCat.of k)))
          (fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (Additive.toMul (w σ))⁻¹)
          (hD.poincare.pullbackAlong (φ ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩)).L)

    (hν₁_mul : ∀ a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,
        postComp ν₁ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ a b) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).mul _ (postComp ν₁ a) (postComp ν₁ b))
    (hν₂_mul : ∀ a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,
        postComp ν₂ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _ a b) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).mul _ (postComp ν₂ a) (postComp ν₂ b))
    (a : ↥(GluingData.admissible S))
    (ha : φ a = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).one _) :
    GluedPic0.mk S a = 0 := by sorry
