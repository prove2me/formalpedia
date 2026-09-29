-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.exists_gluedTwist_admissible_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/bb44218a-03c1-5afd-96b0-a3986c5a4025
-- title:
--   Bundles of admissible gluing data on two glued smooth curves
-- statement:
--   Let $k$ be an algebraically closed field, $x : X \to \operatorname{Spec} k$ proper with $X$ reduced, and $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be closed immersions $C_j \to X$ over $\operatorname{Spec} k$ (i.e. $i_j$ followed by $x$ is $c_j$) such that every point of $X$ lies in the image of $i_1$ or of $i_2$, with $C_1 \times_X C_2$ reduced, of positive finite cardinality $s$, and with the two induced maps $C_1\times_X C_2 \to \operatorname{Spec} k$ equal (`hc`). Let $F/k$ be a field extension in which every nonzero $g$ has a degree-zero divisor with multiplicities $v.\mathrm{ord}\,g$, and with $L(0)$ the image of $k$ in $F$; let $\mathrm{Mdl}_1,\mathrm{Mdl}_2$ be curve models of $F/k$ together with isomorphisms $e_j : \mathrm{Mdl}_j.C \cong C_j$ over $\operatorname{Spec} k$. For each place $v$ of $F/k$ let $\mathrm{pt}_j(v)$ be the $k$-point of $C_j$ corresponding to $v$ under $\mathrm{Mdl}_j.\mathrm{pointEquivPlace}$ and $e_j$. Let $S$ be a finite set of ordered pairs of places and $\mathrm{nd}$ a bijection from $S$ to the $k$-points of $C_1\times_X C_2$ such that, for each $\sigma\in S$, the two components of $\sigma$ are the places of the two branches through the crossing $\mathrm{nd}(\sigma)$ (`hS`). Then there is an assignment $a \mapsto E(a)$ of a module on $X \times_{\operatorname{Spec} k} \operatorname{Spec} k$ to each admissible gluing datum $a = (D_1, D_2, w) \in \operatorname{Div}(F)\times\operatorname{Div}(F)\times(S\to \mathrm{Additive}\,k^\times)$, admissibility meaning $\deg D_1 = \deg D_2 = 0$ and $D_1(\sigma_1) = D_2(\sigma_2) = 0$ for all $\sigma \in S$, such that: each $E(a)$ is invertible (locally isomorphic to the unit); $E(a+b) \cong E(a)\otimes E(b)$; $E(a)$ is isomorphic to the unit whenever $D_1 = D_2 = 0$; the pullback of $E(a)$ along the map $\mathrm{curveChange}$ induced by $i_j$ is isomorphic to the iterated tensor product, over the finite support of $D_j$ (folded along its list of elements), of $(I_{\mathrm{pt}_j(v)}^{\,(D_j v)_+})^{\vee}$ with $I_{\mathrm{pt}_j(v)}^{\,(-D_j v)_+}$, where $I_{\mathrm{pt}_j(v)}$ is the ideal sheaf of the relative effective Cartier divisor `RelEffCartierDiv.ofPoint` cut out by $\mathrm{pt}_j(v)$, for $j = 1, 2$; if $g_1, g_2 \in F$ are nonzero with $D_1 v = v.\mathrm{ord}\,g_1$ and $D_2 v = v.\mathrm{ord}\,g_2$ for all $v$, and $va, vb : S \to k^\times$ are such that $g_1$ has value $va(\sigma)$ at $\sigma_1$ and $g_2$ has value $vb(\sigma)$ at $\sigma_2$, then $E(a)$ satisfies `IsNodeUnitModule` for the crossing points $\mathrm{nd}(\sigma)$ projected to $C_1$ and $C_2$ and the units $va(\sigma)/vb(\sigma)$ transported to global units on $\operatorname{Spec} k$; and, for $k$-points $P, Q$ of $C_1$ whose images in $X$ avoid the image of $i_2$ and for admissible $a$ with $D_1$ the difference of the places of $P$ and $Q$ and $D_2 = 0$, $E(a)$ is isomorphic to the dual of the ideal sheaf module of the relative divisor at $P$ followed by $i_1$, tensored with the ideal sheaf module of the relative divisor at $Q$ followed by $i_1$, and symmetrically with the roles of $C_1$ and $C_2$ exchanged.
--
--   This is the divisor half of Raynaud's description of the Picard group of a curve with two smooth components crossing transversally: $E(a)$ plays the role of $\mathcal{O}_X(i_1D_1 + i_2D_2)$, admissibility of $a$ ensuring that the divisor is supported away from the crossings. It is used by [`AlgebraicGeometry.RelPicard.exists_hom_admissible_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.exists_hom_admissible_of_twoGluedSmoothCurves), where these bundles are combined with node-unit bundles built from the unit component $w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_gluedTwist_admissible_of_twoGluedSmoothCurves.lean

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

theorem AlgebraicGeometry.RelPicard.exists_gluedTwist_admissible_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)

    (hc : pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.fst i₁.1 i₂.1 ≫ c₁)
    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F] (hCB : ConstantsAreBase k F)
    (Mdl₁ : CurveModel k F) (e₁ : Mdl₁.C ≅ C₁) (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : CurveModel k F) (e₂ : Mdl₂.C ≅ C₂) (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (pt₁ : Place k F → (Spec (CommRingCat.of k) ⟶ C₁)) (hpt₁ : ∀ v, pt₁ v ≫ c₁ = 𝟙 _)
    (hpt₁' : ∀ v, pt₁ v = (Mdl₁.pointEquivPlace.symm v).1 ≫ e₁.hom)
    (pt₂ : Place k F → (Spec (CommRingCat.of k) ⟶ C₂)) (hpt₂ : ∀ v, pt₂ v ≫ c₂ = 𝟙 _)
    (hpt₂' : ∀ v, pt₂ v = (Mdl₂.pointEquivPlace.symm v).1 ≫ e₂.hom)
    (S : Finset (Place k F × Place k F))
    (nd : ↥S ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.fst i₁.1 i₂.1 ≫ c₁))
    (hS : ∀ σ : ↥S,
        (σ : Place k F × Place k F).1 = Mdl₁.pointEquivPlace ⟨((nd σ).1 ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv,
            by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc, Category.assoc]; exact (nd σ).2⟩ ∧
        (σ : Place k F × Place k F).2 = Mdl₂.pointEquivPlace ⟨((nd σ).1 ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv,
            by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc, Category.assoc, hc]; exact (nd σ).2⟩) :
    ∃ E : ↥(GluingData.admissible S) → (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules,

      (∀ a, Scheme.Modules.IsInvertible (E a)) ∧

      (∀ a b, Nonempty (E (a + b) ≅ E a ⊗ E b)) ∧

      (∀ a : ↥(GluingData.admissible S), (a : GluingData k F S).1 = 0 → (a : GluingData k F S).2.1 = 0 →
        Nonempty (E a ≅ 𝟙_ (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules)) ∧

      (∀ a : ↥(GluingData.admissible S),
        Nonempty ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 (𝟙 (Spec (CommRingCat.of k))))).obj (E a) ≅
          ((((a : GluingData k F S).1).support.toList).foldr
            (fun v M => ((RelEffCartierDiv.ofPoint c₁ (pt₁ v) (hpt₁ v)).I ^ (((a : GluingData k F S).1) v).toNat).invModule ⊗
              ((RelEffCartierDiv.ofPoint c₁ (pt₁ v) (hpt₁ v)).I ^ (-(((a : GluingData k F S).1) v)).toNat).module ⊗ M)
            (𝟙_ (pullback c₁ (𝟙 (Spec (CommRingCat.of k)))).Modules))) ∧
        Nonempty ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 (𝟙 (Spec (CommRingCat.of k))))).obj (E a) ≅
          ((((a : GluingData k F S).2.1).support.toList).foldr
            (fun v M => ((RelEffCartierDiv.ofPoint c₂ (pt₂ v) (hpt₂ v)).I ^ (((a : GluingData k F S).2.1) v).toNat).invModule ⊗
              ((RelEffCartierDiv.ofPoint c₂ (pt₂ v) (hpt₂ v)).I ^ (-(((a : GluingData k F S).2.1) v)).toNat).module ⊗ M)
            (𝟙_ (pullback c₂ (𝟙 (Spec (CommRingCat.of k)))).Modules)))) ∧

      (∀ (a : ↥(GluingData.admissible S)) (g₁ g₂ : F) (va vb : ↥S → kˣ), g₁ ≠ 0 → g₂ ≠ 0 →
        (∀ v : Place k F, (a : GluingData k F S).1 v = v.ord g₁) → (∀ v : Place k F, (a : GluingData k F S).2.1 v = v.ord g₂) →
        (∀ σ : ↥S, (σ : Place k F × Place k F).1.HasValue g₁ (va σ) ∧ (σ : Place k F × Place k F).2.HasValue g₂ (vb σ)) →
        IsNodeUnitModule x i₁ i₂
          (fun σ => ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩)
          (fun σ => ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩)
          (𝟙 (Spec (CommRingCat.of k)))
          (fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (va σ / vb σ))
          (E a)) ∧

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁)
        (_ : (P.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
        (_ : (Q.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base)
        (a : ↥(GluingData.admissible S))
        (_ : (a : GluingData k F S).1 = Finsupp.single (Mdl₁.pointEquivPlace ⟨P.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact P.2⟩) 1 - Finsupp.single (Mdl₁.pointEquivPlace ⟨Q.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact Q.2⟩) 1)
        (_ : (a : GluingData k F S).2.1 = 0),
        Nonempty (E a ≅
          (RelEffCartierDiv.ofPoint x (P.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact P.2)).lineBundle ⊗
            (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact Q.2)).idealModule)) ∧

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
        (_ : (P.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base)
        (_ : (Q.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base)
        (a : ↥(GluingData.admissible S))
        (_ : (a : GluingData k F S).1 = 0)
        (_ : (a : GluingData k F S).2.1 = Finsupp.single (Mdl₂.pointEquivPlace ⟨P.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact P.2⟩) 1 - Finsupp.single (Mdl₂.pointEquivPlace ⟨Q.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact Q.2⟩) 1),
        Nonempty (E a ≅
          (RelEffCartierDiv.ofPoint x (P.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact P.2)).lineBundle ⊗
            (RelEffCartierDiv.ofPoint x (Q.1 ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact Q.2)).idealModule)) := by sorry
