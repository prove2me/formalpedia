-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_tensor_foldr_ofPoint_of_forall_eq_ord_of_twoGluedSmoothCurves
-- name    : AlgebraicGeometry.RelPicard.isNodeUnitModule_foldr_ofPoint_tensor_foldr_ofPoint_of_forall_eq_ord_of_twoGluedSmoothCurves
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/0df0f678-9f38-535a-99ef-0532fcfba02c
-- title:
--   Principal glued data give node-unit modules on two glued curves
-- statement:
--   Let $k$ be an algebraically closed field, $x : X \to \operatorname{Spec} k$ a proper morphism with $X$ reduced, and $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ proper, smooth of relative dimension $1$ and geometrically integral. Let $i_1, i_2$ be closed immersions $C_j \to X$ with $i_j$ followed by $x$ equal to $c_j$, such that every point of $X$ lies in the image of $i_1$ or of $i_2$, with $C_1 \times_X C_2$ reduced, $\operatorname{Nat.card}(C_1\times_X C_2) = s > 0$, and $\mathrm{pr}_2$ followed by $c_2$ equal to $\mathrm{pr}_1$ followed by $c_1$. Let $F$ be a field extension of $k$ satisfying `HasPrincipalDivisors k F` (every nonzero $f$ has a degree-zero divisor with multiplicities $v.\mathrm{ord}\,f$) and $\mathrm{ConstantsAreBase}\;k\;F$, i.e. $L(0) = k \subseteq F$. Let $\mathrm{Mdl}_1, \mathrm{Mdl}_2$ be `CurveModel`s for $F/k$ with isomorphisms $e_j : \mathrm{Mdl}_j.C \cong C_j$ over $\operatorname{Spec} k$, and let $\mathrm{pt}_j : \mathrm{Place}\;k\;F \to (\operatorname{Spec} k \to C_j)$ be sections of $c_j$ given by transporting $\mathrm{Mdl}_j.\mathrm{pointEquivPlace}^{-1}$ along $e_j$. Let $S$ be a finite set of pairs of places together with a bijection $\mathrm{nd}$ from $S$ to the $k$-points of $C_1\times_X C_2$ (morphisms $\operatorname{Spec} k \to C_1\times_X C_2$ over $\operatorname{Spec} k$), such that the two components of $\sigma \in S$ are the places of the images of $\mathrm{nd}\,\sigma$ in $C_1$ and in $C_2$, read through $e_1^{-1}, e_2^{-1}$ and $\mathrm{pointEquivPlace}$. Let $a = (D_1, D_2, w)$ lie in $\mathrm{GluingData.admissible}\;S$, so $D_1, D_2$ have degree zero and $D_1(\sigma_1) = D_2(\sigma_2) = 0$ for all $\sigma \in S$. Assume $g_1, g_2 \in F$ are nonzero with $D_1(v) = v.\mathrm{ord}\,g_1$ and $D_2(v) = v.\mathrm{ord}\,g_2$ for every place $v$, and that $v_a(\sigma), v_b(\sigma) \in k^\times$ are the residues of $g_1$ at $\sigma_1$ and of $g_2$ at $\sigma_2$ (`HasValue`). The conclusion is $\mathrm{IsNodeUnitModule}$ for $x, i_1, i_2$, the two families of nodes $\mathrm{nd}\,\sigma$ followed by $\mathrm{pr}_1$ resp. $\mathrm{pr}_2$, base $\mathrm{id}_{\operatorname{Spec} k}$, units $v_a(\sigma)/v_b(\sigma)$ transported to $\Gamma(\operatorname{Spec} k, \top)^\times$ along the inverse of `Scheme.ΓSpecIso`, and the module
--   $$\bigotimes_{v \in \operatorname{supp} D_1} \big(I_{1,v}^{D_1(v)^+}\big)^{\vee} \otimes I_{1,v}^{D_1(v)^-} \;\otimes\; \bigotimes_{v \in \operatorname{supp} D_2} \big(I_{2,v}^{D_2(v)^+}\big)^{\vee} \otimes I_{2,v}^{D_2(v)^-},$$
--   formed as right folds over the support lists starting from the unit object of the modules on $X \times_{\operatorname{Spec} k} \operatorname{Spec} k$, where $I_{j,v}$ is the ideal of the relative effective Cartier divisor `RelEffCartierDiv.ofPoint` attached to the section $\mathrm{pt}_j(v)$ followed by $i_j$ of $x$. That is, this module admits maps $j_1, j_2$ to the pushforwards of the structure sheaves of the two base-changed components under which, on every open $W$, sections inject into pairs and their image consists exactly of the pairs satisfying `NodeCondition` at every node with the prescribed units.
--
--   This is the computational heart of Raynaud's dictionary between gluing data on a curve with two smooth components meeting transversally and line bundles on the glued curve: a gluing datum whose two divisors are principal, given by $g_1$ on $C_1$ and $g_2$ on $C_2$, is realised by an explicit tensor product of (duals of) powers of the ideal sheaves of the relevant points, the gluing units at the nodes being the ratios of the residues of $g_1$ and $g_2$ there. It is used by [`AlgebraicGeometry.RelPicard.exists_gluedTwist_admissible_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.exists_gluedTwist_admissible_of_twoGluedSmoothCurves).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_tensor_foldr_ofPoint_of_forall_eq_ord_of_twoGluedSmoothCurves.lean

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

theorem AlgebraicGeometry.RelPicard.isNodeUnitModule_foldr_ofPoint_tensor_foldr_ofPoint_of_forall_eq_ord_of_twoGluedSmoothCurves
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
            by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc, Category.assoc, hc]; exact (nd σ).2⟩)
    (a : ↥(GluingData.admissible S)) (g₁ g₂ : F) (va vb : ↥S → kˣ) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (ha₁ : ∀ v : Place k F, (a : GluingData k F S).1 v = v.ord g₁) (ha₂ : ∀ v : Place k F, (a : GluingData k F S).2.1 v = v.ord g₂)
    (hv : ∀ σ : ↥S, (σ : Place k F × Place k F).1.HasValue g₁ (va σ) ∧ (σ : Place k F × Place k F).2.HasValue g₂ (vb σ)) :
    IsNodeUnitModule x i₁ i₂
      (fun σ => ⟨(nd σ).1 ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact (nd σ).2⟩)
      (fun σ => ⟨(nd σ).1 ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hc]; exact (nd σ).2⟩)
      (𝟙 (Spec (CommRingCat.of k)))
      (fun σ => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (va σ / vb σ))
      (((((a : GluingData k F S).1).support.toList).foldr
          (fun v M => ((RelEffCartierDiv.ofPoint x (pt₁ v ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact hpt₁ v)).I ^ (((a : GluingData k F S).1) v).toNat).invModule ⊗
            ((RelEffCartierDiv.ofPoint x (pt₁ v ≫ i₁.1) (by rw [Category.assoc, i₁.2]; exact hpt₁ v)).I ^ (-(((a : GluingData k F S).1) v)).toNat).module ⊗ M)
          (𝟙_ (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules)) ⊗
        ((((a : GluingData k F S).2.1).support.toList).foldr
          (fun v M => ((RelEffCartierDiv.ofPoint x (pt₂ v ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact hpt₂ v)).I ^ (((a : GluingData k F S).2.1) v).toNat).invModule ⊗
            ((RelEffCartierDiv.ofPoint x (pt₂ v ≫ i₂.1) (by rw [Category.assoc, i₂.2]; exact hpt₂ v)).I ^ (-(((a : GluingData k F S).2.1) v)).toNat).module ⊗ M)
          (𝟙_ (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules))) := by sorry
