-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue
-- name    : AlgebraicGeometry.RelPicard.isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/d5fee4ff-3b31-519d-a250-c064a1a0f595
-- title:
--   Principal divisor on one component gives a node-unit module
-- statement:
--   Let $k$ be an algebraically closed field and let $X$, $C$, $C'$ be $k$-schemes, given by structure morphisms $x : X \to \operatorname{Spec} k$ (separated, with $X$ reduced), $c : C \to \operatorname{Spec} k$ (proper, smooth of relative dimension $1$, geometrically integral) and $c' : C' \to \operatorname{Spec} k$. Let $i$ and $i'$ be morphisms $C \to X$ and $C' \to X$ over $\operatorname{Spec} k$ (i.e. pairs consisting of a morphism and a proof that composing with $x$ gives $c$, resp. $c'$) which are closed immersions, such that every point of $X$ lies in the image of $i$ or of $i'$ and such that the fibre product $C \times_X C'$ is reduced. Let $\iota$ be a finite type and let $p_j$, $p'_j$ be $k$-points of $C$, resp. $C'$ (morphisms from $\operatorname{Spec} k$ composing to the identity), such that $j \mapsto p_j(\ast)$ is injective, $p_j$ followed by $i$ equals $p'_j$ followed by $i'$ for every $j$, and every pair of points $q \in C$, $q' \in C'$ with the same image in $X$ arises as $(p_j(\ast), p'_j(\ast))$ for some $j$. Let $F$ be a field extension of $k$ satisfying `HasPrincipalDivisors k F` (every nonzero element has a degree-zero divisor recording its orders at all places) and `ConstantsAreBase k F` (the Riemann–Roch space of the zero divisor is the image of $k$). Let `Mdl` be a `CurveModel` for $k, F$ together with an isomorphism $e : \mathrm{Mdl}.C \cong C$ over $\operatorname{Spec} k$; let $pt$ assign to each place $v$ of $F/k$ a $k$-point of $C$, namely the image under $e$ of the point corresponding to $v$ under the model's bijection between $k$-points and places, and let $plc : \iota \to \operatorname{Place} k\,F$ send $j$ to the place corresponding to $p_j$ transported through $e^{-1}$. Finally let $D$ be a finitely supported $\mathbb{Z}$-valued function on places, $g \in F$ nonzero, and $va_j \in k^\times$, such that $D(v) = \operatorname{ord}_v g$ for every $v$, $D(plc_j) = 0$ for every $j$, and $g$ lies in the valuation subring of $plc_j$ with residue the image of $va_j$ (the predicate `HasValue`). The conclusion is `IsNodeUnitModule` for $x$, $i$, $i'$, $(p_j)$, $(p'_j)$ over the identity of $\operatorname{Spec} k$, with gluing units the images of the $va_j$ in $\Gamma(\operatorname{Spec} k, \mathcal{O})^\times$ under the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism, and with module the iterated tensor product obtained by folding over a list enumerating the support of $D$: for each such place $v$ one tensors the dual of $I_v^{\,D(v)^+}$ and $I_v^{\,(-D(v))^+}$, where $I_v$ is the ideal of the relative effective Cartier divisor `RelEffCartierDiv.ofPoint` attached to the $k$-point $pt(v)$ of $X$ (i.e. $pt(v)$ followed by $i$) and the exponents are the positive and negative parts of $D(v)$, starting from the tensor unit of the modules over $X \times_{\operatorname{Spec} k} \operatorname{Spec} k$. Thus this module admits maps to the pushforwards of the structure sheaves of the two components which, over every open subset, identify its sections injectively with the pairs of sections satisfying the node condition with unit $va_j$ at each crossing $j$.
--
--   This is the classical description of the line bundle attached to a divisor that is principal on one component of a two-component nodal curve and trivial near the crossings: such a bundle is the node-unit bundle determined by the values of the function at the nodes, i.e. the image of these values under the boundary map from units at the nodes to the Picard group. It feeds the companion statement [`AlgebraicGeometry.RelPicard.isNodeUnitModule_foldr_ofPoint_tensor_foldr_ofPoint_of_forall_eq_ord_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.isNodeUnitModule_foldr_ofPoint_tensor_foldr_ofPoint_of_forall_eq_ord_of_twoGluedSmoothCurves), where divisors on both components are treated simultaneously, in the analysis of Picard groups of glued curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue.lean

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

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.TwoGluedCurves AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C C' : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsSeparated x] (hXred : IsReduced X)
    (c : C ⟶ Spec (CommRingCat.of k)) (c' : C' ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (i : SchemeHomOver c x) (i' : SchemeHomOver c' x) [IsClosedImmersion i.1] [IsClosedImmersion i'.1]
    (hjs : ∀ z : X, z ∈ Set.range i.1.base ∨ z ∈ Set.range i'.1.base)
    (hcr : IsReduced (pullback i.1 i'.1))
    {ι : Type v} [Finite ι]
    (p : ι → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (p' : ι → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c')
    (hinj : Function.Injective fun j => (p j).1.base (IsLocalRing.closedPoint k))
    (hnode : ∀ j, (p j).1 ≫ i.1 = (p' j).1 ≫ i'.1)
    (hinter : ∀ (q : C) (q' : C'), i.1.base q = i'.1.base q' →
      ∃ j, q = (p j).1.base (IsLocalRing.closedPoint k) ∧ q' = (p' j).1.base (IsLocalRing.closedPoint k))

    (F : Type u) [Field F] [Algebra k F] [HasPrincipalDivisors k F] (hCB : ConstantsAreBase k F)
    (Mdl : CurveModel k F) (e : Mdl.C ≅ C) (he : e.hom ≫ c = Mdl.toBase)
    (pt : Place k F → (Spec (CommRingCat.of k) ⟶ C)) (hpt : ∀ v, pt v ≫ c = 𝟙 _)
    (hpt' : ∀ v, pt v = (Mdl.pointEquivPlace.symm v).1 ≫ e.hom)
    (plc : ι → Place k F)
    (hplc : ∀ j, plc j = Mdl.pointEquivPlace ⟨(p j).1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact (p j).2⟩)

    (D : Place k F →₀ ℤ) (g : F) (va : ι → kˣ) (hg : g ≠ 0)
    (ha : ∀ v : Place k F, D v = v.ord g) (hD : ∀ j, D (plc j) = 0)
    (hv : ∀ j, (plc j).HasValue g (va j)) :
    IsNodeUnitModule x i i' p p' (𝟙 (Spec (CommRingCat.of k)))
      (fun j => Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom (va j))
      (((D.support.toList).foldr
          (fun v M => ((RelEffCartierDiv.ofPoint x (pt v ≫ i.1) (by rw [Category.assoc, i.2]; exact hpt v)).I ^ (D v).toNat).invModule ⊗
            ((RelEffCartierDiv.ofPoint x (pt v ≫ i.1) (by rw [Category.assoc, i.2]; exact hpt v)).I ^ (-(D v)).toNat).module ⊗ M)
          (𝟙_ (pullback x (𝟙 (Spec (CommRingCat.of k)))).Modules))) := by sorry
