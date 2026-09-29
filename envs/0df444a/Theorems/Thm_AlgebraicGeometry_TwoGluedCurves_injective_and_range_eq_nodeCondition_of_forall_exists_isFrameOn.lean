-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn
-- name    : AlgebraicGeometry.TwoGluedCurves.injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/7568f0e6-033c-54e8-bc64-1d3cb4e60480
-- title:
--   Frame criterion for the node-unit description of sections
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $x : X \to \operatorname{Spec}\kappa$ with $X$ reduced, and let $c_1 : C_1 \to \operatorname{Spec}\kappa$, $c_2 : C_2 \to \operatorname{Spec}\kappa$ be $\kappa$-schemes. Let $i_1, i_2$ be morphisms $C_1 \to X$, $C_2 \to X$ over $\operatorname{Spec}\kappa$ (each given together with the identity $i_k$ followed by $x$ equals $c_k$) which are closed immersions, and assume every point of $X$ lies in the image of $i_1$ or of $i_2$. Let $\iota$ be a finite index type and $p_1(j) : \operatorname{Spec}\kappa \to C_1$, $p_2(j) : \operatorname{Spec}\kappa \to C_2$ sections of $c_1$, $c_2$ (morphisms whose composite with the structure morphism is the identity of $\operatorname{Spec}\kappa$), such that $j \mapsto p_1(j)(\text{closed point})$ is injective, $p_1(j)$ followed by $i_1$ equals $p_2(j)$ followed by $i_2$ for all $j$, and every pair $(q_1,q_2) \in C_1 \times C_2$ with $i_1(q_1) = i_2(q_2)$ is of the form $(p_1(j)(\text{closed point}), p_2(j)(\text{closed point}))$ for some $j$; assume moreover that the scheme $C_1 \times_X C_2$ is reduced. Let $h : T \to \operatorname{Spec}\kappa$, let $u : \iota \to \Gamma(T,\mathcal{O}_T)^\times$, let $N$ be a sheaf of modules on $X_T := X \times_\kappa T$, and let $J_1, J_2$ be morphisms from $N$ to the pushforwards along the base-changed maps $C_{1,T} \to X_T$, $C_{2,T} \to X_T$ (given by `curveChange`) of the structure sheaves of $C_{1,T}$, $C_{2,T}$ regarded as unit modules. The hypothesis is local existence of good frames: for every point $y$ of $X_T$ there are an open $W \ni y$, a section $e \in \Gamma(N,W)$ and sections $v_1 \in \Gamma(C_{1,T}, \text{preimage of } W)$, $v_2 \in \Gamma(C_{2,T}, \text{preimage of } W)$ such that $e$ is a frame on $W$, i.e. for every open $W' \le W$ the map $g \mapsto g \cdot (e|_{W'})$ from $\Gamma(X_T, W')$ to $\Gamma(N, W')$ is bijective, such that $J_1(e) = v_1$, $J_2(e) = v_2$, both $v_1$ and $v_2$ are units, and for each $j$ the pair $(v_1,v_2)$ satisfies the $j$-th node condition: on the node locus in $T$ (the intersection of the preimages of the two preimages of $W$ under the sections of $C_{1,T}$, $C_{2,T}$ determined by $p_1(j)$, $p_2(j)$), the pullback of $v_1$ along the first node section equals $u_j$ times the pullback of $v_2$ along the second. The conclusion is that for every open $W$ of $X_T$ the map $m \mapsto (J_1(m), J_2(m))$ on $\Gamma(N,W)$ is injective and its image is exactly the set of pairs $(f,g)$ satisfying the $j$-th node condition for every $j \in \iota$.
--
--   This is the frame criterion identifying a module on the base change $X_T$ of a scheme covered by two closed subschemes meeting in the prescribed rational nodes with the sheaf of pairs of functions on the two components agreeing, up to the units $u_j$, at the nodes — the module $\mathcal{M}_u$ attached to a gluing cocycle in the units–Picard sequence of a two-component curve. It serves as the common tool for the existence, multiplicativity in $u$ and exhaustion statements about these node-unit modules, being cited by [`AlgebraicGeometry.RelPicard.isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue`](thm.html#AlgebraicGeometry.RelPicard.isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue), [`AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.tensor`](thm.html#AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.tensor) and [`AlgebraicGeometry.TwoGluedCurves.exists_isNodeUnitModule_of_pullback_curveChange_iso_unit`](thm.html#AlgebraicGeometry.TwoGluedCurves.exists_isNodeUnitModule_of_pullback_curveChange_iso_unit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra AlgebraicGeometry.TwoGluedCurves

theorem AlgebraicGeometry.TwoGluedCurves.injective_and_range_eq_nodeCondition_of_forall_exists_isFrameOn
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X]
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    {ι : Type v} [Finite ι]
    (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
    (hinj : Function.Injective fun j => (p₁ j).1.base (IsLocalRing.closedPoint κ))
    (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1)
    (hinter : ∀ (q₁ : C₁) (q₂ : C₂), i₁.1.base q₁ = i₂.1.base q₂ →
      ∃ j, q₁ = (p₁ j).1.base (IsLocalRing.closedPoint κ) ∧ q₂ = (p₂ j).1.base (IsLocalRing.closedPoint κ))
    (hcr : IsReduced (pullback i₁.1 i₂.1))
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} (u : ι → Γ(T, ⊤)ˣ) {N : (pullback x h).Modules}
    (J₁ : N ⟶ (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj
      (SheafOfModules.unit (pullback c₁ h).ringCatSheaf))
    (J₂ : N ⟶ (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj
      (SheafOfModules.unit (pullback c₂ h).ringCatSheaf))
    (hloc : ∀ y : ↥(pullback x h), ∃ (W : (pullback x h).Opens) (e : Γ(N, W))
      (v₁ : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)) (v₂ : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)),
      y ∈ W ∧ Scheme.Modules.IsFrameOn e W ∧ J₁.app W e = v₁ ∧ J₂.app W e = v₂ ∧ IsUnit v₁ ∧ IsUnit v₂ ∧
      ∀ j, NodeCondition x i₁ i₂ p₁ p₂ h u W j v₁ v₂) :
    ∀ W : (pullback x h).Opens,
      Function.Injective (fun m : Γ(N, W) => (J₁.app W m, J₂.app W m)) ∧
      Set.range (fun m : Γ(N, W) => (J₁.app W m, J₂.app W m)) =
        {fg | ∀ j : ι, NodeCondition x i₁ i₂ p₁ p₂ h u W j fg.1 fg.2} := by sorry
