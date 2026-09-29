-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_opens_iSup_eq_top_nodeLocus_eq_bot
-- name    : AlgebraicGeometry.TwoGluedCurves.exists_opens_iSup_eq_top_nodeLocus_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/3103c04b-a1e8-5e5b-8e02-a2f6849b0fe3
-- title:
--   One-node open cover for a base-changed glued curve
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $x \colon X \to \operatorname{Spec}\kappa$ be a $\kappa$-scheme with $X$ reduced, and let $c_1 \colon C_1 \to \operatorname{Spec}\kappa$, $c_2 \colon C_2 \to \operatorname{Spec}\kappa$ be $\kappa$-schemes. Let $i_1, i_2$ be morphisms $C_1 \to X$, $C_2 \to X$ over $\operatorname{Spec}\kappa$ (that is, pairs consisting of a morphism and a proof that composing with $x$ gives $c_1$, resp. $c_2$), both closed immersions, such that every point of $X$ lies in the image of $i_1$ or of $i_2$, and such that the pullback $C_1 \times_X C_2$ is reduced. Let $\iota$ be a finite index type and, for each $j \in \iota$, let $p_1 j \colon \operatorname{Spec}\kappa \to C_1$ and $p_2 j \colon \operatorname{Spec}\kappa \to C_2$ be sections of $c_1$, resp. $c_2$ (morphisms whose composite with $c_1$, resp. $c_2$, is the identity), assume $j \mapsto (p_1 j)(\ast)$ is injective, where $\ast$ denotes the closed point of $\operatorname{Spec}\kappa$, assume $p_1 j$ followed by $i_1$ equals $p_2 j$ followed by $i_2$ for every $j$, and assume that any pair of points $q_1 \in C_1$, $q_2 \in C_2$ with $i_1(q_1) = i_2(q_2)$ is of the form $q_1 = (p_1 j)(\ast)$, $q_2 = (p_2 j)(\ast)$ for some $j$. Finally let $h \colon T \to \operatorname{Spec}\kappa$ be an arbitrary $\kappa$-scheme. The assertion is that there are an open $U_0$ and a family of opens $U_i$, $i \in \iota$, of $X \times_\kappa T$ with: $U_0 \sqcup \bigsqcup_i U_i = \top$; $U_0 \le U_i$ for all $i$; for every $j$ and every open $W \le U_0$ the $j$-th node locus of $W$ is empty, where the $j$-th node locus of $W$ is the open of $T$ obtained by intersecting the preimage of the preimage of $W$ under the base change $C_1 \times_\kappa T \to X \times_\kappa T$ of $i_1$ along the section $T \to C_1 \times_\kappa T$ determined by $p_1 j$ with the corresponding open formed from $i_2$ and $p_2 j$; for all $i \ne j$ and every open $W \le U_i$ the $j$-th node locus of $W$ is empty; the $i$-th node locus of $U_i$ is all of $T$ for every $i$; and, for every family of units $u_j \in \Gamma(T,\mathcal O_T)^\times$, the node condition at $j$ — that the pullback of $f$ along the first node section agrees, after restriction to the $j$-th node locus, with $u_j$ times the pullback of $g$ along the second node section — holds for all sections $f$ over the preimage of $W$ in $C_1 \times_\kappa T$ and $g$ over the preimage of $W$ in $C_2 \times_\kappa T$, whenever either $W \le U_0$, or $W \le U_i$ with $j \ne i$.
--
--   This is the combinatorial covering statement underlying the local trivialisation of node-unit modules on a curve obtained by gluing $C_1$ and $C_2$ at finitely many $\kappa$-rational nodes: on $U_0$ no gluing condition survives and on $U_i$ only the one at the $i$-th node does, so that the gluing units can be dealt with one node at a time. It is used in the study of such bundles, for instance by [`AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.tensor`](thm.html#AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.tensor).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_exists_opens_iSup_eq_top_nodeLocus_eq_bot.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra AlgebraicGeometry.TwoGluedCurves

theorem AlgebraicGeometry.TwoGluedCurves.exists_opens_iSup_eq_top_nodeLocus_eq_bot
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
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) :
    ∃ (U₀ : (pullback x h).Opens) (U : ι → (pullback x h).Opens),
      U₀ ⊔ ⨆ i, U i = ⊤ ∧ (∀ i, U₀ ≤ U i) ∧
      (∀ (j : ι) (W : (pullback x h).Opens), W ≤ U₀ →
        nodeLocus x i₁ i₂ p₁ p₂ h j W = ⊥) ∧
      (∀ (i j : ι), j ≠ i → ∀ W : (pullback x h).Opens, W ≤ U i →
        nodeLocus x i₁ i₂ p₁ p₂ h j W = ⊥) ∧
      (∀ i : ι, nodeLocus x i₁ i₂ p₁ p₂ h i (U i) = ⊤) ∧
      (∀ (u : ι → Γ(T, ⊤)ˣ) (j : ι) (W : (pullback x h).Opens), W ≤ U₀ →
        ∀ f g, NodeCondition x i₁ i₂ p₁ p₂ h u W j f g) ∧
      (∀ (u : ι → Γ(T, ⊤)ˣ) (i j : ι), j ≠ i → ∀ W : (pullback x h).Opens, W ≤ U i →
        ∀ f g, NodeCondition x i₁ i₂ p₁ p₂ h u W j f g) := by sorry
