-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_of_iso
-- name    : AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/b8dd5fc1-4810-587d-bf33-6ef7221f20c8
-- title:
--   Node-unit modules are stable under isomorphism
-- statement:
--   Let $\kappa$ be a field and let $X$, $C_1$, $C_2$ be schemes equipped with structure morphisms $x : X \to \operatorname{Spec}\kappa$, $c_1 : C_1 \to \operatorname{Spec}\kappa$, $c_2 : C_2 \to \operatorname{Spec}\kappa$; let $i_1$ and $i_2$ be morphisms $C_1 \to X$, $C_2 \to X$ together with the witnesses that composing them with $x$ gives $c_1$, resp. $c_2$, and let $p_1, p_2$ be families, indexed by a type $\iota$, of sections of $c_1$, resp. $c_2$, i.e. morphisms $\operatorname{Spec}\kappa \to C_k$ whose composite with $c_k$ is the identity. Let $T$ be a scheme with $h : T \to \operatorname{Spec}\kappa$, let $u : \iota \to \Gamma(T,\top)^\times$, and let $M$, $M'$ be sheaves of modules on the pullback $X \times_{\operatorname{Spec}\kappa} T$. Assume given an isomorphism $e : M \cong M'$ in that category of modules, and assume `IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M`: there are morphisms $j_1$ from $M$ to the pushforward along `curveChange i₁.1 i₁.2 h` of the unit module sheaf of $C_1 \times_{\operatorname{Spec}\kappa} T$, and $j_2$ likewise for $C_2$, such that for every open $W$ of $X \times_{\operatorname{Spec}\kappa} T$ the map $m \mapsto (j_1|_W(m), j_2|_W(m))$ on $\Gamma(M,W)$ is injective and its image is exactly the set of pairs $(f,g)$ satisfying, for every $j \in \iota$, the condition `NodeCondition`, namely that the restriction of $f$ along `nodeSectionFst p₁ h j` to `nodeLocus x i₁ i₂ p₁ p₂ h j W` equals the restriction of $g$ along `nodeSectionSnd p₂ h j` to the same locus, multiplied by the image of the unit $u_j$ under restriction from $\Gamma(T,\top)$. The conclusion is that $M'$ satisfies the same predicate, with the same units $u$.
--
--   This is the transport of the node-unit presentation of a module along an isomorphism: being a node-unit module with prescribed gluing units $u$ depends only on the isomorphism class of the module. It is used in the Néron-model analysis of the Jacobian of a curve with two components glued at the points $p_1(j)$, $p_2(j)$, when the predicate has to be moved along canonical identifications of modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_of_iso.lean

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

theorem AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.of_iso
    {κ : Type u} [Field κ]
    {X C₁ C₂ : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    {i₁ : SchemeHomOver c₁ x} {i₂ : SchemeHomOver c₂ x}
    {ι : Type v} {p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁} {p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂}
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u : ι → Γ(T, ⊤)ˣ} {M M' : (pullback x h).Modules}
    (e : M ≅ M') (hM : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M) :
    IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M' := by sorry
