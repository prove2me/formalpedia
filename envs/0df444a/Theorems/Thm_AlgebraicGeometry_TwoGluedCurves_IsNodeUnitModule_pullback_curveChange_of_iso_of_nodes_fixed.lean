-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_curveChange_of_iso_of_nodes_fixed
-- name    : AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.pullback_curveChange_of_iso_of_nodes_fixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/b9425523-4297-56fb-a0dd-f392d4d874b7
-- title:
--   Node-unit modules are preserved by node-fixing automorphisms
-- statement:
--   Let $\kappa$ be a field, let $x\colon X\to\operatorname{Spec}\kappa$ be a $\kappa$-scheme, and let $c_1\colon C_1\to\operatorname{Spec}\kappa$, $c_2\colon C_2\to\operatorname{Spec}\kappa$ be $\kappa$-schemes equipped with morphisms $i_1\colon C_1\to X$, $i_2\colon C_2\to X$ over $\operatorname{Spec}\kappa$ (i.e. $i_k$ followed by $x$ is $c_k$) which are closed immersions. Let $\iota$ be an index type and let $p_1(j)\colon\operatorname{Spec}\kappa\to C_1$, $p_2(j)\colon\operatorname{Spec}\kappa\to C_2$ be families of sections of $c_1$, $c_2$ (morphisms whose composites with $c_1$, resp. $c_2$, are the identity of $\operatorname{Spec}\kappa$). Assume given automorphisms $w_s$ of $X$, $\alpha_1$ of $C_1$ and $\alpha_2$ of $C_2$, each compatible with the structure morphisms to $\operatorname{Spec}\kappa$, such that $\alpha_k$ followed by $i_k$ equals $i_k$ followed by $w_s$ for $k=1,2$, and such that $\alpha_k$ fixes every section: $p_k(j)$ followed by $\alpha_k$ is $p_k(j)$ for all $j$. Finally let $h\colon T\to\operatorname{Spec}\kappa$ be a $\kappa$-scheme, $u\colon\iota\to\Gamma(T,\mathcal O_T)^\times$ a family of units, and $M$ a sheaf of modules on $X\times_{\kappa}T$ satisfying `IsNodeUnitModule` for these data: there are morphisms $j_1$, $j_2$ from $M$ to the pushforwards along the base-changed immersions $C_1\times_\kappa T\to X\times_\kappa T$, resp. $C_2\times_\kappa T\to X\times_\kappa T$, of the unit sheaves of modules, such that over every open $W$ of $X\times_\kappa T$ the map $m\mapsto (j_1(m),j_2(m))$ is injective with image exactly the pairs $(f,g)$ satisfying, for every $j\in\iota$, the node condition at $j$: the restriction of $f$ along the first node section equals $u_j$ times the restriction of $g$ along the second node section, on the node locus inside $W$. The conclusion is that the pullback of $M$ along `curveChange` applied to $w_s$ and $h$, that is along the base change $w_s\times\operatorname{id}_T$ of $w_s$ to $X\times_\kappa T$, again satisfies `IsNodeUnitModule` for the same $i_1,i_2$, $p_1,p_2$, $h$ and the same units $u$.
--
--   This is the invariance, under an automorphism of the ambient scheme which preserves each of the two components and fixes each of the marked node sections, of the description of line bundles on two curves glued at nodes by gluing data with prescribed units. It is used in the study of the relative Picard functor of two glued smooth curves, where it enters [`AlgebraicGeometry.RelPicard.RepresentsRelSubPic.postComp_transport_eq_self_of_ker_restrictPair_of_iso_comp_eq_of_crossing_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.RepresentsRelSubPic.postComp_transport_eq_self_of_ker_restrictPair_of_iso_comp_eq_of_crossing_of_twoGluedSmoothCurves).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_curveChange_of_iso_of_nodes_fixed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves

universe u v

theorem AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.pullback_curveChange_of_iso_of_nodes_fixed
    {κ : Type u} [Field κ]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ))
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    {ι : Type v} (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
    (ws : X ≅ X) (hws : ws.hom ≫ x = x)
    (α₁ : C₁ ≅ C₁) (hα₁ : α₁.hom ≫ c₁ = c₁) (hα₁i : α₁.hom ≫ i₁.1 = i₁.1 ≫ ws.hom)
    (α₂ : C₂ ≅ C₂) (hα₂ : α₂.hom ≫ c₂ = c₂) (hα₂i : α₂.hom ≫ i₂.1 = i₂.1 ≫ ws.hom)
    (hα₁p : ∀ j, (p₁ j).1 ≫ α₁.hom = (p₁ j).1) (hα₂p : ∀ j, (p₂ j).1 ≫ α₂.hom = (p₂ j).1)
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) (u : ι → Γ(T, ⊤)ˣ) (M : (pullback x h).Modules)
    (hM : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M) :
    IsNodeUnitModule x i₁ i₂ p₁ p₂ h u
      ((Scheme.Modules.pullback (curveChange (c := x) (c' := x) ws.hom hws h)).obj M) := by sorry
