-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_iso
-- name    : AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.nonempty_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/944ecc85-9ec4-52e4-93eb-82b1f7520d51
-- title:
--   Uniqueness of node-unit modules with given gluing units
-- statement:
--   Let $\kappa$ be a field and let $x : X \to \operatorname{Spec}\kappa$, $c_1 : C_1 \to \operatorname{Spec}\kappa$, $c_2 : C_2 \to \operatorname{Spec}\kappa$ be schemes over $\kappa$, together with $\kappa$-morphisms $i_1 : C_1 \to X$ and $i_2 : C_2 \to X$ (elements of `SchemeHomOver`, i.e. morphisms whose composite with $x$ is $c_1$, resp. $c_2$), and, indexed by a type $\iota$, families $p_1 : \iota \to$ sections of $c_1$ and $p_2 : \iota \to$ sections of $c_2$ (morphisms $\operatorname{Spec}\kappa \to C_i$ splitting $c_i$). Let $h : T \to \operatorname{Spec}\kappa$ be a further $\kappa$-scheme, let $u : \iota \to \Gamma(T,\top)^\times$, and let $M, M'$ be sheaves of modules on the fibre product $X \times_{\operatorname{Spec}\kappa} T$. Assume both $M$ and $M'$ satisfy `IsNodeUnitModule` for the same data: that is, for each of them there exist morphisms $j_1$ to the pushforward along `curveChange` of $i_1$ of the unit module on $C_1 \times_{\operatorname{Spec}\kappa} T$ and $j_2$ to the corresponding pushforward for $i_2$, such that for every open $W$ of the base change of $X$ the map $m \mapsto (j_1(m), j_2(m))$ on sections over $W$ is injective with image exactly the set of pairs $(f,g)$ satisfying, for every $j \in \iota$, the node condition that the restriction of $f$ along the $j$-th node section of the first curve equals $u_j$ times the restriction of $g$ along the $j$-th node section of the second curve, as sections over the $j$-th node locus inside $W$. Then the type of isomorphisms $M \cong M'$ is nonempty.
--
--   This is the uniqueness half of the construction attaching to a family of units $u$ the structure sheaf of the curve obtained by gluing $C_1$ and $C_2$ along the prescribed pairs of rational points with the twists $u_j$: a module described sectionwise as the fibre product of the two pushed-forward structure sheaves over the node conditions is determined by $u$ up to isomorphism. It is used in the construction of line bundles on two glued smooth curves and in the identification of the relative Picard functor of such a configuration, in particular by the results producing admissible homomorphisms for two glued smooth curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_iso.lean

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

theorem AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.nonempty_iso
    {κ : Type u} [Field κ]
    {X C₁ C₂ : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    {i₁ : SchemeHomOver c₁ x} {i₂ : SchemeHomOver c₂ x}
    {ι : Type v} {p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁} {p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂}
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u : ι → Γ(T, ⊤)ˣ} {M M' : (pullback x h).Modules}
    (hM : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M) (hM' : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M') :
    Nonempty (M ≅ M') := by sorry
