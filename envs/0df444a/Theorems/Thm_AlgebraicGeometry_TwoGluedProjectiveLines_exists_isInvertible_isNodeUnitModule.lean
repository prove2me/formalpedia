-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.exists_isInvertible_isNodeUnitModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/05c1d0b1-1a4a-5f0c-a558-8be815590689
-- title:
--   Existence of node-unit line bundles on two glued lines
-- statement:
--   Let $\kappa$ be an algebraically closed field, and let $x : X \to \operatorname{Spec}\kappa$ be a reduced $\kappa$-scheme. Let $M_1, M_2$ be curve models of $\kappa(t) =$ `RatFunc κ` over $\kappa$, i.e. integral schemes $M_j.C$ that are proper and smooth of relative dimension $1$ over $\kappa$, equipped with a ring isomorphism of $\kappa(t)$ with the function field compatible with the structure map, with a bijection `placeEquiv` from the closed points onto the places of $\kappa(t)/\kappa$ matching stalks with valuation subrings, and with the property that any finite set of points lies in an affine open. Let $i_1 : M_1.C \to X$ and $i_2 : M_2.C \to X$ be closed immersions with $i_j$ followed by $x$ equal to $M_j.\mathrm{toBase}$, whose images cover $X$. Let $s \in \mathbb{N}$ and $a, b : \mathrm{Fin}\, s \to \kappa^\times$ with $a$ injective; write $\alpha_i, \beta_i$ for the closed points of $M_1.C$, $M_2.C$ corresponding under `placeEquiv` to the places of $\kappa(t)$ attached to $X - a_i$, resp. $X - b_i$. Assume $i_1(\alpha_i) = i_2(\beta_i)$ for all $i$, that every pair $(p,q)$ with $i_1(p) = i_2(q)$ is of this form, and that $M_1.C \times_X M_2.C$ is reduced. Finally let $h : T \to \operatorname{Spec}\kappa$ be a $\kappa$-scheme and $u : \mathrm{Fin}\, s \to \Gamma(T,\top)^\times$. Then there is a sheaf of modules $M$ on $X \times_\kappa T$ which is invertible (each point has an open neighbourhood $U$ with the restriction of $M$ to $U$ isomorphic to the unit sheaf) and is a node-unit module for these data: there exist morphisms $j_1, j_2$ from $M$ to the pushforwards along $i_1 \times \mathrm{id}_T$, resp. $i_2 \times \mathrm{id}_T$, of the unit sheaves of $M_1.C \times_\kappa T$ and $M_2.C \times_\kappa T$, such that over every open $W$ of $X \times_\kappa T$ the map $m \mapsto (j_1(m), j_2(m))$ on sections is injective with image exactly the set of pairs $(f,g)$ whose restrictions to the $i$-th node locus satisfy $f = u_i\, g$ for every $i$, in the sense of the predicate `NodeCondition`.
--
--   This is the existence half of the description of line bundles on a curve obtained by gluing two projective lines transversally at $s$ nodes: the bundle glued from the trivial bundles of the two lines via prescribed units $u_i$ at the nodes, formed over an arbitrary parameter scheme $T$. It is used by [`AlgebraicGeometry.TwoGluedProjectiveLines.IsNodeUnitModule.pullback_baseChangeSnd`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.IsNodeUnitModule.pullback_baseChangeSnd) and by [`AlgebraicGeometry.TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit) in the computation of the relative Picard functor of such a configuration.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
  NeronModelInfra AlgebraicGeometry.TwoGluedProjectiveLines

theorem AlgebraicGeometry.TwoGluedProjectiveLines.exists_isInvertible_isNodeUnitModule
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X]
    (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {s : ℕ} (a b : Fin s → κˣ) (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).1
                = i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i : κ))).1)
    (hinter : ∀ p q, i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) (u : Fin s → Γ(T, ⊤)ˣ) :
    ∃ M : (pullback x h).Modules, Scheme.Modules.IsInvertible M ∧
      IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u M := by sorry
