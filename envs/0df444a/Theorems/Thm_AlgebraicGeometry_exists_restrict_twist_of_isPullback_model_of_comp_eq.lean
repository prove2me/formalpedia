-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_restrict_twist_of_isPullback_model_of_comp_eq
-- name    : AlgebraicGeometry.exists_restrict_twist_of_isPullback_model_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/916d7a33-c1ea-5cd8-9c6e-464999b23038
-- title:
--   Twist of a base change restricts to a model
-- statement:
--   Let $A$ be a commutative ring, $R_0$ an $A$-algebra and $k$ an algebra over both, with $A \to R_0 \to k$ a scalar tower, and write $\mathrm{specMap}$ for the morphism of spectra induced by a structure map. Let $c_X : X \to \operatorname{Spec} A$ be a scheme over $A$ and let $\varphi : \operatorname{Spec} k \to \operatorname{Spec} k$ satisfy $\mathrm{specMap}_{R_0,k} \circ \varphi = \mathrm{specMap}_{R_0,k}$, i.e. $\varphi$ lies over $\operatorname{Spec} R_0$. Let $F$ be an endomorphism of $X_k := X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ with $\mathrm{pr}_X \circ F = \mathrm{pr}_X$ and $\mathrm{pr}_{\operatorname{Spec} k} \circ F = \varphi \circ \mathrm{pr}_{\operatorname{Spec} k}$. Let $c : C \to \operatorname{Spec} k$ be a $k$-scheme and $i : C \to X_k$ a morphism with $\mathrm{pr}_{\operatorname{Spec} k} \circ i = c$. Suppose given $c_p : C_p \to \operatorname{Spec} R_0$, a morphism $i_p : C_p \to X \times_{\operatorname{Spec} A} \operatorname{Spec} R_0$ and $g : C \to C_p$ such that the square with $g, c, c_p, \mathrm{specMap}_{R_0,k}$ is a pullback, and $\mathrm{pr}_X \circ i_p \circ g = \mathrm{pr}_X \circ i$. Then there is $F_C : C \to C$ with $i \circ F_C = F \circ i$, $g \circ F_C = g$, such that the square with $F_C, c, c, \varphi$ is a pullback, and such that for every section $x$ of $c$ (a morphism $\operatorname{Spec} k \to C$ with $c \circ x = \mathrm{id}$) there is a section $x'$ of $c$ with $F_C \circ x' = x \circ \varphi$ and $\mathrm{pr}_X \circ i \circ x' = \mathrm{pr}_X \circ i \circ x \circ \varphi$.
--
--   This is the descent of a twist of the base, such as a Frobenius, to a subscheme admitting a model over a subring over which the twist is trivial: since $C \cong C_p \times_{\operatorname{Spec} R_0} \operatorname{Spec} k$, the endomorphism $\mathrm{id} \times \varphi$ of $X_k$ restricts to $C$ compatibly with the given embedding and acts on $k$-points by twisting. It is used in the analysis of Frobenius on the special fibre of a modular curve, where the components of the fibre are defined over the prime field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_restrict_twist_of_isPullback_model_of_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.exists_restrict_twist_of_isPullback_model_of_comp_eq
    {A : Type u} [CommRing A] (R₀ : Type u) [CommRing R₀] [Algebra A R₀] (k : Type u) [CommRing k] [Algebra A k] [Algebra R₀ k]
    [IsScalarTower A R₀ k]
    {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of A))
    (φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)) (hφ : φ ≫ specMap R₀ k = specMap R₀ k)
    (F : pullback cX (specMap A k) ⟶ pullback cX (specMap A k))
    (hF₁ : F ≫ pullback.fst cX (specMap A k) = pullback.fst cX (specMap A k))
    (hF₂ : F ≫ pullback.snd cX (specMap A k) = pullback.snd cX (specMap A k) ≫ φ)
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (i : SchemeHomOver c (baseChange A cX k))
    {Cₚ : Scheme.{u}} (cₚ : Cₚ ⟶ Spec (CommRingCat.of R₀)) (iₚ : Cₚ ⟶ pullback cX (specMap A R₀)) (g : C ⟶ Cₚ)
    (hg : IsPullback g c cₚ (specMap R₀ k))
    (hgi : g ≫ iₚ ≫ pullback.fst cX (specMap A R₀) = i.1 ≫ pullback.fst cX (specMap A k)) :
    ∃ F_C : C ⟶ C,
      F_C ≫ i.1 = i.1 ≫ F ∧ F_C ≫ g = g ∧ IsPullback F_C c c φ ∧
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c, ∃ x' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c,
        x'.1 ≫ F_C = φ ≫ x.1 ∧
        x'.1 ≫ i.1 ≫ pullback.fst cX (specMap A k) = φ ≫ x.1 ≫ i.1 ≫ pullback.fst cX (specMap A k) := by sorry
