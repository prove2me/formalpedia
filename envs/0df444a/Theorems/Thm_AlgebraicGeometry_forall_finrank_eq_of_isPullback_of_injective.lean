-- Prove2me | Theorems.Thm_AlgebraicGeometry_forall_finrank_eq_of_isPullback_of_injective
-- name    : AlgebraicGeometry.forall_finrank_eq_of_isPullback_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/a09008d8-f193-591f-b992-313fc8441606
-- title:
--   Constant rank of a finite flat morphism detected after base change along an injection
-- statement:
--   Let $\varphi : R_0 \to L$ be an injective ring homomorphism between commutative rings, and let $h_0 : C_0 \to \operatorname{Spec} R_0$ be a morphism of schemes that is finite, flat and locally of finite presentation. Suppose given a morphism $h : C \to \operatorname{Spec} L$ together with $g : C \to C_0$ such that the square with sides $g$, $h$, $h_0$ and $\operatorname{Spec}\varphi$ is cartesian, i.e. $C$ is the base change of $C_0$ along $\operatorname{Spec}\varphi : \operatorname{Spec} L \to \operatorname{Spec} R_0$. Let $r$ be a natural number and assume that the fibrewise rank $h.\mathrm{finrank}$ of $h$ equals $r$ at every point of $\operatorname{Spec} L$. Then for every point $t$ of $\operatorname{Spec} R_0$ the rank $h_0.\mathrm{finrank}$ of $h_0$ at $t$ equals $r$. Thus a finite locally free morphism over $R_0$ whose base change to $L$ has constant rank $r$ has constant rank $r$ over the whole of $\operatorname{Spec} R_0$; the conclusion is stated pointwise, for each $t$ separately.
--
--   This is the statement that the rank of a finite locally free morphism over a base ring $R_0$ may be read off after base change along an injection $R_0 \hookrightarrow L$, the point being that $\operatorname{Spec}\varphi$ has dense image when $\varphi$ is injective. It is used in the construction of finitely generated subalgebras of $L$ over which a fake elliptic curve and its level structures are already defined, in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_forall_finrank_eq_of_isPullback_of_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.forall_finrank_eq_of_isPullback_of_injective
    {R₀ L : Type} [CommRing R₀] [CommRing L] (φ : R₀ →+* L) (hφ : Function.Injective φ)
    {C₀ : Scheme.{0}} (h₀ : C₀ ⟶ Spec (CommRingCat.of R₀)) (hfin : IsFinite h₀) (hfl : Flat h₀)
    (hlfp : LocallyOfFinitePresentation h₀)
    {C : Scheme.{0}} (h : C ⟶ Spec (CommRingCat.of L)) (g : C ⟶ C₀)
    (hg : IsPullback g h h₀ (Spec.map (CommRingCat.ofHom φ)))
    (r : ℕ) (hrank : ∀ x : ↥(Spec (CommRingCat.of L)), h.finrank x = r)
    (t : ↥(Spec (CommRingCat.of R₀))) : h₀.finrank t = r := by sorry
