-- Prove2me | Theorems.Thm_AlgebraicGeometry_forall_topologicalKrullDim_preimage_eq_of_isPullback_of_injective_of_isConnected
-- name    : AlgebraicGeometry.forall_topologicalKrullDim_preimage_eq_of_isPullback_of_injective_of_isConnected
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/b3e08894-e0d7-5045-84cf-1a105005b384
-- title:
--   Fibre dimension descends from the base change along an injection
-- statement:
--   Let $R_0$ and $L$ be commutative rings and $\varphi : R_0 \to L$ an injective ring homomorphism. Let $f_0 : A_0 \to \operatorname{Spec} R_0$ be a morphism of schemes (all schemes here in universe $0$) which is smooth and proper, and assume that for every point $t$ of $\operatorname{Spec} R_0$ the fibre $f_0^{-1}(\{t\})$, as a subspace of the underlying topological space of $A_0$, is connected (and nonempty). Let $f : A \to \operatorname{Spec} L$ and $g : A \to A_0$ be morphisms such that the square formed by $g$, $f$, $f_0$ and $\operatorname{Spec}$ of $\varphi$ is cartesian, i.e. $g$ followed by $f_0$ equals $f$ followed by $\operatorname{Spec}(\varphi)$ and the square is a pullback. Let $d$ be a natural number and suppose that for every point $x$ of $\operatorname{Spec} L$ the topological Krull dimension of the fibre $f^{-1}(\{x\})$ equals $d$. Then for every point $t$ of $\operatorname{Spec} R_0$ the topological Krull dimension of $f_0^{-1}(\{t\})$ equals $d$. Dimensions are taken in the sense of `topologicalKrullDim`, the supremum of lengths of chains of irreducible closed subsets of the fibre with its subspace topology.
--
--   This is the descent step of a constancy-of-fibre-dimension argument: a proper smooth family with connected fibres over $\operatorname{Spec} R_0$ has all its fibres of one dimension as soon as this holds after base change along an injection $R_0 \hookrightarrow L$ (typically $R_0$ a finitely generated subring of a field $L$). It is used in the construction of fake elliptic curves over finitely generated subalgebras, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_isPullback_levelIff_sections`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_isPullback_levelIff_sections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_forall_topologicalKrullDim_preimage_eq_of_isPullback_of_injective_of_isConnected.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.forall_topologicalKrullDim_preimage_eq_of_isPullback_of_injective_of_isConnected
    {R₀ L : Type} [CommRing R₀] [CommRing L] (φ : R₀ →+* L) (hφ : Function.Injective φ)
    {A₀ : Scheme.{0}} (f₀ : A₀ ⟶ Spec (CommRingCat.of R₀)) (hs : Smooth f₀) (hp : IsProper f₀)
    (hconn : ∀ t : ↥(Spec (CommRingCat.of R₀)), _root_.IsConnected (f₀.base ⁻¹' {t}))
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of L)) (g : A ⟶ A₀)
    (hg : IsPullback g f f₀ (Spec.map (CommRingCat.ofHom φ)))
    (d : ℕ) (hdim : ∀ x : ↥(Spec (CommRingCat.of L)), topologicalKrullDim ↥(f.base ⁻¹' {x}) = d)
    (t : ↥(Spec (CommRingCat.of R₀))) : topologicalKrullDim ↥(f₀.base ⁻¹' {t}) = d := by sorry
