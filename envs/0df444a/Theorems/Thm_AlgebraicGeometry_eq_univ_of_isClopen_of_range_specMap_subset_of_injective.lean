-- Prove2me | Theorems.Thm_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective
-- name    : AlgebraicGeometry.eq_univ_of_isClopen_of_range_specMap_subset_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/0ac35521-ccc0-5820-bb0d-49dd4be2d37c
-- title:
--   A closed set containing a dense image is all of Spec R₀
-- statement:
--   Let $R_0$ and $L$ be commutative rings (in the lowest universe) and let $\varphi : R_0 \to L$ be a ring homomorphism which is injective as a function. Let $W$ be a subset of the underlying topological space of the scheme $\operatorname{Spec} R_0$, i.e. of the prime spectrum of $R_0$, and assume $W$ is clopen (closed and open). Assume further that the set-theoretic range of the continuous map underlying the morphism of schemes $\operatorname{Spec}\varphi : \operatorname{Spec} L \to \operatorname{Spec} R_0$ is contained in $W$; concretely, every prime of $R_0$ of the form $\varphi^{-1}(\mathfrak q)$ with $\mathfrak q$ a prime of $L$ lies in $W$. The conclusion is that $W$ is the whole space, $W = \operatorname{Spec} R_0$.
--
--   This is the standard fact that the image of $\operatorname{Spec}\varphi$ is dense when $\varphi$ is injective (its closure is $V(\ker\varphi) = V(0)$), combined with the observation that a closed set containing a dense subset is everything. It is used as a connectedness/clopen-descent step in the noetherian-approximation arguments for fake elliptic curves, being cited by [`AlgebraicGeometry.forall_finrank_eq_of_isPullback_of_injective`](thm.html#AlgebraicGeometry.forall_finrank_eq_of_isPullback_of_injective), [`AlgebraicGeometry.forall_topologicalKrullDim_preimage_eq_of_isPullback_of_injective_of_isConnected`](thm.html#AlgebraicGeometry.forall_topologicalKrullDim_preimage_eq_of_isPullback_of_injective_of_isConnected) and [`CerednikDrinfeld.QM.FakeEllipticCurve.generates_annihilator_of_isPullback_of_injective_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.generates_annihilator_of_isPullback_of_injective_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.eq_univ_of_isClopen_of_range_specMap_subset_of_injective
    {R₀ L : Type} [CommRing R₀] [CommRing L] (φ : R₀ →+* L) (hφ : Function.Injective φ)
    (W : Set ↥(Spec (CommRingCat.of R₀))) (hW : IsClopen W)
    (hWL : Set.range (Spec.map (CommRingCat.ofHom φ)).base ⊆ W) : W = Set.univ := by sorry
