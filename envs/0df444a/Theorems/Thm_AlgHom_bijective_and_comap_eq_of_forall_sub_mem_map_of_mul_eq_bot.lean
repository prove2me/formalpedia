-- Prove2me | Theorems.Thm_AlgHom_bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot
-- name    : AlgHom.bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/a3dd6f98-4e05-5b49-88c7-2a8b3214f874
-- title:
--   Endomorphisms congruent to the identity modulo a square-zero ideal
-- statement:
--   Let $T'$ be a commutative ring and $I \subseteq T'$ an ideal with $I \cdot I = \bot$, let $C$ be a commutative ring equipped with a $T'$-algebra structure, and let $\psi \colon C \to C$ be a $T'$-algebra homomorphism such that for every $c \in C$ the difference $\psi(c) - c$ lies in the ideal $I \cdot C$, that is, in the image ideal $I.\mathrm{map}\,(\mathrm{algebraMap}\ T'\ C)$ of $I$ under the structure map. The conclusion is a conjunction: first, the underlying function of $\psi$ is bijective; second, for every point $\mathfrak p$ of the prime spectrum of $C$, the pullback of $\mathfrak p$ along the ring homomorphism underlying $\psi$ equals $\mathfrak p$, i.e. $\mathrm{Spec}\,\psi$ is the identity map on points of $\operatorname{Spec} C$. Note that $T'$ and $C$ are taken in the same universe, and no finiteness, Noetherian, local or flatness hypothesis is imposed.
--
--   This is the affine algebraic form of the statement that an endomorphism of a scheme which is the identity modulo a square-zero ideal is an automorphism inducing the identity on the underlying topological space; it is the infinitesimal-automorphism input used by [`AlgebraicGeometry.exists_iso_of_specMap_quotient_comp_eq_fromSpec`](thm.html#AlgebraicGeometry.exists_iso_of_specMap_quotient_comp_eq_fromSpec).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem AlgHom.bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot
    {T' : Type u} [CommRing T'] (I : Ideal T') (hI2 : I * I = ⊥)
    (C : Type u) [CommRing C] [Algebra T' C]
    (ψ : C →ₐ[T'] C) (hψ : ∀ c : C, ψ c - c ∈ I.map (algebraMap T' C)) :
    Function.Bijective ψ ∧ ∀ p : PrimeSpectrum C, PrimeSpectrum.comap ψ.toRingHom p = p := by sorry
