-- Prove2me | Theorems.Thm_Algebra_FormallyEtale_existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp
-- name    : Algebra.FormallyEtale.existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/acb9515d-f742-5a2f-b98f-d7832c8be537
-- title:
--   Unique lifting of algebra maps mod p for formally étale H
-- statement:
--   Let $\mathcal O$ be a commutative ring, let $p$ be a prime, assume $p$ is a non-zero-divisor in $\mathcal O$, let $\mathcal O$ carry an algebra structure over which $\mathbb Z/p$ is an $\mathcal O$-algebra whose structure map has kernel exactly the ideal $(p)$ of $\mathcal O$, and assume $\mathcal O$ is adically complete (complete and separated) for the ideal $(p)$. Let $H$ be a commutative $\mathcal O$-algebra which is free and finite as an $\mathcal O$-module and formally étale over $\mathcal O$, and let $T$ be a commutative $\mathcal O$-algebra which is free and finite as an $\mathcal O$-module. Then for every homomorphism of $\mathbb Z/p$-algebras $\bar\psi\colon \mathbb Z/p \otimes_{\mathcal O} H \to \mathbb Z/p \otimes_{\mathcal O} T$ there is a unique homomorphism of $\mathcal O$-algebras $\psi\colon H \to T$ whose base change along the identity of $\mathbb Z/p$, namely $\mathrm{id}_{\mathbb Z/p} \otimes \psi$, equals $\bar\psi$.
--
--   This is the full faithfulness of reduction modulo $p$ for formally étale finite free algebras over a $p$-adically complete base: the map $\mathrm{Hom}_{\mathcal O}(H,T) \to \mathrm{Hom}_{\mathbb Z/p}(H/p, T/p)$ is bijective. It is used in the treatment of Hopf algebras and bialgebras over such a base, for instance to lift bialgebra homomorphisms and formally étale equivalences from the reduction, and in the deformation-theoretic constructions that invoke them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallyEtale_existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v w

theorem Algebra.FormallyEtale.existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (H : Type v) [CommRing H] [Algebra 𝓞 H] [Module.Free 𝓞 H] [Module.Finite 𝓞 H] [Algebra.FormallyEtale 𝓞 H]
    (T : Type w) [CommRing T] [Algebra 𝓞 T] [Module.Free 𝓞 T] [Module.Finite 𝓞 T]
    (ψbar : ZMod p ⊗[𝓞] H →ₐ[ZMod p] ZMod p ⊗[𝓞] T) :
    ∃! ψ : H →ₐ[𝓞] T, Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) ψ = ψbar := by sorry
