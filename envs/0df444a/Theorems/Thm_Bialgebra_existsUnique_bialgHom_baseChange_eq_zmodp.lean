-- Prove2me | Theorems.Thm_Bialgebra_existsUnique_bialgHom_baseChange_eq_zmodp
-- name    : Bialgebra.existsUnique_bialgHom_baseChange_eq_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/750b7aa2-6041-505f-a44b-be54c058f8d1
-- title:
--   Unique bialgebra lift of maps from a formally étale bialgebra
-- statement:
--   Let $p$ be a prime and let $\mathcal O$ be a commutative ring in which the image of $p$ is a non-zero-divisor, equipped with an $\mathcal O$-algebra structure on $\mathbb Z/p$ whose structure morphism $\mathcal O \to \mathbb Z/p$ has kernel exactly the principal ideal $(p)$, and assume $\mathcal O$ is complete and separated for the $(p)$-adic filtration. Let $H$ be a commutative $\mathcal O$-bialgebra which is finite and free as an $\mathcal O$-module and formally étale as an $\mathcal O$-algebra, and let $L$ be a commutative $\mathcal O$-bialgebra which is finite and free as an $\mathcal O$-module. Then for every homomorphism of $\mathbb Z/p$-bialgebras $\bar\varphi \colon \mathbb Z/p \otimes_{\mathcal O} H \to \mathbb Z/p \otimes_{\mathcal O} L$ there is a unique homomorphism of $\mathcal O$-bialgebras $\varphi \colon H \to L$ whose base change $\mathrm{id}_{\mathbb Z/p} \otimes \varphi$ agrees with $\bar\varphi$ as a morphism of $\mathbb Z/p$-algebras. (The uniqueness clause is uniqueness among bialgebra homomorphisms with this property.)
--
--   This is the bialgebra form of full faithfulness of reduction modulo $p$ on maps out of a finite étale object: on Spec, $\mathrm{Hom}(G, E) = \mathrm{Hom}(G_{\mathbb F_p}, E_{\mathbb F_p})$ for $E$ finite étale and $G$ finite flat over a $p$-adically complete base. It is used in the construction of formally étale bialgebra quotients and of the associated towers attached to $p$-divisible groups, via [`HopfAlgebra.exists_formallyEtale_bialgHom_injective_bijective_baseChange_zmodp`](thm.html#HopfAlgebra.exists_formallyEtale_bialgHom_injective_bijective_baseChange_zmodp) and [`PDivisibleGroup.exists_formallyEtale_tower_bijective_baseChange_zmodp`](thm.html#PDivisibleGroup.exists_formallyEtale_tower_bijective_baseChange_zmodp); the underlying algebra statement is [`Algebra.FormallyEtale.existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp`](thm.html#Algebra.FormallyEtale.existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Bialgebra_existsUnique_bialgHom_baseChange_eq_zmodp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v w

theorem Bialgebra.existsUnique_bialgHom_baseChange_eq_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (H : Type v) [CommRing H] [Bialgebra 𝓞 H] [Module.Free 𝓞 H] [Module.Finite 𝓞 H]
    [Algebra.FormallyEtale 𝓞 H]
    (L : Type w) [CommRing L] [Bialgebra 𝓞 L] [Module.Free 𝓞 L] [Module.Finite 𝓞 L]
    (φbar : (ZMod p ⊗[𝓞] H) →ₐc[ZMod p] (ZMod p ⊗[𝓞] L)) :
    ∃! φ : H →ₐc[𝓞] L,
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (φ : H →ₐ[𝓞] L) =
        (φbar : ZMod p ⊗[𝓞] H →ₐ[ZMod p] ZMod p ⊗[𝓞] L) := by sorry
