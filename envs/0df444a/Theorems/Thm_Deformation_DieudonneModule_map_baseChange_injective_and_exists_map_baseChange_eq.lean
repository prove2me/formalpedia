-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_map_baseChange_injective_and_exists_map_baseChange_eq
-- name    : Deformation.DieudonneModule.map_baseChange_injective_and_exists_map_baseChange_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/2154b54e-1a55-59d5-934d-687ad709b2c3
-- title:
--   Fontaine full faithfulness for unipotent p-group schemes
-- statement:
--   Let $p$ be a prime and let $\mathcal O$ be a commutative ring in which $p$ is a non-zero-divisor, equipped with an $\mathcal O$-algebra structure on $\mathbf Z/p$ whose structure map has kernel exactly the ideal $(p)$, and complete and separated for the $(p)$-adic filtration. Let $\mathcal R$ and $\mathcal R'$ be commutative rings carrying cocommutative Hopf algebra structures over $\mathcal O$, each free and finite as an $\mathcal O$-module, with $\operatorname{rank}_{\mathcal O}\mathcal R' = p^{a}$ for some $a$, and assume that for both of them the Cartier dual of the base change — that is, the $\mathbf Z/p$-linear dual `Module.Dual` of $\mathbf Z/p\otimes_{\mathcal O}\mathcal R$, respectively of $\mathbf Z/p\otimes_{\mathcal O}\mathcal R'$ — is a local ring. Write $M(\,\cdot\,)$ for [`Deformation.DieudonneModule (ZMod p) p`](def/Dieudonne_WittHomColimit.html#L234), the direct limit over $n$, along the shift maps, of the additive groups of those truncated Witt vectors of length $n$ over the given bialgebra that are primitive for the comultiplication, with the additive endomorphisms `frobenius` and `verschiebung` induced by the level-wise Frobenius and Verschiebung, and with the $\mathbb Z$-submodule [`Deformation.fontaineHodge`](def/Dieudonne_FontaineHodge.html#L272) attached to a ring homomorphism $\pi$, consisting of the classes represented at some level $n$ by an element whose underlying truncated Witt vector lies in `fontaineKer p n π`. Then two assertions hold simultaneously. First, the map sending an $\mathcal O$-bialgebra homomorphism $f : \mathcal R' \to \mathcal R$ to the induced additive map $M(\mathbf Z/p\otimes_{\mathcal O}\mathcal R') \to M(\mathbf Z/p\otimes_{\mathcal O}\mathcal R)$ coming from the base change $\mathrm{id}\otimes f$ is injective. Second, every additive homomorphism $\varphi : M(\mathbf Z/p\otimes_{\mathcal O}\mathcal R') \to M(\mathbf Z/p\otimes_{\mathcal O}\mathcal R)$ which commutes with `frobenius`, commutes with `verschiebung`, and carries the `fontaineHodge` submodule attached to the ring homomorphism underlying $\mathcal R' \to \mathbf Z/p\otimes_{\mathcal O}\mathcal R'$, $r \mapsto 1\otimes r$, into the one attached to $\mathcal R \to \mathbf Z/p\otimes_{\mathcal O}\mathcal R$, is of this form for some $\mathcal O$-bialgebra homomorphism $f : \mathcal R' \to \mathcal R$.
--
--   This is the full faithfulness half of Fontaine's theorem identifying finite flat commutative $p$-group schemes over a $p$-adically complete base with unipotent special fibre with their finite Honda systems, stated for all primes including $p = 2$: morphisms of the group schemes correspond exactly to the additive maps of Dieudonné modules respecting $F$, $V$ and the Fontaine submodule. It is used in the construction of Honda-system models for residual Galois representations, namely in [`ResidualGaloisRep.exists_injective_flatClassSet_selfExt_of_hondaSystem_model`](thm.html#ResidualGaloisRep.exists_injective_flatClassSet_selfExt_of_hondaSystem_model) and [`ResidualGaloisRep.finrank_endHonda_le_finrank_invariants_of_hondaSystem_model`](thm.html#ResidualGaloisRep.finrank_endHonda_le_finrank_invariants_of_hondaSystem_model).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_map_baseChange_injective_and_exists_map_baseChange_eq.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem Deformation.DieudonneModule.map_baseChange_injective_and_exists_map_baseChange_eq
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (ℛ : Type v) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ]
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) ℛ)))
    (ℛ' : Type w) [CommRing ℛ'] [HopfAlgebra 𝓞 ℛ'] [Coalgebra.IsCocomm 𝓞 ℛ']
    [Module.Free 𝓞 ℛ'] [Module.Finite 𝓞 ℛ'] (hrank' : ∃ a : ℕ, Module.finrank 𝓞 ℛ' = p ^ a)
    (hunip' : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) ℛ'))) :
    (∀ f g : ℛ' →ₐc[𝓞] ℛ,
        Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) f) =
          Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) g) →
        f = g) ∧
    (∀ φ : Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ') →+
        Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ),
      (∀ z, φ (Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ') z) =
          Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ) (φ z)) →
      (∀ z, φ (Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ') z) =
          Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ) (φ z)) →
      (∀ z ∈ Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight : ℛ' →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ').toRingHom,
        φ z ∈ Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom) →
      ∃ f : ℛ' →ₐc[𝓞] ℛ,
        Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) f) = φ) := by sorry
