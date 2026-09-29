-- Prove2me | Theorems.Thm_Deformation_HondaSystem_exists_pDivisibleTower_dieudonneModule_of_range_pow_le
-- name    : Deformation.HondaSystem.exists_pDivisibleTower_dieudonneModule_of_range_pow_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/f98490b8-7b1b-58f0-8ab0-70eb1a75221a
-- title:
--   Realising Honda systems by unipotent p-divisible towers
-- statement:
--   Let $\mathcal O$ be a commutative ring and $p$ a prime such that $p$ is a non-zero-divisor in $\mathcal O$, let $\mathbf Z/p$ carry an $\mathcal O$-algebra structure whose structure map has kernel exactly $(p)$, and assume $\mathcal O$ is adically complete for $(p)$. Let $r \in \mathbb N$ and let $H_1$ be a Honda system with parameter $p$ on the free module $\mathcal O^r$: $\mathcal O$-linear endomorphisms $F, V$ with $F \circ V = V \circ F = p\,\mathrm{id}$, together with a submodule $L$ such that every element of $L \cap \operatorname{range} F$ is $p$ times an element of $L$, $p\,y \in \operatorname{range} F$ for all $y \in L$, $\operatorname{range} F + L = \mathcal O^r$, and $V$ is injective on $L$. Assume $V^N(\mathcal O^r) \subseteq p\,\mathcal O^r$ for some $N$. Then there exist types $L_v$ ($v \in \mathbb N$), each a commutative ring and a cocommutative Hopf algebra over $\mathcal O$, free and finite as an $\mathcal O$-module, and bialgebra maps $t_v \colon L_{v+1} \to L_v$ such that: each $t_v$ is surjective; $\operatorname{rank}_{\mathcal O} L_v = p^{vr}$; $\ker t_v$ is the image of the augmentation ideal of $L_{v+1}$ under the $p^v$-multiplication algebra endomorphism; and the Cartier dual of $\mathbf Z/p \otimes_{\mathcal O} L_v$ is a local ring. Moreover there exist additive surjections $\pi_v \colon \mathcal O^r \to M(\mathbf Z/p \otimes_{\mathcal O} L_v)$ onto the Dieudonné module (the colimit over $n$ of the additive maps into truncated Witt vectors of length $n$) with $\pi_v(x) = 0$ exactly when $x \in p^v \mathcal O^r$, intertwining $F$ and $V$ with the Frobenius and Verschiebung of the Dieudonné module, carrying the additive subgroup underlying $L$ onto the Fontaine–Hodge subgroup attached to the ring map $L_v \to \mathbf Z/p \otimes_{\mathcal O} L_v$, and satisfying $M(\mathbf Z/p \otimes t_v) \circ \pi_{v+1} = \pi_v$.
--
--   This is the object half of Fontaine's classification of $p$-divisible groups over $W(k)$ by Honda systems, in the unipotent case and for $k = \mathbf F_p$, written levelwise: the data produced is that of a $p$-divisible group of height $r$ over $\mathcal O$ whose $v$-th level has Dieudonné module $\mathcal O^r/p^v$ and Fontaine submodule the image of $L$. It is used in the construction of $p$-divisible groups with prescribed Dieudonné-theoretic invariants, being cited by [`Deformation.exists_pDivisibleTower_ker_eq_map_bijective_map_comp_mem_fontaineKer_of_isLocalRing_cartierDual_zmodp`](thm.html#Deformation.exists_pDivisibleTower_ker_eq_map_bijective_map_comp_mem_fontaineKer_of_isLocalRing_cartierDual_zmodp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_HondaSystem_exists_pDivisibleTower_dieudonneModule_of_range_pow_le.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem Deformation.HondaSystem.exists_pDivisibleTower_dieudonneModule_of_range_pow_le
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (hV : ∃ N : ℕ, ∀ x, ∃ y, (H₁.V ^ N) x = (p : 𝓞) • y) :
    ∃ (L : ℕ → Type u) (_ : ∀ v, CommRing (L v)) (_ : ∀ v, HopfAlgebra 𝓞 (L v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (L v)) (_ : ∀ v, Module.Free 𝓞 (L v))
      (_ : ∀ v, Module.Finite 𝓞 (L v)) (t : ∀ v, L (v + 1) →ₐc[𝓞] L v),
      (∀ v, Function.Surjective (t v)) ∧ (∀ v, Module.finrank 𝓞 (L v) = p ^ (v * r)) ∧
      (∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v)) ∧
      (∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v)))) ∧
    ∃ π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)),
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y) ∧
      (∀ v x, π v (H₁.F x) =
        Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)) (π v x)) ∧
      (∀ v x, π v (H₁.V x) =
        Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)) (π v x)) ∧
      (∀ v, (Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight :
            L v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L v)).toRingHom).toAddSubgroup =
        H₁.L.toAddSubgroup.map (π v)) ∧
      (∀ v x, Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v)) (π (v + 1) x) = π v x) := by sorry
