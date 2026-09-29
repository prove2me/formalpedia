-- Prove2me | Theorems.Thm_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod
-- name    : Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/79ccb934-6539-5279-af45-78987194f236
-- title:
--   Fontaine lifting of a unipotent p-divisible tower over mathbf Fₚ
-- statement:
--   Let $p$ be a prime and $\mathcal O$ a commutative ring in which $p$ is a non-zero-divisor, equipped with an $\mathcal O$-algebra structure on $\mathbf Z/p$ whose structure map has kernel exactly the ideal $(p)$, and assume $\mathcal O$ is $(p)$-adically complete. Let $r\in\mathbb N$ and let $H_1$ be a Honda system for the element $p$ on the free module $\mathcal O^r$: $\mathcal O$-linear maps $F,V$ with $F\circ V=V\circ F=p\cdot\mathrm{id}$, together with a submodule $H_1.L$ such that every $x\in H_1.L\cap\operatorname{range}F$ is $p\cdot y$ for some $y\in H_1.L$, $p\cdot y\in\operatorname{range}F$ for $y\in H_1.L$, $\operatorname{range}F+H_1.L$ is everything, and $V$ is injective on $H_1.L$. Let $G_v$ ($v\in\mathbb N$) be commutative rings that are cocommutative Hopf algebras over $\mathbf Z/p$, finite as modules, with surjective bialgebra maps $s_v\colon G_{v+1}\to G_v$ such that $\dim_{\mathbf Z/p}G_v=p^{vr}$ and $\ker s_v$ is the image of the augmentation ideal of $G_{v+1}$ under multiplication by $p^v$, each Cartier dual $\operatorname{Hom}_{\mathbf Z/p}(G_v,\mathbf Z/p)$ being a local ring. Let $\pi_v\colon\mathcal O^r\to D(G_v)$ be additive maps into the Dieudonné modules (the colimit over $n$ of the additive, i.e. primitive, truncated Witt vectors of length $n$ on $G_v$), each surjective, with $\pi_v x=0$ exactly when $x\in p^v\mathcal O^r$, intertwining $H_1.F$, $H_1.V$ with the Frobenius and Verschiebung of $D(G_v)$, and compatible with the tower in the sense that $D(s_v)\circ\pi_{v+1}=\pi_v$. Then there exist commutative rings $L_v$ that are cocommutative Hopf algebras over $\mathcal O$, free and finite as $\mathcal O$-modules, and bialgebra maps $t_v\colon L_{v+1}\to L_v$ which are surjective, satisfy $\operatorname{rank}_{\mathcal O}L_v=p^{vr}$ and $\ker t_v=$ the image of the augmentation ideal of $L_{v+1}$ under multiplication by $p^v$, together with bijective $\mathbf Z/p$-bialgebra maps $e_v\colon G_v\to (\mathbf Z/p)\otimes_{\mathcal O}L_v$ satisfying $e_v\circ s_v=(\mathrm{id}\otimes t_v)\circ e_{v+1}$ for all $v$, and such that for every $v$ and every $x\in H_1.L$ the element $D(e_v)(\pi_v x)$ lies in the Fontaine–Hodge subgroup $\mathrm{fontaineHodge}$ attached to the ring homomorphism $L_v\to(\mathbf Z/p)\otimes_{\mathcal O}L_v$, $y\mapsto 1\otimes y$, that is, it is represented at some finite level $n$ by a primitive truncated Witt vector lying in $\mathrm{fontaineKer}$ of that homomorphism.
--
--   This is Fontaine's lifting theorem in the unipotent case over the prime field: a unipotent $p$-divisible tower of height $r$ over $\mathbf Z/p$ whose Dieudonné module is identified with $\mathcal O^r$ carrying a Honda system lifts to a $p$-divisible tower over $\mathcal O$ with the prescribed Hodge data, the identification of special fibres being realised by bialgebra isomorphisms compatible with the transition maps. It is the input to [`Deformation.HondaSystem.exists_pDivisibleTower_dieudonneModule_of_range_pow_le`](thm.html#Deformation.HondaSystem.exists_pDivisibleTower_dieudonneModule_of_range_pow_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod.lean

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

universe u v

theorem Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * r))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hunipG : ∀ v, IsLocalRing (CartierDual (ZMod p) (G v)))
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπ : ∀ v, Function.Surjective (π v))
    (hπker : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x))
    (hπV : ∀ v x, π v (H₁.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p (G v) (π v x))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x) :
    ∃ (L : ℕ → Type u) (_ : ∀ v, CommRing (L v)) (_ : ∀ v, HopfAlgebra 𝓞 (L v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (L v)) (_ : ∀ v, Module.Free 𝓞 (L v))
      (_ : ∀ v, Module.Finite 𝓞 (L v)) (t : ∀ v, L (v + 1) →ₐc[𝓞] L v),
      (∀ v, Function.Surjective (t v)) ∧ (∀ v, Module.finrank 𝓞 (L v) = p ^ (v * r)) ∧
      (∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v)) ∧
    ∃ e : ∀ v, G v →ₐc[ZMod p] TensorProduct 𝓞 (ZMod p) (L v),
      (∀ v, Function.Bijective (e v)) ∧
      (∀ v, (e v).comp (s v) =
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v)).comp (e (v + 1))) ∧
      (∀ v, ∀ x ∈ H₁.L, Deformation.DieudonneModule.map (ZMod p) p (e v) (π v x) ∈
        Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight :
            L v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L v)).toRingHom) := by sorry
