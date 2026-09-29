-- Prove2me | Theorems.Thm_Deformation_exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_zmodp
-- name    : Deformation.exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/7b26d620-dc91-500d-8ad4-77f71786e9c6
-- title:
--   Fontaine's criterion for lifting special-fibre points, residue field mathbf Fₚ
-- statement:
--   Let $p$ be a prime and let $\mathcal O$ be a commutative ring in which $p$ is a non-zero-divisor, equipped with an $\mathcal O$-algebra structure on $\mathbf Z/p$ whose structure map has kernel exactly the ideal $(p)$, and which is complete and separated for the $(p)$-adic topology. Let $\mathcal R$ be a commutative ring which is a Hopf algebra over $\mathcal O$ with cocommutative comultiplication, free and finite as an $\mathcal O$-module of rank $p^{a}$ for some $a\in\mathbf N$, and such that the $\mathbf Z/p$-linear dual [`CartierDual`](def/HopfAlgebra_CartierDual.html#L12) of the special fibre $\mathbf Z/p\otimes_{\mathcal O}\mathcal R$ is a local ring. Let $Y$ be a commutative $\mathcal O$-algebra, finite and free as an $\mathcal O$-module, and let $\chi\colon \mathbf Z/p\otimes_{\mathcal O}\mathcal R\to\mathbf Z/p\otimes_{\mathcal O}Y$ be a $\mathbf Z/p$-algebra homomorphism. Assume that for every $n$ and every element $m$ of the additive subgroup [`Deformation.wittHom`](def/Dieudonne_WittVectorHom.html#L246) of $W_n(\mathbf Z/p\otimes_{\mathcal O}\mathcal R)$ — the truncated Witt vectors $x$ of length $n$ satisfying $W_n(\Delta)(x)=W_n(\iota_1)(x)+W_n(\iota_2)(x)$ for the comultiplication $\Delta$ and the two inclusions into the tensor square — the following holds: if $m$ lifts to a Witt vector $X$ over $\mathcal R$ whose $(n-1)$-st ghost component lies in $(p^{n})$, then its image under $W_n(\chi)$ lifts to a Witt vector over $Y$ with $(n-1)$-st ghost component in $(p^{n})$. Then $\chi$ is the base change along $\mathcal O\to\mathbf Z/p$ of some $\mathcal O$-algebra homomorphism $x\colon\mathcal R\to Y$, i.e. $\mathrm{id}_{\mathbf Z/p}\otimes x=\chi$.
--
--   This is Fontaine's lifting criterion for points of a finite flat commutative unipotent $p$-group scheme $G=\operatorname{Spec}\mathcal R$ over a $p$-adically complete base with residue ring $\mathbf F_p$: a point of the special fibre with values in $\operatorname{Spec}Y$ whose effect on truncated Witt-vector homomorphisms preserves the Fontaine kernel condition on ghost components comes from an integral point. It is the surjectivity half of the statement that the Dieudonné-module functor with its Fontaine submodule is fully faithful, and is used by [`Deformation.DieudonneModule.map_baseChange_injective_and_exists_map_baseChange_eq`](thm.html#Deformation.DieudonneModule.map_baseChange_injective_and_exists_map_baseChange_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_zmodp.lean

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

theorem Deformation.exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (ℛ : Type v) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] (hrank : ∃ a : ℕ, Module.finrank 𝓞 ℛ = p ^ a)
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) ℛ)))
    (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
    (χ : TensorProduct 𝓞 (ZMod p) ℛ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) Y)
    (hχ : ∀ (n : ℕ) (m : Deformation.wittHom (ZMod p) p n (TensorProduct 𝓞 (ZMod p) ℛ)),
      (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) ℛ)) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom →
        Deformation.TruncWitt.map χ.toRingHom
            (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) ℛ)) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y).toRingHom) :
    ∃ x : ℛ →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) x = χ := by sorry
