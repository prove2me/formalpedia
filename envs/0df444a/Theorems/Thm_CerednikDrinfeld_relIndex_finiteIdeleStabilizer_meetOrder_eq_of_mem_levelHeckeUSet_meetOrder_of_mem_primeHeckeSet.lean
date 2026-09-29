-- Prove2me | Theorems.Thm_CerednikDrinfeld_relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet
-- name    : CerednikDrinfeld.relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/64e510d9-62fb-5391-bd67-957c06175c72
-- title:
--   Index ℓ of the stabiliser of a meet order in U_R
-- statement:
--   Fix $a,b\in\mathbb Q$, a nonzero squarefree $N\in\mathbb N$, and primes $q,q'$ with $q\nmid N$ and $q'\nmid N$; assume $a<0$, $b<0$, and that for every $v$ in the height-one spectrum of $\mathcal O_{\mathbb Q}$ the completion $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly when $q'$ lies in $v$. Let $\Lambda,R$ be $\mathbb Z$-submodules of $\mathbb H[\mathbb Q,a,b]$ with $R\le\Lambda$, where $\Lambda$ is an order maximal among orders, and $R=\Lambda_1\sqcap\Lambda_2$ for maximal orders $\Lambda_i$ with $[\Lambda_1:R]=N$ as additive groups. Let $n$ be a unit of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb A_{\mathbb Q}^{\mathrm f}$ lying in `primeHeckeSet R q`, i.e. $n\in\hat R$, $q\,n^{-1}\in\hat R$, $n^{-1}\notin\hat R$, $q^{-1}n\notin\hat R$, where $\hat R$ denotes [`Submodule.finiteAdeleBox R`](def/Submodule_FiniteAdeleBox.html#L14). Put $S=R\sqcap(\mathbb H\cap n\hat Rn^{-1})$. Let $\ell$ be a prime dividing $N$ and let $g$ be a finite idele belonging to `levelHeckeUSet Λ S ℓ`: thus $g\in\hat S$, $\ell\,g^{-1}\in\hat S$, $g^{-1}\notin\hat S$, $\ell^{-1}g\notin\hat S$, $\mathbb H\cap g\hat Sg^{-1}\neq S$, and $S\not\le\mathbb H\cap g\hat\Lambda g^{-1}$. Then the stabiliser in the finite idele units of the box of the meet order $R\sqcap(\mathbb H\cap g\hat Rg^{-1})$ has relative index $\ell$ in the stabiliser of $\hat R$. Note that the conclusion forms the meet order of $R$, not of $S$, along $g$.
--
--   This is the local index computation underlying the degree-$\ell$ edges of the class-set graph of an Eichler order of squarefree level: passing from the unit group of a vertex order to that of the meet order cut out by an oriented level-$\ell$ Hecke idele divides the index by $\ell$. It is the edge-keyed companion of the corresponding statement for ideles in the level-$\ell$ Hecke set of $R$ itself, and is used in the construction of the degeneracy data of the class-set tower and in the identification of arrow degrees in the coset graph.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet

    {a b : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∣ N)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hg : g ∈ levelHeckeUSet Λ (meetOrder R n) ℓ) :
    (Submodule.finiteIdeleStabilizer (meetOrder R g)).relIndex (Submodule.finiteIdeleStabilizer R) = ℓ := by sorry
