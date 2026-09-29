-- Prove2me | Theorems.Thm_CerednikDrinfeld_relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_dvd
-- name    : CerednikDrinfeld.relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/d5007e1f-85e6-53b3-8e6b-8ddd60ae368b
-- title:
--   Index ℓ of an idelic stabiliser of a meet order
-- statement:
--   Fix rationals $a,b$, natural numbers $N,q,q'$ with $N$ nonzero and squarefree and $q,q'$ prime, and assume $q\nmid N$, $q'\nmid N$, $q'\neq q$ and $q'\geq 5$, together with `IsDefiniteRamifiedExactlyAt a b q'`, i.e. $a<0$, $b<0$ and, for every finite place $v$ of $\mathbb{Q}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $q'$ lies in the prime of $v$. Let $\Lambda,R$ be $\mathbb{Z}$-submodules of $\mathbb{H}[\mathbb{Q},a,b]$ with $\Lambda$ a maximal order (an order, maximal among orders containing it), $R$ an Eichler order of level $N$ (an intersection $\Lambda_1\sqcap\Lambda_2$ of two maximal orders with relative additive index $N$ in $\Lambda_1$), and $R\leq\Lambda$. Let $n$ be a unit of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ lying in `primeHeckeSet R q`: $n$ lies in the finite adele box $\hat R$, $q\cdot n^{-1}\in\hat R$, while $n^{-1}\notin\hat R$ and $q^{-1}n\notin\hat R$. Let $\ell$ be a prime dividing $N$ and let $s$ be a finite idele such that $h=\hat\ell\,s^{-1}$, with $\hat\ell$ the diagonal idele of the scalar $\ell$, lies in `levelHeckeUSet Λ (meetOrder R n) ℓ`; writing $S=R\sqcap nRn^{-1}$ for `meetOrder R n`, this means $h\in$ `primeHeckeSet S ℓ`, $hSh^{-1}\neq S$, and $S\not\leq h\Lambda h^{-1}$ (conjugation taken in the sense of [`Submodule.conjByFiniteIdele`](def/Submodule_FiniteAdeleBox.html#L31)). Then the stabiliser, inside the unit group of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$, of the finite adele box of $R\sqcap sRs^{-1}$ has relative index exactly $\ell$ in the corresponding stabiliser of the finite adele box of $R$.
--
--   This is the local degree computation underlying the $U_\ell$-storey of the class-set tower at a prime $\ell$ dividing the squarefree level: passing from the Eichler order $R$ of level $N$ to the order $R\cap sRs^{-1}$ of level $N\ell$ multiplies the idelic unit group index by $\ell$, the classical Eichler–Hijikata count of Iwahori double cosets. It feeds the degeneracy and arrow-degree data on the Čerednik–Drinfeld coset graph, being used by [`CerednikDrinfeld.CosetGraph.relIndex_inf_map_conj_eq_arrowDegree_of_hecke`](thm.html#CerednikDrinfeld.CosetGraph.relIndex_inf_map_conj_eq_arrowDegree_of_hecke), its inverse-conjugate companion, and the existence statement for the class-set degeneracy data of the meet orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.relIndex_finiteIdeleStabilizer_meetOrder_eq_of_mem_levelHeckeUSet_meetOrder_of_dvd

    {a b : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq'5 : 5 ≤ q')
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∣ N)
    (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      levelHeckeUSet Λ (meetOrder R n) ℓ) :
    (Submodule.finiteIdeleStabilizer (meetOrder R s)).relIndex (Submodule.finiteIdeleStabilizer R) = ℓ := by sorry
