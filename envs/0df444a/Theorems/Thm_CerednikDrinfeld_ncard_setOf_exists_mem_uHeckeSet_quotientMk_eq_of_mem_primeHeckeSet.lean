-- Prove2me | Theorems.Thm_CerednikDrinfeld_ncard_setOf_exists_mem_uHeckeSet_quotientMk_eq_of_mem_primeHeckeSet
-- name    : CerednikDrinfeld.ncard_setOf_exists_mem_uHeckeSet_quotientMk_eq_of_mem_primeHeckeSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/1d5ca263-8e5a-5074-82f2-6b6e870e5fc5
-- title:
--   Iwahori Hecke set meets exactly q cosets
-- statement:
--   Fix natural numbers $N \neq 0$ and primes $q \neq q'$ with $q \nmid N$ and $q' \nmid N$, and rationals $a,b$ such that the quaternion algebra $\mathbb{H} = \mathbb{H}[\mathbb{Q},a,b]$ satisfies $a<0$, $b<0$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H} \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $q'$ lies in $v$. Let $\Lambda, R$ be $\mathbb{Z}$-submodules of $\mathbb{H}$ with $R \le \Lambda$, where $\Lambda$ is a maximal order (an order being a finitely generated submodule containing $1$, closed under multiplication and spanning $\mathbb{H}$ over $\mathbb{Q}$, maximal among orders containing it) and $R$ is Eichler of level $N$, i.e. $R = \Lambda_1 \sqcap \Lambda_2$ for maximal orders $\Lambda_i$ with relative index $N$ of $R$ in $\Lambda_1$. Let $n$ be a unit of $\mathbb{H} \otimes_{\mathbb{Q}} \mathbb{A}_{\mathbb{Q},\mathrm{fin}}$ lying in `primeHeckeSet R q`, so that $n$ lies in the adelic box of $R$, $q\,n^{-1}$ lies in that box, while $n^{-1}$ and $q^{-1}n$ do not; assume moreover that $S := R \sqcap nRn^{-1}$ (the submodule `meetOrder R n`) is Eichler of level $Nq$. Then, in the quotient of the unit group by the stabiliser of the adelic box of $S$, the set of classes represented by some $h$ in `uHeckeSet R n q` — that is, $h \in$ `primeHeckeSet S q` with $h(nRn^{-1})h^{-1} = R$ and $hRh^{-1} \neq nRn^{-1}$ — has cardinality exactly $q$.
--
--   This is the exact count underlying the edge Hecke operator on the Čerednik–Drinfeld class set graph attached to an Eichler order of level $N$ in a definite quaternion algebra: the Iwahori Hecke set at $q$ splits into precisely $q$ cosets of the idelic stabiliser of the level-$Nq$ order, matching the $q$ neighbours of a vertex of the Bruhat–Tits tree of $\mathrm{GL}_2(\mathbb{Q}_q)$ other than the given one. It feeds the computation of the action of the edge Hecke operator on the joint delta classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_ncard_setOf_exists_mem_uHeckeSet_quotientMk_eq_of_mem_primeHeckeSet.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.ncard_setOf_exists_mem_uHeckeSet_quotientMk_eq_of_mem_primeHeckeSet
    (N q q' : ℕ) [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hn : IsEichlerOrder (meetOrder R n) (N * q)) (hnH : n ∈ primeHeckeSet R q) :
    Set.ncard {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer (meetOrder R n) |
        ∃ h ∈ uHeckeSet R n q, (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer (meetOrder R n)) = c} = q := by sorry
