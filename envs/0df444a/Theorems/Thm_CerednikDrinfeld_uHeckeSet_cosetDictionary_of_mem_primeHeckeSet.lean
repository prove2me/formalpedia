-- Prove2me | Theorems.Thm_CerednikDrinfeld_uHeckeSet_cosetDictionary_of_mem_primeHeckeSet
-- name    : CerednikDrinfeld.uHeckeSet_cosetDictionary_of_mem_primeHeckeSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/d2bb2264-f432-532d-87e1-765d42db869f
-- title:
--   Iwahori U_q-cosets versus T_q-cosets for an Eichler order
-- statement:
--   Fix rationals $a,b$ and primes $q,q'$ with $q'\neq q$, and assume $\mathbb{H}[\mathbb{Q},a,b]$ is definite and ramified exactly at $q'$ in the sense of `IsDefiniteRamifiedExactlyAt`: $a<0$, $b<0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division ring exactly when $q'\in v$. Let $R$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an Eichler order of level $N$, i.e. $R=\Lambda_1\cap\Lambda_2$ for maximal orders $\Lambda_i$ with $[\Lambda_1:R]=N$, and assume $q\nmid N$. Let $n$ be a unit of $\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{A}_f$ lying in `primeHeckeSet R q`, that is $n\in\widehat R$, $qn^{-1}\in\widehat R$, $n^{-1}\notin\widehat R$ and $q^{-1}n\notin\widehat R$, where $\widehat R$ denotes [`Submodule.finiteAdeleBox R`](def/Submodule_FiniteAdeleBox.html#L14). Write $S=R\cap n\widehat Rn^{-1}$ for `meetOrder R n`, $U_\Lambda$ for the stabiliser of $\widehat\Lambda$ in the idelic unit group, and $\mathcal{U}$ for `uHeckeSet R n q`, the set of $h\in$ `primeHeckeSet S q` with $(hn)\widehat R(hn)^{-1}\cap\mathbb{H}=R$ and $h\widehat Rh^{-1}\cap\mathbb{H}\neq n\widehat Rn^{-1}\cap\mathbb{H}$. The conclusion is fivefold: $U_S\le U_R$; $\mathcal{U}\subseteq$ `primeHeckeSet R q`; $h^{-1}n\notin U_R$ for all $h\in\mathcal{U}$; for $h,h'\in\mathcal{U}$, $h^{-1}h'\in U_R$ implies $h^{-1}h'\in U_S$; and every $g\in$ `primeHeckeSet R q` with $g^{-1}n\notin U_R$ satisfies $g^{-1}h\in U_R$ for some $h\in\mathcal{U}$.
--
--   Together the five assertions say that $hU_S\mapsto hU_R$ is a well-defined injection from the $U_S$-cosets in the Iwahori Hecke set of the pair $(R,n)$ at $q$ onto the $U_R$-cosets in the Hecke set of $R$ at $q$ other than $nU_R$; on the Bruhat–Tits tree of $\mathrm{GL}_2(\mathbb{Q}_q)$ this is the statement that the $q$ edges produced at Iwahori level match the neighbours of the vertex $R_q$ other than $n_qR_qn_q^{-1}$. It is the counting input for the degeneracy relation between $U_q$ and $T_q$ on Brandt modules, and is used by [`CerednikDrinfeld.uHeckeSet_cosets_eq_finiteIdeleStabilizer_mul_of_conjByFiniteIdele_meetOrder_eq`](thm.html#CerednikDrinfeld.uHeckeSet_cosets_eq_finiteIdeleStabilizer_mul_of_conjByFiniteIdele_meetOrder_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_uHeckeSet_cosetDictionary_of_mem_primeHeckeSet.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.uHeckeSet_cosetDictionary_of_mem_primeHeckeSet
    {a b : ℚ} (q q' : ℕ) [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (hR : IsEichlerOrder R N) (hqN : ¬ q ∣ N)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hnH : n ∈ primeHeckeSet R q) :
    Submodule.finiteIdeleStabilizer (meetOrder R n) ≤ Submodule.finiteIdeleStabilizer R ∧
    uHeckeSet R n q ⊆ primeHeckeSet R q ∧
    (∀ h ∈ uHeckeSet R n q, h⁻¹ * n ∉ Submodule.finiteIdeleStabilizer R) ∧
    (∀ h ∈ uHeckeSet R n q, ∀ h' ∈ uHeckeSet R n q,
      h⁻¹ * h' ∈ Submodule.finiteIdeleStabilizer R →
        h⁻¹ * h' ∈ Submodule.finiteIdeleStabilizer (meetOrder R n)) ∧
    (∀ g ∈ primeHeckeSet R q, g⁻¹ * n ∉ Submodule.finiteIdeleStabilizer R →
      ∃ h ∈ uHeckeSet R n q, g⁻¹ * h ∈ Submodule.finiteIdeleStabilizer R) := by sorry
