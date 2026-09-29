-- Prove2me | Theorems.Thm_CerednikDrinfeld_uHeckeSet_quotient_bijOn_primeHeckeSet_quotient_diff_of_prime
-- name    : CerednikDrinfeld.uHeckeSet_quotient_bijOn_primeHeckeSet_quotient_diff_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/3e170412-12df-5445-9e78-39fcc1625af0
-- title:
--   Iwahori cosets at q biject with Hecke cosets avoiding n
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $R$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a prime $q$, and a unit $n$ of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ (the finite adele ring of $\mathbb{Q}$). Assume: `IsEichlerOrder R N`, i.e. $R=\Lambda_1\cap\Lambda_2$ for maximal orders $\Lambda_1,\Lambda_2$ with relative index $[\Lambda_1:R]=N$; $q\nmid N$; a prime $q'\neq q$ with `IsDefiniteRamifiedExactlyAt a b q'`, i.e. $a<0$, $b<0$ and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q'\in v$; that $n$ lies in the Hecke set of $R$ at $q$, meaning $n$ lies in the finite adele box $\widehat{R}$ of $R$, $q\,n^{-1}\in\widehat{R}$, $n^{-1}\notin\widehat{R}$ and $q^{-1}n\notin\widehat{R}$; and that `meetOrder R n` $=R\cap nRn^{-1}$ (intersection of $R$ with the conjugate submodule [`Submodule.conjByFiniteIdele R n`](def/Submodule_FiniteAdeleBox.html#L31)) is an Eichler order of level $Nq$. Write $U_R$, $U_S$ for the stabilisers in the unit group of the boxes of $R$ and of $R\cap nRn^{-1}$, and let $\mathcal{U}$ be the set of units $h$ lying in the Hecke set of $R\cap nRn^{-1}$ at $q$ with $h(nRn^{-1})h^{-1}=R$ and $hRh^{-1}\neq nRn^{-1}$. The conclusion is the conjunction of: (i) for $h,h'\in\mathcal{U}$, $hU_R=h'U_R$ implies $hU_S=h'U_S$; (ii) every $g$ in the Hecke set of $R$ at $q$ with $gU_R\neq nU_R$ satisfies $gU_R=hU_R$ for some $h\in\mathcal{U}$; (iii) $hU_R\neq nU_R$ for every $h\in\mathcal{U}$.
--
--   Together the three clauses express that $h\mapsto hU_R$ induces a bijection from $\mathcal{U}U_S/U_S$ onto the set of $U_R$-cosets in the Hecke set of $R$ at $q$ other than $nU_R$; in the lattice picture at $q$ this is the statement that the index-$q$ sublattices of $L_0$ other than $nL_0$ correspond to the Iwahori Hecke set attached to the edge $(L_0,nL_0)$ of the Bruhat–Tits tree. It is the local input for the edge–vertex relation between the Hecke operators on the class-set graph, used in [`CerednikDrinfeld.jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet`](thm.html#CerednikDrinfeld.jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_uHeckeSet_quotient_bijOn_primeHeckeSet_quotient_diff_of_prime.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.uHeckeSet_quotient_bijOn_primeHeckeSet_quotient_diff_of_prime
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (q : ℕ) [Fact q.Prime]
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hR : IsEichlerOrder R N) (hqN : ¬ q ∣ N) {q' : ℕ} [Fact q'.Prime] (hqq' : q' ≠ q)
    (hdef : IsDefiniteRamifiedExactlyAt a b q') (hnH : n ∈ primeHeckeSet R q)
    (hn : IsEichlerOrder (meetOrder R n) (N * q)) :
    (∀ h ∈ uHeckeSet R n q, ∀ h' ∈ uHeckeSet R n q,
        (QuotientGroup.mk h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer R) =
            QuotientGroup.mk h' →
          (QuotientGroup.mk h :
              (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer (meetOrder R n)) =
            QuotientGroup.mk h') ∧
      (∀ g ∈ primeHeckeSet R q,
        (QuotientGroup.mk g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer R) ≠
            QuotientGroup.mk n →
          ∃ h ∈ uHeckeSet R n q,
            (QuotientGroup.mk h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer R) =
              QuotientGroup.mk g) ∧
      (∀ h ∈ uHeckeSet R n q,
        (QuotientGroup.mk h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer R) ≠
          QuotientGroup.mk n) := by sorry
