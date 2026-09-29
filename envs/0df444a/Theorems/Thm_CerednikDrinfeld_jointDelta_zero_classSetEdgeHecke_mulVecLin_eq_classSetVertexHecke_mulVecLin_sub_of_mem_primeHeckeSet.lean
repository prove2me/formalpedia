-- Prove2me | Theorems.Thm_CerednikDrinfeld_jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet
-- name    : CerednikDrinfeld.jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/7fd40790-aaca-5cfa-9261-207dea2339f5
-- title:
--   Degeneracy relation a_*U_q=T_qa_*-b_* on class sets
-- statement:
--   Fix natural numbers $N\neq 0$ and primes $q,q'$ with $q'\neq q$, $q\nmid N$ and $q'\nmid N$, and rationals $a,b$ such that `IsDefiniteRamifiedExactlyAt a b q'` holds, i.e. $a<0$, $b<0$ and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completed algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $q$ lies in $v$. Let $\Lambda,R\subseteq\mathbb H[\mathbb Q,a,b]$ be $\mathbb Z$-submodules with $\Lambda$ a maximal order, $R$ an Eichler order of level $N$ (an intersection of two maximal orders, of relative index $N$ in the first), and $R\le\Lambda$. Let $n$ be a unit of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb A_{\mathbb Q,f}$ lying in `primeHeckeSet R q`, i.e. $n$ and $q\,n^{-1}$ lie in the finite adelic box of $R$ while $n^{-1}$ and $q^{-1}n$ do not, and assume the meet order $S=R\sqcap nRn^{-1}$ is an Eichler order of level $Nq$; the class sets of the finite-idele stabilisers of $S$ and of $R$ are assumed finite, with decidable equality for the latter. For every $x\colon \mathrm{Cl}(S)\to\mathbb Z$ the conclusion reads
--   $$a_*\big((U_q)\,x\big)=T_q\big(a_*x\big)-b_*x,$$
--   where $a_*$ and $b_*$ are the two pushforwards `jointDelta (classSetDegeneracyData R n) 0` and `… 1` attached to the degeneracy data with first map the class-set forgetting map $[x]\mapsto[x]$ from $\mathrm{Cl}(S)$ to $\mathrm{Cl}(R)$, second map $[x]\mapsto[xn]$ and weight function $[x]\mapsto \mathrm{unitWeight}$ of the conjugate of $S$ by a representative; $U_q$ is the Hecke matrix `classSetEdgeHecke N q Λ R n ⟨q,_⟩`, which at the prime $q$ is the matrix of `uHeckeSet R n q` (those $h\in$ `primeHeckeSet S q` with $h^{-1}(nRn^{-1})h=R$ and $h^{-1}Rh\neq nRn^{-1}$), and $T_q$ is `classSetVertexHecke N Λ R ⟨q,_⟩`, which since $q\nmid N$ is the matrix of `primeHeckeSet R q` on $\mathrm{Cl}(R)$.
--
--   This is the first of the two Iwahori-level degeneracy relations for Brandt modules of the Eichler order $S=R\cap nRn^{-1}$ of level $Nq$, expressing that on the Bruhat–Tits tree at $q$ the $U_q$-correspondence on edges, followed by the source-vertex map, is the $q+1$-neighbour correspondence $T_q$ minus the target-vertex map. It is used in [`CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet`](thm.html#CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet
    (N q q' : ℕ) [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hn : IsEichlerOrder (meetOrder R n) (N * q)) (hnH : n ∈ primeHeckeSet R q)
    (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ) :
    jointDelta (classSetDegeneracyData R n) 0 ((classSetEdgeHecke N q Λ R n ⟨q, Fact.out⟩).mulVecLin x) =
      (classSetVertexHecke N Λ R ⟨q, Fact.out⟩).mulVecLin (jointDelta (classSetDegeneracyData R n) 0 x) -
        jointDelta (classSetDegeneracyData R n) 1 x := by sorry
