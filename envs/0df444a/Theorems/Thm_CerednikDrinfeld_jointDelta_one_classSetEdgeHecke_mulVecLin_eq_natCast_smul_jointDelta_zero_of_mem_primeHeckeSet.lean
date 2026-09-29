-- Prove2me | Theorems.Thm_CerednikDrinfeld_jointDelta_one_classSetEdgeHecke_mulVecLin_eq_natCast_smul_jointDelta_zero_of_mem_primeHeckeSet
-- name    : CerednikDrinfeld.jointDelta_one_classSetEdgeHecke_mulVecLin_eq_natCast_smul_jointDelta_zero_of_mem_primeHeckeSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/c87bdb63-3274-5cb4-bd03-e590978d6899
-- title:
--   Edge Hecke operator at q: b_* U_q = q a_*
-- statement:
--   Let $N$ be a non-zero natural number and $q,q'$ primes with $q'\neq q$, $q\nmid N$ and $q'\nmid N$. Let $a,b\in\mathbb{Q}$ satisfy `IsDefiniteRamifiedExactlyAt a b q'`, i.e. $a<0$, $b<0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q'$ lies in $v$. Let $\Lambda, R\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be $\mathbb{Z}$-submodules with $\Lambda$ a maximal order, $R$ an Eichler order of level $N$ (an intersection of two maximal orders, with relative index $N$ in the first) and $R\le\Lambda$. Let $n$ be a unit of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q},f}$ such that `meetOrder R n` $=R\sqcap n R n^{-1}$ is an Eichler order of level $Nq$, and such that $n\in$ `primeHeckeSet R q`: $n$ lies in the finite adelic box of $R$, so does $q\cdot n^{-1}$, while $n^{-1}$ and $q^{-1}\cdot n$ do not. The class sets of the finite-idele stabilisers of `meetOrder R n` and of $R$ are assumed finite, the latter with decidable equality. Then for every $x:\mathrm{ClassSet}(\widehat{S}^\times)\to\mathbb{Z}$, where $S=$ `meetOrder R n`, the component $1$ of `jointDelta (classSetDegeneracyData R n)` — the push-forward along $[\,\cdot\,]\mapsto[\,\cdot\,n]$ — applied to the image of $x$ under the matrix `classSetEdgeHecke N q Λ R n ⟨q, Fact.out⟩`, which at the prime $q$ is the Hecke matrix with entries `heckeKernel` of the set `uHeckeSet R n q` of $h\in$ `primeHeckeSet S q` with $h(nRn^{-1})h^{-1}=R$ and $hRh^{-1}\neq nRn^{-1}$, equals $q$ times the component $0$ of `jointDelta (classSetDegeneracyData R n)` applied to $x$, that is $q$ times the push-forward of $x$ along the forgetful map of class sets.
--
--   This is the second of the two degeneracy relations for the Iwahori-type Hecke operator at $q$ on the Brandt module of the Eichler order $R\cap nRn^{-1}$ of level $Nq$, the counterpart of the relation expressing $b_*\circ U_q$ through $a_*$ in the level-lowering argument at $q$. It is used in [`CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet`](thm.html#CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet), where the vanishing of both degeneracy push-forwards is propagated through the edge Hecke operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_jointDelta_one_classSetEdgeHecke_mulVecLin_eq_natCast_smul_jointDelta_zero_of_mem_primeHeckeSet.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.jointDelta_one_classSetEdgeHecke_mulVecLin_eq_natCast_smul_jointDelta_zero_of_mem_primeHeckeSet
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
    jointDelta (classSetDegeneracyData R n) 1 ((classSetEdgeHecke N q Λ R n ⟨q, Fact.out⟩).mulVecLin x) =
      (q : ℤ) • jointDelta (classSetDegeneracyData R n) 0 x := by sorry
