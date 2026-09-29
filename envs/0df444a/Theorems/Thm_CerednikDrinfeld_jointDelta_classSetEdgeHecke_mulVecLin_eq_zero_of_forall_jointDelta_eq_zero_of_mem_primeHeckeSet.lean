-- Prove2me | Theorems.Thm_CerednikDrinfeld_jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet
-- name    : CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/2b21c1d9-6143-5c4d-8438-8f0b09cf77dc
-- title:
--   U_q preserves the joint kernel of the class-set degeneracy maps
-- statement:
--   Let $N$, $q$, $q'$ be natural numbers with $N \neq 0$ and $q$, $q'$ prime, and suppose $q' \neq q$, $q \nmid N$, $q' \nmid N$. Let $a, b \in \mathbb{Q}$ satisfy `IsDefiniteRamifiedExactlyAt a b q'`, i.e. $a < 0$, $b < 0$ and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division ring exactly when $q' \in v$. Let $\Lambda, R$ be $\mathbb{Z}$-submodules of $\mathbb{H}[\mathbb{Q},a,b]$ with $\Lambda$ a maximal order (an order not properly contained in another order), $R$ an Eichler order of level $N$ (an intersection $\Lambda_1 \cap \Lambda_2$ of two maximal orders of relative index $N$ in $\Lambda_1$), and $R \le \Lambda$. Let $n$ be a unit of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{A}_{\mathbb{Q},f}$ lying in `primeHeckeSet R q`, so that $n$ and $q n^{-1}$ lie in the adelic box of $R$ while $n^{-1}$ and $q^{-1}n$ do not, and assume `meetOrder R n` $= R \cap nRn^{-1}$ is an Eichler order of level $Nq$; the class sets of the finite-idele stabilisers of `meetOrder R n` and of $R$ are assumed finite. Write $a_*$ and $b_*$ for the two pushforwards attached to `classSetDegeneracyData R n`, namely those along the forgetful map $[x] \mapsto [x]$ and along $[x] \mapsto [xn]$ from the class set of `meetOrder R n` to that of $R$, these being the two components of `jointDelta`. Then for every $x : \mathrm{Cl}(\mathrm{meetOrder}\,R\,n) \to \mathbb{Z}$ with $a_*(x) = b_*(x) = 0$ and every $i \in \mathrm{Fin}\,2$, the $i$-th pushforward of $(\mathrm{classSetEdgeHecke}\ N\ q\ \Lambda\ R\ n\ \langle q, \cdot\rangle) \cdot x$ vanishes, where the matrix in question is, at the prime $q$ itself, the Hecke matrix of the set `uHeckeSet R n q` of ideles $h \in$ `primeHeckeSet (meetOrder R n) q` with $h^{-1}(nRn^{-1})h = R$ and $h^{-1}Rh \neq nRn^{-1}$.
--
--   This is the case $\ell = q$ of the kernel-stability law for the degeneracy datum of the pair of Eichler orders $R \cap nRn^{-1} \subseteq R$: the Iwahori operator at $q$ preserves the joint kernel of the two degeneracy pushforwards, i.e. the $q$-new part of the Brandt module of the level-$Nq$ order. It feeds into [`CerednikDrinfeld.classSetHeckeLaws_of_isEichlerOrder_meetOrder`](thm.html#CerednikDrinfeld.classSetHeckeLaws_of_isEichlerOrder_meetOrder), which collects the Hecke laws of the class-set degeneracy datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_zero_of_forall_jointDelta_eq_zero_of_mem_primeHeckeSet
    (N q q' : ℕ) [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hn : IsEichlerOrder (meetOrder R n) (N * q)) (hnH : n ∈ primeHeckeSet R q)
    (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ)
    (hx : ∀ i, jointDelta (classSetDegeneracyData R n) i x = 0) (i : Fin 2) :
    jointDelta (classSetDegeneracyData R n) i
      ((classSetEdgeHecke N q Λ R n ⟨q, Fact.out⟩).mulVecLin x) = 0 := by sorry
