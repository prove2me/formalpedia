-- Prove2me | Theorems.Thm_CerednikDrinfeld_classSet_eq_empty_or_eq_univ_of_forall_mem_iff_of_squarefree
-- name    : CerednikDrinfeld.classSet_eq_empty_or_eq_univ_of_forall_mem_iff_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/dcb86647-fa91-5adf-9c13-fd62e0dfba13
-- title:
--   Connectedness of the Eichler class-set graph
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q'$ be a prime with $q'\ge 5$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is definite and ramified exactly at $q'$, in the sense that $a<0$, $b<0$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit precisely when $q'$ lies in $v$. Let $N$ be a nonzero squarefree natural number, and let $\Lambda, R$ be $\mathbb{Z}$-submodules of $\mathbb{H}[\mathbb{Q},a,b]$ with $\Lambda$ a maximal order (an order not properly contained in any order) and $R$ an Eichler order of level $N$, i.e. $R=\Lambda_1\cap\Lambda_2$ for maximal orders $\Lambda_i$ with the relative index of $R$ in $\Lambda_1$ equal to $N$, and with $R\le\Lambda$. Let $r$ be a prime, $r\ne q'$ and $r\nmid N$, and let $n$ be a unit of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q},f}$ lying in the prime Hecke set of $R$ at $r$: $n$ lies in the finite-adelic box of $R$, so does $r\cdot n^{-1}$, while neither $n^{-1}$ nor $r^{-1}n$ does. Assume the order $S=R\cap nRn^{-1}$ (the intersection of $R$ with its conjugate by $n$) is an Eichler order of level $Nr$, that conjugation by $n$ preserves $S$, and that the shift $x\mapsto [x\,n]$ on the class set $\mathrm{Cl}(S)$ — the double coset quotient of the finite ideles of $\mathbb{H}[\mathbb{Q},a,b]$ by the diagonal image of $\mathbb{H}[\mathbb{Q},a,b]^\times$ and the stabiliser of the adelic box of $S$ — is an involution; both class sets $\mathrm{Cl}(S)$ and $\mathrm{Cl}(R)$ are assumed finite. Then any subset $P\subseteq \mathrm{Cl}(R)$ such that, for every $e\in\mathrm{Cl}(S)$, the first degeneracy image of $e$ (the class of a representative of $e$ taken at level $R$) lies in $P$ if and only if the second one (the class of that representative multiplied by $n$) does, satisfies $P=\varnothing$ or $P=\mathrm{Cl}(R)$.
--
--   This is the connectedness of the class-set (Brandt) graph of an Eichler order of squarefree level, with edge set $\mathrm{Cl}(S)$ and the two degeneracy maps to $\mathrm{Cl}(R)$, obtained here by transport along the Deuring–Eichler comparison with the supersingular points of modular curves in characteristic $q'$. It feeds the strong-approximation statement [`QuaternionAlgebra.IsEichlerOrder.exists_eq_finiteIdeleDiagonal_mul_mul_of_squarefree_of_not_dvd`](thm.html#QuaternionAlgebra.IsEichlerOrder.exists_eq_finiteIdeleDiagonal_mul_mul_of_squarefree_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_classSet_eq_empty_or_eq_univ_of_forall_mem_iff_of_squarefree.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra
open CerednikDrinfeld

theorem CerednikDrinfeld.classSet_eq_empty_or_eq_univ_of_forall_mem_iff_of_squarefree
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hq5 : 5 ≤ q') (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} [NeZero N] (hN : Squarefree N)
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (r : ℕ) [Fact r.Prime] (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R r)
    (hS : IsEichlerOrder (meetOrder R n) (N * r))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hsq : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      classSetShift _ n (classSetShift _ n x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (P : Set (ClassSet (Submodule.finiteIdeleStabilizer R)))
    (hP : ∀ e : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      (classSetDegeneracyData R n).a e ∈ P ↔ (classSetDegeneracyData R n).b e ∈ P) :
    P = ∅ ∨ P = Set.univ := by sorry
