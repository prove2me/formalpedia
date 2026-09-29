-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq
-- name    : CerednikDrinfeld.exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/472184bd-689b-5f84-b559-baa8b3b9cdec
-- title:
--   Atkin–Lehner rigidity at a split Hecke prime
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $R$ be a $\mathbb{Z}$-submodule of $\mathbb{H}=\mathbb{H}[\mathbb{Q},a,b]$, let $N\in\mathbb{N}$, let $q$ and $q'$ be primes with $q'\neq q$, and let $n$ be a unit of $\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$, where $\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}=$ `FiniteAdeleRing (𝓞 ℚ) ℚ`. Assume: $R$ is an Eichler order of level $N$, i.e. $R=\Lambda_1\sqcap\Lambda_2$ for maximal orders $\Lambda_1,\Lambda_2$ of $\mathbb{H}$ with the relative index of $R$ in $\Lambda_1$ equal to $N$; $q\nmid N$; $a<0$, $b<0$ and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q'\in v$; $n$ lies in the Hecke set of $R$ at $q$, i.e. $n$ lies in the finite adèle box $\widehat{R}$ of $R$, $q\cdot n^{-1}\in\widehat{R}$, while $n^{-1}\notin\widehat{R}$ and $q^{-1}n\notin\widehat{R}$; the meet order $S=R\sqcap(\mathbb{H}\cap n\widehat{R}n^{-1})$ is an Eichler order of level $Nq$; and $\mathbb{H}\cap n\widehat{S}n^{-1}=S$. Then, writing $U_S$ and $U_R$ for the stabilisers of the boxes $\widehat{S}$, $\widehat{R}$ in the unit group, (i) there is $u\in U_S$ with $n^2=\hat{q}\,u$, where $\hat q$ is the diagonal image of the scalar unit $q\in\mathbb{H}^{\times}$; and (ii) for every $u\in U_R$, if $\mathbb{H}\cap(un)\widehat{R}(un)^{-1}=\mathbb{H}\cap n\widehat{R}n^{-1}$ then $u\in U_S$.
--
--   This is the Atkin–Lehner rigidity statement underlying the Čerednik–Drinfeld coset-graph picture: at the split prime $q$ the element $n$ swaps the two maximal orders containing the Iwahori-type order $S$, its square is the central idèle $q$ up to $U_S$, and only elements of $U_S$ can fix the conjugated order. It is used in the construction and identification of the quotient graph attached to the class sets of $R$ and $S$, in particular by the lemmas producing an equivalence of the edge and vertex class sets with the quotient of the Bruhat–Tits tree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (q : ℕ) [Fact q.Prime]
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hR : IsEichlerOrder R N) (hqN : ¬ q ∣ N) {q' : ℕ} [Fact q'.Prime] (hqq' : q' ≠ q)
    (hdef : IsDefiniteRamifiedExactlyAt a b q') (hnH : n ∈ primeHeckeSet R q)
    (hn : IsEichlerOrder (meetOrder R n) (N * q))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n) :
    (∃ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n),
        n * n = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) * u) ∧
    (∀ u ∈ Submodule.finiteIdeleStabilizer R,
        Submodule.conjByFiniteIdele R (u * n) = Submodule.conjByFiniteIdele R n →
          u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n)) := by sorry
