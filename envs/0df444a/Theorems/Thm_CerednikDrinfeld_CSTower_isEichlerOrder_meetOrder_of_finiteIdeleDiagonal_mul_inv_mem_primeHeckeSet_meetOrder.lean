-- Prove2me | Theorems.Thm_CerednikDrinfeld_CSTower_isEichlerOrder_meetOrder_of_finiteIdeleDiagonal_mul_inv_mem_primeHeckeSet_meetOrder
-- name    : CerednikDrinfeld.CSTower.isEichlerOrder_meetOrder_of_finiteIdeleDiagonal_mul_inv_mem_primeHeckeSet_meetOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/7a2a0e64-f659-50a6-8c07-f42d91fc9cad
-- title:
--   Meet order at an admissible T_ℓ-shift is Eichler of level Nℓ
-- statement:
--   Fix rationals $a,b$ and natural numbers $N,q,q'$ with $N$ nonzero and $q,q'$ prime, and assume `IsDefiniteRamifiedExactlyAt a b q'`, i.e. $a<0$, $b<0$ and, for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$, the completed algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all its nonzero elements invertible precisely when $q'\in v$. Let $R$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q,a,b]$ that is Eichler of level $N$, meaning $R=\Lambda_1\cap\Lambda_2$ for two maximal orders with relative index $[\Lambda_1:R]=N$. Let $n$ be a unit of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb A_{\mathbb Q,f}$ such that the meet order $R\cap(\mathbb H\cap n\widehat R n^{-1})$ — the submodule of elements of $R$ whose diagonal image lies in $n\,\widehat R\,n^{-1}$, $\widehat R$ being the finite adelic box of $R$ — is Eichler of level $Nq$. Let $\ell$ be a prime with $\ell\nmid Nqq'$ and let $s$ be a further finite idèle such that, writing $\hat\ell$ for the central idèle attached to $\ell$ and $h=\hat\ell\,s^{-1}$, one has $h\in\widehat S$, $\ell h^{-1}\in\widehat S$, $h^{-1}\notin\widehat S$ and $\ell^{-1}h\notin\widehat S$, where $S$ is the meet order attached to $n$. The conclusion is that $R\cap(\mathbb H\cap s\widehat R s^{-1})$ is an Eichler order of level $N\ell$.
--
--   This is the level-raising step for the class-set (Brandt) tower of a definite rational quaternion algebra: any shift idèle $s$ whose dual $\hat\ell s^{-1}$ lies in the $T_\ell$ Hecke set of the edge order produces an Eichler order of level $N\ell$, with no assumption that $s$ be supported at $\ell$. It is used by the storey-existence statement for the tower and by the computations of arrow degrees for the Hecke correspondence on the associated coset graphs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_CSTower_isEichlerOrder_meetOrder_of_finiteIdeleDiagonal_mul_inv_mem_primeHeckeSet_meetOrder.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CSTower.isEichlerOrder_meetOrder_of_finiteIdeleDiagonal_mul_inv_mem_primeHeckeSet_meetOrder
    {a b : ℚ} {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsEichlerOrder R N)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hS : IsEichlerOrder (meetOrder R n) (N * q))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N * q * q')
    (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      primeHeckeSet (meetOrder R n) ℓ) :
    IsEichlerOrder (meetOrder R s) (N * ℓ) := by sorry
