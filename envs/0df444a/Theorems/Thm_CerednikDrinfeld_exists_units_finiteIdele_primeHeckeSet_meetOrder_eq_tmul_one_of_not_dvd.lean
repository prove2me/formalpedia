-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd
-- name    : CerednikDrinfeld.exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/f01888aa-01d5-5af8-91eb-cb772f291712
-- title:
--   Global quaternion of reduced norm ℓ away from q
-- statement:
--   Fix $a,b\in\mathbb Q$ and natural numbers $N\neq 0$ and primes $q,q'$ with $q'\neq q$ and $q'\ge 5$, and assume $\mathrm{IsDefiniteRamifiedExactlyAt}\ a\ b\ q'$, i.e. $a<0$, $b<0$ and, for every finite place $v$ of $\mathbb Q$, the algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $q'$ lies in the prime ideal of $v$. Let $R$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q,a,b]$ which is Eichler of level $N$, meaning $R=\Lambda_1\cap\Lambda_2$ for two maximal orders with $[\Lambda_1:R]=N$. Let $n$ be a unit of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\widehat{\mathbb Q}$ (finite adeles of $\mathbb Q$) lying in `primeHeckeSet R q`, i.e. $n$ lies in the adelic box $\widehat R$ of $R$, $q\,n^{-1}\in\widehat R$, while $n^{-1}\notin\widehat R$ and $q^{-1}n\notin\widehat R$; assume further that $\mathrm{meetOrder}\ R\ n=R\cap\mathrm{conjByFiniteIdele}\ R\ n$ is Eichler of level $Nq$. Let $\ell$ be a prime not dividing $Nqq'$. Then there are a unit $s$ of $\mathbb H[\mathbb Q,a,b]$ and a finite-adelic unit $s^\flat$ such that the component of $s^\flat$ at every place $w$ with $q\notin w$ equals $s\otimes 1$, its component at every $w$ containing $q$ equals $1$, the product of the diagonal finite idele attached to $\ell\in\mathbb Q^\times$ (pushed into $\mathbb H[\mathbb Q,a,b]^\times$) with $(s^\flat)^{-1}$ lies in `primeHeckeSet (meetOrder R n) ℓ`, and $\mathrm{nrd}(s)=\ell$.
--
--   This produces the level-$\ell$ Hecke datum for the Čerednik–Drinfeld class-set tower attached to the pair $(R,\mathrm{meetOrder}\ R\ n)$ in a form coming from a single global quaternion of reduced norm $\ell$, whose adelic avatar is allowed to be modified only at the places above $q$. It feeds the construction of the Shimura-curve model together with its Hecke tower and interchange data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_LocalBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.exists_units_finiteIdele_primeHeckeSet_meetOrder_eq_tmul_one_of_not_dvd
    {a b : ℚ} {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hq'5 : 5 ≤ q') (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)
    (hS : IsEichlerOrder (meetOrder R n) (N * q))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N * q * q') :
    ∃ (s : (ℍ[ℚ, a, b])ˣ) (sf : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (sf : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (sf : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * sf⁻¹ ∈
        primeHeckeSet (meetOrder R n) ℓ ∧
      QuaternionAlgebra.nrd (s : ℍ[ℚ, a, b]) = (ℓ : ℚ) := by sorry
