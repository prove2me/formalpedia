-- Prove2me | Theorems.Thm_CerednikDrinfeld_CSTower_exists_finiteIdeleDiagonal_mul_inv_mem_levelHeckeUSet_meetOrder_isEichlerOrder_of_dvd
-- name    : CerednikDrinfeld.CSTower.exists_finiteIdeleDiagonal_mul_inv_mem_levelHeckeUSet_meetOrder_isEichlerOrder_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/4b567df8-380e-5037-9fec-6139443dd6b9
-- title:
--   Level-raising idele at a prime ℓ dividing N
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\mathbb{H}=\mathbb{H}[\mathbb{Q},a,b]$. Let $N$ be a nonzero squarefree natural number and $q,q'$ primes with $q\nmid N$, $q'\nmid N$ and $q'\neq q$, and assume `IsDefiniteRamifiedExactlyAt a b q'`: $a<0$, $b<0$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) precisely when $q'\in v$. Let $\Lambda,R$ be $\mathbb{Z}$-submodules of $\mathbb{H}$ with $\Lambda$ a maximal order (an order: containing $1$, closed under multiplication, $\mathbb{Q}$-spanning $\mathbb{H}$, finitely generated; and maximal among orders), $R$ an Eichler order of level $N$, i.e. $R=\Lambda_1\sqcap\Lambda_2$ for maximal orders $\Lambda_1,\Lambda_2$ with relative index $[\Lambda_1:R]=N$ of additive groups, and $R\le\Lambda$. Let $n$ be a unit of $\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ in `primeHeckeSet R q`, that is: $n$ lies in the finite adelic box $\widehat R$, $q\cdot n^{-1}$ lies in $\widehat R$, while $n^{-1}\notin\widehat R$ and $q^{-1}n\notin\widehat R$. Let $\ell$ be a prime dividing $N$, and put $S=R\sqcap(\mathbb{H}\cap n\widehat Rn^{-1})$, the `meetOrder` of $R$ at $n$. The conclusion asserts the existence of a unit $s$ of $\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ such that: (i) the component of $s$ at every height-one prime $v$ with $\ell\notin v$ equals $1$; (ii) $\hat\ell\,s^{-1}$, where $\hat\ell$ is the diagonal image of the scalar $\ell\in\mathbb{Q}^{\times}$ in $(\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}})^{\times}$, lies in `levelHeckeUSet` $\Lambda\,S\,\ell$, i.e. it belongs to `primeHeckeSet S ℓ`, does not conjugate $\widehat S$ to itself, and $S$ is not contained in $\mathbb{H}\cap \hat\ell s^{-1}\widehat\Lambda s\hat\ell^{-1}$; and (iii) $R\sqcap(\mathbb{H}\cap s\widehat Rs^{-1})$ is an Eichler order of level $N\ell$.
--
--   This is the existence step, at a prime $\ell$ dividing the level, used to raise the level of the Eichler order in the Čerednik–Drinfel'd class-set tower: it produces a finite idele supported at $\ell$ which plays the role of an Iwahori double-coset representative of degree $\ell$ oriented by the maximal order $\Lambda$. It is cited by [`CerednikDrinfeld.exists_units_finiteIdele_levelHeckeUSet_meetOrder_eq_tmul_one_of_dvd`](thm.html#CerednikDrinfeld.exists_units_finiteIdele_levelHeckeUSet_meetOrder_eq_tmul_one_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_CSTower_exists_finiteIdeleDiagonal_mul_inv_mem_levelHeckeUSet_meetOrder_isEichlerOrder_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CSTower.exists_finiteIdeleDiagonal_mul_inv_mem_levelHeckeUSet_meetOrder_isEichlerOrder_of_dvd
    {a b : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∣ N) :
    ∃ s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (s : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
        levelHeckeUSet Λ (meetOrder R n) ℓ ∧
      IsEichlerOrder (meetOrder R s) (N * ℓ) := by sorry
