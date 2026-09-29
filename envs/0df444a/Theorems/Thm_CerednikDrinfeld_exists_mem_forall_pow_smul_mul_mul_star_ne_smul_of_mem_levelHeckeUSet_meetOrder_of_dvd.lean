-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_mem_forall_pow_smul_mul_mul_star_ne_smul_of_mem_levelHeckeUSet_meetOrder_of_dvd
-- name    : CerednikDrinfeld.exists_mem_forall_pow_smul_mul_mul_star_ne_smul_of_mem_levelHeckeUSet_meetOrder_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/49ea88b2-8f4c-540d-bdd9-66f22a85114f
-- title:
--   Orientation clause of U_ℓ forces sR₁s⁻¹not⊆Λ₁[1/r]
-- statement:
--   Fix primes $r$, $\bar r$ and a nonzero natural number $N$, rationals $a_1,b_1$, and work in the quaternion algebra $H=\mathbb{H}[\mathbb{Q},a_1,b_1]$. Let $\Lambda_1,R_1$ be $\mathbb{Z}$-submodules of $H$ with $\Lambda_1$ a maximal order (an order in the sense of containing $1$, closed under multiplication, spanning $H$ over $\mathbb{Q}$ and finitely generated, and maximal among orders containing it) and $R_1$ an Eichler order of level $N$, i.e. $R_1=\Lambda'\cap\Lambda''$ for maximal orders $\Lambda',\Lambda''$ with relative index $N$ of $R_1$ in $\Lambda'$; assume $R_1\le\Lambda_1$. Let $n_1$ be a unit of $H\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q},f}$ lying in `primeHeckeSet R₁ r` (that is, $n_1$ lies in the finite adelic box of $R_1$, $r\cdot n_1^{-1}$ lies in that box, while $n_1^{-1}$ and $r^{-1}n_1$ do not), and assume $S_1:=R_1\cap\operatorname{conj}(R_1,n_1)$, the meet order `meetOrder R₁ n₁`, is an Eichler order of level $Nr$. Let $\ell$ be a prime distinct from $r$ and $\bar r$, let $s\in H^\times$ and let $s_f$ be a unit of $H\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q},f}$ such that: the component of $s_f$ at every finite place $u$ of $\mathbb{Q}$ with $r\notin u$ equals $s\otimes 1$; the component at every $u$ with $r\in u$ equals $1$; the element $(\ell\otimes 1)\,s_f^{-1}$, with $\ell$ the diagonal finite idele image of the scalar $\ell\in\mathbb{Q}^\times\subseteq H^\times$, lies in `levelHeckeUSet Λ₁ S₁ ℓ` when $\ell\mid N$ and in `primeHeckeSet S₁ ℓ` otherwise; and $\mathrm{nrd}(s)=\ell$. Assume finally $\ell\mid N$, so that the third condition reads: $(\ell\otimes 1)s_f^{-1}$ lies in the prime Hecke set of $S_1$ at $\ell$, does not stabilise $S_1$ under adelic conjugation, and $S_1\not\le\operatorname{conj}(\Lambda_1,(\ell\otimes 1)s_f^{-1})$. The conclusion is that there exists $z\in R_1$ such that for every $c\in\mathbb{N}$ and every $y\in\Lambda_1$ one has $r^c\cdot(s\,z\,\bar s)\ne\ell\cdot y$ in $H$, where $\bar s$ is the quaternion conjugate of $s$.
--
--   This is the global reading of the orientation clause in the definition of the level-$\ell$ Hecke set attached to an Eichler order at a prime $\ell$ dividing its level (the Atkin–Lehner–Eichler $U_\ell$ situation): since $s\bar s=\mathrm{nrd}(s)=\ell$, the conclusion says that $sR_1s^{-1}$ is not contained in $\Lambda_1\otimes\mathbb{Z}[1/r]$. It is used in the Čerednik–Drinfel'd uniformisation frame, by [`CerednikDrinfeld.CosetGraph.mem_map_conj_of_mem_awayUnits_of_exists_pow_smul_star_mul_mul_eq_smul`](thm.html#CerednikDrinfeld.CosetGraph.mem_map_conj_of_mem_awayUnits_of_exists_pow_smul_star_mul_mul_eq_smul) and by [`CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_nsmulPt_eq_one_mapPt_eq_one_imp_eq_one_of_levelHeckeUSet_of_endIsoFull`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_nsmulPt_eq_one_mapPt_eq_one_imp_eq_one_of_levelHeckeUSet_of_endIsoFull).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_mem_forall_pow_smul_mul_mul_star_ne_smul_of_mem_levelHeckeUSet_meetOrder_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.exists_mem_forall_pow_smul_mul_mul_star_ne_smul_of_mem_levelHeckeUSet_meetOrder_of_dvd
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N]
    {a₁ b₁ : ℚ}
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * r))
    (ℓ : HeckeTower.AwayPrime r rbar) (s : (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs :
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * sf⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (hℓN : (ℓ.1 : ℕ) ∣ N) :
    ∃ z : ℍ[ℚ, a₁, b₁], z ∈ R₁ ∧ ∀ (c : ℕ) (y : ℍ[ℚ, a₁, b₁]), y ∈ Λ₁ →
      ((r ^ c : ℕ) : ℚ) • ((s : ℍ[ℚ, a₁, b₁]) * z * star (s : ℍ[ℚ, a₁, b₁])) ≠ ((ℓ.1 : ℕ) : ℚ) • y := by sorry
