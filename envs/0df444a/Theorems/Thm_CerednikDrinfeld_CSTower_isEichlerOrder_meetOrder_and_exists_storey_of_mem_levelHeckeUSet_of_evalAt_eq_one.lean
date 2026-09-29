-- Prove2me | Theorems.Thm_CerednikDrinfeld_CSTower_isEichlerOrder_meetOrder_and_exists_storey_of_mem_levelHeckeUSet_of_evalAt_eq_one
-- name    : CerednikDrinfeld.CSTower.isEichlerOrder_meetOrder_and_exists_storey_of_mem_levelHeckeUSet_of_evalAt_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/1e8cf630-4a4a-5d64-b627-9a6e697e64e8
-- title:
--   U_ℓ storey of the class-set tower at ℓ ∣ N
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $N,q,q'$ be natural numbers with $N$ nonzero and squarefree, $q$ and $q'$ prime, $q\nmid N$, $q'\nmid N$, $q'\neq q$ and $q'\geq 5$, and assume `IsDefiniteRamifiedExactlyAt a b q'`: $a<0$, $b<0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $q'\in v$. Let $\Lambda, R$ be $\mathbb{Z}$-submodules of $\mathbb{H}[\mathbb{Q},a,b]$ with $\Lambda$ a maximal order (an order, i.e. containing $1$, closed under multiplication, $\mathbb{Q}$-spanning and finitely generated, maximal among orders), $R$ an Eichler order of level $N$ (an intersection $\Lambda_1\cap\Lambda_2$ of two maximal orders whose additive relative index in $\Lambda_1$ is $N$), and $R\leq\Lambda$. Let $n$ be a unit of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q},f}$ lying in `primeHeckeSet R q`, i.e. $n$ lies in the finite adelic box of $R$, $q\,n^{-1}$ lies in that box while $n^{-1}$ does not, and $q^{-1}n$ does not. Assume the meet order $R\cap nRn^{-1}$ (`meetOrder R n`, the intersection of $R$ with its conjugate by $n$) is an Eichler order of level $Nq$, that $n$ normalises it, and that shifting by $n$ twice is the identity on the class set $\mathbb{H}^{\times}\backslash(\mathbb{H}\otimes\mathbb{A}_f)^{\times}/\widehat{(R\cap nRn^{-1})}^{\times}$, with the two class sets for $R\cap nRn^{-1}$ and for $R$ finite and with decidable equality. Let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ containing $q$, let $\ell$ be a prime dividing $N$, and let $s$ be a finite idelic unit such that the central idele attached to $\ell$ times $s^{-1}$ lies in `levelHeckeUSet Λ (meetOrder R n) ℓ` — that is, it lies in `primeHeckeSet (meetOrder R n) ℓ`, does not normalise $R\cap nRn^{-1}$, and does not conjugate $\Lambda$ to an order containing $R\cap nRn^{-1}$ — and such that the component of $s$ at $v$ is $1$. Then $R\cap sRs^{-1}$ is an Eichler order of level $N\ell$, and there is a finite idelic unit $n'$ with: $n'\in$ `primeHeckeSet (meetOrder R s) q`; $(R\cap sRs^{-1})\cap n'(R\cap sRs^{-1})n'^{-1}$ an Eichler order of level $N\ell q$, normalised by $n'$, with shifting by $n'$ an involution of its class set; $n^{-1}n'$ in the finite idelic stabiliser of the adelic box of $R$; $sn'=n's$; and both class sets, for $R\cap sRs^{-1}$ and for $(R\cap sRs^{-1})\cap n'(R\cap sRs^{-1})n'^{-1}$, finite.
--
--   This is the inductive step building one storey of the class-set tower attached to a definite quaternion algebra on the Čerednik–Drinfeld special fibre, in the universally quantified form where the degeneracy shift idele $s$ at a prime $\ell\mid N$ is given in advance, subject only to the oriented $U_\ell$ condition at $\ell$ and triviality at the place above $q$. It is used by the results producing quotient presentations of class sets with their Hecke and degeneracy data, and the associated permutation realisations of vertex and edge quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_CSTower_isEichlerOrder_meetOrder_and_exists_storey_of_mem_levelHeckeUSet_of_evalAt_eq_one.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CSTower.isEichlerOrder_meetOrder_and_exists_storey_of_mem_levelHeckeUSet_of_evalAt_eq_one

    {a b : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq'5 : 5 ≤ q')
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R q)
    (hS : IsEichlerOrder (meetOrder R n) (N * q))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hsq : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      classSetShift _ n (classSetShift _ n x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]

    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∣ N)
    (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      levelHeckeUSet Λ (meetOrder R n) ℓ)
    (hsv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (s : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) :
    IsEichlerOrder (meetOrder R s) (N * ℓ) ∧
    ∃ n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      n' ∈ primeHeckeSet (meetOrder R s) q ∧
      IsEichlerOrder (meetOrder (meetOrder R s) n') (N * ℓ * q) ∧
      Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') n' = meetOrder (meetOrder R s) n' ∧
      (∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')),
        classSetShift _ n' (classSetShift _ n' x) = x) ∧
      n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R ∧
      s * n' = n' * s ∧
      Finite (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s))) ∧
      Finite (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n'))) := by sorry
