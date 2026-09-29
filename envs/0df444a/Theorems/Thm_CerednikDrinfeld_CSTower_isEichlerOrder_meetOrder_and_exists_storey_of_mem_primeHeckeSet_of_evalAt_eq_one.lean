-- Prove2me | Theorems.Thm_CerednikDrinfeld_CSTower_isEichlerOrder_meetOrder_and_exists_storey_of_mem_primeHeckeSet_of_evalAt_eq_one
-- name    : CerednikDrinfeld.CSTower.isEichlerOrder_meetOrder_and_exists_storey_of_mem_primeHeckeSet_of_evalAt_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/1d39cf84-0000-5b79-8419-1916c4e6fd79
-- title:
--   Level-ℓ storey of the class-set tower for a given shift
-- statement:
--   Let $a,b\in\mathbb Q$, let $N\ge 1$ be squarefree, and let $q,q'$ be primes with $q\nmid N$, $q'\nmid N$, $q'\neq q$ and $q'\ge 5$, such that `IsDefiniteRamifiedExactlyAt a b q'` holds: $a<0$, $b<0$, and for a finite place $v$ of $\mathbb Q$ the algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly when $q'\in v$. Let $\Lambda\supseteq R$ be $\mathbb Z$-submodules of $\mathbb H[\mathbb Q,a,b]$ with $\Lambda$ a maximal order and $R$ an Eichler order of level $N$ (an intersection of two maximal orders of relative index $N$ in the first). Let $n$ be a unit of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb A_{\mathbb Q,f}$ lying in the prime Hecke set `primeHeckeSet R q` (that is, $n$ lies in the finite-adelic box of $R$, $q\,n^{-1}$ lies in that box while $n^{-1}$ does not, and $q^{-1}n$ does not), such that `meetOrder R n` $=R\cap nRn^{-1}$ is an Eichler order of level $Nq$, is stable under conjugation by $n$, and such that right translation by $n$ is an involution on the class set $\mathbb H^\times\backslash\widehat{\mathbb H}^\times/\widehat{(R\cap nRn^{-1})}^\times$, the double coset quotient by the image of the diagonal and by the finite-idèle stabiliser of the box. Let $v$ be a height-one prime of $\mathcal O_{\mathbb Q}$ containing $q$. Let $\ell$ be a prime not dividing $Nqq'$, and let $s$ be a finite idèle such that the diagonal central idèle attached to $\ell$ times $s^{-1}$ lies in `primeHeckeSet (meetOrder R n) ℓ` and the component of $s$ at $v$ is $1$. Then `meetOrder R s` $=R\cap sRs^{-1}$ is an Eichler order of level $N\ell$, and there is a finite idèle $n'$ in `primeHeckeSet (meetOrder R s) q` such that $(R\cap sRs^{-1})\cap n'(R\cap sRs^{-1})n'^{-1}$ is an Eichler order of level $N\ell q$, is stable under conjugation by $n'$, and has right translation by $n'$ acting as an involution on its class set, while moreover $n^{-1}n'$ lies in the finite-idèle stabiliser of the box of $R$, $s$ and $n'$ commute, and the class sets of the finite-idèle stabilisers of $R\cap sRs^{-1}$ and of $(R\cap sRs^{-1})\cap n'(R\cap sRs^{-1})n'^{-1}$ are finite.
--
--   This is the $T_\ell$ storey ($\ell\nmid Nqq'$) of the class-set tower used to describe Hecke action on the Čerednik–Drinfeld special fibre, in the form where the shift idèle $s$ is given in advance, subject only to the tower condition at $\ell$ and to triviality at the place above $q$; the output is the corresponding level-raising datum at $q$ one level up, compatible with the datum downstairs. It is invoked by the statements producing permutation realisations of the quotient vertex and edge sets and the quotient presentations of the Hecke-equivariant class sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_CSTower_isEichlerOrder_meetOrder_and_exists_storey_of_mem_primeHeckeSet_of_evalAt_eq_one.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CSTower.isEichlerOrder_meetOrder_and_exists_storey_of_mem_primeHeckeSet_of_evalAt_eq_one

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

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N * q * q')
    (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      primeHeckeSet (meetOrder R n) ℓ)
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
