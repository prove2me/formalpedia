-- Prove2me | Theorems.Thm_CerednikDrinfeld_pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_levelHeckeUSet_mulVec_of_dvd
-- name    : CerednikDrinfeld.pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_levelHeckeUSet_mulVec_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/8043a6ab-82db-5ad2-b459-78279af8b556
-- title:
--   Push–pull identity for U_ℓ on class-set edge divisors
-- statement:
--   Fix $a,b\in\mathbb Q$, a nonzero $N\in\mathbb N$ with $N$ squarefree, and primes $q,q'$ with $q\nmid N$, $q'\nmid N$, $q'\neq q$ and $q'\geq 5$, such that $a<0$, $b<0$ and $\mathbb H=\mathbb H[\mathbb Q,a,b]$ becomes a division algebra over the completion at a height-one prime $v$ of $\mathcal O_{\mathbb Q}$ exactly when $q'\in v$. Let $\Lambda,R\subseteq\mathbb H$ be $\mathbb Z$-submodules with $\Lambda$ an order maximal among orders, $R$ an Eichler order of level $N$ (an intersection of two such maximal orders of relative index $N$) and $R\leq\Lambda$. Let $n$ be a unit of $\mathbb H\otimes_{\mathbb Q}\mathbb A_{\mathbb Q}^{\mathrm{fin}}$ lying in `primeHeckeSet R q` (i.e. $n$ lies in the adelic box of $R$, so does $q\,n^{-1}$, while $n^{-1}$ and $q^{-1}n$ do not), with $S=R\sqcap R^{n}$ an Eichler order of level $Nq$, with $S^{n}=S$, and such that shifting twice by $n$ is the identity on the class set $\mathrm{Cl}(\hat S^{\times})$ of the finite-idele stabiliser of $S$. Let $\ell$ be a prime dividing $N$ and $s$ a finite idele unit such that the diagonal idele of $\ell$ times $s^{-1}$ lies in `levelHeckeUSet` $\Lambda\,S\,\ell$, that is, it lies in `primeHeckeSet S ℓ`, does not normalise $S$, and its $\Lambda$-conjugate does not contain $S$. Let $R'=R\sqcap R^{s}$ be Eichler of level $N\ell$, let $n'$ lie in `primeHeckeSet R' q` with $S'=R'\sqcap (R')^{n'}$ Eichler of level $N\ell q$, $(S')^{n'}=S'$, double shifting by $n'$ the identity on $\mathrm{Cl}(\hat{S'}^{\times})$, and assume $n^{-1}n'\in\hat R^{\times}$ and $sn'=n's$; finiteness and decidability instances for the class sets involved are assumed. Let $\alpha,\beta$ be finite morphisms from the class-set degeneracy datum of $(R',n')$ (edges $\mathrm{Cl}(\hat{S'}^{\times})$, vertices $\mathrm{Cl}(\hat{R'}^{\times})$, source the forgetful map, target the shift by $n'$, weights the class weights of $S'$) to that of $(R,n)$, with edge map of $\alpha$ the forgetful map $\mathrm{Cl}(\hat{S'}^{\times})\to\mathrm{Cl}(\hat S^{\times})$ and edge map of $\beta$ given by $e\mapsto[\,\tilde e\,s\,]$. Then for every $x:\mathrm{Cl}(\hat S^{\times})\to\mathbb Z$, the fibrewise sum along the edge map of $\alpha$ of the degree-weighted pullback $e\mapsto \beta.\mathrm{deg}(e)\cdot x(\beta.\mathrm{mapE}(e))$ equals the product of $x$ with the matrix $\big(\,\mathrm{heckeKernel}\,\hat S^{\times}\,(\mathrm{levelHeckeUSet}\,\Lambda\,S\,\ell)\,j\,i\,\big)_{i,j}$, the matrix of incidence counts attached to the double coset `levelHeckeUSet` $\Lambda\,S\,\ell$.
--
--   This is the dictionary identifying the $U_\ell$-operator on edge divisors of the class-set (Brandt) graph of level $Nq$ with the composite of the degree-weighted pullback along the $s$-shift and the pushforward along the forgetful map through the storey of level $N\ell q$, for a prime $\ell$ dividing the squarefree level $N$. It is used by [`CerednikDrinfeld.pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq`](thm.html#CerednikDrinfeld.pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq), in the comparison of Hecke actions on the Čerednik–Drinfeld special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_levelHeckeUSet_mulVec_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_levelHeckeUSet_mulVec_of_dvd

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

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ∣ N)
    (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      levelHeckeUSet Λ (meetOrder R n) ℓ)
    (hR' : IsEichlerOrder (meetOrder R s) (N * ℓ))
    (n' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn' : n' ∈ primeHeckeSet (meetOrder R s) q)
    (hS' : IsEichlerOrder (meetOrder (meetOrder R s) n') (N * ℓ * q))
    (hnorm' : Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') n' = meetOrder (meetOrder R s) n')
    (hsq' : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')),
      classSetShift _ n' (classSetShift _ n' x) = x)
    (hnn' : n⁻¹ * n' ∈ Submodule.finiteIdeleStabilizer R) (hsn' : s * n' = n' * s)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder (meetOrder R s) n')))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s)))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s)))]
    (α β : (classSetDegeneracyData (meetOrder R s) n').FiniteHom (classSetDegeneracyData R n))
    (hα : α.mapE = classSetForget _ _) (hβ : β.mapE = fun e => ClassSet.mk _ (e.out * s))
    (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ) :
    CerednikDrinfeld.pushforward α.mapE (β.pullbackFun x) =
      (classSetHeckeMatrix (Submodule.finiteIdeleStabilizer (meetOrder R n))
        (levelHeckeUSet Λ (meetOrder R n) ℓ)).mulVec x := by sorry
