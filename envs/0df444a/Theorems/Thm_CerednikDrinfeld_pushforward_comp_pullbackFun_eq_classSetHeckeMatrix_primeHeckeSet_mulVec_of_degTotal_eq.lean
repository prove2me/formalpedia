-- Prove2me | Theorems.Thm_CerednikDrinfeld_pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_primeHeckeSet_mulVec_of_degTotal_eq
-- name    : CerednikDrinfeld.pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_primeHeckeSet_mulVec_of_degTotal_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/1479da6c-86a7-5589-8a7a-4b4b67d810ed
-- title:
--   Push–pull along class-set degeneracy maps computes T_ℓ
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and natural numbers $N,q,q'$ with $N\neq 0$ squarefree and $q,q'$ prime, subject to $q\nmid N$, $q'\nmid N$, $q'\neq q$ and $q'\geq 5$, and assume `IsDefiniteRamifiedExactlyAt a b q'`, i.e. $a<0$, $b<0$ and, for each finite place $v$ of $\mathbb{Q}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit precisely when $q$ lies in $v$. Let $\Lambda,R\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be $\mathbb{Z}$-submodules with $\Lambda$ a maximal order, $R$ an Eichler order of level $N$ (an intersection of two maximal orders of relative additive index $N$ in the first), and $R\le\Lambda$. For an order $\Lambda_0$ write $\widehat{\Lambda_0}$ for its finite adelic box, $\widehat{\Lambda_0}^{\times}$ for the stabiliser of that box in $(\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{f})^{\times}$, and `primeHeckeSet` $\Lambda_0\,m$ for the set of adelic units $h$ with $h\in\widehat{\Lambda_0}$, $m\,h^{-1}\in\widehat{\Lambda_0}$, $h^{-1}\notin\widehat{\Lambda_0}$ and $m^{-1}h\notin\widehat{\Lambda_0}$. Let $n$ be an adelic unit in `primeHeckeSet` $R\,q$ such that $S:=R\cap nRn^{-1}$ (`meetOrder R n`) is Eichler of level $Nq$, is stable under conjugation by $n$, and such that shifting twice by $n$ on $\mathrm{Cl}(\widehat{S}^{\times})$ is the identity; the class sets occurring are assumed finite with decidable equality. Let $\ell$ be a prime with $\ell\nmid Nqq'$, and let $s$ be an adelic unit such that the diagonal image of the scalar $\ell$ times $s^{-1}$ lies in `primeHeckeSet` $S\,\ell$ and $R':=R\cap sRs^{-1}$ is Eichler of level $N\ell$. Let $n'\in$ `primeHeckeSet` $R'\,q$ be such that $S':=R'\cap n'R'n'^{-1}$ is Eichler of level $N\ell q$, is stable under conjugation by $n'$, shifting twice by $n'$ on $\mathrm{Cl}(\widehat{S'}^{\times})$ is the identity, $n^{-1}n'\in\widehat{R}^{\times}$ and $sn'=n's$. Consider the class-set degeneracy data of $(R',n')$ and of $(R,n)$, with edges $\mathrm{Cl}(\widehat{S'}^{\times})$, resp. $\mathrm{Cl}(\widehat{S}^{\times})$, vertices $\mathrm{Cl}(\widehat{R'}^{\times})$, resp. $\mathrm{Cl}(\widehat{R}^{\times})$, maps $a$ the forgetful map and $b$ the forgetful map twisted by right multiplication by $n'$, resp. $n$, and weights given by `classWeight`. Let $\alpha,\beta$ be finite morphisms from the first datum to the second (each consisting of maps on vertices and edges compatible with $a$, $b$, edge, vertex and total degrees satisfying the weight law and the fibre-sum laws), with $\alpha$'s edge map the forgetful map $\mathrm{Cl}(\widehat{S'}^{\times})\to\mathrm{Cl}(\widehat{S}^{\times})$, $\beta$'s edge map $e\mapsto[\tilde e\,s]$, and $\beta$'s total degree equal to $\ell+1$. Then for every $x:\mathrm{Cl}(\widehat{S}^{\times})\to\mathbb{Z}$, the pushforward along $\alpha$'s edge map of the degree-weighted pullback $e\mapsto \deg_{\beta}(e)\,x(\beta(e))$ equals the matrix–vector product of $x$ with the class-set Hecke matrix of $\widehat{S}^{\times}$ at the set `primeHeckeSet` $S\,\ell$, whose $(i,j)$ entry is the number of elements of the Hecke incidence set of $\widehat{S}^{\times}$ and that set at a representative of $j$ and at $i$; explicitly, $\sum_{\alpha(e)=i}\deg_{\beta}(e)\,x(\beta(e))$ equals that weighted sum over $j$ of $x(j)$.
--
--   This is the Hecke dictionary for one storey of the class-set (Brandt) graph tower: it identifies the composite of the degree-weighted pullback along the $s$-shift with the pushforward along the forgetful edge map as the Hecke operator $T_\ell$ on edge divisors of the class-set degeneracy datum attached to $(R,n)$, the dual graph of the Čerednik–Drinfeld special fibre at $q$. It is used by [`CerednikDrinfeld.pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq`](thm.html#CerednikDrinfeld.pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq), which packages the same identity for composites of degeneracy morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_primeHeckeSet_mulVec_of_degTotal_eq.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.pushforward_comp_pullbackFun_eq_classSetHeckeMatrix_primeHeckeSet_mulVec_of_degTotal_eq

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

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N * q * q')
    (s : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
          (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * s⁻¹ ∈
      primeHeckeSet (meetOrder R n) ℓ)
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
    (hdeg : (β.degTotal : ℕ) = ℓ + 1)
    (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ) :
    CerednikDrinfeld.pushforward α.mapE (β.pullbackFun x) =
      (classSetHeckeMatrix (Submodule.finiteIdeleStabilizer (meetOrder R n))
        (primeHeckeSet (meetOrder R n) ℓ)).mulVec x := by sorry
