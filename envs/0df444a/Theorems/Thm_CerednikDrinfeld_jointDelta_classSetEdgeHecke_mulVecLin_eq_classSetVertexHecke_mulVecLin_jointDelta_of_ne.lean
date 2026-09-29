-- Prove2me | Theorems.Thm_CerednikDrinfeld_jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne
-- name    : CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/ec57d40f-34a9-5044-a65f-273314c61c90
-- title:
--   Degeneracy pushforwards intertwine edge and vertex Hecke matrices away from q
-- statement:
--   Fix rationals $a,b$ and work in the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ and its finite-adelic unit group $(\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb A_{\mathbb Q,\mathrm f})^{\times}$. Let $N$ be a nonzero natural number and $q,q'$ primes with $q'\neq q$, $q\nmid N$, $q'\nmid N$, and assume $a<0$, $b<0$ and that for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completion $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly when $q'\in v$. Let $\Lambda,R$ be $\mathbb Z$-submodules of $\mathbb H[\mathbb Q,a,b]$ with $\Lambda$ a maximal order (an order maximal among the orders containing it), $R$ an Eichler order of level $N$ (an intersection $\Lambda_1\sqcap\Lambda_2$ of two maximal orders with $[\Lambda_1:R]=N$), and $R\le\Lambda$. Let $n$ be a finite-adelic unit, put $S=\mathrm{meetOrder}\,R\,n=R\sqcap nRn^{-1}$, and assume $S$ is an Eichler order of level $Nq$ and that $n$ lies in $\mathrm{primeHeckeSet}\,R\,q$, i.e. $n$ and $q\,n^{-1}$ lie in the adelic box of $R$ while $n^{-1}$ and $q^{-1}n$ do not. The class sets $\mathrm{ClassSet}$ of the finite-idele stabilisers of $S$ and of $R$ are the double coset spaces of the diagonal $\mathbb H[\mathbb Q,a,b]^{\times}$ against those stabilisers, and are assumed finite (with decidable equality on the $R$-side). Let $\ell$ be a prime with $\ell\neq q$, let $i\in\{0,1\}$ and let $x$ be an integer-valued function on the class set of $S$. Then $\delta_i$, the pushforward along $[\,\cdot\,]\mapsto[\,\cdot\,]$ for $i=0$ and along $[\,\tilde x\,]\mapsto[\tilde x\,n]$ for $i=1$, satisfies $\delta_i(T^{E}_{\ell}x)=T^{V}_{\ell}(\delta_i x)$, where $T^{E}_{\ell}$ is `classSetEdgeHecke N q Λ R n ℓ`, equal (as $\ell\neq q$) to the class-set Hecke matrix of the $\Lambda$-oriented $U_\ell$-set `levelHeckeUSet Λ S ℓ` if $\ell\mid N$ and of $\mathrm{primeHeckeSet}\,S\,\ell$ otherwise, and $T^{V}_{\ell}$ is the corresponding matrix `classSetVertexHecke N Λ R ℓ` for $R$; both matrices act by `Matrix.mulVecLin`.
--
--   This is the equivariance of the two degeneracy maps from the edge class set $\mathrm{Cl}(S)$ to the vertex class set $\mathrm{Cl}(R)$ with respect to the Hecke operators at primes $\ell\neq q$, the classical statement that the degeneracy maps between level $Nq$ and level $N$ commute with the good-prime (and $U_\ell$ for $\ell\mid N$) correspondences. It supplies the good-prime clause of the package [`CerednikDrinfeld.classSetHeckeLaws_of_isEichlerOrder_meetOrder`](thm.html#CerednikDrinfeld.classSetHeckeLaws_of_isEichlerOrder_meetOrder), which records the Hecke laws of the class-set graph used in the Čerednik–Drinfeld description of the relevant Shimura curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne
    (N q q' : ℕ) [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hn : IsEichlerOrder (meetOrder R n) (N * q)) (hnH : n ∈ primeHeckeSet R q)
    (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ q) (i : Fin 2)
    (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ) :
    jointDelta (classSetDegeneracyData R n) i ((classSetEdgeHecke N q Λ R n ℓ).mulVecLin x) =
      (classSetVertexHecke N Λ R ℓ).mulVecLin (jointDelta (classSetDegeneracyData R n) i x) := by sorry
