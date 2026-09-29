-- Prove2me | Theorems.Thm_CerednikDrinfeld_classSetHeckeLaws_of_isEichlerOrder_meetOrder
-- name    : CerednikDrinfeld.classSetHeckeLaws_of_isEichlerOrder_meetOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/e9291320-2424-5a2b-8d51-d3384c24d921
-- title:
--   Class-set Hecke laws for an Eichler order and its meet order
-- statement:
--   Let $N\ge 1$ and let $q,q'$ be primes with $q'\neq q$ and $q\nmid N$, $q'\nmid N$. Let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsDefiniteRamifiedExactlyAt a b q'`: $a<0$, $b<0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $q'$ lies in $v$. Let $\Lambda,R$ be $\mathbb{Z}$-submodules of $\mathbb{H}[\mathbb{Q},a,b]$ with $\Lambda$ a maximal order (an order, i.e. containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning and finitely generated, and maximal among orders containing it), $R$ an Eichler order of level $N$ (an intersection $\Lambda_1\cap\Lambda_2$ of two maximal orders with relative index $N$ of $R$ in $\Lambda_1$), and $R\le\Lambda$. Let $n$ be a unit of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q},f}$ lying in `primeHeckeSet R q`, i.e. $n$ lies in the finite adelic box of $R$, $q\,n^{-1}$ lies in that box, while $n^{-1}$ and $q^{-1}n$ do not. Assume the class sets of the finite idelic stabilisers of $R$ and of $\mathrm{meetOrder}\,R\,n=R\cap\mathrm{conj}_n(R)$ are finite, and that $\mathrm{meetOrder}\,R\,n$ is an Eichler order of level $Nq$. Then `ClassSetHeckeLaws N q Λ R n` holds: the edge matrices `classSetEdgeHecke N q Λ R n ℓ` (given by the Hecke matrix of `uHeckeSet R n q` when $\ell=q$, of `levelHeckeUSet Λ (meetOrder R n) ℓ` when $\ell\mid N$, and of `primeHeckeSet (meetOrder R n) ℓ` otherwise) commute pairwise; the vertex matrices `classSetVertexHecke N Λ R ℓ` (the Hecke matrix of `levelHeckeUSet Λ R ℓ` when $\ell\mid N$, of `primeHeckeSet R ℓ` otherwise) commute pairwise; for every prime $\ell\neq q$, each of the two pushforwards of `classSetDegeneracyData R n` (forgetting the level structure, and $[x]\mapsto[xn]$) intertwines the edge matrix at $\ell$ with the vertex matrix at $\ell$; and for every prime $\ell$ each edge matrix preserves the joint kernel of the two pushforwards.
--
--   This is the verification, for class sets of Eichler orders in a definite quaternion algebra over $\mathbb{Q}$, of the axioms required of a Hecke degeneracy datum on the class-set graph: commutation of the Eichler–Brandt matrices at the edge and vertex levels, intertwining with the two degeneracy maps away from the Iwahori prime $q$, and stability of the joint kernel. It supplies the laws hypothesis used in the Čerednik–Drinfeld construction of a two-place torsion datum and in the transport of Hecke data along the degeneracy pushforward and pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_classSetHeckeLaws_of_isEichlerOrder_meetOrder.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra
open CerednikDrinfeld

theorem CerednikDrinfeld.classSetHeckeLaws_of_isEichlerOrder_meetOrder
    (N q q' : ℕ) [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hn : IsEichlerOrder (meetOrder R n) (N * q)) (hnH : n ∈ primeHeckeSet R q) :
    ClassSetHeckeLaws N q Λ R n := by sorry
