-- Prove2me | Theorems.Thm_CerednikDrinfeld_classSet_mk_eq_classSetShift_mk_of_finiteAdeleEvalAt_eq_mul_of_nrd_eq
-- name    : CerednikDrinfeld.classSet_mk_eq_classSetShift_mk_of_finiteAdeleEvalAt_eq_mul_of_nrd_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/85d9a2a5-bd90-52c5-81d4-0110c1a3e97e
-- title:
--   Class of ̄ w x equals the varpi'-shift of x
-- statement:
--   Fix rationals $a,b$ and a prime $q'\ge 5$ such that $\mathrm{IsDefiniteRamifiedExactlyAt}$ holds for $a,b,q'$: $a<0$, $b<0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $q'\in v$. Let $N$ be a nonzero squarefree natural number, let $\Lambda, R$ be $\mathbb{Z}$-submodules of $\mathbb{H}[\mathbb{Q},a,b]$ with $\Lambda$ a maximal order, $R$ Eichler of level $N$ (an intersection of two maximal orders of relative index $N$ in the first), $R\le\Lambda$ and $q'\nmid N$. Let $r$ be a prime with $r\ne q'$ and $r\nmid N$, let $v$ be a height-one prime containing $r$, and let $n$ be a unit of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q},f}$ lying in the prime Hecke set of $R$ at $r$ (that is, $n$ lies in the finite adelic box of $R$, $r\,n^{-1}$ lies in it, while $n^{-1}$ and $r^{-1}n$ do not). Assume that $\mathrm{meetOrder}\,R\,n = R\cap nRn^{-1}$ is Eichler of level $Nr$, is normalised by $n$, that the shift by $n$ is an involution on the class set of the finite-idele stabiliser of $\mathrm{meetOrder}\,R\,n$, and that this class set and that of the stabiliser of $R$ are finite. Let $\bar w\in\mathbb{H}[\mathbb{Q},a,b]^{\times}$ satisfy $\mathrm{nrd}(\bar w)=q'$, lie in the local unit group of $R$ at every prime $u\ne v$ not containing $q'$, and have the property that for every $u\ne v$ conjugation $x\mapsto \bar w^{-1}x\bar w$ in $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_u$ preserves both the local box of $R$ at $u$ and that of $\Lambda$ at $u$. Let $\varpi'$ be a unit of the adelic algebra whose local component is $1$ at every prime not containing $q'$, lying in the prime Hecke set of $\mathrm{meetOrder}\,R\,n$ at $q'$, normalising $\mathrm{meetOrder}\,R\,n$, and with $\varpi'^2$ equal to the diagonal image of the scalar $q'$ times an element of the finite-idele stabiliser of $\mathrm{meetOrder}\,R\,n$. Finally let $x,y$ be units of the adelic algebra whose components at every prime $u\ne v$ are $1$, with $y_v=\bar w_v\,x_v$. Then the double coset classes, taken modulo the diagonal image of $\mathbb{H}[\mathbb{Q},a,b]^{\times}$ on the left and the finite-idele stabiliser of $\mathrm{meetOrder}\,R\,n$ on the right, satisfy $[y] = \mathrm{classSetShift}_{\varpi'}[x]$, where the shift sends a class to the class of a chosen representative multiplied on the right by $\varpi'$.
--
--   This is the compatibility, in Kurihara's dictionary for the Čerednik–Drinfeld description, between the Atkin–Lehner type element of reduced norm $q'$ acting at the place $v$ and the shift of the class set of the level-$Nr$ Eichler order by the uniformiser $\varpi'$ at the ramified prime $q'$. It is used in the construction of the equivalence between the quotient graph data and the shifted class set in the Mumford-side frame.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_classSet_mk_eq_classSetShift_mk_of_finiteAdeleEvalAt_eq_mul_of_nrd_eq.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra
open CerednikDrinfeld

theorem CerednikDrinfeld.classSet_mk_eq_classSetShift_mk_of_finiteAdeleEvalAt_eq_mul_of_nrd_eq
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hq5 : 5 ≤ q') (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (N : ℕ) [NeZero N] (hN : Squarefree N) (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (r : ℕ) [Fact r.Prime] (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R r)
    (hS : IsEichlerOrder (meetOrder R n) (N * r))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hsq : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      classSetShift _ n (classSetShift _ n x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hq'N : ¬ q' ∣ N)
    (wbar : (ℍ[ℚ, a, b])ˣ)
    (hwbar : (nrd (wbar : ℍ[ℚ, a, b]) = (q' : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u wbar ∈ Submodule.localBoxUnits R u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → ∀ x : CosetGraph.Loc a b u,
          ((((CosetGraph.toLoc u wbar)⁻¹ : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) * x *
              ((CosetGraph.toLoc u wbar : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) ∈ Submodule.localBox R u ↔
            x ∈ Submodule.localBox R u) ∧
          ((((CosetGraph.toLoc u wbar)⁻¹ : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) * x *
              ((CosetGraph.toLoc u wbar : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) ∈ Submodule.localBox Λ u ↔
            x ∈ Submodule.localBox Λ u))))
    (ϖ' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hϖ'supp : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (ϖ' : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hϖ'T : ϖ' ∈ primeHeckeSet (meetOrder R n) q')
    (hϖ'norm : Submodule.conjByFiniteIdele (meetOrder R n) ϖ' = meetOrder R n)
    (hϖ'sq : ∃ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n),
      ϖ' * ϖ' = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
        (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q'.Prime).ne_zero))) * u)
    (x y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hx : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hy : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hyv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] wbar : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder R n)) y =
      classSetShift (Submodule.finiteIdeleStabilizer (meetOrder R n)) ϖ'
        (ClassSet.mk (Submodule.finiteIdeleStabilizer (meetOrder R n)) x) := by sorry
