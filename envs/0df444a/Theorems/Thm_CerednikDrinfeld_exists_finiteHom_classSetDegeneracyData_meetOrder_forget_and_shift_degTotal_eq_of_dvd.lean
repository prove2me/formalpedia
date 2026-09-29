-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_of_dvd
-- name    : CerednikDrinfeld.exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/ef511a9f-5577-5ea8-817f-5e730b2869f6
-- title:
--   Two degree-ℓ morphisms of class-set degeneracy data
-- statement:
--   Let $\mathbb{H} = \mathbb{H}[\mathbb{Q},a,b]$ for rationals $a,b$, let $N$ be a nonzero squarefree natural number and $q,q'$ primes with $q \nmid N$, $q' \nmid N$, $q' \neq q$ and $q' \ge 5$, and assume $a<0$, $b<0$ and that for every finite place $v$ of $\mathbb{Q}$ the algebra $\mathbb{H} \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ lies over $q'$. Let $\Lambda$ be a maximal $\mathbb{Z}$-order in $\mathbb{H}$ and $R \le \Lambda$ an Eichler order of level $N$, i.e. an intersection of two maximal orders of relative index $N$. Let $n$ be a finite idele of $\mathbb{H}$ lying in `primeHeckeSet R q` (so $n$ lies in the adelic box of $R$, $q\,n^{-1}$ lies in it, while $n^{-1}$ and $q^{-1}n$ do not), and assume $\mathrm{meetOrder}\,R\,n = R \cap nRn^{-1}$ is an Eichler order of level $Nq$, is normalised by $n$, and that the shift $[x] \mapsto [xn]$ on the class set of the finite-idele stabiliser of $R \cap nRn^{-1}$ is an involution. Let $\ell$ be a prime dividing $N$ and $s$ a finite idele such that the central idele $\ell$ times $s^{-1}$ lies in `levelHeckeUSet` $\Lambda\,(R\cap nRn^{-1})\,\ell$, that is: it lies in `primeHeckeSet` $(R\cap nRn^{-1})\,\ell$, does not normalise $R\cap nRn^{-1}$, and does not conjugate $\Lambda$ into an order containing $R \cap nRn^{-1}$. Assume $R' := R \cap sRs^{-1}$ is an Eichler order of level $N\ell$, and let $n'$ lie in `primeHeckeSet` $R'\,q$ with $R' \cap n'R'n'^{-1}$ an Eichler order of level $N\ell q$ normalised by $n'$, with involutive shift by $n'$ on the corresponding class set, and with $n^{-1}n'$ in the finite-idele stabiliser of $R$ and $sn' = n's$. All class sets occurring are assumed finite with decidable equality. Then there exist two finite morphisms $\alpha,\beta$ of degeneracy data from `classSetDegeneracyData` $R'\,n'$ to `classSetDegeneracyData` $R\,n$ — each consisting of maps on vertices (class set of the stabiliser of the vertex order) and on edges (class set of the stabiliser of the edge order) compatible with both endpoint maps, together with edge degrees, vertex degrees and a total degree satisfying the weight-multiplicativity and fibre-sum identities of `DegeneracyData.FiniteHom` — such that: $\alpha$ is given on vertices and on edges by the forgetful map $[x] \mapsto [x]$, while $\beta$ is given on both by $[x] \mapsto [xs]$; for every edge $e$ and vertex $v$, the degrees $\alpha.\mathrm{deg}$, $\alpha.\mathrm{degV}$, $\beta.\mathrm{deg}$, $\beta.\mathrm{degV}$ multiply the number of units of the conjugated finer order at the source into the number of units of the conjugated coarser order at the image (with $e.\mathrm{out}$, $v.\mathrm{out}$ for $\alpha$ and $e.\mathrm{out}\,s$, $v.\mathrm{out}\,s$ for $\beta$), where units of an order $\Lambda_0$ means elements $u \in \Lambda_0$ invertible with inverse in $\Lambda_0$; and both total degrees equal $\ell$.
--
--   This supplies the two degeneracy maps of class-set (Brandt) graphs realising the Hecke operator $U_\ell$ at a prime $\ell$ dividing the squarefree level $N$, as harmonic morphisms of degeneracy data of total degree $\ell$ between the graph at level $N\ell q$ and the graph at level $Nq$. It is used by [`CerednikDrinfeld.pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq`](thm.html#CerednikDrinfeld.pushforward_pullback_eq_heckeKernelMap_of_mapE_comp_eq) in the comparison of pushforward and pullback along these maps with the Hecke kernel map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_of_dvd

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
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R s)))] :
    ∃ α β : (classSetDegeneracyData (meetOrder R s) n').FiniteHom (classSetDegeneracyData R n),

      α.mapV = classSetForget _ _ ∧
      α.mapE = classSetForget _ _ ∧
      (∀ e, (α.deg e : ℕ) *
          Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') e.out) u} =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R n) e.out) u}) ∧
      (∀ v, (α.degV v : ℕ) *
          Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R s) v.out) u} =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele R v.out) u}) ∧
      (α.degTotal : ℕ) = ℓ ∧

      (β.mapV = fun v => ClassSet.mk _ (v.out * s)) ∧
      (β.mapE = fun e => ClassSet.mk _ (e.out * s)) ∧
      (∀ e, (β.deg e : ℕ) *
          Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder (meetOrder R s) n') e.out) u} =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R n) (e.out * s)) u}) ∧
      (∀ v, (β.degV v : ℕ) *
          Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R s) v.out) u} =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele R (v.out * s)) u}) ∧
      (β.degTotal : ℕ) = ℓ := by sorry
