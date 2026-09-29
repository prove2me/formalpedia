-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_equiv_classSet_ssPlaces_degeneracy_hecke_comm
-- name    : CerednikDrinfeld.exists_equiv_classSet_ssPlaces_degeneracy_hecke_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/942945e7-b2d5-5e15-9730-c013b48c30ff
-- title:
--   Two-level Deuring transport of class sets to supersingular places
-- statement:
--   Let $q'\ge 5$ be a prime, $M$ a nonzero squarefree natural number and $s$ a prime with $s\ne q'$ and $s\nmid M$. Let $a,b\in\mathbb Q$ be such that $\mathbb H=\mathbb H[\mathbb Q,a,b]$ is definite and ramified exactly at $q'$, in the sense of `IsDefiniteRamifiedExactlyAt`: $a<0$, $b<0$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completion $\mathbb H\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly when $q'\in v$. Let $\Lambda$ be a maximal order (an order, i.e. a finitely generated $\mathbb Z$-submodule containing $1$, closed under multiplication and spanning $\mathbb H$ over $\mathbb Q$, maximal among orders) and let $R\le\Lambda$ be an Eichler order of level $M$, that is $R=\Lambda_1\cap\Lambda_2$ with $\Lambda_1,\Lambda_2$ maximal and the relative index of $R$ in $\Lambda_1$ equal to $M$. Let $n$ be a unit of $\mathbb H\otimes_{\mathbb Q}\mathbb A_{\mathbb Q}^{\mathrm{fin}}$ lying in `primeHeckeSet R s`, i.e. $n$ lies in the adelic box $\widehat R$, $s\,n^{-1}\in\widehat R$, while $n^{-1}\notin\widehat R$ and $s^{-1}n\notin\widehat R$. Assume that `meetOrder R n` $=R\cap nRn^{-1}$ is an Eichler order of level $Ms$, that it is fixed by conjugation by $n$, and that right translation by $n$ is an involution of the class set $\mathrm{ClassSet}$ of the stabiliser of its adelic box (the double coset quotient of the adelic units by the diagonal $\mathbb H^\times$ on the left and that stabiliser on the right). Let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $\kappa$ has characteristic $q'$, and let $X$ be a supersingular level datum `SSLevelDatum q' κ M s`: it records that $j_{Ms/M}$ and $j_{Ms/s}$ lie in the modular function field of level $Ms$ over $\kappa$, integrality of the two level maps `levelAlphaC`, `levelBetaC` and of all Hecke legs, that restriction of supersingular places of level $Ms$ along either level map is supersingular of level $M$, an Atkin–Lehner automorphism satisfying the prescribed exchange relations on the generators and preserving supersingular places, and a modular polynomial datum at $q'$ satisfying the Kronecker congruence; here a place is supersingular when it is rational, affine geometric, and its value at the geometric $j$-generator lies in `ssJSet q' κ`. The class set of `meetOrder R n` and the set of supersingular places of level $Ms$ are assumed finite. Then there are bijections $e_E$ from the class set of `meetOrder R n` onto the supersingular places of level $Ms$ over $\kappa$, and $e_V$ from the class set of $R$ onto those of level $M$, such that: the first leg `X.degeneracyData.a` of $X$ evaluated at $e_E(e)$ equals $e_V$ of the forgetful class-set map `classSetForget`; the width `X.degeneracyData.w` at $e_E(e)$, namely `Nat.toPNat'` of `placeWidth`, equals the class weight of `meetOrder R n` at $e$; for every prime $\ell$ and every $x:\mathrm{ClassSet}\to\mathbb Z$ the matrices `X.edgeHecke ℓ` (the Frobenius matrix when $\ell=q'$, otherwise the Hecke matrix at $\ell$ on supersingular places of level $Ms$) and `classSetEdgeHecke M s Λ R n ℓ` (the class-set matrix of `uHeckeSet R n s` when $\ell=s$, of `levelHeckeUSet Λ (meetOrder R n) ℓ` when $\ell\mid M$, and of `primeHeckeSet (meetOrder R n) ℓ` otherwise) have matching matrix–vector actions under $e_E$; and $e_E$ carries right translation by $n$ on the class set to the Atkin–Lehner permutation `X.atkinLehnerPerm`. Only the $a$-legs and the widths of the two degeneracy data are matched; no assertion is made about the $b$-legs.
--
--   This is the Deuring–Eichler comparison in the two-level form used in Ribet's work on level lowering: the supersingular points of the modular curve of level $Ms$ in characteristic $q'$, with their widths, their degeneracy map to level $M$, their Hecke action and the Atkin–Lehner involution at $s$, are identified with the class set of an Eichler order of level $Ms$ in the definite quaternion algebra ramified exactly at $q'$, carrying the corresponding quaternionic data. It feeds the statements [`CerednikDrinfeld.classSet_eq_empty_or_eq_univ_of_forall_mem_iff_of_squarefree`](thm.html#CerednikDrinfeld.classSet_eq_empty_or_eq_univ_of_forall_mem_iff_of_squarefree) and [`CerednikDrinfeld.exists_twoPlaceTorsionDatum_laws_of_ssLevelDatum_of_squarefree_of_six_mul_dvd_of_neZero`](thm.html#CerednikDrinfeld.exists_twoPlaceTorsionDatum_laws_of_ssLevelDatum_of_squarefree_of_six_mul_dvd_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_equiv_classSet_ssPlaces_degeneracy_hecke_comm.lean

import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra CerednikDrinfeld ModularCurve

theorem CerednikDrinfeld.exists_equiv_classSet_ssPlaces_degeneracy_hecke_comm
    (M s q' : ℕ) [NeZero M] [Fact q'.Prime] [Fact s.Prime]
    (hq5 : 5 ≤ q') (hM : Squarefree M) (hsq' : s ≠ q') (hsM : ¬ s ∣ M)
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a) (b := b) q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R M) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R s)
    (hS : IsEichlerOrder (meetOrder R n) (M * s))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (hsq : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)),
      classSetShift _ n (classSetShift _ n x) = x)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) q'] [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))] :
    ∃ (eE : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) ≃
          ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)))
      (eV : ClassSet (Submodule.finiteIdeleStabilizer R) ≃ ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))),
      (∀ e, X.degeneracyData.a (eE e) = eV ((classSetDegeneracyData R n).a e)) ∧
      (∀ e, X.degeneracyData.w (eE e) = (classSetDegeneracyData R n).w e) ∧
      (∀ (ℓ : Nat.Primes) (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ),
          (X.edgeHecke ℓ).mulVecLin (x ∘ eE.symm) = ((classSetEdgeHecke M s Λ R n ℓ).mulVecLin x) ∘ eE.symm) ∧
      (∀ e, eE (classSetShift _ n e) = X.atkinLehnerPerm (eE e)) := by sorry
