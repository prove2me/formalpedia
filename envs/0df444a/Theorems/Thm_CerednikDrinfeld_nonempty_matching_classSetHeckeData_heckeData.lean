-- Prove2me | Theorems.Thm_CerednikDrinfeld_nonempty_matching_classSetHeckeData_heckeData
-- name    : CerednikDrinfeld.nonempty_matching_classSetHeckeData_heckeData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/2d9f9a99-2898-520c-a169-3759457ac2fc
-- title:
--   Matching class-set Hecke data with supersingular Hecke data
-- statement:
--   Fix rationals $a,b$, natural numbers $M,s,q'$ with $M$ nonzero and $s,q'$ prime, two $\mathbb{Z}$-submodules $\Lambda, R$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and a unit $n$ of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}$ (finite adèles of $\mathbb{Q}$); write $S =$ `meetOrder R n`, the intersection of $R$ with its conjugate by $n$, and form the double-coset class sets $\mathrm{Cl}(S)$, $\mathrm{Cl}(R)$ of the finite-idèle stabilisers of $S$ and of $R$, assumed finite (and $\mathrm{Cl}(R)$ with decidable equality). Assume the stabiliser of $S$ is contained in that of $R$, and that the class-set edge and vertex Hecke matrices attached to $(M,s,\Lambda,R,n)$ satisfy `ClassSetHeckeLaws` (pairwise commutation of the edge matrices, pairwise commutation of the vertex matrices, equivariance of both joint degeneracy maps for primes $\ell \neq s$, and stability of the joint kernel). Let $K$ be a field of characteristic $q'$ with decidable equality, and $X$ a supersingular level datum `SSLevelDatum q' K M s`, with the supersingular place sets $\mathrm{ssPlaces}(q', Ms, K)$ and $\mathrm{ssPlaces}(q', M, K)$ finite (the latter with decidable equality), satisfying the corresponding laws `X.HeckeLaws`. Suppose given bijections $e_E \colon \mathrm{Cl}(S) \simeq \mathrm{ssPlaces}(q', Ms, K)$ and $e_V \colon \mathrm{Cl}(R) \simeq \mathrm{ssPlaces}(q', M, K)$ such that: the first degeneracy map of $X$ composed with $e_E$ equals $e_V$ composed with the class-set forgetful map; the widths of $X$ pull back to the class weights; for every prime $\ell$ and every $x \colon \mathrm{Cl}(S) \to \mathbb{Z}$ one has $T^X_\ell (x \circ e_E^{-1}) = (T^{\mathrm{Cl}}_\ell x)\circ e_E^{-1}$ for the edge Hecke matrices `X.edgeHecke` and `classSetEdgeHecke M s Λ R n`; and $e_E$ carries right translation by $n$ on $\mathrm{Cl}(S)$ to the Atkin–Lehner permutation `X.atkinLehnerPerm`. The conclusion is that there exists a `Matching` of the Hecke data `classSetHeckeData M s Λ R n` and `X.heckeData` whose edge bijection is $e_E$, whose vertex bijection is $e_V$, and whose exceptional set of primes `bad` is empty.
--
--   This is the assembly step that converts a Deuring–Eichler style dictionary between the class sets of a quaternion order and the supersingular points of the two-level modular curve into a single matching object, with no exceptional primes, between the class-set Hecke degeneracy datum and the supersingular one. It feeds the transport of a two-place torsion datum along matchings, being used in the construction of such data from a supersingular level datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_nonempty_matching_classSetHeckeData_heckeData.lean

import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve

theorem CerednikDrinfeld.nonempty_matching_classSetHeckeData_heckeData
    {a b : ℚ} (M s q' : ℕ) [NeZero M] [Fact s.Prime] [Fact q'.Prime]
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hU : Submodule.finiteIdeleStabilizer (meetOrder R n) ≤ Submodule.finiteIdeleStabilizer R)
    (hlaws : ClassSetHeckeLaws M s Λ R n)
    (K : Type) [Field K] [CharP K q'] [DecidableEq K]
    (X : SSLevelDatum q' K M s)
    [Fintype ↥(ssPlaces q' (M * s) K)] [Fintype ↥(ssPlaces q' M K)] [DecidableEq ↥(ssPlaces q' M K)]
    (hX : X.HeckeLaws)
    (eE : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) ≃ ↥(ssPlaces q' (M * s) K))
    (eV : ClassSet (Submodule.finiteIdeleStabilizer R) ≃ ↥(ssPlaces q' M K))
    (ha : ∀ e, X.degeneracyData.a (eE e) = eV ((classSetDegeneracyData R n).a e))
    (hw : ∀ e, X.degeneracyData.w (eE e) = (classSetDegeneracyData R n).w e)
    (hT : ∀ (ℓ : Nat.Primes) (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ),
      (X.edgeHecke ℓ).mulVecLin (x ∘ eE.symm) = ((classSetEdgeHecke M s Λ R n ℓ).mulVecLin x) ∘ eE.symm)
    (hAL : ∀ e, eE (classSetShift _ n e) = X.atkinLehnerPerm (eE e)) :
    ∃ 𝓜 : Matching (classSetHeckeData M s Λ R n) X.heckeData,
      𝓜.eE = eE ∧ 𝓜.eV = eV ∧ 𝓜.bad = ∅ := by sorry
