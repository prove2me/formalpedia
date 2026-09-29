-- Prove2me | Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes
-- name    : AlgebraicGeometry.LocallyQuasiFinite.exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/ebeae714-df1a-50af-a458-25b9907ee6a2
-- title:
--   Generic finiteness at a minimal prime over an affine base
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $f : X \to \operatorname{Spec} R$ a morphism of schemes (the target being the spectrum of $R$ viewed as an object of `CommRingCat`), assumed locally of finite type, locally quasi-finite, separated and quasi-compact. Let $p$ be an ideal of $R$ lying in `minimalPrimes R`, that is, $p$ is a minimal element of the set of prime ideals of $R$. The assertion is that there exists $r \in R$ with $r \notin p$ such that the restriction $f \mid_{D(r)}$ of $f$ over the basic open subset $D(r) = \{\mathfrak q : r \notin \mathfrak q\}$ of $\operatorname{Spec} R$ — the induced morphism $f^{-1}(D(r)) \to D(r)$ obtained by pulling $f$ back along the open immersion $D(r) \hookrightarrow \operatorname{Spec} R$ — is a finite morphism. Thus $f$ becomes finite after passing to some basic open neighbourhood of the point of $\operatorname{Spec} R$ corresponding to $p$.
--
--   This is the scheme-theoretic form of generic finiteness: a separated, quasi-compact, locally quasi-finite morphism of finite type over an affine base is finite over a suitable basic open neighbourhood of any minimal prime of the base. It refines the ring-level statement [`Algebra.QuasiFinite.exists_not_mem_finite_awayMap_of_mem_minimalPrimes`](thm.html#Algebra.QuasiFinite.exists_not_mem_finite_awayMap_of_mem_minimalPrimes), which it cites, and is used in turn to obtain finiteness over a dense open of an irreducible base in [`AlgebraicGeometry.LocallyQuasiFinite.exists_isFinite_morphismRestrict_of_irreducibleSpace`](thm.html#AlgebraicGeometry.LocallyQuasiFinite.exists_isFinite_morphismRestrict_of_irreducibleSpace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_LocallyQuasiFinite_exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.LocallyQuasiFinite.exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsSeparated f] [QuasiCompact f]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ IsFinite (f ∣_ PrimeSpectrum.basicOpen r) := by sorry
