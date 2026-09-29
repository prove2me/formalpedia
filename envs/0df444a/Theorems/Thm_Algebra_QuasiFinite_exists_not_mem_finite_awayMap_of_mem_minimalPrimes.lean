-- Prove2me | Theorems.Thm_Algebra_QuasiFinite_exists_not_mem_finite_awayMap_of_mem_minimalPrimes
-- name    : Algebra.QuasiFinite.exists_not_mem_finite_awayMap_of_mem_minimalPrimes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/d7abfb35-707c-5074-a4e9-eb3fa9e9d352
-- title:
--   Generic finiteness at a minimal prime (ring form)
-- statement:
--   Let $R$ and $A$ be commutative rings in a common universe and let $A$ be an $R$-algebra which is of finite type (`Algebra.FiniteType R A`) and quasi-finite over $R$ (`Algebra.QuasiFinite R A`). Let $p$ be an ideal of $R$ lying in `minimalPrimes R`, that is, a minimal member of the set of prime ideals of $R$ containing the zero ideal, so a minimal prime of $R$. The assertion is that there exists an element $r \in R$ with $r \notin p$ such that the ring homomorphism obtained from the structure map $R \to A$ by localising away from $r$ on the source and away from its image $\mathrm{algebraMap}\,R\,A\,r$ on the target, namely `Localization.awayMap (algebraMap R A) r` from `Localization.Away r` to `Localization.Away (algebraMap R A r)`, is finite in the sense of `RingHom.Finite`: the target $A[1/r]$ is a finitely generated module over the source $R[1/r]$. Thus a quasi-finite algebra of finite type becomes finite after inverting one element of $R$ outside a prescribed minimal prime; no noetherian or reducedness hypothesis on $R$ is imposed.
--
--   This is the affine, ring-theoretic form of generic finiteness for quasi-finite morphisms of finite type (EGA IV 9.6.1), specialised to a basic open neighbourhood of a minimal prime of the base. It is used to derive the scheme-level statement [`AlgebraicGeometry.LocallyQuasiFinite.exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes`](thm.html#AlgebraicGeometry.LocallyQuasiFinite.exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes), where the restriction of a locally quasi-finite morphism over a basic open set around a minimal prime is shown to be finite.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_QuasiFinite_exists_not_mem_finite_awayMap_of_mem_minimalPrimes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem Algebra.QuasiFinite.exists_not_mem_finite_awayMap_of_mem_minimalPrimes
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [Algebra.QuasiFinite R A]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ (Localization.awayMap (algebraMap R A) r).Finite := by sorry
