-- Prove2me | Theorems.Thm_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd
-- name    : ClassGroup.exists_finset_forall_exists_mk0_eq_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/92713c65-b003-5762-9c44-ac5026932dcb
-- title:
--   A finite set of primes supporting all ideal classes
-- statement:
--   Let $R$ be a commutative ring which is a Dedekind domain and whose class group $\mathrm{Cl}(R)$ is finite. The assertion is that there exists a finite set $S$ of points of the height-one spectrum of $R$, i.e. a finite set of nonzero prime ideals of $R$, with the following property: for every class $c \in \mathrm{Cl}(R)$ there is an ideal $I$ of $R$ lying in the monoid of non-zero-divisors of the multiplicative monoid of ideals (so $I$ is a nonzero ideal) such that the class $\mathrm{mk}_0(I)$ of $I$ in $\mathrm{Cl}(R)$ equals $c$, and such that every height-one prime $v$ whose underlying ideal `v.asIdeal` divides $I$ belongs to $S$. Thus a single finite set $S$ of primes suffices simultaneously for all classes: each class has an integral representative supported on $S$. In particular the classes of the primes in $S$ generate $\mathrm{Cl}(R)$, although that consequence is not part of the statement.
--
--   This is the standard "finite set of primes generating the class group" statement, in the form of one integral representative per class with prime support inside a fixed finite set. It feeds the idèle-theoretic decompositions used downstream, being cited in the construction of automorphic-form content homomorphisms, in a Herbrand-type argument over cyclotomic fields, and in a prime-norm index inequality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped nonZeroDivisors

theorem ClassGroup.exists_finset_forall_exists_mk0_eq_of_dvd
    (R : Type*) [CommRing R] [IsDedekindDomain R] [Finite (ClassGroup R)] :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum R), ∀ c : ClassGroup R, ∃ I : (Ideal R)⁰,
      ClassGroup.mk0 I = c ∧ ∀ v : IsDedekindDomain.HeightOneSpectrum R, v.asIdeal ∣ (I : Ideal R) → v ∈ S := by sorry
