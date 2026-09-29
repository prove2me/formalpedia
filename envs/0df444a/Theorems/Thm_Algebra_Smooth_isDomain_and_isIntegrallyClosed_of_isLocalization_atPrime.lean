-- Prove2me | Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
-- name    : Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/61e6c5f1-9f23-5a2f-9e53-69887a828d68
-- title:
--   Local rings of smooth algebras over a UFD are normal
-- statement:
--   Let $R$ be a commutative ring which is a domain and a unique factorisation monoid, and let $S$ be a commutative $R$-algebra which is smooth over $R$, i.e. formally smooth and of finite presentation in the sense of Mathlib's `Algebra.Smooth`. Let $p$ be a prime ideal of $S$, and let $S_p$ be any commutative ring equipped with an $S$-algebra structure making it a localisation of $S$ at the complement of $p$ (`IsLocalization.AtPrime`). The theorem asserts the conjunction of two facts about $S_p$: it is an integral domain, and it is integrally closed in the sense of `IsIntegrallyClosed`, i.e. every element of its fraction field that is integral over $S_p$ lies in the image of $S_p$. Since the conclusion is stated for an arbitrary ring satisfying the localisation-at-a-prime property rather than for a fixed model of $S_p$, it applies in particular to stalks of the structure sheaf of a scheme smooth over such a base.
--
--   This is the local-ring form of 'smooth over a normal base is normal', here with the base assumed to be a unique factorisation domain (which covers fields, discrete valuation rings and $\mathbb{Z}$). It is used for the corresponding statement about stalks of schemes smooth over a discrete valuation ring, and in arguments about minimal primes over a discrete valuation ring base within the deformation-theoretic part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] (Sₚ : Type u) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization.AtPrime Sₚ p] :
    IsDomain Sₚ ∧ IsIntegrallyClosed Sₚ := by sorry
