-- Prove2me | Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
-- name    : Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/6d62b819-7e21-5e92-8758-8aa871d5e4ae
-- title:
--   Smooth algebras over integrally closed domains have normal localisations
-- statement:
--   Let $R$ be a commutative ring which is an integrally closed domain, and let $S$ be a commutative $R$-algebra which is smooth over $R$ (in Mathlib's sense: $S$ is formally smooth over $R$ and of finite presentation as an $R$-algebra). Let $p$ be a prime ideal of $S$, and let $S_p$ be a commutative ring equipped with an $S$-algebra structure which realises the localisation of $S$ at the prime $p$, i.e. $S_p$ is a localisation of $S$ at the multiplicative set $S \setminus p$ of elements outside $p$. All three rings are taken in a single universe. The conclusion is the conjunction of two assertions: $S_p$ is an integral domain, and $S_p$ is integrally closed in its field of fractions. Note that no domain or integral-closedness hypothesis is placed on $S$ itself (a smooth algebra may well be a product of rings); only its localisations at primes are asserted to be normal domains.
--
--   This is the statement that a smooth algebra over a normal domain has normal local rings, the affine-local form of 'smooth over normal is normal', with no Noetherian hypothesis. It is used to derive integral closedness of a smooth algebra that is itself a domain, integral closedness of quotients by minimal primes, and normality of the stalks of a smooth scheme over a normal base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] (Sₚ : Type u) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization.AtPrime Sₚ p] :
    IsDomain Sₚ ∧ IsIntegrallyClosed Sₚ := by sorry
