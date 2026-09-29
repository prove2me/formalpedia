-- Prove2me | Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
-- name    : Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/29266709-afaa-5d14-ace5-f5d5634b6a71
-- title:
--   Local rings of an étale algebra over a normal domain
-- statement:
--   Let $P$ be a commutative ring that is an integral domain and is integrally closed in its field of fractions, and let $A$ be a commutative $P$-algebra that is étale over $P$ (flat and formally étale, i.e. formally smooth and formally unramified). Let $\mathfrak q$ be a prime ideal of $A$, and let $A_{\mathfrak q}$ be a commutative ring equipped with an $A$-algebra structure that realises the localisation of $A$ at the prime $\mathfrak q$, that is, $A \to A_{\mathfrak q}$ inverts exactly the complement of $\mathfrak q$ in the sense of `IsLocalization.AtPrime`. The conclusion is the conjunction of two assertions about $A_{\mathfrak q}$: it is an integral domain, and it is integrally closed in its field of fractions. All three rings lie in a single universe, and no Noetherian or finiteness hypothesis is imposed on $P$ or on $A$; in particular $A$ itself is not asserted to be a domain, only each of its localisations at primes.
--
--   This is the normality of étale (more generally smooth) algebras over a normal base, in the case of an integrally closed domain base and stated localisation by localisation at the primes of $A$, since $A$ need not be a domain globally (for instance $A = P \times P$). It feeds the results on integral closure in tensor products over étale and smooth algebras, and the criteria for being étale at a point used in the study of the deformation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    (P : Type u) [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    (A : Type u) [CommRing A] [Algebra P A] [Algebra.Etale P A]
    (q : Ideal A) [q.IsPrime] (A_q : Type u) [CommRing A_q] [Algebra A A_q] [IsLocalization.AtPrime A_q q] :
    IsDomain A_q ∧ IsIntegrallyClosed A_q := by sorry
