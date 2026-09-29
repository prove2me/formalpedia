-- Prove2me | Theorems.Thm_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field
-- name    : Algebra.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/d5635a38-b3a5-5341-8bb2-40aefe48b625
-- title:
--   Standard smooth algebras have some relative dimension
-- statement:
--   Let $k$ be a field and let $B$ be a commutative ring equipped with a $k$-algebra structure, and suppose $B$ is standard smooth over $k$ in Mathlib's sense, i.e. `Algebra.IsStandardSmooth k B` holds: there exist finite index types, one for the polynomial generators and one for the relations, together with a submersive presentation of $B$ as a quotient of the corresponding polynomial ring over $k$. The conclusion is that there exists a natural number $n$ for which `Algebra.IsStandardSmoothOfRelativeDimension n k B` holds, that is, $B$ admits a finite submersive presentation over $k$ whose dimension, the difference between the cardinality of its set of generators and the cardinality of its set of relations, is exactly $n$. Thus the unindexed standard smoothness hypothesis is upgraded to standard smoothness of a definite relative dimension, the value of $n$ being produced by the statement rather than prescribed. Nothing beyond the ring structure of $k$ is used in reaching the conclusion.
--
--   This is the definitional bridge from standard smoothness to standard smoothness of some relative dimension, the form in which Mathlib's results on regularity are stated. It feeds [`isRegularLocalRing_localization_atPrime_of_isStandardSmooth`](thm.html#isRegularLocalRing_localization_atPrime_of_isStandardSmooth), the statement that localisations of a standard smooth algebra over a field at its primes are regular local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_of_field
    {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
    [Algebra.IsStandardSmooth k B] :
    ∃ n, Algebra.IsStandardSmoothOfRelativeDimension n k B := by sorry
