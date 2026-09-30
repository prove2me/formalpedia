-- Prove2me | Theorems.Thm_Algebra_FiniteType_prime_quotient_dimension_formula
-- name    : Algebra.FiniteType.prime_quotient_dimension_formula
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T00:56:55.212784+00:00
-- url     : https://prove2.me/theorems/27a5b723-39f9-4251-88cc-0d1cfd4f4c28
-- title:
--   Affine altitude formula for finite type domains over a field
-- statement:
--   Let $K$ be a field and let $A$ be an integral domain that is a finitely generated commutative $K$-algebra. For every prime ideal $q$ of $A$,
--   $$\dim(A/q)+\operatorname{ht}_A(q)=\dim A.$$
--   The dimensions and height are the actual Krull dimensions and prime-chain height. The equality is expressed in the extended natural numbers with a bottom value, as in the library definitions. All three values are finite under these hypotheses. This standard affine dimension theorem is an explicit open foundation, not a conclusion built into a new definition.
-- source:
--   Stacks Project, Section 10.114, Lemmas 10.114.3 and 10.114.4 (maximal prime-chain lengths in polynomial rings and their prime quotients), https://stacks.math.columbia.edu/tag/00OO . The displayed altitude formula follows by concatenating chains below and above q. Used as a general algebraic foundation for Philippon Proposition 3.3.

import Mathlib
set_option autoImplicit false

theorem Algebra.FiniteType.prime_quotient_dimension_formula
(K A : Type*) [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (q : Ideal A) (hq : q.IsPrime) :
    ringKrullDim (A ⧸ q) + (q.height : WithBot ℕ∞) = ringKrullDim A := by sorry
