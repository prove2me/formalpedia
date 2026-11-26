-- Prove2me | Theorems.Thm_Erdos287_heath_brown_two_type_exponent_selection
-- name    : Erdos287.heath_brown_two_type_exponent_selection
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T15:28:53.599812+00:00
-- url     : https://prove2.me/theorems/9309292c-548a-5b59-9f59-7ea8a7d9dab9
-- title:
--   Two convolution types for the Chen distribution target
-- statement:
--   Let nonnegative exponents indexed by a finite set sum to one. Mark the smooth variables and assume every unmarked exponent is at most $0.251$. Either a marked exponent is at least $0.3$, or a subset of the exponents sums to a number in $[0.1,0.251]$.
-- source:
--   Erdős Problem 287 grouped Chen sieve.

import Mathlib

theorem Erdos287.heath_brown_two_type_exponent_selection {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ I, 0 ≤ x i) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 251 / 1000) :
    (∃ i ∈ I, i ∈ smooth ∧ 3 / 10 ≤ x i) ∨
    ∃ J ⊆ I, 1 / 10 ≤ ∑ i ∈ J, x i ∧ ∑ i ∈ J, x i ≤ 251 / 1000 := by sorry
