-- Prove2me | solution 1 for syracuse_reaches_one_below_91130
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T06:44:16.518804+00:00
-- url     : https://prove2.me/submissions/16ca6533-7331-40e5-9951-937837e6cdf7

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_87129

set_option maxHeartbeats 1000000

open Nat

abbrev Reach (n : ℕ) : Prop := ∃ j : ℕ, syracuseStep^[j] n = 1

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]

theorem rs {x y : ℕ} (h : syracuseStep x = y) (hy : Reach y) : Reach x := by
  obtain ⟨j, hj⟩ := hy
  exact ⟨j + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact hj⟩

/-- Everything below the previously verified bound is already known to reach 1. -/
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 87128) : Reach n :=
  syracuse_reaches_one_below_87129 n h1 h2 h3
theorem R196613 : Reach 196613 := rs (se 4 (by rfl) ⟨18432, by rfl⟩) (B 36865 (by norm_num) ⟨18432, by rfl⟩ (by norm_num))
theorem R131093 : Reach 131093 := rs (se 6 (by rfl) ⟨3072, by rfl⟩) (B 6145 (by norm_num) ⟨3072, by rfl⟩ (by norm_num))
theorem R98329 : Reach 98329 := rs (se 2 (by rfl) ⟨36873, by rfl⟩) (B 73747 (by norm_num) ⟨36873, by rfl⟩ (by norm_num))
theorem R131117 : Reach 131117 := rs (se 3 (by rfl) ⟨24584, by rfl⟩) (B 49169 (by norm_num) ⟨24584, by rfl⟩ (by norm_num))
theorem R163885 : Reach 163885 := rs (se 3 (by rfl) ⟨30728, by rfl⟩) (B 61457 (by norm_num) ⟨30728, by rfl⟩ (by norm_num))
theorem R98365 : Reach 98365 := rs (se 3 (by rfl) ⟨18443, by rfl⟩) (B 36887 (by norm_num) ⟨18443, by rfl⟩ (by norm_num))
theorem R131141 : Reach 131141 := rs (se 4 (by rfl) ⟨12294, by rfl⟩) (B 24589 (by norm_num) ⟨12294, by rfl⟩ (by norm_num))
theorem R196685 : Reach 196685 := rs (se 3 (by rfl) ⟨36878, by rfl⟩) (B 73757 (by norm_num) ⟨36878, by rfl⟩ (by norm_num))
theorem R131165 : Reach 131165 := rs (se 3 (by rfl) ⟨24593, by rfl⟩) (B 49187 (by norm_num) ⟨24593, by rfl⟩ (by norm_num))
theorem R98401 : Reach 98401 := rs (se 2 (by rfl) ⟨36900, by rfl⟩) (B 73801 (by norm_num) ⟨36900, by rfl⟩ (by norm_num))
theorem R131189 : Reach 131189 := rs (se 5 (by rfl) ⟨6149, by rfl⟩) (B 12299 (by norm_num) ⟨6149, by rfl⟩ (by norm_num))
theorem R229493 : Reach 229493 := rs (se 5 (by rfl) ⟨10757, by rfl⟩) (B 21515 (by norm_num) ⟨10757, by rfl⟩ (by norm_num))
theorem R98437 : Reach 98437 := rs (se 4 (by rfl) ⟨9228, by rfl⟩) (B 18457 (by norm_num) ⟨9228, by rfl⟩ (by norm_num))
theorem R131213 : Reach 131213 := rs (se 3 (by rfl) ⟨24602, by rfl⟩) (B 49205 (by norm_num) ⟨24602, by rfl⟩ (by norm_num))
theorem R196757 : Reach 196757 := rs (se 6 (by rfl) ⟨4611, by rfl⟩) (B 9223 (by norm_num) ⟨4611, by rfl⟩ (by norm_num))
theorem R131237 : Reach 131237 := rs (se 4 (by rfl) ⟨12303, by rfl⟩) (B 24607 (by norm_num) ⟨12303, by rfl⟩ (by norm_num))
theorem R98473 : Reach 98473 := rs (se 2 (by rfl) ⟨36927, by rfl⟩) (B 73855 (by norm_num) ⟨36927, by rfl⟩ (by norm_num))
theorem R295093 : Reach 295093 := rs (se 5 (by rfl) ⟨13832, by rfl⟩) (B 27665 (by norm_num) ⟨13832, by rfl⟩ (by norm_num))
theorem R131261 : Reach 131261 := rs (se 3 (by rfl) ⟨24611, by rfl⟩) (B 49223 (by norm_num) ⟨24611, by rfl⟩ (by norm_num))
theorem R295109 : Reach 295109 := rs (se 4 (by rfl) ⟨27666, by rfl⟩) (B 55333 (by norm_num) ⟨27666, by rfl⟩ (by norm_num))
theorem R98509 : Reach 98509 := rs (se 3 (by rfl) ⟨18470, by rfl⟩) (B 36941 (by norm_num) ⟨18470, by rfl⟩ (by norm_num))
theorem R131285 : Reach 131285 := rs (se 7 (by rfl) ⟨1538, by rfl⟩) (B 3077 (by norm_num) ⟨1538, by rfl⟩ (by norm_num))
theorem R196829 : Reach 196829 := rs (se 3 (by rfl) ⟨36905, by rfl⟩) (B 73811 (by norm_num) ⟨36905, by rfl⟩ (by norm_num))
theorem R131309 : Reach 131309 := rs (se 3 (by rfl) ⟨24620, by rfl⟩) (B 49241 (by norm_num) ⟨24620, by rfl⟩ (by norm_num))
theorem R98545 : Reach 98545 := rs (se 2 (by rfl) ⟨36954, by rfl⟩) (B 73909 (by norm_num) ⟨36954, by rfl⟩ (by norm_num))
theorem R131333 : Reach 131333 := rs (se 4 (by rfl) ⟨12312, by rfl⟩) (B 24625 (by norm_num) ⟨12312, by rfl⟩ (by norm_num))
theorem R98581 : Reach 98581 := rs (se 6 (by rfl) ⟨2310, by rfl⟩) (B 4621 (by norm_num) ⟨2310, by rfl⟩ (by norm_num))
theorem R131357 : Reach 131357 := rs (se 3 (by rfl) ⟨24629, by rfl⟩) (B 49259 (by norm_num) ⟨24629, by rfl⟩ (by norm_num))
theorem R196901 : Reach 196901 := rs (se 4 (by rfl) ⟨18459, by rfl⟩) (B 36919 (by norm_num) ⟨18459, by rfl⟩ (by norm_num))
theorem R131381 : Reach 131381 := rs (se 5 (by rfl) ⟨6158, by rfl⟩) (B 12317 (by norm_num) ⟨6158, by rfl⟩ (by norm_num))
theorem R98617 : Reach 98617 := rs (se 2 (by rfl) ⟨36981, by rfl⟩) (B 73963 (by norm_num) ⟨36981, by rfl⟩ (by norm_num))
theorem R131405 : Reach 131405 := rs (se 3 (by rfl) ⟨24638, by rfl⟩) (B 49277 (by norm_num) ⟨24638, by rfl⟩ (by norm_num))
theorem R98653 : Reach 98653 := rs (se 3 (by rfl) ⟨18497, by rfl⟩) (B 36995 (by norm_num) ⟨18497, by rfl⟩ (by norm_num))
theorem R131429 : Reach 131429 := rs (se 4 (by rfl) ⟨12321, by rfl⟩) (B 24643 (by norm_num) ⟨12321, by rfl⟩ (by norm_num))
theorem R196973 : Reach 196973 := rs (se 3 (by rfl) ⟨36932, by rfl⟩) (B 73865 (by norm_num) ⟨36932, by rfl⟩ (by norm_num))
theorem R131453 : Reach 131453 := rs (se 3 (by rfl) ⟨24647, by rfl⟩) (B 49295 (by norm_num) ⟨24647, by rfl⟩ (by norm_num))
theorem R98689 : Reach 98689 := rs (se 2 (by rfl) ⟨37008, by rfl⟩) (B 74017 (by norm_num) ⟨37008, by rfl⟩ (by norm_num))
theorem R131477 : Reach 131477 := rs (se 6 (by rfl) ⟨3081, by rfl⟩) (B 6163 (by norm_num) ⟨3081, by rfl⟩ (by norm_num))
theorem R98725 : Reach 98725 := rs (se 4 (by rfl) ⟨9255, by rfl⟩) (B 18511 (by norm_num) ⟨9255, by rfl⟩ (by norm_num))
theorem R131501 : Reach 131501 := rs (se 3 (by rfl) ⟨24656, by rfl⟩) (B 49313 (by norm_num) ⟨24656, by rfl⟩ (by norm_num))
theorem R197045 : Reach 197045 := rs (se 5 (by rfl) ⟨9236, by rfl⟩) (B 18473 (by norm_num) ⟨9236, by rfl⟩ (by norm_num))
theorem R131525 : Reach 131525 := rs (se 4 (by rfl) ⟨12330, by rfl⟩) (B 24661 (by norm_num) ⟨12330, by rfl⟩ (by norm_num))
theorem R98761 : Reach 98761 := rs (se 2 (by rfl) ⟨37035, by rfl⟩) (B 74071 (by norm_num) ⟨37035, by rfl⟩ (by norm_num))
theorem R229837 : Reach 229837 := rs (se 3 (by rfl) ⟨43094, by rfl⟩) (B 86189 (by norm_num) ⟨43094, by rfl⟩ (by norm_num))
theorem R131549 : Reach 131549 := rs (se 3 (by rfl) ⟨24665, by rfl⟩) (B 49331 (by norm_num) ⟨24665, by rfl⟩ (by norm_num))
theorem R98797 : Reach 98797 := rs (se 3 (by rfl) ⟨18524, by rfl⟩) (B 37049 (by norm_num) ⟨18524, by rfl⟩ (by norm_num))
theorem R131573 : Reach 131573 := rs (se 5 (by rfl) ⟨6167, by rfl⟩) (B 12335 (by norm_num) ⟨6167, by rfl⟩ (by norm_num))
theorem R197117 : Reach 197117 := rs (se 3 (by rfl) ⟨36959, by rfl⟩) (B 73919 (by norm_num) ⟨36959, by rfl⟩ (by norm_num))
theorem R459269 : Reach 459269 := rs (se 4 (by rfl) ⟨43056, by rfl⟩) (B 86113 (by norm_num) ⟨43056, by rfl⟩ (by norm_num))
theorem R131597 : Reach 131597 := rs (se 3 (by rfl) ⟨24674, by rfl⟩) (B 49349 (by norm_num) ⟨24674, by rfl⟩ (by norm_num))
theorem R98833 : Reach 98833 := rs (se 2 (by rfl) ⟨37062, by rfl⟩) (B 74125 (by norm_num) ⟨37062, by rfl⟩ (by norm_num))
theorem R688661 : Reach 688661 := rs (se 6 (by rfl) ⟨16140, by rfl⟩) (B 32281 (by norm_num) ⟨16140, by rfl⟩ (by norm_num))
theorem R131621 : Reach 131621 := rs (se 4 (by rfl) ⟨12339, by rfl⟩) (B 24679 (by norm_num) ⟨12339, by rfl⟩ (by norm_num))
theorem R98869 : Reach 98869 := rs (se 5 (by rfl) ⟨4634, by rfl⟩) (B 9269 (by norm_num) ⟨4634, by rfl⟩ (by norm_num))
theorem R131645 : Reach 131645 := rs (se 3 (by rfl) ⟨24683, by rfl⟩) (B 49367 (by norm_num) ⟨24683, by rfl⟩ (by norm_num))
theorem R229949 : Reach 229949 := rs (se 3 (by rfl) ⟨43115, by rfl⟩) (B 86231 (by norm_num) ⟨43115, by rfl⟩ (by norm_num))
theorem R197189 : Reach 197189 := rs (se 4 (by rfl) ⟨18486, by rfl⟩) (B 36973 (by norm_num) ⟨18486, by rfl⟩ (by norm_num))
theorem R131669 : Reach 131669 := rs (se 8 (by rfl) ⟨771, by rfl⟩) (B 1543 (by norm_num) ⟨771, by rfl⟩ (by norm_num))
theorem R98905 : Reach 98905 := rs (se 2 (by rfl) ⟨37089, by rfl⟩) (B 74179 (by norm_num) ⟨37089, by rfl⟩ (by norm_num))
theorem R131693 : Reach 131693 := rs (se 3 (by rfl) ⟨24692, by rfl⟩) (B 49385 (by norm_num) ⟨24692, by rfl⟩ (by norm_num))
theorem R295541 : Reach 295541 := rs (se 5 (by rfl) ⟨13853, by rfl⟩) (B 27707 (by norm_num) ⟨13853, by rfl⟩ (by norm_num))
theorem R98941 : Reach 98941 := rs (se 3 (by rfl) ⟨18551, by rfl⟩) (B 37103 (by norm_num) ⟨18551, by rfl⟩ (by norm_num))
theorem R131717 : Reach 131717 := rs (se 4 (by rfl) ⟨12348, by rfl⟩) (B 24697 (by norm_num) ⟨12348, by rfl⟩ (by norm_num))
theorem R197261 : Reach 197261 := rs (se 3 (by rfl) ⟨36986, by rfl⟩) (B 73973 (by norm_num) ⟨36986, by rfl⟩ (by norm_num))
theorem R131741 : Reach 131741 := rs (se 3 (by rfl) ⟨24701, by rfl⟩) (B 49403 (by norm_num) ⟨24701, by rfl⟩ (by norm_num))
theorem R98977 : Reach 98977 := rs (se 2 (by rfl) ⟨37116, by rfl⟩) (B 74233 (by norm_num) ⟨37116, by rfl⟩ (by norm_num))
theorem R131765 : Reach 131765 := rs (se 5 (by rfl) ⟨6176, by rfl⟩) (B 12353 (by norm_num) ⟨6176, by rfl⟩ (by norm_num))
theorem R99013 : Reach 99013 := rs (se 4 (by rfl) ⟨9282, by rfl⟩) (B 18565 (by norm_num) ⟨9282, by rfl⟩ (by norm_num))
theorem R131789 : Reach 131789 := rs (se 3 (by rfl) ⟨24710, by rfl⟩) (B 49421 (by norm_num) ⟨24710, by rfl⟩ (by norm_num))
theorem R197333 : Reach 197333 := rs (se 7 (by rfl) ⟨2312, by rfl⟩) (B 4625 (by norm_num) ⟨2312, by rfl⟩ (by norm_num))
theorem R131813 : Reach 131813 := rs (se 4 (by rfl) ⟨12357, by rfl⟩) (B 24715 (by norm_num) ⟨12357, by rfl⟩ (by norm_num))
theorem R99049 : Reach 99049 := rs (se 2 (by rfl) ⟨37143, by rfl⟩) (B 74287 (by norm_num) ⟨37143, by rfl⟩ (by norm_num))
theorem R361205 : Reach 361205 := rs (se 5 (by rfl) ⟨16931, by rfl⟩) (B 33863 (by norm_num) ⟨16931, by rfl⟩ (by norm_num))
theorem R99065 : Reach 99065 := rs (se 2 (by rfl) ⟨37149, by rfl⟩) (B 74299 (by norm_num) ⟨37149, by rfl⟩ (by norm_num))
theorem R131837 : Reach 131837 := rs (se 3 (by rfl) ⟨24719, by rfl⟩) (B 49439 (by norm_num) ⟨24719, by rfl⟩ (by norm_num))
theorem R230141 : Reach 230141 := rs (se 3 (by rfl) ⟨43151, by rfl⟩) (B 86303 (by norm_num) ⟨43151, by rfl⟩ (by norm_num))
theorem R99085 : Reach 99085 := rs (se 3 (by rfl) ⟨18578, by rfl⟩) (B 37157 (by norm_num) ⟨18578, by rfl⟩ (by norm_num))
theorem R131861 : Reach 131861 := rs (se 6 (by rfl) ⟨3090, by rfl⟩) (B 6181 (by norm_num) ⟨3090, by rfl⟩ (by norm_num))
theorem R197405 : Reach 197405 := rs (se 3 (by rfl) ⟨37013, by rfl⟩) (B 74027 (by norm_num) ⟨37013, by rfl⟩ (by norm_num))
theorem R131885 : Reach 131885 := rs (se 3 (by rfl) ⟨24728, by rfl⟩) (B 49457 (by norm_num) ⟨24728, by rfl⟩ (by norm_num))
theorem R99121 : Reach 99121 := rs (se 2 (by rfl) ⟨37170, by rfl⟩) (B 74341 (by norm_num) ⟨37170, by rfl⟩ (by norm_num))
theorem R131909 : Reach 131909 := rs (se 4 (by rfl) ⟨12366, by rfl⟩) (B 24733 (by norm_num) ⟨12366, by rfl⟩ (by norm_num))
theorem R99157 : Reach 99157 := rs (se 9 (by rfl) ⟨290, by rfl⟩) (B 581 (by norm_num) ⟨290, by rfl⟩ (by norm_num))
theorem R131933 : Reach 131933 := rs (se 3 (by rfl) ⟨24737, by rfl⟩) (B 49475 (by norm_num) ⟨24737, by rfl⟩ (by norm_num))
theorem R197477 : Reach 197477 := rs (se 4 (by rfl) ⟨18513, by rfl⟩) (B 37027 (by norm_num) ⟨18513, by rfl⟩ (by norm_num))
theorem R131957 : Reach 131957 := rs (se 5 (by rfl) ⟨6185, by rfl⟩) (B 12371 (by norm_num) ⟨6185, by rfl⟩ (by norm_num))
theorem R99193 : Reach 99193 := rs (se 2 (by rfl) ⟨37197, by rfl⟩) (B 74395 (by norm_num) ⟨37197, by rfl⟩ (by norm_num))
theorem R131981 : Reach 131981 := rs (se 3 (by rfl) ⟨24746, by rfl⟩) (B 49493 (by norm_num) ⟨24746, by rfl⟩ (by norm_num))
theorem R99229 : Reach 99229 := rs (se 3 (by rfl) ⟨18605, by rfl⟩) (B 37211 (by norm_num) ⟨18605, by rfl⟩ (by norm_num))
theorem R132005 : Reach 132005 := rs (se 4 (by rfl) ⟨12375, by rfl⟩) (B 24751 (by norm_num) ⟨12375, by rfl⟩ (by norm_num))
theorem R197549 : Reach 197549 := rs (se 3 (by rfl) ⟨37040, by rfl⟩) (B 74081 (by norm_num) ⟨37040, by rfl⟩ (by norm_num))
theorem R132029 : Reach 132029 := rs (se 3 (by rfl) ⟨24755, by rfl⟩) (B 49511 (by norm_num) ⟨24755, by rfl⟩ (by norm_num))
theorem R99265 : Reach 99265 := rs (se 2 (by rfl) ⟨37224, by rfl⟩) (B 74449 (by norm_num) ⟨37224, by rfl⟩ (by norm_num))
theorem R132053 : Reach 132053 := rs (se 7 (by rfl) ⟨1547, by rfl⟩) (B 3095 (by norm_num) ⟨1547, by rfl⟩ (by norm_num))
theorem R99301 : Reach 99301 := rs (se 4 (by rfl) ⟨9309, by rfl⟩) (B 18619 (by norm_num) ⟨9309, by rfl⟩ (by norm_num))
theorem R132077 : Reach 132077 := rs (se 3 (by rfl) ⟨24764, by rfl⟩) (B 49529 (by norm_num) ⟨24764, by rfl⟩ (by norm_num))
theorem R197621 : Reach 197621 := rs (se 5 (by rfl) ⟨9263, by rfl⟩) (B 18527 (by norm_num) ⟨9263, by rfl⟩ (by norm_num))
theorem R132101 : Reach 132101 := rs (se 4 (by rfl) ⟨12384, by rfl⟩) (B 24769 (by norm_num) ⟨12384, by rfl⟩ (by norm_num))
theorem R99337 : Reach 99337 := rs (se 2 (by rfl) ⟨37251, by rfl⟩) (B 74503 (by norm_num) ⟨37251, by rfl⟩ (by norm_num))
theorem R132125 : Reach 132125 := rs (se 3 (by rfl) ⟨24773, by rfl⟩) (B 49547 (by norm_num) ⟨24773, by rfl⟩ (by norm_num))
theorem R295973 : Reach 295973 := rs (se 4 (by rfl) ⟨27747, by rfl⟩) (B 55495 (by norm_num) ⟨27747, by rfl⟩ (by norm_num))
theorem R99373 : Reach 99373 := rs (se 3 (by rfl) ⟨18632, by rfl⟩) (B 37265 (by norm_num) ⟨18632, by rfl⟩ (by norm_num))
theorem R132149 : Reach 132149 := rs (se 5 (by rfl) ⟨6194, by rfl⟩) (B 12389 (by norm_num) ⟨6194, by rfl⟩ (by norm_num))
theorem R197693 : Reach 197693 := rs (se 3 (by rfl) ⟨37067, by rfl⟩) (B 74135 (by norm_num) ⟨37067, by rfl⟩ (by norm_num))
theorem R132173 : Reach 132173 := rs (se 3 (by rfl) ⟨24782, by rfl⟩) (B 49565 (by norm_num) ⟨24782, by rfl⟩ (by norm_num))
theorem R99409 : Reach 99409 := rs (se 2 (by rfl) ⟨37278, by rfl⟩) (B 74557 (by norm_num) ⟨37278, by rfl⟩ (by norm_num))
theorem R230485 : Reach 230485 := rs (se 8 (by rfl) ⟨1350, by rfl⟩) (B 2701 (by norm_num) ⟨1350, by rfl⟩ (by norm_num))
theorem R132197 : Reach 132197 := rs (se 4 (by rfl) ⟨12393, by rfl⟩) (B 24787 (by norm_num) ⟨12393, by rfl⟩ (by norm_num))
theorem R99445 : Reach 99445 := rs (se 5 (by rfl) ⟨4661, by rfl⟩) (B 9323 (by norm_num) ⟨4661, by rfl⟩ (by norm_num))
theorem R132221 : Reach 132221 := rs (se 3 (by rfl) ⟨24791, by rfl⟩) (B 49583 (by norm_num) ⟨24791, by rfl⟩ (by norm_num))
theorem R197765 : Reach 197765 := rs (se 4 (by rfl) ⟨18540, by rfl⟩) (B 37081 (by norm_num) ⟨18540, by rfl⟩ (by norm_num))
theorem R132245 : Reach 132245 := rs (se 6 (by rfl) ⟨3099, by rfl⟩) (B 6199 (by norm_num) ⟨3099, by rfl⟩ (by norm_num))
theorem R99481 : Reach 99481 := rs (se 2 (by rfl) ⟨37305, by rfl⟩) (B 74611 (by norm_num) ⟨37305, by rfl⟩ (by norm_num))
theorem R132269 : Reach 132269 := rs (se 3 (by rfl) ⟨24800, by rfl⟩) (B 49601 (by norm_num) ⟨24800, by rfl⟩ (by norm_num))
theorem R99517 : Reach 99517 := rs (se 3 (by rfl) ⟨18659, by rfl⟩) (B 37319 (by norm_num) ⟨18659, by rfl⟩ (by norm_num))
theorem R132293 : Reach 132293 := rs (se 4 (by rfl) ⟨12402, by rfl⟩) (B 24805 (by norm_num) ⟨12402, by rfl⟩ (by norm_num))
theorem R230597 : Reach 230597 := rs (se 4 (by rfl) ⟨21618, by rfl⟩) (B 43237 (by norm_num) ⟨21618, by rfl⟩ (by norm_num))
theorem R197837 : Reach 197837 := rs (se 3 (by rfl) ⟨37094, by rfl⟩) (B 74189 (by norm_num) ⟨37094, by rfl⟩ (by norm_num))
theorem R132317 : Reach 132317 := rs (se 3 (by rfl) ⟨24809, by rfl⟩) (B 49619 (by norm_num) ⟨24809, by rfl⟩ (by norm_num))
theorem R99553 : Reach 99553 := rs (se 2 (by rfl) ⟨37332, by rfl⟩) (B 74665 (by norm_num) ⟨37332, by rfl⟩ (by norm_num))
theorem R132341 : Reach 132341 := rs (se 5 (by rfl) ⟨6203, by rfl⟩) (B 12407 (by norm_num) ⟨6203, by rfl⟩ (by norm_num))
theorem R99589 : Reach 99589 := rs (se 4 (by rfl) ⟨9336, by rfl⟩) (B 18673 (by norm_num) ⟨9336, by rfl⟩ (by norm_num))
theorem R132365 : Reach 132365 := rs (se 3 (by rfl) ⟨24818, by rfl⟩) (B 49637 (by norm_num) ⟨24818, by rfl⟩ (by norm_num))
theorem R197909 : Reach 197909 := rs (se 6 (by rfl) ⟨4638, by rfl⟩) (B 9277 (by norm_num) ⟨4638, by rfl⟩ (by norm_num))
theorem R132389 : Reach 132389 := rs (se 4 (by rfl) ⟨12411, by rfl⟩) (B 24823 (by norm_num) ⟨12411, by rfl⟩ (by norm_num))
theorem R99625 : Reach 99625 := rs (se 2 (by rfl) ⟨37359, by rfl⟩) (B 74719 (by norm_num) ⟨37359, by rfl⟩ (by norm_num))
theorem R656693 : Reach 656693 := rs (se 5 (by rfl) ⟨30782, by rfl⟩) (B 61565 (by norm_num) ⟨30782, by rfl⟩ (by norm_num))
theorem R132413 : Reach 132413 := rs (se 3 (by rfl) ⟨24827, by rfl⟩) (B 49655 (by norm_num) ⟨24827, by rfl⟩ (by norm_num))
theorem R99661 : Reach 99661 := rs (se 3 (by rfl) ⟨18686, by rfl⟩) (B 37373 (by norm_num) ⟨18686, by rfl⟩ (by norm_num))
theorem R132437 : Reach 132437 := rs (se 12 (by rfl) ⟨48, by rfl⟩) (B 97 (by norm_num) ⟨48, by rfl⟩ (by norm_num))
theorem R197981 : Reach 197981 := rs (se 3 (by rfl) ⟨37121, by rfl⟩) (B 74243 (by norm_num) ⟨37121, by rfl⟩ (by norm_num))
theorem R132461 : Reach 132461 := rs (se 3 (by rfl) ⟨24836, by rfl⟩) (B 49673 (by norm_num) ⟨24836, by rfl⟩ (by norm_num))
theorem R99697 : Reach 99697 := rs (se 2 (by rfl) ⟨37386, by rfl⟩) (B 74773 (by norm_num) ⟨37386, by rfl⟩ (by norm_num))
theorem R132485 : Reach 132485 := rs (se 4 (by rfl) ⟨12420, by rfl⟩) (B 24841 (by norm_num) ⟨12420, by rfl⟩ (by norm_num))
theorem R99733 : Reach 99733 := rs (se 6 (by rfl) ⟨2337, by rfl⟩) (B 4675 (by norm_num) ⟨2337, by rfl⟩ (by norm_num))
theorem R132509 : Reach 132509 := rs (se 3 (by rfl) ⟨24845, by rfl⟩) (B 49691 (by norm_num) ⟨24845, by rfl⟩ (by norm_num))
theorem R198053 : Reach 198053 := rs (se 4 (by rfl) ⟨18567, by rfl⟩) (B 37135 (by norm_num) ⟨18567, by rfl⟩ (by norm_num))
theorem R132533 : Reach 132533 := rs (se 5 (by rfl) ⟨6212, by rfl⟩) (B 12425 (by norm_num) ⟨6212, by rfl⟩ (by norm_num))
theorem R99769 : Reach 99769 := rs (se 2 (by rfl) ⟨37413, by rfl⟩) (B 74827 (by norm_num) ⟨37413, by rfl⟩ (by norm_num))
theorem R132557 : Reach 132557 := rs (se 3 (by rfl) ⟨24854, by rfl⟩) (B 49709 (by norm_num) ⟨24854, by rfl⟩ (by norm_num))
theorem R296405 : Reach 296405 := rs (se 7 (by rfl) ⟨3473, by rfl⟩) (B 6947 (by norm_num) ⟨3473, by rfl⟩ (by norm_num))
theorem R99805 : Reach 99805 := rs (se 3 (by rfl) ⟨18713, by rfl⟩) (B 37427 (by norm_num) ⟨18713, by rfl⟩ (by norm_num))
theorem R132581 : Reach 132581 := rs (se 4 (by rfl) ⟨12429, by rfl⟩) (B 24859 (by norm_num) ⟨12429, by rfl⟩ (by norm_num))
theorem R198125 : Reach 198125 := rs (se 3 (by rfl) ⟨37148, by rfl⟩) (B 74297 (by norm_num) ⟨37148, by rfl⟩ (by norm_num))
theorem R132605 : Reach 132605 := rs (se 3 (by rfl) ⟨24863, by rfl⟩) (B 49727 (by norm_num) ⟨24863, by rfl⟩ (by norm_num))
theorem R99841 : Reach 99841 := rs (se 2 (by rfl) ⟨37440, by rfl⟩) (B 74881 (by norm_num) ⟨37440, by rfl⟩ (by norm_num))
theorem R132629 : Reach 132629 := rs (se 6 (by rfl) ⟨3108, by rfl⟩) (B 6217 (by norm_num) ⟨3108, by rfl⟩ (by norm_num))
theorem R99877 : Reach 99877 := rs (se 4 (by rfl) ⟨9363, by rfl⟩) (B 18727 (by norm_num) ⟨9363, by rfl⟩ (by norm_num))
theorem R132653 : Reach 132653 := rs (se 3 (by rfl) ⟨24872, by rfl⟩) (B 49745 (by norm_num) ⟨24872, by rfl⟩ (by norm_num))
theorem R198197 : Reach 198197 := rs (se 5 (by rfl) ⟨9290, by rfl⟩) (B 18581 (by norm_num) ⟨9290, by rfl⟩ (by norm_num))
theorem R132677 : Reach 132677 := rs (se 4 (by rfl) ⟨12438, by rfl⟩) (B 24877 (by norm_num) ⟨12438, by rfl⟩ (by norm_num))
theorem R99913 : Reach 99913 := rs (se 2 (by rfl) ⟨37467, by rfl⟩) (B 74935 (by norm_num) ⟨37467, by rfl⟩ (by norm_num))
theorem R132701 : Reach 132701 := rs (se 3 (by rfl) ⟨24881, by rfl⟩) (B 49763 (by norm_num) ⟨24881, by rfl⟩ (by norm_num))
theorem R99949 : Reach 99949 := rs (se 3 (by rfl) ⟨18740, by rfl⟩) (B 37481 (by norm_num) ⟨18740, by rfl⟩ (by norm_num))
theorem R132725 : Reach 132725 := rs (se 5 (by rfl) ⟨6221, by rfl⟩) (B 12443 (by norm_num) ⟨6221, by rfl⟩ (by norm_num))
theorem R198269 : Reach 198269 := rs (se 3 (by rfl) ⟨37175, by rfl⟩) (B 74351 (by norm_num) ⟨37175, by rfl⟩ (by norm_num))
theorem R132749 : Reach 132749 := rs (se 3 (by rfl) ⟨24890, by rfl⟩) (B 49781 (by norm_num) ⟨24890, by rfl⟩ (by norm_num))
theorem R99985 : Reach 99985 := rs (se 2 (by rfl) ⟨37494, by rfl⟩) (B 74989 (by norm_num) ⟨37494, by rfl⟩ (by norm_num))
theorem R132773 : Reach 132773 := rs (se 4 (by rfl) ⟨12447, by rfl⟩) (B 24895 (by norm_num) ⟨12447, by rfl⟩ (by norm_num))
theorem R100021 : Reach 100021 := rs (se 5 (by rfl) ⟨4688, by rfl⟩) (B 9377 (by norm_num) ⟨4688, by rfl⟩ (by norm_num))
theorem R132797 : Reach 132797 := rs (se 3 (by rfl) ⟨24899, by rfl⟩) (B 49799 (by norm_num) ⟨24899, by rfl⟩ (by norm_num))
theorem R198341 : Reach 198341 := rs (se 4 (by rfl) ⟨18594, by rfl⟩) (B 37189 (by norm_num) ⟨18594, by rfl⟩ (by norm_num))
theorem R132821 : Reach 132821 := rs (se 7 (by rfl) ⟨1556, by rfl⟩) (B 3113 (by norm_num) ⟨1556, by rfl⟩ (by norm_num))
theorem R100057 : Reach 100057 := rs (se 2 (by rfl) ⟨37521, by rfl⟩) (B 75043 (by norm_num) ⟨37521, by rfl⟩ (by norm_num))
theorem R132845 : Reach 132845 := rs (se 3 (by rfl) ⟨24908, by rfl⟩) (B 49817 (by norm_num) ⟨24908, by rfl⟩ (by norm_num))
theorem R100093 : Reach 100093 := rs (se 3 (by rfl) ⟨18767, by rfl⟩) (B 37535 (by norm_num) ⟨18767, by rfl⟩ (by norm_num))
theorem R132869 : Reach 132869 := rs (se 4 (by rfl) ⟨12456, by rfl⟩) (B 24913 (by norm_num) ⟨12456, by rfl⟩ (by norm_num))
theorem R198413 : Reach 198413 := rs (se 3 (by rfl) ⟨37202, by rfl⟩) (B 74405 (by norm_num) ⟨37202, by rfl⟩ (by norm_num))
theorem R460565 : Reach 460565 := rs (se 6 (by rfl) ⟨10794, by rfl⟩) (B 21589 (by norm_num) ⟨10794, by rfl⟩ (by norm_num))
theorem R132893 : Reach 132893 := rs (se 3 (by rfl) ⟨24917, by rfl⟩) (B 49835 (by norm_num) ⟨24917, by rfl⟩ (by norm_num))
theorem R100129 : Reach 100129 := rs (se 2 (by rfl) ⟨37548, by rfl⟩) (B 75097 (by norm_num) ⟨37548, by rfl⟩ (by norm_num))
theorem R132917 : Reach 132917 := rs (se 5 (by rfl) ⟨6230, by rfl⟩) (B 12461 (by norm_num) ⟨6230, by rfl⟩ (by norm_num))
theorem R100165 : Reach 100165 := rs (se 4 (by rfl) ⟨9390, by rfl⟩) (B 18781 (by norm_num) ⟨9390, by rfl⟩ (by norm_num))
theorem R132941 : Reach 132941 := rs (se 3 (by rfl) ⟨24926, by rfl⟩) (B 49853 (by norm_num) ⟨24926, by rfl⟩ (by norm_num))
theorem R198485 : Reach 198485 := rs (se 9 (by rfl) ⟨581, by rfl⟩) (B 1163 (by norm_num) ⟨581, by rfl⟩ (by norm_num))
theorem R132949 : Reach 132949 := rs (se 9 (by rfl) ⟨389, by rfl⟩) (B 779 (by norm_num) ⟨389, by rfl⟩ (by norm_num))
theorem R132965 : Reach 132965 := rs (se 4 (by rfl) ⟨12465, by rfl⟩) (B 24931 (by norm_num) ⟨12465, by rfl⟩ (by norm_num))
theorem R100201 : Reach 100201 := rs (se 2 (by rfl) ⟨37575, by rfl⟩) (B 75151 (by norm_num) ⟨37575, by rfl⟩ (by norm_num))
theorem R132989 : Reach 132989 := rs (se 3 (by rfl) ⟨24935, by rfl⟩) (B 49871 (by norm_num) ⟨24935, by rfl⟩ (by norm_num))
theorem R296837 : Reach 296837 := rs (se 4 (by rfl) ⟨27828, by rfl⟩) (B 55657 (by norm_num) ⟨27828, by rfl⟩ (by norm_num))
theorem R100237 : Reach 100237 := rs (se 3 (by rfl) ⟨18794, by rfl⟩) (B 37589 (by norm_num) ⟨18794, by rfl⟩ (by norm_num))
theorem R133013 : Reach 133013 := rs (se 6 (by rfl) ⟨3117, by rfl⟩) (B 6235 (by norm_num) ⟨3117, by rfl⟩ (by norm_num))
theorem R198557 : Reach 198557 := rs (se 3 (by rfl) ⟨37229, by rfl⟩) (B 74459 (by norm_num) ⟨37229, by rfl⟩ (by norm_num))
theorem R133037 : Reach 133037 := rs (se 3 (by rfl) ⟨24944, by rfl⟩) (B 49889 (by norm_num) ⟨24944, by rfl⟩ (by norm_num))
theorem R100273 : Reach 100273 := rs (se 2 (by rfl) ⟨37602, by rfl⟩) (B 75205 (by norm_num) ⟨37602, by rfl⟩ (by norm_num))
theorem R133061 : Reach 133061 := rs (se 4 (by rfl) ⟨12474, by rfl⟩) (B 24949 (by norm_num) ⟨12474, by rfl⟩ (by norm_num))
theorem R100309 : Reach 100309 := rs (se 7 (by rfl) ⟨1175, by rfl⟩) (B 2351 (by norm_num) ⟨1175, by rfl⟩ (by norm_num))
theorem R133085 : Reach 133085 := rs (se 3 (by rfl) ⟨24953, by rfl⟩) (B 49907 (by norm_num) ⟨24953, by rfl⟩ (by norm_num))
theorem R100325 : Reach 100325 := rs (se 4 (by rfl) ⟨9405, by rfl⟩) (B 18811 (by norm_num) ⟨9405, by rfl⟩ (by norm_num))
theorem R198629 : Reach 198629 := rs (se 4 (by rfl) ⟨18621, by rfl⟩) (B 37243 (by norm_num) ⟨18621, by rfl⟩ (by norm_num))
theorem R133109 : Reach 133109 := rs (se 5 (by rfl) ⟨6239, by rfl⟩) (B 12479 (by norm_num) ⟨6239, by rfl⟩ (by norm_num))
theorem R100345 : Reach 100345 := rs (se 2 (by rfl) ⟨37629, by rfl⟩) (B 75259 (by norm_num) ⟨37629, by rfl⟩ (by norm_num))
theorem R165901 : Reach 165901 := rs (se 3 (by rfl) ⟨31106, by rfl⟩) (B 62213 (by norm_num) ⟨31106, by rfl⟩ (by norm_num))
theorem R133133 : Reach 133133 := rs (se 3 (by rfl) ⟨24962, by rfl⟩) (B 49925 (by norm_num) ⟨24962, by rfl⟩ (by norm_num))
theorem R100381 : Reach 100381 := rs (se 3 (by rfl) ⟨18821, by rfl⟩) (B 37643 (by norm_num) ⟨18821, by rfl⟩ (by norm_num))
theorem R133157 : Reach 133157 := rs (se 4 (by rfl) ⟨12483, by rfl⟩) (B 24967 (by norm_num) ⟨12483, by rfl⟩ (by norm_num))
theorem R198701 : Reach 198701 := rs (se 3 (by rfl) ⟨37256, by rfl⟩) (B 74513 (by norm_num) ⟨37256, by rfl⟩ (by norm_num))
theorem R133181 : Reach 133181 := rs (se 3 (by rfl) ⟨24971, by rfl⟩) (B 49943 (by norm_num) ⟨24971, by rfl⟩ (by norm_num))
theorem R100417 : Reach 100417 := rs (se 2 (by rfl) ⟨37656, by rfl⟩) (B 75313 (by norm_num) ⟨37656, by rfl⟩ (by norm_num))
theorem R133205 : Reach 133205 := rs (se 8 (by rfl) ⟨780, by rfl⟩) (B 1561 (by norm_num) ⟨780, by rfl⟩ (by norm_num))
theorem R100453 : Reach 100453 := rs (se 4 (by rfl) ⟨9417, by rfl⟩) (B 18835 (by norm_num) ⟨9417, by rfl⟩ (by norm_num))
theorem R133229 : Reach 133229 := rs (se 3 (by rfl) ⟨24980, by rfl⟩) (B 49961 (by norm_num) ⟨24980, by rfl⟩ (by norm_num))
theorem R198773 : Reach 198773 := rs (se 5 (by rfl) ⟨9317, by rfl⟩) (B 18635 (by norm_num) ⟨9317, by rfl⟩ (by norm_num))
theorem R133253 : Reach 133253 := rs (se 4 (by rfl) ⟨12492, by rfl⟩) (B 24985 (by norm_num) ⟨12492, by rfl⟩ (by norm_num))
theorem R100489 : Reach 100489 := rs (se 2 (by rfl) ⟨37683, by rfl⟩) (B 75367 (by norm_num) ⟨37683, by rfl⟩ (by norm_num))
theorem R166045 : Reach 166045 := rs (se 3 (by rfl) ⟨31133, by rfl⟩) (B 62267 (by norm_num) ⟨31133, by rfl⟩ (by norm_num))
theorem R133277 : Reach 133277 := rs (se 3 (by rfl) ⟨24989, by rfl⟩) (B 49979 (by norm_num) ⟨24989, by rfl⟩ (by norm_num))
theorem R100525 : Reach 100525 := rs (se 3 (by rfl) ⟨18848, by rfl⟩) (B 37697 (by norm_num) ⟨18848, by rfl⟩ (by norm_num))
theorem R133301 : Reach 133301 := rs (se 5 (by rfl) ⟨6248, by rfl⟩) (B 12497 (by norm_num) ⟨6248, by rfl⟩ (by norm_num))
theorem R198845 : Reach 198845 := rs (se 3 (by rfl) ⟨37283, by rfl⟩) (B 74567 (by norm_num) ⟨37283, by rfl⟩ (by norm_num))
theorem R133325 : Reach 133325 := rs (se 3 (by rfl) ⟨24998, by rfl⟩) (B 49997 (by norm_num) ⟨24998, by rfl⟩ (by norm_num))
theorem R100561 : Reach 100561 := rs (se 2 (by rfl) ⟨37710, by rfl⟩) (B 75421 (by norm_num) ⟨37710, by rfl⟩ (by norm_num))
theorem R133349 : Reach 133349 := rs (se 4 (by rfl) ⟨12501, by rfl⟩) (B 25003 (by norm_num) ⟨12501, by rfl⟩ (by norm_num))
theorem R100597 : Reach 100597 := rs (se 5 (by rfl) ⟨4715, by rfl⟩) (B 9431 (by norm_num) ⟨4715, by rfl⟩ (by norm_num))
theorem R133373 : Reach 133373 := rs (se 3 (by rfl) ⟨25007, by rfl⟩) (B 50015 (by norm_num) ⟨25007, by rfl⟩ (by norm_num))
theorem R198917 : Reach 198917 := rs (se 4 (by rfl) ⟨18648, by rfl⟩) (B 37297 (by norm_num) ⟨18648, by rfl⟩ (by norm_num))
theorem R133397 : Reach 133397 := rs (se 6 (by rfl) ⟨3126, by rfl⟩) (B 6253 (by norm_num) ⟨3126, by rfl⟩ (by norm_num))
theorem R100633 : Reach 100633 := rs (se 2 (by rfl) ⟨37737, by rfl⟩) (B 75475 (by norm_num) ⟨37737, by rfl⟩ (by norm_num))
theorem R133421 : Reach 133421 := rs (se 3 (by rfl) ⟨25016, by rfl⟩) (B 50033 (by norm_num) ⟨25016, by rfl⟩ (by norm_num))
theorem R297269 : Reach 297269 := rs (se 5 (by rfl) ⟨13934, by rfl⟩) (B 27869 (by norm_num) ⟨13934, by rfl⟩ (by norm_num))
theorem R166205 : Reach 166205 := rs (se 3 (by rfl) ⟨31163, by rfl⟩) (B 62327 (by norm_num) ⟨31163, by rfl⟩ (by norm_num))
theorem R100669 : Reach 100669 := rs (se 3 (by rfl) ⟨18875, by rfl⟩) (B 37751 (by norm_num) ⟨18875, by rfl⟩ (by norm_num))
theorem R133445 : Reach 133445 := rs (se 4 (by rfl) ⟨12510, by rfl⟩) (B 25021 (by norm_num) ⟨12510, by rfl⟩ (by norm_num))
theorem R198989 : Reach 198989 := rs (se 3 (by rfl) ⟨37310, by rfl⟩) (B 74621 (by norm_num) ⟨37310, by rfl⟩ (by norm_num))
theorem R133469 : Reach 133469 := rs (se 3 (by rfl) ⟨25025, by rfl⟩) (B 50051 (by norm_num) ⟨25025, by rfl⟩ (by norm_num))
theorem R100705 : Reach 100705 := rs (se 2 (by rfl) ⟨37764, by rfl⟩) (B 75529 (by norm_num) ⟨37764, by rfl⟩ (by norm_num))
theorem R133493 : Reach 133493 := rs (se 5 (by rfl) ⟨6257, by rfl⟩) (B 12515 (by norm_num) ⟨6257, by rfl⟩ (by norm_num))
theorem R100741 : Reach 100741 := rs (se 4 (by rfl) ⟨9444, by rfl⟩) (B 18889 (by norm_num) ⟨9444, by rfl⟩ (by norm_num))
theorem R133517 : Reach 133517 := rs (se 3 (by rfl) ⟨25034, by rfl⟩) (B 50069 (by norm_num) ⟨25034, by rfl⟩ (by norm_num))
theorem R199061 : Reach 199061 := rs (se 6 (by rfl) ⟨4665, by rfl⟩) (B 9331 (by norm_num) ⟨4665, by rfl⟩ (by norm_num))
theorem R133541 : Reach 133541 := rs (se 4 (by rfl) ⟨12519, by rfl⟩) (B 25039 (by norm_num) ⟨12519, by rfl⟩ (by norm_num))
theorem R100777 : Reach 100777 := rs (se 2 (by rfl) ⟨37791, by rfl⟩) (B 75583 (by norm_num) ⟨37791, by rfl⟩ (by norm_num))
theorem R133565 : Reach 133565 := rs (se 3 (by rfl) ⟨25043, by rfl⟩) (B 50087 (by norm_num) ⟨25043, by rfl⟩ (by norm_num))
theorem R166349 : Reach 166349 := rs (se 3 (by rfl) ⟨31190, by rfl⟩) (B 62381 (by norm_num) ⟨31190, by rfl⟩ (by norm_num))
theorem R100813 : Reach 100813 := rs (se 3 (by rfl) ⟨18902, by rfl⟩) (B 37805 (by norm_num) ⟨18902, by rfl⟩ (by norm_num))
theorem R133589 : Reach 133589 := rs (se 7 (by rfl) ⟨1565, by rfl⟩) (B 3131 (by norm_num) ⟨1565, by rfl⟩ (by norm_num))
theorem R199133 : Reach 199133 := rs (se 3 (by rfl) ⟨37337, by rfl⟩) (B 74675 (by norm_num) ⟨37337, by rfl⟩ (by norm_num))
theorem R133613 : Reach 133613 := rs (se 3 (by rfl) ⟨25052, by rfl⟩) (B 50105 (by norm_num) ⟨25052, by rfl⟩ (by norm_num))
theorem R100849 : Reach 100849 := rs (se 2 (by rfl) ⟨37818, by rfl⟩) (B 75637 (by norm_num) ⟨37818, by rfl⟩ (by norm_num))
theorem R133637 : Reach 133637 := rs (se 4 (by rfl) ⟨12528, by rfl⟩) (B 25057 (by norm_num) ⟨12528, by rfl⟩ (by norm_num))
theorem R100885 : Reach 100885 := rs (se 6 (by rfl) ⟨2364, by rfl⟩) (B 4729 (by norm_num) ⟨2364, by rfl⟩ (by norm_num))
theorem R133661 : Reach 133661 := rs (se 3 (by rfl) ⟨25061, by rfl⟩) (B 50123 (by norm_num) ⟨25061, by rfl⟩ (by norm_num))
theorem R199205 : Reach 199205 := rs (se 4 (by rfl) ⟨18675, by rfl⟩) (B 37351 (by norm_num) ⟨18675, by rfl⟩ (by norm_num))
theorem R133685 : Reach 133685 := rs (se 5 (by rfl) ⟨6266, by rfl⟩) (B 12533 (by norm_num) ⟨6266, by rfl⟩ (by norm_num))
theorem R100921 : Reach 100921 := rs (se 2 (by rfl) ⟨37845, by rfl⟩) (B 75691 (by norm_num) ⟨37845, by rfl⟩ (by norm_num))
theorem R133709 : Reach 133709 := rs (se 3 (by rfl) ⟨25070, by rfl⟩) (B 50141 (by norm_num) ⟨25070, by rfl⟩ (by norm_num))
theorem R100957 : Reach 100957 := rs (se 3 (by rfl) ⟨18929, by rfl⟩) (B 37859 (by norm_num) ⟨18929, by rfl⟩ (by norm_num))
theorem R133733 : Reach 133733 := rs (se 4 (by rfl) ⟨12537, by rfl⟩) (B 25075 (by norm_num) ⟨12537, by rfl⟩ (by norm_num))
theorem R428645 : Reach 428645 := rs (se 4 (by rfl) ⟨40185, by rfl⟩) (B 80371 (by norm_num) ⟨40185, by rfl⟩ (by norm_num))
theorem R199277 : Reach 199277 := rs (se 3 (by rfl) ⟨37364, by rfl⟩) (B 74729 (by norm_num) ⟨37364, by rfl⟩ (by norm_num))
theorem R133757 : Reach 133757 := rs (se 3 (by rfl) ⟨25079, by rfl⟩) (B 50159 (by norm_num) ⟨25079, by rfl⟩ (by norm_num))
theorem R100993 : Reach 100993 := rs (se 2 (by rfl) ⟨37872, by rfl⟩) (B 75745 (by norm_num) ⟨37872, by rfl⟩ (by norm_num))
theorem R133781 : Reach 133781 := rs (se 6 (by rfl) ⟨3135, by rfl⟩) (B 6271 (by norm_num) ⟨3135, by rfl⟩ (by norm_num))
theorem R101029 : Reach 101029 := rs (se 4 (by rfl) ⟨9471, by rfl⟩) (B 18943 (by norm_num) ⟨9471, by rfl⟩ (by norm_num))
theorem R133805 : Reach 133805 := rs (se 3 (by rfl) ⟨25088, by rfl⟩) (B 50177 (by norm_num) ⟨25088, by rfl⟩ (by norm_num))
theorem R199349 : Reach 199349 := rs (se 5 (by rfl) ⟨9344, by rfl⟩) (B 18689 (by norm_num) ⟨9344, by rfl⟩ (by norm_num))
theorem R133829 : Reach 133829 := rs (se 4 (by rfl) ⟨12546, by rfl⟩) (B 25093 (by norm_num) ⟨12546, by rfl⟩ (by norm_num))
theorem R101065 : Reach 101065 := rs (se 2 (by rfl) ⟨37899, by rfl⟩) (B 75799 (by norm_num) ⟨37899, by rfl⟩ (by norm_num))
theorem R133853 : Reach 133853 := rs (se 3 (by rfl) ⟨25097, by rfl⟩) (B 50195 (by norm_num) ⟨25097, by rfl⟩ (by norm_num))
theorem R297701 : Reach 297701 := rs (se 4 (by rfl) ⟨27909, by rfl⟩) (B 55819 (by norm_num) ⟨27909, by rfl⟩ (by norm_num))
theorem R166637 : Reach 166637 := rs (se 3 (by rfl) ⟨31244, by rfl⟩) (B 62489 (by norm_num) ⟨31244, by rfl⟩ (by norm_num))
theorem R101101 : Reach 101101 := rs (se 3 (by rfl) ⟨18956, by rfl⟩) (B 37913 (by norm_num) ⟨18956, by rfl⟩ (by norm_num))
theorem R133877 : Reach 133877 := rs (se 5 (by rfl) ⟨6275, by rfl⟩) (B 12551 (by norm_num) ⟨6275, by rfl⟩ (by norm_num))
theorem R199421 : Reach 199421 := rs (se 3 (by rfl) ⟨37391, by rfl⟩) (B 74783 (by norm_num) ⟨37391, by rfl⟩ (by norm_num))
theorem R133901 : Reach 133901 := rs (se 3 (by rfl) ⟨25106, by rfl⟩) (B 50213 (by norm_num) ⟨25106, by rfl⟩ (by norm_num))
theorem R101137 : Reach 101137 := rs (se 2 (by rfl) ⟨37926, by rfl⟩) (B 75853 (by norm_num) ⟨37926, by rfl⟩ (by norm_num))
theorem R133925 : Reach 133925 := rs (se 4 (by rfl) ⟨12555, by rfl⟩) (B 25111 (by norm_num) ⟨12555, by rfl⟩ (by norm_num))
theorem R101173 : Reach 101173 := rs (se 5 (by rfl) ⟨4742, by rfl⟩) (B 9485 (by norm_num) ⟨4742, by rfl⟩ (by norm_num))
theorem R133949 : Reach 133949 := rs (se 3 (by rfl) ⟨25115, by rfl⟩) (B 50231 (by norm_num) ⟨25115, by rfl⟩ (by norm_num))
theorem R199493 : Reach 199493 := rs (se 4 (by rfl) ⟨18702, by rfl⟩) (B 37405 (by norm_num) ⟨18702, by rfl⟩ (by norm_num))
theorem R133973 : Reach 133973 := rs (se 9 (by rfl) ⟨392, by rfl⟩) (B 785 (by norm_num) ⟨392, by rfl⟩ (by norm_num))
theorem R101209 : Reach 101209 := rs (se 2 (by rfl) ⟨37953, by rfl⟩) (B 75907 (by norm_num) ⟨37953, by rfl⟩ (by norm_num))
theorem R133997 : Reach 133997 := rs (se 3 (by rfl) ⟨25124, by rfl⟩) (B 50249 (by norm_num) ⟨25124, by rfl⟩ (by norm_num))
theorem R101245 : Reach 101245 := rs (se 3 (by rfl) ⟨18983, by rfl⟩) (B 37967 (by norm_num) ⟨18983, by rfl⟩ (by norm_num))
theorem R166789 : Reach 166789 := rs (se 4 (by rfl) ⟨15636, by rfl⟩) (B 31273 (by norm_num) ⟨15636, by rfl⟩ (by norm_num))
theorem R134021 : Reach 134021 := rs (se 4 (by rfl) ⟨12564, by rfl⟩) (B 25129 (by norm_num) ⟨12564, by rfl⟩ (by norm_num))
theorem R199565 : Reach 199565 := rs (se 3 (by rfl) ⟨37418, by rfl⟩) (B 74837 (by norm_num) ⟨37418, by rfl⟩ (by norm_num))
theorem R134045 : Reach 134045 := rs (se 3 (by rfl) ⟨25133, by rfl⟩) (B 50267 (by norm_num) ⟨25133, by rfl⟩ (by norm_num))
theorem R101281 : Reach 101281 := rs (se 2 (by rfl) ⟨37980, by rfl⟩) (B 75961 (by norm_num) ⟨37980, by rfl⟩ (by norm_num))
theorem R101297 : Reach 101297 := rs (se 2 (by rfl) ⟨37986, by rfl⟩) (B 75973 (by norm_num) ⟨37986, by rfl⟩ (by norm_num))
theorem R134069 : Reach 134069 := rs (se 5 (by rfl) ⟨6284, by rfl⟩) (B 12569 (by norm_num) ⟨6284, by rfl⟩ (by norm_num))
theorem R101317 : Reach 101317 := rs (se 4 (by rfl) ⟨9498, by rfl⟩) (B 18997 (by norm_num) ⟨9498, by rfl⟩ (by norm_num))
theorem R134093 : Reach 134093 := rs (se 3 (by rfl) ⟨25142, by rfl⟩) (B 50285 (by norm_num) ⟨25142, by rfl⟩ (by norm_num))
theorem R199637 : Reach 199637 := rs (se 7 (by rfl) ⟨2339, by rfl⟩) (B 4679 (by norm_num) ⟨2339, by rfl⟩ (by norm_num))
theorem R429029 : Reach 429029 := rs (se 4 (by rfl) ⟨40221, by rfl⟩) (B 80443 (by norm_num) ⟨40221, by rfl⟩ (by norm_num))
theorem R134117 : Reach 134117 := rs (se 4 (by rfl) ⟨12573, by rfl⟩) (B 25147 (by norm_num) ⟨12573, by rfl⟩ (by norm_num))
theorem R330725 : Reach 330725 := rs (se 4 (by rfl) ⟨31005, by rfl⟩) (B 62011 (by norm_num) ⟨31005, by rfl⟩ (by norm_num))
theorem R101353 : Reach 101353 := rs (se 2 (by rfl) ⟨38007, by rfl⟩) (B 76015 (by norm_num) ⟨38007, by rfl⟩ (by norm_num))
theorem R134141 : Reach 134141 := rs (se 3 (by rfl) ⟨25151, by rfl⟩) (B 50303 (by norm_num) ⟨25151, by rfl⟩ (by norm_num))
theorem R101389 : Reach 101389 := rs (se 3 (by rfl) ⟨19010, by rfl⟩) (B 38021 (by norm_num) ⟨19010, by rfl⟩ (by norm_num))
theorem R134165 : Reach 134165 := rs (se 6 (by rfl) ⟨3144, by rfl⟩) (B 6289 (by norm_num) ⟨3144, by rfl⟩ (by norm_num))
theorem R199709 : Reach 199709 := rs (se 3 (by rfl) ⟨37445, by rfl⟩) (B 74891 (by norm_num) ⟨37445, by rfl⟩ (by norm_num))
theorem R134189 : Reach 134189 := rs (se 3 (by rfl) ⟨25160, by rfl⟩) (B 50321 (by norm_num) ⟨25160, by rfl⟩ (by norm_num))
theorem R101425 : Reach 101425 := rs (se 2 (by rfl) ⟨38034, by rfl⟩) (B 76069 (by norm_num) ⟨38034, by rfl⟩ (by norm_num))
theorem R134213 : Reach 134213 := rs (se 4 (by rfl) ⟨12582, by rfl⟩) (B 25165 (by norm_num) ⟨12582, by rfl⟩ (by norm_num))
theorem R101461 : Reach 101461 := rs (se 8 (by rfl) ⟨594, by rfl⟩) (B 1189 (by norm_num) ⟨594, by rfl⟩ (by norm_num))
theorem R134237 : Reach 134237 := rs (se 3 (by rfl) ⟨25169, by rfl⟩) (B 50339 (by norm_num) ⟨25169, by rfl⟩ (by norm_num))
theorem R199781 : Reach 199781 := rs (se 4 (by rfl) ⟨18729, by rfl⟩) (B 37459 (by norm_num) ⟨18729, by rfl⟩ (by norm_num))
theorem R134261 : Reach 134261 := rs (se 5 (by rfl) ⟨6293, by rfl⟩) (B 12587 (by norm_num) ⟨6293, by rfl⟩ (by norm_num))
theorem R101497 : Reach 101497 := rs (se 2 (by rfl) ⟨38061, by rfl⟩) (B 76123 (by norm_num) ⟨38061, by rfl⟩ (by norm_num))
theorem R134285 : Reach 134285 := rs (se 3 (by rfl) ⟨25178, by rfl⟩) (B 50357 (by norm_num) ⟨25178, by rfl⟩ (by norm_num))
theorem R298133 : Reach 298133 := rs (se 6 (by rfl) ⟨6987, by rfl⟩) (B 13975 (by norm_num) ⟨6987, by rfl⟩ (by norm_num))
theorem R101533 : Reach 101533 := rs (se 3 (by rfl) ⟨19037, by rfl⟩) (B 38075 (by norm_num) ⟨19037, by rfl⟩ (by norm_num))
theorem R134309 : Reach 134309 := rs (se 4 (by rfl) ⟨12591, by rfl⟩) (B 25183 (by norm_num) ⟨12591, by rfl⟩ (by norm_num))
theorem R199853 : Reach 199853 := rs (se 3 (by rfl) ⟨37472, by rfl⟩) (B 74945 (by norm_num) ⟨37472, by rfl⟩ (by norm_num))
theorem R167093 : Reach 167093 := rs (se 5 (by rfl) ⟨7832, by rfl⟩) (B 15665 (by norm_num) ⟨7832, by rfl⟩ (by norm_num))
theorem R134333 : Reach 134333 := rs (se 3 (by rfl) ⟨25187, by rfl⟩) (B 50375 (by norm_num) ⟨25187, by rfl⟩ (by norm_num))
theorem R101569 : Reach 101569 := rs (se 2 (by rfl) ⟨38088, by rfl⟩) (B 76177 (by norm_num) ⟨38088, by rfl⟩ (by norm_num))
theorem R134357 : Reach 134357 := rs (se 7 (by rfl) ⟨1574, by rfl⟩) (B 3149 (by norm_num) ⟨1574, by rfl⟩ (by norm_num))
theorem R101605 : Reach 101605 := rs (se 4 (by rfl) ⟨9525, by rfl⟩) (B 19051 (by norm_num) ⟨9525, by rfl⟩ (by norm_num))
theorem R134381 : Reach 134381 := rs (se 3 (by rfl) ⟨25196, by rfl⟩) (B 50393 (by norm_num) ⟨25196, by rfl⟩ (by norm_num))
theorem R199925 : Reach 199925 := rs (se 5 (by rfl) ⟨9371, by rfl⟩) (B 18743 (by norm_num) ⟨9371, by rfl⟩ (by norm_num))
theorem R134389 : Reach 134389 := rs (se 5 (by rfl) ⟨6299, by rfl⟩) (B 12599 (by norm_num) ⟨6299, by rfl⟩ (by norm_num))
theorem R134405 : Reach 134405 := rs (se 4 (by rfl) ⟨12600, by rfl⟩) (B 25201 (by norm_num) ⟨12600, by rfl⟩ (by norm_num))
theorem R101641 : Reach 101641 := rs (se 2 (by rfl) ⟨38115, by rfl⟩) (B 76231 (by norm_num) ⟨38115, by rfl⟩ (by norm_num))
theorem R134429 : Reach 134429 := rs (se 3 (by rfl) ⟨25205, by rfl⟩) (B 50411 (by norm_num) ⟨25205, by rfl⟩ (by norm_num))
theorem R101677 : Reach 101677 := rs (se 3 (by rfl) ⟨19064, by rfl⟩) (B 38129 (by norm_num) ⟨19064, by rfl⟩ (by norm_num))
theorem R134453 : Reach 134453 := rs (se 5 (by rfl) ⟨6302, by rfl⟩) (B 12605 (by norm_num) ⟨6302, by rfl⟩ (by norm_num))
theorem R199997 : Reach 199997 := rs (se 3 (by rfl) ⟨37499, by rfl⟩) (B 74999 (by norm_num) ⟨37499, by rfl⟩ (by norm_num))
theorem R134477 : Reach 134477 := rs (se 3 (by rfl) ⟨25214, by rfl⟩) (B 50429 (by norm_num) ⟨25214, by rfl⟩ (by norm_num))
theorem R101713 : Reach 101713 := rs (se 2 (by rfl) ⟨38142, by rfl⟩) (B 76285 (by norm_num) ⟨38142, by rfl⟩ (by norm_num))
theorem R134501 : Reach 134501 := rs (se 4 (by rfl) ⟨12609, by rfl⟩) (B 25219 (by norm_num) ⟨12609, by rfl⟩ (by norm_num))
theorem R101749 : Reach 101749 := rs (se 5 (by rfl) ⟨4769, by rfl⟩) (B 9539 (by norm_num) ⟨4769, by rfl⟩ (by norm_num))
theorem R134525 : Reach 134525 := rs (se 3 (by rfl) ⟨25223, by rfl⟩) (B 50447 (by norm_num) ⟨25223, by rfl⟩ (by norm_num))
theorem R200069 : Reach 200069 := rs (se 4 (by rfl) ⟨18756, by rfl⟩) (B 37513 (by norm_num) ⟨18756, by rfl⟩ (by norm_num))
theorem R134549 : Reach 134549 := rs (se 6 (by rfl) ⟨3153, by rfl⟩) (B 6307 (by norm_num) ⟨3153, by rfl⟩ (by norm_num))
theorem R101785 : Reach 101785 := rs (se 2 (by rfl) ⟨38169, by rfl⟩) (B 76339 (by norm_num) ⟨38169, by rfl⟩ (by norm_num))
theorem R134573 : Reach 134573 := rs (se 3 (by rfl) ⟨25232, by rfl⟩) (B 50465 (by norm_num) ⟨25232, by rfl⟩ (by norm_num))
theorem R101821 : Reach 101821 := rs (se 3 (by rfl) ⟨19091, by rfl⟩) (B 38183 (by norm_num) ⟨19091, by rfl⟩ (by norm_num))
theorem R134597 : Reach 134597 := rs (se 4 (by rfl) ⟨12618, by rfl⟩) (B 25237 (by norm_num) ⟨12618, by rfl⟩ (by norm_num))
theorem R200141 : Reach 200141 := rs (se 3 (by rfl) ⟨37526, by rfl⟩) (B 75053 (by norm_num) ⟨37526, by rfl⟩ (by norm_num))
theorem R134621 : Reach 134621 := rs (se 3 (by rfl) ⟨25241, by rfl⟩) (B 50483 (by norm_num) ⟨25241, by rfl⟩ (by norm_num))
theorem R101857 : Reach 101857 := rs (se 2 (by rfl) ⟨38196, by rfl⟩) (B 76393 (by norm_num) ⟨38196, by rfl⟩ (by norm_num))
theorem R134645 : Reach 134645 := rs (se 5 (by rfl) ⟨6311, by rfl⟩) (B 12623 (by norm_num) ⟨6311, by rfl⟩ (by norm_num))
theorem R101893 : Reach 101893 := rs (se 4 (by rfl) ⟨9552, by rfl⟩) (B 19105 (by norm_num) ⟨9552, by rfl⟩ (by norm_num))
theorem R134669 : Reach 134669 := rs (se 3 (by rfl) ⟨25250, by rfl⟩) (B 50501 (by norm_num) ⟨25250, by rfl⟩ (by norm_num))
theorem R134677 : Reach 134677 := rs (se 6 (by rfl) ⟨3156, by rfl⟩) (B 6313 (by norm_num) ⟨3156, by rfl⟩ (by norm_num))
theorem R200213 : Reach 200213 := rs (se 6 (by rfl) ⟨4692, by rfl⟩) (B 9385 (by norm_num) ⟨4692, by rfl⟩ (by norm_num))
theorem R134693 : Reach 134693 := rs (se 4 (by rfl) ⟨12627, by rfl⟩) (B 25255 (by norm_num) ⟨12627, by rfl⟩ (by norm_num))
theorem R101929 : Reach 101929 := rs (se 2 (by rfl) ⟨38223, by rfl⟩) (B 76447 (by norm_num) ⟨38223, by rfl⟩ (by norm_num))
theorem R134717 : Reach 134717 := rs (se 3 (by rfl) ⟨25259, by rfl⟩) (B 50519 (by norm_num) ⟨25259, by rfl⟩ (by norm_num))
theorem R298565 : Reach 298565 := rs (se 4 (by rfl) ⟨27990, by rfl⟩) (B 55981 (by norm_num) ⟨27990, by rfl⟩ (by norm_num))
theorem R101965 : Reach 101965 := rs (se 3 (by rfl) ⟨19118, by rfl⟩) (B 38237 (by norm_num) ⟨19118, by rfl⟩ (by norm_num))
theorem R134741 : Reach 134741 := rs (se 8 (by rfl) ⟨789, by rfl⟩) (B 1579 (by norm_num) ⟨789, by rfl⟩ (by norm_num))
theorem R200285 : Reach 200285 := rs (se 3 (by rfl) ⟨37553, by rfl⟩) (B 75107 (by norm_num) ⟨37553, by rfl⟩ (by norm_num))
theorem R134765 : Reach 134765 := rs (se 3 (by rfl) ⟨25268, by rfl⟩) (B 50537 (by norm_num) ⟨25268, by rfl⟩ (by norm_num))
theorem R102001 : Reach 102001 := rs (se 2 (by rfl) ⟨38250, by rfl⟩) (B 76501 (by norm_num) ⟨38250, by rfl⟩ (by norm_num))
theorem R134789 : Reach 134789 := rs (se 4 (by rfl) ⟨12636, by rfl⟩) (B 25273 (by norm_num) ⟨12636, by rfl⟩ (by norm_num))
theorem R102037 : Reach 102037 := rs (se 6 (by rfl) ⟨2391, by rfl⟩) (B 4783 (by norm_num) ⟨2391, by rfl⟩ (by norm_num))
theorem R134813 : Reach 134813 := rs (se 3 (by rfl) ⟨25277, by rfl⟩) (B 50555 (by norm_num) ⟨25277, by rfl⟩ (by norm_num))
theorem R200357 : Reach 200357 := rs (se 4 (by rfl) ⟨18783, by rfl⟩) (B 37567 (by norm_num) ⟨18783, by rfl⟩ (by norm_num))
theorem R134837 : Reach 134837 := rs (se 5 (by rfl) ⟨6320, by rfl⟩) (B 12641 (by norm_num) ⟨6320, by rfl⟩ (by norm_num))
theorem R102073 : Reach 102073 := rs (se 2 (by rfl) ⟨38277, by rfl⟩) (B 76555 (by norm_num) ⟨38277, by rfl⟩ (by norm_num))
theorem R134861 : Reach 134861 := rs (se 3 (by rfl) ⟨25286, by rfl⟩) (B 50573 (by norm_num) ⟨25286, by rfl⟩ (by norm_num))
theorem R102109 : Reach 102109 := rs (se 3 (by rfl) ⟨19145, by rfl⟩) (B 38291 (by norm_num) ⟨19145, by rfl⟩ (by norm_num))
theorem R134885 : Reach 134885 := rs (se 4 (by rfl) ⟨12645, by rfl⟩) (B 25291 (by norm_num) ⟨12645, by rfl⟩ (by norm_num))
theorem R200429 : Reach 200429 := rs (se 3 (by rfl) ⟨37580, by rfl⟩) (B 75161 (by norm_num) ⟨37580, by rfl⟩ (by norm_num))
theorem R134909 : Reach 134909 := rs (se 3 (by rfl) ⟨25295, by rfl⟩) (B 50591 (by norm_num) ⟨25295, by rfl⟩ (by norm_num))
theorem R102145 : Reach 102145 := rs (se 2 (by rfl) ⟨38304, by rfl⟩) (B 76609 (by norm_num) ⟨38304, by rfl⟩ (by norm_num))
theorem R134933 : Reach 134933 := rs (se 6 (by rfl) ⟨3162, by rfl⟩) (B 6325 (by norm_num) ⟨3162, by rfl⟩ (by norm_num))
theorem R102181 : Reach 102181 := rs (se 4 (by rfl) ⟨9579, by rfl⟩) (B 19159 (by norm_num) ⟨9579, by rfl⟩ (by norm_num))
theorem R134957 : Reach 134957 := rs (se 3 (by rfl) ⟨25304, by rfl⟩) (B 50609 (by norm_num) ⟨25304, by rfl⟩ (by norm_num))
theorem R331573 : Reach 331573 := rs (se 5 (by rfl) ⟨15542, by rfl⟩) (B 31085 (by norm_num) ⟨15542, by rfl⟩ (by norm_num))
theorem R200501 : Reach 200501 := rs (se 5 (by rfl) ⟨9398, by rfl⟩) (B 18797 (by norm_num) ⟨9398, by rfl⟩ (by norm_num))
theorem R134981 : Reach 134981 := rs (se 4 (by rfl) ⟨12654, by rfl⟩) (B 25309 (by norm_num) ⟨12654, by rfl⟩ (by norm_num))
theorem R102217 : Reach 102217 := rs (se 2 (by rfl) ⟨38331, by rfl⟩) (B 76663 (by norm_num) ⟨38331, by rfl⟩ (by norm_num))
theorem R1544021 : Reach 1544021 := rs (se 9 (by rfl) ⟨4523, by rfl⟩) (B 9047 (by norm_num) ⟨4523, by rfl⟩ (by norm_num))
theorem R135005 : Reach 135005 := rs (se 3 (by rfl) ⟨25313, by rfl⟩) (B 50627 (by norm_num) ⟨25313, by rfl⟩ (by norm_num))
theorem R102253 : Reach 102253 := rs (se 3 (by rfl) ⟨19172, by rfl⟩) (B 38345 (by norm_num) ⟨19172, by rfl⟩ (by norm_num))
theorem R135029 : Reach 135029 := rs (se 5 (by rfl) ⟨6329, by rfl⟩) (B 12659 (by norm_num) ⟨6329, by rfl⟩ (by norm_num))
theorem R200573 : Reach 200573 := rs (se 3 (by rfl) ⟨37607, by rfl⟩) (B 75215 (by norm_num) ⟨37607, by rfl⟩ (by norm_num))
theorem R135053 : Reach 135053 := rs (se 3 (by rfl) ⟨25322, by rfl⟩) (B 50645 (by norm_num) ⟨25322, by rfl⟩ (by norm_num))
theorem R102289 : Reach 102289 := rs (se 2 (by rfl) ⟨38358, by rfl⟩) (B 76717 (by norm_num) ⟨38358, by rfl⟩ (by norm_num))
theorem R167845 : Reach 167845 := rs (se 4 (by rfl) ⟨15735, by rfl⟩) (B 31471 (by norm_num) ⟨15735, by rfl⟩ (by norm_num))
theorem R135077 : Reach 135077 := rs (se 4 (by rfl) ⟨12663, by rfl⟩) (B 25327 (by norm_num) ⟨12663, by rfl⟩ (by norm_num))
theorem R102313 : Reach 102313 := rs (se 2 (by rfl) ⟨38367, by rfl⟩) (B 76735 (by norm_num) ⟨38367, by rfl⟩ (by norm_num))
theorem R102325 : Reach 102325 := rs (se 5 (by rfl) ⟨4796, by rfl⟩) (B 9593 (by norm_num) ⟨4796, by rfl⟩ (by norm_num))
theorem R135101 : Reach 135101 := rs (se 3 (by rfl) ⟨25331, by rfl⟩) (B 50663 (by norm_num) ⟨25331, by rfl⟩ (by norm_num))
theorem R200645 : Reach 200645 := rs (se 4 (by rfl) ⟨18810, by rfl⟩) (B 37621 (by norm_num) ⟨18810, by rfl⟩ (by norm_num))
theorem R135125 : Reach 135125 := rs (se 7 (by rfl) ⟨1583, by rfl⟩) (B 3167 (by norm_num) ⟨1583, by rfl⟩ (by norm_num))
theorem R102361 : Reach 102361 := rs (se 2 (by rfl) ⟨38385, by rfl⟩) (B 76771 (by norm_num) ⟨38385, by rfl⟩ (by norm_num))
theorem R135149 : Reach 135149 := rs (se 3 (by rfl) ⟨25340, by rfl⟩) (B 50681 (by norm_num) ⟨25340, by rfl⟩ (by norm_num))
theorem R298997 : Reach 298997 := rs (se 5 (by rfl) ⟨14015, by rfl⟩) (B 28031 (by norm_num) ⟨14015, by rfl⟩ (by norm_num))
theorem R102397 : Reach 102397 := rs (se 3 (by rfl) ⟨19199, by rfl⟩) (B 38399 (by norm_num) ⟨19199, by rfl⟩ (by norm_num))
theorem R135173 : Reach 135173 := rs (se 4 (by rfl) ⟨12672, by rfl⟩) (B 25345 (by norm_num) ⟨12672, by rfl⟩ (by norm_num))
theorem R200717 : Reach 200717 := rs (se 3 (by rfl) ⟨37634, by rfl⟩) (B 75269 (by norm_num) ⟨37634, by rfl⟩ (by norm_num))
theorem R135197 : Reach 135197 := rs (se 3 (by rfl) ⟨25349, by rfl⟩) (B 50699 (by norm_num) ⟨25349, by rfl⟩ (by norm_num))
theorem R102433 : Reach 102433 := rs (se 2 (by rfl) ⟨38412, by rfl⟩) (B 76825 (by norm_num) ⟨38412, by rfl⟩ (by norm_num))
theorem R167989 : Reach 167989 := rs (se 5 (by rfl) ⟨7874, by rfl⟩) (B 15749 (by norm_num) ⟨7874, by rfl⟩ (by norm_num))
theorem R135221 : Reach 135221 := rs (se 5 (by rfl) ⟨6338, by rfl⟩) (B 12677 (by norm_num) ⟨6338, by rfl⟩ (by norm_num))
theorem R102469 : Reach 102469 := rs (se 4 (by rfl) ⟨9606, by rfl⟩) (B 19213 (by norm_num) ⟨9606, by rfl⟩ (by norm_num))
theorem R135245 : Reach 135245 := rs (se 3 (by rfl) ⟨25358, by rfl⟩) (B 50717 (by norm_num) ⟨25358, by rfl⟩ (by norm_num))
theorem R200789 : Reach 200789 := rs (se 8 (by rfl) ⟨1176, by rfl⟩) (B 2353 (by norm_num) ⟨1176, by rfl⟩ (by norm_num))
theorem R331877 : Reach 331877 := rs (se 4 (by rfl) ⟨31113, by rfl⟩) (B 62227 (by norm_num) ⟨31113, by rfl⟩ (by norm_num))
theorem R135269 : Reach 135269 := rs (se 4 (by rfl) ⟨12681, by rfl⟩) (B 25363 (by norm_num) ⟨12681, by rfl⟩ (by norm_num))
theorem R102505 : Reach 102505 := rs (se 2 (by rfl) ⟨38439, by rfl⟩) (B 76879 (by norm_num) ⟨38439, by rfl⟩ (by norm_num))
theorem R135293 : Reach 135293 := rs (se 3 (by rfl) ⟨25367, by rfl⟩) (B 50735 (by norm_num) ⟨25367, by rfl⟩ (by norm_num))
theorem R135317 : Reach 135317 := rs (se 6 (by rfl) ⟨3171, by rfl⟩) (B 6343 (by norm_num) ⟨3171, by rfl⟩ (by norm_num))
theorem R200861 : Reach 200861 := rs (se 3 (by rfl) ⟨37661, by rfl⟩) (B 75323 (by norm_num) ⟨37661, by rfl⟩ (by norm_num))
theorem R135341 : Reach 135341 := rs (se 3 (by rfl) ⟨25376, by rfl⟩) (B 50753 (by norm_num) ⟨25376, by rfl⟩ (by norm_num))
theorem R135365 : Reach 135365 := rs (se 4 (by rfl) ⟨12690, by rfl⟩) (B 25381 (by norm_num) ⟨12690, by rfl⟩ (by norm_num))
theorem R168149 : Reach 168149 := rs (se 7 (by rfl) ⟨1970, by rfl⟩) (B 3941 (by norm_num) ⟨1970, by rfl⟩ (by norm_num))
theorem R135389 : Reach 135389 := rs (se 3 (by rfl) ⟨25385, by rfl⟩) (B 50771 (by norm_num) ⟨25385, by rfl⟩ (by norm_num))
theorem R200933 : Reach 200933 := rs (se 4 (by rfl) ⟨18837, by rfl⟩) (B 37675 (by norm_num) ⟨18837, by rfl⟩ (by norm_num))
theorem R135413 : Reach 135413 := rs (se 5 (by rfl) ⟨6347, by rfl⟩) (B 12695 (by norm_num) ⟨6347, by rfl⟩ (by norm_num))
theorem R135437 : Reach 135437 := rs (se 3 (by rfl) ⟨25394, by rfl⟩) (B 50789 (by norm_num) ⟨25394, by rfl⟩ (by norm_num))
theorem R135461 : Reach 135461 := rs (se 4 (by rfl) ⟨12699, by rfl⟩) (B 25399 (by norm_num) ⟨12699, by rfl⟩ (by norm_num))
theorem R201005 : Reach 201005 := rs (se 3 (by rfl) ⟨37688, by rfl⟩) (B 75377 (by norm_num) ⟨37688, by rfl⟩ (by norm_num))
theorem R758069 : Reach 758069 := rs (se 5 (by rfl) ⟨35534, by rfl⟩) (B 71069 (by norm_num) ⟨35534, by rfl⟩ (by norm_num))
theorem R135485 : Reach 135485 := rs (se 3 (by rfl) ⟨25403, by rfl⟩) (B 50807 (by norm_num) ⟨25403, by rfl⟩ (by norm_num))
theorem R135509 : Reach 135509 := rs (se 10 (by rfl) ⟨198, by rfl⟩) (B 397 (by norm_num) ⟨198, by rfl⟩ (by norm_num))
theorem R168293 : Reach 168293 := rs (se 4 (by rfl) ⟨15777, by rfl⟩) (B 31555 (by norm_num) ⟨15777, by rfl⟩ (by norm_num))
theorem R135533 : Reach 135533 := rs (se 3 (by rfl) ⟨25412, by rfl⟩) (B 50825 (by norm_num) ⟨25412, by rfl⟩ (by norm_num))
theorem R201077 : Reach 201077 := rs (se 5 (by rfl) ⟨9425, by rfl⟩) (B 18851 (by norm_num) ⟨9425, by rfl⟩ (by norm_num))
theorem R135557 : Reach 135557 := rs (se 4 (by rfl) ⟨12708, by rfl⟩) (B 25417 (by norm_num) ⟨12708, by rfl⟩ (by norm_num))
theorem R135581 : Reach 135581 := rs (se 3 (by rfl) ⟨25421, by rfl⟩) (B 50843 (by norm_num) ⟨25421, by rfl⟩ (by norm_num))
theorem R299429 : Reach 299429 := rs (se 4 (by rfl) ⟨28071, by rfl⟩) (B 56143 (by norm_num) ⟨28071, by rfl⟩ (by norm_num))
theorem R135605 : Reach 135605 := rs (se 5 (by rfl) ⟨6356, by rfl⟩) (B 12713 (by norm_num) ⟨6356, by rfl⟩ (by norm_num))
theorem R201149 : Reach 201149 := rs (se 3 (by rfl) ⟨37715, by rfl⟩) (B 75431 (by norm_num) ⟨37715, by rfl⟩ (by norm_num))
theorem R135629 : Reach 135629 := rs (se 3 (by rfl) ⟨25430, by rfl⟩) (B 50861 (by norm_num) ⟨25430, by rfl⟩ (by norm_num))
theorem R135653 : Reach 135653 := rs (se 4 (by rfl) ⟨12717, by rfl⟩) (B 25435 (by norm_num) ⟨12717, by rfl⟩ (by norm_num))
theorem R135677 : Reach 135677 := rs (se 3 (by rfl) ⟨25439, by rfl⟩) (B 50879 (by norm_num) ⟨25439, by rfl⟩ (by norm_num))
theorem R201221 : Reach 201221 := rs (se 4 (by rfl) ⟨18864, by rfl⟩) (B 37729 (by norm_num) ⟨18864, by rfl⟩ (by norm_num))
theorem R135701 : Reach 135701 := rs (se 6 (by rfl) ⟨3180, by rfl⟩) (B 6361 (by norm_num) ⟨3180, by rfl⟩ (by norm_num))
theorem R135725 : Reach 135725 := rs (se 3 (by rfl) ⟨25448, by rfl⟩) (B 50897 (by norm_num) ⟨25448, by rfl⟩ (by norm_num))
theorem R135749 : Reach 135749 := rs (se 4 (by rfl) ⟨12726, by rfl⟩) (B 25453 (by norm_num) ⟨12726, by rfl⟩ (by norm_num))
theorem R201293 : Reach 201293 := rs (se 3 (by rfl) ⟨37742, by rfl⟩) (B 75485 (by norm_num) ⟨37742, by rfl⟩ (by norm_num))
theorem R135773 : Reach 135773 := rs (se 3 (by rfl) ⟨25457, by rfl⟩) (B 50915 (by norm_num) ⟨25457, by rfl⟩ (by norm_num))
theorem R135797 : Reach 135797 := rs (se 5 (by rfl) ⟨6365, by rfl⟩) (B 12731 (by norm_num) ⟨6365, by rfl⟩ (by norm_num))
theorem R168581 : Reach 168581 := rs (se 4 (by rfl) ⟨15804, by rfl⟩) (B 31609 (by norm_num) ⟨15804, by rfl⟩ (by norm_num))
theorem R135821 : Reach 135821 := rs (se 3 (by rfl) ⟨25466, by rfl⟩) (B 50933 (by norm_num) ⟨25466, by rfl⟩ (by norm_num))
theorem R201365 : Reach 201365 := rs (se 6 (by rfl) ⟨4719, by rfl⟩) (B 9439 (by norm_num) ⟨4719, by rfl⟩ (by norm_num))
theorem R135845 : Reach 135845 := rs (se 4 (by rfl) ⟨12735, by rfl⟩) (B 25471 (by norm_num) ⟨12735, by rfl⟩ (by norm_num))
theorem R135869 : Reach 135869 := rs (se 3 (by rfl) ⟨25475, by rfl⟩) (B 50951 (by norm_num) ⟨25475, by rfl⟩ (by norm_num))
theorem R135893 : Reach 135893 := rs (se 7 (by rfl) ⟨1592, by rfl⟩) (B 3185 (by norm_num) ⟨1592, by rfl⟩ (by norm_num))
theorem R201437 : Reach 201437 := rs (se 3 (by rfl) ⟨37769, by rfl⟩) (B 75539 (by norm_num) ⟨37769, by rfl⟩ (by norm_num))
theorem R135917 : Reach 135917 := rs (se 3 (by rfl) ⟨25484, by rfl⟩) (B 50969 (by norm_num) ⟨25484, by rfl⟩ (by norm_num))
theorem R135941 : Reach 135941 := rs (se 4 (by rfl) ⟨12744, by rfl⟩) (B 25489 (by norm_num) ⟨12744, by rfl⟩ (by norm_num))
theorem R168733 : Reach 168733 := rs (se 3 (by rfl) ⟨31637, by rfl⟩) (B 63275 (by norm_num) ⟨31637, by rfl⟩ (by norm_num))
theorem R135965 : Reach 135965 := rs (se 3 (by rfl) ⟨25493, by rfl⟩) (B 50987 (by norm_num) ⟨25493, by rfl⟩ (by norm_num))
theorem R201509 : Reach 201509 := rs (se 4 (by rfl) ⟨18891, by rfl⟩) (B 37783 (by norm_num) ⟨18891, by rfl⟩ (by norm_num))
theorem R135989 : Reach 135989 := rs (se 5 (by rfl) ⟨6374, by rfl⟩) (B 12749 (by norm_num) ⟨6374, by rfl⟩ (by norm_num))
theorem R136013 : Reach 136013 := rs (se 3 (by rfl) ⟨25502, by rfl⟩) (B 51005 (by norm_num) ⟨25502, by rfl⟩ (by norm_num))
theorem R299861 : Reach 299861 := rs (se 9 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R2954069 : Reach 2954069 := rs (se 9 (by rfl) ⟨8654, by rfl⟩) (B 17309 (by norm_num) ⟨8654, by rfl⟩ (by norm_num))
theorem R136037 : Reach 136037 := rs (se 4 (by rfl) ⟨12753, by rfl⟩) (B 25507 (by norm_num) ⟨12753, by rfl⟩ (by norm_num))
theorem R201581 : Reach 201581 := rs (se 3 (by rfl) ⟨37796, by rfl⟩) (B 75593 (by norm_num) ⟨37796, by rfl⟩ (by norm_num))
theorem R136061 : Reach 136061 := rs (se 3 (by rfl) ⟨25511, by rfl⟩) (B 51023 (by norm_num) ⟨25511, by rfl⟩ (by norm_num))
theorem R136085 : Reach 136085 := rs (se 6 (by rfl) ⟨3189, by rfl⟩) (B 6379 (by norm_num) ⟨3189, by rfl⟩ (by norm_num))
theorem R136109 : Reach 136109 := rs (se 3 (by rfl) ⟨25520, by rfl⟩) (B 51041 (by norm_num) ⟨25520, by rfl⟩ (by norm_num))
theorem R201653 : Reach 201653 := rs (se 5 (by rfl) ⟨9452, by rfl⟩) (B 18905 (by norm_num) ⟨9452, by rfl⟩ (by norm_num))
theorem R136133 : Reach 136133 := rs (se 4 (by rfl) ⟨12762, by rfl⟩) (B 25525 (by norm_num) ⟨12762, by rfl⟩ (by norm_num))
theorem R136157 : Reach 136157 := rs (se 3 (by rfl) ⟨25529, by rfl⟩) (B 51059 (by norm_num) ⟨25529, by rfl⟩ (by norm_num))
theorem R136181 : Reach 136181 := rs (se 5 (by rfl) ⟨6383, by rfl⟩) (B 12767 (by norm_num) ⟨6383, by rfl⟩ (by norm_num))
theorem R201725 : Reach 201725 := rs (se 3 (by rfl) ⟨37823, by rfl⟩) (B 75647 (by norm_num) ⟨37823, by rfl⟩ (by norm_num))
theorem R136205 : Reach 136205 := rs (se 3 (by rfl) ⟨25538, by rfl⟩) (B 51077 (by norm_num) ⟨25538, by rfl⟩ (by norm_num))
theorem R136229 : Reach 136229 := rs (se 4 (by rfl) ⟨12771, by rfl⟩) (B 25543 (by norm_num) ⟨12771, by rfl⟩ (by norm_num))
theorem R136253 : Reach 136253 := rs (se 3 (by rfl) ⟨25547, by rfl⟩) (B 51095 (by norm_num) ⟨25547, by rfl⟩ (by norm_num))
theorem R201797 : Reach 201797 := rs (se 4 (by rfl) ⟨18918, by rfl⟩) (B 37837 (by norm_num) ⟨18918, by rfl⟩ (by norm_num))
theorem R169037 : Reach 169037 := rs (se 3 (by rfl) ⟨31694, by rfl⟩) (B 63389 (by norm_num) ⟨31694, by rfl⟩ (by norm_num))
theorem R136277 : Reach 136277 := rs (se 8 (by rfl) ⟨798, by rfl⟩) (B 1597 (by norm_num) ⟨798, by rfl⟩ (by norm_num))
theorem R136301 : Reach 136301 := rs (se 3 (by rfl) ⟨25556, by rfl⟩) (B 51113 (by norm_num) ⟨25556, by rfl⟩ (by norm_num))
theorem R136325 : Reach 136325 := rs (se 4 (by rfl) ⟨12780, by rfl⟩) (B 25561 (by norm_num) ⟨12780, by rfl⟩ (by norm_num))
theorem R201869 : Reach 201869 := rs (se 3 (by rfl) ⟨37850, by rfl⟩) (B 75701 (by norm_num) ⟨37850, by rfl⟩ (by norm_num))
theorem R136349 : Reach 136349 := rs (se 3 (by rfl) ⟨25565, by rfl⟩) (B 51131 (by norm_num) ⟨25565, by rfl⟩ (by norm_num))
theorem R136373 : Reach 136373 := rs (se 5 (by rfl) ⟨6392, by rfl⟩) (B 12785 (by norm_num) ⟨6392, by rfl⟩ (by norm_num))
theorem R136397 : Reach 136397 := rs (se 3 (by rfl) ⟨25574, by rfl⟩) (B 51149 (by norm_num) ⟨25574, by rfl⟩ (by norm_num))
theorem R201941 : Reach 201941 := rs (se 7 (by rfl) ⟨2366, by rfl⟩) (B 4733 (by norm_num) ⟨2366, by rfl⟩ (by norm_num))
theorem R136421 : Reach 136421 := rs (se 4 (by rfl) ⟨12789, by rfl⟩) (B 25579 (by norm_num) ⟨12789, by rfl⟩ (by norm_num))
theorem R136445 : Reach 136445 := rs (se 3 (by rfl) ⟨25583, by rfl⟩) (B 51167 (by norm_num) ⟨25583, by rfl⟩ (by norm_num))
theorem R300293 : Reach 300293 := rs (se 4 (by rfl) ⟨28152, by rfl⟩) (B 56305 (by norm_num) ⟨28152, by rfl⟩ (by norm_num))
theorem R136469 : Reach 136469 := rs (se 6 (by rfl) ⟨3198, by rfl⟩) (B 6397 (by norm_num) ⟨3198, by rfl⟩ (by norm_num))
theorem R202013 : Reach 202013 := rs (se 3 (by rfl) ⟨37877, by rfl⟩) (B 75755 (by norm_num) ⟨37877, by rfl⟩ (by norm_num))
theorem R136493 : Reach 136493 := rs (se 3 (by rfl) ⟨25592, by rfl⟩) (B 51185 (by norm_num) ⟨25592, by rfl⟩ (by norm_num))
theorem R136517 : Reach 136517 := rs (se 4 (by rfl) ⟨12798, by rfl⟩) (B 25597 (by norm_num) ⟨12798, by rfl⟩ (by norm_num))
theorem R136541 : Reach 136541 := rs (se 3 (by rfl) ⟨25601, by rfl⟩) (B 51203 (by norm_num) ⟨25601, by rfl⟩ (by norm_num))
theorem R202085 : Reach 202085 := rs (se 4 (by rfl) ⟨18945, by rfl⟩) (B 37891 (by norm_num) ⟨18945, by rfl⟩ (by norm_num))
theorem R136565 : Reach 136565 := rs (se 5 (by rfl) ⟨6401, by rfl⟩) (B 12803 (by norm_num) ⟨6401, by rfl⟩ (by norm_num))
theorem R136589 : Reach 136589 := rs (se 3 (by rfl) ⟨25610, by rfl⟩) (B 51221 (by norm_num) ⟨25610, by rfl⟩ (by norm_num))
theorem R136613 : Reach 136613 := rs (se 4 (by rfl) ⟨12807, by rfl⟩) (B 25615 (by norm_num) ⟨12807, by rfl⟩ (by norm_num))
theorem R202157 : Reach 202157 := rs (se 3 (by rfl) ⟨37904, by rfl⟩) (B 75809 (by norm_num) ⟨37904, by rfl⟩ (by norm_num))
theorem R136637 : Reach 136637 := rs (se 3 (by rfl) ⟨25619, by rfl⟩) (B 51239 (by norm_num) ⟨25619, by rfl⟩ (by norm_num))
theorem R136661 : Reach 136661 := rs (se 7 (by rfl) ⟨1601, by rfl⟩) (B 3203 (by norm_num) ⟨1601, by rfl⟩ (by norm_num))
theorem R136685 : Reach 136685 := rs (se 3 (by rfl) ⟨25628, by rfl⟩) (B 51257 (by norm_num) ⟨25628, by rfl⟩ (by norm_num))
theorem R202229 : Reach 202229 := rs (se 5 (by rfl) ⟨9479, by rfl⟩) (B 18959 (by norm_num) ⟨9479, by rfl⟩ (by norm_num))
theorem R267797 : Reach 267797 := rs (se 6 (by rfl) ⟨6276, by rfl⟩) (B 12553 (by norm_num) ⟨6276, by rfl⟩ (by norm_num))
theorem R202301 : Reach 202301 := rs (se 3 (by rfl) ⟨37931, by rfl⟩) (B 75863 (by norm_num) ⟨37931, by rfl⟩ (by norm_num))
theorem R136765 : Reach 136765 := rs (se 3 (by rfl) ⟨25643, by rfl⟩) (B 51287 (by norm_num) ⟨25643, by rfl⟩ (by norm_num))
theorem R202373 : Reach 202373 := rs (se 4 (by rfl) ⟨18972, by rfl⟩) (B 37945 (by norm_num) ⟨18972, by rfl⟩ (by norm_num))
theorem R857749 : Reach 857749 := rs (se 6 (by rfl) ⟨20103, by rfl⟩) (B 40207 (by norm_num) ⟨20103, by rfl⟩ (by norm_num))
theorem R300725 : Reach 300725 := rs (se 5 (by rfl) ⟨14096, by rfl⟩) (B 28193 (by norm_num) ⟨14096, by rfl⟩ (by norm_num))
theorem R366277 : Reach 366277 := rs (se 4 (by rfl) ⟨34338, by rfl⟩) (B 68677 (by norm_num) ⟨34338, by rfl⟩ (by norm_num))
theorem R202445 : Reach 202445 := rs (se 3 (by rfl) ⟨37958, by rfl⟩) (B 75917 (by norm_num) ⟨37958, by rfl⟩ (by norm_num))
theorem R202517 : Reach 202517 := rs (se 6 (by rfl) ⟨4746, by rfl⟩) (B 9493 (by norm_num) ⟨4746, by rfl⟩ (by norm_num))
theorem R169789 : Reach 169789 := rs (se 3 (by rfl) ⟨31835, by rfl⟩) (B 63671 (by norm_num) ⟨31835, by rfl⟩ (by norm_num))
theorem R202589 : Reach 202589 := rs (se 3 (by rfl) ⟨37985, by rfl⟩) (B 75971 (by norm_num) ⟨37985, by rfl⟩ (by norm_num))
theorem R202661 : Reach 202661 := rs (se 4 (by rfl) ⟨18999, by rfl⟩) (B 37999 (by norm_num) ⟨18999, by rfl⟩ (by norm_num))
theorem R169933 : Reach 169933 := rs (se 3 (by rfl) ⟨31862, by rfl⟩) (B 63725 (by norm_num) ⟨31862, by rfl⟩ (by norm_num))
theorem R202733 : Reach 202733 := rs (se 3 (by rfl) ⟨38012, by rfl⟩) (B 76025 (by norm_num) ⟨38012, by rfl⟩ (by norm_num))
theorem R202805 : Reach 202805 := rs (se 5 (by rfl) ⟨9506, by rfl⟩) (B 19013 (by norm_num) ⟨9506, by rfl⟩ (by norm_num))
theorem R301157 : Reach 301157 := rs (se 4 (by rfl) ⟨28233, by rfl⟩) (B 56467 (by norm_num) ⟨28233, by rfl⟩ (by norm_num))
theorem R170093 : Reach 170093 := rs (se 3 (by rfl) ⟨31892, by rfl⟩) (B 63785 (by norm_num) ⟨31892, by rfl⟩ (by norm_num))
theorem R202877 : Reach 202877 := rs (se 3 (by rfl) ⟨38039, by rfl⟩) (B 76079 (by norm_num) ⟨38039, by rfl⟩ (by norm_num))
theorem R333989 : Reach 333989 := rs (se 4 (by rfl) ⟨31311, by rfl⟩) (B 62623 (by norm_num) ⟨31311, by rfl⟩ (by norm_num))
theorem R202949 : Reach 202949 := rs (se 4 (by rfl) ⟨19026, by rfl⟩) (B 38053 (by norm_num) ⟨19026, by rfl⟩ (by norm_num))
theorem R104701 : Reach 104701 := rs (se 3 (by rfl) ⟨19631, by rfl⟩) (B 39263 (by norm_num) ⟨19631, by rfl⟩ (by norm_num))
theorem R170237 : Reach 170237 := rs (se 3 (by rfl) ⟨31919, by rfl⟩) (B 63839 (by norm_num) ⟨31919, by rfl⟩ (by norm_num))
theorem R203021 : Reach 203021 := rs (se 3 (by rfl) ⟨38066, by rfl⟩) (B 76133 (by norm_num) ⟨38066, by rfl⟩ (by norm_num))
theorem R203093 : Reach 203093 := rs (se 10 (by rfl) ⟨297, by rfl⟩) (B 595 (by norm_num) ⟨297, by rfl⟩ (by norm_num))
theorem R104797 : Reach 104797 := rs (se 3 (by rfl) ⟨19649, by rfl⟩) (B 39299 (by norm_num) ⟨19649, by rfl⟩ (by norm_num))
theorem R203165 : Reach 203165 := rs (se 3 (by rfl) ⟨38093, by rfl⟩) (B 76187 (by norm_num) ⟨38093, by rfl⟩ (by norm_num))
theorem R334277 : Reach 334277 := rs (se 4 (by rfl) ⟨31338, by rfl⟩) (B 62677 (by norm_num) ⟨31338, by rfl⟩ (by norm_num))
theorem R203237 : Reach 203237 := rs (se 4 (by rfl) ⟨19053, by rfl⟩) (B 38107 (by norm_num) ⟨19053, by rfl⟩ (by norm_num))
theorem R301589 : Reach 301589 := rs (se 6 (by rfl) ⟨7068, by rfl⟩) (B 14137 (by norm_num) ⟨7068, by rfl⟩ (by norm_num))
theorem R170525 : Reach 170525 := rs (se 3 (by rfl) ⟨31973, by rfl⟩) (B 63947 (by norm_num) ⟨31973, by rfl⟩ (by norm_num))
theorem R203309 : Reach 203309 := rs (se 3 (by rfl) ⟨38120, by rfl⟩) (B 76241 (by norm_num) ⟨38120, by rfl⟩ (by norm_num))
theorem R662069 : Reach 662069 := rs (se 5 (by rfl) ⟨31034, by rfl⟩) (B 62069 (by norm_num) ⟨31034, by rfl⟩ (by norm_num))
theorem R203381 : Reach 203381 := rs (se 5 (by rfl) ⟨9533, by rfl⟩) (B 19067 (by norm_num) ⟨9533, by rfl⟩ (by norm_num))
theorem R170677 : Reach 170677 := rs (se 5 (by rfl) ⟨8000, by rfl⟩) (B 16001 (by norm_num) ⟨8000, by rfl⟩ (by norm_num))
theorem R203453 : Reach 203453 := rs (se 3 (by rfl) ⟨38147, by rfl⟩) (B 76295 (by norm_num) ⟨38147, by rfl⟩ (by norm_num))
theorem R137933 : Reach 137933 := rs (se 3 (by rfl) ⟨25862, by rfl⟩) (B 51725 (by norm_num) ⟨25862, by rfl⟩ (by norm_num))
theorem R105181 : Reach 105181 := rs (se 3 (by rfl) ⟨19721, by rfl⟩) (B 39443 (by norm_num) ⟨19721, by rfl⟩ (by norm_num))
theorem R203525 : Reach 203525 := rs (se 4 (by rfl) ⟨19080, by rfl⟩) (B 38161 (by norm_num) ⟨19080, by rfl⟩ (by norm_num))
theorem R138029 : Reach 138029 := rs (se 3 (by rfl) ⟨25880, by rfl⟩) (B 51761 (by norm_num) ⟨25880, by rfl⟩ (by norm_num))
theorem R203597 : Reach 203597 := rs (se 3 (by rfl) ⟨38174, by rfl⟩) (B 76349 (by norm_num) ⟨38174, by rfl⟩ (by norm_num))
theorem R170837 : Reach 170837 := rs (se 9 (by rfl) ⟨500, by rfl⟩) (B 1001 (by norm_num) ⟨500, by rfl⟩ (by norm_num))
theorem R203669 : Reach 203669 := rs (se 6 (by rfl) ⟨4773, by rfl⟩) (B 9547 (by norm_num) ⟨4773, by rfl⟩ (by norm_num))
theorem R302021 : Reach 302021 := rs (se 4 (by rfl) ⟨28314, by rfl⟩) (B 56629 (by norm_num) ⟨28314, by rfl⟩ (by norm_num))
theorem R203741 : Reach 203741 := rs (se 3 (by rfl) ⟨38201, by rfl⟩) (B 76403 (by norm_num) ⟨38201, by rfl⟩ (by norm_num))
theorem R170981 : Reach 170981 := rs (se 4 (by rfl) ⟨16029, by rfl⟩) (B 32059 (by norm_num) ⟨16029, by rfl⟩ (by norm_num))
theorem R203813 : Reach 203813 := rs (se 4 (by rfl) ⟨19107, by rfl⟩) (B 38215 (by norm_num) ⟨19107, by rfl⟩ (by norm_num))
theorem R138341 : Reach 138341 := rs (se 4 (by rfl) ⟨12969, by rfl⟩) (B 25939 (by norm_num) ⟨12969, by rfl⟩ (by norm_num))
theorem R203885 : Reach 203885 := rs (se 3 (by rfl) ⟨38228, by rfl⟩) (B 76457 (by norm_num) ⟨38228, by rfl⟩ (by norm_num))
theorem R203957 : Reach 203957 := rs (se 5 (by rfl) ⟨9560, by rfl⟩) (B 19121 (by norm_num) ⟨9560, by rfl⟩ (by norm_num))
theorem R204005 : Reach 204005 := rs (se 4 (by rfl) ⟨19125, by rfl⟩) (B 38251 (by norm_num) ⟨19125, by rfl⟩ (by norm_num))
theorem R204029 : Reach 204029 := rs (se 3 (by rfl) ⟨38255, by rfl⟩) (B 76511 (by norm_num) ⟨38255, by rfl⟩ (by norm_num))
theorem R695573 : Reach 695573 := rs (se 6 (by rfl) ⟨16302, by rfl⟩) (B 32605 (by norm_num) ⟨16302, by rfl⟩ (by norm_num))
theorem R204101 : Reach 204101 := rs (se 4 (by rfl) ⟨19134, by rfl⟩) (B 38269 (by norm_num) ⟨19134, by rfl⟩ (by norm_num))
theorem R204133 : Reach 204133 := rs (se 4 (by rfl) ⟨19137, by rfl⟩) (B 38275 (by norm_num) ⟨19137, by rfl⟩ (by norm_num))
theorem R302453 : Reach 302453 := rs (se 5 (by rfl) ⟨14177, by rfl⟩) (B 28355 (by norm_num) ⟨14177, by rfl⟩ (by norm_num))
theorem R204173 : Reach 204173 := rs (se 3 (by rfl) ⟨38282, by rfl⟩) (B 76565 (by norm_num) ⟨38282, by rfl⟩ (by norm_num))
theorem R204205 : Reach 204205 := rs (se 3 (by rfl) ⟨38288, by rfl⟩) (B 76577 (by norm_num) ⟨38288, by rfl⟩ (by norm_num))
theorem R204245 : Reach 204245 := rs (se 7 (by rfl) ⟨2393, by rfl⟩) (B 4787 (by norm_num) ⟨2393, by rfl⟩ (by norm_num))
theorem R204317 : Reach 204317 := rs (se 3 (by rfl) ⟨38309, by rfl⟩) (B 76619 (by norm_num) ⟨38309, by rfl⟩ (by norm_num))
theorem R335461 : Reach 335461 := rs (se 4 (by rfl) ⟨31449, by rfl⟩) (B 62899 (by norm_num) ⟨31449, by rfl⟩ (by norm_num))
theorem R204389 : Reach 204389 := rs (se 4 (by rfl) ⟨19161, by rfl⟩) (B 38323 (by norm_num) ⟨19161, by rfl⟩ (by norm_num))
theorem R204461 : Reach 204461 := rs (se 3 (by rfl) ⟨38336, by rfl⟩) (B 76673 (by norm_num) ⟨38336, by rfl⟩ (by norm_num))
theorem R171733 : Reach 171733 := rs (se 7 (by rfl) ⟨2012, by rfl⟩) (B 4025 (by norm_num) ⟨2012, by rfl⟩ (by norm_num))
theorem R106229 : Reach 106229 := rs (se 5 (by rfl) ⟨4979, by rfl⟩) (B 9959 (by norm_num) ⟨4979, by rfl⟩ (by norm_num))
theorem R204533 : Reach 204533 := rs (se 5 (by rfl) ⟨9587, by rfl⟩) (B 19175 (by norm_num) ⟨9587, by rfl⟩ (by norm_num))
theorem R302885 : Reach 302885 := rs (se 4 (by rfl) ⟨28395, by rfl⟩) (B 56791 (by norm_num) ⟨28395, by rfl⟩ (by norm_num))
theorem R204605 : Reach 204605 := rs (se 3 (by rfl) ⟨38363, by rfl⟩) (B 76727 (by norm_num) ⟨38363, by rfl⟩ (by norm_num))
theorem R171877 : Reach 171877 := rs (se 4 (by rfl) ⟨16113, by rfl⟩) (B 32227 (by norm_num) ⟨16113, by rfl⟩ (by norm_num))
theorem R204677 : Reach 204677 := rs (se 4 (by rfl) ⟨19188, by rfl⟩) (B 38377 (by norm_num) ⟨19188, by rfl⟩ (by norm_num))
theorem R434069 : Reach 434069 := rs (se 6 (by rfl) ⟨10173, by rfl⟩) (B 20347 (by norm_num) ⟨10173, by rfl⟩ (by norm_num))
theorem R335765 : Reach 335765 := rs (se 6 (by rfl) ⟨7869, by rfl⟩) (B 15739 (by norm_num) ⟨7869, by rfl⟩ (by norm_num))
theorem R204709 : Reach 204709 := rs (se 4 (by rfl) ⟨19191, by rfl⟩) (B 38383 (by norm_num) ⟨19191, by rfl⟩ (by norm_num))
theorem R204749 : Reach 204749 := rs (se 3 (by rfl) ⟨38390, by rfl⟩) (B 76781 (by norm_num) ⟨38390, by rfl⟩ (by norm_num))
theorem R172037 : Reach 172037 := rs (se 4 (by rfl) ⟨16128, by rfl⟩) (B 32257 (by norm_num) ⟨16128, by rfl⟩ (by norm_num))
theorem R204821 : Reach 204821 := rs (se 6 (by rfl) ⟨4800, by rfl⟩) (B 9601 (by norm_num) ⟨4800, by rfl⟩ (by norm_num))
theorem R106537 : Reach 106537 := rs (se 2 (by rfl) ⟨39951, by rfl⟩) (B 79903 (by norm_num) ⟨39951, by rfl⟩ (by norm_num))
theorem R106565 : Reach 106565 := rs (se 4 (by rfl) ⟨9990, by rfl⟩) (B 19981 (by norm_num) ⟨9990, by rfl⟩ (by norm_num))
theorem R204893 : Reach 204893 := rs (se 3 (by rfl) ⟨38417, by rfl⟩) (B 76835 (by norm_num) ⟨38417, by rfl⟩ (by norm_num))
theorem R172181 : Reach 172181 := rs (se 6 (by rfl) ⟨4035, by rfl⟩) (B 8071 (by norm_num) ⟨4035, by rfl⟩ (by norm_num))
theorem R204965 : Reach 204965 := rs (se 4 (by rfl) ⟨19215, by rfl⟩) (B 38431 (by norm_num) ⟨19215, by rfl⟩ (by norm_num))
theorem R303317 : Reach 303317 := rs (se 7 (by rfl) ⟨3554, by rfl⟩) (B 7109 (by norm_num) ⟨3554, by rfl⟩ (by norm_num))
theorem R205037 : Reach 205037 := rs (se 3 (by rfl) ⟨38444, by rfl⟩) (B 76889 (by norm_num) ⟨38444, by rfl⟩ (by norm_num))
theorem R205229 : Reach 205229 := rs (se 3 (by rfl) ⟨38480, by rfl⟩) (B 76961 (by norm_num) ⟨38480, by rfl⟩ (by norm_num))
theorem R172469 : Reach 172469 := rs (se 5 (by rfl) ⟨8084, by rfl⟩) (B 16169 (by norm_num) ⟨8084, by rfl⟩ (by norm_num))
theorem R205301 : Reach 205301 := rs (se 5 (by rfl) ⟨9623, by rfl⟩) (B 19247 (by norm_num) ⟨9623, by rfl⟩ (by norm_num))
theorem R139781 : Reach 139781 := rs (se 4 (by rfl) ⟨13104, by rfl⟩) (B 26209 (by norm_num) ⟨13104, by rfl⟩ (by norm_num))
theorem R107065 : Reach 107065 := rs (se 2 (by rfl) ⟨40149, by rfl⟩) (B 80299 (by norm_num) ⟨40149, by rfl⟩ (by norm_num))
theorem R205373 : Reach 205373 := rs (se 3 (by rfl) ⟨38507, by rfl⟩) (B 77015 (by norm_num) ⟨38507, by rfl⟩ (by norm_num))
theorem R172621 : Reach 172621 := rs (se 3 (by rfl) ⟨32366, by rfl⟩) (B 64733 (by norm_num) ⟨32366, by rfl⟩ (by norm_num))
theorem R139909 : Reach 139909 := rs (se 4 (by rfl) ⟨13116, by rfl⟩) (B 26233 (by norm_num) ⟨13116, by rfl⟩ (by norm_num))
theorem R303749 : Reach 303749 := rs (se 4 (by rfl) ⟨28476, by rfl⟩) (B 56953 (by norm_num) ⟨28476, by rfl⟩ (by norm_num))
theorem R303845 : Reach 303845 := rs (se 4 (by rfl) ⟨28485, by rfl⟩) (B 56971 (by norm_num) ⟨28485, by rfl⟩ (by norm_num))
theorem R107353 : Reach 107353 := rs (se 2 (by rfl) ⟨40257, by rfl⟩) (B 80515 (by norm_num) ⟨40257, by rfl⟩ (by norm_num))
theorem R172925 : Reach 172925 := rs (se 3 (by rfl) ⟨32423, by rfl⟩) (B 64847 (by norm_num) ⟨32423, by rfl⟩ (by norm_num))
theorem R140293 : Reach 140293 := rs (se 4 (by rfl) ⟨13152, by rfl⟩) (B 26305 (by norm_num) ⟨13152, by rfl⟩ (by norm_num))
theorem R304181 : Reach 304181 := rs (se 5 (by rfl) ⟨14258, by rfl⟩) (B 28517 (by norm_num) ⟨14258, by rfl⟩ (by norm_num))
theorem R533749 : Reach 533749 := rs (se 5 (by rfl) ⟨25019, by rfl⟩) (B 50039 (by norm_num) ⟨25019, by rfl⟩ (by norm_num))
theorem R140549 : Reach 140549 := rs (se 4 (by rfl) ⟨13176, by rfl⟩) (B 26353 (by norm_num) ⟨13176, by rfl⟩ (by norm_num))
theorem R959957 : Reach 959957 := rs (se 7 (by rfl) ⟨11249, by rfl⟩) (B 22499 (by norm_num) ⟨11249, by rfl⟩ (by norm_num))
theorem R304613 : Reach 304613 := rs (se 4 (by rfl) ⟨28557, by rfl⟩) (B 57115 (by norm_num) ⟨28557, by rfl⟩ (by norm_num))
theorem R501461 : Reach 501461 := rs (se 7 (by rfl) ⟨5876, by rfl⟩) (B 11753 (by norm_num) ⟨5876, by rfl⟩ (by norm_num))
theorem R403157 : Reach 403157 := rs (se 7 (by rfl) ⟨4724, by rfl⟩) (B 9449 (by norm_num) ⟨4724, by rfl⟩ (by norm_num))
theorem R108253 : Reach 108253 := rs (se 3 (by rfl) ⟨20297, by rfl⟩) (B 40595 (by norm_num) ⟨20297, by rfl⟩ (by norm_num))
theorem R665333 : Reach 665333 := rs (se 5 (by rfl) ⟨31187, by rfl⟩) (B 62375 (by norm_num) ⟨31187, by rfl⟩ (by norm_num))
theorem R305045 : Reach 305045 := rs (se 6 (by rfl) ⟨7149, by rfl⟩) (B 14299 (by norm_num) ⟨7149, by rfl⟩ (by norm_num))
theorem R108445 : Reach 108445 := rs (se 3 (by rfl) ⟨20333, by rfl⟩) (B 40667 (by norm_num) ⟨20333, by rfl⟩ (by norm_num))
theorem R239557 : Reach 239557 := rs (se 4 (by rfl) ⟨22458, by rfl⟩) (B 44917 (by norm_num) ⟨22458, by rfl⟩ (by norm_num))
theorem R206797 : Reach 206797 := rs (se 3 (by rfl) ⟨38774, by rfl⟩) (B 77549 (by norm_num) ⟨38774, by rfl⟩ (by norm_num))
theorem R337877 : Reach 337877 := rs (se 7 (by rfl) ⟨3959, by rfl⟩) (B 7919 (by norm_num) ⟨3959, by rfl⟩ (by norm_num))
theorem R108545 : Reach 108545 := rs (se 2 (by rfl) ⟨40704, by rfl⟩) (B 81409 (by norm_num) ⟨40704, by rfl⟩ (by norm_num))
theorem R141421 : Reach 141421 := rs (se 3 (by rfl) ⟨26516, by rfl⟩) (B 53033 (by norm_num) ⟨26516, by rfl⟩ (by norm_num))
theorem R174269 : Reach 174269 := rs (se 3 (by rfl) ⟨32675, by rfl⟩) (B 65351 (by norm_num) ⟨32675, by rfl⟩ (by norm_num))
theorem R141517 : Reach 141517 := rs (se 3 (by rfl) ⟨26534, by rfl⟩) (B 53069 (by norm_num) ⟨26534, by rfl⟩ (by norm_num))
theorem R338165 : Reach 338165 := rs (se 5 (by rfl) ⟨15851, by rfl⟩) (B 31703 (by norm_num) ⟨15851, by rfl⟩ (by norm_num))
theorem R207125 : Reach 207125 := rs (se 6 (by rfl) ⟨4854, by rfl⟩) (B 9709 (by norm_num) ⟨4854, by rfl⟩ (by norm_num))
theorem R305477 : Reach 305477 := rs (se 4 (by rfl) ⟨28638, by rfl⟩) (B 57277 (by norm_num) ⟨28638, by rfl⟩ (by norm_num))
theorem R141677 : Reach 141677 := rs (se 3 (by rfl) ⟨26564, by rfl⟩) (B 53129 (by norm_num) ⟨26564, by rfl⟩ (by norm_num))
theorem R436853 : Reach 436853 := rs (se 5 (by rfl) ⟨20477, by rfl⟩) (B 40955 (by norm_num) ⟨20477, by rfl⟩ (by norm_num))
theorem R207485 : Reach 207485 := rs (se 3 (by rfl) ⟨38903, by rfl⟩) (B 77807 (by norm_num) ⟨38903, by rfl⟩ (by norm_num))
theorem R305909 : Reach 305909 := rs (se 5 (by rfl) ⟨14339, by rfl⟩) (B 28679 (by norm_num) ⟨14339, by rfl⟩ (by norm_num))
theorem R109333 : Reach 109333 := rs (se 6 (by rfl) ⟨2562, by rfl⟩) (B 5125 (by norm_num) ⟨2562, by rfl⟩ (by norm_num))
theorem R502645 : Reach 502645 := rs (se 5 (by rfl) ⟨23561, by rfl⟩) (B 47123 (by norm_num) ⟨23561, by rfl⟩ (by norm_num))
theorem R240725 : Reach 240725 := rs (se 8 (by rfl) ⟨1410, by rfl⟩) (B 2821 (by norm_num) ⟨1410, by rfl⟩ (by norm_num))
theorem R207973 : Reach 207973 := rs (se 4 (by rfl) ⟨19497, by rfl⟩) (B 38995 (by norm_num) ⟨19497, by rfl⟩ (by norm_num))
theorem R797845 : Reach 797845 := rs (se 6 (by rfl) ⟨18699, by rfl⟩) (B 37399 (by norm_num) ⟨18699, by rfl⟩ (by norm_num))
theorem R306341 : Reach 306341 := rs (se 4 (by rfl) ⟨28719, by rfl⟩) (B 57439 (by norm_num) ⟨28719, by rfl⟩ (by norm_num))
theorem R339349 : Reach 339349 := rs (se 6 (by rfl) ⟨7953, by rfl⟩) (B 15907 (by norm_num) ⟨7953, by rfl⟩ (by norm_num))
theorem R568757 : Reach 568757 := rs (se 5 (by rfl) ⟨26660, by rfl⟩) (B 53321 (by norm_num) ⟨26660, by rfl⟩ (by norm_num))
theorem R142805 : Reach 142805 := rs (se 7 (by rfl) ⟨1673, by rfl⟩) (B 3347 (by norm_num) ⟨1673, by rfl⟩ (by norm_num))
theorem R306773 : Reach 306773 := rs (se 8 (by rfl) ⟨1797, by rfl⟩) (B 3595 (by norm_num) ⟨1797, by rfl⟩ (by norm_num))
theorem R339653 : Reach 339653 := rs (se 4 (by rfl) ⟨31842, by rfl⟩) (B 63685 (by norm_num) ⟨31842, by rfl⟩ (by norm_num))
theorem R110317 : Reach 110317 := rs (se 3 (by rfl) ⟨20684, by rfl⟩) (B 41369 (by norm_num) ⟨20684, by rfl⟩ (by norm_num))
theorem R306965 : Reach 306965 := rs (se 6 (by rfl) ⟨7194, by rfl⟩) (B 14389 (by norm_num) ⟨7194, by rfl⟩ (by norm_num))
theorem R110413 : Reach 110413 := rs (se 3 (by rfl) ⟨20702, by rfl⟩) (B 41405 (by norm_num) ⟨20702, by rfl⟩ (by norm_num))
theorem R143317 : Reach 143317 := rs (se 7 (by rfl) ⟨1679, by rfl⟩) (B 3359 (by norm_num) ⟨1679, by rfl⟩ (by norm_num))
theorem R110585 : Reach 110585 := rs (se 2 (by rfl) ⟨41469, by rfl⟩) (B 82939 (by norm_num) ⟨41469, by rfl⟩ (by norm_num))
theorem R307205 : Reach 307205 := rs (se 4 (by rfl) ⟨28800, by rfl⟩) (B 57601 (by norm_num) ⟨28800, by rfl⟩ (by norm_num))
theorem R110641 : Reach 110641 := rs (se 2 (by rfl) ⟨41490, by rfl⟩) (B 82981 (by norm_num) ⟨41490, by rfl⟩ (by norm_num))
theorem R372869 : Reach 372869 := rs (se 4 (by rfl) ⟨34956, by rfl⟩) (B 69913 (by norm_num) ⟨34956, by rfl⟩ (by norm_num))
theorem R110737 : Reach 110737 := rs (se 2 (by rfl) ⟨41526, by rfl⟩) (B 83053 (by norm_num) ⟨41526, by rfl⟩ (by norm_num))
theorem R110909 : Reach 110909 := rs (se 3 (by rfl) ⟨20795, by rfl⟩) (B 41591 (by norm_num) ⟨20795, by rfl⟩ (by norm_num))
theorem R471413 : Reach 471413 := rs (se 5 (by rfl) ⟨22097, by rfl⟩) (B 44195 (by norm_num) ⟨22097, by rfl⟩ (by norm_num))
theorem R110965 : Reach 110965 := rs (se 5 (by rfl) ⟨5201, by rfl⟩) (B 10403 (by norm_num) ⟨5201, by rfl⟩ (by norm_num))
theorem R373157 : Reach 373157 := rs (se 4 (by rfl) ⟨34983, by rfl⟩) (B 69967 (by norm_num) ⟨34983, by rfl⟩ (by norm_num))
theorem R111061 : Reach 111061 := rs (se 7 (by rfl) ⟨1301, by rfl⟩) (B 2603 (by norm_num) ⟨1301, by rfl⟩ (by norm_num))
theorem R111233 : Reach 111233 := rs (se 2 (by rfl) ⟨41712, by rfl⟩) (B 83425 (by norm_num) ⟨41712, by rfl⟩ (by norm_num))
theorem R111289 : Reach 111289 := rs (se 2 (by rfl) ⟨41733, by rfl⟩) (B 83467 (by norm_num) ⟨41733, by rfl⟩ (by norm_num))
theorem R111385 : Reach 111385 := rs (se 2 (by rfl) ⟨41769, by rfl⟩) (B 83539 (by norm_num) ⟨41769, by rfl⟩ (by norm_num))
theorem R504629 : Reach 504629 := rs (se 5 (by rfl) ⟨23654, by rfl⟩) (B 47309 (by norm_num) ⟨23654, by rfl⟩ (by norm_num))
theorem R144317 : Reach 144317 := rs (se 3 (by rfl) ⟨27059, by rfl⟩) (B 54119 (by norm_num) ⟨27059, by rfl⟩ (by norm_num))
theorem R111557 : Reach 111557 := rs (se 4 (by rfl) ⟨10458, by rfl⟩) (B 20917 (by norm_num) ⟨10458, by rfl⟩ (by norm_num))
theorem R111613 : Reach 111613 := rs (se 3 (by rfl) ⟨20927, by rfl⟩) (B 41855 (by norm_num) ⟨20927, by rfl⟩ (by norm_num))
theorem R472085 : Reach 472085 := rs (se 6 (by rfl) ⟨11064, by rfl⟩) (B 22129 (by norm_num) ⟨11064, by rfl⟩ (by norm_num))
theorem R144445 : Reach 144445 := rs (se 3 (by rfl) ⟨27083, by rfl⟩) (B 54167 (by norm_num) ⟨27083, by rfl⟩ (by norm_num))
theorem R111709 : Reach 111709 := rs (se 3 (by rfl) ⟨20945, by rfl⟩) (B 41891 (by norm_num) ⟨20945, by rfl⟩ (by norm_num))
theorem R144509 : Reach 144509 := rs (se 3 (by rfl) ⟨27095, by rfl⟩) (B 54191 (by norm_num) ⟨27095, by rfl⟩ (by norm_num))
theorem R373909 : Reach 373909 := rs (se 6 (by rfl) ⟨8763, by rfl⟩) (B 17527 (by norm_num) ⟨8763, by rfl⟩ (by norm_num))
theorem R111881 : Reach 111881 := rs (se 2 (by rfl) ⟨41955, by rfl⟩) (B 83911 (by norm_num) ⟨41955, by rfl⟩ (by norm_num))
theorem R111937 : Reach 111937 := rs (se 2 (by rfl) ⟨41976, by rfl⟩) (B 83953 (by norm_num) ⟨41976, by rfl⟩ (by norm_num))
theorem R112033 : Reach 112033 := rs (se 2 (by rfl) ⟨42012, by rfl⟩) (B 84025 (by norm_num) ⟨42012, by rfl⟩ (by norm_num))
theorem R374341 : Reach 374341 := rs (se 4 (by rfl) ⟨35094, by rfl⟩) (B 70189 (by norm_num) ⟨35094, by rfl⟩ (by norm_num))
theorem R112205 : Reach 112205 := rs (se 3 (by rfl) ⟨21038, by rfl⟩) (B 42077 (by norm_num) ⟨21038, by rfl⟩ (by norm_num))
theorem R112261 : Reach 112261 := rs (se 4 (by rfl) ⟨10524, by rfl⟩) (B 21049 (by norm_num) ⟨10524, by rfl⟩ (by norm_num))
theorem R210613 : Reach 210613 := rs (se 5 (by rfl) ⟨9872, by rfl⟩) (B 19745 (by norm_num) ⟨9872, by rfl⟩ (by norm_num))
theorem R308933 : Reach 308933 := rs (se 4 (by rfl) ⟨28962, by rfl⟩) (B 57925 (by norm_num) ⟨28962, by rfl⟩ (by norm_num))
theorem R112357 : Reach 112357 := rs (se 4 (by rfl) ⟨10533, by rfl⟩) (B 21067 (by norm_num) ⟨10533, by rfl⟩ (by norm_num))
theorem R341765 : Reach 341765 := rs (se 4 (by rfl) ⟨32040, by rfl⟩) (B 64081 (by norm_num) ⟨32040, by rfl⟩ (by norm_num))
theorem R177965 : Reach 177965 := rs (se 3 (by rfl) ⟨33368, by rfl⟩) (B 66737 (by norm_num) ⟨33368, by rfl⟩ (by norm_num))
theorem R374645 : Reach 374645 := rs (se 5 (by rfl) ⟨17561, by rfl⟩) (B 35123 (by norm_num) ⟨17561, by rfl⟩ (by norm_num))
theorem R112529 : Reach 112529 := rs (se 2 (by rfl) ⟨42198, by rfl⟩) (B 84397 (by norm_num) ⟨42198, by rfl⟩ (by norm_num))
theorem R112585 : Reach 112585 := rs (se 2 (by rfl) ⟨42219, by rfl⟩) (B 84439 (by norm_num) ⟨42219, by rfl⟩ (by norm_num))
theorem R538613 : Reach 538613 := rs (se 5 (by rfl) ⟨25247, by rfl⟩) (B 50495 (by norm_num) ⟨25247, by rfl⟩ (by norm_num))
theorem R342053 : Reach 342053 := rs (se 4 (by rfl) ⟨32067, by rfl⟩) (B 64135 (by norm_num) ⟨32067, by rfl⟩ (by norm_num))
theorem R112681 : Reach 112681 := rs (se 2 (by rfl) ⟨42255, by rfl⟩) (B 84511 (by norm_num) ⟨42255, by rfl⟩ (by norm_num))
theorem R112685 : Reach 112685 := rs (se 3 (by rfl) ⟨21128, by rfl⟩) (B 42257 (by norm_num) ⟨21128, by rfl⟩ (by norm_num))
theorem R112793 : Reach 112793 := rs (se 2 (by rfl) ⟨42297, by rfl⟩) (B 84595 (by norm_num) ⟨42297, by rfl⟩ (by norm_num))
theorem R112853 : Reach 112853 := rs (se 7 (by rfl) ⟨1322, by rfl⟩) (B 2645 (by norm_num) ⟨1322, by rfl⟩ (by norm_num))
theorem R112909 : Reach 112909 := rs (se 3 (by rfl) ⟨21170, by rfl⟩) (B 42341 (by norm_num) ⟨21170, by rfl⟩ (by norm_num))
theorem R211285 : Reach 211285 := rs (se 10 (by rfl) ⟨309, by rfl⟩) (B 619 (by norm_num) ⟨309, by rfl⟩ (by norm_num))
theorem R113005 : Reach 113005 := rs (se 3 (by rfl) ⟨21188, by rfl⟩) (B 42377 (by norm_num) ⟨21188, by rfl⟩ (by norm_num))
theorem R145829 : Reach 145829 := rs (se 4 (by rfl) ⟨13671, by rfl⟩) (B 27343 (by norm_num) ⟨13671, by rfl⟩ (by norm_num))
theorem R113177 : Reach 113177 := rs (se 2 (by rfl) ⟨42441, by rfl⟩) (B 84883 (by norm_num) ⟨42441, by rfl⟩ (by norm_num))
theorem R145957 : Reach 145957 := rs (se 4 (by rfl) ⟨13683, by rfl⟩) (B 27367 (by norm_num) ⟨13683, by rfl⟩ (by norm_num))
theorem R211517 : Reach 211517 := rs (se 3 (by rfl) ⟨39659, by rfl⟩) (B 79319 (by norm_num) ⟨39659, by rfl⟩ (by norm_num))
theorem R113233 : Reach 113233 := rs (se 2 (by rfl) ⟨42462, by rfl⟩) (B 84925 (by norm_num) ⟨42462, by rfl⟩ (by norm_num))
theorem R1030805 : Reach 1030805 := rs (se 6 (by rfl) ⟨24159, by rfl⟩) (B 48319 (by norm_num) ⟨24159, by rfl⟩ (by norm_num))
theorem R113329 : Reach 113329 := rs (se 2 (by rfl) ⟨42498, by rfl⟩) (B 84997 (by norm_num) ⟨42498, by rfl⟩ (by norm_num))
theorem R211661 : Reach 211661 := rs (se 3 (by rfl) ⟨39686, by rfl⟩) (B 79373 (by norm_num) ⟨39686, by rfl⟩ (by norm_num))
theorem R211709 : Reach 211709 := rs (se 3 (by rfl) ⟨39695, by rfl⟩) (B 79391 (by norm_num) ⟨39695, by rfl⟩ (by norm_num))
theorem R441125 : Reach 441125 := rs (se 4 (by rfl) ⟨41355, by rfl⟩) (B 82711 (by norm_num) ⟨41355, by rfl⟩ (by norm_num))
theorem R113501 : Reach 113501 := rs (se 3 (by rfl) ⟨21281, by rfl⟩) (B 42563 (by norm_num) ⟨21281, by rfl⟩ (by norm_num))
theorem R113557 : Reach 113557 := rs (se 6 (by rfl) ⟨2661, by rfl⟩) (B 5323 (by norm_num) ⟨2661, by rfl⟩ (by norm_num))
theorem R113593 : Reach 113593 := rs (se 2 (by rfl) ⟨42597, by rfl⟩) (B 85195 (by norm_num) ⟨42597, by rfl⟩ (by norm_num))
theorem R506837 : Reach 506837 := rs (se 7 (by rfl) ⟨5939, by rfl⟩) (B 11879 (by norm_num) ⟨5939, by rfl⟩ (by norm_num))
theorem R113653 : Reach 113653 := rs (se 5 (by rfl) ⟨5327, by rfl⟩) (B 10655 (by norm_num) ⟨5327, by rfl⟩ (by norm_num))
theorem R211997 : Reach 211997 := rs (se 3 (by rfl) ⟨39749, by rfl⟩) (B 79499 (by norm_num) ⟨39749, by rfl⟩ (by norm_num))
theorem R113825 : Reach 113825 := rs (se 2 (by rfl) ⟨42684, by rfl⟩) (B 85369 (by norm_num) ⟨42684, by rfl⟩ (by norm_num))
theorem R343237 : Reach 343237 := rs (se 4 (by rfl) ⟨32178, by rfl⟩) (B 64357 (by norm_num) ⟨32178, by rfl⟩ (by norm_num))
theorem R572629 : Reach 572629 := rs (se 7 (by rfl) ⟨6710, by rfl⟩) (B 13421 (by norm_num) ⟨6710, by rfl⟩ (by norm_num))
theorem R113881 : Reach 113881 := rs (se 2 (by rfl) ⟨42705, by rfl⟩) (B 85411 (by norm_num) ⟨42705, by rfl⟩ (by norm_num))
theorem R113977 : Reach 113977 := rs (se 2 (by rfl) ⟨42741, by rfl⟩) (B 85483 (by norm_num) ⟨42741, by rfl⟩ (by norm_num))
theorem R179605 : Reach 179605 := rs (se 6 (by rfl) ⟨4209, by rfl⟩) (B 8419 (by norm_num) ⟨4209, by rfl⟩ (by norm_num))
theorem R114149 : Reach 114149 := rs (se 4 (by rfl) ⟨10701, by rfl⟩) (B 21403 (by norm_num) ⟨10701, by rfl⟩ (by norm_num))
theorem R343541 : Reach 343541 := rs (se 5 (by rfl) ⟨16103, by rfl⟩) (B 32207 (by norm_num) ⟨16103, by rfl⟩ (by norm_num))
theorem R114205 : Reach 114205 := rs (se 3 (by rfl) ⟨21413, by rfl⟩) (B 42827 (by norm_num) ⟨21413, by rfl⟩ (by norm_num))
theorem R114301 : Reach 114301 := rs (se 3 (by rfl) ⟨21431, by rfl⟩) (B 42863 (by norm_num) ⟨21431, by rfl⟩ (by norm_num))
theorem R147109 : Reach 147109 := rs (se 4 (by rfl) ⟨13791, by rfl⟩) (B 27583 (by norm_num) ⟨13791, by rfl⟩ (by norm_num))
theorem R245413 : Reach 245413 := rs (se 4 (by rfl) ⟨23007, by rfl⟩) (B 46015 (by norm_num) ⟨23007, by rfl⟩ (by norm_num))
theorem R147197 : Reach 147197 := rs (se 3 (by rfl) ⟨27599, by rfl⟩) (B 55199 (by norm_num) ⟨27599, by rfl⟩ (by norm_num))
theorem R540437 : Reach 540437 := rs (se 6 (by rfl) ⟨12666, by rfl⟩) (B 25333 (by norm_num) ⟨12666, by rfl⟩ (by norm_num))
theorem R114473 : Reach 114473 := rs (se 2 (by rfl) ⟨42927, by rfl⟩) (B 85855 (by norm_num) ⟨42927, by rfl⟩ (by norm_num))
theorem R114529 : Reach 114529 := rs (se 2 (by rfl) ⟨42948, by rfl⟩) (B 85897 (by norm_num) ⟨42948, by rfl⟩ (by norm_num))
theorem R147325 : Reach 147325 := rs (se 3 (by rfl) ⟨27623, by rfl⟩) (B 55247 (by norm_num) ⟨27623, by rfl⟩ (by norm_num))
theorem R114625 : Reach 114625 := rs (se 2 (by rfl) ⟨42984, by rfl⟩) (B 85969 (by norm_num) ⟨42984, by rfl⟩ (by norm_num))
theorem R147413 : Reach 147413 := rs (se 7 (by rfl) ⟨1727, by rfl⟩) (B 3455 (by norm_num) ⟨1727, by rfl⟩ (by norm_num))
theorem R442421 : Reach 442421 := rs (se 5 (by rfl) ⟨20738, by rfl⟩) (B 41477 (by norm_num) ⟨20738, by rfl⟩ (by norm_num))
theorem R147541 : Reach 147541 := rs (se 8 (by rfl) ⟨864, by rfl⟩) (B 1729 (by norm_num) ⟨864, by rfl⟩ (by norm_num))
theorem R114797 : Reach 114797 := rs (se 3 (by rfl) ⟨21524, by rfl⟩) (B 43049 (by norm_num) ⟨21524, by rfl⟩ (by norm_num))
theorem R114853 : Reach 114853 := rs (se 4 (by rfl) ⟨10767, by rfl⟩) (B 21535 (by norm_num) ⟨10767, by rfl⟩ (by norm_num))
theorem R147629 : Reach 147629 := rs (se 3 (by rfl) ⟨27680, by rfl⟩) (B 55361 (by norm_num) ⟨27680, by rfl⟩ (by norm_num))
theorem R114949 : Reach 114949 := rs (se 4 (by rfl) ⟨10776, by rfl⟩) (B 21553 (by norm_num) ⟨10776, by rfl⟩ (by norm_num))
theorem R147757 : Reach 147757 := rs (se 3 (by rfl) ⟨27704, by rfl⟩) (B 55409 (by norm_num) ⟨27704, by rfl⟩ (by norm_num))
theorem R147845 : Reach 147845 := rs (se 4 (by rfl) ⟨13860, by rfl⟩) (B 27721 (by norm_num) ⟨13860, by rfl⟩ (by norm_num))
theorem R115121 : Reach 115121 := rs (se 2 (by rfl) ⟨43170, by rfl⟩) (B 86341 (by norm_num) ⟨43170, by rfl⟩ (by norm_num))
theorem R115177 : Reach 115177 := rs (se 2 (by rfl) ⟨43191, by rfl⟩) (B 86383 (by norm_num) ⟨43191, by rfl⟩ (by norm_num))
theorem R147973 : Reach 147973 := rs (se 4 (by rfl) ⟨13872, by rfl⟩) (B 27745 (by norm_num) ⟨13872, by rfl⟩ (by norm_num))
theorem R115273 : Reach 115273 := rs (se 2 (by rfl) ⟨43227, by rfl⟩) (B 86455 (by norm_num) ⟨43227, by rfl⟩ (by norm_num))
theorem R148061 : Reach 148061 := rs (se 3 (by rfl) ⟨27761, by rfl⟩) (B 55523 (by norm_num) ⟨27761, by rfl⟩ (by norm_num))
theorem R180949 : Reach 180949 := rs (se 7 (by rfl) ⟨2120, by rfl⟩) (B 4241 (by norm_num) ⟨2120, by rfl⟩ (by norm_num))
theorem R148189 : Reach 148189 := rs (se 3 (by rfl) ⟨27785, by rfl⟩) (B 55571 (by norm_num) ⟨27785, by rfl⟩ (by norm_num))
theorem R148277 : Reach 148277 := rs (se 5 (by rfl) ⟨6950, by rfl⟩) (B 13901 (by norm_num) ⟨6950, by rfl⟩ (by norm_num))
theorem R148405 : Reach 148405 := rs (se 5 (by rfl) ⟨6956, by rfl⟩) (B 13913 (by norm_num) ⟨6956, by rfl⟩ (by norm_num))
theorem R148493 : Reach 148493 := rs (se 3 (by rfl) ⟨27842, by rfl⟩) (B 55685 (by norm_num) ⟨27842, by rfl⟩ (by norm_num))
theorem R377941 : Reach 377941 := rs (se 8 (by rfl) ⟨2214, by rfl⟩) (B 4429 (by norm_num) ⟨2214, by rfl⟩ (by norm_num))
theorem R148621 : Reach 148621 := rs (se 3 (by rfl) ⟨27866, by rfl⟩) (B 55733 (by norm_num) ⟨27866, by rfl⟩ (by norm_num))
theorem R181397 : Reach 181397 := rs (se 6 (by rfl) ⟨4251, by rfl⟩) (B 8503 (by norm_num) ⟨4251, by rfl⟩ (by norm_num))
theorem R148709 : Reach 148709 := rs (se 4 (by rfl) ⟨13941, by rfl⟩) (B 27883 (by norm_num) ⟨13941, by rfl⟩ (by norm_num))
theorem R443717 : Reach 443717 := rs (se 4 (by rfl) ⟨41598, by rfl⟩) (B 83197 (by norm_num) ⟨41598, by rfl⟩ (by norm_num))
theorem R673109 : Reach 673109 := rs (se 12 (by rfl) ⟨246, by rfl⟩) (B 493 (by norm_num) ⟨246, by rfl⟩ (by norm_num))
theorem R148837 : Reach 148837 := rs (se 4 (by rfl) ⟨13953, by rfl⟩) (B 27907 (by norm_num) ⟨13953, by rfl⟩ (by norm_num))
theorem R247157 : Reach 247157 := rs (se 5 (by rfl) ⟨11585, by rfl⟩) (B 23171 (by norm_num) ⟨11585, by rfl⟩ (by norm_num))
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) (B 68117 (by norm_num) ⟨34058, by rfl⟩ (by norm_num))
theorem R607637 : Reach 607637 := rs (se 6 (by rfl) ⟨14241, by rfl⟩) (B 28483 (by norm_num) ⟨14241, by rfl⟩ (by norm_num))
theorem R214429 : Reach 214429 := rs (se 3 (by rfl) ⟨40205, by rfl⟩) (B 80411 (by norm_num) ⟨40205, by rfl⟩ (by norm_num))
theorem R148925 : Reach 148925 := rs (se 3 (by rfl) ⟨27923, by rfl⟩) (B 55847 (by norm_num) ⟨27923, by rfl⟩ (by norm_num))
theorem R1066517 : Reach 1066517 := rs (se 6 (by rfl) ⟨24996, by rfl⟩) (B 49993 (by norm_num) ⟨24996, by rfl⟩ (by norm_num))
theorem R345653 : Reach 345653 := rs (se 5 (by rfl) ⟨16202, by rfl⟩) (B 32405 (by norm_num) ⟨16202, by rfl⟩ (by norm_num))
theorem R149053 : Reach 149053 := rs (se 3 (by rfl) ⟨27947, by rfl⟩) (B 55895 (by norm_num) ⟨27947, by rfl⟩ (by norm_num))
theorem R673429 : Reach 673429 := rs (se 6 (by rfl) ⟨15783, by rfl⟩) (B 31567 (by norm_num) ⟨15783, by rfl⟩ (by norm_num))
theorem R149141 : Reach 149141 := rs (se 6 (by rfl) ⟨3495, by rfl⟩) (B 6991 (by norm_num) ⟨3495, by rfl⟩ (by norm_num))
theorem R149269 : Reach 149269 := rs (se 6 (by rfl) ⟨3498, by rfl⟩) (B 6997 (by norm_num) ⟨3498, by rfl⟩ (by norm_num))
theorem R345941 : Reach 345941 := rs (se 9 (by rfl) ⟨1013, by rfl⟩) (B 2027 (by norm_num) ⟨1013, by rfl⟩ (by norm_num))
theorem R149357 : Reach 149357 := rs (se 3 (by rfl) ⟨28004, by rfl⟩) (B 56009 (by norm_num) ⟨28004, by rfl⟩ (by norm_num))
theorem R247781 : Reach 247781 := rs (se 4 (by rfl) ⟨23229, by rfl⟩) (B 46459 (by norm_num) ⟨23229, by rfl⟩ (by norm_num))
theorem R149485 : Reach 149485 := rs (se 3 (by rfl) ⟨28028, by rfl⟩) (B 56057 (by norm_num) ⟨28028, by rfl⟩ (by norm_num))
theorem R870389 : Reach 870389 := rs (se 5 (by rfl) ⟨40799, by rfl⟩) (B 81599 (by norm_num) ⟨40799, by rfl⟩ (by norm_num))
theorem R215045 : Reach 215045 := rs (se 4 (by rfl) ⟨20160, by rfl⟩) (B 40321 (by norm_num) ⟨20160, by rfl⟩ (by norm_num))
theorem R149573 : Reach 149573 := rs (se 4 (by rfl) ⟨14022, by rfl⟩) (B 28045 (by norm_num) ⟨14022, by rfl⟩ (by norm_num))
theorem R149701 : Reach 149701 := rs (se 4 (by rfl) ⟨14034, by rfl⟩) (B 28069 (by norm_num) ⟨14034, by rfl⟩ (by norm_num))
theorem R215245 : Reach 215245 := rs (se 3 (by rfl) ⟨40358, by rfl⟩) (B 80717 (by norm_num) ⟨40358, by rfl⟩ (by norm_num))
theorem R149789 : Reach 149789 := rs (se 3 (by rfl) ⟨28085, by rfl⟩) (B 56171 (by norm_num) ⟨28085, by rfl⟩ (by norm_num))
theorem R149917 : Reach 149917 := rs (se 3 (by rfl) ⟨28109, by rfl⟩) (B 56219 (by norm_num) ⟨28109, by rfl⟩ (by norm_num))
theorem R182741 : Reach 182741 := rs (se 7 (by rfl) ⟨2141, by rfl⟩) (B 4283 (by norm_num) ⟨2141, by rfl⟩ (by norm_num))
theorem R182749 : Reach 182749 := rs (se 3 (by rfl) ⟨34265, by rfl⟩) (B 68531 (by norm_num) ⟨34265, by rfl⟩ (by norm_num))
theorem R150005 : Reach 150005 := rs (se 5 (by rfl) ⟨7031, by rfl⟩) (B 14063 (by norm_num) ⟨7031, by rfl⟩ (by norm_num))
theorem R445013 : Reach 445013 := rs (se 8 (by rfl) ⟨2607, by rfl⟩) (B 5215 (by norm_num) ⟨2607, by rfl⟩ (by norm_num))
theorem R150133 : Reach 150133 := rs (se 5 (by rfl) ⟨7037, by rfl⟩) (B 14075 (by norm_num) ⟨7037, by rfl⟩ (by norm_num))
theorem R248453 : Reach 248453 := rs (se 4 (by rfl) ⟨23292, by rfl⟩) (B 46585 (by norm_num) ⟨23292, by rfl⟩ (by norm_num))
theorem R1493653 : Reach 1493653 := rs (se 6 (by rfl) ⟨35007, by rfl⟩) (B 70015 (by norm_num) ⟨35007, by rfl⟩ (by norm_num))
theorem R150221 : Reach 150221 := rs (se 3 (by rfl) ⟨28166, by rfl⟩) (B 56333 (by norm_num) ⟨28166, by rfl⟩ (by norm_num))
theorem R150349 : Reach 150349 := rs (se 3 (by rfl) ⟨28190, by rfl⟩) (B 56381 (by norm_num) ⟨28190, by rfl⟩ (by norm_num))
theorem R150437 : Reach 150437 := rs (se 4 (by rfl) ⟨14103, by rfl⟩) (B 28207 (by norm_num) ⟨14103, by rfl⟩ (by norm_num))
theorem R216053 : Reach 216053 := rs (se 5 (by rfl) ⟨10127, by rfl⟩) (B 20255 (by norm_num) ⟨10127, by rfl⟩ (by norm_num))
theorem R150565 : Reach 150565 := rs (se 4 (by rfl) ⟨14115, by rfl⟩) (B 28231 (by norm_num) ⟨14115, by rfl⟩ (by norm_num))
theorem R150653 : Reach 150653 := rs (se 3 (by rfl) ⟨28247, by rfl⟩) (B 56495 (by norm_num) ⟨28247, by rfl⟩ (by norm_num))
theorem R150781 : Reach 150781 := rs (se 3 (by rfl) ⟨28271, by rfl⟩) (B 56543 (by norm_num) ⟨28271, by rfl⟩ (by norm_num))
theorem R150869 : Reach 150869 := rs (se 11 (by rfl) ⟨110, by rfl⟩) (B 221 (by norm_num) ⟨110, by rfl⟩ (by norm_num))
theorem R150997 : Reach 150997 := rs (se 7 (by rfl) ⟨1769, by rfl⟩) (B 3539 (by norm_num) ⟨1769, by rfl⟩ (by norm_num))
theorem R151085 : Reach 151085 := rs (se 3 (by rfl) ⟨28328, by rfl⟩) (B 56657 (by norm_num) ⟨28328, by rfl⟩ (by norm_num))
theorem R151213 : Reach 151213 := rs (se 3 (by rfl) ⟨28352, by rfl⟩) (B 56705 (by norm_num) ⟨28352, by rfl⟩ (by norm_num))
theorem R216821 : Reach 216821 := rs (se 5 (by rfl) ⟨10163, by rfl⟩) (B 20327 (by norm_num) ⟨10163, by rfl⟩ (by norm_num))
theorem R151301 : Reach 151301 := rs (se 4 (by rfl) ⟨14184, by rfl⟩) (B 28369 (by norm_num) ⟨14184, by rfl⟩ (by norm_num))
theorem R249637 : Reach 249637 := rs (se 4 (by rfl) ⟨23403, by rfl⟩) (B 46807 (by norm_num) ⟨23403, by rfl⟩ (by norm_num))
theorem R446309 : Reach 446309 := rs (se 4 (by rfl) ⟨41841, by rfl⟩) (B 83683 (by norm_num) ⟨41841, by rfl⟩ (by norm_num))
theorem R151429 : Reach 151429 := rs (se 4 (by rfl) ⟨14196, by rfl⟩) (B 28393 (by norm_num) ⟨14196, by rfl⟩ (by norm_num))
theorem R282533 : Reach 282533 := rs (se 4 (by rfl) ⟨26487, by rfl⟩) (B 52975 (by norm_num) ⟨26487, by rfl⟩ (by norm_num))
theorem R249797 : Reach 249797 := rs (se 4 (by rfl) ⟨23418, by rfl⟩) (B 46837 (by norm_num) ⟨23418, by rfl⟩ (by norm_num))
theorem R151517 : Reach 151517 := rs (se 3 (by rfl) ⟨28409, by rfl⟩) (B 56819 (by norm_num) ⟨28409, by rfl⟩ (by norm_num))
theorem R380933 : Reach 380933 := rs (se 4 (by rfl) ⟨35712, by rfl⟩) (B 71425 (by norm_num) ⟨35712, by rfl⟩ (by norm_num))
theorem R151645 : Reach 151645 := rs (se 3 (by rfl) ⟨28433, by rfl⟩) (B 56867 (by norm_num) ⟨28433, by rfl⟩ (by norm_num))
theorem R250037 : Reach 250037 := rs (se 5 (by rfl) ⟨11720, by rfl⟩) (B 23441 (by norm_num) ⟨11720, by rfl⟩ (by norm_num))
theorem R151733 : Reach 151733 := rs (se 5 (by rfl) ⟨7112, by rfl⟩) (B 14225 (by norm_num) ⟨7112, by rfl⟩ (by norm_num))
theorem R413957 : Reach 413957 := rs (se 4 (by rfl) ⟨38808, by rfl⟩) (B 77617 (by norm_num) ⟨38808, by rfl⟩ (by norm_num))
theorem R151861 : Reach 151861 := rs (se 5 (by rfl) ⟨7118, by rfl⟩) (B 14237 (by norm_num) ⟨7118, by rfl⟩ (by norm_num))
theorem R250229 : Reach 250229 := rs (se 5 (by rfl) ⟨11729, by rfl⟩) (B 23459 (by norm_num) ⟨11729, by rfl⟩ (by norm_num))
theorem R119173 : Reach 119173 := rs (se 4 (by rfl) ⟨11172, by rfl⟩) (B 22345 (by norm_num) ⟨11172, by rfl⟩ (by norm_num))
theorem R151949 : Reach 151949 := rs (se 3 (by rfl) ⟨28490, by rfl⟩) (B 56981 (by norm_num) ⟨28490, by rfl⟩ (by norm_num))
theorem R152077 : Reach 152077 := rs (se 3 (by rfl) ⟨28514, by rfl⟩) (B 57029 (by norm_num) ⟨28514, by rfl⟩ (by norm_num))
theorem R348725 : Reach 348725 := rs (se 5 (by rfl) ⟨16346, by rfl⟩) (B 32693 (by norm_num) ⟨16346, by rfl⟩ (by norm_num))
theorem R152165 : Reach 152165 := rs (se 4 (by rfl) ⟨14265, by rfl⟩) (B 28531 (by norm_num) ⟨14265, by rfl⟩ (by norm_num))
theorem R152293 : Reach 152293 := rs (se 4 (by rfl) ⟨14277, by rfl⟩) (B 28555 (by norm_num) ⟨14277, by rfl⟩ (by norm_num))
theorem R283445 : Reach 283445 := rs (se 5 (by rfl) ⟨13286, by rfl⟩) (B 26573 (by norm_num) ⟨13286, by rfl⟩ (by norm_num))
theorem R152381 : Reach 152381 := rs (se 3 (by rfl) ⟨28571, by rfl⟩) (B 57143 (by norm_num) ⟨28571, by rfl⟩ (by norm_num))
theorem R152437 : Reach 152437 := rs (se 5 (by rfl) ⟨7145, by rfl⟩) (B 14291 (by norm_num) ⟨7145, by rfl⟩ (by norm_num))
theorem R152509 : Reach 152509 := rs (se 3 (by rfl) ⟨28595, by rfl⟩) (B 57191 (by norm_num) ⟨28595, by rfl⟩ (by norm_num))
theorem R381941 : Reach 381941 := rs (se 5 (by rfl) ⟨17903, by rfl⟩) (B 35807 (by norm_num) ⟨17903, by rfl⟩ (by norm_num))
theorem R152597 : Reach 152597 := rs (se 6 (by rfl) ⟨3576, by rfl⟩) (B 7153 (by norm_num) ⟨3576, by rfl⟩ (by norm_num))
theorem R87129 : Reach 87129 := rs (se 2 (by rfl) ⟨32673, by rfl⟩) (B 65347 (by norm_num) ⟨32673, by rfl⟩ (by norm_num))
theorem R87133 : Reach 87133 := rs (se 3 (by rfl) ⟨16337, by rfl⟩) (B 32675 (by norm_num) ⟨16337, by rfl⟩ (by norm_num))
theorem R87137 : Reach 87137 := rs (se 2 (by rfl) ⟨32676, by rfl⟩) (B 65353 (by norm_num) ⟨32676, by rfl⟩ (by norm_num))
theorem R87141 : Reach 87141 := rs (se 4 (by rfl) ⟨8169, by rfl⟩) (B 16339 (by norm_num) ⟨8169, by rfl⟩ (by norm_num))
theorem R87145 : Reach 87145 := rs (se 2 (by rfl) ⟨32679, by rfl⟩) (B 65359 (by norm_num) ⟨32679, by rfl⟩ (by norm_num))
theorem R87149 : Reach 87149 := rs (se 3 (by rfl) ⟨16340, by rfl⟩) (B 32681 (by norm_num) ⟨16340, by rfl⟩ (by norm_num))
theorem R87153 : Reach 87153 := rs (se 2 (by rfl) ⟨32682, by rfl⟩) (B 65365 (by norm_num) ⟨32682, by rfl⟩ (by norm_num))
theorem R87157 : Reach 87157 := rs (se 5 (by rfl) ⟨4085, by rfl⟩) (B 8171 (by norm_num) ⟨4085, by rfl⟩ (by norm_num))
theorem R447605 : Reach 447605 := rs (se 5 (by rfl) ⟨20981, by rfl⟩) (B 41963 (by norm_num) ⟨20981, by rfl⟩ (by norm_num))
theorem R87161 : Reach 87161 := rs (se 2 (by rfl) ⟨32685, by rfl⟩) (B 65371 (by norm_num) ⟨32685, by rfl⟩ (by norm_num))
theorem R87165 : Reach 87165 := rs (se 3 (by rfl) ⟨16343, by rfl⟩) (B 32687 (by norm_num) ⟨16343, by rfl⟩ (by norm_num))
theorem R87169 : Reach 87169 := rs (se 2 (by rfl) ⟨32688, by rfl⟩) (B 65377 (by norm_num) ⟨32688, by rfl⟩ (by norm_num))
theorem R87173 : Reach 87173 := rs (se 4 (by rfl) ⟨8172, by rfl⟩) (B 16345 (by norm_num) ⟨8172, by rfl⟩ (by norm_num))
theorem R87177 : Reach 87177 := rs (se 2 (by rfl) ⟨32691, by rfl⟩) (B 65383 (by norm_num) ⟨32691, by rfl⟩ (by norm_num))
theorem R87181 : Reach 87181 := rs (se 3 (by rfl) ⟨16346, by rfl⟩) (B 32693 (by norm_num) ⟨16346, by rfl⟩ (by norm_num))
theorem R87185 : Reach 87185 := rs (se 2 (by rfl) ⟨32694, by rfl⟩) (B 65389 (by norm_num) ⟨32694, by rfl⟩ (by norm_num))
theorem R87189 : Reach 87189 := rs (se 6 (by rfl) ⟨2043, by rfl⟩) (B 4087 (by norm_num) ⟨2043, by rfl⟩ (by norm_num))
theorem R152725 : Reach 152725 := rs (se 6 (by rfl) ⟨3579, by rfl⟩) (B 7159 (by norm_num) ⟨3579, by rfl⟩ (by norm_num))
theorem R87193 : Reach 87193 := rs (se 2 (by rfl) ⟨32697, by rfl⟩) (B 65395 (by norm_num) ⟨32697, by rfl⟩ (by norm_num))
theorem R87197 : Reach 87197 := rs (se 3 (by rfl) ⟨16349, by rfl⟩) (B 32699 (by norm_num) ⟨16349, by rfl⟩ (by norm_num))
theorem R87201 : Reach 87201 := rs (se 2 (by rfl) ⟨32700, by rfl⟩) (B 65401 (by norm_num) ⟨32700, by rfl⟩ (by norm_num))
theorem R87205 : Reach 87205 := rs (se 4 (by rfl) ⟨8175, by rfl⟩) (B 16351 (by norm_num) ⟨8175, by rfl⟩ (by norm_num))
theorem R87209 : Reach 87209 := rs (se 2 (by rfl) ⟨32703, by rfl⟩) (B 65407 (by norm_num) ⟨32703, by rfl⟩ (by norm_num))
theorem R87213 : Reach 87213 := rs (se 3 (by rfl) ⟨16352, by rfl⟩) (B 32705 (by norm_num) ⟨16352, by rfl⟩ (by norm_num))
theorem R87217 : Reach 87217 := rs (se 2 (by rfl) ⟨32706, by rfl⟩) (B 65413 (by norm_num) ⟨32706, by rfl⟩ (by norm_num))
theorem R87221 : Reach 87221 := rs (se 5 (by rfl) ⟨4088, by rfl⟩) (B 8177 (by norm_num) ⟨4088, by rfl⟩ (by norm_num))
theorem R87225 : Reach 87225 := rs (se 2 (by rfl) ⟨32709, by rfl⟩) (B 65419 (by norm_num) ⟨32709, by rfl⟩ (by norm_num))
theorem R87229 : Reach 87229 := rs (se 3 (by rfl) ⟨16355, by rfl⟩) (B 32711 (by norm_num) ⟨16355, by rfl⟩ (by norm_num))
theorem R87233 : Reach 87233 := rs (se 2 (by rfl) ⟨32712, by rfl⟩) (B 65425 (by norm_num) ⟨32712, by rfl⟩ (by norm_num))
theorem R87237 : Reach 87237 := rs (se 4 (by rfl) ⟨8178, by rfl⟩) (B 16357 (by norm_num) ⟨8178, by rfl⟩ (by norm_num))
theorem R87241 : Reach 87241 := rs (se 2 (by rfl) ⟨32715, by rfl⟩) (B 65431 (by norm_num) ⟨32715, by rfl⟩ (by norm_num))
theorem R87245 : Reach 87245 := rs (se 3 (by rfl) ⟨16358, by rfl⟩) (B 32717 (by norm_num) ⟨16358, by rfl⟩ (by norm_num))
theorem R87249 : Reach 87249 := rs (se 2 (by rfl) ⟨32718, by rfl⟩) (B 65437 (by norm_num) ⟨32718, by rfl⟩ (by norm_num))
theorem R87253 : Reach 87253 := rs (se 7 (by rfl) ⟨1022, by rfl⟩) (B 2045 (by norm_num) ⟨1022, by rfl⟩ (by norm_num))
theorem R87257 : Reach 87257 := rs (se 2 (by rfl) ⟨32721, by rfl⟩) (B 65443 (by norm_num) ⟨32721, by rfl⟩ (by norm_num))
theorem R87261 : Reach 87261 := rs (se 3 (by rfl) ⟨16361, by rfl⟩) (B 32723 (by norm_num) ⟨16361, by rfl⟩ (by norm_num))
theorem R87265 : Reach 87265 := rs (se 2 (by rfl) ⟨32724, by rfl⟩) (B 65449 (by norm_num) ⟨32724, by rfl⟩ (by norm_num))
theorem R87269 : Reach 87269 := rs (se 4 (by rfl) ⟨8181, by rfl⟩) (B 16363 (by norm_num) ⟨8181, by rfl⟩ (by norm_num))
theorem R87273 : Reach 87273 := rs (se 2 (by rfl) ⟨32727, by rfl⟩) (B 65455 (by norm_num) ⟨32727, by rfl⟩ (by norm_num))
theorem R87277 : Reach 87277 := rs (se 3 (by rfl) ⟨16364, by rfl⟩) (B 32729 (by norm_num) ⟨16364, by rfl⟩ (by norm_num))
theorem R152813 : Reach 152813 := rs (se 3 (by rfl) ⟨28652, by rfl⟩) (B 57305 (by norm_num) ⟨28652, by rfl⟩ (by norm_num))
theorem R87281 : Reach 87281 := rs (se 2 (by rfl) ⟨32730, by rfl⟩) (B 65461 (by norm_num) ⟨32730, by rfl⟩ (by norm_num))
theorem R87285 : Reach 87285 := rs (se 5 (by rfl) ⟨4091, by rfl⟩) (B 8183 (by norm_num) ⟨4091, by rfl⟩ (by norm_num))
theorem R87289 : Reach 87289 := rs (se 2 (by rfl) ⟨32733, by rfl⟩) (B 65467 (by norm_num) ⟨32733, by rfl⟩ (by norm_num))
theorem R87293 : Reach 87293 := rs (se 3 (by rfl) ⟨16367, by rfl⟩) (B 32735 (by norm_num) ⟨16367, by rfl⟩ (by norm_num))
theorem R87297 : Reach 87297 := rs (se 2 (by rfl) ⟨32736, by rfl⟩) (B 65473 (by norm_num) ⟨32736, by rfl⟩ (by norm_num))
theorem R87301 : Reach 87301 := rs (se 4 (by rfl) ⟨8184, by rfl⟩) (B 16369 (by norm_num) ⟨8184, by rfl⟩ (by norm_num))
theorem R87305 : Reach 87305 := rs (se 2 (by rfl) ⟨32739, by rfl⟩) (B 65479 (by norm_num) ⟨32739, by rfl⟩ (by norm_num))
theorem R87309 : Reach 87309 := rs (se 3 (by rfl) ⟨16370, by rfl⟩) (B 32741 (by norm_num) ⟨16370, by rfl⟩ (by norm_num))
theorem R87313 : Reach 87313 := rs (se 2 (by rfl) ⟨32742, by rfl⟩) (B 65485 (by norm_num) ⟨32742, by rfl⟩ (by norm_num))
theorem R87317 : Reach 87317 := rs (se 6 (by rfl) ⟨2046, by rfl⟩) (B 4093 (by norm_num) ⟨2046, by rfl⟩ (by norm_num))
theorem R87321 : Reach 87321 := rs (se 2 (by rfl) ⟨32745, by rfl⟩) (B 65491 (by norm_num) ⟨32745, by rfl⟩ (by norm_num))
theorem R87325 : Reach 87325 := rs (se 3 (by rfl) ⟨16373, by rfl⟩) (B 32747 (by norm_num) ⟨16373, by rfl⟩ (by norm_num))
theorem R87329 : Reach 87329 := rs (se 2 (by rfl) ⟨32748, by rfl⟩) (B 65497 (by norm_num) ⟨32748, by rfl⟩ (by norm_num))
theorem R87333 : Reach 87333 := rs (se 4 (by rfl) ⟨8187, by rfl⟩) (B 16375 (by norm_num) ⟨8187, by rfl⟩ (by norm_num))
theorem R87337 : Reach 87337 := rs (se 2 (by rfl) ⟨32751, by rfl⟩) (B 65503 (by norm_num) ⟨32751, by rfl⟩ (by norm_num))
theorem R87341 : Reach 87341 := rs (se 3 (by rfl) ⟨16376, by rfl⟩) (B 32753 (by norm_num) ⟨16376, by rfl⟩ (by norm_num))
theorem R87345 : Reach 87345 := rs (se 2 (by rfl) ⟨32754, by rfl⟩) (B 65509 (by norm_num) ⟨32754, by rfl⟩ (by norm_num))
theorem R87349 : Reach 87349 := rs (se 5 (by rfl) ⟨4094, by rfl⟩) (B 8189 (by norm_num) ⟨4094, by rfl⟩ (by norm_num))
theorem R87353 : Reach 87353 := rs (se 2 (by rfl) ⟨32757, by rfl⟩) (B 65515 (by norm_num) ⟨32757, by rfl⟩ (by norm_num))
theorem R87357 : Reach 87357 := rs (se 3 (by rfl) ⟨16379, by rfl⟩) (B 32759 (by norm_num) ⟨16379, by rfl⟩ (by norm_num))
theorem R87361 : Reach 87361 := rs (se 2 (by rfl) ⟨32760, by rfl⟩) (B 65521 (by norm_num) ⟨32760, by rfl⟩ (by norm_num))
theorem R87365 : Reach 87365 := rs (se 4 (by rfl) ⟨8190, by rfl⟩) (B 16381 (by norm_num) ⟨8190, by rfl⟩ (by norm_num))
theorem R87369 : Reach 87369 := rs (se 2 (by rfl) ⟨32763, by rfl⟩) (B 65527 (by norm_num) ⟨32763, by rfl⟩ (by norm_num))
theorem R87373 : Reach 87373 := rs (se 3 (by rfl) ⟨16382, by rfl⟩) (B 32765 (by norm_num) ⟨16382, by rfl⟩ (by norm_num))
theorem R87377 : Reach 87377 := rs (se 2 (by rfl) ⟨32766, by rfl⟩) (B 65533 (by norm_num) ⟨32766, by rfl⟩ (by norm_num))
theorem R87381 : Reach 87381 := rs (se 18 (by rfl) ⟨0, by rfl⟩) (B 1 (by norm_num) ⟨0, by rfl⟩ (by norm_num))
theorem R251221 : Reach 251221 := rs (se 15 (by rfl) ⟨11, by rfl⟩) (B 23 (by norm_num) ⟨11, by rfl⟩ (by norm_num))
theorem R87385 : Reach 87385 := rs (se 2 (by rfl) ⟨32769, by rfl⟩) (B 65539 (by norm_num) ⟨32769, by rfl⟩ (by norm_num))
theorem R87389 : Reach 87389 := rs (se 3 (by rfl) ⟨16385, by rfl⟩) (B 32771 (by norm_num) ⟨16385, by rfl⟩ (by norm_num))
theorem R87393 : Reach 87393 := rs (se 2 (by rfl) ⟨32772, by rfl⟩) (B 65545 (by norm_num) ⟨32772, by rfl⟩ (by norm_num))
theorem R87397 : Reach 87397 := rs (se 4 (by rfl) ⟨8193, by rfl⟩) (B 16387 (by norm_num) ⟨8193, by rfl⟩ (by norm_num))
theorem R87401 : Reach 87401 := rs (se 2 (by rfl) ⟨32775, by rfl⟩) (B 65551 (by norm_num) ⟨32775, by rfl⟩ (by norm_num))
theorem R87405 : Reach 87405 := rs (se 3 (by rfl) ⟨16388, by rfl⟩) (B 32777 (by norm_num) ⟨16388, by rfl⟩ (by norm_num))
theorem R152941 : Reach 152941 := rs (se 3 (by rfl) ⟨28676, by rfl⟩) (B 57353 (by norm_num) ⟨28676, by rfl⟩ (by norm_num))
theorem R87409 : Reach 87409 := rs (se 2 (by rfl) ⟨32778, by rfl⟩) (B 65557 (by norm_num) ⟨32778, by rfl⟩ (by norm_num))
theorem R87413 : Reach 87413 := rs (se 5 (by rfl) ⟨4097, by rfl⟩) (B 8195 (by norm_num) ⟨4097, by rfl⟩ (by norm_num))
theorem R87417 : Reach 87417 := rs (se 2 (by rfl) ⟨32781, by rfl⟩) (B 65563 (by norm_num) ⟨32781, by rfl⟩ (by norm_num))
theorem R87421 : Reach 87421 := rs (se 3 (by rfl) ⟨16391, by rfl⟩) (B 32783 (by norm_num) ⟨16391, by rfl⟩ (by norm_num))
theorem R87425 : Reach 87425 := rs (se 2 (by rfl) ⟨32784, by rfl⟩) (B 65569 (by norm_num) ⟨32784, by rfl⟩ (by norm_num))
theorem R87429 : Reach 87429 := rs (se 4 (by rfl) ⟨8196, by rfl⟩) (B 16393 (by norm_num) ⟨8196, by rfl⟩ (by norm_num))
theorem R87433 : Reach 87433 := rs (se 2 (by rfl) ⟨32787, by rfl⟩) (B 65575 (by norm_num) ⟨32787, by rfl⟩ (by norm_num))
theorem R87437 : Reach 87437 := rs (se 3 (by rfl) ⟨16394, by rfl⟩) (B 32789 (by norm_num) ⟨16394, by rfl⟩ (by norm_num))
theorem R87441 : Reach 87441 := rs (se 2 (by rfl) ⟨32790, by rfl⟩) (B 65581 (by norm_num) ⟨32790, by rfl⟩ (by norm_num))
theorem R87445 : Reach 87445 := rs (se 6 (by rfl) ⟨2049, by rfl⟩) (B 4099 (by norm_num) ⟨2049, by rfl⟩ (by norm_num))
theorem R87449 : Reach 87449 := rs (se 2 (by rfl) ⟨32793, by rfl⟩) (B 65587 (by norm_num) ⟨32793, by rfl⟩ (by norm_num))
theorem R87453 : Reach 87453 := rs (se 3 (by rfl) ⟨16397, by rfl⟩) (B 32795 (by norm_num) ⟨16397, by rfl⟩ (by norm_num))
theorem R87457 : Reach 87457 := rs (se 2 (by rfl) ⟨32796, by rfl⟩) (B 65593 (by norm_num) ⟨32796, by rfl⟩ (by norm_num))
theorem R87461 : Reach 87461 := rs (se 4 (by rfl) ⟨8199, by rfl⟩) (B 16399 (by norm_num) ⟨8199, by rfl⟩ (by norm_num))
theorem R218533 : Reach 218533 := rs (se 4 (by rfl) ⟨20487, by rfl⟩) (B 40975 (by norm_num) ⟨20487, by rfl⟩ (by norm_num))
theorem R87465 : Reach 87465 := rs (se 2 (by rfl) ⟨32799, by rfl⟩) (B 65599 (by norm_num) ⟨32799, by rfl⟩ (by norm_num))
theorem R87469 : Reach 87469 := rs (se 3 (by rfl) ⟨16400, by rfl⟩) (B 32801 (by norm_num) ⟨16400, by rfl⟩ (by norm_num))
theorem R87473 : Reach 87473 := rs (se 2 (by rfl) ⟨32802, by rfl⟩) (B 65605 (by norm_num) ⟨32802, by rfl⟩ (by norm_num))
theorem R87477 : Reach 87477 := rs (se 5 (by rfl) ⟨4100, by rfl⟩) (B 8201 (by norm_num) ⟨4100, by rfl⟩ (by norm_num))
theorem R87481 : Reach 87481 := rs (se 2 (by rfl) ⟨32805, by rfl⟩) (B 65611 (by norm_num) ⟨32805, by rfl⟩ (by norm_num))
theorem R87485 : Reach 87485 := rs (se 3 (by rfl) ⟨16403, by rfl⟩) (B 32807 (by norm_num) ⟨16403, by rfl⟩ (by norm_num))
theorem R87489 : Reach 87489 := rs (se 2 (by rfl) ⟨32808, by rfl⟩) (B 65617 (by norm_num) ⟨32808, by rfl⟩ (by norm_num))
theorem R87493 : Reach 87493 := rs (se 4 (by rfl) ⟨8202, by rfl⟩) (B 16405 (by norm_num) ⟨8202, by rfl⟩ (by norm_num))
theorem R153029 : Reach 153029 := rs (se 4 (by rfl) ⟨14346, by rfl⟩) (B 28693 (by norm_num) ⟨14346, by rfl⟩ (by norm_num))
theorem R87497 : Reach 87497 := rs (se 2 (by rfl) ⟨32811, by rfl⟩) (B 65623 (by norm_num) ⟨32811, by rfl⟩ (by norm_num))
theorem R87501 : Reach 87501 := rs (se 3 (by rfl) ⟨16406, by rfl⟩) (B 32813 (by norm_num) ⟨16406, by rfl⟩ (by norm_num))
theorem R87505 : Reach 87505 := rs (se 2 (by rfl) ⟨32814, by rfl⟩) (B 65629 (by norm_num) ⟨32814, by rfl⟩ (by norm_num))
theorem R87509 : Reach 87509 := rs (se 7 (by rfl) ⟨1025, by rfl⟩) (B 2051 (by norm_num) ⟨1025, by rfl⟩ (by norm_num))
theorem R87513 : Reach 87513 := rs (se 2 (by rfl) ⟨32817, by rfl⟩) (B 65635 (by norm_num) ⟨32817, by rfl⟩ (by norm_num))
theorem R87517 : Reach 87517 := rs (se 3 (by rfl) ⟨16409, by rfl⟩) (B 32819 (by norm_num) ⟨16409, by rfl⟩ (by norm_num))
theorem R87521 : Reach 87521 := rs (se 2 (by rfl) ⟨32820, by rfl⟩) (B 65641 (by norm_num) ⟨32820, by rfl⟩ (by norm_num))
theorem R87525 : Reach 87525 := rs (se 4 (by rfl) ⟨8205, by rfl⟩) (B 16411 (by norm_num) ⟨8205, by rfl⟩ (by norm_num))
theorem R87529 : Reach 87529 := rs (se 2 (by rfl) ⟨32823, by rfl⟩) (B 65647 (by norm_num) ⟨32823, by rfl⟩ (by norm_num))
theorem R87533 : Reach 87533 := rs (se 3 (by rfl) ⟨16412, by rfl⟩) (B 32825 (by norm_num) ⟨16412, by rfl⟩ (by norm_num))
theorem R87537 : Reach 87537 := rs (se 2 (by rfl) ⟨32826, by rfl⟩) (B 65653 (by norm_num) ⟨32826, by rfl⟩ (by norm_num))
theorem R87541 : Reach 87541 := rs (se 5 (by rfl) ⟨4103, by rfl⟩) (B 8207 (by norm_num) ⟨4103, by rfl⟩ (by norm_num))
theorem R87545 : Reach 87545 := rs (se 2 (by rfl) ⟨32829, by rfl⟩) (B 65659 (by norm_num) ⟨32829, by rfl⟩ (by norm_num))
theorem R87549 : Reach 87549 := rs (se 3 (by rfl) ⟨16415, by rfl⟩) (B 32831 (by norm_num) ⟨16415, by rfl⟩ (by norm_num))
theorem R87553 : Reach 87553 := rs (se 2 (by rfl) ⟨32832, by rfl⟩) (B 65665 (by norm_num) ⟨32832, by rfl⟩ (by norm_num))
theorem R87557 : Reach 87557 := rs (se 4 (by rfl) ⟨8208, by rfl⟩) (B 16417 (by norm_num) ⟨8208, by rfl⟩ (by norm_num))
theorem R87561 : Reach 87561 := rs (se 2 (by rfl) ⟨32835, by rfl⟩) (B 65671 (by norm_num) ⟨32835, by rfl⟩ (by norm_num))
theorem R87565 : Reach 87565 := rs (se 3 (by rfl) ⟨16418, by rfl⟩) (B 32837 (by norm_num) ⟨16418, by rfl⟩ (by norm_num))
theorem R87569 : Reach 87569 := rs (se 2 (by rfl) ⟨32838, by rfl⟩) (B 65677 (by norm_num) ⟨32838, by rfl⟩ (by norm_num))
theorem R87573 : Reach 87573 := rs (se 6 (by rfl) ⟨2052, by rfl⟩) (B 4105 (by norm_num) ⟨2052, by rfl⟩ (by norm_num))
theorem R87577 : Reach 87577 := rs (se 2 (by rfl) ⟨32841, by rfl⟩) (B 65683 (by norm_num) ⟨32841, by rfl⟩ (by norm_num))
theorem R87581 : Reach 87581 := rs (se 3 (by rfl) ⟨16421, by rfl⟩) (B 32843 (by norm_num) ⟨16421, by rfl⟩ (by norm_num))
theorem R87585 : Reach 87585 := rs (se 2 (by rfl) ⟨32844, by rfl⟩) (B 65689 (by norm_num) ⟨32844, by rfl⟩ (by norm_num))
theorem R87589 : Reach 87589 := rs (se 4 (by rfl) ⟨8211, by rfl⟩) (B 16423 (by norm_num) ⟨8211, by rfl⟩ (by norm_num))
theorem R87593 : Reach 87593 := rs (se 2 (by rfl) ⟨32847, by rfl⟩) (B 65695 (by norm_num) ⟨32847, by rfl⟩ (by norm_num))
theorem R87597 : Reach 87597 := rs (se 3 (by rfl) ⟨16424, by rfl⟩) (B 32849 (by norm_num) ⟨16424, by rfl⟩ (by norm_num))
theorem R87601 : Reach 87601 := rs (se 2 (by rfl) ⟨32850, by rfl⟩) (B 65701 (by norm_num) ⟨32850, by rfl⟩ (by norm_num))
theorem R87605 : Reach 87605 := rs (se 5 (by rfl) ⟨4106, by rfl⟩) (B 8213 (by norm_num) ⟨4106, by rfl⟩ (by norm_num))
theorem R87609 : Reach 87609 := rs (se 2 (by rfl) ⟨32853, by rfl⟩) (B 65707 (by norm_num) ⟨32853, by rfl⟩ (by norm_num))
theorem R87613 : Reach 87613 := rs (se 3 (by rfl) ⟨16427, by rfl⟩) (B 32855 (by norm_num) ⟨16427, by rfl⟩ (by norm_num))
theorem R87617 : Reach 87617 := rs (se 2 (by rfl) ⟨32856, by rfl⟩) (B 65713 (by norm_num) ⟨32856, by rfl⟩ (by norm_num))
theorem R87621 : Reach 87621 := rs (se 4 (by rfl) ⟨8214, by rfl⟩) (B 16429 (by norm_num) ⟨8214, by rfl⟩ (by norm_num))
theorem R218693 : Reach 218693 := rs (se 4 (by rfl) ⟨20502, by rfl⟩) (B 41005 (by norm_num) ⟨20502, by rfl⟩ (by norm_num))
theorem R153157 : Reach 153157 := rs (se 4 (by rfl) ⟨14358, by rfl⟩) (B 28717 (by norm_num) ⟨14358, by rfl⟩ (by norm_num))
theorem R87625 : Reach 87625 := rs (se 2 (by rfl) ⟨32859, by rfl⟩) (B 65719 (by norm_num) ⟨32859, by rfl⟩ (by norm_num))
theorem R87629 : Reach 87629 := rs (se 3 (by rfl) ⟨16430, by rfl⟩) (B 32861 (by norm_num) ⟨16430, by rfl⟩ (by norm_num))
theorem R87633 : Reach 87633 := rs (se 2 (by rfl) ⟨32862, by rfl⟩) (B 65725 (by norm_num) ⟨32862, by rfl⟩ (by norm_num))
theorem R87637 : Reach 87637 := rs (se 8 (by rfl) ⟨513, by rfl⟩) (B 1027 (by norm_num) ⟨513, by rfl⟩ (by norm_num))
theorem R87641 : Reach 87641 := rs (se 2 (by rfl) ⟨32865, by rfl⟩) (B 65731 (by norm_num) ⟨32865, by rfl⟩ (by norm_num))
theorem R87645 : Reach 87645 := rs (se 3 (by rfl) ⟨16433, by rfl⟩) (B 32867 (by norm_num) ⟨16433, by rfl⟩ (by norm_num))
theorem R87649 : Reach 87649 := rs (se 2 (by rfl) ⟨32868, by rfl⟩) (B 65737 (by norm_num) ⟨32868, by rfl⟩ (by norm_num))
theorem R87653 : Reach 87653 := rs (se 4 (by rfl) ⟨8217, by rfl⟩) (B 16435 (by norm_num) ⟨8217, by rfl⟩ (by norm_num))
theorem R87657 : Reach 87657 := rs (se 2 (by rfl) ⟨32871, by rfl⟩) (B 65743 (by norm_num) ⟨32871, by rfl⟩ (by norm_num))
theorem R87661 : Reach 87661 := rs (se 3 (by rfl) ⟨16436, by rfl⟩) (B 32873 (by norm_num) ⟨16436, by rfl⟩ (by norm_num))
theorem R87665 : Reach 87665 := rs (se 2 (by rfl) ⟨32874, by rfl⟩) (B 65749 (by norm_num) ⟨32874, by rfl⟩ (by norm_num))
theorem R87669 : Reach 87669 := rs (se 5 (by rfl) ⟨4109, by rfl⟩) (B 8219 (by norm_num) ⟨4109, by rfl⟩ (by norm_num))
theorem R87673 : Reach 87673 := rs (se 2 (by rfl) ⟨32877, by rfl⟩) (B 65755 (by norm_num) ⟨32877, by rfl⟩ (by norm_num))
theorem R87677 : Reach 87677 := rs (se 3 (by rfl) ⟨16439, by rfl⟩) (B 32879 (by norm_num) ⟨16439, by rfl⟩ (by norm_num))
theorem R87681 : Reach 87681 := rs (se 2 (by rfl) ⟨32880, by rfl⟩) (B 65761 (by norm_num) ⟨32880, by rfl⟩ (by norm_num))
theorem R87685 : Reach 87685 := rs (se 4 (by rfl) ⟨8220, by rfl⟩) (B 16441 (by norm_num) ⟨8220, by rfl⟩ (by norm_num))
theorem R87689 : Reach 87689 := rs (se 2 (by rfl) ⟨32883, by rfl⟩) (B 65767 (by norm_num) ⟨32883, by rfl⟩ (by norm_num))
theorem R87693 : Reach 87693 := rs (se 3 (by rfl) ⟨16442, by rfl⟩) (B 32885 (by norm_num) ⟨16442, by rfl⟩ (by norm_num))
theorem R87697 : Reach 87697 := rs (se 2 (by rfl) ⟨32886, by rfl⟩) (B 65773 (by norm_num) ⟨32886, by rfl⟩ (by norm_num))
theorem R87701 : Reach 87701 := rs (se 6 (by rfl) ⟨2055, by rfl⟩) (B 4111 (by norm_num) ⟨2055, by rfl⟩ (by norm_num))
theorem R87705 : Reach 87705 := rs (se 2 (by rfl) ⟨32889, by rfl⟩) (B 65779 (by norm_num) ⟨32889, by rfl⟩ (by norm_num))
theorem R87709 : Reach 87709 := rs (se 3 (by rfl) ⟨16445, by rfl⟩) (B 32891 (by norm_num) ⟨16445, by rfl⟩ (by norm_num))
theorem R153245 : Reach 153245 := rs (se 3 (by rfl) ⟨28733, by rfl⟩) (B 57467 (by norm_num) ⟨28733, by rfl⟩ (by norm_num))
theorem R87713 : Reach 87713 := rs (se 2 (by rfl) ⟨32892, by rfl⟩) (B 65785 (by norm_num) ⟨32892, by rfl⟩ (by norm_num))
theorem R87717 : Reach 87717 := rs (se 4 (by rfl) ⟨8223, by rfl⟩) (B 16447 (by norm_num) ⟨8223, by rfl⟩ (by norm_num))
theorem R87721 : Reach 87721 := rs (se 2 (by rfl) ⟨32895, by rfl⟩) (B 65791 (by norm_num) ⟨32895, by rfl⟩ (by norm_num))
theorem R87725 : Reach 87725 := rs (se 3 (by rfl) ⟨16448, by rfl⟩) (B 32897 (by norm_num) ⟨16448, by rfl⟩ (by norm_num))
theorem R87729 : Reach 87729 := rs (se 2 (by rfl) ⟨32898, by rfl⟩) (B 65797 (by norm_num) ⟨32898, by rfl⟩ (by norm_num))
theorem R87733 : Reach 87733 := rs (se 5 (by rfl) ⟨4112, by rfl⟩) (B 8225 (by norm_num) ⟨4112, by rfl⟩ (by norm_num))
theorem R87737 : Reach 87737 := rs (se 2 (by rfl) ⟨32901, by rfl⟩) (B 65803 (by norm_num) ⟨32901, by rfl⟩ (by norm_num))
theorem R87741 : Reach 87741 := rs (se 3 (by rfl) ⟨16451, by rfl⟩) (B 32903 (by norm_num) ⟨16451, by rfl⟩ (by norm_num))
theorem R87745 : Reach 87745 := rs (se 2 (by rfl) ⟨32904, by rfl⟩) (B 65809 (by norm_num) ⟨32904, by rfl⟩ (by norm_num))
theorem R87749 : Reach 87749 := rs (se 4 (by rfl) ⟨8226, by rfl⟩) (B 16453 (by norm_num) ⟨8226, by rfl⟩ (by norm_num))
theorem R87753 : Reach 87753 := rs (se 2 (by rfl) ⟨32907, by rfl⟩) (B 65815 (by norm_num) ⟨32907, by rfl⟩ (by norm_num))
theorem R87757 : Reach 87757 := rs (se 3 (by rfl) ⟨16454, by rfl⟩) (B 32909 (by norm_num) ⟨16454, by rfl⟩ (by norm_num))
theorem R87761 : Reach 87761 := rs (se 2 (by rfl) ⟨32910, by rfl⟩) (B 65821 (by norm_num) ⟨32910, by rfl⟩ (by norm_num))
theorem R87765 : Reach 87765 := rs (se 7 (by rfl) ⟨1028, by rfl⟩) (B 2057 (by norm_num) ⟨1028, by rfl⟩ (by norm_num))
theorem R87769 : Reach 87769 := rs (se 2 (by rfl) ⟨32913, by rfl⟩) (B 65827 (by norm_num) ⟨32913, by rfl⟩ (by norm_num))
theorem R87773 : Reach 87773 := rs (se 3 (by rfl) ⟨16457, by rfl⟩) (B 32915 (by norm_num) ⟨16457, by rfl⟩ (by norm_num))
theorem R87777 : Reach 87777 := rs (se 2 (by rfl) ⟨32916, by rfl⟩) (B 65833 (by norm_num) ⟨32916, by rfl⟩ (by norm_num))
theorem R87781 : Reach 87781 := rs (se 4 (by rfl) ⟨8229, by rfl⟩) (B 16459 (by norm_num) ⟨8229, by rfl⟩ (by norm_num))
theorem R87785 : Reach 87785 := rs (se 2 (by rfl) ⟨32919, by rfl⟩) (B 65839 (by norm_num) ⟨32919, by rfl⟩ (by norm_num))
theorem R87789 : Reach 87789 := rs (se 3 (by rfl) ⟨16460, by rfl⟩) (B 32921 (by norm_num) ⟨16460, by rfl⟩ (by norm_num))
theorem R87793 : Reach 87793 := rs (se 2 (by rfl) ⟨32922, by rfl⟩) (B 65845 (by norm_num) ⟨32922, by rfl⟩ (by norm_num))
theorem R87797 : Reach 87797 := rs (se 5 (by rfl) ⟨4115, by rfl⟩) (B 8231 (by norm_num) ⟨4115, by rfl⟩ (by norm_num))
theorem R87801 : Reach 87801 := rs (se 2 (by rfl) ⟨32925, by rfl⟩) (B 65851 (by norm_num) ⟨32925, by rfl⟩ (by norm_num))
theorem R87805 : Reach 87805 := rs (se 3 (by rfl) ⟨16463, by rfl⟩) (B 32927 (by norm_num) ⟨16463, by rfl⟩ (by norm_num))
theorem R87809 : Reach 87809 := rs (se 2 (by rfl) ⟨32928, by rfl⟩) (B 65857 (by norm_num) ⟨32928, by rfl⟩ (by norm_num))
theorem R87813 : Reach 87813 := rs (se 4 (by rfl) ⟨8232, by rfl⟩) (B 16465 (by norm_num) ⟨8232, by rfl⟩ (by norm_num))
theorem R87817 : Reach 87817 := rs (se 2 (by rfl) ⟨32931, by rfl⟩) (B 65863 (by norm_num) ⟨32931, by rfl⟩ (by norm_num))
theorem R87821 : Reach 87821 := rs (se 3 (by rfl) ⟨16466, by rfl⟩) (B 32933 (by norm_num) ⟨16466, by rfl⟩ (by norm_num))
theorem R87825 : Reach 87825 := rs (se 2 (by rfl) ⟨32934, by rfl⟩) (B 65869 (by norm_num) ⟨32934, by rfl⟩ (by norm_num))
theorem R87829 : Reach 87829 := rs (se 6 (by rfl) ⟨2058, by rfl⟩) (B 4117 (by norm_num) ⟨2058, by rfl⟩ (by norm_num))
theorem R87833 : Reach 87833 := rs (se 2 (by rfl) ⟨32937, by rfl⟩) (B 65875 (by norm_num) ⟨32937, by rfl⟩ (by norm_num))
theorem R87837 : Reach 87837 := rs (se 3 (by rfl) ⟨16469, by rfl⟩) (B 32939 (by norm_num) ⟨16469, by rfl⟩ (by norm_num))
theorem R153373 : Reach 153373 := rs (se 3 (by rfl) ⟨28757, by rfl⟩) (B 57515 (by norm_num) ⟨28757, by rfl⟩ (by norm_num))
theorem R87841 : Reach 87841 := rs (se 2 (by rfl) ⟨32940, by rfl⟩) (B 65881 (by norm_num) ⟨32940, by rfl⟩ (by norm_num))
theorem R87845 : Reach 87845 := rs (se 4 (by rfl) ⟨8235, by rfl⟩) (B 16471 (by norm_num) ⟨8235, by rfl⟩ (by norm_num))
theorem R87849 : Reach 87849 := rs (se 2 (by rfl) ⟨32943, by rfl⟩) (B 65887 (by norm_num) ⟨32943, by rfl⟩ (by norm_num))
theorem R87853 : Reach 87853 := rs (se 3 (by rfl) ⟨16472, by rfl⟩) (B 32945 (by norm_num) ⟨16472, by rfl⟩ (by norm_num))
theorem R87857 : Reach 87857 := rs (se 2 (by rfl) ⟨32946, by rfl⟩) (B 65893 (by norm_num) ⟨32946, by rfl⟩ (by norm_num))
theorem R87861 : Reach 87861 := rs (se 5 (by rfl) ⟨4118, by rfl⟩) (B 8237 (by norm_num) ⟨4118, by rfl⟩ (by norm_num))
theorem R87865 : Reach 87865 := rs (se 2 (by rfl) ⟨32949, by rfl⟩) (B 65899 (by norm_num) ⟨32949, by rfl⟩ (by norm_num))
theorem R87869 : Reach 87869 := rs (se 3 (by rfl) ⟨16475, by rfl⟩) (B 32951 (by norm_num) ⟨16475, by rfl⟩ (by norm_num))
theorem R87873 : Reach 87873 := rs (se 2 (by rfl) ⟨32952, by rfl⟩) (B 65905 (by norm_num) ⟨32952, by rfl⟩ (by norm_num))
theorem R87877 : Reach 87877 := rs (se 4 (by rfl) ⟨8238, by rfl⟩) (B 16477 (by norm_num) ⟨8238, by rfl⟩ (by norm_num))
theorem R87881 : Reach 87881 := rs (se 2 (by rfl) ⟨32955, by rfl⟩) (B 65911 (by norm_num) ⟨32955, by rfl⟩ (by norm_num))
theorem R87885 : Reach 87885 := rs (se 3 (by rfl) ⟨16478, by rfl⟩) (B 32957 (by norm_num) ⟨16478, by rfl⟩ (by norm_num))
theorem R87889 : Reach 87889 := rs (se 2 (by rfl) ⟨32958, by rfl⟩) (B 65917 (by norm_num) ⟨32958, by rfl⟩ (by norm_num))
theorem R87893 : Reach 87893 := rs (se 9 (by rfl) ⟨257, by rfl⟩) (B 515 (by norm_num) ⟨257, by rfl⟩ (by norm_num))
theorem R87897 : Reach 87897 := rs (se 2 (by rfl) ⟨32961, by rfl⟩) (B 65923 (by norm_num) ⟨32961, by rfl⟩ (by norm_num))
theorem R87901 : Reach 87901 := rs (se 3 (by rfl) ⟨16481, by rfl⟩) (B 32963 (by norm_num) ⟨16481, by rfl⟩ (by norm_num))
theorem R87905 : Reach 87905 := rs (se 2 (by rfl) ⟨32964, by rfl⟩) (B 65929 (by norm_num) ⟨32964, by rfl⟩ (by norm_num))
theorem R87909 : Reach 87909 := rs (se 4 (by rfl) ⟨8241, by rfl⟩) (B 16483 (by norm_num) ⟨8241, by rfl⟩ (by norm_num))
theorem R87913 : Reach 87913 := rs (se 2 (by rfl) ⟨32967, by rfl⟩) (B 65935 (by norm_num) ⟨32967, by rfl⟩ (by norm_num))
theorem R87917 : Reach 87917 := rs (se 3 (by rfl) ⟨16484, by rfl⟩) (B 32969 (by norm_num) ⟨16484, by rfl⟩ (by norm_num))
theorem R87921 : Reach 87921 := rs (se 2 (by rfl) ⟨32970, by rfl⟩) (B 65941 (by norm_num) ⟨32970, by rfl⟩ (by norm_num))
theorem R186229 : Reach 186229 := rs (se 5 (by rfl) ⟨8729, by rfl⟩) (B 17459 (by norm_num) ⟨8729, by rfl⟩ (by norm_num))
theorem R87925 : Reach 87925 := rs (se 5 (by rfl) ⟨4121, by rfl⟩) (B 8243 (by norm_num) ⟨4121, by rfl⟩ (by norm_num))
theorem R153461 : Reach 153461 := rs (se 5 (by rfl) ⟨7193, by rfl⟩) (B 14387 (by norm_num) ⟨7193, by rfl⟩ (by norm_num))
theorem R87929 : Reach 87929 := rs (se 2 (by rfl) ⟨32973, by rfl⟩) (B 65947 (by norm_num) ⟨32973, by rfl⟩ (by norm_num))
theorem R87933 : Reach 87933 := rs (se 3 (by rfl) ⟨16487, by rfl⟩) (B 32975 (by norm_num) ⟨16487, by rfl⟩ (by norm_num))
theorem R87937 : Reach 87937 := rs (se 2 (by rfl) ⟨32976, by rfl⟩) (B 65953 (by norm_num) ⟨32976, by rfl⟩ (by norm_num))
theorem R87941 : Reach 87941 := rs (se 4 (by rfl) ⟨8244, by rfl⟩) (B 16489 (by norm_num) ⟨8244, by rfl⟩ (by norm_num))
theorem R87945 : Reach 87945 := rs (se 2 (by rfl) ⟨32979, by rfl⟩) (B 65959 (by norm_num) ⟨32979, by rfl⟩ (by norm_num))
theorem R87949 : Reach 87949 := rs (se 3 (by rfl) ⟨16490, by rfl⟩) (B 32981 (by norm_num) ⟨16490, by rfl⟩ (by norm_num))
theorem R87953 : Reach 87953 := rs (se 2 (by rfl) ⟨32982, by rfl⟩) (B 65965 (by norm_num) ⟨32982, by rfl⟩ (by norm_num))
theorem R87957 : Reach 87957 := rs (se 6 (by rfl) ⟨2061, by rfl⟩) (B 4123 (by norm_num) ⟨2061, by rfl⟩ (by norm_num))
theorem R87961 : Reach 87961 := rs (se 2 (by rfl) ⟨32985, by rfl⟩) (B 65971 (by norm_num) ⟨32985, by rfl⟩ (by norm_num))
theorem R87965 : Reach 87965 := rs (se 3 (by rfl) ⟨16493, by rfl⟩) (B 32987 (by norm_num) ⟨16493, by rfl⟩ (by norm_num))
theorem R87969 : Reach 87969 := rs (se 2 (by rfl) ⟨32988, by rfl⟩) (B 65977 (by norm_num) ⟨32988, by rfl⟩ (by norm_num))
theorem R87973 : Reach 87973 := rs (se 4 (by rfl) ⟨8247, by rfl⟩) (B 16495 (by norm_num) ⟨8247, by rfl⟩ (by norm_num))
theorem R87977 : Reach 87977 := rs (se 2 (by rfl) ⟨32991, by rfl⟩) (B 65983 (by norm_num) ⟨32991, by rfl⟩ (by norm_num))
theorem R87981 : Reach 87981 := rs (se 3 (by rfl) ⟨16496, by rfl⟩) (B 32993 (by norm_num) ⟨16496, by rfl⟩ (by norm_num))
theorem R87985 : Reach 87985 := rs (se 2 (by rfl) ⟨32994, by rfl⟩) (B 65989 (by norm_num) ⟨32994, by rfl⟩ (by norm_num))
theorem R87989 : Reach 87989 := rs (se 5 (by rfl) ⟨4124, by rfl⟩) (B 8249 (by norm_num) ⟨4124, by rfl⟩ (by norm_num))
theorem R87993 : Reach 87993 := rs (se 2 (by rfl) ⟨32997, by rfl⟩) (B 65995 (by norm_num) ⟨32997, by rfl⟩ (by norm_num))
theorem R87997 : Reach 87997 := rs (se 3 (by rfl) ⟨16499, by rfl⟩) (B 32999 (by norm_num) ⟨16499, by rfl⟩ (by norm_num))
theorem R88001 : Reach 88001 := rs (se 2 (by rfl) ⟨33000, by rfl⟩) (B 66001 (by norm_num) ⟨33000, by rfl⟩ (by norm_num))
theorem R88005 : Reach 88005 := rs (se 4 (by rfl) ⟨8250, by rfl⟩) (B 16501 (by norm_num) ⟨8250, by rfl⟩ (by norm_num))
theorem R88009 : Reach 88009 := rs (se 2 (by rfl) ⟨33003, by rfl⟩) (B 66007 (by norm_num) ⟨33003, by rfl⟩ (by norm_num))
theorem R88013 : Reach 88013 := rs (se 3 (by rfl) ⟨16502, by rfl⟩) (B 33005 (by norm_num) ⟨16502, by rfl⟩ (by norm_num))
theorem R88017 : Reach 88017 := rs (se 2 (by rfl) ⟨33006, by rfl⟩) (B 66013 (by norm_num) ⟨33006, by rfl⟩ (by norm_num))
theorem R88021 : Reach 88021 := rs (se 7 (by rfl) ⟨1031, by rfl⟩) (B 2063 (by norm_num) ⟨1031, by rfl⟩ (by norm_num))
theorem R88025 : Reach 88025 := rs (se 2 (by rfl) ⟨33009, by rfl⟩) (B 66019 (by norm_num) ⟨33009, by rfl⟩ (by norm_num))
theorem R88029 : Reach 88029 := rs (se 3 (by rfl) ⟨16505, by rfl⟩) (B 33011 (by norm_num) ⟨16505, by rfl⟩ (by norm_num))
theorem R88033 : Reach 88033 := rs (se 2 (by rfl) ⟨33012, by rfl⟩) (B 66025 (by norm_num) ⟨33012, by rfl⟩ (by norm_num))
theorem R88037 : Reach 88037 := rs (se 4 (by rfl) ⟨8253, by rfl⟩) (B 16507 (by norm_num) ⟨8253, by rfl⟩ (by norm_num))
theorem R88041 : Reach 88041 := rs (se 2 (by rfl) ⟨33015, by rfl⟩) (B 66031 (by norm_num) ⟨33015, by rfl⟩ (by norm_num))
theorem R88045 : Reach 88045 := rs (se 3 (by rfl) ⟨16508, by rfl⟩) (B 33017 (by norm_num) ⟨16508, by rfl⟩ (by norm_num))
theorem R88049 : Reach 88049 := rs (se 2 (by rfl) ⟨33018, by rfl⟩) (B 66037 (by norm_num) ⟨33018, by rfl⟩ (by norm_num))
theorem R88053 : Reach 88053 := rs (se 5 (by rfl) ⟨4127, by rfl⟩) (B 8255 (by norm_num) ⟨4127, by rfl⟩ (by norm_num))
theorem R153589 : Reach 153589 := rs (se 5 (by rfl) ⟨7199, by rfl⟩) (B 14399 (by norm_num) ⟨7199, by rfl⟩ (by norm_num))
theorem R88057 : Reach 88057 := rs (se 2 (by rfl) ⟨33021, by rfl⟩) (B 66043 (by norm_num) ⟨33021, by rfl⟩ (by norm_num))
theorem R88061 : Reach 88061 := rs (se 3 (by rfl) ⟨16511, by rfl⟩) (B 33023 (by norm_num) ⟨16511, by rfl⟩ (by norm_num))
theorem R88065 : Reach 88065 := rs (se 2 (by rfl) ⟨33024, by rfl⟩) (B 66049 (by norm_num) ⟨33024, by rfl⟩ (by norm_num))
theorem R88069 : Reach 88069 := rs (se 4 (by rfl) ⟨8256, by rfl⟩) (B 16513 (by norm_num) ⟨8256, by rfl⟩ (by norm_num))
theorem R88073 : Reach 88073 := rs (se 2 (by rfl) ⟨33027, by rfl⟩) (B 66055 (by norm_num) ⟨33027, by rfl⟩ (by norm_num))
theorem R88077 : Reach 88077 := rs (se 3 (by rfl) ⟨16514, by rfl⟩) (B 33029 (by norm_num) ⟨16514, by rfl⟩ (by norm_num))
theorem R88081 : Reach 88081 := rs (se 2 (by rfl) ⟨33030, by rfl⟩) (B 66061 (by norm_num) ⟨33030, by rfl⟩ (by norm_num))
theorem R88085 : Reach 88085 := rs (se 6 (by rfl) ⟨2064, by rfl⟩) (B 4129 (by norm_num) ⟨2064, by rfl⟩ (by norm_num))
theorem R88089 : Reach 88089 := rs (se 2 (by rfl) ⟨33033, by rfl⟩) (B 66067 (by norm_num) ⟨33033, by rfl⟩ (by norm_num))
theorem R88093 : Reach 88093 := rs (se 3 (by rfl) ⟨16517, by rfl⟩) (B 33035 (by norm_num) ⟨16517, by rfl⟩ (by norm_num))
theorem R88097 : Reach 88097 := rs (se 2 (by rfl) ⟨33036, by rfl⟩) (B 66073 (by norm_num) ⟨33036, by rfl⟩ (by norm_num))
theorem R88101 : Reach 88101 := rs (se 4 (by rfl) ⟨8259, by rfl⟩) (B 16519 (by norm_num) ⟨8259, by rfl⟩ (by norm_num))
theorem R88105 : Reach 88105 := rs (se 2 (by rfl) ⟨33039, by rfl⟩) (B 66079 (by norm_num) ⟨33039, by rfl⟩ (by norm_num))
theorem R88109 : Reach 88109 := rs (se 3 (by rfl) ⟨16520, by rfl⟩) (B 33041 (by norm_num) ⟨16520, by rfl⟩ (by norm_num))
theorem R88113 : Reach 88113 := rs (se 2 (by rfl) ⟨33042, by rfl⟩) (B 66085 (by norm_num) ⟨33042, by rfl⟩ (by norm_num))
theorem R88117 : Reach 88117 := rs (se 5 (by rfl) ⟨4130, by rfl⟩) (B 8261 (by norm_num) ⟨4130, by rfl⟩ (by norm_num))
theorem R88121 : Reach 88121 := rs (se 2 (by rfl) ⟨33045, by rfl⟩) (B 66091 (by norm_num) ⟨33045, by rfl⟩ (by norm_num))
theorem R88125 : Reach 88125 := rs (se 3 (by rfl) ⟨16523, by rfl⟩) (B 33047 (by norm_num) ⟨16523, by rfl⟩ (by norm_num))
theorem R88129 : Reach 88129 := rs (se 2 (by rfl) ⟨33048, by rfl⟩) (B 66097 (by norm_num) ⟨33048, by rfl⟩ (by norm_num))
theorem R88133 : Reach 88133 := rs (se 4 (by rfl) ⟨8262, by rfl⟩) (B 16525 (by norm_num) ⟨8262, by rfl⟩ (by norm_num))
theorem R88137 : Reach 88137 := rs (se 2 (by rfl) ⟨33051, by rfl⟩) (B 66103 (by norm_num) ⟨33051, by rfl⟩ (by norm_num))
theorem R88141 : Reach 88141 := rs (se 3 (by rfl) ⟨16526, by rfl⟩) (B 33053 (by norm_num) ⟨16526, by rfl⟩ (by norm_num))
theorem R153677 : Reach 153677 := rs (se 3 (by rfl) ⟨28814, by rfl⟩) (B 57629 (by norm_num) ⟨28814, by rfl⟩ (by norm_num))
theorem R88145 : Reach 88145 := rs (se 2 (by rfl) ⟨33054, by rfl⟩) (B 66109 (by norm_num) ⟨33054, by rfl⟩ (by norm_num))
theorem R88149 : Reach 88149 := rs (se 8 (by rfl) ⟨516, by rfl⟩) (B 1033 (by norm_num) ⟨516, by rfl⟩ (by norm_num))
theorem R88153 : Reach 88153 := rs (se 2 (by rfl) ⟨33057, by rfl⟩) (B 66115 (by norm_num) ⟨33057, by rfl⟩ (by norm_num))
theorem R88157 : Reach 88157 := rs (se 3 (by rfl) ⟨16529, by rfl⟩) (B 33059 (by norm_num) ⟨16529, by rfl⟩ (by norm_num))
theorem R88161 : Reach 88161 := rs (se 2 (by rfl) ⟨33060, by rfl⟩) (B 66121 (by norm_num) ⟨33060, by rfl⟩ (by norm_num))
theorem R88165 : Reach 88165 := rs (se 4 (by rfl) ⟨8265, by rfl⟩) (B 16531 (by norm_num) ⟨8265, by rfl⟩ (by norm_num))
theorem R88169 : Reach 88169 := rs (se 2 (by rfl) ⟨33063, by rfl⟩) (B 66127 (by norm_num) ⟨33063, by rfl⟩ (by norm_num))
theorem R88173 : Reach 88173 := rs (se 3 (by rfl) ⟨16532, by rfl⟩) (B 33065 (by norm_num) ⟨16532, by rfl⟩ (by norm_num))
theorem R88177 : Reach 88177 := rs (se 2 (by rfl) ⟨33066, by rfl⟩) (B 66133 (by norm_num) ⟨33066, by rfl⟩ (by norm_num))
theorem R88181 : Reach 88181 := rs (se 5 (by rfl) ⟨4133, by rfl⟩) (B 8267 (by norm_num) ⟨4133, by rfl⟩ (by norm_num))
theorem R284789 : Reach 284789 := rs (se 5 (by rfl) ⟨13349, by rfl⟩) (B 26699 (by norm_num) ⟨13349, by rfl⟩ (by norm_num))
theorem R88185 : Reach 88185 := rs (se 2 (by rfl) ⟨33069, by rfl⟩) (B 66139 (by norm_num) ⟨33069, by rfl⟩ (by norm_num))
theorem R88189 : Reach 88189 := rs (se 3 (by rfl) ⟨16535, by rfl⟩) (B 33071 (by norm_num) ⟨16535, by rfl⟩ (by norm_num))
theorem R88193 : Reach 88193 := rs (se 2 (by rfl) ⟨33072, by rfl⟩) (B 66145 (by norm_num) ⟨33072, by rfl⟩ (by norm_num))
theorem R88197 : Reach 88197 := rs (se 4 (by rfl) ⟨8268, by rfl⟩) (B 16537 (by norm_num) ⟨8268, by rfl⟩ (by norm_num))
theorem R88201 : Reach 88201 := rs (se 2 (by rfl) ⟨33075, by rfl⟩) (B 66151 (by norm_num) ⟨33075, by rfl⟩ (by norm_num))
theorem R88205 : Reach 88205 := rs (se 3 (by rfl) ⟨16538, by rfl⟩) (B 33077 (by norm_num) ⟨16538, by rfl⟩ (by norm_num))
theorem R88209 : Reach 88209 := rs (se 2 (by rfl) ⟨33078, by rfl⟩) (B 66157 (by norm_num) ⟨33078, by rfl⟩ (by norm_num))
theorem R88213 : Reach 88213 := rs (se 6 (by rfl) ⟨2067, by rfl⟩) (B 4135 (by norm_num) ⟨2067, by rfl⟩ (by norm_num))
theorem R88217 : Reach 88217 := rs (se 2 (by rfl) ⟨33081, by rfl⟩) (B 66163 (by norm_num) ⟨33081, by rfl⟩ (by norm_num))
theorem R88221 : Reach 88221 := rs (se 3 (by rfl) ⟨16541, by rfl⟩) (B 33083 (by norm_num) ⟨16541, by rfl⟩ (by norm_num))
theorem R88225 : Reach 88225 := rs (se 2 (by rfl) ⟨33084, by rfl⟩) (B 66169 (by norm_num) ⟨33084, by rfl⟩ (by norm_num))
theorem R88229 : Reach 88229 := rs (se 4 (by rfl) ⟨8271, by rfl⟩) (B 16543 (by norm_num) ⟨8271, by rfl⟩ (by norm_num))
theorem R88233 : Reach 88233 := rs (se 2 (by rfl) ⟨33087, by rfl⟩) (B 66175 (by norm_num) ⟨33087, by rfl⟩ (by norm_num))
theorem R88237 : Reach 88237 := rs (se 3 (by rfl) ⟨16544, by rfl⟩) (B 33089 (by norm_num) ⟨16544, by rfl⟩ (by norm_num))
theorem R88241 : Reach 88241 := rs (se 2 (by rfl) ⟨33090, by rfl⟩) (B 66181 (by norm_num) ⟨33090, by rfl⟩ (by norm_num))
theorem R317621 : Reach 317621 := rs (se 5 (by rfl) ⟨14888, by rfl⟩) (B 29777 (by norm_num) ⟨14888, by rfl⟩ (by norm_num))
theorem R88245 : Reach 88245 := rs (se 5 (by rfl) ⟨4136, by rfl⟩) (B 8273 (by norm_num) ⟨4136, by rfl⟩ (by norm_num))
theorem R88249 : Reach 88249 := rs (se 2 (by rfl) ⟨33093, by rfl⟩) (B 66187 (by norm_num) ⟨33093, by rfl⟩ (by norm_num))
theorem R88253 : Reach 88253 := rs (se 3 (by rfl) ⟨16547, by rfl⟩) (B 33095 (by norm_num) ⟨16547, by rfl⟩ (by norm_num))
theorem R88257 : Reach 88257 := rs (se 2 (by rfl) ⟨33096, by rfl⟩) (B 66193 (by norm_num) ⟨33096, by rfl⟩ (by norm_num))
theorem R88261 : Reach 88261 := rs (se 4 (by rfl) ⟨8274, by rfl⟩) (B 16549 (by norm_num) ⟨8274, by rfl⟩ (by norm_num))
theorem R88265 : Reach 88265 := rs (se 2 (by rfl) ⟨33099, by rfl⟩) (B 66199 (by norm_num) ⟨33099, by rfl⟩ (by norm_num))
theorem R88269 : Reach 88269 := rs (se 3 (by rfl) ⟨16550, by rfl⟩) (B 33101 (by norm_num) ⟨16550, by rfl⟩ (by norm_num))
theorem R88273 : Reach 88273 := rs (se 2 (by rfl) ⟨33102, by rfl⟩) (B 66205 (by norm_num) ⟨33102, by rfl⟩ (by norm_num))
theorem R88277 : Reach 88277 := rs (se 7 (by rfl) ⟨1034, by rfl⟩) (B 2069 (by norm_num) ⟨1034, by rfl⟩ (by norm_num))
theorem R88281 : Reach 88281 := rs (se 2 (by rfl) ⟨33105, by rfl⟩) (B 66211 (by norm_num) ⟨33105, by rfl⟩ (by norm_num))
theorem R88285 : Reach 88285 := rs (se 3 (by rfl) ⟨16553, by rfl⟩) (B 33107 (by norm_num) ⟨16553, by rfl⟩ (by norm_num))
theorem R88289 : Reach 88289 := rs (se 2 (by rfl) ⟨33108, by rfl⟩) (B 66217 (by norm_num) ⟨33108, by rfl⟩ (by norm_num))
theorem R88293 : Reach 88293 := rs (se 4 (by rfl) ⟨8277, by rfl⟩) (B 16555 (by norm_num) ⟨8277, by rfl⟩ (by norm_num))
theorem R88297 : Reach 88297 := rs (se 2 (by rfl) ⟨33111, by rfl⟩) (B 66223 (by norm_num) ⟨33111, by rfl⟩ (by norm_num))
theorem R88301 : Reach 88301 := rs (se 3 (by rfl) ⟨16556, by rfl⟩) (B 33113 (by norm_num) ⟨16556, by rfl⟩ (by norm_num))
theorem R88305 : Reach 88305 := rs (se 2 (by rfl) ⟨33114, by rfl⟩) (B 66229 (by norm_num) ⟨33114, by rfl⟩ (by norm_num))
theorem R88309 : Reach 88309 := rs (se 5 (by rfl) ⟨4139, by rfl⟩) (B 8279 (by norm_num) ⟨4139, by rfl⟩ (by norm_num))
theorem R88313 : Reach 88313 := rs (se 2 (by rfl) ⟨33117, by rfl⟩) (B 66235 (by norm_num) ⟨33117, by rfl⟩ (by norm_num))
theorem R88317 : Reach 88317 := rs (se 3 (by rfl) ⟨16559, by rfl⟩) (B 33119 (by norm_num) ⟨16559, by rfl⟩ (by norm_num))
theorem R88321 : Reach 88321 := rs (se 2 (by rfl) ⟨33120, by rfl⟩) (B 66241 (by norm_num) ⟨33120, by rfl⟩ (by norm_num))
theorem R88325 : Reach 88325 := rs (se 4 (by rfl) ⟨8280, by rfl⟩) (B 16561 (by norm_num) ⟨8280, by rfl⟩ (by norm_num))
theorem R88329 : Reach 88329 := rs (se 2 (by rfl) ⟨33123, by rfl⟩) (B 66247 (by norm_num) ⟨33123, by rfl⟩ (by norm_num))
theorem R88333 : Reach 88333 := rs (se 3 (by rfl) ⟨16562, by rfl⟩) (B 33125 (by norm_num) ⟨16562, by rfl⟩ (by norm_num))
theorem R88337 : Reach 88337 := rs (se 2 (by rfl) ⟨33126, by rfl⟩) (B 66253 (by norm_num) ⟨33126, by rfl⟩ (by norm_num))
theorem R88341 : Reach 88341 := rs (se 6 (by rfl) ⟨2070, by rfl⟩) (B 4141 (by norm_num) ⟨2070, by rfl⟩ (by norm_num))
theorem R88345 : Reach 88345 := rs (se 2 (by rfl) ⟨33129, by rfl⟩) (B 66259 (by norm_num) ⟨33129, by rfl⟩ (by norm_num))
theorem R88349 : Reach 88349 := rs (se 3 (by rfl) ⟨16565, by rfl⟩) (B 33131 (by norm_num) ⟨16565, by rfl⟩ (by norm_num))
theorem R88353 : Reach 88353 := rs (se 2 (by rfl) ⟨33132, by rfl⟩) (B 66265 (by norm_num) ⟨33132, by rfl⟩ (by norm_num))
theorem R88357 : Reach 88357 := rs (se 4 (by rfl) ⟨8283, by rfl⟩) (B 16567 (by norm_num) ⟨8283, by rfl⟩ (by norm_num))
theorem R88361 : Reach 88361 := rs (se 2 (by rfl) ⟨33135, by rfl⟩) (B 66271 (by norm_num) ⟨33135, by rfl⟩ (by norm_num))
theorem R88365 : Reach 88365 := rs (se 3 (by rfl) ⟨16568, by rfl⟩) (B 33137 (by norm_num) ⟨16568, by rfl⟩ (by norm_num))
theorem R88369 : Reach 88369 := rs (se 2 (by rfl) ⟨33138, by rfl⟩) (B 66277 (by norm_num) ⟨33138, by rfl⟩ (by norm_num))
theorem R88373 : Reach 88373 := rs (se 5 (by rfl) ⟨4142, by rfl⟩) (B 8285 (by norm_num) ⟨4142, by rfl⟩ (by norm_num))
theorem R88377 : Reach 88377 := rs (se 2 (by rfl) ⟨33141, by rfl⟩) (B 66283 (by norm_num) ⟨33141, by rfl⟩ (by norm_num))
theorem R88381 : Reach 88381 := rs (se 3 (by rfl) ⟨16571, by rfl⟩) (B 33143 (by norm_num) ⟨16571, by rfl⟩ (by norm_num))
theorem R88385 : Reach 88385 := rs (se 2 (by rfl) ⟨33144, by rfl⟩) (B 66289 (by norm_num) ⟨33144, by rfl⟩ (by norm_num))
theorem R317765 : Reach 317765 := rs (se 4 (by rfl) ⟨29790, by rfl⟩) (B 59581 (by norm_num) ⟨29790, by rfl⟩ (by norm_num))
theorem R88389 : Reach 88389 := rs (se 4 (by rfl) ⟨8286, by rfl⟩) (B 16573 (by norm_num) ⟨8286, by rfl⟩ (by norm_num))
theorem R88393 : Reach 88393 := rs (se 2 (by rfl) ⟨33147, by rfl⟩) (B 66295 (by norm_num) ⟨33147, by rfl⟩ (by norm_num))
theorem R88397 : Reach 88397 := rs (se 3 (by rfl) ⟨16574, by rfl⟩) (B 33149 (by norm_num) ⟨16574, by rfl⟩ (by norm_num))
theorem R88401 : Reach 88401 := rs (se 2 (by rfl) ⟨33150, by rfl⟩) (B 66301 (by norm_num) ⟨33150, by rfl⟩ (by norm_num))
theorem R88405 : Reach 88405 := rs (se 10 (by rfl) ⟨129, by rfl⟩) (B 259 (by norm_num) ⟨129, by rfl⟩ (by norm_num))
theorem R88409 : Reach 88409 := rs (se 2 (by rfl) ⟨33153, by rfl⟩) (B 66307 (by norm_num) ⟨33153, by rfl⟩ (by norm_num))
theorem R88413 : Reach 88413 := rs (se 3 (by rfl) ⟨16577, by rfl⟩) (B 33155 (by norm_num) ⟨16577, by rfl⟩ (by norm_num))
theorem R88417 : Reach 88417 := rs (se 2 (by rfl) ⟨33156, by rfl⟩) (B 66313 (by norm_num) ⟨33156, by rfl⟩ (by norm_num))
theorem R88421 : Reach 88421 := rs (se 4 (by rfl) ⟨8289, by rfl⟩) (B 16579 (by norm_num) ⟨8289, by rfl⟩ (by norm_num))
theorem R88425 : Reach 88425 := rs (se 2 (by rfl) ⟨33159, by rfl⟩) (B 66319 (by norm_num) ⟨33159, by rfl⟩ (by norm_num))
theorem R88429 : Reach 88429 := rs (se 3 (by rfl) ⟨16580, by rfl⟩) (B 33161 (by norm_num) ⟨16580, by rfl⟩ (by norm_num))
theorem R88433 : Reach 88433 := rs (se 2 (by rfl) ⟨33162, by rfl⟩) (B 66325 (by norm_num) ⟨33162, by rfl⟩ (by norm_num))
theorem R88437 : Reach 88437 := rs (se 5 (by rfl) ⟨4145, by rfl⟩) (B 8291 (by norm_num) ⟨4145, by rfl⟩ (by norm_num))
theorem R88441 : Reach 88441 := rs (se 2 (by rfl) ⟨33165, by rfl⟩) (B 66331 (by norm_num) ⟨33165, by rfl⟩ (by norm_num))
theorem R88445 : Reach 88445 := rs (se 3 (by rfl) ⟨16583, by rfl⟩) (B 33167 (by norm_num) ⟨16583, by rfl⟩ (by norm_num))
theorem R88449 : Reach 88449 := rs (se 2 (by rfl) ⟨33168, by rfl⟩) (B 66337 (by norm_num) ⟨33168, by rfl⟩ (by norm_num))
theorem R88453 : Reach 88453 := rs (se 4 (by rfl) ⟨8292, by rfl⟩) (B 16585 (by norm_num) ⟨8292, by rfl⟩ (by norm_num))
theorem R448901 : Reach 448901 := rs (se 4 (by rfl) ⟨42084, by rfl⟩) (B 84169 (by norm_num) ⟨42084, by rfl⟩ (by norm_num))
theorem R88457 : Reach 88457 := rs (se 2 (by rfl) ⟨33171, by rfl⟩) (B 66343 (by norm_num) ⟨33171, by rfl⟩ (by norm_num))
theorem R88461 : Reach 88461 := rs (se 3 (by rfl) ⟨16586, by rfl⟩) (B 33173 (by norm_num) ⟨16586, by rfl⟩ (by norm_num))
theorem R88465 : Reach 88465 := rs (se 2 (by rfl) ⟨33174, by rfl⟩) (B 66349 (by norm_num) ⟨33174, by rfl⟩ (by norm_num))
theorem R88469 : Reach 88469 := rs (se 6 (by rfl) ⟨2073, by rfl⟩) (B 4147 (by norm_num) ⟨2073, by rfl⟩ (by norm_num))
theorem R88473 : Reach 88473 := rs (se 2 (by rfl) ⟨33177, by rfl⟩) (B 66355 (by norm_num) ⟨33177, by rfl⟩ (by norm_num))
theorem R88477 : Reach 88477 := rs (se 3 (by rfl) ⟨16589, by rfl⟩) (B 33179 (by norm_num) ⟨16589, by rfl⟩ (by norm_num))
theorem R88481 : Reach 88481 := rs (se 2 (by rfl) ⟨33180, by rfl⟩) (B 66361 (by norm_num) ⟨33180, by rfl⟩ (by norm_num))
theorem R88485 : Reach 88485 := rs (se 4 (by rfl) ⟨8295, by rfl⟩) (B 16591 (by norm_num) ⟨8295, by rfl⟩ (by norm_num))
theorem R252325 : Reach 252325 := rs (se 4 (by rfl) ⟨23655, by rfl⟩) (B 47311 (by norm_num) ⟨23655, by rfl⟩ (by norm_num))
theorem R88489 : Reach 88489 := rs (se 2 (by rfl) ⟨33183, by rfl⟩) (B 66367 (by norm_num) ⟨33183, by rfl⟩ (by norm_num))
theorem R88493 : Reach 88493 := rs (se 3 (by rfl) ⟨16592, by rfl⟩) (B 33185 (by norm_num) ⟨16592, by rfl⟩ (by norm_num))
theorem R88497 : Reach 88497 := rs (se 2 (by rfl) ⟨33186, by rfl⟩) (B 66373 (by norm_num) ⟨33186, by rfl⟩ (by norm_num))
theorem R88501 : Reach 88501 := rs (se 5 (by rfl) ⟨4148, by rfl⟩) (B 8297 (by norm_num) ⟨4148, by rfl⟩ (by norm_num))
theorem R88505 : Reach 88505 := rs (se 2 (by rfl) ⟨33189, by rfl⟩) (B 66379 (by norm_num) ⟨33189, by rfl⟩ (by norm_num))
theorem R88509 : Reach 88509 := rs (se 3 (by rfl) ⟨16595, by rfl⟩) (B 33191 (by norm_num) ⟨16595, by rfl⟩ (by norm_num))
theorem R88513 : Reach 88513 := rs (se 2 (by rfl) ⟨33192, by rfl⟩) (B 66385 (by norm_num) ⟨33192, by rfl⟩ (by norm_num))
theorem R88517 : Reach 88517 := rs (se 4 (by rfl) ⟨8298, by rfl⟩) (B 16597 (by norm_num) ⟨8298, by rfl⟩ (by norm_num))
theorem R88521 : Reach 88521 := rs (se 2 (by rfl) ⟨33195, by rfl⟩) (B 66391 (by norm_num) ⟨33195, by rfl⟩ (by norm_num))
theorem R88525 : Reach 88525 := rs (se 3 (by rfl) ⟨16598, by rfl⟩) (B 33197 (by norm_num) ⟨16598, by rfl⟩ (by norm_num))
theorem R88529 : Reach 88529 := rs (se 2 (by rfl) ⟨33198, by rfl⟩) (B 66397 (by norm_num) ⟨33198, by rfl⟩ (by norm_num))
theorem R88533 : Reach 88533 := rs (se 7 (by rfl) ⟨1037, by rfl⟩) (B 2075 (by norm_num) ⟨1037, by rfl⟩ (by norm_num))
theorem R88537 : Reach 88537 := rs (se 2 (by rfl) ⟨33201, by rfl⟩) (B 66403 (by norm_num) ⟨33201, by rfl⟩ (by norm_num))
theorem R88541 : Reach 88541 := rs (se 3 (by rfl) ⟨16601, by rfl⟩) (B 33203 (by norm_num) ⟨16601, by rfl⟩ (by norm_num))
theorem R88545 : Reach 88545 := rs (se 2 (by rfl) ⟨33204, by rfl⟩) (B 66409 (by norm_num) ⟨33204, by rfl⟩ (by norm_num))
theorem R88549 : Reach 88549 := rs (se 4 (by rfl) ⟨8301, by rfl⟩) (B 16603 (by norm_num) ⟨8301, by rfl⟩ (by norm_num))
theorem R88553 : Reach 88553 := rs (se 2 (by rfl) ⟨33207, by rfl⟩) (B 66415 (by norm_num) ⟨33207, by rfl⟩ (by norm_num))
theorem R88557 : Reach 88557 := rs (se 3 (by rfl) ⟨16604, by rfl⟩) (B 33209 (by norm_num) ⟨16604, by rfl⟩ (by norm_num))
theorem R88561 : Reach 88561 := rs (se 2 (by rfl) ⟨33210, by rfl⟩) (B 66421 (by norm_num) ⟨33210, by rfl⟩ (by norm_num))
theorem R88565 : Reach 88565 := rs (se 5 (by rfl) ⟨4151, by rfl⟩) (B 8303 (by norm_num) ⟨4151, by rfl⟩ (by norm_num))
theorem R88569 : Reach 88569 := rs (se 2 (by rfl) ⟨33213, by rfl⟩) (B 66427 (by norm_num) ⟨33213, by rfl⟩ (by norm_num))
theorem R88573 : Reach 88573 := rs (se 3 (by rfl) ⟨16607, by rfl⟩) (B 33215 (by norm_num) ⟨16607, by rfl⟩ (by norm_num))
theorem R88577 : Reach 88577 := rs (se 2 (by rfl) ⟨33216, by rfl⟩) (B 66433 (by norm_num) ⟨33216, by rfl⟩ (by norm_num))
theorem R88581 : Reach 88581 := rs (se 4 (by rfl) ⟨8304, by rfl⟩) (B 16609 (by norm_num) ⟨8304, by rfl⟩ (by norm_num))
theorem R88585 : Reach 88585 := rs (se 2 (by rfl) ⟨33219, by rfl⟩) (B 66439 (by norm_num) ⟨33219, by rfl⟩ (by norm_num))
theorem R88589 : Reach 88589 := rs (se 3 (by rfl) ⟨16610, by rfl⟩) (B 33221 (by norm_num) ⟨16610, by rfl⟩ (by norm_num))
theorem R88593 : Reach 88593 := rs (se 2 (by rfl) ⟨33222, by rfl⟩) (B 66445 (by norm_num) ⟨33222, by rfl⟩ (by norm_num))
theorem R88597 : Reach 88597 := rs (se 6 (by rfl) ⟨2076, by rfl⟩) (B 4153 (by norm_num) ⟨2076, by rfl⟩ (by norm_num))
theorem R88601 : Reach 88601 := rs (se 2 (by rfl) ⟨33225, by rfl⟩) (B 66451 (by norm_num) ⟨33225, by rfl⟩ (by norm_num))
theorem R88605 : Reach 88605 := rs (se 3 (by rfl) ⟨16613, by rfl⟩) (B 33227 (by norm_num) ⟨16613, by rfl⟩ (by norm_num))
theorem R88609 : Reach 88609 := rs (se 2 (by rfl) ⟨33228, by rfl⟩) (B 66457 (by norm_num) ⟨33228, by rfl⟩ (by norm_num))
theorem R88613 : Reach 88613 := rs (se 4 (by rfl) ⟨8307, by rfl⟩) (B 16615 (by norm_num) ⟨8307, by rfl⟩ (by norm_num))
theorem R88617 : Reach 88617 := rs (se 2 (by rfl) ⟨33231, by rfl⟩) (B 66463 (by norm_num) ⟨33231, by rfl⟩ (by norm_num))
theorem R88621 : Reach 88621 := rs (se 3 (by rfl) ⟨16616, by rfl⟩) (B 33233 (by norm_num) ⟨16616, by rfl⟩ (by norm_num))
theorem R88625 : Reach 88625 := rs (se 2 (by rfl) ⟨33234, by rfl⟩) (B 66469 (by norm_num) ⟨33234, by rfl⟩ (by norm_num))
theorem R88629 : Reach 88629 := rs (se 5 (by rfl) ⟨4154, by rfl⟩) (B 8309 (by norm_num) ⟨4154, by rfl⟩ (by norm_num))
theorem R88633 : Reach 88633 := rs (se 2 (by rfl) ⟨33237, by rfl⟩) (B 66475 (by norm_num) ⟨33237, by rfl⟩ (by norm_num))
theorem R88637 : Reach 88637 := rs (se 3 (by rfl) ⟨16619, by rfl⟩) (B 33239 (by norm_num) ⟨16619, by rfl⟩ (by norm_num))
theorem R88641 : Reach 88641 := rs (se 2 (by rfl) ⟨33240, by rfl⟩) (B 66481 (by norm_num) ⟨33240, by rfl⟩ (by norm_num))
theorem R88645 : Reach 88645 := rs (se 4 (by rfl) ⟨8310, by rfl⟩) (B 16621 (by norm_num) ⟨8310, by rfl⟩ (by norm_num))
theorem R88649 : Reach 88649 := rs (se 2 (by rfl) ⟨33243, by rfl⟩) (B 66487 (by norm_num) ⟨33243, by rfl⟩ (by norm_num))
theorem R88653 : Reach 88653 := rs (se 3 (by rfl) ⟨16622, by rfl⟩) (B 33245 (by norm_num) ⟨16622, by rfl⟩ (by norm_num))
theorem R88657 : Reach 88657 := rs (se 2 (by rfl) ⟨33246, by rfl⟩) (B 66493 (by norm_num) ⟨33246, by rfl⟩ (by norm_num))
theorem R88661 : Reach 88661 := rs (se 8 (by rfl) ⟨519, by rfl⟩) (B 1039 (by norm_num) ⟨519, by rfl⟩ (by norm_num))
theorem R88665 : Reach 88665 := rs (se 2 (by rfl) ⟨33249, by rfl⟩) (B 66499 (by norm_num) ⟨33249, by rfl⟩ (by norm_num))
theorem R88669 : Reach 88669 := rs (se 3 (by rfl) ⟨16625, by rfl⟩) (B 33251 (by norm_num) ⟨16625, by rfl⟩ (by norm_num))
theorem R88673 : Reach 88673 := rs (se 2 (by rfl) ⟨33252, by rfl⟩) (B 66505 (by norm_num) ⟨33252, by rfl⟩ (by norm_num))
theorem R88677 : Reach 88677 := rs (se 4 (by rfl) ⟨8313, by rfl⟩) (B 16627 (by norm_num) ⟨8313, by rfl⟩ (by norm_num))
theorem R88681 : Reach 88681 := rs (se 2 (by rfl) ⟨33255, by rfl⟩) (B 66511 (by norm_num) ⟨33255, by rfl⟩ (by norm_num))
theorem R88685 : Reach 88685 := rs (se 3 (by rfl) ⟨16628, by rfl⟩) (B 33257 (by norm_num) ⟨16628, by rfl⟩ (by norm_num))
theorem R88689 : Reach 88689 := rs (se 2 (by rfl) ⟨33258, by rfl⟩) (B 66517 (by norm_num) ⟨33258, by rfl⟩ (by norm_num))
theorem R88693 : Reach 88693 := rs (se 5 (by rfl) ⟨4157, by rfl⟩) (B 8315 (by norm_num) ⟨4157, by rfl⟩ (by norm_num))
theorem R88697 : Reach 88697 := rs (se 2 (by rfl) ⟨33261, by rfl⟩) (B 66523 (by norm_num) ⟨33261, by rfl⟩ (by norm_num))
theorem R88701 : Reach 88701 := rs (se 3 (by rfl) ⟨16631, by rfl⟩) (B 33263 (by norm_num) ⟨16631, by rfl⟩ (by norm_num))
theorem R88705 : Reach 88705 := rs (se 2 (by rfl) ⟨33264, by rfl⟩) (B 66529 (by norm_num) ⟨33264, by rfl⟩ (by norm_num))
theorem R88709 : Reach 88709 := rs (se 4 (by rfl) ⟨8316, by rfl⟩) (B 16633 (by norm_num) ⟨8316, by rfl⟩ (by norm_num))
theorem R88713 : Reach 88713 := rs (se 2 (by rfl) ⟨33267, by rfl⟩) (B 66535 (by norm_num) ⟨33267, by rfl⟩ (by norm_num))
theorem R88717 : Reach 88717 := rs (se 3 (by rfl) ⟨16634, by rfl⟩) (B 33269 (by norm_num) ⟨16634, by rfl⟩ (by norm_num))
theorem R88721 : Reach 88721 := rs (se 2 (by rfl) ⟨33270, by rfl⟩) (B 66541 (by norm_num) ⟨33270, by rfl⟩ (by norm_num))
theorem R88725 : Reach 88725 := rs (se 6 (by rfl) ⟨2079, by rfl⟩) (B 4159 (by norm_num) ⟨2079, by rfl⟩ (by norm_num))
theorem R88729 : Reach 88729 := rs (se 2 (by rfl) ⟨33273, by rfl⟩) (B 66547 (by norm_num) ⟨33273, by rfl⟩ (by norm_num))
theorem R88733 : Reach 88733 := rs (se 3 (by rfl) ⟨16637, by rfl⟩) (B 33275 (by norm_num) ⟨16637, by rfl⟩ (by norm_num))
theorem R88737 : Reach 88737 := rs (se 2 (by rfl) ⟨33276, by rfl⟩) (B 66553 (by norm_num) ⟨33276, by rfl⟩ (by norm_num))
theorem R88741 : Reach 88741 := rs (se 4 (by rfl) ⟨8319, by rfl⟩) (B 16639 (by norm_num) ⟨8319, by rfl⟩ (by norm_num))
theorem R88745 : Reach 88745 := rs (se 2 (by rfl) ⟨33279, by rfl⟩) (B 66559 (by norm_num) ⟨33279, by rfl⟩ (by norm_num))
theorem R88749 : Reach 88749 := rs (se 3 (by rfl) ⟨16640, by rfl⟩) (B 33281 (by norm_num) ⟨16640, by rfl⟩ (by norm_num))
theorem R88753 : Reach 88753 := rs (se 2 (by rfl) ⟨33282, by rfl⟩) (B 66565 (by norm_num) ⟨33282, by rfl⟩ (by norm_num))
theorem R88757 : Reach 88757 := rs (se 5 (by rfl) ⟨4160, by rfl⟩) (B 8321 (by norm_num) ⟨4160, by rfl⟩ (by norm_num))
theorem R88761 : Reach 88761 := rs (se 2 (by rfl) ⟨33285, by rfl⟩) (B 66571 (by norm_num) ⟨33285, by rfl⟩ (by norm_num))
theorem R88765 : Reach 88765 := rs (se 3 (by rfl) ⟨16643, by rfl⟩) (B 33287 (by norm_num) ⟨16643, by rfl⟩ (by norm_num))
theorem R88769 : Reach 88769 := rs (se 2 (by rfl) ⟨33288, by rfl⟩) (B 66577 (by norm_num) ⟨33288, by rfl⟩ (by norm_num))
theorem R88773 : Reach 88773 := rs (se 4 (by rfl) ⟨8322, by rfl⟩) (B 16645 (by norm_num) ⟨8322, by rfl⟩ (by norm_num))
theorem R88777 : Reach 88777 := rs (se 2 (by rfl) ⟨33291, by rfl⟩) (B 66583 (by norm_num) ⟨33291, by rfl⟩ (by norm_num))
theorem R88781 : Reach 88781 := rs (se 3 (by rfl) ⟨16646, by rfl⟩) (B 33293 (by norm_num) ⟨16646, by rfl⟩ (by norm_num))
theorem R88785 : Reach 88785 := rs (se 2 (by rfl) ⟨33294, by rfl⟩) (B 66589 (by norm_num) ⟨33294, by rfl⟩ (by norm_num))
theorem R88789 : Reach 88789 := rs (se 7 (by rfl) ⟨1040, by rfl⟩) (B 2081 (by norm_num) ⟨1040, by rfl⟩ (by norm_num))
theorem R88793 : Reach 88793 := rs (se 2 (by rfl) ⟨33297, by rfl⟩) (B 66595 (by norm_num) ⟨33297, by rfl⟩ (by norm_num))
theorem R88797 : Reach 88797 := rs (se 3 (by rfl) ⟨16649, by rfl⟩) (B 33299 (by norm_num) ⟨16649, by rfl⟩ (by norm_num))
theorem R88801 : Reach 88801 := rs (se 2 (by rfl) ⟨33300, by rfl⟩) (B 66601 (by norm_num) ⟨33300, by rfl⟩ (by norm_num))
theorem R88805 : Reach 88805 := rs (se 4 (by rfl) ⟨8325, by rfl⟩) (B 16651 (by norm_num) ⟨8325, by rfl⟩ (by norm_num))
theorem R383717 : Reach 383717 := rs (se 4 (by rfl) ⟨35973, by rfl⟩) (B 71947 (by norm_num) ⟨35973, by rfl⟩ (by norm_num))
theorem R88809 : Reach 88809 := rs (se 2 (by rfl) ⟨33303, by rfl⟩) (B 66607 (by norm_num) ⟨33303, by rfl⟩ (by norm_num))
theorem R88813 : Reach 88813 := rs (se 3 (by rfl) ⟨16652, by rfl⟩) (B 33305 (by norm_num) ⟨16652, by rfl⟩ (by norm_num))
theorem R88817 : Reach 88817 := rs (se 2 (by rfl) ⟨33306, by rfl⟩) (B 66613 (by norm_num) ⟨33306, by rfl⟩ (by norm_num))
theorem R88821 : Reach 88821 := rs (se 5 (by rfl) ⟨4163, by rfl⟩) (B 8327 (by norm_num) ⟨4163, by rfl⟩ (by norm_num))
theorem R88825 : Reach 88825 := rs (se 2 (by rfl) ⟨33309, by rfl⟩) (B 66619 (by norm_num) ⟨33309, by rfl⟩ (by norm_num))
theorem R88829 : Reach 88829 := rs (se 3 (by rfl) ⟨16655, by rfl⟩) (B 33311 (by norm_num) ⟨16655, by rfl⟩ (by norm_num))
theorem R88833 : Reach 88833 := rs (se 2 (by rfl) ⟨33312, by rfl⟩) (B 66625 (by norm_num) ⟨33312, by rfl⟩ (by norm_num))
theorem R88837 : Reach 88837 := rs (se 4 (by rfl) ⟨8328, by rfl⟩) (B 16657 (by norm_num) ⟨8328, by rfl⟩ (by norm_num))
theorem R88841 : Reach 88841 := rs (se 2 (by rfl) ⟨33315, by rfl⟩) (B 66631 (by norm_num) ⟨33315, by rfl⟩ (by norm_num))
theorem R88845 : Reach 88845 := rs (se 3 (by rfl) ⟨16658, by rfl⟩) (B 33317 (by norm_num) ⟨16658, by rfl⟩ (by norm_num))
theorem R88849 : Reach 88849 := rs (se 2 (by rfl) ⟨33318, by rfl⟩) (B 66637 (by norm_num) ⟨33318, by rfl⟩ (by norm_num))
theorem R88853 : Reach 88853 := rs (se 6 (by rfl) ⟨2082, by rfl⟩) (B 4165 (by norm_num) ⟨2082, by rfl⟩ (by norm_num))
theorem R88857 : Reach 88857 := rs (se 2 (by rfl) ⟨33321, by rfl⟩) (B 66643 (by norm_num) ⟨33321, by rfl⟩ (by norm_num))
theorem R88861 : Reach 88861 := rs (se 3 (by rfl) ⟨16661, by rfl⟩) (B 33323 (by norm_num) ⟨16661, by rfl⟩ (by norm_num))
theorem R88865 : Reach 88865 := rs (se 2 (by rfl) ⟨33324, by rfl⟩) (B 66649 (by norm_num) ⟨33324, by rfl⟩ (by norm_num))
theorem R88869 : Reach 88869 := rs (se 4 (by rfl) ⟨8331, by rfl⟩) (B 16663 (by norm_num) ⟨8331, by rfl⟩ (by norm_num))
theorem R88873 : Reach 88873 := rs (se 2 (by rfl) ⟨33327, by rfl⟩) (B 66655 (by norm_num) ⟨33327, by rfl⟩ (by norm_num))
theorem R88877 : Reach 88877 := rs (se 3 (by rfl) ⟨16664, by rfl⟩) (B 33329 (by norm_num) ⟨16664, by rfl⟩ (by norm_num))
theorem R88881 : Reach 88881 := rs (se 2 (by rfl) ⟨33330, by rfl⟩) (B 66661 (by norm_num) ⟨33330, by rfl⟩ (by norm_num))
theorem R88885 : Reach 88885 := rs (se 5 (by rfl) ⟨4166, by rfl⟩) (B 8333 (by norm_num) ⟨4166, by rfl⟩ (by norm_num))
theorem R88889 : Reach 88889 := rs (se 2 (by rfl) ⟨33333, by rfl⟩) (B 66667 (by norm_num) ⟨33333, by rfl⟩ (by norm_num))
theorem R88893 : Reach 88893 := rs (se 3 (by rfl) ⟨16667, by rfl⟩) (B 33335 (by norm_num) ⟨16667, by rfl⟩ (by norm_num))
theorem R88897 : Reach 88897 := rs (se 2 (by rfl) ⟨33336, by rfl⟩) (B 66673 (by norm_num) ⟨33336, by rfl⟩ (by norm_num))
theorem R88901 : Reach 88901 := rs (se 4 (by rfl) ⟨8334, by rfl⟩) (B 16669 (by norm_num) ⟨8334, by rfl⟩ (by norm_num))
theorem R88905 : Reach 88905 := rs (se 2 (by rfl) ⟨33339, by rfl⟩) (B 66679 (by norm_num) ⟨33339, by rfl⟩ (by norm_num))
theorem R88909 : Reach 88909 := rs (se 3 (by rfl) ⟨16670, by rfl⟩) (B 33341 (by norm_num) ⟨16670, by rfl⟩ (by norm_num))
theorem R88913 : Reach 88913 := rs (se 2 (by rfl) ⟨33342, by rfl⟩) (B 66685 (by norm_num) ⟨33342, by rfl⟩ (by norm_num))
theorem R88917 : Reach 88917 := rs (se 9 (by rfl) ⟨260, by rfl⟩) (B 521 (by norm_num) ⟨260, by rfl⟩ (by norm_num))
theorem R88921 : Reach 88921 := rs (se 2 (by rfl) ⟨33345, by rfl⟩) (B 66691 (by norm_num) ⟨33345, by rfl⟩ (by norm_num))
theorem R88925 : Reach 88925 := rs (se 3 (by rfl) ⟨16673, by rfl⟩) (B 33347 (by norm_num) ⟨16673, by rfl⟩ (by norm_num))
theorem R88929 : Reach 88929 := rs (se 2 (by rfl) ⟨33348, by rfl⟩) (B 66697 (by norm_num) ⟨33348, by rfl⟩ (by norm_num))
theorem R88933 : Reach 88933 := rs (se 4 (by rfl) ⟨8337, by rfl⟩) (B 16675 (by norm_num) ⟨8337, by rfl⟩ (by norm_num))
theorem R154469 : Reach 154469 := rs (se 4 (by rfl) ⟨14481, by rfl⟩) (B 28963 (by norm_num) ⟨14481, by rfl⟩ (by norm_num))
theorem R88937 : Reach 88937 := rs (se 2 (by rfl) ⟨33351, by rfl⟩) (B 66703 (by norm_num) ⟨33351, by rfl⟩ (by norm_num))
theorem R88941 : Reach 88941 := rs (se 3 (by rfl) ⟨16676, by rfl⟩) (B 33353 (by norm_num) ⟨16676, by rfl⟩ (by norm_num))
theorem R88945 : Reach 88945 := rs (se 2 (by rfl) ⟨33354, by rfl⟩) (B 66709 (by norm_num) ⟨33354, by rfl⟩ (by norm_num))
theorem R88949 : Reach 88949 := rs (se 5 (by rfl) ⟨4169, by rfl⟩) (B 8339 (by norm_num) ⟨4169, by rfl⟩ (by norm_num))
theorem R88953 : Reach 88953 := rs (se 2 (by rfl) ⟨33357, by rfl⟩) (B 66715 (by norm_num) ⟨33357, by rfl⟩ (by norm_num))
theorem R88957 : Reach 88957 := rs (se 3 (by rfl) ⟨16679, by rfl⟩) (B 33359 (by norm_num) ⟨16679, by rfl⟩ (by norm_num))
theorem R88961 : Reach 88961 := rs (se 2 (by rfl) ⟨33360, by rfl⟩) (B 66721 (by norm_num) ⟨33360, by rfl⟩ (by norm_num))
theorem R88965 : Reach 88965 := rs (se 4 (by rfl) ⟨8340, by rfl⟩) (B 16681 (by norm_num) ⟨8340, by rfl⟩ (by norm_num))
theorem R88969 : Reach 88969 := rs (se 2 (by rfl) ⟨33363, by rfl⟩) (B 66727 (by norm_num) ⟨33363, by rfl⟩ (by norm_num))
theorem R88973 : Reach 88973 := rs (se 3 (by rfl) ⟨16682, by rfl⟩) (B 33365 (by norm_num) ⟨16682, by rfl⟩ (by norm_num))
theorem R88977 : Reach 88977 := rs (se 2 (by rfl) ⟨33366, by rfl⟩) (B 66733 (by norm_num) ⟨33366, by rfl⟩ (by norm_num))
theorem R88981 : Reach 88981 := rs (se 6 (by rfl) ⟨2085, by rfl⟩) (B 4171 (by norm_num) ⟨2085, by rfl⟩ (by norm_num))
theorem R88985 : Reach 88985 := rs (se 2 (by rfl) ⟨33369, by rfl⟩) (B 66739 (by norm_num) ⟨33369, by rfl⟩ (by norm_num))
theorem R88989 : Reach 88989 := rs (se 3 (by rfl) ⟨16685, by rfl⟩) (B 33371 (by norm_num) ⟨16685, by rfl⟩ (by norm_num))
theorem R88993 : Reach 88993 := rs (se 2 (by rfl) ⟨33372, by rfl⟩) (B 66745 (by norm_num) ⟨33372, by rfl⟩ (by norm_num))
theorem R88997 : Reach 88997 := rs (se 4 (by rfl) ⟨8343, by rfl⟩) (B 16687 (by norm_num) ⟨8343, by rfl⟩ (by norm_num))
theorem R89001 : Reach 89001 := rs (se 2 (by rfl) ⟨33375, by rfl⟩) (B 66751 (by norm_num) ⟨33375, by rfl⟩ (by norm_num))
theorem R89005 : Reach 89005 := rs (se 3 (by rfl) ⟨16688, by rfl⟩) (B 33377 (by norm_num) ⟨16688, by rfl⟩ (by norm_num))
theorem R89009 : Reach 89009 := rs (se 2 (by rfl) ⟨33378, by rfl⟩) (B 66757 (by norm_num) ⟨33378, by rfl⟩ (by norm_num))
theorem R89013 : Reach 89013 := rs (se 5 (by rfl) ⟨4172, by rfl⟩) (B 8345 (by norm_num) ⟨4172, by rfl⟩ (by norm_num))
theorem R89017 : Reach 89017 := rs (se 2 (by rfl) ⟨33381, by rfl⟩) (B 66763 (by norm_num) ⟨33381, by rfl⟩ (by norm_num))
theorem R89021 : Reach 89021 := rs (se 3 (by rfl) ⟨16691, by rfl⟩) (B 33383 (by norm_num) ⟨16691, by rfl⟩ (by norm_num))
theorem R89025 : Reach 89025 := rs (se 2 (by rfl) ⟨33384, by rfl⟩) (B 66769 (by norm_num) ⟨33384, by rfl⟩ (by norm_num))
theorem R89029 : Reach 89029 := rs (se 4 (by rfl) ⟨8346, by rfl⟩) (B 16693 (by norm_num) ⟨8346, by rfl⟩ (by norm_num))
theorem R89033 : Reach 89033 := rs (se 2 (by rfl) ⟨33387, by rfl⟩) (B 66775 (by norm_num) ⟨33387, by rfl⟩ (by norm_num))
theorem R89037 : Reach 89037 := rs (se 3 (by rfl) ⟨16694, by rfl⟩) (B 33389 (by norm_num) ⟨16694, by rfl⟩ (by norm_num))
theorem R89041 : Reach 89041 := rs (se 2 (by rfl) ⟨33390, by rfl⟩) (B 66781 (by norm_num) ⟨33390, by rfl⟩ (by norm_num))
theorem R89045 : Reach 89045 := rs (se 7 (by rfl) ⟨1043, by rfl⟩) (B 2087 (by norm_num) ⟨1043, by rfl⟩ (by norm_num))
theorem R89049 : Reach 89049 := rs (se 2 (by rfl) ⟨33393, by rfl⟩) (B 66787 (by norm_num) ⟨33393, by rfl⟩ (by norm_num))
theorem R89053 : Reach 89053 := rs (se 3 (by rfl) ⟨16697, by rfl⟩) (B 33395 (by norm_num) ⟨16697, by rfl⟩ (by norm_num))
theorem R89057 : Reach 89057 := rs (se 2 (by rfl) ⟨33396, by rfl⟩) (B 66793 (by norm_num) ⟨33396, by rfl⟩ (by norm_num))
theorem R89061 : Reach 89061 := rs (se 4 (by rfl) ⟨8349, by rfl⟩) (B 16699 (by norm_num) ⟨8349, by rfl⟩ (by norm_num))
theorem R89065 : Reach 89065 := rs (se 2 (by rfl) ⟨33399, by rfl⟩) (B 66799 (by norm_num) ⟨33399, by rfl⟩ (by norm_num))
theorem R89069 : Reach 89069 := rs (se 3 (by rfl) ⟨16700, by rfl⟩) (B 33401 (by norm_num) ⟨16700, by rfl⟩ (by norm_num))
theorem R89073 : Reach 89073 := rs (se 2 (by rfl) ⟨33402, by rfl⟩) (B 66805 (by norm_num) ⟨33402, by rfl⟩ (by norm_num))
theorem R89077 : Reach 89077 := rs (se 5 (by rfl) ⟨4175, by rfl⟩) (B 8351 (by norm_num) ⟨4175, by rfl⟩ (by norm_num))
theorem R89081 : Reach 89081 := rs (se 2 (by rfl) ⟨33405, by rfl⟩) (B 66811 (by norm_num) ⟨33405, by rfl⟩ (by norm_num))
theorem R89085 : Reach 89085 := rs (se 3 (by rfl) ⟨16703, by rfl⟩) (B 33407 (by norm_num) ⟨16703, by rfl⟩ (by norm_num))
theorem R89089 : Reach 89089 := rs (se 2 (by rfl) ⟨33408, by rfl⟩) (B 66817 (by norm_num) ⟨33408, by rfl⟩ (by norm_num))
theorem R89093 : Reach 89093 := rs (se 4 (by rfl) ⟨8352, by rfl⟩) (B 16705 (by norm_num) ⟨8352, by rfl⟩ (by norm_num))
theorem R89097 : Reach 89097 := rs (se 2 (by rfl) ⟨33411, by rfl⟩) (B 66823 (by norm_num) ⟨33411, by rfl⟩ (by norm_num))
theorem R89101 : Reach 89101 := rs (se 3 (by rfl) ⟨16706, by rfl⟩) (B 33413 (by norm_num) ⟨16706, by rfl⟩ (by norm_num))
theorem R89105 : Reach 89105 := rs (se 2 (by rfl) ⟨33414, by rfl⟩) (B 66829 (by norm_num) ⟨33414, by rfl⟩ (by norm_num))
theorem R89109 : Reach 89109 := rs (se 6 (by rfl) ⟨2088, by rfl⟩) (B 4177 (by norm_num) ⟨2088, by rfl⟩ (by norm_num))
theorem R89113 : Reach 89113 := rs (se 2 (by rfl) ⟨33417, by rfl⟩) (B 66835 (by norm_num) ⟨33417, by rfl⟩ (by norm_num))
theorem R89117 : Reach 89117 := rs (se 3 (by rfl) ⟨16709, by rfl⟩) (B 33419 (by norm_num) ⟨16709, by rfl⟩ (by norm_num))
theorem R89121 : Reach 89121 := rs (se 2 (by rfl) ⟨33420, by rfl⟩) (B 66841 (by norm_num) ⟨33420, by rfl⟩ (by norm_num))
theorem R89125 : Reach 89125 := rs (se 4 (by rfl) ⟨8355, by rfl⟩) (B 16711 (by norm_num) ⟨8355, by rfl⟩ (by norm_num))
theorem R89129 : Reach 89129 := rs (se 2 (by rfl) ⟨33423, by rfl⟩) (B 66847 (by norm_num) ⟨33423, by rfl⟩ (by norm_num))
theorem R89133 : Reach 89133 := rs (se 3 (by rfl) ⟨16712, by rfl⟩) (B 33425 (by norm_num) ⟨16712, by rfl⟩ (by norm_num))
theorem R89137 : Reach 89137 := rs (se 2 (by rfl) ⟨33426, by rfl⟩) (B 66853 (by norm_num) ⟨33426, by rfl⟩ (by norm_num))
theorem R89141 : Reach 89141 := rs (se 5 (by rfl) ⟨4178, by rfl⟩) (B 8357 (by norm_num) ⟨4178, by rfl⟩ (by norm_num))
theorem R89145 : Reach 89145 := rs (se 2 (by rfl) ⟨33429, by rfl⟩) (B 66859 (by norm_num) ⟨33429, by rfl⟩ (by norm_num))
theorem R89149 : Reach 89149 := rs (se 3 (by rfl) ⟨16715, by rfl⟩) (B 33431 (by norm_num) ⟨16715, by rfl⟩ (by norm_num))
theorem R89153 : Reach 89153 := rs (se 2 (by rfl) ⟨33432, by rfl⟩) (B 66865 (by norm_num) ⟨33432, by rfl⟩ (by norm_num))
theorem R89157 : Reach 89157 := rs (se 4 (by rfl) ⟨8358, by rfl⟩) (B 16717 (by norm_num) ⟨8358, by rfl⟩ (by norm_num))
theorem R89161 : Reach 89161 := rs (se 2 (by rfl) ⟨33435, by rfl⟩) (B 66871 (by norm_num) ⟨33435, by rfl⟩ (by norm_num))
theorem R89165 : Reach 89165 := rs (se 3 (by rfl) ⟨16718, by rfl⟩) (B 33437 (by norm_num) ⟨16718, by rfl⟩ (by norm_num))
theorem R89169 : Reach 89169 := rs (se 2 (by rfl) ⟨33438, by rfl⟩) (B 66877 (by norm_num) ⟨33438, by rfl⟩ (by norm_num))
theorem R89173 : Reach 89173 := rs (se 8 (by rfl) ⟨522, by rfl⟩) (B 1045 (by norm_num) ⟨522, by rfl⟩ (by norm_num))
theorem R89177 : Reach 89177 := rs (se 2 (by rfl) ⟨33441, by rfl⟩) (B 66883 (by norm_num) ⟨33441, by rfl⟩ (by norm_num))
theorem R89181 : Reach 89181 := rs (se 3 (by rfl) ⟨16721, by rfl⟩) (B 33443 (by norm_num) ⟨16721, by rfl⟩ (by norm_num))
theorem R89185 : Reach 89185 := rs (se 2 (by rfl) ⟨33444, by rfl⟩) (B 66889 (by norm_num) ⟨33444, by rfl⟩ (by norm_num))
theorem R89189 : Reach 89189 := rs (se 4 (by rfl) ⟨8361, by rfl⟩) (B 16723 (by norm_num) ⟨8361, by rfl⟩ (by norm_num))
theorem R89193 : Reach 89193 := rs (se 2 (by rfl) ⟨33447, by rfl⟩) (B 66895 (by norm_num) ⟨33447, by rfl⟩ (by norm_num))
theorem R89197 : Reach 89197 := rs (se 3 (by rfl) ⟨16724, by rfl⟩) (B 33449 (by norm_num) ⟨16724, by rfl⟩ (by norm_num))
theorem R89201 : Reach 89201 := rs (se 2 (by rfl) ⟨33450, by rfl⟩) (B 66901 (by norm_num) ⟨33450, by rfl⟩ (by norm_num))
theorem R89205 : Reach 89205 := rs (se 5 (by rfl) ⟨4181, by rfl⟩) (B 8363 (by norm_num) ⟨4181, by rfl⟩ (by norm_num))
theorem R89209 : Reach 89209 := rs (se 2 (by rfl) ⟨33453, by rfl⟩) (B 66907 (by norm_num) ⟨33453, by rfl⟩ (by norm_num))
theorem R89213 : Reach 89213 := rs (se 3 (by rfl) ⟨16727, by rfl⟩) (B 33455 (by norm_num) ⟨16727, by rfl⟩ (by norm_num))
theorem R89217 : Reach 89217 := rs (se 2 (by rfl) ⟨33456, by rfl⟩) (B 66913 (by norm_num) ⟨33456, by rfl⟩ (by norm_num))
theorem R89221 : Reach 89221 := rs (se 4 (by rfl) ⟨8364, by rfl⟩) (B 16729 (by norm_num) ⟨8364, by rfl⟩ (by norm_num))
theorem R89225 : Reach 89225 := rs (se 2 (by rfl) ⟨33459, by rfl⟩) (B 66919 (by norm_num) ⟨33459, by rfl⟩ (by norm_num))
theorem R89229 : Reach 89229 := rs (se 3 (by rfl) ⟨16730, by rfl⟩) (B 33461 (by norm_num) ⟨16730, by rfl⟩ (by norm_num))
theorem R89233 : Reach 89233 := rs (se 2 (by rfl) ⟨33462, by rfl⟩) (B 66925 (by norm_num) ⟨33462, by rfl⟩ (by norm_num))
theorem R89237 : Reach 89237 := rs (se 6 (by rfl) ⟨2091, by rfl⟩) (B 4183 (by norm_num) ⟨2091, by rfl⟩ (by norm_num))
theorem R122005 : Reach 122005 := rs (se 6 (by rfl) ⟨2859, by rfl⟩) (B 5719 (by norm_num) ⟨2859, by rfl⟩ (by norm_num))
theorem R89241 : Reach 89241 := rs (se 2 (by rfl) ⟨33465, by rfl⟩) (B 66931 (by norm_num) ⟨33465, by rfl⟩ (by norm_num))
theorem R89245 : Reach 89245 := rs (se 3 (by rfl) ⟨16733, by rfl⟩) (B 33467 (by norm_num) ⟨16733, by rfl⟩ (by norm_num))
theorem R89249 : Reach 89249 := rs (se 2 (by rfl) ⟨33468, by rfl⟩) (B 66937 (by norm_num) ⟨33468, by rfl⟩ (by norm_num))
theorem R89253 : Reach 89253 := rs (se 4 (by rfl) ⟨8367, by rfl⟩) (B 16735 (by norm_num) ⟨8367, by rfl⟩ (by norm_num))
theorem R89257 : Reach 89257 := rs (se 2 (by rfl) ⟨33471, by rfl⟩) (B 66943 (by norm_num) ⟨33471, by rfl⟩ (by norm_num))
theorem R89261 : Reach 89261 := rs (se 3 (by rfl) ⟨16736, by rfl⟩) (B 33473 (by norm_num) ⟨16736, by rfl⟩ (by norm_num))
theorem R89265 : Reach 89265 := rs (se 2 (by rfl) ⟨33474, by rfl⟩) (B 66949 (by norm_num) ⟨33474, by rfl⟩ (by norm_num))
theorem R89269 : Reach 89269 := rs (se 5 (by rfl) ⟨4184, by rfl⟩) (B 8369 (by norm_num) ⟨4184, by rfl⟩ (by norm_num))
theorem R89273 : Reach 89273 := rs (se 2 (by rfl) ⟨33477, by rfl⟩) (B 66955 (by norm_num) ⟨33477, by rfl⟩ (by norm_num))
theorem R89277 : Reach 89277 := rs (se 3 (by rfl) ⟨16739, by rfl⟩) (B 33479 (by norm_num) ⟨16739, by rfl⟩ (by norm_num))
theorem R89281 : Reach 89281 := rs (se 2 (by rfl) ⟨33480, by rfl⟩) (B 66961 (by norm_num) ⟨33480, by rfl⟩ (by norm_num))
theorem R89285 : Reach 89285 := rs (se 4 (by rfl) ⟨8370, by rfl⟩) (B 16741 (by norm_num) ⟨8370, by rfl⟩ (by norm_num))
theorem R89289 : Reach 89289 := rs (se 2 (by rfl) ⟨33483, by rfl⟩) (B 66967 (by norm_num) ⟨33483, by rfl⟩ (by norm_num))
theorem R89293 : Reach 89293 := rs (se 3 (by rfl) ⟨16742, by rfl⟩) (B 33485 (by norm_num) ⟨16742, by rfl⟩ (by norm_num))
theorem R89297 : Reach 89297 := rs (se 2 (by rfl) ⟨33486, by rfl⟩) (B 66973 (by norm_num) ⟨33486, by rfl⟩ (by norm_num))
theorem R89301 : Reach 89301 := rs (se 7 (by rfl) ⟨1046, by rfl⟩) (B 2093 (by norm_num) ⟨1046, by rfl⟩ (by norm_num))
theorem R89305 : Reach 89305 := rs (se 2 (by rfl) ⟨33489, by rfl⟩) (B 66979 (by norm_num) ⟨33489, by rfl⟩ (by norm_num))
theorem R89309 : Reach 89309 := rs (se 3 (by rfl) ⟨16745, by rfl⟩) (B 33491 (by norm_num) ⟨16745, by rfl⟩ (by norm_num))
theorem R89313 : Reach 89313 := rs (se 2 (by rfl) ⟨33492, by rfl⟩) (B 66985 (by norm_num) ⟨33492, by rfl⟩ (by norm_num))
theorem R89317 : Reach 89317 := rs (se 4 (by rfl) ⟨8373, by rfl⟩) (B 16747 (by norm_num) ⟨8373, by rfl⟩ (by norm_num))
theorem R89321 : Reach 89321 := rs (se 2 (by rfl) ⟨33495, by rfl⟩) (B 66991 (by norm_num) ⟨33495, by rfl⟩ (by norm_num))
theorem R89325 : Reach 89325 := rs (se 3 (by rfl) ⟨16748, by rfl⟩) (B 33497 (by norm_num) ⟨16748, by rfl⟩ (by norm_num))
theorem R89329 : Reach 89329 := rs (se 2 (by rfl) ⟨33498, by rfl⟩) (B 66997 (by norm_num) ⟨33498, by rfl⟩ (by norm_num))
theorem R89333 : Reach 89333 := rs (se 5 (by rfl) ⟨4187, by rfl⟩) (B 8375 (by norm_num) ⟨4187, by rfl⟩ (by norm_num))
theorem R89337 : Reach 89337 := rs (se 2 (by rfl) ⟨33501, by rfl⟩) (B 67003 (by norm_num) ⟨33501, by rfl⟩ (by norm_num))
theorem R89341 : Reach 89341 := rs (se 3 (by rfl) ⟨16751, by rfl⟩) (B 33503 (by norm_num) ⟨16751, by rfl⟩ (by norm_num))
theorem R89345 : Reach 89345 := rs (se 2 (by rfl) ⟨33504, by rfl⟩) (B 67009 (by norm_num) ⟨33504, by rfl⟩ (by norm_num))
theorem R89349 : Reach 89349 := rs (se 4 (by rfl) ⟨8376, by rfl⟩) (B 16753 (by norm_num) ⟨8376, by rfl⟩ (by norm_num))
theorem R89353 : Reach 89353 := rs (se 2 (by rfl) ⟨33507, by rfl⟩) (B 67015 (by norm_num) ⟨33507, by rfl⟩ (by norm_num))
theorem R89357 : Reach 89357 := rs (se 3 (by rfl) ⟨16754, by rfl⟩) (B 33509 (by norm_num) ⟨16754, by rfl⟩ (by norm_num))
theorem R89361 : Reach 89361 := rs (se 2 (by rfl) ⟨33510, by rfl⟩) (B 67021 (by norm_num) ⟨33510, by rfl⟩ (by norm_num))
theorem R89365 : Reach 89365 := rs (se 6 (by rfl) ⟨2094, by rfl⟩) (B 4189 (by norm_num) ⟨2094, by rfl⟩ (by norm_num))
theorem R89369 : Reach 89369 := rs (se 2 (by rfl) ⟨33513, by rfl⟩) (B 67027 (by norm_num) ⟨33513, by rfl⟩ (by norm_num))
theorem R89373 : Reach 89373 := rs (se 3 (by rfl) ⟨16757, by rfl⟩) (B 33515 (by norm_num) ⟨16757, by rfl⟩ (by norm_num))
theorem R89377 : Reach 89377 := rs (se 2 (by rfl) ⟨33516, by rfl⟩) (B 67033 (by norm_num) ⟨33516, by rfl⟩ (by norm_num))
theorem R89381 : Reach 89381 := rs (se 4 (by rfl) ⟨8379, by rfl⟩) (B 16759 (by norm_num) ⟨8379, by rfl⟩ (by norm_num))
theorem R89385 : Reach 89385 := rs (se 2 (by rfl) ⟨33519, by rfl⟩) (B 67039 (by norm_num) ⟨33519, by rfl⟩ (by norm_num))
theorem R89389 : Reach 89389 := rs (se 3 (by rfl) ⟨16760, by rfl⟩) (B 33521 (by norm_num) ⟨16760, by rfl⟩ (by norm_num))
theorem R89393 : Reach 89393 := rs (se 2 (by rfl) ⟨33522, by rfl⟩) (B 67045 (by norm_num) ⟨33522, by rfl⟩ (by norm_num))
theorem R89397 : Reach 89397 := rs (se 5 (by rfl) ⟨4190, by rfl⟩) (B 8381 (by norm_num) ⟨4190, by rfl⟩ (by norm_num))
theorem R89401 : Reach 89401 := rs (se 2 (by rfl) ⟨33525, by rfl⟩) (B 67051 (by norm_num) ⟨33525, by rfl⟩ (by norm_num))
theorem R89405 : Reach 89405 := rs (se 3 (by rfl) ⟨16763, by rfl⟩) (B 33527 (by norm_num) ⟨16763, by rfl⟩ (by norm_num))
theorem R220477 : Reach 220477 := rs (se 3 (by rfl) ⟨41339, by rfl⟩) (B 82679 (by norm_num) ⟨41339, by rfl⟩ (by norm_num))
theorem R89409 : Reach 89409 := rs (se 2 (by rfl) ⟨33528, by rfl⟩) (B 67057 (by norm_num) ⟨33528, by rfl⟩ (by norm_num))
theorem R89413 : Reach 89413 := rs (se 4 (by rfl) ⟨8382, by rfl⟩) (B 16765 (by norm_num) ⟨8382, by rfl⟩ (by norm_num))
theorem R89417 : Reach 89417 := rs (se 2 (by rfl) ⟨33531, by rfl⟩) (B 67063 (by norm_num) ⟨33531, by rfl⟩ (by norm_num))
theorem R89421 : Reach 89421 := rs (se 3 (by rfl) ⟨16766, by rfl⟩) (B 33533 (by norm_num) ⟨16766, by rfl⟩ (by norm_num))
theorem R89425 : Reach 89425 := rs (se 2 (by rfl) ⟨33534, by rfl⟩) (B 67069 (by norm_num) ⟨33534, by rfl⟩ (by norm_num))
theorem R187733 : Reach 187733 := rs (se 11 (by rfl) ⟨137, by rfl⟩) (B 275 (by norm_num) ⟨137, by rfl⟩ (by norm_num))
theorem R89429 : Reach 89429 := rs (se 11 (by rfl) ⟨65, by rfl⟩) (B 131 (by norm_num) ⟨65, by rfl⟩ (by norm_num))
theorem R89433 : Reach 89433 := rs (se 2 (by rfl) ⟨33537, by rfl⟩) (B 67075 (by norm_num) ⟨33537, by rfl⟩ (by norm_num))
theorem R89437 : Reach 89437 := rs (se 3 (by rfl) ⟨16769, by rfl⟩) (B 33539 (by norm_num) ⟨16769, by rfl⟩ (by norm_num))
theorem R89441 : Reach 89441 := rs (se 2 (by rfl) ⟨33540, by rfl⟩) (B 67081 (by norm_num) ⟨33540, by rfl⟩ (by norm_num))
theorem R89445 : Reach 89445 := rs (se 4 (by rfl) ⟨8385, by rfl⟩) (B 16771 (by norm_num) ⟨8385, by rfl⟩ (by norm_num))
theorem R89449 : Reach 89449 := rs (se 2 (by rfl) ⟨33543, by rfl⟩) (B 67087 (by norm_num) ⟨33543, by rfl⟩ (by norm_num))
theorem R89453 : Reach 89453 := rs (se 3 (by rfl) ⟨16772, by rfl⟩) (B 33545 (by norm_num) ⟨16772, by rfl⟩ (by norm_num))
theorem R89457 : Reach 89457 := rs (se 2 (by rfl) ⟨33546, by rfl⟩) (B 67093 (by norm_num) ⟨33546, by rfl⟩ (by norm_num))
theorem R89461 : Reach 89461 := rs (se 5 (by rfl) ⟨4193, by rfl⟩) (B 8387 (by norm_num) ⟨4193, by rfl⟩ (by norm_num))
theorem R89465 : Reach 89465 := rs (se 2 (by rfl) ⟨33549, by rfl⟩) (B 67099 (by norm_num) ⟨33549, by rfl⟩ (by norm_num))
theorem R89469 : Reach 89469 := rs (se 3 (by rfl) ⟨16775, by rfl⟩) (B 33551 (by norm_num) ⟨16775, by rfl⟩ (by norm_num))
theorem R89473 : Reach 89473 := rs (se 2 (by rfl) ⟨33552, by rfl⟩) (B 67105 (by norm_num) ⟨33552, by rfl⟩ (by norm_num))
theorem R89477 : Reach 89477 := rs (se 4 (by rfl) ⟨8388, by rfl⟩) (B 16777 (by norm_num) ⟨8388, by rfl⟩ (by norm_num))
theorem R89481 : Reach 89481 := rs (se 2 (by rfl) ⟨33555, by rfl⟩) (B 67111 (by norm_num) ⟨33555, by rfl⟩ (by norm_num))
theorem R89485 : Reach 89485 := rs (se 3 (by rfl) ⟨16778, by rfl⟩) (B 33557 (by norm_num) ⟨16778, by rfl⟩ (by norm_num))
theorem R89489 : Reach 89489 := rs (se 2 (by rfl) ⟨33558, by rfl⟩) (B 67117 (by norm_num) ⟨33558, by rfl⟩ (by norm_num))
theorem R89493 : Reach 89493 := rs (se 6 (by rfl) ⟨2097, by rfl⟩) (B 4195 (by norm_num) ⟨2097, by rfl⟩ (by norm_num))
theorem R89497 : Reach 89497 := rs (se 2 (by rfl) ⟨33561, by rfl⟩) (B 67123 (by norm_num) ⟨33561, by rfl⟩ (by norm_num))
theorem R89501 : Reach 89501 := rs (se 3 (by rfl) ⟨16781, by rfl⟩) (B 33563 (by norm_num) ⟨16781, by rfl⟩ (by norm_num))
theorem R89505 : Reach 89505 := rs (se 2 (by rfl) ⟨33564, by rfl⟩) (B 67129 (by norm_num) ⟨33564, by rfl⟩ (by norm_num))
theorem R89509 : Reach 89509 := rs (se 4 (by rfl) ⟨8391, by rfl⟩) (B 16783 (by norm_num) ⟨8391, by rfl⟩ (by norm_num))
theorem R89513 : Reach 89513 := rs (se 2 (by rfl) ⟨33567, by rfl⟩) (B 67135 (by norm_num) ⟨33567, by rfl⟩ (by norm_num))
theorem R89517 : Reach 89517 := rs (se 3 (by rfl) ⟨16784, by rfl⟩) (B 33569 (by norm_num) ⟨16784, by rfl⟩ (by norm_num))
theorem R89521 : Reach 89521 := rs (se 2 (by rfl) ⟨33570, by rfl⟩) (B 67141 (by norm_num) ⟨33570, by rfl⟩ (by norm_num))
theorem R89525 : Reach 89525 := rs (se 5 (by rfl) ⟨4196, by rfl⟩) (B 8393 (by norm_num) ⟨4196, by rfl⟩ (by norm_num))
theorem R89529 : Reach 89529 := rs (se 2 (by rfl) ⟨33573, by rfl⟩) (B 67147 (by norm_num) ⟨33573, by rfl⟩ (by norm_num))
theorem R89533 : Reach 89533 := rs (se 3 (by rfl) ⟨16787, by rfl⟩) (B 33575 (by norm_num) ⟨16787, by rfl⟩ (by norm_num))
theorem R89537 : Reach 89537 := rs (se 2 (by rfl) ⟨33576, by rfl⟩) (B 67153 (by norm_num) ⟨33576, by rfl⟩ (by norm_num))
theorem R89541 : Reach 89541 := rs (se 4 (by rfl) ⟨8394, by rfl⟩) (B 16789 (by norm_num) ⟨8394, by rfl⟩ (by norm_num))
theorem R89545 : Reach 89545 := rs (se 2 (by rfl) ⟨33579, by rfl⟩) (B 67159 (by norm_num) ⟨33579, by rfl⟩ (by norm_num))
theorem R89549 : Reach 89549 := rs (se 3 (by rfl) ⟨16790, by rfl⟩) (B 33581 (by norm_num) ⟨16790, by rfl⟩ (by norm_num))
theorem R89553 : Reach 89553 := rs (se 2 (by rfl) ⟨33582, by rfl⟩) (B 67165 (by norm_num) ⟨33582, by rfl⟩ (by norm_num))
theorem R89557 : Reach 89557 := rs (se 7 (by rfl) ⟨1049, by rfl⟩) (B 2099 (by norm_num) ⟨1049, by rfl⟩ (by norm_num))
theorem R89561 : Reach 89561 := rs (se 2 (by rfl) ⟨33585, by rfl⟩) (B 67171 (by norm_num) ⟨33585, by rfl⟩ (by norm_num))
theorem R89565 : Reach 89565 := rs (se 3 (by rfl) ⟨16793, by rfl⟩) (B 33587 (by norm_num) ⟨16793, by rfl⟩ (by norm_num))
theorem R89569 : Reach 89569 := rs (se 2 (by rfl) ⟨33588, by rfl⟩) (B 67177 (by norm_num) ⟨33588, by rfl⟩ (by norm_num))
theorem R187877 : Reach 187877 := rs (se 4 (by rfl) ⟨17613, by rfl⟩) (B 35227 (by norm_num) ⟨17613, by rfl⟩ (by norm_num))
theorem R89573 : Reach 89573 := rs (se 4 (by rfl) ⟨8397, by rfl⟩) (B 16795 (by norm_num) ⟨8397, by rfl⟩ (by norm_num))
theorem R89577 : Reach 89577 := rs (se 2 (by rfl) ⟨33591, by rfl⟩) (B 67183 (by norm_num) ⟨33591, by rfl⟩ (by norm_num))
theorem R89581 : Reach 89581 := rs (se 3 (by rfl) ⟨16796, by rfl⟩) (B 33593 (by norm_num) ⟨16796, by rfl⟩ (by norm_num))
theorem R89585 : Reach 89585 := rs (se 2 (by rfl) ⟨33594, by rfl⟩) (B 67189 (by norm_num) ⟨33594, by rfl⟩ (by norm_num))
theorem R89589 : Reach 89589 := rs (se 5 (by rfl) ⟨4199, by rfl⟩) (B 8399 (by norm_num) ⟨4199, by rfl⟩ (by norm_num))
theorem R89593 : Reach 89593 := rs (se 2 (by rfl) ⟨33597, by rfl⟩) (B 67195 (by norm_num) ⟨33597, by rfl⟩ (by norm_num))
theorem R89597 : Reach 89597 := rs (se 3 (by rfl) ⟨16799, by rfl⟩) (B 33599 (by norm_num) ⟨16799, by rfl⟩ (by norm_num))
theorem R89601 : Reach 89601 := rs (se 2 (by rfl) ⟨33600, by rfl⟩) (B 67201 (by norm_num) ⟨33600, by rfl⟩ (by norm_num))
theorem R286213 : Reach 286213 := rs (se 4 (by rfl) ⟨26832, by rfl⟩) (B 53665 (by norm_num) ⟨26832, by rfl⟩ (by norm_num))
theorem R89605 : Reach 89605 := rs (se 4 (by rfl) ⟨8400, by rfl⟩) (B 16801 (by norm_num) ⟨8400, by rfl⟩ (by norm_num))
theorem R89609 : Reach 89609 := rs (se 2 (by rfl) ⟨33603, by rfl⟩) (B 67207 (by norm_num) ⟨33603, by rfl⟩ (by norm_num))
theorem R89613 : Reach 89613 := rs (se 3 (by rfl) ⟨16802, by rfl⟩) (B 33605 (by norm_num) ⟨16802, by rfl⟩ (by norm_num))
theorem R89617 : Reach 89617 := rs (se 2 (by rfl) ⟨33606, by rfl⟩) (B 67213 (by norm_num) ⟨33606, by rfl⟩ (by norm_num))
theorem R89621 : Reach 89621 := rs (se 6 (by rfl) ⟨2100, by rfl⟩) (B 4201 (by norm_num) ⟨2100, by rfl⟩ (by norm_num))
theorem R89625 : Reach 89625 := rs (se 2 (by rfl) ⟨33609, by rfl⟩) (B 67219 (by norm_num) ⟨33609, by rfl⟩ (by norm_num))
theorem R89629 : Reach 89629 := rs (se 3 (by rfl) ⟨16805, by rfl⟩) (B 33611 (by norm_num) ⟨16805, by rfl⟩ (by norm_num))
theorem R89633 : Reach 89633 := rs (se 2 (by rfl) ⟨33612, by rfl⟩) (B 67225 (by norm_num) ⟨33612, by rfl⟩ (by norm_num))
theorem R89637 : Reach 89637 := rs (se 4 (by rfl) ⟨8403, by rfl⟩) (B 16807 (by norm_num) ⟨8403, by rfl⟩ (by norm_num))
theorem R89641 : Reach 89641 := rs (se 2 (by rfl) ⟨33615, by rfl⟩) (B 67231 (by norm_num) ⟨33615, by rfl⟩ (by norm_num))
theorem R89645 : Reach 89645 := rs (se 3 (by rfl) ⟨16808, by rfl⟩) (B 33617 (by norm_num) ⟨16808, by rfl⟩ (by norm_num))
theorem R89649 : Reach 89649 := rs (se 2 (by rfl) ⟨33618, by rfl⟩) (B 67237 (by norm_num) ⟨33618, by rfl⟩ (by norm_num))
theorem R89653 : Reach 89653 := rs (se 5 (by rfl) ⟨4202, by rfl⟩) (B 8405 (by norm_num) ⟨4202, by rfl⟩ (by norm_num))
theorem R89657 : Reach 89657 := rs (se 2 (by rfl) ⟨33621, by rfl⟩) (B 67243 (by norm_num) ⟨33621, by rfl⟩ (by norm_num))
theorem R89661 : Reach 89661 := rs (se 3 (by rfl) ⟨16811, by rfl⟩) (B 33623 (by norm_num) ⟨16811, by rfl⟩ (by norm_num))
theorem R89665 : Reach 89665 := rs (se 2 (by rfl) ⟨33624, by rfl⟩) (B 67249 (by norm_num) ⟨33624, by rfl⟩ (by norm_num))
theorem R89669 : Reach 89669 := rs (se 4 (by rfl) ⟨8406, by rfl⟩) (B 16813 (by norm_num) ⟨8406, by rfl⟩ (by norm_num))
theorem R89673 : Reach 89673 := rs (se 2 (by rfl) ⟨33627, by rfl⟩) (B 67255 (by norm_num) ⟨33627, by rfl⟩ (by norm_num))
theorem R89677 : Reach 89677 := rs (se 3 (by rfl) ⟨16814, by rfl⟩) (B 33629 (by norm_num) ⟨16814, by rfl⟩ (by norm_num))
theorem R89681 : Reach 89681 := rs (se 2 (by rfl) ⟨33630, by rfl⟩) (B 67261 (by norm_num) ⟨33630, by rfl⟩ (by norm_num))
theorem R89685 : Reach 89685 := rs (se 8 (by rfl) ⟨525, by rfl⟩) (B 1051 (by norm_num) ⟨525, by rfl⟩ (by norm_num))
theorem R89689 : Reach 89689 := rs (se 2 (by rfl) ⟨33633, by rfl⟩) (B 67267 (by norm_num) ⟨33633, by rfl⟩ (by norm_num))
theorem R220765 : Reach 220765 := rs (se 3 (by rfl) ⟨41393, by rfl⟩) (B 82787 (by norm_num) ⟨41393, by rfl⟩ (by norm_num))
theorem R89693 : Reach 89693 := rs (se 3 (by rfl) ⟨16817, by rfl⟩) (B 33635 (by norm_num) ⟨16817, by rfl⟩ (by norm_num))
theorem R89697 : Reach 89697 := rs (se 2 (by rfl) ⟨33636, by rfl⟩) (B 67273 (by norm_num) ⟨33636, by rfl⟩ (by norm_num))
theorem R89701 : Reach 89701 := rs (se 4 (by rfl) ⟨8409, by rfl⟩) (B 16819 (by norm_num) ⟨8409, by rfl⟩ (by norm_num))
theorem R89705 : Reach 89705 := rs (se 2 (by rfl) ⟨33639, by rfl⟩) (B 67279 (by norm_num) ⟨33639, by rfl⟩ (by norm_num))
theorem R89709 : Reach 89709 := rs (se 3 (by rfl) ⟨16820, by rfl⟩) (B 33641 (by norm_num) ⟨16820, by rfl⟩ (by norm_num))
theorem R89713 : Reach 89713 := rs (se 2 (by rfl) ⟨33642, by rfl⟩) (B 67285 (by norm_num) ⟨33642, by rfl⟩ (by norm_num))
theorem R89717 : Reach 89717 := rs (se 5 (by rfl) ⟨4205, by rfl⟩) (B 8411 (by norm_num) ⟨4205, by rfl⟩ (by norm_num))
theorem R89721 : Reach 89721 := rs (se 2 (by rfl) ⟨33645, by rfl⟩) (B 67291 (by norm_num) ⟨33645, by rfl⟩ (by norm_num))
theorem R89725 : Reach 89725 := rs (se 3 (by rfl) ⟨16823, by rfl⟩) (B 33647 (by norm_num) ⟨16823, by rfl⟩ (by norm_num))
theorem R89729 : Reach 89729 := rs (se 2 (by rfl) ⟨33648, by rfl⟩) (B 67297 (by norm_num) ⟨33648, by rfl⟩ (by norm_num))
theorem R89733 : Reach 89733 := rs (se 4 (by rfl) ⟨8412, by rfl⟩) (B 16825 (by norm_num) ⟨8412, by rfl⟩ (by norm_num))
theorem R89737 : Reach 89737 := rs (se 2 (by rfl) ⟨33651, by rfl⟩) (B 67303 (by norm_num) ⟨33651, by rfl⟩ (by norm_num))
theorem R89741 : Reach 89741 := rs (se 3 (by rfl) ⟨16826, by rfl⟩) (B 33653 (by norm_num) ⟨16826, by rfl⟩ (by norm_num))
theorem R89745 : Reach 89745 := rs (se 2 (by rfl) ⟨33654, by rfl⟩) (B 67309 (by norm_num) ⟨33654, by rfl⟩ (by norm_num))
theorem R450197 : Reach 450197 := rs (se 6 (by rfl) ⟨10551, by rfl⟩) (B 21103 (by norm_num) ⟨10551, by rfl⟩ (by norm_num))
theorem R89749 : Reach 89749 := rs (se 6 (by rfl) ⟨2103, by rfl⟩) (B 4207 (by norm_num) ⟨2103, by rfl⟩ (by norm_num))
theorem R89753 : Reach 89753 := rs (se 2 (by rfl) ⟨33657, by rfl⟩) (B 67315 (by norm_num) ⟨33657, by rfl⟩ (by norm_num))
theorem R89757 : Reach 89757 := rs (se 3 (by rfl) ⟨16829, by rfl⟩) (B 33659 (by norm_num) ⟨16829, by rfl⟩ (by norm_num))
theorem R89761 : Reach 89761 := rs (se 2 (by rfl) ⟨33660, by rfl⟩) (B 67321 (by norm_num) ⟨33660, by rfl⟩ (by norm_num))
theorem R89765 : Reach 89765 := rs (se 4 (by rfl) ⟨8415, by rfl⟩) (B 16831 (by norm_num) ⟨8415, by rfl⟩ (by norm_num))
theorem R89769 : Reach 89769 := rs (se 2 (by rfl) ⟨33663, by rfl⟩) (B 67327 (by norm_num) ⟨33663, by rfl⟩ (by norm_num))
theorem R89773 : Reach 89773 := rs (se 3 (by rfl) ⟨16832, by rfl⟩) (B 33665 (by norm_num) ⟨16832, by rfl⟩ (by norm_num))
theorem R89777 : Reach 89777 := rs (se 2 (by rfl) ⟨33666, by rfl⟩) (B 67333 (by norm_num) ⟨33666, by rfl⟩ (by norm_num))
theorem R89781 : Reach 89781 := rs (se 5 (by rfl) ⟨4208, by rfl⟩) (B 8417 (by norm_num) ⟨4208, by rfl⟩ (by norm_num))
theorem R89785 : Reach 89785 := rs (se 2 (by rfl) ⟨33669, by rfl⟩) (B 67339 (by norm_num) ⟨33669, by rfl⟩ (by norm_num))
theorem R89789 : Reach 89789 := rs (se 3 (by rfl) ⟨16835, by rfl⟩) (B 33671 (by norm_num) ⟨16835, by rfl⟩ (by norm_num))
theorem R89793 : Reach 89793 := rs (se 2 (by rfl) ⟨33672, by rfl⟩) (B 67345 (by norm_num) ⟨33672, by rfl⟩ (by norm_num))
theorem R89797 : Reach 89797 := rs (se 4 (by rfl) ⟨8418, by rfl⟩) (B 16837 (by norm_num) ⟨8418, by rfl⟩ (by norm_num))
theorem R89801 : Reach 89801 := rs (se 2 (by rfl) ⟨33675, by rfl⟩) (B 67351 (by norm_num) ⟨33675, by rfl⟩ (by norm_num))
theorem R220877 : Reach 220877 := rs (se 3 (by rfl) ⟨41414, by rfl⟩) (B 82829 (by norm_num) ⟨41414, by rfl⟩ (by norm_num))
theorem R89805 : Reach 89805 := rs (se 3 (by rfl) ⟨16838, by rfl⟩) (B 33677 (by norm_num) ⟨16838, by rfl⟩ (by norm_num))
theorem R89809 : Reach 89809 := rs (se 2 (by rfl) ⟨33678, by rfl⟩) (B 67357 (by norm_num) ⟨33678, by rfl⟩ (by norm_num))
theorem R89813 : Reach 89813 := rs (se 7 (by rfl) ⟨1052, by rfl⟩) (B 2105 (by norm_num) ⟨1052, by rfl⟩ (by norm_num))
theorem R89817 : Reach 89817 := rs (se 2 (by rfl) ⟨33681, by rfl⟩) (B 67363 (by norm_num) ⟨33681, by rfl⟩ (by norm_num))
theorem R89821 : Reach 89821 := rs (se 3 (by rfl) ⟨16841, by rfl⟩) (B 33683 (by norm_num) ⟨16841, by rfl⟩ (by norm_num))
theorem R89825 : Reach 89825 := rs (se 2 (by rfl) ⟨33684, by rfl⟩) (B 67369 (by norm_num) ⟨33684, by rfl⟩ (by norm_num))
theorem R89829 : Reach 89829 := rs (se 4 (by rfl) ⟨8421, by rfl⟩) (B 16843 (by norm_num) ⟨8421, by rfl⟩ (by norm_num))
theorem R89833 : Reach 89833 := rs (se 2 (by rfl) ⟨33687, by rfl⟩) (B 67375 (by norm_num) ⟨33687, by rfl⟩ (by norm_num))
theorem R89837 : Reach 89837 := rs (se 3 (by rfl) ⟨16844, by rfl⟩) (B 33689 (by norm_num) ⟨16844, by rfl⟩ (by norm_num))
theorem R89841 : Reach 89841 := rs (se 2 (by rfl) ⟨33690, by rfl⟩) (B 67381 (by norm_num) ⟨33690, by rfl⟩ (by norm_num))
theorem R89845 : Reach 89845 := rs (se 5 (by rfl) ⟨4211, by rfl⟩) (B 8423 (by norm_num) ⟨4211, by rfl⟩ (by norm_num))
theorem R351989 : Reach 351989 := rs (se 5 (by rfl) ⟨16499, by rfl⟩) (B 32999 (by norm_num) ⟨16499, by rfl⟩ (by norm_num))
theorem R89849 : Reach 89849 := rs (se 2 (by rfl) ⟨33693, by rfl⟩) (B 67387 (by norm_num) ⟨33693, by rfl⟩ (by norm_num))
theorem R89853 : Reach 89853 := rs (se 3 (by rfl) ⟨16847, by rfl⟩) (B 33695 (by norm_num) ⟨16847, by rfl⟩ (by norm_num))
theorem R89857 : Reach 89857 := rs (se 2 (by rfl) ⟨33696, by rfl⟩) (B 67393 (by norm_num) ⟨33696, by rfl⟩ (by norm_num))
theorem R89861 : Reach 89861 := rs (se 4 (by rfl) ⟨8424, by rfl⟩) (B 16849 (by norm_num) ⟨8424, by rfl⟩ (by norm_num))
theorem R89865 : Reach 89865 := rs (se 2 (by rfl) ⟨33699, by rfl⟩) (B 67399 (by norm_num) ⟨33699, by rfl⟩ (by norm_num))
theorem R89869 : Reach 89869 := rs (se 3 (by rfl) ⟨16850, by rfl⟩) (B 33701 (by norm_num) ⟨16850, by rfl⟩ (by norm_num))
theorem R89873 : Reach 89873 := rs (se 2 (by rfl) ⟨33702, by rfl⟩) (B 67405 (by norm_num) ⟨33702, by rfl⟩ (by norm_num))
theorem R89877 : Reach 89877 := rs (se 6 (by rfl) ⟨2106, by rfl⟩) (B 4213 (by norm_num) ⟨2106, by rfl⟩ (by norm_num))
theorem R89881 : Reach 89881 := rs (se 2 (by rfl) ⟨33705, by rfl⟩) (B 67411 (by norm_num) ⟨33705, by rfl⟩ (by norm_num))
theorem R89885 : Reach 89885 := rs (se 3 (by rfl) ⟨16853, by rfl⟩) (B 33707 (by norm_num) ⟨16853, by rfl⟩ (by norm_num))
theorem R89889 : Reach 89889 := rs (se 2 (by rfl) ⟨33708, by rfl⟩) (B 67417 (by norm_num) ⟨33708, by rfl⟩ (by norm_num))
theorem R89893 : Reach 89893 := rs (se 4 (by rfl) ⟨8427, by rfl⟩) (B 16855 (by norm_num) ⟨8427, by rfl⟩ (by norm_num))
theorem R89897 : Reach 89897 := rs (se 2 (by rfl) ⟨33711, by rfl⟩) (B 67423 (by norm_num) ⟨33711, by rfl⟩ (by norm_num))
theorem R89901 : Reach 89901 := rs (se 3 (by rfl) ⟨16856, by rfl⟩) (B 33713 (by norm_num) ⟨16856, by rfl⟩ (by norm_num))
theorem R89905 : Reach 89905 := rs (se 2 (by rfl) ⟨33714, by rfl⟩) (B 67429 (by norm_num) ⟨33714, by rfl⟩ (by norm_num))
theorem R89909 : Reach 89909 := rs (se 5 (by rfl) ⟨4214, by rfl⟩) (B 8429 (by norm_num) ⟨4214, by rfl⟩ (by norm_num))
theorem R89913 : Reach 89913 := rs (se 2 (by rfl) ⟨33717, by rfl⟩) (B 67435 (by norm_num) ⟨33717, by rfl⟩ (by norm_num))
theorem R89917 : Reach 89917 := rs (se 3 (by rfl) ⟨16859, by rfl⟩) (B 33719 (by norm_num) ⟨16859, by rfl⟩ (by norm_num))
theorem R89921 : Reach 89921 := rs (se 2 (by rfl) ⟨33720, by rfl⟩) (B 67441 (by norm_num) ⟨33720, by rfl⟩ (by norm_num))
theorem R89925 : Reach 89925 := rs (se 4 (by rfl) ⟨8430, by rfl⟩) (B 16861 (by norm_num) ⟨8430, by rfl⟩ (by norm_num))
theorem R89929 : Reach 89929 := rs (se 2 (by rfl) ⟨33723, by rfl⟩) (B 67447 (by norm_num) ⟨33723, by rfl⟩ (by norm_num))
theorem R188237 : Reach 188237 := rs (se 3 (by rfl) ⟨35294, by rfl⟩) (B 70589 (by norm_num) ⟨35294, by rfl⟩ (by norm_num))
theorem R89933 : Reach 89933 := rs (se 3 (by rfl) ⟨16862, by rfl⟩) (B 33725 (by norm_num) ⟨16862, by rfl⟩ (by norm_num))
theorem R89937 : Reach 89937 := rs (se 2 (by rfl) ⟨33726, by rfl⟩) (B 67453 (by norm_num) ⟨33726, by rfl⟩ (by norm_num))
theorem R89941 : Reach 89941 := rs (se 9 (by rfl) ⟨263, by rfl⟩) (B 527 (by norm_num) ⟨263, by rfl⟩ (by norm_num))
theorem R89945 : Reach 89945 := rs (se 2 (by rfl) ⟨33729, by rfl⟩) (B 67459 (by norm_num) ⟨33729, by rfl⟩ (by norm_num))
theorem R89949 : Reach 89949 := rs (se 3 (by rfl) ⟨16865, by rfl⟩) (B 33731 (by norm_num) ⟨16865, by rfl⟩ (by norm_num))
theorem R89953 : Reach 89953 := rs (se 2 (by rfl) ⟨33732, by rfl⟩) (B 67465 (by norm_num) ⟨33732, by rfl⟩ (by norm_num))
theorem R89957 : Reach 89957 := rs (se 4 (by rfl) ⟨8433, by rfl⟩) (B 16867 (by norm_num) ⟨8433, by rfl⟩ (by norm_num))
theorem R89961 : Reach 89961 := rs (se 2 (by rfl) ⟨33735, by rfl⟩) (B 67471 (by norm_num) ⟨33735, by rfl⟩ (by norm_num))
theorem R89965 : Reach 89965 := rs (se 3 (by rfl) ⟨16868, by rfl⟩) (B 33737 (by norm_num) ⟨16868, by rfl⟩ (by norm_num))
theorem R89969 : Reach 89969 := rs (se 2 (by rfl) ⟨33738, by rfl⟩) (B 67477 (by norm_num) ⟨33738, by rfl⟩ (by norm_num))
theorem R89973 : Reach 89973 := rs (se 5 (by rfl) ⟨4217, by rfl⟩) (B 8435 (by norm_num) ⟨4217, by rfl⟩ (by norm_num))
theorem R89977 : Reach 89977 := rs (se 2 (by rfl) ⟨33741, by rfl⟩) (B 67483 (by norm_num) ⟨33741, by rfl⟩ (by norm_num))
theorem R89981 : Reach 89981 := rs (se 3 (by rfl) ⟨16871, by rfl⟩) (B 33743 (by norm_num) ⟨16871, by rfl⟩ (by norm_num))
theorem R89985 : Reach 89985 := rs (se 2 (by rfl) ⟨33744, by rfl⟩) (B 67489 (by norm_num) ⟨33744, by rfl⟩ (by norm_num))
theorem R253829 : Reach 253829 := rs (se 4 (by rfl) ⟨23796, by rfl⟩) (B 47593 (by norm_num) ⟨23796, by rfl⟩ (by norm_num))
theorem R89989 : Reach 89989 := rs (se 4 (by rfl) ⟨8436, by rfl⟩) (B 16873 (by norm_num) ⟨8436, by rfl⟩ (by norm_num))
theorem R89993 : Reach 89993 := rs (se 2 (by rfl) ⟨33747, by rfl⟩) (B 67495 (by norm_num) ⟨33747, by rfl⟩ (by norm_num))
theorem R221069 : Reach 221069 := rs (se 3 (by rfl) ⟨41450, by rfl⟩) (B 82901 (by norm_num) ⟨41450, by rfl⟩ (by norm_num))
theorem R89997 : Reach 89997 := rs (se 3 (by rfl) ⟨16874, by rfl⟩) (B 33749 (by norm_num) ⟨16874, by rfl⟩ (by norm_num))
theorem R90001 : Reach 90001 := rs (se 2 (by rfl) ⟨33750, by rfl⟩) (B 67501 (by norm_num) ⟨33750, by rfl⟩ (by norm_num))
theorem R90005 : Reach 90005 := rs (se 6 (by rfl) ⟨2109, by rfl⟩) (B 4219 (by norm_num) ⟨2109, by rfl⟩ (by norm_num))
theorem R90009 : Reach 90009 := rs (se 2 (by rfl) ⟨33753, by rfl⟩) (B 67507 (by norm_num) ⟨33753, by rfl⟩ (by norm_num))
theorem R90013 : Reach 90013 := rs (se 3 (by rfl) ⟨16877, by rfl⟩) (B 33755 (by norm_num) ⟨16877, by rfl⟩ (by norm_num))
theorem R90017 : Reach 90017 := rs (se 2 (by rfl) ⟨33756, by rfl⟩) (B 67513 (by norm_num) ⟨33756, by rfl⟩ (by norm_num))
theorem R90021 : Reach 90021 := rs (se 4 (by rfl) ⟨8439, by rfl⟩) (B 16879 (by norm_num) ⟨8439, by rfl⟩ (by norm_num))
theorem R90025 : Reach 90025 := rs (se 2 (by rfl) ⟨33759, by rfl⟩) (B 67519 (by norm_num) ⟨33759, by rfl⟩ (by norm_num))
theorem R90029 : Reach 90029 := rs (se 3 (by rfl) ⟨16880, by rfl⟩) (B 33761 (by norm_num) ⟨16880, by rfl⟩ (by norm_num))
theorem R90033 : Reach 90033 := rs (se 2 (by rfl) ⟨33762, by rfl⟩) (B 67525 (by norm_num) ⟨33762, by rfl⟩ (by norm_num))
theorem R90037 : Reach 90037 := rs (se 5 (by rfl) ⟨4220, by rfl⟩) (B 8441 (by norm_num) ⟨4220, by rfl⟩ (by norm_num))
theorem R90041 : Reach 90041 := rs (se 2 (by rfl) ⟨33765, by rfl⟩) (B 67531 (by norm_num) ⟨33765, by rfl⟩ (by norm_num))
theorem R90045 : Reach 90045 := rs (se 3 (by rfl) ⟨16883, by rfl⟩) (B 33767 (by norm_num) ⟨16883, by rfl⟩ (by norm_num))
theorem R90049 : Reach 90049 := rs (se 2 (by rfl) ⟨33768, by rfl⟩) (B 67537 (by norm_num) ⟨33768, by rfl⟩ (by norm_num))
theorem R90053 : Reach 90053 := rs (se 4 (by rfl) ⟨8442, by rfl⟩) (B 16885 (by norm_num) ⟨8442, by rfl⟩ (by norm_num))
theorem R90057 : Reach 90057 := rs (se 2 (by rfl) ⟨33771, by rfl⟩) (B 67543 (by norm_num) ⟨33771, by rfl⟩ (by norm_num))
theorem R90061 : Reach 90061 := rs (se 3 (by rfl) ⟨16886, by rfl⟩) (B 33773 (by norm_num) ⟨16886, by rfl⟩ (by norm_num))
theorem R90065 : Reach 90065 := rs (se 2 (by rfl) ⟨33774, by rfl⟩) (B 67549 (by norm_num) ⟨33774, by rfl⟩ (by norm_num))
theorem R90069 : Reach 90069 := rs (se 7 (by rfl) ⟨1055, by rfl⟩) (B 2111 (by norm_num) ⟨1055, by rfl⟩ (by norm_num))
theorem R90073 : Reach 90073 := rs (se 2 (by rfl) ⟨33777, by rfl⟩) (B 67555 (by norm_num) ⟨33777, by rfl⟩ (by norm_num))
theorem R90077 : Reach 90077 := rs (se 3 (by rfl) ⟨16889, by rfl⟩) (B 33779 (by norm_num) ⟨16889, by rfl⟩ (by norm_num))
theorem R90081 : Reach 90081 := rs (se 2 (by rfl) ⟨33780, by rfl⟩) (B 67561 (by norm_num) ⟨33780, by rfl⟩ (by norm_num))
theorem R90085 : Reach 90085 := rs (se 4 (by rfl) ⟨8445, by rfl⟩) (B 16891 (by norm_num) ⟨8445, by rfl⟩ (by norm_num))
theorem R90089 : Reach 90089 := rs (se 2 (by rfl) ⟨33783, by rfl⟩) (B 67567 (by norm_num) ⟨33783, by rfl⟩ (by norm_num))
theorem R90093 : Reach 90093 := rs (se 3 (by rfl) ⟨16892, by rfl⟩) (B 33785 (by norm_num) ⟨16892, by rfl⟩ (by norm_num))
theorem R90097 : Reach 90097 := rs (se 2 (by rfl) ⟨33786, by rfl⟩) (B 67573 (by norm_num) ⟨33786, by rfl⟩ (by norm_num))
theorem R90101 : Reach 90101 := rs (se 5 (by rfl) ⟨4223, by rfl⟩) (B 8447 (by norm_num) ⟨4223, by rfl⟩ (by norm_num))
theorem R90105 : Reach 90105 := rs (se 2 (by rfl) ⟨33789, by rfl⟩) (B 67579 (by norm_num) ⟨33789, by rfl⟩ (by norm_num))
theorem R90109 : Reach 90109 := rs (se 3 (by rfl) ⟨16895, by rfl⟩) (B 33791 (by norm_num) ⟨16895, by rfl⟩ (by norm_num))
theorem R90113 : Reach 90113 := rs (se 2 (by rfl) ⟨33792, by rfl⟩) (B 67585 (by norm_num) ⟨33792, by rfl⟩ (by norm_num))
theorem R90117 : Reach 90117 := rs (se 4 (by rfl) ⟨8448, by rfl⟩) (B 16897 (by norm_num) ⟨8448, by rfl⟩ (by norm_num))
theorem R90121 : Reach 90121 := rs (se 2 (by rfl) ⟨33795, by rfl⟩) (B 67591 (by norm_num) ⟨33795, by rfl⟩ (by norm_num))
theorem R90125 : Reach 90125 := rs (se 3 (by rfl) ⟨16898, by rfl⟩) (B 33797 (by norm_num) ⟨16898, by rfl⟩ (by norm_num))
theorem R90129 : Reach 90129 := rs (se 2 (by rfl) ⟨33798, by rfl⟩) (B 67597 (by norm_num) ⟨33798, by rfl⟩ (by norm_num))
theorem R90133 : Reach 90133 := rs (se 6 (by rfl) ⟨2112, by rfl⟩) (B 4225 (by norm_num) ⟨2112, by rfl⟩ (by norm_num))
theorem R90137 : Reach 90137 := rs (se 2 (by rfl) ⟨33801, by rfl⟩) (B 67603 (by norm_num) ⟨33801, by rfl⟩ (by norm_num))
theorem R90141 : Reach 90141 := rs (se 3 (by rfl) ⟨16901, by rfl⟩) (B 33803 (by norm_num) ⟨16901, by rfl⟩ (by norm_num))
theorem R90145 : Reach 90145 := rs (se 2 (by rfl) ⟨33804, by rfl⟩) (B 67609 (by norm_num) ⟨33804, by rfl⟩ (by norm_num))
theorem R90149 : Reach 90149 := rs (se 4 (by rfl) ⟨8451, by rfl⟩) (B 16903 (by norm_num) ⟨8451, by rfl⟩ (by norm_num))
theorem R90153 : Reach 90153 := rs (se 2 (by rfl) ⟨33807, by rfl⟩) (B 67615 (by norm_num) ⟨33807, by rfl⟩ (by norm_num))
theorem R90157 : Reach 90157 := rs (se 3 (by rfl) ⟨16904, by rfl⟩) (B 33809 (by norm_num) ⟨16904, by rfl⟩ (by norm_num))
theorem R90161 : Reach 90161 := rs (se 2 (by rfl) ⟨33810, by rfl⟩) (B 67621 (by norm_num) ⟨33810, by rfl⟩ (by norm_num))
theorem R90165 : Reach 90165 := rs (se 5 (by rfl) ⟨4226, by rfl⟩) (B 8453 (by norm_num) ⟨4226, by rfl⟩ (by norm_num))
theorem R90169 : Reach 90169 := rs (se 2 (by rfl) ⟨33813, by rfl⟩) (B 67627 (by norm_num) ⟨33813, by rfl⟩ (by norm_num))
theorem R90173 : Reach 90173 := rs (se 3 (by rfl) ⟨16907, by rfl⟩) (B 33815 (by norm_num) ⟨16907, by rfl⟩ (by norm_num))
theorem R90177 : Reach 90177 := rs (se 2 (by rfl) ⟨33816, by rfl⟩) (B 67633 (by norm_num) ⟨33816, by rfl⟩ (by norm_num))
theorem R90181 : Reach 90181 := rs (se 4 (by rfl) ⟨8454, by rfl⟩) (B 16909 (by norm_num) ⟨8454, by rfl⟩ (by norm_num))
theorem R90185 : Reach 90185 := rs (se 2 (by rfl) ⟨33819, by rfl⟩) (B 67639 (by norm_num) ⟨33819, by rfl⟩ (by norm_num))
theorem R90189 : Reach 90189 := rs (se 3 (by rfl) ⟨16910, by rfl⟩) (B 33821 (by norm_num) ⟨16910, by rfl⟩ (by norm_num))
theorem R90193 : Reach 90193 := rs (se 2 (by rfl) ⟨33822, by rfl⟩) (B 67645 (by norm_num) ⟨33822, by rfl⟩ (by norm_num))
theorem R286805 : Reach 286805 := rs (se 8 (by rfl) ⟨1680, by rfl⟩) (B 3361 (by norm_num) ⟨1680, by rfl⟩ (by norm_num))
theorem R90197 : Reach 90197 := rs (se 8 (by rfl) ⟨528, by rfl⟩) (B 1057 (by norm_num) ⟨528, by rfl⟩ (by norm_num))
theorem R90201 : Reach 90201 := rs (se 2 (by rfl) ⟨33825, by rfl⟩) (B 67651 (by norm_num) ⟨33825, by rfl⟩ (by norm_num))
theorem R90205 : Reach 90205 := rs (se 3 (by rfl) ⟨16913, by rfl⟩) (B 33827 (by norm_num) ⟨16913, by rfl⟩ (by norm_num))
theorem R90209 : Reach 90209 := rs (se 2 (by rfl) ⟨33828, by rfl⟩) (B 67657 (by norm_num) ⟨33828, by rfl⟩ (by norm_num))
theorem R90213 : Reach 90213 := rs (se 4 (by rfl) ⟨8457, by rfl⟩) (B 16915 (by norm_num) ⟨8457, by rfl⟩ (by norm_num))
theorem R90217 : Reach 90217 := rs (se 2 (by rfl) ⟨33831, by rfl⟩) (B 67663 (by norm_num) ⟨33831, by rfl⟩ (by norm_num))
theorem R90221 : Reach 90221 := rs (se 3 (by rfl) ⟨16916, by rfl⟩) (B 33833 (by norm_num) ⟨16916, by rfl⟩ (by norm_num))
theorem R90225 : Reach 90225 := rs (se 2 (by rfl) ⟨33834, by rfl⟩) (B 67669 (by norm_num) ⟨33834, by rfl⟩ (by norm_num))
theorem R90229 : Reach 90229 := rs (se 5 (by rfl) ⟨4229, by rfl⟩) (B 8459 (by norm_num) ⟨4229, by rfl⟩ (by norm_num))
theorem R90233 : Reach 90233 := rs (se 2 (by rfl) ⟨33837, by rfl⟩) (B 67675 (by norm_num) ⟨33837, by rfl⟩ (by norm_num))
theorem R90237 : Reach 90237 := rs (se 3 (by rfl) ⟨16919, by rfl⟩) (B 33839 (by norm_num) ⟨16919, by rfl⟩ (by norm_num))
theorem R90241 : Reach 90241 := rs (se 2 (by rfl) ⟨33840, by rfl⟩) (B 67681 (by norm_num) ⟨33840, by rfl⟩ (by norm_num))
theorem R90245 : Reach 90245 := rs (se 4 (by rfl) ⟨8460, by rfl⟩) (B 16921 (by norm_num) ⟨8460, by rfl⟩ (by norm_num))
theorem R90249 : Reach 90249 := rs (se 2 (by rfl) ⟨33843, by rfl⟩) (B 67687 (by norm_num) ⟨33843, by rfl⟩ (by norm_num))
theorem R90253 : Reach 90253 := rs (se 3 (by rfl) ⟨16922, by rfl⟩) (B 33845 (by norm_num) ⟨16922, by rfl⟩ (by norm_num))
theorem R90257 : Reach 90257 := rs (se 2 (by rfl) ⟨33846, by rfl⟩) (B 67693 (by norm_num) ⟨33846, by rfl⟩ (by norm_num))
theorem R90261 : Reach 90261 := rs (se 6 (by rfl) ⟨2115, by rfl⟩) (B 4231 (by norm_num) ⟨2115, by rfl⟩ (by norm_num))
theorem R90265 : Reach 90265 := rs (se 2 (by rfl) ⟨33849, by rfl⟩) (B 67699 (by norm_num) ⟨33849, by rfl⟩ (by norm_num))
theorem R90269 : Reach 90269 := rs (se 3 (by rfl) ⟨16925, by rfl⟩) (B 33851 (by norm_num) ⟨16925, by rfl⟩ (by norm_num))
theorem R90273 : Reach 90273 := rs (se 2 (by rfl) ⟨33852, by rfl⟩) (B 67705 (by norm_num) ⟨33852, by rfl⟩ (by norm_num))
theorem R90277 : Reach 90277 := rs (se 4 (by rfl) ⟨8463, by rfl⟩) (B 16927 (by norm_num) ⟨8463, by rfl⟩ (by norm_num))
theorem R90281 : Reach 90281 := rs (se 2 (by rfl) ⟨33855, by rfl⟩) (B 67711 (by norm_num) ⟨33855, by rfl⟩ (by norm_num))
theorem R90285 : Reach 90285 := rs (se 3 (by rfl) ⟨16928, by rfl⟩) (B 33857 (by norm_num) ⟨16928, by rfl⟩ (by norm_num))
theorem R90289 : Reach 90289 := rs (se 2 (by rfl) ⟨33858, by rfl⟩) (B 67717 (by norm_num) ⟨33858, by rfl⟩ (by norm_num))
theorem R90293 : Reach 90293 := rs (se 5 (by rfl) ⟨4232, by rfl⟩) (B 8465 (by norm_num) ⟨4232, by rfl⟩ (by norm_num))
theorem R90297 : Reach 90297 := rs (se 2 (by rfl) ⟨33861, by rfl⟩) (B 67723 (by norm_num) ⟨33861, by rfl⟩ (by norm_num))
theorem R90301 : Reach 90301 := rs (se 3 (by rfl) ⟨16931, by rfl⟩) (B 33863 (by norm_num) ⟨16931, by rfl⟩ (by norm_num))
theorem R90305 : Reach 90305 := rs (se 2 (by rfl) ⟨33864, by rfl⟩) (B 67729 (by norm_num) ⟨33864, by rfl⟩ (by norm_num))
theorem R90309 : Reach 90309 := rs (se 4 (by rfl) ⟨8466, by rfl⟩) (B 16933 (by norm_num) ⟨8466, by rfl⟩ (by norm_num))
theorem R90313 : Reach 90313 := rs (se 2 (by rfl) ⟨33867, by rfl⟩) (B 67735 (by norm_num) ⟨33867, by rfl⟩ (by norm_num))
theorem R90317 : Reach 90317 := rs (se 3 (by rfl) ⟨16934, by rfl⟩) (B 33869 (by norm_num) ⟨16934, by rfl⟩ (by norm_num))
theorem R90321 : Reach 90321 := rs (se 2 (by rfl) ⟨33870, by rfl⟩) (B 67741 (by norm_num) ⟨33870, by rfl⟩ (by norm_num))
theorem R90325 : Reach 90325 := rs (se 7 (by rfl) ⟨1058, by rfl⟩) (B 2117 (by norm_num) ⟨1058, by rfl⟩ (by norm_num))
theorem R90329 : Reach 90329 := rs (se 2 (by rfl) ⟨33873, by rfl⟩) (B 67747 (by norm_num) ⟨33873, by rfl⟩ (by norm_num))
theorem R90333 : Reach 90333 := rs (se 3 (by rfl) ⟨16937, by rfl⟩) (B 33875 (by norm_num) ⟨16937, by rfl⟩ (by norm_num))
theorem R90337 : Reach 90337 := rs (se 2 (by rfl) ⟨33876, by rfl⟩) (B 67753 (by norm_num) ⟨33876, by rfl⟩ (by norm_num))
theorem R221413 : Reach 221413 := rs (se 4 (by rfl) ⟨20757, by rfl⟩) (B 41515 (by norm_num) ⟨20757, by rfl⟩ (by norm_num))
theorem R90341 : Reach 90341 := rs (se 4 (by rfl) ⟨8469, by rfl⟩) (B 16939 (by norm_num) ⟨8469, by rfl⟩ (by norm_num))
theorem R90345 : Reach 90345 := rs (se 2 (by rfl) ⟨33879, by rfl⟩) (B 67759 (by norm_num) ⟨33879, by rfl⟩ (by norm_num))
theorem R90349 : Reach 90349 := rs (se 3 (by rfl) ⟨16940, by rfl⟩) (B 33881 (by norm_num) ⟨16940, by rfl⟩ (by norm_num))
theorem R90353 : Reach 90353 := rs (se 2 (by rfl) ⟨33882, by rfl⟩) (B 67765 (by norm_num) ⟨33882, by rfl⟩ (by norm_num))
theorem R90357 : Reach 90357 := rs (se 5 (by rfl) ⟨4235, by rfl⟩) (B 8471 (by norm_num) ⟨4235, by rfl⟩ (by norm_num))
theorem R90361 : Reach 90361 := rs (se 2 (by rfl) ⟨33885, by rfl⟩) (B 67771 (by norm_num) ⟨33885, by rfl⟩ (by norm_num))
theorem R90365 : Reach 90365 := rs (se 3 (by rfl) ⟨16943, by rfl⟩) (B 33887 (by norm_num) ⟨16943, by rfl⟩ (by norm_num))
theorem R90369 : Reach 90369 := rs (se 2 (by rfl) ⟨33888, by rfl⟩) (B 67777 (by norm_num) ⟨33888, by rfl⟩ (by norm_num))
theorem R90373 : Reach 90373 := rs (se 4 (by rfl) ⟨8472, by rfl⟩) (B 16945 (by norm_num) ⟨8472, by rfl⟩ (by norm_num))
theorem R90377 : Reach 90377 := rs (se 2 (by rfl) ⟨33891, by rfl⟩) (B 67783 (by norm_num) ⟨33891, by rfl⟩ (by norm_num))
theorem R90381 : Reach 90381 := rs (se 3 (by rfl) ⟨16946, by rfl⟩) (B 33893 (by norm_num) ⟨16946, by rfl⟩ (by norm_num))
theorem R90385 : Reach 90385 := rs (se 2 (by rfl) ⟨33894, by rfl⟩) (B 67789 (by norm_num) ⟨33894, by rfl⟩ (by norm_num))
theorem R90389 : Reach 90389 := rs (se 6 (by rfl) ⟨2118, by rfl⟩) (B 4237 (by norm_num) ⟨2118, by rfl⟩ (by norm_num))
theorem R90393 : Reach 90393 := rs (se 2 (by rfl) ⟨33897, by rfl⟩) (B 67795 (by norm_num) ⟨33897, by rfl⟩ (by norm_num))
theorem R90397 : Reach 90397 := rs (se 3 (by rfl) ⟨16949, by rfl⟩) (B 33899 (by norm_num) ⟨16949, by rfl⟩ (by norm_num))
theorem R90401 : Reach 90401 := rs (se 2 (by rfl) ⟨33900, by rfl⟩) (B 67801 (by norm_num) ⟨33900, by rfl⟩ (by norm_num))
theorem R90405 : Reach 90405 := rs (se 4 (by rfl) ⟨8475, by rfl⟩) (B 16951 (by norm_num) ⟨8475, by rfl⟩ (by norm_num))
theorem R90409 : Reach 90409 := rs (se 2 (by rfl) ⟨33903, by rfl⟩) (B 67807 (by norm_num) ⟨33903, by rfl⟩ (by norm_num))
theorem R90413 : Reach 90413 := rs (se 3 (by rfl) ⟨16952, by rfl⟩) (B 33905 (by norm_num) ⟨16952, by rfl⟩ (by norm_num))
theorem R90417 : Reach 90417 := rs (se 2 (by rfl) ⟨33906, by rfl⟩) (B 67813 (by norm_num) ⟨33906, by rfl⟩ (by norm_num))
theorem R90421 : Reach 90421 := rs (se 5 (by rfl) ⟨4238, by rfl⟩) (B 8477 (by norm_num) ⟨4238, by rfl⟩ (by norm_num))
theorem R90425 : Reach 90425 := rs (se 2 (by rfl) ⟨33909, by rfl⟩) (B 67819 (by norm_num) ⟨33909, by rfl⟩ (by norm_num))
theorem R90429 : Reach 90429 := rs (se 3 (by rfl) ⟨16955, by rfl⟩) (B 33911 (by norm_num) ⟨16955, by rfl⟩ (by norm_num))
theorem R90433 : Reach 90433 := rs (se 2 (by rfl) ⟨33912, by rfl⟩) (B 67825 (by norm_num) ⟨33912, by rfl⟩ (by norm_num))
theorem R90437 : Reach 90437 := rs (se 4 (by rfl) ⟨8478, by rfl⟩) (B 16957 (by norm_num) ⟨8478, by rfl⟩ (by norm_num))
theorem R90441 : Reach 90441 := rs (se 2 (by rfl) ⟨33915, by rfl⟩) (B 67831 (by norm_num) ⟨33915, by rfl⟩ (by norm_num))
theorem R90445 : Reach 90445 := rs (se 3 (by rfl) ⟨16958, by rfl⟩) (B 33917 (by norm_num) ⟨16958, by rfl⟩ (by norm_num))
theorem R90449 : Reach 90449 := rs (se 2 (by rfl) ⟨33918, by rfl⟩) (B 67837 (by norm_num) ⟨33918, by rfl⟩ (by norm_num))
theorem R221525 : Reach 221525 := rs (se 10 (by rfl) ⟨324, by rfl⟩) (B 649 (by norm_num) ⟨324, by rfl⟩ (by norm_num))
theorem R90453 : Reach 90453 := rs (se 10 (by rfl) ⟨132, by rfl⟩) (B 265 (by norm_num) ⟨132, by rfl⟩ (by norm_num))
theorem R90457 : Reach 90457 := rs (se 2 (by rfl) ⟨33921, by rfl⟩) (B 67843 (by norm_num) ⟨33921, by rfl⟩ (by norm_num))
theorem R90461 : Reach 90461 := rs (se 3 (by rfl) ⟨16961, by rfl⟩) (B 33923 (by norm_num) ⟨16961, by rfl⟩ (by norm_num))
theorem R90465 : Reach 90465 := rs (se 2 (by rfl) ⟨33924, by rfl⟩) (B 67849 (by norm_num) ⟨33924, by rfl⟩ (by norm_num))
theorem R90469 : Reach 90469 := rs (se 4 (by rfl) ⟨8481, by rfl⟩) (B 16963 (by norm_num) ⟨8481, by rfl⟩ (by norm_num))
theorem R90473 : Reach 90473 := rs (se 2 (by rfl) ⟨33927, by rfl⟩) (B 67855 (by norm_num) ⟨33927, by rfl⟩ (by norm_num))
theorem R90477 : Reach 90477 := rs (se 3 (by rfl) ⟨16964, by rfl⟩) (B 33929 (by norm_num) ⟨16964, by rfl⟩ (by norm_num))
theorem R90481 : Reach 90481 := rs (se 2 (by rfl) ⟨33930, by rfl⟩) (B 67861 (by norm_num) ⟨33930, by rfl⟩ (by norm_num))
theorem R90485 : Reach 90485 := rs (se 5 (by rfl) ⟨4241, by rfl⟩) (B 8483 (by norm_num) ⟨4241, by rfl⟩ (by norm_num))
theorem R90489 : Reach 90489 := rs (se 2 (by rfl) ⟨33933, by rfl⟩) (B 67867 (by norm_num) ⟨33933, by rfl⟩ (by norm_num))
theorem R90493 : Reach 90493 := rs (se 3 (by rfl) ⟨16967, by rfl⟩) (B 33935 (by norm_num) ⟨16967, by rfl⟩ (by norm_num))
theorem R90497 : Reach 90497 := rs (se 2 (by rfl) ⟨33936, by rfl⟩) (B 67873 (by norm_num) ⟨33936, by rfl⟩ (by norm_num))
theorem R90501 : Reach 90501 := rs (se 4 (by rfl) ⟨8484, by rfl⟩) (B 16969 (by norm_num) ⟨8484, by rfl⟩ (by norm_num))
theorem R90505 : Reach 90505 := rs (se 2 (by rfl) ⟨33939, by rfl⟩) (B 67879 (by norm_num) ⟨33939, by rfl⟩ (by norm_num))
theorem R90509 : Reach 90509 := rs (se 3 (by rfl) ⟨16970, by rfl⟩) (B 33941 (by norm_num) ⟨16970, by rfl⟩ (by norm_num))
theorem R90513 : Reach 90513 := rs (se 2 (by rfl) ⟨33942, by rfl⟩) (B 67885 (by norm_num) ⟨33942, by rfl⟩ (by norm_num))
theorem R90517 : Reach 90517 := rs (se 6 (by rfl) ⟨2121, by rfl⟩) (B 4243 (by norm_num) ⟨2121, by rfl⟩ (by norm_num))
theorem R90521 : Reach 90521 := rs (se 2 (by rfl) ⟨33945, by rfl⟩) (B 67891 (by norm_num) ⟨33945, by rfl⟩ (by norm_num))
theorem R90525 : Reach 90525 := rs (se 3 (by rfl) ⟨16973, by rfl⟩) (B 33947 (by norm_num) ⟨16973, by rfl⟩ (by norm_num))
theorem R90529 : Reach 90529 := rs (se 2 (by rfl) ⟨33948, by rfl⟩) (B 67897 (by norm_num) ⟨33948, by rfl⟩ (by norm_num))
theorem R90533 : Reach 90533 := rs (se 4 (by rfl) ⟨8487, by rfl⟩) (B 16975 (by norm_num) ⟨8487, by rfl⟩ (by norm_num))
theorem R90537 : Reach 90537 := rs (se 2 (by rfl) ⟨33951, by rfl⟩) (B 67903 (by norm_num) ⟨33951, by rfl⟩ (by norm_num))
theorem R90541 : Reach 90541 := rs (se 3 (by rfl) ⟨16976, by rfl⟩) (B 33953 (by norm_num) ⟨16976, by rfl⟩ (by norm_num))
theorem R90545 : Reach 90545 := rs (se 2 (by rfl) ⟨33954, by rfl⟩) (B 67909 (by norm_num) ⟨33954, by rfl⟩ (by norm_num))
theorem R90549 : Reach 90549 := rs (se 5 (by rfl) ⟨4244, by rfl⟩) (B 8489 (by norm_num) ⟨4244, by rfl⟩ (by norm_num))
theorem R90553 : Reach 90553 := rs (se 2 (by rfl) ⟨33957, by rfl⟩) (B 67915 (by norm_num) ⟨33957, by rfl⟩ (by norm_num))
theorem R90557 : Reach 90557 := rs (se 3 (by rfl) ⟨16979, by rfl⟩) (B 33959 (by norm_num) ⟨16979, by rfl⟩ (by norm_num))
theorem R90561 : Reach 90561 := rs (se 2 (by rfl) ⟨33960, by rfl⟩) (B 67921 (by norm_num) ⟨33960, by rfl⟩ (by norm_num))
theorem R90565 : Reach 90565 := rs (se 4 (by rfl) ⟨8490, by rfl⟩) (B 16981 (by norm_num) ⟨8490, by rfl⟩ (by norm_num))
theorem R90569 : Reach 90569 := rs (se 2 (by rfl) ⟨33963, by rfl⟩) (B 67927 (by norm_num) ⟨33963, by rfl⟩ (by norm_num))
theorem R90573 : Reach 90573 := rs (se 3 (by rfl) ⟨16982, by rfl⟩) (B 33965 (by norm_num) ⟨16982, by rfl⟩ (by norm_num))
theorem R90577 : Reach 90577 := rs (se 2 (by rfl) ⟨33966, by rfl⟩) (B 67933 (by norm_num) ⟨33966, by rfl⟩ (by norm_num))
theorem R90581 : Reach 90581 := rs (se 7 (by rfl) ⟨1061, by rfl⟩) (B 2123 (by norm_num) ⟨1061, by rfl⟩ (by norm_num))
theorem R90585 : Reach 90585 := rs (se 2 (by rfl) ⟨33969, by rfl⟩) (B 67939 (by norm_num) ⟨33969, by rfl⟩ (by norm_num))
theorem R90589 : Reach 90589 := rs (se 3 (by rfl) ⟨16985, by rfl⟩) (B 33971 (by norm_num) ⟨16985, by rfl⟩ (by norm_num))
theorem R90593 : Reach 90593 := rs (se 2 (by rfl) ⟨33972, by rfl⟩) (B 67945 (by norm_num) ⟨33972, by rfl⟩ (by norm_num))
theorem R90597 : Reach 90597 := rs (se 4 (by rfl) ⟨8493, by rfl⟩) (B 16987 (by norm_num) ⟨8493, by rfl⟩ (by norm_num))
theorem R90601 : Reach 90601 := rs (se 2 (by rfl) ⟨33975, by rfl⟩) (B 67951 (by norm_num) ⟨33975, by rfl⟩ (by norm_num))
theorem R90605 : Reach 90605 := rs (se 3 (by rfl) ⟨16988, by rfl⟩) (B 33977 (by norm_num) ⟨16988, by rfl⟩ (by norm_num))
theorem R90609 : Reach 90609 := rs (se 2 (by rfl) ⟨33978, by rfl⟩) (B 67957 (by norm_num) ⟨33978, by rfl⟩ (by norm_num))
theorem R90613 : Reach 90613 := rs (se 5 (by rfl) ⟨4247, by rfl⟩) (B 8495 (by norm_num) ⟨4247, by rfl⟩ (by norm_num))
theorem R90617 : Reach 90617 := rs (se 2 (by rfl) ⟨33981, by rfl⟩) (B 67963 (by norm_num) ⟨33981, by rfl⟩ (by norm_num))
theorem R90621 : Reach 90621 := rs (se 3 (by rfl) ⟨16991, by rfl⟩) (B 33983 (by norm_num) ⟨16991, by rfl⟩ (by norm_num))
theorem R90625 : Reach 90625 := rs (se 2 (by rfl) ⟨33984, by rfl⟩) (B 67969 (by norm_num) ⟨33984, by rfl⟩ (by norm_num))
theorem R90629 : Reach 90629 := rs (se 4 (by rfl) ⟨8496, by rfl⟩) (B 16993 (by norm_num) ⟨8496, by rfl⟩ (by norm_num))
theorem R90633 : Reach 90633 := rs (se 2 (by rfl) ⟨33987, by rfl⟩) (B 67975 (by norm_num) ⟨33987, by rfl⟩ (by norm_num))
theorem R90637 : Reach 90637 := rs (se 3 (by rfl) ⟨16994, by rfl⟩) (B 33989 (by norm_num) ⟨16994, by rfl⟩ (by norm_num))
theorem R90641 : Reach 90641 := rs (se 2 (by rfl) ⟨33990, by rfl⟩) (B 67981 (by norm_num) ⟨33990, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R90645 : Reach 90645 := rs (se 6 (by rfl) ⟨2124, by rfl⟩) (B 4249 (by norm_num) ⟨2124, by rfl⟩ (by norm_num))
theorem R90649 : Reach 90649 := rs (se 2 (by rfl) ⟨33993, by rfl⟩) (B 67987 (by norm_num) ⟨33993, by rfl⟩ (by norm_num))
theorem R90653 : Reach 90653 := rs (se 3 (by rfl) ⟨16997, by rfl⟩) (B 33995 (by norm_num) ⟨16997, by rfl⟩ (by norm_num))
theorem R90657 : Reach 90657 := rs (se 2 (by rfl) ⟨33996, by rfl⟩) (B 67993 (by norm_num) ⟨33996, by rfl⟩ (by norm_num))
theorem R90661 : Reach 90661 := rs (se 4 (by rfl) ⟨8499, by rfl⟩) (B 16999 (by norm_num) ⟨8499, by rfl⟩ (by norm_num))
theorem R90665 : Reach 90665 := rs (se 2 (by rfl) ⟨33999, by rfl⟩) (B 67999 (by norm_num) ⟨33999, by rfl⟩ (by norm_num))
theorem R90669 : Reach 90669 := rs (se 3 (by rfl) ⟨17000, by rfl⟩) (B 34001 (by norm_num) ⟨17000, by rfl⟩ (by norm_num))
theorem R90673 : Reach 90673 := rs (se 2 (by rfl) ⟨34002, by rfl⟩) (B 68005 (by norm_num) ⟨34002, by rfl⟩ (by norm_num))
theorem R90677 : Reach 90677 := rs (se 5 (by rfl) ⟨4250, by rfl⟩) (B 8501 (by norm_num) ⟨4250, by rfl⟩ (by norm_num))
theorem R90681 : Reach 90681 := rs (se 2 (by rfl) ⟨34005, by rfl⟩) (B 68011 (by norm_num) ⟨34005, by rfl⟩ (by norm_num))
theorem R90685 : Reach 90685 := rs (se 3 (by rfl) ⟨17003, by rfl⟩) (B 34007 (by norm_num) ⟨17003, by rfl⟩ (by norm_num))
theorem R90689 : Reach 90689 := rs (se 2 (by rfl) ⟨34008, by rfl⟩) (B 68017 (by norm_num) ⟨34008, by rfl⟩ (by norm_num))
theorem R90693 : Reach 90693 := rs (se 4 (by rfl) ⟨8502, by rfl⟩) (B 17005 (by norm_num) ⟨8502, by rfl⟩ (by norm_num))
theorem R90697 : Reach 90697 := rs (se 2 (by rfl) ⟨34011, by rfl⟩) (B 68023 (by norm_num) ⟨34011, by rfl⟩ (by norm_num))
theorem R90701 : Reach 90701 := rs (se 3 (by rfl) ⟨17006, by rfl⟩) (B 34013 (by norm_num) ⟨17006, by rfl⟩ (by norm_num))
theorem R90705 : Reach 90705 := rs (se 2 (by rfl) ⟨34014, by rfl⟩) (B 68029 (by norm_num) ⟨34014, by rfl⟩ (by norm_num))
theorem R90709 : Reach 90709 := rs (se 8 (by rfl) ⟨531, by rfl⟩) (B 1063 (by norm_num) ⟨531, by rfl⟩ (by norm_num))
theorem R90713 : Reach 90713 := rs (se 2 (by rfl) ⟨34017, by rfl⟩) (B 68035 (by norm_num) ⟨34017, by rfl⟩ (by norm_num))
theorem R90717 : Reach 90717 := rs (se 3 (by rfl) ⟨17009, by rfl⟩) (B 34019 (by norm_num) ⟨17009, by rfl⟩ (by norm_num))
theorem R90721 : Reach 90721 := rs (se 2 (by rfl) ⟨34020, by rfl⟩) (B 68041 (by norm_num) ⟨34020, by rfl⟩ (by norm_num))
theorem R90725 : Reach 90725 := rs (se 4 (by rfl) ⟨8505, by rfl⟩) (B 17011 (by norm_num) ⟨8505, by rfl⟩ (by norm_num))
theorem R90729 : Reach 90729 := rs (se 2 (by rfl) ⟨34023, by rfl⟩) (B 68047 (by norm_num) ⟨34023, by rfl⟩ (by norm_num))
theorem R90733 : Reach 90733 := rs (se 3 (by rfl) ⟨17012, by rfl⟩) (B 34025 (by norm_num) ⟨17012, by rfl⟩ (by norm_num))
theorem R90737 : Reach 90737 := rs (se 2 (by rfl) ⟨34026, by rfl⟩) (B 68053 (by norm_num) ⟨34026, by rfl⟩ (by norm_num))
theorem R516725 : Reach 516725 := rs (se 5 (by rfl) ⟨24221, by rfl⟩) (B 48443 (by norm_num) ⟨24221, by rfl⟩ (by norm_num))
theorem R90741 : Reach 90741 := rs (se 5 (by rfl) ⟨4253, by rfl⟩) (B 8507 (by norm_num) ⟨4253, by rfl⟩ (by norm_num))
theorem R90745 : Reach 90745 := rs (se 2 (by rfl) ⟨34029, by rfl⟩) (B 68059 (by norm_num) ⟨34029, by rfl⟩ (by norm_num))
theorem R90749 : Reach 90749 := rs (se 3 (by rfl) ⟨17015, by rfl⟩) (B 34031 (by norm_num) ⟨17015, by rfl⟩ (by norm_num))
theorem R90753 : Reach 90753 := rs (se 2 (by rfl) ⟨34032, by rfl⟩) (B 68065 (by norm_num) ⟨34032, by rfl⟩ (by norm_num))
theorem R90757 : Reach 90757 := rs (se 4 (by rfl) ⟨8508, by rfl⟩) (B 17017 (by norm_num) ⟨8508, by rfl⟩ (by norm_num))
theorem R90761 : Reach 90761 := rs (se 2 (by rfl) ⟨34035, by rfl⟩) (B 68071 (by norm_num) ⟨34035, by rfl⟩ (by norm_num))
theorem R90765 : Reach 90765 := rs (se 3 (by rfl) ⟨17018, by rfl⟩) (B 34037 (by norm_num) ⟨17018, by rfl⟩ (by norm_num))
theorem R90769 : Reach 90769 := rs (se 2 (by rfl) ⟨34038, by rfl⟩) (B 68077 (by norm_num) ⟨34038, by rfl⟩ (by norm_num))
theorem R90773 : Reach 90773 := rs (se 6 (by rfl) ⟨2127, by rfl⟩) (B 4255 (by norm_num) ⟨2127, by rfl⟩ (by norm_num))
theorem R90777 : Reach 90777 := rs (se 2 (by rfl) ⟨34041, by rfl⟩) (B 68083 (by norm_num) ⟨34041, by rfl⟩ (by norm_num))
theorem R90781 : Reach 90781 := rs (se 3 (by rfl) ⟨17021, by rfl⟩) (B 34043 (by norm_num) ⟨17021, by rfl⟩ (by norm_num))
theorem R90785 : Reach 90785 := rs (se 2 (by rfl) ⟨34044, by rfl⟩) (B 68089 (by norm_num) ⟨34044, by rfl⟩ (by norm_num))
theorem R90789 : Reach 90789 := rs (se 4 (by rfl) ⟨8511, by rfl⟩) (B 17023 (by norm_num) ⟨8511, by rfl⟩ (by norm_num))
theorem R90793 : Reach 90793 := rs (se 2 (by rfl) ⟨34047, by rfl⟩) (B 68095 (by norm_num) ⟨34047, by rfl⟩ (by norm_num))
theorem R90797 : Reach 90797 := rs (se 3 (by rfl) ⟨17024, by rfl⟩) (B 34049 (by norm_num) ⟨17024, by rfl⟩ (by norm_num))
theorem R90801 : Reach 90801 := rs (se 2 (by rfl) ⟨34050, by rfl⟩) (B 68101 (by norm_num) ⟨34050, by rfl⟩ (by norm_num))
theorem R90805 : Reach 90805 := rs (se 5 (by rfl) ⟨4256, by rfl⟩) (B 8513 (by norm_num) ⟨4256, by rfl⟩ (by norm_num))
theorem R90809 : Reach 90809 := rs (se 2 (by rfl) ⟨34053, by rfl⟩) (B 68107 (by norm_num) ⟨34053, by rfl⟩ (by norm_num))
theorem R90813 : Reach 90813 := rs (se 3 (by rfl) ⟨17027, by rfl⟩) (B 34055 (by norm_num) ⟨17027, by rfl⟩ (by norm_num))
theorem R90817 : Reach 90817 := rs (se 2 (by rfl) ⟨34056, by rfl⟩) (B 68113 (by norm_num) ⟨34056, by rfl⟩ (by norm_num))
theorem R189125 : Reach 189125 := rs (se 4 (by rfl) ⟨17730, by rfl⟩) (B 35461 (by norm_num) ⟨17730, by rfl⟩ (by norm_num))
theorem R90821 : Reach 90821 := rs (se 4 (by rfl) ⟨8514, by rfl⟩) (B 17029 (by norm_num) ⟨8514, by rfl⟩ (by norm_num))
theorem R90825 : Reach 90825 := rs (se 2 (by rfl) ⟨34059, by rfl⟩) (B 68119 (by norm_num) ⟨34059, by rfl⟩ (by norm_num))
theorem R90829 : Reach 90829 := rs (se 3 (by rfl) ⟨17030, by rfl⟩) (B 34061 (by norm_num) ⟨17030, by rfl⟩ (by norm_num))
theorem R90833 : Reach 90833 := rs (se 2 (by rfl) ⟨34062, by rfl⟩) (B 68125 (by norm_num) ⟨34062, by rfl⟩ (by norm_num))
theorem R90837 : Reach 90837 := rs (se 7 (by rfl) ⟨1064, by rfl⟩) (B 2129 (by norm_num) ⟨1064, by rfl⟩ (by norm_num))
theorem R90841 : Reach 90841 := rs (se 2 (by rfl) ⟨34065, by rfl⟩) (B 68131 (by norm_num) ⟨34065, by rfl⟩ (by norm_num))
theorem R90845 : Reach 90845 := rs (se 3 (by rfl) ⟨17033, by rfl⟩) (B 34067 (by norm_num) ⟨17033, by rfl⟩ (by norm_num))
theorem R90849 : Reach 90849 := rs (se 2 (by rfl) ⟨34068, by rfl⟩) (B 68137 (by norm_num) ⟨34068, by rfl⟩ (by norm_num))
theorem R90853 : Reach 90853 := rs (se 4 (by rfl) ⟨8517, by rfl⟩) (B 17035 (by norm_num) ⟨8517, by rfl⟩ (by norm_num))
theorem R90857 : Reach 90857 := rs (se 2 (by rfl) ⟨34071, by rfl⟩) (B 68143 (by norm_num) ⟨34071, by rfl⟩ (by norm_num))
theorem R90861 : Reach 90861 := rs (se 3 (by rfl) ⟨17036, by rfl⟩) (B 34073 (by norm_num) ⟨17036, by rfl⟩ (by norm_num))
theorem R90865 : Reach 90865 := rs (se 2 (by rfl) ⟨34074, by rfl⟩) (B 68149 (by norm_num) ⟨34074, by rfl⟩ (by norm_num))
theorem R90869 : Reach 90869 := rs (se 5 (by rfl) ⟨4259, by rfl⟩) (B 8519 (by norm_num) ⟨4259, by rfl⟩ (by norm_num))
theorem R90873 : Reach 90873 := rs (se 2 (by rfl) ⟨34077, by rfl⟩) (B 68155 (by norm_num) ⟨34077, by rfl⟩ (by norm_num))
theorem R90877 : Reach 90877 := rs (se 3 (by rfl) ⟨17039, by rfl⟩) (B 34079 (by norm_num) ⟨17039, by rfl⟩ (by norm_num))
theorem R90881 : Reach 90881 := rs (se 2 (by rfl) ⟨34080, by rfl⟩) (B 68161 (by norm_num) ⟨34080, by rfl⟩ (by norm_num))
theorem R90885 : Reach 90885 := rs (se 4 (by rfl) ⟨8520, by rfl⟩) (B 17041 (by norm_num) ⟨8520, by rfl⟩ (by norm_num))
theorem R90889 : Reach 90889 := rs (se 2 (by rfl) ⟨34083, by rfl⟩) (B 68167 (by norm_num) ⟨34083, by rfl⟩ (by norm_num))
theorem R90893 : Reach 90893 := rs (se 3 (by rfl) ⟨17042, by rfl⟩) (B 34085 (by norm_num) ⟨17042, by rfl⟩ (by norm_num))
theorem R90897 : Reach 90897 := rs (se 2 (by rfl) ⟨34086, by rfl⟩) (B 68173 (by norm_num) ⟨34086, by rfl⟩ (by norm_num))
theorem R90901 : Reach 90901 := rs (se 6 (by rfl) ⟨2130, by rfl⟩) (B 4261 (by norm_num) ⟨2130, by rfl⟩ (by norm_num))
theorem R90905 : Reach 90905 := rs (se 2 (by rfl) ⟨34089, by rfl⟩) (B 68179 (by norm_num) ⟨34089, by rfl⟩ (by norm_num))
theorem R90909 : Reach 90909 := rs (se 3 (by rfl) ⟨17045, by rfl⟩) (B 34091 (by norm_num) ⟨17045, by rfl⟩ (by norm_num))
theorem R90913 : Reach 90913 := rs (se 2 (by rfl) ⟨34092, by rfl⟩) (B 68185 (by norm_num) ⟨34092, by rfl⟩ (by norm_num))
theorem R90917 : Reach 90917 := rs (se 4 (by rfl) ⟨8523, by rfl⟩) (B 17047 (by norm_num) ⟨8523, by rfl⟩ (by norm_num))
theorem R90921 : Reach 90921 := rs (se 2 (by rfl) ⟨34095, by rfl⟩) (B 68191 (by norm_num) ⟨34095, by rfl⟩ (by norm_num))
theorem R90925 : Reach 90925 := rs (se 3 (by rfl) ⟨17048, by rfl⟩) (B 34097 (by norm_num) ⟨17048, by rfl⟩ (by norm_num))
theorem R90929 : Reach 90929 := rs (se 2 (by rfl) ⟨34098, by rfl⟩) (B 68197 (by norm_num) ⟨34098, by rfl⟩ (by norm_num))
theorem R90933 : Reach 90933 := rs (se 5 (by rfl) ⟨4262, by rfl⟩) (B 8525 (by norm_num) ⟨4262, by rfl⟩ (by norm_num))
theorem R90937 : Reach 90937 := rs (se 2 (by rfl) ⟨34101, by rfl⟩) (B 68203 (by norm_num) ⟨34101, by rfl⟩ (by norm_num))
theorem R90941 : Reach 90941 := rs (se 3 (by rfl) ⟨17051, by rfl⟩) (B 34103 (by norm_num) ⟨17051, by rfl⟩ (by norm_num))
theorem R90945 : Reach 90945 := rs (se 2 (by rfl) ⟨34104, by rfl⟩) (B 68209 (by norm_num) ⟨34104, by rfl⟩ (by norm_num))
theorem R90949 : Reach 90949 := rs (se 4 (by rfl) ⟨8526, by rfl⟩) (B 17053 (by norm_num) ⟨8526, by rfl⟩ (by norm_num))
theorem R90953 : Reach 90953 := rs (se 2 (by rfl) ⟨34107, by rfl⟩) (B 68215 (by norm_num) ⟨34107, by rfl⟩ (by norm_num))
theorem R90957 : Reach 90957 := rs (se 3 (by rfl) ⟨17054, by rfl⟩) (B 34109 (by norm_num) ⟨17054, by rfl⟩ (by norm_num))
theorem R90961 : Reach 90961 := rs (se 2 (by rfl) ⟨34110, by rfl⟩) (B 68221 (by norm_num) ⟨34110, by rfl⟩ (by norm_num))
theorem R90965 : Reach 90965 := rs (se 9 (by rfl) ⟨266, by rfl⟩) (B 533 (by norm_num) ⟨266, by rfl⟩ (by norm_num))
theorem R90969 : Reach 90969 := rs (se 2 (by rfl) ⟨34113, by rfl⟩) (B 68227 (by norm_num) ⟨34113, by rfl⟩ (by norm_num))
theorem R90973 : Reach 90973 := rs (se 3 (by rfl) ⟨17057, by rfl⟩) (B 34115 (by norm_num) ⟨17057, by rfl⟩ (by norm_num))
theorem R90977 : Reach 90977 := rs (se 2 (by rfl) ⟨34116, by rfl⟩) (B 68233 (by norm_num) ⟨34116, by rfl⟩ (by norm_num))
theorem R90981 : Reach 90981 := rs (se 4 (by rfl) ⟨8529, by rfl⟩) (B 17059 (by norm_num) ⟨8529, by rfl⟩ (by norm_num))
theorem R90985 : Reach 90985 := rs (se 2 (by rfl) ⟨34119, by rfl⟩) (B 68239 (by norm_num) ⟨34119, by rfl⟩ (by norm_num))
theorem R222061 : Reach 222061 := rs (se 3 (by rfl) ⟨41636, by rfl⟩) (B 83273 (by norm_num) ⟨41636, by rfl⟩ (by norm_num))
theorem R90989 : Reach 90989 := rs (se 3 (by rfl) ⟨17060, by rfl⟩) (B 34121 (by norm_num) ⟨17060, by rfl⟩ (by norm_num))
theorem R90993 : Reach 90993 := rs (se 2 (by rfl) ⟨34122, by rfl⟩) (B 68245 (by norm_num) ⟨34122, by rfl⟩ (by norm_num))
theorem R90997 : Reach 90997 := rs (se 5 (by rfl) ⟨4265, by rfl⟩) (B 8531 (by norm_num) ⟨4265, by rfl⟩ (by norm_num))
theorem R91001 : Reach 91001 := rs (se 2 (by rfl) ⟨34125, by rfl⟩) (B 68251 (by norm_num) ⟨34125, by rfl⟩ (by norm_num))
theorem R91005 : Reach 91005 := rs (se 3 (by rfl) ⟨17063, by rfl⟩) (B 34127 (by norm_num) ⟨17063, by rfl⟩ (by norm_num))
theorem R91009 : Reach 91009 := rs (se 2 (by rfl) ⟨34128, by rfl⟩) (B 68257 (by norm_num) ⟨34128, by rfl⟩ (by norm_num))
theorem R91013 : Reach 91013 := rs (se 4 (by rfl) ⟨8532, by rfl⟩) (B 17065 (by norm_num) ⟨8532, by rfl⟩ (by norm_num))
theorem R91017 : Reach 91017 := rs (se 2 (by rfl) ⟨34131, by rfl⟩) (B 68263 (by norm_num) ⟨34131, by rfl⟩ (by norm_num))
theorem R91021 : Reach 91021 := rs (se 3 (by rfl) ⟨17066, by rfl⟩) (B 34133 (by norm_num) ⟨17066, by rfl⟩ (by norm_num))
theorem R91025 : Reach 91025 := rs (se 2 (by rfl) ⟨34134, by rfl⟩) (B 68269 (by norm_num) ⟨34134, by rfl⟩ (by norm_num))
theorem R418709 : Reach 418709 := rs (se 6 (by rfl) ⟨9813, by rfl⟩) (B 19627 (by norm_num) ⟨9813, by rfl⟩ (by norm_num))
theorem R91029 : Reach 91029 := rs (se 6 (by rfl) ⟨2133, by rfl⟩) (B 4267 (by norm_num) ⟨2133, by rfl⟩ (by norm_num))
theorem R91033 : Reach 91033 := rs (se 2 (by rfl) ⟨34137, by rfl⟩) (B 68275 (by norm_num) ⟨34137, by rfl⟩ (by norm_num))
theorem R91037 : Reach 91037 := rs (se 3 (by rfl) ⟨17069, by rfl⟩) (B 34139 (by norm_num) ⟨17069, by rfl⟩ (by norm_num))
theorem R91041 : Reach 91041 := rs (se 2 (by rfl) ⟨34140, by rfl⟩) (B 68281 (by norm_num) ⟨34140, by rfl⟩ (by norm_num))
theorem R451493 : Reach 451493 := rs (se 4 (by rfl) ⟨42327, by rfl⟩) (B 84655 (by norm_num) ⟨42327, by rfl⟩ (by norm_num))
theorem R91045 : Reach 91045 := rs (se 4 (by rfl) ⟨8535, by rfl⟩) (B 17071 (by norm_num) ⟨8535, by rfl⟩ (by norm_num))
theorem R91049 : Reach 91049 := rs (se 2 (by rfl) ⟨34143, by rfl⟩) (B 68287 (by norm_num) ⟨34143, by rfl⟩ (by norm_num))
theorem R91053 : Reach 91053 := rs (se 3 (by rfl) ⟨17072, by rfl⟩) (B 34145 (by norm_num) ⟨17072, by rfl⟩ (by norm_num))
theorem R91057 : Reach 91057 := rs (se 2 (by rfl) ⟨34146, by rfl⟩) (B 68293 (by norm_num) ⟨34146, by rfl⟩ (by norm_num))
theorem R680885 : Reach 680885 := rs (se 5 (by rfl) ⟨31916, by rfl⟩) (B 63833 (by norm_num) ⟨31916, by rfl⟩ (by norm_num))
theorem R91061 : Reach 91061 := rs (se 5 (by rfl) ⟨4268, by rfl⟩) (B 8537 (by norm_num) ⟨4268, by rfl⟩ (by norm_num))
theorem R91065 : Reach 91065 := rs (se 2 (by rfl) ⟨34149, by rfl⟩) (B 68299 (by norm_num) ⟨34149, by rfl⟩ (by norm_num))
theorem R189373 : Reach 189373 := rs (se 3 (by rfl) ⟨35507, by rfl⟩) (B 71015 (by norm_num) ⟨35507, by rfl⟩ (by norm_num))
theorem R91069 : Reach 91069 := rs (se 3 (by rfl) ⟨17075, by rfl⟩) (B 34151 (by norm_num) ⟨17075, by rfl⟩ (by norm_num))
theorem R91073 : Reach 91073 := rs (se 2 (by rfl) ⟨34152, by rfl⟩) (B 68305 (by norm_num) ⟨34152, by rfl⟩ (by norm_num))
theorem R91077 : Reach 91077 := rs (se 4 (by rfl) ⟨8538, by rfl⟩) (B 17077 (by norm_num) ⟨8538, by rfl⟩ (by norm_num))
theorem R91081 : Reach 91081 := rs (se 2 (by rfl) ⟨34155, by rfl⟩) (B 68311 (by norm_num) ⟨34155, by rfl⟩ (by norm_num))
theorem R91085 : Reach 91085 := rs (se 3 (by rfl) ⟨17078, by rfl⟩) (B 34157 (by norm_num) ⟨17078, by rfl⟩ (by norm_num))
theorem R91089 : Reach 91089 := rs (se 2 (by rfl) ⟨34158, by rfl⟩) (B 68317 (by norm_num) ⟨34158, by rfl⟩ (by norm_num))
theorem R1139669 : Reach 1139669 := rs (se 7 (by rfl) ⟨13355, by rfl⟩) (B 26711 (by norm_num) ⟨13355, by rfl⟩ (by norm_num))
theorem R91093 : Reach 91093 := rs (se 7 (by rfl) ⟨1067, by rfl⟩) (B 2135 (by norm_num) ⟨1067, by rfl⟩ (by norm_num))
theorem R91097 : Reach 91097 := rs (se 2 (by rfl) ⟨34161, by rfl⟩) (B 68323 (by norm_num) ⟨34161, by rfl⟩ (by norm_num))
theorem R222173 : Reach 222173 := rs (se 3 (by rfl) ⟨41657, by rfl⟩) (B 83315 (by norm_num) ⟨41657, by rfl⟩ (by norm_num))
theorem R91101 : Reach 91101 := rs (se 3 (by rfl) ⟨17081, by rfl⟩) (B 34163 (by norm_num) ⟨17081, by rfl⟩ (by norm_num))
theorem R91105 : Reach 91105 := rs (se 2 (by rfl) ⟨34164, by rfl⟩) (B 68329 (by norm_num) ⟨34164, by rfl⟩ (by norm_num))
theorem R91109 : Reach 91109 := rs (se 4 (by rfl) ⟨8541, by rfl⟩) (B 17083 (by norm_num) ⟨8541, by rfl⟩ (by norm_num))
theorem R91113 : Reach 91113 := rs (se 2 (by rfl) ⟨34167, by rfl⟩) (B 68335 (by norm_num) ⟨34167, by rfl⟩ (by norm_num))
theorem R91117 : Reach 91117 := rs (se 3 (by rfl) ⟨17084, by rfl⟩) (B 34169 (by norm_num) ⟨17084, by rfl⟩ (by norm_num))
theorem R91121 : Reach 91121 := rs (se 2 (by rfl) ⟨34170, by rfl⟩) (B 68341 (by norm_num) ⟨34170, by rfl⟩ (by norm_num))
theorem R91125 : Reach 91125 := rs (se 5 (by rfl) ⟨4271, by rfl⟩) (B 8543 (by norm_num) ⟨4271, by rfl⟩ (by norm_num))
theorem R91129 : Reach 91129 := rs (se 2 (by rfl) ⟨34173, by rfl⟩) (B 68347 (by norm_num) ⟨34173, by rfl⟩ (by norm_num))
theorem R287813 : Reach 287813 := rs (se 4 (by rfl) ⟨26982, by rfl⟩) (B 53965 (by norm_num) ⟨26982, by rfl⟩ (by norm_num))
theorem R222365 : Reach 222365 := rs (se 3 (by rfl) ⟨41693, by rfl⟩) (B 83387 (by norm_num) ⟨41693, by rfl⟩ (by norm_num))
theorem R517429 : Reach 517429 := rs (se 5 (by rfl) ⟨24254, by rfl⟩) (B 48509 (by norm_num) ⟨24254, by rfl⟩ (by norm_num))
theorem R157037 : Reach 157037 := rs (se 3 (by rfl) ⟨29444, by rfl⟩) (B 58889 (by norm_num) ⟨29444, by rfl⟩ (by norm_num))
theorem R189877 : Reach 189877 := rs (se 5 (by rfl) ⟨8900, by rfl⟩) (B 17801 (by norm_num) ⟨8900, by rfl⟩ (by norm_num))
theorem R255413 : Reach 255413 := rs (se 5 (by rfl) ⟨11972, by rfl⟩) (B 23945 (by norm_num) ⟨11972, by rfl⟩ (by norm_num))
theorem R222709 : Reach 222709 := rs (se 5 (by rfl) ⟨10439, by rfl⟩) (B 20879 (by norm_num) ⟨10439, by rfl⟩ (by norm_num))
theorem R419381 : Reach 419381 := rs (se 5 (by rfl) ⟨19658, by rfl⟩) (B 39317 (by norm_num) ⟨19658, by rfl⟩ (by norm_num))
theorem R124517 : Reach 124517 := rs (se 4 (by rfl) ⟨11673, by rfl⟩) (B 23347 (by norm_num) ⟨11673, by rfl⟩ (by norm_num))
theorem R222821 : Reach 222821 := rs (se 4 (by rfl) ⟨20889, by rfl⟩) (B 41779 (by norm_num) ⟨20889, by rfl⟩ (by norm_num))
theorem R91837 : Reach 91837 := rs (se 3 (by rfl) ⟨17219, by rfl⟩) (B 34439 (by norm_num) ⟨17219, by rfl⟩ (by norm_num))
theorem R223013 : Reach 223013 := rs (se 4 (by rfl) ⟨20907, by rfl⟩) (B 41815 (by norm_num) ⟨20907, by rfl⟩ (by norm_num))
theorem R256085 : Reach 256085 := rs (se 8 (by rfl) ⟨1500, by rfl⟩) (B 3001 (by norm_num) ⟨1500, by rfl⟩ (by norm_num))
theorem R223357 : Reach 223357 := rs (se 3 (by rfl) ⟨41879, by rfl⟩) (B 83759 (by norm_num) ⟨41879, by rfl⟩ (by norm_num))
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) (B 46901 (by norm_num) ⟨23450, by rfl⟩ (by norm_num))
theorem R288917 : Reach 288917 := rs (se 6 (by rfl) ⟨6771, by rfl⟩) (B 13543 (by norm_num) ⟨6771, by rfl⟩ (by norm_num))
theorem R354469 : Reach 354469 := rs (se 4 (by rfl) ⟨33231, by rfl⟩) (B 66463 (by norm_num) ⟨33231, by rfl⟩ (by norm_num))
theorem R452789 : Reach 452789 := rs (se 5 (by rfl) ⟨21224, by rfl⟩) (B 42449 (by norm_num) ⟨21224, by rfl⟩ (by norm_num))
theorem R223469 : Reach 223469 := rs (se 3 (by rfl) ⟨41900, by rfl⟩) (B 83801 (by norm_num) ⟨41900, by rfl⟩ (by norm_num))
theorem R190765 : Reach 190765 := rs (se 3 (by rfl) ⟨35768, by rfl⟩) (B 71537 (by norm_num) ⟨35768, by rfl⟩ (by norm_num))
theorem R223661 : Reach 223661 := rs (se 3 (by rfl) ⟨41936, by rfl⟩) (B 83873 (by norm_num) ⟨41936, by rfl⟩ (by norm_num))
theorem R256517 : Reach 256517 := rs (se 4 (by rfl) ⟨24048, by rfl⟩) (B 48097 (by norm_num) ⟨24048, by rfl⟩ (by norm_num))
theorem R453205 : Reach 453205 := rs (se 8 (by rfl) ⟨2655, by rfl⟩) (B 5311 (by norm_num) ⟨2655, by rfl⟩ (by norm_num))
theorem R813685 : Reach 813685 := rs (se 5 (by rfl) ⟨38141, by rfl⟩) (B 76283 (by norm_num) ⟨38141, by rfl⟩ (by norm_num))
theorem R224005 : Reach 224005 := rs (se 4 (by rfl) ⟨21000, by rfl⟩) (B 42001 (by norm_num) ⟨21000, by rfl⟩ (by norm_num))
theorem R191261 : Reach 191261 := rs (se 3 (by rfl) ⟨35861, by rfl⟩) (B 71723 (by norm_num) ⟨35861, by rfl⟩ (by norm_num))
theorem R224117 : Reach 224117 := rs (se 5 (by rfl) ⟨10505, by rfl⟩) (B 21011 (by norm_num) ⟨10505, by rfl⟩ (by norm_num))
theorem R125821 : Reach 125821 := rs (se 3 (by rfl) ⟨23591, by rfl⟩) (B 47183 (by norm_num) ⟨23591, by rfl⟩ (by norm_num))
theorem R387989 : Reach 387989 := rs (se 6 (by rfl) ⟨9093, by rfl⟩) (B 18187 (by norm_num) ⟨9093, by rfl⟩ (by norm_num))
theorem R224309 : Reach 224309 := rs (se 5 (by rfl) ⟨10514, by rfl⟩) (B 21029 (by norm_num) ⟨10514, by rfl⟩ (by norm_num))
theorem R257269 : Reach 257269 := rs (se 5 (by rfl) ⟨12059, by rfl⟩) (B 24119 (by norm_num) ⟨12059, by rfl⟩ (by norm_num))
theorem R93469 : Reach 93469 := rs (se 3 (by rfl) ⟨17525, by rfl⟩) (B 35051 (by norm_num) ⟨17525, by rfl⟩ (by norm_num))
theorem R93485 : Reach 93485 := rs (se 3 (by rfl) ⟨17528, by rfl⟩) (B 35057 (by norm_num) ⟨17528, by rfl⟩ (by norm_num))
theorem R224653 : Reach 224653 := rs (se 3 (by rfl) ⟨42122, by rfl⟩) (B 84245 (by norm_num) ⟨42122, by rfl⟩ (by norm_num))
theorem R93593 : Reach 93593 := rs (se 2 (by rfl) ⟨35097, by rfl⟩) (B 70195 (by norm_num) ⟨35097, by rfl⟩ (by norm_num))
theorem R454085 : Reach 454085 := rs (se 4 (by rfl) ⟨42570, by rfl⟩) (B 85141 (by norm_num) ⟨42570, by rfl⟩ (by norm_num))
theorem R257525 : Reach 257525 := rs (se 5 (by rfl) ⟨12071, by rfl⟩) (B 24143 (by norm_num) ⟨12071, by rfl⟩ (by norm_num))
theorem R224765 : Reach 224765 := rs (se 3 (by rfl) ⟨42143, by rfl⟩) (B 84287 (by norm_num) ⟨42143, by rfl⟩ (by norm_num))
theorem R93845 : Reach 93845 := rs (se 6 (by rfl) ⟨2199, by rfl⟩) (B 4399 (by norm_num) ⟨2199, by rfl⟩ (by norm_num))
theorem R126613 : Reach 126613 := rs (se 6 (by rfl) ⟨2967, by rfl⟩) (B 5935 (by norm_num) ⟨2967, by rfl⟩ (by norm_num))
theorem R192149 : Reach 192149 := rs (se 6 (by rfl) ⟨4503, by rfl⟩) (B 9007 (by norm_num) ⟨4503, by rfl⟩ (by norm_num))
theorem R224957 : Reach 224957 := rs (se 3 (by rfl) ⟨42179, by rfl⟩) (B 84359 (by norm_num) ⟨42179, by rfl⟩ (by norm_num))
theorem R192269 : Reach 192269 := rs (se 3 (by rfl) ⟨36050, by rfl⟩) (B 72101 (by norm_num) ⟨36050, by rfl⟩ (by norm_num))
theorem R126949 : Reach 126949 := rs (se 4 (by rfl) ⟨11901, by rfl⟩) (B 23803 (by norm_num) ⟨11901, by rfl⟩ (by norm_num))
theorem R716789 : Reach 716789 := rs (se 5 (by rfl) ⟨33599, by rfl⟩) (B 67199 (by norm_num) ⟨33599, by rfl⟩ (by norm_num))
theorem R225301 : Reach 225301 := rs (se 6 (by rfl) ⟨5280, by rfl⟩) (B 10561 (by norm_num) ⟨5280, by rfl⟩ (by norm_num))
theorem R290837 : Reach 290837 := rs (se 6 (by rfl) ⟨6816, by rfl⟩) (B 13633 (by norm_num) ⟨6816, by rfl⟩ (by norm_num))
theorem R94289 : Reach 94289 := rs (se 2 (by rfl) ⟨35358, by rfl⟩) (B 70717 (by norm_num) ⟨35358, by rfl⟩ (by norm_num))
theorem R225413 : Reach 225413 := rs (se 4 (by rfl) ⟨21132, by rfl⟩) (B 42265 (by norm_num) ⟨21132, by rfl⟩ (by norm_num))
theorem R127165 : Reach 127165 := rs (se 3 (by rfl) ⟨23843, by rfl⟩) (B 47687 (by norm_num) ⟨23843, by rfl⟩ (by norm_num))
theorem R520501 : Reach 520501 := rs (se 5 (by rfl) ⟨24398, by rfl⟩) (B 48797 (by norm_num) ⟨24398, by rfl⟩ (by norm_num))
theorem R225605 : Reach 225605 := rs (se 4 (by rfl) ⟨21150, by rfl⟩) (B 42301 (by norm_num) ⟨21150, by rfl⟩ (by norm_num))
theorem R94537 : Reach 94537 := rs (se 2 (by rfl) ⟨35451, by rfl⟩) (B 70903 (by norm_num) ⟨35451, by rfl⟩ (by norm_num))
theorem R192901 : Reach 192901 := rs (se 4 (by rfl) ⟨18084, by rfl⟩) (B 36169 (by norm_num) ⟨18084, by rfl⟩ (by norm_num))
theorem R750005 : Reach 750005 := rs (se 5 (by rfl) ⟨35156, by rfl⟩) (B 70313 (by norm_num) ⟨35156, by rfl⟩ (by norm_num))
theorem R160309 : Reach 160309 := rs (se 5 (by rfl) ⟨7514, by rfl⟩) (B 15029 (by norm_num) ⟨7514, by rfl⟩ (by norm_num))
theorem R127541 : Reach 127541 := rs (se 5 (by rfl) ⟨5978, by rfl⟩) (B 11957 (by norm_num) ⟨5978, by rfl⟩ (by norm_num))
theorem R225949 : Reach 225949 := rs (se 3 (by rfl) ⟨42365, by rfl⟩) (B 84731 (by norm_num) ⟨42365, by rfl⟩ (by norm_num))
theorem R455381 : Reach 455381 := rs (se 7 (by rfl) ⟨5336, by rfl⟩) (B 10673 (by norm_num) ⟨5336, by rfl⟩ (by norm_num))
theorem R94981 : Reach 94981 := rs (se 4 (by rfl) ⟨8904, by rfl⟩) (B 17809 (by norm_num) ⟨8904, by rfl⟩ (by norm_num))
theorem R226061 : Reach 226061 := rs (se 3 (by rfl) ⟨42386, by rfl⟩) (B 84773 (by norm_num) ⟨42386, by rfl⟩ (by norm_num))
theorem R95041 : Reach 95041 := rs (se 2 (by rfl) ⟨35640, by rfl⟩) (B 71281 (by norm_num) ⟨35640, by rfl⟩ (by norm_num))
theorem R226253 : Reach 226253 := rs (se 3 (by rfl) ⟨42422, by rfl⟩) (B 84845 (by norm_num) ⟨42422, by rfl⟩ (by norm_num))
theorem R95357 : Reach 95357 := rs (se 3 (by rfl) ⟨17879, by rfl⟩) (B 35759 (by norm_num) ⟨17879, by rfl⟩ (by norm_num))
theorem R488693 : Reach 488693 := rs (se 5 (by rfl) ⟨22907, by rfl⟩) (B 45815 (by norm_num) ⟨22907, by rfl⟩ (by norm_num))
theorem R193789 : Reach 193789 := rs (se 3 (by rfl) ⟨36335, by rfl⟩) (B 72671 (by norm_num) ⟨36335, by rfl⟩ (by norm_num))
theorem R226597 : Reach 226597 := rs (se 4 (by rfl) ⟨21243, by rfl⟩) (B 42487 (by norm_num) ⟨21243, by rfl⟩ (by norm_num))
theorem R3437909 : Reach 3437909 := rs (se 13 (by rfl) ⟨629, by rfl⟩) (B 1259 (by norm_num) ⟨629, by rfl⟩ (by norm_num))
theorem R161117 : Reach 161117 := rs (se 3 (by rfl) ⟨30209, by rfl⟩) (B 60419 (by norm_num) ⟨30209, by rfl⟩ (by norm_num))
theorem R193909 : Reach 193909 := rs (se 5 (by rfl) ⟨9089, by rfl⟩) (B 18179 (by norm_num) ⟨9089, by rfl⟩ (by norm_num))
theorem R226709 : Reach 226709 := rs (se 6 (by rfl) ⟨5313, by rfl⟩) (B 10627 (by norm_num) ⟨5313, by rfl⟩ (by norm_num))
theorem R128461 : Reach 128461 := rs (se 3 (by rfl) ⟨24086, by rfl⟩) (B 48173 (by norm_num) ⟨24086, by rfl⟩ (by norm_num))
theorem R456245 : Reach 456245 := rs (se 5 (by rfl) ⟨21386, by rfl⟩) (B 42773 (by norm_num) ⟨21386, by rfl⟩ (by norm_num))
theorem R292405 : Reach 292405 := rs (se 5 (by rfl) ⟨13706, by rfl⟩) (B 27413 (by norm_num) ⟨13706, by rfl⟩ (by norm_num))
theorem R95801 : Reach 95801 := rs (se 2 (by rfl) ⟨35925, by rfl⟩) (B 71851 (by norm_num) ⟨35925, by rfl⟩ (by norm_num))
theorem R226901 : Reach 226901 := rs (se 8 (by rfl) ⟨1329, by rfl⟩) (B 2659 (by norm_num) ⟨1329, by rfl⟩ (by norm_num))
theorem R95861 : Reach 95861 := rs (se 5 (by rfl) ⟨4493, by rfl⟩) (B 8987 (by norm_num) ⟨4493, by rfl⟩ (by norm_num))
theorem R194165 : Reach 194165 := rs (se 5 (by rfl) ⟨9101, by rfl⟩) (B 18203 (by norm_num) ⟨9101, by rfl⟩ (by norm_num))
theorem R358037 : Reach 358037 := rs (se 6 (by rfl) ⟨8391, by rfl⟩) (B 16783 (by norm_num) ⟨8391, by rfl⟩ (by norm_num))
theorem R95989 : Reach 95989 := rs (se 5 (by rfl) ⟨4499, by rfl⟩) (B 8999 (by norm_num) ⟨4499, by rfl⟩ (by norm_num))
theorem R96049 : Reach 96049 := rs (se 2 (by rfl) ⟨36018, by rfl⟩) (B 72037 (by norm_num) ⟨36018, by rfl⟩ (by norm_num))
theorem R161605 : Reach 161605 := rs (se 4 (by rfl) ⟨15150, by rfl⟩) (B 30301 (by norm_num) ⟨15150, by rfl⟩ (by norm_num))
theorem R227245 : Reach 227245 := rs (se 3 (by rfl) ⟨42608, by rfl⟩) (B 85217 (by norm_num) ⟨42608, by rfl⟩ (by norm_num))
theorem R128965 : Reach 128965 := rs (se 4 (by rfl) ⟨12090, by rfl⟩) (B 24181 (by norm_num) ⟨12090, by rfl⟩ (by norm_num))
theorem R456677 : Reach 456677 := rs (se 4 (by rfl) ⟨42813, by rfl⟩) (B 85627 (by norm_num) ⟨42813, by rfl⟩ (by norm_num))
theorem R227357 : Reach 227357 := rs (se 3 (by rfl) ⟨42629, by rfl⟩) (B 85259 (by norm_num) ⟨42629, by rfl⟩ (by norm_num))
theorem R96433 : Reach 96433 := rs (se 2 (by rfl) ⟨36162, by rfl⟩) (B 72325 (by norm_num) ⟨36162, by rfl⟩ (by norm_num))
theorem R227549 : Reach 227549 := rs (se 3 (by rfl) ⟨42665, by rfl⟩) (B 85331 (by norm_num) ⟨42665, by rfl⟩ (by norm_num))
theorem R96553 : Reach 96553 := rs (se 2 (by rfl) ⟨36207, by rfl⟩) (B 72415 (by norm_num) ⟨36207, by rfl⟩ (by norm_num))
theorem R391493 : Reach 391493 := rs (se 4 (by rfl) ⟨36702, by rfl⟩) (B 73405 (by norm_num) ⟨36702, by rfl⟩ (by norm_num))
theorem R719189 : Reach 719189 := rs (se 10 (by rfl) ⟨1053, by rfl⟩) (B 2107 (by norm_num) ⟨1053, by rfl⟩ (by norm_num))
theorem R227701 : Reach 227701 := rs (se 5 (by rfl) ⟨10673, by rfl⟩) (B 21347 (by norm_num) ⟨10673, by rfl⟩ (by norm_num))
theorem R326069 : Reach 326069 := rs (se 5 (by rfl) ⟨15284, by rfl⟩) (B 30569 (by norm_num) ⟨15284, by rfl⟩ (by norm_num))
theorem R260597 : Reach 260597 := rs (se 5 (by rfl) ⟨12215, by rfl⟩) (B 24431 (by norm_num) ⟨12215, by rfl⟩ (by norm_num))
theorem R129557 : Reach 129557 := rs (se 6 (by rfl) ⟨3036, by rfl⟩) (B 6073 (by norm_num) ⟨3036, by rfl⟩ (by norm_num))
theorem R96805 : Reach 96805 := rs (se 4 (by rfl) ⟨9075, by rfl⟩) (B 18151 (by norm_num) ⟨9075, by rfl⟩ (by norm_num))
theorem R96809 : Reach 96809 := rs (se 2 (by rfl) ⟨36303, by rfl⟩) (B 72607 (by norm_num) ⟨36303, by rfl⟩ (by norm_num))
theorem R227893 : Reach 227893 := rs (se 5 (by rfl) ⟨10682, by rfl⟩) (B 21365 (by norm_num) ⟨10682, by rfl⟩ (by norm_num))
theorem R129637 : Reach 129637 := rs (se 4 (by rfl) ⟨12153, by rfl⟩) (B 24307 (by norm_num) ⟨12153, by rfl⟩ (by norm_num))
theorem R424597 : Reach 424597 := rs (se 6 (by rfl) ⟨9951, by rfl⟩) (B 19903 (by norm_num) ⟨9951, by rfl⟩ (by norm_num))
theorem R228005 : Reach 228005 := rs (se 4 (by rfl) ⟨21375, by rfl⟩) (B 42751 (by norm_num) ⟨21375, by rfl⟩ (by norm_num))
theorem R228197 : Reach 228197 := rs (se 4 (by rfl) ⟨21393, by rfl⟩) (B 42787 (by norm_num) ⟨21393, by rfl⟩ (by norm_num))
theorem R326501 : Reach 326501 := rs (se 4 (by rfl) ⟨30609, by rfl⟩) (B 61219 (by norm_num) ⟨30609, by rfl⟩ (by norm_num))
theorem R228541 : Reach 228541 := rs (se 3 (by rfl) ⟨42851, by rfl⟩) (B 85703 (by norm_num) ⟨42851, by rfl⟩ (by norm_num))
theorem R195797 : Reach 195797 := rs (se 7 (by rfl) ⟨2294, by rfl⟩) (B 4589 (by norm_num) ⟨2294, by rfl⟩ (by norm_num))
theorem R457973 : Reach 457973 := rs (se 5 (by rfl) ⟨21467, by rfl⟩) (B 42935 (by norm_num) ⟨21467, by rfl⟩ (by norm_num))
theorem R228653 : Reach 228653 := rs (se 3 (by rfl) ⟨42872, by rfl⟩) (B 85745 (by norm_num) ⟨42872, by rfl⟩ (by norm_num))
theorem R294245 : Reach 294245 := rs (se 4 (by rfl) ⟨27585, by rfl⟩) (B 55171 (by norm_num) ⟨27585, by rfl⟩ (by norm_num))
theorem R228845 : Reach 228845 := rs (se 3 (by rfl) ⟨42908, by rfl⟩) (B 85817 (by norm_num) ⟨42908, by rfl⟩ (by norm_num))
theorem R196109 : Reach 196109 := rs (se 3 (by rfl) ⟨36770, by rfl⟩) (B 73541 (by norm_num) ⟨36770, by rfl⟩ (by norm_num))
theorem R196181 : Reach 196181 := rs (se 8 (by rfl) ⟨1149, by rfl⟩) (B 2299 (by norm_num) ⟨1149, by rfl⟩ (by norm_num))
theorem R982613 : Reach 982613 := rs (se 8 (by rfl) ⟨5757, by rfl⟩) (B 11515 (by norm_num) ⟨5757, by rfl⟩ (by norm_num))
theorem R130709 : Reach 130709 := rs (se 6 (by rfl) ⟨3063, by rfl⟩) (B 6127 (by norm_num) ⟨3063, by rfl⟩ (by norm_num))
theorem R196253 : Reach 196253 := rs (se 3 (by rfl) ⟨36797, by rfl⟩) (B 73595 (by norm_num) ⟨36797, by rfl⟩ (by norm_num))
theorem R130733 : Reach 130733 := rs (se 3 (by rfl) ⟨24512, by rfl⟩) (B 49025 (by norm_num) ⟨24512, by rfl⟩ (by norm_num))
theorem R130757 : Reach 130757 := rs (se 4 (by rfl) ⟨12258, by rfl⟩) (B 24517 (by norm_num) ⟨12258, by rfl⟩ (by norm_num))
theorem R491221 : Reach 491221 := rs (se 7 (by rfl) ⟨5756, by rfl⟩) (B 11513 (by norm_num) ⟨5756, by rfl⟩ (by norm_num))
theorem R130781 : Reach 130781 := rs (se 3 (by rfl) ⟨24521, by rfl⟩) (B 49043 (by norm_num) ⟨24521, by rfl⟩ (by norm_num))
theorem R196325 : Reach 196325 := rs (se 4 (by rfl) ⟨18405, by rfl⟩) (B 36811 (by norm_num) ⟨18405, by rfl⟩ (by norm_num))
theorem R130805 : Reach 130805 := rs (se 5 (by rfl) ⟨6131, by rfl⟩) (B 12263 (by norm_num) ⟨6131, by rfl⟩ (by norm_num))
theorem R98041 : Reach 98041 := rs (se 2 (by rfl) ⟨36765, by rfl⟩) (B 73531 (by norm_num) ⟨36765, by rfl⟩ (by norm_num))
theorem R130829 : Reach 130829 := rs (se 3 (by rfl) ⟨24530, by rfl⟩) (B 49061 (by norm_num) ⟨24530, by rfl⟩ (by norm_num))
theorem R294677 : Reach 294677 := rs (se 6 (by rfl) ⟨6906, by rfl⟩) (B 13813 (by norm_num) ⟨6906, by rfl⟩ (by norm_num))
theorem R98077 : Reach 98077 := rs (se 3 (by rfl) ⟨18389, by rfl⟩) (B 36779 (by norm_num) ⟨18389, by rfl⟩ (by norm_num))
theorem R130853 : Reach 130853 := rs (se 4 (by rfl) ⟨12267, by rfl⟩) (B 24535 (by norm_num) ⟨12267, by rfl⟩ (by norm_num))
theorem R196397 : Reach 196397 := rs (se 3 (by rfl) ⟨36824, by rfl⟩) (B 73649 (by norm_num) ⟨36824, by rfl⟩ (by norm_num))
theorem R130877 : Reach 130877 := rs (se 3 (by rfl) ⟨24539, by rfl⟩) (B 49079 (by norm_num) ⟨24539, by rfl⟩ (by norm_num))
theorem R98113 : Reach 98113 := rs (se 2 (by rfl) ⟨36792, by rfl⟩) (B 73585 (by norm_num) ⟨36792, by rfl⟩ (by norm_num))
theorem R229189 : Reach 229189 := rs (se 4 (by rfl) ⟨21486, by rfl⟩) (B 42973 (by norm_num) ⟨21486, by rfl⟩ (by norm_num))
theorem R130901 : Reach 130901 := rs (se 9 (by rfl) ⟨383, by rfl⟩) (B 767 (by norm_num) ⟨383, by rfl⟩ (by norm_num))
theorem R98149 : Reach 98149 := rs (se 4 (by rfl) ⟨9201, by rfl⟩) (B 18403 (by norm_num) ⟨9201, by rfl⟩ (by norm_num))
theorem R130925 : Reach 130925 := rs (se 3 (by rfl) ⟨24548, by rfl⟩) (B 49097 (by norm_num) ⟨24548, by rfl⟩ (by norm_num))
theorem R196469 : Reach 196469 := rs (se 5 (by rfl) ⟨9209, by rfl⟩) (B 18419 (by norm_num) ⟨9209, by rfl⟩ (by norm_num))
theorem R130949 : Reach 130949 := rs (se 4 (by rfl) ⟨12276, by rfl⟩) (B 24553 (by norm_num) ⟨12276, by rfl⟩ (by norm_num))
theorem R98185 : Reach 98185 := rs (se 2 (by rfl) ⟨36819, by rfl⟩) (B 73639 (by norm_num) ⟨36819, by rfl⟩ (by norm_num))
theorem R130973 : Reach 130973 := rs (se 3 (by rfl) ⟨24557, by rfl⟩) (B 49115 (by norm_num) ⟨24557, by rfl⟩ (by norm_num))
theorem R98221 : Reach 98221 := rs (se 3 (by rfl) ⟨18416, by rfl⟩) (B 36833 (by norm_num) ⟨18416, by rfl⟩ (by norm_num))
theorem R130997 : Reach 130997 := rs (se 5 (by rfl) ⟨6140, by rfl⟩) (B 12281 (by norm_num) ⟨6140, by rfl⟩ (by norm_num))
theorem R229301 : Reach 229301 := rs (se 5 (by rfl) ⟨10748, by rfl⟩) (B 21497 (by norm_num) ⟨10748, by rfl⟩ (by norm_num))
theorem R196541 : Reach 196541 := rs (se 3 (by rfl) ⟨36851, by rfl⟩) (B 73703 (by norm_num) ⟨36851, by rfl⟩ (by norm_num))
theorem R131021 : Reach 131021 := rs (se 3 (by rfl) ⟨24566, by rfl⟩) (B 49133 (by norm_num) ⟨24566, by rfl⟩ (by norm_num))
theorem R98257 : Reach 98257 := rs (se 2 (by rfl) ⟨36846, by rfl⟩) (B 73693 (by norm_num) ⟨36846, by rfl⟩ (by norm_num))
theorem R131045 : Reach 131045 := rs (se 4 (by rfl) ⟨12285, by rfl⟩) (B 24571 (by norm_num) ⟨12285, by rfl⟩ (by norm_num))
theorem R98293 : Reach 98293 := rs (se 5 (by rfl) ⟨4607, by rfl⟩) (B 9215 (by norm_num) ⟨4607, by rfl⟩ (by norm_num))
theorem R131069 : Reach 131069 := rs (se 3 (by rfl) ⟨24575, by rfl⟩) (B 49151 (by norm_num) ⟨24575, by rfl⟩ (by norm_num))
theorem R131075 : Reach 131075 := rs (se 1 (by rfl) ⟨98306, by rfl⟩) R196613
theorem R131105 : Reach 131105 := rs (se 2 (by rfl) ⟨49164, by rfl⟩) R98329
theorem R294947 : Reach 294947 := rs (se 1 (by rfl) ⟨221210, by rfl⟩) R442421
theorem R131123 : Reach 131123 := rs (se 1 (by rfl) ⟨98342, by rfl⟩) R196685
theorem R131153 : Reach 131153 := rs (se 2 (by rfl) ⟨49182, by rfl⟩) R98365
theorem R131171 : Reach 131171 := rs (se 1 (by rfl) ⟨98378, by rfl⟩) R196757
theorem R196721 : Reach 196721 := rs (se 2 (by rfl) ⟨73770, by rfl⟩) R147541
theorem R98419 : Reach 98419 := rs (se 1 (by rfl) ⟨73814, by rfl⟩) R147629
theorem R131201 : Reach 131201 := rs (se 2 (by rfl) ⟨49200, by rfl⟩) R98401
theorem R196739 : Reach 196739 := rs (se 1 (by rfl) ⟨147554, by rfl⟩) R295109
theorem R131219 : Reach 131219 := rs (se 1 (by rfl) ⟨98414, by rfl⟩) R196829
theorem R131249 : Reach 131249 := rs (se 2 (by rfl) ⟨49218, by rfl⟩) R98437
theorem R131267 : Reach 131267 := rs (se 1 (by rfl) ⟨98450, by rfl⟩) R196901
theorem R131297 : Reach 131297 := rs (se 2 (by rfl) ⟨49236, by rfl⟩) R98473
theorem R131315 : Reach 131315 := rs (se 1 (by rfl) ⟨98486, by rfl⟩) R196973
theorem R98563 : Reach 98563 := rs (se 1 (by rfl) ⟨73922, by rfl⟩) R147845
theorem R131345 : Reach 131345 := rs (se 2 (by rfl) ⟨49254, by rfl⟩) R98509
theorem R131363 : Reach 131363 := rs (se 1 (by rfl) ⟨98522, by rfl⟩) R197045
theorem R295217 : Reach 295217 := rs (se 2 (by rfl) ⟨110706, by rfl⟩) R221413
theorem R131393 : Reach 131393 := rs (se 2 (by rfl) ⟨49272, by rfl⟩) R98545
theorem R131411 : Reach 131411 := rs (se 1 (by rfl) ⟨98558, by rfl⟩) R197117
theorem R459107 : Reach 459107 := rs (se 1 (by rfl) ⟨344330, by rfl⟩) R688661
theorem R131441 : Reach 131441 := rs (se 2 (by rfl) ⟨49290, by rfl⟩) R98581
theorem R131459 : Reach 131459 := rs (se 1 (by rfl) ⟨98594, by rfl⟩) R197189
theorem R197009 : Reach 197009 := rs (se 2 (by rfl) ⟨73878, by rfl⟩) R147757
theorem R98707 : Reach 98707 := rs (se 1 (by rfl) ⟨74030, by rfl⟩) R148061
theorem R131489 : Reach 131489 := rs (se 2 (by rfl) ⟨49308, by rfl⟩) R98617
theorem R197027 : Reach 197027 := rs (se 1 (by rfl) ⟨147770, by rfl⟩) R295541
theorem R131507 : Reach 131507 := rs (se 1 (by rfl) ⟨98630, by rfl⟩) R197261
theorem R131537 : Reach 131537 := rs (se 2 (by rfl) ⟨49326, by rfl⟩) R98653
theorem R131555 : Reach 131555 := rs (se 1 (by rfl) ⟨98666, by rfl⟩) R197333
theorem R131585 : Reach 131585 := rs (se 2 (by rfl) ⟨49344, by rfl⟩) R98689
theorem R131603 : Reach 131603 := rs (se 1 (by rfl) ⟨98702, by rfl⟩) R197405
theorem R98851 : Reach 98851 := rs (se 1 (by rfl) ⟨74138, by rfl⟩) R148277
theorem R131633 : Reach 131633 := rs (se 2 (by rfl) ⟨49362, by rfl⟩) R98725
theorem R131651 : Reach 131651 := rs (se 1 (by rfl) ⟨98738, by rfl⟩) R197477
theorem R131681 : Reach 131681 := rs (se 2 (by rfl) ⟨49380, by rfl⟩) R98761
theorem R131699 : Reach 131699 := rs (se 1 (by rfl) ⟨98774, by rfl⟩) R197549
theorem R131729 : Reach 131729 := rs (se 2 (by rfl) ⟨49398, by rfl⟩) R98797
theorem R131747 : Reach 131747 := rs (se 1 (by rfl) ⟨98810, by rfl⟩) R197621
theorem R197297 : Reach 197297 := rs (se 2 (by rfl) ⟨73986, by rfl⟩) R147973
theorem R98995 : Reach 98995 := rs (se 1 (by rfl) ⟨74246, by rfl⟩) R148493
theorem R131777 : Reach 131777 := rs (se 2 (by rfl) ⟨49416, by rfl⟩) R98833
theorem R197315 : Reach 197315 := rs (se 1 (by rfl) ⟨147986, by rfl⟩) R295973
theorem R131795 : Reach 131795 := rs (se 1 (by rfl) ⟨98846, by rfl⟩) R197693
theorem R131825 : Reach 131825 := rs (se 2 (by rfl) ⟨49434, by rfl⟩) R98869
theorem R131843 : Reach 131843 := rs (se 1 (by rfl) ⟨98882, by rfl⟩) R197765
theorem R230161 : Reach 230161 := rs (se 2 (by rfl) ⟨86310, by rfl⟩) R172621
theorem R131873 : Reach 131873 := rs (se 2 (by rfl) ⟨49452, by rfl⟩) R98905
theorem R131891 : Reach 131891 := rs (se 1 (by rfl) ⟨98918, by rfl⟩) R197837
theorem R99139 : Reach 99139 := rs (se 1 (by rfl) ⟨74354, by rfl⟩) R148709
theorem R295757 : Reach 295757 := rs (se 3 (by rfl) ⟨55454, by rfl⟩) R110909
theorem R131921 : Reach 131921 := rs (se 2 (by rfl) ⟨49470, by rfl⟩) R98941
theorem R131939 : Reach 131939 := rs (se 1 (by rfl) ⟨98954, by rfl⟩) R197909
theorem R131969 : Reach 131969 := rs (se 2 (by rfl) ⟨49488, by rfl⟩) R98977
theorem R295811 : Reach 295811 := rs (se 1 (by rfl) ⟨221858, by rfl⟩) R443717
theorem R131987 : Reach 131987 := rs (se 1 (by rfl) ⟨98990, by rfl⟩) R197981
theorem R164771 : Reach 164771 := rs (se 1 (by rfl) ⟨123578, by rfl⟩) R247157
theorem R132017 : Reach 132017 := rs (se 2 (by rfl) ⟨49506, by rfl⟩) R99013
theorem R132035 : Reach 132035 := rs (se 1 (by rfl) ⟨99026, by rfl⟩) R198053
theorem R1573829 : Reach 1573829 := rs (se 4 (by rfl) ⟨147546, by rfl⟩) R295093
theorem R197585 : Reach 197585 := rs (se 2 (by rfl) ⟨74094, by rfl⟩) R148189
theorem R99283 : Reach 99283 := rs (se 1 (by rfl) ⟨74462, by rfl⟩) R148925
theorem R132065 : Reach 132065 := rs (se 2 (by rfl) ⟨49524, by rfl⟩) R99049
theorem R197603 : Reach 197603 := rs (se 1 (by rfl) ⟨148202, by rfl⟩) R296405
theorem R132083 : Reach 132083 := rs (se 1 (by rfl) ⟨99062, by rfl⟩) R198125
theorem R132113 : Reach 132113 := rs (se 2 (by rfl) ⟨49542, by rfl⟩) R99085
theorem R132131 : Reach 132131 := rs (se 1 (by rfl) ⟨99098, by rfl⟩) R198197
theorem R230435 : Reach 230435 := rs (se 1 (by rfl) ⟨172826, by rfl⟩) R345653
theorem R132161 : Reach 132161 := rs (se 2 (by rfl) ⟨49560, by rfl⟩) R99121
theorem R754757 : Reach 754757 := rs (se 4 (by rfl) ⟨70758, by rfl⟩) R141517
theorem R132179 : Reach 132179 := rs (se 1 (by rfl) ⟨99134, by rfl⟩) R198269
theorem R99427 : Reach 99427 := rs (se 1 (by rfl) ⟨74570, by rfl⟩) R149141
theorem R132209 : Reach 132209 := rs (se 2 (by rfl) ⟨49578, by rfl⟩) R99157
theorem R132227 : Reach 132227 := rs (se 1 (by rfl) ⟨99170, by rfl⟩) R198341
theorem R459917 : Reach 459917 := rs (se 3 (by rfl) ⟨86234, by rfl⟩) R172469
theorem R296081 : Reach 296081 := rs (se 2 (by rfl) ⟨111030, by rfl⟩) R222061
theorem R132257 : Reach 132257 := rs (se 2 (by rfl) ⟨49596, by rfl⟩) R99193
theorem R132275 : Reach 132275 := rs (se 1 (by rfl) ⟨99206, by rfl⟩) R198413
theorem R132305 : Reach 132305 := rs (se 2 (by rfl) ⟨49614, by rfl⟩) R99229
theorem R132323 : Reach 132323 := rs (se 1 (by rfl) ⟨99242, by rfl⟩) R198485
theorem R230627 : Reach 230627 := rs (se 1 (by rfl) ⟨172970, by rfl⟩) R345941
theorem R197873 : Reach 197873 := rs (se 2 (by rfl) ⟨74202, by rfl⟩) R148405
theorem R99571 : Reach 99571 := rs (se 1 (by rfl) ⟨74678, by rfl⟩) R149357
theorem R132353 : Reach 132353 := rs (se 2 (by rfl) ⟨49632, by rfl⟩) R99265
theorem R197891 : Reach 197891 := rs (se 1 (by rfl) ⟨148418, by rfl⟩) R296837
theorem R132371 : Reach 132371 := rs (se 1 (by rfl) ⟨99278, by rfl⟩) R198557
theorem R132401 : Reach 132401 := rs (se 2 (by rfl) ⟨49650, by rfl⟩) R99301
theorem R132419 : Reach 132419 := rs (se 1 (by rfl) ⟨99314, by rfl⟩) R198629
theorem R165187 : Reach 165187 := rs (se 1 (by rfl) ⟨123890, by rfl⟩) R247781
theorem R132449 : Reach 132449 := rs (se 2 (by rfl) ⟨49668, by rfl⟩) R99337
theorem R132467 : Reach 132467 := rs (se 1 (by rfl) ⟨99350, by rfl⟩) R198701
theorem R99715 : Reach 99715 := rs (se 1 (by rfl) ⟨74786, by rfl⟩) R149573
theorem R132497 : Reach 132497 := rs (se 2 (by rfl) ⟨49686, by rfl⟩) R99373
theorem R132515 : Reach 132515 := rs (se 1 (by rfl) ⟨99386, by rfl⟩) R198773
theorem R132545 : Reach 132545 := rs (se 2 (by rfl) ⟨49704, by rfl⟩) R99409
theorem R132563 : Reach 132563 := rs (se 1 (by rfl) ⟨99422, by rfl⟩) R198845
theorem R132593 : Reach 132593 := rs (se 2 (by rfl) ⟨49722, by rfl⟩) R99445
theorem R132611 : Reach 132611 := rs (se 1 (by rfl) ⟨99458, by rfl⟩) R198917
theorem R198161 : Reach 198161 := rs (se 2 (by rfl) ⟨74310, by rfl⟩) R148621
theorem R99859 : Reach 99859 := rs (se 1 (by rfl) ⟨74894, by rfl⟩) R149789
theorem R132641 : Reach 132641 := rs (se 2 (by rfl) ⟨49740, by rfl⟩) R99481
theorem R198179 : Reach 198179 := rs (se 1 (by rfl) ⟨148634, by rfl⟩) R297269
theorem R132659 : Reach 132659 := rs (se 1 (by rfl) ⟨99494, by rfl⟩) R198989
theorem R132689 : Reach 132689 := rs (se 2 (by rfl) ⟨49758, by rfl⟩) R99517
theorem R132707 : Reach 132707 := rs (se 1 (by rfl) ⟨99530, by rfl⟩) R199061
theorem R132737 : Reach 132737 := rs (se 2 (by rfl) ⟨49776, by rfl⟩) R99553
theorem R132755 : Reach 132755 := rs (se 1 (by rfl) ⟨99566, by rfl⟩) R199133
theorem R100003 : Reach 100003 := rs (se 1 (by rfl) ⟨75002, by rfl⟩) R150005
theorem R296621 : Reach 296621 := rs (se 3 (by rfl) ⟨55616, by rfl⟩) R111233
theorem R132785 : Reach 132785 := rs (se 2 (by rfl) ⟨49794, by rfl⟩) R99589
theorem R132803 : Reach 132803 := rs (se 1 (by rfl) ⟨99602, by rfl⟩) R199205
theorem R132833 : Reach 132833 := rs (se 2 (by rfl) ⟨49812, by rfl⟩) R99625
theorem R296675 : Reach 296675 := rs (se 1 (by rfl) ⟨222506, by rfl⟩) R445013
theorem R689905 : Reach 689905 := rs (se 2 (by rfl) ⟨258714, by rfl⟩) R517429
theorem R132851 : Reach 132851 := rs (se 1 (by rfl) ⟨99638, by rfl⟩) R199277
theorem R165635 : Reach 165635 := rs (se 1 (by rfl) ⟨124226, by rfl⟩) R248453
theorem R132881 : Reach 132881 := rs (se 2 (by rfl) ⟨49830, by rfl⟩) R99661
theorem R132899 : Reach 132899 := rs (se 1 (by rfl) ⟨99674, by rfl⟩) R199349
theorem R198449 : Reach 198449 := rs (se 2 (by rfl) ⟨74418, by rfl⟩) R148837
theorem R100147 : Reach 100147 := rs (se 1 (by rfl) ⟨75110, by rfl⟩) R150221
theorem R132929 : Reach 132929 := rs (se 2 (by rfl) ⟨49848, by rfl⟩) R99697
theorem R198467 : Reach 198467 := rs (se 1 (by rfl) ⟨148850, by rfl⟩) R297701
theorem R132947 : Reach 132947 := rs (se 1 (by rfl) ⟨99710, by rfl⟩) R199421
theorem R132977 : Reach 132977 := rs (se 2 (by rfl) ⟨49866, by rfl⟩) R99733
theorem R132995 : Reach 132995 := rs (se 1 (by rfl) ⟨99746, by rfl⟩) R199493
theorem R133025 : Reach 133025 := rs (se 2 (by rfl) ⟨49884, by rfl⟩) R99769
theorem R133043 : Reach 133043 := rs (se 1 (by rfl) ⟨99782, by rfl⟩) R199565
theorem R100291 : Reach 100291 := rs (se 1 (by rfl) ⟨75218, by rfl⟩) R150437
theorem R133073 : Reach 133073 := rs (se 2 (by rfl) ⟨49902, by rfl⟩) R99805
theorem R133091 : Reach 133091 := rs (se 1 (by rfl) ⟨99818, by rfl⟩) R199637
theorem R264173 : Reach 264173 := rs (se 3 (by rfl) ⟨49532, by rfl⟩) R99065
theorem R296945 : Reach 296945 := rs (se 2 (by rfl) ⟨111354, by rfl⟩) R222709
theorem R133121 : Reach 133121 := rs (se 2 (by rfl) ⟨49920, by rfl⟩) R99841
theorem R133139 : Reach 133139 := rs (se 1 (by rfl) ⟨99854, by rfl⟩) R199709
theorem R133169 : Reach 133169 := rs (se 2 (by rfl) ⟨49938, by rfl⟩) R99877
theorem R133187 : Reach 133187 := rs (se 1 (by rfl) ⟨99890, by rfl⟩) R199781
theorem R198737 : Reach 198737 := rs (se 2 (by rfl) ⟨74526, by rfl⟩) R149053
theorem R100435 : Reach 100435 := rs (se 1 (by rfl) ⟨75326, by rfl⟩) R150653
theorem R133217 : Reach 133217 := rs (se 2 (by rfl) ⟨49956, by rfl⟩) R99913
theorem R198755 : Reach 198755 := rs (se 1 (by rfl) ⟨149066, by rfl⟩) R298133
theorem R133235 : Reach 133235 := rs (se 1 (by rfl) ⟨99926, by rfl⟩) R199853
theorem R133265 : Reach 133265 := rs (se 2 (by rfl) ⟨49974, by rfl⟩) R99949
theorem R133283 : Reach 133283 := rs (se 1 (by rfl) ⟨99962, by rfl⟩) R199925
theorem R133313 : Reach 133313 := rs (se 2 (by rfl) ⟨49992, by rfl⟩) R99985
theorem R133331 : Reach 133331 := rs (se 1 (by rfl) ⟨99998, by rfl⟩) R199997
theorem R100579 : Reach 100579 := rs (se 1 (by rfl) ⟨75434, by rfl⟩) R150869
theorem R133361 : Reach 133361 := rs (se 2 (by rfl) ⟨50010, by rfl⟩) R100021
theorem R133379 : Reach 133379 := rs (se 1 (by rfl) ⟨100034, by rfl⟩) R200069
theorem R133409 : Reach 133409 := rs (se 2 (by rfl) ⟨50028, by rfl⟩) R100057
theorem R133427 : Reach 133427 := rs (se 1 (by rfl) ⟨100070, by rfl⟩) R200141
theorem R133457 : Reach 133457 := rs (se 2 (by rfl) ⟨50046, by rfl⟩) R100093
theorem R133475 : Reach 133475 := rs (se 1 (by rfl) ⟨100106, by rfl⟩) R200213
theorem R199025 : Reach 199025 := rs (se 2 (by rfl) ⟨74634, by rfl⟩) R149269
theorem R100723 : Reach 100723 := rs (se 1 (by rfl) ⟨75542, by rfl⟩) R151085
theorem R133505 : Reach 133505 := rs (se 2 (by rfl) ⟨50064, by rfl⟩) R100129
theorem R199043 : Reach 199043 := rs (se 1 (by rfl) ⟨149282, by rfl⟩) R298565
theorem R133523 : Reach 133523 := rs (se 1 (by rfl) ⟨100142, by rfl⟩) R200285
theorem R133553 : Reach 133553 := rs (se 2 (by rfl) ⟨50082, by rfl⟩) R100165
theorem R133571 : Reach 133571 := rs (se 1 (by rfl) ⟨100178, by rfl⟩) R200357
theorem R133601 : Reach 133601 := rs (se 2 (by rfl) ⟨50100, by rfl⟩) R100201
theorem R133619 : Reach 133619 := rs (se 1 (by rfl) ⟨100214, by rfl⟩) R200429
theorem R100867 : Reach 100867 := rs (se 1 (by rfl) ⟨75650, by rfl⟩) R151301
theorem R297485 : Reach 297485 := rs (se 3 (by rfl) ⟨55778, by rfl⟩) R111557
theorem R133649 : Reach 133649 := rs (se 2 (by rfl) ⟨50118, by rfl⟩) R100237
theorem R133667 : Reach 133667 := rs (se 1 (by rfl) ⟨100250, by rfl⟩) R200501
theorem R133697 : Reach 133697 := rs (se 2 (by rfl) ⟨50136, by rfl⟩) R100273
theorem R297539 : Reach 297539 := rs (se 1 (by rfl) ⟨223154, by rfl⟩) R446309
theorem R133715 : Reach 133715 := rs (se 1 (by rfl) ⟨100286, by rfl⟩) R200573
theorem R133745 : Reach 133745 := rs (se 2 (by rfl) ⟨50154, by rfl⟩) R100309
theorem R166531 : Reach 166531 := rs (se 1 (by rfl) ⟨124898, by rfl⟩) R249797
theorem R133763 : Reach 133763 := rs (se 1 (by rfl) ⟨100322, by rfl⟩) R200645
theorem R199313 : Reach 199313 := rs (se 2 (by rfl) ⟨74742, by rfl⟩) R149485
theorem R101011 : Reach 101011 := rs (se 1 (by rfl) ⟨75758, by rfl⟩) R151517
theorem R133793 : Reach 133793 := rs (se 2 (by rfl) ⟨50172, by rfl⟩) R100345
theorem R199331 : Reach 199331 := rs (se 1 (by rfl) ⟨149498, by rfl⟩) R298997
theorem R133811 : Reach 133811 := rs (se 1 (by rfl) ⟨100358, by rfl⟩) R200717
theorem R133841 : Reach 133841 := rs (se 2 (by rfl) ⟨50190, by rfl⟩) R100381
theorem R133859 : Reach 133859 := rs (se 1 (by rfl) ⟨100394, by rfl⟩) R200789
theorem R133889 : Reach 133889 := rs (se 2 (by rfl) ⟨50208, by rfl⟩) R100417
theorem R133907 : Reach 133907 := rs (se 1 (by rfl) ⟨100430, by rfl⟩) R200861
theorem R166691 : Reach 166691 := rs (se 1 (by rfl) ⟨125018, by rfl⟩) R250037
theorem R101155 : Reach 101155 := rs (se 1 (by rfl) ⟨75866, by rfl⟩) R151733
theorem R133937 : Reach 133937 := rs (se 2 (by rfl) ⟨50226, by rfl⟩) R100453
theorem R133955 : Reach 133955 := rs (se 1 (by rfl) ⟨100466, by rfl⟩) R200933
theorem R297809 : Reach 297809 := rs (se 2 (by rfl) ⟨111678, by rfl⟩) R223357
theorem R133985 : Reach 133985 := rs (se 2 (by rfl) ⟨50244, by rfl⟩) R100489
theorem R134003 : Reach 134003 := rs (se 1 (by rfl) ⟨100502, by rfl⟩) R201005
theorem R134033 : Reach 134033 := rs (se 2 (by rfl) ⟨50262, by rfl⟩) R100525
theorem R134051 : Reach 134051 := rs (se 1 (by rfl) ⟨100538, by rfl⟩) R201077
theorem R199601 : Reach 199601 := rs (se 2 (by rfl) ⟨74850, by rfl⟩) R149701
theorem R101299 : Reach 101299 := rs (se 1 (by rfl) ⟨75974, by rfl⟩) R151949
theorem R134081 : Reach 134081 := rs (se 2 (by rfl) ⟨50280, by rfl⟩) R100561
theorem R199619 : Reach 199619 := rs (se 1 (by rfl) ⟨149714, by rfl⟩) R299429
theorem R854981 : Reach 854981 := rs (se 4 (by rfl) ⟨80154, by rfl⟩) R160309
theorem R134099 : Reach 134099 := rs (se 1 (by rfl) ⟨100574, by rfl⟩) R201149
theorem R134129 : Reach 134129 := rs (se 2 (by rfl) ⟨50298, by rfl⟩) R100597
theorem R134147 : Reach 134147 := rs (se 1 (by rfl) ⟨100610, by rfl⟩) R201221
theorem R134177 : Reach 134177 := rs (se 2 (by rfl) ⟨50316, by rfl⟩) R100633
theorem R232483 : Reach 232483 := rs (se 1 (by rfl) ⟨174362, by rfl⟩) R348725
theorem R134195 : Reach 134195 := rs (se 1 (by rfl) ⟨100646, by rfl⟩) R201293
theorem R101443 : Reach 101443 := rs (se 1 (by rfl) ⟨76082, by rfl⟩) R152165
theorem R134225 : Reach 134225 := rs (se 2 (by rfl) ⟨50334, by rfl⟩) R100669
theorem R134243 : Reach 134243 := rs (se 1 (by rfl) ⟨100682, by rfl⟩) R201365
theorem R134273 : Reach 134273 := rs (se 2 (by rfl) ⟨50352, by rfl⟩) R100705
theorem R134291 : Reach 134291 := rs (se 1 (by rfl) ⟨100718, by rfl⟩) R201437
theorem R134321 : Reach 134321 := rs (se 2 (by rfl) ⟨50370, by rfl⟩) R100741
theorem R134339 : Reach 134339 := rs (se 1 (by rfl) ⟨100754, by rfl⟩) R201509
theorem R199889 : Reach 199889 := rs (se 2 (by rfl) ⟨74958, by rfl⟩) R149917
theorem R101587 : Reach 101587 := rs (se 1 (by rfl) ⟨76190, by rfl⟩) R152381
theorem R134369 : Reach 134369 := rs (se 2 (by rfl) ⟨50388, by rfl⟩) R100777
theorem R199907 : Reach 199907 := rs (se 1 (by rfl) ⟨149930, by rfl⟩) R299861
theorem R1969379 : Reach 1969379 := rs (se 1 (by rfl) ⟨1477034, by rfl⟩) R2954069
theorem R134387 : Reach 134387 := rs (se 1 (by rfl) ⟨100790, by rfl⟩) R201581
theorem R134417 : Reach 134417 := rs (se 2 (by rfl) ⟨50406, by rfl⟩) R100813
theorem R134435 : Reach 134435 := rs (se 1 (by rfl) ⟨100826, by rfl⟩) R201653
theorem R134465 : Reach 134465 := rs (se 2 (by rfl) ⟨50424, by rfl⟩) R100849
theorem R134483 : Reach 134483 := rs (se 1 (by rfl) ⟨100862, by rfl⟩) R201725
theorem R101731 : Reach 101731 := rs (se 1 (by rfl) ⟨76298, by rfl⟩) R152597
theorem R298349 : Reach 298349 := rs (se 3 (by rfl) ⟨55940, by rfl⟩) R111881
theorem R134513 : Reach 134513 := rs (se 2 (by rfl) ⟨50442, by rfl⟩) R100885
theorem R134531 : Reach 134531 := rs (se 1 (by rfl) ⟨100898, by rfl⟩) R201797
theorem R134561 : Reach 134561 := rs (se 2 (by rfl) ⟨50460, by rfl⟩) R100921
theorem R298403 : Reach 298403 := rs (se 1 (by rfl) ⟨223802, by rfl⟩) R447605
theorem R134579 : Reach 134579 := rs (se 1 (by rfl) ⟨100934, by rfl⟩) R201869
theorem R134609 : Reach 134609 := rs (se 2 (by rfl) ⟨50478, by rfl⟩) R100957
theorem R134627 : Reach 134627 := rs (se 1 (by rfl) ⟨100970, by rfl⟩) R201941
theorem R200177 : Reach 200177 := rs (se 2 (by rfl) ⟨75066, by rfl⟩) R150133
theorem R1084913 : Reach 1084913 := rs (se 2 (by rfl) ⟨406842, by rfl⟩) R813685
theorem R101875 : Reach 101875 := rs (se 1 (by rfl) ⟨76406, by rfl⟩) R152813
theorem R134657 : Reach 134657 := rs (se 2 (by rfl) ⟨50496, by rfl⟩) R100993
theorem R200195 : Reach 200195 := rs (se 1 (by rfl) ⟨150146, by rfl⟩) R300293
theorem R134675 : Reach 134675 := rs (se 1 (by rfl) ⟨101006, by rfl⟩) R202013
theorem R134705 : Reach 134705 := rs (se 2 (by rfl) ⟨50514, by rfl⟩) R101029
theorem R134723 : Reach 134723 := rs (se 1 (by rfl) ⟨101042, by rfl⟩) R202085
theorem R134753 : Reach 134753 := rs (se 2 (by rfl) ⟨50532, by rfl⟩) R101065
theorem R134771 : Reach 134771 := rs (se 1 (by rfl) ⟨101078, by rfl⟩) R202157
theorem R102019 : Reach 102019 := rs (se 1 (by rfl) ⟨76514, by rfl⟩) R153029
theorem R134801 : Reach 134801 := rs (se 2 (by rfl) ⟨50550, by rfl⟩) R101101
theorem R134819 : Reach 134819 := rs (se 1 (by rfl) ⟨101114, by rfl⟩) R202229
theorem R298673 : Reach 298673 := rs (se 2 (by rfl) ⟨112002, by rfl⟩) R224005
theorem R134849 : Reach 134849 := rs (se 2 (by rfl) ⟨50568, by rfl⟩) R101137
theorem R134867 : Reach 134867 := rs (se 1 (by rfl) ⟨101150, by rfl⟩) R202301
theorem R134897 : Reach 134897 := rs (se 2 (by rfl) ⟨50586, by rfl⟩) R101173
theorem R134915 : Reach 134915 := rs (se 1 (by rfl) ⟨101186, by rfl⟩) R202373
theorem R200465 : Reach 200465 := rs (se 2 (by rfl) ⟨75174, by rfl⟩) R150349
theorem R102163 : Reach 102163 := rs (se 1 (by rfl) ⟨76622, by rfl⟩) R153245
theorem R134945 : Reach 134945 := rs (se 2 (by rfl) ⟨50604, by rfl⟩) R101209
theorem R200483 : Reach 200483 := rs (se 1 (by rfl) ⟨150362, by rfl⟩) R300725
theorem R134963 : Reach 134963 := rs (se 1 (by rfl) ⟨101222, by rfl⟩) R202445
theorem R167761 : Reach 167761 := rs (se 2 (by rfl) ⟨62910, by rfl⟩) R125821
theorem R134993 : Reach 134993 := rs (se 2 (by rfl) ⟨50622, by rfl⟩) R101245
theorem R135011 : Reach 135011 := rs (se 1 (by rfl) ⟨101258, by rfl⟩) R202517
theorem R135041 : Reach 135041 := rs (se 2 (by rfl) ⟨50640, by rfl⟩) R101281
theorem R135059 : Reach 135059 := rs (se 1 (by rfl) ⟨101294, by rfl⟩) R202589
theorem R102307 : Reach 102307 := rs (se 1 (by rfl) ⟨76730, by rfl⟩) R153461
theorem R135089 : Reach 135089 := rs (se 2 (by rfl) ⟨50658, by rfl⟩) R101317
theorem R135107 : Reach 135107 := rs (se 1 (by rfl) ⟨101330, by rfl⟩) R202661
theorem R135137 : Reach 135137 := rs (se 2 (by rfl) ⟨50676, by rfl⟩) R101353
theorem R135155 : Reach 135155 := rs (se 1 (by rfl) ⟨101366, by rfl⟩) R202733
theorem R135185 : Reach 135185 := rs (se 2 (by rfl) ⟨50694, by rfl⟩) R101389
theorem R135203 : Reach 135203 := rs (se 1 (by rfl) ⟨101402, by rfl⟩) R202805
theorem R200753 : Reach 200753 := rs (se 2 (by rfl) ⟨75282, by rfl⟩) R150565
theorem R102451 : Reach 102451 := rs (se 1 (by rfl) ⟨76838, by rfl⟩) R153677
theorem R135233 : Reach 135233 := rs (se 2 (by rfl) ⟨50712, by rfl⟩) R101425
theorem R200771 : Reach 200771 := rs (se 1 (by rfl) ⟨150578, by rfl⟩) R301157
theorem R135251 : Reach 135251 := rs (se 1 (by rfl) ⟨101438, by rfl⟩) R202877
theorem R135281 : Reach 135281 := rs (se 2 (by rfl) ⟨50730, by rfl⟩) R101461
theorem R135299 : Reach 135299 := rs (se 1 (by rfl) ⟨101474, by rfl⟩) R202949
theorem R135329 : Reach 135329 := rs (se 2 (by rfl) ⟨50748, by rfl⟩) R101497
theorem R135347 : Reach 135347 := rs (se 1 (by rfl) ⟨101510, by rfl⟩) R203021
theorem R299213 : Reach 299213 := rs (se 3 (by rfl) ⟨56102, by rfl⟩) R112205
theorem R135377 : Reach 135377 := rs (se 2 (by rfl) ⟨50766, by rfl⟩) R101533
theorem R135395 : Reach 135395 := rs (se 1 (by rfl) ⟨101546, by rfl⟩) R203093
theorem R135425 : Reach 135425 := rs (se 2 (by rfl) ⟨50784, by rfl⟩) R101569
theorem R299267 : Reach 299267 := rs (se 1 (by rfl) ⟨224450, by rfl⟩) R448901
theorem R332045 : Reach 332045 := rs (se 3 (by rfl) ⟨62258, by rfl⟩) R124517
theorem R135443 : Reach 135443 := rs (se 1 (by rfl) ⟨101582, by rfl⟩) R203165
theorem R135473 : Reach 135473 := rs (se 2 (by rfl) ⟨50802, by rfl⟩) R101605
theorem R135491 : Reach 135491 := rs (se 1 (by rfl) ⟨101618, by rfl⟩) R203237
theorem R201041 : Reach 201041 := rs (se 2 (by rfl) ⟨75390, by rfl⟩) R150781
theorem R135521 : Reach 135521 := rs (se 2 (by rfl) ⟨50820, by rfl⟩) R101641
theorem R201059 : Reach 201059 := rs (se 1 (by rfl) ⟨150794, by rfl⟩) R301589
theorem R135539 : Reach 135539 := rs (se 1 (by rfl) ⟨101654, by rfl⟩) R203309
theorem R135569 : Reach 135569 := rs (se 2 (by rfl) ⟨50838, by rfl⟩) R101677
theorem R135587 : Reach 135587 := rs (se 1 (by rfl) ⟨101690, by rfl⟩) R203381
theorem R135617 : Reach 135617 := rs (se 2 (by rfl) ⟨50856, by rfl⟩) R101713
theorem R135635 : Reach 135635 := rs (se 1 (by rfl) ⟨101726, by rfl⟩) R203453
theorem R135665 : Reach 135665 := rs (se 2 (by rfl) ⟨50874, by rfl⟩) R101749
theorem R135683 : Reach 135683 := rs (se 1 (by rfl) ⟨101762, by rfl⟩) R203525
theorem R299537 : Reach 299537 := rs (se 2 (by rfl) ⟨112326, by rfl⟩) R224653
theorem R135713 : Reach 135713 := rs (se 2 (by rfl) ⟨50892, by rfl⟩) R101785
theorem R135731 : Reach 135731 := rs (se 1 (by rfl) ⟨101798, by rfl⟩) R203597
theorem R102979 : Reach 102979 := rs (se 1 (by rfl) ⟨77234, by rfl⟩) R154469
theorem R135761 : Reach 135761 := rs (se 2 (by rfl) ⟨50910, by rfl⟩) R101821
theorem R135779 : Reach 135779 := rs (se 1 (by rfl) ⟨101834, by rfl⟩) R203669
theorem R201329 : Reach 201329 := rs (se 2 (by rfl) ⟨75498, by rfl⟩) R150997
theorem R135809 : Reach 135809 := rs (se 2 (by rfl) ⟨50928, by rfl⟩) R101857
theorem R201347 : Reach 201347 := rs (se 1 (by rfl) ⟨151010, by rfl⟩) R302021
theorem R135827 : Reach 135827 := rs (se 1 (by rfl) ⟨101870, by rfl⟩) R203741
theorem R135857 : Reach 135857 := rs (se 2 (by rfl) ⟨50946, by rfl⟩) R101893
theorem R135875 : Reach 135875 := rs (se 1 (by rfl) ⟨101906, by rfl⟩) R203813
theorem R135905 : Reach 135905 := rs (se 2 (by rfl) ⟨50964, by rfl⟩) R101929
theorem R135923 : Reach 135923 := rs (se 1 (by rfl) ⟨101942, by rfl⟩) R203885
theorem R135953 : Reach 135953 := rs (se 2 (by rfl) ⟨50982, by rfl⟩) R101965
theorem R135971 : Reach 135971 := rs (se 1 (by rfl) ⟨101978, by rfl⟩) R203957
theorem R136001 : Reach 136001 := rs (se 2 (by rfl) ⟨51000, by rfl⟩) R102001
theorem R136019 : Reach 136019 := rs (se 1 (by rfl) ⟨102014, by rfl⟩) R204029
theorem R463715 : Reach 463715 := rs (se 1 (by rfl) ⟨347786, by rfl⟩) R695573
theorem R168817 : Reach 168817 := rs (se 2 (by rfl) ⟨63306, by rfl⟩) R126613
theorem R136049 : Reach 136049 := rs (se 2 (by rfl) ⟨51018, by rfl⟩) R102037
theorem R136067 : Reach 136067 := rs (se 1 (by rfl) ⟨102050, by rfl⟩) R204101
theorem R201617 : Reach 201617 := rs (se 2 (by rfl) ⟨75606, by rfl⟩) R151213
theorem R136097 : Reach 136097 := rs (se 2 (by rfl) ⟨51036, by rfl⟩) R102073
theorem R201635 : Reach 201635 := rs (se 1 (by rfl) ⟨151226, by rfl⟩) R302453
theorem R136115 : Reach 136115 := rs (se 1 (by rfl) ⟨102086, by rfl⟩) R204173
theorem R136145 : Reach 136145 := rs (se 2 (by rfl) ⟨51054, by rfl⟩) R102109
theorem R136163 : Reach 136163 := rs (se 1 (by rfl) ⟨102122, by rfl⟩) R204245
theorem R136193 : Reach 136193 := rs (se 2 (by rfl) ⟨51072, by rfl⟩) R102145
theorem R136211 : Reach 136211 := rs (se 1 (by rfl) ⟨102158, by rfl⟩) R204317
theorem R300077 : Reach 300077 := rs (se 3 (by rfl) ⟨56264, by rfl⟩) R112529
theorem R332849 : Reach 332849 := rs (se 2 (by rfl) ⟨124818, by rfl⟩) R249637
theorem R136241 : Reach 136241 := rs (se 2 (by rfl) ⟨51090, by rfl⟩) R102181
theorem R136259 : Reach 136259 := rs (se 1 (by rfl) ⟨102194, by rfl⟩) R204389
theorem R136289 : Reach 136289 := rs (se 2 (by rfl) ⟨51108, by rfl⟩) R102217
theorem R300131 : Reach 300131 := rs (se 1 (by rfl) ⟨225098, by rfl⟩) R450197
theorem R136307 : Reach 136307 := rs (se 1 (by rfl) ⟨102230, by rfl⟩) R204461
theorem R136337 : Reach 136337 := rs (se 2 (by rfl) ⟨51126, by rfl⟩) R102253
theorem R234659 : Reach 234659 := rs (se 1 (by rfl) ⟨175994, by rfl⟩) R351989
theorem R136355 : Reach 136355 := rs (se 1 (by rfl) ⟨102266, by rfl⟩) R204533
theorem R201905 : Reach 201905 := rs (se 2 (by rfl) ⟨75714, by rfl⟩) R151429
theorem R136385 : Reach 136385 := rs (se 2 (by rfl) ⟨51144, by rfl⟩) R102289
theorem R201923 : Reach 201923 := rs (se 1 (by rfl) ⟨151442, by rfl⟩) R302885
theorem R136403 : Reach 136403 := rs (se 1 (by rfl) ⟨102302, by rfl⟩) R204605
theorem R136417 : Reach 136417 := rs (se 2 (by rfl) ⟨51156, by rfl⟩) R102313
theorem R136433 : Reach 136433 := rs (se 2 (by rfl) ⟨51162, by rfl⟩) R102325
theorem R169219 : Reach 169219 := rs (se 1 (by rfl) ⟨126914, by rfl⟩) R253829
theorem R136451 : Reach 136451 := rs (se 1 (by rfl) ⟨102338, by rfl⟩) R204677
theorem R267533 : Reach 267533 := rs (se 3 (by rfl) ⟨50162, by rfl⟩) R100325
theorem R136481 : Reach 136481 := rs (se 2 (by rfl) ⟨51180, by rfl⟩) R102361
theorem R169265 : Reach 169265 := rs (se 2 (by rfl) ⟨63474, by rfl⟩) R126949
theorem R136499 : Reach 136499 := rs (se 1 (by rfl) ⟨102374, by rfl⟩) R204749
theorem R136529 : Reach 136529 := rs (se 2 (by rfl) ⟨51198, by rfl⟩) R102397
theorem R136547 : Reach 136547 := rs (se 1 (by rfl) ⟨102410, by rfl⟩) R204821
theorem R300401 : Reach 300401 := rs (se 2 (by rfl) ⟨112650, by rfl⟩) R225301
theorem R136577 : Reach 136577 := rs (se 2 (by rfl) ⟨51216, by rfl⟩) R102433
theorem R136595 : Reach 136595 := rs (se 1 (by rfl) ⟨102446, by rfl⟩) R204893
theorem R136625 : Reach 136625 := rs (se 2 (by rfl) ⟨51234, by rfl⟩) R102469
theorem R136643 : Reach 136643 := rs (se 1 (by rfl) ⟨102482, by rfl⟩) R204965
theorem R300493 : Reach 300493 := rs (se 3 (by rfl) ⟨56342, by rfl⟩) R112685
theorem R202193 : Reach 202193 := rs (se 2 (by rfl) ⟨75822, by rfl⟩) R151645
theorem R136673 : Reach 136673 := rs (se 2 (by rfl) ⟨51252, by rfl⟩) R102505
theorem R202211 : Reach 202211 := rs (se 1 (by rfl) ⟨151658, by rfl⟩) R303317
theorem R136691 : Reach 136691 := rs (se 1 (by rfl) ⟨102518, by rfl⟩) R205037
theorem R169553 : Reach 169553 := rs (se 2 (by rfl) ⟨63582, by rfl⟩) R127165
theorem R136819 : Reach 136819 := rs (se 1 (by rfl) ⟨102614, by rfl⟩) R205229
theorem R333517 : Reach 333517 := rs (se 3 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R300781 : Reach 300781 := rs (se 3 (by rfl) ⟨56396, by rfl⟩) R112793
theorem R202481 : Reach 202481 := rs (se 2 (by rfl) ⟨75930, by rfl⟩) R151861
theorem R694001 : Reach 694001 := rs (se 2 (by rfl) ⟨260250, by rfl⟩) R520501
theorem R202499 : Reach 202499 := rs (se 1 (by rfl) ⟨151874, by rfl⟩) R303749
theorem R464717 : Reach 464717 := rs (se 3 (by rfl) ⟨87134, by rfl⟩) R174269
theorem R300941 : Reach 300941 := rs (se 3 (by rfl) ⟨56426, by rfl⟩) R112853
theorem R300995 : Reach 300995 := rs (se 1 (by rfl) ⟨225746, by rfl⟩) R451493
theorem R759779 : Reach 759779 := rs (se 1 (by rfl) ⟨569834, by rfl⟩) R1139669
theorem R202769 : Reach 202769 := rs (se 2 (by rfl) ⟨76038, by rfl⟩) R152077
theorem R202787 : Reach 202787 := rs (se 1 (by rfl) ⟨152090, by rfl⟩) R304181
theorem R301265 : Reach 301265 := rs (se 2 (by rfl) ⟨112974, by rfl⟩) R225949
theorem R170275 : Reach 170275 := rs (se 1 (by rfl) ⟨127706, by rfl⟩) R255413
theorem R203057 : Reach 203057 := rs (se 2 (by rfl) ⟨76146, by rfl⟩) R152293
theorem R203075 : Reach 203075 := rs (se 1 (by rfl) ⟨152306, by rfl⟩) R304613
theorem R334307 : Reach 334307 := rs (se 1 (by rfl) ⟨250730, by rfl⟩) R501461
theorem R268771 : Reach 268771 := rs (se 1 (by rfl) ⟨201578, by rfl⟩) R403157
theorem R203249 : Reach 203249 := rs (se 2 (by rfl) ⟨76218, by rfl⟩) R152437
theorem R203345 : Reach 203345 := rs (se 2 (by rfl) ⟨76254, by rfl⟩) R152509
theorem R203363 : Reach 203363 := rs (se 1 (by rfl) ⟨152522, by rfl⟩) R305045
theorem R694925 : Reach 694925 := rs (se 3 (by rfl) ⟨130298, by rfl⟩) R260597
theorem R170723 : Reach 170723 := rs (se 1 (by rfl) ⟨128042, by rfl⟩) R256085
theorem R301805 : Reach 301805 := rs (se 3 (by rfl) ⟨56588, by rfl⟩) R113177
theorem R301859 : Reach 301859 := rs (se 1 (by rfl) ⟨226394, by rfl⟩) R452789
theorem R138083 : Reach 138083 := rs (se 1 (by rfl) ⟨103562, by rfl⟩) R207125
theorem R498545 : Reach 498545 := rs (se 2 (by rfl) ⟨186954, by rfl⟩) R373909
theorem R203633 : Reach 203633 := rs (se 2 (by rfl) ⟨76362, by rfl⟩) R152725
theorem R203651 : Reach 203651 := rs (se 1 (by rfl) ⟨152738, by rfl⟩) R305477
theorem R171011 : Reach 171011 := rs (se 1 (by rfl) ⟨128258, by rfl⟩) R256517
theorem R302129 : Reach 302129 := rs (se 2 (by rfl) ⟨113298, by rfl⟩) R226597
theorem R138323 : Reach 138323 := rs (se 1 (by rfl) ⟨103742, by rfl⟩) R207485
theorem R334961 : Reach 334961 := rs (se 2 (by rfl) ⟨125610, by rfl⟩) R251221
theorem R203921 : Reach 203921 := rs (se 2 (by rfl) ⟨76470, by rfl⟩) R152941
theorem R203939 : Reach 203939 := rs (se 1 (by rfl) ⟨152954, by rfl⟩) R305909
theorem R171281 : Reach 171281 := rs (se 2 (by rfl) ⟨64230, by rfl⟩) R128461
theorem R499121 : Reach 499121 := rs (se 2 (by rfl) ⟨187170, by rfl⟩) R374341
theorem R204209 : Reach 204209 := rs (se 2 (by rfl) ⟨76578, by rfl⟩) R153157
theorem R204227 : Reach 204227 := rs (se 1 (by rfl) ⟨153170, by rfl⟩) R306341
theorem R368077 : Reach 368077 := rs (se 3 (by rfl) ⟨69014, by rfl⟩) R138029
theorem R302669 : Reach 302669 := rs (se 3 (by rfl) ⟨56750, by rfl⟩) R113501
theorem R302723 : Reach 302723 := rs (se 1 (by rfl) ⟨227042, by rfl⟩) R454085
theorem R171683 : Reach 171683 := rs (se 1 (by rfl) ⟨128762, by rfl⟩) R257525
theorem R204497 : Reach 204497 := rs (se 2 (by rfl) ⟨76686, by rfl⟩) R153373
theorem R204515 : Reach 204515 := rs (se 1 (by rfl) ⟨153386, by rfl⟩) R306773
theorem R270125 : Reach 270125 := rs (se 3 (by rfl) ⟨50648, by rfl⟩) R101297
theorem R204643 : Reach 204643 := rs (se 1 (by rfl) ⟨153482, by rfl⟩) R306965
theorem R302993 : Reach 302993 := rs (se 2 (by rfl) ⟨113622, by rfl⟩) R227245
theorem R171953 : Reach 171953 := rs (se 2 (by rfl) ⟨64482, by rfl⟩) R128965
theorem R204785 : Reach 204785 := rs (se 2 (by rfl) ⟨76794, by rfl⟩) R153589
theorem R204803 : Reach 204803 := rs (se 1 (by rfl) ⟨153602, by rfl⟩) R307205
theorem R565325 : Reach 565325 := rs (se 3 (by rfl) ⟨105998, by rfl⟩) R211997
theorem R500003 : Reach 500003 := rs (se 1 (by rfl) ⟨375002, by rfl⟩) R750005
theorem R139601 : Reach 139601 := rs (se 2 (by rfl) ⟨52350, by rfl⟩) R104701
theorem R303533 : Reach 303533 := rs (se 3 (by rfl) ⟨56912, by rfl⟩) R113825
theorem R139729 : Reach 139729 := rs (se 2 (by rfl) ⟨52398, by rfl⟩) R104797
theorem R303587 : Reach 303587 := rs (se 1 (by rfl) ⟨227690, by rfl⟩) R455381
theorem R303601 : Reach 303601 := rs (se 2 (by rfl) ⟨113850, by rfl⟩) R227701
theorem R336419 : Reach 336419 := rs (se 1 (by rfl) ⟨252314, by rfl⟩) R504629
theorem R336433 : Reach 336433 := rs (se 2 (by rfl) ⟨126162, by rfl⟩) R252325
theorem R303857 : Reach 303857 := rs (se 2 (by rfl) ⟨113946, by rfl⟩) R227893
theorem R172849 : Reach 172849 := rs (se 2 (by rfl) ⟨64818, by rfl⟩) R129637
theorem R566129 : Reach 566129 := rs (se 2 (by rfl) ⟨212298, by rfl⟩) R424597
theorem R107411 : Reach 107411 := rs (se 1 (by rfl) ⟨80558, by rfl⟩) R161117
theorem R304163 : Reach 304163 := rs (se 1 (by rfl) ⟨228122, by rfl⟩) R456245
theorem R238691 : Reach 238691 := rs (se 1 (by rfl) ⟨179018, by rfl⟩) R358037
theorem R205955 : Reach 205955 := rs (se 1 (by rfl) ⟨154466, by rfl⟩) R308933
theorem R501005 : Reach 501005 := rs (se 3 (by rfl) ⟨93938, by rfl⟩) R187877
theorem R304397 : Reach 304397 := rs (se 3 (by rfl) ⟨57074, by rfl⟩) R114149
theorem R304451 : Reach 304451 := rs (se 1 (by rfl) ⟨228338, by rfl⟩) R456677
theorem R304721 : Reach 304721 := rs (se 2 (by rfl) ⟨114270, by rfl⟩) R228541
theorem R763505 : Reach 763505 := rs (se 2 (by rfl) ⟨286314, by rfl⟩) R572629
theorem R141011 : Reach 141011 := rs (se 1 (by rfl) ⟨105758, by rfl⟩) R211517
theorem R272177 : Reach 272177 := rs (se 2 (by rfl) ⟨102066, by rfl⟩) R204133
theorem R141107 : Reach 141107 := rs (se 1 (by rfl) ⟨105830, by rfl⟩) R211661
theorem R141139 : Reach 141139 := rs (se 1 (by rfl) ⟨105854, by rfl⟩) R211709
theorem R239473 : Reach 239473 := rs (se 2 (by rfl) ⟨89802, by rfl⟩) R179605
theorem R272273 : Reach 272273 := rs (se 2 (by rfl) ⟨102102, by rfl⟩) R204205
theorem R337891 : Reach 337891 := rs (se 1 (by rfl) ⟨253418, by rfl⟩) R506837
theorem R305261 : Reach 305261 := rs (se 3 (by rfl) ⟨57236, by rfl⟩) R114473
theorem R305315 : Reach 305315 := rs (se 1 (by rfl) ⟨228986, by rfl⟩) R457973
theorem R960821 : Reach 960821 := rs (se 5 (by rfl) ⟨45038, by rfl⟩) R90077
theorem R305585 : Reach 305585 := rs (se 2 (by rfl) ⟨114594, by rfl⟩) R229189
theorem R272945 : Reach 272945 := rs (se 2 (by rfl) ⟨102354, by rfl⟩) R204709
theorem R1911437 : Reach 1911437 := rs (se 3 (by rfl) ⟨358394, by rfl⟩) R716789
theorem R1157813 : Reach 1157813 := rs (se 5 (by rfl) ⟨54272, by rfl⟩) R108545
theorem R142049 : Reach 142049 := rs (se 2 (by rfl) ⟨53268, by rfl⟩) R106537
theorem R306125 : Reach 306125 := rs (se 3 (by rfl) ⟨57398, by rfl⟩) R114797
theorem R306179 : Reach 306179 := rs (se 1 (by rfl) ⟨229634, by rfl⟩) R459269
theorem R240803 : Reach 240803 := rs (se 1 (by rfl) ⟨180602, by rfl⟩) R361205
theorem R306449 : Reach 306449 := rs (se 2 (by rfl) ⟨114918, by rfl⟩) R229837
theorem R437795 : Reach 437795 := rs (se 1 (by rfl) ⟨328346, by rfl⟩) R656693
theorem R405091 : Reach 405091 := rs (se 1 (by rfl) ⟨303818, by rfl⟩) R607637
theorem R241265 : Reach 241265 := rs (se 2 (by rfl) ⟨90474, by rfl⟩) R180949
theorem R667277 : Reach 667277 := rs (se 3 (by rfl) ⟨125114, by rfl⟩) R250229
theorem R143137 : Reach 143137 := rs (se 2 (by rfl) ⟨53676, by rfl⟩) R107353
theorem R306989 : Reach 306989 := rs (se 3 (by rfl) ⟨57560, by rfl⟩) R115121
theorem R307043 : Reach 307043 := rs (se 1 (by rfl) ⟨230282, by rfl⟩) R460565
theorem R143363 : Reach 143363 := rs (se 1 (by rfl) ⟨107522, by rfl⟩) R215045
theorem R503921 : Reach 503921 := rs (se 2 (by rfl) ⟨188970, by rfl⟩) R377941
theorem R307313 : Reach 307313 := rs (se 2 (by rfl) ⟨115242, by rfl⟩) R230485
theorem R340109 : Reach 340109 := rs (se 3 (by rfl) ⟨63770, by rfl⟩) R127541
theorem R110803 : Reach 110803 := rs (se 1 (by rfl) ⟨83102, by rfl⟩) R166205
theorem R110899 : Reach 110899 := rs (se 1 (by rfl) ⟨83174, by rfl⟩) R166349
theorem R144035 : Reach 144035 := rs (se 1 (by rfl) ⟨108026, by rfl⟩) R216053
theorem R111395 : Reach 111395 := rs (se 1 (by rfl) ⟨83546, by rfl⟩) R167093
theorem R242477 : Reach 242477 := rs (se 3 (by rfl) ⟨45464, by rfl⟩) R90929
theorem R897905 : Reach 897905 := rs (se 2 (by rfl) ⟨336714, by rfl⟩) R673429
theorem R144337 : Reach 144337 := rs (se 2 (by rfl) ⟨54126, by rfl⟩) R108253
theorem R177265 : Reach 177265 := rs (se 2 (by rfl) ⟨66474, by rfl⟩) R132949
theorem R144547 : Reach 144547 := rs (se 1 (by rfl) ⟨108410, by rfl⟩) R216821
theorem R144593 : Reach 144593 := rs (se 2 (by rfl) ⟨54222, by rfl⟩) R108445
theorem R1029347 : Reach 1029347 := rs (se 1 (by rfl) ⟨772010, by rfl⟩) R1544021
theorem R275729 : Reach 275729 := rs (se 2 (by rfl) ⟨103398, by rfl⟩) R206797
theorem R112099 : Reach 112099 := rs (se 1 (by rfl) ⟨84074, by rfl⟩) R168149
theorem R275971 : Reach 275971 := rs (se 1 (by rfl) ⟨206978, by rfl⟩) R413957
theorem R767501 : Reach 767501 := rs (se 3 (by rfl) ⟨143906, by rfl⟩) R287813
theorem R505379 : Reach 505379 := rs (se 1 (by rfl) ⟨379034, by rfl⟩) R758069
theorem R472625 : Reach 472625 := rs (se 2 (by rfl) ⟨177234, by rfl⟩) R354469
theorem R112195 : Reach 112195 := rs (se 1 (by rfl) ⟨84146, by rfl⟩) R168293
theorem R571013 : Reach 571013 := rs (se 4 (by rfl) ⟨53532, by rfl⟩) R107065
theorem R243665 : Reach 243665 := rs (se 2 (by rfl) ⟨91374, by rfl⟩) R182749
theorem R374797 : Reach 374797 := rs (se 3 (by rfl) ⟨70274, by rfl⟩) R140549
theorem R112691 : Reach 112691 := rs (se 1 (by rfl) ⟨84518, by rfl⟩) R169037
theorem R604273 : Reach 604273 := rs (se 2 (by rfl) ⟨226602, by rfl⟩) R453205
theorem R178531 : Reach 178531 := rs (se 1 (by rfl) ⟨133898, by rfl⟩) R267797
theorem R145795 : Reach 145795 := rs (se 1 (by rfl) ⟨109346, by rfl⟩) R218693
theorem R670193 : Reach 670193 := rs (se 2 (by rfl) ⟨251322, by rfl⟩) R502645
theorem R113395 : Reach 113395 := rs (se 1 (by rfl) ⟨85046, by rfl⟩) R170093
theorem R211747 : Reach 211747 := rs (se 1 (by rfl) ⟨158810, by rfl⟩) R317621
theorem R113491 : Reach 113491 := rs (se 1 (by rfl) ⟨85118, by rfl⟩) R170237
theorem R1063793 : Reach 1063793 := rs (se 2 (by rfl) ⟨398922, by rfl⟩) R797845
theorem R211843 : Reach 211843 := rs (se 1 (by rfl) ⟨158882, by rfl⟩) R317765
theorem R343025 : Reach 343025 := rs (se 2 (by rfl) ⟨128634, by rfl⟩) R257269
theorem R179185 : Reach 179185 := rs (se 2 (by rfl) ⟨67194, by rfl⟩) R134389
theorem R441379 : Reach 441379 := rs (se 1 (by rfl) ⟨331034, by rfl⟩) R662069
theorem R113891 : Reach 113891 := rs (se 1 (by rfl) ⟨85418, by rfl⟩) R170837
theorem R2243861 : Reach 2243861 := rs (se 6 (by rfl) ⟨52590, by rfl⟩) R105181
theorem R113987 : Reach 113987 := rs (se 1 (by rfl) ⟨85490, by rfl⟩) R170981
theorem R179569 : Reach 179569 := rs (se 2 (by rfl) ⟨67338, by rfl⟩) R134677
theorem R147089 : Reach 147089 := rs (se 2 (by rfl) ⟨55158, by rfl⟩) R110317
theorem R442097 : Reach 442097 := rs (se 2 (by rfl) ⟨165786, by rfl⟩) R331573
theorem R147217 : Reach 147217 := rs (se 2 (by rfl) ⟨55206, by rfl⟩) R110413
theorem R147251 : Reach 147251 := rs (se 1 (by rfl) ⟨110438, by rfl⟩) R220877
theorem R147379 : Reach 147379 := rs (se 1 (by rfl) ⟨110534, by rfl⟩) R221069
theorem R114691 : Reach 114691 := rs (se 1 (by rfl) ⟨86018, by rfl⟩) R172037
theorem R147521 : Reach 147521 := rs (se 2 (by rfl) ⟨55320, by rfl⟩) R110641
theorem R114787 : Reach 114787 := rs (se 1 (by rfl) ⟨86090, by rfl⟩) R172181
theorem R147649 : Reach 147649 := rs (se 2 (by rfl) ⟨55368, by rfl⟩) R110737
theorem R147683 : Reach 147683 := rs (se 1 (by rfl) ⟨110762, by rfl⟩) R221525
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R344483 : Reach 344483 := rs (se 1 (by rfl) ⟨258362, by rfl⟩) R516725
theorem R147953 : Reach 147953 := rs (se 2 (by rfl) ⟨55482, by rfl⟩) R110965
theorem R115283 : Reach 115283 := rs (se 1 (by rfl) ⟨86462, by rfl⟩) R172925
theorem R279139 : Reach 279139 := rs (se 1 (by rfl) ⟨209354, by rfl⟩) R418709
theorem R148081 : Reach 148081 := rs (se 2 (by rfl) ⟨55530, by rfl⟩) R111061
theorem R148115 : Reach 148115 := rs (se 1 (by rfl) ⟨111086, by rfl⟩) R222173
theorem R148243 : Reach 148243 := rs (se 1 (by rfl) ⟨111182, by rfl⟩) R222365
theorem R148385 : Reach 148385 := rs (se 2 (by rfl) ⟨55644, by rfl⟩) R111289
theorem R639971 : Reach 639971 := rs (se 1 (by rfl) ⟨479978, by rfl⟩) R959957
theorem R148513 : Reach 148513 := rs (se 2 (by rfl) ⟨55692, by rfl⟩) R111385
theorem R279587 : Reach 279587 := rs (se 1 (by rfl) ⟨209690, by rfl⟩) R419381
theorem R148547 : Reach 148547 := rs (se 1 (by rfl) ⟨111410, by rfl⟩) R222821
theorem R443555 : Reach 443555 := rs (se 1 (by rfl) ⟨332666, by rfl⟩) R665333
theorem R148675 : Reach 148675 := rs (se 1 (by rfl) ⟨111506, by rfl⟩) R223013
theorem R148817 : Reach 148817 := rs (se 2 (by rfl) ⟨55806, by rfl⟩) R111613
theorem R345485 : Reach 345485 := rs (se 3 (by rfl) ⟨64778, by rfl⟩) R129557
theorem R148945 : Reach 148945 := rs (se 2 (by rfl) ⟨55854, by rfl⟩) R111709
theorem R148979 : Reach 148979 := rs (se 1 (by rfl) ⟨111734, by rfl⟩) R223469
theorem R149107 : Reach 149107 := rs (se 1 (by rfl) ⟨111830, by rfl⟩) R223661
theorem R1164941 : Reach 1164941 := rs (se 3 (by rfl) ⟨218426, by rfl⟩) R436853
theorem R149249 : Reach 149249 := rs (se 2 (by rfl) ⟨55968, by rfl⟩) R111937
theorem R149377 : Reach 149377 := rs (se 2 (by rfl) ⟨56016, by rfl⟩) R112033
theorem R149411 : Reach 149411 := rs (se 1 (by rfl) ⟨112058, by rfl⟩) R224117
theorem R444365 : Reach 444365 := rs (se 3 (by rfl) ⟨83318, by rfl⟩) R166637
theorem R149539 : Reach 149539 := rs (se 1 (by rfl) ⟨112154, by rfl⟩) R224309
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R182353 : Reach 182353 := rs (se 2 (by rfl) ⟨68382, by rfl⟩) R136765
theorem R149681 : Reach 149681 := rs (se 2 (by rfl) ⟨56130, by rfl⟩) R112261
theorem R280817 : Reach 280817 := rs (se 2 (by rfl) ⟨105306, by rfl⟩) R210613
theorem R379171 : Reach 379171 := rs (se 1 (by rfl) ⟨284378, by rfl⟩) R568757
theorem R149809 : Reach 149809 := rs (se 2 (by rfl) ⟨56178, by rfl⟩) R112357
theorem R149843 : Reach 149843 := rs (se 1 (by rfl) ⟨112382, by rfl⟩) R224765
theorem R215473 : Reach 215473 := rs (se 2 (by rfl) ⟨80802, by rfl⟩) R161605
theorem R149971 : Reach 149971 := rs (se 1 (by rfl) ⟨112478, by rfl⟩) R224957
theorem R248305 : Reach 248305 := rs (se 2 (by rfl) ⟨93114, by rfl⟩) R186229
theorem R150113 : Reach 150113 := rs (se 2 (by rfl) ⟨56292, by rfl⟩) R112585
theorem R150241 : Reach 150241 := rs (se 2 (by rfl) ⟨56340, by rfl⟩) R112681
theorem R248579 : Reach 248579 := rs (se 1 (by rfl) ⟨186434, by rfl⟩) R372869
theorem R150275 : Reach 150275 := rs (se 1 (by rfl) ⟨112706, by rfl⟩) R225413
theorem R150403 : Reach 150403 := rs (se 1 (by rfl) ⟨112802, by rfl⟩) R225605
theorem R314275 : Reach 314275 := rs (se 1 (by rfl) ⟨235706, by rfl⟩) R471413
theorem R248771 : Reach 248771 := rs (se 1 (by rfl) ⟨186578, by rfl⟩) R373157
theorem R150545 : Reach 150545 := rs (se 2 (by rfl) ⟨56454, by rfl⟩) R112909
theorem R281713 : Reach 281713 := rs (se 2 (by rfl) ⟨105642, by rfl⟩) R211285
theorem R150673 : Reach 150673 := rs (se 2 (by rfl) ⟨56502, by rfl⟩) R113005
theorem R150707 : Reach 150707 := rs (se 1 (by rfl) ⟨113030, by rfl⟩) R226061
theorem R544013 : Reach 544013 := rs (se 3 (by rfl) ⟨102002, by rfl⟩) R204005
theorem R150835 : Reach 150835 := rs (se 1 (by rfl) ⟨113126, by rfl⟩) R226253
theorem R118081 : Reach 118081 := rs (se 2 (by rfl) ⟨44280, by rfl⟩) R88561
theorem R314723 : Reach 314723 := rs (se 1 (by rfl) ⟨236042, by rfl⟩) R472085
theorem R150977 : Reach 150977 := rs (se 2 (by rfl) ⟨56616, by rfl⟩) R113233
theorem R249293 : Reach 249293 := rs (se 3 (by rfl) ⟨46742, by rfl⟩) R93485
theorem R151105 : Reach 151105 := rs (se 2 (by rfl) ⟨56664, by rfl⟩) R113329
theorem R151139 : Reach 151139 := rs (se 1 (by rfl) ⟨113354, by rfl⟩) R226709
theorem R151267 : Reach 151267 := rs (se 1 (by rfl) ⟨113450, by rfl⟩) R226901
theorem R249581 : Reach 249581 := rs (se 3 (by rfl) ⟨46796, by rfl⟩) R93593
theorem R151409 : Reach 151409 := rs (se 2 (by rfl) ⟨56778, by rfl⟩) R113557
theorem R118643 : Reach 118643 := rs (se 1 (by rfl) ⟨88982, by rfl⟩) R177965
theorem R249763 : Reach 249763 := rs (se 1 (by rfl) ⟨187322, by rfl⟩) R374645
theorem R151537 : Reach 151537 := rs (se 2 (by rfl) ⟨56826, by rfl⟩) R113653
theorem R151571 : Reach 151571 := rs (se 1 (by rfl) ⟨113678, by rfl⟩) R227357
theorem R151699 : Reach 151699 := rs (se 1 (by rfl) ⟨113774, by rfl⟩) R227549
theorem R479459 : Reach 479459 := rs (se 1 (by rfl) ⟨359594, by rfl⟩) R719189
theorem R151841 : Reach 151841 := rs (se 2 (by rfl) ⟨56940, by rfl⟩) R113881
theorem R217379 : Reach 217379 := rs (se 1 (by rfl) ⟨163034, by rfl⟩) R326069
theorem R250253 : Reach 250253 := rs (se 3 (by rfl) ⟨46922, by rfl⟩) R93845
theorem R151969 : Reach 151969 := rs (se 2 (by rfl) ⟨56988, by rfl⟩) R113977
theorem R152003 : Reach 152003 := rs (se 1 (by rfl) ⟨114002, by rfl⟩) R228005
theorem R152131 : Reach 152131 := rs (se 1 (by rfl) ⟨114098, by rfl⟩) R228197
theorem R217667 : Reach 217667 := rs (se 1 (by rfl) ⟨163250, by rfl⟩) R326501
theorem R283277 : Reach 283277 := rs (se 3 (by rfl) ⟨53114, by rfl⟩) R106229
theorem R381617 : Reach 381617 := rs (se 2 (by rfl) ⟨143106, by rfl⟩) R286213
theorem R152273 : Reach 152273 := rs (se 2 (by rfl) ⟨57102, by rfl⟩) R114205
theorem R447281 : Reach 447281 := rs (se 2 (by rfl) ⟨167730, by rfl⟩) R335461
theorem R152401 : Reach 152401 := rs (se 2 (by rfl) ⟨57150, by rfl⟩) R114301
theorem R152435 : Reach 152435 := rs (se 1 (by rfl) ⟨114326, by rfl⟩) R228653
theorem R152563 : Reach 152563 := rs (se 1 (by rfl) ⟨114422, by rfl⟩) R228845
theorem R87139 : Reach 87139 := rs (se 1 (by rfl) ⟨65354, by rfl⟩) R130709
theorem R87155 : Reach 87155 := rs (se 1 (by rfl) ⟨65366, by rfl⟩) R130733
theorem R152705 : Reach 152705 := rs (se 2 (by rfl) ⟨57264, by rfl⟩) R114529
theorem R87171 : Reach 87171 := rs (se 1 (by rfl) ⟨65378, by rfl⟩) R130757
theorem R87187 : Reach 87187 := rs (se 1 (by rfl) ⟨65390, by rfl⟩) R130781
theorem R87203 : Reach 87203 := rs (se 1 (by rfl) ⟨65402, by rfl⟩) R130805
theorem R87219 : Reach 87219 := rs (se 1 (by rfl) ⟨65414, by rfl⟩) R130829
theorem R87235 : Reach 87235 := rs (se 1 (by rfl) ⟨65426, by rfl⟩) R130853
theorem R87251 : Reach 87251 := rs (se 1 (by rfl) ⟨65438, by rfl⟩) R130877
theorem R87267 : Reach 87267 := rs (se 1 (by rfl) ⟨65450, by rfl⟩) R130901
theorem R87283 : Reach 87283 := rs (se 1 (by rfl) ⟨65462, by rfl⟩) R130925
theorem R152833 : Reach 152833 := rs (se 2 (by rfl) ⟨57312, by rfl⟩) R114625
theorem R87299 : Reach 87299 := rs (se 1 (by rfl) ⟨65474, by rfl⟩) R130949
theorem R87315 : Reach 87315 := rs (se 1 (by rfl) ⟨65486, by rfl⟩) R130973
theorem R87331 : Reach 87331 := rs (se 1 (by rfl) ⟨65498, by rfl⟩) R130997
theorem R152867 : Reach 152867 := rs (se 1 (by rfl) ⟨114650, by rfl⟩) R229301
theorem R87347 : Reach 87347 := rs (se 1 (by rfl) ⟨65510, by rfl⟩) R131021
theorem R87363 : Reach 87363 := rs (se 1 (by rfl) ⟨65522, by rfl⟩) R131045
theorem R87379 : Reach 87379 := rs (se 1 (by rfl) ⟨65534, by rfl⟩) R131069
theorem R87395 : Reach 87395 := rs (se 1 (by rfl) ⟨65546, by rfl⟩) R131093
theorem R87411 : Reach 87411 := rs (se 1 (by rfl) ⟨65558, by rfl⟩) R131117
theorem R87427 : Reach 87427 := rs (se 1 (by rfl) ⟨65570, by rfl⟩) R131141
theorem R775565 : Reach 775565 := rs (se 3 (by rfl) ⟨145418, by rfl⟩) R290837
theorem R218513 : Reach 218513 := rs (se 2 (by rfl) ⟨81942, by rfl⟩) R163885
theorem R87443 : Reach 87443 := rs (se 1 (by rfl) ⟨65582, by rfl⟩) R131165
theorem R87459 : Reach 87459 := rs (se 1 (by rfl) ⟨65594, by rfl⟩) R131189
theorem R152995 : Reach 152995 := rs (se 1 (by rfl) ⟨114746, by rfl⟩) R229493
theorem R87475 : Reach 87475 := rs (se 1 (by rfl) ⟨65606, by rfl⟩) R131213
theorem R87491 : Reach 87491 := rs (se 1 (by rfl) ⟨65618, by rfl⟩) R131237
theorem R87507 : Reach 87507 := rs (se 1 (by rfl) ⟨65630, by rfl⟩) R131261
theorem R87523 : Reach 87523 := rs (se 1 (by rfl) ⟨65642, by rfl⟩) R131285
theorem R87539 : Reach 87539 := rs (se 1 (by rfl) ⟨65654, by rfl⟩) R131309
theorem R87555 : Reach 87555 := rs (se 1 (by rfl) ⟨65666, by rfl⟩) R131333
theorem R87571 : Reach 87571 := rs (se 1 (by rfl) ⟨65678, by rfl⟩) R131357
theorem R87587 : Reach 87587 := rs (se 1 (by rfl) ⟨65690, by rfl⟩) R131381
theorem R251437 : Reach 251437 := rs (se 3 (by rfl) ⟨47144, by rfl⟩) R94289
theorem R153137 : Reach 153137 := rs (se 2 (by rfl) ⟨57426, by rfl⟩) R114853
theorem R87603 : Reach 87603 := rs (se 1 (by rfl) ⟨65702, by rfl⟩) R131405
theorem R87619 : Reach 87619 := rs (se 1 (by rfl) ⟨65714, by rfl⟩) R131429
theorem R87635 : Reach 87635 := rs (se 1 (by rfl) ⟨65726, by rfl⟩) R131453
theorem R87651 : Reach 87651 := rs (se 1 (by rfl) ⟨65738, by rfl⟩) R131477
theorem R87667 : Reach 87667 := rs (se 1 (by rfl) ⟨65750, by rfl⟩) R131501
theorem R87683 : Reach 87683 := rs (se 1 (by rfl) ⟨65762, by rfl⟩) R131525
theorem R87699 : Reach 87699 := rs (se 1 (by rfl) ⟨65774, by rfl⟩) R131549
theorem R87715 : Reach 87715 := rs (se 1 (by rfl) ⟨65786, by rfl⟩) R131573
theorem R153265 : Reach 153265 := rs (se 2 (by rfl) ⟨57474, by rfl⟩) R114949
theorem R87731 : Reach 87731 := rs (se 1 (by rfl) ⟨65798, by rfl⟩) R131597
theorem R87747 : Reach 87747 := rs (se 1 (by rfl) ⟨65810, by rfl⟩) R131621
theorem R87763 : Reach 87763 := rs (se 1 (by rfl) ⟨65822, by rfl⟩) R131645
theorem R153299 : Reach 153299 := rs (se 1 (by rfl) ⟨114974, by rfl⟩) R229949
theorem R87779 : Reach 87779 := rs (se 1 (by rfl) ⟨65834, by rfl⟩) R131669
theorem R87795 : Reach 87795 := rs (se 1 (by rfl) ⟨65846, by rfl⟩) R131693
theorem R87811 : Reach 87811 := rs (se 1 (by rfl) ⟨65858, by rfl⟩) R131717
theorem R87827 : Reach 87827 := rs (se 1 (by rfl) ⟨65870, by rfl⟩) R131741
theorem R87843 : Reach 87843 := rs (se 1 (by rfl) ⟨65882, by rfl⟩) R131765
theorem R87859 : Reach 87859 := rs (se 1 (by rfl) ⟨65894, by rfl⟩) R131789
theorem R87875 : Reach 87875 := rs (se 1 (by rfl) ⟨65906, by rfl⟩) R131813
theorem R87891 : Reach 87891 := rs (se 1 (by rfl) ⟨65918, by rfl⟩) R131837
theorem R153427 : Reach 153427 := rs (se 1 (by rfl) ⟨115070, by rfl⟩) R230141
theorem R87907 : Reach 87907 := rs (se 1 (by rfl) ⟨65930, by rfl⟩) R131861
theorem R87923 : Reach 87923 := rs (se 1 (by rfl) ⟨65942, by rfl⟩) R131885
theorem R87939 : Reach 87939 := rs (se 1 (by rfl) ⟨65954, by rfl⟩) R131909
theorem R87955 : Reach 87955 := rs (se 1 (by rfl) ⟨65966, by rfl⟩) R131933
theorem R87971 : Reach 87971 := rs (se 1 (by rfl) ⟨65978, by rfl⟩) R131957
theorem R87987 : Reach 87987 := rs (se 1 (by rfl) ⟨65990, by rfl⟩) R131981
theorem R88003 : Reach 88003 := rs (se 1 (by rfl) ⟨66002, by rfl⟩) R132005
theorem R88019 : Reach 88019 := rs (se 1 (by rfl) ⟨66014, by rfl⟩) R132029
theorem R153569 : Reach 153569 := rs (se 2 (by rfl) ⟨57588, by rfl⟩) R115177
theorem R88035 : Reach 88035 := rs (se 1 (by rfl) ⟨66026, by rfl⟩) R132053
theorem R88051 : Reach 88051 := rs (se 1 (by rfl) ⟨66038, by rfl⟩) R132077
theorem R88067 : Reach 88067 := rs (se 1 (by rfl) ⟨66050, by rfl⟩) R132101
theorem R88083 : Reach 88083 := rs (se 1 (by rfl) ⟨66062, by rfl⟩) R132125
theorem R88099 : Reach 88099 := rs (se 1 (by rfl) ⟨66074, by rfl⟩) R132149
theorem R88115 : Reach 88115 := rs (se 1 (by rfl) ⟨66086, by rfl⟩) R132173
theorem R1136693 : Reach 1136693 := rs (se 5 (by rfl) ⟨53282, by rfl⟩) R106565
theorem R88131 : Reach 88131 := rs (se 1 (by rfl) ⟨66098, by rfl⟩) R132197
theorem R88147 : Reach 88147 := rs (se 1 (by rfl) ⟨66110, by rfl⟩) R132221
theorem R153697 : Reach 153697 := rs (se 2 (by rfl) ⟨57636, by rfl⟩) R115273
theorem R88163 : Reach 88163 := rs (se 1 (by rfl) ⟨66122, by rfl⟩) R132245
theorem R88179 : Reach 88179 := rs (se 1 (by rfl) ⟨66134, by rfl⟩) R132269
theorem R88195 : Reach 88195 := rs (se 1 (by rfl) ⟨66146, by rfl⟩) R132293
theorem R153731 : Reach 153731 := rs (se 1 (by rfl) ⟨115298, by rfl⟩) R230597
theorem R88211 : Reach 88211 := rs (se 1 (by rfl) ⟨66158, by rfl⟩) R132317
theorem R88227 : Reach 88227 := rs (se 1 (by rfl) ⟨66170, by rfl⟩) R132341
theorem R186545 : Reach 186545 := rs (se 2 (by rfl) ⟨69954, by rfl⟩) R139909
theorem R88243 : Reach 88243 := rs (se 1 (by rfl) ⟨66182, by rfl⟩) R132365
theorem R88259 : Reach 88259 := rs (se 1 (by rfl) ⟨66194, by rfl⟩) R132389
theorem R88275 : Reach 88275 := rs (se 1 (by rfl) ⟨66206, by rfl⟩) R132413
theorem R88291 : Reach 88291 := rs (se 1 (by rfl) ⟨66218, by rfl⟩) R132437
theorem R448739 : Reach 448739 := rs (se 1 (by rfl) ⟨336554, by rfl⟩) R673109
theorem R88307 : Reach 88307 := rs (se 1 (by rfl) ⟨66230, by rfl⟩) R132461
theorem R88323 : Reach 88323 := rs (se 1 (by rfl) ⟨66242, by rfl⟩) R132485
theorem R514309 : Reach 514309 := rs (se 4 (by rfl) ⟨48216, by rfl⟩) R96433
theorem R88339 : Reach 88339 := rs (se 1 (by rfl) ⟨66254, by rfl⟩) R132509
theorem R88355 : Reach 88355 := rs (se 1 (by rfl) ⟨66266, by rfl⟩) R132533
theorem R88371 : Reach 88371 := rs (se 1 (by rfl) ⟨66278, by rfl⟩) R132557
theorem R88387 : Reach 88387 := rs (se 1 (by rfl) ⟨66290, by rfl⟩) R132581
theorem R88403 : Reach 88403 := rs (se 1 (by rfl) ⟨66302, by rfl⟩) R132605
theorem R711011 : Reach 711011 := rs (se 1 (by rfl) ⟨533258, by rfl⟩) R1066517
theorem R88419 : Reach 88419 := rs (se 1 (by rfl) ⟨66314, by rfl⟩) R132629
theorem R88435 : Reach 88435 := rs (se 1 (by rfl) ⟨66326, by rfl⟩) R132653
theorem R88451 : Reach 88451 := rs (se 1 (by rfl) ⟨66338, by rfl⟩) R132677
theorem R88467 : Reach 88467 := rs (se 1 (by rfl) ⟨66350, by rfl⟩) R132701
theorem R88483 : Reach 88483 := rs (se 1 (by rfl) ⟨66362, by rfl⟩) R132725
theorem R88499 : Reach 88499 := rs (se 1 (by rfl) ⟨66374, by rfl⟩) R132749
theorem R88515 : Reach 88515 := rs (se 1 (by rfl) ⟨66386, by rfl⟩) R132773
theorem R88531 : Reach 88531 := rs (se 1 (by rfl) ⟨66398, by rfl⟩) R132797
theorem R88547 : Reach 88547 := rs (se 1 (by rfl) ⟨66410, by rfl⟩) R132821
theorem R88563 : Reach 88563 := rs (se 1 (by rfl) ⟨66422, by rfl⟩) R132845
theorem R88579 : Reach 88579 := rs (se 1 (by rfl) ⟨66434, by rfl⟩) R132869
theorem R88595 : Reach 88595 := rs (se 1 (by rfl) ⟨66446, by rfl⟩) R132893
theorem R88611 : Reach 88611 := rs (se 1 (by rfl) ⟨66458, by rfl⟩) R132917
theorem R88627 : Reach 88627 := rs (se 1 (by rfl) ⟨66470, by rfl⟩) R132941
theorem R88643 : Reach 88643 := rs (se 1 (by rfl) ⟨66482, by rfl⟩) R132965
theorem R252497 : Reach 252497 := rs (se 2 (by rfl) ⟨94686, by rfl⟩) R189373
theorem R88659 : Reach 88659 := rs (se 1 (by rfl) ⟨66494, by rfl⟩) R132989
theorem R88675 : Reach 88675 := rs (se 1 (by rfl) ⟨66506, by rfl⟩) R133013
theorem R88691 : Reach 88691 := rs (se 1 (by rfl) ⟨66518, by rfl⟩) R133037
theorem R88707 : Reach 88707 := rs (se 1 (by rfl) ⟨66530, by rfl⟩) R133061
theorem R547469 : Reach 547469 := rs (se 3 (by rfl) ⟨102650, by rfl⟩) R205301
theorem R88723 : Reach 88723 := rs (se 1 (by rfl) ⟨66542, by rfl⟩) R133085
theorem R88739 : Reach 88739 := rs (se 1 (by rfl) ⟨66554, by rfl⟩) R133109
theorem R580259 : Reach 580259 := rs (se 1 (by rfl) ⟨435194, by rfl⟩) R870389
theorem R187057 : Reach 187057 := rs (se 2 (by rfl) ⟨70146, by rfl⟩) R140293
theorem R88755 : Reach 88755 := rs (se 1 (by rfl) ⟨66566, by rfl⟩) R133133
theorem R88771 : Reach 88771 := rs (se 1 (by rfl) ⟨66578, by rfl⟩) R133157
theorem R88787 : Reach 88787 := rs (se 1 (by rfl) ⟨66590, by rfl⟩) R133181
theorem R88803 : Reach 88803 := rs (se 1 (by rfl) ⟨66602, by rfl⟩) R133205
theorem R88819 : Reach 88819 := rs (se 1 (by rfl) ⟨66614, by rfl⟩) R133229
theorem R88835 : Reach 88835 := rs (se 1 (by rfl) ⟨66626, by rfl⟩) R133253
theorem R88851 : Reach 88851 := rs (se 1 (by rfl) ⟨66638, by rfl⟩) R133277
theorem R88867 : Reach 88867 := rs (se 1 (by rfl) ⟨66650, by rfl⟩) R133301
theorem R88883 : Reach 88883 := rs (se 1 (by rfl) ⟨66662, by rfl⟩) R133325
theorem R88899 : Reach 88899 := rs (se 1 (by rfl) ⟨66674, by rfl⟩) R133349
theorem R547661 : Reach 547661 := rs (se 3 (by rfl) ⟨102686, by rfl⟩) R205373
theorem R88915 : Reach 88915 := rs (se 1 (by rfl) ⟨66686, by rfl⟩) R133373
theorem R88931 : Reach 88931 := rs (se 1 (by rfl) ⟨66698, by rfl⟩) R133397
theorem R88947 : Reach 88947 := rs (se 1 (by rfl) ⟨66710, by rfl⟩) R133421
theorem R88963 : Reach 88963 := rs (se 1 (by rfl) ⟨66722, by rfl⟩) R133445
theorem R88979 : Reach 88979 := rs (se 1 (by rfl) ⟨66734, by rfl⟩) R133469
theorem R88995 : Reach 88995 := rs (se 1 (by rfl) ⟨66746, by rfl⟩) R133493
theorem R89011 : Reach 89011 := rs (se 1 (by rfl) ⟨66758, by rfl⟩) R133517
theorem R89027 : Reach 89027 := rs (se 1 (by rfl) ⟨66770, by rfl⟩) R133541
theorem R89043 : Reach 89043 := rs (se 1 (by rfl) ⟨66782, by rfl⟩) R133565
theorem R89059 : Reach 89059 := rs (se 1 (by rfl) ⟨66794, by rfl⟩) R133589
theorem R711665 : Reach 711665 := rs (se 2 (by rfl) ⟨266874, by rfl⟩) R533749
theorem R89075 : Reach 89075 := rs (se 1 (by rfl) ⟨66806, by rfl⟩) R133613
theorem R89091 : Reach 89091 := rs (se 1 (by rfl) ⟨66818, by rfl⟩) R133637
theorem R449549 : Reach 449549 := rs (se 3 (by rfl) ⟨84290, by rfl⟩) R168581
theorem R89107 : Reach 89107 := rs (se 1 (by rfl) ⟨66830, by rfl⟩) R133661
theorem R89123 : Reach 89123 := rs (se 1 (by rfl) ⟨66842, by rfl⟩) R133685
theorem R89139 : Reach 89139 := rs (se 1 (by rfl) ⟨66854, by rfl⟩) R133709
theorem R89155 : Reach 89155 := rs (se 1 (by rfl) ⟨66866, by rfl⟩) R133733
theorem R285763 : Reach 285763 := rs (se 1 (by rfl) ⟨214322, by rfl⟩) R428645
theorem R89171 : Reach 89171 := rs (se 1 (by rfl) ⟨66878, by rfl⟩) R133757
theorem R89187 : Reach 89187 := rs (se 1 (by rfl) ⟨66890, by rfl⟩) R133781
theorem R89203 : Reach 89203 := rs (se 1 (by rfl) ⟨66902, by rfl⟩) R133805
theorem R89219 : Reach 89219 := rs (se 1 (by rfl) ⟨66914, by rfl⟩) R133829
theorem R89235 : Reach 89235 := rs (se 1 (by rfl) ⟨66926, by rfl⟩) R133853
theorem R89251 : Reach 89251 := rs (se 1 (by rfl) ⟨66938, by rfl⟩) R133877
theorem R89267 : Reach 89267 := rs (se 1 (by rfl) ⟨66950, by rfl⟩) R133901
theorem R89283 : Reach 89283 := rs (se 1 (by rfl) ⟨66962, by rfl⟩) R133925
theorem R285905 : Reach 285905 := rs (se 2 (by rfl) ⟨107214, by rfl⟩) R214429
theorem R89299 : Reach 89299 := rs (se 1 (by rfl) ⟨66974, by rfl⟩) R133949
theorem R89315 : Reach 89315 := rs (se 1 (by rfl) ⟨66986, by rfl⟩) R133973
theorem R253169 : Reach 253169 := rs (se 2 (by rfl) ⟨94938, by rfl⟩) R189877
theorem R89331 : Reach 89331 := rs (se 1 (by rfl) ⟨66998, by rfl⟩) R133997
theorem R89347 : Reach 89347 := rs (se 1 (by rfl) ⟨67010, by rfl⟩) R134021
theorem R810253 : Reach 810253 := rs (se 3 (by rfl) ⟨151922, by rfl⟩) R303845
theorem R89363 : Reach 89363 := rs (se 1 (by rfl) ⟨67022, by rfl⟩) R134045
theorem R89379 : Reach 89379 := rs (se 1 (by rfl) ⟨67034, by rfl⟩) R134069
theorem R89395 : Reach 89395 := rs (se 1 (by rfl) ⟨67046, by rfl⟩) R134093
theorem R286019 : Reach 286019 := rs (se 1 (by rfl) ⟨214514, by rfl⟩) R429029
theorem R89411 : Reach 89411 := rs (se 1 (by rfl) ⟨67058, by rfl⟩) R134117
theorem R220483 : Reach 220483 := rs (se 1 (by rfl) ⟨165362, by rfl⟩) R330725
theorem R89427 : Reach 89427 := rs (se 1 (by rfl) ⟨67070, by rfl⟩) R134141
theorem R89443 : Reach 89443 := rs (se 1 (by rfl) ⟨67082, by rfl⟩) R134165
theorem R89459 : Reach 89459 := rs (se 1 (by rfl) ⟨67094, by rfl⟩) R134189
theorem R89475 : Reach 89475 := rs (se 1 (by rfl) ⟨67106, by rfl⟩) R134213
theorem R89491 : Reach 89491 := rs (se 1 (by rfl) ⟨67118, by rfl⟩) R134237
theorem R89507 : Reach 89507 := rs (se 1 (by rfl) ⟨67130, by rfl⟩) R134261
theorem R89523 : Reach 89523 := rs (se 1 (by rfl) ⟨67142, by rfl⟩) R134285
theorem R89539 : Reach 89539 := rs (se 1 (by rfl) ⟨67154, by rfl⟩) R134309
theorem R89555 : Reach 89555 := rs (se 1 (by rfl) ⟨67166, by rfl⟩) R134333
theorem R89571 : Reach 89571 := rs (se 1 (by rfl) ⟨67178, by rfl⟩) R134357
theorem R89587 : Reach 89587 := rs (se 1 (by rfl) ⟨67190, by rfl⟩) R134381
theorem R89603 : Reach 89603 := rs (se 1 (by rfl) ⟨67202, by rfl⟩) R134405
theorem R89619 : Reach 89619 := rs (se 1 (by rfl) ⟨67214, by rfl⟩) R134429
theorem R89635 : Reach 89635 := rs (se 1 (by rfl) ⟨67226, by rfl⟩) R134453
theorem R89651 : Reach 89651 := rs (se 1 (by rfl) ⟨67238, by rfl⟩) R134477
theorem R89667 : Reach 89667 := rs (se 1 (by rfl) ⟨67250, by rfl⟩) R134501
theorem R89683 : Reach 89683 := rs (se 1 (by rfl) ⟨67262, by rfl⟩) R134525
theorem R89699 : Reach 89699 := rs (se 1 (by rfl) ⟨67274, by rfl⟩) R134549
theorem R89715 : Reach 89715 := rs (se 1 (by rfl) ⟨67286, by rfl⟩) R134573
theorem R89731 : Reach 89731 := rs (se 1 (by rfl) ⟨67298, by rfl⟩) R134597
theorem R89747 : Reach 89747 := rs (se 1 (by rfl) ⟨67310, by rfl⟩) R134621
theorem R89763 : Reach 89763 := rs (se 1 (by rfl) ⟨67322, by rfl⟩) R134645
theorem R89779 : Reach 89779 := rs (se 1 (by rfl) ⟨67334, by rfl⟩) R134669
theorem R89795 : Reach 89795 := rs (se 1 (by rfl) ⟨67346, by rfl⟩) R134693
theorem R89811 : Reach 89811 := rs (se 1 (by rfl) ⟨67358, by rfl⟩) R134717
theorem R89827 : Reach 89827 := rs (se 1 (by rfl) ⟨67370, by rfl⟩) R134741
theorem R89843 : Reach 89843 := rs (se 1 (by rfl) ⟨67382, by rfl⟩) R134765
theorem R89859 : Reach 89859 := rs (se 1 (by rfl) ⟨67394, by rfl⟩) R134789
theorem R89875 : Reach 89875 := rs (se 1 (by rfl) ⟨67406, by rfl⟩) R134813
theorem R89891 : Reach 89891 := rs (se 1 (by rfl) ⟨67418, by rfl⟩) R134837
theorem R89907 : Reach 89907 := rs (se 1 (by rfl) ⟨67430, by rfl⟩) R134861
theorem R89923 : Reach 89923 := rs (se 1 (by rfl) ⟨67442, by rfl⟩) R134885
theorem R89939 : Reach 89939 := rs (se 1 (by rfl) ⟨67454, by rfl⟩) R134909
theorem R89955 : Reach 89955 := rs (se 1 (by rfl) ⟨67466, by rfl⟩) R134933
theorem R89971 : Reach 89971 := rs (se 1 (by rfl) ⟨67478, by rfl⟩) R134957
theorem R89987 : Reach 89987 := rs (se 1 (by rfl) ⟨67490, by rfl⟩) R134981
theorem R90003 : Reach 90003 := rs (se 1 (by rfl) ⟨67502, by rfl⟩) R135005
theorem R90019 : Reach 90019 := rs (se 1 (by rfl) ⟨67514, by rfl⟩) R135029
theorem R319409 : Reach 319409 := rs (se 2 (by rfl) ⟨119778, by rfl⟩) R239557
theorem R90035 : Reach 90035 := rs (se 1 (by rfl) ⟨67526, by rfl⟩) R135053
theorem R90051 : Reach 90051 := rs (se 1 (by rfl) ⟨67538, by rfl⟩) R135077
theorem R90067 : Reach 90067 := rs (se 1 (by rfl) ⟨67550, by rfl⟩) R135101
theorem R90083 : Reach 90083 := rs (se 1 (by rfl) ⟨67562, by rfl⟩) R135125
theorem R90099 : Reach 90099 := rs (se 1 (by rfl) ⟨67574, by rfl⟩) R135149
theorem R253955 : Reach 253955 := rs (se 1 (by rfl) ⟨190466, by rfl⟩) R380933
theorem R90115 : Reach 90115 := rs (se 1 (by rfl) ⟨67586, by rfl⟩) R135173
theorem R221201 : Reach 221201 := rs (se 2 (by rfl) ⟨82950, by rfl⟩) R165901
theorem R90131 : Reach 90131 := rs (se 1 (by rfl) ⟨67598, by rfl⟩) R135197
theorem R90147 : Reach 90147 := rs (se 1 (by rfl) ⟨67610, by rfl⟩) R135221
theorem R90163 : Reach 90163 := rs (se 1 (by rfl) ⟨67622, by rfl⟩) R135245
theorem R221251 : Reach 221251 := rs (se 1 (by rfl) ⟨165938, by rfl⟩) R331877
theorem R90179 : Reach 90179 := rs (se 1 (by rfl) ⟨67634, by rfl⟩) R135269
theorem R90195 : Reach 90195 := rs (se 1 (by rfl) ⟨67646, by rfl⟩) R135293
theorem R90211 : Reach 90211 := rs (se 1 (by rfl) ⟨67658, by rfl⟩) R135317
theorem R90227 : Reach 90227 := rs (se 1 (by rfl) ⟨67670, by rfl⟩) R135341
theorem R90243 : Reach 90243 := rs (se 1 (by rfl) ⟨67682, by rfl⟩) R135365
theorem R188561 : Reach 188561 := rs (se 2 (by rfl) ⟨70710, by rfl⟩) R141421
theorem R90259 : Reach 90259 := rs (se 1 (by rfl) ⟨67694, by rfl⟩) R135389
theorem R90275 : Reach 90275 := rs (se 1 (by rfl) ⟨67706, by rfl⟩) R135413
theorem R90291 : Reach 90291 := rs (se 1 (by rfl) ⟨67718, by rfl⟩) R135437
theorem R90307 : Reach 90307 := rs (se 1 (by rfl) ⟨67730, by rfl⟩) R135461
theorem R516293 : Reach 516293 := rs (se 4 (by rfl) ⟨48402, by rfl⟩) R96805
theorem R221393 : Reach 221393 := rs (se 2 (by rfl) ⟨83022, by rfl⟩) R166045
theorem R90323 : Reach 90323 := rs (se 1 (by rfl) ⟨67742, by rfl⟩) R135485
theorem R90339 : Reach 90339 := rs (se 1 (by rfl) ⟨67754, by rfl⟩) R135509
theorem R90355 : Reach 90355 := rs (se 1 (by rfl) ⟨67766, by rfl⟩) R135533
theorem R90371 : Reach 90371 := rs (se 1 (by rfl) ⟨67778, by rfl⟩) R135557
theorem R286993 : Reach 286993 := rs (se 2 (by rfl) ⟨107622, by rfl⟩) R215245
theorem R90387 : Reach 90387 := rs (se 1 (by rfl) ⟨67790, by rfl⟩) R135581
theorem R90403 : Reach 90403 := rs (se 1 (by rfl) ⟨67802, by rfl⟩) R135605
theorem R90419 : Reach 90419 := rs (se 1 (by rfl) ⟨67814, by rfl⟩) R135629
theorem R90435 : Reach 90435 := rs (se 1 (by rfl) ⟨67826, by rfl⟩) R135653
theorem R254285 : Reach 254285 := rs (se 3 (by rfl) ⟨47678, by rfl⟩) R95357
theorem R385357 : Reach 385357 := rs (se 3 (by rfl) ⟨72254, by rfl⟩) R144509
theorem R90451 : Reach 90451 := rs (se 1 (by rfl) ⟨67838, by rfl⟩) R135677
theorem R90467 : Reach 90467 := rs (se 1 (by rfl) ⟨67850, by rfl⟩) R135701
theorem R90483 : Reach 90483 := rs (se 1 (by rfl) ⟨67862, by rfl⟩) R135725
theorem R90499 : Reach 90499 := rs (se 1 (by rfl) ⟨67874, by rfl⟩) R135749
theorem R614789 : Reach 614789 := rs (se 4 (by rfl) ⟨57636, by rfl⟩) R115273
theorem R483725 : Reach 483725 := rs (se 3 (by rfl) ⟨90698, by rfl⟩) R181397
theorem R254353 : Reach 254353 := rs (se 2 (by rfl) ⟨95382, by rfl⟩) R190765
theorem R90515 : Reach 90515 := rs (se 1 (by rfl) ⟨67886, by rfl⟩) R135773
theorem R90531 : Reach 90531 := rs (se 1 (by rfl) ⟨67898, by rfl⟩) R135797
theorem R90547 : Reach 90547 := rs (se 1 (by rfl) ⟨67910, by rfl⟩) R135821
theorem R90563 : Reach 90563 := rs (se 1 (by rfl) ⟨67922, by rfl⟩) R135845
theorem R90579 : Reach 90579 := rs (se 1 (by rfl) ⟨67934, by rfl⟩) R135869
theorem R90595 : Reach 90595 := rs (se 1 (by rfl) ⟨67946, by rfl⟩) R135893
theorem R90611 : Reach 90611 := rs (se 1 (by rfl) ⟨67958, by rfl⟩) R135917
theorem R90627 : Reach 90627 := rs (se 1 (by rfl) ⟨67970, by rfl⟩) R135941
theorem R90643 : Reach 90643 := rs (se 1 (by rfl) ⟨67982, by rfl⟩) R135965
theorem R188963 : Reach 188963 := rs (se 1 (by rfl) ⟨141722, by rfl⟩) R283445
theorem R90659 : Reach 90659 := rs (se 1 (by rfl) ⟨67994, by rfl⟩) R135989
theorem R90675 : Reach 90675 := rs (se 1 (by rfl) ⟨68006, by rfl⟩) R136013
theorem R90691 : Reach 90691 := rs (se 1 (by rfl) ⟨68018, by rfl⟩) R136037
theorem R90707 : Reach 90707 := rs (se 1 (by rfl) ⟨68030, by rfl⟩) R136061
theorem R90723 : Reach 90723 := rs (se 1 (by rfl) ⟨68042, by rfl⟩) R136085
theorem R90739 : Reach 90739 := rs (se 1 (by rfl) ⟨68054, by rfl⟩) R136109
theorem R90755 : Reach 90755 := rs (se 1 (by rfl) ⟨68066, by rfl⟩) R136133
theorem R90771 : Reach 90771 := rs (se 1 (by rfl) ⟨68078, by rfl⟩) R136157
theorem R254627 : Reach 254627 := rs (se 1 (by rfl) ⟨190970, by rfl⟩) R381941
theorem R90787 : Reach 90787 := rs (se 1 (by rfl) ⟨68090, by rfl⟩) R136181
theorem R90803 : Reach 90803 := rs (se 1 (by rfl) ⟨68102, by rfl⟩) R136205
theorem R90819 : Reach 90819 := rs (se 1 (by rfl) ⟨68114, by rfl⟩) R136229
theorem R90835 : Reach 90835 := rs (se 1 (by rfl) ⟨68126, by rfl⟩) R136253
theorem R90851 : Reach 90851 := rs (se 1 (by rfl) ⟨68138, by rfl⟩) R136277
theorem R90867 : Reach 90867 := rs (se 1 (by rfl) ⟨68150, by rfl⟩) R136301
theorem R90883 : Reach 90883 := rs (se 1 (by rfl) ⟨68162, by rfl⟩) R136325
theorem R90899 : Reach 90899 := rs (se 1 (by rfl) ⟨68174, by rfl⟩) R136349
theorem R90915 : Reach 90915 := rs (se 1 (by rfl) ⟨68186, by rfl⟩) R136373
theorem R90931 : Reach 90931 := rs (se 1 (by rfl) ⟨68198, by rfl⟩) R136397
theorem R90947 : Reach 90947 := rs (se 1 (by rfl) ⟨68210, by rfl⟩) R136421
theorem R90963 : Reach 90963 := rs (se 1 (by rfl) ⟨68222, by rfl⟩) R136445
theorem R90979 : Reach 90979 := rs (se 1 (by rfl) ⟨68234, by rfl⟩) R136469
theorem R1991537 : Reach 1991537 := rs (se 2 (by rfl) ⟨746826, by rfl⟩) R1493653
theorem R90995 : Reach 90995 := rs (se 1 (by rfl) ⟨68246, by rfl⟩) R136493
theorem R91011 : Reach 91011 := rs (se 1 (by rfl) ⟨68258, by rfl⟩) R136517
theorem R91027 : Reach 91027 := rs (se 1 (by rfl) ⟨68270, by rfl⟩) R136541
theorem R91043 : Reach 91043 := rs (se 1 (by rfl) ⟨68282, by rfl⟩) R136565
theorem R91059 : Reach 91059 := rs (se 1 (by rfl) ⟨68294, by rfl⟩) R136589
theorem R91075 : Reach 91075 := rs (se 1 (by rfl) ⟨68306, by rfl⟩) R136613
theorem R418765 : Reach 418765 := rs (se 3 (by rfl) ⟨78518, by rfl⟩) R157037
theorem R91091 : Reach 91091 := rs (se 1 (by rfl) ⟨68318, by rfl⟩) R136637
theorem R91107 : Reach 91107 := rs (se 1 (by rfl) ⟨68330, by rfl⟩) R136661
theorem R91123 : Reach 91123 := rs (se 1 (by rfl) ⟨68342, by rfl⟩) R136685
theorem R222385 : Reach 222385 := rs (se 2 (by rfl) ⟨83394, by rfl⟩) R166789
theorem R189859 : Reach 189859 := rs (se 1 (by rfl) ⟨142394, by rfl⟩) R284789
theorem R222659 : Reach 222659 := rs (se 1 (by rfl) ⟨166994, by rfl⟩) R333989
theorem R583109 : Reach 583109 := rs (se 4 (by rfl) ⟨54666, by rfl⟩) R109333
theorem R255469 : Reach 255469 := rs (se 3 (by rfl) ⟨47900, by rfl⟩) R95801
theorem R222851 : Reach 222851 := rs (se 1 (by rfl) ⟨167138, by rfl⟩) R334277
theorem R255629 : Reach 255629 := rs (se 3 (by rfl) ⟨47930, by rfl⟩) R95861
theorem R124625 : Reach 124625 := rs (se 2 (by rfl) ⟨46734, by rfl⟩) R93469
theorem R91955 : Reach 91955 := rs (se 1 (by rfl) ⟨68966, by rfl⟩) R137933
theorem R255811 : Reach 255811 := rs (se 1 (by rfl) ⟨191858, by rfl⟩) R383717
theorem R452465 : Reach 452465 := rs (se 2 (by rfl) ⟨169674, by rfl⟩) R339349
theorem R92227 : Reach 92227 := rs (se 1 (by rfl) ⟨69170, by rfl⟩) R138341
theorem R125155 : Reach 125155 := rs (se 1 (by rfl) ⟨93866, by rfl⟩) R187733
theorem R223793 : Reach 223793 := rs (se 2 (by rfl) ⟨83922, by rfl⟩) R167845
theorem R125491 : Reach 125491 := rs (se 1 (by rfl) ⟨94118, by rfl⟩) R188237
theorem R289379 : Reach 289379 := rs (se 1 (by rfl) ⟨217034, by rfl⟩) R434069
theorem R223843 : Reach 223843 := rs (se 1 (by rfl) ⟨167882, by rfl⟩) R335765
theorem R191089 : Reach 191089 := rs (se 2 (by rfl) ⟨71658, by rfl⟩) R143317
theorem R191203 : Reach 191203 := rs (se 1 (by rfl) ⟨143402, by rfl⟩) R286805
theorem R223985 : Reach 223985 := rs (se 2 (by rfl) ⟨83994, by rfl⟩) R167989
theorem R93187 : Reach 93187 := rs (se 1 (by rfl) ⟨69890, by rfl⟩) R139781
theorem R126049 : Reach 126049 := rs (se 2 (by rfl) ⟨47268, by rfl⟩) R94537
theorem R126083 : Reach 126083 := rs (se 1 (by rfl) ⟨94562, by rfl⟩) R189125
theorem R158897 : Reach 158897 := rs (se 2 (by rfl) ⟨59586, by rfl⟩) R119173
theorem R257201 : Reach 257201 := rs (se 2 (by rfl) ⟨96450, by rfl⟩) R192901
theorem R1109189 : Reach 1109189 := rs (se 4 (by rfl) ⟨103986, by rfl⟩) R207973
theorem R453923 : Reach 453923 := rs (se 1 (by rfl) ⟨340442, by rfl⟩) R680885
theorem R650693 : Reach 650693 := rs (se 4 (by rfl) ⟨61002, by rfl⟩) R122005
theorem R126641 : Reach 126641 := rs (se 2 (by rfl) ⟨47490, by rfl⟩) R94981
theorem R224977 : Reach 224977 := rs (se 2 (by rfl) ⟨84366, by rfl⟩) R168733
theorem R126721 : Reach 126721 := rs (se 2 (by rfl) ⟨47520, by rfl⟩) R95041
theorem R487309 : Reach 487309 := rs (se 3 (by rfl) ⟨91370, by rfl⟩) R182741
theorem R225251 : Reach 225251 := rs (se 1 (by rfl) ⟨168938, by rfl⟩) R337877
theorem R454733 : Reach 454733 := rs (se 3 (by rfl) ⟨85262, by rfl⟩) R170525
theorem R192593 : Reach 192593 := rs (se 2 (by rfl) ⟨72222, by rfl⟩) R144445
theorem R192611 : Reach 192611 := rs (se 1 (by rfl) ⟨144458, by rfl⟩) R288917
theorem R258157 : Reach 258157 := rs (se 3 (by rfl) ⟨48404, by rfl⟩) R96809
theorem R225443 : Reach 225443 := rs (se 1 (by rfl) ⟨169082, by rfl⟩) R338165
theorem R94451 : Reach 94451 := rs (se 1 (by rfl) ⟨70838, by rfl⟩) R141677
theorem R258385 : Reach 258385 := rs (se 2 (by rfl) ⟨96894, by rfl⟩) R193789
theorem R258545 : Reach 258545 := rs (se 2 (by rfl) ⟨96954, by rfl⟩) R193909
theorem R127507 : Reach 127507 := rs (se 1 (by rfl) ⟨95630, by rfl⟩) R191261
theorem R291377 : Reach 291377 := rs (se 2 (by rfl) ⟨109266, by rfl⟩) R218533
theorem R258659 : Reach 258659 := rs (se 1 (by rfl) ⟨193994, by rfl⟩) R387989
theorem R160483 : Reach 160483 := rs (se 1 (by rfl) ⟨120362, by rfl⟩) R240725
theorem R389873 : Reach 389873 := rs (se 2 (by rfl) ⟨146202, by rfl⟩) R292405
theorem R1143665 : Reach 1143665 := rs (se 2 (by rfl) ⟨428874, by rfl⟩) R857749
theorem R488369 : Reach 488369 := rs (se 2 (by rfl) ⟨183138, by rfl⟩) R366277
theorem R95203 : Reach 95203 := rs (se 1 (by rfl) ⟨71402, by rfl⟩) R142805
theorem R127985 : Reach 127985 := rs (se 2 (by rfl) ⟨47994, by rfl⟩) R95989
theorem R128065 : Reach 128065 := rs (se 2 (by rfl) ⟨48024, by rfl⟩) R96049
theorem R226385 : Reach 226385 := rs (se 2 (by rfl) ⟨84894, by rfl⟩) R169789
theorem R128099 : Reach 128099 := rs (se 1 (by rfl) ⟨96074, by rfl⟩) R192149
theorem R226435 : Reach 226435 := rs (se 1 (by rfl) ⟨169826, by rfl⟩) R339653
theorem R128179 : Reach 128179 := rs (se 1 (by rfl) ⟨96134, by rfl⟩) R192269
theorem R226577 : Reach 226577 := rs (se 2 (by rfl) ⟨84966, by rfl⟩) R169933
theorem R128737 : Reach 128737 := rs (se 2 (by rfl) ⟨48276, by rfl⟩) R96553
theorem R522125 : Reach 522125 := rs (se 3 (by rfl) ⟨97898, by rfl⟩) R195797
theorem R96211 : Reach 96211 := rs (se 1 (by rfl) ⟨72158, by rfl⟩) R144317
theorem R194609 : Reach 194609 := rs (se 2 (by rfl) ⟨72978, by rfl⟩) R145957
theorem R325795 : Reach 325795 := rs (se 1 (by rfl) ⟨244346, by rfl⟩) R488693
theorem R1308869 : Reach 1308869 := rs (se 4 (by rfl) ⟨122706, by rfl⟩) R245413
theorem R2291939 : Reach 2291939 := rs (se 1 (by rfl) ⟨1718954, by rfl⟩) R3437909
theorem R227569 : Reach 227569 := rs (se 2 (by rfl) ⟨85338, by rfl⟩) R170677
theorem R489797 : Reach 489797 := rs (se 4 (by rfl) ⟨45918, by rfl⟩) R91837
theorem R129443 : Reach 129443 := rs (se 1 (by rfl) ⟨97082, by rfl⟩) R194165
theorem R227843 : Reach 227843 := rs (se 1 (by rfl) ⟨170882, by rfl⟩) R341765
theorem R2423317 : Reach 2423317 := rs (se 6 (by rfl) ⟨56796, by rfl⟩) R113593
theorem R359075 : Reach 359075 := rs (se 1 (by rfl) ⟨269306, by rfl⟩) R538613
theorem R228035 : Reach 228035 := rs (se 1 (by rfl) ⟨171026, by rfl⟩) R342053
theorem R260995 : Reach 260995 := rs (se 1 (by rfl) ⟨195746, by rfl⟩) R391493
theorem R457649 : Reach 457649 := rs (se 2 (by rfl) ⟨171618, by rfl⟩) R343237
theorem R97219 : Reach 97219 := rs (se 1 (by rfl) ⟨72914, by rfl⟩) R145829
theorem R293969 : Reach 293969 := rs (se 2 (by rfl) ⟨110238, by rfl⟩) R220477
theorem R687203 : Reach 687203 := rs (se 1 (by rfl) ⟨515402, by rfl⟩) R1030805
theorem R294083 : Reach 294083 := rs (se 1 (by rfl) ⟨220562, by rfl⟩) R441125
theorem R1441165 : Reach 1441165 := rs (se 3 (by rfl) ⟨270218, by rfl⟩) R540437
theorem R294353 : Reach 294353 := rs (se 2 (by rfl) ⟨110382, by rfl⟩) R220765
theorem R196145 : Reach 196145 := rs (se 2 (by rfl) ⟨73554, by rfl⟩) R147109
theorem R196163 : Reach 196163 := rs (se 1 (by rfl) ⟨147122, by rfl⟩) R294245
theorem R228977 : Reach 228977 := rs (se 2 (by rfl) ⟨85866, by rfl⟩) R171733
theorem R654961 : Reach 654961 := rs (se 2 (by rfl) ⟨245610, by rfl⟩) R491221
theorem R130721 : Reach 130721 := rs (se 2 (by rfl) ⟨49020, by rfl⟩) R98041
theorem R229027 : Reach 229027 := rs (se 1 (by rfl) ⟨171770, by rfl⟩) R343541
theorem R130739 : Reach 130739 := rs (se 1 (by rfl) ⟨98054, by rfl⟩) R196109
theorem R130769 : Reach 130769 := rs (se 2 (by rfl) ⟨49038, by rfl⟩) R98077
theorem R130787 : Reach 130787 := rs (se 1 (by rfl) ⟨98090, by rfl⟩) R196181
theorem R655075 : Reach 655075 := rs (se 1 (by rfl) ⟨491306, by rfl⟩) R982613
theorem R130817 : Reach 130817 := rs (se 2 (by rfl) ⟨49056, by rfl⟩) R98113
theorem R753421 : Reach 753421 := rs (se 3 (by rfl) ⟨141266, by rfl⟩) R282533
theorem R130835 : Reach 130835 := rs (se 1 (by rfl) ⟨98126, by rfl⟩) R196253
theorem R130865 : Reach 130865 := rs (se 2 (by rfl) ⟨49074, by rfl⟩) R98149
theorem R229169 : Reach 229169 := rs (se 2 (by rfl) ⟨85938, by rfl⟩) R171877
theorem R130883 : Reach 130883 := rs (se 1 (by rfl) ⟨98162, by rfl⟩) R196325
theorem R196433 : Reach 196433 := rs (se 2 (by rfl) ⟨73662, by rfl⟩) R147325
theorem R98131 : Reach 98131 := rs (se 1 (by rfl) ⟨73598, by rfl⟩) R147197
theorem R130913 : Reach 130913 := rs (se 2 (by rfl) ⟨49092, by rfl⟩) R98185
theorem R196451 : Reach 196451 := rs (se 1 (by rfl) ⟨147338, by rfl⟩) R294677
theorem R130931 : Reach 130931 := rs (se 1 (by rfl) ⟨98198, by rfl⟩) R196397
theorem R130961 : Reach 130961 := rs (se 2 (by rfl) ⟨49110, by rfl⟩) R98221
theorem R130979 : Reach 130979 := rs (se 1 (by rfl) ⟨98234, by rfl⟩) R196469
theorem R131009 : Reach 131009 := rs (se 2 (by rfl) ⟨49128, by rfl⟩) R98257
theorem R131027 : Reach 131027 := rs (se 1 (by rfl) ⟨98270, by rfl⟩) R196541
theorem R98275 : Reach 98275 := rs (se 1 (by rfl) ⟨73706, by rfl⟩) R147413
theorem R294893 : Reach 294893 := rs (se 3 (by rfl) ⟨55292, by rfl⟩) R110585
theorem R131057 : Reach 131057 := rs (se 2 (by rfl) ⟨49146, by rfl⟩) R98293
theorem R196631 : Reach 196631 := rs (se 1 (by rfl) ⟨147473, by rfl⟩) R294947
theorem R98347 : Reach 98347 := rs (se 1 (by rfl) ⟨73760, by rfl⟩) R147521
theorem R131147 : Reach 131147 := rs (se 1 (by rfl) ⟨98360, by rfl⟩) R196721
theorem R131159 : Reach 131159 := rs (se 1 (by rfl) ⟨98369, by rfl⟩) R196739
theorem R295001 : Reach 295001 := rs (se 2 (by rfl) ⟨110625, by rfl⟩) R221251
theorem R98455 : Reach 98455 := rs (se 1 (by rfl) ⟨73841, by rfl⟩) R147683
theorem R131225 : Reach 131225 := rs (se 2 (by rfl) ⟨49209, by rfl⟩) R98419
theorem R196811 : Reach 196811 := rs (se 1 (by rfl) ⟨147608, by rfl⟩) R295217
theorem R196865 : Reach 196865 := rs (se 2 (by rfl) ⟨73824, by rfl⟩) R147649
theorem R131339 : Reach 131339 := rs (se 1 (by rfl) ⟨98504, by rfl⟩) R197009
theorem R131351 : Reach 131351 := rs (se 1 (by rfl) ⟨98513, by rfl⟩) R197027
theorem R229655 : Reach 229655 := rs (se 1 (by rfl) ⟨172241, by rfl⟩) R344483
theorem R98635 : Reach 98635 := rs (se 1 (by rfl) ⟨73976, by rfl⟩) R147953
theorem R131417 : Reach 131417 := rs (se 2 (by rfl) ⟨49281, by rfl⟩) R98563
theorem R98743 : Reach 98743 := rs (se 1 (by rfl) ⟨74057, by rfl⟩) R148115
theorem R131531 : Reach 131531 := rs (se 1 (by rfl) ⟨98648, by rfl⟩) R197297
theorem R131543 : Reach 131543 := rs (se 1 (by rfl) ⟨98657, by rfl⟩) R197315
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R131609 : Reach 131609 := rs (se 2 (by rfl) ⟨49353, by rfl⟩) R98707
theorem R197171 : Reach 197171 := rs (se 1 (by rfl) ⟨147878, by rfl⟩) R295757
theorem R197207 : Reach 197207 := rs (se 1 (by rfl) ⟨147905, by rfl⟩) R295811
theorem R98923 : Reach 98923 := rs (se 1 (by rfl) ⟨74192, by rfl⟩) R148385
theorem R1049219 : Reach 1049219 := rs (se 1 (by rfl) ⟨786914, by rfl⟩) R1573829
theorem R131723 : Reach 131723 := rs (se 1 (by rfl) ⟨98792, by rfl⟩) R197585
theorem R131735 : Reach 131735 := rs (se 1 (by rfl) ⟨98801, by rfl⟩) R197603
theorem R426647 : Reach 426647 := rs (se 1 (by rfl) ⟨319985, by rfl⟩) R639971
theorem R99031 : Reach 99031 := rs (se 1 (by rfl) ⟨74273, by rfl⟩) R148547
theorem R131801 : Reach 131801 := rs (se 2 (by rfl) ⟨49425, by rfl⟩) R98851
theorem R197387 : Reach 197387 := rs (se 1 (by rfl) ⟨148040, by rfl⟩) R296081
theorem R295703 : Reach 295703 := rs (se 1 (by rfl) ⟨221777, by rfl⟩) R443555
theorem R197441 : Reach 197441 := rs (se 2 (by rfl) ⟨74040, by rfl⟩) R148081
theorem R131915 : Reach 131915 := rs (se 1 (by rfl) ⟨98936, by rfl⟩) R197873
theorem R131927 : Reach 131927 := rs (se 1 (by rfl) ⟨98945, by rfl⟩) R197891
theorem R99211 : Reach 99211 := rs (se 1 (by rfl) ⟨74408, by rfl⟩) R148817
theorem R131993 : Reach 131993 := rs (se 2 (by rfl) ⟨49497, by rfl⟩) R98995
theorem R230323 : Reach 230323 := rs (se 1 (by rfl) ⟨172742, by rfl⟩) R345485
theorem R99319 : Reach 99319 := rs (se 1 (by rfl) ⟨74489, by rfl⟩) R148979
theorem R132107 : Reach 132107 := rs (se 1 (by rfl) ⟨99080, by rfl⟩) R198161
theorem R132119 : Reach 132119 := rs (se 1 (by rfl) ⟨99089, by rfl⟩) R198179
theorem R197657 : Reach 197657 := rs (se 2 (by rfl) ⟨74121, by rfl⟩) R148243
theorem R230465 : Reach 230465 := rs (se 2 (by rfl) ⟨86424, by rfl⟩) R172849
theorem R132185 : Reach 132185 := rs (se 2 (by rfl) ⟨49569, by rfl⟩) R99139
theorem R197747 : Reach 197747 := rs (se 1 (by rfl) ⟨148310, by rfl⟩) R296621
theorem R197783 : Reach 197783 := rs (se 1 (by rfl) ⟨148337, by rfl⟩) R296675
theorem R99499 : Reach 99499 := rs (se 1 (by rfl) ⟨74624, by rfl⟩) R149249
theorem R132299 : Reach 132299 := rs (se 1 (by rfl) ⟨99224, by rfl⟩) R198449
theorem R132311 : Reach 132311 := rs (se 1 (by rfl) ⟨99233, by rfl⟩) R198467
theorem R558353 : Reach 558353 := rs (se 2 (by rfl) ⟨209382, by rfl⟩) R418765
theorem R99607 : Reach 99607 := rs (se 1 (by rfl) ⟨74705, by rfl⟩) R149411
theorem R132377 : Reach 132377 := rs (se 2 (by rfl) ⟨49641, by rfl⟩) R99283
theorem R296243 : Reach 296243 := rs (se 1 (by rfl) ⟨222182, by rfl⟩) R444365
theorem R197963 : Reach 197963 := rs (se 1 (by rfl) ⟨148472, by rfl⟩) R296945
theorem R198017 : Reach 198017 := rs (se 2 (by rfl) ⟨74256, by rfl⟩) R148513
theorem R132491 : Reach 132491 := rs (se 1 (by rfl) ⟨99368, by rfl⟩) R198737
theorem R132503 : Reach 132503 := rs (se 1 (by rfl) ⟨99377, by rfl⟩) R198755
theorem R99787 : Reach 99787 := rs (se 1 (by rfl) ⟨74840, by rfl⟩) R149681
theorem R132569 : Reach 132569 := rs (se 2 (by rfl) ⟨49713, by rfl⟩) R99427
theorem R99895 : Reach 99895 := rs (se 1 (by rfl) ⟨74921, by rfl⟩) R149843
theorem R296513 : Reach 296513 := rs (se 2 (by rfl) ⟨111192, by rfl⟩) R222385
theorem R132683 : Reach 132683 := rs (se 1 (by rfl) ⟨99512, by rfl⟩) R199025
theorem R132695 : Reach 132695 := rs (se 1 (by rfl) ⟨99521, by rfl⟩) R199043
theorem R198233 : Reach 198233 := rs (se 2 (by rfl) ⟨74337, by rfl⟩) R148675
theorem R132761 : Reach 132761 := rs (se 2 (by rfl) ⟨49785, by rfl⟩) R99571
theorem R198323 : Reach 198323 := rs (se 1 (by rfl) ⟨148742, by rfl⟩) R297485
theorem R755405 : Reach 755405 := rs (se 3 (by rfl) ⟨141638, by rfl⟩) R283277
theorem R198359 : Reach 198359 := rs (se 1 (by rfl) ⟨148769, by rfl⟩) R297539
theorem R100075 : Reach 100075 := rs (se 1 (by rfl) ⟨75056, by rfl⟩) R150113
theorem R132875 : Reach 132875 := rs (se 1 (by rfl) ⟨99656, by rfl⟩) R199313
theorem R132887 : Reach 132887 := rs (se 1 (by rfl) ⟨99665, by rfl⟩) R199331
theorem R165719 : Reach 165719 := rs (se 1 (by rfl) ⟨124289, by rfl⟩) R248579
theorem R100183 : Reach 100183 := rs (se 1 (by rfl) ⟨75137, by rfl⟩) R150275
theorem R132953 : Reach 132953 := rs (se 2 (by rfl) ⟨49857, by rfl⟩) R99715
theorem R952165 : Reach 952165 := rs (se 4 (by rfl) ⟨89265, by rfl⟩) R178531
theorem R198539 : Reach 198539 := rs (se 1 (by rfl) ⟨148904, by rfl⟩) R297809
theorem R198593 : Reach 198593 := rs (se 2 (by rfl) ⟨74472, by rfl⟩) R148945
theorem R133067 : Reach 133067 := rs (se 1 (by rfl) ⟨99800, by rfl⟩) R199601
theorem R133079 : Reach 133079 := rs (se 1 (by rfl) ⟨99809, by rfl⟩) R199619
theorem R100363 : Reach 100363 := rs (se 1 (by rfl) ⟨75272, by rfl⟩) R150545
theorem R133145 : Reach 133145 := rs (se 2 (by rfl) ⟨49929, by rfl⟩) R99859
theorem R297053 : Reach 297053 := rs (se 3 (by rfl) ⟨55697, by rfl⟩) R111395
theorem R100471 : Reach 100471 := rs (se 1 (by rfl) ⟨75353, by rfl⟩) R150707
theorem R133259 : Reach 133259 := rs (se 1 (by rfl) ⟨99944, by rfl⟩) R199889
theorem R133271 : Reach 133271 := rs (se 1 (by rfl) ⟨99953, by rfl⟩) R199907
theorem R1312919 : Reach 1312919 := rs (se 1 (by rfl) ⟨984689, by rfl⟩) R1969379
theorem R198809 : Reach 198809 := rs (se 2 (by rfl) ⟨74553, by rfl⟩) R149107
theorem R362675 : Reach 362675 := rs (se 1 (by rfl) ⟨272006, by rfl⟩) R544013
theorem R133337 : Reach 133337 := rs (se 2 (by rfl) ⟨50001, by rfl⟩) R100003
theorem R198899 : Reach 198899 := rs (se 1 (by rfl) ⟨149174, by rfl⟩) R298349
theorem R198935 : Reach 198935 := rs (se 1 (by rfl) ⟨149201, by rfl⟩) R298403
theorem R100651 : Reach 100651 := rs (se 1 (by rfl) ⟨75488, by rfl⟩) R150977
theorem R166195 : Reach 166195 := rs (se 1 (by rfl) ⟨124646, by rfl⟩) R249293
theorem R919873 : Reach 919873 := rs (se 2 (by rfl) ⟨344952, by rfl⟩) R689905
theorem R133451 : Reach 133451 := rs (se 1 (by rfl) ⟨100088, by rfl⟩) R200177
theorem R723275 : Reach 723275 := rs (se 1 (by rfl) ⟨542456, by rfl⟩) R1084913
theorem R133463 : Reach 133463 := rs (se 1 (by rfl) ⟨100097, by rfl⟩) R200195
theorem R100759 : Reach 100759 := rs (se 1 (by rfl) ⟨75569, by rfl⟩) R151139
theorem R133529 : Reach 133529 := rs (se 2 (by rfl) ⟨50073, by rfl⟩) R100147
theorem R199115 : Reach 199115 := rs (se 1 (by rfl) ⟨149336, by rfl⟩) R298673
theorem R166387 : Reach 166387 := rs (se 1 (by rfl) ⟨124790, by rfl⟩) R249581
theorem R199169 : Reach 199169 := rs (se 2 (by rfl) ⟨74688, by rfl⟩) R149377
theorem R133643 : Reach 133643 := rs (se 1 (by rfl) ⟨100232, by rfl⟩) R200465
theorem R133655 : Reach 133655 := rs (se 1 (by rfl) ⟨100241, by rfl⟩) R200483
theorem R100939 : Reach 100939 := rs (se 1 (by rfl) ⟨75704, by rfl⟩) R151409
theorem R133721 : Reach 133721 := rs (se 2 (by rfl) ⟨50145, by rfl⟩) R100291
theorem R101047 : Reach 101047 := rs (se 1 (by rfl) ⟨75785, by rfl⟩) R151571
theorem R133835 : Reach 133835 := rs (se 1 (by rfl) ⟨100376, by rfl⟩) R200753
theorem R133847 : Reach 133847 := rs (se 1 (by rfl) ⟨100385, by rfl⟩) R200771
theorem R199385 : Reach 199385 := rs (se 2 (by rfl) ⟨74769, by rfl⟩) R149539
theorem R133913 : Reach 133913 := rs (se 2 (by rfl) ⟨50217, by rfl⟩) R100435
theorem R199475 : Reach 199475 := rs (se 1 (by rfl) ⟨149606, by rfl⟩) R299213
theorem R199511 : Reach 199511 := rs (se 1 (by rfl) ⟨149633, by rfl⟩) R299267
theorem R101227 : Reach 101227 := rs (se 1 (by rfl) ⟨75920, by rfl⟩) R151841
theorem R134027 : Reach 134027 := rs (se 1 (by rfl) ⟨100520, by rfl⟩) R201041
theorem R134039 : Reach 134039 := rs (se 1 (by rfl) ⟨100529, by rfl⟩) R201059
theorem R166835 : Reach 166835 := rs (se 1 (by rfl) ⟨125126, by rfl⟩) R250253
theorem R101335 : Reach 101335 := rs (se 1 (by rfl) ⟨76001, by rfl⟩) R152003
theorem R166873 : Reach 166873 := rs (se 2 (by rfl) ⟨62577, by rfl⟩) R125155
theorem R134105 : Reach 134105 := rs (se 2 (by rfl) ⟨50289, by rfl⟩) R100579
theorem R199691 : Reach 199691 := rs (se 1 (by rfl) ⟨149768, by rfl⟩) R299537
theorem R199745 : Reach 199745 := rs (se 2 (by rfl) ⟨74904, by rfl⟩) R149809
theorem R134219 : Reach 134219 := rs (se 1 (by rfl) ⟨100664, by rfl⟩) R201329
theorem R134231 : Reach 134231 := rs (se 1 (by rfl) ⟨100673, by rfl⟩) R201347
theorem R101515 : Reach 101515 := rs (se 1 (by rfl) ⟨76136, by rfl⟩) R152273
theorem R134297 : Reach 134297 := rs (se 2 (by rfl) ⟨50361, by rfl⟩) R100723
theorem R298187 : Reach 298187 := rs (se 1 (by rfl) ⟨223640, by rfl⟩) R447281
theorem R101623 : Reach 101623 := rs (se 1 (by rfl) ⟨76217, by rfl⟩) R152435
theorem R1019141 : Reach 1019141 := rs (se 4 (by rfl) ⟨95544, by rfl⟩) R191089
theorem R134411 : Reach 134411 := rs (se 1 (by rfl) ⟨100808, by rfl⟩) R201617
theorem R134423 : Reach 134423 := rs (se 1 (by rfl) ⟨100817, by rfl⟩) R201635
theorem R199961 : Reach 199961 := rs (se 2 (by rfl) ⟨74985, by rfl⟩) R149971
theorem R331073 : Reach 331073 := rs (se 2 (by rfl) ⟨124152, by rfl⟩) R248305
theorem R134489 : Reach 134489 := rs (se 2 (by rfl) ⟨50433, by rfl⟩) R100867
theorem R200051 : Reach 200051 := rs (se 1 (by rfl) ⟨150038, by rfl⟩) R300077
theorem R200087 : Reach 200087 := rs (se 1 (by rfl) ⟨150065, by rfl⟩) R300131
theorem R167321 : Reach 167321 := rs (se 2 (by rfl) ⟨62745, by rfl⟩) R125491
theorem R101803 : Reach 101803 := rs (se 1 (by rfl) ⟨76352, by rfl⟩) R152705
theorem R134603 : Reach 134603 := rs (se 1 (by rfl) ⟨100952, by rfl⟩) R201905
theorem R134615 : Reach 134615 := rs (se 1 (by rfl) ⟨100961, by rfl⟩) R201923
theorem R298457 : Reach 298457 := rs (se 2 (by rfl) ⟨111921, by rfl⟩) R223843
theorem R101911 : Reach 101911 := rs (se 1 (by rfl) ⟨76433, by rfl⟩) R152867
theorem R134681 : Reach 134681 := rs (se 2 (by rfl) ⟨50505, by rfl⟩) R101011
theorem R200267 : Reach 200267 := rs (se 1 (by rfl) ⟨150200, by rfl⟩) R300401
theorem R200321 : Reach 200321 := rs (se 2 (by rfl) ⟨75120, by rfl⟩) R150241
theorem R134795 : Reach 134795 := rs (se 1 (by rfl) ⟨101096, by rfl⟩) R202193
theorem R134807 : Reach 134807 := rs (se 1 (by rfl) ⟨101105, by rfl⟩) R202211
theorem R102091 : Reach 102091 := rs (se 1 (by rfl) ⟨76568, by rfl⟩) R153137
theorem R134873 : Reach 134873 := rs (se 2 (by rfl) ⟨50577, by rfl⟩) R101155
theorem R102199 : Reach 102199 := rs (se 1 (by rfl) ⟨76649, by rfl⟩) R153299
theorem R134987 : Reach 134987 := rs (se 1 (by rfl) ⟨101240, by rfl⟩) R202481
theorem R462667 : Reach 462667 := rs (se 1 (by rfl) ⟨347000, by rfl⟩) R694001
theorem R134999 : Reach 134999 := rs (se 1 (by rfl) ⟨101249, by rfl⟩) R202499
theorem R200537 : Reach 200537 := rs (se 2 (by rfl) ⟨75201, by rfl⟩) R150403
theorem R135065 : Reach 135065 := rs (se 2 (by rfl) ⟨50649, by rfl⟩) R101299
theorem R200627 : Reach 200627 := rs (se 1 (by rfl) ⟨150470, by rfl⟩) R300941
theorem R200663 : Reach 200663 := rs (se 1 (by rfl) ⟨150497, by rfl⟩) R300995
theorem R102379 : Reach 102379 := rs (se 1 (by rfl) ⟨76784, by rfl⟩) R153569
theorem R135179 : Reach 135179 := rs (se 1 (by rfl) ⟨101384, by rfl⟩) R202769
theorem R135191 : Reach 135191 := rs (se 1 (by rfl) ⟨101393, by rfl⟩) R202787
theorem R757795 : Reach 757795 := rs (se 1 (by rfl) ⟨568346, by rfl⟩) R1136693
theorem R102487 : Reach 102487 := rs (se 1 (by rfl) ⟨76865, by rfl⟩) R153731
theorem R135257 : Reach 135257 := rs (se 2 (by rfl) ⟨50721, by rfl⟩) R101443
theorem R168065 : Reach 168065 := rs (se 2 (by rfl) ⟨63024, by rfl⟩) R126049
theorem R200843 : Reach 200843 := rs (se 1 (by rfl) ⟨150632, by rfl⟩) R301265
theorem R299159 : Reach 299159 := rs (se 1 (by rfl) ⟨224369, by rfl⟩) R448739
theorem R200897 : Reach 200897 := rs (se 2 (by rfl) ⟨75336, by rfl⟩) R150673
theorem R135371 : Reach 135371 := rs (se 1 (by rfl) ⟨101528, by rfl⟩) R203057
theorem R135383 : Reach 135383 := rs (se 1 (by rfl) ⟨101537, by rfl⟩) R203075
theorem R135449 : Reach 135449 := rs (se 2 (by rfl) ⟨50793, by rfl⟩) R101587
theorem R168331 : Reach 168331 := rs (se 1 (by rfl) ⟨126248, by rfl⟩) R252497
theorem R135563 : Reach 135563 := rs (se 1 (by rfl) ⟨101672, by rfl⟩) R203345
theorem R135575 : Reach 135575 := rs (se 1 (by rfl) ⟨101681, by rfl⟩) R203363
theorem R201113 : Reach 201113 := rs (se 2 (by rfl) ⟨75417, by rfl⟩) R150835
theorem R364979 : Reach 364979 := rs (se 1 (by rfl) ⟨273734, by rfl⟩) R547469
theorem R463283 : Reach 463283 := rs (se 1 (by rfl) ⟨347462, by rfl⟩) R694925
theorem R135641 : Reach 135641 := rs (se 2 (by rfl) ⟨50865, by rfl⟩) R101731
theorem R201203 : Reach 201203 := rs (se 1 (by rfl) ⟨150902, by rfl⟩) R301805
theorem R201239 : Reach 201239 := rs (se 1 (by rfl) ⟨150929, by rfl⟩) R301859
theorem R332333 : Reach 332333 := rs (se 3 (by rfl) ⟨62312, by rfl⟩) R124625
theorem R332363 : Reach 332363 := rs (se 1 (by rfl) ⟨249272, by rfl⟩) R498545
theorem R135755 : Reach 135755 := rs (se 1 (by rfl) ⟨101816, by rfl⟩) R203633
theorem R135767 : Reach 135767 := rs (se 1 (by rfl) ⟨101825, by rfl⟩) R203651
theorem R135833 : Reach 135833 := rs (se 2 (by rfl) ⟨50937, by rfl⟩) R101875
theorem R299699 : Reach 299699 := rs (se 1 (by rfl) ⟨224774, by rfl⟩) R449549
theorem R201419 : Reach 201419 := rs (se 1 (by rfl) ⟨151064, by rfl⟩) R302129
theorem R201473 : Reach 201473 := rs (se 2 (by rfl) ⟨75552, by rfl⟩) R151105
theorem R135947 : Reach 135947 := rs (se 1 (by rfl) ⟨101960, by rfl⟩) R203921
theorem R135959 : Reach 135959 := rs (se 1 (by rfl) ⟨101969, by rfl⟩) R203939
theorem R168779 : Reach 168779 := rs (se 1 (by rfl) ⟨126584, by rfl⟩) R253169
theorem R136025 : Reach 136025 := rs (se 2 (by rfl) ⟨51009, by rfl⟩) R102019
theorem R299969 : Reach 299969 := rs (se 2 (by rfl) ⟨112488, by rfl⟩) R224977
theorem R332747 : Reach 332747 := rs (se 1 (by rfl) ⟨249560, by rfl⟩) R499121
theorem R136139 : Reach 136139 := rs (se 1 (by rfl) ⟨102104, by rfl⟩) R204209
theorem R136151 : Reach 136151 := rs (se 1 (by rfl) ⟨102113, by rfl⟩) R204227
theorem R201689 : Reach 201689 := rs (se 2 (by rfl) ⟨75633, by rfl⟩) R151267
theorem R168961 : Reach 168961 := rs (se 2 (by rfl) ⟨63360, by rfl⟩) R126721
theorem R136217 : Reach 136217 := rs (se 2 (by rfl) ⟨51081, by rfl⟩) R102163
theorem R201779 : Reach 201779 := rs (se 1 (by rfl) ⟨151334, by rfl⟩) R302669
theorem R201815 : Reach 201815 := rs (se 1 (by rfl) ⟨151361, by rfl⟩) R302723
theorem R136331 : Reach 136331 := rs (se 1 (by rfl) ⟨102248, by rfl⟩) R204497
theorem R136343 : Reach 136343 := rs (se 1 (by rfl) ⟨102257, by rfl⟩) R204515
theorem R333017 : Reach 333017 := rs (se 2 (by rfl) ⟨124881, by rfl⟩) R249763
theorem R136409 : Reach 136409 := rs (se 2 (by rfl) ⟨51153, by rfl⟩) R102307
theorem R201995 : Reach 201995 := rs (se 1 (by rfl) ⟨151496, by rfl⟩) R302993
theorem R202049 : Reach 202049 := rs (se 2 (by rfl) ⟨75768, by rfl⟩) R151537
theorem R136523 : Reach 136523 := rs (se 1 (by rfl) ⟨102392, by rfl⟩) R204785
theorem R169303 : Reach 169303 := rs (se 1 (by rfl) ⟨126977, by rfl⟩) R253955
theorem R136535 : Reach 136535 := rs (se 1 (by rfl) ⟨102401, by rfl⟩) R204803
theorem R136601 : Reach 136601 := rs (se 2 (by rfl) ⟨51225, by rfl⟩) R102451
theorem R300509 : Reach 300509 := rs (se 3 (by rfl) ⟨56345, by rfl⟩) R112691
theorem R333335 : Reach 333335 := rs (se 1 (by rfl) ⟨250001, by rfl⟩) R500003
theorem R202265 : Reach 202265 := rs (se 2 (by rfl) ⟨75849, by rfl⟩) R151699
theorem R169523 : Reach 169523 := rs (se 1 (by rfl) ⟨127142, by rfl⟩) R254285
theorem R202355 : Reach 202355 := rs (se 1 (by rfl) ⟨151766, by rfl⟩) R303533
theorem R202391 : Reach 202391 := rs (se 1 (by rfl) ⟨151793, by rfl⟩) R303587
theorem R169751 : Reach 169751 := rs (se 1 (by rfl) ⟨127313, by rfl⟩) R254627
theorem R202571 : Reach 202571 := rs (se 1 (by rfl) ⟨151928, by rfl⟩) R303857
theorem R202625 : Reach 202625 := rs (se 2 (by rfl) ⟨75984, by rfl⟩) R151969
theorem R202775 : Reach 202775 := rs (se 1 (by rfl) ⟨152081, by rfl⟩) R304163
theorem R170009 : Reach 170009 := rs (se 2 (by rfl) ⟨63753, by rfl⟩) R127507
theorem R137303 : Reach 137303 := rs (se 1 (by rfl) ⟨102977, by rfl⟩) R205955
theorem R137305 : Reach 137305 := rs (se 2 (by rfl) ⟨51489, by rfl⟩) R102979
theorem R202841 : Reach 202841 := rs (se 2 (by rfl) ⟨76065, by rfl⟩) R152131
theorem R334003 : Reach 334003 := rs (se 1 (by rfl) ⟨250502, by rfl⟩) R501005
theorem R202931 : Reach 202931 := rs (se 1 (by rfl) ⟨152198, by rfl⟩) R304397
theorem R202967 : Reach 202967 := rs (se 1 (by rfl) ⟨152225, by rfl⟩) R304451
theorem R399581 : Reach 399581 := rs (se 3 (by rfl) ⟨74921, by rfl⟩) R149843
theorem R203147 : Reach 203147 := rs (se 1 (by rfl) ⟨152360, by rfl⟩) R304721
theorem R170419 : Reach 170419 := rs (se 1 (by rfl) ⟨127814, by rfl⟩) R255629
theorem R203201 : Reach 203201 := rs (se 2 (by rfl) ⟨76200, by rfl⟩) R152401
theorem R301643 : Reach 301643 := rs (se 1 (by rfl) ⟨226232, by rfl⟩) R452465
theorem R203417 : Reach 203417 := rs (se 2 (by rfl) ⟨76281, by rfl⟩) R152563
theorem R203507 : Reach 203507 := rs (se 1 (by rfl) ⟨152630, by rfl⟩) R305261
theorem R170753 : Reach 170753 := rs (se 2 (by rfl) ⟨64032, by rfl⟩) R128065
theorem R203543 : Reach 203543 := rs (se 1 (by rfl) ⟨152657, by rfl⟩) R305315
theorem R301913 : Reach 301913 := rs (se 2 (by rfl) ⟨113217, by rfl⟩) R226435
theorem R170905 : Reach 170905 := rs (se 2 (by rfl) ⟨64089, by rfl⟩) R128179
theorem R203723 : Reach 203723 := rs (se 1 (by rfl) ⟨152792, by rfl⟩) R305585
theorem R203777 : Reach 203777 := rs (se 2 (by rfl) ⟨76416, by rfl⟩) R152833
theorem R629765 : Reach 629765 := rs (se 4 (by rfl) ⟨59040, by rfl⟩) R118081
theorem R203993 : Reach 203993 := rs (se 2 (by rfl) ⟨76497, by rfl⟩) R152995
theorem R957701 : Reach 957701 := rs (se 4 (by rfl) ⟨89784, by rfl⟩) R179569
theorem R400657 : Reach 400657 := rs (se 2 (by rfl) ⟨150246, by rfl⟩) R300493
theorem R597293 : Reach 597293 := rs (se 3 (by rfl) ⟨111992, by rfl⟩) R223985
theorem R204083 : Reach 204083 := rs (se 1 (by rfl) ⟨153062, by rfl⟩) R306125
theorem R204119 : Reach 204119 := rs (se 1 (by rfl) ⟨153089, by rfl⟩) R306179
theorem R367961 : Reach 367961 := rs (se 2 (by rfl) ⟨137985, by rfl⟩) R275971
theorem R335249 : Reach 335249 := rs (se 2 (by rfl) ⟨125718, by rfl⟩) R251437
theorem R105931 : Reach 105931 := rs (se 1 (by rfl) ⟨79448, by rfl⟩) R158897
theorem R171467 : Reach 171467 := rs (se 1 (by rfl) ⟨128600, by rfl⟩) R257201
theorem R204299 : Reach 204299 := rs (se 1 (by rfl) ⟨153224, by rfl⟩) R306449
theorem R302615 : Reach 302615 := rs (se 1 (by rfl) ⟨226961, by rfl⟩) R453923
theorem R204353 : Reach 204353 := rs (se 2 (by rfl) ⟨76632, by rfl⟩) R153265
theorem R368221 : Reach 368221 := rs (se 3 (by rfl) ⟨69041, by rfl⟩) R138083
theorem R171649 : Reach 171649 := rs (se 2 (by rfl) ⟨64368, by rfl⟩) R128737
theorem R401041 : Reach 401041 := rs (se 2 (by rfl) ⟨150390, by rfl⟩) R300781
theorem R204569 : Reach 204569 := rs (se 2 (by rfl) ⟨76713, by rfl⟩) R153427
theorem R663389 : Reach 663389 := rs (se 3 (by rfl) ⟨124385, by rfl⟩) R248771
theorem R204659 : Reach 204659 := rs (se 1 (by rfl) ⟨153494, by rfl⟩) R306989
theorem R204695 : Reach 204695 := rs (se 1 (by rfl) ⟨153521, by rfl⟩) R307043
theorem R499729 : Reach 499729 := rs (se 2 (by rfl) ⟨187398, by rfl⟩) R374797
theorem R303155 : Reach 303155 := rs (se 1 (by rfl) ⟨227366, by rfl⟩) R454733
theorem R335947 : Reach 335947 := rs (se 1 (by rfl) ⟨251960, by rfl⟩) R503921
theorem R204875 : Reach 204875 := rs (se 1 (by rfl) ⟨153656, by rfl⟩) R307313
theorem R204929 : Reach 204929 := rs (se 2 (by rfl) ⟨76848, by rfl⟩) R153697
theorem R434393 : Reach 434393 := rs (se 2 (by rfl) ⟨162897, by rfl⟩) R325795
theorem R303425 : Reach 303425 := rs (se 2 (by rfl) ⟨113784, by rfl⟩) R227569
theorem R172363 : Reach 172363 := rs (se 1 (by rfl) ⟨129272, by rfl⟩) R258545
theorem R336221 : Reach 336221 := rs (se 3 (by rfl) ⟨63041, by rfl⟩) R126083
theorem R172439 : Reach 172439 := rs (se 1 (by rfl) ⟨129329, by rfl⟩) R258659
theorem R598603 : Reach 598603 := rs (se 1 (by rfl) ⟨448952, by rfl⟩) R897905
theorem R762443 : Reach 762443 := rs (se 1 (by rfl) ⟨571832, by rfl⟩) R1143665
theorem R303709 : Reach 303709 := rs (se 3 (by rfl) ⟨56945, by rfl⟩) R113891
theorem R303965 : Reach 303965 := rs (se 3 (by rfl) ⟨56993, by rfl⟩) R113987
theorem R336919 : Reach 336919 := rs (se 1 (by rfl) ⟨252689, by rfl⟩) R505379
theorem R238913 : Reach 238913 := rs (se 2 (by rfl) ⟨89592, by rfl⟩) R179185
theorem R763397 : Reach 763397 := rs (se 4 (by rfl) ⟨71568, by rfl⟩) R143137
theorem R239383 : Reach 239383 := rs (se 1 (by rfl) ⟨179537, by rfl⟩) R359075
theorem R337709 : Reach 337709 := rs (se 3 (by rfl) ⟨63320, by rfl⟩) R126641
theorem R305099 : Reach 305099 := rs (se 1 (by rfl) ⟨228824, by rfl⟩) R457649
theorem R305369 : Reach 305369 := rs (se 2 (by rfl) ⟨114513, by rfl⟩) R229027
theorem R272857 : Reach 272857 := rs (se 2 (by rfl) ⟨102321, by rfl⟩) R204643
theorem R306071 : Reach 306071 := rs (se 1 (by rfl) ⟨229553, by rfl⟩) R459107
theorem R339137 : Reach 339137 := rs (se 2 (by rfl) ⟨127176, by rfl⟩) R254353
theorem R109847 : Reach 109847 := rs (se 1 (by rfl) ⟨82385, by rfl⟩) R164771
theorem R404801 : Reach 404801 := rs (se 2 (by rfl) ⟨151800, by rfl⟩) R303601
theorem R503171 : Reach 503171 := rs (se 1 (by rfl) ⟨377378, by rfl⟩) R754757
theorem R306611 : Reach 306611 := rs (se 1 (by rfl) ⟨229958, by rfl⟩) R459917
theorem R372185 : Reach 372185 := rs (se 2 (by rfl) ⟨139569, by rfl⟩) R279139
theorem R372269 : Reach 372269 := rs (se 3 (by rfl) ⟨69800, by rfl⟩) R139601
theorem R306881 : Reach 306881 := rs (se 2 (by rfl) ⟨115080, by rfl⟩) R230161
theorem R110423 : Reach 110423 := rs (se 1 (by rfl) ⟨82817, by rfl⟩) R165635
theorem R307421 : Reach 307421 := rs (se 3 (by rfl) ⟨57641, by rfl⟩) R115283
theorem R111127 : Reach 111127 := rs (se 1 (by rfl) ⟨83345, by rfl⟩) R166691
theorem R569987 : Reach 569987 := rs (se 1 (by rfl) ⟨427490, by rfl⟩) R854981
theorem R340625 : Reach 340625 := rs (se 2 (by rfl) ⟨127734, by rfl⟩) R255469
theorem R341081 : Reach 341081 := rs (se 2 (by rfl) ⟨127905, by rfl⟩) R255811
theorem R341293 : Reach 341293 := rs (se 3 (by rfl) ⟨63992, by rfl⟩) R127985
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R243137 : Reach 243137 := rs (se 2 (by rfl) ⟨91176, by rfl⟩) R182353
theorem R144919 : Reach 144919 := rs (se 1 (by rfl) ⟨108689, by rfl⟩) R217379
theorem R341597 : Reach 341597 := rs (se 3 (by rfl) ⟨64049, by rfl⟩) R128099
theorem R505561 : Reach 505561 := rs (se 2 (by rfl) ⟨189585, by rfl⟩) R379171
theorem R309143 : Reach 309143 := rs (se 1 (by rfl) ⟨231857, by rfl⟩) R463715
theorem R735277 : Reach 735277 := rs (se 3 (by rfl) ⟨137864, by rfl⟩) R275729
theorem R178355 : Reach 178355 := rs (se 1 (by rfl) ⟨133766, by rfl⟩) R267533
theorem R112843 : Reach 112843 := rs (se 1 (by rfl) ⟨84632, by rfl⟩) R169265
theorem R145675 : Reach 145675 := rs (se 1 (by rfl) ⟨109256, by rfl⟩) R218513
theorem R506519 : Reach 506519 := rs (se 1 (by rfl) ⟨379889, by rfl⟩) R759779
theorem R309977 : Reach 309977 := rs (se 2 (by rfl) ⟨116241, by rfl⟩) R232483
theorem R375617 : Reach 375617 := rs (se 2 (by rfl) ⟨140856, by rfl⟩) R281713
theorem R474007 : Reach 474007 := rs (se 1 (by rfl) ⟨355505, by rfl⟩) R711011
theorem R113815 : Reach 113815 := rs (se 1 (by rfl) ⟨85361, by rfl⟩) R170723
theorem R474443 : Reach 474443 := rs (se 1 (by rfl) ⟨355832, by rfl⟩) R711665
theorem R4078997 : Reach 4078997 := rs (se 6 (by rfl) ⟨95601, by rfl⟩) R191203
theorem R540121 : Reach 540121 := rs (se 2 (by rfl) ⟨202545, by rfl⟩) R405091
theorem R376285 : Reach 376285 := rs (se 3 (by rfl) ⟨70553, by rfl⟩) R141107
theorem R245213 : Reach 245213 := rs (se 3 (by rfl) ⟨45977, by rfl⟩) R91955
theorem R114455 : Reach 114455 := rs (se 1 (by rfl) ⟨85841, by rfl⟩) R171683
theorem R180083 : Reach 180083 := rs (se 1 (by rfl) ⟨135062, by rfl⟩) R270125
theorem R212939 : Reach 212939 := rs (se 1 (by rfl) ⟨159704, by rfl⟩) R319409
theorem R114635 : Reach 114635 := rs (se 1 (by rfl) ⟨85976, by rfl⟩) R171953
theorem R147467 : Reach 147467 := rs (se 1 (by rfl) ⟨110600, by rfl⟩) R221201
theorem R376883 : Reach 376883 := rs (se 1 (by rfl) ⟨282662, by rfl⟩) R565325
theorem R344195 : Reach 344195 := rs (se 1 (by rfl) ⟨258146, by rfl⟩) R516293
theorem R147595 : Reach 147595 := rs (se 1 (by rfl) ⟨110696, by rfl⟩) R221393
theorem R344209 : Reach 344209 := rs (se 2 (by rfl) ⟨129078, by rfl⟩) R258157
theorem R409859 : Reach 409859 := rs (se 1 (by rfl) ⟨307394, by rfl⟩) R614789
theorem R147737 : Reach 147737 := rs (se 2 (by rfl) ⟨55401, by rfl⟩) R110803
theorem R147865 : Reach 147865 := rs (se 2 (by rfl) ⟨55449, by rfl⟩) R110899
theorem R344513 : Reach 344513 := rs (se 2 (by rfl) ⟨129192, by rfl⟩) R258385
theorem R377419 : Reach 377419 := rs (se 1 (by rfl) ⟨283064, by rfl⟩) R566129
theorem R1327691 : Reach 1327691 := rs (se 1 (by rfl) ⟨995768, by rfl⟩) R1991537
theorem R770917 : Reach 770917 := rs (se 4 (by rfl) ⟨72273, by rfl⟩) R144547
theorem R148439 : Reach 148439 := rs (se 1 (by rfl) ⟨111329, by rfl⟩) R222659
theorem R213977 : Reach 213977 := rs (se 2 (by rfl) ⟨80241, by rfl⟩) R160483
theorem R509003 : Reach 509003 := rs (se 1 (by rfl) ⟨381752, by rfl⟩) R763505
theorem R148567 : Reach 148567 := rs (se 1 (by rfl) ⟨111425, by rfl⟩) R222851
theorem R345181 : Reach 345181 := rs (se 3 (by rfl) ⟨64721, by rfl⟩) R129443
theorem R181451 : Reach 181451 := rs (se 1 (by rfl) ⟨136088, by rfl⟩) R272177
theorem R541997 : Reach 541997 := rs (se 3 (by rfl) ⟨101624, by rfl⟩) R203249
theorem R640547 : Reach 640547 := rs (se 1 (by rfl) ⟨480410, by rfl⟩) R960821
theorem R771677 : Reach 771677 := rs (se 3 (by rfl) ⟨144689, by rfl⟩) R289379
theorem R181889 : Reach 181889 := rs (se 2 (by rfl) ⟨68208, by rfl⟩) R136417
theorem R149195 : Reach 149195 := rs (se 1 (by rfl) ⟨111896, by rfl⟩) R223793
theorem R181963 : Reach 181963 := rs (se 1 (by rfl) ⟨136472, by rfl⟩) R272945
theorem R771875 : Reach 771875 := rs (se 1 (by rfl) ⟨578906, by rfl⟩) R1157813
theorem R149323 : Reach 149323 := rs (se 1 (by rfl) ⟨111992, by rfl⟩) R223985
theorem R149465 : Reach 149465 := rs (se 2 (by rfl) ⟨56049, by rfl⟩) R112099
theorem R149593 : Reach 149593 := rs (se 2 (by rfl) ⟨56097, by rfl⟩) R112195
theorem R739459 : Reach 739459 := rs (se 1 (by rfl) ⟨554594, by rfl⟩) R1109189
theorem R182425 : Reach 182425 := rs (se 2 (by rfl) ⟨68409, by rfl⟩) R136819
theorem R1460429 : Reach 1460429 := rs (se 3 (by rfl) ⟨273830, by rfl⟩) R547661
theorem R444689 : Reach 444689 := rs (se 2 (by rfl) ⟨166758, by rfl⟩) R333517
theorem R2836781 : Reach 2836781 := rs (se 3 (by rfl) ⟨531896, by rfl⟩) R1063793
theorem R444851 : Reach 444851 := rs (se 1 (by rfl) ⟨333638, by rfl⟩) R667277
theorem R150167 : Reach 150167 := rs (se 1 (by rfl) ⟨112625, by rfl⟩) R225251
theorem R150295 : Reach 150295 := rs (se 1 (by rfl) ⟨112721, by rfl⟩) R225443
theorem R805697 : Reach 805697 := rs (se 2 (by rfl) ⟨302136, by rfl⟩) R604273
theorem R3231089 : Reach 3231089 := rs (se 2 (by rfl) ⟨1211658, by rfl⟩) R2423317
theorem R150923 : Reach 150923 := rs (se 1 (by rfl) ⟨113192, by rfl⟩) R226385
theorem R151051 : Reach 151051 := rs (se 1 (by rfl) ⟨113288, by rfl⟩) R226577
theorem R249409 : Reach 249409 := rs (se 2 (by rfl) ⟨93528, by rfl⟩) R187057
theorem R839261 : Reach 839261 := rs (se 3 (by rfl) ⟨157361, by rfl⟩) R314723
theorem R151193 : Reach 151193 := rs (se 2 (by rfl) ⟨56697, by rfl⟩) R113395
theorem R511667 : Reach 511667 := rs (se 1 (by rfl) ⟨383750, by rfl⟩) R767501
theorem R315083 : Reach 315083 := rs (se 1 (by rfl) ⟨236312, by rfl⟩) R472625
theorem R282329 : Reach 282329 := rs (se 2 (by rfl) ⟨105873, by rfl⟩) R211747
theorem R380675 : Reach 380675 := rs (se 1 (by rfl) ⟨285506, by rfl⟩) R571013
theorem R151321 : Reach 151321 := rs (se 2 (by rfl) ⟨56745, by rfl⟩) R113491
theorem R347993 : Reach 347993 := rs (se 2 (by rfl) ⟨130497, by rfl⟩) R260995
theorem R282457 : Reach 282457 := rs (se 2 (by rfl) ⟨105921, by rfl⟩) R211843
theorem R348083 : Reach 348083 := rs (se 1 (by rfl) ⟨261062, by rfl⟩) R522125
theorem R381017 : Reach 381017 := rs (se 2 (by rfl) ⟨142881, by rfl⟩) R285763
theorem R872579 : Reach 872579 := rs (se 1 (by rfl) ⟨654434, by rfl⟩) R1308869
theorem R1527959 : Reach 1527959 := rs (se 1 (by rfl) ⟨1145969, by rfl⟩) R2291939
theorem R2904245 : Reach 2904245 := rs (se 5 (by rfl) ⟨136136, by rfl⟩) R272273
theorem R119065 : Reach 119065 := rs (se 2 (by rfl) ⟨44649, by rfl⟩) R89299
theorem R643373 : Reach 643373 := rs (se 3 (by rfl) ⟨120632, by rfl⟩) R241265
theorem R446795 : Reach 446795 := rs (se 1 (by rfl) ⟨335096, by rfl⟩) R670193
theorem R151895 : Reach 151895 := rs (se 1 (by rfl) ⟨113921, by rfl⟩) R227843
theorem R152023 : Reach 152023 := rs (se 1 (by rfl) ⟨114017, by rfl⟩) R228035
theorem R1921553 : Reach 1921553 := rs (se 2 (by rfl) ⟨720582, by rfl⟩) R1441165
theorem R873281 : Reach 873281 := rs (se 2 (by rfl) ⟨327480, by rfl⟩) R654961
theorem R1495907 : Reach 1495907 := rs (se 1 (by rfl) ⟨1121930, by rfl⟩) R2243861
theorem R873433 : Reach 873433 := rs (se 2 (by rfl) ⟨327537, by rfl⟩) R655075
theorem R316381 : Reach 316381 := rs (se 3 (by rfl) ⟨59321, by rfl⟩) R118643
theorem R1004561 : Reach 1004561 := rs (se 2 (by rfl) ⟨376710, by rfl⟩) R753421
theorem R152651 : Reach 152651 := rs (se 1 (by rfl) ⟨114488, by rfl⟩) R228977
theorem R513125 : Reach 513125 := rs (se 4 (by rfl) ⟨48105, by rfl⟩) R96211
theorem R87147 : Reach 87147 := rs (se 1 (by rfl) ⟨65360, by rfl⟩) R130721
theorem R87159 : Reach 87159 := rs (se 1 (by rfl) ⟨65369, by rfl⟩) R130739
theorem R87179 : Reach 87179 := rs (se 1 (by rfl) ⟨65384, by rfl⟩) R130769
theorem R87191 : Reach 87191 := rs (se 1 (by rfl) ⟨65393, by rfl⟩) R130787
theorem R87211 : Reach 87211 := rs (se 1 (by rfl) ⟨65408, by rfl⟩) R130817
theorem R87223 : Reach 87223 := rs (se 1 (by rfl) ⟨65417, by rfl⟩) R130835
theorem R87243 : Reach 87243 := rs (se 1 (by rfl) ⟨65432, by rfl⟩) R130865
theorem R152779 : Reach 152779 := rs (se 1 (by rfl) ⟨114584, by rfl⟩) R229169
theorem R87255 : Reach 87255 := rs (se 1 (by rfl) ⟨65441, by rfl⟩) R130883
theorem R87275 : Reach 87275 := rs (se 1 (by rfl) ⟨65456, by rfl⟩) R130913
theorem R87287 : Reach 87287 := rs (se 1 (by rfl) ⟨65465, by rfl⟩) R130931
theorem R87307 : Reach 87307 := rs (se 1 (by rfl) ⟨65480, by rfl⟩) R130961
theorem R87319 : Reach 87319 := rs (se 1 (by rfl) ⟨65489, by rfl⟩) R130979
theorem R87339 : Reach 87339 := rs (se 1 (by rfl) ⟨65504, by rfl⟩) R131009
theorem R87351 : Reach 87351 := rs (se 1 (by rfl) ⟨65513, by rfl⟩) R131027
theorem R87371 : Reach 87371 := rs (se 1 (by rfl) ⟨65528, by rfl⟩) R131057
theorem R87383 : Reach 87383 := rs (se 1 (by rfl) ⟨65537, by rfl⟩) R131075
theorem R152921 : Reach 152921 := rs (se 2 (by rfl) ⟨57345, by rfl⟩) R114691
theorem R87403 : Reach 87403 := rs (se 1 (by rfl) ⟨65552, by rfl⟩) R131105
theorem R87415 : Reach 87415 := rs (se 1 (by rfl) ⟨65561, by rfl⟩) R131123
theorem R87435 : Reach 87435 := rs (se 1 (by rfl) ⟨65576, by rfl⟩) R131153
theorem R87447 : Reach 87447 := rs (se 1 (by rfl) ⟨65585, by rfl⟩) R131171
theorem R87467 : Reach 87467 := rs (se 1 (by rfl) ⟨65600, by rfl⟩) R131201
theorem R87479 : Reach 87479 := rs (se 1 (by rfl) ⟨65609, by rfl⟩) R131219
theorem R87499 : Reach 87499 := rs (se 1 (by rfl) ⟨65624, by rfl⟩) R131249
theorem R87511 : Reach 87511 := rs (se 1 (by rfl) ⟨65633, by rfl⟩) R131267
theorem R153049 : Reach 153049 := rs (se 2 (by rfl) ⟨57393, by rfl⟩) R114787
theorem R87531 : Reach 87531 := rs (se 1 (by rfl) ⟨65648, by rfl⟩) R131297
theorem R87543 : Reach 87543 := rs (se 1 (by rfl) ⟨65657, by rfl⟩) R131315
theorem R87563 : Reach 87563 := rs (se 1 (by rfl) ⟨65672, by rfl⟩) R131345
theorem R87575 : Reach 87575 := rs (se 1 (by rfl) ⟨65681, by rfl⟩) R131363
theorem R87595 : Reach 87595 := rs (se 1 (by rfl) ⟨65696, by rfl⟩) R131393
theorem R87607 : Reach 87607 := rs (se 1 (by rfl) ⟨65705, by rfl⟩) R131411
theorem R87627 : Reach 87627 := rs (se 1 (by rfl) ⟨65720, by rfl⟩) R131441
theorem R87639 : Reach 87639 := rs (se 1 (by rfl) ⟨65729, by rfl⟩) R131459
theorem R87659 : Reach 87659 := rs (se 1 (by rfl) ⟨65744, by rfl⟩) R131489
theorem R87671 : Reach 87671 := rs (se 1 (by rfl) ⟨65753, by rfl⟩) R131507
theorem R87691 : Reach 87691 := rs (se 1 (by rfl) ⟨65768, by rfl⟩) R131537
theorem R87703 : Reach 87703 := rs (se 1 (by rfl) ⟨65777, by rfl⟩) R131555
theorem R87723 : Reach 87723 := rs (se 1 (by rfl) ⟨65792, by rfl⟩) R131585
theorem R87735 : Reach 87735 := rs (se 1 (by rfl) ⟨65801, by rfl⟩) R131603
theorem R382657 : Reach 382657 := rs (se 2 (by rfl) ⟨143496, by rfl⟩) R286993
theorem R87755 : Reach 87755 := rs (se 1 (by rfl) ⟨65816, by rfl⟩) R131633
theorem R87767 : Reach 87767 := rs (se 1 (by rfl) ⟨65825, by rfl⟩) R131651
theorem R87787 : Reach 87787 := rs (se 1 (by rfl) ⟨65840, by rfl⟩) R131681
theorem R87799 : Reach 87799 := rs (se 1 (by rfl) ⟨65849, by rfl⟩) R131699
theorem R87819 : Reach 87819 := rs (se 1 (by rfl) ⟨65864, by rfl⟩) R131729
theorem R513809 : Reach 513809 := rs (se 2 (by rfl) ⟨192678, by rfl⟩) R385357
theorem R87831 : Reach 87831 := rs (se 1 (by rfl) ⟨65873, by rfl⟩) R131747
theorem R87851 : Reach 87851 := rs (se 1 (by rfl) ⟨65888, by rfl⟩) R131777
theorem R87863 : Reach 87863 := rs (se 1 (by rfl) ⟨65897, by rfl⟩) R131795
theorem R87883 : Reach 87883 := rs (se 1 (by rfl) ⟨65912, by rfl⟩) R131825
theorem R87895 : Reach 87895 := rs (se 1 (by rfl) ⟨65921, by rfl⟩) R131843
theorem R87915 : Reach 87915 := rs (se 1 (by rfl) ⟨65936, by rfl⟩) R131873
theorem R87927 : Reach 87927 := rs (se 1 (by rfl) ⟨65945, by rfl⟩) R131891
theorem R87947 : Reach 87947 := rs (se 1 (by rfl) ⟨65960, by rfl⟩) R131921
theorem R87959 : Reach 87959 := rs (se 1 (by rfl) ⟨65969, by rfl⟩) R131939
theorem R87979 : Reach 87979 := rs (se 1 (by rfl) ⟨65984, by rfl⟩) R131969
theorem R87991 : Reach 87991 := rs (se 1 (by rfl) ⟨65993, by rfl⟩) R131987
theorem R186305 : Reach 186305 := rs (se 2 (by rfl) ⟨69864, by rfl⟩) R139729
theorem R88011 : Reach 88011 := rs (se 1 (by rfl) ⟨66008, by rfl⟩) R132017
theorem R88023 : Reach 88023 := rs (se 1 (by rfl) ⟨66017, by rfl⟩) R132035
theorem R88043 : Reach 88043 := rs (se 1 (by rfl) ⟨66032, by rfl⟩) R132065
theorem R88055 : Reach 88055 := rs (se 1 (by rfl) ⟨66041, by rfl⟩) R132083
theorem R88075 : Reach 88075 := rs (se 1 (by rfl) ⟨66056, by rfl⟩) R132113
theorem R186391 : Reach 186391 := rs (se 1 (by rfl) ⟨139793, by rfl⟩) R279587
theorem R88087 : Reach 88087 := rs (se 1 (by rfl) ⟨66065, by rfl⟩) R132131
theorem R153623 : Reach 153623 := rs (se 1 (by rfl) ⟨115217, by rfl⟩) R230435
theorem R88107 : Reach 88107 := rs (se 1 (by rfl) ⟨66080, by rfl⟩) R132161
theorem R88119 : Reach 88119 := rs (se 1 (by rfl) ⟨66089, by rfl⟩) R132179
theorem R448577 : Reach 448577 := rs (se 2 (by rfl) ⟨168216, by rfl⟩) R336433
theorem R88139 : Reach 88139 := rs (se 1 (by rfl) ⟨66104, by rfl⟩) R132209
theorem R88151 : Reach 88151 := rs (se 1 (by rfl) ⟨66113, by rfl⟩) R132227
theorem R88171 : Reach 88171 := rs (se 1 (by rfl) ⟨66128, by rfl⟩) R132257
theorem R88183 : Reach 88183 := rs (se 1 (by rfl) ⟨66137, by rfl⟩) R132275
theorem R88203 : Reach 88203 := rs (se 1 (by rfl) ⟨66152, by rfl⟩) R132305
theorem R88215 : Reach 88215 := rs (se 1 (by rfl) ⟨66161, by rfl⟩) R132323
theorem R153751 : Reach 153751 := rs (se 1 (by rfl) ⟨115313, by rfl⟩) R230627
theorem R88235 : Reach 88235 := rs (se 1 (by rfl) ⟨66176, by rfl⟩) R132353
theorem R88247 : Reach 88247 := rs (se 1 (by rfl) ⟨66185, by rfl⟩) R132371
theorem R88267 : Reach 88267 := rs (se 1 (by rfl) ⟨66200, by rfl⟩) R132401
theorem R88279 : Reach 88279 := rs (se 1 (by rfl) ⟨66209, by rfl⟩) R132419
theorem R88299 : Reach 88299 := rs (se 1 (by rfl) ⟨66224, by rfl⟩) R132449
theorem R88311 : Reach 88311 := rs (se 1 (by rfl) ⟨66233, by rfl⟩) R132467
theorem R88331 : Reach 88331 := rs (se 1 (by rfl) ⟨66248, by rfl⟩) R132497
theorem R88343 : Reach 88343 := rs (se 1 (by rfl) ⟨66257, by rfl⟩) R132515
theorem R88363 : Reach 88363 := rs (se 1 (by rfl) ⟨66272, by rfl⟩) R132545
theorem R88375 : Reach 88375 := rs (se 1 (by rfl) ⟨66281, by rfl⟩) R132563
theorem R88395 : Reach 88395 := rs (se 1 (by rfl) ⟨66296, by rfl⟩) R132593
theorem R88407 : Reach 88407 := rs (se 1 (by rfl) ⟨66305, by rfl⟩) R132611
theorem R88427 : Reach 88427 := rs (se 1 (by rfl) ⟨66320, by rfl⟩) R132641
theorem R88439 : Reach 88439 := rs (se 1 (by rfl) ⟨66329, by rfl⟩) R132659
theorem R88459 : Reach 88459 := rs (se 1 (by rfl) ⟨66344, by rfl⟩) R132689
theorem R88471 : Reach 88471 := rs (se 1 (by rfl) ⟨66353, by rfl⟩) R132707
theorem R88491 : Reach 88491 := rs (se 1 (by rfl) ⟨66368, by rfl⟩) R132737
theorem R776627 : Reach 776627 := rs (se 1 (by rfl) ⟨582470, by rfl⟩) R1164941
theorem R88503 : Reach 88503 := rs (se 1 (by rfl) ⟨66377, by rfl⟩) R132755
theorem R88523 : Reach 88523 := rs (se 1 (by rfl) ⟨66392, by rfl⟩) R132785
theorem R88535 : Reach 88535 := rs (se 1 (by rfl) ⟨66401, by rfl⟩) R132803
theorem R88555 : Reach 88555 := rs (se 1 (by rfl) ⟨66416, by rfl⟩) R132833
theorem R88567 : Reach 88567 := rs (se 1 (by rfl) ⟨66425, by rfl⟩) R132851
theorem R88587 : Reach 88587 := rs (se 1 (by rfl) ⟨66440, by rfl⟩) R132881
theorem R88599 : Reach 88599 := rs (se 1 (by rfl) ⟨66449, by rfl⟩) R132899
theorem R88619 : Reach 88619 := rs (se 1 (by rfl) ⟨66464, by rfl⟩) R132929
theorem R88631 : Reach 88631 := rs (se 1 (by rfl) ⟨66473, by rfl⟩) R132947
theorem R88651 : Reach 88651 := rs (se 1 (by rfl) ⟨66488, by rfl⟩) R132977
theorem R88663 : Reach 88663 := rs (se 1 (by rfl) ⟨66497, by rfl⟩) R132995
theorem R88683 : Reach 88683 := rs (se 1 (by rfl) ⟨66512, by rfl⟩) R133025
theorem R88695 : Reach 88695 := rs (se 1 (by rfl) ⟨66521, by rfl⟩) R133043
theorem R88715 : Reach 88715 := rs (se 1 (by rfl) ⟨66536, by rfl⟩) R133073
theorem R88727 : Reach 88727 := rs (se 1 (by rfl) ⟨66545, by rfl⟩) R133091
theorem R88747 : Reach 88747 := rs (se 1 (by rfl) ⟨66560, by rfl⟩) R133121
theorem R88759 : Reach 88759 := rs (se 1 (by rfl) ⟨66569, by rfl⟩) R133139
theorem R88779 : Reach 88779 := rs (se 1 (by rfl) ⟨66584, by rfl⟩) R133169
theorem R88791 : Reach 88791 := rs (se 1 (by rfl) ⟨66593, by rfl⟩) R133187
theorem R88811 : Reach 88811 := rs (se 1 (by rfl) ⟨66608, by rfl⟩) R133217
theorem R88823 : Reach 88823 := rs (se 1 (by rfl) ⟨66617, by rfl⟩) R133235
theorem R88843 : Reach 88843 := rs (se 1 (by rfl) ⟨66632, by rfl⟩) R133265
theorem R88855 : Reach 88855 := rs (se 1 (by rfl) ⟨66641, by rfl⟩) R133283
theorem R88875 : Reach 88875 := rs (se 1 (by rfl) ⟨66656, by rfl⟩) R133313
theorem R88887 : Reach 88887 := rs (se 1 (by rfl) ⟨66665, by rfl⟩) R133331
theorem R187211 : Reach 187211 := rs (se 1 (by rfl) ⟨140408, by rfl⟩) R280817
theorem R88907 : Reach 88907 := rs (se 1 (by rfl) ⟨66680, by rfl⟩) R133361
theorem R88919 : Reach 88919 := rs (se 1 (by rfl) ⟨66689, by rfl⟩) R133379
theorem R580445 : Reach 580445 := rs (se 3 (by rfl) ⟨108833, by rfl⟩) R217667
theorem R88939 : Reach 88939 := rs (se 1 (by rfl) ⟨66704, by rfl⟩) R133409
theorem R88951 : Reach 88951 := rs (se 1 (by rfl) ⟨66713, by rfl⟩) R133427
theorem R88971 : Reach 88971 := rs (se 1 (by rfl) ⟨66728, by rfl⟩) R133457
theorem R88983 : Reach 88983 := rs (se 1 (by rfl) ⟨66737, by rfl⟩) R133475
theorem R89003 : Reach 89003 := rs (se 1 (by rfl) ⟨66752, by rfl⟩) R133505
theorem R89015 : Reach 89015 := rs (se 1 (by rfl) ⟨66761, by rfl⟩) R133523
theorem R89035 : Reach 89035 := rs (se 1 (by rfl) ⟨66776, by rfl⟩) R133553
theorem R89047 : Reach 89047 := rs (se 1 (by rfl) ⟨66785, by rfl⟩) R133571
theorem R89067 : Reach 89067 := rs (se 1 (by rfl) ⟨66800, by rfl⟩) R133601
theorem R89079 : Reach 89079 := rs (se 1 (by rfl) ⟨66809, by rfl⟩) R133619
theorem R89099 : Reach 89099 := rs (se 1 (by rfl) ⟨66824, by rfl⟩) R133649
theorem R89111 : Reach 89111 := rs (se 1 (by rfl) ⟨66833, by rfl⟩) R133667
theorem R89131 : Reach 89131 := rs (se 1 (by rfl) ⟨66848, by rfl⟩) R133697
theorem R89143 : Reach 89143 := rs (se 1 (by rfl) ⟨66857, by rfl⟩) R133715
theorem R89163 : Reach 89163 := rs (se 1 (by rfl) ⟨66872, by rfl⟩) R133745
theorem R89175 : Reach 89175 := rs (se 1 (by rfl) ⟨66881, by rfl⟩) R133763
theorem R220249 : Reach 220249 := rs (se 2 (by rfl) ⟨82593, by rfl⟩) R165187
theorem R89195 : Reach 89195 := rs (se 1 (by rfl) ⟨66896, by rfl⟩) R133793
theorem R89207 : Reach 89207 := rs (se 1 (by rfl) ⟨66905, by rfl⟩) R133811
theorem R89227 : Reach 89227 := rs (se 1 (by rfl) ⟨66920, by rfl⟩) R133841
theorem R89239 : Reach 89239 := rs (se 1 (by rfl) ⟨66929, by rfl⟩) R133859
theorem R89259 : Reach 89259 := rs (se 1 (by rfl) ⟨66944, by rfl⟩) R133889
theorem R89271 : Reach 89271 := rs (se 1 (by rfl) ⟨66953, by rfl⟩) R133907
theorem R89291 : Reach 89291 := rs (se 1 (by rfl) ⟨66968, by rfl⟩) R133937
theorem R89303 : Reach 89303 := rs (se 1 (by rfl) ⟨66977, by rfl⟩) R133955
theorem R253145 : Reach 253145 := rs (se 2 (by rfl) ⟨94929, by rfl⟩) R189859
theorem R89323 : Reach 89323 := rs (se 1 (by rfl) ⟨66992, by rfl⟩) R133985
theorem R89335 : Reach 89335 := rs (se 1 (by rfl) ⟨67001, by rfl⟩) R134003
theorem R89355 : Reach 89355 := rs (se 1 (by rfl) ⟨67016, by rfl⟩) R134033
theorem R89367 : Reach 89367 := rs (se 1 (by rfl) ⟨67025, by rfl⟩) R134051
theorem R89387 : Reach 89387 := rs (se 1 (by rfl) ⟨67040, by rfl⟩) R134081
theorem R1039661 : Reach 1039661 := rs (se 3 (by rfl) ⟨194936, by rfl⟩) R389873
theorem R89399 : Reach 89399 := rs (se 1 (by rfl) ⟨67049, by rfl⟩) R134099
theorem R89419 : Reach 89419 := rs (se 1 (by rfl) ⟨67064, by rfl⟩) R134129
theorem R89431 : Reach 89431 := rs (se 1 (by rfl) ⟨67073, by rfl⟩) R134147
theorem R89451 : Reach 89451 := rs (se 1 (by rfl) ⟨67088, by rfl⟩) R134177
theorem R89463 : Reach 89463 := rs (se 1 (by rfl) ⟨67097, by rfl⟩) R134195
theorem R89483 : Reach 89483 := rs (se 1 (by rfl) ⟨67112, by rfl⟩) R134225
theorem R89495 : Reach 89495 := rs (se 1 (by rfl) ⟨67121, by rfl⟩) R134243
theorem R89515 : Reach 89515 := rs (se 1 (by rfl) ⟨67136, by rfl⟩) R134273
theorem R89527 : Reach 89527 := rs (se 1 (by rfl) ⟨67145, by rfl⟩) R134291
theorem R89547 : Reach 89547 := rs (se 1 (by rfl) ⟨67160, by rfl⟩) R134321
theorem R89559 : Reach 89559 := rs (se 1 (by rfl) ⟨67169, by rfl⟩) R134339
theorem R89579 : Reach 89579 := rs (se 1 (by rfl) ⟨67184, by rfl⟩) R134369
theorem R89591 : Reach 89591 := rs (se 1 (by rfl) ⟨67193, by rfl⟩) R134387
theorem R89611 : Reach 89611 := rs (se 1 (by rfl) ⟨67208, by rfl⟩) R134417
theorem R89623 : Reach 89623 := rs (se 1 (by rfl) ⟨67217, by rfl⟩) R134435
theorem R89643 : Reach 89643 := rs (se 1 (by rfl) ⟨67232, by rfl⟩) R134465
theorem R89655 : Reach 89655 := rs (se 1 (by rfl) ⟨67241, by rfl⟩) R134483
theorem R89675 : Reach 89675 := rs (se 1 (by rfl) ⟨67256, by rfl⟩) R134513
theorem R89687 : Reach 89687 := rs (se 1 (by rfl) ⟨67265, by rfl⟩) R134531
theorem R482917 : Reach 482917 := rs (se 4 (by rfl) ⟨45273, by rfl⟩) R90547
theorem R89707 : Reach 89707 := rs (se 1 (by rfl) ⟨67280, by rfl⟩) R134561
theorem R89719 : Reach 89719 := rs (se 1 (by rfl) ⟨67289, by rfl⟩) R134579
theorem R89739 : Reach 89739 := rs (se 1 (by rfl) ⟨67304, by rfl⟩) R134609
theorem R89751 : Reach 89751 := rs (se 1 (by rfl) ⟨67313, by rfl⟩) R134627
theorem R89771 : Reach 89771 := rs (se 1 (by rfl) ⟨67328, by rfl⟩) R134657
theorem R89783 : Reach 89783 := rs (se 1 (by rfl) ⟨67337, by rfl⟩) R134675
theorem R89803 : Reach 89803 := rs (se 1 (by rfl) ⟨67352, by rfl⟩) R134705
theorem R89815 : Reach 89815 := rs (se 1 (by rfl) ⟨67361, by rfl⟩) R134723
theorem R286429 : Reach 286429 := rs (se 3 (by rfl) ⟨53705, by rfl⟩) R107411
theorem R89835 : Reach 89835 := rs (se 1 (by rfl) ⟨67376, by rfl⟩) R134753
theorem R89847 : Reach 89847 := rs (se 1 (by rfl) ⟨67385, by rfl⟩) R134771
theorem R89867 : Reach 89867 := rs (se 1 (by rfl) ⟨67400, by rfl⟩) R134801
theorem R89879 : Reach 89879 := rs (se 1 (by rfl) ⟨67409, by rfl⟩) R134819
theorem R188185 : Reach 188185 := rs (se 2 (by rfl) ⟨70569, by rfl⟩) R141139
theorem R89899 : Reach 89899 := rs (se 1 (by rfl) ⟨67424, by rfl⟩) R134849
theorem R89911 : Reach 89911 := rs (se 1 (by rfl) ⟨67433, by rfl⟩) R134867
theorem R319297 : Reach 319297 := rs (se 2 (by rfl) ⟨119736, by rfl⟩) R239473
theorem R89931 : Reach 89931 := rs (se 1 (by rfl) ⟨67448, by rfl⟩) R134897
theorem R89943 : Reach 89943 := rs (se 1 (by rfl) ⟨67457, by rfl⟩) R134915
theorem R89963 : Reach 89963 := rs (se 1 (by rfl) ⟨67472, by rfl⟩) R134945
theorem R1007477 : Reach 1007477 := rs (se 5 (by rfl) ⟨47225, by rfl⟩) R94451
theorem R89975 : Reach 89975 := rs (se 1 (by rfl) ⟨67481, by rfl⟩) R134963
theorem R89995 : Reach 89995 := rs (se 1 (by rfl) ⟨67496, by rfl⟩) R134993
theorem R90007 : Reach 90007 := rs (se 1 (by rfl) ⟨67505, by rfl⟩) R135011
theorem R90027 : Reach 90027 := rs (se 1 (by rfl) ⟨67520, by rfl⟩) R135041
theorem R90039 : Reach 90039 := rs (se 1 (by rfl) ⟨67529, by rfl⟩) R135059
theorem R90059 : Reach 90059 := rs (se 1 (by rfl) ⟨67544, by rfl⟩) R135089
theorem R90071 : Reach 90071 := rs (se 1 (by rfl) ⟨67553, by rfl⟩) R135107
theorem R450521 : Reach 450521 := rs (se 2 (by rfl) ⟨168945, by rfl⟩) R337891
theorem R90091 : Reach 90091 := rs (se 1 (by rfl) ⟨67568, by rfl⟩) R135137
theorem R90103 : Reach 90103 := rs (se 1 (by rfl) ⟨67577, by rfl⟩) R135155
theorem R90123 : Reach 90123 := rs (se 1 (by rfl) ⟨67592, by rfl⟩) R135185
theorem R90135 : Reach 90135 := rs (se 1 (by rfl) ⟨67601, by rfl⟩) R135203
theorem R90155 : Reach 90155 := rs (se 1 (by rfl) ⟨67616, by rfl⟩) R135233
theorem R90167 : Reach 90167 := rs (se 1 (by rfl) ⟨67625, by rfl⟩) R135251
theorem R90187 : Reach 90187 := rs (se 1 (by rfl) ⟨67640, by rfl⟩) R135281
theorem R90199 : Reach 90199 := rs (se 1 (by rfl) ⟨67649, by rfl⟩) R135299
theorem R122969 : Reach 122969 := rs (se 2 (by rfl) ⟨46113, by rfl⟩) R92227
theorem R90219 : Reach 90219 := rs (se 1 (by rfl) ⟨67664, by rfl⟩) R135329
theorem R90231 : Reach 90231 := rs (se 1 (by rfl) ⟨67673, by rfl⟩) R135347
theorem R90251 : Reach 90251 := rs (se 1 (by rfl) ⟨67688, by rfl⟩) R135377
theorem R319639 : Reach 319639 := rs (se 1 (by rfl) ⟨239729, by rfl⟩) R479459
theorem R90263 : Reach 90263 := rs (se 1 (by rfl) ⟨67697, by rfl⟩) R135395
theorem R90283 : Reach 90283 := rs (se 1 (by rfl) ⟨67712, by rfl⟩) R135425
theorem R221363 : Reach 221363 := rs (se 1 (by rfl) ⟨166022, by rfl⟩) R332045
theorem R90295 : Reach 90295 := rs (se 1 (by rfl) ⟨67721, by rfl⟩) R135443
theorem R90315 : Reach 90315 := rs (se 1 (by rfl) ⟨67736, by rfl⟩) R135473
theorem R90327 : Reach 90327 := rs (se 1 (by rfl) ⟨67745, by rfl⟩) R135491
theorem R90347 : Reach 90347 := rs (se 1 (by rfl) ⟨67760, by rfl⟩) R135521
theorem R90359 : Reach 90359 := rs (se 1 (by rfl) ⟨67769, by rfl⟩) R135539
theorem R90379 : Reach 90379 := rs (se 1 (by rfl) ⟨67784, by rfl⟩) R135569
theorem R90391 : Reach 90391 := rs (se 1 (by rfl) ⟨67793, by rfl⟩) R135587
theorem R90411 : Reach 90411 := rs (se 1 (by rfl) ⟨67808, by rfl⟩) R135617
theorem R90423 : Reach 90423 := rs (se 1 (by rfl) ⟨67817, by rfl⟩) R135635
theorem R90443 : Reach 90443 := rs (se 1 (by rfl) ⟨67832, by rfl⟩) R135665
theorem R90455 : Reach 90455 := rs (se 1 (by rfl) ⟨67841, by rfl⟩) R135683
theorem R90475 : Reach 90475 := rs (se 1 (by rfl) ⟨67856, by rfl⟩) R135713
theorem R90487 : Reach 90487 := rs (se 1 (by rfl) ⟨67865, by rfl⟩) R135731
theorem R90507 : Reach 90507 := rs (se 1 (by rfl) ⟨67880, by rfl⟩) R135761
theorem R90519 : Reach 90519 := rs (se 1 (by rfl) ⟨67889, by rfl⟩) R135779
theorem R90539 : Reach 90539 := rs (se 1 (by rfl) ⟨67904, by rfl⟩) R135809
theorem R90551 : Reach 90551 := rs (se 1 (by rfl) ⟨67913, by rfl⟩) R135827
theorem R254411 : Reach 254411 := rs (se 1 (by rfl) ⟨190808, by rfl⟩) R381617
theorem R90571 : Reach 90571 := rs (se 1 (by rfl) ⟨67928, by rfl⟩) R135857
theorem R90583 : Reach 90583 := rs (se 1 (by rfl) ⟨67937, by rfl⟩) R135875
theorem R90603 : Reach 90603 := rs (se 1 (by rfl) ⟨67952, by rfl⟩) R135905
theorem R90615 : Reach 90615 := rs (se 1 (by rfl) ⟨67961, by rfl⟩) R135923
theorem R90635 : Reach 90635 := rs (se 1 (by rfl) ⟨67976, by rfl⟩) R135953
theorem R90647 : Reach 90647 := rs (se 1 (by rfl) ⟨67985, by rfl⟩) R135971
theorem R90667 : Reach 90667 := rs (se 1 (by rfl) ⟨68000, by rfl⟩) R136001
theorem R90679 : Reach 90679 := rs (se 1 (by rfl) ⟨68009, by rfl⟩) R136019
theorem R287297 : Reach 287297 := rs (se 2 (by rfl) ⟨107736, by rfl⟩) R215473
theorem R90699 : Reach 90699 := rs (se 1 (by rfl) ⟨68024, by rfl⟩) R136049
theorem R90711 : Reach 90711 := rs (se 1 (by rfl) ⟨68033, by rfl⟩) R136067
theorem R90731 : Reach 90731 := rs (se 1 (by rfl) ⟨68048, by rfl⟩) R136097
theorem R90743 : Reach 90743 := rs (se 1 (by rfl) ⟨68057, by rfl⟩) R136115
theorem R90763 : Reach 90763 := rs (se 1 (by rfl) ⟨68072, by rfl⟩) R136145
theorem R90775 : Reach 90775 := rs (se 1 (by rfl) ⟨68081, by rfl⟩) R136163
theorem R90795 : Reach 90795 := rs (se 1 (by rfl) ⟨68096, by rfl⟩) R136193
theorem R90807 : Reach 90807 := rs (se 1 (by rfl) ⟨68105, by rfl⟩) R136211
theorem R221899 : Reach 221899 := rs (se 1 (by rfl) ⟨166424, by rfl⟩) R332849
theorem R90827 : Reach 90827 := rs (se 1 (by rfl) ⟨68120, by rfl⟩) R136241
theorem R90839 : Reach 90839 := rs (se 1 (by rfl) ⟨68129, by rfl⟩) R136259
theorem R90859 : Reach 90859 := rs (se 1 (by rfl) ⟨68144, by rfl⟩) R136289
theorem R90871 : Reach 90871 := rs (se 1 (by rfl) ⟨68153, by rfl⟩) R136307
theorem R90891 : Reach 90891 := rs (se 1 (by rfl) ⟨68168, by rfl⟩) R136337
theorem R156439 : Reach 156439 := rs (se 1 (by rfl) ⟨117329, by rfl⟩) R234659
theorem R90903 : Reach 90903 := rs (se 1 (by rfl) ⟨68177, by rfl⟩) R136355
theorem R90923 : Reach 90923 := rs (se 1 (by rfl) ⟨68192, by rfl⟩) R136385
theorem R90935 : Reach 90935 := rs (se 1 (by rfl) ⟨68201, by rfl⟩) R136403
theorem R90955 : Reach 90955 := rs (se 1 (by rfl) ⟨68216, by rfl⟩) R136433
theorem R90967 : Reach 90967 := rs (se 1 (by rfl) ⟨68225, by rfl⟩) R136451
theorem R222041 : Reach 222041 := rs (se 2 (by rfl) ⟨83265, by rfl⟩) R166531
theorem R90987 : Reach 90987 := rs (se 1 (by rfl) ⟨68240, by rfl⟩) R136481
theorem R90999 : Reach 90999 := rs (se 1 (by rfl) ⟨68249, by rfl⟩) R136499
theorem R91019 : Reach 91019 := rs (se 1 (by rfl) ⟨68264, by rfl⟩) R136529
theorem R91031 : Reach 91031 := rs (se 1 (by rfl) ⟨68273, by rfl⟩) R136547
theorem R91051 : Reach 91051 := rs (se 1 (by rfl) ⟨68288, by rfl⟩) R136577
theorem R517043 : Reach 517043 := rs (se 1 (by rfl) ⟨387782, by rfl⟩) R775565
theorem R91063 : Reach 91063 := rs (se 1 (by rfl) ⟨68297, by rfl⟩) R136595
theorem R91083 : Reach 91083 := rs (se 1 (by rfl) ⟨68312, by rfl⟩) R136625
theorem R91095 : Reach 91095 := rs (se 1 (by rfl) ⟨68321, by rfl⟩) R136643
theorem R91115 : Reach 91115 := rs (se 1 (by rfl) ⟨68336, by rfl⟩) R136673
theorem R91127 : Reach 91127 := rs (se 1 (by rfl) ⟨68345, by rfl⟩) R136691
theorem R419033 : Reach 419033 := rs (se 2 (by rfl) ⟨157137, by rfl⟩) R314275
theorem R124249 : Reach 124249 := rs (se 2 (by rfl) ⟨46593, by rfl⟩) R93187
theorem R124363 : Reach 124363 := rs (se 1 (by rfl) ⟨93272, by rfl⟩) R186545
theorem R452141 : Reach 452141 := rs (se 3 (by rfl) ⟨84776, by rfl⟩) R169553
theorem R222871 : Reach 222871 := rs (se 1 (by rfl) ⟨167153, by rfl⟩) R334307
theorem R386839 : Reach 386839 := rs (se 1 (by rfl) ⟨290129, by rfl⟩) R580259
theorem R92215 : Reach 92215 := rs (se 1 (by rfl) ⟨69161, by rfl⟩) R138323
theorem R223307 : Reach 223307 := rs (se 1 (by rfl) ⟨167480, by rfl⟩) R334961
theorem R190603 : Reach 190603 := rs (se 1 (by rfl) ⟨142952, by rfl⟩) R285905
theorem R1239245 : Reach 1239245 := rs (se 3 (by rfl) ⟨232358, by rfl⟩) R464717
theorem R190679 : Reach 190679 := rs (se 1 (by rfl) ⟨143009, by rfl⟩) R286019
theorem R518501 : Reach 518501 := rs (se 4 (by rfl) ⟨48609, by rfl⟩) R97219
theorem R223681 : Reach 223681 := rs (se 2 (by rfl) ⟨83880, by rfl⟩) R167761
theorem R649745 : Reach 649745 := rs (se 2 (by rfl) ⟨243654, by rfl⟩) R487309
theorem R125707 : Reach 125707 := rs (se 1 (by rfl) ⟨94280, by rfl⟩) R188561
theorem R518957 : Reach 518957 := rs (se 3 (by rfl) ⟨97304, by rfl⟩) R194609
theorem R322483 : Reach 322483 := rs (se 1 (by rfl) ⟨241862, by rfl⟩) R483725
theorem R125975 : Reach 125975 := rs (se 1 (by rfl) ⟨94481, by rfl⟩) R188963
theorem R224279 : Reach 224279 := rs (se 1 (by rfl) ⟨168209, by rfl⟩) R336419
theorem R945413 : Reach 945413 := rs (se 4 (by rfl) ⟨88632, by rfl⟩) R177265
theorem R159127 : Reach 159127 := rs (se 1 (by rfl) ⟨119345, by rfl⟩) R238691
theorem R388739 : Reach 388739 := rs (se 1 (by rfl) ⟨291554, by rfl⟩) R583109
theorem R94007 : Reach 94007 := rs (se 1 (by rfl) ⟨70505, by rfl⟩) R141011
theorem R225089 : Reach 225089 := rs (se 2 (by rfl) ⟨84408, by rfl⟩) R168817
theorem R192449 : Reach 192449 := rs (se 2 (by rfl) ⟨72168, by rfl⟩) R144337
theorem R126937 : Reach 126937 := rs (se 2 (by rfl) ⟨47601, by rfl⟩) R95203
theorem R225625 : Reach 225625 := rs (se 2 (by rfl) ⟨84609, by rfl⟩) R169219
theorem R1274291 : Reach 1274291 := rs (se 1 (by rfl) ⟨955718, by rfl⟩) R1911437
theorem R94699 : Reach 94699 := rs (se 1 (by rfl) ⟨71024, by rfl⟩) R142049
theorem R160535 : Reach 160535 := rs (se 1 (by rfl) ⟨120401, by rfl⟩) R240803
theorem R291863 : Reach 291863 := rs (se 1 (by rfl) ⟨218897, by rfl⟩) R437795
theorem R95575 : Reach 95575 := rs (se 1 (by rfl) ⟨71681, by rfl⟩) R143363
theorem R456029 : Reach 456029 := rs (se 3 (by rfl) ⟨85505, by rfl⟩) R171011
theorem R128395 : Reach 128395 := rs (se 1 (by rfl) ⟨96296, by rfl⟩) R192593
theorem R128407 : Reach 128407 := rs (se 1 (by rfl) ⟨96305, by rfl⟩) R192611
theorem R226739 : Reach 226739 := rs (se 1 (by rfl) ⟨170054, by rfl⟩) R340109
theorem R783917 : Reach 783917 := rs (se 3 (by rfl) ⟨146984, by rfl⟩) R293969
theorem R685745 : Reach 685745 := rs (se 2 (by rfl) ⟨257154, by rfl⟩) R514309
theorem R194251 : Reach 194251 := rs (se 1 (by rfl) ⟨145688, by rfl⟩) R291377
theorem R227033 : Reach 227033 := rs (se 2 (by rfl) ⟨85137, by rfl⟩) R170275
theorem R96023 : Reach 96023 := rs (se 1 (by rfl) ⟨72017, by rfl⟩) R144035
theorem R194393 : Reach 194393 := rs (se 2 (by rfl) ⟨72897, by rfl⟩) R145795
theorem R161651 : Reach 161651 := rs (se 1 (by rfl) ⟨121238, by rfl⟩) R242477
theorem R325579 : Reach 325579 := rs (se 1 (by rfl) ⟨244184, by rfl⟩) R488369
theorem R358361 : Reach 358361 := rs (se 2 (by rfl) ⟨134385, by rfl⟩) R268771
theorem R456749 : Reach 456749 := rs (se 3 (by rfl) ⟨85640, by rfl⟩) R171281
theorem R96395 : Reach 96395 := rs (se 1 (by rfl) ⟨72296, by rfl⟩) R144593
theorem R686231 : Reach 686231 := rs (se 1 (by rfl) ⟨514673, by rfl⟩) R1029347
theorem R1735181 : Reach 1735181 := rs (se 3 (by rfl) ⟨325346, by rfl⟩) R650693
theorem R162443 : Reach 162443 := rs (se 1 (by rfl) ⟨121832, by rfl⟩) R243665
theorem R588505 : Reach 588505 := rs (se 2 (by rfl) ⟨220689, by rfl⟩) R441379
theorem R326531 : Reach 326531 := rs (se 1 (by rfl) ⟨244898, by rfl⟩) R489797
theorem R1080337 : Reach 1080337 := rs (se 2 (by rfl) ⟨405126, by rfl⟩) R810253
theorem R293977 : Reach 293977 := rs (se 2 (by rfl) ⟨110241, by rfl⟩) R220483
theorem R490769 : Reach 490769 := rs (se 2 (by rfl) ⟨184038, by rfl⟩) R368077
theorem R228683 : Reach 228683 := rs (se 1 (by rfl) ⟨171512, by rfl⟩) R343025
theorem R458135 : Reach 458135 := rs (se 1 (by rfl) ⟨343601, by rfl⟩) R687203
theorem R196055 : Reach 196055 := rs (se 1 (by rfl) ⟨147041, by rfl⟩) R294083
theorem R196235 : Reach 196235 := rs (se 1 (by rfl) ⟨147176, by rfl⟩) R294353
theorem R196289 : Reach 196289 := rs (se 2 (by rfl) ⟨73608, by rfl⟩) R147217
theorem R130763 : Reach 130763 := rs (se 1 (by rfl) ⟨98072, by rfl⟩) R196145
theorem R130775 : Reach 130775 := rs (se 1 (by rfl) ⟨98081, by rfl⟩) R196163
theorem R98059 : Reach 98059 := rs (se 1 (by rfl) ⟨73544, by rfl⟩) R147089
theorem R130841 : Reach 130841 := rs (se 2 (by rfl) ⟨49065, by rfl⟩) R98131
theorem R2817845 : Reach 2817845 := rs (se 5 (by rfl) ⟨132086, by rfl⟩) R264173
theorem R294731 : Reach 294731 := rs (se 1 (by rfl) ⟨221048, by rfl⟩) R442097
theorem R98167 : Reach 98167 := rs (se 1 (by rfl) ⟨73625, by rfl⟩) R147251
theorem R130955 : Reach 130955 := rs (se 1 (by rfl) ⟨98216, by rfl⟩) R196433
theorem R130967 : Reach 130967 := rs (se 1 (by rfl) ⟨98225, by rfl⟩) R196451
theorem R196505 : Reach 196505 := rs (se 2 (by rfl) ⟨73689, by rfl⟩) R147379
theorem R131033 : Reach 131033 := rs (se 2 (by rfl) ⟨49137, by rfl⟩) R98275
theorem R196595 : Reach 196595 := rs (se 1 (by rfl) ⟨147446, by rfl⟩) R294893
theorem R98311 : Reach 98311 := rs (se 1 (by rfl) ⟨73733, by rfl⟩) R147467
theorem R131087 : Reach 131087 := rs (se 1 (by rfl) ⟨98315, by rfl⟩) R196631
theorem R131129 : Reach 131129 := rs (se 2 (by rfl) ⟨49173, by rfl⟩) R98347
theorem R196667 : Reach 196667 := rs (se 1 (by rfl) ⟨147500, by rfl⟩) R295001
theorem R229463 : Reach 229463 := rs (se 1 (by rfl) ⟨172097, by rfl⟩) R344195
theorem R131207 : Reach 131207 := rs (se 1 (by rfl) ⟨98405, by rfl⟩) R196811
theorem R131243 : Reach 131243 := rs (se 1 (by rfl) ⟨98432, by rfl⟩) R196865
theorem R196793 : Reach 196793 := rs (se 2 (by rfl) ⟨73797, by rfl⟩) R147595
theorem R98491 : Reach 98491 := rs (se 1 (by rfl) ⟨73868, by rfl⟩) R147737
theorem R458945 : Reach 458945 := rs (se 2 (by rfl) ⟨172104, by rfl⟩) R344209
theorem R131273 : Reach 131273 := rs (se 2 (by rfl) ⟨49227, by rfl⟩) R98455
theorem R426185 : Reach 426185 := rs (se 2 (by rfl) ⟨159819, by rfl⟩) R319639
theorem R40337621 : Reach 40337621 := rs (se 7 (by rfl) ⟨472706, by rfl⟩) R945413
theorem R327917 : Reach 327917 := rs (se 3 (by rfl) ⟨61484, by rfl⟩) R122969
theorem R2162933 : Reach 2162933 := rs (se 5 (by rfl) ⟨101387, by rfl⟩) R202775
theorem R229675 : Reach 229675 := rs (se 1 (by rfl) ⟨172256, by rfl⟩) R344513
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R2326877 : Reach 2326877 := rs (se 3 (by rfl) ⟨436289, by rfl⟩) R872579
theorem R131447 : Reach 131447 := rs (se 1 (by rfl) ⟨98585, by rfl⟩) R197171
theorem R885127 : Reach 885127 := rs (se 1 (by rfl) ⟨663845, by rfl⟩) R1327691
theorem R131471 : Reach 131471 := rs (se 1 (by rfl) ⟨98603, by rfl⟩) R197207
theorem R131513 : Reach 131513 := rs (se 2 (by rfl) ⟨49317, by rfl⟩) R98635
theorem R229817 : Reach 229817 := rs (se 2 (by rfl) ⟨86181, by rfl⟩) R172363
theorem R131591 : Reach 131591 := rs (se 1 (by rfl) ⟨98693, by rfl⟩) R197387
theorem R197135 : Reach 197135 := rs (se 1 (by rfl) ⟨147851, by rfl⟩) R295703
theorem R197153 : Reach 197153 := rs (se 2 (by rfl) ⟨73932, by rfl⟩) R147865
theorem R131627 : Reach 131627 := rs (se 1 (by rfl) ⟨98720, by rfl⟩) R197441
theorem R131657 : Reach 131657 := rs (se 2 (by rfl) ⟨49371, by rfl⟩) R98743
theorem R98959 : Reach 98959 := rs (se 1 (by rfl) ⟨74219, by rfl⟩) R148439
theorem R131771 : Reach 131771 := rs (se 1 (by rfl) ⟨98828, by rfl⟩) R197657
theorem R131831 : Reach 131831 := rs (se 1 (by rfl) ⟨98873, by rfl⟩) R197747
theorem R131855 : Reach 131855 := rs (se 1 (by rfl) ⟨98891, by rfl⟩) R197783
theorem R131897 : Reach 131897 := rs (se 2 (by rfl) ⟨49461, by rfl⟩) R98923
theorem R361331 : Reach 361331 := rs (se 1 (by rfl) ⟨270998, by rfl⟩) R541997
theorem R197495 : Reach 197495 := rs (se 1 (by rfl) ⟨148121, by rfl⟩) R296243
theorem R131975 : Reach 131975 := rs (se 1 (by rfl) ⟨98981, by rfl⟩) R197963
theorem R132011 : Reach 132011 := rs (se 1 (by rfl) ⟨99008, by rfl⟩) R198017
theorem R295865 : Reach 295865 := rs (se 2 (by rfl) ⟨110949, by rfl⟩) R221899
theorem R132041 : Reach 132041 := rs (se 2 (by rfl) ⟨49515, by rfl⟩) R99031
theorem R427031 : Reach 427031 := rs (se 1 (by rfl) ⟨320273, by rfl⟩) R640547
theorem R197675 : Reach 197675 := rs (se 1 (by rfl) ⟨148256, by rfl⟩) R296513
theorem R132155 : Reach 132155 := rs (se 1 (by rfl) ⟨99116, by rfl⟩) R198233
theorem R132215 : Reach 132215 := rs (se 1 (by rfl) ⟨99161, by rfl⟩) R198323
theorem R99463 : Reach 99463 := rs (se 1 (by rfl) ⟨74597, by rfl⟩) R149195
theorem R132239 : Reach 132239 := rs (se 1 (by rfl) ⟨99179, by rfl⟩) R198359
theorem R132281 : Reach 132281 := rs (se 2 (by rfl) ⟨49605, by rfl⟩) R99211
theorem R132359 : Reach 132359 := rs (se 1 (by rfl) ⟨99269, by rfl⟩) R198539
theorem R132395 : Reach 132395 := rs (se 1 (by rfl) ⟨99296, by rfl⟩) R198593
theorem R99643 : Reach 99643 := rs (se 1 (by rfl) ⟨74732, by rfl⟩) R149465
theorem R132425 : Reach 132425 := rs (se 2 (by rfl) ⟨49659, by rfl⟩) R99319
theorem R198035 : Reach 198035 := rs (se 1 (by rfl) ⟨148526, by rfl⟩) R297053
theorem R132539 : Reach 132539 := rs (se 1 (by rfl) ⟨99404, by rfl⟩) R198809
theorem R198089 : Reach 198089 := rs (se 2 (by rfl) ⟨74283, by rfl⟩) R148567
theorem R460241 : Reach 460241 := rs (se 2 (by rfl) ⟨172590, by rfl⟩) R345181
theorem R132599 : Reach 132599 := rs (se 1 (by rfl) ⟨99449, by rfl⟩) R198899
theorem R296459 : Reach 296459 := rs (se 1 (by rfl) ⟨222344, by rfl⟩) R444689
theorem R132623 : Reach 132623 := rs (se 1 (by rfl) ⟨99467, by rfl⟩) R198935
theorem R132665 : Reach 132665 := rs (se 2 (by rfl) ⟨49749, by rfl⟩) R99499
theorem R886373 : Reach 886373 := rs (se 4 (by rfl) ⟨83097, by rfl⟩) R166195
theorem R296567 : Reach 296567 := rs (se 1 (by rfl) ⟨222425, by rfl⟩) R444851
theorem R132743 : Reach 132743 := rs (se 1 (by rfl) ⟨99557, by rfl⟩) R199115
theorem R132779 : Reach 132779 := rs (se 1 (by rfl) ⟨99584, by rfl⟩) R199169
theorem R132809 : Reach 132809 := rs (se 2 (by rfl) ⟨49803, by rfl⟩) R99607
theorem R100111 : Reach 100111 := rs (se 1 (by rfl) ⟨75083, by rfl⟩) R150167
theorem R165665 : Reach 165665 := rs (se 2 (by rfl) ⟨62124, by rfl⟩) R124249
theorem R132923 : Reach 132923 := rs (se 1 (by rfl) ⟨99692, by rfl⟩) R199385
theorem R132983 : Reach 132983 := rs (se 1 (by rfl) ⟨99737, by rfl⟩) R199475
theorem R133007 : Reach 133007 := rs (se 1 (by rfl) ⟨99755, by rfl⟩) R199511
theorem R165817 : Reach 165817 := rs (se 2 (by rfl) ⟨62181, by rfl⟩) R124363
theorem R133049 : Reach 133049 := rs (se 2 (by rfl) ⟨49893, by rfl⟩) R99787
theorem R133127 : Reach 133127 := rs (se 1 (by rfl) ⟨99845, by rfl⟩) R199691
theorem R133163 : Reach 133163 := rs (se 1 (by rfl) ⟨99872, by rfl⟩) R199745
theorem R133193 : Reach 133193 := rs (se 2 (by rfl) ⟨49947, by rfl⟩) R99895
theorem R198791 : Reach 198791 := rs (se 1 (by rfl) ⟨149093, by rfl⟩) R298187
theorem R133307 : Reach 133307 := rs (se 1 (by rfl) ⟨99980, by rfl⟩) R199961
theorem R297161 : Reach 297161 := rs (se 2 (by rfl) ⟨111435, by rfl⟩) R222871
theorem R133367 : Reach 133367 := rs (se 1 (by rfl) ⟨100025, by rfl⟩) R200051
theorem R100615 : Reach 100615 := rs (se 1 (by rfl) ⟨75461, by rfl⟩) R150923
theorem R133391 : Reach 133391 := rs (se 1 (by rfl) ⟨100043, by rfl⟩) R200087
theorem R133433 : Reach 133433 := rs (se 2 (by rfl) ⟨50037, by rfl⟩) R100075
theorem R198971 : Reach 198971 := rs (se 1 (by rfl) ⟨149228, by rfl⟩) R298457
theorem R133511 : Reach 133511 := rs (se 1 (by rfl) ⟨100133, by rfl⟩) R200267
theorem R559507 : Reach 559507 := rs (se 1 (by rfl) ⟨419630, by rfl⟩) R839261
theorem R133547 : Reach 133547 := rs (se 1 (by rfl) ⟨100160, by rfl⟩) R200321
theorem R199097 : Reach 199097 := rs (se 2 (by rfl) ⟨74661, by rfl⟩) R149323
theorem R100795 : Reach 100795 := rs (se 1 (by rfl) ⟨75596, by rfl⟩) R151193
theorem R133577 : Reach 133577 := rs (se 2 (by rfl) ⟨50091, by rfl⟩) R100183
theorem R231995 : Reach 231995 := rs (se 1 (by rfl) ⟨173996, by rfl⟩) R347993
theorem R133691 : Reach 133691 := rs (se 1 (by rfl) ⟨100268, by rfl⟩) R200537
theorem R133751 : Reach 133751 := rs (se 1 (by rfl) ⟨100313, by rfl⟩) R200627
theorem R232055 : Reach 232055 := rs (se 1 (by rfl) ⟨174041, by rfl⟩) R348083
theorem R133775 : Reach 133775 := rs (se 1 (by rfl) ⟨100331, by rfl⟩) R200663
theorem R133817 : Reach 133817 := rs (se 2 (by rfl) ⟨50181, by rfl⟩) R100363
theorem R133895 : Reach 133895 := rs (se 1 (by rfl) ⟨100421, by rfl⟩) R200843
theorem R1018639 : Reach 1018639 := rs (se 1 (by rfl) ⟨763979, by rfl⟩) R1527959
theorem R199439 : Reach 199439 := rs (se 1 (by rfl) ⟨149579, by rfl⟩) R299159
theorem R199457 : Reach 199457 := rs (se 2 (by rfl) ⟨74796, by rfl⟩) R149593
theorem R1936163 : Reach 1936163 := rs (se 1 (by rfl) ⟨1452122, by rfl⟩) R2904245
theorem R133931 : Reach 133931 := rs (se 1 (by rfl) ⟨100448, by rfl⟩) R200897
theorem R133961 : Reach 133961 := rs (se 2 (by rfl) ⟨50235, by rfl⟩) R100471
theorem R985945 : Reach 985945 := rs (se 2 (by rfl) ⟨369729, by rfl⟩) R739459
theorem R428915 : Reach 428915 := rs (se 1 (by rfl) ⟨321686, by rfl⟩) R643373
theorem R297863 : Reach 297863 := rs (se 1 (by rfl) ⟨223397, by rfl⟩) R446795
theorem R101263 : Reach 101263 := rs (se 1 (by rfl) ⟨75947, by rfl⟩) R151895
theorem R134075 : Reach 134075 := rs (se 1 (by rfl) ⟨100556, by rfl⟩) R201113
theorem R134135 : Reach 134135 := rs (se 1 (by rfl) ⟨100601, by rfl⟩) R201203
theorem R1281035 : Reach 1281035 := rs (se 1 (by rfl) ⟨960776, by rfl⟩) R1921553
theorem R134159 : Reach 134159 := rs (se 1 (by rfl) ⟨100619, by rfl⟩) R201239
theorem R134201 : Reach 134201 := rs (se 2 (by rfl) ⟨50325, by rfl⟩) R100651
theorem R199799 : Reach 199799 := rs (se 1 (by rfl) ⟨149849, by rfl⟩) R299699
theorem R134279 : Reach 134279 := rs (se 1 (by rfl) ⟨100709, by rfl⟩) R201419
theorem R134315 : Reach 134315 := rs (se 1 (by rfl) ⟨100736, by rfl⟩) R201473
theorem R134345 : Reach 134345 := rs (se 2 (by rfl) ⟨50379, by rfl⟩) R100759
theorem R1117421 : Reach 1117421 := rs (se 3 (by rfl) ⟨209516, by rfl⟩) R419033
theorem R298241 : Reach 298241 := rs (se 2 (by rfl) ⟨111840, by rfl⟩) R223681
theorem R363809 : Reach 363809 := rs (se 2 (by rfl) ⟨136428, by rfl⟩) R272857
theorem R199979 : Reach 199979 := rs (se 1 (by rfl) ⟨149984, by rfl⟩) R299969
theorem R134459 : Reach 134459 := rs (se 1 (by rfl) ⟨100844, by rfl⟩) R201689
theorem R134519 : Reach 134519 := rs (se 1 (by rfl) ⟨100889, by rfl⟩) R201779
theorem R101767 : Reach 101767 := rs (se 1 (by rfl) ⟨76325, by rfl⟩) R152651
theorem R134543 : Reach 134543 := rs (se 1 (by rfl) ⟨100907, by rfl⟩) R201815
theorem R134585 : Reach 134585 := rs (se 2 (by rfl) ⟨50469, by rfl⟩) R100939
theorem R134663 : Reach 134663 := rs (se 1 (by rfl) ⟨100997, by rfl⟩) R201995
theorem R134699 : Reach 134699 := rs (se 1 (by rfl) ⟨101024, by rfl⟩) R202049
theorem R101947 : Reach 101947 := rs (se 1 (by rfl) ⟨76460, by rfl⟩) R152921
theorem R134729 : Reach 134729 := rs (se 2 (by rfl) ⟨50523, by rfl⟩) R101047
theorem R200339 : Reach 200339 := rs (se 1 (by rfl) ⟨150254, by rfl⟩) R300509
theorem R167609 : Reach 167609 := rs (se 2 (by rfl) ⟨62853, by rfl⟩) R125707
theorem R134843 : Reach 134843 := rs (se 1 (by rfl) ⟨101132, by rfl⟩) R202265
theorem R200393 : Reach 200393 := rs (se 2 (by rfl) ⟨75147, by rfl⟩) R150295
theorem R134903 : Reach 134903 := rs (se 1 (by rfl) ⟨101177, by rfl⟩) R202355
theorem R134927 : Reach 134927 := rs (se 1 (by rfl) ⟨101195, by rfl⟩) R202391
theorem R134969 : Reach 134969 := rs (se 2 (by rfl) ⟨50613, by rfl⟩) R101227
theorem R135047 : Reach 135047 := rs (se 1 (by rfl) ⟨101285, by rfl⟩) R202571
theorem R429977 : Reach 429977 := rs (se 2 (by rfl) ⟨161241, by rfl⟩) R322483
theorem R135083 : Reach 135083 := rs (se 1 (by rfl) ⟨101312, by rfl⟩) R202625
theorem R135113 : Reach 135113 := rs (se 2 (by rfl) ⟨50667, by rfl⟩) R101335
theorem R102415 : Reach 102415 := rs (se 1 (by rfl) ⟨76811, by rfl⟩) R153623
theorem R299051 : Reach 299051 := rs (se 1 (by rfl) ⟨224288, by rfl⟩) R448577
theorem R135227 : Reach 135227 := rs (se 1 (by rfl) ⟨101420, by rfl⟩) R202841
theorem R135287 : Reach 135287 := rs (se 1 (by rfl) ⟨101465, by rfl⟩) R202931
theorem R135311 : Reach 135311 := rs (se 1 (by rfl) ⟨101483, by rfl⟩) R202967
theorem R266387 : Reach 266387 := rs (se 1 (by rfl) ⟨199790, by rfl⟩) R399581
theorem R135353 : Reach 135353 := rs (se 2 (by rfl) ⟨50757, by rfl⟩) R101515
theorem R135431 : Reach 135431 := rs (se 1 (by rfl) ⟨101573, by rfl⟩) R203147
theorem R135467 : Reach 135467 := rs (se 1 (by rfl) ⟨101600, by rfl⟩) R203201
theorem R135497 : Reach 135497 := rs (se 2 (by rfl) ⟨50811, by rfl⟩) R101623
theorem R201095 : Reach 201095 := rs (se 1 (by rfl) ⟨150821, by rfl⟩) R301643
theorem R135611 : Reach 135611 := rs (se 1 (by rfl) ⟨101708, by rfl⟩) R203417
theorem R135671 : Reach 135671 := rs (se 1 (by rfl) ⟨101753, by rfl⟩) R203507
theorem R135695 : Reach 135695 := rs (se 1 (by rfl) ⟨101771, by rfl⟩) R203543
theorem R135737 : Reach 135737 := rs (se 2 (by rfl) ⟨50901, by rfl⟩) R101803
theorem R201275 : Reach 201275 := rs (se 1 (by rfl) ⟨150956, by rfl⟩) R301913
theorem R135815 : Reach 135815 := rs (se 1 (by rfl) ⟨101861, by rfl⟩) R203723
theorem R135851 : Reach 135851 := rs (se 1 (by rfl) ⟨101888, by rfl⟩) R203777
theorem R201401 : Reach 201401 := rs (se 2 (by rfl) ⟨75525, by rfl⟩) R151051
theorem R135881 : Reach 135881 := rs (se 2 (by rfl) ⟨50955, by rfl⟩) R101911
theorem R332545 : Reach 332545 := rs (se 2 (by rfl) ⟨124704, by rfl⟩) R249409
theorem R135995 : Reach 135995 := rs (se 1 (by rfl) ⟨101996, by rfl⟩) R203993
theorem R398195 : Reach 398195 := rs (se 1 (by rfl) ⟨298646, by rfl⟩) R597293
theorem R693107 : Reach 693107 := rs (se 1 (by rfl) ⟨519830, by rfl⟩) R1039661
theorem R136055 : Reach 136055 := rs (se 1 (by rfl) ⟨102041, by rfl⟩) R204083
theorem R136079 : Reach 136079 := rs (se 1 (by rfl) ⟨102059, by rfl⟩) R204119
theorem R136121 : Reach 136121 := rs (se 2 (by rfl) ⟨51045, by rfl⟩) R102091
theorem R136199 : Reach 136199 := rs (se 1 (by rfl) ⟨102149, by rfl⟩) R204299
theorem R201743 : Reach 201743 := rs (se 1 (by rfl) ⟨151307, by rfl⟩) R302615
theorem R201761 : Reach 201761 := rs (se 2 (by rfl) ⟨75660, by rfl⟩) R151321
theorem R136235 : Reach 136235 := rs (se 1 (by rfl) ⟨102176, by rfl⟩) R204353
theorem R824381 : Reach 824381 := rs (se 3 (by rfl) ⟨154571, by rfl⟩) R309143
theorem R136265 : Reach 136265 := rs (se 2 (by rfl) ⟨51099, by rfl⟩) R102199
theorem R496813 : Reach 496813 := rs (se 3 (by rfl) ⟨93152, by rfl⟩) R186305
theorem R136379 : Reach 136379 := rs (se 1 (by rfl) ⟨102284, by rfl⟩) R204569
theorem R136439 : Reach 136439 := rs (se 1 (by rfl) ⟨102329, by rfl⟩) R204659
theorem R136463 : Reach 136463 := rs (se 1 (by rfl) ⟨102347, by rfl⟩) R204695
theorem R136505 : Reach 136505 := rs (se 2 (by rfl) ⟨51189, by rfl⟩) R102379
theorem R300347 : Reach 300347 := rs (se 1 (by rfl) ⟨225260, by rfl⟩) R450521
theorem R202103 : Reach 202103 := rs (se 1 (by rfl) ⟨151577, by rfl⟩) R303155
theorem R136583 : Reach 136583 := rs (se 1 (by rfl) ⟨102437, by rfl⟩) R204875
theorem R136619 : Reach 136619 := rs (se 1 (by rfl) ⟨102464, by rfl⟩) R204929
theorem R136649 : Reach 136649 := rs (se 2 (by rfl) ⟨51243, by rfl⟩) R102487
theorem R202283 : Reach 202283 := rs (se 1 (by rfl) ⟨151712, by rfl⟩) R303425
theorem R169607 : Reach 169607 := rs (se 1 (by rfl) ⟨127205, by rfl⟩) R254411
theorem R300833 : Reach 300833 := rs (se 2 (by rfl) ⟨112812, by rfl⟩) R225625
theorem R202643 : Reach 202643 := rs (se 1 (by rfl) ⟨151982, by rfl⟩) R303965
theorem R202697 : Reach 202697 := rs (se 2 (by rfl) ⟨76011, by rfl⟩) R152023
theorem R301427 : Reach 301427 := rs (se 1 (by rfl) ⟨226070, by rfl⟩) R452141
theorem R203399 : Reach 203399 := rs (se 1 (by rfl) ⟨152549, by rfl⟩) R305099
theorem R826163 : Reach 826163 := rs (se 1 (by rfl) ⟨619622, by rfl⟩) R1239245
theorem R203579 : Reach 203579 := rs (se 1 (by rfl) ⟨152684, by rfl⟩) R305369
theorem R203705 : Reach 203705 := rs (se 2 (by rfl) ⟨76389, by rfl⟩) R152779
theorem R433163 : Reach 433163 := rs (se 1 (by rfl) ⟨324872, by rfl⟩) R649745
theorem R236573 : Reach 236573 := rs (se 3 (by rfl) ⟨44357, by rfl⟩) R88715
theorem R433181 : Reach 433181 := rs (se 3 (by rfl) ⟨81221, by rfl⟩) R162443
theorem R171209 : Reach 171209 := rs (se 2 (by rfl) ⟨64203, by rfl⟩) R128407
theorem R204047 : Reach 204047 := rs (se 1 (by rfl) ⟨153035, by rfl⟩) R306071
theorem R204065 : Reach 204065 := rs (se 2 (by rfl) ⟨76524, by rfl⟩) R153049
theorem R499229 : Reach 499229 := rs (se 3 (by rfl) ⟨93605, by rfl⟩) R187211
theorem R269867 : Reach 269867 := rs (se 1 (by rfl) ⟨202400, by rfl⟩) R404801
theorem R335447 : Reach 335447 := rs (se 1 (by rfl) ⟨251585, by rfl⟩) R503171
theorem R204407 : Reach 204407 := rs (se 1 (by rfl) ⟨153305, by rfl⟩) R306611
theorem R564965 : Reach 564965 := rs (se 4 (by rfl) ⟨52965, by rfl⟩) R105931
theorem R204587 : Reach 204587 := rs (se 1 (by rfl) ⟨153440, by rfl⟩) R306881
theorem R434105 : Reach 434105 := rs (se 2 (by rfl) ⟨162789, by rfl⟩) R325579
theorem R335933 : Reach 335933 := rs (se 3 (by rfl) ⟨62987, by rfl⟩) R125975
theorem R204947 : Reach 204947 := rs (se 1 (by rfl) ⟨153710, by rfl⟩) R307421
theorem R205001 : Reach 205001 := rs (se 2 (by rfl) ⟨76875, by rfl⟩) R153751
theorem R107023 : Reach 107023 := rs (se 1 (by rfl) ⟨80267, by rfl⟩) R160535
theorem R2138885 : Reach 2138885 := rs (se 4 (by rfl) ⟨200520, by rfl⟩) R401041
theorem R304019 : Reach 304019 := rs (se 1 (by rfl) ⟨228014, by rfl⟩) R456029
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R632009 : Reach 632009 := rs (se 2 (by rfl) ⟨237003, by rfl⟩) R474007
theorem R107767 : Reach 107767 := rs (se 1 (by rfl) ⟨80825, by rfl⟩) R161651
theorem R238907 : Reach 238907 := rs (se 1 (by rfl) ⟨179180, by rfl⟩) R358361
theorem R304499 : Reach 304499 := rs (se 1 (by rfl) ⟨228374, by rfl⟩) R456749
theorem R1156787 : Reach 1156787 := rs (se 1 (by rfl) ⟨867590, by rfl⟩) R1735181
theorem R534209 : Reach 534209 := rs (se 2 (by rfl) ⟨200328, by rfl⟩) R400657
theorem R337679 : Reach 337679 := rs (se 1 (by rfl) ⟨253259, by rfl⟩) R506519
theorem R206651 : Reach 206651 := rs (se 1 (by rfl) ⟨154988, by rfl⟩) R309977
theorem R501713 : Reach 501713 := rs (se 2 (by rfl) ⟨188142, by rfl⟩) R376285
theorem R305213 : Reach 305213 := rs (se 3 (by rfl) ⟨57227, by rfl⟩) R114455
theorem R305423 : Reach 305423 := rs (se 1 (by rfl) ⟨229067, by rfl⟩) R458135
theorem R305693 : Reach 305693 := rs (se 3 (by rfl) ⟨57317, by rfl⟩) R114635
theorem R1878563 : Reach 1878563 := rs (se 1 (by rfl) ⟨1408922, by rfl⟩) R2817845
theorem R141959 : Reach 141959 := rs (se 1 (by rfl) ⟨106469, by rfl⟩) R212939
theorem R666305 : Reach 666305 := rs (se 2 (by rfl) ⟨249864, by rfl⟩) R499729
theorem R273239 : Reach 273239 := rs (se 1 (by rfl) ⟨204929, by rfl⟩) R409859
theorem R699479 : Reach 699479 := rs (se 1 (by rfl) ⟨524609, by rfl⟩) R1049219
theorem R142651 : Reach 142651 := rs (se 1 (by rfl) ⟨106988, by rfl⟩) R213977
theorem R339335 : Reach 339335 := rs (se 1 (by rfl) ⟨254501, by rfl⟩) R509003
theorem R503225 : Reach 503225 := rs (se 2 (by rfl) ⟨188709, by rfl⟩) R377419
theorem R798137 : Reach 798137 := rs (se 2 (by rfl) ⟨299301, by rfl⟩) R598603
theorem R404945 : Reach 404945 := rs (se 2 (by rfl) ⟨151854, by rfl⟩) R303709
theorem R372235 : Reach 372235 := rs (se 1 (by rfl) ⟨279176, by rfl⟩) R558353
theorem R208585 : Reach 208585 := rs (se 2 (by rfl) ⟨78219, by rfl⟩) R156439
theorem R1027889 : Reach 1027889 := rs (se 2 (by rfl) ⟨385458, by rfl⟩) R770917
theorem R503603 : Reach 503603 := rs (se 1 (by rfl) ⟨377702, by rfl⟩) R755405
theorem R110479 : Reach 110479 := rs (se 1 (by rfl) ⟨82859, by rfl⟩) R165719
theorem R307097 : Reach 307097 := rs (se 2 (by rfl) ⟨115161, by rfl⟩) R230323
theorem R537131 : Reach 537131 := rs (se 1 (by rfl) ⟨402848, by rfl⟩) R805697
theorem R111223 : Reach 111223 := rs (se 1 (by rfl) ⟨83417, by rfl⟩) R166835
theorem R242617 : Reach 242617 := rs (se 2 (by rfl) ⟨90981, by rfl⟩) R181963
theorem R111547 : Reach 111547 := rs (se 1 (by rfl) ⟨83660, by rfl⟩) R167321
theorem R341111 : Reach 341111 := rs (se 1 (by rfl) ⟨255833, by rfl⟩) R511667
theorem R210055 : Reach 210055 := rs (se 1 (by rfl) ⟨157541, by rfl⟩) R315083
theorem R505061 : Reach 505061 := rs (se 4 (by rfl) ⟨47349, by rfl⟩) R94699
theorem R112043 : Reach 112043 := rs (se 1 (by rfl) ⟨84032, by rfl⟩) R168065
theorem R243233 : Reach 243233 := rs (se 2 (by rfl) ⟨91212, by rfl⟩) R182425
theorem R243319 : Reach 243319 := rs (se 1 (by rfl) ⟨182489, by rfl⟩) R364979
theorem R308855 : Reach 308855 := rs (se 1 (by rfl) ⟨231641, by rfl⟩) R463283
theorem R1226497 : Reach 1226497 := rs (se 2 (by rfl) ⟨459936, by rfl⟩) R919873
theorem R112519 : Reach 112519 := rs (se 1 (by rfl) ⟨84389, by rfl⟩) R168779
theorem R997271 : Reach 997271 := rs (se 1 (by rfl) ⟨747953, by rfl⟩) R1495907
theorem R669707 : Reach 669707 := rs (se 1 (by rfl) ⟨502280, by rfl⟩) R1004561
theorem R342083 : Reach 342083 := rs (se 1 (by rfl) ⟨256562, by rfl⟩) R513125
theorem R113015 : Reach 113015 := rs (se 1 (by rfl) ⟨84761, by rfl⟩) R169523
theorem R342539 : Reach 342539 := rs (se 1 (by rfl) ⟨256904, by rfl⟩) R513809
theorem R113167 : Reach 113167 := rs (se 1 (by rfl) ⟨84875, by rfl⟩) R169751
theorem R113339 : Reach 113339 := rs (se 1 (by rfl) ⟨85004, by rfl⟩) R170009
theorem R114311 : Reach 114311 := rs (se 1 (by rfl) ⟨85733, by rfl⟩) R171467
theorem R376609 : Reach 376609 := rs (se 2 (by rfl) ⟨141228, by rfl⟩) R282457
theorem R442259 : Reach 442259 := rs (se 1 (by rfl) ⟨331694, by rfl⟩) R663389
theorem R671651 : Reach 671651 := rs (se 1 (by rfl) ⟨503738, by rfl⟩) R1007477
theorem R147575 : Reach 147575 := rs (se 1 (by rfl) ⟨110681, by rfl⟩) R221363
theorem R114959 : Reach 114959 := rs (se 1 (by rfl) ⟨86219, by rfl⟩) R172439
theorem R508295 : Reach 508295 := rs (se 1 (by rfl) ⟨381221, by rfl⟩) R762443
theorem R967133 : Reach 967133 := rs (se 3 (by rfl) ⟨181337, by rfl⟩) R362675
theorem R148027 : Reach 148027 := rs (se 1 (by rfl) ⟨111020, by rfl⟩) R222041
theorem R508477 : Reach 508477 := rs (se 3 (by rfl) ⟨95339, by rfl⟩) R190679
theorem R344695 : Reach 344695 := rs (se 1 (by rfl) ⟨258521, by rfl⟩) R517043
theorem R148169 : Reach 148169 := rs (se 2 (by rfl) ⟨55563, by rfl⟩) R111127
theorem R508931 : Reach 508931 := rs (se 1 (by rfl) ⟨381698, by rfl⟩) R763397
theorem R1164577 : Reach 1164577 := rs (se 2 (by rfl) ⟨436716, by rfl⟩) R873433
theorem R148871 : Reach 148871 := rs (se 1 (by rfl) ⟨111653, by rfl⟩) R223307
theorem R345667 : Reach 345667 := rs (se 1 (by rfl) ⟨259250, by rfl⟩) R518501
theorem R345971 : Reach 345971 := rs (se 1 (by rfl) ⟨259478, by rfl⟩) R518957
theorem R149519 : Reach 149519 := rs (se 1 (by rfl) ⟨112139, by rfl⟩) R224279
theorem R1001645 : Reach 1001645 := rs (se 3 (by rfl) ⟨187808, by rfl⟩) R375617
theorem R510209 : Reach 510209 := rs (se 2 (by rfl) ⟨191328, by rfl⟩) R382657
theorem R674081 : Reach 674081 := rs (se 2 (by rfl) ⟨252780, by rfl⟩) R505561
theorem R248123 : Reach 248123 := rs (se 1 (by rfl) ⟨186092, by rfl⟩) R372185
theorem R248179 : Reach 248179 := rs (se 1 (by rfl) ⟨186134, by rfl⟩) R372269
theorem R150059 : Reach 150059 := rs (se 1 (by rfl) ⟨112544, by rfl⟩) R225089
theorem R248521 : Reach 248521 := rs (se 2 (by rfl) ⟨93195, by rfl⟩) R186391
theorem R183073 : Reach 183073 := rs (se 2 (by rfl) ⟨68652, by rfl⟩) R137305
theorem R772901 : Reach 772901 := rs (se 4 (by rfl) ⟨72459, by rfl⟩) R144919
theorem R445337 : Reach 445337 := rs (se 2 (by rfl) ⟨167001, by rfl⟩) R334003
theorem R150457 : Reach 150457 := rs (se 2 (by rfl) ⟨56421, by rfl⟩) R112843
theorem R379991 : Reach 379991 := rs (se 1 (by rfl) ⟨284993, by rfl⟩) R569987
theorem R675053 : Reach 675053 := rs (se 3 (by rfl) ⟨126572, by rfl⟩) R253145
theorem R151159 : Reach 151159 := rs (se 1 (by rfl) ⟨113369, by rfl⟩) R226739
theorem R151355 : Reach 151355 := rs (se 1 (by rfl) ⟨113516, by rfl⟩) R227033
theorem R118903 : Reach 118903 := rs (se 1 (by rfl) ⟨89177, by rfl⟩) R178355
theorem R151753 : Reach 151753 := rs (se 2 (by rfl) ⟨56907, by rfl⟩) R113815
theorem R1036637 : Reach 1036637 := rs (se 3 (by rfl) ⟨194369, by rfl⟩) R388739
theorem R217687 : Reach 217687 := rs (se 1 (by rfl) ⟨163265, by rfl⟩) R326531
theorem R643889 : Reach 643889 := rs (se 2 (by rfl) ⟨241458, by rfl⟩) R482917
theorem R250685 : Reach 250685 := rs (se 3 (by rfl) ⟨47003, by rfl⟩) R94007
theorem R316295 : Reach 316295 := rs (se 1 (by rfl) ⟨237221, by rfl⟩) R474443
theorem R152455 : Reach 152455 := rs (se 1 (by rfl) ⟨114341, by rfl⟩) R228683
theorem R381905 : Reach 381905 := rs (se 2 (by rfl) ⟨143214, by rfl⟩) R286429
theorem R250913 : Reach 250913 := rs (se 2 (by rfl) ⟨94092, by rfl⟩) R188185
theorem R676997 : Reach 676997 := rs (se 4 (by rfl) ⟨63468, by rfl⟩) R126937
theorem R87175 : Reach 87175 := rs (se 1 (by rfl) ⟨65381, by rfl⟩) R130763
theorem R87183 : Reach 87183 := rs (se 1 (by rfl) ⟨65387, by rfl⟩) R130775
theorem R87227 : Reach 87227 := rs (se 1 (by rfl) ⟨65420, by rfl⟩) R130841
theorem R120055 : Reach 120055 := rs (se 1 (by rfl) ⟨90041, by rfl⟩) R180083
theorem R87303 : Reach 87303 := rs (se 1 (by rfl) ⟨65477, by rfl⟩) R130955
theorem R87311 : Reach 87311 := rs (se 1 (by rfl) ⟨65483, by rfl⟩) R130967
theorem R87355 : Reach 87355 := rs (se 1 (by rfl) ⟨65516, by rfl⟩) R131033
theorem R251255 : Reach 251255 := rs (se 1 (by rfl) ⟨188441, by rfl⟩) R376883
theorem R87431 : Reach 87431 := rs (se 1 (by rfl) ⟨65573, by rfl⟩) R131147
theorem R87439 : Reach 87439 := rs (se 1 (by rfl) ⟨65579, by rfl⟩) R131159
theorem R447929 : Reach 447929 := rs (se 2 (by rfl) ⟨167973, by rfl⟩) R335947
theorem R87483 : Reach 87483 := rs (se 1 (by rfl) ⟨65612, by rfl⟩) R131225
theorem R87559 : Reach 87559 := rs (se 1 (by rfl) ⟨65669, by rfl⟩) R131339
theorem R87567 : Reach 87567 := rs (se 1 (by rfl) ⟨65675, by rfl⟩) R131351
theorem R153103 : Reach 153103 := rs (se 1 (by rfl) ⟨114827, by rfl⟩) R229655
theorem R87611 : Reach 87611 := rs (se 1 (by rfl) ⟨65708, by rfl⟩) R131417
theorem R87687 : Reach 87687 := rs (se 1 (by rfl) ⟨65765, by rfl⟩) R131531
theorem R87695 : Reach 87695 := rs (se 1 (by rfl) ⟨65771, by rfl⟩) R131543
theorem R87739 : Reach 87739 := rs (se 1 (by rfl) ⟨65804, by rfl⟩) R131609
theorem R87815 : Reach 87815 := rs (se 1 (by rfl) ⟨65861, by rfl⟩) R131723
theorem R87823 : Reach 87823 := rs (se 1 (by rfl) ⟨65867, by rfl⟩) R131735
theorem R284431 : Reach 284431 := rs (se 1 (by rfl) ⟨213323, by rfl⟩) R426647
theorem R87867 : Reach 87867 := rs (se 1 (by rfl) ⟨65900, by rfl⟩) R131801
theorem R87943 : Reach 87943 := rs (se 1 (by rfl) ⟨65957, by rfl⟩) R131915
theorem R87951 : Reach 87951 := rs (se 1 (by rfl) ⟨65963, by rfl⟩) R131927
theorem R87995 : Reach 87995 := rs (se 1 (by rfl) ⟨65996, by rfl⟩) R131993
theorem R88071 : Reach 88071 := rs (se 1 (by rfl) ⟨66053, by rfl⟩) R132107
theorem R88079 : Reach 88079 := rs (se 1 (by rfl) ⟨66059, by rfl⟩) R132119
theorem R153643 : Reach 153643 := rs (se 1 (by rfl) ⟨115232, by rfl⟩) R230465
theorem R88123 : Reach 88123 := rs (se 1 (by rfl) ⟨66092, by rfl⟩) R132185
theorem R88199 : Reach 88199 := rs (se 1 (by rfl) ⟨66149, by rfl⟩) R132299
theorem R88207 : Reach 88207 := rs (se 1 (by rfl) ⟨66155, by rfl⟩) R132311
theorem R88251 : Reach 88251 := rs (se 1 (by rfl) ⟨66188, by rfl⟩) R132377
theorem R88327 : Reach 88327 := rs (se 1 (by rfl) ⟨66245, by rfl⟩) R132491
theorem R88335 : Reach 88335 := rs (se 1 (by rfl) ⟨66251, by rfl⟩) R132503
theorem R88379 : Reach 88379 := rs (se 1 (by rfl) ⟨66284, by rfl⟩) R132569
theorem R88455 : Reach 88455 := rs (se 1 (by rfl) ⟨66341, by rfl⟩) R132683
theorem R88463 : Reach 88463 := rs (se 1 (by rfl) ⟨66347, by rfl⟩) R132695
theorem R514451 : Reach 514451 := rs (se 1 (by rfl) ⟨385838, by rfl⟩) R771677
theorem R121259 : Reach 121259 := rs (se 1 (by rfl) ⟨90944, by rfl⟩) R181889
theorem R88507 : Reach 88507 := rs (se 1 (by rfl) ⟨66380, by rfl⟩) R132761
theorem R88583 : Reach 88583 := rs (se 1 (by rfl) ⟨66437, by rfl⟩) R132875
theorem R88591 : Reach 88591 := rs (se 1 (by rfl) ⟨66443, by rfl⟩) R132887
theorem R514583 : Reach 514583 := rs (se 1 (by rfl) ⟨385937, by rfl⟩) R771875
theorem R88635 : Reach 88635 := rs (se 1 (by rfl) ⟨66476, by rfl⟩) R132953
theorem R88711 : Reach 88711 := rs (se 1 (by rfl) ⟨66533, by rfl⟩) R133067
theorem R88719 : Reach 88719 := rs (se 1 (by rfl) ⟨66539, by rfl⟩) R133079
theorem R88763 : Reach 88763 := rs (se 1 (by rfl) ⟨66572, by rfl⟩) R133145
theorem R449225 : Reach 449225 := rs (se 2 (by rfl) ⟨168459, by rfl⟩) R336919
theorem R88839 : Reach 88839 := rs (se 1 (by rfl) ⟨66629, by rfl⟩) R133259
theorem R88847 : Reach 88847 := rs (se 1 (by rfl) ⟨66635, by rfl⟩) R133271
theorem R875279 : Reach 875279 := rs (se 1 (by rfl) ⟨656459, by rfl⟩) R1312919
theorem R973619 : Reach 973619 := rs (se 1 (by rfl) ⟨730214, by rfl⟩) R1460429
theorem R88891 : Reach 88891 := rs (se 1 (by rfl) ⟨66668, by rfl⟩) R133337
theorem R1891187 : Reach 1891187 := rs (se 1 (by rfl) ⟨1418390, by rfl⟩) R2836781
theorem R88967 : Reach 88967 := rs (se 1 (by rfl) ⟨66725, by rfl⟩) R133451
theorem R482183 : Reach 482183 := rs (se 1 (by rfl) ⟨361637, by rfl⟩) R723275
theorem R88975 : Reach 88975 := rs (se 1 (by rfl) ⟨66731, by rfl⟩) R133463
theorem R89019 : Reach 89019 := rs (se 1 (by rfl) ⟨66764, by rfl⟩) R133529
theorem R89095 : Reach 89095 := rs (se 1 (by rfl) ⟨66821, by rfl⟩) R133643
theorem R89103 : Reach 89103 := rs (se 1 (by rfl) ⟨66827, by rfl⟩) R133655
theorem R89147 : Reach 89147 := rs (se 1 (by rfl) ⟨66860, by rfl⟩) R133721
theorem R89223 : Reach 89223 := rs (se 1 (by rfl) ⟨66917, by rfl⟩) R133835
theorem R89231 : Reach 89231 := rs (se 1 (by rfl) ⟨66923, by rfl⟩) R133847
theorem R89275 : Reach 89275 := rs (se 1 (by rfl) ⟨66956, by rfl⟩) R133913
theorem R89351 : Reach 89351 := rs (se 1 (by rfl) ⟨67013, by rfl⟩) R134027
theorem R89359 : Reach 89359 := rs (se 1 (by rfl) ⟨67019, by rfl⟩) R134039
theorem R89403 : Reach 89403 := rs (se 1 (by rfl) ⟨67052, by rfl⟩) R134105
theorem R89479 : Reach 89479 := rs (se 1 (by rfl) ⟨67109, by rfl⟩) R134219
theorem R89487 : Reach 89487 := rs (se 1 (by rfl) ⟨67115, by rfl⟩) R134231
theorem R89531 : Reach 89531 := rs (se 1 (by rfl) ⟨67148, by rfl⟩) R134297
theorem R679427 : Reach 679427 := rs (se 1 (by rfl) ⟨509570, by rfl⟩) R1019141
theorem R89607 : Reach 89607 := rs (se 1 (by rfl) ⟨67205, by rfl⟩) R134411
theorem R89615 : Reach 89615 := rs (se 1 (by rfl) ⟨67211, by rfl⟩) R134423
theorem R220715 : Reach 220715 := rs (se 1 (by rfl) ⟨165536, by rfl⟩) R331073
theorem R89659 : Reach 89659 := rs (se 1 (by rfl) ⟨67244, by rfl⟩) R134489
theorem R2154059 : Reach 2154059 := rs (se 1 (by rfl) ⟨1615544, by rfl⟩) R3231089
theorem R89735 : Reach 89735 := rs (se 1 (by rfl) ⟨67301, by rfl⟩) R134603
theorem R89743 : Reach 89743 := rs (se 1 (by rfl) ⟨67307, by rfl⟩) R134615
theorem R89787 : Reach 89787 := rs (se 1 (by rfl) ⟨67340, by rfl⟩) R134681
theorem R319177 : Reach 319177 := rs (se 2 (by rfl) ⟨119691, by rfl⟩) R239383
theorem R89863 : Reach 89863 := rs (se 1 (by rfl) ⟨67397, by rfl⟩) R134795
theorem R89871 : Reach 89871 := rs (se 1 (by rfl) ⟨67403, by rfl⟩) R134807
theorem R89915 : Reach 89915 := rs (se 1 (by rfl) ⟨67436, by rfl⟩) R134873
theorem R188219 : Reach 188219 := rs (se 1 (by rfl) ⟨141164, by rfl⟩) R282329
theorem R253783 : Reach 253783 := rs (se 1 (by rfl) ⟨190337, by rfl⟩) R380675
theorem R89991 : Reach 89991 := rs (se 1 (by rfl) ⟨67493, by rfl⟩) R134987
theorem R89999 : Reach 89999 := rs (se 1 (by rfl) ⟨67499, by rfl⟩) R134999
theorem R90043 : Reach 90043 := rs (se 1 (by rfl) ⟨67532, by rfl⟩) R135065
theorem R90119 : Reach 90119 := rs (se 1 (by rfl) ⟨67589, by rfl⟩) R135179
theorem R90127 : Reach 90127 := rs (se 1 (by rfl) ⟨67595, by rfl⟩) R135191
theorem R254011 : Reach 254011 := rs (se 1 (by rfl) ⟨190508, by rfl⟩) R381017
theorem R90171 : Reach 90171 := rs (se 1 (by rfl) ⟨67628, by rfl⟩) R135257
theorem R122953 : Reach 122953 := rs (se 2 (by rfl) ⟨46107, by rfl⟩) R92215
theorem R90247 : Reach 90247 := rs (se 1 (by rfl) ⟨67685, by rfl⟩) R135371
theorem R90255 : Reach 90255 := rs (se 1 (by rfl) ⟨67691, by rfl⟩) R135383
theorem R254137 : Reach 254137 := rs (se 2 (by rfl) ⟨95301, by rfl⟩) R190603
theorem R90299 : Reach 90299 := rs (se 1 (by rfl) ⟨67724, by rfl⟩) R135449
theorem R90375 : Reach 90375 := rs (se 1 (by rfl) ⟨67781, by rfl⟩) R135563
theorem R90383 : Reach 90383 := rs (se 1 (by rfl) ⟨67787, by rfl⟩) R135575
theorem R90427 : Reach 90427 := rs (se 1 (by rfl) ⟨67820, by rfl⟩) R135641
theorem R221555 : Reach 221555 := rs (se 1 (by rfl) ⟨166166, by rfl⟩) R332333
theorem R221575 : Reach 221575 := rs (se 1 (by rfl) ⟨166181, by rfl⟩) R332363
theorem R90503 : Reach 90503 := rs (se 1 (by rfl) ⟨67877, by rfl⟩) R135755
theorem R90511 : Reach 90511 := rs (se 1 (by rfl) ⟨67883, by rfl⟩) R135767
theorem R90555 : Reach 90555 := rs (se 1 (by rfl) ⟨67916, by rfl⟩) R135833
theorem R90631 : Reach 90631 := rs (se 1 (by rfl) ⟨67973, by rfl⟩) R135947
theorem R90639 : Reach 90639 := rs (se 1 (by rfl) ⟨67979, by rfl⟩) R135959
theorem R483869 : Reach 483869 := rs (se 3 (by rfl) ⟨90725, by rfl⟩) R181451
theorem R582187 : Reach 582187 := rs (se 1 (by rfl) ⟨436640, by rfl⟩) R873281
theorem R90683 : Reach 90683 := rs (se 1 (by rfl) ⟨68012, by rfl⟩) R136025
theorem R221831 : Reach 221831 := rs (se 1 (by rfl) ⟨166373, by rfl⟩) R332747
theorem R90759 : Reach 90759 := rs (se 1 (by rfl) ⟨68069, by rfl⟩) R136139
theorem R90767 : Reach 90767 := rs (se 1 (by rfl) ⟨68075, by rfl⟩) R136151
theorem R221849 : Reach 221849 := rs (se 2 (by rfl) ⟨83193, by rfl⟩) R166387
theorem R90811 : Reach 90811 := rs (se 1 (by rfl) ⟨68108, by rfl⟩) R136217
theorem R90887 : Reach 90887 := rs (se 1 (by rfl) ⟨68165, by rfl⟩) R136331
theorem R90895 : Reach 90895 := rs (se 1 (by rfl) ⟨68171, by rfl⟩) R136343
theorem R222011 : Reach 222011 := rs (se 1 (by rfl) ⟨166508, by rfl⟩) R333017
theorem R90939 : Reach 90939 := rs (se 1 (by rfl) ⟨68204, by rfl⟩) R136409
theorem R91015 : Reach 91015 := rs (se 1 (by rfl) ⟨68261, by rfl⟩) R136523
theorem R91023 : Reach 91023 := rs (se 1 (by rfl) ⟨68267, by rfl⟩) R136535
theorem R91067 : Reach 91067 := rs (se 1 (by rfl) ⟨68300, by rfl⟩) R136601
theorem R222223 : Reach 222223 := rs (se 1 (by rfl) ⟨166667, by rfl⟩) R333335
theorem R222497 : Reach 222497 := rs (se 2 (by rfl) ⟨83436, by rfl⟩) R166873
theorem R91535 : Reach 91535 := rs (se 1 (by rfl) ⟨68651, by rfl⟩) R137303
theorem R517751 : Reach 517751 := rs (se 1 (by rfl) ⟨388313, by rfl⟩) R776627
theorem R386963 : Reach 386963 := rs (se 1 (by rfl) ⟨290222, by rfl⟩) R580445
theorem R419843 : Reach 419843 := rs (se 1 (by rfl) ⟨314882, by rfl⟩) R629765
theorem R256061 : Reach 256061 := rs (se 3 (by rfl) ⟨48011, by rfl⟩) R96023
theorem R223499 : Reach 223499 := rs (se 1 (by rfl) ⟨167624, by rfl⟩) R335249
theorem R616889 : Reach 616889 := rs (se 2 (by rfl) ⟨231333, by rfl⟩) R462667
theorem R1010393 : Reach 1010393 := rs (se 2 (by rfl) ⟨378897, by rfl⟩) R757795
theorem R289595 : Reach 289595 := rs (se 1 (by rfl) ⟨217196, by rfl⟩) R434393
theorem R224147 : Reach 224147 := rs (se 1 (by rfl) ⟨168110, by rfl⟩) R336221
theorem R257053 : Reach 257053 := rs (se 3 (by rfl) ⟨48197, by rfl⟩) R96395
theorem R158753 : Reach 158753 := rs (se 2 (by rfl) ⟨59532, by rfl⟩) R119065
theorem R191531 : Reach 191531 := rs (se 1 (by rfl) ⟨143648, by rfl⟩) R287297
theorem R224441 : Reach 224441 := rs (se 2 (by rfl) ⟨84165, by rfl⟩) R168331
theorem R159275 : Reach 159275 := rs (se 1 (by rfl) ⟨119456, by rfl⟩) R238913
theorem R225139 : Reach 225139 := rs (se 1 (by rfl) ⟨168854, by rfl⟩) R337709
theorem R421841 : Reach 421841 := rs (se 2 (by rfl) ⟨158190, by rfl⟩) R316381
theorem R225281 : Reach 225281 := rs (se 2 (by rfl) ⟨84480, by rfl⟩) R168961
theorem R455057 : Reach 455057 := rs (se 2 (by rfl) ⟨170646, by rfl⟩) R341293
theorem R225737 : Reach 225737 := rs (se 2 (by rfl) ⟨84651, by rfl⟩) R169303
theorem R127433 : Reach 127433 := rs (se 2 (by rfl) ⟨47787, by rfl⟩) R95575
theorem R455341 : Reach 455341 := rs (se 3 (by rfl) ⟨85376, by rfl⟩) R170753
theorem R684773 : Reach 684773 := rs (se 4 (by rfl) ⟨64197, by rfl⟩) R128395
theorem R848677 : Reach 848677 := rs (se 4 (by rfl) ⟨79563, by rfl⟩) R159127
theorem R226091 : Reach 226091 := rs (se 1 (by rfl) ⟨169568, by rfl⟩) R339137
theorem R259001 : Reach 259001 := rs (se 2 (by rfl) ⟨97125, by rfl⟩) R194251
theorem R128299 : Reach 128299 := rs (se 1 (by rfl) ⟨96224, by rfl⟩) R192449
theorem R980369 : Reach 980369 := rs (se 2 (by rfl) ⟨367638, by rfl⟩) R735277
theorem R849527 : Reach 849527 := rs (se 1 (by rfl) ⟨637145, by rfl⟩) R1274291
theorem R194233 : Reach 194233 := rs (se 2 (by rfl) ⟨72837, by rfl⟩) R145675
theorem R227083 : Reach 227083 := rs (se 1 (by rfl) ⟨170312, by rfl⟩) R340625
theorem R227225 : Reach 227225 := rs (se 2 (by rfl) ⟨85209, by rfl⟩) R170419
theorem R2553869 : Reach 2553869 := rs (se 3 (by rfl) ⟨478850, by rfl⟩) R957701
theorem R194575 : Reach 194575 := rs (se 1 (by rfl) ⟨145931, by rfl⟩) R291863
theorem R227387 : Reach 227387 := rs (se 1 (by rfl) ⟨170540, by rfl⟩) R341081
theorem R292925 : Reach 292925 := rs (se 3 (by rfl) ⟨54923, by rfl⟩) R109847
theorem R981229 : Reach 981229 := rs (se 3 (by rfl) ⟨183980, by rfl⟩) R367961
theorem R784673 : Reach 784673 := rs (se 2 (by rfl) ⟨294252, by rfl⟩) R588505
theorem R162091 : Reach 162091 := rs (se 1 (by rfl) ⟨121568, by rfl⟩) R243137
theorem R522611 : Reach 522611 := rs (se 1 (by rfl) ⟨391958, by rfl⟩) R783917
theorem R227731 : Reach 227731 := rs (se 1 (by rfl) ⟨170798, by rfl⟩) R341597
theorem R457163 : Reach 457163 := rs (se 1 (by rfl) ⟨342872, by rfl⟩) R685745
theorem R227873 : Reach 227873 := rs (se 2 (by rfl) ⟨85452, by rfl⟩) R170905
theorem R129595 : Reach 129595 := rs (se 1 (by rfl) ⟨97196, by rfl⟩) R194393
theorem R1440449 : Reach 1440449 := rs (se 2 (by rfl) ⟨540168, by rfl⟩) R1080337
theorem R457487 : Reach 457487 := rs (se 1 (by rfl) ⟨343115, by rfl⟩) R686231
theorem R293665 : Reach 293665 := rs (se 2 (by rfl) ⟨110124, by rfl⟩) R220249
theorem R391969 : Reach 391969 := rs (se 2 (by rfl) ⟨146988, by rfl⟩) R293977
theorem R2063141 : Reach 2063141 := rs (se 4 (by rfl) ⟨193419, by rfl⟩) R386839
theorem R5078213 : Reach 5078213 := rs (se 4 (by rfl) ⟨476082, by rfl⟩) R952165
theorem R720161 : Reach 720161 := rs (se 2 (by rfl) ⟨270060, by rfl⟩) R540121
theorem R490961 : Reach 490961 := rs (se 2 (by rfl) ⟨184110, by rfl⟩) R368221
theorem R228865 : Reach 228865 := rs (se 2 (by rfl) ⟨85824, by rfl⟩) R171649
theorem R327179 : Reach 327179 := rs (se 1 (by rfl) ⟨245384, by rfl⟩) R490769
theorem R294461 : Reach 294461 := rs (se 3 (by rfl) ⟨55211, by rfl⟩) R110423
theorem R2719331 : Reach 2719331 := rs (se 1 (by rfl) ⟨2039498, by rfl⟩) R4078997
theorem R130703 : Reach 130703 := rs (se 1 (by rfl) ⟨98027, by rfl⟩) R196055
theorem R163475 : Reach 163475 := rs (se 1 (by rfl) ⟨122606, by rfl⟩) R245213
theorem R130745 : Reach 130745 := rs (se 2 (by rfl) ⟨49029, by rfl⟩) R98059
theorem R425729 : Reach 425729 := rs (se 2 (by rfl) ⟨159648, by rfl⟩) R319297
theorem R130823 : Reach 130823 := rs (se 1 (by rfl) ⟨98117, by rfl⟩) R196235
theorem R130859 : Reach 130859 := rs (se 1 (by rfl) ⟨98144, by rfl⟩) R196289
theorem R130889 : Reach 130889 := rs (se 2 (by rfl) ⟨49083, by rfl⟩) R98167
theorem R196487 : Reach 196487 := rs (se 1 (by rfl) ⟨147365, by rfl⟩) R294731
theorem R131003 : Reach 131003 := rs (se 1 (by rfl) ⟨98252, by rfl⟩) R196505
theorem R131063 : Reach 131063 := rs (se 1 (by rfl) ⟨98297, by rfl⟩) R196595
theorem R131081 : Reach 131081 := rs (se 2 (by rfl) ⟨49155, by rfl⟩) R98311
theorem R131111 : Reach 131111 := rs (se 1 (by rfl) ⟨98333, by rfl⟩) R196667
theorem R98383 : Reach 98383 := rs (se 1 (by rfl) ⟨73787, by rfl⟩) R147575
theorem R163937 : Reach 163937 := rs (se 2 (by rfl) ⟨61476, by rfl⟩) R122953
theorem R131195 : Reach 131195 := rs (se 1 (by rfl) ⟨98396, by rfl⟩) R196793
theorem R1441955 : Reach 1441955 := rs (se 1 (by rfl) ⟨1081466, by rfl⟩) R2162933
theorem R131321 : Reach 131321 := rs (se 2 (by rfl) ⟨49245, by rfl⟩) R98491
theorem R131423 : Reach 131423 := rs (se 1 (by rfl) ⟨98567, by rfl⟩) R197135
theorem R131435 : Reach 131435 := rs (se 1 (by rfl) ⟨98576, by rfl⟩) R197153
theorem R98779 : Reach 98779 := rs (se 1 (by rfl) ⟨74084, by rfl⟩) R148169
theorem R295433 : Reach 295433 := rs (se 2 (by rfl) ⟨110787, by rfl⟩) R221575
theorem R1180169 : Reach 1180169 := rs (se 2 (by rfl) ⟨442563, by rfl⟩) R885127
theorem R131663 : Reach 131663 := rs (se 1 (by rfl) ⟨98747, by rfl⟩) R197495
theorem R197243 : Reach 197243 := rs (se 1 (by rfl) ⟨147932, by rfl⟩) R295865
theorem R131783 : Reach 131783 := rs (se 1 (by rfl) ⟨98837, by rfl⟩) R197675
theorem R197369 : Reach 197369 := rs (se 2 (by rfl) ⟨74013, by rfl⟩) R148027
theorem R459593 : Reach 459593 := rs (se 2 (by rfl) ⟨172347, by rfl⟩) R344695
theorem R131945 : Reach 131945 := rs (se 2 (by rfl) ⟨49479, by rfl⟩) R98959
theorem R99247 : Reach 99247 := rs (se 1 (by rfl) ⟨74435, by rfl⟩) R148871
theorem R132023 : Reach 132023 := rs (se 1 (by rfl) ⟨99017, by rfl⟩) R198035
theorem R132059 : Reach 132059 := rs (se 1 (by rfl) ⟨99044, by rfl⟩) R198089
theorem R197639 : Reach 197639 := rs (se 1 (by rfl) ⟨148229, by rfl⟩) R296459
theorem R590915 : Reach 590915 := rs (se 1 (by rfl) ⟨443186, by rfl⟩) R886373
theorem R197711 : Reach 197711 := rs (se 1 (by rfl) ⟨148283, by rfl⟩) R296567
theorem R230647 : Reach 230647 := rs (se 1 (by rfl) ⟨172985, by rfl⟩) R345971
theorem R99679 : Reach 99679 := rs (se 1 (by rfl) ⟨74759, by rfl⟩) R149519
theorem R296297 : Reach 296297 := rs (se 2 (by rfl) ⟨111111, by rfl⟩) R222223
theorem R132527 : Reach 132527 := rs (se 1 (by rfl) ⟨99395, by rfl⟩) R198791
theorem R198107 : Reach 198107 := rs (se 1 (by rfl) ⟨148580, by rfl⟩) R297161
theorem R132617 : Reach 132617 := rs (se 2 (by rfl) ⟨49731, by rfl⟩) R99463
theorem R165415 : Reach 165415 := rs (se 1 (by rfl) ⟨124061, by rfl⟩) R248123
theorem R132647 : Reach 132647 := rs (se 1 (by rfl) ⟨99485, by rfl⟩) R198971
theorem R132731 : Reach 132731 := rs (se 1 (by rfl) ⟨99548, by rfl⟩) R199097
theorem R100039 : Reach 100039 := rs (se 1 (by rfl) ⟨75029, by rfl⟩) R150059
theorem R132857 : Reach 132857 := rs (se 2 (by rfl) ⟨49821, by rfl⟩) R99643
theorem R132959 : Reach 132959 := rs (se 1 (by rfl) ⟨99719, by rfl⟩) R199439
theorem R132971 : Reach 132971 := rs (se 1 (by rfl) ⟨99728, by rfl⟩) R199457
theorem R198575 : Reach 198575 := rs (se 1 (by rfl) ⟨148931, by rfl⟩) R297863
theorem R296891 : Reach 296891 := rs (se 1 (by rfl) ⟨222668, by rfl⟩) R445337
theorem R854023 : Reach 854023 := rs (se 1 (by rfl) ⟨640517, by rfl⟩) R1281035
theorem R133199 : Reach 133199 := rs (se 1 (by rfl) ⟨99899, by rfl⟩) R199799
theorem R460889 : Reach 460889 := rs (se 2 (by rfl) ⟨172833, by rfl⟩) R345667
theorem R198827 : Reach 198827 := rs (se 1 (by rfl) ⟨149120, by rfl⟩) R298241
theorem R133319 : Reach 133319 := rs (se 1 (by rfl) ⟨99989, by rfl⟩) R199979
theorem R133481 : Reach 133481 := rs (se 2 (by rfl) ⟨50055, by rfl⟩) R100111
theorem R133559 : Reach 133559 := rs (se 1 (by rfl) ⟨100169, by rfl⟩) R200339
theorem R133595 : Reach 133595 := rs (se 1 (by rfl) ⟨100196, by rfl⟩) R200393
theorem R2296349 : Reach 2296349 := rs (se 3 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R100903 : Reach 100903 := rs (se 1 (by rfl) ⟨75677, by rfl⟩) R151355
theorem R199367 : Reach 199367 := rs (se 1 (by rfl) ⟨149525, by rfl⟩) R299051
theorem R691091 : Reach 691091 := rs (se 1 (by rfl) ⟨518318, by rfl⟩) R1036637
theorem R134063 : Reach 134063 := rs (se 1 (by rfl) ⟨100547, by rfl⟩) R201095
theorem R134153 : Reach 134153 := rs (se 2 (by rfl) ⟨50307, by rfl⟩) R100615
theorem R134183 : Reach 134183 := rs (se 1 (by rfl) ⟨100637, by rfl⟩) R201275
theorem R134267 : Reach 134267 := rs (se 1 (by rfl) ⟨100700, by rfl⟩) R201401
theorem R330905 : Reach 330905 := rs (se 2 (by rfl) ⟨124089, by rfl⟩) R248179
theorem R167123 : Reach 167123 := rs (se 1 (by rfl) ⟨125342, by rfl⟩) R250685
theorem R265463 : Reach 265463 := rs (se 1 (by rfl) ⟨199097, by rfl⟩) R398195
theorem R462071 : Reach 462071 := rs (se 1 (by rfl) ⟨346553, by rfl⟩) R693107
theorem R134393 : Reach 134393 := rs (se 2 (by rfl) ⟨50397, by rfl⟩) R100795
theorem R134495 : Reach 134495 := rs (se 1 (by rfl) ⟨100871, by rfl⟩) R201743
theorem R167275 : Reach 167275 := rs (se 1 (by rfl) ⟨125456, by rfl⟩) R250913
theorem R134507 : Reach 134507 := rs (se 1 (by rfl) ⟨100880, by rfl⟩) R201761
theorem R200231 : Reach 200231 := rs (se 1 (by rfl) ⟨150173, by rfl⟩) R300347
theorem R167503 : Reach 167503 := rs (se 1 (by rfl) ⟨125627, by rfl⟩) R251255
theorem R134735 : Reach 134735 := rs (se 1 (by rfl) ⟨101051, by rfl⟩) R202103
theorem R331361 : Reach 331361 := rs (se 2 (by rfl) ⟨124260, by rfl⟩) R248521
theorem R298619 : Reach 298619 := rs (se 1 (by rfl) ⟨223964, by rfl⟩) R447929
theorem R134855 : Reach 134855 := rs (se 1 (by rfl) ⟨101141, by rfl⟩) R202283
theorem R298781 : Reach 298781 := rs (se 3 (by rfl) ⟨56021, by rfl⟩) R112043
theorem R1314593 : Reach 1314593 := rs (se 2 (by rfl) ⟨492972, by rfl⟩) R985945
theorem R135017 : Reach 135017 := rs (se 2 (by rfl) ⟨50631, by rfl⟩) R101263
theorem R200555 : Reach 200555 := rs (se 1 (by rfl) ⟨150416, by rfl⟩) R300833
theorem R200609 : Reach 200609 := rs (se 2 (by rfl) ⟨75228, by rfl⟩) R150457
theorem R135095 : Reach 135095 := rs (se 1 (by rfl) ⟨101321, by rfl⟩) R202643
theorem R135131 : Reach 135131 := rs (se 1 (by rfl) ⟨101348, by rfl⟩) R202697
theorem R200951 : Reach 200951 := rs (se 1 (by rfl) ⟨150713, by rfl⟩) R301427
theorem R135599 : Reach 135599 := rs (se 1 (by rfl) ⟨101699, by rfl⟩) R203399
theorem R299483 : Reach 299483 := rs (se 1 (by rfl) ⟨224612, by rfl⟩) R449225
theorem R135689 : Reach 135689 := rs (se 2 (by rfl) ⟨50883, by rfl⟩) R101767
theorem R135719 : Reach 135719 := rs (se 1 (by rfl) ⟨101789, by rfl⟩) R203579
theorem R135803 : Reach 135803 := rs (se 1 (by rfl) ⟨101852, by rfl⟩) R203705
theorem R496313 : Reach 496313 := rs (se 2 (by rfl) ⟨186117, by rfl⟩) R372235
theorem R135929 : Reach 135929 := rs (se 2 (by rfl) ⟨50973, by rfl⟩) R101947
theorem R201545 : Reach 201545 := rs (se 2 (by rfl) ⟨75579, by rfl⟩) R151159
theorem R136031 : Reach 136031 := rs (se 1 (by rfl) ⟨102023, by rfl⟩) R204047
theorem R136043 : Reach 136043 := rs (se 1 (by rfl) ⟨102032, by rfl⟩) R204065
theorem R332819 : Reach 332819 := rs (se 1 (by rfl) ⟨249614, by rfl⟩) R499229
theorem R136271 : Reach 136271 := rs (se 1 (by rfl) ⟨102203, by rfl⟩) R204407
theorem R300185 : Reach 300185 := rs (se 2 (by rfl) ⟨112569, by rfl⟩) R225139
theorem R136391 : Reach 136391 := rs (se 1 (by rfl) ⟨102293, by rfl⟩) R204587
theorem R136553 : Reach 136553 := rs (se 2 (by rfl) ⟨51207, by rfl⟩) R102415
theorem R136631 : Reach 136631 := rs (se 1 (by rfl) ⟨102473, by rfl⟩) R204947
theorem R136667 : Reach 136667 := rs (se 1 (by rfl) ⟨102500, by rfl⟩) R205001
theorem R202337 : Reach 202337 := rs (se 2 (by rfl) ⟨75876, by rfl⟩) R151753
theorem R202679 : Reach 202679 := rs (se 1 (by rfl) ⟨152009, by rfl⟩) R304019
theorem R202999 : Reach 202999 := rs (se 1 (by rfl) ⟨152249, by rfl⟩) R304499
theorem R301373 : Reach 301373 := rs (se 3 (by rfl) ⟨56507, by rfl⟩) R113015
theorem R203273 : Reach 203273 := rs (se 2 (by rfl) ⟨76227, by rfl⟩) R152455
theorem R334475 : Reach 334475 := rs (se 1 (by rfl) ⟨250856, by rfl⟩) R501713
theorem R203615 : Reach 203615 := rs (se 1 (by rfl) ⟨152711, by rfl⟩) R305423
theorem R662417 : Reach 662417 := rs (se 2 (by rfl) ⟨248406, by rfl⟩) R496813
theorem R203795 : Reach 203795 := rs (se 1 (by rfl) ⟨152846, by rfl⟩) R305693
theorem R171065 : Reach 171065 := rs (se 2 (by rfl) ⟨64149, by rfl⟩) R128299
theorem R302237 : Reach 302237 := rs (se 3 (by rfl) ⟨56669, by rfl⟩) R113339
theorem R204137 : Reach 204137 := rs (se 2 (by rfl) ⟨76551, by rfl⟩) R153103
theorem R105835 : Reach 105835 := rs (se 1 (by rfl) ⟨79376, by rfl⟩) R158753
theorem R466319 : Reach 466319 := rs (se 1 (by rfl) ⟨349739, by rfl⟩) R699479
theorem R335483 : Reach 335483 := rs (se 1 (by rfl) ⟨251612, by rfl⟩) R503225
theorem R532091 : Reach 532091 := rs (se 1 (by rfl) ⟨399068, by rfl⟩) R798137
theorem R269963 : Reach 269963 := rs (se 1 (by rfl) ⟨202472, by rfl⟩) R404945
theorem R302777 : Reach 302777 := rs (se 2 (by rfl) ⟨113541, by rfl⟩) R227083
theorem R106183 : Reach 106183 := rs (se 1 (by rfl) ⟨79637, by rfl⟩) R159275
theorem R335735 : Reach 335735 := rs (se 1 (by rfl) ⟨251801, by rfl⟩) R503603
theorem R204731 : Reach 204731 := rs (se 1 (by rfl) ⟨153548, by rfl⟩) R307097
theorem R204857 : Reach 204857 := rs (se 2 (by rfl) ⟨76821, by rfl⟩) R153643
theorem R303371 : Reach 303371 := rs (se 1 (by rfl) ⟨227528, by rfl⟩) R455057
theorem R303641 : Reach 303641 := rs (se 2 (by rfl) ⟨113865, by rfl⟩) R227731
theorem R172667 : Reach 172667 := rs (se 1 (by rfl) ⟨129500, by rfl⟩) R259001
theorem R172793 : Reach 172793 := rs (se 2 (by rfl) ⟨64797, by rfl⟩) R129595
theorem R336707 : Reach 336707 := rs (se 1 (by rfl) ⟨252530, by rfl⟩) R505061
theorem R566351 : Reach 566351 := rs (se 1 (by rfl) ⟨424763, by rfl⟩) R849527
theorem R205903 : Reach 205903 := rs (se 1 (by rfl) ⟨154427, by rfl⟩) R308855
theorem R664847 : Reach 664847 := rs (se 1 (by rfl) ⟨498635, by rfl⟩) R997271
theorem R304775 : Reach 304775 := rs (se 1 (by rfl) ⟨228581, by rfl⟩) R457163
theorem R304829 : Reach 304829 := rs (se 3 (by rfl) ⟨57155, by rfl⟩) R114311
theorem R960299 : Reach 960299 := rs (se 1 (by rfl) ⟨720224, by rfl⟩) R1440449
theorem R304991 : Reach 304991 := rs (se 1 (by rfl) ⟨228743, by rfl⟩) R457487
theorem R305153 : Reach 305153 := rs (se 2 (by rfl) ⟨114432, by rfl⟩) R228865
theorem R3385475 : Reach 3385475 := rs (se 1 (by rfl) ⟨2539106, by rfl⟩) R5078213
theorem R502145 : Reach 502145 := rs (se 2 (by rfl) ⟨188304, by rfl⟩) R376609
theorem R1812887 : Reach 1812887 := rs (se 1 (by rfl) ⟨1359665, by rfl⟩) R2719331
theorem R108983 : Reach 108983 := rs (se 1 (by rfl) ⟨81737, by rfl⟩) R163475
theorem R338377 : Reach 338377 := rs (se 2 (by rfl) ⟨126891, by rfl⟩) R253783
theorem R338681 : Reach 338681 := rs (se 2 (by rfl) ⟨127005, by rfl⟩) R254011
theorem R305963 : Reach 305963 := rs (se 1 (by rfl) ⟨229472, by rfl⟩) R458945
theorem R1551251 : Reach 1551251 := rs (se 1 (by rfl) ⟨1163438, by rfl⟩) R2326877
theorem R338849 : Reach 338849 := rs (se 2 (by rfl) ⟨127068, by rfl⟩) R254137
theorem R338863 : Reach 338863 := rs (se 1 (by rfl) ⟨254147, by rfl⟩) R508295
theorem R306233 : Reach 306233 := rs (se 2 (by rfl) ⟨114837, by rfl⟩) R229675
theorem R240887 : Reach 240887 := rs (se 1 (by rfl) ⟨180665, by rfl⟩) R361331
theorem R339287 : Reach 339287 := rs (se 1 (by rfl) ⟨254465, by rfl⟩) R508931
theorem R142697 : Reach 142697 := rs (se 2 (by rfl) ⟨53511, by rfl⟩) R107023
theorem R306557 : Reach 306557 := rs (se 3 (by rfl) ⟨57479, by rfl⟩) R114959
theorem R306827 : Reach 306827 := rs (se 1 (by rfl) ⟨230120, by rfl⟩) R460241
theorem R339821 : Reach 339821 := rs (se 3 (by rfl) ⟨63716, by rfl⟩) R127433
theorem R667763 : Reach 667763 := rs (se 1 (by rfl) ⟨500822, by rfl⟩) R1001645
theorem R340139 : Reach 340139 := rs (se 1 (by rfl) ⟨255104, by rfl⟩) R510209
theorem R143689 : Reach 143689 := rs (se 2 (by rfl) ⟨53883, by rfl⟩) R107767
theorem R1552769 : Reach 1552769 := rs (se 2 (by rfl) ⟨582288, by rfl⟩) R1164577
theorem R1290775 : Reach 1290775 := rs (se 1 (by rfl) ⟨968081, by rfl⟩) R1936163
theorem R1717037 : Reach 1717037 := rs (se 3 (by rfl) ⟨321944, by rfl⟩) R643889
theorem R1685357 : Reach 1685357 := rs (se 3 (by rfl) ⟨316004, by rfl⟩) R632009
theorem R210863 : Reach 210863 := rs (se 1 (by rfl) ⟨158147, by rfl⟩) R316295
theorem R637085 : Reach 637085 := rs (se 3 (by rfl) ⟨119453, by rfl⟩) R238907
theorem R244097 : Reach 244097 := rs (se 2 (by rfl) ⟨91536, by rfl⟩) R183073
theorem R113071 : Reach 113071 := rs (se 1 (by rfl) ⟨84803, by rfl⟩) R169607
theorem R342737 : Reach 342737 := rs (se 2 (by rfl) ⟨128526, by rfl⟩) R257053
theorem R342967 : Reach 342967 := rs (se 1 (by rfl) ⟨257225, by rfl⟩) R514451
theorem R343055 : Reach 343055 := rs (se 1 (by rfl) ⟨257291, by rfl⟩) R514583
theorem R1424557 : Reach 1424557 := rs (se 3 (by rfl) ⟨267104, by rfl⟩) R534209
theorem R1260791 : Reach 1260791 := rs (se 1 (by rfl) ⟨945593, by rfl⟩) R1891187
theorem R441773 : Reach 441773 := rs (se 3 (by rfl) ⟨82832, by rfl⟩) R165665
theorem R114139 : Reach 114139 := rs (se 1 (by rfl) ⟨85604, by rfl⟩) R171209
theorem R147143 : Reach 147143 := rs (se 1 (by rfl) ⟨110357, by rfl⟩) R220715
theorem R179911 : Reach 179911 := rs (se 1 (by rfl) ⟨134933, by rfl⟩) R269867
theorem R376643 : Reach 376643 := rs (se 1 (by rfl) ⟨282482, by rfl⟩) R564965
theorem R147305 : Reach 147305 := rs (se 2 (by rfl) ⟨55239, by rfl⟩) R110479
theorem R147703 : Reach 147703 := rs (se 1 (by rfl) ⟨110777, by rfl⟩) R221555
theorem R147887 : Reach 147887 := rs (se 1 (by rfl) ⟨110915, by rfl⟩) R221831
theorem R147899 : Reach 147899 := rs (se 1 (by rfl) ⟨110924, by rfl⟩) R221849
theorem R1425923 : Reach 1425923 := rs (se 1 (by rfl) ⟨1069442, by rfl⟩) R2138885
theorem R148007 : Reach 148007 := rs (se 1 (by rfl) ⟨111005, by rfl⟩) R222011
theorem R148297 : Reach 148297 := rs (se 2 (by rfl) ⟨55611, by rfl⟩) R111223
theorem R148331 : Reach 148331 := rs (se 1 (by rfl) ⟨111248, by rfl⟩) R222497
theorem R607121 : Reach 607121 := rs (se 2 (by rfl) ⟨227670, by rfl⟩) R455341
theorem R443393 : Reach 443393 := rs (se 2 (by rfl) ⟨166272, by rfl⟩) R332545
theorem R1131569 : Reach 1131569 := rs (se 2 (by rfl) ⟨424338, by rfl⟩) R848677
theorem R345167 : Reach 345167 := rs (se 1 (by rfl) ⟨258875, by rfl⟩) R517751
theorem R771191 : Reach 771191 := rs (se 1 (by rfl) ⟨578393, by rfl⟩) R1156787
theorem R148729 : Reach 148729 := rs (se 2 (by rfl) ⟨55773, by rfl⟩) R111547
theorem R279895 : Reach 279895 := rs (se 1 (by rfl) ⟨209921, by rfl⟩) R419843
theorem R148999 : Reach 148999 := rs (se 1 (by rfl) ⟨111749, by rfl⟩) R223499
theorem R280073 : Reach 280073 := rs (se 2 (by rfl) ⟨105027, by rfl⟩) R210055
theorem R411259 : Reach 411259 := rs (se 1 (by rfl) ⟨308444, by rfl⟩) R616889
theorem R378557 : Reach 378557 := rs (se 3 (by rfl) ⟨70979, by rfl⟩) R141959
theorem R444203 : Reach 444203 := rs (se 1 (by rfl) ⟨333152, by rfl⟩) R666305
theorem R673595 : Reach 673595 := rs (se 1 (by rfl) ⟨505196, by rfl⟩) R1010393
theorem R182159 : Reach 182159 := rs (se 1 (by rfl) ⟨136619, by rfl⟩) R273239
theorem R149431 : Reach 149431 := rs (se 1 (by rfl) ⟨112073, by rfl⟩) R224147
theorem R149627 : Reach 149627 := rs (se 1 (by rfl) ⟨112220, by rfl⟩) R224441
theorem R772253 : Reach 772253 := rs (se 3 (by rfl) ⟨144797, by rfl⟩) R289595
theorem R379241 : Reach 379241 := rs (se 2 (by rfl) ⟨142215, by rfl⟩) R284431
theorem R150025 : Reach 150025 := rs (se 2 (by rfl) ⟨56259, by rfl⟩) R112519
theorem R281227 : Reach 281227 := rs (se 1 (by rfl) ⟨210920, by rfl⟩) R421841
theorem R150187 : Reach 150187 := rs (se 1 (by rfl) ⟨112640, by rfl⟩) R225281
theorem R510749 : Reach 510749 := rs (se 3 (by rfl) ⟨95765, by rfl⟩) R191531
theorem R150491 : Reach 150491 := rs (se 1 (by rfl) ⟨112868, by rfl⟩) R225737
theorem R216121 : Reach 216121 := rs (se 2 (by rfl) ⟨81045, by rfl⟩) R162091
theorem R150727 : Reach 150727 := rs (se 1 (by rfl) ⟨113045, by rfl⟩) R226091
theorem R150889 : Reach 150889 := rs (se 2 (by rfl) ⟨56583, by rfl⟩) R113167
theorem R970157 : Reach 970157 := rs (se 3 (by rfl) ⟨181904, by rfl⟩) R363809
theorem R151483 : Reach 151483 := rs (se 1 (by rfl) ⟨113612, by rfl⟩) R227225
theorem R446471 : Reach 446471 := rs (se 1 (by rfl) ⟨334853, by rfl⟩) R669707
theorem R872477 : Reach 872477 := rs (se 3 (by rfl) ⟨163589, by rfl⟩) R327179
theorem R151591 : Reach 151591 := rs (se 1 (by rfl) ⟨113693, by rfl⟩) R227387
theorem R348407 : Reach 348407 := rs (se 1 (by rfl) ⟨261305, by rfl⟩) R522611
theorem R151915 : Reach 151915 := rs (se 1 (by rfl) ⟨113936, by rfl⟩) R227873
theorem R446957 : Reach 446957 := rs (se 3 (by rfl) ⟨83804, by rfl⟩) R167609
theorem R480107 : Reach 480107 := rs (se 1 (by rfl) ⟨360080, by rfl⟩) R720161
theorem R87135 : Reach 87135 := rs (se 1 (by rfl) ⟨65351, by rfl⟩) R130703
theorem R87163 : Reach 87163 := rs (se 1 (by rfl) ⟨65372, by rfl⟩) R130745
theorem R283819 : Reach 283819 := rs (se 1 (by rfl) ⟨212864, by rfl⟩) R425729
theorem R87215 : Reach 87215 := rs (se 1 (by rfl) ⟨65411, by rfl⟩) R130823
theorem R87239 : Reach 87239 := rs (se 1 (by rfl) ⟨65429, by rfl⟩) R130859
theorem R87259 : Reach 87259 := rs (se 1 (by rfl) ⟨65444, by rfl⟩) R130889
theorem R447767 : Reach 447767 := rs (se 1 (by rfl) ⟨335825, by rfl⟩) R671651
theorem R87335 : Reach 87335 := rs (se 1 (by rfl) ⟨65501, by rfl⟩) R131003
theorem R87375 : Reach 87375 := rs (se 1 (by rfl) ⟨65531, by rfl⟩) R131063
theorem R87391 : Reach 87391 := rs (se 1 (by rfl) ⟨65543, by rfl⟩) R131087
theorem R87419 : Reach 87419 := rs (se 1 (by rfl) ⟨65564, by rfl⟩) R131129
theorem R152975 : Reach 152975 := rs (se 1 (by rfl) ⟨114731, by rfl⟩) R229463
theorem R87471 : Reach 87471 := rs (se 1 (by rfl) ⟨65603, by rfl⟩) R131207
theorem R87495 : Reach 87495 := rs (se 1 (by rfl) ⟨65621, by rfl⟩) R131243
theorem R87515 : Reach 87515 := rs (se 1 (by rfl) ⟨65636, by rfl⟩) R131273
theorem R284123 : Reach 284123 := rs (se 1 (by rfl) ⟨213092, by rfl⟩) R426185
theorem R26891747 : Reach 26891747 := rs (se 1 (by rfl) ⟨20168810, by rfl⟩) R40337621
theorem R218611 : Reach 218611 := rs (se 1 (by rfl) ⟨163958, by rfl⟩) R327917
theorem R87591 : Reach 87591 := rs (se 1 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R87631 : Reach 87631 := rs (se 1 (by rfl) ⟨65723, by rfl⟩) R131447
theorem R87647 : Reach 87647 := rs (se 1 (by rfl) ⟨65735, by rfl⟩) R131471
theorem R87675 : Reach 87675 := rs (se 1 (by rfl) ⟨65756, by rfl⟩) R131513
theorem R153211 : Reach 153211 := rs (se 1 (by rfl) ⟨114908, by rfl⟩) R229817
theorem R644755 : Reach 644755 := rs (se 1 (by rfl) ⟨483566, by rfl⟩) R967133
theorem R87727 : Reach 87727 := rs (se 1 (by rfl) ⟨65795, by rfl⟩) R131591
theorem R87751 : Reach 87751 := rs (se 1 (by rfl) ⟨65813, by rfl⟩) R131627
theorem R87771 : Reach 87771 := rs (se 1 (by rfl) ⟨65828, by rfl⟩) R131657
theorem R710365 : Reach 710365 := rs (se 3 (by rfl) ⟨133193, by rfl⟩) R266387
theorem R87847 : Reach 87847 := rs (se 1 (by rfl) ⟨65885, by rfl⟩) R131771
theorem R87887 : Reach 87887 := rs (se 1 (by rfl) ⟨65915, by rfl⟩) R131831
theorem R87903 : Reach 87903 := rs (se 1 (by rfl) ⟨65927, by rfl⟩) R131855
theorem R87931 : Reach 87931 := rs (se 1 (by rfl) ⟨65948, by rfl⟩) R131897
theorem R87983 : Reach 87983 := rs (se 1 (by rfl) ⟨65987, by rfl⟩) R131975
theorem R88007 : Reach 88007 := rs (se 1 (by rfl) ⟨66005, by rfl⟩) R132011
theorem R88027 : Reach 88027 := rs (se 1 (by rfl) ⟨66020, by rfl⟩) R132041
theorem R284687 : Reach 284687 := rs (se 1 (by rfl) ⟨213515, by rfl⟩) R427031
theorem R88103 : Reach 88103 := rs (se 1 (by rfl) ⟨66077, by rfl⟩) R132155
theorem R776249 : Reach 776249 := rs (se 2 (by rfl) ⟨291093, by rfl⟩) R582187
theorem R88143 : Reach 88143 := rs (se 1 (by rfl) ⟨66107, by rfl⟩) R132215
theorem R677969 : Reach 677969 := rs (se 2 (by rfl) ⟨254238, by rfl⟩) R508477
theorem R88159 : Reach 88159 := rs (se 1 (by rfl) ⟨66119, by rfl⟩) R132239
theorem R88187 : Reach 88187 := rs (se 1 (by rfl) ⟨66140, by rfl⟩) R132281
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R88239 : Reach 88239 := rs (se 1 (by rfl) ⟨66179, by rfl⟩) R132359
theorem R88263 : Reach 88263 := rs (se 1 (by rfl) ⟨66197, by rfl⟩) R132395
theorem R88283 : Reach 88283 := rs (se 1 (by rfl) ⟨66212, by rfl⟩) R132425
theorem R88359 : Reach 88359 := rs (se 1 (by rfl) ⟨66269, by rfl⟩) R132539
theorem R88399 : Reach 88399 := rs (se 1 (by rfl) ⟨66299, by rfl⟩) R132599
theorem R88415 : Reach 88415 := rs (se 1 (by rfl) ⟨66311, by rfl⟩) R132623
theorem R88443 : Reach 88443 := rs (se 1 (by rfl) ⟨66332, by rfl⟩) R132665
theorem R88495 : Reach 88495 := rs (se 1 (by rfl) ⟨66371, by rfl⟩) R132743
theorem R88519 : Reach 88519 := rs (se 1 (by rfl) ⟨66389, by rfl⟩) R132779
theorem R88539 : Reach 88539 := rs (se 1 (by rfl) ⟨66404, by rfl⟩) R132809
theorem R88615 : Reach 88615 := rs (se 1 (by rfl) ⟨66461, by rfl⟩) R132923
theorem R88655 : Reach 88655 := rs (se 1 (by rfl) ⟨66491, by rfl⟩) R132983
theorem R88671 : Reach 88671 := rs (se 1 (by rfl) ⟨66503, by rfl⟩) R133007
theorem R88699 : Reach 88699 := rs (se 1 (by rfl) ⟨66524, by rfl⟩) R133049
theorem R88751 : Reach 88751 := rs (se 1 (by rfl) ⟨66563, by rfl⟩) R133127
theorem R88775 : Reach 88775 := rs (se 1 (by rfl) ⟨66581, by rfl⟩) R133163
theorem R88795 : Reach 88795 := rs (se 1 (by rfl) ⟨66596, by rfl⟩) R133193
theorem R1432349 : Reach 1432349 := rs (se 3 (by rfl) ⟨268565, by rfl⟩) R537131
theorem R88871 : Reach 88871 := rs (se 1 (by rfl) ⟨66653, by rfl⟩) R133307
theorem R88911 : Reach 88911 := rs (se 1 (by rfl) ⟨66683, by rfl⟩) R133367
theorem R88927 : Reach 88927 := rs (se 1 (by rfl) ⟨66695, by rfl⟩) R133391
theorem R449387 : Reach 449387 := rs (se 1 (by rfl) ⟨337040, by rfl⟩) R674081
theorem R88955 : Reach 88955 := rs (se 1 (by rfl) ⟨66716, by rfl⟩) R133433
theorem R89007 : Reach 89007 := rs (se 1 (by rfl) ⟨66755, by rfl⟩) R133511
theorem R89031 : Reach 89031 := rs (se 1 (by rfl) ⟨66773, by rfl⟩) R133547
theorem R89051 : Reach 89051 := rs (se 1 (by rfl) ⟨66788, by rfl⟩) R133577
theorem R89127 : Reach 89127 := rs (se 1 (by rfl) ⟨66845, by rfl⟩) R133691
theorem R89167 : Reach 89167 := rs (se 1 (by rfl) ⟨66875, by rfl⟩) R133751
theorem R154703 : Reach 154703 := rs (se 1 (by rfl) ⟨116027, by rfl⟩) R232055
theorem R89183 : Reach 89183 := rs (se 1 (by rfl) ⟨66887, by rfl⟩) R133775
theorem R89211 : Reach 89211 := rs (se 1 (by rfl) ⟨66908, by rfl⟩) R133817
theorem R89263 : Reach 89263 := rs (se 1 (by rfl) ⟨66947, by rfl⟩) R133895
theorem R515267 : Reach 515267 := rs (se 1 (by rfl) ⟨386450, by rfl⟩) R772901
theorem R89287 : Reach 89287 := rs (se 1 (by rfl) ⟨66965, by rfl⟩) R133931
theorem R89307 : Reach 89307 := rs (se 1 (by rfl) ⟨66980, by rfl⟩) R133961
theorem R285943 : Reach 285943 := rs (se 1 (by rfl) ⟨214457, by rfl⟩) R428915
theorem R89383 : Reach 89383 := rs (se 1 (by rfl) ⟨67037, by rfl⟩) R134075
theorem R89423 : Reach 89423 := rs (se 1 (by rfl) ⟨67067, by rfl⟩) R134135
theorem R89439 : Reach 89439 := rs (se 1 (by rfl) ⟨67079, by rfl⟩) R134159
theorem R89467 : Reach 89467 := rs (se 1 (by rfl) ⟨67100, by rfl⟩) R134201
theorem R89519 : Reach 89519 := rs (se 1 (by rfl) ⟨67139, by rfl⟩) R134279
theorem R89543 : Reach 89543 := rs (se 1 (by rfl) ⟨67157, by rfl⟩) R134315
theorem R89563 : Reach 89563 := rs (se 1 (by rfl) ⟨67172, by rfl⟩) R134345
theorem R744947 : Reach 744947 := rs (se 1 (by rfl) ⟨558710, by rfl⟩) R1117421
theorem R450035 : Reach 450035 := rs (se 1 (by rfl) ⟨337526, by rfl⟩) R675053
theorem R89639 : Reach 89639 := rs (se 1 (by rfl) ⟨67229, by rfl⟩) R134459
theorem R89679 : Reach 89679 := rs (se 1 (by rfl) ⟨67259, by rfl⟩) R134519
theorem R89695 : Reach 89695 := rs (se 1 (by rfl) ⟨67271, by rfl⟩) R134543
theorem R89723 : Reach 89723 := rs (se 1 (by rfl) ⟨67292, by rfl⟩) R134585
theorem R89775 : Reach 89775 := rs (se 1 (by rfl) ⟨67331, by rfl⟩) R134663
theorem R89799 : Reach 89799 := rs (se 1 (by rfl) ⟨67349, by rfl⟩) R134699
theorem R89819 : Reach 89819 := rs (se 1 (by rfl) ⟨67364, by rfl⟩) R134729
theorem R89895 : Reach 89895 := rs (se 1 (by rfl) ⟨67421, by rfl⟩) R134843
theorem R89935 : Reach 89935 := rs (se 1 (by rfl) ⟨67451, by rfl⟩) R134903
theorem R89951 : Reach 89951 := rs (se 1 (by rfl) ⟨67463, by rfl⟩) R134927
theorem R89979 : Reach 89979 := rs (se 1 (by rfl) ⟨67484, by rfl⟩) R134969
theorem R221089 : Reach 221089 := rs (se 2 (by rfl) ⟨82908, by rfl⟩) R165817
theorem R90031 : Reach 90031 := rs (se 1 (by rfl) ⟨67523, by rfl⟩) R135047
theorem R286651 : Reach 286651 := rs (se 1 (by rfl) ⟨214988, by rfl⟩) R429977
theorem R90055 : Reach 90055 := rs (se 1 (by rfl) ⟨67541, by rfl⟩) R135083
theorem R90075 : Reach 90075 := rs (se 1 (by rfl) ⟨67556, by rfl⟩) R135113
theorem R90151 : Reach 90151 := rs (se 1 (by rfl) ⟨67613, by rfl⟩) R135227
theorem R90191 : Reach 90191 := rs (se 1 (by rfl) ⟨67643, by rfl⟩) R135287
theorem R90207 : Reach 90207 := rs (se 1 (by rfl) ⟨67655, by rfl⟩) R135311
theorem R90235 : Reach 90235 := rs (se 1 (by rfl) ⟨67676, by rfl⟩) R135353
theorem R90287 : Reach 90287 := rs (se 1 (by rfl) ⟨67715, by rfl⟩) R135431
theorem R90311 : Reach 90311 := rs (se 1 (by rfl) ⟨67733, by rfl⟩) R135467
theorem R90331 : Reach 90331 := rs (se 1 (by rfl) ⟨67748, by rfl⟩) R135497
theorem R90407 : Reach 90407 := rs (se 1 (by rfl) ⟨67805, by rfl⟩) R135611
theorem R90447 : Reach 90447 := rs (se 1 (by rfl) ⟨67835, by rfl⟩) R135671
theorem R90463 : Reach 90463 := rs (se 1 (by rfl) ⟨67847, by rfl⟩) R135695
theorem R90491 : Reach 90491 := rs (se 1 (by rfl) ⟨67868, by rfl⟩) R135737
theorem R90543 : Reach 90543 := rs (se 1 (by rfl) ⟨67907, by rfl⟩) R135815
theorem R90567 : Reach 90567 := rs (se 1 (by rfl) ⟨67925, by rfl⟩) R135851
theorem R90587 : Reach 90587 := rs (se 1 (by rfl) ⟨67940, by rfl⟩) R135881
theorem R746009 : Reach 746009 := rs (se 2 (by rfl) ⟨279753, by rfl⟩) R559507
theorem R90663 : Reach 90663 := rs (se 1 (by rfl) ⟨67997, by rfl⟩) R135995
theorem R90703 : Reach 90703 := rs (se 1 (by rfl) ⟨68027, by rfl⟩) R136055
theorem R90719 : Reach 90719 := rs (se 1 (by rfl) ⟨68039, by rfl⟩) R136079
theorem R90747 : Reach 90747 := rs (se 1 (by rfl) ⟨68060, by rfl⟩) R136121
theorem R254603 : Reach 254603 := rs (se 1 (by rfl) ⟨190952, by rfl⟩) R381905
theorem R90799 : Reach 90799 := rs (se 1 (by rfl) ⟨68099, by rfl⟩) R136199
theorem R90823 : Reach 90823 := rs (se 1 (by rfl) ⟨68117, by rfl⟩) R136235
theorem R549587 : Reach 549587 := rs (se 1 (by rfl) ⟨412190, by rfl⟩) R824381
theorem R90843 : Reach 90843 := rs (se 1 (by rfl) ⟨68132, by rfl⟩) R136265
theorem R451331 : Reach 451331 := rs (se 1 (by rfl) ⟨338498, by rfl⟩) R676997
theorem R90919 : Reach 90919 := rs (se 1 (by rfl) ⟨68189, by rfl⟩) R136379
theorem R90959 : Reach 90959 := rs (se 1 (by rfl) ⟨68219, by rfl⟩) R136439
theorem R90975 : Reach 90975 := rs (se 1 (by rfl) ⟨68231, by rfl⟩) R136463
theorem R91003 : Reach 91003 := rs (se 1 (by rfl) ⟨68252, by rfl⟩) R136505
theorem R91055 : Reach 91055 := rs (se 1 (by rfl) ⟨68291, by rfl⟩) R136583
theorem R91079 : Reach 91079 := rs (se 1 (by rfl) ⟨68309, by rfl⟩) R136619
theorem R91099 : Reach 91099 := rs (se 1 (by rfl) ⟨68324, by rfl⟩) R136649
theorem R5432741 : Reach 5432741 := rs (se 4 (by rfl) ⟨509319, by rfl⟩) R1018639
theorem R976373 : Reach 976373 := rs (se 5 (by rfl) ⟨45767, by rfl⟩) R91535
theorem R190201 : Reach 190201 := rs (se 2 (by rfl) ⟨71325, by rfl⟩) R142651
theorem R583519 : Reach 583519 := rs (se 1 (by rfl) ⟨437639, by rfl⟩) R875279
theorem R649079 : Reach 649079 := rs (se 1 (by rfl) ⟨486809, by rfl⟩) R973619
theorem R550775 : Reach 550775 := rs (se 1 (by rfl) ⟨413081, by rfl⟩) R826163
theorem R321455 : Reach 321455 := rs (se 1 (by rfl) ⟨241091, by rfl⟩) R482183
theorem R288775 : Reach 288775 := rs (se 1 (by rfl) ⟨216581, by rfl⟩) R433163
theorem R157715 : Reach 157715 := rs (se 1 (by rfl) ⟨118286, by rfl⟩) R236573
theorem R288787 : Reach 288787 := rs (se 1 (by rfl) ⟨216590, by rfl⟩) R433181
theorem R551069 : Reach 551069 := rs (se 3 (by rfl) ⟨103325, by rfl⟩) R206651
theorem R452951 : Reach 452951 := rs (se 1 (by rfl) ⟨339713, by rfl⟩) R679427
theorem R1436039 : Reach 1436039 := rs (se 1 (by rfl) ⟨1077029, by rfl⟩) R2154059
theorem R223631 : Reach 223631 := rs (se 1 (by rfl) ⟨167723, by rfl⟩) R335447
theorem R125479 : Reach 125479 := rs (se 1 (by rfl) ⟨94109, by rfl⟩) R188219
theorem R289403 : Reach 289403 := rs (se 1 (by rfl) ⟨217052, by rfl⟩) R434105
theorem R223955 : Reach 223955 := rs (se 1 (by rfl) ⟨167966, by rfl⟩) R335933
theorem R158537 : Reach 158537 := rs (se 2 (by rfl) ⟨59451, by rfl⟩) R118903
theorem R813901 : Reach 813901 := rs (se 3 (by rfl) ⟨152606, by rfl⟩) R305213
theorem R682829 : Reach 682829 := rs (se 3 (by rfl) ⟨128030, by rfl⟩) R256061
theorem R322579 : Reach 322579 := rs (se 1 (by rfl) ⟨241934, by rfl⟩) R483869
theorem R290249 : Reach 290249 := rs (se 2 (by rfl) ⟨108843, by rfl⟩) R217687
theorem R323357 : Reach 323357 := rs (se 3 (by rfl) ⟨60629, by rfl⟩) R121259
theorem R225119 : Reach 225119 := rs (se 1 (by rfl) ⟨168839, by rfl⟩) R337679
theorem R323489 : Reach 323489 := rs (se 2 (by rfl) ⟨121308, by rfl⟩) R242617
theorem R257975 : Reach 257975 := rs (se 1 (by rfl) ⟨193481, by rfl⟩) R386963
theorem R5009501 : Reach 5009501 := rs (se 3 (by rfl) ⟨939281, by rfl⟩) R1878563
theorem R618653 : Reach 618653 := rs (se 3 (by rfl) ⟨115997, by rfl⟩) R231995
theorem R160073 : Reach 160073 := rs (se 2 (by rfl) ⟨60027, by rfl⟩) R120055
theorem R324425 : Reach 324425 := rs (se 2 (by rfl) ⟨121659, by rfl⟩) R243319
theorem R258977 : Reach 258977 := rs (se 2 (by rfl) ⟨97116, by rfl⟩) R194233
theorem R226223 : Reach 226223 := rs (se 1 (by rfl) ⟨169667, by rfl⟩) R339335
theorem R1635329 : Reach 1635329 := rs (se 2 (by rfl) ⟨613248, by rfl⟩) R1226497
theorem R685259 : Reach 685259 := rs (se 1 (by rfl) ⟨513944, by rfl⟩) R1027889
theorem R259433 : Reach 259433 := rs (se 2 (by rfl) ⟨97287, by rfl⟩) R194575
theorem R1013309 : Reach 1013309 := rs (se 3 (by rfl) ⟨189995, by rfl⟩) R379991
theorem R1308305 : Reach 1308305 := rs (se 2 (by rfl) ⟨490614, by rfl⟩) R981229
theorem R456515 : Reach 456515 := rs (se 1 (by rfl) ⟨342386, by rfl⟩) R684773
theorem R227407 : Reach 227407 := rs (se 1 (by rfl) ⟨170555, by rfl⟩) R341111
theorem R653579 : Reach 653579 := rs (se 1 (by rfl) ⟨490184, by rfl⟩) R980369
theorem R162155 : Reach 162155 := rs (se 1 (by rfl) ⟨121616, by rfl⟩) R243233
theorem R391553 : Reach 391553 := rs (se 2 (by rfl) ⟨146832, by rfl⟩) R293665
theorem R522625 : Reach 522625 := rs (se 2 (by rfl) ⟨195984, by rfl⟩) R391969
theorem R1112453 : Reach 1112453 := rs (se 4 (by rfl) ⟨104292, by rfl⟩) R208585
theorem R1309229 : Reach 1309229 := rs (se 3 (by rfl) ⟨245480, by rfl⟩) R490961
theorem R1702579 : Reach 1702579 := rs (se 1 (by rfl) ⟨1276934, by rfl⟩) R2553869
theorem R195283 : Reach 195283 := rs (se 1 (by rfl) ⟨146462, by rfl⟩) R292925
theorem R228055 : Reach 228055 := rs (se 1 (by rfl) ⟨171041, by rfl⟩) R342083
theorem R523115 : Reach 523115 := rs (se 1 (by rfl) ⟨392336, by rfl⟩) R784673
theorem R228359 : Reach 228359 := rs (se 1 (by rfl) ⟨171269, by rfl⟩) R342539
theorem R1375427 : Reach 1375427 := rs (se 1 (by rfl) ⟨1031570, by rfl⟩) R2063141
theorem R425569 : Reach 425569 := rs (se 2 (by rfl) ⟨159588, by rfl⟩) R319177
theorem R196307 : Reach 196307 := rs (se 1 (by rfl) ⟨147230, by rfl⟩) R294461
theorem R130991 : Reach 130991 := rs (se 1 (by rfl) ⟨98243, by rfl⟩) R196487
theorem R294839 : Reach 294839 := rs (se 1 (by rfl) ⟨221129, by rfl⟩) R442259
theorem R131177 : Reach 131177 := rs (se 2 (by rfl) ⟨49191, by rfl⟩) R98383
theorem R98591 : Reach 98591 := rs (se 1 (by rfl) ⟨73943, by rfl⟩) R147887
theorem R98599 : Reach 98599 := rs (se 1 (by rfl) ⟨73949, by rfl⟩) R147899
theorem R196937 : Reach 196937 := rs (se 2 (by rfl) ⟨73851, by rfl⟩) R147703
theorem R950615 : Reach 950615 := rs (se 1 (by rfl) ⟨712961, by rfl⟩) R1425923
theorem R196955 : Reach 196955 := rs (se 1 (by rfl) ⟨147716, by rfl⟩) R295433
theorem R786779 : Reach 786779 := rs (se 1 (by rfl) ⟨590084, by rfl⟩) R1180169
theorem R98671 : Reach 98671 := rs (se 1 (by rfl) ⟨74003, by rfl⟩) R148007
theorem R131495 : Reach 131495 := rs (se 1 (by rfl) ⟨98621, by rfl⟩) R197243
theorem R131579 : Reach 131579 := rs (se 1 (by rfl) ⟨98684, by rfl⟩) R197369
theorem R98887 : Reach 98887 := rs (se 1 (by rfl) ⟨74165, by rfl⟩) R148331
theorem R131705 : Reach 131705 := rs (se 2 (by rfl) ⟨49389, by rfl⟩) R98779
theorem R295595 : Reach 295595 := rs (se 1 (by rfl) ⟨221696, by rfl⟩) R443393
theorem R131759 : Reach 131759 := rs (se 1 (by rfl) ⟨98819, by rfl⟩) R197639
theorem R754379 : Reach 754379 := rs (se 1 (by rfl) ⟨565784, by rfl⟩) R1131569
theorem R393943 : Reach 393943 := rs (se 1 (by rfl) ⟨295457, by rfl⟩) R590915
theorem R131807 : Reach 131807 := rs (se 1 (by rfl) ⟨98855, by rfl⟩) R197711
theorem R230111 : Reach 230111 := rs (se 1 (by rfl) ⟨172583, by rfl⟩) R345167
theorem R197531 : Reach 197531 := rs (se 1 (by rfl) ⟨148148, by rfl⟩) R296297
theorem R132071 : Reach 132071 := rs (se 1 (by rfl) ⟨99053, by rfl⟩) R198107
theorem R197729 : Reach 197729 := rs (se 2 (by rfl) ⟨74148, by rfl⟩) R148297
theorem R296135 : Reach 296135 := rs (se 1 (by rfl) ⟨222101, by rfl⟩) R444203
theorem R132329 : Reach 132329 := rs (se 2 (by rfl) ⟨49623, by rfl⟩) R99247
theorem R132383 : Reach 132383 := rs (se 1 (by rfl) ⟨99287, by rfl⟩) R198575
theorem R197927 : Reach 197927 := rs (se 1 (by rfl) ⟨148445, by rfl⟩) R296891
theorem R99751 : Reach 99751 := rs (se 1 (by rfl) ⟨74813, by rfl⟩) R149627
theorem R132551 : Reach 132551 := rs (se 1 (by rfl) ⟨99413, by rfl⟩) R198827
theorem R198305 : Reach 198305 := rs (se 2 (by rfl) ⟨74364, by rfl⟩) R148729
theorem R132905 : Reach 132905 := rs (se 2 (by rfl) ⟨49839, by rfl⟩) R99679
theorem R132911 : Reach 132911 := rs (se 1 (by rfl) ⟨99683, by rfl⟩) R199367
theorem R460727 : Reach 460727 := rs (se 1 (by rfl) ⟨345545, by rfl⟩) R691091
theorem R100327 : Reach 100327 := rs (se 1 (by rfl) ⟨75245, by rfl⟩) R150491
theorem R198665 : Reach 198665 := rs (se 2 (by rfl) ⟨74499, by rfl⟩) R148999
theorem R133385 : Reach 133385 := rs (se 2 (by rfl) ⟨50019, by rfl⟩) R100039
theorem R1280285 : Reach 1280285 := rs (se 3 (by rfl) ⟨240053, by rfl⟩) R480107
theorem R133487 : Reach 133487 := rs (se 1 (by rfl) ⟨100115, by rfl⟩) R200231
theorem R199079 : Reach 199079 := rs (se 1 (by rfl) ⟨149309, by rfl⟩) R298619
theorem R690605 : Reach 690605 := rs (se 3 (by rfl) ⟨129488, by rfl⟩) R258977
theorem R199187 : Reach 199187 := rs (se 1 (by rfl) ⟨149390, by rfl⟩) R298781
theorem R133703 : Reach 133703 := rs (se 1 (by rfl) ⟨100277, by rfl⟩) R200555
theorem R199241 : Reach 199241 := rs (se 2 (by rfl) ⟨74715, by rfl⟩) R149431
theorem R133739 : Reach 133739 := rs (se 1 (by rfl) ⟨100304, by rfl⟩) R200609
theorem R297647 : Reach 297647 := rs (se 1 (by rfl) ⟨223235, by rfl⟩) R446471
theorem R133967 : Reach 133967 := rs (se 1 (by rfl) ⟨100475, by rfl⟩) R200951
theorem R232271 : Reach 232271 := rs (se 1 (by rfl) ⟨174203, by rfl⟩) R348407
theorem R199655 : Reach 199655 := rs (se 1 (by rfl) ⟨149741, by rfl⟩) R299483
theorem R297971 : Reach 297971 := rs (se 1 (by rfl) ⟨223478, by rfl⟩) R446957
theorem R330875 : Reach 330875 := rs (se 1 (by rfl) ⟨248156, by rfl⟩) R496313
theorem R134363 : Reach 134363 := rs (se 1 (by rfl) ⟨100772, by rfl⟩) R201545
theorem R200033 : Reach 200033 := rs (se 2 (by rfl) ⟨75012, by rfl⟩) R150025
theorem R134537 : Reach 134537 := rs (se 2 (by rfl) ⟨50451, by rfl⟩) R100903
theorem R200123 : Reach 200123 := rs (se 1 (by rfl) ⟨150092, by rfl⟩) R300185
theorem R298511 : Reach 298511 := rs (se 1 (by rfl) ⟨223883, by rfl⟩) R447767
theorem R200249 : Reach 200249 := rs (se 2 (by rfl) ⟨75093, by rfl⟩) R150187
theorem R101983 : Reach 101983 := rs (se 1 (by rfl) ⟨76487, by rfl⟩) R152975
theorem R17927831 : Reach 17927831 := rs (se 1 (by rfl) ⟨13445873, by rfl⟩) R26891747
theorem R134891 : Reach 134891 := rs (se 1 (by rfl) ⟨101168, by rfl⟩) R202337
theorem R1085201 : Reach 1085201 := rs (se 2 (by rfl) ⟨406950, by rfl⟩) R813901
theorem R135119 : Reach 135119 := rs (se 1 (by rfl) ⟨101339, by rfl⟩) R202679
theorem R430105 : Reach 430105 := rs (se 2 (by rfl) ⟨161289, by rfl⟩) R322579
theorem R200915 : Reach 200915 := rs (se 1 (by rfl) ⟨150686, by rfl⟩) R301373
theorem R200969 : Reach 200969 := rs (se 2 (by rfl) ⟨75363, by rfl⟩) R150727
theorem R135515 : Reach 135515 := rs (se 1 (by rfl) ⟨101636, by rfl⟩) R203273
theorem R201185 : Reach 201185 := rs (se 2 (by rfl) ⟨75444, by rfl⟩) R150889
theorem R954899 : Reach 954899 := rs (se 1 (by rfl) ⟨716174, by rfl⟩) R1432349
theorem R135743 : Reach 135743 := rs (se 1 (by rfl) ⟨101807, by rfl⟩) R203615
theorem R299591 : Reach 299591 := rs (se 1 (by rfl) ⟨224693, by rfl⟩) R449387
theorem R135863 : Reach 135863 := rs (se 1 (by rfl) ⟨101897, by rfl⟩) R203795
theorem R103135 : Reach 103135 := rs (se 1 (by rfl) ⟨77351, by rfl⟩) R154703
theorem R201491 : Reach 201491 := rs (se 1 (by rfl) ⟨151118, by rfl⟩) R302237
theorem R136091 : Reach 136091 := rs (se 1 (by rfl) ⟨102068, by rfl⟩) R204137
theorem R496631 : Reach 496631 := rs (se 1 (by rfl) ⟨372473, by rfl⟩) R744947
theorem R300023 : Reach 300023 := rs (se 1 (by rfl) ⟨225017, by rfl⟩) R450035
theorem R201851 : Reach 201851 := rs (se 1 (by rfl) ⟨151388, by rfl⟩) R302777
theorem R562301 : Reach 562301 := rs (se 3 (by rfl) ⟨105431, by rfl⟩) R210863
theorem R857213 : Reach 857213 := rs (se 3 (by rfl) ⟨160727, by rfl⟩) R321455
theorem R201977 : Reach 201977 := rs (se 2 (by rfl) ⟨75741, by rfl⟩) R151483
theorem R136487 : Reach 136487 := rs (se 1 (by rfl) ⟨102365, by rfl⟩) R204731
theorem R136571 : Reach 136571 := rs (se 1 (by rfl) ⟨102428, by rfl⟩) R204857
theorem R202121 : Reach 202121 := rs (se 2 (by rfl) ⟨75795, by rfl⟩) R151591
theorem R202247 : Reach 202247 := rs (se 1 (by rfl) ⟨151685, by rfl⟩) R303371
theorem R497339 : Reach 497339 := rs (se 1 (by rfl) ⟨373004, by rfl⟩) R746009
theorem R202427 : Reach 202427 := rs (se 1 (by rfl) ⟨151820, by rfl⟩) R303641
theorem R366391 : Reach 366391 := rs (se 1 (by rfl) ⟨274793, by rfl⟩) R549587
theorem R202553 : Reach 202553 := rs (se 2 (by rfl) ⟨75957, by rfl⟩) R151915
theorem R300887 : Reach 300887 := rs (se 1 (by rfl) ⟨225665, by rfl⟩) R451331
theorem R203183 : Reach 203183 := rs (se 1 (by rfl) ⟨152387, by rfl⟩) R304775
theorem R203219 : Reach 203219 := rs (se 1 (by rfl) ⟨152414, by rfl⟩) R304829
theorem R203327 : Reach 203327 := rs (se 1 (by rfl) ⟨152495, by rfl⟩) R304991
theorem R432719 : Reach 432719 := rs (se 1 (by rfl) ⟨324539, by rfl⟩) R649079
theorem R367183 : Reach 367183 := rs (se 1 (by rfl) ⟨275387, by rfl⟩) R550775
theorem R203435 : Reach 203435 := rs (se 1 (by rfl) ⟨152576, by rfl⟩) R305153
theorem R105143 : Reach 105143 := rs (se 1 (by rfl) ⟨78857, by rfl⟩) R157715
theorem R367379 : Reach 367379 := rs (se 1 (by rfl) ⟨275534, by rfl⟩) R551069
theorem R301967 : Reach 301967 := rs (se 1 (by rfl) ⟨226475, by rfl⟩) R452951
theorem R334763 : Reach 334763 := rs (se 1 (by rfl) ⟨251072, by rfl⟩) R502145
theorem R957359 : Reach 957359 := rs (se 1 (by rfl) ⟨718019, by rfl⟩) R1436039
theorem R203975 : Reach 203975 := rs (se 1 (by rfl) ⟨152981, by rfl⟩) R305963
theorem R204155 : Reach 204155 := rs (se 1 (by rfl) ⟨153116, by rfl⟩) R306233
theorem R204281 : Reach 204281 := rs (se 2 (by rfl) ⟨76605, by rfl⟩) R153211
theorem R859673 : Reach 859673 := rs (se 2 (by rfl) ⟨322377, by rfl⟩) R644755
theorem R204371 : Reach 204371 := rs (se 1 (by rfl) ⟨153278, by rfl⟩) R306557
theorem R204551 : Reach 204551 := rs (se 1 (by rfl) ⟨153413, by rfl⟩) R306827
theorem R171983 : Reach 171983 := rs (se 1 (by rfl) ⟨128987, by rfl⟩) R257975
theorem R303209 : Reach 303209 := rs (se 2 (by rfl) ⟨113703, by rfl⟩) R227407
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R106715 : Reach 106715 := rs (se 1 (by rfl) ⟨80036, by rfl⟩) R160073
theorem R3449141 : Reach 3449141 := rs (se 5 (by rfl) ⟨161678, by rfl⟩) R323357
theorem R270665 : Reach 270665 := rs (se 2 (by rfl) ⟨101499, by rfl⟩) R202999
theorem R696833 : Reach 696833 := rs (se 2 (by rfl) ⟨261312, by rfl⟩) R522625
theorem R1090219 : Reach 1090219 := rs (se 1 (by rfl) ⟨817664, by rfl⟩) R1635329
theorem R2270105 : Reach 2270105 := rs (se 2 (by rfl) ⟨851289, by rfl⟩) R1702579
theorem R172955 : Reach 172955 := rs (se 1 (by rfl) ⟨129716, by rfl⟩) R259433
theorem R304073 : Reach 304073 := rs (se 2 (by rfl) ⟨114027, by rfl⟩) R228055
theorem R959525 : Reach 959525 := rs (se 4 (by rfl) ⟨89955, by rfl⟩) R179911
theorem R304343 : Reach 304343 := rs (se 1 (by rfl) ⟨228257, by rfl⟩) R456515
theorem R1123571 : Reach 1123571 := rs (se 1 (by rfl) ⟨842678, by rfl⟩) R1685357
theorem R435719 : Reach 435719 := rs (se 1 (by rfl) ⟨326789, by rfl⟩) R653579
theorem R108103 : Reach 108103 := rs (se 1 (by rfl) ⟨81077, by rfl⟩) R162155
theorem R141113 : Reach 141113 := rs (se 2 (by rfl) ⟨52917, by rfl⟩) R105835
theorem R567425 : Reach 567425 := rs (se 2 (by rfl) ⟨212784, by rfl⟩) R425569
theorem R141577 : Reach 141577 := rs (se 2 (by rfl) ⟨53091, by rfl⟩) R106183
theorem R109291 : Reach 109291 := rs (se 1 (by rfl) ⟨81968, by rfl⟩) R163937
theorem R961303 : Reach 961303 := rs (se 1 (by rfl) ⟨720977, by rfl⟩) R1441955
theorem R306395 : Reach 306395 := rs (se 1 (by rfl) ⟨229796, by rfl⟩) R459593
theorem R404747 : Reach 404747 := rs (se 1 (by rfl) ⟨303560, by rfl⟩) R607121
theorem R307259 : Reach 307259 := rs (se 1 (by rfl) ⟨230444, by rfl⟩) R460889
theorem R274537 : Reach 274537 := rs (se 2 (by rfl) ⟨102951, by rfl⟩) R205903
theorem R307529 : Reach 307529 := rs (se 2 (by rfl) ⟨115323, by rfl⟩) R230647
theorem R373193 : Reach 373193 := rs (se 2 (by rfl) ⟨139947, by rfl⟩) R279895
theorem R340499 : Reach 340499 := rs (se 1 (by rfl) ⟨255374, by rfl⟩) R510749
theorem R176975 : Reach 176975 := rs (se 1 (by rfl) ⟨132731, by rfl⟩) R265463
theorem R308047 : Reach 308047 := rs (se 1 (by rfl) ⟨231035, by rfl⟩) R462071
theorem R669221 : Reach 669221 := rs (se 4 (by rfl) ⟨62739, by rfl⟩) R125479
theorem R374969 : Reach 374969 := rs (se 2 (by rfl) ⟨140613, by rfl⟩) R281227
theorem R441611 : Reach 441611 := rs (se 1 (by rfl) ⟨331208, by rfl⟩) R662417
theorem R114043 : Reach 114043 := rs (se 1 (by rfl) ⟨85532, by rfl⟩) R171065
theorem R343511 : Reach 343511 := rs (se 1 (by rfl) ⟨257633, by rfl⟩) R515267
theorem R310879 : Reach 310879 := rs (se 1 (by rfl) ⟨233159, by rfl⟩) R466319
theorem R179975 : Reach 179975 := rs (se 1 (by rfl) ⟨134981, by rfl⟩) R269963
theorem R115111 : Reach 115111 := rs (se 1 (by rfl) ⟨86333, by rfl⟩) R172667
theorem R115195 : Reach 115195 := rs (se 1 (by rfl) ⟨86396, by rfl⟩) R172793
theorem R1721033 : Reach 1721033 := rs (se 2 (by rfl) ⟨645387, by rfl⟩) R1290775
theorem R377567 : Reach 377567 := rs (se 1 (by rfl) ⟨283175, by rfl⟩) R566351
theorem R443231 : Reach 443231 := rs (se 1 (by rfl) ⟨332423, by rfl⟩) R664847
theorem R3621827 : Reach 3621827 := rs (se 1 (by rfl) ⟨2716370, by rfl⟩) R5432741
theorem R640199 : Reach 640199 := rs (se 1 (by rfl) ⟨480149, by rfl⟩) R960299
theorem R378425 : Reach 378425 := rs (se 2 (by rfl) ⟨141909, by rfl⟩) R283819
theorem R149087 : Reach 149087 := rs (se 1 (by rfl) ⟨111815, by rfl⟩) R223631
theorem R149303 : Reach 149303 := rs (se 1 (by rfl) ⟨111977, by rfl⟩) R223955
theorem R1034167 : Reach 1034167 := rs (se 1 (by rfl) ⟨775625, by rfl⟩) R1551251
theorem R150079 : Reach 150079 := rs (se 1 (by rfl) ⟨112559, by rfl⟩) R225119
theorem R215659 : Reach 215659 := rs (se 1 (by rfl) ⟨161744, by rfl⟩) R323489
theorem R445175 : Reach 445175 := rs (se 1 (by rfl) ⟨333881, by rfl⟩) R667763
theorem R412435 : Reach 412435 := rs (se 1 (by rfl) ⟨309326, by rfl⟩) R618653
theorem R1035179 : Reach 1035179 := rs (se 1 (by rfl) ⟨776384, by rfl⟩) R1552769
theorem R117865 : Reach 117865 := rs (se 2 (by rfl) ⟨44199, by rfl⟩) R88399
theorem R216283 : Reach 216283 := rs (se 1 (by rfl) ⟨162212, by rfl⟩) R324425
theorem R445661 : Reach 445661 := rs (se 3 (by rfl) ⟨83561, by rfl⟩) R167123
theorem R150761 : Reach 150761 := rs (se 2 (by rfl) ⟨56535, by rfl⟩) R113071
theorem R150815 : Reach 150815 := rs (se 1 (by rfl) ⟨113111, by rfl⟩) R226223
theorem R118265 : Reach 118265 := rs (se 2 (by rfl) ⟨44349, by rfl⟩) R88699
theorem R904765 : Reach 904765 := rs (se 3 (by rfl) ⟨169643, by rfl⟩) R339287
theorem R675539 : Reach 675539 := rs (se 1 (by rfl) ⟨506654, by rfl⟩) R1013309
theorem R872203 : Reach 872203 := rs (se 1 (by rfl) ⟨654152, by rfl⟩) R1308305
theorem R119017 : Reach 119017 := rs (se 2 (by rfl) ⟨44631, by rfl⟩) R89263
theorem R741635 : Reach 741635 := rs (se 1 (by rfl) ⟨556226, by rfl⟩) R1112453
theorem R381257 : Reach 381257 := rs (se 2 (by rfl) ⟨142971, by rfl⟩) R285943
theorem R872819 : Reach 872819 := rs (se 1 (by rfl) ⟨654614, by rfl⟩) R1309229
theorem R348743 : Reach 348743 := rs (se 1 (by rfl) ⟨261557, by rfl⟩) R523115
theorem R152185 : Reach 152185 := rs (se 2 (by rfl) ⟨57069, by rfl⟩) R114139
theorem R152239 : Reach 152239 := rs (se 1 (by rfl) ⟨114179, by rfl⟩) R228359
theorem R840527 : Reach 840527 := rs (se 1 (by rfl) ⟨630395, by rfl⟩) R1260791
theorem R251095 : Reach 251095 := rs (se 1 (by rfl) ⟨188321, by rfl⟩) R376643
theorem R382201 : Reach 382201 := rs (se 2 (by rfl) ⟨143325, by rfl⟩) R286651
theorem R87327 : Reach 87327 := rs (se 1 (by rfl) ⟨65495, by rfl⟩) R130991
theorem R87387 : Reach 87387 := rs (se 1 (by rfl) ⟨65540, by rfl⟩) R131081
theorem R87407 : Reach 87407 := rs (se 1 (by rfl) ⟨65555, by rfl⟩) R131111
theorem R87463 : Reach 87463 := rs (se 1 (by rfl) ⟨65597, by rfl⟩) R131195
theorem R87547 : Reach 87547 := rs (se 1 (by rfl) ⟨65660, by rfl⟩) R131321
theorem R87615 : Reach 87615 := rs (se 1 (by rfl) ⟨65711, by rfl⟩) R131423
theorem R87623 : Reach 87623 := rs (se 1 (by rfl) ⟨65717, by rfl⟩) R131435
theorem R87775 : Reach 87775 := rs (se 1 (by rfl) ⟨65831, by rfl⟩) R131663
theorem R87855 : Reach 87855 := rs (se 1 (by rfl) ⟨65891, by rfl⟩) R131783
theorem R87963 : Reach 87963 := rs (se 1 (by rfl) ⟨65972, by rfl⟩) R131945
theorem R88015 : Reach 88015 := rs (se 1 (by rfl) ⟨66011, by rfl⟩) R132023
theorem R88039 : Reach 88039 := rs (se 1 (by rfl) ⟨66029, by rfl⟩) R132059
theorem R514127 : Reach 514127 := rs (se 1 (by rfl) ⟨385595, by rfl⟩) R771191
theorem R88351 : Reach 88351 := rs (se 1 (by rfl) ⟨66263, by rfl⟩) R132527
theorem R186715 : Reach 186715 := rs (se 1 (by rfl) ⟨140036, by rfl⟩) R280073
theorem R88411 : Reach 88411 := rs (se 1 (by rfl) ⟨66308, by rfl⟩) R132617
theorem R88431 : Reach 88431 := rs (se 1 (by rfl) ⟨66323, by rfl⟩) R132647
theorem R88487 : Reach 88487 := rs (se 1 (by rfl) ⟨66365, by rfl⟩) R132731
theorem R252371 : Reach 252371 := rs (se 1 (by rfl) ⟨189278, by rfl⟩) R378557
theorem R88571 : Reach 88571 := rs (se 1 (by rfl) ⟨66428, by rfl⟩) R132857
theorem R449063 : Reach 449063 := rs (se 1 (by rfl) ⟨336797, by rfl⟩) R673595
theorem R88639 : Reach 88639 := rs (se 1 (by rfl) ⟨66479, by rfl⟩) R132959
theorem R88647 : Reach 88647 := rs (se 1 (by rfl) ⟨66485, by rfl⟩) R132971
theorem R121439 : Reach 121439 := rs (se 1 (by rfl) ⟨91079, by rfl⟩) R182159
theorem R88799 : Reach 88799 := rs (se 1 (by rfl) ⟨66599, by rfl⟩) R133199
theorem R514835 : Reach 514835 := rs (se 1 (by rfl) ⟨386126, by rfl⟩) R772253
theorem R88879 : Reach 88879 := rs (se 1 (by rfl) ⟨66659, by rfl⟩) R133319
theorem R252827 : Reach 252827 := rs (se 1 (by rfl) ⟨189620, by rfl⟩) R379241
theorem R88987 : Reach 88987 := rs (se 1 (by rfl) ⟨66740, by rfl⟩) R133481
theorem R89039 : Reach 89039 := rs (se 1 (by rfl) ⟨66779, by rfl⟩) R133559
theorem R89063 : Reach 89063 := rs (se 1 (by rfl) ⟨66797, by rfl⟩) R133595
theorem R1530899 : Reach 1530899 := rs (se 1 (by rfl) ⟨1148174, by rfl⟩) R2296349
theorem R678941 : Reach 678941 := rs (se 3 (by rfl) ⟨127301, by rfl⟩) R254603
theorem R89375 : Reach 89375 := rs (se 1 (by rfl) ⟨67031, by rfl⟩) R134063
theorem R89435 : Reach 89435 := rs (se 1 (by rfl) ⟨67076, by rfl⟩) R134153
theorem R89455 : Reach 89455 := rs (se 1 (by rfl) ⟨67091, by rfl⟩) R134183
theorem R220553 : Reach 220553 := rs (se 2 (by rfl) ⟨82707, by rfl⟩) R165415
theorem R89511 : Reach 89511 := rs (se 1 (by rfl) ⟨67133, by rfl⟩) R134267
theorem R220603 : Reach 220603 := rs (se 1 (by rfl) ⟨165452, by rfl⟩) R330905
theorem R548345 : Reach 548345 := rs (se 2 (by rfl) ⟨205629, by rfl⟩) R411259
theorem R89595 : Reach 89595 := rs (se 1 (by rfl) ⟨67196, by rfl⟩) R134393
theorem R89663 : Reach 89663 := rs (se 1 (by rfl) ⟨67247, by rfl⟩) R134495
theorem R89671 : Reach 89671 := rs (se 1 (by rfl) ⟨67253, by rfl⟩) R134507
theorem R253601 : Reach 253601 := rs (se 2 (by rfl) ⟨95100, by rfl⟩) R190201
theorem R89823 : Reach 89823 := rs (se 1 (by rfl) ⟨67367, by rfl⟩) R134735
theorem R220907 : Reach 220907 := rs (se 1 (by rfl) ⟨165680, by rfl⟩) R331361
theorem R778025 : Reach 778025 := rs (se 2 (by rfl) ⟨291759, by rfl⟩) R583519
theorem R89903 : Reach 89903 := rs (se 1 (by rfl) ⟨67427, by rfl⟩) R134855
theorem R876395 : Reach 876395 := rs (se 1 (by rfl) ⟨657296, by rfl⟩) R1314593
theorem R90011 : Reach 90011 := rs (se 1 (by rfl) ⟨67508, by rfl⟩) R135017
theorem R90063 : Reach 90063 := rs (se 1 (by rfl) ⟨67547, by rfl⟩) R135095
theorem R90087 : Reach 90087 := rs (se 1 (by rfl) ⟨67565, by rfl⟩) R135131
theorem R1138697 : Reach 1138697 := rs (se 2 (by rfl) ⟨427011, by rfl⟩) R854023
theorem R385033 : Reach 385033 := rs (se 2 (by rfl) ⟨144387, by rfl⟩) R288775
theorem R581651 : Reach 581651 := rs (se 1 (by rfl) ⟨436238, by rfl⟩) R872477
theorem R385049 : Reach 385049 := rs (se 2 (by rfl) ⟨144393, by rfl⟩) R288787
theorem R90399 : Reach 90399 := rs (se 1 (by rfl) ⟨67799, by rfl⟩) R135599
theorem R90459 : Reach 90459 := rs (se 1 (by rfl) ⟨67844, by rfl⟩) R135689
theorem R90479 : Reach 90479 := rs (se 1 (by rfl) ⟨67859, by rfl⟩) R135719
theorem R90535 : Reach 90535 := rs (se 1 (by rfl) ⟨67901, by rfl⟩) R135803
theorem R90619 : Reach 90619 := rs (se 1 (by rfl) ⟨67964, by rfl⟩) R135929
theorem R90687 : Reach 90687 := rs (se 1 (by rfl) ⟨68015, by rfl⟩) R136031
theorem R90695 : Reach 90695 := rs (se 1 (by rfl) ⟨68021, by rfl⟩) R136043
theorem R451169 : Reach 451169 := rs (se 2 (by rfl) ⟨169188, by rfl⟩) R338377
theorem R221879 : Reach 221879 := rs (se 1 (by rfl) ⟨166409, by rfl⟩) R332819
theorem R90847 : Reach 90847 := rs (se 1 (by rfl) ⟨68135, by rfl⟩) R136271
theorem R90927 : Reach 90927 := rs (se 1 (by rfl) ⟨68195, by rfl⟩) R136391
theorem R91035 : Reach 91035 := rs (se 1 (by rfl) ⟨68276, by rfl⟩) R136553
theorem R91087 : Reach 91087 := rs (se 1 (by rfl) ⟨68315, by rfl⟩) R136631
theorem R189415 : Reach 189415 := rs (se 1 (by rfl) ⟨142061, by rfl⟩) R284123
theorem R91111 : Reach 91111 := rs (se 1 (by rfl) ⟨68333, by rfl⟩) R136667
theorem R451817 : Reach 451817 := rs (se 2 (by rfl) ⟨169431, by rfl⟩) R338863
theorem R189791 : Reach 189791 := rs (se 1 (by rfl) ⟨142343, by rfl⟩) R284687
theorem R517499 : Reach 517499 := rs (se 1 (by rfl) ⟨388124, by rfl⟩) R776249
theorem R451979 : Reach 451979 := rs (se 1 (by rfl) ⟨338984, by rfl⟩) R677969
theorem R288161 : Reach 288161 := rs (se 2 (by rfl) ⟨108060, by rfl⟩) R216121
theorem R222983 : Reach 222983 := rs (se 1 (by rfl) ⟨167237, by rfl⟩) R334475
theorem R223033 : Reach 223033 := rs (se 2 (by rfl) ⟨83637, by rfl⟩) R167275
theorem R223337 : Reach 223337 := rs (se 2 (by rfl) ⟨83751, by rfl⟩) R167503
theorem R223655 : Reach 223655 := rs (se 1 (by rfl) ⟨167741, by rfl⟩) R335483
theorem R354727 : Reach 354727 := rs (se 1 (by rfl) ⟨266045, by rfl⟩) R532091
theorem R223823 : Reach 223823 := rs (se 1 (by rfl) ⟨167867, by rfl⟩) R335735
theorem R191585 : Reach 191585 := rs (se 2 (by rfl) ⟨71844, by rfl⟩) R143689
theorem R224471 : Reach 224471 := rs (se 1 (by rfl) ⟨168353, by rfl⟩) R336707
theorem R650915 : Reach 650915 := rs (se 1 (by rfl) ⟨488186, by rfl⟩) R976373
theorem R290621 : Reach 290621 := rs (se 3 (by rfl) ⟨54491, by rfl⟩) R108983
theorem R2256983 : Reach 2256983 := rs (se 1 (by rfl) ⟨1692737, by rfl⟩) R3385475
theorem R1208591 : Reach 1208591 := rs (se 1 (by rfl) ⟨906443, by rfl⟩) R1812887
theorem R192935 : Reach 192935 := rs (se 1 (by rfl) ⟨144701, by rfl⟩) R289403
theorem R225787 : Reach 225787 := rs (se 1 (by rfl) ⟨169340, by rfl⟩) R338681
theorem R455219 : Reach 455219 := rs (se 1 (by rfl) ⟨341414, by rfl⟩) R682829
theorem R225899 : Reach 225899 := rs (se 1 (by rfl) ⟨169424, by rfl⟩) R338849
theorem R291481 : Reach 291481 := rs (se 2 (by rfl) ⟨109305, by rfl⟩) R218611
theorem R160591 : Reach 160591 := rs (se 1 (by rfl) ⟨120443, by rfl⟩) R240887
theorem R422765 : Reach 422765 := rs (se 3 (by rfl) ⟨79268, by rfl⟩) R158537
theorem R95131 : Reach 95131 := rs (se 1 (by rfl) ⟨71348, by rfl⟩) R142697
theorem R947153 : Reach 947153 := rs (se 2 (by rfl) ⟨355182, by rfl⟩) R710365
theorem R193499 : Reach 193499 := rs (se 1 (by rfl) ⟨145124, by rfl⟩) R290249
theorem R226547 : Reach 226547 := rs (se 1 (by rfl) ⟨169910, by rfl⟩) R339821
theorem R3339667 : Reach 3339667 := rs (se 1 (by rfl) ⟨2504750, by rfl⟩) R5009501
theorem R226759 : Reach 226759 := rs (se 1 (by rfl) ⟨170069, by rfl⟩) R340139
theorem R3667805 : Reach 3667805 := rs (se 3 (by rfl) ⟨687713, by rfl⟩) R1375427
theorem R1144691 : Reach 1144691 := rs (se 1 (by rfl) ⟨858518, by rfl⟩) R1717037
theorem R456839 : Reach 456839 := rs (se 1 (by rfl) ⟨342629, by rfl⟩) R685259
theorem R260377 : Reach 260377 := rs (se 2 (by rfl) ⟨97641, by rfl⟩) R195283
theorem R2587085 : Reach 2587085 := rs (se 3 (by rfl) ⟨485078, by rfl⟩) R970157
theorem R457289 : Reach 457289 := rs (se 2 (by rfl) ⟨171483, by rfl⟩) R342967
theorem R424723 : Reach 424723 := rs (se 1 (by rfl) ⟨318542, by rfl⟩) R637085
theorem R1899409 : Reach 1899409 := rs (se 2 (by rfl) ⟨712278, by rfl⟩) R1424557
theorem R162731 : Reach 162731 := rs (se 1 (by rfl) ⟨122048, by rfl⟩) R244097
theorem R261035 : Reach 261035 := rs (se 1 (by rfl) ⟨195776, by rfl⟩) R391553
theorem R228491 : Reach 228491 := rs (se 1 (by rfl) ⟨171368, by rfl⟩) R342737
theorem R228703 : Reach 228703 := rs (se 1 (by rfl) ⟨171527, by rfl⟩) R343055
theorem R294515 : Reach 294515 := rs (se 1 (by rfl) ⟨220886, by rfl⟩) R441773
theorem R98095 : Reach 98095 := rs (se 1 (by rfl) ⟨73571, by rfl⟩) R147143
theorem R130871 : Reach 130871 := rs (se 1 (by rfl) ⟨98153, by rfl⟩) R196307
theorem R294785 : Reach 294785 := rs (se 2 (by rfl) ⟨110544, by rfl⟩) R221089
theorem R98203 : Reach 98203 := rs (se 1 (by rfl) ⟨73652, by rfl⟩) R147305
theorem R196559 : Reach 196559 := rs (se 1 (by rfl) ⟨147419, by rfl⟩) R294839
theorem R131291 : Reach 131291 := rs (se 1 (by rfl) ⟨98468, by rfl⟩) R196937
theorem R131303 : Reach 131303 := rs (se 1 (by rfl) ⟨98477, by rfl⟩) R196955
theorem R524519 : Reach 524519 := rs (se 1 (by rfl) ⟨393389, by rfl⟩) R786779
theorem R131465 : Reach 131465 := rs (se 2 (by rfl) ⟨49299, by rfl⟩) R98599
theorem R197063 : Reach 197063 := rs (se 1 (by rfl) ⟨147797, by rfl⟩) R295595
theorem R1147355 : Reach 1147355 := rs (se 1 (by rfl) ⟨860516, by rfl⟩) R1721033
theorem R131561 : Reach 131561 := rs (se 2 (by rfl) ⟨49335, by rfl⟩) R98671
theorem R295487 : Reach 295487 := rs (se 1 (by rfl) ⟨221615, by rfl⟩) R443231
theorem R131687 : Reach 131687 := rs (se 1 (by rfl) ⟨98765, by rfl⟩) R197531
theorem R131819 : Reach 131819 := rs (se 1 (by rfl) ⟨98864, by rfl⟩) R197729
theorem R262909 : Reach 262909 := rs (se 3 (by rfl) ⟨49295, by rfl⟩) R98591
theorem R131849 : Reach 131849 := rs (se 2 (by rfl) ⟨49443, by rfl⟩) R98887
theorem R197423 : Reach 197423 := rs (se 1 (by rfl) ⟨148067, by rfl⟩) R296135
theorem R426799 : Reach 426799 := rs (se 1 (by rfl) ⟨320099, by rfl⟩) R640199
theorem R131951 : Reach 131951 := rs (se 1 (by rfl) ⟨98963, by rfl⟩) R197927
theorem R525257 : Reach 525257 := rs (se 2 (by rfl) ⟨196971, by rfl⟩) R393943
theorem R99391 : Reach 99391 := rs (se 1 (by rfl) ⟨74543, by rfl⟩) R149087
theorem R132203 : Reach 132203 := rs (se 1 (by rfl) ⟨99152, by rfl⟩) R198305
theorem R99535 : Reach 99535 := rs (se 1 (by rfl) ⟨74651, by rfl⟩) R149303
theorem R132443 : Reach 132443 := rs (se 1 (by rfl) ⟨99332, by rfl⟩) R198665
theorem R755077 : Reach 755077 := rs (se 4 (by rfl) ⟨70788, by rfl⟩) R141577
theorem R853523 : Reach 853523 := rs (se 1 (by rfl) ⟨640142, by rfl⟩) R1280285
theorem R132719 : Reach 132719 := rs (se 1 (by rfl) ⟨99539, by rfl⟩) R199079
theorem R460403 : Reach 460403 := rs (se 1 (by rfl) ⟨345302, by rfl⟩) R690605
theorem R132791 : Reach 132791 := rs (se 1 (by rfl) ⟨99593, by rfl⟩) R199187
theorem R132827 : Reach 132827 := rs (se 1 (by rfl) ⟨99620, by rfl⟩) R199241
theorem R198431 : Reach 198431 := rs (se 1 (by rfl) ⟨148823, by rfl⟩) R297647
theorem R296783 : Reach 296783 := rs (se 1 (by rfl) ⟨222587, by rfl⟩) R445175
theorem R133001 : Reach 133001 := rs (se 2 (by rfl) ⟨49875, by rfl⟩) R99751
theorem R690119 : Reach 690119 := rs (se 1 (by rfl) ⟨517589, by rfl⟩) R1035179
theorem R133103 : Reach 133103 := rs (se 1 (by rfl) ⟨99827, by rfl⟩) R199655
theorem R198647 : Reach 198647 := rs (se 1 (by rfl) ⟨148985, by rfl⟩) R297971
theorem R297107 : Reach 297107 := rs (se 1 (by rfl) ⟨222830, by rfl⟩) R445661
theorem R100507 : Reach 100507 := rs (se 1 (by rfl) ⟨75380, by rfl⟩) R150761
theorem R100543 : Reach 100543 := rs (se 1 (by rfl) ⟨75407, by rfl⟩) R150815
theorem R133355 : Reach 133355 := rs (se 1 (by rfl) ⟨100016, by rfl⟩) R200033
theorem R133415 : Reach 133415 := rs (se 1 (by rfl) ⟨100061, by rfl⟩) R200123
theorem R199007 : Reach 199007 := rs (se 1 (by rfl) ⟨149255, by rfl⟩) R298511
theorem R133499 : Reach 133499 := rs (se 1 (by rfl) ⟨100124, by rfl⟩) R200249
theorem R461213 : Reach 461213 := rs (se 3 (by rfl) ⟨86477, by rfl⟩) R172955
theorem R297377 : Reach 297377 := rs (se 2 (by rfl) ⟨111516, by rfl⟩) R223033
theorem R723467 : Reach 723467 := rs (se 1 (by rfl) ⟨542600, by rfl⟩) R1085201
theorem R1378889 : Reach 1378889 := rs (se 2 (by rfl) ⟨517083, by rfl⟩) R1034167
theorem R133769 : Reach 133769 := rs (se 2 (by rfl) ⟨50163, by rfl⟩) R100327
theorem R133943 : Reach 133943 := rs (se 1 (by rfl) ⟨100457, by rfl⟩) R200915
theorem R494423 : Reach 494423 := rs (se 1 (by rfl) ⟨370817, by rfl⟩) R741635
theorem R133979 : Reach 133979 := rs (se 1 (by rfl) ⟨100484, by rfl⟩) R200969
theorem R134123 : Reach 134123 := rs (se 1 (by rfl) ⟨100592, by rfl⟩) R201185
theorem R199727 : Reach 199727 := rs (se 1 (by rfl) ⟨149795, by rfl⟩) R299591
theorem R134327 : Reach 134327 := rs (se 1 (by rfl) ⟨100745, by rfl⟩) R201491
theorem R560351 : Reach 560351 := rs (se 1 (by rfl) ⟨420263, by rfl⟩) R840527
theorem R331087 : Reach 331087 := rs (se 1 (by rfl) ⟨248315, by rfl⟩) R496631
theorem R200015 : Reach 200015 := rs (se 1 (by rfl) ⟨150011, by rfl⟩) R300023
theorem R134567 : Reach 134567 := rs (se 1 (by rfl) ⟨100925, by rfl⟩) R201851
theorem R200105 : Reach 200105 := rs (se 2 (by rfl) ⟨75039, by rfl⟩) R150079
theorem R134651 : Reach 134651 := rs (se 1 (by rfl) ⟨100988, by rfl⟩) R201977
theorem R134747 : Reach 134747 := rs (se 1 (by rfl) ⟨101060, by rfl⟩) R202121
theorem R134831 : Reach 134831 := rs (se 1 (by rfl) ⟨101123, by rfl⟩) R202247
theorem R1281737 : Reach 1281737 := rs (se 2 (by rfl) ⟨480651, by rfl⟩) R961303
theorem R331559 : Reach 331559 := rs (se 1 (by rfl) ⟨248669, by rfl⟩) R497339
theorem R134951 : Reach 134951 := rs (se 1 (by rfl) ⟨101213, by rfl⟩) R202427
theorem R135035 : Reach 135035 := rs (se 1 (by rfl) ⟨101276, by rfl⟩) R202553
theorem R200591 : Reach 200591 := rs (se 1 (by rfl) ⟨150443, by rfl⟩) R300887
theorem R2199653 : Reach 2199653 := rs (se 4 (by rfl) ⟨206217, by rfl⟩) R412435
theorem R135455 : Reach 135455 := rs (se 1 (by rfl) ⟨101591, by rfl⟩) R203183
theorem R168247 : Reach 168247 := rs (se 1 (by rfl) ⟨126185, by rfl⟩) R252371
theorem R135479 : Reach 135479 := rs (se 1 (by rfl) ⟨101609, by rfl⟩) R203219
theorem R299375 : Reach 299375 := rs (se 1 (by rfl) ⟨224531, by rfl⟩) R449063
theorem R135551 : Reach 135551 := rs (se 1 (by rfl) ⟨101663, by rfl⟩) R203327
theorem R135623 : Reach 135623 := rs (se 1 (by rfl) ⟨101717, by rfl⟩) R203435
theorem R201311 : Reach 201311 := rs (se 1 (by rfl) ⟨150983, by rfl⟩) R301967
theorem R168551 : Reach 168551 := rs (se 1 (by rfl) ⟨126413, by rfl⟩) R252827
theorem R1020599 : Reach 1020599 := rs (se 1 (by rfl) ⟨765449, by rfl⟩) R1530899
theorem R135977 : Reach 135977 := rs (se 2 (by rfl) ⟨50991, by rfl⟩) R101983
theorem R135983 : Reach 135983 := rs (se 1 (by rfl) ⟨101987, by rfl⟩) R203975
theorem R136103 : Reach 136103 := rs (se 1 (by rfl) ⟨102077, by rfl⟩) R204155
theorem R365563 : Reach 365563 := rs (se 1 (by rfl) ⟨274172, by rfl⟩) R548345
theorem R136187 : Reach 136187 := rs (se 1 (by rfl) ⟨102140, by rfl⟩) R204281
theorem R136247 : Reach 136247 := rs (se 1 (by rfl) ⟨102185, by rfl⟩) R204371
theorem R169067 : Reach 169067 := rs (se 1 (by rfl) ⟨126800, by rfl⟩) R253601
theorem R136367 : Reach 136367 := rs (se 1 (by rfl) ⟨102275, by rfl⟩) R204551
theorem R759131 : Reach 759131 := rs (se 1 (by rfl) ⟨569348, by rfl⟩) R1138697
theorem R202139 : Reach 202139 := rs (se 1 (by rfl) ⟨151604, by rfl⟩) R303209
theorem R366049 : Reach 366049 := rs (se 2 (by rfl) ⟨137268, by rfl⟩) R274537
theorem R2299427 : Reach 2299427 := rs (se 1 (by rfl) ⟨1724570, by rfl⟩) R3449141
theorem R464555 : Reach 464555 := rs (se 1 (by rfl) ⟨348416, by rfl⟩) R696833
theorem R300779 : Reach 300779 := rs (se 1 (by rfl) ⟨225584, by rfl⟩) R451169
theorem R1513403 : Reach 1513403 := rs (se 1 (by rfl) ⟨1135052, by rfl⟩) R2270105
theorem R202715 : Reach 202715 := rs (se 1 (by rfl) ⟨152036, by rfl⟩) R304073
theorem R301049 : Reach 301049 := rs (se 2 (by rfl) ⟨112893, by rfl⟩) R225787
theorem R202895 : Reach 202895 := rs (se 1 (by rfl) ⟨152171, by rfl⟩) R304343
theorem R301211 : Reach 301211 := rs (se 1 (by rfl) ⟨225908, by rfl⟩) R451817
theorem R202913 : Reach 202913 := rs (se 2 (by rfl) ⟨76092, by rfl⟩) R152185
theorem R202985 : Reach 202985 := rs (se 2 (by rfl) ⟨76119, by rfl⟩) R152239
theorem R301319 : Reach 301319 := rs (se 1 (by rfl) ⟨225989, by rfl⟩) R451979
theorem R137513 : Reach 137513 := rs (se 2 (by rfl) ⟨51567, by rfl⟩) R103135
theorem R596413 : Reach 596413 := rs (se 3 (by rfl) ⟨111827, by rfl⟩) R223655
theorem R2038405 : Reach 2038405 := rs (se 4 (by rfl) ⟨191100, by rfl⟩) R382201
theorem R334793 : Reach 334793 := rs (se 2 (by rfl) ⟨125547, by rfl⟩) R251095
theorem R302345 : Reach 302345 := rs (se 2 (by rfl) ⟨113379, by rfl⟩) R226759
theorem R204263 : Reach 204263 := rs (se 1 (by rfl) ⟨153197, by rfl⟩) R306395
theorem R269831 : Reach 269831 := rs (se 1 (by rfl) ⟨202373, by rfl⟩) R404747
theorem R433943 : Reach 433943 := rs (se 1 (by rfl) ⟨325457, by rfl⟩) R650915
theorem R204839 : Reach 204839 := rs (se 1 (by rfl) ⟨153629, by rfl⟩) R307259
theorem R205019 : Reach 205019 := rs (se 1 (by rfl) ⟨153764, by rfl⟩) R307529
theorem R303479 : Reach 303479 := rs (se 1 (by rfl) ⟨227609, by rfl⟩) R455219
theorem R631435 : Reach 631435 := rs (se 1 (by rfl) ⟨473576, by rfl⟩) R947153
theorem R566297 : Reach 566297 := rs (se 2 (by rfl) ⟨212361, by rfl⟩) R424723
theorem R2532545 : Reach 2532545 := rs (se 2 (by rfl) ⟨949704, by rfl⟩) R1899409
theorem R763127 : Reach 763127 := rs (se 1 (by rfl) ⟨572345, by rfl⟩) R1144691
theorem R304559 : Reach 304559 := rs (se 1 (by rfl) ⟨228419, by rfl⟩) R456839
theorem R304859 : Reach 304859 := rs (se 1 (by rfl) ⟨228644, by rfl⟩) R457289
theorem R304937 : Reach 304937 := rs (se 2 (by rfl) ⟨114351, by rfl⟩) R228703
theorem R108487 : Reach 108487 := rs (se 1 (by rfl) ⟨81365, by rfl⟩) R162731
theorem R174023 : Reach 174023 := rs (se 1 (by rfl) ⟨130517, by rfl⟩) R261035
theorem R633743 : Reach 633743 := rs (se 1 (by rfl) ⟨475307, by rfl⟩) R950615
theorem R502919 : Reach 502919 := rs (se 1 (by rfl) ⟨377189, by rfl⟩) R754379
theorem R1453625 : Reach 1453625 := rs (se 2 (by rfl) ⟨545109, by rfl⟩) R1090219
theorem R307151 : Reach 307151 := rs (se 1 (by rfl) ⟨230363, by rfl⟩) R460727
theorem R1388677 : Reach 1388677 := rs (se 4 (by rfl) ⟨130188, by rfl⟩) R260377
theorem R929981 : Reach 929981 := rs (se 3 (by rfl) ⟨174371, by rfl⟩) R348743
theorem R995813 : Reach 995813 := rs (se 4 (by rfl) ⟨93357, by rfl⟩) R186715
theorem R144137 : Reach 144137 := rs (se 2 (by rfl) ⟨54051, by rfl⟩) R108103
theorem R636599 : Reach 636599 := rs (se 1 (by rfl) ⟨477449, by rfl⟩) R954899
theorem R472969 : Reach 472969 := rs (se 2 (by rfl) ⟨177363, by rfl⟩) R354727
theorem R374867 : Reach 374867 := rs (se 1 (by rfl) ⟨281150, by rfl⟩) R562301
theorem R571475 : Reach 571475 := rs (se 1 (by rfl) ⟨428606, by rfl⟩) R857213
theorem R1554565 : Reach 1554565 := rs (se 4 (by rfl) ⟨145740, by rfl⟩) R291481
theorem R145721 : Reach 145721 := rs (se 2 (by rfl) ⟨54645, by rfl⟩) R109291
theorem R342751 : Reach 342751 := rs (se 1 (by rfl) ⟨257063, by rfl⟩) R514127
theorem R343223 : Reach 343223 := rs (se 1 (by rfl) ⟨257417, by rfl⟩) R514835
theorem R244919 : Reach 244919 := rs (se 1 (by rfl) ⟨183689, by rfl⟩) R367379
theorem R638239 : Reach 638239 := rs (se 1 (by rfl) ⟨478679, by rfl⟩) R957359
theorem R376301 : Reach 376301 := rs (se 3 (by rfl) ⟨70556, by rfl⟩) R141113
theorem R147035 : Reach 147035 := rs (se 1 (by rfl) ⟨110276, by rfl⟩) R220553
theorem R1162937 : Reach 1162937 := rs (se 2 (by rfl) ⟨436101, by rfl⟩) R872203
theorem R573115 : Reach 573115 := rs (se 1 (by rfl) ⟨429836, by rfl⟩) R859673
theorem R147271 : Reach 147271 := rs (se 1 (by rfl) ⟨110453, by rfl⟩) R220907
theorem R573473 : Reach 573473 := rs (se 2 (by rfl) ⟨215052, by rfl⟩) R430105
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R180443 : Reach 180443 := rs (se 1 (by rfl) ⟨135332, by rfl⟩) R270665
theorem R147919 : Reach 147919 := rs (se 1 (by rfl) ⟨110939, by rfl⟩) R221879
theorem R639683 : Reach 639683 := rs (se 1 (by rfl) ⟨479762, by rfl⟩) R959525
theorem R344999 : Reach 344999 := rs (se 1 (by rfl) ⟨258749, by rfl⟩) R517499
theorem R410729 : Reach 410729 := rs (se 2 (by rfl) ⟨154023, by rfl⟩) R308047
theorem R214121 : Reach 214121 := rs (se 2 (by rfl) ⟨80295, by rfl⟩) R160591
theorem R148655 : Reach 148655 := rs (se 1 (by rfl) ⟨111491, by rfl⟩) R222983
theorem R148891 : Reach 148891 := rs (se 1 (by rfl) ⟨111668, by rfl⟩) R223337
theorem R378283 : Reach 378283 := rs (se 1 (by rfl) ⟨283712, by rfl⟩) R567425
theorem R149215 : Reach 149215 := rs (se 1 (by rfl) ⟨111911, by rfl⟩) R223823
theorem R280381 : Reach 280381 := rs (se 3 (by rfl) ⟨52571, by rfl⟩) R105143
theorem R149647 : Reach 149647 := rs (se 1 (by rfl) ⟨112235, by rfl⟩) R224471
theorem R805727 : Reach 805727 := rs (se 1 (by rfl) ⟨604295, by rfl⟩) R1208591
theorem R510893 : Reach 510893 := rs (se 3 (by rfl) ⟨95792, by rfl⟩) R191585
theorem R248795 : Reach 248795 := rs (se 1 (by rfl) ⟨186596, by rfl⟩) R373193
theorem R150599 : Reach 150599 := rs (se 1 (by rfl) ⟨112949, by rfl⟩) R225899
theorem R117983 : Reach 117983 := rs (se 1 (by rfl) ⟨88487, by rfl⟩) R176975
theorem R281843 : Reach 281843 := rs (se 1 (by rfl) ⟨211382, by rfl⟩) R422765
theorem R151031 : Reach 151031 := rs (se 1 (by rfl) ⟨113273, by rfl⟩) R226547
theorem R446147 : Reach 446147 := rs (se 1 (by rfl) ⟨334610, by rfl⟩) R669221
theorem R2445203 : Reach 2445203 := rs (se 1 (by rfl) ⟨1833902, by rfl⟩) R3667805
theorem R315373 : Reach 315373 := rs (se 3 (by rfl) ⟨59132, by rfl⟩) R118265
theorem R249979 : Reach 249979 := rs (se 1 (by rfl) ⟨187484, by rfl⟩) R374969
theorem R1724723 : Reach 1724723 := rs (se 1 (by rfl) ⟨1293542, by rfl⟩) R2587085
theorem R152057 : Reach 152057 := rs (se 2 (by rfl) ⟨57021, by rfl⟩) R114043
theorem R479933 : Reach 479933 := rs (se 3 (by rfl) ⟨89987, by rfl⟩) R179975
theorem R152327 : Reach 152327 := rs (se 1 (by rfl) ⟨114245, by rfl⟩) R228491
theorem R414505 : Reach 414505 := rs (se 2 (by rfl) ⟨155439, by rfl⟩) R310879
theorem R87247 : Reach 87247 := rs (se 1 (by rfl) ⟨65435, by rfl⟩) R130871
theorem R513377 : Reach 513377 := rs (se 2 (by rfl) ⟨192516, by rfl⟩) R385033
theorem R87451 : Reach 87451 := rs (se 1 (by rfl) ⟨65588, by rfl⟩) R131177
theorem R87663 : Reach 87663 := rs (se 1 (by rfl) ⟨65747, by rfl⟩) R131495
theorem R87719 : Reach 87719 := rs (se 1 (by rfl) ⟨65789, by rfl⟩) R131579
theorem R87803 : Reach 87803 := rs (se 1 (by rfl) ⟨65852, by rfl⟩) R131705
theorem R87839 : Reach 87839 := rs (se 1 (by rfl) ⟨65879, by rfl⟩) R131759
theorem R87871 : Reach 87871 := rs (se 1 (by rfl) ⟨65903, by rfl⟩) R131807
theorem R251711 : Reach 251711 := rs (se 1 (by rfl) ⟨188783, by rfl⟩) R377567
theorem R153407 : Reach 153407 := rs (se 1 (by rfl) ⟨115055, by rfl⟩) R230111
theorem R153481 : Reach 153481 := rs (se 2 (by rfl) ⟨57555, by rfl⟩) R115111
theorem R284573 : Reach 284573 := rs (se 3 (by rfl) ⟨53357, by rfl⟩) R106715
theorem R2414551 : Reach 2414551 := rs (se 1 (by rfl) ⟨1810913, by rfl⟩) R3621827
theorem R88047 : Reach 88047 := rs (se 1 (by rfl) ⟨66035, by rfl⟩) R132071
theorem R153593 : Reach 153593 := rs (se 2 (by rfl) ⟨57597, by rfl⟩) R115195
theorem R88219 : Reach 88219 := rs (se 1 (by rfl) ⟨66164, by rfl⟩) R132329
theorem R88255 : Reach 88255 := rs (se 1 (by rfl) ⟨66191, by rfl⟩) R132383
theorem R88367 : Reach 88367 := rs (se 1 (by rfl) ⟨66275, by rfl⟩) R132551
theorem R252283 : Reach 252283 := rs (se 1 (by rfl) ⟨189212, by rfl⟩) R378425
theorem R88603 : Reach 88603 := rs (se 1 (by rfl) ⟨66452, by rfl⟩) R132905
theorem R88607 : Reach 88607 := rs (se 1 (by rfl) ⟨66455, by rfl⟩) R132911
theorem R252553 : Reach 252553 := rs (se 2 (by rfl) ⟨94707, by rfl⟩) R189415
theorem R121481 : Reach 121481 := rs (se 2 (by rfl) ⟨45555, by rfl⟩) R91111
theorem R88923 : Reach 88923 := rs (se 1 (by rfl) ⟨66692, by rfl⟩) R133385
theorem R88991 : Reach 88991 := rs (se 1 (by rfl) ⟨66743, by rfl⟩) R133487
theorem R89135 : Reach 89135 := rs (se 1 (by rfl) ⟨66851, by rfl⟩) R133703
theorem R89159 : Reach 89159 := rs (se 1 (by rfl) ⟨66869, by rfl⟩) R133739
theorem R89311 : Reach 89311 := rs (se 1 (by rfl) ⟨66983, by rfl⟩) R133967
theorem R154847 : Reach 154847 := rs (se 1 (by rfl) ⟨116135, by rfl⟩) R232271
theorem R220583 : Reach 220583 := rs (se 1 (by rfl) ⟨165437, by rfl⟩) R330875
theorem R89575 : Reach 89575 := rs (se 1 (by rfl) ⟨67181, by rfl⟩) R134363
theorem R89691 : Reach 89691 := rs (se 1 (by rfl) ⟨67268, by rfl⟩) R134537
theorem R11951887 : Reach 11951887 := rs (se 1 (by rfl) ⟨8963915, by rfl⟩) R17927831
theorem R450359 : Reach 450359 := rs (se 1 (by rfl) ⟨337769, by rfl⟩) R675539
theorem R89927 : Reach 89927 := rs (se 1 (by rfl) ⟨67445, by rfl⟩) R134891
theorem R90079 : Reach 90079 := rs (se 1 (by rfl) ⟨67559, by rfl⟩) R135119
theorem R254171 : Reach 254171 := rs (se 1 (by rfl) ⟨190628, by rfl⟩) R381257
theorem R90343 : Reach 90343 := rs (se 1 (by rfl) ⟨67757, by rfl⟩) R135515
theorem R581879 : Reach 581879 := rs (se 1 (by rfl) ⟨436409, by rfl⟩) R872819
theorem R90495 : Reach 90495 := rs (se 1 (by rfl) ⟨67871, by rfl⟩) R135743
theorem R90575 : Reach 90575 := rs (se 1 (by rfl) ⟨67931, by rfl⟩) R135863
theorem R90727 : Reach 90727 := rs (se 1 (by rfl) ⟨68045, by rfl⟩) R136091
theorem R287545 : Reach 287545 := rs (se 2 (by rfl) ⟨107829, by rfl⟩) R215659
theorem R90991 : Reach 90991 := rs (se 1 (by rfl) ⟨68243, by rfl⟩) R136487
theorem R91047 : Reach 91047 := rs (se 1 (by rfl) ⟨68285, by rfl⟩) R136571
theorem R157153 : Reach 157153 := rs (se 2 (by rfl) ⟨58932, by rfl⟩) R117865
theorem R288377 : Reach 288377 := rs (se 2 (by rfl) ⟨108141, by rfl⟩) R216283
theorem R288479 : Reach 288479 := rs (se 1 (by rfl) ⟨216359, by rfl⟩) R432719
theorem R223175 : Reach 223175 := rs (se 1 (by rfl) ⟨167381, by rfl⟩) R334763
theorem R452627 : Reach 452627 := rs (se 1 (by rfl) ⟨339470, by rfl⟩) R678941
theorem R1206353 : Reach 1206353 := rs (se 2 (by rfl) ⟨452382, by rfl⟩) R904765
theorem R518683 : Reach 518683 := rs (se 1 (by rfl) ⟨389012, by rfl⟩) R778025
theorem R584263 : Reach 584263 := rs (se 1 (by rfl) ⟨438197, by rfl⟩) R876395
theorem R387767 : Reach 387767 := rs (se 1 (by rfl) ⟨290825, by rfl⟩) R581651
theorem R256699 : Reach 256699 := rs (se 1 (by rfl) ⟨192524, by rfl⟩) R385049
theorem R158689 : Reach 158689 := rs (se 2 (by rfl) ⟨59508, by rfl⟩) R119017
theorem R749047 : Reach 749047 := rs (se 1 (by rfl) ⟨561785, by rfl⟩) R1123571
theorem R126527 : Reach 126527 := rs (se 1 (by rfl) ⟨94895, by rfl⟩) R189791
theorem R192107 : Reach 192107 := rs (se 1 (by rfl) ⟨144080, by rfl⟩) R288161
theorem R290479 : Reach 290479 := rs (se 1 (by rfl) ⟨217859, by rfl⟩) R435719
theorem R126841 : Reach 126841 := rs (se 2 (by rfl) ⟨47565, by rfl⟩) R95131
theorem R323837 : Reach 323837 := rs (se 3 (by rfl) ⟨60719, by rfl⟩) R121439
theorem R4452889 : Reach 4452889 := rs (se 2 (by rfl) ⟨1669833, by rfl⟩) R3339667
theorem R488521 : Reach 488521 := rs (se 2 (by rfl) ⟨183195, by rfl⟩) R366391
theorem R193747 : Reach 193747 := rs (se 1 (by rfl) ⟨145310, by rfl⟩) R290621
theorem R1504655 : Reach 1504655 := rs (se 1 (by rfl) ⟨1128491, by rfl⟩) R2256983
theorem R128623 : Reach 128623 := rs (se 1 (by rfl) ⟨96467, by rfl⟩) R192935
theorem R226999 : Reach 226999 := rs (se 1 (by rfl) ⟨170249, by rfl⟩) R340499
theorem R128999 : Reach 128999 := rs (se 1 (by rfl) ⟨96749, by rfl⟩) R193499
theorem R489577 : Reach 489577 := rs (se 2 (by rfl) ⟨183591, by rfl⟩) R367183
theorem R294137 : Reach 294137 := rs (se 2 (by rfl) ⟨110301, by rfl⟩) R220603
theorem R294407 : Reach 294407 := rs (se 1 (by rfl) ⟨220805, by rfl⟩) R441611
theorem R229007 : Reach 229007 := rs (se 1 (by rfl) ⟨171755, by rfl⟩) R343511
theorem R130793 : Reach 130793 := rs (se 2 (by rfl) ⟨49047, by rfl⟩) R98095
theorem R196343 : Reach 196343 := rs (se 1 (by rfl) ⟨147257, by rfl⟩) R294515
theorem R130937 : Reach 130937 := rs (se 2 (by rfl) ⟨49101, by rfl⟩) R98203
theorem R458621 : Reach 458621 := rs (se 3 (by rfl) ⟨85991, by rfl⟩) R171983
theorem R196523 : Reach 196523 := rs (se 1 (by rfl) ⟨147392, by rfl⟩) R294785
theorem R131039 : Reach 131039 := rs (se 1 (by rfl) ⟨98279, by rfl⟩) R196559
theorem R131375 : Reach 131375 := rs (se 1 (by rfl) ⟨98531, by rfl⟩) R197063
theorem R196991 : Reach 196991 := rs (se 1 (by rfl) ⟨147743, by rfl⟩) R295487
theorem R426455 : Reach 426455 := rs (se 1 (by rfl) ⟨319841, by rfl⟩) R639683
theorem R131615 : Reach 131615 := rs (se 1 (by rfl) ⟨98711, by rfl⟩) R197423
theorem R197225 : Reach 197225 := rs (se 2 (by rfl) ⟨73959, by rfl⟩) R147919
theorem R229999 : Reach 229999 := rs (se 1 (by rfl) ⟨172499, by rfl⟩) R344999
theorem R99103 : Reach 99103 := rs (se 1 (by rfl) ⟨74327, by rfl⟩) R148655
theorem R132287 : Reach 132287 := rs (se 1 (by rfl) ⟨99215, by rfl⟩) R198431
theorem R197855 : Reach 197855 := rs (se 1 (by rfl) ⟨148391, by rfl⟩) R296783
theorem R460079 : Reach 460079 := rs (se 1 (by rfl) ⟨345059, by rfl⟩) R690119
theorem R132431 : Reach 132431 := rs (se 1 (by rfl) ⟨99323, by rfl⟩) R198647
theorem R132521 : Reach 132521 := rs (se 2 (by rfl) ⟨49695, by rfl⟩) R99391
theorem R198071 : Reach 198071 := rs (se 1 (by rfl) ⟨148553, by rfl⟩) R297107
theorem R132671 : Reach 132671 := rs (se 1 (by rfl) ⟨99503, by rfl⟩) R199007
theorem R132713 : Reach 132713 := rs (se 2 (by rfl) ⟨49767, by rfl⟩) R99535
theorem R198251 : Reach 198251 := rs (se 1 (by rfl) ⟨148688, by rfl⟩) R297377
theorem R919259 : Reach 919259 := rs (se 1 (by rfl) ⟨689444, by rfl⟩) R1378889
theorem R198521 : Reach 198521 := rs (se 2 (by rfl) ⟨74445, by rfl⟩) R148891
theorem R329615 : Reach 329615 := rs (se 1 (by rfl) ⟨247211, by rfl⟩) R494423
theorem R165863 : Reach 165863 := rs (se 1 (by rfl) ⟨124397, by rfl⟩) R248795
theorem R133151 : Reach 133151 := rs (se 1 (by rfl) ⟨99863, by rfl⟩) R199727
theorem R100399 : Reach 100399 := rs (se 1 (by rfl) ⟨75299, by rfl⟩) R150599
theorem R133343 : Reach 133343 := rs (se 1 (by rfl) ⟨100007, by rfl⟩) R200015
theorem R133403 : Reach 133403 := rs (se 1 (by rfl) ⟨100052, by rfl⟩) R200105
theorem R198953 : Reach 198953 := rs (se 2 (by rfl) ⟨74607, by rfl⟩) R149215
theorem R3180869 : Reach 3180869 := rs (se 4 (by rfl) ⟨298206, by rfl⟩) R596413
theorem R100687 : Reach 100687 := rs (se 1 (by rfl) ⟨75515, by rfl⟩) R151031
theorem R297431 : Reach 297431 := rs (se 1 (by rfl) ⟨223073, by rfl⟩) R446147
theorem R854491 : Reach 854491 := rs (se 1 (by rfl) ⟨640868, by rfl⟩) R1281737
theorem R133727 : Reach 133727 := rs (se 1 (by rfl) ⟨100295, by rfl⟩) R200591
theorem R199529 : Reach 199529 := rs (se 2 (by rfl) ⟨74823, by rfl⟩) R149647
theorem R1149815 : Reach 1149815 := rs (se 1 (by rfl) ⟨862361, by rfl⟩) R1724723
theorem R134009 : Reach 134009 := rs (se 2 (by rfl) ⟨50253, by rfl⟩) R100507
theorem R199583 : Reach 199583 := rs (se 1 (by rfl) ⟨149687, by rfl⟩) R299375
theorem R134057 : Reach 134057 := rs (se 2 (by rfl) ⟨50271, by rfl⟩) R100543
theorem R101371 : Reach 101371 := rs (se 1 (by rfl) ⟨76028, by rfl⟩) R152057
theorem R134207 : Reach 134207 := rs (se 1 (by rfl) ⟨100655, by rfl⟩) R201311
theorem R101551 : Reach 101551 := rs (se 1 (by rfl) ⟨76163, by rfl⟩) R152327
theorem R691577 : Reach 691577 := rs (se 2 (by rfl) ⟨259341, by rfl⟩) R518683
theorem R134759 : Reach 134759 := rs (se 1 (by rfl) ⟨101069, by rfl⟩) R202139
theorem R200519 : Reach 200519 := rs (se 1 (by rfl) ⟨150389, by rfl⟩) R300779
theorem R167807 : Reach 167807 := rs (se 1 (by rfl) ⟨125855, by rfl⟩) R251711
theorem R102271 : Reach 102271 := rs (se 1 (by rfl) ⟨76703, by rfl⟩) R153407
theorem R135143 : Reach 135143 := rs (se 1 (by rfl) ⟨101357, by rfl⟩) R202715
theorem R200699 : Reach 200699 := rs (se 1 (by rfl) ⟨150524, by rfl⟩) R301049
theorem R102395 : Reach 102395 := rs (se 1 (by rfl) ⟨76796, by rfl⟩) R153593
theorem R135263 : Reach 135263 := rs (se 1 (by rfl) ⟨101447, by rfl⟩) R202895
theorem R200807 : Reach 200807 := rs (se 1 (by rfl) ⟨150605, by rfl⟩) R301211
theorem R135275 : Reach 135275 := rs (se 1 (by rfl) ⟨101456, by rfl⟩) R202913
theorem R135323 : Reach 135323 := rs (se 1 (by rfl) ⟨101492, by rfl⟩) R202985
theorem R200879 : Reach 200879 := rs (se 1 (by rfl) ⟨150659, by rfl⟩) R301319
theorem R103231 : Reach 103231 := rs (se 1 (by rfl) ⟨77423, by rfl⟩) R154847
theorem R201563 : Reach 201563 := rs (se 1 (by rfl) ⟨151172, by rfl⟩) R302345
theorem R136175 : Reach 136175 := rs (se 1 (by rfl) ⟨102131, by rfl⟩) R204263
theorem R169121 : Reach 169121 := rs (se 2 (by rfl) ⟨63420, by rfl⟩) R126841
theorem R300239 : Reach 300239 := rs (se 1 (by rfl) ⟨225179, by rfl⟩) R450359
theorem R136559 : Reach 136559 := rs (se 1 (by rfl) ⟨102419, by rfl⟩) R204839
theorem R169447 : Reach 169447 := rs (se 1 (by rfl) ⟨127085, by rfl⟩) R254171
theorem R136679 : Reach 136679 := rs (se 1 (by rfl) ⟨102509, by rfl⟩) R205019
theorem R333305 : Reach 333305 := rs (se 2 (by rfl) ⟨124989, by rfl⟩) R249979
theorem R3216941 : Reach 3216941 := rs (se 3 (by rfl) ⟨603176, by rfl⟩) R1206353
theorem R202319 : Reach 202319 := rs (se 1 (by rfl) ⟨151739, by rfl⟩) R303479
theorem R5937185 : Reach 5937185 := rs (se 2 (by rfl) ⟨2226444, by rfl⟩) R4452889
theorem R203039 : Reach 203039 := rs (se 1 (by rfl) ⟨152279, by rfl⟩) R304559
theorem R203239 : Reach 203239 := rs (se 1 (by rfl) ⟨152429, by rfl⟩) R304859
theorem R203291 : Reach 203291 := rs (se 1 (by rfl) ⟨152468, by rfl⟩) R304937
theorem R301751 : Reach 301751 := rs (se 1 (by rfl) ⟨226313, by rfl⟩) R452627
theorem R335279 : Reach 335279 := rs (se 1 (by rfl) ⟨251459, by rfl⟩) R502919
theorem R171497 : Reach 171497 := rs (se 2 (by rfl) ⟨64311, by rfl⟩) R128623
theorem R302665 : Reach 302665 := rs (se 2 (by rfl) ⟨113499, by rfl⟩) R226999
theorem R204641 : Reach 204641 := rs (se 2 (by rfl) ⟨76740, by rfl⟩) R153481
theorem R3219401 : Reach 3219401 := rs (se 2 (by rfl) ⟨1207275, by rfl⟩) R2414551
theorem R204767 : Reach 204767 := rs (se 1 (by rfl) ⟨153575, by rfl⟩) R307151
theorem R2072753 : Reach 2072753 := rs (se 2 (by rfl) ⟨777282, by rfl⟩) R1554565
theorem R663875 : Reach 663875 := rs (se 1 (by rfl) ⟨497906, by rfl⟩) R995813
theorem R336377 : Reach 336377 := rs (se 2 (by rfl) ⟨126141, by rfl⟩) R252283
theorem R336737 : Reach 336737 := rs (se 2 (by rfl) ⟨126276, by rfl⟩) R252553
theorem R337405 : Reach 337405 := rs (se 3 (by rfl) ⟨63263, by rfl⟩) R126527
theorem R764153 : Reach 764153 := rs (se 2 (by rfl) ⟨286557, by rfl⟩) R573115
theorem R15935849 : Reach 15935849 := rs (se 2 (by rfl) ⟨5975943, by rfl⟩) R11951887
theorem R305747 : Reach 305747 := rs (se 1 (by rfl) ⟨229310, by rfl⟩) R458621
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R764903 : Reach 764903 := rs (se 1 (by rfl) ⟨573677, by rfl⟩) R1147355
theorem R569015 : Reach 569015 := rs (se 1 (by rfl) ⟨426761, by rfl⟩) R853523
theorem R569065 : Reach 569065 := rs (se 2 (by rfl) ⟨213399, by rfl⟩) R426799
theorem R306935 : Reach 306935 := rs (se 1 (by rfl) ⟨230201, by rfl⟩) R460403
theorem R307475 : Reach 307475 := rs (se 1 (by rfl) ⟨230606, by rfl⟩) R461213
theorem R504377 : Reach 504377 := rs (se 2 (by rfl) ⟨189141, by rfl⟩) R378283
theorem R340595 : Reach 340595 := rs (se 1 (by rfl) ⟨255446, by rfl⟩) R510893
theorem R209537 : Reach 209537 := rs (se 2 (by rfl) ⟨78576, by rfl⟩) R157153
theorem R373567 : Reach 373567 := rs (se 1 (by rfl) ⟨280175, by rfl⟩) R560351
theorem R373841 : Reach 373841 := rs (se 2 (by rfl) ⟨140190, by rfl⟩) R280381
theorem R144649 : Reach 144649 := rs (se 2 (by rfl) ⟨54243, by rfl⟩) R108487
theorem R1095277 : Reach 1095277 := rs (se 3 (by rfl) ⟨205364, by rfl⟩) R410729
theorem R570989 : Reach 570989 := rs (se 3 (by rfl) ⟨107060, by rfl⟩) R214121
theorem R112367 : Reach 112367 := rs (se 1 (by rfl) ⟨84275, by rfl⟩) R168551
theorem R506087 : Reach 506087 := rs (se 1 (by rfl) ⟨379565, by rfl⟩) R759131
theorem R342251 : Reach 342251 := rs (se 1 (by rfl) ⟨256688, by rfl⟩) R513377
theorem R342265 : Reach 342265 := rs (se 2 (by rfl) ⟨128349, by rfl⟩) R256699
theorem R211585 : Reach 211585 := rs (se 2 (by rfl) ⟨79344, by rfl⟩) R158689
theorem R441449 : Reach 441449 := rs (se 2 (by rfl) ⟨165543, by rfl⟩) R331087
theorem R769277 : Reach 769277 := rs (se 3 (by rfl) ⟨144239, by rfl⟩) R288479
theorem R998729 : Reach 998729 := rs (se 2 (by rfl) ⟨374523, by rfl⟩) R749047
theorem R147055 : Reach 147055 := rs (se 1 (by rfl) ⟨110291, by rfl⟩) R220583
theorem R179887 : Reach 179887 := rs (se 1 (by rfl) ⟨134915, by rfl⟩) R269831
theorem R343997 : Reach 343997 := rs (se 3 (by rfl) ⟨64499, by rfl⟩) R128999
theorem R1851569 : Reach 1851569 := rs (se 2 (by rfl) ⟨694338, by rfl⟩) R1388677
theorem R377531 : Reach 377531 := rs (se 1 (by rfl) ⟨283148, by rfl⟩) R566297
theorem R1688363 : Reach 1688363 := rs (se 1 (by rfl) ⟨1266272, by rfl⟩) R2532545
theorem R508751 : Reach 508751 := rs (se 1 (by rfl) ⟨381563, by rfl⟩) R763127
theorem R148783 : Reach 148783 := rs (se 1 (by rfl) ⟨111587, by rfl⟩) R223175
theorem R116015 : Reach 116015 := rs (se 1 (by rfl) ⟨87011, by rfl⟩) R174023
theorem R1295797 : Reach 1295797 := rs (se 5 (by rfl) ⟨60740, by rfl⟩) R121481
theorem R2148605 : Reach 2148605 := rs (se 3 (by rfl) ⟨402863, by rfl⟩) R805727
theorem R969083 : Reach 969083 := rs (se 1 (by rfl) ⟨726812, by rfl⟩) R1453625
theorem R1952261 : Reach 1952261 := rs (se 4 (by rfl) ⟨183024, by rfl⟩) R366049
theorem R215891 : Reach 215891 := rs (se 1 (by rfl) ⟨161918, by rfl⟩) R323837
theorem R314621 : Reach 314621 := rs (se 3 (by rfl) ⟨58991, by rfl⟩) R117983
theorem R1003103 : Reach 1003103 := rs (se 1 (by rfl) ⟨752327, by rfl⟩) R1504655
theorem R249911 : Reach 249911 := rs (se 1 (by rfl) ⟨187433, by rfl⟩) R374867
theorem R380983 : Reach 380983 := rs (se 1 (by rfl) ⟨285737, by rfl⟩) R571475
theorem R250867 : Reach 250867 := rs (se 1 (by rfl) ⟨188150, by rfl⟩) R376301
theorem R152671 : Reach 152671 := rs (se 1 (by rfl) ⟨114503, by rfl⟩) R229007
theorem R775291 : Reach 775291 := rs (se 1 (by rfl) ⟨581468, by rfl⟩) R1162937
theorem R87195 : Reach 87195 := rs (se 1 (by rfl) ⟨65396, by rfl⟩) R130793
theorem R87291 : Reach 87291 := rs (se 1 (by rfl) ⟨65468, by rfl⟩) R130937
theorem R87359 : Reach 87359 := rs (se 1 (by rfl) ⟨65519, by rfl⟩) R131039
theorem R382315 : Reach 382315 := rs (se 1 (by rfl) ⟨286736, by rfl⟩) R573473
theorem R87527 : Reach 87527 := rs (se 1 (by rfl) ⟨65645, by rfl⟩) R131291
theorem R120295 : Reach 120295 := rs (se 1 (by rfl) ⟨90221, by rfl⟩) R180443
theorem R87535 : Reach 87535 := rs (se 1 (by rfl) ⟨65651, by rfl⟩) R131303
theorem R349679 : Reach 349679 := rs (se 1 (by rfl) ⟨262259, by rfl⟩) R524519
theorem R87643 : Reach 87643 := rs (se 1 (by rfl) ⟨65732, by rfl⟩) R131465
theorem R87707 : Reach 87707 := rs (se 1 (by rfl) ⟨65780, by rfl⟩) R131561
theorem R87791 : Reach 87791 := rs (se 1 (by rfl) ⟨65843, by rfl⟩) R131687
theorem R87879 : Reach 87879 := rs (se 1 (by rfl) ⟨65909, by rfl⟩) R131819
theorem R87899 : Reach 87899 := rs (se 1 (by rfl) ⟨65924, by rfl⟩) R131849
theorem R87967 : Reach 87967 := rs (se 1 (by rfl) ⟨65975, by rfl⟩) R131951
theorem R350171 : Reach 350171 := rs (se 1 (by rfl) ⟨262628, by rfl⟩) R525257
theorem R88135 : Reach 88135 := rs (se 1 (by rfl) ⟨66101, by rfl⟩) R132203
theorem R841913 : Reach 841913 := rs (se 2 (by rfl) ⟨315717, by rfl⟩) R631435
theorem R88295 : Reach 88295 := rs (se 1 (by rfl) ⟨66221, by rfl⟩) R132443
theorem R88479 : Reach 88479 := rs (se 1 (by rfl) ⟨66359, by rfl⟩) R132719
theorem R383393 : Reach 383393 := rs (se 2 (by rfl) ⟨143772, by rfl⟩) R287545
theorem R88527 : Reach 88527 := rs (se 1 (by rfl) ⟨66395, by rfl⟩) R132791
theorem R88551 : Reach 88551 := rs (se 1 (by rfl) ⟨66413, by rfl⟩) R132827
theorem R88667 : Reach 88667 := rs (se 1 (by rfl) ⟨66500, by rfl⟩) R133001
theorem R88735 : Reach 88735 := rs (se 1 (by rfl) ⟨66551, by rfl⟩) R133103
theorem R88903 : Reach 88903 := rs (se 1 (by rfl) ⟨66677, by rfl⟩) R133355
theorem R88943 : Reach 88943 := rs (se 1 (by rfl) ⟨66707, by rfl⟩) R133415
theorem R88999 : Reach 88999 := rs (se 1 (by rfl) ⟨66749, by rfl⟩) R133499
theorem R482311 : Reach 482311 := rs (se 1 (by rfl) ⟨361733, by rfl⟩) R723467
theorem R89179 : Reach 89179 := rs (se 1 (by rfl) ⟨66884, by rfl⟩) R133769
theorem R1006769 : Reach 1006769 := rs (se 2 (by rfl) ⟨377538, by rfl⟩) R755077
theorem R89295 : Reach 89295 := rs (se 1 (by rfl) ⟨66971, by rfl⟩) R133943
theorem R89319 : Reach 89319 := rs (se 1 (by rfl) ⟨66989, by rfl⟩) R133979
theorem R89415 : Reach 89415 := rs (se 1 (by rfl) ⟨67061, by rfl⟩) R134123
theorem R384365 : Reach 384365 := rs (se 3 (by rfl) ⟨72068, by rfl⟩) R144137
theorem R89551 : Reach 89551 := rs (se 1 (by rfl) ⟨67163, by rfl⟩) R134327
theorem R187895 : Reach 187895 := rs (se 1 (by rfl) ⟨140921, by rfl⟩) R281843
theorem R89711 : Reach 89711 := rs (se 1 (by rfl) ⟨67283, by rfl⟩) R134567
theorem R89767 : Reach 89767 := rs (se 1 (by rfl) ⟨67325, by rfl⟩) R134651
theorem R89831 : Reach 89831 := rs (se 1 (by rfl) ⟨67373, by rfl⟩) R134747
theorem R89887 : Reach 89887 := rs (se 1 (by rfl) ⟨67415, by rfl⟩) R134831
theorem R89967 : Reach 89967 := rs (se 1 (by rfl) ⟨67475, by rfl⟩) R134951
theorem R221039 : Reach 221039 := rs (se 1 (by rfl) ⟨165779, by rfl⟩) R331559
theorem R90023 : Reach 90023 := rs (se 1 (by rfl) ⟨67517, by rfl⟩) R135035
theorem R1630135 : Reach 1630135 := rs (se 1 (by rfl) ⟨1222601, by rfl⟩) R2445203
theorem R1466435 : Reach 1466435 := rs (se 1 (by rfl) ⟨1099826, by rfl⟩) R2199653
theorem R90303 : Reach 90303 := rs (se 1 (by rfl) ⟨67727, by rfl⟩) R135455
theorem R90319 : Reach 90319 := rs (se 1 (by rfl) ⟨67739, by rfl⟩) R135479
theorem R90367 : Reach 90367 := rs (se 1 (by rfl) ⟨67775, by rfl⟩) R135551
theorem R450845 : Reach 450845 := rs (se 3 (by rfl) ⟨84533, by rfl⟩) R169067
theorem R90415 : Reach 90415 := rs (se 1 (by rfl) ⟨67811, by rfl⟩) R135623
theorem R680399 : Reach 680399 := rs (se 1 (by rfl) ⟨510299, by rfl⟩) R1020599
theorem R319955 : Reach 319955 := rs (se 1 (by rfl) ⟨239966, by rfl⟩) R479933
theorem R90651 : Reach 90651 := rs (se 1 (by rfl) ⟨67988, by rfl⟩) R135977
theorem R90655 : Reach 90655 := rs (se 1 (by rfl) ⟨67991, by rfl⟩) R135983
theorem R90735 : Reach 90735 := rs (se 1 (by rfl) ⟨68051, by rfl⟩) R136103
theorem R90791 : Reach 90791 := rs (se 1 (by rfl) ⟨68093, by rfl⟩) R136187
theorem R90831 : Reach 90831 := rs (se 1 (by rfl) ⟨68123, by rfl⟩) R136247
theorem R779017 : Reach 779017 := rs (se 2 (by rfl) ⟨292131, by rfl⟩) R584263
theorem R90911 : Reach 90911 := rs (se 1 (by rfl) ⟨68183, by rfl⟩) R136367
theorem R1532951 : Reach 1532951 := rs (se 1 (by rfl) ⟨1149713, by rfl⟩) R2299427
theorem R189715 : Reach 189715 := rs (se 1 (by rfl) ⟨142286, by rfl⟩) R284573
theorem R1008935 : Reach 1008935 := rs (se 1 (by rfl) ⟨756701, by rfl⟩) R1513403
theorem R1402181 : Reach 1402181 := rs (se 4 (by rfl) ⟨131454, by rfl⟩) R262909
theorem R91675 : Reach 91675 := rs (se 1 (by rfl) ⟨68756, by rfl⟩) R137513
theorem R1238813 : Reach 1238813 := rs (se 3 (by rfl) ⟨232277, by rfl⟩) R464555
theorem R223195 : Reach 223195 := rs (se 1 (by rfl) ⟨167396, by rfl⟩) R334793
theorem R387305 : Reach 387305 := rs (se 2 (by rfl) ⟨145239, by rfl⟩) R290479
theorem R289295 : Reach 289295 := rs (se 1 (by rfl) ⟨216971, by rfl⟩) R433943
theorem R420497 : Reach 420497 := rs (se 2 (by rfl) ⟨157686, by rfl⟩) R315373
theorem R387919 : Reach 387919 := rs (se 1 (by rfl) ⟨290939, by rfl⟩) R581879
theorem R224329 : Reach 224329 := rs (se 2 (by rfl) ⟨84123, by rfl⟩) R168247
theorem R552673 : Reach 552673 := rs (se 2 (by rfl) ⟨207252, by rfl⟩) R414505
theorem R192251 : Reach 192251 := rs (se 1 (by rfl) ⟨144188, by rfl⟩) R288377
theorem R487417 : Reach 487417 := rs (se 2 (by rfl) ⟨182781, by rfl⟩) R365563
theorem R651361 : Reach 651361 := rs (se 2 (by rfl) ⟨244260, by rfl⟩) R488521
theorem R258329 : Reach 258329 := rs (se 2 (by rfl) ⟨96873, by rfl⟩) R193747
theorem R258511 : Reach 258511 := rs (se 1 (by rfl) ⟨193883, by rfl⟩) R387767
theorem R422495 : Reach 422495 := rs (se 1 (by rfl) ⟨316871, by rfl⟩) R633743
theorem R128071 : Reach 128071 := rs (se 1 (by rfl) ⟨96053, by rfl⟩) R192107
theorem R619987 : Reach 619987 := rs (se 1 (by rfl) ⟨464990, by rfl⟩) R929981
theorem R652769 : Reach 652769 := rs (se 2 (by rfl) ⟨244788, by rfl⟩) R489577
theorem R2717873 : Reach 2717873 := rs (se 2 (by rfl) ⟨1019202, by rfl⟩) R2038405
theorem R457001 : Reach 457001 := rs (se 2 (by rfl) ⟨171375, by rfl⟩) R342751
theorem R424399 : Reach 424399 := rs (se 1 (by rfl) ⟨318299, by rfl⟩) R636599
theorem R97147 : Reach 97147 := rs (se 1 (by rfl) ⟨72860, by rfl⟩) R145721
theorem R850985 : Reach 850985 := rs (se 2 (by rfl) ⟨319119, by rfl⟩) R638239
theorem R2522501 : Reach 2522501 := rs (se 4 (by rfl) ⟨236484, by rfl⟩) R472969
theorem R228815 : Reach 228815 := rs (se 1 (by rfl) ⟨171611, by rfl⟩) R343223
theorem R163279 : Reach 163279 := rs (se 1 (by rfl) ⟨122459, by rfl⟩) R244919
theorem R196091 : Reach 196091 := rs (se 1 (by rfl) ⟨147068, by rfl⟩) R294137
theorem R196271 : Reach 196271 := rs (se 1 (by rfl) ⟨147203, by rfl⟩) R294407
theorem R98023 : Reach 98023 := rs (se 1 (by rfl) ⟨73517, by rfl⟩) R147035
theorem R196361 : Reach 196361 := rs (se 2 (by rfl) ⟨73635, by rfl⟩) R147271
theorem R130895 : Reach 130895 := rs (se 1 (by rfl) ⟨98171, by rfl⟩) R196343
theorem R131015 : Reach 131015 := rs (se 1 (by rfl) ⟨98261, by rfl⟩) R196523
theorem R131327 : Reach 131327 := rs (se 1 (by rfl) ⟨98495, by rfl⟩) R196991
theorem R131483 : Reach 131483 := rs (se 1 (by rfl) ⟨98612, by rfl⟩) R197225
theorem R131903 : Reach 131903 := rs (se 1 (by rfl) ⟨98927, by rfl⟩) R197855
theorem R132047 : Reach 132047 := rs (se 1 (by rfl) ⟨99035, by rfl⟩) R198071
theorem R132137 : Reach 132137 := rs (se 2 (by rfl) ⟨49551, by rfl⟩) R99103
theorem R132167 : Reach 132167 := rs (se 1 (by rfl) ⟨99125, by rfl⟩) R198251
theorem R853213 : Reach 853213 := rs (se 3 (by rfl) ⟨159977, by rfl⟩) R319955
theorem R132347 : Reach 132347 := rs (se 1 (by rfl) ⟨99260, by rfl⟩) R198521
theorem R132635 : Reach 132635 := rs (se 1 (by rfl) ⟨99476, by rfl⟩) R198953
theorem R198287 : Reach 198287 := rs (se 1 (by rfl) ⟨148715, by rfl⟩) R297431
theorem R198377 : Reach 198377 := rs (se 2 (by rfl) ⟨74391, by rfl⟩) R148783
theorem R133019 : Reach 133019 := rs (se 1 (by rfl) ⟨99764, by rfl⟩) R199529
theorem R133055 : Reach 133055 := rs (se 1 (by rfl) ⟨99791, by rfl⟩) R199583
theorem R461051 : Reach 461051 := rs (se 1 (by rfl) ⟨345788, by rfl⟩) R691577
theorem R1083941 : Reach 1083941 := rs (se 4 (by rfl) ⟨101619, by rfl⟩) R203239
theorem R133679 : Reach 133679 := rs (se 1 (by rfl) ⟨100259, by rfl⟩) R200519
theorem R297593 : Reach 297593 := rs (se 2 (by rfl) ⟨111597, by rfl⟩) R223195
theorem R133799 : Reach 133799 := rs (se 1 (by rfl) ⟨100349, by rfl⟩) R200699
theorem R166607 : Reach 166607 := rs (se 1 (by rfl) ⟨124955, by rfl⟩) R249911
theorem R133865 : Reach 133865 := rs (se 2 (by rfl) ⟨50199, by rfl⟩) R100399
theorem R133871 : Reach 133871 := rs (se 1 (by rfl) ⟨100403, by rfl⟩) R200807
theorem R133919 : Reach 133919 := rs (se 1 (by rfl) ⟨100439, by rfl⟩) R200879
theorem R134249 : Reach 134249 := rs (se 2 (by rfl) ⟨50343, by rfl⟩) R100687
theorem R134375 : Reach 134375 := rs (se 1 (by rfl) ⟨100781, by rfl⟩) R201563
theorem R200159 : Reach 200159 := rs (se 1 (by rfl) ⟨150119, by rfl⟩) R300239
theorem R233119 : Reach 233119 := rs (se 1 (by rfl) ⟨174839, by rfl⟩) R349679
theorem R134879 : Reach 134879 := rs (se 1 (by rfl) ⟨101159, by rfl⟩) R202319
theorem R233447 : Reach 233447 := rs (se 1 (by rfl) ⟨175085, by rfl⟩) R350171
theorem R135161 : Reach 135161 := rs (se 2 (by rfl) ⟨50685, by rfl⟩) R101371
theorem R299105 : Reach 299105 := rs (se 2 (by rfl) ⟨112164, by rfl⟩) R224329
theorem R561275 : Reach 561275 := rs (se 1 (by rfl) ⟨420956, by rfl⟩) R841913
theorem R135359 : Reach 135359 := rs (se 1 (by rfl) ⟨101519, by rfl⟩) R203039
theorem R135401 : Reach 135401 := rs (se 2 (by rfl) ⟨50775, by rfl⟩) R101551
theorem R135527 : Reach 135527 := rs (se 1 (by rfl) ⟨101645, by rfl⟩) R203291
theorem R201167 : Reach 201167 := rs (se 1 (by rfl) ⟨150875, by rfl⟩) R301751
theorem R299645 : Reach 299645 := rs (se 3 (by rfl) ⟨56183, by rfl⟩) R112367
theorem R758753 : Reach 758753 := rs (se 2 (by rfl) ⟨284532, by rfl⟩) R569065
theorem R136361 : Reach 136361 := rs (se 2 (by rfl) ⟨51135, by rfl⟩) R102271
theorem R136427 : Reach 136427 := rs (se 1 (by rfl) ⟨102320, by rfl⟩) R204641
theorem R136511 : Reach 136511 := rs (se 1 (by rfl) ⟨102383, by rfl⟩) R204767
theorem R15832493 : Reach 15832493 := rs (se 3 (by rfl) ⟨2968592, by rfl⟩) R5937185
theorem R1381835 : Reach 1381835 := rs (se 1 (by rfl) ⟨1036376, by rfl⟩) R2072753
theorem R300563 : Reach 300563 := rs (se 1 (by rfl) ⟨225422, by rfl⟩) R450845
theorem R1021967 : Reach 1021967 := rs (se 1 (by rfl) ⟨766475, by rfl⟩) R1532951
theorem R498089 : Reach 498089 := rs (se 2 (by rfl) ⟨186783, by rfl⟩) R373567
theorem R137641 : Reach 137641 := rs (se 2 (by rfl) ⟨51615, by rfl⟩) R103231
theorem R825875 : Reach 825875 := rs (se 1 (by rfl) ⟨619406, by rfl⟩) R1238813
theorem R334489 : Reach 334489 := rs (se 2 (by rfl) ⟨125433, by rfl⟩) R250867
theorem R170761 : Reach 170761 := rs (se 2 (by rfl) ⟨64035, by rfl⟩) R128071
theorem R203561 : Reach 203561 := rs (se 2 (by rfl) ⟨76335, by rfl⟩) R152671
theorem R10623899 : Reach 10623899 := rs (se 1 (by rfl) ⟨7967924, by rfl⟩) R15935849
theorem R203831 : Reach 203831 := rs (se 1 (by rfl) ⟨152873, by rfl⟩) R305747
theorem R826649 : Reach 826649 := rs (se 2 (by rfl) ⟨309993, by rfl⟩) R619987
theorem R204623 : Reach 204623 := rs (se 1 (by rfl) ⟨153467, by rfl⟩) R306935
theorem R204983 : Reach 204983 := rs (se 1 (by rfl) ⟨153737, by rfl⟩) R307475
theorem R172219 : Reach 172219 := rs (se 1 (by rfl) ⟨129164, by rfl⟩) R258329
theorem R336251 : Reach 336251 := rs (se 1 (by rfl) ⟨252188, by rfl⟩) R504377
theorem R139691 : Reach 139691 := rs (se 1 (by rfl) ⟨104768, by rfl⟩) R209537
theorem R565865 : Reach 565865 := rs (se 2 (by rfl) ⟨212199, by rfl⟩) R424399
theorem R1024973 : Reach 1024973 := rs (se 3 (by rfl) ⟨192182, by rfl⟩) R384365
theorem R435179 : Reach 435179 := rs (se 1 (by rfl) ⟨326384, by rfl⟩) R652769
theorem R1811915 : Reach 1811915 := rs (se 1 (by rfl) ⟨1358936, by rfl⟩) R2717873
theorem R337391 : Reach 337391 := rs (se 1 (by rfl) ⟨253043, by rfl⟩) R506087
theorem R304667 : Reach 304667 := rs (se 1 (by rfl) ⟨228500, by rfl⟩) R457001
theorem R567323 : Reach 567323 := rs (se 1 (by rfl) ⟨425492, by rfl⟩) R850985
theorem R403553 : Reach 403553 := rs (se 2 (by rfl) ⟨151332, by rfl⟩) R302665
theorem R665819 : Reach 665819 := rs (se 1 (by rfl) ⟨499364, by rfl⟩) R998729
theorem R239849 : Reach 239849 := rs (se 2 (by rfl) ⟨89943, by rfl⟩) R179887
theorem R1681667 : Reach 1681667 := rs (se 1 (by rfl) ⟨1261250, by rfl⟩) R2522501
theorem R2173513 : Reach 2173513 := rs (se 2 (by rfl) ⟨815067, by rfl⟩) R1630135
theorem R273053 : Reach 273053 := rs (se 3 (by rfl) ⟨51197, by rfl⟩) R102395
theorem R3910493 : Reach 3910493 := rs (se 3 (by rfl) ⟨733217, by rfl⟩) R1466435
theorem R1125575 : Reach 1125575 := rs (se 1 (by rfl) ⟨844181, by rfl⟩) R1688363
theorem R339167 : Reach 339167 := rs (se 1 (by rfl) ⟨254375, by rfl⟩) R508751
theorem R306665 : Reach 306665 := rs (se 2 (by rfl) ⟨114999, by rfl⟩) R229999
theorem R306719 : Reach 306719 := rs (se 1 (by rfl) ⟨230039, by rfl⟩) R460079
theorem R110575 : Reach 110575 := rs (se 1 (by rfl) ⟨82931, by rfl⟩) R165863
theorem R143927 : Reach 143927 := rs (se 1 (by rfl) ⟨107945, by rfl⟩) R215891
theorem R766543 : Reach 766543 := rs (se 1 (by rfl) ⟨574907, by rfl⟩) R1149815
theorem R209747 : Reach 209747 := rs (se 1 (by rfl) ⟨157310, by rfl⟩) R314621
theorem R668735 : Reach 668735 := rs (se 1 (by rfl) ⟨501551, by rfl⟩) R1003103
theorem R111871 : Reach 111871 := rs (se 1 (by rfl) ⟨83903, by rfl⟩) R167807
theorem R14956597 : Reach 14956597 := rs (se 5 (by rfl) ⟨701090, by rfl⟩) R1402181
theorem R112747 : Reach 112747 := rs (se 1 (by rfl) ⟨84560, by rfl⟩) R169121
theorem R2144627 : Reach 2144627 := rs (se 1 (by rfl) ⟨1608470, by rfl⟩) R3216941
theorem R671179 : Reach 671179 := rs (se 1 (by rfl) ⟨503384, by rfl⟩) R1006769
theorem R736897 : Reach 736897 := rs (se 2 (by rfl) ⟨276336, by rfl⟩) R552673
theorem R147359 : Reach 147359 := rs (se 1 (by rfl) ⟨110519, by rfl⟩) R221039
theorem R2146267 : Reach 2146267 := rs (se 1 (by rfl) ⟨1609700, by rfl⟩) R3219401
theorem R507977 : Reach 507977 := rs (se 2 (by rfl) ⟨190491, by rfl⟩) R380983
theorem R868481 : Reach 868481 := rs (se 2 (by rfl) ⟨325680, by rfl⟩) R651361
theorem R442583 : Reach 442583 := rs (se 1 (by rfl) ⟨331937, by rfl⟩) R663875
theorem R344681 : Reach 344681 := rs (se 2 (by rfl) ⟨129255, by rfl⟩) R258511
theorem R672623 : Reach 672623 := rs (se 1 (by rfl) ⟨504467, by rfl⟩) R1008935
theorem R771461 : Reach 771461 := rs (se 4 (by rfl) ⟨72324, by rfl⟩) R144649
theorem R1033721 : Reach 1033721 := rs (se 2 (by rfl) ⟨387645, by rfl⟩) R775291
theorem R509435 : Reach 509435 := rs (se 1 (by rfl) ⟨382076, by rfl⟩) R764153
theorem R280331 : Reach 280331 := rs (se 1 (by rfl) ⟨210248, by rfl⟩) R420497
theorem R509753 : Reach 509753 := rs (se 2 (by rfl) ⟨191157, by rfl⟩) R382315
theorem R509935 : Reach 509935 := rs (se 1 (by rfl) ⟨382451, by rfl⟩) R764903
theorem R1460369 : Reach 1460369 := rs (se 2 (by rfl) ⟨547638, by rfl⟩) R1095277
theorem R870821 : Reach 870821 := rs (se 4 (by rfl) ⟨81639, by rfl⟩) R163279
theorem R379343 : Reach 379343 := rs (se 1 (by rfl) ⟨284507, by rfl⟩) R569015
theorem R281663 : Reach 281663 := rs (se 1 (by rfl) ⟨211247, by rfl⟩) R422495
theorem R249227 : Reach 249227 := rs (se 1 (by rfl) ⟨186920, by rfl⟩) R373841
theorem R282113 : Reach 282113 := rs (se 2 (by rfl) ⟨105792, by rfl⟩) R211585
theorem R380659 : Reach 380659 := rs (se 1 (by rfl) ⟨285494, by rfl⟩) R570989
theorem R643081 : Reach 643081 := rs (se 2 (by rfl) ⟨241155, by rfl⟩) R482311
theorem R512669 : Reach 512669 := rs (se 3 (by rfl) ⟨96125, by rfl⟩) R192251
theorem R512851 : Reach 512851 := rs (se 1 (by rfl) ⟨384638, by rfl⟩) R769277
theorem R152543 : Reach 152543 := rs (se 1 (by rfl) ⟨114407, by rfl⟩) R228815
theorem R87263 : Reach 87263 := rs (se 1 (by rfl) ⟨65447, by rfl⟩) R130895
theorem R87343 : Reach 87343 := rs (se 1 (by rfl) ⟨65507, by rfl⟩) R131015
theorem R1234379 : Reach 1234379 := rs (se 1 (by rfl) ⟨925784, by rfl⟩) R1851569
theorem R87583 : Reach 87583 := rs (se 1 (by rfl) ⟨65687, by rfl⟩) R131375
theorem R284303 : Reach 284303 := rs (se 1 (by rfl) ⟨213227, by rfl⟩) R426455
theorem R87743 : Reach 87743 := rs (se 1 (by rfl) ⟨65807, by rfl⟩) R131615
theorem R251687 : Reach 251687 := rs (se 1 (by rfl) ⟨188765, by rfl⟩) R377531
theorem R88191 : Reach 88191 := rs (se 1 (by rfl) ⟨66143, by rfl⟩) R132287
theorem R88287 : Reach 88287 := rs (se 1 (by rfl) ⟨66215, by rfl⟩) R132431
theorem R88347 : Reach 88347 := rs (se 1 (by rfl) ⟨66260, by rfl⟩) R132521
theorem R1038689 : Reach 1038689 := rs (se 2 (by rfl) ⟨389508, by rfl⟩) R779017
theorem R88447 : Reach 88447 := rs (se 1 (by rfl) ⟨66335, by rfl⟩) R132671
theorem R88475 : Reach 88475 := rs (se 1 (by rfl) ⟨66356, by rfl⟩) R132713
theorem R612839 : Reach 612839 := rs (se 1 (by rfl) ⟨459629, by rfl⟩) R919259
theorem R219743 : Reach 219743 := rs (se 1 (by rfl) ⟨164807, by rfl⟩) R329615
theorem R88767 : Reach 88767 := rs (se 1 (by rfl) ⟨66575, by rfl⟩) R133151
theorem R88895 : Reach 88895 := rs (se 1 (by rfl) ⟨66671, by rfl⟩) R133343
theorem R1432403 : Reach 1432403 := rs (se 1 (by rfl) ⟨1074302, by rfl⟩) R2148605
theorem R88935 : Reach 88935 := rs (se 1 (by rfl) ⟨66701, by rfl⟩) R133403
theorem R2120579 : Reach 2120579 := rs (se 1 (by rfl) ⟨1590434, by rfl⟩) R3180869
theorem R646055 : Reach 646055 := rs (se 1 (by rfl) ⟨484541, by rfl⟩) R969083
theorem R1301507 : Reach 1301507 := rs (se 1 (by rfl) ⟨976130, by rfl⟩) R1952261
theorem R252953 : Reach 252953 := rs (se 2 (by rfl) ⟨94857, by rfl⟩) R189715
theorem R89151 : Reach 89151 := rs (se 1 (by rfl) ⟨66863, by rfl⟩) R133727
theorem R1727729 : Reach 1727729 := rs (se 2 (by rfl) ⟨647898, by rfl⟩) R1295797
theorem R89339 : Reach 89339 := rs (se 1 (by rfl) ⟨67004, by rfl⟩) R134009
theorem R89371 : Reach 89371 := rs (se 1 (by rfl) ⟨67028, by rfl⟩) R134057
theorem R449873 : Reach 449873 := rs (se 2 (by rfl) ⟨168702, by rfl⟩) R337405
theorem R122233 : Reach 122233 := rs (se 2 (by rfl) ⟨45837, by rfl⟩) R91675
theorem R89471 : Reach 89471 := rs (se 1 (by rfl) ⟨67103, by rfl⟩) R134207
theorem R89839 : Reach 89839 := rs (se 1 (by rfl) ⟨67379, by rfl⟩) R134759
theorem R90095 : Reach 90095 := rs (se 1 (by rfl) ⟨67571, by rfl⟩) R135143
theorem R90175 : Reach 90175 := rs (se 1 (by rfl) ⟨67631, by rfl⟩) R135263
theorem R90183 : Reach 90183 := rs (se 1 (by rfl) ⟨67637, by rfl⟩) R135275
theorem R90215 : Reach 90215 := rs (se 1 (by rfl) ⟨67661, by rfl⟩) R135323
theorem R1237493 : Reach 1237493 := rs (se 5 (by rfl) ⟨58007, by rfl⟩) R116015
theorem R1139321 : Reach 1139321 := rs (se 2 (by rfl) ⟨427245, by rfl⟩) R854491
theorem R90783 : Reach 90783 := rs (se 1 (by rfl) ⟨68087, by rfl⟩) R136175
theorem R91039 : Reach 91039 := rs (se 1 (by rfl) ⟨68279, by rfl⟩) R136559
theorem R91119 : Reach 91119 := rs (se 1 (by rfl) ⟨68339, by rfl⟩) R136679
theorem R222203 : Reach 222203 := rs (se 1 (by rfl) ⟨166652, by rfl⟩) R333305
theorem R517225 : Reach 517225 := rs (se 2 (by rfl) ⟨193959, by rfl⟩) R387919
theorem R255595 : Reach 255595 := rs (se 1 (by rfl) ⟨191696, by rfl⟩) R383393
theorem R223519 : Reach 223519 := rs (se 1 (by rfl) ⟨167639, by rfl⟩) R335279
theorem R125263 : Reach 125263 := rs (se 1 (by rfl) ⟨93947, by rfl⟩) R187895
theorem R649889 : Reach 649889 := rs (se 2 (by rfl) ⟨243708, by rfl⟩) R487417
theorem R453599 : Reach 453599 := rs (se 1 (by rfl) ⟨340199, by rfl⟩) R680399
theorem R224251 : Reach 224251 := rs (se 1 (by rfl) ⟨168188, by rfl⟩) R336377
theorem R224491 : Reach 224491 := rs (se 1 (by rfl) ⟨168368, by rfl⟩) R336737
theorem R258203 : Reach 258203 := rs (se 1 (by rfl) ⟨193652, by rfl⟩) R387305
theorem R192863 : Reach 192863 := rs (se 1 (by rfl) ⟨144647, by rfl⟩) R289295
theorem R160393 : Reach 160393 := rs (se 2 (by rfl) ⟨60147, by rfl⟩) R120295
theorem R225929 : Reach 225929 := rs (se 2 (by rfl) ⟨84723, by rfl⟩) R169447
theorem R553661 : Reach 553661 := rs (se 3 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R456353 : Reach 456353 := rs (se 2 (by rfl) ⟨171132, by rfl⟩) R342265
theorem R227063 : Reach 227063 := rs (se 1 (by rfl) ⟨170297, by rfl⟩) R340595
theorem R129529 : Reach 129529 := rs (se 2 (by rfl) ⟨48573, by rfl⟩) R97147
theorem R457325 : Reach 457325 := rs (se 3 (by rfl) ⟨85748, by rfl⟩) R171497
theorem R228167 : Reach 228167 := rs (se 1 (by rfl) ⟨171125, by rfl⟩) R342251
theorem R294299 : Reach 294299 := rs (se 1 (by rfl) ⟨220724, by rfl⟩) R441449
theorem R196073 : Reach 196073 := rs (se 2 (by rfl) ⟨73527, by rfl⟩) R147055
theorem R130697 : Reach 130697 := rs (se 2 (by rfl) ⟨49011, by rfl⟩) R98023
theorem R130727 : Reach 130727 := rs (se 1 (by rfl) ⟨98045, by rfl⟩) R196091
theorem R130847 : Reach 130847 := rs (se 1 (by rfl) ⟨98135, by rfl⟩) R196271
theorem R130907 : Reach 130907 := rs (se 1 (by rfl) ⟨98180, by rfl⟩) R196361
theorem R229331 : Reach 229331 := rs (se 1 (by rfl) ⟨171998, by rfl⟩) R343997
theorem R295055 : Reach 295055 := rs (se 1 (by rfl) ⟨221291, by rfl⟩) R442583
theorem R229625 : Reach 229625 := rs (se 2 (by rfl) ⟨86109, by rfl⟩) R172219
theorem R229787 : Reach 229787 := rs (se 1 (by rfl) ⟨172340, by rfl⟩) R344681
theorem R689147 : Reach 689147 := rs (se 1 (by rfl) ⟨516860, by rfl⟩) R1033721
theorem R132191 : Reach 132191 := rs (se 1 (by rfl) ⟨99143, by rfl⟩) R198287
theorem R132251 : Reach 132251 := rs (se 1 (by rfl) ⟨99188, by rfl⟩) R198377
theorem R689633 : Reach 689633 := rs (se 2 (by rfl) ⟨258612, by rfl⟩) R517225
theorem R722627 : Reach 722627 := rs (se 1 (by rfl) ⟨541970, by rfl⟩) R1083941
theorem R198395 : Reach 198395 := rs (se 1 (by rfl) ⟨148796, by rfl⟩) R297593
theorem R559325 : Reach 559325 := rs (se 3 (by rfl) ⟨104873, by rfl⟩) R209747
theorem R166151 : Reach 166151 := rs (se 1 (by rfl) ⟨124613, by rfl⟩) R249227
theorem R133439 : Reach 133439 := rs (se 1 (by rfl) ⟨100079, by rfl⟩) R200159
theorem R199403 : Reach 199403 := rs (se 1 (by rfl) ⟨149552, by rfl⟩) R299105
theorem R134111 : Reach 134111 := rs (se 1 (by rfl) ⟨100583, by rfl⟩) R201167
theorem R298025 : Reach 298025 := rs (se 2 (by rfl) ⟨111759, by rfl⟩) R223519
theorem R199763 : Reach 199763 := rs (se 1 (by rfl) ⟨149822, by rfl⟩) R299645
theorem R167017 : Reach 167017 := rs (se 2 (by rfl) ⟨62631, by rfl⟩) R125263
theorem R101695 : Reach 101695 := rs (se 1 (by rfl) ⟨76271, by rfl⟩) R152543
theorem R10554995 : Reach 10554995 := rs (se 1 (by rfl) ⟨7916246, by rfl⟩) R15832493
theorem R921223 : Reach 921223 := rs (se 1 (by rfl) ⟨690917, by rfl⟩) R1381835
theorem R200375 : Reach 200375 := rs (se 1 (by rfl) ⟨150281, by rfl⟩) R300563
theorem R692459 : Reach 692459 := rs (se 1 (by rfl) ⟨519344, by rfl⟩) R1038689
theorem R332059 : Reach 332059 := rs (se 1 (by rfl) ⟨249044, by rfl⟩) R498089
theorem R299321 : Reach 299321 := rs (se 2 (by rfl) ⟨112245, by rfl⟩) R224491
theorem R135707 : Reach 135707 := rs (se 1 (by rfl) ⟨101780, by rfl⟩) R203561
theorem R954935 : Reach 954935 := rs (se 1 (by rfl) ⟨716201, by rfl⟩) R1432403
theorem R1413719 : Reach 1413719 := rs (se 1 (by rfl) ⟨1060289, by rfl⟩) R2120579
theorem R7082599 : Reach 7082599 := rs (se 1 (by rfl) ⟨5311949, by rfl⟩) R10623899
theorem R430703 : Reach 430703 := rs (se 1 (by rfl) ⟨323027, by rfl⟩) R646055
theorem R168635 : Reach 168635 := rs (se 1 (by rfl) ⟨126476, by rfl⟩) R252953
theorem R135887 : Reach 135887 := rs (se 1 (by rfl) ⟨101915, by rfl⟩) R203831
theorem R1151819 : Reach 1151819 := rs (se 1 (by rfl) ⟨863864, by rfl⟩) R1727729
theorem R299915 : Reach 299915 := rs (se 1 (by rfl) ⟨224936, by rfl⟩) R449873
theorem R136415 : Reach 136415 := rs (se 1 (by rfl) ⟨102311, by rfl⟩) R204623
theorem R857441 : Reach 857441 := rs (se 2 (by rfl) ⟨321540, by rfl⟩) R643081
theorem R136655 : Reach 136655 := rs (se 1 (by rfl) ⟨102491, by rfl⟩) R204983
theorem R824995 : Reach 824995 := rs (se 1 (by rfl) ⟨618746, by rfl⟩) R1237493
theorem R759547 : Reach 759547 := rs (se 1 (by rfl) ⟨569660, by rfl⟩) R1139321
theorem R1022057 : Reach 1022057 := rs (se 2 (by rfl) ⟨383271, by rfl⟩) R766543
theorem R203111 : Reach 203111 := rs (se 1 (by rfl) ⟨152333, by rfl⟩) R304667
theorem R1121111 : Reach 1121111 := rs (se 1 (by rfl) ⟨840833, by rfl⟩) R1681667
theorem R433259 : Reach 433259 := rs (se 1 (by rfl) ⟨324944, by rfl⟩) R649889
theorem R302399 : Reach 302399 := rs (se 1 (by rfl) ⟨226799, by rfl⟩) R453599
theorem R204443 : Reach 204443 := rs (se 1 (by rfl) ⟨153332, by rfl⟩) R306665
theorem R204479 : Reach 204479 := rs (se 1 (by rfl) ⟨153359, by rfl⟩) R306719
theorem R172135 : Reach 172135 := rs (se 1 (by rfl) ⟨129101, by rfl⟩) R258203
theorem R369107 : Reach 369107 := rs (se 1 (by rfl) ⟨276830, by rfl⟩) R553661
theorem R172705 : Reach 172705 := rs (se 2 (by rfl) ⟨64764, by rfl⟩) R129529
theorem R304235 : Reach 304235 := rs (se 1 (by rfl) ⟨228176, by rfl⟩) R456353
theorem R304883 : Reach 304883 := rs (se 1 (by rfl) ⟨228662, by rfl⟩) R457325
theorem R894905 : Reach 894905 := rs (se 2 (by rfl) ⟨335589, by rfl⟩) R671179
theorem R2861689 : Reach 2861689 := rs (se 2 (by rfl) ⟨1073133, by rfl⟩) R2146267
theorem R338651 : Reach 338651 := rs (se 1 (by rfl) ⟨253988, by rfl⟩) R507977
theorem R339623 : Reach 339623 := rs (se 1 (by rfl) ⟨254717, by rfl⟩) R509435
theorem R372509 : Reach 372509 := rs (se 3 (by rfl) ⟨69845, by rfl⟩) R139691
theorem R339835 : Reach 339835 := rs (se 1 (by rfl) ⟨254876, by rfl⟩) R509753
theorem R307367 : Reach 307367 := rs (se 1 (by rfl) ⟨230525, by rfl⟩) R461051
theorem R111071 : Reach 111071 := rs (se 1 (by rfl) ⟨83303, by rfl⟩) R166607
theorem R340793 : Reach 340793 := rs (se 2 (by rfl) ⟨127797, by rfl⟩) R255595
theorem R1160477 : Reach 1160477 := rs (se 3 (by rfl) ⟨217589, by rfl⟩) R435179
theorem R374183 : Reach 374183 := rs (se 1 (by rfl) ⟨280637, by rfl⟩) R561275
theorem R341779 : Reach 341779 := rs (se 1 (by rfl) ⟨256334, by rfl⟩) R512669
theorem R505835 : Reach 505835 := rs (se 1 (by rfl) ⟨379376, by rfl⟩) R758753
theorem R2898017 : Reach 2898017 := rs (se 2 (by rfl) ⟨1086756, by rfl⟩) R2173513
theorem R3291677 : Reach 3291677 := rs (se 3 (by rfl) ⟨617189, by rfl⟩) R1234379
theorem R408559 : Reach 408559 := rs (se 1 (by rfl) ⟨306419, by rfl⟩) R612839
theorem R146495 : Reach 146495 := rs (se 1 (by rfl) ⟨109871, by rfl⟩) R219743
theorem R867671 : Reach 867671 := rs (se 1 (by rfl) ⟨650753, by rfl⟩) R1301507
theorem R671165 : Reach 671165 := rs (se 3 (by rfl) ⟨125843, by rfl⟩) R251687
theorem R310825 : Reach 310825 := rs (se 2 (by rfl) ⟨116559, by rfl⟩) R233119
theorem R507545 : Reach 507545 := rs (se 2 (by rfl) ⟨190329, by rfl⟩) R380659
theorem R1196005 : Reach 1196005 := rs (se 4 (by rfl) ⟨112125, by rfl⟩) R224251
theorem R147433 : Reach 147433 := rs (se 2 (by rfl) ⟨55287, by rfl⟩) R110575
theorem R377243 : Reach 377243 := rs (se 1 (by rfl) ⟨282932, by rfl⟩) R565865
theorem R148135 : Reach 148135 := rs (se 1 (by rfl) ⟨111101, by rfl⟩) R222203
theorem R213857 : Reach 213857 := rs (se 2 (by rfl) ⟨80196, by rfl⟩) R160393
theorem R378215 : Reach 378215 := rs (se 1 (by rfl) ⟨283661, by rfl⟩) R567323
theorem R443879 : Reach 443879 := rs (se 1 (by rfl) ⟨332909, by rfl⟩) R665819
theorem R149161 : Reach 149161 := rs (se 2 (by rfl) ⟨55935, by rfl⟩) R111871
theorem R182035 : Reach 182035 := rs (se 1 (by rfl) ⟨136526, by rfl⟩) R273053
theorem R2606995 : Reach 2606995 := rs (se 1 (by rfl) ⟨1955246, by rfl⟩) R3910493
theorem R19942129 : Reach 19942129 := rs (se 2 (by rfl) ⟨7478298, by rfl⟩) R14956597
theorem R150329 : Reach 150329 := rs (se 2 (by rfl) ⟨56373, by rfl⟩) R112747
theorem R150619 : Reach 150619 := rs (se 1 (by rfl) ⟨112964, by rfl⟩) R225929
theorem R183521 : Reach 183521 := rs (se 2 (by rfl) ⟨68820, by rfl⟩) R137641
theorem R445823 : Reach 445823 := rs (se 1 (by rfl) ⟨334367, by rfl⟩) R668735
theorem R445985 : Reach 445985 := rs (se 2 (by rfl) ⟨167244, by rfl⟩) R334489
theorem R151375 : Reach 151375 := rs (se 1 (by rfl) ⟨113531, by rfl⟩) R227063
theorem R1429751 : Reach 1429751 := rs (se 1 (by rfl) ⟨1072313, by rfl⟩) R2144627
theorem R152111 : Reach 152111 := rs (se 1 (by rfl) ⟨114083, by rfl⟩) R228167
theorem R87131 : Reach 87131 := rs (se 1 (by rfl) ⟨65348, by rfl⟩) R130697
theorem R87151 : Reach 87151 := rs (se 1 (by rfl) ⟨65363, by rfl⟩) R130727
theorem R87231 : Reach 87231 := rs (se 1 (by rfl) ⟨65423, by rfl⟩) R130847
theorem R87271 : Reach 87271 := rs (se 1 (by rfl) ⟨65453, by rfl⟩) R130907
theorem R152887 : Reach 152887 := rs (se 1 (by rfl) ⟨114665, by rfl⟩) R229331
theorem R578987 : Reach 578987 := rs (se 1 (by rfl) ⟨434240, by rfl⟩) R868481
theorem R87551 : Reach 87551 := rs (se 1 (by rfl) ⟨65663, by rfl⟩) R131327
theorem R87655 : Reach 87655 := rs (se 1 (by rfl) ⟨65741, by rfl⟩) R131483
theorem R87935 : Reach 87935 := rs (se 1 (by rfl) ⟨65951, by rfl⟩) R131903
theorem R448415 : Reach 448415 := rs (se 1 (by rfl) ⟨336311, by rfl⟩) R672623
theorem R88031 : Reach 88031 := rs (se 1 (by rfl) ⟨66023, by rfl⟩) R132047
theorem R88091 : Reach 88091 := rs (se 1 (by rfl) ⟨66068, by rfl⟩) R132137
theorem R88111 : Reach 88111 := rs (se 1 (by rfl) ⟨66083, by rfl⟩) R132167
theorem R88231 : Reach 88231 := rs (se 1 (by rfl) ⟨66173, by rfl⟩) R132347
theorem R514307 : Reach 514307 := rs (se 1 (by rfl) ⟨385730, by rfl⟩) R771461
theorem R88423 : Reach 88423 := rs (se 1 (by rfl) ⟨66317, by rfl⟩) R132635
theorem R186887 : Reach 186887 := rs (se 1 (by rfl) ⟨140165, by rfl⟩) R280331
theorem R88679 : Reach 88679 := rs (se 1 (by rfl) ⟨66509, by rfl⟩) R133019
theorem R88703 : Reach 88703 := rs (se 1 (by rfl) ⟨66527, by rfl⟩) R133055
theorem R580547 : Reach 580547 := rs (se 1 (by rfl) ⟨435410, by rfl⟩) R870821
theorem R1137617 : Reach 1137617 := rs (se 2 (by rfl) ⟨426606, by rfl⟩) R853213
theorem R252895 : Reach 252895 := rs (se 1 (by rfl) ⟨189671, by rfl⟩) R379343
theorem R89119 : Reach 89119 := rs (se 1 (by rfl) ⟨66839, by rfl⟩) R133679
theorem R89199 : Reach 89199 := rs (se 1 (by rfl) ⟨66899, by rfl⟩) R133799
theorem R89243 : Reach 89243 := rs (se 1 (by rfl) ⟨66932, by rfl⟩) R133865
theorem R89247 : Reach 89247 := rs (se 1 (by rfl) ⟨66935, by rfl⟩) R133871
theorem R89279 : Reach 89279 := rs (se 1 (by rfl) ⟨66959, by rfl⟩) R133919
theorem R187775 : Reach 187775 := rs (se 1 (by rfl) ⟨140831, by rfl⟩) R281663
theorem R89499 : Reach 89499 := rs (se 1 (by rfl) ⟨67124, by rfl⟩) R134249
theorem R89583 : Reach 89583 := rs (se 1 (by rfl) ⟨67187, by rfl⟩) R134375
theorem R188075 : Reach 188075 := rs (se 1 (by rfl) ⟨141056, by rfl⟩) R282113
theorem R89919 : Reach 89919 := rs (se 1 (by rfl) ⟨67439, by rfl⟩) R134879
theorem R679913 : Reach 679913 := rs (se 2 (by rfl) ⟨254967, by rfl⟩) R509935
theorem R90107 : Reach 90107 := rs (se 1 (by rfl) ⟨67580, by rfl⟩) R135161
theorem R90239 : Reach 90239 := rs (se 1 (by rfl) ⟨67679, by rfl⟩) R135359
theorem R90267 : Reach 90267 := rs (se 1 (by rfl) ⟨67700, by rfl⟩) R135401
theorem R90351 : Reach 90351 := rs (se 1 (by rfl) ⟨67763, by rfl⟩) R135527
theorem R90907 : Reach 90907 := rs (se 1 (by rfl) ⟨68180, by rfl⟩) R136361
theorem R90951 : Reach 90951 := rs (se 1 (by rfl) ⟨68213, by rfl⟩) R136427
theorem R91007 : Reach 91007 := rs (se 1 (by rfl) ⟨68255, by rfl⟩) R136511
theorem R189535 : Reach 189535 := rs (se 1 (by rfl) ⟨142151, by rfl⟩) R284303
theorem R681311 : Reach 681311 := rs (se 1 (by rfl) ⟨510983, by rfl⟩) R1021967
theorem R550583 : Reach 550583 := rs (se 1 (by rfl) ⟨412937, by rfl⟩) R825875
theorem R551099 : Reach 551099 := rs (se 1 (by rfl) ⟨413324, by rfl⟩) R826649
theorem R224167 : Reach 224167 := rs (se 1 (by rfl) ⟨168125, by rfl⟩) R336251
theorem R1076141 : Reach 1076141 := rs (se 3 (by rfl) ⟨201776, by rfl⟩) R403553
theorem R3894317 : Reach 3894317 := rs (se 3 (by rfl) ⟨730184, by rfl⟩) R1460369
theorem R683315 : Reach 683315 := rs (se 1 (by rfl) ⟨512486, by rfl⟩) R1024973
theorem R1207943 : Reach 1207943 := rs (se 1 (by rfl) ⟨905957, by rfl⟩) R1811915
theorem R224927 : Reach 224927 := rs (se 1 (by rfl) ⟨168695, by rfl⟩) R337391
theorem R683801 : Reach 683801 := rs (se 2 (by rfl) ⟨256425, by rfl⟩) R512851
theorem R159899 : Reach 159899 := rs (se 1 (by rfl) ⟨119924, by rfl⟩) R239849
theorem R750383 : Reach 750383 := rs (se 1 (by rfl) ⟨562787, by rfl⟩) R1125575
theorem R226111 : Reach 226111 := rs (se 1 (by rfl) ⟨169583, by rfl⟩) R339167
theorem R128575 : Reach 128575 := rs (se 1 (by rfl) ⟨96431, by rfl⟩) R192863
theorem R95951 : Reach 95951 := rs (se 1 (by rfl) ⟨71963, by rfl⟩) R143927
theorem R227681 : Reach 227681 := rs (se 2 (by rfl) ⟨85380, by rfl⟩) R170761
theorem R162977 : Reach 162977 := rs (se 2 (by rfl) ⟨61116, by rfl⟩) R122233
theorem R982529 : Reach 982529 := rs (se 2 (by rfl) ⟨368448, by rfl⟩) R736897
theorem R196199 : Reach 196199 := rs (se 1 (by rfl) ⟨147149, by rfl⟩) R294299
theorem R130715 : Reach 130715 := rs (se 1 (by rfl) ⟨98036, by rfl⟩) R196073
theorem R622525 : Reach 622525 := rs (se 3 (by rfl) ⟨116723, by rfl⟩) R233447
theorem R98239 : Reach 98239 := rs (se 1 (by rfl) ⟨73679, by rfl⟩) R147359
theorem R196703 : Reach 196703 := rs (se 1 (by rfl) ⟨147527, by rfl⟩) R295055
theorem R229513 : Reach 229513 := rs (se 2 (by rfl) ⟨86067, by rfl⟩) R172135
theorem R426397 : Reach 426397 := rs (se 3 (by rfl) ⟨79949, by rfl⟩) R159899
theorem R459431 : Reach 459431 := rs (se 1 (by rfl) ⟨344573, by rfl⟩) R689147
theorem R230273 : Reach 230273 := rs (se 2 (by rfl) ⟨86352, by rfl⟩) R172705
theorem R197513 : Reach 197513 := rs (se 2 (by rfl) ⟨74067, by rfl⟩) R148135
theorem R459755 : Reach 459755 := rs (se 1 (by rfl) ⟨344816, by rfl⟩) R689633
theorem R295919 : Reach 295919 := rs (se 1 (by rfl) ⟨221939, by rfl⟩) R443879
theorem R132263 : Reach 132263 := rs (se 1 (by rfl) ⟨99197, by rfl⟩) R198395
theorem R296189 : Reach 296189 := rs (se 3 (by rfl) ⟨55535, by rfl⟩) R111071
theorem R132935 : Reach 132935 := rs (se 1 (by rfl) ⟨99701, by rfl⟩) R199403
theorem R100219 : Reach 100219 := rs (se 1 (by rfl) ⟨75164, by rfl⟩) R150329
theorem R198683 : Reach 198683 := rs (se 1 (by rfl) ⟨149012, by rfl⟩) R298025
theorem R133175 : Reach 133175 := rs (se 1 (by rfl) ⟨99881, by rfl⟩) R199763
theorem R198881 : Reach 198881 := rs (se 2 (by rfl) ⟨74580, by rfl⟩) R149161
theorem R297215 : Reach 297215 := rs (se 1 (by rfl) ⟨222911, by rfl⟩) R445823
theorem R297323 : Reach 297323 := rs (se 1 (by rfl) ⟨222992, by rfl⟩) R445985
theorem R133583 : Reach 133583 := rs (se 1 (by rfl) ⟨100187, by rfl⟩) R200375
theorem R3475993 : Reach 3475993 := rs (se 2 (by rfl) ⟨1303497, by rfl⟩) R2606995
theorem R461639 : Reach 461639 := rs (se 1 (by rfl) ⟨346229, by rfl⟩) R692459
theorem R953167 : Reach 953167 := rs (se 1 (by rfl) ⟨714875, by rfl⟩) R1429751
theorem R199547 : Reach 199547 := rs (se 1 (by rfl) ⟨149660, by rfl⟩) R299321
theorem R101407 : Reach 101407 := rs (se 1 (by rfl) ⟨76055, by rfl⟩) R152111
theorem R199943 : Reach 199943 := rs (se 1 (by rfl) ⟨149957, by rfl⟩) R299915
theorem R298889 : Reach 298889 := rs (se 2 (by rfl) ⟨112083, by rfl⟩) R224167
theorem R298943 : Reach 298943 := rs (se 1 (by rfl) ⟨224207, by rfl⟩) R448415
theorem R200825 : Reach 200825 := rs (se 2 (by rfl) ⟨75309, by rfl⟩) R150619
theorem R135407 : Reach 135407 := rs (se 1 (by rfl) ⟨101555, by rfl⟩) R203111
theorem R135593 : Reach 135593 := rs (se 2 (by rfl) ⟨50847, by rfl⟩) R101695
theorem R758411 : Reach 758411 := rs (se 1 (by rfl) ⟨568808, by rfl⟩) R1137617
theorem R201599 : Reach 201599 := rs (se 1 (by rfl) ⟨151199, by rfl⟩) R302399
theorem R136295 : Reach 136295 := rs (se 1 (by rfl) ⟨102221, by rfl⟩) R204443
theorem R201833 : Reach 201833 := rs (se 2 (by rfl) ⟨75687, by rfl⟩) R151375
theorem R136319 : Reach 136319 := rs (se 1 (by rfl) ⟨102239, by rfl⟩) R204479
theorem R202823 : Reach 202823 := rs (se 1 (by rfl) ⟨152117, by rfl⟩) R304235
theorem R9443465 : Reach 9443465 := rs (se 2 (by rfl) ⟨3541299, by rfl⟩) R7082599
theorem R301481 : Reach 301481 := rs (se 2 (by rfl) ⟨113055, by rfl⟩) R226111
theorem R367055 : Reach 367055 := rs (se 1 (by rfl) ⟨275291, by rfl⟩) R550583
theorem R203255 : Reach 203255 := rs (se 1 (by rfl) ⟨152441, by rfl⟩) R304883
theorem R596603 : Reach 596603 := rs (se 1 (by rfl) ⟨447452, by rfl⟩) R894905
theorem R367399 : Reach 367399 := rs (se 1 (by rfl) ⟨275549, by rfl⟩) R551099
theorem R203849 : Reach 203849 := rs (se 2 (by rfl) ⟨76443, by rfl⟩) R152887
theorem R2596211 : Reach 2596211 := rs (se 1 (by rfl) ⟨1947158, by rfl⟩) R3894317
theorem R171433 : Reach 171433 := rs (se 2 (by rfl) ⟨64287, by rfl⟩) R128575
theorem R204911 : Reach 204911 := rs (se 1 (by rfl) ⟨153683, by rfl⟩) R307367
theorem R434605 : Reach 434605 := rs (se 3 (by rfl) ⟨81488, by rfl⟩) R162977
theorem R500255 : Reach 500255 := rs (se 1 (by rfl) ⟨375191, by rfl⟩) R750383
theorem R337193 : Reach 337193 := rs (se 2 (by rfl) ⟨126447, by rfl⟩) R252895
theorem R337223 : Reach 337223 := rs (se 1 (by rfl) ⟨252917, by rfl⟩) R505835
theorem R338363 : Reach 338363 := rs (se 1 (by rfl) ⟨253772, by rfl⟩) R507545
theorem R830033 : Reach 830033 := rs (se 2 (by rfl) ⟨311262, by rfl⟩) R622525
theorem R240637 : Reach 240637 := rs (se 3 (by rfl) ⟨45119, by rfl⟩) R90239
theorem R142571 : Reach 142571 := rs (se 1 (by rfl) ⟨106928, by rfl⟩) R213857
theorem R242713 : Reach 242713 := rs (se 2 (by rfl) ⟨91017, by rfl⟩) R182035
theorem R636623 : Reach 636623 := rs (se 1 (by rfl) ⟨477467, by rfl⟩) R954935
theorem R112423 : Reach 112423 := rs (se 1 (by rfl) ⟨84317, by rfl⟩) R168635
theorem R767879 : Reach 767879 := rs (se 1 (by rfl) ⟨575909, by rfl⟩) R1151819
theorem R3815585 : Reach 3815585 := rs (se 2 (by rfl) ⟨1430844, by rfl⟩) R2861689
theorem R571627 : Reach 571627 := rs (se 1 (by rfl) ⟨428720, by rfl⟩) R857441
theorem R1816829 : Reach 1816829 := rs (se 3 (by rfl) ⟨340655, by rfl⟩) R681311
theorem R26589505 : Reach 26589505 := rs (se 2 (by rfl) ⟨9971064, by rfl⟩) R19942129
theorem R1228297 : Reach 1228297 := rs (se 2 (by rfl) ⟨460611, by rfl⟩) R921223
theorem R246071 : Reach 246071 := rs (se 1 (by rfl) ⟨184553, by rfl⟩) R369107
theorem R442745 : Reach 442745 := rs (se 2 (by rfl) ⟨166029, by rfl⟩) R332059
theorem R1491533 : Reach 1491533 := rs (se 3 (by rfl) ⟨279662, by rfl⟩) R559325
theorem R443069 : Reach 443069 := rs (se 3 (by rfl) ⟨83075, by rfl⟩) R166151
theorem R1099993 : Reach 1099993 := rs (se 2 (by rfl) ⟨412497, by rfl⟩) R824995
theorem R805295 : Reach 805295 := rs (se 1 (by rfl) ⟨603971, by rfl⟩) R1207943
theorem R149951 : Reach 149951 := rs (se 1 (by rfl) ⟨112463, by rfl⟩) R224927
theorem R248339 : Reach 248339 := rs (se 1 (by rfl) ⟨186254, by rfl⟩) R372509
theorem R773651 : Reach 773651 := rs (se 1 (by rfl) ⟨580238, by rfl⟩) R1160477
theorem R249455 : Reach 249455 := rs (se 1 (by rfl) ⟨187091, by rfl⟩) R374183
theorem R4050917 : Reach 4050917 := rs (se 4 (by rfl) ⟨379773, by rfl⟩) R759547
theorem R544745 : Reach 544745 := rs (se 2 (by rfl) ⟨204279, by rfl⟩) R408559
theorem R151787 : Reach 151787 := rs (se 1 (by rfl) ⟨113840, by rfl⟩) R227681
theorem R414433 : Reach 414433 := rs (se 2 (by rfl) ⟨155412, by rfl⟩) R310825
theorem R578447 : Reach 578447 := rs (se 1 (by rfl) ⟨433835, by rfl⟩) R867671
theorem R447443 : Reach 447443 := rs (se 1 (by rfl) ⟨335582, by rfl⟩) R671165
theorem R87143 : Reach 87143 := rs (se 1 (by rfl) ⟨65357, by rfl⟩) R130715
theorem R1594673 : Reach 1594673 := rs (se 2 (by rfl) ⟨598002, by rfl⟩) R1196005
theorem R153083 : Reach 153083 := rs (se 1 (by rfl) ⟨114812, by rfl⟩) R229625
theorem R251495 : Reach 251495 := rs (se 1 (by rfl) ⟨188621, by rfl⟩) R377243
theorem R153191 : Reach 153191 := rs (se 1 (by rfl) ⟨114893, by rfl⟩) R229787
theorem R88127 : Reach 88127 := rs (se 1 (by rfl) ⟨66095, by rfl⟩) R132191
theorem R88167 : Reach 88167 := rs (se 1 (by rfl) ⟨66125, by rfl⟩) R132251
theorem R252143 : Reach 252143 := rs (se 1 (by rfl) ⟨189107, by rfl⟩) R378215
theorem R481751 : Reach 481751 := rs (se 1 (by rfl) ⟨361313, by rfl⟩) R722627
theorem R252713 : Reach 252713 := rs (se 2 (by rfl) ⟨94767, by rfl⟩) R189535
theorem R88959 : Reach 88959 := rs (se 1 (by rfl) ⟨66719, by rfl⟩) R133439
theorem R89407 : Reach 89407 := rs (se 1 (by rfl) ⟨67055, by rfl⟩) R134111
theorem R122347 : Reach 122347 := rs (se 1 (by rfl) ⟨91760, by rfl⟩) R183521
theorem R90471 : Reach 90471 := rs (se 1 (by rfl) ⟨67853, by rfl⟩) R135707
theorem R942479 : Reach 942479 := rs (se 1 (by rfl) ⟨706859, by rfl⟩) R1413719
theorem R287135 : Reach 287135 := rs (se 1 (by rfl) ⟨215351, by rfl⟩) R430703
theorem R90591 : Reach 90591 := rs (se 1 (by rfl) ⟨67943, by rfl⟩) R135887
theorem R90943 : Reach 90943 := rs (se 1 (by rfl) ⟨68207, by rfl⟩) R136415
theorem R385991 : Reach 385991 := rs (se 1 (by rfl) ⟨289493, by rfl⟩) R578987
theorem R91103 : Reach 91103 := rs (se 1 (by rfl) ⟨68327, by rfl⟩) R136655
theorem R681371 : Reach 681371 := rs (se 1 (by rfl) ⟨511028, by rfl⟩) R1022057
theorem R222689 : Reach 222689 := rs (se 2 (by rfl) ⟨83508, by rfl⟩) R167017
theorem R124591 : Reach 124591 := rs (se 1 (by rfl) ⟨93443, by rfl⟩) R186887
theorem R255869 : Reach 255869 := rs (se 3 (by rfl) ⟨47975, by rfl⟩) R95951
theorem R747407 : Reach 747407 := rs (se 1 (by rfl) ⟨560555, by rfl⟩) R1121111
theorem R387031 : Reach 387031 := rs (se 1 (by rfl) ⟨290273, by rfl⟩) R580547
theorem R288839 : Reach 288839 := rs (se 1 (by rfl) ⟨216629, by rfl⟩) R433259
theorem R125183 : Reach 125183 := rs (se 1 (by rfl) ⟨93887, by rfl⟩) R187775
theorem R125383 : Reach 125383 := rs (se 1 (by rfl) ⟨94037, by rfl⟩) R188075
theorem R453113 : Reach 453113 := rs (se 2 (by rfl) ⟨169917, by rfl⟩) R339835
theorem R453275 : Reach 453275 := rs (se 1 (by rfl) ⟨339956, by rfl⟩) R679913
theorem R1371485 : Reach 1371485 := rs (se 3 (by rfl) ⟨257153, by rfl⟩) R514307
theorem R225767 : Reach 225767 := rs (se 1 (by rfl) ⟨169325, by rfl⟩) R338651
theorem R717427 : Reach 717427 := rs (se 1 (by rfl) ⟨538070, by rfl⟩) R1076141
theorem R455543 : Reach 455543 := rs (se 1 (by rfl) ⟨341657, by rfl⟩) R683315
theorem R455705 : Reach 455705 := rs (se 2 (by rfl) ⟨170889, by rfl⟩) R341779
theorem R226415 : Reach 226415 := rs (se 1 (by rfl) ⟨169811, by rfl⟩) R339623
theorem R455867 : Reach 455867 := rs (se 1 (by rfl) ⟨341900, by rfl⟩) R683801
theorem R390653 : Reach 390653 := rs (se 3 (by rfl) ⟨73247, by rfl⟩) R146495
theorem R227195 : Reach 227195 := rs (se 1 (by rfl) ⟨170396, by rfl⟩) R340793
theorem R1932011 : Reach 1932011 := rs (se 1 (by rfl) ⟨1449008, by rfl⟩) R2898017
theorem R28146653 : Reach 28146653 := rs (se 3 (by rfl) ⟨5277497, by rfl⟩) R10554995
theorem R2194451 : Reach 2194451 := rs (se 1 (by rfl) ⟨1645838, by rfl⟩) R3291677
theorem R655019 : Reach 655019 := rs (se 1 (by rfl) ⟨491264, by rfl⟩) R982529
theorem R130799 : Reach 130799 := rs (se 1 (by rfl) ⟨98099, by rfl⟩) R196199
theorem R130985 : Reach 130985 := rs (se 2 (by rfl) ⟨49119, by rfl⟩) R98239
theorem R196577 : Reach 196577 := rs (se 2 (by rfl) ⟨73716, by rfl⟩) R147433
theorem R131135 : Reach 131135 := rs (se 1 (by rfl) ⟨98351, by rfl⟩) R196703
theorem R164047 : Reach 164047 := rs (se 1 (by rfl) ⟨123035, by rfl⟩) R246071
theorem R295163 : Reach 295163 := rs (se 1 (by rfl) ⟨221372, by rfl⟩) R442745
theorem R295379 : Reach 295379 := rs (se 1 (by rfl) ⟨221534, by rfl⟩) R443069
theorem R131675 : Reach 131675 := rs (se 1 (by rfl) ⟨98756, by rfl⟩) R197513
theorem R197279 : Reach 197279 := rs (se 1 (by rfl) ⟨147959, by rfl⟩) R295919
theorem R197459 : Reach 197459 := rs (se 1 (by rfl) ⟨148094, by rfl⟩) R296189
theorem R132455 : Reach 132455 := rs (se 1 (by rfl) ⟨99341, by rfl⟩) R198683
theorem R132587 : Reach 132587 := rs (se 1 (by rfl) ⟨99440, by rfl⟩) R198881
theorem R198143 : Reach 198143 := rs (se 1 (by rfl) ⟨148607, by rfl⟩) R297215
theorem R198215 : Reach 198215 := rs (se 1 (by rfl) ⟨148661, by rfl⟩) R297323
theorem R99967 : Reach 99967 := rs (se 1 (by rfl) ⟨74975, by rfl⟩) R149951
theorem R165559 : Reach 165559 := rs (se 1 (by rfl) ⟨124169, by rfl⟩) R248339
theorem R133031 : Reach 133031 := rs (se 1 (by rfl) ⟨99773, by rfl⟩) R199547
theorem R133295 : Reach 133295 := rs (se 1 (by rfl) ⟨99971, by rfl⟩) R199943
theorem R166121 : Reach 166121 := rs (se 2 (by rfl) ⟨62295, by rfl⟩) R124591
theorem R166303 : Reach 166303 := rs (se 1 (by rfl) ⟨124727, by rfl⟩) R249455
theorem R133625 : Reach 133625 := rs (se 2 (by rfl) ⟨50109, by rfl⟩) R100219
theorem R199259 : Reach 199259 := rs (se 1 (by rfl) ⟨149444, by rfl⟩) R298889
theorem R199295 : Reach 199295 := rs (se 1 (by rfl) ⟨149471, by rfl⟩) R298943
theorem R363163 : Reach 363163 := rs (se 1 (by rfl) ⟨272372, by rfl⟩) R544745
theorem R133883 : Reach 133883 := rs (se 1 (by rfl) ⟨100412, by rfl⟩) R200825
theorem R101191 : Reach 101191 := rs (se 1 (by rfl) ⟨75893, by rfl⟩) R151787
theorem R134399 : Reach 134399 := rs (se 1 (by rfl) ⟨100799, by rfl⟩) R201599
theorem R167177 : Reach 167177 := rs (se 2 (by rfl) ⟨62691, by rfl⟩) R125383
theorem R298295 : Reach 298295 := rs (se 1 (by rfl) ⟨223721, by rfl⟩) R447443
theorem R134555 : Reach 134555 := rs (se 1 (by rfl) ⟨100916, by rfl⟩) R201833
theorem R102055 : Reach 102055 := rs (se 1 (by rfl) ⟨76541, by rfl⟩) R153083
theorem R167663 : Reach 167663 := rs (se 1 (by rfl) ⟨125747, by rfl⟩) R251495
theorem R102127 : Reach 102127 := rs (se 1 (by rfl) ⟨76595, by rfl⟩) R153191
theorem R135209 : Reach 135209 := rs (se 2 (by rfl) ⟨50703, by rfl⟩) R101407
theorem R135215 : Reach 135215 := rs (se 1 (by rfl) ⟨101411, by rfl⟩) R202823
theorem R6295643 : Reach 6295643 := rs (se 1 (by rfl) ⟨4721732, by rfl⟩) R9443465
theorem R168095 : Reach 168095 := rs (se 1 (by rfl) ⟨126071, by rfl⟩) R252143
theorem R200987 : Reach 200987 := rs (se 1 (by rfl) ⟨150740, by rfl⟩) R301481
theorem R135503 : Reach 135503 := rs (se 1 (by rfl) ⟨101627, by rfl⟩) R203255
theorem R397735 : Reach 397735 := rs (se 1 (by rfl) ⟨298301, by rfl⟩) R596603
theorem R168475 : Reach 168475 := rs (se 1 (by rfl) ⟨126356, by rfl⟩) R252713
theorem R135899 : Reach 135899 := rs (se 1 (by rfl) ⟨101924, by rfl⟩) R203849
theorem R136607 : Reach 136607 := rs (se 1 (by rfl) ⟨102455, by rfl⟩) R204911
theorem R628319 : Reach 628319 := rs (se 1 (by rfl) ⟨471239, by rfl⟩) R942479
theorem R333503 : Reach 333503 := rs (se 1 (by rfl) ⟨250127, by rfl⟩) R500255
theorem R333821 : Reach 333821 := rs (se 3 (by rfl) ⟨62591, by rfl⟩) R125183
theorem R956569 : Reach 956569 := rs (se 2 (by rfl) ⟨358713, by rfl⟩) R717427
theorem R170579 : Reach 170579 := rs (se 1 (by rfl) ⟨127934, by rfl⟩) R255869
theorem R498271 : Reach 498271 := rs (se 1 (by rfl) ⟨373703, by rfl⟩) R747407
theorem R302075 : Reach 302075 := rs (se 1 (by rfl) ⟨226556, by rfl⟩) R453113
theorem R302183 : Reach 302183 := rs (se 1 (by rfl) ⟨226637, by rfl⟩) R453275
theorem R762169 : Reach 762169 := rs (se 2 (by rfl) ⟨285813, by rfl⟩) R571627
theorem R303695 : Reach 303695 := rs (se 1 (by rfl) ⟨227771, by rfl⟩) R455543
theorem R303803 : Reach 303803 := rs (se 1 (by rfl) ⟨227852, by rfl⟩) R455705
theorem R303911 : Reach 303911 := rs (se 1 (by rfl) ⟨227933, by rfl⟩) R455867
theorem R1288007 : Reach 1288007 := rs (se 1 (by rfl) ⟨966005, by rfl⟩) R1932011
theorem R436679 : Reach 436679 := rs (se 1 (by rfl) ⟨327509, by rfl⟩) R655019
theorem R306017 : Reach 306017 := rs (se 2 (by rfl) ⟨114756, by rfl⟩) R229513
theorem R994355 : Reach 994355 := rs (se 1 (by rfl) ⟨745766, by rfl⟩) R1491533
theorem R306287 : Reach 306287 := rs (se 1 (by rfl) ⟨229715, by rfl⟩) R459431
theorem R568529 : Reach 568529 := rs (se 2 (by rfl) ⟨213198, by rfl⟩) R426397
theorem R306503 : Reach 306503 := rs (se 1 (by rfl) ⟨229877, by rfl⟩) R459755
theorem R536863 : Reach 536863 := rs (se 1 (by rfl) ⟨402647, by rfl⟩) R805295
theorem R2700611 : Reach 2700611 := rs (se 1 (by rfl) ⟨2025458, by rfl⟩) R4050917
theorem R505607 : Reach 505607 := rs (se 1 (by rfl) ⟨379205, by rfl⟩) R758411
theorem R4634657 : Reach 4634657 := rs (se 2 (by rfl) ⟨1737996, by rfl⟩) R3475993
theorem R1063115 : Reach 1063115 := rs (se 1 (by rfl) ⟨797336, by rfl⟩) R1594673
theorem R244703 : Reach 244703 := rs (se 1 (by rfl) ⟨183527, by rfl⟩) R367055
theorem R148459 : Reach 148459 := rs (se 1 (by rfl) ⟨111344, by rfl⟩) R222689
theorem R1231037 : Reach 1231037 := rs (se 3 (by rfl) ⟨230819, by rfl⟩) R461639
theorem R149897 : Reach 149897 := rs (se 2 (by rfl) ⟨56211, by rfl⟩) R112423
theorem R150511 : Reach 150511 := rs (se 1 (by rfl) ⟨112883, by rfl⟩) R225767
theorem R380189 : Reach 380189 := rs (se 3 (by rfl) ⟨71285, by rfl⟩) R142571
theorem R150943 : Reach 150943 := rs (se 1 (by rfl) ⟨113207, by rfl⟩) R226415
theorem R151463 : Reach 151463 := rs (se 1 (by rfl) ⟨113597, by rfl⟩) R227195
theorem R511919 : Reach 511919 := rs (se 1 (by rfl) ⟨383939, by rfl⟩) R767879
theorem R2543723 : Reach 2543723 := rs (se 1 (by rfl) ⟨1907792, by rfl⟩) R3815585
theorem R18764435 : Reach 18764435 := rs (se 1 (by rfl) ⟨14073326, by rfl⟩) R28146653
theorem R1462967 : Reach 1462967 := rs (se 1 (by rfl) ⟨1097225, by rfl⟩) R2194451
theorem R87199 : Reach 87199 := rs (se 1 (by rfl) ⟨65399, by rfl⟩) R130799
theorem R87323 : Reach 87323 := rs (se 1 (by rfl) ⟨65492, by rfl⟩) R130985
theorem R579473 : Reach 579473 := rs (se 2 (by rfl) ⟨217302, by rfl⟩) R434605
theorem R153515 : Reach 153515 := rs (se 1 (by rfl) ⟨115136, by rfl⟩) R230273
theorem R88175 : Reach 88175 := rs (se 1 (by rfl) ⟨66131, by rfl⟩) R132263
theorem R88623 : Reach 88623 := rs (se 1 (by rfl) ⟨66467, by rfl⟩) R132935
theorem R88783 : Reach 88783 := rs (se 1 (by rfl) ⟨66587, by rfl⟩) R133175
theorem R89055 : Reach 89055 := rs (se 1 (by rfl) ⟨66791, by rfl⟩) R133583
theorem R515767 : Reach 515767 := rs (se 1 (by rfl) ⟨386825, by rfl⟩) R773651
theorem R516041 : Reach 516041 := rs (se 2 (by rfl) ⟨193515, by rfl⟩) R387031
theorem R90271 : Reach 90271 := rs (se 1 (by rfl) ⟨67703, by rfl⟩) R135407
theorem R90395 : Reach 90395 := rs (se 1 (by rfl) ⟨67796, by rfl⟩) R135593
theorem R1466657 : Reach 1466657 := rs (se 2 (by rfl) ⟨549996, by rfl⟩) R1099993
theorem R385631 : Reach 385631 := rs (se 1 (by rfl) ⟨289223, by rfl⟩) R578447
theorem R90863 : Reach 90863 := rs (se 1 (by rfl) ⟨68147, by rfl⟩) R136295
theorem R90879 : Reach 90879 := rs (se 1 (by rfl) ⟨68159, by rfl⟩) R136319
theorem R1270889 : Reach 1270889 := rs (se 2 (by rfl) ⟨476583, by rfl⟩) R953167
theorem R320849 : Reach 320849 := rs (se 2 (by rfl) ⟨120318, by rfl⟩) R240637
theorem R1959461 : Reach 1959461 := rs (se 4 (by rfl) ⟨183699, by rfl⟩) R367399
theorem R321167 : Reach 321167 := rs (se 1 (by rfl) ⟨240875, by rfl⟩) R481751
theorem R1730807 : Reach 1730807 := rs (se 1 (by rfl) ⟨1298105, by rfl⟩) R2596211
theorem R191423 : Reach 191423 := rs (se 1 (by rfl) ⟨143567, by rfl⟩) R287135
theorem R257327 : Reach 257327 := rs (se 1 (by rfl) ⟨192995, by rfl⟩) R385991
theorem R224795 : Reach 224795 := rs (se 1 (by rfl) ⟨168596, by rfl⟩) R337193
theorem R224815 : Reach 224815 := rs (se 1 (by rfl) ⟨168611, by rfl⟩) R337223
theorem R454247 : Reach 454247 := rs (se 1 (by rfl) ⟨340685, by rfl⟩) R681371
theorem R552577 : Reach 552577 := rs (se 2 (by rfl) ⟨207216, by rfl⟩) R414433
theorem R323617 : Reach 323617 := rs (se 2 (by rfl) ⟨121356, by rfl⟩) R242713
theorem R192559 : Reach 192559 := rs (se 1 (by rfl) ⟨144419, by rfl⟩) R288839
theorem R225575 : Reach 225575 := rs (se 1 (by rfl) ⟨169181, by rfl⟩) R338363
theorem R553355 : Reach 553355 := rs (se 1 (by rfl) ⟨415016, by rfl⟩) R830033
theorem R914323 : Reach 914323 := rs (se 1 (by rfl) ⟨685742, by rfl⟩) R1371485
theorem R35452673 : Reach 35452673 := rs (se 2 (by rfl) ⟨13294752, by rfl⟩) R26589505
theorem R260435 : Reach 260435 := rs (se 1 (by rfl) ⟨195326, by rfl⟩) R390653
theorem R424415 : Reach 424415 := rs (se 1 (by rfl) ⟨318311, by rfl⟩) R636623
theorem R1211219 : Reach 1211219 := rs (se 1 (by rfl) ⟨908414, by rfl⟩) R1816829
theorem R228577 : Reach 228577 := rs (se 2 (by rfl) ⟨85716, by rfl⟩) R171433
theorem R163129 : Reach 163129 := rs (se 2 (by rfl) ⟨61173, by rfl⟩) R122347
theorem R1637729 : Reach 1637729 := rs (se 2 (by rfl) ⟨614148, by rfl⟩) R1228297
theorem R131051 : Reach 131051 := rs (se 1 (by rfl) ⟨98288, by rfl⟩) R196577
theorem R196775 : Reach 196775 := rs (se 1 (by rfl) ⟨147581, by rfl⟩) R295163
theorem R196919 : Reach 196919 := rs (se 1 (by rfl) ⟨147689, by rfl⟩) R295379
theorem R1016225 : Reach 1016225 := rs (se 2 (by rfl) ⟨381084, by rfl⟩) R762169
theorem R131519 : Reach 131519 := rs (se 1 (by rfl) ⟨98639, by rfl⟩) R197279
theorem R131639 : Reach 131639 := rs (se 1 (by rfl) ⟨98729, by rfl⟩) R197459
theorem R132095 : Reach 132095 := rs (se 1 (by rfl) ⟨99071, by rfl⟩) R198143
theorem R132143 : Reach 132143 := rs (se 1 (by rfl) ⟨99107, by rfl⟩) R198215
theorem R197945 : Reach 197945 := rs (se 2 (by rfl) ⟨74229, by rfl⟩) R148459
theorem R820691 : Reach 820691 := rs (se 1 (by rfl) ⟨615518, by rfl⟩) R1231037
theorem R99931 : Reach 99931 := rs (se 1 (by rfl) ⟨74948, by rfl⟩) R149897
theorem R132839 : Reach 132839 := rs (se 1 (by rfl) ⟨99629, by rfl⟩) R199259
theorem R132863 : Reach 132863 := rs (se 1 (by rfl) ⟨99647, by rfl⟩) R199295
theorem R133289 : Reach 133289 := rs (se 2 (by rfl) ⟨49983, by rfl⟩) R99967
theorem R198863 : Reach 198863 := rs (se 1 (by rfl) ⟨149147, by rfl⟩) R298295
theorem R100975 : Reach 100975 := rs (se 1 (by rfl) ⟨75731, by rfl⟩) R151463
theorem R4197095 : Reach 4197095 := rs (se 1 (by rfl) ⟨3147821, by rfl⟩) R6295643
theorem R133991 : Reach 133991 := rs (se 1 (by rfl) ⟨100493, by rfl⟩) R200987
theorem R134921 : Reach 134921 := rs (se 2 (by rfl) ⟨50595, by rfl⟩) R101191
theorem R102343 : Reach 102343 := rs (se 1 (by rfl) ⟨76757, by rfl⟩) R153515
theorem R200681 : Reach 200681 := rs (se 2 (by rfl) ⟨75255, by rfl⟩) R150511
theorem R201257 : Reach 201257 := rs (se 2 (by rfl) ⟨75471, by rfl⟩) R150943
theorem R201383 : Reach 201383 := rs (se 1 (by rfl) ⟨151037, by rfl⟩) R302075
theorem R299753 : Reach 299753 := rs (se 2 (by rfl) ⟨112407, by rfl⟩) R224815
theorem R201455 : Reach 201455 := rs (se 1 (by rfl) ⟨151091, by rfl⟩) R302183
theorem R136073 : Reach 136073 := rs (se 2 (by rfl) ⟨51027, by rfl⟩) R102055
theorem R136169 : Reach 136169 := rs (se 2 (by rfl) ⟨51063, by rfl⟩) R102127
theorem R431489 : Reach 431489 := rs (se 2 (by rfl) ⟨161808, by rfl⟩) R323617
theorem R202463 : Reach 202463 := rs (se 1 (by rfl) ⟨151847, by rfl⟩) R303695
theorem R202535 : Reach 202535 := rs (se 1 (by rfl) ⟨151901, by rfl⟩) R303803
theorem R202607 : Reach 202607 := rs (se 1 (by rfl) ⟨151955, by rfl⟩) R303911
theorem R694493 : Reach 694493 := rs (se 3 (by rfl) ⟨130217, by rfl⟩) R260435
theorem R1219097 : Reach 1219097 := rs (se 2 (by rfl) ⟨457161, by rfl⟩) R914323
theorem R858671 : Reach 858671 := rs (se 1 (by rfl) ⟨644003, by rfl⟩) R1288007
theorem R1153871 : Reach 1153871 := rs (se 1 (by rfl) ⟨865403, by rfl⟩) R1730807
theorem R204011 : Reach 204011 := rs (se 1 (by rfl) ⟨153008, by rfl⟩) R306017
theorem R662903 : Reach 662903 := rs (se 1 (by rfl) ⟨497177, by rfl⟩) R994355
theorem R204191 : Reach 204191 := rs (se 1 (by rfl) ⟨153143, by rfl⟩) R306287
theorem R171551 : Reach 171551 := rs (se 1 (by rfl) ⟨128663, by rfl⟩) R257327
theorem R204335 : Reach 204335 := rs (se 1 (by rfl) ⟨153251, by rfl⟩) R306503
theorem R302831 : Reach 302831 := rs (se 1 (by rfl) ⟨227123, by rfl⟩) R454247
theorem R368903 : Reach 368903 := rs (se 1 (by rfl) ⟨276677, by rfl⟩) R553355
theorem R664361 : Reach 664361 := rs (se 2 (by rfl) ⟨249135, by rfl⟩) R498271
theorem R23635115 : Reach 23635115 := rs (se 1 (by rfl) ⟨17726336, by rfl⟩) R35452673
theorem R3089771 : Reach 3089771 := rs (se 1 (by rfl) ⟨2317328, by rfl⟩) R4634657
theorem R304769 : Reach 304769 := rs (se 2 (by rfl) ⟨114288, by rfl⟩) R228577
theorem R1091819 : Reach 1091819 := rs (se 1 (by rfl) ⟨818864, by rfl⟩) R1637729
theorem R110747 : Reach 110747 := rs (se 1 (by rfl) ⟨83060, by rfl⟩) R166121
theorem R111451 : Reach 111451 := rs (se 1 (by rfl) ⟨83588, by rfl⟩) R167177
theorem R111775 : Reach 111775 := rs (se 1 (by rfl) ⟨83831, by rfl⟩) R167663
theorem R341279 : Reach 341279 := rs (se 1 (by rfl) ⟨255959, by rfl⟩) R511919
theorem R113719 : Reach 113719 := rs (se 1 (by rfl) ⟨85289, by rfl⟩) R170579
theorem R736769 : Reach 736769 := rs (se 2 (by rfl) ⟨276288, by rfl⟩) R552577
theorem R344027 : Reach 344027 := rs (se 1 (by rfl) ⟨258020, by rfl⟩) R516041
theorem R213899 : Reach 213899 := rs (se 1 (by rfl) ⟨160424, by rfl⟩) R320849
theorem R214111 : Reach 214111 := rs (se 1 (by rfl) ⟨160583, by rfl⟩) R321167
theorem R379019 : Reach 379019 := rs (se 1 (by rfl) ⟨284264, by rfl⟩) R568529
theorem R149863 : Reach 149863 := rs (se 1 (by rfl) ⟨112397, by rfl⟩) R224795
theorem R510461 : Reach 510461 := rs (se 3 (by rfl) ⟨95711, by rfl⟩) R191423
theorem R5393141 : Reach 5393141 := rs (se 5 (by rfl) ⟨252803, by rfl⟩) R505607
theorem R150383 : Reach 150383 := rs (se 1 (by rfl) ⟨112787, by rfl⟩) R225575
theorem R708743 : Reach 708743 := rs (se 1 (by rfl) ⟨531557, by rfl⟩) R1063115
theorem R282943 : Reach 282943 := rs (se 1 (by rfl) ⟨212207, by rfl⟩) R424415
theorem R217505 : Reach 217505 := rs (se 2 (by rfl) ⟨81564, by rfl⟩) R163129
theorem R807479 : Reach 807479 := rs (se 1 (by rfl) ⟨605609, by rfl⟩) R1211219
theorem R87367 : Reach 87367 := rs (se 1 (by rfl) ⟨65525, by rfl⟩) R131051
theorem R87423 : Reach 87423 := rs (se 1 (by rfl) ⟨65567, by rfl⟩) R131135
theorem R218729 : Reach 218729 := rs (se 2 (by rfl) ⟨82023, by rfl⟩) R164047
theorem R87783 : Reach 87783 := rs (se 1 (by rfl) ⟨65837, by rfl⟩) R131675
theorem R448253 : Reach 448253 := rs (se 3 (by rfl) ⟨84047, by rfl⟩) R168095
theorem R88303 : Reach 88303 := rs (se 1 (by rfl) ⟨66227, by rfl⟩) R132455
theorem R88391 : Reach 88391 := rs (se 1 (by rfl) ⟨66293, by rfl⟩) R132587
theorem R88687 : Reach 88687 := rs (se 1 (by rfl) ⟨66515, by rfl⟩) R133031
theorem R88863 : Reach 88863 := rs (se 1 (by rfl) ⟨66647, by rfl⟩) R133295
theorem R89083 : Reach 89083 := rs (se 1 (by rfl) ⟨66812, by rfl⟩) R133625
theorem R89255 : Reach 89255 := rs (se 1 (by rfl) ⟨66941, by rfl⟩) R133883
theorem R89599 : Reach 89599 := rs (se 1 (by rfl) ⟨67199, by rfl⟩) R134399
theorem R253459 : Reach 253459 := rs (se 1 (by rfl) ⟨190094, by rfl⟩) R380189
theorem R220745 : Reach 220745 := rs (se 2 (by rfl) ⟨82779, by rfl⟩) R165559
theorem R89703 : Reach 89703 := rs (se 1 (by rfl) ⟨67277, by rfl⟩) R134555
theorem R90139 : Reach 90139 := rs (se 1 (by rfl) ⟨67604, by rfl⟩) R135209
theorem R90143 : Reach 90143 := rs (se 1 (by rfl) ⟨67607, by rfl⟩) R135215
theorem R1695815 : Reach 1695815 := rs (se 1 (by rfl) ⟨1271861, by rfl⟩) R2543723
theorem R90335 : Reach 90335 := rs (se 1 (by rfl) ⟨67751, by rfl⟩) R135503
theorem R12509623 : Reach 12509623 := rs (se 1 (by rfl) ⟨9382217, by rfl⟩) R18764435
theorem R975311 : Reach 975311 := rs (se 1 (by rfl) ⟨731483, by rfl⟩) R1462967
theorem R90599 : Reach 90599 := rs (se 1 (by rfl) ⟨67949, by rfl⟩) R135899
theorem R221737 : Reach 221737 := rs (se 2 (by rfl) ⟨83151, by rfl⟩) R166303
theorem R484217 : Reach 484217 := rs (se 2 (by rfl) ⟨181581, by rfl⟩) R363163
theorem R91071 : Reach 91071 := rs (se 1 (by rfl) ⟨68303, by rfl⟩) R136607
theorem R418879 : Reach 418879 := rs (se 1 (by rfl) ⟨314159, by rfl⟩) R628319
theorem R222335 : Reach 222335 := rs (se 1 (by rfl) ⟨166751, by rfl⟩) R333503
theorem R386315 : Reach 386315 := rs (se 1 (by rfl) ⟨289736, by rfl⟩) R579473
theorem R222547 : Reach 222547 := rs (se 1 (by rfl) ⟨166910, by rfl⟩) R333821
theorem R256745 : Reach 256745 := rs (se 2 (by rfl) ⟨96279, by rfl⟩) R192559
theorem R977771 : Reach 977771 := rs (se 1 (by rfl) ⟨733328, by rfl⟩) R1466657
theorem R715817 : Reach 715817 := rs (se 2 (by rfl) ⟨268431, by rfl⟩) R536863
theorem R257087 : Reach 257087 := rs (se 1 (by rfl) ⟨192815, by rfl⟩) R385631
theorem R224633 : Reach 224633 := rs (se 2 (by rfl) ⟨84237, by rfl⟩) R168475
theorem R847259 : Reach 847259 := rs (se 1 (by rfl) ⟨635444, by rfl⟩) R1270889
theorem R1306307 : Reach 1306307 := rs (se 1 (by rfl) ⟨979730, by rfl⟩) R1959461
theorem R291119 : Reach 291119 := rs (se 1 (by rfl) ⟨218339, by rfl⟩) R436679
theorem R1275425 : Reach 1275425 := rs (se 2 (by rfl) ⟨478284, by rfl⟩) R956569
theorem R8485013 : Reach 8485013 := rs (se 6 (by rfl) ⟨198867, by rfl⟩) R397735
theorem R1800407 : Reach 1800407 := rs (se 1 (by rfl) ⟨1350305, by rfl⟩) R2700611
theorem R163135 : Reach 163135 := rs (se 1 (by rfl) ⟨122351, by rfl⟩) R244703
theorem R687689 : Reach 687689 := rs (se 2 (by rfl) ⟨257883, by rfl⟩) R515767
theorem R131183 : Reach 131183 := rs (se 1 (by rfl) ⟨98387, by rfl⟩) R196775
theorem R131279 : Reach 131279 := rs (se 1 (by rfl) ⟨98459, by rfl⟩) R196919
theorem R295325 : Reach 295325 := rs (se 3 (by rfl) ⟨55373, by rfl⟩) R110747
theorem R295649 : Reach 295649 := rs (se 2 (by rfl) ⟨110868, by rfl⟩) R221737
theorem R131963 : Reach 131963 := rs (se 1 (by rfl) ⟨98972, by rfl⟩) R197945
theorem R558505 : Reach 558505 := rs (se 2 (by rfl) ⟨209439, by rfl⟩) R418879
theorem R132575 : Reach 132575 := rs (se 1 (by rfl) ⟨99431, by rfl⟩) R198863
theorem R1509029 : Reach 1509029 := rs (se 4 (by rfl) ⟨141471, by rfl⟩) R282943
theorem R296729 : Reach 296729 := rs (se 2 (by rfl) ⟨111273, by rfl⟩) R222547
theorem R100255 : Reach 100255 := rs (se 1 (by rfl) ⟨75191, by rfl⟩) R150383
theorem R133241 : Reach 133241 := rs (se 2 (by rfl) ⟨49965, by rfl⟩) R99931
theorem R66717989 : Reach 66717989 := rs (se 4 (by rfl) ⟨6254811, by rfl⟩) R12509623
theorem R133787 : Reach 133787 := rs (se 1 (by rfl) ⟨100340, by rfl⟩) R200681
theorem R134171 : Reach 134171 := rs (se 1 (by rfl) ⟨100628, by rfl⟩) R201257
theorem R134255 : Reach 134255 := rs (se 1 (by rfl) ⟨100691, by rfl⟩) R201383
theorem R199817 : Reach 199817 := rs (se 2 (by rfl) ⟨74931, by rfl⟩) R149863
theorem R199835 : Reach 199835 := rs (se 1 (by rfl) ⟨149876, by rfl⟩) R299753
theorem R134303 : Reach 134303 := rs (se 1 (by rfl) ⟨100727, by rfl⟩) R201455
theorem R134633 : Reach 134633 := rs (se 2 (by rfl) ⟨50487, by rfl⟩) R100975
theorem R134975 : Reach 134975 := rs (se 1 (by rfl) ⟨101231, by rfl⟩) R202463
theorem R298835 : Reach 298835 := rs (se 1 (by rfl) ⟨224126, by rfl⟩) R448253
theorem R135023 : Reach 135023 := rs (se 1 (by rfl) ⟨101267, by rfl⟩) R202535
theorem R135071 : Reach 135071 := rs (se 1 (by rfl) ⟨101303, by rfl⟩) R202607
theorem R462995 : Reach 462995 := rs (se 1 (by rfl) ⟨347246, by rfl⟩) R694493
theorem R136007 : Reach 136007 := rs (se 1 (by rfl) ⟨102005, by rfl⟩) R204011
theorem R136127 : Reach 136127 := rs (se 1 (by rfl) ⟨102095, by rfl⟩) R204191
theorem R136223 : Reach 136223 := rs (se 1 (by rfl) ⟨102167, by rfl⟩) R204335
theorem R201887 : Reach 201887 := rs (se 1 (by rfl) ⟨151415, by rfl⟩) R302831
theorem R136457 : Reach 136457 := rs (se 2 (by rfl) ⟨51171, by rfl⟩) R102343
theorem R3250925 : Reach 3250925 := rs (se 3 (by rfl) ⟨609548, by rfl⟩) R1219097
theorem R727879 : Reach 727879 := rs (se 1 (by rfl) ⟨545909, by rfl⟩) R1091819
theorem R171163 : Reach 171163 := rs (se 1 (by rfl) ⟨128372, by rfl⟩) R256745
theorem R171391 : Reach 171391 := rs (se 1 (by rfl) ⟨128543, by rfl⟩) R257087
theorem R564839 : Reach 564839 := rs (se 1 (by rfl) ⟨423629, by rfl⟩) R847259
theorem R1351781 : Reach 1351781 := rs (se 4 (by rfl) ⟨126729, by rfl⟩) R253459
theorem R340307 : Reach 340307 := rs (se 1 (by rfl) ⟨255230, by rfl⟩) R510461
theorem R2798063 : Reach 2798063 := rs (se 1 (by rfl) ⟨2098547, by rfl⟩) R4197095
theorem R570397 : Reach 570397 := rs (se 3 (by rfl) ⟨106949, by rfl⟩) R213899
theorem R472495 : Reach 472495 := rs (se 1 (by rfl) ⟨354371, by rfl⟩) R708743
theorem R145003 : Reach 145003 := rs (se 1 (by rfl) ⟨108752, by rfl⟩) R217505
theorem R538319 : Reach 538319 := rs (se 1 (by rfl) ⟨403739, by rfl⟩) R807479
theorem R145819 : Reach 145819 := rs (se 1 (by rfl) ⟨109364, by rfl⟩) R218729
theorem R572447 : Reach 572447 := rs (se 1 (by rfl) ⟨429335, by rfl⟩) R858671
theorem R769247 : Reach 769247 := rs (se 1 (by rfl) ⟨576935, by rfl⟩) R1153871
theorem R441935 : Reach 441935 := rs (se 1 (by rfl) ⟨331451, by rfl⟩) R662903
theorem R114367 : Reach 114367 := rs (se 1 (by rfl) ⟨85775, by rfl⟩) R171551
theorem R147163 : Reach 147163 := rs (se 1 (by rfl) ⟨110372, by rfl⟩) R220745
theorem R1130543 : Reach 1130543 := rs (se 1 (by rfl) ⟨847907, by rfl⟩) R1695815
theorem R245935 : Reach 245935 := rs (se 1 (by rfl) ⟨184451, by rfl⟩) R368903
theorem R442907 : Reach 442907 := rs (se 1 (by rfl) ⟨332180, by rfl⟩) R664361
theorem R148223 : Reach 148223 := rs (se 1 (by rfl) ⟨111167, by rfl⟩) R222335
theorem R148601 : Reach 148601 := rs (se 2 (by rfl) ⟨55725, by rfl⟩) R111451
theorem R149033 : Reach 149033 := rs (se 2 (by rfl) ⟨55887, by rfl⟩) R111775
theorem R477211 : Reach 477211 := rs (se 1 (by rfl) ⟨357908, by rfl⟩) R715817
theorem R149755 : Reach 149755 := rs (se 1 (by rfl) ⟨112316, by rfl⟩) R224633
theorem R870871 : Reach 870871 := rs (se 1 (by rfl) ⟨653153, by rfl⟩) R1306307
theorem R151625 : Reach 151625 := rs (se 2 (by rfl) ⟨56859, by rfl⟩) R113719
theorem R5656675 : Reach 5656675 := rs (se 1 (by rfl) ⟨4242506, by rfl⟩) R8485013
theorem R1200271 : Reach 1200271 := rs (se 1 (by rfl) ⟨900203, by rfl⟩) R1800407
theorem R217513 : Reach 217513 := rs (se 2 (by rfl) ⟨81567, by rfl⟩) R163135
theorem R677483 : Reach 677483 := rs (se 1 (by rfl) ⟨508112, by rfl⟩) R1016225
theorem R87679 : Reach 87679 := rs (se 1 (by rfl) ⟨65759, by rfl⟩) R131519
theorem R87759 : Reach 87759 := rs (se 1 (by rfl) ⟨65819, by rfl⟩) R131639
theorem R88063 : Reach 88063 := rs (se 1 (by rfl) ⟨66047, by rfl⟩) R132095
theorem R88095 : Reach 88095 := rs (se 1 (by rfl) ⟨66071, by rfl⟩) R132143
theorem R776317 : Reach 776317 := rs (se 3 (by rfl) ⟨145559, by rfl⟩) R291119
theorem R547127 : Reach 547127 := rs (se 1 (by rfl) ⟨410345, by rfl⟩) R820691
theorem R88559 : Reach 88559 := rs (se 1 (by rfl) ⟨66419, by rfl⟩) R132839
theorem R88575 : Reach 88575 := rs (se 1 (by rfl) ⟨66431, by rfl⟩) R132863
theorem R252679 : Reach 252679 := rs (se 1 (by rfl) ⟨189509, by rfl⟩) R379019
theorem R88859 : Reach 88859 := rs (se 1 (by rfl) ⟨66644, by rfl⟩) R133289
theorem R285481 : Reach 285481 := rs (se 2 (by rfl) ⟨107055, by rfl⟩) R214111
theorem R3595427 : Reach 3595427 := rs (se 1 (by rfl) ⟨2696570, by rfl⟩) R5393141
theorem R89327 : Reach 89327 := rs (se 1 (by rfl) ⟨66995, by rfl⟩) R133991
theorem R89947 : Reach 89947 := rs (se 1 (by rfl) ⟨67460, by rfl⟩) R134921
theorem R90715 : Reach 90715 := rs (se 1 (by rfl) ⟨68036, by rfl⟩) R136073
theorem R90779 : Reach 90779 := rs (se 1 (by rfl) ⟨68084, by rfl⟩) R136169
theorem R287659 : Reach 287659 := rs (se 1 (by rfl) ⟨215744, by rfl⟩) R431489
theorem R812717 : Reach 812717 := rs (se 3 (by rfl) ⟨152384, by rfl⟩) R304769
theorem R650207 : Reach 650207 := rs (se 1 (by rfl) ⟨487655, by rfl⟩) R975311
theorem R322811 : Reach 322811 := rs (se 1 (by rfl) ⟨242108, by rfl⟩) R484217
theorem R15756743 : Reach 15756743 := rs (se 1 (by rfl) ⟨11817557, by rfl⟩) R23635115
theorem R257543 : Reach 257543 := rs (se 1 (by rfl) ⟨193157, by rfl⟩) R386315
theorem R2059847 : Reach 2059847 := rs (se 1 (by rfl) ⟨1544885, by rfl⟩) R3089771
theorem R651847 : Reach 651847 := rs (se 1 (by rfl) ⟨488885, by rfl⟩) R977771
theorem R227519 : Reach 227519 := rs (se 1 (by rfl) ⟨170639, by rfl⟩) R341279
theorem R850283 : Reach 850283 := rs (se 1 (by rfl) ⟨637712, by rfl⟩) R1275425
theorem R491179 : Reach 491179 := rs (se 1 (by rfl) ⟨368384, by rfl⟩) R736769
theorem R458459 : Reach 458459 := rs (se 1 (by rfl) ⟨343844, by rfl⟩) R687689
theorem R229351 : Reach 229351 := rs (se 1 (by rfl) ⟨172013, by rfl⟩) R344027
theorem R753695 : Reach 753695 := rs (se 1 (by rfl) ⟨565271, by rfl⟩) R1130543
theorem R196883 : Reach 196883 := rs (se 1 (by rfl) ⟨147662, by rfl⟩) R295325
theorem R295271 : Reach 295271 := rs (se 1 (by rfl) ⟨221453, by rfl⟩) R442907
theorem R197099 : Reach 197099 := rs (se 1 (by rfl) ⟨147824, by rfl⟩) R295649
theorem R98815 : Reach 98815 := rs (se 1 (by rfl) ⟨74111, by rfl⟩) R148223
theorem R99067 : Reach 99067 := rs (se 1 (by rfl) ⟨74300, by rfl⟩) R148601
theorem R1311653 : Reach 1311653 := rs (se 4 (by rfl) ⟨122967, by rfl⟩) R245935
theorem R99355 : Reach 99355 := rs (se 1 (by rfl) ⟨74516, by rfl⟩) R149033
theorem R197819 : Reach 197819 := rs (se 1 (by rfl) ⟨148364, by rfl⟩) R296729
theorem R133211 : Reach 133211 := rs (se 1 (by rfl) ⟨99908, by rfl⟩) R199817
theorem R133223 : Reach 133223 := rs (se 1 (by rfl) ⟨99917, by rfl⟩) R199835
theorem R133673 : Reach 133673 := rs (se 2 (by rfl) ⟨50127, by rfl⟩) R100255
theorem R199223 : Reach 199223 := rs (se 1 (by rfl) ⟨149417, by rfl⟩) R298835
theorem R101083 : Reach 101083 := rs (se 1 (by rfl) ⟨75812, by rfl⟩) R151625
theorem R199673 : Reach 199673 := rs (se 2 (by rfl) ⟨74877, by rfl⟩) R149755
theorem R134591 : Reach 134591 := rs (se 1 (by rfl) ⟨100943, by rfl⟩) R201887
theorem R364751 : Reach 364751 := rs (se 1 (by rfl) ⟨273563, by rfl⟩) R547127
theorem R2167283 : Reach 2167283 := rs (se 1 (by rfl) ⟨1625462, by rfl⟩) R3250925
theorem R2396951 : Reach 2396951 := rs (se 1 (by rfl) ⟨1797713, by rfl⟩) R3595427
theorem R7542233 : Reach 7542233 := rs (se 2 (by rfl) ⟨2828337, by rfl⟩) R5656675
theorem R760529 : Reach 760529 := rs (se 2 (by rfl) ⟨285198, by rfl⟩) R570397
theorem R629993 : Reach 629993 := rs (se 2 (by rfl) ⟨236247, by rfl⟩) R472495
theorem R433471 : Reach 433471 := rs (se 1 (by rfl) ⟨325103, by rfl⟩) R650207
theorem R171695 : Reach 171695 := rs (se 1 (by rfl) ⟨128771, by rfl⟩) R257543
theorem R336905 : Reach 336905 := rs (se 2 (by rfl) ⟨126339, by rfl⟩) R252679
theorem R566855 : Reach 566855 := rs (se 1 (by rfl) ⟨425141, by rfl⟩) R850283
theorem R305639 : Reach 305639 := rs (se 1 (by rfl) ⟨229229, by rfl⟩) R458459
theorem R305801 : Reach 305801 := rs (se 2 (by rfl) ⟨114675, by rfl⟩) R229351
theorem R44478659 : Reach 44478659 := rs (se 1 (by rfl) ⟨33358994, by rfl⟩) R66717989
theorem R636281 : Reach 636281 := rs (se 2 (by rfl) ⟨238605, by rfl⟩) R477211
theorem R308663 : Reach 308663 := rs (se 1 (by rfl) ⟨231497, by rfl⟩) R462995
theorem R1161161 : Reach 1161161 := rs (se 2 (by rfl) ⟨435435, by rfl⟩) R870871
theorem R376559 : Reach 376559 := rs (se 1 (by rfl) ⟨282419, by rfl⟩) R564839
theorem R901187 : Reach 901187 := rs (se 1 (by rfl) ⟨675890, by rfl⟩) R1351781
theorem R869129 : Reach 869129 := rs (se 2 (by rfl) ⟨325923, by rfl⟩) R651847
theorem R541811 : Reach 541811 := rs (se 1 (by rfl) ⟨406358, by rfl⟩) R812717
theorem R215207 : Reach 215207 := rs (se 1 (by rfl) ⟨161405, by rfl⟩) R322811
theorem R10504495 : Reach 10504495 := rs (se 1 (by rfl) ⟨7878371, by rfl⟩) R15756743
theorem R1526525 : Reach 1526525 := rs (se 3 (by rfl) ⟨286223, by rfl⟩) R572447
theorem R1035089 : Reach 1035089 := rs (se 2 (by rfl) ⟨388158, by rfl⟩) R776317
theorem R380641 : Reach 380641 := rs (se 2 (by rfl) ⟨142740, by rfl⟩) R285481
theorem R970505 : Reach 970505 := rs (se 2 (by rfl) ⟨363939, by rfl⟩) R727879
theorem R151679 : Reach 151679 := rs (se 1 (by rfl) ⟨113759, by rfl⟩) R227519
theorem R512831 : Reach 512831 := rs (se 1 (by rfl) ⟨384623, by rfl⟩) R769247
theorem R152489 : Reach 152489 := rs (se 2 (by rfl) ⟨57183, by rfl⟩) R114367
theorem R87455 : Reach 87455 := rs (se 1 (by rfl) ⟨65591, by rfl⟩) R131183
theorem R87519 : Reach 87519 := rs (se 1 (by rfl) ⟨65639, by rfl⟩) R131279
theorem R87975 : Reach 87975 := rs (se 1 (by rfl) ⟨65981, by rfl⟩) R131963
theorem R88383 : Reach 88383 := rs (se 1 (by rfl) ⟨66287, by rfl⟩) R132575
theorem R1006019 : Reach 1006019 := rs (se 1 (by rfl) ⟨754514, by rfl⟩) R1509029
theorem R383545 : Reach 383545 := rs (se 2 (by rfl) ⟨143829, by rfl⟩) R287659
theorem R88827 : Reach 88827 := rs (se 1 (by rfl) ⟨66620, by rfl⟩) R133241
theorem R89191 : Reach 89191 := rs (se 1 (by rfl) ⟨66893, by rfl⟩) R133787
theorem R744673 : Reach 744673 := rs (se 2 (by rfl) ⟨279252, by rfl⟩) R558505
theorem R89447 : Reach 89447 := rs (se 1 (by rfl) ⟨67085, by rfl⟩) R134171
theorem R89503 : Reach 89503 := rs (se 1 (by rfl) ⟨67127, by rfl⟩) R134255
theorem R89535 : Reach 89535 := rs (se 1 (by rfl) ⟨67151, by rfl⟩) R134303
theorem R777701 : Reach 777701 := rs (se 4 (by rfl) ⟨72909, by rfl⟩) R145819
theorem R89755 : Reach 89755 := rs (se 1 (by rfl) ⟨67316, by rfl⟩) R134633
theorem R89983 : Reach 89983 := rs (se 1 (by rfl) ⟨67487, by rfl⟩) R134975
theorem R90015 : Reach 90015 := rs (se 1 (by rfl) ⟨67511, by rfl⟩) R135023
theorem R90047 : Reach 90047 := rs (se 1 (by rfl) ⟨67535, by rfl⟩) R135071
theorem R90671 : Reach 90671 := rs (se 1 (by rfl) ⟨68003, by rfl⟩) R136007
theorem R90751 : Reach 90751 := rs (se 1 (by rfl) ⟨68063, by rfl⟩) R136127
theorem R90815 : Reach 90815 := rs (se 1 (by rfl) ⟨68111, by rfl⟩) R136223
theorem R90971 : Reach 90971 := rs (se 1 (by rfl) ⟨68228, by rfl⟩) R136457
theorem R451655 : Reach 451655 := rs (se 1 (by rfl) ⟨338741, by rfl⟩) R677483
theorem R1600361 : Reach 1600361 := rs (se 2 (by rfl) ⟨600135, by rfl⟩) R1200271
theorem R290017 : Reach 290017 := rs (se 2 (by rfl) ⟨108756, by rfl⟩) R217513
theorem R193337 : Reach 193337 := rs (se 2 (by rfl) ⟨72501, by rfl⟩) R145003
theorem R1373231 : Reach 1373231 := rs (se 1 (by rfl) ⟨1029923, by rfl⟩) R2059847
theorem R226871 : Reach 226871 := rs (se 1 (by rfl) ⟨170153, by rfl⟩) R340307
theorem R1865375 : Reach 1865375 := rs (se 1 (by rfl) ⟨1399031, by rfl⟩) R2798063
theorem R358879 : Reach 358879 := rs (se 1 (by rfl) ⟨269159, by rfl⟩) R538319
theorem R228217 : Reach 228217 := rs (se 2 (by rfl) ⟨85581, by rfl⟩) R171163
theorem R228521 : Reach 228521 := rs (se 2 (by rfl) ⟨85695, by rfl⟩) R171391
theorem R654905 : Reach 654905 := rs (se 2 (by rfl) ⟨245589, by rfl⟩) R491179
theorem R196217 : Reach 196217 := rs (se 2 (by rfl) ⟨73581, by rfl⟩) R147163
theorem R294623 : Reach 294623 := rs (se 1 (by rfl) ⟨220967, by rfl⟩) R441935
theorem R131255 : Reach 131255 := rs (se 1 (by rfl) ⟨98441, by rfl⟩) R196883
theorem R196847 : Reach 196847 := rs (se 1 (by rfl) ⟨147635, by rfl⟩) R295271
theorem R131399 : Reach 131399 := rs (se 1 (by rfl) ⟨98549, by rfl⟩) R197099
theorem R131753 : Reach 131753 := rs (se 2 (by rfl) ⟨49407, by rfl⟩) R98815
theorem R361207 : Reach 361207 := rs (se 1 (by rfl) ⟨270905, by rfl⟩) R541811
theorem R131879 : Reach 131879 := rs (se 1 (by rfl) ⟨98909, by rfl⟩) R197819
theorem R132089 : Reach 132089 := rs (se 2 (by rfl) ⟨49533, by rfl⟩) R99067
theorem R132473 : Reach 132473 := rs (se 2 (by rfl) ⟨49677, by rfl⟩) R99355
theorem R132815 : Reach 132815 := rs (se 1 (by rfl) ⟨99611, by rfl⟩) R199223
theorem R1017683 : Reach 1017683 := rs (se 1 (by rfl) ⟨763262, by rfl⟩) R1526525
theorem R690059 : Reach 690059 := rs (se 1 (by rfl) ⟨517544, by rfl⟩) R1035089
theorem R133115 : Reach 133115 := rs (se 1 (by rfl) ⟨99836, by rfl⟩) R199673
theorem R101119 : Reach 101119 := rs (se 1 (by rfl) ⟨75839, by rfl⟩) R151679
theorem R101659 : Reach 101659 := rs (se 1 (by rfl) ⟨76244, by rfl⟩) R152489
theorem R134777 : Reach 134777 := rs (se 2 (by rfl) ⟨50541, by rfl⟩) R101083
theorem R301103 : Reach 301103 := rs (se 1 (by rfl) ⟨225827, by rfl⟩) R451655
theorem R203759 : Reach 203759 := rs (se 1 (by rfl) ⟨152819, by rfl⟩) R305639
theorem R203867 : Reach 203867 := rs (se 1 (by rfl) ⟨152900, by rfl⟩) R305801
theorem R205775 : Reach 205775 := rs (se 1 (by rfl) ⟨154331, by rfl⟩) R308663
theorem R304289 : Reach 304289 := rs (se 2 (by rfl) ⟨114108, by rfl⟩) R228217
theorem R992897 : Reach 992897 := rs (se 2 (by rfl) ⟨372336, by rfl⟩) R744673
theorem R436603 : Reach 436603 := rs (se 1 (by rfl) ⟨327452, by rfl⟩) R654905
theorem R502463 : Reach 502463 := rs (se 1 (by rfl) ⟨376847, by rfl⟩) R753695
theorem R600791 : Reach 600791 := rs (se 1 (by rfl) ⟨450593, by rfl⟩) R901187
theorem R5779421 : Reach 5779421 := rs (se 3 (by rfl) ⟨1083641, by rfl⟩) R2167283
theorem R143471 : Reach 143471 := rs (se 1 (by rfl) ⟨107603, by rfl⟩) R215207
theorem R243167 : Reach 243167 := rs (se 1 (by rfl) ⟨182375, by rfl⟩) R364751
theorem R14005993 : Reach 14005993 := rs (se 2 (by rfl) ⟨5252247, by rfl⟩) R10504495
theorem R5028155 : Reach 5028155 := rs (se 1 (by rfl) ⟨3771116, by rfl⟩) R7542233
theorem R670679 : Reach 670679 := rs (se 1 (by rfl) ⟨503009, by rfl⟩) R1006019
theorem R507019 : Reach 507019 := rs (se 1 (by rfl) ⟨380264, by rfl⟩) R760529
theorem R507521 : Reach 507521 := rs (se 2 (by rfl) ⟨190320, by rfl⟩) R380641
theorem R114463 : Reach 114463 := rs (se 1 (by rfl) ⟨85847, by rfl⟩) R171695
theorem R377903 : Reach 377903 := rs (se 1 (by rfl) ⟨283427, by rfl⟩) R566855
theorem R1066907 : Reach 1066907 := rs (se 1 (by rfl) ⟨800180, by rfl⟩) R1600361
theorem R478505 : Reach 478505 := rs (se 2 (by rfl) ⟨179439, by rfl⟩) R358879
theorem R511393 : Reach 511393 := rs (se 2 (by rfl) ⟨191772, by rfl⟩) R383545
theorem R151247 : Reach 151247 := rs (se 1 (by rfl) ⟨113435, by rfl⟩) R226871
theorem R774107 : Reach 774107 := rs (se 1 (by rfl) ⟨580580, by rfl⟩) R1161161
theorem R577961 : Reach 577961 := rs (se 2 (by rfl) ⟨216735, by rfl⟩) R433471
theorem R152347 : Reach 152347 := rs (se 1 (by rfl) ⟨114260, by rfl⟩) R228521
theorem R251039 : Reach 251039 := rs (se 1 (by rfl) ⟨188279, by rfl⟩) R376559
theorem R579419 : Reach 579419 := rs (se 1 (by rfl) ⟨434564, by rfl⟩) R869129
theorem R874435 : Reach 874435 := rs (se 1 (by rfl) ⟨655826, by rfl⟩) R1311653
theorem R88807 : Reach 88807 := rs (se 1 (by rfl) ⟨66605, by rfl⟩) R133211
theorem R88815 : Reach 88815 := rs (se 1 (by rfl) ⟨66611, by rfl⟩) R133223
theorem R89115 : Reach 89115 := rs (se 1 (by rfl) ⟨66836, by rfl⟩) R133673
theorem R1367549 : Reach 1367549 := rs (se 3 (by rfl) ⟨256415, by rfl⟩) R512831
theorem R89727 : Reach 89727 := rs (se 1 (by rfl) ⟨67295, by rfl⟩) R134591
theorem R647003 : Reach 647003 := rs (se 1 (by rfl) ⟨485252, by rfl⟩) R970505
theorem R3661949 : Reach 3661949 := rs (se 3 (by rfl) ⟨686615, by rfl⟩) R1373231
theorem R1597967 : Reach 1597967 := rs (se 1 (by rfl) ⟨1198475, by rfl⟩) R2396951
theorem R386689 : Reach 386689 := rs (se 2 (by rfl) ⟨145008, by rfl⟩) R290017
theorem R419995 : Reach 419995 := rs (se 1 (by rfl) ⟨314996, by rfl⟩) R629993
theorem R518467 : Reach 518467 := rs (se 1 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R224603 : Reach 224603 := rs (se 1 (by rfl) ⟨168452, by rfl⟩) R336905
theorem R29652439 : Reach 29652439 := rs (se 1 (by rfl) ⟨22239329, by rfl⟩) R44478659
theorem R128891 : Reach 128891 := rs (se 1 (by rfl) ⟨96668, by rfl⟩) R193337
theorem R424187 : Reach 424187 := rs (se 1 (by rfl) ⟨318140, by rfl⟩) R636281
theorem R1243583 : Reach 1243583 := rs (se 1 (by rfl) ⟨932687, by rfl⟩) R1865375
theorem R130811 : Reach 130811 := rs (se 1 (by rfl) ⟨98108, by rfl⟩) R196217
theorem R196415 : Reach 196415 := rs (se 1 (by rfl) ⟨147311, by rfl⟩) R294623
theorem R131231 : Reach 131231 := rs (se 1 (by rfl) ⟨98423, by rfl⟩) R196847
theorem R9765197 : Reach 9765197 := rs (se 3 (by rfl) ⟨1830974, by rfl⟩) R3661949
theorem R100831 : Reach 100831 := rs (se 1 (by rfl) ⟨75623, by rfl⟩) R151247
theorem R559993 : Reach 559993 := rs (se 2 (by rfl) ⟨209997, by rfl⟩) R419995
theorem R691289 : Reach 691289 := rs (se 2 (by rfl) ⟨259233, by rfl⟩) R518467
theorem R167359 : Reach 167359 := rs (se 1 (by rfl) ⟨125519, by rfl⟩) R251039
theorem R134825 : Reach 134825 := rs (se 2 (by rfl) ⟨50559, by rfl⟩) R101119
theorem R200735 : Reach 200735 := rs (se 1 (by rfl) ⟨150551, by rfl⟩) R301103
theorem R135545 : Reach 135545 := rs (se 2 (by rfl) ⟨50829, by rfl⟩) R101659
theorem R135839 : Reach 135839 := rs (se 1 (by rfl) ⟨101879, by rfl⟩) R203759
theorem R135911 : Reach 135911 := rs (se 1 (by rfl) ⟨101933, by rfl⟩) R203867
theorem R2593781 : Reach 2593781 := rs (se 5 (by rfl) ⟨121583, by rfl⟩) R243167
theorem R1840157 : Reach 1840157 := rs (se 3 (by rfl) ⟨345029, by rfl⟩) R690059
theorem R431335 : Reach 431335 := rs (se 1 (by rfl) ⟨323501, by rfl⟩) R647003
theorem R137183 : Reach 137183 := rs (se 1 (by rfl) ⟨102887, by rfl⟩) R205775
theorem R202859 : Reach 202859 := rs (se 1 (by rfl) ⟨152144, by rfl⟩) R304289
theorem R203129 : Reach 203129 := rs (se 2 (by rfl) ⟨76173, by rfl⟩) R152347
theorem R661931 : Reach 661931 := rs (se 1 (by rfl) ⟨496448, by rfl⟩) R992897
theorem R334975 : Reach 334975 := rs (se 1 (by rfl) ⟨251231, by rfl⟩) R502463
theorem R3352103 : Reach 3352103 := rs (se 1 (by rfl) ⟨2514077, by rfl⟩) R5028155
theorem R829055 : Reach 829055 := rs (se 1 (by rfl) ⟨621791, by rfl⟩) R1243583
theorem R338347 : Reach 338347 := rs (se 1 (by rfl) ⟨253760, by rfl⟩) R507521
theorem R343709 : Reach 343709 := rs (se 3 (by rfl) ⟨64445, by rfl⟩) R128891
theorem R1065311 : Reach 1065311 := rs (se 1 (by rfl) ⟨798983, by rfl⟩) R1597967
theorem R39536585 : Reach 39536585 := rs (se 2 (by rfl) ⟨14826219, by rfl⟩) R29652439
theorem R149735 : Reach 149735 := rs (se 1 (by rfl) ⟨112301, by rfl⟩) R224603
theorem R1165913 : Reach 1165913 := rs (se 2 (by rfl) ⟨437217, by rfl⟩) R874435
theorem R3852947 : Reach 3852947 := rs (se 1 (by rfl) ⟨2889710, by rfl⟩) R5779421
theorem R282791 : Reach 282791 := rs (se 1 (by rfl) ⟨212093, by rfl⟩) R424187
theorem R676025 : Reach 676025 := rs (se 2 (by rfl) ⟨253509, by rfl⟩) R507019
theorem R447119 : Reach 447119 := rs (se 1 (by rfl) ⟨335339, by rfl⟩) R670679
theorem R152617 : Reach 152617 := rs (se 2 (by rfl) ⟨57231, by rfl⟩) R114463
theorem R87207 : Reach 87207 := rs (se 1 (by rfl) ⟨65405, by rfl⟩) R130811
theorem R87503 : Reach 87503 := rs (se 1 (by rfl) ⟨65627, by rfl⟩) R131255
theorem R87599 : Reach 87599 := rs (se 1 (by rfl) ⟨65699, by rfl⟩) R131399
theorem R382589 : Reach 382589 := rs (se 3 (by rfl) ⟨71735, by rfl⟩) R143471
theorem R87835 : Reach 87835 := rs (se 1 (by rfl) ⟨65876, by rfl⟩) R131753
theorem R87919 : Reach 87919 := rs (se 1 (by rfl) ⟨65939, by rfl⟩) R131879
theorem R88059 : Reach 88059 := rs (se 1 (by rfl) ⟨66044, by rfl⟩) R132089
theorem R251935 : Reach 251935 := rs (se 1 (by rfl) ⟨188951, by rfl⟩) R377903
theorem R88315 : Reach 88315 := rs (se 1 (by rfl) ⟨66236, by rfl⟩) R132473
theorem R481609 : Reach 481609 := rs (se 2 (by rfl) ⟨180603, by rfl⟩) R361207
theorem R88543 : Reach 88543 := rs (se 1 (by rfl) ⟨66407, by rfl⟩) R132815
theorem R678455 : Reach 678455 := rs (se 1 (by rfl) ⟨508841, by rfl⟩) R1017683
theorem R711271 : Reach 711271 := rs (se 1 (by rfl) ⟨533453, by rfl⟩) R1066907
theorem R88743 : Reach 88743 := rs (se 1 (by rfl) ⟨66557, by rfl⟩) R133115
theorem R515585 : Reach 515585 := rs (se 2 (by rfl) ⟨193344, by rfl⟩) R386689
theorem R89851 : Reach 89851 := rs (se 1 (by rfl) ⟨67388, by rfl⟩) R134777
theorem R516071 : Reach 516071 := rs (se 1 (by rfl) ⟨387053, by rfl⟩) R774107
theorem R385307 : Reach 385307 := rs (se 1 (by rfl) ⟨288980, by rfl⟩) R577961
theorem R582137 : Reach 582137 := rs (se 2 (by rfl) ⟨218301, by rfl⟩) R436603
theorem R386279 : Reach 386279 := rs (se 1 (by rfl) ⟨289709, by rfl⟩) R579419
theorem R681857 : Reach 681857 := rs (se 2 (by rfl) ⟨255696, by rfl⟩) R511393
theorem R911699 : Reach 911699 := rs (se 1 (by rfl) ⟨683774, by rfl⟩) R1367549
theorem R1602109 : Reach 1602109 := rs (se 3 (by rfl) ⟨300395, by rfl⟩) R600791
theorem R18674657 : Reach 18674657 := rs (se 2 (by rfl) ⟨7002996, by rfl⟩) R14005993
theorem R1276013 : Reach 1276013 := rs (se 3 (by rfl) ⟨239252, by rfl⟩) R478505
theorem R130943 : Reach 130943 := rs (se 1 (by rfl) ⟨98207, by rfl⟩) R196415
theorem R5374613 : Reach 5374613 := rs (se 6 (by rfl) ⟨125967, by rfl⟩) R251935
theorem R99823 : Reach 99823 := rs (se 1 (by rfl) ⟨74867, by rfl⟩) R149735
theorem R460859 : Reach 460859 := rs (se 1 (by rfl) ⟨345644, by rfl⟩) R691289
theorem R1804517 : Reach 1804517 := rs (se 4 (by rfl) ⟨169173, by rfl⟩) R338347
theorem R133823 : Reach 133823 := rs (se 1 (by rfl) ⟨100367, by rfl⟩) R200735
theorem R298079 : Reach 298079 := rs (se 1 (by rfl) ⟨223559, by rfl⟩) R447119
theorem R134441 : Reach 134441 := rs (se 2 (by rfl) ⟨50415, by rfl⟩) R100831
theorem R135239 : Reach 135239 := rs (se 1 (by rfl) ⟨101429, by rfl⟩) R202859
theorem R135419 : Reach 135419 := rs (se 1 (by rfl) ⟨101564, by rfl⟩) R203129
theorem R2136145 : Reach 2136145 := rs (se 2 (by rfl) ⟨801054, by rfl⟩) R1602109
theorem R2234735 : Reach 2234735 := rs (se 1 (by rfl) ⟨1676051, by rfl⟩) R3352103
theorem R203489 : Reach 203489 := rs (se 2 (by rfl) ⟨76308, by rfl⟩) R152617
theorem R26357723 : Reach 26357723 := rs (se 1 (by rfl) ⟨19768292, by rfl⟩) R39536585
theorem R2568581 : Reach 2568581 := rs (se 4 (by rfl) ⟨240804, by rfl⟩) R481609
theorem R2568631 : Reach 2568631 := rs (se 1 (by rfl) ⟨1926473, by rfl⟩) R3852947
theorem R1226771 : Reach 1226771 := rs (se 1 (by rfl) ⟨920078, by rfl⟩) R1840157
theorem R441287 : Reach 441287 := rs (se 1 (by rfl) ⟨330965, by rfl⟩) R661931
theorem R343723 : Reach 343723 := rs (se 1 (by rfl) ⟨257792, by rfl⟩) R515585
theorem R344047 : Reach 344047 := rs (se 1 (by rfl) ⟨258035, by rfl⟩) R516071
theorem R607799 : Reach 607799 := rs (se 1 (by rfl) ⟨455849, by rfl⟩) R911699
theorem R575113 : Reach 575113 := rs (se 2 (by rfl) ⟨215667, by rfl⟩) R431335
theorem R446633 : Reach 446633 := rs (se 2 (by rfl) ⟨167487, by rfl⟩) R334975
theorem R1463285 : Reach 1463285 := rs (se 5 (by rfl) ⟨68591, by rfl⟩) R137183
theorem R87295 : Reach 87295 := rs (se 1 (by rfl) ⟨65471, by rfl⟩) R130943
theorem R87487 : Reach 87487 := rs (se 1 (by rfl) ⟨65615, by rfl⟩) R131231
theorem R6510131 : Reach 6510131 := rs (se 1 (by rfl) ⟨4882598, by rfl⟩) R9765197
theorem R710207 : Reach 710207 := rs (se 1 (by rfl) ⟨532655, by rfl⟩) R1065311
theorem R777275 : Reach 777275 := rs (se 1 (by rfl) ⟨582956, by rfl⟩) R1165913
theorem R89883 : Reach 89883 := rs (se 1 (by rfl) ⟨67412, by rfl⟩) R134825
theorem R188527 : Reach 188527 := rs (se 1 (by rfl) ⟨141395, by rfl⟩) R282791
theorem R450683 : Reach 450683 := rs (se 1 (by rfl) ⟨338012, by rfl⟩) R676025
theorem R90363 : Reach 90363 := rs (se 1 (by rfl) ⟨67772, by rfl⟩) R135545
theorem R90559 : Reach 90559 := rs (se 1 (by rfl) ⟨67919, by rfl⟩) R135839
theorem R90607 : Reach 90607 := rs (se 1 (by rfl) ⟨67955, by rfl⟩) R135911
theorem R1729187 : Reach 1729187 := rs (se 1 (by rfl) ⟨1296890, by rfl⟩) R2593781
theorem R255059 : Reach 255059 := rs (se 1 (by rfl) ⟨191294, by rfl⟩) R382589
theorem R746657 : Reach 746657 := rs (se 2 (by rfl) ⟨279996, by rfl⟩) R559993
theorem R452303 : Reach 452303 := rs (se 1 (by rfl) ⟨339227, by rfl⟩) R678455
theorem R223145 : Reach 223145 := rs (se 2 (by rfl) ⟨83679, by rfl⟩) R167359
theorem R256871 : Reach 256871 := rs (se 1 (by rfl) ⟨192653, by rfl⟩) R385307
theorem R388091 : Reach 388091 := rs (se 1 (by rfl) ⟨291068, by rfl⟩) R582137
theorem R257519 : Reach 257519 := rs (se 1 (by rfl) ⟨193139, by rfl⟩) R386279
theorem R552703 : Reach 552703 := rs (se 1 (by rfl) ⟨414527, by rfl⟩) R829055
theorem R454571 : Reach 454571 := rs (se 1 (by rfl) ⟨340928, by rfl⟩) R681857
theorem R12449771 : Reach 12449771 := rs (se 1 (by rfl) ⟨9337328, by rfl⟩) R18674657
theorem R948361 : Reach 948361 := rs (se 2 (by rfl) ⟨355635, by rfl⟩) R711271
theorem R850675 : Reach 850675 := rs (se 1 (by rfl) ⟨638006, by rfl⟩) R1276013
theorem R229139 : Reach 229139 := rs (se 1 (by rfl) ⟨171854, by rfl⟩) R343709
theorem R4915829 : Reach 4915829 := rs (se 5 (by rfl) ⟨230429, by rfl⟩) R460859
theorem R133097 : Reach 133097 := rs (se 2 (by rfl) ⟨49911, by rfl⟩) R99823
theorem R198719 : Reach 198719 := rs (se 1 (by rfl) ⟨149039, by rfl⟩) R298079
theorem R297755 : Reach 297755 := rs (se 1 (by rfl) ⟨223316, by rfl⟩) R446633
theorem R135659 : Reach 135659 := rs (se 1 (by rfl) ⟨101744, by rfl⟩) R203489
theorem R300455 : Reach 300455 := rs (se 1 (by rfl) ⟨225341, by rfl⟩) R450683
theorem R1152791 : Reach 1152791 := rs (se 1 (by rfl) ⟨864593, by rfl⟩) R1729187
theorem R170039 : Reach 170039 := rs (se 1 (by rfl) ⟨127529, by rfl⟩) R255059
theorem R497771 : Reach 497771 := rs (se 1 (by rfl) ⟨373328, by rfl⟩) R746657
theorem R301535 : Reach 301535 := rs (se 1 (by rfl) ⟨226151, by rfl⟩) R452303
theorem R171247 : Reach 171247 := rs (se 1 (by rfl) ⟨128435, by rfl⟩) R256871
theorem R303047 : Reach 303047 := rs (se 1 (by rfl) ⟨227285, by rfl⟩) R454571
theorem R17571815 : Reach 17571815 := rs (se 1 (by rfl) ⟨13178861, by rfl⟩) R26357723
theorem R1712387 : Reach 1712387 := rs (se 1 (by rfl) ⟨1284290, by rfl⟩) R2568581
theorem R8299847 : Reach 8299847 := rs (se 1 (by rfl) ⟨6224885, by rfl⟩) R12449771
theorem R405199 : Reach 405199 := rs (se 1 (by rfl) ⟨303899, by rfl⟩) R607799
theorem R14332301 : Reach 14332301 := rs (se 3 (by rfl) ⟨2687306, by rfl⟩) R5374613
theorem R766817 : Reach 766817 := rs (se 2 (by rfl) ⟨287556, by rfl⟩) R575113
theorem R4340087 : Reach 4340087 := rs (se 1 (by rfl) ⟨3255065, by rfl⟩) R6510131
theorem R473471 : Reach 473471 := rs (se 1 (by rfl) ⟨355103, by rfl⟩) R710207
theorem R1489823 : Reach 1489823 := rs (se 1 (by rfl) ⟨1117367, by rfl⟩) R2234735
theorem R736937 : Reach 736937 := rs (se 2 (by rfl) ⟨276351, by rfl⟩) R552703
theorem R3424841 : Reach 3424841 := rs (se 2 (by rfl) ⟨1284315, by rfl⟩) R2568631
theorem R148763 : Reach 148763 := rs (se 1 (by rfl) ⟨111572, by rfl⟩) R223145
theorem R1264481 : Reach 1264481 := rs (se 2 (by rfl) ⟨474180, by rfl⟩) R948361
theorem R1134233 : Reach 1134233 := rs (se 2 (by rfl) ⟨425337, by rfl⟩) R850675
theorem R152759 : Reach 152759 := rs (se 1 (by rfl) ⟨114569, by rfl⟩) R229139
theorem R251369 : Reach 251369 := rs (se 2 (by rfl) ⟨94263, by rfl⟩) R188527
theorem R1203011 : Reach 1203011 := rs (se 1 (by rfl) ⟨902258, by rfl⟩) R1804517
theorem R89215 : Reach 89215 := rs (se 1 (by rfl) ⟨66911, by rfl⟩) R133823
theorem R89627 : Reach 89627 := rs (se 1 (by rfl) ⟨67220, by rfl⟩) R134441
theorem R90159 : Reach 90159 := rs (se 1 (by rfl) ⟨67619, by rfl⟩) R135239
theorem R90279 : Reach 90279 := rs (se 1 (by rfl) ⟨67709, by rfl⟩) R135419
theorem R975523 : Reach 975523 := rs (se 1 (by rfl) ⟨731642, by rfl⟩) R1463285
theorem R518183 : Reach 518183 := rs (se 1 (by rfl) ⟨388637, by rfl⟩) R777275
theorem R258727 : Reach 258727 := rs (se 1 (by rfl) ⟨194045, by rfl⟩) R388091
theorem R2848193 : Reach 2848193 := rs (se 2 (by rfl) ⟨1068072, by rfl⟩) R2136145
theorem R686717 : Reach 686717 := rs (se 3 (by rfl) ⟨128759, by rfl⟩) R257519
theorem R817847 : Reach 817847 := rs (se 1 (by rfl) ⟨613385, by rfl⟩) R1226771
theorem R294191 : Reach 294191 := rs (se 1 (by rfl) ⟨220643, by rfl⟩) R441287
theorem R458297 : Reach 458297 := rs (se 2 (by rfl) ⟨171861, by rfl⟩) R343723
theorem R458729 : Reach 458729 := rs (se 2 (by rfl) ⟨172023, by rfl⟩) R344047
theorem R3277219 : Reach 3277219 := rs (se 1 (by rfl) ⟨2457914, by rfl⟩) R4915829
theorem R99175 : Reach 99175 := rs (se 1 (by rfl) ⟨74381, by rfl⟩) R148763
theorem R132479 : Reach 132479 := rs (se 1 (by rfl) ⟨99359, by rfl⟩) R198719
theorem R198503 : Reach 198503 := rs (se 1 (by rfl) ⟨148877, by rfl⟩) R297755
theorem R756155 : Reach 756155 := rs (se 1 (by rfl) ⟨567116, by rfl⟩) R1134233
theorem R101839 : Reach 101839 := rs (se 1 (by rfl) ⟨76379, by rfl⟩) R152759
theorem R200303 : Reach 200303 := rs (se 1 (by rfl) ⟨150227, by rfl⟩) R300455
theorem R167579 : Reach 167579 := rs (se 1 (by rfl) ⟨125684, by rfl⟩) R251369
theorem R331847 : Reach 331847 := rs (se 1 (by rfl) ⟨248885, by rfl⟩) R497771
theorem R201023 : Reach 201023 := rs (se 1 (by rfl) ⟨150767, by rfl⟩) R301535
theorem R202031 : Reach 202031 := rs (se 1 (by rfl) ⟨151523, by rfl⟩) R303047
theorem R2893391 : Reach 2893391 := rs (se 1 (by rfl) ⟨2170043, by rfl⟩) R4340087
theorem R993215 : Reach 993215 := rs (se 1 (by rfl) ⟨744911, by rfl⟩) R1489823
theorem R305531 : Reach 305531 := rs (se 1 (by rfl) ⟨229148, by rfl⟩) R458297
theorem R305819 : Reach 305819 := rs (se 1 (by rfl) ⟨229364, by rfl⟩) R458729
theorem R4566365 : Reach 4566365 := rs (se 3 (by rfl) ⟨856193, by rfl⟩) R1712387
theorem R768527 : Reach 768527 := rs (se 1 (by rfl) ⟨576395, by rfl⟩) R1152791
theorem R802007 : Reach 802007 := rs (se 1 (by rfl) ⟨601505, by rfl⟩) R1203011
theorem R540265 : Reach 540265 := rs (se 2 (by rfl) ⟨202599, by rfl⟩) R405199
theorem R11714543 : Reach 11714543 := rs (se 1 (by rfl) ⟨8785907, by rfl⟩) R17571815
theorem R344969 : Reach 344969 := rs (se 2 (by rfl) ⟨129363, by rfl⟩) R258727
theorem R345455 : Reach 345455 := rs (se 1 (by rfl) ⟨259091, by rfl⟩) R518183
theorem R9554867 : Reach 9554867 := rs (se 1 (by rfl) ⟨7166150, by rfl⟩) R14332301
theorem R511211 : Reach 511211 := rs (se 1 (by rfl) ⟨383408, by rfl⟩) R766817
theorem R315647 : Reach 315647 := rs (se 1 (by rfl) ⟨236735, by rfl⟩) R473471
theorem R545231 : Reach 545231 := rs (se 1 (by rfl) ⟨408923, by rfl⟩) R817847
theorem R2283227 : Reach 2283227 := rs (se 1 (by rfl) ⟨1712420, by rfl⟩) R3424841
theorem R1300697 : Reach 1300697 := rs (se 2 (by rfl) ⟨487761, by rfl⟩) R975523
theorem R88731 : Reach 88731 := rs (se 1 (by rfl) ⟨66548, by rfl⟩) R133097
theorem R842987 : Reach 842987 := rs (se 1 (by rfl) ⟨632240, by rfl⟩) R1264481
theorem R90439 : Reach 90439 := rs (se 1 (by rfl) ⟨67829, by rfl⟩) R135659
theorem R453437 : Reach 453437 := rs (se 3 (by rfl) ⟨85019, by rfl⟩) R170039
theorem R5533231 : Reach 5533231 := rs (se 1 (by rfl) ⟨4149923, by rfl⟩) R8299847
theorem R1898795 : Reach 1898795 := rs (se 1 (by rfl) ⟨1424096, by rfl⟩) R2848193
theorem R228329 : Reach 228329 := rs (se 2 (by rfl) ⟨85623, by rfl⟩) R171247
theorem R457811 : Reach 457811 := rs (se 1 (by rfl) ⟨343358, by rfl⟩) R686717
theorem R196127 : Reach 196127 := rs (se 1 (by rfl) ⟨147095, by rfl⟩) R294191
theorem R491291 : Reach 491291 := rs (se 1 (by rfl) ⟨368468, by rfl⟩) R736937
theorem R229979 : Reach 229979 := rs (se 1 (by rfl) ⟨172484, by rfl⟩) R344969
theorem R230303 : Reach 230303 := rs (se 1 (by rfl) ⟨172727, by rfl⟩) R345455
theorem R132233 : Reach 132233 := rs (se 2 (by rfl) ⟨49587, by rfl⟩) R99175
theorem R132335 : Reach 132335 := rs (se 1 (by rfl) ⟨99251, by rfl⟩) R198503
theorem R133535 : Reach 133535 := rs (se 1 (by rfl) ⟨100151, by rfl⟩) R200303
theorem R134015 : Reach 134015 := rs (se 1 (by rfl) ⟨100511, by rfl⟩) R201023
theorem R363487 : Reach 363487 := rs (se 1 (by rfl) ⟨272615, by rfl⟩) R545231
theorem R134687 : Reach 134687 := rs (se 1 (by rfl) ⟨101015, by rfl⟩) R202031
theorem R135785 : Reach 135785 := rs (se 2 (by rfl) ⟨50919, by rfl⟩) R101839
theorem R7377641 : Reach 7377641 := rs (se 2 (by rfl) ⟨2766615, by rfl⟩) R5533231
theorem R561991 : Reach 561991 := rs (se 1 (by rfl) ⟨421493, by rfl⟩) R842987
theorem R662143 : Reach 662143 := rs (se 1 (by rfl) ⟨496607, by rfl⟩) R993215
theorem R203687 : Reach 203687 := rs (se 1 (by rfl) ⟨152765, by rfl⟩) R305531
theorem R203879 : Reach 203879 := rs (se 1 (by rfl) ⟨152909, by rfl⟩) R305819
theorem R302291 : Reach 302291 := rs (se 1 (by rfl) ⟨226718, by rfl⟩) R453437
theorem R305207 : Reach 305207 := rs (se 1 (by rfl) ⟨228905, by rfl⟩) R457811
theorem R534671 : Reach 534671 := rs (se 1 (by rfl) ⟨401003, by rfl⟩) R802007
theorem R7809695 : Reach 7809695 := rs (se 1 (by rfl) ⟨5857271, by rfl⟩) R11714543
theorem R4369625 : Reach 4369625 := rs (se 2 (by rfl) ⟨1638609, by rfl⟩) R3277219
theorem R504103 : Reach 504103 := rs (se 1 (by rfl) ⟨378077, by rfl⟩) R756155
theorem R6369911 : Reach 6369911 := rs (se 1 (by rfl) ⟨4777433, by rfl⟩) R9554867
theorem R340807 : Reach 340807 := rs (se 1 (by rfl) ⟨255605, by rfl⟩) R511211
theorem R111719 : Reach 111719 := rs (se 1 (by rfl) ⟨83789, by rfl⟩) R167579
theorem R210431 : Reach 210431 := rs (se 1 (by rfl) ⟨157823, by rfl⟩) R315647
theorem R1522151 : Reach 1522151 := rs (se 1 (by rfl) ⟨1141613, by rfl⟩) R2283227
theorem R867131 : Reach 867131 := rs (se 1 (by rfl) ⟨650348, by rfl⟩) R1300697
theorem R1265863 : Reach 1265863 := rs (se 1 (by rfl) ⟨949397, by rfl⟩) R1898795
theorem R512351 : Reach 512351 := rs (se 1 (by rfl) ⟨384263, by rfl⟩) R768527
theorem R152219 : Reach 152219 := rs (se 1 (by rfl) ⟨114164, by rfl⟩) R228329
theorem R88319 : Reach 88319 := rs (se 1 (by rfl) ⟨66239, by rfl⟩) R132479
theorem R221231 : Reach 221231 := rs (se 1 (by rfl) ⟨165923, by rfl⟩) R331847
theorem R1928927 : Reach 1928927 := rs (se 1 (by rfl) ⟨1446695, by rfl⟩) R2893391
theorem R3044243 : Reach 3044243 := rs (se 1 (by rfl) ⟨2283182, by rfl⟩) R4566365
theorem R720353 : Reach 720353 := rs (se 2 (by rfl) ⟨270132, by rfl⟩) R540265
theorem R130751 : Reach 130751 := rs (se 1 (by rfl) ⟨98063, by rfl⟩) R196127
theorem R327527 : Reach 327527 := rs (se 1 (by rfl) ⟨245645, by rfl⟩) R491291
theorem R297917 : Reach 297917 := rs (se 3 (by rfl) ⟨55859, by rfl⟩) R111719
theorem R101479 : Reach 101479 := rs (se 1 (by rfl) ⟨76109, by rfl⟩) R152219
theorem R4918427 : Reach 4918427 := rs (se 1 (by rfl) ⟨3688820, by rfl⟩) R7377641
theorem R135791 : Reach 135791 := rs (se 1 (by rfl) ⟨101843, by rfl⟩) R203687
theorem R135919 : Reach 135919 := rs (se 1 (by rfl) ⟨101939, by rfl⟩) R203879
theorem R201527 : Reach 201527 := rs (se 1 (by rfl) ⟨151145, by rfl⟩) R302291
theorem R203471 : Reach 203471 := rs (se 1 (by rfl) ⟨152603, by rfl⟩) R305207
theorem R1285951 : Reach 1285951 := rs (se 1 (by rfl) ⟨964463, by rfl⟩) R1928927
theorem R140287 : Reach 140287 := rs (se 1 (by rfl) ⟨105215, by rfl⟩) R210431
theorem R341567 : Reach 341567 := rs (se 1 (by rfl) ⟨256175, by rfl⟩) R512351
theorem R147487 : Reach 147487 := rs (se 1 (by rfl) ⟨110615, by rfl⟩) R221231
theorem R1687817 : Reach 1687817 := rs (se 2 (by rfl) ⟨632931, by rfl⟩) R1265863
theorem R672137 : Reach 672137 := rs (se 2 (by rfl) ⟨252051, by rfl⟩) R504103
theorem R4246607 : Reach 4246607 := rs (se 1 (by rfl) ⟨3184955, by rfl⟩) R6369911
theorem R578087 : Reach 578087 := rs (se 1 (by rfl) ⟨433565, by rfl⟩) R867131
theorem R480235 : Reach 480235 := rs (se 1 (by rfl) ⟨360176, by rfl⟩) R720353
theorem R87167 : Reach 87167 := rs (se 1 (by rfl) ⟨65375, by rfl⟩) R130751
theorem R218351 : Reach 218351 := rs (se 1 (by rfl) ⟨163763, by rfl⟩) R327527
theorem R153319 : Reach 153319 := rs (se 1 (by rfl) ⟨114989, by rfl⟩) R229979
theorem R153535 : Reach 153535 := rs (se 1 (by rfl) ⟨115151, by rfl⟩) R230303
theorem R88155 : Reach 88155 := rs (se 1 (by rfl) ⟨66116, by rfl⟩) R132233
theorem R88223 : Reach 88223 := rs (se 1 (by rfl) ⟨66167, by rfl⟩) R132335
theorem R613277 : Reach 613277 := rs (se 3 (by rfl) ⟨114989, by rfl⟩) R229979
theorem R89023 : Reach 89023 := rs (se 1 (by rfl) ⟨66767, by rfl⟩) R133535
theorem R89343 : Reach 89343 := rs (se 1 (by rfl) ⟨67007, by rfl⟩) R134015
theorem R89791 : Reach 89791 := rs (se 1 (by rfl) ⟨67343, by rfl⟩) R134687
theorem R90523 : Reach 90523 := rs (se 1 (by rfl) ⟨67892, by rfl⟩) R135785
theorem R484649 : Reach 484649 := rs (se 2 (by rfl) ⟨181743, by rfl⟩) R363487
theorem R749321 : Reach 749321 := rs (se 2 (by rfl) ⟨280995, by rfl⟩) R561991
theorem R454409 : Reach 454409 := rs (se 2 (by rfl) ⟨170403, by rfl⟩) R340807
theorem R356447 : Reach 356447 := rs (se 1 (by rfl) ⟨267335, by rfl⟩) R534671
theorem R5206463 : Reach 5206463 := rs (se 1 (by rfl) ⟨3904847, by rfl⟩) R7809695
theorem R2913083 : Reach 2913083 := rs (se 1 (by rfl) ⟨2184812, by rfl⟩) R4369625
theorem R2029495 : Reach 2029495 := rs (se 1 (by rfl) ⟨1522121, by rfl⟩) R3044243
theorem R882857 : Reach 882857 := rs (se 2 (by rfl) ⟨331071, by rfl⟩) R662143
theorem R1014767 : Reach 1014767 := rs (se 1 (by rfl) ⟨761075, by rfl⟩) R1522151
theorem R196649 : Reach 196649 := rs (se 2 (by rfl) ⟨73743, by rfl⟩) R147487
theorem R950525 : Reach 950525 := rs (se 3 (by rfl) ⟨178223, by rfl⟩) R356447
theorem R198611 : Reach 198611 := rs (se 1 (by rfl) ⟨148958, by rfl⟩) R297917
theorem R3278951 : Reach 3278951 := rs (se 1 (by rfl) ⟨2459213, by rfl⟩) R4918427
theorem R134351 : Reach 134351 := rs (se 1 (by rfl) ⟨100763, by rfl⟩) R201527
theorem R135305 : Reach 135305 := rs (se 2 (by rfl) ⟨50739, by rfl⟩) R101479
theorem R135647 : Reach 135647 := rs (se 1 (by rfl) ⟨101735, by rfl⟩) R203471
theorem R204425 : Reach 204425 := rs (se 2 (by rfl) ⟨76659, by rfl⟩) R153319
theorem R499547 : Reach 499547 := rs (se 1 (by rfl) ⟨374660, by rfl⟩) R749321
theorem R302939 : Reach 302939 := rs (se 1 (by rfl) ⟨227204, by rfl⟩) R454409
theorem R204713 : Reach 204713 := rs (se 2 (by rfl) ⟨76767, by rfl⟩) R153535
theorem R1942055 : Reach 1942055 := rs (se 1 (by rfl) ⟨1456541, by rfl⟩) R2913083
theorem R1714601 : Reach 1714601 := rs (se 2 (by rfl) ⟨642975, by rfl⟩) R1285951
theorem R1125211 : Reach 1125211 := rs (se 1 (by rfl) ⟨843908, by rfl⟩) R1687817
theorem R2831071 : Reach 2831071 := rs (se 1 (by rfl) ⟨2123303, by rfl⟩) R4246607
theorem R145567 : Reach 145567 := rs (se 1 (by rfl) ⟨109175, by rfl⟩) R218351
theorem R408851 : Reach 408851 := rs (se 1 (by rfl) ⟨306638, by rfl⟩) R613277
theorem R181225 : Reach 181225 := rs (se 2 (by rfl) ⟨67959, by rfl⟩) R135919
theorem R640313 : Reach 640313 := rs (se 2 (by rfl) ⟨240117, by rfl⟩) R480235
theorem R2705993 : Reach 2705993 := rs (se 2 (by rfl) ⟨1014747, by rfl⟩) R2029495
theorem R676511 : Reach 676511 := rs (se 1 (by rfl) ⟨507383, by rfl⟩) R1014767
theorem R448091 : Reach 448091 := rs (se 1 (by rfl) ⟨336068, by rfl⟩) R672137
theorem R187049 : Reach 187049 := rs (se 2 (by rfl) ⟨70143, by rfl⟩) R140287
theorem R385391 : Reach 385391 := rs (se 1 (by rfl) ⟨289043, by rfl⟩) R578087
theorem R90527 : Reach 90527 := rs (se 1 (by rfl) ⟨67895, by rfl⟩) R135791
theorem R2354285 : Reach 2354285 := rs (se 3 (by rfl) ⟨441428, by rfl⟩) R882857
theorem R323099 : Reach 323099 := rs (se 1 (by rfl) ⟨242324, by rfl⟩) R484649
theorem R3470975 : Reach 3470975 := rs (se 1 (by rfl) ⟨2603231, by rfl⟩) R5206463
theorem R227711 : Reach 227711 := rs (se 1 (by rfl) ⟨170783, by rfl⟩) R341567
theorem R131099 : Reach 131099 := rs (se 1 (by rfl) ⟨98324, by rfl⟩) R196649
theorem R426875 : Reach 426875 := rs (se 1 (by rfl) ⟨320156, by rfl⟩) R640313
theorem R132407 : Reach 132407 := rs (se 1 (by rfl) ⟨99305, by rfl⟩) R198611
theorem R1803995 : Reach 1803995 := rs (se 1 (by rfl) ⟨1352996, by rfl⟩) R2705993
theorem R298727 : Reach 298727 := rs (se 1 (by rfl) ⟨224045, by rfl⟩) R448091
theorem R136283 : Reach 136283 := rs (se 1 (by rfl) ⟨102212, by rfl⟩) R204425
theorem R333031 : Reach 333031 := rs (se 1 (by rfl) ⟨249773, by rfl⟩) R499547
theorem R201959 : Reach 201959 := rs (se 1 (by rfl) ⟨151469, by rfl⟩) R302939
theorem R136475 : Reach 136475 := rs (se 1 (by rfl) ⟨102356, by rfl⟩) R204713
theorem R3774761 : Reach 3774761 := rs (se 2 (by rfl) ⟨1415535, by rfl⟩) R2831071
theorem R498797 : Reach 498797 := rs (se 3 (by rfl) ⟨93524, by rfl⟩) R187049
theorem R272567 : Reach 272567 := rs (se 1 (by rfl) ⟨204425, by rfl⟩) R408851
theorem R633683 : Reach 633683 := rs (se 1 (by rfl) ⟨475262, by rfl⟩) R950525
theorem R241633 : Reach 241633 := rs (se 2 (by rfl) ⟨90612, by rfl⟩) R181225
theorem R1294703 : Reach 1294703 := rs (se 1 (by rfl) ⟨971027, by rfl⟩) R1942055
theorem R215399 : Reach 215399 := rs (se 1 (by rfl) ⟨161549, by rfl⟩) R323099
theorem R6278093 : Reach 6278093 := rs (se 3 (by rfl) ⟨1177142, by rfl⟩) R2354285
theorem R2313983 : Reach 2313983 := rs (se 1 (by rfl) ⟨1735487, by rfl⟩) R3470975
theorem R151807 : Reach 151807 := rs (se 1 (by rfl) ⟨113855, by rfl⟩) R227711
theorem R2185967 : Reach 2185967 := rs (se 1 (by rfl) ⟨1639475, by rfl⟩) R3278951
theorem R89567 : Reach 89567 := rs (se 1 (by rfl) ⟨67175, by rfl⟩) R134351
theorem R90203 : Reach 90203 := rs (se 1 (by rfl) ⟨67652, by rfl⟩) R135305
theorem R90431 : Reach 90431 := rs (se 1 (by rfl) ⟨67823, by rfl⟩) R135647
theorem R451007 : Reach 451007 := rs (se 1 (by rfl) ⟨338255, by rfl⟩) R676511
theorem R1500281 : Reach 1500281 := rs (se 2 (by rfl) ⟨562605, by rfl⟩) R1125211
theorem R256927 : Reach 256927 := rs (se 1 (by rfl) ⟨192695, by rfl⟩) R385391
theorem R1143067 : Reach 1143067 := rs (se 1 (by rfl) ⟨857300, by rfl⟩) R1714601
theorem R194089 : Reach 194089 := rs (se 2 (by rfl) ⟨72783, by rfl⟩) R145567
theorem R199151 : Reach 199151 := rs (se 1 (by rfl) ⟨149363, by rfl⟩) R298727
theorem R1542655 : Reach 1542655 := rs (se 1 (by rfl) ⟨1156991, by rfl⟩) R2313983
theorem R134639 : Reach 134639 := rs (se 1 (by rfl) ⟨100979, by rfl⟩) R201959
theorem R332531 : Reach 332531 := rs (se 1 (by rfl) ⟨249398, by rfl⟩) R498797
theorem R300671 : Reach 300671 := rs (se 1 (by rfl) ⟨225503, by rfl⟩) R451007
theorem R202409 : Reach 202409 := rs (se 2 (by rfl) ⟨75903, by rfl⟩) R151807
theorem R863135 : Reach 863135 := rs (se 1 (by rfl) ⟨647351, by rfl⟩) R1294703
theorem R342569 : Reach 342569 := rs (se 2 (by rfl) ⟨128463, by rfl⟩) R256927
theorem R1524089 : Reach 1524089 := rs (se 2 (by rfl) ⟨571533, by rfl⟩) R1143067
theorem R1000187 : Reach 1000187 := rs (se 1 (by rfl) ⟨750140, by rfl⟩) R1500281
theorem R574397 : Reach 574397 := rs (se 3 (by rfl) ⟨107699, by rfl⟩) R215399
theorem R181711 : Reach 181711 := rs (se 1 (by rfl) ⟨136283, by rfl⟩) R272567
theorem R444041 : Reach 444041 := rs (se 2 (by rfl) ⟨166515, by rfl⟩) R333031
theorem R1689821 : Reach 1689821 := rs (se 3 (by rfl) ⟨316841, by rfl⟩) R633683
theorem R87399 : Reach 87399 := rs (se 1 (by rfl) ⟨65549, by rfl⟩) R131099
theorem R88271 : Reach 88271 := rs (se 1 (by rfl) ⟨66203, by rfl⟩) R132407
theorem R1202663 : Reach 1202663 := rs (se 1 (by rfl) ⟨901997, by rfl⟩) R1803995
theorem R4185395 : Reach 4185395 := rs (se 1 (by rfl) ⟨3139046, by rfl⟩) R6278093
theorem R1138333 : Reach 1138333 := rs (se 3 (by rfl) ⟨213437, by rfl⟩) R426875
theorem R90855 : Reach 90855 := rs (se 1 (by rfl) ⟨68141, by rfl⟩) R136283
theorem R90983 : Reach 90983 := rs (se 1 (by rfl) ⟨68237, by rfl⟩) R136475
theorem R2516507 : Reach 2516507 := rs (se 1 (by rfl) ⟨1887380, by rfl⟩) R3774761
theorem R322177 : Reach 322177 := rs (se 2 (by rfl) ⟨120816, by rfl⟩) R241633
theorem R5829245 : Reach 5829245 := rs (se 3 (by rfl) ⟨1092983, by rfl⟩) R2185967
theorem R258785 : Reach 258785 := rs (se 2 (by rfl) ⟨97044, by rfl⟩) R194089
theorem R1016059 : Reach 1016059 := rs (se 1 (by rfl) ⟨762044, by rfl⟩) R1524089
theorem R296027 : Reach 296027 := rs (se 1 (by rfl) ⟨222020, by rfl⟩) R444041
theorem R132767 : Reach 132767 := rs (se 1 (by rfl) ⟨99575, by rfl⟩) R199151
theorem R8227493 : Reach 8227493 := rs (se 4 (by rfl) ⟨771327, by rfl⟩) R1542655
theorem R429569 : Reach 429569 := rs (se 2 (by rfl) ⟨161088, by rfl⟩) R322177
theorem R200447 : Reach 200447 := rs (se 1 (by rfl) ⟨150335, by rfl⟩) R300671
theorem R134939 : Reach 134939 := rs (se 1 (by rfl) ⟨101204, by rfl⟩) R202409
theorem R2790263 : Reach 2790263 := rs (se 1 (by rfl) ⟨2092697, by rfl⟩) R4185395
theorem R1677671 : Reach 1677671 := rs (se 1 (by rfl) ⟨1258253, by rfl⟩) R2516507
theorem R172523 : Reach 172523 := rs (se 1 (by rfl) ⟨129392, by rfl⟩) R258785
theorem R1517777 : Reach 1517777 := rs (se 2 (by rfl) ⟨569166, by rfl⟩) R1138333
theorem R666791 : Reach 666791 := rs (se 1 (by rfl) ⟨500093, by rfl⟩) R1000187
theorem R1126547 : Reach 1126547 := rs (se 1 (by rfl) ⟨844910, by rfl⟩) R1689821
theorem R242281 : Reach 242281 := rs (se 2 (by rfl) ⟨90855, by rfl⟩) R181711
theorem R801775 : Reach 801775 := rs (se 1 (by rfl) ⟨601331, by rfl⟩) R1202663
theorem R575423 : Reach 575423 := rs (se 1 (by rfl) ⟨431567, by rfl⟩) R863135
theorem R3886163 : Reach 3886163 := rs (se 1 (by rfl) ⟨2914622, by rfl⟩) R5829245
theorem R382931 : Reach 382931 := rs (se 1 (by rfl) ⟨287198, by rfl⟩) R574397
theorem R89759 : Reach 89759 := rs (se 1 (by rfl) ⟨67319, by rfl⟩) R134639
theorem R221687 : Reach 221687 := rs (se 1 (by rfl) ⟨166265, by rfl⟩) R332531
theorem R228379 : Reach 228379 := rs (se 1 (by rfl) ⟨171284, by rfl⟩) R342569
theorem R197351 : Reach 197351 := rs (se 1 (by rfl) ⟨148013, by rfl⟩) R296027
theorem R2590775 : Reach 2590775 := rs (se 1 (by rfl) ⟨1943081, by rfl⟩) R3886163
theorem R133631 : Reach 133631 := rs (se 1 (by rfl) ⟨100223, by rfl⟩) R200447
theorem R1118447 : Reach 1118447 := rs (se 1 (by rfl) ⟨838835, by rfl⟩) R1677671
theorem R304505 : Reach 304505 := rs (se 2 (by rfl) ⟨114189, by rfl⟩) R228379
theorem R1354745 : Reach 1354745 := rs (se 2 (by rfl) ⟨508029, by rfl⟩) R1016059
theorem R5484995 : Reach 5484995 := rs (se 1 (by rfl) ⟨4113746, by rfl⟩) R8227493
theorem R115015 : Reach 115015 := rs (se 1 (by rfl) ⟨86261, by rfl⟩) R172523
theorem R147791 : Reach 147791 := rs (se 1 (by rfl) ⟨110843, by rfl⟩) R221687
theorem R444527 : Reach 444527 := rs (se 1 (by rfl) ⟨333395, by rfl⟩) R666791
theorem R1069033 : Reach 1069033 := rs (se 2 (by rfl) ⟨400887, by rfl⟩) R801775
theorem R88511 : Reach 88511 := rs (se 1 (by rfl) ⟨66383, by rfl⟩) R132767
theorem R383615 : Reach 383615 := rs (se 1 (by rfl) ⟨287711, by rfl⟩) R575423
theorem R286379 : Reach 286379 := rs (se 1 (by rfl) ⟨214784, by rfl⟩) R429569
theorem R89959 : Reach 89959 := rs (se 1 (by rfl) ⟨67469, by rfl⟩) R134939
theorem R1860175 : Reach 1860175 := rs (se 1 (by rfl) ⟨1395131, by rfl⟩) R2790263
theorem R255287 : Reach 255287 := rs (se 1 (by rfl) ⟨191465, by rfl⟩) R382931
theorem R323041 : Reach 323041 := rs (se 2 (by rfl) ⟨121140, by rfl⟩) R242281
theorem R1011851 : Reach 1011851 := rs (se 1 (by rfl) ⟨758888, by rfl⟩) R1517777
theorem R751031 : Reach 751031 := rs (se 1 (by rfl) ⟨563273, by rfl⟩) R1126547
theorem R98527 : Reach 98527 := rs (se 1 (by rfl) ⟨73895, by rfl⟩) R147791
theorem R131567 : Reach 131567 := rs (se 1 (by rfl) ⟨98675, by rfl⟩) R197351
theorem R296351 : Reach 296351 := rs (se 1 (by rfl) ⟨222263, by rfl⟩) R444527
theorem R430721 : Reach 430721 := rs (se 2 (by rfl) ⟨161520, by rfl⟩) R323041
theorem R170191 : Reach 170191 := rs (se 1 (by rfl) ⟨127643, by rfl⟩) R255287
theorem R203003 : Reach 203003 := rs (se 1 (by rfl) ⟨152252, by rfl⟩) R304505
theorem R500687 : Reach 500687 := rs (se 1 (by rfl) ⟨375515, by rfl⟩) R751031
theorem R1425377 : Reach 1425377 := rs (se 2 (by rfl) ⟨534516, by rfl⟩) R1069033
theorem R903163 : Reach 903163 := rs (se 1 (by rfl) ⟨677372, by rfl⟩) R1354745
theorem R674567 : Reach 674567 := rs (se 1 (by rfl) ⟨505925, by rfl⟩) R1011851
theorem R3656663 : Reach 3656663 := rs (se 1 (by rfl) ⟨2742497, by rfl⟩) R5484995
theorem R153353 : Reach 153353 := rs (se 2 (by rfl) ⟨57507, by rfl⟩) R115015
theorem R2480233 : Reach 2480233 := rs (se 2 (by rfl) ⟨930087, by rfl⟩) R1860175
theorem R1727183 : Reach 1727183 := rs (se 1 (by rfl) ⟨1295387, by rfl⟩) R2590775
theorem R89087 : Reach 89087 := rs (se 1 (by rfl) ⟨66815, by rfl⟩) R133631
theorem R745631 : Reach 745631 := rs (se 1 (by rfl) ⟨559223, by rfl⟩) R1118447
theorem R255743 : Reach 255743 := rs (se 1 (by rfl) ⟨191807, by rfl⟩) R383615
theorem R190919 : Reach 190919 := rs (se 1 (by rfl) ⟨143189, by rfl⟩) R286379
theorem R131369 : Reach 131369 := rs (se 2 (by rfl) ⟨49263, by rfl⟩) R98527
theorem R197567 : Reach 197567 := rs (se 1 (by rfl) ⟨148175, by rfl⟩) R296351
theorem R102235 : Reach 102235 := rs (se 1 (by rfl) ⟨76676, by rfl⟩) R153353
theorem R135335 : Reach 135335 := rs (se 1 (by rfl) ⟨101501, by rfl⟩) R203003
theorem R1151455 : Reach 1151455 := rs (se 1 (by rfl) ⟨863591, by rfl⟩) R1727183
theorem R497087 : Reach 497087 := rs (se 1 (by rfl) ⟨372815, by rfl⟩) R745631
theorem R333791 : Reach 333791 := rs (se 1 (by rfl) ⟨250343, by rfl⟩) R500687
theorem R170495 : Reach 170495 := rs (se 1 (by rfl) ⟨127871, by rfl⟩) R255743
theorem R2437775 : Reach 2437775 := rs (se 1 (by rfl) ⟨1828331, by rfl⟩) R3656663
theorem R87711 : Reach 87711 := rs (se 1 (by rfl) ⟨65783, by rfl⟩) R131567
theorem R449711 : Reach 449711 := rs (se 1 (by rfl) ⟨337283, by rfl⟩) R674567
theorem R1204217 : Reach 1204217 := rs (se 2 (by rfl) ⟨451581, by rfl⟩) R903163
theorem R287147 : Reach 287147 := rs (se 1 (by rfl) ⟨215360, by rfl⟩) R430721
theorem R127279 : Reach 127279 := rs (se 1 (by rfl) ⟨95459, by rfl⟩) R190919
theorem R3306977 : Reach 3306977 := rs (se 2 (by rfl) ⟨1240116, by rfl⟩) R2480233
theorem R226921 : Reach 226921 := rs (se 2 (by rfl) ⟨85095, by rfl⟩) R170191
theorem R3801005 : Reach 3801005 := rs (se 3 (by rfl) ⟨712688, by rfl⟩) R1425377
theorem R131711 : Reach 131711 := rs (se 1 (by rfl) ⟨98783, by rfl⟩) R197567
theorem R331391 : Reach 331391 := rs (se 1 (by rfl) ⟨248543, by rfl⟩) R497087
theorem R299807 : Reach 299807 := rs (se 1 (by rfl) ⟨224855, by rfl⟩) R449711
theorem R136313 : Reach 136313 := rs (se 2 (by rfl) ⟨51117, by rfl⟩) R102235
theorem R169705 : Reach 169705 := rs (se 2 (by rfl) ⟨63639, by rfl⟩) R127279
theorem R302561 : Reach 302561 := rs (se 2 (by rfl) ⟨113460, by rfl⟩) R226921
theorem R2204651 : Reach 2204651 := rs (se 1 (by rfl) ⟨1653488, by rfl⟩) R3306977
theorem R2534003 : Reach 2534003 := rs (se 1 (by rfl) ⟨1900502, by rfl⟩) R3801005
theorem R113663 : Reach 113663 := rs (se 1 (by rfl) ⟨85247, by rfl⟩) R170495
theorem R802811 : Reach 802811 := rs (se 1 (by rfl) ⟨602108, by rfl⟩) R1204217
theorem R1625183 : Reach 1625183 := rs (se 1 (by rfl) ⟨1218887, by rfl⟩) R2437775
theorem R87579 : Reach 87579 := rs (se 1 (by rfl) ⟨65684, by rfl⟩) R131369
theorem R90223 : Reach 90223 := rs (se 1 (by rfl) ⟨67667, by rfl⟩) R135335
theorem R222527 : Reach 222527 := rs (se 1 (by rfl) ⟨166895, by rfl⟩) R333791
theorem R191431 : Reach 191431 := rs (se 1 (by rfl) ⟨143573, by rfl⟩) R287147
theorem R1535273 : Reach 1535273 := rs (se 2 (by rfl) ⟨575727, by rfl⟩) R1151455
theorem R1083455 : Reach 1083455 := rs (se 1 (by rfl) ⟨812591, by rfl⟩) R1625183
theorem R199871 : Reach 199871 := rs (se 1 (by rfl) ⟨149903, by rfl⟩) R299807
theorem R201707 : Reach 201707 := rs (se 1 (by rfl) ⟨151280, by rfl⟩) R302561
theorem R1023515 : Reach 1023515 := rs (se 1 (by rfl) ⟨767636, by rfl⟩) R1535273
theorem R303101 : Reach 303101 := rs (se 3 (by rfl) ⟨56831, by rfl⟩) R113663
theorem R535207 : Reach 535207 := rs (se 1 (by rfl) ⟨401405, by rfl⟩) R802811
theorem R148351 : Reach 148351 := rs (se 1 (by rfl) ⟨111263, by rfl⟩) R222527
theorem R1689335 : Reach 1689335 := rs (se 1 (by rfl) ⟨1267001, by rfl⟩) R2534003
theorem R87807 : Reach 87807 := rs (se 1 (by rfl) ⟨65855, by rfl⟩) R131711
theorem R220927 : Reach 220927 := rs (se 1 (by rfl) ⟨165695, by rfl⟩) R331391
theorem R90875 : Reach 90875 := rs (se 1 (by rfl) ⟨68156, by rfl⟩) R136313
theorem R255241 : Reach 255241 := rs (se 2 (by rfl) ⟨95715, by rfl⟩) R191431
theorem R1469767 : Reach 1469767 := rs (se 1 (by rfl) ⟨1102325, by rfl⟩) R2204651
theorem R226273 : Reach 226273 := rs (se 2 (by rfl) ⟨84852, by rfl⟩) R169705
theorem R197801 : Reach 197801 := rs (se 2 (by rfl) ⟨74175, by rfl⟩) R148351
theorem R722303 : Reach 722303 := rs (se 1 (by rfl) ⟨541727, by rfl⟩) R1083455
theorem R133247 : Reach 133247 := rs (se 1 (by rfl) ⟨99935, by rfl⟩) R199871
theorem R134471 : Reach 134471 := rs (se 1 (by rfl) ⟨100853, by rfl⟩) R201707
theorem R202067 : Reach 202067 := rs (se 1 (by rfl) ⟨151550, by rfl⟩) R303101
theorem R301697 : Reach 301697 := rs (se 2 (by rfl) ⟨113136, by rfl⟩) R226273
theorem R1126223 : Reach 1126223 := rs (se 1 (by rfl) ⟨844667, by rfl⟩) R1689335
theorem R340321 : Reach 340321 := rs (se 2 (by rfl) ⟨127620, by rfl⟩) R255241
theorem R713609 : Reach 713609 := rs (se 2 (by rfl) ⟨267603, by rfl⟩) R535207
theorem R1959689 : Reach 1959689 := rs (se 2 (by rfl) ⟨734883, by rfl⟩) R1469767
theorem R682343 : Reach 682343 := rs (se 1 (by rfl) ⟨511757, by rfl⟩) R1023515
theorem R294569 : Reach 294569 := rs (se 2 (by rfl) ⟨110463, by rfl⟩) R220927
theorem R131867 : Reach 131867 := rs (se 1 (by rfl) ⟨98900, by rfl⟩) R197801
theorem R134711 : Reach 134711 := rs (se 1 (by rfl) ⟨101033, by rfl⟩) R202067
theorem R201131 : Reach 201131 := rs (se 1 (by rfl) ⟨150848, by rfl⟩) R301697
theorem R475739 : Reach 475739 := rs (se 1 (by rfl) ⟨356804, by rfl⟩) R713609
theorem R481535 : Reach 481535 := rs (se 1 (by rfl) ⟨361151, by rfl⟩) R722303
theorem R88831 : Reach 88831 := rs (se 1 (by rfl) ⟨66623, by rfl⟩) R133247
theorem R89647 : Reach 89647 := rs (se 1 (by rfl) ⟨67235, by rfl⟩) R134471
theorem R453761 : Reach 453761 := rs (se 2 (by rfl) ⟨170160, by rfl⟩) R340321
theorem R1306459 : Reach 1306459 := rs (se 1 (by rfl) ⟨979844, by rfl⟩) R1959689
theorem R454895 : Reach 454895 := rs (se 1 (by rfl) ⟨341171, by rfl⟩) R682343
theorem R750815 : Reach 750815 := rs (se 1 (by rfl) ⟨563111, by rfl⟩) R1126223
theorem R196379 : Reach 196379 := rs (se 1 (by rfl) ⟨147284, by rfl⟩) R294569
theorem R134087 : Reach 134087 := rs (se 1 (by rfl) ⟨100565, by rfl⟩) R201131
theorem R1741945 : Reach 1741945 := rs (se 2 (by rfl) ⟨653229, by rfl⟩) R1306459
theorem R302507 : Reach 302507 := rs (se 1 (by rfl) ⟨226880, by rfl⟩) R453761
theorem R303263 : Reach 303263 := rs (se 1 (by rfl) ⟨227447, by rfl⟩) R454895
theorem R500543 : Reach 500543 := rs (se 1 (by rfl) ⟨375407, by rfl⟩) R750815
theorem R317159 : Reach 317159 := rs (se 1 (by rfl) ⟨237869, by rfl⟩) R475739
theorem R87911 : Reach 87911 := rs (se 1 (by rfl) ⟨65933, by rfl⟩) R131867
theorem R89807 : Reach 89807 := rs (se 1 (by rfl) ⟨67355, by rfl⟩) R134711
theorem R321023 : Reach 321023 := rs (se 1 (by rfl) ⟨240767, by rfl⟩) R481535
theorem R130919 : Reach 130919 := rs (se 1 (by rfl) ⟨98189, by rfl⟩) R196379
theorem R201671 : Reach 201671 := rs (se 1 (by rfl) ⟨151253, by rfl⟩) R302507
theorem R202175 : Reach 202175 := rs (se 1 (by rfl) ⟨151631, by rfl⟩) R303263
theorem R333695 : Reach 333695 := rs (se 1 (by rfl) ⟨250271, by rfl⟩) R500543
theorem R211439 : Reach 211439 := rs (se 1 (by rfl) ⟨158579, by rfl⟩) R317159
theorem R214015 : Reach 214015 := rs (se 1 (by rfl) ⟨160511, by rfl⟩) R321023
theorem R87279 : Reach 87279 := rs (se 1 (by rfl) ⟨65459, by rfl⟩) R130919
theorem R89391 : Reach 89391 := rs (se 1 (by rfl) ⟨67043, by rfl⟩) R134087
theorem R2322593 : Reach 2322593 := rs (se 2 (by rfl) ⟨870972, by rfl⟩) R1741945
theorem R134447 : Reach 134447 := rs (se 1 (by rfl) ⟨100835, by rfl⟩) R201671
theorem R134783 : Reach 134783 := rs (se 1 (by rfl) ⟨101087, by rfl⟩) R202175
theorem R1548395 : Reach 1548395 := rs (se 1 (by rfl) ⟨1161296, by rfl⟩) R2322593
theorem R140959 : Reach 140959 := rs (se 1 (by rfl) ⟨105719, by rfl⟩) R211439
theorem R285353 : Reach 285353 := rs (se 2 (by rfl) ⟨107007, by rfl⟩) R214015
theorem R222463 : Reach 222463 := rs (se 1 (by rfl) ⟨166847, by rfl⟩) R333695
theorem R296617 : Reach 296617 := rs (se 2 (by rfl) ⟨111231, by rfl⟩) R222463
theorem R1032263 : Reach 1032263 := rs (se 1 (by rfl) ⟨774197, by rfl⟩) R1548395
theorem R89631 : Reach 89631 := rs (se 1 (by rfl) ⟨67223, by rfl⟩) R134447
theorem R89855 : Reach 89855 := rs (se 1 (by rfl) ⟨67391, by rfl⟩) R134783
theorem R190235 : Reach 190235 := rs (se 1 (by rfl) ⟨142676, by rfl⟩) R285353
theorem R751781 : Reach 751781 := rs (se 4 (by rfl) ⟨70479, by rfl⟩) R140959
theorem R688175 : Reach 688175 := rs (se 1 (by rfl) ⟨516131, by rfl⟩) R1032263
theorem R395489 : Reach 395489 := rs (se 2 (by rfl) ⟨148308, by rfl⟩) R296617
theorem R501187 : Reach 501187 := rs (se 1 (by rfl) ⟨375890, by rfl⟩) R751781
theorem R507293 : Reach 507293 := rs (se 3 (by rfl) ⟨95117, by rfl⟩) R190235
theorem R458783 : Reach 458783 := rs (se 1 (by rfl) ⟨344087, by rfl⟩) R688175
theorem R1054637 : Reach 1054637 := rs (se 3 (by rfl) ⟨197744, by rfl⟩) R395489
theorem R338195 : Reach 338195 := rs (se 1 (by rfl) ⟨253646, by rfl⟩) R507293
theorem R668249 : Reach 668249 := rs (se 2 (by rfl) ⟨250593, by rfl⟩) R501187
theorem R305855 : Reach 305855 := rs (se 1 (by rfl) ⟨229391, by rfl⟩) R458783
theorem R703091 : Reach 703091 := rs (se 1 (by rfl) ⟨527318, by rfl⟩) R1054637
theorem R445499 : Reach 445499 := rs (se 1 (by rfl) ⟨334124, by rfl⟩) R668249
theorem R225463 : Reach 225463 := rs (se 1 (by rfl) ⟨169097, by rfl⟩) R338195
theorem R296999 : Reach 296999 := rs (se 1 (by rfl) ⟨222749, by rfl⟩) R445499
theorem R300617 : Reach 300617 := rs (se 2 (by rfl) ⟨112731, by rfl⟩) R225463
theorem R1874909 : Reach 1874909 := rs (se 3 (by rfl) ⟨351545, by rfl⟩) R703091
theorem R203903 : Reach 203903 := rs (se 1 (by rfl) ⟨152927, by rfl⟩) R305855
theorem R197999 : Reach 197999 := rs (se 1 (by rfl) ⟨148499, by rfl⟩) R296999
theorem R200411 : Reach 200411 := rs (se 1 (by rfl) ⟨150308, by rfl⟩) R300617
theorem R1249939 : Reach 1249939 := rs (se 1 (by rfl) ⟨937454, by rfl⟩) R1874909
theorem R135935 : Reach 135935 := rs (se 1 (by rfl) ⟨101951, by rfl⟩) R203903
theorem R131999 : Reach 131999 := rs (se 1 (by rfl) ⟨98999, by rfl⟩) R197999
theorem R133607 : Reach 133607 := rs (se 1 (by rfl) ⟨100205, by rfl⟩) R200411
theorem R90623 : Reach 90623 := rs (se 1 (by rfl) ⟨67967, by rfl⟩) R135935
theorem R1666585 : Reach 1666585 := rs (se 2 (by rfl) ⟨624969, by rfl⟩) R1249939
theorem R87999 : Reach 87999 := rs (se 1 (by rfl) ⟨65999, by rfl⟩) R131999
theorem R89071 : Reach 89071 := rs (se 1 (by rfl) ⟨66803, by rfl⟩) R133607
theorem R2222113 : Reach 2222113 := rs (se 2 (by rfl) ⟨833292, by rfl⟩) R1666585
theorem R2962817 : Reach 2962817 := rs (se 2 (by rfl) ⟨1111056, by rfl⟩) R2222113
theorem R1975211 : Reach 1975211 := rs (se 1 (by rfl) ⟨1481408, by rfl⟩) R2962817
theorem R1316807 : Reach 1316807 := rs (se 1 (by rfl) ⟨987605, by rfl⟩) R1975211
theorem R877871 : Reach 877871 := rs (se 1 (by rfl) ⟨658403, by rfl⟩) R1316807
theorem R585247 : Reach 585247 := rs (se 1 (by rfl) ⟨438935, by rfl⟩) R877871
theorem R780329 : Reach 780329 := rs (se 2 (by rfl) ⟨292623, by rfl⟩) R585247
theorem R520219 : Reach 520219 := rs (se 1 (by rfl) ⟨390164, by rfl⟩) R780329
theorem R693625 : Reach 693625 := rs (se 2 (by rfl) ⟨260109, by rfl⟩) R520219
theorem R924833 : Reach 924833 := rs (se 2 (by rfl) ⟨346812, by rfl⟩) R693625
theorem R616555 : Reach 616555 := rs (se 1 (by rfl) ⟨462416, by rfl⟩) R924833
theorem R822073 : Reach 822073 := rs (se 2 (by rfl) ⟨308277, by rfl⟩) R616555
theorem R1096097 : Reach 1096097 := rs (se 2 (by rfl) ⟨411036, by rfl⟩) R822073
theorem R11691701 : Reach 11691701 := rs (se 5 (by rfl) ⟨548048, by rfl⟩) R1096097
theorem R7794467 : Reach 7794467 := rs (se 1 (by rfl) ⟨5845850, by rfl⟩) R11691701
theorem R5196311 : Reach 5196311 := rs (se 1 (by rfl) ⟨3897233, by rfl⟩) R7794467
theorem R3464207 : Reach 3464207 := rs (se 1 (by rfl) ⟨2598155, by rfl⟩) R5196311
theorem R2309471 : Reach 2309471 := rs (se 1 (by rfl) ⟨1732103, by rfl⟩) R3464207
theorem R1539647 : Reach 1539647 := rs (se 1 (by rfl) ⟨1154735, by rfl⟩) R2309471
theorem R1026431 : Reach 1026431 := rs (se 1 (by rfl) ⟨769823, by rfl⟩) R1539647
theorem R684287 : Reach 684287 := rs (se 1 (by rfl) ⟨513215, by rfl⟩) R1026431
theorem R456191 : Reach 456191 := rs (se 1 (by rfl) ⟨342143, by rfl⟩) R684287
theorem R304127 : Reach 304127 := rs (se 1 (by rfl) ⟨228095, by rfl⟩) R456191
theorem R202751 : Reach 202751 := rs (se 1 (by rfl) ⟨152063, by rfl⟩) R304127
theorem R135167 : Reach 135167 := rs (se 1 (by rfl) ⟨101375, by rfl⟩) R202751
theorem R90111 : Reach 90111 := rs (se 1 (by rfl) ⟨67583, by rfl⟩) R135167

theorem C0 (j : ℕ) (h1 : 43564 ≤ j) (h2 : j ≤ 44263) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R87129
  · exact R87131
  · exact R87133
  · exact R87135
  · exact R87137
  · exact R87139
  · exact R87141
  · exact R87143
  · exact R87145
  · exact R87147
  · exact R87149
  · exact R87151
  · exact R87153
  · exact R87155
  · exact R87157
  · exact R87159
  · exact R87161
  · exact R87163
  · exact R87165
  · exact R87167
  · exact R87169
  · exact R87171
  · exact R87173
  · exact R87175
  · exact R87177
  · exact R87179
  · exact R87181
  · exact R87183
  · exact R87185
  · exact R87187
  · exact R87189
  · exact R87191
  · exact R87193
  · exact R87195
  · exact R87197
  · exact R87199
  · exact R87201
  · exact R87203
  · exact R87205
  · exact R87207
  · exact R87209
  · exact R87211
  · exact R87213
  · exact R87215
  · exact R87217
  · exact R87219
  · exact R87221
  · exact R87223
  · exact R87225
  · exact R87227
  · exact R87229
  · exact R87231
  · exact R87233
  · exact R87235
  · exact R87237
  · exact R87239
  · exact R87241
  · exact R87243
  · exact R87245
  · exact R87247
  · exact R87249
  · exact R87251
  · exact R87253
  · exact R87255
  · exact R87257
  · exact R87259
  · exact R87261
  · exact R87263
  · exact R87265
  · exact R87267
  · exact R87269
  · exact R87271
  · exact R87273
  · exact R87275
  · exact R87277
  · exact R87279
  · exact R87281
  · exact R87283
  · exact R87285
  · exact R87287
  · exact R87289
  · exact R87291
  · exact R87293
  · exact R87295
  · exact R87297
  · exact R87299
  · exact R87301
  · exact R87303
  · exact R87305
  · exact R87307
  · exact R87309
  · exact R87311
  · exact R87313
  · exact R87315
  · exact R87317
  · exact R87319
  · exact R87321
  · exact R87323
  · exact R87325
  · exact R87327
  · exact R87329
  · exact R87331
  · exact R87333
  · exact R87335
  · exact R87337
  · exact R87339
  · exact R87341
  · exact R87343
  · exact R87345
  · exact R87347
  · exact R87349
  · exact R87351
  · exact R87353
  · exact R87355
  · exact R87357
  · exact R87359
  · exact R87361
  · exact R87363
  · exact R87365
  · exact R87367
  · exact R87369
  · exact R87371
  · exact R87373
  · exact R87375
  · exact R87377
  · exact R87379
  · exact R87381
  · exact R87383
  · exact R87385
  · exact R87387
  · exact R87389
  · exact R87391
  · exact R87393
  · exact R87395
  · exact R87397
  · exact R87399
  · exact R87401
  · exact R87403
  · exact R87405
  · exact R87407
  · exact R87409
  · exact R87411
  · exact R87413
  · exact R87415
  · exact R87417
  · exact R87419
  · exact R87421
  · exact R87423
  · exact R87425
  · exact R87427
  · exact R87429
  · exact R87431
  · exact R87433
  · exact R87435
  · exact R87437
  · exact R87439
  · exact R87441
  · exact R87443
  · exact R87445
  · exact R87447
  · exact R87449
  · exact R87451
  · exact R87453
  · exact R87455
  · exact R87457
  · exact R87459
  · exact R87461
  · exact R87463
  · exact R87465
  · exact R87467
  · exact R87469
  · exact R87471
  · exact R87473
  · exact R87475
  · exact R87477
  · exact R87479
  · exact R87481
  · exact R87483
  · exact R87485
  · exact R87487
  · exact R87489
  · exact R87491
  · exact R87493
  · exact R87495
  · exact R87497
  · exact R87499
  · exact R87501
  · exact R87503
  · exact R87505
  · exact R87507
  · exact R87509
  · exact R87511
  · exact R87513
  · exact R87515
  · exact R87517
  · exact R87519
  · exact R87521
  · exact R87523
  · exact R87525
  · exact R87527
  · exact R87529
  · exact R87531
  · exact R87533
  · exact R87535
  · exact R87537
  · exact R87539
  · exact R87541
  · exact R87543
  · exact R87545
  · exact R87547
  · exact R87549
  · exact R87551
  · exact R87553
  · exact R87555
  · exact R87557
  · exact R87559
  · exact R87561
  · exact R87563
  · exact R87565
  · exact R87567
  · exact R87569
  · exact R87571
  · exact R87573
  · exact R87575
  · exact R87577
  · exact R87579
  · exact R87581
  · exact R87583
  · exact R87585
  · exact R87587
  · exact R87589
  · exact R87591
  · exact R87593
  · exact R87595
  · exact R87597
  · exact R87599
  · exact R87601
  · exact R87603
  · exact R87605
  · exact R87607
  · exact R87609
  · exact R87611
  · exact R87613
  · exact R87615
  · exact R87617
  · exact R87619
  · exact R87621
  · exact R87623
  · exact R87625
  · exact R87627
  · exact R87629
  · exact R87631
  · exact R87633
  · exact R87635
  · exact R87637
  · exact R87639
  · exact R87641
  · exact R87643
  · exact R87645
  · exact R87647
  · exact R87649
  · exact R87651
  · exact R87653
  · exact R87655
  · exact R87657
  · exact R87659
  · exact R87661
  · exact R87663
  · exact R87665
  · exact R87667
  · exact R87669
  · exact R87671
  · exact R87673
  · exact R87675
  · exact R87677
  · exact R87679
  · exact R87681
  · exact R87683
  · exact R87685
  · exact R87687
  · exact R87689
  · exact R87691
  · exact R87693
  · exact R87695
  · exact R87697
  · exact R87699
  · exact R87701
  · exact R87703
  · exact R87705
  · exact R87707
  · exact R87709
  · exact R87711
  · exact R87713
  · exact R87715
  · exact R87717
  · exact R87719
  · exact R87721
  · exact R87723
  · exact R87725
  · exact R87727
  · exact R87729
  · exact R87731
  · exact R87733
  · exact R87735
  · exact R87737
  · exact R87739
  · exact R87741
  · exact R87743
  · exact R87745
  · exact R87747
  · exact R87749
  · exact R87751
  · exact R87753
  · exact R87755
  · exact R87757
  · exact R87759
  · exact R87761
  · exact R87763
  · exact R87765
  · exact R87767
  · exact R87769
  · exact R87771
  · exact R87773
  · exact R87775
  · exact R87777
  · exact R87779
  · exact R87781
  · exact R87783
  · exact R87785
  · exact R87787
  · exact R87789
  · exact R87791
  · exact R87793
  · exact R87795
  · exact R87797
  · exact R87799
  · exact R87801
  · exact R87803
  · exact R87805
  · exact R87807
  · exact R87809
  · exact R87811
  · exact R87813
  · exact R87815
  · exact R87817
  · exact R87819
  · exact R87821
  · exact R87823
  · exact R87825
  · exact R87827
  · exact R87829
  · exact R87831
  · exact R87833
  · exact R87835
  · exact R87837
  · exact R87839
  · exact R87841
  · exact R87843
  · exact R87845
  · exact R87847
  · exact R87849
  · exact R87851
  · exact R87853
  · exact R87855
  · exact R87857
  · exact R87859
  · exact R87861
  · exact R87863
  · exact R87865
  · exact R87867
  · exact R87869
  · exact R87871
  · exact R87873
  · exact R87875
  · exact R87877
  · exact R87879
  · exact R87881
  · exact R87883
  · exact R87885
  · exact R87887
  · exact R87889
  · exact R87891
  · exact R87893
  · exact R87895
  · exact R87897
  · exact R87899
  · exact R87901
  · exact R87903
  · exact R87905
  · exact R87907
  · exact R87909
  · exact R87911
  · exact R87913
  · exact R87915
  · exact R87917
  · exact R87919
  · exact R87921
  · exact R87923
  · exact R87925
  · exact R87927
  · exact R87929
  · exact R87931
  · exact R87933
  · exact R87935
  · exact R87937
  · exact R87939
  · exact R87941
  · exact R87943
  · exact R87945
  · exact R87947
  · exact R87949
  · exact R87951
  · exact R87953
  · exact R87955
  · exact R87957
  · exact R87959
  · exact R87961
  · exact R87963
  · exact R87965
  · exact R87967
  · exact R87969
  · exact R87971
  · exact R87973
  · exact R87975
  · exact R87977
  · exact R87979
  · exact R87981
  · exact R87983
  · exact R87985
  · exact R87987
  · exact R87989
  · exact R87991
  · exact R87993
  · exact R87995
  · exact R87997
  · exact R87999
  · exact R88001
  · exact R88003
  · exact R88005
  · exact R88007
  · exact R88009
  · exact R88011
  · exact R88013
  · exact R88015
  · exact R88017
  · exact R88019
  · exact R88021
  · exact R88023
  · exact R88025
  · exact R88027
  · exact R88029
  · exact R88031
  · exact R88033
  · exact R88035
  · exact R88037
  · exact R88039
  · exact R88041
  · exact R88043
  · exact R88045
  · exact R88047
  · exact R88049
  · exact R88051
  · exact R88053
  · exact R88055
  · exact R88057
  · exact R88059
  · exact R88061
  · exact R88063
  · exact R88065
  · exact R88067
  · exact R88069
  · exact R88071
  · exact R88073
  · exact R88075
  · exact R88077
  · exact R88079
  · exact R88081
  · exact R88083
  · exact R88085
  · exact R88087
  · exact R88089
  · exact R88091
  · exact R88093
  · exact R88095
  · exact R88097
  · exact R88099
  · exact R88101
  · exact R88103
  · exact R88105
  · exact R88107
  · exact R88109
  · exact R88111
  · exact R88113
  · exact R88115
  · exact R88117
  · exact R88119
  · exact R88121
  · exact R88123
  · exact R88125
  · exact R88127
  · exact R88129
  · exact R88131
  · exact R88133
  · exact R88135
  · exact R88137
  · exact R88139
  · exact R88141
  · exact R88143
  · exact R88145
  · exact R88147
  · exact R88149
  · exact R88151
  · exact R88153
  · exact R88155
  · exact R88157
  · exact R88159
  · exact R88161
  · exact R88163
  · exact R88165
  · exact R88167
  · exact R88169
  · exact R88171
  · exact R88173
  · exact R88175
  · exact R88177
  · exact R88179
  · exact R88181
  · exact R88183
  · exact R88185
  · exact R88187
  · exact R88189
  · exact R88191
  · exact R88193
  · exact R88195
  · exact R88197
  · exact R88199
  · exact R88201
  · exact R88203
  · exact R88205
  · exact R88207
  · exact R88209
  · exact R88211
  · exact R88213
  · exact R88215
  · exact R88217
  · exact R88219
  · exact R88221
  · exact R88223
  · exact R88225
  · exact R88227
  · exact R88229
  · exact R88231
  · exact R88233
  · exact R88235
  · exact R88237
  · exact R88239
  · exact R88241
  · exact R88243
  · exact R88245
  · exact R88247
  · exact R88249
  · exact R88251
  · exact R88253
  · exact R88255
  · exact R88257
  · exact R88259
  · exact R88261
  · exact R88263
  · exact R88265
  · exact R88267
  · exact R88269
  · exact R88271
  · exact R88273
  · exact R88275
  · exact R88277
  · exact R88279
  · exact R88281
  · exact R88283
  · exact R88285
  · exact R88287
  · exact R88289
  · exact R88291
  · exact R88293
  · exact R88295
  · exact R88297
  · exact R88299
  · exact R88301
  · exact R88303
  · exact R88305
  · exact R88307
  · exact R88309
  · exact R88311
  · exact R88313
  · exact R88315
  · exact R88317
  · exact R88319
  · exact R88321
  · exact R88323
  · exact R88325
  · exact R88327
  · exact R88329
  · exact R88331
  · exact R88333
  · exact R88335
  · exact R88337
  · exact R88339
  · exact R88341
  · exact R88343
  · exact R88345
  · exact R88347
  · exact R88349
  · exact R88351
  · exact R88353
  · exact R88355
  · exact R88357
  · exact R88359
  · exact R88361
  · exact R88363
  · exact R88365
  · exact R88367
  · exact R88369
  · exact R88371
  · exact R88373
  · exact R88375
  · exact R88377
  · exact R88379
  · exact R88381
  · exact R88383
  · exact R88385
  · exact R88387
  · exact R88389
  · exact R88391
  · exact R88393
  · exact R88395
  · exact R88397
  · exact R88399
  · exact R88401
  · exact R88403
  · exact R88405
  · exact R88407
  · exact R88409
  · exact R88411
  · exact R88413
  · exact R88415
  · exact R88417
  · exact R88419
  · exact R88421
  · exact R88423
  · exact R88425
  · exact R88427
  · exact R88429
  · exact R88431
  · exact R88433
  · exact R88435
  · exact R88437
  · exact R88439
  · exact R88441
  · exact R88443
  · exact R88445
  · exact R88447
  · exact R88449
  · exact R88451
  · exact R88453
  · exact R88455
  · exact R88457
  · exact R88459
  · exact R88461
  · exact R88463
  · exact R88465
  · exact R88467
  · exact R88469
  · exact R88471
  · exact R88473
  · exact R88475
  · exact R88477
  · exact R88479
  · exact R88481
  · exact R88483
  · exact R88485
  · exact R88487
  · exact R88489
  · exact R88491
  · exact R88493
  · exact R88495
  · exact R88497
  · exact R88499
  · exact R88501
  · exact R88503
  · exact R88505
  · exact R88507
  · exact R88509
  · exact R88511
  · exact R88513
  · exact R88515
  · exact R88517
  · exact R88519
  · exact R88521
  · exact R88523
  · exact R88525
  · exact R88527

theorem C1 (j : ℕ) (h1 : 44264 ≤ j) (h2 : j ≤ 44963) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R88529
  · exact R88531
  · exact R88533
  · exact R88535
  · exact R88537
  · exact R88539
  · exact R88541
  · exact R88543
  · exact R88545
  · exact R88547
  · exact R88549
  · exact R88551
  · exact R88553
  · exact R88555
  · exact R88557
  · exact R88559
  · exact R88561
  · exact R88563
  · exact R88565
  · exact R88567
  · exact R88569
  · exact R88571
  · exact R88573
  · exact R88575
  · exact R88577
  · exact R88579
  · exact R88581
  · exact R88583
  · exact R88585
  · exact R88587
  · exact R88589
  · exact R88591
  · exact R88593
  · exact R88595
  · exact R88597
  · exact R88599
  · exact R88601
  · exact R88603
  · exact R88605
  · exact R88607
  · exact R88609
  · exact R88611
  · exact R88613
  · exact R88615
  · exact R88617
  · exact R88619
  · exact R88621
  · exact R88623
  · exact R88625
  · exact R88627
  · exact R88629
  · exact R88631
  · exact R88633
  · exact R88635
  · exact R88637
  · exact R88639
  · exact R88641
  · exact R88643
  · exact R88645
  · exact R88647
  · exact R88649
  · exact R88651
  · exact R88653
  · exact R88655
  · exact R88657
  · exact R88659
  · exact R88661
  · exact R88663
  · exact R88665
  · exact R88667
  · exact R88669
  · exact R88671
  · exact R88673
  · exact R88675
  · exact R88677
  · exact R88679
  · exact R88681
  · exact R88683
  · exact R88685
  · exact R88687
  · exact R88689
  · exact R88691
  · exact R88693
  · exact R88695
  · exact R88697
  · exact R88699
  · exact R88701
  · exact R88703
  · exact R88705
  · exact R88707
  · exact R88709
  · exact R88711
  · exact R88713
  · exact R88715
  · exact R88717
  · exact R88719
  · exact R88721
  · exact R88723
  · exact R88725
  · exact R88727
  · exact R88729
  · exact R88731
  · exact R88733
  · exact R88735
  · exact R88737
  · exact R88739
  · exact R88741
  · exact R88743
  · exact R88745
  · exact R88747
  · exact R88749
  · exact R88751
  · exact R88753
  · exact R88755
  · exact R88757
  · exact R88759
  · exact R88761
  · exact R88763
  · exact R88765
  · exact R88767
  · exact R88769
  · exact R88771
  · exact R88773
  · exact R88775
  · exact R88777
  · exact R88779
  · exact R88781
  · exact R88783
  · exact R88785
  · exact R88787
  · exact R88789
  · exact R88791
  · exact R88793
  · exact R88795
  · exact R88797
  · exact R88799
  · exact R88801
  · exact R88803
  · exact R88805
  · exact R88807
  · exact R88809
  · exact R88811
  · exact R88813
  · exact R88815
  · exact R88817
  · exact R88819
  · exact R88821
  · exact R88823
  · exact R88825
  · exact R88827
  · exact R88829
  · exact R88831
  · exact R88833
  · exact R88835
  · exact R88837
  · exact R88839
  · exact R88841
  · exact R88843
  · exact R88845
  · exact R88847
  · exact R88849
  · exact R88851
  · exact R88853
  · exact R88855
  · exact R88857
  · exact R88859
  · exact R88861
  · exact R88863
  · exact R88865
  · exact R88867
  · exact R88869
  · exact R88871
  · exact R88873
  · exact R88875
  · exact R88877
  · exact R88879
  · exact R88881
  · exact R88883
  · exact R88885
  · exact R88887
  · exact R88889
  · exact R88891
  · exact R88893
  · exact R88895
  · exact R88897
  · exact R88899
  · exact R88901
  · exact R88903
  · exact R88905
  · exact R88907
  · exact R88909
  · exact R88911
  · exact R88913
  · exact R88915
  · exact R88917
  · exact R88919
  · exact R88921
  · exact R88923
  · exact R88925
  · exact R88927
  · exact R88929
  · exact R88931
  · exact R88933
  · exact R88935
  · exact R88937
  · exact R88939
  · exact R88941
  · exact R88943
  · exact R88945
  · exact R88947
  · exact R88949
  · exact R88951
  · exact R88953
  · exact R88955
  · exact R88957
  · exact R88959
  · exact R88961
  · exact R88963
  · exact R88965
  · exact R88967
  · exact R88969
  · exact R88971
  · exact R88973
  · exact R88975
  · exact R88977
  · exact R88979
  · exact R88981
  · exact R88983
  · exact R88985
  · exact R88987
  · exact R88989
  · exact R88991
  · exact R88993
  · exact R88995
  · exact R88997
  · exact R88999
  · exact R89001
  · exact R89003
  · exact R89005
  · exact R89007
  · exact R89009
  · exact R89011
  · exact R89013
  · exact R89015
  · exact R89017
  · exact R89019
  · exact R89021
  · exact R89023
  · exact R89025
  · exact R89027
  · exact R89029
  · exact R89031
  · exact R89033
  · exact R89035
  · exact R89037
  · exact R89039
  · exact R89041
  · exact R89043
  · exact R89045
  · exact R89047
  · exact R89049
  · exact R89051
  · exact R89053
  · exact R89055
  · exact R89057
  · exact R89059
  · exact R89061
  · exact R89063
  · exact R89065
  · exact R89067
  · exact R89069
  · exact R89071
  · exact R89073
  · exact R89075
  · exact R89077
  · exact R89079
  · exact R89081
  · exact R89083
  · exact R89085
  · exact R89087
  · exact R89089
  · exact R89091
  · exact R89093
  · exact R89095
  · exact R89097
  · exact R89099
  · exact R89101
  · exact R89103
  · exact R89105
  · exact R89107
  · exact R89109
  · exact R89111
  · exact R89113
  · exact R89115
  · exact R89117
  · exact R89119
  · exact R89121
  · exact R89123
  · exact R89125
  · exact R89127
  · exact R89129
  · exact R89131
  · exact R89133
  · exact R89135
  · exact R89137
  · exact R89139
  · exact R89141
  · exact R89143
  · exact R89145
  · exact R89147
  · exact R89149
  · exact R89151
  · exact R89153
  · exact R89155
  · exact R89157
  · exact R89159
  · exact R89161
  · exact R89163
  · exact R89165
  · exact R89167
  · exact R89169
  · exact R89171
  · exact R89173
  · exact R89175
  · exact R89177
  · exact R89179
  · exact R89181
  · exact R89183
  · exact R89185
  · exact R89187
  · exact R89189
  · exact R89191
  · exact R89193
  · exact R89195
  · exact R89197
  · exact R89199
  · exact R89201
  · exact R89203
  · exact R89205
  · exact R89207
  · exact R89209
  · exact R89211
  · exact R89213
  · exact R89215
  · exact R89217
  · exact R89219
  · exact R89221
  · exact R89223
  · exact R89225
  · exact R89227
  · exact R89229
  · exact R89231
  · exact R89233
  · exact R89235
  · exact R89237
  · exact R89239
  · exact R89241
  · exact R89243
  · exact R89245
  · exact R89247
  · exact R89249
  · exact R89251
  · exact R89253
  · exact R89255
  · exact R89257
  · exact R89259
  · exact R89261
  · exact R89263
  · exact R89265
  · exact R89267
  · exact R89269
  · exact R89271
  · exact R89273
  · exact R89275
  · exact R89277
  · exact R89279
  · exact R89281
  · exact R89283
  · exact R89285
  · exact R89287
  · exact R89289
  · exact R89291
  · exact R89293
  · exact R89295
  · exact R89297
  · exact R89299
  · exact R89301
  · exact R89303
  · exact R89305
  · exact R89307
  · exact R89309
  · exact R89311
  · exact R89313
  · exact R89315
  · exact R89317
  · exact R89319
  · exact R89321
  · exact R89323
  · exact R89325
  · exact R89327
  · exact R89329
  · exact R89331
  · exact R89333
  · exact R89335
  · exact R89337
  · exact R89339
  · exact R89341
  · exact R89343
  · exact R89345
  · exact R89347
  · exact R89349
  · exact R89351
  · exact R89353
  · exact R89355
  · exact R89357
  · exact R89359
  · exact R89361
  · exact R89363
  · exact R89365
  · exact R89367
  · exact R89369
  · exact R89371
  · exact R89373
  · exact R89375
  · exact R89377
  · exact R89379
  · exact R89381
  · exact R89383
  · exact R89385
  · exact R89387
  · exact R89389
  · exact R89391
  · exact R89393
  · exact R89395
  · exact R89397
  · exact R89399
  · exact R89401
  · exact R89403
  · exact R89405
  · exact R89407
  · exact R89409
  · exact R89411
  · exact R89413
  · exact R89415
  · exact R89417
  · exact R89419
  · exact R89421
  · exact R89423
  · exact R89425
  · exact R89427
  · exact R89429
  · exact R89431
  · exact R89433
  · exact R89435
  · exact R89437
  · exact R89439
  · exact R89441
  · exact R89443
  · exact R89445
  · exact R89447
  · exact R89449
  · exact R89451
  · exact R89453
  · exact R89455
  · exact R89457
  · exact R89459
  · exact R89461
  · exact R89463
  · exact R89465
  · exact R89467
  · exact R89469
  · exact R89471
  · exact R89473
  · exact R89475
  · exact R89477
  · exact R89479
  · exact R89481
  · exact R89483
  · exact R89485
  · exact R89487
  · exact R89489
  · exact R89491
  · exact R89493
  · exact R89495
  · exact R89497
  · exact R89499
  · exact R89501
  · exact R89503
  · exact R89505
  · exact R89507
  · exact R89509
  · exact R89511
  · exact R89513
  · exact R89515
  · exact R89517
  · exact R89519
  · exact R89521
  · exact R89523
  · exact R89525
  · exact R89527
  · exact R89529
  · exact R89531
  · exact R89533
  · exact R89535
  · exact R89537
  · exact R89539
  · exact R89541
  · exact R89543
  · exact R89545
  · exact R89547
  · exact R89549
  · exact R89551
  · exact R89553
  · exact R89555
  · exact R89557
  · exact R89559
  · exact R89561
  · exact R89563
  · exact R89565
  · exact R89567
  · exact R89569
  · exact R89571
  · exact R89573
  · exact R89575
  · exact R89577
  · exact R89579
  · exact R89581
  · exact R89583
  · exact R89585
  · exact R89587
  · exact R89589
  · exact R89591
  · exact R89593
  · exact R89595
  · exact R89597
  · exact R89599
  · exact R89601
  · exact R89603
  · exact R89605
  · exact R89607
  · exact R89609
  · exact R89611
  · exact R89613
  · exact R89615
  · exact R89617
  · exact R89619
  · exact R89621
  · exact R89623
  · exact R89625
  · exact R89627
  · exact R89629
  · exact R89631
  · exact R89633
  · exact R89635
  · exact R89637
  · exact R89639
  · exact R89641
  · exact R89643
  · exact R89645
  · exact R89647
  · exact R89649
  · exact R89651
  · exact R89653
  · exact R89655
  · exact R89657
  · exact R89659
  · exact R89661
  · exact R89663
  · exact R89665
  · exact R89667
  · exact R89669
  · exact R89671
  · exact R89673
  · exact R89675
  · exact R89677
  · exact R89679
  · exact R89681
  · exact R89683
  · exact R89685
  · exact R89687
  · exact R89689
  · exact R89691
  · exact R89693
  · exact R89695
  · exact R89697
  · exact R89699
  · exact R89701
  · exact R89703
  · exact R89705
  · exact R89707
  · exact R89709
  · exact R89711
  · exact R89713
  · exact R89715
  · exact R89717
  · exact R89719
  · exact R89721
  · exact R89723
  · exact R89725
  · exact R89727
  · exact R89729
  · exact R89731
  · exact R89733
  · exact R89735
  · exact R89737
  · exact R89739
  · exact R89741
  · exact R89743
  · exact R89745
  · exact R89747
  · exact R89749
  · exact R89751
  · exact R89753
  · exact R89755
  · exact R89757
  · exact R89759
  · exact R89761
  · exact R89763
  · exact R89765
  · exact R89767
  · exact R89769
  · exact R89771
  · exact R89773
  · exact R89775
  · exact R89777
  · exact R89779
  · exact R89781
  · exact R89783
  · exact R89785
  · exact R89787
  · exact R89789
  · exact R89791
  · exact R89793
  · exact R89795
  · exact R89797
  · exact R89799
  · exact R89801
  · exact R89803
  · exact R89805
  · exact R89807
  · exact R89809
  · exact R89811
  · exact R89813
  · exact R89815
  · exact R89817
  · exact R89819
  · exact R89821
  · exact R89823
  · exact R89825
  · exact R89827
  · exact R89829
  · exact R89831
  · exact R89833
  · exact R89835
  · exact R89837
  · exact R89839
  · exact R89841
  · exact R89843
  · exact R89845
  · exact R89847
  · exact R89849
  · exact R89851
  · exact R89853
  · exact R89855
  · exact R89857
  · exact R89859
  · exact R89861
  · exact R89863
  · exact R89865
  · exact R89867
  · exact R89869
  · exact R89871
  · exact R89873
  · exact R89875
  · exact R89877
  · exact R89879
  · exact R89881
  · exact R89883
  · exact R89885
  · exact R89887
  · exact R89889
  · exact R89891
  · exact R89893
  · exact R89895
  · exact R89897
  · exact R89899
  · exact R89901
  · exact R89903
  · exact R89905
  · exact R89907
  · exact R89909
  · exact R89911
  · exact R89913
  · exact R89915
  · exact R89917
  · exact R89919
  · exact R89921
  · exact R89923
  · exact R89925
  · exact R89927

theorem C2 (j : ℕ) (h1 : 44964 ≤ j) (h2 : j ≤ 45564) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R89929
  · exact R89931
  · exact R89933
  · exact R89935
  · exact R89937
  · exact R89939
  · exact R89941
  · exact R89943
  · exact R89945
  · exact R89947
  · exact R89949
  · exact R89951
  · exact R89953
  · exact R89955
  · exact R89957
  · exact R89959
  · exact R89961
  · exact R89963
  · exact R89965
  · exact R89967
  · exact R89969
  · exact R89971
  · exact R89973
  · exact R89975
  · exact R89977
  · exact R89979
  · exact R89981
  · exact R89983
  · exact R89985
  · exact R89987
  · exact R89989
  · exact R89991
  · exact R89993
  · exact R89995
  · exact R89997
  · exact R89999
  · exact R90001
  · exact R90003
  · exact R90005
  · exact R90007
  · exact R90009
  · exact R90011
  · exact R90013
  · exact R90015
  · exact R90017
  · exact R90019
  · exact R90021
  · exact R90023
  · exact R90025
  · exact R90027
  · exact R90029
  · exact R90031
  · exact R90033
  · exact R90035
  · exact R90037
  · exact R90039
  · exact R90041
  · exact R90043
  · exact R90045
  · exact R90047
  · exact R90049
  · exact R90051
  · exact R90053
  · exact R90055
  · exact R90057
  · exact R90059
  · exact R90061
  · exact R90063
  · exact R90065
  · exact R90067
  · exact R90069
  · exact R90071
  · exact R90073
  · exact R90075
  · exact R90077
  · exact R90079
  · exact R90081
  · exact R90083
  · exact R90085
  · exact R90087
  · exact R90089
  · exact R90091
  · exact R90093
  · exact R90095
  · exact R90097
  · exact R90099
  · exact R90101
  · exact R90103
  · exact R90105
  · exact R90107
  · exact R90109
  · exact R90111
  · exact R90113
  · exact R90115
  · exact R90117
  · exact R90119
  · exact R90121
  · exact R90123
  · exact R90125
  · exact R90127
  · exact R90129
  · exact R90131
  · exact R90133
  · exact R90135
  · exact R90137
  · exact R90139
  · exact R90141
  · exact R90143
  · exact R90145
  · exact R90147
  · exact R90149
  · exact R90151
  · exact R90153
  · exact R90155
  · exact R90157
  · exact R90159
  · exact R90161
  · exact R90163
  · exact R90165
  · exact R90167
  · exact R90169
  · exact R90171
  · exact R90173
  · exact R90175
  · exact R90177
  · exact R90179
  · exact R90181
  · exact R90183
  · exact R90185
  · exact R90187
  · exact R90189
  · exact R90191
  · exact R90193
  · exact R90195
  · exact R90197
  · exact R90199
  · exact R90201
  · exact R90203
  · exact R90205
  · exact R90207
  · exact R90209
  · exact R90211
  · exact R90213
  · exact R90215
  · exact R90217
  · exact R90219
  · exact R90221
  · exact R90223
  · exact R90225
  · exact R90227
  · exact R90229
  · exact R90231
  · exact R90233
  · exact R90235
  · exact R90237
  · exact R90239
  · exact R90241
  · exact R90243
  · exact R90245
  · exact R90247
  · exact R90249
  · exact R90251
  · exact R90253
  · exact R90255
  · exact R90257
  · exact R90259
  · exact R90261
  · exact R90263
  · exact R90265
  · exact R90267
  · exact R90269
  · exact R90271
  · exact R90273
  · exact R90275
  · exact R90277
  · exact R90279
  · exact R90281
  · exact R90283
  · exact R90285
  · exact R90287
  · exact R90289
  · exact R90291
  · exact R90293
  · exact R90295
  · exact R90297
  · exact R90299
  · exact R90301
  · exact R90303
  · exact R90305
  · exact R90307
  · exact R90309
  · exact R90311
  · exact R90313
  · exact R90315
  · exact R90317
  · exact R90319
  · exact R90321
  · exact R90323
  · exact R90325
  · exact R90327
  · exact R90329
  · exact R90331
  · exact R90333
  · exact R90335
  · exact R90337
  · exact R90339
  · exact R90341
  · exact R90343
  · exact R90345
  · exact R90347
  · exact R90349
  · exact R90351
  · exact R90353
  · exact R90355
  · exact R90357
  · exact R90359
  · exact R90361
  · exact R90363
  · exact R90365
  · exact R90367
  · exact R90369
  · exact R90371
  · exact R90373
  · exact R90375
  · exact R90377
  · exact R90379
  · exact R90381
  · exact R90383
  · exact R90385
  · exact R90387
  · exact R90389
  · exact R90391
  · exact R90393
  · exact R90395
  · exact R90397
  · exact R90399
  · exact R90401
  · exact R90403
  · exact R90405
  · exact R90407
  · exact R90409
  · exact R90411
  · exact R90413
  · exact R90415
  · exact R90417
  · exact R90419
  · exact R90421
  · exact R90423
  · exact R90425
  · exact R90427
  · exact R90429
  · exact R90431
  · exact R90433
  · exact R90435
  · exact R90437
  · exact R90439
  · exact R90441
  · exact R90443
  · exact R90445
  · exact R90447
  · exact R90449
  · exact R90451
  · exact R90453
  · exact R90455
  · exact R90457
  · exact R90459
  · exact R90461
  · exact R90463
  · exact R90465
  · exact R90467
  · exact R90469
  · exact R90471
  · exact R90473
  · exact R90475
  · exact R90477
  · exact R90479
  · exact R90481
  · exact R90483
  · exact R90485
  · exact R90487
  · exact R90489
  · exact R90491
  · exact R90493
  · exact R90495
  · exact R90497
  · exact R90499
  · exact R90501
  · exact R90503
  · exact R90505
  · exact R90507
  · exact R90509
  · exact R90511
  · exact R90513
  · exact R90515
  · exact R90517
  · exact R90519
  · exact R90521
  · exact R90523
  · exact R90525
  · exact R90527
  · exact R90529
  · exact R90531
  · exact R90533
  · exact R90535
  · exact R90537
  · exact R90539
  · exact R90541
  · exact R90543
  · exact R90545
  · exact R90547
  · exact R90549
  · exact R90551
  · exact R90553
  · exact R90555
  · exact R90557
  · exact R90559
  · exact R90561
  · exact R90563
  · exact R90565
  · exact R90567
  · exact R90569
  · exact R90571
  · exact R90573
  · exact R90575
  · exact R90577
  · exact R90579
  · exact R90581
  · exact R90583
  · exact R90585
  · exact R90587
  · exact R90589
  · exact R90591
  · exact R90593
  · exact R90595
  · exact R90597
  · exact R90599
  · exact R90601
  · exact R90603
  · exact R90605
  · exact R90607
  · exact R90609
  · exact R90611
  · exact R90613
  · exact R90615
  · exact R90617
  · exact R90619
  · exact R90621
  · exact R90623
  · exact R90625
  · exact R90627
  · exact R90629
  · exact R90631
  · exact R90633
  · exact R90635
  · exact R90637
  · exact R90639
  · exact R90641
  · exact R90643
  · exact R90645
  · exact R90647
  · exact R90649
  · exact R90651
  · exact R90653
  · exact R90655
  · exact R90657
  · exact R90659
  · exact R90661
  · exact R90663
  · exact R90665
  · exact R90667
  · exact R90669
  · exact R90671
  · exact R90673
  · exact R90675
  · exact R90677
  · exact R90679
  · exact R90681
  · exact R90683
  · exact R90685
  · exact R90687
  · exact R90689
  · exact R90691
  · exact R90693
  · exact R90695
  · exact R90697
  · exact R90699
  · exact R90701
  · exact R90703
  · exact R90705
  · exact R90707
  · exact R90709
  · exact R90711
  · exact R90713
  · exact R90715
  · exact R90717
  · exact R90719
  · exact R90721
  · exact R90723
  · exact R90725
  · exact R90727
  · exact R90729
  · exact R90731
  · exact R90733
  · exact R90735
  · exact R90737
  · exact R90739
  · exact R90741
  · exact R90743
  · exact R90745
  · exact R90747
  · exact R90749
  · exact R90751
  · exact R90753
  · exact R90755
  · exact R90757
  · exact R90759
  · exact R90761
  · exact R90763
  · exact R90765
  · exact R90767
  · exact R90769
  · exact R90771
  · exact R90773
  · exact R90775
  · exact R90777
  · exact R90779
  · exact R90781
  · exact R90783
  · exact R90785
  · exact R90787
  · exact R90789
  · exact R90791
  · exact R90793
  · exact R90795
  · exact R90797
  · exact R90799
  · exact R90801
  · exact R90803
  · exact R90805
  · exact R90807
  · exact R90809
  · exact R90811
  · exact R90813
  · exact R90815
  · exact R90817
  · exact R90819
  · exact R90821
  · exact R90823
  · exact R90825
  · exact R90827
  · exact R90829
  · exact R90831
  · exact R90833
  · exact R90835
  · exact R90837
  · exact R90839
  · exact R90841
  · exact R90843
  · exact R90845
  · exact R90847
  · exact R90849
  · exact R90851
  · exact R90853
  · exact R90855
  · exact R90857
  · exact R90859
  · exact R90861
  · exact R90863
  · exact R90865
  · exact R90867
  · exact R90869
  · exact R90871
  · exact R90873
  · exact R90875
  · exact R90877
  · exact R90879
  · exact R90881
  · exact R90883
  · exact R90885
  · exact R90887
  · exact R90889
  · exact R90891
  · exact R90893
  · exact R90895
  · exact R90897
  · exact R90899
  · exact R90901
  · exact R90903
  · exact R90905
  · exact R90907
  · exact R90909
  · exact R90911
  · exact R90913
  · exact R90915
  · exact R90917
  · exact R90919
  · exact R90921
  · exact R90923
  · exact R90925
  · exact R90927
  · exact R90929
  · exact R90931
  · exact R90933
  · exact R90935
  · exact R90937
  · exact R90939
  · exact R90941
  · exact R90943
  · exact R90945
  · exact R90947
  · exact R90949
  · exact R90951
  · exact R90953
  · exact R90955
  · exact R90957
  · exact R90959
  · exact R90961
  · exact R90963
  · exact R90965
  · exact R90967
  · exact R90969
  · exact R90971
  · exact R90973
  · exact R90975
  · exact R90977
  · exact R90979
  · exact R90981
  · exact R90983
  · exact R90985
  · exact R90987
  · exact R90989
  · exact R90991
  · exact R90993
  · exact R90995
  · exact R90997
  · exact R90999
  · exact R91001
  · exact R91003
  · exact R91005
  · exact R91007
  · exact R91009
  · exact R91011
  · exact R91013
  · exact R91015
  · exact R91017
  · exact R91019
  · exact R91021
  · exact R91023
  · exact R91025
  · exact R91027
  · exact R91029
  · exact R91031
  · exact R91033
  · exact R91035
  · exact R91037
  · exact R91039
  · exact R91041
  · exact R91043
  · exact R91045
  · exact R91047
  · exact R91049
  · exact R91051
  · exact R91053
  · exact R91055
  · exact R91057
  · exact R91059
  · exact R91061
  · exact R91063
  · exact R91065
  · exact R91067
  · exact R91069
  · exact R91071
  · exact R91073
  · exact R91075
  · exact R91077
  · exact R91079
  · exact R91081
  · exact R91083
  · exact R91085
  · exact R91087
  · exact R91089
  · exact R91091
  · exact R91093
  · exact R91095
  · exact R91097
  · exact R91099
  · exact R91101
  · exact R91103
  · exact R91105
  · exact R91107
  · exact R91109
  · exact R91111
  · exact R91113
  · exact R91115
  · exact R91117
  · exact R91119
  · exact R91121
  · exact R91123
  · exact R91125
  · exact R91127
  · exact R91129

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 91129) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 87129 with hlo | hlo
  · exact syracuse_reaches_one_below_87129 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 44264 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 44964 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
