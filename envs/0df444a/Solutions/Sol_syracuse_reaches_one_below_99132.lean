-- Prove2me | solution 1 for syracuse_reaches_one_below_99132
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T06:55:46.988585+00:00
-- url     : https://prove2.me/submissions/c30e21df-362a-400e-b966-af14da5e288a

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_95131

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 95130) : Reach n :=
  syracuse_reaches_one_below_95131 n h1 h2 h3
theorem R98305 : Reach 98305 := rs (se 2 (by rfl) ⟨36864, by rfl⟩) (B 73729 (by norm_num) ⟨36864, by rfl⟩ (by norm_num))
theorem R98309 : Reach 98309 := rs (se 4 (by rfl) ⟨9216, by rfl⟩) (B 18433 (by norm_num) ⟨9216, by rfl⟩ (by norm_num))
theorem R98313 : Reach 98313 := rs (se 2 (by rfl) ⟨36867, by rfl⟩) (B 73735 (by norm_num) ⟨36867, by rfl⟩ (by norm_num))
theorem R98317 : Reach 98317 := rs (se 3 (by rfl) ⟨18434, by rfl⟩) (B 36869 (by norm_num) ⟨18434, by rfl⟩ (by norm_num))
theorem R98321 : Reach 98321 := rs (se 2 (by rfl) ⟨36870, by rfl⟩) (B 73741 (by norm_num) ⟨36870, by rfl⟩ (by norm_num))
theorem R98325 : Reach 98325 := rs (se 6 (by rfl) ⟨2304, by rfl⟩) (B 4609 (by norm_num) ⟨2304, by rfl⟩ (by norm_num))
theorem R98329 : Reach 98329 := rs (se 2 (by rfl) ⟨36873, by rfl⟩) (B 73747 (by norm_num) ⟨36873, by rfl⟩ (by norm_num))
theorem R98333 : Reach 98333 := rs (se 3 (by rfl) ⟨18437, by rfl⟩) (B 36875 (by norm_num) ⟨18437, by rfl⟩ (by norm_num))
theorem R98337 : Reach 98337 := rs (se 2 (by rfl) ⟨36876, by rfl⟩) (B 73753 (by norm_num) ⟨36876, by rfl⟩ (by norm_num))
theorem R98341 : Reach 98341 := rs (se 4 (by rfl) ⟨9219, by rfl⟩) (B 18439 (by norm_num) ⟨9219, by rfl⟩ (by norm_num))
theorem R98345 : Reach 98345 := rs (se 2 (by rfl) ⟨36879, by rfl⟩) (B 73759 (by norm_num) ⟨36879, by rfl⟩ (by norm_num))
theorem R98349 : Reach 98349 := rs (se 3 (by rfl) ⟨18440, by rfl⟩) (B 36881 (by norm_num) ⟨18440, by rfl⟩ (by norm_num))
theorem R98353 : Reach 98353 := rs (se 2 (by rfl) ⟨36882, by rfl⟩) (B 73765 (by norm_num) ⟨36882, by rfl⟩ (by norm_num))
theorem R98357 : Reach 98357 := rs (se 5 (by rfl) ⟨4610, by rfl⟩) (B 9221 (by norm_num) ⟨4610, by rfl⟩ (by norm_num))
theorem R98361 : Reach 98361 := rs (se 2 (by rfl) ⟨36885, by rfl⟩) (B 73771 (by norm_num) ⟨36885, by rfl⟩ (by norm_num))
theorem R98365 : Reach 98365 := rs (se 3 (by rfl) ⟨18443, by rfl⟩) (B 36887 (by norm_num) ⟨18443, by rfl⟩ (by norm_num))
theorem R98369 : Reach 98369 := rs (se 2 (by rfl) ⟨36888, by rfl⟩) (B 73777 (by norm_num) ⟨36888, by rfl⟩ (by norm_num))
theorem R98373 : Reach 98373 := rs (se 4 (by rfl) ⟨9222, by rfl⟩) (B 18445 (by norm_num) ⟨9222, by rfl⟩ (by norm_num))
theorem R98377 : Reach 98377 := rs (se 2 (by rfl) ⟨36891, by rfl⟩) (B 73783 (by norm_num) ⟨36891, by rfl⟩ (by norm_num))
theorem R98381 : Reach 98381 := rs (se 3 (by rfl) ⟨18446, by rfl⟩) (B 36893 (by norm_num) ⟨18446, by rfl⟩ (by norm_num))
theorem R98385 : Reach 98385 := rs (se 2 (by rfl) ⟨36894, by rfl⟩) (B 73789 (by norm_num) ⟨36894, by rfl⟩ (by norm_num))
theorem R98389 : Reach 98389 := rs (se 8 (by rfl) ⟨576, by rfl⟩) (B 1153 (by norm_num) ⟨576, by rfl⟩ (by norm_num))
theorem R98393 : Reach 98393 := rs (se 2 (by rfl) ⟨36897, by rfl⟩) (B 73795 (by norm_num) ⟨36897, by rfl⟩ (by norm_num))
theorem R98397 : Reach 98397 := rs (se 3 (by rfl) ⟨18449, by rfl⟩) (B 36899 (by norm_num) ⟨18449, by rfl⟩ (by norm_num))
theorem R98401 : Reach 98401 := rs (se 2 (by rfl) ⟨36900, by rfl⟩) (B 73801 (by norm_num) ⟨36900, by rfl⟩ (by norm_num))
theorem R98405 : Reach 98405 := rs (se 4 (by rfl) ⟨9225, by rfl⟩) (B 18451 (by norm_num) ⟨9225, by rfl⟩ (by norm_num))
theorem R98409 : Reach 98409 := rs (se 2 (by rfl) ⟨36903, by rfl⟩) (B 73807 (by norm_num) ⟨36903, by rfl⟩ (by norm_num))
theorem R98413 : Reach 98413 := rs (se 3 (by rfl) ⟨18452, by rfl⟩) (B 36905 (by norm_num) ⟨18452, by rfl⟩ (by norm_num))
theorem R98417 : Reach 98417 := rs (se 2 (by rfl) ⟨36906, by rfl⟩) (B 73813 (by norm_num) ⟨36906, by rfl⟩ (by norm_num))
theorem R262261 : Reach 262261 := rs (se 5 (by rfl) ⟨12293, by rfl⟩) (B 24587 (by norm_num) ⟨12293, by rfl⟩ (by norm_num))
theorem R163957 : Reach 163957 := rs (se 5 (by rfl) ⟨7685, by rfl⟩) (B 15371 (by norm_num) ⟨7685, by rfl⟩ (by norm_num))
theorem R98421 : Reach 98421 := rs (se 5 (by rfl) ⟨4613, by rfl⟩) (B 9227 (by norm_num) ⟨4613, by rfl⟩ (by norm_num))
theorem R98425 : Reach 98425 := rs (se 2 (by rfl) ⟨36909, by rfl⟩) (B 73819 (by norm_num) ⟨36909, by rfl⟩ (by norm_num))
theorem R98429 : Reach 98429 := rs (se 3 (by rfl) ⟨18455, by rfl⟩) (B 36911 (by norm_num) ⟨18455, by rfl⟩ (by norm_num))
theorem R98433 : Reach 98433 := rs (se 2 (by rfl) ⟨36912, by rfl⟩) (B 73825 (by norm_num) ⟨36912, by rfl⟩ (by norm_num))
theorem R98437 : Reach 98437 := rs (se 4 (by rfl) ⟨9228, by rfl⟩) (B 18457 (by norm_num) ⟨9228, by rfl⟩ (by norm_num))
theorem R98441 : Reach 98441 := rs (se 2 (by rfl) ⟨36915, by rfl⟩) (B 73831 (by norm_num) ⟨36915, by rfl⟩ (by norm_num))
theorem R98445 : Reach 98445 := rs (se 3 (by rfl) ⟨18458, by rfl⟩) (B 36917 (by norm_num) ⟨18458, by rfl⟩ (by norm_num))
theorem R98449 : Reach 98449 := rs (se 2 (by rfl) ⟨36918, by rfl⟩) (B 73837 (by norm_num) ⟨36918, by rfl⟩ (by norm_num))
theorem R491669 : Reach 491669 := rs (se 6 (by rfl) ⟨11523, by rfl⟩) (B 23047 (by norm_num) ⟨11523, by rfl⟩ (by norm_num))
theorem R98453 : Reach 98453 := rs (se 6 (by rfl) ⟨2307, by rfl⟩) (B 4615 (by norm_num) ⟨2307, by rfl⟩ (by norm_num))
theorem R98457 : Reach 98457 := rs (se 2 (by rfl) ⟨36921, by rfl⟩) (B 73843 (by norm_num) ⟨36921, by rfl⟩ (by norm_num))
theorem R98461 : Reach 98461 := rs (se 3 (by rfl) ⟨18461, by rfl⟩) (B 36923 (by norm_num) ⟨18461, by rfl⟩ (by norm_num))
theorem R98465 : Reach 98465 := rs (se 2 (by rfl) ⟨36924, by rfl⟩) (B 73849 (by norm_num) ⟨36924, by rfl⟩ (by norm_num))
theorem R98469 : Reach 98469 := rs (se 4 (by rfl) ⟨9231, by rfl⟩) (B 18463 (by norm_num) ⟨9231, by rfl⟩ (by norm_num))
theorem R98473 : Reach 98473 := rs (se 2 (by rfl) ⟨36927, by rfl⟩) (B 73855 (by norm_num) ⟨36927, by rfl⟩ (by norm_num))
theorem R98477 : Reach 98477 := rs (se 3 (by rfl) ⟨18464, by rfl⟩) (B 36929 (by norm_num) ⟨18464, by rfl⟩ (by norm_num))
theorem R98481 : Reach 98481 := rs (se 2 (by rfl) ⟨36930, by rfl⟩) (B 73861 (by norm_num) ⟨36930, by rfl⟩ (by norm_num))
theorem R98485 : Reach 98485 := rs (se 5 (by rfl) ⟨4616, by rfl⟩) (B 9233 (by norm_num) ⟨4616, by rfl⟩ (by norm_num))
theorem R98489 : Reach 98489 := rs (se 2 (by rfl) ⟨36933, by rfl⟩) (B 73867 (by norm_num) ⟨36933, by rfl⟩ (by norm_num))
theorem R98493 : Reach 98493 := rs (se 3 (by rfl) ⟨18467, by rfl⟩) (B 36935 (by norm_num) ⟨18467, by rfl⟩ (by norm_num))
theorem R98497 : Reach 98497 := rs (se 2 (by rfl) ⟨36936, by rfl⟩) (B 73873 (by norm_num) ⟨36936, by rfl⟩ (by norm_num))
theorem R98501 : Reach 98501 := rs (se 4 (by rfl) ⟨9234, by rfl⟩) (B 18469 (by norm_num) ⟨9234, by rfl⟩ (by norm_num))
theorem R98505 : Reach 98505 := rs (se 2 (by rfl) ⟨36939, by rfl⟩) (B 73879 (by norm_num) ⟨36939, by rfl⟩ (by norm_num))
theorem R164045 : Reach 164045 := rs (se 3 (by rfl) ⟨30758, by rfl⟩) (B 61517 (by norm_num) ⟨30758, by rfl⟩ (by norm_num))
theorem R98509 : Reach 98509 := rs (se 3 (by rfl) ⟨18470, by rfl⟩) (B 36941 (by norm_num) ⟨18470, by rfl⟩ (by norm_num))
theorem R98513 : Reach 98513 := rs (se 2 (by rfl) ⟨36942, by rfl⟩) (B 73885 (by norm_num) ⟨36942, by rfl⟩ (by norm_num))
theorem R98517 : Reach 98517 := rs (se 7 (by rfl) ⟨1154, by rfl⟩) (B 2309 (by norm_num) ⟨1154, by rfl⟩ (by norm_num))
theorem R98521 : Reach 98521 := rs (se 2 (by rfl) ⟨36945, by rfl⟩) (B 73891 (by norm_num) ⟨36945, by rfl⟩ (by norm_num))
theorem R98525 : Reach 98525 := rs (se 3 (by rfl) ⟨18473, by rfl⟩) (B 36947 (by norm_num) ⟨18473, by rfl⟩ (by norm_num))
theorem R98529 : Reach 98529 := rs (se 2 (by rfl) ⟨36948, by rfl⟩) (B 73897 (by norm_num) ⟨36948, by rfl⟩ (by norm_num))
theorem R98533 : Reach 98533 := rs (se 4 (by rfl) ⟨9237, by rfl⟩) (B 18475 (by norm_num) ⟨9237, by rfl⟩ (by norm_num))
theorem R98537 : Reach 98537 := rs (se 2 (by rfl) ⟨36951, by rfl⟩) (B 73903 (by norm_num) ⟨36951, by rfl⟩ (by norm_num))
theorem R98541 : Reach 98541 := rs (se 3 (by rfl) ⟨18476, by rfl⟩) (B 36953 (by norm_num) ⟨18476, by rfl⟩ (by norm_num))
theorem R98545 : Reach 98545 := rs (se 2 (by rfl) ⟨36954, by rfl⟩) (B 73909 (by norm_num) ⟨36954, by rfl⟩ (by norm_num))
theorem R98549 : Reach 98549 := rs (se 5 (by rfl) ⟨4619, by rfl⟩) (B 9239 (by norm_num) ⟨4619, by rfl⟩ (by norm_num))
theorem R98553 : Reach 98553 := rs (se 2 (by rfl) ⟨36957, by rfl⟩) (B 73915 (by norm_num) ⟨36957, by rfl⟩ (by norm_num))
theorem R98557 : Reach 98557 := rs (se 3 (by rfl) ⟨18479, by rfl⟩) (B 36959 (by norm_num) ⟨18479, by rfl⟩ (by norm_num))
theorem R98561 : Reach 98561 := rs (se 2 (by rfl) ⟨36960, by rfl⟩) (B 73921 (by norm_num) ⟨36960, by rfl⟩ (by norm_num))
theorem R327941 : Reach 327941 := rs (se 4 (by rfl) ⟨30744, by rfl⟩) (B 61489 (by norm_num) ⟨30744, by rfl⟩ (by norm_num))
theorem R98565 : Reach 98565 := rs (se 4 (by rfl) ⟨9240, by rfl⟩) (B 18481 (by norm_num) ⟨9240, by rfl⟩ (by norm_num))
theorem R98569 : Reach 98569 := rs (se 2 (by rfl) ⟨36963, by rfl⟩) (B 73927 (by norm_num) ⟨36963, by rfl⟩ (by norm_num))
theorem R98573 : Reach 98573 := rs (se 3 (by rfl) ⟨18482, by rfl⟩) (B 36965 (by norm_num) ⟨18482, by rfl⟩ (by norm_num))
theorem R98577 : Reach 98577 := rs (se 2 (by rfl) ⟨36966, by rfl⟩) (B 73933 (by norm_num) ⟨36966, by rfl⟩ (by norm_num))
theorem R98581 : Reach 98581 := rs (se 6 (by rfl) ⟨2310, by rfl⟩) (B 4621 (by norm_num) ⟨2310, by rfl⟩ (by norm_num))
theorem R98585 : Reach 98585 := rs (se 2 (by rfl) ⟨36969, by rfl⟩) (B 73939 (by norm_num) ⟨36969, by rfl⟩ (by norm_num))
theorem R98589 : Reach 98589 := rs (se 3 (by rfl) ⟨18485, by rfl⟩) (B 36971 (by norm_num) ⟨18485, by rfl⟩ (by norm_num))
theorem R98593 : Reach 98593 := rs (se 2 (by rfl) ⟨36972, by rfl⟩) (B 73945 (by norm_num) ⟨36972, by rfl⟩ (by norm_num))
theorem R98597 : Reach 98597 := rs (se 4 (by rfl) ⟨9243, by rfl⟩) (B 18487 (by norm_num) ⟨9243, by rfl⟩ (by norm_num))
theorem R98601 : Reach 98601 := rs (se 2 (by rfl) ⟨36975, by rfl⟩) (B 73951 (by norm_num) ⟨36975, by rfl⟩ (by norm_num))
theorem R98605 : Reach 98605 := rs (se 3 (by rfl) ⟨18488, by rfl⟩) (B 36977 (by norm_num) ⟨18488, by rfl⟩ (by norm_num))
theorem R98609 : Reach 98609 := rs (se 2 (by rfl) ⟨36978, by rfl⟩) (B 73957 (by norm_num) ⟨36978, by rfl⟩ (by norm_num))
theorem R98613 : Reach 98613 := rs (se 5 (by rfl) ⟨4622, by rfl⟩) (B 9245 (by norm_num) ⟨4622, by rfl⟩ (by norm_num))
theorem R98617 : Reach 98617 := rs (se 2 (by rfl) ⟨36981, by rfl⟩) (B 73963 (by norm_num) ⟨36981, by rfl⟩ (by norm_num))
theorem R98621 : Reach 98621 := rs (se 3 (by rfl) ⟨18491, by rfl⟩) (B 36983 (by norm_num) ⟨18491, by rfl⟩ (by norm_num))
theorem R98625 : Reach 98625 := rs (se 2 (by rfl) ⟨36984, by rfl⟩) (B 73969 (by norm_num) ⟨36984, by rfl⟩ (by norm_num))
theorem R98629 : Reach 98629 := rs (se 4 (by rfl) ⟨9246, by rfl⟩) (B 18493 (by norm_num) ⟨9246, by rfl⟩ (by norm_num))
theorem R98633 : Reach 98633 := rs (se 2 (by rfl) ⟨36987, by rfl⟩) (B 73975 (by norm_num) ⟨36987, by rfl⟩ (by norm_num))
theorem R164173 : Reach 164173 := rs (se 3 (by rfl) ⟨30782, by rfl⟩) (B 61565 (by norm_num) ⟨30782, by rfl⟩ (by norm_num))
theorem R98637 : Reach 98637 := rs (se 3 (by rfl) ⟨18494, by rfl⟩) (B 36989 (by norm_num) ⟨18494, by rfl⟩ (by norm_num))
theorem R98641 : Reach 98641 := rs (se 2 (by rfl) ⟨36990, by rfl⟩) (B 73981 (by norm_num) ⟨36990, by rfl⟩ (by norm_num))
theorem R98645 : Reach 98645 := rs (se 10 (by rfl) ⟨144, by rfl⟩) (B 289 (by norm_num) ⟨144, by rfl⟩ (by norm_num))
theorem R98649 : Reach 98649 := rs (se 2 (by rfl) ⟨36993, by rfl⟩) (B 73987 (by norm_num) ⟨36993, by rfl⟩ (by norm_num))
theorem R98653 : Reach 98653 := rs (se 3 (by rfl) ⟨18497, by rfl⟩) (B 36995 (by norm_num) ⟨18497, by rfl⟩ (by norm_num))
theorem R98657 : Reach 98657 := rs (se 2 (by rfl) ⟨36996, by rfl⟩) (B 73993 (by norm_num) ⟨36996, by rfl⟩ (by norm_num))
theorem R98661 : Reach 98661 := rs (se 4 (by rfl) ⟨9249, by rfl⟩) (B 18499 (by norm_num) ⟨9249, by rfl⟩ (by norm_num))
theorem R98665 : Reach 98665 := rs (se 2 (by rfl) ⟨36999, by rfl⟩) (B 73999 (by norm_num) ⟨36999, by rfl⟩ (by norm_num))
theorem R98669 : Reach 98669 := rs (se 3 (by rfl) ⟨18500, by rfl⟩) (B 37001 (by norm_num) ⟨18500, by rfl⟩ (by norm_num))
theorem R98673 : Reach 98673 := rs (se 2 (by rfl) ⟨37002, by rfl⟩) (B 74005 (by norm_num) ⟨37002, by rfl⟩ (by norm_num))
theorem R98677 : Reach 98677 := rs (se 5 (by rfl) ⟨4625, by rfl⟩) (B 9251 (by norm_num) ⟨4625, by rfl⟩ (by norm_num))
theorem R98681 : Reach 98681 := rs (se 2 (by rfl) ⟨37005, by rfl⟩) (B 74011 (by norm_num) ⟨37005, by rfl⟩ (by norm_num))
theorem R98685 : Reach 98685 := rs (se 3 (by rfl) ⟨18503, by rfl⟩) (B 37007 (by norm_num) ⟨18503, by rfl⟩ (by norm_num))
theorem R98689 : Reach 98689 := rs (se 2 (by rfl) ⟨37008, by rfl⟩) (B 74017 (by norm_num) ⟨37008, by rfl⟩ (by norm_num))
theorem R98693 : Reach 98693 := rs (se 4 (by rfl) ⟨9252, by rfl⟩) (B 18505 (by norm_num) ⟨9252, by rfl⟩ (by norm_num))
theorem R98697 : Reach 98697 := rs (se 2 (by rfl) ⟨37011, by rfl⟩) (B 74023 (by norm_num) ⟨37011, by rfl⟩ (by norm_num))
theorem R98701 : Reach 98701 := rs (se 3 (by rfl) ⟨18506, by rfl⟩) (B 37013 (by norm_num) ⟨18506, by rfl⟩ (by norm_num))
theorem R98705 : Reach 98705 := rs (se 2 (by rfl) ⟨37014, by rfl⟩) (B 74029 (by norm_num) ⟨37014, by rfl⟩ (by norm_num))
theorem R98709 : Reach 98709 := rs (se 6 (by rfl) ⟨2313, by rfl⟩) (B 4627 (by norm_num) ⟨2313, by rfl⟩ (by norm_num))
theorem R98713 : Reach 98713 := rs (se 2 (by rfl) ⟨37017, by rfl⟩) (B 74035 (by norm_num) ⟨37017, by rfl⟩ (by norm_num))
theorem R98717 : Reach 98717 := rs (se 3 (by rfl) ⟨18509, by rfl⟩) (B 37019 (by norm_num) ⟨18509, by rfl⟩ (by norm_num))
theorem R98721 : Reach 98721 := rs (se 2 (by rfl) ⟨37020, by rfl⟩) (B 74041 (by norm_num) ⟨37020, by rfl⟩ (by norm_num))
theorem R164261 : Reach 164261 := rs (se 4 (by rfl) ⟨15399, by rfl⟩) (B 30799 (by norm_num) ⟨15399, by rfl⟩ (by norm_num))
theorem R98725 : Reach 98725 := rs (se 4 (by rfl) ⟨9255, by rfl⟩) (B 18511 (by norm_num) ⟨9255, by rfl⟩ (by norm_num))
theorem R98729 : Reach 98729 := rs (se 2 (by rfl) ⟨37023, by rfl⟩) (B 74047 (by norm_num) ⟨37023, by rfl⟩ (by norm_num))
theorem R98733 : Reach 98733 := rs (se 3 (by rfl) ⟨18512, by rfl⟩) (B 37025 (by norm_num) ⟨18512, by rfl⟩ (by norm_num))
theorem R98737 : Reach 98737 := rs (se 2 (by rfl) ⟨37026, by rfl⟩) (B 74053 (by norm_num) ⟨37026, by rfl⟩ (by norm_num))
theorem R393653 : Reach 393653 := rs (se 5 (by rfl) ⟨18452, by rfl⟩) (B 36905 (by norm_num) ⟨18452, by rfl⟩ (by norm_num))
theorem R98741 : Reach 98741 := rs (se 5 (by rfl) ⟨4628, by rfl⟩) (B 9257 (by norm_num) ⟨4628, by rfl⟩ (by norm_num))
theorem R98745 : Reach 98745 := rs (se 2 (by rfl) ⟨37029, by rfl⟩) (B 74059 (by norm_num) ⟨37029, by rfl⟩ (by norm_num))
theorem R98749 : Reach 98749 := rs (se 3 (by rfl) ⟨18515, by rfl⟩) (B 37031 (by norm_num) ⟨18515, by rfl⟩ (by norm_num))
theorem R98753 : Reach 98753 := rs (se 2 (by rfl) ⟨37032, by rfl⟩) (B 74065 (by norm_num) ⟨37032, by rfl⟩ (by norm_num))
theorem R98757 : Reach 98757 := rs (se 4 (by rfl) ⟨9258, by rfl⟩) (B 18517 (by norm_num) ⟨9258, by rfl⟩ (by norm_num))
theorem R98761 : Reach 98761 := rs (se 2 (by rfl) ⟨37035, by rfl⟩) (B 74071 (by norm_num) ⟨37035, by rfl⟩ (by norm_num))
theorem R98765 : Reach 98765 := rs (se 3 (by rfl) ⟨18518, by rfl⟩) (B 37037 (by norm_num) ⟨18518, by rfl⟩ (by norm_num))
theorem R98769 : Reach 98769 := rs (se 2 (by rfl) ⟨37038, by rfl⟩) (B 74077 (by norm_num) ⟨37038, by rfl⟩ (by norm_num))
theorem R98773 : Reach 98773 := rs (se 7 (by rfl) ⟨1157, by rfl⟩) (B 2315 (by norm_num) ⟨1157, by rfl⟩ (by norm_num))
theorem R98777 : Reach 98777 := rs (se 2 (by rfl) ⟨37041, by rfl⟩) (B 74083 (by norm_num) ⟨37041, by rfl⟩ (by norm_num))
theorem R98781 : Reach 98781 := rs (se 3 (by rfl) ⟨18521, by rfl⟩) (B 37043 (by norm_num) ⟨18521, by rfl⟩ (by norm_num))
theorem R98785 : Reach 98785 := rs (se 2 (by rfl) ⟨37044, by rfl⟩) (B 74089 (by norm_num) ⟨37044, by rfl⟩ (by norm_num))
theorem R98789 : Reach 98789 := rs (se 4 (by rfl) ⟨9261, by rfl⟩) (B 18523 (by norm_num) ⟨9261, by rfl⟩ (by norm_num))
theorem R98793 : Reach 98793 := rs (se 2 (by rfl) ⟨37047, by rfl⟩) (B 74095 (by norm_num) ⟨37047, by rfl⟩ (by norm_num))
theorem R98797 : Reach 98797 := rs (se 3 (by rfl) ⟨18524, by rfl⟩) (B 37049 (by norm_num) ⟨18524, by rfl⟩ (by norm_num))
theorem R98801 : Reach 98801 := rs (se 2 (by rfl) ⟨37050, by rfl⟩) (B 74101 (by norm_num) ⟨37050, by rfl⟩ (by norm_num))
theorem R98805 : Reach 98805 := rs (se 5 (by rfl) ⟨4631, by rfl⟩) (B 9263 (by norm_num) ⟨4631, by rfl⟩ (by norm_num))
theorem R98809 : Reach 98809 := rs (se 2 (by rfl) ⟨37053, by rfl⟩) (B 74107 (by norm_num) ⟨37053, by rfl⟩ (by norm_num))
theorem R98813 : Reach 98813 := rs (se 3 (by rfl) ⟨18527, by rfl⟩) (B 37055 (by norm_num) ⟨18527, by rfl⟩ (by norm_num))
theorem R98817 : Reach 98817 := rs (se 2 (by rfl) ⟨37056, by rfl⟩) (B 74113 (by norm_num) ⟨37056, by rfl⟩ (by norm_num))
theorem R98821 : Reach 98821 := rs (se 4 (by rfl) ⟨9264, by rfl⟩) (B 18529 (by norm_num) ⟨9264, by rfl⟩ (by norm_num))
theorem R98825 : Reach 98825 := rs (se 2 (by rfl) ⟨37059, by rfl⟩) (B 74119 (by norm_num) ⟨37059, by rfl⟩ (by norm_num))
theorem R98829 : Reach 98829 := rs (se 3 (by rfl) ⟨18530, by rfl⟩) (B 37061 (by norm_num) ⟨18530, by rfl⟩ (by norm_num))
theorem R98833 : Reach 98833 := rs (se 2 (by rfl) ⟨37062, by rfl⟩) (B 74125 (by norm_num) ⟨37062, by rfl⟩ (by norm_num))
theorem R98837 : Reach 98837 := rs (se 6 (by rfl) ⟨2316, by rfl⟩) (B 4633 (by norm_num) ⟨2316, by rfl⟩ (by norm_num))
theorem R98841 : Reach 98841 := rs (se 2 (by rfl) ⟨37065, by rfl⟩) (B 74131 (by norm_num) ⟨37065, by rfl⟩ (by norm_num))
theorem R98845 : Reach 98845 := rs (se 3 (by rfl) ⟨18533, by rfl⟩) (B 37067 (by norm_num) ⟨18533, by rfl⟩ (by norm_num))
theorem R98849 : Reach 98849 := rs (se 2 (by rfl) ⟨37068, by rfl⟩) (B 74137 (by norm_num) ⟨37068, by rfl⟩ (by norm_num))
theorem R164389 : Reach 164389 := rs (se 4 (by rfl) ⟨15411, by rfl⟩) (B 30823 (by norm_num) ⟨15411, by rfl⟩ (by norm_num))
theorem R98853 : Reach 98853 := rs (se 4 (by rfl) ⟨9267, by rfl⟩) (B 18535 (by norm_num) ⟨9267, by rfl⟩ (by norm_num))
theorem R98857 : Reach 98857 := rs (se 2 (by rfl) ⟨37071, by rfl⟩) (B 74143 (by norm_num) ⟨37071, by rfl⟩ (by norm_num))
theorem R98861 : Reach 98861 := rs (se 3 (by rfl) ⟨18536, by rfl⟩) (B 37073 (by norm_num) ⟨18536, by rfl⟩ (by norm_num))
theorem R98865 : Reach 98865 := rs (se 2 (by rfl) ⟨37074, by rfl⟩) (B 74149 (by norm_num) ⟨37074, by rfl⟩ (by norm_num))
theorem R98869 : Reach 98869 := rs (se 5 (by rfl) ⟨4634, by rfl⟩) (B 9269 (by norm_num) ⟨4634, by rfl⟩ (by norm_num))
theorem R98873 : Reach 98873 := rs (se 2 (by rfl) ⟨37077, by rfl⟩) (B 74155 (by norm_num) ⟨37077, by rfl⟩ (by norm_num))
theorem R98877 : Reach 98877 := rs (se 3 (by rfl) ⟨18539, by rfl⟩) (B 37079 (by norm_num) ⟨18539, by rfl⟩ (by norm_num))
theorem R98881 : Reach 98881 := rs (se 2 (by rfl) ⟨37080, by rfl⟩) (B 74161 (by norm_num) ⟨37080, by rfl⟩ (by norm_num))
theorem R98885 : Reach 98885 := rs (se 4 (by rfl) ⟨9270, by rfl⟩) (B 18541 (by norm_num) ⟨9270, by rfl⟩ (by norm_num))
theorem R98889 : Reach 98889 := rs (se 2 (by rfl) ⟨37083, by rfl⟩) (B 74167 (by norm_num) ⟨37083, by rfl⟩ (by norm_num))
theorem R98893 : Reach 98893 := rs (se 3 (by rfl) ⟨18542, by rfl⟩) (B 37085 (by norm_num) ⟨18542, by rfl⟩ (by norm_num))
theorem R98897 : Reach 98897 := rs (se 2 (by rfl) ⟨37086, by rfl⟩) (B 74173 (by norm_num) ⟨37086, by rfl⟩ (by norm_num))
theorem R98901 : Reach 98901 := rs (se 8 (by rfl) ⟨579, by rfl⟩) (B 1159 (by norm_num) ⟨579, by rfl⟩ (by norm_num))
theorem R98905 : Reach 98905 := rs (se 2 (by rfl) ⟨37089, by rfl⟩) (B 74179 (by norm_num) ⟨37089, by rfl⟩ (by norm_num))
theorem R98909 : Reach 98909 := rs (se 3 (by rfl) ⟨18545, by rfl⟩) (B 37091 (by norm_num) ⟨18545, by rfl⟩ (by norm_num))
theorem R98913 : Reach 98913 := rs (se 2 (by rfl) ⟨37092, by rfl⟩) (B 74185 (by norm_num) ⟨37092, by rfl⟩ (by norm_num))
theorem R98917 : Reach 98917 := rs (se 4 (by rfl) ⟨9273, by rfl⟩) (B 18547 (by norm_num) ⟨9273, by rfl⟩ (by norm_num))
theorem R98921 : Reach 98921 := rs (se 2 (by rfl) ⟨37095, by rfl⟩) (B 74191 (by norm_num) ⟨37095, by rfl⟩ (by norm_num))
theorem R98925 : Reach 98925 := rs (se 3 (by rfl) ⟨18548, by rfl⟩) (B 37097 (by norm_num) ⟨18548, by rfl⟩ (by norm_num))
theorem R98929 : Reach 98929 := rs (se 2 (by rfl) ⟨37098, by rfl⟩) (B 74197 (by norm_num) ⟨37098, by rfl⟩ (by norm_num))
theorem R98933 : Reach 98933 := rs (se 5 (by rfl) ⟨4637, by rfl⟩) (B 9275 (by norm_num) ⟨4637, by rfl⟩ (by norm_num))
theorem R98937 : Reach 98937 := rs (se 2 (by rfl) ⟨37101, by rfl⟩) (B 74203 (by norm_num) ⟨37101, by rfl⟩ (by norm_num))
theorem R164477 : Reach 164477 := rs (se 3 (by rfl) ⟨30839, by rfl⟩) (B 61679 (by norm_num) ⟨30839, by rfl⟩ (by norm_num))
theorem R98941 : Reach 98941 := rs (se 3 (by rfl) ⟨18551, by rfl⟩) (B 37103 (by norm_num) ⟨18551, by rfl⟩ (by norm_num))
theorem R98945 : Reach 98945 := rs (se 2 (by rfl) ⟨37104, by rfl⟩) (B 74209 (by norm_num) ⟨37104, by rfl⟩ (by norm_num))
theorem R98949 : Reach 98949 := rs (se 4 (by rfl) ⟨9276, by rfl⟩) (B 18553 (by norm_num) ⟨9276, by rfl⟩ (by norm_num))
theorem R98953 : Reach 98953 := rs (se 2 (by rfl) ⟨37107, by rfl⟩) (B 74215 (by norm_num) ⟨37107, by rfl⟩ (by norm_num))
theorem R98957 : Reach 98957 := rs (se 3 (by rfl) ⟨18554, by rfl⟩) (B 37109 (by norm_num) ⟨18554, by rfl⟩ (by norm_num))
theorem R98961 : Reach 98961 := rs (se 2 (by rfl) ⟨37110, by rfl⟩) (B 74221 (by norm_num) ⟨37110, by rfl⟩ (by norm_num))
theorem R98965 : Reach 98965 := rs (se 6 (by rfl) ⟨2319, by rfl⟩) (B 4639 (by norm_num) ⟨2319, by rfl⟩ (by norm_num))
theorem R98969 : Reach 98969 := rs (se 2 (by rfl) ⟨37113, by rfl⟩) (B 74227 (by norm_num) ⟨37113, by rfl⟩ (by norm_num))
theorem R230045 : Reach 230045 := rs (se 3 (by rfl) ⟨43133, by rfl⟩) (B 86267 (by norm_num) ⟨43133, by rfl⟩ (by norm_num))
theorem R98973 : Reach 98973 := rs (se 3 (by rfl) ⟨18557, by rfl⟩) (B 37115 (by norm_num) ⟨18557, by rfl⟩ (by norm_num))
theorem R98977 : Reach 98977 := rs (se 2 (by rfl) ⟨37116, by rfl⟩) (B 74233 (by norm_num) ⟨37116, by rfl⟩ (by norm_num))
theorem R98981 : Reach 98981 := rs (se 4 (by rfl) ⟨9279, by rfl⟩) (B 18559 (by norm_num) ⟨9279, by rfl⟩ (by norm_num))
theorem R98985 : Reach 98985 := rs (se 2 (by rfl) ⟨37119, by rfl⟩) (B 74239 (by norm_num) ⟨37119, by rfl⟩ (by norm_num))
theorem R98989 : Reach 98989 := rs (se 3 (by rfl) ⟨18560, by rfl⟩) (B 37121 (by norm_num) ⟨18560, by rfl⟩ (by norm_num))
theorem R98993 : Reach 98993 := rs (se 2 (by rfl) ⟨37122, by rfl⟩) (B 74245 (by norm_num) ⟨37122, by rfl⟩ (by norm_num))
theorem R328373 : Reach 328373 := rs (se 5 (by rfl) ⟨15392, by rfl⟩) (B 30785 (by norm_num) ⟨15392, by rfl⟩ (by norm_num))
theorem R98997 : Reach 98997 := rs (se 5 (by rfl) ⟨4640, by rfl⟩) (B 9281 (by norm_num) ⟨4640, by rfl⟩ (by norm_num))
theorem R99001 : Reach 99001 := rs (se 2 (by rfl) ⟨37125, by rfl⟩) (B 74251 (by norm_num) ⟨37125, by rfl⟩ (by norm_num))
theorem R99005 : Reach 99005 := rs (se 3 (by rfl) ⟨18563, by rfl⟩) (B 37127 (by norm_num) ⟨18563, by rfl⟩ (by norm_num))
theorem R99009 : Reach 99009 := rs (se 2 (by rfl) ⟨37128, by rfl⟩) (B 74257 (by norm_num) ⟨37128, by rfl⟩ (by norm_num))
theorem R99013 : Reach 99013 := rs (se 4 (by rfl) ⟨9282, by rfl⟩) (B 18565 (by norm_num) ⟨9282, by rfl⟩ (by norm_num))
theorem R99017 : Reach 99017 := rs (se 2 (by rfl) ⟨37131, by rfl⟩) (B 74263 (by norm_num) ⟨37131, by rfl⟩ (by norm_num))
theorem R99021 : Reach 99021 := rs (se 3 (by rfl) ⟨18566, by rfl⟩) (B 37133 (by norm_num) ⟨18566, by rfl⟩ (by norm_num))
theorem R99025 : Reach 99025 := rs (se 2 (by rfl) ⟨37134, by rfl⟩) (B 74269 (by norm_num) ⟨37134, by rfl⟩ (by norm_num))
theorem R99029 : Reach 99029 := rs (se 7 (by rfl) ⟨1160, by rfl⟩) (B 2321 (by norm_num) ⟨1160, by rfl⟩ (by norm_num))
theorem R99033 : Reach 99033 := rs (se 2 (by rfl) ⟨37137, by rfl⟩) (B 74275 (by norm_num) ⟨37137, by rfl⟩ (by norm_num))
theorem R99037 : Reach 99037 := rs (se 3 (by rfl) ⟨18569, by rfl⟩) (B 37139 (by norm_num) ⟨18569, by rfl⟩ (by norm_num))
theorem R99041 : Reach 99041 := rs (se 2 (by rfl) ⟨37140, by rfl⟩) (B 74281 (by norm_num) ⟨37140, by rfl⟩ (by norm_num))
theorem R328421 : Reach 328421 := rs (se 4 (by rfl) ⟨30789, by rfl⟩) (B 61579 (by norm_num) ⟨30789, by rfl⟩ (by norm_num))
theorem R99045 : Reach 99045 := rs (se 4 (by rfl) ⟨9285, by rfl⟩) (B 18571 (by norm_num) ⟨9285, by rfl⟩ (by norm_num))
theorem R99049 : Reach 99049 := rs (se 2 (by rfl) ⟨37143, by rfl⟩) (B 74287 (by norm_num) ⟨37143, by rfl⟩ (by norm_num))
theorem R99053 : Reach 99053 := rs (se 3 (by rfl) ⟨18572, by rfl⟩) (B 37145 (by norm_num) ⟨18572, by rfl⟩ (by norm_num))
theorem R99057 : Reach 99057 := rs (se 2 (by rfl) ⟨37146, by rfl⟩) (B 74293 (by norm_num) ⟨37146, by rfl⟩ (by norm_num))
theorem R361205 : Reach 361205 := rs (se 5 (by rfl) ⟨16931, by rfl⟩) (B 33863 (by norm_num) ⟨16931, by rfl⟩ (by norm_num))
theorem R99061 : Reach 99061 := rs (se 5 (by rfl) ⟨4643, by rfl⟩) (B 9287 (by norm_num) ⟨4643, by rfl⟩ (by norm_num))
theorem R99065 : Reach 99065 := rs (se 2 (by rfl) ⟨37149, by rfl⟩) (B 74299 (by norm_num) ⟨37149, by rfl⟩ (by norm_num))
theorem R164605 : Reach 164605 := rs (se 3 (by rfl) ⟨30863, by rfl⟩) (B 61727 (by norm_num) ⟨30863, by rfl⟩ (by norm_num))
theorem R99069 : Reach 99069 := rs (se 3 (by rfl) ⟨18575, by rfl⟩) (B 37151 (by norm_num) ⟨18575, by rfl⟩ (by norm_num))
theorem R99073 : Reach 99073 := rs (se 2 (by rfl) ⟨37152, by rfl⟩) (B 74305 (by norm_num) ⟨37152, by rfl⟩ (by norm_num))
theorem R99077 : Reach 99077 := rs (se 4 (by rfl) ⟨9288, by rfl⟩) (B 18577 (by norm_num) ⟨9288, by rfl⟩ (by norm_num))
theorem R99081 : Reach 99081 := rs (se 2 (by rfl) ⟨37155, by rfl⟩) (B 74311 (by norm_num) ⟨37155, by rfl⟩ (by norm_num))
theorem R99085 : Reach 99085 := rs (se 3 (by rfl) ⟨18578, by rfl⟩) (B 37157 (by norm_num) ⟨18578, by rfl⟩ (by norm_num))
theorem R99089 : Reach 99089 := rs (se 2 (by rfl) ⟨37158, by rfl⟩) (B 74317 (by norm_num) ⟨37158, by rfl⟩ (by norm_num))
theorem R819989 : Reach 819989 := rs (se 6 (by rfl) ⟨19218, by rfl⟩) (B 38437 (by norm_num) ⟨19218, by rfl⟩ (by norm_num))
theorem R131861 : Reach 131861 := rs (se 6 (by rfl) ⟨3090, by rfl⟩) (B 6181 (by norm_num) ⟨3090, by rfl⟩ (by norm_num))
theorem R99093 : Reach 99093 := rs (se 6 (by rfl) ⟨2322, by rfl⟩) (B 4645 (by norm_num) ⟨2322, by rfl⟩ (by norm_num))
theorem R99097 : Reach 99097 := rs (se 2 (by rfl) ⟨37161, by rfl⟩) (B 74323 (by norm_num) ⟨37161, by rfl⟩ (by norm_num))
theorem R99101 : Reach 99101 := rs (se 3 (by rfl) ⟨18581, by rfl⟩) (B 37163 (by norm_num) ⟨18581, by rfl⟩ (by norm_num))
theorem R99105 : Reach 99105 := rs (se 2 (by rfl) ⟨37164, by rfl⟩) (B 74329 (by norm_num) ⟨37164, by rfl⟩ (by norm_num))
theorem R99109 : Reach 99109 := rs (se 4 (by rfl) ⟨9291, by rfl⟩) (B 18583 (by norm_num) ⟨9291, by rfl⟩ (by norm_num))
theorem R99113 : Reach 99113 := rs (se 2 (by rfl) ⟨37167, by rfl⟩) (B 74335 (by norm_num) ⟨37167, by rfl⟩ (by norm_num))
theorem R99117 : Reach 99117 := rs (se 3 (by rfl) ⟨18584, by rfl⟩) (B 37169 (by norm_num) ⟨18584, by rfl⟩ (by norm_num))
theorem R99121 : Reach 99121 := rs (se 2 (by rfl) ⟨37170, by rfl⟩) (B 74341 (by norm_num) ⟨37170, by rfl⟩ (by norm_num))
theorem R99125 : Reach 99125 := rs (se 5 (by rfl) ⟨4646, by rfl⟩) (B 9293 (by norm_num) ⟨4646, by rfl⟩ (by norm_num))
theorem R99129 : Reach 99129 := rs (se 2 (by rfl) ⟨37173, by rfl⟩) (B 74347 (by norm_num) ⟨37173, by rfl⟩ (by norm_num))
theorem R164693 : Reach 164693 := rs (se 9 (by rfl) ⟨482, by rfl⟩) (B 965 (by norm_num) ⟨482, by rfl⟩ (by norm_num))
theorem R623477 : Reach 623477 := rs (se 5 (by rfl) ⟨29225, by rfl⟩) (B 58451 (by norm_num) ⟨29225, by rfl⟩ (by norm_num))
theorem R164821 : Reach 164821 := rs (se 7 (by rfl) ⟨1931, by rfl⟩) (B 3863 (by norm_num) ⟨1931, by rfl⟩ (by norm_num))
theorem R99289 : Reach 99289 := rs (se 2 (by rfl) ⟨37233, by rfl⟩) (B 74467 (by norm_num) ⟨37233, by rfl⟩ (by norm_num))
theorem R361493 : Reach 361493 := rs (se 6 (by rfl) ⟨8472, by rfl⟩) (B 16945 (by norm_num) ⟨8472, by rfl⟩ (by norm_num))
theorem R164909 : Reach 164909 := rs (se 3 (by rfl) ⟨30920, by rfl⟩) (B 61841 (by norm_num) ⟨30920, by rfl⟩ (by norm_num))
theorem R328805 : Reach 328805 := rs (se 4 (by rfl) ⟨30825, by rfl⟩) (B 61651 (by norm_num) ⟨30825, by rfl⟩ (by norm_num))
theorem R165037 : Reach 165037 := rs (se 3 (by rfl) ⟨30944, by rfl⟩) (B 61889 (by norm_num) ⟨30944, by rfl⟩ (by norm_num))
theorem R165125 : Reach 165125 := rs (se 4 (by rfl) ⟨15480, by rfl⟩) (B 30961 (by norm_num) ⟨15480, by rfl⟩ (by norm_num))
theorem R296309 : Reach 296309 := rs (se 5 (by rfl) ⟨13889, by rfl⟩) (B 27779 (by norm_num) ⟨13889, by rfl⟩ (by norm_num))
theorem R165253 : Reach 165253 := rs (se 4 (by rfl) ⟨15492, by rfl⟩) (B 30985 (by norm_num) ⟨15492, by rfl⟩ (by norm_num))
theorem R492965 : Reach 492965 := rs (se 4 (by rfl) ⟨46215, by rfl⟩) (B 92431 (by norm_num) ⟨46215, by rfl⟩ (by norm_num))
theorem R165341 : Reach 165341 := rs (se 3 (by rfl) ⟨31001, by rfl⟩) (B 62003 (by norm_num) ⟨31001, by rfl⟩ (by norm_num))
theorem R329237 : Reach 329237 := rs (se 6 (by rfl) ⟨7716, by rfl⟩) (B 15433 (by norm_num) ⟨7716, by rfl⟩ (by norm_num))
theorem R165469 : Reach 165469 := rs (se 3 (by rfl) ⟨31025, by rfl⟩) (B 62051 (by norm_num) ⟨31025, by rfl⟩ (by norm_num))
theorem R394885 : Reach 394885 := rs (se 4 (by rfl) ⟨37020, by rfl⟩) (B 74041 (by norm_num) ⟨37020, by rfl⟩ (by norm_num))
theorem R165557 : Reach 165557 := rs (se 5 (by rfl) ⟨7760, by rfl⟩) (B 15521 (by norm_num) ⟨7760, by rfl⟩ (by norm_num))
theorem R394949 : Reach 394949 := rs (se 4 (by rfl) ⟨37026, by rfl⟩) (B 74053 (by norm_num) ⟨37026, by rfl⟩ (by norm_num))
theorem R165685 : Reach 165685 := rs (se 5 (by rfl) ⟨7766, by rfl⟩) (B 15533 (by norm_num) ⟨7766, by rfl⟩ (by norm_num))
theorem R165773 : Reach 165773 := rs (se 3 (by rfl) ⟨31082, by rfl⟩) (B 62165 (by norm_num) ⟨31082, by rfl⟩ (by norm_num))
theorem R329669 : Reach 329669 := rs (se 4 (by rfl) ⟨30906, by rfl⟩) (B 61813 (by norm_num) ⟨30906, by rfl⟩ (by norm_num))
theorem R100325 : Reach 100325 := rs (se 4 (by rfl) ⟨9405, by rfl⟩) (B 18811 (by norm_num) ⟨9405, by rfl⟩ (by norm_num))
theorem R165901 : Reach 165901 := rs (se 3 (by rfl) ⟨31106, by rfl⟩) (B 62213 (by norm_num) ⟨31106, by rfl⟩ (by norm_num))
theorem R165989 : Reach 165989 := rs (se 4 (by rfl) ⟨15561, by rfl⟩) (B 31123 (by norm_num) ⟨15561, by rfl⟩ (by norm_num))
theorem R362677 : Reach 362677 := rs (se 5 (by rfl) ⟨17000, by rfl⟩) (B 34001 (by norm_num) ⟨17000, by rfl⟩ (by norm_num))
theorem R166117 : Reach 166117 := rs (se 4 (by rfl) ⟨15573, by rfl⟩) (B 31147 (by norm_num) ⟨15573, by rfl⟩ (by norm_num))
theorem R166141 : Reach 166141 := rs (se 3 (by rfl) ⟨31151, by rfl⟩) (B 62303 (by norm_num) ⟨31151, by rfl⟩ (by norm_num))
theorem R166205 : Reach 166205 := rs (se 3 (by rfl) ⟨31163, by rfl⟩) (B 62327 (by norm_num) ⟨31163, by rfl⟩ (by norm_num))
theorem R330101 : Reach 330101 := rs (se 5 (by rfl) ⟨15473, by rfl⟩) (B 30947 (by norm_num) ⟨15473, by rfl⟩ (by norm_num))
theorem R166333 : Reach 166333 := rs (se 3 (by rfl) ⟨31187, by rfl⟩) (B 62375 (by norm_num) ⟨31187, by rfl⟩ (by norm_num))
theorem R362981 : Reach 362981 := rs (se 4 (by rfl) ⟨34029, by rfl⟩) (B 68059 (by norm_num) ⟨34029, by rfl⟩ (by norm_num))
theorem R166421 : Reach 166421 := rs (se 6 (by rfl) ⟨3900, by rfl⟩) (B 7801 (by norm_num) ⟨3900, by rfl⟩ (by norm_num))
theorem R166549 : Reach 166549 := rs (se 6 (by rfl) ⟨3903, by rfl⟩) (B 7807 (by norm_num) ⟨3903, by rfl⟩ (by norm_num))
theorem R494261 : Reach 494261 := rs (se 5 (by rfl) ⟨23168, by rfl⟩) (B 46337 (by norm_num) ⟨23168, by rfl⟩ (by norm_num))
theorem R199349 : Reach 199349 := rs (se 5 (by rfl) ⟨9344, by rfl⟩) (B 18689 (by norm_num) ⟨9344, by rfl⟩ (by norm_num))
theorem R232141 : Reach 232141 := rs (se 3 (by rfl) ⟨43526, by rfl⟩) (B 87053 (by norm_num) ⟨43526, by rfl⟩ (by norm_num))
theorem R166637 : Reach 166637 := rs (se 3 (by rfl) ⟨31244, by rfl⟩) (B 62489 (by norm_num) ⟨31244, by rfl⟩ (by norm_num))
theorem R133877 : Reach 133877 := rs (se 5 (by rfl) ⟨6275, by rfl⟩) (B 12551 (by norm_num) ⟨6275, by rfl⟩ (by norm_num))
theorem R330533 : Reach 330533 := rs (se 4 (by rfl) ⟨30987, by rfl⟩) (B 61975 (by norm_num) ⟨30987, by rfl⟩ (by norm_num))
theorem R166765 : Reach 166765 := rs (se 3 (by rfl) ⟨31268, by rfl⟩) (B 62537 (by norm_num) ⟨31268, by rfl⟩ (by norm_num))
theorem R166853 : Reach 166853 := rs (se 4 (by rfl) ⟨15642, by rfl⟩) (B 31285 (by norm_num) ⟨15642, by rfl⟩ (by norm_num))
theorem R98297 : Reach 98297 := rs (se 2 (by rfl) ⟨36861, by rfl⟩) (B 73723 (by norm_num) ⟨36861, by rfl⟩ (by norm_num))
theorem R461861 : Reach 461861 := rs (se 4 (by rfl) ⟨43299, by rfl⟩) (B 86599 (by norm_num) ⟨43299, by rfl⟩ (by norm_num))
theorem R166949 : Reach 166949 := rs (se 4 (by rfl) ⟨15651, by rfl⟩) (B 31303 (by norm_num) ⟨15651, by rfl⟩ (by norm_num))
theorem R166981 : Reach 166981 := rs (se 4 (by rfl) ⟨15654, by rfl⟩) (B 31309 (by norm_num) ⟨15654, by rfl⟩ (by norm_num))
theorem R1346645 : Reach 1346645 := rs (se 8 (by rfl) ⟨7890, by rfl⟩) (B 15781 (by norm_num) ⟨7890, by rfl⟩ (by norm_num))
theorem R167069 : Reach 167069 := rs (se 3 (by rfl) ⟨31325, by rfl⟩) (B 62651 (by norm_num) ⟨31325, by rfl⟩ (by norm_num))
theorem R330965 : Reach 330965 := rs (se 7 (by rfl) ⟨3878, by rfl⟩) (B 7757 (by norm_num) ⟨3878, by rfl⟩ (by norm_num))
theorem R101593 : Reach 101593 := rs (se 2 (by rfl) ⟨38097, by rfl⟩) (B 76195 (by norm_num) ⟨38097, by rfl⟩ (by norm_num))
theorem R199957 : Reach 199957 := rs (se 6 (by rfl) ⟨4686, by rfl⟩) (B 9373 (by norm_num) ⟨4686, by rfl⟩ (by norm_num))
theorem R167197 : Reach 167197 := rs (se 3 (by rfl) ⟨31349, by rfl⟩) (B 62699 (by norm_num) ⟨31349, by rfl⟩ (by norm_num))
theorem R232757 : Reach 232757 := rs (se 5 (by rfl) ⟨10910, by rfl⟩) (B 21821 (by norm_num) ⟨10910, by rfl⟩ (by norm_num))
theorem R232813 : Reach 232813 := rs (se 3 (by rfl) ⟨43652, by rfl⟩) (B 87305 (by norm_num) ⟨43652, by rfl⟩ (by norm_num))
theorem R167285 : Reach 167285 := rs (se 5 (by rfl) ⟨7841, by rfl⟩) (B 15683 (by norm_num) ⟨7841, by rfl⟩ (by norm_num))
theorem R101773 : Reach 101773 := rs (se 3 (by rfl) ⟨19082, by rfl⟩) (B 38165 (by norm_num) ⟨19082, by rfl⟩ (by norm_num))
theorem R331397 : Reach 331397 := rs (se 4 (by rfl) ⟨31068, by rfl⟩) (B 62137 (by norm_num) ⟨31068, by rfl⟩ (by norm_num))
theorem R102217 : Reach 102217 := rs (se 2 (by rfl) ⟨38331, by rfl⟩) (B 76663 (by norm_num) ⟨38331, by rfl⟩ (by norm_num))
theorem R102341 : Reach 102341 := rs (se 4 (by rfl) ⟨9594, by rfl⟩) (B 19189 (by norm_num) ⟨9594, by rfl⟩ (by norm_num))
theorem R495557 : Reach 495557 := rs (se 4 (by rfl) ⟨46458, by rfl⟩) (B 92917 (by norm_num) ⟨46458, by rfl⟩ (by norm_num))
theorem R167989 : Reach 167989 := rs (se 5 (by rfl) ⟨7874, by rfl⟩) (B 15749 (by norm_num) ⟨7874, by rfl⟩ (by norm_num))
theorem R331829 : Reach 331829 := rs (se 5 (by rfl) ⟨15554, by rfl⟩) (B 31109 (by norm_num) ⟨15554, by rfl⟩ (by norm_num))
theorem R102593 : Reach 102593 := rs (se 2 (by rfl) ⟨38472, by rfl⟩) (B 76945 (by norm_num) ⟨38472, by rfl⟩ (by norm_num))
theorem R135469 : Reach 135469 := rs (se 3 (by rfl) ⟨25400, by rfl⟩) (B 50801 (by norm_num) ⟨25400, by rfl⟩ (by norm_num))
theorem R233813 : Reach 233813 := rs (se 10 (by rfl) ⟨342, by rfl⟩) (B 685 (by norm_num) ⟨342, by rfl⟩ (by norm_num))
theorem R135589 : Reach 135589 := rs (se 4 (by rfl) ⟨12711, by rfl⟩) (B 25423 (by norm_num) ⟨12711, by rfl⟩ (by norm_num))
theorem R332261 : Reach 332261 := rs (se 4 (by rfl) ⟨31149, by rfl⟩) (B 62299 (by norm_num) ⟨31149, by rfl⟩ (by norm_num))
theorem R135685 : Reach 135685 := rs (se 4 (by rfl) ⟨12720, by rfl⟩) (B 25441 (by norm_num) ⟨12720, by rfl⟩ (by norm_num))
theorem R365093 : Reach 365093 := rs (se 4 (by rfl) ⟨34227, by rfl⟩) (B 68455 (by norm_num) ⟨34227, by rfl⟩ (by norm_num))
theorem R103037 : Reach 103037 := rs (se 3 (by rfl) ⟨19319, by rfl⟩) (B 38639 (by norm_num) ⟨19319, by rfl⟩ (by norm_num))
theorem R365381 : Reach 365381 := rs (se 4 (by rfl) ⟨34254, by rfl⟩) (B 68509 (by norm_num) ⟨34254, by rfl⟩ (by norm_num))
theorem R103285 : Reach 103285 := rs (se 5 (by rfl) ⟨4841, by rfl⟩) (B 9683 (by norm_num) ⟨4841, by rfl⟩ (by norm_num))
theorem R463765 : Reach 463765 := rs (se 6 (by rfl) ⟨10869, by rfl⟩) (B 21739 (by norm_num) ⟨10869, by rfl⟩ (by norm_num))
theorem R332693 : Reach 332693 := rs (se 6 (by rfl) ⟨7797, by rfl⟩) (B 15595 (by norm_num) ⟨7797, by rfl⟩ (by norm_num))
theorem R463781 : Reach 463781 := rs (se 4 (by rfl) ⟨43479, by rfl⟩) (B 86959 (by norm_num) ⟨43479, by rfl⟩ (by norm_num))
theorem R136181 : Reach 136181 := rs (se 5 (by rfl) ⟨6383, by rfl⟩) (B 12767 (by norm_num) ⟨6383, by rfl⟩ (by norm_num))
theorem R496853 : Reach 496853 := rs (se 7 (by rfl) ⟨5822, by rfl⟩) (B 11645 (by norm_num) ⟨5822, by rfl⟩ (by norm_num))
theorem R103729 : Reach 103729 := rs (se 2 (by rfl) ⟨38898, by rfl⟩) (B 77797 (by norm_num) ⟨38898, by rfl⟩ (by norm_num))
theorem R333125 : Reach 333125 := rs (se 4 (by rfl) ⟨31230, by rfl⟩) (B 62461 (by norm_num) ⟨31230, by rfl⟩ (by norm_num))
theorem R333157 : Reach 333157 := rs (se 4 (by rfl) ⟨31233, by rfl⟩) (B 62467 (by norm_num) ⟨31233, by rfl⟩ (by norm_num))
theorem R103789 : Reach 103789 := rs (se 3 (by rfl) ⟨19460, by rfl⟩) (B 38921 (by norm_num) ⟨19460, by rfl⟩ (by norm_num))
theorem R267733 : Reach 267733 := rs (se 7 (by rfl) ⟨3137, by rfl⟩) (B 6275 (by norm_num) ⟨3137, by rfl⟩ (by norm_num))
theorem R267797 : Reach 267797 := rs (se 6 (by rfl) ⟨6276, by rfl⟩) (B 12553 (by norm_num) ⟨6276, by rfl⟩ (by norm_num))
theorem R136733 : Reach 136733 := rs (se 3 (by rfl) ⟨25637, by rfl⟩) (B 51275 (by norm_num) ⟨25637, by rfl⟩ (by norm_num))
theorem R529973 : Reach 529973 := rs (se 5 (by rfl) ⟨24842, by rfl⟩) (B 49685 (by norm_num) ⟨24842, by rfl⟩ (by norm_num))
theorem R104105 : Reach 104105 := rs (se 2 (by rfl) ⟨39039, by rfl⟩) (B 78079 (by norm_num) ⟨39039, by rfl⟩ (by norm_num))
theorem R333557 : Reach 333557 := rs (se 5 (by rfl) ⟨15635, by rfl⟩) (B 31271 (by norm_num) ⟨15635, by rfl⟩ (by norm_num))
theorem R366565 : Reach 366565 := rs (se 4 (by rfl) ⟨34365, by rfl⟩) (B 68731 (by norm_num) ⟨34365, by rfl⟩ (by norm_num))
theorem R104549 : Reach 104549 := rs (se 4 (by rfl) ⟨9801, by rfl⟩) (B 19603 (by norm_num) ⟨9801, by rfl⟩ (by norm_num))
theorem R104609 : Reach 104609 := rs (se 2 (by rfl) ⟨39228, by rfl⟩) (B 78457 (by norm_num) ⟨39228, by rfl⟩ (by norm_num))
theorem R333989 : Reach 333989 := rs (se 4 (by rfl) ⟨31311, by rfl⟩) (B 62623 (by norm_num) ⟨31311, by rfl⟩ (by norm_num))
theorem R563381 : Reach 563381 := rs (se 5 (by rfl) ⟨26408, by rfl⟩) (B 52817 (by norm_num) ⟨26408, by rfl⟩ (by norm_num))
theorem R137485 : Reach 137485 := rs (se 3 (by rfl) ⟨25778, by rfl⟩) (B 51557 (by norm_num) ⟨25778, by rfl⟩ (by norm_num))
theorem R891157 : Reach 891157 := rs (se 6 (by rfl) ⟨20886, by rfl⟩) (B 41773 (by norm_num) ⟨20886, by rfl⟩ (by norm_num))
theorem R366869 : Reach 366869 := rs (se 6 (by rfl) ⟨8598, by rfl⟩) (B 17197 (by norm_num) ⟨8598, by rfl⟩ (by norm_num))
theorem R104737 : Reach 104737 := rs (se 2 (by rfl) ⟨39276, by rfl⟩) (B 78553 (by norm_num) ⟨39276, by rfl⟩ (by norm_num))
theorem R498149 : Reach 498149 := rs (se 4 (by rfl) ⟨46701, by rfl⟩) (B 93403 (by norm_num) ⟨46701, by rfl⟩ (by norm_num))
theorem R727541 : Reach 727541 := rs (se 5 (by rfl) ⟨34103, by rfl⟩) (B 68207 (by norm_num) ⟨34103, by rfl⟩ (by norm_num))
theorem R334421 : Reach 334421 := rs (se 8 (by rfl) ⟨1959, by rfl⟩) (B 3919 (by norm_num) ⟨1959, by rfl⟩ (by norm_num))
theorem R203357 : Reach 203357 := rs (se 3 (by rfl) ⟨38129, by rfl⟩) (B 76259 (by norm_num) ⟨38129, by rfl⟩ (by norm_num))
theorem R236189 : Reach 236189 := rs (se 3 (by rfl) ⟨44285, by rfl⟩) (B 88571 (by norm_num) ⟨44285, by rfl⟩ (by norm_num))
theorem R3185365 : Reach 3185365 := rs (se 7 (by rfl) ⟨37328, by rfl⟩) (B 74657 (by norm_num) ⟨37328, by rfl⟩ (by norm_num))
theorem R105181 : Reach 105181 := rs (se 3 (by rfl) ⟨19721, by rfl⟩) (B 39443 (by norm_num) ⟨19721, by rfl⟩ (by norm_num))
theorem R170837 : Reach 170837 := rs (se 9 (by rfl) ⟨500, by rfl⟩) (B 1001 (by norm_num) ⟨500, by rfl⟩ (by norm_num))
theorem R105301 : Reach 105301 := rs (se 9 (by rfl) ⟨308, by rfl⟩) (B 617 (by norm_num) ⟨308, by rfl⟩ (by norm_num))
theorem R1579925 : Reach 1579925 := rs (se 6 (by rfl) ⟨37029, by rfl⟩) (B 74059 (by norm_num) ⟨37029, by rfl⟩ (by norm_num))
theorem R203725 : Reach 203725 := rs (se 3 (by rfl) ⟨38198, by rfl⟩) (B 76397 (by norm_num) ⟨38198, by rfl⟩ (by norm_num))
theorem R236573 : Reach 236573 := rs (se 3 (by rfl) ⟨44357, by rfl⟩) (B 88715 (by norm_num) ⟨44357, by rfl⟩ (by norm_num))
theorem R138277 : Reach 138277 := rs (se 4 (by rfl) ⟨12963, by rfl⟩) (B 25927 (by norm_num) ⟨12963, by rfl⟩ (by norm_num))
theorem R105509 : Reach 105509 := rs (se 4 (by rfl) ⟨9891, by rfl⟩) (B 19783 (by norm_num) ⟨9891, by rfl⟩ (by norm_num))
theorem R105553 : Reach 105553 := rs (se 2 (by rfl) ⟨39582, by rfl⟩) (B 79165 (by norm_num) ⟨39582, by rfl⟩ (by norm_num))
theorem R105557 : Reach 105557 := rs (se 8 (by rfl) ⟨618, by rfl⟩) (B 1237 (by norm_num) ⟨618, by rfl⟩ (by norm_num))
theorem R269525 : Reach 269525 := rs (se 7 (by rfl) ⟨3158, by rfl⟩) (B 6317 (by norm_num) ⟨3158, by rfl⟩ (by norm_num))
theorem R236773 : Reach 236773 := rs (se 4 (by rfl) ⟨22197, by rfl⟩) (B 44395 (by norm_num) ⟨22197, by rfl⟩ (by norm_num))
theorem R466165 : Reach 466165 := rs (se 5 (by rfl) ⟨21851, by rfl⟩) (B 43703 (by norm_num) ⟨21851, by rfl⟩ (by norm_num))
theorem R138613 : Reach 138613 := rs (se 5 (by rfl) ⟨6497, by rfl⟩) (B 12995 (by norm_num) ⟨6497, by rfl⟩ (by norm_num))
theorem R138829 : Reach 138829 := rs (se 3 (by rfl) ⟨26030, by rfl⟩) (B 52061 (by norm_num) ⟨26030, by rfl⟩ (by norm_num))
theorem R499445 : Reach 499445 := rs (se 5 (by rfl) ⟨23411, by rfl⟩) (B 46823 (by norm_num) ⟨23411, by rfl⟩ (by norm_num))
theorem R139205 : Reach 139205 := rs (se 4 (by rfl) ⟨13050, by rfl⟩) (B 26101 (by norm_num) ⟨13050, by rfl⟩ (by norm_num))
theorem R368981 : Reach 368981 := rs (se 10 (by rfl) ⟨540, by rfl⟩) (B 1081 (by norm_num) ⟨540, by rfl⟩ (by norm_num))
theorem R205229 : Reach 205229 := rs (se 3 (by rfl) ⟨38480, by rfl⟩) (B 76961 (by norm_num) ⟨38480, by rfl⟩ (by norm_num))
theorem R172477 : Reach 172477 := rs (se 3 (by rfl) ⟨32339, by rfl⟩) (B 64679 (by norm_num) ⟨32339, by rfl⟩ (by norm_num))
theorem R107041 : Reach 107041 := rs (se 2 (by rfl) ⟨40140, by rfl⟩) (B 80281 (by norm_num) ⟨40140, by rfl⟩ (by norm_num))
theorem R205373 : Reach 205373 := rs (se 3 (by rfl) ⟨38507, by rfl⟩) (B 77015 (by norm_num) ⟨38507, by rfl⟩ (by norm_num))
theorem R107077 : Reach 107077 := rs (se 4 (by rfl) ⟨10038, by rfl⟩) (B 20077 (by norm_num) ⟨10038, by rfl⟩ (by norm_num))
theorem R172621 : Reach 172621 := rs (se 3 (by rfl) ⟨32366, by rfl⟩) (B 64733 (by norm_num) ⟨32366, by rfl⟩ (by norm_num))
theorem R1679957 : Reach 1679957 := rs (se 8 (by rfl) ⟨9843, by rfl⟩) (B 19687 (by norm_num) ⟨9843, by rfl⟩ (by norm_num))
theorem R107113 : Reach 107113 := rs (se 2 (by rfl) ⟨40167, by rfl⟩) (B 80335 (by norm_num) ⟨40167, by rfl⟩ (by norm_num))
theorem R369269 : Reach 369269 := rs (se 5 (by rfl) ⟨17309, by rfl⟩) (B 34619 (by norm_num) ⟨17309, by rfl⟩ (by norm_num))
theorem R107149 : Reach 107149 := rs (se 3 (by rfl) ⟨20090, by rfl⟩) (B 40181 (by norm_num) ⟨20090, by rfl⟩ (by norm_num))
theorem R828053 : Reach 828053 := rs (se 6 (by rfl) ⟨19407, by rfl⟩) (B 38815 (by norm_num) ⟨19407, by rfl⟩ (by norm_num))
theorem R107185 : Reach 107185 := rs (se 2 (by rfl) ⟨40194, by rfl⟩) (B 80389 (by norm_num) ⟨40194, by rfl⟩ (by norm_num))
theorem R107221 : Reach 107221 := rs (se 7 (by rfl) ⟨1256, by rfl⟩) (B 2513 (by norm_num) ⟨1256, by rfl⟩ (by norm_num))
theorem R107257 : Reach 107257 := rs (se 2 (by rfl) ⟨40221, by rfl⟩) (B 80443 (by norm_num) ⟨40221, by rfl⟩ (by norm_num))
theorem R107293 : Reach 107293 := rs (se 3 (by rfl) ⟨20117, by rfl⟩) (B 40235 (by norm_num) ⟨20117, by rfl⟩ (by norm_num))
theorem R107329 : Reach 107329 := rs (se 2 (by rfl) ⟨40248, by rfl⟩) (B 80497 (by norm_num) ⟨40248, by rfl⟩ (by norm_num))
theorem R107365 : Reach 107365 := rs (se 4 (by rfl) ⟨10065, by rfl⟩) (B 20131 (by norm_num) ⟨10065, by rfl⟩ (by norm_num))
theorem R107401 : Reach 107401 := rs (se 2 (by rfl) ⟨40275, by rfl⟩) (B 80551 (by norm_num) ⟨40275, by rfl⟩ (by norm_num))
theorem R205733 : Reach 205733 := rs (se 4 (by rfl) ⟨19287, by rfl⟩) (B 38575 (by norm_num) ⟨19287, by rfl⟩ (by norm_num))
theorem R107437 : Reach 107437 := rs (se 3 (by rfl) ⟨20144, by rfl⟩) (B 40289 (by norm_num) ⟨20144, by rfl⟩ (by norm_num))
theorem R107473 : Reach 107473 := rs (se 2 (by rfl) ⟨40302, by rfl⟩) (B 80605 (by norm_num) ⟨40302, by rfl⟩ (by norm_num))
theorem R107509 : Reach 107509 := rs (se 5 (by rfl) ⟨5039, by rfl⟩) (B 10079 (by norm_num) ⟨5039, by rfl⟩ (by norm_num))
theorem R500741 : Reach 500741 := rs (se 4 (by rfl) ⟨46944, by rfl⟩) (B 93889 (by norm_num) ⟨46944, by rfl⟩ (by norm_num))
theorem R107545 : Reach 107545 := rs (se 2 (by rfl) ⟨40329, by rfl⟩) (B 80659 (by norm_num) ⟨40329, by rfl⟩ (by norm_num))
theorem R107581 : Reach 107581 := rs (se 3 (by rfl) ⟨20171, by rfl⟩) (B 40343 (by norm_num) ⟨20171, by rfl⟩ (by norm_num))
theorem R107617 : Reach 107617 := rs (se 2 (by rfl) ⟨40356, by rfl⟩) (B 80713 (by norm_num) ⟨40356, by rfl⟩ (by norm_num))
theorem R107653 : Reach 107653 := rs (se 4 (by rfl) ⟨10092, by rfl⟩) (B 20185 (by norm_num) ⟨10092, by rfl⟩ (by norm_num))
theorem R107689 : Reach 107689 := rs (se 2 (by rfl) ⟨40383, by rfl⟩) (B 80767 (by norm_num) ⟨40383, by rfl⟩ (by norm_num))
theorem R107725 : Reach 107725 := rs (se 3 (by rfl) ⟨20198, by rfl⟩) (B 40397 (by norm_num) ⟨20198, by rfl⟩ (by norm_num))
theorem R107761 : Reach 107761 := rs (se 2 (by rfl) ⟨40410, by rfl⟩) (B 80821 (by norm_num) ⟨40410, by rfl⟩ (by norm_num))
theorem R107797 : Reach 107797 := rs (se 6 (by rfl) ⟨2526, by rfl⟩) (B 5053 (by norm_num) ⟨2526, by rfl⟩ (by norm_num))
theorem R107833 : Reach 107833 := rs (se 2 (by rfl) ⟨40437, by rfl⟩) (B 80875 (by norm_num) ⟨40437, by rfl⟩ (by norm_num))
theorem R140629 : Reach 140629 := rs (se 12 (by rfl) ⟨51, by rfl⟩) (B 103 (by norm_num) ⟨51, by rfl⟩ (by norm_num))
theorem R107869 : Reach 107869 := rs (se 3 (by rfl) ⟨20225, by rfl⟩) (B 40451 (by norm_num) ⟨20225, by rfl⟩ (by norm_num))
theorem R107905 : Reach 107905 := rs (se 2 (by rfl) ⟨40464, by rfl⟩) (B 80929 (by norm_num) ⟨40464, by rfl⟩ (by norm_num))
theorem R271781 : Reach 271781 := rs (se 4 (by rfl) ⟨25479, by rfl⟩) (B 50959 (by norm_num) ⟨25479, by rfl⟩ (by norm_num))
theorem R107941 : Reach 107941 := rs (se 4 (by rfl) ⟨10119, by rfl⟩) (B 20239 (by norm_num) ⟨10119, by rfl⟩ (by norm_num))
theorem R107977 : Reach 107977 := rs (se 2 (by rfl) ⟨40491, by rfl⟩) (B 80983 (by norm_num) ⟨40491, by rfl⟩ (by norm_num))
theorem R2139605 : Reach 2139605 := rs (se 7 (by rfl) ⟨25073, by rfl⟩) (B 50147 (by norm_num) ⟨25073, by rfl⟩ (by norm_num))
theorem R108013 : Reach 108013 := rs (se 3 (by rfl) ⟨20252, by rfl⟩) (B 40505 (by norm_num) ⟨20252, by rfl⟩ (by norm_num))
theorem R173573 : Reach 173573 := rs (se 4 (by rfl) ⟨16272, by rfl⟩) (B 32545 (by norm_num) ⟨16272, by rfl⟩ (by norm_num))
theorem R108037 : Reach 108037 := rs (se 4 (by rfl) ⟨10128, by rfl⟩) (B 20257 (by norm_num) ⟨10128, by rfl⟩ (by norm_num))
theorem R108049 : Reach 108049 := rs (se 2 (by rfl) ⟨40518, by rfl⟩) (B 81037 (by norm_num) ⟨40518, by rfl⟩ (by norm_num))
theorem R108085 : Reach 108085 := rs (se 5 (by rfl) ⟨5066, by rfl⟩) (B 10133 (by norm_num) ⟨5066, by rfl⟩ (by norm_num))
theorem R173645 : Reach 173645 := rs (se 3 (by rfl) ⟨32558, by rfl⟩) (B 65117 (by norm_num) ⟨32558, by rfl⟩ (by norm_num))
theorem R108121 : Reach 108121 := rs (se 2 (by rfl) ⟨40545, by rfl⟩) (B 81091 (by norm_num) ⟨40545, by rfl⟩ (by norm_num))
theorem R108157 : Reach 108157 := rs (se 3 (by rfl) ⟨20279, by rfl⟩) (B 40559 (by norm_num) ⟨20279, by rfl⟩ (by norm_num))
theorem R108193 : Reach 108193 := rs (se 2 (by rfl) ⟨40572, by rfl⟩) (B 81145 (by norm_num) ⟨40572, by rfl⟩ (by norm_num))
theorem R108229 : Reach 108229 := rs (se 4 (by rfl) ⟨10146, by rfl⟩) (B 20293 (by norm_num) ⟨10146, by rfl⟩ (by norm_num))
theorem R108265 : Reach 108265 := rs (se 2 (by rfl) ⟨40599, by rfl⟩) (B 81199 (by norm_num) ⟨40599, by rfl⟩ (by norm_num))
theorem R108301 : Reach 108301 := rs (se 3 (by rfl) ⟨20306, by rfl⟩) (B 40613 (by norm_num) ⟨20306, by rfl⟩ (by norm_num))
theorem R370453 : Reach 370453 := rs (se 6 (by rfl) ⟨8682, by rfl⟩) (B 17365 (by norm_num) ⟨8682, by rfl⟩ (by norm_num))
theorem R1124117 : Reach 1124117 := rs (se 6 (by rfl) ⟨26346, by rfl⟩) (B 52693 (by norm_num) ⟨26346, by rfl⟩ (by norm_num))
theorem R206621 : Reach 206621 := rs (se 3 (by rfl) ⟨38741, by rfl⟩) (B 77483 (by norm_num) ⟨38741, by rfl⟩ (by norm_num))
theorem R108337 : Reach 108337 := rs (se 2 (by rfl) ⟨40626, by rfl⟩) (B 81253 (by norm_num) ⟨40626, by rfl⟩ (by norm_num))
theorem R108373 : Reach 108373 := rs (se 9 (by rfl) ⟨317, by rfl⟩) (B 635 (by norm_num) ⟨317, by rfl⟩ (by norm_num))
theorem R108409 : Reach 108409 := rs (se 2 (by rfl) ⟨40653, by rfl⟩) (B 81307 (by norm_num) ⟨40653, by rfl⟩ (by norm_num))
theorem R108445 : Reach 108445 := rs (se 3 (by rfl) ⟨20333, by rfl⟩) (B 40667 (by norm_num) ⟨20333, by rfl⟩ (by norm_num))
theorem R108481 : Reach 108481 := rs (se 2 (by rfl) ⟨40680, by rfl⟩) (B 81361 (by norm_num) ⟨40680, by rfl⟩ (by norm_num))
theorem R108517 : Reach 108517 := rs (se 4 (by rfl) ⟨10173, by rfl⟩) (B 20347 (by norm_num) ⟨10173, by rfl⟩ (by norm_num))
theorem R108553 : Reach 108553 := rs (se 2 (by rfl) ⟨40707, by rfl⟩) (B 81415 (by norm_num) ⟨40707, by rfl⟩ (by norm_num))
theorem R206869 : Reach 206869 := rs (se 6 (by rfl) ⟨4848, by rfl⟩) (B 9697 (by norm_num) ⟨4848, by rfl⟩ (by norm_num))
theorem R108589 : Reach 108589 := rs (se 3 (by rfl) ⟨20360, by rfl⟩) (B 40721 (by norm_num) ⟨20360, by rfl⟩ (by norm_num))
theorem R370757 : Reach 370757 := rs (se 4 (by rfl) ⟨34758, by rfl⟩) (B 69517 (by norm_num) ⟨34758, by rfl⟩ (by norm_num))
theorem R108625 : Reach 108625 := rs (se 2 (by rfl) ⟨40734, by rfl⟩) (B 81469 (by norm_num) ⟨40734, by rfl⟩ (by norm_num))
theorem R108661 : Reach 108661 := rs (se 5 (by rfl) ⟨5093, by rfl⟩) (B 10187 (by norm_num) ⟨5093, by rfl⟩ (by norm_num))
theorem R108697 : Reach 108697 := rs (se 2 (by rfl) ⟨40761, by rfl⟩) (B 81523 (by norm_num) ⟨40761, by rfl⟩ (by norm_num))
theorem R108733 : Reach 108733 := rs (se 3 (by rfl) ⟨20387, by rfl⟩) (B 40775 (by norm_num) ⟨20387, by rfl⟩ (by norm_num))
theorem R108769 : Reach 108769 := rs (se 2 (by rfl) ⟨40788, by rfl⟩) (B 81577 (by norm_num) ⟨40788, by rfl⟩ (by norm_num))
theorem R108805 : Reach 108805 := rs (se 4 (by rfl) ⟨10200, by rfl⟩) (B 20401 (by norm_num) ⟨10200, by rfl⟩ (by norm_num))
theorem R698645 : Reach 698645 := rs (se 6 (by rfl) ⟨16374, by rfl⟩) (B 32749 (by norm_num) ⟨16374, by rfl⟩ (by norm_num))
theorem R108841 : Reach 108841 := rs (se 2 (by rfl) ⟨40815, by rfl⟩) (B 81631 (by norm_num) ⟨40815, by rfl⟩ (by norm_num))
theorem R108877 : Reach 108877 := rs (se 3 (by rfl) ⟨20414, by rfl⟩) (B 40829 (by norm_num) ⟨20414, by rfl⟩ (by norm_num))
theorem R9382229 : Reach 9382229 := rs (se 10 (by rfl) ⟨13743, by rfl⟩) (B 27487 (by norm_num) ⟨13743, by rfl⟩ (by norm_num))
theorem R1419605 : Reach 1419605 := rs (se 10 (by rfl) ⟨2079, by rfl⟩) (B 4159 (by norm_num) ⟨2079, by rfl⟩ (by norm_num))
theorem R108913 : Reach 108913 := rs (se 2 (by rfl) ⟨40842, by rfl⟩) (B 81685 (by norm_num) ⟨40842, by rfl⟩ (by norm_num))
theorem R108949 : Reach 108949 := rs (se 6 (by rfl) ⟨2553, by rfl⟩) (B 5107 (by norm_num) ⟨2553, by rfl⟩ (by norm_num))
theorem R108973 : Reach 108973 := rs (se 3 (by rfl) ⟨20432, by rfl⟩) (B 40865 (by norm_num) ⟨20432, by rfl⟩ (by norm_num))
theorem R108985 : Reach 108985 := rs (se 2 (by rfl) ⟨40869, by rfl⟩) (B 81739 (by norm_num) ⟨40869, by rfl⟩ (by norm_num))
theorem R109009 : Reach 109009 := rs (se 2 (by rfl) ⟨40878, by rfl⟩) (B 81757 (by norm_num) ⟨40878, by rfl⟩ (by norm_num))
theorem R109021 : Reach 109021 := rs (se 3 (by rfl) ⟨20441, by rfl⟩) (B 40883 (by norm_num) ⟨20441, by rfl⟩ (by norm_num))
theorem R109057 : Reach 109057 := rs (se 2 (by rfl) ⟨40896, by rfl⟩) (B 81793 (by norm_num) ⟨40896, by rfl⟩ (by norm_num))
theorem R207373 : Reach 207373 := rs (se 3 (by rfl) ⟨38882, by rfl⟩) (B 77765 (by norm_num) ⟨38882, by rfl⟩ (by norm_num))
theorem R109093 : Reach 109093 := rs (se 4 (by rfl) ⟨10227, by rfl⟩) (B 20455 (by norm_num) ⟨10227, by rfl⟩ (by norm_num))
theorem R272965 : Reach 272965 := rs (se 4 (by rfl) ⟨25590, by rfl⟩) (B 51181 (by norm_num) ⟨25590, by rfl⟩ (by norm_num))
theorem R109129 : Reach 109129 := rs (se 2 (by rfl) ⟨40923, by rfl⟩) (B 81847 (by norm_num) ⟨40923, by rfl⟩ (by norm_num))
theorem R109165 : Reach 109165 := rs (se 3 (by rfl) ⟨20468, by rfl⟩) (B 40937 (by norm_num) ⟨20468, by rfl⟩ (by norm_num))
theorem R109201 : Reach 109201 := rs (se 2 (by rfl) ⟨40950, by rfl⟩) (B 81901 (by norm_num) ⟨40950, by rfl⟩ (by norm_num))
theorem R109237 : Reach 109237 := rs (se 5 (by rfl) ⟨5120, by rfl⟩) (B 10241 (by norm_num) ⟨5120, by rfl⟩ (by norm_num))
theorem R109273 : Reach 109273 := rs (se 2 (by rfl) ⟨40977, by rfl⟩) (B 81955 (by norm_num) ⟨40977, by rfl⟩ (by norm_num))
theorem R273125 : Reach 273125 := rs (se 4 (by rfl) ⟨25605, by rfl⟩) (B 51211 (by norm_num) ⟨25605, by rfl⟩ (by norm_num))
theorem R109309 : Reach 109309 := rs (se 3 (by rfl) ⟨20495, by rfl⟩) (B 40991 (by norm_num) ⟨20495, by rfl⟩ (by norm_num))
theorem R109345 : Reach 109345 := rs (se 2 (by rfl) ⟨41004, by rfl⟩) (B 82009 (by norm_num) ⟨41004, by rfl⟩ (by norm_num))
theorem R109381 : Reach 109381 := rs (se 4 (by rfl) ⟨10254, by rfl⟩) (B 20509 (by norm_num) ⟨10254, by rfl⟩ (by norm_num))
theorem R109417 : Reach 109417 := rs (se 2 (by rfl) ⟨41031, by rfl⟩) (B 82063 (by norm_num) ⟨41031, by rfl⟩ (by norm_num))
theorem R109453 : Reach 109453 := rs (se 3 (by rfl) ⟨20522, by rfl⟩) (B 41045 (by norm_num) ⟨20522, by rfl⟩ (by norm_num))
theorem R109489 : Reach 109489 := rs (se 2 (by rfl) ⟨41058, by rfl⟩) (B 82117 (by norm_num) ⟨41058, by rfl⟩ (by norm_num))
theorem R273365 : Reach 273365 := rs (se 7 (by rfl) ⟨3203, by rfl⟩) (B 6407 (by norm_num) ⟨3203, by rfl⟩ (by norm_num))
theorem R109525 : Reach 109525 := rs (se 7 (by rfl) ⟨1283, by rfl⟩) (B 2567 (by norm_num) ⟨1283, by rfl⟩ (by norm_num))
theorem R109561 : Reach 109561 := rs (se 2 (by rfl) ⟨41085, by rfl⟩) (B 82171 (by norm_num) ⟨41085, by rfl⟩ (by norm_num))
theorem R109597 : Reach 109597 := rs (se 3 (by rfl) ⟨20549, by rfl⟩) (B 41099 (by norm_num) ⟨20549, by rfl⟩ (by norm_num))
theorem R470069 : Reach 470069 := rs (se 5 (by rfl) ⟨22034, by rfl⟩) (B 44069 (by norm_num) ⟨22034, by rfl⟩ (by norm_num))
theorem R109633 : Reach 109633 := rs (se 2 (by rfl) ⟨41112, by rfl⟩) (B 82225 (by norm_num) ⟨41112, by rfl⟩ (by norm_num))
theorem R339029 : Reach 339029 := rs (se 8 (by rfl) ⟨1986, by rfl⟩) (B 3973 (by norm_num) ⟨1986, by rfl⟩ (by norm_num))
theorem R109669 : Reach 109669 := rs (se 4 (by rfl) ⟨10281, by rfl⟩) (B 20563 (by norm_num) ⟨10281, by rfl⟩ (by norm_num))
theorem R109705 : Reach 109705 := rs (se 2 (by rfl) ⟨41139, by rfl⟩) (B 82279 (by norm_num) ⟨41139, by rfl⟩ (by norm_num))
theorem R273557 : Reach 273557 := rs (se 6 (by rfl) ⟨6411, by rfl⟩) (B 12823 (by norm_num) ⟨6411, by rfl⟩ (by norm_num))
theorem R109741 : Reach 109741 := rs (se 3 (by rfl) ⟨20576, by rfl⟩) (B 41153 (by norm_num) ⟨20576, by rfl⟩ (by norm_num))
theorem R109777 : Reach 109777 := rs (se 2 (by rfl) ⟨41166, by rfl⟩) (B 82333 (by norm_num) ⟨41166, by rfl⟩ (by norm_num))
theorem R240853 : Reach 240853 := rs (se 7 (by rfl) ⟨2822, by rfl⟩) (B 5645 (by norm_num) ⟨2822, by rfl⟩ (by norm_num))
theorem R109813 : Reach 109813 := rs (se 5 (by rfl) ⟨5147, by rfl⟩) (B 10295 (by norm_num) ⟨5147, by rfl⟩ (by norm_num))
theorem R109849 : Reach 109849 := rs (se 2 (by rfl) ⟨41193, by rfl⟩) (B 82387 (by norm_num) ⟨41193, by rfl⟩ (by norm_num))
theorem R109885 : Reach 109885 := rs (se 3 (by rfl) ⟨20603, by rfl⟩) (B 41207 (by norm_num) ⟨20603, by rfl⟩ (by norm_num))
theorem R240965 : Reach 240965 := rs (se 4 (by rfl) ⟨22590, by rfl⟩) (B 45181 (by norm_num) ⟨22590, by rfl⟩ (by norm_num))
theorem R3026261 : Reach 3026261 := rs (se 11 (by rfl) ⟨2216, by rfl⟩) (B 4433 (by norm_num) ⟨2216, by rfl⟩ (by norm_num))
theorem R109921 : Reach 109921 := rs (se 2 (by rfl) ⟨41220, by rfl⟩) (B 82441 (by norm_num) ⟨41220, by rfl⟩ (by norm_num))
theorem R142709 : Reach 142709 := rs (se 5 (by rfl) ⟨6689, by rfl⟩) (B 13379 (by norm_num) ⟨6689, by rfl⟩ (by norm_num))
theorem R208261 : Reach 208261 := rs (se 4 (by rfl) ⟨19524, by rfl⟩) (B 39049 (by norm_num) ⟨19524, by rfl⟩ (by norm_num))
theorem R109957 : Reach 109957 := rs (se 4 (by rfl) ⟨10308, by rfl⟩) (B 20617 (by norm_num) ⟨10308, by rfl⟩ (by norm_num))
theorem R142733 : Reach 142733 := rs (se 3 (by rfl) ⟨26762, by rfl⟩) (B 53525 (by norm_num) ⟨26762, by rfl⟩ (by norm_num))
theorem R142757 : Reach 142757 := rs (se 4 (by rfl) ⟨13383, by rfl⟩) (B 26767 (by norm_num) ⟨13383, by rfl⟩ (by norm_num))
theorem R109993 : Reach 109993 := rs (se 2 (by rfl) ⟨41247, by rfl⟩) (B 82495 (by norm_num) ⟨41247, by rfl⟩ (by norm_num))
theorem R142781 : Reach 142781 := rs (se 3 (by rfl) ⟨26771, by rfl⟩) (B 53543 (by norm_num) ⟨26771, by rfl⟩ (by norm_num))
theorem R110029 : Reach 110029 := rs (se 3 (by rfl) ⟨20630, by rfl⟩) (B 41261 (by norm_num) ⟨20630, by rfl⟩ (by norm_num))
theorem R142805 : Reach 142805 := rs (se 7 (by rfl) ⟨1673, by rfl⟩) (B 3347 (by norm_num) ⟨1673, by rfl⟩ (by norm_num))
theorem R142829 : Reach 142829 := rs (se 3 (by rfl) ⟨26780, by rfl⟩) (B 53561 (by norm_num) ⟨26780, by rfl⟩ (by norm_num))
theorem R110065 : Reach 110065 := rs (se 2 (by rfl) ⟨41274, by rfl⟩) (B 82549 (by norm_num) ⟨41274, by rfl⟩ (by norm_num))
theorem R142853 : Reach 142853 := rs (se 4 (by rfl) ⟨13392, by rfl⟩) (B 26785 (by norm_num) ⟨13392, by rfl⟩ (by norm_num))
theorem R241157 : Reach 241157 := rs (se 4 (by rfl) ⟨22608, by rfl⟩) (B 45217 (by norm_num) ⟨22608, by rfl⟩ (by norm_num))
theorem R110101 : Reach 110101 := rs (se 6 (by rfl) ⟨2580, by rfl⟩) (B 5161 (by norm_num) ⟨2580, by rfl⟩ (by norm_num))
theorem R142877 : Reach 142877 := rs (se 3 (by rfl) ⟨26789, by rfl⟩) (B 53579 (by norm_num) ⟨26789, by rfl⟩ (by norm_num))
theorem R142901 : Reach 142901 := rs (se 5 (by rfl) ⟨6698, by rfl⟩) (B 13397 (by norm_num) ⟨6698, by rfl⟩ (by norm_num))
theorem R110137 : Reach 110137 := rs (se 2 (by rfl) ⟨41301, by rfl⟩) (B 82603 (by norm_num) ⟨41301, by rfl⟩ (by norm_num))
theorem R142925 : Reach 142925 := rs (se 3 (by rfl) ⟨26798, by rfl⟩) (B 53597 (by norm_num) ⟨26798, by rfl⟩ (by norm_num))
theorem R110173 : Reach 110173 := rs (se 3 (by rfl) ⟨20657, by rfl⟩) (B 41315 (by norm_num) ⟨20657, by rfl⟩ (by norm_num))
theorem R142949 : Reach 142949 := rs (se 4 (by rfl) ⟨13401, by rfl⟩) (B 26803 (by norm_num) ⟨13401, by rfl⟩ (by norm_num))
theorem R142973 : Reach 142973 := rs (se 3 (by rfl) ⟨26807, by rfl⟩) (B 53615 (by norm_num) ⟨26807, by rfl⟩ (by norm_num))
theorem R110209 : Reach 110209 := rs (se 2 (by rfl) ⟨41328, by rfl⟩) (B 82657 (by norm_num) ⟨41328, by rfl⟩ (by norm_num))
theorem R142997 : Reach 142997 := rs (se 6 (by rfl) ⟨3351, by rfl⟩) (B 6703 (by norm_num) ⟨3351, by rfl⟩ (by norm_num))
theorem R110245 : Reach 110245 := rs (se 4 (by rfl) ⟨10335, by rfl⟩) (B 20671 (by norm_num) ⟨10335, by rfl⟩ (by norm_num))
theorem R143021 : Reach 143021 := rs (se 3 (by rfl) ⟨26816, by rfl⟩) (B 53633 (by norm_num) ⟨26816, by rfl⟩ (by norm_num))
theorem R143045 : Reach 143045 := rs (se 4 (by rfl) ⟨13410, by rfl⟩) (B 26821 (by norm_num) ⟨13410, by rfl⟩ (by norm_num))
theorem R110281 : Reach 110281 := rs (se 2 (by rfl) ⟨41355, by rfl⟩) (B 82711 (by norm_num) ⟨41355, by rfl⟩ (by norm_num))
theorem R143069 : Reach 143069 := rs (se 3 (by rfl) ⟨26825, by rfl⟩) (B 53651 (by norm_num) ⟨26825, by rfl⟩ (by norm_num))
theorem R110317 : Reach 110317 := rs (se 3 (by rfl) ⟨20684, by rfl⟩) (B 41369 (by norm_num) ⟨20684, by rfl⟩ (by norm_num))
theorem R143093 : Reach 143093 := rs (se 5 (by rfl) ⟨6707, by rfl⟩) (B 13415 (by norm_num) ⟨6707, by rfl⟩ (by norm_num))
theorem R110341 : Reach 110341 := rs (se 4 (by rfl) ⟨10344, by rfl⟩) (B 20689 (by norm_num) ⟨10344, by rfl⟩ (by norm_num))
theorem R143117 : Reach 143117 := rs (se 3 (by rfl) ⟨26834, by rfl⟩) (B 53669 (by norm_num) ⟨26834, by rfl⟩ (by norm_num))
theorem R110353 : Reach 110353 := rs (se 2 (by rfl) ⟨41382, by rfl⟩) (B 82765 (by norm_num) ⟨41382, by rfl⟩ (by norm_num))
theorem R143141 : Reach 143141 := rs (se 4 (by rfl) ⟨13419, by rfl⟩) (B 26839 (by norm_num) ⟨13419, by rfl⟩ (by norm_num))
theorem R110389 : Reach 110389 := rs (se 5 (by rfl) ⟨5174, by rfl⟩) (B 10349 (by norm_num) ⟨5174, by rfl⟩ (by norm_num))
theorem R143165 : Reach 143165 := rs (se 3 (by rfl) ⟨26843, by rfl⟩) (B 53687 (by norm_num) ⟨26843, by rfl⟩ (by norm_num))
theorem R143189 : Reach 143189 := rs (se 9 (by rfl) ⟨419, by rfl⟩) (B 839 (by norm_num) ⟨419, by rfl⟩ (by norm_num))
theorem R110425 : Reach 110425 := rs (se 2 (by rfl) ⟨41409, by rfl⟩) (B 82819 (by norm_num) ⟨41409, by rfl⟩ (by norm_num))
theorem R241501 : Reach 241501 := rs (se 3 (by rfl) ⟨45281, by rfl⟩) (B 90563 (by norm_num) ⟨45281, by rfl⟩ (by norm_num))
theorem R143213 : Reach 143213 := rs (se 3 (by rfl) ⟨26852, by rfl⟩) (B 53705 (by norm_num) ⟨26852, by rfl⟩ (by norm_num))
theorem R307061 : Reach 307061 := rs (se 5 (by rfl) ⟨14393, by rfl⟩) (B 28787 (by norm_num) ⟨14393, by rfl⟩ (by norm_num))
theorem R208757 : Reach 208757 := rs (se 5 (by rfl) ⟨9785, by rfl⟩) (B 19571 (by norm_num) ⟨9785, by rfl⟩ (by norm_num))
theorem R110461 : Reach 110461 := rs (se 3 (by rfl) ⟨20711, by rfl⟩) (B 41423 (by norm_num) ⟨20711, by rfl⟩ (by norm_num))
theorem R143237 : Reach 143237 := rs (se 4 (by rfl) ⟨13428, by rfl⟩) (B 26857 (by norm_num) ⟨13428, by rfl⟩ (by norm_num))
theorem R143261 : Reach 143261 := rs (se 3 (by rfl) ⟨26861, by rfl⟩) (B 53723 (by norm_num) ⟨26861, by rfl⟩ (by norm_num))
theorem R110497 : Reach 110497 := rs (se 2 (by rfl) ⟨41436, by rfl⟩) (B 82873 (by norm_num) ⟨41436, by rfl⟩ (by norm_num))
theorem R143285 : Reach 143285 := rs (se 5 (by rfl) ⟨6716, by rfl⟩) (B 13433 (by norm_num) ⟨6716, by rfl⟩ (by norm_num))
theorem R929717 : Reach 929717 := rs (se 5 (by rfl) ⟨43580, by rfl⟩) (B 87161 (by norm_num) ⟨43580, by rfl⟩ (by norm_num))
theorem R110533 : Reach 110533 := rs (se 4 (by rfl) ⟨10362, by rfl⟩) (B 20725 (by norm_num) ⟨10362, by rfl⟩ (by norm_num))
theorem R241613 : Reach 241613 := rs (se 3 (by rfl) ⟨45302, by rfl⟩) (B 90605 (by norm_num) ⟨45302, by rfl⟩ (by norm_num))
theorem R143309 : Reach 143309 := rs (se 3 (by rfl) ⟨26870, by rfl⟩) (B 53741 (by norm_num) ⟨26870, by rfl⟩ (by norm_num))
theorem R143333 : Reach 143333 := rs (se 4 (by rfl) ⟨13437, by rfl⟩) (B 26875 (by norm_num) ⟨13437, by rfl⟩ (by norm_num))
theorem R110569 : Reach 110569 := rs (se 2 (by rfl) ⟨41463, by rfl⟩) (B 82927 (by norm_num) ⟨41463, by rfl⟩ (by norm_num))
theorem R143357 : Reach 143357 := rs (se 3 (by rfl) ⟨26879, by rfl⟩) (B 53759 (by norm_num) ⟨26879, by rfl⟩ (by norm_num))
theorem R110605 : Reach 110605 := rs (se 3 (by rfl) ⟨20738, by rfl⟩) (B 41477 (by norm_num) ⟨20738, by rfl⟩ (by norm_num))
theorem R143381 : Reach 143381 := rs (se 6 (by rfl) ⟨3360, by rfl⟩) (B 6721 (by norm_num) ⟨3360, by rfl⟩ (by norm_num))
theorem R143405 : Reach 143405 := rs (se 3 (by rfl) ⟨26888, by rfl⟩) (B 53777 (by norm_num) ⟨26888, by rfl⟩ (by norm_num))
theorem R110641 : Reach 110641 := rs (se 2 (by rfl) ⟨41490, by rfl⟩) (B 82981 (by norm_num) ⟨41490, by rfl⟩ (by norm_num))
theorem R143429 : Reach 143429 := rs (se 4 (by rfl) ⟨13446, by rfl⟩) (B 26893 (by norm_num) ⟨13446, by rfl⟩ (by norm_num))
theorem R110677 : Reach 110677 := rs (se 8 (by rfl) ⟨648, by rfl⟩) (B 1297 (by norm_num) ⟨648, by rfl⟩ (by norm_num))
theorem R143453 : Reach 143453 := rs (se 3 (by rfl) ⟨26897, by rfl⟩) (B 53795 (by norm_num) ⟨26897, by rfl⟩ (by norm_num))
theorem R143477 : Reach 143477 := rs (se 5 (by rfl) ⟨6725, by rfl⟩) (B 13451 (by norm_num) ⟨6725, by rfl⟩ (by norm_num))
theorem R274549 : Reach 274549 := rs (se 5 (by rfl) ⟨12869, by rfl⟩) (B 25739 (by norm_num) ⟨12869, by rfl⟩ (by norm_num))
theorem R110713 : Reach 110713 := rs (se 2 (by rfl) ⟨41517, by rfl⟩) (B 83035 (by norm_num) ⟨41517, by rfl⟩ (by norm_num))
theorem R372869 : Reach 372869 := rs (se 4 (by rfl) ⟨34956, by rfl⟩) (B 69913 (by norm_num) ⟨34956, by rfl⟩ (by norm_num))
theorem R241805 : Reach 241805 := rs (se 3 (by rfl) ⟨45338, by rfl⟩) (B 90677 (by norm_num) ⟨45338, by rfl⟩ (by norm_num))
theorem R143501 : Reach 143501 := rs (se 3 (by rfl) ⟨26906, by rfl⟩) (B 53813 (by norm_num) ⟨26906, by rfl⟩ (by norm_num))
theorem R110749 : Reach 110749 := rs (se 3 (by rfl) ⟨20765, by rfl⟩) (B 41531 (by norm_num) ⟨20765, by rfl⟩ (by norm_num))
theorem R143525 : Reach 143525 := rs (se 4 (by rfl) ⟨13455, by rfl⟩) (B 26911 (by norm_num) ⟨13455, by rfl⟩ (by norm_num))
theorem R143549 : Reach 143549 := rs (se 3 (by rfl) ⟨26915, by rfl⟩) (B 53831 (by norm_num) ⟨26915, by rfl⟩ (by norm_num))
theorem R110785 : Reach 110785 := rs (se 2 (by rfl) ⟨41544, by rfl⟩) (B 83089 (by norm_num) ⟨41544, by rfl⟩ (by norm_num))
theorem R143573 : Reach 143573 := rs (se 7 (by rfl) ⟨1682, by rfl⟩) (B 3365 (by norm_num) ⟨1682, by rfl⟩ (by norm_num))
theorem R110821 : Reach 110821 := rs (se 4 (by rfl) ⟨10389, by rfl⟩) (B 20779 (by norm_num) ⟨10389, by rfl⟩ (by norm_num))
theorem R143597 : Reach 143597 := rs (se 3 (by rfl) ⟨26924, by rfl⟩) (B 53849 (by norm_num) ⟨26924, by rfl⟩ (by norm_num))
theorem R143621 : Reach 143621 := rs (se 4 (by rfl) ⟨13464, by rfl⟩) (B 26929 (by norm_num) ⟨13464, by rfl⟩ (by norm_num))
theorem R110857 : Reach 110857 := rs (se 2 (by rfl) ⟨41571, by rfl⟩) (B 83143 (by norm_num) ⟨41571, by rfl⟩ (by norm_num))
theorem R143645 : Reach 143645 := rs (se 3 (by rfl) ⟨26933, by rfl⟩) (B 53867 (by norm_num) ⟨26933, by rfl⟩ (by norm_num))
theorem R176413 : Reach 176413 := rs (se 3 (by rfl) ⟨33077, by rfl⟩) (B 66155 (by norm_num) ⟨33077, by rfl⟩ (by norm_num))
theorem R110893 : Reach 110893 := rs (se 3 (by rfl) ⟨20792, by rfl⟩) (B 41585 (by norm_num) ⟨20792, by rfl⟩ (by norm_num))
theorem R143669 : Reach 143669 := rs (se 5 (by rfl) ⟨6734, by rfl⟩) (B 13469 (by norm_num) ⟨6734, by rfl⟩ (by norm_num))
theorem R143693 : Reach 143693 := rs (se 3 (by rfl) ⟨26942, by rfl⟩) (B 53885 (by norm_num) ⟨26942, by rfl⟩ (by norm_num))
theorem R110929 : Reach 110929 := rs (se 2 (by rfl) ⟨41598, by rfl⟩) (B 83197 (by norm_num) ⟨41598, by rfl⟩ (by norm_num))
theorem R143717 : Reach 143717 := rs (se 4 (by rfl) ⟨13473, by rfl⟩) (B 26947 (by norm_num) ⟨13473, by rfl⟩ (by norm_num))
theorem R110965 : Reach 110965 := rs (se 5 (by rfl) ⟨5201, by rfl⟩) (B 10403 (by norm_num) ⟨5201, by rfl⟩ (by norm_num))
theorem R143741 : Reach 143741 := rs (se 3 (by rfl) ⟨26951, by rfl⟩) (B 53903 (by norm_num) ⟨26951, by rfl⟩ (by norm_num))
theorem R143765 : Reach 143765 := rs (se 6 (by rfl) ⟨3369, by rfl⟩) (B 6739 (by norm_num) ⟨3369, by rfl⟩ (by norm_num))
theorem R111001 : Reach 111001 := rs (se 2 (by rfl) ⟨41625, by rfl⟩) (B 83251 (by norm_num) ⟨41625, by rfl⟩ (by norm_num))
theorem R373157 : Reach 373157 := rs (se 4 (by rfl) ⟨34983, by rfl⟩) (B 69967 (by norm_num) ⟨34983, by rfl⟩ (by norm_num))
theorem R143789 : Reach 143789 := rs (se 3 (by rfl) ⟨26960, by rfl⟩) (B 53921 (by norm_num) ⟨26960, by rfl⟩ (by norm_num))
theorem R111037 : Reach 111037 := rs (se 3 (by rfl) ⟨20819, by rfl⟩) (B 41639 (by norm_num) ⟨20819, by rfl⟩ (by norm_num))
theorem R143813 : Reach 143813 := rs (se 4 (by rfl) ⟨13482, by rfl⟩) (B 26965 (by norm_num) ⟨13482, by rfl⟩ (by norm_num))
theorem R143837 : Reach 143837 := rs (se 3 (by rfl) ⟨26969, by rfl⟩) (B 53939 (by norm_num) ⟨26969, by rfl⟩ (by norm_num))
theorem R111073 : Reach 111073 := rs (se 2 (by rfl) ⟨41652, by rfl⟩) (B 83305 (by norm_num) ⟨41652, by rfl⟩ (by norm_num))
theorem R242149 : Reach 242149 := rs (se 4 (by rfl) ⟨22701, by rfl⟩) (B 45403 (by norm_num) ⟨22701, by rfl⟩ (by norm_num))
theorem R143861 : Reach 143861 := rs (se 5 (by rfl) ⟨6743, by rfl⟩) (B 13487 (by norm_num) ⟨6743, by rfl⟩ (by norm_num))
theorem R111109 : Reach 111109 := rs (se 4 (by rfl) ⟨10416, by rfl⟩) (B 20833 (by norm_num) ⟨10416, by rfl⟩ (by norm_num))
theorem R143885 : Reach 143885 := rs (se 3 (by rfl) ⟨26978, by rfl⟩) (B 53957 (by norm_num) ⟨26978, by rfl⟩ (by norm_num))
theorem R1683989 : Reach 1683989 := rs (se 6 (by rfl) ⟨39468, by rfl⟩) (B 78937 (by norm_num) ⟨39468, by rfl⟩ (by norm_num))
theorem R143909 : Reach 143909 := rs (se 4 (by rfl) ⟨13491, by rfl⟩) (B 26983 (by norm_num) ⟨13491, by rfl⟩ (by norm_num))
theorem R111145 : Reach 111145 := rs (se 2 (by rfl) ⟨41679, by rfl⟩) (B 83359 (by norm_num) ⟨41679, by rfl⟩ (by norm_num))
theorem R143933 : Reach 143933 := rs (se 3 (by rfl) ⟨26987, by rfl⟩) (B 53975 (by norm_num) ⟨26987, by rfl⟩ (by norm_num))
theorem R111181 : Reach 111181 := rs (se 3 (by rfl) ⟨20846, by rfl⟩) (B 41693 (by norm_num) ⟨20846, by rfl⟩ (by norm_num))
theorem R242261 : Reach 242261 := rs (se 8 (by rfl) ⟨1419, by rfl⟩) (B 2839 (by norm_num) ⟨1419, by rfl⟩ (by norm_num))
theorem R143957 : Reach 143957 := rs (se 8 (by rfl) ⟨843, by rfl⟩) (B 1687 (by norm_num) ⟨843, by rfl⟩ (by norm_num))
theorem R143981 : Reach 143981 := rs (se 3 (by rfl) ⟨26996, by rfl⟩) (B 53993 (by norm_num) ⟨26996, by rfl⟩ (by norm_num))
theorem R111217 : Reach 111217 := rs (se 2 (by rfl) ⟨41706, by rfl⟩) (B 83413 (by norm_num) ⟨41706, by rfl⟩ (by norm_num))
theorem R144005 : Reach 144005 := rs (se 4 (by rfl) ⟨13500, by rfl⟩) (B 27001 (by norm_num) ⟨13500, by rfl⟩ (by norm_num))
theorem R111253 : Reach 111253 := rs (se 6 (by rfl) ⟨2607, by rfl⟩) (B 5215 (by norm_num) ⟨2607, by rfl⟩ (by norm_num))
theorem R144029 : Reach 144029 := rs (se 3 (by rfl) ⟨27005, by rfl⟩) (B 54011 (by norm_num) ⟨27005, by rfl⟩ (by norm_num))
theorem R144053 : Reach 144053 := rs (se 5 (by rfl) ⟨6752, by rfl⟩) (B 13505 (by norm_num) ⟨6752, by rfl⟩ (by norm_num))
theorem R111289 : Reach 111289 := rs (se 2 (by rfl) ⟨41733, by rfl⟩) (B 83467 (by norm_num) ⟨41733, by rfl⟩ (by norm_num))
theorem R144077 : Reach 144077 := rs (se 3 (by rfl) ⟨27014, by rfl⟩) (B 54029 (by norm_num) ⟨27014, by rfl⟩ (by norm_num))
theorem R111325 : Reach 111325 := rs (se 3 (by rfl) ⟨20873, by rfl⟩) (B 41747 (by norm_num) ⟨20873, by rfl⟩ (by norm_num))
theorem R144101 : Reach 144101 := rs (se 4 (by rfl) ⟨13509, by rfl⟩) (B 27019 (by norm_num) ⟨13509, by rfl⟩ (by norm_num))
theorem R209645 : Reach 209645 := rs (se 3 (by rfl) ⟨39308, by rfl⟩) (B 78617 (by norm_num) ⟨39308, by rfl⟩ (by norm_num))
theorem R307957 : Reach 307957 := rs (se 5 (by rfl) ⟨14435, by rfl⟩) (B 28871 (by norm_num) ⟨14435, by rfl⟩ (by norm_num))
theorem R144125 : Reach 144125 := rs (se 3 (by rfl) ⟨27023, by rfl⟩) (B 54047 (by norm_num) ⟨27023, by rfl⟩ (by norm_num))
theorem R111361 : Reach 111361 := rs (se 2 (by rfl) ⟨41760, by rfl⟩) (B 83521 (by norm_num) ⟨41760, by rfl⟩ (by norm_num))
theorem R242453 : Reach 242453 := rs (se 6 (by rfl) ⟨5682, by rfl⟩) (B 11365 (by norm_num) ⟨5682, by rfl⟩ (by norm_num))
theorem R144149 : Reach 144149 := rs (se 6 (by rfl) ⟨3378, by rfl⟩) (B 6757 (by norm_num) ⟨3378, by rfl⟩ (by norm_num))
theorem R176917 : Reach 176917 := rs (se 6 (by rfl) ⟨4146, by rfl⟩) (B 8293 (by norm_num) ⟨4146, by rfl⟩ (by norm_num))
theorem R111397 : Reach 111397 := rs (se 4 (by rfl) ⟨10443, by rfl⟩) (B 20887 (by norm_num) ⟨10443, by rfl⟩ (by norm_num))
theorem R144173 : Reach 144173 := rs (se 3 (by rfl) ⟨27032, by rfl⟩) (B 54065 (by norm_num) ⟨27032, by rfl⟩ (by norm_num))
theorem R144197 : Reach 144197 := rs (se 4 (by rfl) ⟨13518, by rfl⟩) (B 27037 (by norm_num) ⟨13518, by rfl⟩ (by norm_num))
theorem R111433 : Reach 111433 := rs (se 2 (by rfl) ⟨41787, by rfl⟩) (B 83575 (by norm_num) ⟨41787, by rfl⟩ (by norm_num))
theorem R144221 : Reach 144221 := rs (se 3 (by rfl) ⟨27041, by rfl⟩) (B 54083 (by norm_num) ⟨27041, by rfl⟩ (by norm_num))
theorem R209765 : Reach 209765 := rs (se 4 (by rfl) ⟨19665, by rfl⟩) (B 39331 (by norm_num) ⟨19665, by rfl⟩ (by norm_num))
theorem R111469 : Reach 111469 := rs (se 3 (by rfl) ⟨20900, by rfl⟩) (B 41801 (by norm_num) ⟨20900, by rfl⟩ (by norm_num))
theorem R144245 : Reach 144245 := rs (se 5 (by rfl) ⟨6761, by rfl⟩) (B 13523 (by norm_num) ⟨6761, by rfl⟩ (by norm_num))
theorem R144269 : Reach 144269 := rs (se 3 (by rfl) ⟨27050, by rfl⟩) (B 54101 (by norm_num) ⟨27050, by rfl⟩ (by norm_num))
theorem R111505 : Reach 111505 := rs (se 2 (by rfl) ⟨41814, by rfl⟩) (B 83629 (by norm_num) ⟨41814, by rfl⟩ (by norm_num))
theorem R144293 : Reach 144293 := rs (se 4 (by rfl) ⟨13527, by rfl⟩) (B 27055 (by norm_num) ⟨13527, by rfl⟩ (by norm_num))
theorem R144317 : Reach 144317 := rs (se 3 (by rfl) ⟨27059, by rfl⟩) (B 54119 (by norm_num) ⟨27059, by rfl⟩ (by norm_num))
theorem R144341 : Reach 144341 := rs (se 7 (by rfl) ⟨1691, by rfl⟩) (B 3383 (by norm_num) ⟨1691, by rfl⟩ (by norm_num))
theorem R144365 : Reach 144365 := rs (se 3 (by rfl) ⟨27068, by rfl⟩) (B 54137 (by norm_num) ⟨27068, by rfl⟩ (by norm_num))
theorem R144389 : Reach 144389 := rs (se 4 (by rfl) ⟨13536, by rfl⟩) (B 27073 (by norm_num) ⟨13536, by rfl⟩ (by norm_num))
theorem R472085 : Reach 472085 := rs (se 6 (by rfl) ⟨11064, by rfl⟩) (B 22129 (by norm_num) ⟨11064, by rfl⟩ (by norm_num))
theorem R144413 : Reach 144413 := rs (se 3 (by rfl) ⟨27077, by rfl⟩) (B 54155 (by norm_num) ⟨27077, by rfl⟩ (by norm_num))
theorem R144437 : Reach 144437 := rs (se 5 (by rfl) ⟨6770, by rfl⟩) (B 13541 (by norm_num) ⟨6770, by rfl⟩ (by norm_num))
theorem R144461 : Reach 144461 := rs (se 3 (by rfl) ⟨27086, by rfl⟩) (B 54173 (by norm_num) ⟨27086, by rfl⟩ (by norm_num))
theorem R144485 : Reach 144485 := rs (se 4 (by rfl) ⟨13545, by rfl⟩) (B 27091 (by norm_num) ⟨13545, by rfl⟩ (by norm_num))
theorem R242797 : Reach 242797 := rs (se 3 (by rfl) ⟨45524, by rfl⟩) (B 91049 (by norm_num) ⟨45524, by rfl⟩ (by norm_num))
theorem R144509 : Reach 144509 := rs (se 3 (by rfl) ⟨27095, by rfl⟩) (B 54191 (by norm_num) ⟨27095, by rfl⟩ (by norm_num))
theorem R308357 : Reach 308357 := rs (se 4 (by rfl) ⟨28908, by rfl⟩) (B 57817 (by norm_num) ⟨28908, by rfl⟩ (by norm_num))
theorem R373909 : Reach 373909 := rs (se 6 (by rfl) ⟨8763, by rfl⟩) (B 17527 (by norm_num) ⟨8763, by rfl⟩ (by norm_num))
theorem R144533 : Reach 144533 := rs (se 6 (by rfl) ⟨3387, by rfl⟩) (B 6775 (by norm_num) ⟨3387, by rfl⟩ (by norm_num))
theorem R144557 : Reach 144557 := rs (se 3 (by rfl) ⟨27104, by rfl⟩) (B 54209 (by norm_num) ⟨27104, by rfl⟩ (by norm_num))
theorem R144581 : Reach 144581 := rs (se 4 (by rfl) ⟨13554, by rfl⟩) (B 27109 (by norm_num) ⟨13554, by rfl⟩ (by norm_num))
theorem R275653 : Reach 275653 := rs (se 4 (by rfl) ⟨25842, by rfl⟩) (B 51685 (by norm_num) ⟨25842, by rfl⟩ (by norm_num))
theorem R242909 : Reach 242909 := rs (se 3 (by rfl) ⟨45545, by rfl⟩) (B 91091 (by norm_num) ⟨45545, by rfl⟩ (by norm_num))
theorem R144605 : Reach 144605 := rs (se 3 (by rfl) ⟨27113, by rfl⟩) (B 54227 (by norm_num) ⟨27113, by rfl⟩ (by norm_num))
theorem R144629 : Reach 144629 := rs (se 5 (by rfl) ⟨6779, by rfl⟩) (B 13559 (by norm_num) ⟨6779, by rfl⟩ (by norm_num))
theorem R144653 : Reach 144653 := rs (se 3 (by rfl) ⟨27122, by rfl⟩) (B 54245 (by norm_num) ⟨27122, by rfl⟩ (by norm_num))
theorem R144677 : Reach 144677 := rs (se 4 (by rfl) ⟨13563, by rfl⟩) (B 27127 (by norm_num) ⟨13563, by rfl⟩ (by norm_num))
theorem R144701 : Reach 144701 := rs (se 3 (by rfl) ⟨27131, by rfl⟩) (B 54263 (by norm_num) ⟨27131, by rfl⟩ (by norm_num))
theorem R144725 : Reach 144725 := rs (se 13 (by rfl) ⟨26, by rfl⟩) (B 53 (by norm_num) ⟨26, by rfl⟩ (by norm_num))
theorem R144749 : Reach 144749 := rs (se 3 (by rfl) ⟨27140, by rfl⟩) (B 54281 (by norm_num) ⟨27140, by rfl⟩ (by norm_num))
theorem R144773 : Reach 144773 := rs (se 4 (by rfl) ⟨13572, by rfl⟩) (B 27145 (by norm_num) ⟨13572, by rfl⟩ (by norm_num))
theorem R144797 : Reach 144797 := rs (se 3 (by rfl) ⟨27149, by rfl⟩) (B 54299 (by norm_num) ⟨27149, by rfl⟩ (by norm_num))
theorem R243101 : Reach 243101 := rs (se 3 (by rfl) ⟨45581, by rfl⟩) (B 91163 (by norm_num) ⟨45581, by rfl⟩ (by norm_num))
theorem R144821 : Reach 144821 := rs (se 5 (by rfl) ⟨6788, by rfl⟩) (B 13577 (by norm_num) ⟨6788, by rfl⟩ (by norm_num))
theorem R144845 : Reach 144845 := rs (se 3 (by rfl) ⟨27158, by rfl⟩) (B 54317 (by norm_num) ⟨27158, by rfl⟩ (by norm_num))
theorem R210397 : Reach 210397 := rs (se 3 (by rfl) ⟨39449, by rfl⟩) (B 78899 (by norm_num) ⟨39449, by rfl⟩ (by norm_num))
theorem R144869 : Reach 144869 := rs (se 4 (by rfl) ⟨13581, by rfl⟩) (B 27163 (by norm_num) ⟨13581, by rfl⟩ (by norm_num))
theorem R144893 : Reach 144893 := rs (se 3 (by rfl) ⟨27167, by rfl⟩) (B 54335 (by norm_num) ⟨27167, by rfl⟩ (by norm_num))
theorem R144917 : Reach 144917 := rs (se 6 (by rfl) ⟨3396, by rfl⟩) (B 6793 (by norm_num) ⟨3396, by rfl⟩ (by norm_num))
theorem R144941 : Reach 144941 := rs (se 3 (by rfl) ⟨27176, by rfl⟩) (B 54353 (by norm_num) ⟨27176, by rfl⟩ (by norm_num))
theorem R144965 : Reach 144965 := rs (se 4 (by rfl) ⟨13590, by rfl⟩) (B 27181 (by norm_num) ⟨13590, by rfl⟩ (by norm_num))
theorem R374341 : Reach 374341 := rs (se 4 (by rfl) ⟨35094, by rfl⟩) (B 70189 (by norm_num) ⟨35094, by rfl⟩ (by norm_num))
theorem R144989 : Reach 144989 := rs (se 3 (by rfl) ⟨27185, by rfl⟩) (B 54371 (by norm_num) ⟨27185, by rfl⟩ (by norm_num))
theorem R112229 : Reach 112229 := rs (se 4 (by rfl) ⟨10521, by rfl⟩) (B 21043 (by norm_num) ⟨10521, by rfl⟩ (by norm_num))
theorem R145013 : Reach 145013 := rs (se 5 (by rfl) ⟨6797, by rfl⟩) (B 13595 (by norm_num) ⟨6797, by rfl⟩ (by norm_num))
theorem R177797 : Reach 177797 := rs (se 4 (by rfl) ⟨16668, by rfl⟩) (B 33337 (by norm_num) ⟨16668, by rfl⟩ (by norm_num))
theorem R145037 : Reach 145037 := rs (se 3 (by rfl) ⟨27194, by rfl⟩) (B 54389 (by norm_num) ⟨27194, by rfl⟩ (by norm_num))
theorem R145061 : Reach 145061 := rs (se 4 (by rfl) ⟨13599, by rfl⟩) (B 27199 (by norm_num) ⟨13599, by rfl⟩ (by norm_num))
theorem R145085 : Reach 145085 := rs (se 3 (by rfl) ⟨27203, by rfl⟩) (B 54407 (by norm_num) ⟨27203, by rfl⟩ (by norm_num))
theorem R145109 : Reach 145109 := rs (se 7 (by rfl) ⟨1700, by rfl⟩) (B 3401 (by norm_num) ⟨1700, by rfl⟩ (by norm_num))
theorem R145133 : Reach 145133 := rs (se 3 (by rfl) ⟨27212, by rfl⟩) (B 54425 (by norm_num) ⟨27212, by rfl⟩ (by norm_num))
theorem R243445 : Reach 243445 := rs (se 5 (by rfl) ⟨11411, by rfl⟩) (B 22823 (by norm_num) ⟨11411, by rfl⟩ (by norm_num))
theorem R145157 : Reach 145157 := rs (se 4 (by rfl) ⟨13608, by rfl⟩) (B 27217 (by norm_num) ⟨13608, by rfl⟩ (by norm_num))
theorem R472837 : Reach 472837 := rs (se 4 (by rfl) ⟨44328, by rfl⟩) (B 88657 (by norm_num) ⟨44328, by rfl⟩ (by norm_num))
theorem R145181 : Reach 145181 := rs (se 3 (by rfl) ⟨27221, by rfl⟩) (B 54443 (by norm_num) ⟨27221, by rfl⟩ (by norm_num))
theorem R145205 : Reach 145205 := rs (se 5 (by rfl) ⟨6806, by rfl⟩) (B 13613 (by norm_num) ⟨6806, by rfl⟩ (by norm_num))
theorem R145229 : Reach 145229 := rs (se 3 (by rfl) ⟨27230, by rfl⟩) (B 54461 (by norm_num) ⟨27230, by rfl⟩ (by norm_num))
theorem R178013 : Reach 178013 := rs (se 3 (by rfl) ⟨33377, by rfl⟩) (B 66755 (by norm_num) ⟨33377, by rfl⟩ (by norm_num))
theorem R243557 : Reach 243557 := rs (se 4 (by rfl) ⟨22833, by rfl⟩) (B 45667 (by norm_num) ⟨22833, by rfl⟩ (by norm_num))
theorem R145253 : Reach 145253 := rs (se 4 (by rfl) ⟨13617, by rfl⟩) (B 27235 (by norm_num) ⟨13617, by rfl⟩ (by norm_num))
theorem R145261 : Reach 145261 := rs (se 3 (by rfl) ⟨27236, by rfl⟩) (B 54473 (by norm_num) ⟨27236, by rfl⟩ (by norm_num))
theorem R374645 : Reach 374645 := rs (se 5 (by rfl) ⟨17561, by rfl⟩) (B 35123 (by norm_num) ⟨17561, by rfl⟩ (by norm_num))
theorem R145277 : Reach 145277 := rs (se 3 (by rfl) ⟨27239, by rfl⟩) (B 54479 (by norm_num) ⟨27239, by rfl⟩ (by norm_num))
theorem R145301 : Reach 145301 := rs (se 6 (by rfl) ⟨3405, by rfl⟩) (B 6811 (by norm_num) ⟨3405, by rfl⟩ (by norm_num))
theorem R145325 : Reach 145325 := rs (se 3 (by rfl) ⟨27248, by rfl⟩) (B 54497 (by norm_num) ⟨27248, by rfl⟩ (by norm_num))
theorem R145349 : Reach 145349 := rs (se 4 (by rfl) ⟨13626, by rfl⟩) (B 27253 (by norm_num) ⟨13626, by rfl⟩ (by norm_num))
theorem R145373 : Reach 145373 := rs (se 3 (by rfl) ⟨27257, by rfl⟩) (B 54515 (by norm_num) ⟨27257, by rfl⟩ (by norm_num))
theorem R178157 : Reach 178157 := rs (se 3 (by rfl) ⟨33404, by rfl⟩) (B 66809 (by norm_num) ⟨33404, by rfl⟩ (by norm_num))
theorem R145397 : Reach 145397 := rs (se 5 (by rfl) ⟨6815, by rfl⟩) (B 13631 (by norm_num) ⟨6815, by rfl⟩ (by norm_num))
theorem R145421 : Reach 145421 := rs (se 3 (by rfl) ⟨27266, by rfl⟩) (B 54533 (by norm_num) ⟨27266, by rfl⟩ (by norm_num))
theorem R145445 : Reach 145445 := rs (se 4 (by rfl) ⟨13635, by rfl⟩) (B 27271 (by norm_num) ⟨13635, by rfl⟩ (by norm_num))
theorem R243749 : Reach 243749 := rs (se 4 (by rfl) ⟨22851, by rfl⟩) (B 45703 (by norm_num) ⟨22851, by rfl⟩ (by norm_num))
theorem R112685 : Reach 112685 := rs (se 3 (by rfl) ⟨21128, by rfl⟩) (B 42257 (by norm_num) ⟨21128, by rfl⟩ (by norm_num))
theorem R145469 : Reach 145469 := rs (se 3 (by rfl) ⟨27275, by rfl⟩) (B 54551 (by norm_num) ⟨27275, by rfl⟩ (by norm_num))
theorem R178237 : Reach 178237 := rs (se 3 (by rfl) ⟨33419, by rfl⟩) (B 66839 (by norm_num) ⟨33419, by rfl⟩ (by norm_num))
theorem R735317 : Reach 735317 := rs (se 8 (by rfl) ⟨4308, by rfl⟩) (B 8617 (by norm_num) ⟨4308, by rfl⟩ (by norm_num))
theorem R145493 : Reach 145493 := rs (se 8 (by rfl) ⟨852, by rfl⟩) (B 1705 (by norm_num) ⟨852, by rfl⟩ (by norm_num))
theorem R145517 : Reach 145517 := rs (se 3 (by rfl) ⟨27284, by rfl⟩) (B 54569 (by norm_num) ⟨27284, by rfl⟩ (by norm_num))
theorem R145541 : Reach 145541 := rs (se 4 (by rfl) ⟨13644, by rfl⟩) (B 27289 (by norm_num) ⟨13644, by rfl⟩ (by norm_num))
theorem R145565 : Reach 145565 := rs (se 3 (by rfl) ⟨27293, by rfl⟩) (B 54587 (by norm_num) ⟨27293, by rfl⟩ (by norm_num))
theorem R145589 : Reach 145589 := rs (se 5 (by rfl) ⟨6824, by rfl⟩) (B 13649 (by norm_num) ⟨6824, by rfl⟩ (by norm_num))
theorem R145613 : Reach 145613 := rs (se 3 (by rfl) ⟨27302, by rfl⟩) (B 54605 (by norm_num) ⟨27302, by rfl⟩ (by norm_num))
theorem R145637 : Reach 145637 := rs (se 4 (by rfl) ⟨13653, by rfl⟩) (B 27307 (by norm_num) ⟨13653, by rfl⟩ (by norm_num))
theorem R145661 : Reach 145661 := rs (se 3 (by rfl) ⟨27311, by rfl⟩) (B 54623 (by norm_num) ⟨27311, by rfl⟩ (by norm_num))
theorem R145685 : Reach 145685 := rs (se 6 (by rfl) ⟨3414, by rfl⟩) (B 6829 (by norm_num) ⟨3414, by rfl⟩ (by norm_num))
theorem R145709 : Reach 145709 := rs (se 3 (by rfl) ⟨27320, by rfl⟩) (B 54641 (by norm_num) ⟨27320, by rfl⟩ (by norm_num))
theorem R407861 : Reach 407861 := rs (se 5 (by rfl) ⟨19118, by rfl⟩) (B 38237 (by norm_num) ⟨19118, by rfl⟩ (by norm_num))
theorem R211261 : Reach 211261 := rs (se 3 (by rfl) ⟨39611, by rfl⟩) (B 79223 (by norm_num) ⟨39611, by rfl⟩ (by norm_num))
theorem R145733 : Reach 145733 := rs (se 4 (by rfl) ⟨13662, by rfl⟩) (B 27325 (by norm_num) ⟨13662, by rfl⟩ (by norm_num))
theorem R211285 : Reach 211285 := rs (se 10 (by rfl) ⟨309, by rfl⟩) (B 619 (by norm_num) ⟨309, by rfl⟩ (by norm_num))
theorem R145757 : Reach 145757 := rs (se 3 (by rfl) ⟨27329, by rfl⟩) (B 54659 (by norm_num) ⟨27329, by rfl⟩ (by norm_num))
theorem R145781 : Reach 145781 := rs (se 5 (by rfl) ⟨6833, by rfl⟩) (B 13667 (by norm_num) ⟨6833, by rfl⟩ (by norm_num))
theorem R244093 : Reach 244093 := rs (se 3 (by rfl) ⟨45767, by rfl⟩) (B 91535 (by norm_num) ⟨45767, by rfl⟩ (by norm_num))
theorem R145805 : Reach 145805 := rs (se 3 (by rfl) ⟨27338, by rfl⟩) (B 54677 (by norm_num) ⟨27338, by rfl⟩ (by norm_num))
theorem R145829 : Reach 145829 := rs (se 4 (by rfl) ⟨13671, by rfl⟩) (B 27343 (by norm_num) ⟨13671, by rfl⟩ (by norm_num))
theorem R145853 : Reach 145853 := rs (se 3 (by rfl) ⟨27347, by rfl⟩) (B 54695 (by norm_num) ⟨27347, by rfl⟩ (by norm_num))
theorem R211405 : Reach 211405 := rs (se 3 (by rfl) ⟨39638, by rfl⟩) (B 79277 (by norm_num) ⟨39638, by rfl⟩ (by norm_num))
theorem R145877 : Reach 145877 := rs (se 7 (by rfl) ⟨1709, by rfl⟩) (B 3419 (by norm_num) ⟨1709, by rfl⟩ (by norm_num))
theorem R244205 : Reach 244205 := rs (se 3 (by rfl) ⟨45788, by rfl⟩) (B 91577 (by norm_num) ⟨45788, by rfl⟩ (by norm_num))
theorem R145901 : Reach 145901 := rs (se 3 (by rfl) ⟨27356, by rfl⟩) (B 54713 (by norm_num) ⟨27356, by rfl⟩ (by norm_num))
theorem R145925 : Reach 145925 := rs (se 4 (by rfl) ⟨13680, by rfl⟩) (B 27361 (by norm_num) ⟨13680, by rfl⟩ (by norm_num))
theorem R145949 : Reach 145949 := rs (se 3 (by rfl) ⟨27365, by rfl⟩) (B 54731 (by norm_num) ⟨27365, by rfl⟩ (by norm_num))
theorem R145973 : Reach 145973 := rs (se 5 (by rfl) ⟨6842, by rfl⟩) (B 13685 (by norm_num) ⟨6842, by rfl⟩ (by norm_num))
theorem R145997 : Reach 145997 := rs (se 3 (by rfl) ⟨27374, by rfl⟩) (B 54749 (by norm_num) ⟨27374, by rfl⟩ (by norm_num))
theorem R408149 : Reach 408149 := rs (se 8 (by rfl) ⟨2391, by rfl⟩) (B 4783 (by norm_num) ⟨2391, by rfl⟩ (by norm_num))
theorem R146021 : Reach 146021 := rs (se 4 (by rfl) ⟨13689, by rfl⟩) (B 27379 (by norm_num) ⟨13689, by rfl⟩ (by norm_num))
theorem R146045 : Reach 146045 := rs (se 3 (by rfl) ⟨27383, by rfl⟩) (B 54767 (by norm_num) ⟨27383, by rfl⟩ (by norm_num))
theorem R146069 : Reach 146069 := rs (se 6 (by rfl) ⟨3423, by rfl⟩) (B 6847 (by norm_num) ⟨3423, by rfl⟩ (by norm_num))
theorem R277157 : Reach 277157 := rs (se 4 (by rfl) ⟨25983, by rfl⟩) (B 51967 (by norm_num) ⟨25983, by rfl⟩ (by norm_num))
theorem R244397 : Reach 244397 := rs (se 3 (by rfl) ⟨45824, by rfl⟩) (B 91649 (by norm_num) ⟨45824, by rfl⟩ (by norm_num))
theorem R146093 : Reach 146093 := rs (se 3 (by rfl) ⟨27392, by rfl⟩) (B 54785 (by norm_num) ⟨27392, by rfl⟩ (by norm_num))
theorem R113333 : Reach 113333 := rs (se 5 (by rfl) ⟨5312, by rfl⟩) (B 10625 (by norm_num) ⟨5312, by rfl⟩ (by norm_num))
theorem R244421 : Reach 244421 := rs (se 4 (by rfl) ⟨22914, by rfl⟩) (B 45829 (by norm_num) ⟨22914, by rfl⟩ (by norm_num))
theorem R146117 : Reach 146117 := rs (se 4 (by rfl) ⟨13698, by rfl⟩) (B 27397 (by norm_num) ⟨13698, by rfl⟩ (by norm_num))
theorem R211661 : Reach 211661 := rs (se 3 (by rfl) ⟨39686, by rfl⟩) (B 79373 (by norm_num) ⟨39686, by rfl⟩ (by norm_num))
theorem R146141 : Reach 146141 := rs (se 3 (by rfl) ⟨27401, by rfl⟩) (B 54803 (by norm_num) ⟨27401, by rfl⟩ (by norm_num))
theorem R146165 : Reach 146165 := rs (se 5 (by rfl) ⟨6851, by rfl⟩) (B 13703 (by norm_num) ⟨6851, by rfl⟩ (by norm_num))
theorem R146189 : Reach 146189 := rs (se 3 (by rfl) ⟨27410, by rfl⟩) (B 54821 (by norm_num) ⟨27410, by rfl⟩ (by norm_num))
theorem R146213 : Reach 146213 := rs (se 4 (by rfl) ⟨13707, by rfl⟩) (B 27415 (by norm_num) ⟨13707, by rfl⟩ (by norm_num))
theorem R146237 : Reach 146237 := rs (se 3 (by rfl) ⟨27419, by rfl⟩) (B 54839 (by norm_num) ⟨27419, by rfl⟩ (by norm_num))
theorem R310085 : Reach 310085 := rs (se 4 (by rfl) ⟨29070, by rfl⟩) (B 58141 (by norm_num) ⟨29070, by rfl⟩ (by norm_num))
theorem R146261 : Reach 146261 := rs (se 9 (by rfl) ⟨428, by rfl⟩) (B 857 (by norm_num) ⟨428, by rfl⟩ (by norm_num))
theorem R146285 : Reach 146285 := rs (se 3 (by rfl) ⟨27428, by rfl⟩) (B 54857 (by norm_num) ⟨27428, by rfl⟩ (by norm_num))
theorem R146309 : Reach 146309 := rs (se 4 (by rfl) ⟨13716, by rfl⟩) (B 27433 (by norm_num) ⟨13716, by rfl⟩ (by norm_num))
theorem R146333 : Reach 146333 := rs (se 3 (by rfl) ⟨27437, by rfl⟩) (B 54875 (by norm_num) ⟨27437, by rfl⟩ (by norm_num))
theorem R146357 : Reach 146357 := rs (se 5 (by rfl) ⟨6860, by rfl⟩) (B 13721 (by norm_num) ⟨6860, by rfl⟩ (by norm_num))
theorem R146381 : Reach 146381 := rs (se 3 (by rfl) ⟨27446, by rfl⟩) (B 54893 (by norm_num) ⟨27446, by rfl⟩ (by norm_num))
theorem R1391573 : Reach 1391573 := rs (se 7 (by rfl) ⟨16307, by rfl⟩) (B 32615 (by norm_num) ⟨16307, by rfl⟩ (by norm_num))
theorem R146405 : Reach 146405 := rs (se 4 (by rfl) ⟨13725, by rfl⟩) (B 27451 (by norm_num) ⟨13725, by rfl⟩ (by norm_num))
theorem R146429 : Reach 146429 := rs (se 3 (by rfl) ⟨27455, by rfl⟩) (B 54911 (by norm_num) ⟨27455, by rfl⟩ (by norm_num))
theorem R244741 : Reach 244741 := rs (se 4 (by rfl) ⟨22944, by rfl⟩) (B 45889 (by norm_num) ⟨22944, by rfl⟩ (by norm_num))
theorem R146453 : Reach 146453 := rs (se 6 (by rfl) ⟨3432, by rfl⟩) (B 6865 (by norm_num) ⟨3432, by rfl⟩ (by norm_num))
theorem R146477 : Reach 146477 := rs (se 3 (by rfl) ⟨27464, by rfl⟩) (B 54929 (by norm_num) ⟨27464, by rfl⟩ (by norm_num))
theorem R343109 : Reach 343109 := rs (se 4 (by rfl) ⟨32166, by rfl⟩) (B 64333 (by norm_num) ⟨32166, by rfl⟩ (by norm_num))
theorem R146501 : Reach 146501 := rs (se 4 (by rfl) ⟨13734, by rfl⟩) (B 27469 (by norm_num) ⟨13734, by rfl⟩ (by norm_num))
theorem R146525 : Reach 146525 := rs (se 3 (by rfl) ⟨27473, by rfl⟩) (B 54947 (by norm_num) ⟨27473, by rfl⟩ (by norm_num))
theorem R244853 : Reach 244853 := rs (se 5 (by rfl) ⟨11477, by rfl⟩) (B 22955 (by norm_num) ⟨11477, by rfl⟩ (by norm_num))
theorem R146549 : Reach 146549 := rs (se 5 (by rfl) ⟨6869, by rfl⟩) (B 13739 (by norm_num) ⟨6869, by rfl⟩ (by norm_num))
theorem R146573 : Reach 146573 := rs (se 3 (by rfl) ⟨27482, by rfl⟩) (B 54965 (by norm_num) ⟨27482, by rfl⟩ (by norm_num))
theorem R146597 : Reach 146597 := rs (se 4 (by rfl) ⟨13743, by rfl⟩) (B 27487 (by norm_num) ⟨13743, by rfl⟩ (by norm_num))
theorem R146621 : Reach 146621 := rs (se 3 (by rfl) ⟨27491, by rfl⟩) (B 54983 (by norm_num) ⟨27491, by rfl⟩ (by norm_num))
theorem R146645 : Reach 146645 := rs (se 7 (by rfl) ⟨1718, by rfl⟩) (B 3437 (by norm_num) ⟨1718, by rfl⟩ (by norm_num))
theorem R146669 : Reach 146669 := rs (se 3 (by rfl) ⟨27500, by rfl⟩) (B 55001 (by norm_num) ⟨27500, by rfl⟩ (by norm_num))
theorem R146693 : Reach 146693 := rs (se 4 (by rfl) ⟨13752, by rfl⟩) (B 27505 (by norm_num) ⟨13752, by rfl⟩ (by norm_num))
theorem R146717 : Reach 146717 := rs (se 3 (by rfl) ⟨27509, by rfl⟩) (B 55019 (by norm_num) ⟨27509, by rfl⟩ (by norm_num))
theorem R146741 : Reach 146741 := rs (se 5 (by rfl) ⟨6878, by rfl⟩) (B 13757 (by norm_num) ⟨6878, by rfl⟩ (by norm_num))
theorem R245045 : Reach 245045 := rs (se 5 (by rfl) ⟨11486, by rfl⟩) (B 22973 (by norm_num) ⟨11486, by rfl⟩ (by norm_num))
theorem R408901 : Reach 408901 := rs (se 4 (by rfl) ⟨38334, by rfl⟩) (B 76669 (by norm_num) ⟨38334, by rfl⟩ (by norm_num))
theorem R146765 : Reach 146765 := rs (se 3 (by rfl) ⟨27518, by rfl⟩) (B 55037 (by norm_num) ⟨27518, by rfl⟩ (by norm_num))
theorem R146789 : Reach 146789 := rs (se 4 (by rfl) ⟨13761, by rfl⟩) (B 27523 (by norm_num) ⟨13761, by rfl⟩ (by norm_num))
theorem R146813 : Reach 146813 := rs (se 3 (by rfl) ⟨27527, by rfl⟩) (B 55055 (by norm_num) ⟨27527, by rfl⟩ (by norm_num))
theorem R146837 : Reach 146837 := rs (se 6 (by rfl) ⟨3441, by rfl⟩) (B 6883 (by norm_num) ⟨3441, by rfl⟩ (by norm_num))
theorem R146861 : Reach 146861 := rs (se 3 (by rfl) ⟨27536, by rfl⟩) (B 55073 (by norm_num) ⟨27536, by rfl⟩ (by norm_num))
theorem R146885 : Reach 146885 := rs (se 4 (by rfl) ⟨13770, by rfl⟩) (B 27541 (by norm_num) ⟨13770, by rfl⟩ (by norm_num))
theorem R146909 : Reach 146909 := rs (se 3 (by rfl) ⟨27545, by rfl⟩) (B 55091 (by norm_num) ⟨27545, by rfl⟩ (by norm_num))
theorem R146933 : Reach 146933 := rs (se 5 (by rfl) ⟨6887, by rfl⟩) (B 13775 (by norm_num) ⟨6887, by rfl⟩ (by norm_num))
theorem R146957 : Reach 146957 := rs (se 3 (by rfl) ⟨27554, by rfl⟩) (B 55109 (by norm_num) ⟨27554, by rfl⟩ (by norm_num))
theorem R146981 : Reach 146981 := rs (se 4 (by rfl) ⟨13779, by rfl⟩) (B 27559 (by norm_num) ⟨13779, by rfl⟩ (by norm_num))
theorem R147005 : Reach 147005 := rs (se 3 (by rfl) ⟨27563, by rfl⟩) (B 55127 (by norm_num) ⟨27563, by rfl⟩ (by norm_num))
theorem R147029 : Reach 147029 := rs (se 8 (by rfl) ⟨861, by rfl⟩) (B 1723 (by norm_num) ⟨861, by rfl⟩ (by norm_num))
theorem R147053 : Reach 147053 := rs (se 3 (by rfl) ⟨27572, by rfl⟩) (B 55145 (by norm_num) ⟨27572, by rfl⟩ (by norm_num))
theorem R147077 : Reach 147077 := rs (se 4 (by rfl) ⟨13788, by rfl⟩) (B 27577 (by norm_num) ⟨13788, by rfl⟩ (by norm_num))
theorem R245389 : Reach 245389 := rs (se 3 (by rfl) ⟨46010, by rfl⟩) (B 92021 (by norm_num) ⟨46010, by rfl⟩ (by norm_num))
theorem R147101 : Reach 147101 := rs (se 3 (by rfl) ⟨27581, by rfl⟩) (B 55163 (by norm_num) ⟨27581, by rfl⟩ (by norm_num))
theorem R245413 : Reach 245413 := rs (se 4 (by rfl) ⟨23007, by rfl⟩) (B 46015 (by norm_num) ⟨23007, by rfl⟩ (by norm_num))
theorem R147125 : Reach 147125 := rs (se 5 (by rfl) ⟨6896, by rfl⟩) (B 13793 (by norm_num) ⟨6896, by rfl⟩ (by norm_num))
theorem R147149 : Reach 147149 := rs (se 3 (by rfl) ⟨27590, by rfl⟩) (B 55181 (by norm_num) ⟨27590, by rfl⟩ (by norm_num))
theorem R147173 : Reach 147173 := rs (se 4 (by rfl) ⟨13797, by rfl⟩) (B 27595 (by norm_num) ⟨13797, by rfl⟩ (by norm_num))
theorem R245501 : Reach 245501 := rs (se 3 (by rfl) ⟨46031, by rfl⟩) (B 92063 (by norm_num) ⟨46031, by rfl⟩ (by norm_num))
theorem R147197 : Reach 147197 := rs (se 3 (by rfl) ⟨27599, by rfl⟩) (B 55199 (by norm_num) ⟨27599, by rfl⟩ (by norm_num))
theorem R147221 : Reach 147221 := rs (se 6 (by rfl) ⟨3450, by rfl⟩) (B 6901 (by norm_num) ⟨3450, by rfl⟩ (by norm_num))
theorem R147245 : Reach 147245 := rs (se 3 (by rfl) ⟨27608, by rfl⟩) (B 55217 (by norm_num) ⟨27608, by rfl⟩ (by norm_num))
theorem R147269 : Reach 147269 := rs (se 4 (by rfl) ⟨13806, by rfl⟩) (B 27613 (by norm_num) ⟨13806, by rfl⟩ (by norm_num))
theorem R147293 : Reach 147293 := rs (se 3 (by rfl) ⟨27617, by rfl⟩) (B 55235 (by norm_num) ⟨27617, by rfl⟩ (by norm_num))
theorem R147317 : Reach 147317 := rs (se 5 (by rfl) ⟨6905, by rfl⟩) (B 13811 (by norm_num) ⟨6905, by rfl⟩ (by norm_num))
theorem R147341 : Reach 147341 := rs (se 3 (by rfl) ⟨27626, by rfl⟩) (B 55253 (by norm_num) ⟨27626, by rfl⟩ (by norm_num))
theorem R147365 : Reach 147365 := rs (se 4 (by rfl) ⟨13815, by rfl⟩) (B 27631 (by norm_num) ⟨13815, by rfl⟩ (by norm_num))
theorem R245693 : Reach 245693 := rs (se 3 (by rfl) ⟨46067, by rfl⟩) (B 92135 (by norm_num) ⟨46067, by rfl⟩ (by norm_num))
theorem R147389 : Reach 147389 := rs (se 3 (by rfl) ⟨27635, by rfl⟩) (B 55271 (by norm_num) ⟨27635, by rfl⟩ (by norm_num))
theorem R147413 : Reach 147413 := rs (se 7 (by rfl) ⟨1727, by rfl⟩) (B 3455 (by norm_num) ⟨1727, by rfl⟩ (by norm_num))
theorem R147437 : Reach 147437 := rs (se 3 (by rfl) ⟨27644, by rfl⟩) (B 55289 (by norm_num) ⟨27644, by rfl⟩ (by norm_num))
theorem R147461 : Reach 147461 := rs (se 4 (by rfl) ⟨13824, by rfl⟩) (B 27649 (by norm_num) ⟨13824, by rfl⟩ (by norm_num))
theorem R147485 : Reach 147485 := rs (se 3 (by rfl) ⟨27653, by rfl⟩) (B 55307 (by norm_num) ⟨27653, by rfl⟩ (by norm_num))
theorem R409637 : Reach 409637 := rs (se 4 (by rfl) ⟨38403, by rfl⟩) (B 76807 (by norm_num) ⟨38403, by rfl⟩ (by norm_num))
theorem R147509 : Reach 147509 := rs (se 5 (by rfl) ⟨6914, by rfl⟩) (B 13829 (by norm_num) ⟨6914, by rfl⟩ (by norm_num))
theorem R147533 : Reach 147533 := rs (se 3 (by rfl) ⟨27662, by rfl⟩) (B 55325 (by norm_num) ⟨27662, by rfl⟩ (by norm_num))
theorem R147557 : Reach 147557 := rs (se 4 (by rfl) ⟨13833, by rfl⟩) (B 27667 (by norm_num) ⟨13833, by rfl⟩ (by norm_num))
theorem R147565 : Reach 147565 := rs (se 3 (by rfl) ⟨27668, by rfl⟩) (B 55337 (by norm_num) ⟨27668, by rfl⟩ (by norm_num))
theorem R147581 : Reach 147581 := rs (se 3 (by rfl) ⟨27671, by rfl⟩) (B 55343 (by norm_num) ⟨27671, by rfl⟩ (by norm_num))
theorem R147605 : Reach 147605 := rs (se 6 (by rfl) ⟨3459, by rfl⟩) (B 6919 (by norm_num) ⟨3459, by rfl⟩ (by norm_num))
theorem R147629 : Reach 147629 := rs (se 3 (by rfl) ⟨27680, by rfl⟩) (B 55361 (by norm_num) ⟨27680, by rfl⟩ (by norm_num))
theorem R114869 : Reach 114869 := rs (se 5 (by rfl) ⟨5384, by rfl⟩) (B 10769 (by norm_num) ⟨5384, by rfl⟩ (by norm_num))
theorem R147653 : Reach 147653 := rs (se 4 (by rfl) ⟨13842, by rfl⟩) (B 27685 (by norm_num) ⟨13842, by rfl⟩ (by norm_num))
theorem R278741 : Reach 278741 := rs (se 7 (by rfl) ⟨3266, by rfl⟩) (B 6533 (by norm_num) ⟨3266, by rfl⟩ (by norm_num))
theorem R147677 : Reach 147677 := rs (se 3 (by rfl) ⟨27689, by rfl⟩) (B 55379 (by norm_num) ⟨27689, by rfl⟩ (by norm_num))
theorem R147701 : Reach 147701 := rs (se 5 (by rfl) ⟨6923, by rfl⟩) (B 13847 (by norm_num) ⟨6923, by rfl⟩ (by norm_num))
theorem R147725 : Reach 147725 := rs (se 3 (by rfl) ⟨27698, by rfl⟩) (B 55397 (by norm_num) ⟨27698, by rfl⟩ (by norm_num))
theorem R246037 : Reach 246037 := rs (se 6 (by rfl) ⟨5766, by rfl⟩) (B 11533 (by norm_num) ⟨5766, by rfl⟩ (by norm_num))
theorem R147749 : Reach 147749 := rs (se 4 (by rfl) ⟨13851, by rfl⟩) (B 27703 (by norm_num) ⟨13851, by rfl⟩ (by norm_num))
theorem R147773 : Reach 147773 := rs (se 3 (by rfl) ⟨27707, by rfl⟩) (B 55415 (by norm_num) ⟨27707, by rfl⟩ (by norm_num))
theorem R147797 : Reach 147797 := rs (se 10 (by rfl) ⟨216, by rfl⟩) (B 433 (by norm_num) ⟨216, by rfl⟩ (by norm_num))
theorem R147821 : Reach 147821 := rs (se 3 (by rfl) ⟨27716, by rfl⟩) (B 55433 (by norm_num) ⟨27716, by rfl⟩ (by norm_num))
theorem R115057 : Reach 115057 := rs (se 2 (by rfl) ⟨43146, by rfl⟩) (B 86293 (by norm_num) ⟨43146, by rfl⟩ (by norm_num))
theorem R246149 : Reach 246149 := rs (se 4 (by rfl) ⟨23076, by rfl⟩) (B 46153 (by norm_num) ⟨23076, by rfl⟩ (by norm_num))
theorem R147845 : Reach 147845 := rs (se 4 (by rfl) ⟨13860, by rfl⟩) (B 27721 (by norm_num) ⟨13860, by rfl⟩ (by norm_num))
theorem R147869 : Reach 147869 := rs (se 3 (by rfl) ⟨27725, by rfl⟩) (B 55451 (by norm_num) ⟨27725, by rfl⟩ (by norm_num))
theorem R147893 : Reach 147893 := rs (se 5 (by rfl) ⟨6932, by rfl⟩) (B 13865 (by norm_num) ⟨6932, by rfl⟩ (by norm_num))
theorem R147917 : Reach 147917 := rs (se 3 (by rfl) ⟨27734, by rfl⟩) (B 55469 (by norm_num) ⟨27734, by rfl⟩ (by norm_num))
theorem R4047317 : Reach 4047317 := rs (se 7 (by rfl) ⟨47429, by rfl⟩) (B 94859 (by norm_num) ⟨47429, by rfl⟩ (by norm_num))
theorem R180701 : Reach 180701 := rs (se 3 (by rfl) ⟨33881, by rfl⟩) (B 67763 (by norm_num) ⟨33881, by rfl⟩ (by norm_num))
theorem R147941 : Reach 147941 := rs (se 4 (by rfl) ⟨13869, by rfl⟩) (B 27739 (by norm_num) ⟨13869, by rfl⟩ (by norm_num))
theorem R147965 : Reach 147965 := rs (se 3 (by rfl) ⟨27743, by rfl⟩) (B 55487 (by norm_num) ⟨27743, by rfl⟩ (by norm_num))
theorem R147989 : Reach 147989 := rs (se 6 (by rfl) ⟨3468, by rfl⟩) (B 6937 (by norm_num) ⟨3468, by rfl⟩ (by norm_num))
theorem R148013 : Reach 148013 := rs (se 3 (by rfl) ⟨27752, by rfl⟩) (B 55505 (by norm_num) ⟨27752, by rfl⟩ (by norm_num))
theorem R246341 : Reach 246341 := rs (se 4 (by rfl) ⟨23094, by rfl⟩) (B 46189 (by norm_num) ⟨23094, by rfl⟩ (by norm_num))
theorem R148037 : Reach 148037 := rs (se 4 (by rfl) ⟨13878, by rfl⟩) (B 27757 (by norm_num) ⟨13878, by rfl⟩ (by norm_num))
theorem R115273 : Reach 115273 := rs (se 2 (by rfl) ⟨43227, by rfl⟩) (B 86455 (by norm_num) ⟨43227, by rfl⟩ (by norm_num))
theorem R148061 : Reach 148061 := rs (se 3 (by rfl) ⟨27761, by rfl⟩) (B 55523 (by norm_num) ⟨27761, by rfl⟩ (by norm_num))
theorem R148085 : Reach 148085 := rs (se 5 (by rfl) ⟨6941, by rfl⟩) (B 13883 (by norm_num) ⟨6941, by rfl⟩ (by norm_num))
theorem R148109 : Reach 148109 := rs (se 3 (by rfl) ⟨27770, by rfl⟩) (B 55541 (by norm_num) ⟨27770, by rfl⟩ (by norm_num))
theorem R148133 : Reach 148133 := rs (se 4 (by rfl) ⟨13887, by rfl⟩) (B 27775 (by norm_num) ⟨13887, by rfl⟩ (by norm_num))
theorem R148157 : Reach 148157 := rs (se 3 (by rfl) ⟨27779, by rfl⟩) (B 55559 (by norm_num) ⟨27779, by rfl⟩ (by norm_num))
theorem R148181 : Reach 148181 := rs (se 7 (by rfl) ⟨1736, by rfl⟩) (B 3473 (by norm_num) ⟨1736, by rfl⟩ (by norm_num))
theorem R148205 : Reach 148205 := rs (se 3 (by rfl) ⟨27788, by rfl⟩) (B 55577 (by norm_num) ⟨27788, by rfl⟩ (by norm_num))
theorem R148229 : Reach 148229 := rs (se 4 (by rfl) ⟨13896, by rfl⟩) (B 27793 (by norm_num) ⟨13896, by rfl⟩ (by norm_num))
theorem R148253 : Reach 148253 := rs (se 3 (by rfl) ⟨27797, by rfl⟩) (B 55595 (by norm_num) ⟨27797, by rfl⟩ (by norm_num))
theorem R836405 : Reach 836405 := rs (se 5 (by rfl) ⟨39206, by rfl⟩) (B 78413 (by norm_num) ⟨39206, by rfl⟩ (by norm_num))
theorem R148277 : Reach 148277 := rs (se 5 (by rfl) ⟨6950, by rfl⟩) (B 13901 (by norm_num) ⟨6950, by rfl⟩ (by norm_num))
theorem R148301 : Reach 148301 := rs (se 3 (by rfl) ⟨27806, by rfl⟩) (B 55613 (by norm_num) ⟨27806, by rfl⟩ (by norm_num))
theorem R312149 : Reach 312149 := rs (se 9 (by rfl) ⟨914, by rfl⟩) (B 1829 (by norm_num) ⟨914, by rfl⟩ (by norm_num))
theorem R148325 : Reach 148325 := rs (se 4 (by rfl) ⟨13905, by rfl⟩) (B 27811 (by norm_num) ⟨13905, by rfl⟩ (by norm_num))
theorem R115561 : Reach 115561 := rs (se 2 (by rfl) ⟨43335, by rfl⟩) (B 86671 (by norm_num) ⟨43335, by rfl⟩ (by norm_num))
theorem R279413 : Reach 279413 := rs (se 5 (by rfl) ⟨13097, by rfl⟩) (B 26195 (by norm_num) ⟨13097, by rfl⟩ (by norm_num))
theorem R148349 : Reach 148349 := rs (se 3 (by rfl) ⟨27815, by rfl⟩) (B 55631 (by norm_num) ⟨27815, by rfl⟩ (by norm_num))
theorem R148373 : Reach 148373 := rs (se 6 (by rfl) ⟨3477, by rfl⟩) (B 6955 (by norm_num) ⟨3477, by rfl⟩ (by norm_num))
theorem R246685 : Reach 246685 := rs (se 3 (by rfl) ⟨46253, by rfl⟩) (B 92507 (by norm_num) ⟨46253, by rfl⟩ (by norm_num))
theorem R148397 : Reach 148397 := rs (se 3 (by rfl) ⟨27824, by rfl⟩) (B 55649 (by norm_num) ⟨27824, by rfl⟩ (by norm_num))
theorem R148421 : Reach 148421 := rs (se 4 (by rfl) ⟨13914, by rfl⟩) (B 27829 (by norm_num) ⟨13914, by rfl⟩ (by norm_num))
theorem R148445 : Reach 148445 := rs (se 3 (by rfl) ⟨27833, by rfl⟩) (B 55667 (by norm_num) ⟨27833, by rfl⟩ (by norm_num))
theorem R148469 : Reach 148469 := rs (se 5 (by rfl) ⟨6959, by rfl⟩) (B 13919 (by norm_num) ⟨6959, by rfl⟩ (by norm_num))
theorem R246797 : Reach 246797 := rs (se 3 (by rfl) ⟨46274, by rfl⟩) (B 92549 (by norm_num) ⟨46274, by rfl⟩ (by norm_num))
theorem R148493 : Reach 148493 := rs (se 3 (by rfl) ⟨27842, by rfl⟩) (B 55685 (by norm_num) ⟨27842, by rfl⟩ (by norm_num))
theorem R148517 : Reach 148517 := rs (se 4 (by rfl) ⟨13923, by rfl⟩) (B 27847 (by norm_num) ⟨13923, by rfl⟩ (by norm_num))
theorem R148541 : Reach 148541 := rs (se 3 (by rfl) ⟨27851, by rfl⟩) (B 55703 (by norm_num) ⟨27851, by rfl⟩ (by norm_num))
theorem R148565 : Reach 148565 := rs (se 8 (by rfl) ⟨870, by rfl⟩) (B 1741 (by norm_num) ⟨870, by rfl⟩ (by norm_num))
theorem R214109 : Reach 214109 := rs (se 3 (by rfl) ⟨40145, by rfl⟩) (B 80291 (by norm_num) ⟨40145, by rfl⟩ (by norm_num))
theorem R148589 : Reach 148589 := rs (se 3 (by rfl) ⟨27860, by rfl⟩) (B 55721 (by norm_num) ⟨27860, by rfl⟩ (by norm_num))
theorem R148613 : Reach 148613 := rs (se 4 (by rfl) ⟨13932, by rfl⟩) (B 27865 (by norm_num) ⟨13932, by rfl⟩ (by norm_num))
theorem R148637 : Reach 148637 := rs (se 3 (by rfl) ⟨27869, by rfl⟩) (B 55739 (by norm_num) ⟨27869, by rfl⟩ (by norm_num))
theorem R214181 : Reach 214181 := rs (se 4 (by rfl) ⟨20079, by rfl⟩) (B 40159 (by norm_num) ⟨20079, by rfl⟩ (by norm_num))
theorem R148661 : Reach 148661 := rs (se 5 (by rfl) ⟨6968, by rfl⟩) (B 13937 (by norm_num) ⟨6968, by rfl⟩ (by norm_num))
theorem R181453 : Reach 181453 := rs (se 3 (by rfl) ⟨34022, by rfl⟩) (B 68045 (by norm_num) ⟨34022, by rfl⟩ (by norm_num))
theorem R246989 : Reach 246989 := rs (se 3 (by rfl) ⟨46310, by rfl⟩) (B 92621 (by norm_num) ⟨46310, by rfl⟩ (by norm_num))
theorem R148685 : Reach 148685 := rs (se 3 (by rfl) ⟨27878, by rfl⟩) (B 55757 (by norm_num) ⟨27878, by rfl⟩ (by norm_num))
theorem R214253 : Reach 214253 := rs (se 3 (by rfl) ⟨40172, by rfl⟩) (B 80345 (by norm_num) ⟨40172, by rfl⟩ (by norm_num))
theorem R279845 : Reach 279845 := rs (se 4 (by rfl) ⟨26235, by rfl⟩) (B 52471 (by norm_num) ⟨26235, by rfl⟩ (by norm_num))
theorem R214325 : Reach 214325 := rs (se 5 (by rfl) ⟨10046, by rfl⟩) (B 20093 (by norm_num) ⟨10046, by rfl⟩ (by norm_num))
theorem R673109 : Reach 673109 := rs (se 12 (by rfl) ⟨246, by rfl⟩) (B 493 (by norm_num) ⟨246, by rfl⟩ (by norm_num))
theorem R181597 : Reach 181597 := rs (se 3 (by rfl) ⟨34049, by rfl⟩) (B 68099 (by norm_num) ⟨34049, by rfl⟩ (by norm_num))
theorem R214397 : Reach 214397 := rs (se 3 (by rfl) ⟨40199, by rfl⟩) (B 80399 (by norm_num) ⟨40199, by rfl⟩ (by norm_num))
theorem R214469 : Reach 214469 := rs (se 4 (by rfl) ⟨20106, by rfl⟩) (B 40213 (by norm_num) ⟨20106, by rfl⟩ (by norm_num))
theorem R378341 : Reach 378341 := rs (se 4 (by rfl) ⟨35469, by rfl⟩) (B 70939 (by norm_num) ⟨35469, by rfl⟩ (by norm_num))
theorem R181757 : Reach 181757 := rs (se 3 (by rfl) ⟨34079, by rfl⟩) (B 68159 (by norm_num) ⟨34079, by rfl⟩ (by norm_num))
theorem R214541 : Reach 214541 := rs (se 3 (by rfl) ⟨40226, by rfl⟩) (B 80453 (by norm_num) ⟨40226, by rfl⟩ (by norm_num))
theorem R247333 : Reach 247333 := rs (se 4 (by rfl) ⟨23187, by rfl⟩) (B 46375 (by norm_num) ⟨23187, by rfl⟩ (by norm_num))
theorem R214613 : Reach 214613 := rs (se 8 (by rfl) ⟨1257, by rfl⟩) (B 2515 (by norm_num) ⟨1257, by rfl⟩ (by norm_num))
theorem R181901 : Reach 181901 := rs (se 3 (by rfl) ⟨34106, by rfl⟩) (B 68213 (by norm_num) ⟨34106, by rfl⟩ (by norm_num))
theorem R247445 : Reach 247445 := rs (se 6 (by rfl) ⟨5799, by rfl⟩) (B 11599 (by norm_num) ⟨5799, by rfl⟩ (by norm_num))
theorem R214685 : Reach 214685 := rs (se 3 (by rfl) ⟨40253, by rfl⟩) (B 80507 (by norm_num) ⟨40253, by rfl⟩ (by norm_num))
theorem R214757 : Reach 214757 := rs (se 4 (by rfl) ⟨20133, by rfl⟩) (B 40267 (by norm_num) ⟨20133, by rfl⟩ (by norm_num))
theorem R214829 : Reach 214829 := rs (se 3 (by rfl) ⟨40280, by rfl⟩) (B 80561 (by norm_num) ⟨40280, by rfl⟩ (by norm_num))
theorem R247637 : Reach 247637 := rs (se 9 (by rfl) ⟨725, by rfl⟩) (B 1451 (by norm_num) ⟨725, by rfl⟩ (by norm_num))
theorem R214901 : Reach 214901 := rs (se 5 (by rfl) ⟨10073, by rfl⟩) (B 20147 (by norm_num) ⟨10073, by rfl⟩ (by norm_num))
theorem R313237 : Reach 313237 := rs (se 6 (by rfl) ⟨7341, by rfl⟩) (B 14683 (by norm_num) ⟨7341, by rfl⟩ (by norm_num))
theorem R182189 : Reach 182189 := rs (se 3 (by rfl) ⟨34160, by rfl⟩) (B 68321 (by norm_num) ⟨34160, by rfl⟩ (by norm_num))
theorem R214973 : Reach 214973 := rs (se 3 (by rfl) ⟨40307, by rfl⟩) (B 80615 (by norm_num) ⟨40307, by rfl⟩ (by norm_num))
theorem R215045 : Reach 215045 := rs (se 4 (by rfl) ⟨20160, by rfl⟩) (B 40321 (by norm_num) ⟨20160, by rfl⟩ (by norm_num))
theorem R280597 : Reach 280597 := rs (se 6 (by rfl) ⟨6576, by rfl⟩) (B 13153 (by norm_num) ⟨6576, by rfl⟩ (by norm_num))
theorem R182341 : Reach 182341 := rs (se 4 (by rfl) ⟨17094, by rfl⟩) (B 34189 (by norm_num) ⟨17094, by rfl⟩ (by norm_num))
theorem R215117 : Reach 215117 := rs (se 3 (by rfl) ⟨40334, by rfl⟩) (B 80669 (by norm_num) ⟨40334, by rfl⟩ (by norm_num))
theorem R116849 : Reach 116849 := rs (se 2 (by rfl) ⟨43818, by rfl⟩) (B 87637 (by norm_num) ⟨43818, by rfl⟩ (by norm_num))
theorem R215189 : Reach 215189 := rs (se 6 (by rfl) ⟨5043, by rfl⟩) (B 10087 (by norm_num) ⟨5043, by rfl⟩ (by norm_num))
theorem R247981 : Reach 247981 := rs (se 3 (by rfl) ⟨46496, by rfl⟩) (B 92993 (by norm_num) ⟨46496, by rfl⟩ (by norm_num))
theorem R215261 : Reach 215261 := rs (se 3 (by rfl) ⟨40361, by rfl⟩) (B 80723 (by norm_num) ⟨40361, by rfl⟩ (by norm_num))
theorem R248093 : Reach 248093 := rs (se 3 (by rfl) ⟨46517, by rfl⟩) (B 93035 (by norm_num) ⟨46517, by rfl⟩ (by norm_num))
theorem R215333 : Reach 215333 := rs (se 4 (by rfl) ⟨20187, by rfl⟩) (B 40375 (by norm_num) ⟨20187, by rfl⟩ (by norm_num))
theorem R215405 : Reach 215405 := rs (se 3 (by rfl) ⟨40388, by rfl⟩) (B 80777 (by norm_num) ⟨40388, by rfl⟩ (by norm_num))
theorem R182645 : Reach 182645 := rs (se 5 (by rfl) ⟨8561, by rfl⟩) (B 17123 (by norm_num) ⟨8561, by rfl⟩ (by norm_num))
theorem R215477 : Reach 215477 := rs (se 5 (by rfl) ⟨10100, by rfl⟩) (B 20201 (by norm_num) ⟨10100, by rfl⟩ (by norm_num))
theorem R248285 : Reach 248285 := rs (se 3 (by rfl) ⟨46553, by rfl⟩) (B 93107 (by norm_num) ⟨46553, by rfl⟩ (by norm_num))
theorem R444901 : Reach 444901 := rs (se 4 (by rfl) ⟨41709, by rfl⟩) (B 83419 (by norm_num) ⟨41709, by rfl⟩ (by norm_num))
theorem R215549 : Reach 215549 := rs (se 3 (by rfl) ⟨40415, by rfl⟩) (B 80831 (by norm_num) ⟨40415, by rfl⟩ (by norm_num))
theorem R215621 : Reach 215621 := rs (se 4 (by rfl) ⟨20214, by rfl⟩) (B 40429 (by norm_num) ⟨20214, by rfl⟩ (by norm_num))
theorem R215693 : Reach 215693 := rs (se 3 (by rfl) ⟨40442, by rfl⟩) (B 80885 (by norm_num) ⟨40442, by rfl⟩ (by norm_num))
theorem R117445 : Reach 117445 := rs (se 4 (by rfl) ⟨11010, by rfl⟩) (B 22021 (by norm_num) ⟨11010, by rfl⟩ (by norm_num))
theorem R215765 : Reach 215765 := rs (se 7 (by rfl) ⟨2528, by rfl⟩) (B 5057 (by norm_num) ⟨2528, by rfl⟩ (by norm_num))
theorem R215837 : Reach 215837 := rs (se 3 (by rfl) ⟨40469, by rfl⟩) (B 80939 (by norm_num) ⟨40469, by rfl⟩ (by norm_num))
theorem R117541 : Reach 117541 := rs (se 4 (by rfl) ⟨11019, by rfl⟩) (B 22039 (by norm_num) ⟨11019, by rfl⟩ (by norm_num))
theorem R248629 : Reach 248629 := rs (se 5 (by rfl) ⟨11654, by rfl⟩) (B 23309 (by norm_num) ⟨11654, by rfl⟩ (by norm_num))
theorem R215909 : Reach 215909 := rs (se 4 (by rfl) ⟨20241, by rfl⟩) (B 40483 (by norm_num) ⟨20241, by rfl⟩ (by norm_num))
theorem R248741 : Reach 248741 := rs (se 4 (by rfl) ⟨23319, by rfl⟩) (B 46639 (by norm_num) ⟨23319, by rfl⟩ (by norm_num))
theorem R215981 : Reach 215981 := rs (se 3 (by rfl) ⟨40496, by rfl⟩) (B 80993 (by norm_num) ⟨40496, by rfl⟩ (by norm_num))
theorem R216053 : Reach 216053 := rs (se 5 (by rfl) ⟨10127, by rfl⟩) (B 20255 (by norm_num) ⟨10127, by rfl⟩ (by norm_num))
theorem R248845 : Reach 248845 := rs (se 3 (by rfl) ⟨46658, by rfl⟩) (B 93317 (by norm_num) ⟨46658, by rfl⟩ (by norm_num))
theorem R314405 : Reach 314405 := rs (se 4 (by rfl) ⟨29475, by rfl⟩) (B 58951 (by norm_num) ⟨29475, by rfl⟩ (by norm_num))
theorem R216125 : Reach 216125 := rs (se 3 (by rfl) ⟨40523, by rfl⟩) (B 81047 (by norm_num) ⟨40523, by rfl⟩ (by norm_num))
theorem R117821 : Reach 117821 := rs (se 3 (by rfl) ⟨22091, by rfl⟩) (B 44183 (by norm_num) ⟨22091, by rfl⟩ (by norm_num))
theorem R183397 : Reach 183397 := rs (se 4 (by rfl) ⟨17193, by rfl⟩) (B 34387 (by norm_num) ⟨17193, by rfl⟩ (by norm_num))
theorem R248933 : Reach 248933 := rs (se 4 (by rfl) ⟨23337, by rfl⟩) (B 46675 (by norm_num) ⟨23337, by rfl⟩ (by norm_num))
theorem R216197 : Reach 216197 := rs (se 4 (by rfl) ⟨20268, by rfl⟩) (B 40537 (by norm_num) ⟨20268, by rfl⟩ (by norm_num))
theorem R216269 : Reach 216269 := rs (se 3 (by rfl) ⟨40550, by rfl⟩) (B 81101 (by norm_num) ⟨40550, by rfl⟩ (by norm_num))
theorem R183541 : Reach 183541 := rs (se 5 (by rfl) ⟨8603, by rfl⟩) (B 17207 (by norm_num) ⟨8603, by rfl⟩ (by norm_num))
theorem R412933 : Reach 412933 := rs (se 4 (by rfl) ⟨38712, by rfl⟩) (B 77425 (by norm_num) ⟨38712, by rfl⟩ (by norm_num))
theorem R216341 : Reach 216341 := rs (se 6 (by rfl) ⟨5070, by rfl⟩) (B 10141 (by norm_num) ⟨5070, by rfl⟩ (by norm_num))
theorem R544085 : Reach 544085 := rs (se 11 (by rfl) ⟨398, by rfl⟩) (B 797 (by norm_num) ⟨398, by rfl⟩ (by norm_num))
theorem R216413 : Reach 216413 := rs (se 3 (by rfl) ⟨40577, by rfl⟩) (B 81155 (by norm_num) ⟨40577, by rfl⟩ (by norm_num))
theorem R183701 : Reach 183701 := rs (se 6 (by rfl) ⟨4305, by rfl⟩) (B 8611 (by norm_num) ⟨4305, by rfl⟩ (by norm_num))
theorem R216485 : Reach 216485 := rs (se 4 (by rfl) ⟨20295, by rfl⟩) (B 40591 (by norm_num) ⟨20295, by rfl⟩ (by norm_num))
theorem R249277 : Reach 249277 := rs (se 3 (by rfl) ⟨46739, by rfl⟩) (B 93479 (by norm_num) ⟨46739, by rfl⟩ (by norm_num))
theorem R216557 : Reach 216557 := rs (se 3 (by rfl) ⟨40604, by rfl⟩) (B 81209 (by norm_num) ⟨40604, by rfl⟩ (by norm_num))
theorem R183845 : Reach 183845 := rs (se 4 (by rfl) ⟨17235, by rfl⟩) (B 34471 (by norm_num) ⟨17235, by rfl⟩ (by norm_num))
theorem R249389 : Reach 249389 := rs (se 3 (by rfl) ⟨46760, by rfl⟩) (B 93521 (by norm_num) ⟨46760, by rfl⟩ (by norm_num))
theorem R216629 : Reach 216629 := rs (se 5 (by rfl) ⟨10154, by rfl⟩) (B 20309 (by norm_num) ⟨10154, by rfl⟩ (by norm_num))
theorem R446069 : Reach 446069 := rs (se 5 (by rfl) ⟨20909, by rfl⟩) (B 41819 (by norm_num) ⟨20909, by rfl⟩ (by norm_num))
theorem R216701 : Reach 216701 := rs (se 3 (by rfl) ⟨40631, by rfl⟩) (B 81263 (by norm_num) ⟨40631, by rfl⟩ (by norm_num))
theorem R216773 : Reach 216773 := rs (se 4 (by rfl) ⟨20322, by rfl⟩) (B 40645 (by norm_num) ⟨20322, by rfl⟩ (by norm_num))
theorem R249581 : Reach 249581 := rs (se 3 (by rfl) ⟨46796, by rfl⟩) (B 93593 (by norm_num) ⟨46796, by rfl⟩ (by norm_num))
theorem R216845 : Reach 216845 := rs (se 3 (by rfl) ⟨40658, by rfl⟩) (B 81317 (by norm_num) ⟨40658, by rfl⟩ (by norm_num))
theorem R184133 : Reach 184133 := rs (se 4 (by rfl) ⟨17262, by rfl⟩) (B 34525 (by norm_num) ⟨17262, by rfl⟩ (by norm_num))
theorem R216917 : Reach 216917 := rs (se 9 (by rfl) ⟨635, by rfl⟩) (B 1271 (by norm_num) ⟨635, by rfl⟩ (by norm_num))
theorem R2117461 : Reach 2117461 := rs (se 9 (by rfl) ⟨6203, by rfl⟩) (B 12407 (by norm_num) ⟨6203, by rfl⟩ (by norm_num))
theorem R216989 : Reach 216989 := rs (se 3 (by rfl) ⟨40685, by rfl⟩) (B 81371 (by norm_num) ⟨40685, by rfl⟩ (by norm_num))
theorem R118685 : Reach 118685 := rs (se 3 (by rfl) ⟨22253, by rfl⟩) (B 44507 (by norm_num) ⟨22253, by rfl⟩ (by norm_num))
theorem R282533 : Reach 282533 := rs (se 4 (by rfl) ⟨26487, by rfl⟩) (B 52975 (by norm_num) ⟨26487, by rfl⟩ (by norm_num))
theorem R184285 : Reach 184285 := rs (se 3 (by rfl) ⟨34553, by rfl⟩) (B 69107 (by norm_num) ⟨34553, by rfl⟩ (by norm_num))
theorem R217061 : Reach 217061 := rs (se 4 (by rfl) ⟨20349, by rfl⟩) (B 40699 (by norm_num) ⟨20349, by rfl⟩ (by norm_num))
theorem R380933 : Reach 380933 := rs (se 4 (by rfl) ⟨35712, by rfl⟩) (B 71425 (by norm_num) ⟨35712, by rfl⟩ (by norm_num))
theorem R217133 : Reach 217133 := rs (se 3 (by rfl) ⟨40712, by rfl⟩) (B 81425 (by norm_num) ⟨40712, by rfl⟩ (by norm_num))
theorem R249925 : Reach 249925 := rs (se 4 (by rfl) ⟨23430, by rfl⟩) (B 46861 (by norm_num) ⟨23430, by rfl⟩ (by norm_num))
theorem R217205 : Reach 217205 := rs (se 5 (by rfl) ⟨10181, by rfl⟩) (B 20363 (by norm_num) ⟨10181, by rfl⟩ (by norm_num))
theorem R250037 : Reach 250037 := rs (se 5 (by rfl) ⟨11720, by rfl⟩) (B 23441 (by norm_num) ⟨11720, by rfl⟩ (by norm_num))
theorem R217277 : Reach 217277 := rs (se 3 (by rfl) ⟨40739, by rfl⟩) (B 81479 (by norm_num) ⟨40739, by rfl⟩ (by norm_num))
theorem R708821 : Reach 708821 := rs (se 7 (by rfl) ⟨8306, by rfl⟩) (B 16613 (by norm_num) ⟨8306, by rfl⟩ (by norm_num))
theorem R119017 : Reach 119017 := rs (se 2 (by rfl) ⟨44631, by rfl⟩) (B 89263 (by norm_num) ⟨44631, by rfl⟩ (by norm_num))
theorem R217349 : Reach 217349 := rs (se 4 (by rfl) ⟨20376, by rfl⟩) (B 40753 (by norm_num) ⟨20376, by rfl⟩ (by norm_num))
theorem R184589 : Reach 184589 := rs (se 3 (by rfl) ⟨34610, by rfl⟩) (B 69221 (by norm_num) ⟨34610, by rfl⟩ (by norm_num))
theorem R217421 : Reach 217421 := rs (se 3 (by rfl) ⟨40766, by rfl⟩) (B 81533 (by norm_num) ⟨40766, by rfl⟩ (by norm_num))
theorem R250229 : Reach 250229 := rs (se 5 (by rfl) ⟨11729, by rfl⟩) (B 23459 (by norm_num) ⟨11729, by rfl⟩ (by norm_num))
theorem R217493 : Reach 217493 := rs (se 6 (by rfl) ⟨5097, by rfl⟩) (B 10195 (by norm_num) ⟨5097, by rfl⟩ (by norm_num))
theorem R217565 : Reach 217565 := rs (se 3 (by rfl) ⟨40793, by rfl⟩) (B 81587 (by norm_num) ⟨40793, by rfl⟩ (by norm_num))
theorem R217637 : Reach 217637 := rs (se 4 (by rfl) ⟨20403, by rfl⟩) (B 40807 (by norm_num) ⟨20403, by rfl⟩ (by norm_num))
theorem R217709 : Reach 217709 := rs (se 3 (by rfl) ⟨40820, by rfl⟩) (B 81641 (by norm_num) ⟨40820, by rfl⟩ (by norm_num))
theorem R217781 : Reach 217781 := rs (se 5 (by rfl) ⟨10208, by rfl⟩) (B 20417 (by norm_num) ⟨10208, by rfl⟩ (by norm_num))
theorem R250573 : Reach 250573 := rs (se 3 (by rfl) ⟨46982, by rfl⟩) (B 93965 (by norm_num) ⟨46982, by rfl⟩ (by norm_num))
theorem R217853 : Reach 217853 := rs (se 3 (by rfl) ⟨40847, by rfl⟩) (B 81695 (by norm_num) ⟨40847, by rfl⟩ (by norm_num))
theorem R250685 : Reach 250685 := rs (se 3 (by rfl) ⟨47003, by rfl⟩) (B 94007 (by norm_num) ⟨47003, by rfl⟩ (by norm_num))
theorem R217925 : Reach 217925 := rs (se 4 (by rfl) ⟨20430, by rfl⟩) (B 40861 (by norm_num) ⟨20430, by rfl⟩ (by norm_num))
theorem R316261 : Reach 316261 := rs (se 4 (by rfl) ⟨29649, by rfl⟩) (B 59299 (by norm_num) ⟨29649, by rfl⟩ (by norm_num))
theorem R217997 : Reach 217997 := rs (se 3 (by rfl) ⟨40874, by rfl⟩) (B 81749 (by norm_num) ⟨40874, by rfl⟩ (by norm_num))
theorem R218069 : Reach 218069 := rs (se 7 (by rfl) ⟨2555, by rfl⟩) (B 5111 (by norm_num) ⟨2555, by rfl⟩ (by norm_num))
theorem R185341 : Reach 185341 := rs (se 3 (by rfl) ⟨34751, by rfl⟩) (B 69503 (by norm_num) ⟨34751, by rfl⟩ (by norm_num))
theorem R250877 : Reach 250877 := rs (se 3 (by rfl) ⟨47039, by rfl⟩) (B 94079 (by norm_num) ⟨47039, by rfl⟩ (by norm_num))
theorem R218141 : Reach 218141 := rs (se 3 (by rfl) ⟨40901, by rfl⟩) (B 81803 (by norm_num) ⟨40901, by rfl⟩ (by norm_num))
theorem R152621 : Reach 152621 := rs (se 3 (by rfl) ⟨28616, by rfl⟩) (B 57233 (by norm_num) ⟨28616, by rfl⟩ (by norm_num))
theorem R218213 : Reach 218213 := rs (se 4 (by rfl) ⟨20457, by rfl⟩) (B 40915 (by norm_num) ⟨20457, by rfl⟩ (by norm_num))
theorem R250997 : Reach 250997 := rs (se 5 (by rfl) ⟨11765, by rfl⟩) (B 23531 (by norm_num) ⟨11765, by rfl⟩ (by norm_num))
theorem R185485 : Reach 185485 := rs (se 3 (by rfl) ⟨34778, by rfl⟩) (B 69557 (by norm_num) ⟨34778, by rfl⟩ (by norm_num))
theorem R218285 : Reach 218285 := rs (se 3 (by rfl) ⟨40928, by rfl⟩) (B 81857 (by norm_num) ⟨40928, by rfl⟩ (by norm_num))
theorem R152813 : Reach 152813 := rs (se 3 (by rfl) ⟨28652, by rfl⟩) (B 57305 (by norm_num) ⟨28652, by rfl⟩ (by norm_num))
theorem R218357 : Reach 218357 := rs (se 5 (by rfl) ⟨10235, by rfl⟩) (B 20471 (by norm_num) ⟨10235, by rfl⟩ (by norm_num))
theorem R185645 : Reach 185645 := rs (se 3 (by rfl) ⟨34808, by rfl⟩) (B 69617 (by norm_num) ⟨34808, by rfl⟩ (by norm_num))
theorem R218429 : Reach 218429 := rs (se 3 (by rfl) ⟨40955, by rfl⟩) (B 81911 (by norm_num) ⟨40955, by rfl⟩ (by norm_num))
theorem R218501 : Reach 218501 := rs (se 4 (by rfl) ⟨20484, by rfl⟩) (B 40969 (by norm_num) ⟨20484, by rfl⟩ (by norm_num))
theorem R1037717 : Reach 1037717 := rs (se 6 (by rfl) ⟨24321, by rfl⟩) (B 48643 (by norm_num) ⟨24321, by rfl⟩ (by norm_num))
theorem R185789 : Reach 185789 := rs (se 3 (by rfl) ⟨34835, by rfl⟩) (B 69671 (by norm_num) ⟨34835, by rfl⟩ (by norm_num))
theorem R218573 : Reach 218573 := rs (se 3 (by rfl) ⟨40982, by rfl⟩) (B 81965 (by norm_num) ⟨40982, by rfl⟩ (by norm_num))
theorem R218645 : Reach 218645 := rs (se 6 (by rfl) ⟨5124, by rfl⟩) (B 10249 (by norm_num) ⟨5124, by rfl⟩ (by norm_num))
theorem R218717 : Reach 218717 := rs (se 3 (by rfl) ⟨41009, by rfl⟩) (B 82019 (by norm_num) ⟨41009, by rfl⟩ (by norm_num))
theorem R120457 : Reach 120457 := rs (se 2 (by rfl) ⟨45171, by rfl⟩) (B 90343 (by norm_num) ⟨45171, by rfl⟩ (by norm_num))
theorem R218789 : Reach 218789 := rs (se 4 (by rfl) ⟨20511, by rfl⟩) (B 41023 (by norm_num) ⟨20511, by rfl⟩ (by norm_num))
theorem R743093 : Reach 743093 := rs (se 5 (by rfl) ⟨34832, by rfl⟩) (B 69665 (by norm_num) ⟨34832, by rfl⟩ (by norm_num))
theorem R186077 : Reach 186077 := rs (se 3 (by rfl) ⟨34889, by rfl⟩) (B 69779 (by norm_num) ⟨34889, by rfl⟩ (by norm_num))
theorem R218861 : Reach 218861 := rs (se 3 (by rfl) ⟨41036, by rfl⟩) (B 82073 (by norm_num) ⟨41036, by rfl⟩ (by norm_num))
theorem R218933 : Reach 218933 := rs (se 5 (by rfl) ⟨10262, by rfl⟩) (B 20525 (by norm_num) ⟨10262, by rfl⟩ (by norm_num))
theorem R120629 : Reach 120629 := rs (se 5 (by rfl) ⟨5654, by rfl⟩) (B 11309 (by norm_num) ⟨5654, by rfl⟩ (by norm_num))
theorem R120685 : Reach 120685 := rs (se 3 (by rfl) ⟨22628, by rfl⟩) (B 45257 (by norm_num) ⟨22628, by rfl⟩ (by norm_num))
theorem R186229 : Reach 186229 := rs (se 5 (by rfl) ⟨8729, by rfl⟩) (B 17459 (by norm_num) ⟨8729, by rfl⟩ (by norm_num))
theorem R219005 : Reach 219005 := rs (se 3 (by rfl) ⟨41063, by rfl⟩) (B 82127 (by norm_num) ⟨41063, by rfl⟩ (by norm_num))
theorem R219077 : Reach 219077 := rs (se 4 (by rfl) ⟨20538, by rfl⟩) (B 41077 (by norm_num) ⟨20538, by rfl⟩ (by norm_num))
theorem R120781 : Reach 120781 := rs (se 3 (by rfl) ⟨22646, by rfl⟩) (B 45293 (by norm_num) ⟨22646, by rfl⟩ (by norm_num))
theorem R219149 : Reach 219149 := rs (se 3 (by rfl) ⟨41090, by rfl⟩) (B 82181 (by norm_num) ⟨41090, by rfl⟩ (by norm_num))
theorem R219221 : Reach 219221 := rs (se 8 (by rfl) ⟨1284, by rfl⟩) (B 2569 (by norm_num) ⟨1284, by rfl⟩ (by norm_num))
theorem R120953 : Reach 120953 := rs (se 2 (by rfl) ⟨45357, by rfl⟩) (B 90715 (by norm_num) ⟨45357, by rfl⟩ (by norm_num))
theorem R219293 : Reach 219293 := rs (se 3 (by rfl) ⟨41117, by rfl⟩) (B 82235 (by norm_num) ⟨41117, by rfl⟩ (by norm_num))
theorem R186533 : Reach 186533 := rs (se 4 (by rfl) ⟨17487, by rfl⟩) (B 34975 (by norm_num) ⟨17487, by rfl⟩ (by norm_num))
theorem R121009 : Reach 121009 := rs (se 2 (by rfl) ⟨45378, by rfl⟩) (B 90757 (by norm_num) ⟨45378, by rfl⟩ (by norm_num))
theorem R415925 : Reach 415925 := rs (se 5 (by rfl) ⟨19496, by rfl⟩) (B 38993 (by norm_num) ⟨19496, by rfl⟩ (by norm_num))
theorem R219365 : Reach 219365 := rs (se 4 (by rfl) ⟨20565, by rfl⟩) (B 41131 (by norm_num) ⟨20565, by rfl⟩ (by norm_num))
theorem R121105 : Reach 121105 := rs (se 2 (by rfl) ⟨45414, by rfl⟩) (B 90829 (by norm_num) ⟨45414, by rfl⟩ (by norm_num))
theorem R219437 : Reach 219437 := rs (se 3 (by rfl) ⟨41144, by rfl⟩) (B 82289 (by norm_num) ⟨41144, by rfl⟩ (by norm_num))
theorem R219509 : Reach 219509 := rs (se 5 (by rfl) ⟨10289, by rfl⟩) (B 20579 (by norm_num) ⟨10289, by rfl⟩ (by norm_num))
theorem R121277 : Reach 121277 := rs (se 3 (by rfl) ⟨22739, by rfl⟩) (B 45479 (by norm_num) ⟨22739, by rfl⟩ (by norm_num))
theorem R219581 : Reach 219581 := rs (se 3 (by rfl) ⟨41171, by rfl⟩) (B 82343 (by norm_num) ⟨41171, by rfl⟩ (by norm_num))
theorem R121333 : Reach 121333 := rs (se 5 (by rfl) ⟨5687, by rfl⟩) (B 11375 (by norm_num) ⟨5687, by rfl⟩ (by norm_num))
theorem R219653 : Reach 219653 := rs (se 4 (by rfl) ⟨20592, by rfl⟩) (B 41185 (by norm_num) ⟨20592, by rfl⟩ (by norm_num))
theorem R154133 : Reach 154133 := rs (se 6 (by rfl) ⟨3612, by rfl⟩) (B 7225 (by norm_num) ⟨3612, by rfl⟩ (by norm_num))
theorem R219725 : Reach 219725 := rs (se 3 (by rfl) ⟨41198, by rfl⟩) (B 82397 (by norm_num) ⟨41198, by rfl⟩ (by norm_num))
theorem R121429 : Reach 121429 := rs (se 8 (by rfl) ⟨711, by rfl⟩) (B 1423 (by norm_num) ⟨711, by rfl⟩ (by norm_num))
theorem R350837 : Reach 350837 := rs (se 5 (by rfl) ⟨16445, by rfl⟩) (B 32891 (by norm_num) ⟨16445, by rfl⟩ (by norm_num))
theorem R154229 : Reach 154229 := rs (se 5 (by rfl) ⟨7229, by rfl⟩) (B 14459 (by norm_num) ⟨7229, by rfl⟩ (by norm_num))
theorem R154261 : Reach 154261 := rs (se 6 (by rfl) ⟨3615, by rfl⟩) (B 7231 (by norm_num) ⟨3615, by rfl⟩ (by norm_num))
theorem R219797 : Reach 219797 := rs (se 6 (by rfl) ⟨5151, by rfl⟩) (B 10303 (by norm_num) ⟨5151, by rfl⟩ (by norm_num))
theorem R219869 : Reach 219869 := rs (se 3 (by rfl) ⟨41225, by rfl⟩) (B 82451 (by norm_num) ⟨41225, by rfl⟩ (by norm_num))
theorem R121601 : Reach 121601 := rs (se 2 (by rfl) ⟨45600, by rfl⟩) (B 91201 (by norm_num) ⟨45600, by rfl⟩ (by norm_num))
theorem R219941 : Reach 219941 := rs (se 4 (by rfl) ⟨20619, by rfl⟩) (B 41239 (by norm_num) ⟨20619, by rfl⟩ (by norm_num))
theorem R121657 : Reach 121657 := rs (se 2 (by rfl) ⟨45621, by rfl⟩) (B 91243 (by norm_num) ⟨45621, by rfl⟩ (by norm_num))
theorem R220013 : Reach 220013 := rs (se 3 (by rfl) ⟨41252, by rfl⟩) (B 82505 (by norm_num) ⟨41252, by rfl⟩ (by norm_num))
theorem R187285 : Reach 187285 := rs (se 6 (by rfl) ⟨4389, by rfl⟩) (B 8779 (by norm_num) ⟨4389, by rfl⟩ (by norm_num))
theorem R121753 : Reach 121753 := rs (se 2 (by rfl) ⟨45657, by rfl⟩) (B 91315 (by norm_num) ⟨45657, by rfl⟩ (by norm_num))
theorem R220085 : Reach 220085 := rs (se 5 (by rfl) ⟨10316, by rfl⟩) (B 20633 (by norm_num) ⟨10316, by rfl⟩ (by norm_num))
theorem R220157 : Reach 220157 := rs (se 3 (by rfl) ⟨41279, by rfl⟩) (B 82559 (by norm_num) ⟨41279, by rfl⟩ (by norm_num))
theorem R187429 : Reach 187429 := rs (se 4 (by rfl) ⟨17571, by rfl⟩) (B 35143 (by norm_num) ⟨17571, by rfl⟩ (by norm_num))
theorem R121925 : Reach 121925 := rs (se 4 (by rfl) ⟨11430, by rfl⟩) (B 22861 (by norm_num) ⟨11430, by rfl⟩ (by norm_num))
theorem R220229 : Reach 220229 := rs (se 4 (by rfl) ⟨20646, by rfl⟩) (B 41293 (by norm_num) ⟨20646, by rfl⟩ (by norm_num))
theorem R121981 : Reach 121981 := rs (se 3 (by rfl) ⟨22871, by rfl⟩) (B 45743 (by norm_num) ⟨22871, by rfl⟩ (by norm_num))
theorem R187525 : Reach 187525 := rs (se 4 (by rfl) ⟨17580, by rfl⟩) (B 35161 (by norm_num) ⟨17580, by rfl⟩ (by norm_num))
theorem R220301 : Reach 220301 := rs (se 3 (by rfl) ⟨41306, by rfl⟩) (B 82613 (by norm_num) ⟨41306, by rfl⟩ (by norm_num))
theorem R416933 : Reach 416933 := rs (se 4 (by rfl) ⟨39087, by rfl⟩) (B 78175 (by norm_num) ⟨39087, by rfl⟩ (by norm_num))
theorem R187589 : Reach 187589 := rs (se 4 (by rfl) ⟨17586, by rfl⟩) (B 35173 (by norm_num) ⟨17586, by rfl⟩ (by norm_num))
theorem R220373 : Reach 220373 := rs (se 7 (by rfl) ⟨2582, by rfl⟩) (B 5165 (by norm_num) ⟨2582, by rfl⟩ (by norm_num))
theorem R122077 : Reach 122077 := rs (se 3 (by rfl) ⟨22889, by rfl⟩) (B 45779 (by norm_num) ⟨22889, by rfl⟩ (by norm_num))
theorem R154885 : Reach 154885 := rs (se 4 (by rfl) ⟨14520, by rfl⟩) (B 29041 (by norm_num) ⟨14520, by rfl⟩ (by norm_num))
theorem R548117 : Reach 548117 := rs (se 6 (by rfl) ⟨12846, by rfl⟩) (B 25693 (by norm_num) ⟨12846, by rfl⟩ (by norm_num))
theorem R220445 : Reach 220445 := rs (se 3 (by rfl) ⟨41333, by rfl⟩) (B 82667 (by norm_num) ⟨41333, by rfl⟩ (by norm_num))
theorem R482597 : Reach 482597 := rs (se 4 (by rfl) ⟨45243, by rfl⟩) (B 90487 (by norm_num) ⟨45243, by rfl⟩ (by norm_num))
theorem R187733 : Reach 187733 := rs (se 11 (by rfl) ⟨137, by rfl⟩) (B 275 (by norm_num) ⟨137, by rfl⟩ (by norm_num))
theorem R220517 : Reach 220517 := rs (se 4 (by rfl) ⟨20673, by rfl⟩) (B 41347 (by norm_num) ⟨20673, by rfl⟩ (by norm_num))
theorem R122249 : Reach 122249 := rs (se 2 (by rfl) ⟨45843, by rfl⟩) (B 91687 (by norm_num) ⟨45843, by rfl⟩ (by norm_num))
theorem R220589 : Reach 220589 := rs (se 3 (by rfl) ⟨41360, by rfl⟩) (B 82721 (by norm_num) ⟨41360, by rfl⟩ (by norm_num))
theorem R122305 : Reach 122305 := rs (se 2 (by rfl) ⟨45864, by rfl⟩) (B 91729 (by norm_num) ⟨45864, by rfl⟩ (by norm_num))
theorem R2252245 : Reach 2252245 := rs (se 7 (by rfl) ⟨26393, by rfl⟩) (B 52787 (by norm_num) ⟨26393, by rfl⟩ (by norm_num))
theorem R220661 : Reach 220661 := rs (se 5 (by rfl) ⟨10343, by rfl⟩) (B 20687 (by norm_num) ⟨10343, by rfl⟩ (by norm_num))
theorem R122401 : Reach 122401 := rs (se 2 (by rfl) ⟨45900, by rfl⟩) (B 91801 (by norm_num) ⟨45900, by rfl⟩ (by norm_num))
theorem R220733 : Reach 220733 := rs (se 3 (by rfl) ⟨41387, by rfl⟩) (B 82775 (by norm_num) ⟨41387, by rfl⟩ (by norm_num))
theorem R188021 : Reach 188021 := rs (se 5 (by rfl) ⟨8813, by rfl⟩) (B 17627 (by norm_num) ⟨8813, by rfl⟩ (by norm_num))
theorem R220805 : Reach 220805 := rs (se 4 (by rfl) ⟨20700, by rfl⟩) (B 41401 (by norm_num) ⟨20700, by rfl⟩ (by norm_num))
theorem R122573 : Reach 122573 := rs (se 3 (by rfl) ⟨22982, by rfl⟩) (B 45965 (by norm_num) ⟨22982, by rfl⟩ (by norm_num))
theorem R220877 : Reach 220877 := rs (se 3 (by rfl) ⟨41414, by rfl⟩) (B 82829 (by norm_num) ⟨41414, by rfl⟩ (by norm_num))
theorem R351989 : Reach 351989 := rs (se 5 (by rfl) ⟨16499, by rfl⟩) (B 32999 (by norm_num) ⟨16499, by rfl⟩ (by norm_num))
theorem R122629 : Reach 122629 := rs (se 4 (by rfl) ⟨11496, by rfl⟩) (B 22993 (by norm_num) ⟨11496, by rfl⟩ (by norm_num))
theorem R188173 : Reach 188173 := rs (se 3 (by rfl) ⟨35282, by rfl⟩) (B 70565 (by norm_num) ⟨35282, by rfl⟩ (by norm_num))
theorem R220949 : Reach 220949 := rs (se 6 (by rfl) ⟨5178, by rfl⟩) (B 10357 (by norm_num) ⟨5178, by rfl⟩ (by norm_num))
theorem R221021 : Reach 221021 := rs (se 3 (by rfl) ⟨41441, by rfl⟩) (B 82883 (by norm_num) ⟨41441, by rfl⟩ (by norm_num))
theorem R122725 : Reach 122725 := rs (se 4 (by rfl) ⟨11505, by rfl⟩) (B 23011 (by norm_num) ⟨11505, by rfl⟩ (by norm_num))
theorem R221093 : Reach 221093 := rs (se 4 (by rfl) ⟨20727, by rfl⟩) (B 41455 (by norm_num) ⟨20727, by rfl⟩ (by norm_num))
theorem R221165 : Reach 221165 := rs (se 3 (by rfl) ⟨41468, by rfl⟩) (B 82937 (by norm_num) ⟨41468, by rfl⟩ (by norm_num))
theorem R122897 : Reach 122897 := rs (se 2 (by rfl) ⟨46086, by rfl⟩) (B 92173 (by norm_num) ⟨46086, by rfl⟩ (by norm_num))
theorem R221237 : Reach 221237 := rs (se 5 (by rfl) ⟨10370, by rfl⟩) (B 20741 (by norm_num) ⟨10370, by rfl⟩ (by norm_num))
theorem R122953 : Reach 122953 := rs (se 2 (by rfl) ⟨46107, by rfl⟩) (B 92215 (by norm_num) ⟨46107, by rfl⟩ (by norm_num))
theorem R155773 : Reach 155773 := rs (se 3 (by rfl) ⟨29207, by rfl⟩) (B 58415 (by norm_num) ⟨29207, by rfl⟩ (by norm_num))
theorem R221309 : Reach 221309 := rs (se 3 (by rfl) ⟨41495, by rfl⟩) (B 82991 (by norm_num) ⟨41495, by rfl⟩ (by norm_num))
theorem R123049 : Reach 123049 := rs (se 2 (by rfl) ⟨46143, by rfl⟩) (B 92287 (by norm_num) ⟨46143, by rfl⟩ (by norm_num))
theorem R123077 : Reach 123077 := rs (se 4 (by rfl) ⟨11538, by rfl⟩) (B 23077 (by norm_num) ⟨11538, by rfl⟩ (by norm_num))
theorem R221381 : Reach 221381 := rs (se 4 (by rfl) ⟨20754, by rfl⟩) (B 41509 (by norm_num) ⟨20754, by rfl⟩ (by norm_num))
theorem R221453 : Reach 221453 := rs (se 3 (by rfl) ⟨41522, by rfl⟩) (B 83045 (by norm_num) ⟨41522, by rfl⟩ (by norm_num))
theorem R123221 : Reach 123221 := rs (se 10 (by rfl) ⟨180, by rfl⟩) (B 361 (by norm_num) ⟨180, by rfl⟩ (by norm_num))
theorem R221525 : Reach 221525 := rs (se 10 (by rfl) ⟨324, by rfl⟩) (B 649 (by norm_num) ⟨324, by rfl⟩ (by norm_num))
theorem R123277 : Reach 123277 := rs (se 3 (by rfl) ⟨23114, by rfl⟩) (B 46229 (by norm_num) ⟨23114, by rfl⟩ (by norm_num))
theorem R221597 : Reach 221597 := rs (se 3 (by rfl) ⟨41549, by rfl⟩) (B 83099 (by norm_num) ⟨41549, by rfl⟩ (by norm_num))
theorem R549301 : Reach 549301 := rs (se 5 (by rfl) ⟨25748, by rfl⟩) (B 51497 (by norm_num) ⟨25748, by rfl⟩ (by norm_num))
theorem R778709 : Reach 778709 := rs (se 7 (by rfl) ⟨9125, by rfl⟩) (B 18251 (by norm_num) ⟨9125, by rfl⟩ (by norm_num))
theorem R221669 : Reach 221669 := rs (se 4 (by rfl) ⟨20781, by rfl⟩) (B 41563 (by norm_num) ⟨20781, by rfl⟩ (by norm_num))
theorem R123373 : Reach 123373 := rs (se 3 (by rfl) ⟨23132, by rfl⟩) (B 46265 (by norm_num) ⟨23132, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R221741 : Reach 221741 := rs (se 3 (by rfl) ⟨41576, by rfl⟩) (B 83153 (by norm_num) ⟨41576, by rfl⟩ (by norm_num))
theorem R483893 : Reach 483893 := rs (se 5 (by rfl) ⟨22682, by rfl⟩) (B 45365 (by norm_num) ⟨22682, by rfl⟩ (by norm_num))
theorem R221813 : Reach 221813 := rs (se 5 (by rfl) ⟨10397, by rfl⟩) (B 20795 (by norm_num) ⟨10397, by rfl⟩ (by norm_num))
theorem R123545 : Reach 123545 := rs (se 2 (by rfl) ⟨46329, by rfl⟩) (B 92659 (by norm_num) ⟨46329, by rfl⟩ (by norm_num))
theorem R221885 : Reach 221885 := rs (se 3 (by rfl) ⟨41603, by rfl⟩) (B 83207 (by norm_num) ⟨41603, by rfl⟩ (by norm_num))
theorem R123601 : Reach 123601 := rs (se 2 (by rfl) ⟨46350, by rfl⟩) (B 92701 (by norm_num) ⟨46350, by rfl⟩ (by norm_num))
theorem R320213 : Reach 320213 := rs (se 7 (by rfl) ⟨3752, by rfl⟩) (B 7505 (by norm_num) ⟨3752, by rfl⟩ (by norm_num))
theorem R221957 : Reach 221957 := rs (se 4 (by rfl) ⟨20808, by rfl⟩) (B 41617 (by norm_num) ⟨20808, by rfl⟩ (by norm_num))
theorem R123697 : Reach 123697 := rs (se 2 (by rfl) ⟨46386, by rfl⟩) (B 92773 (by norm_num) ⟨46386, by rfl⟩ (by norm_num))
theorem R156485 : Reach 156485 := rs (se 4 (by rfl) ⟨14670, by rfl⟩) (B 29341 (by norm_num) ⟨14670, by rfl⟩ (by norm_num))
theorem R222029 : Reach 222029 := rs (se 3 (by rfl) ⟨41630, by rfl⟩) (B 83261 (by norm_num) ⟨41630, by rfl⟩ (by norm_num))
theorem R418709 : Reach 418709 := rs (se 6 (by rfl) ⟨9813, by rfl⟩) (B 19627 (by norm_num) ⟨9813, by rfl⟩ (by norm_num))
theorem R222101 : Reach 222101 := rs (se 6 (by rfl) ⟨5205, by rfl⟩) (B 10411 (by norm_num) ⟨5205, by rfl⟩ (by norm_num))
theorem R123869 : Reach 123869 := rs (se 3 (by rfl) ⟨23225, by rfl⟩) (B 46451 (by norm_num) ⟨23225, by rfl⟩ (by norm_num))
theorem R222173 : Reach 222173 := rs (se 3 (by rfl) ⟨41657, by rfl⟩) (B 83315 (by norm_num) ⟨41657, by rfl⟩ (by norm_num))
theorem R123925 : Reach 123925 := rs (se 6 (by rfl) ⟨2904, by rfl⟩) (B 5809 (by norm_num) ⟨2904, by rfl⟩ (by norm_num))
theorem R222245 : Reach 222245 := rs (se 4 (by rfl) ⟨20835, by rfl⟩) (B 41671 (by norm_num) ⟨20835, by rfl⟩ (by norm_num))
theorem R123961 : Reach 123961 := rs (se 2 (by rfl) ⟨46485, by rfl⟩) (B 92971 (by norm_num) ⟨46485, by rfl⟩ (by norm_num))
theorem R222317 : Reach 222317 := rs (se 3 (by rfl) ⟨41684, by rfl⟩) (B 83369 (by norm_num) ⟨41684, by rfl⟩ (by norm_num))
theorem R124021 : Reach 124021 := rs (se 5 (by rfl) ⟨5813, by rfl⟩) (B 11627 (by norm_num) ⟨5813, by rfl⟩ (by norm_num))
theorem R222389 : Reach 222389 := rs (se 5 (by rfl) ⟨10424, by rfl⟩) (B 20849 (by norm_num) ⟨10424, by rfl⟩ (by norm_num))
theorem R222461 : Reach 222461 := rs (se 3 (by rfl) ⟨41711, by rfl⟩) (B 83423 (by norm_num) ⟨41711, by rfl⟩ (by norm_num))
theorem R124193 : Reach 124193 := rs (se 2 (by rfl) ⟨46572, by rfl⟩) (B 93145 (by norm_num) ⟨46572, by rfl⟩ (by norm_num))
theorem R222533 : Reach 222533 := rs (se 4 (by rfl) ⟨20862, by rfl⟩) (B 41725 (by norm_num) ⟨20862, by rfl⟩ (by norm_num))
theorem R124249 : Reach 124249 := rs (se 2 (by rfl) ⟨46593, by rfl⟩) (B 93187 (by norm_num) ⟨46593, by rfl⟩ (by norm_num))
theorem R222605 : Reach 222605 := rs (se 3 (by rfl) ⟨41738, by rfl⟩) (B 83477 (by norm_num) ⟨41738, by rfl⟩ (by norm_num))
theorem R124345 : Reach 124345 := rs (se 2 (by rfl) ⟨46629, by rfl⟩) (B 93259 (by norm_num) ⟨46629, by rfl⟩ (by norm_num))
theorem R222677 : Reach 222677 := rs (se 7 (by rfl) ⟨2609, by rfl⟩) (B 5219 (by norm_num) ⟨2609, by rfl⟩ (by norm_num))
theorem R157157 : Reach 157157 := rs (se 4 (by rfl) ⟨14733, by rfl⟩) (B 29467 (by norm_num) ⟨14733, by rfl⟩ (by norm_num))
theorem R386549 : Reach 386549 := rs (se 5 (by rfl) ⟨18119, by rfl⟩) (B 36239 (by norm_num) ⟨18119, by rfl⟩ (by norm_num))
theorem R222749 : Reach 222749 := rs (se 3 (by rfl) ⟨41765, by rfl⟩) (B 83531 (by norm_num) ⟨41765, by rfl⟩ (by norm_num))
theorem R124517 : Reach 124517 := rs (se 4 (by rfl) ⟨11673, by rfl⟩) (B 23347 (by norm_num) ⟨11673, by rfl⟩ (by norm_num))
theorem R222821 : Reach 222821 := rs (se 4 (by rfl) ⟨20889, by rfl⟩) (B 41779 (by norm_num) ⟨20889, by rfl⟩ (by norm_num))
theorem R124573 : Reach 124573 := rs (se 3 (by rfl) ⟨23357, by rfl⟩) (B 46715 (by norm_num) ⟨23357, by rfl⟩ (by norm_num))
theorem R222893 : Reach 222893 := rs (se 3 (by rfl) ⟨41792, by rfl⟩) (B 83585 (by norm_num) ⟨41792, by rfl⟩ (by norm_num))
theorem R222965 : Reach 222965 := rs (se 5 (by rfl) ⟨10451, by rfl⟩) (B 20903 (by norm_num) ⟨10451, by rfl⟩ (by norm_num))
theorem R124669 : Reach 124669 := rs (se 3 (by rfl) ⟨23375, by rfl⟩) (B 46751 (by norm_num) ⟨23375, by rfl⟩ (by norm_num))
theorem R223037 : Reach 223037 := rs (se 3 (by rfl) ⟨41819, by rfl⟩) (B 83639 (by norm_num) ⟨41819, by rfl⟩ (by norm_num))
theorem R485189 : Reach 485189 := rs (se 4 (by rfl) ⟨45486, by rfl⟩) (B 90973 (by norm_num) ⟨45486, by rfl⟩ (by norm_num))
theorem R419717 : Reach 419717 := rs (se 4 (by rfl) ⟨39348, by rfl⟩) (B 78697 (by norm_num) ⟨39348, by rfl⟩ (by norm_num))
theorem R124841 : Reach 124841 := rs (se 2 (by rfl) ⟨46815, by rfl⟩) (B 93631 (by norm_num) ⟨46815, by rfl⟩ (by norm_num))
theorem R321461 : Reach 321461 := rs (se 5 (by rfl) ⟨15068, by rfl⟩) (B 30137 (by norm_num) ⟨15068, by rfl⟩ (by norm_num))
theorem R124897 : Reach 124897 := rs (se 2 (by rfl) ⟨46836, by rfl⟩) (B 93673 (by norm_num) ⟨46836, by rfl⟩ (by norm_num))
theorem R157669 : Reach 157669 := rs (se 4 (by rfl) ⟨14781, by rfl⟩) (B 29563 (by norm_num) ⟨14781, by rfl⟩ (by norm_num))
theorem R124993 : Reach 124993 := rs (se 2 (by rfl) ⟨46872, by rfl⟩) (B 93745 (by norm_num) ⟨46872, by rfl⟩ (by norm_num))
theorem R354469 : Reach 354469 := rs (se 4 (by rfl) ⟨33231, by rfl⟩) (B 66463 (by norm_num) ⟨33231, by rfl⟩ (by norm_num))
theorem R125165 : Reach 125165 := rs (se 3 (by rfl) ⟨23468, by rfl⟩) (B 46937 (by norm_num) ⟨23468, by rfl⟩ (by norm_num))
theorem R125221 : Reach 125221 := rs (se 4 (by rfl) ⟨11739, by rfl⟩) (B 23479 (by norm_num) ⟨11739, by rfl⟩ (by norm_num))
theorem R321893 : Reach 321893 := rs (se 4 (by rfl) ⟨30177, by rfl⟩) (B 60355 (by norm_num) ⟨30177, by rfl⟩ (by norm_num))
theorem R551285 : Reach 551285 := rs (se 5 (by rfl) ⟨25841, by rfl⟩) (B 51683 (by norm_num) ⟨25841, by rfl⟩ (by norm_num))
theorem R125317 : Reach 125317 := rs (se 4 (by rfl) ⟨11748, by rfl⟩) (B 23497 (by norm_num) ⟨11748, by rfl⟩ (by norm_num))
theorem R158125 : Reach 158125 := rs (se 3 (by rfl) ⟨29648, by rfl⟩) (B 59297 (by norm_num) ⟨29648, by rfl⟩ (by norm_num))
theorem R322325 : Reach 322325 := rs (se 6 (by rfl) ⟨7554, by rfl⟩) (B 15109 (by norm_num) ⟨7554, by rfl⟩ (by norm_num))
theorem R125725 : Reach 125725 := rs (se 3 (by rfl) ⟨23573, by rfl⟩) (B 47147 (by norm_num) ⟨23573, by rfl⟩ (by norm_num))
theorem R191333 : Reach 191333 := rs (se 4 (by rfl) ⟨17937, by rfl⟩) (B 35875 (by norm_num) ⟨17937, by rfl⟩ (by norm_num))
theorem R355205 : Reach 355205 := rs (se 4 (by rfl) ⟨33300, by rfl⟩) (B 66601 (by norm_num) ⟨33300, by rfl⟩ (by norm_num))
theorem R486485 : Reach 486485 := rs (se 8 (by rfl) ⟨2850, by rfl⟩) (B 5701 (by norm_num) ⟨2850, by rfl⟩ (by norm_num))
theorem R322757 : Reach 322757 := rs (se 4 (by rfl) ⟨30258, by rfl⟩) (B 60517 (by norm_num) ⟨30258, by rfl⟩ (by norm_num))
theorem R617813 : Reach 617813 := rs (se 11 (by rfl) ⟨452, by rfl⟩) (B 905 (by norm_num) ⟨452, by rfl⟩ (by norm_num))
theorem R159197 : Reach 159197 := rs (se 3 (by rfl) ⟨29849, by rfl⟩) (B 59699 (by norm_num) ⟨29849, by rfl⟩ (by norm_num))
theorem R355909 : Reach 355909 := rs (se 4 (by rfl) ⟨33366, by rfl⟩) (B 66733 (by norm_num) ⟨33366, by rfl⟩ (by norm_num))
theorem R323189 : Reach 323189 := rs (se 5 (by rfl) ⟨15149, by rfl⟩) (B 30299 (by norm_num) ⟨15149, by rfl⟩ (by norm_num))
theorem R716597 : Reach 716597 := rs (se 5 (by rfl) ⟨33590, by rfl⟩) (B 67181 (by norm_num) ⟨33590, by rfl⟩ (by norm_num))
theorem R323621 : Reach 323621 := rs (se 4 (by rfl) ⟨30339, by rfl⟩) (B 60679 (by norm_num) ⟨30339, by rfl⟩ (by norm_num))
theorem R127045 : Reach 127045 := rs (se 4 (by rfl) ⟨11910, by rfl⟩) (B 23821 (by norm_num) ⟨11910, by rfl⟩ (by norm_num))
theorem R487781 : Reach 487781 := rs (se 4 (by rfl) ⟨45729, by rfl⟩) (B 91459 (by norm_num) ⟨45729, by rfl⟩ (by norm_num))
theorem R324053 : Reach 324053 := rs (se 7 (by rfl) ⟨3797, by rfl⟩) (B 7595 (by norm_num) ⟨3797, by rfl⟩ (by norm_num))
theorem R553493 : Reach 553493 := rs (se 6 (by rfl) ⟨12972, by rfl⟩) (B 25945 (by norm_num) ⟨12972, by rfl⟩ (by norm_num))
theorem R848501 : Reach 848501 := rs (se 5 (by rfl) ⟨39773, by rfl⟩) (B 79547 (by norm_num) ⟨39773, by rfl⟩ (by norm_num))
theorem R127637 : Reach 127637 := rs (se 6 (by rfl) ⟨2991, by rfl⟩) (B 5983 (by norm_num) ⟨2991, by rfl⟩ (by norm_num))
theorem R291541 : Reach 291541 := rs (se 7 (by rfl) ⟨3416, by rfl⟩) (B 6833 (by norm_num) ⟨3416, by rfl⟩ (by norm_num))
theorem R160589 : Reach 160589 := rs (se 3 (by rfl) ⟨30110, by rfl⟩) (B 60221 (by norm_num) ⟨30110, by rfl⟩ (by norm_num))
theorem R324485 : Reach 324485 := rs (se 4 (by rfl) ⟨30420, by rfl⟩) (B 60841 (by norm_num) ⟨30420, by rfl⟩ (by norm_num))
theorem R95133 : Reach 95133 := rs (se 3 (by rfl) ⟨17837, by rfl⟩) (B 35675 (by norm_num) ⟨17837, by rfl⟩ (by norm_num))
theorem R95137 : Reach 95137 := rs (se 2 (by rfl) ⟨35676, by rfl⟩) (B 71353 (by norm_num) ⟨35676, by rfl⟩ (by norm_num))
theorem R95141 : Reach 95141 := rs (se 4 (by rfl) ⟨8919, by rfl⟩) (B 17839 (by norm_num) ⟨8919, by rfl⟩ (by norm_num))
theorem R95145 : Reach 95145 := rs (se 2 (by rfl) ⟨35679, by rfl⟩) (B 71359 (by norm_num) ⟨35679, by rfl⟩ (by norm_num))
theorem R95149 : Reach 95149 := rs (se 3 (by rfl) ⟨17840, by rfl⟩) (B 35681 (by norm_num) ⟨17840, by rfl⟩ (by norm_num))
theorem R95153 : Reach 95153 := rs (se 2 (by rfl) ⟨35682, by rfl⟩) (B 71365 (by norm_num) ⟨35682, by rfl⟩ (by norm_num))
theorem R95157 : Reach 95157 := rs (se 5 (by rfl) ⟨4460, by rfl⟩) (B 8921 (by norm_num) ⟨4460, by rfl⟩ (by norm_num))
theorem R95161 : Reach 95161 := rs (se 2 (by rfl) ⟨35685, by rfl⟩) (B 71371 (by norm_num) ⟨35685, by rfl⟩ (by norm_num))
theorem R95165 : Reach 95165 := rs (se 3 (by rfl) ⟨17843, by rfl⟩) (B 35687 (by norm_num) ⟨17843, by rfl⟩ (by norm_num))
theorem R95169 : Reach 95169 := rs (se 2 (by rfl) ⟨35688, by rfl⟩) (B 71377 (by norm_num) ⟨35688, by rfl⟩ (by norm_num))
theorem R95173 : Reach 95173 := rs (se 4 (by rfl) ⟨8922, by rfl⟩) (B 17845 (by norm_num) ⟨8922, by rfl⟩ (by norm_num))
theorem R95177 : Reach 95177 := rs (se 2 (by rfl) ⟨35691, by rfl⟩) (B 71383 (by norm_num) ⟨35691, by rfl⟩ (by norm_num))
theorem R95181 : Reach 95181 := rs (se 3 (by rfl) ⟨17846, by rfl⟩) (B 35693 (by norm_num) ⟨17846, by rfl⟩ (by norm_num))
theorem R160717 : Reach 160717 := rs (se 3 (by rfl) ⟨30134, by rfl⟩) (B 60269 (by norm_num) ⟨30134, by rfl⟩ (by norm_num))
theorem R95185 : Reach 95185 := rs (se 2 (by rfl) ⟨35694, by rfl⟩) (B 71389 (by norm_num) ⟨35694, by rfl⟩ (by norm_num))
theorem R95189 : Reach 95189 := rs (se 7 (by rfl) ⟨1115, by rfl⟩) (B 2231 (by norm_num) ⟨1115, by rfl⟩ (by norm_num))
theorem R95193 : Reach 95193 := rs (se 2 (by rfl) ⟨35697, by rfl⟩) (B 71395 (by norm_num) ⟨35697, by rfl⟩ (by norm_num))
theorem R95197 : Reach 95197 := rs (se 3 (by rfl) ⟨17849, by rfl⟩) (B 35699 (by norm_num) ⟨17849, by rfl⟩ (by norm_num))
theorem R95201 : Reach 95201 := rs (se 2 (by rfl) ⟨35700, by rfl⟩) (B 71401 (by norm_num) ⟨35700, by rfl⟩ (by norm_num))
theorem R95205 : Reach 95205 := rs (se 4 (by rfl) ⟨8925, by rfl⟩) (B 17851 (by norm_num) ⟨8925, by rfl⟩ (by norm_num))
theorem R95209 : Reach 95209 := rs (se 2 (by rfl) ⟨35703, by rfl⟩) (B 71407 (by norm_num) ⟨35703, by rfl⟩ (by norm_num))
theorem R95213 : Reach 95213 := rs (se 3 (by rfl) ⟨17852, by rfl⟩) (B 35705 (by norm_num) ⟨17852, by rfl⟩ (by norm_num))
theorem R95217 : Reach 95217 := rs (se 2 (by rfl) ⟨35706, by rfl⟩) (B 71413 (by norm_num) ⟨35706, by rfl⟩ (by norm_num))
theorem R95221 : Reach 95221 := rs (se 5 (by rfl) ⟨4463, by rfl⟩) (B 8927 (by norm_num) ⟨4463, by rfl⟩ (by norm_num))
theorem R95225 : Reach 95225 := rs (se 2 (by rfl) ⟨35709, by rfl⟩) (B 71419 (by norm_num) ⟨35709, by rfl⟩ (by norm_num))
theorem R95229 : Reach 95229 := rs (se 3 (by rfl) ⟨17855, by rfl⟩) (B 35711 (by norm_num) ⟨17855, by rfl⟩ (by norm_num))
theorem R95233 : Reach 95233 := rs (se 2 (by rfl) ⟨35712, by rfl⟩) (B 71425 (by norm_num) ⟨35712, by rfl⟩ (by norm_num))
theorem R95237 : Reach 95237 := rs (se 4 (by rfl) ⟨8928, by rfl⟩) (B 17857 (by norm_num) ⟨8928, by rfl⟩ (by norm_num))
theorem R95241 : Reach 95241 := rs (se 2 (by rfl) ⟨35715, by rfl⟩) (B 71431 (by norm_num) ⟨35715, by rfl⟩ (by norm_num))
theorem R95245 : Reach 95245 := rs (se 3 (by rfl) ⟨17858, by rfl⟩) (B 35717 (by norm_num) ⟨17858, by rfl⟩ (by norm_num))
theorem R95249 : Reach 95249 := rs (se 2 (by rfl) ⟨35718, by rfl⟩) (B 71437 (by norm_num) ⟨35718, by rfl⟩ (by norm_num))
theorem R95253 : Reach 95253 := rs (se 6 (by rfl) ⟨2232, by rfl⟩) (B 4465 (by norm_num) ⟨2232, by rfl⟩ (by norm_num))
theorem R95257 : Reach 95257 := rs (se 2 (by rfl) ⟨35721, by rfl⟩) (B 71443 (by norm_num) ⟨35721, by rfl⟩ (by norm_num))
theorem R95261 : Reach 95261 := rs (se 3 (by rfl) ⟨17861, by rfl⟩) (B 35723 (by norm_num) ⟨17861, by rfl⟩ (by norm_num))
theorem R95265 : Reach 95265 := rs (se 2 (by rfl) ⟨35724, by rfl⟩) (B 71449 (by norm_num) ⟨35724, by rfl⟩ (by norm_num))
theorem R95269 : Reach 95269 := rs (se 4 (by rfl) ⟨8931, by rfl⟩) (B 17863 (by norm_num) ⟨8931, by rfl⟩ (by norm_num))
theorem R160805 : Reach 160805 := rs (se 4 (by rfl) ⟨15075, by rfl⟩) (B 30151 (by norm_num) ⟨15075, by rfl⟩ (by norm_num))
theorem R95273 : Reach 95273 := rs (se 2 (by rfl) ⟨35727, by rfl⟩) (B 71455 (by norm_num) ⟨35727, by rfl⟩ (by norm_num))
theorem R95277 : Reach 95277 := rs (se 3 (by rfl) ⟨17864, by rfl⟩) (B 35729 (by norm_num) ⟨17864, by rfl⟩ (by norm_num))
theorem R95281 : Reach 95281 := rs (se 2 (by rfl) ⟨35730, by rfl⟩) (B 71461 (by norm_num) ⟨35730, by rfl⟩ (by norm_num))
theorem R95285 : Reach 95285 := rs (se 5 (by rfl) ⟨4466, by rfl⟩) (B 8933 (by norm_num) ⟨4466, by rfl⟩ (by norm_num))
theorem R95289 : Reach 95289 := rs (se 2 (by rfl) ⟨35733, by rfl⟩) (B 71467 (by norm_num) ⟨35733, by rfl⟩ (by norm_num))
theorem R95293 : Reach 95293 := rs (se 3 (by rfl) ⟨17867, by rfl⟩) (B 35735 (by norm_num) ⟨17867, by rfl⟩ (by norm_num))
theorem R95297 : Reach 95297 := rs (se 2 (by rfl) ⟨35736, by rfl⟩) (B 71473 (by norm_num) ⟨35736, by rfl⟩ (by norm_num))
theorem R95301 : Reach 95301 := rs (se 4 (by rfl) ⟨8934, by rfl⟩) (B 17869 (by norm_num) ⟨8934, by rfl⟩ (by norm_num))
theorem R422981 : Reach 422981 := rs (se 4 (by rfl) ⟨39654, by rfl⟩) (B 79309 (by norm_num) ⟨39654, by rfl⟩ (by norm_num))
theorem R95305 : Reach 95305 := rs (se 2 (by rfl) ⟨35739, by rfl⟩) (B 71479 (by norm_num) ⟨35739, by rfl⟩ (by norm_num))
theorem R95309 : Reach 95309 := rs (se 3 (by rfl) ⟨17870, by rfl⟩) (B 35741 (by norm_num) ⟨17870, by rfl⟩ (by norm_num))
theorem R95313 : Reach 95313 := rs (se 2 (by rfl) ⟨35742, by rfl⟩) (B 71485 (by norm_num) ⟨35742, by rfl⟩ (by norm_num))
theorem R95317 : Reach 95317 := rs (se 8 (by rfl) ⟨558, by rfl⟩) (B 1117 (by norm_num) ⟨558, by rfl⟩ (by norm_num))
theorem R95321 : Reach 95321 := rs (se 2 (by rfl) ⟨35745, by rfl⟩) (B 71491 (by norm_num) ⟨35745, by rfl⟩ (by norm_num))
theorem R95325 : Reach 95325 := rs (se 3 (by rfl) ⟨17873, by rfl⟩) (B 35747 (by norm_num) ⟨17873, by rfl⟩ (by norm_num))
theorem R95329 : Reach 95329 := rs (se 2 (by rfl) ⟨35748, by rfl⟩) (B 71497 (by norm_num) ⟨35748, by rfl⟩ (by norm_num))
theorem R95333 : Reach 95333 := rs (se 4 (by rfl) ⟨8937, by rfl⟩) (B 17875 (by norm_num) ⟨8937, by rfl⟩ (by norm_num))
theorem R95337 : Reach 95337 := rs (se 2 (by rfl) ⟨35751, by rfl⟩) (B 71503 (by norm_num) ⟨35751, by rfl⟩ (by norm_num))
theorem R95341 : Reach 95341 := rs (se 3 (by rfl) ⟨17876, by rfl⟩) (B 35753 (by norm_num) ⟨17876, by rfl⟩ (by norm_num))
theorem R95345 : Reach 95345 := rs (se 2 (by rfl) ⟨35754, by rfl⟩) (B 71509 (by norm_num) ⟨35754, by rfl⟩ (by norm_num))
theorem R95349 : Reach 95349 := rs (se 5 (by rfl) ⟨4469, by rfl⟩) (B 8939 (by norm_num) ⟨4469, by rfl⟩ (by norm_num))
theorem R95353 : Reach 95353 := rs (se 2 (by rfl) ⟨35757, by rfl⟩) (B 71515 (by norm_num) ⟨35757, by rfl⟩ (by norm_num))
theorem R95357 : Reach 95357 := rs (se 3 (by rfl) ⟨17879, by rfl⟩) (B 35759 (by norm_num) ⟨17879, by rfl⟩ (by norm_num))
theorem R95361 : Reach 95361 := rs (se 2 (by rfl) ⟨35760, by rfl⟩) (B 71521 (by norm_num) ⟨35760, by rfl⟩ (by norm_num))
theorem R95365 : Reach 95365 := rs (se 4 (by rfl) ⟨8940, by rfl⟩) (B 17881 (by norm_num) ⟨8940, by rfl⟩ (by norm_num))
theorem R390277 : Reach 390277 := rs (se 4 (by rfl) ⟨36588, by rfl⟩) (B 73177 (by norm_num) ⟨36588, by rfl⟩ (by norm_num))
theorem R95369 : Reach 95369 := rs (se 2 (by rfl) ⟨35763, by rfl⟩) (B 71527 (by norm_num) ⟨35763, by rfl⟩ (by norm_num))
theorem R95373 : Reach 95373 := rs (se 3 (by rfl) ⟨17882, by rfl⟩) (B 35765 (by norm_num) ⟨17882, by rfl⟩ (by norm_num))
theorem R95377 : Reach 95377 := rs (se 2 (by rfl) ⟨35766, by rfl⟩) (B 71533 (by norm_num) ⟨35766, by rfl⟩ (by norm_num))
theorem R95381 : Reach 95381 := rs (se 6 (by rfl) ⟨2235, by rfl⟩) (B 4471 (by norm_num) ⟨2235, by rfl⟩ (by norm_num))
theorem R1766549 : Reach 1766549 := rs (se 6 (by rfl) ⟨41403, by rfl⟩) (B 82807 (by norm_num) ⟨41403, by rfl⟩ (by norm_num))
theorem R95385 : Reach 95385 := rs (se 2 (by rfl) ⟨35769, by rfl⟩) (B 71539 (by norm_num) ⟨35769, by rfl⟩ (by norm_num))
theorem R95389 : Reach 95389 := rs (se 3 (by rfl) ⟨17885, by rfl⟩) (B 35771 (by norm_num) ⟨17885, by rfl⟩ (by norm_num))
theorem R95393 : Reach 95393 := rs (se 2 (by rfl) ⟨35772, by rfl⟩) (B 71545 (by norm_num) ⟨35772, by rfl⟩ (by norm_num))
theorem R160933 : Reach 160933 := rs (se 4 (by rfl) ⟨15087, by rfl⟩) (B 30175 (by norm_num) ⟨15087, by rfl⟩ (by norm_num))
theorem R95397 : Reach 95397 := rs (se 4 (by rfl) ⟨8943, by rfl⟩) (B 17887 (by norm_num) ⟨8943, by rfl⟩ (by norm_num))
theorem R95401 : Reach 95401 := rs (se 2 (by rfl) ⟨35775, by rfl⟩) (B 71551 (by norm_num) ⟨35775, by rfl⟩ (by norm_num))
theorem R95405 : Reach 95405 := rs (se 3 (by rfl) ⟨17888, by rfl⟩) (B 35777 (by norm_num) ⟨17888, by rfl⟩ (by norm_num))
theorem R95409 : Reach 95409 := rs (se 2 (by rfl) ⟨35778, by rfl⟩) (B 71557 (by norm_num) ⟨35778, by rfl⟩ (by norm_num))
theorem R95413 : Reach 95413 := rs (se 5 (by rfl) ⟨4472, by rfl⟩) (B 8945 (by norm_num) ⟨4472, by rfl⟩ (by norm_num))
theorem R95417 : Reach 95417 := rs (se 2 (by rfl) ⟨35781, by rfl⟩) (B 71563 (by norm_num) ⟨35781, by rfl⟩ (by norm_num))
theorem R95421 : Reach 95421 := rs (se 3 (by rfl) ⟨17891, by rfl⟩) (B 35783 (by norm_num) ⟨17891, by rfl⟩ (by norm_num))
theorem R95425 : Reach 95425 := rs (se 2 (by rfl) ⟨35784, by rfl⟩) (B 71569 (by norm_num) ⟨35784, by rfl⟩ (by norm_num))
theorem R95429 : Reach 95429 := rs (se 4 (by rfl) ⟨8946, by rfl⟩) (B 17893 (by norm_num) ⟨8946, by rfl⟩ (by norm_num))
theorem R95433 : Reach 95433 := rs (se 2 (by rfl) ⟨35787, by rfl⟩) (B 71575 (by norm_num) ⟨35787, by rfl⟩ (by norm_num))
theorem R95437 : Reach 95437 := rs (se 3 (by rfl) ⟨17894, by rfl⟩) (B 35789 (by norm_num) ⟨17894, by rfl⟩ (by norm_num))
theorem R95441 : Reach 95441 := rs (se 2 (by rfl) ⟨35790, by rfl⟩) (B 71581 (by norm_num) ⟨35790, by rfl⟩ (by norm_num))
theorem R914645 : Reach 914645 := rs (se 7 (by rfl) ⟨10718, by rfl⟩) (B 21437 (by norm_num) ⟨10718, by rfl⟩ (by norm_num))
theorem R95445 : Reach 95445 := rs (se 7 (by rfl) ⟨1118, by rfl⟩) (B 2237 (by norm_num) ⟨1118, by rfl⟩ (by norm_num))
theorem R95449 : Reach 95449 := rs (se 2 (by rfl) ⟨35793, by rfl⟩) (B 71587 (by norm_num) ⟨35793, by rfl⟩ (by norm_num))
theorem R95453 : Reach 95453 := rs (se 3 (by rfl) ⟨17897, by rfl⟩) (B 35795 (by norm_num) ⟨17897, by rfl⟩ (by norm_num))
theorem R95457 : Reach 95457 := rs (se 2 (by rfl) ⟨35796, by rfl⟩) (B 71593 (by norm_num) ⟨35796, by rfl⟩ (by norm_num))
theorem R95461 : Reach 95461 := rs (se 4 (by rfl) ⟨8949, by rfl⟩) (B 17899 (by norm_num) ⟨8949, by rfl⟩ (by norm_num))
theorem R95465 : Reach 95465 := rs (se 2 (by rfl) ⟨35799, by rfl⟩) (B 71599 (by norm_num) ⟨35799, by rfl⟩ (by norm_num))
theorem R95469 : Reach 95469 := rs (se 3 (by rfl) ⟨17900, by rfl⟩) (B 35801 (by norm_num) ⟨17900, by rfl⟩ (by norm_num))
theorem R95473 : Reach 95473 := rs (se 2 (by rfl) ⟨35802, by rfl⟩) (B 71605 (by norm_num) ⟨35802, by rfl⟩ (by norm_num))
theorem R95477 : Reach 95477 := rs (se 5 (by rfl) ⟨4475, by rfl⟩) (B 8951 (by norm_num) ⟨4475, by rfl⟩ (by norm_num))
theorem R95481 : Reach 95481 := rs (se 2 (by rfl) ⟨35805, by rfl⟩) (B 71611 (by norm_num) ⟨35805, by rfl⟩ (by norm_num))
theorem R161021 : Reach 161021 := rs (se 3 (by rfl) ⟨30191, by rfl⟩) (B 60383 (by norm_num) ⟨30191, by rfl⟩ (by norm_num))
theorem R95485 : Reach 95485 := rs (se 3 (by rfl) ⟨17903, by rfl⟩) (B 35807 (by norm_num) ⟨17903, by rfl⟩ (by norm_num))
theorem R95489 : Reach 95489 := rs (se 2 (by rfl) ⟨35808, by rfl⟩) (B 71617 (by norm_num) ⟨35808, by rfl⟩ (by norm_num))
theorem R95493 : Reach 95493 := rs (se 4 (by rfl) ⟨8952, by rfl⟩) (B 17905 (by norm_num) ⟨8952, by rfl⟩ (by norm_num))
theorem R95497 : Reach 95497 := rs (se 2 (by rfl) ⟨35811, by rfl⟩) (B 71623 (by norm_num) ⟨35811, by rfl⟩ (by norm_num))
theorem R95501 : Reach 95501 := rs (se 3 (by rfl) ⟨17906, by rfl⟩) (B 35813 (by norm_num) ⟨17906, by rfl⟩ (by norm_num))
theorem R95505 : Reach 95505 := rs (se 2 (by rfl) ⟨35814, by rfl⟩) (B 71629 (by norm_num) ⟨35814, by rfl⟩ (by norm_num))
theorem R95509 : Reach 95509 := rs (se 6 (by rfl) ⟨2238, by rfl⟩) (B 4477 (by norm_num) ⟨2238, by rfl⟩ (by norm_num))
theorem R750869 : Reach 750869 := rs (se 6 (by rfl) ⟨17598, by rfl⟩) (B 35197 (by norm_num) ⟨17598, by rfl⟩ (by norm_num))
theorem R95513 : Reach 95513 := rs (se 2 (by rfl) ⟨35817, by rfl⟩) (B 71635 (by norm_num) ⟨35817, by rfl⟩ (by norm_num))
theorem R95517 : Reach 95517 := rs (se 3 (by rfl) ⟨17909, by rfl⟩) (B 35819 (by norm_num) ⟨17909, by rfl⟩ (by norm_num))
theorem R95521 : Reach 95521 := rs (se 2 (by rfl) ⟨35820, by rfl⟩) (B 71641 (by norm_num) ⟨35820, by rfl⟩ (by norm_num))
theorem R95525 : Reach 95525 := rs (se 4 (by rfl) ⟨8955, by rfl⟩) (B 17911 (by norm_num) ⟨8955, by rfl⟩ (by norm_num))
theorem R95529 : Reach 95529 := rs (se 2 (by rfl) ⟨35823, by rfl⟩) (B 71647 (by norm_num) ⟨35823, by rfl⟩ (by norm_num))
theorem R95533 : Reach 95533 := rs (se 3 (by rfl) ⟨17912, by rfl⟩) (B 35825 (by norm_num) ⟨17912, by rfl⟩ (by norm_num))
theorem R95537 : Reach 95537 := rs (se 2 (by rfl) ⟨35826, by rfl⟩) (B 71653 (by norm_num) ⟨35826, by rfl⟩ (by norm_num))
theorem R95541 : Reach 95541 := rs (se 5 (by rfl) ⟨4478, by rfl⟩) (B 8957 (by norm_num) ⟨4478, by rfl⟩ (by norm_num))
theorem R324917 : Reach 324917 := rs (se 5 (by rfl) ⟨15230, by rfl⟩) (B 30461 (by norm_num) ⟨15230, by rfl⟩ (by norm_num))
theorem R95545 : Reach 95545 := rs (se 2 (by rfl) ⟨35829, by rfl⟩) (B 71659 (by norm_num) ⟨35829, by rfl⟩ (by norm_num))
theorem R95549 : Reach 95549 := rs (se 3 (by rfl) ⟨17915, by rfl⟩) (B 35831 (by norm_num) ⟨17915, by rfl⟩ (by norm_num))
theorem R95553 : Reach 95553 := rs (se 2 (by rfl) ⟨35832, by rfl⟩) (B 71665 (by norm_num) ⟨35832, by rfl⟩ (by norm_num))
theorem R95557 : Reach 95557 := rs (se 4 (by rfl) ⟨8958, by rfl⟩) (B 17917 (by norm_num) ⟨8958, by rfl⟩ (by norm_num))
theorem R95561 : Reach 95561 := rs (se 2 (by rfl) ⟨35835, by rfl⟩) (B 71671 (by norm_num) ⟨35835, by rfl⟩ (by norm_num))
theorem R95565 : Reach 95565 := rs (se 3 (by rfl) ⟨17918, by rfl⟩) (B 35837 (by norm_num) ⟨17918, by rfl⟩ (by norm_num))
theorem R95569 : Reach 95569 := rs (se 2 (by rfl) ⟨35838, by rfl⟩) (B 71677 (by norm_num) ⟨35838, by rfl⟩ (by norm_num))
theorem R95573 : Reach 95573 := rs (se 13 (by rfl) ⟨17, by rfl⟩) (B 35 (by norm_num) ⟨17, by rfl⟩ (by norm_num))
theorem R95577 : Reach 95577 := rs (se 2 (by rfl) ⟨35841, by rfl⟩) (B 71683 (by norm_num) ⟨35841, by rfl⟩ (by norm_num))
theorem R95581 : Reach 95581 := rs (se 3 (by rfl) ⟨17921, by rfl⟩) (B 35843 (by norm_num) ⟨17921, by rfl⟩ (by norm_num))
theorem R95585 : Reach 95585 := rs (se 2 (by rfl) ⟨35844, by rfl⟩) (B 71689 (by norm_num) ⟨35844, by rfl⟩ (by norm_num))
theorem R95589 : Reach 95589 := rs (se 4 (by rfl) ⟨8961, by rfl⟩) (B 17923 (by norm_num) ⟨8961, by rfl⟩ (by norm_num))
theorem R95593 : Reach 95593 := rs (se 2 (by rfl) ⟨35847, by rfl⟩) (B 71695 (by norm_num) ⟨35847, by rfl⟩ (by norm_num))
theorem R95597 : Reach 95597 := rs (se 3 (by rfl) ⟨17924, by rfl⟩) (B 35849 (by norm_num) ⟨17924, by rfl⟩ (by norm_num))
theorem R95601 : Reach 95601 := rs (se 2 (by rfl) ⟨35850, by rfl⟩) (B 71701 (by norm_num) ⟨35850, by rfl⟩ (by norm_num))
theorem R95605 : Reach 95605 := rs (se 5 (by rfl) ⟨4481, by rfl⟩) (B 8963 (by norm_num) ⟨4481, by rfl⟩ (by norm_num))
theorem R95609 : Reach 95609 := rs (se 2 (by rfl) ⟨35853, by rfl⟩) (B 71707 (by norm_num) ⟨35853, by rfl⟩ (by norm_num))
theorem R161149 : Reach 161149 := rs (se 3 (by rfl) ⟨30215, by rfl⟩) (B 60431 (by norm_num) ⟨30215, by rfl⟩ (by norm_num))
theorem R95613 : Reach 95613 := rs (se 3 (by rfl) ⟨17927, by rfl⟩) (B 35855 (by norm_num) ⟨17927, by rfl⟩ (by norm_num))
theorem R95617 : Reach 95617 := rs (se 2 (by rfl) ⟨35856, by rfl⟩) (B 71713 (by norm_num) ⟨35856, by rfl⟩ (by norm_num))
theorem R95621 : Reach 95621 := rs (se 4 (by rfl) ⟨8964, by rfl⟩) (B 17929 (by norm_num) ⟨8964, by rfl⟩ (by norm_num))
theorem R95625 : Reach 95625 := rs (se 2 (by rfl) ⟨35859, by rfl⟩) (B 71719 (by norm_num) ⟨35859, by rfl⟩ (by norm_num))
theorem R95629 : Reach 95629 := rs (se 3 (by rfl) ⟨17930, by rfl⟩) (B 35861 (by norm_num) ⟨17930, by rfl⟩ (by norm_num))
theorem R95633 : Reach 95633 := rs (se 2 (by rfl) ⟨35862, by rfl⟩) (B 71725 (by norm_num) ⟨35862, by rfl⟩ (by norm_num))
theorem R95637 : Reach 95637 := rs (se 6 (by rfl) ⟨2241, by rfl⟩) (B 4483 (by norm_num) ⟨2241, by rfl⟩ (by norm_num))
theorem R95641 : Reach 95641 := rs (se 2 (by rfl) ⟨35865, by rfl⟩) (B 71731 (by norm_num) ⟨35865, by rfl⟩ (by norm_num))
theorem R95645 : Reach 95645 := rs (se 3 (by rfl) ⟨17933, by rfl⟩) (B 35867 (by norm_num) ⟨17933, by rfl⟩ (by norm_num))
theorem R95649 : Reach 95649 := rs (se 2 (by rfl) ⟨35868, by rfl⟩) (B 71737 (by norm_num) ⟨35868, by rfl⟩ (by norm_num))
theorem R95653 : Reach 95653 := rs (se 4 (by rfl) ⟨8967, by rfl⟩) (B 17935 (by norm_num) ⟨8967, by rfl⟩ (by norm_num))
theorem R95657 : Reach 95657 := rs (se 2 (by rfl) ⟨35871, by rfl⟩) (B 71743 (by norm_num) ⟨35871, by rfl⟩ (by norm_num))
theorem R95661 : Reach 95661 := rs (se 3 (by rfl) ⟨17936, by rfl⟩) (B 35873 (by norm_num) ⟨17936, by rfl⟩ (by norm_num))
theorem R95665 : Reach 95665 := rs (se 2 (by rfl) ⟨35874, by rfl⟩) (B 71749 (by norm_num) ⟨35874, by rfl⟩ (by norm_num))
theorem R95669 : Reach 95669 := rs (se 5 (by rfl) ⟨4484, by rfl⟩) (B 8969 (by norm_num) ⟨4484, by rfl⟩ (by norm_num))
theorem R95673 : Reach 95673 := rs (se 2 (by rfl) ⟨35877, by rfl⟩) (B 71755 (by norm_num) ⟨35877, by rfl⟩ (by norm_num))
theorem R95677 : Reach 95677 := rs (se 3 (by rfl) ⟨17939, by rfl⟩) (B 35879 (by norm_num) ⟨17939, by rfl⟩ (by norm_num))
theorem R95681 : Reach 95681 := rs (se 2 (by rfl) ⟨35880, by rfl⟩) (B 71761 (by norm_num) ⟨35880, by rfl⟩ (by norm_num))
theorem R95685 : Reach 95685 := rs (se 4 (by rfl) ⟨8970, by rfl⟩) (B 17941 (by norm_num) ⟨8970, by rfl⟩ (by norm_num))
theorem R95689 : Reach 95689 := rs (se 2 (by rfl) ⟨35883, by rfl⟩) (B 71767 (by norm_num) ⟨35883, by rfl⟩ (by norm_num))
theorem R95693 : Reach 95693 := rs (se 3 (by rfl) ⟨17942, by rfl⟩) (B 35885 (by norm_num) ⟨17942, by rfl⟩ (by norm_num))
theorem R95697 : Reach 95697 := rs (se 2 (by rfl) ⟨35886, by rfl⟩) (B 71773 (by norm_num) ⟨35886, by rfl⟩ (by norm_num))
theorem R161237 : Reach 161237 := rs (se 7 (by rfl) ⟨1889, by rfl⟩) (B 3779 (by norm_num) ⟨1889, by rfl⟩ (by norm_num))
theorem R194005 : Reach 194005 := rs (se 7 (by rfl) ⟨2273, by rfl⟩) (B 4547 (by norm_num) ⟨2273, by rfl⟩ (by norm_num))
theorem R95701 : Reach 95701 := rs (se 7 (by rfl) ⟨1121, by rfl⟩) (B 2243 (by norm_num) ⟨1121, by rfl⟩ (by norm_num))
theorem R95705 : Reach 95705 := rs (se 2 (by rfl) ⟨35889, by rfl⟩) (B 71779 (by norm_num) ⟨35889, by rfl⟩ (by norm_num))
theorem R95709 : Reach 95709 := rs (se 3 (by rfl) ⟨17945, by rfl⟩) (B 35891 (by norm_num) ⟨17945, by rfl⟩ (by norm_num))
theorem R95713 : Reach 95713 := rs (se 2 (by rfl) ⟨35892, by rfl⟩) (B 71785 (by norm_num) ⟨35892, by rfl⟩ (by norm_num))
theorem R95717 : Reach 95717 := rs (se 4 (by rfl) ⟨8973, by rfl⟩) (B 17947 (by norm_num) ⟨8973, by rfl⟩ (by norm_num))
theorem R95721 : Reach 95721 := rs (se 2 (by rfl) ⟨35895, by rfl⟩) (B 71791 (by norm_num) ⟨35895, by rfl⟩ (by norm_num))
theorem R95725 : Reach 95725 := rs (se 3 (by rfl) ⟨17948, by rfl⟩) (B 35897 (by norm_num) ⟨17948, by rfl⟩ (by norm_num))
theorem R95729 : Reach 95729 := rs (se 2 (by rfl) ⟨35898, by rfl⟩) (B 71797 (by norm_num) ⟨35898, by rfl⟩ (by norm_num))
theorem R95733 : Reach 95733 := rs (se 5 (by rfl) ⟨4487, by rfl⟩) (B 8975 (by norm_num) ⟨4487, by rfl⟩ (by norm_num))
theorem R95737 : Reach 95737 := rs (se 2 (by rfl) ⟨35901, by rfl⟩) (B 71803 (by norm_num) ⟨35901, by rfl⟩ (by norm_num))
theorem R95741 : Reach 95741 := rs (se 3 (by rfl) ⟨17951, by rfl⟩) (B 35903 (by norm_num) ⟨17951, by rfl⟩ (by norm_num))
theorem R95745 : Reach 95745 := rs (se 2 (by rfl) ⟨35904, by rfl⟩) (B 71809 (by norm_num) ⟨35904, by rfl⟩ (by norm_num))
theorem R95749 : Reach 95749 := rs (se 4 (by rfl) ⟨8976, by rfl⟩) (B 17953 (by norm_num) ⟨8976, by rfl⟩ (by norm_num))
theorem R95753 : Reach 95753 := rs (se 2 (by rfl) ⟨35907, by rfl⟩) (B 71815 (by norm_num) ⟨35907, by rfl⟩ (by norm_num))
theorem R95757 : Reach 95757 := rs (se 3 (by rfl) ⟨17954, by rfl⟩) (B 35909 (by norm_num) ⟨17954, by rfl⟩ (by norm_num))
theorem R95761 : Reach 95761 := rs (se 2 (by rfl) ⟨35910, by rfl⟩) (B 71821 (by norm_num) ⟨35910, by rfl⟩ (by norm_num))
theorem R95765 : Reach 95765 := rs (se 6 (by rfl) ⟨2244, by rfl⟩) (B 4489 (by norm_num) ⟨2244, by rfl⟩ (by norm_num))
theorem R95769 : Reach 95769 := rs (se 2 (by rfl) ⟨35913, by rfl⟩) (B 71827 (by norm_num) ⟨35913, by rfl⟩ (by norm_num))
theorem R95773 : Reach 95773 := rs (se 3 (by rfl) ⟨17957, by rfl⟩) (B 35915 (by norm_num) ⟨17957, by rfl⟩ (by norm_num))
theorem R95777 : Reach 95777 := rs (se 2 (by rfl) ⟨35916, by rfl⟩) (B 71833 (by norm_num) ⟨35916, by rfl⟩ (by norm_num))
theorem R95781 : Reach 95781 := rs (se 4 (by rfl) ⟨8979, by rfl⟩) (B 17959 (by norm_num) ⟨8979, by rfl⟩ (by norm_num))
theorem R95785 : Reach 95785 := rs (se 2 (by rfl) ⟨35919, by rfl⟩) (B 71839 (by norm_num) ⟨35919, by rfl⟩ (by norm_num))
theorem R95789 : Reach 95789 := rs (se 3 (by rfl) ⟨17960, by rfl⟩) (B 35921 (by norm_num) ⟨17960, by rfl⟩ (by norm_num))
theorem R95793 : Reach 95793 := rs (se 2 (by rfl) ⟨35922, by rfl⟩) (B 71845 (by norm_num) ⟨35922, by rfl⟩ (by norm_num))
theorem R95797 : Reach 95797 := rs (se 5 (by rfl) ⟨4490, by rfl⟩) (B 8981 (by norm_num) ⟨4490, by rfl⟩ (by norm_num))
theorem R95801 : Reach 95801 := rs (se 2 (by rfl) ⟨35925, by rfl⟩) (B 71851 (by norm_num) ⟨35925, by rfl⟩ (by norm_num))
theorem R95805 : Reach 95805 := rs (se 3 (by rfl) ⟨17963, by rfl⟩) (B 35927 (by norm_num) ⟨17963, by rfl⟩ (by norm_num))
theorem R95809 : Reach 95809 := rs (se 2 (by rfl) ⟨35928, by rfl⟩) (B 71857 (by norm_num) ⟨35928, by rfl⟩ (by norm_num))
theorem R95813 : Reach 95813 := rs (se 4 (by rfl) ⟨8982, by rfl⟩) (B 17965 (by norm_num) ⟨8982, by rfl⟩ (by norm_num))
theorem R95817 : Reach 95817 := rs (se 2 (by rfl) ⟨35931, by rfl⟩) (B 71863 (by norm_num) ⟨35931, by rfl⟩ (by norm_num))
theorem R95821 : Reach 95821 := rs (se 3 (by rfl) ⟨17966, by rfl⟩) (B 35933 (by norm_num) ⟨17966, by rfl⟩ (by norm_num))
theorem R95825 : Reach 95825 := rs (se 2 (by rfl) ⟨35934, by rfl⟩) (B 71869 (by norm_num) ⟨35934, by rfl⟩ (by norm_num))
theorem R161365 : Reach 161365 := rs (se 8 (by rfl) ⟨945, by rfl⟩) (B 1891 (by norm_num) ⟨945, by rfl⟩ (by norm_num))
theorem R95829 : Reach 95829 := rs (se 8 (by rfl) ⟨561, by rfl⟩) (B 1123 (by norm_num) ⟨561, by rfl⟩ (by norm_num))
theorem R95833 : Reach 95833 := rs (se 2 (by rfl) ⟨35937, by rfl⟩) (B 71875 (by norm_num) ⟨35937, by rfl⟩ (by norm_num))
theorem R95837 : Reach 95837 := rs (se 3 (by rfl) ⟨17969, by rfl⟩) (B 35939 (by norm_num) ⟨17969, by rfl⟩ (by norm_num))
theorem R95841 : Reach 95841 := rs (se 2 (by rfl) ⟨35940, by rfl⟩) (B 71881 (by norm_num) ⟨35940, by rfl⟩ (by norm_num))
theorem R95845 : Reach 95845 := rs (se 4 (by rfl) ⟨8985, by rfl⟩) (B 17971 (by norm_num) ⟨8985, by rfl⟩ (by norm_num))
theorem R95849 : Reach 95849 := rs (se 2 (by rfl) ⟨35943, by rfl⟩) (B 71887 (by norm_num) ⟨35943, by rfl⟩ (by norm_num))
theorem R95853 : Reach 95853 := rs (se 3 (by rfl) ⟨17972, by rfl⟩) (B 35945 (by norm_num) ⟨17972, by rfl⟩ (by norm_num))
theorem R95857 : Reach 95857 := rs (se 2 (by rfl) ⟨35946, by rfl⟩) (B 71893 (by norm_num) ⟨35946, by rfl⟩ (by norm_num))
theorem R95861 : Reach 95861 := rs (se 5 (by rfl) ⟨4493, by rfl⟩) (B 8987 (by norm_num) ⟨4493, by rfl⟩ (by norm_num))
theorem R489077 : Reach 489077 := rs (se 5 (by rfl) ⟨22925, by rfl⟩) (B 45851 (by norm_num) ⟨22925, by rfl⟩ (by norm_num))
theorem R95865 : Reach 95865 := rs (se 2 (by rfl) ⟨35949, by rfl⟩) (B 71899 (by norm_num) ⟨35949, by rfl⟩ (by norm_num))
theorem R95869 : Reach 95869 := rs (se 3 (by rfl) ⟨17975, by rfl⟩) (B 35951 (by norm_num) ⟨17975, by rfl⟩ (by norm_num))
theorem R95873 : Reach 95873 := rs (se 2 (by rfl) ⟨35952, by rfl⟩) (B 71905 (by norm_num) ⟨35952, by rfl⟩ (by norm_num))
theorem R95877 : Reach 95877 := rs (se 4 (by rfl) ⟨8988, by rfl⟩) (B 17977 (by norm_num) ⟨8988, by rfl⟩ (by norm_num))
theorem R95881 : Reach 95881 := rs (se 2 (by rfl) ⟨35955, by rfl⟩) (B 71911 (by norm_num) ⟨35955, by rfl⟩ (by norm_num))
theorem R95885 : Reach 95885 := rs (se 3 (by rfl) ⟨17978, by rfl⟩) (B 35957 (by norm_num) ⟨17978, by rfl⟩ (by norm_num))
theorem R95889 : Reach 95889 := rs (se 2 (by rfl) ⟨35958, by rfl⟩) (B 71917 (by norm_num) ⟨35958, by rfl⟩ (by norm_num))
theorem R95893 : Reach 95893 := rs (se 6 (by rfl) ⟨2247, by rfl⟩) (B 4495 (by norm_num) ⟨2247, by rfl⟩ (by norm_num))
theorem R947861 : Reach 947861 := rs (se 6 (by rfl) ⟨22215, by rfl⟩) (B 44431 (by norm_num) ⟨22215, by rfl⟩ (by norm_num))
theorem R95897 : Reach 95897 := rs (se 2 (by rfl) ⟨35961, by rfl⟩) (B 71923 (by norm_num) ⟨35961, by rfl⟩ (by norm_num))
theorem R95901 : Reach 95901 := rs (se 3 (by rfl) ⟨17981, by rfl⟩) (B 35963 (by norm_num) ⟨17981, by rfl⟩ (by norm_num))
theorem R95905 : Reach 95905 := rs (se 2 (by rfl) ⟨35964, by rfl⟩) (B 71929 (by norm_num) ⟨35964, by rfl⟩ (by norm_num))
theorem R95909 : Reach 95909 := rs (se 4 (by rfl) ⟨8991, by rfl⟩) (B 17983 (by norm_num) ⟨8991, by rfl⟩ (by norm_num))
theorem R95913 : Reach 95913 := rs (se 2 (by rfl) ⟨35967, by rfl⟩) (B 71935 (by norm_num) ⟨35967, by rfl⟩ (by norm_num))
theorem R161453 : Reach 161453 := rs (se 3 (by rfl) ⟨30272, by rfl⟩) (B 60545 (by norm_num) ⟨30272, by rfl⟩ (by norm_num))
theorem R95917 : Reach 95917 := rs (se 3 (by rfl) ⟨17984, by rfl⟩) (B 35969 (by norm_num) ⟨17984, by rfl⟩ (by norm_num))
theorem R95921 : Reach 95921 := rs (se 2 (by rfl) ⟨35970, by rfl⟩) (B 71941 (by norm_num) ⟨35970, by rfl⟩ (by norm_num))
theorem R95925 : Reach 95925 := rs (se 5 (by rfl) ⟨4496, by rfl⟩) (B 8993 (by norm_num) ⟨4496, by rfl⟩ (by norm_num))
theorem R521909 : Reach 521909 := rs (se 5 (by rfl) ⟨24464, by rfl⟩) (B 48929 (by norm_num) ⟨24464, by rfl⟩ (by norm_num))
theorem R95929 : Reach 95929 := rs (se 2 (by rfl) ⟨35973, by rfl⟩) (B 71947 (by norm_num) ⟨35973, by rfl⟩ (by norm_num))
theorem R95933 : Reach 95933 := rs (se 3 (by rfl) ⟨17987, by rfl⟩) (B 35975 (by norm_num) ⟨17987, by rfl⟩ (by norm_num))
theorem R95937 : Reach 95937 := rs (se 2 (by rfl) ⟨35976, by rfl⟩) (B 71953 (by norm_num) ⟨35976, by rfl⟩ (by norm_num))
theorem R95941 : Reach 95941 := rs (se 4 (by rfl) ⟨8994, by rfl⟩) (B 17989 (by norm_num) ⟨8994, by rfl⟩ (by norm_num))
theorem R95945 : Reach 95945 := rs (se 2 (by rfl) ⟨35979, by rfl⟩) (B 71959 (by norm_num) ⟨35979, by rfl⟩ (by norm_num))
theorem R95949 : Reach 95949 := rs (se 3 (by rfl) ⟨17990, by rfl⟩) (B 35981 (by norm_num) ⟨17990, by rfl⟩ (by norm_num))
theorem R95953 : Reach 95953 := rs (se 2 (by rfl) ⟨35982, by rfl⟩) (B 71965 (by norm_num) ⟨35982, by rfl⟩ (by norm_num))
theorem R95957 : Reach 95957 := rs (se 7 (by rfl) ⟨1124, by rfl⟩) (B 2249 (by norm_num) ⟨1124, by rfl⟩ (by norm_num))
theorem R95961 : Reach 95961 := rs (se 2 (by rfl) ⟨35985, by rfl⟩) (B 71971 (by norm_num) ⟨35985, by rfl⟩ (by norm_num))
theorem R95965 : Reach 95965 := rs (se 3 (by rfl) ⟨17993, by rfl⟩) (B 35987 (by norm_num) ⟨17993, by rfl⟩ (by norm_num))
theorem R95969 : Reach 95969 := rs (se 2 (by rfl) ⟨35988, by rfl⟩) (B 71977 (by norm_num) ⟨35988, by rfl⟩ (by norm_num))
theorem R95973 : Reach 95973 := rs (se 4 (by rfl) ⟨8997, by rfl⟩) (B 17995 (by norm_num) ⟨8997, by rfl⟩ (by norm_num))
theorem R325349 : Reach 325349 := rs (se 4 (by rfl) ⟨30501, by rfl⟩) (B 61003 (by norm_num) ⟨30501, by rfl⟩ (by norm_num))
theorem R95977 : Reach 95977 := rs (se 2 (by rfl) ⟨35991, by rfl⟩) (B 71983 (by norm_num) ⟨35991, by rfl⟩ (by norm_num))
theorem R95981 : Reach 95981 := rs (se 3 (by rfl) ⟨17996, by rfl⟩) (B 35993 (by norm_num) ⟨17996, by rfl⟩ (by norm_num))
theorem R95985 : Reach 95985 := rs (se 2 (by rfl) ⟨35994, by rfl⟩) (B 71989 (by norm_num) ⟨35994, by rfl⟩ (by norm_num))
theorem R95989 : Reach 95989 := rs (se 5 (by rfl) ⟨4499, by rfl⟩) (B 8999 (by norm_num) ⟨4499, by rfl⟩ (by norm_num))
theorem R95993 : Reach 95993 := rs (se 2 (by rfl) ⟨35997, by rfl⟩) (B 71995 (by norm_num) ⟨35997, by rfl⟩ (by norm_num))
theorem R95997 : Reach 95997 := rs (se 3 (by rfl) ⟨17999, by rfl⟩) (B 35999 (by norm_num) ⟨17999, by rfl⟩ (by norm_num))
theorem R96001 : Reach 96001 := rs (se 2 (by rfl) ⟨36000, by rfl⟩) (B 72001 (by norm_num) ⟨36000, by rfl⟩ (by norm_num))
theorem R96005 : Reach 96005 := rs (se 4 (by rfl) ⟨9000, by rfl⟩) (B 18001 (by norm_num) ⟨9000, by rfl⟩ (by norm_num))
theorem R96009 : Reach 96009 := rs (se 2 (by rfl) ⟨36003, by rfl⟩) (B 72007 (by norm_num) ⟨36003, by rfl⟩ (by norm_num))
theorem R96013 : Reach 96013 := rs (se 3 (by rfl) ⟨18002, by rfl⟩) (B 36005 (by norm_num) ⟨18002, by rfl⟩ (by norm_num))
theorem R96017 : Reach 96017 := rs (se 2 (by rfl) ⟨36006, by rfl⟩) (B 72013 (by norm_num) ⟨36006, by rfl⟩ (by norm_num))
theorem R96021 : Reach 96021 := rs (se 6 (by rfl) ⟨2250, by rfl⟩) (B 4501 (by norm_num) ⟨2250, by rfl⟩ (by norm_num))
theorem R96025 : Reach 96025 := rs (se 2 (by rfl) ⟨36009, by rfl⟩) (B 72019 (by norm_num) ⟨36009, by rfl⟩ (by norm_num))
theorem R96029 : Reach 96029 := rs (se 3 (by rfl) ⟨18005, by rfl⟩) (B 36011 (by norm_num) ⟨18005, by rfl⟩ (by norm_num))
theorem R96033 : Reach 96033 := rs (se 2 (by rfl) ⟨36012, by rfl⟩) (B 72025 (by norm_num) ⟨36012, by rfl⟩ (by norm_num))
theorem R96037 : Reach 96037 := rs (se 4 (by rfl) ⟨9003, by rfl⟩) (B 18007 (by norm_num) ⟨9003, by rfl⟩ (by norm_num))
theorem R96041 : Reach 96041 := rs (se 2 (by rfl) ⟨36015, by rfl⟩) (B 72031 (by norm_num) ⟨36015, by rfl⟩ (by norm_num))
theorem R161581 : Reach 161581 := rs (se 3 (by rfl) ⟨30296, by rfl⟩) (B 60593 (by norm_num) ⟨30296, by rfl⟩ (by norm_num))
theorem R96045 : Reach 96045 := rs (se 3 (by rfl) ⟨18008, by rfl⟩) (B 36017 (by norm_num) ⟨18008, by rfl⟩ (by norm_num))
theorem R96049 : Reach 96049 := rs (se 2 (by rfl) ⟨36018, by rfl⟩) (B 72037 (by norm_num) ⟨36018, by rfl⟩ (by norm_num))
theorem R96053 : Reach 96053 := rs (se 5 (by rfl) ⟨4502, by rfl⟩) (B 9005 (by norm_num) ⟨4502, by rfl⟩ (by norm_num))
theorem R96057 : Reach 96057 := rs (se 2 (by rfl) ⟨36021, by rfl⟩) (B 72043 (by norm_num) ⟨36021, by rfl⟩ (by norm_num))
theorem R96061 : Reach 96061 := rs (se 3 (by rfl) ⟨18011, by rfl⟩) (B 36023 (by norm_num) ⟨18011, by rfl⟩ (by norm_num))
theorem R96065 : Reach 96065 := rs (se 2 (by rfl) ⟨36024, by rfl⟩) (B 72049 (by norm_num) ⟨36024, by rfl⟩ (by norm_num))
theorem R96069 : Reach 96069 := rs (se 4 (by rfl) ⟨9006, by rfl⟩) (B 18013 (by norm_num) ⟨9006, by rfl⟩ (by norm_num))
theorem R96073 : Reach 96073 := rs (se 2 (by rfl) ⟨36027, by rfl⟩) (B 72055 (by norm_num) ⟨36027, by rfl⟩ (by norm_num))
theorem R96077 : Reach 96077 := rs (se 3 (by rfl) ⟨18014, by rfl⟩) (B 36029 (by norm_num) ⟨18014, by rfl⟩ (by norm_num))
theorem R96081 : Reach 96081 := rs (se 2 (by rfl) ⟨36030, by rfl⟩) (B 72061 (by norm_num) ⟨36030, by rfl⟩ (by norm_num))
theorem R96085 : Reach 96085 := rs (se 9 (by rfl) ⟨281, by rfl⟩) (B 563 (by norm_num) ⟨281, by rfl⟩ (by norm_num))
theorem R96089 : Reach 96089 := rs (se 2 (by rfl) ⟨36033, by rfl⟩) (B 72067 (by norm_num) ⟨36033, by rfl⟩ (by norm_num))
theorem R96093 : Reach 96093 := rs (se 3 (by rfl) ⟨18017, by rfl⟩) (B 36035 (by norm_num) ⟨18017, by rfl⟩ (by norm_num))
theorem R96097 : Reach 96097 := rs (se 2 (by rfl) ⟨36036, by rfl⟩) (B 72073 (by norm_num) ⟨36036, by rfl⟩ (by norm_num))
theorem R96101 : Reach 96101 := rs (se 4 (by rfl) ⟨9009, by rfl⟩) (B 18019 (by norm_num) ⟨9009, by rfl⟩ (by norm_num))
theorem R96105 : Reach 96105 := rs (se 2 (by rfl) ⟨36039, by rfl⟩) (B 72079 (by norm_num) ⟨36039, by rfl⟩ (by norm_num))
theorem R96109 : Reach 96109 := rs (se 3 (by rfl) ⟨18020, by rfl⟩) (B 36041 (by norm_num) ⟨18020, by rfl⟩ (by norm_num))
theorem R96113 : Reach 96113 := rs (se 2 (by rfl) ⟨36042, by rfl⟩) (B 72085 (by norm_num) ⟨36042, by rfl⟩ (by norm_num))
theorem R96117 : Reach 96117 := rs (se 5 (by rfl) ⟨4505, by rfl⟩) (B 9011 (by norm_num) ⟨4505, by rfl⟩ (by norm_num))
theorem R522101 : Reach 522101 := rs (se 5 (by rfl) ⟨24473, by rfl⟩) (B 48947 (by norm_num) ⟨24473, by rfl⟩ (by norm_num))
theorem R96121 : Reach 96121 := rs (se 2 (by rfl) ⟨36045, by rfl⟩) (B 72091 (by norm_num) ⟨36045, by rfl⟩ (by norm_num))
theorem R96125 : Reach 96125 := rs (se 3 (by rfl) ⟨18023, by rfl⟩) (B 36047 (by norm_num) ⟨18023, by rfl⟩ (by norm_num))
theorem R96129 : Reach 96129 := rs (se 2 (by rfl) ⟨36048, by rfl⟩) (B 72097 (by norm_num) ⟨36048, by rfl⟩ (by norm_num))
theorem R161669 : Reach 161669 := rs (se 4 (by rfl) ⟨15156, by rfl⟩) (B 30313 (by norm_num) ⟨15156, by rfl⟩ (by norm_num))
theorem R96133 : Reach 96133 := rs (se 4 (by rfl) ⟨9012, by rfl⟩) (B 18025 (by norm_num) ⟨9012, by rfl⟩ (by norm_num))
theorem R96137 : Reach 96137 := rs (se 2 (by rfl) ⟨36051, by rfl⟩) (B 72103 (by norm_num) ⟨36051, by rfl⟩ (by norm_num))
theorem R96141 : Reach 96141 := rs (se 3 (by rfl) ⟨18026, by rfl⟩) (B 36053 (by norm_num) ⟨18026, by rfl⟩ (by norm_num))
theorem R96145 : Reach 96145 := rs (se 2 (by rfl) ⟨36054, by rfl⟩) (B 72109 (by norm_num) ⟨36054, by rfl⟩ (by norm_num))
theorem R96149 : Reach 96149 := rs (se 6 (by rfl) ⟨2253, by rfl⟩) (B 4507 (by norm_num) ⟨2253, by rfl⟩ (by norm_num))
theorem R96153 : Reach 96153 := rs (se 2 (by rfl) ⟨36057, by rfl⟩) (B 72115 (by norm_num) ⟨36057, by rfl⟩ (by norm_num))
theorem R96157 : Reach 96157 := rs (se 3 (by rfl) ⟨18029, by rfl⟩) (B 36059 (by norm_num) ⟨18029, by rfl⟩ (by norm_num))
theorem R96161 : Reach 96161 := rs (se 2 (by rfl) ⟨36060, by rfl⟩) (B 72121 (by norm_num) ⟨36060, by rfl⟩ (by norm_num))
theorem R96165 : Reach 96165 := rs (se 4 (by rfl) ⟨9015, by rfl⟩) (B 18031 (by norm_num) ⟨9015, by rfl⟩ (by norm_num))
theorem R96169 : Reach 96169 := rs (se 2 (by rfl) ⟨36063, by rfl⟩) (B 72127 (by norm_num) ⟨36063, by rfl⟩ (by norm_num))
theorem R96173 : Reach 96173 := rs (se 3 (by rfl) ⟨18032, by rfl⟩) (B 36065 (by norm_num) ⟨18032, by rfl⟩ (by norm_num))
theorem R96177 : Reach 96177 := rs (se 2 (by rfl) ⟨36066, by rfl⟩) (B 72133 (by norm_num) ⟨36066, by rfl⟩ (by norm_num))
theorem R96181 : Reach 96181 := rs (se 5 (by rfl) ⟨4508, by rfl⟩) (B 9017 (by norm_num) ⟨4508, by rfl⟩ (by norm_num))
theorem R96185 : Reach 96185 := rs (se 2 (by rfl) ⟨36069, by rfl⟩) (B 72139 (by norm_num) ⟨36069, by rfl⟩ (by norm_num))
theorem R96189 : Reach 96189 := rs (se 3 (by rfl) ⟨18035, by rfl⟩) (B 36071 (by norm_num) ⟨18035, by rfl⟩ (by norm_num))
theorem R96193 : Reach 96193 := rs (se 2 (by rfl) ⟨36072, by rfl⟩) (B 72145 (by norm_num) ⟨36072, by rfl⟩ (by norm_num))
theorem R96197 : Reach 96197 := rs (se 4 (by rfl) ⟨9018, by rfl⟩) (B 18037 (by norm_num) ⟨9018, by rfl⟩ (by norm_num))
theorem R96201 : Reach 96201 := rs (se 2 (by rfl) ⟨36075, by rfl⟩) (B 72151 (by norm_num) ⟨36075, by rfl⟩ (by norm_num))
theorem R96205 : Reach 96205 := rs (se 3 (by rfl) ⟨18038, by rfl⟩) (B 36077 (by norm_num) ⟨18038, by rfl⟩ (by norm_num))
theorem R96209 : Reach 96209 := rs (se 2 (by rfl) ⟨36078, by rfl⟩) (B 72157 (by norm_num) ⟨36078, by rfl⟩ (by norm_num))
theorem R96213 : Reach 96213 := rs (se 7 (by rfl) ⟨1127, by rfl⟩) (B 2255 (by norm_num) ⟨1127, by rfl⟩ (by norm_num))
theorem R96217 : Reach 96217 := rs (se 2 (by rfl) ⟨36081, by rfl⟩) (B 72163 (by norm_num) ⟨36081, by rfl⟩ (by norm_num))
theorem R96221 : Reach 96221 := rs (se 3 (by rfl) ⟨18041, by rfl⟩) (B 36083 (by norm_num) ⟨18041, by rfl⟩ (by norm_num))
theorem R96225 : Reach 96225 := rs (se 2 (by rfl) ⟨36084, by rfl⟩) (B 72169 (by norm_num) ⟨36084, by rfl⟩ (by norm_num))
theorem R96229 : Reach 96229 := rs (se 4 (by rfl) ⟨9021, by rfl⟩) (B 18043 (by norm_num) ⟨9021, by rfl⟩ (by norm_num))
theorem R96233 : Reach 96233 := rs (se 2 (by rfl) ⟨36087, by rfl⟩) (B 72175 (by norm_num) ⟨36087, by rfl⟩ (by norm_num))
theorem R96237 : Reach 96237 := rs (se 3 (by rfl) ⟨18044, by rfl⟩) (B 36089 (by norm_num) ⟨18044, by rfl⟩ (by norm_num))
theorem R96241 : Reach 96241 := rs (se 2 (by rfl) ⟨36090, by rfl⟩) (B 72181 (by norm_num) ⟨36090, by rfl⟩ (by norm_num))
theorem R96245 : Reach 96245 := rs (se 5 (by rfl) ⟨4511, by rfl⟩) (B 9023 (by norm_num) ⟨4511, by rfl⟩ (by norm_num))
theorem R96249 : Reach 96249 := rs (se 2 (by rfl) ⟨36093, by rfl⟩) (B 72187 (by norm_num) ⟨36093, by rfl⟩ (by norm_num))
theorem R96253 : Reach 96253 := rs (se 3 (by rfl) ⟨18047, by rfl⟩) (B 36095 (by norm_num) ⟨18047, by rfl⟩ (by norm_num))
theorem R96257 : Reach 96257 := rs (se 2 (by rfl) ⟨36096, by rfl⟩) (B 72193 (by norm_num) ⟨36096, by rfl⟩ (by norm_num))
theorem R161797 : Reach 161797 := rs (se 4 (by rfl) ⟨15168, by rfl⟩) (B 30337 (by norm_num) ⟨15168, by rfl⟩ (by norm_num))
theorem R96261 : Reach 96261 := rs (se 4 (by rfl) ⟨9024, by rfl⟩) (B 18049 (by norm_num) ⟨9024, by rfl⟩ (by norm_num))
theorem R96265 : Reach 96265 := rs (se 2 (by rfl) ⟨36099, by rfl⟩) (B 72199 (by norm_num) ⟨36099, by rfl⟩ (by norm_num))
theorem R96269 : Reach 96269 := rs (se 3 (by rfl) ⟨18050, by rfl⟩) (B 36101 (by norm_num) ⟨18050, by rfl⟩ (by norm_num))
theorem R96273 : Reach 96273 := rs (se 2 (by rfl) ⟨36102, by rfl⟩) (B 72205 (by norm_num) ⟨36102, by rfl⟩ (by norm_num))
theorem R96277 : Reach 96277 := rs (se 6 (by rfl) ⟨2256, by rfl⟩) (B 4513 (by norm_num) ⟨2256, by rfl⟩ (by norm_num))
theorem R391189 : Reach 391189 := rs (se 6 (by rfl) ⟨9168, by rfl⟩) (B 18337 (by norm_num) ⟨9168, by rfl⟩ (by norm_num))
theorem R96281 : Reach 96281 := rs (se 2 (by rfl) ⟨36105, by rfl⟩) (B 72211 (by norm_num) ⟨36105, by rfl⟩ (by norm_num))
theorem R96285 : Reach 96285 := rs (se 3 (by rfl) ⟨18053, by rfl⟩) (B 36107 (by norm_num) ⟨18053, by rfl⟩ (by norm_num))
theorem R96289 : Reach 96289 := rs (se 2 (by rfl) ⟨36108, by rfl⟩) (B 72217 (by norm_num) ⟨36108, by rfl⟩ (by norm_num))
theorem R96293 : Reach 96293 := rs (se 4 (by rfl) ⟨9027, by rfl⟩) (B 18055 (by norm_num) ⟨9027, by rfl⟩ (by norm_num))
theorem R96297 : Reach 96297 := rs (se 2 (by rfl) ⟨36111, by rfl⟩) (B 72223 (by norm_num) ⟨36111, by rfl⟩ (by norm_num))
theorem R96301 : Reach 96301 := rs (se 3 (by rfl) ⟨18056, by rfl⟩) (B 36113 (by norm_num) ⟨18056, by rfl⟩ (by norm_num))
theorem R96305 : Reach 96305 := rs (se 2 (by rfl) ⟨36114, by rfl⟩) (B 72229 (by norm_num) ⟨36114, by rfl⟩ (by norm_num))
theorem R96309 : Reach 96309 := rs (se 5 (by rfl) ⟨4514, by rfl⟩) (B 9029 (by norm_num) ⟨4514, by rfl⟩ (by norm_num))
theorem R96313 : Reach 96313 := rs (se 2 (by rfl) ⟨36117, by rfl⟩) (B 72235 (by norm_num) ⟨36117, by rfl⟩ (by norm_num))
theorem R96317 : Reach 96317 := rs (se 3 (by rfl) ⟨18059, by rfl⟩) (B 36119 (by norm_num) ⟨18059, by rfl⟩ (by norm_num))
theorem R96321 : Reach 96321 := rs (se 2 (by rfl) ⟨36120, by rfl⟩) (B 72241 (by norm_num) ⟨36120, by rfl⟩ (by norm_num))
theorem R96325 : Reach 96325 := rs (se 4 (by rfl) ⟨9030, by rfl⟩) (B 18061 (by norm_num) ⟨9030, by rfl⟩ (by norm_num))
theorem R96329 : Reach 96329 := rs (se 2 (by rfl) ⟨36123, by rfl⟩) (B 72247 (by norm_num) ⟨36123, by rfl⟩ (by norm_num))
theorem R96333 : Reach 96333 := rs (se 3 (by rfl) ⟨18062, by rfl⟩) (B 36125 (by norm_num) ⟨18062, by rfl⟩ (by norm_num))
theorem R96337 : Reach 96337 := rs (se 2 (by rfl) ⟨36126, by rfl⟩) (B 72253 (by norm_num) ⟨36126, by rfl⟩ (by norm_num))
theorem R96341 : Reach 96341 := rs (se 8 (by rfl) ⟨564, by rfl⟩) (B 1129 (by norm_num) ⟨564, by rfl⟩ (by norm_num))
theorem R96345 : Reach 96345 := rs (se 2 (by rfl) ⟨36129, by rfl⟩) (B 72259 (by norm_num) ⟨36129, by rfl⟩ (by norm_num))
theorem R161885 : Reach 161885 := rs (se 3 (by rfl) ⟨30353, by rfl⟩) (B 60707 (by norm_num) ⟨30353, by rfl⟩ (by norm_num))
theorem R96349 : Reach 96349 := rs (se 3 (by rfl) ⟨18065, by rfl⟩) (B 36131 (by norm_num) ⟨18065, by rfl⟩ (by norm_num))
theorem R96353 : Reach 96353 := rs (se 2 (by rfl) ⟨36132, by rfl⟩) (B 72265 (by norm_num) ⟨36132, by rfl⟩ (by norm_num))
theorem R96357 : Reach 96357 := rs (se 4 (by rfl) ⟨9033, by rfl⟩) (B 18067 (by norm_num) ⟨9033, by rfl⟩ (by norm_num))
theorem R96361 : Reach 96361 := rs (se 2 (by rfl) ⟨36135, by rfl⟩) (B 72271 (by norm_num) ⟨36135, by rfl⟩ (by norm_num))
theorem R96365 : Reach 96365 := rs (se 3 (by rfl) ⟨18068, by rfl⟩) (B 36137 (by norm_num) ⟨18068, by rfl⟩ (by norm_num))
theorem R96369 : Reach 96369 := rs (se 2 (by rfl) ⟨36138, by rfl⟩) (B 72277 (by norm_num) ⟨36138, by rfl⟩ (by norm_num))
theorem R96373 : Reach 96373 := rs (se 5 (by rfl) ⟨4517, by rfl⟩) (B 9035 (by norm_num) ⟨4517, by rfl⟩ (by norm_num))
theorem R96377 : Reach 96377 := rs (se 2 (by rfl) ⟨36141, by rfl⟩) (B 72283 (by norm_num) ⟨36141, by rfl⟩ (by norm_num))
theorem R96381 : Reach 96381 := rs (se 3 (by rfl) ⟨18071, by rfl⟩) (B 36143 (by norm_num) ⟨18071, by rfl⟩ (by norm_num))
theorem R96385 : Reach 96385 := rs (se 2 (by rfl) ⟨36144, by rfl⟩) (B 72289 (by norm_num) ⟨36144, by rfl⟩ (by norm_num))
theorem R96389 : Reach 96389 := rs (se 4 (by rfl) ⟨9036, by rfl⟩) (B 18073 (by norm_num) ⟨9036, by rfl⟩ (by norm_num))
theorem R96393 : Reach 96393 := rs (se 2 (by rfl) ⟨36147, by rfl⟩) (B 72295 (by norm_num) ⟨36147, by rfl⟩ (by norm_num))
theorem R96397 : Reach 96397 := rs (se 3 (by rfl) ⟨18074, by rfl⟩) (B 36149 (by norm_num) ⟨18074, by rfl⟩ (by norm_num))
theorem R96401 : Reach 96401 := rs (se 2 (by rfl) ⟨36150, by rfl⟩) (B 72301 (by norm_num) ⟨36150, by rfl⟩ (by norm_num))
theorem R96405 : Reach 96405 := rs (se 6 (by rfl) ⟨2259, by rfl⟩) (B 4519 (by norm_num) ⟨2259, by rfl⟩ (by norm_num))
theorem R325781 : Reach 325781 := rs (se 6 (by rfl) ⟨7635, by rfl⟩) (B 15271 (by norm_num) ⟨7635, by rfl⟩ (by norm_num))
theorem R96409 : Reach 96409 := rs (se 2 (by rfl) ⟨36153, by rfl⟩) (B 72307 (by norm_num) ⟨36153, by rfl⟩ (by norm_num))
theorem R96413 : Reach 96413 := rs (se 3 (by rfl) ⟨18077, by rfl⟩) (B 36155 (by norm_num) ⟨18077, by rfl⟩ (by norm_num))
theorem R96417 : Reach 96417 := rs (se 2 (by rfl) ⟨36156, by rfl⟩) (B 72313 (by norm_num) ⟨36156, by rfl⟩ (by norm_num))
theorem R96421 : Reach 96421 := rs (se 4 (by rfl) ⟨9039, by rfl⟩) (B 18079 (by norm_num) ⟨9039, by rfl⟩ (by norm_num))
theorem R96425 : Reach 96425 := rs (se 2 (by rfl) ⟨36159, by rfl⟩) (B 72319 (by norm_num) ⟨36159, by rfl⟩ (by norm_num))
theorem R96429 : Reach 96429 := rs (se 3 (by rfl) ⟨18080, by rfl⟩) (B 36161 (by norm_num) ⟨18080, by rfl⟩ (by norm_num))
theorem R96433 : Reach 96433 := rs (se 2 (by rfl) ⟨36162, by rfl⟩) (B 72325 (by norm_num) ⟨36162, by rfl⟩ (by norm_num))
theorem R96437 : Reach 96437 := rs (se 5 (by rfl) ⟨4520, by rfl⟩) (B 9041 (by norm_num) ⟨4520, by rfl⟩ (by norm_num))
theorem R96441 : Reach 96441 := rs (se 2 (by rfl) ⟨36165, by rfl⟩) (B 72331 (by norm_num) ⟨36165, by rfl⟩ (by norm_num))
theorem R96445 : Reach 96445 := rs (se 3 (by rfl) ⟨18083, by rfl⟩) (B 36167 (by norm_num) ⟨18083, by rfl⟩ (by norm_num))
theorem R96449 : Reach 96449 := rs (se 2 (by rfl) ⟨36168, by rfl⟩) (B 72337 (by norm_num) ⟨36168, by rfl⟩ (by norm_num))
theorem R96453 : Reach 96453 := rs (se 4 (by rfl) ⟨9042, by rfl⟩) (B 18085 (by norm_num) ⟨9042, by rfl⟩ (by norm_num))
theorem R96457 : Reach 96457 := rs (se 2 (by rfl) ⟨36171, by rfl⟩) (B 72343 (by norm_num) ⟨36171, by rfl⟩ (by norm_num))
theorem R96461 : Reach 96461 := rs (se 3 (by rfl) ⟨18086, by rfl⟩) (B 36173 (by norm_num) ⟨18086, by rfl⟩ (by norm_num))
theorem R96465 : Reach 96465 := rs (se 2 (by rfl) ⟨36174, by rfl⟩) (B 72349 (by norm_num) ⟨36174, by rfl⟩ (by norm_num))
theorem R96469 : Reach 96469 := rs (se 7 (by rfl) ⟨1130, by rfl⟩) (B 2261 (by norm_num) ⟨1130, by rfl⟩ (by norm_num))
theorem R96473 : Reach 96473 := rs (se 2 (by rfl) ⟨36177, by rfl⟩) (B 72355 (by norm_num) ⟨36177, by rfl⟩ (by norm_num))
theorem R162013 : Reach 162013 := rs (se 3 (by rfl) ⟨30377, by rfl⟩) (B 60755 (by norm_num) ⟨30377, by rfl⟩ (by norm_num))
theorem R96477 : Reach 96477 := rs (se 3 (by rfl) ⟨18089, by rfl⟩) (B 36179 (by norm_num) ⟨18089, by rfl⟩ (by norm_num))
theorem R96481 : Reach 96481 := rs (se 2 (by rfl) ⟨36180, by rfl⟩) (B 72361 (by norm_num) ⟨36180, by rfl⟩ (by norm_num))
theorem R96485 : Reach 96485 := rs (se 4 (by rfl) ⟨9045, by rfl⟩) (B 18091 (by norm_num) ⟨9045, by rfl⟩ (by norm_num))
theorem R96489 : Reach 96489 := rs (se 2 (by rfl) ⟨36183, by rfl⟩) (B 72367 (by norm_num) ⟨36183, by rfl⟩ (by norm_num))
theorem R96493 : Reach 96493 := rs (se 3 (by rfl) ⟨18092, by rfl⟩) (B 36185 (by norm_num) ⟨18092, by rfl⟩ (by norm_num))
theorem R96497 : Reach 96497 := rs (se 2 (by rfl) ⟨36186, by rfl⟩) (B 72373 (by norm_num) ⟨36186, by rfl⟩ (by norm_num))
theorem R96501 : Reach 96501 := rs (se 5 (by rfl) ⟨4523, by rfl⟩) (B 9047 (by norm_num) ⟨4523, by rfl⟩ (by norm_num))
theorem R96505 : Reach 96505 := rs (se 2 (by rfl) ⟨36189, by rfl⟩) (B 72379 (by norm_num) ⟨36189, by rfl⟩ (by norm_num))
theorem R96509 : Reach 96509 := rs (se 3 (by rfl) ⟨18095, by rfl⟩) (B 36191 (by norm_num) ⟨18095, by rfl⟩ (by norm_num))
theorem R96513 : Reach 96513 := rs (se 2 (by rfl) ⟨36192, by rfl⟩) (B 72385 (by norm_num) ⟨36192, by rfl⟩ (by norm_num))
theorem R96517 : Reach 96517 := rs (se 4 (by rfl) ⟨9048, by rfl⟩) (B 18097 (by norm_num) ⟨9048, by rfl⟩ (by norm_num))
theorem R96521 : Reach 96521 := rs (se 2 (by rfl) ⟨36195, by rfl⟩) (B 72391 (by norm_num) ⟨36195, by rfl⟩ (by norm_num))
theorem R96525 : Reach 96525 := rs (se 3 (by rfl) ⟨18098, by rfl⟩) (B 36197 (by norm_num) ⟨18098, by rfl⟩ (by norm_num))
theorem R96529 : Reach 96529 := rs (se 2 (by rfl) ⟨36198, by rfl⟩) (B 72397 (by norm_num) ⟨36198, by rfl⟩ (by norm_num))
theorem R96533 : Reach 96533 := rs (se 6 (by rfl) ⟨2262, by rfl⟩) (B 4525 (by norm_num) ⟨2262, by rfl⟩ (by norm_num))
theorem R96537 : Reach 96537 := rs (se 2 (by rfl) ⟨36201, by rfl⟩) (B 72403 (by norm_num) ⟨36201, by rfl⟩ (by norm_num))
theorem R96541 : Reach 96541 := rs (se 3 (by rfl) ⟨18101, by rfl⟩) (B 36203 (by norm_num) ⟨18101, by rfl⟩ (by norm_num))
theorem R96545 : Reach 96545 := rs (se 2 (by rfl) ⟨36204, by rfl⟩) (B 72409 (by norm_num) ⟨36204, by rfl⟩ (by norm_num))
theorem R96549 : Reach 96549 := rs (se 4 (by rfl) ⟨9051, by rfl⟩) (B 18103 (by norm_num) ⟨9051, by rfl⟩ (by norm_num))
theorem R96553 : Reach 96553 := rs (se 2 (by rfl) ⟨36207, by rfl⟩) (B 72415 (by norm_num) ⟨36207, by rfl⟩ (by norm_num))
theorem R96557 : Reach 96557 := rs (se 3 (by rfl) ⟨18104, by rfl⟩) (B 36209 (by norm_num) ⟨18104, by rfl⟩ (by norm_num))
theorem R96561 : Reach 96561 := rs (se 2 (by rfl) ⟨36210, by rfl⟩) (B 72421 (by norm_num) ⟨36210, by rfl⟩ (by norm_num))
theorem R162101 : Reach 162101 := rs (se 5 (by rfl) ⟨7598, by rfl⟩) (B 15197 (by norm_num) ⟨7598, by rfl⟩ (by norm_num))
theorem R96565 : Reach 96565 := rs (se 5 (by rfl) ⟨4526, by rfl⟩) (B 9053 (by norm_num) ⟨4526, by rfl⟩ (by norm_num))
theorem R96569 : Reach 96569 := rs (se 2 (by rfl) ⟨36213, by rfl⟩) (B 72427 (by norm_num) ⟨36213, by rfl⟩ (by norm_num))
theorem R96573 : Reach 96573 := rs (se 3 (by rfl) ⟨18107, by rfl⟩) (B 36215 (by norm_num) ⟨18107, by rfl⟩ (by norm_num))
theorem R96577 : Reach 96577 := rs (se 2 (by rfl) ⟨36216, by rfl⟩) (B 72433 (by norm_num) ⟨36216, by rfl⟩ (by norm_num))
theorem R96581 : Reach 96581 := rs (se 4 (by rfl) ⟨9054, by rfl⟩) (B 18109 (by norm_num) ⟨9054, by rfl⟩ (by norm_num))
theorem R96585 : Reach 96585 := rs (se 2 (by rfl) ⟨36219, by rfl⟩) (B 72439 (by norm_num) ⟨36219, by rfl⟩ (by norm_num))
theorem R96589 : Reach 96589 := rs (se 3 (by rfl) ⟨18110, by rfl⟩) (B 36221 (by norm_num) ⟨18110, by rfl⟩ (by norm_num))
theorem R96593 : Reach 96593 := rs (se 2 (by rfl) ⟨36222, by rfl⟩) (B 72445 (by norm_num) ⟨36222, by rfl⟩ (by norm_num))
theorem R96597 : Reach 96597 := rs (se 10 (by rfl) ⟨141, by rfl⟩) (B 283 (by norm_num) ⟨141, by rfl⟩ (by norm_num))
theorem R96601 : Reach 96601 := rs (se 2 (by rfl) ⟨36225, by rfl⟩) (B 72451 (by norm_num) ⟨36225, by rfl⟩ (by norm_num))
theorem R96605 : Reach 96605 := rs (se 3 (by rfl) ⟨18113, by rfl⟩) (B 36227 (by norm_num) ⟨18113, by rfl⟩ (by norm_num))
theorem R96609 : Reach 96609 := rs (se 2 (by rfl) ⟨36228, by rfl⟩) (B 72457 (by norm_num) ⟨36228, by rfl⟩ (by norm_num))
theorem R96613 : Reach 96613 := rs (se 4 (by rfl) ⟨9057, by rfl⟩) (B 18115 (by norm_num) ⟨9057, by rfl⟩ (by norm_num))
theorem R96617 : Reach 96617 := rs (se 2 (by rfl) ⟨36231, by rfl⟩) (B 72463 (by norm_num) ⟨36231, by rfl⟩ (by norm_num))
theorem R96621 : Reach 96621 := rs (se 3 (by rfl) ⟨18116, by rfl⟩) (B 36233 (by norm_num) ⟨18116, by rfl⟩ (by norm_num))
theorem R96625 : Reach 96625 := rs (se 2 (by rfl) ⟨36234, by rfl⟩) (B 72469 (by norm_num) ⟨36234, by rfl⟩ (by norm_num))
theorem R96629 : Reach 96629 := rs (se 5 (by rfl) ⟨4529, by rfl⟩) (B 9059 (by norm_num) ⟨4529, by rfl⟩ (by norm_num))
theorem R96633 : Reach 96633 := rs (se 2 (by rfl) ⟨36237, by rfl⟩) (B 72475 (by norm_num) ⟨36237, by rfl⟩ (by norm_num))
theorem R96637 : Reach 96637 := rs (se 3 (by rfl) ⟨18119, by rfl⟩) (B 36239 (by norm_num) ⟨18119, by rfl⟩ (by norm_num))
theorem R96641 : Reach 96641 := rs (se 2 (by rfl) ⟨36240, by rfl⟩) (B 72481 (by norm_num) ⟨36240, by rfl⟩ (by norm_num))
theorem R96645 : Reach 96645 := rs (se 4 (by rfl) ⟨9060, by rfl⟩) (B 18121 (by norm_num) ⟨9060, by rfl⟩ (by norm_num))
theorem R96649 : Reach 96649 := rs (se 2 (by rfl) ⟨36243, by rfl⟩) (B 72487 (by norm_num) ⟨36243, by rfl⟩ (by norm_num))
theorem R96653 : Reach 96653 := rs (se 3 (by rfl) ⟨18122, by rfl⟩) (B 36245 (by norm_num) ⟨18122, by rfl⟩ (by norm_num))
theorem R96657 : Reach 96657 := rs (se 2 (by rfl) ⟨36246, by rfl⟩) (B 72493 (by norm_num) ⟨36246, by rfl⟩ (by norm_num))
theorem R96661 : Reach 96661 := rs (se 6 (by rfl) ⟨2265, by rfl⟩) (B 4531 (by norm_num) ⟨2265, by rfl⟩ (by norm_num))
theorem R96665 : Reach 96665 := rs (se 2 (by rfl) ⟨36249, by rfl⟩) (B 72499 (by norm_num) ⟨36249, by rfl⟩ (by norm_num))
theorem R96669 : Reach 96669 := rs (se 3 (by rfl) ⟨18125, by rfl⟩) (B 36251 (by norm_num) ⟨18125, by rfl⟩ (by norm_num))
theorem R96673 : Reach 96673 := rs (se 2 (by rfl) ⟨36252, by rfl⟩) (B 72505 (by norm_num) ⟨36252, by rfl⟩ (by norm_num))
theorem R96677 : Reach 96677 := rs (se 4 (by rfl) ⟨9063, by rfl⟩) (B 18127 (by norm_num) ⟨9063, by rfl⟩ (by norm_num))
theorem R96681 : Reach 96681 := rs (se 2 (by rfl) ⟨36255, by rfl⟩) (B 72511 (by norm_num) ⟨36255, by rfl⟩ (by norm_num))
theorem R96685 : Reach 96685 := rs (se 3 (by rfl) ⟨18128, by rfl⟩) (B 36257 (by norm_num) ⟨18128, by rfl⟩ (by norm_num))
theorem R96689 : Reach 96689 := rs (se 2 (by rfl) ⟨36258, by rfl⟩) (B 72517 (by norm_num) ⟨36258, by rfl⟩ (by norm_num))
theorem R162229 : Reach 162229 := rs (se 5 (by rfl) ⟨7604, by rfl⟩) (B 15209 (by norm_num) ⟨7604, by rfl⟩ (by norm_num))
theorem R96693 : Reach 96693 := rs (se 5 (by rfl) ⟨4532, by rfl⟩) (B 9065 (by norm_num) ⟨4532, by rfl⟩ (by norm_num))
theorem R96697 : Reach 96697 := rs (se 2 (by rfl) ⟨36261, by rfl⟩) (B 72523 (by norm_num) ⟨36261, by rfl⟩ (by norm_num))
theorem R96701 : Reach 96701 := rs (se 3 (by rfl) ⟨18131, by rfl⟩) (B 36263 (by norm_num) ⟨18131, by rfl⟩ (by norm_num))
theorem R96705 : Reach 96705 := rs (se 2 (by rfl) ⟨36264, by rfl⟩) (B 72529 (by norm_num) ⟨36264, by rfl⟩ (by norm_num))
theorem R96709 : Reach 96709 := rs (se 4 (by rfl) ⟨9066, by rfl⟩) (B 18133 (by norm_num) ⟨9066, by rfl⟩ (by norm_num))
theorem R96713 : Reach 96713 := rs (se 2 (by rfl) ⟨36267, by rfl⟩) (B 72535 (by norm_num) ⟨36267, by rfl⟩ (by norm_num))
theorem R96717 : Reach 96717 := rs (se 3 (by rfl) ⟨18134, by rfl⟩) (B 36269 (by norm_num) ⟨18134, by rfl⟩ (by norm_num))
theorem R96721 : Reach 96721 := rs (se 2 (by rfl) ⟨36270, by rfl⟩) (B 72541 (by norm_num) ⟨36270, by rfl⟩ (by norm_num))
theorem R96725 : Reach 96725 := rs (se 7 (by rfl) ⟨1133, by rfl⟩) (B 2267 (by norm_num) ⟨1133, by rfl⟩ (by norm_num))
theorem R96729 : Reach 96729 := rs (se 2 (by rfl) ⟨36273, by rfl⟩) (B 72547 (by norm_num) ⟨36273, by rfl⟩ (by norm_num))
theorem R96733 : Reach 96733 := rs (se 3 (by rfl) ⟨18137, by rfl⟩) (B 36275 (by norm_num) ⟨18137, by rfl⟩ (by norm_num))
theorem R96737 : Reach 96737 := rs (se 2 (by rfl) ⟨36276, by rfl⟩) (B 72553 (by norm_num) ⟨36276, by rfl⟩ (by norm_num))
theorem R96741 : Reach 96741 := rs (se 4 (by rfl) ⟨9069, by rfl⟩) (B 18139 (by norm_num) ⟨9069, by rfl⟩ (by norm_num))
theorem R96745 : Reach 96745 := rs (se 2 (by rfl) ⟨36279, by rfl⟩) (B 72559 (by norm_num) ⟨36279, by rfl⟩ (by norm_num))
theorem R96749 : Reach 96749 := rs (se 3 (by rfl) ⟨18140, by rfl⟩) (B 36281 (by norm_num) ⟨18140, by rfl⟩ (by norm_num))
theorem R96753 : Reach 96753 := rs (se 2 (by rfl) ⟨36282, by rfl⟩) (B 72565 (by norm_num) ⟨36282, by rfl⟩ (by norm_num))
theorem R96757 : Reach 96757 := rs (se 5 (by rfl) ⟨4535, by rfl⟩) (B 9071 (by norm_num) ⟨4535, by rfl⟩ (by norm_num))
theorem R96761 : Reach 96761 := rs (se 2 (by rfl) ⟨36285, by rfl⟩) (B 72571 (by norm_num) ⟨36285, by rfl⟩ (by norm_num))
theorem R96765 : Reach 96765 := rs (se 3 (by rfl) ⟨18143, by rfl⟩) (B 36287 (by norm_num) ⟨18143, by rfl⟩ (by norm_num))
theorem R96769 : Reach 96769 := rs (se 2 (by rfl) ⟨36288, by rfl⟩) (B 72577 (by norm_num) ⟨36288, by rfl⟩ (by norm_num))
theorem R96773 : Reach 96773 := rs (se 4 (by rfl) ⟨9072, by rfl⟩) (B 18145 (by norm_num) ⟨9072, by rfl⟩ (by norm_num))
theorem R96777 : Reach 96777 := rs (se 2 (by rfl) ⟨36291, by rfl⟩) (B 72583 (by norm_num) ⟨36291, by rfl⟩ (by norm_num))
theorem R162317 : Reach 162317 := rs (se 3 (by rfl) ⟨30434, by rfl⟩) (B 60869 (by norm_num) ⟨30434, by rfl⟩ (by norm_num))
theorem R96781 : Reach 96781 := rs (se 3 (by rfl) ⟨18146, by rfl⟩) (B 36293 (by norm_num) ⟨18146, by rfl⟩ (by norm_num))
theorem R96785 : Reach 96785 := rs (se 2 (by rfl) ⟨36294, by rfl⟩) (B 72589 (by norm_num) ⟨36294, by rfl⟩ (by norm_num))
theorem R96789 : Reach 96789 := rs (se 6 (by rfl) ⟨2268, by rfl⟩) (B 4537 (by norm_num) ⟨2268, by rfl⟩ (by norm_num))
theorem R96793 : Reach 96793 := rs (se 2 (by rfl) ⟨36297, by rfl⟩) (B 72595 (by norm_num) ⟨36297, by rfl⟩ (by norm_num))
theorem R96797 : Reach 96797 := rs (se 3 (by rfl) ⟨18149, by rfl⟩) (B 36299 (by norm_num) ⟨18149, by rfl⟩ (by norm_num))
theorem R96801 : Reach 96801 := rs (se 2 (by rfl) ⟨36300, by rfl⟩) (B 72601 (by norm_num) ⟨36300, by rfl⟩ (by norm_num))
theorem R96805 : Reach 96805 := rs (se 4 (by rfl) ⟨9075, by rfl⟩) (B 18151 (by norm_num) ⟨9075, by rfl⟩ (by norm_num))
theorem R96809 : Reach 96809 := rs (se 2 (by rfl) ⟨36303, by rfl⟩) (B 72607 (by norm_num) ⟨36303, by rfl⟩ (by norm_num))
theorem R96813 : Reach 96813 := rs (se 3 (by rfl) ⟨18152, by rfl⟩) (B 36305 (by norm_num) ⟨18152, by rfl⟩ (by norm_num))
theorem R96817 : Reach 96817 := rs (se 2 (by rfl) ⟨36306, by rfl⟩) (B 72613 (by norm_num) ⟨36306, by rfl⟩ (by norm_num))
theorem R96821 : Reach 96821 := rs (se 5 (by rfl) ⟨4538, by rfl⟩) (B 9077 (by norm_num) ⟨4538, by rfl⟩ (by norm_num))
theorem R96825 : Reach 96825 := rs (se 2 (by rfl) ⟨36309, by rfl⟩) (B 72619 (by norm_num) ⟨36309, by rfl⟩ (by norm_num))
theorem R96829 : Reach 96829 := rs (se 3 (by rfl) ⟨18155, by rfl⟩) (B 36311 (by norm_num) ⟨18155, by rfl⟩ (by norm_num))
theorem R96833 : Reach 96833 := rs (se 2 (by rfl) ⟨36312, by rfl⟩) (B 72625 (by norm_num) ⟨36312, by rfl⟩ (by norm_num))
theorem R326213 : Reach 326213 := rs (se 4 (by rfl) ⟨30582, by rfl⟩) (B 61165 (by norm_num) ⟨30582, by rfl⟩ (by norm_num))
theorem R96837 : Reach 96837 := rs (se 4 (by rfl) ⟨9078, by rfl⟩) (B 18157 (by norm_num) ⟨9078, by rfl⟩ (by norm_num))
theorem R96841 : Reach 96841 := rs (se 2 (by rfl) ⟨36315, by rfl⟩) (B 72631 (by norm_num) ⟨36315, by rfl⟩ (by norm_num))
theorem R96845 : Reach 96845 := rs (se 3 (by rfl) ⟨18158, by rfl⟩) (B 36317 (by norm_num) ⟨18158, by rfl⟩ (by norm_num))
theorem R96849 : Reach 96849 := rs (se 2 (by rfl) ⟨36318, by rfl⟩) (B 72637 (by norm_num) ⟨36318, by rfl⟩ (by norm_num))
theorem R686677 : Reach 686677 := rs (se 8 (by rfl) ⟨4023, by rfl⟩) (B 8047 (by norm_num) ⟨4023, by rfl⟩ (by norm_num))
theorem R96853 : Reach 96853 := rs (se 8 (by rfl) ⟨567, by rfl⟩) (B 1135 (by norm_num) ⟨567, by rfl⟩ (by norm_num))
theorem R96857 : Reach 96857 := rs (se 2 (by rfl) ⟨36321, by rfl⟩) (B 72643 (by norm_num) ⟨36321, by rfl⟩ (by norm_num))
theorem R96861 : Reach 96861 := rs (se 3 (by rfl) ⟨18161, by rfl⟩) (B 36323 (by norm_num) ⟨18161, by rfl⟩ (by norm_num))
theorem R96865 : Reach 96865 := rs (se 2 (by rfl) ⟨36324, by rfl⟩) (B 72649 (by norm_num) ⟨36324, by rfl⟩ (by norm_num))
theorem R96869 : Reach 96869 := rs (se 4 (by rfl) ⟨9081, by rfl⟩) (B 18163 (by norm_num) ⟨9081, by rfl⟩ (by norm_num))
theorem R96873 : Reach 96873 := rs (se 2 (by rfl) ⟨36327, by rfl⟩) (B 72655 (by norm_num) ⟨36327, by rfl⟩ (by norm_num))
theorem R96877 : Reach 96877 := rs (se 3 (by rfl) ⟨18164, by rfl⟩) (B 36329 (by norm_num) ⟨18164, by rfl⟩ (by norm_num))
theorem R96881 : Reach 96881 := rs (se 2 (by rfl) ⟨36330, by rfl⟩) (B 72661 (by norm_num) ⟨36330, by rfl⟩ (by norm_num))
theorem R96885 : Reach 96885 := rs (se 5 (by rfl) ⟨4541, by rfl⟩) (B 9083 (by norm_num) ⟨4541, by rfl⟩ (by norm_num))
theorem R96889 : Reach 96889 := rs (se 2 (by rfl) ⟨36333, by rfl⟩) (B 72667 (by norm_num) ⟨36333, by rfl⟩ (by norm_num))
theorem R96893 : Reach 96893 := rs (se 3 (by rfl) ⟨18167, by rfl⟩) (B 36335 (by norm_num) ⟨18167, by rfl⟩ (by norm_num))
theorem R96897 : Reach 96897 := rs (se 2 (by rfl) ⟨36336, by rfl⟩) (B 72673 (by norm_num) ⟨36336, by rfl⟩ (by norm_num))
theorem R195205 : Reach 195205 := rs (se 4 (by rfl) ⟨18300, by rfl⟩) (B 36601 (by norm_num) ⟨18300, by rfl⟩ (by norm_num))
theorem R96901 : Reach 96901 := rs (se 4 (by rfl) ⟨9084, by rfl⟩) (B 18169 (by norm_num) ⟨9084, by rfl⟩ (by norm_num))
theorem R96905 : Reach 96905 := rs (se 2 (by rfl) ⟨36339, by rfl⟩) (B 72679 (by norm_num) ⟨36339, by rfl⟩ (by norm_num))
theorem R162445 : Reach 162445 := rs (se 3 (by rfl) ⟨30458, by rfl⟩) (B 60917 (by norm_num) ⟨30458, by rfl⟩ (by norm_num))
theorem R96909 : Reach 96909 := rs (se 3 (by rfl) ⟨18170, by rfl⟩) (B 36341 (by norm_num) ⟨18170, by rfl⟩ (by norm_num))
theorem R96913 : Reach 96913 := rs (se 2 (by rfl) ⟨36342, by rfl⟩) (B 72685 (by norm_num) ⟨36342, by rfl⟩ (by norm_num))
theorem R96917 : Reach 96917 := rs (se 6 (by rfl) ⟨2271, by rfl⟩) (B 4543 (by norm_num) ⟨2271, by rfl⟩ (by norm_num))
theorem R96921 : Reach 96921 := rs (se 2 (by rfl) ⟨36345, by rfl⟩) (B 72691 (by norm_num) ⟨36345, by rfl⟩ (by norm_num))
theorem R96925 : Reach 96925 := rs (se 3 (by rfl) ⟨18173, by rfl⟩) (B 36347 (by norm_num) ⟨18173, by rfl⟩ (by norm_num))
theorem R96929 : Reach 96929 := rs (se 2 (by rfl) ⟨36348, by rfl⟩) (B 72697 (by norm_num) ⟨36348, by rfl⟩ (by norm_num))
theorem R96933 : Reach 96933 := rs (se 4 (by rfl) ⟨9087, by rfl⟩) (B 18175 (by norm_num) ⟨9087, by rfl⟩ (by norm_num))
theorem R96937 : Reach 96937 := rs (se 2 (by rfl) ⟨36351, by rfl⟩) (B 72703 (by norm_num) ⟨36351, by rfl⟩ (by norm_num))
theorem R96941 : Reach 96941 := rs (se 3 (by rfl) ⟨18176, by rfl⟩) (B 36353 (by norm_num) ⟨18176, by rfl⟩ (by norm_num))
theorem R96945 : Reach 96945 := rs (se 2 (by rfl) ⟨36354, by rfl⟩) (B 72709 (by norm_num) ⟨36354, by rfl⟩ (by norm_num))
theorem R96949 : Reach 96949 := rs (se 5 (by rfl) ⟨4544, by rfl⟩) (B 9089 (by norm_num) ⟨4544, by rfl⟩ (by norm_num))
theorem R96953 : Reach 96953 := rs (se 2 (by rfl) ⟨36357, by rfl⟩) (B 72715 (by norm_num) ⟨36357, by rfl⟩ (by norm_num))
theorem R96957 : Reach 96957 := rs (se 3 (by rfl) ⟨18179, by rfl⟩) (B 36359 (by norm_num) ⟨18179, by rfl⟩ (by norm_num))
theorem R96961 : Reach 96961 := rs (se 2 (by rfl) ⟨36360, by rfl⟩) (B 72721 (by norm_num) ⟨36360, by rfl⟩ (by norm_num))
theorem R96965 : Reach 96965 := rs (se 4 (by rfl) ⟨9090, by rfl⟩) (B 18181 (by norm_num) ⟨9090, by rfl⟩ (by norm_num))
theorem R96969 : Reach 96969 := rs (se 2 (by rfl) ⟨36363, by rfl⟩) (B 72727 (by norm_num) ⟨36363, by rfl⟩ (by norm_num))
theorem R96973 : Reach 96973 := rs (se 3 (by rfl) ⟨18182, by rfl⟩) (B 36365 (by norm_num) ⟨18182, by rfl⟩ (by norm_num))
theorem R96977 : Reach 96977 := rs (se 2 (by rfl) ⟨36366, by rfl⟩) (B 72733 (by norm_num) ⟨36366, by rfl⟩ (by norm_num))
theorem R96981 : Reach 96981 := rs (se 7 (by rfl) ⟨1136, by rfl⟩) (B 2273 (by norm_num) ⟨1136, by rfl⟩ (by norm_num))
theorem R96985 : Reach 96985 := rs (se 2 (by rfl) ⟨36369, by rfl⟩) (B 72739 (by norm_num) ⟨36369, by rfl⟩ (by norm_num))
theorem R96989 : Reach 96989 := rs (se 3 (by rfl) ⟨18185, by rfl⟩) (B 36371 (by norm_num) ⟨18185, by rfl⟩ (by norm_num))
theorem R96993 : Reach 96993 := rs (se 2 (by rfl) ⟨36372, by rfl⟩) (B 72745 (by norm_num) ⟨36372, by rfl⟩ (by norm_num))
theorem R162533 : Reach 162533 := rs (se 4 (by rfl) ⟨15237, by rfl⟩) (B 30475 (by norm_num) ⟨15237, by rfl⟩ (by norm_num))
theorem R96997 : Reach 96997 := rs (se 4 (by rfl) ⟨9093, by rfl⟩) (B 18187 (by norm_num) ⟨9093, by rfl⟩ (by norm_num))
theorem R97001 : Reach 97001 := rs (se 2 (by rfl) ⟨36375, by rfl⟩) (B 72751 (by norm_num) ⟨36375, by rfl⟩ (by norm_num))
theorem R97005 : Reach 97005 := rs (se 3 (by rfl) ⟨18188, by rfl⟩) (B 36377 (by norm_num) ⟨18188, by rfl⟩ (by norm_num))
theorem R97009 : Reach 97009 := rs (se 2 (by rfl) ⟨36378, by rfl⟩) (B 72757 (by norm_num) ⟨36378, by rfl⟩ (by norm_num))
theorem R97013 : Reach 97013 := rs (se 5 (by rfl) ⟨4547, by rfl⟩) (B 9095 (by norm_num) ⟨4547, by rfl⟩ (by norm_num))
theorem R97017 : Reach 97017 := rs (se 2 (by rfl) ⟨36381, by rfl⟩) (B 72763 (by norm_num) ⟨36381, by rfl⟩ (by norm_num))
theorem R97021 : Reach 97021 := rs (se 3 (by rfl) ⟨18191, by rfl⟩) (B 36383 (by norm_num) ⟨18191, by rfl⟩ (by norm_num))
theorem R97025 : Reach 97025 := rs (se 2 (by rfl) ⟨36384, by rfl⟩) (B 72769 (by norm_num) ⟨36384, by rfl⟩ (by norm_num))
theorem R97029 : Reach 97029 := rs (se 4 (by rfl) ⟨9096, by rfl⟩) (B 18193 (by norm_num) ⟨9096, by rfl⟩ (by norm_num))
theorem R97033 : Reach 97033 := rs (se 2 (by rfl) ⟨36387, by rfl⟩) (B 72775 (by norm_num) ⟨36387, by rfl⟩ (by norm_num))
theorem R97037 : Reach 97037 := rs (se 3 (by rfl) ⟨18194, by rfl⟩) (B 36389 (by norm_num) ⟨18194, by rfl⟩ (by norm_num))
theorem R97041 : Reach 97041 := rs (se 2 (by rfl) ⟨36390, by rfl⟩) (B 72781 (by norm_num) ⟨36390, by rfl⟩ (by norm_num))
theorem R97045 : Reach 97045 := rs (se 6 (by rfl) ⟨2274, by rfl⟩) (B 4549 (by norm_num) ⟨2274, by rfl⟩ (by norm_num))
theorem R97049 : Reach 97049 := rs (se 2 (by rfl) ⟨36393, by rfl⟩) (B 72787 (by norm_num) ⟨36393, by rfl⟩ (by norm_num))
theorem R97053 : Reach 97053 := rs (se 3 (by rfl) ⟨18197, by rfl⟩) (B 36395 (by norm_num) ⟨18197, by rfl⟩ (by norm_num))
theorem R97057 : Reach 97057 := rs (se 2 (by rfl) ⟨36396, by rfl⟩) (B 72793 (by norm_num) ⟨36396, by rfl⟩ (by norm_num))
theorem R97061 : Reach 97061 := rs (se 4 (by rfl) ⟨9099, by rfl⟩) (B 18199 (by norm_num) ⟨9099, by rfl⟩ (by norm_num))
theorem R97065 : Reach 97065 := rs (se 2 (by rfl) ⟨36399, by rfl⟩) (B 72799 (by norm_num) ⟨36399, by rfl⟩ (by norm_num))
theorem R97069 : Reach 97069 := rs (se 3 (by rfl) ⟨18200, by rfl⟩) (B 36401 (by norm_num) ⟨18200, by rfl⟩ (by norm_num))
theorem R97073 : Reach 97073 := rs (se 2 (by rfl) ⟨36402, by rfl⟩) (B 72805 (by norm_num) ⟨36402, by rfl⟩ (by norm_num))
theorem R97077 : Reach 97077 := rs (se 5 (by rfl) ⟨4550, by rfl⟩) (B 9101 (by norm_num) ⟨4550, by rfl⟩ (by norm_num))
theorem R97081 : Reach 97081 := rs (se 2 (by rfl) ⟨36405, by rfl⟩) (B 72811 (by norm_num) ⟨36405, by rfl⟩ (by norm_num))
theorem R97085 : Reach 97085 := rs (se 3 (by rfl) ⟨18203, by rfl⟩) (B 36407 (by norm_num) ⟨18203, by rfl⟩ (by norm_num))
theorem R97089 : Reach 97089 := rs (se 2 (by rfl) ⟨36408, by rfl⟩) (B 72817 (by norm_num) ⟨36408, by rfl⟩ (by norm_num))
theorem R97093 : Reach 97093 := rs (se 4 (by rfl) ⟨9102, by rfl⟩) (B 18205 (by norm_num) ⟨9102, by rfl⟩ (by norm_num))
theorem R97097 : Reach 97097 := rs (se 2 (by rfl) ⟨36411, by rfl⟩) (B 72823 (by norm_num) ⟨36411, by rfl⟩ (by norm_num))
theorem R97101 : Reach 97101 := rs (se 3 (by rfl) ⟨18206, by rfl⟩) (B 36413 (by norm_num) ⟨18206, by rfl⟩ (by norm_num))
theorem R97105 : Reach 97105 := rs (se 2 (by rfl) ⟨36414, by rfl⟩) (B 72829 (by norm_num) ⟨36414, by rfl⟩ (by norm_num))
theorem R97109 : Reach 97109 := rs (se 9 (by rfl) ⟨284, by rfl⟩) (B 569 (by norm_num) ⟨284, by rfl⟩ (by norm_num))
theorem R97113 : Reach 97113 := rs (se 2 (by rfl) ⟨36417, by rfl⟩) (B 72835 (by norm_num) ⟨36417, by rfl⟩ (by norm_num))
theorem R97117 : Reach 97117 := rs (se 3 (by rfl) ⟨18209, by rfl⟩) (B 36419 (by norm_num) ⟨18209, by rfl⟩ (by norm_num))
theorem R97121 : Reach 97121 := rs (se 2 (by rfl) ⟨36420, by rfl⟩) (B 72841 (by norm_num) ⟨36420, by rfl⟩ (by norm_num))
theorem R162661 : Reach 162661 := rs (se 4 (by rfl) ⟨15249, by rfl⟩) (B 30499 (by norm_num) ⟨15249, by rfl⟩ (by norm_num))
theorem R97125 : Reach 97125 := rs (se 4 (by rfl) ⟨9105, by rfl⟩) (B 18211 (by norm_num) ⟨9105, by rfl⟩ (by norm_num))
theorem R97129 : Reach 97129 := rs (se 2 (by rfl) ⟨36423, by rfl⟩) (B 72847 (by norm_num) ⟨36423, by rfl⟩ (by norm_num))
theorem R97133 : Reach 97133 := rs (se 3 (by rfl) ⟨18212, by rfl⟩) (B 36425 (by norm_num) ⟨18212, by rfl⟩ (by norm_num))
theorem R97137 : Reach 97137 := rs (se 2 (by rfl) ⟨36426, by rfl⟩) (B 72853 (by norm_num) ⟨36426, by rfl⟩ (by norm_num))
theorem R97141 : Reach 97141 := rs (se 5 (by rfl) ⟨4553, by rfl⟩) (B 9107 (by norm_num) ⟨4553, by rfl⟩ (by norm_num))
theorem R97145 : Reach 97145 := rs (se 2 (by rfl) ⟨36429, by rfl⟩) (B 72859 (by norm_num) ⟨36429, by rfl⟩ (by norm_num))
theorem R97149 : Reach 97149 := rs (se 3 (by rfl) ⟨18215, by rfl⟩) (B 36431 (by norm_num) ⟨18215, by rfl⟩ (by norm_num))
theorem R97153 : Reach 97153 := rs (se 2 (by rfl) ⟨36432, by rfl⟩) (B 72865 (by norm_num) ⟨36432, by rfl⟩ (by norm_num))
theorem R490373 : Reach 490373 := rs (se 4 (by rfl) ⟨45972, by rfl⟩) (B 91945 (by norm_num) ⟨45972, by rfl⟩ (by norm_num))
theorem R97157 : Reach 97157 := rs (se 4 (by rfl) ⟨9108, by rfl⟩) (B 18217 (by norm_num) ⟨9108, by rfl⟩ (by norm_num))
theorem R97161 : Reach 97161 := rs (se 2 (by rfl) ⟨36435, by rfl⟩) (B 72871 (by norm_num) ⟨36435, by rfl⟩ (by norm_num))
theorem R97165 : Reach 97165 := rs (se 3 (by rfl) ⟨18218, by rfl⟩) (B 36437 (by norm_num) ⟨18218, by rfl⟩ (by norm_num))
theorem R97169 : Reach 97169 := rs (se 2 (by rfl) ⟨36438, by rfl⟩) (B 72877 (by norm_num) ⟨36438, by rfl⟩ (by norm_num))
theorem R97173 : Reach 97173 := rs (se 6 (by rfl) ⟨2277, by rfl⟩) (B 4555 (by norm_num) ⟨2277, by rfl⟩ (by norm_num))
theorem R97177 : Reach 97177 := rs (se 2 (by rfl) ⟨36441, by rfl⟩) (B 72883 (by norm_num) ⟨36441, by rfl⟩ (by norm_num))
theorem R97181 : Reach 97181 := rs (se 3 (by rfl) ⟨18221, by rfl⟩) (B 36443 (by norm_num) ⟨18221, by rfl⟩ (by norm_num))
theorem R97185 : Reach 97185 := rs (se 2 (by rfl) ⟨36444, by rfl⟩) (B 72889 (by norm_num) ⟨36444, by rfl⟩ (by norm_num))
theorem R97189 : Reach 97189 := rs (se 4 (by rfl) ⟨9111, by rfl⟩) (B 18223 (by norm_num) ⟨9111, by rfl⟩ (by norm_num))
theorem R97193 : Reach 97193 := rs (se 2 (by rfl) ⟨36447, by rfl⟩) (B 72895 (by norm_num) ⟨36447, by rfl⟩ (by norm_num))
theorem R97197 : Reach 97197 := rs (se 3 (by rfl) ⟨18224, by rfl⟩) (B 36449 (by norm_num) ⟨18224, by rfl⟩ (by norm_num))
theorem R97201 : Reach 97201 := rs (se 2 (by rfl) ⟨36450, by rfl⟩) (B 72901 (by norm_num) ⟨36450, by rfl⟩ (by norm_num))
theorem R97205 : Reach 97205 := rs (se 5 (by rfl) ⟨4556, by rfl⟩) (B 9113 (by norm_num) ⟨4556, by rfl⟩ (by norm_num))
theorem R97209 : Reach 97209 := rs (se 2 (by rfl) ⟨36453, by rfl⟩) (B 72907 (by norm_num) ⟨36453, by rfl⟩ (by norm_num))
theorem R162749 : Reach 162749 := rs (se 3 (by rfl) ⟨30515, by rfl⟩) (B 61031 (by norm_num) ⟨30515, by rfl⟩ (by norm_num))
theorem R97213 : Reach 97213 := rs (se 3 (by rfl) ⟨18227, by rfl⟩) (B 36455 (by norm_num) ⟨18227, by rfl⟩ (by norm_num))
theorem R97217 : Reach 97217 := rs (se 2 (by rfl) ⟨36456, by rfl⟩) (B 72913 (by norm_num) ⟨36456, by rfl⟩ (by norm_num))
theorem R97221 : Reach 97221 := rs (se 4 (by rfl) ⟨9114, by rfl⟩) (B 18229 (by norm_num) ⟨9114, by rfl⟩ (by norm_num))
theorem R97225 : Reach 97225 := rs (se 2 (by rfl) ⟨36459, by rfl⟩) (B 72919 (by norm_num) ⟨36459, by rfl⟩ (by norm_num))
theorem R97229 : Reach 97229 := rs (se 3 (by rfl) ⟨18230, by rfl⟩) (B 36461 (by norm_num) ⟨18230, by rfl⟩ (by norm_num))
theorem R97233 : Reach 97233 := rs (se 2 (by rfl) ⟨36462, by rfl⟩) (B 72925 (by norm_num) ⟨36462, by rfl⟩ (by norm_num))
theorem R97237 : Reach 97237 := rs (se 7 (by rfl) ⟨1139, by rfl⟩) (B 2279 (by norm_num) ⟨1139, by rfl⟩ (by norm_num))
theorem R97241 : Reach 97241 := rs (se 2 (by rfl) ⟨36465, by rfl⟩) (B 72931 (by norm_num) ⟨36465, by rfl⟩ (by norm_num))
theorem R97245 : Reach 97245 := rs (se 3 (by rfl) ⟨18233, by rfl⟩) (B 36467 (by norm_num) ⟨18233, by rfl⟩ (by norm_num))
theorem R97249 : Reach 97249 := rs (se 2 (by rfl) ⟨36468, by rfl⟩) (B 72937 (by norm_num) ⟨36468, by rfl⟩ (by norm_num))
theorem R97253 : Reach 97253 := rs (se 4 (by rfl) ⟨9117, by rfl⟩) (B 18235 (by norm_num) ⟨9117, by rfl⟩ (by norm_num))
theorem R97257 : Reach 97257 := rs (se 2 (by rfl) ⟨36471, by rfl⟩) (B 72943 (by norm_num) ⟨36471, by rfl⟩ (by norm_num))
theorem R97261 : Reach 97261 := rs (se 3 (by rfl) ⟨18236, by rfl⟩) (B 36473 (by norm_num) ⟨18236, by rfl⟩ (by norm_num))
theorem R97265 : Reach 97265 := rs (se 2 (by rfl) ⟨36474, by rfl⟩) (B 72949 (by norm_num) ⟨36474, by rfl⟩ (by norm_num))
theorem R326645 : Reach 326645 := rs (se 5 (by rfl) ⟨15311, by rfl⟩) (B 30623 (by norm_num) ⟨15311, by rfl⟩ (by norm_num))
theorem R97269 : Reach 97269 := rs (se 5 (by rfl) ⟨4559, by rfl⟩) (B 9119 (by norm_num) ⟨4559, by rfl⟩ (by norm_num))
theorem R97273 : Reach 97273 := rs (se 2 (by rfl) ⟨36477, by rfl⟩) (B 72955 (by norm_num) ⟨36477, by rfl⟩ (by norm_num))
theorem R97277 : Reach 97277 := rs (se 3 (by rfl) ⟨18239, by rfl⟩) (B 36479 (by norm_num) ⟨18239, by rfl⟩ (by norm_num))
theorem R97281 : Reach 97281 := rs (se 2 (by rfl) ⟨36480, by rfl⟩) (B 72961 (by norm_num) ⟨36480, by rfl⟩ (by norm_num))
theorem R97285 : Reach 97285 := rs (se 4 (by rfl) ⟨9120, by rfl⟩) (B 18241 (by norm_num) ⟨9120, by rfl⟩ (by norm_num))
theorem R97289 : Reach 97289 := rs (se 2 (by rfl) ⟨36483, by rfl⟩) (B 72967 (by norm_num) ⟨36483, by rfl⟩ (by norm_num))
theorem R97293 : Reach 97293 := rs (se 3 (by rfl) ⟨18242, by rfl⟩) (B 36485 (by norm_num) ⟨18242, by rfl⟩ (by norm_num))
theorem R97297 : Reach 97297 := rs (se 2 (by rfl) ⟨36486, by rfl⟩) (B 72973 (by norm_num) ⟨36486, by rfl⟩ (by norm_num))
theorem R97301 : Reach 97301 := rs (se 6 (by rfl) ⟨2280, by rfl⟩) (B 4561 (by norm_num) ⟨2280, by rfl⟩ (by norm_num))
theorem R97305 : Reach 97305 := rs (se 2 (by rfl) ⟨36489, by rfl⟩) (B 72979 (by norm_num) ⟨36489, by rfl⟩ (by norm_num))
theorem R97309 : Reach 97309 := rs (se 3 (by rfl) ⟨18245, by rfl⟩) (B 36491 (by norm_num) ⟨18245, by rfl⟩ (by norm_num))
theorem R97313 : Reach 97313 := rs (se 2 (by rfl) ⟨36492, by rfl⟩) (B 72985 (by norm_num) ⟨36492, by rfl⟩ (by norm_num))
theorem R97317 : Reach 97317 := rs (se 4 (by rfl) ⟨9123, by rfl⟩) (B 18247 (by norm_num) ⟨9123, by rfl⟩ (by norm_num))
theorem R97321 : Reach 97321 := rs (se 2 (by rfl) ⟨36495, by rfl⟩) (B 72991 (by norm_num) ⟨36495, by rfl⟩ (by norm_num))
theorem R97325 : Reach 97325 := rs (se 3 (by rfl) ⟨18248, by rfl⟩) (B 36497 (by norm_num) ⟨18248, by rfl⟩ (by norm_num))
theorem R97329 : Reach 97329 := rs (se 2 (by rfl) ⟨36498, by rfl⟩) (B 72997 (by norm_num) ⟨36498, by rfl⟩ (by norm_num))
theorem R97333 : Reach 97333 := rs (se 5 (by rfl) ⟨4562, by rfl⟩) (B 9125 (by norm_num) ⟨4562, by rfl⟩ (by norm_num))
theorem R97337 : Reach 97337 := rs (se 2 (by rfl) ⟨36501, by rfl⟩) (B 73003 (by norm_num) ⟨36501, by rfl⟩ (by norm_num))
theorem R162877 : Reach 162877 := rs (se 3 (by rfl) ⟨30539, by rfl⟩) (B 61079 (by norm_num) ⟨30539, by rfl⟩ (by norm_num))
theorem R97341 : Reach 97341 := rs (se 3 (by rfl) ⟨18251, by rfl⟩) (B 36503 (by norm_num) ⟨18251, by rfl⟩ (by norm_num))
theorem R97345 : Reach 97345 := rs (se 2 (by rfl) ⟨36504, by rfl⟩) (B 73009 (by norm_num) ⟨36504, by rfl⟩ (by norm_num))
theorem R228413 : Reach 228413 := rs (se 3 (by rfl) ⟨42827, by rfl⟩) (B 85655 (by norm_num) ⟨42827, by rfl⟩ (by norm_num))
theorem R97349 : Reach 97349 := rs (se 4 (by rfl) ⟨9126, by rfl⟩) (B 18253 (by norm_num) ⟨9126, by rfl⟩ (by norm_num))
theorem R97353 : Reach 97353 := rs (se 2 (by rfl) ⟨36507, by rfl⟩) (B 73015 (by norm_num) ⟨36507, by rfl⟩ (by norm_num))
theorem R97357 : Reach 97357 := rs (se 3 (by rfl) ⟨18254, by rfl⟩) (B 36509 (by norm_num) ⟨18254, by rfl⟩ (by norm_num))
theorem R97361 : Reach 97361 := rs (se 2 (by rfl) ⟨36510, by rfl⟩) (B 73021 (by norm_num) ⟨36510, by rfl⟩ (by norm_num))
theorem R97365 : Reach 97365 := rs (se 8 (by rfl) ⟨570, by rfl⟩) (B 1141 (by norm_num) ⟨570, by rfl⟩ (by norm_num))
theorem R97369 : Reach 97369 := rs (se 2 (by rfl) ⟨36513, by rfl⟩) (B 73027 (by norm_num) ⟨36513, by rfl⟩ (by norm_num))
theorem R97373 : Reach 97373 := rs (se 3 (by rfl) ⟨18257, by rfl⟩) (B 36515 (by norm_num) ⟨18257, by rfl⟩ (by norm_num))
theorem R97377 : Reach 97377 := rs (se 2 (by rfl) ⟨36516, by rfl⟩) (B 73033 (by norm_num) ⟨36516, by rfl⟩ (by norm_num))
theorem R97381 : Reach 97381 := rs (se 4 (by rfl) ⟨9129, by rfl⟩) (B 18259 (by norm_num) ⟨9129, by rfl⟩ (by norm_num))
theorem R97385 : Reach 97385 := rs (se 2 (by rfl) ⟨36519, by rfl⟩) (B 73039 (by norm_num) ⟨36519, by rfl⟩ (by norm_num))
theorem R97389 : Reach 97389 := rs (se 3 (by rfl) ⟨18260, by rfl⟩) (B 36521 (by norm_num) ⟨18260, by rfl⟩ (by norm_num))
theorem R97393 : Reach 97393 := rs (se 2 (by rfl) ⟨36522, by rfl⟩) (B 73045 (by norm_num) ⟨36522, by rfl⟩ (by norm_num))
theorem R97397 : Reach 97397 := rs (se 5 (by rfl) ⟨4565, by rfl⟩) (B 9131 (by norm_num) ⟨4565, by rfl⟩ (by norm_num))
theorem R97401 : Reach 97401 := rs (se 2 (by rfl) ⟨36525, by rfl⟩) (B 73051 (by norm_num) ⟨36525, by rfl⟩ (by norm_num))
theorem R97405 : Reach 97405 := rs (se 3 (by rfl) ⟨18263, by rfl⟩) (B 36527 (by norm_num) ⟨18263, by rfl⟩ (by norm_num))
theorem R97409 : Reach 97409 := rs (se 2 (by rfl) ⟨36528, by rfl⟩) (B 73057 (by norm_num) ⟨36528, by rfl⟩ (by norm_num))
theorem R97413 : Reach 97413 := rs (se 4 (by rfl) ⟨9132, by rfl⟩) (B 18265 (by norm_num) ⟨9132, by rfl⟩ (by norm_num))
theorem R97417 : Reach 97417 := rs (se 2 (by rfl) ⟨36531, by rfl⟩) (B 73063 (by norm_num) ⟨36531, by rfl⟩ (by norm_num))
theorem R97421 : Reach 97421 := rs (se 3 (by rfl) ⟨18266, by rfl⟩) (B 36533 (by norm_num) ⟨18266, by rfl⟩ (by norm_num))
theorem R97425 : Reach 97425 := rs (se 2 (by rfl) ⟨36534, by rfl⟩) (B 73069 (by norm_num) ⟨36534, by rfl⟩ (by norm_num))
theorem R162965 : Reach 162965 := rs (se 6 (by rfl) ⟨3819, by rfl⟩) (B 7639 (by norm_num) ⟨3819, by rfl⟩ (by norm_num))
theorem R97429 : Reach 97429 := rs (se 6 (by rfl) ⟨2283, by rfl⟩) (B 4567 (by norm_num) ⟨2283, by rfl⟩ (by norm_num))
theorem R97433 : Reach 97433 := rs (se 2 (by rfl) ⟨36537, by rfl⟩) (B 73075 (by norm_num) ⟨36537, by rfl⟩ (by norm_num))
theorem R97437 : Reach 97437 := rs (se 3 (by rfl) ⟨18269, by rfl⟩) (B 36539 (by norm_num) ⟨18269, by rfl⟩ (by norm_num))
theorem R97441 : Reach 97441 := rs (se 2 (by rfl) ⟨36540, by rfl⟩) (B 73081 (by norm_num) ⟨36540, by rfl⟩ (by norm_num))
theorem R97445 : Reach 97445 := rs (se 4 (by rfl) ⟨9135, by rfl⟩) (B 18271 (by norm_num) ⟨9135, by rfl⟩ (by norm_num))
theorem R97449 : Reach 97449 := rs (se 2 (by rfl) ⟨36543, by rfl⟩) (B 73087 (by norm_num) ⟨36543, by rfl⟩ (by norm_num))
theorem R97453 : Reach 97453 := rs (se 3 (by rfl) ⟨18272, by rfl⟩) (B 36545 (by norm_num) ⟨18272, by rfl⟩ (by norm_num))
theorem R97457 : Reach 97457 := rs (se 2 (by rfl) ⟨36546, by rfl⟩) (B 73093 (by norm_num) ⟨36546, by rfl⟩ (by norm_num))
theorem R261301 : Reach 261301 := rs (se 5 (by rfl) ⟨12248, by rfl⟩) (B 24497 (by norm_num) ⟨12248, by rfl⟩ (by norm_num))
theorem R97461 : Reach 97461 := rs (se 5 (by rfl) ⟨4568, by rfl⟩) (B 9137 (by norm_num) ⟨4568, by rfl⟩ (by norm_num))
theorem R97465 : Reach 97465 := rs (se 2 (by rfl) ⟨36549, by rfl⟩) (B 73099 (by norm_num) ⟨36549, by rfl⟩ (by norm_num))
theorem R97469 : Reach 97469 := rs (se 3 (by rfl) ⟨18275, by rfl⟩) (B 36551 (by norm_num) ⟨18275, by rfl⟩ (by norm_num))
theorem R97473 : Reach 97473 := rs (se 2 (by rfl) ⟨36552, by rfl⟩) (B 73105 (by norm_num) ⟨36552, by rfl⟩ (by norm_num))
theorem R97477 : Reach 97477 := rs (se 4 (by rfl) ⟨9138, by rfl⟩) (B 18277 (by norm_num) ⟨9138, by rfl⟩ (by norm_num))
theorem R97481 : Reach 97481 := rs (se 2 (by rfl) ⟨36555, by rfl⟩) (B 73111 (by norm_num) ⟨36555, by rfl⟩ (by norm_num))
theorem R97485 : Reach 97485 := rs (se 3 (by rfl) ⟨18278, by rfl⟩) (B 36557 (by norm_num) ⟨18278, by rfl⟩ (by norm_num))
theorem R97489 : Reach 97489 := rs (se 2 (by rfl) ⟨36558, by rfl⟩) (B 73117 (by norm_num) ⟨36558, by rfl⟩ (by norm_num))
theorem R97493 : Reach 97493 := rs (se 7 (by rfl) ⟨1142, by rfl⟩) (B 2285 (by norm_num) ⟨1142, by rfl⟩ (by norm_num))
theorem R97497 : Reach 97497 := rs (se 2 (by rfl) ⟨36561, by rfl⟩) (B 73123 (by norm_num) ⟨36561, by rfl⟩ (by norm_num))
theorem R195805 : Reach 195805 := rs (se 3 (by rfl) ⟨36713, by rfl⟩) (B 73427 (by norm_num) ⟨36713, by rfl⟩ (by norm_num))
theorem R97501 : Reach 97501 := rs (se 3 (by rfl) ⟨18281, by rfl⟩) (B 36563 (by norm_num) ⟨18281, by rfl⟩ (by norm_num))
theorem R97505 : Reach 97505 := rs (se 2 (by rfl) ⟨36564, by rfl⟩) (B 73129 (by norm_num) ⟨36564, by rfl⟩ (by norm_num))
theorem R97509 : Reach 97509 := rs (se 4 (by rfl) ⟨9141, by rfl⟩) (B 18283 (by norm_num) ⟨9141, by rfl⟩ (by norm_num))
theorem R97513 : Reach 97513 := rs (se 2 (by rfl) ⟨36567, by rfl⟩) (B 73135 (by norm_num) ⟨36567, by rfl⟩ (by norm_num))
theorem R97517 : Reach 97517 := rs (se 3 (by rfl) ⟨18284, by rfl⟩) (B 36569 (by norm_num) ⟨18284, by rfl⟩ (by norm_num))
theorem R97521 : Reach 97521 := rs (se 2 (by rfl) ⟨36570, by rfl⟩) (B 73141 (by norm_num) ⟨36570, by rfl⟩ (by norm_num))
theorem R97525 : Reach 97525 := rs (se 5 (by rfl) ⟨4571, by rfl⟩) (B 9143 (by norm_num) ⟨4571, by rfl⟩ (by norm_num))
theorem R97529 : Reach 97529 := rs (se 2 (by rfl) ⟨36573, by rfl⟩) (B 73147 (by norm_num) ⟨36573, by rfl⟩ (by norm_num))
theorem R97533 : Reach 97533 := rs (se 3 (by rfl) ⟨18287, by rfl⟩) (B 36575 (by norm_num) ⟨18287, by rfl⟩ (by norm_num))
theorem R97537 : Reach 97537 := rs (se 2 (by rfl) ⟨36576, by rfl⟩) (B 73153 (by norm_num) ⟨36576, by rfl⟩ (by norm_num))
theorem R97541 : Reach 97541 := rs (se 4 (by rfl) ⟨9144, by rfl⟩) (B 18289 (by norm_num) ⟨9144, by rfl⟩ (by norm_num))
theorem R97545 : Reach 97545 := rs (se 2 (by rfl) ⟨36579, by rfl⟩) (B 73159 (by norm_num) ⟨36579, by rfl⟩ (by norm_num))
theorem R97549 : Reach 97549 := rs (se 3 (by rfl) ⟨18290, by rfl⟩) (B 36581 (by norm_num) ⟨18290, by rfl⟩ (by norm_num))
theorem R97553 : Reach 97553 := rs (se 2 (by rfl) ⟨36582, by rfl⟩) (B 73165 (by norm_num) ⟨36582, by rfl⟩ (by norm_num))
theorem R163093 : Reach 163093 := rs (se 6 (by rfl) ⟨3822, by rfl⟩) (B 7645 (by norm_num) ⟨3822, by rfl⟩ (by norm_num))
theorem R97557 : Reach 97557 := rs (se 6 (by rfl) ⟨2286, by rfl⟩) (B 4573 (by norm_num) ⟨2286, by rfl⟩ (by norm_num))
theorem R97561 : Reach 97561 := rs (se 2 (by rfl) ⟨36585, by rfl⟩) (B 73171 (by norm_num) ⟨36585, by rfl⟩ (by norm_num))
theorem R97565 : Reach 97565 := rs (se 3 (by rfl) ⟨18293, by rfl⟩) (B 36587 (by norm_num) ⟨18293, by rfl⟩ (by norm_num))
theorem R97569 : Reach 97569 := rs (se 2 (by rfl) ⟨36588, by rfl⟩) (B 73177 (by norm_num) ⟨36588, by rfl⟩ (by norm_num))
theorem R97573 : Reach 97573 := rs (se 4 (by rfl) ⟨9147, by rfl⟩) (B 18295 (by norm_num) ⟨9147, by rfl⟩ (by norm_num))
theorem R97577 : Reach 97577 := rs (se 2 (by rfl) ⟨36591, by rfl⟩) (B 73183 (by norm_num) ⟨36591, by rfl⟩ (by norm_num))
theorem R97581 : Reach 97581 := rs (se 3 (by rfl) ⟨18296, by rfl⟩) (B 36593 (by norm_num) ⟨18296, by rfl⟩ (by norm_num))
theorem R97585 : Reach 97585 := rs (se 2 (by rfl) ⟨36594, by rfl⟩) (B 73189 (by norm_num) ⟨36594, by rfl⟩ (by norm_num))
theorem R97589 : Reach 97589 := rs (se 5 (by rfl) ⟨4574, by rfl⟩) (B 9149 (by norm_num) ⟨4574, by rfl⟩ (by norm_num))
theorem R97593 : Reach 97593 := rs (se 2 (by rfl) ⟨36597, by rfl⟩) (B 73195 (by norm_num) ⟨36597, by rfl⟩ (by norm_num))
theorem R97597 : Reach 97597 := rs (se 3 (by rfl) ⟨18299, by rfl⟩) (B 36599 (by norm_num) ⟨18299, by rfl⟩ (by norm_num))
theorem R97601 : Reach 97601 := rs (se 2 (by rfl) ⟨36600, by rfl⟩) (B 73201 (by norm_num) ⟨36600, by rfl⟩ (by norm_num))
theorem R97605 : Reach 97605 := rs (se 4 (by rfl) ⟨9150, by rfl⟩) (B 18301 (by norm_num) ⟨9150, by rfl⟩ (by norm_num))
theorem R97609 : Reach 97609 := rs (se 2 (by rfl) ⟨36603, by rfl⟩) (B 73207 (by norm_num) ⟨36603, by rfl⟩ (by norm_num))
theorem R97613 : Reach 97613 := rs (se 3 (by rfl) ⟨18302, by rfl⟩) (B 36605 (by norm_num) ⟨18302, by rfl⟩ (by norm_num))
theorem R97617 : Reach 97617 := rs (se 2 (by rfl) ⟨36606, by rfl⟩) (B 73213 (by norm_num) ⟨36606, by rfl⟩ (by norm_num))
theorem R97621 : Reach 97621 := rs (se 11 (by rfl) ⟨71, by rfl⟩) (B 143 (by norm_num) ⟨71, by rfl⟩ (by norm_num))
theorem R97625 : Reach 97625 := rs (se 2 (by rfl) ⟨36609, by rfl⟩) (B 73219 (by norm_num) ⟨36609, by rfl⟩ (by norm_num))
theorem R97629 : Reach 97629 := rs (se 3 (by rfl) ⟨18305, by rfl⟩) (B 36611 (by norm_num) ⟨18305, by rfl⟩ (by norm_num))
theorem R97633 : Reach 97633 := rs (se 2 (by rfl) ⟨36612, by rfl⟩) (B 73225 (by norm_num) ⟨36612, by rfl⟩ (by norm_num))
theorem R97637 : Reach 97637 := rs (se 4 (by rfl) ⟨9153, by rfl⟩) (B 18307 (by norm_num) ⟨9153, by rfl⟩ (by norm_num))
theorem R97641 : Reach 97641 := rs (se 2 (by rfl) ⟨36615, by rfl⟩) (B 73231 (by norm_num) ⟨36615, by rfl⟩ (by norm_num))
theorem R163181 : Reach 163181 := rs (se 3 (by rfl) ⟨30596, by rfl⟩) (B 61193 (by norm_num) ⟨30596, by rfl⟩ (by norm_num))
theorem R97645 : Reach 97645 := rs (se 3 (by rfl) ⟨18308, by rfl⟩) (B 36617 (by norm_num) ⟨18308, by rfl⟩ (by norm_num))
theorem R97649 : Reach 97649 := rs (se 2 (by rfl) ⟨36618, by rfl⟩) (B 73237 (by norm_num) ⟨36618, by rfl⟩ (by norm_num))
theorem R97653 : Reach 97653 := rs (se 5 (by rfl) ⟨4577, by rfl⟩) (B 9155 (by norm_num) ⟨4577, by rfl⟩ (by norm_num))
theorem R97657 : Reach 97657 := rs (se 2 (by rfl) ⟨36621, by rfl⟩) (B 73243 (by norm_num) ⟨36621, by rfl⟩ (by norm_num))
theorem R97661 : Reach 97661 := rs (se 3 (by rfl) ⟨18311, by rfl⟩) (B 36623 (by norm_num) ⟨18311, by rfl⟩ (by norm_num))
theorem R97665 : Reach 97665 := rs (se 2 (by rfl) ⟨36624, by rfl⟩) (B 73249 (by norm_num) ⟨36624, by rfl⟩ (by norm_num))
theorem R97669 : Reach 97669 := rs (se 4 (by rfl) ⟨9156, by rfl⟩) (B 18313 (by norm_num) ⟨9156, by rfl⟩ (by norm_num))
theorem R97673 : Reach 97673 := rs (se 2 (by rfl) ⟨36627, by rfl⟩) (B 73255 (by norm_num) ⟨36627, by rfl⟩ (by norm_num))
theorem R97677 : Reach 97677 := rs (se 3 (by rfl) ⟨18314, by rfl⟩) (B 36629 (by norm_num) ⟨18314, by rfl⟩ (by norm_num))
theorem R97681 : Reach 97681 := rs (se 2 (by rfl) ⟨36630, by rfl⟩) (B 73261 (by norm_num) ⟨36630, by rfl⟩ (by norm_num))
theorem R97685 : Reach 97685 := rs (se 6 (by rfl) ⟨2289, by rfl⟩) (B 4579 (by norm_num) ⟨2289, by rfl⟩ (by norm_num))
theorem R97689 : Reach 97689 := rs (se 2 (by rfl) ⟨36633, by rfl⟩) (B 73267 (by norm_num) ⟨36633, by rfl⟩ (by norm_num))
theorem R97693 : Reach 97693 := rs (se 3 (by rfl) ⟨18317, by rfl⟩) (B 36635 (by norm_num) ⟨18317, by rfl⟩ (by norm_num))
theorem R97697 : Reach 97697 := rs (se 2 (by rfl) ⟨36636, by rfl⟩) (B 73273 (by norm_num) ⟨36636, by rfl⟩ (by norm_num))
theorem R327077 : Reach 327077 := rs (se 4 (by rfl) ⟨30663, by rfl⟩) (B 61327 (by norm_num) ⟨30663, by rfl⟩ (by norm_num))
theorem R97701 : Reach 97701 := rs (se 4 (by rfl) ⟨9159, by rfl⟩) (B 18319 (by norm_num) ⟨9159, by rfl⟩ (by norm_num))
theorem R97705 : Reach 97705 := rs (se 2 (by rfl) ⟨36639, by rfl⟩) (B 73279 (by norm_num) ⟨36639, by rfl⟩ (by norm_num))
theorem R97709 : Reach 97709 := rs (se 3 (by rfl) ⟨18320, by rfl⟩) (B 36641 (by norm_num) ⟨18320, by rfl⟩ (by norm_num))
theorem R97713 : Reach 97713 := rs (se 2 (by rfl) ⟨36642, by rfl⟩) (B 73285 (by norm_num) ⟨36642, by rfl⟩ (by norm_num))
theorem R97717 : Reach 97717 := rs (se 5 (by rfl) ⟨4580, by rfl⟩) (B 9161 (by norm_num) ⟨4580, by rfl⟩ (by norm_num))
theorem R97721 : Reach 97721 := rs (se 2 (by rfl) ⟨36645, by rfl⟩) (B 73291 (by norm_num) ⟨36645, by rfl⟩ (by norm_num))
theorem R97725 : Reach 97725 := rs (se 3 (by rfl) ⟨18323, by rfl⟩) (B 36647 (by norm_num) ⟨18323, by rfl⟩ (by norm_num))
theorem R97729 : Reach 97729 := rs (se 2 (by rfl) ⟨36648, by rfl⟩) (B 73297 (by norm_num) ⟨36648, by rfl⟩ (by norm_num))
theorem R97733 : Reach 97733 := rs (se 4 (by rfl) ⟨9162, by rfl⟩) (B 18325 (by norm_num) ⟨9162, by rfl⟩ (by norm_num))
theorem R97737 : Reach 97737 := rs (se 2 (by rfl) ⟨36651, by rfl⟩) (B 73303 (by norm_num) ⟨36651, by rfl⟩ (by norm_num))
theorem R97741 : Reach 97741 := rs (se 3 (by rfl) ⟨18326, by rfl⟩) (B 36653 (by norm_num) ⟨18326, by rfl⟩ (by norm_num))
theorem R97745 : Reach 97745 := rs (se 2 (by rfl) ⟨36654, by rfl⟩) (B 73309 (by norm_num) ⟨36654, by rfl⟩ (by norm_num))
theorem R261589 : Reach 261589 := rs (se 7 (by rfl) ⟨3065, by rfl⟩) (B 6131 (by norm_num) ⟨3065, by rfl⟩ (by norm_num))
theorem R97749 : Reach 97749 := rs (se 7 (by rfl) ⟨1145, by rfl⟩) (B 2291 (by norm_num) ⟨1145, by rfl⟩ (by norm_num))
theorem R97753 : Reach 97753 := rs (se 2 (by rfl) ⟨36657, by rfl⟩) (B 73315 (by norm_num) ⟨36657, by rfl⟩ (by norm_num))
theorem R97757 : Reach 97757 := rs (se 3 (by rfl) ⟨18329, by rfl⟩) (B 36659 (by norm_num) ⟨18329, by rfl⟩ (by norm_num))
theorem R97761 : Reach 97761 := rs (se 2 (by rfl) ⟨36660, by rfl⟩) (B 73321 (by norm_num) ⟨36660, by rfl⟩ (by norm_num))
theorem R97765 : Reach 97765 := rs (se 4 (by rfl) ⟨9165, by rfl⟩) (B 18331 (by norm_num) ⟨9165, by rfl⟩ (by norm_num))
theorem R97769 : Reach 97769 := rs (se 2 (by rfl) ⟨36663, by rfl⟩) (B 73327 (by norm_num) ⟨36663, by rfl⟩ (by norm_num))
theorem R163309 : Reach 163309 := rs (se 3 (by rfl) ⟨30620, by rfl⟩) (B 61241 (by norm_num) ⟨30620, by rfl⟩ (by norm_num))
theorem R97773 : Reach 97773 := rs (se 3 (by rfl) ⟨18332, by rfl⟩) (B 36665 (by norm_num) ⟨18332, by rfl⟩ (by norm_num))
theorem R97777 : Reach 97777 := rs (se 2 (by rfl) ⟨36666, by rfl⟩) (B 73333 (by norm_num) ⟨36666, by rfl⟩ (by norm_num))
theorem R97781 : Reach 97781 := rs (se 5 (by rfl) ⟨4583, by rfl⟩) (B 9167 (by norm_num) ⟨4583, by rfl⟩ (by norm_num))
theorem R97785 : Reach 97785 := rs (se 2 (by rfl) ⟨36669, by rfl⟩) (B 73339 (by norm_num) ⟨36669, by rfl⟩ (by norm_num))
theorem R97789 : Reach 97789 := rs (se 3 (by rfl) ⟨18335, by rfl⟩) (B 36671 (by norm_num) ⟨18335, by rfl⟩ (by norm_num))
theorem R97793 : Reach 97793 := rs (se 2 (by rfl) ⟨36672, by rfl⟩) (B 73345 (by norm_num) ⟨36672, by rfl⟩ (by norm_num))
theorem R458245 : Reach 458245 := rs (se 4 (by rfl) ⟨42960, by rfl⟩) (B 85921 (by norm_num) ⟨42960, by rfl⟩ (by norm_num))
theorem R97797 : Reach 97797 := rs (se 4 (by rfl) ⟨9168, by rfl⟩) (B 18337 (by norm_num) ⟨9168, by rfl⟩ (by norm_num))
theorem R97801 : Reach 97801 := rs (se 2 (by rfl) ⟨36675, by rfl⟩) (B 73351 (by norm_num) ⟨36675, by rfl⟩ (by norm_num))
theorem R97805 : Reach 97805 := rs (se 3 (by rfl) ⟨18338, by rfl⟩) (B 36677 (by norm_num) ⟨18338, by rfl⟩ (by norm_num))
theorem R97809 : Reach 97809 := rs (se 2 (by rfl) ⟨36678, by rfl⟩) (B 73357 (by norm_num) ⟨36678, by rfl⟩ (by norm_num))
theorem R97813 : Reach 97813 := rs (se 6 (by rfl) ⟨2292, by rfl⟩) (B 4585 (by norm_num) ⟨2292, by rfl⟩ (by norm_num))
theorem R97817 : Reach 97817 := rs (se 2 (by rfl) ⟨36681, by rfl⟩) (B 73363 (by norm_num) ⟨36681, by rfl⟩ (by norm_num))
theorem R97821 : Reach 97821 := rs (se 3 (by rfl) ⟨18341, by rfl⟩) (B 36683 (by norm_num) ⟨18341, by rfl⟩ (by norm_num))
theorem R97825 : Reach 97825 := rs (se 2 (by rfl) ⟨36684, by rfl⟩) (B 73369 (by norm_num) ⟨36684, by rfl⟩ (by norm_num))
theorem R97829 : Reach 97829 := rs (se 4 (by rfl) ⟨9171, by rfl⟩) (B 18343 (by norm_num) ⟨9171, by rfl⟩ (by norm_num))
theorem R97833 : Reach 97833 := rs (se 2 (by rfl) ⟨36687, by rfl⟩) (B 73375 (by norm_num) ⟨36687, by rfl⟩ (by norm_num))
theorem R97837 : Reach 97837 := rs (se 3 (by rfl) ⟨18344, by rfl⟩) (B 36689 (by norm_num) ⟨18344, by rfl⟩ (by norm_num))
theorem R97841 : Reach 97841 := rs (se 2 (by rfl) ⟨36690, by rfl⟩) (B 73381 (by norm_num) ⟨36690, by rfl⟩ (by norm_num))
theorem R97845 : Reach 97845 := rs (se 5 (by rfl) ⟨4586, by rfl⟩) (B 9173 (by norm_num) ⟨4586, by rfl⟩ (by norm_num))
theorem R97849 : Reach 97849 := rs (se 2 (by rfl) ⟨36693, by rfl⟩) (B 73387 (by norm_num) ⟨36693, by rfl⟩ (by norm_num))
theorem R97853 : Reach 97853 := rs (se 3 (by rfl) ⟨18347, by rfl⟩) (B 36695 (by norm_num) ⟨18347, by rfl⟩ (by norm_num))
theorem R97857 : Reach 97857 := rs (se 2 (by rfl) ⟨36696, by rfl⟩) (B 73393 (by norm_num) ⟨36696, by rfl⟩ (by norm_num))
theorem R261701 : Reach 261701 := rs (se 4 (by rfl) ⟨24534, by rfl⟩) (B 49069 (by norm_num) ⟨24534, by rfl⟩ (by norm_num))
theorem R163397 : Reach 163397 := rs (se 4 (by rfl) ⟨15318, by rfl⟩) (B 30637 (by norm_num) ⟨15318, by rfl⟩ (by norm_num))
theorem R97861 : Reach 97861 := rs (se 4 (by rfl) ⟨9174, by rfl⟩) (B 18349 (by norm_num) ⟨9174, by rfl⟩ (by norm_num))
theorem R97865 : Reach 97865 := rs (se 2 (by rfl) ⟨36699, by rfl⟩) (B 73399 (by norm_num) ⟨36699, by rfl⟩ (by norm_num))
theorem R97869 : Reach 97869 := rs (se 3 (by rfl) ⟨18350, by rfl⟩) (B 36701 (by norm_num) ⟨18350, by rfl⟩ (by norm_num))
theorem R97873 : Reach 97873 := rs (se 2 (by rfl) ⟨36702, by rfl⟩) (B 73405 (by norm_num) ⟨36702, by rfl⟩ (by norm_num))
theorem R97877 : Reach 97877 := rs (se 8 (by rfl) ⟨573, by rfl⟩) (B 1147 (by norm_num) ⟨573, by rfl⟩ (by norm_num))
theorem R97881 : Reach 97881 := rs (se 2 (by rfl) ⟨36705, by rfl⟩) (B 73411 (by norm_num) ⟨36705, by rfl⟩ (by norm_num))
theorem R97885 : Reach 97885 := rs (se 3 (by rfl) ⟨18353, by rfl⟩) (B 36707 (by norm_num) ⟨18353, by rfl⟩ (by norm_num))
theorem R97889 : Reach 97889 := rs (se 2 (by rfl) ⟨36708, by rfl⟩) (B 73417 (by norm_num) ⟨36708, by rfl⟩ (by norm_num))
theorem R97893 : Reach 97893 := rs (se 4 (by rfl) ⟨9177, by rfl⟩) (B 18355 (by norm_num) ⟨9177, by rfl⟩ (by norm_num))
theorem R97897 : Reach 97897 := rs (se 2 (by rfl) ⟨36711, by rfl⟩) (B 73423 (by norm_num) ⟨36711, by rfl⟩ (by norm_num))
theorem R97901 : Reach 97901 := rs (se 3 (by rfl) ⟨18356, by rfl⟩) (B 36713 (by norm_num) ⟨18356, by rfl⟩ (by norm_num))
theorem R97905 : Reach 97905 := rs (se 2 (by rfl) ⟨36714, by rfl⟩) (B 73429 (by norm_num) ⟨36714, by rfl⟩ (by norm_num))
theorem R97909 : Reach 97909 := rs (se 5 (by rfl) ⟨4589, by rfl⟩) (B 9179 (by norm_num) ⟨4589, by rfl⟩ (by norm_num))
theorem R97913 : Reach 97913 := rs (se 2 (by rfl) ⟨36717, by rfl⟩) (B 73435 (by norm_num) ⟨36717, by rfl⟩ (by norm_num))
theorem R97917 : Reach 97917 := rs (se 3 (by rfl) ⟨18359, by rfl⟩) (B 36719 (by norm_num) ⟨18359, by rfl⟩ (by norm_num))
theorem R97921 : Reach 97921 := rs (se 2 (by rfl) ⟨36720, by rfl⟩) (B 73441 (by norm_num) ⟨36720, by rfl⟩ (by norm_num))
theorem R97925 : Reach 97925 := rs (se 4 (by rfl) ⟨9180, by rfl⟩) (B 18361 (by norm_num) ⟨9180, by rfl⟩ (by norm_num))
theorem R97929 : Reach 97929 := rs (se 2 (by rfl) ⟨36723, by rfl⟩) (B 73447 (by norm_num) ⟨36723, by rfl⟩ (by norm_num))
theorem R97933 : Reach 97933 := rs (se 3 (by rfl) ⟨18362, by rfl⟩) (B 36725 (by norm_num) ⟨18362, by rfl⟩ (by norm_num))
theorem R97937 : Reach 97937 := rs (se 2 (by rfl) ⟨36726, by rfl⟩) (B 73453 (by norm_num) ⟨36726, by rfl⟩ (by norm_num))
theorem R97941 : Reach 97941 := rs (se 6 (by rfl) ⟨2295, by rfl⟩) (B 4591 (by norm_num) ⟨2295, by rfl⟩ (by norm_num))
theorem R97945 : Reach 97945 := rs (se 2 (by rfl) ⟨36729, by rfl⟩) (B 73459 (by norm_num) ⟨36729, by rfl⟩ (by norm_num))
theorem R97949 : Reach 97949 := rs (se 3 (by rfl) ⟨18365, by rfl⟩) (B 36731 (by norm_num) ⟨18365, by rfl⟩ (by norm_num))
theorem R97953 : Reach 97953 := rs (se 2 (by rfl) ⟨36732, by rfl⟩) (B 73465 (by norm_num) ⟨36732, by rfl⟩ (by norm_num))
theorem R97957 : Reach 97957 := rs (se 4 (by rfl) ⟨9183, by rfl⟩) (B 18367 (by norm_num) ⟨9183, by rfl⟩ (by norm_num))
theorem R97961 : Reach 97961 := rs (se 2 (by rfl) ⟨36735, by rfl⟩) (B 73471 (by norm_num) ⟨36735, by rfl⟩ (by norm_num))
theorem R97965 : Reach 97965 := rs (se 3 (by rfl) ⟨18368, by rfl⟩) (B 36737 (by norm_num) ⟨18368, by rfl⟩ (by norm_num))
theorem R97969 : Reach 97969 := rs (se 2 (by rfl) ⟨36738, by rfl⟩) (B 73477 (by norm_num) ⟨36738, by rfl⟩ (by norm_num))
theorem R97973 : Reach 97973 := rs (se 5 (by rfl) ⟨4592, by rfl⟩) (B 9185 (by norm_num) ⟨4592, by rfl⟩ (by norm_num))
theorem R97977 : Reach 97977 := rs (se 2 (by rfl) ⟨36741, by rfl⟩) (B 73483 (by norm_num) ⟨36741, by rfl⟩ (by norm_num))
theorem R97981 : Reach 97981 := rs (se 3 (by rfl) ⟨18371, by rfl⟩) (B 36743 (by norm_num) ⟨18371, by rfl⟩ (by norm_num))
theorem R97985 : Reach 97985 := rs (se 2 (by rfl) ⟨36744, by rfl⟩) (B 73489 (by norm_num) ⟨36744, by rfl⟩ (by norm_num))
theorem R163525 : Reach 163525 := rs (se 4 (by rfl) ⟨15330, by rfl⟩) (B 30661 (by norm_num) ⟨15330, by rfl⟩ (by norm_num))
theorem R97989 : Reach 97989 := rs (se 4 (by rfl) ⟨9186, by rfl⟩) (B 18373 (by norm_num) ⟨9186, by rfl⟩ (by norm_num))
theorem R97993 : Reach 97993 := rs (se 2 (by rfl) ⟨36747, by rfl⟩) (B 73495 (by norm_num) ⟨36747, by rfl⟩ (by norm_num))
theorem R97997 : Reach 97997 := rs (se 3 (by rfl) ⟨18374, by rfl⟩) (B 36749 (by norm_num) ⟨18374, by rfl⟩ (by norm_num))
theorem R98001 : Reach 98001 := rs (se 2 (by rfl) ⟨36750, by rfl⟩) (B 73501 (by norm_num) ⟨36750, by rfl⟩ (by norm_num))
theorem R98005 : Reach 98005 := rs (se 7 (by rfl) ⟨1148, by rfl⟩) (B 2297 (by norm_num) ⟨1148, by rfl⟩ (by norm_num))
theorem R98009 : Reach 98009 := rs (se 2 (by rfl) ⟨36753, by rfl⟩) (B 73507 (by norm_num) ⟨36753, by rfl⟩ (by norm_num))
theorem R229085 : Reach 229085 := rs (se 3 (by rfl) ⟨42953, by rfl⟩) (B 85907 (by norm_num) ⟨42953, by rfl⟩ (by norm_num))
theorem R98013 : Reach 98013 := rs (se 3 (by rfl) ⟨18377, by rfl⟩) (B 36755 (by norm_num) ⟨18377, by rfl⟩ (by norm_num))
theorem R98017 : Reach 98017 := rs (se 2 (by rfl) ⟨36756, by rfl⟩) (B 73513 (by norm_num) ⟨36756, by rfl⟩ (by norm_num))
theorem R98021 : Reach 98021 := rs (se 4 (by rfl) ⟨9189, by rfl⟩) (B 18379 (by norm_num) ⟨9189, by rfl⟩ (by norm_num))
theorem R98025 : Reach 98025 := rs (se 2 (by rfl) ⟨36759, by rfl⟩) (B 73519 (by norm_num) ⟨36759, by rfl⟩ (by norm_num))
theorem R98029 : Reach 98029 := rs (se 3 (by rfl) ⟨18380, by rfl⟩) (B 36761 (by norm_num) ⟨18380, by rfl⟩ (by norm_num))
theorem R98033 : Reach 98033 := rs (se 2 (by rfl) ⟨36762, by rfl⟩) (B 73525 (by norm_num) ⟨36762, by rfl⟩ (by norm_num))
theorem R98037 : Reach 98037 := rs (se 5 (by rfl) ⟨4595, by rfl⟩) (B 9191 (by norm_num) ⟨4595, by rfl⟩ (by norm_num))
theorem R98041 : Reach 98041 := rs (se 2 (by rfl) ⟨36765, by rfl⟩) (B 73531 (by norm_num) ⟨36765, by rfl⟩ (by norm_num))
theorem R98045 : Reach 98045 := rs (se 3 (by rfl) ⟨18383, by rfl⟩) (B 36767 (by norm_num) ⟨18383, by rfl⟩ (by norm_num))
theorem R98049 : Reach 98049 := rs (se 2 (by rfl) ⟨36768, by rfl⟩) (B 73537 (by norm_num) ⟨36768, by rfl⟩ (by norm_num))
theorem R98053 : Reach 98053 := rs (se 4 (by rfl) ⟨9192, by rfl⟩) (B 18385 (by norm_num) ⟨9192, by rfl⟩ (by norm_num))
theorem R98057 : Reach 98057 := rs (se 2 (by rfl) ⟨36771, by rfl⟩) (B 73543 (by norm_num) ⟨36771, by rfl⟩ (by norm_num))
theorem R98061 : Reach 98061 := rs (se 3 (by rfl) ⟨18386, by rfl⟩) (B 36773 (by norm_num) ⟨18386, by rfl⟩ (by norm_num))
theorem R98065 : Reach 98065 := rs (se 2 (by rfl) ⟨36774, by rfl⟩) (B 73549 (by norm_num) ⟨36774, by rfl⟩ (by norm_num))
theorem R98069 : Reach 98069 := rs (se 6 (by rfl) ⟨2298, by rfl⟩) (B 4597 (by norm_num) ⟨2298, by rfl⟩ (by norm_num))
theorem R98073 : Reach 98073 := rs (se 2 (by rfl) ⟨36777, by rfl⟩) (B 73555 (by norm_num) ⟨36777, by rfl⟩ (by norm_num))
theorem R163613 : Reach 163613 := rs (se 3 (by rfl) ⟨30677, by rfl⟩) (B 61355 (by norm_num) ⟨30677, by rfl⟩ (by norm_num))
theorem R98077 : Reach 98077 := rs (se 3 (by rfl) ⟨18389, by rfl⟩) (B 36779 (by norm_num) ⟨18389, by rfl⟩ (by norm_num))
theorem R98081 : Reach 98081 := rs (se 2 (by rfl) ⟨36780, by rfl⟩) (B 73561 (by norm_num) ⟨36780, by rfl⟩ (by norm_num))
theorem R98085 : Reach 98085 := rs (se 4 (by rfl) ⟨9195, by rfl⟩) (B 18391 (by norm_num) ⟨9195, by rfl⟩ (by norm_num))
theorem R98089 : Reach 98089 := rs (se 2 (by rfl) ⟨36783, by rfl⟩) (B 73567 (by norm_num) ⟨36783, by rfl⟩ (by norm_num))
theorem R98093 : Reach 98093 := rs (se 3 (by rfl) ⟨18392, by rfl⟩) (B 36785 (by norm_num) ⟨18392, by rfl⟩ (by norm_num))
theorem R98097 : Reach 98097 := rs (se 2 (by rfl) ⟨36786, by rfl⟩) (B 73573 (by norm_num) ⟨36786, by rfl⟩ (by norm_num))
theorem R98101 : Reach 98101 := rs (se 5 (by rfl) ⟨4598, by rfl⟩) (B 9197 (by norm_num) ⟨4598, by rfl⟩ (by norm_num))
theorem R98105 : Reach 98105 := rs (se 2 (by rfl) ⟨36789, by rfl⟩) (B 73579 (by norm_num) ⟨36789, by rfl⟩ (by norm_num))
theorem R98109 : Reach 98109 := rs (se 3 (by rfl) ⟨18395, by rfl⟩) (B 36791 (by norm_num) ⟨18395, by rfl⟩ (by norm_num))
theorem R98113 : Reach 98113 := rs (se 2 (by rfl) ⟨36792, by rfl⟩) (B 73585 (by norm_num) ⟨36792, by rfl⟩ (by norm_num))
theorem R98117 : Reach 98117 := rs (se 4 (by rfl) ⟨9198, by rfl⟩) (B 18397 (by norm_num) ⟨9198, by rfl⟩ (by norm_num))
theorem R98121 : Reach 98121 := rs (se 2 (by rfl) ⟨36795, by rfl⟩) (B 73591 (by norm_num) ⟨36795, by rfl⟩ (by norm_num))
theorem R98125 : Reach 98125 := rs (se 3 (by rfl) ⟨18398, by rfl⟩) (B 36797 (by norm_num) ⟨18398, by rfl⟩ (by norm_num))
theorem R98129 : Reach 98129 := rs (se 2 (by rfl) ⟨36798, by rfl⟩) (B 73597 (by norm_num) ⟨36798, by rfl⟩ (by norm_num))
theorem R3211093 : Reach 3211093 := rs (se 9 (by rfl) ⟨9407, by rfl⟩) (B 18815 (by norm_num) ⟨9407, by rfl⟩ (by norm_num))
theorem R327509 : Reach 327509 := rs (se 9 (by rfl) ⟨959, by rfl⟩) (B 1919 (by norm_num) ⟨959, by rfl⟩ (by norm_num))
theorem R98133 : Reach 98133 := rs (se 9 (by rfl) ⟨287, by rfl⟩) (B 575 (by norm_num) ⟨287, by rfl⟩ (by norm_num))
theorem R98137 : Reach 98137 := rs (se 2 (by rfl) ⟨36801, by rfl⟩) (B 73603 (by norm_num) ⟨36801, by rfl⟩ (by norm_num))
theorem R98141 : Reach 98141 := rs (se 3 (by rfl) ⟨18401, by rfl⟩) (B 36803 (by norm_num) ⟨18401, by rfl⟩ (by norm_num))
theorem R98145 : Reach 98145 := rs (se 2 (by rfl) ⟨36804, by rfl⟩) (B 73609 (by norm_num) ⟨36804, by rfl⟩ (by norm_num))
theorem R98149 : Reach 98149 := rs (se 4 (by rfl) ⟨9201, by rfl⟩) (B 18403 (by norm_num) ⟨9201, by rfl⟩ (by norm_num))
theorem R98153 : Reach 98153 := rs (se 2 (by rfl) ⟨36807, by rfl⟩) (B 73615 (by norm_num) ⟨36807, by rfl⟩ (by norm_num))
theorem R98157 : Reach 98157 := rs (se 3 (by rfl) ⟨18404, by rfl⟩) (B 36809 (by norm_num) ⟨18404, by rfl⟩ (by norm_num))
theorem R98161 : Reach 98161 := rs (se 2 (by rfl) ⟨36810, by rfl⟩) (B 73621 (by norm_num) ⟨36810, by rfl⟩ (by norm_num))
theorem R98165 : Reach 98165 := rs (se 5 (by rfl) ⟨4601, by rfl⟩) (B 9203 (by norm_num) ⟨4601, by rfl⟩ (by norm_num))
theorem R98169 : Reach 98169 := rs (se 2 (by rfl) ⟨36813, by rfl⟩) (B 73627 (by norm_num) ⟨36813, by rfl⟩ (by norm_num))
theorem R98173 : Reach 98173 := rs (se 3 (by rfl) ⟨18407, by rfl⟩) (B 36815 (by norm_num) ⟨18407, by rfl⟩ (by norm_num))
theorem R98177 : Reach 98177 := rs (se 2 (by rfl) ⟨36816, by rfl⟩) (B 73633 (by norm_num) ⟨36816, by rfl⟩ (by norm_num))
theorem R98181 : Reach 98181 := rs (se 4 (by rfl) ⟨9204, by rfl⟩) (B 18409 (by norm_num) ⟨9204, by rfl⟩ (by norm_num))
theorem R98185 : Reach 98185 := rs (se 2 (by rfl) ⟨36819, by rfl⟩) (B 73639 (by norm_num) ⟨36819, by rfl⟩ (by norm_num))
theorem R98189 : Reach 98189 := rs (se 3 (by rfl) ⟨18410, by rfl⟩) (B 36821 (by norm_num) ⟨18410, by rfl⟩ (by norm_num))
theorem R98193 : Reach 98193 := rs (se 2 (by rfl) ⟨36822, by rfl⟩) (B 73645 (by norm_num) ⟨36822, by rfl⟩ (by norm_num))
theorem R98197 : Reach 98197 := rs (se 6 (by rfl) ⟨2301, by rfl⟩) (B 4603 (by norm_num) ⟨2301, by rfl⟩ (by norm_num))
theorem R98201 : Reach 98201 := rs (se 2 (by rfl) ⟨36825, by rfl⟩) (B 73651 (by norm_num) ⟨36825, by rfl⟩ (by norm_num))
theorem R229277 : Reach 229277 := rs (se 3 (by rfl) ⟨42989, by rfl⟩) (B 85979 (by norm_num) ⟨42989, by rfl⟩ (by norm_num))
theorem R163741 : Reach 163741 := rs (se 3 (by rfl) ⟨30701, by rfl⟩) (B 61403 (by norm_num) ⟨30701, by rfl⟩ (by norm_num))
theorem R98205 : Reach 98205 := rs (se 3 (by rfl) ⟨18413, by rfl⟩) (B 36827 (by norm_num) ⟨18413, by rfl⟩ (by norm_num))
theorem R98209 : Reach 98209 := rs (se 2 (by rfl) ⟨36828, by rfl⟩) (B 73657 (by norm_num) ⟨36828, by rfl⟩ (by norm_num))
theorem R98213 : Reach 98213 := rs (se 4 (by rfl) ⟨9207, by rfl⟩) (B 18415 (by norm_num) ⟨9207, by rfl⟩ (by norm_num))
theorem R98217 : Reach 98217 := rs (se 2 (by rfl) ⟨36831, by rfl⟩) (B 73663 (by norm_num) ⟨36831, by rfl⟩ (by norm_num))
theorem R98221 : Reach 98221 := rs (se 3 (by rfl) ⟨18416, by rfl⟩) (B 36833 (by norm_num) ⟨18416, by rfl⟩ (by norm_num))
theorem R98225 : Reach 98225 := rs (se 2 (by rfl) ⟨36834, by rfl⟩) (B 73669 (by norm_num) ⟨36834, by rfl⟩ (by norm_num))
theorem R98229 : Reach 98229 := rs (se 5 (by rfl) ⟨4604, by rfl⟩) (B 9209 (by norm_num) ⟨4604, by rfl⟩ (by norm_num))
theorem R98233 : Reach 98233 := rs (se 2 (by rfl) ⟨36837, by rfl⟩) (B 73675 (by norm_num) ⟨36837, by rfl⟩ (by norm_num))
theorem R98237 : Reach 98237 := rs (se 3 (by rfl) ⟨18419, by rfl⟩) (B 36839 (by norm_num) ⟨18419, by rfl⟩ (by norm_num))
theorem R98241 : Reach 98241 := rs (se 2 (by rfl) ⟨36840, by rfl⟩) (B 73681 (by norm_num) ⟨36840, by rfl⟩ (by norm_num))
theorem R98245 : Reach 98245 := rs (se 4 (by rfl) ⟨9210, by rfl⟩) (B 18421 (by norm_num) ⟨9210, by rfl⟩ (by norm_num))
theorem R98249 : Reach 98249 := rs (se 2 (by rfl) ⟨36843, by rfl⟩) (B 73687 (by norm_num) ⟨36843, by rfl⟩ (by norm_num))
theorem R98253 : Reach 98253 := rs (se 3 (by rfl) ⟨18422, by rfl⟩) (B 36845 (by norm_num) ⟨18422, by rfl⟩ (by norm_num))
theorem R98257 : Reach 98257 := rs (se 2 (by rfl) ⟨36846, by rfl⟩) (B 73693 (by norm_num) ⟨36846, by rfl⟩ (by norm_num))
theorem R98261 : Reach 98261 := rs (se 7 (by rfl) ⟨1151, by rfl⟩) (B 2303 (by norm_num) ⟨1151, by rfl⟩ (by norm_num))
theorem R98265 : Reach 98265 := rs (se 2 (by rfl) ⟨36849, by rfl⟩) (B 73699 (by norm_num) ⟨36849, by rfl⟩ (by norm_num))
theorem R98269 : Reach 98269 := rs (se 3 (by rfl) ⟨18425, by rfl⟩) (B 36851 (by norm_num) ⟨18425, by rfl⟩ (by norm_num))
theorem R98273 : Reach 98273 := rs (se 2 (by rfl) ⟨36852, by rfl⟩) (B 73705 (by norm_num) ⟨36852, by rfl⟩ (by norm_num))
theorem R98277 : Reach 98277 := rs (se 4 (by rfl) ⟨9213, by rfl⟩) (B 18427 (by norm_num) ⟨9213, by rfl⟩ (by norm_num))
theorem R98281 : Reach 98281 := rs (se 2 (by rfl) ⟨36855, by rfl⟩) (B 73711 (by norm_num) ⟨36855, by rfl⟩ (by norm_num))
theorem R98285 : Reach 98285 := rs (se 3 (by rfl) ⟨18428, by rfl⟩) (B 36857 (by norm_num) ⟨18428, by rfl⟩ (by norm_num))
theorem R98289 : Reach 98289 := rs (se 2 (by rfl) ⟨36858, by rfl⟩) (B 73717 (by norm_num) ⟨36858, by rfl⟩ (by norm_num))
theorem R163829 : Reach 163829 := rs (se 5 (by rfl) ⟨7679, by rfl⟩) (B 15359 (by norm_num) ⟨7679, by rfl⟩ (by norm_num))
theorem R262133 : Reach 262133 := rs (se 5 (by rfl) ⟨12287, by rfl⟩) (B 24575 (by norm_num) ⟨12287, by rfl⟩ (by norm_num))
theorem R98293 : Reach 98293 := rs (se 5 (by rfl) ⟨4607, by rfl⟩) (B 9215 (by norm_num) ⟨4607, by rfl⟩ (by norm_num))
theorem R98301 : Reach 98301 := rs (se 3 (by rfl) ⟨18431, by rfl⟩) (B 36863 (by norm_num) ⟨18431, by rfl⟩ (by norm_num))
theorem R98307 : Reach 98307 := rs (se 1 (by rfl) ⟨73730, by rfl⟩) R147461
theorem R98323 : Reach 98323 := rs (se 1 (by rfl) ⟨73742, by rfl⟩) R147485
theorem R98339 : Reach 98339 := rs (se 1 (by rfl) ⟨73754, by rfl⟩) R147509
theorem R327725 : Reach 327725 := rs (se 3 (by rfl) ⟨61448, by rfl⟩) R122897
theorem R98355 : Reach 98355 := rs (se 1 (by rfl) ⟨73766, by rfl⟩) R147533
theorem R98371 : Reach 98371 := rs (se 1 (by rfl) ⟨73778, by rfl⟩) R147557
theorem R98387 : Reach 98387 := rs (se 1 (by rfl) ⟨73790, by rfl⟩) R147581
theorem R163937 : Reach 163937 := rs (se 2 (by rfl) ⟨61476, by rfl⟩) R122953
theorem R327779 : Reach 327779 := rs (se 1 (by rfl) ⟨245834, by rfl⟩) R491669
theorem R98403 : Reach 98403 := rs (se 1 (by rfl) ⟨73802, by rfl⟩) R147605
theorem R262253 : Reach 262253 := rs (se 3 (by rfl) ⟨49172, by rfl⟩) R98345
theorem R98419 : Reach 98419 := rs (se 1 (by rfl) ⟨73814, by rfl⟩) R147629
theorem R98435 : Reach 98435 := rs (se 1 (by rfl) ⟨73826, by rfl⟩) R147653
theorem R98451 : Reach 98451 := rs (se 1 (by rfl) ⟨73838, by rfl⟩) R147677
theorem R98467 : Reach 98467 := rs (se 1 (by rfl) ⟨73850, by rfl⟩) R147701
theorem R98483 : Reach 98483 := rs (se 1 (by rfl) ⟨73862, by rfl⟩) R147725
theorem R98499 : Reach 98499 := rs (se 1 (by rfl) ⟨73874, by rfl⟩) R147749
theorem R262349 : Reach 262349 := rs (se 3 (by rfl) ⟨49190, by rfl⟩) R98381
theorem R98515 : Reach 98515 := rs (se 1 (by rfl) ⟨73886, by rfl⟩) R147773
theorem R164065 : Reach 164065 := rs (se 2 (by rfl) ⟨61524, by rfl⟩) R123049
theorem R98531 : Reach 98531 := rs (se 1 (by rfl) ⟨73898, by rfl⟩) R147797
theorem R98547 : Reach 98547 := rs (se 1 (by rfl) ⟨73910, by rfl⟩) R147821
theorem R164099 : Reach 164099 := rs (se 1 (by rfl) ⟨123074, by rfl⟩) R246149
theorem R98563 : Reach 98563 := rs (se 1 (by rfl) ⟨73922, by rfl⟩) R147845
theorem R98579 : Reach 98579 := rs (se 1 (by rfl) ⟨73934, by rfl⟩) R147869
theorem R262435 : Reach 262435 := rs (se 1 (by rfl) ⟨196826, by rfl⟩) R393653
theorem R98595 : Reach 98595 := rs (se 1 (by rfl) ⟨73946, by rfl⟩) R147893
theorem R98611 : Reach 98611 := rs (se 1 (by rfl) ⟨73958, by rfl⟩) R147917
theorem R98627 : Reach 98627 := rs (se 1 (by rfl) ⟨73970, by rfl⟩) R147941
theorem R98643 : Reach 98643 := rs (se 1 (by rfl) ⟨73982, by rfl⟩) R147965
theorem R98659 : Reach 98659 := rs (se 1 (by rfl) ⟨73994, by rfl⟩) R147989
theorem R328049 : Reach 328049 := rs (se 2 (by rfl) ⟨123018, by rfl⟩) R246037
theorem R98675 : Reach 98675 := rs (se 1 (by rfl) ⟨74006, by rfl⟩) R148013
theorem R164227 : Reach 164227 := rs (se 1 (by rfl) ⟨123170, by rfl⟩) R246341
theorem R98691 : Reach 98691 := rs (se 1 (by rfl) ⟨74018, by rfl⟩) R148037
theorem R131473 : Reach 131473 := rs (se 2 (by rfl) ⟨49302, by rfl⟩) R98605
theorem R98707 : Reach 98707 := rs (se 1 (by rfl) ⟨74030, by rfl⟩) R148061
theorem R98723 : Reach 98723 := rs (se 1 (by rfl) ⟨74042, by rfl⟩) R148085
theorem R98739 : Reach 98739 := rs (se 1 (by rfl) ⟨74054, by rfl⟩) R148109
theorem R98755 : Reach 98755 := rs (se 1 (by rfl) ⟨74066, by rfl⟩) R148133
theorem R98771 : Reach 98771 := rs (se 1 (by rfl) ⟨74078, by rfl⟩) R148157
theorem R98787 : Reach 98787 := rs (se 1 (by rfl) ⟨74090, by rfl⟩) R148181
theorem R98803 : Reach 98803 := rs (se 1 (by rfl) ⟨74102, by rfl⟩) R148205
theorem R98819 : Reach 98819 := rs (se 1 (by rfl) ⟨74114, by rfl⟩) R148229
theorem R328205 : Reach 328205 := rs (se 3 (by rfl) ⟨61538, by rfl⟩) R123077
theorem R164369 : Reach 164369 := rs (se 2 (by rfl) ⟨61638, by rfl⟩) R123277
theorem R98835 : Reach 98835 := rs (se 1 (by rfl) ⟨74126, by rfl⟩) R148253
theorem R557603 : Reach 557603 := rs (se 1 (by rfl) ⟨418202, by rfl⟩) R836405
theorem R98851 : Reach 98851 := rs (se 1 (by rfl) ⟨74138, by rfl⟩) R148277
theorem R98867 : Reach 98867 := rs (se 1 (by rfl) ⟨74150, by rfl⟩) R148301
theorem R98883 : Reach 98883 := rs (se 1 (by rfl) ⟨74162, by rfl⟩) R148325
theorem R787013 : Reach 787013 := rs (se 4 (by rfl) ⟨73782, by rfl⟩) R147565
theorem R229969 : Reach 229969 := rs (se 2 (by rfl) ⟨86238, by rfl⟩) R172477
theorem R98899 : Reach 98899 := rs (se 1 (by rfl) ⟨74174, by rfl⟩) R148349
theorem R98915 : Reach 98915 := rs (se 1 (by rfl) ⟨74186, by rfl⟩) R148373
theorem R98931 : Reach 98931 := rs (se 1 (by rfl) ⟨74198, by rfl⟩) R148397
theorem R98947 : Reach 98947 := rs (se 1 (by rfl) ⟨74210, by rfl⟩) R148421
theorem R164497 : Reach 164497 := rs (se 2 (by rfl) ⟨61686, by rfl⟩) R123373
theorem R98963 : Reach 98963 := rs (se 1 (by rfl) ⟨74222, by rfl⟩) R148445
theorem R98979 : Reach 98979 := rs (se 1 (by rfl) ⟨74234, by rfl⟩) R148469
theorem R164531 : Reach 164531 := rs (se 1 (by rfl) ⟨123398, by rfl⟩) R246797
theorem R98995 : Reach 98995 := rs (se 1 (by rfl) ⟨74246, by rfl⟩) R148493
theorem R99011 : Reach 99011 := rs (se 1 (by rfl) ⟨74258, by rfl⟩) R148517
theorem R99027 : Reach 99027 := rs (se 1 (by rfl) ⟨74270, by rfl⟩) R148541
theorem R99043 : Reach 99043 := rs (se 1 (by rfl) ⟨74282, by rfl⟩) R148565
theorem R99059 : Reach 99059 := rs (se 1 (by rfl) ⟨74294, by rfl⟩) R148589
theorem R99075 : Reach 99075 := rs (se 1 (by rfl) ⟨74306, by rfl⟩) R148613
theorem R99091 : Reach 99091 := rs (se 1 (by rfl) ⟨74318, by rfl⟩) R148637
theorem R99107 : Reach 99107 := rs (se 1 (by rfl) ⟨74330, by rfl⟩) R148661
theorem R164659 : Reach 164659 := rs (se 1 (by rfl) ⟨123494, by rfl⟩) R246989
theorem R99123 : Reach 99123 := rs (se 1 (by rfl) ⟨74342, by rfl⟩) R148685
theorem R623501 : Reach 623501 := rs (se 3 (by rfl) ⟨116906, by rfl⟩) R233813
theorem R328589 : Reach 328589 := rs (se 3 (by rfl) ⟨61610, by rfl⟩) R123221
theorem R164801 : Reach 164801 := rs (se 2 (by rfl) ⟨61800, by rfl⟩) R123601
theorem R328643 : Reach 328643 := rs (se 1 (by rfl) ⟨246482, by rfl⟩) R492965
theorem R164929 : Reach 164929 := rs (se 2 (by rfl) ⟨61848, by rfl⟩) R123697
theorem R164963 : Reach 164963 := rs (se 1 (by rfl) ⟨123722, by rfl⟩) R247445
theorem R263299 : Reach 263299 := rs (se 1 (by rfl) ⟨197474, by rfl⟩) R394949
theorem R328913 : Reach 328913 := rs (se 2 (by rfl) ⟨123342, by rfl⟩) R246685
theorem R165091 : Reach 165091 := rs (se 1 (by rfl) ⟨123818, by rfl⟩) R247637
theorem R132385 : Reach 132385 := rs (se 2 (by rfl) ⟨49644, by rfl⟩) R99289
theorem R886085 : Reach 886085 := rs (se 4 (by rfl) ⟨83070, by rfl⟩) R166141
theorem R165233 : Reach 165233 := rs (se 2 (by rfl) ⟨61962, by rfl⟩) R123925
theorem R165281 : Reach 165281 := rs (se 2 (by rfl) ⟨61980, by rfl⟩) R123961
theorem R165361 : Reach 165361 := rs (se 2 (by rfl) ⟨62010, by rfl⟩) R124021
theorem R165395 : Reach 165395 := rs (se 1 (by rfl) ⟨124046, by rfl⟩) R248093
theorem R165523 : Reach 165523 := rs (se 1 (by rfl) ⟨124142, by rfl⟩) R248285
theorem R329453 : Reach 329453 := rs (se 3 (by rfl) ⟨61772, by rfl⟩) R123545
theorem R165665 : Reach 165665 := rs (se 2 (by rfl) ⟨62124, by rfl⟩) R124249
theorem R329507 : Reach 329507 := rs (se 1 (by rfl) ⟨247130, by rfl⟩) R494261
theorem R132899 : Reach 132899 := rs (se 1 (by rfl) ⟨99674, by rfl⟩) R199349
theorem R853901 : Reach 853901 := rs (se 3 (by rfl) ⟨160106, by rfl⟩) R320213
theorem R165793 : Reach 165793 := rs (se 2 (by rfl) ⟨62172, by rfl⟩) R124345
theorem R165827 : Reach 165827 := rs (se 1 (by rfl) ⟨124370, by rfl⟩) R248741
theorem R329777 : Reach 329777 := rs (se 2 (by rfl) ⟨123666, by rfl⟩) R247333
theorem R165955 : Reach 165955 := rs (se 1 (by rfl) ⟨124466, by rfl⟩) R248933
theorem R526513 : Reach 526513 := rs (se 2 (by rfl) ⟨197442, by rfl⟩) R394885
theorem R166097 : Reach 166097 := rs (se 2 (by rfl) ⟨62286, by rfl⟩) R124573
theorem R362723 : Reach 362723 := rs (se 1 (by rfl) ⟨272042, by rfl⟩) R544085
theorem R166225 : Reach 166225 := rs (se 2 (by rfl) ⟨62334, by rfl⟩) R124669
theorem R493937 : Reach 493937 := rs (se 2 (by rfl) ⟨185226, by rfl⟩) R370453
theorem R166259 : Reach 166259 := rs (se 1 (by rfl) ⟨124694, by rfl⟩) R249389
theorem R297379 : Reach 297379 := rs (se 1 (by rfl) ⟨223034, by rfl⟩) R446069
theorem R166387 : Reach 166387 := rs (se 1 (by rfl) ⟨124790, by rfl⟩) R249581
theorem R330317 : Reach 330317 := rs (se 3 (by rfl) ⟨61934, by rfl⟩) R123869
theorem R166529 : Reach 166529 := rs (se 2 (by rfl) ⟨62448, by rfl⟩) R124897
theorem R330371 : Reach 330371 := rs (se 1 (by rfl) ⟨247778, by rfl⟩) R495557
theorem R363149 : Reach 363149 := rs (se 3 (by rfl) ⟨68090, by rfl⟩) R136181
theorem R723653 : Reach 723653 := rs (se 4 (by rfl) ⟨67842, by rfl⟩) R135685
theorem R166657 : Reach 166657 := rs (se 2 (by rfl) ⟨62496, by rfl⟩) R124993
theorem R166691 : Reach 166691 := rs (se 1 (by rfl) ⟨125018, by rfl⟩) R250037
theorem R330641 : Reach 330641 := rs (se 2 (by rfl) ⟨123990, by rfl⟩) R247981
theorem R166819 : Reach 166819 := rs (se 1 (by rfl) ⟨125114, by rfl⟩) R250229
theorem R166961 : Reach 166961 := rs (se 2 (by rfl) ⟨62610, by rfl⟩) R125221
theorem R920645 : Reach 920645 := rs (se 4 (by rfl) ⟨86310, by rfl⟩) R172621
theorem R167089 : Reach 167089 := rs (se 2 (by rfl) ⟨62658, by rfl⟩) R125317
theorem R167123 : Reach 167123 := rs (se 1 (by rfl) ⟨125342, by rfl⟩) R250685
theorem R593201 : Reach 593201 := rs (se 2 (by rfl) ⟨222450, by rfl⟩) R444901
theorem R167251 : Reach 167251 := rs (se 1 (by rfl) ⟨125438, by rfl⟩) R250877
theorem R101747 : Reach 101747 := rs (se 1 (by rfl) ⟨76310, by rfl⟩) R152621
theorem R331181 : Reach 331181 := rs (se 3 (by rfl) ⟨62096, by rfl⟩) R124193
theorem R363953 : Reach 363953 := rs (se 2 (by rfl) ⟨136482, by rfl⟩) R272965
theorem R331235 : Reach 331235 := rs (se 1 (by rfl) ⟨248426, by rfl⟩) R496853
theorem R691811 : Reach 691811 := rs (se 1 (by rfl) ⟨518858, by rfl⟩) R1037717
theorem R790157 : Reach 790157 := rs (se 3 (by rfl) ⟨148154, by rfl⟩) R296309
theorem R167633 : Reach 167633 := rs (se 2 (by rfl) ⟨62862, by rfl⟩) R125725
theorem R331505 : Reach 331505 := rs (se 2 (by rfl) ⟨124314, by rfl⟩) R248629
theorem R495395 : Reach 495395 := rs (se 1 (by rfl) ⟨371546, by rfl⟩) R743093
theorem R560965 : Reach 560965 := rs (se 4 (by rfl) ⟨52590, by rfl⟩) R105181
theorem R331793 : Reach 331793 := rs (se 2 (by rfl) ⟨124422, by rfl⟩) R248845
theorem R364621 : Reach 364621 := rs (se 3 (by rfl) ⟨68366, by rfl⟩) R136733
theorem R626885 : Reach 626885 := rs (se 4 (by rfl) ⟨58770, by rfl⟩) R117541
theorem R332045 : Reach 332045 := rs (se 3 (by rfl) ⟨62258, by rfl⟩) R124517
theorem R1544501 : Reach 1544501 := rs (se 5 (by rfl) ⟨72398, by rfl⟩) R144797
theorem R332099 : Reach 332099 := rs (se 1 (by rfl) ⟨249074, by rfl⟩) R498149
theorem R102755 : Reach 102755 := rs (se 1 (by rfl) ⟨77066, by rfl⟩) R154133
theorem R266609 : Reach 266609 := rs (se 2 (by rfl) ⟨99978, by rfl⟩) R199957
theorem R233891 : Reach 233891 := rs (se 1 (by rfl) ⟨175418, by rfl⟩) R350837
theorem R135697 : Reach 135697 := rs (se 2 (by rfl) ⟨50886, by rfl⟩) R101773
theorem R496205 : Reach 496205 := rs (se 3 (by rfl) ⟨93038, by rfl⟩) R186077
theorem R332369 : Reach 332369 := rs (se 2 (by rfl) ⟨124638, by rfl⟩) R249277
theorem R1053283 : Reach 1053283 := rs (se 1 (by rfl) ⟨789962, by rfl⟩) R1579925
theorem R365411 : Reach 365411 := rs (se 1 (by rfl) ⟨274058, by rfl⟩) R548117
theorem R136289 : Reach 136289 := rs (se 2 (by rfl) ⟨51108, by rfl⟩) R102217
theorem R332909 : Reach 332909 := rs (se 3 (by rfl) ⟨62420, by rfl⟩) R124841
theorem R2823281 : Reach 2823281 := rs (se 2 (by rfl) ⟨1058730, by rfl⟩) R2117461
theorem R234659 : Reach 234659 := rs (se 1 (by rfl) ⟨175994, by rfl⟩) R351989
theorem R332963 : Reach 332963 := rs (se 1 (by rfl) ⟨249722, by rfl⟩) R499445
theorem R267533 : Reach 267533 := rs (se 3 (by rfl) ⟨50162, by rfl⟩) R100325
theorem R169393 : Reach 169393 := rs (se 2 (by rfl) ⟨63522, by rfl⟩) R127045
theorem R333233 : Reach 333233 := rs (se 2 (by rfl) ⟨124962, by rfl⟩) R249925
theorem R300493 : Reach 300493 := rs (se 3 (by rfl) ⟨56342, by rfl⟩) R112685
theorem R366065 : Reach 366065 := rs (se 2 (by rfl) ⟨137274, by rfl⟩) R274549
theorem R136819 : Reach 136819 := rs (se 1 (by rfl) ⟨102614, by rfl⟩) R205229
theorem R235217 : Reach 235217 := rs (se 2 (by rfl) ⟨88206, by rfl⟩) R176413
theorem R1119971 : Reach 1119971 := rs (se 1 (by rfl) ⟨839978, by rfl⟩) R1679957
theorem R562949 : Reach 562949 := rs (se 4 (by rfl) ⟨52776, by rfl⟩) R105553
theorem R104323 : Reach 104323 := rs (se 1 (by rfl) ⟨78242, by rfl⟩) R156485
theorem R137155 : Reach 137155 := rs (se 1 (by rfl) ⟨102866, by rfl⟩) R205733
theorem R333773 : Reach 333773 := rs (se 3 (by rfl) ⟨62582, by rfl⟩) R125165
theorem R333827 : Reach 333827 := rs (se 1 (by rfl) ⟨250370, by rfl⟩) R500741
theorem R5445845 : Reach 5445845 := rs (se 7 (by rfl) ⟨63818, by rfl⟩) R127637
theorem R334097 : Reach 334097 := rs (se 2 (by rfl) ⟨125286, by rfl⟩) R250573
theorem R104771 : Reach 104771 := rs (se 1 (by rfl) ⟨78578, by rfl⟩) R157157
theorem R235889 : Reach 235889 := rs (se 2 (by rfl) ⟨88458, by rfl⟩) R176917
theorem R137713 : Reach 137713 := rs (se 2 (by rfl) ⟨51642, by rfl⟩) R103285
theorem R137747 : Reach 137747 := rs (se 1 (by rfl) ⟨103310, by rfl⟩) R206621
theorem R465763 : Reach 465763 := rs (se 1 (by rfl) ⟨349322, by rfl⟩) R698645
theorem R498545 : Reach 498545 := rs (se 2 (by rfl) ⟨186954, by rfl⟩) R373909
theorem R367523 : Reach 367523 := rs (se 1 (by rfl) ⟨275642, by rfl⟩) R551285
theorem R367537 : Reach 367537 := rs (se 2 (by rfl) ⟨137826, by rfl⟩) R275653
theorem R138305 : Reach 138305 := rs (se 2 (by rfl) ⟨51864, by rfl⟩) R103729
theorem R302221 : Reach 302221 := rs (se 3 (by rfl) ⟨56666, by rfl⟩) R113333
theorem R138385 : Reach 138385 := rs (se 2 (by rfl) ⟨51894, by rfl⟩) R103789
theorem R499121 : Reach 499121 := rs (se 2 (by rfl) ⟨187170, by rfl⟩) R374341
theorem R630449 : Reach 630449 := rs (se 2 (by rfl) ⟨236418, by rfl⟩) R472837
theorem R3710861 : Reach 3710861 := rs (se 3 (by rfl) ⟨695786, by rfl⟩) R1391573
theorem R204707 : Reach 204707 := rs (se 1 (by rfl) ⟨153530, by rfl⟩) R307061
theorem R139171 : Reach 139171 := rs (se 1 (by rfl) ⟨104378, by rfl⟩) R208757
theorem R237649 : Reach 237649 := rs (se 2 (by rfl) ⟨89118, by rfl⟩) R178237
theorem R368995 : Reach 368995 := rs (se 1 (by rfl) ⟨276746, by rfl⟩) R553493
theorem R1122659 : Reach 1122659 := rs (se 1 (by rfl) ⟨841994, by rfl⟩) R1683989
theorem R1188209 : Reach 1188209 := rs (se 2 (by rfl) ⟨445578, by rfl⟩) R891157
theorem R139649 : Reach 139649 := rs (se 2 (by rfl) ⟨52368, by rfl⟩) R104737
theorem R729485 : Reach 729485 := rs (se 3 (by rfl) ⟨136778, by rfl⟩) R273557
theorem R565667 : Reach 565667 := rs (se 1 (by rfl) ⟨424250, by rfl⟩) R848501
theorem R139763 : Reach 139763 := rs (se 1 (by rfl) ⟨104822, by rfl⟩) R209645
theorem R107059 : Reach 107059 := rs (se 1 (by rfl) ⟨80294, by rfl⟩) R160589
theorem R139843 : Reach 139843 := rs (se 1 (by rfl) ⟨104882, by rfl⟩) R209765
theorem R107203 : Reach 107203 := rs (se 1 (by rfl) ⟨80402, by rfl⟩) R160805
theorem R205571 : Reach 205571 := rs (se 1 (by rfl) ⟨154178, by rfl⟩) R308357
theorem R107347 : Reach 107347 := rs (se 1 (by rfl) ⟨80510, by rfl⟩) R161021
theorem R500579 : Reach 500579 := rs (se 1 (by rfl) ⟨375434, by rfl⟩) R750869
theorem R205681 : Reach 205681 := rs (se 2 (by rfl) ⟨77130, by rfl⟩) R154261
theorem R107491 : Reach 107491 := rs (se 1 (by rfl) ⟨80618, by rfl⟩) R161237
theorem R631907 : Reach 631907 := rs (se 1 (by rfl) ⟨473930, by rfl⟩) R947861
theorem R140401 : Reach 140401 := rs (se 2 (by rfl) ⟨52650, by rfl⟩) R105301
theorem R107635 : Reach 107635 := rs (se 1 (by rfl) ⟨80726, by rfl⟩) R161453
theorem R107779 : Reach 107779 := rs (se 1 (by rfl) ⟨80834, by rfl⟩) R161669
theorem R271633 : Reach 271633 := rs (se 2 (by rfl) ⟨101862, by rfl⟩) R203725
theorem R107923 : Reach 107923 := rs (se 1 (by rfl) ⟨80942, by rfl⟩) R161885
theorem R271907 : Reach 271907 := rs (se 1 (by rfl) ⟨203930, by rfl⟩) R407861
theorem R108067 : Reach 108067 := rs (se 1 (by rfl) ⟨81050, by rfl⟩) R162101
theorem R501389 : Reach 501389 := rs (se 3 (by rfl) ⟨94010, by rfl⟩) R188021
theorem R206513 : Reach 206513 := rs (se 2 (by rfl) ⟨77442, by rfl⟩) R154885
theorem R108211 : Reach 108211 := rs (se 1 (by rfl) ⟨81158, by rfl⟩) R162317
theorem R272099 : Reach 272099 := rs (se 1 (by rfl) ⟨204074, by rfl⟩) R408149
theorem R141107 : Reach 141107 := rs (se 1 (by rfl) ⟨105830, by rfl⟩) R211661
theorem R108355 : Reach 108355 := rs (se 1 (by rfl) ⟨81266, by rfl⟩) R162533
theorem R206723 : Reach 206723 := rs (se 1 (by rfl) ⟨155042, by rfl⟩) R310085
theorem R108499 : Reach 108499 := rs (se 1 (by rfl) ⟨81374, by rfl⟩) R162749
theorem R108643 : Reach 108643 := rs (se 1 (by rfl) ⟨81482, by rfl⟩) R162965
theorem R108787 : Reach 108787 := rs (se 1 (by rfl) ⟨81590, by rfl⟩) R163181
theorem R174467 : Reach 174467 := rs (se 1 (by rfl) ⟨130850, by rfl⟩) R261701
theorem R108931 : Reach 108931 := rs (se 1 (by rfl) ⟨81698, by rfl⟩) R163397
theorem R272909 : Reach 272909 := rs (se 3 (by rfl) ⟨51170, by rfl⟩) R102341
theorem R371213 : Reach 371213 := rs (se 3 (by rfl) ⟨69602, by rfl⟩) R139205
theorem R109075 : Reach 109075 := rs (se 1 (by rfl) ⟨81806, by rfl⟩) R163613
theorem R436877 : Reach 436877 := rs (se 3 (by rfl) ⟨81914, by rfl⟩) R163829
theorem R174755 : Reach 174755 := rs (se 1 (by rfl) ⟨131066, by rfl⟩) R262133
theorem R109219 : Reach 109219 := rs (se 1 (by rfl) ⟨81914, by rfl⟩) R163829
theorem R273091 : Reach 273091 := rs (se 1 (by rfl) ⟨204818, by rfl⟩) R409637
theorem R109363 : Reach 109363 := rs (se 1 (by rfl) ⟨82022, by rfl⟩) R164045
theorem R207697 : Reach 207697 := rs (se 2 (by rfl) ⟨77886, by rfl⟩) R155773
theorem R109507 : Reach 109507 := rs (se 1 (by rfl) ⟨82130, by rfl⟩) R164261
theorem R2698211 : Reach 2698211 := rs (se 1 (by rfl) ⟨2023658, by rfl⟩) R4047317
theorem R109651 : Reach 109651 := rs (se 1 (by rfl) ⟨82238, by rfl⟩) R164477
theorem R306317 : Reach 306317 := rs (se 3 (by rfl) ⟨57434, by rfl⟩) R114869
theorem R240803 : Reach 240803 := rs (se 1 (by rfl) ⟨180602, by rfl⟩) R361205
theorem R273581 : Reach 273581 := rs (se 3 (by rfl) ⟨51296, by rfl⟩) R102593
theorem R208099 : Reach 208099 := rs (se 1 (by rfl) ⟨156074, by rfl⟩) R312149
theorem R109795 : Reach 109795 := rs (se 1 (by rfl) ⟨82346, by rfl⟩) R164693
theorem R732401 : Reach 732401 := rs (se 2 (by rfl) ⟨274650, by rfl⟩) R549301
theorem R240995 : Reach 240995 := rs (se 1 (by rfl) ⟨180746, by rfl⟩) R361493
theorem R109939 : Reach 109939 := rs (se 1 (by rfl) ⟨82454, by rfl⟩) R164909
theorem R142721 : Reach 142721 := rs (se 2 (by rfl) ⟨53520, by rfl⟩) R107041
theorem R142739 : Reach 142739 := rs (se 1 (by rfl) ⟨107054, by rfl⟩) R214109
theorem R142769 : Reach 142769 := rs (se 2 (by rfl) ⟨53538, by rfl⟩) R107077
theorem R142787 : Reach 142787 := rs (se 1 (by rfl) ⟨107090, by rfl⟩) R214181
theorem R142817 : Reach 142817 := rs (se 2 (by rfl) ⟨53556, by rfl⟩) R107113
theorem R142835 : Reach 142835 := rs (se 1 (by rfl) ⟨107126, by rfl⟩) R214253
theorem R110083 : Reach 110083 := rs (se 1 (by rfl) ⟨82562, by rfl⟩) R165125
theorem R142865 : Reach 142865 := rs (se 2 (by rfl) ⟨53574, by rfl⟩) R107149
theorem R142883 : Reach 142883 := rs (se 1 (by rfl) ⟨107162, by rfl⟩) R214325
theorem R142913 : Reach 142913 := rs (se 2 (by rfl) ⟨53592, by rfl⟩) R107185
theorem R142931 : Reach 142931 := rs (se 1 (by rfl) ⟨107198, by rfl⟩) R214397
theorem R142961 : Reach 142961 := rs (se 2 (by rfl) ⟨53610, by rfl⟩) R107221
theorem R142979 : Reach 142979 := rs (se 1 (by rfl) ⟨107234, by rfl⟩) R214469
theorem R110227 : Reach 110227 := rs (se 1 (by rfl) ⟨82670, by rfl⟩) R165341
theorem R143009 : Reach 143009 := rs (se 2 (by rfl) ⟨53628, by rfl⟩) R107257
theorem R143027 : Reach 143027 := rs (se 1 (by rfl) ⟨107270, by rfl⟩) R214541
theorem R143057 : Reach 143057 := rs (se 2 (by rfl) ⟨53646, by rfl⟩) R107293
theorem R143075 : Reach 143075 := rs (se 1 (by rfl) ⟨107306, by rfl⟩) R214613
theorem R143105 : Reach 143105 := rs (se 2 (by rfl) ⟨53664, by rfl⟩) R107329
theorem R143123 : Reach 143123 := rs (se 1 (by rfl) ⟨107342, by rfl⟩) R214685
theorem R110371 : Reach 110371 := rs (se 1 (by rfl) ⟨82778, by rfl⟩) R165557
theorem R143153 : Reach 143153 := rs (se 2 (by rfl) ⟨53682, by rfl⟩) R107365
theorem R143171 : Reach 143171 := rs (se 1 (by rfl) ⟨107378, by rfl⟩) R214757
theorem R143201 : Reach 143201 := rs (se 2 (by rfl) ⟨53700, by rfl⟩) R107401
theorem R143219 : Reach 143219 := rs (se 1 (by rfl) ⟨107414, by rfl⟩) R214829
theorem R143249 : Reach 143249 := rs (se 2 (by rfl) ⟨53718, by rfl⟩) R107437
theorem R143267 : Reach 143267 := rs (se 1 (by rfl) ⟨107450, by rfl⟩) R214901
theorem R110515 : Reach 110515 := rs (se 1 (by rfl) ⟨82886, by rfl⟩) R165773
theorem R143297 : Reach 143297 := rs (se 2 (by rfl) ⟨53736, by rfl⟩) R107473
theorem R143315 : Reach 143315 := rs (se 1 (by rfl) ⟨107486, by rfl⟩) R214973
theorem R143345 : Reach 143345 := rs (se 2 (by rfl) ⟨53754, by rfl⟩) R107509
theorem R143363 : Reach 143363 := rs (se 1 (by rfl) ⟨107522, by rfl⟩) R215045
theorem R143393 : Reach 143393 := rs (se 2 (by rfl) ⟨53772, by rfl⟩) R107545
theorem R143411 : Reach 143411 := rs (se 1 (by rfl) ⟨107558, by rfl⟩) R215117
theorem R110659 : Reach 110659 := rs (se 1 (by rfl) ⟨82994, by rfl⟩) R165989
theorem R143441 : Reach 143441 := rs (se 2 (by rfl) ⟨53790, by rfl⟩) R107581
theorem R143459 : Reach 143459 := rs (se 1 (by rfl) ⟨107594, by rfl⟩) R215189
theorem R143489 : Reach 143489 := rs (se 2 (by rfl) ⟨53808, by rfl⟩) R107617
theorem R143507 : Reach 143507 := rs (se 1 (by rfl) ⟨107630, by rfl⟩) R215261
theorem R143537 : Reach 143537 := rs (se 2 (by rfl) ⟨53826, by rfl⟩) R107653
theorem R143555 : Reach 143555 := rs (se 1 (by rfl) ⟨107666, by rfl⟩) R215333
theorem R110803 : Reach 110803 := rs (se 1 (by rfl) ⟨83102, by rfl⟩) R166205
theorem R143585 : Reach 143585 := rs (se 2 (by rfl) ⟨53844, by rfl⟩) R107689
theorem R143603 : Reach 143603 := rs (se 1 (by rfl) ⟨107702, by rfl⟩) R215405
theorem R241937 : Reach 241937 := rs (se 2 (by rfl) ⟨90726, by rfl⟩) R181453
theorem R143633 : Reach 143633 := rs (se 2 (by rfl) ⟨53862, by rfl⟩) R107725
theorem R143651 : Reach 143651 := rs (se 1 (by rfl) ⟨107738, by rfl⟩) R215477
theorem R143681 : Reach 143681 := rs (se 2 (by rfl) ⟨53880, by rfl⟩) R107761
theorem R241987 : Reach 241987 := rs (se 1 (by rfl) ⟨181490, by rfl⟩) R362981
theorem R274765 : Reach 274765 := rs (se 3 (by rfl) ⟨51518, by rfl⟩) R103037
theorem R143699 : Reach 143699 := rs (se 1 (by rfl) ⟨107774, by rfl⟩) R215549
theorem R110947 : Reach 110947 := rs (se 1 (by rfl) ⟨83210, by rfl⟩) R166421
theorem R143729 : Reach 143729 := rs (se 2 (by rfl) ⟨53898, by rfl⟩) R107797
theorem R143747 : Reach 143747 := rs (se 1 (by rfl) ⟨107810, by rfl⟩) R215621
theorem R143777 : Reach 143777 := rs (se 2 (by rfl) ⟨53916, by rfl⟩) R107833
theorem R143795 : Reach 143795 := rs (se 1 (by rfl) ⟨107846, by rfl⟩) R215693
theorem R242129 : Reach 242129 := rs (se 2 (by rfl) ⟨90798, by rfl⟩) R181597
theorem R143825 : Reach 143825 := rs (se 2 (by rfl) ⟨53934, by rfl⟩) R107869
theorem R143843 : Reach 143843 := rs (se 1 (by rfl) ⟨107882, by rfl⟩) R215765
theorem R111091 : Reach 111091 := rs (se 1 (by rfl) ⟨83318, by rfl⟩) R166637
theorem R143873 : Reach 143873 := rs (se 2 (by rfl) ⟨53952, by rfl⟩) R107905
theorem R143891 : Reach 143891 := rs (se 1 (by rfl) ⟨107918, by rfl⟩) R215837
theorem R143921 : Reach 143921 := rs (se 2 (by rfl) ⟨53970, by rfl⟩) R107941
theorem R143939 : Reach 143939 := rs (se 1 (by rfl) ⟨107954, by rfl⟩) R215909
theorem R143969 : Reach 143969 := rs (se 2 (by rfl) ⟨53988, by rfl⟩) R107977
theorem R143987 : Reach 143987 := rs (se 1 (by rfl) ⟨107990, by rfl⟩) R215981
theorem R111235 : Reach 111235 := rs (se 1 (by rfl) ⟨83426, by rfl⟩) R166853
theorem R144017 : Reach 144017 := rs (se 2 (by rfl) ⟨54006, by rfl⟩) R108013
theorem R144035 : Reach 144035 := rs (se 1 (by rfl) ⟨108026, by rfl⟩) R216053
theorem R144049 : Reach 144049 := rs (se 2 (by rfl) ⟨54018, by rfl⟩) R108037
theorem R144065 : Reach 144065 := rs (se 2 (by rfl) ⟨54024, by rfl⟩) R108049
theorem R307907 : Reach 307907 := rs (se 1 (by rfl) ⟨230930, by rfl⟩) R461861
theorem R111299 : Reach 111299 := rs (se 1 (by rfl) ⟨83474, by rfl⟩) R166949
theorem R209603 : Reach 209603 := rs (se 1 (by rfl) ⟨157202, by rfl⟩) R314405
theorem R144083 : Reach 144083 := rs (se 1 (by rfl) ⟨108062, by rfl⟩) R216125
theorem R897763 : Reach 897763 := rs (se 1 (by rfl) ⟨673322, by rfl⟩) R1346645
theorem R144113 : Reach 144113 := rs (se 2 (by rfl) ⟨54042, by rfl⟩) R108085
theorem R144131 : Reach 144131 := rs (se 1 (by rfl) ⟨108098, by rfl⟩) R216197
theorem R111379 : Reach 111379 := rs (se 1 (by rfl) ⟨83534, by rfl⟩) R167069
theorem R144161 : Reach 144161 := rs (se 2 (by rfl) ⟨54060, by rfl⟩) R108121
theorem R144179 : Reach 144179 := rs (se 1 (by rfl) ⟨108134, by rfl⟩) R216269
theorem R144209 : Reach 144209 := rs (se 2 (by rfl) ⟨54078, by rfl⟩) R108157
theorem R144227 : Reach 144227 := rs (se 1 (by rfl) ⟨108170, by rfl⟩) R216341
theorem R144257 : Reach 144257 := rs (se 2 (by rfl) ⟨54096, by rfl⟩) R108193
theorem R144275 : Reach 144275 := rs (se 1 (by rfl) ⟨108206, by rfl⟩) R216413
theorem R111523 : Reach 111523 := rs (se 1 (by rfl) ⟨83642, by rfl⟩) R167285
theorem R144305 : Reach 144305 := rs (se 2 (by rfl) ⟨54114, by rfl⟩) R108229
theorem R144323 : Reach 144323 := rs (se 1 (by rfl) ⟨108242, by rfl⟩) R216485
theorem R144353 : Reach 144353 := rs (se 2 (by rfl) ⟨54132, by rfl⟩) R108265
theorem R144371 : Reach 144371 := rs (se 1 (by rfl) ⟨108278, by rfl⟩) R216557
theorem R144401 : Reach 144401 := rs (se 2 (by rfl) ⟨54150, by rfl⟩) R108301
theorem R144419 : Reach 144419 := rs (se 1 (by rfl) ⟨108314, by rfl⟩) R216629
theorem R144449 : Reach 144449 := rs (se 2 (by rfl) ⟨54168, by rfl⟩) R108337
theorem R144467 : Reach 144467 := rs (se 1 (by rfl) ⟨108350, by rfl⟩) R216701
theorem R144497 : Reach 144497 := rs (se 2 (by rfl) ⟨54186, by rfl⟩) R108373
theorem R144515 : Reach 144515 := rs (se 1 (by rfl) ⟨108386, by rfl⟩) R216773
theorem R144545 : Reach 144545 := rs (se 2 (by rfl) ⟨54204, by rfl⟩) R108409
theorem R144563 : Reach 144563 := rs (se 1 (by rfl) ⟨108422, by rfl⟩) R216845
theorem R144593 : Reach 144593 := rs (se 2 (by rfl) ⟨54222, by rfl⟩) R108445
theorem R144611 : Reach 144611 := rs (se 1 (by rfl) ⟨108458, by rfl⟩) R216917
theorem R144641 : Reach 144641 := rs (se 2 (by rfl) ⟨54240, by rfl⟩) R108481
theorem R144659 : Reach 144659 := rs (se 1 (by rfl) ⟨108494, by rfl⟩) R216989
theorem R144689 : Reach 144689 := rs (se 2 (by rfl) ⟨54258, by rfl⟩) R108517
theorem R144707 : Reach 144707 := rs (se 1 (by rfl) ⟨108530, by rfl⟩) R217061
theorem R144737 : Reach 144737 := rs (se 2 (by rfl) ⟨54276, by rfl⟩) R108553
theorem R275825 : Reach 275825 := rs (se 2 (by rfl) ⟨103434, by rfl⟩) R206869
theorem R374129 : Reach 374129 := rs (se 2 (by rfl) ⟨140298, by rfl⟩) R280597
theorem R144755 : Reach 144755 := rs (se 1 (by rfl) ⟨108566, by rfl⟩) R217133
theorem R144785 : Reach 144785 := rs (se 2 (by rfl) ⟨54294, by rfl⟩) R108589
theorem R144803 : Reach 144803 := rs (se 1 (by rfl) ⟨108602, by rfl⟩) R217205
theorem R243121 : Reach 243121 := rs (se 2 (by rfl) ⟨91170, by rfl⟩) R182341
theorem R144833 : Reach 144833 := rs (se 2 (by rfl) ⟨54312, by rfl⟩) R108625
theorem R144851 : Reach 144851 := rs (se 1 (by rfl) ⟨108638, by rfl⟩) R217277
theorem R472547 : Reach 472547 := rs (se 1 (by rfl) ⟨354410, by rfl⟩) R708821
theorem R144881 : Reach 144881 := rs (se 2 (by rfl) ⟨54330, by rfl⟩) R108661
theorem R144899 : Reach 144899 := rs (se 1 (by rfl) ⟨108674, by rfl⟩) R217349
theorem R144929 : Reach 144929 := rs (se 2 (by rfl) ⟨54348, by rfl⟩) R108697
theorem R472625 : Reach 472625 := rs (se 2 (by rfl) ⟨177234, by rfl⟩) R354469
theorem R144947 : Reach 144947 := rs (se 1 (by rfl) ⟨108710, by rfl⟩) R217421
theorem R144977 : Reach 144977 := rs (se 2 (by rfl) ⟨54366, by rfl⟩) R108733
theorem R144995 : Reach 144995 := rs (se 1 (by rfl) ⟨108746, by rfl⟩) R217493
theorem R145025 : Reach 145025 := rs (se 2 (by rfl) ⟨54384, by rfl⟩) R108769
theorem R669325 : Reach 669325 := rs (se 3 (by rfl) ⟨125498, by rfl⟩) R250997
theorem R145043 : Reach 145043 := rs (se 1 (by rfl) ⟨108782, by rfl⟩) R217565
theorem R145073 : Reach 145073 := rs (se 2 (by rfl) ⟨54402, by rfl⟩) R108805
theorem R243395 : Reach 243395 := rs (se 1 (by rfl) ⟨182546, by rfl⟩) R365093
theorem R145091 : Reach 145091 := rs (se 1 (by rfl) ⟨108818, by rfl⟩) R217637
theorem R145121 : Reach 145121 := rs (se 2 (by rfl) ⟨54420, by rfl⟩) R108841
theorem R145139 : Reach 145139 := rs (se 1 (by rfl) ⟨108854, by rfl⟩) R217709
theorem R145169 : Reach 145169 := rs (se 2 (by rfl) ⟨54438, by rfl⟩) R108877
theorem R145187 : Reach 145187 := rs (se 1 (by rfl) ⟨108890, by rfl⟩) R217781
theorem R145217 : Reach 145217 := rs (se 2 (by rfl) ⟨54456, by rfl⟩) R108913
theorem R145235 : Reach 145235 := rs (se 1 (by rfl) ⟨108926, by rfl⟩) R217853
theorem R145265 : Reach 145265 := rs (se 2 (by rfl) ⟨54474, by rfl⟩) R108949
theorem R243587 : Reach 243587 := rs (se 1 (by rfl) ⟨182690, by rfl⟩) R365381
theorem R145283 : Reach 145283 := rs (se 1 (by rfl) ⟨108962, by rfl⟩) R217925
theorem R145297 : Reach 145297 := rs (se 2 (by rfl) ⟨54486, by rfl⟩) R108973
theorem R210833 : Reach 210833 := rs (se 2 (by rfl) ⟨79062, by rfl⟩) R158125
theorem R145313 : Reach 145313 := rs (se 2 (by rfl) ⟨54492, by rfl⟩) R108985
theorem R145331 : Reach 145331 := rs (se 1 (by rfl) ⟨108998, by rfl⟩) R217997
theorem R309187 : Reach 309187 := rs (se 1 (by rfl) ⟨231890, by rfl⟩) R463781
theorem R407501 : Reach 407501 := rs (se 3 (by rfl) ⟨76406, by rfl⟩) R152813
theorem R145361 : Reach 145361 := rs (se 2 (by rfl) ⟨54510, by rfl⟩) R109021
theorem R145379 : Reach 145379 := rs (se 1 (by rfl) ⟨109034, by rfl⟩) R218069
theorem R145409 : Reach 145409 := rs (se 2 (by rfl) ⟨54528, by rfl⟩) R109057
theorem R276497 : Reach 276497 := rs (se 2 (by rfl) ⟨103686, by rfl⟩) R207373
theorem R145427 : Reach 145427 := rs (se 1 (by rfl) ⟨109070, by rfl⟩) R218141
theorem R145457 : Reach 145457 := rs (se 2 (by rfl) ⟨54546, by rfl⟩) R109093
theorem R145475 : Reach 145475 := rs (se 1 (by rfl) ⟨109106, by rfl⟩) R218213
theorem R145505 : Reach 145505 := rs (se 2 (by rfl) ⟨54564, by rfl⟩) R109129
theorem R145523 : Reach 145523 := rs (se 1 (by rfl) ⟨109142, by rfl⟩) R218285
theorem R145553 : Reach 145553 := rs (se 2 (by rfl) ⟨54582, by rfl⟩) R109165
theorem R145571 : Reach 145571 := rs (se 1 (by rfl) ⟨109178, by rfl⟩) R218357
theorem R145601 : Reach 145601 := rs (se 2 (by rfl) ⟨54600, by rfl⟩) R109201
theorem R145619 : Reach 145619 := rs (se 1 (by rfl) ⟨109214, by rfl⟩) R218429
theorem R145649 : Reach 145649 := rs (se 2 (by rfl) ⟨54618, by rfl⟩) R109237
theorem R145667 : Reach 145667 := rs (se 1 (by rfl) ⟨109250, by rfl⟩) R218501
theorem R309521 : Reach 309521 := rs (se 2 (by rfl) ⟨116070, by rfl⟩) R232141
theorem R145697 : Reach 145697 := rs (se 2 (by rfl) ⟨54636, by rfl⟩) R109273
theorem R145715 : Reach 145715 := rs (se 1 (by rfl) ⟨109286, by rfl⟩) R218573
theorem R145745 : Reach 145745 := rs (se 2 (by rfl) ⟨54654, by rfl⟩) R109309
theorem R145763 : Reach 145763 := rs (se 1 (by rfl) ⟨109322, by rfl⟩) R218645
theorem R178531 : Reach 178531 := rs (se 1 (by rfl) ⟨133898, by rfl⟩) R267797
theorem R145793 : Reach 145793 := rs (se 2 (by rfl) ⟨54672, by rfl⟩) R109345
theorem R145811 : Reach 145811 := rs (se 1 (by rfl) ⟨109358, by rfl⟩) R218717
theorem R145841 : Reach 145841 := rs (se 2 (by rfl) ⟨54690, by rfl⟩) R109381
theorem R145859 : Reach 145859 := rs (se 1 (by rfl) ⟨109394, by rfl⟩) R218789
theorem R145889 : Reach 145889 := rs (se 2 (by rfl) ⟨54708, by rfl⟩) R109417
theorem R145907 : Reach 145907 := rs (se 1 (by rfl) ⟨109430, by rfl⟩) R218861
theorem R145937 : Reach 145937 := rs (se 2 (by rfl) ⟨54726, by rfl⟩) R109453
theorem R145955 : Reach 145955 := rs (se 1 (by rfl) ⟨109466, by rfl⟩) R218933
theorem R145985 : Reach 145985 := rs (se 2 (by rfl) ⟨54744, by rfl⟩) R109489
theorem R146003 : Reach 146003 := rs (se 1 (by rfl) ⟨109502, by rfl⟩) R219005
theorem R146033 : Reach 146033 := rs (se 2 (by rfl) ⟨54762, by rfl⟩) R109525
theorem R146051 : Reach 146051 := rs (se 1 (by rfl) ⟨109538, by rfl⟩) R219077
theorem R146081 : Reach 146081 := rs (se 2 (by rfl) ⟨54780, by rfl⟩) R109561
theorem R146099 : Reach 146099 := rs (se 1 (by rfl) ⟨109574, by rfl⟩) R219149
theorem R146129 : Reach 146129 := rs (se 2 (by rfl) ⟨54798, by rfl⟩) R109597
theorem R146147 : Reach 146147 := rs (se 1 (by rfl) ⟨109610, by rfl⟩) R219221
theorem R146177 : Reach 146177 := rs (se 2 (by rfl) ⟨54816, by rfl⟩) R109633
theorem R146195 : Reach 146195 := rs (se 1 (by rfl) ⟨109646, by rfl⟩) R219293
theorem R277283 : Reach 277283 := rs (se 1 (by rfl) ⟨207962, by rfl⟩) R415925
theorem R375587 : Reach 375587 := rs (se 1 (by rfl) ⟨281690, by rfl⟩) R563381
theorem R244529 : Reach 244529 := rs (se 2 (by rfl) ⟨91698, by rfl⟩) R183397
theorem R146225 : Reach 146225 := rs (se 2 (by rfl) ⟨54834, by rfl⟩) R109669
theorem R146243 : Reach 146243 := rs (se 1 (by rfl) ⟨109682, by rfl⟩) R219365
theorem R146273 : Reach 146273 := rs (se 2 (by rfl) ⟨54852, by rfl⟩) R109705
theorem R244579 : Reach 244579 := rs (se 1 (by rfl) ⟨183434, by rfl⟩) R366869
theorem R146291 : Reach 146291 := rs (se 1 (by rfl) ⟨109718, by rfl⟩) R219437
theorem R146321 : Reach 146321 := rs (se 2 (by rfl) ⟨54870, by rfl⟩) R109741
theorem R146339 : Reach 146339 := rs (se 1 (by rfl) ⟨109754, by rfl⟩) R219509
theorem R146369 : Reach 146369 := rs (se 2 (by rfl) ⟨54888, by rfl⟩) R109777
theorem R146387 : Reach 146387 := rs (se 1 (by rfl) ⟨109790, by rfl⟩) R219581
theorem R244721 : Reach 244721 := rs (se 2 (by rfl) ⟨91770, by rfl⟩) R183541
theorem R146417 : Reach 146417 := rs (se 2 (by rfl) ⟨54906, by rfl⟩) R109813
theorem R146435 : Reach 146435 := rs (se 1 (by rfl) ⟨109826, by rfl⟩) R219653
theorem R146465 : Reach 146465 := rs (se 2 (by rfl) ⟨54924, by rfl⟩) R109849
theorem R146483 : Reach 146483 := rs (se 1 (by rfl) ⟨109862, by rfl⟩) R219725
theorem R146513 : Reach 146513 := rs (se 2 (by rfl) ⟨54942, by rfl⟩) R109885
theorem R146531 : Reach 146531 := rs (se 1 (by rfl) ⟨109898, by rfl⟩) R219797
theorem R277613 : Reach 277613 := rs (se 3 (by rfl) ⟨52052, by rfl⟩) R104105
theorem R146561 : Reach 146561 := rs (se 2 (by rfl) ⟨54960, by rfl⟩) R109921
theorem R146579 : Reach 146579 := rs (se 1 (by rfl) ⟨109934, by rfl⟩) R219869
theorem R277681 : Reach 277681 := rs (se 2 (by rfl) ⟨104130, by rfl⟩) R208261
theorem R146609 : Reach 146609 := rs (se 2 (by rfl) ⟨54978, by rfl⟩) R109957
theorem R146627 : Reach 146627 := rs (se 1 (by rfl) ⟨109970, by rfl⟩) R219941
theorem R146657 : Reach 146657 := rs (se 2 (by rfl) ⟨54996, by rfl⟩) R109993
theorem R113891 : Reach 113891 := rs (se 1 (by rfl) ⟨85418, by rfl⟩) R170837
theorem R146675 : Reach 146675 := rs (se 1 (by rfl) ⟨110006, by rfl⟩) R220013
theorem R146705 : Reach 146705 := rs (se 2 (by rfl) ⟨55014, by rfl⟩) R110029
theorem R146723 : Reach 146723 := rs (se 1 (by rfl) ⟨110042, by rfl⟩) R220085
theorem R146753 : Reach 146753 := rs (se 2 (by rfl) ⟨55032, by rfl⟩) R110065
theorem R146771 : Reach 146771 := rs (se 1 (by rfl) ⟨110078, by rfl⟩) R220157
theorem R146801 : Reach 146801 := rs (se 2 (by rfl) ⟨55050, by rfl⟩) R110101
theorem R146819 : Reach 146819 := rs (se 1 (by rfl) ⟨110114, by rfl⟩) R220229
theorem R146849 : Reach 146849 := rs (se 2 (by rfl) ⟨55068, by rfl⟩) R110137
theorem R474545 : Reach 474545 := rs (se 2 (by rfl) ⟨177954, by rfl⟩) R355909
theorem R146867 : Reach 146867 := rs (se 1 (by rfl) ⟨110150, by rfl⟩) R220301
theorem R277955 : Reach 277955 := rs (se 1 (by rfl) ⟨208466, by rfl⟩) R416933
theorem R146897 : Reach 146897 := rs (se 2 (by rfl) ⟨55086, by rfl⟩) R110173
theorem R146915 : Reach 146915 := rs (se 1 (by rfl) ⟨110186, by rfl⟩) R220373
theorem R146945 : Reach 146945 := rs (se 2 (by rfl) ⟨55104, by rfl⟩) R110209
theorem R146963 : Reach 146963 := rs (se 1 (by rfl) ⟨110222, by rfl⟩) R220445
theorem R146993 : Reach 146993 := rs (se 2 (by rfl) ⟨55122, by rfl⟩) R110245
theorem R147011 : Reach 147011 := rs (se 1 (by rfl) ⟨110258, by rfl⟩) R220517
theorem R147041 : Reach 147041 := rs (se 2 (by rfl) ⟨55140, by rfl⟩) R110281
theorem R147059 : Reach 147059 := rs (se 1 (by rfl) ⟨110294, by rfl⟩) R220589
theorem R147089 : Reach 147089 := rs (se 2 (by rfl) ⟨55158, by rfl⟩) R110317
theorem R147107 : Reach 147107 := rs (se 1 (by rfl) ⟨110330, by rfl⟩) R220661
theorem R147137 : Reach 147137 := rs (se 2 (by rfl) ⟨55176, by rfl⟩) R110353
theorem R147155 : Reach 147155 := rs (se 1 (by rfl) ⟨110366, by rfl⟩) R220733
theorem R147185 : Reach 147185 := rs (se 2 (by rfl) ⟨55194, by rfl⟩) R110389
theorem R147203 : Reach 147203 := rs (se 1 (by rfl) ⟨110402, by rfl⟩) R220805
theorem R147233 : Reach 147233 := rs (se 2 (by rfl) ⟨55212, by rfl⟩) R110425
theorem R147251 : Reach 147251 := rs (se 1 (by rfl) ⟨110438, by rfl⟩) R220877
theorem R147281 : Reach 147281 := rs (se 2 (by rfl) ⟨55230, by rfl⟩) R110461
theorem R147299 : Reach 147299 := rs (se 1 (by rfl) ⟨110474, by rfl⟩) R220949
theorem R147329 : Reach 147329 := rs (se 2 (by rfl) ⟨55248, by rfl⟩) R110497
theorem R147347 : Reach 147347 := rs (se 1 (by rfl) ⟨110510, by rfl⟩) R221021
theorem R147377 : Reach 147377 := rs (se 2 (by rfl) ⟨55266, by rfl⟩) R110533
theorem R147395 : Reach 147395 := rs (se 1 (by rfl) ⟨110546, by rfl⟩) R221093
theorem R475085 : Reach 475085 := rs (se 3 (by rfl) ⟨89078, by rfl⟩) R178157
theorem R245713 : Reach 245713 := rs (se 2 (by rfl) ⟨92142, by rfl⟩) R184285
theorem R147425 : Reach 147425 := rs (se 2 (by rfl) ⟨55284, by rfl⟩) R110569
theorem R147443 : Reach 147443 := rs (se 1 (by rfl) ⟨110582, by rfl⟩) R221165
theorem R147473 : Reach 147473 := rs (se 2 (by rfl) ⟨55302, by rfl⟩) R110605
theorem R147491 : Reach 147491 := rs (se 1 (by rfl) ⟨110618, by rfl⟩) R221237
theorem R147521 : Reach 147521 := rs (se 2 (by rfl) ⟨55320, by rfl⟩) R110641
theorem R147539 : Reach 147539 := rs (se 1 (by rfl) ⟨110654, by rfl⟩) R221309
theorem R147569 : Reach 147569 := rs (se 2 (by rfl) ⟨55338, by rfl⟩) R110677
theorem R147587 : Reach 147587 := rs (se 1 (by rfl) ⟨110690, by rfl⟩) R221381
theorem R147617 : Reach 147617 := rs (se 2 (by rfl) ⟨55356, by rfl⟩) R110713
theorem R147635 : Reach 147635 := rs (se 1 (by rfl) ⟨110726, by rfl⟩) R221453
theorem R147665 : Reach 147665 := rs (se 2 (by rfl) ⟨55374, by rfl⟩) R110749
theorem R245987 : Reach 245987 := rs (se 1 (by rfl) ⟨184490, by rfl⟩) R368981
theorem R147683 : Reach 147683 := rs (se 1 (by rfl) ⟨110762, by rfl⟩) R221525
theorem R147713 : Reach 147713 := rs (se 2 (by rfl) ⟨55392, by rfl⟩) R110785
theorem R278797 : Reach 278797 := rs (se 3 (by rfl) ⟨52274, by rfl⟩) R104549
theorem R147731 : Reach 147731 := rs (se 1 (by rfl) ⟨110798, by rfl⟩) R221597
theorem R311597 : Reach 311597 := rs (se 3 (by rfl) ⟨58424, by rfl⟩) R116849
theorem R147761 : Reach 147761 := rs (se 2 (by rfl) ⟨55410, by rfl⟩) R110821
theorem R147779 : Reach 147779 := rs (se 1 (by rfl) ⟨110834, by rfl⟩) R221669
theorem R147809 : Reach 147809 := rs (se 2 (by rfl) ⟨55428, by rfl⟩) R110857
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R147827 : Reach 147827 := rs (se 1 (by rfl) ⟨110870, by rfl⟩) R221741
theorem R180625 : Reach 180625 := rs (se 2 (by rfl) ⟨67734, by rfl⟩) R135469
theorem R147857 : Reach 147857 := rs (se 2 (by rfl) ⟨55446, by rfl⟩) R110893
theorem R246179 : Reach 246179 := rs (se 1 (by rfl) ⟨184634, by rfl⟩) R369269
theorem R147875 : Reach 147875 := rs (se 1 (by rfl) ⟨110906, by rfl⟩) R221813
theorem R278957 : Reach 278957 := rs (se 3 (by rfl) ⟨52304, by rfl⟩) R104609
theorem R147905 : Reach 147905 := rs (se 2 (by rfl) ⟨55464, by rfl⟩) R110929
theorem R147923 : Reach 147923 := rs (se 1 (by rfl) ⟨110942, by rfl⟩) R221885
theorem R147953 : Reach 147953 := rs (se 2 (by rfl) ⟨55482, by rfl⟩) R110965
theorem R147971 : Reach 147971 := rs (se 1 (by rfl) ⟨110978, by rfl⟩) R221957
theorem R148001 : Reach 148001 := rs (se 2 (by rfl) ⟨55500, by rfl⟩) R111001
theorem R180785 : Reach 180785 := rs (se 2 (by rfl) ⟨67794, by rfl⟩) R135589
theorem R148019 : Reach 148019 := rs (se 1 (by rfl) ⟨111014, by rfl⟩) R222029
theorem R148049 : Reach 148049 := rs (se 2 (by rfl) ⟨55518, by rfl⟩) R111037
theorem R279139 : Reach 279139 := rs (se 1 (by rfl) ⟨209354, by rfl⟩) R418709
theorem R148067 : Reach 148067 := rs (se 1 (by rfl) ⟨111050, by rfl⟩) R222101
theorem R148097 : Reach 148097 := rs (se 2 (by rfl) ⟨55536, by rfl⟩) R111073
theorem R148115 : Reach 148115 := rs (se 1 (by rfl) ⟨111086, by rfl⟩) R222173
theorem R148145 : Reach 148145 := rs (se 2 (by rfl) ⟨55554, by rfl⟩) R111109
theorem R148163 : Reach 148163 := rs (se 1 (by rfl) ⟨111122, by rfl⟩) R222245
theorem R2081477 : Reach 2081477 := rs (se 4 (by rfl) ⟨195138, by rfl⟩) R390277
theorem R1000133 : Reach 1000133 := rs (se 4 (by rfl) ⟨93762, by rfl⟩) R187525
theorem R148193 : Reach 148193 := rs (se 2 (by rfl) ⟨55572, by rfl⟩) R111145
theorem R148211 : Reach 148211 := rs (se 1 (by rfl) ⟨111158, by rfl⟩) R222317
theorem R148241 : Reach 148241 := rs (se 2 (by rfl) ⟨55590, by rfl⟩) R111181
theorem R148259 : Reach 148259 := rs (se 1 (by rfl) ⟨111194, by rfl⟩) R222389
theorem R148289 : Reach 148289 := rs (se 2 (by rfl) ⟨55608, by rfl⟩) R111217
theorem R148307 : Reach 148307 := rs (se 1 (by rfl) ⟨111230, by rfl⟩) R222461
theorem R148337 : Reach 148337 := rs (se 2 (by rfl) ⟨55626, by rfl⟩) R111253
theorem R148355 : Reach 148355 := rs (se 1 (by rfl) ⟨111266, by rfl⟩) R222533
theorem R148385 : Reach 148385 := rs (se 2 (by rfl) ⟨55644, by rfl⟩) R111289
theorem R148403 : Reach 148403 := rs (se 1 (by rfl) ⟨111302, by rfl⟩) R222605
theorem R181187 : Reach 181187 := rs (se 1 (by rfl) ⟨135890, by rfl⟩) R271781
theorem R148433 : Reach 148433 := rs (se 2 (by rfl) ⟨55662, by rfl⟩) R111325
theorem R1426403 : Reach 1426403 := rs (se 1 (by rfl) ⟨1069802, by rfl⟩) R2139605
theorem R148451 : Reach 148451 := rs (se 1 (by rfl) ⟨111338, by rfl⟩) R222677
theorem R410609 : Reach 410609 := rs (se 2 (by rfl) ⟨153978, by rfl⟩) R307957
theorem R148481 : Reach 148481 := rs (se 2 (by rfl) ⟨55680, by rfl⟩) R111361
theorem R115715 : Reach 115715 := rs (se 1 (by rfl) ⟨86786, by rfl⟩) R173573
theorem R148499 : Reach 148499 := rs (se 1 (by rfl) ⟨111374, by rfl⟩) R222749
theorem R148529 : Reach 148529 := rs (se 2 (by rfl) ⟨55698, by rfl⟩) R111397
theorem R115763 : Reach 115763 := rs (se 1 (by rfl) ⟨86822, by rfl⟩) R173645
theorem R1197109 : Reach 1197109 := rs (se 5 (by rfl) ⟨56114, by rfl⟩) R112229
theorem R148547 : Reach 148547 := rs (se 1 (by rfl) ⟨111410, by rfl⟩) R222821
theorem R148577 : Reach 148577 := rs (se 2 (by rfl) ⟨55716, by rfl⟩) R111433
theorem R148595 : Reach 148595 := rs (se 1 (by rfl) ⟨111446, by rfl⟩) R222893
theorem R541829 : Reach 541829 := rs (se 4 (by rfl) ⟨50796, by rfl⟩) R101593
theorem R148625 : Reach 148625 := rs (se 2 (by rfl) ⟨55734, by rfl⟩) R111469
theorem R148643 : Reach 148643 := rs (se 1 (by rfl) ⟨111482, by rfl⟩) R222965
theorem R148673 : Reach 148673 := rs (se 2 (by rfl) ⟨55752, by rfl⟩) R111505
theorem R1262789 : Reach 1262789 := rs (se 4 (by rfl) ⟨118386, by rfl⟩) R236773
theorem R148691 : Reach 148691 := rs (se 1 (by rfl) ⟨111518, by rfl⟩) R223037
theorem R279811 : Reach 279811 := rs (se 1 (by rfl) ⟨209858, by rfl⟩) R419717
theorem R214289 : Reach 214289 := rs (se 2 (by rfl) ⟨80358, by rfl⟩) R160717
theorem R214307 : Reach 214307 := rs (se 1 (by rfl) ⟨160730, by rfl⟩) R321461
theorem R247121 : Reach 247121 := rs (se 2 (by rfl) ⟨92670, by rfl⟩) R185341
theorem R247171 : Reach 247171 := rs (se 1 (by rfl) ⟨185378, by rfl⟩) R370757
theorem R247313 : Reach 247313 := rs (se 2 (by rfl) ⟨92742, by rfl⟩) R185485
theorem R214577 : Reach 214577 := rs (se 2 (by rfl) ⟨80466, by rfl⟩) R160933
theorem R214595 : Reach 214595 := rs (se 1 (by rfl) ⟨160946, by rfl⟩) R321893
theorem R542285 : Reach 542285 := rs (se 3 (by rfl) ⟨101678, by rfl⟩) R203357
theorem R411277 : Reach 411277 := rs (se 3 (by rfl) ⟨77114, by rfl⟩) R154229
theorem R444209 : Reach 444209 := rs (se 2 (by rfl) ⟨166578, by rfl⟩) R333157
theorem R182083 : Reach 182083 := rs (se 1 (by rfl) ⟨136562, by rfl⟩) R273125
theorem R214865 : Reach 214865 := rs (se 2 (by rfl) ⟨80574, by rfl⟩) R161149
theorem R214883 : Reach 214883 := rs (se 1 (by rfl) ⟨161162, by rfl⟩) R322325
theorem R280529 : Reach 280529 := rs (se 2 (by rfl) ⟨105198, by rfl⟩) R210397
theorem R182243 : Reach 182243 := rs (se 1 (by rfl) ⟨136682, by rfl⟩) R273365
theorem R313379 : Reach 313379 := rs (se 1 (by rfl) ⟨235034, by rfl⟩) R470069
theorem R215153 : Reach 215153 := rs (se 2 (by rfl) ⟨80682, by rfl⟩) R161365
theorem R215171 : Reach 215171 := rs (se 1 (by rfl) ⟨161378, by rfl⟩) R322757
theorem R411875 : Reach 411875 := rs (se 1 (by rfl) ⟨308906, by rfl⟩) R617813
theorem R2017507 : Reach 2017507 := rs (se 1 (by rfl) ⟨1513130, by rfl⟩) R3026261
theorem R510221 : Reach 510221 := rs (se 3 (by rfl) ⟨95666, by rfl⟩) R191333
theorem R215441 : Reach 215441 := rs (se 2 (by rfl) ⟨80790, by rfl⟩) R161581
theorem R215459 : Reach 215459 := rs (se 1 (by rfl) ⟨161594, by rfl⟩) R323189
theorem R1034693 : Reach 1034693 := rs (se 4 (by rfl) ⟨97002, by rfl⟩) R194005
theorem R248305 : Reach 248305 := rs (se 2 (by rfl) ⟨93114, by rfl⟩) R186229
theorem R477731 : Reach 477731 := rs (se 1 (by rfl) ⟨358298, by rfl⟩) R716597
theorem R215729 : Reach 215729 := rs (se 2 (by rfl) ⟨80898, by rfl⟩) R161797
theorem R215747 : Reach 215747 := rs (se 1 (by rfl) ⟨161810, by rfl⟩) R323621
theorem R248579 : Reach 248579 := rs (se 1 (by rfl) ⟨186434, by rfl⟩) R372869
theorem R281357 : Reach 281357 := rs (se 3 (by rfl) ⟨52754, by rfl⟩) R105509
theorem R314189 : Reach 314189 := rs (se 3 (by rfl) ⟨58910, by rfl⟩) R117821
theorem R281485 : Reach 281485 := rs (se 3 (by rfl) ⟨52778, by rfl⟩) R105557
theorem R248771 : Reach 248771 := rs (se 1 (by rfl) ⟨186578, by rfl⟩) R373157
theorem R216017 : Reach 216017 := rs (se 2 (by rfl) ⟨81006, by rfl⟩) R162013
theorem R216035 : Reach 216035 := rs (se 1 (by rfl) ⟨162026, by rfl⟩) R324053
theorem R183313 : Reach 183313 := rs (se 2 (by rfl) ⟨68742, by rfl⟩) R137485
theorem R281681 : Reach 281681 := rs (se 2 (by rfl) ⟨105630, by rfl⟩) R211261
theorem R281713 : Reach 281713 := rs (se 2 (by rfl) ⟨105642, by rfl⟩) R211285
theorem R216305 : Reach 216305 := rs (se 2 (by rfl) ⟨81114, by rfl⟩) R162229
theorem R216323 : Reach 216323 := rs (se 1 (by rfl) ⟨162242, by rfl⟩) R324485
theorem R281873 : Reach 281873 := rs (se 2 (by rfl) ⟨105702, by rfl⟩) R211405
theorem R314723 : Reach 314723 := rs (se 1 (by rfl) ⟨236042, by rfl⟩) R472085
theorem R281987 : Reach 281987 := rs (se 1 (by rfl) ⟨211490, by rfl⟩) R422981
theorem R609763 : Reach 609763 := rs (se 1 (by rfl) ⟨457322, by rfl⟩) R914645
theorem R216593 : Reach 216593 := rs (se 2 (by rfl) ⟨81222, by rfl⟩) R162445
theorem R216611 : Reach 216611 := rs (se 1 (by rfl) ⟨162458, by rfl⟩) R324917
theorem R4247153 : Reach 4247153 := rs (se 2 (by rfl) ⟨1592682, by rfl⟩) R3185365
theorem R118531 : Reach 118531 := rs (se 1 (by rfl) ⟨88898, by rfl⟩) R177797
theorem R347939 : Reach 347939 := rs (se 1 (by rfl) ⟨260954, by rfl⟩) R521909
theorem R216881 : Reach 216881 := rs (se 2 (by rfl) ⟨81330, by rfl⟩) R162661
theorem R216899 : Reach 216899 := rs (se 1 (by rfl) ⟨162674, by rfl⟩) R325349
theorem R249713 : Reach 249713 := rs (se 2 (by rfl) ⟨93642, by rfl⟩) R187285
theorem R118675 : Reach 118675 := rs (se 1 (by rfl) ⟨89006, by rfl⟩) R178013
theorem R348067 : Reach 348067 := rs (se 1 (by rfl) ⟨261050, by rfl⟩) R522101
theorem R249763 : Reach 249763 := rs (se 1 (by rfl) ⟨187322, by rfl⟩) R374645
theorem R184369 : Reach 184369 := rs (se 2 (by rfl) ⟨69138, by rfl⟩) R138277
theorem R249905 : Reach 249905 := rs (se 2 (by rfl) ⟨93714, by rfl⟩) R187429
theorem R217169 : Reach 217169 := rs (se 2 (by rfl) ⟨81438, by rfl⟩) R162877
theorem R217187 : Reach 217187 := rs (se 1 (by rfl) ⟨162890, by rfl⟩) R325781
theorem R348401 : Reach 348401 := rs (se 2 (by rfl) ⟨130650, by rfl⟩) R261301
theorem R217457 : Reach 217457 := rs (se 2 (by rfl) ⟨81546, by rfl⟩) R163093
theorem R217475 : Reach 217475 := rs (se 1 (by rfl) ⟨163106, by rfl⟩) R326213
theorem R545201 : Reach 545201 := rs (se 2 (by rfl) ⟨204450, by rfl⟩) R408901
theorem R184771 : Reach 184771 := rs (se 1 (by rfl) ⟨138578, by rfl⟩) R277157
theorem R17125829 : Reach 17125829 := rs (se 4 (by rfl) ⟨1605546, by rfl⟩) R3211093
theorem R184817 : Reach 184817 := rs (se 2 (by rfl) ⟨69306, by rfl⟩) R138613
theorem R348785 : Reach 348785 := rs (se 2 (by rfl) ⟨130794, by rfl⟩) R261589
theorem R3002993 : Reach 3002993 := rs (se 2 (by rfl) ⟨1126122, by rfl⟩) R2252245
theorem R217745 : Reach 217745 := rs (se 2 (by rfl) ⟨81654, by rfl⟩) R163309
theorem R217763 : Reach 217763 := rs (se 1 (by rfl) ⟨163322, by rfl⟩) R326645
theorem R610993 : Reach 610993 := rs (se 2 (by rfl) ⟨229122, by rfl⟩) R458245
theorem R152275 : Reach 152275 := rs (se 1 (by rfl) ⟨114206, by rfl⟩) R228413
theorem R185105 : Reach 185105 := rs (se 2 (by rfl) ⟨69414, by rfl⟩) R138829
theorem R218033 : Reach 218033 := rs (se 2 (by rfl) ⟨81762, by rfl⟩) R163525
theorem R218051 : Reach 218051 := rs (se 1 (by rfl) ⟨163538, by rfl⟩) R327077
theorem R250897 : Reach 250897 := rs (se 2 (by rfl) ⟨94086, by rfl⟩) R188173
theorem R316493 : Reach 316493 := rs (se 3 (by rfl) ⟨59342, by rfl⟩) R118685
theorem R152723 : Reach 152723 := rs (se 1 (by rfl) ⟨114542, by rfl⟩) R229085
theorem R840901 : Reach 840901 := rs (se 4 (by rfl) ⟨78834, by rfl⟩) R157669
theorem R218321 : Reach 218321 := rs (se 2 (by rfl) ⟨81870, by rfl⟩) R163741
theorem R218339 : Reach 218339 := rs (se 1 (by rfl) ⟨163754, by rfl⟩) R327509
theorem R152851 : Reach 152851 := rs (se 1 (by rfl) ⟨114638, by rfl⟩) R229277
theorem R185827 : Reach 185827 := rs (se 1 (by rfl) ⟨139370, by rfl⟩) R278741
theorem R349681 : Reach 349681 := rs (se 2 (by rfl) ⟨131130, by rfl⟩) R262261
theorem R218609 : Reach 218609 := rs (se 2 (by rfl) ⟨81978, by rfl⟩) R163957
theorem R218627 : Reach 218627 := rs (se 1 (by rfl) ⟨163970, by rfl⟩) R327941
theorem R120467 : Reach 120467 := rs (se 1 (by rfl) ⟨90350, by rfl⟩) R180701
theorem R218897 : Reach 218897 := rs (se 2 (by rfl) ⟨82086, by rfl⟩) R164173
theorem R218915 : Reach 218915 := rs (se 1 (by rfl) ⟨164186, by rfl⟩) R328373
theorem R153409 : Reach 153409 := rs (se 2 (by rfl) ⟨57528, by rfl⟩) R115057
theorem R546659 : Reach 546659 := rs (se 1 (by rfl) ⟨409994, by rfl⟩) R819989
theorem R415651 : Reach 415651 := rs (se 1 (by rfl) ⟨311738, by rfl⟩) R623477
theorem R186275 : Reach 186275 := rs (se 1 (by rfl) ⟨139706, by rfl⟩) R279413
theorem R219185 : Reach 219185 := rs (se 2 (by rfl) ⟨82194, by rfl⟩) R164389
theorem R219203 : Reach 219203 := rs (se 1 (by rfl) ⟨164402, by rfl⟩) R328805
theorem R186563 : Reach 186563 := rs (se 1 (by rfl) ⟨139922, by rfl⟩) R279845
theorem R448739 : Reach 448739 := rs (se 1 (by rfl) ⟨336554, by rfl⟩) R673109
theorem R252227 : Reach 252227 := rs (se 1 (by rfl) ⟨189170, by rfl⟩) R378341
theorem R219473 : Reach 219473 := rs (se 2 (by rfl) ⟨82302, by rfl⟩) R164605
theorem R121171 : Reach 121171 := rs (se 1 (by rfl) ⟨90878, by rfl⟩) R181757
theorem R219491 : Reach 219491 := rs (se 1 (by rfl) ⟨164618, by rfl⟩) R329237
theorem R121267 : Reach 121267 := rs (se 1 (by rfl) ⟨90950, by rfl⟩) R181901
theorem R154081 : Reach 154081 := rs (se 2 (by rfl) ⟨57780, by rfl⟩) R115561
theorem R219761 : Reach 219761 := rs (se 2 (by rfl) ⟨82410, by rfl⟩) R164821
theorem R219779 : Reach 219779 := rs (se 1 (by rfl) ⟨164834, by rfl⟩) R329669
theorem R547661 : Reach 547661 := rs (se 3 (by rfl) ⟨102686, by rfl⟩) R205373
theorem R220049 : Reach 220049 := rs (se 2 (by rfl) ⟨82518, by rfl⟩) R165037
theorem R220067 : Reach 220067 := rs (se 1 (by rfl) ⟨165050, by rfl⟩) R330101
theorem R121763 : Reach 121763 := rs (se 1 (by rfl) ⟨91322, by rfl⟩) R182645
theorem R187505 : Reach 187505 := rs (se 2 (by rfl) ⟨70314, by rfl⟩) R140629
theorem R220337 : Reach 220337 := rs (se 2 (by rfl) ⟨82626, by rfl⟩) R165253
theorem R220355 : Reach 220355 := rs (se 1 (by rfl) ⟨165266, by rfl⟩) R330533
theorem R875789 : Reach 875789 := rs (se 3 (by rfl) ⟨164210, by rfl⟩) R328421
theorem R351629 : Reach 351629 := rs (se 3 (by rfl) ⟨65930, by rfl⟩) R131861
theorem R220625 : Reach 220625 := rs (se 2 (by rfl) ⟨82734, by rfl⟩) R165469
theorem R220643 : Reach 220643 := rs (se 1 (by rfl) ⟨165482, by rfl⟩) R330965
theorem R155171 : Reach 155171 := rs (se 1 (by rfl) ⟨116378, by rfl⟩) R232757
theorem R122467 : Reach 122467 := rs (se 1 (by rfl) ⟨91850, by rfl⟩) R183701
theorem R122563 : Reach 122563 := rs (se 1 (by rfl) ⟨91922, by rfl⟩) R183845
theorem R220913 : Reach 220913 := rs (se 2 (by rfl) ⟨82842, by rfl⟩) R165685
theorem R220931 : Reach 220931 := rs (se 1 (by rfl) ⟨165698, by rfl⟩) R331397
theorem R581381 : Reach 581381 := rs (se 4 (by rfl) ⟨54504, by rfl⟩) R109009
theorem R417649 : Reach 417649 := rs (se 2 (by rfl) ⟨156618, by rfl⟩) R313237
theorem R253955 : Reach 253955 := rs (se 1 (by rfl) ⟨190466, by rfl⟩) R380933
theorem R221201 : Reach 221201 := rs (se 2 (by rfl) ⟨82950, by rfl⟩) R165901
theorem R221219 : Reach 221219 := rs (se 1 (by rfl) ⟨165914, by rfl⟩) R331829
theorem R123059 : Reach 123059 := rs (se 1 (by rfl) ⟨92294, by rfl⟩) R184589
theorem R483569 : Reach 483569 := rs (se 2 (by rfl) ⟨181338, by rfl⟩) R362677
theorem R221489 : Reach 221489 := rs (se 2 (by rfl) ⟨83058, by rfl⟩) R166117
theorem R221507 : Reach 221507 := rs (se 1 (by rfl) ⟨166130, by rfl⟩) R332261
theorem R614789 : Reach 614789 := rs (se 4 (by rfl) ⟨57636, by rfl⟩) R115273
theorem R221777 : Reach 221777 := rs (se 2 (by rfl) ⟨83166, by rfl⟩) R166333
theorem R221795 : Reach 221795 := rs (se 1 (by rfl) ⟨166346, by rfl⟩) R332693
theorem R222065 : Reach 222065 := rs (se 2 (by rfl) ⟨83274, by rfl⟩) R166549
theorem R123763 : Reach 123763 := rs (se 1 (by rfl) ⟨92822, by rfl⟩) R185645
theorem R222083 : Reach 222083 := rs (se 1 (by rfl) ⟨166562, by rfl⟩) R333125
theorem R156593 : Reach 156593 := rs (se 2 (by rfl) ⟨58722, by rfl⟩) R117445
theorem R123859 : Reach 123859 := rs (se 1 (by rfl) ⟨92894, by rfl⟩) R185789
theorem R353315 : Reach 353315 := rs (se 1 (by rfl) ⟨264986, by rfl⟩) R529973
theorem R222353 : Reach 222353 := rs (se 2 (by rfl) ⟨83382, by rfl⟩) R166765
theorem R222371 : Reach 222371 := rs (se 1 (by rfl) ⟨166778, by rfl⟩) R333557
theorem R222641 : Reach 222641 := rs (se 2 (by rfl) ⟨83490, by rfl⟩) R166981
theorem R124355 : Reach 124355 := rs (se 1 (by rfl) ⟨93266, by rfl⟩) R186533
theorem R222659 : Reach 222659 := rs (se 1 (by rfl) ⟨166994, by rfl⟩) R333989
theorem R321137 : Reach 321137 := rs (se 2 (by rfl) ⟨120426, by rfl⟩) R240853
theorem R485027 : Reach 485027 := rs (se 1 (by rfl) ⟨363770, by rfl⟩) R727541
theorem R550577 : Reach 550577 := rs (se 2 (by rfl) ⟨206466, by rfl⟩) R412933
theorem R222929 : Reach 222929 := rs (se 2 (by rfl) ⟨83598, by rfl⟩) R167197
theorem R222947 : Reach 222947 := rs (se 1 (by rfl) ⟨167210, by rfl⟩) R334421
theorem R157459 : Reach 157459 := rs (se 1 (by rfl) ⟨118094, by rfl⟩) R236189
theorem R157715 : Reach 157715 := rs (se 1 (by rfl) ⟨118286, by rfl⟩) R236573
theorem R125059 : Reach 125059 := rs (se 1 (by rfl) ⟨93794, by rfl⟩) R187589
theorem R321677 : Reach 321677 := rs (se 3 (by rfl) ⟨60314, by rfl⟩) R120629
theorem R321731 : Reach 321731 := rs (se 1 (by rfl) ⟨241298, by rfl⟩) R482597
theorem R125155 : Reach 125155 := rs (se 1 (by rfl) ⟨93866, by rfl⟩) R187733
theorem R485837 : Reach 485837 := rs (se 3 (by rfl) ⟨91094, by rfl⟩) R182189
theorem R322001 : Reach 322001 := rs (se 2 (by rfl) ⟨120750, by rfl⟩) R241501
theorem R223985 : Reach 223985 := rs (se 2 (by rfl) ⟨83994, by rfl⟩) R167989
theorem R158689 : Reach 158689 := rs (se 2 (by rfl) ⟨59508, by rfl⟩) R119017
theorem R519139 : Reach 519139 := rs (se 1 (by rfl) ⟨389354, by rfl⟩) R778709
theorem R322541 : Reach 322541 := rs (se 3 (by rfl) ⟨60476, by rfl⟩) R120953
theorem R322595 : Reach 322595 := rs (se 1 (by rfl) ⟨241946, by rfl⟩) R483893
theorem R552035 : Reach 552035 := rs (se 1 (by rfl) ⟨414026, by rfl⟩) R828053
theorem R322865 : Reach 322865 := rs (se 2 (by rfl) ⟨121074, by rfl⟩) R242149
theorem R388721 : Reach 388721 := rs (se 2 (by rfl) ⟨145770, by rfl⟩) R291541
theorem R257699 : Reach 257699 := rs (se 1 (by rfl) ⟨193274, by rfl⟩) R386549
theorem R421681 : Reach 421681 := rs (se 2 (by rfl) ⟨158130, by rfl⟩) R316261
theorem R323405 : Reach 323405 := rs (se 3 (by rfl) ⟨60638, by rfl⟩) R121277
theorem R749411 : Reach 749411 := rs (se 1 (by rfl) ⟨562058, by rfl⟩) R1124117
theorem R618353 : Reach 618353 := rs (se 2 (by rfl) ⟨231882, by rfl⟩) R463765
theorem R323459 : Reach 323459 := rs (se 1 (by rfl) ⟨242594, by rfl⟩) R485189
theorem R323729 : Reach 323729 := rs (se 2 (by rfl) ⟨121398, by rfl⟩) R242797
theorem R6254819 : Reach 6254819 := rs (se 1 (by rfl) ⟨4691114, by rfl⟩) R9382229
theorem R946403 : Reach 946403 := rs (se 1 (by rfl) ⟨709802, by rfl⟩) R1419605
theorem R2453813 : Reach 2453813 := rs (se 5 (by rfl) ⟨115022, by rfl⟩) R230045
theorem R127555 : Reach 127555 := rs (se 1 (by rfl) ⟨95666, by rfl⟩) R191333
theorem R1241669 : Reach 1241669 := rs (se 4 (by rfl) ⟨116406, by rfl⟩) R232813
theorem R356977 : Reach 356977 := rs (se 2 (by rfl) ⟨133866, by rfl⟩) R267733
theorem R357005 : Reach 357005 := rs (se 3 (by rfl) ⟨66938, by rfl⟩) R133877
theorem R324269 : Reach 324269 := rs (se 3 (by rfl) ⟨60800, by rfl⟩) R121601
theorem R324323 : Reach 324323 := rs (se 1 (by rfl) ⟨243242, by rfl⟩) R486485
theorem R226019 : Reach 226019 := rs (se 1 (by rfl) ⟨169514, by rfl⟩) R339029
theorem R160609 : Reach 160609 := rs (se 2 (by rfl) ⟨60228, by rfl⟩) R120457
theorem R160643 : Reach 160643 := rs (se 1 (by rfl) ⟨120482, by rfl⟩) R240965
theorem R95139 : Reach 95139 := rs (se 1 (by rfl) ⟨71354, by rfl⟩) R142709
theorem R95155 : Reach 95155 := rs (se 1 (by rfl) ⟨71366, by rfl⟩) R142733
theorem R95171 : Reach 95171 := rs (se 1 (by rfl) ⟨71378, by rfl⟩) R142757
theorem R95187 : Reach 95187 := rs (se 1 (by rfl) ⟨71390, by rfl⟩) R142781
theorem R95203 : Reach 95203 := rs (se 1 (by rfl) ⟨71402, by rfl⟩) R142805
theorem R95219 : Reach 95219 := rs (se 1 (by rfl) ⟨71414, by rfl⟩) R142829
theorem R324593 : Reach 324593 := rs (se 2 (by rfl) ⟨121722, by rfl⟩) R243445
theorem R95235 : Reach 95235 := rs (se 1 (by rfl) ⟨71426, by rfl⟩) R142853
theorem R160771 : Reach 160771 := rs (se 1 (by rfl) ⟨120578, by rfl⟩) R241157
theorem R947213 : Reach 947213 := rs (se 3 (by rfl) ⟨177602, by rfl⟩) R355205
theorem R95251 : Reach 95251 := rs (se 1 (by rfl) ⟨71438, by rfl⟩) R142877
theorem R95267 : Reach 95267 := rs (se 1 (by rfl) ⟨71450, by rfl⟩) R142901
theorem R95283 : Reach 95283 := rs (se 1 (by rfl) ⟨71462, by rfl⟩) R142925
theorem R95299 : Reach 95299 := rs (se 1 (by rfl) ⟨71474, by rfl⟩) R142949
theorem R95315 : Reach 95315 := rs (se 1 (by rfl) ⟨71486, by rfl⟩) R142973
theorem R95331 : Reach 95331 := rs (se 1 (by rfl) ⟨71498, by rfl⟩) R142997
theorem R95347 : Reach 95347 := rs (se 1 (by rfl) ⟨71510, by rfl⟩) R143021
theorem R95363 : Reach 95363 := rs (se 1 (by rfl) ⟨71522, by rfl⟩) R143045
theorem R160913 : Reach 160913 := rs (se 2 (by rfl) ⟨60342, by rfl⟩) R120685
theorem R95379 : Reach 95379 := rs (se 1 (by rfl) ⟨71534, by rfl⟩) R143069
theorem R193681 : Reach 193681 := rs (se 2 (by rfl) ⟨72630, by rfl⟩) R145261
theorem R95395 : Reach 95395 := rs (se 1 (by rfl) ⟨71546, by rfl⟩) R143093
theorem R95411 : Reach 95411 := rs (se 1 (by rfl) ⟨71558, by rfl⟩) R143117
theorem R95427 : Reach 95427 := rs (se 1 (by rfl) ⟨71570, by rfl⟩) R143141
theorem R95443 : Reach 95443 := rs (se 1 (by rfl) ⟨71582, by rfl⟩) R143165
theorem R95459 : Reach 95459 := rs (se 1 (by rfl) ⟨71594, by rfl⟩) R143189
theorem R95475 : Reach 95475 := rs (se 1 (by rfl) ⟨71606, by rfl⟩) R143213
theorem R95491 : Reach 95491 := rs (se 1 (by rfl) ⟨71618, by rfl⟩) R143237
theorem R161041 : Reach 161041 := rs (se 2 (by rfl) ⟨60390, by rfl⟩) R120781
theorem R95507 : Reach 95507 := rs (se 1 (by rfl) ⟨71630, by rfl⟩) R143261
theorem R95523 : Reach 95523 := rs (se 1 (by rfl) ⟨71642, by rfl⟩) R143285
theorem R619811 : Reach 619811 := rs (se 1 (by rfl) ⟨464858, by rfl⟩) R929717
theorem R488753 : Reach 488753 := rs (se 2 (by rfl) ⟨183282, by rfl⟩) R366565
theorem R161075 : Reach 161075 := rs (se 1 (by rfl) ⟨120806, by rfl⟩) R241613
theorem R95539 : Reach 95539 := rs (se 1 (by rfl) ⟨71654, by rfl⟩) R143309
theorem R95555 : Reach 95555 := rs (se 1 (by rfl) ⟨71666, by rfl⟩) R143333
theorem R95571 : Reach 95571 := rs (se 1 (by rfl) ⟨71678, by rfl⟩) R143357
theorem R95587 : Reach 95587 := rs (se 1 (by rfl) ⟨71690, by rfl⟩) R143381
theorem R521585 : Reach 521585 := rs (se 2 (by rfl) ⟨195594, by rfl⟩) R391189
theorem R95603 : Reach 95603 := rs (se 1 (by rfl) ⟨71702, by rfl⟩) R143405
theorem R95619 : Reach 95619 := rs (se 1 (by rfl) ⟨71714, by rfl⟩) R143429
theorem R95635 : Reach 95635 := rs (se 1 (by rfl) ⟨71726, by rfl⟩) R143453
theorem R95651 : Reach 95651 := rs (se 1 (by rfl) ⟨71738, by rfl⟩) R143477
theorem R161203 : Reach 161203 := rs (se 1 (by rfl) ⟨120902, by rfl⟩) R241805
theorem R95667 : Reach 95667 := rs (se 1 (by rfl) ⟨71750, by rfl⟩) R143501
theorem R95683 : Reach 95683 := rs (se 1 (by rfl) ⟨71762, by rfl⟩) R143525
theorem R95699 : Reach 95699 := rs (se 1 (by rfl) ⟨71774, by rfl⟩) R143549
theorem R95715 : Reach 95715 := rs (se 1 (by rfl) ⟨71786, by rfl⟩) R143573
theorem R95731 : Reach 95731 := rs (se 1 (by rfl) ⟨71798, by rfl⟩) R143597
theorem R95747 : Reach 95747 := rs (se 1 (by rfl) ⟨71810, by rfl⟩) R143621
theorem R325133 : Reach 325133 := rs (se 3 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R95763 : Reach 95763 := rs (se 1 (by rfl) ⟨71822, by rfl⟩) R143645
theorem R95779 : Reach 95779 := rs (se 1 (by rfl) ⟨71834, by rfl⟩) R143669
theorem R95795 : Reach 95795 := rs (se 1 (by rfl) ⟨71846, by rfl⟩) R143693
theorem R161345 : Reach 161345 := rs (se 2 (by rfl) ⟨60504, by rfl⟩) R121009
theorem R95811 : Reach 95811 := rs (se 1 (by rfl) ⟨71858, by rfl⟩) R143717
theorem R325187 : Reach 325187 := rs (se 1 (by rfl) ⟨243890, by rfl⟩) R487781
theorem R95827 : Reach 95827 := rs (se 1 (by rfl) ⟨71870, by rfl⟩) R143741
theorem R95843 : Reach 95843 := rs (se 1 (by rfl) ⟨71882, by rfl⟩) R143765
theorem R95859 : Reach 95859 := rs (se 1 (by rfl) ⟨71894, by rfl⟩) R143789
theorem R95875 : Reach 95875 := rs (se 1 (by rfl) ⟨71906, by rfl⟩) R143813
theorem R95891 : Reach 95891 := rs (se 1 (by rfl) ⟨71918, by rfl⟩) R143837
theorem R95907 : Reach 95907 := rs (se 1 (by rfl) ⟨71930, by rfl⟩) R143861
theorem R95923 : Reach 95923 := rs (se 1 (by rfl) ⟨71942, by rfl⟩) R143885
theorem R161473 : Reach 161473 := rs (se 2 (by rfl) ⟨60552, by rfl⟩) R121105
theorem R95939 : Reach 95939 := rs (se 1 (by rfl) ⟨71954, by rfl⟩) R143909
theorem R95955 : Reach 95955 := rs (se 1 (by rfl) ⟨71966, by rfl⟩) R143933
theorem R161507 : Reach 161507 := rs (se 1 (by rfl) ⟨121130, by rfl⟩) R242261
theorem R95971 : Reach 95971 := rs (se 1 (by rfl) ⟨71978, by rfl⟩) R143957
theorem R95987 : Reach 95987 := rs (se 1 (by rfl) ⟨71990, by rfl⟩) R143981
theorem R96003 : Reach 96003 := rs (se 1 (by rfl) ⟨72002, by rfl⟩) R144005
theorem R96019 : Reach 96019 := rs (se 1 (by rfl) ⟨72014, by rfl⟩) R144029
theorem R96035 : Reach 96035 := rs (se 1 (by rfl) ⟨72026, by rfl⟩) R144053
theorem R96051 : Reach 96051 := rs (se 1 (by rfl) ⟨72038, by rfl⟩) R144077
theorem R96067 : Reach 96067 := rs (se 1 (by rfl) ⟨72050, by rfl⟩) R144101
theorem R325457 : Reach 325457 := rs (se 2 (by rfl) ⟨122046, by rfl⟩) R244093
theorem R96083 : Reach 96083 := rs (se 1 (by rfl) ⟨72062, by rfl⟩) R144125
theorem R161635 : Reach 161635 := rs (se 1 (by rfl) ⟨121226, by rfl⟩) R242453
theorem R96099 : Reach 96099 := rs (se 1 (by rfl) ⟨72074, by rfl⟩) R144149
theorem R259949 : Reach 259949 := rs (se 3 (by rfl) ⟨48740, by rfl⟩) R97481
theorem R96115 : Reach 96115 := rs (se 1 (by rfl) ⟨72086, by rfl⟩) R144173
theorem R96131 : Reach 96131 := rs (se 1 (by rfl) ⟨72098, by rfl⟩) R144197
theorem R718733 : Reach 718733 := rs (se 3 (by rfl) ⟨134762, by rfl⟩) R269525
theorem R96147 : Reach 96147 := rs (se 1 (by rfl) ⟨72110, by rfl⟩) R144221
theorem R96163 : Reach 96163 := rs (se 1 (by rfl) ⟨72122, by rfl⟩) R144245
theorem R96179 : Reach 96179 := rs (se 1 (by rfl) ⟨72134, by rfl⟩) R144269
theorem R96195 : Reach 96195 := rs (se 1 (by rfl) ⟨72146, by rfl⟩) R144293
theorem R96211 : Reach 96211 := rs (se 1 (by rfl) ⟨72158, by rfl⟩) R144317
theorem R96227 : Reach 96227 := rs (se 1 (by rfl) ⟨72170, by rfl⟩) R144341
theorem R161777 : Reach 161777 := rs (se 2 (by rfl) ⟨60666, by rfl⟩) R121333
theorem R96243 : Reach 96243 := rs (se 1 (by rfl) ⟨72182, by rfl⟩) R144365
theorem R96259 : Reach 96259 := rs (se 1 (by rfl) ⟨72194, by rfl⟩) R144389
theorem R96275 : Reach 96275 := rs (se 1 (by rfl) ⟨72206, by rfl⟩) R144413
theorem R96291 : Reach 96291 := rs (se 1 (by rfl) ⟨72218, by rfl⟩) R144437
theorem R96307 : Reach 96307 := rs (se 1 (by rfl) ⟨72230, by rfl⟩) R144461
theorem R96323 : Reach 96323 := rs (se 1 (by rfl) ⟨72242, by rfl⟩) R144485
theorem R96339 : Reach 96339 := rs (se 1 (by rfl) ⟨72254, by rfl⟩) R144509
theorem R1177699 : Reach 1177699 := rs (se 1 (by rfl) ⟨883274, by rfl⟩) R1766549
theorem R96355 : Reach 96355 := rs (se 1 (by rfl) ⟨72266, by rfl⟩) R144533
theorem R915569 : Reach 915569 := rs (se 2 (by rfl) ⟨343338, by rfl⟩) R686677
theorem R161905 : Reach 161905 := rs (se 2 (by rfl) ⟨60714, by rfl⟩) R121429
theorem R96371 : Reach 96371 := rs (se 1 (by rfl) ⟨72278, by rfl⟩) R144557
theorem R96387 : Reach 96387 := rs (se 1 (by rfl) ⟨72290, by rfl⟩) R144581
theorem R161939 : Reach 161939 := rs (se 1 (by rfl) ⟨121454, by rfl⟩) R242909
theorem R96403 : Reach 96403 := rs (se 1 (by rfl) ⟨72302, by rfl⟩) R144605
theorem R96419 : Reach 96419 := rs (se 1 (by rfl) ⟨72314, by rfl⟩) R144629
theorem R260273 : Reach 260273 := rs (se 2 (by rfl) ⟨97602, by rfl⟩) R195205
theorem R96435 : Reach 96435 := rs (se 1 (by rfl) ⟨72326, by rfl⟩) R144653
theorem R96451 : Reach 96451 := rs (se 1 (by rfl) ⟨72338, by rfl⟩) R144677
theorem R1308869 : Reach 1308869 := rs (se 4 (by rfl) ⟨122706, by rfl⟩) R245413
theorem R96467 : Reach 96467 := rs (se 1 (by rfl) ⟨72350, by rfl⟩) R144701
theorem R96483 : Reach 96483 := rs (se 1 (by rfl) ⟨72362, by rfl⟩) R144725
theorem R96499 : Reach 96499 := rs (se 1 (by rfl) ⟨72374, by rfl⟩) R144749
theorem R96515 : Reach 96515 := rs (se 1 (by rfl) ⟨72386, by rfl⟩) R144773
theorem R162067 : Reach 162067 := rs (se 1 (by rfl) ⟨121550, by rfl⟩) R243101
theorem R96531 : Reach 96531 := rs (se 1 (by rfl) ⟨72398, by rfl⟩) R144797
theorem R96547 : Reach 96547 := rs (se 1 (by rfl) ⟨72410, by rfl⟩) R144821
theorem R96563 : Reach 96563 := rs (se 1 (by rfl) ⟨72422, by rfl⟩) R144845
theorem R96579 : Reach 96579 := rs (se 1 (by rfl) ⟨72434, by rfl⟩) R144869
theorem R96595 : Reach 96595 := rs (se 1 (by rfl) ⟨72446, by rfl⟩) R144893
theorem R96611 : Reach 96611 := rs (se 1 (by rfl) ⟨72458, by rfl⟩) R144917
theorem R325997 : Reach 325997 := rs (se 3 (by rfl) ⟨61124, by rfl⟩) R122249
theorem R96627 : Reach 96627 := rs (se 1 (by rfl) ⟨72470, by rfl⟩) R144941
theorem R96643 : Reach 96643 := rs (se 1 (by rfl) ⟨72482, by rfl⟩) R144965
theorem R96659 : Reach 96659 := rs (se 1 (by rfl) ⟨72494, by rfl⟩) R144989
theorem R162209 : Reach 162209 := rs (se 2 (by rfl) ⟨60828, by rfl⟩) R121657
theorem R326051 : Reach 326051 := rs (se 1 (by rfl) ⟨244538, by rfl⟩) R489077
theorem R96675 : Reach 96675 := rs (se 1 (by rfl) ⟨72506, by rfl⟩) R145013
theorem R96691 : Reach 96691 := rs (se 1 (by rfl) ⟨72518, by rfl⟩) R145037
theorem R96707 : Reach 96707 := rs (se 1 (by rfl) ⟨72530, by rfl⟩) R145061
theorem R96723 : Reach 96723 := rs (se 1 (by rfl) ⟨72542, by rfl⟩) R145085
theorem R96739 : Reach 96739 := rs (se 1 (by rfl) ⟨72554, by rfl⟩) R145109
theorem R96755 : Reach 96755 := rs (se 1 (by rfl) ⟨72566, by rfl⟩) R145133
theorem R96771 : Reach 96771 := rs (se 1 (by rfl) ⟨72578, by rfl⟩) R145157
theorem R96787 : Reach 96787 := rs (se 1 (by rfl) ⟨72590, by rfl⟩) R145181
theorem R162337 : Reach 162337 := rs (se 2 (by rfl) ⟨60876, by rfl⟩) R121753
theorem R96803 : Reach 96803 := rs (se 1 (by rfl) ⟨72602, by rfl⟩) R145205
theorem R96819 : Reach 96819 := rs (se 1 (by rfl) ⟨72614, by rfl⟩) R145229
theorem R162371 : Reach 162371 := rs (se 1 (by rfl) ⟨121778, by rfl⟩) R243557
theorem R96835 : Reach 96835 := rs (se 1 (by rfl) ⟨72626, by rfl⟩) R145253
theorem R424525 : Reach 424525 := rs (se 3 (by rfl) ⟨79598, by rfl⟩) R159197
theorem R96851 : Reach 96851 := rs (se 1 (by rfl) ⟨72638, by rfl⟩) R145277
theorem R96867 : Reach 96867 := rs (se 1 (by rfl) ⟨72650, by rfl⟩) R145301
theorem R96883 : Reach 96883 := rs (se 1 (by rfl) ⟨72662, by rfl⟩) R145325
theorem R96899 : Reach 96899 := rs (se 1 (by rfl) ⟨72674, by rfl⟩) R145349
theorem R260749 : Reach 260749 := rs (se 3 (by rfl) ⟨48890, by rfl⟩) R97781
theorem R96915 : Reach 96915 := rs (se 1 (by rfl) ⟨72686, by rfl⟩) R145373
theorem R96931 : Reach 96931 := rs (se 1 (by rfl) ⟨72698, by rfl⟩) R145397
theorem R326321 : Reach 326321 := rs (se 2 (by rfl) ⟨122370, by rfl⟩) R244741
theorem R96947 : Reach 96947 := rs (se 1 (by rfl) ⟨72710, by rfl⟩) R145421
theorem R162499 : Reach 162499 := rs (se 1 (by rfl) ⟨121874, by rfl⟩) R243749
theorem R96963 : Reach 96963 := rs (se 1 (by rfl) ⟨72722, by rfl⟩) R145445
theorem R588485 : Reach 588485 := rs (se 4 (by rfl) ⟨55170, by rfl⟩) R110341
theorem R96979 : Reach 96979 := rs (se 1 (by rfl) ⟨72734, by rfl⟩) R145469
theorem R490211 : Reach 490211 := rs (se 1 (by rfl) ⟨367658, by rfl⟩) R735317
theorem R96995 : Reach 96995 := rs (se 1 (by rfl) ⟨72746, by rfl⟩) R145493
theorem R97011 : Reach 97011 := rs (se 1 (by rfl) ⟨72758, by rfl⟩) R145517
theorem R97027 : Reach 97027 := rs (se 1 (by rfl) ⟨72770, by rfl⟩) R145541
theorem R97043 : Reach 97043 := rs (se 1 (by rfl) ⟨72782, by rfl⟩) R145565
theorem R97059 : Reach 97059 := rs (se 1 (by rfl) ⟨72794, by rfl⟩) R145589
theorem R97075 : Reach 97075 := rs (se 1 (by rfl) ⟨72806, by rfl⟩) R145613
theorem R97091 : Reach 97091 := rs (se 1 (by rfl) ⟨72818, by rfl⟩) R145637
theorem R162641 : Reach 162641 := rs (se 2 (by rfl) ⟨60990, by rfl⟩) R121981
theorem R97107 : Reach 97107 := rs (se 1 (by rfl) ⟨72830, by rfl⟩) R145661
theorem R97123 : Reach 97123 := rs (se 1 (by rfl) ⟨72842, by rfl⟩) R145685
theorem R97139 : Reach 97139 := rs (se 1 (by rfl) ⟨72854, by rfl⟩) R145709
theorem R97155 : Reach 97155 := rs (se 1 (by rfl) ⟨72866, by rfl⟩) R145733
theorem R97171 : Reach 97171 := rs (se 1 (by rfl) ⟨72878, by rfl⟩) R145757
theorem R97187 : Reach 97187 := rs (se 1 (by rfl) ⟨72890, by rfl⟩) R145781
theorem R97203 : Reach 97203 := rs (se 1 (by rfl) ⟨72902, by rfl⟩) R145805
theorem R97219 : Reach 97219 := rs (se 1 (by rfl) ⟨72914, by rfl⟩) R145829
theorem R162769 : Reach 162769 := rs (se 2 (by rfl) ⟨61038, by rfl⟩) R122077
theorem R261073 : Reach 261073 := rs (se 2 (by rfl) ⟨97902, by rfl⟩) R195805
theorem R97235 : Reach 97235 := rs (se 1 (by rfl) ⟨72926, by rfl⟩) R145853
theorem R97251 : Reach 97251 := rs (se 1 (by rfl) ⟨72938, by rfl⟩) R145877
theorem R621553 : Reach 621553 := rs (se 2 (by rfl) ⟨233082, by rfl⟩) R466165
theorem R162803 : Reach 162803 := rs (se 1 (by rfl) ⟨122102, by rfl⟩) R244205
theorem R97267 : Reach 97267 := rs (se 1 (by rfl) ⟨72950, by rfl⟩) R145901
theorem R97283 : Reach 97283 := rs (se 1 (by rfl) ⟨72962, by rfl⟩) R145925
theorem R97299 : Reach 97299 := rs (se 1 (by rfl) ⟨72974, by rfl⟩) R145949
theorem R97315 : Reach 97315 := rs (se 1 (by rfl) ⟨72986, by rfl⟩) R145973
theorem R97331 : Reach 97331 := rs (se 1 (by rfl) ⟨72998, by rfl⟩) R145997
theorem R3013685 : Reach 3013685 := rs (se 5 (by rfl) ⟨141266, by rfl⟩) R282533
theorem R97347 : Reach 97347 := rs (se 1 (by rfl) ⟨73010, by rfl⟩) R146021
theorem R97363 : Reach 97363 := rs (se 1 (by rfl) ⟨73022, by rfl⟩) R146045
theorem R97379 : Reach 97379 := rs (se 1 (by rfl) ⟨73034, by rfl⟩) R146069
theorem R162931 : Reach 162931 := rs (se 1 (by rfl) ⟨122198, by rfl⟩) R244397
theorem R97395 : Reach 97395 := rs (se 1 (by rfl) ⟨73046, by rfl⟩) R146093
theorem R162947 : Reach 162947 := rs (se 1 (by rfl) ⟨122210, by rfl⟩) R244421
theorem R97411 : Reach 97411 := rs (se 1 (by rfl) ⟨73058, by rfl⟩) R146117
theorem R97427 : Reach 97427 := rs (se 1 (by rfl) ⟨73070, by rfl⟩) R146141
theorem R97443 : Reach 97443 := rs (se 1 (by rfl) ⟨73082, by rfl⟩) R146165
theorem R97459 : Reach 97459 := rs (se 1 (by rfl) ⟨73094, by rfl⟩) R146189
theorem R97475 : Reach 97475 := rs (se 1 (by rfl) ⟨73106, by rfl⟩) R146213
theorem R326861 : Reach 326861 := rs (se 3 (by rfl) ⟨61286, by rfl⟩) R122573
theorem R97491 : Reach 97491 := rs (se 1 (by rfl) ⟨73118, by rfl⟩) R146237
theorem R97507 : Reach 97507 := rs (se 1 (by rfl) ⟨73130, by rfl⟩) R146261
theorem R97523 : Reach 97523 := rs (se 1 (by rfl) ⟨73142, by rfl⟩) R146285
theorem R163073 : Reach 163073 := rs (se 2 (by rfl) ⟨61152, by rfl⟩) R122305
theorem R326915 : Reach 326915 := rs (se 1 (by rfl) ⟨245186, by rfl⟩) R490373
theorem R97539 : Reach 97539 := rs (se 1 (by rfl) ⟨73154, by rfl⟩) R146309
theorem R97555 : Reach 97555 := rs (se 1 (by rfl) ⟨73166, by rfl⟩) R146333
theorem R97571 : Reach 97571 := rs (se 1 (by rfl) ⟨73178, by rfl⟩) R146357
theorem R97587 : Reach 97587 := rs (se 1 (by rfl) ⟨73190, by rfl⟩) R146381
theorem R97603 : Reach 97603 := rs (se 1 (by rfl) ⟨73202, by rfl⟩) R146405
theorem R97619 : Reach 97619 := rs (se 1 (by rfl) ⟨73214, by rfl⟩) R146429
theorem R97635 : Reach 97635 := rs (se 1 (by rfl) ⟨73226, by rfl⟩) R146453
theorem R130417 : Reach 130417 := rs (se 2 (by rfl) ⟨48906, by rfl⟩) R97813
theorem R97651 : Reach 97651 := rs (se 1 (by rfl) ⟨73238, by rfl⟩) R146477
theorem R163201 : Reach 163201 := rs (se 2 (by rfl) ⟨61200, by rfl⟩) R122401
theorem R228739 : Reach 228739 := rs (se 1 (by rfl) ⟨171554, by rfl⟩) R343109
theorem R97667 : Reach 97667 := rs (se 1 (by rfl) ⟨73250, by rfl⟩) R146501
theorem R97683 : Reach 97683 := rs (se 1 (by rfl) ⟨73262, by rfl⟩) R146525
theorem R163235 : Reach 163235 := rs (se 1 (by rfl) ⟨122426, by rfl⟩) R244853
theorem R97699 : Reach 97699 := rs (se 1 (by rfl) ⟨73274, by rfl⟩) R146549
theorem R97715 : Reach 97715 := rs (se 1 (by rfl) ⟨73286, by rfl⟩) R146573
theorem R97731 : Reach 97731 := rs (se 1 (by rfl) ⟨73298, by rfl⟩) R146597
theorem R97747 : Reach 97747 := rs (se 1 (by rfl) ⟨73310, by rfl⟩) R146621
theorem R97763 : Reach 97763 := rs (se 1 (by rfl) ⟨73322, by rfl⟩) R146645
theorem R97779 : Reach 97779 := rs (se 1 (by rfl) ⟨73334, by rfl⟩) R146669
theorem R97795 : Reach 97795 := rs (se 1 (by rfl) ⟨73346, by rfl⟩) R146693
theorem R491021 : Reach 491021 := rs (se 3 (by rfl) ⟨92066, by rfl⟩) R184133
theorem R327185 : Reach 327185 := rs (se 2 (by rfl) ⟨122694, by rfl⟩) R245389
theorem R97811 : Reach 97811 := rs (se 1 (by rfl) ⟨73358, by rfl⟩) R146717
theorem R163363 : Reach 163363 := rs (se 1 (by rfl) ⟨122522, by rfl⟩) R245045
theorem R97827 : Reach 97827 := rs (se 1 (by rfl) ⟨73370, by rfl⟩) R146741
theorem R97843 : Reach 97843 := rs (se 1 (by rfl) ⟨73382, by rfl⟩) R146765
theorem R97859 : Reach 97859 := rs (se 1 (by rfl) ⟨73394, by rfl⟩) R146789
theorem R97875 : Reach 97875 := rs (se 1 (by rfl) ⟨73406, by rfl⟩) R146813
theorem R97891 : Reach 97891 := rs (se 1 (by rfl) ⟨73418, by rfl⟩) R146837
theorem R97907 : Reach 97907 := rs (se 1 (by rfl) ⟨73430, by rfl⟩) R146861
theorem R97923 : Reach 97923 := rs (se 1 (by rfl) ⟨73442, by rfl⟩) R146885
theorem R97939 : Reach 97939 := rs (se 1 (by rfl) ⟨73454, by rfl⟩) R146909
theorem R97955 : Reach 97955 := rs (se 1 (by rfl) ⟨73466, by rfl⟩) R146933
theorem R163505 : Reach 163505 := rs (se 2 (by rfl) ⟨61314, by rfl⟩) R122629
theorem R97971 : Reach 97971 := rs (se 1 (by rfl) ⟨73478, by rfl⟩) R146957
theorem R97987 : Reach 97987 := rs (se 1 (by rfl) ⟨73490, by rfl⟩) R146981
theorem R98003 : Reach 98003 := rs (se 1 (by rfl) ⟨73502, by rfl⟩) R147005
theorem R98019 : Reach 98019 := rs (se 1 (by rfl) ⟨73514, by rfl⟩) R147029
theorem R98035 : Reach 98035 := rs (se 1 (by rfl) ⟨73526, by rfl⟩) R147053
theorem R98051 : Reach 98051 := rs (se 1 (by rfl) ⟨73538, by rfl⟩) R147077
theorem R98067 : Reach 98067 := rs (se 1 (by rfl) ⟨73550, by rfl⟩) R147101
theorem R98083 : Reach 98083 := rs (se 1 (by rfl) ⟨73562, by rfl⟩) R147125
theorem R163633 : Reach 163633 := rs (se 2 (by rfl) ⟨61362, by rfl⟩) R122725
theorem R98099 : Reach 98099 := rs (se 1 (by rfl) ⟨73574, by rfl⟩) R147149
theorem R98115 : Reach 98115 := rs (se 1 (by rfl) ⟨73586, by rfl⟩) R147173
theorem R163667 : Reach 163667 := rs (se 1 (by rfl) ⟨122750, by rfl⟩) R245501
theorem R98131 : Reach 98131 := rs (se 1 (by rfl) ⟨73598, by rfl⟩) R147197
theorem R98147 : Reach 98147 := rs (se 1 (by rfl) ⟨73610, by rfl⟩) R147221
theorem R98163 : Reach 98163 := rs (se 1 (by rfl) ⟨73622, by rfl⟩) R147245
theorem R98179 : Reach 98179 := rs (se 1 (by rfl) ⟨73634, by rfl⟩) R147269
theorem R98195 : Reach 98195 := rs (se 1 (by rfl) ⟨73646, by rfl⟩) R147293
theorem R98211 : Reach 98211 := rs (se 1 (by rfl) ⟨73658, by rfl⟩) R147317
theorem R98227 : Reach 98227 := rs (se 1 (by rfl) ⟨73670, by rfl⟩) R147341
theorem R98243 : Reach 98243 := rs (se 1 (by rfl) ⟨73682, by rfl⟩) R147365
theorem R163795 : Reach 163795 := rs (se 1 (by rfl) ⟨122846, by rfl⟩) R245693
theorem R98259 : Reach 98259 := rs (se 1 (by rfl) ⟨73694, by rfl⟩) R147389
theorem R98275 : Reach 98275 := rs (se 1 (by rfl) ⟨73706, by rfl⟩) R147413
theorem R98291 : Reach 98291 := rs (se 1 (by rfl) ⟨73718, by rfl⟩) R147437
theorem R98315 : Reach 98315 := rs (se 1 (by rfl) ⟨73736, by rfl⟩) R147473
theorem R98327 : Reach 98327 := rs (se 1 (by rfl) ⟨73745, by rfl⟩) R147491
theorem R98347 : Reach 98347 := rs (se 1 (by rfl) ⟨73760, by rfl⟩) R147521
theorem R98359 : Reach 98359 := rs (se 1 (by rfl) ⟨73769, by rfl⟩) R147539
theorem R98379 : Reach 98379 := rs (se 1 (by rfl) ⟨73784, by rfl⟩) R147569
theorem R98391 : Reach 98391 := rs (se 1 (by rfl) ⟨73793, by rfl⟩) R147587
theorem R98411 : Reach 98411 := rs (se 1 (by rfl) ⟨73808, by rfl⟩) R147617
theorem R98423 : Reach 98423 := rs (se 1 (by rfl) ⟨73817, by rfl⟩) R147635
theorem R98443 : Reach 98443 := rs (se 1 (by rfl) ⟨73832, by rfl⟩) R147665
theorem R163991 : Reach 163991 := rs (se 1 (by rfl) ⟨122993, by rfl⟩) R245987
theorem R98455 : Reach 98455 := rs (se 1 (by rfl) ⟨73841, by rfl⟩) R147683
theorem R98475 : Reach 98475 := rs (se 1 (by rfl) ⟨73856, by rfl⟩) R147713
theorem R98487 : Reach 98487 := rs (se 1 (by rfl) ⟨73865, by rfl⟩) R147731
theorem R98507 : Reach 98507 := rs (se 1 (by rfl) ⟨73880, by rfl⟩) R147761
theorem R98519 : Reach 98519 := rs (se 1 (by rfl) ⟨73889, by rfl⟩) R147779
theorem R98539 : Reach 98539 := rs (se 1 (by rfl) ⟨73904, by rfl⟩) R147809
theorem R98551 : Reach 98551 := rs (se 1 (by rfl) ⟨73913, by rfl⟩) R147827
theorem R98571 : Reach 98571 := rs (se 1 (by rfl) ⟨73928, by rfl⟩) R147857
theorem R164119 : Reach 164119 := rs (se 1 (by rfl) ⟨123089, by rfl⟩) R246179
theorem R98583 : Reach 98583 := rs (se 1 (by rfl) ⟨73937, by rfl⟩) R147875
theorem R98603 : Reach 98603 := rs (se 1 (by rfl) ⟨73952, by rfl⟩) R147905
theorem R98615 : Reach 98615 := rs (se 1 (by rfl) ⟨73961, by rfl⟩) R147923
theorem R98635 : Reach 98635 := rs (se 1 (by rfl) ⟨73976, by rfl⟩) R147953
theorem R98647 : Reach 98647 := rs (se 1 (by rfl) ⟨73985, by rfl⟩) R147971
theorem R98667 : Reach 98667 := rs (se 1 (by rfl) ⟨74000, by rfl⟩) R148001
theorem R98679 : Reach 98679 := rs (se 1 (by rfl) ⟨74009, by rfl⟩) R148019
theorem R524675 : Reach 524675 := rs (se 1 (by rfl) ⟨393506, by rfl⟩) R787013
theorem R98699 : Reach 98699 := rs (se 1 (by rfl) ⟨74024, by rfl⟩) R148049
theorem R98711 : Reach 98711 := rs (se 1 (by rfl) ⟨74033, by rfl⟩) R148067
theorem R98731 : Reach 98731 := rs (se 1 (by rfl) ⟨74048, by rfl⟩) R148097
theorem R98743 : Reach 98743 := rs (se 1 (by rfl) ⟨74057, by rfl⟩) R148115
theorem R98763 : Reach 98763 := rs (se 1 (by rfl) ⟨74072, by rfl⟩) R148145
theorem R98775 : Reach 98775 := rs (se 1 (by rfl) ⟨74081, by rfl⟩) R148163
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R491993 : Reach 491993 := rs (se 2 (by rfl) ⟨184497, by rfl⟩) R368995
theorem R328157 : Reach 328157 := rs (se 3 (by rfl) ⟨61529, by rfl⟩) R123059
theorem R98795 : Reach 98795 := rs (se 1 (by rfl) ⟨74096, by rfl⟩) R148193
theorem R98807 : Reach 98807 := rs (se 1 (by rfl) ⟨74105, by rfl⟩) R148211
theorem R98827 : Reach 98827 := rs (se 1 (by rfl) ⟨74120, by rfl⟩) R148241
theorem R98839 : Reach 98839 := rs (se 1 (by rfl) ⟨74129, by rfl⟩) R148259
theorem R98859 : Reach 98859 := rs (se 1 (by rfl) ⟨74144, by rfl⟩) R148289
theorem R98871 : Reach 98871 := rs (se 1 (by rfl) ⟨74153, by rfl⟩) R148307
theorem R98891 : Reach 98891 := rs (se 1 (by rfl) ⟨74168, by rfl⟩) R148337
theorem R98903 : Reach 98903 := rs (se 1 (by rfl) ⟨74177, by rfl⟩) R148355
theorem R98923 : Reach 98923 := rs (se 1 (by rfl) ⟨74192, by rfl⟩) R148385
theorem R98935 : Reach 98935 := rs (se 1 (by rfl) ⟨74201, by rfl⟩) R148403
theorem R98955 : Reach 98955 := rs (se 1 (by rfl) ⟨74216, by rfl⟩) R148433
theorem R950935 : Reach 950935 := rs (se 1 (by rfl) ⟨713201, by rfl⟩) R1426403
theorem R98967 : Reach 98967 := rs (se 1 (by rfl) ⟨74225, by rfl⟩) R148451
theorem R98987 : Reach 98987 := rs (se 1 (by rfl) ⟨74240, by rfl⟩) R148481
theorem R98999 : Reach 98999 := rs (se 1 (by rfl) ⟨74249, by rfl⟩) R148499
theorem R99019 : Reach 99019 := rs (se 1 (by rfl) ⟨74264, by rfl⟩) R148529
theorem R99031 : Reach 99031 := rs (se 1 (by rfl) ⟨74273, by rfl⟩) R148547
theorem R131801 : Reach 131801 := rs (se 2 (by rfl) ⟨49425, by rfl⟩) R98851
theorem R99051 : Reach 99051 := rs (se 1 (by rfl) ⟨74288, by rfl⟩) R148577
theorem R99063 : Reach 99063 := rs (se 1 (by rfl) ⟨74297, by rfl⟩) R148595
theorem R361219 : Reach 361219 := rs (se 1 (by rfl) ⟨270914, by rfl⟩) R541829
theorem R99083 : Reach 99083 := rs (se 1 (by rfl) ⟨74312, by rfl⟩) R148625
theorem R99095 : Reach 99095 := rs (se 1 (by rfl) ⟨74321, by rfl⟩) R148643
theorem R99115 : Reach 99115 := rs (se 1 (by rfl) ⟨74336, by rfl⟩) R148673
theorem R99127 : Reach 99127 := rs (se 1 (by rfl) ⟨74345, by rfl⟩) R148691
theorem R590723 : Reach 590723 := rs (se 1 (by rfl) ⟨443042, by rfl⟩) R886085
theorem R164747 : Reach 164747 := rs (se 1 (by rfl) ⟨123560, by rfl⟩) R247121
theorem R164875 : Reach 164875 := rs (se 1 (by rfl) ⟨123656, by rfl⟩) R247313
theorem R361523 : Reach 361523 := rs (se 1 (by rfl) ⟨271142, by rfl⟩) R542285
theorem R165017 : Reach 165017 := rs (se 2 (by rfl) ⟨61881, by rfl⟩) R123763
theorem R165145 : Reach 165145 := rs (se 2 (by rfl) ⟨61929, by rfl⟩) R123859
theorem R329291 : Reach 329291 := rs (se 1 (by rfl) ⟨246968, by rfl⟩) R493937
theorem R689795 : Reach 689795 := rs (se 1 (by rfl) ⟨517346, by rfl⟩) R1034693
theorem R362177 : Reach 362177 := rs (se 2 (by rfl) ⟨135816, by rfl⟩) R271633
theorem R952013 : Reach 952013 := rs (se 3 (by rfl) ⟨178502, by rfl⟩) R357005
theorem R165719 : Reach 165719 := rs (se 1 (by rfl) ⟨124289, by rfl⟩) R248579
theorem R329561 : Reach 329561 := rs (se 2 (by rfl) ⟨123585, by rfl⟩) R247171
theorem R296797 : Reach 296797 := rs (se 3 (by rfl) ⟨55649, by rfl⟩) R111299
theorem R952165 : Reach 952165 := rs (se 4 (by rfl) ⟨89265, by rfl⟩) R178531
theorem R165847 : Reach 165847 := rs (se 1 (by rfl) ⟨124385, by rfl⟩) R248771
theorem R493613 : Reach 493613 := rs (se 3 (by rfl) ⟨92552, by rfl⟩) R185105
theorem R3869045 : Reach 3869045 := rs (se 5 (by rfl) ⟨181361, by rfl⟩) R362723
theorem R461207 : Reach 461207 := rs (se 1 (by rfl) ⟨345905, by rfl⟩) R691811
theorem R526771 : Reach 526771 := rs (se 1 (by rfl) ⟨395078, by rfl⟩) R790157
theorem R821765 : Reach 821765 := rs (se 4 (by rfl) ⟨77040, by rfl⟩) R154081
theorem R231959 : Reach 231959 := rs (se 1 (by rfl) ⟨173969, by rfl⟩) R347939
theorem R330263 : Reach 330263 := rs (se 1 (by rfl) ⟨247697, by rfl⟩) R495395
theorem R166475 : Reach 166475 := rs (se 1 (by rfl) ⟨124856, by rfl⟩) R249713
theorem R166603 : Reach 166603 := rs (se 1 (by rfl) ⟨124952, by rfl⟩) R249905
theorem R232267 : Reach 232267 := rs (se 1 (by rfl) ⟨174200, by rfl⟩) R348401
theorem R166745 : Reach 166745 := rs (se 2 (by rfl) ⟨62529, by rfl⟩) R125059
theorem R363437 : Reach 363437 := rs (se 3 (by rfl) ⟨68144, by rfl⟩) R136289
theorem R363467 : Reach 363467 := rs (se 1 (by rfl) ⟨272600, by rfl⟩) R545201
theorem R98295 : Reach 98295 := rs (se 1 (by rfl) ⟨73721, by rfl⟩) R147443
theorem R2690009 : Reach 2690009 := rs (se 2 (by rfl) ⟨1008753, by rfl⟩) R2017507
theorem R166873 : Reach 166873 := rs (se 2 (by rfl) ⟨62577, by rfl⟩) R125155
theorem R330803 : Reach 330803 := rs (se 1 (by rfl) ⟨248102, by rfl⟩) R496205
theorem R232523 : Reach 232523 := rs (se 1 (by rfl) ⟨174392, by rfl⟩) R348785
theorem R2001995 : Reach 2001995 := rs (se 1 (by rfl) ⟨1501496, by rfl⟩) R3002993
theorem R396505 : Reach 396505 := rs (se 2 (by rfl) ⟨148689, by rfl⟩) R297379
theorem R331073 : Reach 331073 := rs (se 2 (by rfl) ⟨124152, by rfl⟩) R248305
theorem R364121 : Reach 364121 := rs (se 2 (by rfl) ⟨136545, by rfl⟩) R273091
theorem R331613 : Reach 331613 := rs (se 3 (by rfl) ⟨62177, by rfl⟩) R124355
theorem R364439 : Reach 364439 := rs (se 1 (by rfl) ⟨273329, by rfl⟩) R546659
theorem R299159 : Reach 299159 := rs (se 1 (by rfl) ⟨224369, by rfl⟩) R448739
theorem R365107 : Reach 365107 := rs (se 1 (by rfl) ⟨273830, by rfl⟩) R547661
theorem R332363 : Reach 332363 := rs (se 1 (by rfl) ⟨249272, by rfl⟩) R498545
theorem R725597 : Reach 725597 := rs (se 3 (by rfl) ⟨136049, by rfl⟩) R272099
theorem R1184557 : Reach 1184557 := rs (se 3 (by rfl) ⟨222104, by rfl⟩) R444209
theorem R234419 : Reach 234419 := rs (se 1 (by rfl) ⟨175814, by rfl⟩) R351629
theorem R332747 : Reach 332747 := rs (se 1 (by rfl) ⟨249560, by rfl⟩) R499121
theorem R693197 : Reach 693197 := rs (se 3 (by rfl) ⟨129974, by rfl⟩) R259949
theorem R103447 : Reach 103447 := rs (se 1 (by rfl) ⟨77585, by rfl⟩) R155171
theorem R562241 : Reach 562241 := rs (se 2 (by rfl) ⟨210840, by rfl⟩) R421681
theorem R464089 : Reach 464089 := rs (se 2 (by rfl) ⟨174033, by rfl⟩) R348067
theorem R333017 : Reach 333017 := rs (se 2 (by rfl) ⟨124881, by rfl⟩) R249763
theorem R169303 : Reach 169303 := rs (se 1 (by rfl) ⟨126977, by rfl⟩) R253955
theorem R792139 : Reach 792139 := rs (se 1 (by rfl) ⟨594104, by rfl⟩) R1188209
theorem R366353 : Reach 366353 := rs (se 2 (by rfl) ⟨137382, by rfl⟩) R274765
theorem R137047 : Reach 137047 := rs (se 1 (by rfl) ⟨102785, by rfl⟩) R205571
theorem R497501 : Reach 497501 := rs (se 3 (by rfl) ⟨93281, by rfl⟩) R186563
theorem R333719 : Reach 333719 := rs (se 1 (by rfl) ⟨250289, by rfl⟩) R500579
theorem R235543 : Reach 235543 := rs (se 1 (by rfl) ⟨176657, by rfl⟩) R353315
theorem R825389 : Reach 825389 := rs (se 3 (by rfl) ⟨154760, by rfl⟩) R309521
theorem R203033 : Reach 203033 := rs (se 2 (by rfl) ⟨76137, by rfl⟩) R152275
theorem R334259 : Reach 334259 := rs (se 1 (by rfl) ⟨250694, by rfl⟩) R501389
theorem R367051 : Reach 367051 := rs (se 1 (by rfl) ⟨275288, by rfl⟩) R550577
theorem R105143 : Reach 105143 := rs (se 1 (by rfl) ⟨78857, by rfl⟩) R157715
theorem R334529 : Reach 334529 := rs (se 2 (by rfl) ⟨125448, by rfl⟩) R250897
theorem R367325 : Reach 367325 := rs (se 3 (by rfl) ⟨68873, by rfl⟩) R137747
theorem R1121201 : Reach 1121201 := rs (se 2 (by rfl) ⟨420450, by rfl⟩) R840901
theorem R203801 : Reach 203801 := rs (se 2 (by rfl) ⟨76425, by rfl⟩) R152851
theorem R466013 : Reach 466013 := rs (se 3 (by rfl) ⟨87377, by rfl⟩) R174755
theorem R2202805 : Reach 2202805 := rs (se 5 (by rfl) ⟨103256, by rfl⟩) R206513
theorem R695557 : Reach 695557 := rs (se 4 (by rfl) ⟨65208, by rfl⟩) R130417
theorem R400657 : Reach 400657 := rs (se 2 (by rfl) ⟨150246, by rfl⟩) R300493
theorem R597293 : Reach 597293 := rs (se 3 (by rfl) ⟨111992, by rfl⟩) R223985
theorem R466241 : Reach 466241 := rs (se 2 (by rfl) ⟨174840, by rfl⟩) R349681
theorem R368023 : Reach 368023 := rs (se 1 (by rfl) ⟨276017, by rfl⟩) R552035
theorem R204211 : Reach 204211 := rs (se 1 (by rfl) ⟨153158, by rfl⟩) R306317
theorem R892433 : Reach 892433 := rs (se 2 (by rfl) ⟨334662, by rfl⟩) R669325
theorem R204545 : Reach 204545 := rs (se 2 (by rfl) ⟨76704, by rfl⟩) R153409
theorem R139097 : Reach 139097 := rs (se 2 (by rfl) ⟨52161, by rfl⟩) R104323
theorem R499607 : Reach 499607 := rs (se 1 (by rfl) ⟨374705, by rfl⟩) R749411
theorem R4169879 : Reach 4169879 := rs (se 1 (by rfl) ⟨3127409, by rfl⟩) R6254819
theorem R630935 : Reach 630935 := rs (se 1 (by rfl) ⟨473201, by rfl⟩) R946403
theorem R368813 : Reach 368813 := rs (se 3 (by rfl) ⟨69152, by rfl⟩) R138305
theorem R827779 : Reach 827779 := rs (se 1 (by rfl) ⟨620834, by rfl⟩) R1241669
theorem R205271 : Reach 205271 := rs (se 1 (by rfl) ⟨153953, by rfl⟩) R307907
theorem R139735 : Reach 139735 := rs (se 1 (by rfl) ⟨104801, by rfl⟩) R209603
theorem R107095 : Reach 107095 := rs (se 1 (by rfl) ⟨80321, by rfl⟩) R160643
theorem R303709 : Reach 303709 := rs (se 3 (by rfl) ⟨56945, by rfl⟩) R113891
theorem R631475 : Reach 631475 := rs (se 1 (by rfl) ⟨473606, by rfl⟩) R947213
theorem R107275 : Reach 107275 := rs (se 1 (by rfl) ⟨80456, by rfl⟩) R160913
theorem R566033 : Reach 566033 := rs (se 2 (by rfl) ⟨212262, by rfl⟩) R424525
theorem R1581869 : Reach 1581869 := rs (se 3 (by rfl) ⟨296600, by rfl⟩) R593201
theorem R107383 : Reach 107383 := rs (se 1 (by rfl) ⟨80537, by rfl⟩) R161075
theorem R271325 : Reach 271325 := rs (se 3 (by rfl) ⟨50873, by rfl⟩) R101747
theorem R107563 : Reach 107563 := rs (se 1 (by rfl) ⟨80672, by rfl⟩) R161345
theorem R107671 : Reach 107671 := rs (se 1 (by rfl) ⟨80753, by rfl⟩) R161507
theorem R140555 : Reach 140555 := rs (se 1 (by rfl) ⟨105416, by rfl⟩) R210833
theorem R271667 : Reach 271667 := rs (se 1 (by rfl) ⟨203750, by rfl⟩) R407501
theorem R828737 : Reach 828737 := rs (se 2 (by rfl) ⟨310776, by rfl⟩) R621553
theorem R107851 : Reach 107851 := rs (se 1 (by rfl) ⟨80888, by rfl⟩) R161777
theorem R107959 : Reach 107959 := rs (se 1 (by rfl) ⟨80969, by rfl⟩) R161939
theorem R173515 : Reach 173515 := rs (se 1 (by rfl) ⟨130136, by rfl⟩) R260273
theorem R402961 : Reach 402961 := rs (se 2 (by rfl) ⟨151110, by rfl⟩) R302221
theorem R370241 : Reach 370241 := rs (se 2 (by rfl) ⟨138840, by rfl⟩) R277681
theorem R108139 : Reach 108139 := rs (se 1 (by rfl) ⟨81104, by rfl⟩) R162209
theorem R108247 : Reach 108247 := rs (se 1 (by rfl) ⟨81185, by rfl⟩) R162371
theorem R304985 : Reach 304985 := rs (se 2 (by rfl) ⟨114369, by rfl⟩) R228739
theorem R108427 : Reach 108427 := rs (se 1 (by rfl) ⟨81320, by rfl⟩) R162641
theorem R108535 : Reach 108535 := rs (se 1 (by rfl) ⟨81401, by rfl⟩) R162803
theorem R2009123 : Reach 2009123 := rs (se 1 (by rfl) ⟨1506842, by rfl⟩) R3013685
theorem R108631 : Reach 108631 := rs (se 1 (by rfl) ⟨81473, by rfl⟩) R162947
theorem R632933 : Reach 632933 := rs (se 4 (by rfl) ⟨59337, by rfl⟩) R118675
theorem R108715 : Reach 108715 := rs (se 1 (by rfl) ⟨81536, by rfl⟩) R163073
theorem R108823 : Reach 108823 := rs (se 1 (by rfl) ⟨81617, by rfl⟩) R163235
theorem R1648997 : Reach 1648997 := rs (se 4 (by rfl) ⟨154593, by rfl⟩) R309187
theorem R109003 : Reach 109003 := rs (se 1 (by rfl) ⟨81752, by rfl⟩) R163505
theorem R109111 : Reach 109111 := rs (se 1 (by rfl) ⟨81833, by rfl⟩) R163667
theorem R109291 : Reach 109291 := rs (se 1 (by rfl) ⟨81968, by rfl⟩) R163937
theorem R174835 : Reach 174835 := rs (se 1 (by rfl) ⟨131126, by rfl⟩) R262253
theorem R174899 : Reach 174899 := rs (se 1 (by rfl) ⟨131174, by rfl⟩) R262349
theorem R109399 : Reach 109399 := rs (se 1 (by rfl) ⟨82049, by rfl⟩) R164099
theorem R207731 : Reach 207731 := rs (se 1 (by rfl) ⟨155798, by rfl⟩) R311597
theorem R109579 : Reach 109579 := rs (se 1 (by rfl) ⟨82184, by rfl⟩) R164369
theorem R371729 : Reach 371729 := rs (se 2 (by rfl) ⟨139398, by rfl⟩) R278797
theorem R371735 : Reach 371735 := rs (se 1 (by rfl) ⟨278801, by rfl⟩) R557603
theorem R109687 : Reach 109687 := rs (se 1 (by rfl) ⟨82265, by rfl⟩) R164531
theorem R666755 : Reach 666755 := rs (se 1 (by rfl) ⟨500066, by rfl⟩) R1000133
theorem R240833 : Reach 240833 := rs (se 2 (by rfl) ⟨90312, by rfl⟩) R180625
theorem R175297 : Reach 175297 := rs (se 2 (by rfl) ⟨65736, by rfl⟩) R131473
theorem R109867 : Reach 109867 := rs (se 1 (by rfl) ⟨82400, by rfl⟩) R164801
theorem R109975 : Reach 109975 := rs (se 1 (by rfl) ⟨82481, by rfl⟩) R164963
theorem R142745 : Reach 142745 := rs (se 2 (by rfl) ⟨53529, by rfl⟩) R107059
theorem R306625 : Reach 306625 := rs (se 2 (by rfl) ⟨114984, by rfl⟩) R229969
theorem R372185 : Reach 372185 := rs (se 2 (by rfl) ⟨139569, by rfl⟩) R279139
theorem R142859 : Reach 142859 := rs (se 1 (by rfl) ⟨107144, by rfl⟩) R214289
theorem R142871 : Reach 142871 := rs (se 1 (by rfl) ⟨107153, by rfl⟩) R214307
theorem R110155 : Reach 110155 := rs (se 1 (by rfl) ⟨82616, by rfl⟩) R165233
theorem R142937 : Reach 142937 := rs (se 2 (by rfl) ⟨53601, by rfl⟩) R107203
theorem R274013 : Reach 274013 := rs (se 3 (by rfl) ⟨51377, by rfl⟩) R102755
theorem R372397 : Reach 372397 := rs (se 3 (by rfl) ⟨69824, by rfl⟩) R139649
theorem R110263 : Reach 110263 := rs (se 1 (by rfl) ⟨82697, by rfl⟩) R165395
theorem R143051 : Reach 143051 := rs (se 1 (by rfl) ⟨107288, by rfl⟩) R214577
theorem R143063 : Reach 143063 := rs (se 1 (by rfl) ⟨107297, by rfl⟩) R214595
theorem R143129 : Reach 143129 := rs (se 2 (by rfl) ⟨53673, by rfl⟩) R107347
theorem R274241 : Reach 274241 := rs (se 2 (by rfl) ⟨102840, by rfl⟩) R205681
theorem R110443 : Reach 110443 := rs (se 1 (by rfl) ⟨82832, by rfl⟩) R165665
theorem R143243 : Reach 143243 := rs (se 1 (by rfl) ⟨107432, by rfl⟩) R214865
theorem R143255 : Reach 143255 := rs (se 1 (by rfl) ⟨107441, by rfl⟩) R214883
theorem R569267 : Reach 569267 := rs (se 1 (by rfl) ⟨426950, by rfl⟩) R853901
theorem R110551 : Reach 110551 := rs (se 1 (by rfl) ⟨82913, by rfl⟩) R165827
theorem R143321 : Reach 143321 := rs (se 2 (by rfl) ⟨53745, by rfl⟩) R107491
theorem R372701 : Reach 372701 := rs (se 3 (by rfl) ⟨69881, by rfl⟩) R139763
theorem R208919 : Reach 208919 := rs (se 1 (by rfl) ⟨156689, by rfl⟩) R313379
theorem R143435 : Reach 143435 := rs (se 1 (by rfl) ⟨107576, by rfl⟩) R215153
theorem R143447 : Reach 143447 := rs (se 1 (by rfl) ⟨107585, by rfl⟩) R215171
theorem R110731 : Reach 110731 := rs (se 1 (by rfl) ⟨83048, by rfl⟩) R166097
theorem R274583 : Reach 274583 := rs (se 1 (by rfl) ⟨205937, by rfl⟩) R411875
theorem R143513 : Reach 143513 := rs (se 2 (by rfl) ⟨53817, by rfl⟩) R107635
theorem R340147 : Reach 340147 := rs (se 1 (by rfl) ⟨255110, by rfl⟩) R510221
theorem R110839 : Reach 110839 := rs (se 1 (by rfl) ⟨83129, by rfl⟩) R166259
theorem R143627 : Reach 143627 := rs (se 1 (by rfl) ⟨107720, by rfl⟩) R215441
theorem R143639 : Reach 143639 := rs (se 1 (by rfl) ⟨107729, by rfl⟩) R215459
theorem R143705 : Reach 143705 := rs (se 2 (by rfl) ⟨53889, by rfl⟩) R107779
theorem R373081 : Reach 373081 := rs (se 2 (by rfl) ⟨139905, by rfl⟩) R279811
theorem R176513 : Reach 176513 := rs (se 2 (by rfl) ⟨66192, by rfl⟩) R132385
theorem R111019 : Reach 111019 := rs (se 1 (by rfl) ⟨83264, by rfl⟩) R166529
theorem R242099 : Reach 242099 := rs (se 1 (by rfl) ⟨181574, by rfl⟩) R363149
theorem R143819 : Reach 143819 := rs (se 1 (by rfl) ⟨107864, by rfl⟩) R215729
theorem R143831 : Reach 143831 := rs (se 1 (by rfl) ⟨107873, by rfl⟩) R215747
theorem R5550605 : Reach 5550605 := rs (se 3 (by rfl) ⟨1040738, by rfl⟩) R2081477
theorem R111127 : Reach 111127 := rs (se 1 (by rfl) ⟨83345, by rfl⟩) R166691
theorem R143897 : Reach 143897 := rs (se 2 (by rfl) ⟨53961, by rfl⟩) R107923
theorem R209459 : Reach 209459 := rs (se 1 (by rfl) ⟨157094, by rfl⟩) R314189
theorem R144011 : Reach 144011 := rs (se 1 (by rfl) ⟨108008, by rfl⟩) R216017
theorem R144023 : Reach 144023 := rs (se 1 (by rfl) ⟨108017, by rfl⟩) R216035
theorem R111307 : Reach 111307 := rs (se 1 (by rfl) ⟨83480, by rfl⟩) R166961
theorem R144089 : Reach 144089 := rs (se 2 (by rfl) ⟨54033, by rfl⟩) R108067
theorem R111415 : Reach 111415 := rs (se 1 (by rfl) ⟨83561, by rfl⟩) R167123
theorem R144203 : Reach 144203 := rs (se 1 (by rfl) ⟨108152, by rfl⟩) R216305
theorem R144215 : Reach 144215 := rs (se 1 (by rfl) ⟨108161, by rfl⟩) R216323
theorem R144281 : Reach 144281 := rs (se 2 (by rfl) ⟨54105, by rfl⟩) R108211
theorem R242635 : Reach 242635 := rs (se 1 (by rfl) ⟨181976, by rfl⟩) R363953
theorem R144395 : Reach 144395 := rs (se 1 (by rfl) ⟨108296, by rfl⟩) R216593
theorem R144407 : Reach 144407 := rs (se 1 (by rfl) ⟨108305, by rfl⟩) R216611
theorem R209945 : Reach 209945 := rs (se 2 (by rfl) ⟨78729, by rfl⟩) R157459
theorem R2831435 : Reach 2831435 := rs (se 1 (by rfl) ⟨2123576, by rfl⟩) R4247153
theorem R242777 : Reach 242777 := rs (se 2 (by rfl) ⟨91041, by rfl⟩) R182083
theorem R144473 : Reach 144473 := rs (se 2 (by rfl) ⟨54177, by rfl⟩) R108355
theorem R111755 : Reach 111755 := rs (se 1 (by rfl) ⟨83816, by rfl⟩) R167633
theorem R144587 : Reach 144587 := rs (se 1 (by rfl) ⟨108440, by rfl⟩) R216881
theorem R144599 : Reach 144599 := rs (se 1 (by rfl) ⟨108449, by rfl⟩) R216899
theorem R144665 : Reach 144665 := rs (se 2 (by rfl) ⟨54249, by rfl⟩) R108499
theorem R1094957 : Reach 1094957 := rs (se 3 (by rfl) ⟨205304, by rfl⟩) R410609
theorem R308573 : Reach 308573 := rs (se 3 (by rfl) ⟨57857, by rfl⟩) R115715
theorem R144779 : Reach 144779 := rs (se 1 (by rfl) ⟨108584, by rfl⟩) R217169
theorem R144791 : Reach 144791 := rs (se 1 (by rfl) ⟨108593, by rfl⟩) R217187
theorem R144857 : Reach 144857 := rs (se 2 (by rfl) ⟨54321, by rfl⟩) R108643
theorem R308701 : Reach 308701 := rs (se 3 (by rfl) ⟨57881, by rfl⟩) R115763
theorem R1029667 : Reach 1029667 := rs (se 1 (by rfl) ⟨772250, by rfl⟩) R1544501
theorem R702017 : Reach 702017 := rs (se 2 (by rfl) ⟨263256, by rfl⟩) R526513
theorem R144971 : Reach 144971 := rs (se 1 (by rfl) ⟨108728, by rfl⟩) R217457
theorem R144983 : Reach 144983 := rs (se 1 (by rfl) ⟨108737, by rfl⟩) R217475
theorem R11417219 : Reach 11417219 := rs (se 1 (by rfl) ⟨8562914, by rfl⟩) R17125829
theorem R145049 : Reach 145049 := rs (se 2 (by rfl) ⟨54393, by rfl⟩) R108787
theorem R407261 : Reach 407261 := rs (se 3 (by rfl) ⟨76361, by rfl⟩) R152723
theorem R145163 : Reach 145163 := rs (se 1 (by rfl) ⟨108872, by rfl⟩) R217745
theorem R145175 : Reach 145175 := rs (se 1 (by rfl) ⟨108881, by rfl⟩) R217763
theorem R145241 : Reach 145241 := rs (se 2 (by rfl) ⟨54465, by rfl⟩) R108931
theorem R243607 : Reach 243607 := rs (se 1 (by rfl) ⟨182705, by rfl⟩) R365411
theorem R145355 : Reach 145355 := rs (se 1 (by rfl) ⟨109016, by rfl⟩) R218033
theorem R145367 : Reach 145367 := rs (se 1 (by rfl) ⟨109025, by rfl⟩) R218051
theorem R145433 : Reach 145433 := rs (se 2 (by rfl) ⟨54537, by rfl⟩) R109075
theorem R210995 : Reach 210995 := rs (se 1 (by rfl) ⟨158246, by rfl⟩) R316493
theorem R1882187 : Reach 1882187 := rs (se 1 (by rfl) ⟨1411640, by rfl⟩) R2823281
theorem R145547 : Reach 145547 := rs (se 1 (by rfl) ⟨109160, by rfl⟩) R218321
theorem R145559 : Reach 145559 := rs (se 1 (by rfl) ⟨109169, by rfl⟩) R218339
theorem R178355 : Reach 178355 := rs (se 1 (by rfl) ⟨133766, by rfl⟩) R267533
theorem R145625 : Reach 145625 := rs (se 2 (by rfl) ⟨54609, by rfl⟩) R109219
theorem R244043 : Reach 244043 := rs (se 1 (by rfl) ⟨183032, by rfl⟩) R366065
theorem R145739 : Reach 145739 := rs (se 1 (by rfl) ⟨109304, by rfl⟩) R218609
theorem R145751 : Reach 145751 := rs (se 1 (by rfl) ⟨109313, by rfl⟩) R218627
theorem R145817 : Reach 145817 := rs (se 2 (by rfl) ⟨54681, by rfl⟩) R109363
theorem R440749 : Reach 440749 := rs (se 3 (by rfl) ⟨82640, by rfl⟩) R165281
theorem R276929 : Reach 276929 := rs (se 2 (by rfl) ⟨103848, by rfl⟩) R207697
theorem R375299 : Reach 375299 := rs (se 1 (by rfl) ⟨281474, by rfl⟩) R562949
theorem R145931 : Reach 145931 := rs (se 1 (by rfl) ⟨109448, by rfl⟩) R218897
theorem R375313 : Reach 375313 := rs (se 2 (by rfl) ⟨140742, by rfl⟩) R281485
theorem R145943 : Reach 145943 := rs (se 1 (by rfl) ⟨109457, by rfl⟩) R218915
theorem R146009 : Reach 146009 := rs (se 2 (by rfl) ⟨54753, by rfl⟩) R109507
theorem R211585 : Reach 211585 := rs (se 2 (by rfl) ⟨79344, by rfl⟩) R158689
theorem R244417 : Reach 244417 := rs (se 2 (by rfl) ⟨91656, by rfl⟩) R183313
theorem R146123 : Reach 146123 := rs (se 1 (by rfl) ⟨109592, by rfl⟩) R219185
theorem R146135 : Reach 146135 := rs (se 1 (by rfl) ⟨109601, by rfl⟩) R219203
theorem R146201 : Reach 146201 := rs (se 2 (by rfl) ⟨54825, by rfl⟩) R109651
theorem R375617 : Reach 375617 := rs (se 2 (by rfl) ⟨140856, by rfl⟩) R281713
theorem R146315 : Reach 146315 := rs (se 1 (by rfl) ⟨109736, by rfl⟩) R219473
theorem R146327 : Reach 146327 := rs (se 1 (by rfl) ⟨109745, by rfl⟩) R219491
theorem R277465 : Reach 277465 := rs (se 2 (by rfl) ⟨104049, by rfl⟩) R208099
theorem R146393 : Reach 146393 := rs (se 2 (by rfl) ⟨54897, by rfl⟩) R109795
theorem R146507 : Reach 146507 := rs (se 1 (by rfl) ⟨109880, by rfl⟩) R219761
theorem R146519 : Reach 146519 := rs (se 1 (by rfl) ⟨109889, by rfl⟩) R219779
theorem R146585 : Reach 146585 := rs (se 2 (by rfl) ⟨54969, by rfl⟩) R109939
theorem R146699 : Reach 146699 := rs (se 1 (by rfl) ⟨110024, by rfl⟩) R220049
theorem R146711 : Reach 146711 := rs (se 1 (by rfl) ⟨110033, by rfl⟩) R220067
theorem R245015 : Reach 245015 := rs (se 1 (by rfl) ⟨183761, by rfl⟩) R367523
theorem R146777 : Reach 146777 := rs (se 2 (by rfl) ⟨55041, by rfl⟩) R110083
theorem R146891 : Reach 146891 := rs (se 1 (by rfl) ⟨110168, by rfl⟩) R220337
theorem R146903 : Reach 146903 := rs (se 1 (by rfl) ⟨110177, by rfl⟩) R220355
theorem R376285 : Reach 376285 := rs (se 3 (by rfl) ⟨70553, by rfl⟩) R141107
theorem R146969 : Reach 146969 := rs (se 2 (by rfl) ⟨55113, by rfl⟩) R110227
theorem R147083 : Reach 147083 := rs (se 1 (by rfl) ⟨110312, by rfl⟩) R220625
theorem R147095 : Reach 147095 := rs (se 1 (by rfl) ⟨110321, by rfl⟩) R220643
theorem R147161 : Reach 147161 := rs (se 2 (by rfl) ⟨55185, by rfl⟩) R110371
theorem R1392389 : Reach 1392389 := rs (se 4 (by rfl) ⟨130536, by rfl⟩) R261073
theorem R147275 : Reach 147275 := rs (se 1 (by rfl) ⟨110456, by rfl⟩) R220913
theorem R147287 : Reach 147287 := rs (se 1 (by rfl) ⟨110465, by rfl⟩) R220931
theorem R2768741 : Reach 2768741 := rs (se 4 (by rfl) ⟨259569, by rfl⟩) R519139
theorem R147353 : Reach 147353 := rs (se 2 (by rfl) ⟨55257, by rfl⟩) R110515
theorem R2473907 : Reach 2473907 := rs (se 1 (by rfl) ⟨1855430, by rfl⟩) R3710861
theorem R147467 : Reach 147467 := rs (se 1 (by rfl) ⟨110600, by rfl⟩) R221201
theorem R147479 : Reach 147479 := rs (se 1 (by rfl) ⟨110609, by rfl⟩) R221219
theorem R245825 : Reach 245825 := rs (se 2 (by rfl) ⟨92184, by rfl⟩) R184369
theorem R147545 : Reach 147545 := rs (se 2 (by rfl) ⟨55329, by rfl⟩) R110659
theorem R147659 : Reach 147659 := rs (se 1 (by rfl) ⟨110744, by rfl⟩) R221489
theorem R147671 : Reach 147671 := rs (se 1 (by rfl) ⟨110753, by rfl⟩) R221507
theorem R409859 : Reach 409859 := rs (se 1 (by rfl) ⟨307394, by rfl⟩) R614789
theorem R377111 : Reach 377111 := rs (se 1 (by rfl) ⟨282833, by rfl⟩) R565667
theorem R147737 : Reach 147737 := rs (se 2 (by rfl) ⟨55401, by rfl⟩) R110803
theorem R147851 : Reach 147851 := rs (se 1 (by rfl) ⟨110888, by rfl⟩) R221777
theorem R147863 : Reach 147863 := rs (se 1 (by rfl) ⟨110897, by rfl⟩) R221795
theorem R147929 : Reach 147929 := rs (se 2 (by rfl) ⟨55473, by rfl⟩) R110947
theorem R148043 : Reach 148043 := rs (se 1 (by rfl) ⟨111032, by rfl⟩) R222065
theorem R148055 : Reach 148055 := rs (se 1 (by rfl) ⟨111041, by rfl⟩) R222083
theorem R246361 : Reach 246361 := rs (se 2 (by rfl) ⟨92385, by rfl⟩) R184771
theorem R148121 : Reach 148121 := rs (se 2 (by rfl) ⟨55545, by rfl⟩) R111091
theorem R180929 : Reach 180929 := rs (se 2 (by rfl) ⟨67848, by rfl⟩) R135697
theorem R148235 : Reach 148235 := rs (se 1 (by rfl) ⟨111176, by rfl⟩) R222353
theorem R148247 : Reach 148247 := rs (se 1 (by rfl) ⟨111185, by rfl⟩) R222371
theorem R475969 : Reach 475969 := rs (se 2 (by rfl) ⟨178488, by rfl⟩) R356977
theorem R148313 : Reach 148313 := rs (se 2 (by rfl) ⟨55617, by rfl⟩) R111235
theorem R279389 : Reach 279389 := rs (se 3 (by rfl) ⟨52385, by rfl⟩) R104771
theorem R672605 : Reach 672605 := rs (se 3 (by rfl) ⟨126113, by rfl⟩) R252227
theorem R148427 : Reach 148427 := rs (se 1 (by rfl) ⟨111320, by rfl⟩) R222641
theorem R148439 : Reach 148439 := rs (se 1 (by rfl) ⟨111329, by rfl⟩) R222659
theorem R1197017 : Reach 1197017 := rs (se 2 (by rfl) ⟨448881, by rfl⟩) R897763
theorem R181271 : Reach 181271 := rs (se 1 (by rfl) ⟨135953, by rfl⟩) R271907
theorem R148505 : Reach 148505 := rs (se 2 (by rfl) ⟨55689, by rfl⟩) R111379
theorem R214091 : Reach 214091 := rs (se 1 (by rfl) ⟨160568, by rfl⟩) R321137
theorem R214145 : Reach 214145 := rs (se 2 (by rfl) ⟨80304, by rfl⟩) R160609
theorem R148619 : Reach 148619 := rs (se 1 (by rfl) ⟨111464, by rfl⟩) R222929
theorem R148631 : Reach 148631 := rs (se 1 (by rfl) ⟨111473, by rfl⟩) R222947
theorem R148697 : Reach 148697 := rs (se 2 (by rfl) ⟨55761, by rfl⟩) R111523
theorem R214361 : Reach 214361 := rs (se 2 (by rfl) ⟨80385, by rfl⟩) R160771
theorem R214451 : Reach 214451 := rs (se 1 (by rfl) ⟨160838, by rfl⟩) R321677
theorem R214487 : Reach 214487 := rs (se 1 (by rfl) ⟨160865, by rfl⟩) R321731
theorem R116311 : Reach 116311 := rs (se 1 (by rfl) ⟨87233, by rfl⟩) R174467
theorem R214667 : Reach 214667 := rs (se 1 (by rfl) ⟨161000, by rfl⟩) R322001
theorem R181939 : Reach 181939 := rs (se 1 (by rfl) ⟨136454, by rfl⟩) R272909
theorem R247475 : Reach 247475 := rs (se 1 (by rfl) ⟨185606, by rfl⟩) R371213
theorem R214721 : Reach 214721 := rs (se 2 (by rfl) ⟨80520, by rfl⟩) R161041
theorem R214937 : Reach 214937 := rs (se 2 (by rfl) ⟨80601, by rfl⟩) R161203
theorem R247769 : Reach 247769 := rs (se 2 (by rfl) ⟨92913, by rfl⟩) R185827
theorem R215027 : Reach 215027 := rs (se 1 (by rfl) ⟨161270, by rfl⟩) R322541
theorem R215063 : Reach 215063 := rs (se 1 (by rfl) ⟨161297, by rfl⟩) R322595
theorem R182387 : Reach 182387 := rs (se 1 (by rfl) ⟨136790, by rfl⟩) R273581
theorem R182425 : Reach 182425 := rs (se 2 (by rfl) ⟨68409, by rfl⟩) R136819
theorem R215243 : Reach 215243 := rs (se 1 (by rfl) ⟨161432, by rfl⟩) R322865
theorem R215297 : Reach 215297 := rs (se 2 (by rfl) ⟨80736, by rfl⟩) R161473
theorem R215513 : Reach 215513 := rs (se 2 (by rfl) ⟨80817, by rfl⟩) R161635
theorem R215603 : Reach 215603 := rs (se 1 (by rfl) ⟨161702, by rfl⟩) R323405
theorem R412235 : Reach 412235 := rs (se 1 (by rfl) ⟨309176, by rfl⟩) R618353
theorem R215639 : Reach 215639 := rs (se 1 (by rfl) ⟨161729, by rfl⟩) R323459
theorem R182873 : Reach 182873 := rs (se 2 (by rfl) ⟨68577, by rfl⟩) R137155
theorem R215819 : Reach 215819 := rs (se 1 (by rfl) ⟨161864, by rfl⟩) R323729
theorem R215873 : Reach 215873 := rs (se 2 (by rfl) ⟨80952, by rfl⟩) R161905
theorem R216089 : Reach 216089 := rs (se 2 (by rfl) ⟨81033, by rfl⟩) R162067
theorem R216179 : Reach 216179 := rs (se 1 (by rfl) ⟨162134, by rfl⟩) R324269
theorem R216215 : Reach 216215 := rs (se 1 (by rfl) ⟨162161, by rfl⟩) R324323
theorem R150679 : Reach 150679 := rs (se 1 (by rfl) ⟨113009, by rfl⟩) R226019
theorem R183617 : Reach 183617 := rs (se 2 (by rfl) ⟨68856, by rfl⟩) R137713
theorem R216395 : Reach 216395 := rs (se 1 (by rfl) ⟨162296, by rfl⟩) R324593
theorem R216449 : Reach 216449 := rs (se 2 (by rfl) ⟨81168, by rfl⟩) R162337
theorem R347665 : Reach 347665 := rs (se 2 (by rfl) ⟨130374, by rfl⟩) R260749
theorem R413207 : Reach 413207 := rs (se 1 (by rfl) ⟨309905, by rfl⟩) R619811
theorem R347723 : Reach 347723 := rs (se 1 (by rfl) ⟨260792, by rfl⟩) R521585
theorem R183883 : Reach 183883 := rs (se 1 (by rfl) ⟨137912, by rfl⟩) R275825
theorem R249419 : Reach 249419 := rs (se 1 (by rfl) ⟨187064, by rfl⟩) R374129
theorem R216665 : Reach 216665 := rs (se 2 (by rfl) ⟨81249, by rfl⟩) R162499
theorem R839261 : Reach 839261 := rs (se 3 (by rfl) ⟨157361, by rfl⟩) R314723
theorem R315031 : Reach 315031 := rs (se 1 (by rfl) ⟨236273, by rfl⟩) R472547
theorem R216755 : Reach 216755 := rs (se 1 (by rfl) ⟨162566, by rfl⟩) R325133
theorem R315083 : Reach 315083 := rs (se 1 (by rfl) ⟨236312, by rfl⟩) R472625
theorem R216791 : Reach 216791 := rs (se 1 (by rfl) ⟨162593, by rfl⟩) R325187
theorem R1265453 : Reach 1265453 := rs (se 3 (by rfl) ⟨237272, by rfl⟩) R474545
theorem R216971 : Reach 216971 := rs (se 1 (by rfl) ⟨162728, by rfl⟩) R325457
theorem R479155 : Reach 479155 := rs (se 1 (by rfl) ⟨359366, by rfl⟩) R718733
theorem R217025 : Reach 217025 := rs (se 2 (by rfl) ⟨81384, by rfl⟩) R162769
theorem R184331 : Reach 184331 := rs (se 1 (by rfl) ⟨138248, by rfl⟩) R276497
theorem R610379 : Reach 610379 := rs (se 1 (by rfl) ⟨457784, by rfl⟩) R915569
theorem R872579 : Reach 872579 := rs (se 1 (by rfl) ⟨654434, by rfl⟩) R1308869
theorem R217241 : Reach 217241 := rs (se 2 (by rfl) ⟨81465, by rfl⟩) R162931
theorem R184513 : Reach 184513 := rs (se 2 (by rfl) ⟨69192, by rfl⟩) R138385
theorem R217331 : Reach 217331 := rs (se 1 (by rfl) ⟨162998, by rfl⟩) R325997
theorem R217367 : Reach 217367 := rs (se 1 (by rfl) ⟨163025, by rfl⟩) R326051
theorem R217547 : Reach 217547 := rs (se 1 (by rfl) ⟨163160, by rfl⟩) R326321
theorem R217601 : Reach 217601 := rs (se 2 (by rfl) ⟨81600, by rfl⟩) R163201
theorem R184855 : Reach 184855 := rs (se 1 (by rfl) ⟨138641, by rfl⟩) R277283
theorem R250391 : Reach 250391 := rs (se 1 (by rfl) ⟨187793, by rfl⟩) R375587
theorem R217817 : Reach 217817 := rs (se 2 (by rfl) ⟨81681, by rfl⟩) R163363
theorem R185075 : Reach 185075 := rs (se 1 (by rfl) ⟨138806, by rfl⟩) R277613
theorem R774917 : Reach 774917 := rs (se 4 (by rfl) ⟨72648, by rfl⟩) R145297
theorem R217907 : Reach 217907 := rs (se 1 (by rfl) ⟨163430, by rfl⟩) R326861
theorem R217943 : Reach 217943 := rs (se 1 (by rfl) ⟨163457, by rfl⟩) R326915
theorem R185303 : Reach 185303 := rs (se 1 (by rfl) ⟨138977, by rfl⟩) R277955
theorem R218123 : Reach 218123 := rs (se 1 (by rfl) ⟨163592, by rfl⟩) R327185
theorem R218177 : Reach 218177 := rs (se 2 (by rfl) ⟨81816, by rfl⟩) R163633
theorem R545885 : Reach 545885 := rs (se 3 (by rfl) ⟨102353, by rfl⟩) R204707
theorem R185561 : Reach 185561 := rs (se 2 (by rfl) ⟨69585, by rfl⟩) R139171
theorem R218393 : Reach 218393 := rs (se 2 (by rfl) ⟨81897, by rfl⟩) R163795
theorem R316723 : Reach 316723 := rs (se 1 (by rfl) ⟨237542, by rfl⟩) R475085
theorem R218483 : Reach 218483 := rs (se 1 (by rfl) ⟨163862, by rfl⟩) R327725
theorem R218519 : Reach 218519 := rs (se 1 (by rfl) ⟨163889, by rfl⟩) R327779
theorem R316865 : Reach 316865 := rs (se 2 (by rfl) ⟨118824, by rfl⟩) R237649
theorem R218699 : Reach 218699 := rs (se 1 (by rfl) ⟨164024, by rfl⟩) R328049
theorem R185971 : Reach 185971 := rs (se 1 (by rfl) ⟨139478, by rfl⟩) R278957
theorem R218753 : Reach 218753 := rs (se 2 (by rfl) ⟨82032, by rfl⟩) R164065
theorem R218803 : Reach 218803 := rs (se 1 (by rfl) ⟨164102, by rfl⟩) R328205
theorem R120523 : Reach 120523 := rs (se 1 (by rfl) ⟨90392, by rfl⟩) R180785
theorem R349913 : Reach 349913 := rs (se 2 (by rfl) ⟨131217, by rfl⟩) R262435
theorem R218969 : Reach 218969 := rs (se 2 (by rfl) ⟨82113, by rfl⟩) R164227
theorem R219059 : Reach 219059 := rs (se 1 (by rfl) ⟨164294, by rfl⟩) R328589
theorem R415667 : Reach 415667 := rs (se 1 (by rfl) ⟨311750, by rfl⟩) R623501
theorem R120791 : Reach 120791 := rs (se 1 (by rfl) ⟨90593, by rfl⟩) R181187
theorem R219095 : Reach 219095 := rs (se 1 (by rfl) ⟨164321, by rfl⟩) R328643
theorem R186457 : Reach 186457 := rs (se 2 (by rfl) ⟨69921, by rfl⟩) R139843
theorem R841859 : Reach 841859 := rs (se 1 (by rfl) ⟨631394, by rfl⟩) R1262789
theorem R219275 : Reach 219275 := rs (se 1 (by rfl) ⟨164456, by rfl⟩) R328913
theorem R219329 : Reach 219329 := rs (se 2 (by rfl) ⟨82248, by rfl⟩) R164497
theorem R710957 : Reach 710957 := rs (se 3 (by rfl) ⟨133304, by rfl⟩) R266609
theorem R219545 : Reach 219545 := rs (se 2 (by rfl) ⟨82329, by rfl⟩) R164659
theorem R219635 : Reach 219635 := rs (se 1 (by rfl) ⟨164726, by rfl⟩) R329453
theorem R219671 : Reach 219671 := rs (se 1 (by rfl) ⟨164753, by rfl⟩) R329507
theorem R187019 : Reach 187019 := rs (se 1 (by rfl) ⟨140264, by rfl⟩) R280529
theorem R121495 : Reach 121495 := rs (se 1 (by rfl) ⟨91121, by rfl⟩) R182243
theorem R219851 : Reach 219851 := rs (se 1 (by rfl) ⟨164888, by rfl⟩) R329777
theorem R1596145 : Reach 1596145 := rs (se 2 (by rfl) ⟨598554, by rfl⟩) R1197109
theorem R219905 : Reach 219905 := rs (se 2 (by rfl) ⟨82464, by rfl⟩) R164929
theorem R187201 : Reach 187201 := rs (se 2 (by rfl) ⟨70200, by rfl⟩) R140401
theorem R351065 : Reach 351065 := rs (se 2 (by rfl) ⟨131649, by rfl⟩) R263299
theorem R220121 : Reach 220121 := rs (se 2 (by rfl) ⟨82545, by rfl⟩) R165091
theorem R318487 : Reach 318487 := rs (se 1 (by rfl) ⟨238865, by rfl⟩) R477731
theorem R220211 : Reach 220211 := rs (se 1 (by rfl) ⟨165158, by rfl⟩) R330317
theorem R220247 : Reach 220247 := rs (se 1 (by rfl) ⟨165185, by rfl⟩) R330371
theorem R482435 : Reach 482435 := rs (se 1 (by rfl) ⟨361826, by rfl⟩) R723653
theorem R187571 : Reach 187571 := rs (se 1 (by rfl) ⟨140678, by rfl⟩) R281357
theorem R220427 : Reach 220427 := rs (se 1 (by rfl) ⟨165320, by rfl⟩) R330641
theorem R220481 : Reach 220481 := rs (se 2 (by rfl) ⟨82680, by rfl⟩) R165361
theorem R613763 : Reach 613763 := rs (se 1 (by rfl) ⟨460322, by rfl⟩) R920645
theorem R187787 : Reach 187787 := rs (se 1 (by rfl) ⟨140840, by rfl⟩) R281681
theorem R187915 : Reach 187915 := rs (se 1 (by rfl) ⟨140936, by rfl⟩) R281873
theorem R548369 : Reach 548369 := rs (se 2 (by rfl) ⟨205638, by rfl⟩) R411277
theorem R220697 : Reach 220697 := rs (se 2 (by rfl) ⟨82761, by rfl⟩) R165523
theorem R187991 : Reach 187991 := rs (se 1 (by rfl) ⟨140993, by rfl⟩) R281987
theorem R220787 : Reach 220787 := rs (se 1 (by rfl) ⟨165590, by rfl⟩) R331181
theorem R220823 : Reach 220823 := rs (se 1 (by rfl) ⟨165617, by rfl⟩) R331235
theorem R417581 : Reach 417581 := rs (se 3 (by rfl) ⟨78296, by rfl⟩) R156593
theorem R221003 : Reach 221003 := rs (se 1 (by rfl) ⟨165752, by rfl⟩) R331505
theorem R221057 : Reach 221057 := rs (se 2 (by rfl) ⟨82896, by rfl⟩) R165793
theorem R221195 : Reach 221195 := rs (se 1 (by rfl) ⟨165896, by rfl⟩) R331793
theorem R221273 : Reach 221273 := rs (se 2 (by rfl) ⟨82977, by rfl⟩) R165955
theorem R417923 : Reach 417923 := rs (se 1 (by rfl) ⟨313442, by rfl⟩) R626885
theorem R221363 : Reach 221363 := rs (se 1 (by rfl) ⟨166022, by rfl⟩) R332045
theorem R221399 : Reach 221399 := rs (se 1 (by rfl) ⟨166049, by rfl⟩) R332099
theorem R254173 : Reach 254173 := rs (se 3 (by rfl) ⟨47657, by rfl⟩) R95315
theorem R155927 : Reach 155927 := rs (se 1 (by rfl) ⟨116945, by rfl⟩) R233891
theorem R123211 : Reach 123211 := rs (se 1 (by rfl) ⟨92408, by rfl⟩) R184817
theorem R680293 : Reach 680293 := rs (se 4 (by rfl) ⟨63777, by rfl⟩) R127555
theorem R221579 : Reach 221579 := rs (se 1 (by rfl) ⟨166184, by rfl⟩) R332369
theorem R221633 : Reach 221633 := rs (se 2 (by rfl) ⟨83112, by rfl⟩) R166225
theorem R221849 : Reach 221849 := rs (se 2 (by rfl) ⟨83193, by rfl⟩) R166387
theorem R221939 : Reach 221939 := rs (se 1 (by rfl) ⟨166454, by rfl⟩) R332909
theorem R156439 : Reach 156439 := rs (se 1 (by rfl) ⟨117329, by rfl⟩) R234659
theorem R221975 : Reach 221975 := rs (se 1 (by rfl) ⟨166481, by rfl⟩) R332963
theorem R222155 : Reach 222155 := rs (se 1 (by rfl) ⟨166616, by rfl⟩) R333233
theorem R222209 : Reach 222209 := rs (se 2 (by rfl) ⟨83328, by rfl⟩) R166657
theorem R156811 : Reach 156811 := rs (se 1 (by rfl) ⟨117608, by rfl⟩) R235217
theorem R746647 : Reach 746647 := rs (se 1 (by rfl) ⟨559985, by rfl⟩) R1119971
theorem R222425 : Reach 222425 := rs (se 2 (by rfl) ⟨83409, by rfl⟩) R166819
theorem R124183 : Reach 124183 := rs (se 1 (by rfl) ⟨93137, by rfl⟩) R186275
theorem R222515 : Reach 222515 := rs (se 1 (by rfl) ⟨166886, by rfl⟩) R333773
theorem R222551 : Reach 222551 := rs (se 1 (by rfl) ⟨166913, by rfl⟩) R333827
theorem R3630563 : Reach 3630563 := rs (se 1 (by rfl) ⟨2722922, by rfl⟩) R5445845
theorem R222731 : Reach 222731 := rs (se 1 (by rfl) ⟨167048, by rfl⟩) R334097
theorem R222785 : Reach 222785 := rs (se 2 (by rfl) ⟨83544, by rfl⟩) R167089
theorem R157259 : Reach 157259 := rs (se 1 (by rfl) ⟨117944, by rfl⟩) R235889
theorem R321245 : Reach 321245 := rs (se 3 (by rfl) ⟨60233, by rfl⟩) R120467
theorem R223001 : Reach 223001 := rs (se 2 (by rfl) ⟨83625, by rfl⟩) R167251
theorem R813017 : Reach 813017 := rs (se 2 (by rfl) ⟨304881, by rfl⟩) R609763
theorem R125003 : Reach 125003 := rs (se 1 (by rfl) ⟨93752, by rfl⟩) R187505
theorem R354397 : Reach 354397 := rs (se 3 (by rfl) ⟨66449, by rfl⟩) R132899
theorem R583859 : Reach 583859 := rs (se 1 (by rfl) ⟨437894, by rfl⟩) R875789
theorem R158041 : Reach 158041 := rs (se 2 (by rfl) ⟨59265, by rfl⟩) R118531
theorem R551261 : Reach 551261 := rs (se 3 (by rfl) ⟨103361, by rfl⟩) R206723
theorem R747953 : Reach 747953 := rs (se 2 (by rfl) ⟨280482, by rfl⟩) R560965
theorem R420299 : Reach 420299 := rs (se 1 (by rfl) ⟨315224, by rfl⟩) R630449
theorem R387587 : Reach 387587 := rs (se 1 (by rfl) ⟨290690, by rfl⟩) R581381
theorem R387629 : Reach 387629 := rs (se 3 (by rfl) ⟨72680, by rfl⟩) R145361
theorem R486161 : Reach 486161 := rs (se 2 (by rfl) ⟨182310, by rfl⟩) R364621
theorem R322379 : Reach 322379 := rs (se 1 (by rfl) ⟨241784, by rfl⟩) R483569
theorem R748439 : Reach 748439 := rs (se 1 (by rfl) ⟨561329, by rfl⟩) R1122659
theorem R486323 : Reach 486323 := rs (se 1 (by rfl) ⟨364742, by rfl⟩) R729485
theorem R322649 : Reach 322649 := rs (se 2 (by rfl) ⟨120993, by rfl⟩) R241987
theorem R421271 : Reach 421271 := rs (se 1 (by rfl) ⟨315953, by rfl⟩) R631907
theorem R1404377 : Reach 1404377 := rs (se 2 (by rfl) ⟨526641, by rfl⟩) R1053283
theorem R814657 : Reach 814657 := rs (se 2 (by rfl) ⟨305496, by rfl⟩) R610993
theorem R192065 : Reach 192065 := rs (se 2 (by rfl) ⟨72024, by rfl⟩) R144049
theorem R323351 : Reach 323351 := rs (se 1 (by rfl) ⟨242513, by rfl⟩) R485027
theorem R258241 : Reach 258241 := rs (se 2 (by rfl) ⟨96840, by rfl⟩) R193681
theorem R323891 : Reach 323891 := rs (se 1 (by rfl) ⟨242918, by rfl⟩) R485837
theorem R291251 : Reach 291251 := rs (se 1 (by rfl) ⟨218438, by rfl⟩) R436877
theorem R324161 : Reach 324161 := rs (se 2 (by rfl) ⟨121560, by rfl⟩) R243121
theorem R225857 : Reach 225857 := rs (se 2 (by rfl) ⟨84696, by rfl⟩) R169393
theorem R1798807 : Reach 1798807 := rs (se 1 (by rfl) ⟨1349105, by rfl⟩) R2698211
theorem R160535 : Reach 160535 := rs (se 1 (by rfl) ⟨120401, by rfl⟩) R240803
theorem R488267 : Reach 488267 := rs (se 1 (by rfl) ⟨366200, by rfl⟩) R732401
theorem R160663 : Reach 160663 := rs (se 1 (by rfl) ⟨120497, by rfl⟩) R240995
theorem R95147 : Reach 95147 := rs (se 1 (by rfl) ⟨71360, by rfl⟩) R142721
theorem R95159 : Reach 95159 := rs (se 1 (by rfl) ⟨71369, by rfl⟩) R142739
theorem R95179 : Reach 95179 := rs (se 1 (by rfl) ⟨71384, by rfl⟩) R142769
theorem R95191 : Reach 95191 := rs (se 1 (by rfl) ⟨71393, by rfl⟩) R142787
theorem R95211 : Reach 95211 := rs (se 1 (by rfl) ⟨71408, by rfl⟩) R142817
theorem R95223 : Reach 95223 := rs (se 1 (by rfl) ⟨71417, by rfl⟩) R142835
theorem R95243 : Reach 95243 := rs (se 1 (by rfl) ⟨71432, by rfl⟩) R142865
theorem R95255 : Reach 95255 := rs (se 1 (by rfl) ⟨71441, by rfl⟩) R142883
theorem R95275 : Reach 95275 := rs (se 1 (by rfl) ⟨71456, by rfl⟩) R142913
theorem R95287 : Reach 95287 := rs (se 1 (by rfl) ⟨71465, by rfl⟩) R142931
theorem R95307 : Reach 95307 := rs (se 1 (by rfl) ⟨71480, by rfl⟩) R142961
theorem R259147 : Reach 259147 := rs (se 1 (by rfl) ⟨194360, by rfl⟩) R388721
theorem R95319 : Reach 95319 := rs (se 1 (by rfl) ⟨71489, by rfl⟩) R142979
theorem R324701 : Reach 324701 := rs (se 3 (by rfl) ⟨60881, by rfl⟩) R121763
theorem R95339 : Reach 95339 := rs (se 1 (by rfl) ⟨71504, by rfl⟩) R143009
theorem R95351 : Reach 95351 := rs (se 1 (by rfl) ⟨71513, by rfl⟩) R143027
theorem R95371 : Reach 95371 := rs (se 1 (by rfl) ⟨71528, by rfl⟩) R143057
theorem R95383 : Reach 95383 := rs (se 1 (by rfl) ⟨71537, by rfl⟩) R143075
theorem R95403 : Reach 95403 := rs (se 1 (by rfl) ⟨71552, by rfl⟩) R143105
theorem R95415 : Reach 95415 := rs (se 1 (by rfl) ⟨71561, by rfl⟩) R143123
theorem R95435 : Reach 95435 := rs (se 1 (by rfl) ⟨71576, by rfl⟩) R143153
theorem R95447 : Reach 95447 := rs (se 1 (by rfl) ⟨71585, by rfl⟩) R143171
theorem R554201 : Reach 554201 := rs (se 2 (by rfl) ⟨207825, by rfl⟩) R415651
theorem R95467 : Reach 95467 := rs (se 1 (by rfl) ⟨71600, by rfl⟩) R143201
theorem R95479 : Reach 95479 := rs (se 1 (by rfl) ⟨71609, by rfl⟩) R143219
theorem R95499 : Reach 95499 := rs (se 1 (by rfl) ⟨71624, by rfl⟩) R143249
theorem R95511 : Reach 95511 := rs (se 1 (by rfl) ⟨71633, by rfl⟩) R143267
theorem R95531 : Reach 95531 := rs (se 1 (by rfl) ⟨71648, by rfl⟩) R143297
theorem R95543 : Reach 95543 := rs (se 1 (by rfl) ⟨71657, by rfl⟩) R143315
theorem R95563 : Reach 95563 := rs (se 1 (by rfl) ⟨71672, by rfl⟩) R143345
theorem R95575 : Reach 95575 := rs (se 1 (by rfl) ⟨71681, by rfl⟩) R143363
theorem R95595 : Reach 95595 := rs (se 1 (by rfl) ⟨71696, by rfl⟩) R143393
theorem R95607 : Reach 95607 := rs (se 1 (by rfl) ⟨71705, by rfl⟩) R143411
theorem R95627 : Reach 95627 := rs (se 1 (by rfl) ⟨71720, by rfl⟩) R143441
theorem R95639 : Reach 95639 := rs (se 1 (by rfl) ⟨71729, by rfl⟩) R143459
theorem R95659 : Reach 95659 := rs (se 1 (by rfl) ⟨71744, by rfl⟩) R143489
theorem R95671 : Reach 95671 := rs (se 1 (by rfl) ⟨71753, by rfl⟩) R143507
theorem R95691 : Reach 95691 := rs (se 1 (by rfl) ⟨71768, by rfl⟩) R143537
theorem R95703 : Reach 95703 := rs (se 1 (by rfl) ⟨71777, by rfl⟩) R143555
theorem R1570265 : Reach 1570265 := rs (se 2 (by rfl) ⟨588849, by rfl⟩) R1177699
theorem R95723 : Reach 95723 := rs (se 1 (by rfl) ⟨71792, by rfl⟩) R143585
theorem R95735 : Reach 95735 := rs (se 1 (by rfl) ⟨71801, by rfl⟩) R143603
theorem R161291 : Reach 161291 := rs (se 1 (by rfl) ⟨120968, by rfl⟩) R241937
theorem R95755 : Reach 95755 := rs (se 1 (by rfl) ⟨71816, by rfl⟩) R143633
theorem R95767 : Reach 95767 := rs (se 1 (by rfl) ⟨71825, by rfl⟩) R143651
theorem R1635875 : Reach 1635875 := rs (se 1 (by rfl) ⟨1226906, by rfl⟩) R2453813
theorem R95787 : Reach 95787 := rs (se 1 (by rfl) ⟨71840, by rfl⟩) R143681
theorem R95799 : Reach 95799 := rs (se 1 (by rfl) ⟨71849, by rfl⟩) R143699
theorem R95819 : Reach 95819 := rs (se 1 (by rfl) ⟨71864, by rfl⟩) R143729
theorem R95831 : Reach 95831 := rs (se 1 (by rfl) ⟨71873, by rfl⟩) R143747
theorem R95851 : Reach 95851 := rs (se 1 (by rfl) ⟨71888, by rfl⟩) R143777
theorem R95863 : Reach 95863 := rs (se 1 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R161419 : Reach 161419 := rs (se 1 (by rfl) ⟨121064, by rfl⟩) R242129
theorem R95883 : Reach 95883 := rs (se 1 (by rfl) ⟨71912, by rfl⟩) R143825
theorem R95895 : Reach 95895 := rs (se 1 (by rfl) ⟨71921, by rfl⟩) R143843
theorem R95915 : Reach 95915 := rs (se 1 (by rfl) ⟨71936, by rfl⟩) R143873
theorem R95927 : Reach 95927 := rs (se 1 (by rfl) ⟨71945, by rfl⟩) R143891
theorem R95947 : Reach 95947 := rs (se 1 (by rfl) ⟨71960, by rfl⟩) R143921
theorem R95959 : Reach 95959 := rs (se 1 (by rfl) ⟨71969, by rfl⟩) R143939
theorem R95979 : Reach 95979 := rs (se 1 (by rfl) ⟨71984, by rfl⟩) R143969
theorem R95991 : Reach 95991 := rs (se 1 (by rfl) ⟨71993, by rfl⟩) R143987
theorem R96011 : Reach 96011 := rs (se 1 (by rfl) ⟨72008, by rfl⟩) R144017
theorem R96023 : Reach 96023 := rs (se 1 (by rfl) ⟨72017, by rfl⟩) R144035
theorem R161561 : Reach 161561 := rs (se 2 (by rfl) ⟨60585, by rfl⟩) R121171
theorem R96043 : Reach 96043 := rs (se 1 (by rfl) ⟨72032, by rfl⟩) R144065
theorem R96055 : Reach 96055 := rs (se 1 (by rfl) ⟨72041, by rfl⟩) R144083
theorem R96075 : Reach 96075 := rs (se 1 (by rfl) ⟨72056, by rfl⟩) R144113
theorem R96087 : Reach 96087 := rs (se 1 (by rfl) ⟨72065, by rfl⟩) R144131
theorem R96107 : Reach 96107 := rs (se 1 (by rfl) ⟨72080, by rfl⟩) R144161
theorem R96119 : Reach 96119 := rs (se 1 (by rfl) ⟨72089, by rfl⟩) R144179
theorem R96139 : Reach 96139 := rs (se 1 (by rfl) ⟨72104, by rfl⟩) R144209
theorem R96151 : Reach 96151 := rs (se 1 (by rfl) ⟨72113, by rfl⟩) R144227
theorem R161689 : Reach 161689 := rs (se 2 (by rfl) ⟨60633, by rfl⟩) R121267
theorem R96171 : Reach 96171 := rs (se 1 (by rfl) ⟨72128, by rfl⟩) R144257
theorem R96183 : Reach 96183 := rs (se 1 (by rfl) ⟨72137, by rfl⟩) R144275
theorem R96203 : Reach 96203 := rs (se 1 (by rfl) ⟨72152, by rfl⟩) R144305
theorem R96215 : Reach 96215 := rs (se 1 (by rfl) ⟨72161, by rfl⟩) R144323
theorem R96235 : Reach 96235 := rs (se 1 (by rfl) ⟨72176, by rfl⟩) R144353
theorem R96247 : Reach 96247 := rs (se 1 (by rfl) ⟨72185, by rfl⟩) R144371
theorem R96267 : Reach 96267 := rs (se 1 (by rfl) ⟨72200, by rfl⟩) R144401
theorem R96279 : Reach 96279 := rs (se 1 (by rfl) ⟨72209, by rfl⟩) R144419
theorem R96299 : Reach 96299 := rs (se 1 (by rfl) ⟨72224, by rfl⟩) R144449
theorem R96311 : Reach 96311 := rs (se 1 (by rfl) ⟨72233, by rfl⟩) R144467
theorem R96331 : Reach 96331 := rs (se 1 (by rfl) ⟨72248, by rfl⟩) R144497
theorem R96343 : Reach 96343 := rs (se 1 (by rfl) ⟨72257, by rfl⟩) R144515
theorem R96363 : Reach 96363 := rs (se 1 (by rfl) ⟨72272, by rfl⟩) R144545
theorem R96375 : Reach 96375 := rs (se 1 (by rfl) ⟨72281, by rfl⟩) R144563
theorem R96395 : Reach 96395 := rs (se 1 (by rfl) ⟨72296, by rfl⟩) R144593
theorem R96407 : Reach 96407 := rs (se 1 (by rfl) ⟨72305, by rfl⟩) R144611
theorem R96427 : Reach 96427 := rs (se 1 (by rfl) ⟨72320, by rfl⟩) R144641
theorem R96439 : Reach 96439 := rs (se 1 (by rfl) ⟨72329, by rfl⟩) R144659
theorem R96459 : Reach 96459 := rs (se 1 (by rfl) ⟨72344, by rfl⟩) R144689
theorem R325835 : Reach 325835 := rs (se 1 (by rfl) ⟨244376, by rfl⟩) R488753
theorem R96471 : Reach 96471 := rs (se 1 (by rfl) ⟨72353, by rfl⟩) R144707
theorem R96491 : Reach 96491 := rs (se 1 (by rfl) ⟨72368, by rfl⟩) R144737
theorem R96503 : Reach 96503 := rs (se 1 (by rfl) ⟨72377, by rfl⟩) R144755
theorem R96523 : Reach 96523 := rs (se 1 (by rfl) ⟨72392, by rfl⟩) R144785
theorem R96535 : Reach 96535 := rs (se 1 (by rfl) ⟨72401, by rfl⟩) R144803
theorem R96555 : Reach 96555 := rs (se 1 (by rfl) ⟨72416, by rfl⟩) R144833
theorem R96567 : Reach 96567 := rs (se 1 (by rfl) ⟨72425, by rfl⟩) R144851
theorem R96587 : Reach 96587 := rs (se 1 (by rfl) ⟨72440, by rfl⟩) R144881
theorem R96599 : Reach 96599 := rs (se 1 (by rfl) ⟨72449, by rfl⟩) R144899
theorem R96619 : Reach 96619 := rs (se 1 (by rfl) ⟨72464, by rfl⟩) R144929
theorem R96631 : Reach 96631 := rs (se 1 (by rfl) ⟨72473, by rfl⟩) R144947
theorem R96651 : Reach 96651 := rs (se 1 (by rfl) ⟨72488, by rfl⟩) R144977
theorem R96663 : Reach 96663 := rs (se 1 (by rfl) ⟨72497, by rfl⟩) R144995
theorem R96683 : Reach 96683 := rs (se 1 (by rfl) ⟨72512, by rfl⟩) R145025
theorem R96695 : Reach 96695 := rs (se 1 (by rfl) ⟨72521, by rfl⟩) R145043
theorem R96715 : Reach 96715 := rs (se 1 (by rfl) ⟨72536, by rfl⟩) R145073
theorem R162263 : Reach 162263 := rs (se 1 (by rfl) ⟨121697, by rfl⟩) R243395
theorem R96727 : Reach 96727 := rs (se 1 (by rfl) ⟨72545, by rfl⟩) R145091
theorem R326105 : Reach 326105 := rs (se 2 (by rfl) ⟨122289, by rfl⟩) R244579
theorem R621017 : Reach 621017 := rs (se 2 (by rfl) ⟨232881, by rfl⟩) R465763
theorem R96747 : Reach 96747 := rs (se 1 (by rfl) ⟨72560, by rfl⟩) R145121
theorem R96759 : Reach 96759 := rs (se 1 (by rfl) ⟨72569, by rfl⟩) R145139
theorem R96779 : Reach 96779 := rs (se 1 (by rfl) ⟨72584, by rfl⟩) R145169
theorem R96791 : Reach 96791 := rs (se 1 (by rfl) ⟨72593, by rfl⟩) R145187
theorem R96811 : Reach 96811 := rs (se 1 (by rfl) ⟨72608, by rfl⟩) R145217
theorem R96823 : Reach 96823 := rs (se 1 (by rfl) ⟨72617, by rfl⟩) R145235
theorem R490049 : Reach 490049 := rs (se 2 (by rfl) ⟨183768, by rfl⟩) R367537
theorem R96843 : Reach 96843 := rs (se 1 (by rfl) ⟨72632, by rfl⟩) R145265
theorem R162391 : Reach 162391 := rs (se 1 (by rfl) ⟨121793, by rfl⟩) R243587
theorem R96855 : Reach 96855 := rs (se 1 (by rfl) ⟨72641, by rfl⟩) R145283
theorem R96875 : Reach 96875 := rs (se 1 (by rfl) ⟨72656, by rfl⟩) R145313
theorem R96887 : Reach 96887 := rs (se 1 (by rfl) ⟨72665, by rfl⟩) R145331
theorem R96907 : Reach 96907 := rs (se 1 (by rfl) ⟨72680, by rfl⟩) R145361
theorem R96919 : Reach 96919 := rs (se 1 (by rfl) ⟨72689, by rfl⟩) R145379
theorem R96939 : Reach 96939 := rs (se 1 (by rfl) ⟨72704, by rfl⟩) R145409
theorem R96951 : Reach 96951 := rs (se 1 (by rfl) ⟨72713, by rfl⟩) R145427
theorem R96971 : Reach 96971 := rs (se 1 (by rfl) ⟨72728, by rfl⟩) R145457
theorem R96983 : Reach 96983 := rs (se 1 (by rfl) ⟨72737, by rfl⟩) R145475
theorem R97003 : Reach 97003 := rs (se 1 (by rfl) ⟨72752, by rfl⟩) R145505
theorem R97015 : Reach 97015 := rs (se 1 (by rfl) ⟨72761, by rfl⟩) R145523
theorem R97035 : Reach 97035 := rs (se 1 (by rfl) ⟨72776, by rfl⟩) R145553
theorem R97047 : Reach 97047 := rs (se 1 (by rfl) ⟨72785, by rfl⟩) R145571
theorem R97067 : Reach 97067 := rs (se 1 (by rfl) ⟨72800, by rfl⟩) R145601
theorem R97079 : Reach 97079 := rs (se 1 (by rfl) ⟨72809, by rfl⟩) R145619
theorem R97099 : Reach 97099 := rs (se 1 (by rfl) ⟨72824, by rfl⟩) R145649
theorem R97111 : Reach 97111 := rs (se 1 (by rfl) ⟨72833, by rfl⟩) R145667
theorem R97131 : Reach 97131 := rs (se 1 (by rfl) ⟨72848, by rfl⟩) R145697
theorem R97143 : Reach 97143 := rs (se 1 (by rfl) ⟨72857, by rfl⟩) R145715
theorem R97163 : Reach 97163 := rs (se 1 (by rfl) ⟨72872, by rfl⟩) R145745
theorem R97175 : Reach 97175 := rs (se 1 (by rfl) ⟨72881, by rfl⟩) R145763
theorem R97195 : Reach 97195 := rs (se 1 (by rfl) ⟨72896, by rfl⟩) R145793
theorem R97207 : Reach 97207 := rs (se 1 (by rfl) ⟨72905, by rfl⟩) R145811
theorem R97227 : Reach 97227 := rs (se 1 (by rfl) ⟨72920, by rfl⟩) R145841
theorem R97239 : Reach 97239 := rs (se 1 (by rfl) ⟨72929, by rfl⟩) R145859
theorem R97259 : Reach 97259 := rs (se 1 (by rfl) ⟨72944, by rfl⟩) R145889
theorem R97271 : Reach 97271 := rs (se 1 (by rfl) ⟨72953, by rfl⟩) R145907
theorem R97291 : Reach 97291 := rs (se 1 (by rfl) ⟨72968, by rfl⟩) R145937
theorem R97303 : Reach 97303 := rs (se 1 (by rfl) ⟨72977, by rfl⟩) R145955
theorem R97323 : Reach 97323 := rs (se 1 (by rfl) ⟨72992, by rfl⟩) R145985
theorem R97335 : Reach 97335 := rs (se 1 (by rfl) ⟨73001, by rfl⟩) R146003
theorem R97355 : Reach 97355 := rs (se 1 (by rfl) ⟨73016, by rfl⟩) R146033
theorem R97367 : Reach 97367 := rs (se 1 (by rfl) ⟨73025, by rfl⟩) R146051
theorem R687197 : Reach 687197 := rs (se 3 (by rfl) ⟨128849, by rfl⟩) R257699
theorem R97387 : Reach 97387 := rs (se 1 (by rfl) ⟨73040, by rfl⟩) R146081
theorem R97399 : Reach 97399 := rs (se 1 (by rfl) ⟨73049, by rfl⟩) R146099
theorem R392323 : Reach 392323 := rs (se 1 (by rfl) ⟨294242, by rfl⟩) R588485
theorem R97419 : Reach 97419 := rs (se 1 (by rfl) ⟨73064, by rfl⟩) R146129
theorem R326807 : Reach 326807 := rs (se 1 (by rfl) ⟨245105, by rfl⟩) R490211
theorem R97431 : Reach 97431 := rs (se 1 (by rfl) ⟨73073, by rfl⟩) R146147
theorem R97451 : Reach 97451 := rs (se 1 (by rfl) ⟨73088, by rfl⟩) R146177
theorem R97463 : Reach 97463 := rs (se 1 (by rfl) ⟨73097, by rfl⟩) R146195
theorem R163019 : Reach 163019 := rs (se 1 (by rfl) ⟨122264, by rfl⟩) R244529
theorem R97483 : Reach 97483 := rs (se 1 (by rfl) ⟨73112, by rfl⟩) R146225
theorem R97495 : Reach 97495 := rs (se 1 (by rfl) ⟨73121, by rfl⟩) R146243
theorem R97515 : Reach 97515 := rs (se 1 (by rfl) ⟨73136, by rfl⟩) R146273
theorem R97527 : Reach 97527 := rs (se 1 (by rfl) ⟨73145, by rfl⟩) R146291
theorem R97547 : Reach 97547 := rs (se 1 (by rfl) ⟨73160, by rfl⟩) R146321
theorem R97559 : Reach 97559 := rs (se 1 (by rfl) ⟨73169, by rfl⟩) R146339
theorem R97579 : Reach 97579 := rs (se 1 (by rfl) ⟨73184, by rfl⟩) R146369
theorem R97591 : Reach 97591 := rs (se 1 (by rfl) ⟨73193, by rfl⟩) R146387
theorem R163147 : Reach 163147 := rs (se 1 (by rfl) ⟨122360, by rfl⟩) R244721
theorem R97611 : Reach 97611 := rs (se 1 (by rfl) ⟨73208, by rfl⟩) R146417
theorem R97623 : Reach 97623 := rs (se 1 (by rfl) ⟨73217, by rfl⟩) R146435
theorem R97643 : Reach 97643 := rs (se 1 (by rfl) ⟨73232, by rfl⟩) R146465
theorem R97655 : Reach 97655 := rs (se 1 (by rfl) ⟨73241, by rfl⟩) R146483
theorem R97675 : Reach 97675 := rs (se 1 (by rfl) ⟨73256, by rfl⟩) R146513
theorem R97687 : Reach 97687 := rs (se 1 (by rfl) ⟨73265, by rfl⟩) R146531
theorem R97707 : Reach 97707 := rs (se 1 (by rfl) ⟨73280, by rfl⟩) R146561
theorem R97719 : Reach 97719 := rs (se 1 (by rfl) ⟨73289, by rfl⟩) R146579
theorem R97739 : Reach 97739 := rs (se 1 (by rfl) ⟨73304, by rfl⟩) R146609
theorem R97751 : Reach 97751 := rs (se 1 (by rfl) ⟨73313, by rfl⟩) R146627
theorem R163289 : Reach 163289 := rs (se 2 (by rfl) ⟨61233, by rfl⟩) R122467
theorem R97771 : Reach 97771 := rs (se 1 (by rfl) ⟨73328, by rfl⟩) R146657
theorem R97783 : Reach 97783 := rs (se 1 (by rfl) ⟨73337, by rfl⟩) R146675
theorem R97803 : Reach 97803 := rs (se 1 (by rfl) ⟨73352, by rfl⟩) R146705
theorem R97815 : Reach 97815 := rs (se 1 (by rfl) ⟨73361, by rfl⟩) R146723
theorem R97835 : Reach 97835 := rs (se 1 (by rfl) ⟨73376, by rfl⟩) R146753
theorem R97847 : Reach 97847 := rs (se 1 (by rfl) ⟨73385, by rfl⟩) R146771
theorem R97867 : Reach 97867 := rs (se 1 (by rfl) ⟨73400, by rfl⟩) R146801
theorem R97879 : Reach 97879 := rs (se 1 (by rfl) ⟨73409, by rfl⟩) R146819
theorem R163417 : Reach 163417 := rs (se 2 (by rfl) ⟨61281, by rfl⟩) R122563
theorem R97899 : Reach 97899 := rs (se 1 (by rfl) ⟨73424, by rfl⟩) R146849
theorem R97911 : Reach 97911 := rs (se 1 (by rfl) ⟨73433, by rfl⟩) R146867
theorem R97931 : Reach 97931 := rs (se 1 (by rfl) ⟨73448, by rfl⟩) R146897
theorem R97943 : Reach 97943 := rs (se 1 (by rfl) ⟨73457, by rfl⟩) R146915
theorem R97963 : Reach 97963 := rs (se 1 (by rfl) ⟨73472, by rfl⟩) R146945
theorem R327347 : Reach 327347 := rs (se 1 (by rfl) ⟨245510, by rfl⟩) R491021
theorem R97975 : Reach 97975 := rs (se 1 (by rfl) ⟨73481, by rfl⟩) R146963
theorem R97995 : Reach 97995 := rs (se 1 (by rfl) ⟨73496, by rfl⟩) R146993
theorem R98007 : Reach 98007 := rs (se 1 (by rfl) ⟨73505, by rfl⟩) R147011
theorem R98027 : Reach 98027 := rs (se 1 (by rfl) ⟨73520, by rfl⟩) R147041
theorem R98039 : Reach 98039 := rs (se 1 (by rfl) ⟨73529, by rfl⟩) R147059
theorem R98059 : Reach 98059 := rs (se 1 (by rfl) ⟨73544, by rfl⟩) R147089
theorem R98071 : Reach 98071 := rs (se 1 (by rfl) ⟨73553, by rfl⟩) R147107
theorem R98091 : Reach 98091 := rs (se 1 (by rfl) ⟨73568, by rfl⟩) R147137
theorem R98103 : Reach 98103 := rs (se 1 (by rfl) ⟨73577, by rfl⟩) R147155
theorem R556865 : Reach 556865 := rs (se 2 (by rfl) ⟨208824, by rfl⟩) R417649
theorem R98123 : Reach 98123 := rs (se 1 (by rfl) ⟨73592, by rfl⟩) R147185
theorem R98135 : Reach 98135 := rs (se 1 (by rfl) ⟨73601, by rfl⟩) R147203
theorem R98155 : Reach 98155 := rs (se 1 (by rfl) ⟨73616, by rfl⟩) R147233
theorem R98167 : Reach 98167 := rs (se 1 (by rfl) ⟨73625, by rfl⟩) R147251
theorem R98187 : Reach 98187 := rs (se 1 (by rfl) ⟨73640, by rfl⟩) R147281
theorem R98199 : Reach 98199 := rs (se 1 (by rfl) ⟨73649, by rfl⟩) R147299
theorem R98219 : Reach 98219 := rs (se 1 (by rfl) ⟨73664, by rfl⟩) R147329
theorem R393133 : Reach 393133 := rs (se 3 (by rfl) ⟨73712, by rfl⟩) R147425
theorem R98231 : Reach 98231 := rs (se 1 (by rfl) ⟨73673, by rfl⟩) R147347
theorem R327617 : Reach 327617 := rs (se 2 (by rfl) ⟨122856, by rfl⟩) R245713
theorem R98251 : Reach 98251 := rs (se 1 (by rfl) ⟨73688, by rfl⟩) R147377
theorem R98263 : Reach 98263 := rs (se 1 (by rfl) ⟨73697, by rfl⟩) R147395
theorem R98283 : Reach 98283 := rs (se 1 (by rfl) ⟨73712, by rfl⟩) R147425
theorem R98311 : Reach 98311 := rs (se 1 (by rfl) ⟨73733, by rfl⟩) R147467
theorem R98319 : Reach 98319 := rs (se 1 (by rfl) ⟨73739, by rfl⟩) R147479
theorem R589853 : Reach 589853 := rs (se 3 (by rfl) ⟨110597, by rfl⟩) R221195
theorem R163883 : Reach 163883 := rs (se 1 (by rfl) ⟨122912, by rfl⟩) R245825
theorem R98363 : Reach 98363 := rs (se 1 (by rfl) ⟨73772, by rfl⟩) R147545
theorem R557117 : Reach 557117 := rs (se 3 (by rfl) ⟨104459, by rfl⟩) R208919
theorem R98439 : Reach 98439 := rs (se 1 (by rfl) ⟨73829, by rfl⟩) R147659
theorem R98447 : Reach 98447 := rs (se 1 (by rfl) ⟨73835, by rfl⟩) R147671
theorem R98491 : Reach 98491 := rs (se 1 (by rfl) ⟨73868, by rfl⟩) R147737
theorem R98567 : Reach 98567 := rs (se 1 (by rfl) ⟨73925, by rfl⟩) R147851
theorem R98575 : Reach 98575 := rs (se 1 (by rfl) ⟨73931, by rfl⟩) R147863
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R327995 : Reach 327995 := rs (se 1 (by rfl) ⟨245996, by rfl⟩) R491993
theorem R98619 : Reach 98619 := rs (se 1 (by rfl) ⟨73964, by rfl⟩) R147929
theorem R2326877 : Reach 2326877 := rs (se 3 (by rfl) ⟨436289, by rfl⟩) R872579
theorem R98695 : Reach 98695 := rs (se 1 (by rfl) ⟨74021, by rfl⟩) R148043
theorem R98703 : Reach 98703 := rs (se 1 (by rfl) ⟨74027, by rfl⟩) R148055
theorem R164281 : Reach 164281 := rs (se 2 (by rfl) ⟨61605, by rfl⟩) R123211
theorem R98747 : Reach 98747 := rs (se 1 (by rfl) ⟨74060, by rfl⟩) R148121
theorem R98823 : Reach 98823 := rs (se 1 (by rfl) ⟨74117, by rfl⟩) R148235
theorem R98831 : Reach 98831 := rs (se 1 (by rfl) ⟨74123, by rfl⟩) R148247
theorem R98875 : Reach 98875 := rs (se 1 (by rfl) ⟨74156, by rfl⟩) R148313
theorem R393815 : Reach 393815 := rs (se 1 (by rfl) ⟨295361, by rfl⟩) R590723
theorem R98951 : Reach 98951 := rs (se 1 (by rfl) ⟨74213, by rfl⟩) R148427
theorem R98959 : Reach 98959 := rs (se 1 (by rfl) ⟨74219, by rfl⟩) R148439
theorem R99003 : Reach 99003 := rs (se 1 (by rfl) ⟨74252, by rfl⟩) R148505
theorem R99079 : Reach 99079 := rs (se 1 (by rfl) ⟨74309, by rfl⟩) R148619
theorem R99087 : Reach 99087 := rs (se 1 (by rfl) ⟨74315, by rfl⟩) R148631
theorem R328481 : Reach 328481 := rs (se 2 (by rfl) ⟨123180, by rfl⟩) R246361
theorem R99131 : Reach 99131 := rs (se 1 (by rfl) ⟨74348, by rfl⟩) R148697
theorem R459863 : Reach 459863 := rs (se 1 (by rfl) ⟨344897, by rfl⟩) R689795
theorem R164983 : Reach 164983 := rs (se 1 (by rfl) ⟨123737, by rfl⟩) R247475
theorem R165179 : Reach 165179 := rs (se 1 (by rfl) ⟨123884, by rfl⟩) R247769
theorem R329075 : Reach 329075 := rs (se 1 (by rfl) ⟨246806, by rfl⟩) R493613
theorem R886301 : Reach 886301 := rs (se 3 (by rfl) ⟨166181, by rfl⟩) R332363
theorem R165577 : Reach 165577 := rs (se 2 (by rfl) ⟨62091, by rfl⟩) R124183
theorem R231353 : Reach 231353 := rs (se 2 (by rfl) ⟨86757, by rfl⟩) R173515
theorem R231815 : Reach 231815 := rs (se 1 (by rfl) ⟨173861, by rfl⟩) R347723
theorem R166279 : Reach 166279 := rs (se 1 (by rfl) ⟨124709, by rfl⟩) R249419
theorem R559507 : Reach 559507 := rs (se 1 (by rfl) ⟨419630, by rfl⟩) R839261
theorem R395729 : Reach 395729 := rs (se 2 (by rfl) ⟨148398, by rfl⟩) R296797
theorem R625117 : Reach 625117 := rs (se 3 (by rfl) ⟨117209, by rfl⟩) R234419
theorem R199439 : Reach 199439 := rs (se 1 (by rfl) ⟨149579, by rfl⟩) R299159
theorem R166927 : Reach 166927 := rs (se 1 (by rfl) ⟨125195, by rfl⟩) R250391
theorem R298013 : Reach 298013 := rs (se 3 (by rfl) ⟨55877, by rfl⟩) R111755
theorem R462131 : Reach 462131 := rs (se 1 (by rfl) ⟨346598, by rfl⟩) R693197
theorem R363923 : Reach 363923 := rs (se 1 (by rfl) ⟨272942, by rfl⟩) R545885
theorem R233113 : Reach 233113 := rs (se 2 (by rfl) ⟨87417, by rfl⟩) R174835
theorem R233275 : Reach 233275 := rs (se 1 (by rfl) ⟨174956, by rfl⟩) R349913
theorem R331667 : Reach 331667 := rs (se 1 (by rfl) ⟨248750, by rfl⟩) R497501
theorem R561239 : Reach 561239 := rs (se 1 (by rfl) ⟨420929, by rfl⟩) R841859
theorem R135355 : Reach 135355 := rs (se 1 (by rfl) ⟨101516, by rfl⟩) R203033
theorem R233729 : Reach 233729 := rs (se 2 (by rfl) ⟨87648, by rfl⟩) R175297
theorem R463553 : Reach 463553 := rs (se 2 (by rfl) ⟨173832, by rfl⟩) R347665
theorem R1086209 : Reach 1086209 := rs (se 2 (by rfl) ⟨407328, by rfl⟩) R814657
theorem R398195 : Reach 398195 := rs (se 1 (by rfl) ⟨298646, by rfl⟩) R597293
theorem R496529 : Reach 496529 := rs (se 2 (by rfl) ⟨186198, by rfl⟩) R372397
theorem R594955 : Reach 594955 := rs (se 1 (by rfl) ⟨446216, by rfl⟩) R892433
theorem R365579 : Reach 365579 := rs (se 1 (by rfl) ⟨274184, by rfl⟩) R548369
theorem R333071 : Reach 333071 := rs (se 1 (by rfl) ⟨249803, by rfl⟩) R499607
theorem R103951 : Reach 103951 := rs (se 1 (by rfl) ⟨77963, by rfl⟩) R155927
theorem R333341 : Reach 333341 := rs (se 3 (by rfl) ⟨62501, by rfl⟩) R125003
theorem R136847 : Reach 136847 := rs (se 1 (by rfl) ⟨102635, by rfl⟩) R205271
theorem R497441 : Reach 497441 := rs (se 2 (by rfl) ⟨186540, by rfl⟩) R373081
theorem R1054579 : Reach 1054579 := rs (se 1 (by rfl) ⟨790934, by rfl⟩) R1581869
theorem R2398409 : Reach 2398409 := rs (se 2 (by rfl) ⟨899403, by rfl⟩) R1798807
theorem R1579409 : Reach 1579409 := rs (se 2 (by rfl) ⟨592278, by rfl⟩) R1184557
theorem R203323 : Reach 203323 := rs (se 1 (by rfl) ⟨152492, by rfl⟩) R304985
theorem R367507 : Reach 367507 := rs (se 1 (by rfl) ⟨275630, by rfl⟩) R551261
theorem R498635 : Reach 498635 := rs (se 1 (by rfl) ⟨373976, by rfl⟩) R747953
theorem R498959 : Reach 498959 := rs (se 1 (by rfl) ⟨374219, by rfl⟩) R748439
theorem R1056185 : Reach 1056185 := rs (se 2 (by rfl) ⟨396069, by rfl⟩) R792139
theorem R466397 : Reach 466397 := rs (se 3 (by rfl) ⟨87449, by rfl⟩) R174899
theorem R1089125 : Reach 1089125 := rs (se 4 (by rfl) ⟨102105, by rfl⟩) R204211
theorem R6037685 : Reach 6037685 := rs (se 5 (by rfl) ⟨283016, by rfl⟩) R566033
theorem R139639 : Reach 139639 := rs (se 1 (by rfl) ⟨104729, by rfl⟩) R209459
theorem R107023 : Reach 107023 := rs (se 1 (by rfl) ⟨80267, by rfl⟩) R160535
theorem R139963 : Reach 139963 := rs (se 1 (by rfl) ⟨104972, by rfl⟩) R209945
theorem R500417 : Reach 500417 := rs (se 2 (by rfl) ⟨187656, by rfl⟩) R375313
theorem R369467 : Reach 369467 := rs (se 1 (by rfl) ⟨277100, by rfl⟩) R554201
theorem R729971 : Reach 729971 := rs (se 1 (by rfl) ⟨547478, by rfl⟩) R1094957
theorem R205715 : Reach 205715 := rs (se 1 (by rfl) ⟨154286, by rfl⟩) R308573
theorem R107527 : Reach 107527 := rs (se 1 (by rfl) ⟨80645, by rfl⟩) R161291
theorem R1090583 : Reach 1090583 := rs (se 1 (by rfl) ⟨817937, by rfl⟩) R1635875
theorem R468011 : Reach 468011 := rs (se 1 (by rfl) ⟨351008, by rfl⟩) R702017
theorem R7611479 : Reach 7611479 := rs (se 1 (by rfl) ⟨5708609, by rfl⟩) R11417219
theorem R271507 : Reach 271507 := rs (se 1 (by rfl) ⟨203630, by rfl⟩) R407261
theorem R107707 : Reach 107707 := rs (se 1 (by rfl) ⟨80780, by rfl⟩) R161561
theorem R369953 : Reach 369953 := rs (se 2 (by rfl) ⟨138732, by rfl⟩) R277465
theorem R140663 : Reach 140663 := rs (se 1 (by rfl) ⟨105497, by rfl⟩) R210995
theorem R1254791 : Reach 1254791 := rs (se 1 (by rfl) ⟨941093, by rfl⟩) R1882187
theorem R108175 : Reach 108175 := rs (se 1 (by rfl) ⟨81131, by rfl⟩) R162263
theorem R927409 : Reach 927409 := rs (se 2 (by rfl) ⟨347778, by rfl⟩) R695557
theorem R534209 : Reach 534209 := rs (se 2 (by rfl) ⟨200328, by rfl⟩) R400657
theorem R26388341 : Reach 26388341 := rs (se 5 (by rfl) ⟨1236953, by rfl⟩) R2473907
theorem R501713 : Reach 501713 := rs (se 2 (by rfl) ⟨188142, by rfl⟩) R376285
theorem R108679 : Reach 108679 := rs (se 1 (by rfl) ⟨81509, by rfl⟩) R163019
theorem R370925 : Reach 370925 := rs (se 3 (by rfl) ⟨69548, by rfl⟩) R139097
theorem R108859 : Reach 108859 := rs (se 1 (by rfl) ⟨81644, by rfl⟩) R163289
theorem R928259 : Reach 928259 := rs (se 1 (by rfl) ⟨696194, by rfl⟩) R1392389
theorem R371243 : Reach 371243 := rs (se 1 (by rfl) ⟨278432, by rfl⟩) R556865
theorem R1845827 : Reach 1845827 := rs (se 1 (by rfl) ⟨1384370, by rfl⟩) R2768741
theorem R109327 : Reach 109327 := rs (se 1 (by rfl) ⟨81995, by rfl⟩) R163991
theorem R273239 : Reach 273239 := rs (se 1 (by rfl) ⟨204929, by rfl⟩) R409859
theorem R338897 : Reach 338897 := rs (se 2 (by rfl) ⟨127086, by rfl⟩) R254173
theorem R109831 : Reach 109831 := rs (se 1 (by rfl) ⟨82373, by rfl⟩) R164747
theorem R798011 : Reach 798011 := rs (se 1 (by rfl) ⟨598508, by rfl⟩) R1197017
theorem R241015 : Reach 241015 := rs (se 1 (by rfl) ⟨180761, by rfl⟩) R361523
theorem R142727 : Reach 142727 := rs (se 1 (by rfl) ⟨107045, by rfl⟩) R214091
theorem R142763 : Reach 142763 := rs (se 1 (by rfl) ⟨107072, by rfl⟩) R214145
theorem R110011 : Reach 110011 := rs (se 1 (by rfl) ⟨82508, by rfl⟩) R165017
theorem R142793 : Reach 142793 := rs (se 2 (by rfl) ⟨53547, by rfl⟩) R107095
theorem R404945 : Reach 404945 := rs (se 2 (by rfl) ⟨151854, by rfl⟩) R303709
theorem R142907 : Reach 142907 := rs (se 1 (by rfl) ⟨107180, by rfl⟩) R214361
theorem R142967 : Reach 142967 := rs (se 1 (by rfl) ⟨107225, by rfl⟩) R214451
theorem R142991 : Reach 142991 := rs (se 1 (by rfl) ⟨107243, by rfl⟩) R214487
theorem R470701 : Reach 470701 := rs (se 3 (by rfl) ⟨88256, by rfl⟩) R176513
theorem R143033 : Reach 143033 := rs (se 2 (by rfl) ⟨53637, by rfl⟩) R107275
theorem R208585 : Reach 208585 := rs (se 2 (by rfl) ⟨78219, by rfl⟩) R156439
theorem R634625 : Reach 634625 := rs (se 2 (by rfl) ⟨237984, by rfl⟩) R475969
theorem R143111 : Reach 143111 := rs (se 1 (by rfl) ⟨107333, by rfl⟩) R214667
theorem R241451 : Reach 241451 := rs (se 1 (by rfl) ⟨181088, by rfl⟩) R362177
theorem R143147 : Reach 143147 := rs (se 1 (by rfl) ⟨107360, by rfl⟩) R214721
theorem R634675 : Reach 634675 := rs (se 1 (by rfl) ⟨476006, by rfl⟩) R952013
theorem R143177 : Reach 143177 := rs (se 2 (by rfl) ⟨53691, by rfl⟩) R107383
theorem R110479 : Reach 110479 := rs (se 1 (by rfl) ⟨82859, by rfl⟩) R165719
theorem R143291 : Reach 143291 := rs (se 1 (by rfl) ⟨107468, by rfl⟩) R214937
theorem R143351 : Reach 143351 := rs (se 1 (by rfl) ⟨107513, by rfl⟩) R215027
theorem R143375 : Reach 143375 := rs (se 1 (by rfl) ⟨107531, by rfl⟩) R215063
theorem R143417 : Reach 143417 := rs (se 2 (by rfl) ⟨53781, by rfl⟩) R107563
theorem R143495 : Reach 143495 := rs (se 1 (by rfl) ⟨107621, by rfl⟩) R215243
theorem R143531 : Reach 143531 := rs (se 1 (by rfl) ⟨107648, by rfl⟩) R215297
theorem R209081 : Reach 209081 := rs (se 2 (by rfl) ⟨78405, by rfl⟩) R156811
theorem R143561 : Reach 143561 := rs (se 2 (by rfl) ⟨53835, by rfl⟩) R107671
theorem R307471 : Reach 307471 := rs (se 1 (by rfl) ⟨230603, by rfl⟩) R461207
theorem R143675 : Reach 143675 := rs (se 1 (by rfl) ⟨107756, by rfl⟩) R215513
theorem R143735 : Reach 143735 := rs (se 1 (by rfl) ⟨107801, by rfl⟩) R215603
theorem R274823 : Reach 274823 := rs (se 1 (by rfl) ⟨206117, by rfl⟩) R412235
theorem R110983 : Reach 110983 := rs (se 1 (by rfl) ⟨83237, by rfl⟩) R166475
theorem R143759 : Reach 143759 := rs (se 1 (by rfl) ⟨107819, by rfl⟩) R215639
theorem R143801 : Reach 143801 := rs (se 2 (by rfl) ⟨53925, by rfl⟩) R107851
theorem R143879 : Reach 143879 := rs (se 1 (by rfl) ⟨107909, by rfl⟩) R215819
theorem R143915 : Reach 143915 := rs (se 1 (by rfl) ⟨107936, by rfl⟩) R215873
theorem R111163 : Reach 111163 := rs (se 1 (by rfl) ⟨83372, by rfl⟩) R166745
theorem R143945 : Reach 143945 := rs (se 2 (by rfl) ⟨53979, by rfl⟩) R107959
theorem R242291 : Reach 242291 := rs (se 1 (by rfl) ⟨181718, by rfl⟩) R363437
theorem R242311 : Reach 242311 := rs (se 1 (by rfl) ⟨181733, by rfl⟩) R363467
theorem R144059 : Reach 144059 := rs (se 1 (by rfl) ⟨108044, by rfl⟩) R216089
theorem R537281 : Reach 537281 := rs (se 2 (by rfl) ⟨201480, by rfl⟩) R402961
theorem R144119 : Reach 144119 := rs (se 1 (by rfl) ⟨108089, by rfl⟩) R216179
theorem R144143 : Reach 144143 := rs (se 1 (by rfl) ⟨108107, by rfl⟩) R216215
theorem R144185 : Reach 144185 := rs (se 2 (by rfl) ⟨54069, by rfl⟩) R108139
theorem R144263 : Reach 144263 := rs (se 1 (by rfl) ⟨108197, by rfl⟩) R216395
theorem R242585 : Reach 242585 := rs (se 2 (by rfl) ⟨90969, by rfl⟩) R181939
theorem R144299 : Reach 144299 := rs (se 1 (by rfl) ⟨108224, by rfl⟩) R216449
theorem R144329 : Reach 144329 := rs (se 2 (by rfl) ⟨54123, by rfl⟩) R108247
theorem R275471 : Reach 275471 := rs (se 1 (by rfl) ⟨206603, by rfl⟩) R413207
theorem R242747 : Reach 242747 := rs (se 1 (by rfl) ⟨182060, by rfl⟩) R364121
theorem R144443 : Reach 144443 := rs (se 1 (by rfl) ⟨108332, by rfl⟩) R216665
theorem R144503 : Reach 144503 := rs (se 1 (by rfl) ⟨108377, by rfl⟩) R216755
theorem R210055 : Reach 210055 := rs (se 1 (by rfl) ⟨157541, by rfl⟩) R315083
theorem R144527 : Reach 144527 := rs (se 1 (by rfl) ⟨108395, by rfl⟩) R216791
theorem R144569 : Reach 144569 := rs (se 2 (by rfl) ⟨54213, by rfl⟩) R108427
theorem R144647 : Reach 144647 := rs (se 1 (by rfl) ⟨108485, by rfl⟩) R216971
theorem R242959 : Reach 242959 := rs (se 1 (by rfl) ⟨182219, by rfl⟩) R364439
theorem R144683 : Reach 144683 := rs (se 1 (by rfl) ⟨108512, by rfl⟩) R217025
theorem R144713 : Reach 144713 := rs (se 2 (by rfl) ⟨54267, by rfl⟩) R108535
theorem R406919 : Reach 406919 := rs (se 1 (by rfl) ⟨305189, by rfl⟩) R610379
theorem R144827 : Reach 144827 := rs (se 1 (by rfl) ⟨108620, by rfl⟩) R217241
theorem R144841 : Reach 144841 := rs (se 2 (by rfl) ⟨54315, by rfl⟩) R108631
theorem R472529 : Reach 472529 := rs (se 2 (by rfl) ⟨177198, by rfl⟩) R354397
theorem R144887 : Reach 144887 := rs (se 1 (by rfl) ⟨108665, by rfl⟩) R217331
theorem R144911 : Reach 144911 := rs (se 1 (by rfl) ⟨108683, by rfl⟩) R217367
theorem R243233 : Reach 243233 := rs (se 2 (by rfl) ⟨91212, by rfl⟩) R182425
theorem R144953 : Reach 144953 := rs (se 2 (by rfl) ⟨54357, by rfl⟩) R108715
theorem R145031 : Reach 145031 := rs (se 1 (by rfl) ⟨108773, by rfl⟩) R217547
theorem R145067 : Reach 145067 := rs (se 1 (by rfl) ⟨108800, by rfl⟩) R217601
theorem R145097 : Reach 145097 := rs (se 2 (by rfl) ⟨54411, by rfl⟩) R108823
theorem R145211 : Reach 145211 := rs (se 1 (by rfl) ⟨108908, by rfl⟩) R217817
theorem R145271 : Reach 145271 := rs (se 1 (by rfl) ⟨108953, by rfl⟩) R217907
theorem R145295 : Reach 145295 := rs (se 1 (by rfl) ⟨108971, by rfl⟩) R217943
theorem R702361 : Reach 702361 := rs (se 2 (by rfl) ⟨263385, by rfl⟩) R526771
theorem R145337 : Reach 145337 := rs (se 2 (by rfl) ⟨54501, by rfl⟩) R109003
theorem R145415 : Reach 145415 := rs (se 1 (by rfl) ⟨109061, by rfl⟩) R218123
theorem R374813 : Reach 374813 := rs (se 3 (by rfl) ⟨70277, by rfl⟩) R140555
theorem R145451 : Reach 145451 := rs (se 1 (by rfl) ⟨109088, by rfl⟩) R218177
theorem R374827 : Reach 374827 := rs (se 1 (by rfl) ⟨281120, by rfl⟩) R562241
theorem R145481 : Reach 145481 := rs (se 2 (by rfl) ⟨54555, by rfl⟩) R109111
theorem R145595 : Reach 145595 := rs (se 1 (by rfl) ⟨109196, by rfl⟩) R218393
theorem R145655 : Reach 145655 := rs (se 1 (by rfl) ⟨109241, by rfl⟩) R218483
theorem R145679 : Reach 145679 := rs (se 1 (by rfl) ⟨109259, by rfl⟩) R218519
theorem R211243 : Reach 211243 := rs (se 1 (by rfl) ⟨158432, by rfl⟩) R316865
theorem R145721 : Reach 145721 := rs (se 2 (by rfl) ⟨54645, by rfl⟩) R109291
theorem R145799 : Reach 145799 := rs (se 1 (by rfl) ⟨109349, by rfl⟩) R218699
theorem R145835 : Reach 145835 := rs (se 1 (by rfl) ⟨109376, by rfl⟩) R218753
theorem R309689 : Reach 309689 := rs (se 2 (by rfl) ⟨116133, by rfl⟩) R232267
theorem R145865 : Reach 145865 := rs (se 2 (by rfl) ⟨54699, by rfl⟩) R109399
theorem R244235 : Reach 244235 := rs (se 1 (by rfl) ⟨183176, by rfl⟩) R366353
theorem R145979 : Reach 145979 := rs (se 1 (by rfl) ⟨109484, by rfl⟩) R218969
theorem R146039 : Reach 146039 := rs (se 1 (by rfl) ⟨109529, by rfl⟩) R219059
theorem R277111 : Reach 277111 := rs (se 1 (by rfl) ⟨207833, by rfl⟩) R415667
theorem R146063 : Reach 146063 := rs (se 1 (by rfl) ⟨109547, by rfl⟩) R219095
theorem R146105 : Reach 146105 := rs (se 2 (by rfl) ⟨54789, by rfl⟩) R109579
theorem R146183 : Reach 146183 := rs (se 1 (by rfl) ⟨109637, by rfl⟩) R219275
theorem R146219 : Reach 146219 := rs (se 1 (by rfl) ⟨109664, by rfl⟩) R219329
theorem R146249 : Reach 146249 := rs (se 2 (by rfl) ⟨54843, by rfl⟩) R109687
theorem R473971 : Reach 473971 := rs (se 1 (by rfl) ⟨355478, by rfl⟩) R710957
theorem R146363 : Reach 146363 := rs (se 1 (by rfl) ⟨109772, by rfl⟩) R219545
theorem R146423 : Reach 146423 := rs (se 1 (by rfl) ⟨109817, by rfl⟩) R219635
theorem R146447 : Reach 146447 := rs (se 1 (by rfl) ⟨109835, by rfl⟩) R219671
theorem R146489 : Reach 146489 := rs (se 2 (by rfl) ⟨54933, by rfl⟩) R109867
theorem R146567 : Reach 146567 := rs (se 1 (by rfl) ⟨109925, by rfl⟩) R219851
theorem R244883 : Reach 244883 := rs (se 1 (by rfl) ⟨183662, by rfl⟩) R367325
theorem R146603 : Reach 146603 := rs (se 1 (by rfl) ⟨109952, by rfl⟩) R219905
theorem R146633 : Reach 146633 := rs (se 2 (by rfl) ⟨54987, by rfl⟩) R109975
theorem R408833 : Reach 408833 := rs (se 2 (by rfl) ⟨153312, by rfl⟩) R306625
theorem R146747 : Reach 146747 := rs (se 1 (by rfl) ⟨110060, by rfl⟩) R220121
theorem R146807 : Reach 146807 := rs (se 1 (by rfl) ⟨110105, by rfl⟩) R220211
theorem R146831 : Reach 146831 := rs (se 1 (by rfl) ⟨110123, by rfl⟩) R220247
theorem R310675 : Reach 310675 := rs (se 1 (by rfl) ⟨233006, by rfl⟩) R466013
theorem R245177 : Reach 245177 := rs (se 2 (by rfl) ⟨91941, by rfl⟩) R183883
theorem R146873 : Reach 146873 := rs (se 2 (by rfl) ⟨55077, by rfl⟩) R110155
theorem R146951 : Reach 146951 := rs (se 1 (by rfl) ⟨110213, by rfl⟩) R220427
theorem R146987 : Reach 146987 := rs (se 1 (by rfl) ⟨110240, by rfl⟩) R220481
theorem R147017 : Reach 147017 := rs (se 2 (by rfl) ⟨55131, by rfl⟩) R110263
theorem R409175 : Reach 409175 := rs (se 1 (by rfl) ⟨306881, by rfl⟩) R613763
theorem R147131 : Reach 147131 := rs (se 1 (by rfl) ⟨110348, by rfl⟩) R220697
theorem R147191 : Reach 147191 := rs (se 1 (by rfl) ⟨110393, by rfl⟩) R220787
theorem R147215 : Reach 147215 := rs (se 1 (by rfl) ⟨110411, by rfl⟩) R220823
theorem R147257 : Reach 147257 := rs (se 2 (by rfl) ⟨55221, by rfl⟩) R110443
theorem R278387 : Reach 278387 := rs (se 1 (by rfl) ⟨208790, by rfl⟩) R417581
theorem R147335 : Reach 147335 := rs (se 1 (by rfl) ⟨110501, by rfl⟩) R221003
theorem R638873 : Reach 638873 := rs (se 2 (by rfl) ⟨239577, by rfl⟩) R479155
theorem R147371 : Reach 147371 := rs (se 1 (by rfl) ⟨110528, by rfl⟩) R221057
theorem R147401 : Reach 147401 := rs (se 2 (by rfl) ⟨55275, by rfl⟩) R110551
theorem R147515 : Reach 147515 := rs (se 1 (by rfl) ⟨110636, by rfl⟩) R221273
theorem R278615 : Reach 278615 := rs (se 1 (by rfl) ⟨208961, by rfl⟩) R417923
theorem R245875 : Reach 245875 := rs (se 1 (by rfl) ⟨184406, by rfl⟩) R368813
theorem R147575 : Reach 147575 := rs (se 1 (by rfl) ⟨110681, by rfl⟩) R221363
theorem R147599 : Reach 147599 := rs (se 1 (by rfl) ⟨110699, by rfl⟩) R221399
theorem R147641 : Reach 147641 := rs (se 2 (by rfl) ⟨55365, by rfl⟩) R110731
theorem R344321 : Reach 344321 := rs (se 2 (by rfl) ⟨129120, by rfl⟩) R258241
theorem R246017 : Reach 246017 := rs (se 2 (by rfl) ⟨92256, by rfl⟩) R184513
theorem R147719 : Reach 147719 := rs (se 1 (by rfl) ⟨110789, by rfl⟩) R221579
theorem R147755 : Reach 147755 := rs (se 1 (by rfl) ⟨110816, by rfl⟩) R221633
theorem R147785 : Reach 147785 := rs (se 2 (by rfl) ⟨55419, by rfl⟩) R110839
theorem R147899 : Reach 147899 := rs (se 1 (by rfl) ⟨110924, by rfl⟩) R221849
theorem R1556957 : Reach 1556957 := rs (se 3 (by rfl) ⟨291929, by rfl⟩) R583859
theorem R147959 : Reach 147959 := rs (se 1 (by rfl) ⟨110969, by rfl⟩) R221939
theorem R147983 : Reach 147983 := rs (se 1 (by rfl) ⟨110987, by rfl⟩) R221975
theorem R148025 : Reach 148025 := rs (se 2 (by rfl) ⟨55509, by rfl⟩) R111019
theorem R148103 : Reach 148103 := rs (se 1 (by rfl) ⟨111077, by rfl⟩) R222155
theorem R180883 : Reach 180883 := rs (se 1 (by rfl) ⟨135662, by rfl⟩) R271325
theorem R148139 : Reach 148139 := rs (se 1 (by rfl) ⟨111104, by rfl⟩) R222209
theorem R246473 : Reach 246473 := rs (se 2 (by rfl) ⟨92427, by rfl⟩) R184855
theorem R148169 : Reach 148169 := rs (se 2 (by rfl) ⟨55563, by rfl⟩) R111127
theorem R3982117 : Reach 3982117 := rs (se 4 (by rfl) ⟨373323, by rfl⟩) R746647
theorem R803621 : Reach 803621 := rs (se 4 (by rfl) ⟨75339, by rfl⟩) R150679
theorem R148283 : Reach 148283 := rs (se 1 (by rfl) ⟨111212, by rfl⟩) R222425
theorem R181111 : Reach 181111 := rs (se 1 (by rfl) ⟨135833, by rfl⟩) R271667
theorem R148343 : Reach 148343 := rs (se 1 (by rfl) ⟨111257, by rfl⟩) R222515
theorem R148367 : Reach 148367 := rs (se 1 (by rfl) ⟨111275, by rfl⟩) R222551
theorem R148409 : Reach 148409 := rs (se 2 (by rfl) ⟨55653, by rfl⟩) R111307
theorem R148487 : Reach 148487 := rs (se 1 (by rfl) ⟨111365, by rfl⟩) R222731
theorem R246827 : Reach 246827 := rs (se 1 (by rfl) ⟨185120, by rfl⟩) R370241
theorem R148523 : Reach 148523 := rs (se 1 (by rfl) ⟨111392, by rfl⟩) R222785
theorem R148553 : Reach 148553 := rs (se 2 (by rfl) ⟨55707, by rfl⟩) R111415
theorem R2114693 : Reach 2114693 := rs (se 4 (by rfl) ⟨198252, by rfl⟩) R396505
theorem R214163 : Reach 214163 := rs (se 1 (by rfl) ⟨160622, by rfl⟩) R321245
theorem R148667 : Reach 148667 := rs (se 1 (by rfl) ⟨111500, by rfl⟩) R223001
theorem R214217 : Reach 214217 := rs (se 2 (by rfl) ⟨80331, by rfl⟩) R160663
theorem R542011 : Reach 542011 := rs (se 1 (by rfl) ⟨406508, by rfl⟩) R813017
theorem R345529 : Reach 345529 := rs (se 2 (by rfl) ⟨129573, by rfl⟩) R259147
theorem R1099331 : Reach 1099331 := rs (se 1 (by rfl) ⟨824498, by rfl⟩) R1648997
theorem R280199 : Reach 280199 := rs (se 1 (by rfl) ⟨210149, by rfl⟩) R420299
theorem R280381 : Reach 280381 := rs (se 3 (by rfl) ⟨52571, by rfl⟩) R105143
theorem R214919 : Reach 214919 := rs (se 1 (by rfl) ⟨161189, by rfl⟩) R322379
theorem R411601 : Reach 411601 := rs (se 2 (by rfl) ⟨154350, by rfl⟩) R308701
theorem R247819 : Reach 247819 := rs (se 1 (by rfl) ⟨185864, by rfl⟩) R371729
theorem R247823 : Reach 247823 := rs (se 1 (by rfl) ⟨185867, by rfl⟩) R371735
theorem R215099 : Reach 215099 := rs (se 1 (by rfl) ⟨161324, by rfl⟩) R322649
theorem R444503 : Reach 444503 := rs (se 1 (by rfl) ⟨333377, by rfl⟩) R666755
theorem R247961 : Reach 247961 := rs (se 2 (by rfl) ⟨92985, by rfl⟩) R185971
theorem R215225 : Reach 215225 := rs (se 2 (by rfl) ⟨80709, by rfl⟩) R161419
theorem R936173 : Reach 936173 := rs (se 3 (by rfl) ⟨175532, by rfl⟩) R351065
theorem R280847 : Reach 280847 := rs (se 1 (by rfl) ⟨210635, by rfl⟩) R421271
theorem R936251 : Reach 936251 := rs (se 1 (by rfl) ⟨702188, by rfl⟩) R1404377
theorem R248123 : Reach 248123 := rs (se 1 (by rfl) ⟨186092, by rfl⟩) R372185
theorem R182675 : Reach 182675 := rs (se 1 (by rfl) ⟨137006, by rfl⟩) R274013
theorem R182729 : Reach 182729 := rs (se 2 (by rfl) ⟨68523, by rfl⟩) R137047
theorem R215567 : Reach 215567 := rs (se 1 (by rfl) ⟨161675, by rfl⟩) R323351
theorem R215585 : Reach 215585 := rs (se 2 (by rfl) ⟨80844, by rfl⟩) R161689
theorem R182827 : Reach 182827 := rs (se 1 (by rfl) ⟨137120, by rfl⟩) R274241
theorem R379511 : Reach 379511 := rs (se 1 (by rfl) ⟨284633, by rfl⟩) R569267
theorem R248467 : Reach 248467 := rs (se 1 (by rfl) ⟨186350, by rfl⟩) R372701
theorem R314057 : Reach 314057 := rs (se 2 (by rfl) ⟨117771, by rfl⟩) R235543
theorem R543469 : Reach 543469 := rs (se 3 (by rfl) ⟨101900, by rfl⟩) R203801
theorem R183055 : Reach 183055 := rs (se 1 (by rfl) ⟨137291, by rfl⟩) R274583
theorem R248609 : Reach 248609 := rs (se 2 (by rfl) ⟨93228, by rfl⟩) R186457
theorem R215927 : Reach 215927 := rs (se 1 (by rfl) ⟨161945, by rfl⟩) R323891
theorem R216107 : Reach 216107 := rs (se 1 (by rfl) ⟨162080, by rfl⟩) R324161
theorem R150571 : Reach 150571 := rs (se 1 (by rfl) ⟨112928, by rfl⟩) R225857
theorem R1887623 : Reach 1887623 := rs (se 1 (by rfl) ⟨1415717, by rfl⟩) R2831435
theorem R216467 : Reach 216467 := rs (se 1 (by rfl) ⟨162350, by rfl⟩) R324701
theorem R216521 : Reach 216521 := rs (se 2 (by rfl) ⟨81195, by rfl⟩) R162391
theorem R282113 : Reach 282113 := rs (se 2 (by rfl) ⟨105792, by rfl⟩) R211585
theorem R249601 : Reach 249601 := rs (se 2 (by rfl) ⟨93600, by rfl⟩) R187201
theorem R118903 : Reach 118903 := rs (se 1 (by rfl) ⟨89177, by rfl⟩) R178355
theorem R217223 : Reach 217223 := rs (se 1 (by rfl) ⟨162917, by rfl⟩) R325835
theorem R512173 : Reach 512173 := rs (se 3 (by rfl) ⟨96032, by rfl⟩) R192065
theorem R2937073 : Reach 2937073 := rs (se 2 (by rfl) ⟨1101402, by rfl⟩) R2202805
theorem R184619 : Reach 184619 := rs (se 1 (by rfl) ⟨138464, by rfl⟩) R276929
theorem R217403 : Reach 217403 := rs (se 1 (by rfl) ⟨163052, by rfl⟩) R326105
theorem R414011 : Reach 414011 := rs (se 1 (by rfl) ⟨310508, by rfl⟩) R621017
theorem R250199 : Reach 250199 := rs (se 1 (by rfl) ⟨187649, by rfl⟩) R375299
theorem R217529 : Reach 217529 := rs (se 2 (by rfl) ⟨81573, by rfl⟩) R163147
theorem R250411 : Reach 250411 := rs (se 1 (by rfl) ⟨187808, by rfl⟩) R375617
theorem R545453 : Reach 545453 := rs (se 3 (by rfl) ⟨102272, by rfl⟩) R204545
theorem R250553 : Reach 250553 := rs (se 2 (by rfl) ⟨93957, by rfl⟩) R187915
theorem R217871 : Reach 217871 := rs (se 1 (by rfl) ⟨163403, by rfl⟩) R326807
theorem R217889 : Reach 217889 := rs (se 2 (by rfl) ⟨81708, by rfl⟩) R163417
theorem R218231 : Reach 218231 := rs (se 1 (by rfl) ⟨163673, by rfl⟩) R327347
theorem R218411 : Reach 218411 := rs (se 1 (by rfl) ⟨163808, by rfl⟩) R327617
theorem R251407 : Reach 251407 := rs (se 1 (by rfl) ⟨188555, by rfl⟩) R377111
theorem R218771 : Reach 218771 := rs (se 1 (by rfl) ⟨164078, by rfl⟩) R328157
theorem R218825 : Reach 218825 := rs (se 2 (by rfl) ⟨82059, by rfl⟩) R164119
theorem R120619 : Reach 120619 := rs (se 1 (by rfl) ⟨90464, by rfl⟩) R180929
theorem R907057 : Reach 907057 := rs (se 2 (by rfl) ⟨340146, by rfl⟩) R680293
theorem R1103705 : Reach 1103705 := rs (se 2 (by rfl) ⟨413889, by rfl⟩) R827779
theorem R186313 : Reach 186313 := rs (se 2 (by rfl) ⟨69867, by rfl⟩) R139735
theorem R120847 : Reach 120847 := rs (se 1 (by rfl) ⟨90635, by rfl⟩) R181271
theorem R1267913 : Reach 1267913 := rs (se 2 (by rfl) ⟨475467, by rfl⟩) R950935
theorem R481625 : Reach 481625 := rs (se 2 (by rfl) ⟨180609, by rfl⟩) R361219
theorem R1399133 : Reach 1399133 := rs (se 3 (by rfl) ⟨262337, by rfl⟩) R524675
theorem R219527 : Reach 219527 := rs (se 1 (by rfl) ⟨164645, by rfl⟩) R329291
theorem R219707 : Reach 219707 := rs (se 1 (by rfl) ⟨164780, by rfl⟩) R329561
theorem R219833 : Reach 219833 := rs (se 2 (by rfl) ⟨82437, by rfl⟩) R164875
theorem R121591 : Reach 121591 := rs (se 1 (by rfl) ⟨91193, by rfl⟩) R182387
theorem R2579363 : Reach 2579363 := rs (se 1 (by rfl) ⟨1934522, by rfl⟩) R3869045
theorem R547843 : Reach 547843 := rs (se 1 (by rfl) ⟨410882, by rfl⟩) R821765
theorem R154639 : Reach 154639 := rs (se 1 (by rfl) ⟨115979, by rfl⟩) R231959
theorem R220175 : Reach 220175 := rs (se 1 (by rfl) ⟨165131, by rfl⟩) R330263
theorem R220193 : Reach 220193 := rs (se 2 (by rfl) ⟨82572, by rfl⟩) R165145
theorem R121915 : Reach 121915 := rs (se 1 (by rfl) ⟨91436, by rfl⟩) R182873
theorem R842885 : Reach 842885 := rs (se 4 (by rfl) ⟨79020, by rfl⟩) R158041
theorem R351469 : Reach 351469 := rs (se 3 (by rfl) ⟨65900, by rfl⟩) R131801
theorem R1793339 : Reach 1793339 := rs (se 1 (by rfl) ⟨1345004, by rfl⟩) R2690009
theorem R220535 : Reach 220535 := rs (se 1 (by rfl) ⟨165401, by rfl⟩) R330803
theorem R155015 : Reach 155015 := rs (se 1 (by rfl) ⟨116261, by rfl⟩) R232523
theorem R1334663 : Reach 1334663 := rs (se 1 (by rfl) ⟨1000997, by rfl⟩) R2001995
theorem R155081 : Reach 155081 := rs (se 2 (by rfl) ⟨58155, by rfl⟩) R116311
theorem R122411 : Reach 122411 := rs (se 1 (by rfl) ⟨91808, by rfl⟩) R183617
theorem R220715 : Reach 220715 := rs (se 1 (by rfl) ⟨165536, by rfl⟩) R331073
theorem R745037 : Reach 745037 := rs (se 3 (by rfl) ⟨139694, by rfl⟩) R279389
theorem R1269553 : Reach 1269553 := rs (se 2 (by rfl) ⟨476082, by rfl⟩) R952165
theorem R843635 : Reach 843635 := rs (se 1 (by rfl) ⟨632726, by rfl⟩) R1265453
theorem R221075 : Reach 221075 := rs (se 1 (by rfl) ⟨165806, by rfl⟩) R331613
theorem R221129 : Reach 221129 := rs (se 2 (by rfl) ⟨82923, by rfl⟩) R165847
theorem R122887 : Reach 122887 := rs (se 1 (by rfl) ⟨92165, by rfl⟩) R184331
theorem R483731 : Reach 483731 := rs (se 1 (by rfl) ⟨362798, by rfl⟩) R725597
theorem R123383 : Reach 123383 := rs (se 1 (by rfl) ⟨92537, by rfl⟩) R185075
theorem R516611 : Reach 516611 := rs (se 1 (by rfl) ⟨387458, by rfl⟩) R774917
theorem R221831 : Reach 221831 := rs (se 1 (by rfl) ⟨166373, by rfl⟩) R332747
theorem R123535 : Reach 123535 := rs (se 1 (by rfl) ⟨92651, by rfl⟩) R185303
theorem R123707 : Reach 123707 := rs (se 1 (by rfl) ⟨92780, by rfl⟩) R185561
theorem R222011 : Reach 222011 := rs (se 1 (by rfl) ⟨166508, by rfl⟩) R333017
theorem R222137 : Reach 222137 := rs (se 2 (by rfl) ⟨83301, by rfl⟩) R166603
theorem R28697813 : Reach 28697813 := rs (se 7 (by rfl) ⟨336302, by rfl⟩) R672605
theorem R222479 : Reach 222479 := rs (se 1 (by rfl) ⟨166859, by rfl⟩) R333719
theorem R222497 : Reach 222497 := rs (se 2 (by rfl) ⟨83436, by rfl⟩) R166873
theorem R550259 : Reach 550259 := rs (se 1 (by rfl) ⟨412694, by rfl⟩) R825389
theorem R419357 : Reach 419357 := rs (se 3 (by rfl) ⟨78629, by rfl⟩) R157259
theorem R222839 : Reach 222839 := rs (se 1 (by rfl) ⟨167129, by rfl⟩) R334259
theorem R124679 : Reach 124679 := rs (se 1 (by rfl) ⟨93509, by rfl⟩) R187019
theorem R223019 : Reach 223019 := rs (se 1 (by rfl) ⟨167264, by rfl⟩) R334529
theorem R747467 : Reach 747467 := rs (se 1 (by rfl) ⟨560600, by rfl⟩) R1121201
theorem R321623 : Reach 321623 := rs (se 1 (by rfl) ⟨241217, by rfl⟩) R482435
theorem R125047 : Reach 125047 := rs (se 1 (by rfl) ⟨93785, by rfl⟩) R187571
theorem R420041 : Reach 420041 := rs (se 2 (by rfl) ⟨157515, by rfl⟩) R315031
theorem R125191 : Reach 125191 := rs (se 1 (by rfl) ⟨93893, by rfl⟩) R187787
theorem R125327 : Reach 125327 := rs (se 1 (by rfl) ⟨93995, by rfl⟩) R187991
theorem R322109 : Reach 322109 := rs (se 3 (by rfl) ⟨60395, by rfl⟩) R120791
theorem R2779919 : Reach 2779919 := rs (se 1 (by rfl) ⟨2084939, by rfl⟩) R4169879
theorem R420623 : Reach 420623 := rs (se 1 (by rfl) ⟨315467, by rfl⟩) R630935
theorem R551717 : Reach 551717 := rs (se 4 (by rfl) ⟨51723, by rfl⟩) R103447
theorem R453529 : Reach 453529 := rs (se 2 (by rfl) ⟨170073, by rfl⟩) R340147
theorem R420983 : Reach 420983 := rs (se 1 (by rfl) ⟨315737, by rfl⟩) R631475
theorem R486809 : Reach 486809 := rs (se 2 (by rfl) ⟨182553, by rfl⟩) R365107
theorem R552491 : Reach 552491 := rs (se 1 (by rfl) ⟨414368, by rfl⟩) R828737
theorem R2420375 : Reach 2420375 := rs (se 1 (by rfl) ⟨1815281, by rfl⟩) R3630563
theorem R323513 : Reach 323513 := rs (se 2 (by rfl) ⟨121317, by rfl⟩) R242635
theorem R1339415 : Reach 1339415 := rs (se 1 (by rfl) ⟨1004561, by rfl⟩) R2009123
theorem R421955 : Reach 421955 := rs (se 1 (by rfl) ⟨316466, by rfl⟩) R632933
theorem R618785 : Reach 618785 := rs (se 2 (by rfl) ⟨232044, by rfl⟩) R464089
theorem R258391 : Reach 258391 := rs (se 1 (by rfl) ⟨193793, by rfl⟩) R387587
theorem R258419 : Reach 258419 := rs (se 1 (by rfl) ⟨193814, by rfl⟩) R387629
theorem R422297 : Reach 422297 := rs (se 2 (by rfl) ⟨158361, by rfl⟩) R316723
theorem R225737 : Reach 225737 := rs (se 2 (by rfl) ⟨84651, by rfl⟩) R169303
theorem R324107 : Reach 324107 := rs (se 1 (by rfl) ⟨243080, by rfl⟩) R486161
theorem R324215 : Reach 324215 := rs (se 1 (by rfl) ⟨243161, by rfl⟩) R486323
theorem R1372889 : Reach 1372889 := rs (se 2 (by rfl) ⟨514833, by rfl⟩) R1029667
theorem R160555 : Reach 160555 := rs (se 1 (by rfl) ⟨120416, by rfl⟩) R240833
theorem R291737 : Reach 291737 := rs (se 2 (by rfl) ⟨109401, by rfl⟩) R218803
theorem R160697 : Reach 160697 := rs (se 2 (by rfl) ⟨60261, by rfl⟩) R120523
theorem R95163 : Reach 95163 := rs (se 1 (by rfl) ⟨71372, by rfl⟩) R142745
theorem R553949 : Reach 553949 := rs (se 3 (by rfl) ⟨103865, by rfl⟩) R207731
theorem R95239 : Reach 95239 := rs (se 1 (by rfl) ⟨71429, by rfl⟩) R142859
theorem R95247 : Reach 95247 := rs (se 1 (by rfl) ⟨71435, by rfl⟩) R142871
theorem R95291 : Reach 95291 := rs (se 1 (by rfl) ⟨71468, by rfl⟩) R142937
theorem R95367 : Reach 95367 := rs (se 1 (by rfl) ⟨71525, by rfl⟩) R143051
theorem R95375 : Reach 95375 := rs (se 1 (by rfl) ⟨71531, by rfl⟩) R143063
theorem R95419 : Reach 95419 := rs (se 1 (by rfl) ⟨71564, by rfl⟩) R143129
theorem R324809 : Reach 324809 := rs (se 2 (by rfl) ⟨121803, by rfl⟩) R243607
theorem R95495 : Reach 95495 := rs (se 1 (by rfl) ⟨71621, by rfl⟩) R143243
theorem R95503 : Reach 95503 := rs (se 1 (by rfl) ⟨71627, by rfl⟩) R143255
theorem R95547 : Reach 95547 := rs (se 1 (by rfl) ⟨71660, by rfl⟩) R143321
theorem R95623 : Reach 95623 := rs (se 1 (by rfl) ⟨71717, by rfl⟩) R143435
theorem R95631 : Reach 95631 := rs (se 1 (by rfl) ⟨71723, by rfl⟩) R143447
theorem R95675 : Reach 95675 := rs (se 1 (by rfl) ⟨71756, by rfl⟩) R143513
theorem R95751 : Reach 95751 := rs (se 1 (by rfl) ⟨71813, by rfl⟩) R143627
theorem R95759 : Reach 95759 := rs (se 1 (by rfl) ⟨71819, by rfl⟩) R143639
theorem R95803 : Reach 95803 := rs (se 1 (by rfl) ⟨71852, by rfl⟩) R143705
theorem R161399 : Reach 161399 := rs (se 1 (by rfl) ⟨121049, by rfl⟩) R242099
theorem R194167 : Reach 194167 := rs (se 1 (by rfl) ⟨145625, by rfl⟩) R291251
theorem R95879 : Reach 95879 := rs (se 1 (by rfl) ⟨71909, by rfl⟩) R143819
theorem R95887 : Reach 95887 := rs (se 1 (by rfl) ⟨71915, by rfl⟩) R143831
theorem R3700403 : Reach 3700403 := rs (se 1 (by rfl) ⟨2775302, by rfl⟩) R5550605
theorem R95931 : Reach 95931 := rs (se 1 (by rfl) ⟨71948, by rfl⟩) R143897
theorem R96007 : Reach 96007 := rs (se 1 (by rfl) ⟨72005, by rfl⟩) R144011
theorem R96015 : Reach 96015 := rs (se 1 (by rfl) ⟨72011, by rfl⟩) R144023
theorem R96059 : Reach 96059 := rs (se 1 (by rfl) ⟨72044, by rfl⟩) R144089
theorem R96135 : Reach 96135 := rs (se 1 (by rfl) ⟨72101, by rfl⟩) R144203
theorem R325511 : Reach 325511 := rs (se 1 (by rfl) ⟨244133, by rfl⟩) R488267
theorem R96143 : Reach 96143 := rs (se 1 (by rfl) ⟨72107, by rfl⟩) R144215
theorem R587665 : Reach 587665 := rs (se 2 (by rfl) ⟨220374, by rfl⟩) R440749
theorem R489401 : Reach 489401 := rs (se 2 (by rfl) ⟨183525, by rfl⟩) R367051
theorem R96187 : Reach 96187 := rs (se 1 (by rfl) ⟨72140, by rfl⟩) R144281
theorem R96263 : Reach 96263 := rs (se 1 (by rfl) ⟨72197, by rfl⟩) R144395
theorem R96271 : Reach 96271 := rs (se 1 (by rfl) ⟨72203, by rfl⟩) R144407
theorem R161851 : Reach 161851 := rs (se 1 (by rfl) ⟨121388, by rfl⟩) R242777
theorem R96315 : Reach 96315 := rs (se 1 (by rfl) ⟨72236, by rfl⟩) R144473
theorem R96391 : Reach 96391 := rs (se 1 (by rfl) ⟨72293, by rfl⟩) R144587
theorem R96399 : Reach 96399 := rs (se 1 (by rfl) ⟨72299, by rfl⟩) R144599
theorem R1243309 : Reach 1243309 := rs (se 3 (by rfl) ⟨233120, by rfl⟩) R466241
theorem R96443 : Reach 96443 := rs (se 1 (by rfl) ⟨72332, by rfl⟩) R144665
theorem R161993 : Reach 161993 := rs (se 2 (by rfl) ⟨60747, by rfl⟩) R121495
theorem R325889 : Reach 325889 := rs (se 2 (by rfl) ⟨122208, by rfl⟩) R244417
theorem R96519 : Reach 96519 := rs (se 1 (by rfl) ⟨72389, by rfl⟩) R144779
theorem R96527 : Reach 96527 := rs (se 1 (by rfl) ⟨72395, by rfl⟩) R144791
theorem R1046843 : Reach 1046843 := rs (se 1 (by rfl) ⟨785132, by rfl⟩) R1570265
theorem R96571 : Reach 96571 := rs (se 1 (by rfl) ⟨72428, by rfl⟩) R144857
theorem R2128193 : Reach 2128193 := rs (se 2 (by rfl) ⟨798072, by rfl⟩) R1596145
theorem R96647 : Reach 96647 := rs (se 1 (by rfl) ⟨72485, by rfl⟩) R144971
theorem R96655 : Reach 96655 := rs (se 1 (by rfl) ⟨72491, by rfl⟩) R144983
theorem R96699 : Reach 96699 := rs (se 1 (by rfl) ⟨72524, by rfl⟩) R145049
theorem R96775 : Reach 96775 := rs (se 1 (by rfl) ⟨72581, by rfl⟩) R145163
theorem R96783 : Reach 96783 := rs (se 1 (by rfl) ⟨72587, by rfl⟩) R145175
theorem R96827 : Reach 96827 := rs (se 1 (by rfl) ⟨72620, by rfl⟩) R145241
theorem R96903 : Reach 96903 := rs (se 1 (by rfl) ⟨72677, by rfl⟩) R145355
theorem R96911 : Reach 96911 := rs (se 1 (by rfl) ⟨72683, by rfl⟩) R145367
theorem R96955 : Reach 96955 := rs (se 1 (by rfl) ⟨72716, by rfl⟩) R145433
theorem R424649 : Reach 424649 := rs (se 2 (by rfl) ⟨159243, by rfl⟩) R318487
theorem R97031 : Reach 97031 := rs (se 1 (by rfl) ⟨72773, by rfl⟩) R145547
theorem R97039 : Reach 97039 := rs (se 1 (by rfl) ⟨72779, by rfl⟩) R145559
theorem R97083 : Reach 97083 := rs (se 1 (by rfl) ⟨72812, by rfl⟩) R145625
theorem R523097 : Reach 523097 := rs (se 2 (by rfl) ⟨196161, by rfl⟩) R392323
theorem R162695 : Reach 162695 := rs (se 1 (by rfl) ⟨122021, by rfl⟩) R244043
theorem R97159 : Reach 97159 := rs (se 1 (by rfl) ⟨72869, by rfl⟩) R145739
theorem R97167 : Reach 97167 := rs (se 1 (by rfl) ⟨72875, by rfl⟩) R145751
theorem R97211 : Reach 97211 := rs (se 1 (by rfl) ⟨72908, by rfl⟩) R145817
theorem R97287 : Reach 97287 := rs (se 1 (by rfl) ⟨72965, by rfl⟩) R145931
theorem R97295 : Reach 97295 := rs (se 1 (by rfl) ⟨72971, by rfl⟩) R145943
theorem R326699 : Reach 326699 := rs (se 1 (by rfl) ⟨245024, by rfl⟩) R490049
theorem R97339 : Reach 97339 := rs (se 1 (by rfl) ⟨73004, by rfl⟩) R146009
theorem R97415 : Reach 97415 := rs (se 1 (by rfl) ⟨73061, by rfl⟩) R146123
theorem R97423 : Reach 97423 := rs (se 1 (by rfl) ⟨73067, by rfl⟩) R146135
theorem R97467 : Reach 97467 := rs (se 1 (by rfl) ⟨73100, by rfl⟩) R146201
theorem R490697 : Reach 490697 := rs (se 2 (by rfl) ⟨184011, by rfl⟩) R368023
theorem R97543 : Reach 97543 := rs (se 1 (by rfl) ⟨73157, by rfl⟩) R146315
theorem R97551 : Reach 97551 := rs (se 1 (by rfl) ⟨73163, by rfl⟩) R146327
theorem R97595 : Reach 97595 := rs (se 1 (by rfl) ⟨73196, by rfl⟩) R146393
theorem R97671 : Reach 97671 := rs (se 1 (by rfl) ⟨73253, by rfl⟩) R146507
theorem R97679 : Reach 97679 := rs (se 1 (by rfl) ⟨73259, by rfl⟩) R146519
theorem R458131 : Reach 458131 := rs (se 1 (by rfl) ⟨343598, by rfl⟩) R687197
theorem R97723 : Reach 97723 := rs (se 1 (by rfl) ⟨73292, by rfl⟩) R146585
theorem R97799 : Reach 97799 := rs (se 1 (by rfl) ⟨73349, by rfl⟩) R146699
theorem R163343 : Reach 163343 := rs (se 1 (by rfl) ⟨122507, by rfl⟩) R245015
theorem R97807 : Reach 97807 := rs (se 1 (by rfl) ⟨73355, by rfl⟩) R146711
theorem R97851 : Reach 97851 := rs (se 1 (by rfl) ⟨73388, by rfl⟩) R146777
theorem R97927 : Reach 97927 := rs (se 1 (by rfl) ⟨73445, by rfl⟩) R146891
theorem R97935 : Reach 97935 := rs (se 1 (by rfl) ⟨73451, by rfl⟩) R146903
theorem R97979 : Reach 97979 := rs (se 1 (by rfl) ⟨73484, by rfl⟩) R146969
theorem R98055 : Reach 98055 := rs (se 1 (by rfl) ⟨73541, by rfl⟩) R147083
theorem R98063 : Reach 98063 := rs (se 1 (by rfl) ⟨73547, by rfl⟩) R147095
theorem R98107 : Reach 98107 := rs (se 1 (by rfl) ⟨73580, by rfl⟩) R147161
theorem R98183 : Reach 98183 := rs (se 1 (by rfl) ⟨73637, by rfl⟩) R147275
theorem R98191 : Reach 98191 := rs (se 1 (by rfl) ⟨73643, by rfl⟩) R147287
theorem R524177 : Reach 524177 := rs (se 2 (by rfl) ⟨196566, by rfl⟩) R393133
theorem R98235 : Reach 98235 := rs (se 1 (by rfl) ⟨73676, by rfl⟩) R147353
theorem R163849 : Reach 163849 := rs (se 2 (by rfl) ⟨61443, by rfl⟩) R122887
theorem R98343 : Reach 98343 := rs (se 1 (by rfl) ⟨73757, by rfl⟩) R147515
theorem R1572941 : Reach 1572941 := rs (se 3 (by rfl) ⟨294926, by rfl⟩) R589853
theorem R98383 : Reach 98383 := rs (se 1 (by rfl) ⟨73787, by rfl⟩) R147575
theorem R98399 : Reach 98399 := rs (se 1 (by rfl) ⟨73799, by rfl⟩) R147599
theorem R98427 : Reach 98427 := rs (se 1 (by rfl) ⟨73820, by rfl⟩) R147641
theorem R327833 : Reach 327833 := rs (se 2 (by rfl) ⟨122937, by rfl⟩) R245875
theorem R229547 : Reach 229547 := rs (se 1 (by rfl) ⟨172160, by rfl⟩) R344321
theorem R164011 : Reach 164011 := rs (se 1 (by rfl) ⟨123008, by rfl⟩) R246017
theorem R98479 : Reach 98479 := rs (se 1 (by rfl) ⟨73859, by rfl⟩) R147719
theorem R98503 : Reach 98503 := rs (se 1 (by rfl) ⟨73877, by rfl⟩) R147755
theorem R98523 : Reach 98523 := rs (se 1 (by rfl) ⟨73892, by rfl⟩) R147785
theorem R98599 : Reach 98599 := rs (se 1 (by rfl) ⟨73949, by rfl⟩) R147899
theorem R98639 : Reach 98639 := rs (se 1 (by rfl) ⟨73979, by rfl⟩) R147959
theorem R98655 : Reach 98655 := rs (se 1 (by rfl) ⟨73991, by rfl⟩) R147983
theorem R98683 : Reach 98683 := rs (se 1 (by rfl) ⟨74012, by rfl⟩) R148025
theorem R262543 : Reach 262543 := rs (se 1 (by rfl) ⟨196907, by rfl⟩) R393815
theorem R98735 : Reach 98735 := rs (se 1 (by rfl) ⟨74051, by rfl⟩) R148103
theorem R98759 : Reach 98759 := rs (se 1 (by rfl) ⟨74069, by rfl⟩) R148139
theorem R164315 : Reach 164315 := rs (se 1 (by rfl) ⟨123236, by rfl⟩) R246473
theorem R98779 : Reach 98779 := rs (se 1 (by rfl) ⟨74084, by rfl⟩) R148169
theorem R557549 : Reach 557549 := rs (se 3 (by rfl) ⟨104540, by rfl⟩) R209081
theorem R98855 : Reach 98855 := rs (se 1 (by rfl) ⟨74141, by rfl⟩) R148283
theorem R98895 : Reach 98895 := rs (se 1 (by rfl) ⟨74171, by rfl⟩) R148343
theorem R98911 : Reach 98911 := rs (se 1 (by rfl) ⟨74183, by rfl⟩) R148367
theorem R98939 : Reach 98939 := rs (se 1 (by rfl) ⟨74204, by rfl⟩) R148409
theorem R98991 : Reach 98991 := rs (se 1 (by rfl) ⟨74243, by rfl⟩) R148487
theorem R164551 : Reach 164551 := rs (se 1 (by rfl) ⟨123413, by rfl⟩) R246827
theorem R99015 : Reach 99015 := rs (se 1 (by rfl) ⟨74261, by rfl⟩) R148523
theorem R99035 : Reach 99035 := rs (se 1 (by rfl) ⟨74276, by rfl⟩) R148553
theorem R1409795 : Reach 1409795 := rs (se 1 (by rfl) ⟨1057346, by rfl⟩) R2114693
theorem R492317 : Reach 492317 := rs (se 3 (by rfl) ⟨92309, by rfl⟩) R184619
theorem R99111 : Reach 99111 := rs (se 1 (by rfl) ⟨74333, by rfl⟩) R148667
theorem R164713 : Reach 164713 := rs (se 2 (by rfl) ⟨61767, by rfl⟩) R123535
theorem R590867 : Reach 590867 := rs (se 1 (by rfl) ⟨443150, by rfl⟩) R886301
theorem R5309489 : Reach 5309489 := rs (se 2 (by rfl) ⟨1991058, by rfl⟩) R3982117
theorem R329021 : Reach 329021 := rs (se 3 (by rfl) ⟨61691, by rfl⟩) R123383
theorem R165215 : Reach 165215 := rs (se 1 (by rfl) ⟨123911, by rfl⟩) R247823
theorem R296335 : Reach 296335 := rs (se 1 (by rfl) ⟨222251, by rfl⟩) R444503
theorem R165307 : Reach 165307 := rs (se 1 (by rfl) ⟨123980, by rfl⟩) R247961
theorem R624115 : Reach 624115 := rs (se 1 (by rfl) ⟨468086, by rfl⟩) R936173
theorem R362009 : Reach 362009 := rs (se 2 (by rfl) ⟨135753, by rfl⟩) R271507
theorem R624167 : Reach 624167 := rs (se 1 (by rfl) ⟨468125, by rfl⟩) R936251
theorem R165415 : Reach 165415 := rs (se 1 (by rfl) ⟨124061, by rfl⟩) R248123
theorem R263819 : Reach 263819 := rs (se 1 (by rfl) ⟨197864, by rfl⟩) R395729
theorem R722681 : Reach 722681 := rs (se 2 (by rfl) ⟨271005, by rfl⟩) R542011
theorem R132959 : Reach 132959 := rs (se 1 (by rfl) ⟨99719, by rfl⟩) R199439
theorem R165739 : Reach 165739 := rs (se 1 (by rfl) ⟨124304, by rfl⟩) R248609
theorem R329885 : Reach 329885 := rs (se 3 (by rfl) ⟨61853, by rfl⟩) R123707
theorem R330425 : Reach 330425 := rs (se 2 (by rfl) ⟨123909, by rfl⟩) R247819
theorem R166799 : Reach 166799 := rs (se 1 (by rfl) ⟨125099, by rfl⟩) R250199
theorem R363635 : Reach 363635 := rs (se 1 (by rfl) ⟨272726, by rfl⟩) R545453
theorem R167035 : Reach 167035 := rs (se 1 (by rfl) ⟨125276, by rfl⟩) R250553
theorem R724139 : Reach 724139 := rs (se 1 (by rfl) ⟨543104, by rfl⟩) R1086209
theorem R265463 : Reach 265463 := rs (se 1 (by rfl) ⟨199097, by rfl⟩) R398195
theorem R331019 : Reach 331019 := rs (se 1 (by rfl) ⟨248264, by rfl⟩) R496529
theorem R331289 : Reach 331289 := rs (se 2 (by rfl) ⟨124233, by rfl⟩) R248467
theorem R724625 : Reach 724625 := rs (se 2 (by rfl) ⟨271734, by rfl⟩) R543469
theorem R331627 : Reach 331627 := rs (se 1 (by rfl) ⟨248720, by rfl⟩) R497441
theorem R200761 : Reach 200761 := rs (se 2 (by rfl) ⟨75285, by rfl⟩) R150571
theorem R1118285 : Reach 1118285 := rs (se 3 (by rfl) ⟨209678, by rfl⟩) R419357
theorem R1052939 : Reach 1052939 := rs (se 1 (by rfl) ⟨789704, by rfl⟩) R1579409
theorem R364925 : Reach 364925 := rs (se 3 (by rfl) ⟨68423, by rfl⟩) R136847
theorem R332423 : Reach 332423 := rs (se 1 (by rfl) ⟨249317, by rfl⟩) R498635
theorem R332477 : Reach 332477 := rs (se 3 (by rfl) ⟨62339, by rfl⟩) R124679
theorem R561923 : Reach 561923 := rs (se 1 (by rfl) ⟨421442, by rfl⟩) R842885
theorem R332639 : Reach 332639 := rs (se 1 (by rfl) ⟨249479, by rfl⟩) R498959
theorem R627601 : Reach 627601 := rs (se 2 (by rfl) ⟨235350, by rfl⟩) R470701
theorem R889775 : Reach 889775 := rs (se 1 (by rfl) ⟨667331, by rfl⟩) R1334663
theorem R103343 : Reach 103343 := rs (se 1 (by rfl) ⟨77507, by rfl⟩) R155015
theorem R332801 : Reach 332801 := rs (se 2 (by rfl) ⟨124800, by rfl⟩) R249601
theorem R496691 : Reach 496691 := rs (se 1 (by rfl) ⟨372518, by rfl⟩) R745037
theorem R726083 : Reach 726083 := rs (se 1 (by rfl) ⟨544562, by rfl⟩) R1089125
theorem R562423 : Reach 562423 := rs (se 1 (by rfl) ⟨421817, by rfl⟩) R843635
theorem R824741 : Reach 824741 := rs (se 4 (by rfl) ⟨77319, by rfl⟩) R154639
theorem R333611 : Reach 333611 := rs (se 1 (by rfl) ⟨250208, by rfl⟩) R500417
theorem R137143 : Reach 137143 := rs (se 1 (by rfl) ⟨102857, by rfl⟩) R205715
theorem R727055 : Reach 727055 := rs (se 1 (by rfl) ⟨545291, by rfl⟩) R1090583
theorem R333881 : Reach 333881 := rs (se 2 (by rfl) ⟨125205, by rfl⟩) R250411
theorem R366839 : Reach 366839 := rs (se 1 (by rfl) ⟨275129, by rfl⟩) R550259
theorem R334205 : Reach 334205 := rs (se 3 (by rfl) ⟨62663, by rfl⟩) R125327
theorem R1874501 : Reach 1874501 := rs (se 4 (by rfl) ⟨175734, by rfl⟩) R351469
theorem R498311 : Reach 498311 := rs (se 1 (by rfl) ⟨373733, by rfl⟩) R747467
theorem R334475 : Reach 334475 := rs (se 1 (by rfl) ⟨250856, by rfl⟩) R501713
theorem R793273 : Reach 793273 := rs (se 2 (by rfl) ⟨297477, by rfl⟩) R594955
theorem R367811 : Reach 367811 := rs (se 1 (by rfl) ⟨275858, by rfl⟩) R551717
theorem R138601 : Reach 138601 := rs (se 2 (by rfl) ⟨51975, by rfl⟩) R103951
theorem R532007 : Reach 532007 := rs (se 1 (by rfl) ⟨399005, by rfl⟩) R798011
theorem R1842821 : Reach 1842821 := rs (se 4 (by rfl) ⟨172764, by rfl⟩) R345529
theorem R269963 : Reach 269963 := rs (se 1 (by rfl) ⟨202472, by rfl⟩) R404945
theorem R368327 : Reach 368327 := rs (se 1 (by rfl) ⟨276245, by rfl⟩) R552491
theorem R892943 : Reach 892943 := rs (se 1 (by rfl) ⟨669707, by rfl⟩) R1339415
theorem R499769 : Reach 499769 := rs (se 2 (by rfl) ⟨187413, by rfl⟩) R374827
theorem R794701 : Reach 794701 := rs (se 3 (by rfl) ⟨149006, by rfl⟩) R298013
theorem R172279 : Reach 172279 := rs (se 1 (by rfl) ⟨129209, by rfl⟩) R258419
theorem R107131 : Reach 107131 := rs (se 1 (by rfl) ⟨80348, by rfl⟩) R160697
theorem R369299 : Reach 369299 := rs (se 1 (by rfl) ⟨276974, by rfl⟩) R553949
theorem R271097 : Reach 271097 := rs (se 2 (by rfl) ⟨101661, by rfl⟩) R203323
theorem R369481 : Reach 369481 := rs (se 2 (by rfl) ⟨138555, by rfl⟩) R277111
theorem R271279 : Reach 271279 := rs (se 1 (by rfl) ⟨203459, by rfl⟩) R406919
theorem R107599 : Reach 107599 := rs (se 1 (by rfl) ⟨80699, by rfl⟩) R161399
theorem R2466935 : Reach 2466935 := rs (se 1 (by rfl) ⟨1850201, by rfl⟩) R3700403
theorem R631961 : Reach 631961 := rs (se 2 (by rfl) ⟨236985, by rfl⟩) R473971
theorem R730457 : Reach 730457 := rs (se 2 (by rfl) ⟨273921, by rfl⟩) R547843
theorem R107995 : Reach 107995 := rs (se 1 (by rfl) ⟨80996, by rfl⟩) R161993
theorem R697895 : Reach 697895 := rs (se 1 (by rfl) ⟨523421, by rfl⟩) R1046843
theorem R1418795 : Reach 1418795 := rs (se 1 (by rfl) ⟨1064096, by rfl⟩) R2128193
theorem R206459 : Reach 206459 := rs (se 1 (by rfl) ⟨154844, by rfl⟩) R309689
theorem R108463 : Reach 108463 := rs (se 1 (by rfl) ⟨81347, by rfl⟩) R162695
theorem R272555 : Reach 272555 := rs (se 1 (by rfl) ⟨204416, by rfl⟩) R408833
theorem R108895 : Reach 108895 := rs (se 1 (by rfl) ⟨81671, by rfl⟩) R163343
theorem R272783 : Reach 272783 := rs (se 1 (by rfl) ⟨204587, by rfl⟩) R409175
theorem R109255 : Reach 109255 := rs (se 1 (by rfl) ⟨81941, by rfl⟩) R163883
theorem R371411 : Reach 371411 := rs (se 1 (by rfl) ⟨278558, by rfl⟩) R557117
theorem R1551251 : Reach 1551251 := rs (se 1 (by rfl) ⟨1163438, by rfl⟩) R2326877
theorem R535747 : Reach 535747 := rs (se 1 (by rfl) ⟨401810, by rfl⟩) R803621
theorem R666917 : Reach 666917 := rs (se 4 (by rfl) ⟨62523, by rfl⟩) R125047
theorem R142697 : Reach 142697 := rs (se 2 (by rfl) ⟨53511, by rfl⟩) R107023
theorem R306575 : Reach 306575 := rs (se 1 (by rfl) ⟨229931, by rfl⟩) R459863
theorem R142775 : Reach 142775 := rs (se 1 (by rfl) ⟨107081, by rfl⟩) R214163
theorem R142811 : Reach 142811 := rs (se 1 (by rfl) ⟨107108, by rfl⟩) R214217
theorem R241177 : Reach 241177 := rs (se 2 (by rfl) ⟨90441, by rfl⟩) R180883
theorem R110119 : Reach 110119 := rs (se 1 (by rfl) ⟨82589, by rfl⟩) R165179
theorem R732887 : Reach 732887 := rs (se 1 (by rfl) ⟨549665, by rfl⟩) R1099331
theorem R241481 : Reach 241481 := rs (se 2 (by rfl) ⟨90555, by rfl⟩) R181111
theorem R143279 : Reach 143279 := rs (se 1 (by rfl) ⟨107459, by rfl⟩) R214919
theorem R143369 : Reach 143369 := rs (se 2 (by rfl) ⟨53763, by rfl⟩) R107527
theorem R667685 : Reach 667685 := rs (se 4 (by rfl) ⟨62595, by rfl⟩) R125191
theorem R143399 : Reach 143399 := rs (se 1 (by rfl) ⟨107549, by rfl⟩) R215099
theorem R143483 : Reach 143483 := rs (se 1 (by rfl) ⟨107612, by rfl⟩) R215225
theorem R143609 : Reach 143609 := rs (se 2 (by rfl) ⟨53853, by rfl⟩) R107707
theorem R143711 : Reach 143711 := rs (se 1 (by rfl) ⟨107783, by rfl⟩) R215567
theorem R143723 : Reach 143723 := rs (se 1 (by rfl) ⟨107792, by rfl⟩) R215585
theorem R143951 : Reach 143951 := rs (se 1 (by rfl) ⟨107963, by rfl⟩) R215927
theorem R144071 : Reach 144071 := rs (se 1 (by rfl) ⟨108053, by rfl⟩) R216107
theorem R144233 : Reach 144233 := rs (se 2 (by rfl) ⟨54087, by rfl⟩) R108175
theorem R308087 : Reach 308087 := rs (se 1 (by rfl) ⟨231065, by rfl⟩) R462131
theorem R1258415 : Reach 1258415 := rs (se 1 (by rfl) ⟨943811, by rfl⟩) R1887623
theorem R242615 : Reach 242615 := rs (se 1 (by rfl) ⟨181961, by rfl⟩) R363923
theorem R144311 : Reach 144311 := rs (se 1 (by rfl) ⟨108233, by rfl⟩) R216467
theorem R144347 : Reach 144347 := rs (se 1 (by rfl) ⟨108260, by rfl⟩) R216521
theorem R373841 : Reach 373841 := rs (se 2 (by rfl) ⟨140190, by rfl⟩) R280381
theorem R374159 : Reach 374159 := rs (se 1 (by rfl) ⟨280619, by rfl⟩) R561239
theorem R144815 : Reach 144815 := rs (se 1 (by rfl) ⟨108611, by rfl⟩) R217223
theorem R144905 : Reach 144905 := rs (se 2 (by rfl) ⟨54339, by rfl⟩) R108679
theorem R276007 : Reach 276007 := rs (se 1 (by rfl) ⟨207005, by rfl⟩) R414011
theorem R144935 : Reach 144935 := rs (se 1 (by rfl) ⟨108701, by rfl⟩) R217403
theorem R145019 : Reach 145019 := rs (se 1 (by rfl) ⟨108764, by rfl⟩) R217529
theorem R145145 : Reach 145145 := rs (se 2 (by rfl) ⟨54429, by rfl⟩) R108859
theorem R309035 : Reach 309035 := rs (se 1 (by rfl) ⟨231776, by rfl⟩) R463553
theorem R145247 : Reach 145247 := rs (se 1 (by rfl) ⟨108935, by rfl⟩) R217871
theorem R145259 : Reach 145259 := rs (se 1 (by rfl) ⟨108944, by rfl⟩) R217889
theorem R833489 : Reach 833489 := rs (se 2 (by rfl) ⟨312558, by rfl⟩) R625117
theorem R243719 : Reach 243719 := rs (se 1 (by rfl) ⟨182789, by rfl⟩) R365579
theorem R243769 : Reach 243769 := rs (se 2 (by rfl) ⟨91413, by rfl⟩) R182827
theorem R145487 : Reach 145487 := rs (se 1 (by rfl) ⟨109115, by rfl⟩) R218231
theorem R145607 : Reach 145607 := rs (se 1 (by rfl) ⟨109205, by rfl⟩) R218411
theorem R375101 : Reach 375101 := rs (se 3 (by rfl) ⟨70331, by rfl⟩) R140663
theorem R145769 : Reach 145769 := rs (se 2 (by rfl) ⟨54663, by rfl⟩) R109327
theorem R244073 : Reach 244073 := rs (se 2 (by rfl) ⟨91527, by rfl⟩) R183055
theorem R145847 : Reach 145847 := rs (se 1 (by rfl) ⟨109385, by rfl⟩) R218771
theorem R145883 : Reach 145883 := rs (se 1 (by rfl) ⟨109412, by rfl⟩) R218825
theorem R604705 : Reach 604705 := rs (se 2 (by rfl) ⟨226764, by rfl⟩) R453529
theorem R735803 : Reach 735803 := rs (se 1 (by rfl) ⟨551852, by rfl⟩) R1103705
theorem R932755 : Reach 932755 := rs (se 1 (by rfl) ⟨699566, by rfl⟩) R1399133
theorem R146351 : Reach 146351 := rs (se 1 (by rfl) ⟨109763, by rfl⟩) R219527
theorem R146441 : Reach 146441 := rs (se 2 (by rfl) ⟨54915, by rfl⟩) R109831
theorem R146471 : Reach 146471 := rs (se 1 (by rfl) ⟨109853, by rfl⟩) R219707
theorem R146555 : Reach 146555 := rs (se 1 (by rfl) ⟨109916, by rfl⟩) R219833
theorem R1424557 : Reach 1424557 := rs (se 3 (by rfl) ⟨267104, by rfl⟩) R534209
theorem R146681 : Reach 146681 := rs (se 2 (by rfl) ⟨55005, by rfl⟩) R110011
theorem R1719575 : Reach 1719575 := rs (se 1 (by rfl) ⟨1289681, by rfl⟩) R2579363
theorem R146783 : Reach 146783 := rs (se 1 (by rfl) ⟨110087, by rfl⟩) R220175
theorem R146795 : Reach 146795 := rs (se 1 (by rfl) ⟨110096, by rfl⟩) R220193
theorem R310817 : Reach 310817 := rs (se 2 (by rfl) ⟨116556, by rfl⟩) R233113
theorem R1195559 : Reach 1195559 := rs (se 1 (by rfl) ⟨896669, by rfl⟩) R1793339
theorem R147023 : Reach 147023 := rs (se 1 (by rfl) ⟨110267, by rfl⟩) R220535
theorem R704123 : Reach 704123 := rs (se 1 (by rfl) ⟨528092, by rfl⟩) R1056185
theorem R310931 : Reach 310931 := rs (se 1 (by rfl) ⟨233198, by rfl⟩) R466397
theorem R147143 : Reach 147143 := rs (se 1 (by rfl) ⟨110357, by rfl⟩) R220715
theorem R311033 : Reach 311033 := rs (se 2 (by rfl) ⟨116637, by rfl⟩) R233275
theorem R147305 : Reach 147305 := rs (se 2 (by rfl) ⟨55239, by rfl⟩) R110479
theorem R147383 : Reach 147383 := rs (se 1 (by rfl) ⟨110537, by rfl⟩) R221075
theorem R147419 : Reach 147419 := rs (se 1 (by rfl) ⟨110564, by rfl⟩) R221129
theorem R180473 : Reach 180473 := rs (se 2 (by rfl) ⟨67677, by rfl⟩) R135355
theorem R3916097 : Reach 3916097 := rs (se 2 (by rfl) ⟨1468536, by rfl⟩) R2937073
theorem R344407 : Reach 344407 := rs (se 1 (by rfl) ⟨258305, by rfl⟩) R516611
theorem R409961 : Reach 409961 := rs (se 2 (by rfl) ⟨153735, by rfl⟩) R307471
theorem R147887 : Reach 147887 := rs (se 1 (by rfl) ⟨110915, by rfl⟩) R221831
theorem R344521 : Reach 344521 := rs (se 2 (by rfl) ⟨129195, by rfl⟩) R258391
theorem R147977 : Reach 147977 := rs (se 2 (by rfl) ⟨55491, by rfl⟩) R110983
theorem R246311 : Reach 246311 := rs (se 1 (by rfl) ⟨184733, by rfl⟩) R369467
theorem R148007 : Reach 148007 := rs (se 1 (by rfl) ⟨111005, by rfl⟩) R222011
theorem R148091 : Reach 148091 := rs (se 1 (by rfl) ⟨111068, by rfl⟩) R222137
theorem R312007 : Reach 312007 := rs (se 1 (by rfl) ⟨234005, by rfl⟩) R468011
theorem R148217 : Reach 148217 := rs (se 2 (by rfl) ⟨55581, by rfl⟩) R111163
theorem R148319 : Reach 148319 := rs (se 1 (by rfl) ⟨111239, by rfl⟩) R222479
theorem R246635 : Reach 246635 := rs (se 1 (by rfl) ⟨184976, by rfl⟩) R369953
theorem R148331 : Reach 148331 := rs (se 1 (by rfl) ⟨111248, by rfl⟩) R222497
theorem R836527 : Reach 836527 := rs (se 1 (by rfl) ⟨627395, by rfl⟩) R1254791
theorem R214073 : Reach 214073 := rs (se 2 (by rfl) ⟨80277, by rfl⟩) R160555
theorem R148559 : Reach 148559 := rs (se 1 (by rfl) ⟨111419, by rfl⟩) R222839
theorem R148679 : Reach 148679 := rs (se 1 (by rfl) ⟨111509, by rfl⟩) R223019
theorem R214415 : Reach 214415 := rs (se 1 (by rfl) ⟨160811, by rfl⟩) R321623
theorem R280027 : Reach 280027 := rs (se 1 (by rfl) ⟨210020, by rfl⟩) R420041
theorem R247283 : Reach 247283 := rs (se 1 (by rfl) ⟨185462, by rfl⟩) R370925
theorem R280073 : Reach 280073 := rs (se 2 (by rfl) ⟨105027, by rfl⟩) R210055
theorem R247495 : Reach 247495 := rs (se 1 (by rfl) ⟨185621, by rfl⟩) R371243
theorem R214739 : Reach 214739 := rs (se 1 (by rfl) ⟨161054, by rfl⟩) R322109
theorem R1230551 : Reach 1230551 := rs (se 1 (by rfl) ⟨922913, by rfl⟩) R1845827
theorem R1853279 : Reach 1853279 := rs (se 1 (by rfl) ⟨1389959, by rfl⟩) R2779919
theorem R280415 : Reach 280415 := rs (se 1 (by rfl) ⟨210311, by rfl⟩) R420623
theorem R837485 : Reach 837485 := rs (se 3 (by rfl) ⟨157028, by rfl⟩) R314057
theorem R182159 : Reach 182159 := rs (se 1 (by rfl) ⟨136619, by rfl⟩) R273239
theorem R280655 : Reach 280655 := rs (se 1 (by rfl) ⟨210491, by rfl⟩) R420983
theorem R936481 : Reach 936481 := rs (se 2 (by rfl) ⟨351180, by rfl⟩) R702361
theorem R248417 : Reach 248417 := rs (se 2 (by rfl) ⟨93156, by rfl⟩) R186313
theorem R215675 : Reach 215675 := rs (se 1 (by rfl) ⟨161756, by rfl⟩) R323513
theorem R281303 : Reach 281303 := rs (se 1 (by rfl) ⟨210977, by rfl⟩) R421955
theorem R215801 : Reach 215801 := rs (se 2 (by rfl) ⟨80925, by rfl⟩) R161851
theorem R412523 : Reach 412523 := rs (se 1 (by rfl) ⟨309392, by rfl⟩) R618785
theorem R1657745 : Reach 1657745 := rs (se 2 (by rfl) ⟨621654, by rfl⟩) R1243309
theorem R183215 : Reach 183215 := rs (se 1 (by rfl) ⟨137411, by rfl⟩) R274823
theorem R281531 : Reach 281531 := rs (se 1 (by rfl) ⟨211148, by rfl⟩) R422297
theorem R150491 : Reach 150491 := rs (se 1 (by rfl) ⟨112868, by rfl⟩) R225737
theorem R216071 : Reach 216071 := rs (se 1 (by rfl) ⟨162053, by rfl⟩) R324107
theorem R281657 : Reach 281657 := rs (se 2 (by rfl) ⟨105621, by rfl⟩) R211243
theorem R216143 : Reach 216143 := rs (se 1 (by rfl) ⟨162107, by rfl⟩) R324215
theorem R183647 : Reach 183647 := rs (se 1 (by rfl) ⟨137735, by rfl⟩) R275471
theorem R216539 : Reach 216539 := rs (se 1 (by rfl) ⟨162404, by rfl⟩) R324809
theorem R315019 : Reach 315019 := rs (se 1 (by rfl) ⟨236264, by rfl⟩) R472529
theorem R413549 : Reach 413549 := rs (se 3 (by rfl) ⟨77540, by rfl⟩) R155081
theorem R217007 : Reach 217007 := rs (se 1 (by rfl) ⟨162755, by rfl⟩) R325511
theorem R249875 : Reach 249875 := rs (se 1 (by rfl) ⟨187406, by rfl⟩) R374813
theorem R217259 : Reach 217259 := rs (se 1 (by rfl) ⟨162944, by rfl⟩) R325889
theorem R4837637 : Reach 4837637 := rs (se 4 (by rfl) ⟨453528, by rfl⟩) R907057
theorem R283099 : Reach 283099 := rs (se 1 (by rfl) ⟨212324, by rfl⟩) R424649
theorem R610841 : Reach 610841 := rs (se 2 (by rfl) ⟨229065, by rfl⟩) R458131
theorem R414233 : Reach 414233 := rs (se 2 (by rfl) ⟨155337, by rfl⟩) R310675
theorem R348731 : Reach 348731 := rs (se 1 (by rfl) ⟨261548, by rfl⟩) R523097
theorem R217799 : Reach 217799 := rs (se 1 (by rfl) ⟨163349, by rfl⟩) R326699
theorem R3134213 : Reach 3134213 := rs (se 4 (by rfl) ⟨293832, by rfl⟩) R587665
theorem R1692737 : Reach 1692737 := rs (se 2 (by rfl) ⟨634776, by rfl⟩) R1269553
theorem R185591 : Reach 185591 := rs (se 1 (by rfl) ⟨139193, by rfl⟩) R278387
theorem R349451 : Reach 349451 := rs (se 1 (by rfl) ⟨262088, by rfl⟩) R524177
theorem R185743 : Reach 185743 := rs (se 1 (by rfl) ⟨139307, by rfl⟩) R278615
theorem R218663 : Reach 218663 := rs (se 1 (by rfl) ⟨163997, by rfl⟩) R327995
theorem R1037971 : Reach 1037971 := rs (se 1 (by rfl) ⟨778478, by rfl⟩) R1556957
theorem R186185 : Reach 186185 := rs (se 2 (by rfl) ⟨69819, by rfl⟩) R139639
theorem R218987 : Reach 218987 := rs (se 1 (by rfl) ⟨164240, by rfl⟩) R328481
theorem R219041 : Reach 219041 := rs (se 2 (by rfl) ⟨82140, by rfl⟩) R164281
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R219383 : Reach 219383 := rs (se 1 (by rfl) ⟨164537, by rfl⟩) R329075
theorem R186617 : Reach 186617 := rs (se 2 (by rfl) ⟨69981, by rfl⟩) R139963
theorem R186799 : Reach 186799 := rs (se 1 (by rfl) ⟨140099, by rfl⟩) R280199
theorem R154235 : Reach 154235 := rs (se 1 (by rfl) ⟨115676, by rfl⟩) R231353
theorem R219977 : Reach 219977 := rs (se 2 (by rfl) ⟨82491, by rfl⟩) R164983
theorem R154543 : Reach 154543 := rs (se 1 (by rfl) ⟨115907, by rfl⟩) R231815
theorem R121819 : Reach 121819 := rs (se 1 (by rfl) ⟨91364, by rfl⟩) R182729
theorem R253007 : Reach 253007 := rs (se 1 (by rfl) ⟨189755, by rfl⟩) R379511
theorem R3661037 : Reach 3661037 := rs (se 3 (by rfl) ⟨686444, by rfl⟩) R1372889
theorem R1236545 : Reach 1236545 := rs (se 2 (by rfl) ⟨463704, by rfl⟩) R927409
theorem R220769 : Reach 220769 := rs (se 2 (by rfl) ⟨82788, by rfl⟩) R165577
theorem R188075 : Reach 188075 := rs (se 1 (by rfl) ⟨141056, by rfl⟩) R282113
theorem R221111 : Reach 221111 := rs (se 1 (by rfl) ⟨165833, by rfl⟩) R331667
theorem R548801 : Reach 548801 := rs (se 2 (by rfl) ⟨205800, by rfl⟩) R411601
theorem R155819 : Reach 155819 := rs (se 1 (by rfl) ⟨116864, by rfl⟩) R233729
theorem R221705 : Reach 221705 := rs (se 2 (by rfl) ⟨83139, by rfl⟩) R166279
theorem R746009 : Reach 746009 := rs (se 2 (by rfl) ⟨279753, by rfl⟩) R559507
theorem R222047 : Reach 222047 := rs (se 1 (by rfl) ⟨166535, by rfl⟩) R333071
theorem R222227 : Reach 222227 := rs (se 1 (by rfl) ⟨166670, by rfl⟩) R333341
theorem R222569 : Reach 222569 := rs (se 2 (by rfl) ⟨83463, by rfl⟩) R166927
theorem R1598939 : Reach 1598939 := rs (se 1 (by rfl) ⟨1199204, by rfl⟩) R2398409
theorem R845275 : Reach 845275 := rs (se 1 (by rfl) ⟨633956, by rfl⟩) R1267913
theorem R321083 : Reach 321083 := rs (se 1 (by rfl) ⟨240812, by rfl⟩) R481625
theorem R321353 : Reach 321353 := rs (se 2 (by rfl) ⟨120507, by rfl⟩) R241015
theorem R846233 : Reach 846233 := rs (se 2 (by rfl) ⟨317337, by rfl⟩) R634675
theorem R4025123 : Reach 4025123 := rs (se 1 (by rfl) ⟨3018842, by rfl⟩) R6037685
theorem R158537 : Reach 158537 := rs (se 2 (by rfl) ⟨59451, by rfl⟩) R118903
theorem R682897 : Reach 682897 := rs (se 2 (by rfl) ⟨256086, by rfl⟩) R512173
theorem R322487 : Reach 322487 := rs (se 1 (by rfl) ⟨241865, by rfl⟩) R483731
theorem R486647 : Reach 486647 := rs (se 1 (by rfl) ⟨364985, by rfl⟩) R729971
theorem R748925 : Reach 748925 := rs (se 3 (by rfl) ⟨140423, by rfl⟩) R280847
theorem R5074319 : Reach 5074319 := rs (se 1 (by rfl) ⟨3805739, by rfl⟩) R7611479
theorem R19131875 : Reach 19131875 := rs (se 1 (by rfl) ⟨14348906, by rfl⟩) R28697813
theorem R323081 : Reach 323081 := rs (se 2 (by rfl) ⟨121155, by rfl⟩) R242311
theorem R487133 : Reach 487133 := rs (se 3 (by rfl) ⟨91337, by rfl⟩) R182675
theorem R17592227 : Reach 17592227 := rs (se 1 (by rfl) ⟨13194170, by rfl⟩) R26388341
theorem R618839 : Reach 618839 := rs (se 1 (by rfl) ⟨464129, by rfl⟩) R928259
theorem R323945 : Reach 323945 := rs (se 2 (by rfl) ⟨121479, by rfl⟩) R242959
theorem R193121 : Reach 193121 := rs (se 2 (by rfl) ⟨72420, by rfl⟩) R144841
theorem R225931 : Reach 225931 := rs (se 1 (by rfl) ⟨169448, by rfl⟩) R338897
theorem R258889 : Reach 258889 := rs (se 2 (by rfl) ⟨97083, by rfl⟩) R194167
theorem R95151 : Reach 95151 := rs (se 1 (by rfl) ⟨71363, by rfl⟩) R142727
theorem R324539 : Reach 324539 := rs (se 1 (by rfl) ⟨243404, by rfl⟩) R486809
theorem R95175 : Reach 95175 := rs (se 1 (by rfl) ⟨71381, by rfl⟩) R142763
theorem R95195 : Reach 95195 := rs (se 1 (by rfl) ⟨71396, by rfl⟩) R142793
theorem R95271 : Reach 95271 := rs (se 1 (by rfl) ⟨71453, by rfl⟩) R142907
theorem R160825 : Reach 160825 := rs (se 2 (by rfl) ⟨60309, by rfl⟩) R120619
theorem R95311 : Reach 95311 := rs (se 1 (by rfl) ⟨71483, by rfl⟩) R142967
theorem R95327 : Reach 95327 := rs (se 1 (by rfl) ⟨71495, by rfl⟩) R142991
theorem R95355 : Reach 95355 := rs (se 1 (by rfl) ⟨71516, by rfl⟩) R143033
theorem R1406105 : Reach 1406105 := rs (se 2 (by rfl) ⟨527289, by rfl⟩) R1054579
theorem R423083 : Reach 423083 := rs (se 1 (by rfl) ⟨317312, by rfl⟩) R634625
theorem R95407 : Reach 95407 := rs (se 1 (by rfl) ⟨71555, by rfl⟩) R143111
theorem R160967 : Reach 160967 := rs (se 1 (by rfl) ⟨120725, by rfl⟩) R241451
theorem R95431 : Reach 95431 := rs (se 1 (by rfl) ⟨71573, by rfl⟩) R143147
theorem R95451 : Reach 95451 := rs (se 1 (by rfl) ⟨71588, by rfl⟩) R143177
theorem R95527 : Reach 95527 := rs (se 1 (by rfl) ⟨71645, by rfl⟩) R143291
theorem R95567 : Reach 95567 := rs (se 1 (by rfl) ⟨71675, by rfl⟩) R143351
theorem R95583 : Reach 95583 := rs (se 1 (by rfl) ⟨71687, by rfl⟩) R143375
theorem R161129 : Reach 161129 := rs (se 2 (by rfl) ⟨60423, by rfl⟩) R120847
theorem R95611 : Reach 95611 := rs (se 1 (by rfl) ⟨71708, by rfl⟩) R143417
theorem R1340837 : Reach 1340837 := rs (se 4 (by rfl) ⟨125703, by rfl⟩) R251407
theorem R95663 : Reach 95663 := rs (se 1 (by rfl) ⟨71747, by rfl⟩) R143495
theorem R95687 : Reach 95687 := rs (se 1 (by rfl) ⟨71765, by rfl⟩) R143531
theorem R95707 : Reach 95707 := rs (se 1 (by rfl) ⟨71780, by rfl⟩) R143561
theorem R95783 : Reach 95783 := rs (se 1 (by rfl) ⟨71837, by rfl⟩) R143675
theorem R95823 : Reach 95823 := rs (se 1 (by rfl) ⟨71867, by rfl⟩) R143735
theorem R95839 : Reach 95839 := rs (se 1 (by rfl) ⟨71879, by rfl⟩) R143759
theorem R95867 : Reach 95867 := rs (se 1 (by rfl) ⟨71900, by rfl⟩) R143801
theorem R95919 : Reach 95919 := rs (se 1 (by rfl) ⟨71939, by rfl⟩) R143879
theorem R95943 : Reach 95943 := rs (se 1 (by rfl) ⟨71957, by rfl⟩) R143915
theorem R95963 : Reach 95963 := rs (se 1 (by rfl) ⟨71972, by rfl⟩) R143945
theorem R161527 : Reach 161527 := rs (se 1 (by rfl) ⟨121145, by rfl⟩) R242291
theorem R96039 : Reach 96039 := rs (se 1 (by rfl) ⟨72029, by rfl⟩) R144059
theorem R358187 : Reach 358187 := rs (se 1 (by rfl) ⟨268640, by rfl⟩) R537281
theorem R96079 : Reach 96079 := rs (se 1 (by rfl) ⟨72059, by rfl⟩) R144119
theorem R96095 : Reach 96095 := rs (se 1 (by rfl) ⟨72071, by rfl⟩) R144143
theorem R96123 : Reach 96123 := rs (se 1 (by rfl) ⟨72092, by rfl⟩) R144185
theorem R96175 : Reach 96175 := rs (se 1 (by rfl) ⟨72131, by rfl⟩) R144263
theorem R161723 : Reach 161723 := rs (se 1 (by rfl) ⟨121292, by rfl⟩) R242585
theorem R194491 : Reach 194491 := rs (se 1 (by rfl) ⟨145868, by rfl⟩) R291737
theorem R96199 : Reach 96199 := rs (se 1 (by rfl) ⟨72149, by rfl⟩) R144299
theorem R96219 : Reach 96219 := rs (se 1 (by rfl) ⟨72164, by rfl⟩) R144329
theorem R161831 : Reach 161831 := rs (se 1 (by rfl) ⟨121373, by rfl⟩) R242747
theorem R96295 : Reach 96295 := rs (se 1 (by rfl) ⟨72221, by rfl⟩) R144443
theorem R96335 : Reach 96335 := rs (se 1 (by rfl) ⟨72251, by rfl⟩) R144503
theorem R96351 : Reach 96351 := rs (se 1 (by rfl) ⟨72263, by rfl⟩) R144527
theorem R96379 : Reach 96379 := rs (se 1 (by rfl) ⟨72284, by rfl⟩) R144569
theorem R96431 : Reach 96431 := rs (se 1 (by rfl) ⟨72323, by rfl⟩) R144647
theorem R96455 : Reach 96455 := rs (se 1 (by rfl) ⟨72341, by rfl⟩) R144683
theorem R96475 : Reach 96475 := rs (se 1 (by rfl) ⟨72356, by rfl⟩) R144713
theorem R96551 : Reach 96551 := rs (se 1 (by rfl) ⟨72413, by rfl⟩) R144827
theorem R162121 : Reach 162121 := rs (se 2 (by rfl) ⟨60795, by rfl⟩) R121591
theorem R96591 : Reach 96591 := rs (se 1 (by rfl) ⟨72443, by rfl⟩) R144887
theorem R96607 : Reach 96607 := rs (se 1 (by rfl) ⟨72455, by rfl⟩) R144911
theorem R162155 : Reach 162155 := rs (se 1 (by rfl) ⟨121616, by rfl⟩) R243233
theorem R96635 : Reach 96635 := rs (se 1 (by rfl) ⟨72476, by rfl⟩) R144953
theorem R1112453 : Reach 1112453 := rs (se 4 (by rfl) ⟨104292, by rfl⟩) R208585
theorem R96687 : Reach 96687 := rs (se 1 (by rfl) ⟨72515, by rfl⟩) R145031
theorem R96711 : Reach 96711 := rs (se 1 (by rfl) ⟨72533, by rfl⟩) R145067
theorem R96731 : Reach 96731 := rs (se 1 (by rfl) ⟨72548, by rfl⟩) R145097
theorem R490009 : Reach 490009 := rs (se 2 (by rfl) ⟨183753, by rfl⟩) R367507
theorem R96807 : Reach 96807 := rs (se 1 (by rfl) ⟨72605, by rfl⟩) R145211
theorem R96847 : Reach 96847 := rs (se 1 (by rfl) ⟨72635, by rfl⟩) R145271
theorem R96863 : Reach 96863 := rs (se 1 (by rfl) ⟨72647, by rfl⟩) R145295
theorem R326267 : Reach 326267 := rs (se 1 (by rfl) ⟨244700, by rfl⟩) R489401
theorem R96891 : Reach 96891 := rs (se 1 (by rfl) ⟨72668, by rfl⟩) R145337
theorem R96943 : Reach 96943 := rs (se 1 (by rfl) ⟨72707, by rfl⟩) R145415
theorem R96967 : Reach 96967 := rs (se 1 (by rfl) ⟨72725, by rfl⟩) R145451
theorem R96987 : Reach 96987 := rs (se 1 (by rfl) ⟨72740, by rfl⟩) R145481
theorem R162553 : Reach 162553 := rs (se 2 (by rfl) ⟨60957, by rfl⟩) R121915
theorem R326429 : Reach 326429 := rs (se 3 (by rfl) ⟨61205, by rfl⟩) R122411
theorem R97063 : Reach 97063 := rs (se 1 (by rfl) ⟨72797, by rfl⟩) R145595
theorem R97103 : Reach 97103 := rs (se 1 (by rfl) ⟨72827, by rfl⟩) R145655
theorem R97119 : Reach 97119 := rs (se 1 (by rfl) ⟨72839, by rfl⟩) R145679
theorem R97147 : Reach 97147 := rs (se 1 (by rfl) ⟨72860, by rfl⟩) R145721
theorem R97199 : Reach 97199 := rs (se 1 (by rfl) ⟨72899, by rfl⟩) R145799
theorem R97223 : Reach 97223 := rs (se 1 (by rfl) ⟨72917, by rfl⟩) R145835
theorem R97243 : Reach 97243 := rs (se 1 (by rfl) ⟨72932, by rfl⟩) R145865
theorem R162823 : Reach 162823 := rs (se 1 (by rfl) ⟨122117, by rfl⟩) R244235
theorem R97319 : Reach 97319 := rs (se 1 (by rfl) ⟨72989, by rfl⟩) R145979
theorem R6454333 : Reach 6454333 := rs (se 3 (by rfl) ⟨1210187, by rfl⟩) R2420375
theorem R97359 : Reach 97359 := rs (se 1 (by rfl) ⟨73019, by rfl⟩) R146039
theorem R97375 : Reach 97375 := rs (se 1 (by rfl) ⟨73031, by rfl⟩) R146063
theorem R97403 : Reach 97403 := rs (se 1 (by rfl) ⟨73052, by rfl⟩) R146105
theorem R97455 : Reach 97455 := rs (se 1 (by rfl) ⟨73091, by rfl⟩) R146183
theorem R97479 : Reach 97479 := rs (se 1 (by rfl) ⟨73109, by rfl⟩) R146219
theorem R97499 : Reach 97499 := rs (se 1 (by rfl) ⟨73124, by rfl⟩) R146249
theorem R97575 : Reach 97575 := rs (se 1 (by rfl) ⟨73181, by rfl⟩) R146363
theorem R97615 : Reach 97615 := rs (se 1 (by rfl) ⟨73211, by rfl⟩) R146423
theorem R97631 : Reach 97631 := rs (se 1 (by rfl) ⟨73223, by rfl⟩) R146447
theorem R97659 : Reach 97659 := rs (se 1 (by rfl) ⟨73244, by rfl⟩) R146489
theorem R97711 : Reach 97711 := rs (se 1 (by rfl) ⟨73283, by rfl⟩) R146567
theorem R163255 : Reach 163255 := rs (se 1 (by rfl) ⟨122441, by rfl⟩) R244883
theorem R97735 : Reach 97735 := rs (se 1 (by rfl) ⟨73301, by rfl⟩) R146603
theorem R327131 : Reach 327131 := rs (se 1 (by rfl) ⟨245348, by rfl⟩) R490697
theorem R97755 : Reach 97755 := rs (se 1 (by rfl) ⟨73316, by rfl⟩) R146633
theorem R97831 : Reach 97831 := rs (se 1 (by rfl) ⟨73373, by rfl⟩) R146747
theorem R97871 : Reach 97871 := rs (se 1 (by rfl) ⟨73403, by rfl⟩) R146807
theorem R97887 : Reach 97887 := rs (se 1 (by rfl) ⟨73415, by rfl⟩) R146831
theorem R163451 : Reach 163451 := rs (se 1 (by rfl) ⟨122588, by rfl⟩) R245177
theorem R97915 : Reach 97915 := rs (se 1 (by rfl) ⟨73436, by rfl⟩) R146873
theorem R97967 : Reach 97967 := rs (se 1 (by rfl) ⟨73475, by rfl⟩) R146951
theorem R97991 : Reach 97991 := rs (se 1 (by rfl) ⟨73493, by rfl⟩) R146987
theorem R98011 : Reach 98011 := rs (se 1 (by rfl) ⟨73508, by rfl⟩) R147017
theorem R98087 : Reach 98087 := rs (se 1 (by rfl) ⟨73565, by rfl⟩) R147131
theorem R98127 : Reach 98127 := rs (se 1 (by rfl) ⟨73595, by rfl⟩) R147191
theorem R98143 : Reach 98143 := rs (se 1 (by rfl) ⟨73607, by rfl⟩) R147215
theorem R98171 : Reach 98171 := rs (se 1 (by rfl) ⟨73628, by rfl⟩) R147257
theorem R98223 : Reach 98223 := rs (se 1 (by rfl) ⟨73667, by rfl⟩) R147335
theorem R425915 : Reach 425915 := rs (se 1 (by rfl) ⟨319436, by rfl⟩) R638873
theorem R98247 : Reach 98247 := rs (se 1 (by rfl) ⟨73685, by rfl⟩) R147371
theorem R98267 : Reach 98267 := rs (se 1 (by rfl) ⟨73700, by rfl⟩) R147401
theorem R1048627 : Reach 1048627 := rs (se 1 (by rfl) ⟨786470, by rfl⟩) R1572941
theorem R98591 : Reach 98591 := rs (se 1 (by rfl) ⟨73943, by rfl⟩) R147887
theorem R98651 : Reach 98651 := rs (se 1 (by rfl) ⟨73988, by rfl⟩) R147977
theorem R164207 : Reach 164207 := rs (se 1 (by rfl) ⟨123155, by rfl⟩) R246311
theorem R98671 : Reach 98671 := rs (se 1 (by rfl) ⟨74003, by rfl⟩) R148007
theorem R98727 : Reach 98727 := rs (se 1 (by rfl) ⟨74045, by rfl⟩) R148091
theorem R459209 : Reach 459209 := rs (se 2 (by rfl) ⟨172203, by rfl⟩) R344407
theorem R98811 : Reach 98811 := rs (se 1 (by rfl) ⟨74108, by rfl⟩) R148217
theorem R328211 : Reach 328211 := rs (se 1 (by rfl) ⟨246158, by rfl⟩) R492317
theorem R98879 : Reach 98879 := rs (se 1 (by rfl) ⟨74159, by rfl⟩) R148319
theorem R164423 : Reach 164423 := rs (se 1 (by rfl) ⟨123317, by rfl⟩) R246635
theorem R98887 : Reach 98887 := rs (se 1 (by rfl) ⟨74165, by rfl⟩) R148331
theorem R459361 : Reach 459361 := rs (se 2 (by rfl) ⟨172260, by rfl⟩) R344521
theorem R393911 : Reach 393911 := rs (se 1 (by rfl) ⟨295433, by rfl⟩) R590867
theorem R3539659 : Reach 3539659 := rs (se 1 (by rfl) ⟨2654744, by rfl⟩) R5309489
theorem R99039 : Reach 99039 := rs (se 1 (by rfl) ⟨74279, by rfl⟩) R148559
theorem R99119 : Reach 99119 := rs (se 1 (by rfl) ⟨74339, by rfl⟩) R148679
theorem R164855 : Reach 164855 := rs (se 1 (by rfl) ⟨123641, by rfl⟩) R247283
theorem R492641 : Reach 492641 := rs (se 2 (by rfl) ⟨184740, by rfl⟩) R369481
theorem R820367 : Reach 820367 := rs (se 1 (by rfl) ⟨615275, by rfl⟩) R1230551
theorem R361705 : Reach 361705 := rs (se 2 (by rfl) ⟨135639, by rfl⟩) R271279
theorem R1115369 : Reach 1115369 := rs (se 2 (by rfl) ⟨418263, by rfl⟩) R836527
theorem R558323 : Reach 558323 := rs (se 1 (by rfl) ⟨418742, by rfl⟩) R837485
theorem R918821 : Reach 918821 := rs (se 4 (by rfl) ⟨86139, by rfl⟩) R172279
theorem R165611 : Reach 165611 := rs (se 1 (by rfl) ⟨124208, by rfl⟩) R248417
theorem R395113 : Reach 395113 := rs (se 2 (by rfl) ⟨148167, by rfl⟩) R296335
theorem R100327 : Reach 100327 := rs (se 1 (by rfl) ⟨75245, by rfl⟩) R150491
theorem R329993 : Reach 329993 := rs (se 2 (by rfl) ⟨123747, by rfl⟩) R247495
theorem R166583 : Reach 166583 := rs (se 1 (by rfl) ⟨124937, by rfl⟩) R249875
theorem R232487 : Reach 232487 := rs (se 1 (by rfl) ⟨174365, by rfl⟩) R348731
theorem R593183 : Reach 593183 := rs (se 1 (by rfl) ⟨444887, by rfl⟩) R889775
theorem R494909 : Reach 494909 := rs (se 3 (by rfl) ⟨92795, by rfl⟩) R185591
theorem R331127 : Reach 331127 := rs (se 1 (by rfl) ⟨248345, by rfl⟩) R496691
theorem R1248641 : Reach 1248641 := rs (se 2 (by rfl) ⟨468240, by rfl⟩) R936481
theorem R232967 : Reach 232967 := rs (se 1 (by rfl) ⟨174725, by rfl⟩) R349451
theorem R1249667 : Reach 1249667 := rs (se 1 (by rfl) ⟨937250, by rfl⟩) R1874501
theorem R332207 : Reach 332207 := rs (se 1 (by rfl) ⟨249155, by rfl⟩) R498311
theorem R168671 : Reach 168671 := rs (se 1 (by rfl) ⟨126503, by rfl⟩) R253007
theorem R955165 : Reach 955165 := rs (se 3 (by rfl) ⟨179093, by rfl⟩) R358187
theorem R496493 : Reach 496493 := rs (se 3 (by rfl) ⟨93092, by rfl⟩) R186185
theorem R824363 : Reach 824363 := rs (se 1 (by rfl) ⟨618272, by rfl⟩) R1236545
theorem R365867 : Reach 365867 := rs (se 1 (by rfl) ⟨274400, by rfl⟩) R548801
theorem R595295 : Reach 595295 := rs (se 1 (by rfl) ⟨446471, by rfl⟩) R892943
theorem R333179 : Reach 333179 := rs (se 1 (by rfl) ⟨249884, by rfl⟩) R499769
theorem R103879 : Reach 103879 := rs (se 1 (by rfl) ⟨77909, by rfl⟩) R155819
theorem R497339 : Reach 497339 := rs (se 1 (by rfl) ⟨373004, by rfl⟩) R746009
theorem R1644623 : Reach 1644623 := rs (se 1 (by rfl) ⟨1233467, by rfl⟩) R2466935
theorem R301241 : Reach 301241 := rs (se 2 (by rfl) ⟨112965, by rfl⟩) R225931
theorem R465263 : Reach 465263 := rs (se 1 (by rfl) ⟨348947, by rfl⟩) R697895
theorem R137639 : Reach 137639 := rs (se 1 (by rfl) ⟨103229, by rfl⟩) R206459
theorem R564155 : Reach 564155 := rs (se 1 (by rfl) ⟨423116, by rfl⟩) R846233
theorem R368009 : Reach 368009 := rs (se 2 (by rfl) ⟨138003, by rfl⟩) R276007
theorem R1383961 : Reach 1383961 := rs (se 2 (by rfl) ⟨518985, by rfl⟩) R1037971
theorem R499283 : Reach 499283 := rs (se 1 (by rfl) ⟨374462, by rfl⟩) R748925
theorem R204383 : Reach 204383 := rs (se 1 (by rfl) ⟨153287, by rfl⟩) R306575
theorem R3382879 : Reach 3382879 := rs (se 1 (by rfl) ⟨2537159, by rfl⟩) R5074319
theorem R12754583 : Reach 12754583 := rs (se 1 (by rfl) ⟨9565937, by rfl⟩) R19131875
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R205391 : Reach 205391 := rs (se 1 (by rfl) ⟨154043, by rfl⟩) R308087
theorem R107311 : Reach 107311 := rs (se 1 (by rfl) ⟨80483, by rfl⟩) R160967
theorem R107419 : Reach 107419 := rs (se 1 (by rfl) ⟨80564, by rfl⟩) R161129
theorem R1057697 : Reach 1057697 := rs (se 2 (by rfl) ⟨396636, by rfl⟩) R793273
theorem R893891 : Reach 893891 := rs (se 1 (by rfl) ⟨670418, by rfl⟩) R1340837
theorem R206023 : Reach 206023 := rs (se 1 (by rfl) ⟨154517, by rfl⟩) R309035
theorem R206057 : Reach 206057 := rs (se 2 (by rfl) ⟨77271, by rfl⟩) R154543
theorem R107815 : Reach 107815 := rs (se 1 (by rfl) ⟨80861, by rfl⟩) R161723
theorem R107887 : Reach 107887 := rs (se 1 (by rfl) ⟨80915, by rfl⟩) R161831
theorem R108103 : Reach 108103 := rs (se 1 (by rfl) ⟨81077, by rfl⟩) R162155
theorem R731429 : Reach 731429 := rs (se 4 (by rfl) ⟨68571, by rfl⟩) R137143
theorem R207211 : Reach 207211 := rs (se 1 (by rfl) ⟨155408, by rfl⟩) R310817
theorem R797039 : Reach 797039 := rs (se 1 (by rfl) ⟨597779, by rfl⟩) R1195559
theorem R469415 : Reach 469415 := rs (se 1 (by rfl) ⟨352061, by rfl⟩) R704123
theorem R108967 : Reach 108967 := rs (se 1 (by rfl) ⟨81725, by rfl⟩) R163451
theorem R207287 : Reach 207287 := rs (se 1 (by rfl) ⟨155465, by rfl⟩) R310931
theorem R207355 : Reach 207355 := rs (se 1 (by rfl) ⟨155516, by rfl⟩) R311033
theorem R1059601 : Reach 1059601 := rs (se 2 (by rfl) ⟨397350, by rfl⟩) R794701
theorem R273307 : Reach 273307 := rs (se 1 (by rfl) ⟨204980, by rfl⟩) R409961
theorem R109543 : Reach 109543 := rs (se 1 (by rfl) ⟨82157, by rfl⟩) R164315
theorem R371699 : Reach 371699 := rs (se 1 (by rfl) ⟨278774, by rfl⟩) R557549
theorem R142715 : Reach 142715 := rs (se 1 (by rfl) ⟨107036, by rfl⟩) R214073
theorem R142841 : Reach 142841 := rs (se 2 (by rfl) ⟨53565, by rfl⟩) R107131
theorem R110143 : Reach 110143 := rs (se 1 (by rfl) ⟨82607, by rfl⟩) R165215
theorem R142943 : Reach 142943 := rs (se 1 (by rfl) ⟨107207, by rfl⟩) R214415
theorem R241339 : Reach 241339 := rs (se 1 (by rfl) ⟨181004, by rfl⟩) R362009
theorem R175879 : Reach 175879 := rs (se 1 (by rfl) ⟨131909, by rfl⟩) R263819
theorem R143159 : Reach 143159 := rs (se 1 (by rfl) ⟨107369, by rfl⟩) R214739
theorem R143465 : Reach 143465 := rs (se 2 (by rfl) ⟨53799, by rfl⟩) R107599
theorem R143783 : Reach 143783 := rs (se 1 (by rfl) ⟨107837, by rfl⟩) R215675
theorem R143867 : Reach 143867 := rs (se 1 (by rfl) ⟨107900, by rfl⟩) R215801
theorem R275015 : Reach 275015 := rs (se 1 (by rfl) ⟨206261, by rfl⟩) R412523
theorem R111199 : Reach 111199 := rs (se 1 (by rfl) ⟨83399, by rfl⟩) R166799
theorem R143993 : Reach 143993 := rs (se 2 (by rfl) ⟨53997, by rfl⟩) R107995
theorem R373369 : Reach 373369 := rs (se 2 (by rfl) ⟨140013, by rfl⟩) R280027
theorem R1127033 : Reach 1127033 := rs (se 2 (by rfl) ⟨422637, by rfl⟩) R845275
theorem R832153 : Reach 832153 := rs (se 2 (by rfl) ⟨312057, by rfl⟩) R624115
theorem R144047 : Reach 144047 := rs (se 1 (by rfl) ⟨108035, by rfl⟩) R216071
theorem R144095 : Reach 144095 := rs (se 1 (by rfl) ⟨108071, by rfl⟩) R216143
theorem R242423 : Reach 242423 := rs (se 1 (by rfl) ⟨181817, by rfl⟩) R363635
theorem R176975 : Reach 176975 := rs (se 1 (by rfl) ⟨132731, by rfl⟩) R265463
theorem R144359 : Reach 144359 := rs (se 1 (by rfl) ⟨108269, by rfl⟩) R216539
theorem R144617 : Reach 144617 := rs (se 2 (by rfl) ⟨54231, by rfl⟩) R108463
theorem R275699 : Reach 275699 := rs (se 1 (by rfl) ⟨206774, by rfl⟩) R413549
theorem R144671 : Reach 144671 := rs (se 1 (by rfl) ⟨108503, by rfl⟩) R217007
theorem R144839 : Reach 144839 := rs (se 1 (by rfl) ⟨108629, by rfl⟩) R217259
theorem R3225091 : Reach 3225091 := rs (se 1 (by rfl) ⟨2418818, by rfl⟩) R4837637
theorem R701959 : Reach 701959 := rs (se 1 (by rfl) ⟨526469, by rfl⟩) R1052939
theorem R243283 : Reach 243283 := rs (se 1 (by rfl) ⟨182462, by rfl⟩) R364925
theorem R276155 : Reach 276155 := rs (se 1 (by rfl) ⟨207116, by rfl⟩) R414233
theorem R407227 : Reach 407227 := rs (se 1 (by rfl) ⟨305420, by rfl⟩) R610841
theorem R145193 : Reach 145193 := rs (se 2 (by rfl) ⟨54447, by rfl⟩) R108895
theorem R145199 : Reach 145199 := rs (se 1 (by rfl) ⟨108899, by rfl⟩) R217799
theorem R374615 : Reach 374615 := rs (se 1 (by rfl) ⟨280961, by rfl⟩) R561923
theorem R1128491 : Reach 1128491 := rs (se 1 (by rfl) ⟨846368, by rfl⟩) R1692737
theorem R145673 : Reach 145673 := rs (se 2 (by rfl) ⟨54627, by rfl⟩) R109255
theorem R145775 : Reach 145775 := rs (se 1 (by rfl) ⟨109331, by rfl⟩) R218663
theorem R145991 : Reach 145991 := rs (se 1 (by rfl) ⟨109493, by rfl⟩) R218987
theorem R146027 : Reach 146027 := rs (se 1 (by rfl) ⟨109520, by rfl⟩) R219041
theorem R244559 : Reach 244559 := rs (se 1 (by rfl) ⟨183419, by rfl⟩) R366839
theorem R146255 : Reach 146255 := rs (se 1 (by rfl) ⟨109691, by rfl⟩) R219383
theorem R146651 : Reach 146651 := rs (se 1 (by rfl) ⟨109988, by rfl⟩) R219977
theorem R146825 : Reach 146825 := rs (se 2 (by rfl) ⟨55059, by rfl⟩) R110119
theorem R245207 : Reach 245207 := rs (se 1 (by rfl) ⟨183905, by rfl⟩) R367811
theorem R2440691 : Reach 2440691 := rs (se 1 (by rfl) ⟨1830518, by rfl⟩) R3661037
theorem R147179 : Reach 147179 := rs (se 1 (by rfl) ⟨110384, by rfl⟩) R220769
theorem R1228547 : Reach 1228547 := rs (se 1 (by rfl) ⟨921410, by rfl⟩) R1842821
theorem R179975 : Reach 179975 := rs (se 1 (by rfl) ⟨134981, by rfl⟩) R269963
theorem R245551 : Reach 245551 := rs (se 1 (by rfl) ⟨184163, by rfl⟩) R368327
theorem R442169 : Reach 442169 := rs (se 2 (by rfl) ⟨165813, by rfl⟩) R331627
theorem R147407 : Reach 147407 := rs (se 1 (by rfl) ⟨110555, by rfl⟩) R221111
theorem R147803 : Reach 147803 := rs (se 1 (by rfl) ⟨110852, by rfl⟩) R221705
theorem R246199 : Reach 246199 := rs (se 1 (by rfl) ⟨184649, by rfl⟩) R369299
theorem R180731 : Reach 180731 := rs (se 1 (by rfl) ⟨135548, by rfl⟩) R271097
theorem R148031 : Reach 148031 := rs (se 1 (by rfl) ⟨111023, by rfl⟩) R222047
theorem R377465 : Reach 377465 := rs (se 2 (by rfl) ⟨141549, by rfl⟩) R283099
theorem R148151 : Reach 148151 := rs (se 1 (by rfl) ⟨111113, by rfl⟩) R222227
theorem R148379 : Reach 148379 := rs (se 1 (by rfl) ⟨111284, by rfl⟩) R222569
theorem R1065959 : Reach 1065959 := rs (se 1 (by rfl) ⟨799469, by rfl⟩) R1598939
theorem R214055 : Reach 214055 := rs (se 1 (by rfl) ⟨160541, by rfl⟩) R321083
theorem R345185 : Reach 345185 := rs (se 2 (by rfl) ⟨129444, by rfl⟩) R258889
theorem R836801 : Reach 836801 := rs (se 2 (by rfl) ⟨313800, by rfl⟩) R627601
theorem R214235 : Reach 214235 := rs (se 1 (by rfl) ⟨160676, by rfl⟩) R321353
theorem R214433 : Reach 214433 := rs (se 2 (by rfl) ⟨80412, by rfl⟩) R160825
theorem R181703 : Reach 181703 := rs (se 1 (by rfl) ⟨136277, by rfl⟩) R272555
theorem R181855 : Reach 181855 := rs (se 1 (by rfl) ⟨136391, by rfl⟩) R272783
theorem R411293 : Reach 411293 := rs (se 3 (by rfl) ⟨77117, by rfl⟩) R154235
theorem R247607 : Reach 247607 := rs (se 1 (by rfl) ⟨185705, by rfl⟩) R371411
theorem R247657 : Reach 247657 := rs (se 2 (by rfl) ⟨92871, by rfl⟩) R185743
theorem R739205 : Reach 739205 := rs (se 4 (by rfl) ⟨69300, by rfl⟩) R138601
theorem R1034167 : Reach 1034167 := rs (se 1 (by rfl) ⟨775625, by rfl⟩) R1551251
theorem R214991 : Reach 214991 := rs (se 1 (by rfl) ⟨161243, by rfl⟩) R322487
theorem R444611 : Reach 444611 := rs (se 1 (by rfl) ⟨333458, by rfl⟩) R666917
theorem R215369 : Reach 215369 := rs (se 2 (by rfl) ⟨80763, by rfl⟩) R161527
theorem R215387 : Reach 215387 := rs (se 1 (by rfl) ⟨161540, by rfl⟩) R323081
theorem R445123 : Reach 445123 := rs (se 1 (by rfl) ⟨333842, by rfl⟩) R667685
theorem R412559 : Reach 412559 := rs (se 1 (by rfl) ⟨309419, by rfl⟩) R618839
theorem R215963 : Reach 215963 := rs (se 1 (by rfl) ⟨161972, by rfl⟩) R323945
theorem R216161 : Reach 216161 := rs (se 2 (by rfl) ⟨81060, by rfl⟩) R162121
theorem R249065 : Reach 249065 := rs (se 2 (by rfl) ⟨93399, by rfl⟩) R186799
theorem R838943 : Reach 838943 := rs (se 1 (by rfl) ⟨629207, by rfl⟩) R1258415
theorem R216359 : Reach 216359 := rs (se 1 (by rfl) ⟨162269, by rfl⟩) R324539
theorem R806273 : Reach 806273 := rs (se 2 (by rfl) ⟨302352, by rfl⟩) R604705
theorem R249227 : Reach 249227 := rs (se 1 (by rfl) ⟨186920, by rfl⟩) R373841
theorem R937403 : Reach 937403 := rs (se 1 (by rfl) ⟨703052, by rfl⟩) R1406105
theorem R282055 : Reach 282055 := rs (se 1 (by rfl) ⟨211541, by rfl⟩) R423083
theorem R249439 : Reach 249439 := rs (se 1 (by rfl) ⟨187079, by rfl⟩) R374159
theorem R216737 : Reach 216737 := rs (se 2 (by rfl) ⟨81276, by rfl⟩) R162553
theorem R217097 : Reach 217097 := rs (se 2 (by rfl) ⟨81411, by rfl⟩) R162823
theorem R8605777 : Reach 8605777 := rs (se 2 (by rfl) ⟨3227166, by rfl⟩) R6454333
theorem R250067 : Reach 250067 := rs (se 1 (by rfl) ⟨187550, by rfl⟩) R375101
theorem R741635 : Reach 741635 := rs (se 1 (by rfl) ⟨556226, by rfl⟩) R1112453
theorem R217511 : Reach 217511 := rs (se 1 (by rfl) ⟨163133, by rfl⟩) R326267
theorem R1102325 : Reach 1102325 := rs (se 5 (by rfl) ⟨51671, by rfl⟩) R103343
theorem R217619 : Reach 217619 := rs (se 1 (by rfl) ⟨163214, by rfl⟩) R326429
theorem R217673 : Reach 217673 := rs (se 2 (by rfl) ⟨81627, by rfl⟩) R163255
theorem R218087 : Reach 218087 := rs (se 1 (by rfl) ⟨163565, by rfl⟩) R327131
theorem R283943 : Reach 283943 := rs (se 1 (by rfl) ⟨212957, by rfl⟩) R425915
theorem R218465 : Reach 218465 := rs (se 2 (by rfl) ⟨81924, by rfl⟩) R163849
theorem R218555 : Reach 218555 := rs (se 1 (by rfl) ⟨163916, by rfl⟩) R327833
theorem R153031 : Reach 153031 := rs (se 1 (by rfl) ⟨114773, by rfl⟩) R229547
theorem R2610731 : Reach 2610731 := rs (se 1 (by rfl) ⟨1958048, by rfl⟩) R3916097
theorem R218681 : Reach 218681 := rs (se 2 (by rfl) ⟨82005, by rfl⟩) R164011
theorem R1070725 : Reach 1070725 := rs (se 4 (by rfl) ⟨100380, by rfl⟩) R200761
theorem R939863 : Reach 939863 := rs (se 1 (by rfl) ⟨704897, by rfl⟩) R1409795
theorem R350057 : Reach 350057 := rs (se 2 (by rfl) ⟨131271, by rfl⟩) R262543
theorem R481261 : Reach 481261 := rs (se 3 (by rfl) ⟨90236, by rfl⟩) R180473
theorem R219347 : Reach 219347 := rs (se 1 (by rfl) ⟨164510, by rfl⟩) R329021
theorem R416009 : Reach 416009 := rs (se 2 (by rfl) ⟨156003, by rfl⟩) R312007
theorem R219401 : Reach 219401 := rs (se 2 (by rfl) ⟨82275, by rfl⟩) R164551
theorem R186715 : Reach 186715 := rs (se 1 (by rfl) ⟨140036, by rfl⟩) R280073
theorem R416111 : Reach 416111 := rs (se 1 (by rfl) ⟨312083, by rfl⟩) R624167
theorem R219617 : Reach 219617 := rs (se 2 (by rfl) ⟨82356, by rfl⟩) R164713
theorem R481787 : Reach 481787 := rs (se 1 (by rfl) ⟨361340, by rfl⟩) R722681
theorem R1235519 : Reach 1235519 := rs (se 1 (by rfl) ⟨926639, by rfl⟩) R1853279
theorem R186943 : Reach 186943 := rs (se 1 (by rfl) ⟨140207, by rfl⟩) R280415
theorem R121439 : Reach 121439 := rs (se 1 (by rfl) ⟨91079, by rfl⟩) R182159
theorem R187103 : Reach 187103 := rs (se 1 (by rfl) ⟨140327, by rfl⟩) R280655
theorem R219923 : Reach 219923 := rs (se 1 (by rfl) ⟨164942, by rfl⟩) R329885
theorem R220283 : Reach 220283 := rs (se 1 (by rfl) ⟨165212, by rfl⟩) R330425
theorem R187535 : Reach 187535 := rs (se 1 (by rfl) ⟨140651, by rfl⟩) R281303
theorem R220409 : Reach 220409 := rs (se 2 (by rfl) ⟨82653, by rfl⟩) R165307
theorem R1105163 : Reach 1105163 := rs (se 1 (by rfl) ⟨828872, by rfl⟩) R1657745
theorem R122143 : Reach 122143 := rs (se 1 (by rfl) ⟨91607, by rfl⟩) R183215
theorem R187687 : Reach 187687 := rs (se 1 (by rfl) ⟨140765, by rfl⟩) R281531
theorem R187771 : Reach 187771 := rs (se 1 (by rfl) ⟨140828, by rfl⟩) R281657
theorem R220553 : Reach 220553 := rs (se 2 (by rfl) ⟨82707, by rfl⟩) R165415
theorem R482759 : Reach 482759 := rs (se 1 (by rfl) ⟨362069, by rfl⟩) R724139
theorem R220679 : Reach 220679 := rs (se 1 (by rfl) ⟨165509, by rfl⟩) R331019
theorem R220859 : Reach 220859 := rs (se 1 (by rfl) ⟨165644, by rfl⟩) R331289
theorem R483083 : Reach 483083 := rs (se 1 (by rfl) ⟨362312, by rfl⟩) R724625
theorem R220985 : Reach 220985 := rs (se 2 (by rfl) ⟨82869, by rfl⟩) R165739
theorem R745523 : Reach 745523 := rs (se 1 (by rfl) ⟨559142, by rfl⟩) R1118285
theorem R221615 : Reach 221615 := rs (se 1 (by rfl) ⟨166211, by rfl⟩) R332423
theorem R221651 : Reach 221651 := rs (se 1 (by rfl) ⟨166238, by rfl⟩) R332477
theorem R2089475 : Reach 2089475 := rs (se 1 (by rfl) ⟨1567106, by rfl⟩) R3134213
theorem R221759 : Reach 221759 := rs (se 1 (by rfl) ⟨166319, by rfl⟩) R332639
theorem R221867 : Reach 221867 := rs (se 1 (by rfl) ⟨166400, by rfl⟩) R332801
theorem R484055 : Reach 484055 := rs (se 1 (by rfl) ⟨363041, by rfl⟩) R726083
theorem R549827 : Reach 549827 := rs (se 1 (by rfl) ⟨412370, by rfl⟩) R824741
theorem R910529 : Reach 910529 := rs (se 2 (by rfl) ⟨341448, by rfl⟩) R682897
theorem R222407 : Reach 222407 := rs (se 1 (by rfl) ⟨166805, by rfl⟩) R333611
theorem R484703 : Reach 484703 := rs (se 1 (by rfl) ⟨363527, by rfl⟩) R727055
theorem R222587 : Reach 222587 := rs (se 1 (by rfl) ⟨166940, by rfl⟩) R333881
theorem R222713 : Reach 222713 := rs (se 2 (by rfl) ⟨83517, by rfl⟩) R167035
theorem R124411 : Reach 124411 := rs (se 1 (by rfl) ⟨93308, by rfl⟩) R186617
theorem R222803 : Reach 222803 := rs (se 1 (by rfl) ⟨167102, by rfl⟩) R334205
theorem R714329 : Reach 714329 := rs (se 2 (by rfl) ⟨267873, by rfl⟩) R535747
theorem R222983 : Reach 222983 := rs (se 1 (by rfl) ⟨167237, by rfl⟩) R334475
theorem R321569 : Reach 321569 := rs (se 2 (by rfl) ⟨120588, by rfl⟩) R241177
theorem R420025 : Reach 420025 := rs (se 2 (by rfl) ⟨157509, by rfl⟩) R315019
theorem R354557 : Reach 354557 := rs (se 3 (by rfl) ⟨66479, by rfl⟩) R132959
theorem R354671 : Reach 354671 := rs (se 1 (by rfl) ⟨266003, by rfl⟩) R532007
theorem R125383 : Reach 125383 := rs (se 1 (by rfl) ⟨94037, by rfl⟩) R188075
theorem R421307 : Reach 421307 := rs (se 1 (by rfl) ⟨315980, by rfl⟩) R631961
theorem R486971 : Reach 486971 := rs (se 1 (by rfl) ⟨365228, by rfl⟩) R730457
theorem R945863 : Reach 945863 := rs (se 1 (by rfl) ⟨709397, by rfl⟩) R1418795
theorem R749897 : Reach 749897 := rs (se 2 (by rfl) ⟨281211, by rfl⟩) R562423
theorem R2683415 : Reach 2683415 := rs (se 1 (by rfl) ⟨2012561, by rfl⟩) R4025123
theorem R324431 : Reach 324431 := rs (se 1 (by rfl) ⟨243323, by rfl⟩) R486647
theorem R422765 : Reach 422765 := rs (se 3 (by rfl) ⟨79268, by rfl⟩) R158537
theorem R95131 : Reach 95131 := rs (se 1 (by rfl) ⟨71348, by rfl⟩) R142697
theorem R95183 : Reach 95183 := rs (se 1 (by rfl) ⟨71387, by rfl⟩) R142775
theorem R95207 : Reach 95207 := rs (se 1 (by rfl) ⟨71405, by rfl⟩) R142811
theorem R488591 : Reach 488591 := rs (se 1 (by rfl) ⟨366443, by rfl⟩) R732887
theorem R324755 : Reach 324755 := rs (se 1 (by rfl) ⟨243566, by rfl⟩) R487133
theorem R160987 : Reach 160987 := rs (se 1 (by rfl) ⟨120740, by rfl⟩) R241481
theorem R259321 : Reach 259321 := rs (se 2 (by rfl) ⟨97245, by rfl⟩) R194491
theorem R11728151 : Reach 11728151 := rs (se 1 (by rfl) ⟨8796113, by rfl⟩) R17592227
theorem R95519 : Reach 95519 := rs (se 1 (by rfl) ⟨71639, by rfl⟩) R143279
theorem R95579 : Reach 95579 := rs (se 1 (by rfl) ⟨71684, by rfl⟩) R143369
theorem R95599 : Reach 95599 := rs (se 1 (by rfl) ⟨71699, by rfl⟩) R143399
theorem R325025 : Reach 325025 := rs (se 2 (by rfl) ⟨121884, by rfl⟩) R243769
theorem R95655 : Reach 95655 := rs (se 1 (by rfl) ⟨71741, by rfl⟩) R143483
theorem R95739 : Reach 95739 := rs (se 1 (by rfl) ⟨71804, by rfl⟩) R143609
theorem R95807 : Reach 95807 := rs (se 1 (by rfl) ⟨71855, by rfl⟩) R143711
theorem R95815 : Reach 95815 := rs (se 1 (by rfl) ⟨71861, by rfl⟩) R143723
theorem R95967 : Reach 95967 := rs (se 1 (by rfl) ⟨71975, by rfl⟩) R143951
theorem R128747 : Reach 128747 := rs (se 1 (by rfl) ⟨96560, by rfl⟩) R193121
theorem R96047 : Reach 96047 := rs (se 1 (by rfl) ⟨72035, by rfl⟩) R144071
theorem R96155 : Reach 96155 := rs (se 1 (by rfl) ⟨72116, by rfl⟩) R144233
theorem R161743 : Reach 161743 := rs (se 1 (by rfl) ⟨121307, by rfl⟩) R242615
theorem R96207 : Reach 96207 := rs (se 1 (by rfl) ⟨72155, by rfl⟩) R144311
theorem R96231 : Reach 96231 := rs (se 1 (by rfl) ⟨72173, by rfl⟩) R144347
theorem R653345 : Reach 653345 := rs (se 2 (by rfl) ⟨245004, by rfl⟩) R490009
theorem R489725 : Reach 489725 := rs (se 3 (by rfl) ⟨91823, by rfl⟩) R183647
theorem R96543 : Reach 96543 := rs (se 1 (by rfl) ⟨72407, by rfl⟩) R144815
theorem R96603 : Reach 96603 := rs (se 1 (by rfl) ⟨72452, by rfl⟩) R144905
theorem R96623 : Reach 96623 := rs (se 1 (by rfl) ⟨72467, by rfl⟩) R144935
theorem R96679 : Reach 96679 := rs (se 1 (by rfl) ⟨72509, by rfl⟩) R145019
theorem R96763 : Reach 96763 := rs (se 1 (by rfl) ⟨72572, by rfl⟩) R145145
theorem R1243673 : Reach 1243673 := rs (se 2 (by rfl) ⟨466377, by rfl⟩) R932755
theorem R96831 : Reach 96831 := rs (se 1 (by rfl) ⟨72623, by rfl⟩) R145247
theorem R96839 : Reach 96839 := rs (se 1 (by rfl) ⟨72629, by rfl⟩) R145259
theorem R162425 : Reach 162425 := rs (se 2 (by rfl) ⟨60909, by rfl⟩) R121819
theorem R555659 : Reach 555659 := rs (se 1 (by rfl) ⟨416744, by rfl⟩) R833489
theorem R162479 : Reach 162479 := rs (se 1 (by rfl) ⟨121859, by rfl⟩) R243719
theorem R96991 : Reach 96991 := rs (se 1 (by rfl) ⟨72743, by rfl⟩) R145487
theorem R97071 : Reach 97071 := rs (se 1 (by rfl) ⟨72803, by rfl⟩) R145607
theorem R1899409 : Reach 1899409 := rs (se 2 (by rfl) ⟨712278, by rfl⟩) R1424557
theorem R162715 : Reach 162715 := rs (se 1 (by rfl) ⟨122036, by rfl⟩) R244073
theorem R97179 : Reach 97179 := rs (se 1 (by rfl) ⟨72884, by rfl⟩) R145769
theorem R97231 : Reach 97231 := rs (se 1 (by rfl) ⟨72923, by rfl⟩) R145847
theorem R97255 : Reach 97255 := rs (se 1 (by rfl) ⟨72941, by rfl⟩) R145883
theorem R490535 : Reach 490535 := rs (se 1 (by rfl) ⟨367901, by rfl⟩) R735803
theorem R97567 : Reach 97567 := rs (se 1 (by rfl) ⟨73175, by rfl⟩) R146351
theorem R97627 : Reach 97627 := rs (se 1 (by rfl) ⟨73220, by rfl⟩) R146441
theorem R97647 : Reach 97647 := rs (se 1 (by rfl) ⟨73235, by rfl⟩) R146471
theorem R97703 : Reach 97703 := rs (se 1 (by rfl) ⟨73277, by rfl⟩) R146555
theorem R97787 : Reach 97787 := rs (se 1 (by rfl) ⟨73340, by rfl⟩) R146681
theorem R1146383 : Reach 1146383 := rs (se 1 (by rfl) ⟨859787, by rfl⟩) R1719575
theorem R97855 : Reach 97855 := rs (se 1 (by rfl) ⟨73391, by rfl⟩) R146783
theorem R97863 : Reach 97863 := rs (se 1 (by rfl) ⟨73397, by rfl⟩) R146795
theorem R98015 : Reach 98015 := rs (se 1 (by rfl) ⟨73511, by rfl⟩) R147023
theorem R98095 : Reach 98095 := rs (se 1 (by rfl) ⟨73571, by rfl⟩) R147143
theorem R98203 : Reach 98203 := rs (se 1 (by rfl) ⟨73652, by rfl⟩) R147305
theorem R98255 : Reach 98255 := rs (se 1 (by rfl) ⟨73691, by rfl⟩) R147383
theorem R98279 : Reach 98279 := rs (se 1 (by rfl) ⟨73709, by rfl⟩) R147419
theorem R98535 : Reach 98535 := rs (se 1 (by rfl) ⟨73901, by rfl⟩) R147803
theorem R98687 : Reach 98687 := rs (se 1 (by rfl) ⟨74015, by rfl⟩) R148031
theorem R262607 : Reach 262607 := rs (se 1 (by rfl) ⟨196955, by rfl⟩) R393911
theorem R98767 : Reach 98767 := rs (se 1 (by rfl) ⟨74075, by rfl⟩) R148151
theorem R328265 : Reach 328265 := rs (se 2 (by rfl) ⟨123099, by rfl⟩) R246199
theorem R98919 : Reach 98919 := rs (se 1 (by rfl) ⟨74189, by rfl⟩) R148379
theorem R230123 : Reach 230123 := rs (se 1 (by rfl) ⟨172592, by rfl⟩) R345185
theorem R328427 : Reach 328427 := rs (se 1 (by rfl) ⟨246320, by rfl⟩) R492641
theorem R557867 : Reach 557867 := rs (se 1 (by rfl) ⟨418400, by rfl⟩) R836801
theorem R4719545 : Reach 4719545 := rs (se 2 (by rfl) ⟨1769829, by rfl⟩) R3539659
theorem R165071 : Reach 165071 := rs (se 1 (by rfl) ⟨123803, by rfl⟩) R247607
theorem R492803 : Reach 492803 := rs (se 1 (by rfl) ⟨369602, by rfl⟩) R739205
theorem R296407 : Reach 296407 := rs (se 1 (by rfl) ⟨222305, by rfl⟩) R444611
theorem R165881 : Reach 165881 := rs (se 2 (by rfl) ⟨62205, by rfl⟩) R124411
theorem R166043 : Reach 166043 := rs (se 1 (by rfl) ⟨124532, by rfl⟩) R249065
theorem R559295 : Reach 559295 := rs (se 1 (by rfl) ⟨419471, by rfl⟩) R838943
theorem R395455 : Reach 395455 := rs (se 1 (by rfl) ⟨296591, by rfl⟩) R593183
theorem R329939 : Reach 329939 := rs (se 1 (by rfl) ⟨247454, by rfl⟩) R494909
theorem R166151 : Reach 166151 := rs (se 1 (by rfl) ⟨124613, by rfl⟩) R249227
theorem R624935 : Reach 624935 := rs (se 1 (by rfl) ⟨468701, by rfl⟩) R937403
theorem R526817 : Reach 526817 := rs (se 2 (by rfl) ⟨197556, by rfl⟩) R395113
theorem R330209 : Reach 330209 := rs (se 2 (by rfl) ⟨123828, by rfl⟩) R247657
theorem R1378889 : Reach 1378889 := rs (se 2 (by rfl) ⟨517083, by rfl⟩) R1034167
theorem R133769 : Reach 133769 := rs (se 2 (by rfl) ⟨50163, by rfl⟩) R100327
theorem R166711 : Reach 166711 := rs (se 1 (by rfl) ⟨125033, by rfl⟩) R250067
theorem R494423 : Reach 494423 := rs (se 1 (by rfl) ⟨370817, by rfl⟩) R741635
theorem R560033 : Reach 560033 := rs (se 2 (by rfl) ⟨210012, by rfl⟩) R420025
theorem R330995 : Reach 330995 := rs (se 1 (by rfl) ⟨248246, by rfl⟩) R496493
theorem R167177 : Reach 167177 := rs (se 2 (by rfl) ⟨62691, by rfl⟩) R125383
theorem R757181 : Reach 757181 := rs (se 3 (by rfl) ⟨141971, by rfl⟩) R283943
theorem R396863 : Reach 396863 := rs (se 1 (by rfl) ⟨297647, by rfl⟩) R595295
theorem R593497 : Reach 593497 := rs (se 2 (by rfl) ⟨222561, by rfl⟩) R445123
theorem R1412801 : Reach 1412801 := rs (se 2 (by rfl) ⟨529800, by rfl⟩) R1059601
theorem R1740487 : Reach 1740487 := rs (se 1 (by rfl) ⟨1305365, by rfl⟩) R2610731
theorem R331559 : Reach 331559 := rs (se 1 (by rfl) ⟨248669, by rfl⟩) R497339
theorem R364409 : Reach 364409 := rs (se 2 (by rfl) ⟨136653, by rfl⟩) R273307
theorem R233371 : Reach 233371 := rs (se 1 (by rfl) ⟨175028, by rfl⟩) R350057
theorem R200827 : Reach 200827 := rs (se 1 (by rfl) ⟨150620, by rfl⟩) R301241
theorem R823679 : Reach 823679 := rs (se 1 (by rfl) ⟨617759, by rfl⟩) R1235519
theorem R332585 : Reach 332585 := rs (se 2 (by rfl) ⟨124719, by rfl⟩) R249439
theorem R234505 : Reach 234505 := rs (se 2 (by rfl) ⟨87939, by rfl⟩) R175879
theorem R332855 : Reach 332855 := rs (se 1 (by rfl) ⟨249641, by rfl⟩) R499283
theorem R136255 : Reach 136255 := rs (se 1 (by rfl) ⟨102191, by rfl⟩) R204383
theorem R497015 : Reach 497015 := rs (se 1 (by rfl) ⟨372761, by rfl⟩) R745523
theorem R11474369 : Reach 11474369 := rs (se 2 (by rfl) ⟨4302888, by rfl⟩) R8605777
theorem R136927 : Reach 136927 := rs (se 1 (by rfl) ⟨102695, by rfl⟩) R205391
theorem R366551 : Reach 366551 := rs (se 1 (by rfl) ⟨274913, by rfl⟩) R549827
theorem R595927 : Reach 595927 := rs (se 1 (by rfl) ⟨446945, by rfl⟩) R893891
theorem R137371 : Reach 137371 := rs (se 1 (by rfl) ⟨103028, by rfl⟩) R206057
theorem R497825 : Reach 497825 := rs (se 2 (by rfl) ⟨186684, by rfl⟩) R373369
theorem R367037 : Reach 367037 := rs (se 3 (by rfl) ⟨68819, by rfl⟩) R137639
theorem R236371 : Reach 236371 := rs (se 1 (by rfl) ⟨177278, by rfl⟩) R354557
theorem R531359 : Reach 531359 := rs (se 1 (by rfl) ⟨398519, by rfl⟩) R797039
theorem R236447 : Reach 236447 := rs (se 1 (by rfl) ⟨177335, by rfl⟩) R354671
theorem R138191 : Reach 138191 := rs (se 1 (by rfl) ⟨103643, by rfl⟩) R207287
theorem R204041 : Reach 204041 := rs (se 2 (by rfl) ⟨76515, by rfl⟩) R153031
theorem R138505 : Reach 138505 := rs (se 2 (by rfl) ⟨51939, by rfl⟩) R103879
theorem R4300121 : Reach 4300121 := rs (se 2 (by rfl) ⟨1612545, by rfl⟩) R3225091
theorem R630575 : Reach 630575 := rs (se 1 (by rfl) ⟨472931, by rfl⟩) R945863
theorem R499931 : Reach 499931 := rs (se 1 (by rfl) ⟨374948, by rfl⟩) R749897
theorem R500093 : Reach 500093 := rs (se 3 (by rfl) ⟨93767, by rfl⟩) R187535
theorem R2532545 : Reach 2532545 := rs (se 2 (by rfl) ⟨949704, by rfl⟩) R1899409
theorem R435563 : Reach 435563 := rs (se 1 (by rfl) ⟨326672, by rfl⟩) R653345
theorem R829115 : Reach 829115 := rs (se 1 (by rfl) ⟨621836, by rfl⟩) R1243673
theorem R108283 : Reach 108283 := rs (se 1 (by rfl) ⟨81212, by rfl⟩) R162425
theorem R370439 : Reach 370439 := rs (se 1 (by rfl) ⟨277829, by rfl⟩) R555659
theorem R108319 : Reach 108319 := rs (se 1 (by rfl) ⟨81239, by rfl⟩) R162479
theorem R1845281 : Reach 1845281 := rs (se 2 (by rfl) ⟨691980, by rfl⟩) R1383961
theorem R764255 : Reach 764255 := rs (se 1 (by rfl) ⟨573191, by rfl⟩) R1146383
theorem R109471 : Reach 109471 := rs (se 1 (by rfl) ⟨82103, by rfl⟩) R164207
theorem R306139 : Reach 306139 := rs (se 1 (by rfl) ⟨229604, by rfl⟩) R459209
theorem R109615 : Reach 109615 := rs (se 1 (by rfl) ⟨82211, by rfl⟩) R164423
theorem R109903 : Reach 109903 := rs (se 1 (by rfl) ⟨82427, by rfl⟩) R164855
theorem R142703 : Reach 142703 := rs (se 1 (by rfl) ⟨107027, by rfl⟩) R214055
theorem R142823 : Reach 142823 := rs (se 1 (by rfl) ⟨107117, by rfl⟩) R214235
theorem R372215 : Reach 372215 := rs (se 1 (by rfl) ⟨279161, by rfl⟩) R558323
theorem R142955 : Reach 142955 := rs (se 1 (by rfl) ⟨107216, by rfl⟩) R214433
theorem R143081 : Reach 143081 := rs (se 2 (by rfl) ⟨53655, by rfl⟩) R107311
theorem R274195 : Reach 274195 := rs (se 1 (by rfl) ⟨205646, by rfl⟩) R411293
theorem R110407 : Reach 110407 := rs (se 1 (by rfl) ⟨82805, by rfl⟩) R165611
theorem R143225 : Reach 143225 := rs (se 2 (by rfl) ⟨53709, by rfl⟩) R107419
theorem R143327 : Reach 143327 := rs (se 1 (by rfl) ⟨107495, by rfl⟩) R214991
theorem R7155773 : Reach 7155773 := rs (se 3 (by rfl) ⟨1341707, by rfl⟩) R2683415
theorem R733373 : Reach 733373 := rs (se 3 (by rfl) ⟨137507, by rfl⟩) R275015
theorem R143579 : Reach 143579 := rs (se 1 (by rfl) ⟨107684, by rfl⟩) R215369
theorem R143591 : Reach 143591 := rs (se 1 (by rfl) ⟨107693, by rfl⟩) R215387
theorem R274697 : Reach 274697 := rs (se 2 (by rfl) ⟨103011, by rfl⟩) R206023
theorem R143753 : Reach 143753 := rs (se 2 (by rfl) ⟨53907, by rfl⟩) R107815
theorem R111055 : Reach 111055 := rs (se 1 (by rfl) ⟨83291, by rfl⟩) R166583
theorem R143849 : Reach 143849 := rs (se 2 (by rfl) ⟨53943, by rfl⟩) R107887
theorem R275039 : Reach 275039 := rs (se 1 (by rfl) ⟨206279, by rfl⟩) R412559
theorem R143975 : Reach 143975 := rs (se 1 (by rfl) ⟨107981, by rfl⟩) R215963
theorem R144107 : Reach 144107 := rs (se 1 (by rfl) ⟨108080, by rfl⟩) R216161
theorem R144137 : Reach 144137 := rs (se 2 (by rfl) ⟨54051, by rfl⟩) R108103
theorem R242473 : Reach 242473 := rs (se 2 (by rfl) ⟨90927, by rfl⟩) R181855
theorem R144239 : Reach 144239 := rs (se 1 (by rfl) ⟨108179, by rfl⟩) R216359
theorem R832427 : Reach 832427 := rs (se 1 (by rfl) ⟨624320, by rfl⟩) R1248641
theorem R537515 : Reach 537515 := rs (se 1 (by rfl) ⟨403136, by rfl⟩) R806273
theorem R144491 : Reach 144491 := rs (se 1 (by rfl) ⟨108368, by rfl⟩) R216737
theorem R144731 : Reach 144731 := rs (se 1 (by rfl) ⟨108548, by rfl⟩) R217097
theorem R833111 : Reach 833111 := rs (se 1 (by rfl) ⟨624833, by rfl⟩) R1249667
theorem R145007 : Reach 145007 := rs (se 1 (by rfl) ⟨108755, by rfl⟩) R217511
theorem R145079 : Reach 145079 := rs (se 1 (by rfl) ⟨108809, by rfl⟩) R217619
theorem R145115 : Reach 145115 := rs (se 1 (by rfl) ⟨108836, by rfl⟩) R217673
theorem R276281 : Reach 276281 := rs (se 2 (by rfl) ⟨103605, by rfl⟩) R207211
theorem R112447 : Reach 112447 := rs (se 1 (by rfl) ⟨84335, by rfl⟩) R168671
theorem R145289 : Reach 145289 := rs (se 2 (by rfl) ⟨54483, by rfl⟩) R108967
theorem R145391 : Reach 145391 := rs (se 1 (by rfl) ⟨109043, by rfl⟩) R218087
theorem R276473 : Reach 276473 := rs (se 2 (by rfl) ⟨103677, by rfl⟩) R207355
theorem R243911 : Reach 243911 := rs (se 1 (by rfl) ⟨182933, by rfl⟩) R365867
theorem R145643 : Reach 145643 := rs (se 1 (by rfl) ⟨109232, by rfl⟩) R218465
theorem R145703 : Reach 145703 := rs (se 1 (by rfl) ⟨109277, by rfl⟩) R218555
theorem R145787 : Reach 145787 := rs (se 1 (by rfl) ⟨109340, by rfl⟩) R218681
theorem R146057 : Reach 146057 := rs (se 2 (by rfl) ⟨54771, by rfl⟩) R109543
theorem R1096415 : Reach 1096415 := rs (se 1 (by rfl) ⟨822311, by rfl⟩) R1644623
theorem R146231 : Reach 146231 := rs (se 1 (by rfl) ⟨109673, by rfl⟩) R219347
theorem R146267 : Reach 146267 := rs (se 1 (by rfl) ⟨109700, by rfl⟩) R219401
theorem R277339 : Reach 277339 := rs (se 1 (by rfl) ⟨208004, by rfl⟩) R416009
theorem R310175 : Reach 310175 := rs (se 1 (by rfl) ⟨232631, by rfl⟩) R465263
theorem R146411 : Reach 146411 := rs (se 1 (by rfl) ⟨109808, by rfl⟩) R219617
theorem R146615 : Reach 146615 := rs (se 1 (by rfl) ⟨109961, by rfl⟩) R219923
theorem R376073 : Reach 376073 := rs (se 2 (by rfl) ⟨141027, by rfl⟩) R282055
theorem R343325 : Reach 343325 := rs (se 3 (by rfl) ⟨64373, by rfl⟩) R128747
theorem R376103 : Reach 376103 := rs (se 1 (by rfl) ⟨282077, by rfl⟩) R564155
theorem R146855 : Reach 146855 := rs (se 1 (by rfl) ⟨110141, by rfl⟩) R220283
theorem R146857 : Reach 146857 := rs (se 2 (by rfl) ⟨55071, by rfl⟩) R110143
theorem R146939 : Reach 146939 := rs (se 1 (by rfl) ⟨110204, by rfl⟩) R220409
theorem R736775 : Reach 736775 := rs (se 1 (by rfl) ⟨552581, by rfl⟩) R1105163
theorem R2506301 : Reach 2506301 := rs (se 3 (by rfl) ⟨469931, by rfl⟩) R939863
theorem R245339 : Reach 245339 := rs (se 1 (by rfl) ⟨184004, by rfl⟩) R368009
theorem R147035 : Reach 147035 := rs (se 1 (by rfl) ⟨110276, by rfl⟩) R220553
theorem R147119 : Reach 147119 := rs (se 1 (by rfl) ⟨110339, by rfl⟩) R220679
theorem R8503055 : Reach 8503055 := rs (se 1 (by rfl) ⟨6377291, by rfl⟩) R12754583
theorem R147239 : Reach 147239 := rs (se 1 (by rfl) ⟨110429, by rfl⟩) R220859
theorem R147323 : Reach 147323 := rs (se 1 (by rfl) ⟨110492, by rfl⟩) R220985
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R147743 : Reach 147743 := rs (se 1 (by rfl) ⟨110807, by rfl⟩) R221615
theorem R147767 : Reach 147767 := rs (se 1 (by rfl) ⟨110825, by rfl⟩) R221651
theorem R1392983 : Reach 1392983 := rs (se 1 (by rfl) ⟨1044737, by rfl⟩) R2089475
theorem R147839 : Reach 147839 := rs (se 1 (by rfl) ⟨110879, by rfl⟩) R221759
theorem R147911 : Reach 147911 := rs (se 1 (by rfl) ⟨110933, by rfl⟩) R221867
theorem R705131 : Reach 705131 := rs (se 1 (by rfl) ⟨528848, by rfl⟩) R1057697
theorem R148265 : Reach 148265 := rs (se 2 (by rfl) ⟨55599, by rfl⟩) R111199
theorem R607019 : Reach 607019 := rs (se 1 (by rfl) ⟨455264, by rfl⟩) R910529
theorem R148271 : Reach 148271 := rs (se 1 (by rfl) ⟨111203, by rfl⟩) R222407
theorem R148391 : Reach 148391 := rs (se 1 (by rfl) ⟨111293, by rfl⟩) R222587
theorem R148475 : Reach 148475 := rs (se 1 (by rfl) ⟨111356, by rfl⟩) R222713
theorem R148535 : Reach 148535 := rs (se 1 (by rfl) ⟨111401, by rfl⟩) R222803
theorem R476219 : Reach 476219 := rs (se 1 (by rfl) ⟨357164, by rfl⟩) R714329
theorem R148655 : Reach 148655 := rs (se 1 (by rfl) ⟨111491, by rfl⟩) R222983
theorem R214379 : Reach 214379 := rs (se 1 (by rfl) ⟨160784, by rfl⟩) R321569
theorem R312943 : Reach 312943 := rs (se 1 (by rfl) ⟨234707, by rfl⟩) R469415
theorem R214649 : Reach 214649 := rs (se 2 (by rfl) ⟨80493, by rfl⟩) R160987
theorem R345761 : Reach 345761 := rs (se 2 (by rfl) ⟨129660, by rfl⟩) R259321
theorem R247799 : Reach 247799 := rs (se 1 (by rfl) ⟨185849, by rfl⟩) R371699
theorem R935945 : Reach 935945 := rs (se 2 (by rfl) ⟨350979, by rfl⟩) R701959
theorem R1427633 : Reach 1427633 := rs (se 2 (by rfl) ⟨535362, by rfl⟩) R1070725
theorem R542969 : Reach 542969 := rs (se 2 (by rfl) ⟨203613, by rfl⟩) R407227
theorem R280871 : Reach 280871 := rs (se 1 (by rfl) ⟨210653, by rfl⟩) R421307
theorem R215657 : Reach 215657 := rs (se 2 (by rfl) ⟨80871, by rfl⟩) R161743
theorem R641681 : Reach 641681 := rs (se 2 (by rfl) ⟨240630, by rfl⟩) R481261
theorem R248953 : Reach 248953 := rs (se 2 (by rfl) ⟨93357, by rfl⟩) R186715
theorem R216287 : Reach 216287 := rs (se 1 (by rfl) ⟨162215, by rfl⟩) R324431
theorem R117983 : Reach 117983 := rs (se 1 (by rfl) ⟨88487, by rfl⟩) R176975
theorem R281843 : Reach 281843 := rs (se 1 (by rfl) ⟨211382, by rfl⟩) R422765
theorem R249257 : Reach 249257 := rs (se 2 (by rfl) ⟨93471, by rfl⟩) R186943
theorem R216503 : Reach 216503 := rs (se 1 (by rfl) ⟨162377, by rfl⟩) R324755
theorem R183799 : Reach 183799 := rs (se 1 (by rfl) ⟨137849, by rfl⟩) R275699
theorem R7818767 : Reach 7818767 := rs (se 1 (by rfl) ⟨5864075, by rfl⟩) R11728151
theorem R216683 : Reach 216683 := rs (se 1 (by rfl) ⟨162512, by rfl⟩) R325025
theorem R184103 : Reach 184103 := rs (se 1 (by rfl) ⟨138077, by rfl⟩) R276155
theorem R216953 : Reach 216953 := rs (se 2 (by rfl) ⟨81357, by rfl⟩) R162715
theorem R249743 : Reach 249743 := rs (se 1 (by rfl) ⟨187307, by rfl⟩) R374615
theorem R250249 : Reach 250249 := rs (se 2 (by rfl) ⟨93843, by rfl⟩) R187687
theorem R250361 : Reach 250361 := rs (se 2 (by rfl) ⟨93885, by rfl⟩) R187771
theorem R479933 : Reach 479933 := rs (se 3 (by rfl) ⟨89987, by rfl⟩) R179975
theorem R4510505 : Reach 4510505 := rs (se 2 (by rfl) ⟨1691439, by rfl⟩) R3382879
theorem R1627127 : Reach 1627127 := rs (se 1 (by rfl) ⟨1220345, by rfl⟩) R2440691
theorem R1398169 : Reach 1398169 := rs (se 2 (by rfl) ⟨524313, by rfl⟩) R1048627
theorem R218807 : Reach 218807 := rs (se 1 (by rfl) ⟨164105, by rfl⟩) R328211
theorem R710639 : Reach 710639 := rs (se 1 (by rfl) ⟨532979, by rfl⟩) R1065959
theorem R546911 : Reach 546911 := rs (se 1 (by rfl) ⟨410183, by rfl⟩) R820367
theorem R612481 : Reach 612481 := rs (se 2 (by rfl) ⟨229680, by rfl⟩) R459361
theorem R743579 : Reach 743579 := rs (se 1 (by rfl) ⟨557684, by rfl⟩) R1115369
theorem R2939533 : Reach 2939533 := rs (se 3 (by rfl) ⟨551162, by rfl⟩) R1102325
theorem R481949 : Reach 481949 := rs (se 3 (by rfl) ⟨90365, by rfl⟩) R180731
theorem R219995 : Reach 219995 := rs (se 1 (by rfl) ⟨164996, by rfl⟩) R329993
theorem R482273 : Reach 482273 := rs (se 2 (by rfl) ⟨180852, by rfl⟩) R361705
theorem R1006573 : Reach 1006573 := rs (se 3 (by rfl) ⟨188732, by rfl⟩) R377465
theorem R154991 : Reach 154991 := rs (se 1 (by rfl) ⟨116243, by rfl⟩) R232487
theorem R220751 : Reach 220751 := rs (se 1 (by rfl) ⟨165563, by rfl⟩) R331127
theorem R221471 : Reach 221471 := rs (se 1 (by rfl) ⟨166103, by rfl⟩) R332207
theorem R549575 : Reach 549575 := rs (se 1 (by rfl) ⟨412181, by rfl⟩) R824363
theorem R2450189 : Reach 2450189 := rs (se 3 (by rfl) ⟨459410, by rfl⟩) R918821
theorem R222119 : Reach 222119 := rs (se 1 (by rfl) ⟨166589, by rfl⟩) R333179
theorem R484541 : Reach 484541 := rs (se 3 (by rfl) ⟨90851, by rfl⟩) R181703
theorem R321191 : Reach 321191 := rs (se 1 (by rfl) ⟨240893, by rfl⟩) R481787
theorem R124735 : Reach 124735 := rs (se 1 (by rfl) ⟨93551, by rfl⟩) R187103
theorem R321785 : Reach 321785 := rs (se 2 (by rfl) ⟨120669, by rfl⟩) R241339
theorem R321839 : Reach 321839 := rs (se 1 (by rfl) ⟨241379, by rfl⟩) R482759
theorem R322055 : Reach 322055 := rs (se 1 (by rfl) ⟨241541, by rfl⟩) R483083
theorem R322703 : Reach 322703 := rs (se 1 (by rfl) ⟨242027, by rfl⟩) R484055
theorem R1109537 : Reach 1109537 := rs (se 2 (by rfl) ⟨416076, by rfl⟩) R832153
theorem R323135 : Reach 323135 := rs (se 1 (by rfl) ⟨242351, by rfl⟩) R484703
theorem R1109629 : Reach 1109629 := rs (se 3 (by rfl) ⟨208055, by rfl⟩) R416111
theorem R1273553 : Reach 1273553 := rs (se 2 (by rfl) ⟨477582, by rfl⟩) R955165
theorem R487619 : Reach 487619 := rs (se 1 (by rfl) ⟨365714, by rfl⟩) R731429
theorem R323837 : Reach 323837 := rs (se 3 (by rfl) ⟨60719, by rfl⟩) R121439
theorem R324377 : Reach 324377 := rs (se 2 (by rfl) ⟨121641, by rfl⟩) R243283
theorem R95143 : Reach 95143 := rs (se 1 (by rfl) ⟨71357, by rfl⟩) R142715
theorem R95227 : Reach 95227 := rs (se 1 (by rfl) ⟨71420, by rfl⟩) R142841
theorem R324647 : Reach 324647 := rs (se 1 (by rfl) ⟨243485, by rfl⟩) R486971
theorem R95295 : Reach 95295 := rs (se 1 (by rfl) ⟨71471, by rfl⟩) R142943
theorem R95439 : Reach 95439 := rs (se 1 (by rfl) ⟨71579, by rfl⟩) R143159
theorem R95643 : Reach 95643 := rs (se 1 (by rfl) ⟨71732, by rfl⟩) R143465
theorem R95855 : Reach 95855 := rs (se 1 (by rfl) ⟨71891, by rfl⟩) R143783
theorem R95911 : Reach 95911 := rs (se 1 (by rfl) ⟨71933, by rfl⟩) R143867
theorem R95995 : Reach 95995 := rs (se 1 (by rfl) ⟨71996, by rfl⟩) R143993
theorem R751355 : Reach 751355 := rs (se 1 (by rfl) ⟨563516, by rfl⟩) R1127033
theorem R96031 : Reach 96031 := rs (se 1 (by rfl) ⟨72023, by rfl⟩) R144047
theorem R96063 : Reach 96063 := rs (se 1 (by rfl) ⟨72047, by rfl⟩) R144095
theorem R161615 : Reach 161615 := rs (se 1 (by rfl) ⟨121211, by rfl⟩) R242423
theorem R96239 : Reach 96239 := rs (se 1 (by rfl) ⟨72179, by rfl⟩) R144359
theorem R325727 : Reach 325727 := rs (se 1 (by rfl) ⟨244295, by rfl⟩) R488591
theorem R96411 : Reach 96411 := rs (se 1 (by rfl) ⟨72308, by rfl⟩) R144617
theorem R96447 : Reach 96447 := rs (se 1 (by rfl) ⟨72335, by rfl⟩) R144671
theorem R96559 : Reach 96559 := rs (se 1 (by rfl) ⟨72419, by rfl⟩) R144839
theorem R96795 : Reach 96795 := rs (se 1 (by rfl) ⟨72596, by rfl⟩) R145193
theorem R96799 : Reach 96799 := rs (se 1 (by rfl) ⟨72599, by rfl⟩) R145199
theorem R621245 : Reach 621245 := rs (se 3 (by rfl) ⟨116483, by rfl⟩) R232967
theorem R752327 : Reach 752327 := rs (se 1 (by rfl) ⟨564245, by rfl⟩) R1128491
theorem R326483 : Reach 326483 := rs (se 1 (by rfl) ⟨244862, by rfl⟩) R489725
theorem R97115 : Reach 97115 := rs (se 1 (by rfl) ⟨72836, by rfl⟩) R145673
theorem R97183 : Reach 97183 := rs (se 1 (by rfl) ⟨72887, by rfl⟩) R145775
theorem R162857 : Reach 162857 := rs (se 2 (by rfl) ⟨61071, by rfl⟩) R122143
theorem R97327 : Reach 97327 := rs (se 1 (by rfl) ⟨72995, by rfl⟩) R145991
theorem R97351 : Reach 97351 := rs (se 1 (by rfl) ⟨73013, by rfl⟩) R146027
theorem R163039 : Reach 163039 := rs (se 1 (by rfl) ⟨122279, by rfl⟩) R244559
theorem R97503 : Reach 97503 := rs (se 1 (by rfl) ⟨73127, by rfl⟩) R146255
theorem R327023 : Reach 327023 := rs (se 1 (by rfl) ⟨245267, by rfl⟩) R490535
theorem R97767 : Reach 97767 := rs (se 1 (by rfl) ⟨73325, by rfl⟩) R146651
theorem R97883 : Reach 97883 := rs (se 1 (by rfl) ⟨73412, by rfl⟩) R146825
theorem R163471 : Reach 163471 := rs (se 1 (by rfl) ⟨122603, by rfl⟩) R245207
theorem R327401 : Reach 327401 := rs (se 2 (by rfl) ⟨122775, by rfl⟩) R245551
theorem R98119 : Reach 98119 := rs (se 1 (by rfl) ⟨73589, by rfl⟩) R147179
theorem R819031 : Reach 819031 := rs (se 1 (by rfl) ⟨614273, by rfl⟩) R1228547
theorem R294779 : Reach 294779 := rs (se 1 (by rfl) ⟨221084, by rfl⟩) R442169
theorem R98271 : Reach 98271 := rs (se 1 (by rfl) ⟨73703, by rfl⟩) R147407
theorem R98495 : Reach 98495 := rs (se 1 (by rfl) ⟨73871, by rfl⟩) R147743
theorem R98511 : Reach 98511 := rs (se 1 (by rfl) ⟨73883, by rfl⟩) R147767
theorem R98559 : Reach 98559 := rs (se 1 (by rfl) ⟨73919, by rfl⟩) R147839
theorem R98607 : Reach 98607 := rs (se 1 (by rfl) ⟨73955, by rfl⟩) R147911
theorem R98843 : Reach 98843 := rs (se 1 (by rfl) ⟨74132, by rfl⟩) R148265
theorem R98847 : Reach 98847 := rs (se 1 (by rfl) ⟨74135, by rfl⟩) R148271
theorem R98927 : Reach 98927 := rs (se 1 (by rfl) ⟨74195, by rfl⟩) R148391
theorem R3146363 : Reach 3146363 := rs (se 1 (by rfl) ⟨2359772, by rfl⟩) R4719545
theorem R98983 : Reach 98983 := rs (se 1 (by rfl) ⟨74237, by rfl⟩) R148475
theorem R99023 : Reach 99023 := rs (se 1 (by rfl) ⟨74267, by rfl⟩) R148535
theorem R99103 : Reach 99103 := rs (se 1 (by rfl) ⟨74327, by rfl⟩) R148655
theorem R328535 : Reach 328535 := rs (se 1 (by rfl) ⟨246401, by rfl⟩) R492803
theorem R230507 : Reach 230507 := rs (se 1 (by rfl) ⟨172880, by rfl⟩) R345761
theorem R165199 : Reach 165199 := rs (se 1 (by rfl) ⟨123899, by rfl⟩) R247799
theorem R623963 : Reach 623963 := rs (se 1 (by rfl) ⟨467972, by rfl⟩) R935945
theorem R951755 : Reach 951755 := rs (se 1 (by rfl) ⟨713816, by rfl⟩) R1427633
theorem R361979 : Reach 361979 := rs (se 1 (by rfl) ⟨271484, by rfl⟩) R542969
theorem R919259 : Reach 919259 := rs (se 1 (by rfl) ⟨689444, by rfl⟩) R1378889
theorem R427787 : Reach 427787 := rs (se 1 (by rfl) ⟨320840, by rfl⟩) R641681
theorem R329615 : Reach 329615 := rs (se 1 (by rfl) ⟨247211, by rfl⟩) R494423
theorem R395209 : Reach 395209 := rs (se 2 (by rfl) ⟨148203, by rfl⟩) R296407
theorem R166171 : Reach 166171 := rs (se 1 (by rfl) ⟨124628, by rfl⟩) R249257
theorem R5212511 : Reach 5212511 := rs (se 1 (by rfl) ⟨3909383, by rfl⟩) R7818767
theorem R264575 : Reach 264575 := rs (se 1 (by rfl) ⟨198431, by rfl⟩) R396863
theorem R166313 : Reach 166313 := rs (se 2 (by rfl) ⟨62367, by rfl⟩) R124735
theorem R166495 : Reach 166495 := rs (se 1 (by rfl) ⟨124871, by rfl⟩) R249743
theorem R527273 : Reach 527273 := rs (se 2 (by rfl) ⟨197727, by rfl⟩) R395455
theorem R166907 : Reach 166907 := rs (se 1 (by rfl) ⟨125180, by rfl⟩) R250361
theorem R1084751 : Reach 1084751 := rs (se 1 (by rfl) ⟨813563, by rfl⟩) R1627127
theorem R331343 : Reach 331343 := rs (se 1 (by rfl) ⟨248507, by rfl⟩) R497015
theorem R364607 : Reach 364607 := rs (se 1 (by rfl) ⟨273455, by rfl⟩) R546911
theorem R495719 : Reach 495719 := rs (se 1 (by rfl) ⟨371789, by rfl⟩) R743579
theorem R331883 : Reach 331883 := rs (se 1 (by rfl) ⟨248912, by rfl⟩) R497825
theorem R331937 : Reach 331937 := rs (se 2 (by rfl) ⟨124476, by rfl⟩) R248953
theorem R791329 : Reach 791329 := rs (se 2 (by rfl) ⟨296748, by rfl⟩) R593497
theorem R1479505 : Reach 1479505 := rs (se 2 (by rfl) ⟨554814, by rfl⟩) R1109629
theorem R136027 : Reach 136027 := rs (se 1 (by rfl) ⟨102020, by rfl⟩) R204041
theorem R365593 : Reach 365593 := rs (se 2 (by rfl) ⟨137097, by rfl⟩) R274195
theorem R333287 : Reach 333287 := rs (se 1 (by rfl) ⟨249965, by rfl⟩) R499931
theorem R267769 : Reach 267769 := rs (se 2 (by rfl) ⟨100413, by rfl⟩) R200827
theorem R333395 : Reach 333395 := rs (se 1 (by rfl) ⟨250046, by rfl⟩) R500093
theorem R366383 : Reach 366383 := rs (se 1 (by rfl) ⟨274787, by rfl⟩) R549575
theorem R333665 : Reach 333665 := rs (se 2 (by rfl) ⟨125124, by rfl⟩) R250249
theorem R368509 : Reach 368509 := rs (se 3 (by rfl) ⟨69095, by rfl⟩) R138191
theorem R794569 : Reach 794569 := rs (se 2 (by rfl) ⟨297963, by rfl⟩) R595927
theorem R369785 : Reach 369785 := rs (se 2 (by rfl) ⟨138669, by rfl⟩) R277339
theorem R500903 : Reach 500903 := rs (se 1 (by rfl) ⟨375677, by rfl⟩) R751355
theorem R107743 : Reach 107743 := rs (se 1 (by rfl) ⟨80807, by rfl⟩) R161615
theorem R501551 : Reach 501551 := rs (se 1 (by rfl) ⟨376163, by rfl⟩) R752327
theorem R730943 : Reach 730943 := rs (se 1 (by rfl) ⟨548207, by rfl⟩) R1096415
theorem R206783 : Reach 206783 := rs (se 1 (by rfl) ⟨155087, by rfl⟩) R310175
theorem R108571 : Reach 108571 := rs (se 1 (by rfl) ⟨81428, by rfl⟩) R162857
theorem R1092041 : Reach 1092041 := rs (se 2 (by rfl) ⟨409515, by rfl⟩) R819031
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R928655 : Reach 928655 := rs (se 1 (by rfl) ⟨696491, by rfl⟩) R1392983
theorem R470087 : Reach 470087 := rs (se 1 (by rfl) ⟨352565, by rfl⟩) R705131
theorem R371911 : Reach 371911 := rs (se 1 (by rfl) ⟨278933, by rfl⟩) R557867
theorem R110047 : Reach 110047 := rs (se 1 (by rfl) ⟨82535, by rfl⟩) R165071
theorem R142919 : Reach 142919 := rs (se 1 (by rfl) ⟨107189, by rfl⟩) R214379
theorem R143099 : Reach 143099 := rs (se 1 (by rfl) ⟨107324, by rfl⟩) R214649
theorem R700285 : Reach 700285 := rs (se 3 (by rfl) ⟨131303, by rfl⟩) R262607
theorem R110587 : Reach 110587 := rs (se 1 (by rfl) ⟨82940, by rfl⟩) R165881
theorem R110695 : Reach 110695 := rs (se 1 (by rfl) ⟨83021, by rfl⟩) R166043
theorem R372863 : Reach 372863 := rs (se 1 (by rfl) ⟨279647, by rfl⟩) R559295
theorem R110767 : Reach 110767 := rs (se 1 (by rfl) ⟨83075, by rfl⟩) R166151
theorem R143771 : Reach 143771 := rs (se 1 (by rfl) ⟨107828, by rfl⟩) R215657
theorem R373355 : Reach 373355 := rs (se 1 (by rfl) ⟨280016, by rfl⟩) R560033
theorem R1618717 : Reach 1618717 := rs (se 3 (by rfl) ⟨303509, by rfl⟩) R607019
theorem R144191 : Reach 144191 := rs (se 1 (by rfl) ⟨108143, by rfl⟩) R216287
theorem R111451 : Reach 111451 := rs (se 1 (by rfl) ⟨83588, by rfl⟩) R167177
theorem R144335 : Reach 144335 := rs (se 1 (by rfl) ⟨108251, by rfl⟩) R216503
theorem R504787 : Reach 504787 := rs (se 1 (by rfl) ⟨378590, by rfl⟩) R757181
theorem R144377 : Reach 144377 := rs (se 2 (by rfl) ⟨54141, by rfl⟩) R108283
theorem R144425 : Reach 144425 := rs (se 2 (by rfl) ⟨54159, by rfl⟩) R108319
theorem R144455 : Reach 144455 := rs (se 1 (by rfl) ⟨108341, by rfl⟩) R216683
theorem R242939 : Reach 242939 := rs (se 1 (by rfl) ⟨182204, by rfl⟩) R364409
theorem R144635 : Reach 144635 := rs (se 1 (by rfl) ⟨108476, by rfl⟩) R216953
theorem R15677509 : Reach 15677509 := rs (se 4 (by rfl) ⟨1469766, by rfl⟩) R2939533
theorem R7649579 : Reach 7649579 := rs (se 1 (by rfl) ⟨5737184, by rfl⟩) R11474369
theorem R145871 : Reach 145871 := rs (se 1 (by rfl) ⟨109403, by rfl⟩) R218807
theorem R145961 : Reach 145961 := rs (se 2 (by rfl) ⟨54735, by rfl⟩) R109471
theorem R408185 : Reach 408185 := rs (se 2 (by rfl) ⟨153069, by rfl⟩) R306139
theorem R244367 : Reach 244367 := rs (se 1 (by rfl) ⟨183275, by rfl⟩) R366551
theorem R473759 : Reach 473759 := rs (se 1 (by rfl) ⟨355319, by rfl⟩) R710639
theorem R146153 : Reach 146153 := rs (se 2 (by rfl) ⟨54807, by rfl⟩) R109615
theorem R244691 : Reach 244691 := rs (se 1 (by rfl) ⟨183518, by rfl⟩) R367037
theorem R146537 : Reach 146537 := rs (se 2 (by rfl) ⟨54951, by rfl⟩) R109903
theorem R146663 : Reach 146663 := rs (se 1 (by rfl) ⟨109997, by rfl⟩) R219995
theorem R245065 : Reach 245065 := rs (se 2 (by rfl) ⟨91899, by rfl⟩) R183799
theorem R2866747 : Reach 2866747 := rs (se 1 (by rfl) ⟨2150060, by rfl⟩) R4300121
theorem R147167 : Reach 147167 := rs (se 1 (by rfl) ⟨110375, by rfl⟩) R220751
theorem R147209 : Reach 147209 := rs (se 2 (by rfl) ⟨55203, by rfl⟩) R110407
theorem R737261 : Reach 737261 := rs (se 3 (by rfl) ⟨138236, by rfl⟩) R276473
theorem R147647 : Reach 147647 := rs (se 1 (by rfl) ⟨110735, by rfl⟩) R221471
theorem R148073 : Reach 148073 := rs (se 2 (by rfl) ⟨55527, by rfl⟩) R111055
theorem R148079 : Reach 148079 := rs (se 1 (by rfl) ⟨111059, by rfl⟩) R222119
theorem R1688363 : Reach 1688363 := rs (se 1 (by rfl) ⟨1266272, by rfl⟩) R2532545
theorem R214127 : Reach 214127 := rs (se 1 (by rfl) ⟨160595, by rfl⟩) R321191
theorem R246959 : Reach 246959 := rs (se 1 (by rfl) ⟨185219, by rfl⟩) R370439
theorem R312673 : Reach 312673 := rs (se 2 (by rfl) ⟨117252, by rfl⟩) R234505
theorem R1230187 : Reach 1230187 := rs (se 1 (by rfl) ⟨922640, by rfl⟩) R1845281
theorem R181673 : Reach 181673 := rs (se 2 (by rfl) ⟨68127, by rfl⟩) R136255
theorem R214523 : Reach 214523 := rs (se 1 (by rfl) ⟨160892, by rfl⟩) R321785
theorem R214559 : Reach 214559 := rs (se 1 (by rfl) ⟨160919, by rfl⟩) R321839
theorem R509503 : Reach 509503 := rs (se 1 (by rfl) ⟨382127, by rfl⟩) R764255
theorem R214703 : Reach 214703 := rs (se 1 (by rfl) ⟨161027, by rfl⟩) R322055
theorem R215135 : Reach 215135 := rs (se 1 (by rfl) ⟨161351, by rfl⟩) R322703
theorem R182569 : Reach 182569 := rs (se 2 (by rfl) ⟨68463, by rfl⟩) R136927
theorem R248143 : Reach 248143 := rs (se 1 (by rfl) ⟨186107, by rfl⟩) R372215
theorem R739691 : Reach 739691 := rs (se 1 (by rfl) ⟨554768, by rfl⟩) R1109537
theorem R215423 : Reach 215423 := rs (se 1 (by rfl) ⟨161567, by rfl⟩) R323135
theorem R149929 : Reach 149929 := rs (se 2 (by rfl) ⟨56223, by rfl⟩) R112447
theorem R4770515 : Reach 4770515 := rs (se 1 (by rfl) ⟨3577886, by rfl⟩) R7155773
theorem R215891 : Reach 215891 := rs (se 1 (by rfl) ⟨161918, by rfl⟩) R323837
theorem R183131 : Reach 183131 := rs (se 1 (by rfl) ⟨137348, by rfl⟩) R274697
theorem R183161 : Reach 183161 := rs (se 2 (by rfl) ⟨68685, by rfl⟩) R137371
theorem R183359 : Reach 183359 := rs (se 1 (by rfl) ⟨137519, by rfl⟩) R275039
theorem R216251 : Reach 216251 := rs (se 1 (by rfl) ⟨162188, by rfl⟩) R324377
theorem R314621 : Reach 314621 := rs (se 3 (by rfl) ⟨58991, by rfl⟩) R117983
theorem R216431 : Reach 216431 := rs (se 1 (by rfl) ⟨162323, by rfl⟩) R324647
theorem R413309 : Reach 413309 := rs (se 3 (by rfl) ⟨77495, by rfl⟩) R154991
theorem R315161 : Reach 315161 := rs (se 2 (by rfl) ⟨118185, by rfl⟩) R236371
theorem R184187 : Reach 184187 := rs (se 1 (by rfl) ⟨138140, by rfl⟩) R276281
theorem R217151 : Reach 217151 := rs (se 1 (by rfl) ⟨162863, by rfl⟩) R325727
theorem R217385 : Reach 217385 := rs (se 2 (by rfl) ⟨81519, by rfl⟩) R163039
theorem R184673 : Reach 184673 := rs (se 2 (by rfl) ⟨69252, by rfl⟩) R138505
theorem R414163 : Reach 414163 := rs (se 1 (by rfl) ⟨310622, by rfl⟩) R621245
theorem R217655 : Reach 217655 := rs (se 1 (by rfl) ⟨163241, by rfl⟩) R326483
theorem R250715 : Reach 250715 := rs (se 1 (by rfl) ⟨188036, by rfl⟩) R376073
theorem R217961 : Reach 217961 := rs (se 2 (by rfl) ⟨81735, by rfl⟩) R163471
theorem R250735 : Reach 250735 := rs (se 1 (by rfl) ⟨188051, by rfl⟩) R376103
theorem R218015 : Reach 218015 := rs (se 1 (by rfl) ⟨163511, by rfl⟩) R327023
theorem R218267 : Reach 218267 := rs (se 1 (by rfl) ⟨163700, by rfl⟩) R327401
theorem R218843 : Reach 218843 := rs (se 1 (by rfl) ⟨164132, by rfl⟩) R328265
theorem R218951 : Reach 218951 := rs (se 1 (by rfl) ⟨164213, by rfl⟩) R328427
theorem R153415 : Reach 153415 := rs (se 1 (by rfl) ⟨115061, by rfl⟩) R230123
theorem R219959 : Reach 219959 := rs (se 1 (by rfl) ⟨164969, by rfl⟩) R329939
theorem R187247 : Reach 187247 := rs (se 1 (by rfl) ⟨140435, by rfl⟩) R280871
theorem R220139 : Reach 220139 := rs (se 1 (by rfl) ⟨165104, by rfl⟩) R330209
theorem R351211 : Reach 351211 := rs (se 1 (by rfl) ⟨263408, by rfl⟩) R526817
theorem R417257 : Reach 417257 := rs (se 2 (by rfl) ⟨156471, by rfl⟩) R312943
theorem R220663 : Reach 220663 := rs (se 1 (by rfl) ⟨165497, by rfl⟩) R330995
theorem R187895 : Reach 187895 := rs (se 1 (by rfl) ⟨140921, by rfl⟩) R281843
theorem R941867 : Reach 941867 := rs (se 1 (by rfl) ⟨706400, by rfl⟩) R1412801
theorem R122735 : Reach 122735 := rs (se 1 (by rfl) ⟨92051, by rfl⟩) R184103
theorem R221039 : Reach 221039 := rs (se 1 (by rfl) ⟨165779, by rfl⟩) R331559
theorem R1269917 : Reach 1269917 := rs (se 3 (by rfl) ⟨238109, by rfl⟩) R476219
theorem R549119 : Reach 549119 := rs (se 1 (by rfl) ⟨411839, by rfl⟩) R823679
theorem R319955 : Reach 319955 := rs (se 1 (by rfl) ⟨239966, by rfl⟩) R479933
theorem R3007003 : Reach 3007003 := rs (se 1 (by rfl) ⟨2255252, by rfl⟩) R4510505
theorem R221723 : Reach 221723 := rs (se 1 (by rfl) ⟨166292, by rfl⟩) R332585
theorem R221903 : Reach 221903 := rs (se 1 (by rfl) ⟨166427, by rfl⟩) R332855
theorem R222281 : Reach 222281 := rs (se 2 (by rfl) ⟨83355, by rfl⟩) R166711
theorem R321299 : Reach 321299 := rs (se 1 (by rfl) ⟨240974, by rfl⟩) R481949
theorem R354239 : Reach 354239 := rs (se 1 (by rfl) ⟨265679, by rfl⟩) R531359
theorem R157631 : Reach 157631 := rs (se 1 (by rfl) ⟨118223, by rfl⟩) R236447
theorem R321515 : Reach 321515 := rs (se 1 (by rfl) ⟨241136, by rfl⟩) R482273
theorem R2320649 : Reach 2320649 := rs (se 2 (by rfl) ⟨870243, by rfl⟩) R1740487
theorem R420383 : Reach 420383 := rs (se 1 (by rfl) ⟨315287, by rfl⟩) R630575
theorem R1633459 : Reach 1633459 := rs (se 1 (by rfl) ⟨1225094, by rfl⟩) R2450189
theorem R1666493 : Reach 1666493 := rs (se 3 (by rfl) ⟨312467, by rfl⟩) R624935
theorem R323027 : Reach 323027 := rs (se 1 (by rfl) ⟨242270, by rfl⟩) R484541
theorem R290375 : Reach 290375 := rs (se 1 (by rfl) ⟨217781, by rfl⟩) R435563
theorem R323297 : Reach 323297 := rs (se 2 (by rfl) ⟨121236, by rfl⟩) R242473
theorem R552743 : Reach 552743 := rs (se 1 (by rfl) ⟨414557, by rfl⟩) R829115
theorem R356717 : Reach 356717 := rs (se 3 (by rfl) ⟨66884, by rfl⟩) R133769
theorem R1864225 : Reach 1864225 := rs (se 2 (by rfl) ⟨699084, by rfl⟩) R1398169
theorem R95135 : Reach 95135 := rs (se 1 (by rfl) ⟨71351, by rfl⟩) R142703
theorem R95215 : Reach 95215 := rs (se 1 (by rfl) ⟨71411, by rfl⟩) R142823
theorem R95303 : Reach 95303 := rs (se 1 (by rfl) ⟨71477, by rfl⟩) R142955
theorem R849035 : Reach 849035 := rs (se 1 (by rfl) ⟨636776, by rfl⟩) R1273553
theorem R95387 : Reach 95387 := rs (se 1 (by rfl) ⟨71540, by rfl⟩) R143081
theorem R95483 : Reach 95483 := rs (se 1 (by rfl) ⟨71612, by rfl⟩) R143225
theorem R95551 : Reach 95551 := rs (se 1 (by rfl) ⟨71663, by rfl⟩) R143327
theorem R488915 : Reach 488915 := rs (se 1 (by rfl) ⟨366686, by rfl⟩) R733373
theorem R325079 : Reach 325079 := rs (se 1 (by rfl) ⟨243809, by rfl⟩) R487619
theorem R95719 : Reach 95719 := rs (se 1 (by rfl) ⟨71789, by rfl⟩) R143579
theorem R95727 : Reach 95727 := rs (se 1 (by rfl) ⟨71795, by rfl⟩) R143591
theorem R816641 : Reach 816641 := rs (se 2 (by rfl) ⟨306240, by rfl⟩) R612481
theorem R95835 : Reach 95835 := rs (se 1 (by rfl) ⟨71876, by rfl⟩) R143753
theorem R95899 : Reach 95899 := rs (se 1 (by rfl) ⟨71924, by rfl⟩) R143849
theorem R95983 : Reach 95983 := rs (se 1 (by rfl) ⟨71987, by rfl⟩) R143975
theorem R96071 : Reach 96071 := rs (se 1 (by rfl) ⟨72053, by rfl⟩) R144107
theorem R96091 : Reach 96091 := rs (se 1 (by rfl) ⟨72068, by rfl⟩) R144137
theorem R96159 : Reach 96159 := rs (se 1 (by rfl) ⟨72119, by rfl⟩) R144239
theorem R358343 : Reach 358343 := rs (se 1 (by rfl) ⟨268757, by rfl⟩) R537515
theorem R554951 : Reach 554951 := rs (se 1 (by rfl) ⟨416213, by rfl⟩) R832427
theorem R96327 : Reach 96327 := rs (se 1 (by rfl) ⟨72245, by rfl⟩) R144491
theorem R915533 : Reach 915533 := rs (se 3 (by rfl) ⟨171662, by rfl⟩) R343325
theorem R96487 : Reach 96487 := rs (se 1 (by rfl) ⟨72365, by rfl⟩) R144731
theorem R555407 : Reach 555407 := rs (se 1 (by rfl) ⟨416555, by rfl⟩) R833111
theorem R96671 : Reach 96671 := rs (se 1 (by rfl) ⟨72503, by rfl⟩) R145007
theorem R96719 : Reach 96719 := rs (se 1 (by rfl) ⟨72539, by rfl⟩) R145079
theorem R96743 : Reach 96743 := rs (se 1 (by rfl) ⟨72557, by rfl⟩) R145115
theorem R96859 : Reach 96859 := rs (se 1 (by rfl) ⟨72644, by rfl⟩) R145289
theorem R1342097 : Reach 1342097 := rs (se 2 (by rfl) ⟨503286, by rfl⟩) R1006573
theorem R391837 : Reach 391837 := rs (se 3 (by rfl) ⟨73469, by rfl⟩) R146939
theorem R96927 : Reach 96927 := rs (se 1 (by rfl) ⟨72695, by rfl⟩) R145391
theorem R162607 : Reach 162607 := rs (se 1 (by rfl) ⟨121955, by rfl⟩) R243911
theorem R97095 : Reach 97095 := rs (se 1 (by rfl) ⟨72821, by rfl⟩) R145643
theorem R97135 : Reach 97135 := rs (se 1 (by rfl) ⟨72851, by rfl⟩) R145703
theorem R97191 : Reach 97191 := rs (se 1 (by rfl) ⟨72893, by rfl⟩) R145787
theorem R97371 : Reach 97371 := rs (se 1 (by rfl) ⟨73028, by rfl⟩) R146057
theorem R97487 : Reach 97487 := rs (se 1 (by rfl) ⟨73115, by rfl⟩) R146231
theorem R195809 : Reach 195809 := rs (se 2 (by rfl) ⟨73428, by rfl⟩) R146857
theorem R97511 : Reach 97511 := rs (se 1 (by rfl) ⟨73133, by rfl⟩) R146267
theorem R97607 : Reach 97607 := rs (se 1 (by rfl) ⟨73205, by rfl⟩) R146411
theorem R97743 : Reach 97743 := rs (se 1 (by rfl) ⟨73307, by rfl⟩) R146615
theorem R1244645 : Reach 1244645 := rs (se 4 (by rfl) ⟨116685, by rfl⟩) R233371
theorem R97903 : Reach 97903 := rs (se 1 (by rfl) ⟨73427, by rfl⟩) R146855
theorem R97959 : Reach 97959 := rs (se 1 (by rfl) ⟨73469, by rfl⟩) R146939
theorem R491183 : Reach 491183 := rs (se 1 (by rfl) ⟨368387, by rfl⟩) R736775
theorem R1670867 : Reach 1670867 := rs (se 1 (by rfl) ⟨1253150, by rfl⟩) R2506301
theorem R163559 : Reach 163559 := rs (se 1 (by rfl) ⟨122669, by rfl⟩) R245339
theorem R98023 : Reach 98023 := rs (se 1 (by rfl) ⟨73517, by rfl⟩) R147035
theorem R98079 : Reach 98079 := rs (se 1 (by rfl) ⟨73559, by rfl⟩) R147119
theorem R5668703 : Reach 5668703 := rs (se 1 (by rfl) ⟨4251527, by rfl⟩) R8503055
theorem R98159 : Reach 98159 := rs (se 1 (by rfl) ⟨73619, by rfl⟩) R147239
theorem R196519 : Reach 196519 := rs (se 1 (by rfl) ⟨147389, by rfl⟩) R294779
theorem R98215 : Reach 98215 := rs (se 1 (by rfl) ⟨73661, by rfl⟩) R147323
theorem R98431 : Reach 98431 := rs (se 1 (by rfl) ⟨73823, by rfl⟩) R147647
theorem R98715 : Reach 98715 := rs (se 1 (by rfl) ⟨74036, by rfl⟩) R148073
theorem R98719 : Reach 98719 := rs (se 1 (by rfl) ⟨74039, by rfl⟩) R148079
theorem R2097575 : Reach 2097575 := rs (se 1 (by rfl) ⟨1573181, by rfl⟩) R3146363
theorem R164639 : Reach 164639 := rs (se 1 (by rfl) ⟨123479, by rfl⟩) R246959
theorem R853213 : Reach 853213 := rs (se 3 (by rfl) ⟨159977, by rfl⟩) R319955
theorem R3475007 : Reach 3475007 := rs (se 1 (by rfl) ⟨2606255, by rfl⟩) R5212511
theorem R493127 : Reach 493127 := rs (se 1 (by rfl) ⟨369845, by rfl⟩) R739691
theorem R3180343 : Reach 3180343 := rs (se 1 (by rfl) ⟨2385257, by rfl⟩) R4770515
theorem R1640249 : Reach 1640249 := rs (se 2 (by rfl) ⟨615093, by rfl⟩) R1230187
theorem R723167 : Reach 723167 := rs (se 1 (by rfl) ⟨542375, by rfl⟩) R1084751
theorem R526945 : Reach 526945 := rs (se 2 (by rfl) ⟨197604, by rfl⟩) R395209
theorem R330479 : Reach 330479 := rs (se 1 (by rfl) ⟨247859, by rfl⟩) R495719
theorem R330857 : Reach 330857 := rs (se 2 (by rfl) ⟨124071, by rfl⟩) R248143
theorem R167143 : Reach 167143 := rs (se 1 (by rfl) ⟨125357, by rfl⟩) R250715
theorem R495881 : Reach 495881 := rs (se 2 (by rfl) ⟨185955, by rfl⟩) R371911
theorem R627911 : Reach 627911 := rs (se 1 (by rfl) ⟨470933, by rfl⟩) R941867
theorem R366079 : Reach 366079 := rs (se 1 (by rfl) ⟨274559, by rfl⟩) R549119
theorem R333935 : Reach 333935 := rs (se 1 (by rfl) ⟨250451, by rfl⟩) R500903
theorem R1055105 : Reach 1055105 := rs (se 2 (by rfl) ⟨395664, by rfl⟩) R791329
theorem R1972673 : Reach 1972673 := rs (se 2 (by rfl) ⟨739752, by rfl⟩) R1479505
theorem R334313 : Reach 334313 := rs (se 2 (by rfl) ⟨125367, by rfl⟩) R250735
theorem R334367 : Reach 334367 := rs (se 1 (by rfl) ⟨250775, by rfl⟩) R501551
theorem R137855 : Reach 137855 := rs (se 1 (by rfl) ⟨103391, by rfl⟩) R206783
theorem R236159 : Reach 236159 := rs (se 1 (by rfl) ⟨177119, by rfl⟩) R354239
theorem R1547099 : Reach 1547099 := rs (se 1 (by rfl) ⟨1160324, by rfl⟩) R2320649
theorem R728027 : Reach 728027 := rs (se 1 (by rfl) ⟨546020, by rfl⟩) R1092041
theorem R204553 : Reach 204553 := rs (se 2 (by rfl) ⟨76707, by rfl⟩) R153415
theorem R368495 : Reach 368495 := rs (se 1 (by rfl) ⟨276371, by rfl⟩) R552743
theorem R237811 : Reach 237811 := rs (se 1 (by rfl) ⟨178358, by rfl⟩) R356717
theorem R566023 : Reach 566023 := rs (se 1 (by rfl) ⟨424517, by rfl⟩) R849035
theorem R238895 : Reach 238895 := rs (se 1 (by rfl) ⟨179171, by rfl⟩) R358343
theorem R369967 : Reach 369967 := rs (se 1 (by rfl) ⟨277475, by rfl⟩) R554951
theorem R468281 : Reach 468281 := rs (se 2 (by rfl) ⟨175605, by rfl⟩) R351211
theorem R370271 : Reach 370271 := rs (se 1 (by rfl) ⟨277703, by rfl⟩) R555407
theorem R272123 : Reach 272123 := rs (se 1 (by rfl) ⟨204092, by rfl⟩) R408185
theorem R894731 : Reach 894731 := rs (se 1 (by rfl) ⟨671048, by rfl⟩) R1342097
theorem R829763 : Reach 829763 := rs (se 1 (by rfl) ⟨622322, by rfl⟩) R1244645
theorem R109039 : Reach 109039 := rs (se 1 (by rfl) ⟨81779, by rfl⟩) R163559
theorem R3779135 : Reach 3779135 := rs (se 1 (by rfl) ⟨2834351, by rfl⟩) R5668703
theorem R1059425 : Reach 1059425 := rs (se 2 (by rfl) ⟨397284, by rfl⟩) R794569
theorem R994301 : Reach 994301 := rs (se 3 (by rfl) ⟨186431, by rfl⟩) R372863
theorem R1125575 : Reach 1125575 := rs (se 1 (by rfl) ⟨844181, by rfl⟩) R1688363
theorem R4009337 : Reach 4009337 := rs (se 2 (by rfl) ⟨1503501, by rfl⟩) R3007003
theorem R142751 : Reach 142751 := rs (se 1 (by rfl) ⟨107063, by rfl⟩) R214127
theorem R241319 : Reach 241319 := rs (se 1 (by rfl) ⟨180989, by rfl⟩) R361979
theorem R143015 : Reach 143015 := rs (se 1 (by rfl) ⟨107261, by rfl⟩) R214523
theorem R143039 : Reach 143039 := rs (se 1 (by rfl) ⟨107279, by rfl⟩) R214559
theorem R143135 : Reach 143135 := rs (se 1 (by rfl) ⟨107351, by rfl⟩) R214703
theorem R143423 : Reach 143423 := rs (se 1 (by rfl) ⟨107567, by rfl⟩) R215135
theorem R143615 : Reach 143615 := rs (se 1 (by rfl) ⟨107711, by rfl⟩) R215423
theorem R176383 : Reach 176383 := rs (se 1 (by rfl) ⟨132287, by rfl⟩) R264575
theorem R110875 : Reach 110875 := rs (se 1 (by rfl) ⟨83156, by rfl⟩) R166313
theorem R143657 : Reach 143657 := rs (se 2 (by rfl) ⟨53871, by rfl⟩) R107743
theorem R143927 : Reach 143927 := rs (se 1 (by rfl) ⟨107945, by rfl⟩) R215891
theorem R111271 : Reach 111271 := rs (se 1 (by rfl) ⟨83453, by rfl⟩) R166907
theorem R144167 : Reach 144167 := rs (se 1 (by rfl) ⟨108125, by rfl⟩) R216251
theorem R209747 : Reach 209747 := rs (se 1 (by rfl) ⟨157310, by rfl⟩) R314621
theorem R799621 : Reach 799621 := rs (se 4 (by rfl) ⟨74964, by rfl⟩) R149929
theorem R144287 : Reach 144287 := rs (se 1 (by rfl) ⟨108215, by rfl⟩) R216431
theorem R210107 : Reach 210107 := rs (se 1 (by rfl) ⟨157580, by rfl⟩) R315161
theorem R144761 : Reach 144761 := rs (se 2 (by rfl) ⟨54285, by rfl⟩) R108571
theorem R243071 : Reach 243071 := rs (se 1 (by rfl) ⟨182303, by rfl⟩) R364607
theorem R144767 : Reach 144767 := rs (se 1 (by rfl) ⟨108575, by rfl⟩) R217151
theorem R144923 : Reach 144923 := rs (se 1 (by rfl) ⟨108692, by rfl⟩) R217385
theorem R145103 : Reach 145103 := rs (se 1 (by rfl) ⟨108827, by rfl⟩) R217655
theorem R243425 : Reach 243425 := rs (se 2 (by rfl) ⟨91284, by rfl⟩) R182569
theorem R145307 : Reach 145307 := rs (se 1 (by rfl) ⟨108980, by rfl⟩) R217961
theorem R145343 : Reach 145343 := rs (se 1 (by rfl) ⟨109007, by rfl⟩) R218015
theorem R145511 : Reach 145511 := rs (se 1 (by rfl) ⟨109133, by rfl⟩) R218267
theorem R145895 : Reach 145895 := rs (se 1 (by rfl) ⟨109421, by rfl⟩) R218843
theorem R244255 : Reach 244255 := rs (se 1 (by rfl) ⟨183191, by rfl⟩) R366383
theorem R145967 : Reach 145967 := rs (se 1 (by rfl) ⟨109475, by rfl⟩) R218951
theorem R2177945 : Reach 2177945 := rs (se 2 (by rfl) ⟨816729, by rfl⟩) R1633459
theorem R146639 : Reach 146639 := rs (se 1 (by rfl) ⟨109979, by rfl⟩) R219959
theorem R146729 : Reach 146729 := rs (se 2 (by rfl) ⟨55023, by rfl⟩) R110047
theorem R146759 : Reach 146759 := rs (se 1 (by rfl) ⟨110069, by rfl⟩) R220139
theorem R278171 : Reach 278171 := rs (se 1 (by rfl) ⟨208628, by rfl⟩) R417257
theorem R933713 : Reach 933713 := rs (se 2 (by rfl) ⟨350142, by rfl⟩) R700285
theorem R147359 : Reach 147359 := rs (se 1 (by rfl) ⟨110519, by rfl⟩) R221039
theorem R147449 : Reach 147449 := rs (se 2 (by rfl) ⟨55293, by rfl⟩) R110587
theorem R147593 : Reach 147593 := rs (se 2 (by rfl) ⟨55347, by rfl⟩) R110695
theorem R147689 : Reach 147689 := rs (se 2 (by rfl) ⟨55383, by rfl⟩) R110767
theorem R147815 : Reach 147815 := rs (se 1 (by rfl) ⟨110861, by rfl⟩) R221723
theorem R147935 : Reach 147935 := rs (se 1 (by rfl) ⟨110951, by rfl⟩) R221903
theorem R148187 : Reach 148187 := rs (se 1 (by rfl) ⟨111140, by rfl⟩) R222281
theorem R246523 : Reach 246523 := rs (se 1 (by rfl) ⟨184892, by rfl⟩) R369785
theorem R181369 : Reach 181369 := rs (se 2 (by rfl) ⟨68013, by rfl⟩) R136027
theorem R148601 : Reach 148601 := rs (se 2 (by rfl) ⟨55725, by rfl⟩) R111451
theorem R214199 : Reach 214199 := rs (se 1 (by rfl) ⟨160649, by rfl⟩) R321299
theorem R673049 : Reach 673049 := rs (se 2 (by rfl) ⟨252393, by rfl⟩) R504787
theorem R214343 : Reach 214343 := rs (se 1 (by rfl) ⟨160757, by rfl⟩) R321515
theorem R280255 : Reach 280255 := rs (se 1 (by rfl) ⟨210191, by rfl⟩) R420383
theorem R313391 : Reach 313391 := rs (se 1 (by rfl) ⟨235043, by rfl⟩) R470087
theorem R215351 : Reach 215351 := rs (se 1 (by rfl) ⟨161513, by rfl⟩) R323027
theorem R215531 : Reach 215531 := rs (se 1 (by rfl) ⟨161648, by rfl⟩) R323297
theorem R1428101 : Reach 1428101 := rs (se 4 (by rfl) ⟨133884, by rfl⟩) R267769
theorem R248903 : Reach 248903 := rs (se 1 (by rfl) ⟨186677, by rfl⟩) R373355
theorem R216719 : Reach 216719 := rs (se 1 (by rfl) ⟨162539, by rfl⟩) R325079
theorem R544427 : Reach 544427 := rs (se 1 (by rfl) ⟨408320, by rfl⟩) R816641
theorem R216809 : Reach 216809 := rs (se 2 (by rfl) ⟨81303, by rfl⟩) R162607
theorem R610355 : Reach 610355 := rs (se 1 (by rfl) ⟨457766, by rfl⟩) R915533
theorem R5099719 : Reach 5099719 := rs (se 1 (by rfl) ⟨3824789, by rfl⟩) R7649579
theorem R1102157 : Reach 1102157 := rs (se 3 (by rfl) ⟨206654, by rfl⟩) R413309
theorem R315839 : Reach 315839 := rs (se 1 (by rfl) ⟨236879, by rfl⟩) R473759
theorem R3822329 : Reach 3822329 := rs (se 2 (by rfl) ⟨1433373, by rfl⟩) R2866747
theorem R219023 : Reach 219023 := rs (se 1 (by rfl) ⟨164267, by rfl⟩) R328535
theorem R153671 : Reach 153671 := rs (se 1 (by rfl) ⟨115253, by rfl⟩) R230507
theorem R415975 : Reach 415975 := rs (se 1 (by rfl) ⟨311981, by rfl⟩) R623963
theorem R121115 : Reach 121115 := rs (se 1 (by rfl) ⟨90836, by rfl⟩) R181673
theorem R612839 : Reach 612839 := rs (se 1 (by rfl) ⟨459629, by rfl⟩) R919259
theorem R285191 : Reach 285191 := rs (se 1 (by rfl) ⟨213893, by rfl⟩) R427787
theorem R219743 : Reach 219743 := rs (se 1 (by rfl) ⟨164807, by rfl⟩) R329615
theorem R220265 : Reach 220265 := rs (se 2 (by rfl) ⟨82599, by rfl⟩) R165199
theorem R416897 : Reach 416897 := rs (se 2 (by rfl) ⟨156336, by rfl⟩) R312673
theorem R122087 : Reach 122087 := rs (se 1 (by rfl) ⟨91565, by rfl⟩) R183131
theorem R351515 : Reach 351515 := rs (se 1 (by rfl) ⟨263636, by rfl⟩) R527273
theorem R122239 : Reach 122239 := rs (se 1 (by rfl) ⟨91679, by rfl⟩) R183359
theorem R679337 : Reach 679337 := rs (se 2 (by rfl) ⟨254751, by rfl⟩) R509503
theorem R2088629 : Reach 2088629 := rs (se 5 (by rfl) ⟨97904, by rfl⟩) R195809
theorem R220895 : Reach 220895 := rs (se 1 (by rfl) ⟨165671, by rfl⟩) R331343
theorem R122791 : Reach 122791 := rs (se 1 (by rfl) ⟨92093, by rfl⟩) R184187
theorem R221255 : Reach 221255 := rs (se 1 (by rfl) ⟨165941, by rfl⟩) R331883
theorem R221291 : Reach 221291 := rs (se 1 (by rfl) ⟨165968, by rfl⟩) R331937
theorem R123115 : Reach 123115 := rs (se 1 (by rfl) ⟨92336, by rfl⟩) R184673
theorem R221561 : Reach 221561 := rs (se 2 (by rfl) ⟨83085, by rfl⟩) R166171
theorem R221993 : Reach 221993 := rs (se 2 (by rfl) ⟨83247, by rfl⟩) R166495
theorem R222191 : Reach 222191 := rs (se 1 (by rfl) ⟨166643, by rfl⟩) R333287
theorem R222263 : Reach 222263 := rs (se 1 (by rfl) ⟨166697, by rfl⟩) R333395
theorem R222443 : Reach 222443 := rs (se 1 (by rfl) ⟨166832, by rfl⟩) R333665
theorem R124831 : Reach 124831 := rs (se 1 (by rfl) ⟨93623, by rfl⟩) R187247
theorem R10152053 : Reach 10152053 := rs (se 5 (by rfl) ⟨475877, by rfl⟩) R951755
theorem R125263 : Reach 125263 := rs (se 1 (by rfl) ⟨93947, by rfl⟩) R187895
theorem R420349 : Reach 420349 := rs (se 3 (by rfl) ⟨78815, by rfl⟩) R157631
theorem R846611 : Reach 846611 := rs (se 1 (by rfl) ⟨634958, by rfl⟩) R1269917
theorem R552217 : Reach 552217 := rs (se 2 (by rfl) ⟨207081, by rfl⟩) R414163
theorem R2485633 : Reach 2485633 := rs (se 2 (by rfl) ⟨932112, by rfl⟩) R1864225
theorem R2158289 : Reach 2158289 := rs (se 2 (by rfl) ⟨809358, by rfl⟩) R1618717
theorem R487295 : Reach 487295 := rs (se 1 (by rfl) ⟨365471, by rfl⟩) R730943
theorem R487457 : Reach 487457 := rs (se 2 (by rfl) ⟨182796, by rfl⟩) R365593
theorem R619103 : Reach 619103 := rs (se 1 (by rfl) ⟨464327, by rfl⟩) R928655
theorem R553661 : Reach 553661 := rs (se 3 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R1110995 : Reach 1110995 := rs (se 1 (by rfl) ⟨833246, by rfl⟩) R1666493
theorem R488429 : Reach 488429 := rs (se 3 (by rfl) ⟨91580, by rfl⟩) R183161
theorem R95279 : Reach 95279 := rs (se 1 (by rfl) ⟨71459, by rfl⟩) R142919
theorem R193583 : Reach 193583 := rs (se 1 (by rfl) ⟨145187, by rfl⟩) R290375
theorem R95399 : Reach 95399 := rs (se 1 (by rfl) ⟨71549, by rfl⟩) R143099
theorem R1176869 : Reach 1176869 := rs (se 4 (by rfl) ⟨110331, by rfl⟩) R220663
theorem R20903345 : Reach 20903345 := rs (se 2 (by rfl) ⟨7838754, by rfl⟩) R15677509
theorem R95847 : Reach 95847 := rs (se 1 (by rfl) ⟨71885, by rfl⟩) R143771
theorem R96127 : Reach 96127 := rs (se 1 (by rfl) ⟨72095, by rfl⟩) R144191
theorem R96223 : Reach 96223 := rs (se 1 (by rfl) ⟨72167, by rfl⟩) R144335
theorem R96251 : Reach 96251 := rs (se 1 (by rfl) ⟨72188, by rfl⟩) R144377
theorem R96283 : Reach 96283 := rs (se 1 (by rfl) ⟨72212, by rfl⟩) R144425
theorem R96303 : Reach 96303 := rs (se 1 (by rfl) ⟨72227, by rfl⟩) R144455
theorem R161959 : Reach 161959 := rs (se 1 (by rfl) ⟨121469, by rfl⟩) R242939
theorem R96423 : Reach 96423 := rs (se 1 (by rfl) ⟨72317, by rfl⟩) R144635
theorem R522449 : Reach 522449 := rs (se 2 (by rfl) ⟨195918, by rfl⟩) R391837
theorem R325943 : Reach 325943 := rs (se 1 (by rfl) ⟨244457, by rfl⟩) R488915
theorem R97247 : Reach 97247 := rs (se 1 (by rfl) ⟨72935, by rfl⟩) R145871
theorem R97307 : Reach 97307 := rs (se 1 (by rfl) ⟨72980, by rfl⟩) R145961
theorem R162911 : Reach 162911 := rs (se 1 (by rfl) ⟨122183, by rfl⟩) R244367
theorem R326753 : Reach 326753 := rs (se 2 (by rfl) ⟨122532, by rfl⟩) R245065
theorem R97435 : Reach 97435 := rs (se 1 (by rfl) ⟨73076, by rfl⟩) R146153
theorem R163127 : Reach 163127 := rs (se 1 (by rfl) ⟨122345, by rfl⟩) R244691
theorem R97691 : Reach 97691 := rs (se 1 (by rfl) ⟨73268, by rfl⟩) R146537
theorem R97775 : Reach 97775 := rs (se 1 (by rfl) ⟨73331, by rfl⟩) R146663
theorem R327293 : Reach 327293 := rs (se 3 (by rfl) ⟨61367, by rfl⟩) R122735
theorem R327455 : Reach 327455 := rs (se 1 (by rfl) ⟨245591, by rfl⟩) R491183
theorem R1113911 : Reach 1113911 := rs (se 1 (by rfl) ⟨835433, by rfl⟩) R1670867
theorem R98111 : Reach 98111 := rs (se 1 (by rfl) ⟨73583, by rfl⟩) R147167
theorem R491345 : Reach 491345 := rs (se 2 (by rfl) ⟨184254, by rfl⟩) R368509
theorem R98139 : Reach 98139 := rs (se 1 (by rfl) ⟨73604, by rfl⟩) R147209
theorem R262025 : Reach 262025 := rs (se 2 (by rfl) ⟨98259, by rfl⟩) R196519
theorem R491507 : Reach 491507 := rs (se 1 (by rfl) ⟨368630, by rfl⟩) R737261
theorem R98395 : Reach 98395 := rs (se 1 (by rfl) ⟨73796, by rfl⟩) R147593
theorem R98459 : Reach 98459 := rs (se 1 (by rfl) ⟨73844, by rfl⟩) R147689
theorem R98543 : Reach 98543 := rs (se 1 (by rfl) ⟨73907, by rfl⟩) R147815
theorem R164153 : Reach 164153 := rs (se 2 (by rfl) ⟨61557, by rfl⟩) R123115
theorem R98623 : Reach 98623 := rs (se 1 (by rfl) ⟨73967, by rfl⟩) R147935
theorem R98791 : Reach 98791 := rs (se 1 (by rfl) ⟨74093, by rfl⟩) R148187
theorem R99067 : Reach 99067 := rs (se 1 (by rfl) ⟨74300, by rfl⟩) R148601
theorem R328697 : Reach 328697 := rs (se 2 (by rfl) ⟨123261, by rfl⟩) R246523
theorem R754697 : Reach 754697 := rs (se 2 (by rfl) ⟨283011, by rfl⟩) R566023
theorem R328751 : Reach 328751 := rs (se 1 (by rfl) ⟨246563, by rfl⟩) R493127
theorem R493289 : Reach 493289 := rs (se 2 (by rfl) ⟨184983, by rfl⟩) R369967
theorem R952067 : Reach 952067 := rs (se 1 (by rfl) ⟨714050, by rfl⟩) R1428101
theorem R10192877 : Reach 10192877 := rs (se 3 (by rfl) ⟨1911164, by rfl⟩) R3822329
theorem R165935 : Reach 165935 := rs (se 1 (by rfl) ⟨124451, by rfl⟩) R248903
theorem R559325 : Reach 559325 := rs (se 3 (by rfl) ⟨104873, by rfl⟩) R209747
theorem R362951 : Reach 362951 := rs (se 1 (by rfl) ⟨272213, by rfl⟩) R544427
theorem R166441 : Reach 166441 := rs (se 2 (by rfl) ⟨62415, by rfl⟩) R124831
theorem R330587 : Reach 330587 := rs (se 1 (by rfl) ⟨247940, by rfl⟩) R495881
theorem R98299 : Reach 98299 := rs (se 1 (by rfl) ⟨73724, by rfl⟩) R147449
theorem R167017 : Reach 167017 := rs (se 2 (by rfl) ⟨62631, by rfl⟩) R125263
theorem R560465 : Reach 560465 := rs (se 2 (by rfl) ⟨210174, by rfl⟩) R420349
theorem R1315115 : Reach 1315115 := rs (se 1 (by rfl) ⟨986336, by rfl⟩) R1972673
theorem R3314177 : Reach 3314177 := rs (se 2 (by rfl) ⟨1242816, by rfl⟩) R2485633
theorem R4264645 : Reach 4264645 := rs (se 4 (by rfl) ⟨399810, by rfl⟩) R799621
theorem R234343 : Reach 234343 := rs (se 1 (by rfl) ⟨175757, by rfl⟩) R351515
theorem R367613 : Reach 367613 := rs (se 3 (by rfl) ⟨68927, by rfl⟩) R137855
theorem R564407 : Reach 564407 := rs (se 1 (by rfl) ⟨423305, by rfl⟩) R846611
theorem R662867 : Reach 662867 := rs (se 1 (by rfl) ⟨497150, by rfl⟩) R994301
theorem R369107 : Reach 369107 := rs (se 1 (by rfl) ⟨276830, by rfl⟩) R553661
theorem R140071 : Reach 140071 := rs (se 1 (by rfl) ⟨105053, by rfl⟩) R210107
theorem R13935563 : Reach 13935563 := rs (se 1 (by rfl) ⟨10451672, by rfl⟩) R20903345
theorem R1451963 : Reach 1451963 := rs (se 1 (by rfl) ⟨1088972, by rfl⟩) R2177945
theorem R108607 : Reach 108607 := rs (se 1 (by rfl) ⟨81455, by rfl⟩) R162911
theorem R108751 : Reach 108751 := rs (se 1 (by rfl) ⟨81563, by rfl⟩) R163127
theorem R272737 : Reach 272737 := rs (se 2 (by rfl) ⟨102276, by rfl⟩) R204553
theorem R174683 : Reach 174683 := rs (se 1 (by rfl) ⟨131012, by rfl⟩) R262025
theorem R109759 : Reach 109759 := rs (se 1 (by rfl) ⟨82319, by rfl⟩) R164639
theorem R142799 : Reach 142799 := rs (se 1 (by rfl) ⟨107099, by rfl⟩) R214199
theorem R142895 : Reach 142895 := rs (se 1 (by rfl) ⟨107171, by rfl⟩) R214343
theorem R1093499 : Reach 1093499 := rs (se 1 (by rfl) ⟨820124, by rfl⟩) R1640249
theorem R208927 : Reach 208927 := rs (se 1 (by rfl) ⟨156695, by rfl⟩) R313391
theorem R241825 : Reach 241825 := rs (se 2 (by rfl) ⟨90684, by rfl⟩) R181369
theorem R143567 : Reach 143567 := rs (se 1 (by rfl) ⟨107675, by rfl⟩) R215351
theorem R1650941 : Reach 1650941 := rs (se 3 (by rfl) ⟨309551, by rfl⟩) R619103
theorem R143687 : Reach 143687 := rs (se 1 (by rfl) ⟨107765, by rfl⟩) R215531
theorem R373673 : Reach 373673 := rs (se 2 (by rfl) ⟨140127, by rfl⟩) R280255
theorem R4240457 : Reach 4240457 := rs (se 2 (by rfl) ⟨1590171, by rfl⟩) R3180343
theorem R144479 : Reach 144479 := rs (se 1 (by rfl) ⟨108359, by rfl⟩) R216719
theorem R144539 : Reach 144539 := rs (se 1 (by rfl) ⟨108404, by rfl⟩) R216809
theorem R406903 : Reach 406903 := rs (se 1 (by rfl) ⟨305177, by rfl⟩) R610355
theorem R734771 : Reach 734771 := rs (se 1 (by rfl) ⟨551078, by rfl⟩) R1102157
theorem R145385 : Reach 145385 := rs (se 2 (by rfl) ⟨54519, by rfl⟩) R109039
theorem R702593 : Reach 702593 := rs (se 2 (by rfl) ⟨263472, by rfl⟩) R526945
theorem R146015 : Reach 146015 := rs (se 1 (by rfl) ⟨109511, by rfl⟩) R219023
theorem R703403 : Reach 703403 := rs (se 1 (by rfl) ⟨527552, by rfl⟩) R1055105
theorem R408559 : Reach 408559 := rs (se 1 (by rfl) ⟨306419, by rfl⟩) R612839
theorem R736289 : Reach 736289 := rs (se 2 (by rfl) ⟨276108, by rfl⟩) R552217
theorem R146495 : Reach 146495 := rs (se 1 (by rfl) ⟨109871, by rfl⟩) R219743
theorem R1031399 : Reach 1031399 := rs (se 1 (by rfl) ⟨773549, by rfl⟩) R1547099
theorem R146843 : Reach 146843 := rs (se 1 (by rfl) ⟨110132, by rfl⟩) R220265
theorem R277931 : Reach 277931 := rs (se 1 (by rfl) ⟨208448, by rfl⟩) R416897
theorem R1392419 : Reach 1392419 := rs (se 1 (by rfl) ⟨1044314, by rfl⟩) R2088629
theorem R147263 : Reach 147263 := rs (se 1 (by rfl) ⟨110447, by rfl⟩) R220895
theorem R245663 : Reach 245663 := rs (se 1 (by rfl) ⟨184247, by rfl⟩) R368495
theorem R147503 : Reach 147503 := rs (se 1 (by rfl) ⟨110627, by rfl⟩) R221255
theorem R147527 : Reach 147527 := rs (se 1 (by rfl) ⟨110645, by rfl⟩) R221291
theorem R409789 : Reach 409789 := rs (se 3 (by rfl) ⟨76835, by rfl⟩) R153671
theorem R147707 : Reach 147707 := rs (se 1 (by rfl) ⟨110780, by rfl⟩) R221561
theorem R6799625 : Reach 6799625 := rs (se 2 (by rfl) ⟨2549859, by rfl⟩) R5099719
theorem R147833 : Reach 147833 := rs (se 2 (by rfl) ⟨55437, by rfl⟩) R110875
theorem R147995 : Reach 147995 := rs (se 1 (by rfl) ⟨110996, by rfl⟩) R221993
theorem R148127 : Reach 148127 := rs (se 1 (by rfl) ⟨111095, by rfl⟩) R222191
theorem R148175 : Reach 148175 := rs (se 1 (by rfl) ⟨111131, by rfl⟩) R222263
theorem R148295 : Reach 148295 := rs (se 1 (by rfl) ⟨111221, by rfl⟩) R222443
theorem R312187 : Reach 312187 := rs (se 1 (by rfl) ⟨234140, by rfl⟩) R468281
theorem R148361 : Reach 148361 := rs (se 2 (by rfl) ⟨55635, by rfl⟩) R111271
theorem R246847 : Reach 246847 := rs (se 1 (by rfl) ⟨185135, by rfl⟩) R370271
theorem R181415 : Reach 181415 := rs (se 1 (by rfl) ⟨136061, by rfl⟩) R272123
theorem R6768035 : Reach 6768035 := rs (se 1 (by rfl) ⟨5076026, by rfl⟩) R10152053
theorem R706283 : Reach 706283 := rs (se 1 (by rfl) ⟨529712, by rfl⟩) R1059425
theorem R2672891 : Reach 2672891 := rs (se 1 (by rfl) ⟨2004668, by rfl⟩) R4009337
theorem R215945 : Reach 215945 := rs (se 2 (by rfl) ⟨80979, by rfl⟩) R161959
theorem R740663 : Reach 740663 := rs (se 1 (by rfl) ⟨555497, by rfl⟩) R1110995
theorem R348299 : Reach 348299 := rs (se 1 (by rfl) ⟨261224, by rfl⟩) R522449
theorem R217295 : Reach 217295 := rs (se 1 (by rfl) ⟨162971, by rfl⟩) R325943
theorem R217835 : Reach 217835 := rs (se 1 (by rfl) ⟨163376, by rfl⟩) R326753
theorem R218195 : Reach 218195 := rs (se 1 (by rfl) ⟨163646, by rfl⟩) R327293
theorem R185447 : Reach 185447 := rs (se 1 (by rfl) ⟨139085, by rfl⟩) R278171
theorem R218303 : Reach 218303 := rs (se 1 (by rfl) ⟨163727, by rfl⟩) R327455
theorem R742607 : Reach 742607 := rs (se 1 (by rfl) ⟨556955, by rfl⟩) R1113911
theorem R1398383 : Reach 1398383 := rs (se 1 (by rfl) ⟨1048787, by rfl⟩) R2097575
theorem R317081 : Reach 317081 := rs (se 2 (by rfl) ⟨118905, by rfl⟩) R237811
theorem R2316671 : Reach 2316671 := rs (se 1 (by rfl) ⟨1737503, by rfl⟩) R3475007
theorem R842237 : Reach 842237 := rs (se 3 (by rfl) ⟨157919, by rfl⟩) R315839
theorem R940709 : Reach 940709 := rs (se 4 (by rfl) ⟨88191, by rfl⟩) R176383
theorem R482111 : Reach 482111 := rs (se 1 (by rfl) ⟨361583, by rfl⟩) R723167
theorem R1137617 : Reach 1137617 := rs (se 2 (by rfl) ⟨426606, by rfl⟩) R853213
theorem R220319 : Reach 220319 := rs (se 1 (by rfl) ⟨165239, by rfl⟩) R330479
theorem R220571 : Reach 220571 := rs (se 1 (by rfl) ⟨165428, by rfl⟩) R330857
theorem R1794797 : Reach 1794797 := rs (se 3 (by rfl) ⟨336524, by rfl⟩) R673049
theorem R418607 : Reach 418607 := rs (se 1 (by rfl) ⟨313955, by rfl⟩) R627911
theorem R222623 : Reach 222623 := rs (se 1 (by rfl) ⟨166967, by rfl⟩) R333935
theorem R222857 : Reach 222857 := rs (se 2 (by rfl) ⟨83571, by rfl⟩) R167143
theorem R222875 : Reach 222875 := rs (se 1 (by rfl) ⟨167156, by rfl⟩) R334313
theorem R190127 : Reach 190127 := rs (se 1 (by rfl) ⟨142595, by rfl⟩) R285191
theorem R222911 : Reach 222911 := rs (se 1 (by rfl) ⟨167183, by rfl⟩) R334367
theorem R157439 : Reach 157439 := rs (se 1 (by rfl) ⟨118079, by rfl⟩) R236159
theorem R485351 : Reach 485351 := rs (se 1 (by rfl) ⟨364013, by rfl⟩) R728027
theorem R2385949 : Reach 2385949 := rs (se 3 (by rfl) ⟨447365, by rfl⟩) R894731
theorem R452891 : Reach 452891 := rs (se 1 (by rfl) ⟨339668, by rfl⟩) R679337
theorem R322973 : Reach 322973 := rs (se 3 (by rfl) ⟨60557, by rfl⟩) R121115
theorem R159263 : Reach 159263 := rs (se 1 (by rfl) ⟨119447, by rfl⟩) R238895
theorem R553175 : Reach 553175 := rs (se 1 (by rfl) ⟨414881, by rfl⟩) R829763
theorem R2519423 : Reach 2519423 := rs (se 1 (by rfl) ⟨1889567, by rfl⟩) R3779135
theorem R488105 : Reach 488105 := rs (se 2 (by rfl) ⟨183039, by rfl⟩) R366079
theorem R750383 : Reach 750383 := rs (se 1 (by rfl) ⟨562787, by rfl⟩) R1125575
theorem R95167 : Reach 95167 := rs (se 1 (by rfl) ⟨71375, by rfl⟩) R142751
theorem R160879 : Reach 160879 := rs (se 1 (by rfl) ⟨120659, by rfl⟩) R241319
theorem R95343 : Reach 95343 := rs (se 1 (by rfl) ⟨71507, by rfl⟩) R143015
theorem R95359 : Reach 95359 := rs (se 1 (by rfl) ⟨71519, by rfl⟩) R143039
theorem R1438859 : Reach 1438859 := rs (se 1 (by rfl) ⟨1079144, by rfl⟩) R2158289
theorem R95423 : Reach 95423 := rs (se 1 (by rfl) ⟨71567, by rfl⟩) R143135
theorem R324863 : Reach 324863 := rs (se 1 (by rfl) ⟨243647, by rfl⟩) R487295
theorem R324971 : Reach 324971 := rs (se 1 (by rfl) ⟨243728, by rfl⟩) R487457
theorem R95615 : Reach 95615 := rs (se 1 (by rfl) ⟨71711, by rfl⟩) R143423
theorem R95743 : Reach 95743 := rs (se 1 (by rfl) ⟨71807, by rfl⟩) R143615
theorem R95771 : Reach 95771 := rs (se 1 (by rfl) ⟨71828, by rfl⟩) R143657
theorem R554633 : Reach 554633 := rs (se 2 (by rfl) ⟨207987, by rfl⟩) R415975
theorem R95951 : Reach 95951 := rs (se 1 (by rfl) ⟨71963, by rfl⟩) R143927
theorem R96111 : Reach 96111 := rs (se 1 (by rfl) ⟨72083, by rfl⟩) R144167
theorem R96191 : Reach 96191 := rs (se 1 (by rfl) ⟨72143, by rfl⟩) R144287
theorem R325565 : Reach 325565 := rs (se 3 (by rfl) ⟨61043, by rfl⟩) R122087
theorem R325619 : Reach 325619 := rs (se 1 (by rfl) ⟨244214, by rfl⟩) R488429
theorem R129055 : Reach 129055 := rs (se 1 (by rfl) ⟨96791, by rfl⟩) R193583
theorem R325673 : Reach 325673 := rs (se 2 (by rfl) ⟨122127, by rfl⟩) R244255
theorem R784579 : Reach 784579 := rs (se 1 (by rfl) ⟨588434, by rfl⟩) R1176869
theorem R96507 : Reach 96507 := rs (se 1 (by rfl) ⟨72380, by rfl⟩) R144761
theorem R162047 : Reach 162047 := rs (se 1 (by rfl) ⟨121535, by rfl⟩) R243071
theorem R96511 : Reach 96511 := rs (se 1 (by rfl) ⟨72383, by rfl⟩) R144767
theorem R96615 : Reach 96615 := rs (se 1 (by rfl) ⟨72461, by rfl⟩) R144923
theorem R96735 : Reach 96735 := rs (se 1 (by rfl) ⟨72551, by rfl⟩) R145103
theorem R162283 : Reach 162283 := rs (se 1 (by rfl) ⟨121712, by rfl⟩) R243425
theorem R96871 : Reach 96871 := rs (se 1 (by rfl) ⟨72653, by rfl⟩) R145307
theorem R96895 : Reach 96895 := rs (se 1 (by rfl) ⟨72671, by rfl⟩) R145343
theorem R97007 : Reach 97007 := rs (se 1 (by rfl) ⟨72755, by rfl⟩) R145511
theorem R97263 : Reach 97263 := rs (se 1 (by rfl) ⟨72947, by rfl⟩) R145895
theorem R97311 : Reach 97311 := rs (se 1 (by rfl) ⟨72983, by rfl⟩) R145967
theorem R162985 : Reach 162985 := rs (se 2 (by rfl) ⟨61119, by rfl⟩) R122239
theorem R97759 : Reach 97759 := rs (se 1 (by rfl) ⟨73319, by rfl⟩) R146639
theorem R97819 : Reach 97819 := rs (se 1 (by rfl) ⟨73364, by rfl⟩) R146729
theorem R97839 : Reach 97839 := rs (se 1 (by rfl) ⟨73379, by rfl⟩) R146759
theorem R163721 : Reach 163721 := rs (se 2 (by rfl) ⟨61395, by rfl⟩) R122791
theorem R327563 : Reach 327563 := rs (se 1 (by rfl) ⟨245672, by rfl⟩) R491345
theorem R622475 : Reach 622475 := rs (se 1 (by rfl) ⟨466856, by rfl⟩) R933713
theorem R98239 : Reach 98239 := rs (se 1 (by rfl) ⟨73679, by rfl⟩) R147359
theorem R327671 : Reach 327671 := rs (se 1 (by rfl) ⟨245753, by rfl⟩) R491507
theorem R98335 : Reach 98335 := rs (se 1 (by rfl) ⟨73751, by rfl⟩) R147503
theorem R98351 : Reach 98351 := rs (se 1 (by rfl) ⟨73763, by rfl⟩) R147527
theorem R98471 : Reach 98471 := rs (se 1 (by rfl) ⟨73853, by rfl⟩) R147707
theorem R98555 : Reach 98555 := rs (se 1 (by rfl) ⟨73916, by rfl⟩) R147833
theorem R98663 : Reach 98663 := rs (se 1 (by rfl) ⟨73997, by rfl⟩) R147995
theorem R98751 : Reach 98751 := rs (se 1 (by rfl) ⟨74063, by rfl⟩) R148127
theorem R98783 : Reach 98783 := rs (se 1 (by rfl) ⟨74087, by rfl⟩) R148175
theorem R98863 : Reach 98863 := rs (se 1 (by rfl) ⟨74147, by rfl⟩) R148295
theorem R98907 : Reach 98907 := rs (se 1 (by rfl) ⟨74180, by rfl⟩) R148361
theorem R262781 : Reach 262781 := rs (se 3 (by rfl) ⟨49271, by rfl⟩) R98543
theorem R328859 : Reach 328859 := rs (se 1 (by rfl) ⟨246644, by rfl⟩) R493289
theorem R329129 : Reach 329129 := rs (se 2 (by rfl) ⟨123423, by rfl⟩) R246847
theorem R493775 : Reach 493775 := rs (se 1 (by rfl) ⟨370331, by rfl⟩) R740663
theorem R3181265 : Reach 3181265 := rs (se 2 (by rfl) ⟨1192974, by rfl⟩) R2385949
theorem R232199 : Reach 232199 := rs (se 1 (by rfl) ⟨174149, by rfl⟩) R348299
theorem R494525 : Reach 494525 := rs (se 3 (by rfl) ⟨92723, by rfl⟩) R185447
theorem R363649 : Reach 363649 := rs (se 2 (by rfl) ⟨136368, by rfl⟩) R272737
theorem R495071 : Reach 495071 := rs (se 1 (by rfl) ⟨371303, by rfl⟩) R742607
theorem R1544447 : Reach 1544447 := rs (se 1 (by rfl) ⟨1158335, by rfl⟩) R2316671
theorem R561491 : Reach 561491 := rs (se 1 (by rfl) ⟨421118, by rfl⟩) R842237
theorem R627139 : Reach 627139 := rs (se 1 (by rfl) ⟨470354, by rfl⟩) R940709
theorem R758411 : Reach 758411 := rs (se 1 (by rfl) ⟨568808, by rfl⟩) R1137617
theorem R3871901 : Reach 3871901 := rs (se 3 (by rfl) ⟨725981, by rfl⟩) R1451963
theorem R104959 : Reach 104959 := rs (se 1 (by rfl) ⟨78719, by rfl⟩) R157439
theorem R301927 : Reach 301927 := rs (se 1 (by rfl) ⟨226445, by rfl⟩) R452891
theorem R465821 : Reach 465821 := rs (se 3 (by rfl) ⟨87341, by rfl⟩) R174683
theorem R106175 : Reach 106175 := rs (se 1 (by rfl) ⟨79631, by rfl⟩) R159263
theorem R728999 : Reach 728999 := rs (se 1 (by rfl) ⟨546749, by rfl⟩) R1093499
theorem R172073 : Reach 172073 := rs (se 2 (by rfl) ⟨64527, by rfl⟩) R129055
theorem R368783 : Reach 368783 := rs (se 1 (by rfl) ⟨276587, by rfl⟩) R553175
theorem R1679615 : Reach 1679615 := rs (se 1 (by rfl) ⟨1259711, by rfl⟩) R2519423
theorem R500255 : Reach 500255 := rs (se 1 (by rfl) ⟨375191, by rfl⟩) R750383
theorem R2826971 : Reach 2826971 := rs (se 1 (by rfl) ⟨2120228, by rfl⟩) R4240457
theorem R959239 : Reach 959239 := rs (se 1 (by rfl) ⟨719429, by rfl⟩) R1438859
theorem R369755 : Reach 369755 := rs (se 1 (by rfl) ⟨277316, by rfl⟩) R554633
theorem R468395 : Reach 468395 := rs (se 1 (by rfl) ⟨351296, by rfl⟩) R702593
theorem R108031 : Reach 108031 := rs (se 1 (by rfl) ⟨81023, by rfl⟩) R162047
theorem R468935 : Reach 468935 := rs (se 1 (by rfl) ⟨351701, by rfl⟩) R703403
theorem R928279 : Reach 928279 := rs (se 1 (by rfl) ⟨696209, by rfl⟩) R1392419
theorem R109147 : Reach 109147 := rs (se 1 (by rfl) ⟨81860, by rfl⟩) R163721
theorem R4533083 : Reach 4533083 := rs (se 1 (by rfl) ⟨3399812, by rfl⟩) R6799625
theorem R109435 : Reach 109435 := rs (se 1 (by rfl) ⟨82076, by rfl⟩) R164153
theorem R503131 : Reach 503131 := rs (se 1 (by rfl) ⟨377348, by rfl⟩) R754697
theorem R470855 : Reach 470855 := rs (se 1 (by rfl) ⟨353141, by rfl⟩) R706283
theorem R634711 : Reach 634711 := rs (se 1 (by rfl) ⟨476033, by rfl⟩) R952067
theorem R6795251 : Reach 6795251 := rs (se 1 (by rfl) ⟨5096438, by rfl⟩) R10192877
theorem R110623 : Reach 110623 := rs (se 1 (by rfl) ⟨82967, by rfl⟩) R165935
theorem R372883 : Reach 372883 := rs (se 1 (by rfl) ⟨279662, by rfl⟩) R559325
theorem R1781927 : Reach 1781927 := rs (se 1 (by rfl) ⟨1336445, by rfl⟩) R2672891
theorem R241967 : Reach 241967 := rs (se 1 (by rfl) ⟨181475, by rfl⟩) R362951
theorem R143963 : Reach 143963 := rs (se 1 (by rfl) ⟨107972, by rfl⟩) R215945
theorem R373643 : Reach 373643 := rs (se 1 (by rfl) ⟨280232, by rfl⟩) R560465
theorem R144809 : Reach 144809 := rs (se 2 (by rfl) ⟨54303, by rfl⟩) R108607
theorem R144863 : Reach 144863 := rs (se 1 (by rfl) ⟨108647, by rfl⟩) R217295
theorem R145001 : Reach 145001 := rs (se 2 (by rfl) ⟨54375, by rfl⟩) R108751
theorem R2209451 : Reach 2209451 := rs (se 1 (by rfl) ⟨1657088, by rfl⟩) R3314177
theorem R145223 : Reach 145223 := rs (se 1 (by rfl) ⟨108917, by rfl⟩) R217835
theorem R145463 : Reach 145463 := rs (se 1 (by rfl) ⟨109097, by rfl⟩) R218195
theorem R145535 : Reach 145535 := rs (se 1 (by rfl) ⟨109151, by rfl⟩) R218303
theorem R932255 : Reach 932255 := rs (se 1 (by rfl) ⟨699191, by rfl⟩) R1398383
theorem R146345 : Reach 146345 := rs (se 2 (by rfl) ⟨54879, by rfl⟩) R109759
theorem R507005 : Reach 507005 := rs (se 3 (by rfl) ⟨95063, by rfl⟩) R190127
theorem R245075 : Reach 245075 := rs (se 1 (by rfl) ⟨183806, by rfl⟩) R367613
theorem R146879 : Reach 146879 := rs (se 1 (by rfl) ⟨110159, by rfl⟩) R220319
theorem R376271 : Reach 376271 := rs (se 1 (by rfl) ⟨282203, by rfl⟩) R564407
theorem R441911 : Reach 441911 := rs (se 1 (by rfl) ⟨331433, by rfl⟩) R662867
theorem R147047 : Reach 147047 := rs (se 1 (by rfl) ⟨110285, by rfl⟩) R220571
theorem R278569 : Reach 278569 := rs (se 2 (by rfl) ⟨104463, by rfl⟩) R208927
theorem R246071 : Reach 246071 := rs (se 1 (by rfl) ⟨184553, by rfl⟩) R369107
theorem R1196531 : Reach 1196531 := rs (se 1 (by rfl) ⟨897398, by rfl⟩) R1794797
theorem R279071 : Reach 279071 := rs (se 1 (by rfl) ⟨209303, by rfl⟩) R418607
theorem R9290375 : Reach 9290375 := rs (se 1 (by rfl) ⟨6967781, by rfl⟩) R13935563
theorem R5686193 : Reach 5686193 := rs (se 2 (by rfl) ⟨2132322, by rfl⟩) R4264645
theorem R148415 : Reach 148415 := rs (se 1 (by rfl) ⟨111311, by rfl⟩) R222623
theorem R148571 : Reach 148571 := rs (se 1 (by rfl) ⟨111428, by rfl⟩) R222857
theorem R148583 : Reach 148583 := rs (se 1 (by rfl) ⟨111437, by rfl⟩) R222875
theorem R148607 : Reach 148607 := rs (se 1 (by rfl) ⟨111455, by rfl⟩) R222911
theorem R312457 : Reach 312457 := rs (se 2 (by rfl) ⟨117171, by rfl⟩) R234343
theorem R214505 : Reach 214505 := rs (se 2 (by rfl) ⟨80439, by rfl⟩) R160879
theorem R542537 : Reach 542537 := rs (se 2 (by rfl) ⟨203451, by rfl⟩) R406903
theorem R215315 : Reach 215315 := rs (se 1 (by rfl) ⟨161486, by rfl⟩) R322973
theorem R1100627 : Reach 1100627 := rs (se 1 (by rfl) ⟨825470, by rfl⟩) R1650941
theorem R249115 : Reach 249115 := rs (se 1 (by rfl) ⟨186836, by rfl⟩) R373673
theorem R216377 : Reach 216377 := rs (se 2 (by rfl) ⟨81141, by rfl⟩) R162283
theorem R216575 : Reach 216575 := rs (se 1 (by rfl) ⟨162431, by rfl⟩) R324863
theorem R216647 : Reach 216647 := rs (se 1 (by rfl) ⟨162485, by rfl⟩) R324971
theorem R741149 : Reach 741149 := rs (se 3 (by rfl) ⟨138965, by rfl⟩) R277931
theorem R217043 : Reach 217043 := rs (se 1 (by rfl) ⟨162782, by rfl⟩) R325565
theorem R544745 : Reach 544745 := rs (se 2 (by rfl) ⟨204279, by rfl⟩) R408559
theorem R217079 : Reach 217079 := rs (se 1 (by rfl) ⟨162809, by rfl⟩) R325619
theorem R217115 : Reach 217115 := rs (se 1 (by rfl) ⟨162836, by rfl⟩) R325673
theorem R217313 : Reach 217313 := rs (se 2 (by rfl) ⟨81492, by rfl⟩) R162985
theorem R218375 : Reach 218375 := rs (se 1 (by rfl) ⟨163781, by rfl⟩) R327563
theorem R414983 : Reach 414983 := rs (se 1 (by rfl) ⟨311237, by rfl⟩) R622475
theorem R218447 : Reach 218447 := rs (se 1 (by rfl) ⟨163835, by rfl⟩) R327671
theorem R546385 : Reach 546385 := rs (se 2 (by rfl) ⟨204894, by rfl⟩) R409789
theorem R219131 : Reach 219131 := rs (se 1 (by rfl) ⟨164348, by rfl⟩) R328697
theorem R219167 : Reach 219167 := rs (se 1 (by rfl) ⟨164375, by rfl⟩) R328751
theorem R120943 : Reach 120943 := rs (se 1 (by rfl) ⟨90707, by rfl⟩) R181415
theorem R4512023 : Reach 4512023 := rs (se 1 (by rfl) ⟨3384017, by rfl⟩) R6768035
theorem R186761 : Reach 186761 := rs (se 2 (by rfl) ⟨70035, by rfl⟩) R140071
theorem R416249 : Reach 416249 := rs (se 2 (by rfl) ⟨156093, by rfl⟩) R312187
theorem R220391 : Reach 220391 := rs (se 1 (by rfl) ⟨165293, by rfl⟩) R330587
theorem R876743 : Reach 876743 := rs (se 1 (by rfl) ⟨657557, by rfl⟩) R1315115
theorem R221921 : Reach 221921 := rs (se 2 (by rfl) ⟨83220, by rfl⟩) R166441
theorem R222689 : Reach 222689 := rs (se 2 (by rfl) ⟨83508, by rfl⟩) R167017
theorem R845549 : Reach 845549 := rs (se 3 (by rfl) ⟨158540, by rfl⟩) R317081
theorem R321407 : Reach 321407 := rs (se 1 (by rfl) ⟨241055, by rfl⟩) R482111
theorem R322433 : Reach 322433 := rs (se 2 (by rfl) ⟨120912, by rfl⟩) R241825
theorem R323567 : Reach 323567 := rs (se 1 (by rfl) ⟨242675, by rfl⟩) R485351
theorem R95199 : Reach 95199 := rs (se 1 (by rfl) ⟨71399, by rfl⟩) R142799
theorem R95263 : Reach 95263 := rs (se 1 (by rfl) ⟨71447, by rfl⟩) R142895
theorem R95711 : Reach 95711 := rs (se 1 (by rfl) ⟨71783, by rfl⟩) R143567
theorem R95791 : Reach 95791 := rs (se 1 (by rfl) ⟨71843, by rfl⟩) R143687
theorem R1046105 : Reach 1046105 := rs (se 2 (by rfl) ⟨392289, by rfl⟩) R784579
theorem R325403 : Reach 325403 := rs (se 1 (by rfl) ⟨244052, by rfl⟩) R488105
theorem R96319 : Reach 96319 := rs (se 1 (by rfl) ⟨72239, by rfl⟩) R144479
theorem R96359 : Reach 96359 := rs (se 1 (by rfl) ⟨72269, by rfl⟩) R144539
theorem R489847 : Reach 489847 := rs (se 1 (by rfl) ⟨367385, by rfl⟩) R734771
theorem R96923 : Reach 96923 := rs (se 1 (by rfl) ⟨72692, by rfl⟩) R145385
theorem R97343 : Reach 97343 := rs (se 1 (by rfl) ⟨73007, by rfl⟩) R146015
theorem R490859 : Reach 490859 := rs (se 1 (by rfl) ⟨368144, by rfl⟩) R736289
theorem R97663 : Reach 97663 := rs (se 1 (by rfl) ⟨73247, by rfl⟩) R146495
theorem R687599 : Reach 687599 := rs (se 1 (by rfl) ⟨515699, by rfl⟩) R1031399
theorem R97895 : Reach 97895 := rs (se 1 (by rfl) ⟨73421, by rfl⟩) R146843
theorem R98175 : Reach 98175 := rs (se 1 (by rfl) ⟨73631, by rfl⟩) R147263
theorem R163775 : Reach 163775 := rs (se 1 (by rfl) ⟨122831, by rfl⟩) R245663
theorem R164047 : Reach 164047 := rs (se 1 (by rfl) ⟨123035, by rfl⟩) R246071
theorem R6193583 : Reach 6193583 := rs (se 1 (by rfl) ⟨4645187, by rfl⟩) R9290375
theorem R98943 : Reach 98943 := rs (se 1 (by rfl) ⟨74207, by rfl⟩) R148415
theorem R99047 : Reach 99047 := rs (se 1 (by rfl) ⟨74285, by rfl⟩) R148571
theorem R99055 : Reach 99055 := rs (se 1 (by rfl) ⟨74291, by rfl⟩) R148583
theorem R99071 : Reach 99071 := rs (se 1 (by rfl) ⟨74303, by rfl⟩) R148607
theorem R1278985 : Reach 1278985 := rs (se 2 (by rfl) ⟨479619, by rfl⟩) R959239
theorem R361691 : Reach 361691 := rs (se 1 (by rfl) ⟨271268, by rfl⟩) R542537
theorem R329183 : Reach 329183 := rs (se 1 (by rfl) ⟨246887, by rfl⟩) R493775
theorem R329683 : Reach 329683 := rs (se 1 (by rfl) ⟨247262, by rfl⟩) R494525
theorem R330047 : Reach 330047 := rs (se 1 (by rfl) ⟨247535, by rfl⟩) R495071
theorem R494099 : Reach 494099 := rs (se 1 (by rfl) ⟨370574, by rfl⟩) R741149
theorem R363163 : Reach 363163 := rs (se 1 (by rfl) ⟨272372, by rfl⟩) R544745
theorem R559781 : Reach 559781 := rs (se 4 (by rfl) ⟨52479, by rfl⟩) R104959
theorem R4950821 : Reach 4950821 := rs (se 4 (by rfl) ⟨464139, by rfl⟩) R928279
theorem R10325069 : Reach 10325069 := rs (se 3 (by rfl) ⟨1935950, by rfl⟩) R3871901
theorem R593837 : Reach 593837 := rs (se 3 (by rfl) ⟨111344, by rfl⟩) R222689
theorem R332153 : Reach 332153 := rs (se 2 (by rfl) ⟨124557, by rfl⟩) R249115
theorem R1119743 : Reach 1119743 := rs (se 1 (by rfl) ⟨839807, by rfl⟩) R1679615
theorem R497177 : Reach 497177 := rs (se 2 (by rfl) ⟨186441, by rfl⟩) R372883
theorem R333503 : Reach 333503 := rs (se 1 (by rfl) ⟨250127, by rfl⟩) R500255
theorem R563699 : Reach 563699 := rs (se 1 (by rfl) ⟨422774, by rfl⟩) R845549
theorem R3022055 : Reach 3022055 := rs (se 1 (by rfl) ⟨2266541, by rfl⟩) R4533083
theorem R728513 : Reach 728513 := rs (se 2 (by rfl) ⟨273192, by rfl⟩) R546385
theorem R4530167 : Reach 4530167 := rs (se 1 (by rfl) ⟨3397625, by rfl⟩) R6795251
theorem R1187951 : Reach 1187951 := rs (se 1 (by rfl) ⟨890963, by rfl⟩) R1781927
theorem R697403 : Reach 697403 := rs (se 1 (by rfl) ⟨523052, by rfl⟩) R1046105
theorem R402569 : Reach 402569 := rs (se 2 (by rfl) ⟨150963, by rfl⟩) R301927
theorem R338003 : Reach 338003 := rs (se 1 (by rfl) ⟨253502, by rfl⟩) R507005
theorem R109183 : Reach 109183 := rs (se 1 (by rfl) ⟨81887, by rfl⟩) R163775
theorem R371425 : Reach 371425 := rs (se 2 (by rfl) ⟨139284, by rfl⟩) R278569
theorem R797687 : Reach 797687 := rs (se 1 (by rfl) ⟨598265, by rfl⟩) R1196531
theorem R175187 : Reach 175187 := rs (se 1 (by rfl) ⟨131390, by rfl⟩) R262781
theorem R143003 : Reach 143003 := rs (se 1 (by rfl) ⟨107252, by rfl⟩) R214505
theorem R143543 : Reach 143543 := rs (se 1 (by rfl) ⟨107657, by rfl⟩) R215315
theorem R733751 : Reach 733751 := rs (se 1 (by rfl) ⟨550313, by rfl⟩) R1100627
theorem R144041 : Reach 144041 := rs (se 2 (by rfl) ⟨54015, by rfl⟩) R108031
theorem R144251 : Reach 144251 := rs (se 1 (by rfl) ⟨108188, by rfl⟩) R216377
theorem R144383 : Reach 144383 := rs (se 1 (by rfl) ⟨108287, by rfl⟩) R216575
theorem R144431 : Reach 144431 := rs (se 1 (by rfl) ⟨108323, by rfl⟩) R216647
theorem R144695 : Reach 144695 := rs (se 1 (by rfl) ⟨108521, by rfl⟩) R217043
theorem R144719 : Reach 144719 := rs (se 1 (by rfl) ⟨108539, by rfl⟩) R217079
theorem R144743 : Reach 144743 := rs (se 1 (by rfl) ⟨108557, by rfl⟩) R217115
theorem R144875 : Reach 144875 := rs (se 1 (by rfl) ⟨108656, by rfl⟩) R217313
theorem R1029631 : Reach 1029631 := rs (se 1 (by rfl) ⟨772223, by rfl⟩) R1544447
theorem R374327 : Reach 374327 := rs (se 1 (by rfl) ⟨280745, by rfl⟩) R561491
theorem R505607 : Reach 505607 := rs (se 1 (by rfl) ⟨379205, by rfl⟩) R758411
theorem R145529 : Reach 145529 := rs (se 2 (by rfl) ⟨54573, by rfl⟩) R109147
theorem R145583 : Reach 145583 := rs (se 1 (by rfl) ⟨109187, by rfl⟩) R218375
theorem R145631 : Reach 145631 := rs (se 1 (by rfl) ⟨109223, by rfl⟩) R218447
theorem R145913 : Reach 145913 := rs (se 2 (by rfl) ⟨54717, by rfl⟩) R109435
theorem R146087 : Reach 146087 := rs (se 1 (by rfl) ⟨109565, by rfl⟩) R219131
theorem R146111 : Reach 146111 := rs (se 1 (by rfl) ⟨109583, by rfl⟩) R219167
theorem R277499 : Reach 277499 := rs (se 1 (by rfl) ⟨208124, by rfl⟩) R416249
theorem R670841 : Reach 670841 := rs (se 2 (by rfl) ⟨251565, by rfl⟩) R503131
theorem R310547 : Reach 310547 := rs (se 1 (by rfl) ⟨232910, by rfl⟩) R465821
theorem R146927 : Reach 146927 := rs (se 1 (by rfl) ⟨110195, by rfl⟩) R220391
theorem R114715 : Reach 114715 := rs (se 1 (by rfl) ⟨86036, by rfl⟩) R172073
theorem R147497 : Reach 147497 := rs (se 2 (by rfl) ⟨55311, by rfl⟩) R110623
theorem R245855 : Reach 245855 := rs (se 1 (by rfl) ⟨184391, by rfl⟩) R368783
theorem R1884647 : Reach 1884647 := rs (se 1 (by rfl) ⟨1413485, by rfl⟩) R2826971
theorem R147947 : Reach 147947 := rs (se 1 (by rfl) ⟨110960, by rfl⟩) R221921
theorem R836185 : Reach 836185 := rs (se 2 (by rfl) ⟨313569, by rfl⟩) R627139
theorem R246503 : Reach 246503 := rs (se 1 (by rfl) ⟨184877, by rfl⟩) R369755
theorem R312263 : Reach 312263 := rs (se 1 (by rfl) ⟨234197, by rfl⟩) R468395
theorem R214271 : Reach 214271 := rs (se 1 (by rfl) ⟨160703, by rfl⟩) R321407
theorem R312623 : Reach 312623 := rs (se 1 (by rfl) ⟨234467, by rfl⟩) R468935
theorem R214955 : Reach 214955 := rs (se 1 (by rfl) ⟨161216, by rfl⟩) R322433
theorem R313903 : Reach 313903 := rs (se 1 (by rfl) ⟨235427, by rfl⟩) R470855
theorem R215711 : Reach 215711 := rs (se 1 (by rfl) ⟨161783, by rfl⟩) R323567
theorem R249095 : Reach 249095 := rs (se 1 (by rfl) ⟨186821, by rfl⟩) R373643
theorem R216935 : Reach 216935 := rs (se 1 (by rfl) ⟨162701, by rfl⟩) R325403
theorem R283133 : Reach 283133 := rs (se 3 (by rfl) ⟨53087, by rfl⟩) R106175
theorem R250847 : Reach 250847 := rs (se 1 (by rfl) ⟨188135, by rfl⟩) R376271
theorem R186047 : Reach 186047 := rs (se 1 (by rfl) ⟨139535, by rfl⟩) R279071
theorem R3790795 : Reach 3790795 := rs (se 1 (by rfl) ⟨2843096, by rfl⟩) R5686193
theorem R219239 : Reach 219239 := rs (se 1 (by rfl) ⟨164429, by rfl⟩) R328859
theorem R219419 : Reach 219419 := rs (se 1 (by rfl) ⟨164564, by rfl⟩) R329129
theorem R416609 : Reach 416609 := rs (se 2 (by rfl) ⟨156228, by rfl⟩) R312457
theorem R2120843 : Reach 2120843 := rs (se 1 (by rfl) ⟨1590632, by rfl⟩) R3181265
theorem R154799 : Reach 154799 := rs (se 1 (by rfl) ⟨116099, by rfl⟩) R232199
theorem R1106621 : Reach 1106621 := rs (se 3 (by rfl) ⟨207491, by rfl⟩) R414983
theorem R2614133 : Reach 2614133 := rs (se 5 (by rfl) ⟨122537, by rfl⟩) R245075
theorem R484865 : Reach 484865 := rs (se 2 (by rfl) ⟨181824, by rfl⟩) R363649
theorem R3008015 : Reach 3008015 := rs (se 1 (by rfl) ⟨2256011, by rfl⟩) R4512023
theorem R124507 : Reach 124507 := rs (se 1 (by rfl) ⟨93380, by rfl⟩) R186761
theorem R5891869 : Reach 5891869 := rs (se 3 (by rfl) ⟨1104725, by rfl⟩) R2209451
theorem R846281 : Reach 846281 := rs (se 2 (by rfl) ⟨317355, by rfl⟩) R634711
theorem R485999 : Reach 485999 := rs (se 1 (by rfl) ⟨364499, by rfl⟩) R728999
theorem R584495 : Reach 584495 := rs (se 1 (by rfl) ⟨438371, by rfl⟩) R876743
theorem R161257 : Reach 161257 := rs (se 2 (by rfl) ⟨60471, by rfl⟩) R120943
theorem R161311 : Reach 161311 := rs (se 1 (by rfl) ⟨120983, by rfl⟩) R241967
theorem R95975 : Reach 95975 := rs (se 1 (by rfl) ⟨71981, by rfl⟩) R143963
theorem R653129 : Reach 653129 := rs (se 2 (by rfl) ⟨244923, by rfl⟩) R489847
theorem R96539 : Reach 96539 := rs (se 1 (by rfl) ⟨72404, by rfl⟩) R144809
theorem R96575 : Reach 96575 := rs (se 1 (by rfl) ⟨72431, by rfl⟩) R144863
theorem R96667 : Reach 96667 := rs (se 1 (by rfl) ⟨72500, by rfl⟩) R145001
theorem R96815 : Reach 96815 := rs (se 1 (by rfl) ⟨72611, by rfl⟩) R145223
theorem R96975 : Reach 96975 := rs (se 1 (by rfl) ⟨72731, by rfl⟩) R145463
theorem R97023 : Reach 97023 := rs (se 1 (by rfl) ⟨72767, by rfl⟩) R145535
theorem R621503 : Reach 621503 := rs (se 1 (by rfl) ⟨466127, by rfl⟩) R932255
theorem R97563 : Reach 97563 := rs (se 1 (by rfl) ⟨73172, by rfl⟩) R146345
theorem R327239 : Reach 327239 := rs (se 1 (by rfl) ⟨245429, by rfl⟩) R490859
theorem R97919 : Reach 97919 := rs (se 1 (by rfl) ⟨73439, by rfl⟩) R146879
theorem R458399 : Reach 458399 := rs (se 1 (by rfl) ⟨343799, by rfl⟩) R687599
theorem R294607 : Reach 294607 := rs (se 1 (by rfl) ⟨220955, by rfl⟩) R441911
theorem R98031 : Reach 98031 := rs (se 1 (by rfl) ⟨73523, by rfl⟩) R147047
theorem R98331 : Reach 98331 := rs (se 1 (by rfl) ⟨73748, by rfl⟩) R147497
theorem R163903 : Reach 163903 := rs (se 1 (by rfl) ⟨122927, by rfl⟩) R245855
theorem R4129055 : Reach 4129055 := rs (se 1 (by rfl) ⟨3096791, by rfl⟩) R6193583
theorem R98631 : Reach 98631 := rs (se 1 (by rfl) ⟨73973, by rfl⟩) R147947
theorem R164335 : Reach 164335 := rs (se 1 (by rfl) ⟨123251, by rfl⟩) R246503
theorem R1114913 : Reach 1114913 := rs (se 2 (by rfl) ⟨418092, by rfl⟩) R836185
theorem R755021 : Reach 755021 := rs (se 3 (by rfl) ⟨141566, by rfl⟩) R283133
theorem R1705313 : Reach 1705313 := rs (se 2 (by rfl) ⟨639492, by rfl⟩) R1278985
theorem R329399 : Reach 329399 := rs (se 1 (by rfl) ⟨247049, by rfl⟩) R494099
theorem R6883379 : Reach 6883379 := rs (se 1 (by rfl) ⟨5162534, by rfl⟩) R10325069
theorem R166009 : Reach 166009 := rs (se 2 (by rfl) ⟨62253, by rfl⟩) R124507
theorem R166063 : Reach 166063 := rs (se 1 (by rfl) ⟨124547, by rfl⟩) R249095
theorem R395891 : Reach 395891 := rs (se 1 (by rfl) ⟨296918, by rfl⟩) R593837
theorem R167231 : Reach 167231 := rs (se 1 (by rfl) ⟨125423, by rfl⟩) R250847
theorem R495233 : Reach 495233 := rs (se 2 (by rfl) ⟨185712, by rfl⟩) R371425
theorem R331451 : Reach 331451 := rs (se 1 (by rfl) ⟨248588, by rfl⟩) R497177
theorem R1413895 : Reach 1413895 := rs (se 1 (by rfl) ⟨1060421, by rfl⟩) R2120843
theorem R103199 : Reach 103199 := rs (se 1 (by rfl) ⟨77399, by rfl⟩) R154799
theorem R3020111 : Reach 3020111 := rs (se 1 (by rfl) ⟨2265083, by rfl⟩) R4530167
theorem R1742755 : Reach 1742755 := rs (se 1 (by rfl) ⟨1307066, by rfl⟩) R2614133
theorem R464935 : Reach 464935 := rs (se 1 (by rfl) ⟨348701, by rfl⟩) R697403
theorem R268379 : Reach 268379 := rs (se 1 (by rfl) ⟨201284, by rfl⟩) R402569
theorem R2005343 : Reach 2005343 := rs (se 1 (by rfl) ⟨1504007, by rfl⟩) R3008015
theorem R564187 : Reach 564187 := rs (se 1 (by rfl) ⟨423140, by rfl⟩) R846281
theorem R531791 : Reach 531791 := rs (se 1 (by rfl) ⟨398843, by rfl⟩) R797687
theorem R5054393 : Reach 5054393 := rs (se 2 (by rfl) ⟨1895397, by rfl⟩) R3790795
theorem R435419 : Reach 435419 := rs (se 1 (by rfl) ⟨326564, by rfl⟩) R653129
theorem R1222397 : Reach 1222397 := rs (se 3 (by rfl) ⟨229199, by rfl⟩) R458399
theorem R207031 : Reach 207031 := rs (se 1 (by rfl) ⟨155273, by rfl⟩) R310547
theorem R1256431 : Reach 1256431 := rs (se 1 (by rfl) ⟨942323, by rfl⟩) R1884647
theorem R208175 : Reach 208175 := rs (se 1 (by rfl) ⟨156131, by rfl⟩) R312263
theorem R241127 : Reach 241127 := rs (se 1 (by rfl) ⟨180845, by rfl⟩) R361691
theorem R142847 : Reach 142847 := rs (se 1 (by rfl) ⟨107135, by rfl⟩) R214271
theorem R208415 : Reach 208415 := rs (se 1 (by rfl) ⟨156311, by rfl⟩) R312623
theorem R143303 : Reach 143303 := rs (se 1 (by rfl) ⟨107477, by rfl⟩) R214955
theorem R143807 : Reach 143807 := rs (se 1 (by rfl) ⟨107855, by rfl⟩) R215711
theorem R373187 : Reach 373187 := rs (se 1 (by rfl) ⟨279890, by rfl⟩) R559781
theorem R144623 : Reach 144623 := rs (se 1 (by rfl) ⟨108467, by rfl⟩) R216935
theorem R439577 : Reach 439577 := rs (se 2 (by rfl) ⟨164841, by rfl⟩) R329683
theorem R145577 : Reach 145577 := rs (se 2 (by rfl) ⟨54591, by rfl⟩) R109183
theorem R146159 : Reach 146159 := rs (se 1 (by rfl) ⟨109619, by rfl⟩) R219239
theorem R146279 : Reach 146279 := rs (se 1 (by rfl) ⟨109709, by rfl⟩) R219419
theorem R375799 : Reach 375799 := rs (se 1 (by rfl) ⟨281849, by rfl⟩) R563699
theorem R277739 : Reach 277739 := rs (se 1 (by rfl) ⟨208304, by rfl⟩) R416609
theorem R2014703 : Reach 2014703 := rs (se 1 (by rfl) ⟨1511027, by rfl⟩) R3022055
theorem R737747 : Reach 737747 := rs (se 1 (by rfl) ⟨553310, by rfl⟩) R1106621
theorem R215009 : Reach 215009 := rs (se 2 (by rfl) ⟨80628, by rfl⟩) R161257
theorem R215081 : Reach 215081 := rs (se 2 (by rfl) ⟨80655, by rfl⟩) R161311
theorem R116791 : Reach 116791 := rs (se 1 (by rfl) ⟨87593, by rfl⟩) R175187
theorem R5393141 : Reach 5393141 := rs (se 5 (by rfl) ⟨252803, by rfl⟩) R505607
theorem R249551 : Reach 249551 := rs (se 1 (by rfl) ⟨187163, by rfl⟩) R374327
theorem R414335 : Reach 414335 := rs (se 1 (by rfl) ⟨310751, by rfl⟩) R621503
theorem R184999 : Reach 184999 := rs (se 1 (by rfl) ⟨138749, by rfl⟩) R277499
theorem R447227 : Reach 447227 := rs (se 1 (by rfl) ⟨335420, by rfl⟩) R670841
theorem R218159 : Reach 218159 := rs (se 1 (by rfl) ⟨163619, by rfl⟩) R327239
theorem R611813 : Reach 611813 := rs (se 4 (by rfl) ⟨57357, by rfl⟩) R114715
theorem R218729 : Reach 218729 := rs (se 2 (by rfl) ⟨82023, by rfl⟩) R164047
theorem R219455 : Reach 219455 := rs (se 1 (by rfl) ⟨164591, by rfl⟩) R329183
theorem R12671477 : Reach 12671477 := rs (se 5 (by rfl) ⟨593975, by rfl⟩) R1187951
theorem R220031 : Reach 220031 := rs (se 1 (by rfl) ⟨165023, by rfl⟩) R330047
theorem R7855825 : Reach 7855825 := rs (se 2 (by rfl) ⟨2945934, by rfl⟩) R5891869
theorem R221435 : Reach 221435 := rs (se 1 (by rfl) ⟨166076, by rfl⟩) R332153
theorem R418537 : Reach 418537 := rs (se 2 (by rfl) ⟨156951, by rfl⟩) R313903
theorem R484217 : Reach 484217 := rs (se 2 (by rfl) ⟨181581, by rfl⟩) R363163
theorem R746495 : Reach 746495 := rs (se 1 (by rfl) ⟨559871, by rfl⟩) R1119743
theorem R124031 : Reach 124031 := rs (se 1 (by rfl) ⟨93023, by rfl⟩) R186047
theorem R222335 : Reach 222335 := rs (se 1 (by rfl) ⟨166751, by rfl⟩) R333503
theorem R485675 : Reach 485675 := rs (se 1 (by rfl) ⟨364256, by rfl⟩) R728513
theorem R323243 : Reach 323243 := rs (se 1 (by rfl) ⟨242432, by rfl⟩) R484865
theorem R225335 : Reach 225335 := rs (se 1 (by rfl) ⟨169001, by rfl⟩) R338003
theorem R323999 : Reach 323999 := rs (se 1 (by rfl) ⟨242999, by rfl⟩) R485999
theorem R389663 : Reach 389663 := rs (se 1 (by rfl) ⟨292247, by rfl⟩) R584495
theorem R1372841 : Reach 1372841 := rs (se 2 (by rfl) ⟨514815, by rfl⟩) R1029631
theorem R13202189 : Reach 13202189 := rs (se 3 (by rfl) ⟨2475410, by rfl⟩) R4950821
theorem R95335 : Reach 95335 := rs (se 1 (by rfl) ⟨71501, by rfl⟩) R143003
theorem R95695 : Reach 95695 := rs (se 1 (by rfl) ⟨71771, by rfl⟩) R143543
theorem R489167 : Reach 489167 := rs (se 1 (by rfl) ⟨366875, by rfl⟩) R733751
theorem R96027 : Reach 96027 := rs (se 1 (by rfl) ⟨72020, by rfl⟩) R144041
theorem R96167 : Reach 96167 := rs (se 1 (by rfl) ⟨72125, by rfl⟩) R144251
theorem R96255 : Reach 96255 := rs (se 1 (by rfl) ⟨72191, by rfl⟩) R144383
theorem R96287 : Reach 96287 := rs (se 1 (by rfl) ⟨72215, by rfl⟩) R144431
theorem R96463 : Reach 96463 := rs (se 1 (by rfl) ⟨72347, by rfl⟩) R144695
theorem R96479 : Reach 96479 := rs (se 1 (by rfl) ⟨72359, by rfl⟩) R144719
theorem R96495 : Reach 96495 := rs (se 1 (by rfl) ⟨72371, by rfl⟩) R144743
theorem R96583 : Reach 96583 := rs (se 1 (by rfl) ⟨72437, by rfl⟩) R144875
theorem R1571237 : Reach 1571237 := rs (se 4 (by rfl) ⟨147303, by rfl⟩) R294607
theorem R97019 : Reach 97019 := rs (se 1 (by rfl) ⟨72764, by rfl⟩) R145529
theorem R97055 : Reach 97055 := rs (se 1 (by rfl) ⟨72791, by rfl⟩) R145583
theorem R97087 : Reach 97087 := rs (se 1 (by rfl) ⟨72815, by rfl⟩) R145631
theorem R97275 : Reach 97275 := rs (se 1 (by rfl) ⟨72956, by rfl⟩) R145913
theorem R97391 : Reach 97391 := rs (se 1 (by rfl) ⟨73043, by rfl⟩) R146087
theorem R97407 : Reach 97407 := rs (se 1 (by rfl) ⟨73055, by rfl⟩) R146111
theorem R97951 : Reach 97951 := rs (se 1 (by rfl) ⟨73463, by rfl⟩) R146927
theorem R2752703 : Reach 2752703 := rs (se 1 (by rfl) ⟨2064527, by rfl⟩) R4129055
theorem R622885 : Reach 622885 := rs (se 4 (by rfl) ⟨58395, by rfl⟩) R116791
theorem R491831 : Reach 491831 := rs (se 1 (by rfl) ⟨368873, by rfl⟩) R737747
theorem R558049 : Reach 558049 := rs (se 2 (by rfl) ⟨209268, by rfl⟩) R418537
theorem R4588919 : Reach 4588919 := rs (se 1 (by rfl) ⟨3441689, by rfl⟩) R6883379
theorem R263927 : Reach 263927 := rs (se 1 (by rfl) ⟨197945, by rfl⟩) R395891
theorem R330155 : Reach 330155 := rs (se 1 (by rfl) ⟨247616, by rfl⟩) R495233
theorem R166367 : Reach 166367 := rs (se 1 (by rfl) ⟨124775, by rfl⟩) R249551
theorem R330749 : Reach 330749 := rs (se 3 (by rfl) ⟨62015, by rfl⟩) R124031
theorem R298151 : Reach 298151 := rs (se 1 (by rfl) ⟨223613, by rfl⟩) R447227
theorem R1675241 : Reach 1675241 := rs (se 2 (by rfl) ⟨628215, by rfl⟩) R1256431
theorem R497663 : Reach 497663 := rs (se 1 (by rfl) ⟨373247, by rfl⟩) R746495
theorem R138943 : Reach 138943 := rs (se 1 (by rfl) ⟨104207, by rfl⟩) R208415
theorem R501065 : Reach 501065 := rs (se 2 (by rfl) ⟨187899, by rfl⟩) R375799
theorem R503347 : Reach 503347 := rs (se 1 (by rfl) ⟨377510, by rfl⟩) R755021
theorem R143339 : Reach 143339 := rs (se 1 (by rfl) ⟨107504, by rfl⟩) R215009
theorem R143387 : Reach 143387 := rs (se 1 (by rfl) ⟨107540, by rfl⟩) R215081
theorem R111487 : Reach 111487 := rs (se 1 (by rfl) ⟨83615, by rfl⟩) R167231
theorem R276041 : Reach 276041 := rs (se 2 (by rfl) ⟨103515, by rfl⟩) R207031
theorem R276223 : Reach 276223 := rs (se 1 (by rfl) ⟨207167, by rfl⟩) R414335
theorem R145439 : Reach 145439 := rs (se 1 (by rfl) ⟨109079, by rfl⟩) R218159
theorem R2013407 : Reach 2013407 := rs (se 1 (by rfl) ⟨1510055, by rfl⟩) R3020111
theorem R145819 : Reach 145819 := rs (se 1 (by rfl) ⟨109364, by rfl⟩) R218729
theorem R178919 : Reach 178919 := rs (se 1 (by rfl) ⟨134189, by rfl⟩) R268379
theorem R146303 : Reach 146303 := rs (se 1 (by rfl) ⟨109727, by rfl⟩) R219455
theorem R146687 : Reach 146687 := rs (se 1 (by rfl) ⟨110015, by rfl⟩) R220031
theorem R147623 : Reach 147623 := rs (se 1 (by rfl) ⟨110717, by rfl⟩) R221435
theorem R148223 : Reach 148223 := rs (se 1 (by rfl) ⟨111167, by rfl⟩) R222335
theorem R246665 : Reach 246665 := rs (se 2 (by rfl) ⟨92499, by rfl⟩) R184999
theorem R1885193 : Reach 1885193 := rs (se 2 (by rfl) ⟨706947, by rfl⟩) R1413895
theorem R215495 : Reach 215495 := rs (se 1 (by rfl) ⟨161621, by rfl⟩) R323243
theorem R150223 : Reach 150223 := rs (se 1 (by rfl) ⟨112667, by rfl⟩) R225335
theorem R215999 : Reach 215999 := rs (se 1 (by rfl) ⟨161999, by rfl⟩) R323999
theorem R248791 : Reach 248791 := rs (se 1 (by rfl) ⟨186593, by rfl⟩) R373187
theorem R1100789 : Reach 1100789 := rs (se 5 (by rfl) ⟨51599, by rfl⟩) R103199
theorem R8801459 : Reach 8801459 := rs (se 1 (by rfl) ⟨6601094, by rfl⟩) R13202189
theorem R185159 : Reach 185159 := rs (se 1 (by rfl) ⟨138869, by rfl⟩) R277739
theorem R10474433 : Reach 10474433 := rs (se 2 (by rfl) ⟨3927912, by rfl⟩) R7855825
theorem R218537 : Reach 218537 := rs (se 2 (by rfl) ⟨81951, by rfl⟩) R163903
theorem R743275 : Reach 743275 := rs (se 1 (by rfl) ⟨557456, by rfl⟩) R1114913
theorem R219113 : Reach 219113 := rs (se 2 (by rfl) ⟨82167, by rfl⟩) R164335
theorem R1136875 : Reach 1136875 := rs (se 1 (by rfl) ⟨852656, by rfl⟩) R1705313
theorem R219599 : Reach 219599 := rs (se 1 (by rfl) ⟨164699, by rfl⟩) R329399
theorem R3595427 : Reach 3595427 := rs (se 1 (by rfl) ⟨2696570, by rfl⟩) R5393141
theorem R220967 : Reach 220967 := rs (se 1 (by rfl) ⟨165725, by rfl⟩) R331451
theorem R221345 : Reach 221345 := rs (se 2 (by rfl) ⟨83004, by rfl⟩) R166009
theorem R221417 : Reach 221417 := rs (se 2 (by rfl) ⟨83031, by rfl⟩) R166063
theorem R1631501 : Reach 1631501 := rs (se 3 (by rfl) ⟨305906, by rfl⟩) R611813
theorem R1336895 : Reach 1336895 := rs (se 1 (by rfl) ⟨1002671, by rfl⟩) R2005343
theorem R8447651 : Reach 8447651 := rs (se 1 (by rfl) ⟨6335738, by rfl⟩) R12671477
theorem R354527 : Reach 354527 := rs (se 1 (by rfl) ⟨265895, by rfl⟩) R531791
theorem R3369595 : Reach 3369595 := rs (se 1 (by rfl) ⟨2527196, by rfl⟩) R5054393
theorem R322811 : Reach 322811 := rs (se 1 (by rfl) ⟨242108, by rfl⟩) R484217
theorem R290279 : Reach 290279 := rs (se 1 (by rfl) ⟨217709, by rfl⟩) R435419
theorem R814931 : Reach 814931 := rs (se 1 (by rfl) ⟨611198, by rfl⟩) R1222397
theorem R323783 : Reach 323783 := rs (se 1 (by rfl) ⟨242837, by rfl⟩) R485675
theorem R160751 : Reach 160751 := rs (se 1 (by rfl) ⟨120563, by rfl⟩) R241127
theorem R95231 : Reach 95231 := rs (se 1 (by rfl) ⟨71423, by rfl⟩) R142847
theorem R2323673 : Reach 2323673 := rs (se 2 (by rfl) ⟨871377, by rfl⟩) R1742755
theorem R95535 : Reach 95535 := rs (se 1 (by rfl) ⟨71651, by rfl⟩) R143303
theorem R619913 : Reach 619913 := rs (se 2 (by rfl) ⟨232467, by rfl⟩) R464935
theorem R95871 : Reach 95871 := rs (se 1 (by rfl) ⟨71903, by rfl⟩) R143807
theorem R259775 : Reach 259775 := rs (se 1 (by rfl) ⟨194831, by rfl⟩) R389663
theorem R915227 : Reach 915227 := rs (se 1 (by rfl) ⟨686420, by rfl⟩) R1372841
theorem R555133 : Reach 555133 := rs (se 3 (by rfl) ⟨104087, by rfl⟩) R208175
theorem R96415 : Reach 96415 := rs (se 1 (by rfl) ⟨72311, by rfl⟩) R144623
theorem R293051 : Reach 293051 := rs (se 1 (by rfl) ⟨219788, by rfl⟩) R439577
theorem R326111 : Reach 326111 := rs (se 1 (by rfl) ⟨244583, by rfl⟩) R489167
theorem R752249 : Reach 752249 := rs (se 2 (by rfl) ⟨282093, by rfl⟩) R564187
theorem R97051 : Reach 97051 := rs (se 1 (by rfl) ⟨72788, by rfl⟩) R145577
theorem R1047491 : Reach 1047491 := rs (se 1 (by rfl) ⟨785618, by rfl⟩) R1571237
theorem R97439 : Reach 97439 := rs (se 1 (by rfl) ⟨73079, by rfl⟩) R146159
theorem R97519 : Reach 97519 := rs (se 1 (by rfl) ⟨73139, by rfl⟩) R146279
theorem R1343135 : Reach 1343135 := rs (se 1 (by rfl) ⟨1007351, by rfl⟩) R2014703
theorem R98415 : Reach 98415 := rs (se 1 (by rfl) ⟨73811, by rfl⟩) R147623
theorem R1835135 : Reach 1835135 := rs (se 1 (by rfl) ⟨1376351, by rfl⟩) R2752703
theorem R327887 : Reach 327887 := rs (se 1 (by rfl) ⟨245915, by rfl⟩) R491831
theorem R98815 : Reach 98815 := rs (se 1 (by rfl) ⟨74111, by rfl⟩) R148223
theorem R164443 : Reach 164443 := rs (se 1 (by rfl) ⟨123332, by rfl⟩) R246665
theorem R198767 : Reach 198767 := rs (se 1 (by rfl) ⟨149075, by rfl⟩) R298151
theorem R5867639 : Reach 5867639 := rs (se 1 (by rfl) ⟨4400729, by rfl⟩) R8801459
theorem R1116827 : Reach 1116827 := rs (se 1 (by rfl) ⟨837620, by rfl⟩) R1675241
theorem R6982955 : Reach 6982955 := rs (se 1 (by rfl) ⟨5237216, by rfl⟩) R10474433
theorem R4492793 : Reach 4492793 := rs (se 2 (by rfl) ⟨1684797, by rfl⟩) R3369595
theorem R200297 : Reach 200297 := rs (se 2 (by rfl) ⟨75111, by rfl⟩) R150223
theorem R331721 : Reach 331721 := rs (se 2 (by rfl) ⟨124395, by rfl⟩) R248791
theorem R331775 : Reach 331775 := rs (se 1 (by rfl) ⟨248831, by rfl⟩) R497663
theorem R2396951 : Reach 2396951 := rs (se 1 (by rfl) ⟨1797713, by rfl⟩) R3595427
theorem R1087667 : Reach 1087667 := rs (se 1 (by rfl) ⟨815750, by rfl⟩) R1631501
theorem R334043 : Reach 334043 := rs (se 1 (by rfl) ⟨250532, by rfl⟩) R501065
theorem R891263 : Reach 891263 := rs (se 1 (by rfl) ⟨668447, by rfl⟩) R1336895
theorem R236351 : Reach 236351 := rs (se 1 (by rfl) ⟨177263, by rfl⟩) R354527
theorem R368297 : Reach 368297 := rs (se 2 (by rfl) ⟨138111, by rfl⟩) R276223
theorem R991033 : Reach 991033 := rs (se 2 (by rfl) ⟨371637, by rfl⟩) R743275
theorem R1515833 : Reach 1515833 := rs (se 2 (by rfl) ⟨568437, by rfl⟩) R1136875
theorem R107167 : Reach 107167 := rs (se 1 (by rfl) ⟨80375, by rfl⟩) R160751
theorem R1549115 : Reach 1549115 := rs (se 1 (by rfl) ⟨1161836, by rfl⟩) R2323673
theorem R173183 : Reach 173183 := rs (se 1 (by rfl) ⟨129887, by rfl⟩) R259775
theorem R501499 : Reach 501499 := rs (se 1 (by rfl) ⟨376124, by rfl⟩) R752249
theorem R698327 : Reach 698327 := rs (se 1 (by rfl) ⟨523745, by rfl⟩) R1047491
theorem R895423 : Reach 895423 := rs (se 1 (by rfl) ⟨671567, by rfl⟩) R1343135
theorem R830513 : Reach 830513 := rs (se 2 (by rfl) ⟨311442, by rfl⟩) R622885
theorem R1256795 : Reach 1256795 := rs (se 1 (by rfl) ⟨942596, by rfl⟩) R1885193
theorem R3059279 : Reach 3059279 := rs (se 1 (by rfl) ⟨2294459, by rfl⟩) R4588919
theorem R175951 : Reach 175951 := rs (se 1 (by rfl) ⟨131963, by rfl⟩) R263927
theorem R143663 : Reach 143663 := rs (se 1 (by rfl) ⟨107747, by rfl⟩) R215495
theorem R110911 : Reach 110911 := rs (se 1 (by rfl) ⟨83183, by rfl⟩) R166367
theorem R143999 : Reach 143999 := rs (se 1 (by rfl) ⟨107999, by rfl⟩) R215999
theorem R733859 : Reach 733859 := rs (se 1 (by rfl) ⟨550394, by rfl⟩) R1100789
theorem R145691 : Reach 145691 := rs (se 1 (by rfl) ⟨109268, by rfl⟩) R218537
theorem R146075 : Reach 146075 := rs (se 1 (by rfl) ⟨109556, by rfl⟩) R219113
theorem R146399 : Reach 146399 := rs (se 1 (by rfl) ⟨109799, by rfl⟩) R219599
theorem R671129 : Reach 671129 := rs (se 2 (by rfl) ⟨251673, by rfl⟩) R503347
theorem R147311 : Reach 147311 := rs (se 1 (by rfl) ⟨110483, by rfl⟩) R220967
theorem R147563 : Reach 147563 := rs (se 1 (by rfl) ⟨110672, by rfl⟩) R221345
theorem R147611 : Reach 147611 := rs (se 1 (by rfl) ⟨110708, by rfl⟩) R221417
theorem R148649 : Reach 148649 := rs (se 2 (by rfl) ⟨55743, by rfl⟩) R111487
theorem R869629 : Reach 869629 := rs (se 3 (by rfl) ⟨163055, by rfl⟩) R326111
theorem R215207 : Reach 215207 := rs (se 1 (by rfl) ⟨161405, by rfl⟩) R322811
theorem R543287 : Reach 543287 := rs (se 1 (by rfl) ⟨407465, by rfl⟩) R814931
theorem R215855 : Reach 215855 := rs (se 1 (by rfl) ⟨161891, by rfl⟩) R323783
theorem R740177 : Reach 740177 := rs (se 2 (by rfl) ⟨277566, by rfl⟩) R555133
theorem R413275 : Reach 413275 := rs (se 1 (by rfl) ⟨309956, by rfl⟩) R619913
theorem R184027 : Reach 184027 := rs (se 1 (by rfl) ⟨138020, by rfl⟩) R276041
theorem R610151 : Reach 610151 := rs (se 1 (by rfl) ⟨457613, by rfl⟩) R915227
theorem R119279 : Reach 119279 := rs (se 1 (by rfl) ⟨89459, by rfl⟩) R178919
theorem R185257 : Reach 185257 := rs (se 2 (by rfl) ⟨69471, by rfl⟩) R138943
theorem R744065 : Reach 744065 := rs (se 2 (by rfl) ⟨279024, by rfl⟩) R558049
theorem R220103 : Reach 220103 := rs (se 1 (by rfl) ⟨165077, by rfl⟩) R330155
theorem R220499 : Reach 220499 := rs (se 1 (by rfl) ⟨165374, by rfl⟩) R330749
theorem R777701 : Reach 777701 := rs (se 4 (by rfl) ⟨72909, by rfl⟩) R145819
theorem R123439 : Reach 123439 := rs (se 1 (by rfl) ⟨92579, by rfl⟩) R185159
theorem R5631767 : Reach 5631767 := rs (se 1 (by rfl) ⟨4223825, by rfl⟩) R8447651
theorem R193519 : Reach 193519 := rs (se 1 (by rfl) ⟨145139, by rfl⟩) R290279
theorem R95559 : Reach 95559 := rs (se 1 (by rfl) ⟨71669, by rfl⟩) R143339
theorem R95591 : Reach 95591 := rs (se 1 (by rfl) ⟨71693, by rfl⟩) R143387
theorem R96959 : Reach 96959 := rs (se 1 (by rfl) ⟨72719, by rfl⟩) R145439
theorem R195367 : Reach 195367 := rs (se 1 (by rfl) ⟨146525, by rfl⟩) R293051
theorem R1342271 : Reach 1342271 := rs (se 1 (by rfl) ⟨1006703, by rfl⟩) R2013407
theorem R97535 : Reach 97535 := rs (se 1 (by rfl) ⟨73151, by rfl⟩) R146303
theorem R97791 : Reach 97791 := rs (se 1 (by rfl) ⟨73343, by rfl⟩) R146687
theorem R98375 : Reach 98375 := rs (se 1 (by rfl) ⟨73781, by rfl⟩) R147563
theorem R98407 : Reach 98407 := rs (se 1 (by rfl) ⟨73805, by rfl⟩) R147611
theorem R164585 : Reach 164585 := rs (se 2 (by rfl) ⟨61719, by rfl⟩) R123439
theorem R99099 : Reach 99099 := rs (se 1 (by rfl) ⟨74324, by rfl⟩) R148649
theorem R132511 : Reach 132511 := rs (se 1 (by rfl) ⟨99383, by rfl⟩) R198767
theorem R362191 : Reach 362191 := rs (se 1 (by rfl) ⟨271643, by rfl⟩) R543287
theorem R493451 : Reach 493451 := rs (se 1 (by rfl) ⟨370088, by rfl⟩) R740177
theorem R4655303 : Reach 4655303 := rs (se 1 (by rfl) ⟨3491477, by rfl⟩) R6982955
theorem R133531 : Reach 133531 := rs (se 1 (by rfl) ⟨100148, by rfl⟩) R200297
theorem R725111 : Reach 725111 := rs (se 1 (by rfl) ⟨543833, by rfl⟩) R1087667
theorem R496043 : Reach 496043 := rs (se 1 (by rfl) ⟨372032, by rfl⟩) R744065
theorem R21142037 : Reach 21142037 := rs (se 6 (by rfl) ⟨495516, by rfl⟩) R991033
theorem R465551 : Reach 465551 := rs (se 1 (by rfl) ⟨349163, by rfl⟩) R698327
theorem R3579389 : Reach 3579389 := rs (se 3 (by rfl) ⟨671135, by rfl⟩) R1342271
theorem R2039519 : Reach 2039519 := rs (se 1 (by rfl) ⟨1529639, by rfl⟩) R3059279
theorem R2073869 : Reach 2073869 := rs (se 3 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R1223423 : Reach 1223423 := rs (se 1 (by rfl) ⟨917567, by rfl⟩) R1835135
theorem R142889 : Reach 142889 := rs (se 2 (by rfl) ⟨53583, by rfl⟩) R107167
theorem R1847285 : Reach 1847285 := rs (se 5 (by rfl) ⟨86591, by rfl⟩) R173183
theorem R3911759 : Reach 3911759 := rs (se 1 (by rfl) ⟨2933819, by rfl⟩) R5867639
theorem R143471 : Reach 143471 := rs (se 1 (by rfl) ⟨107603, by rfl⟩) R215207
theorem R1159505 : Reach 1159505 := rs (se 2 (by rfl) ⟨434814, by rfl⟩) R869629
theorem R143903 : Reach 143903 := rs (se 1 (by rfl) ⟨107927, by rfl⟩) R215855
theorem R668665 : Reach 668665 := rs (se 2 (by rfl) ⟨250749, by rfl⟩) R501499
theorem R1193897 : Reach 1193897 := rs (se 2 (by rfl) ⟨447711, by rfl⟩) R895423
theorem R146735 : Reach 146735 := rs (se 1 (by rfl) ⟨110051, by rfl⟩) R220103
theorem R146999 : Reach 146999 := rs (se 1 (by rfl) ⟨110249, by rfl⟩) R220499
theorem R245369 : Reach 245369 := rs (se 2 (by rfl) ⟨92013, by rfl⟩) R184027
theorem R245531 : Reach 245531 := rs (se 1 (by rfl) ⟨184148, by rfl⟩) R368297
theorem R147881 : Reach 147881 := rs (se 2 (by rfl) ⟨55455, by rfl⟩) R110911
theorem R1032743 : Reach 1032743 := rs (se 1 (by rfl) ⟨774557, by rfl⟩) R1549115
theorem R2376701 : Reach 2376701 := rs (se 3 (by rfl) ⟨445631, by rfl⟩) R891263
theorem R247009 : Reach 247009 := rs (se 2 (by rfl) ⟨92628, by rfl⟩) R185257
theorem R837863 : Reach 837863 := rs (se 1 (by rfl) ⟨628397, by rfl⟩) R1256795
theorem R3754511 : Reach 3754511 := rs (se 1 (by rfl) ⟨2815883, by rfl⟩) R5631767
theorem R11980781 : Reach 11980781 := rs (se 3 (by rfl) ⟨2246396, by rfl⟩) R4492793
theorem R938405 : Reach 938405 := rs (se 4 (by rfl) ⟨87975, by rfl⟩) R175951
theorem R447419 : Reach 447419 := rs (se 1 (by rfl) ⟨335564, by rfl⟩) R671129
theorem R1627069 : Reach 1627069 := rs (se 3 (by rfl) ⟨305075, by rfl⟩) R610151
theorem R218591 : Reach 218591 := rs (se 1 (by rfl) ⟨163943, by rfl⟩) R327887
theorem R219257 : Reach 219257 := rs (se 2 (by rfl) ⟨82221, by rfl⟩) R164443
theorem R318077 : Reach 318077 := rs (se 3 (by rfl) ⟨59639, by rfl⟩) R119279
theorem R744551 : Reach 744551 := rs (se 1 (by rfl) ⟨558413, by rfl⟩) R1116827
theorem R221147 : Reach 221147 := rs (se 1 (by rfl) ⟨165860, by rfl⟩) R331721
theorem R221183 : Reach 221183 := rs (se 1 (by rfl) ⟨165887, by rfl⟩) R331775
theorem R1597967 : Reach 1597967 := rs (se 1 (by rfl) ⟨1198475, by rfl⟩) R2396951
theorem R222695 : Reach 222695 := rs (se 1 (by rfl) ⟨167021, by rfl⟩) R334043
theorem R157567 : Reach 157567 := rs (se 1 (by rfl) ⟨118175, by rfl⟩) R236351
theorem R551033 : Reach 551033 := rs (se 2 (by rfl) ⟨206637, by rfl⟩) R413275
theorem R1010555 : Reach 1010555 := rs (se 1 (by rfl) ⟨757916, by rfl⟩) R1515833
theorem R258025 : Reach 258025 := rs (se 2 (by rfl) ⟨96759, by rfl⟩) R193519
theorem R553675 : Reach 553675 := rs (se 1 (by rfl) ⟨415256, by rfl⟩) R830513
theorem R95775 : Reach 95775 := rs (se 1 (by rfl) ⟨71831, by rfl⟩) R143663
theorem R95999 : Reach 95999 := rs (se 1 (by rfl) ⟨71999, by rfl⟩) R143999
theorem R489239 : Reach 489239 := rs (se 1 (by rfl) ⟨366929, by rfl⟩) R733859
theorem R260489 : Reach 260489 := rs (se 2 (by rfl) ⟨97683, by rfl⟩) R195367
theorem R97127 : Reach 97127 := rs (se 1 (by rfl) ⟨72845, by rfl⟩) R145691
theorem R97383 : Reach 97383 := rs (se 1 (by rfl) ⟨73037, by rfl⟩) R146075
theorem R97599 : Reach 97599 := rs (se 1 (by rfl) ⟨73199, by rfl⟩) R146399
theorem R98207 : Reach 98207 := rs (se 1 (by rfl) ⟨73655, by rfl⟩) R147311
theorem R98587 : Reach 98587 := rs (se 1 (by rfl) ⟨73940, by rfl⟩) R147881
theorem R688495 : Reach 688495 := rs (se 1 (by rfl) ⟨516371, by rfl⟩) R1032743
theorem R328967 : Reach 328967 := rs (se 1 (by rfl) ⟨246725, by rfl⟩) R493451
theorem R558575 : Reach 558575 := rs (se 1 (by rfl) ⟨418931, by rfl⟩) R837863
theorem R329345 : Reach 329345 := rs (se 2 (by rfl) ⟨123504, by rfl⟩) R247009
theorem R625603 : Reach 625603 := rs (se 1 (by rfl) ⟨469202, by rfl⟩) R938405
theorem R330695 : Reach 330695 := rs (se 1 (by rfl) ⟨248021, by rfl⟩) R496043
theorem R298279 : Reach 298279 := rs (se 1 (by rfl) ⟨223709, by rfl⟩) R447419
theorem R14094691 : Reach 14094691 := rs (se 1 (by rfl) ⟨10571018, by rfl⟩) R21142037
theorem R496367 : Reach 496367 := rs (se 1 (by rfl) ⟨372275, by rfl⟩) R744551
theorem R3183725 : Reach 3183725 := rs (se 3 (by rfl) ⟨596948, by rfl⟩) R1193897
theorem R1382579 : Reach 1382579 := rs (se 1 (by rfl) ⟨1036934, by rfl⟩) R2073869
theorem R2169425 : Reach 2169425 := rs (se 2 (by rfl) ⟨813534, by rfl⟩) R1627069
theorem R367355 : Reach 367355 := rs (se 1 (by rfl) ⟨275516, by rfl⟩) R551033
theorem R173659 : Reach 173659 := rs (se 1 (by rfl) ⟨130244, by rfl⟩) R260489
theorem R109723 : Reach 109723 := rs (se 1 (by rfl) ⟨82292, by rfl⟩) R164585
theorem R1584467 : Reach 1584467 := rs (se 1 (by rfl) ⟨1188350, by rfl⟩) R2376701
theorem R2503007 : Reach 2503007 := rs (se 1 (by rfl) ⟨1877255, by rfl⟩) R3754511
theorem R176681 : Reach 176681 := rs (se 2 (by rfl) ⟨66255, by rfl⟩) R132511
theorem R210089 : Reach 210089 := rs (se 2 (by rfl) ⟨78783, by rfl⟩) R157567
theorem R145727 : Reach 145727 := rs (se 1 (by rfl) ⟨109295, by rfl⟩) R218591
theorem R146171 : Reach 146171 := rs (se 1 (by rfl) ⟨109628, by rfl⟩) R219257
theorem R212051 : Reach 212051 := rs (se 1 (by rfl) ⟨159038, by rfl⟩) R318077
theorem R310367 : Reach 310367 := rs (se 1 (by rfl) ⟨232775, by rfl⟩) R465551
theorem R1359679 : Reach 1359679 := rs (se 1 (by rfl) ⟨1019759, by rfl⟩) R2039519
theorem R344033 : Reach 344033 := rs (se 2 (by rfl) ⟨129012, by rfl⟩) R258025
theorem R147431 : Reach 147431 := rs (se 1 (by rfl) ⟨110573, by rfl⟩) R221147
theorem R147455 : Reach 147455 := rs (se 1 (by rfl) ⟨110591, by rfl⟩) R221183
theorem R1065311 : Reach 1065311 := rs (se 1 (by rfl) ⟨798983, by rfl⟩) R1597967
theorem R738233 : Reach 738233 := rs (se 2 (by rfl) ⟨276837, by rfl⟩) R553675
theorem R148463 : Reach 148463 := rs (se 1 (by rfl) ⟨111347, by rfl⟩) R222695
theorem R673703 : Reach 673703 := rs (se 1 (by rfl) ⟨505277, by rfl⟩) R1010555
theorem R1231523 : Reach 1231523 := rs (se 1 (by rfl) ⟨923642, by rfl⟩) R1847285
theorem R2607839 : Reach 2607839 := rs (se 1 (by rfl) ⟨1955879, by rfl⟩) R3911759
theorem R773003 : Reach 773003 := rs (se 1 (by rfl) ⟨579752, by rfl⟩) R1159505
theorem R3103535 : Reach 3103535 := rs (se 1 (by rfl) ⟨2327651, by rfl⟩) R4655303
theorem R712165 : Reach 712165 := rs (se 4 (by rfl) ⟨66765, by rfl⟩) R133531
theorem R482921 : Reach 482921 := rs (se 2 (by rfl) ⟨181095, by rfl⟩) R362191
theorem R7987187 : Reach 7987187 := rs (se 1 (by rfl) ⟨5990390, by rfl⟩) R11980781
theorem R483407 : Reach 483407 := rs (se 1 (by rfl) ⟨362555, by rfl⟩) R725111
theorem R2386259 : Reach 2386259 := rs (se 1 (by rfl) ⟨1789694, by rfl⟩) R3579389
theorem R3566213 : Reach 3566213 := rs (se 4 (by rfl) ⟨334332, by rfl⟩) R668665
theorem R815615 : Reach 815615 := rs (se 1 (by rfl) ⟨611711, by rfl⟩) R1223423
theorem R95259 : Reach 95259 := rs (se 1 (by rfl) ⟨71444, by rfl⟩) R142889
theorem R95647 : Reach 95647 := rs (se 1 (by rfl) ⟨71735, by rfl⟩) R143471
theorem R95935 : Reach 95935 := rs (se 1 (by rfl) ⟨71951, by rfl⟩) R143903
theorem R326159 : Reach 326159 := rs (se 1 (by rfl) ⟨244619, by rfl⟩) R489239
theorem R97823 : Reach 97823 := rs (se 1 (by rfl) ⟨73367, by rfl⟩) R146735
theorem R97999 : Reach 97999 := rs (se 1 (by rfl) ⟨73499, by rfl⟩) R146999
theorem R163579 : Reach 163579 := rs (se 1 (by rfl) ⟨122684, by rfl⟩) R245369
theorem R163687 : Reach 163687 := rs (se 1 (by rfl) ⟨122765, by rfl⟩) R245531
theorem R917993 : Reach 917993 := rs (se 2 (by rfl) ⟨344247, by rfl⟩) R688495
theorem R492155 : Reach 492155 := rs (se 1 (by rfl) ⟨369116, by rfl⟩) R738233
theorem R98975 : Reach 98975 := rs (se 1 (by rfl) ⟨74231, by rfl⟩) R148463
theorem R821015 : Reach 821015 := rs (se 1 (by rfl) ⟨615761, by rfl⟩) R1231523
theorem R1738559 : Reach 1738559 := rs (se 1 (by rfl) ⟨1303919, by rfl⟩) R2607839
theorem R75171685 : Reach 75171685 := rs (se 4 (by rfl) ⟨7047345, by rfl⟩) R14094691
theorem R231545 : Reach 231545 := rs (se 2 (by rfl) ⟨86829, by rfl⟩) R173659
theorem R330911 : Reach 330911 := rs (se 1 (by rfl) ⟨248183, by rfl⟩) R496367
theorem R921719 : Reach 921719 := rs (se 1 (by rfl) ⟨691289, by rfl⟩) R1382579
theorem R1446283 : Reach 1446283 := rs (se 1 (by rfl) ⟨1084712, by rfl⟩) R2169425
theorem R2069023 : Reach 2069023 := rs (se 1 (by rfl) ⟨1551767, by rfl⟩) R3103535
theorem R1056311 : Reach 1056311 := rs (se 1 (by rfl) ⟨792233, by rfl⟩) R1584467
theorem R140059 : Reach 140059 := rs (se 1 (by rfl) ⟨105044, by rfl⟩) R210089
theorem R141367 : Reach 141367 := rs (se 1 (by rfl) ⟨106025, by rfl⟩) R212051
theorem R206911 : Reach 206911 := rs (se 1 (by rfl) ⟨155183, by rfl⟩) R310367
theorem R1812905 : Reach 1812905 := rs (se 2 (by rfl) ⟨679839, by rfl⟩) R1359679
theorem R372383 : Reach 372383 := rs (se 1 (by rfl) ⟨279287, by rfl⟩) R558575
theorem R834137 : Reach 834137 := rs (se 2 (by rfl) ⟨312801, by rfl⟩) R625603
theorem R146297 : Reach 146297 := rs (se 2 (by rfl) ⟨54861, by rfl⟩) R109723
theorem R244903 : Reach 244903 := rs (se 1 (by rfl) ⟨183677, by rfl⟩) R367355
theorem R5324791 : Reach 5324791 := rs (se 1 (by rfl) ⟨3993593, by rfl⟩) R7987187
theorem R1590821 : Reach 1590821 := rs (se 4 (by rfl) ⟨149139, by rfl⟩) R298279
theorem R1590839 : Reach 1590839 := rs (se 1 (by rfl) ⟨1193129, by rfl⟩) R2386259
theorem R2377475 : Reach 2377475 := rs (se 1 (by rfl) ⟨1783106, by rfl⟩) R3566213
theorem R543743 : Reach 543743 := rs (se 1 (by rfl) ⟨407807, by rfl⟩) R815615
theorem R117787 : Reach 117787 := rs (se 1 (by rfl) ⟨88340, by rfl⟩) R176681
theorem R217439 : Reach 217439 := rs (se 1 (by rfl) ⟨163079, by rfl⟩) R326159
theorem R218105 : Reach 218105 := rs (se 2 (by rfl) ⟨81789, by rfl⟩) R163579
theorem R218249 : Reach 218249 := rs (se 2 (by rfl) ⟨81843, by rfl⟩) R163687
theorem R710207 : Reach 710207 := rs (se 1 (by rfl) ⟨532655, by rfl⟩) R1065311
theorem R219311 : Reach 219311 := rs (se 1 (by rfl) ⟨164483, by rfl⟩) R328967
theorem R219563 : Reach 219563 := rs (se 1 (by rfl) ⟨164672, by rfl⟩) R329345
theorem R449135 : Reach 449135 := rs (se 1 (by rfl) ⟨336851, by rfl⟩) R673703
theorem R515335 : Reach 515335 := rs (se 1 (by rfl) ⟨386501, by rfl⟩) R773003
theorem R220463 : Reach 220463 := rs (se 1 (by rfl) ⟨165347, by rfl⟩) R330695
theorem R2122483 : Reach 2122483 := rs (se 1 (by rfl) ⟨1591862, by rfl⟩) R3183725
theorem R321947 : Reach 321947 := rs (se 1 (by rfl) ⟨241460, by rfl⟩) R482921
theorem R322271 : Reach 322271 := rs (se 1 (by rfl) ⟨241703, by rfl⟩) R483407
theorem R1668671 : Reach 1668671 := rs (se 1 (by rfl) ⟨1251503, by rfl⟩) R2503007
theorem R97151 : Reach 97151 := rs (se 1 (by rfl) ⟨72863, by rfl⟩) R145727
theorem R97447 : Reach 97447 := rs (se 1 (by rfl) ⟨73085, by rfl⟩) R146171
theorem R949553 : Reach 949553 := rs (se 2 (by rfl) ⟨356082, by rfl⟩) R712165
theorem R229355 : Reach 229355 := rs (se 1 (by rfl) ⟨172016, by rfl⟩) R344033
theorem R98287 : Reach 98287 := rs (se 1 (by rfl) ⟨73715, by rfl⟩) R147431
theorem R98303 : Reach 98303 := rs (se 1 (by rfl) ⟨73727, by rfl⟩) R147455
theorem R328103 : Reach 328103 := rs (se 1 (by rfl) ⟨246077, by rfl⟩) R492155
theorem R362495 : Reach 362495 := rs (se 1 (by rfl) ⟨271871, by rfl⟩) R543743
theorem R299423 : Reach 299423 := rs (se 1 (by rfl) ⟨224567, by rfl⟩) R449135
theorem R2758697 : Reach 2758697 := rs (se 2 (by rfl) ⟨1034511, by rfl⟩) R2069023
theorem R633035 : Reach 633035 := rs (se 1 (by rfl) ⟨474776, by rfl⟩) R949553
theorem R2829977 : Reach 2829977 := rs (se 2 (by rfl) ⟨1061241, by rfl⟩) R2122483
theorem R1060547 : Reach 1060547 := rs (se 1 (by rfl) ⟨795410, by rfl⟩) R1590821
theorem R1060559 : Reach 1060559 := rs (se 1 (by rfl) ⟨795419, by rfl⟩) R1590839
theorem R1584983 : Reach 1584983 := rs (se 1 (by rfl) ⟨1188737, by rfl⟩) R2377475
theorem R1159039 : Reach 1159039 := rs (se 1 (by rfl) ⟨869279, by rfl⟩) R1738559
theorem R275881 : Reach 275881 := rs (se 2 (by rfl) ⟨103455, by rfl⟩) R206911
theorem R144959 : Reach 144959 := rs (se 1 (by rfl) ⟨108719, by rfl⟩) R217439
theorem R145403 : Reach 145403 := rs (se 1 (by rfl) ⟨109052, by rfl⟩) R218105
theorem R145499 : Reach 145499 := rs (se 1 (by rfl) ⟨109124, by rfl⟩) R218249
theorem R473471 : Reach 473471 := rs (se 1 (by rfl) ⟨355103, by rfl⟩) R710207
theorem R146207 : Reach 146207 := rs (se 1 (by rfl) ⟨109655, by rfl⟩) R219311
theorem R146375 : Reach 146375 := rs (se 1 (by rfl) ⟨109781, by rfl⟩) R219563
theorem R146975 : Reach 146975 := rs (se 1 (by rfl) ⟨110231, by rfl⟩) R220463
theorem R704207 : Reach 704207 := rs (se 1 (by rfl) ⟨528155, by rfl⟩) R1056311
theorem R214631 : Reach 214631 := rs (se 1 (by rfl) ⟨160973, by rfl⟩) R321947
theorem R214847 : Reach 214847 := rs (se 1 (by rfl) ⟨161135, by rfl⟩) R322271
theorem R248255 : Reach 248255 := rs (se 1 (by rfl) ⟨186191, by rfl⟩) R372383
theorem R152903 : Reach 152903 := rs (se 1 (by rfl) ⟨114677, by rfl⟩) R229355
theorem R7099721 : Reach 7099721 := rs (se 2 (by rfl) ⟨2662395, by rfl⟩) R5324791
theorem R611995 : Reach 611995 := rs (se 1 (by rfl) ⟨458996, by rfl⟩) R917993
theorem R547343 : Reach 547343 := rs (se 1 (by rfl) ⟨410507, by rfl⟩) R821015
theorem R220607 : Reach 220607 := rs (se 1 (by rfl) ⟨165455, by rfl⟩) R330911
theorem R100228913 : Reach 100228913 := rs (se 2 (by rfl) ⟨37585842, by rfl⟩) R75171685
theorem R188489 : Reach 188489 := rs (se 2 (by rfl) ⟨70683, by rfl⟩) R141367
theorem R614479 : Reach 614479 := rs (se 1 (by rfl) ⟨460859, by rfl⟩) R921719
theorem R157049 : Reach 157049 := rs (se 2 (by rfl) ⟨58893, by rfl⟩) R117787
theorem R746981 : Reach 746981 := rs (se 4 (by rfl) ⟨70029, by rfl⟩) R140059
theorem R617453 : Reach 617453 := rs (se 3 (by rfl) ⟨115772, by rfl⟩) R231545
theorem R1928377 : Reach 1928377 := rs (se 2 (by rfl) ⟨723141, by rfl⟩) R1446283
theorem R1208603 : Reach 1208603 := rs (se 1 (by rfl) ⟨906452, by rfl⟩) R1812905
theorem R1112447 : Reach 1112447 := rs (se 1 (by rfl) ⟨834335, by rfl⟩) R1668671
theorem R326537 : Reach 326537 := rs (se 2 (by rfl) ⟨122451, by rfl⟩) R244903
theorem R687113 : Reach 687113 := rs (se 2 (by rfl) ⟨257667, by rfl⟩) R515335
theorem R556091 : Reach 556091 := rs (se 1 (by rfl) ⟨417068, by rfl⟩) R834137
theorem R97531 : Reach 97531 := rs (se 1 (by rfl) ⟨73148, by rfl⟩) R146297
theorem R819305 : Reach 819305 := rs (se 2 (by rfl) ⟨307239, by rfl⟩) R614479
theorem R165503 : Reach 165503 := rs (se 1 (by rfl) ⟨124127, by rfl⟩) R248255
theorem R101935 : Reach 101935 := rs (se 1 (by rfl) ⟨76451, by rfl⟩) R152903
theorem R1839131 : Reach 1839131 := rs (se 1 (by rfl) ⟨1379348, by rfl⟩) R2758697
theorem R364895 : Reach 364895 := rs (se 1 (by rfl) ⟨273671, by rfl⟩) R547343
theorem R66819275 : Reach 66819275 := rs (se 1 (by rfl) ⟨50114456, by rfl⟩) R100228913
theorem R104699 : Reach 104699 := rs (se 1 (by rfl) ⟨78524, by rfl⟩) R157049
theorem R497987 : Reach 497987 := rs (se 1 (by rfl) ⟨373490, by rfl⟩) R746981
theorem R367841 : Reach 367841 := rs (se 2 (by rfl) ⟨137940, by rfl⟩) R275881
theorem R1056655 : Reach 1056655 := rs (se 1 (by rfl) ⟨792491, by rfl⟩) R1584983
theorem R2828125 : Reach 2828125 := rs (se 3 (by rfl) ⟨530273, by rfl⟩) R1060547
theorem R370727 : Reach 370727 := rs (se 1 (by rfl) ⟨278045, by rfl⟩) R556091
theorem R469471 : Reach 469471 := rs (se 1 (by rfl) ⟨352103, by rfl⟩) R704207
theorem R143087 : Reach 143087 := rs (se 1 (by rfl) ⟨107315, by rfl⟩) R214631
theorem R798461 : Reach 798461 := rs (se 3 (by rfl) ⟨149711, by rfl⟩) R299423
theorem R143231 : Reach 143231 := rs (se 1 (by rfl) ⟨107423, by rfl⟩) R214847
theorem R241663 : Reach 241663 := rs (se 1 (by rfl) ⟨181247, by rfl⟩) R362495
theorem R4733147 : Reach 4733147 := rs (se 1 (by rfl) ⟨3549860, by rfl⟩) R7099721
theorem R147071 : Reach 147071 := rs (se 1 (by rfl) ⟨110303, by rfl⟩) R220607
theorem R411635 : Reach 411635 := rs (se 1 (by rfl) ⟨308726, by rfl⟩) R617453
theorem R1886651 : Reach 1886651 := rs (se 1 (by rfl) ⟨1414988, by rfl⟩) R2829977
theorem R707039 : Reach 707039 := rs (se 1 (by rfl) ⟨530279, by rfl⟩) R1060559
theorem R805735 : Reach 805735 := rs (se 1 (by rfl) ⟨604301, by rfl⟩) R1208603
theorem R741631 : Reach 741631 := rs (se 1 (by rfl) ⟨556223, by rfl⟩) R1112447
theorem R315647 : Reach 315647 := rs (se 1 (by rfl) ⟨236735, by rfl⟩) R473471
theorem R217691 : Reach 217691 := rs (se 1 (by rfl) ⟨163268, by rfl⟩) R326537
theorem R6181541 : Reach 6181541 := rs (se 4 (by rfl) ⟨579519, by rfl⟩) R1159039
theorem R218735 : Reach 218735 := rs (se 1 (by rfl) ⟨164051, by rfl⟩) R328103
theorem R125659 : Reach 125659 := rs (se 1 (by rfl) ⟨94244, by rfl⟩) R188489
theorem R10284677 : Reach 10284677 := rs (se 4 (by rfl) ⟨964188, by rfl⟩) R1928377
theorem R422023 : Reach 422023 := rs (se 1 (by rfl) ⟨316517, by rfl⟩) R633035
theorem R815993 : Reach 815993 := rs (se 2 (by rfl) ⟨305997, by rfl⟩) R611995
theorem R96639 : Reach 96639 := rs (se 1 (by rfl) ⟨72479, by rfl⟩) R144959
theorem R96935 : Reach 96935 := rs (se 1 (by rfl) ⟨72701, by rfl⟩) R145403
theorem R96999 : Reach 96999 := rs (se 1 (by rfl) ⟨72749, by rfl⟩) R145499
theorem R97471 : Reach 97471 := rs (se 1 (by rfl) ⟨73103, by rfl⟩) R146207
theorem R97583 : Reach 97583 := rs (se 1 (by rfl) ⟨73187, by rfl⟩) R146375
theorem R458075 : Reach 458075 := rs (se 1 (by rfl) ⟨343556, by rfl⟩) R687113
theorem R97983 : Reach 97983 := rs (se 1 (by rfl) ⟨73487, by rfl⟩) R146975
theorem R3770833 : Reach 3770833 := rs (se 2 (by rfl) ⟨1414062, by rfl⟩) R2828125
theorem R625961 : Reach 625961 := rs (se 2 (by rfl) ⟨234735, by rfl⟩) R469471
theorem R167545 : Reach 167545 := rs (se 2 (by rfl) ⟨62829, by rfl⟩) R125659
theorem R331991 : Reach 331991 := rs (se 1 (by rfl) ⟨248993, by rfl⟩) R497987
theorem R135913 : Reach 135913 := rs (se 2 (by rfl) ⟨50967, by rfl⟩) R101935
theorem R562697 : Reach 562697 := rs (se 2 (by rfl) ⟨211011, by rfl⟩) R422023
theorem R988841 : Reach 988841 := rs (se 2 (by rfl) ⟨370815, by rfl⟩) R741631
theorem R6856451 : Reach 6856451 := rs (se 1 (by rfl) ⟨5142338, by rfl⟩) R10284677
theorem R532307 : Reach 532307 := rs (se 1 (by rfl) ⟨399230, by rfl⟩) R798461
theorem R3155431 : Reach 3155431 := rs (se 1 (by rfl) ⟨2366573, by rfl⟩) R4733147
theorem R305383 : Reach 305383 := rs (se 1 (by rfl) ⟨229037, by rfl⟩) R458075
theorem R110335 : Reach 110335 := rs (se 1 (by rfl) ⟨82751, by rfl⟩) R165503
theorem R274423 : Reach 274423 := rs (se 1 (by rfl) ⟨205817, by rfl⟩) R411635
theorem R1257767 : Reach 1257767 := rs (se 1 (by rfl) ⟨943325, by rfl⟩) R1886651
theorem R471359 : Reach 471359 := rs (se 1 (by rfl) ⟨353519, by rfl⟩) R707039
theorem R1226087 : Reach 1226087 := rs (se 1 (by rfl) ⟨919565, by rfl⟩) R1839131
theorem R210431 : Reach 210431 := rs (se 1 (by rfl) ⟨157823, by rfl⟩) R315647
theorem R243263 : Reach 243263 := rs (se 1 (by rfl) ⟨182447, by rfl⟩) R364895
theorem R145127 : Reach 145127 := rs (se 1 (by rfl) ⟨108845, by rfl⟩) R217691
theorem R44546183 : Reach 44546183 := rs (se 1 (by rfl) ⟨33409637, by rfl⟩) R66819275
theorem R145823 : Reach 145823 := rs (se 1 (by rfl) ⟨109367, by rfl⟩) R218735
theorem R245227 : Reach 245227 := rs (se 1 (by rfl) ⟨183920, by rfl⟩) R367841
theorem R279197 : Reach 279197 := rs (se 3 (by rfl) ⟨52349, by rfl⟩) R104699
theorem R247151 : Reach 247151 := rs (se 1 (by rfl) ⟨185363, by rfl⟩) R370727
theorem R543995 : Reach 543995 := rs (se 1 (by rfl) ⟨407996, by rfl⟩) R815993
theorem R546203 : Reach 546203 := rs (se 1 (by rfl) ⟨409652, by rfl⟩) R819305
theorem R4121027 : Reach 4121027 := rs (se 1 (by rfl) ⟨3090770, by rfl⟩) R6181541
theorem R1074313 : Reach 1074313 := rs (se 2 (by rfl) ⟨402867, by rfl⟩) R805735
theorem R322217 : Reach 322217 := rs (se 2 (by rfl) ⟨120831, by rfl⟩) R241663
theorem R95391 : Reach 95391 := rs (se 1 (by rfl) ⟨71543, by rfl⟩) R143087
theorem R95487 : Reach 95487 := rs (se 1 (by rfl) ⟨71615, by rfl⟩) R143231
theorem R98047 : Reach 98047 := rs (se 1 (by rfl) ⟨73535, by rfl⟩) R147071
theorem R1408873 : Reach 1408873 := rs (se 2 (by rfl) ⟨528327, by rfl⟩) R1056655
theorem R164767 : Reach 164767 := rs (se 1 (by rfl) ⟨123575, by rfl⟩) R247151
theorem R362663 : Reach 362663 := rs (se 1 (by rfl) ⟨271997, by rfl⟩) R543995
theorem R364135 : Reach 364135 := rs (se 1 (by rfl) ⟨273101, by rfl⟩) R546203
theorem R659227 : Reach 659227 := rs (se 1 (by rfl) ⟨494420, by rfl⟩) R988841
theorem R365897 : Reach 365897 := rs (se 2 (by rfl) ⟨137211, by rfl⟩) R274423
theorem R140287 : Reach 140287 := rs (se 1 (by rfl) ⟨105215, by rfl⟩) R210431
theorem R29697455 : Reach 29697455 := rs (se 1 (by rfl) ⟨22273091, by rfl⟩) R44546183
theorem R1878497 : Reach 1878497 := rs (se 2 (by rfl) ⟨704436, by rfl⟩) R1408873
theorem R1256957 : Reach 1256957 := rs (se 3 (by rfl) ⟨235679, by rfl⟩) R471359
theorem R4207241 : Reach 4207241 := rs (se 2 (by rfl) ⟨1577715, by rfl⟩) R3155431
theorem R407177 : Reach 407177 := rs (se 2 (by rfl) ⟨152691, by rfl⟩) R305383
theorem R5027777 : Reach 5027777 := rs (se 2 (by rfl) ⟨1885416, by rfl⟩) R3770833
theorem R375131 : Reach 375131 := rs (se 1 (by rfl) ⟨281348, by rfl⟩) R562697
theorem R147113 : Reach 147113 := rs (se 2 (by rfl) ⟨55167, by rfl⟩) R110335
theorem R4570967 : Reach 4570967 := rs (se 1 (by rfl) ⟨3428225, by rfl⟩) R6856451
theorem R181217 : Reach 181217 := rs (se 2 (by rfl) ⟨67956, by rfl⟩) R135913
theorem R214811 : Reach 214811 := rs (se 1 (by rfl) ⟨161108, by rfl⟩) R322217
theorem R838511 : Reach 838511 := rs (se 1 (by rfl) ⟨628883, by rfl⟩) R1257767
theorem R186131 : Reach 186131 := rs (se 1 (by rfl) ⟨139598, by rfl⟩) R279197
theorem R1432417 : Reach 1432417 := rs (se 2 (by rfl) ⟨537156, by rfl⟩) R1074313
theorem R417307 : Reach 417307 := rs (se 1 (by rfl) ⟨312980, by rfl⟩) R625961
theorem R221327 : Reach 221327 := rs (se 1 (by rfl) ⟨165995, by rfl⟩) R331991
theorem R223393 : Reach 223393 := rs (se 2 (by rfl) ⟨83772, by rfl⟩) R167545
theorem R354871 : Reach 354871 := rs (se 1 (by rfl) ⟨266153, by rfl⟩) R532307
theorem R2747351 : Reach 2747351 := rs (se 1 (by rfl) ⟨2060513, by rfl⟩) R4121027
theorem R817391 : Reach 817391 := rs (se 1 (by rfl) ⟨613043, by rfl⟩) R1226087
theorem R162175 : Reach 162175 := rs (se 1 (by rfl) ⟨121631, by rfl⟩) R243263
theorem R96751 : Reach 96751 := rs (se 1 (by rfl) ⟨72563, by rfl⟩) R145127
theorem R97215 : Reach 97215 := rs (se 1 (by rfl) ⟨72911, by rfl⟩) R145823
theorem R326969 : Reach 326969 := rs (se 2 (by rfl) ⟨122613, by rfl⟩) R245227
theorem R559007 : Reach 559007 := rs (se 1 (by rfl) ⟨419255, by rfl⟩) R838511
theorem R297857 : Reach 297857 := rs (se 2 (by rfl) ⟨111696, by rfl⟩) R223393
theorem R1252331 : Reach 1252331 := rs (se 1 (by rfl) ⟨939248, by rfl⟩) R1878497
theorem R271451 : Reach 271451 := rs (se 1 (by rfl) ⟨203588, by rfl⟩) R407177
theorem R1909889 : Reach 1909889 := rs (se 2 (by rfl) ⟨716208, by rfl⟩) R1432417
theorem R3351851 : Reach 3351851 := rs (se 1 (by rfl) ⟨2513888, by rfl⟩) R5027777
theorem R143207 : Reach 143207 := rs (se 1 (by rfl) ⟨107405, by rfl⟩) R214811
theorem R241775 : Reach 241775 := rs (se 1 (by rfl) ⟨181331, by rfl⟩) R362663
theorem R243931 : Reach 243931 := rs (se 1 (by rfl) ⟨182948, by rfl⟩) R365897
theorem R147551 : Reach 147551 := rs (se 1 (by rfl) ⟨110663, by rfl⟩) R221327
theorem R837971 : Reach 837971 := rs (se 1 (by rfl) ⟨628478, by rfl⟩) R1256957
theorem R2804827 : Reach 2804827 := rs (se 1 (by rfl) ⟨2103620, by rfl⟩) R4207241
theorem R216233 : Reach 216233 := rs (se 2 (by rfl) ⟨81087, by rfl⟩) R162175
theorem R544927 : Reach 544927 := rs (se 1 (by rfl) ⟨408695, by rfl⟩) R817391
theorem R250087 : Reach 250087 := rs (se 1 (by rfl) ⟨187565, by rfl⟩) R375131
theorem R217979 : Reach 217979 := rs (se 1 (by rfl) ⟨163484, by rfl⟩) R326969
theorem R219689 : Reach 219689 := rs (se 2 (by rfl) ⟨82383, by rfl⟩) R164767
theorem R187049 : Reach 187049 := rs (se 2 (by rfl) ⟨70143, by rfl⟩) R140287
theorem R483245 : Reach 483245 := rs (se 3 (by rfl) ⟨90608, by rfl⟩) R181217
theorem R1892645 : Reach 1892645 := rs (se 4 (by rfl) ⟨177435, by rfl⟩) R354871
theorem R79193213 : Reach 79193213 := rs (se 3 (by rfl) ⟨14848727, by rfl⟩) R29697455
theorem R124087 : Reach 124087 := rs (se 1 (by rfl) ⟨93065, by rfl⟩) R186131
theorem R485513 : Reach 485513 := rs (se 2 (by rfl) ⟨182067, by rfl⟩) R364135
theorem R878969 : Reach 878969 := rs (se 2 (by rfl) ⟨329613, by rfl⟩) R659227
theorem R1831567 : Reach 1831567 := rs (se 1 (by rfl) ⟨1373675, by rfl⟩) R2747351
theorem R556409 : Reach 556409 := rs (se 2 (by rfl) ⟨208653, by rfl⟩) R417307
theorem R98075 : Reach 98075 := rs (se 1 (by rfl) ⟨73556, by rfl⟩) R147113
theorem R3047311 : Reach 3047311 := rs (se 1 (by rfl) ⟨2285483, by rfl⟩) R4570967
theorem R98367 : Reach 98367 := rs (se 1 (by rfl) ⟨73775, by rfl⟩) R147551
theorem R558647 : Reach 558647 := rs (se 1 (by rfl) ⟨418985, by rfl⟩) R837971
theorem R165449 : Reach 165449 := rs (se 2 (by rfl) ⟨62043, by rfl⟩) R124087
theorem R198571 : Reach 198571 := rs (se 1 (by rfl) ⟨148928, by rfl⟩) R297857
theorem R3739769 : Reach 3739769 := rs (se 2 (by rfl) ⟨1402413, by rfl⟩) R2804827
theorem R726569 : Reach 726569 := rs (se 2 (by rfl) ⟨272463, by rfl⟩) R544927
theorem R333449 : Reach 333449 := rs (se 2 (by rfl) ⟨125043, by rfl⟩) R250087
theorem R52795475 : Reach 52795475 := rs (se 1 (by rfl) ⟨39596606, by rfl⟩) R79193213
theorem R2234567 : Reach 2234567 := rs (se 1 (by rfl) ⟨1675925, by rfl⟩) R3351851
theorem R498797 : Reach 498797 := rs (se 3 (by rfl) ⟨93524, by rfl⟩) R187049
theorem R370939 : Reach 370939 := rs (se 1 (by rfl) ⟨278204, by rfl⟩) R556409
theorem R372671 : Reach 372671 := rs (se 1 (by rfl) ⟨279503, by rfl⟩) R559007
theorem R144155 : Reach 144155 := rs (se 1 (by rfl) ⟨108116, by rfl⟩) R216233
theorem R145319 : Reach 145319 := rs (se 1 (by rfl) ⟨108989, by rfl⟩) R217979
theorem R146459 : Reach 146459 := rs (se 1 (by rfl) ⟨109844, by rfl⟩) R219689
theorem R834887 : Reach 834887 := rs (se 1 (by rfl) ⟨626165, by rfl⟩) R1252331
theorem R1261763 : Reach 1261763 := rs (se 1 (by rfl) ⟨946322, by rfl⟩) R1892645
theorem R180967 : Reach 180967 := rs (se 1 (by rfl) ⟨135725, by rfl⟩) R271451
theorem R2442089 : Reach 2442089 := rs (se 2 (by rfl) ⟨915783, by rfl⟩) R1831567
theorem R2343917 : Reach 2343917 := rs (se 3 (by rfl) ⟨439484, by rfl⟩) R878969
theorem R322163 : Reach 322163 := rs (se 1 (by rfl) ⟨241622, by rfl⟩) R483245
theorem R1273259 : Reach 1273259 := rs (se 1 (by rfl) ⟨954944, by rfl⟩) R1909889
theorem R323675 : Reach 323675 := rs (se 1 (by rfl) ⟨242756, by rfl⟩) R485513
theorem R95471 : Reach 95471 := rs (se 1 (by rfl) ⟨71603, by rfl⟩) R143207
theorem R161183 : Reach 161183 := rs (se 1 (by rfl) ⟨120887, by rfl⟩) R241775
theorem R325241 : Reach 325241 := rs (se 2 (by rfl) ⟨121965, by rfl⟩) R243931
theorem R4063081 : Reach 4063081 := rs (se 2 (by rfl) ⟨1523655, by rfl⟩) R3047311
theorem R264761 : Reach 264761 := rs (se 2 (by rfl) ⟨99285, by rfl⟩) R198571
theorem R2493179 : Reach 2493179 := rs (se 1 (by rfl) ⟨1869884, by rfl⟩) R3739769
theorem R494585 : Reach 494585 := rs (se 2 (by rfl) ⟨185469, by rfl⟩) R370939
theorem R35196983 : Reach 35196983 := rs (se 1 (by rfl) ⟨26397737, by rfl⟩) R52795475
theorem R332531 : Reach 332531 := rs (se 1 (by rfl) ⟨249398, by rfl⟩) R498797
theorem R107455 : Reach 107455 := rs (se 1 (by rfl) ⟨80591, by rfl⟩) R161183
theorem R5417441 : Reach 5417441 := rs (se 2 (by rfl) ⟨2031540, by rfl⟩) R4063081
theorem R241289 : Reach 241289 := rs (se 2 (by rfl) ⟨90483, by rfl⟩) R180967
theorem R372431 : Reach 372431 := rs (se 1 (by rfl) ⟨279323, by rfl⟩) R558647
theorem R110299 : Reach 110299 := rs (se 1 (by rfl) ⟨82724, by rfl⟩) R165449
theorem R214775 : Reach 214775 := rs (se 1 (by rfl) ⟨161081, by rfl⟩) R322163
theorem R248447 : Reach 248447 := rs (se 1 (by rfl) ⟨186335, by rfl⟩) R372671
theorem R215783 : Reach 215783 := rs (se 1 (by rfl) ⟨161837, by rfl⟩) R323675
theorem R216827 : Reach 216827 := rs (se 1 (by rfl) ⟨162620, by rfl⟩) R325241
theorem R841175 : Reach 841175 := rs (se 1 (by rfl) ⟨630881, by rfl⟩) R1261763
theorem R1628059 : Reach 1628059 := rs (se 1 (by rfl) ⟨1221044, by rfl⟩) R2442089
theorem R1562611 : Reach 1562611 := rs (se 1 (by rfl) ⟨1171958, by rfl⟩) R2343917
theorem R484379 : Reach 484379 := rs (se 1 (by rfl) ⟨363284, by rfl⟩) R726569
theorem R222299 : Reach 222299 := rs (se 1 (by rfl) ⟨166724, by rfl⟩) R333449
theorem R5958845 : Reach 5958845 := rs (se 3 (by rfl) ⟨1117283, by rfl⟩) R2234567
theorem R848839 : Reach 848839 := rs (se 1 (by rfl) ⟨636629, by rfl⟩) R1273259
theorem R96103 : Reach 96103 := rs (se 1 (by rfl) ⟨72077, by rfl⟩) R144155
theorem R96879 : Reach 96879 := rs (se 1 (by rfl) ⟨72659, by rfl⟩) R145319
theorem R97639 : Reach 97639 := rs (se 1 (by rfl) ⟨73229, by rfl⟩) R146459
theorem R556591 : Reach 556591 := rs (se 1 (by rfl) ⟨417443, by rfl⟩) R834887
theorem R165631 : Reach 165631 := rs (se 1 (by rfl) ⟨124223, by rfl⟩) R248447
theorem R329723 : Reach 329723 := rs (se 1 (by rfl) ⟨247292, by rfl⟩) R494585
theorem R23464655 : Reach 23464655 := rs (se 1 (by rfl) ⟨17598491, by rfl⟩) R35196983
theorem R560783 : Reach 560783 := rs (se 1 (by rfl) ⟨420587, by rfl⟩) R841175
theorem R3611627 : Reach 3611627 := rs (se 1 (by rfl) ⟨2708720, by rfl⟩) R5417441
theorem R3972563 : Reach 3972563 := rs (se 1 (by rfl) ⟨2979422, by rfl⟩) R5958845
theorem R2170745 : Reach 2170745 := rs (se 2 (by rfl) ⟨814029, by rfl⟩) R1628059
theorem R143183 : Reach 143183 := rs (se 1 (by rfl) ⟨107387, by rfl⟩) R214775
theorem R143273 : Reach 143273 := rs (se 2 (by rfl) ⟨53727, by rfl⟩) R107455
theorem R176507 : Reach 176507 := rs (se 1 (by rfl) ⟨132380, by rfl⟩) R264761
theorem R143855 : Reach 143855 := rs (se 1 (by rfl) ⟨107891, by rfl⟩) R215783
theorem R144551 : Reach 144551 := rs (se 1 (by rfl) ⟨108413, by rfl⟩) R216827
theorem R147065 : Reach 147065 := rs (se 2 (by rfl) ⟨55149, by rfl⟩) R110299
theorem R148199 : Reach 148199 := rs (se 1 (by rfl) ⟨111149, by rfl⟩) R222299
theorem R1131785 : Reach 1131785 := rs (se 2 (by rfl) ⟨424419, by rfl⟩) R848839
theorem R248287 : Reach 248287 := rs (se 1 (by rfl) ⟨186215, by rfl⟩) R372431
theorem R2083481 : Reach 2083481 := rs (se 2 (by rfl) ⟨781305, by rfl⟩) R1562611
theorem R742121 : Reach 742121 := rs (se 2 (by rfl) ⟨278295, by rfl⟩) R556591
theorem R1662119 : Reach 1662119 := rs (se 1 (by rfl) ⟨1246589, by rfl⟩) R2493179
theorem R221687 : Reach 221687 := rs (se 1 (by rfl) ⟨166265, by rfl⟩) R332531
theorem R322919 : Reach 322919 := rs (se 1 (by rfl) ⟨242189, by rfl⟩) R484379
theorem R160859 : Reach 160859 := rs (se 1 (by rfl) ⟨120644, by rfl⟩) R241289
theorem R98799 : Reach 98799 := rs (se 1 (by rfl) ⟨74099, by rfl⟩) R148199
theorem R754523 : Reach 754523 := rs (se 1 (by rfl) ⟨565892, by rfl⟩) R1131785
theorem R494747 : Reach 494747 := rs (se 1 (by rfl) ⟨371060, by rfl⟩) R742121
theorem R331049 : Reach 331049 := rs (se 2 (by rfl) ⟨124143, by rfl⟩) R248287
theorem R1447163 : Reach 1447163 := rs (se 1 (by rfl) ⟨1085372, by rfl⟩) R2170745
theorem R107239 : Reach 107239 := rs (se 1 (by rfl) ⟨80429, by rfl⟩) R160859
theorem R1388987 : Reach 1388987 := rs (se 1 (by rfl) ⟨1041740, by rfl⟩) R2083481
theorem R15643103 : Reach 15643103 := rs (se 1 (by rfl) ⟨11732327, by rfl⟩) R23464655
theorem R373855 : Reach 373855 := rs (se 1 (by rfl) ⟨280391, by rfl⟩) R560783
theorem R2407751 : Reach 2407751 := rs (se 1 (by rfl) ⟨1805813, by rfl⟩) R3611627
theorem R147791 : Reach 147791 := rs (se 1 (by rfl) ⟨110843, by rfl⟩) R221687
theorem R215279 : Reach 215279 := rs (se 1 (by rfl) ⟨161459, by rfl⟩) R322919
theorem R117671 : Reach 117671 := rs (se 1 (by rfl) ⟨88253, by rfl⟩) R176507
theorem R219815 : Reach 219815 := rs (se 1 (by rfl) ⟨164861, by rfl⟩) R329723
theorem R220841 : Reach 220841 := rs (se 2 (by rfl) ⟨82815, by rfl⟩) R165631
theorem R1108079 : Reach 1108079 := rs (se 1 (by rfl) ⟨831059, by rfl⟩) R1662119
theorem R2648375 : Reach 2648375 := rs (se 1 (by rfl) ⟨1986281, by rfl⟩) R3972563
theorem R95455 : Reach 95455 := rs (se 1 (by rfl) ⟨71591, by rfl⟩) R143183
theorem R95515 : Reach 95515 := rs (se 1 (by rfl) ⟨71636, by rfl⟩) R143273
theorem R95903 : Reach 95903 := rs (se 1 (by rfl) ⟨71927, by rfl⟩) R143855
theorem R96367 : Reach 96367 := rs (se 1 (by rfl) ⟨72275, by rfl⟩) R144551
theorem R98043 : Reach 98043 := rs (se 1 (by rfl) ⟨73532, by rfl⟩) R147065
theorem R98527 : Reach 98527 := rs (se 1 (by rfl) ⟨73895, by rfl⟩) R147791
theorem R41714941 : Reach 41714941 := rs (se 3 (by rfl) ⟨7821551, by rfl⟩) R15643103
theorem R329831 : Reach 329831 := rs (se 1 (by rfl) ⟨247373, by rfl⟩) R494747
theorem R498473 : Reach 498473 := rs (se 2 (by rfl) ⟨186927, by rfl⟩) R373855
theorem R925991 : Reach 925991 := rs (se 1 (by rfl) ⟨694493, by rfl⟩) R1388987
theorem R503015 : Reach 503015 := rs (se 1 (by rfl) ⟨377261, by rfl⟩) R754523
theorem R142985 : Reach 142985 := rs (se 2 (by rfl) ⟨53619, by rfl⟩) R107239
theorem R143519 : Reach 143519 := rs (se 1 (by rfl) ⟨107639, by rfl⟩) R215279
theorem R964775 : Reach 964775 := rs (se 1 (by rfl) ⟨723581, by rfl⟩) R1447163
theorem R146543 : Reach 146543 := rs (se 1 (by rfl) ⟨109907, by rfl⟩) R219815
theorem R147227 : Reach 147227 := rs (se 1 (by rfl) ⟨110420, by rfl⟩) R220841
theorem R738719 : Reach 738719 := rs (se 1 (by rfl) ⟨554039, by rfl⟩) R1108079
theorem R313789 : Reach 313789 := rs (se 3 (by rfl) ⟨58835, by rfl⟩) R117671
theorem R220699 : Reach 220699 := rs (se 1 (by rfl) ⟨165524, by rfl⟩) R331049
theorem R1765583 : Reach 1765583 := rs (se 1 (by rfl) ⟨1324187, by rfl⟩) R2648375
theorem R1605167 : Reach 1605167 := rs (se 1 (by rfl) ⟨1203875, by rfl⟩) R2407751
theorem R492479 : Reach 492479 := rs (se 1 (by rfl) ⟨369359, by rfl⟩) R738719
theorem R332315 : Reach 332315 := rs (se 1 (by rfl) ⟨249236, by rfl⟩) R498473
theorem R55619921 : Reach 55619921 := rs (se 2 (by rfl) ⟨20857470, by rfl⟩) R41714941
theorem R643183 : Reach 643183 := rs (se 1 (by rfl) ⟨482387, by rfl⟩) R964775
theorem R1070111 : Reach 1070111 := rs (se 1 (by rfl) ⟨802583, by rfl⟩) R1605167
theorem R219887 : Reach 219887 := rs (se 1 (by rfl) ⟨164915, by rfl⟩) R329831
theorem R418385 : Reach 418385 := rs (se 2 (by rfl) ⟨156894, by rfl⟩) R313789
theorem R617327 : Reach 617327 := rs (se 1 (by rfl) ⟨462995, by rfl⟩) R925991
theorem R95323 : Reach 95323 := rs (se 1 (by rfl) ⟨71492, by rfl⟩) R142985
theorem R95679 : Reach 95679 := rs (se 1 (by rfl) ⟨71759, by rfl⟩) R143519
theorem R1177055 : Reach 1177055 := rs (se 1 (by rfl) ⟨882791, by rfl⟩) R1765583
theorem R1341373 : Reach 1341373 := rs (se 3 (by rfl) ⟨251507, by rfl⟩) R503015
theorem R294265 : Reach 294265 := rs (se 2 (by rfl) ⟨110349, by rfl⟩) R220699
theorem R97695 : Reach 97695 := rs (se 1 (by rfl) ⟨73271, by rfl⟩) R146543
theorem R98151 : Reach 98151 := rs (se 1 (by rfl) ⟨73613, by rfl⟩) R147227
theorem R328319 : Reach 328319 := rs (se 1 (by rfl) ⟨246239, by rfl⟩) R492479
theorem R146591 : Reach 146591 := rs (se 1 (by rfl) ⟨109943, by rfl⟩) R219887
theorem R278923 : Reach 278923 := rs (se 1 (by rfl) ⟨209192, by rfl⟩) R418385
theorem R411551 : Reach 411551 := rs (se 1 (by rfl) ⟨308663, by rfl⟩) R617327
theorem R1788497 : Reach 1788497 := rs (se 2 (by rfl) ⟨670686, by rfl⟩) R1341373
theorem R37079947 : Reach 37079947 := rs (se 1 (by rfl) ⟨27809960, by rfl⟩) R55619921
theorem R13721237 : Reach 13721237 := rs (se 6 (by rfl) ⟨321591, by rfl⟩) R643183
theorem R221543 : Reach 221543 := rs (se 1 (by rfl) ⟨166157, by rfl⟩) R332315
theorem R713407 : Reach 713407 := rs (se 1 (by rfl) ⟨535055, by rfl⟩) R1070111
theorem R784703 : Reach 784703 := rs (se 1 (by rfl) ⟨588527, by rfl⟩) R1177055
theorem R392353 : Reach 392353 := rs (se 2 (by rfl) ⟨147132, by rfl⟩) R294265
theorem R951209 : Reach 951209 := rs (se 2 (by rfl) ⟨356703, by rfl⟩) R713407
theorem R197759717 : Reach 197759717 := rs (se 4 (by rfl) ⟨18539973, by rfl⟩) R37079947
theorem R9147491 : Reach 9147491 := rs (se 1 (by rfl) ⟨6860618, by rfl⟩) R13721237
theorem R371897 : Reach 371897 := rs (se 2 (by rfl) ⟨139461, by rfl⟩) R278923
theorem R274367 : Reach 274367 := rs (se 1 (by rfl) ⟨205775, by rfl⟩) R411551
theorem R1192331 : Reach 1192331 := rs (se 1 (by rfl) ⟨894248, by rfl⟩) R1788497
theorem R147695 : Reach 147695 := rs (se 1 (by rfl) ⟨110771, by rfl⟩) R221543
theorem R218879 : Reach 218879 := rs (se 1 (by rfl) ⟨164159, by rfl⟩) R328319
theorem R2092549 : Reach 2092549 := rs (se 4 (by rfl) ⟨196176, by rfl⟩) R392353
theorem R523135 : Reach 523135 := rs (se 1 (by rfl) ⟨392351, by rfl⟩) R784703
theorem R97727 : Reach 97727 := rs (se 1 (by rfl) ⟨73295, by rfl⟩) R146591
theorem R98463 : Reach 98463 := rs (se 1 (by rfl) ⟨73847, by rfl⟩) R147695
theorem R6098327 : Reach 6098327 := rs (se 1 (by rfl) ⟨4573745, by rfl⟩) R9147491
theorem R2790065 : Reach 2790065 := rs (se 2 (by rfl) ⟨1046274, by rfl⟩) R2092549
theorem R794887 : Reach 794887 := rs (se 1 (by rfl) ⟨596165, by rfl⟩) R1192331
theorem R697513 : Reach 697513 := rs (se 2 (by rfl) ⟨261567, by rfl⟩) R523135
theorem R634139 : Reach 634139 := rs (se 1 (by rfl) ⟨475604, by rfl⟩) R951209
theorem R131839811 : Reach 131839811 := rs (se 1 (by rfl) ⟨98879858, by rfl⟩) R197759717
theorem R145919 : Reach 145919 := rs (se 1 (by rfl) ⟨109439, by rfl⟩) R218879
theorem R247931 : Reach 247931 := rs (se 1 (by rfl) ⟨185948, by rfl⟩) R371897
theorem R182911 : Reach 182911 := rs (se 1 (by rfl) ⟨137183, by rfl⟩) R274367
theorem R165287 : Reach 165287 := rs (se 1 (by rfl) ⟨123965, by rfl⟩) R247931
theorem R4065551 : Reach 4065551 := rs (se 1 (by rfl) ⟨3049163, by rfl⟩) R6098327
theorem R87893207 : Reach 87893207 := rs (se 1 (by rfl) ⟨65919905, by rfl⟩) R131839811
theorem R4239397 : Reach 4239397 := rs (se 4 (by rfl) ⟨397443, by rfl⟩) R794887
theorem R930017 : Reach 930017 := rs (se 2 (by rfl) ⟨348756, by rfl⟩) R697513
theorem R243881 : Reach 243881 := rs (se 2 (by rfl) ⟨91455, by rfl⟩) R182911
theorem R1860043 : Reach 1860043 := rs (se 1 (by rfl) ⟨1395032, by rfl⟩) R2790065
theorem R422759 : Reach 422759 := rs (se 1 (by rfl) ⟨317069, by rfl⟩) R634139
theorem R97279 : Reach 97279 := rs (se 1 (by rfl) ⟨72959, by rfl⟩) R145919
theorem R22610117 : Reach 22610117 := rs (se 4 (by rfl) ⟨2119698, by rfl⟩) R4239397
theorem R58595471 : Reach 58595471 := rs (se 1 (by rfl) ⟨43946603, by rfl⟩) R87893207
theorem R110191 : Reach 110191 := rs (se 1 (by rfl) ⟨82643, by rfl⟩) R165287
theorem R281839 : Reach 281839 := rs (se 1 (by rfl) ⟨211379, by rfl⟩) R422759
theorem R2480057 : Reach 2480057 := rs (se 2 (by rfl) ⟨930021, by rfl⟩) R1860043
theorem R2710367 : Reach 2710367 := rs (se 1 (by rfl) ⟨2032775, by rfl⟩) R4065551
theorem R620011 : Reach 620011 := rs (se 1 (by rfl) ⟨465008, by rfl⟩) R930017
theorem R162587 : Reach 162587 := rs (se 1 (by rfl) ⟨121940, by rfl⟩) R243881
theorem R60293645 : Reach 60293645 := rs (se 3 (by rfl) ⟨11305058, by rfl⟩) R22610117
theorem R39063647 : Reach 39063647 := rs (se 1 (by rfl) ⟨29297735, by rfl⟩) R58595471
theorem R1806911 : Reach 1806911 := rs (se 1 (by rfl) ⟨1355183, by rfl⟩) R2710367
theorem R826681 : Reach 826681 := rs (se 2 (by rfl) ⟨310005, by rfl⟩) R620011
theorem R108391 : Reach 108391 := rs (se 1 (by rfl) ⟨81293, by rfl⟩) R162587
theorem R1653371 : Reach 1653371 := rs (se 1 (by rfl) ⟨1240028, by rfl⟩) R2480057
theorem R375785 : Reach 375785 := rs (se 2 (by rfl) ⟨140919, by rfl⟩) R281839
theorem R146921 : Reach 146921 := rs (se 2 (by rfl) ⟨55095, by rfl⟩) R110191
theorem R144521 : Reach 144521 := rs (se 2 (by rfl) ⟨54195, by rfl⟩) R108391
theorem R1102241 : Reach 1102241 := rs (se 2 (by rfl) ⟨413340, by rfl⟩) R826681
theorem R1102247 : Reach 1102247 := rs (se 1 (by rfl) ⟨826685, by rfl⟩) R1653371
theorem R250523 : Reach 250523 := rs (se 1 (by rfl) ⟨187892, by rfl⟩) R375785
theorem R40195763 : Reach 40195763 := rs (se 1 (by rfl) ⟨30146822, by rfl⟩) R60293645
theorem R26042431 : Reach 26042431 := rs (se 1 (by rfl) ⟨19531823, by rfl⟩) R39063647
theorem R1204607 : Reach 1204607 := rs (se 1 (by rfl) ⟨903455, by rfl⟩) R1806911
theorem R97947 : Reach 97947 := rs (se 1 (by rfl) ⟨73460, by rfl⟩) R146921
theorem R167015 : Reach 167015 := rs (se 1 (by rfl) ⟨125261, by rfl⟩) R250523
theorem R734827 : Reach 734827 := rs (se 1 (by rfl) ⟨551120, by rfl⟩) R1102241
theorem R734831 : Reach 734831 := rs (se 1 (by rfl) ⟨551123, by rfl⟩) R1102247
theorem R803071 : Reach 803071 := rs (se 1 (by rfl) ⟨602303, by rfl⟩) R1204607
theorem R34723241 : Reach 34723241 := rs (se 2 (by rfl) ⟨13021215, by rfl⟩) R26042431
theorem R26797175 : Reach 26797175 := rs (se 1 (by rfl) ⟨20097881, by rfl⟩) R40195763
theorem R96347 : Reach 96347 := rs (se 1 (by rfl) ⟨72260, by rfl⟩) R144521
theorem R17864783 : Reach 17864783 := rs (se 1 (by rfl) ⟨13398587, by rfl⟩) R26797175
theorem R111343 : Reach 111343 := rs (se 1 (by rfl) ⟨83507, by rfl⟩) R167015
theorem R23148827 : Reach 23148827 := rs (se 1 (by rfl) ⟨17361620, by rfl⟩) R34723241
theorem R1070761 : Reach 1070761 := rs (se 2 (by rfl) ⟨401535, by rfl⟩) R803071
theorem R979769 : Reach 979769 := rs (se 2 (by rfl) ⟨367413, by rfl⟩) R734827
theorem R489887 : Reach 489887 := rs (se 1 (by rfl) ⟨367415, by rfl⟩) R734831
theorem R11909855 : Reach 11909855 := rs (se 1 (by rfl) ⟨8932391, by rfl⟩) R17864783
theorem R148457 : Reach 148457 := rs (se 2 (by rfl) ⟨55671, by rfl⟩) R111343
theorem R1427681 : Reach 1427681 := rs (se 2 (by rfl) ⟨535380, by rfl⟩) R1070761
theorem R653179 : Reach 653179 := rs (se 1 (by rfl) ⟨489884, by rfl⟩) R979769
theorem R15432551 : Reach 15432551 := rs (se 1 (by rfl) ⟨11574413, by rfl⟩) R23148827
theorem R326591 : Reach 326591 := rs (se 1 (by rfl) ⟨244943, by rfl⟩) R489887
theorem R98971 : Reach 98971 := rs (se 1 (by rfl) ⟨74228, by rfl⟩) R148457
theorem R951787 : Reach 951787 := rs (se 1 (by rfl) ⟨713840, by rfl⟩) R1427681
theorem R7939903 : Reach 7939903 := rs (se 1 (by rfl) ⟨5954927, by rfl⟩) R11909855
theorem R870905 : Reach 870905 := rs (se 2 (by rfl) ⟨326589, by rfl⟩) R653179
theorem R217727 : Reach 217727 := rs (se 1 (by rfl) ⟨163295, by rfl⟩) R326591
theorem R10288367 : Reach 10288367 := rs (se 1 (by rfl) ⟨7716275, by rfl⟩) R15432551
theorem R10586537 : Reach 10586537 := rs (se 2 (by rfl) ⟨3969951, by rfl⟩) R7939903
theorem R6858911 : Reach 6858911 := rs (se 1 (by rfl) ⟨5144183, by rfl⟩) R10288367
theorem R145151 : Reach 145151 := rs (se 1 (by rfl) ⟨108863, by rfl⟩) R217727
theorem R580603 : Reach 580603 := rs (se 1 (by rfl) ⟨435452, by rfl⟩) R870905
theorem R1269049 : Reach 1269049 := rs (se 2 (by rfl) ⟨475893, by rfl⟩) R951787
theorem R7057691 : Reach 7057691 := rs (se 1 (by rfl) ⟨5293268, by rfl⟩) R10586537
theorem R4572607 : Reach 4572607 := rs (se 1 (by rfl) ⟨3429455, by rfl⟩) R6858911
theorem R774137 : Reach 774137 := rs (se 2 (by rfl) ⟨290301, by rfl⟩) R580603
theorem R1692065 : Reach 1692065 := rs (se 2 (by rfl) ⟨634524, by rfl⟩) R1269049
theorem R96767 : Reach 96767 := rs (se 1 (by rfl) ⟨72575, by rfl⟩) R145151
theorem R6096809 : Reach 6096809 := rs (se 2 (by rfl) ⟨2286303, by rfl⟩) R4572607
theorem R1128043 : Reach 1128043 := rs (se 1 (by rfl) ⟨846032, by rfl⟩) R1692065
theorem R4705127 : Reach 4705127 := rs (se 1 (by rfl) ⟨3528845, by rfl⟩) R7057691
theorem R516091 : Reach 516091 := rs (se 1 (by rfl) ⟨387068, by rfl⟩) R774137
theorem R16258157 : Reach 16258157 := rs (se 3 (by rfl) ⟨3048404, by rfl⟩) R6096809
theorem R3136751 : Reach 3136751 := rs (se 1 (by rfl) ⟨2352563, by rfl⟩) R4705127
theorem R1504057 : Reach 1504057 := rs (se 2 (by rfl) ⟨564021, by rfl⟩) R1128043
theorem R688121 : Reach 688121 := rs (se 2 (by rfl) ⟨258045, by rfl⟩) R516091
theorem R2005409 : Reach 2005409 := rs (se 2 (by rfl) ⟨752028, by rfl⟩) R1504057
theorem R10838771 : Reach 10838771 := rs (se 1 (by rfl) ⟨8129078, by rfl⟩) R16258157
theorem R2091167 : Reach 2091167 := rs (se 1 (by rfl) ⟨1568375, by rfl⟩) R3136751
theorem R458747 : Reach 458747 := rs (se 1 (by rfl) ⟨344060, by rfl⟩) R688121
theorem R5347757 : Reach 5347757 := rs (se 3 (by rfl) ⟨1002704, by rfl⟩) R2005409
theorem R305831 : Reach 305831 := rs (se 1 (by rfl) ⟨229373, by rfl⟩) R458747
theorem R7225847 : Reach 7225847 := rs (se 1 (by rfl) ⟨5419385, by rfl⟩) R10838771
theorem R1394111 : Reach 1394111 := rs (se 1 (by rfl) ⟨1045583, by rfl⟩) R2091167
theorem R4817231 : Reach 4817231 := rs (se 1 (by rfl) ⟨3612923, by rfl⟩) R7225847
theorem R203887 : Reach 203887 := rs (se 1 (by rfl) ⟨152915, by rfl⟩) R305831
theorem R929407 : Reach 929407 := rs (se 1 (by rfl) ⟨697055, by rfl⟩) R1394111
theorem R3565171 : Reach 3565171 := rs (se 1 (by rfl) ⟨2673878, by rfl⟩) R5347757
theorem R3211487 : Reach 3211487 := rs (se 1 (by rfl) ⟨2408615, by rfl⟩) R4817231
theorem R4753561 : Reach 4753561 := rs (se 2 (by rfl) ⟨1782585, by rfl⟩) R3565171
theorem R271849 : Reach 271849 := rs (se 2 (by rfl) ⟨101943, by rfl⟩) R203887
theorem R1239209 : Reach 1239209 := rs (se 2 (by rfl) ⟨464703, by rfl⟩) R929407
theorem R362465 : Reach 362465 := rs (se 2 (by rfl) ⟨135924, by rfl⟩) R271849
theorem R826139 : Reach 826139 := rs (se 1 (by rfl) ⟨619604, by rfl⟩) R1239209
theorem R2140991 : Reach 2140991 := rs (se 1 (by rfl) ⟨1605743, by rfl⟩) R3211487
theorem R6338081 : Reach 6338081 := rs (se 2 (by rfl) ⟨2376780, by rfl⟩) R4753561
theorem R241643 : Reach 241643 := rs (se 1 (by rfl) ⟨181232, by rfl⟩) R362465
theorem R1427327 : Reach 1427327 := rs (se 1 (by rfl) ⟨1070495, by rfl⟩) R2140991
theorem R550759 : Reach 550759 := rs (se 1 (by rfl) ⟨413069, by rfl⟩) R826139
theorem R4225387 : Reach 4225387 := rs (se 1 (by rfl) ⟨3169040, by rfl⟩) R6338081
theorem R951551 : Reach 951551 := rs (se 1 (by rfl) ⟨713663, by rfl⟩) R1427327
theorem R734345 : Reach 734345 := rs (se 2 (by rfl) ⟨275379, by rfl⟩) R550759
theorem R161095 : Reach 161095 := rs (se 1 (by rfl) ⟨120821, by rfl⟩) R241643
theorem R5633849 : Reach 5633849 := rs (se 2 (by rfl) ⟨2112693, by rfl⟩) R4225387
theorem R634367 : Reach 634367 := rs (se 1 (by rfl) ⟨475775, by rfl⟩) R951551
theorem R214793 : Reach 214793 := rs (se 2 (by rfl) ⟨80547, by rfl⟩) R161095
theorem R3755899 : Reach 3755899 := rs (se 1 (by rfl) ⟨2816924, by rfl⟩) R5633849
theorem R489563 : Reach 489563 := rs (se 1 (by rfl) ⟨367172, by rfl⟩) R734345
theorem R143195 : Reach 143195 := rs (se 1 (by rfl) ⟨107396, by rfl⟩) R214793
theorem R5007865 : Reach 5007865 := rs (se 2 (by rfl) ⟨1877949, by rfl⟩) R3755899
theorem R422911 : Reach 422911 := rs (se 1 (by rfl) ⟨317183, by rfl⟩) R634367
theorem R326375 : Reach 326375 := rs (se 1 (by rfl) ⟨244781, by rfl⟩) R489563
theorem R563881 : Reach 563881 := rs (se 2 (by rfl) ⟨211455, by rfl⟩) R422911
theorem R217583 : Reach 217583 := rs (se 1 (by rfl) ⟨163187, by rfl⟩) R326375
theorem R6677153 : Reach 6677153 := rs (se 2 (by rfl) ⟨2503932, by rfl⟩) R5007865
theorem R95463 : Reach 95463 := rs (se 1 (by rfl) ⟨71597, by rfl⟩) R143195
theorem R145055 : Reach 145055 := rs (se 1 (by rfl) ⟨108791, by rfl⟩) R217583
theorem R4451435 : Reach 4451435 := rs (se 1 (by rfl) ⟨3338576, by rfl⟩) R6677153
theorem R751841 : Reach 751841 := rs (se 2 (by rfl) ⟨281940, by rfl⟩) R563881
theorem R501227 : Reach 501227 := rs (se 1 (by rfl) ⟨375920, by rfl⟩) R751841
theorem R2967623 : Reach 2967623 := rs (se 1 (by rfl) ⟨2225717, by rfl⟩) R4451435
theorem R96703 : Reach 96703 := rs (se 1 (by rfl) ⟨72527, by rfl⟩) R145055
theorem R334151 : Reach 334151 := rs (se 1 (by rfl) ⟨250613, by rfl⟩) R501227
theorem R1978415 : Reach 1978415 := rs (se 1 (by rfl) ⟨1483811, by rfl⟩) R2967623
theorem R1318943 : Reach 1318943 := rs (se 1 (by rfl) ⟨989207, by rfl⟩) R1978415
theorem R222767 : Reach 222767 := rs (se 1 (by rfl) ⟨167075, by rfl⟩) R334151
theorem R148511 : Reach 148511 := rs (se 1 (by rfl) ⟨111383, by rfl⟩) R222767
theorem R879295 : Reach 879295 := rs (se 1 (by rfl) ⟨659471, by rfl⟩) R1318943
theorem R99007 : Reach 99007 := rs (se 1 (by rfl) ⟨74255, by rfl⟩) R148511
theorem R1172393 : Reach 1172393 := rs (se 2 (by rfl) ⟨439647, by rfl⟩) R879295
theorem R781595 : Reach 781595 := rs (se 1 (by rfl) ⟨586196, by rfl⟩) R1172393
theorem R521063 : Reach 521063 := rs (se 1 (by rfl) ⟨390797, by rfl⟩) R781595
theorem R347375 : Reach 347375 := rs (se 1 (by rfl) ⟨260531, by rfl⟩) R521063
theorem R231583 : Reach 231583 := rs (se 1 (by rfl) ⟨173687, by rfl⟩) R347375
theorem R308777 : Reach 308777 := rs (se 2 (by rfl) ⟨115791, by rfl⟩) R231583
theorem R823405 : Reach 823405 := rs (se 3 (by rfl) ⟨154388, by rfl⟩) R308777
theorem R1097873 : Reach 1097873 := rs (se 2 (by rfl) ⟨411702, by rfl⟩) R823405
theorem R731915 : Reach 731915 := rs (se 1 (by rfl) ⟨548936, by rfl⟩) R1097873
theorem R487943 : Reach 487943 := rs (se 1 (by rfl) ⟨365957, by rfl⟩) R731915
theorem R325295 : Reach 325295 := rs (se 1 (by rfl) ⟨243971, by rfl⟩) R487943
theorem R216863 : Reach 216863 := rs (se 1 (by rfl) ⟨162647, by rfl⟩) R325295
theorem R144575 : Reach 144575 := rs (se 1 (by rfl) ⟨108431, by rfl⟩) R216863
theorem R96383 : Reach 96383 := rs (se 1 (by rfl) ⟨72287, by rfl⟩) R144575

theorem C0 (j : ℕ) (h1 : 47565 ≤ j) (h2 : j ≤ 48264) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R95131
  · exact R95133
  · exact R95135
  · exact R95137
  · exact R95139
  · exact R95141
  · exact R95143
  · exact R95145
  · exact R95147
  · exact R95149
  · exact R95151
  · exact R95153
  · exact R95155
  · exact R95157
  · exact R95159
  · exact R95161
  · exact R95163
  · exact R95165
  · exact R95167
  · exact R95169
  · exact R95171
  · exact R95173
  · exact R95175
  · exact R95177
  · exact R95179
  · exact R95181
  · exact R95183
  · exact R95185
  · exact R95187
  · exact R95189
  · exact R95191
  · exact R95193
  · exact R95195
  · exact R95197
  · exact R95199
  · exact R95201
  · exact R95203
  · exact R95205
  · exact R95207
  · exact R95209
  · exact R95211
  · exact R95213
  · exact R95215
  · exact R95217
  · exact R95219
  · exact R95221
  · exact R95223
  · exact R95225
  · exact R95227
  · exact R95229
  · exact R95231
  · exact R95233
  · exact R95235
  · exact R95237
  · exact R95239
  · exact R95241
  · exact R95243
  · exact R95245
  · exact R95247
  · exact R95249
  · exact R95251
  · exact R95253
  · exact R95255
  · exact R95257
  · exact R95259
  · exact R95261
  · exact R95263
  · exact R95265
  · exact R95267
  · exact R95269
  · exact R95271
  · exact R95273
  · exact R95275
  · exact R95277
  · exact R95279
  · exact R95281
  · exact R95283
  · exact R95285
  · exact R95287
  · exact R95289
  · exact R95291
  · exact R95293
  · exact R95295
  · exact R95297
  · exact R95299
  · exact R95301
  · exact R95303
  · exact R95305
  · exact R95307
  · exact R95309
  · exact R95311
  · exact R95313
  · exact R95315
  · exact R95317
  · exact R95319
  · exact R95321
  · exact R95323
  · exact R95325
  · exact R95327
  · exact R95329
  · exact R95331
  · exact R95333
  · exact R95335
  · exact R95337
  · exact R95339
  · exact R95341
  · exact R95343
  · exact R95345
  · exact R95347
  · exact R95349
  · exact R95351
  · exact R95353
  · exact R95355
  · exact R95357
  · exact R95359
  · exact R95361
  · exact R95363
  · exact R95365
  · exact R95367
  · exact R95369
  · exact R95371
  · exact R95373
  · exact R95375
  · exact R95377
  · exact R95379
  · exact R95381
  · exact R95383
  · exact R95385
  · exact R95387
  · exact R95389
  · exact R95391
  · exact R95393
  · exact R95395
  · exact R95397
  · exact R95399
  · exact R95401
  · exact R95403
  · exact R95405
  · exact R95407
  · exact R95409
  · exact R95411
  · exact R95413
  · exact R95415
  · exact R95417
  · exact R95419
  · exact R95421
  · exact R95423
  · exact R95425
  · exact R95427
  · exact R95429
  · exact R95431
  · exact R95433
  · exact R95435
  · exact R95437
  · exact R95439
  · exact R95441
  · exact R95443
  · exact R95445
  · exact R95447
  · exact R95449
  · exact R95451
  · exact R95453
  · exact R95455
  · exact R95457
  · exact R95459
  · exact R95461
  · exact R95463
  · exact R95465
  · exact R95467
  · exact R95469
  · exact R95471
  · exact R95473
  · exact R95475
  · exact R95477
  · exact R95479
  · exact R95481
  · exact R95483
  · exact R95485
  · exact R95487
  · exact R95489
  · exact R95491
  · exact R95493
  · exact R95495
  · exact R95497
  · exact R95499
  · exact R95501
  · exact R95503
  · exact R95505
  · exact R95507
  · exact R95509
  · exact R95511
  · exact R95513
  · exact R95515
  · exact R95517
  · exact R95519
  · exact R95521
  · exact R95523
  · exact R95525
  · exact R95527
  · exact R95529
  · exact R95531
  · exact R95533
  · exact R95535
  · exact R95537
  · exact R95539
  · exact R95541
  · exact R95543
  · exact R95545
  · exact R95547
  · exact R95549
  · exact R95551
  · exact R95553
  · exact R95555
  · exact R95557
  · exact R95559
  · exact R95561
  · exact R95563
  · exact R95565
  · exact R95567
  · exact R95569
  · exact R95571
  · exact R95573
  · exact R95575
  · exact R95577
  · exact R95579
  · exact R95581
  · exact R95583
  · exact R95585
  · exact R95587
  · exact R95589
  · exact R95591
  · exact R95593
  · exact R95595
  · exact R95597
  · exact R95599
  · exact R95601
  · exact R95603
  · exact R95605
  · exact R95607
  · exact R95609
  · exact R95611
  · exact R95613
  · exact R95615
  · exact R95617
  · exact R95619
  · exact R95621
  · exact R95623
  · exact R95625
  · exact R95627
  · exact R95629
  · exact R95631
  · exact R95633
  · exact R95635
  · exact R95637
  · exact R95639
  · exact R95641
  · exact R95643
  · exact R95645
  · exact R95647
  · exact R95649
  · exact R95651
  · exact R95653
  · exact R95655
  · exact R95657
  · exact R95659
  · exact R95661
  · exact R95663
  · exact R95665
  · exact R95667
  · exact R95669
  · exact R95671
  · exact R95673
  · exact R95675
  · exact R95677
  · exact R95679
  · exact R95681
  · exact R95683
  · exact R95685
  · exact R95687
  · exact R95689
  · exact R95691
  · exact R95693
  · exact R95695
  · exact R95697
  · exact R95699
  · exact R95701
  · exact R95703
  · exact R95705
  · exact R95707
  · exact R95709
  · exact R95711
  · exact R95713
  · exact R95715
  · exact R95717
  · exact R95719
  · exact R95721
  · exact R95723
  · exact R95725
  · exact R95727
  · exact R95729
  · exact R95731
  · exact R95733
  · exact R95735
  · exact R95737
  · exact R95739
  · exact R95741
  · exact R95743
  · exact R95745
  · exact R95747
  · exact R95749
  · exact R95751
  · exact R95753
  · exact R95755
  · exact R95757
  · exact R95759
  · exact R95761
  · exact R95763
  · exact R95765
  · exact R95767
  · exact R95769
  · exact R95771
  · exact R95773
  · exact R95775
  · exact R95777
  · exact R95779
  · exact R95781
  · exact R95783
  · exact R95785
  · exact R95787
  · exact R95789
  · exact R95791
  · exact R95793
  · exact R95795
  · exact R95797
  · exact R95799
  · exact R95801
  · exact R95803
  · exact R95805
  · exact R95807
  · exact R95809
  · exact R95811
  · exact R95813
  · exact R95815
  · exact R95817
  · exact R95819
  · exact R95821
  · exact R95823
  · exact R95825
  · exact R95827
  · exact R95829
  · exact R95831
  · exact R95833
  · exact R95835
  · exact R95837
  · exact R95839
  · exact R95841
  · exact R95843
  · exact R95845
  · exact R95847
  · exact R95849
  · exact R95851
  · exact R95853
  · exact R95855
  · exact R95857
  · exact R95859
  · exact R95861
  · exact R95863
  · exact R95865
  · exact R95867
  · exact R95869
  · exact R95871
  · exact R95873
  · exact R95875
  · exact R95877
  · exact R95879
  · exact R95881
  · exact R95883
  · exact R95885
  · exact R95887
  · exact R95889
  · exact R95891
  · exact R95893
  · exact R95895
  · exact R95897
  · exact R95899
  · exact R95901
  · exact R95903
  · exact R95905
  · exact R95907
  · exact R95909
  · exact R95911
  · exact R95913
  · exact R95915
  · exact R95917
  · exact R95919
  · exact R95921
  · exact R95923
  · exact R95925
  · exact R95927
  · exact R95929
  · exact R95931
  · exact R95933
  · exact R95935
  · exact R95937
  · exact R95939
  · exact R95941
  · exact R95943
  · exact R95945
  · exact R95947
  · exact R95949
  · exact R95951
  · exact R95953
  · exact R95955
  · exact R95957
  · exact R95959
  · exact R95961
  · exact R95963
  · exact R95965
  · exact R95967
  · exact R95969
  · exact R95971
  · exact R95973
  · exact R95975
  · exact R95977
  · exact R95979
  · exact R95981
  · exact R95983
  · exact R95985
  · exact R95987
  · exact R95989
  · exact R95991
  · exact R95993
  · exact R95995
  · exact R95997
  · exact R95999
  · exact R96001
  · exact R96003
  · exact R96005
  · exact R96007
  · exact R96009
  · exact R96011
  · exact R96013
  · exact R96015
  · exact R96017
  · exact R96019
  · exact R96021
  · exact R96023
  · exact R96025
  · exact R96027
  · exact R96029
  · exact R96031
  · exact R96033
  · exact R96035
  · exact R96037
  · exact R96039
  · exact R96041
  · exact R96043
  · exact R96045
  · exact R96047
  · exact R96049
  · exact R96051
  · exact R96053
  · exact R96055
  · exact R96057
  · exact R96059
  · exact R96061
  · exact R96063
  · exact R96065
  · exact R96067
  · exact R96069
  · exact R96071
  · exact R96073
  · exact R96075
  · exact R96077
  · exact R96079
  · exact R96081
  · exact R96083
  · exact R96085
  · exact R96087
  · exact R96089
  · exact R96091
  · exact R96093
  · exact R96095
  · exact R96097
  · exact R96099
  · exact R96101
  · exact R96103
  · exact R96105
  · exact R96107
  · exact R96109
  · exact R96111
  · exact R96113
  · exact R96115
  · exact R96117
  · exact R96119
  · exact R96121
  · exact R96123
  · exact R96125
  · exact R96127
  · exact R96129
  · exact R96131
  · exact R96133
  · exact R96135
  · exact R96137
  · exact R96139
  · exact R96141
  · exact R96143
  · exact R96145
  · exact R96147
  · exact R96149
  · exact R96151
  · exact R96153
  · exact R96155
  · exact R96157
  · exact R96159
  · exact R96161
  · exact R96163
  · exact R96165
  · exact R96167
  · exact R96169
  · exact R96171
  · exact R96173
  · exact R96175
  · exact R96177
  · exact R96179
  · exact R96181
  · exact R96183
  · exact R96185
  · exact R96187
  · exact R96189
  · exact R96191
  · exact R96193
  · exact R96195
  · exact R96197
  · exact R96199
  · exact R96201
  · exact R96203
  · exact R96205
  · exact R96207
  · exact R96209
  · exact R96211
  · exact R96213
  · exact R96215
  · exact R96217
  · exact R96219
  · exact R96221
  · exact R96223
  · exact R96225
  · exact R96227
  · exact R96229
  · exact R96231
  · exact R96233
  · exact R96235
  · exact R96237
  · exact R96239
  · exact R96241
  · exact R96243
  · exact R96245
  · exact R96247
  · exact R96249
  · exact R96251
  · exact R96253
  · exact R96255
  · exact R96257
  · exact R96259
  · exact R96261
  · exact R96263
  · exact R96265
  · exact R96267
  · exact R96269
  · exact R96271
  · exact R96273
  · exact R96275
  · exact R96277
  · exact R96279
  · exact R96281
  · exact R96283
  · exact R96285
  · exact R96287
  · exact R96289
  · exact R96291
  · exact R96293
  · exact R96295
  · exact R96297
  · exact R96299
  · exact R96301
  · exact R96303
  · exact R96305
  · exact R96307
  · exact R96309
  · exact R96311
  · exact R96313
  · exact R96315
  · exact R96317
  · exact R96319
  · exact R96321
  · exact R96323
  · exact R96325
  · exact R96327
  · exact R96329
  · exact R96331
  · exact R96333
  · exact R96335
  · exact R96337
  · exact R96339
  · exact R96341
  · exact R96343
  · exact R96345
  · exact R96347
  · exact R96349
  · exact R96351
  · exact R96353
  · exact R96355
  · exact R96357
  · exact R96359
  · exact R96361
  · exact R96363
  · exact R96365
  · exact R96367
  · exact R96369
  · exact R96371
  · exact R96373
  · exact R96375
  · exact R96377
  · exact R96379
  · exact R96381
  · exact R96383
  · exact R96385
  · exact R96387
  · exact R96389
  · exact R96391
  · exact R96393
  · exact R96395
  · exact R96397
  · exact R96399
  · exact R96401
  · exact R96403
  · exact R96405
  · exact R96407
  · exact R96409
  · exact R96411
  · exact R96413
  · exact R96415
  · exact R96417
  · exact R96419
  · exact R96421
  · exact R96423
  · exact R96425
  · exact R96427
  · exact R96429
  · exact R96431
  · exact R96433
  · exact R96435
  · exact R96437
  · exact R96439
  · exact R96441
  · exact R96443
  · exact R96445
  · exact R96447
  · exact R96449
  · exact R96451
  · exact R96453
  · exact R96455
  · exact R96457
  · exact R96459
  · exact R96461
  · exact R96463
  · exact R96465
  · exact R96467
  · exact R96469
  · exact R96471
  · exact R96473
  · exact R96475
  · exact R96477
  · exact R96479
  · exact R96481
  · exact R96483
  · exact R96485
  · exact R96487
  · exact R96489
  · exact R96491
  · exact R96493
  · exact R96495
  · exact R96497
  · exact R96499
  · exact R96501
  · exact R96503
  · exact R96505
  · exact R96507
  · exact R96509
  · exact R96511
  · exact R96513
  · exact R96515
  · exact R96517
  · exact R96519
  · exact R96521
  · exact R96523
  · exact R96525
  · exact R96527
  · exact R96529

theorem C1 (j : ℕ) (h1 : 48265 ≤ j) (h2 : j ≤ 48964) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R96531
  · exact R96533
  · exact R96535
  · exact R96537
  · exact R96539
  · exact R96541
  · exact R96543
  · exact R96545
  · exact R96547
  · exact R96549
  · exact R96551
  · exact R96553
  · exact R96555
  · exact R96557
  · exact R96559
  · exact R96561
  · exact R96563
  · exact R96565
  · exact R96567
  · exact R96569
  · exact R96571
  · exact R96573
  · exact R96575
  · exact R96577
  · exact R96579
  · exact R96581
  · exact R96583
  · exact R96585
  · exact R96587
  · exact R96589
  · exact R96591
  · exact R96593
  · exact R96595
  · exact R96597
  · exact R96599
  · exact R96601
  · exact R96603
  · exact R96605
  · exact R96607
  · exact R96609
  · exact R96611
  · exact R96613
  · exact R96615
  · exact R96617
  · exact R96619
  · exact R96621
  · exact R96623
  · exact R96625
  · exact R96627
  · exact R96629
  · exact R96631
  · exact R96633
  · exact R96635
  · exact R96637
  · exact R96639
  · exact R96641
  · exact R96643
  · exact R96645
  · exact R96647
  · exact R96649
  · exact R96651
  · exact R96653
  · exact R96655
  · exact R96657
  · exact R96659
  · exact R96661
  · exact R96663
  · exact R96665
  · exact R96667
  · exact R96669
  · exact R96671
  · exact R96673
  · exact R96675
  · exact R96677
  · exact R96679
  · exact R96681
  · exact R96683
  · exact R96685
  · exact R96687
  · exact R96689
  · exact R96691
  · exact R96693
  · exact R96695
  · exact R96697
  · exact R96699
  · exact R96701
  · exact R96703
  · exact R96705
  · exact R96707
  · exact R96709
  · exact R96711
  · exact R96713
  · exact R96715
  · exact R96717
  · exact R96719
  · exact R96721
  · exact R96723
  · exact R96725
  · exact R96727
  · exact R96729
  · exact R96731
  · exact R96733
  · exact R96735
  · exact R96737
  · exact R96739
  · exact R96741
  · exact R96743
  · exact R96745
  · exact R96747
  · exact R96749
  · exact R96751
  · exact R96753
  · exact R96755
  · exact R96757
  · exact R96759
  · exact R96761
  · exact R96763
  · exact R96765
  · exact R96767
  · exact R96769
  · exact R96771
  · exact R96773
  · exact R96775
  · exact R96777
  · exact R96779
  · exact R96781
  · exact R96783
  · exact R96785
  · exact R96787
  · exact R96789
  · exact R96791
  · exact R96793
  · exact R96795
  · exact R96797
  · exact R96799
  · exact R96801
  · exact R96803
  · exact R96805
  · exact R96807
  · exact R96809
  · exact R96811
  · exact R96813
  · exact R96815
  · exact R96817
  · exact R96819
  · exact R96821
  · exact R96823
  · exact R96825
  · exact R96827
  · exact R96829
  · exact R96831
  · exact R96833
  · exact R96835
  · exact R96837
  · exact R96839
  · exact R96841
  · exact R96843
  · exact R96845
  · exact R96847
  · exact R96849
  · exact R96851
  · exact R96853
  · exact R96855
  · exact R96857
  · exact R96859
  · exact R96861
  · exact R96863
  · exact R96865
  · exact R96867
  · exact R96869
  · exact R96871
  · exact R96873
  · exact R96875
  · exact R96877
  · exact R96879
  · exact R96881
  · exact R96883
  · exact R96885
  · exact R96887
  · exact R96889
  · exact R96891
  · exact R96893
  · exact R96895
  · exact R96897
  · exact R96899
  · exact R96901
  · exact R96903
  · exact R96905
  · exact R96907
  · exact R96909
  · exact R96911
  · exact R96913
  · exact R96915
  · exact R96917
  · exact R96919
  · exact R96921
  · exact R96923
  · exact R96925
  · exact R96927
  · exact R96929
  · exact R96931
  · exact R96933
  · exact R96935
  · exact R96937
  · exact R96939
  · exact R96941
  · exact R96943
  · exact R96945
  · exact R96947
  · exact R96949
  · exact R96951
  · exact R96953
  · exact R96955
  · exact R96957
  · exact R96959
  · exact R96961
  · exact R96963
  · exact R96965
  · exact R96967
  · exact R96969
  · exact R96971
  · exact R96973
  · exact R96975
  · exact R96977
  · exact R96979
  · exact R96981
  · exact R96983
  · exact R96985
  · exact R96987
  · exact R96989
  · exact R96991
  · exact R96993
  · exact R96995
  · exact R96997
  · exact R96999
  · exact R97001
  · exact R97003
  · exact R97005
  · exact R97007
  · exact R97009
  · exact R97011
  · exact R97013
  · exact R97015
  · exact R97017
  · exact R97019
  · exact R97021
  · exact R97023
  · exact R97025
  · exact R97027
  · exact R97029
  · exact R97031
  · exact R97033
  · exact R97035
  · exact R97037
  · exact R97039
  · exact R97041
  · exact R97043
  · exact R97045
  · exact R97047
  · exact R97049
  · exact R97051
  · exact R97053
  · exact R97055
  · exact R97057
  · exact R97059
  · exact R97061
  · exact R97063
  · exact R97065
  · exact R97067
  · exact R97069
  · exact R97071
  · exact R97073
  · exact R97075
  · exact R97077
  · exact R97079
  · exact R97081
  · exact R97083
  · exact R97085
  · exact R97087
  · exact R97089
  · exact R97091
  · exact R97093
  · exact R97095
  · exact R97097
  · exact R97099
  · exact R97101
  · exact R97103
  · exact R97105
  · exact R97107
  · exact R97109
  · exact R97111
  · exact R97113
  · exact R97115
  · exact R97117
  · exact R97119
  · exact R97121
  · exact R97123
  · exact R97125
  · exact R97127
  · exact R97129
  · exact R97131
  · exact R97133
  · exact R97135
  · exact R97137
  · exact R97139
  · exact R97141
  · exact R97143
  · exact R97145
  · exact R97147
  · exact R97149
  · exact R97151
  · exact R97153
  · exact R97155
  · exact R97157
  · exact R97159
  · exact R97161
  · exact R97163
  · exact R97165
  · exact R97167
  · exact R97169
  · exact R97171
  · exact R97173
  · exact R97175
  · exact R97177
  · exact R97179
  · exact R97181
  · exact R97183
  · exact R97185
  · exact R97187
  · exact R97189
  · exact R97191
  · exact R97193
  · exact R97195
  · exact R97197
  · exact R97199
  · exact R97201
  · exact R97203
  · exact R97205
  · exact R97207
  · exact R97209
  · exact R97211
  · exact R97213
  · exact R97215
  · exact R97217
  · exact R97219
  · exact R97221
  · exact R97223
  · exact R97225
  · exact R97227
  · exact R97229
  · exact R97231
  · exact R97233
  · exact R97235
  · exact R97237
  · exact R97239
  · exact R97241
  · exact R97243
  · exact R97245
  · exact R97247
  · exact R97249
  · exact R97251
  · exact R97253
  · exact R97255
  · exact R97257
  · exact R97259
  · exact R97261
  · exact R97263
  · exact R97265
  · exact R97267
  · exact R97269
  · exact R97271
  · exact R97273
  · exact R97275
  · exact R97277
  · exact R97279
  · exact R97281
  · exact R97283
  · exact R97285
  · exact R97287
  · exact R97289
  · exact R97291
  · exact R97293
  · exact R97295
  · exact R97297
  · exact R97299
  · exact R97301
  · exact R97303
  · exact R97305
  · exact R97307
  · exact R97309
  · exact R97311
  · exact R97313
  · exact R97315
  · exact R97317
  · exact R97319
  · exact R97321
  · exact R97323
  · exact R97325
  · exact R97327
  · exact R97329
  · exact R97331
  · exact R97333
  · exact R97335
  · exact R97337
  · exact R97339
  · exact R97341
  · exact R97343
  · exact R97345
  · exact R97347
  · exact R97349
  · exact R97351
  · exact R97353
  · exact R97355
  · exact R97357
  · exact R97359
  · exact R97361
  · exact R97363
  · exact R97365
  · exact R97367
  · exact R97369
  · exact R97371
  · exact R97373
  · exact R97375
  · exact R97377
  · exact R97379
  · exact R97381
  · exact R97383
  · exact R97385
  · exact R97387
  · exact R97389
  · exact R97391
  · exact R97393
  · exact R97395
  · exact R97397
  · exact R97399
  · exact R97401
  · exact R97403
  · exact R97405
  · exact R97407
  · exact R97409
  · exact R97411
  · exact R97413
  · exact R97415
  · exact R97417
  · exact R97419
  · exact R97421
  · exact R97423
  · exact R97425
  · exact R97427
  · exact R97429
  · exact R97431
  · exact R97433
  · exact R97435
  · exact R97437
  · exact R97439
  · exact R97441
  · exact R97443
  · exact R97445
  · exact R97447
  · exact R97449
  · exact R97451
  · exact R97453
  · exact R97455
  · exact R97457
  · exact R97459
  · exact R97461
  · exact R97463
  · exact R97465
  · exact R97467
  · exact R97469
  · exact R97471
  · exact R97473
  · exact R97475
  · exact R97477
  · exact R97479
  · exact R97481
  · exact R97483
  · exact R97485
  · exact R97487
  · exact R97489
  · exact R97491
  · exact R97493
  · exact R97495
  · exact R97497
  · exact R97499
  · exact R97501
  · exact R97503
  · exact R97505
  · exact R97507
  · exact R97509
  · exact R97511
  · exact R97513
  · exact R97515
  · exact R97517
  · exact R97519
  · exact R97521
  · exact R97523
  · exact R97525
  · exact R97527
  · exact R97529
  · exact R97531
  · exact R97533
  · exact R97535
  · exact R97537
  · exact R97539
  · exact R97541
  · exact R97543
  · exact R97545
  · exact R97547
  · exact R97549
  · exact R97551
  · exact R97553
  · exact R97555
  · exact R97557
  · exact R97559
  · exact R97561
  · exact R97563
  · exact R97565
  · exact R97567
  · exact R97569
  · exact R97571
  · exact R97573
  · exact R97575
  · exact R97577
  · exact R97579
  · exact R97581
  · exact R97583
  · exact R97585
  · exact R97587
  · exact R97589
  · exact R97591
  · exact R97593
  · exact R97595
  · exact R97597
  · exact R97599
  · exact R97601
  · exact R97603
  · exact R97605
  · exact R97607
  · exact R97609
  · exact R97611
  · exact R97613
  · exact R97615
  · exact R97617
  · exact R97619
  · exact R97621
  · exact R97623
  · exact R97625
  · exact R97627
  · exact R97629
  · exact R97631
  · exact R97633
  · exact R97635
  · exact R97637
  · exact R97639
  · exact R97641
  · exact R97643
  · exact R97645
  · exact R97647
  · exact R97649
  · exact R97651
  · exact R97653
  · exact R97655
  · exact R97657
  · exact R97659
  · exact R97661
  · exact R97663
  · exact R97665
  · exact R97667
  · exact R97669
  · exact R97671
  · exact R97673
  · exact R97675
  · exact R97677
  · exact R97679
  · exact R97681
  · exact R97683
  · exact R97685
  · exact R97687
  · exact R97689
  · exact R97691
  · exact R97693
  · exact R97695
  · exact R97697
  · exact R97699
  · exact R97701
  · exact R97703
  · exact R97705
  · exact R97707
  · exact R97709
  · exact R97711
  · exact R97713
  · exact R97715
  · exact R97717
  · exact R97719
  · exact R97721
  · exact R97723
  · exact R97725
  · exact R97727
  · exact R97729
  · exact R97731
  · exact R97733
  · exact R97735
  · exact R97737
  · exact R97739
  · exact R97741
  · exact R97743
  · exact R97745
  · exact R97747
  · exact R97749
  · exact R97751
  · exact R97753
  · exact R97755
  · exact R97757
  · exact R97759
  · exact R97761
  · exact R97763
  · exact R97765
  · exact R97767
  · exact R97769
  · exact R97771
  · exact R97773
  · exact R97775
  · exact R97777
  · exact R97779
  · exact R97781
  · exact R97783
  · exact R97785
  · exact R97787
  · exact R97789
  · exact R97791
  · exact R97793
  · exact R97795
  · exact R97797
  · exact R97799
  · exact R97801
  · exact R97803
  · exact R97805
  · exact R97807
  · exact R97809
  · exact R97811
  · exact R97813
  · exact R97815
  · exact R97817
  · exact R97819
  · exact R97821
  · exact R97823
  · exact R97825
  · exact R97827
  · exact R97829
  · exact R97831
  · exact R97833
  · exact R97835
  · exact R97837
  · exact R97839
  · exact R97841
  · exact R97843
  · exact R97845
  · exact R97847
  · exact R97849
  · exact R97851
  · exact R97853
  · exact R97855
  · exact R97857
  · exact R97859
  · exact R97861
  · exact R97863
  · exact R97865
  · exact R97867
  · exact R97869
  · exact R97871
  · exact R97873
  · exact R97875
  · exact R97877
  · exact R97879
  · exact R97881
  · exact R97883
  · exact R97885
  · exact R97887
  · exact R97889
  · exact R97891
  · exact R97893
  · exact R97895
  · exact R97897
  · exact R97899
  · exact R97901
  · exact R97903
  · exact R97905
  · exact R97907
  · exact R97909
  · exact R97911
  · exact R97913
  · exact R97915
  · exact R97917
  · exact R97919
  · exact R97921
  · exact R97923
  · exact R97925
  · exact R97927
  · exact R97929

theorem C2 (j : ℕ) (h1 : 48965 ≤ j) (h2 : j ≤ 49565) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R97931
  · exact R97933
  · exact R97935
  · exact R97937
  · exact R97939
  · exact R97941
  · exact R97943
  · exact R97945
  · exact R97947
  · exact R97949
  · exact R97951
  · exact R97953
  · exact R97955
  · exact R97957
  · exact R97959
  · exact R97961
  · exact R97963
  · exact R97965
  · exact R97967
  · exact R97969
  · exact R97971
  · exact R97973
  · exact R97975
  · exact R97977
  · exact R97979
  · exact R97981
  · exact R97983
  · exact R97985
  · exact R97987
  · exact R97989
  · exact R97991
  · exact R97993
  · exact R97995
  · exact R97997
  · exact R97999
  · exact R98001
  · exact R98003
  · exact R98005
  · exact R98007
  · exact R98009
  · exact R98011
  · exact R98013
  · exact R98015
  · exact R98017
  · exact R98019
  · exact R98021
  · exact R98023
  · exact R98025
  · exact R98027
  · exact R98029
  · exact R98031
  · exact R98033
  · exact R98035
  · exact R98037
  · exact R98039
  · exact R98041
  · exact R98043
  · exact R98045
  · exact R98047
  · exact R98049
  · exact R98051
  · exact R98053
  · exact R98055
  · exact R98057
  · exact R98059
  · exact R98061
  · exact R98063
  · exact R98065
  · exact R98067
  · exact R98069
  · exact R98071
  · exact R98073
  · exact R98075
  · exact R98077
  · exact R98079
  · exact R98081
  · exact R98083
  · exact R98085
  · exact R98087
  · exact R98089
  · exact R98091
  · exact R98093
  · exact R98095
  · exact R98097
  · exact R98099
  · exact R98101
  · exact R98103
  · exact R98105
  · exact R98107
  · exact R98109
  · exact R98111
  · exact R98113
  · exact R98115
  · exact R98117
  · exact R98119
  · exact R98121
  · exact R98123
  · exact R98125
  · exact R98127
  · exact R98129
  · exact R98131
  · exact R98133
  · exact R98135
  · exact R98137
  · exact R98139
  · exact R98141
  · exact R98143
  · exact R98145
  · exact R98147
  · exact R98149
  · exact R98151
  · exact R98153
  · exact R98155
  · exact R98157
  · exact R98159
  · exact R98161
  · exact R98163
  · exact R98165
  · exact R98167
  · exact R98169
  · exact R98171
  · exact R98173
  · exact R98175
  · exact R98177
  · exact R98179
  · exact R98181
  · exact R98183
  · exact R98185
  · exact R98187
  · exact R98189
  · exact R98191
  · exact R98193
  · exact R98195
  · exact R98197
  · exact R98199
  · exact R98201
  · exact R98203
  · exact R98205
  · exact R98207
  · exact R98209
  · exact R98211
  · exact R98213
  · exact R98215
  · exact R98217
  · exact R98219
  · exact R98221
  · exact R98223
  · exact R98225
  · exact R98227
  · exact R98229
  · exact R98231
  · exact R98233
  · exact R98235
  · exact R98237
  · exact R98239
  · exact R98241
  · exact R98243
  · exact R98245
  · exact R98247
  · exact R98249
  · exact R98251
  · exact R98253
  · exact R98255
  · exact R98257
  · exact R98259
  · exact R98261
  · exact R98263
  · exact R98265
  · exact R98267
  · exact R98269
  · exact R98271
  · exact R98273
  · exact R98275
  · exact R98277
  · exact R98279
  · exact R98281
  · exact R98283
  · exact R98285
  · exact R98287
  · exact R98289
  · exact R98291
  · exact R98293
  · exact R98295
  · exact R98297
  · exact R98299
  · exact R98301
  · exact R98303
  · exact R98305
  · exact R98307
  · exact R98309
  · exact R98311
  · exact R98313
  · exact R98315
  · exact R98317
  · exact R98319
  · exact R98321
  · exact R98323
  · exact R98325
  · exact R98327
  · exact R98329
  · exact R98331
  · exact R98333
  · exact R98335
  · exact R98337
  · exact R98339
  · exact R98341
  · exact R98343
  · exact R98345
  · exact R98347
  · exact R98349
  · exact R98351
  · exact R98353
  · exact R98355
  · exact R98357
  · exact R98359
  · exact R98361
  · exact R98363
  · exact R98365
  · exact R98367
  · exact R98369
  · exact R98371
  · exact R98373
  · exact R98375
  · exact R98377
  · exact R98379
  · exact R98381
  · exact R98383
  · exact R98385
  · exact R98387
  · exact R98389
  · exact R98391
  · exact R98393
  · exact R98395
  · exact R98397
  · exact R98399
  · exact R98401
  · exact R98403
  · exact R98405
  · exact R98407
  · exact R98409
  · exact R98411
  · exact R98413
  · exact R98415
  · exact R98417
  · exact R98419
  · exact R98421
  · exact R98423
  · exact R98425
  · exact R98427
  · exact R98429
  · exact R98431
  · exact R98433
  · exact R98435
  · exact R98437
  · exact R98439
  · exact R98441
  · exact R98443
  · exact R98445
  · exact R98447
  · exact R98449
  · exact R98451
  · exact R98453
  · exact R98455
  · exact R98457
  · exact R98459
  · exact R98461
  · exact R98463
  · exact R98465
  · exact R98467
  · exact R98469
  · exact R98471
  · exact R98473
  · exact R98475
  · exact R98477
  · exact R98479
  · exact R98481
  · exact R98483
  · exact R98485
  · exact R98487
  · exact R98489
  · exact R98491
  · exact R98493
  · exact R98495
  · exact R98497
  · exact R98499
  · exact R98501
  · exact R98503
  · exact R98505
  · exact R98507
  · exact R98509
  · exact R98511
  · exact R98513
  · exact R98515
  · exact R98517
  · exact R98519
  · exact R98521
  · exact R98523
  · exact R98525
  · exact R98527
  · exact R98529
  · exact R98531
  · exact R98533
  · exact R98535
  · exact R98537
  · exact R98539
  · exact R98541
  · exact R98543
  · exact R98545
  · exact R98547
  · exact R98549
  · exact R98551
  · exact R98553
  · exact R98555
  · exact R98557
  · exact R98559
  · exact R98561
  · exact R98563
  · exact R98565
  · exact R98567
  · exact R98569
  · exact R98571
  · exact R98573
  · exact R98575
  · exact R98577
  · exact R98579
  · exact R98581
  · exact R98583
  · exact R98585
  · exact R98587
  · exact R98589
  · exact R98591
  · exact R98593
  · exact R98595
  · exact R98597
  · exact R98599
  · exact R98601
  · exact R98603
  · exact R98605
  · exact R98607
  · exact R98609
  · exact R98611
  · exact R98613
  · exact R98615
  · exact R98617
  · exact R98619
  · exact R98621
  · exact R98623
  · exact R98625
  · exact R98627
  · exact R98629
  · exact R98631
  · exact R98633
  · exact R98635
  · exact R98637
  · exact R98639
  · exact R98641
  · exact R98643
  · exact R98645
  · exact R98647
  · exact R98649
  · exact R98651
  · exact R98653
  · exact R98655
  · exact R98657
  · exact R98659
  · exact R98661
  · exact R98663
  · exact R98665
  · exact R98667
  · exact R98669
  · exact R98671
  · exact R98673
  · exact R98675
  · exact R98677
  · exact R98679
  · exact R98681
  · exact R98683
  · exact R98685
  · exact R98687
  · exact R98689
  · exact R98691
  · exact R98693
  · exact R98695
  · exact R98697
  · exact R98699
  · exact R98701
  · exact R98703
  · exact R98705
  · exact R98707
  · exact R98709
  · exact R98711
  · exact R98713
  · exact R98715
  · exact R98717
  · exact R98719
  · exact R98721
  · exact R98723
  · exact R98725
  · exact R98727
  · exact R98729
  · exact R98731
  · exact R98733
  · exact R98735
  · exact R98737
  · exact R98739
  · exact R98741
  · exact R98743
  · exact R98745
  · exact R98747
  · exact R98749
  · exact R98751
  · exact R98753
  · exact R98755
  · exact R98757
  · exact R98759
  · exact R98761
  · exact R98763
  · exact R98765
  · exact R98767
  · exact R98769
  · exact R98771
  · exact R98773
  · exact R98775
  · exact R98777
  · exact R98779
  · exact R98781
  · exact R98783
  · exact R98785
  · exact R98787
  · exact R98789
  · exact R98791
  · exact R98793
  · exact R98795
  · exact R98797
  · exact R98799
  · exact R98801
  · exact R98803
  · exact R98805
  · exact R98807
  · exact R98809
  · exact R98811
  · exact R98813
  · exact R98815
  · exact R98817
  · exact R98819
  · exact R98821
  · exact R98823
  · exact R98825
  · exact R98827
  · exact R98829
  · exact R98831
  · exact R98833
  · exact R98835
  · exact R98837
  · exact R98839
  · exact R98841
  · exact R98843
  · exact R98845
  · exact R98847
  · exact R98849
  · exact R98851
  · exact R98853
  · exact R98855
  · exact R98857
  · exact R98859
  · exact R98861
  · exact R98863
  · exact R98865
  · exact R98867
  · exact R98869
  · exact R98871
  · exact R98873
  · exact R98875
  · exact R98877
  · exact R98879
  · exact R98881
  · exact R98883
  · exact R98885
  · exact R98887
  · exact R98889
  · exact R98891
  · exact R98893
  · exact R98895
  · exact R98897
  · exact R98899
  · exact R98901
  · exact R98903
  · exact R98905
  · exact R98907
  · exact R98909
  · exact R98911
  · exact R98913
  · exact R98915
  · exact R98917
  · exact R98919
  · exact R98921
  · exact R98923
  · exact R98925
  · exact R98927
  · exact R98929
  · exact R98931
  · exact R98933
  · exact R98935
  · exact R98937
  · exact R98939
  · exact R98941
  · exact R98943
  · exact R98945
  · exact R98947
  · exact R98949
  · exact R98951
  · exact R98953
  · exact R98955
  · exact R98957
  · exact R98959
  · exact R98961
  · exact R98963
  · exact R98965
  · exact R98967
  · exact R98969
  · exact R98971
  · exact R98973
  · exact R98975
  · exact R98977
  · exact R98979
  · exact R98981
  · exact R98983
  · exact R98985
  · exact R98987
  · exact R98989
  · exact R98991
  · exact R98993
  · exact R98995
  · exact R98997
  · exact R98999
  · exact R99001
  · exact R99003
  · exact R99005
  · exact R99007
  · exact R99009
  · exact R99011
  · exact R99013
  · exact R99015
  · exact R99017
  · exact R99019
  · exact R99021
  · exact R99023
  · exact R99025
  · exact R99027
  · exact R99029
  · exact R99031
  · exact R99033
  · exact R99035
  · exact R99037
  · exact R99039
  · exact R99041
  · exact R99043
  · exact R99045
  · exact R99047
  · exact R99049
  · exact R99051
  · exact R99053
  · exact R99055
  · exact R99057
  · exact R99059
  · exact R99061
  · exact R99063
  · exact R99065
  · exact R99067
  · exact R99069
  · exact R99071
  · exact R99073
  · exact R99075
  · exact R99077
  · exact R99079
  · exact R99081
  · exact R99083
  · exact R99085
  · exact R99087
  · exact R99089
  · exact R99091
  · exact R99093
  · exact R99095
  · exact R99097
  · exact R99099
  · exact R99101
  · exact R99103
  · exact R99105
  · exact R99107
  · exact R99109
  · exact R99111
  · exact R99113
  · exact R99115
  · exact R99117
  · exact R99119
  · exact R99121
  · exact R99123
  · exact R99125
  · exact R99127
  · exact R99129
  · exact R99131

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 99131) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 95131 with hlo | hlo
  · exact syracuse_reaches_one_below_95131 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 48265 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 48965 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
