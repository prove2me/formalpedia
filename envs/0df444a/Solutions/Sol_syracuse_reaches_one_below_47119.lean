-- Prove2me | solution 1 for syracuse_reaches_one_below_47119
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T05:46:09.227579+00:00
-- url     : https://prove2.me/submissions/d74faca1-76a6-4dc8-ae9e-1d9912c7b6b3

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_43118

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 43117) : Reach n :=
  syracuse_reaches_one_below_43118 n h1 h2 h3
theorem R65549 : Reach 65549 := rs (se 3 (by rfl) ⟨12290, by rfl⟩) (B 24581 (by norm_num) ⟨12290, by rfl⟩ (by norm_num))
theorem R98333 : Reach 98333 := rs (se 3 (by rfl) ⟨18437, by rfl⟩) (B 36875 (by norm_num) ⟨18437, by rfl⟩ (by norm_num))
theorem R65573 : Reach 65573 := rs (se 4 (by rfl) ⟨6147, by rfl⟩) (B 12295 (by norm_num) ⟨6147, by rfl⟩ (by norm_num))
theorem R65597 : Reach 65597 := rs (se 3 (by rfl) ⟨12299, by rfl⟩) (B 24599 (by norm_num) ⟨12299, by rfl⟩ (by norm_num))
theorem R65605 : Reach 65605 := rs (se 4 (by rfl) ⟨6150, by rfl⟩) (B 12301 (by norm_num) ⟨6150, by rfl⟩ (by norm_num))
theorem R98381 : Reach 98381 := rs (se 3 (by rfl) ⟨18446, by rfl⟩) (B 36893 (by norm_num) ⟨18446, by rfl⟩ (by norm_num))
theorem R65621 : Reach 65621 := rs (se 8 (by rfl) ⟨384, by rfl⟩) (B 769 (by norm_num) ⟨384, by rfl⟩ (by norm_num))
theorem R98405 : Reach 98405 := rs (se 4 (by rfl) ⟨9225, by rfl⟩) (B 18451 (by norm_num) ⟨9225, by rfl⟩ (by norm_num))
theorem R65645 : Reach 65645 := rs (se 3 (by rfl) ⟨12308, by rfl⟩) (B 24617 (by norm_num) ⟨12308, by rfl⟩ (by norm_num))
theorem R65669 : Reach 65669 := rs (se 4 (by rfl) ⟨6156, by rfl⟩) (B 12313 (by norm_num) ⟨6156, by rfl⟩ (by norm_num))
theorem R65693 : Reach 65693 := rs (se 3 (by rfl) ⟨12317, by rfl⟩) (B 24635 (by norm_num) ⟨12317, by rfl⟩ (by norm_num))
theorem R65701 : Reach 65701 := rs (se 4 (by rfl) ⟨6159, by rfl⟩) (B 12319 (by norm_num) ⟨6159, by rfl⟩ (by norm_num))
theorem R98477 : Reach 98477 := rs (se 3 (by rfl) ⟨18464, by rfl⟩) (B 36929 (by norm_num) ⟨18464, by rfl⟩ (by norm_num))
theorem R65717 : Reach 65717 := rs (se 5 (by rfl) ⟨3080, by rfl⟩) (B 6161 (by norm_num) ⟨3080, by rfl⟩ (by norm_num))
theorem R65741 : Reach 65741 := rs (se 3 (by rfl) ⟨12326, by rfl⟩) (B 24653 (by norm_num) ⟨12326, by rfl⟩ (by norm_num))
theorem R65765 : Reach 65765 := rs (se 4 (by rfl) ⟨6165, by rfl⟩) (B 12331 (by norm_num) ⟨6165, by rfl⟩ (by norm_num))
theorem R98549 : Reach 98549 := rs (se 5 (by rfl) ⟨4619, by rfl⟩) (B 9239 (by norm_num) ⟨4619, by rfl⟩ (by norm_num))
theorem R65789 : Reach 65789 := rs (se 3 (by rfl) ⟨12335, by rfl⟩) (B 24671 (by norm_num) ⟨12335, by rfl⟩ (by norm_num))
theorem R65813 : Reach 65813 := rs (se 6 (by rfl) ⟨1542, by rfl⟩) (B 3085 (by norm_num) ⟨1542, by rfl⟩ (by norm_num))
theorem R65837 : Reach 65837 := rs (se 3 (by rfl) ⟨12344, by rfl⟩) (B 24689 (by norm_num) ⟨12344, by rfl⟩ (by norm_num))
theorem R98621 : Reach 98621 := rs (se 3 (by rfl) ⟨18491, by rfl⟩) (B 36983 (by norm_num) ⟨18491, by rfl⟩ (by norm_num))
theorem R65861 : Reach 65861 := rs (se 4 (by rfl) ⟨6174, by rfl⟩) (B 12349 (by norm_num) ⟨6174, by rfl⟩ (by norm_num))
theorem R65885 : Reach 65885 := rs (se 3 (by rfl) ⟨12353, by rfl⟩) (B 24707 (by norm_num) ⟨12353, by rfl⟩ (by norm_num))
theorem R65909 : Reach 65909 := rs (se 5 (by rfl) ⟨3089, by rfl⟩) (B 6179 (by norm_num) ⟨3089, by rfl⟩ (by norm_num))
theorem R98693 : Reach 98693 := rs (se 4 (by rfl) ⟨9252, by rfl⟩) (B 18505 (by norm_num) ⟨9252, by rfl⟩ (by norm_num))
theorem R65933 : Reach 65933 := rs (se 3 (by rfl) ⟨12362, by rfl⟩) (B 24725 (by norm_num) ⟨12362, by rfl⟩ (by norm_num))
theorem R65957 : Reach 65957 := rs (se 4 (by rfl) ⟨6183, by rfl⟩) (B 12367 (by norm_num) ⟨6183, by rfl⟩ (by norm_num))
theorem R65981 : Reach 65981 := rs (se 3 (by rfl) ⟨12371, by rfl⟩) (B 24743 (by norm_num) ⟨12371, by rfl⟩ (by norm_num))
theorem R98749 : Reach 98749 := rs (se 3 (by rfl) ⟨18515, by rfl⟩) (B 37031 (by norm_num) ⟨18515, by rfl⟩ (by norm_num))
theorem R98765 : Reach 98765 := rs (se 3 (by rfl) ⟨18518, by rfl⟩) (B 37037 (by norm_num) ⟨18518, by rfl⟩ (by norm_num))
theorem R66005 : Reach 66005 := rs (se 7 (by rfl) ⟨773, by rfl⟩) (B 1547 (by norm_num) ⟨773, by rfl⟩ (by norm_num))
theorem R66029 : Reach 66029 := rs (se 3 (by rfl) ⟨12380, by rfl⟩) (B 24761 (by norm_num) ⟨12380, by rfl⟩ (by norm_num))
theorem R229877 : Reach 229877 := rs (se 5 (by rfl) ⟨10775, by rfl⟩) (B 21551 (by norm_num) ⟨10775, by rfl⟩ (by norm_num))
theorem R66053 : Reach 66053 := rs (se 4 (by rfl) ⟨6192, by rfl⟩) (B 12385 (by norm_num) ⟨6192, by rfl⟩ (by norm_num))
theorem R98837 : Reach 98837 := rs (se 6 (by rfl) ⟨2316, by rfl⟩) (B 4633 (by norm_num) ⟨2316, by rfl⟩ (by norm_num))
theorem R66077 : Reach 66077 := rs (se 3 (by rfl) ⟨12389, by rfl⟩) (B 24779 (by norm_num) ⟨12389, by rfl⟩ (by norm_num))
theorem R164389 : Reach 164389 := rs (se 4 (by rfl) ⟨15411, by rfl⟩) (B 30823 (by norm_num) ⟨15411, by rfl⟩ (by norm_num))
theorem R66101 : Reach 66101 := rs (se 5 (by rfl) ⟨3098, by rfl⟩) (B 6197 (by norm_num) ⟨3098, by rfl⟩ (by norm_num))
theorem R164405 : Reach 164405 := rs (se 5 (by rfl) ⟨7706, by rfl⟩) (B 15413 (by norm_num) ⟨7706, by rfl⟩ (by norm_num))
theorem R66125 : Reach 66125 := rs (se 3 (by rfl) ⟨12398, by rfl⟩) (B 24797 (by norm_num) ⟨12398, by rfl⟩ (by norm_num))
theorem R98909 : Reach 98909 := rs (se 3 (by rfl) ⟨18545, by rfl⟩) (B 37091 (by norm_num) ⟨18545, by rfl⟩ (by norm_num))
theorem R66149 : Reach 66149 := rs (se 4 (by rfl) ⟨6201, by rfl⟩) (B 12403 (by norm_num) ⟨6201, by rfl⟩ (by norm_num))
theorem R66173 : Reach 66173 := rs (se 3 (by rfl) ⟨12407, by rfl⟩) (B 24815 (by norm_num) ⟨12407, by rfl⟩ (by norm_num))
theorem R66197 : Reach 66197 := rs (se 6 (by rfl) ⟨1551, by rfl⟩) (B 3103 (by norm_num) ⟨1551, by rfl⟩ (by norm_num))
theorem R98981 : Reach 98981 := rs (se 4 (by rfl) ⟨9279, by rfl⟩) (B 18559 (by norm_num) ⟨9279, by rfl⟩ (by norm_num))
theorem R66221 : Reach 66221 := rs (se 3 (by rfl) ⟨12416, by rfl⟩) (B 24833 (by norm_num) ⟨12416, by rfl⟩ (by norm_num))
theorem R66245 : Reach 66245 := rs (se 4 (by rfl) ⟨6210, by rfl⟩) (B 12421 (by norm_num) ⟨6210, by rfl⟩ (by norm_num))
theorem R66269 : Reach 66269 := rs (se 3 (by rfl) ⟨12425, by rfl⟩) (B 24851 (by norm_num) ⟨12425, by rfl⟩ (by norm_num))
theorem R131813 : Reach 131813 := rs (se 4 (by rfl) ⟨12357, by rfl⟩) (B 24715 (by norm_num) ⟨12357, by rfl⟩ (by norm_num))
theorem R99053 : Reach 99053 := rs (se 3 (by rfl) ⟨18572, by rfl⟩) (B 37145 (by norm_num) ⟨18572, by rfl⟩ (by norm_num))
theorem R66293 : Reach 66293 := rs (se 5 (by rfl) ⟨3107, by rfl⟩) (B 6215 (by norm_num) ⟨3107, by rfl⟩ (by norm_num))
theorem R66317 : Reach 66317 := rs (se 3 (by rfl) ⟨12434, by rfl⟩) (B 24869 (by norm_num) ⟨12434, by rfl⟩ (by norm_num))
theorem R66341 : Reach 66341 := rs (se 4 (by rfl) ⟨6219, by rfl⟩) (B 12439 (by norm_num) ⟨6219, by rfl⟩ (by norm_num))
theorem R99125 : Reach 99125 := rs (se 5 (by rfl) ⟨4646, by rfl⟩) (B 9293 (by norm_num) ⟨4646, by rfl⟩ (by norm_num))
theorem R66365 : Reach 66365 := rs (se 3 (by rfl) ⟨12443, by rfl⟩) (B 24887 (by norm_num) ⟨12443, by rfl⟩ (by norm_num))
theorem R164693 : Reach 164693 := rs (se 9 (by rfl) ⟨482, by rfl⟩) (B 965 (by norm_num) ⟨482, by rfl⟩ (by norm_num))
theorem R66389 : Reach 66389 := rs (se 9 (by rfl) ⟨194, by rfl⟩) (B 389 (by norm_num) ⟨194, by rfl⟩ (by norm_num))
theorem R66413 : Reach 66413 := rs (se 3 (by rfl) ⟨12452, by rfl⟩) (B 24905 (by norm_num) ⟨12452, by rfl⟩ (by norm_num))
theorem R99197 : Reach 99197 := rs (se 3 (by rfl) ⟨18599, by rfl⟩) (B 37199 (by norm_num) ⟨18599, by rfl⟩ (by norm_num))
theorem R66437 : Reach 66437 := rs (se 4 (by rfl) ⟨6228, by rfl⟩) (B 12457 (by norm_num) ⟨6228, by rfl⟩ (by norm_num))
theorem R66461 : Reach 66461 := rs (se 3 (by rfl) ⟨12461, by rfl⟩) (B 24923 (by norm_num) ⟨12461, by rfl⟩ (by norm_num))
theorem R66485 : Reach 66485 := rs (se 5 (by rfl) ⟨3116, by rfl⟩) (B 6233 (by norm_num) ⟨3116, by rfl⟩ (by norm_num))
theorem R99269 : Reach 99269 := rs (se 4 (by rfl) ⟨9306, by rfl⟩) (B 18613 (by norm_num) ⟨9306, by rfl⟩ (by norm_num))
theorem R66509 : Reach 66509 := rs (se 3 (by rfl) ⟨12470, by rfl⟩) (B 24941 (by norm_num) ⟨12470, by rfl⟩ (by norm_num))
theorem R66533 : Reach 66533 := rs (se 4 (by rfl) ⟨6237, by rfl⟩) (B 12475 (by norm_num) ⟨6237, by rfl⟩ (by norm_num))
theorem R66557 : Reach 66557 := rs (se 3 (by rfl) ⟨12479, by rfl⟩) (B 24959 (by norm_num) ⟨12479, by rfl⟩ (by norm_num))
theorem R99341 : Reach 99341 := rs (se 3 (by rfl) ⟨18626, by rfl⟩) (B 37253 (by norm_num) ⟨18626, by rfl⟩ (by norm_num))
theorem R66581 : Reach 66581 := rs (se 6 (by rfl) ⟨1560, by rfl⟩) (B 3121 (by norm_num) ⟨1560, by rfl⟩ (by norm_num))
theorem R66605 : Reach 66605 := rs (se 3 (by rfl) ⟨12488, by rfl⟩) (B 24977 (by norm_num) ⟨12488, by rfl⟩ (by norm_num))
theorem R66629 : Reach 66629 := rs (se 4 (by rfl) ⟨6246, by rfl⟩) (B 12493 (by norm_num) ⟨6246, by rfl⟩ (by norm_num))
theorem R99413 : Reach 99413 := rs (se 8 (by rfl) ⟨582, by rfl⟩) (B 1165 (by norm_num) ⟨582, by rfl⟩ (by norm_num))
theorem R66653 : Reach 66653 := rs (se 3 (by rfl) ⟨12497, by rfl⟩) (B 24995 (by norm_num) ⟨12497, by rfl⟩ (by norm_num))
theorem R66677 : Reach 66677 := rs (se 5 (by rfl) ⟨3125, by rfl⟩) (B 6251 (by norm_num) ⟨3125, by rfl⟩ (by norm_num))
theorem R66701 : Reach 66701 := rs (se 3 (by rfl) ⟨12506, by rfl⟩) (B 25013 (by norm_num) ⟨12506, by rfl⟩ (by norm_num))
theorem R99485 : Reach 99485 := rs (se 3 (by rfl) ⟨18653, by rfl⟩) (B 37307 (by norm_num) ⟨18653, by rfl⟩ (by norm_num))
theorem R66725 : Reach 66725 := rs (se 4 (by rfl) ⟨6255, by rfl⟩) (B 12511 (by norm_num) ⟨6255, by rfl⟩ (by norm_num))
theorem R66749 : Reach 66749 := rs (se 3 (by rfl) ⟨12515, by rfl⟩) (B 25031 (by norm_num) ⟨12515, by rfl⟩ (by norm_num))
theorem R66773 : Reach 66773 := rs (se 7 (by rfl) ⟨782, by rfl⟩) (B 1565 (by norm_num) ⟨782, by rfl⟩ (by norm_num))
theorem R99557 : Reach 99557 := rs (se 4 (by rfl) ⟨9333, by rfl⟩) (B 18667 (by norm_num) ⟨9333, by rfl⟩ (by norm_num))
theorem R66797 : Reach 66797 := rs (se 3 (by rfl) ⟨12524, by rfl⟩) (B 25049 (by norm_num) ⟨12524, by rfl⟩ (by norm_num))
theorem R66821 : Reach 66821 := rs (se 4 (by rfl) ⟨6264, by rfl⟩) (B 12529 (by norm_num) ⟨6264, by rfl⟩ (by norm_num))
theorem R197909 : Reach 197909 := rs (se 6 (by rfl) ⟨4638, by rfl⟩) (B 9277 (by norm_num) ⟨4638, by rfl⟩ (by norm_num))
theorem R66845 : Reach 66845 := rs (se 3 (by rfl) ⟨12533, by rfl⟩) (B 25067 (by norm_num) ⟨12533, by rfl⟩ (by norm_num))
theorem R99629 : Reach 99629 := rs (se 3 (by rfl) ⟨18680, by rfl⟩) (B 37361 (by norm_num) ⟨18680, by rfl⟩ (by norm_num))
theorem R66869 : Reach 66869 := rs (se 5 (by rfl) ⟨3134, by rfl⟩) (B 6269 (by norm_num) ⟨3134, by rfl⟩ (by norm_num))
theorem R66893 : Reach 66893 := rs (se 3 (by rfl) ⟨12542, by rfl⟩) (B 25085 (by norm_num) ⟨12542, by rfl⟩ (by norm_num))
theorem R66917 : Reach 66917 := rs (se 4 (by rfl) ⟨6273, by rfl⟩) (B 12547 (by norm_num) ⟨6273, by rfl⟩ (by norm_num))
theorem R99701 : Reach 99701 := rs (se 5 (by rfl) ⟨4673, by rfl⟩) (B 9347 (by norm_num) ⟨4673, by rfl⟩ (by norm_num))
theorem R66941 : Reach 66941 := rs (se 3 (by rfl) ⟨12551, by rfl⟩) (B 25103 (by norm_num) ⟨12551, by rfl⟩ (by norm_num))
theorem R99733 : Reach 99733 := rs (se 6 (by rfl) ⟨2337, by rfl⟩) (B 4675 (by norm_num) ⟨2337, by rfl⟩ (by norm_num))
theorem R66965 : Reach 66965 := rs (se 6 (by rfl) ⟨1569, by rfl⟩) (B 3139 (by norm_num) ⟨1569, by rfl⟩ (by norm_num))
theorem R66989 : Reach 66989 := rs (se 3 (by rfl) ⟨12560, by rfl⟩) (B 25121 (by norm_num) ⟨12560, by rfl⟩ (by norm_num))
theorem R99773 : Reach 99773 := rs (se 3 (by rfl) ⟨18707, by rfl⟩) (B 37415 (by norm_num) ⟨18707, by rfl⟩ (by norm_num))
theorem R67013 : Reach 67013 := rs (se 4 (by rfl) ⟨6282, by rfl⟩) (B 12565 (by norm_num) ⟨6282, by rfl⟩ (by norm_num))
theorem R99805 : Reach 99805 := rs (se 3 (by rfl) ⟨18713, by rfl⟩) (B 37427 (by norm_num) ⟨18713, by rfl⟩ (by norm_num))
theorem R67037 : Reach 67037 := rs (se 3 (by rfl) ⟨12569, by rfl⟩) (B 25139 (by norm_num) ⟨12569, by rfl⟩ (by norm_num))
theorem R67061 : Reach 67061 := rs (se 5 (by rfl) ⟨3143, by rfl⟩) (B 6287 (by norm_num) ⟨3143, by rfl⟩ (by norm_num))
theorem R99845 : Reach 99845 := rs (se 4 (by rfl) ⟨9360, by rfl⟩) (B 18721 (by norm_num) ⟨9360, by rfl⟩ (by norm_num))
theorem R67085 : Reach 67085 := rs (se 3 (by rfl) ⟨12578, by rfl⟩) (B 25157 (by norm_num) ⟨12578, by rfl⟩ (by norm_num))
theorem R67109 : Reach 67109 := rs (se 4 (by rfl) ⟨6291, by rfl⟩) (B 12583 (by norm_num) ⟨6291, by rfl⟩ (by norm_num))
theorem R198197 : Reach 198197 := rs (se 5 (by rfl) ⟨9290, by rfl⟩) (B 18581 (by norm_num) ⟨9290, by rfl⟩ (by norm_num))
theorem R67133 : Reach 67133 := rs (se 3 (by rfl) ⟨12587, by rfl⟩) (B 25175 (by norm_num) ⟨12587, by rfl⟩ (by norm_num))
theorem R99917 : Reach 99917 := rs (se 3 (by rfl) ⟨18734, by rfl⟩) (B 37469 (by norm_num) ⟨18734, by rfl⟩ (by norm_num))
theorem R67157 : Reach 67157 := rs (se 8 (by rfl) ⟨393, by rfl⟩) (B 787 (by norm_num) ⟨393, by rfl⟩ (by norm_num))
theorem R67181 : Reach 67181 := rs (se 3 (by rfl) ⟨12596, by rfl⟩) (B 25193 (by norm_num) ⟨12596, by rfl⟩ (by norm_num))
theorem R67205 : Reach 67205 := rs (se 4 (by rfl) ⟨6300, by rfl⟩) (B 12601 (by norm_num) ⟨6300, by rfl⟩ (by norm_num))
theorem R99989 : Reach 99989 := rs (se 6 (by rfl) ⟨2343, by rfl⟩) (B 4687 (by norm_num) ⟨2343, by rfl⟩ (by norm_num))
theorem R67229 : Reach 67229 := rs (se 3 (by rfl) ⟨12605, by rfl⟩) (B 25211 (by norm_num) ⟨12605, by rfl⟩ (by norm_num))
theorem R67253 : Reach 67253 := rs (se 5 (by rfl) ⟨3152, by rfl⟩) (B 6305 (by norm_num) ⟨3152, by rfl⟩ (by norm_num))
theorem R100037 : Reach 100037 := rs (se 4 (by rfl) ⟨9378, by rfl⟩) (B 18757 (by norm_num) ⟨9378, by rfl⟩ (by norm_num))
theorem R67277 : Reach 67277 := rs (se 3 (by rfl) ⟨12614, by rfl⟩) (B 25229 (by norm_num) ⟨12614, by rfl⟩ (by norm_num))
theorem R100061 : Reach 100061 := rs (se 3 (by rfl) ⟨18761, by rfl⟩) (B 37523 (by norm_num) ⟨18761, by rfl⟩ (by norm_num))
theorem R67301 : Reach 67301 := rs (se 4 (by rfl) ⟨6309, by rfl⟩) (B 12619 (by norm_num) ⟨6309, by rfl⟩ (by norm_num))
theorem R67325 : Reach 67325 := rs (se 3 (by rfl) ⟨12623, by rfl⟩) (B 25247 (by norm_num) ⟨12623, by rfl⟩ (by norm_num))
theorem R67349 : Reach 67349 := rs (se 6 (by rfl) ⟨1578, by rfl⟩) (B 3157 (by norm_num) ⟨1578, by rfl⟩ (by norm_num))
theorem R100133 : Reach 100133 := rs (se 4 (by rfl) ⟨9387, by rfl⟩) (B 18775 (by norm_num) ⟨9387, by rfl⟩ (by norm_num))
theorem R67373 : Reach 67373 := rs (se 3 (by rfl) ⟨12632, by rfl⟩) (B 25265 (by norm_num) ⟨12632, by rfl⟩ (by norm_num))
theorem R67397 : Reach 67397 := rs (se 4 (by rfl) ⟨6318, by rfl⟩) (B 12637 (by norm_num) ⟨6318, by rfl⟩ (by norm_num))
theorem R67421 : Reach 67421 := rs (se 3 (by rfl) ⟨12641, by rfl⟩) (B 25283 (by norm_num) ⟨12641, by rfl⟩ (by norm_num))
theorem R100205 : Reach 100205 := rs (se 3 (by rfl) ⟨18788, by rfl⟩) (B 37577 (by norm_num) ⟨18788, by rfl⟩ (by norm_num))
theorem R67445 : Reach 67445 := rs (se 5 (by rfl) ⟨3161, by rfl⟩) (B 6323 (by norm_num) ⟨3161, by rfl⟩ (by norm_num))
theorem R132997 : Reach 132997 := rs (se 4 (by rfl) ⟨12468, by rfl⟩) (B 24937 (by norm_num) ⟨12468, by rfl⟩ (by norm_num))
theorem R67469 : Reach 67469 := rs (se 3 (by rfl) ⟨12650, by rfl⟩) (B 25301 (by norm_num) ⟨12650, by rfl⟩ (by norm_num))
theorem R100253 : Reach 100253 := rs (se 3 (by rfl) ⟨18797, by rfl⟩) (B 37595 (by norm_num) ⟨18797, by rfl⟩ (by norm_num))
theorem R67493 : Reach 67493 := rs (se 4 (by rfl) ⟨6327, by rfl⟩) (B 12655 (by norm_num) ⟨6327, by rfl⟩ (by norm_num))
theorem R100277 : Reach 100277 := rs (se 5 (by rfl) ⟨4700, by rfl⟩) (B 9401 (by norm_num) ⟨4700, by rfl⟩ (by norm_num))
theorem R296885 : Reach 296885 := rs (se 5 (by rfl) ⟨13916, by rfl⟩) (B 27833 (by norm_num) ⟨13916, by rfl⟩ (by norm_num))
theorem R67517 : Reach 67517 := rs (se 3 (by rfl) ⟨12659, by rfl⟩) (B 25319 (by norm_num) ⟨12659, by rfl⟩ (by norm_num))
theorem R165845 : Reach 165845 := rs (se 7 (by rfl) ⟨1943, by rfl⟩) (B 3887 (by norm_num) ⟨1943, by rfl⟩ (by norm_num))
theorem R67541 : Reach 67541 := rs (se 7 (by rfl) ⟨791, by rfl⟩) (B 1583 (by norm_num) ⟨791, by rfl⟩ (by norm_num))
theorem R67565 : Reach 67565 := rs (se 3 (by rfl) ⟨12668, by rfl⟩) (B 25337 (by norm_num) ⟨12668, by rfl⟩ (by norm_num))
theorem R100349 : Reach 100349 := rs (se 3 (by rfl) ⟨18815, by rfl⟩) (B 37631 (by norm_num) ⟨18815, by rfl⟩ (by norm_num))
theorem R67589 : Reach 67589 := rs (se 4 (by rfl) ⟨6336, by rfl⟩) (B 12673 (by norm_num) ⟨6336, by rfl⟩ (by norm_num))
theorem R67613 : Reach 67613 := rs (se 3 (by rfl) ⟨12677, by rfl⟩) (B 25355 (by norm_num) ⟨12677, by rfl⟩ (by norm_num))
theorem R133157 : Reach 133157 := rs (se 4 (by rfl) ⟨12483, by rfl⟩) (B 24967 (by norm_num) ⟨12483, by rfl⟩ (by norm_num))
theorem R100397 : Reach 100397 := rs (se 3 (by rfl) ⟨18824, by rfl⟩) (B 37649 (by norm_num) ⟨18824, by rfl⟩ (by norm_num))
theorem R67637 : Reach 67637 := rs (se 5 (by rfl) ⟨3170, by rfl⟩) (B 6341 (by norm_num) ⟨3170, by rfl⟩ (by norm_num))
theorem R100421 : Reach 100421 := rs (se 4 (by rfl) ⟨9414, by rfl⟩) (B 18829 (by norm_num) ⟨9414, by rfl⟩ (by norm_num))
theorem R67661 : Reach 67661 := rs (se 3 (by rfl) ⟨12686, by rfl⟩) (B 25373 (by norm_num) ⟨12686, by rfl⟩ (by norm_num))
theorem R67685 : Reach 67685 := rs (se 4 (by rfl) ⟨6345, by rfl⟩) (B 12691 (by norm_num) ⟨6345, by rfl⟩ (by norm_num))
theorem R329845 : Reach 329845 := rs (se 5 (by rfl) ⟨15461, by rfl⟩) (B 30923 (by norm_num) ⟨15461, by rfl⟩ (by norm_num))
theorem R67709 : Reach 67709 := rs (se 3 (by rfl) ⟨12695, by rfl⟩) (B 25391 (by norm_num) ⟨12695, by rfl⟩ (by norm_num))
theorem R100493 : Reach 100493 := rs (se 3 (by rfl) ⟨18842, by rfl⟩) (B 37685 (by norm_num) ⟨18842, by rfl⟩ (by norm_num))
theorem R67733 : Reach 67733 := rs (se 6 (by rfl) ⟨1587, by rfl⟩) (B 3175 (by norm_num) ⟨1587, by rfl⟩ (by norm_num))
theorem R67757 : Reach 67757 := rs (se 3 (by rfl) ⟨12704, by rfl⟩) (B 25409 (by norm_num) ⟨12704, by rfl⟩ (by norm_num))
theorem R67781 : Reach 67781 := rs (se 4 (by rfl) ⟨6354, by rfl⟩) (B 12709 (by norm_num) ⟨6354, by rfl⟩ (by norm_num))
theorem R100565 : Reach 100565 := rs (se 7 (by rfl) ⟨1178, by rfl⟩) (B 2357 (by norm_num) ⟨1178, by rfl⟩ (by norm_num))
theorem R67805 : Reach 67805 := rs (se 3 (by rfl) ⟨12713, by rfl⟩) (B 25427 (by norm_num) ⟨12713, by rfl⟩ (by norm_num))
theorem R67829 : Reach 67829 := rs (se 5 (by rfl) ⟨3179, by rfl⟩) (B 6359 (by norm_num) ⟨3179, by rfl⟩ (by norm_num))
theorem R67853 : Reach 67853 := rs (se 3 (by rfl) ⟨12722, by rfl⟩) (B 25445 (by norm_num) ⟨12722, by rfl⟩ (by norm_num))
theorem R133397 : Reach 133397 := rs (se 6 (by rfl) ⟨3126, by rfl⟩) (B 6253 (by norm_num) ⟨3126, by rfl⟩ (by norm_num))
theorem R100637 : Reach 100637 := rs (se 3 (by rfl) ⟨18869, by rfl⟩) (B 37739 (by norm_num) ⟨18869, by rfl⟩ (by norm_num))
theorem R67877 : Reach 67877 := rs (se 4 (by rfl) ⟨6363, by rfl⟩) (B 12727 (by norm_num) ⟨6363, by rfl⟩ (by norm_num))
theorem R198949 : Reach 198949 := rs (se 4 (by rfl) ⟨18651, by rfl⟩) (B 37303 (by norm_num) ⟨18651, by rfl⟩ (by norm_num))
theorem R67901 : Reach 67901 := rs (se 3 (by rfl) ⟨12731, by rfl⟩) (B 25463 (by norm_num) ⟨12731, by rfl⟩ (by norm_num))
theorem R67925 : Reach 67925 := rs (se 10 (by rfl) ⟨99, by rfl⟩) (B 199 (by norm_num) ⟨99, by rfl⟩ (by norm_num))
theorem R100709 : Reach 100709 := rs (se 4 (by rfl) ⟨9441, by rfl⟩) (B 18883 (by norm_num) ⟨9441, by rfl⟩ (by norm_num))
theorem R67949 : Reach 67949 := rs (se 3 (by rfl) ⟨12740, by rfl⟩) (B 25481 (by norm_num) ⟨12740, by rfl⟩ (by norm_num))
theorem R67973 : Reach 67973 := rs (se 4 (by rfl) ⟨6372, by rfl⟩) (B 12745 (by norm_num) ⟨6372, by rfl⟩ (by norm_num))
theorem R67997 : Reach 67997 := rs (se 3 (by rfl) ⟨12749, by rfl⟩) (B 25499 (by norm_num) ⟨12749, by rfl⟩ (by norm_num))
theorem R100781 : Reach 100781 := rs (se 3 (by rfl) ⟨18896, by rfl⟩) (B 37793 (by norm_num) ⟨18896, by rfl⟩ (by norm_num))
theorem R68021 : Reach 68021 := rs (se 5 (by rfl) ⟨3188, by rfl⟩) (B 6377 (by norm_num) ⟨3188, by rfl⟩ (by norm_num))
theorem R68045 : Reach 68045 := rs (se 3 (by rfl) ⟨12758, by rfl⟩) (B 25517 (by norm_num) ⟨12758, by rfl⟩ (by norm_num))
theorem R133589 : Reach 133589 := rs (se 7 (by rfl) ⟨1565, by rfl⟩) (B 3131 (by norm_num) ⟨1565, by rfl⟩ (by norm_num))
theorem R68069 : Reach 68069 := rs (se 4 (by rfl) ⟨6381, by rfl⟩) (B 12763 (by norm_num) ⟨6381, by rfl⟩ (by norm_num))
theorem R100853 : Reach 100853 := rs (se 5 (by rfl) ⟨4727, by rfl⟩) (B 9455 (by norm_num) ⟨4727, by rfl⟩ (by norm_num))
theorem R68093 : Reach 68093 := rs (se 3 (by rfl) ⟨12767, by rfl⟩) (B 25535 (by norm_num) ⟨12767, by rfl⟩ (by norm_num))
theorem R68117 : Reach 68117 := rs (se 6 (by rfl) ⟨1596, by rfl⟩) (B 3193 (by norm_num) ⟨1596, by rfl⟩ (by norm_num))
theorem R68141 : Reach 68141 := rs (se 3 (by rfl) ⟨12776, by rfl⟩) (B 25553 (by norm_num) ⟨12776, by rfl⟩ (by norm_num))
theorem R100925 : Reach 100925 := rs (se 3 (by rfl) ⟨18923, by rfl⟩) (B 37847 (by norm_num) ⟨18923, by rfl⟩ (by norm_num))
theorem R68165 : Reach 68165 := rs (se 4 (by rfl) ⟨6390, by rfl⟩) (B 12781 (by norm_num) ⟨6390, by rfl⟩ (by norm_num))
theorem R68189 : Reach 68189 := rs (se 3 (by rfl) ⟨12785, by rfl⟩) (B 25571 (by norm_num) ⟨12785, by rfl⟩ (by norm_num))
theorem R68213 : Reach 68213 := rs (se 5 (by rfl) ⟨3197, by rfl⟩) (B 6395 (by norm_num) ⟨3197, by rfl⟩ (by norm_num))
theorem R100997 : Reach 100997 := rs (se 4 (by rfl) ⟨9468, by rfl⟩) (B 18937 (by norm_num) ⟨9468, by rfl⟩ (by norm_num))
theorem R68237 : Reach 68237 := rs (se 3 (by rfl) ⟨12794, by rfl⟩) (B 25589 (by norm_num) ⟨12794, by rfl⟩ (by norm_num))
theorem R68261 : Reach 68261 := rs (se 4 (by rfl) ⟨6399, by rfl⟩) (B 12799 (by norm_num) ⟨6399, by rfl⟩ (by norm_num))
theorem R68285 : Reach 68285 := rs (se 3 (by rfl) ⟨12803, by rfl⟩) (B 25607 (by norm_num) ⟨12803, by rfl⟩ (by norm_num))
theorem R101069 : Reach 101069 := rs (se 3 (by rfl) ⟨18950, by rfl⟩) (B 37901 (by norm_num) ⟨18950, by rfl⟩ (by norm_num))
theorem R68309 : Reach 68309 := rs (se 7 (by rfl) ⟨800, by rfl⟩) (B 1601 (by norm_num) ⟨800, by rfl⟩ (by norm_num))
theorem R68333 : Reach 68333 := rs (se 3 (by rfl) ⟨12812, by rfl⟩) (B 25625 (by norm_num) ⟨12812, by rfl⟩ (by norm_num))
theorem R68357 : Reach 68357 := rs (se 4 (by rfl) ⟨6408, by rfl⟩) (B 12817 (by norm_num) ⟨6408, by rfl⟩ (by norm_num))
theorem R101141 : Reach 101141 := rs (se 6 (by rfl) ⟨2370, by rfl⟩) (B 4741 (by norm_num) ⟨2370, by rfl⟩ (by norm_num))
theorem R68381 : Reach 68381 := rs (se 3 (by rfl) ⟨12821, by rfl⟩) (B 25643 (by norm_num) ⟨12821, by rfl⟩ (by norm_num))
theorem R68405 : Reach 68405 := rs (se 5 (by rfl) ⟨3206, by rfl⟩) (B 6413 (by norm_num) ⟨3206, by rfl⟩ (by norm_num))
theorem R68429 : Reach 68429 := rs (se 3 (by rfl) ⟨12830, by rfl⟩) (B 25661 (by norm_num) ⟨12830, by rfl⟩ (by norm_num))
theorem R101213 : Reach 101213 := rs (se 3 (by rfl) ⟨18977, by rfl⟩) (B 37955 (by norm_num) ⟨18977, by rfl⟩ (by norm_num))
theorem R68453 : Reach 68453 := rs (se 4 (by rfl) ⟨6417, by rfl⟩) (B 12835 (by norm_num) ⟨6417, by rfl⟩ (by norm_num))
theorem R68477 : Reach 68477 := rs (se 3 (by rfl) ⟨12839, by rfl⟩) (B 25679 (by norm_num) ⟨12839, by rfl⟩ (by norm_num))
theorem R68501 : Reach 68501 := rs (se 6 (by rfl) ⟨1605, by rfl⟩) (B 3211 (by norm_num) ⟨1605, by rfl⟩ (by norm_num))
theorem R166805 : Reach 166805 := rs (se 6 (by rfl) ⟨3909, by rfl⟩) (B 7819 (by norm_num) ⟨3909, by rfl⟩ (by norm_num))
theorem R101285 : Reach 101285 := rs (se 4 (by rfl) ⟨9495, by rfl⟩) (B 18991 (by norm_num) ⟨9495, by rfl⟩ (by norm_num))
theorem R68525 : Reach 68525 := rs (se 3 (by rfl) ⟨12848, by rfl⟩) (B 25697 (by norm_num) ⟨12848, by rfl⟩ (by norm_num))
theorem R68549 : Reach 68549 := rs (se 4 (by rfl) ⟨6426, by rfl⟩) (B 12853 (by norm_num) ⟨6426, by rfl⟩ (by norm_num))
theorem R68573 : Reach 68573 := rs (se 3 (by rfl) ⟨12857, by rfl⟩) (B 25715 (by norm_num) ⟨12857, by rfl⟩ (by norm_num))
theorem R101357 : Reach 101357 := rs (se 3 (by rfl) ⟨19004, by rfl⟩) (B 38009 (by norm_num) ⟨19004, by rfl⟩ (by norm_num))
theorem R68597 : Reach 68597 := rs (se 5 (by rfl) ⟨3215, by rfl⟩) (B 6431 (by norm_num) ⟨3215, by rfl⟩ (by norm_num))
theorem R199685 : Reach 199685 := rs (se 4 (by rfl) ⟨18720, by rfl⟩) (B 37441 (by norm_num) ⟨18720, by rfl⟩ (by norm_num))
theorem R68621 : Reach 68621 := rs (se 3 (by rfl) ⟨12866, by rfl⟩) (B 25733 (by norm_num) ⟨12866, by rfl⟩ (by norm_num))
theorem R232469 : Reach 232469 := rs (se 6 (by rfl) ⟨5448, by rfl⟩) (B 10897 (by norm_num) ⟨5448, by rfl⟩ (by norm_num))
theorem R68645 : Reach 68645 := rs (se 4 (by rfl) ⟨6435, by rfl⟩) (B 12871 (by norm_num) ⟨6435, by rfl⟩ (by norm_num))
theorem R101429 : Reach 101429 := rs (se 5 (by rfl) ⟨4754, by rfl⟩) (B 9509 (by norm_num) ⟨4754, by rfl⟩ (by norm_num))
theorem R68669 : Reach 68669 := rs (se 3 (by rfl) ⟨12875, by rfl⟩) (B 25751 (by norm_num) ⟨12875, by rfl⟩ (by norm_num))
theorem R68677 : Reach 68677 := rs (se 4 (by rfl) ⟨6438, by rfl⟩) (B 12877 (by norm_num) ⟨6438, by rfl⟩ (by norm_num))
theorem R68693 : Reach 68693 := rs (se 8 (by rfl) ⟨402, by rfl⟩) (B 805 (by norm_num) ⟨402, by rfl⟩ (by norm_num))
theorem R68717 : Reach 68717 := rs (se 3 (by rfl) ⟨12884, by rfl⟩) (B 25769 (by norm_num) ⟨12884, by rfl⟩ (by norm_num))
theorem R101501 : Reach 101501 := rs (se 3 (by rfl) ⟨19031, by rfl⟩) (B 38063 (by norm_num) ⟨19031, by rfl⟩ (by norm_num))
theorem R68741 : Reach 68741 := rs (se 4 (by rfl) ⟨6444, by rfl⟩) (B 12889 (by norm_num) ⟨6444, by rfl⟩ (by norm_num))
theorem R68765 : Reach 68765 := rs (se 3 (by rfl) ⟨12893, by rfl⟩) (B 25787 (by norm_num) ⟨12893, by rfl⟩ (by norm_num))
theorem R167093 : Reach 167093 := rs (se 5 (by rfl) ⟨7832, by rfl⟩) (B 15665 (by norm_num) ⟨7832, by rfl⟩ (by norm_num))
theorem R68789 : Reach 68789 := rs (se 5 (by rfl) ⟨3224, by rfl⟩) (B 6449 (by norm_num) ⟨3224, by rfl⟩ (by norm_num))
theorem R101573 : Reach 101573 := rs (se 4 (by rfl) ⟨9522, by rfl⟩) (B 19045 (by norm_num) ⟨9522, by rfl⟩ (by norm_num))
theorem R68813 : Reach 68813 := rs (se 3 (by rfl) ⟨12902, by rfl⟩) (B 25805 (by norm_num) ⟨12902, by rfl⟩ (by norm_num))
theorem R330965 : Reach 330965 := rs (se 7 (by rfl) ⟨3878, by rfl⟩) (B 7757 (by norm_num) ⟨3878, by rfl⟩ (by norm_num))
theorem R68837 : Reach 68837 := rs (se 4 (by rfl) ⟨6453, by rfl⟩) (B 12907 (by norm_num) ⟨6453, by rfl⟩ (by norm_num))
theorem R68861 : Reach 68861 := rs (se 3 (by rfl) ⟨12911, by rfl⟩) (B 25823 (by norm_num) ⟨12911, by rfl⟩ (by norm_num))
theorem R101645 : Reach 101645 := rs (se 3 (by rfl) ⟨19058, by rfl⟩) (B 38117 (by norm_num) ⟨19058, by rfl⟩ (by norm_num))
theorem R68885 : Reach 68885 := rs (se 6 (by rfl) ⟨1614, by rfl⟩) (B 3229 (by norm_num) ⟨1614, by rfl⟩ (by norm_num))
theorem R68909 : Reach 68909 := rs (se 3 (by rfl) ⟨12920, by rfl⟩) (B 25841 (by norm_num) ⟨12920, by rfl⟩ (by norm_num))
theorem R68933 : Reach 68933 := rs (se 4 (by rfl) ⟨6462, by rfl⟩) (B 12925 (by norm_num) ⟨6462, by rfl⟩ (by norm_num))
theorem R101717 : Reach 101717 := rs (se 11 (by rfl) ⟨74, by rfl⟩) (B 149 (by norm_num) ⟨74, by rfl⟩ (by norm_num))
theorem R68957 : Reach 68957 := rs (se 3 (by rfl) ⟨12929, by rfl⟩) (B 25859 (by norm_num) ⟨12929, by rfl⟩ (by norm_num))
theorem R68981 : Reach 68981 := rs (se 5 (by rfl) ⟨3233, by rfl⟩) (B 6467 (by norm_num) ⟨3233, by rfl⟩ (by norm_num))
theorem R69005 : Reach 69005 := rs (se 3 (by rfl) ⟨12938, by rfl⟩) (B 25877 (by norm_num) ⟨12938, by rfl⟩ (by norm_num))
theorem R101789 : Reach 101789 := rs (se 3 (by rfl) ⟨19085, by rfl⟩) (B 38171 (by norm_num) ⟨19085, by rfl⟩ (by norm_num))
theorem R69029 : Reach 69029 := rs (se 4 (by rfl) ⟨6471, by rfl⟩) (B 12943 (by norm_num) ⟨6471, by rfl⟩ (by norm_num))
theorem R69053 : Reach 69053 := rs (se 3 (by rfl) ⟨12947, by rfl⟩) (B 25895 (by norm_num) ⟨12947, by rfl⟩ (by norm_num))
theorem R69077 : Reach 69077 := rs (se 7 (by rfl) ⟨809, by rfl⟩) (B 1619 (by norm_num) ⟨809, by rfl⟩ (by norm_num))
theorem R101861 : Reach 101861 := rs (se 4 (by rfl) ⟨9549, by rfl⟩) (B 19099 (by norm_num) ⟨9549, by rfl⟩ (by norm_num))
theorem R69101 : Reach 69101 := rs (se 3 (by rfl) ⟨12956, by rfl⟩) (B 25913 (by norm_num) ⟨12956, by rfl⟩ (by norm_num))
theorem R69125 : Reach 69125 := rs (se 4 (by rfl) ⟨6480, by rfl⟩) (B 12961 (by norm_num) ⟨6480, by rfl⟩ (by norm_num))
theorem R69149 : Reach 69149 := rs (se 3 (by rfl) ⟨12965, by rfl⟩) (B 25931 (by norm_num) ⟨12965, by rfl⟩ (by norm_num))
theorem R101933 : Reach 101933 := rs (se 3 (by rfl) ⟨19112, by rfl⟩) (B 38225 (by norm_num) ⟨19112, by rfl⟩ (by norm_num))
theorem R69173 : Reach 69173 := rs (se 5 (by rfl) ⟨3242, by rfl⟩) (B 6485 (by norm_num) ⟨3242, by rfl⟩ (by norm_num))
theorem R69197 : Reach 69197 := rs (se 3 (by rfl) ⟨12974, by rfl⟩) (B 25949 (by norm_num) ⟨12974, by rfl⟩ (by norm_num))
theorem R69221 : Reach 69221 := rs (se 4 (by rfl) ⟨6489, by rfl⟩) (B 12979 (by norm_num) ⟨6489, by rfl⟩ (by norm_num))
theorem R102005 : Reach 102005 := rs (se 5 (by rfl) ⟨4781, by rfl⟩) (B 9563 (by norm_num) ⟨4781, by rfl⟩ (by norm_num))
theorem R69245 : Reach 69245 := rs (se 3 (by rfl) ⟨12983, by rfl⟩) (B 25967 (by norm_num) ⟨12983, by rfl⟩ (by norm_num))
theorem R69269 : Reach 69269 := rs (se 6 (by rfl) ⟨1623, by rfl⟩) (B 3247 (by norm_num) ⟨1623, by rfl⟩ (by norm_num))
theorem R69293 : Reach 69293 := rs (se 3 (by rfl) ⟨12992, by rfl⟩) (B 25985 (by norm_num) ⟨12992, by rfl⟩ (by norm_num))
theorem R102077 : Reach 102077 := rs (se 3 (by rfl) ⟨19139, by rfl⟩) (B 38279 (by norm_num) ⟨19139, by rfl⟩ (by norm_num))
theorem R69317 : Reach 69317 := rs (se 4 (by rfl) ⟨6498, by rfl⟩) (B 12997 (by norm_num) ⟨6498, by rfl⟩ (by norm_num))
theorem R69341 : Reach 69341 := rs (se 3 (by rfl) ⟨13001, by rfl⟩) (B 26003 (by norm_num) ⟨13001, by rfl⟩ (by norm_num))
theorem R69365 : Reach 69365 := rs (se 5 (by rfl) ⟨3251, by rfl⟩) (B 6503 (by norm_num) ⟨3251, by rfl⟩ (by norm_num))
theorem R102149 : Reach 102149 := rs (se 4 (by rfl) ⟨9576, by rfl⟩) (B 19153 (by norm_num) ⟨9576, by rfl⟩ (by norm_num))
theorem R69389 : Reach 69389 := rs (se 3 (by rfl) ⟨13010, by rfl⟩) (B 26021 (by norm_num) ⟨13010, by rfl⟩ (by norm_num))
theorem R69413 : Reach 69413 := rs (se 4 (by rfl) ⟨6507, by rfl⟩) (B 13015 (by norm_num) ⟨6507, by rfl⟩ (by norm_num))
theorem R69437 : Reach 69437 := rs (se 3 (by rfl) ⟨13019, by rfl⟩) (B 26039 (by norm_num) ⟨13019, by rfl⟩ (by norm_num))
theorem R102221 : Reach 102221 := rs (se 3 (by rfl) ⟨19166, by rfl⟩) (B 38333 (by norm_num) ⟨19166, by rfl⟩ (by norm_num))
theorem R69461 : Reach 69461 := rs (se 9 (by rfl) ⟨203, by rfl⟩) (B 407 (by norm_num) ⟨203, by rfl⟩ (by norm_num))
theorem R69485 : Reach 69485 := rs (se 3 (by rfl) ⟨13028, by rfl⟩) (B 26057 (by norm_num) ⟨13028, by rfl⟩ (by norm_num))
theorem R69509 : Reach 69509 := rs (se 4 (by rfl) ⟨6516, by rfl⟩) (B 13033 (by norm_num) ⟨6516, by rfl⟩ (by norm_num))
theorem R102293 : Reach 102293 := rs (se 6 (by rfl) ⟨2397, by rfl⟩) (B 4795 (by norm_num) ⟨2397, by rfl⟩ (by norm_num))
theorem R69533 : Reach 69533 := rs (se 3 (by rfl) ⟨13037, by rfl⟩) (B 26075 (by norm_num) ⟨13037, by rfl⟩ (by norm_num))
theorem R69557 : Reach 69557 := rs (se 5 (by rfl) ⟨3260, by rfl⟩) (B 6521 (by norm_num) ⟨3260, by rfl⟩ (by norm_num))
theorem R69581 : Reach 69581 := rs (se 3 (by rfl) ⟨13046, by rfl⟩) (B 26093 (by norm_num) ⟨13046, by rfl⟩ (by norm_num))
theorem R102365 : Reach 102365 := rs (se 3 (by rfl) ⟨19193, by rfl⟩) (B 38387 (by norm_num) ⟨19193, by rfl⟩ (by norm_num))
theorem R69605 : Reach 69605 := rs (se 4 (by rfl) ⟨6525, by rfl⟩) (B 13051 (by norm_num) ⟨6525, by rfl⟩ (by norm_num))
theorem R69629 : Reach 69629 := rs (se 3 (by rfl) ⟨13055, by rfl⟩) (B 26111 (by norm_num) ⟨13055, by rfl⟩ (by norm_num))
theorem R69653 : Reach 69653 := rs (se 6 (by rfl) ⟨1632, by rfl⟩) (B 3265 (by norm_num) ⟨1632, by rfl⟩ (by norm_num))
theorem R102437 : Reach 102437 := rs (se 4 (by rfl) ⟨9603, by rfl⟩) (B 19207 (by norm_num) ⟨9603, by rfl⟩ (by norm_num))
theorem R69677 : Reach 69677 := rs (se 3 (by rfl) ⟨13064, by rfl⟩) (B 26129 (by norm_num) ⟨13064, by rfl⟩ (by norm_num))
theorem R167989 : Reach 167989 := rs (se 5 (by rfl) ⟨7874, by rfl⟩) (B 15749 (by norm_num) ⟨7874, by rfl⟩ (by norm_num))
theorem R69701 : Reach 69701 := rs (se 4 (by rfl) ⟨6534, by rfl⟩) (B 13069 (by norm_num) ⟨6534, by rfl⟩ (by norm_num))
theorem R69725 : Reach 69725 := rs (se 3 (by rfl) ⟨13073, by rfl⟩) (B 26147 (by norm_num) ⟨13073, by rfl⟩ (by norm_num))
theorem R102509 : Reach 102509 := rs (se 3 (by rfl) ⟨19220, by rfl⟩) (B 38441 (by norm_num) ⟨19220, by rfl⟩ (by norm_num))
theorem R364661 : Reach 364661 := rs (se 5 (by rfl) ⟨17093, by rfl⟩) (B 34187 (by norm_num) ⟨17093, by rfl⟩ (by norm_num))
theorem R69749 : Reach 69749 := rs (se 5 (by rfl) ⟨3269, by rfl⟩) (B 6539 (by norm_num) ⟨3269, by rfl⟩ (by norm_num))
theorem R69773 : Reach 69773 := rs (se 3 (by rfl) ⟨13082, by rfl⟩) (B 26165 (by norm_num) ⟨13082, by rfl⟩ (by norm_num))
theorem R69797 : Reach 69797 := rs (se 4 (by rfl) ⟨6543, by rfl⟩) (B 13087 (by norm_num) ⟨6543, by rfl⟩ (by norm_num))
theorem R102581 : Reach 102581 := rs (se 5 (by rfl) ⟨4808, by rfl⟩) (B 9617 (by norm_num) ⟨4808, by rfl⟩ (by norm_num))
theorem R69821 : Reach 69821 := rs (se 3 (by rfl) ⟨13091, by rfl⟩) (B 26183 (by norm_num) ⟨13091, by rfl⟩ (by norm_num))
theorem R69845 : Reach 69845 := rs (se 7 (by rfl) ⟨818, by rfl⟩) (B 1637 (by norm_num) ⟨818, by rfl⟩ (by norm_num))
theorem R69869 : Reach 69869 := rs (se 3 (by rfl) ⟨13100, by rfl⟩) (B 26201 (by norm_num) ⟨13100, by rfl⟩ (by norm_num))
theorem R102653 : Reach 102653 := rs (se 3 (by rfl) ⟨19247, by rfl⟩) (B 38495 (by norm_num) ⟨19247, by rfl⟩ (by norm_num))
theorem R69893 : Reach 69893 := rs (se 4 (by rfl) ⟨6552, by rfl⟩) (B 13105 (by norm_num) ⟨6552, by rfl⟩ (by norm_num))
theorem R69917 : Reach 69917 := rs (se 3 (by rfl) ⟨13109, by rfl⟩) (B 26219 (by norm_num) ⟨13109, by rfl⟩ (by norm_num))
theorem R69941 : Reach 69941 := rs (se 5 (by rfl) ⟨3278, by rfl⟩) (B 6557 (by norm_num) ⟨3278, by rfl⟩ (by norm_num))
theorem R102725 : Reach 102725 := rs (se 4 (by rfl) ⟨9630, by rfl⟩) (B 19261 (by norm_num) ⟨9630, by rfl⟩ (by norm_num))
theorem R69965 : Reach 69965 := rs (se 3 (by rfl) ⟨13118, by rfl⟩) (B 26237 (by norm_num) ⟨13118, by rfl⟩ (by norm_num))
theorem R168277 : Reach 168277 := rs (se 10 (by rfl) ⟨246, by rfl⟩) (B 493 (by norm_num) ⟨246, by rfl⟩ (by norm_num))
theorem R69989 : Reach 69989 := rs (se 4 (by rfl) ⟨6561, by rfl⟩) (B 13123 (by norm_num) ⟨6561, by rfl⟩ (by norm_num))
theorem R70013 : Reach 70013 := rs (se 3 (by rfl) ⟨13127, by rfl⟩) (B 26255 (by norm_num) ⟨13127, by rfl⟩ (by norm_num))
theorem R102797 : Reach 102797 := rs (se 3 (by rfl) ⟨19274, by rfl⟩) (B 38549 (by norm_num) ⟨19274, by rfl⟩ (by norm_num))
theorem R70037 : Reach 70037 := rs (se 6 (by rfl) ⟨1641, by rfl⟩) (B 3283 (by norm_num) ⟨1641, by rfl⟩ (by norm_num))
theorem R70061 : Reach 70061 := rs (se 3 (by rfl) ⟨13136, by rfl⟩) (B 26273 (by norm_num) ⟨13136, by rfl⟩ (by norm_num))
theorem R70085 : Reach 70085 := rs (se 4 (by rfl) ⟨6570, by rfl⟩) (B 13141 (by norm_num) ⟨6570, by rfl⟩ (by norm_num))
theorem R102869 : Reach 102869 := rs (se 7 (by rfl) ⟨1205, by rfl⟩) (B 2411 (by norm_num) ⟨1205, by rfl⟩ (by norm_num))
theorem R70109 : Reach 70109 := rs (se 3 (by rfl) ⟨13145, by rfl⟩) (B 26291 (by norm_num) ⟨13145, by rfl⟩ (by norm_num))
theorem R70133 : Reach 70133 := rs (se 5 (by rfl) ⟨3287, by rfl⟩) (B 6575 (by norm_num) ⟨3287, by rfl⟩ (by norm_num))
theorem R70157 : Reach 70157 := rs (se 3 (by rfl) ⟨13154, by rfl⟩) (B 26309 (by norm_num) ⟨13154, by rfl⟩ (by norm_num))
theorem R102941 : Reach 102941 := rs (se 3 (by rfl) ⟨19301, by rfl⟩) (B 38603 (by norm_num) ⟨19301, by rfl⟩ (by norm_num))
theorem R70181 : Reach 70181 := rs (se 4 (by rfl) ⟨6579, by rfl⟩) (B 13159 (by norm_num) ⟨6579, by rfl⟩ (by norm_num))
theorem R70205 : Reach 70205 := rs (se 3 (by rfl) ⟨13163, by rfl⟩) (B 26327 (by norm_num) ⟨13163, by rfl⟩ (by norm_num))
theorem R70229 : Reach 70229 := rs (se 8 (by rfl) ⟨411, by rfl⟩) (B 823 (by norm_num) ⟨411, by rfl⟩ (by norm_num))
theorem R70237 : Reach 70237 := rs (se 3 (by rfl) ⟨13169, by rfl⟩) (B 26339 (by norm_num) ⟨13169, by rfl⟩ (by norm_num))
theorem R103013 : Reach 103013 := rs (se 4 (by rfl) ⟨9657, by rfl⟩) (B 19315 (by norm_num) ⟨9657, by rfl⟩ (by norm_num))
theorem R70253 : Reach 70253 := rs (se 3 (by rfl) ⟨13172, by rfl⟩) (B 26345 (by norm_num) ⟨13172, by rfl⟩ (by norm_num))
theorem R168581 : Reach 168581 := rs (se 4 (by rfl) ⟨15804, by rfl⟩) (B 31609 (by norm_num) ⟨15804, by rfl⟩ (by norm_num))
theorem R70277 : Reach 70277 := rs (se 4 (by rfl) ⟨6588, by rfl⟩) (B 13177 (by norm_num) ⟨6588, by rfl⟩ (by norm_num))
theorem R70301 : Reach 70301 := rs (se 3 (by rfl) ⟨13181, by rfl⟩) (B 26363 (by norm_num) ⟨13181, by rfl⟩ (by norm_num))
theorem R103085 : Reach 103085 := rs (se 3 (by rfl) ⟨19328, by rfl⟩) (B 38657 (by norm_num) ⟨19328, by rfl⟩ (by norm_num))
theorem R70325 : Reach 70325 := rs (se 5 (by rfl) ⟨3296, by rfl⟩) (B 6593 (by norm_num) ⟨3296, by rfl⟩ (by norm_num))
theorem R70349 : Reach 70349 := rs (se 3 (by rfl) ⟨13190, by rfl⟩) (B 26381 (by norm_num) ⟨13190, by rfl⟩ (by norm_num))
theorem R70373 : Reach 70373 := rs (se 4 (by rfl) ⟨6597, by rfl⟩) (B 13195 (by norm_num) ⟨6597, by rfl⟩ (by norm_num))
theorem R103157 : Reach 103157 := rs (se 5 (by rfl) ⟨4835, by rfl⟩) (B 9671 (by norm_num) ⟨4835, by rfl⟩ (by norm_num))
theorem R70397 : Reach 70397 := rs (se 3 (by rfl) ⟨13199, by rfl⟩) (B 26399 (by norm_num) ⟨13199, by rfl⟩ (by norm_num))
theorem R70421 : Reach 70421 := rs (se 6 (by rfl) ⟨1650, by rfl⟩) (B 3301 (by norm_num) ⟨1650, by rfl⟩ (by norm_num))
theorem R70445 : Reach 70445 := rs (se 3 (by rfl) ⟨13208, by rfl⟩) (B 26417 (by norm_num) ⟨13208, by rfl⟩ (by norm_num))
theorem R103229 : Reach 103229 := rs (se 3 (by rfl) ⟨19355, by rfl⟩) (B 38711 (by norm_num) ⟨19355, by rfl⟩ (by norm_num))
theorem R70469 : Reach 70469 := rs (se 4 (by rfl) ⟨6606, by rfl⟩) (B 13213 (by norm_num) ⟨6606, by rfl⟩ (by norm_num))
theorem R299861 : Reach 299861 := rs (se 9 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R70493 : Reach 70493 := rs (se 3 (by rfl) ⟨13217, by rfl⟩) (B 26435 (by norm_num) ⟨13217, by rfl⟩ (by norm_num))
theorem R70517 : Reach 70517 := rs (se 5 (by rfl) ⟨3305, by rfl⟩) (B 6611 (by norm_num) ⟨3305, by rfl⟩ (by norm_num))
theorem R103301 : Reach 103301 := rs (se 4 (by rfl) ⟨9684, by rfl⟩) (B 19369 (by norm_num) ⟨9684, by rfl⟩ (by norm_num))
theorem R70541 : Reach 70541 := rs (se 3 (by rfl) ⟨13226, by rfl⟩) (B 26453 (by norm_num) ⟨13226, by rfl⟩ (by norm_num))
theorem R70565 : Reach 70565 := rs (se 4 (by rfl) ⟨6615, by rfl⟩) (B 13231 (by norm_num) ⟨6615, by rfl⟩ (by norm_num))
theorem R70589 : Reach 70589 := rs (se 3 (by rfl) ⟨13235, by rfl⟩) (B 26471 (by norm_num) ⟨13235, by rfl⟩ (by norm_num))
theorem R103373 : Reach 103373 := rs (se 3 (by rfl) ⟨19382, by rfl⟩) (B 38765 (by norm_num) ⟨19382, by rfl⟩ (by norm_num))
theorem R70613 : Reach 70613 := rs (se 7 (by rfl) ⟨827, by rfl⟩) (B 1655 (by norm_num) ⟨827, by rfl⟩ (by norm_num))
theorem R70637 : Reach 70637 := rs (se 3 (by rfl) ⟨13244, by rfl⟩) (B 26489 (by norm_num) ⟨13244, by rfl⟩ (by norm_num))
theorem R70661 : Reach 70661 := rs (se 4 (by rfl) ⟨6624, by rfl⟩) (B 13249 (by norm_num) ⟨6624, by rfl⟩ (by norm_num))
theorem R103445 : Reach 103445 := rs (se 6 (by rfl) ⟨2424, by rfl⟩) (B 4849 (by norm_num) ⟨2424, by rfl⟩ (by norm_num))
theorem R103517 : Reach 103517 := rs (se 3 (by rfl) ⟨19409, by rfl⟩) (B 38819 (by norm_num) ⟨19409, by rfl⟩ (by norm_num))
theorem R103589 : Reach 103589 := rs (se 4 (by rfl) ⟨9711, by rfl⟩) (B 19423 (by norm_num) ⟨9711, by rfl⟩ (by norm_num))
theorem R103661 : Reach 103661 := rs (se 3 (by rfl) ⟨19436, by rfl⟩) (B 38873 (by norm_num) ⟨19436, by rfl⟩ (by norm_num))
theorem R103733 : Reach 103733 := rs (se 5 (by rfl) ⟨4862, by rfl⟩) (B 9725 (by norm_num) ⟨4862, by rfl⟩ (by norm_num))
theorem R103805 : Reach 103805 := rs (se 3 (by rfl) ⟨19463, by rfl⟩) (B 38927 (by norm_num) ⟨19463, by rfl⟩ (by norm_num))
theorem R103837 : Reach 103837 := rs (se 3 (by rfl) ⟨19469, by rfl⟩) (B 38939 (by norm_num) ⟨19469, by rfl⟩ (by norm_num))
theorem R103877 : Reach 103877 := rs (se 4 (by rfl) ⟨9738, by rfl⟩) (B 19477 (by norm_num) ⟨9738, by rfl⟩ (by norm_num))
theorem R103949 : Reach 103949 := rs (se 3 (by rfl) ⟨19490, by rfl⟩) (B 38981 (by norm_num) ⟨19490, by rfl⟩ (by norm_num))
theorem R267797 : Reach 267797 := rs (se 6 (by rfl) ⟨6276, by rfl⟩) (B 12553 (by norm_num) ⟨6276, by rfl⟩ (by norm_num))
theorem R235061 : Reach 235061 := rs (se 5 (by rfl) ⟨11018, by rfl⟩) (B 22037 (by norm_num) ⟨11018, by rfl⟩ (by norm_num))
theorem R104021 : Reach 104021 := rs (se 8 (by rfl) ⟨609, by rfl⟩) (B 1219 (by norm_num) ⟨609, by rfl⟩ (by norm_num))
theorem R104093 : Reach 104093 := rs (se 3 (by rfl) ⟨19517, by rfl⟩) (B 39035 (by norm_num) ⟨19517, by rfl⟩ (by norm_num))
theorem R104165 : Reach 104165 := rs (se 4 (by rfl) ⟨9765, by rfl⟩) (B 19531 (by norm_num) ⟨9765, by rfl⟩ (by norm_num))
theorem R104237 : Reach 104237 := rs (se 3 (by rfl) ⟨19544, by rfl⟩) (B 39089 (by norm_num) ⟨19544, by rfl⟩ (by norm_num))
theorem R104309 : Reach 104309 := rs (se 5 (by rfl) ⟨4889, by rfl⟩) (B 9779 (by norm_num) ⟨4889, by rfl⟩ (by norm_num))
theorem R268181 : Reach 268181 := rs (se 6 (by rfl) ⟨6285, by rfl⟩) (B 12571 (by norm_num) ⟨6285, by rfl⟩ (by norm_num))
theorem R104381 : Reach 104381 := rs (se 3 (by rfl) ⟨19571, by rfl⟩) (B 39143 (by norm_num) ⟨19571, by rfl⟩ (by norm_num))
theorem R71621 : Reach 71621 := rs (se 4 (by rfl) ⟨6714, by rfl⟩) (B 13429 (by norm_num) ⟨6714, by rfl⟩ (by norm_num))
theorem R104453 : Reach 104453 := rs (se 4 (by rfl) ⟨9792, by rfl⟩) (B 19585 (by norm_num) ⟨9792, by rfl⟩ (by norm_num))
theorem R104525 : Reach 104525 := rs (se 3 (by rfl) ⟨19598, by rfl⟩) (B 39197 (by norm_num) ⟨19598, by rfl⟩ (by norm_num))
theorem R71813 : Reach 71813 := rs (se 4 (by rfl) ⟨6732, by rfl⟩) (B 13465 (by norm_num) ⟨6732, by rfl⟩ (by norm_num))
theorem R104597 : Reach 104597 := rs (se 6 (by rfl) ⟨2451, by rfl⟩) (B 4903 (by norm_num) ⟨2451, by rfl⟩ (by norm_num))
theorem R104669 : Reach 104669 := rs (se 3 (by rfl) ⟨19625, by rfl⟩) (B 39251 (by norm_num) ⟨19625, by rfl⟩ (by norm_num))
theorem R71941 : Reach 71941 := rs (se 4 (by rfl) ⟨6744, by rfl⟩) (B 13489 (by norm_num) ⟨6744, by rfl⟩ (by norm_num))
theorem R104741 : Reach 104741 := rs (se 4 (by rfl) ⟨9819, by rfl⟩) (B 19639 (by norm_num) ⟨9819, by rfl⟩ (by norm_num))
theorem R104789 : Reach 104789 := rs (se 10 (by rfl) ⟨153, by rfl⟩) (B 307 (by norm_num) ⟨153, by rfl⟩ (by norm_num))
theorem R104813 : Reach 104813 := rs (se 3 (by rfl) ⟨19652, by rfl⟩) (B 39305 (by norm_num) ⟨19652, by rfl⟩ (by norm_num))
theorem R104885 : Reach 104885 := rs (se 5 (by rfl) ⟨4916, by rfl⟩) (B 9833 (by norm_num) ⟨4916, by rfl⟩ (by norm_num))
theorem R104957 : Reach 104957 := rs (se 3 (by rfl) ⟨19679, by rfl⟩) (B 39359 (by norm_num) ⟨19679, by rfl⟩ (by norm_num))
theorem R105029 : Reach 105029 := rs (se 4 (by rfl) ⟨9846, by rfl⟩) (B 19693 (by norm_num) ⟨9846, by rfl⟩ (by norm_num))
theorem R72325 : Reach 72325 := rs (se 4 (by rfl) ⟨6780, by rfl⟩) (B 13561 (by norm_num) ⟨6780, by rfl⟩ (by norm_num))
theorem R105101 : Reach 105101 := rs (se 3 (by rfl) ⟨19706, by rfl⟩) (B 39413 (by norm_num) ⟨19706, by rfl⟩ (by norm_num))
theorem R170693 : Reach 170693 := rs (se 4 (by rfl) ⟨16002, by rfl⟩) (B 32005 (by norm_num) ⟨16002, by rfl⟩ (by norm_num))
theorem R105173 : Reach 105173 := rs (se 7 (by rfl) ⟨1232, by rfl⟩) (B 2465 (by norm_num) ⟨1232, by rfl⟩ (by norm_num))
theorem R400085 : Reach 400085 := rs (se 7 (by rfl) ⟨4688, by rfl⟩) (B 9377 (by norm_num) ⟨4688, by rfl⟩ (by norm_num))
theorem R105181 : Reach 105181 := rs (se 3 (by rfl) ⟨19721, by rfl⟩) (B 39443 (by norm_num) ⟨19721, by rfl⟩ (by norm_num))
theorem R105245 : Reach 105245 := rs (se 3 (by rfl) ⟨19733, by rfl⟩) (B 39467 (by norm_num) ⟨19733, by rfl⟩ (by norm_num))
theorem R105317 : Reach 105317 := rs (se 4 (by rfl) ⟨9873, by rfl⟩) (B 19747 (by norm_num) ⟨9873, by rfl⟩ (by norm_num))
theorem R72581 : Reach 72581 := rs (se 4 (by rfl) ⟨6804, by rfl⟩) (B 13609 (by norm_num) ⟨6804, by rfl⟩ (by norm_num))
theorem R105389 : Reach 105389 := rs (se 3 (by rfl) ⟨19760, by rfl⟩) (B 39521 (by norm_num) ⟨19760, by rfl⟩ (by norm_num))
theorem R170981 : Reach 170981 := rs (se 4 (by rfl) ⟨16029, by rfl⟩) (B 32059 (by norm_num) ⟨16029, by rfl⟩ (by norm_num))
theorem R105461 : Reach 105461 := rs (se 5 (by rfl) ⟨4943, by rfl⟩) (B 9887 (by norm_num) ⟨4943, by rfl⟩ (by norm_num))
theorem R105533 : Reach 105533 := rs (se 3 (by rfl) ⟨19787, by rfl⟩) (B 39575 (by norm_num) ⟨19787, by rfl⟩ (by norm_num))
theorem R236629 : Reach 236629 := rs (se 8 (by rfl) ⟨1386, by rfl⟩) (B 2773 (by norm_num) ⟨1386, by rfl⟩ (by norm_num))
theorem R72805 : Reach 72805 := rs (se 4 (by rfl) ⟨6825, by rfl⟩) (B 13651 (by norm_num) ⟨6825, by rfl⟩ (by norm_num))
theorem R105605 : Reach 105605 := rs (se 4 (by rfl) ⟨9900, by rfl⟩) (B 19801 (by norm_num) ⟨9900, by rfl⟩ (by norm_num))
theorem R72893 : Reach 72893 := rs (se 3 (by rfl) ⟨13667, by rfl⟩) (B 27335 (by norm_num) ⟨13667, by rfl⟩ (by norm_num))
theorem R105677 : Reach 105677 := rs (se 3 (by rfl) ⟨19814, by rfl⟩) (B 39629 (by norm_num) ⟨19814, by rfl⟩ (by norm_num))
theorem R105749 : Reach 105749 := rs (se 6 (by rfl) ⟨2478, by rfl⟩) (B 4957 (by norm_num) ⟨2478, by rfl⟩ (by norm_num))
theorem R73021 : Reach 73021 := rs (se 3 (by rfl) ⟨13691, by rfl⟩) (B 27383 (by norm_num) ⟨13691, by rfl⟩ (by norm_num))
theorem R73037 : Reach 73037 := rs (se 3 (by rfl) ⟨13694, by rfl⟩) (B 27389 (by norm_num) ⟨13694, by rfl⟩ (by norm_num))
theorem R105821 : Reach 105821 := rs (se 3 (by rfl) ⟨19841, by rfl⟩) (B 39683 (by norm_num) ⟨19841, by rfl⟩ (by norm_num))
theorem R73109 : Reach 73109 := rs (se 6 (by rfl) ⟨1713, by rfl⟩) (B 3427 (by norm_num) ⟨1713, by rfl⟩ (by norm_num))
theorem R105893 : Reach 105893 := rs (se 4 (by rfl) ⟨9927, by rfl⟩) (B 19855 (by norm_num) ⟨9927, by rfl⟩ (by norm_num))
theorem R105965 : Reach 105965 := rs (se 3 (by rfl) ⟨19868, by rfl⟩) (B 39737 (by norm_num) ⟨19868, by rfl⟩ (by norm_num))
theorem R73237 : Reach 73237 := rs (se 6 (by rfl) ⟨1716, by rfl⟩) (B 3433 (by norm_num) ⟨1716, by rfl⟩ (by norm_num))
theorem R73261 : Reach 73261 := rs (se 3 (by rfl) ⟨13736, by rfl⟩) (B 27473 (by norm_num) ⟨13736, by rfl⟩ (by norm_num))
theorem R73325 : Reach 73325 := rs (se 3 (by rfl) ⟨13748, by rfl⟩) (B 27497 (by norm_num) ⟨13748, by rfl⟩ (by norm_num))
theorem R73453 : Reach 73453 := rs (se 3 (by rfl) ⟨13772, by rfl⟩) (B 27545 (by norm_num) ⟨13772, by rfl⟩ (by norm_num))
theorem R73541 : Reach 73541 := rs (se 4 (by rfl) ⟨6894, by rfl⟩) (B 13789 (by norm_num) ⟨6894, by rfl⟩ (by norm_num))
theorem R73669 : Reach 73669 := rs (se 4 (by rfl) ⟨6906, by rfl⟩) (B 13813 (by norm_num) ⟨6906, by rfl⟩ (by norm_num))
theorem R73757 : Reach 73757 := rs (se 3 (by rfl) ⟨13829, by rfl⟩) (B 27659 (by norm_num) ⟨13829, by rfl⟩ (by norm_num))
theorem R237653 : Reach 237653 := rs (se 8 (by rfl) ⟨1392, by rfl⟩) (B 2785 (by norm_num) ⟨1392, by rfl⟩ (by norm_num))
theorem R172165 : Reach 172165 := rs (se 4 (by rfl) ⟨16140, by rfl⟩) (B 32281 (by norm_num) ⟨16140, by rfl⟩ (by norm_num))
theorem R73885 : Reach 73885 := rs (se 3 (by rfl) ⟨13853, by rfl⟩) (B 27707 (by norm_num) ⟨13853, by rfl⟩ (by norm_num))
theorem R139445 : Reach 139445 := rs (se 5 (by rfl) ⟨6536, by rfl⟩) (B 13073 (by norm_num) ⟨6536, by rfl⟩ (by norm_num))
theorem R73973 : Reach 73973 := rs (se 5 (by rfl) ⟨3467, by rfl⟩) (B 6935 (by norm_num) ⟨3467, by rfl⟩ (by norm_num))
theorem R74101 : Reach 74101 := rs (se 5 (by rfl) ⟨3473, by rfl⟩) (B 6947 (by norm_num) ⟨3473, by rfl⟩ (by norm_num))
theorem R172469 : Reach 172469 := rs (se 5 (by rfl) ⟨8084, by rfl⟩) (B 16169 (by norm_num) ⟨8084, by rfl⟩ (by norm_num))
theorem R74189 : Reach 74189 := rs (se 3 (by rfl) ⟨13910, by rfl⟩) (B 27821 (by norm_num) ⟨13910, by rfl⟩ (by norm_num))
theorem R434645 : Reach 434645 := rs (se 7 (by rfl) ⟨5093, by rfl⟩) (B 10187 (by norm_num) ⟨5093, by rfl⟩ (by norm_num))
theorem R139781 : Reach 139781 := rs (se 4 (by rfl) ⟨13104, by rfl⟩) (B 26209 (by norm_num) ⟨13104, by rfl⟩ (by norm_num))
theorem R74317 : Reach 74317 := rs (se 3 (by rfl) ⟨13934, by rfl⟩) (B 27869 (by norm_num) ⟨13934, by rfl⟩ (by norm_num))
theorem R74405 : Reach 74405 := rs (se 4 (by rfl) ⟨6975, by rfl⟩) (B 13951 (by norm_num) ⟨6975, by rfl⟩ (by norm_num))
theorem R107189 : Reach 107189 := rs (se 5 (by rfl) ⟨5024, by rfl⟩) (B 10049 (by norm_num) ⟨5024, by rfl⟩ (by norm_num))
theorem R74533 : Reach 74533 := rs (se 4 (by rfl) ⟨6987, by rfl⟩) (B 13975 (by norm_num) ⟨6987, by rfl⟩ (by norm_num))
theorem R107365 : Reach 107365 := rs (se 4 (by rfl) ⟨10065, by rfl⟩) (B 20131 (by norm_num) ⟨10065, by rfl⟩ (by norm_num))
theorem R74621 : Reach 74621 := rs (se 3 (by rfl) ⟨13991, by rfl⟩) (B 27983 (by norm_num) ⟨13991, by rfl⟩ (by norm_num))
theorem R74677 : Reach 74677 := rs (se 5 (by rfl) ⟨3500, by rfl⟩) (B 7001 (by norm_num) ⟨3500, by rfl⟩ (by norm_num))
theorem R74749 : Reach 74749 := rs (se 3 (by rfl) ⟨14015, by rfl⟩) (B 28031 (by norm_num) ⟨14015, by rfl⟩ (by norm_num))
theorem R74837 : Reach 74837 := rs (se 8 (by rfl) ⟨438, by rfl⟩) (B 877 (by norm_num) ⟨438, by rfl⟩ (by norm_num))
theorem R369845 : Reach 369845 := rs (se 5 (by rfl) ⟨17336, by rfl⟩) (B 34673 (by norm_num) ⟨17336, by rfl⟩ (by norm_num))
theorem R74965 : Reach 74965 := rs (se 7 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R75053 : Reach 75053 := rs (se 3 (by rfl) ⟨14072, by rfl⟩) (B 28145 (by norm_num) ⟨14072, by rfl⟩ (by norm_num))
theorem R75181 : Reach 75181 := rs (se 3 (by rfl) ⟨14096, by rfl⟩) (B 28193 (by norm_num) ⟨14096, by rfl⟩ (by norm_num))
theorem R959957 : Reach 959957 := rs (se 7 (by rfl) ⟨11249, by rfl⟩) (B 22499 (by norm_num) ⟨11249, by rfl⟩ (by norm_num))
theorem R75269 : Reach 75269 := rs (se 4 (by rfl) ⟨7056, by rfl⟩) (B 14113 (by norm_num) ⟨7056, by rfl⟩ (by norm_num))
theorem R75349 : Reach 75349 := rs (se 8 (by rfl) ⟨441, by rfl⟩) (B 883 (by norm_num) ⟨441, by rfl⟩ (by norm_num))
theorem R75397 : Reach 75397 := rs (se 4 (by rfl) ⟨7068, by rfl⟩) (B 14137 (by norm_num) ⟨7068, by rfl⟩ (by norm_num))
theorem R403157 : Reach 403157 := rs (se 7 (by rfl) ⟨4724, by rfl⟩) (B 9449 (by norm_num) ⟨4724, by rfl⟩ (by norm_num))
theorem R75485 : Reach 75485 := rs (se 3 (by rfl) ⟨14153, by rfl⟩) (B 28307 (by norm_num) ⟨14153, by rfl⟩ (by norm_num))
theorem R108253 : Reach 108253 := rs (se 3 (by rfl) ⟨20297, by rfl⟩) (B 40595 (by norm_num) ⟨20297, by rfl⟩ (by norm_num))
theorem R108325 : Reach 108325 := rs (se 4 (by rfl) ⟨10155, by rfl⟩) (B 20311 (by norm_num) ⟨10155, by rfl⟩ (by norm_num))
theorem R108373 : Reach 108373 := rs (se 9 (by rfl) ⟨317, by rfl⟩) (B 635 (by norm_num) ⟨317, by rfl⟩ (by norm_num))
theorem R75613 : Reach 75613 := rs (se 3 (by rfl) ⟨14177, by rfl⟩) (B 28355 (by norm_num) ⟨14177, by rfl⟩ (by norm_num))
theorem R75701 : Reach 75701 := rs (se 5 (by rfl) ⟨3548, by rfl⟩) (B 7097 (by norm_num) ⟨3548, by rfl⟩ (by norm_num))
theorem R75757 : Reach 75757 := rs (se 3 (by rfl) ⟨14204, by rfl⟩) (B 28409 (by norm_num) ⟨14204, by rfl⟩ (by norm_num))
theorem R75829 : Reach 75829 := rs (se 5 (by rfl) ⟨3554, by rfl⟩) (B 7109 (by norm_num) ⟨3554, by rfl⟩ (by norm_num))
theorem R43121 : Reach 43121 := rs (se 2 (by rfl) ⟨16170, by rfl⟩) (B 32341 (by norm_num) ⟨16170, by rfl⟩ (by norm_num))
theorem R43125 : Reach 43125 := rs (se 5 (by rfl) ⟨2021, by rfl⟩) (B 4043 (by norm_num) ⟨2021, by rfl⟩ (by norm_num))
theorem R43129 : Reach 43129 := rs (se 2 (by rfl) ⟨16173, by rfl⟩) (B 32347 (by norm_num) ⟨16173, by rfl⟩ (by norm_num))
theorem R43133 : Reach 43133 := rs (se 3 (by rfl) ⟨8087, by rfl⟩) (B 16175 (by norm_num) ⟨8087, by rfl⟩ (by norm_num))
theorem R43137 : Reach 43137 := rs (se 2 (by rfl) ⟨16176, by rfl⟩) (B 32353 (by norm_num) ⟨16176, by rfl⟩ (by norm_num))
theorem R43141 : Reach 43141 := rs (se 4 (by rfl) ⟨4044, by rfl⟩) (B 8089 (by norm_num) ⟨4044, by rfl⟩ (by norm_num))
theorem R43145 : Reach 43145 := rs (se 2 (by rfl) ⟨16179, by rfl⟩) (B 32359 (by norm_num) ⟨16179, by rfl⟩ (by norm_num))
theorem R43149 : Reach 43149 := rs (se 3 (by rfl) ⟨8090, by rfl⟩) (B 16181 (by norm_num) ⟨8090, by rfl⟩ (by norm_num))
theorem R75917 : Reach 75917 := rs (se 3 (by rfl) ⟨14234, by rfl⟩) (B 28469 (by norm_num) ⟨14234, by rfl⟩ (by norm_num))
theorem R43153 : Reach 43153 := rs (se 2 (by rfl) ⟨16182, by rfl⟩) (B 32365 (by norm_num) ⟨16182, by rfl⟩ (by norm_num))
theorem R43157 : Reach 43157 := rs (se 6 (by rfl) ⟨1011, by rfl⟩) (B 2023 (by norm_num) ⟨1011, by rfl⟩ (by norm_num))
theorem R43161 : Reach 43161 := rs (se 2 (by rfl) ⟨16185, by rfl⟩) (B 32371 (by norm_num) ⟨16185, by rfl⟩ (by norm_num))
theorem R43165 : Reach 43165 := rs (se 3 (by rfl) ⟨8093, by rfl⟩) (B 16187 (by norm_num) ⟨8093, by rfl⟩ (by norm_num))
theorem R43169 : Reach 43169 := rs (se 2 (by rfl) ⟨16188, by rfl⟩) (B 32377 (by norm_num) ⟨16188, by rfl⟩ (by norm_num))
theorem R43173 : Reach 43173 := rs (se 4 (by rfl) ⟨4047, by rfl⟩) (B 8095 (by norm_num) ⟨4047, by rfl⟩ (by norm_num))
theorem R43177 : Reach 43177 := rs (se 2 (by rfl) ⟨16191, by rfl⟩) (B 32383 (by norm_num) ⟨16191, by rfl⟩ (by norm_num))
theorem R43181 : Reach 43181 := rs (se 3 (by rfl) ⟨8096, by rfl⟩) (B 16193 (by norm_num) ⟨8096, by rfl⟩ (by norm_num))
theorem R43185 : Reach 43185 := rs (se 2 (by rfl) ⟨16194, by rfl⟩) (B 32389 (by norm_num) ⟨16194, by rfl⟩ (by norm_num))
theorem R43189 : Reach 43189 := rs (se 5 (by rfl) ⟨2024, by rfl⟩) (B 4049 (by norm_num) ⟨2024, by rfl⟩ (by norm_num))
theorem R43193 : Reach 43193 := rs (se 2 (by rfl) ⟨16197, by rfl⟩) (B 32395 (by norm_num) ⟨16197, by rfl⟩ (by norm_num))
theorem R43197 : Reach 43197 := rs (se 3 (by rfl) ⟨8099, by rfl⟩) (B 16199 (by norm_num) ⟨8099, by rfl⟩ (by norm_num))
theorem R43201 : Reach 43201 := rs (se 2 (by rfl) ⟨16200, by rfl⟩) (B 32401 (by norm_num) ⟨16200, by rfl⟩ (by norm_num))
theorem R43205 : Reach 43205 := rs (se 4 (by rfl) ⟨4050, by rfl⟩) (B 8101 (by norm_num) ⟨4050, by rfl⟩ (by norm_num))
theorem R43209 : Reach 43209 := rs (se 2 (by rfl) ⟨16203, by rfl⟩) (B 32407 (by norm_num) ⟨16203, by rfl⟩ (by norm_num))
theorem R43213 : Reach 43213 := rs (se 3 (by rfl) ⟨8102, by rfl⟩) (B 16205 (by norm_num) ⟨8102, by rfl⟩ (by norm_num))
theorem R43217 : Reach 43217 := rs (se 2 (by rfl) ⟨16206, by rfl⟩) (B 32413 (by norm_num) ⟨16206, by rfl⟩ (by norm_num))
theorem R43221 : Reach 43221 := rs (se 7 (by rfl) ⟨506, by rfl⟩) (B 1013 (by norm_num) ⟨506, by rfl⟩ (by norm_num))
theorem R43225 : Reach 43225 := rs (se 2 (by rfl) ⟨16209, by rfl⟩) (B 32419 (by norm_num) ⟨16209, by rfl⟩ (by norm_num))
theorem R43229 : Reach 43229 := rs (se 3 (by rfl) ⟨8105, by rfl⟩) (B 16211 (by norm_num) ⟨8105, by rfl⟩ (by norm_num))
theorem R43233 : Reach 43233 := rs (se 2 (by rfl) ⟨16212, by rfl⟩) (B 32425 (by norm_num) ⟨16212, by rfl⟩ (by norm_num))
theorem R43237 : Reach 43237 := rs (se 4 (by rfl) ⟨4053, by rfl⟩) (B 8107 (by norm_num) ⟨4053, by rfl⟩ (by norm_num))
theorem R43241 : Reach 43241 := rs (se 2 (by rfl) ⟨16215, by rfl⟩) (B 32431 (by norm_num) ⟨16215, by rfl⟩ (by norm_num))
theorem R43245 : Reach 43245 := rs (se 3 (by rfl) ⟨8108, by rfl⟩) (B 16217 (by norm_num) ⟨8108, by rfl⟩ (by norm_num))
theorem R43249 : Reach 43249 := rs (se 2 (by rfl) ⟨16218, by rfl⟩) (B 32437 (by norm_num) ⟨16218, by rfl⟩ (by norm_num))
theorem R43253 : Reach 43253 := rs (se 5 (by rfl) ⟨2027, by rfl⟩) (B 4055 (by norm_num) ⟨2027, by rfl⟩ (by norm_num))
theorem R43257 : Reach 43257 := rs (se 2 (by rfl) ⟨16221, by rfl⟩) (B 32443 (by norm_num) ⟨16221, by rfl⟩ (by norm_num))
theorem R43261 : Reach 43261 := rs (se 3 (by rfl) ⟨8111, by rfl⟩) (B 16223 (by norm_num) ⟨8111, by rfl⟩ (by norm_num))
theorem R43265 : Reach 43265 := rs (se 2 (by rfl) ⟨16224, by rfl⟩) (B 32449 (by norm_num) ⟨16224, by rfl⟩ (by norm_num))
theorem R43269 : Reach 43269 := rs (se 4 (by rfl) ⟨4056, by rfl⟩) (B 8113 (by norm_num) ⟨4056, by rfl⟩ (by norm_num))
theorem R43273 : Reach 43273 := rs (se 2 (by rfl) ⟨16227, by rfl⟩) (B 32455 (by norm_num) ⟨16227, by rfl⟩ (by norm_num))
theorem R43277 : Reach 43277 := rs (se 3 (by rfl) ⟨8114, by rfl⟩) (B 16229 (by norm_num) ⟨8114, by rfl⟩ (by norm_num))
theorem R76045 : Reach 76045 := rs (se 3 (by rfl) ⟨14258, by rfl⟩) (B 28517 (by norm_num) ⟨14258, by rfl⟩ (by norm_num))
theorem R43281 : Reach 43281 := rs (se 2 (by rfl) ⟨16230, by rfl⟩) (B 32461 (by norm_num) ⟨16230, by rfl⟩ (by norm_num))
theorem R43285 : Reach 43285 := rs (se 6 (by rfl) ⟨1014, by rfl⟩) (B 2029 (by norm_num) ⟨1014, by rfl⟩ (by norm_num))
theorem R43289 : Reach 43289 := rs (se 2 (by rfl) ⟨16233, by rfl⟩) (B 32467 (by norm_num) ⟨16233, by rfl⟩ (by norm_num))
theorem R43293 : Reach 43293 := rs (se 3 (by rfl) ⟨8117, by rfl⟩) (B 16235 (by norm_num) ⟨8117, by rfl⟩ (by norm_num))
theorem R43297 : Reach 43297 := rs (se 2 (by rfl) ⟨16236, by rfl⟩) (B 32473 (by norm_num) ⟨16236, by rfl⟩ (by norm_num))
theorem R43301 : Reach 43301 := rs (se 4 (by rfl) ⟨4059, by rfl⟩) (B 8119 (by norm_num) ⟨4059, by rfl⟩ (by norm_num))
theorem R43305 : Reach 43305 := rs (se 2 (by rfl) ⟨16239, by rfl⟩) (B 32479 (by norm_num) ⟨16239, by rfl⟩ (by norm_num))
theorem R43309 : Reach 43309 := rs (se 3 (by rfl) ⟨8120, by rfl⟩) (B 16241 (by norm_num) ⟨8120, by rfl⟩ (by norm_num))
theorem R43313 : Reach 43313 := rs (se 2 (by rfl) ⟨16242, by rfl⟩) (B 32485 (by norm_num) ⟨16242, by rfl⟩ (by norm_num))
theorem R43317 : Reach 43317 := rs (se 5 (by rfl) ⟨2030, by rfl⟩) (B 4061 (by norm_num) ⟨2030, by rfl⟩ (by norm_num))
theorem R43321 : Reach 43321 := rs (se 2 (by rfl) ⟨16245, by rfl⟩) (B 32491 (by norm_num) ⟨16245, by rfl⟩ (by norm_num))
theorem R43325 : Reach 43325 := rs (se 3 (by rfl) ⟨8123, by rfl⟩) (B 16247 (by norm_num) ⟨8123, by rfl⟩ (by norm_num))
theorem R43329 : Reach 43329 := rs (se 2 (by rfl) ⟨16248, by rfl⟩) (B 32497 (by norm_num) ⟨16248, by rfl⟩ (by norm_num))
theorem R43333 : Reach 43333 := rs (se 4 (by rfl) ⟨4062, by rfl⟩) (B 8125 (by norm_num) ⟨4062, by rfl⟩ (by norm_num))
theorem R43337 : Reach 43337 := rs (se 2 (by rfl) ⟨16251, by rfl⟩) (B 32503 (by norm_num) ⟨16251, by rfl⟩ (by norm_num))
theorem R43341 : Reach 43341 := rs (se 3 (by rfl) ⟨8126, by rfl⟩) (B 16253 (by norm_num) ⟨8126, by rfl⟩ (by norm_num))
theorem R43345 : Reach 43345 := rs (se 2 (by rfl) ⟨16254, by rfl⟩) (B 32509 (by norm_num) ⟨16254, by rfl⟩ (by norm_num))
theorem R43349 : Reach 43349 := rs (se 10 (by rfl) ⟨63, by rfl⟩) (B 127 (by norm_num) ⟨63, by rfl⟩ (by norm_num))
theorem R43353 : Reach 43353 := rs (se 2 (by rfl) ⟨16257, by rfl⟩) (B 32515 (by norm_num) ⟨16257, by rfl⟩ (by norm_num))
theorem R43357 : Reach 43357 := rs (se 3 (by rfl) ⟨8129, by rfl⟩) (B 16259 (by norm_num) ⟨8129, by rfl⟩ (by norm_num))
theorem R43361 : Reach 43361 := rs (se 2 (by rfl) ⟨16260, by rfl⟩) (B 32521 (by norm_num) ⟨16260, by rfl⟩ (by norm_num))
theorem R43365 : Reach 43365 := rs (se 4 (by rfl) ⟨4065, by rfl⟩) (B 8131 (by norm_num) ⟨4065, by rfl⟩ (by norm_num))
theorem R76133 : Reach 76133 := rs (se 4 (by rfl) ⟨7137, by rfl⟩) (B 14275 (by norm_num) ⟨7137, by rfl⟩ (by norm_num))
theorem R43369 : Reach 43369 := rs (se 2 (by rfl) ⟨16263, by rfl⟩) (B 32527 (by norm_num) ⟨16263, by rfl⟩ (by norm_num))
theorem R43373 : Reach 43373 := rs (se 3 (by rfl) ⟨8132, by rfl⟩) (B 16265 (by norm_num) ⟨8132, by rfl⟩ (by norm_num))
theorem R43377 : Reach 43377 := rs (se 2 (by rfl) ⟨16266, by rfl⟩) (B 32533 (by norm_num) ⟨16266, by rfl⟩ (by norm_num))
theorem R43381 : Reach 43381 := rs (se 5 (by rfl) ⟨2033, by rfl⟩) (B 4067 (by norm_num) ⟨2033, by rfl⟩ (by norm_num))
theorem R43385 : Reach 43385 := rs (se 2 (by rfl) ⟨16269, by rfl⟩) (B 32539 (by norm_num) ⟨16269, by rfl⟩ (by norm_num))
theorem R43389 : Reach 43389 := rs (se 3 (by rfl) ⟨8135, by rfl⟩) (B 16271 (by norm_num) ⟨8135, by rfl⟩ (by norm_num))
theorem R43393 : Reach 43393 := rs (se 2 (by rfl) ⟨16272, by rfl⟩) (B 32545 (by norm_num) ⟨16272, by rfl⟩ (by norm_num))
theorem R43397 : Reach 43397 := rs (se 4 (by rfl) ⟨4068, by rfl⟩) (B 8137 (by norm_num) ⟨4068, by rfl⟩ (by norm_num))
theorem R43401 : Reach 43401 := rs (se 2 (by rfl) ⟨16275, by rfl⟩) (B 32551 (by norm_num) ⟨16275, by rfl⟩ (by norm_num))
theorem R43405 : Reach 43405 := rs (se 3 (by rfl) ⟨8138, by rfl⟩) (B 16277 (by norm_num) ⟨8138, by rfl⟩ (by norm_num))
theorem R43409 : Reach 43409 := rs (se 2 (by rfl) ⟨16278, by rfl⟩) (B 32557 (by norm_num) ⟨16278, by rfl⟩ (by norm_num))
theorem R43413 : Reach 43413 := rs (se 6 (by rfl) ⟨1017, by rfl⟩) (B 2035 (by norm_num) ⟨1017, by rfl⟩ (by norm_num))
theorem R43417 : Reach 43417 := rs (se 2 (by rfl) ⟨16281, by rfl⟩) (B 32563 (by norm_num) ⟨16281, by rfl⟩ (by norm_num))
theorem R43421 : Reach 43421 := rs (se 3 (by rfl) ⟨8141, by rfl⟩) (B 16283 (by norm_num) ⟨8141, by rfl⟩ (by norm_num))
theorem R43425 : Reach 43425 := rs (se 2 (by rfl) ⟨16284, by rfl⟩) (B 32569 (by norm_num) ⟨16284, by rfl⟩ (by norm_num))
theorem R43429 : Reach 43429 := rs (se 4 (by rfl) ⟨4071, by rfl⟩) (B 8143 (by norm_num) ⟨4071, by rfl⟩ (by norm_num))
theorem R43433 : Reach 43433 := rs (se 2 (by rfl) ⟨16287, by rfl⟩) (B 32575 (by norm_num) ⟨16287, by rfl⟩ (by norm_num))
theorem R43437 : Reach 43437 := rs (se 3 (by rfl) ⟨8144, by rfl⟩) (B 16289 (by norm_num) ⟨8144, by rfl⟩ (by norm_num))
theorem R43441 : Reach 43441 := rs (se 2 (by rfl) ⟨16290, by rfl⟩) (B 32581 (by norm_num) ⟨16290, by rfl⟩ (by norm_num))
theorem R43445 : Reach 43445 := rs (se 5 (by rfl) ⟨2036, by rfl⟩) (B 4073 (by norm_num) ⟨2036, by rfl⟩ (by norm_num))
theorem R43449 : Reach 43449 := rs (se 2 (by rfl) ⟨16293, by rfl⟩) (B 32587 (by norm_num) ⟨16293, by rfl⟩ (by norm_num))
theorem R43453 : Reach 43453 := rs (se 3 (by rfl) ⟨8147, by rfl⟩) (B 16295 (by norm_num) ⟨8147, by rfl⟩ (by norm_num))
theorem R108989 : Reach 108989 := rs (se 3 (by rfl) ⟨20435, by rfl⟩) (B 40871 (by norm_num) ⟨20435, by rfl⟩ (by norm_num))
theorem R43457 : Reach 43457 := rs (se 2 (by rfl) ⟨16296, by rfl⟩) (B 32593 (by norm_num) ⟨16296, by rfl⟩ (by norm_num))
theorem R43461 : Reach 43461 := rs (se 4 (by rfl) ⟨4074, by rfl⟩) (B 8149 (by norm_num) ⟨4074, by rfl⟩ (by norm_num))
theorem R43465 : Reach 43465 := rs (se 2 (by rfl) ⟨16299, by rfl⟩) (B 32599 (by norm_num) ⟨16299, by rfl⟩ (by norm_num))
theorem R43469 : Reach 43469 := rs (se 3 (by rfl) ⟨8150, by rfl⟩) (B 16301 (by norm_num) ⟨8150, by rfl⟩ (by norm_num))
theorem R43473 : Reach 43473 := rs (se 2 (by rfl) ⟨16302, by rfl⟩) (B 32605 (by norm_num) ⟨16302, by rfl⟩ (by norm_num))
theorem R43477 : Reach 43477 := rs (se 7 (by rfl) ⟨509, by rfl⟩) (B 1019 (by norm_num) ⟨509, by rfl⟩ (by norm_num))
theorem R43481 : Reach 43481 := rs (se 2 (by rfl) ⟨16305, by rfl⟩) (B 32611 (by norm_num) ⟨16305, by rfl⟩ (by norm_num))
theorem R43485 : Reach 43485 := rs (se 3 (by rfl) ⟨8153, by rfl⟩) (B 16307 (by norm_num) ⟨8153, by rfl⟩ (by norm_num))
theorem R43489 : Reach 43489 := rs (se 2 (by rfl) ⟨16308, by rfl⟩) (B 32617 (by norm_num) ⟨16308, by rfl⟩ (by norm_num))
theorem R43493 : Reach 43493 := rs (se 4 (by rfl) ⟨4077, by rfl⟩) (B 8155 (by norm_num) ⟨4077, by rfl⟩ (by norm_num))
theorem R76261 : Reach 76261 := rs (se 4 (by rfl) ⟨7149, by rfl⟩) (B 14299 (by norm_num) ⟨7149, by rfl⟩ (by norm_num))
theorem R43497 : Reach 43497 := rs (se 2 (by rfl) ⟨16311, by rfl⟩) (B 32623 (by norm_num) ⟨16311, by rfl⟩ (by norm_num))
theorem R43501 : Reach 43501 := rs (se 3 (by rfl) ⟨8156, by rfl⟩) (B 16313 (by norm_num) ⟨8156, by rfl⟩ (by norm_num))
theorem R43505 : Reach 43505 := rs (se 2 (by rfl) ⟨16314, by rfl⟩) (B 32629 (by norm_num) ⟨16314, by rfl⟩ (by norm_num))
theorem R174581 : Reach 174581 := rs (se 5 (by rfl) ⟨8183, by rfl⟩) (B 16367 (by norm_num) ⟨8183, by rfl⟩ (by norm_num))
theorem R43509 : Reach 43509 := rs (se 5 (by rfl) ⟨2039, by rfl⟩) (B 4079 (by norm_num) ⟨2039, by rfl⟩ (by norm_num))
theorem R43513 : Reach 43513 := rs (se 2 (by rfl) ⟨16317, by rfl⟩) (B 32635 (by norm_num) ⟨16317, by rfl⟩ (by norm_num))
theorem R43517 : Reach 43517 := rs (se 3 (by rfl) ⟨8159, by rfl⟩) (B 16319 (by norm_num) ⟨8159, by rfl⟩ (by norm_num))
theorem R43521 : Reach 43521 := rs (se 2 (by rfl) ⟨16320, by rfl⟩) (B 32641 (by norm_num) ⟨16320, by rfl⟩ (by norm_num))
theorem R43525 : Reach 43525 := rs (se 4 (by rfl) ⟨4080, by rfl⟩) (B 8161 (by norm_num) ⟨4080, by rfl⟩ (by norm_num))
theorem R43529 : Reach 43529 := rs (se 2 (by rfl) ⟨16323, by rfl⟩) (B 32647 (by norm_num) ⟨16323, by rfl⟩ (by norm_num))
theorem R43533 : Reach 43533 := rs (se 3 (by rfl) ⟨8162, by rfl⟩) (B 16325 (by norm_num) ⟨8162, by rfl⟩ (by norm_num))
theorem R43537 : Reach 43537 := rs (se 2 (by rfl) ⟨16326, by rfl⟩) (B 32653 (by norm_num) ⟨16326, by rfl⟩ (by norm_num))
theorem R43541 : Reach 43541 := rs (se 6 (by rfl) ⟨1020, by rfl⟩) (B 2041 (by norm_num) ⟨1020, by rfl⟩ (by norm_num))
theorem R43545 : Reach 43545 := rs (se 2 (by rfl) ⟨16329, by rfl⟩) (B 32659 (by norm_num) ⟨16329, by rfl⟩ (by norm_num))
theorem R43549 : Reach 43549 := rs (se 3 (by rfl) ⟨8165, by rfl⟩) (B 16331 (by norm_num) ⟨8165, by rfl⟩ (by norm_num))
theorem R43553 : Reach 43553 := rs (se 2 (by rfl) ⟨16332, by rfl⟩) (B 32665 (by norm_num) ⟨16332, by rfl⟩ (by norm_num))
theorem R43557 : Reach 43557 := rs (se 4 (by rfl) ⟨4083, by rfl⟩) (B 8167 (by norm_num) ⟨4083, by rfl⟩ (by norm_num))
theorem R43561 : Reach 43561 := rs (se 2 (by rfl) ⟨16335, by rfl⟩) (B 32671 (by norm_num) ⟨16335, by rfl⟩ (by norm_num))
theorem R43565 : Reach 43565 := rs (se 3 (by rfl) ⟨8168, by rfl⟩) (B 16337 (by norm_num) ⟨8168, by rfl⟩ (by norm_num))
theorem R43569 : Reach 43569 := rs (se 2 (by rfl) ⟨16338, by rfl⟩) (B 32677 (by norm_num) ⟨16338, by rfl⟩ (by norm_num))
theorem R43573 : Reach 43573 := rs (se 5 (by rfl) ⟨2042, by rfl⟩) (B 4085 (by norm_num) ⟨2042, by rfl⟩ (by norm_num))
theorem R43577 : Reach 43577 := rs (se 2 (by rfl) ⟨16341, by rfl⟩) (B 32683 (by norm_num) ⟨16341, by rfl⟩ (by norm_num))
theorem R43581 : Reach 43581 := rs (se 3 (by rfl) ⟨8171, by rfl⟩) (B 16343 (by norm_num) ⟨8171, by rfl⟩ (by norm_num))
theorem R76349 : Reach 76349 := rs (se 3 (by rfl) ⟨14315, by rfl⟩) (B 28631 (by norm_num) ⟨14315, by rfl⟩ (by norm_num))
theorem R43585 : Reach 43585 := rs (se 2 (by rfl) ⟨16344, by rfl⟩) (B 32689 (by norm_num) ⟨16344, by rfl⟩ (by norm_num))
theorem R43589 : Reach 43589 := rs (se 4 (by rfl) ⟨4086, by rfl⟩) (B 8173 (by norm_num) ⟨4086, by rfl⟩ (by norm_num))
theorem R43593 : Reach 43593 := rs (se 2 (by rfl) ⟨16347, by rfl⟩) (B 32695 (by norm_num) ⟨16347, by rfl⟩ (by norm_num))
theorem R43597 : Reach 43597 := rs (se 3 (by rfl) ⟨8174, by rfl⟩) (B 16349 (by norm_num) ⟨8174, by rfl⟩ (by norm_num))
theorem R43601 : Reach 43601 := rs (se 2 (by rfl) ⟨16350, by rfl⟩) (B 32701 (by norm_num) ⟨16350, by rfl⟩ (by norm_num))
theorem R43605 : Reach 43605 := rs (se 8 (by rfl) ⟨255, by rfl⟩) (B 511 (by norm_num) ⟨255, by rfl⟩ (by norm_num))
theorem R43609 : Reach 43609 := rs (se 2 (by rfl) ⟨16353, by rfl⟩) (B 32707 (by norm_num) ⟨16353, by rfl⟩ (by norm_num))
theorem R43613 : Reach 43613 := rs (se 3 (by rfl) ⟨8177, by rfl⟩) (B 16355 (by norm_num) ⟨8177, by rfl⟩ (by norm_num))
theorem R43617 : Reach 43617 := rs (se 2 (by rfl) ⟨16356, by rfl⟩) (B 32713 (by norm_num) ⟨16356, by rfl⟩ (by norm_num))
theorem R43621 : Reach 43621 := rs (se 4 (by rfl) ⟨4089, by rfl⟩) (B 8179 (by norm_num) ⟨4089, by rfl⟩ (by norm_num))
theorem R43625 : Reach 43625 := rs (se 2 (by rfl) ⟨16359, by rfl⟩) (B 32719 (by norm_num) ⟨16359, by rfl⟩ (by norm_num))
theorem R43629 : Reach 43629 := rs (se 3 (by rfl) ⟨8180, by rfl⟩) (B 16361 (by norm_num) ⟨8180, by rfl⟩ (by norm_num))
theorem R43633 : Reach 43633 := rs (se 2 (by rfl) ⟨16362, by rfl⟩) (B 32725 (by norm_num) ⟨16362, by rfl⟩ (by norm_num))
theorem R43637 : Reach 43637 := rs (se 5 (by rfl) ⟨2045, by rfl⟩) (B 4091 (by norm_num) ⟨2045, by rfl⟩ (by norm_num))
theorem R43641 : Reach 43641 := rs (se 2 (by rfl) ⟨16365, by rfl⟩) (B 32731 (by norm_num) ⟨16365, by rfl⟩ (by norm_num))
theorem R43645 : Reach 43645 := rs (se 3 (by rfl) ⟨8183, by rfl⟩) (B 16367 (by norm_num) ⟨8183, by rfl⟩ (by norm_num))
theorem R43649 : Reach 43649 := rs (se 2 (by rfl) ⟨16368, by rfl⟩) (B 32737 (by norm_num) ⟨16368, by rfl⟩ (by norm_num))
theorem R43653 : Reach 43653 := rs (se 4 (by rfl) ⟨4092, by rfl⟩) (B 8185 (by norm_num) ⟨4092, by rfl⟩ (by norm_num))
theorem R43657 : Reach 43657 := rs (se 2 (by rfl) ⟨16371, by rfl⟩) (B 32743 (by norm_num) ⟨16371, by rfl⟩ (by norm_num))
theorem R43661 : Reach 43661 := rs (se 3 (by rfl) ⟨8186, by rfl⟩) (B 16373 (by norm_num) ⟨8186, by rfl⟩ (by norm_num))
theorem R43665 : Reach 43665 := rs (se 2 (by rfl) ⟨16374, by rfl⟩) (B 32749 (by norm_num) ⟨16374, by rfl⟩ (by norm_num))
theorem R43669 : Reach 43669 := rs (se 6 (by rfl) ⟨1023, by rfl⟩) (B 2047 (by norm_num) ⟨1023, by rfl⟩ (by norm_num))
theorem R43673 : Reach 43673 := rs (se 2 (by rfl) ⟨16377, by rfl⟩) (B 32755 (by norm_num) ⟨16377, by rfl⟩ (by norm_num))
theorem R43677 : Reach 43677 := rs (se 3 (by rfl) ⟨8189, by rfl⟩) (B 16379 (by norm_num) ⟨8189, by rfl⟩ (by norm_num))
theorem R43681 : Reach 43681 := rs (se 2 (by rfl) ⟨16380, by rfl⟩) (B 32761 (by norm_num) ⟨16380, by rfl⟩ (by norm_num))
theorem R43685 : Reach 43685 := rs (se 4 (by rfl) ⟨4095, by rfl⟩) (B 8191 (by norm_num) ⟨4095, by rfl⟩ (by norm_num))
theorem R43689 : Reach 43689 := rs (se 2 (by rfl) ⟨16383, by rfl⟩) (B 32767 (by norm_num) ⟨16383, by rfl⟩ (by norm_num))
theorem R43693 : Reach 43693 := rs (se 3 (by rfl) ⟨8192, by rfl⟩) (B 16385 (by norm_num) ⟨8192, by rfl⟩ (by norm_num))
theorem R43697 : Reach 43697 := rs (se 2 (by rfl) ⟨16386, by rfl⟩) (B 32773 (by norm_num) ⟨16386, by rfl⟩ (by norm_num))
theorem R43701 : Reach 43701 := rs (se 5 (by rfl) ⟨2048, by rfl⟩) (B 4097 (by norm_num) ⟨2048, by rfl⟩ (by norm_num))
theorem R43705 : Reach 43705 := rs (se 2 (by rfl) ⟨16389, by rfl⟩) (B 32779 (by norm_num) ⟨16389, by rfl⟩ (by norm_num))
theorem R43709 : Reach 43709 := rs (se 3 (by rfl) ⟨8195, by rfl⟩) (B 16391 (by norm_num) ⟨8195, by rfl⟩ (by norm_num))
theorem R76477 : Reach 76477 := rs (se 3 (by rfl) ⟨14339, by rfl⟩) (B 28679 (by norm_num) ⟨14339, by rfl⟩ (by norm_num))
theorem R43713 : Reach 43713 := rs (se 2 (by rfl) ⟨16392, by rfl⟩) (B 32785 (by norm_num) ⟨16392, by rfl⟩ (by norm_num))
theorem R43717 : Reach 43717 := rs (se 4 (by rfl) ⟨4098, by rfl⟩) (B 8197 (by norm_num) ⟨4098, by rfl⟩ (by norm_num))
theorem R43721 : Reach 43721 := rs (se 2 (by rfl) ⟨16395, by rfl⟩) (B 32791 (by norm_num) ⟨16395, by rfl⟩ (by norm_num))
theorem R43725 : Reach 43725 := rs (se 3 (by rfl) ⟨8198, by rfl⟩) (B 16397 (by norm_num) ⟨8198, by rfl⟩ (by norm_num))
theorem R43729 : Reach 43729 := rs (se 2 (by rfl) ⟨16398, by rfl⟩) (B 32797 (by norm_num) ⟨16398, by rfl⟩ (by norm_num))
theorem R43733 : Reach 43733 := rs (se 7 (by rfl) ⟨512, by rfl⟩) (B 1025 (by norm_num) ⟨512, by rfl⟩ (by norm_num))
theorem R142037 : Reach 142037 := rs (se 7 (by rfl) ⟨1664, by rfl⟩) (B 3329 (by norm_num) ⟨1664, by rfl⟩ (by norm_num))
theorem R43737 : Reach 43737 := rs (se 2 (by rfl) ⟨16401, by rfl⟩) (B 32803 (by norm_num) ⟨16401, by rfl⟩ (by norm_num))
theorem R43741 : Reach 43741 := rs (se 3 (by rfl) ⟨8201, by rfl⟩) (B 16403 (by norm_num) ⟨8201, by rfl⟩ (by norm_num))
theorem R43745 : Reach 43745 := rs (se 2 (by rfl) ⟨16404, by rfl⟩) (B 32809 (by norm_num) ⟨16404, by rfl⟩ (by norm_num))
theorem R43749 : Reach 43749 := rs (se 4 (by rfl) ⟨4101, by rfl⟩) (B 8203 (by norm_num) ⟨4101, by rfl⟩ (by norm_num))
theorem R43753 : Reach 43753 := rs (se 2 (by rfl) ⟨16407, by rfl⟩) (B 32815 (by norm_num) ⟨16407, by rfl⟩ (by norm_num))
theorem R43757 : Reach 43757 := rs (se 3 (by rfl) ⟨8204, by rfl⟩) (B 16409 (by norm_num) ⟨8204, by rfl⟩ (by norm_num))
theorem R43761 : Reach 43761 := rs (se 2 (by rfl) ⟨16410, by rfl⟩) (B 32821 (by norm_num) ⟨16410, by rfl⟩ (by norm_num))
theorem R43765 : Reach 43765 := rs (se 5 (by rfl) ⟨2051, by rfl⟩) (B 4103 (by norm_num) ⟨2051, by rfl⟩ (by norm_num))
theorem R43769 : Reach 43769 := rs (se 2 (by rfl) ⟨16413, by rfl⟩) (B 32827 (by norm_num) ⟨16413, by rfl⟩ (by norm_num))
theorem R109309 : Reach 109309 := rs (se 3 (by rfl) ⟨20495, by rfl⟩) (B 40991 (by norm_num) ⟨20495, by rfl⟩ (by norm_num))
theorem R43773 : Reach 43773 := rs (se 3 (by rfl) ⟨8207, by rfl⟩) (B 16415 (by norm_num) ⟨8207, by rfl⟩ (by norm_num))
theorem R43777 : Reach 43777 := rs (se 2 (by rfl) ⟨16416, by rfl⟩) (B 32833 (by norm_num) ⟨16416, by rfl⟩ (by norm_num))
theorem R43781 : Reach 43781 := rs (se 4 (by rfl) ⟨4104, by rfl⟩) (B 8209 (by norm_num) ⟨4104, by rfl⟩ (by norm_num))
theorem R43785 : Reach 43785 := rs (se 2 (by rfl) ⟨16419, by rfl⟩) (B 32839 (by norm_num) ⟨16419, by rfl⟩ (by norm_num))
theorem R43789 : Reach 43789 := rs (se 3 (by rfl) ⟨8210, by rfl⟩) (B 16421 (by norm_num) ⟨8210, by rfl⟩ (by norm_num))
theorem R43793 : Reach 43793 := rs (se 2 (by rfl) ⟨16422, by rfl⟩) (B 32845 (by norm_num) ⟨16422, by rfl⟩ (by norm_num))
theorem R43797 : Reach 43797 := rs (se 6 (by rfl) ⟨1026, by rfl⟩) (B 2053 (by norm_num) ⟨1026, by rfl⟩ (by norm_num))
theorem R76565 : Reach 76565 := rs (se 6 (by rfl) ⟨1794, by rfl⟩) (B 3589 (by norm_num) ⟨1794, by rfl⟩ (by norm_num))
theorem R109333 : Reach 109333 := rs (se 6 (by rfl) ⟨2562, by rfl⟩) (B 5125 (by norm_num) ⟨2562, by rfl⟩ (by norm_num))
theorem R43801 : Reach 43801 := rs (se 2 (by rfl) ⟨16425, by rfl⟩) (B 32851 (by norm_num) ⟨16425, by rfl⟩ (by norm_num))
theorem R174869 : Reach 174869 := rs (se 6 (by rfl) ⟨4098, by rfl⟩) (B 8197 (by norm_num) ⟨4098, by rfl⟩ (by norm_num))
theorem R43805 : Reach 43805 := rs (se 3 (by rfl) ⟨8213, by rfl⟩) (B 16427 (by norm_num) ⟨8213, by rfl⟩ (by norm_num))
theorem R43809 : Reach 43809 := rs (se 2 (by rfl) ⟨16428, by rfl⟩) (B 32857 (by norm_num) ⟨16428, by rfl⟩ (by norm_num))
theorem R43813 : Reach 43813 := rs (se 4 (by rfl) ⟨4107, by rfl⟩) (B 8215 (by norm_num) ⟨4107, by rfl⟩ (by norm_num))
theorem R43817 : Reach 43817 := rs (se 2 (by rfl) ⟨16431, by rfl⟩) (B 32863 (by norm_num) ⟨16431, by rfl⟩ (by norm_num))
theorem R43821 : Reach 43821 := rs (se 3 (by rfl) ⟨8216, by rfl⟩) (B 16433 (by norm_num) ⟨8216, by rfl⟩ (by norm_num))
theorem R43825 : Reach 43825 := rs (se 2 (by rfl) ⟨16434, by rfl⟩) (B 32869 (by norm_num) ⟨16434, by rfl⟩ (by norm_num))
theorem R43829 : Reach 43829 := rs (se 5 (by rfl) ⟨2054, by rfl⟩) (B 4109 (by norm_num) ⟨2054, by rfl⟩ (by norm_num))
theorem R338741 : Reach 338741 := rs (se 5 (by rfl) ⟨15878, by rfl⟩) (B 31757 (by norm_num) ⟨15878, by rfl⟩ (by norm_num))
theorem R43833 : Reach 43833 := rs (se 2 (by rfl) ⟨16437, by rfl⟩) (B 32875 (by norm_num) ⟨16437, by rfl⟩ (by norm_num))
theorem R43837 : Reach 43837 := rs (se 3 (by rfl) ⟨8219, by rfl⟩) (B 16439 (by norm_num) ⟨8219, by rfl⟩ (by norm_num))
theorem R43841 : Reach 43841 := rs (se 2 (by rfl) ⟨16440, by rfl⟩) (B 32881 (by norm_num) ⟨16440, by rfl⟩ (by norm_num))
theorem R43845 : Reach 43845 := rs (se 4 (by rfl) ⟨4110, by rfl⟩) (B 8221 (by norm_num) ⟨4110, by rfl⟩ (by norm_num))
theorem R43849 : Reach 43849 := rs (se 2 (by rfl) ⟨16443, by rfl⟩) (B 32887 (by norm_num) ⟨16443, by rfl⟩ (by norm_num))
theorem R43853 : Reach 43853 := rs (se 3 (by rfl) ⟨8222, by rfl⟩) (B 16445 (by norm_num) ⟨8222, by rfl⟩ (by norm_num))
theorem R43857 : Reach 43857 := rs (se 2 (by rfl) ⟨16446, by rfl⟩) (B 32893 (by norm_num) ⟨16446, by rfl⟩ (by norm_num))
theorem R43861 : Reach 43861 := rs (se 9 (by rfl) ⟨128, by rfl⟩) (B 257 (by norm_num) ⟨128, by rfl⟩ (by norm_num))
theorem R43865 : Reach 43865 := rs (se 2 (by rfl) ⟨16449, by rfl⟩) (B 32899 (by norm_num) ⟨16449, by rfl⟩ (by norm_num))
theorem R43869 : Reach 43869 := rs (se 3 (by rfl) ⟨8225, by rfl⟩) (B 16451 (by norm_num) ⟨8225, by rfl⟩ (by norm_num))
theorem R43873 : Reach 43873 := rs (se 2 (by rfl) ⟨16452, by rfl⟩) (B 32905 (by norm_num) ⟨16452, by rfl⟩ (by norm_num))
theorem R43877 : Reach 43877 := rs (se 4 (by rfl) ⟨4113, by rfl⟩) (B 8227 (by norm_num) ⟨4113, by rfl⟩ (by norm_num))
theorem R43881 : Reach 43881 := rs (se 2 (by rfl) ⟨16455, by rfl⟩) (B 32911 (by norm_num) ⟨16455, by rfl⟩ (by norm_num))
theorem R109421 : Reach 109421 := rs (se 3 (by rfl) ⟨20516, by rfl⟩) (B 41033 (by norm_num) ⟨20516, by rfl⟩ (by norm_num))
theorem R43885 : Reach 43885 := rs (se 3 (by rfl) ⟨8228, by rfl⟩) (B 16457 (by norm_num) ⟨8228, by rfl⟩ (by norm_num))
theorem R43889 : Reach 43889 := rs (se 2 (by rfl) ⟨16458, by rfl⟩) (B 32917 (by norm_num) ⟨16458, by rfl⟩ (by norm_num))
theorem R43893 : Reach 43893 := rs (se 5 (by rfl) ⟨2057, by rfl⟩) (B 4115 (by norm_num) ⟨2057, by rfl⟩ (by norm_num))
theorem R43897 : Reach 43897 := rs (se 2 (by rfl) ⟨16461, by rfl⟩) (B 32923 (by norm_num) ⟨16461, by rfl⟩ (by norm_num))
theorem R43901 : Reach 43901 := rs (se 3 (by rfl) ⟨8231, by rfl⟩) (B 16463 (by norm_num) ⟨8231, by rfl⟩ (by norm_num))
theorem R43905 : Reach 43905 := rs (se 2 (by rfl) ⟨16464, by rfl⟩) (B 32929 (by norm_num) ⟨16464, by rfl⟩ (by norm_num))
theorem R43909 : Reach 43909 := rs (se 4 (by rfl) ⟨4116, by rfl⟩) (B 8233 (by norm_num) ⟨4116, by rfl⟩ (by norm_num))
theorem R43913 : Reach 43913 := rs (se 2 (by rfl) ⟨16467, by rfl⟩) (B 32935 (by norm_num) ⟨16467, by rfl⟩ (by norm_num))
theorem R43917 : Reach 43917 := rs (se 3 (by rfl) ⟨8234, by rfl⟩) (B 16469 (by norm_num) ⟨8234, by rfl⟩ (by norm_num))
theorem R43921 : Reach 43921 := rs (se 2 (by rfl) ⟨16470, by rfl⟩) (B 32941 (by norm_num) ⟨16470, by rfl⟩ (by norm_num))
theorem R76693 : Reach 76693 := rs (se 6 (by rfl) ⟨1797, by rfl⟩) (B 3595 (by norm_num) ⟨1797, by rfl⟩ (by norm_num))
theorem R43925 : Reach 43925 := rs (se 6 (by rfl) ⟨1029, by rfl⟩) (B 2059 (by norm_num) ⟨1029, by rfl⟩ (by norm_num))
theorem R43929 : Reach 43929 := rs (se 2 (by rfl) ⟨16473, by rfl⟩) (B 32947 (by norm_num) ⟨16473, by rfl⟩ (by norm_num))
theorem R43933 : Reach 43933 := rs (se 3 (by rfl) ⟨8237, by rfl⟩) (B 16475 (by norm_num) ⟨8237, by rfl⟩ (by norm_num))
theorem R43937 : Reach 43937 := rs (se 2 (by rfl) ⟨16476, by rfl⟩) (B 32953 (by norm_num) ⟨16476, by rfl⟩ (by norm_num))
theorem R43941 : Reach 43941 := rs (se 4 (by rfl) ⟨4119, by rfl⟩) (B 8239 (by norm_num) ⟨4119, by rfl⟩ (by norm_num))
theorem R43945 : Reach 43945 := rs (se 2 (by rfl) ⟨16479, by rfl⟩) (B 32959 (by norm_num) ⟨16479, by rfl⟩ (by norm_num))
theorem R43949 : Reach 43949 := rs (se 3 (by rfl) ⟨8240, by rfl⟩) (B 16481 (by norm_num) ⟨8240, by rfl⟩ (by norm_num))
theorem R43953 : Reach 43953 := rs (se 2 (by rfl) ⟨16482, by rfl⟩) (B 32965 (by norm_num) ⟨16482, by rfl⟩ (by norm_num))
theorem R43957 : Reach 43957 := rs (se 5 (by rfl) ⟨2060, by rfl⟩) (B 4121 (by norm_num) ⟨2060, by rfl⟩ (by norm_num))
theorem R43961 : Reach 43961 := rs (se 2 (by rfl) ⟨16485, by rfl⟩) (B 32971 (by norm_num) ⟨16485, by rfl⟩ (by norm_num))
theorem R43965 : Reach 43965 := rs (se 3 (by rfl) ⟨8243, by rfl⟩) (B 16487 (by norm_num) ⟨8243, by rfl⟩ (by norm_num))
theorem R43969 : Reach 43969 := rs (se 2 (by rfl) ⟨16488, by rfl⟩) (B 32977 (by norm_num) ⟨16488, by rfl⟩ (by norm_num))
theorem R43973 : Reach 43973 := rs (se 4 (by rfl) ⟨4122, by rfl⟩) (B 8245 (by norm_num) ⟨4122, by rfl⟩ (by norm_num))
theorem R43977 : Reach 43977 := rs (se 2 (by rfl) ⟨16491, by rfl⟩) (B 32983 (by norm_num) ⟨16491, by rfl⟩ (by norm_num))
theorem R43981 : Reach 43981 := rs (se 3 (by rfl) ⟨8246, by rfl⟩) (B 16493 (by norm_num) ⟨8246, by rfl⟩ (by norm_num))
theorem R43985 : Reach 43985 := rs (se 2 (by rfl) ⟨16494, by rfl⟩) (B 32989 (by norm_num) ⟨16494, by rfl⟩ (by norm_num))
theorem R43989 : Reach 43989 := rs (se 7 (by rfl) ⟨515, by rfl⟩) (B 1031 (by norm_num) ⟨515, by rfl⟩ (by norm_num))
theorem R43993 : Reach 43993 := rs (se 2 (by rfl) ⟨16497, by rfl⟩) (B 32995 (by norm_num) ⟨16497, by rfl⟩ (by norm_num))
theorem R43997 : Reach 43997 := rs (se 3 (by rfl) ⟨8249, by rfl⟩) (B 16499 (by norm_num) ⟨8249, by rfl⟩ (by norm_num))
theorem R44001 : Reach 44001 := rs (se 2 (by rfl) ⟨16500, by rfl⟩) (B 33001 (by norm_num) ⟨16500, by rfl⟩ (by norm_num))
theorem R44005 : Reach 44005 := rs (se 4 (by rfl) ⟨4125, by rfl⟩) (B 8251 (by norm_num) ⟨4125, by rfl⟩ (by norm_num))
theorem R44009 : Reach 44009 := rs (se 2 (by rfl) ⟨16503, by rfl⟩) (B 33007 (by norm_num) ⟨16503, by rfl⟩ (by norm_num))
theorem R44013 : Reach 44013 := rs (se 3 (by rfl) ⟨8252, by rfl⟩) (B 16505 (by norm_num) ⟨8252, by rfl⟩ (by norm_num))
theorem R76781 : Reach 76781 := rs (se 3 (by rfl) ⟨14396, by rfl⟩) (B 28793 (by norm_num) ⟨14396, by rfl⟩ (by norm_num))
theorem R44017 : Reach 44017 := rs (se 2 (by rfl) ⟨16506, by rfl⟩) (B 33013 (by norm_num) ⟨16506, by rfl⟩ (by norm_num))
theorem R44021 : Reach 44021 := rs (se 5 (by rfl) ⟨2063, by rfl⟩) (B 4127 (by norm_num) ⟨2063, by rfl⟩ (by norm_num))
theorem R44025 : Reach 44025 := rs (se 2 (by rfl) ⟨16509, by rfl⟩) (B 33019 (by norm_num) ⟨16509, by rfl⟩ (by norm_num))
theorem R44029 : Reach 44029 := rs (se 3 (by rfl) ⟨8255, by rfl⟩) (B 16511 (by norm_num) ⟨8255, by rfl⟩ (by norm_num))
theorem R109565 : Reach 109565 := rs (se 3 (by rfl) ⟨20543, by rfl⟩) (B 41087 (by norm_num) ⟨20543, by rfl⟩ (by norm_num))
theorem R44033 : Reach 44033 := rs (se 2 (by rfl) ⟨16512, by rfl⟩) (B 33025 (by norm_num) ⟨16512, by rfl⟩ (by norm_num))
theorem R44037 : Reach 44037 := rs (se 4 (by rfl) ⟨4128, by rfl⟩) (B 8257 (by norm_num) ⟨4128, by rfl⟩ (by norm_num))
theorem R44041 : Reach 44041 := rs (se 2 (by rfl) ⟨16515, by rfl⟩) (B 33031 (by norm_num) ⟨16515, by rfl⟩ (by norm_num))
theorem R44045 : Reach 44045 := rs (se 3 (by rfl) ⟨8258, by rfl⟩) (B 16517 (by norm_num) ⟨8258, by rfl⟩ (by norm_num))
theorem R44049 : Reach 44049 := rs (se 2 (by rfl) ⟨16518, by rfl⟩) (B 33037 (by norm_num) ⟨16518, by rfl⟩ (by norm_num))
theorem R44053 : Reach 44053 := rs (se 6 (by rfl) ⟨1032, by rfl⟩) (B 2065 (by norm_num) ⟨1032, by rfl⟩ (by norm_num))
theorem R44057 : Reach 44057 := rs (se 2 (by rfl) ⟨16521, by rfl⟩) (B 33043 (by norm_num) ⟨16521, by rfl⟩ (by norm_num))
theorem R44061 : Reach 44061 := rs (se 3 (by rfl) ⟨8261, by rfl⟩) (B 16523 (by norm_num) ⟨8261, by rfl⟩ (by norm_num))
theorem R44065 : Reach 44065 := rs (se 2 (by rfl) ⟨16524, by rfl⟩) (B 33049 (by norm_num) ⟨16524, by rfl⟩ (by norm_num))
theorem R44069 : Reach 44069 := rs (se 4 (by rfl) ⟨4131, by rfl⟩) (B 8263 (by norm_num) ⟨4131, by rfl⟩ (by norm_num))
theorem R44073 : Reach 44073 := rs (se 2 (by rfl) ⟨16527, by rfl⟩) (B 33055 (by norm_num) ⟨16527, by rfl⟩ (by norm_num))
theorem R109613 : Reach 109613 := rs (se 3 (by rfl) ⟨20552, by rfl⟩) (B 41105 (by norm_num) ⟨20552, by rfl⟩ (by norm_num))
theorem R44077 : Reach 44077 := rs (se 3 (by rfl) ⟨8264, by rfl⟩) (B 16529 (by norm_num) ⟨8264, by rfl⟩ (by norm_num))
theorem R44081 : Reach 44081 := rs (se 2 (by rfl) ⟨16530, by rfl⟩) (B 33061 (by norm_num) ⟨16530, by rfl⟩ (by norm_num))
theorem R44085 : Reach 44085 := rs (se 5 (by rfl) ⟨2066, by rfl⟩) (B 4133 (by norm_num) ⟨2066, by rfl⟩ (by norm_num))
theorem R44089 : Reach 44089 := rs (se 2 (by rfl) ⟨16533, by rfl⟩) (B 33067 (by norm_num) ⟨16533, by rfl⟩ (by norm_num))
theorem R44093 : Reach 44093 := rs (se 3 (by rfl) ⟨8267, by rfl⟩) (B 16535 (by norm_num) ⟨8267, by rfl⟩ (by norm_num))
theorem R44097 : Reach 44097 := rs (se 2 (by rfl) ⟨16536, by rfl⟩) (B 33073 (by norm_num) ⟨16536, by rfl⟩ (by norm_num))
theorem R44101 : Reach 44101 := rs (se 4 (by rfl) ⟨4134, by rfl⟩) (B 8269 (by norm_num) ⟨4134, by rfl⟩ (by norm_num))
theorem R44105 : Reach 44105 := rs (se 2 (by rfl) ⟨16539, by rfl⟩) (B 33079 (by norm_num) ⟨16539, by rfl⟩ (by norm_num))
theorem R44109 : Reach 44109 := rs (se 3 (by rfl) ⟨8270, by rfl⟩) (B 16541 (by norm_num) ⟨8270, by rfl⟩ (by norm_num))
theorem R44113 : Reach 44113 := rs (se 2 (by rfl) ⟨16542, by rfl⟩) (B 33085 (by norm_num) ⟨16542, by rfl⟩ (by norm_num))
theorem R44117 : Reach 44117 := rs (se 8 (by rfl) ⟨258, by rfl⟩) (B 517 (by norm_num) ⟨258, by rfl⟩ (by norm_num))
theorem R240725 : Reach 240725 := rs (se 8 (by rfl) ⟨1410, by rfl⟩) (B 2821 (by norm_num) ⟨1410, by rfl⟩ (by norm_num))
theorem R44121 : Reach 44121 := rs (se 2 (by rfl) ⟨16545, by rfl⟩) (B 33091 (by norm_num) ⟨16545, by rfl⟩ (by norm_num))
theorem R44125 : Reach 44125 := rs (se 3 (by rfl) ⟨8273, by rfl⟩) (B 16547 (by norm_num) ⟨8273, by rfl⟩ (by norm_num))
theorem R44129 : Reach 44129 := rs (se 2 (by rfl) ⟨16548, by rfl⟩) (B 33097 (by norm_num) ⟨16548, by rfl⟩ (by norm_num))
theorem R44133 : Reach 44133 := rs (se 4 (by rfl) ⟨4137, by rfl⟩) (B 8275 (by norm_num) ⟨4137, by rfl⟩ (by norm_num))
theorem R44137 : Reach 44137 := rs (se 2 (by rfl) ⟨16551, by rfl⟩) (B 33103 (by norm_num) ⟨16551, by rfl⟩ (by norm_num))
theorem R44141 : Reach 44141 := rs (se 3 (by rfl) ⟨8276, by rfl⟩) (B 16553 (by norm_num) ⟨8276, by rfl⟩ (by norm_num))
theorem R76909 : Reach 76909 := rs (se 3 (by rfl) ⟨14420, by rfl⟩) (B 28841 (by norm_num) ⟨14420, by rfl⟩ (by norm_num))
theorem R44145 : Reach 44145 := rs (se 2 (by rfl) ⟨16554, by rfl⟩) (B 33109 (by norm_num) ⟨16554, by rfl⟩ (by norm_num))
theorem R44149 : Reach 44149 := rs (se 5 (by rfl) ⟨2069, by rfl⟩) (B 4139 (by norm_num) ⟨2069, by rfl⟩ (by norm_num))
theorem R44153 : Reach 44153 := rs (se 2 (by rfl) ⟨16557, by rfl⟩) (B 33115 (by norm_num) ⟨16557, by rfl⟩ (by norm_num))
theorem R44157 : Reach 44157 := rs (se 3 (by rfl) ⟨8279, by rfl⟩) (B 16559 (by norm_num) ⟨8279, by rfl⟩ (by norm_num))
theorem R44161 : Reach 44161 := rs (se 2 (by rfl) ⟨16560, by rfl⟩) (B 33121 (by norm_num) ⟨16560, by rfl⟩ (by norm_num))
theorem R44165 : Reach 44165 := rs (se 4 (by rfl) ⟨4140, by rfl⟩) (B 8281 (by norm_num) ⟨4140, by rfl⟩ (by norm_num))
theorem R44169 : Reach 44169 := rs (se 2 (by rfl) ⟨16563, by rfl⟩) (B 33127 (by norm_num) ⟨16563, by rfl⟩ (by norm_num))
theorem R44173 : Reach 44173 := rs (se 3 (by rfl) ⟨8282, by rfl⟩) (B 16565 (by norm_num) ⟨8282, by rfl⟩ (by norm_num))
theorem R44177 : Reach 44177 := rs (se 2 (by rfl) ⟨16566, by rfl⟩) (B 33133 (by norm_num) ⟨16566, by rfl⟩ (by norm_num))
theorem R44181 : Reach 44181 := rs (se 6 (by rfl) ⟨1035, by rfl⟩) (B 2071 (by norm_num) ⟨1035, by rfl⟩ (by norm_num))
theorem R44185 : Reach 44185 := rs (se 2 (by rfl) ⟨16569, by rfl⟩) (B 33139 (by norm_num) ⟨16569, by rfl⟩ (by norm_num))
theorem R44189 : Reach 44189 := rs (se 3 (by rfl) ⟨8285, by rfl⟩) (B 16571 (by norm_num) ⟨8285, by rfl⟩ (by norm_num))
theorem R44193 : Reach 44193 := rs (se 2 (by rfl) ⟨16572, by rfl⟩) (B 33145 (by norm_num) ⟨16572, by rfl⟩ (by norm_num))
theorem R44197 : Reach 44197 := rs (se 4 (by rfl) ⟨4143, by rfl⟩) (B 8287 (by norm_num) ⟨4143, by rfl⟩ (by norm_num))
theorem R44201 : Reach 44201 := rs (se 2 (by rfl) ⟨16575, by rfl⟩) (B 33151 (by norm_num) ⟨16575, by rfl⟩ (by norm_num))
theorem R44205 : Reach 44205 := rs (se 3 (by rfl) ⟨8288, by rfl⟩) (B 16577 (by norm_num) ⟨8288, by rfl⟩ (by norm_num))
theorem R44209 : Reach 44209 := rs (se 2 (by rfl) ⟨16578, by rfl⟩) (B 33157 (by norm_num) ⟨16578, by rfl⟩ (by norm_num))
theorem R44213 : Reach 44213 := rs (se 5 (by rfl) ⟨2072, by rfl⟩) (B 4145 (by norm_num) ⟨2072, by rfl⟩ (by norm_num))
theorem R44217 : Reach 44217 := rs (se 2 (by rfl) ⟨16581, by rfl⟩) (B 33163 (by norm_num) ⟨16581, by rfl⟩ (by norm_num))
theorem R44221 : Reach 44221 := rs (se 3 (by rfl) ⟨8291, by rfl⟩) (B 16583 (by norm_num) ⟨8291, by rfl⟩ (by norm_num))
theorem R109757 : Reach 109757 := rs (se 3 (by rfl) ⟨20579, by rfl⟩) (B 41159 (by norm_num) ⟨20579, by rfl⟩ (by norm_num))
theorem R44225 : Reach 44225 := rs (se 2 (by rfl) ⟨16584, by rfl⟩) (B 33169 (by norm_num) ⟨16584, by rfl⟩ (by norm_num))
theorem R44229 : Reach 44229 := rs (se 4 (by rfl) ⟨4146, by rfl⟩) (B 8293 (by norm_num) ⟨4146, by rfl⟩ (by norm_num))
theorem R76997 : Reach 76997 := rs (se 4 (by rfl) ⟨7218, by rfl⟩) (B 14437 (by norm_num) ⟨7218, by rfl⟩ (by norm_num))
theorem R44233 : Reach 44233 := rs (se 2 (by rfl) ⟨16587, by rfl⟩) (B 33175 (by norm_num) ⟨16587, by rfl⟩ (by norm_num))
theorem R44237 : Reach 44237 := rs (se 3 (by rfl) ⟨8294, by rfl⟩) (B 16589 (by norm_num) ⟨8294, by rfl⟩ (by norm_num))
theorem R44241 : Reach 44241 := rs (se 2 (by rfl) ⟨16590, by rfl⟩) (B 33181 (by norm_num) ⟨16590, by rfl⟩ (by norm_num))
theorem R44245 : Reach 44245 := rs (se 7 (by rfl) ⟨518, by rfl⟩) (B 1037 (by norm_num) ⟨518, by rfl⟩ (by norm_num))
theorem R44249 : Reach 44249 := rs (se 2 (by rfl) ⟨16593, by rfl⟩) (B 33187 (by norm_num) ⟨16593, by rfl⟩ (by norm_num))
theorem R44253 : Reach 44253 := rs (se 3 (by rfl) ⟨8297, by rfl⟩) (B 16595 (by norm_num) ⟨8297, by rfl⟩ (by norm_num))
theorem R44257 : Reach 44257 := rs (se 2 (by rfl) ⟨16596, by rfl⟩) (B 33193 (by norm_num) ⟨16596, by rfl⟩ (by norm_num))
theorem R44261 : Reach 44261 := rs (se 4 (by rfl) ⟨4149, by rfl⟩) (B 8299 (by norm_num) ⟨4149, by rfl⟩ (by norm_num))
theorem R44265 : Reach 44265 := rs (se 2 (by rfl) ⟨16599, by rfl⟩) (B 33199 (by norm_num) ⟨16599, by rfl⟩ (by norm_num))
theorem R44269 : Reach 44269 := rs (se 3 (by rfl) ⟨8300, by rfl⟩) (B 16601 (by norm_num) ⟨8300, by rfl⟩ (by norm_num))
theorem R44273 : Reach 44273 := rs (se 2 (by rfl) ⟨16602, by rfl⟩) (B 33205 (by norm_num) ⟨16602, by rfl⟩ (by norm_num))
theorem R44277 : Reach 44277 := rs (se 5 (by rfl) ⟨2075, by rfl⟩) (B 4151 (by norm_num) ⟨2075, by rfl⟩ (by norm_num))
theorem R44281 : Reach 44281 := rs (se 2 (by rfl) ⟨16605, by rfl⟩) (B 33211 (by norm_num) ⟨16605, by rfl⟩ (by norm_num))
theorem R44285 : Reach 44285 := rs (se 3 (by rfl) ⟨8303, by rfl⟩) (B 16607 (by norm_num) ⟨8303, by rfl⟩ (by norm_num))
theorem R44289 : Reach 44289 := rs (se 2 (by rfl) ⟨16608, by rfl⟩) (B 33217 (by norm_num) ⟨16608, by rfl⟩ (by norm_num))
theorem R44293 : Reach 44293 := rs (se 4 (by rfl) ⟨4152, by rfl⟩) (B 8305 (by norm_num) ⟨4152, by rfl⟩ (by norm_num))
theorem R44297 : Reach 44297 := rs (se 2 (by rfl) ⟨16611, by rfl⟩) (B 33223 (by norm_num) ⟨16611, by rfl⟩ (by norm_num))
theorem R44301 : Reach 44301 := rs (se 3 (by rfl) ⟨8306, by rfl⟩) (B 16613 (by norm_num) ⟨8306, by rfl⟩ (by norm_num))
theorem R44305 : Reach 44305 := rs (se 2 (by rfl) ⟨16614, by rfl⟩) (B 33229 (by norm_num) ⟨16614, by rfl⟩ (by norm_num))
theorem R44309 : Reach 44309 := rs (se 6 (by rfl) ⟨1038, by rfl⟩) (B 2077 (by norm_num) ⟨1038, by rfl⟩ (by norm_num))
theorem R44313 : Reach 44313 := rs (se 2 (by rfl) ⟨16617, by rfl⟩) (B 33235 (by norm_num) ⟨16617, by rfl⟩ (by norm_num))
theorem R44317 : Reach 44317 := rs (se 3 (by rfl) ⟨8309, by rfl⟩) (B 16619 (by norm_num) ⟨8309, by rfl⟩ (by norm_num))
theorem R44321 : Reach 44321 := rs (se 2 (by rfl) ⟨16620, by rfl⟩) (B 33241 (by norm_num) ⟨16620, by rfl⟩ (by norm_num))
theorem R44325 : Reach 44325 := rs (se 4 (by rfl) ⟨4155, by rfl⟩) (B 8311 (by norm_num) ⟨4155, by rfl⟩ (by norm_num))
theorem R44329 : Reach 44329 := rs (se 2 (by rfl) ⟨16623, by rfl⟩) (B 33247 (by norm_num) ⟨16623, by rfl⟩ (by norm_num))
theorem R44333 : Reach 44333 := rs (se 3 (by rfl) ⟨8312, by rfl⟩) (B 16625 (by norm_num) ⟨8312, by rfl⟩ (by norm_num))
theorem R44337 : Reach 44337 := rs (se 2 (by rfl) ⟨16626, by rfl⟩) (B 33253 (by norm_num) ⟨16626, by rfl⟩ (by norm_num))
theorem R44341 : Reach 44341 := rs (se 5 (by rfl) ⟨2078, by rfl⟩) (B 4157 (by norm_num) ⟨2078, by rfl⟩ (by norm_num))
theorem R44345 : Reach 44345 := rs (se 2 (by rfl) ⟨16629, by rfl⟩) (B 33259 (by norm_num) ⟨16629, by rfl⟩ (by norm_num))
theorem R44349 : Reach 44349 := rs (se 3 (by rfl) ⟨8315, by rfl⟩) (B 16631 (by norm_num) ⟨8315, by rfl⟩ (by norm_num))
theorem R44353 : Reach 44353 := rs (se 2 (by rfl) ⟨16632, by rfl⟩) (B 33265 (by norm_num) ⟨16632, by rfl⟩ (by norm_num))
theorem R44357 : Reach 44357 := rs (se 4 (by rfl) ⟨4158, by rfl⟩) (B 8317 (by norm_num) ⟨4158, by rfl⟩ (by norm_num))
theorem R77125 : Reach 77125 := rs (se 4 (by rfl) ⟨7230, by rfl⟩) (B 14461 (by norm_num) ⟨7230, by rfl⟩ (by norm_num))
theorem R44361 : Reach 44361 := rs (se 2 (by rfl) ⟨16635, by rfl⟩) (B 33271 (by norm_num) ⟨16635, by rfl⟩ (by norm_num))
theorem R44365 : Reach 44365 := rs (se 3 (by rfl) ⟨8318, by rfl⟩) (B 16637 (by norm_num) ⟨8318, by rfl⟩ (by norm_num))
theorem R44369 : Reach 44369 := rs (se 2 (by rfl) ⟨16638, by rfl⟩) (B 33277 (by norm_num) ⟨16638, by rfl⟩ (by norm_num))
theorem R44373 : Reach 44373 := rs (se 11 (by rfl) ⟨32, by rfl⟩) (B 65 (by norm_num) ⟨32, by rfl⟩ (by norm_num))
theorem R44377 : Reach 44377 := rs (se 2 (by rfl) ⟨16641, by rfl⟩) (B 33283 (by norm_num) ⟨16641, by rfl⟩ (by norm_num))
theorem R44381 : Reach 44381 := rs (se 3 (by rfl) ⟨8321, by rfl⟩) (B 16643 (by norm_num) ⟨8321, by rfl⟩ (by norm_num))
theorem R44385 : Reach 44385 := rs (se 2 (by rfl) ⟨16644, by rfl⟩) (B 33289 (by norm_num) ⟨16644, by rfl⟩ (by norm_num))
theorem R44389 : Reach 44389 := rs (se 4 (by rfl) ⟨4161, by rfl⟩) (B 8323 (by norm_num) ⟨4161, by rfl⟩ (by norm_num))
theorem R44393 : Reach 44393 := rs (se 2 (by rfl) ⟨16647, by rfl⟩) (B 33295 (by norm_num) ⟨16647, by rfl⟩ (by norm_num))
theorem R44397 : Reach 44397 := rs (se 3 (by rfl) ⟨8324, by rfl⟩) (B 16649 (by norm_num) ⟨8324, by rfl⟩ (by norm_num))
theorem R44401 : Reach 44401 := rs (se 2 (by rfl) ⟨16650, by rfl⟩) (B 33301 (by norm_num) ⟨16650, by rfl⟩ (by norm_num))
theorem R44405 : Reach 44405 := rs (se 5 (by rfl) ⟨2081, by rfl⟩) (B 4163 (by norm_num) ⟨2081, by rfl⟩ (by norm_num))
theorem R44409 : Reach 44409 := rs (se 2 (by rfl) ⟨16653, by rfl⟩) (B 33307 (by norm_num) ⟨16653, by rfl⟩ (by norm_num))
theorem R44413 : Reach 44413 := rs (se 3 (by rfl) ⟨8327, by rfl⟩) (B 16655 (by norm_num) ⟨8327, by rfl⟩ (by norm_num))
theorem R44417 : Reach 44417 := rs (se 2 (by rfl) ⟨16656, by rfl⟩) (B 33313 (by norm_num) ⟨16656, by rfl⟩ (by norm_num))
theorem R109957 : Reach 109957 := rs (se 4 (by rfl) ⟨10308, by rfl⟩) (B 20617 (by norm_num) ⟨10308, by rfl⟩ (by norm_num))
theorem R44421 : Reach 44421 := rs (se 4 (by rfl) ⟨4164, by rfl⟩) (B 8329 (by norm_num) ⟨4164, by rfl⟩ (by norm_num))
theorem R44425 : Reach 44425 := rs (se 2 (by rfl) ⟨16659, by rfl⟩) (B 33319 (by norm_num) ⟨16659, by rfl⟩ (by norm_num))
theorem R44429 : Reach 44429 := rs (se 3 (by rfl) ⟨8330, by rfl⟩) (B 16661 (by norm_num) ⟨8330, by rfl⟩ (by norm_num))
theorem R44433 : Reach 44433 := rs (se 2 (by rfl) ⟨16662, by rfl⟩) (B 33325 (by norm_num) ⟨16662, by rfl⟩ (by norm_num))
theorem R44437 : Reach 44437 := rs (se 6 (by rfl) ⟨1041, by rfl⟩) (B 2083 (by norm_num) ⟨1041, by rfl⟩ (by norm_num))
theorem R44441 : Reach 44441 := rs (se 2 (by rfl) ⟨16665, by rfl⟩) (B 33331 (by norm_num) ⟨16665, by rfl⟩ (by norm_num))
theorem R44445 : Reach 44445 := rs (se 3 (by rfl) ⟨8333, by rfl⟩) (B 16667 (by norm_num) ⟨8333, by rfl⟩ (by norm_num))
theorem R77213 : Reach 77213 := rs (se 3 (by rfl) ⟨14477, by rfl⟩) (B 28955 (by norm_num) ⟨14477, by rfl⟩ (by norm_num))
theorem R44449 : Reach 44449 := rs (se 2 (by rfl) ⟨16668, by rfl⟩) (B 33337 (by norm_num) ⟨16668, by rfl⟩ (by norm_num))
theorem R44453 : Reach 44453 := rs (se 4 (by rfl) ⟨4167, by rfl⟩) (B 8335 (by norm_num) ⟨4167, by rfl⟩ (by norm_num))
theorem R44457 : Reach 44457 := rs (se 2 (by rfl) ⟨16671, by rfl⟩) (B 33343 (by norm_num) ⟨16671, by rfl⟩ (by norm_num))
theorem R44461 : Reach 44461 := rs (se 3 (by rfl) ⟨8336, by rfl⟩) (B 16673 (by norm_num) ⟨8336, by rfl⟩ (by norm_num))
theorem R44465 : Reach 44465 := rs (se 2 (by rfl) ⟨16674, by rfl⟩) (B 33349 (by norm_num) ⟨16674, by rfl⟩ (by norm_num))
theorem R44469 : Reach 44469 := rs (se 5 (by rfl) ⟨2084, by rfl⟩) (B 4169 (by norm_num) ⟨2084, by rfl⟩ (by norm_num))
theorem R44473 : Reach 44473 := rs (se 2 (by rfl) ⟨16677, by rfl⟩) (B 33355 (by norm_num) ⟨16677, by rfl⟩ (by norm_num))
theorem R44477 : Reach 44477 := rs (se 3 (by rfl) ⟨8339, by rfl⟩) (B 16679 (by norm_num) ⟨8339, by rfl⟩ (by norm_num))
theorem R44481 : Reach 44481 := rs (se 2 (by rfl) ⟨16680, by rfl⟩) (B 33361 (by norm_num) ⟨16680, by rfl⟩ (by norm_num))
theorem R44485 : Reach 44485 := rs (se 4 (by rfl) ⟨4170, by rfl⟩) (B 8341 (by norm_num) ⟨4170, by rfl⟩ (by norm_num))
theorem R44489 : Reach 44489 := rs (se 2 (by rfl) ⟨16683, by rfl⟩) (B 33367 (by norm_num) ⟨16683, by rfl⟩ (by norm_num))
theorem R44493 : Reach 44493 := rs (se 3 (by rfl) ⟨8342, by rfl⟩) (B 16685 (by norm_num) ⟨8342, by rfl⟩ (by norm_num))
theorem R44497 : Reach 44497 := rs (se 2 (by rfl) ⟨16686, by rfl⟩) (B 33373 (by norm_num) ⟨16686, by rfl⟩ (by norm_num))
theorem R44501 : Reach 44501 := rs (se 7 (by rfl) ⟨521, by rfl⟩) (B 1043 (by norm_num) ⟨521, by rfl⟩ (by norm_num))
theorem R142805 : Reach 142805 := rs (se 7 (by rfl) ⟨1673, by rfl⟩) (B 3347 (by norm_num) ⟨1673, by rfl⟩ (by norm_num))
theorem R44505 : Reach 44505 := rs (se 2 (by rfl) ⟨16689, by rfl⟩) (B 33379 (by norm_num) ⟨16689, by rfl⟩ (by norm_num))
theorem R44509 : Reach 44509 := rs (se 3 (by rfl) ⟨8345, by rfl⟩) (B 16691 (by norm_num) ⟨8345, by rfl⟩ (by norm_num))
theorem R110045 : Reach 110045 := rs (se 3 (by rfl) ⟨20633, by rfl⟩) (B 41267 (by norm_num) ⟨20633, by rfl⟩ (by norm_num))
theorem R44513 : Reach 44513 := rs (se 2 (by rfl) ⟨16692, by rfl⟩) (B 33385 (by norm_num) ⟨16692, by rfl⟩ (by norm_num))
theorem R44517 : Reach 44517 := rs (se 4 (by rfl) ⟨4173, by rfl⟩) (B 8347 (by norm_num) ⟨4173, by rfl⟩ (by norm_num))
theorem R44521 : Reach 44521 := rs (se 2 (by rfl) ⟨16695, by rfl⟩) (B 33391 (by norm_num) ⟨16695, by rfl⟩ (by norm_num))
theorem R44525 : Reach 44525 := rs (se 3 (by rfl) ⟨8348, by rfl⟩) (B 16697 (by norm_num) ⟨8348, by rfl⟩ (by norm_num))
theorem R44529 : Reach 44529 := rs (se 2 (by rfl) ⟨16698, by rfl⟩) (B 33397 (by norm_num) ⟨16698, by rfl⟩ (by norm_num))
theorem R110069 : Reach 110069 := rs (se 5 (by rfl) ⟨5159, by rfl⟩) (B 10319 (by norm_num) ⟨5159, by rfl⟩ (by norm_num))
theorem R44533 : Reach 44533 := rs (se 5 (by rfl) ⟨2087, by rfl⟩) (B 4175 (by norm_num) ⟨2087, by rfl⟩ (by norm_num))
theorem R44537 : Reach 44537 := rs (se 2 (by rfl) ⟨16701, by rfl⟩) (B 33403 (by norm_num) ⟨16701, by rfl⟩ (by norm_num))
theorem R44541 : Reach 44541 := rs (se 3 (by rfl) ⟨8351, by rfl⟩) (B 16703 (by norm_num) ⟨8351, by rfl⟩ (by norm_num))
theorem R44545 : Reach 44545 := rs (se 2 (by rfl) ⟨16704, by rfl⟩) (B 33409 (by norm_num) ⟨16704, by rfl⟩ (by norm_num))
theorem R44549 : Reach 44549 := rs (se 4 (by rfl) ⟨4176, by rfl⟩) (B 8353 (by norm_num) ⟨4176, by rfl⟩ (by norm_num))
theorem R44553 : Reach 44553 := rs (se 2 (by rfl) ⟨16707, by rfl⟩) (B 33415 (by norm_num) ⟨16707, by rfl⟩ (by norm_num))
theorem R44557 : Reach 44557 := rs (se 3 (by rfl) ⟨8354, by rfl⟩) (B 16709 (by norm_num) ⟨8354, by rfl⟩ (by norm_num))
theorem R44561 : Reach 44561 := rs (se 2 (by rfl) ⟨16710, by rfl⟩) (B 33421 (by norm_num) ⟨16710, by rfl⟩ (by norm_num))
theorem R44565 : Reach 44565 := rs (se 6 (by rfl) ⟨1044, by rfl⟩) (B 2089 (by norm_num) ⟨1044, by rfl⟩ (by norm_num))
theorem R44569 : Reach 44569 := rs (se 2 (by rfl) ⟨16713, by rfl⟩) (B 33427 (by norm_num) ⟨16713, by rfl⟩ (by norm_num))
theorem R44573 : Reach 44573 := rs (se 3 (by rfl) ⟨8357, by rfl⟩) (B 16715 (by norm_num) ⟨8357, by rfl⟩ (by norm_num))
theorem R77341 : Reach 77341 := rs (se 3 (by rfl) ⟨14501, by rfl⟩) (B 29003 (by norm_num) ⟨14501, by rfl⟩ (by norm_num))
theorem R44577 : Reach 44577 := rs (se 2 (by rfl) ⟨16716, by rfl⟩) (B 33433 (by norm_num) ⟨16716, by rfl⟩ (by norm_num))
theorem R44581 : Reach 44581 := rs (se 4 (by rfl) ⟨4179, by rfl⟩) (B 8359 (by norm_num) ⟨4179, by rfl⟩ (by norm_num))
theorem R44585 : Reach 44585 := rs (se 2 (by rfl) ⟨16719, by rfl⟩) (B 33439 (by norm_num) ⟨16719, by rfl⟩ (by norm_num))
theorem R44589 : Reach 44589 := rs (se 3 (by rfl) ⟨8360, by rfl⟩) (B 16721 (by norm_num) ⟨8360, by rfl⟩ (by norm_num))
theorem R44593 : Reach 44593 := rs (se 2 (by rfl) ⟨16722, by rfl⟩) (B 33445 (by norm_num) ⟨16722, by rfl⟩ (by norm_num))
theorem R44597 : Reach 44597 := rs (se 5 (by rfl) ⟨2090, by rfl⟩) (B 4181 (by norm_num) ⟨2090, by rfl⟩ (by norm_num))
theorem R44601 : Reach 44601 := rs (se 2 (by rfl) ⟨16725, by rfl⟩) (B 33451 (by norm_num) ⟨16725, by rfl⟩ (by norm_num))
theorem R44605 : Reach 44605 := rs (se 3 (by rfl) ⟨8363, by rfl⟩) (B 16727 (by norm_num) ⟨8363, by rfl⟩ (by norm_num))
theorem R44609 : Reach 44609 := rs (se 2 (by rfl) ⟨16728, by rfl⟩) (B 33457 (by norm_num) ⟨16728, by rfl⟩ (by norm_num))
theorem R44613 : Reach 44613 := rs (se 4 (by rfl) ⟨4182, by rfl⟩) (B 8365 (by norm_num) ⟨4182, by rfl⟩ (by norm_num))
theorem R44617 : Reach 44617 := rs (se 2 (by rfl) ⟨16731, by rfl⟩) (B 33463 (by norm_num) ⟨16731, by rfl⟩ (by norm_num))
theorem R44621 : Reach 44621 := rs (se 3 (by rfl) ⟨8366, by rfl⟩) (B 16733 (by norm_num) ⟨8366, by rfl⟩ (by norm_num))
theorem R44625 : Reach 44625 := rs (se 2 (by rfl) ⟨16734, by rfl⟩) (B 33469 (by norm_num) ⟨16734, by rfl⟩ (by norm_num))
theorem R44629 : Reach 44629 := rs (se 8 (by rfl) ⟨261, by rfl⟩) (B 523 (by norm_num) ⟨261, by rfl⟩ (by norm_num))
theorem R44633 : Reach 44633 := rs (se 2 (by rfl) ⟨16737, by rfl⟩) (B 33475 (by norm_num) ⟨16737, by rfl⟩ (by norm_num))
theorem R44637 : Reach 44637 := rs (se 3 (by rfl) ⟨8369, by rfl⟩) (B 16739 (by norm_num) ⟨8369, by rfl⟩ (by norm_num))
theorem R44641 : Reach 44641 := rs (se 2 (by rfl) ⟨16740, by rfl⟩) (B 33481 (by norm_num) ⟨16740, by rfl⟩ (by norm_num))
theorem R44645 : Reach 44645 := rs (se 4 (by rfl) ⟨4185, by rfl⟩) (B 8371 (by norm_num) ⟨4185, by rfl⟩ (by norm_num))
theorem R44649 : Reach 44649 := rs (se 2 (by rfl) ⟨16743, by rfl⟩) (B 33487 (by norm_num) ⟨16743, by rfl⟩ (by norm_num))
theorem R44653 : Reach 44653 := rs (se 3 (by rfl) ⟨8372, by rfl⟩) (B 16745 (by norm_num) ⟨8372, by rfl⟩ (by norm_num))
theorem R44657 : Reach 44657 := rs (se 2 (by rfl) ⟨16746, by rfl⟩) (B 33493 (by norm_num) ⟨16746, by rfl⟩ (by norm_num))
theorem R44661 : Reach 44661 := rs (se 5 (by rfl) ⟨2093, by rfl⟩) (B 4187 (by norm_num) ⟨2093, by rfl⟩ (by norm_num))
theorem R77429 : Reach 77429 := rs (se 5 (by rfl) ⟨3629, by rfl⟩) (B 7259 (by norm_num) ⟨3629, by rfl⟩ (by norm_num))
theorem R44665 : Reach 44665 := rs (se 2 (by rfl) ⟨16749, by rfl⟩) (B 33499 (by norm_num) ⟨16749, by rfl⟩ (by norm_num))
theorem R44669 : Reach 44669 := rs (se 3 (by rfl) ⟨8375, by rfl⟩) (B 16751 (by norm_num) ⟨8375, by rfl⟩ (by norm_num))
theorem R44673 : Reach 44673 := rs (se 2 (by rfl) ⟨16752, by rfl⟩) (B 33505 (by norm_num) ⟨16752, by rfl⟩ (by norm_num))
theorem R44677 : Reach 44677 := rs (se 4 (by rfl) ⟨4188, by rfl⟩) (B 8377 (by norm_num) ⟨4188, by rfl⟩ (by norm_num))
theorem R44681 : Reach 44681 := rs (se 2 (by rfl) ⟨16755, by rfl⟩) (B 33511 (by norm_num) ⟨16755, by rfl⟩ (by norm_num))
theorem R44685 : Reach 44685 := rs (se 3 (by rfl) ⟨8378, by rfl⟩) (B 16757 (by norm_num) ⟨8378, by rfl⟩ (by norm_num))
theorem R44689 : Reach 44689 := rs (se 2 (by rfl) ⟨16758, by rfl⟩) (B 33517 (by norm_num) ⟨16758, by rfl⟩ (by norm_num))
theorem R44693 : Reach 44693 := rs (se 6 (by rfl) ⟨1047, by rfl⟩) (B 2095 (by norm_num) ⟨1047, by rfl⟩ (by norm_num))
theorem R44697 : Reach 44697 := rs (se 2 (by rfl) ⟨16761, by rfl⟩) (B 33523 (by norm_num) ⟨16761, by rfl⟩ (by norm_num))
theorem R44701 : Reach 44701 := rs (se 3 (by rfl) ⟨8381, by rfl⟩) (B 16763 (by norm_num) ⟨8381, by rfl⟩ (by norm_num))
theorem R44705 : Reach 44705 := rs (se 2 (by rfl) ⟨16764, by rfl⟩) (B 33529 (by norm_num) ⟨16764, by rfl⟩ (by norm_num))
theorem R44709 : Reach 44709 := rs (se 4 (by rfl) ⟨4191, by rfl⟩) (B 8383 (by norm_num) ⟨4191, by rfl⟩ (by norm_num))
theorem R44713 : Reach 44713 := rs (se 2 (by rfl) ⟨16767, by rfl⟩) (B 33535 (by norm_num) ⟨16767, by rfl⟩ (by norm_num))
theorem R44717 : Reach 44717 := rs (se 3 (by rfl) ⟨8384, by rfl⟩) (B 16769 (by norm_num) ⟨8384, by rfl⟩ (by norm_num))
theorem R44721 : Reach 44721 := rs (se 2 (by rfl) ⟨16770, by rfl⟩) (B 33541 (by norm_num) ⟨16770, by rfl⟩ (by norm_num))
theorem R110261 : Reach 110261 := rs (se 5 (by rfl) ⟨5168, by rfl⟩) (B 10337 (by norm_num) ⟨5168, by rfl⟩ (by norm_num))
theorem R44725 : Reach 44725 := rs (se 5 (by rfl) ⟨2096, by rfl⟩) (B 4193 (by norm_num) ⟨2096, by rfl⟩ (by norm_num))
theorem R44729 : Reach 44729 := rs (se 2 (by rfl) ⟨16773, by rfl⟩) (B 33547 (by norm_num) ⟨16773, by rfl⟩ (by norm_num))
theorem R44733 : Reach 44733 := rs (se 3 (by rfl) ⟨8387, by rfl⟩) (B 16775 (by norm_num) ⟨8387, by rfl⟩ (by norm_num))
theorem R44737 : Reach 44737 := rs (se 2 (by rfl) ⟨16776, by rfl⟩) (B 33553 (by norm_num) ⟨16776, by rfl⟩ (by norm_num))
theorem R44741 : Reach 44741 := rs (se 4 (by rfl) ⟨4194, by rfl⟩) (B 8389 (by norm_num) ⟨4194, by rfl⟩ (by norm_num))
theorem R44745 : Reach 44745 := rs (se 2 (by rfl) ⟨16779, by rfl⟩) (B 33559 (by norm_num) ⟨16779, by rfl⟩ (by norm_num))
theorem R44749 : Reach 44749 := rs (se 3 (by rfl) ⟨8390, by rfl⟩) (B 16781 (by norm_num) ⟨8390, by rfl⟩ (by norm_num))
theorem R44753 : Reach 44753 := rs (se 2 (by rfl) ⟨16782, by rfl⟩) (B 33565 (by norm_num) ⟨16782, by rfl⟩ (by norm_num))
theorem R44757 : Reach 44757 := rs (se 7 (by rfl) ⟨524, by rfl⟩) (B 1049 (by norm_num) ⟨524, by rfl⟩ (by norm_num))
theorem R44761 : Reach 44761 := rs (se 2 (by rfl) ⟨16785, by rfl⟩) (B 33571 (by norm_num) ⟨16785, by rfl⟩ (by norm_num))
theorem R44765 : Reach 44765 := rs (se 3 (by rfl) ⟨8393, by rfl⟩) (B 16787 (by norm_num) ⟨8393, by rfl⟩ (by norm_num))
theorem R44769 : Reach 44769 := rs (se 2 (by rfl) ⟨16788, by rfl⟩) (B 33577 (by norm_num) ⟨16788, by rfl⟩ (by norm_num))
theorem R44773 : Reach 44773 := rs (se 4 (by rfl) ⟨4197, by rfl⟩) (B 8395 (by norm_num) ⟨4197, by rfl⟩ (by norm_num))
theorem R44777 : Reach 44777 := rs (se 2 (by rfl) ⟨16791, by rfl⟩) (B 33583 (by norm_num) ⟨16791, by rfl⟩ (by norm_num))
theorem R44781 : Reach 44781 := rs (se 3 (by rfl) ⟨8396, by rfl⟩) (B 16793 (by norm_num) ⟨8396, by rfl⟩ (by norm_num))
theorem R44785 : Reach 44785 := rs (se 2 (by rfl) ⟨16794, by rfl⟩) (B 33589 (by norm_num) ⟨16794, by rfl⟩ (by norm_num))
theorem R44789 : Reach 44789 := rs (se 5 (by rfl) ⟨2099, by rfl⟩) (B 4199 (by norm_num) ⟨2099, by rfl⟩ (by norm_num))
theorem R77557 : Reach 77557 := rs (se 5 (by rfl) ⟨3635, by rfl⟩) (B 7271 (by norm_num) ⟨3635, by rfl⟩ (by norm_num))
theorem R44793 : Reach 44793 := rs (se 2 (by rfl) ⟨16797, by rfl⟩) (B 33595 (by norm_num) ⟨16797, by rfl⟩ (by norm_num))
theorem R44797 : Reach 44797 := rs (se 3 (by rfl) ⟨8399, by rfl⟩) (B 16799 (by norm_num) ⟨8399, by rfl⟩ (by norm_num))
theorem R44801 : Reach 44801 := rs (se 2 (by rfl) ⟨16800, by rfl⟩) (B 33601 (by norm_num) ⟨16800, by rfl⟩ (by norm_num))
theorem R44805 : Reach 44805 := rs (se 4 (by rfl) ⟨4200, by rfl⟩) (B 8401 (by norm_num) ⟨4200, by rfl⟩ (by norm_num))
theorem R44809 : Reach 44809 := rs (se 2 (by rfl) ⟨16803, by rfl⟩) (B 33607 (by norm_num) ⟨16803, by rfl⟩ (by norm_num))
theorem R44813 : Reach 44813 := rs (se 3 (by rfl) ⟨8402, by rfl⟩) (B 16805 (by norm_num) ⟨8402, by rfl⟩ (by norm_num))
theorem R44817 : Reach 44817 := rs (se 2 (by rfl) ⟨16806, by rfl⟩) (B 33613 (by norm_num) ⟨16806, by rfl⟩ (by norm_num))
theorem R44821 : Reach 44821 := rs (se 6 (by rfl) ⟨1050, by rfl⟩) (B 2101 (by norm_num) ⟨1050, by rfl⟩ (by norm_num))
theorem R44825 : Reach 44825 := rs (se 2 (by rfl) ⟨16809, by rfl⟩) (B 33619 (by norm_num) ⟨16809, by rfl⟩ (by norm_num))
theorem R44829 : Reach 44829 := rs (se 3 (by rfl) ⟨8405, by rfl⟩) (B 16811 (by norm_num) ⟨8405, by rfl⟩ (by norm_num))
theorem R44833 : Reach 44833 := rs (se 2 (by rfl) ⟨16812, by rfl⟩) (B 33625 (by norm_num) ⟨16812, by rfl⟩ (by norm_num))
theorem R44837 : Reach 44837 := rs (se 4 (by rfl) ⟨4203, by rfl⟩) (B 8407 (by norm_num) ⟨4203, by rfl⟩ (by norm_num))
theorem R44841 : Reach 44841 := rs (se 2 (by rfl) ⟨16815, by rfl⟩) (B 33631 (by norm_num) ⟨16815, by rfl⟩ (by norm_num))
theorem R44845 : Reach 44845 := rs (se 3 (by rfl) ⟨8408, by rfl⟩) (B 16817 (by norm_num) ⟨8408, by rfl⟩ (by norm_num))
theorem R44849 : Reach 44849 := rs (se 2 (by rfl) ⟨16818, by rfl⟩) (B 33637 (by norm_num) ⟨16818, by rfl⟩ (by norm_num))
theorem R44853 : Reach 44853 := rs (se 5 (by rfl) ⟨2102, by rfl⟩) (B 4205 (by norm_num) ⟨2102, by rfl⟩ (by norm_num))
theorem R44857 : Reach 44857 := rs (se 2 (by rfl) ⟨16821, by rfl⟩) (B 33643 (by norm_num) ⟨16821, by rfl⟩ (by norm_num))
theorem R44861 : Reach 44861 := rs (se 3 (by rfl) ⟨8411, by rfl⟩) (B 16823 (by norm_num) ⟨8411, by rfl⟩ (by norm_num))
theorem R44865 : Reach 44865 := rs (se 2 (by rfl) ⟨16824, by rfl⟩) (B 33649 (by norm_num) ⟨16824, by rfl⟩ (by norm_num))
theorem R44869 : Reach 44869 := rs (se 4 (by rfl) ⟨4206, by rfl⟩) (B 8413 (by norm_num) ⟨4206, by rfl⟩ (by norm_num))
theorem R44873 : Reach 44873 := rs (se 2 (by rfl) ⟨16827, by rfl⟩) (B 33655 (by norm_num) ⟨16827, by rfl⟩ (by norm_num))
theorem R44877 : Reach 44877 := rs (se 3 (by rfl) ⟨8414, by rfl⟩) (B 16829 (by norm_num) ⟨8414, by rfl⟩ (by norm_num))
theorem R77645 : Reach 77645 := rs (se 3 (by rfl) ⟨14558, by rfl⟩) (B 29117 (by norm_num) ⟨14558, by rfl⟩ (by norm_num))
theorem R44881 : Reach 44881 := rs (se 2 (by rfl) ⟨16830, by rfl⟩) (B 33661 (by norm_num) ⟨16830, by rfl⟩ (by norm_num))
theorem R44885 : Reach 44885 := rs (se 9 (by rfl) ⟨131, by rfl⟩) (B 263 (by norm_num) ⟨131, by rfl⟩ (by norm_num))
theorem R44889 : Reach 44889 := rs (se 2 (by rfl) ⟨16833, by rfl⟩) (B 33667 (by norm_num) ⟨16833, by rfl⟩ (by norm_num))
theorem R44893 : Reach 44893 := rs (se 3 (by rfl) ⟨8417, by rfl⟩) (B 16835 (by norm_num) ⟨8417, by rfl⟩ (by norm_num))
theorem R44897 : Reach 44897 := rs (se 2 (by rfl) ⟨16836, by rfl⟩) (B 33673 (by norm_num) ⟨16836, by rfl⟩ (by norm_num))
theorem R44901 : Reach 44901 := rs (se 4 (by rfl) ⟨4209, by rfl⟩) (B 8419 (by norm_num) ⟨4209, by rfl⟩ (by norm_num))
theorem R44905 : Reach 44905 := rs (se 2 (by rfl) ⟨16839, by rfl⟩) (B 33679 (by norm_num) ⟨16839, by rfl⟩ (by norm_num))
theorem R44909 : Reach 44909 := rs (se 3 (by rfl) ⟨8420, by rfl⟩) (B 16841 (by norm_num) ⟨8420, by rfl⟩ (by norm_num))
theorem R44913 : Reach 44913 := rs (se 2 (by rfl) ⟨16842, by rfl⟩) (B 33685 (by norm_num) ⟨16842, by rfl⟩ (by norm_num))
theorem R44917 : Reach 44917 := rs (se 5 (by rfl) ⟨2105, by rfl⟩) (B 4211 (by norm_num) ⟨2105, by rfl⟩ (by norm_num))
theorem R44921 : Reach 44921 := rs (se 2 (by rfl) ⟨16845, by rfl⟩) (B 33691 (by norm_num) ⟨16845, by rfl⟩ (by norm_num))
theorem R44925 : Reach 44925 := rs (se 3 (by rfl) ⟨8423, by rfl⟩) (B 16847 (by norm_num) ⟨8423, by rfl⟩ (by norm_num))
theorem R44929 : Reach 44929 := rs (se 2 (by rfl) ⟨16848, by rfl⟩) (B 33697 (by norm_num) ⟨16848, by rfl⟩ (by norm_num))
theorem R44933 : Reach 44933 := rs (se 4 (by rfl) ⟨4212, by rfl⟩) (B 8425 (by norm_num) ⟨4212, by rfl⟩ (by norm_num))
theorem R44937 : Reach 44937 := rs (se 2 (by rfl) ⟨16851, by rfl⟩) (B 33703 (by norm_num) ⟨16851, by rfl⟩ (by norm_num))
theorem R44941 : Reach 44941 := rs (se 3 (by rfl) ⟨8426, by rfl⟩) (B 16853 (by norm_num) ⟨8426, by rfl⟩ (by norm_num))
theorem R44945 : Reach 44945 := rs (se 2 (by rfl) ⟨16854, by rfl⟩) (B 33709 (by norm_num) ⟨16854, by rfl⟩ (by norm_num))
theorem R44949 : Reach 44949 := rs (se 6 (by rfl) ⟨1053, by rfl⟩) (B 2107 (by norm_num) ⟨1053, by rfl⟩ (by norm_num))
theorem R44953 : Reach 44953 := rs (se 2 (by rfl) ⟨16857, by rfl⟩) (B 33715 (by norm_num) ⟨16857, by rfl⟩ (by norm_num))
theorem R44957 : Reach 44957 := rs (se 3 (by rfl) ⟨8429, by rfl⟩) (B 16859 (by norm_num) ⟨8429, by rfl⟩ (by norm_num))
theorem R44961 : Reach 44961 := rs (se 2 (by rfl) ⟨16860, by rfl⟩) (B 33721 (by norm_num) ⟨16860, by rfl⟩ (by norm_num))
theorem R44965 : Reach 44965 := rs (se 4 (by rfl) ⟨4215, by rfl⟩) (B 8431 (by norm_num) ⟨4215, by rfl⟩ (by norm_num))
theorem R44969 : Reach 44969 := rs (se 2 (by rfl) ⟨16863, by rfl⟩) (B 33727 (by norm_num) ⟨16863, by rfl⟩ (by norm_num))
theorem R44973 : Reach 44973 := rs (se 3 (by rfl) ⟨8432, by rfl⟩) (B 16865 (by norm_num) ⟨8432, by rfl⟩ (by norm_num))
theorem R44977 : Reach 44977 := rs (se 2 (by rfl) ⟨16866, by rfl⟩) (B 33733 (by norm_num) ⟨16866, by rfl⟩ (by norm_num))
theorem R44981 : Reach 44981 := rs (se 5 (by rfl) ⟨2108, by rfl⟩) (B 4217 (by norm_num) ⟨2108, by rfl⟩ (by norm_num))
theorem R176053 : Reach 176053 := rs (se 5 (by rfl) ⟨8252, by rfl⟩) (B 16505 (by norm_num) ⟨8252, by rfl⟩ (by norm_num))
theorem R44985 : Reach 44985 := rs (se 2 (by rfl) ⟨16869, by rfl⟩) (B 33739 (by norm_num) ⟨16869, by rfl⟩ (by norm_num))
theorem R44989 : Reach 44989 := rs (se 3 (by rfl) ⟨8435, by rfl⟩) (B 16871 (by norm_num) ⟨8435, by rfl⟩ (by norm_num))
theorem R44993 : Reach 44993 := rs (se 2 (by rfl) ⟨16872, by rfl⟩) (B 33745 (by norm_num) ⟨16872, by rfl⟩ (by norm_num))
theorem R44997 : Reach 44997 := rs (se 4 (by rfl) ⟨4218, by rfl⟩) (B 8437 (by norm_num) ⟨4218, by rfl⟩ (by norm_num))
theorem R45001 : Reach 45001 := rs (se 2 (by rfl) ⟨16875, by rfl⟩) (B 33751 (by norm_num) ⟨16875, by rfl⟩ (by norm_num))
theorem R45005 : Reach 45005 := rs (se 3 (by rfl) ⟨8438, by rfl⟩) (B 16877 (by norm_num) ⟨8438, by rfl⟩ (by norm_num))
theorem R77773 : Reach 77773 := rs (se 3 (by rfl) ⟨14582, by rfl⟩) (B 29165 (by norm_num) ⟨14582, by rfl⟩ (by norm_num))
theorem R45009 : Reach 45009 := rs (se 2 (by rfl) ⟨16878, by rfl⟩) (B 33757 (by norm_num) ⟨16878, by rfl⟩ (by norm_num))
theorem R143317 : Reach 143317 := rs (se 7 (by rfl) ⟨1679, by rfl⟩) (B 3359 (by norm_num) ⟨1679, by rfl⟩ (by norm_num))
theorem R45013 : Reach 45013 := rs (se 7 (by rfl) ⟨527, by rfl⟩) (B 1055 (by norm_num) ⟨527, by rfl⟩ (by norm_num))
theorem R45017 : Reach 45017 := rs (se 2 (by rfl) ⟨16881, by rfl⟩) (B 33763 (by norm_num) ⟨16881, by rfl⟩ (by norm_num))
theorem R45021 : Reach 45021 := rs (se 3 (by rfl) ⟨8441, by rfl⟩) (B 16883 (by norm_num) ⟨8441, by rfl⟩ (by norm_num))
theorem R45025 : Reach 45025 := rs (se 2 (by rfl) ⟨16884, by rfl⟩) (B 33769 (by norm_num) ⟨16884, by rfl⟩ (by norm_num))
theorem R45029 : Reach 45029 := rs (se 4 (by rfl) ⟨4221, by rfl⟩) (B 8443 (by norm_num) ⟨4221, by rfl⟩ (by norm_num))
theorem R45033 : Reach 45033 := rs (se 2 (by rfl) ⟨16887, by rfl⟩) (B 33775 (by norm_num) ⟨16887, by rfl⟩ (by norm_num))
theorem R45037 : Reach 45037 := rs (se 3 (by rfl) ⟨8444, by rfl⟩) (B 16889 (by norm_num) ⟨8444, by rfl⟩ (by norm_num))
theorem R45041 : Reach 45041 := rs (se 2 (by rfl) ⟨16890, by rfl⟩) (B 33781 (by norm_num) ⟨16890, by rfl⟩ (by norm_num))
theorem R45045 : Reach 45045 := rs (se 5 (by rfl) ⟨2111, by rfl⟩) (B 4223 (by norm_num) ⟨2111, by rfl⟩ (by norm_num))
theorem R45049 : Reach 45049 := rs (se 2 (by rfl) ⟨16893, by rfl⟩) (B 33787 (by norm_num) ⟨16893, by rfl⟩ (by norm_num))
theorem R45053 : Reach 45053 := rs (se 3 (by rfl) ⟨8447, by rfl⟩) (B 16895 (by norm_num) ⟨8447, by rfl⟩ (by norm_num))
theorem R45057 : Reach 45057 := rs (se 2 (by rfl) ⟨16896, by rfl⟩) (B 33793 (by norm_num) ⟨16896, by rfl⟩ (by norm_num))
theorem R45061 : Reach 45061 := rs (se 4 (by rfl) ⟨4224, by rfl⟩) (B 8449 (by norm_num) ⟨4224, by rfl⟩ (by norm_num))
theorem R45065 : Reach 45065 := rs (se 2 (by rfl) ⟨16899, by rfl⟩) (B 33799 (by norm_num) ⟨16899, by rfl⟩ (by norm_num))
theorem R110605 : Reach 110605 := rs (se 3 (by rfl) ⟨20738, by rfl⟩) (B 41477 (by norm_num) ⟨20738, by rfl⟩ (by norm_num))
theorem R45069 : Reach 45069 := rs (se 3 (by rfl) ⟨8450, by rfl⟩) (B 16901 (by norm_num) ⟨8450, by rfl⟩ (by norm_num))
theorem R45073 : Reach 45073 := rs (se 2 (by rfl) ⟨16902, by rfl⟩) (B 33805 (by norm_num) ⟨16902, by rfl⟩ (by norm_num))
theorem R45077 : Reach 45077 := rs (se 6 (by rfl) ⟨1056, by rfl⟩) (B 2113 (by norm_num) ⟨1056, by rfl⟩ (by norm_num))
theorem R45081 : Reach 45081 := rs (se 2 (by rfl) ⟨16905, by rfl⟩) (B 33811 (by norm_num) ⟨16905, by rfl⟩ (by norm_num))
theorem R45085 : Reach 45085 := rs (se 3 (by rfl) ⟨8453, by rfl⟩) (B 16907 (by norm_num) ⟨8453, by rfl⟩ (by norm_num))
theorem R45089 : Reach 45089 := rs (se 2 (by rfl) ⟨16908, by rfl⟩) (B 33817 (by norm_num) ⟨16908, by rfl⟩ (by norm_num))
theorem R45093 : Reach 45093 := rs (se 4 (by rfl) ⟨4227, by rfl⟩) (B 8455 (by norm_num) ⟨4227, by rfl⟩ (by norm_num))
theorem R77861 : Reach 77861 := rs (se 4 (by rfl) ⟨7299, by rfl⟩) (B 14599 (by norm_num) ⟨7299, by rfl⟩ (by norm_num))
theorem R45097 : Reach 45097 := rs (se 2 (by rfl) ⟨16911, by rfl⟩) (B 33823 (by norm_num) ⟨16911, by rfl⟩ (by norm_num))
theorem R45101 : Reach 45101 := rs (se 3 (by rfl) ⟨8456, by rfl⟩) (B 16913 (by norm_num) ⟨8456, by rfl⟩ (by norm_num))
theorem R45105 : Reach 45105 := rs (se 2 (by rfl) ⟨16914, by rfl⟩) (B 33829 (by norm_num) ⟨16914, by rfl⟩ (by norm_num))
theorem R45109 : Reach 45109 := rs (se 5 (by rfl) ⟨2114, by rfl⟩) (B 4229 (by norm_num) ⟨2114, by rfl⟩ (by norm_num))
theorem R45113 : Reach 45113 := rs (se 2 (by rfl) ⟨16917, by rfl⟩) (B 33835 (by norm_num) ⟨16917, by rfl⟩ (by norm_num))
theorem R45117 : Reach 45117 := rs (se 3 (by rfl) ⟨8459, by rfl⟩) (B 16919 (by norm_num) ⟨8459, by rfl⟩ (by norm_num))
theorem R45121 : Reach 45121 := rs (se 2 (by rfl) ⟨16920, by rfl⟩) (B 33841 (by norm_num) ⟨16920, by rfl⟩ (by norm_num))
theorem R45125 : Reach 45125 := rs (se 4 (by rfl) ⟨4230, by rfl⟩) (B 8461 (by norm_num) ⟨4230, by rfl⟩ (by norm_num))
theorem R45129 : Reach 45129 := rs (se 2 (by rfl) ⟨16923, by rfl⟩) (B 33847 (by norm_num) ⟨16923, by rfl⟩ (by norm_num))
theorem R45133 : Reach 45133 := rs (se 3 (by rfl) ⟨8462, by rfl⟩) (B 16925 (by norm_num) ⟨8462, by rfl⟩ (by norm_num))
theorem R45137 : Reach 45137 := rs (se 2 (by rfl) ⟨16926, by rfl⟩) (B 33853 (by norm_num) ⟨16926, by rfl⟩ (by norm_num))
theorem R45141 : Reach 45141 := rs (se 8 (by rfl) ⟨264, by rfl⟩) (B 529 (by norm_num) ⟨264, by rfl⟩ (by norm_num))
theorem R45145 : Reach 45145 := rs (se 2 (by rfl) ⟨16929, by rfl⟩) (B 33859 (by norm_num) ⟨16929, by rfl⟩ (by norm_num))
theorem R45149 : Reach 45149 := rs (se 3 (by rfl) ⟨8465, by rfl⟩) (B 16931 (by norm_num) ⟨8465, by rfl⟩ (by norm_num))
theorem R45153 : Reach 45153 := rs (se 2 (by rfl) ⟨16932, by rfl⟩) (B 33865 (by norm_num) ⟨16932, by rfl⟩ (by norm_num))
theorem R45157 : Reach 45157 := rs (se 4 (by rfl) ⟨4233, by rfl⟩) (B 8467 (by norm_num) ⟨4233, by rfl⟩ (by norm_num))
theorem R45161 : Reach 45161 := rs (se 2 (by rfl) ⟨16935, by rfl⟩) (B 33871 (by norm_num) ⟨16935, by rfl⟩ (by norm_num))
theorem R45165 : Reach 45165 := rs (se 3 (by rfl) ⟨8468, by rfl⟩) (B 16937 (by norm_num) ⟨8468, by rfl⟩ (by norm_num))
theorem R45169 : Reach 45169 := rs (se 2 (by rfl) ⟨16938, by rfl⟩) (B 33877 (by norm_num) ⟨16938, by rfl⟩ (by norm_num))
theorem R45173 : Reach 45173 := rs (se 5 (by rfl) ⟨2117, by rfl⟩) (B 4235 (by norm_num) ⟨2117, by rfl⟩ (by norm_num))
theorem R45177 : Reach 45177 := rs (se 2 (by rfl) ⟨16941, by rfl⟩) (B 33883 (by norm_num) ⟨16941, by rfl⟩ (by norm_num))
theorem R110717 : Reach 110717 := rs (se 3 (by rfl) ⟨20759, by rfl⟩) (B 41519 (by norm_num) ⟨20759, by rfl⟩ (by norm_num))
theorem R45181 : Reach 45181 := rs (se 3 (by rfl) ⟨8471, by rfl⟩) (B 16943 (by norm_num) ⟨8471, by rfl⟩ (by norm_num))
theorem R45185 : Reach 45185 := rs (se 2 (by rfl) ⟨16944, by rfl⟩) (B 33889 (by norm_num) ⟨16944, by rfl⟩ (by norm_num))
theorem R45189 : Reach 45189 := rs (se 4 (by rfl) ⟨4236, by rfl⟩) (B 8473 (by norm_num) ⟨4236, by rfl⟩ (by norm_num))
theorem R45193 : Reach 45193 := rs (se 2 (by rfl) ⟨16947, by rfl⟩) (B 33895 (by norm_num) ⟨16947, by rfl⟩ (by norm_num))
theorem R45197 : Reach 45197 := rs (se 3 (by rfl) ⟨8474, by rfl⟩) (B 16949 (by norm_num) ⟨8474, by rfl⟩ (by norm_num))
theorem R45201 : Reach 45201 := rs (se 2 (by rfl) ⟨16950, by rfl⟩) (B 33901 (by norm_num) ⟨16950, by rfl⟩ (by norm_num))
theorem R45205 : Reach 45205 := rs (se 6 (by rfl) ⟨1059, by rfl⟩) (B 2119 (by norm_num) ⟨1059, by rfl⟩ (by norm_num))
theorem R45209 : Reach 45209 := rs (se 2 (by rfl) ⟨16953, by rfl⟩) (B 33907 (by norm_num) ⟨16953, by rfl⟩ (by norm_num))
theorem R45213 : Reach 45213 := rs (se 3 (by rfl) ⟨8477, by rfl⟩) (B 16955 (by norm_num) ⟨8477, by rfl⟩ (by norm_num))
theorem R45217 : Reach 45217 := rs (se 2 (by rfl) ⟨16956, by rfl⟩) (B 33913 (by norm_num) ⟨16956, by rfl⟩ (by norm_num))
theorem R45221 : Reach 45221 := rs (se 4 (by rfl) ⟨4239, by rfl⟩) (B 8479 (by norm_num) ⟨4239, by rfl⟩ (by norm_num))
theorem R77989 : Reach 77989 := rs (se 4 (by rfl) ⟨7311, by rfl⟩) (B 14623 (by norm_num) ⟨7311, by rfl⟩ (by norm_num))
theorem R45225 : Reach 45225 := rs (se 2 (by rfl) ⟨16959, by rfl⟩) (B 33919 (by norm_num) ⟨16959, by rfl⟩ (by norm_num))
theorem R45229 : Reach 45229 := rs (se 3 (by rfl) ⟨8480, by rfl⟩) (B 16961 (by norm_num) ⟨8480, by rfl⟩ (by norm_num))
theorem R45233 : Reach 45233 := rs (se 2 (by rfl) ⟨16962, by rfl⟩) (B 33925 (by norm_num) ⟨16962, by rfl⟩ (by norm_num))
theorem R45237 : Reach 45237 := rs (se 5 (by rfl) ⟨2120, by rfl⟩) (B 4241 (by norm_num) ⟨2120, by rfl⟩ (by norm_num))
theorem R45241 : Reach 45241 := rs (se 2 (by rfl) ⟨16965, by rfl⟩) (B 33931 (by norm_num) ⟨16965, by rfl⟩ (by norm_num))
theorem R45245 : Reach 45245 := rs (se 3 (by rfl) ⟨8483, by rfl⟩) (B 16967 (by norm_num) ⟨8483, by rfl⟩ (by norm_num))
theorem R45249 : Reach 45249 := rs (se 2 (by rfl) ⟨16968, by rfl⟩) (B 33937 (by norm_num) ⟨16968, by rfl⟩ (by norm_num))
theorem R45253 : Reach 45253 := rs (se 4 (by rfl) ⟨4242, by rfl⟩) (B 8485 (by norm_num) ⟨4242, by rfl⟩ (by norm_num))
theorem R45257 : Reach 45257 := rs (se 2 (by rfl) ⟨16971, by rfl⟩) (B 33943 (by norm_num) ⟨16971, by rfl⟩ (by norm_num))
theorem R45261 : Reach 45261 := rs (se 3 (by rfl) ⟨8486, by rfl⟩) (B 16973 (by norm_num) ⟨8486, by rfl⟩ (by norm_num))
theorem R45265 : Reach 45265 := rs (se 2 (by rfl) ⟨16974, by rfl⟩) (B 33949 (by norm_num) ⟨16974, by rfl⟩ (by norm_num))
theorem R45269 : Reach 45269 := rs (se 7 (by rfl) ⟨530, by rfl⟩) (B 1061 (by norm_num) ⟨530, by rfl⟩ (by norm_num))
theorem R45273 : Reach 45273 := rs (se 2 (by rfl) ⟨16977, by rfl⟩) (B 33955 (by norm_num) ⟨16977, by rfl⟩ (by norm_num))
theorem R45277 : Reach 45277 := rs (se 3 (by rfl) ⟨8489, by rfl⟩) (B 16979 (by norm_num) ⟨8489, by rfl⟩ (by norm_num))
theorem R45281 : Reach 45281 := rs (se 2 (by rfl) ⟨16980, by rfl⟩) (B 33961 (by norm_num) ⟨16980, by rfl⟩ (by norm_num))
theorem R45285 : Reach 45285 := rs (se 4 (by rfl) ⟨4245, by rfl⟩) (B 8491 (by norm_num) ⟨4245, by rfl⟩ (by norm_num))
theorem R176357 : Reach 176357 := rs (se 4 (by rfl) ⟨16533, by rfl⟩) (B 33067 (by norm_num) ⟨16533, by rfl⟩ (by norm_num))
theorem R45289 : Reach 45289 := rs (se 2 (by rfl) ⟨16983, by rfl⟩) (B 33967 (by norm_num) ⟨16983, by rfl⟩ (by norm_num))
theorem R45293 : Reach 45293 := rs (se 3 (by rfl) ⟨8492, by rfl⟩) (B 16985 (by norm_num) ⟨8492, by rfl⟩ (by norm_num))
theorem R45297 : Reach 45297 := rs (se 2 (by rfl) ⟨16986, by rfl⟩) (B 33973 (by norm_num) ⟨16986, by rfl⟩ (by norm_num))
theorem R45301 : Reach 45301 := rs (se 5 (by rfl) ⟨2123, by rfl⟩) (B 4247 (by norm_num) ⟨2123, by rfl⟩ (by norm_num))
theorem R45305 : Reach 45305 := rs (se 2 (by rfl) ⟨16989, by rfl⟩) (B 33979 (by norm_num) ⟨16989, by rfl⟩ (by norm_num))
theorem R45309 : Reach 45309 := rs (se 3 (by rfl) ⟨8495, by rfl⟩) (B 16991 (by norm_num) ⟨8495, by rfl⟩ (by norm_num))
theorem R78077 : Reach 78077 := rs (se 3 (by rfl) ⟨14639, by rfl⟩) (B 29279 (by norm_num) ⟨14639, by rfl⟩ (by norm_num))
theorem R45313 : Reach 45313 := rs (se 2 (by rfl) ⟨16992, by rfl⟩) (B 33985 (by norm_num) ⟨16992, by rfl⟩ (by norm_num))
theorem R45317 : Reach 45317 := rs (se 4 (by rfl) ⟨4248, by rfl⟩) (B 8497 (by norm_num) ⟨4248, by rfl⟩ (by norm_num))
theorem R45321 : Reach 45321 := rs (se 2 (by rfl) ⟨16995, by rfl⟩) (B 33991 (by norm_num) ⟨16995, by rfl⟩ (by norm_num))
theorem R45325 : Reach 45325 := rs (se 3 (by rfl) ⟨8498, by rfl⟩) (B 16997 (by norm_num) ⟨8498, by rfl⟩ (by norm_num))
theorem R45329 : Reach 45329 := rs (se 2 (by rfl) ⟨16998, by rfl⟩) (B 33997 (by norm_num) ⟨16998, by rfl⟩ (by norm_num))
theorem R45333 : Reach 45333 := rs (se 6 (by rfl) ⟨1062, by rfl⟩) (B 2125 (by norm_num) ⟨1062, by rfl⟩ (by norm_num))
theorem R45337 : Reach 45337 := rs (se 2 (by rfl) ⟨17001, by rfl⟩) (B 34003 (by norm_num) ⟨17001, by rfl⟩ (by norm_num))
theorem R45341 : Reach 45341 := rs (se 3 (by rfl) ⟨8501, by rfl⟩) (B 17003 (by norm_num) ⟨8501, by rfl⟩ (by norm_num))
theorem R45345 : Reach 45345 := rs (se 2 (by rfl) ⟨17004, by rfl⟩) (B 34009 (by norm_num) ⟨17004, by rfl⟩ (by norm_num))
theorem R45349 : Reach 45349 := rs (se 4 (by rfl) ⟨4251, by rfl⟩) (B 8503 (by norm_num) ⟨4251, by rfl⟩ (by norm_num))
theorem R45353 : Reach 45353 := rs (se 2 (by rfl) ⟨17007, by rfl⟩) (B 34015 (by norm_num) ⟨17007, by rfl⟩ (by norm_num))
theorem R45357 : Reach 45357 := rs (se 3 (by rfl) ⟨8504, by rfl⟩) (B 17009 (by norm_num) ⟨8504, by rfl⟩ (by norm_num))
theorem R45361 : Reach 45361 := rs (se 2 (by rfl) ⟨17010, by rfl⟩) (B 34021 (by norm_num) ⟨17010, by rfl⟩ (by norm_num))
theorem R45365 : Reach 45365 := rs (se 5 (by rfl) ⟨2126, by rfl⟩) (B 4253 (by norm_num) ⟨2126, by rfl⟩ (by norm_num))
theorem R45369 : Reach 45369 := rs (se 2 (by rfl) ⟨17013, by rfl⟩) (B 34027 (by norm_num) ⟨17013, by rfl⟩ (by norm_num))
theorem R110909 : Reach 110909 := rs (se 3 (by rfl) ⟨20795, by rfl⟩) (B 41591 (by norm_num) ⟨20795, by rfl⟩ (by norm_num))
theorem R45373 : Reach 45373 := rs (se 3 (by rfl) ⟨8507, by rfl⟩) (B 17015 (by norm_num) ⟨8507, by rfl⟩ (by norm_num))
theorem R45377 : Reach 45377 := rs (se 2 (by rfl) ⟨17016, by rfl⟩) (B 34033 (by norm_num) ⟨17016, by rfl⟩ (by norm_num))
theorem R45381 : Reach 45381 := rs (se 4 (by rfl) ⟨4254, by rfl⟩) (B 8509 (by norm_num) ⟨4254, by rfl⟩ (by norm_num))
theorem R45385 : Reach 45385 := rs (se 2 (by rfl) ⟨17019, by rfl⟩) (B 34039 (by norm_num) ⟨17019, by rfl⟩ (by norm_num))
theorem R45389 : Reach 45389 := rs (se 3 (by rfl) ⟨8510, by rfl⟩) (B 17021 (by norm_num) ⟨8510, by rfl⟩ (by norm_num))
theorem R45393 : Reach 45393 := rs (se 2 (by rfl) ⟨17022, by rfl⟩) (B 34045 (by norm_num) ⟨17022, by rfl⟩ (by norm_num))
theorem R45397 : Reach 45397 := rs (se 10 (by rfl) ⟨66, by rfl⟩) (B 133 (by norm_num) ⟨66, by rfl⟩ (by norm_num))
theorem R45401 : Reach 45401 := rs (se 2 (by rfl) ⟨17025, by rfl⟩) (B 34051 (by norm_num) ⟨17025, by rfl⟩ (by norm_num))
theorem R45405 : Reach 45405 := rs (se 3 (by rfl) ⟨8513, by rfl⟩) (B 17027 (by norm_num) ⟨8513, by rfl⟩ (by norm_num))
theorem R45409 : Reach 45409 := rs (se 2 (by rfl) ⟨17028, by rfl⟩) (B 34057 (by norm_num) ⟨17028, by rfl⟩ (by norm_num))
theorem R45413 : Reach 45413 := rs (se 4 (by rfl) ⟨4257, by rfl⟩) (B 8515 (by norm_num) ⟨4257, by rfl⟩ (by norm_num))
theorem R45417 : Reach 45417 := rs (se 2 (by rfl) ⟨17031, by rfl⟩) (B 34063 (by norm_num) ⟨17031, by rfl⟩ (by norm_num))
theorem R45421 : Reach 45421 := rs (se 3 (by rfl) ⟨8516, by rfl⟩) (B 17033 (by norm_num) ⟨8516, by rfl⟩ (by norm_num))
theorem R45425 : Reach 45425 := rs (se 2 (by rfl) ⟨17034, by rfl⟩) (B 34069 (by norm_num) ⟨17034, by rfl⟩ (by norm_num))
theorem R45429 : Reach 45429 := rs (se 5 (by rfl) ⟨2129, by rfl⟩) (B 4259 (by norm_num) ⟨2129, by rfl⟩ (by norm_num))
theorem R45433 : Reach 45433 := rs (se 2 (by rfl) ⟨17037, by rfl⟩) (B 34075 (by norm_num) ⟨17037, by rfl⟩ (by norm_num))
theorem R45437 : Reach 45437 := rs (se 3 (by rfl) ⟨8519, by rfl⟩) (B 17039 (by norm_num) ⟨8519, by rfl⟩ (by norm_num))
theorem R78205 : Reach 78205 := rs (se 3 (by rfl) ⟨14663, by rfl⟩) (B 29327 (by norm_num) ⟨14663, by rfl⟩ (by norm_num))
theorem R45441 : Reach 45441 := rs (se 2 (by rfl) ⟨17040, by rfl⟩) (B 34081 (by norm_num) ⟨17040, by rfl⟩ (by norm_num))
theorem R45445 : Reach 45445 := rs (se 4 (by rfl) ⟨4260, by rfl⟩) (B 8521 (by norm_num) ⟨4260, by rfl⟩ (by norm_num))
theorem R45449 : Reach 45449 := rs (se 2 (by rfl) ⟨17043, by rfl⟩) (B 34087 (by norm_num) ⟨17043, by rfl⟩ (by norm_num))
theorem R45453 : Reach 45453 := rs (se 3 (by rfl) ⟨8522, by rfl⟩) (B 17045 (by norm_num) ⟨8522, by rfl⟩ (by norm_num))
theorem R45457 : Reach 45457 := rs (se 2 (by rfl) ⟨17046, by rfl⟩) (B 34093 (by norm_num) ⟨17046, by rfl⟩ (by norm_num))
theorem R45461 : Reach 45461 := rs (se 6 (by rfl) ⟨1065, by rfl⟩) (B 2131 (by norm_num) ⟨1065, by rfl⟩ (by norm_num))
theorem R45465 : Reach 45465 := rs (se 2 (by rfl) ⟨17049, by rfl⟩) (B 34099 (by norm_num) ⟨17049, by rfl⟩ (by norm_num))
theorem R45469 : Reach 45469 := rs (se 3 (by rfl) ⟨8525, by rfl⟩) (B 17051 (by norm_num) ⟨8525, by rfl⟩ (by norm_num))
theorem R45473 : Reach 45473 := rs (se 2 (by rfl) ⟨17052, by rfl⟩) (B 34105 (by norm_num) ⟨17052, by rfl⟩ (by norm_num))
theorem R45477 : Reach 45477 := rs (se 4 (by rfl) ⟨4263, by rfl⟩) (B 8527 (by norm_num) ⟨4263, by rfl⟩ (by norm_num))
theorem R45481 : Reach 45481 := rs (se 2 (by rfl) ⟨17055, by rfl⟩) (B 34111 (by norm_num) ⟨17055, by rfl⟩ (by norm_num))
theorem R45485 : Reach 45485 := rs (se 3 (by rfl) ⟨8528, by rfl⟩) (B 17057 (by norm_num) ⟨8528, by rfl⟩ (by norm_num))
theorem R45489 : Reach 45489 := rs (se 2 (by rfl) ⟨17058, by rfl⟩) (B 34117 (by norm_num) ⟨17058, by rfl⟩ (by norm_num))
theorem R45493 : Reach 45493 := rs (se 5 (by rfl) ⟨2132, by rfl⟩) (B 4265 (by norm_num) ⟨2132, by rfl⟩ (by norm_num))
theorem R45497 : Reach 45497 := rs (se 2 (by rfl) ⟨17061, by rfl⟩) (B 34123 (by norm_num) ⟨17061, by rfl⟩ (by norm_num))
theorem R45501 : Reach 45501 := rs (se 3 (by rfl) ⟨8531, by rfl⟩) (B 17063 (by norm_num) ⟨8531, by rfl⟩ (by norm_num))
theorem R45505 : Reach 45505 := rs (se 2 (by rfl) ⟨17064, by rfl⟩) (B 34129 (by norm_num) ⟨17064, by rfl⟩ (by norm_num))
theorem R45509 : Reach 45509 := rs (se 4 (by rfl) ⟨4266, by rfl⟩) (B 8533 (by norm_num) ⟨4266, by rfl⟩ (by norm_num))
theorem R45513 : Reach 45513 := rs (se 2 (by rfl) ⟨17067, by rfl⟩) (B 34135 (by norm_num) ⟨17067, by rfl⟩ (by norm_num))
theorem R45517 : Reach 45517 := rs (se 3 (by rfl) ⟨8534, by rfl⟩) (B 17069 (by norm_num) ⟨8534, by rfl⟩ (by norm_num))
theorem R45521 : Reach 45521 := rs (se 2 (by rfl) ⟨17070, by rfl⟩) (B 34141 (by norm_num) ⟨17070, by rfl⟩ (by norm_num))
theorem R45525 : Reach 45525 := rs (se 7 (by rfl) ⟨533, by rfl⟩) (B 1067 (by norm_num) ⟨533, by rfl⟩ (by norm_num))
theorem R78293 : Reach 78293 := rs (se 7 (by rfl) ⟨917, by rfl⟩) (B 1835 (by norm_num) ⟨917, by rfl⟩ (by norm_num))
theorem R45529 : Reach 45529 := rs (se 2 (by rfl) ⟨17073, by rfl⟩) (B 34147 (by norm_num) ⟨17073, by rfl⟩ (by norm_num))
theorem R45533 : Reach 45533 := rs (se 3 (by rfl) ⟨8537, by rfl⟩) (B 17075 (by norm_num) ⟨8537, by rfl⟩ (by norm_num))
theorem R45537 : Reach 45537 := rs (se 2 (by rfl) ⟨17076, by rfl⟩) (B 34153 (by norm_num) ⟨17076, by rfl⟩ (by norm_num))
theorem R45541 : Reach 45541 := rs (se 4 (by rfl) ⟨4269, by rfl⟩) (B 8539 (by norm_num) ⟨4269, by rfl⟩ (by norm_num))
theorem R45545 : Reach 45545 := rs (se 2 (by rfl) ⟨17079, by rfl⟩) (B 34159 (by norm_num) ⟨17079, by rfl⟩ (by norm_num))
theorem R45549 : Reach 45549 := rs (se 3 (by rfl) ⟨8540, by rfl⟩) (B 17081 (by norm_num) ⟨8540, by rfl⟩ (by norm_num))
theorem R45553 : Reach 45553 := rs (se 2 (by rfl) ⟨17082, by rfl⟩) (B 34165 (by norm_num) ⟨17082, by rfl⟩ (by norm_num))
theorem R45557 : Reach 45557 := rs (se 5 (by rfl) ⟨2135, by rfl⟩) (B 4271 (by norm_num) ⟨2135, by rfl⟩ (by norm_num))
theorem R45561 : Reach 45561 := rs (se 2 (by rfl) ⟨17085, by rfl⟩) (B 34171 (by norm_num) ⟨17085, by rfl⟩ (by norm_num))
theorem R45565 : Reach 45565 := rs (se 3 (by rfl) ⟨8543, by rfl⟩) (B 17087 (by norm_num) ⟨8543, by rfl⟩ (by norm_num))
theorem R45569 : Reach 45569 := rs (se 2 (by rfl) ⟨17088, by rfl⟩) (B 34177 (by norm_num) ⟨17088, by rfl⟩ (by norm_num))
theorem R45573 : Reach 45573 := rs (se 4 (by rfl) ⟨4272, by rfl⟩) (B 8545 (by norm_num) ⟨4272, by rfl⟩ (by norm_num))
theorem R45577 : Reach 45577 := rs (se 2 (by rfl) ⟨17091, by rfl⟩) (B 34183 (by norm_num) ⟨17091, by rfl⟩ (by norm_num))
theorem R45581 : Reach 45581 := rs (se 3 (by rfl) ⟨8546, by rfl⟩) (B 17093 (by norm_num) ⟨8546, by rfl⟩ (by norm_num))
theorem R45585 : Reach 45585 := rs (se 2 (by rfl) ⟨17094, by rfl⟩) (B 34189 (by norm_num) ⟨17094, by rfl⟩ (by norm_num))
theorem R45589 : Reach 45589 := rs (se 6 (by rfl) ⟨1068, by rfl⟩) (B 2137 (by norm_num) ⟨1068, by rfl⟩ (by norm_num))
theorem R45593 : Reach 45593 := rs (se 2 (by rfl) ⟨17097, by rfl⟩) (B 34195 (by norm_num) ⟨17097, by rfl⟩ (by norm_num))
theorem R45597 : Reach 45597 := rs (se 3 (by rfl) ⟨8549, by rfl⟩) (B 17099 (by norm_num) ⟨8549, by rfl⟩ (by norm_num))
theorem R45601 : Reach 45601 := rs (se 2 (by rfl) ⟨17100, by rfl⟩) (B 34201 (by norm_num) ⟨17100, by rfl⟩ (by norm_num))
theorem R45605 : Reach 45605 := rs (se 4 (by rfl) ⟨4275, by rfl⟩) (B 8551 (by norm_num) ⟨4275, by rfl⟩ (by norm_num))
theorem R45609 : Reach 45609 := rs (se 2 (by rfl) ⟨17103, by rfl⟩) (B 34207 (by norm_num) ⟨17103, by rfl⟩ (by norm_num))
theorem R45613 : Reach 45613 := rs (se 3 (by rfl) ⟨8552, by rfl⟩) (B 17105 (by norm_num) ⟨8552, by rfl⟩ (by norm_num))
theorem R45617 : Reach 45617 := rs (se 2 (by rfl) ⟨17106, by rfl⟩) (B 34213 (by norm_num) ⟨17106, by rfl⟩ (by norm_num))
theorem R45621 : Reach 45621 := rs (se 5 (by rfl) ⟨2138, by rfl⟩) (B 4277 (by norm_num) ⟨2138, by rfl⟩ (by norm_num))
theorem R45625 : Reach 45625 := rs (se 2 (by rfl) ⟨17109, by rfl⟩) (B 34219 (by norm_num) ⟨17109, by rfl⟩ (by norm_num))
theorem R45629 : Reach 45629 := rs (se 3 (by rfl) ⟨8555, by rfl⟩) (B 17111 (by norm_num) ⟨8555, by rfl⟩ (by norm_num))
theorem R45633 : Reach 45633 := rs (se 2 (by rfl) ⟨17112, by rfl⟩) (B 34225 (by norm_num) ⟨17112, by rfl⟩ (by norm_num))
theorem R45637 : Reach 45637 := rs (se 4 (by rfl) ⟨4278, by rfl⟩) (B 8557 (by norm_num) ⟨4278, by rfl⟩ (by norm_num))
theorem R45641 : Reach 45641 := rs (se 2 (by rfl) ⟨17115, by rfl⟩) (B 34231 (by norm_num) ⟨17115, by rfl⟩ (by norm_num))
theorem R78413 : Reach 78413 := rs (se 3 (by rfl) ⟨14702, by rfl⟩) (B 29405 (by norm_num) ⟨14702, by rfl⟩ (by norm_num))
theorem R45645 : Reach 45645 := rs (se 3 (by rfl) ⟨8558, by rfl⟩) (B 17117 (by norm_num) ⟨8558, by rfl⟩ (by norm_num))
theorem R45649 : Reach 45649 := rs (se 2 (by rfl) ⟨17118, by rfl⟩) (B 34237 (by norm_num) ⟨17118, by rfl⟩ (by norm_num))
theorem R45653 : Reach 45653 := rs (se 8 (by rfl) ⟨267, by rfl⟩) (B 535 (by norm_num) ⟨267, by rfl⟩ (by norm_num))
theorem R78421 : Reach 78421 := rs (se 8 (by rfl) ⟨459, by rfl⟩) (B 919 (by norm_num) ⟨459, by rfl⟩ (by norm_num))
theorem R45657 : Reach 45657 := rs (se 2 (by rfl) ⟨17121, by rfl⟩) (B 34243 (by norm_num) ⟨17121, by rfl⟩ (by norm_num))
theorem R45661 : Reach 45661 := rs (se 3 (by rfl) ⟨8561, by rfl⟩) (B 17123 (by norm_num) ⟨8561, by rfl⟩ (by norm_num))
theorem R45665 : Reach 45665 := rs (se 2 (by rfl) ⟨17124, by rfl⟩) (B 34249 (by norm_num) ⟨17124, by rfl⟩ (by norm_num))
theorem R45669 : Reach 45669 := rs (se 4 (by rfl) ⟨4281, by rfl⟩) (B 8563 (by norm_num) ⟨4281, by rfl⟩ (by norm_num))
theorem R45673 : Reach 45673 := rs (se 2 (by rfl) ⟨17127, by rfl⟩) (B 34255 (by norm_num) ⟨17127, by rfl⟩ (by norm_num))
theorem R45677 : Reach 45677 := rs (se 3 (by rfl) ⟨8564, by rfl⟩) (B 17129 (by norm_num) ⟨8564, by rfl⟩ (by norm_num))
theorem R45681 : Reach 45681 := rs (se 2 (by rfl) ⟨17130, by rfl⟩) (B 34261 (by norm_num) ⟨17130, by rfl⟩ (by norm_num))
theorem R45685 : Reach 45685 := rs (se 5 (by rfl) ⟨2141, by rfl⟩) (B 4283 (by norm_num) ⟨2141, by rfl⟩ (by norm_num))
theorem R45689 : Reach 45689 := rs (se 2 (by rfl) ⟨17133, by rfl⟩) (B 34267 (by norm_num) ⟨17133, by rfl⟩ (by norm_num))
theorem R45693 : Reach 45693 := rs (se 3 (by rfl) ⟨8567, by rfl⟩) (B 17135 (by norm_num) ⟨8567, by rfl⟩ (by norm_num))
theorem R45697 : Reach 45697 := rs (se 2 (by rfl) ⟨17136, by rfl⟩) (B 34273 (by norm_num) ⟨17136, by rfl⟩ (by norm_num))
theorem R45701 : Reach 45701 := rs (se 4 (by rfl) ⟨4284, by rfl⟩) (B 8569 (by norm_num) ⟨4284, by rfl⟩ (by norm_num))
theorem R45705 : Reach 45705 := rs (se 2 (by rfl) ⟨17139, by rfl⟩) (B 34279 (by norm_num) ⟨17139, by rfl⟩ (by norm_num))
theorem R45709 : Reach 45709 := rs (se 3 (by rfl) ⟨8570, by rfl⟩) (B 17141 (by norm_num) ⟨8570, by rfl⟩ (by norm_num))
theorem R45713 : Reach 45713 := rs (se 2 (by rfl) ⟨17142, by rfl⟩) (B 34285 (by norm_num) ⟨17142, by rfl⟩ (by norm_num))
theorem R111253 : Reach 111253 := rs (se 6 (by rfl) ⟨2607, by rfl⟩) (B 5215 (by norm_num) ⟨2607, by rfl⟩ (by norm_num))
theorem R45717 : Reach 45717 := rs (se 6 (by rfl) ⟨1071, by rfl⟩) (B 2143 (by norm_num) ⟨1071, by rfl⟩ (by norm_num))
theorem R45721 : Reach 45721 := rs (se 2 (by rfl) ⟨17145, by rfl⟩) (B 34291 (by norm_num) ⟨17145, by rfl⟩ (by norm_num))
theorem R45725 : Reach 45725 := rs (se 3 (by rfl) ⟨8573, by rfl⟩) (B 17147 (by norm_num) ⟨8573, by rfl⟩ (by norm_num))
theorem R45729 : Reach 45729 := rs (se 2 (by rfl) ⟨17148, by rfl⟩) (B 34297 (by norm_num) ⟨17148, by rfl⟩ (by norm_num))
theorem R45733 : Reach 45733 := rs (se 4 (by rfl) ⟨4287, by rfl⟩) (B 8575 (by norm_num) ⟨4287, by rfl⟩ (by norm_num))
theorem R45737 : Reach 45737 := rs (se 2 (by rfl) ⟨17151, by rfl⟩) (B 34303 (by norm_num) ⟨17151, by rfl⟩ (by norm_num))
theorem R45741 : Reach 45741 := rs (se 3 (by rfl) ⟨8576, by rfl⟩) (B 17153 (by norm_num) ⟨8576, by rfl⟩ (by norm_num))
theorem R78509 : Reach 78509 := rs (se 3 (by rfl) ⟨14720, by rfl⟩) (B 29441 (by norm_num) ⟨14720, by rfl⟩ (by norm_num))
theorem R45745 : Reach 45745 := rs (se 2 (by rfl) ⟨17154, by rfl⟩) (B 34309 (by norm_num) ⟨17154, by rfl⟩ (by norm_num))
theorem R45749 : Reach 45749 := rs (se 5 (by rfl) ⟨2144, by rfl⟩) (B 4289 (by norm_num) ⟨2144, by rfl⟩ (by norm_num))
theorem R45753 : Reach 45753 := rs (se 2 (by rfl) ⟨17157, by rfl⟩) (B 34315 (by norm_num) ⟨17157, by rfl⟩ (by norm_num))
theorem R45757 : Reach 45757 := rs (se 3 (by rfl) ⟨8579, by rfl⟩) (B 17159 (by norm_num) ⟨8579, by rfl⟩ (by norm_num))
theorem R45761 : Reach 45761 := rs (se 2 (by rfl) ⟨17160, by rfl⟩) (B 34321 (by norm_num) ⟨17160, by rfl⟩ (by norm_num))
theorem R45765 : Reach 45765 := rs (se 4 (by rfl) ⟨4290, by rfl⟩) (B 8581 (by norm_num) ⟨4290, by rfl⟩ (by norm_num))
theorem R45769 : Reach 45769 := rs (se 2 (by rfl) ⟨17163, by rfl⟩) (B 34327 (by norm_num) ⟨17163, by rfl⟩ (by norm_num))
theorem R45773 : Reach 45773 := rs (se 3 (by rfl) ⟨8582, by rfl⟩) (B 17165 (by norm_num) ⟨8582, by rfl⟩ (by norm_num))
theorem R45777 : Reach 45777 := rs (se 2 (by rfl) ⟨17166, by rfl⟩) (B 34333 (by norm_num) ⟨17166, by rfl⟩ (by norm_num))
theorem R45781 : Reach 45781 := rs (se 7 (by rfl) ⟨536, by rfl⟩) (B 1073 (by norm_num) ⟨536, by rfl⟩ (by norm_num))
theorem R45785 : Reach 45785 := rs (se 2 (by rfl) ⟨17169, by rfl⟩) (B 34339 (by norm_num) ⟨17169, by rfl⟩ (by norm_num))
theorem R45789 : Reach 45789 := rs (se 3 (by rfl) ⟨8585, by rfl⟩) (B 17171 (by norm_num) ⟨8585, by rfl⟩ (by norm_num))
theorem R45793 : Reach 45793 := rs (se 2 (by rfl) ⟨17172, by rfl⟩) (B 34345 (by norm_num) ⟨17172, by rfl⟩ (by norm_num))
theorem R45797 : Reach 45797 := rs (se 4 (by rfl) ⟨4293, by rfl⟩) (B 8587 (by norm_num) ⟨4293, by rfl⟩ (by norm_num))
theorem R45801 : Reach 45801 := rs (se 2 (by rfl) ⟨17175, by rfl⟩) (B 34351 (by norm_num) ⟨17175, by rfl⟩ (by norm_num))
theorem R45805 : Reach 45805 := rs (se 3 (by rfl) ⟨8588, by rfl⟩) (B 17177 (by norm_num) ⟨8588, by rfl⟩ (by norm_num))
theorem R45809 : Reach 45809 := rs (se 2 (by rfl) ⟨17178, by rfl⟩) (B 34357 (by norm_num) ⟨17178, by rfl⟩ (by norm_num))
theorem R45813 : Reach 45813 := rs (se 5 (by rfl) ⟨2147, by rfl⟩) (B 4295 (by norm_num) ⟨2147, by rfl⟩ (by norm_num))
theorem R45817 : Reach 45817 := rs (se 2 (by rfl) ⟨17181, by rfl⟩) (B 34363 (by norm_num) ⟨17181, by rfl⟩ (by norm_num))
theorem R45821 : Reach 45821 := rs (se 3 (by rfl) ⟨8591, by rfl⟩) (B 17183 (by norm_num) ⟨8591, by rfl⟩ (by norm_num))
theorem R45825 : Reach 45825 := rs (se 2 (by rfl) ⟨17184, by rfl⟩) (B 34369 (by norm_num) ⟨17184, by rfl⟩ (by norm_num))
theorem R111365 : Reach 111365 := rs (se 4 (by rfl) ⟨10440, by rfl⟩) (B 20881 (by norm_num) ⟨10440, by rfl⟩ (by norm_num))
theorem R45829 : Reach 45829 := rs (se 4 (by rfl) ⟨4296, by rfl⟩) (B 8593 (by norm_num) ⟨4296, by rfl⟩ (by norm_num))
theorem R45833 : Reach 45833 := rs (se 2 (by rfl) ⟨17187, by rfl⟩) (B 34375 (by norm_num) ⟨17187, by rfl⟩ (by norm_num))
theorem R45837 : Reach 45837 := rs (se 3 (by rfl) ⟨8594, by rfl⟩) (B 17189 (by norm_num) ⟨8594, by rfl⟩ (by norm_num))
theorem R45841 : Reach 45841 := rs (se 2 (by rfl) ⟨17190, by rfl⟩) (B 34381 (by norm_num) ⟨17190, by rfl⟩ (by norm_num))
theorem R45845 : Reach 45845 := rs (se 6 (by rfl) ⟨1074, by rfl⟩) (B 2149 (by norm_num) ⟨1074, by rfl⟩ (by norm_num))
theorem R45849 : Reach 45849 := rs (se 2 (by rfl) ⟨17193, by rfl⟩) (B 34387 (by norm_num) ⟨17193, by rfl⟩ (by norm_num))
theorem R45853 : Reach 45853 := rs (se 3 (by rfl) ⟨8597, by rfl⟩) (B 17195 (by norm_num) ⟨8597, by rfl⟩ (by norm_num))
theorem R45857 : Reach 45857 := rs (se 2 (by rfl) ⟨17196, by rfl⟩) (B 34393 (by norm_num) ⟨17196, by rfl⟩ (by norm_num))
theorem R45861 : Reach 45861 := rs (se 4 (by rfl) ⟨4299, by rfl⟩) (B 8599 (by norm_num) ⟨4299, by rfl⟩ (by norm_num))
theorem R45865 : Reach 45865 := rs (se 2 (by rfl) ⟨17199, by rfl⟩) (B 34399 (by norm_num) ⟨17199, by rfl⟩ (by norm_num))
theorem R45869 : Reach 45869 := rs (se 3 (by rfl) ⟨8600, by rfl⟩) (B 17201 (by norm_num) ⟨8600, by rfl⟩ (by norm_num))
theorem R78637 : Reach 78637 := rs (se 3 (by rfl) ⟨14744, by rfl⟩) (B 29489 (by norm_num) ⟨14744, by rfl⟩ (by norm_num))
theorem R45873 : Reach 45873 := rs (se 2 (by rfl) ⟨17202, by rfl⟩) (B 34405 (by norm_num) ⟨17202, by rfl⟩ (by norm_num))
theorem R45877 : Reach 45877 := rs (se 5 (by rfl) ⟨2150, by rfl⟩) (B 4301 (by norm_num) ⟨2150, by rfl⟩ (by norm_num))
theorem R45881 : Reach 45881 := rs (se 2 (by rfl) ⟨17205, by rfl⟩) (B 34411 (by norm_num) ⟨17205, by rfl⟩ (by norm_num))
theorem R45885 : Reach 45885 := rs (se 3 (by rfl) ⟨8603, by rfl⟩) (B 17207 (by norm_num) ⟨8603, by rfl⟩ (by norm_num))
theorem R45889 : Reach 45889 := rs (se 2 (by rfl) ⟨17208, by rfl⟩) (B 34417 (by norm_num) ⟨17208, by rfl⟩ (by norm_num))
theorem R45893 : Reach 45893 := rs (se 4 (by rfl) ⟨4302, by rfl⟩) (B 8605 (by norm_num) ⟨4302, by rfl⟩ (by norm_num))
theorem R45897 : Reach 45897 := rs (se 2 (by rfl) ⟨17211, by rfl⟩) (B 34423 (by norm_num) ⟨17211, by rfl⟩ (by norm_num))
theorem R45901 : Reach 45901 := rs (se 3 (by rfl) ⟨8606, by rfl⟩) (B 17213 (by norm_num) ⟨8606, by rfl⟩ (by norm_num))
theorem R45905 : Reach 45905 := rs (se 2 (by rfl) ⟨17214, by rfl⟩) (B 34429 (by norm_num) ⟨17214, by rfl⟩ (by norm_num))
theorem R45909 : Reach 45909 := rs (se 9 (by rfl) ⟨134, by rfl⟩) (B 269 (by norm_num) ⟨134, by rfl⟩ (by norm_num))
theorem R45913 : Reach 45913 := rs (se 2 (by rfl) ⟨17217, by rfl⟩) (B 34435 (by norm_num) ⟨17217, by rfl⟩ (by norm_num))
theorem R45917 : Reach 45917 := rs (se 3 (by rfl) ⟨8609, by rfl⟩) (B 17219 (by norm_num) ⟨8609, by rfl⟩ (by norm_num))
theorem R45921 : Reach 45921 := rs (se 2 (by rfl) ⟨17220, by rfl⟩) (B 34441 (by norm_num) ⟨17220, by rfl⟩ (by norm_num))
theorem R45925 : Reach 45925 := rs (se 4 (by rfl) ⟨4305, by rfl⟩) (B 8611 (by norm_num) ⟨4305, by rfl⟩ (by norm_num))
theorem R45929 : Reach 45929 := rs (se 2 (by rfl) ⟨17223, by rfl⟩) (B 34447 (by norm_num) ⟨17223, by rfl⟩ (by norm_num))
theorem R45933 : Reach 45933 := rs (se 3 (by rfl) ⟨8612, by rfl⟩) (B 17225 (by norm_num) ⟨8612, by rfl⟩ (by norm_num))
theorem R45937 : Reach 45937 := rs (se 2 (by rfl) ⟨17226, by rfl⟩) (B 34453 (by norm_num) ⟨17226, by rfl⟩ (by norm_num))
theorem R45941 : Reach 45941 := rs (se 5 (by rfl) ⟨2153, by rfl⟩) (B 4307 (by norm_num) ⟨2153, by rfl⟩ (by norm_num))
theorem R45945 : Reach 45945 := rs (se 2 (by rfl) ⟨17229, by rfl⟩) (B 34459 (by norm_num) ⟨17229, by rfl⟩ (by norm_num))
theorem R45949 : Reach 45949 := rs (se 3 (by rfl) ⟨8615, by rfl⟩) (B 17231 (by norm_num) ⟨8615, by rfl⟩ (by norm_num))
theorem R45953 : Reach 45953 := rs (se 2 (by rfl) ⟨17232, by rfl⟩) (B 34465 (by norm_num) ⟨17232, by rfl⟩ (by norm_num))
theorem R45957 : Reach 45957 := rs (se 4 (by rfl) ⟨4308, by rfl⟩) (B 8617 (by norm_num) ⟨4308, by rfl⟩ (by norm_num))
theorem R78725 : Reach 78725 := rs (se 4 (by rfl) ⟨7380, by rfl⟩) (B 14761 (by norm_num) ⟨7380, by rfl⟩ (by norm_num))
theorem R45961 : Reach 45961 := rs (se 2 (by rfl) ⟨17235, by rfl⟩) (B 34471 (by norm_num) ⟨17235, by rfl⟩ (by norm_num))
theorem R45965 : Reach 45965 := rs (se 3 (by rfl) ⟨8618, by rfl⟩) (B 17237 (by norm_num) ⟨8618, by rfl⟩ (by norm_num))
theorem R45969 : Reach 45969 := rs (se 2 (by rfl) ⟨17238, by rfl⟩) (B 34477 (by norm_num) ⟨17238, by rfl⟩ (by norm_num))
theorem R45973 : Reach 45973 := rs (se 6 (by rfl) ⟨1077, by rfl⟩) (B 2155 (by norm_num) ⟨1077, by rfl⟩ (by norm_num))
theorem R45977 : Reach 45977 := rs (se 2 (by rfl) ⟨17241, by rfl⟩) (B 34483 (by norm_num) ⟨17241, by rfl⟩ (by norm_num))
theorem R45981 : Reach 45981 := rs (se 3 (by rfl) ⟨8621, by rfl⟩) (B 17243 (by norm_num) ⟨8621, by rfl⟩ (by norm_num))
theorem R45985 : Reach 45985 := rs (se 2 (by rfl) ⟨17244, by rfl⟩) (B 34489 (by norm_num) ⟨17244, by rfl⟩ (by norm_num))
theorem R45989 : Reach 45989 := rs (se 4 (by rfl) ⟨4311, by rfl⟩) (B 8623 (by norm_num) ⟨4311, by rfl⟩ (by norm_num))
theorem R45993 : Reach 45993 := rs (se 2 (by rfl) ⟨17247, by rfl⟩) (B 34495 (by norm_num) ⟨17247, by rfl⟩ (by norm_num))
theorem R45997 : Reach 45997 := rs (se 3 (by rfl) ⟨8624, by rfl⟩) (B 17249 (by norm_num) ⟨8624, by rfl⟩ (by norm_num))
theorem R46001 : Reach 46001 := rs (se 2 (by rfl) ⟨17250, by rfl⟩) (B 34501 (by norm_num) ⟨17250, by rfl⟩ (by norm_num))
theorem R46005 : Reach 46005 := rs (se 5 (by rfl) ⟨2156, by rfl⟩) (B 4313 (by norm_num) ⟨2156, by rfl⟩ (by norm_num))
theorem R46009 : Reach 46009 := rs (se 2 (by rfl) ⟨17253, by rfl⟩) (B 34507 (by norm_num) ⟨17253, by rfl⟩ (by norm_num))
theorem R46013 : Reach 46013 := rs (se 3 (by rfl) ⟨8627, by rfl⟩) (B 17255 (by norm_num) ⟨8627, by rfl⟩ (by norm_num))
theorem R46017 : Reach 46017 := rs (se 2 (by rfl) ⟨17256, by rfl⟩) (B 34513 (by norm_num) ⟨17256, by rfl⟩ (by norm_num))
theorem R111557 : Reach 111557 := rs (se 4 (by rfl) ⟨10458, by rfl⟩) (B 20917 (by norm_num) ⟨10458, by rfl⟩ (by norm_num))
theorem R46021 : Reach 46021 := rs (se 4 (by rfl) ⟨4314, by rfl⟩) (B 8629 (by norm_num) ⟨4314, by rfl⟩ (by norm_num))
theorem R46025 : Reach 46025 := rs (se 2 (by rfl) ⟨17259, by rfl⟩) (B 34519 (by norm_num) ⟨17259, by rfl⟩ (by norm_num))
theorem R46029 : Reach 46029 := rs (se 3 (by rfl) ⟨8630, by rfl⟩) (B 17261 (by norm_num) ⟨8630, by rfl⟩ (by norm_num))
theorem R46033 : Reach 46033 := rs (se 2 (by rfl) ⟨17262, by rfl⟩) (B 34525 (by norm_num) ⟨17262, by rfl⟩ (by norm_num))
theorem R46037 : Reach 46037 := rs (se 7 (by rfl) ⟨539, by rfl⟩) (B 1079 (by norm_num) ⟨539, by rfl⟩ (by norm_num))
theorem R46041 : Reach 46041 := rs (se 2 (by rfl) ⟨17265, by rfl⟩) (B 34531 (by norm_num) ⟨17265, by rfl⟩ (by norm_num))
theorem R46045 : Reach 46045 := rs (se 3 (by rfl) ⟨8633, by rfl⟩) (B 17267 (by norm_num) ⟨8633, by rfl⟩ (by norm_num))
theorem R46049 : Reach 46049 := rs (se 2 (by rfl) ⟨17268, by rfl⟩) (B 34537 (by norm_num) ⟨17268, by rfl⟩ (by norm_num))
theorem R46053 : Reach 46053 := rs (se 4 (by rfl) ⟨4317, by rfl⟩) (B 8635 (by norm_num) ⟨4317, by rfl⟩ (by norm_num))
theorem R46057 : Reach 46057 := rs (se 2 (by rfl) ⟨17271, by rfl⟩) (B 34543 (by norm_num) ⟨17271, by rfl⟩ (by norm_num))
theorem R46061 : Reach 46061 := rs (se 3 (by rfl) ⟨8636, by rfl⟩) (B 17273 (by norm_num) ⟨8636, by rfl⟩ (by norm_num))
theorem R46065 : Reach 46065 := rs (se 2 (by rfl) ⟨17274, by rfl⟩) (B 34549 (by norm_num) ⟨17274, by rfl⟩ (by norm_num))
theorem R46069 : Reach 46069 := rs (se 5 (by rfl) ⟨2159, by rfl⟩) (B 4319 (by norm_num) ⟨2159, by rfl⟩ (by norm_num))
theorem R46073 : Reach 46073 := rs (se 2 (by rfl) ⟨17277, by rfl⟩) (B 34555 (by norm_num) ⟨17277, by rfl⟩ (by norm_num))
theorem R46077 : Reach 46077 := rs (se 3 (by rfl) ⟨8639, by rfl⟩) (B 17279 (by norm_num) ⟨8639, by rfl⟩ (by norm_num))
theorem R46081 : Reach 46081 := rs (se 2 (by rfl) ⟨17280, by rfl⟩) (B 34561 (by norm_num) ⟨17280, by rfl⟩ (by norm_num))
theorem R46085 : Reach 46085 := rs (se 4 (by rfl) ⟨4320, by rfl⟩) (B 8641 (by norm_num) ⟨4320, by rfl⟩ (by norm_num))
theorem R78853 : Reach 78853 := rs (se 4 (by rfl) ⟨7392, by rfl⟩) (B 14785 (by norm_num) ⟨7392, by rfl⟩ (by norm_num))
theorem R46089 : Reach 46089 := rs (se 2 (by rfl) ⟨17283, by rfl⟩) (B 34567 (by norm_num) ⟨17283, by rfl⟩ (by norm_num))
theorem R46093 : Reach 46093 := rs (se 3 (by rfl) ⟨8642, by rfl⟩) (B 17285 (by norm_num) ⟨8642, by rfl⟩ (by norm_num))
theorem R46097 : Reach 46097 := rs (se 2 (by rfl) ⟨17286, by rfl⟩) (B 34573 (by norm_num) ⟨17286, by rfl⟩ (by norm_num))
theorem R46101 : Reach 46101 := rs (se 6 (by rfl) ⟨1080, by rfl⟩) (B 2161 (by norm_num) ⟨1080, by rfl⟩ (by norm_num))
theorem R46105 : Reach 46105 := rs (se 2 (by rfl) ⟨17289, by rfl⟩) (B 34579 (by norm_num) ⟨17289, by rfl⟩ (by norm_num))
theorem R46109 : Reach 46109 := rs (se 3 (by rfl) ⟨8645, by rfl⟩) (B 17291 (by norm_num) ⟨8645, by rfl⟩ (by norm_num))
theorem R46113 : Reach 46113 := rs (se 2 (by rfl) ⟨17292, by rfl⟩) (B 34585 (by norm_num) ⟨17292, by rfl⟩ (by norm_num))
theorem R46117 : Reach 46117 := rs (se 4 (by rfl) ⟨4323, by rfl⟩) (B 8647 (by norm_num) ⟨4323, by rfl⟩ (by norm_num))
theorem R46121 : Reach 46121 := rs (se 2 (by rfl) ⟨17295, by rfl⟩) (B 34591 (by norm_num) ⟨17295, by rfl⟩ (by norm_num))
theorem R46125 : Reach 46125 := rs (se 3 (by rfl) ⟨8648, by rfl⟩) (B 17297 (by norm_num) ⟨8648, by rfl⟩ (by norm_num))
theorem R46129 : Reach 46129 := rs (se 2 (by rfl) ⟨17298, by rfl⟩) (B 34597 (by norm_num) ⟨17298, by rfl⟩ (by norm_num))
theorem R46133 : Reach 46133 := rs (se 5 (by rfl) ⟨2162, by rfl⟩) (B 4325 (by norm_num) ⟨2162, by rfl⟩ (by norm_num))
theorem R46137 : Reach 46137 := rs (se 2 (by rfl) ⟨17301, by rfl⟩) (B 34603 (by norm_num) ⟨17301, by rfl⟩ (by norm_num))
theorem R46141 : Reach 46141 := rs (se 3 (by rfl) ⟨8651, by rfl⟩) (B 17303 (by norm_num) ⟨8651, by rfl⟩ (by norm_num))
theorem R46145 : Reach 46145 := rs (se 2 (by rfl) ⟨17304, by rfl⟩) (B 34609 (by norm_num) ⟨17304, by rfl⟩ (by norm_num))
theorem R46149 : Reach 46149 := rs (se 4 (by rfl) ⟨4326, by rfl⟩) (B 8653 (by norm_num) ⟨4326, by rfl⟩ (by norm_num))
theorem R46153 : Reach 46153 := rs (se 2 (by rfl) ⟨17307, by rfl⟩) (B 34615 (by norm_num) ⟨17307, by rfl⟩ (by norm_num))
theorem R46157 : Reach 46157 := rs (se 3 (by rfl) ⟨8654, by rfl⟩) (B 17309 (by norm_num) ⟨8654, by rfl⟩ (by norm_num))
theorem R46161 : Reach 46161 := rs (se 2 (by rfl) ⟨17310, by rfl⟩) (B 34621 (by norm_num) ⟨17310, by rfl⟩ (by norm_num))
theorem R46165 : Reach 46165 := rs (se 8 (by rfl) ⟨270, by rfl⟩) (B 541 (by norm_num) ⟨270, by rfl⟩ (by norm_num))
theorem R46169 : Reach 46169 := rs (se 2 (by rfl) ⟨17313, by rfl⟩) (B 34627 (by norm_num) ⟨17313, by rfl⟩ (by norm_num))
theorem R46173 : Reach 46173 := rs (se 3 (by rfl) ⟨8657, by rfl⟩) (B 17315 (by norm_num) ⟨8657, by rfl⟩ (by norm_num))
theorem R78941 : Reach 78941 := rs (se 3 (by rfl) ⟨14801, by rfl⟩) (B 29603 (by norm_num) ⟨14801, by rfl⟩ (by norm_num))
theorem R46177 : Reach 46177 := rs (se 2 (by rfl) ⟨17316, by rfl⟩) (B 34633 (by norm_num) ⟨17316, by rfl⟩ (by norm_num))
theorem R46181 : Reach 46181 := rs (se 4 (by rfl) ⟨4329, by rfl⟩) (B 8659 (by norm_num) ⟨4329, by rfl⟩ (by norm_num))
theorem R46185 : Reach 46185 := rs (se 2 (by rfl) ⟨17319, by rfl⟩) (B 34639 (by norm_num) ⟨17319, by rfl⟩ (by norm_num))
theorem R46189 : Reach 46189 := rs (se 3 (by rfl) ⟨8660, by rfl⟩) (B 17321 (by norm_num) ⟨8660, by rfl⟩ (by norm_num))
theorem R46193 : Reach 46193 := rs (se 2 (by rfl) ⟨17322, by rfl⟩) (B 34645 (by norm_num) ⟨17322, by rfl⟩ (by norm_num))
theorem R46197 : Reach 46197 := rs (se 5 (by rfl) ⟨2165, by rfl⟩) (B 4331 (by norm_num) ⟨2165, by rfl⟩ (by norm_num))
theorem R46201 : Reach 46201 := rs (se 2 (by rfl) ⟨17325, by rfl⟩) (B 34651 (by norm_num) ⟨17325, by rfl⟩ (by norm_num))
theorem R46205 : Reach 46205 := rs (se 3 (by rfl) ⟨8663, by rfl⟩) (B 17327 (by norm_num) ⟨8663, by rfl⟩ (by norm_num))
theorem R46209 : Reach 46209 := rs (se 2 (by rfl) ⟨17328, by rfl⟩) (B 34657 (by norm_num) ⟨17328, by rfl⟩ (by norm_num))
theorem R46213 : Reach 46213 := rs (se 4 (by rfl) ⟨4332, by rfl⟩) (B 8665 (by norm_num) ⟨4332, by rfl⟩ (by norm_num))
theorem R46217 : Reach 46217 := rs (se 2 (by rfl) ⟨17331, by rfl⟩) (B 34663 (by norm_num) ⟨17331, by rfl⟩ (by norm_num))
theorem R46221 : Reach 46221 := rs (se 3 (by rfl) ⟨8666, by rfl⟩) (B 17333 (by norm_num) ⟨8666, by rfl⟩ (by norm_num))
theorem R46225 : Reach 46225 := rs (se 2 (by rfl) ⟨17334, by rfl⟩) (B 34669 (by norm_num) ⟨17334, by rfl⟩ (by norm_num))
theorem R46229 : Reach 46229 := rs (se 6 (by rfl) ⟨1083, by rfl⟩) (B 2167 (by norm_num) ⟨1083, by rfl⟩ (by norm_num))
theorem R46233 : Reach 46233 := rs (se 2 (by rfl) ⟨17337, by rfl⟩) (B 34675 (by norm_num) ⟨17337, by rfl⟩ (by norm_num))
theorem R46237 : Reach 46237 := rs (se 3 (by rfl) ⟨8669, by rfl⟩) (B 17339 (by norm_num) ⟨8669, by rfl⟩ (by norm_num))
theorem R46241 : Reach 46241 := rs (se 2 (by rfl) ⟨17340, by rfl⟩) (B 34681 (by norm_num) ⟨17340, by rfl⟩ (by norm_num))
theorem R46245 : Reach 46245 := rs (se 4 (by rfl) ⟨4335, by rfl⟩) (B 8671 (by norm_num) ⟨4335, by rfl⟩ (by norm_num))
theorem R46249 : Reach 46249 := rs (se 2 (by rfl) ⟨17343, by rfl⟩) (B 34687 (by norm_num) ⟨17343, by rfl⟩ (by norm_num))
theorem R46253 : Reach 46253 := rs (se 3 (by rfl) ⟨8672, by rfl⟩) (B 17345 (by norm_num) ⟨8672, by rfl⟩ (by norm_num))
theorem R46257 : Reach 46257 := rs (se 2 (by rfl) ⟨17346, by rfl⟩) (B 34693 (by norm_num) ⟨17346, by rfl⟩ (by norm_num))
theorem R46261 : Reach 46261 := rs (se 5 (by rfl) ⟨2168, by rfl⟩) (B 4337 (by norm_num) ⟨2168, by rfl⟩ (by norm_num))
theorem R46265 : Reach 46265 := rs (se 2 (by rfl) ⟨17349, by rfl⟩) (B 34699 (by norm_num) ⟨17349, by rfl⟩ (by norm_num))
theorem R46269 : Reach 46269 := rs (se 3 (by rfl) ⟨8675, by rfl⟩) (B 17351 (by norm_num) ⟨8675, by rfl⟩ (by norm_num))
theorem R46273 : Reach 46273 := rs (se 2 (by rfl) ⟨17352, by rfl⟩) (B 34705 (by norm_num) ⟨17352, by rfl⟩ (by norm_num))
theorem R177349 : Reach 177349 := rs (se 4 (by rfl) ⟨16626, by rfl⟩) (B 33253 (by norm_num) ⟨16626, by rfl⟩ (by norm_num))
theorem R46277 : Reach 46277 := rs (se 4 (by rfl) ⟨4338, by rfl⟩) (B 8677 (by norm_num) ⟨4338, by rfl⟩ (by norm_num))
theorem R46281 : Reach 46281 := rs (se 2 (by rfl) ⟨17355, by rfl⟩) (B 34711 (by norm_num) ⟨17355, by rfl⟩ (by norm_num))
theorem R46285 : Reach 46285 := rs (se 3 (by rfl) ⟨8678, by rfl⟩) (B 17357 (by norm_num) ⟨8678, by rfl⟩ (by norm_num))
theorem R46289 : Reach 46289 := rs (se 2 (by rfl) ⟨17358, by rfl⟩) (B 34717 (by norm_num) ⟨17358, by rfl⟩ (by norm_num))
theorem R46293 : Reach 46293 := rs (se 7 (by rfl) ⟨542, by rfl⟩) (B 1085 (by norm_num) ⟨542, by rfl⟩ (by norm_num))
theorem R46297 : Reach 46297 := rs (se 2 (by rfl) ⟨17361, by rfl⟩) (B 34723 (by norm_num) ⟨17361, by rfl⟩ (by norm_num))
theorem R46301 : Reach 46301 := rs (se 3 (by rfl) ⟨8681, by rfl⟩) (B 17363 (by norm_num) ⟨8681, by rfl⟩ (by norm_num))
theorem R79069 : Reach 79069 := rs (se 3 (by rfl) ⟨14825, by rfl⟩) (B 29651 (by norm_num) ⟨14825, by rfl⟩ (by norm_num))
theorem R46305 : Reach 46305 := rs (se 2 (by rfl) ⟨17364, by rfl⟩) (B 34729 (by norm_num) ⟨17364, by rfl⟩ (by norm_num))
theorem R46309 : Reach 46309 := rs (se 4 (by rfl) ⟨4341, by rfl⟩) (B 8683 (by norm_num) ⟨4341, by rfl⟩ (by norm_num))
theorem R46313 : Reach 46313 := rs (se 2 (by rfl) ⟨17367, by rfl⟩) (B 34735 (by norm_num) ⟨17367, by rfl⟩ (by norm_num))
theorem R46317 : Reach 46317 := rs (se 3 (by rfl) ⟨8684, by rfl⟩) (B 17369 (by norm_num) ⟨8684, by rfl⟩ (by norm_num))
theorem R46321 : Reach 46321 := rs (se 2 (by rfl) ⟨17370, by rfl⟩) (B 34741 (by norm_num) ⟨17370, by rfl⟩ (by norm_num))
theorem R46325 : Reach 46325 := rs (se 5 (by rfl) ⟨2171, by rfl⟩) (B 4343 (by norm_num) ⟨2171, by rfl⟩ (by norm_num))
theorem R46329 : Reach 46329 := rs (se 2 (by rfl) ⟨17373, by rfl⟩) (B 34747 (by norm_num) ⟨17373, by rfl⟩ (by norm_num))
theorem R46333 : Reach 46333 := rs (se 3 (by rfl) ⟨8687, by rfl⟩) (B 17375 (by norm_num) ⟨8687, by rfl⟩ (by norm_num))
theorem R46337 : Reach 46337 := rs (se 2 (by rfl) ⟨17376, by rfl⟩) (B 34753 (by norm_num) ⟨17376, by rfl⟩ (by norm_num))
theorem R46341 : Reach 46341 := rs (se 4 (by rfl) ⟨4344, by rfl⟩) (B 8689 (by norm_num) ⟨4344, by rfl⟩ (by norm_num))
theorem R46345 : Reach 46345 := rs (se 2 (by rfl) ⟨17379, by rfl⟩) (B 34759 (by norm_num) ⟨17379, by rfl⟩ (by norm_num))
theorem R46349 : Reach 46349 := rs (se 3 (by rfl) ⟨8690, by rfl⟩) (B 17381 (by norm_num) ⟨8690, by rfl⟩ (by norm_num))
theorem R46353 : Reach 46353 := rs (se 2 (by rfl) ⟨17382, by rfl⟩) (B 34765 (by norm_num) ⟨17382, by rfl⟩ (by norm_num))
theorem R46357 : Reach 46357 := rs (se 6 (by rfl) ⟨1086, by rfl⟩) (B 2173 (by norm_num) ⟨1086, by rfl⟩ (by norm_num))
theorem R46361 : Reach 46361 := rs (se 2 (by rfl) ⟨17385, by rfl⟩) (B 34771 (by norm_num) ⟨17385, by rfl⟩ (by norm_num))
theorem R111901 : Reach 111901 := rs (se 3 (by rfl) ⟨20981, by rfl⟩) (B 41963 (by norm_num) ⟨20981, by rfl⟩ (by norm_num))
theorem R46365 : Reach 46365 := rs (se 3 (by rfl) ⟨8693, by rfl⟩) (B 17387 (by norm_num) ⟨8693, by rfl⟩ (by norm_num))
theorem R46369 : Reach 46369 := rs (se 2 (by rfl) ⟨17388, by rfl⟩) (B 34777 (by norm_num) ⟨17388, by rfl⟩ (by norm_num))
theorem R46373 : Reach 46373 := rs (se 4 (by rfl) ⟨4347, by rfl⟩) (B 8695 (by norm_num) ⟨4347, by rfl⟩ (by norm_num))
theorem R46377 : Reach 46377 := rs (se 2 (by rfl) ⟨17391, by rfl⟩) (B 34783 (by norm_num) ⟨17391, by rfl⟩ (by norm_num))
theorem R46381 : Reach 46381 := rs (se 3 (by rfl) ⟨8696, by rfl⟩) (B 17393 (by norm_num) ⟨8696, by rfl⟩ (by norm_num))
theorem R46385 : Reach 46385 := rs (se 2 (by rfl) ⟨17394, by rfl⟩) (B 34789 (by norm_num) ⟨17394, by rfl⟩ (by norm_num))
theorem R46389 : Reach 46389 := rs (se 5 (by rfl) ⟨2174, by rfl⟩) (B 4349 (by norm_num) ⟨2174, by rfl⟩ (by norm_num))
theorem R79157 : Reach 79157 := rs (se 5 (by rfl) ⟨3710, by rfl⟩) (B 7421 (by norm_num) ⟨3710, by rfl⟩ (by norm_num))
theorem R46393 : Reach 46393 := rs (se 2 (by rfl) ⟨17397, by rfl⟩) (B 34795 (by norm_num) ⟨17397, by rfl⟩ (by norm_num))
theorem R46397 : Reach 46397 := rs (se 3 (by rfl) ⟨8699, by rfl⟩) (B 17399 (by norm_num) ⟨8699, by rfl⟩ (by norm_num))
theorem R46401 : Reach 46401 := rs (se 2 (by rfl) ⟨17400, by rfl⟩) (B 34801 (by norm_num) ⟨17400, by rfl⟩ (by norm_num))
theorem R46405 : Reach 46405 := rs (se 4 (by rfl) ⟨4350, by rfl⟩) (B 8701 (by norm_num) ⟨4350, by rfl⟩ (by norm_num))
theorem R46409 : Reach 46409 := rs (se 2 (by rfl) ⟨17403, by rfl⟩) (B 34807 (by norm_num) ⟨17403, by rfl⟩ (by norm_num))
theorem R46413 : Reach 46413 := rs (se 3 (by rfl) ⟨8702, by rfl⟩) (B 17405 (by norm_num) ⟨8702, by rfl⟩ (by norm_num))
theorem R46417 : Reach 46417 := rs (se 2 (by rfl) ⟨17406, by rfl⟩) (B 34813 (by norm_num) ⟨17406, by rfl⟩ (by norm_num))
theorem R46421 : Reach 46421 := rs (se 13 (by rfl) ⟨8, by rfl⟩) (B 17 (by norm_num) ⟨8, by rfl⟩ (by norm_num))
theorem R46425 : Reach 46425 := rs (se 2 (by rfl) ⟨17409, by rfl⟩) (B 34819 (by norm_num) ⟨17409, by rfl⟩ (by norm_num))
theorem R46429 : Reach 46429 := rs (se 3 (by rfl) ⟨8705, by rfl⟩) (B 17411 (by norm_num) ⟨8705, by rfl⟩ (by norm_num))
theorem R46433 : Reach 46433 := rs (se 2 (by rfl) ⟨17412, by rfl⟩) (B 34825 (by norm_num) ⟨17412, by rfl⟩ (by norm_num))
theorem R46437 : Reach 46437 := rs (se 4 (by rfl) ⟨4353, by rfl⟩) (B 8707 (by norm_num) ⟨4353, by rfl⟩ (by norm_num))
theorem R46441 : Reach 46441 := rs (se 2 (by rfl) ⟨17415, by rfl⟩) (B 34831 (by norm_num) ⟨17415, by rfl⟩ (by norm_num))
theorem R46445 : Reach 46445 := rs (se 3 (by rfl) ⟨8708, by rfl⟩) (B 17417 (by norm_num) ⟨8708, by rfl⟩ (by norm_num))
theorem R46449 : Reach 46449 := rs (se 2 (by rfl) ⟨17418, by rfl⟩) (B 34837 (by norm_num) ⟨17418, by rfl⟩ (by norm_num))
theorem R46453 : Reach 46453 := rs (se 5 (by rfl) ⟨2177, by rfl⟩) (B 4355 (by norm_num) ⟨2177, by rfl⟩ (by norm_num))
theorem R46457 : Reach 46457 := rs (se 2 (by rfl) ⟨17421, by rfl⟩) (B 34843 (by norm_num) ⟨17421, by rfl⟩ (by norm_num))
theorem R46461 : Reach 46461 := rs (se 3 (by rfl) ⟨8711, by rfl⟩) (B 17423 (by norm_num) ⟨8711, by rfl⟩ (by norm_num))
theorem R46465 : Reach 46465 := rs (se 2 (by rfl) ⟨17424, by rfl⟩) (B 34849 (by norm_num) ⟨17424, by rfl⟩ (by norm_num))
theorem R46469 : Reach 46469 := rs (se 4 (by rfl) ⟨4356, by rfl⟩) (B 8713 (by norm_num) ⟨4356, by rfl⟩ (by norm_num))
theorem R46473 : Reach 46473 := rs (se 2 (by rfl) ⟨17427, by rfl⟩) (B 34855 (by norm_num) ⟨17427, by rfl⟩ (by norm_num))
theorem R112013 : Reach 112013 := rs (se 3 (by rfl) ⟨21002, by rfl⟩) (B 42005 (by norm_num) ⟨21002, by rfl⟩ (by norm_num))
theorem R46477 : Reach 46477 := rs (se 3 (by rfl) ⟨8714, by rfl⟩) (B 17429 (by norm_num) ⟨8714, by rfl⟩ (by norm_num))
theorem R46481 : Reach 46481 := rs (se 2 (by rfl) ⟨17430, by rfl⟩) (B 34861 (by norm_num) ⟨17430, by rfl⟩ (by norm_num))
theorem R46485 : Reach 46485 := rs (se 6 (by rfl) ⟨1089, by rfl⟩) (B 2179 (by norm_num) ⟨1089, by rfl⟩ (by norm_num))
theorem R46489 : Reach 46489 := rs (se 2 (by rfl) ⟨17433, by rfl⟩) (B 34867 (by norm_num) ⟨17433, by rfl⟩ (by norm_num))
theorem R46493 : Reach 46493 := rs (se 3 (by rfl) ⟨8717, by rfl⟩) (B 17435 (by norm_num) ⟨8717, by rfl⟩ (by norm_num))
theorem R46497 : Reach 46497 := rs (se 2 (by rfl) ⟨17436, by rfl⟩) (B 34873 (by norm_num) ⟨17436, by rfl⟩ (by norm_num))
theorem R46501 : Reach 46501 := rs (se 4 (by rfl) ⟨4359, by rfl⟩) (B 8719 (by norm_num) ⟨4359, by rfl⟩ (by norm_num))
theorem R46505 : Reach 46505 := rs (se 2 (by rfl) ⟨17439, by rfl⟩) (B 34879 (by norm_num) ⟨17439, by rfl⟩ (by norm_num))
theorem R46509 : Reach 46509 := rs (se 3 (by rfl) ⟨8720, by rfl⟩) (B 17441 (by norm_num) ⟨8720, by rfl⟩ (by norm_num))
theorem R46513 : Reach 46513 := rs (se 2 (by rfl) ⟨17442, by rfl⟩) (B 34885 (by norm_num) ⟨17442, by rfl⟩ (by norm_num))
theorem R46517 : Reach 46517 := rs (se 5 (by rfl) ⟨2180, by rfl⟩) (B 4361 (by norm_num) ⟨2180, by rfl⟩ (by norm_num))
theorem R79285 : Reach 79285 := rs (se 5 (by rfl) ⟨3716, by rfl⟩) (B 7433 (by norm_num) ⟨3716, by rfl⟩ (by norm_num))
theorem R46521 : Reach 46521 := rs (se 2 (by rfl) ⟨17445, by rfl⟩) (B 34891 (by norm_num) ⟨17445, by rfl⟩ (by norm_num))
theorem R46525 : Reach 46525 := rs (se 3 (by rfl) ⟨8723, by rfl⟩) (B 17447 (by norm_num) ⟨8723, by rfl⟩ (by norm_num))
theorem R46529 : Reach 46529 := rs (se 2 (by rfl) ⟨17448, by rfl⟩) (B 34897 (by norm_num) ⟨17448, by rfl⟩ (by norm_num))
theorem R46533 : Reach 46533 := rs (se 4 (by rfl) ⟨4362, by rfl⟩) (B 8725 (by norm_num) ⟨4362, by rfl⟩ (by norm_num))
theorem R46537 : Reach 46537 := rs (se 2 (by rfl) ⟨17451, by rfl⟩) (B 34903 (by norm_num) ⟨17451, by rfl⟩ (by norm_num))
theorem R46541 : Reach 46541 := rs (se 3 (by rfl) ⟨8726, by rfl⟩) (B 17453 (by norm_num) ⟨8726, by rfl⟩ (by norm_num))
theorem R46545 : Reach 46545 := rs (se 2 (by rfl) ⟨17454, by rfl⟩) (B 34909 (by norm_num) ⟨17454, by rfl⟩ (by norm_num))
theorem R46549 : Reach 46549 := rs (se 7 (by rfl) ⟨545, by rfl⟩) (B 1091 (by norm_num) ⟨545, by rfl⟩ (by norm_num))
theorem R46553 : Reach 46553 := rs (se 2 (by rfl) ⟨17457, by rfl⟩) (B 34915 (by norm_num) ⟨17457, by rfl⟩ (by norm_num))
theorem R46557 : Reach 46557 := rs (se 3 (by rfl) ⟨8729, by rfl⟩) (B 17459 (by norm_num) ⟨8729, by rfl⟩ (by norm_num))
theorem R46561 : Reach 46561 := rs (se 2 (by rfl) ⟨17460, by rfl⟩) (B 34921 (by norm_num) ⟨17460, by rfl⟩ (by norm_num))
theorem R46565 : Reach 46565 := rs (se 4 (by rfl) ⟨4365, by rfl⟩) (B 8731 (by norm_num) ⟨4365, by rfl⟩ (by norm_num))
theorem R46569 : Reach 46569 := rs (se 2 (by rfl) ⟨17463, by rfl⟩) (B 34927 (by norm_num) ⟨17463, by rfl⟩ (by norm_num))
theorem R46573 : Reach 46573 := rs (se 3 (by rfl) ⟨8732, by rfl⟩) (B 17465 (by norm_num) ⟨8732, by rfl⟩ (by norm_num))
theorem R46577 : Reach 46577 := rs (se 2 (by rfl) ⟨17466, by rfl⟩) (B 34933 (by norm_num) ⟨17466, by rfl⟩ (by norm_num))
theorem R46581 : Reach 46581 := rs (se 5 (by rfl) ⟨2183, by rfl⟩) (B 4367 (by norm_num) ⟨2183, by rfl⟩ (by norm_num))
theorem R46585 : Reach 46585 := rs (se 2 (by rfl) ⟨17469, by rfl⟩) (B 34939 (by norm_num) ⟨17469, by rfl⟩ (by norm_num))
theorem R46589 : Reach 46589 := rs (se 3 (by rfl) ⟨8735, by rfl⟩) (B 17471 (by norm_num) ⟨8735, by rfl⟩ (by norm_num))
theorem R46593 : Reach 46593 := rs (se 2 (by rfl) ⟨17472, by rfl⟩) (B 34945 (by norm_num) ⟨17472, by rfl⟩ (by norm_num))
theorem R46597 : Reach 46597 := rs (se 4 (by rfl) ⟨4368, by rfl⟩) (B 8737 (by norm_num) ⟨4368, by rfl⟩ (by norm_num))
theorem R46601 : Reach 46601 := rs (se 2 (by rfl) ⟨17475, by rfl⟩) (B 34951 (by norm_num) ⟨17475, by rfl⟩ (by norm_num))
theorem R46605 : Reach 46605 := rs (se 3 (by rfl) ⟨8738, by rfl⟩) (B 17477 (by norm_num) ⟨8738, by rfl⟩ (by norm_num))
theorem R79373 : Reach 79373 := rs (se 3 (by rfl) ⟨14882, by rfl⟩) (B 29765 (by norm_num) ⟨14882, by rfl⟩ (by norm_num))
theorem R46609 : Reach 46609 := rs (se 2 (by rfl) ⟨17478, by rfl⟩) (B 34957 (by norm_num) ⟨17478, by rfl⟩ (by norm_num))
theorem R46613 : Reach 46613 := rs (se 6 (by rfl) ⟨1092, by rfl⟩) (B 2185 (by norm_num) ⟨1092, by rfl⟩ (by norm_num))
theorem R46617 : Reach 46617 := rs (se 2 (by rfl) ⟨17481, by rfl⟩) (B 34963 (by norm_num) ⟨17481, by rfl⟩ (by norm_num))
theorem R46621 : Reach 46621 := rs (se 3 (by rfl) ⟨8741, by rfl⟩) (B 17483 (by norm_num) ⟨8741, by rfl⟩ (by norm_num))
theorem R46625 : Reach 46625 := rs (se 2 (by rfl) ⟨17484, by rfl⟩) (B 34969 (by norm_num) ⟨17484, by rfl⟩ (by norm_num))
theorem R46629 : Reach 46629 := rs (se 4 (by rfl) ⟨4371, by rfl⟩) (B 8743 (by norm_num) ⟨4371, by rfl⟩ (by norm_num))
theorem R46633 : Reach 46633 := rs (se 2 (by rfl) ⟨17487, by rfl⟩) (B 34975 (by norm_num) ⟨17487, by rfl⟩ (by norm_num))
theorem R46637 : Reach 46637 := rs (se 3 (by rfl) ⟨8744, by rfl⟩) (B 17489 (by norm_num) ⟨8744, by rfl⟩ (by norm_num))
theorem R46641 : Reach 46641 := rs (se 2 (by rfl) ⟨17490, by rfl⟩) (B 34981 (by norm_num) ⟨17490, by rfl⟩ (by norm_num))
theorem R46645 : Reach 46645 := rs (se 5 (by rfl) ⟨2186, by rfl⟩) (B 4373 (by norm_num) ⟨2186, by rfl⟩ (by norm_num))
theorem R46649 : Reach 46649 := rs (se 2 (by rfl) ⟨17493, by rfl⟩) (B 34987 (by norm_num) ⟨17493, by rfl⟩ (by norm_num))
theorem R46653 : Reach 46653 := rs (se 3 (by rfl) ⟨8747, by rfl⟩) (B 17495 (by norm_num) ⟨8747, by rfl⟩ (by norm_num))
theorem R46657 : Reach 46657 := rs (se 2 (by rfl) ⟨17496, by rfl⟩) (B 34993 (by norm_num) ⟨17496, by rfl⟩ (by norm_num))
theorem R46661 : Reach 46661 := rs (se 4 (by rfl) ⟨4374, by rfl⟩) (B 8749 (by norm_num) ⟨4374, by rfl⟩ (by norm_num))
theorem R46665 : Reach 46665 := rs (se 2 (by rfl) ⟨17499, by rfl⟩) (B 34999 (by norm_num) ⟨17499, by rfl⟩ (by norm_num))
theorem R112205 : Reach 112205 := rs (se 3 (by rfl) ⟨21038, by rfl⟩) (B 42077 (by norm_num) ⟨21038, by rfl⟩ (by norm_num))
theorem R46669 : Reach 46669 := rs (se 3 (by rfl) ⟨8750, by rfl⟩) (B 17501 (by norm_num) ⟨8750, by rfl⟩ (by norm_num))
theorem R46673 : Reach 46673 := rs (se 2 (by rfl) ⟨17502, by rfl⟩) (B 35005 (by norm_num) ⟨17502, by rfl⟩ (by norm_num))
theorem R46677 : Reach 46677 := rs (se 8 (by rfl) ⟨273, by rfl⟩) (B 547 (by norm_num) ⟨273, by rfl⟩ (by norm_num))
theorem R46681 : Reach 46681 := rs (se 2 (by rfl) ⟨17505, by rfl⟩) (B 35011 (by norm_num) ⟨17505, by rfl⟩ (by norm_num))
theorem R46685 : Reach 46685 := rs (se 3 (by rfl) ⟨8753, by rfl⟩) (B 17507 (by norm_num) ⟨8753, by rfl⟩ (by norm_num))
theorem R46689 : Reach 46689 := rs (se 2 (by rfl) ⟨17508, by rfl⟩) (B 35017 (by norm_num) ⟨17508, by rfl⟩ (by norm_num))
theorem R46693 : Reach 46693 := rs (se 4 (by rfl) ⟨4377, by rfl⟩) (B 8755 (by norm_num) ⟨4377, by rfl⟩ (by norm_num))
theorem R46697 : Reach 46697 := rs (se 2 (by rfl) ⟨17511, by rfl⟩) (B 35023 (by norm_num) ⟨17511, by rfl⟩ (by norm_num))
theorem R46701 : Reach 46701 := rs (se 3 (by rfl) ⟨8756, by rfl⟩) (B 17513 (by norm_num) ⟨8756, by rfl⟩ (by norm_num))
theorem R46705 : Reach 46705 := rs (se 2 (by rfl) ⟨17514, by rfl⟩) (B 35029 (by norm_num) ⟨17514, by rfl⟩ (by norm_num))
theorem R46709 : Reach 46709 := rs (se 5 (by rfl) ⟨2189, by rfl⟩) (B 4379 (by norm_num) ⟨2189, by rfl⟩ (by norm_num))
theorem R46713 : Reach 46713 := rs (se 2 (by rfl) ⟨17517, by rfl⟩) (B 35035 (by norm_num) ⟨17517, by rfl⟩ (by norm_num))
theorem R46717 : Reach 46717 := rs (se 3 (by rfl) ⟨8759, by rfl⟩) (B 17519 (by norm_num) ⟨8759, by rfl⟩ (by norm_num))
theorem R46721 : Reach 46721 := rs (se 2 (by rfl) ⟨17520, by rfl⟩) (B 35041 (by norm_num) ⟨17520, by rfl⟩ (by norm_num))
theorem R112261 : Reach 112261 := rs (se 4 (by rfl) ⟨10524, by rfl⟩) (B 21049 (by norm_num) ⟨10524, by rfl⟩ (by norm_num))
theorem R46725 : Reach 46725 := rs (se 4 (by rfl) ⟨4380, by rfl⟩) (B 8761 (by norm_num) ⟨4380, by rfl⟩ (by norm_num))
theorem R46729 : Reach 46729 := rs (se 2 (by rfl) ⟨17523, by rfl⟩) (B 35047 (by norm_num) ⟨17523, by rfl⟩ (by norm_num))
theorem R46733 : Reach 46733 := rs (se 3 (by rfl) ⟨8762, by rfl⟩) (B 17525 (by norm_num) ⟨8762, by rfl⟩ (by norm_num))
theorem R79501 : Reach 79501 := rs (se 3 (by rfl) ⟨14906, by rfl⟩) (B 29813 (by norm_num) ⟨14906, by rfl⟩ (by norm_num))
theorem R46737 : Reach 46737 := rs (se 2 (by rfl) ⟨17526, by rfl⟩) (B 35053 (by norm_num) ⟨17526, by rfl⟩ (by norm_num))
theorem R46741 : Reach 46741 := rs (se 6 (by rfl) ⟨1095, by rfl⟩) (B 2191 (by norm_num) ⟨1095, by rfl⟩ (by norm_num))
theorem R46745 : Reach 46745 := rs (se 2 (by rfl) ⟨17529, by rfl⟩) (B 35059 (by norm_num) ⟨17529, by rfl⟩ (by norm_num))
theorem R46749 : Reach 46749 := rs (se 3 (by rfl) ⟨8765, by rfl⟩) (B 17531 (by norm_num) ⟨8765, by rfl⟩ (by norm_num))
theorem R46753 : Reach 46753 := rs (se 2 (by rfl) ⟨17532, by rfl⟩) (B 35065 (by norm_num) ⟨17532, by rfl⟩ (by norm_num))
theorem R145061 : Reach 145061 := rs (se 4 (by rfl) ⟨13599, by rfl⟩) (B 27199 (by norm_num) ⟨13599, by rfl⟩ (by norm_num))
theorem R46757 : Reach 46757 := rs (se 4 (by rfl) ⟨4383, by rfl⟩) (B 8767 (by norm_num) ⟨4383, by rfl⟩ (by norm_num))
theorem R46761 : Reach 46761 := rs (se 2 (by rfl) ⟨17535, by rfl⟩) (B 35071 (by norm_num) ⟨17535, by rfl⟩ (by norm_num))
theorem R46765 : Reach 46765 := rs (se 3 (by rfl) ⟨8768, by rfl⟩) (B 17537 (by norm_num) ⟨8768, by rfl⟩ (by norm_num))
theorem R46769 : Reach 46769 := rs (se 2 (by rfl) ⟨17538, by rfl⟩) (B 35077 (by norm_num) ⟨17538, by rfl⟩ (by norm_num))
theorem R210613 : Reach 210613 := rs (se 5 (by rfl) ⟨9872, by rfl⟩) (B 19745 (by norm_num) ⟨9872, by rfl⟩ (by norm_num))
theorem R46773 : Reach 46773 := rs (se 5 (by rfl) ⟨2192, by rfl⟩) (B 4385 (by norm_num) ⟨2192, by rfl⟩ (by norm_num))
theorem R46777 : Reach 46777 := rs (se 2 (by rfl) ⟨17541, by rfl⟩) (B 35083 (by norm_num) ⟨17541, by rfl⟩ (by norm_num))
theorem R46781 : Reach 46781 := rs (se 3 (by rfl) ⟨8771, by rfl⟩) (B 17543 (by norm_num) ⟨8771, by rfl⟩ (by norm_num))
theorem R46785 : Reach 46785 := rs (se 2 (by rfl) ⟨17544, by rfl⟩) (B 35089 (by norm_num) ⟨17544, by rfl⟩ (by norm_num))
theorem R46789 : Reach 46789 := rs (se 4 (by rfl) ⟨4386, by rfl⟩) (B 8773 (by norm_num) ⟨4386, by rfl⟩ (by norm_num))
theorem R46793 : Reach 46793 := rs (se 2 (by rfl) ⟨17547, by rfl⟩) (B 35095 (by norm_num) ⟨17547, by rfl⟩ (by norm_num))
theorem R46797 : Reach 46797 := rs (se 3 (by rfl) ⟨8774, by rfl⟩) (B 17549 (by norm_num) ⟨8774, by rfl⟩ (by norm_num))
theorem R46801 : Reach 46801 := rs (se 2 (by rfl) ⟨17550, by rfl⟩) (B 35101 (by norm_num) ⟨17550, by rfl⟩ (by norm_num))
theorem R46805 : Reach 46805 := rs (se 7 (by rfl) ⟨548, by rfl⟩) (B 1097 (by norm_num) ⟨548, by rfl⟩ (by norm_num))
theorem R46809 : Reach 46809 := rs (se 2 (by rfl) ⟨17553, by rfl⟩) (B 35107 (by norm_num) ⟨17553, by rfl⟩ (by norm_num))
theorem R46813 : Reach 46813 := rs (se 3 (by rfl) ⟨8777, by rfl⟩) (B 17555 (by norm_num) ⟨8777, by rfl⟩ (by norm_num))
theorem R46817 : Reach 46817 := rs (se 2 (by rfl) ⟨17556, by rfl⟩) (B 35113 (by norm_num) ⟨17556, by rfl⟩ (by norm_num))
theorem R46821 : Reach 46821 := rs (se 4 (by rfl) ⟨4389, by rfl⟩) (B 8779 (by norm_num) ⟨4389, by rfl⟩ (by norm_num))
theorem R46825 : Reach 46825 := rs (se 2 (by rfl) ⟨17559, by rfl⟩) (B 35119 (by norm_num) ⟨17559, by rfl⟩ (by norm_num))
theorem R46829 : Reach 46829 := rs (se 3 (by rfl) ⟨8780, by rfl⟩) (B 17561 (by norm_num) ⟨8780, by rfl⟩ (by norm_num))
theorem R46833 : Reach 46833 := rs (se 2 (by rfl) ⟨17562, by rfl⟩) (B 35125 (by norm_num) ⟨17562, by rfl⟩ (by norm_num))
theorem R46837 : Reach 46837 := rs (se 5 (by rfl) ⟨2195, by rfl⟩) (B 4391 (by norm_num) ⟨2195, by rfl⟩ (by norm_num))
theorem R46841 : Reach 46841 := rs (se 2 (by rfl) ⟨17565, by rfl⟩) (B 35131 (by norm_num) ⟨17565, by rfl⟩ (by norm_num))
theorem R46845 : Reach 46845 := rs (se 3 (by rfl) ⟨8783, by rfl⟩) (B 17567 (by norm_num) ⟨8783, by rfl⟩ (by norm_num))
theorem R46849 : Reach 46849 := rs (se 2 (by rfl) ⟨17568, by rfl⟩) (B 35137 (by norm_num) ⟨17568, by rfl⟩ (by norm_num))
theorem R46853 : Reach 46853 := rs (se 4 (by rfl) ⟨4392, by rfl⟩) (B 8785 (by norm_num) ⟨4392, by rfl⟩ (by norm_num))
theorem R46857 : Reach 46857 := rs (se 2 (by rfl) ⟨17571, by rfl⟩) (B 35143 (by norm_num) ⟨17571, by rfl⟩ (by norm_num))
theorem R46861 : Reach 46861 := rs (se 3 (by rfl) ⟨8786, by rfl⟩) (B 17573 (by norm_num) ⟨8786, by rfl⟩ (by norm_num))
theorem R46865 : Reach 46865 := rs (se 2 (by rfl) ⟨17574, by rfl⟩) (B 35149 (by norm_num) ⟨17574, by rfl⟩ (by norm_num))
theorem R46869 : Reach 46869 := rs (se 6 (by rfl) ⟨1098, by rfl⟩) (B 2197 (by norm_num) ⟨1098, by rfl⟩ (by norm_num))
theorem R46873 : Reach 46873 := rs (se 2 (by rfl) ⟨17577, by rfl⟩) (B 35155 (by norm_num) ⟨17577, by rfl⟩ (by norm_num))
theorem R46877 : Reach 46877 := rs (se 3 (by rfl) ⟨8789, by rfl⟩) (B 17579 (by norm_num) ⟨8789, by rfl⟩ (by norm_num))
theorem R46881 : Reach 46881 := rs (se 2 (by rfl) ⟨17580, by rfl⟩) (B 35161 (by norm_num) ⟨17580, by rfl⟩ (by norm_num))
theorem R46885 : Reach 46885 := rs (se 4 (by rfl) ⟨4395, by rfl⟩) (B 8791 (by norm_num) ⟨4395, by rfl⟩ (by norm_num))
theorem R46889 : Reach 46889 := rs (se 2 (by rfl) ⟨17583, by rfl⟩) (B 35167 (by norm_num) ⟨17583, by rfl⟩ (by norm_num))
theorem R46893 : Reach 46893 := rs (se 3 (by rfl) ⟨8792, by rfl⟩) (B 17585 (by norm_num) ⟨8792, by rfl⟩ (by norm_num))
theorem R46897 : Reach 46897 := rs (se 2 (by rfl) ⟨17586, by rfl⟩) (B 35173 (by norm_num) ⟨17586, by rfl⟩ (by norm_num))
theorem R46901 : Reach 46901 := rs (se 5 (by rfl) ⟨2198, by rfl⟩) (B 4397 (by norm_num) ⟨2198, by rfl⟩ (by norm_num))
theorem R46905 : Reach 46905 := rs (se 2 (by rfl) ⟨17589, by rfl⟩) (B 35179 (by norm_num) ⟨17589, by rfl⟩ (by norm_num))
theorem R46909 : Reach 46909 := rs (se 3 (by rfl) ⟨8795, by rfl⟩) (B 17591 (by norm_num) ⟨8795, by rfl⟩ (by norm_num))
theorem R46913 : Reach 46913 := rs (se 2 (by rfl) ⟨17592, by rfl⟩) (B 35185 (by norm_num) ⟨17592, by rfl⟩ (by norm_num))
theorem R46917 : Reach 46917 := rs (se 4 (by rfl) ⟨4398, by rfl⟩) (B 8797 (by norm_num) ⟨4398, by rfl⟩ (by norm_num))
theorem R46921 : Reach 46921 := rs (se 2 (by rfl) ⟨17595, by rfl⟩) (B 35191 (by norm_num) ⟨17595, by rfl⟩ (by norm_num))
theorem R46925 : Reach 46925 := rs (se 3 (by rfl) ⟨8798, by rfl⟩) (B 17597 (by norm_num) ⟨8798, by rfl⟩ (by norm_num))
theorem R46929 : Reach 46929 := rs (se 2 (by rfl) ⟨17598, by rfl⟩) (B 35197 (by norm_num) ⟨17598, by rfl⟩ (by norm_num))
theorem R46933 : Reach 46933 := rs (se 9 (by rfl) ⟨137, by rfl⟩) (B 275 (by norm_num) ⟨137, by rfl⟩ (by norm_num))
theorem R46937 : Reach 46937 := rs (se 2 (by rfl) ⟨17601, by rfl⟩) (B 35203 (by norm_num) ⟨17601, by rfl⟩ (by norm_num))
theorem R46941 : Reach 46941 := rs (se 3 (by rfl) ⟨8801, by rfl⟩) (B 17603 (by norm_num) ⟨8801, by rfl⟩ (by norm_num))
theorem R46945 : Reach 46945 := rs (se 2 (by rfl) ⟨17604, by rfl⟩) (B 35209 (by norm_num) ⟨17604, by rfl⟩ (by norm_num))
theorem R145253 : Reach 145253 := rs (se 4 (by rfl) ⟨13617, by rfl⟩) (B 27235 (by norm_num) ⟨13617, by rfl⟩ (by norm_num))
theorem R46949 : Reach 46949 := rs (se 4 (by rfl) ⟨4401, by rfl⟩) (B 8803 (by norm_num) ⟨4401, by rfl⟩ (by norm_num))
theorem R46953 : Reach 46953 := rs (se 2 (by rfl) ⟨17607, by rfl⟩) (B 35215 (by norm_num) ⟨17607, by rfl⟩ (by norm_num))
theorem R46957 : Reach 46957 := rs (se 3 (by rfl) ⟨8804, by rfl⟩) (B 17609 (by norm_num) ⟨8804, by rfl⟩ (by norm_num))
theorem R46961 : Reach 46961 := rs (se 2 (by rfl) ⟨17610, by rfl⟩) (B 35221 (by norm_num) ⟨17610, by rfl⟩ (by norm_num))
theorem R46965 : Reach 46965 := rs (se 5 (by rfl) ⟨2201, by rfl⟩) (B 4403 (by norm_num) ⟨2201, by rfl⟩ (by norm_num))
theorem R46969 : Reach 46969 := rs (se 2 (by rfl) ⟨17613, by rfl⟩) (B 35227 (by norm_num) ⟨17613, by rfl⟩ (by norm_num))
theorem R46973 : Reach 46973 := rs (se 3 (by rfl) ⟨8807, by rfl⟩) (B 17615 (by norm_num) ⟨8807, by rfl⟩ (by norm_num))
theorem R46977 : Reach 46977 := rs (se 2 (by rfl) ⟨17616, by rfl⟩) (B 35233 (by norm_num) ⟨17616, by rfl⟩ (by norm_num))
theorem R46981 : Reach 46981 := rs (se 4 (by rfl) ⟨4404, by rfl⟩) (B 8809 (by norm_num) ⟨4404, by rfl⟩ (by norm_num))
theorem R46985 : Reach 46985 := rs (se 2 (by rfl) ⟨17619, by rfl⟩) (B 35239 (by norm_num) ⟨17619, by rfl⟩ (by norm_num))
theorem R46989 : Reach 46989 := rs (se 3 (by rfl) ⟨8810, by rfl⟩) (B 17621 (by norm_num) ⟨8810, by rfl⟩ (by norm_num))
theorem R46993 : Reach 46993 := rs (se 2 (by rfl) ⟨17622, by rfl⟩) (B 35245 (by norm_num) ⟨17622, by rfl⟩ (by norm_num))
theorem R46997 : Reach 46997 := rs (se 6 (by rfl) ⟨1101, by rfl⟩) (B 2203 (by norm_num) ⟨1101, by rfl⟩ (by norm_num))
theorem R47001 : Reach 47001 := rs (se 2 (by rfl) ⟨17625, by rfl⟩) (B 35251 (by norm_num) ⟨17625, by rfl⟩ (by norm_num))
theorem R47005 : Reach 47005 := rs (se 3 (by rfl) ⟨8813, by rfl⟩) (B 17627 (by norm_num) ⟨8813, by rfl⟩ (by norm_num))
theorem R47009 : Reach 47009 := rs (se 2 (by rfl) ⟨17628, by rfl⟩) (B 35257 (by norm_num) ⟨17628, by rfl⟩ (by norm_num))
theorem R112549 : Reach 112549 := rs (se 4 (by rfl) ⟨10551, by rfl⟩) (B 21103 (by norm_num) ⟨10551, by rfl⟩ (by norm_num))
theorem R47013 : Reach 47013 := rs (se 4 (by rfl) ⟨4407, by rfl⟩) (B 8815 (by norm_num) ⟨4407, by rfl⟩ (by norm_num))
theorem R47017 : Reach 47017 := rs (se 2 (by rfl) ⟨17631, by rfl⟩) (B 35263 (by norm_num) ⟨17631, by rfl⟩ (by norm_num))
theorem R47021 : Reach 47021 := rs (se 3 (by rfl) ⟨8816, by rfl⟩) (B 17633 (by norm_num) ⟨8816, by rfl⟩ (by norm_num))
theorem R47025 : Reach 47025 := rs (se 2 (by rfl) ⟨17634, by rfl⟩) (B 35269 (by norm_num) ⟨17634, by rfl⟩ (by norm_num))
theorem R47029 : Reach 47029 := rs (se 5 (by rfl) ⟨2204, by rfl⟩) (B 4409 (by norm_num) ⟨2204, by rfl⟩ (by norm_num))
theorem R47033 : Reach 47033 := rs (se 2 (by rfl) ⟨17637, by rfl⟩) (B 35275 (by norm_num) ⟨17637, by rfl⟩ (by norm_num))
theorem R47037 : Reach 47037 := rs (se 3 (by rfl) ⟨8819, by rfl⟩) (B 17639 (by norm_num) ⟨8819, by rfl⟩ (by norm_num))
theorem R47041 : Reach 47041 := rs (se 2 (by rfl) ⟨17640, by rfl⟩) (B 35281 (by norm_num) ⟨17640, by rfl⟩ (by norm_num))
theorem R47045 : Reach 47045 := rs (se 4 (by rfl) ⟨4410, by rfl⟩) (B 8821 (by norm_num) ⟨4410, by rfl⟩ (by norm_num))
theorem R47049 : Reach 47049 := rs (se 2 (by rfl) ⟨17643, by rfl⟩) (B 35287 (by norm_num) ⟨17643, by rfl⟩ (by norm_num))
theorem R112589 : Reach 112589 := rs (se 3 (by rfl) ⟨21110, by rfl⟩) (B 42221 (by norm_num) ⟨21110, by rfl⟩ (by norm_num))
theorem R47053 : Reach 47053 := rs (se 3 (by rfl) ⟨8822, by rfl⟩) (B 17645 (by norm_num) ⟨8822, by rfl⟩ (by norm_num))
theorem R47057 : Reach 47057 := rs (se 2 (by rfl) ⟨17646, by rfl⟩) (B 35293 (by norm_num) ⟨17646, by rfl⟩ (by norm_num))
theorem R47061 : Reach 47061 := rs (se 7 (by rfl) ⟨551, by rfl⟩) (B 1103 (by norm_num) ⟨551, by rfl⟩ (by norm_num))
theorem R47065 : Reach 47065 := rs (se 2 (by rfl) ⟨17649, by rfl⟩) (B 35299 (by norm_num) ⟨17649, by rfl⟩ (by norm_num))
theorem R47069 : Reach 47069 := rs (se 3 (by rfl) ⟨8825, by rfl⟩) (B 17651 (by norm_num) ⟨8825, by rfl⟩ (by norm_num))
theorem R47073 : Reach 47073 := rs (se 2 (by rfl) ⟨17652, by rfl⟩) (B 35305 (by norm_num) ⟨17652, by rfl⟩ (by norm_num))
theorem R47077 : Reach 47077 := rs (se 4 (by rfl) ⟨4413, by rfl⟩) (B 8827 (by norm_num) ⟨4413, by rfl⟩ (by norm_num))
theorem R47081 : Reach 47081 := rs (se 2 (by rfl) ⟨17655, by rfl⟩) (B 35311 (by norm_num) ⟨17655, by rfl⟩ (by norm_num))
theorem R47085 : Reach 47085 := rs (se 3 (by rfl) ⟨8828, by rfl⟩) (B 17657 (by norm_num) ⟨8828, by rfl⟩ (by norm_num))
theorem R47089 : Reach 47089 := rs (se 2 (by rfl) ⟨17658, by rfl⟩) (B 35317 (by norm_num) ⟨17658, by rfl⟩ (by norm_num))
theorem R47093 : Reach 47093 := rs (se 5 (by rfl) ⟨2207, by rfl⟩) (B 4415 (by norm_num) ⟨2207, by rfl⟩ (by norm_num))
theorem R47097 : Reach 47097 := rs (se 2 (by rfl) ⟨17661, by rfl⟩) (B 35323 (by norm_num) ⟨17661, by rfl⟩ (by norm_num))
theorem R47101 : Reach 47101 := rs (se 3 (by rfl) ⟨8831, by rfl⟩) (B 17663 (by norm_num) ⟨8831, by rfl⟩ (by norm_num))
theorem R47105 : Reach 47105 := rs (se 2 (by rfl) ⟨17664, by rfl⟩) (B 35329 (by norm_num) ⟨17664, by rfl⟩ (by norm_num))
theorem R47109 : Reach 47109 := rs (se 4 (by rfl) ⟨4416, by rfl⟩) (B 8833 (by norm_num) ⟨4416, by rfl⟩ (by norm_num))
theorem R47113 : Reach 47113 := rs (se 2 (by rfl) ⟨17667, by rfl⟩) (B 35335 (by norm_num) ⟨17667, by rfl⟩ (by norm_num))
theorem R47117 : Reach 47117 := rs (se 3 (by rfl) ⟨8834, by rfl⟩) (B 17669 (by norm_num) ⟨8834, by rfl⟩ (by norm_num))
theorem R112661 : Reach 112661 := rs (se 6 (by rfl) ⟨2640, by rfl⟩) (B 5281 (by norm_num) ⟨2640, by rfl⟩ (by norm_num))
theorem R47261 : Reach 47261 := rs (se 3 (by rfl) ⟨8861, by rfl⟩) (B 17723 (by norm_num) ⟨8861, by rfl⟩ (by norm_num))
theorem R112853 : Reach 112853 := rs (se 7 (by rfl) ⟨1322, by rfl⟩) (B 2645 (by norm_num) ⟨1322, by rfl⟩ (by norm_num))
theorem R145637 : Reach 145637 := rs (se 4 (by rfl) ⟨13653, by rfl⟩) (B 27307 (by norm_num) ⟨13653, by rfl⟩ (by norm_num))
theorem R178469 : Reach 178469 := rs (se 4 (by rfl) ⟨16731, by rfl⟩) (B 33463 (by norm_num) ⟨16731, by rfl⟩ (by norm_num))
theorem R211285 : Reach 211285 := rs (se 10 (by rfl) ⟨309, by rfl⟩) (B 619 (by norm_num) ⟨309, by rfl⟩ (by norm_num))
theorem R47461 : Reach 47461 := rs (se 4 (by rfl) ⟨4449, by rfl⟩) (B 8899 (by norm_num) ⟨4449, by rfl⟩ (by norm_num))
theorem R80357 : Reach 80357 := rs (se 4 (by rfl) ⟨7533, by rfl⟩) (B 15067 (by norm_num) ⟨7533, by rfl⟩ (by norm_num))
theorem R47593 : Reach 47593 := rs (se 2 (by rfl) ⟨17847, by rfl⟩) (B 35695 (by norm_num) ⟨17847, by rfl⟩ (by norm_num))
theorem R113197 : Reach 113197 := rs (se 3 (by rfl) ⟨21224, by rfl⟩) (B 42449 (by norm_num) ⟨21224, by rfl⟩ (by norm_num))
theorem R178757 : Reach 178757 := rs (se 4 (by rfl) ⟨16758, by rfl⟩) (B 33517 (by norm_num) ⟨16758, by rfl⟩ (by norm_num))
theorem R146069 : Reach 146069 := rs (se 6 (by rfl) ⟨3423, by rfl⟩) (B 6847 (by norm_num) ⟨3423, by rfl⟩ (by norm_num))
theorem R113309 : Reach 113309 := rs (se 3 (by rfl) ⟨21245, by rfl⟩) (B 42491 (by norm_num) ⟨21245, by rfl⟩ (by norm_num))
theorem R47837 : Reach 47837 := rs (se 3 (by rfl) ⟨8969, by rfl⟩) (B 17939 (by norm_num) ⟨8969, by rfl⟩ (by norm_num))
theorem R47909 : Reach 47909 := rs (se 4 (by rfl) ⟨4491, by rfl⟩) (B 8983 (by norm_num) ⟨4491, by rfl⟩ (by norm_num))
theorem R80717 : Reach 80717 := rs (se 3 (by rfl) ⟨15134, by rfl⟩) (B 30269 (by norm_num) ⟨15134, by rfl⟩ (by norm_num))
theorem R113501 : Reach 113501 := rs (se 3 (by rfl) ⟨21281, by rfl⟩) (B 42563 (by norm_num) ⟨21281, by rfl⟩ (by norm_num))
theorem R506837 : Reach 506837 := rs (se 7 (by rfl) ⟨5939, by rfl⟩) (B 11879 (by norm_num) ⟨5939, by rfl⟩ (by norm_num))
theorem R48097 : Reach 48097 := rs (se 2 (by rfl) ⟨18036, by rfl⟩) (B 36073 (by norm_num) ⟨18036, by rfl⟩ (by norm_num))
theorem R146501 : Reach 146501 := rs (se 4 (by rfl) ⟨13734, by rfl⟩) (B 27469 (by norm_num) ⟨13734, by rfl⟩ (by norm_num))
theorem R48281 : Reach 48281 := rs (se 2 (by rfl) ⟨18105, by rfl⟩) (B 36211 (by norm_num) ⟨18105, by rfl⟩ (by norm_num))
theorem R113845 : Reach 113845 := rs (se 5 (by rfl) ⟨5336, by rfl⟩) (B 10673 (by norm_num) ⟨5336, by rfl⟩ (by norm_num))
theorem R113957 : Reach 113957 := rs (se 4 (by rfl) ⟨10683, by rfl⟩) (B 21367 (by norm_num) ⟨10683, by rfl⟩ (by norm_num))
theorem R48541 : Reach 48541 := rs (se 3 (by rfl) ⟨9101, by rfl⟩) (B 18203 (by norm_num) ⟨9101, by rfl⟩ (by norm_num))
theorem R114101 : Reach 114101 := rs (se 5 (by rfl) ⟨5348, by rfl⟩) (B 10697 (by norm_num) ⟨5348, by rfl⟩ (by norm_num))
theorem R48577 : Reach 48577 := rs (se 2 (by rfl) ⟨18216, by rfl⟩) (B 36433 (by norm_num) ⟨18216, by rfl⟩ (by norm_num))
theorem R48613 : Reach 48613 := rs (se 4 (by rfl) ⟨4557, by rfl⟩) (B 9115 (by norm_num) ⟨4557, by rfl⟩ (by norm_num))
theorem R114149 : Reach 114149 := rs (se 4 (by rfl) ⟨10701, by rfl⟩) (B 21403 (by norm_num) ⟨10701, by rfl⟩ (by norm_num))
theorem R146933 : Reach 146933 := rs (se 5 (by rfl) ⟨6887, by rfl⟩) (B 13775 (by norm_num) ⟨6887, by rfl⟩ (by norm_num))
theorem R114173 : Reach 114173 := rs (se 3 (by rfl) ⟨21407, by rfl⟩) (B 42815 (by norm_num) ⟨21407, by rfl⟩ (by norm_num))
theorem R48649 : Reach 48649 := rs (se 2 (by rfl) ⟨18243, by rfl⟩) (B 36487 (by norm_num) ⟨18243, by rfl⟩ (by norm_num))
theorem R48685 : Reach 48685 := rs (se 3 (by rfl) ⟨9128, by rfl⟩) (B 18257 (by norm_num) ⟨9128, by rfl⟩ (by norm_num))
theorem R48721 : Reach 48721 := rs (se 2 (by rfl) ⟨18270, by rfl⟩) (B 36541 (by norm_num) ⟨18270, by rfl⟩ (by norm_num))
theorem R179813 : Reach 179813 := rs (se 4 (by rfl) ⟨16857, by rfl⟩) (B 33715 (by norm_num) ⟨16857, by rfl⟩ (by norm_num))
theorem R48757 : Reach 48757 := rs (se 5 (by rfl) ⟨2285, by rfl⟩) (B 4571 (by norm_num) ⟨2285, by rfl⟩ (by norm_num))
theorem R48793 : Reach 48793 := rs (se 2 (by rfl) ⟨18297, by rfl⟩) (B 36595 (by norm_num) ⟨18297, by rfl⟩ (by norm_num))
theorem R48829 : Reach 48829 := rs (se 3 (by rfl) ⟨9155, by rfl⟩) (B 18311 (by norm_num) ⟨9155, by rfl⟩ (by norm_num))
theorem R704213 : Reach 704213 := rs (se 7 (by rfl) ⟨8252, by rfl⟩) (B 16505 (by norm_num) ⟨8252, by rfl⟩ (by norm_num))
theorem R48865 : Reach 48865 := rs (se 2 (by rfl) ⟨18324, by rfl⟩) (B 36649 (by norm_num) ⟨18324, by rfl⟩ (by norm_num))
theorem R48901 : Reach 48901 := rs (se 4 (by rfl) ⟨4584, by rfl⟩) (B 9169 (by norm_num) ⟨4584, by rfl⟩ (by norm_num))
theorem R48937 : Reach 48937 := rs (se 2 (by rfl) ⟨18351, by rfl⟩) (B 36703 (by norm_num) ⟨18351, by rfl⟩ (by norm_num))
theorem R114493 : Reach 114493 := rs (se 3 (by rfl) ⟨21467, by rfl⟩) (B 42935 (by norm_num) ⟨21467, by rfl⟩ (by norm_num))
theorem R48973 : Reach 48973 := rs (se 3 (by rfl) ⟨9182, by rfl⟩) (B 18365 (by norm_num) ⟨9182, by rfl⟩ (by norm_num))
theorem R49009 : Reach 49009 := rs (se 2 (by rfl) ⟨18378, by rfl⟩) (B 36757 (by norm_num) ⟨18378, by rfl⟩ (by norm_num))
theorem R49033 : Reach 49033 := rs (se 2 (by rfl) ⟨18387, by rfl⟩) (B 36775 (by norm_num) ⟨18387, by rfl⟩ (by norm_num))
theorem R49045 : Reach 49045 := rs (se 6 (by rfl) ⟨1149, by rfl⟩) (B 2299 (by norm_num) ⟨1149, by rfl⟩ (by norm_num))
theorem R147365 : Reach 147365 := rs (se 4 (by rfl) ⟨13815, by rfl⟩) (B 27631 (by norm_num) ⟨13815, by rfl⟩ (by norm_num))
theorem R114605 : Reach 114605 := rs (se 3 (by rfl) ⟨21488, by rfl⟩) (B 42977 (by norm_num) ⟨21488, by rfl⟩ (by norm_num))
theorem R49081 : Reach 49081 := rs (se 2 (by rfl) ⟨18405, by rfl⟩) (B 36811 (by norm_num) ⟨18405, by rfl⟩ (by norm_num))
theorem R49105 : Reach 49105 := rs (se 2 (by rfl) ⟨18414, by rfl⟩) (B 36829 (by norm_num) ⟨18414, by rfl⟩ (by norm_num))
theorem R49117 : Reach 49117 := rs (se 3 (by rfl) ⟨9209, by rfl⟩) (B 18419 (by norm_num) ⟨9209, by rfl⟩ (by norm_num))
theorem R49153 : Reach 49153 := rs (se 2 (by rfl) ⟨18432, by rfl⟩) (B 36865 (by norm_num) ⟨18432, by rfl⟩ (by norm_num))
theorem R49189 : Reach 49189 := rs (se 4 (by rfl) ⟨4611, by rfl⟩) (B 9223 (by norm_num) ⟨4611, by rfl⟩ (by norm_num))
theorem R49225 : Reach 49225 := rs (se 2 (by rfl) ⟨18459, by rfl⟩) (B 36919 (by norm_num) ⟨18459, by rfl⟩ (by norm_num))
theorem R49261 : Reach 49261 := rs (se 3 (by rfl) ⟨9236, by rfl⟩) (B 18473 (by norm_num) ⟨9236, by rfl⟩ (by norm_num))
theorem R114797 : Reach 114797 := rs (se 3 (by rfl) ⟨21524, by rfl⟩) (B 43049 (by norm_num) ⟨21524, by rfl⟩ (by norm_num))
theorem R49285 : Reach 49285 := rs (se 4 (by rfl) ⟨4620, by rfl⟩) (B 9241 (by norm_num) ⟨4620, by rfl⟩ (by norm_num))
theorem R49297 : Reach 49297 := rs (se 2 (by rfl) ⟨18486, by rfl⟩) (B 36973 (by norm_num) ⟨18486, by rfl⟩ (by norm_num))
theorem R49333 : Reach 49333 := rs (se 5 (by rfl) ⟨2312, by rfl⟩) (B 4625 (by norm_num) ⟨2312, by rfl⟩ (by norm_num))
theorem R278741 : Reach 278741 := rs (se 7 (by rfl) ⟨3266, by rfl⟩) (B 6533 (by norm_num) ⟨3266, by rfl⟩ (by norm_num))
theorem R377045 : Reach 377045 := rs (se 7 (by rfl) ⟨4418, by rfl⟩) (B 8837 (by norm_num) ⟨4418, by rfl⟩ (by norm_num))
theorem R49369 : Reach 49369 := rs (se 2 (by rfl) ⟨18513, by rfl⟩) (B 37027 (by norm_num) ⟨18513, by rfl⟩ (by norm_num))
theorem R49405 : Reach 49405 := rs (se 3 (by rfl) ⟨9263, by rfl⟩) (B 18527 (by norm_num) ⟨9263, by rfl⟩ (by norm_num))
theorem R246037 : Reach 246037 := rs (se 6 (by rfl) ⟨5766, by rfl⟩) (B 11533 (by norm_num) ⟨5766, by rfl⟩ (by norm_num))
theorem R49441 : Reach 49441 := rs (se 2 (by rfl) ⟨18540, by rfl⟩) (B 37081 (by norm_num) ⟨18540, by rfl⟩ (by norm_num))
theorem R49477 : Reach 49477 := rs (se 4 (by rfl) ⟨4638, by rfl⟩) (B 9277 (by norm_num) ⟨4638, by rfl⟩ (by norm_num))
theorem R147797 : Reach 147797 := rs (se 10 (by rfl) ⟨216, by rfl⟩) (B 433 (by norm_num) ⟨216, by rfl⟩ (by norm_num))
theorem R49513 : Reach 49513 := rs (se 2 (by rfl) ⟨18567, by rfl⟩) (B 37135 (by norm_num) ⟨18567, by rfl⟩ (by norm_num))
theorem R82309 : Reach 82309 := rs (se 4 (by rfl) ⟨7716, by rfl⟩) (B 15433 (by norm_num) ⟨7716, by rfl⟩ (by norm_num))
theorem R49549 : Reach 49549 := rs (se 3 (by rfl) ⟨9290, by rfl⟩) (B 18581 (by norm_num) ⟨9290, by rfl⟩ (by norm_num))
theorem R49585 : Reach 49585 := rs (se 2 (by rfl) ⟨18594, by rfl⟩) (B 37189 (by norm_num) ⟨18594, by rfl⟩ (by norm_num))
theorem R115141 : Reach 115141 := rs (se 4 (by rfl) ⟨10794, by rfl⟩) (B 21589 (by norm_num) ⟨10794, by rfl⟩ (by norm_num))
theorem R49621 : Reach 49621 := rs (se 7 (by rfl) ⟨581, by rfl⟩) (B 1163 (by norm_num) ⟨581, by rfl⟩ (by norm_num))
theorem R49657 : Reach 49657 := rs (se 2 (by rfl) ⟨18621, by rfl⟩) (B 37243 (by norm_num) ⟨18621, by rfl⟩ (by norm_num))
theorem R82453 : Reach 82453 := rs (se 6 (by rfl) ⟨1932, by rfl⟩) (B 3865 (by norm_num) ⟨1932, by rfl⟩ (by norm_num))
theorem R49693 : Reach 49693 := rs (se 3 (by rfl) ⟨9317, by rfl⟩) (B 18635 (by norm_num) ⟨9317, by rfl⟩ (by norm_num))
theorem R115253 : Reach 115253 := rs (se 5 (by rfl) ⟨5402, by rfl⟩) (B 10805 (by norm_num) ⟨5402, by rfl⟩ (by norm_num))
theorem R49729 : Reach 49729 := rs (se 2 (by rfl) ⟨18648, by rfl⟩) (B 37297 (by norm_num) ⟨18648, by rfl⟩ (by norm_num))
theorem R49765 : Reach 49765 := rs (se 4 (by rfl) ⟨4665, by rfl⟩) (B 9331 (by norm_num) ⟨4665, by rfl⟩ (by norm_num))
theorem R49801 : Reach 49801 := rs (se 2 (by rfl) ⟨18675, by rfl⟩) (B 37351 (by norm_num) ⟨18675, by rfl⟩ (by norm_num))
theorem R49837 : Reach 49837 := rs (se 3 (by rfl) ⟨9344, by rfl⟩) (B 18689 (by norm_num) ⟨9344, by rfl⟩ (by norm_num))
theorem R82613 : Reach 82613 := rs (se 5 (by rfl) ⟨3872, by rfl⟩) (B 7745 (by norm_num) ⟨3872, by rfl⟩ (by norm_num))
theorem R49853 : Reach 49853 := rs (se 3 (by rfl) ⟨9347, by rfl⟩) (B 18695 (by norm_num) ⟨9347, by rfl⟩ (by norm_num))
theorem R49873 : Reach 49873 := rs (se 2 (by rfl) ⟨18702, by rfl⟩) (B 37405 (by norm_num) ⟨18702, by rfl⟩ (by norm_num))
theorem R49909 : Reach 49909 := rs (se 5 (by rfl) ⟨2339, by rfl⟩) (B 4679 (by norm_num) ⟨2339, by rfl⟩ (by norm_num))
theorem R115445 : Reach 115445 := rs (se 5 (by rfl) ⟨5411, by rfl⟩) (B 10823 (by norm_num) ⟨5411, by rfl⟩ (by norm_num))
theorem R148229 : Reach 148229 := rs (se 4 (by rfl) ⟨13896, by rfl⟩) (B 27793 (by norm_num) ⟨13896, by rfl⟩ (by norm_num))
theorem R49945 : Reach 49945 := rs (se 2 (by rfl) ⟨18729, by rfl⟩) (B 37459 (by norm_num) ⟨18729, by rfl⟩ (by norm_num))
theorem R148277 : Reach 148277 := rs (se 5 (by rfl) ⟨6950, by rfl⟩) (B 13901 (by norm_num) ⟨6950, by rfl⟩ (by norm_num))
theorem R49981 : Reach 49981 := rs (se 3 (by rfl) ⟨9371, by rfl⟩) (B 18743 (by norm_num) ⟨9371, by rfl⟩ (by norm_num))
theorem R82757 : Reach 82757 := rs (se 4 (by rfl) ⟨7758, by rfl⟩) (B 15517 (by norm_num) ⟨7758, by rfl⟩ (by norm_num))
theorem R50017 : Reach 50017 := rs (se 2 (by rfl) ⟨18756, by rfl⟩) (B 37513 (by norm_num) ⟨18756, by rfl⟩ (by norm_num))
theorem R50053 : Reach 50053 := rs (se 4 (by rfl) ⟨4692, by rfl⟩) (B 9385 (by norm_num) ⟨4692, by rfl⟩ (by norm_num))
theorem R50089 : Reach 50089 := rs (se 2 (by rfl) ⟨18783, by rfl⟩) (B 37567 (by norm_num) ⟨18783, by rfl⟩ (by norm_num))
theorem R50105 : Reach 50105 := rs (se 2 (by rfl) ⟨18789, by rfl⟩) (B 37579 (by norm_num) ⟨18789, by rfl⟩ (by norm_num))
theorem R50125 : Reach 50125 := rs (se 3 (by rfl) ⟨9398, by rfl⟩) (B 18797 (by norm_num) ⟨9398, by rfl⟩ (by norm_num))
theorem R50161 : Reach 50161 := rs (se 2 (by rfl) ⟨18810, by rfl⟩) (B 37621 (by norm_num) ⟨18810, by rfl⟩ (by norm_num))
theorem R50197 : Reach 50197 := rs (se 6 (by rfl) ⟨1176, by rfl⟩) (B 2353 (by norm_num) ⟨1176, by rfl⟩ (by norm_num))
theorem R82981 : Reach 82981 := rs (se 4 (by rfl) ⟨7779, by rfl⟩) (B 15559 (by norm_num) ⟨7779, by rfl⟩ (by norm_num))
theorem R50233 : Reach 50233 := rs (se 2 (by rfl) ⟨18837, by rfl⟩) (B 37675 (by norm_num) ⟨18837, by rfl⟩ (by norm_num))
theorem R50269 : Reach 50269 := rs (se 3 (by rfl) ⟨9425, by rfl⟩) (B 18851 (by norm_num) ⟨9425, by rfl⟩ (by norm_num))
theorem R83045 : Reach 83045 := rs (se 4 (by rfl) ⟨7785, by rfl⟩) (B 15571 (by norm_num) ⟨7785, by rfl⟩ (by norm_num))
theorem R50305 : Reach 50305 := rs (se 2 (by rfl) ⟨18864, by rfl⟩) (B 37729 (by norm_num) ⟨18864, by rfl⟩ (by norm_num))
theorem R181397 : Reach 181397 := rs (se 6 (by rfl) ⟨4251, by rfl⟩) (B 8503 (by norm_num) ⟨4251, by rfl⟩ (by norm_num))
theorem R50341 : Reach 50341 := rs (se 4 (by rfl) ⟨4719, by rfl⟩) (B 9439 (by norm_num) ⟨4719, by rfl⟩ (by norm_num))
theorem R148661 : Reach 148661 := rs (se 5 (by rfl) ⟨6968, by rfl⟩) (B 13937 (by norm_num) ⟨6968, by rfl⟩ (by norm_num))
theorem R50377 : Reach 50377 := rs (se 2 (by rfl) ⟨18891, by rfl⟩) (B 37783 (by norm_num) ⟨18891, by rfl⟩ (by norm_num))
theorem R50413 : Reach 50413 := rs (se 3 (by rfl) ⟨9452, by rfl⟩) (B 18905 (by norm_num) ⟨9452, by rfl⟩ (by norm_num))
theorem R83197 : Reach 83197 := rs (se 3 (by rfl) ⟨15599, by rfl⟩) (B 31199 (by norm_num) ⟨15599, by rfl⟩ (by norm_num))
theorem R50449 : Reach 50449 := rs (se 2 (by rfl) ⟨18918, by rfl⟩) (B 37837 (by norm_num) ⟨18918, by rfl⟩ (by norm_num))
theorem R50485 : Reach 50485 := rs (se 5 (by rfl) ⟨2366, by rfl⟩) (B 4733 (by norm_num) ⟨2366, by rfl⟩ (by norm_num))
theorem R50521 : Reach 50521 := rs (se 2 (by rfl) ⟨18945, by rfl⟩) (B 37891 (by norm_num) ⟨18945, by rfl⟩ (by norm_num))
theorem R148853 : Reach 148853 := rs (se 5 (by rfl) ⟨6977, by rfl⟩) (B 13955 (by norm_num) ⟨6977, by rfl⟩ (by norm_num))
theorem R50557 : Reach 50557 := rs (se 3 (by rfl) ⟨9479, by rfl⟩) (B 18959 (by norm_num) ⟨9479, by rfl⟩ (by norm_num))
theorem R50593 : Reach 50593 := rs (se 2 (by rfl) ⟨18972, by rfl⟩) (B 37945 (by norm_num) ⟨18972, by rfl⟩ (by norm_num))
theorem R50629 : Reach 50629 := rs (se 4 (by rfl) ⟨4746, by rfl⟩) (B 9493 (by norm_num) ⟨4746, by rfl⟩ (by norm_num))
theorem R148949 : Reach 148949 := rs (se 7 (by rfl) ⟨1745, by rfl⟩) (B 3491 (by norm_num) ⟨1745, by rfl⟩ (by norm_num))
theorem R50665 : Reach 50665 := rs (se 2 (by rfl) ⟨18999, by rfl⟩) (B 37999 (by norm_num) ⟨18999, by rfl⟩ (by norm_num))
theorem R50701 : Reach 50701 := rs (se 3 (by rfl) ⟨9506, by rfl⟩) (B 19013 (by norm_num) ⟨9506, by rfl⟩ (by norm_num))
theorem R83501 : Reach 83501 := rs (se 3 (by rfl) ⟨15656, by rfl⟩) (B 31313 (by norm_num) ⟨15656, by rfl⟩ (by norm_num))
theorem R50737 : Reach 50737 := rs (se 2 (by rfl) ⟨19026, by rfl⟩) (B 38053 (by norm_num) ⟨19026, by rfl⟩ (by norm_num))
theorem R50773 : Reach 50773 := rs (se 8 (by rfl) ⟨297, by rfl⟩) (B 595 (by norm_num) ⟨297, by rfl⟩ (by norm_num))
theorem R149093 : Reach 149093 := rs (se 4 (by rfl) ⟨13977, by rfl⟩) (B 27955 (by norm_num) ⟨13977, by rfl⟩ (by norm_num))
theorem R50809 : Reach 50809 := rs (se 2 (by rfl) ⟨19053, by rfl⟩) (B 38107 (by norm_num) ⟨19053, by rfl⟩ (by norm_num))
theorem R50845 : Reach 50845 := rs (se 3 (by rfl) ⟨9533, by rfl⟩) (B 19067 (by norm_num) ⟨9533, by rfl⟩ (by norm_num))
theorem R50881 : Reach 50881 := rs (se 2 (by rfl) ⟨19080, by rfl⟩) (B 38161 (by norm_num) ⟨19080, by rfl⟩ (by norm_num))
theorem R116437 : Reach 116437 := rs (se 7 (by rfl) ⟨1364, by rfl⟩) (B 2729 (by norm_num) ⟨1364, by rfl⟩ (by norm_num))
theorem R50917 : Reach 50917 := rs (se 4 (by rfl) ⟨4773, by rfl⟩) (B 9547 (by norm_num) ⟨4773, by rfl⟩ (by norm_num))
theorem R50953 : Reach 50953 := rs (se 2 (by rfl) ⟨19107, by rfl⟩) (B 38215 (by norm_num) ⟨19107, by rfl⟩ (by norm_num))
theorem R214805 : Reach 214805 := rs (se 6 (by rfl) ⟨5034, by rfl⟩) (B 10069 (by norm_num) ⟨5034, by rfl⟩ (by norm_num))
theorem R50989 : Reach 50989 := rs (se 3 (by rfl) ⟨9560, by rfl⟩) (B 19121 (by norm_num) ⟨9560, by rfl⟩ (by norm_num))
theorem R116549 : Reach 116549 := rs (se 4 (by rfl) ⟨10926, by rfl⟩) (B 21853 (by norm_num) ⟨10926, by rfl⟩ (by norm_num))
theorem R51025 : Reach 51025 := rs (se 2 (by rfl) ⟨19134, by rfl⟩) (B 38269 (by norm_num) ⟨19134, by rfl⟩ (by norm_num))
theorem R51061 : Reach 51061 := rs (se 5 (by rfl) ⟨2393, by rfl⟩) (B 4787 (by norm_num) ⟨2393, by rfl⟩ (by norm_num))
theorem R313237 : Reach 313237 := rs (se 6 (by rfl) ⟨7341, by rfl⟩) (B 14683 (by norm_num) ⟨7341, by rfl⟩ (by norm_num))
theorem R51097 : Reach 51097 := rs (se 2 (by rfl) ⟨19161, by rfl⟩) (B 38323 (by norm_num) ⟨19161, by rfl⟩ (by norm_num))
theorem R51133 : Reach 51133 := rs (se 3 (by rfl) ⟨9587, by rfl⟩) (B 19175 (by norm_num) ⟨9587, by rfl⟩ (by norm_num))
theorem R51169 : Reach 51169 := rs (se 2 (by rfl) ⟨19188, by rfl⟩) (B 38377 (by norm_num) ⟨19188, by rfl⟩ (by norm_num))
theorem R51205 : Reach 51205 := rs (se 4 (by rfl) ⟨4800, by rfl⟩) (B 9601 (by norm_num) ⟨4800, by rfl⟩ (by norm_num))
theorem R116741 : Reach 116741 := rs (se 4 (by rfl) ⟨10944, by rfl⟩) (B 21889 (by norm_num) ⟨10944, by rfl⟩ (by norm_num))
theorem R149525 : Reach 149525 := rs (se 6 (by rfl) ⟨3504, by rfl⟩) (B 7009 (by norm_num) ⟨3504, by rfl⟩ (by norm_num))
theorem R51241 : Reach 51241 := rs (se 2 (by rfl) ⟨19215, by rfl⟩) (B 38431 (by norm_num) ⟨19215, by rfl⟩ (by norm_num))
theorem R51277 : Reach 51277 := rs (se 3 (by rfl) ⟨9614, by rfl⟩) (B 19229 (by norm_num) ⟨9614, by rfl⟩ (by norm_num))
theorem R51313 : Reach 51313 := rs (se 2 (by rfl) ⟨19242, by rfl⟩) (B 38485 (by norm_num) ⟨19242, by rfl⟩ (by norm_num))
theorem R51349 : Reach 51349 := rs (se 6 (by rfl) ⟨1203, by rfl⟩) (B 2407 (by norm_num) ⟨1203, by rfl⟩ (by norm_num))
theorem R84149 : Reach 84149 := rs (se 5 (by rfl) ⟨3944, by rfl⟩) (B 7889 (by norm_num) ⟨3944, by rfl⟩ (by norm_num))
theorem R51385 : Reach 51385 := rs (se 2 (by rfl) ⟨19269, by rfl⟩) (B 38539 (by norm_num) ⟨19269, by rfl⟩ (by norm_num))
theorem R248021 : Reach 248021 := rs (se 7 (by rfl) ⟨2906, by rfl⟩) (B 5813 (by norm_num) ⟨2906, by rfl⟩ (by norm_num))
theorem R51421 : Reach 51421 := rs (se 3 (by rfl) ⟨9641, by rfl⟩) (B 19283 (by norm_num) ⟨9641, by rfl⟩ (by norm_num))
theorem R51457 : Reach 51457 := rs (se 2 (by rfl) ⟨19296, by rfl⟩) (B 38593 (by norm_num) ⟨19296, by rfl⟩ (by norm_num))
theorem R84253 : Reach 84253 := rs (se 3 (by rfl) ⟨15797, by rfl⟩) (B 31595 (by norm_num) ⟨15797, by rfl⟩ (by norm_num))
theorem R51493 : Reach 51493 := rs (se 4 (by rfl) ⟨4827, by rfl⟩) (B 9655 (by norm_num) ⟨4827, by rfl⟩ (by norm_num))
theorem R51529 : Reach 51529 := rs (se 2 (by rfl) ⟨19323, by rfl⟩) (B 38647 (by norm_num) ⟨19323, by rfl⟩ (by norm_num))
theorem R51565 : Reach 51565 := rs (se 3 (by rfl) ⟨9668, by rfl⟩) (B 19337 (by norm_num) ⟨9668, by rfl⟩ (by norm_num))
theorem R51601 : Reach 51601 := rs (se 2 (by rfl) ⟨19350, by rfl⟩) (B 38701 (by norm_num) ⟨19350, by rfl⟩ (by norm_num))
theorem R346517 : Reach 346517 := rs (se 6 (by rfl) ⟨8121, by rfl⟩) (B 16243 (by norm_num) ⟨8121, by rfl⟩ (by norm_num))
theorem R84397 : Reach 84397 := rs (se 3 (by rfl) ⟨15824, by rfl⟩) (B 31649 (by norm_num) ⟨15824, by rfl⟩ (by norm_num))
theorem R51637 : Reach 51637 := rs (se 5 (by rfl) ⟨2420, by rfl⟩) (B 4841 (by norm_num) ⟨2420, by rfl⟩ (by norm_num))
theorem R149957 : Reach 149957 := rs (se 4 (by rfl) ⟨14058, by rfl⟩) (B 28117 (by norm_num) ⟨14058, by rfl⟩ (by norm_num))
theorem R51673 : Reach 51673 := rs (se 2 (by rfl) ⟨19377, by rfl⟩) (B 38755 (by norm_num) ⟨19377, by rfl⟩ (by norm_num))
theorem R51709 : Reach 51709 := rs (se 3 (by rfl) ⟨9695, by rfl⟩) (B 19391 (by norm_num) ⟨9695, by rfl⟩ (by norm_num))
theorem R51745 : Reach 51745 := rs (se 2 (by rfl) ⟨19404, by rfl⟩) (B 38809 (by norm_num) ⟨19404, by rfl⟩ (by norm_num))
theorem R51781 : Reach 51781 := rs (se 4 (by rfl) ⟨4854, by rfl⟩) (B 9709 (by norm_num) ⟨4854, by rfl⟩ (by norm_num))
theorem R84557 : Reach 84557 := rs (se 3 (by rfl) ⟨15854, by rfl⟩) (B 31709 (by norm_num) ⟨15854, by rfl⟩ (by norm_num))
theorem R51817 : Reach 51817 := rs (se 2 (by rfl) ⟨19431, by rfl⟩) (B 38863 (by norm_num) ⟨19431, by rfl⟩ (by norm_num))
theorem R51853 : Reach 51853 := rs (se 3 (by rfl) ⟨9722, by rfl⟩) (B 19445 (by norm_num) ⟨9722, by rfl⟩ (by norm_num))
theorem R84653 : Reach 84653 := rs (se 3 (by rfl) ⟨15872, by rfl⟩) (B 31745 (by norm_num) ⟨15872, by rfl⟩ (by norm_num))
theorem R51889 : Reach 51889 := rs (se 2 (by rfl) ⟨19458, by rfl⟩) (B 38917 (by norm_num) ⟨19458, by rfl⟩ (by norm_num))
theorem R51925 : Reach 51925 := rs (se 7 (by rfl) ⟨608, by rfl⟩) (B 1217 (by norm_num) ⟨608, by rfl⟩ (by norm_num))
theorem R84701 : Reach 84701 := rs (se 3 (by rfl) ⟨15881, by rfl⟩) (B 31763 (by norm_num) ⟨15881, by rfl⟩ (by norm_num))
theorem R51961 : Reach 51961 := rs (se 2 (by rfl) ⟨19485, by rfl⟩) (B 38971 (by norm_num) ⟨19485, by rfl⟩ (by norm_num))
theorem R51997 : Reach 51997 := rs (se 3 (by rfl) ⟨9749, by rfl⟩) (B 19499 (by norm_num) ⟨9749, by rfl⟩ (by norm_num))
theorem R52033 : Reach 52033 := rs (se 2 (by rfl) ⟨19512, by rfl⟩) (B 39025 (by norm_num) ⟨19512, by rfl⟩ (by norm_num))
theorem R84829 : Reach 84829 := rs (se 3 (by rfl) ⟨15905, by rfl⟩) (B 31811 (by norm_num) ⟨15905, by rfl⟩ (by norm_num))
theorem R52069 : Reach 52069 := rs (se 4 (by rfl) ⟨4881, by rfl⟩) (B 9763 (by norm_num) ⟨4881, by rfl⟩ (by norm_num))
theorem R150389 : Reach 150389 := rs (se 5 (by rfl) ⟨7049, by rfl⟩) (B 14099 (by norm_num) ⟨7049, by rfl⟩ (by norm_num))
theorem R52105 : Reach 52105 := rs (se 2 (by rfl) ⟨19539, by rfl⟩) (B 39079 (by norm_num) ⟨19539, by rfl⟩ (by norm_num))
theorem R52141 : Reach 52141 := rs (se 3 (by rfl) ⟨9776, by rfl⟩) (B 19553 (by norm_num) ⟨9776, by rfl⟩ (by norm_num))
theorem R52177 : Reach 52177 := rs (se 2 (by rfl) ⟨19566, by rfl⟩) (B 39133 (by norm_num) ⟨19566, by rfl⟩ (by norm_num))
theorem R117733 : Reach 117733 := rs (se 4 (by rfl) ⟨11037, by rfl⟩) (B 22075 (by norm_num) ⟨11037, by rfl⟩ (by norm_num))
theorem R216053 : Reach 216053 := rs (se 5 (by rfl) ⟨10127, by rfl⟩) (B 20255 (by norm_num) ⟨10127, by rfl⟩ (by norm_num))
theorem R52213 : Reach 52213 := rs (se 5 (by rfl) ⟨2447, by rfl⟩) (B 4895 (by norm_num) ⟨2447, by rfl⟩ (by norm_num))
theorem R84989 : Reach 84989 := rs (se 3 (by rfl) ⟨15935, by rfl⟩) (B 31871 (by norm_num) ⟨15935, by rfl⟩ (by norm_num))
theorem R52249 : Reach 52249 := rs (se 2 (by rfl) ⟨19593, by rfl⟩) (B 39187 (by norm_num) ⟨19593, by rfl⟩ (by norm_num))
theorem R52285 : Reach 52285 := rs (se 3 (by rfl) ⟨9803, by rfl⟩) (B 19607 (by norm_num) ⟨9803, by rfl⟩ (by norm_num))
theorem R117845 : Reach 117845 := rs (se 8 (by rfl) ⟨690, by rfl⟩) (B 1381 (by norm_num) ⟨690, by rfl⟩ (by norm_num))
theorem R52321 : Reach 52321 := rs (se 2 (by rfl) ⟨19620, by rfl⟩) (B 39241 (by norm_num) ⟨19620, by rfl⟩ (by norm_num))
theorem R52357 : Reach 52357 := rs (se 4 (by rfl) ⟨4908, by rfl⟩) (B 9817 (by norm_num) ⟨4908, by rfl⟩ (by norm_num))
theorem R85141 : Reach 85141 := rs (se 6 (by rfl) ⟨1995, by rfl⟩) (B 3991 (by norm_num) ⟨1995, by rfl⟩ (by norm_num))
theorem R52393 : Reach 52393 := rs (se 2 (by rfl) ⟨19647, by rfl⟩) (B 39295 (by norm_num) ⟨19647, by rfl⟩ (by norm_num))
theorem R52429 : Reach 52429 := rs (se 3 (by rfl) ⟨9830, by rfl⟩) (B 19661 (by norm_num) ⟨9830, by rfl⟩ (by norm_num))
theorem R52465 : Reach 52465 := rs (se 2 (by rfl) ⟨19674, by rfl⟩) (B 39349 (by norm_num) ⟨19674, by rfl⟩ (by norm_num))
theorem R118037 : Reach 118037 := rs (se 6 (by rfl) ⟨2766, by rfl⟩) (B 5533 (by norm_num) ⟨2766, by rfl⟩ (by norm_num))
theorem R52501 : Reach 52501 := rs (se 6 (by rfl) ⟨1230, by rfl⟩) (B 2461 (by norm_num) ⟨1230, by rfl⟩ (by norm_num))
theorem R150821 : Reach 150821 := rs (se 4 (by rfl) ⟨14139, by rfl⟩) (B 28279 (by norm_num) ⟨14139, by rfl⟩ (by norm_num))
theorem R52537 : Reach 52537 := rs (se 2 (by rfl) ⟨19701, by rfl⟩) (B 39403 (by norm_num) ⟨19701, by rfl⟩ (by norm_num))
theorem R52573 : Reach 52573 := rs (se 3 (by rfl) ⟨9857, by rfl⟩) (B 19715 (by norm_num) ⟨9857, by rfl⟩ (by norm_num))
theorem R52609 : Reach 52609 := rs (se 2 (by rfl) ⟨19728, by rfl⟩) (B 39457 (by norm_num) ⟨19728, by rfl⟩ (by norm_num))
theorem R52645 : Reach 52645 := rs (se 4 (by rfl) ⟨4935, by rfl⟩) (B 9871 (by norm_num) ⟨4935, by rfl⟩ (by norm_num))
theorem R85445 : Reach 85445 := rs (se 4 (by rfl) ⟨8010, by rfl⟩) (B 16021 (by norm_num) ⟨8010, by rfl⟩ (by norm_num))
theorem R52681 : Reach 52681 := rs (se 2 (by rfl) ⟨19755, by rfl⟩) (B 39511 (by norm_num) ⟨19755, by rfl⟩ (by norm_num))
theorem R52717 : Reach 52717 := rs (se 3 (by rfl) ⟨9884, by rfl⟩) (B 19769 (by norm_num) ⟨9884, by rfl⟩ (by norm_num))
theorem R52753 : Reach 52753 := rs (se 2 (by rfl) ⟨19782, by rfl⟩) (B 39565 (by norm_num) ⟨19782, by rfl⟩ (by norm_num))
theorem R151093 : Reach 151093 := rs (se 5 (by rfl) ⟨7082, by rfl⟩) (B 14165 (by norm_num) ⟨7082, by rfl⟩ (by norm_num))
theorem R52789 : Reach 52789 := rs (se 5 (by rfl) ⟨2474, by rfl⟩) (B 4949 (by norm_num) ⟨2474, by rfl⟩ (by norm_num))
theorem R52813 : Reach 52813 := rs (se 3 (by rfl) ⟨9902, by rfl⟩) (B 19805 (by norm_num) ⟨9902, by rfl⟩ (by norm_num))
theorem R52825 : Reach 52825 := rs (se 2 (by rfl) ⟨19809, by rfl⟩) (B 39619 (by norm_num) ⟨19809, by rfl⟩ (by norm_num))
theorem R52861 : Reach 52861 := rs (se 3 (by rfl) ⟨9911, by rfl⟩) (B 19823 (by norm_num) ⟨9911, by rfl⟩ (by norm_num))
theorem R52897 : Reach 52897 := rs (se 2 (by rfl) ⟨19836, by rfl⟩) (B 39673 (by norm_num) ⟨19836, by rfl⟩ (by norm_num))
theorem R52933 : Reach 52933 := rs (se 4 (by rfl) ⟨4962, by rfl⟩) (B 9925 (by norm_num) ⟨4962, by rfl⟩ (by norm_num))
theorem R151253 : Reach 151253 := rs (se 7 (by rfl) ⟨1772, by rfl⟩) (B 3545 (by norm_num) ⟨1772, by rfl⟩ (by norm_num))
theorem R52969 : Reach 52969 := rs (se 2 (by rfl) ⟨19863, by rfl⟩) (B 39727 (by norm_num) ⟨19863, by rfl⟩ (by norm_num))
theorem R85765 : Reach 85765 := rs (se 4 (by rfl) ⟨8040, by rfl⟩) (B 16081 (by norm_num) ⟨8040, by rfl⟩ (by norm_num))
theorem R53005 : Reach 53005 := rs (se 3 (by rfl) ⟨9938, by rfl⟩) (B 19877 (by norm_num) ⟨9938, by rfl⟩ (by norm_num))
theorem R53033 : Reach 53033 := rs (se 2 (by rfl) ⟨19887, by rfl⟩) (B 39775 (by norm_num) ⟨19887, by rfl⟩ (by norm_num))
theorem R2117461 : Reach 2117461 := rs (se 9 (by rfl) ⟨6203, by rfl⟩) (B 12407 (by norm_num) ⟨6203, by rfl⟩ (by norm_num))
theorem R53129 : Reach 53129 := rs (se 2 (by rfl) ⟨19923, by rfl⟩) (B 39847 (by norm_num) ⟨19923, by rfl⟩ (by norm_num))
theorem R53149 : Reach 53149 := rs (se 3 (by rfl) ⟨9965, by rfl⟩) (B 19931 (by norm_num) ⟨9965, by rfl⟩ (by norm_num))
theorem R315413 : Reach 315413 := rs (se 6 (by rfl) ⟨7392, by rfl⟩) (B 14785 (by norm_num) ⟨7392, by rfl⟩ (by norm_num))
theorem R53293 : Reach 53293 := rs (se 3 (by rfl) ⟨9992, by rfl⟩) (B 19985 (by norm_num) ⟨9992, by rfl⟩ (by norm_num))
theorem R1527893 : Reach 1527893 := rs (se 8 (by rfl) ⟨8952, by rfl⟩) (B 17905 (by norm_num) ⟨8952, by rfl⟩ (by norm_num))
theorem R151685 : Reach 151685 := rs (se 4 (by rfl) ⟨14220, by rfl⟩) (B 28441 (by norm_num) ⟨14220, by rfl⟩ (by norm_num))
theorem R151733 : Reach 151733 := rs (se 5 (by rfl) ⟨7112, by rfl⟩) (B 14225 (by norm_num) ⟨7112, by rfl⟩ (by norm_num))
theorem R86197 : Reach 86197 := rs (se 5 (by rfl) ⟨4040, by rfl⟩) (B 8081 (by norm_num) ⟨4040, by rfl⟩ (by norm_num))
theorem R119029 : Reach 119029 := rs (se 5 (by rfl) ⟨5579, by rfl⟩) (B 11159 (by norm_num) ⟨5579, by rfl⟩ (by norm_num))
theorem R86341 : Reach 86341 := rs (se 4 (by rfl) ⟨8094, by rfl⟩) (B 16189 (by norm_num) ⟨8094, by rfl⟩ (by norm_num))
theorem R119141 : Reach 119141 := rs (se 4 (by rfl) ⟨11169, by rfl⟩) (B 22339 (by norm_num) ⟨11169, by rfl⟩ (by norm_num))
theorem R250229 : Reach 250229 := rs (se 5 (by rfl) ⟨11729, by rfl⟩) (B 23459 (by norm_num) ⟨11729, by rfl⟩ (by norm_num))
theorem R86501 : Reach 86501 := rs (se 4 (by rfl) ⟨8109, by rfl⟩) (B 16219 (by norm_num) ⟨8109, by rfl⟩ (by norm_num))
theorem R152117 : Reach 152117 := rs (se 5 (by rfl) ⟨7130, by rfl⟩) (B 14261 (by norm_num) ⟨7130, by rfl⟩ (by norm_num))
theorem R86645 : Reach 86645 := rs (se 5 (by rfl) ⟨4061, by rfl⟩) (B 8123 (by norm_num) ⟨4061, by rfl⟩ (by norm_num))
theorem R119477 : Reach 119477 := rs (se 5 (by rfl) ⟨5600, by rfl⟩) (B 11201 (by norm_num) ⟨5600, by rfl⟩ (by norm_num))
theorem R86933 : Reach 86933 := rs (se 6 (by rfl) ⟨2037, by rfl⟩) (B 4075 (by norm_num) ⟨2037, by rfl⟩ (by norm_num))
theorem R152549 : Reach 152549 := rs (se 4 (by rfl) ⟨14301, by rfl⟩) (B 28603 (by norm_num) ⟨14301, by rfl⟩ (by norm_num))
theorem R87085 : Reach 87085 := rs (se 3 (by rfl) ⟨16328, by rfl⟩) (B 32657 (by norm_num) ⟨16328, by rfl⟩ (by norm_num))
theorem R54589 : Reach 54589 := rs (se 3 (by rfl) ⟨10235, by rfl⟩) (B 20471 (by norm_num) ⟨10235, by rfl⟩ (by norm_num))
theorem R87389 : Reach 87389 := rs (se 3 (by rfl) ⟨16385, by rfl⟩) (B 32771 (by norm_num) ⟨16385, by rfl⟩ (by norm_num))
theorem R152981 : Reach 152981 := rs (se 6 (by rfl) ⟨3585, by rfl⟩) (B 7171 (by norm_num) ⟨3585, by rfl⟩ (by norm_num))
theorem R54685 : Reach 54685 := rs (se 3 (by rfl) ⟨10253, by rfl⟩) (B 20507 (by norm_num) ⟨10253, by rfl⟩ (by norm_num))
theorem R185797 : Reach 185797 := rs (se 4 (by rfl) ⟨17418, by rfl⟩) (B 34837 (by norm_num) ⟨17418, by rfl⟩ (by norm_num))
theorem R54857 : Reach 54857 := rs (se 2 (by rfl) ⟨20571, by rfl⟩) (B 41143 (by norm_num) ⟨20571, by rfl⟩ (by norm_num))
theorem R87677 : Reach 87677 := rs (se 3 (by rfl) ⟨16439, by rfl⟩) (B 32879 (by norm_num) ⟨16439, by rfl⟩ (by norm_num))
theorem R54913 : Reach 54913 := rs (se 2 (by rfl) ⟨20592, by rfl⟩) (B 41185 (by norm_num) ⟨20592, by rfl⟩ (by norm_num))
theorem R218821 : Reach 218821 := rs (se 4 (by rfl) ⟨20514, by rfl⟩) (B 41029 (by norm_num) ⟨20514, by rfl⟩ (by norm_num))
theorem R55009 : Reach 55009 := rs (se 2 (by rfl) ⟨20628, by rfl⟩) (B 41257 (by norm_num) ⟨20628, by rfl⟩ (by norm_num))
theorem R186101 : Reach 186101 := rs (se 5 (by rfl) ⟨8723, by rfl⟩) (B 17447 (by norm_num) ⟨8723, by rfl⟩ (by norm_num))
theorem R55085 : Reach 55085 := rs (se 3 (by rfl) ⟨10328, by rfl⟩) (B 20657 (by norm_num) ⟨10328, by rfl⟩ (by norm_num))
theorem R153413 : Reach 153413 := rs (se 4 (by rfl) ⟨14382, by rfl⟩) (B 28765 (by norm_num) ⟨14382, by rfl⟩ (by norm_num))
theorem R55181 : Reach 55181 := rs (se 3 (by rfl) ⟨10346, by rfl⟩) (B 20693 (by norm_num) ⟨10346, by rfl⟩ (by norm_num))
theorem R55237 : Reach 55237 := rs (se 4 (by rfl) ⟨5178, by rfl⟩) (B 10357 (by norm_num) ⟨5178, by rfl⟩ (by norm_num))
theorem R55333 : Reach 55333 := rs (se 4 (by rfl) ⟨5187, by rfl⟩) (B 10375 (by norm_num) ⟨5187, by rfl⟩ (by norm_num))
theorem R88141 : Reach 88141 := rs (se 3 (by rfl) ⟨16526, by rfl⟩) (B 33053 (by norm_num) ⟨16526, by rfl⟩ (by norm_num))
theorem R284789 : Reach 284789 := rs (se 5 (by rfl) ⟨13349, by rfl⟩) (B 26699 (by norm_num) ⟨13349, by rfl⟩ (by norm_num))
theorem R55417 : Reach 55417 := rs (se 2 (by rfl) ⟨20781, by rfl⟩) (B 41563 (by norm_num) ⟨20781, by rfl⟩ (by norm_num))
theorem R317621 : Reach 317621 := rs (se 5 (by rfl) ⟨14888, by rfl⟩) (B 29777 (by norm_num) ⟨14888, by rfl⟩ (by norm_num))
theorem R55505 : Reach 55505 := rs (se 2 (by rfl) ⟨20814, by rfl⟩) (B 41629 (by norm_num) ⟨20814, by rfl⟩ (by norm_num))
theorem R88285 : Reach 88285 := rs (se 3 (by rfl) ⟨16553, by rfl⟩) (B 33107 (by norm_num) ⟨16553, by rfl⟩ (by norm_num))
theorem R153845 : Reach 153845 := rs (se 5 (by rfl) ⟨7211, by rfl⟩) (B 14423 (by norm_num) ⟨7211, by rfl⟩ (by norm_num))
theorem R55561 : Reach 55561 := rs (se 2 (by rfl) ⟨20835, by rfl⟩) (B 41671 (by norm_num) ⟨20835, by rfl⟩ (by norm_num))
theorem R55657 : Reach 55657 := rs (se 2 (by rfl) ⟨20871, by rfl⟩) (B 41743 (by norm_num) ⟨20871, by rfl⟩ (by norm_num))
theorem R219509 : Reach 219509 := rs (se 5 (by rfl) ⟨10289, by rfl⟩) (B 20579 (by norm_num) ⟨10289, by rfl⟩ (by norm_num))
theorem R88445 : Reach 88445 := rs (se 3 (by rfl) ⟨16583, by rfl⟩) (B 33167 (by norm_num) ⟨16583, by rfl⟩ (by norm_num))
theorem R252341 : Reach 252341 := rs (se 5 (by rfl) ⟨11828, by rfl⟩) (B 23657 (by norm_num) ⟨11828, by rfl⟩ (by norm_num))
theorem R88589 : Reach 88589 := rs (se 3 (by rfl) ⟨16610, by rfl⟩) (B 33221 (by norm_num) ⟨16610, by rfl⟩ (by norm_num))
theorem R55829 : Reach 55829 := rs (se 6 (by rfl) ⟨1308, by rfl⟩) (B 2617 (by norm_num) ⟨1308, by rfl⟩ (by norm_num))
theorem R55885 : Reach 55885 := rs (se 3 (by rfl) ⟨10478, by rfl⟩) (B 20957 (by norm_num) ⟨10478, by rfl⟩ (by norm_num))
theorem R350837 : Reach 350837 := rs (se 5 (by rfl) ⟨16445, by rfl⟩) (B 32891 (by norm_num) ⟨16445, by rfl⟩ (by norm_num))
theorem R154277 : Reach 154277 := rs (se 4 (by rfl) ⟨14463, by rfl⟩) (B 28927 (by norm_num) ⟨14463, by rfl⟩ (by norm_num))
theorem R55981 : Reach 55981 := rs (se 3 (by rfl) ⟨10496, by rfl⟩) (B 20993 (by norm_num) ⟨10496, by rfl⟩ (by norm_num))
theorem R88805 : Reach 88805 := rs (se 4 (by rfl) ⟨8325, by rfl⟩) (B 16651 (by norm_num) ⟨8325, by rfl⟩ (by norm_num))
theorem R88813 : Reach 88813 := rs (se 3 (by rfl) ⟨16652, by rfl⟩) (B 33305 (by norm_num) ⟨16652, by rfl⟩ (by norm_num))
theorem R416501 : Reach 416501 := rs (se 5 (by rfl) ⟨19523, by rfl⟩) (B 39047 (by norm_num) ⟨19523, by rfl⟩ (by norm_num))
theorem R88877 : Reach 88877 := rs (se 3 (by rfl) ⟨16664, by rfl⟩) (B 33329 (by norm_num) ⟨16664, by rfl⟩ (by norm_num))
theorem R56153 : Reach 56153 := rs (se 2 (by rfl) ⟨21057, by rfl⟩) (B 42115 (by norm_num) ⟨21057, by rfl⟩ (by norm_num))
theorem R56209 : Reach 56209 := rs (se 2 (by rfl) ⟨21078, by rfl⟩) (B 42157 (by norm_num) ⟨21078, by rfl⟩ (by norm_num))
theorem R89029 : Reach 89029 := rs (se 4 (by rfl) ⟨8346, by rfl⟩) (B 16693 (by norm_num) ⟨8346, by rfl⟩ (by norm_num))
theorem R56305 : Reach 56305 := rs (se 2 (by rfl) ⟨21114, by rfl⟩) (B 42229 (by norm_num) ⟨21114, by rfl⟩ (by norm_num))
theorem R121877 : Reach 121877 := rs (se 6 (by rfl) ⟨2856, by rfl⟩) (B 5713 (by norm_num) ⟨2856, by rfl⟩ (by norm_num))
theorem R154709 : Reach 154709 := rs (se 8 (by rfl) ⟨906, by rfl⟩) (B 1813 (by norm_num) ⟨906, by rfl⟩ (by norm_num))
theorem R56477 : Reach 56477 := rs (se 3 (by rfl) ⟨10589, by rfl⟩) (B 21179 (by norm_num) ⟨10589, by rfl⟩ (by norm_num))
theorem R56533 : Reach 56533 := rs (se 7 (by rfl) ⟨662, by rfl⟩) (B 1325 (by norm_num) ⟨662, by rfl⟩ (by norm_num))
theorem R89333 : Reach 89333 := rs (se 5 (by rfl) ⟨4187, by rfl⟩) (B 8375 (by norm_num) ⟨4187, by rfl⟩ (by norm_num))
theorem R56585 : Reach 56585 := rs (se 2 (by rfl) ⟨21219, by rfl⟩) (B 42439 (by norm_num) ⟨21219, by rfl⟩ (by norm_num))
theorem R56629 : Reach 56629 := rs (se 5 (by rfl) ⟨2654, by rfl⟩) (B 5309 (by norm_num) ⟨2654, by rfl⟩ (by norm_num))
theorem R56801 : Reach 56801 := rs (se 2 (by rfl) ⟨21300, by rfl⟩) (B 42601 (by norm_num) ⟨21300, by rfl⟩ (by norm_num))
theorem R56813 : Reach 56813 := rs (se 3 (by rfl) ⟨10652, by rfl⟩) (B 21305 (by norm_num) ⟨10652, by rfl⟩ (by norm_num))
theorem R155141 : Reach 155141 := rs (se 4 (by rfl) ⟨14544, by rfl⟩) (B 29089 (by norm_num) ⟨14544, by rfl⟩ (by norm_num))
theorem R56845 : Reach 56845 := rs (se 3 (by rfl) ⟨10658, by rfl⟩) (B 21317 (by norm_num) ⟨10658, by rfl⟩ (by norm_num))
theorem R56857 : Reach 56857 := rs (se 2 (by rfl) ⟨21321, by rfl⟩) (B 42643 (by norm_num) ⟨21321, by rfl⟩ (by norm_num))
theorem R56953 : Reach 56953 := rs (se 2 (by rfl) ⟨21357, by rfl⟩) (B 42715 (by norm_num) ⟨21357, by rfl⟩ (by norm_num))
theorem R220805 : Reach 220805 := rs (se 4 (by rfl) ⟨20700, by rfl⟩) (B 41401 (by norm_num) ⟨20700, by rfl⟩ (by norm_num))
theorem R351989 : Reach 351989 := rs (se 5 (by rfl) ⟨16499, by rfl⟩) (B 32999 (by norm_num) ⟨16499, by rfl⟩ (by norm_num))
theorem R57125 : Reach 57125 := rs (se 4 (by rfl) ⟨5355, by rfl⟩) (B 10711 (by norm_num) ⟨5355, by rfl⟩ (by norm_num))
theorem R384821 : Reach 384821 := rs (se 5 (by rfl) ⟨18038, by rfl⟩) (B 36077 (by norm_num) ⟨18038, by rfl⟩ (by norm_num))
theorem R57181 : Reach 57181 := rs (se 3 (by rfl) ⟨10721, by rfl⟩) (B 21443 (by norm_num) ⟨10721, by rfl⟩ (by norm_num))
theorem R155573 : Reach 155573 := rs (se 5 (by rfl) ⟨7292, by rfl⟩) (B 14585 (by norm_num) ⟨7292, by rfl⟩ (by norm_num))
theorem R57277 : Reach 57277 := rs (se 3 (by rfl) ⟨10739, by rfl⟩) (B 21479 (by norm_num) ⟨10739, by rfl⟩ (by norm_num))
theorem R122917 : Reach 122917 := rs (se 4 (by rfl) ⟨11523, by rfl⟩) (B 23047 (by norm_num) ⟨11523, by rfl⟩ (by norm_num))
theorem R286805 : Reach 286805 := rs (se 8 (by rfl) ⟨1680, by rfl⟩) (B 3361 (by norm_num) ⟨1680, by rfl⟩ (by norm_num))
theorem R57449 : Reach 57449 := rs (se 2 (by rfl) ⟨21543, by rfl⟩) (B 43087 (by norm_num) ⟨21543, by rfl⟩ (by norm_num))
theorem R123173 : Reach 123173 := rs (se 4 (by rfl) ⟨11547, by rfl⟩) (B 23095 (by norm_num) ⟨11547, by rfl⟩ (by norm_num))
theorem R156005 : Reach 156005 := rs (se 4 (by rfl) ⟨14625, by rfl⟩) (B 29251 (by norm_num) ⟨14625, by rfl⟩ (by norm_num))
theorem R90533 : Reach 90533 := rs (se 4 (by rfl) ⟨8487, by rfl⟩) (B 16975 (by norm_num) ⟨8487, by rfl⟩ (by norm_num))
theorem R57773 : Reach 57773 := rs (se 3 (by rfl) ⟨10832, by rfl⟩) (B 21665 (by norm_num) ⟨10832, by rfl⟩ (by norm_num))
theorem R57829 : Reach 57829 := rs (se 4 (by rfl) ⟨5421, by rfl⟩) (B 10843 (by norm_num) ⟨5421, by rfl⟩ (by norm_num))
theorem R90629 : Reach 90629 := rs (se 4 (by rfl) ⟨8496, by rfl⟩) (B 16993 (by norm_num) ⟨8496, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R57925 : Reach 57925 := rs (se 4 (by rfl) ⟨5430, by rfl⟩) (B 10861 (by norm_num) ⟨5430, by rfl⟩ (by norm_num))
theorem R156437 : Reach 156437 := rs (se 6 (by rfl) ⟨3666, by rfl⟩) (B 7333 (by norm_num) ⟨3666, by rfl⟩ (by norm_num))
theorem R222101 : Reach 222101 := rs (se 6 (by rfl) ⟨5205, by rfl⟩) (B 10411 (by norm_num) ⟨5205, by rfl⟩ (by norm_num))
theorem R418709 : Reach 418709 := rs (se 6 (by rfl) ⟨9813, by rfl⟩) (B 19627 (by norm_num) ⟨9813, by rfl⟩ (by norm_num))
theorem R386005 : Reach 386005 := rs (se 7 (by rfl) ⟨4523, by rfl⟩) (B 9047 (by norm_num) ⟨4523, by rfl⟩ (by norm_num))
theorem R58421 : Reach 58421 := rs (se 5 (by rfl) ⟨2738, by rfl⟩) (B 5477 (by norm_num) ⟨2738, by rfl⟩ (by norm_num))
theorem R58477 : Reach 58477 := rs (se 3 (by rfl) ⟨10964, by rfl⟩) (B 21929 (by norm_num) ⟨10964, by rfl⟩ (by norm_num))
theorem R124021 : Reach 124021 := rs (se 5 (by rfl) ⟨5813, by rfl⟩) (B 11627 (by norm_num) ⟨5813, by rfl⟩ (by norm_num))
theorem R156869 : Reach 156869 := rs (se 4 (by rfl) ⟨14706, by rfl⟩) (B 29413 (by norm_num) ⟨14706, by rfl⟩ (by norm_num))
theorem R58573 : Reach 58573 := rs (se 3 (by rfl) ⟨10982, by rfl⟩) (B 21965 (by norm_num) ⟨10982, by rfl⟩ (by norm_num))
theorem R517589 : Reach 517589 := rs (se 7 (by rfl) ⟨6065, by rfl⟩) (B 12131 (by norm_num) ⟨6065, by rfl⟩ (by norm_num))
theorem R222725 : Reach 222725 := rs (se 4 (by rfl) ⟨20880, by rfl⟩) (B 41761 (by norm_num) ⟨20880, by rfl⟩ (by norm_num))
theorem R157301 : Reach 157301 := rs (se 5 (by rfl) ⟨7373, by rfl⟩) (B 14747 (by norm_num) ⟨7373, by rfl⟩ (by norm_num))
theorem R190133 : Reach 190133 := rs (se 5 (by rfl) ⟨8912, by rfl⟩) (B 17825 (by norm_num) ⟨8912, by rfl⟩ (by norm_num))
theorem R91829 : Reach 91829 := rs (se 5 (by rfl) ⟨4304, by rfl⟩) (B 8609 (by norm_num) ⟨4304, by rfl⟩ (by norm_num))
theorem R59069 : Reach 59069 := rs (se 3 (by rfl) ⟨11075, by rfl⟩) (B 22151 (by norm_num) ⟨11075, by rfl⟩ (by norm_num))
theorem R59125 : Reach 59125 := rs (se 5 (by rfl) ⟨2771, by rfl⟩) (B 5543 (by norm_num) ⟨2771, by rfl⟩ (by norm_num))
theorem R223013 : Reach 223013 := rs (se 4 (by rfl) ⟨20907, by rfl⟩) (B 41815 (by norm_num) ⟨20907, by rfl⟩ (by norm_num))
theorem R59221 : Reach 59221 := rs (se 9 (by rfl) ⟨173, by rfl⟩) (B 347 (by norm_num) ⟨173, by rfl⟩ (by norm_num))
theorem R354293 : Reach 354293 := rs (se 5 (by rfl) ⟨16607, by rfl⟩) (B 33215 (by norm_num) ⟨16607, by rfl⟩ (by norm_num))
theorem R157733 : Reach 157733 := rs (se 4 (by rfl) ⟨14787, by rfl⟩) (B 29575 (by norm_num) ⟨14787, by rfl⟩ (by norm_num))
theorem R256117 : Reach 256117 := rs (se 5 (by rfl) ⟨12005, by rfl⟩) (B 24011 (by norm_num) ⟨12005, by rfl⟩ (by norm_num))
theorem R125077 : Reach 125077 := rs (se 6 (by rfl) ⟨2931, by rfl⟩) (B 5863 (by norm_num) ⟨2931, by rfl⟩ (by norm_num))
theorem R59549 : Reach 59549 := rs (se 3 (by rfl) ⟨11165, by rfl⟩) (B 22331 (by norm_num) ⟨11165, by rfl⟩ (by norm_num))
theorem R223397 : Reach 223397 := rs (se 4 (by rfl) ⟨20943, by rfl⟩) (B 41887 (by norm_num) ⟨20943, by rfl⟩ (by norm_num))
theorem R92333 : Reach 92333 := rs (se 3 (by rfl) ⟨17312, by rfl⟩) (B 34625 (by norm_num) ⟨17312, by rfl⟩ (by norm_num))
theorem R125381 : Reach 125381 := rs (se 4 (by rfl) ⟨11754, by rfl⟩) (B 23509 (by norm_num) ⟨11754, by rfl⟩ (by norm_num))
theorem R158165 : Reach 158165 := rs (se 7 (by rfl) ⟨1853, by rfl⟩) (B 3707 (by norm_num) ⟨1853, by rfl⟩ (by norm_num))
theorem R125525 : Reach 125525 := rs (se 8 (by rfl) ⟨735, by rfl⟩) (B 1471 (by norm_num) ⟨735, by rfl⟩ (by norm_num))
theorem R191333 : Reach 191333 := rs (se 4 (by rfl) ⟨17937, by rfl⟩) (B 35875 (by norm_num) ⟨17937, by rfl⟩ (by norm_num))
theorem R125813 : Reach 125813 := rs (se 5 (by rfl) ⟨5897, by rfl⟩) (B 11795 (by norm_num) ⟨5897, by rfl⟩ (by norm_num))
theorem R93053 : Reach 93053 := rs (se 3 (by rfl) ⟨17447, by rfl⟩) (B 34895 (by norm_num) ⟨17447, by rfl⟩ (by norm_num))
theorem R158597 : Reach 158597 := rs (se 4 (by rfl) ⟨14868, by rfl⟩) (B 29737 (by norm_num) ⟨14868, by rfl⟩ (by norm_num))
theorem R387989 : Reach 387989 := rs (se 6 (by rfl) ⟨9093, by rfl⟩) (B 18187 (by norm_num) ⟨9093, by rfl⟩ (by norm_num))
theorem R125941 : Reach 125941 := rs (se 5 (by rfl) ⟨5903, by rfl⟩) (B 11807 (by norm_num) ⟨5903, by rfl⟩ (by norm_num))
theorem R60517 : Reach 60517 := rs (se 4 (by rfl) ⟨5673, by rfl⟩) (B 11347 (by norm_num) ⟨5673, by rfl⟩ (by norm_num))
theorem R159029 : Reach 159029 := rs (se 5 (by rfl) ⟨7454, by rfl⟩) (B 14909 (by norm_num) ⟨7454, by rfl⟩ (by norm_num))
theorem R191909 : Reach 191909 := rs (se 4 (by rfl) ⟨17991, by rfl⟩) (B 35983 (by norm_num) ⟨17991, by rfl⟩ (by norm_num))
theorem R224693 : Reach 224693 := rs (se 5 (by rfl) ⟨10532, by rfl⟩) (B 21065 (by norm_num) ⟨10532, by rfl⟩ (by norm_num))
theorem R192149 : Reach 192149 := rs (se 6 (by rfl) ⟨4503, by rfl⟩) (B 9007 (by norm_num) ⟨4503, by rfl⟩ (by norm_num))
theorem R93973 : Reach 93973 := rs (se 6 (by rfl) ⟨2202, by rfl⟩) (B 4405 (by norm_num) ⟨2202, by rfl⟩ (by norm_num))
theorem R61565 : Reach 61565 := rs (se 3 (by rfl) ⟨11543, by rfl⟩) (B 23087 (by norm_num) ⟨11543, by rfl⟩ (by norm_num))
theorem R127109 : Reach 127109 := rs (se 4 (by rfl) ⟨11916, by rfl⟩) (B 23833 (by norm_num) ⟨11916, by rfl⟩ (by norm_num))
theorem R61669 : Reach 61669 := rs (se 4 (by rfl) ⟨5781, by rfl⟩) (B 11563 (by norm_num) ⟨5781, by rfl⟩ (by norm_num))
theorem R94565 : Reach 94565 := rs (se 4 (by rfl) ⟨8865, by rfl⟩) (B 17731 (by norm_num) ⟨8865, by rfl⟩ (by norm_num))
theorem R192901 : Reach 192901 := rs (se 4 (by rfl) ⟨18084, by rfl⟩) (B 36169 (by norm_num) ⟨18084, by rfl⟩ (by norm_num))
theorem R94765 : Reach 94765 := rs (se 3 (by rfl) ⟨17768, by rfl⟩) (B 35537 (by norm_num) ⟨17768, by rfl⟩ (by norm_num))
theorem R160309 : Reach 160309 := rs (se 5 (by rfl) ⟨7514, by rfl⟩) (B 15029 (by norm_num) ⟨7514, by rfl⟩ (by norm_num))
theorem R94861 : Reach 94861 := rs (se 3 (by rfl) ⟨17786, by rfl⟩) (B 35573 (by norm_num) ⟨17786, by rfl⟩ (by norm_num))
theorem R225989 : Reach 225989 := rs (se 4 (by rfl) ⟨21186, by rfl⟩) (B 42373 (by norm_num) ⟨21186, by rfl⟩ (by norm_num))
theorem R127781 : Reach 127781 := rs (se 4 (by rfl) ⟨11979, by rfl⟩) (B 23959 (by norm_num) ⟨11979, by rfl⟩ (by norm_num))
theorem R62317 : Reach 62317 := rs (se 3 (by rfl) ⟨11684, by rfl⟩) (B 23369 (by norm_num) ⟨11684, by rfl⟩ (by norm_num))
theorem R62461 : Reach 62461 := rs (se 3 (by rfl) ⟨11711, by rfl⟩) (B 23423 (by norm_num) ⟨11711, by rfl⟩ (by norm_num))
theorem R95357 : Reach 95357 := rs (se 3 (by rfl) ⟨17879, by rfl⟩) (B 35759 (by norm_num) ⟨17879, by rfl⟩ (by norm_num))
theorem R128213 : Reach 128213 := rs (se 7 (by rfl) ⟨1502, by rfl⟩) (B 3005 (by norm_num) ⟨1502, by rfl⟩ (by norm_num))
theorem R62797 : Reach 62797 := rs (se 3 (by rfl) ⟨11774, by rfl⟩) (B 23549 (by norm_num) ⟨11774, by rfl⟩ (by norm_num))
theorem R63013 : Reach 63013 := rs (se 4 (by rfl) ⟨5907, by rfl⟩) (B 11815 (by norm_num) ⟨5907, by rfl⟩ (by norm_num))
theorem R1799765 : Reach 1799765 := rs (se 8 (by rfl) ⟨10545, by rfl⟩) (B 21091 (by norm_num) ⟨10545, by rfl⟩ (by norm_num))
theorem R95845 : Reach 95845 := rs (se 4 (by rfl) ⟨8985, by rfl⟩) (B 17971 (by norm_num) ⟨8985, by rfl⟩ (by norm_num))
theorem R95941 : Reach 95941 := rs (se 4 (by rfl) ⟨8994, by rfl⟩) (B 17989 (by norm_num) ⟨8994, by rfl⟩ (by norm_num))
theorem R63389 : Reach 63389 := rs (se 3 (by rfl) ⟨11885, by rfl⟩) (B 23771 (by norm_num) ⟨11885, by rfl⟩ (by norm_num))
theorem R128965 : Reach 128965 := rs (se 4 (by rfl) ⟨12090, by rfl⟩) (B 24181 (by norm_num) ⟨12090, by rfl⟩ (by norm_num))
theorem R227285 : Reach 227285 := rs (se 7 (by rfl) ⟨2663, by rfl⟩) (B 5327 (by norm_num) ⟨2663, by rfl⟩ (by norm_num))
theorem R96221 : Reach 96221 := rs (se 3 (by rfl) ⟨18041, by rfl⟩) (B 36083 (by norm_num) ⟨18041, by rfl⟩ (by norm_num))
theorem R161797 : Reach 161797 := rs (se 4 (by rfl) ⟨15168, by rfl⟩) (B 30337 (by norm_num) ⟨15168, by rfl⟩ (by norm_num))
theorem R260117 : Reach 260117 := rs (se 6 (by rfl) ⟨6096, by rfl⟩) (B 12193 (by norm_num) ⟨6096, by rfl⟩ (by norm_num))
theorem R96365 : Reach 96365 := rs (se 3 (by rfl) ⟨18068, by rfl⟩) (B 36137 (by norm_num) ⟨18068, by rfl⟩ (by norm_num))
theorem R227893 : Reach 227893 := rs (se 5 (by rfl) ⟨10682, by rfl⟩) (B 21365 (by norm_num) ⟨10682, by rfl⟩ (by norm_num))
theorem R97037 : Reach 97037 := rs (se 3 (by rfl) ⟨18194, by rfl⟩) (B 36389 (by norm_num) ⟨18194, by rfl⟩ (by norm_num))
theorem R97109 : Reach 97109 := rs (se 9 (by rfl) ⟨284, by rfl⟩) (B 569 (by norm_num) ⟨284, by rfl⟩ (by norm_num))
theorem R97181 : Reach 97181 := rs (se 3 (by rfl) ⟨18221, by rfl⟩) (B 36443 (by norm_num) ⟨18221, by rfl⟩ (by norm_num))
theorem R97253 : Reach 97253 := rs (se 4 (by rfl) ⟨9117, by rfl⟩) (B 18235 (by norm_num) ⟨9117, by rfl⟩ (by norm_num))
theorem R97325 : Reach 97325 := rs (se 3 (by rfl) ⟨18248, by rfl⟩) (B 36497 (by norm_num) ⟨18248, by rfl⟩ (by norm_num))
theorem R97397 : Reach 97397 := rs (se 5 (by rfl) ⟨4565, by rfl⟩) (B 9131 (by norm_num) ⟨4565, by rfl⟩ (by norm_num))
theorem R64685 : Reach 64685 := rs (se 3 (by rfl) ⟨12128, by rfl⟩) (B 24257 (by norm_num) ⟨12128, by rfl⟩ (by norm_num))
theorem R97469 : Reach 97469 := rs (se 3 (by rfl) ⟨18275, by rfl⟩) (B 36551 (by norm_num) ⟨18275, by rfl⟩ (by norm_num))
theorem R64709 : Reach 64709 := rs (se 4 (by rfl) ⟨6066, by rfl⟩) (B 12133 (by norm_num) ⟨6066, by rfl⟩ (by norm_num))
theorem R64733 : Reach 64733 := rs (se 3 (by rfl) ⟨12137, by rfl⟩) (B 24275 (by norm_num) ⟨12137, by rfl⟩ (by norm_num))
theorem R228581 : Reach 228581 := rs (se 4 (by rfl) ⟨21429, by rfl⟩) (B 42859 (by norm_num) ⟨21429, by rfl⟩ (by norm_num))
theorem R64757 : Reach 64757 := rs (se 5 (by rfl) ⟨3035, by rfl⟩) (B 6071 (by norm_num) ⟨3035, by rfl⟩ (by norm_num))
theorem R97541 : Reach 97541 := rs (se 4 (by rfl) ⟨9144, by rfl⟩) (B 18289 (by norm_num) ⟨9144, by rfl⟩ (by norm_num))
theorem R64781 : Reach 64781 := rs (se 3 (by rfl) ⟨12146, by rfl⟩) (B 24293 (by norm_num) ⟨12146, by rfl⟩ (by norm_num))
theorem R64805 : Reach 64805 := rs (se 4 (by rfl) ⟨6075, by rfl⟩) (B 12151 (by norm_num) ⟨6075, by rfl⟩ (by norm_num))
theorem R64813 : Reach 64813 := rs (se 3 (by rfl) ⟨12152, by rfl⟩) (B 24305 (by norm_num) ⟨12152, by rfl⟩ (by norm_num))
theorem R64829 : Reach 64829 := rs (se 3 (by rfl) ⟨12155, by rfl⟩) (B 24311 (by norm_num) ⟨12155, by rfl⟩ (by norm_num))
theorem R97613 : Reach 97613 := rs (se 3 (by rfl) ⟨18302, by rfl⟩) (B 36605 (by norm_num) ⟨18302, by rfl⟩ (by norm_num))
theorem R64853 : Reach 64853 := rs (se 11 (by rfl) ⟨47, by rfl⟩) (B 95 (by norm_num) ⟨47, by rfl⟩ (by norm_num))
theorem R64877 : Reach 64877 := rs (se 3 (by rfl) ⟨12164, by rfl⟩) (B 24329 (by norm_num) ⟨12164, by rfl⟩ (by norm_num))
theorem R64901 : Reach 64901 := rs (se 4 (by rfl) ⟨6084, by rfl⟩) (B 12169 (by norm_num) ⟨6084, by rfl⟩ (by norm_num))
theorem R97685 : Reach 97685 := rs (se 6 (by rfl) ⟨2289, by rfl⟩) (B 4579 (by norm_num) ⟨2289, by rfl⟩ (by norm_num))
theorem R64925 : Reach 64925 := rs (se 3 (by rfl) ⟨12173, by rfl⟩) (B 24347 (by norm_num) ⟨12173, by rfl⟩ (by norm_num))
theorem R64949 : Reach 64949 := rs (se 5 (by rfl) ⟨3044, by rfl⟩) (B 6089 (by norm_num) ⟨3044, by rfl⟩ (by norm_num))
theorem R64973 : Reach 64973 := rs (se 3 (by rfl) ⟨12182, by rfl⟩) (B 24365 (by norm_num) ⟨12182, by rfl⟩ (by norm_num))
theorem R97757 : Reach 97757 := rs (se 3 (by rfl) ⟨18329, by rfl⟩) (B 36659 (by norm_num) ⟨18329, by rfl⟩ (by norm_num))
theorem R64997 : Reach 64997 := rs (se 4 (by rfl) ⟨6093, by rfl⟩) (B 12187 (by norm_num) ⟨6093, by rfl⟩ (by norm_num))
theorem R65021 : Reach 65021 := rs (se 3 (by rfl) ⟨12191, by rfl⟩) (B 24383 (by norm_num) ⟨12191, by rfl⟩ (by norm_num))
theorem R65045 : Reach 65045 := rs (se 6 (by rfl) ⟨1524, by rfl⟩) (B 3049 (by norm_num) ⟨1524, by rfl⟩ (by norm_num))
theorem R97829 : Reach 97829 := rs (se 4 (by rfl) ⟨9171, by rfl⟩) (B 18343 (by norm_num) ⟨9171, by rfl⟩ (by norm_num))
theorem R65069 : Reach 65069 := rs (se 3 (by rfl) ⟨12200, by rfl⟩) (B 24401 (by norm_num) ⟨12200, by rfl⟩ (by norm_num))
theorem R65093 : Reach 65093 := rs (se 4 (by rfl) ⟨6102, by rfl⟩) (B 12205 (by norm_num) ⟨6102, by rfl⟩ (by norm_num))
theorem R97861 : Reach 97861 := rs (se 4 (by rfl) ⟨9174, by rfl⟩) (B 18349 (by norm_num) ⟨9174, by rfl⟩ (by norm_num))
theorem R65117 : Reach 65117 := rs (se 3 (by rfl) ⟨12209, by rfl⟩) (B 24419 (by norm_num) ⟨12209, by rfl⟩ (by norm_num))
theorem R97901 : Reach 97901 := rs (se 3 (by rfl) ⟨18356, by rfl⟩) (B 36713 (by norm_num) ⟨18356, by rfl⟩ (by norm_num))
theorem R65141 : Reach 65141 := rs (se 5 (by rfl) ⟨3053, by rfl⟩) (B 6107 (by norm_num) ⟨3053, by rfl⟩ (by norm_num))
theorem R65165 : Reach 65165 := rs (se 3 (by rfl) ⟨12218, by rfl⟩) (B 24437 (by norm_num) ⟨12218, by rfl⟩ (by norm_num))
theorem R65189 : Reach 65189 := rs (se 4 (by rfl) ⟨6111, by rfl⟩) (B 12223 (by norm_num) ⟨6111, by rfl⟩ (by norm_num))
theorem R97973 : Reach 97973 := rs (se 5 (by rfl) ⟨4592, by rfl⟩) (B 9185 (by norm_num) ⟨4592, by rfl⟩ (by norm_num))
theorem R65213 : Reach 65213 := rs (se 3 (by rfl) ⟨12227, by rfl⟩) (B 24455 (by norm_num) ⟨12227, by rfl⟩ (by norm_num))
theorem R65237 : Reach 65237 := rs (se 7 (by rfl) ⟨764, by rfl⟩) (B 1529 (by norm_num) ⟨764, by rfl⟩ (by norm_num))
theorem R98005 : Reach 98005 := rs (se 7 (by rfl) ⟨1148, by rfl⟩) (B 2297 (by norm_num) ⟨1148, by rfl⟩ (by norm_num))
theorem R65261 : Reach 65261 := rs (se 3 (by rfl) ⟨12236, by rfl⟩) (B 24473 (by norm_num) ⟨12236, by rfl⟩ (by norm_num))
theorem R98045 : Reach 98045 := rs (se 3 (by rfl) ⟨18383, by rfl⟩) (B 36767 (by norm_num) ⟨18383, by rfl⟩ (by norm_num))
theorem R65285 : Reach 65285 := rs (se 4 (by rfl) ⟨6120, by rfl⟩) (B 12241 (by norm_num) ⟨6120, by rfl⟩ (by norm_num))
theorem R65309 : Reach 65309 := rs (se 3 (by rfl) ⟨12245, by rfl⟩) (B 24491 (by norm_num) ⟨12245, by rfl⟩ (by norm_num))
theorem R65333 : Reach 65333 := rs (se 5 (by rfl) ⟨3062, by rfl⟩) (B 6125 (by norm_num) ⟨3062, by rfl⟩ (by norm_num))
theorem R98117 : Reach 98117 := rs (se 4 (by rfl) ⟨9198, by rfl⟩) (B 18397 (by norm_num) ⟨9198, by rfl⟩ (by norm_num))
theorem R65357 : Reach 65357 := rs (se 3 (by rfl) ⟨12254, by rfl⟩) (B 24509 (by norm_num) ⟨12254, by rfl⟩ (by norm_num))
theorem R65381 : Reach 65381 := rs (se 4 (by rfl) ⟨6129, by rfl⟩) (B 12259 (by norm_num) ⟨6129, by rfl⟩ (by norm_num))
theorem R65405 : Reach 65405 := rs (se 3 (by rfl) ⟨12263, by rfl⟩) (B 24527 (by norm_num) ⟨12263, by rfl⟩ (by norm_num))
theorem R98189 : Reach 98189 := rs (se 3 (by rfl) ⟨18410, by rfl⟩) (B 36821 (by norm_num) ⟨18410, by rfl⟩ (by norm_num))
theorem R65429 : Reach 65429 := rs (se 6 (by rfl) ⟨1533, by rfl⟩) (B 3067 (by norm_num) ⟨1533, by rfl⟩ (by norm_num))
theorem R65453 : Reach 65453 := rs (se 3 (by rfl) ⟨12272, by rfl⟩) (B 24545 (by norm_num) ⟨12272, by rfl⟩ (by norm_num))
theorem R65477 : Reach 65477 := rs (se 4 (by rfl) ⟨6138, by rfl⟩) (B 12277 (by norm_num) ⟨6138, by rfl⟩ (by norm_num))
theorem R65485 : Reach 65485 := rs (se 3 (by rfl) ⟨12278, by rfl⟩) (B 24557 (by norm_num) ⟨12278, by rfl⟩ (by norm_num))
theorem R98261 : Reach 98261 := rs (se 7 (by rfl) ⟨1151, by rfl⟩) (B 2303 (by norm_num) ⟨1151, by rfl⟩ (by norm_num))
theorem R65501 : Reach 65501 := rs (se 3 (by rfl) ⟨12281, by rfl⟩) (B 24563 (by norm_num) ⟨12281, by rfl⟩ (by norm_num))
theorem R65525 : Reach 65525 := rs (se 5 (by rfl) ⟨3071, by rfl⟩) (B 6143 (by norm_num) ⟨3071, by rfl⟩ (by norm_num))
theorem R65537 : Reach 65537 := rs (se 2 (by rfl) ⟨24576, by rfl⟩) R49153
theorem R65555 : Reach 65555 := rs (se 1 (by rfl) ⟨49166, by rfl⟩) R98333
theorem R163889 : Reach 163889 := rs (se 2 (by rfl) ⟨61458, by rfl⟩) R122917
theorem R65585 : Reach 65585 := rs (se 2 (by rfl) ⟨24594, by rfl⟩) R49189
theorem R65603 : Reach 65603 := rs (se 1 (by rfl) ⟨49202, by rfl⟩) R98405
theorem R65633 : Reach 65633 := rs (se 2 (by rfl) ⟨24612, by rfl⟩) R49225
theorem R65651 : Reach 65651 := rs (se 1 (by rfl) ⟨49238, by rfl⟩) R98477
theorem R65681 : Reach 65681 := rs (se 2 (by rfl) ⟨24630, by rfl⟩) R49261
theorem R65699 : Reach 65699 := rs (se 1 (by rfl) ⟨49274, by rfl⟩) R98549
theorem R229553 : Reach 229553 := rs (se 2 (by rfl) ⟨86082, by rfl⟩) R172165
theorem R65713 : Reach 65713 := rs (se 2 (by rfl) ⟨24642, by rfl⟩) R49285
theorem R65729 : Reach 65729 := rs (se 2 (by rfl) ⟨24648, by rfl⟩) R49297
theorem R262349 : Reach 262349 := rs (se 3 (by rfl) ⟨49190, by rfl⟩) R98381
theorem R98513 : Reach 98513 := rs (se 2 (by rfl) ⟨36942, by rfl⟩) R73885
theorem R65747 : Reach 65747 := rs (se 1 (by rfl) ⟨49310, by rfl⟩) R98621
theorem R98531 : Reach 98531 := rs (se 1 (by rfl) ⟨73898, by rfl⟩) R147797
theorem R65777 : Reach 65777 := rs (se 2 (by rfl) ⟨24666, by rfl⟩) R49333
theorem R65795 : Reach 65795 := rs (se 1 (by rfl) ⟨49346, by rfl⟩) R98693
theorem R65825 : Reach 65825 := rs (se 2 (by rfl) ⟨24684, by rfl⟩) R49369
theorem R65843 : Reach 65843 := rs (se 1 (by rfl) ⟨49382, by rfl⟩) R98765
theorem R65873 : Reach 65873 := rs (se 2 (by rfl) ⟨24702, by rfl⟩) R49405
theorem R65891 : Reach 65891 := rs (se 1 (by rfl) ⟨49418, by rfl⟩) R98837
theorem R328049 : Reach 328049 := rs (se 2 (by rfl) ⟨123018, by rfl⟩) R246037
theorem R65921 : Reach 65921 := rs (se 2 (by rfl) ⟨24720, by rfl⟩) R49441
theorem R65939 : Reach 65939 := rs (se 1 (by rfl) ⟨49454, by rfl⟩) R98909
theorem R65969 : Reach 65969 := rs (se 2 (by rfl) ⟨24738, by rfl⟩) R49477
theorem R65987 : Reach 65987 := rs (se 1 (by rfl) ⟨49490, by rfl⟩) R98981
theorem R66017 : Reach 66017 := rs (se 2 (by rfl) ⟨24756, by rfl⟩) R49513
theorem R98801 : Reach 98801 := rs (se 2 (by rfl) ⟨37050, by rfl⟩) R74101
theorem R66035 : Reach 66035 := rs (se 1 (by rfl) ⟨49526, by rfl⟩) R99053
theorem R98819 : Reach 98819 := rs (se 1 (by rfl) ⟨74114, by rfl⟩) R148229
theorem R66065 : Reach 66065 := rs (se 2 (by rfl) ⟨24774, by rfl⟩) R49549
theorem R66083 : Reach 66083 := rs (se 1 (by rfl) ⟨49562, by rfl⟩) R99125
theorem R98851 : Reach 98851 := rs (se 1 (by rfl) ⟨74138, by rfl⟩) R148277
theorem R66113 : Reach 66113 := rs (se 2 (by rfl) ⟨24792, by rfl⟩) R49585
theorem R131665 : Reach 131665 := rs (se 2 (by rfl) ⟨49374, by rfl⟩) R98749
theorem R66131 : Reach 66131 := rs (se 1 (by rfl) ⟨49598, by rfl⟩) R99197
theorem R66161 : Reach 66161 := rs (se 2 (by rfl) ⟨24810, by rfl⟩) R49621
theorem R66179 : Reach 66179 := rs (se 1 (by rfl) ⟨49634, by rfl⟩) R99269
theorem R66209 : Reach 66209 := rs (se 2 (by rfl) ⟨24828, by rfl⟩) R49657
theorem R66227 : Reach 66227 := rs (se 1 (by rfl) ⟨49670, by rfl⟩) R99341
theorem R66257 : Reach 66257 := rs (se 2 (by rfl) ⟨24846, by rfl⟩) R49693
theorem R66275 : Reach 66275 := rs (se 1 (by rfl) ⟨49706, by rfl⟩) R99413
theorem R66305 : Reach 66305 := rs (se 2 (by rfl) ⟨24864, by rfl⟩) R49729
theorem R99089 : Reach 99089 := rs (se 2 (by rfl) ⟨37158, by rfl⟩) R74317
theorem R66323 : Reach 66323 := rs (se 1 (by rfl) ⟨49742, by rfl⟩) R99485
theorem R99107 : Reach 99107 := rs (se 1 (by rfl) ⟨74330, by rfl⟩) R148661
theorem R66353 : Reach 66353 := rs (se 2 (by rfl) ⟨24882, by rfl⟩) R49765
theorem R66371 : Reach 66371 := rs (se 1 (by rfl) ⟨49778, by rfl⟩) R99557
theorem R66401 : Reach 66401 := rs (se 2 (by rfl) ⟨24900, by rfl⟩) R49801
theorem R131939 : Reach 131939 := rs (se 1 (by rfl) ⟨98954, by rfl⟩) R197909
theorem R66419 : Reach 66419 := rs (se 1 (by rfl) ⟨49814, by rfl⟩) R99629
theorem R66449 : Reach 66449 := rs (se 2 (by rfl) ⟨24918, by rfl⟩) R49837
theorem R66467 : Reach 66467 := rs (se 1 (by rfl) ⟨49850, by rfl⟩) R99701
theorem R99235 : Reach 99235 := rs (se 1 (by rfl) ⟨74426, by rfl⟩) R148853
theorem R66497 : Reach 66497 := rs (se 2 (by rfl) ⟨24936, by rfl⟩) R49873
theorem R66515 : Reach 66515 := rs (se 1 (by rfl) ⟨49886, by rfl⟩) R99773
theorem R99299 : Reach 99299 := rs (se 1 (by rfl) ⟨74474, by rfl⟩) R148949
theorem R66545 : Reach 66545 := rs (se 2 (by rfl) ⟨24954, by rfl⟩) R49909
theorem R66563 : Reach 66563 := rs (se 1 (by rfl) ⟨49922, by rfl⟩) R99845
theorem R66593 : Reach 66593 := rs (se 2 (by rfl) ⟨24972, by rfl⟩) R49945
theorem R132131 : Reach 132131 := rs (se 1 (by rfl) ⟨99098, by rfl⟩) R198197
theorem R99377 : Reach 99377 := rs (se 2 (by rfl) ⟨37266, by rfl⟩) R74533
theorem R66611 : Reach 66611 := rs (se 1 (by rfl) ⟨49958, by rfl⟩) R99917
theorem R99395 : Reach 99395 := rs (se 1 (by rfl) ⟨74546, by rfl⟩) R149093
theorem R66641 : Reach 66641 := rs (se 2 (by rfl) ⟨24990, by rfl⟩) R49981
theorem R66659 : Reach 66659 := rs (se 1 (by rfl) ⟨49994, by rfl⟩) R99989
theorem R66689 : Reach 66689 := rs (se 2 (by rfl) ⟨25008, by rfl⟩) R50017
theorem R66691 : Reach 66691 := rs (se 1 (by rfl) ⟨50018, by rfl⟩) R100037
theorem R66707 : Reach 66707 := rs (se 1 (by rfl) ⟨50030, by rfl⟩) R100061
theorem R66737 : Reach 66737 := rs (se 2 (by rfl) ⟨25026, by rfl⟩) R50053
theorem R66755 : Reach 66755 := rs (se 1 (by rfl) ⟨50066, by rfl⟩) R100133
theorem R66785 : Reach 66785 := rs (se 2 (by rfl) ⟨25044, by rfl⟩) R50089
theorem R99569 : Reach 99569 := rs (se 2 (by rfl) ⟨37338, by rfl⟩) R74677
theorem R66803 : Reach 66803 := rs (se 1 (by rfl) ⟨50102, by rfl⟩) R100205
theorem R66833 : Reach 66833 := rs (se 2 (by rfl) ⟨25062, by rfl⟩) R50125
theorem R66835 : Reach 66835 := rs (se 1 (by rfl) ⟨50126, by rfl⟩) R100253
theorem R66851 : Reach 66851 := rs (se 1 (by rfl) ⟨50138, by rfl⟩) R100277
theorem R656693 : Reach 656693 := rs (se 5 (by rfl) ⟨30782, by rfl⟩) R61565
theorem R66881 : Reach 66881 := rs (se 2 (by rfl) ⟨25080, by rfl⟩) R50161
theorem R99665 : Reach 99665 := rs (se 2 (by rfl) ⟨37374, by rfl⟩) R74749
theorem R66899 : Reach 66899 := rs (se 1 (by rfl) ⟨50174, by rfl⟩) R100349
theorem R99683 : Reach 99683 := rs (se 1 (by rfl) ⟨74762, by rfl⟩) R149525
theorem R66929 : Reach 66929 := rs (se 2 (by rfl) ⟨25098, by rfl⟩) R50197
theorem R66947 : Reach 66947 := rs (se 1 (by rfl) ⟨50210, by rfl⟩) R100421
theorem R66977 : Reach 66977 := rs (se 2 (by rfl) ⟨25116, by rfl⟩) R50233
theorem R66995 : Reach 66995 := rs (se 1 (by rfl) ⟨50246, by rfl⟩) R100493
theorem R67025 : Reach 67025 := rs (se 2 (by rfl) ⟨25134, by rfl⟩) R50269
theorem R165347 : Reach 165347 := rs (se 1 (by rfl) ⟨124010, by rfl⟩) R248021
theorem R67043 : Reach 67043 := rs (se 1 (by rfl) ⟨50282, by rfl⟩) R100565
theorem R165361 : Reach 165361 := rs (se 2 (by rfl) ⟨62010, by rfl⟩) R124021
theorem R67073 : Reach 67073 := rs (se 2 (by rfl) ⟨25152, by rfl⟩) R50305
theorem R67091 : Reach 67091 := rs (se 1 (by rfl) ⟨50318, by rfl⟩) R100637
theorem R67121 : Reach 67121 := rs (se 2 (by rfl) ⟨25170, by rfl⟩) R50341
theorem R67139 : Reach 67139 := rs (se 1 (by rfl) ⟨50354, by rfl⟩) R100709
theorem R67169 : Reach 67169 := rs (se 2 (by rfl) ⟨25188, by rfl⟩) R50377
theorem R231011 : Reach 231011 := rs (se 1 (by rfl) ⟨173258, by rfl⟩) R346517
theorem R99953 : Reach 99953 := rs (se 2 (by rfl) ⟨37482, by rfl⟩) R74965
theorem R67187 : Reach 67187 := rs (se 1 (by rfl) ⟨50390, by rfl⟩) R100781
theorem R99971 : Reach 99971 := rs (se 1 (by rfl) ⟨74978, by rfl⟩) R149957
theorem R67217 : Reach 67217 := rs (se 2 (by rfl) ⟨25206, by rfl⟩) R50413
theorem R67235 : Reach 67235 := rs (se 1 (by rfl) ⟨50426, by rfl⟩) R100853
theorem R67265 : Reach 67265 := rs (se 2 (by rfl) ⟨25224, by rfl⟩) R50449
theorem R67283 : Reach 67283 := rs (se 1 (by rfl) ⟨50462, by rfl⟩) R100925
theorem R67313 : Reach 67313 := rs (se 2 (by rfl) ⟨25242, by rfl⟩) R50485
theorem R67331 : Reach 67331 := rs (se 1 (by rfl) ⟨50498, by rfl⟩) R100997
theorem R231173 : Reach 231173 := rs (se 4 (by rfl) ⟨21672, by rfl⟩) R43345
theorem R67361 : Reach 67361 := rs (se 2 (by rfl) ⟨25260, by rfl⟩) R50521
theorem R67379 : Reach 67379 := rs (se 1 (by rfl) ⟨50534, by rfl⟩) R101069
theorem R132941 : Reach 132941 := rs (se 3 (by rfl) ⟨24926, by rfl⟩) R49853
theorem R67409 : Reach 67409 := rs (se 2 (by rfl) ⟨25278, by rfl⟩) R50557
theorem R67427 : Reach 67427 := rs (se 1 (by rfl) ⟨50570, by rfl⟩) R101141
theorem R132977 : Reach 132977 := rs (se 2 (by rfl) ⟨49866, by rfl⟩) R99733
theorem R67457 : Reach 67457 := rs (se 2 (by rfl) ⟨25296, by rfl⟩) R50593
theorem R100241 : Reach 100241 := rs (se 2 (by rfl) ⟨37590, by rfl⟩) R75181
theorem R67475 : Reach 67475 := rs (se 1 (by rfl) ⟨50606, by rfl⟩) R101213
theorem R100259 : Reach 100259 := rs (se 1 (by rfl) ⟨75194, by rfl⟩) R150389
theorem R67505 : Reach 67505 := rs (se 2 (by rfl) ⟨25314, by rfl⟩) R50629
theorem R67523 : Reach 67523 := rs (se 1 (by rfl) ⟨50642, by rfl⟩) R101285
theorem R133073 : Reach 133073 := rs (se 2 (by rfl) ⟨49902, by rfl⟩) R99805
theorem R67553 : Reach 67553 := rs (se 2 (by rfl) ⟨25332, by rfl⟩) R50665
theorem R67571 : Reach 67571 := rs (se 1 (by rfl) ⟨50678, by rfl⟩) R101357
theorem R133123 : Reach 133123 := rs (se 1 (by rfl) ⟨99842, by rfl⟩) R199685
theorem R67601 : Reach 67601 := rs (se 2 (by rfl) ⟨25350, by rfl⟩) R50701
theorem R67619 : Reach 67619 := rs (se 1 (by rfl) ⟨50714, by rfl⟩) R101429
theorem R67649 : Reach 67649 := rs (se 2 (by rfl) ⟨25368, by rfl⟩) R50737
theorem R67667 : Reach 67667 := rs (se 1 (by rfl) ⟨50750, by rfl⟩) R101501
theorem R67697 : Reach 67697 := rs (se 2 (by rfl) ⟨25386, by rfl⟩) R50773
theorem R67715 : Reach 67715 := rs (se 1 (by rfl) ⟨50786, by rfl⟩) R101573
theorem R67745 : Reach 67745 := rs (se 2 (by rfl) ⟨25404, by rfl⟩) R50809
theorem R100529 : Reach 100529 := rs (se 2 (by rfl) ⟨37698, by rfl⟩) R75397
theorem R67763 : Reach 67763 := rs (se 1 (by rfl) ⟨50822, by rfl⟩) R101645
theorem R100547 : Reach 100547 := rs (se 1 (by rfl) ⟨75410, by rfl⟩) R150821
theorem R67793 : Reach 67793 := rs (se 2 (by rfl) ⟨25422, by rfl⟩) R50845
theorem R67811 : Reach 67811 := rs (se 1 (by rfl) ⟨50858, by rfl⟩) R101717
theorem R67841 : Reach 67841 := rs (se 2 (by rfl) ⟨25440, by rfl⟩) R50881
theorem R67859 : Reach 67859 := rs (se 1 (by rfl) ⟨50894, by rfl⟩) R101789
theorem R67889 : Reach 67889 := rs (se 2 (by rfl) ⟨25458, by rfl⟩) R50917
theorem R67907 : Reach 67907 := rs (se 1 (by rfl) ⟨50930, by rfl⟩) R101861
theorem R67937 : Reach 67937 := rs (se 2 (by rfl) ⟨25476, by rfl⟩) R50953
theorem R67955 : Reach 67955 := rs (se 1 (by rfl) ⟨50966, by rfl⟩) R101933
theorem R231821 : Reach 231821 := rs (se 3 (by rfl) ⟨43466, by rfl⟩) R86933
theorem R67985 : Reach 67985 := rs (se 2 (by rfl) ⟨25494, by rfl⟩) R50989
theorem R68003 : Reach 68003 := rs (se 1 (by rfl) ⟨51002, by rfl⟩) R102005
theorem R68033 : Reach 68033 := rs (se 2 (by rfl) ⟨25512, by rfl⟩) R51025
theorem R100817 : Reach 100817 := rs (se 2 (by rfl) ⟨37806, by rfl⟩) R75613
theorem R68051 : Reach 68051 := rs (se 1 (by rfl) ⟨51038, by rfl⟩) R102077
theorem R100835 : Reach 100835 := rs (se 1 (by rfl) ⟨75626, by rfl⟩) R151253
theorem R133613 : Reach 133613 := rs (se 3 (by rfl) ⟨25052, by rfl⟩) R50105
theorem R68081 : Reach 68081 := rs (se 2 (by rfl) ⟨25530, by rfl⟩) R51061
theorem R68099 : Reach 68099 := rs (se 1 (by rfl) ⟨51074, by rfl⟩) R102149
theorem R68129 : Reach 68129 := rs (se 2 (by rfl) ⟨25548, by rfl⟩) R51097
theorem R68147 : Reach 68147 := rs (se 1 (by rfl) ⟨51110, by rfl⟩) R102221
theorem R68177 : Reach 68177 := rs (se 2 (by rfl) ⟨25566, by rfl⟩) R51133
theorem R68195 : Reach 68195 := rs (se 1 (by rfl) ⟨51146, by rfl⟩) R102293
theorem R68225 : Reach 68225 := rs (se 2 (by rfl) ⟨25584, by rfl⟩) R51169
theorem R101009 : Reach 101009 := rs (se 2 (by rfl) ⟨37878, by rfl⟩) R75757
theorem R68243 : Reach 68243 := rs (se 1 (by rfl) ⟨51182, by rfl⟩) R102365
theorem R68273 : Reach 68273 := rs (se 2 (by rfl) ⟨25602, by rfl⟩) R51205
theorem R494261 : Reach 494261 := rs (se 5 (by rfl) ⟨23168, by rfl⟩) R46337
theorem R68291 : Reach 68291 := rs (se 1 (by rfl) ⟨51218, by rfl⟩) R102437
theorem R68321 : Reach 68321 := rs (se 2 (by rfl) ⟨25620, by rfl⟩) R51241
theorem R1018595 : Reach 1018595 := rs (se 1 (by rfl) ⟨763946, by rfl⟩) R1527893
theorem R101105 : Reach 101105 := rs (se 2 (by rfl) ⟨37914, by rfl⟩) R75829
theorem R68339 : Reach 68339 := rs (se 1 (by rfl) ⟨51254, by rfl⟩) R102509
theorem R101123 : Reach 101123 := rs (se 1 (by rfl) ⟨75842, by rfl⟩) R151685
theorem R68369 : Reach 68369 := rs (se 2 (by rfl) ⟨25638, by rfl⟩) R51277
theorem R101155 : Reach 101155 := rs (se 1 (by rfl) ⟨75866, by rfl⟩) R151733
theorem R68387 : Reach 68387 := rs (se 1 (by rfl) ⟨51290, by rfl⟩) R102581
theorem R68417 : Reach 68417 := rs (se 2 (by rfl) ⟨25656, by rfl⟩) R51313
theorem R68435 : Reach 68435 := rs (se 1 (by rfl) ⟨51326, by rfl⟩) R102653
theorem R68465 : Reach 68465 := rs (se 2 (by rfl) ⟨25674, by rfl⟩) R51349
theorem R166769 : Reach 166769 := rs (se 2 (by rfl) ⟨62538, by rfl⟩) R125077
theorem R68483 : Reach 68483 := rs (se 1 (by rfl) ⟨51362, by rfl⟩) R102725
theorem R68513 : Reach 68513 := rs (se 2 (by rfl) ⟨25692, by rfl⟩) R51385
theorem R166819 : Reach 166819 := rs (se 1 (by rfl) ⟨125114, by rfl⟩) R250229
theorem R68531 : Reach 68531 := rs (se 1 (by rfl) ⟨51398, by rfl⟩) R102797
theorem R854981 : Reach 854981 := rs (se 4 (by rfl) ⟨80154, by rfl⟩) R160309
theorem R68561 : Reach 68561 := rs (se 2 (by rfl) ⟨25710, by rfl⟩) R51421
theorem R68579 : Reach 68579 := rs (se 1 (by rfl) ⟨51434, by rfl⟩) R102869
theorem R68609 : Reach 68609 := rs (se 2 (by rfl) ⟨25728, by rfl⟩) R51457
theorem R101393 : Reach 101393 := rs (se 2 (by rfl) ⟨38022, by rfl⟩) R76045
theorem R68627 : Reach 68627 := rs (se 1 (by rfl) ⟨51470, by rfl⟩) R102941
theorem R101411 : Reach 101411 := rs (se 1 (by rfl) ⟨76058, by rfl⟩) R152117
theorem R68657 : Reach 68657 := rs (se 2 (by rfl) ⟨25746, by rfl⟩) R51493
theorem R265265 : Reach 265265 := rs (se 2 (by rfl) ⟨99474, by rfl⟩) R198949
theorem R68675 : Reach 68675 := rs (se 1 (by rfl) ⟨51506, by rfl⟩) R103013
theorem R68705 : Reach 68705 := rs (se 2 (by rfl) ⟨25764, by rfl⟩) R51529
theorem R68723 : Reach 68723 := rs (se 1 (by rfl) ⟨51542, by rfl⟩) R103085
theorem R68753 : Reach 68753 := rs (se 2 (by rfl) ⟨25782, by rfl⟩) R51565
theorem R68771 : Reach 68771 := rs (se 1 (by rfl) ⟨51578, by rfl⟩) R103157
theorem R68801 : Reach 68801 := rs (se 2 (by rfl) ⟨25800, by rfl⟩) R51601
theorem R68819 : Reach 68819 := rs (se 1 (by rfl) ⟨51614, by rfl⟩) R103229
theorem R199907 : Reach 199907 := rs (se 1 (by rfl) ⟨149930, by rfl⟩) R299861
theorem R68849 : Reach 68849 := rs (se 2 (by rfl) ⟨25818, by rfl⟩) R51637
theorem R68867 : Reach 68867 := rs (se 1 (by rfl) ⟨51650, by rfl⟩) R103301
theorem R68897 : Reach 68897 := rs (se 2 (by rfl) ⟨25836, by rfl⟩) R51673
theorem R101681 : Reach 101681 := rs (se 2 (by rfl) ⟨38130, by rfl⟩) R76261
theorem R68915 : Reach 68915 := rs (se 1 (by rfl) ⟨51686, by rfl⟩) R103373
theorem R101699 : Reach 101699 := rs (se 1 (by rfl) ⟨76274, by rfl⟩) R152549
theorem R68945 : Reach 68945 := rs (se 2 (by rfl) ⟨25854, by rfl⟩) R51709
theorem R68963 : Reach 68963 := rs (se 1 (by rfl) ⟨51722, by rfl⟩) R103445
theorem R68993 : Reach 68993 := rs (se 2 (by rfl) ⟨25872, by rfl⟩) R51745
theorem R69011 : Reach 69011 := rs (se 1 (by rfl) ⟨51758, by rfl⟩) R103517
theorem R69041 : Reach 69041 := rs (se 2 (by rfl) ⟨25890, by rfl⟩) R51781
theorem R69059 : Reach 69059 := rs (se 1 (by rfl) ⟨51794, by rfl⟩) R103589
theorem R232901 : Reach 232901 := rs (se 4 (by rfl) ⟨21834, by rfl⟩) R43669
theorem R69089 : Reach 69089 := rs (se 2 (by rfl) ⟨25908, by rfl⟩) R51817
theorem R69107 : Reach 69107 := rs (se 1 (by rfl) ⟨51830, by rfl⟩) R103661
theorem R69137 : Reach 69137 := rs (se 2 (by rfl) ⟨25926, by rfl⟩) R51853
theorem R69155 : Reach 69155 := rs (se 1 (by rfl) ⟨51866, by rfl⟩) R103733
theorem R69185 : Reach 69185 := rs (se 2 (by rfl) ⟨25944, by rfl⟩) R51889
theorem R101969 : Reach 101969 := rs (se 2 (by rfl) ⟨38238, by rfl⟩) R76477
theorem R69203 : Reach 69203 := rs (se 1 (by rfl) ⟨51902, by rfl⟩) R103805
theorem R101987 : Reach 101987 := rs (se 1 (by rfl) ⟨76490, by rfl⟩) R152981
theorem R69233 : Reach 69233 := rs (se 2 (by rfl) ⟨25962, by rfl⟩) R51925
theorem R69251 : Reach 69251 := rs (se 1 (by rfl) ⟨51938, by rfl⟩) R103877
theorem R69281 : Reach 69281 := rs (se 2 (by rfl) ⟨25980, by rfl⟩) R51961
theorem R69299 : Reach 69299 := rs (se 1 (by rfl) ⟨51974, by rfl⟩) R103949
theorem R69329 : Reach 69329 := rs (se 2 (by rfl) ⟨25998, by rfl⟩) R51997
theorem R69347 : Reach 69347 := rs (se 1 (by rfl) ⟨52010, by rfl⟩) R104021
theorem R69377 : Reach 69377 := rs (se 2 (by rfl) ⟨26016, by rfl⟩) R52033
theorem R69395 : Reach 69395 := rs (se 1 (by rfl) ⟨52046, by rfl⟩) R104093
theorem R69425 : Reach 69425 := rs (se 2 (by rfl) ⟨26034, by rfl⟩) R52069
theorem R69443 : Reach 69443 := rs (se 1 (by rfl) ⟨52082, by rfl⟩) R104165
theorem R560965 : Reach 560965 := rs (se 4 (by rfl) ⟨52590, by rfl⟩) R105181
theorem R69473 : Reach 69473 := rs (se 2 (by rfl) ⟨26052, by rfl⟩) R52105
theorem R102257 : Reach 102257 := rs (se 2 (by rfl) ⟨38346, by rfl⟩) R76693
theorem R69491 : Reach 69491 := rs (se 1 (by rfl) ⟨52118, by rfl⟩) R104237
theorem R102275 : Reach 102275 := rs (se 1 (by rfl) ⟨76706, by rfl⟩) R153413
theorem R69521 : Reach 69521 := rs (se 2 (by rfl) ⟨26070, by rfl⟩) R52141
theorem R69539 : Reach 69539 := rs (se 1 (by rfl) ⟨52154, by rfl⟩) R104309
theorem R69569 : Reach 69569 := rs (se 2 (by rfl) ⟨26088, by rfl⟩) R52177
theorem R69587 : Reach 69587 := rs (se 1 (by rfl) ⟨52190, by rfl⟩) R104381
theorem R69617 : Reach 69617 := rs (se 2 (by rfl) ⟨26106, by rfl⟩) R52213
theorem R167921 : Reach 167921 := rs (se 2 (by rfl) ⟨62970, by rfl⟩) R125941
theorem R69635 : Reach 69635 := rs (se 1 (by rfl) ⟨52226, by rfl⟩) R104453
theorem R69665 : Reach 69665 := rs (se 2 (by rfl) ⟨26124, by rfl⟩) R52249
theorem R69683 : Reach 69683 := rs (se 1 (by rfl) ⟨52262, by rfl⟩) R104525
theorem R69713 : Reach 69713 := rs (se 2 (by rfl) ⟨26142, by rfl⟩) R52285
theorem R69731 : Reach 69731 := rs (se 1 (by rfl) ⟨52298, by rfl⟩) R104597
theorem R69761 : Reach 69761 := rs (se 2 (by rfl) ⟨26160, by rfl⟩) R52321
theorem R102545 : Reach 102545 := rs (se 2 (by rfl) ⟨38454, by rfl⟩) R76909
theorem R69779 : Reach 69779 := rs (se 1 (by rfl) ⟨52334, by rfl⟩) R104669
theorem R102563 : Reach 102563 := rs (se 1 (by rfl) ⟨76922, by rfl⟩) R153845
theorem R69809 : Reach 69809 := rs (se 2 (by rfl) ⟨26178, by rfl⟩) R52357
theorem R69827 : Reach 69827 := rs (se 1 (by rfl) ⟨52370, by rfl⟩) R104741
theorem R69857 : Reach 69857 := rs (se 2 (by rfl) ⟨26196, by rfl⟩) R52393
theorem R69859 : Reach 69859 := rs (se 1 (by rfl) ⟨52394, by rfl⟩) R104789
theorem R69875 : Reach 69875 := rs (se 1 (by rfl) ⟨52406, by rfl⟩) R104813
theorem R69905 : Reach 69905 := rs (se 2 (by rfl) ⟨26214, by rfl⟩) R52429
theorem R168227 : Reach 168227 := rs (se 1 (by rfl) ⟨126170, by rfl⟩) R252341
theorem R69923 : Reach 69923 := rs (se 1 (by rfl) ⟨52442, by rfl⟩) R104885
theorem R69953 : Reach 69953 := rs (se 2 (by rfl) ⟨26232, by rfl⟩) R52465
theorem R69971 : Reach 69971 := rs (se 1 (by rfl) ⟨52478, by rfl⟩) R104957
theorem R70001 : Reach 70001 := rs (se 2 (by rfl) ⟨26250, by rfl⟩) R52501
theorem R70019 : Reach 70019 := rs (se 1 (by rfl) ⟨52514, by rfl⟩) R105029
theorem R70049 : Reach 70049 := rs (se 2 (by rfl) ⟨26268, by rfl⟩) R52537
theorem R233891 : Reach 233891 := rs (se 1 (by rfl) ⟨175418, by rfl⟩) R350837
theorem R102833 : Reach 102833 := rs (se 2 (by rfl) ⟨38562, by rfl⟩) R77125
theorem R70067 : Reach 70067 := rs (se 1 (by rfl) ⟨52550, by rfl⟩) R105101
theorem R102851 : Reach 102851 := rs (se 1 (by rfl) ⟨77138, by rfl⟩) R154277
theorem R70097 : Reach 70097 := rs (se 2 (by rfl) ⟨26286, by rfl⟩) R52573
theorem R70115 : Reach 70115 := rs (se 1 (by rfl) ⟨52586, by rfl⟩) R105173
theorem R266723 : Reach 266723 := rs (se 1 (by rfl) ⟨200042, by rfl⟩) R400085
theorem R70145 : Reach 70145 := rs (se 2 (by rfl) ⟨26304, by rfl⟩) R52609
theorem R70163 : Reach 70163 := rs (se 1 (by rfl) ⟨52622, by rfl⟩) R105245
theorem R70193 : Reach 70193 := rs (se 2 (by rfl) ⟨26322, by rfl⟩) R52645
theorem R70211 : Reach 70211 := rs (se 1 (by rfl) ⟨52658, by rfl⟩) R105317
theorem R70241 : Reach 70241 := rs (se 2 (by rfl) ⟨26340, by rfl⟩) R52681
theorem R70259 : Reach 70259 := rs (se 1 (by rfl) ⟨52694, by rfl⟩) R105389
theorem R70289 : Reach 70289 := rs (se 2 (by rfl) ⟨26358, by rfl⟩) R52717
theorem R70307 : Reach 70307 := rs (se 1 (by rfl) ⟨52730, by rfl⟩) R105461
theorem R70337 : Reach 70337 := rs (se 2 (by rfl) ⟨26376, by rfl⟩) R52753
theorem R103121 : Reach 103121 := rs (se 2 (by rfl) ⟨38670, by rfl⟩) R77341
theorem R70355 : Reach 70355 := rs (se 1 (by rfl) ⟨52766, by rfl⟩) R105533
theorem R103139 : Reach 103139 := rs (se 1 (by rfl) ⟨77354, by rfl⟩) R154709
theorem R201457 : Reach 201457 := rs (se 2 (by rfl) ⟨75546, by rfl⟩) R151093
theorem R70385 : Reach 70385 := rs (se 2 (by rfl) ⟨26394, by rfl⟩) R52789
theorem R70403 : Reach 70403 := rs (se 1 (by rfl) ⟨52802, by rfl⟩) R105605
theorem R70417 : Reach 70417 := rs (se 2 (by rfl) ⟨26406, by rfl⟩) R52813
theorem R70433 : Reach 70433 := rs (se 2 (by rfl) ⟨26412, by rfl⟩) R52825
theorem R70451 : Reach 70451 := rs (se 1 (by rfl) ⟨52838, by rfl⟩) R105677
theorem R70481 : Reach 70481 := rs (se 2 (by rfl) ⟨26430, by rfl⟩) R52861
theorem R70499 : Reach 70499 := rs (se 1 (by rfl) ⟨52874, by rfl⟩) R105749
theorem R70529 : Reach 70529 := rs (se 2 (by rfl) ⟨26448, by rfl⟩) R52897
theorem R70547 : Reach 70547 := rs (se 1 (by rfl) ⟨52910, by rfl⟩) R105821
theorem R70577 : Reach 70577 := rs (se 2 (by rfl) ⟨26466, by rfl⟩) R52933
theorem R70595 : Reach 70595 := rs (se 1 (by rfl) ⟨52946, by rfl⟩) R105893
theorem R70625 : Reach 70625 := rs (se 2 (by rfl) ⟨26484, by rfl⟩) R52969
theorem R103409 : Reach 103409 := rs (se 2 (by rfl) ⟨38778, by rfl⟩) R77557
theorem R70643 : Reach 70643 := rs (se 1 (by rfl) ⟨52982, by rfl⟩) R105965
theorem R103427 : Reach 103427 := rs (se 1 (by rfl) ⟨77570, by rfl⟩) R155141
theorem R70673 : Reach 70673 := rs (se 2 (by rfl) ⟨26502, by rfl⟩) R53005
theorem R169037 : Reach 169037 := rs (se 3 (by rfl) ⟨31694, by rfl⟩) R63389
theorem R2823281 : Reach 2823281 := rs (se 2 (by rfl) ⟨1058730, by rfl⟩) R2117461
theorem R791693 : Reach 791693 := rs (se 3 (by rfl) ⟨148442, by rfl⟩) R296885
theorem R234659 : Reach 234659 := rs (se 1 (by rfl) ⟨175994, by rfl⟩) R351989
theorem R70865 : Reach 70865 := rs (se 2 (by rfl) ⟨26574, by rfl⟩) R53149
theorem R234737 : Reach 234737 := rs (se 2 (by rfl) ⟨88026, by rfl⟩) R176053
theorem R103697 : Reach 103697 := rs (se 2 (by rfl) ⟨38886, by rfl⟩) R77773
theorem R103715 : Reach 103715 := rs (se 1 (by rfl) ⟨77786, by rfl⟩) R155573
theorem R71057 : Reach 71057 := rs (se 2 (by rfl) ⟨26646, by rfl⟩) R53293
theorem R267725 : Reach 267725 := rs (se 3 (by rfl) ⟨50198, by rfl⟩) R100397
theorem R103985 : Reach 103985 := rs (se 2 (by rfl) ⟨38994, by rfl⟩) R77989
theorem R104003 : Reach 104003 := rs (se 1 (by rfl) ⟨78002, by rfl⟩) R156005
theorem R366277 : Reach 366277 := rs (se 4 (by rfl) ⟨34338, by rfl⟩) R68677
theorem R71459 : Reach 71459 := rs (se 1 (by rfl) ⟨53594, by rfl⟩) R107189
theorem R104273 : Reach 104273 := rs (se 2 (by rfl) ⟨39102, by rfl⟩) R78205
theorem R104291 : Reach 104291 := rs (se 1 (by rfl) ⟨78218, by rfl⟩) R156437
theorem R104561 : Reach 104561 := rs (se 2 (by rfl) ⟨39210, by rfl⟩) R78421
theorem R104579 : Reach 104579 := rs (se 1 (by rfl) ⟨78434, by rfl⟩) R156869
theorem R104849 : Reach 104849 := rs (se 2 (by rfl) ⟨39318, by rfl⟩) R78637
theorem R104867 : Reach 104867 := rs (se 1 (by rfl) ⟨78650, by rfl⟩) R157301
theorem R268771 : Reach 268771 := rs (se 1 (by rfl) ⟨201578, by rfl⟩) R403157
theorem R236195 : Reach 236195 := rs (se 1 (by rfl) ⟨177146, by rfl⟩) R354293
theorem R105137 : Reach 105137 := rs (se 2 (by rfl) ⟨39426, by rfl⟩) R78853
theorem R105155 : Reach 105155 := rs (se 1 (by rfl) ⟨78866, by rfl⟩) R157733
theorem R236357 : Reach 236357 := rs (se 4 (by rfl) ⟨22158, by rfl⟩) R44317
theorem R236465 : Reach 236465 := rs (se 2 (by rfl) ⟨88674, by rfl⟩) R177349
theorem R105425 : Reach 105425 := rs (se 2 (by rfl) ⟨39534, by rfl⟩) R79069
theorem R72659 : Reach 72659 := rs (se 1 (by rfl) ⟨54494, by rfl⟩) R108989
theorem R105443 : Reach 105443 := rs (se 1 (by rfl) ⟨79082, by rfl⟩) R158165
theorem R72785 : Reach 72785 := rs (se 2 (by rfl) ⟨27294, by rfl⟩) R54589
theorem R72913 : Reach 72913 := rs (se 2 (by rfl) ⟨27342, by rfl⟩) R54685
theorem R138449 : Reach 138449 := rs (se 2 (by rfl) ⟨51918, by rfl⟩) R103837
theorem R105713 : Reach 105713 := rs (se 2 (by rfl) ⟨39642, by rfl⟩) R79285
theorem R72947 : Reach 72947 := rs (se 1 (by rfl) ⟨54710, by rfl⟩) R109421
theorem R105731 : Reach 105731 := rs (se 1 (by rfl) ⟨79298, by rfl⟩) R158597
theorem R73043 : Reach 73043 := rs (se 1 (by rfl) ⟨54782, by rfl⟩) R109565
theorem R73075 : Reach 73075 := rs (se 1 (by rfl) ⟨54806, by rfl⟩) R109613
theorem R237005 : Reach 237005 := rs (se 3 (by rfl) ⟨44438, by rfl⟩) R88877
theorem R73171 : Reach 73171 := rs (se 1 (by rfl) ⟨54878, by rfl⟩) R109757
theorem R73217 : Reach 73217 := rs (se 2 (by rfl) ⟨27456, by rfl⟩) R54913
theorem R106001 : Reach 106001 := rs (se 2 (by rfl) ⟨39750, by rfl⟩) R79501
theorem R106019 : Reach 106019 := rs (se 1 (by rfl) ⟨79514, by rfl⟩) R159029
theorem R73345 : Reach 73345 := rs (se 2 (by rfl) ⟨27504, by rfl⟩) R55009
theorem R335501 : Reach 335501 := rs (se 3 (by rfl) ⟨62906, by rfl⟩) R125813
theorem R73379 : Reach 73379 := rs (se 1 (by rfl) ⟨55034, by rfl⟩) R110069
theorem R990917 : Reach 990917 := rs (se 4 (by rfl) ⟨92898, by rfl⟩) R185797
theorem R73507 : Reach 73507 := rs (se 1 (by rfl) ⟨55130, by rfl⟩) R110261
theorem R1351565 : Reach 1351565 := rs (se 3 (by rfl) ⟨253418, by rfl⟩) R506837
theorem R73649 : Reach 73649 := rs (se 2 (by rfl) ⟨27618, by rfl⟩) R55237
theorem R171953 : Reach 171953 := rs (se 2 (by rfl) ⟨64482, by rfl⟩) R128965
theorem R73777 : Reach 73777 := rs (se 2 (by rfl) ⟨27666, by rfl⟩) R55333
theorem R303173 : Reach 303173 := rs (se 4 (by rfl) ⟨28422, by rfl⟩) R56845
theorem R73811 : Reach 73811 := rs (se 1 (by rfl) ⟨55358, by rfl⟩) R110717
theorem R73889 : Reach 73889 := rs (se 2 (by rfl) ⟨27708, by rfl⟩) R55417
theorem R73939 : Reach 73939 := rs (se 1 (by rfl) ⟨55454, by rfl⟩) R110909
theorem R74081 : Reach 74081 := rs (se 2 (by rfl) ⟨27780, by rfl⟩) R55561
theorem R401861 : Reach 401861 := rs (se 4 (by rfl) ⟨37674, by rfl⟩) R75349
theorem R74209 : Reach 74209 := rs (se 2 (by rfl) ⟨27828, by rfl⟩) R55657
theorem R74243 : Reach 74243 := rs (se 1 (by rfl) ⟨55682, by rfl⟩) R111365
theorem R74371 : Reach 74371 := rs (se 1 (by rfl) ⟨55778, by rfl⟩) R111557
theorem R303857 : Reach 303857 := rs (se 2 (by rfl) ⟨113946, by rfl⟩) R227893
theorem R74513 : Reach 74513 := rs (se 2 (by rfl) ⟨27942, by rfl⟩) R55885
theorem R74641 : Reach 74641 := rs (se 2 (by rfl) ⟨27990, by rfl⟩) R55981
theorem R74675 : Reach 74675 := rs (se 1 (by rfl) ⟨56006, by rfl⟩) R112013
theorem R926741 : Reach 926741 := rs (se 6 (by rfl) ⟨21720, by rfl⟩) R43441
theorem R74803 : Reach 74803 := rs (se 1 (by rfl) ⟨56102, by rfl⟩) R112205
theorem R74945 : Reach 74945 := rs (se 2 (by rfl) ⟨28104, by rfl⟩) R56209
theorem R75059 : Reach 75059 := rs (se 1 (by rfl) ⟨56294, by rfl⟩) R112589
theorem R75073 : Reach 75073 := rs (se 2 (by rfl) ⟨28152, by rfl⟩) R56305
theorem R75107 : Reach 75107 := rs (se 1 (by rfl) ⟨56330, by rfl⟩) R112661
theorem R173411 : Reach 173411 := rs (se 1 (by rfl) ⟨130058, by rfl⟩) R260117
theorem R75235 : Reach 75235 := rs (se 1 (by rfl) ⟨56426, by rfl⟩) R112853
theorem R75377 : Reach 75377 := rs (se 2 (by rfl) ⟨28266, by rfl⟩) R56533
theorem R75505 : Reach 75505 := rs (se 2 (by rfl) ⟨28314, by rfl⟩) R56629
theorem R75539 : Reach 75539 := rs (se 1 (by rfl) ⟨56654, by rfl⟩) R113309
theorem R75667 : Reach 75667 := rs (se 1 (by rfl) ⟨56750, by rfl⟩) R113501
theorem R75809 : Reach 75809 := rs (se 2 (by rfl) ⟨28428, by rfl⟩) R56857
theorem R141421 : Reach 141421 := rs (se 3 (by rfl) ⟨26516, by rfl⟩) R53033
theorem R43123 : Reach 43123 := rs (se 1 (by rfl) ⟨32342, by rfl⟩) R64685
theorem R43139 : Reach 43139 := rs (se 1 (by rfl) ⟨32354, by rfl⟩) R64709
theorem R43155 : Reach 43155 := rs (se 1 (by rfl) ⟨32366, by rfl⟩) R64733
theorem R75937 : Reach 75937 := rs (se 2 (by rfl) ⟨28476, by rfl⟩) R56953
theorem R43171 : Reach 43171 := rs (se 1 (by rfl) ⟨32378, by rfl⟩) R64757
theorem R43187 : Reach 43187 := rs (se 1 (by rfl) ⟨32390, by rfl⟩) R64781
theorem R43203 : Reach 43203 := rs (se 1 (by rfl) ⟨32402, by rfl⟩) R64805
theorem R75971 : Reach 75971 := rs (se 1 (by rfl) ⟨56978, by rfl⟩) R113957
theorem R43219 : Reach 43219 := rs (se 1 (by rfl) ⟨32414, by rfl⟩) R64829
theorem R43235 : Reach 43235 := rs (se 1 (by rfl) ⟨32426, by rfl⟩) R64853
theorem R43251 : Reach 43251 := rs (se 1 (by rfl) ⟨32438, by rfl⟩) R64877
theorem R43267 : Reach 43267 := rs (se 1 (by rfl) ⟨32450, by rfl⟩) R64901
theorem R43283 : Reach 43283 := rs (se 1 (by rfl) ⟨32462, by rfl⟩) R64925
theorem R43299 : Reach 43299 := rs (se 1 (by rfl) ⟨32474, by rfl⟩) R64949
theorem R76067 : Reach 76067 := rs (se 1 (by rfl) ⟨57050, by rfl⟩) R114101
theorem R43315 : Reach 43315 := rs (se 1 (by rfl) ⟨32486, by rfl⟩) R64973
theorem R43331 : Reach 43331 := rs (se 1 (by rfl) ⟨32498, by rfl⟩) R64997
theorem R76099 : Reach 76099 := rs (se 1 (by rfl) ⟨57074, by rfl⟩) R114149
theorem R174413 : Reach 174413 := rs (se 3 (by rfl) ⟨32702, by rfl⟩) R65405
theorem R43347 : Reach 43347 := rs (se 1 (by rfl) ⟨32510, by rfl⟩) R65021
theorem R76115 : Reach 76115 := rs (se 1 (by rfl) ⟨57086, by rfl⟩) R114173
theorem R43363 : Reach 43363 := rs (se 1 (by rfl) ⟨32522, by rfl⟩) R65045
theorem R141677 : Reach 141677 := rs (se 3 (by rfl) ⟨26564, by rfl⟩) R53129
theorem R43379 : Reach 43379 := rs (se 1 (by rfl) ⟨32534, by rfl⟩) R65069
theorem R43395 : Reach 43395 := rs (se 1 (by rfl) ⟨32546, by rfl⟩) R65093
theorem R43411 : Reach 43411 := rs (se 1 (by rfl) ⟨32558, by rfl⟩) R65117
theorem R43427 : Reach 43427 := rs (se 1 (by rfl) ⟨32570, by rfl⟩) R65141
theorem R43443 : Reach 43443 := rs (se 1 (by rfl) ⟨32582, by rfl⟩) R65165
theorem R43459 : Reach 43459 := rs (se 1 (by rfl) ⟨32594, by rfl⟩) R65189
theorem R76241 : Reach 76241 := rs (se 2 (by rfl) ⟨28590, by rfl⟩) R57181
theorem R43475 : Reach 43475 := rs (se 1 (by rfl) ⟨32606, by rfl⟩) R65213
theorem R469475 : Reach 469475 := rs (se 1 (by rfl) ⟨352106, by rfl⟩) R704213
theorem R43491 : Reach 43491 := rs (se 1 (by rfl) ⟨32618, by rfl⟩) R65237
theorem R43507 : Reach 43507 := rs (se 1 (by rfl) ⟨32630, by rfl⟩) R65261
theorem R43523 : Reach 43523 := rs (se 1 (by rfl) ⟨32642, by rfl⟩) R65285
theorem R43539 : Reach 43539 := rs (se 1 (by rfl) ⟨32654, by rfl⟩) R65309
theorem R43555 : Reach 43555 := rs (se 1 (by rfl) ⟨32666, by rfl⟩) R65333
theorem R43571 : Reach 43571 := rs (se 1 (by rfl) ⟨32678, by rfl⟩) R65357
theorem R43587 : Reach 43587 := rs (se 1 (by rfl) ⟨32690, by rfl⟩) R65381
theorem R76369 : Reach 76369 := rs (se 2 (by rfl) ⟨28638, by rfl⟩) R57277
theorem R43603 : Reach 43603 := rs (se 1 (by rfl) ⟨32702, by rfl⟩) R65405
theorem R43619 : Reach 43619 := rs (se 1 (by rfl) ⟨32714, by rfl⟩) R65429
theorem R43635 : Reach 43635 := rs (se 1 (by rfl) ⟨32726, by rfl⟩) R65453
theorem R76403 : Reach 76403 := rs (se 1 (by rfl) ⟨57302, by rfl⟩) R114605
theorem R43651 : Reach 43651 := rs (se 1 (by rfl) ⟨32738, by rfl⟩) R65477
theorem R43667 : Reach 43667 := rs (se 1 (by rfl) ⟨32750, by rfl⟩) R65501
theorem R43683 : Reach 43683 := rs (se 1 (by rfl) ⟨32762, by rfl⟩) R65525
theorem R43699 : Reach 43699 := rs (se 1 (by rfl) ⟨32774, by rfl⟩) R65549
theorem R43715 : Reach 43715 := rs (se 1 (by rfl) ⟨32786, by rfl⟩) R65573
theorem R43731 : Reach 43731 := rs (se 1 (by rfl) ⟨32798, by rfl⟩) R65597
theorem R43747 : Reach 43747 := rs (se 1 (by rfl) ⟨32810, by rfl⟩) R65621
theorem R43763 : Reach 43763 := rs (se 1 (by rfl) ⟨32822, by rfl⟩) R65645
theorem R76531 : Reach 76531 := rs (se 1 (by rfl) ⟨57398, by rfl⟩) R114797
theorem R43779 : Reach 43779 := rs (se 1 (by rfl) ⟨32834, by rfl⟩) R65669
theorem R43795 : Reach 43795 := rs (se 1 (by rfl) ⟨32846, by rfl⟩) R65693
theorem R43811 : Reach 43811 := rs (se 1 (by rfl) ⟨32858, by rfl⟩) R65717
theorem R43827 : Reach 43827 := rs (se 1 (by rfl) ⟨32870, by rfl⟩) R65741
theorem R43843 : Reach 43843 := rs (se 1 (by rfl) ⟨32882, by rfl⟩) R65765
theorem R43859 : Reach 43859 := rs (se 1 (by rfl) ⟨32894, by rfl⟩) R65789
theorem R43875 : Reach 43875 := rs (se 1 (by rfl) ⟨32906, by rfl⟩) R65813
theorem R43891 : Reach 43891 := rs (se 1 (by rfl) ⟨32918, by rfl⟩) R65837
theorem R43907 : Reach 43907 := rs (se 1 (by rfl) ⟨32930, by rfl⟩) R65861
theorem R43923 : Reach 43923 := rs (se 1 (by rfl) ⟨32942, by rfl⟩) R65885
theorem R43939 : Reach 43939 := rs (se 1 (by rfl) ⟨32954, by rfl⟩) R65909
theorem R43955 : Reach 43955 := rs (se 1 (by rfl) ⟨32966, by rfl⟩) R65933
theorem R43971 : Reach 43971 := rs (se 1 (by rfl) ⟨32978, by rfl⟩) R65957
theorem R43987 : Reach 43987 := rs (se 1 (by rfl) ⟨32990, by rfl⟩) R65981
theorem R44003 : Reach 44003 := rs (se 1 (by rfl) ⟨33002, by rfl⟩) R66005
theorem R44019 : Reach 44019 := rs (se 1 (by rfl) ⟨33014, by rfl⟩) R66029
theorem R44035 : Reach 44035 := rs (se 1 (by rfl) ⟨33026, by rfl⟩) R66053
theorem R44051 : Reach 44051 := rs (se 1 (by rfl) ⟨33038, by rfl⟩) R66077
theorem R44067 : Reach 44067 := rs (se 1 (by rfl) ⟨33050, by rfl⟩) R66101
theorem R76835 : Reach 76835 := rs (se 1 (by rfl) ⟨57626, by rfl⟩) R115253
theorem R109603 : Reach 109603 := rs (se 1 (by rfl) ⟨82202, by rfl⟩) R164405
theorem R44083 : Reach 44083 := rs (se 1 (by rfl) ⟨33062, by rfl⟩) R66125
theorem R44099 : Reach 44099 := rs (se 1 (by rfl) ⟨33074, by rfl⟩) R66149
theorem R44115 : Reach 44115 := rs (se 1 (by rfl) ⟨33086, by rfl⟩) R66173
theorem R44131 : Reach 44131 := rs (se 1 (by rfl) ⟨33098, by rfl⟩) R66197
theorem R44147 : Reach 44147 := rs (se 1 (by rfl) ⟨33110, by rfl⟩) R66221
theorem R44163 : Reach 44163 := rs (se 1 (by rfl) ⟨33122, by rfl⟩) R66245
theorem R44179 : Reach 44179 := rs (se 1 (by rfl) ⟨33134, by rfl⟩) R66269
theorem R44195 : Reach 44195 := rs (se 1 (by rfl) ⟨33146, by rfl⟩) R66293
theorem R76963 : Reach 76963 := rs (se 1 (by rfl) ⟨57722, by rfl⟩) R115445
theorem R109745 : Reach 109745 := rs (se 2 (by rfl) ⟨41154, by rfl⟩) R82309
theorem R44211 : Reach 44211 := rs (se 1 (by rfl) ⟨33158, by rfl⟩) R66317
theorem R44227 : Reach 44227 := rs (se 1 (by rfl) ⟨33170, by rfl⟩) R66341
theorem R44243 : Reach 44243 := rs (se 1 (by rfl) ⟨33182, by rfl⟩) R66365
theorem R109795 : Reach 109795 := rs (se 1 (by rfl) ⟨82346, by rfl⟩) R164693
theorem R44259 : Reach 44259 := rs (se 1 (by rfl) ⟨33194, by rfl⟩) R66389
theorem R44275 : Reach 44275 := rs (se 1 (by rfl) ⟨33206, by rfl⟩) R66413
theorem R44291 : Reach 44291 := rs (se 1 (by rfl) ⟨33218, by rfl⟩) R66437
theorem R44307 : Reach 44307 := rs (se 1 (by rfl) ⟨33230, by rfl⟩) R66461
theorem R44323 : Reach 44323 := rs (se 1 (by rfl) ⟨33242, by rfl⟩) R66485
theorem R77105 : Reach 77105 := rs (se 2 (by rfl) ⟨28914, by rfl⟩) R57829
theorem R44339 : Reach 44339 := rs (se 1 (by rfl) ⟨33254, by rfl⟩) R66509
theorem R44355 : Reach 44355 := rs (se 1 (by rfl) ⟨33266, by rfl⟩) R66533
theorem R240965 : Reach 240965 := rs (se 4 (by rfl) ⟨22590, by rfl⟩) R45181
theorem R44371 : Reach 44371 := rs (se 1 (by rfl) ⟨33278, by rfl⟩) R66557
theorem R44387 : Reach 44387 := rs (se 1 (by rfl) ⟨33290, by rfl⟩) R66581
theorem R109937 : Reach 109937 := rs (se 2 (by rfl) ⟨41226, by rfl⟩) R82453
theorem R44403 : Reach 44403 := rs (se 1 (by rfl) ⟨33302, by rfl⟩) R66605
theorem R44419 : Reach 44419 := rs (se 1 (by rfl) ⟨33314, by rfl⟩) R66629
theorem R44435 : Reach 44435 := rs (se 1 (by rfl) ⟨33326, by rfl⟩) R66653
theorem R44451 : Reach 44451 := rs (se 1 (by rfl) ⟨33338, by rfl⟩) R66677
theorem R77233 : Reach 77233 := rs (se 2 (by rfl) ⟨28962, by rfl⟩) R57925
theorem R44467 : Reach 44467 := rs (se 1 (by rfl) ⟨33350, by rfl⟩) R66701
theorem R44483 : Reach 44483 := rs (se 1 (by rfl) ⟨33362, by rfl⟩) R66725
theorem R44499 : Reach 44499 := rs (se 1 (by rfl) ⟨33374, by rfl⟩) R66749
theorem R44515 : Reach 44515 := rs (se 1 (by rfl) ⟨33386, by rfl⟩) R66773
theorem R44531 : Reach 44531 := rs (se 1 (by rfl) ⟨33398, by rfl⟩) R66797
theorem R44547 : Reach 44547 := rs (se 1 (by rfl) ⟨33410, by rfl⟩) R66821
theorem R44563 : Reach 44563 := rs (se 1 (by rfl) ⟨33422, by rfl⟩) R66845
theorem R44579 : Reach 44579 := rs (se 1 (by rfl) ⟨33434, by rfl⟩) R66869
theorem R44595 : Reach 44595 := rs (se 1 (by rfl) ⟨33446, by rfl⟩) R66893
theorem R44611 : Reach 44611 := rs (se 1 (by rfl) ⟨33458, by rfl⟩) R66917
theorem R44627 : Reach 44627 := rs (se 1 (by rfl) ⟨33470, by rfl⟩) R66941
theorem R44643 : Reach 44643 := rs (se 1 (by rfl) ⟨33482, by rfl⟩) R66965
theorem R44659 : Reach 44659 := rs (se 1 (by rfl) ⟨33494, by rfl⟩) R66989
theorem R44675 : Reach 44675 := rs (se 1 (by rfl) ⟨33506, by rfl⟩) R67013
theorem R44691 : Reach 44691 := rs (se 1 (by rfl) ⟨33518, by rfl⟩) R67037
theorem R44707 : Reach 44707 := rs (se 1 (by rfl) ⟨33530, by rfl⟩) R67061
theorem R44723 : Reach 44723 := rs (se 1 (by rfl) ⟨33542, by rfl⟩) R67085
theorem R44739 : Reach 44739 := rs (se 1 (by rfl) ⟨33554, by rfl⟩) R67109
theorem R44755 : Reach 44755 := rs (se 1 (by rfl) ⟨33566, by rfl⟩) R67133
theorem R44771 : Reach 44771 := rs (se 1 (by rfl) ⟨33578, by rfl⟩) R67157
theorem R44787 : Reach 44787 := rs (se 1 (by rfl) ⟨33590, by rfl⟩) R67181
theorem R44803 : Reach 44803 := rs (se 1 (by rfl) ⟨33602, by rfl⟩) R67205
theorem R44819 : Reach 44819 := rs (se 1 (by rfl) ⟨33614, by rfl⟩) R67229
theorem R44835 : Reach 44835 := rs (se 1 (by rfl) ⟨33626, by rfl⟩) R67253
theorem R143153 : Reach 143153 := rs (se 2 (by rfl) ⟨53682, by rfl⟩) R107365
theorem R44851 : Reach 44851 := rs (se 1 (by rfl) ⟨33638, by rfl⟩) R67277
theorem R44867 : Reach 44867 := rs (se 1 (by rfl) ⟨33650, by rfl⟩) R67301
theorem R44883 : Reach 44883 := rs (se 1 (by rfl) ⟨33662, by rfl⟩) R67325
theorem R143203 : Reach 143203 := rs (se 1 (by rfl) ⟨107402, by rfl⟩) R214805
theorem R44899 : Reach 44899 := rs (se 1 (by rfl) ⟨33674, by rfl⟩) R67349
theorem R44915 : Reach 44915 := rs (se 1 (by rfl) ⟨33686, by rfl⟩) R67373
theorem R44931 : Reach 44931 := rs (se 1 (by rfl) ⟨33698, by rfl⟩) R67397
theorem R77699 : Reach 77699 := rs (se 1 (by rfl) ⟨58274, by rfl⟩) R116549
theorem R44947 : Reach 44947 := rs (se 1 (by rfl) ⟨33710, by rfl⟩) R67421
theorem R44963 : Reach 44963 := rs (se 1 (by rfl) ⟨33722, by rfl⟩) R67445
theorem R44979 : Reach 44979 := rs (se 1 (by rfl) ⟨33734, by rfl⟩) R67469
theorem R44995 : Reach 44995 := rs (se 1 (by rfl) ⟨33746, by rfl⟩) R67493
theorem R45011 : Reach 45011 := rs (se 1 (by rfl) ⟨33758, by rfl⟩) R67517
theorem R45027 : Reach 45027 := rs (se 1 (by rfl) ⟨33770, by rfl⟩) R67541
theorem R45043 : Reach 45043 := rs (se 1 (by rfl) ⟨33782, by rfl⟩) R67565
theorem R45059 : Reach 45059 := rs (se 1 (by rfl) ⟨33794, by rfl⟩) R67589
theorem R77827 : Reach 77827 := rs (se 1 (by rfl) ⟨58370, by rfl⟩) R116741
theorem R45075 : Reach 45075 := rs (se 1 (by rfl) ⟨33806, by rfl⟩) R67613
theorem R45091 : Reach 45091 := rs (se 1 (by rfl) ⟨33818, by rfl⟩) R67637
theorem R45107 : Reach 45107 := rs (se 1 (by rfl) ⟨33830, by rfl⟩) R67661
theorem R110641 : Reach 110641 := rs (se 2 (by rfl) ⟨41490, by rfl⟩) R82981
theorem R45123 : Reach 45123 := rs (se 1 (by rfl) ⟨33842, by rfl⟩) R67685
theorem R45139 : Reach 45139 := rs (se 1 (by rfl) ⟨33854, by rfl⟩) R67709
theorem R45155 : Reach 45155 := rs (se 1 (by rfl) ⟨33866, by rfl⟩) R67733
theorem R45171 : Reach 45171 := rs (se 1 (by rfl) ⟨33878, by rfl⟩) R67757
theorem R45187 : Reach 45187 := rs (se 1 (by rfl) ⟨33890, by rfl⟩) R67781
theorem R77969 : Reach 77969 := rs (se 2 (by rfl) ⟨29238, by rfl⟩) R58477
theorem R45203 : Reach 45203 := rs (se 1 (by rfl) ⟨33902, by rfl⟩) R67805
theorem R45219 : Reach 45219 := rs (se 1 (by rfl) ⟨33914, by rfl⟩) R67829
theorem R45235 : Reach 45235 := rs (se 1 (by rfl) ⟨33926, by rfl⟩) R67853
theorem R45251 : Reach 45251 := rs (se 1 (by rfl) ⟨33938, by rfl⟩) R67877
theorem R45267 : Reach 45267 := rs (se 1 (by rfl) ⟨33950, by rfl⟩) R67901
theorem R45283 : Reach 45283 := rs (se 1 (by rfl) ⟨33962, by rfl⟩) R67925
theorem R45299 : Reach 45299 := rs (se 1 (by rfl) ⟨33974, by rfl⟩) R67949
theorem R45315 : Reach 45315 := rs (se 1 (by rfl) ⟨33986, by rfl⟩) R67973
theorem R45331 : Reach 45331 := rs (se 1 (by rfl) ⟨33998, by rfl⟩) R67997
theorem R78097 : Reach 78097 := rs (se 2 (by rfl) ⟨29286, by rfl⟩) R58573
theorem R45347 : Reach 45347 := rs (se 1 (by rfl) ⟨34010, by rfl⟩) R68021
theorem R45363 : Reach 45363 := rs (se 1 (by rfl) ⟨34022, by rfl⟩) R68045
theorem R45379 : Reach 45379 := rs (se 1 (by rfl) ⟨34034, by rfl⟩) R68069
theorem R110929 : Reach 110929 := rs (se 2 (by rfl) ⟨41598, by rfl⟩) R83197
theorem R45395 : Reach 45395 := rs (se 1 (by rfl) ⟨34046, by rfl⟩) R68093
theorem R45411 : Reach 45411 := rs (se 1 (by rfl) ⟨34058, by rfl⟩) R68117
theorem R45427 : Reach 45427 := rs (se 1 (by rfl) ⟨34070, by rfl⟩) R68141
theorem R45443 : Reach 45443 := rs (se 1 (by rfl) ⟨34082, by rfl⟩) R68165
theorem R176525 : Reach 176525 := rs (se 3 (by rfl) ⟨33098, by rfl⟩) R66197
theorem R45459 : Reach 45459 := rs (se 1 (by rfl) ⟨34094, by rfl⟩) R68189
theorem R45475 : Reach 45475 := rs (se 1 (by rfl) ⟨34106, by rfl⟩) R68213
theorem R45491 : Reach 45491 := rs (se 1 (by rfl) ⟨34118, by rfl⟩) R68237
theorem R45507 : Reach 45507 := rs (se 1 (by rfl) ⟨34130, by rfl⟩) R68261
theorem R45523 : Reach 45523 := rs (se 1 (by rfl) ⟨34142, by rfl⟩) R68285
theorem R45539 : Reach 45539 := rs (se 1 (by rfl) ⟨34154, by rfl⟩) R68309
theorem R45555 : Reach 45555 := rs (se 1 (by rfl) ⟨34166, by rfl⟩) R68333
theorem R45571 : Reach 45571 := rs (se 1 (by rfl) ⟨34178, by rfl⟩) R68357
theorem R45587 : Reach 45587 := rs (se 1 (by rfl) ⟨34190, by rfl⟩) R68381
theorem R45603 : Reach 45603 := rs (se 1 (by rfl) ⟨34202, by rfl⟩) R68405
theorem R45619 : Reach 45619 := rs (se 1 (by rfl) ⟨34214, by rfl⟩) R68429
theorem R45635 : Reach 45635 := rs (se 1 (by rfl) ⟨34226, by rfl⟩) R68453
theorem R45651 : Reach 45651 := rs (se 1 (by rfl) ⟨34238, by rfl⟩) R68477
theorem R111203 : Reach 111203 := rs (se 1 (by rfl) ⟨83402, by rfl⟩) R166805
theorem R45667 : Reach 45667 := rs (se 1 (by rfl) ⟨34250, by rfl⟩) R68501
theorem R45683 : Reach 45683 := rs (se 1 (by rfl) ⟨34262, by rfl⟩) R68525
theorem R45699 : Reach 45699 := rs (se 1 (by rfl) ⟨34274, by rfl⟩) R68549
theorem R45715 : Reach 45715 := rs (se 1 (by rfl) ⟨34286, by rfl⟩) R68573
theorem R144035 : Reach 144035 := rs (se 1 (by rfl) ⟨108026, by rfl⟩) R216053
theorem R45731 : Reach 45731 := rs (se 1 (by rfl) ⟨34298, by rfl⟩) R68597
theorem R45747 : Reach 45747 := rs (se 1 (by rfl) ⟨34310, by rfl⟩) R68621
theorem R45763 : Reach 45763 := rs (se 1 (by rfl) ⟨34322, by rfl⟩) R68645
theorem R45779 : Reach 45779 := rs (se 1 (by rfl) ⟨34334, by rfl⟩) R68669
theorem R45795 : Reach 45795 := rs (se 1 (by rfl) ⟨34346, by rfl⟩) R68693
theorem R78563 : Reach 78563 := rs (se 1 (by rfl) ⟨58922, by rfl⟩) R117845
theorem R45811 : Reach 45811 := rs (se 1 (by rfl) ⟨34358, by rfl⟩) R68717
theorem R45827 : Reach 45827 := rs (se 1 (by rfl) ⟨34370, by rfl⟩) R68741
theorem R45843 : Reach 45843 := rs (se 1 (by rfl) ⟨34382, by rfl⟩) R68765
theorem R111395 : Reach 111395 := rs (se 1 (by rfl) ⟨83546, by rfl⟩) R167093
theorem R45859 : Reach 45859 := rs (se 1 (by rfl) ⟨34394, by rfl⟩) R68789
theorem R45875 : Reach 45875 := rs (se 1 (by rfl) ⟨34406, by rfl⟩) R68813
theorem R45891 : Reach 45891 := rs (se 1 (by rfl) ⟨34418, by rfl⟩) R68837
theorem R45907 : Reach 45907 := rs (se 1 (by rfl) ⟨34430, by rfl⟩) R68861
theorem R45923 : Reach 45923 := rs (se 1 (by rfl) ⟨34442, by rfl⟩) R68885
theorem R78691 : Reach 78691 := rs (se 1 (by rfl) ⟨59018, by rfl⟩) R118037
theorem R45939 : Reach 45939 := rs (se 1 (by rfl) ⟨34454, by rfl⟩) R68909
theorem R45955 : Reach 45955 := rs (se 1 (by rfl) ⟨34466, by rfl⟩) R68933
theorem R45971 : Reach 45971 := rs (se 1 (by rfl) ⟨34478, by rfl⟩) R68957
theorem R45987 : Reach 45987 := rs (se 1 (by rfl) ⟨34490, by rfl⟩) R68981
theorem R46003 : Reach 46003 := rs (se 1 (by rfl) ⟨34502, by rfl⟩) R69005
theorem R46019 : Reach 46019 := rs (se 1 (by rfl) ⟨34514, by rfl⟩) R69029
theorem R144337 : Reach 144337 := rs (se 2 (by rfl) ⟨54126, by rfl⟩) R108253
theorem R46035 : Reach 46035 := rs (se 1 (by rfl) ⟨34526, by rfl⟩) R69053
theorem R46051 : Reach 46051 := rs (se 1 (by rfl) ⟨34538, by rfl⟩) R69077
theorem R78833 : Reach 78833 := rs (se 2 (by rfl) ⟨29562, by rfl⟩) R59125
theorem R46067 : Reach 46067 := rs (se 1 (by rfl) ⟨34550, by rfl⟩) R69101
theorem R46083 : Reach 46083 := rs (se 1 (by rfl) ⟨34562, by rfl⟩) R69125
theorem R46099 : Reach 46099 := rs (se 1 (by rfl) ⟨34574, by rfl⟩) R69149
theorem R46115 : Reach 46115 := rs (se 1 (by rfl) ⟨34586, by rfl⟩) R69173
theorem R144433 : Reach 144433 := rs (se 2 (by rfl) ⟨54162, by rfl⟩) R108325
theorem R46131 : Reach 46131 := rs (se 1 (by rfl) ⟨34598, by rfl⟩) R69197
theorem R46147 : Reach 46147 := rs (se 1 (by rfl) ⟨34610, by rfl⟩) R69221
theorem R46163 : Reach 46163 := rs (se 1 (by rfl) ⟨34622, by rfl⟩) R69245
theorem R46179 : Reach 46179 := rs (se 1 (by rfl) ⟨34634, by rfl⟩) R69269
theorem R144497 : Reach 144497 := rs (se 2 (by rfl) ⟨54186, by rfl⟩) R108373
theorem R46195 : Reach 46195 := rs (se 1 (by rfl) ⟨34646, by rfl⟩) R69293
theorem R78961 : Reach 78961 := rs (se 2 (by rfl) ⟨29610, by rfl⟩) R59221
theorem R46211 : Reach 46211 := rs (se 1 (by rfl) ⟨34658, by rfl⟩) R69317
theorem R46227 : Reach 46227 := rs (se 1 (by rfl) ⟨34670, by rfl⟩) R69341
theorem R46243 : Reach 46243 := rs (se 1 (by rfl) ⟨34682, by rfl⟩) R69365
theorem R177329 : Reach 177329 := rs (se 2 (by rfl) ⟨66498, by rfl⟩) R132997
theorem R46259 : Reach 46259 := rs (se 1 (by rfl) ⟨34694, by rfl⟩) R69389
theorem R46275 : Reach 46275 := rs (se 1 (by rfl) ⟨34706, by rfl⟩) R69413
theorem R46291 : Reach 46291 := rs (se 1 (by rfl) ⟨34718, by rfl⟩) R69437
theorem R46307 : Reach 46307 := rs (se 1 (by rfl) ⟨34730, by rfl⟩) R69461
theorem R46323 : Reach 46323 := rs (se 1 (by rfl) ⟨34742, by rfl⟩) R69485
theorem R46339 : Reach 46339 := rs (se 1 (by rfl) ⟨34754, by rfl⟩) R69509
theorem R46355 : Reach 46355 := rs (se 1 (by rfl) ⟨34766, by rfl⟩) R69533
theorem R46371 : Reach 46371 := rs (se 1 (by rfl) ⟨34778, by rfl⟩) R69557
theorem R46387 : Reach 46387 := rs (se 1 (by rfl) ⟨34790, by rfl⟩) R69581
theorem R46403 : Reach 46403 := rs (se 1 (by rfl) ⟨34802, by rfl⟩) R69605
theorem R46419 : Reach 46419 := rs (se 1 (by rfl) ⟨34814, by rfl⟩) R69629
theorem R210275 : Reach 210275 := rs (se 1 (by rfl) ⟨157706, by rfl⟩) R315413
theorem R46435 : Reach 46435 := rs (se 1 (by rfl) ⟨34826, by rfl⟩) R69653
theorem R46451 : Reach 46451 := rs (se 1 (by rfl) ⟨34838, by rfl⟩) R69677
theorem R46467 : Reach 46467 := rs (se 1 (by rfl) ⟨34850, by rfl⟩) R69701
theorem R46483 : Reach 46483 := rs (se 1 (by rfl) ⟨34862, by rfl⟩) R69725
theorem R243107 : Reach 243107 := rs (se 1 (by rfl) ⟨182330, by rfl⟩) R364661
theorem R46499 : Reach 46499 := rs (se 1 (by rfl) ⟨34874, by rfl⟩) R69749
theorem R46515 : Reach 46515 := rs (se 1 (by rfl) ⟨34886, by rfl⟩) R69773
theorem R46531 : Reach 46531 := rs (se 1 (by rfl) ⟨34898, by rfl⟩) R69797
theorem R46547 : Reach 46547 := rs (se 1 (by rfl) ⟨34910, by rfl⟩) R69821
theorem R46563 : Reach 46563 := rs (se 1 (by rfl) ⟨34922, by rfl⟩) R69845
theorem R341489 : Reach 341489 := rs (se 2 (by rfl) ⟨128058, by rfl⟩) R256117
theorem R439793 : Reach 439793 := rs (se 2 (by rfl) ⟨164922, by rfl⟩) R329845
theorem R46579 : Reach 46579 := rs (se 1 (by rfl) ⟨34934, by rfl⟩) R69869
theorem R46595 : Reach 46595 := rs (se 1 (by rfl) ⟨34946, by rfl⟩) R69893
theorem R46611 : Reach 46611 := rs (se 1 (by rfl) ⟨34958, by rfl⟩) R69917
theorem R46627 : Reach 46627 := rs (se 1 (by rfl) ⟨34970, by rfl⟩) R69941
theorem R46643 : Reach 46643 := rs (se 1 (by rfl) ⟨34982, by rfl⟩) R69965
theorem R46659 : Reach 46659 := rs (se 1 (by rfl) ⟨34994, by rfl⟩) R69989
theorem R79427 : Reach 79427 := rs (se 1 (by rfl) ⟨59570, by rfl⟩) R119141
theorem R46675 : Reach 46675 := rs (se 1 (by rfl) ⟨35006, by rfl⟩) R70013
theorem R46691 : Reach 46691 := rs (se 1 (by rfl) ⟨35018, by rfl⟩) R70037
theorem R46707 : Reach 46707 := rs (se 1 (by rfl) ⟨35030, by rfl⟩) R70061
theorem R46723 : Reach 46723 := rs (se 1 (by rfl) ⟨35042, by rfl⟩) R70085
theorem R46739 : Reach 46739 := rs (se 1 (by rfl) ⟨35054, by rfl⟩) R70109
theorem R46755 : Reach 46755 := rs (se 1 (by rfl) ⟨35066, by rfl⟩) R70133
theorem R46771 : Reach 46771 := rs (se 1 (by rfl) ⟨35078, by rfl⟩) R70157
theorem R46787 : Reach 46787 := rs (se 1 (by rfl) ⟨35090, by rfl⟩) R70181
theorem R308933 : Reach 308933 := rs (se 4 (by rfl) ⟨28962, by rfl⟩) R57925
theorem R112337 : Reach 112337 := rs (se 2 (by rfl) ⟨42126, by rfl⟩) R84253
theorem R46803 : Reach 46803 := rs (se 1 (by rfl) ⟨35102, by rfl⟩) R70205
theorem R46819 : Reach 46819 := rs (se 1 (by rfl) ⟨35114, by rfl⟩) R70229
theorem R46835 : Reach 46835 := rs (se 1 (by rfl) ⟨35126, by rfl⟩) R70253
theorem R112387 : Reach 112387 := rs (se 1 (by rfl) ⟨84290, by rfl⟩) R168581
theorem R46851 : Reach 46851 := rs (se 1 (by rfl) ⟨35138, by rfl⟩) R70277
theorem R46867 : Reach 46867 := rs (se 1 (by rfl) ⟨35150, by rfl⟩) R70301
theorem R79651 : Reach 79651 := rs (se 1 (by rfl) ⟨59738, by rfl⟩) R119477
theorem R46883 : Reach 46883 := rs (se 1 (by rfl) ⟨35162, by rfl⟩) R70325
theorem R46899 : Reach 46899 := rs (se 1 (by rfl) ⟨35174, by rfl⟩) R70349
theorem R46915 : Reach 46915 := rs (se 1 (by rfl) ⟨35186, by rfl⟩) R70373
theorem R177997 : Reach 177997 := rs (se 3 (by rfl) ⟨33374, by rfl⟩) R66749
theorem R46931 : Reach 46931 := rs (se 1 (by rfl) ⟨35198, by rfl⟩) R70397
theorem R46947 : Reach 46947 := rs (se 1 (by rfl) ⟨35210, by rfl⟩) R70421
theorem R46963 : Reach 46963 := rs (se 1 (by rfl) ⟨35222, by rfl⟩) R70445
theorem R46979 : Reach 46979 := rs (se 1 (by rfl) ⟨35234, by rfl⟩) R70469
theorem R112529 : Reach 112529 := rs (se 2 (by rfl) ⟨42198, by rfl⟩) R84397
theorem R46995 : Reach 46995 := rs (se 1 (by rfl) ⟨35246, by rfl⟩) R70493
theorem R47011 : Reach 47011 := rs (se 1 (by rfl) ⟨35258, by rfl⟩) R70517
theorem R47027 : Reach 47027 := rs (se 1 (by rfl) ⟨35270, by rfl⟩) R70541
theorem R47043 : Reach 47043 := rs (se 1 (by rfl) ⟨35282, by rfl⟩) R70565
theorem R47059 : Reach 47059 := rs (se 1 (by rfl) ⟨35294, by rfl⟩) R70589
theorem R47075 : Reach 47075 := rs (se 1 (by rfl) ⟨35306, by rfl⟩) R70613
theorem R47091 : Reach 47091 := rs (se 1 (by rfl) ⟨35318, by rfl⟩) R70637
theorem R47107 : Reach 47107 := rs (se 1 (by rfl) ⟨35330, by rfl⟩) R70661
theorem R505925 : Reach 505925 := rs (se 4 (by rfl) ⟨47430, by rfl⟩) R94861
theorem R145745 : Reach 145745 := rs (se 2 (by rfl) ⟨54654, by rfl⟩) R109309
theorem R178531 : Reach 178531 := rs (se 1 (by rfl) ⟨133898, by rfl⟩) R267797
theorem R113105 : Reach 113105 := rs (se 2 (by rfl) ⟨42414, by rfl⟩) R84829
theorem R178787 : Reach 178787 := rs (se 1 (by rfl) ⟨134090, by rfl⟩) R268181
theorem R47747 : Reach 47747 := rs (se 1 (by rfl) ⟨35810, by rfl⟩) R71621
theorem R47875 : Reach 47875 := rs (se 1 (by rfl) ⟨35906, by rfl⟩) R71813
theorem R211747 : Reach 211747 := rs (se 1 (by rfl) ⟨158810, by rfl⟩) R317621
theorem R80689 : Reach 80689 := rs (se 2 (by rfl) ⟨30258, by rfl⟩) R60517
theorem R146285 : Reach 146285 := rs (se 3 (by rfl) ⟨27428, by rfl⟩) R54857
theorem R113521 : Reach 113521 := rs (se 2 (by rfl) ⟨42570, by rfl⟩) R85141
theorem R146339 : Reach 146339 := rs (se 1 (by rfl) ⟨109754, by rfl⟩) R219509
theorem R113795 : Reach 113795 := rs (se 1 (by rfl) ⟨85346, by rfl⟩) R170693
theorem R277667 : Reach 277667 := rs (se 1 (by rfl) ⟨208250, by rfl⟩) R416501
theorem R146609 : Reach 146609 := rs (se 2 (by rfl) ⟨54978, by rfl⟩) R109957
theorem R113987 : Reach 113987 := rs (se 1 (by rfl) ⟨85490, by rfl⟩) R170981
theorem R81251 : Reach 81251 := rs (se 1 (by rfl) ⟨60938, by rfl⟩) R121877
theorem R48595 : Reach 48595 := rs (se 1 (by rfl) ⟨36446, by rfl⟩) R72893
theorem R48691 : Reach 48691 := rs (se 1 (by rfl) ⟨36518, by rfl⟩) R73037
theorem R48739 : Reach 48739 := rs (se 1 (by rfl) ⟨36554, by rfl⟩) R73109
theorem R114353 : Reach 114353 := rs (se 2 (by rfl) ⟨42882, by rfl⟩) R85765
theorem R147149 : Reach 147149 := rs (se 3 (by rfl) ⟨27590, by rfl⟩) R55181
theorem R48883 : Reach 48883 := rs (se 1 (by rfl) ⟨36662, by rfl⟩) R73325
theorem R147203 : Reach 147203 := rs (se 1 (by rfl) ⟨110402, by rfl⟩) R220805
theorem R606005 : Reach 606005 := rs (se 5 (by rfl) ⟨28406, by rfl⟩) R56813
theorem R49027 : Reach 49027 := rs (se 1 (by rfl) ⟨36770, by rfl⟩) R73541
theorem R442253 : Reach 442253 := rs (se 3 (by rfl) ⟨82922, by rfl⟩) R165845
theorem R147473 : Reach 147473 := rs (se 2 (by rfl) ⟨55302, by rfl⟩) R110605
theorem R49171 : Reach 49171 := rs (se 1 (by rfl) ⟨36878, by rfl⟩) R73757
theorem R49315 : Reach 49315 := rs (se 1 (by rfl) ⟨36986, by rfl⟩) R73973
theorem R82115 : Reach 82115 := rs (se 1 (by rfl) ⟨61586, by rfl⟩) R123173
theorem R114929 : Reach 114929 := rs (se 2 (by rfl) ⟨43098, by rfl⟩) R86197
theorem R114979 : Reach 114979 := rs (se 1 (by rfl) ⟨86234, by rfl⟩) R172469
theorem R82225 : Reach 82225 := rs (se 2 (by rfl) ⟨30834, by rfl⟩) R61669
theorem R49459 : Reach 49459 := rs (se 1 (by rfl) ⟨37094, by rfl⟩) R74189
theorem R115021 : Reach 115021 := rs (se 3 (by rfl) ⟨21566, by rfl⟩) R43133
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R115121 : Reach 115121 := rs (se 2 (by rfl) ⟨43170, by rfl⟩) R86341
theorem R49603 : Reach 49603 := rs (se 1 (by rfl) ⟨37202, by rfl⟩) R74405
theorem R148013 : Reach 148013 := rs (se 3 (by rfl) ⟨27752, by rfl⟩) R55505
theorem R49747 : Reach 49747 := rs (se 1 (by rfl) ⟨37310, by rfl⟩) R74621
theorem R148067 : Reach 148067 := rs (se 1 (by rfl) ⟨111050, by rfl⟩) R222101
theorem R279139 : Reach 279139 := rs (se 1 (by rfl) ⟨209354, by rfl⟩) R418709
theorem R49891 : Reach 49891 := rs (se 1 (by rfl) ⟨37418, by rfl⟩) R74837
theorem R246563 : Reach 246563 := rs (se 1 (by rfl) ⟨184922, by rfl⟩) R369845
theorem R836405 : Reach 836405 := rs (se 5 (by rfl) ⟨39206, by rfl⟩) R78413
theorem R148337 : Reach 148337 := rs (se 2 (by rfl) ⟨55626, by rfl⟩) R111253
theorem R50035 : Reach 50035 := rs (se 1 (by rfl) ⟨37526, by rfl⟩) R75053
theorem R639971 : Reach 639971 := rs (se 1 (by rfl) ⟨479978, by rfl⟩) R959957
theorem R345059 : Reach 345059 := rs (se 1 (by rfl) ⟨258794, by rfl⟩) R517589
theorem R50179 : Reach 50179 := rs (se 1 (by rfl) ⟨37634, by rfl⟩) R75269
theorem R148483 : Reach 148483 := rs (se 1 (by rfl) ⟨111362, by rfl⟩) R222725
theorem R115789 : Reach 115789 := rs (se 3 (by rfl) ⟨21710, by rfl⟩) R43421
theorem R83089 : Reach 83089 := rs (se 2 (by rfl) ⟨31158, by rfl⟩) R62317
theorem R50323 : Reach 50323 := rs (se 1 (by rfl) ⟨37742, by rfl⟩) R75485
theorem R148675 : Reach 148675 := rs (se 1 (by rfl) ⟨111506, by rfl⟩) R223013
theorem R181453 : Reach 181453 := rs (se 3 (by rfl) ⟨34022, by rfl⟩) R68045
theorem R214285 : Reach 214285 := rs (se 3 (by rfl) ⟨40178, by rfl⟩) R80357
theorem R50467 : Reach 50467 := rs (se 1 (by rfl) ⟨37850, by rfl⟩) R75701
theorem R83281 : Reach 83281 := rs (se 2 (by rfl) ⟨31230, by rfl⟩) R62461
theorem R148877 : Reach 148877 := rs (se 3 (by rfl) ⟨27914, by rfl⟩) R55829
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) R68117
theorem R116113 : Reach 116113 := rs (se 2 (by rfl) ⟨43542, by rfl⟩) R87085
theorem R50611 : Reach 50611 := rs (se 1 (by rfl) ⟨37958, by rfl⟩) R75917
theorem R148931 : Reach 148931 := rs (se 1 (by rfl) ⟨111698, by rfl⟩) R223397
theorem R476725 : Reach 476725 := rs (se 5 (by rfl) ⟨22346, by rfl⟩) R44693
theorem R50755 : Reach 50755 := rs (se 1 (by rfl) ⟨38066, by rfl⟩) R76133
theorem R83587 : Reach 83587 := rs (se 1 (by rfl) ⟨62690, by rfl⟩) R125381
theorem R116387 : Reach 116387 := rs (se 1 (by rfl) ⟨87290, by rfl⟩) R174581
theorem R149201 : Reach 149201 := rs (se 2 (by rfl) ⟨55950, by rfl⟩) R111901
theorem R50899 : Reach 50899 := rs (se 1 (by rfl) ⟨38174, by rfl⟩) R76349
theorem R83683 : Reach 83683 := rs (se 1 (by rfl) ⟨62762, by rfl⟩) R125525
theorem R83729 : Reach 83729 := rs (se 2 (by rfl) ⟨31398, by rfl⟩) R62797
theorem R51043 : Reach 51043 := rs (se 1 (by rfl) ⟨38282, by rfl⟩) R76565
theorem R116579 : Reach 116579 := rs (se 1 (by rfl) ⟨87434, by rfl⟩) R174869
theorem R51187 : Reach 51187 := rs (se 1 (by rfl) ⟨38390, by rfl⟩) R76781
theorem R84017 : Reach 84017 := rs (se 2 (by rfl) ⟨31506, by rfl⟩) R63013
theorem R51331 : Reach 51331 := rs (se 1 (by rfl) ⟨38498, by rfl⟩) R76997
theorem R149681 : Reach 149681 := rs (se 2 (by rfl) ⟨56130, by rfl⟩) R112261
theorem R215245 : Reach 215245 := rs (se 3 (by rfl) ⟨40358, by rfl⟩) R80717
theorem R149741 : Reach 149741 := rs (se 3 (by rfl) ⟨28076, by rfl⟩) R56153
theorem R280817 : Reach 280817 := rs (se 2 (by rfl) ⟨105306, by rfl⟩) R210613
theorem R51475 : Reach 51475 := rs (se 1 (by rfl) ⟨38606, by rfl⟩) R77213
theorem R149795 : Reach 149795 := rs (se 1 (by rfl) ⟨112346, by rfl⟩) R224693
theorem R248141 : Reach 248141 := rs (se 3 (by rfl) ⟨46526, by rfl⟩) R93053
theorem R51619 : Reach 51619 := rs (se 1 (by rfl) ⟨38714, by rfl⟩) R77429
theorem R117197 : Reach 117197 := rs (se 3 (by rfl) ⟨21974, by rfl⟩) R43949
theorem R150065 : Reach 150065 := rs (se 2 (by rfl) ⟨56274, by rfl⟩) R112549
theorem R51763 : Reach 51763 := rs (se 1 (by rfl) ⟨38822, by rfl⟩) R77645
theorem R248453 : Reach 248453 := rs (se 4 (by rfl) ⟨23292, by rfl⟩) R46585
theorem R117389 : Reach 117389 := rs (se 3 (by rfl) ⟨22010, by rfl⟩) R44021
theorem R215729 : Reach 215729 := rs (se 2 (by rfl) ⟨80898, by rfl⟩) R161797
theorem R51907 : Reach 51907 := rs (se 1 (by rfl) ⟨38930, by rfl⟩) R77861
theorem R84739 : Reach 84739 := rs (se 1 (by rfl) ⟨63554, by rfl⟩) R127109
theorem R117521 : Reach 117521 := rs (se 2 (by rfl) ⟨44070, by rfl⟩) R88141
theorem R117571 : Reach 117571 := rs (se 1 (by rfl) ⟨88178, by rfl⟩) R176357
theorem R52051 : Reach 52051 := rs (se 1 (by rfl) ⟨39038, by rfl⟩) R78077
theorem R117713 : Reach 117713 := rs (se 2 (by rfl) ⟨44142, by rfl⟩) R88285
theorem R52195 : Reach 52195 := rs (se 1 (by rfl) ⟨39146, by rfl⟩) R78293
theorem R150605 : Reach 150605 := rs (se 3 (by rfl) ⟨28238, by rfl⟩) R56477
theorem R281713 : Reach 281713 := rs (se 2 (by rfl) ⟨105642, by rfl⟩) R211285
theorem R52339 : Reach 52339 := rs (se 1 (by rfl) ⟨39254, by rfl⟩) R78509
theorem R150659 : Reach 150659 := rs (se 1 (by rfl) ⟨112994, by rfl⟩) R225989
theorem R85187 : Reach 85187 := rs (se 1 (by rfl) ⟨63890, by rfl⟩) R127781
theorem R52483 : Reach 52483 := rs (se 1 (by rfl) ⟨39362, by rfl⟩) R78725
theorem R118061 : Reach 118061 := rs (se 3 (by rfl) ⟨22136, by rfl⟩) R44273
theorem R118093 : Reach 118093 := rs (se 3 (by rfl) ⟨22142, by rfl⟩) R44285
theorem R150893 : Reach 150893 := rs (se 3 (by rfl) ⟨28292, by rfl⟩) R56585
theorem R150929 : Reach 150929 := rs (se 2 (by rfl) ⟨56598, by rfl⟩) R113197
theorem R52627 : Reach 52627 := rs (se 1 (by rfl) ⟨39470, by rfl⟩) R78941
theorem R85475 : Reach 85475 := rs (se 1 (by rfl) ⟨64106, by rfl⟩) R128213
theorem R52771 : Reach 52771 := rs (se 1 (by rfl) ⟨39578, by rfl⟩) R79157
theorem R118381 : Reach 118381 := rs (se 3 (by rfl) ⟨22196, by rfl⟩) R44393
theorem R118417 : Reach 118417 := rs (se 2 (by rfl) ⟨44406, by rfl⟩) R88813
theorem R52915 : Reach 52915 := rs (se 1 (by rfl) ⟨39686, by rfl⟩) R79373
theorem R1199843 : Reach 1199843 := rs (se 1 (by rfl) ⟨899882, by rfl⟩) R1799765
theorem R511757 : Reach 511757 := rs (se 3 (by rfl) ⟨95954, by rfl⟩) R191909
theorem R151469 : Reach 151469 := rs (se 3 (by rfl) ⟨28400, by rfl⟩) R56801
theorem R118705 : Reach 118705 := rs (se 2 (by rfl) ⟨44514, by rfl⟩) R89029
theorem R151523 : Reach 151523 := rs (se 1 (by rfl) ⟨113642, by rfl⟩) R227285
theorem R774197 : Reach 774197 := rs (se 5 (by rfl) ⟨36290, by rfl⟩) R72581
theorem R315505 : Reach 315505 := rs (se 2 (by rfl) ⟨118314, by rfl⟩) R236629
theorem R118979 : Reach 118979 := rs (se 1 (by rfl) ⟨89234, by rfl⟩) R178469
theorem R151793 : Reach 151793 := rs (se 2 (by rfl) ⟨56922, by rfl⟩) R113845
theorem R119171 : Reach 119171 := rs (se 1 (by rfl) ⟨89378, by rfl⟩) R178757
theorem R86417 : Reach 86417 := rs (se 2 (by rfl) ⟨32406, by rfl⟩) R64813
theorem R152333 : Reach 152333 := rs (se 3 (by rfl) ⟨28562, by rfl⟩) R57125
theorem R152387 : Reach 152387 := rs (se 1 (by rfl) ⟨114290, by rfl⟩) R228581
theorem R119875 : Reach 119875 := rs (se 1 (by rfl) ⟨89906, by rfl⟩) R179813
theorem R152657 : Reach 152657 := rs (se 2 (by rfl) ⟨57246, by rfl⟩) R114493
theorem R185485 : Reach 185485 := rs (se 3 (by rfl) ⟨34778, by rfl⟩) R69557
theorem R87313 : Reach 87313 := rs (se 2 (by rfl) ⟨32742, by rfl⟩) R65485
theorem R87473 : Reach 87473 := rs (se 2 (by rfl) ⟨32802, by rfl⟩) R65605
theorem R185827 : Reach 185827 := rs (se 1 (by rfl) ⟨139370, by rfl⟩) R278741
theorem R251363 : Reach 251363 := rs (se 1 (by rfl) ⟨188522, by rfl⟩) R377045
theorem R153197 : Reach 153197 := rs (se 3 (by rfl) ⟨28724, by rfl⟩) R57449
theorem R153251 : Reach 153251 := rs (se 1 (by rfl) ⟨114938, by rfl⟩) R229877
theorem R55075 : Reach 55075 := rs (se 1 (by rfl) ⟨41306, by rfl⟩) R82613
theorem R87875 : Reach 87875 := rs (se 1 (by rfl) ⟨65906, by rfl⟩) R131813
theorem R55171 : Reach 55171 := rs (se 1 (by rfl) ⟨41378, by rfl⟩) R82757
theorem R153521 : Reach 153521 := rs (se 2 (by rfl) ⟨57570, by rfl⟩) R115141
theorem R186317 : Reach 186317 := rs (se 3 (by rfl) ⟨34934, by rfl⟩) R69869
theorem R120781 : Reach 120781 := rs (se 3 (by rfl) ⟨22646, by rfl⟩) R45293
theorem R219185 : Reach 219185 := rs (se 2 (by rfl) ⟨82194, by rfl⟩) R164389
theorem R350405 : Reach 350405 := rs (se 4 (by rfl) ⟨32850, by rfl⟩) R65701
theorem R252173 : Reach 252173 := rs (se 3 (by rfl) ⟨47282, by rfl⟩) R94565
theorem R55667 : Reach 55667 := rs (se 1 (by rfl) ⟨41750, by rfl⟩) R83501
theorem R154061 : Reach 154061 := rs (se 3 (by rfl) ⟨28886, by rfl⟩) R57773
theorem R514673 : Reach 514673 := rs (se 2 (by rfl) ⟨193002, by rfl⟩) R386005
theorem R88771 : Reach 88771 := rs (se 1 (by rfl) ⟨66578, by rfl⟩) R133157
theorem R56099 : Reach 56099 := rs (se 1 (by rfl) ⟨42074, by rfl⟩) R84149
theorem R88931 : Reach 88931 := rs (se 1 (by rfl) ⟨66698, by rfl⟩) R133397
theorem R56371 : Reach 56371 := rs (se 1 (by rfl) ⟨42278, by rfl⟩) R84557
theorem R56435 : Reach 56435 := rs (se 1 (by rfl) ⟨42326, by rfl⟩) R84653
theorem R56467 : Reach 56467 := rs (se 1 (by rfl) ⟨42350, by rfl⟩) R84701
theorem R154979 : Reach 154979 := rs (se 1 (by rfl) ⟨116234, by rfl⟩) R232469
theorem R220643 : Reach 220643 := rs (se 1 (by rfl) ⟨165482, by rfl⟩) R330965
theorem R155249 : Reach 155249 := rs (se 2 (by rfl) ⟨58218, by rfl⟩) R116437
theorem R56963 : Reach 56963 := rs (se 1 (by rfl) ⟨42722, by rfl⟩) R85445
theorem R417649 : Reach 417649 := rs (se 2 (by rfl) ⟨156618, by rfl⟩) R313237
theorem R253829 : Reach 253829 := rs (se 4 (by rfl) ⟨23796, by rfl⟩) R47593
theorem R155789 : Reach 155789 := rs (se 3 (by rfl) ⟨29210, by rfl⟩) R58421
theorem R57505 : Reach 57505 := rs (se 2 (by rfl) ⟨21564, by rfl⟩) R43129
theorem R57601 : Reach 57601 := rs (se 2 (by rfl) ⟨21600, by rfl⟩) R43201
theorem R221453 : Reach 221453 := rs (se 3 (by rfl) ⟨41522, by rfl⟩) R83045
theorem R57667 : Reach 57667 := rs (se 1 (by rfl) ⟨43250, by rfl⟩) R86501
theorem R254285 : Reach 254285 := rs (se 3 (by rfl) ⟨47678, by rfl⟩) R95357
theorem R483725 : Reach 483725 := rs (se 3 (by rfl) ⟨90698, by rfl⟩) R181397
theorem R57763 : Reach 57763 := rs (se 1 (by rfl) ⟨43322, by rfl⟩) R86645
theorem R58097 : Reach 58097 := rs (se 2 (by rfl) ⟨21786, by rfl⟩) R43573
theorem R58259 : Reach 58259 := rs (se 1 (by rfl) ⟨43694, by rfl⟩) R87389
theorem R156707 : Reach 156707 := rs (se 1 (by rfl) ⟨117530, by rfl⟩) R235061
theorem R58451 : Reach 58451 := rs (se 1 (by rfl) ⟨43838, by rfl⟩) R87677
theorem R124067 : Reach 124067 := rs (se 1 (by rfl) ⟨93050, by rfl⟩) R186101
theorem R156977 : Reach 156977 := rs (se 2 (by rfl) ⟨58866, by rfl⟩) R117733
theorem R189859 : Reach 189859 := rs (se 1 (by rfl) ⟨142394, by rfl⟩) R284789
theorem R58801 : Reach 58801 := rs (se 2 (by rfl) ⟨22050, by rfl⟩) R44101
theorem R583109 : Reach 583109 := rs (se 4 (by rfl) ⟨54666, by rfl⟩) R109333
theorem R58897 : Reach 58897 := rs (se 2 (by rfl) ⟨22086, by rfl⟩) R44173
theorem R58963 : Reach 58963 := rs (se 1 (by rfl) ⟨44222, by rfl⟩) R88445
theorem R59059 : Reach 59059 := rs (se 1 (by rfl) ⟨44294, by rfl⟩) R88589
theorem R59203 : Reach 59203 := rs (se 1 (by rfl) ⟨44402, by rfl⟩) R88805
theorem R157517 : Reach 157517 := rs (se 3 (by rfl) ⟨29534, by rfl⟩) R59069
theorem R59393 : Reach 59393 := rs (se 2 (by rfl) ⟨22272, by rfl⟩) R44545
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) R46901
theorem R59555 : Reach 59555 := rs (se 1 (by rfl) ⟨44666, by rfl⟩) R89333
theorem R125165 : Reach 125165 := rs (se 3 (by rfl) ⟨23468, by rfl⟩) R46937
theorem R387341 : Reach 387341 := rs (se 3 (by rfl) ⟨72626, by rfl⟩) R145253
theorem R125297 : Reach 125297 := rs (se 2 (by rfl) ⟨46986, by rfl⟩) R93973
theorem R59825 : Reach 59825 := rs (se 2 (by rfl) ⟨22434, by rfl⟩) R44869
theorem R256517 : Reach 256517 := rs (se 4 (by rfl) ⟨24048, by rfl⟩) R48097
theorem R256547 : Reach 256547 := rs (se 1 (by rfl) ⟨192410, by rfl⟩) R384821
theorem R191089 : Reach 191089 := rs (se 2 (by rfl) ⟨71658, by rfl⟩) R143317
theorem R191203 : Reach 191203 := rs (se 1 (by rfl) ⟨143402, by rfl⟩) R286805
theorem R158435 : Reach 158435 := rs (se 1 (by rfl) ⟨118826, by rfl⟩) R237653
theorem R223985 : Reach 223985 := rs (se 2 (by rfl) ⟨83994, by rfl⟩) R167989
theorem R92963 : Reach 92963 := rs (se 1 (by rfl) ⟨69722, by rfl⟩) R139445
theorem R60355 : Reach 60355 := rs (se 1 (by rfl) ⟨45266, by rfl⟩) R90533
theorem R289763 : Reach 289763 := rs (se 1 (by rfl) ⟨217322, by rfl⟩) R434645
theorem R158705 : Reach 158705 := rs (se 2 (by rfl) ⟨59514, by rfl⟩) R119029
theorem R93187 : Reach 93187 := rs (se 1 (by rfl) ⟨69890, by rfl⟩) R139781
theorem R60419 : Reach 60419 := rs (se 1 (by rfl) ⟨45314, by rfl⟩) R90629
theorem R158797 : Reach 158797 := rs (se 3 (by rfl) ⟨29774, by rfl⟩) R59549
theorem R126029 : Reach 126029 := rs (se 3 (by rfl) ⟨23630, by rfl⟩) R47261
theorem R224369 : Reach 224369 := rs (se 2 (by rfl) ⟨84138, by rfl⟩) R168277
theorem R257201 : Reach 257201 := rs (se 2 (by rfl) ⟨96450, by rfl⟩) R192901
theorem R126353 : Reach 126353 := rs (se 2 (by rfl) ⟨47382, by rfl⟩) R94765
theorem R93649 : Reach 93649 := rs (se 2 (by rfl) ⟨35118, by rfl⟩) R70237
theorem R126755 : Reach 126755 := rs (se 1 (by rfl) ⟨95066, by rfl⟩) R190133
theorem R61219 : Reach 61219 := rs (se 1 (by rfl) ⟨45914, by rfl⟩) R91829
theorem R356237 : Reach 356237 := rs (se 3 (by rfl) ⟨66794, by rfl⟩) R133589
theorem R61457 : Reach 61457 := rs (se 2 (by rfl) ⟨23046, by rfl⟩) R46093
theorem R61555 : Reach 61555 := rs (se 1 (by rfl) ⟨46166, by rfl⟩) R92333
theorem R94691 : Reach 94691 := rs (se 1 (by rfl) ⟨71018, by rfl⟩) R142037
theorem R225827 : Reach 225827 := rs (se 1 (by rfl) ⟨169370, by rfl⟩) R338741
theorem R127555 : Reach 127555 := rs (se 1 (by rfl) ⟨95666, by rfl⟩) R191333
theorem R127565 : Reach 127565 := rs (se 3 (by rfl) ⟨23918, by rfl⟩) R47837
theorem R258659 : Reach 258659 := rs (se 1 (by rfl) ⟨193994, by rfl⟩) R387989
theorem R160483 : Reach 160483 := rs (se 1 (by rfl) ⟨120362, by rfl⟩) R240725
theorem R127757 : Reach 127757 := rs (se 3 (by rfl) ⟨23954, by rfl⟩) R47909
theorem R127793 : Reach 127793 := rs (se 2 (by rfl) ⟨47922, by rfl⟩) R95845
theorem R127921 : Reach 127921 := rs (se 2 (by rfl) ⟨47970, by rfl⟩) R95941
theorem R291761 : Reach 291761 := rs (se 2 (by rfl) ⟨109410, by rfl⟩) R218821
theorem R95203 : Reach 95203 := rs (se 1 (by rfl) ⟨71402, by rfl⟩) R142805
theorem R128099 : Reach 128099 := rs (se 1 (by rfl) ⟨96074, by rfl⟩) R192149
theorem R62689 : Reach 62689 := rs (se 2 (by rfl) ⟨23508, by rfl⟩) R47017
theorem R62785 : Reach 62785 := rs (se 2 (by rfl) ⟨23544, by rfl⟩) R47089
theorem R226637 : Reach 226637 := rs (se 3 (by rfl) ⟨42494, by rfl⟩) R84989
theorem R95921 : Reach 95921 := rs (se 2 (by rfl) ⟨35970, by rfl⟩) R71941
theorem R128749 : Reach 128749 := rs (se 3 (by rfl) ⟨24140, by rfl⟩) R48281
theorem R63281 : Reach 63281 := rs (se 2 (by rfl) ⟨23730, by rfl⟩) R47461
theorem R587573 : Reach 587573 := rs (se 5 (by rfl) ⟨27542, by rfl⟩) R55085
theorem R96433 : Reach 96433 := rs (se 2 (by rfl) ⟨36162, by rfl⟩) R72325
theorem R96707 : Reach 96707 := rs (se 1 (by rfl) ⟨72530, by rfl⟩) R145061
theorem R293453 : Reach 293453 := rs (se 3 (by rfl) ⟨55022, by rfl⟩) R110045
theorem R64147 : Reach 64147 := rs (se 1 (by rfl) ⟨48110, by rfl⟩) R96221
theorem R64243 : Reach 64243 := rs (se 1 (by rfl) ⟨48182, by rfl⟩) R96365
theorem R97073 : Reach 97073 := rs (se 2 (by rfl) ⟨36402, by rfl⟩) R72805
theorem R97091 : Reach 97091 := rs (se 1 (by rfl) ⟨72818, by rfl⟩) R145637
theorem R195533 : Reach 195533 := rs (se 3 (by rfl) ⟨36662, by rfl⟩) R73325
theorem R97361 : Reach 97361 := rs (se 2 (by rfl) ⟨36510, by rfl⟩) R73021
theorem R97379 : Reach 97379 := rs (se 1 (by rfl) ⟨73034, by rfl⟩) R146069
theorem R64691 : Reach 64691 := rs (se 1 (by rfl) ⟨48518, by rfl⟩) R97037
theorem R64721 : Reach 64721 := rs (se 2 (by rfl) ⟨24270, by rfl⟩) R48541
theorem R64739 : Reach 64739 := rs (se 1 (by rfl) ⟨48554, by rfl⟩) R97109
theorem R64769 : Reach 64769 := rs (se 2 (by rfl) ⟨24288, by rfl⟩) R48577
theorem R64787 : Reach 64787 := rs (se 1 (by rfl) ⟨48590, by rfl⟩) R97181
theorem R64817 : Reach 64817 := rs (se 2 (by rfl) ⟨24306, by rfl⟩) R48613
theorem R64835 : Reach 64835 := rs (se 1 (by rfl) ⟨48626, by rfl⟩) R97253
theorem R64865 : Reach 64865 := rs (se 2 (by rfl) ⟨24324, by rfl⟩) R48649
theorem R97649 : Reach 97649 := rs (se 2 (by rfl) ⟨36618, by rfl⟩) R73237
theorem R64883 : Reach 64883 := rs (se 1 (by rfl) ⟨48662, by rfl⟩) R97325
theorem R97667 : Reach 97667 := rs (se 1 (by rfl) ⟨73250, by rfl⟩) R146501
theorem R64913 : Reach 64913 := rs (se 2 (by rfl) ⟨24342, by rfl⟩) R48685
theorem R97681 : Reach 97681 := rs (se 2 (by rfl) ⟨36630, by rfl⟩) R73261
theorem R64931 : Reach 64931 := rs (se 1 (by rfl) ⟨48698, by rfl⟩) R97397
theorem R130481 : Reach 130481 := rs (se 2 (by rfl) ⟨48930, by rfl⟩) R97861
theorem R64961 : Reach 64961 := rs (se 2 (by rfl) ⟨24360, by rfl⟩) R48721
theorem R64979 : Reach 64979 := rs (se 1 (by rfl) ⟨48734, by rfl⟩) R97469
theorem R65009 : Reach 65009 := rs (se 2 (by rfl) ⟨24378, by rfl⟩) R48757
theorem R65027 : Reach 65027 := rs (se 1 (by rfl) ⟨48770, by rfl⟩) R97541
theorem R65057 : Reach 65057 := rs (se 2 (by rfl) ⟨24396, by rfl⟩) R48793
theorem R65075 : Reach 65075 := rs (se 1 (by rfl) ⟨48806, by rfl⟩) R97613
theorem R65105 : Reach 65105 := rs (se 2 (by rfl) ⟨24414, by rfl⟩) R48829
theorem R65123 : Reach 65123 := rs (se 1 (by rfl) ⟨48842, by rfl⟩) R97685
theorem R130673 : Reach 130673 := rs (se 2 (by rfl) ⟨49002, by rfl⟩) R98005
theorem R65153 : Reach 65153 := rs (se 2 (by rfl) ⟨24432, by rfl⟩) R48865
theorem R97937 : Reach 97937 := rs (se 2 (by rfl) ⟨36726, by rfl⟩) R73453
theorem R65171 : Reach 65171 := rs (se 1 (by rfl) ⟨48878, by rfl⟩) R97757
theorem R97955 : Reach 97955 := rs (se 1 (by rfl) ⟨73466, by rfl⟩) R146933
theorem R65201 : Reach 65201 := rs (se 2 (by rfl) ⟨24450, by rfl⟩) R48901
theorem R65219 : Reach 65219 := rs (se 1 (by rfl) ⟨48914, by rfl⟩) R97829
theorem R65249 : Reach 65249 := rs (se 2 (by rfl) ⟨24468, by rfl⟩) R48937
theorem R65267 : Reach 65267 := rs (se 1 (by rfl) ⟨48950, by rfl⟩) R97901
theorem R261893 : Reach 261893 := rs (se 4 (by rfl) ⟨24552, by rfl⟩) R49105
theorem R65297 : Reach 65297 := rs (se 2 (by rfl) ⟨24486, by rfl⟩) R48973
theorem R65315 : Reach 65315 := rs (se 1 (by rfl) ⟨48986, by rfl⟩) R97973
theorem R65345 : Reach 65345 := rs (se 2 (by rfl) ⟨24504, by rfl⟩) R49009
theorem R65363 : Reach 65363 := rs (se 1 (by rfl) ⟨49022, by rfl⟩) R98045
theorem R65377 : Reach 65377 := rs (se 2 (by rfl) ⟨24516, by rfl⟩) R49033
theorem R65393 : Reach 65393 := rs (se 2 (by rfl) ⟨24522, by rfl⟩) R49045
theorem R65411 : Reach 65411 := rs (se 1 (by rfl) ⟨49058, by rfl⟩) R98117
theorem R65441 : Reach 65441 := rs (se 2 (by rfl) ⟨24540, by rfl⟩) R49081
theorem R98225 : Reach 98225 := rs (se 2 (by rfl) ⟨36834, by rfl⟩) R73669
theorem R65459 : Reach 65459 := rs (se 1 (by rfl) ⟨49094, by rfl⟩) R98189
theorem R98243 : Reach 98243 := rs (se 1 (by rfl) ⟨73682, by rfl⟩) R147365
theorem R65489 : Reach 65489 := rs (se 2 (by rfl) ⟨24558, by rfl⟩) R49117
theorem R65507 : Reach 65507 := rs (se 1 (by rfl) ⟨49130, by rfl⟩) R98261
theorem R98315 : Reach 98315 := rs (se 1 (by rfl) ⟨73736, by rfl⟩) R147473
theorem R65561 : Reach 65561 := rs (se 2 (by rfl) ⟨24585, by rfl⟩) R49171
theorem R163885 : Reach 163885 := rs (se 3 (by rfl) ⟨30728, by rfl⟩) R61457
theorem R98369 : Reach 98369 := rs (se 2 (by rfl) ⟨36888, by rfl⟩) R73777
theorem R65675 : Reach 65675 := rs (se 1 (by rfl) ⟨49256, by rfl⟩) R98513
theorem R65687 : Reach 65687 := rs (se 1 (by rfl) ⟨49265, by rfl⟩) R98531
theorem R65753 : Reach 65753 := rs (se 2 (by rfl) ⟨24657, by rfl⟩) R49315
theorem R98585 : Reach 98585 := rs (se 2 (by rfl) ⟨36969, by rfl⟩) R73939
theorem R65867 : Reach 65867 := rs (se 1 (by rfl) ⟨49400, by rfl⟩) R98801
theorem R65879 : Reach 65879 := rs (se 1 (by rfl) ⟨49409, by rfl⟩) R98819
theorem R98675 : Reach 98675 := rs (se 1 (by rfl) ⟨74006, by rfl⟩) R148013
theorem R98711 : Reach 98711 := rs (se 1 (by rfl) ⟨74033, by rfl⟩) R148067
theorem R65945 : Reach 65945 := rs (se 2 (by rfl) ⟨24729, by rfl⟩) R49459
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R66059 : Reach 66059 := rs (se 1 (by rfl) ⟨49544, by rfl⟩) R99089
theorem R164375 : Reach 164375 := rs (se 1 (by rfl) ⟨123281, by rfl⟩) R246563
theorem R66071 : Reach 66071 := rs (se 1 (by rfl) ⟨49553, by rfl⟩) R99107
theorem R557603 : Reach 557603 := rs (se 1 (by rfl) ⟨418202, by rfl⟩) R836405
theorem R98891 : Reach 98891 := rs (se 1 (by rfl) ⟨74168, by rfl⟩) R148337
theorem R66137 : Reach 66137 := rs (se 2 (by rfl) ⟨24801, by rfl⟩) R49603
theorem R98945 : Reach 98945 := rs (se 2 (by rfl) ⟨37104, by rfl⟩) R74209
theorem R426647 : Reach 426647 := rs (se 1 (by rfl) ⟨319985, by rfl⟩) R639971
theorem R66199 : Reach 66199 := rs (se 1 (by rfl) ⟨49649, by rfl⟩) R99299
theorem R230039 : Reach 230039 := rs (se 1 (by rfl) ⟨172529, by rfl⟩) R345059
theorem R66251 : Reach 66251 := rs (se 1 (by rfl) ⟨49688, by rfl⟩) R99377
theorem R66263 : Reach 66263 := rs (se 1 (by rfl) ⟨49697, by rfl⟩) R99395
theorem R131801 : Reach 131801 := rs (se 2 (by rfl) ⟨49425, by rfl⟩) R98851
theorem R66329 : Reach 66329 := rs (se 2 (by rfl) ⟨24873, by rfl⟩) R49747
theorem R99161 : Reach 99161 := rs (se 2 (by rfl) ⟨37185, by rfl⟩) R74371
theorem R623477 : Reach 623477 := rs (se 5 (by rfl) ⟨29225, by rfl⟩) R58451
theorem R66443 : Reach 66443 := rs (se 1 (by rfl) ⟨49832, by rfl⟩) R99665
theorem R66455 : Reach 66455 := rs (se 1 (by rfl) ⟨49841, by rfl⟩) R99683
theorem R197549 : Reach 197549 := rs (se 3 (by rfl) ⟨37040, by rfl⟩) R74081
theorem R99251 : Reach 99251 := rs (se 1 (by rfl) ⟨74438, by rfl⟩) R148877
theorem R99287 : Reach 99287 := rs (se 1 (by rfl) ⟨74465, by rfl⟩) R148931
theorem R66521 : Reach 66521 := rs (se 2 (by rfl) ⟨24945, by rfl⟩) R49891
theorem R66635 : Reach 66635 := rs (se 1 (by rfl) ⟨49976, by rfl⟩) R99953
theorem R66647 : Reach 66647 := rs (se 1 (by rfl) ⟨49985, by rfl⟩) R99971
theorem R99467 : Reach 99467 := rs (se 1 (by rfl) ⟨74600, by rfl⟩) R149201
theorem R66713 : Reach 66713 := rs (se 2 (by rfl) ⟨25017, by rfl⟩) R50035
theorem R99521 : Reach 99521 := rs (se 2 (by rfl) ⟨37320, by rfl⟩) R74641
theorem R66827 : Reach 66827 := rs (se 1 (by rfl) ⟨50120, by rfl⟩) R100241
theorem R66839 : Reach 66839 := rs (se 1 (by rfl) ⟨50129, by rfl⟩) R100259
theorem R66905 : Reach 66905 := rs (se 2 (by rfl) ⟨25089, by rfl⟩) R50179
theorem R99737 : Reach 99737 := rs (se 2 (by rfl) ⟨37401, by rfl⟩) R74803
theorem R99787 : Reach 99787 := rs (se 1 (by rfl) ⟨74840, by rfl⟩) R149681
theorem R67019 : Reach 67019 := rs (se 1 (by rfl) ⟨50264, by rfl⟩) R100529
theorem R67031 : Reach 67031 := rs (se 1 (by rfl) ⟨50273, by rfl⟩) R100547
theorem R99827 : Reach 99827 := rs (se 1 (by rfl) ⟨74870, by rfl⟩) R149741
theorem R99863 : Reach 99863 := rs (se 1 (by rfl) ⟨74897, by rfl⟩) R149795
theorem R67097 : Reach 67097 := rs (se 2 (by rfl) ⟨25161, by rfl⟩) R50323
theorem R198233 : Reach 198233 := rs (se 2 (by rfl) ⟨74337, by rfl⟩) R148675
theorem R67211 : Reach 67211 := rs (se 1 (by rfl) ⟨50408, by rfl⟩) R100817
theorem R67223 : Reach 67223 := rs (se 1 (by rfl) ⟨50417, by rfl⟩) R100835
theorem R100043 : Reach 100043 := rs (se 1 (by rfl) ⟨75032, by rfl⟩) R150065
theorem R67289 : Reach 67289 := rs (se 2 (by rfl) ⟨25233, by rfl⟩) R50467
theorem R100097 : Reach 100097 := rs (se 2 (by rfl) ⟨37536, by rfl⟩) R75073
theorem R165635 : Reach 165635 := rs (se 1 (by rfl) ⟨124226, by rfl⟩) R248453
theorem R67339 : Reach 67339 := rs (se 1 (by rfl) ⟨50504, by rfl⟩) R101009
theorem R329507 : Reach 329507 := rs (se 1 (by rfl) ⟨247130, by rfl⟩) R494261
theorem R67403 : Reach 67403 := rs (se 1 (by rfl) ⟨50552, by rfl⟩) R101105
theorem R67415 : Reach 67415 := rs (se 1 (by rfl) ⟨50561, by rfl⟩) R101123
theorem R952165 : Reach 952165 := rs (se 4 (by rfl) ⟨89265, by rfl⟩) R178531
theorem R67481 : Reach 67481 := rs (se 2 (by rfl) ⟨25305, by rfl⟩) R50611
theorem R100313 : Reach 100313 := rs (se 2 (by rfl) ⟨37617, by rfl⟩) R75235
theorem R67595 : Reach 67595 := rs (se 1 (by rfl) ⟨50696, by rfl⟩) R101393
theorem R67607 : Reach 67607 := rs (se 1 (by rfl) ⟨50705, by rfl⟩) R101411
theorem R100403 : Reach 100403 := rs (se 1 (by rfl) ⟨75302, by rfl⟩) R150605
theorem R100439 : Reach 100439 := rs (se 1 (by rfl) ⟨75329, by rfl⟩) R150659
theorem R67673 : Reach 67673 := rs (se 2 (by rfl) ⟨25377, by rfl⟩) R50755
theorem R133271 : Reach 133271 := rs (se 1 (by rfl) ⟨99953, by rfl⟩) R199907
theorem R67787 : Reach 67787 := rs (se 1 (by rfl) ⟨50840, by rfl⟩) R101681
theorem R67799 : Reach 67799 := rs (se 1 (by rfl) ⟨50849, by rfl⟩) R101699
theorem R100595 : Reach 100595 := rs (se 1 (by rfl) ⟨75446, by rfl⟩) R150893
theorem R100619 : Reach 100619 := rs (se 1 (by rfl) ⟨75464, by rfl⟩) R150929
theorem R67865 : Reach 67865 := rs (se 2 (by rfl) ⟨25449, by rfl⟩) R50899
theorem R100673 : Reach 100673 := rs (se 2 (by rfl) ⟨37752, by rfl⟩) R75505
theorem R67979 : Reach 67979 := rs (se 1 (by rfl) ⟨50984, by rfl⟩) R101969
theorem R67991 : Reach 67991 := rs (se 1 (by rfl) ⟨50993, by rfl⟩) R101987
theorem R68057 : Reach 68057 := rs (se 2 (by rfl) ⟨25521, by rfl⟩) R51043
theorem R100889 : Reach 100889 := rs (se 2 (by rfl) ⟨37833, by rfl⟩) R75667
theorem R68171 : Reach 68171 := rs (se 1 (by rfl) ⟨51128, by rfl⟩) R102257
theorem R68183 : Reach 68183 := rs (se 1 (by rfl) ⟨51137, by rfl⟩) R102275
theorem R100979 : Reach 100979 := rs (se 1 (by rfl) ⟨75734, by rfl⟩) R151469
theorem R101015 : Reach 101015 := rs (se 1 (by rfl) ⟨75761, by rfl⟩) R151523
theorem R68249 : Reach 68249 := rs (se 2 (by rfl) ⟨25593, by rfl⟩) R51187
theorem R68363 : Reach 68363 := rs (se 1 (by rfl) ⟨51272, by rfl⟩) R102545
theorem R68375 : Reach 68375 := rs (se 1 (by rfl) ⟨51281, by rfl⟩) R102563
theorem R101195 : Reach 101195 := rs (se 1 (by rfl) ⟨75896, by rfl⟩) R151793
theorem R68441 : Reach 68441 := rs (se 2 (by rfl) ⟨25665, by rfl⟩) R51331
theorem R101249 : Reach 101249 := rs (se 2 (by rfl) ⟨37968, by rfl⟩) R75937
theorem R68555 : Reach 68555 := rs (se 1 (by rfl) ⟨51416, by rfl⟩) R102833
theorem R68567 : Reach 68567 := rs (se 1 (by rfl) ⟨51425, by rfl⟩) R102851
theorem R68633 : Reach 68633 := rs (se 2 (by rfl) ⟨25737, by rfl⟩) R51475
theorem R101465 : Reach 101465 := rs (se 2 (by rfl) ⟨38049, by rfl⟩) R76099
theorem R68747 : Reach 68747 := rs (se 1 (by rfl) ⟨51560, by rfl⟩) R103121
theorem R68759 : Reach 68759 := rs (se 1 (by rfl) ⟨51569, by rfl⟩) R103139
theorem R101555 : Reach 101555 := rs (se 1 (by rfl) ⟨76166, by rfl⟩) R152333
theorem R101591 : Reach 101591 := rs (se 1 (by rfl) ⟨76193, by rfl⟩) R152387
theorem R68825 : Reach 68825 := rs (se 2 (by rfl) ⟨25809, by rfl⟩) R51619
theorem R265517 : Reach 265517 := rs (se 3 (by rfl) ⟨49784, by rfl⟩) R99569
theorem R68939 : Reach 68939 := rs (se 1 (by rfl) ⟨51704, by rfl⟩) R103409
theorem R68951 : Reach 68951 := rs (se 1 (by rfl) ⟨51713, by rfl⟩) R103427
theorem R101771 : Reach 101771 := rs (se 1 (by rfl) ⟨76328, by rfl⟩) R152657
theorem R69017 : Reach 69017 := rs (se 2 (by rfl) ⟨25881, by rfl⟩) R51763
theorem R527795 : Reach 527795 := rs (se 1 (by rfl) ⟨395846, by rfl⟩) R791693
theorem R101825 : Reach 101825 := rs (se 2 (by rfl) ⟨38184, by rfl⟩) R76369
theorem R69131 : Reach 69131 := rs (se 1 (by rfl) ⟨51848, by rfl⟩) R103697
theorem R69143 : Reach 69143 := rs (se 1 (by rfl) ⟨51857, by rfl⟩) R103715
theorem R69209 : Reach 69209 := rs (se 2 (by rfl) ⟨25953, by rfl⟩) R51907
theorem R102041 : Reach 102041 := rs (se 2 (by rfl) ⟨38265, by rfl⟩) R76531
theorem R69323 : Reach 69323 := rs (se 1 (by rfl) ⟨51992, by rfl⟩) R103985
theorem R69335 : Reach 69335 := rs (se 1 (by rfl) ⟨52001, by rfl⟩) R104003
theorem R134873 : Reach 134873 := rs (se 2 (by rfl) ⟨50577, by rfl⟩) R101155
theorem R102131 : Reach 102131 := rs (se 1 (by rfl) ⟨76598, by rfl⟩) R153197
theorem R102167 : Reach 102167 := rs (se 1 (by rfl) ⟨76625, by rfl⟩) R153251
theorem R69401 : Reach 69401 := rs (se 2 (by rfl) ⟨26025, by rfl⟩) R52051
theorem R69515 : Reach 69515 := rs (se 1 (by rfl) ⟨52136, by rfl⟩) R104273
theorem R69527 : Reach 69527 := rs (se 1 (by rfl) ⟨52145, by rfl⟩) R104291
theorem R102347 : Reach 102347 := rs (se 1 (by rfl) ⟨76760, by rfl⟩) R153521
theorem R69593 : Reach 69593 := rs (se 2 (by rfl) ⟨26097, by rfl⟩) R52195
theorem R69707 : Reach 69707 := rs (se 1 (by rfl) ⟨52280, by rfl⟩) R104561
theorem R69719 : Reach 69719 := rs (se 1 (by rfl) ⟨52289, by rfl⟩) R104579
theorem R233603 : Reach 233603 := rs (se 1 (by rfl) ⟨175202, by rfl⟩) R350405
theorem R69785 : Reach 69785 := rs (se 2 (by rfl) ⟨26169, by rfl⟩) R52339
theorem R168115 : Reach 168115 := rs (se 1 (by rfl) ⟨126086, by rfl⟩) R252173
theorem R102617 : Reach 102617 := rs (se 2 (by rfl) ⟨38481, by rfl⟩) R76963
theorem R69899 : Reach 69899 := rs (se 1 (by rfl) ⟨52424, by rfl⟩) R104849
theorem R69911 : Reach 69911 := rs (se 1 (by rfl) ⟨52433, by rfl⟩) R104867
theorem R102707 : Reach 102707 := rs (se 1 (by rfl) ⟨77030, by rfl⟩) R154061
theorem R69977 : Reach 69977 := rs (se 2 (by rfl) ⟨26241, by rfl⟩) R52483
theorem R70091 : Reach 70091 := rs (se 1 (by rfl) ⟨52568, by rfl⟩) R105137
theorem R70103 : Reach 70103 := rs (se 1 (by rfl) ⟨52577, by rfl⟩) R105155
theorem R70169 : Reach 70169 := rs (se 2 (by rfl) ⟨26313, by rfl⟩) R52627
theorem R102977 : Reach 102977 := rs (se 2 (by rfl) ⟨38616, by rfl⟩) R77233
theorem R70283 : Reach 70283 := rs (se 1 (by rfl) ⟨52712, by rfl⟩) R105425
theorem R70295 : Reach 70295 := rs (se 1 (by rfl) ⟨52721, by rfl⟩) R105443
theorem R70361 : Reach 70361 := rs (se 2 (by rfl) ⟨26385, by rfl⟩) R52771
theorem R168749 : Reach 168749 := rs (se 3 (by rfl) ⟨31640, by rfl⟩) R63281
theorem R70475 : Reach 70475 := rs (se 1 (by rfl) ⟨52856, by rfl⟩) R105713
theorem R70487 : Reach 70487 := rs (se 1 (by rfl) ⟨52865, by rfl⟩) R105731
theorem R529253 : Reach 529253 := rs (se 4 (by rfl) ⟨49617, by rfl⟩) R99235
theorem R103319 : Reach 103319 := rs (se 1 (by rfl) ⟨77489, by rfl⟩) R154979
theorem R70553 : Reach 70553 := rs (se 2 (by rfl) ⟨26457, by rfl⟩) R52915
theorem R70667 : Reach 70667 := rs (se 1 (by rfl) ⟨53000, by rfl⟩) R106001
theorem R70679 : Reach 70679 := rs (se 1 (by rfl) ⟨53009, by rfl⟩) R106019
theorem R103499 : Reach 103499 := rs (se 1 (by rfl) ⟨77624, by rfl⟩) R155249
theorem R660611 : Reach 660611 := rs (se 1 (by rfl) ⟨495458, by rfl⟩) R990917
theorem R169219 : Reach 169219 := rs (se 1 (by rfl) ⟨126914, by rfl⟩) R253829
theorem R103769 : Reach 103769 := rs (se 2 (by rfl) ⟨38913, by rfl⟩) R77827
theorem R791909 : Reach 791909 := rs (se 4 (by rfl) ⟨74241, by rfl⟩) R148483
theorem R202115 : Reach 202115 := rs (se 1 (by rfl) ⟨151586, by rfl⟩) R303173
theorem R103859 : Reach 103859 := rs (se 1 (by rfl) ⟨77894, by rfl⟩) R155789
theorem R169523 : Reach 169523 := rs (se 1 (by rfl) ⟨127142, by rfl⟩) R254285
theorem R267907 : Reach 267907 := rs (se 1 (by rfl) ⟨200930, by rfl⟩) R401861
theorem R104129 : Reach 104129 := rs (se 2 (by rfl) ⟨39048, by rfl⟩) R78097
theorem R202571 : Reach 202571 := rs (se 1 (by rfl) ⟨151928, by rfl⟩) R303857
theorem R104471 : Reach 104471 := rs (se 1 (by rfl) ⟨78353, by rfl⟩) R156707
theorem R104651 : Reach 104651 := rs (se 1 (by rfl) ⟨78488, by rfl⟩) R156977
theorem R661709 : Reach 661709 := rs (se 3 (by rfl) ⟨124070, by rfl⟩) R248141
theorem R268609 : Reach 268609 := rs (se 2 (by rfl) ⟨100728, by rfl⟩) R201457
theorem R104921 : Reach 104921 := rs (se 2 (by rfl) ⟨39345, by rfl⟩) R78691
theorem R105011 : Reach 105011 := rs (se 1 (by rfl) ⟨78758, by rfl⟩) R157517
theorem R170561 : Reach 170561 := rs (se 2 (by rfl) ⟨63960, by rfl⟩) R127921
theorem R105281 : Reach 105281 := rs (se 2 (by rfl) ⟨39480, by rfl⟩) R78961
theorem R171011 : Reach 171011 := rs (se 1 (by rfl) ⟨128258, by rfl⟩) R256517
theorem R334853 : Reach 334853 := rs (se 4 (by rfl) ⟨31392, by rfl⟩) R62785
theorem R171031 : Reach 171031 := rs (se 1 (by rfl) ⟨128273, by rfl⟩) R256547
theorem R105623 : Reach 105623 := rs (se 1 (by rfl) ⟨79217, by rfl⟩) R158435
theorem R597293 : Reach 597293 := rs (se 3 (by rfl) ⟨111992, by rfl⟩) R223985
theorem R105803 : Reach 105803 := rs (se 1 (by rfl) ⟨79352, by rfl⟩) R158705
theorem R73163 : Reach 73163 := rs (se 1 (by rfl) ⟨54872, by rfl⟩) R109745
theorem R171467 : Reach 171467 := rs (se 1 (by rfl) ⟨128600, by rfl⟩) R257201
theorem R73291 : Reach 73291 := rs (se 1 (by rfl) ⟨54968, by rfl⟩) R109937
theorem R171665 : Reach 171665 := rs (se 2 (by rfl) ⟨64374, by rfl⟩) R128749
theorem R73433 : Reach 73433 := rs (se 2 (by rfl) ⟨27537, by rfl⟩) R55075
theorem R106201 : Reach 106201 := rs (se 2 (by rfl) ⟨39825, by rfl⟩) R79651
theorem R237329 : Reach 237329 := rs (se 2 (by rfl) ⟨88998, by rfl⟩) R177997
theorem R73561 : Reach 73561 := rs (se 2 (by rfl) ⟨27585, by rfl⟩) R55171
theorem R237491 : Reach 237491 := rs (se 1 (by rfl) ⟨178118, by rfl⟩) R356237
theorem R74135 : Reach 74135 := rs (se 1 (by rfl) ⟨55601, by rfl⟩) R111203
theorem R172439 : Reach 172439 := rs (se 1 (by rfl) ⟨129329, by rfl⟩) R258659
theorem R74263 : Reach 74263 := rs (se 1 (by rfl) ⟨55697, by rfl⟩) R111395
theorem R172637 : Reach 172637 := rs (se 3 (by rfl) ⟨32369, by rfl⟩) R64739
theorem R140183 : Reach 140183 := rs (se 1 (by rfl) ⟨105137, by rfl⟩) R210275
theorem R107585 : Reach 107585 := rs (se 2 (by rfl) ⟨40344, by rfl⟩) R80689
theorem R205955 : Reach 205955 := rs (se 1 (by rfl) ⟨154466, by rfl⟩) R308933
theorem R74891 : Reach 74891 := rs (se 1 (by rfl) ⟨56168, by rfl⟩) R112337
theorem R75019 : Reach 75019 := rs (se 1 (by rfl) ⟨56264, by rfl⟩) R112529
theorem R337283 : Reach 337283 := rs (se 1 (by rfl) ⟨252962, by rfl⟩) R505925
theorem R75161 : Reach 75161 := rs (se 2 (by rfl) ⟨28185, by rfl⟩) R56371
theorem R75289 : Reach 75289 := rs (se 2 (by rfl) ⟨28233, by rfl⟩) R56467
theorem R75403 : Reach 75403 := rs (se 1 (by rfl) ⟨56552, by rfl⟩) R113105
theorem R75863 : Reach 75863 := rs (se 1 (by rfl) ⟨56897, by rfl⟩) R113795
theorem R43127 : Reach 43127 := rs (se 1 (by rfl) ⟨32345, by rfl⟩) R64691
theorem R43147 : Reach 43147 := rs (se 1 (by rfl) ⟨32360, by rfl⟩) R64721
theorem R43159 : Reach 43159 := rs (se 1 (by rfl) ⟨32369, by rfl⟩) R64739
theorem R43179 : Reach 43179 := rs (se 1 (by rfl) ⟨32384, by rfl⟩) R64769
theorem R43191 : Reach 43191 := rs (se 1 (by rfl) ⟨32393, by rfl⟩) R64787
theorem R43211 : Reach 43211 := rs (se 1 (by rfl) ⟨32408, by rfl⟩) R64817
theorem R43223 : Reach 43223 := rs (se 1 (by rfl) ⟨32417, by rfl⟩) R64835
theorem R75991 : Reach 75991 := rs (se 1 (by rfl) ⟨56993, by rfl⟩) R113987
theorem R43243 : Reach 43243 := rs (se 1 (by rfl) ⟨32432, by rfl⟩) R64865
theorem R43255 : Reach 43255 := rs (se 1 (by rfl) ⟨32441, by rfl⟩) R64883
theorem R43275 : Reach 43275 := rs (se 1 (by rfl) ⟨32456, by rfl⟩) R64913
theorem R43287 : Reach 43287 := rs (se 1 (by rfl) ⟨32465, by rfl⟩) R64931
theorem R43307 : Reach 43307 := rs (se 1 (by rfl) ⟨32480, by rfl⟩) R64961
theorem R43319 : Reach 43319 := rs (se 1 (by rfl) ⟨32489, by rfl⟩) R64979
theorem R43339 : Reach 43339 := rs (se 1 (by rfl) ⟨32504, by rfl⟩) R65009
theorem R43351 : Reach 43351 := rs (se 1 (by rfl) ⟨32513, by rfl⟩) R65027
theorem R43371 : Reach 43371 := rs (se 1 (by rfl) ⟨32528, by rfl⟩) R65057
theorem R43383 : Reach 43383 := rs (se 1 (by rfl) ⟨32537, by rfl⟩) R65075
theorem R43403 : Reach 43403 := rs (se 1 (by rfl) ⟨32552, by rfl⟩) R65105
theorem R43415 : Reach 43415 := rs (se 1 (by rfl) ⟨32561, by rfl⟩) R65123
theorem R43435 : Reach 43435 := rs (se 1 (by rfl) ⟨32576, by rfl⟩) R65153
theorem R43447 : Reach 43447 := rs (se 1 (by rfl) ⟨32585, by rfl⟩) R65171
theorem R43467 : Reach 43467 := rs (se 1 (by rfl) ⟨32600, by rfl⟩) R65201
theorem R76235 : Reach 76235 := rs (se 1 (by rfl) ⟨57176, by rfl⟩) R114353
theorem R43479 : Reach 43479 := rs (se 1 (by rfl) ⟨32609, by rfl⟩) R65219
theorem R43499 : Reach 43499 := rs (se 1 (by rfl) ⟨32624, by rfl⟩) R65249
theorem R43511 : Reach 43511 := rs (se 1 (by rfl) ⟨32633, by rfl⟩) R65267
theorem R174595 : Reach 174595 := rs (se 1 (by rfl) ⟨130946, by rfl⟩) R261893
theorem R43531 : Reach 43531 := rs (se 1 (by rfl) ⟨32648, by rfl⟩) R65297
theorem R43543 : Reach 43543 := rs (se 1 (by rfl) ⟨32657, by rfl⟩) R65315
theorem R404003 : Reach 404003 := rs (se 1 (by rfl) ⟨303002, by rfl⟩) R606005
theorem R43563 : Reach 43563 := rs (se 1 (by rfl) ⟨32672, by rfl⟩) R65345
theorem R43575 : Reach 43575 := rs (se 1 (by rfl) ⟨32681, by rfl⟩) R65363
theorem R43595 : Reach 43595 := rs (se 1 (by rfl) ⟨32696, by rfl⟩) R65393
theorem R43607 : Reach 43607 := rs (se 1 (by rfl) ⟨32705, by rfl⟩) R65411
theorem R43627 : Reach 43627 := rs (se 1 (by rfl) ⟨32720, by rfl⟩) R65441
theorem R43639 : Reach 43639 := rs (se 1 (by rfl) ⟨32729, by rfl⟩) R65459
theorem R43659 : Reach 43659 := rs (se 1 (by rfl) ⟨32744, by rfl⟩) R65489
theorem R43671 : Reach 43671 := rs (se 1 (by rfl) ⟨32753, by rfl⟩) R65507
theorem R43691 : Reach 43691 := rs (se 1 (by rfl) ⟨32768, by rfl⟩) R65537
theorem R43703 : Reach 43703 := rs (se 1 (by rfl) ⟨32777, by rfl⟩) R65555
theorem R109259 : Reach 109259 := rs (se 1 (by rfl) ⟨81944, by rfl⟩) R163889
theorem R43723 : Reach 43723 := rs (se 1 (by rfl) ⟨32792, by rfl⟩) R65585
theorem R43735 : Reach 43735 := rs (se 1 (by rfl) ⟨32801, by rfl⟩) R65603
theorem R43755 : Reach 43755 := rs (se 1 (by rfl) ⟨32816, by rfl⟩) R65633
theorem R43767 : Reach 43767 := rs (se 1 (by rfl) ⟨32825, by rfl⟩) R65651
theorem R43787 : Reach 43787 := rs (se 1 (by rfl) ⟨32840, by rfl⟩) R65681
theorem R43799 : Reach 43799 := rs (se 1 (by rfl) ⟨32849, by rfl⟩) R65699
theorem R43819 : Reach 43819 := rs (se 1 (by rfl) ⟨32864, by rfl⟩) R65729
theorem R174899 : Reach 174899 := rs (se 1 (by rfl) ⟨131174, by rfl⟩) R262349
theorem R43831 : Reach 43831 := rs (se 1 (by rfl) ⟨32873, by rfl⟩) R65747
theorem R43851 : Reach 43851 := rs (se 1 (by rfl) ⟨32888, by rfl⟩) R65777
theorem R76619 : Reach 76619 := rs (se 1 (by rfl) ⟨57464, by rfl⟩) R114929
theorem R43863 : Reach 43863 := rs (se 1 (by rfl) ⟨32897, by rfl⟩) R65795
theorem R43883 : Reach 43883 := rs (se 1 (by rfl) ⟨32912, by rfl⟩) R65825
theorem R43895 : Reach 43895 := rs (se 1 (by rfl) ⟨32921, by rfl⟩) R65843
theorem R76673 : Reach 76673 := rs (se 2 (by rfl) ⟨28752, by rfl⟩) R57505
theorem R43915 : Reach 43915 := rs (se 1 (by rfl) ⟨32936, by rfl⟩) R65873
theorem R43927 : Reach 43927 := rs (se 1 (by rfl) ⟨32945, by rfl⟩) R65891
theorem R43947 : Reach 43947 := rs (se 1 (by rfl) ⟨32960, by rfl⟩) R65921
theorem R43959 : Reach 43959 := rs (se 1 (by rfl) ⟨32969, by rfl⟩) R65939
theorem R43979 : Reach 43979 := rs (se 1 (by rfl) ⟨32984, by rfl⟩) R65969
theorem R76747 : Reach 76747 := rs (se 1 (by rfl) ⟨57560, by rfl⟩) R115121
theorem R43991 : Reach 43991 := rs (se 1 (by rfl) ⟨32993, by rfl⟩) R65987
theorem R44011 : Reach 44011 := rs (se 1 (by rfl) ⟨33008, by rfl⟩) R66017
theorem R44023 : Reach 44023 := rs (se 1 (by rfl) ⟨33017, by rfl⟩) R66035
theorem R76801 : Reach 76801 := rs (se 2 (by rfl) ⟨28800, by rfl⟩) R57601
theorem R44043 : Reach 44043 := rs (se 1 (by rfl) ⟨33032, by rfl⟩) R66065
theorem R44055 : Reach 44055 := rs (se 1 (by rfl) ⟨33041, by rfl⟩) R66083
theorem R44075 : Reach 44075 := rs (se 1 (by rfl) ⟨33056, by rfl⟩) R66113
theorem R44087 : Reach 44087 := rs (se 1 (by rfl) ⟨33065, by rfl⟩) R66131
theorem R109633 : Reach 109633 := rs (se 2 (by rfl) ⟨41112, by rfl⟩) R82225
theorem R44107 : Reach 44107 := rs (se 1 (by rfl) ⟨33080, by rfl⟩) R66161
theorem R44119 : Reach 44119 := rs (se 1 (by rfl) ⟨33089, by rfl⟩) R66179
theorem R76889 : Reach 76889 := rs (se 2 (by rfl) ⟨28833, by rfl⟩) R57667
theorem R44139 : Reach 44139 := rs (se 1 (by rfl) ⟨33104, by rfl⟩) R66209
theorem R44151 : Reach 44151 := rs (se 1 (by rfl) ⟨33113, by rfl⟩) R66227
theorem R44171 : Reach 44171 := rs (se 1 (by rfl) ⟨33128, by rfl⟩) R66257
theorem R44183 : Reach 44183 := rs (se 1 (by rfl) ⟨33137, by rfl⟩) R66275
theorem R44203 : Reach 44203 := rs (se 1 (by rfl) ⟨33152, by rfl⟩) R66305
theorem R44215 : Reach 44215 := rs (se 1 (by rfl) ⟨33161, by rfl⟩) R66323
theorem R44235 : Reach 44235 := rs (se 1 (by rfl) ⟨33176, by rfl⟩) R66353
theorem R44247 : Reach 44247 := rs (se 1 (by rfl) ⟨33185, by rfl⟩) R66371
theorem R77017 : Reach 77017 := rs (se 2 (by rfl) ⟨28881, by rfl⟩) R57763
theorem R44267 : Reach 44267 := rs (se 1 (by rfl) ⟨33200, by rfl⟩) R66401
theorem R44279 : Reach 44279 := rs (se 1 (by rfl) ⟨33209, by rfl⟩) R66419
theorem R1682693 : Reach 1682693 := rs (se 4 (by rfl) ⟨157752, by rfl⟩) R315505
theorem R44299 : Reach 44299 := rs (se 1 (by rfl) ⟨33224, by rfl⟩) R66449
theorem R44311 : Reach 44311 := rs (se 1 (by rfl) ⟨33233, by rfl⟩) R66467
theorem R44331 : Reach 44331 := rs (se 1 (by rfl) ⟨33248, by rfl⟩) R66497
theorem R175405 : Reach 175405 := rs (se 3 (by rfl) ⟨32888, by rfl⟩) R65777
theorem R44343 : Reach 44343 := rs (se 1 (by rfl) ⟨33257, by rfl⟩) R66515
theorem R44363 : Reach 44363 := rs (se 1 (by rfl) ⟨33272, by rfl⟩) R66545
theorem R44375 : Reach 44375 := rs (se 1 (by rfl) ⟨33281, by rfl⟩) R66563
theorem R44395 : Reach 44395 := rs (se 1 (by rfl) ⟨33296, by rfl⟩) R66593
theorem R44407 : Reach 44407 := rs (se 1 (by rfl) ⟨33305, by rfl⟩) R66611
theorem R44427 : Reach 44427 := rs (se 1 (by rfl) ⟨33320, by rfl⟩) R66641
theorem R44439 : Reach 44439 := rs (se 1 (by rfl) ⟨33329, by rfl⟩) R66659
theorem R44459 : Reach 44459 := rs (se 1 (by rfl) ⟨33344, by rfl⟩) R66689
theorem R44471 : Reach 44471 := rs (se 1 (by rfl) ⟨33353, by rfl⟩) R66707
theorem R175553 : Reach 175553 := rs (se 2 (by rfl) ⟨65832, by rfl⟩) R131665
theorem R44491 : Reach 44491 := rs (se 1 (by rfl) ⟨33368, by rfl⟩) R66737
theorem R44503 : Reach 44503 := rs (se 1 (by rfl) ⟨33377, by rfl⟩) R66755
theorem R372185 : Reach 372185 := rs (se 2 (by rfl) ⟨139569, by rfl⟩) R279139
theorem R44523 : Reach 44523 := rs (se 1 (by rfl) ⟨33392, by rfl⟩) R66785
theorem R44535 : Reach 44535 := rs (se 1 (by rfl) ⟨33401, by rfl⟩) R66803
theorem R44555 : Reach 44555 := rs (se 1 (by rfl) ⟨33416, by rfl⟩) R66833
theorem R44567 : Reach 44567 := rs (se 1 (by rfl) ⟨33425, by rfl⟩) R66851
theorem R437795 : Reach 437795 := rs (se 1 (by rfl) ⟨328346, by rfl⟩) R656693
theorem R44587 : Reach 44587 := rs (se 1 (by rfl) ⟨33440, by rfl⟩) R66881
theorem R44599 : Reach 44599 := rs (se 1 (by rfl) ⟨33449, by rfl⟩) R66899
theorem R44619 : Reach 44619 := rs (se 1 (by rfl) ⟨33464, by rfl⟩) R66929
theorem R44631 : Reach 44631 := rs (se 1 (by rfl) ⟨33473, by rfl⟩) R66947
theorem R44651 : Reach 44651 := rs (se 1 (by rfl) ⟨33488, by rfl⟩) R66977
theorem R44663 : Reach 44663 := rs (se 1 (by rfl) ⟨33497, by rfl⟩) R66995
theorem R44683 : Reach 44683 := rs (se 1 (by rfl) ⟨33512, by rfl⟩) R67025
theorem R110231 : Reach 110231 := rs (se 1 (by rfl) ⟨82673, by rfl⟩) R165347
theorem R44695 : Reach 44695 := rs (se 1 (by rfl) ⟨33521, by rfl⟩) R67043
theorem R44715 : Reach 44715 := rs (se 1 (by rfl) ⟨33536, by rfl⟩) R67073
theorem R44727 : Reach 44727 := rs (se 1 (by rfl) ⟨33545, by rfl⟩) R67091
theorem R44747 : Reach 44747 := rs (se 1 (by rfl) ⟨33560, by rfl⟩) R67121
theorem R44759 : Reach 44759 := rs (se 1 (by rfl) ⟨33569, by rfl⟩) R67139
theorem R44779 : Reach 44779 := rs (se 1 (by rfl) ⟨33584, by rfl⟩) R67169
theorem R44791 : Reach 44791 := rs (se 1 (by rfl) ⟨33593, by rfl⟩) R67187
theorem R44811 : Reach 44811 := rs (se 1 (by rfl) ⟨33608, by rfl⟩) R67217
theorem R44823 : Reach 44823 := rs (se 1 (by rfl) ⟨33617, by rfl⟩) R67235
theorem R77591 : Reach 77591 := rs (se 1 (by rfl) ⟨58193, by rfl⟩) R116387
theorem R44843 : Reach 44843 := rs (se 1 (by rfl) ⟨33632, by rfl⟩) R67265
theorem R44855 : Reach 44855 := rs (se 1 (by rfl) ⟨33641, by rfl⟩) R67283
theorem R44875 : Reach 44875 := rs (se 1 (by rfl) ⟨33656, by rfl⟩) R67313
theorem R44887 : Reach 44887 := rs (se 1 (by rfl) ⟨33665, by rfl⟩) R67331
theorem R44907 : Reach 44907 := rs (se 1 (by rfl) ⟨33680, by rfl⟩) R67361
theorem R44919 : Reach 44919 := rs (se 1 (by rfl) ⟨33689, by rfl⟩) R67379
theorem R44939 : Reach 44939 := rs (se 1 (by rfl) ⟨33704, by rfl⟩) R67409
theorem R44951 : Reach 44951 := rs (se 1 (by rfl) ⟨33713, by rfl⟩) R67427
theorem R77719 : Reach 77719 := rs (se 1 (by rfl) ⟨58289, by rfl⟩) R116579
theorem R44971 : Reach 44971 := rs (se 1 (by rfl) ⟨33728, by rfl⟩) R67457
theorem R44983 : Reach 44983 := rs (se 1 (by rfl) ⟨33737, by rfl⟩) R67475
theorem R45003 : Reach 45003 := rs (se 1 (by rfl) ⟨33752, by rfl⟩) R67505
theorem R45015 : Reach 45015 := rs (se 1 (by rfl) ⟨33761, by rfl⟩) R67523
theorem R45035 : Reach 45035 := rs (se 1 (by rfl) ⟨33776, by rfl⟩) R67553
theorem R45047 : Reach 45047 := rs (se 1 (by rfl) ⟨33785, by rfl⟩) R67571
theorem R45067 : Reach 45067 := rs (se 1 (by rfl) ⟨33800, by rfl⟩) R67601
theorem R45079 : Reach 45079 := rs (se 1 (by rfl) ⟨33809, by rfl⟩) R67619
theorem R45099 : Reach 45099 := rs (se 1 (by rfl) ⟨33824, by rfl⟩) R67649
theorem R45111 : Reach 45111 := rs (se 1 (by rfl) ⟨33833, by rfl⟩) R67667
theorem R45131 : Reach 45131 := rs (se 1 (by rfl) ⟨33848, by rfl⟩) R67697
theorem R45143 : Reach 45143 := rs (se 1 (by rfl) ⟨33857, by rfl⟩) R67715
theorem R45163 : Reach 45163 := rs (se 1 (by rfl) ⟨33872, by rfl⟩) R67745
theorem R45175 : Reach 45175 := rs (se 1 (by rfl) ⟨33881, by rfl⟩) R67763
theorem R45195 : Reach 45195 := rs (se 1 (by rfl) ⟨33896, by rfl⟩) R67793
theorem R45207 : Reach 45207 := rs (se 1 (by rfl) ⟨33905, by rfl⟩) R67811
theorem R45227 : Reach 45227 := rs (se 1 (by rfl) ⟨33920, by rfl⟩) R67841
theorem R45239 : Reach 45239 := rs (se 1 (by rfl) ⟨33929, by rfl⟩) R67859
theorem R45259 : Reach 45259 := rs (se 1 (by rfl) ⟨33944, by rfl⟩) R67889
theorem R45271 : Reach 45271 := rs (se 1 (by rfl) ⟨33953, by rfl⟩) R67907
theorem R45291 : Reach 45291 := rs (se 1 (by rfl) ⟨33968, by rfl⟩) R67937
theorem R45303 : Reach 45303 := rs (se 1 (by rfl) ⟨33977, by rfl⟩) R67955
theorem R45323 : Reach 45323 := rs (se 1 (by rfl) ⟨33992, by rfl⟩) R67985
theorem R241937 : Reach 241937 := rs (se 2 (by rfl) ⟨90726, by rfl⟩) R181453
theorem R45335 : Reach 45335 := rs (se 1 (by rfl) ⟨34001, by rfl⟩) R68003
theorem R45355 : Reach 45355 := rs (se 1 (by rfl) ⟨34016, by rfl⟩) R68033
theorem R78131 : Reach 78131 := rs (se 1 (by rfl) ⟨58598, by rfl⟩) R117197
theorem R45367 : Reach 45367 := rs (se 1 (by rfl) ⟨34025, by rfl⟩) R68051
theorem R45387 : Reach 45387 := rs (se 1 (by rfl) ⟨34040, by rfl⟩) R68081
theorem R45399 : Reach 45399 := rs (se 1 (by rfl) ⟨34049, by rfl⟩) R68099
theorem R45419 : Reach 45419 := rs (se 1 (by rfl) ⟨34064, by rfl⟩) R68129
theorem R45431 : Reach 45431 := rs (se 1 (by rfl) ⟨34073, by rfl⟩) R68147
theorem R45451 : Reach 45451 := rs (se 1 (by rfl) ⟨34088, by rfl⟩) R68177
theorem R45463 : Reach 45463 := rs (se 1 (by rfl) ⟨34097, by rfl⟩) R68195
theorem R45483 : Reach 45483 := rs (se 1 (by rfl) ⟨34112, by rfl⟩) R68225
theorem R78259 : Reach 78259 := rs (se 1 (by rfl) ⟨58694, by rfl⟩) R117389
theorem R45495 : Reach 45495 := rs (se 1 (by rfl) ⟨34121, by rfl⟩) R68243
theorem R111041 : Reach 111041 := rs (se 2 (by rfl) ⟨41640, by rfl⟩) R83281
theorem R143819 : Reach 143819 := rs (se 1 (by rfl) ⟨107864, by rfl⟩) R215729
theorem R45515 : Reach 45515 := rs (se 1 (by rfl) ⟨34136, by rfl⟩) R68273
theorem R45527 : Reach 45527 := rs (se 1 (by rfl) ⟨34145, by rfl⟩) R68291
theorem R45547 : Reach 45547 := rs (se 1 (by rfl) ⟨34160, by rfl⟩) R68321
theorem R45559 : Reach 45559 := rs (se 1 (by rfl) ⟨34169, by rfl⟩) R68339
theorem R45579 : Reach 45579 := rs (se 1 (by rfl) ⟨34184, by rfl⟩) R68369
theorem R78347 : Reach 78347 := rs (se 1 (by rfl) ⟨58760, by rfl⟩) R117521
theorem R45591 : Reach 45591 := rs (se 1 (by rfl) ⟨34193, by rfl⟩) R68387
theorem R45611 : Reach 45611 := rs (se 1 (by rfl) ⟨34208, by rfl⟩) R68417
theorem R45623 : Reach 45623 := rs (se 1 (by rfl) ⟨34217, by rfl⟩) R68435
theorem R78401 : Reach 78401 := rs (se 2 (by rfl) ⟨29400, by rfl⟩) R58801
theorem R45643 : Reach 45643 := rs (se 1 (by rfl) ⟨34232, by rfl⟩) R68465
theorem R111179 : Reach 111179 := rs (se 1 (by rfl) ⟨83384, by rfl⟩) R166769
theorem R45655 : Reach 45655 := rs (se 1 (by rfl) ⟨34241, by rfl⟩) R68483
theorem R45675 : Reach 45675 := rs (se 1 (by rfl) ⟨34256, by rfl⟩) R68513
theorem R45687 : Reach 45687 := rs (se 1 (by rfl) ⟨34265, by rfl⟩) R68531
theorem R569987 : Reach 569987 := rs (se 1 (by rfl) ⟨427490, by rfl⟩) R854981
theorem R45707 : Reach 45707 := rs (se 1 (by rfl) ⟨34280, by rfl⟩) R68561
theorem R78475 : Reach 78475 := rs (se 1 (by rfl) ⟨58856, by rfl⟩) R117713
theorem R45719 : Reach 45719 := rs (se 1 (by rfl) ⟨34289, by rfl⟩) R68579
theorem R45739 : Reach 45739 := rs (se 1 (by rfl) ⟨34304, by rfl⟩) R68609
theorem R176813 : Reach 176813 := rs (se 3 (by rfl) ⟨33152, by rfl⟩) R66305
theorem R45751 : Reach 45751 := rs (se 1 (by rfl) ⟨34313, by rfl⟩) R68627
theorem R78529 : Reach 78529 := rs (se 2 (by rfl) ⟨29448, by rfl⟩) R58897
theorem R45771 : Reach 45771 := rs (se 1 (by rfl) ⟨34328, by rfl⟩) R68657
theorem R176843 : Reach 176843 := rs (se 1 (by rfl) ⟨132632, by rfl⟩) R265265
theorem R340685 : Reach 340685 := rs (se 3 (by rfl) ⟨63878, by rfl⟩) R127757
theorem R45783 : Reach 45783 := rs (se 1 (by rfl) ⟨34337, by rfl⟩) R68675
theorem R45803 : Reach 45803 := rs (se 1 (by rfl) ⟨34352, by rfl⟩) R68705
theorem R635633 : Reach 635633 := rs (se 2 (by rfl) ⟨238362, by rfl⟩) R476725
theorem R45815 : Reach 45815 := rs (se 1 (by rfl) ⟨34361, by rfl⟩) R68723
theorem R45835 : Reach 45835 := rs (se 1 (by rfl) ⟨34376, by rfl⟩) R68753
theorem R45847 : Reach 45847 := rs (se 1 (by rfl) ⟨34385, by rfl⟩) R68771
theorem R78617 : Reach 78617 := rs (se 2 (by rfl) ⟨29481, by rfl⟩) R58963
theorem R45867 : Reach 45867 := rs (se 1 (by rfl) ⟨34400, by rfl⟩) R68801
theorem R45879 : Reach 45879 := rs (se 1 (by rfl) ⟨34409, by rfl⟩) R68819
theorem R45899 : Reach 45899 := rs (se 1 (by rfl) ⟨34424, by rfl⟩) R68849
theorem R45911 : Reach 45911 := rs (se 1 (by rfl) ⟨34433, by rfl⟩) R68867
theorem R111449 : Reach 111449 := rs (se 2 (by rfl) ⟨41793, by rfl⟩) R83587
theorem R45931 : Reach 45931 := rs (se 1 (by rfl) ⟨34448, by rfl⟩) R68897
theorem R78707 : Reach 78707 := rs (se 1 (by rfl) ⟨59030, by rfl⟩) R118061
theorem R45943 : Reach 45943 := rs (se 1 (by rfl) ⟨34457, by rfl⟩) R68915
theorem R45963 : Reach 45963 := rs (se 1 (by rfl) ⟨34472, by rfl⟩) R68945
theorem R45975 : Reach 45975 := rs (se 1 (by rfl) ⟨34481, by rfl⟩) R68963
theorem R78745 : Reach 78745 := rs (se 2 (by rfl) ⟨29529, by rfl⟩) R59059
theorem R45995 : Reach 45995 := rs (se 1 (by rfl) ⟨34496, by rfl⟩) R68993
theorem R46007 : Reach 46007 := rs (se 1 (by rfl) ⟨34505, by rfl⟩) R69011
theorem R46027 : Reach 46027 := rs (se 1 (by rfl) ⟨34520, by rfl⟩) R69041
theorem R46039 : Reach 46039 := rs (se 1 (by rfl) ⟨34529, by rfl⟩) R69059
theorem R111577 : Reach 111577 := rs (se 2 (by rfl) ⟨41841, by rfl⟩) R83683
theorem R46059 : Reach 46059 := rs (se 1 (by rfl) ⟨34544, by rfl⟩) R69089
theorem R46071 : Reach 46071 := rs (se 1 (by rfl) ⟨34553, by rfl⟩) R69107
theorem R46091 : Reach 46091 := rs (se 1 (by rfl) ⟨34568, by rfl⟩) R69137
theorem R46103 : Reach 46103 := rs (se 1 (by rfl) ⟨34577, by rfl⟩) R69155
theorem R46123 : Reach 46123 := rs (se 1 (by rfl) ⟨34592, by rfl⟩) R69185
theorem R46135 : Reach 46135 := rs (se 1 (by rfl) ⟨34601, by rfl⟩) R69203
theorem R46155 : Reach 46155 := rs (se 1 (by rfl) ⟨34616, by rfl⟩) R69233
theorem R46167 : Reach 46167 := rs (se 1 (by rfl) ⟨34625, by rfl⟩) R69251
theorem R78937 : Reach 78937 := rs (se 2 (by rfl) ⟨29601, by rfl⟩) R59203
theorem R46187 : Reach 46187 := rs (se 1 (by rfl) ⟨34640, by rfl⟩) R69281
theorem R46199 : Reach 46199 := rs (se 1 (by rfl) ⟨34649, by rfl⟩) R69299
theorem R46219 : Reach 46219 := rs (se 1 (by rfl) ⟨34664, by rfl⟩) R69329
theorem R799895 : Reach 799895 := rs (se 1 (by rfl) ⟨599921, by rfl⟩) R1199843
theorem R46231 : Reach 46231 := rs (se 1 (by rfl) ⟨34673, by rfl⟩) R69347
theorem R46251 : Reach 46251 := rs (se 1 (by rfl) ⟨34688, by rfl⟩) R69377
theorem R341171 : Reach 341171 := rs (se 1 (by rfl) ⟨255878, by rfl⟩) R511757
theorem R46263 : Reach 46263 := rs (se 1 (by rfl) ⟨34697, by rfl⟩) R69395
theorem R46283 : Reach 46283 := rs (se 1 (by rfl) ⟨34712, by rfl⟩) R69425
theorem R46295 : Reach 46295 := rs (se 1 (by rfl) ⟨34721, by rfl⟩) R69443
theorem R46315 : Reach 46315 := rs (se 1 (by rfl) ⟨34736, by rfl⟩) R69473
theorem R46327 : Reach 46327 := rs (se 1 (by rfl) ⟨34745, by rfl⟩) R69491
theorem R46347 : Reach 46347 := rs (se 1 (by rfl) ⟨34760, by rfl⟩) R69521
theorem R46359 : Reach 46359 := rs (se 1 (by rfl) ⟨34769, by rfl⟩) R69539
theorem R46379 : Reach 46379 := rs (se 1 (by rfl) ⟨34784, by rfl⟩) R69569
theorem R46391 : Reach 46391 := rs (se 1 (by rfl) ⟨34793, by rfl⟩) R69587
theorem R46411 : Reach 46411 := rs (se 1 (by rfl) ⟨34808, by rfl⟩) R69617
theorem R111947 : Reach 111947 := rs (se 1 (by rfl) ⟨83960, by rfl⟩) R167921
theorem R46423 : Reach 46423 := rs (se 1 (by rfl) ⟨34817, by rfl⟩) R69635
theorem R177497 : Reach 177497 := rs (se 2 (by rfl) ⟨66561, by rfl⟩) R133123
theorem R46443 : Reach 46443 := rs (se 1 (by rfl) ⟨34832, by rfl⟩) R69665
theorem R46455 : Reach 46455 := rs (se 1 (by rfl) ⟨34841, by rfl⟩) R69683
theorem R46475 : Reach 46475 := rs (se 1 (by rfl) ⟨34856, by rfl⟩) R69713
theorem R46487 : Reach 46487 := rs (se 1 (by rfl) ⟨34865, by rfl⟩) R69731
theorem R46507 : Reach 46507 := rs (se 1 (by rfl) ⟨34880, by rfl⟩) R69761
theorem R46519 : Reach 46519 := rs (se 1 (by rfl) ⟨34889, by rfl⟩) R69779
theorem R46539 : Reach 46539 := rs (se 1 (by rfl) ⟨34904, by rfl⟩) R69809
theorem R79319 : Reach 79319 := rs (se 1 (by rfl) ⟨59489, by rfl⟩) R118979
theorem R46551 : Reach 46551 := rs (se 1 (by rfl) ⟨34913, by rfl⟩) R69827
theorem R46571 : Reach 46571 := rs (se 1 (by rfl) ⟨34928, by rfl⟩) R69857
theorem R46583 : Reach 46583 := rs (se 1 (by rfl) ⟨34937, by rfl⟩) R69875
theorem R46603 : Reach 46603 := rs (se 1 (by rfl) ⟨34952, by rfl⟩) R69905
theorem R112151 : Reach 112151 := rs (se 1 (by rfl) ⟨84113, by rfl⟩) R168227
theorem R46615 : Reach 46615 := rs (se 1 (by rfl) ⟨34961, by rfl⟩) R69923
theorem R46635 : Reach 46635 := rs (se 1 (by rfl) ⟨34976, by rfl⟩) R69953
theorem R46647 : Reach 46647 := rs (se 1 (by rfl) ⟨34985, by rfl⟩) R69971
theorem R46667 : Reach 46667 := rs (se 1 (by rfl) ⟨35000, by rfl⟩) R70001
theorem R46679 : Reach 46679 := rs (se 1 (by rfl) ⟨35009, by rfl⟩) R70019
theorem R79447 : Reach 79447 := rs (se 1 (by rfl) ⟨59585, by rfl⟩) R119171
theorem R341597 : Reach 341597 := rs (se 3 (by rfl) ⟨64049, by rfl⟩) R128099
theorem R46699 : Reach 46699 := rs (se 1 (by rfl) ⟨35024, by rfl⟩) R70049
theorem R46711 : Reach 46711 := rs (se 1 (by rfl) ⟨35033, by rfl⟩) R70067
theorem R46731 : Reach 46731 := rs (se 1 (by rfl) ⟨35048, by rfl⟩) R70097
theorem R46743 : Reach 46743 := rs (se 1 (by rfl) ⟨35057, by rfl⟩) R70115
theorem R177815 : Reach 177815 := rs (se 1 (by rfl) ⟨133361, by rfl⟩) R266723
theorem R46763 : Reach 46763 := rs (se 1 (by rfl) ⟨35072, by rfl⟩) R70145
theorem R46775 : Reach 46775 := rs (se 1 (by rfl) ⟨35081, by rfl⟩) R70163
theorem R46795 : Reach 46795 := rs (se 1 (by rfl) ⟨35096, by rfl⟩) R70193
theorem R46807 : Reach 46807 := rs (se 1 (by rfl) ⟨35105, by rfl⟩) R70211
theorem R46827 : Reach 46827 := rs (se 1 (by rfl) ⟨35120, by rfl⟩) R70241
theorem R46839 : Reach 46839 := rs (se 1 (by rfl) ⟨35129, by rfl⟩) R70259
theorem R46859 : Reach 46859 := rs (se 1 (by rfl) ⟨35144, by rfl⟩) R70289
theorem R46871 : Reach 46871 := rs (se 1 (by rfl) ⟨35153, by rfl⟩) R70307
theorem R46891 : Reach 46891 := rs (se 1 (by rfl) ⟨35168, by rfl⟩) R70337
theorem R177965 : Reach 177965 := rs (se 3 (by rfl) ⟨33368, by rfl⟩) R66737
theorem R46903 : Reach 46903 := rs (se 1 (by rfl) ⟨35177, by rfl⟩) R70355
theorem R46923 : Reach 46923 := rs (se 1 (by rfl) ⟨35192, by rfl⟩) R70385
theorem R46935 : Reach 46935 := rs (se 1 (by rfl) ⟨35201, by rfl⟩) R70403
theorem R178013 : Reach 178013 := rs (se 3 (by rfl) ⟨33377, by rfl⟩) R66755
theorem R46955 : Reach 46955 := rs (se 1 (by rfl) ⟨35216, by rfl⟩) R70433
theorem R46967 : Reach 46967 := rs (se 1 (by rfl) ⟨35225, by rfl⟩) R70451
theorem R46987 : Reach 46987 := rs (se 1 (by rfl) ⟨35240, by rfl⟩) R70481
theorem R46999 : Reach 46999 := rs (se 1 (by rfl) ⟨35249, by rfl⟩) R70499
theorem R47019 : Reach 47019 := rs (se 1 (by rfl) ⟨35264, by rfl⟩) R70529
theorem R47031 : Reach 47031 := rs (se 1 (by rfl) ⟨35273, by rfl⟩) R70547
theorem R47051 : Reach 47051 := rs (se 1 (by rfl) ⟨35288, by rfl⟩) R70577
theorem R47063 : Reach 47063 := rs (se 1 (by rfl) ⟨35297, by rfl⟩) R70595
theorem R47083 : Reach 47083 := rs (se 1 (by rfl) ⟨35312, by rfl⟩) R70625
theorem R47095 : Reach 47095 := rs (se 1 (by rfl) ⟨35321, by rfl⟩) R70643
theorem R47115 : Reach 47115 := rs (se 1 (by rfl) ⟨35336, by rfl⟩) R70673
theorem R112691 : Reach 112691 := rs (se 1 (by rfl) ⟨84518, by rfl⟩) R169037
theorem R1882187 : Reach 1882187 := rs (se 1 (by rfl) ⟨1411640, by rfl⟩) R2823281
theorem R47243 : Reach 47243 := rs (se 1 (by rfl) ⟨35432, by rfl⟩) R70865
theorem R178483 : Reach 178483 := rs (se 1 (by rfl) ⟨133862, by rfl⟩) R267725
theorem R112985 : Reach 112985 := rs (se 2 (by rfl) ⟨42369, by rfl⟩) R84739
theorem R47639 : Reach 47639 := rs (se 1 (by rfl) ⟨35729, by rfl⟩) R71459
theorem R80473 : Reach 80473 := rs (se 2 (by rfl) ⟨30177, by rfl⟩) R60355
theorem R670301 : Reach 670301 := rs (se 3 (by rfl) ⟨125681, by rfl⟩) R251363
theorem R342629 : Reach 342629 := rs (se 4 (by rfl) ⟨32121, by rfl⟩) R64243
theorem R735925 : Reach 735925 := rs (se 5 (by rfl) ⟨34496, by rfl⟩) R68993
theorem R146123 : Reach 146123 := rs (se 1 (by rfl) ⟨109592, by rfl⟩) R219185
theorem R146137 : Reach 146137 := rs (se 2 (by rfl) ⟨54801, by rfl⟩) R109603
theorem R211729 : Reach 211729 := rs (se 2 (by rfl) ⟨79398, by rfl⟩) R158797
theorem R375617 : Reach 375617 := rs (se 2 (by rfl) ⟨140856, by rfl⟩) R281713
theorem R146393 : Reach 146393 := rs (se 2 (by rfl) ⟨54897, by rfl⟩) R109795
theorem R343115 : Reach 343115 := rs (se 1 (by rfl) ⟨257336, by rfl⟩) R514673
theorem R48439 : Reach 48439 := rs (se 1 (by rfl) ⟨36329, by rfl⟩) R72659
theorem R48523 : Reach 48523 := rs (se 1 (by rfl) ⟨36392, by rfl⟩) R72785
theorem R4078997 : Reach 4078997 := rs (se 6 (by rfl) ⟨95601, by rfl⟩) R191203
theorem R48631 : Reach 48631 := rs (se 1 (by rfl) ⟨36473, by rfl⟩) R72947
theorem R48695 : Reach 48695 := rs (se 1 (by rfl) ⟨36521, by rfl⟩) R73043
theorem R147095 : Reach 147095 := rs (se 1 (by rfl) ⟨110321, by rfl⟩) R220643
theorem R48811 : Reach 48811 := rs (se 1 (by rfl) ⟨36608, by rfl⟩) R73217
theorem R48919 : Reach 48919 := rs (se 1 (by rfl) ⟨36689, by rfl⟩) R73379
theorem R901043 : Reach 901043 := rs (se 1 (by rfl) ⟨675782, by rfl⟩) R1351565
theorem R49099 : Reach 49099 := rs (se 1 (by rfl) ⟨36824, by rfl⟩) R73649
theorem R114635 : Reach 114635 := rs (se 1 (by rfl) ⟨85976, by rfl⟩) R171953
theorem R49207 : Reach 49207 := rs (se 1 (by rfl) ⟨36905, by rfl⟩) R73811
theorem R147521 : Reach 147521 := rs (se 2 (by rfl) ⟨55320, by rfl⟩) R110641
theorem R49259 : Reach 49259 := rs (se 1 (by rfl) ⟨36944, by rfl⟩) R73889
theorem R82073 : Reach 82073 := rs (se 2 (by rfl) ⟨30777, by rfl⟩) R61555
theorem R147635 : Reach 147635 := rs (se 1 (by rfl) ⟨110726, by rfl⟩) R221453
theorem R49387 : Reach 49387 := rs (se 1 (by rfl) ⟨37040, by rfl⟩) R74081
theorem R49495 : Reach 49495 := rs (se 1 (by rfl) ⟨37121, by rfl⟩) R74243
theorem R147905 : Reach 147905 := rs (se 2 (by rfl) ⟨55464, by rfl⟩) R110929
theorem R49675 : Reach 49675 := rs (se 1 (by rfl) ⟨37256, by rfl⟩) R74513
theorem R49783 : Reach 49783 := rs (se 1 (by rfl) ⟨37337, by rfl⟩) R74675
theorem R705205 : Reach 705205 := rs (se 5 (by rfl) ⟨33056, by rfl⟩) R66113
theorem R443141 : Reach 443141 := rs (se 4 (by rfl) ⟨41544, by rfl⟩) R83089
theorem R82711 : Reach 82711 := rs (se 1 (by rfl) ⟨62033, by rfl⟩) R124067
theorem R49963 : Reach 49963 := rs (se 1 (by rfl) ⟨37472, by rfl⟩) R74945
theorem R50039 : Reach 50039 := rs (se 1 (by rfl) ⟨37529, by rfl⟩) R75059
theorem R50071 : Reach 50071 := rs (se 1 (by rfl) ⟨37553, by rfl⟩) R75107
theorem R115607 : Reach 115607 := rs (se 1 (by rfl) ⟨86705, by rfl⟩) R173411
theorem R213977 : Reach 213977 := rs (se 2 (by rfl) ⟨80241, by rfl⟩) R160483
theorem R148445 : Reach 148445 := rs (se 3 (by rfl) ⟨27833, by rfl⟩) R55667
theorem R50251 : Reach 50251 := rs (se 1 (by rfl) ⟨37688, by rfl⟩) R75377
theorem R50359 : Reach 50359 := rs (se 1 (by rfl) ⟨37769, by rfl⟩) R75539
theorem R50539 : Reach 50539 := rs (se 1 (by rfl) ⟨37904, by rfl⟩) R75809
theorem R50647 : Reach 50647 := rs (se 1 (by rfl) ⟨37985, by rfl⟩) R75971
theorem R83443 : Reach 83443 := rs (se 1 (by rfl) ⟨62582, by rfl⟩) R125165
theorem R247313 : Reach 247313 := rs (se 2 (by rfl) ⟨92742, by rfl⟩) R185485
theorem R50711 : Reach 50711 := rs (se 1 (by rfl) ⟨38033, by rfl⟩) R76067
theorem R116275 : Reach 116275 := rs (se 1 (by rfl) ⟨87206, by rfl⟩) R174413
theorem R50743 : Reach 50743 := rs (se 1 (by rfl) ⟨38057, by rfl⟩) R76115
theorem R83531 : Reach 83531 := rs (se 1 (by rfl) ⟨62648, by rfl⟩) R125297
theorem R83585 : Reach 83585 := rs (se 2 (by rfl) ⟨31344, by rfl⟩) R62689
theorem R50827 : Reach 50827 := rs (se 1 (by rfl) ⟨38120, by rfl⟩) R76241
theorem R312983 : Reach 312983 := rs (se 1 (by rfl) ⟨234737, by rfl⟩) R469475
theorem R116417 : Reach 116417 := rs (se 2 (by rfl) ⟨43656, by rfl⟩) R87313
theorem R50935 : Reach 50935 := rs (se 1 (by rfl) ⟨38201, by rfl⟩) R76403
theorem R247769 : Reach 247769 := rs (se 2 (by rfl) ⟨92913, by rfl⟩) R185827
theorem R51223 : Reach 51223 := rs (se 1 (by rfl) ⟨38417, by rfl⟩) R76835
theorem R84019 : Reach 84019 := rs (se 1 (by rfl) ⟨63014, by rfl⟩) R126029
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R149579 : Reach 149579 := rs (se 1 (by rfl) ⟨112184, by rfl⟩) R224369
theorem R149597 : Reach 149597 := rs (se 3 (by rfl) ⟨28049, by rfl⟩) R56099
theorem R247901 : Reach 247901 := rs (se 3 (by rfl) ⟨46481, by rfl⟩) R92963
theorem R51403 : Reach 51403 := rs (se 1 (by rfl) ⟨38552, by rfl⟩) R77105
theorem R84235 : Reach 84235 := rs (se 1 (by rfl) ⟨63176, by rfl⟩) R126353
theorem R149849 : Reach 149849 := rs (se 2 (by rfl) ⟨56193, by rfl⟩) R112387
theorem R117085 : Reach 117085 := rs (se 3 (by rfl) ⟨21953, by rfl⟩) R43907
theorem R84503 : Reach 84503 := rs (se 1 (by rfl) ⟨63377, by rfl⟩) R126755
theorem R51799 : Reach 51799 := rs (se 1 (by rfl) ⟨38849, by rfl⟩) R77699
theorem R51979 : Reach 51979 := rs (se 1 (by rfl) ⟨38984, by rfl⟩) R77969
theorem R117683 : Reach 117683 := rs (se 1 (by rfl) ⟨88262, by rfl⟩) R176525
theorem R150493 : Reach 150493 := rs (se 3 (by rfl) ⟨28217, by rfl⟩) R56435
theorem R150551 : Reach 150551 := rs (se 1 (by rfl) ⟨112913, by rfl⟩) R225827
theorem R85043 : Reach 85043 := rs (se 1 (by rfl) ⟨63782, by rfl⟩) R127565
theorem R52375 : Reach 52375 := rs (se 1 (by rfl) ⟨39281, by rfl⟩) R78563
theorem R85195 : Reach 85195 := rs (se 1 (by rfl) ⟨63896, by rfl⟩) R127793
theorem R52555 : Reach 52555 := rs (se 1 (by rfl) ⟨39416, by rfl⟩) R78833
theorem R118219 : Reach 118219 := rs (se 1 (by rfl) ⟨88664, by rfl⟩) R177329
theorem R85529 : Reach 85529 := rs (se 2 (by rfl) ⟨32073, by rfl⟩) R64147
theorem R151091 : Reach 151091 := rs (se 1 (by rfl) ⟨113318, by rfl⟩) R226637
theorem R118361 : Reach 118361 := rs (se 2 (by rfl) ⟨44385, by rfl⟩) R88771
theorem R52951 : Reach 52951 := rs (se 1 (by rfl) ⟨39713, by rfl⟩) R79427
theorem R282329 : Reach 282329 := rs (se 2 (by rfl) ⟨105873, by rfl⟩) R211747
theorem R118493 : Reach 118493 := rs (se 3 (by rfl) ⟨22217, by rfl⟩) R44435
theorem R151361 : Reach 151361 := rs (se 2 (by rfl) ⟨56760, by rfl⟩) R113521
theorem R348461 : Reach 348461 := rs (se 3 (by rfl) ⟨65336, by rfl⟩) R130673
theorem R151901 : Reach 151901 := rs (se 3 (by rfl) ⟨28481, by rfl⟩) R56963
theorem R119191 : Reach 119191 := rs (se 1 (by rfl) ⟨89393, by rfl⟩) R178787
theorem R185111 : Reach 185111 := rs (se 1 (by rfl) ⟨138833, by rfl⟩) R277667
theorem R54167 : Reach 54167 := rs (se 1 (by rfl) ⟨40625, by rfl⟩) R81251
theorem R86987 : Reach 86987 := rs (se 1 (by rfl) ⟨65240, by rfl⟩) R130481
theorem R87169 : Reach 87169 := rs (se 2 (by rfl) ⟨32688, by rfl⟩) R65377
theorem R153035 : Reach 153035 := rs (se 1 (by rfl) ⟨114776, by rfl⟩) R229553
theorem R87617 : Reach 87617 := rs (se 2 (by rfl) ⟨32856, by rfl⟩) R65713
theorem R218699 : Reach 218699 := rs (se 1 (by rfl) ⟨164024, by rfl⟩) R328049
theorem R153305 : Reach 153305 := rs (se 2 (by rfl) ⟨57489, by rfl⟩) R114979
theorem R153361 : Reach 153361 := rs (se 2 (by rfl) ⟨57510, by rfl⟩) R115021
theorem R87959 : Reach 87959 := rs (se 1 (by rfl) ⟨65969, by rfl⟩) R131939
theorem R154007 : Reach 154007 := rs (se 1 (by rfl) ⟨115505, by rfl⟩) R231011
theorem R154115 : Reach 154115 := rs (se 1 (by rfl) ⟨115586, by rfl⟩) R231173
theorem R55819 : Reach 55819 := rs (se 1 (by rfl) ⟨41864, by rfl⟩) R83729
theorem R88627 : Reach 88627 := rs (se 1 (by rfl) ⟨66470, by rfl⟩) R132941
theorem R88651 : Reach 88651 := rs (se 1 (by rfl) ⟨66488, by rfl⟩) R132977
theorem R88715 : Reach 88715 := rs (se 1 (by rfl) ⟨66536, by rfl⟩) R133073
theorem R154385 : Reach 154385 := rs (se 2 (by rfl) ⟨57894, by rfl⟩) R115789
theorem R1334069 : Reach 1334069 := rs (se 5 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R187211 : Reach 187211 := rs (se 1 (by rfl) ⟨140408, by rfl⟩) R280817
theorem R88921 : Reach 88921 := rs (se 2 (by rfl) ⟨33345, by rfl⟩) R66691
theorem R154547 : Reach 154547 := rs (se 1 (by rfl) ⟨115910, by rfl⟩) R231821
theorem R89075 : Reach 89075 := rs (se 1 (by rfl) ⟨66806, by rfl⟩) R133613
theorem R285713 : Reach 285713 := rs (se 2 (by rfl) ⟨107142, by rfl⟩) R214285
theorem R89113 : Reach 89113 := rs (se 2 (by rfl) ⟨33417, by rfl⟩) R66835
theorem R154817 : Reach 154817 := rs (se 2 (by rfl) ⟨58056, by rfl⟩) R116113
theorem R253145 : Reach 253145 := rs (se 2 (by rfl) ⟨94929, by rfl⟩) R189859
theorem R154925 : Reach 154925 := rs (se 3 (by rfl) ⟨29048, by rfl⟩) R58097
theorem R220481 : Reach 220481 := rs (se 2 (by rfl) ⟨82680, by rfl⟩) R165361
theorem R875893 : Reach 875893 := rs (se 5 (by rfl) ⟨41057, by rfl⟩) R82115
theorem R56791 : Reach 56791 := rs (se 1 (by rfl) ⟨42593, by rfl⟩) R85187
theorem R155267 : Reach 155267 := rs (se 1 (by rfl) ⟨116450, by rfl⟩) R232901
theorem R155357 : Reach 155357 := rs (se 3 (by rfl) ⟨29129, by rfl⟩) R58259
theorem R516131 : Reach 516131 := rs (se 1 (by rfl) ⟨387098, by rfl⟩) R774197
theorem R352349 : Reach 352349 := rs (se 3 (by rfl) ⟨66065, by rfl⟩) R132131
theorem R188561 : Reach 188561 := rs (se 2 (by rfl) ⟨70710, by rfl⟩) R141421
theorem R57611 : Reach 57611 := rs (se 1 (by rfl) ⟨43208, by rfl⟩) R86417
theorem R286993 : Reach 286993 := rs (se 2 (by rfl) ⟨107622, by rfl⟩) R215245
theorem R155927 : Reach 155927 := rs (se 1 (by rfl) ⟨116945, by rfl⟩) R233891
theorem R680293 : Reach 680293 := rs (se 4 (by rfl) ⟨63777, by rfl⟩) R127555
theorem R156439 : Reach 156439 := rs (se 1 (by rfl) ⟨117329, by rfl⟩) R234659
theorem R254785 : Reach 254785 := rs (se 2 (by rfl) ⟨95544, by rfl⟩) R191089
theorem R156491 : Reach 156491 := rs (se 1 (by rfl) ⟨117368, by rfl⟩) R234737
theorem R58315 : Reach 58315 := rs (se 1 (by rfl) ⟨43736, by rfl⟩) R87473
theorem R2057237 : Reach 2057237 := rs (se 6 (by rfl) ⟨48216, by rfl⟩) R96433
theorem R189485 : Reach 189485 := rs (se 3 (by rfl) ⟨35528, by rfl⟩) R71057
theorem R156761 : Reach 156761 := rs (se 2 (by rfl) ⟨58785, by rfl⟩) R117571
theorem R58583 : Reach 58583 := rs (se 1 (by rfl) ⟨43937, by rfl⟩) R87875
theorem R222425 : Reach 222425 := rs (se 2 (by rfl) ⟨83409, by rfl⟩) R166819
theorem R124211 : Reach 124211 := rs (se 1 (by rfl) ⟨93158, by rfl⟩) R186317
theorem R124249 : Reach 124249 := rs (se 2 (by rfl) ⟨46593, by rfl⟩) R93187
theorem R157457 : Reach 157457 := rs (se 2 (by rfl) ⟨59046, by rfl⟩) R118093
theorem R157463 : Reach 157463 := rs (se 1 (by rfl) ⟨118097, by rfl⟩) R236195
theorem R157571 : Reach 157571 := rs (se 1 (by rfl) ⟨118178, by rfl⟩) R236357
theorem R59287 : Reach 59287 := rs (se 1 (by rfl) ⟨44465, by rfl⟩) R88931
theorem R124865 : Reach 124865 := rs (se 2 (by rfl) ⟨46824, by rfl⟩) R93649
theorem R157643 : Reach 157643 := rs (se 1 (by rfl) ⟨118232, by rfl⟩) R236465
theorem R92299 : Reach 92299 := rs (se 1 (by rfl) ⟨69224, by rfl⟩) R138449
theorem R157841 : Reach 157841 := rs (se 2 (by rfl) ⟨59190, by rfl⟩) R118381
theorem R59545 : Reach 59545 := rs (se 2 (by rfl) ⟨22329, by rfl⟩) R44659
theorem R157889 : Reach 157889 := rs (se 2 (by rfl) ⟨59208, by rfl⟩) R118417
theorem R158003 : Reach 158003 := rs (se 1 (by rfl) ⟨118502, by rfl⟩) R237005
theorem R747953 : Reach 747953 := rs (se 2 (by rfl) ⟨280482, by rfl⟩) R560965
theorem R223667 : Reach 223667 := rs (se 1 (by rfl) ⟨167750, by rfl⟩) R335501
theorem R190937 : Reach 190937 := rs (se 2 (by rfl) ⟨71601, by rfl⟩) R143203
theorem R158273 : Reach 158273 := rs (se 2 (by rfl) ⟨59352, by rfl⟩) R118705
theorem R158381 : Reach 158381 := rs (se 3 (by rfl) ⟨29696, by rfl⟩) R59393
theorem R224045 : Reach 224045 := rs (se 3 (by rfl) ⟨42008, by rfl⟩) R84017
theorem R322483 : Reach 322483 := rs (se 1 (by rfl) ⟨241862, by rfl⟩) R483725
theorem R93145 : Reach 93145 := rs (se 2 (by rfl) ⟨34929, by rfl⟩) R69859
theorem R158813 : Reach 158813 := rs (se 3 (by rfl) ⟨29777, by rfl⟩) R59555
theorem R617827 : Reach 617827 := rs (se 1 (by rfl) ⟨463370, by rfl⟩) R926741
theorem R388739 : Reach 388739 := rs (se 1 (by rfl) ⟨291554, by rfl⟩) R583109
theorem R93889 : Reach 93889 := rs (se 2 (by rfl) ⟨35208, by rfl⟩) R70417
theorem R159533 : Reach 159533 := rs (se 3 (by rfl) ⟨29912, by rfl⟩) R59825
theorem R192449 : Reach 192449 := rs (se 2 (by rfl) ⟨72168, by rfl⟩) R144337
theorem R126937 : Reach 126937 := rs (se 2 (by rfl) ⟨47601, by rfl⟩) R95203
theorem R192577 : Reach 192577 := rs (se 2 (by rfl) ⟨72216, by rfl⟩) R144433
theorem R159833 : Reach 159833 := rs (se 2 (by rfl) ⟨59937, by rfl⟩) R119875
theorem R258227 : Reach 258227 := rs (se 1 (by rfl) ⟨193670, by rfl⟩) R387341
theorem R94451 : Reach 94451 := rs (se 1 (by rfl) ⟨70838, by rfl⟩) R141677
theorem R127325 : Reach 127325 := rs (se 3 (by rfl) ⟨23873, by rfl⟩) R47747
theorem R2716253 : Reach 2716253 := rs (se 3 (by rfl) ⟨509297, by rfl⟩) R1018595
theorem R193175 : Reach 193175 := rs (se 1 (by rfl) ⟨144881, by rfl⟩) R289763
theorem R160643 : Reach 160643 := rs (se 1 (by rfl) ⟨120482, by rfl⟩) R240965
theorem R488369 : Reach 488369 := rs (se 2 (by rfl) ⟨183138, by rfl⟩) R366277
theorem R62489 : Reach 62489 := rs (se 2 (by rfl) ⟨23433, by rfl⟩) R46867
theorem R95435 : Reach 95435 := rs (se 1 (by rfl) ⟨71576, by rfl⟩) R143153
theorem R161041 : Reach 161041 := rs (se 2 (by rfl) ⟨60390, by rfl⟩) R120781
theorem R161117 : Reach 161117 := rs (se 3 (by rfl) ⟨30209, by rfl⟩) R60419
theorem R259685 : Reach 259685 := rs (se 4 (by rfl) ⟨24345, by rfl⟩) R48691
theorem R63127 : Reach 63127 := rs (se 1 (by rfl) ⟨47345, by rfl⟩) R94691
theorem R96023 : Reach 96023 := rs (se 1 (by rfl) ⟨72017, by rfl⟩) R144035
theorem R194507 : Reach 194507 := rs (se 1 (by rfl) ⟨145880, by rfl⟩) R291761
theorem R358361 : Reach 358361 := rs (se 2 (by rfl) ⟨134385, by rfl⟩) R268771
theorem R96331 : Reach 96331 := rs (se 1 (by rfl) ⟨72248, by rfl⟩) R144497
theorem R162071 : Reach 162071 := rs (se 1 (by rfl) ⟨121553, by rfl⟩) R243107
theorem R227659 : Reach 227659 := rs (se 1 (by rfl) ⟨170744, by rfl⟩) R341489
theorem R293195 : Reach 293195 := rs (se 1 (by rfl) ⟨219896, by rfl⟩) R439793
theorem R63833 : Reach 63833 := rs (se 2 (by rfl) ⟨23937, by rfl⟩) R47875
theorem R63947 : Reach 63947 := rs (se 1 (by rfl) ⟨47960, by rfl⟩) R95921
theorem R391715 : Reach 391715 := rs (se 1 (by rfl) ⟨293786, by rfl⟩) R587573
theorem R227933 : Reach 227933 := rs (se 3 (by rfl) ⟨42737, by rfl⟩) R85475
theorem R326501 : Reach 326501 := rs (se 4 (by rfl) ⟨30609, by rfl⟩) R61219
theorem R97163 : Reach 97163 := rs (se 1 (by rfl) ⟨72872, by rfl⟩) R145745
theorem R97217 : Reach 97217 := rs (se 2 (by rfl) ⟨36456, by rfl⟩) R72913
theorem R64471 : Reach 64471 := rs (se 1 (by rfl) ⟨48353, by rfl⟩) R96707
theorem R195635 : Reach 195635 := rs (se 1 (by rfl) ⟨146726, by rfl⟩) R293453
theorem R97433 : Reach 97433 := rs (se 2 (by rfl) ⟨36537, by rfl⟩) R73075
theorem R130241 : Reach 130241 := rs (se 2 (by rfl) ⟨48840, by rfl⟩) R97681
theorem R64715 : Reach 64715 := rs (se 1 (by rfl) ⟨48536, by rfl⟩) R97073
theorem R64727 : Reach 64727 := rs (se 1 (by rfl) ⟨48545, by rfl⟩) R97091
theorem R97523 : Reach 97523 := rs (se 1 (by rfl) ⟨73142, by rfl⟩) R146285
theorem R97559 : Reach 97559 := rs (se 1 (by rfl) ⟨73169, by rfl⟩) R146339
theorem R64793 : Reach 64793 := rs (se 2 (by rfl) ⟨24297, by rfl⟩) R48595
theorem R97561 : Reach 97561 := rs (se 2 (by rfl) ⟨36585, by rfl⟩) R73171
theorem R130355 : Reach 130355 := rs (se 1 (by rfl) ⟨97766, by rfl⟩) R195533
theorem R64907 : Reach 64907 := rs (se 1 (by rfl) ⟨48680, by rfl⟩) R97361
theorem R64919 : Reach 64919 := rs (se 1 (by rfl) ⟨48689, by rfl⟩) R97379
theorem R97739 : Reach 97739 := rs (se 1 (by rfl) ⟨73304, by rfl⟩) R146609
theorem R64985 : Reach 64985 := rs (se 2 (by rfl) ⟨24369, by rfl⟩) R48739
theorem R97793 : Reach 97793 := rs (se 2 (by rfl) ⟨36672, by rfl⟩) R73345
theorem R65099 : Reach 65099 := rs (se 1 (by rfl) ⟨48824, by rfl⟩) R97649
theorem R65111 : Reach 65111 := rs (se 1 (by rfl) ⟨48833, by rfl⟩) R97667
theorem R65177 : Reach 65177 := rs (se 2 (by rfl) ⟨24441, by rfl⟩) R48883
theorem R98009 : Reach 98009 := rs (se 2 (by rfl) ⟨36753, by rfl⟩) R73507
theorem R65291 : Reach 65291 := rs (se 1 (by rfl) ⟨48968, by rfl⟩) R97937
theorem R65303 : Reach 65303 := rs (se 1 (by rfl) ⟨48977, by rfl⟩) R97955
theorem R98099 : Reach 98099 := rs (se 1 (by rfl) ⟨73574, by rfl⟩) R147149
theorem R556865 : Reach 556865 := rs (se 2 (by rfl) ⟨208824, by rfl⟩) R417649
theorem R98135 : Reach 98135 := rs (se 1 (by rfl) ⟨73601, by rfl⟩) R147203
theorem R65369 : Reach 65369 := rs (se 2 (by rfl) ⟨24513, by rfl⟩) R49027
theorem R294835 : Reach 294835 := rs (se 1 (by rfl) ⟨221126, by rfl⟩) R442253
theorem R65483 : Reach 65483 := rs (se 1 (by rfl) ⟨49112, by rfl⟩) R98225
theorem R65495 : Reach 65495 := rs (se 1 (by rfl) ⟨49121, by rfl⟩) R98243
theorem R65543 : Reach 65543 := rs (se 1 (by rfl) ⟨49157, by rfl⟩) R98315
theorem R65579 : Reach 65579 := rs (se 1 (by rfl) ⟨49184, by rfl⟩) R98369
theorem R98347 : Reach 98347 := rs (se 1 (by rfl) ⟨73760, by rfl⟩) R147521
theorem R65609 : Reach 65609 := rs (se 2 (by rfl) ⟨24603, by rfl⟩) R49207
theorem R98423 : Reach 98423 := rs (se 1 (by rfl) ⟨73817, by rfl⟩) R147635
theorem R65723 : Reach 65723 := rs (se 1 (by rfl) ⟨49292, by rfl⟩) R98585
theorem R426221 : Reach 426221 := rs (se 3 (by rfl) ⟨79916, by rfl⟩) R159833
theorem R65783 : Reach 65783 := rs (se 1 (by rfl) ⟨49337, by rfl⟩) R98675
theorem R65807 : Reach 65807 := rs (se 1 (by rfl) ⟨49355, by rfl⟩) R98711
theorem R131357 : Reach 131357 := rs (se 3 (by rfl) ⟨24629, by rfl⟩) R49259
theorem R98603 : Reach 98603 := rs (se 1 (by rfl) ⟨73952, by rfl⟩) R147905
theorem R65849 : Reach 65849 := rs (se 2 (by rfl) ⟨24693, by rfl⟩) R49387
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R65927 : Reach 65927 := rs (se 1 (by rfl) ⟨49445, by rfl⟩) R98891
theorem R65963 : Reach 65963 := rs (se 1 (by rfl) ⟨49472, by rfl⟩) R98945
theorem R65993 : Reach 65993 := rs (se 2 (by rfl) ⟨24747, by rfl⟩) R49495
theorem R295427 : Reach 295427 := rs (se 1 (by rfl) ⟨221570, by rfl⟩) R443141
theorem R66107 : Reach 66107 := rs (se 1 (by rfl) ⟨49580, by rfl⟩) R99161
theorem R131699 : Reach 131699 := rs (se 1 (by rfl) ⟨98774, by rfl⟩) R197549
theorem R66167 : Reach 66167 := rs (se 1 (by rfl) ⟨49625, by rfl⟩) R99251
theorem R66191 : Reach 66191 := rs (se 1 (by rfl) ⟨49643, by rfl⟩) R99287
theorem R98963 : Reach 98963 := rs (se 1 (by rfl) ⟨74222, by rfl⟩) R148445
theorem R66233 : Reach 66233 := rs (se 2 (by rfl) ⟨24837, by rfl⟩) R49675
theorem R99017 : Reach 99017 := rs (se 2 (by rfl) ⟨37131, by rfl⟩) R74263
theorem R66311 : Reach 66311 := rs (se 1 (by rfl) ⟨49733, by rfl⟩) R99467
theorem R66347 : Reach 66347 := rs (se 1 (by rfl) ⟨49760, by rfl⟩) R99521
theorem R66377 : Reach 66377 := rs (se 2 (by rfl) ⟨24891, by rfl⟩) R49783
theorem R66491 : Reach 66491 := rs (se 1 (by rfl) ⟨49868, by rfl⟩) R99737
theorem R66551 : Reach 66551 := rs (se 1 (by rfl) ⟨49913, by rfl⟩) R99827
theorem R164875 : Reach 164875 := rs (se 1 (by rfl) ⟨123656, by rfl⟩) R247313
theorem R66575 : Reach 66575 := rs (se 1 (by rfl) ⟨49931, by rfl⟩) R99863
theorem R66617 : Reach 66617 := rs (se 2 (by rfl) ⟨24981, by rfl⟩) R49963
theorem R132155 : Reach 132155 := rs (se 1 (by rfl) ⟨99116, by rfl⟩) R198233
theorem R66695 : Reach 66695 := rs (se 1 (by rfl) ⟨50021, by rfl⟩) R100043
theorem R66731 : Reach 66731 := rs (se 1 (by rfl) ⟨50048, by rfl⟩) R100097
theorem R66761 : Reach 66761 := rs (se 2 (by rfl) ⟨25035, by rfl⟩) R50071
theorem R165179 : Reach 165179 := rs (se 1 (by rfl) ⟨123884, by rfl⟩) R247769
theorem R66875 : Reach 66875 := rs (se 1 (by rfl) ⟨50156, by rfl⟩) R100313
theorem R66935 : Reach 66935 := rs (se 1 (by rfl) ⟨50201, by rfl⟩) R100403
theorem R99719 : Reach 99719 := rs (se 1 (by rfl) ⟨74789, by rfl⟩) R149579
theorem R66959 : Reach 66959 := rs (se 1 (by rfl) ⟨50219, by rfl⟩) R100439
theorem R99731 : Reach 99731 := rs (se 1 (by rfl) ⟨74798, by rfl⟩) R149597
theorem R67001 : Reach 67001 := rs (se 2 (by rfl) ⟨25125, by rfl⟩) R50251
theorem R67063 : Reach 67063 := rs (se 1 (by rfl) ⟨50297, by rfl⟩) R100595
theorem R67079 : Reach 67079 := rs (se 1 (by rfl) ⟨50309, by rfl⟩) R100619
theorem R67115 : Reach 67115 := rs (se 1 (by rfl) ⟨50336, by rfl⟩) R100673
theorem R99899 : Reach 99899 := rs (se 1 (by rfl) ⟨74924, by rfl⟩) R149849
theorem R67145 : Reach 67145 := rs (se 2 (by rfl) ⟨25179, by rfl⟩) R50359
theorem R100025 : Reach 100025 := rs (se 2 (by rfl) ⟨37509, by rfl⟩) R75019
theorem R67259 : Reach 67259 := rs (se 1 (by rfl) ⟨50444, by rfl⟩) R100889
theorem R67319 : Reach 67319 := rs (se 1 (by rfl) ⟨50489, by rfl⟩) R100979
theorem R67343 : Reach 67343 := rs (se 1 (by rfl) ⟨50507, by rfl⟩) R101015
theorem R165665 : Reach 165665 := rs (se 2 (by rfl) ⟨62124, by rfl⟩) R124249
theorem R67385 : Reach 67385 := rs (se 2 (by rfl) ⟨25269, by rfl⟩) R50539
theorem R67463 : Reach 67463 := rs (se 1 (by rfl) ⟨50597, by rfl⟩) R101195
theorem R67499 : Reach 67499 := rs (se 1 (by rfl) ⟨50624, by rfl⟩) R101249
theorem R133049 : Reach 133049 := rs (se 2 (by rfl) ⟨49893, by rfl⟩) R99787
theorem R67529 : Reach 67529 := rs (se 2 (by rfl) ⟨25323, by rfl⟩) R50647
theorem R100367 : Reach 100367 := rs (se 1 (by rfl) ⟨75275, by rfl⟩) R150551
theorem R100385 : Reach 100385 := rs (se 2 (by rfl) ⟨37644, by rfl⟩) R75289
theorem R67643 : Reach 67643 := rs (se 1 (by rfl) ⟨50732, by rfl⟩) R101465
theorem R67657 : Reach 67657 := rs (se 2 (by rfl) ⟨25371, by rfl⟩) R50743
theorem R67703 : Reach 67703 := rs (se 1 (by rfl) ⟨50777, by rfl⟩) R101555
theorem R67727 : Reach 67727 := rs (se 1 (by rfl) ⟨50795, by rfl⟩) R101591
theorem R67769 : Reach 67769 := rs (se 2 (by rfl) ⟨25413, by rfl⟩) R50827
theorem R67847 : Reach 67847 := rs (se 1 (by rfl) ⟨50885, by rfl⟩) R101771
theorem R67883 : Reach 67883 := rs (se 1 (by rfl) ⟨50912, by rfl⟩) R101825
theorem R67913 : Reach 67913 := rs (se 2 (by rfl) ⟨25467, by rfl⟩) R50935
theorem R100727 : Reach 100727 := rs (se 1 (by rfl) ⟨75545, by rfl⟩) R151091
theorem R68027 : Reach 68027 := rs (se 1 (by rfl) ⟨51020, by rfl⟩) R102041
theorem R68087 : Reach 68087 := rs (se 1 (by rfl) ⟨51065, by rfl⟩) R102131
theorem R68111 : Reach 68111 := rs (se 1 (by rfl) ⟨51083, by rfl⟩) R102167
theorem R100907 : Reach 100907 := rs (se 1 (by rfl) ⟨75680, by rfl⟩) R151361
theorem R68231 : Reach 68231 := rs (se 1 (by rfl) ⟨51173, by rfl⟩) R102347
theorem R68297 : Reach 68297 := rs (se 2 (by rfl) ⟨25611, by rfl⟩) R51223
theorem R166637 : Reach 166637 := rs (se 3 (by rfl) ⟨31244, by rfl⟩) R62489
theorem R68411 : Reach 68411 := rs (se 1 (by rfl) ⟨51308, by rfl⟩) R102617
theorem R232307 : Reach 232307 := rs (se 1 (by rfl) ⟨174230, by rfl⟩) R348461
theorem R68471 : Reach 68471 := rs (se 1 (by rfl) ⟨51353, by rfl⟩) R102707
theorem R101267 : Reach 101267 := rs (se 1 (by rfl) ⟨75950, by rfl⟩) R151901
theorem R68537 : Reach 68537 := rs (se 2 (by rfl) ⟨25701, by rfl⟩) R51403
theorem R101321 : Reach 101321 := rs (se 2 (by rfl) ⟨37995, by rfl⟩) R75991
theorem R68651 : Reach 68651 := rs (se 1 (by rfl) ⟨51488, by rfl⟩) R102977
theorem R68879 : Reach 68879 := rs (se 1 (by rfl) ⟨51659, by rfl⟩) R103319
theorem R232793 : Reach 232793 := rs (se 2 (by rfl) ⟨87297, by rfl⟩) R174595
theorem R68999 : Reach 68999 := rs (se 1 (by rfl) ⟨51749, by rfl⟩) R103499
theorem R69065 : Reach 69065 := rs (se 2 (by rfl) ⟨25899, by rfl⟩) R51799
theorem R331229 : Reach 331229 := rs (se 3 (by rfl) ⟨62105, by rfl⟩) R124211
theorem R69179 : Reach 69179 := rs (se 1 (by rfl) ⟨51884, by rfl⟩) R103769
theorem R527939 : Reach 527939 := rs (se 1 (by rfl) ⟨395954, by rfl⟩) R791909
theorem R69239 : Reach 69239 := rs (se 1 (by rfl) ⟨51929, by rfl⟩) R103859
theorem R102023 : Reach 102023 := rs (se 1 (by rfl) ⟨76517, by rfl⟩) R153035
theorem R69305 : Reach 69305 := rs (se 2 (by rfl) ⟨25989, by rfl⟩) R51979
theorem R69419 : Reach 69419 := rs (se 1 (by rfl) ⟨52064, by rfl⟩) R104129
theorem R102203 : Reach 102203 := rs (se 1 (by rfl) ⟨76652, by rfl⟩) R153305
theorem R135047 : Reach 135047 := rs (se 1 (by rfl) ⟨101285, by rfl⟩) R202571
theorem R429977 : Reach 429977 := rs (se 2 (by rfl) ⟨161241, by rfl⟩) R322483
theorem R102329 : Reach 102329 := rs (se 2 (by rfl) ⟨38373, by rfl⟩) R76747
theorem R200657 : Reach 200657 := rs (se 2 (by rfl) ⟨75246, by rfl⟩) R150493
theorem R102401 : Reach 102401 := rs (se 2 (by rfl) ⟨38400, by rfl⟩) R76801
theorem R69647 : Reach 69647 := rs (se 1 (by rfl) ⟨52235, by rfl⟩) R104471
theorem R69767 : Reach 69767 := rs (se 1 (by rfl) ⟨52325, by rfl⟩) R104651
theorem R69833 : Reach 69833 := rs (se 2 (by rfl) ⟨26187, by rfl⟩) R52375
theorem R102671 : Reach 102671 := rs (se 1 (by rfl) ⟨77003, by rfl⟩) R154007
theorem R102689 : Reach 102689 := rs (se 2 (by rfl) ⟨38508, by rfl⟩) R77017
theorem R233765 : Reach 233765 := rs (se 4 (by rfl) ⟨21915, by rfl⟩) R43831
theorem R69947 : Reach 69947 := rs (se 1 (by rfl) ⟨52460, by rfl⟩) R104921
theorem R102743 : Reach 102743 := rs (se 1 (by rfl) ⟨77057, by rfl⟩) R154115
theorem R70007 : Reach 70007 := rs (se 1 (by rfl) ⟨52505, by rfl⟩) R105011
theorem R233873 : Reach 233873 := rs (se 2 (by rfl) ⟨87702, by rfl⟩) R175405
theorem R70073 : Reach 70073 := rs (se 2 (by rfl) ⟨26277, by rfl⟩) R52555
theorem R823769 : Reach 823769 := rs (se 2 (by rfl) ⟨308913, by rfl⟩) R617827
theorem R102923 : Reach 102923 := rs (se 1 (by rfl) ⟨77192, by rfl⟩) R154385
theorem R889379 : Reach 889379 := rs (se 1 (by rfl) ⟨667034, by rfl⟩) R1334069
theorem R70187 : Reach 70187 := rs (se 1 (by rfl) ⟨52640, by rfl⟩) R105281
theorem R103031 : Reach 103031 := rs (se 1 (by rfl) ⟨77273, by rfl⟩) R154547
theorem R70415 : Reach 70415 := rs (se 1 (by rfl) ⟨52811, by rfl⟩) R105623
theorem R103211 : Reach 103211 := rs (se 1 (by rfl) ⟨77408, by rfl⟩) R154817
theorem R168763 : Reach 168763 := rs (se 1 (by rfl) ⟨126572, by rfl⟩) R253145
theorem R398195 : Reach 398195 := rs (se 1 (by rfl) ⟨298646, by rfl⟩) R597293
theorem R103283 : Reach 103283 := rs (se 1 (by rfl) ⟨77462, by rfl⟩) R154925
theorem R70535 : Reach 70535 := rs (se 1 (by rfl) ⟨52901, by rfl⟩) R105803
theorem R70601 : Reach 70601 := rs (se 2 (by rfl) ⟨26475, by rfl⟩) R52951
theorem R103511 : Reach 103511 := rs (se 1 (by rfl) ⟨77633, by rfl⟩) R155267
theorem R103571 : Reach 103571 := rs (se 1 (by rfl) ⟨77678, by rfl⟩) R155357
theorem R103625 : Reach 103625 := rs (se 2 (by rfl) ⟨38859, by rfl⟩) R77719
theorem R169249 : Reach 169249 := rs (se 2 (by rfl) ⟨63468, by rfl⟩) R126937
theorem R234899 : Reach 234899 := rs (se 1 (by rfl) ⟨176174, by rfl⟩) R352349
theorem R103951 : Reach 103951 := rs (se 1 (by rfl) ⟨77963, by rfl⟩) R155927
theorem R661069 : Reach 661069 := rs (se 3 (by rfl) ⟨123950, by rfl⟩) R247901
theorem R104327 : Reach 104327 := rs (se 1 (by rfl) ⟨78245, by rfl⟩) R156491
theorem R104345 : Reach 104345 := rs (se 2 (by rfl) ⟨39129, by rfl⟩) R78259
theorem R71723 : Reach 71723 := rs (se 1 (by rfl) ⟨53792, by rfl⟩) R107585
theorem R104507 : Reach 104507 := rs (se 1 (by rfl) ⟨78380, by rfl⟩) R156761
theorem R137303 : Reach 137303 := rs (se 1 (by rfl) ⟨102977, by rfl⟩) R205955
theorem R104633 : Reach 104633 := rs (se 2 (by rfl) ⟨39237, by rfl⟩) R78475
theorem R170221 : Reach 170221 := rs (se 3 (by rfl) ⟨31916, by rfl⟩) R63833
theorem R104705 : Reach 104705 := rs (se 2 (by rfl) ⟨39264, by rfl⟩) R78529
theorem R104971 : Reach 104971 := rs (se 1 (by rfl) ⟨78728, by rfl⟩) R157457
theorem R104975 : Reach 104975 := rs (se 1 (by rfl) ⟨78731, by rfl⟩) R157463
theorem R170525 : Reach 170525 := rs (se 3 (by rfl) ⟨31973, by rfl⟩) R63947
theorem R203293 : Reach 203293 := rs (se 3 (by rfl) ⟨38117, by rfl⟩) R76235
theorem R104993 : Reach 104993 := rs (se 2 (by rfl) ⟨39372, by rfl⟩) R78745
theorem R105047 : Reach 105047 := rs (se 1 (by rfl) ⟨78785, by rfl⟩) R157571
theorem R105095 : Reach 105095 := rs (se 1 (by rfl) ⟨78821, by rfl⟩) R157643
theorem R105227 : Reach 105227 := rs (se 1 (by rfl) ⟨78920, by rfl⟩) R157841
theorem R105259 : Reach 105259 := rs (se 1 (by rfl) ⟨78944, by rfl⟩) R157889
theorem R105335 : Reach 105335 := rs (se 1 (by rfl) ⟨79001, by rfl⟩) R158003
theorem R498635 : Reach 498635 := rs (se 1 (by rfl) ⟨373976, by rfl⟩) R747953
theorem R269335 : Reach 269335 := rs (se 1 (by rfl) ⟨202001, by rfl⟩) R404003
theorem R236573 : Reach 236573 := rs (se 3 (by rfl) ⟨44357, by rfl⟩) R88715
theorem R105515 : Reach 105515 := rs (se 1 (by rfl) ⟨79136, by rfl⟩) R158273
theorem R105587 : Reach 105587 := rs (se 1 (by rfl) ⟨79190, by rfl⟩) R158381
theorem R72839 : Reach 72839 := rs (se 1 (by rfl) ⟨54629, by rfl⟩) R109259
theorem R105875 : Reach 105875 := rs (se 1 (by rfl) ⟨79406, by rfl⟩) R158813
theorem R105929 : Reach 105929 := rs (se 2 (by rfl) ⟨39723, by rfl⟩) R79447
theorem R466397 : Reach 466397 := rs (se 3 (by rfl) ⟨87449, by rfl⟩) R174899
theorem R1121795 : Reach 1121795 := rs (se 1 (by rfl) ⟨841346, by rfl⟩) R1682693
theorem R499229 : Reach 499229 := rs (se 3 (by rfl) ⟨93605, by rfl⟩) R187211
theorem R204481 : Reach 204481 := rs (se 2 (by rfl) ⟨76680, by rfl⟩) R153361
theorem R73487 : Reach 73487 := rs (se 1 (by rfl) ⟨55115, by rfl⟩) R110231
theorem R106355 : Reach 106355 := rs (se 1 (by rfl) ⟨79766, by rfl⟩) R159533
theorem R172151 : Reach 172151 := rs (se 1 (by rfl) ⟨129113, by rfl⟩) R258227
theorem R74027 : Reach 74027 := rs (se 1 (by rfl) ⟨55520, by rfl⟩) R111041
theorem R74119 : Reach 74119 := rs (se 1 (by rfl) ⟨55589, by rfl⟩) R111179
theorem R1810835 : Reach 1810835 := rs (se 1 (by rfl) ⟨1358126, by rfl⟩) R2716253
theorem R237977 : Reach 237977 := rs (se 2 (by rfl) ⟨89241, by rfl⟩) R178483
theorem R303545 : Reach 303545 := rs (se 2 (by rfl) ⟨113829, by rfl⟩) R227659
theorem R74299 : Reach 74299 := rs (se 1 (by rfl) ⟨55724, by rfl⟩) R111449
theorem R107095 : Reach 107095 := rs (se 1 (by rfl) ⟨80321, by rfl⟩) R160643
theorem R74425 : Reach 74425 := rs (se 2 (by rfl) ⟨27909, by rfl⟩) R55819
theorem R402149 : Reach 402149 := rs (se 4 (by rfl) ⟨37701, by rfl⟩) R75403
theorem R533263 : Reach 533263 := rs (se 1 (by rfl) ⟨399947, by rfl⟩) R799895
theorem R107297 : Reach 107297 := rs (se 2 (by rfl) ⟨40236, by rfl⟩) R80473
theorem R107411 : Reach 107411 := rs (se 1 (by rfl) ⟨80558, by rfl⟩) R161117
theorem R500741 : Reach 500741 := rs (se 4 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R74767 : Reach 74767 := rs (se 1 (by rfl) ⟨56075, by rfl⟩) R112151
theorem R173123 : Reach 173123 := rs (se 1 (by rfl) ⟨129842, by rfl⟩) R259685
theorem R533749 : Reach 533749 := rs (se 5 (by rfl) ⟨25019, by rfl⟩) R50039
theorem R238907 : Reach 238907 := rs (se 1 (by rfl) ⟨179180, by rfl⟩) R358361
theorem R75127 : Reach 75127 := rs (se 1 (by rfl) ⟨56345, by rfl⟩) R112691
theorem R1254791 : Reach 1254791 := rs (se 1 (by rfl) ⟨941093, by rfl⟩) R1882187
theorem R108047 : Reach 108047 := rs (se 1 (by rfl) ⟨81035, by rfl⟩) R162071
theorem R75323 : Reach 75323 := rs (se 1 (by rfl) ⟨56492, by rfl⟩) R112985
theorem R75721 : Reach 75721 := rs (se 2 (by rfl) ⟨28395, by rfl⟩) R56791
theorem R174109 : Reach 174109 := rs (se 3 (by rfl) ⟨32645, by rfl⟩) R65291
theorem R43143 : Reach 43143 := rs (se 1 (by rfl) ⟨32357, by rfl⟩) R64715
theorem R43151 : Reach 43151 := rs (se 1 (by rfl) ⟨32363, by rfl⟩) R64727
theorem R43195 : Reach 43195 := rs (se 1 (by rfl) ⟨32396, by rfl⟩) R64793
theorem R43271 : Reach 43271 := rs (se 1 (by rfl) ⟨32453, by rfl⟩) R64907
theorem R43279 : Reach 43279 := rs (se 1 (by rfl) ⟨32459, by rfl⟩) R64919
theorem R141601 : Reach 141601 := rs (se 2 (by rfl) ⟨53100, by rfl⟩) R106201
theorem R43323 : Reach 43323 := rs (se 1 (by rfl) ⟨32492, by rfl⟩) R64985
theorem R43399 : Reach 43399 := rs (se 1 (by rfl) ⟨32549, by rfl⟩) R65099
theorem R43407 : Reach 43407 := rs (se 1 (by rfl) ⟨32555, by rfl⟩) R65111
theorem R43451 : Reach 43451 := rs (se 1 (by rfl) ⟨32588, by rfl⟩) R65177
theorem R43527 : Reach 43527 := rs (se 1 (by rfl) ⟨32645, by rfl⟩) R65291
theorem R43535 : Reach 43535 := rs (se 1 (by rfl) ⟨32651, by rfl⟩) R65303
theorem R371243 : Reach 371243 := rs (se 1 (by rfl) ⟨278432, by rfl⟩) R556865
theorem R43579 : Reach 43579 := rs (se 1 (by rfl) ⟨32684, by rfl⟩) R65369
theorem R600695 : Reach 600695 := rs (se 1 (by rfl) ⟨450521, by rfl⟩) R901043
theorem R43655 : Reach 43655 := rs (se 1 (by rfl) ⟨32741, by rfl⟩) R65483
theorem R76423 : Reach 76423 := rs (se 1 (by rfl) ⟨57317, by rfl⟩) R114635
theorem R43663 : Reach 43663 := rs (se 1 (by rfl) ⟨32747, by rfl⟩) R65495
theorem R43707 : Reach 43707 := rs (se 1 (by rfl) ⟨32780, by rfl⟩) R65561
theorem R43783 : Reach 43783 := rs (se 1 (by rfl) ⟨32837, by rfl⟩) R65675
theorem R43791 : Reach 43791 := rs (se 1 (by rfl) ⟨32843, by rfl⟩) R65687
theorem R43835 : Reach 43835 := rs (se 1 (by rfl) ⟨32876, by rfl⟩) R65753
theorem R43911 : Reach 43911 := rs (se 1 (by rfl) ⟨32933, by rfl⟩) R65867
theorem R43919 : Reach 43919 := rs (se 1 (by rfl) ⟨32939, by rfl⟩) R65879
theorem R43963 : Reach 43963 := rs (se 1 (by rfl) ⟨32972, by rfl⟩) R65945
theorem R44039 : Reach 44039 := rs (se 1 (by rfl) ⟨33029, by rfl⟩) R66059
theorem R109583 : Reach 109583 := rs (se 1 (by rfl) ⟨82187, by rfl⟩) R164375
theorem R44047 : Reach 44047 := rs (se 1 (by rfl) ⟨33035, by rfl⟩) R66071
theorem R371735 : Reach 371735 := rs (se 1 (by rfl) ⟨278801, by rfl⟩) R557603
theorem R44091 : Reach 44091 := rs (se 1 (by rfl) ⟨33068, by rfl⟩) R66137
theorem R44167 : Reach 44167 := rs (se 1 (by rfl) ⟨33125, by rfl⟩) R66251
theorem R44175 : Reach 44175 := rs (se 1 (by rfl) ⟨33131, by rfl⟩) R66263
theorem R44219 : Reach 44219 := rs (se 1 (by rfl) ⟨33164, by rfl⟩) R66329
theorem R44295 : Reach 44295 := rs (se 1 (by rfl) ⟨33221, by rfl⟩) R66443
theorem R44303 : Reach 44303 := rs (se 1 (by rfl) ⟨33227, by rfl⟩) R66455
theorem R77071 : Reach 77071 := rs (se 1 (by rfl) ⟨57803, by rfl⟩) R115607
theorem R44347 : Reach 44347 := rs (se 1 (by rfl) ⟨33260, by rfl⟩) R66521
theorem R142651 : Reach 142651 := rs (se 1 (by rfl) ⟨106988, by rfl⟩) R213977
theorem R44423 : Reach 44423 := rs (se 1 (by rfl) ⟨33317, by rfl⟩) R66635
theorem R44431 : Reach 44431 := rs (se 1 (by rfl) ⟨33323, by rfl⟩) R66647
theorem R44475 : Reach 44475 := rs (se 1 (by rfl) ⟨33356, by rfl⟩) R66713
theorem R44551 : Reach 44551 := rs (se 1 (by rfl) ⟨33413, by rfl⟩) R66827
theorem R44559 : Reach 44559 := rs (se 1 (by rfl) ⟨33419, by rfl⟩) R66839
theorem R44603 : Reach 44603 := rs (se 1 (by rfl) ⟨33452, by rfl⟩) R66905
theorem R44679 : Reach 44679 := rs (se 1 (by rfl) ⟨33509, by rfl⟩) R67019
theorem R44687 : Reach 44687 := rs (se 1 (by rfl) ⟨33515, by rfl⟩) R67031
theorem R44731 : Reach 44731 := rs (se 1 (by rfl) ⟨33548, by rfl⟩) R67097
theorem R208585 : Reach 208585 := rs (se 2 (by rfl) ⟨78219, by rfl⟩) R156439
theorem R110281 : Reach 110281 := rs (se 2 (by rfl) ⟨41355, by rfl⟩) R82711
theorem R339713 : Reach 339713 := rs (se 2 (by rfl) ⟨127392, by rfl⟩) R254785
theorem R44807 : Reach 44807 := rs (se 1 (by rfl) ⟨33605, by rfl⟩) R67211
theorem R208655 : Reach 208655 := rs (se 1 (by rfl) ⟨156491, by rfl⟩) R312983
theorem R44815 : Reach 44815 := rs (se 1 (by rfl) ⟨33611, by rfl⟩) R67223
theorem R77611 : Reach 77611 := rs (se 1 (by rfl) ⟨58208, by rfl⟩) R116417
theorem R44859 : Reach 44859 := rs (se 1 (by rfl) ⟨33644, by rfl⟩) R67289
theorem R110423 : Reach 110423 := rs (se 1 (by rfl) ⟨82817, by rfl⟩) R165635
theorem R44935 : Reach 44935 := rs (se 1 (by rfl) ⟨33701, by rfl⟩) R67403
theorem R44943 : Reach 44943 := rs (se 1 (by rfl) ⟨33707, by rfl⟩) R67415
theorem R77753 : Reach 77753 := rs (se 2 (by rfl) ⟨29157, by rfl⟩) R58315
theorem R44987 : Reach 44987 := rs (se 1 (by rfl) ⟨33740, by rfl⟩) R67481
theorem R45063 : Reach 45063 := rs (se 1 (by rfl) ⟨33797, by rfl⟩) R67595
theorem R45071 : Reach 45071 := rs (se 1 (by rfl) ⟨33803, by rfl⟩) R67607
theorem R45115 : Reach 45115 := rs (se 1 (by rfl) ⟨33836, by rfl⟩) R67673
theorem R45191 : Reach 45191 := rs (se 1 (by rfl) ⟨33893, by rfl⟩) R67787
theorem R45199 : Reach 45199 := rs (se 1 (by rfl) ⟨33899, by rfl⟩) R67799
theorem R45243 : Reach 45243 := rs (se 1 (by rfl) ⟨33932, by rfl⟩) R67865
theorem R45319 : Reach 45319 := rs (se 1 (by rfl) ⟨33989, by rfl⟩) R67979
theorem R45327 : Reach 45327 := rs (se 1 (by rfl) ⟨33995, by rfl⟩) R67991
theorem R45371 : Reach 45371 := rs (se 1 (by rfl) ⟨34028, by rfl⟩) R68057
theorem R45447 : Reach 45447 := rs (se 1 (by rfl) ⟨34085, by rfl⟩) R68171
theorem R45455 : Reach 45455 := rs (se 1 (by rfl) ⟨34091, by rfl⟩) R68183
theorem R45499 : Reach 45499 := rs (se 1 (by rfl) ⟨34124, by rfl⟩) R68249
theorem R45575 : Reach 45575 := rs (se 1 (by rfl) ⟨34181, by rfl⟩) R68363
theorem R45583 : Reach 45583 := rs (se 1 (by rfl) ⟨34187, by rfl⟩) R68375
theorem R45627 : Reach 45627 := rs (se 1 (by rfl) ⟨34220, by rfl⟩) R68441
theorem R78455 : Reach 78455 := rs (se 1 (by rfl) ⟨58841, by rfl⟩) R117683
theorem R45703 : Reach 45703 := rs (se 1 (by rfl) ⟨34277, by rfl⟩) R68555
theorem R45711 : Reach 45711 := rs (se 1 (by rfl) ⟨34283, by rfl⟩) R68567
theorem R111257 : Reach 111257 := rs (se 2 (by rfl) ⟨41721, by rfl⟩) R83443
theorem R45755 : Reach 45755 := rs (se 1 (by rfl) ⟨34316, by rfl⟩) R68633
theorem R45831 : Reach 45831 := rs (se 1 (by rfl) ⟨34373, by rfl⟩) R68747
theorem R45839 : Reach 45839 := rs (se 1 (by rfl) ⟨34379, by rfl⟩) R68759
theorem R45883 : Reach 45883 := rs (se 1 (by rfl) ⟨34412, by rfl⟩) R68825
theorem R177011 : Reach 177011 := rs (se 1 (by rfl) ⟨132758, by rfl⟩) R265517
theorem R45959 : Reach 45959 := rs (se 1 (by rfl) ⟨34469, by rfl⟩) R68939
theorem R45967 : Reach 45967 := rs (se 1 (by rfl) ⟨34475, by rfl⟩) R68951
theorem R46011 : Reach 46011 := rs (se 1 (by rfl) ⟨34508, by rfl⟩) R69017
theorem R46087 : Reach 46087 := rs (se 1 (by rfl) ⟨34565, by rfl⟩) R69131
theorem R46095 : Reach 46095 := rs (se 1 (by rfl) ⟨34571, by rfl⟩) R69143
theorem R46139 : Reach 46139 := rs (se 1 (by rfl) ⟨34604, by rfl⟩) R69209
theorem R78907 : Reach 78907 := rs (se 1 (by rfl) ⟨59180, by rfl⟩) R118361
theorem R144445 : Reach 144445 := rs (se 3 (by rfl) ⟨27083, by rfl⟩) R54167
theorem R46215 : Reach 46215 := rs (se 1 (by rfl) ⟨34661, by rfl⟩) R69323
theorem R46223 : Reach 46223 := rs (se 1 (by rfl) ⟨34667, by rfl⟩) R69335
theorem R78995 : Reach 78995 := rs (se 1 (by rfl) ⟨59246, by rfl⟩) R118493
theorem R46267 : Reach 46267 := rs (se 1 (by rfl) ⟨34700, by rfl⟩) R69401
theorem R79049 : Reach 79049 := rs (se 2 (by rfl) ⟨29643, by rfl⟩) R59287
theorem R46343 : Reach 46343 := rs (se 1 (by rfl) ⟨34757, by rfl⟩) R69515
theorem R46351 : Reach 46351 := rs (se 1 (by rfl) ⟨34763, by rfl⟩) R69527
theorem R46395 : Reach 46395 := rs (se 1 (by rfl) ⟨34796, by rfl⟩) R69593
theorem R46471 : Reach 46471 := rs (se 1 (by rfl) ⟨34853, by rfl⟩) R69707
theorem R46479 : Reach 46479 := rs (se 1 (by rfl) ⟨34859, by rfl⟩) R69719
theorem R112025 : Reach 112025 := rs (se 2 (by rfl) ⟨42009, by rfl⟩) R84019
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R46523 : Reach 46523 := rs (se 1 (by rfl) ⟨34892, by rfl⟩) R69785
theorem R46599 : Reach 46599 := rs (se 1 (by rfl) ⟨34949, by rfl⟩) R69899
theorem R46607 : Reach 46607 := rs (se 1 (by rfl) ⟨34955, by rfl⟩) R69911
theorem R79393 : Reach 79393 := rs (se 2 (by rfl) ⟨29772, by rfl⟩) R59545
theorem R46651 : Reach 46651 := rs (se 1 (by rfl) ⟨34988, by rfl⟩) R69977
theorem R46727 : Reach 46727 := rs (se 1 (by rfl) ⟨35045, by rfl⟩) R70091
theorem R46735 : Reach 46735 := rs (se 1 (by rfl) ⟨35051, by rfl⟩) R70103
theorem R112313 : Reach 112313 := rs (se 2 (by rfl) ⟨42117, by rfl⟩) R84235
theorem R46779 : Reach 46779 := rs (se 1 (by rfl) ⟨35084, by rfl⟩) R70169
theorem R46855 : Reach 46855 := rs (se 1 (by rfl) ⟨35141, by rfl⟩) R70283
theorem R46863 : Reach 46863 := rs (se 1 (by rfl) ⟨35147, by rfl⟩) R70295
theorem R46907 : Reach 46907 := rs (se 1 (by rfl) ⟨35180, by rfl⟩) R70361
theorem R112499 : Reach 112499 := rs (se 1 (by rfl) ⟨84374, by rfl⟩) R168749
theorem R46983 : Reach 46983 := rs (se 1 (by rfl) ⟨35237, by rfl⟩) R70475
theorem R46991 : Reach 46991 := rs (se 1 (by rfl) ⟨35243, by rfl⟩) R70487
theorem R47035 : Reach 47035 := rs (se 1 (by rfl) ⟨35276, by rfl⟩) R70553
theorem R47111 : Reach 47111 := rs (se 1 (by rfl) ⟨35333, by rfl⟩) R70667
theorem R440407 : Reach 440407 := rs (se 1 (by rfl) ⟨330305, by rfl⟩) R660611
theorem R1194101 : Reach 1194101 := rs (se 5 (by rfl) ⟨55973, by rfl⟩) R111947
theorem R538973 : Reach 538973 := rs (se 3 (by rfl) ⟨101057, by rfl⟩) R202115
theorem R113015 : Reach 113015 := rs (se 1 (by rfl) ⟨84761, by rfl⟩) R169523
theorem R145799 : Reach 145799 := rs (se 1 (by rfl) ⟨109349, by rfl⟩) R218699
theorem R211517 : Reach 211517 := rs (se 3 (by rfl) ⟨39659, by rfl⟩) R79319
theorem R146177 : Reach 146177 := rs (se 2 (by rfl) ⟨54816, by rfl⟩) R109633
theorem R441139 : Reach 441139 := rs (se 1 (by rfl) ⟨330854, by rfl⟩) R661709
theorem R113593 : Reach 113593 := rs (se 2 (by rfl) ⟨42597, by rfl⟩) R85195
theorem R113707 : Reach 113707 := rs (se 1 (by rfl) ⟨85280, by rfl⟩) R170561
theorem R474245 : Reach 474245 := rs (se 4 (by rfl) ⟨44460, by rfl⟩) R88921
theorem R114007 : Reach 114007 := rs (se 1 (by rfl) ⟨85505, by rfl⟩) R171011
theorem R146987 : Reach 146987 := rs (se 1 (by rfl) ⟨110240, by rfl⟩) R220481
theorem R48775 : Reach 48775 := rs (se 1 (by rfl) ⟨36581, by rfl⟩) R73163
theorem R114311 : Reach 114311 := rs (se 1 (by rfl) ⟨85733, by rfl⟩) R171467
theorem R114443 : Reach 114443 := rs (se 1 (by rfl) ⟨85832, by rfl⟩) R171665
theorem R48955 : Reach 48955 := rs (se 1 (by rfl) ⟨36716, by rfl⟩) R73433
theorem R344087 : Reach 344087 := rs (se 1 (by rfl) ⟨258065, by rfl⟩) R516131
theorem R540917 : Reach 540917 := rs (se 5 (by rfl) ⟨25355, by rfl⟩) R50711
theorem R49423 : Reach 49423 := rs (se 1 (by rfl) ⟨37067, by rfl⟩) R74135
theorem R114959 : Reach 114959 := rs (se 1 (by rfl) ⟨86219, by rfl⟩) R172439
theorem R115091 : Reach 115091 := rs (se 1 (by rfl) ⟨86318, by rfl⟩) R172637
theorem R49927 : Reach 49927 := rs (se 1 (by rfl) ⟨37445, by rfl⟩) R74891
theorem R148283 : Reach 148283 := rs (se 1 (by rfl) ⟨111212, by rfl⟩) R222425
theorem R50107 : Reach 50107 := rs (se 1 (by rfl) ⟨37580, by rfl⟩) R75161
theorem R148769 : Reach 148769 := rs (se 2 (by rfl) ⟨55788, by rfl⟩) R111577
theorem R83243 : Reach 83243 := rs (se 1 (by rfl) ⟨62432, by rfl⟩) R124865
theorem R902501 : Reach 902501 := rs (se 4 (by rfl) ⟨84609, by rfl⟩) R169219
theorem R50575 : Reach 50575 := rs (se 1 (by rfl) ⟨37931, by rfl⟩) R75863
theorem R116225 : Reach 116225 := rs (se 2 (by rfl) ⟨43584, by rfl⟩) R87169
theorem R149111 : Reach 149111 := rs (se 1 (by rfl) ⟨111833, by rfl⟩) R223667
theorem R214721 : Reach 214721 := rs (se 2 (by rfl) ⟨80520, by rfl⟩) R161041
theorem R149363 : Reach 149363 := rs (se 1 (by rfl) ⟨112022, by rfl⟩) R224045
theorem R116599 : Reach 116599 := rs (se 1 (by rfl) ⟨87449, by rfl⟩) R174899
theorem R51079 : Reach 51079 := rs (se 1 (by rfl) ⟨38309, by rfl⟩) R76619
theorem R51115 : Reach 51115 := rs (se 1 (by rfl) ⟨38336, by rfl⟩) R76673
theorem R51259 : Reach 51259 := rs (se 1 (by rfl) ⟨38444, by rfl⟩) R76889
theorem R1001645 : Reach 1001645 := rs (se 3 (by rfl) ⟨187808, by rfl⟩) R375617
theorem R84169 : Reach 84169 := rs (se 2 (by rfl) ⟨31563, by rfl⟩) R63127
theorem R117035 : Reach 117035 := rs (se 1 (by rfl) ⟨87776, by rfl⟩) R175553
theorem R248123 : Reach 248123 := rs (se 1 (by rfl) ⟨186092, by rfl⟩) R372185
theorem R51727 : Reach 51727 := rs (se 1 (by rfl) ⟨38795, by rfl⟩) R77591
theorem R52087 : Reach 52087 := rs (se 1 (by rfl) ⟨39065, by rfl⟩) R78131
theorem R84883 : Reach 84883 := rs (se 1 (by rfl) ⟨63662, by rfl⟩) R127325
theorem R52231 : Reach 52231 := rs (se 1 (by rfl) ⟨39173, by rfl⟩) R78347
theorem R52267 : Reach 52267 := rs (se 1 (by rfl) ⟨39200, by rfl⟩) R78401
theorem R379991 : Reach 379991 := rs (se 1 (by rfl) ⟨284993, by rfl⟩) R569987
theorem R117875 : Reach 117875 := rs (se 1 (by rfl) ⟨88406, by rfl⟩) R176813
theorem R117895 : Reach 117895 := rs (se 1 (by rfl) ⟨88421, by rfl⟩) R176843
theorem R52411 : Reach 52411 := rs (se 1 (by rfl) ⟨39308, by rfl⟩) R78617
theorem R52471 : Reach 52471 := rs (se 1 (by rfl) ⟨39353, by rfl⟩) R78707
theorem R118169 : Reach 118169 := rs (se 2 (by rfl) ⟨44313, by rfl⟩) R88627
theorem R118201 : Reach 118201 := rs (se 2 (by rfl) ⟨44325, by rfl⟩) R88651
theorem R118331 : Reach 118331 := rs (se 1 (by rfl) ⟨88748, by rfl⟩) R177497
theorem R52879 : Reach 52879 := rs (se 1 (by rfl) ⟨39659, by rfl⟩) R79319
theorem R282305 : Reach 282305 := rs (se 2 (by rfl) ⟨105864, by rfl⟩) R211729
theorem R118543 : Reach 118543 := rs (se 1 (by rfl) ⟨88907, by rfl⟩) R177815
theorem R118643 : Reach 118643 := rs (se 1 (by rfl) ⟨88982, by rfl⟩) R177965
theorem R118675 : Reach 118675 := rs (se 1 (by rfl) ⟨89006, by rfl⟩) R178013
theorem R85961 : Reach 85961 := rs (se 2 (by rfl) ⟨32235, by rfl⟩) R64471
theorem R118817 : Reach 118817 := rs (se 2 (by rfl) ⟨44556, by rfl⟩) R89113
theorem R151955 : Reach 151955 := rs (se 1 (by rfl) ⟨113966, by rfl⟩) R227933
theorem R446867 : Reach 446867 := rs (se 1 (by rfl) ⟨335150, by rfl⟩) R670301
theorem R1167857 : Reach 1167857 := rs (se 2 (by rfl) ⟨437946, by rfl⟩) R875893
theorem R250411 : Reach 250411 := rs (se 1 (by rfl) ⟨187808, by rfl⟩) R375617
theorem R217667 : Reach 217667 := rs (se 1 (by rfl) ⟨163250, by rfl⟩) R326501
theorem R86827 : Reach 86827 := rs (se 1 (by rfl) ⟨65120, by rfl⟩) R130241
theorem R86903 : Reach 86903 := rs (se 1 (by rfl) ⟨65177, by rfl⟩) R130355
theorem R218513 : Reach 218513 := rs (se 2 (by rfl) ⟨81942, by rfl⟩) R163885
theorem R382657 : Reach 382657 := rs (se 2 (by rfl) ⟨143496, by rfl⟩) R286993
theorem R218861 : Reach 218861 := rs (se 3 (by rfl) ⟨41036, by rfl⟩) R82073
theorem R284431 : Reach 284431 := rs (se 1 (by rfl) ⟨213323, by rfl⟩) R426647
theorem R153359 : Reach 153359 := rs (se 1 (by rfl) ⟨115019, by rfl⟩) R230039
theorem R907057 : Reach 907057 := rs (se 2 (by rfl) ⟨340146, by rfl⟩) R680293
theorem R415651 : Reach 415651 := rs (se 1 (by rfl) ⟨311738, by rfl⟩) R623477
theorem R251869 : Reach 251869 := rs (se 3 (by rfl) ⟨47225, by rfl⟩) R94451
theorem R153629 : Reach 153629 := rs (se 3 (by rfl) ⟨28805, by rfl⟩) R57611
theorem R88265 : Reach 88265 := rs (se 2 (by rfl) ⟨33099, by rfl⟩) R66199
theorem R55723 : Reach 55723 := rs (se 1 (by rfl) ⟨41792, by rfl⟩) R83585
theorem R219671 : Reach 219671 := rs (se 1 (by rfl) ⟨164753, by rfl⟩) R329507
theorem R88847 : Reach 88847 := rs (se 1 (by rfl) ⟨66635, by rfl⟩) R133271
theorem R351469 : Reach 351469 := rs (se 3 (by rfl) ⟨65900, by rfl⟩) R131801
theorem R56695 : Reach 56695 := rs (se 1 (by rfl) ⟨42521, by rfl⟩) R85043
theorem R155033 : Reach 155033 := rs (se 2 (by rfl) ⟨58137, by rfl⟩) R116275
theorem R351863 : Reach 351863 := rs (se 1 (by rfl) ⟨263897, by rfl⟩) R527795
theorem R89785 : Reach 89785 := rs (se 2 (by rfl) ⟨33669, by rfl⟩) R67339
theorem R57019 : Reach 57019 := rs (se 1 (by rfl) ⟨42764, by rfl⟩) R85529
theorem R1269553 : Reach 1269553 := rs (se 2 (by rfl) ⟨476082, by rfl⟩) R952165
theorem R188219 : Reach 188219 := rs (se 1 (by rfl) ⟨141164, by rfl⟩) R282329
theorem R89915 : Reach 89915 := rs (se 1 (by rfl) ⟨67436, by rfl⟩) R134873
theorem R188477 : Reach 188477 := rs (se 3 (by rfl) ⟨35339, by rfl⟩) R70679
theorem R155735 : Reach 155735 := rs (se 1 (by rfl) ⟨116801, by rfl⟩) R233603
theorem R123065 : Reach 123065 := rs (se 2 (by rfl) ⟨46149, by rfl⟩) R92299
theorem R156113 : Reach 156113 := rs (se 2 (by rfl) ⟨58542, by rfl⟩) R117085
theorem R123407 : Reach 123407 := rs (se 1 (by rfl) ⟨92555, by rfl⟩) R185111
theorem R156221 : Reach 156221 := rs (se 3 (by rfl) ⟨29291, by rfl⟩) R58583
theorem R352835 : Reach 352835 := rs (se 1 (by rfl) ⟨264626, by rfl⟩) R529253
theorem R57991 : Reach 57991 := rs (se 1 (by rfl) ⟨43493, by rfl⟩) R86987
theorem R3761093 : Reach 3761093 := rs (se 4 (by rfl) ⟨352602, by rfl⟩) R705205
theorem R58411 : Reach 58411 := rs (se 1 (by rfl) ⟨43808, by rfl⟩) R87617
theorem R58639 : Reach 58639 := rs (se 1 (by rfl) ⟨43979, by rfl⟩) R87959
theorem R124193 : Reach 124193 := rs (se 2 (by rfl) ⟨46572, by rfl⟩) R93145
theorem R222749 : Reach 222749 := rs (se 3 (by rfl) ⟨41765, by rfl⟩) R83531
theorem R157625 : Reach 157625 := rs (se 2 (by rfl) ⟨59109, by rfl⟩) R118219
theorem R59383 : Reach 59383 := rs (se 1 (by rfl) ⟨44537, by rfl⟩) R89075
theorem R223235 : Reach 223235 := rs (se 1 (by rfl) ⟨167426, by rfl⟩) R334853
theorem R190475 : Reach 190475 := rs (se 1 (by rfl) ⟨142856, by rfl⟩) R285713
theorem R59449 : Reach 59449 := rs (se 2 (by rfl) ⟨22293, by rfl⟩) R44587
theorem R256061 : Reach 256061 := rs (se 3 (by rfl) ⟨48011, by rfl⟩) R96023
theorem R158219 : Reach 158219 := rs (se 1 (by rfl) ⟨118664, by rfl⟩) R237329
theorem R158327 : Reach 158327 := rs (se 1 (by rfl) ⟨118745, by rfl⟩) R237491
theorem R256769 : Reach 256769 := rs (se 2 (by rfl) ⟨96288, by rfl⟩) R192577
theorem R125707 : Reach 125707 := rs (se 1 (by rfl) ⟨94280, by rfl⟩) R188561
theorem R224153 : Reach 224153 := rs (se 2 (by rfl) ⟨84057, by rfl⟩) R168115
theorem R125981 : Reach 125981 := rs (se 3 (by rfl) ⟨23621, by rfl⟩) R47243
theorem R420997 : Reach 420997 := rs (se 4 (by rfl) ⟨39468, by rfl⟩) R78937
theorem R158921 : Reach 158921 := rs (se 2 (by rfl) ⟨59595, by rfl⟩) R119191
theorem R93455 : Reach 93455 := rs (se 1 (by rfl) ⟨70091, by rfl⟩) R140183
theorem R1371491 : Reach 1371491 := rs (se 1 (by rfl) ⟨1028618, by rfl⟩) R2057237
theorem R126323 : Reach 126323 := rs (se 1 (by rfl) ⟨94742, by rfl⟩) R189485
theorem R224855 : Reach 224855 := rs (se 1 (by rfl) ⟨168641, by rfl⟩) R337283
theorem R225341 : Reach 225341 := rs (se 3 (by rfl) ⟨42251, by rfl⟩) R84503
theorem R127037 : Reach 127037 := rs (se 3 (by rfl) ⟨23819, by rfl⟩) R47639
theorem R127291 : Reach 127291 := rs (se 1 (by rfl) ⟨95468, by rfl⟩) R190937
theorem R61897 : Reach 61897 := rs (se 2 (by rfl) ⟨23211, by rfl⟩) R46423
theorem R357209 : Reach 357209 := rs (se 2 (by rfl) ⟨133953, by rfl⟩) R267907
theorem R291863 : Reach 291863 := rs (se 1 (by rfl) ⟨218897, by rfl⟩) R437795
theorem R259159 : Reach 259159 := rs (se 1 (by rfl) ⟨194369, by rfl⟩) R388739
theorem R128299 : Reach 128299 := rs (se 1 (by rfl) ⟨96224, by rfl⟩) R192449
theorem R128441 : Reach 128441 := rs (se 2 (by rfl) ⟨48165, by rfl⟩) R96331
theorem R161291 : Reach 161291 := rs (se 1 (by rfl) ⟨120968, by rfl⟩) R241937
theorem R95879 : Reach 95879 := rs (se 1 (by rfl) ⟨71909, by rfl⟩) R143819
theorem R358145 : Reach 358145 := rs (se 2 (by rfl) ⟨134304, by rfl⟩) R268609
theorem R128783 : Reach 128783 := rs (se 1 (by rfl) ⟨96587, by rfl⟩) R193175
theorem R227123 : Reach 227123 := rs (se 1 (by rfl) ⟨170342, by rfl⟩) R340685
theorem R423755 : Reach 423755 := rs (se 1 (by rfl) ⟨317816, by rfl⟩) R635633
theorem R325579 : Reach 325579 := rs (se 1 (by rfl) ⟨244184, by rfl⟩) R488369
theorem R227447 : Reach 227447 := rs (se 1 (by rfl) ⟨170585, by rfl⟩) R341171
theorem R63623 : Reach 63623 := rs (se 1 (by rfl) ⟨47717, by rfl⟩) R95435
theorem R981233 : Reach 981233 := rs (se 2 (by rfl) ⟨367962, by rfl⟩) R735925
theorem R194849 : Reach 194849 := rs (se 2 (by rfl) ⟨73068, by rfl⟩) R146137
theorem R227731 : Reach 227731 := rs (se 1 (by rfl) ⟨170798, by rfl⟩) R341597
theorem R129671 : Reach 129671 := rs (se 1 (by rfl) ⟨97253, by rfl⟩) R194507
theorem R228041 : Reach 228041 := rs (se 2 (by rfl) ⟨85515, by rfl⟩) R171031
theorem R129853 : Reach 129853 := rs (se 3 (by rfl) ⟨24347, by rfl⟩) R48695
theorem R195463 : Reach 195463 := rs (se 1 (by rfl) ⟨146597, by rfl⟩) R293195
theorem R261143 : Reach 261143 := rs (se 1 (by rfl) ⟨195857, by rfl⟩) R391715
theorem R130081 : Reach 130081 := rs (se 2 (by rfl) ⟨48780, by rfl⟩) R97561
theorem R228419 : Reach 228419 := rs (se 1 (by rfl) ⟨171314, by rfl⟩) R342629
theorem R64585 : Reach 64585 := rs (se 2 (by rfl) ⟨24219, by rfl⟩) R48439
theorem R97415 : Reach 97415 := rs (se 1 (by rfl) ⟨73061, by rfl⟩) R146123
theorem R64697 : Reach 64697 := rs (se 2 (by rfl) ⟨24261, by rfl⟩) R48523
theorem R64775 : Reach 64775 := rs (se 1 (by rfl) ⟨48581, by rfl⟩) R97163
theorem R64811 : Reach 64811 := rs (se 1 (by rfl) ⟨48608, by rfl⟩) R97217
theorem R97595 : Reach 97595 := rs (se 1 (by rfl) ⟨73196, by rfl⟩) R146393
theorem R64841 : Reach 64841 := rs (se 2 (by rfl) ⟨24315, by rfl⟩) R48631
theorem R130423 : Reach 130423 := rs (se 1 (by rfl) ⟨97817, by rfl⟩) R195635
theorem R228743 : Reach 228743 := rs (se 1 (by rfl) ⟨171557, by rfl⟩) R343115
theorem R97721 : Reach 97721 := rs (se 2 (by rfl) ⟨36645, by rfl⟩) R73291
theorem R64955 : Reach 64955 := rs (se 1 (by rfl) ⟨48716, by rfl⟩) R97433
theorem R65015 : Reach 65015 := rs (se 1 (by rfl) ⟨48761, by rfl⟩) R97523
theorem R65039 : Reach 65039 := rs (se 1 (by rfl) ⟨48779, by rfl⟩) R97559
theorem R65081 : Reach 65081 := rs (se 2 (by rfl) ⟨24405, by rfl⟩) R48811
theorem R2719331 : Reach 2719331 := rs (se 1 (by rfl) ⟨2039498, by rfl⟩) R4078997
theorem R65159 : Reach 65159 := rs (se 1 (by rfl) ⟨48869, by rfl⟩) R97739
theorem R65195 : Reach 65195 := rs (se 1 (by rfl) ⟨48896, by rfl⟩) R97793
theorem R65225 : Reach 65225 := rs (se 2 (by rfl) ⟨24459, by rfl⟩) R48919
theorem R98063 : Reach 98063 := rs (se 1 (by rfl) ⟨73547, by rfl⟩) R147095
theorem R98081 : Reach 98081 := rs (se 2 (by rfl) ⟨36780, by rfl⟩) R73561
theorem R65339 : Reach 65339 := rs (se 1 (by rfl) ⟨49004, by rfl⟩) R98009
theorem R65399 : Reach 65399 := rs (se 1 (by rfl) ⟨49049, by rfl⟩) R98099
theorem R65423 : Reach 65423 := rs (se 1 (by rfl) ⟨49067, by rfl⟩) R98135
theorem R393113 : Reach 393113 := rs (se 2 (by rfl) ⟨147417, by rfl⟩) R294835
theorem R65465 : Reach 65465 := rs (se 2 (by rfl) ⟨24549, by rfl⟩) R49099
theorem R229391 : Reach 229391 := rs (se 1 (by rfl) ⟨172043, by rfl⟩) R344087
theorem R131129 : Reach 131129 := rs (se 2 (by rfl) ⟨49173, by rfl⟩) R98347
theorem R65615 : Reach 65615 := rs (se 1 (by rfl) ⟨49211, by rfl⟩) R98423
theorem R360611 : Reach 360611 := rs (se 1 (by rfl) ⟨270458, by rfl⟩) R540917
theorem R65735 : Reach 65735 := rs (se 1 (by rfl) ⟨49301, by rfl⟩) R98603
theorem R196951 : Reach 196951 := rs (se 1 (by rfl) ⟨147713, by rfl⟩) R295427
theorem R65897 : Reach 65897 := rs (se 2 (by rfl) ⟨24711, by rfl⟩) R49423
theorem R65975 : Reach 65975 := rs (se 1 (by rfl) ⟨49481, by rfl⟩) R98963
theorem R66011 : Reach 66011 := rs (se 1 (by rfl) ⟨49508, by rfl⟩) R99017
theorem R98825 : Reach 98825 := rs (se 2 (by rfl) ⟨37059, by rfl⟩) R74119
theorem R98855 : Reach 98855 := rs (se 1 (by rfl) ⟨74141, by rfl⟩) R148283
theorem R99065 : Reach 99065 := rs (se 2 (by rfl) ⟨37149, by rfl⟩) R74299
theorem R99179 : Reach 99179 := rs (se 1 (by rfl) ⟨74384, by rfl⟩) R148769
theorem R99233 : Reach 99233 := rs (se 2 (by rfl) ⟨37212, by rfl⟩) R74425
theorem R66479 : Reach 66479 := rs (se 1 (by rfl) ⟨49859, by rfl⟩) R99719
theorem R66569 : Reach 66569 := rs (se 2 (by rfl) ⟨24963, by rfl⟩) R49927
theorem R66599 : Reach 66599 := rs (se 1 (by rfl) ⟨49949, by rfl⟩) R99899
theorem R99407 : Reach 99407 := rs (se 1 (by rfl) ⟨74555, by rfl⟩) R149111
theorem R66683 : Reach 66683 := rs (se 1 (by rfl) ⟨50012, by rfl⟩) R100025
theorem R99575 : Reach 99575 := rs (se 1 (by rfl) ⟨74681, by rfl⟩) R149363
theorem R66809 : Reach 66809 := rs (se 2 (by rfl) ⟨25053, by rfl⟩) R50107
theorem R66911 : Reach 66911 := rs (se 1 (by rfl) ⟨50183, by rfl⟩) R100367
theorem R99689 : Reach 99689 := rs (se 2 (by rfl) ⟨37383, by rfl⟩) R74767
theorem R66923 : Reach 66923 := rs (se 1 (by rfl) ⟨50192, by rfl⟩) R100385
theorem R165415 : Reach 165415 := rs (se 1 (by rfl) ⟨124061, by rfl⟩) R248123
theorem R67151 : Reach 67151 := rs (se 1 (by rfl) ⟨50363, by rfl⟩) R100727
theorem R67271 : Reach 67271 := rs (se 1 (by rfl) ⟨50453, by rfl⟩) R100907
theorem R100169 : Reach 100169 := rs (se 2 (by rfl) ⟨37563, by rfl⟩) R75127
theorem R67433 : Reach 67433 := rs (se 2 (by rfl) ⟨25287, by rfl⟩) R50575
theorem R67511 : Reach 67511 := rs (se 1 (by rfl) ⟨50633, by rfl⟩) R101267
theorem R67547 : Reach 67547 := rs (se 1 (by rfl) ⟨50660, by rfl⟩) R101321
theorem R68015 : Reach 68015 := rs (se 1 (by rfl) ⟨51011, by rfl⟩) R102023
theorem R68105 : Reach 68105 := rs (se 2 (by rfl) ⟨25539, by rfl⟩) R51079
theorem R68135 : Reach 68135 := rs (se 1 (by rfl) ⟨51101, by rfl⟩) R102203
theorem R68153 : Reach 68153 := rs (se 2 (by rfl) ⟨25557, by rfl⟩) R51115
theorem R100961 : Reach 100961 := rs (se 2 (by rfl) ⟨37860, by rfl⟩) R75721
theorem R68219 : Reach 68219 := rs (se 1 (by rfl) ⟨51164, by rfl⟩) R102329
theorem R68267 : Reach 68267 := rs (se 1 (by rfl) ⟨51200, by rfl⟩) R102401
theorem R232145 : Reach 232145 := rs (se 2 (by rfl) ⟨87054, by rfl⟩) R174109
theorem R68345 : Reach 68345 := rs (se 2 (by rfl) ⟨25629, by rfl⟩) R51259
theorem R1084229 : Reach 1084229 := rs (se 4 (by rfl) ⟨101646, by rfl⟩) R203293
theorem R68447 : Reach 68447 := rs (se 1 (by rfl) ⟨51335, by rfl⟩) R102671
theorem R68459 : Reach 68459 := rs (se 1 (by rfl) ⟨51344, by rfl⟩) R102689
theorem R68495 : Reach 68495 := rs (se 1 (by rfl) ⟨51371, by rfl⟩) R102743
theorem R101303 : Reach 101303 := rs (se 1 (by rfl) ⟨75977, by rfl⟩) R151955
theorem R297911 : Reach 297911 := rs (se 1 (by rfl) ⟨223433, by rfl⟩) R446867
theorem R68615 : Reach 68615 := rs (se 1 (by rfl) ⟨51461, by rfl⟩) R102923
theorem R592919 : Reach 592919 := rs (se 1 (by rfl) ⟨444689, by rfl⟩) R889379
theorem R68687 : Reach 68687 := rs (se 1 (by rfl) ⟨51515, by rfl⟩) R103031
theorem R68807 : Reach 68807 := rs (se 1 (by rfl) ⟨51605, by rfl⟩) R103211
theorem R265463 : Reach 265463 := rs (se 1 (by rfl) ⟨199097, by rfl⟩) R398195
theorem R68855 : Reach 68855 := rs (se 1 (by rfl) ⟨51641, by rfl⟩) R103283
theorem R68969 : Reach 68969 := rs (se 2 (by rfl) ⟨25863, by rfl⟩) R51727
theorem R69007 : Reach 69007 := rs (se 1 (by rfl) ⟨51755, by rfl⟩) R103511
theorem R69047 : Reach 69047 := rs (se 1 (by rfl) ⟨51785, by rfl⟩) R103571
theorem R69083 : Reach 69083 := rs (se 1 (by rfl) ⟨51812, by rfl⟩) R103625
theorem R101897 : Reach 101897 := rs (se 2 (by rfl) ⟨38211, by rfl⟩) R76423
theorem R167609 : Reach 167609 := rs (se 2 (by rfl) ⟨62853, by rfl⟩) R125707
theorem R265949 : Reach 265949 := rs (se 3 (by rfl) ⟨49865, by rfl⟩) R99731
theorem R69449 : Reach 69449 := rs (se 2 (by rfl) ⟨26043, by rfl⟩) R52087
theorem R102239 : Reach 102239 := rs (se 1 (by rfl) ⟨76679, by rfl⟩) R153359
theorem R69551 : Reach 69551 := rs (se 1 (by rfl) ⟨52163, by rfl⟩) R104327
theorem R69563 : Reach 69563 := rs (se 1 (by rfl) ⟨52172, by rfl⟩) R104345
theorem R69641 : Reach 69641 := rs (se 2 (by rfl) ⟨26115, by rfl⟩) R52231
theorem R102419 : Reach 102419 := rs (se 1 (by rfl) ⟨76814, by rfl⟩) R153629
theorem R430109 : Reach 430109 := rs (se 3 (by rfl) ⟨80645, by rfl⟩) R161291
theorem R69671 : Reach 69671 := rs (se 1 (by rfl) ⟨52253, by rfl⟩) R104507
theorem R69689 : Reach 69689 := rs (se 2 (by rfl) ⟨26133, by rfl⟩) R52267
theorem R69755 : Reach 69755 := rs (se 1 (by rfl) ⟨52316, by rfl⟩) R104633
theorem R69803 : Reach 69803 := rs (se 1 (by rfl) ⟨52352, by rfl⟩) R104705
theorem R561329 : Reach 561329 := rs (se 2 (by rfl) ⟨210498, by rfl⟩) R420997
theorem R69881 : Reach 69881 := rs (se 2 (by rfl) ⟨26205, by rfl⟩) R52411
theorem R69983 : Reach 69983 := rs (se 1 (by rfl) ⟨52487, by rfl⟩) R104975
theorem R102761 : Reach 102761 := rs (se 2 (by rfl) ⟨38535, by rfl⟩) R77071
theorem R69995 : Reach 69995 := rs (se 1 (by rfl) ⟨52496, by rfl⟩) R104993
theorem R70031 : Reach 70031 := rs (se 1 (by rfl) ⟨52523, by rfl⟩) R105047
theorem R299501 : Reach 299501 := rs (se 3 (by rfl) ⟨56156, by rfl⟩) R112313
theorem R70151 : Reach 70151 := rs (se 1 (by rfl) ⟨52613, by rfl⟩) R105227
theorem R70223 : Reach 70223 := rs (se 1 (by rfl) ⟨52667, by rfl⟩) R105335
theorem R332423 : Reach 332423 := rs (se 1 (by rfl) ⟨249317, by rfl⟩) R498635
theorem R70343 : Reach 70343 := rs (se 1 (by rfl) ⟨52757, by rfl⟩) R105515
theorem R70391 : Reach 70391 := rs (se 1 (by rfl) ⟨52793, by rfl⟩) R105587
theorem R70505 : Reach 70505 := rs (se 2 (by rfl) ⟨26439, by rfl⟩) R52879
theorem R70583 : Reach 70583 := rs (se 1 (by rfl) ⟨52937, by rfl⟩) R105875
theorem R103355 : Reach 103355 := rs (se 1 (by rfl) ⟨77516, by rfl⟩) R155033
theorem R70619 : Reach 70619 := rs (se 1 (by rfl) ⟨52964, by rfl⟩) R105929
theorem R332819 : Reach 332819 := rs (se 1 (by rfl) ⟨249614, by rfl⟩) R499229
theorem R103481 : Reach 103481 := rs (se 2 (by rfl) ⟨38805, by rfl⟩) R77611
theorem R234575 : Reach 234575 := rs (se 1 (by rfl) ⟨175931, by rfl⟩) R351863
theorem R70903 : Reach 70903 := rs (se 1 (by rfl) ⟨53177, by rfl⟩) R106355
theorem R103823 : Reach 103823 := rs (se 1 (by rfl) ⟨77867, by rfl⟩) R155735
theorem R104075 : Reach 104075 := rs (se 1 (by rfl) ⟨78056, by rfl⟩) R156113
theorem R169661 : Reach 169661 := rs (se 3 (by rfl) ⟨31811, by rfl⟩) R63623
theorem R104147 : Reach 104147 := rs (se 1 (by rfl) ⟨78110, by rfl⟩) R156221
theorem R235223 : Reach 235223 := rs (se 1 (by rfl) ⟨176417, by rfl⟩) R352835
theorem R169721 : Reach 169721 := rs (se 2 (by rfl) ⟨63645, by rfl⟩) R127291
theorem R71531 : Reach 71531 := rs (se 1 (by rfl) ⟨53648, by rfl⟩) R107297
theorem R333827 : Reach 333827 := rs (se 1 (by rfl) ⟨250370, by rfl⟩) R500741
theorem R333881 : Reach 333881 := rs (se 2 (by rfl) ⟨125205, by rfl⟩) R250411
theorem R72031 : Reach 72031 := rs (se 1 (by rfl) ⟨54023, by rfl⟩) R108047
theorem R1874501 : Reach 1874501 := rs (se 4 (by rfl) ⟨175734, by rfl⟩) R351469
theorem R105083 : Reach 105083 := rs (se 1 (by rfl) ⟨78812, by rfl⟩) R157625
theorem R170707 : Reach 170707 := rs (se 1 (by rfl) ⟨128030, by rfl⟩) R256061
theorem R105209 : Reach 105209 := rs (se 2 (by rfl) ⟨39453, by rfl⟩) R78907
theorem R105479 : Reach 105479 := rs (se 1 (by rfl) ⟨79109, by rfl⟩) R158219
theorem R171065 : Reach 171065 := rs (se 2 (by rfl) ⟨64149, by rfl⟩) R128299
theorem R400463 : Reach 400463 := rs (se 1 (by rfl) ⟨300347, by rfl⟩) R600695
theorem R105551 : Reach 105551 := rs (se 1 (by rfl) ⟨79163, by rfl⟩) R158327
theorem R171179 : Reach 171179 := rs (se 1 (by rfl) ⟨128384, by rfl⟩) R256769
theorem R73055 : Reach 73055 := rs (se 1 (by rfl) ⟨54791, by rfl⟩) R109583
theorem R138601 : Reach 138601 := rs (se 2 (by rfl) ⟨51975, by rfl⟩) R103951
theorem R105857 : Reach 105857 := rs (se 2 (by rfl) ⟨39696, by rfl⟩) R79393
theorem R105947 : Reach 105947 := rs (se 1 (by rfl) ⟨79460, by rfl⟩) R158921
theorem R139103 : Reach 139103 := rs (se 1 (by rfl) ⟨104327, by rfl⟩) R208655
theorem R73615 : Reach 73615 := rs (se 1 (by rfl) ⟨55211, by rfl⟩) R110423
theorem R434105 : Reach 434105 := rs (se 2 (by rfl) ⟨162789, by rfl⟩) R325579
theorem R335825 : Reach 335825 := rs (se 2 (by rfl) ⟨125934, by rfl⟩) R251869
theorem R74171 : Reach 74171 := rs (se 1 (by rfl) ⟨55628, by rfl⟩) R111257
theorem R303641 : Reach 303641 := rs (se 2 (by rfl) ⟨113865, by rfl⟩) R227731
theorem R74297 : Reach 74297 := rs (se 2 (by rfl) ⟨27861, by rfl⟩) R55723
theorem R238139 : Reach 238139 := rs (se 1 (by rfl) ⟨178604, by rfl⟩) R357209
theorem R139961 : Reach 139961 := rs (se 2 (by rfl) ⟨52485, by rfl⟩) R104971
theorem R74683 : Reach 74683 := rs (se 1 (by rfl) ⟨56012, by rfl⟩) R112025
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R140345 : Reach 140345 := rs (se 2 (by rfl) ⟨52629, by rfl⟩) R105259
theorem R173137 : Reach 173137 := rs (se 2 (by rfl) ⟨64926, by rfl⟩) R129853
theorem R238763 : Reach 238763 := rs (se 1 (by rfl) ⟨179072, by rfl⟩) R358145
theorem R74999 : Reach 74999 := rs (se 1 (by rfl) ⟨56249, by rfl⟩) R112499
theorem R173441 : Reach 173441 := rs (se 2 (by rfl) ⟨65040, by rfl⟩) R130081
theorem R796067 : Reach 796067 := rs (se 1 (by rfl) ⟨597050, by rfl⟩) R1194101
theorem R75343 : Reach 75343 := rs (se 1 (by rfl) ⟨56507, by rfl⟩) R113015
theorem R141011 : Reach 141011 := rs (se 1 (by rfl) ⟨105758, by rfl⟩) R211517
theorem R75593 : Reach 75593 := rs (se 2 (by rfl) ⟨28347, by rfl⟩) R56695
theorem R173897 : Reach 173897 := rs (se 2 (by rfl) ⟨65211, by rfl⟩) R130423
theorem R174095 : Reach 174095 := rs (se 1 (by rfl) ⟨130571, by rfl⟩) R261143
theorem R632933 : Reach 632933 := rs (se 4 (by rfl) ⟨59337, by rfl⟩) R118675
theorem R43131 : Reach 43131 := rs (se 1 (by rfl) ⟨32348, by rfl⟩) R64697
theorem R239773 : Reach 239773 := rs (se 3 (by rfl) ⟨44957, by rfl⟩) R89915
theorem R43183 : Reach 43183 := rs (se 1 (by rfl) ⟨32387, by rfl⟩) R64775
theorem R43207 : Reach 43207 := rs (se 1 (by rfl) ⟨32405, by rfl⟩) R64811
theorem R43227 : Reach 43227 := rs (se 1 (by rfl) ⟨32420, by rfl⟩) R64841
theorem R76025 : Reach 76025 := rs (se 2 (by rfl) ⟨28509, by rfl⟩) R57019
theorem R272641 : Reach 272641 := rs (se 2 (by rfl) ⟨102240, by rfl⟩) R204481
theorem R43303 : Reach 43303 := rs (se 1 (by rfl) ⟨32477, by rfl⟩) R64955
theorem R43343 : Reach 43343 := rs (se 1 (by rfl) ⟨32507, by rfl⟩) R65015
theorem R43359 : Reach 43359 := rs (se 1 (by rfl) ⟨32519, by rfl⟩) R65039
theorem R43387 : Reach 43387 := rs (se 1 (by rfl) ⟨32540, by rfl⟩) R65081
theorem R1812887 : Reach 1812887 := rs (se 1 (by rfl) ⟨1359665, by rfl⟩) R2719331
theorem R43439 : Reach 43439 := rs (se 1 (by rfl) ⟨32579, by rfl⟩) R65159
theorem R76207 : Reach 76207 := rs (se 1 (by rfl) ⟨57155, by rfl⟩) R114311
theorem R43463 : Reach 43463 := rs (se 1 (by rfl) ⟨32597, by rfl⟩) R65195
theorem R43483 : Reach 43483 := rs (se 1 (by rfl) ⟨32612, by rfl⟩) R65225
theorem R76295 : Reach 76295 := rs (se 1 (by rfl) ⟨57221, by rfl⟩) R114443
theorem R43559 : Reach 43559 := rs (se 1 (by rfl) ⟨32669, by rfl⟩) R65339
theorem R535085 : Reach 535085 := rs (se 3 (by rfl) ⟨100328, by rfl⟩) R200657
theorem R43599 : Reach 43599 := rs (se 1 (by rfl) ⟨32699, by rfl⟩) R65399
theorem R43615 : Reach 43615 := rs (se 1 (by rfl) ⟨32711, by rfl⟩) R65423
theorem R43643 : Reach 43643 := rs (se 1 (by rfl) ⟨32732, by rfl⟩) R65465
theorem R43695 : Reach 43695 := rs (se 1 (by rfl) ⟨32771, by rfl⟩) R65543
theorem R43719 : Reach 43719 := rs (se 1 (by rfl) ⟨32789, by rfl⟩) R65579
theorem R43739 : Reach 43739 := rs (se 1 (by rfl) ⟨32804, by rfl⟩) R65609
theorem R43815 : Reach 43815 := rs (se 1 (by rfl) ⟨32861, by rfl⟩) R65723
theorem R43855 : Reach 43855 := rs (se 1 (by rfl) ⟨32891, by rfl⟩) R65783
theorem R43871 : Reach 43871 := rs (se 1 (by rfl) ⟨32903, by rfl⟩) R65807
theorem R76639 : Reach 76639 := rs (se 1 (by rfl) ⟨57479, by rfl⟩) R114959
theorem R43899 : Reach 43899 := rs (se 1 (by rfl) ⟨32924, by rfl⟩) R65849
theorem R43951 : Reach 43951 := rs (se 1 (by rfl) ⟨32963, by rfl⟩) R65927
theorem R76727 : Reach 76727 := rs (se 1 (by rfl) ⟨57545, by rfl⟩) R115091
theorem R43975 : Reach 43975 := rs (se 1 (by rfl) ⟨32981, by rfl⟩) R65963
theorem R43995 : Reach 43995 := rs (se 1 (by rfl) ⟨32996, by rfl⟩) R65993
theorem R44071 : Reach 44071 := rs (se 1 (by rfl) ⟨33053, by rfl⟩) R66107
theorem R44111 : Reach 44111 := rs (se 1 (by rfl) ⟨33083, by rfl⟩) R66167
theorem R44127 : Reach 44127 := rs (se 1 (by rfl) ⟨33095, by rfl⟩) R66191
theorem R44155 : Reach 44155 := rs (se 1 (by rfl) ⟨33116, by rfl⟩) R66233
theorem R44207 : Reach 44207 := rs (se 1 (by rfl) ⟨33155, by rfl⟩) R66311
theorem R44231 : Reach 44231 := rs (se 1 (by rfl) ⟨33173, by rfl⟩) R66347
theorem R44251 : Reach 44251 := rs (se 1 (by rfl) ⟨33188, by rfl⟩) R66377
theorem R44327 : Reach 44327 := rs (se 1 (by rfl) ⟨33245, by rfl⟩) R66491
theorem R44367 : Reach 44367 := rs (se 1 (by rfl) ⟨33275, by rfl⟩) R66551
theorem R44383 : Reach 44383 := rs (se 1 (by rfl) ⟨33287, by rfl⟩) R66575
theorem R44411 : Reach 44411 := rs (se 1 (by rfl) ⟨33308, by rfl⟩) R66617
theorem R44463 : Reach 44463 := rs (se 1 (by rfl) ⟨33347, by rfl⟩) R66695
theorem R44487 : Reach 44487 := rs (se 1 (by rfl) ⟨33365, by rfl⟩) R66731
theorem R142793 : Reach 142793 := rs (se 2 (by rfl) ⟨53547, by rfl⟩) R107095
theorem R44507 : Reach 44507 := rs (se 1 (by rfl) ⟨33380, by rfl⟩) R66761
theorem R77321 : Reach 77321 := rs (se 2 (by rfl) ⟨28995, by rfl⟩) R57991
theorem R110119 : Reach 110119 := rs (se 1 (by rfl) ⟨82589, by rfl⟩) R165179
theorem R44583 : Reach 44583 := rs (se 1 (by rfl) ⟨33437, by rfl⟩) R66875
theorem R601667 : Reach 601667 := rs (se 1 (by rfl) ⟨451250, by rfl⟩) R902501
theorem R44623 : Reach 44623 := rs (se 1 (by rfl) ⟨33467, by rfl⟩) R66935
theorem R44639 : Reach 44639 := rs (se 1 (by rfl) ⟨33479, by rfl⟩) R66959
theorem R44667 : Reach 44667 := rs (se 1 (by rfl) ⟨33500, by rfl⟩) R67001
theorem R77483 : Reach 77483 := rs (se 1 (by rfl) ⟨58112, by rfl⟩) R116225
theorem R44719 : Reach 44719 := rs (se 1 (by rfl) ⟨33539, by rfl⟩) R67079
theorem R44743 : Reach 44743 := rs (se 1 (by rfl) ⟨33557, by rfl⟩) R67115
theorem R44763 : Reach 44763 := rs (se 1 (by rfl) ⟨33572, by rfl⟩) R67145
theorem R44839 : Reach 44839 := rs (se 1 (by rfl) ⟨33629, by rfl⟩) R67259
theorem R143147 : Reach 143147 := rs (se 1 (by rfl) ⟨107360, by rfl⟩) R214721
theorem R44879 : Reach 44879 := rs (se 1 (by rfl) ⟨33659, by rfl⟩) R67319
theorem R44895 : Reach 44895 := rs (se 1 (by rfl) ⟨33671, by rfl⟩) R67343
theorem R110443 : Reach 110443 := rs (se 1 (by rfl) ⟨82832, by rfl⟩) R165665
theorem R44923 : Reach 44923 := rs (se 1 (by rfl) ⟨33692, by rfl⟩) R67385
theorem R44975 : Reach 44975 := rs (se 1 (by rfl) ⟨33731, by rfl⟩) R67463
theorem R44999 : Reach 44999 := rs (se 1 (by rfl) ⟨33749, by rfl⟩) R67499
theorem R45019 : Reach 45019 := rs (se 1 (by rfl) ⟨33764, by rfl⟩) R67529
theorem R45095 : Reach 45095 := rs (se 1 (by rfl) ⟨33821, by rfl⟩) R67643
theorem R77881 : Reach 77881 := rs (se 2 (by rfl) ⟨29205, by rfl⟩) R58411
theorem R45135 : Reach 45135 := rs (se 1 (by rfl) ⟨33851, by rfl⟩) R67703
theorem R45151 : Reach 45151 := rs (se 1 (by rfl) ⟨33863, by rfl⟩) R67727
theorem R667763 : Reach 667763 := rs (se 1 (by rfl) ⟨500822, by rfl⟩) R1001645
theorem R45179 : Reach 45179 := rs (se 1 (by rfl) ⟨33884, by rfl⟩) R67769
theorem R45231 : Reach 45231 := rs (se 1 (by rfl) ⟨33923, by rfl⟩) R67847
theorem R45255 : Reach 45255 := rs (se 1 (by rfl) ⟨33941, by rfl⟩) R67883
theorem R78023 : Reach 78023 := rs (se 1 (by rfl) ⟨58517, by rfl⟩) R117035
theorem R45275 : Reach 45275 := rs (se 1 (by rfl) ⟨33956, by rfl⟩) R67913
theorem R45351 : Reach 45351 := rs (se 1 (by rfl) ⟨34013, by rfl⟩) R68027
theorem R45391 : Reach 45391 := rs (se 1 (by rfl) ⟨34043, by rfl⟩) R68087
theorem R45407 : Reach 45407 := rs (se 1 (by rfl) ⟨34055, by rfl⟩) R68111
theorem R78185 : Reach 78185 := rs (se 2 (by rfl) ⟨29319, by rfl⟩) R58639
theorem R45487 : Reach 45487 := rs (se 1 (by rfl) ⟨34115, by rfl⟩) R68231
theorem R45531 : Reach 45531 := rs (se 1 (by rfl) ⟨34148, by rfl⟩) R68297
theorem R111091 : Reach 111091 := rs (se 1 (by rfl) ⟨83318, by rfl⟩) R166637
theorem R45607 : Reach 45607 := rs (se 1 (by rfl) ⟨34205, by rfl⟩) R68411
theorem R45647 : Reach 45647 := rs (se 1 (by rfl) ⟨34235, by rfl⟩) R68471
theorem R45691 : Reach 45691 := rs (se 1 (by rfl) ⟨34268, by rfl⟩) R68537
theorem R45767 : Reach 45767 := rs (se 1 (by rfl) ⟨34325, by rfl⟩) R68651
theorem R78583 : Reach 78583 := rs (se 1 (by rfl) ⟨58937, by rfl⟩) R117875
theorem R45919 : Reach 45919 := rs (se 1 (by rfl) ⟨34439, by rfl⟩) R68879
theorem R45999 : Reach 45999 := rs (se 1 (by rfl) ⟨34499, by rfl⟩) R68999
theorem R78779 : Reach 78779 := rs (se 1 (by rfl) ⟨59084, by rfl⟩) R118169
theorem R46043 : Reach 46043 := rs (se 1 (by rfl) ⟨34532, by rfl⟩) R69065
theorem R46119 : Reach 46119 := rs (se 1 (by rfl) ⟨34589, by rfl⟩) R69179
theorem R78887 : Reach 78887 := rs (se 1 (by rfl) ⟨59165, by rfl⟩) R118331
theorem R46159 : Reach 46159 := rs (se 1 (by rfl) ⟨34619, by rfl⟩) R69239
theorem R46203 : Reach 46203 := rs (se 1 (by rfl) ⟨34652, by rfl⟩) R69305
theorem R46279 : Reach 46279 := rs (se 1 (by rfl) ⟨34709, by rfl⟩) R69419
theorem R79177 : Reach 79177 := rs (se 2 (by rfl) ⟨29691, by rfl⟩) R59383
theorem R46431 : Reach 46431 := rs (se 1 (by rfl) ⟨34823, by rfl⟩) R69647
theorem R79211 : Reach 79211 := rs (se 1 (by rfl) ⟨59408, by rfl⟩) R118817
theorem R79265 : Reach 79265 := rs (se 2 (by rfl) ⟨29724, by rfl⟩) R59449
theorem R46511 : Reach 46511 := rs (se 1 (by rfl) ⟨34883, by rfl⟩) R69767
theorem R46555 : Reach 46555 := rs (se 1 (by rfl) ⟨34916, by rfl⟩) R69833
theorem R46631 : Reach 46631 := rs (se 1 (by rfl) ⟨34973, by rfl⟩) R69947
theorem R46671 : Reach 46671 := rs (se 1 (by rfl) ⟨35003, by rfl⟩) R70007
theorem R112225 : Reach 112225 := rs (se 2 (by rfl) ⟨42084, by rfl⟩) R84169
theorem R46715 : Reach 46715 := rs (se 1 (by rfl) ⟨35036, by rfl⟩) R70073
theorem R46791 : Reach 46791 := rs (se 1 (by rfl) ⟨35093, by rfl⟩) R70187
theorem R46943 : Reach 46943 := rs (se 1 (by rfl) ⟨35207, by rfl⟩) R70415
theorem R47023 : Reach 47023 := rs (se 1 (by rfl) ⟨35267, by rfl⟩) R70535
theorem R47067 : Reach 47067 := rs (se 1 (by rfl) ⟨35300, by rfl⟩) R70601
theorem R637085 : Reach 637085 := rs (se 3 (by rfl) ⟨119453, by rfl⟩) R238907
theorem R145675 : Reach 145675 := rs (se 1 (by rfl) ⟨109256, by rfl⟩) R218513
theorem R145907 : Reach 145907 := rs (se 1 (by rfl) ⟨109430, by rfl⟩) R218861
theorem R113177 : Reach 113177 := rs (se 2 (by rfl) ⟨42441, by rfl⟩) R84883
theorem R146447 : Reach 146447 := rs (se 1 (by rfl) ⟨109835, by rfl⟩) R219671
theorem R113683 : Reach 113683 := rs (se 1 (by rfl) ⟨85262, by rfl⟩) R170525
theorem R48559 : Reach 48559 := rs (se 1 (by rfl) ⟨36419, by rfl⟩) R72839
theorem R147041 : Reach 147041 := rs (se 2 (by rfl) ⟨55140, by rfl⟩) R110281
theorem R310931 : Reach 310931 := rs (se 1 (by rfl) ⟨233198, by rfl⟩) R466397
theorem R48991 : Reach 48991 := rs (se 1 (by rfl) ⟨36743, by rfl⟩) R73487
theorem R114767 : Reach 114767 := rs (se 1 (by rfl) ⟨86075, by rfl⟩) R172151
theorem R82043 : Reach 82043 := rs (se 1 (by rfl) ⟨61532, by rfl⟩) R123065
theorem R49351 : Reach 49351 := rs (se 1 (by rfl) ⟨37013, by rfl⟩) R74027
theorem R606437 : Reach 606437 := rs (se 4 (by rfl) ⟨56853, by rfl⟩) R113707
theorem R82271 : Reach 82271 := rs (se 1 (by rfl) ⟨61703, by rfl⟩) R123407
theorem R82529 : Reach 82529 := rs (se 2 (by rfl) ⟨30948, by rfl⟩) R61897
theorem R2507395 : Reach 2507395 := rs (se 1 (by rfl) ⟨1880546, by rfl⟩) R3761093
theorem R115415 : Reach 115415 := rs (se 1 (by rfl) ⟨86561, by rfl⟩) R173123
theorem R82795 : Reach 82795 := rs (se 1 (by rfl) ⟨62096, by rfl⟩) R124193
theorem R836527 : Reach 836527 := rs (se 1 (by rfl) ⟨627395, by rfl⟩) R1254791
theorem R148499 : Reach 148499 := rs (se 1 (by rfl) ⟨111374, by rfl⟩) R222749
theorem R50215 : Reach 50215 := rs (se 1 (by rfl) ⟨37661, by rfl⟩) R75323
theorem R115769 : Reach 115769 := rs (se 2 (by rfl) ⟨43413, by rfl⟩) R86827
theorem R279845 : Reach 279845 := rs (se 4 (by rfl) ⟨26235, by rfl⟩) R52471
theorem R148823 : Reach 148823 := rs (se 1 (by rfl) ⟨111617, by rfl⟩) R223235
theorem R116093 : Reach 116093 := rs (se 3 (by rfl) ⟨21767, by rfl⟩) R43535
theorem R345545 : Reach 345545 := rs (se 2 (by rfl) ⟨129579, by rfl⟩) R259159
theorem R280253 : Reach 280253 := rs (se 3 (by rfl) ⟨52547, by rfl⟩) R105095
theorem R247495 : Reach 247495 := rs (se 1 (by rfl) ⟨185621, by rfl⟩) R371243
theorem R149435 : Reach 149435 := rs (se 1 (by rfl) ⟨112076, by rfl⟩) R224153
theorem R247823 : Reach 247823 := rs (se 1 (by rfl) ⟨185867, by rfl⟩) R371735
theorem R83987 : Reach 83987 := rs (se 1 (by rfl) ⟨62990, by rfl⟩) R125981
theorem R84215 : Reach 84215 := rs (se 1 (by rfl) ⟨63161, by rfl⟩) R126323
theorem R510209 : Reach 510209 := rs (se 2 (by rfl) ⟨191328, by rfl⟩) R382657
theorem R379241 : Reach 379241 := rs (se 2 (by rfl) ⟨142215, by rfl⟩) R284431
theorem R149903 : Reach 149903 := rs (se 1 (by rfl) ⟨112427, by rfl⟩) R224855
theorem R51835 : Reach 51835 := rs (se 1 (by rfl) ⟨38876, by rfl⟩) R77753
theorem R150227 : Reach 150227 := rs (se 1 (by rfl) ⟨112670, by rfl⟩) R225341
theorem R84691 : Reach 84691 := rs (se 1 (by rfl) ⟨63518, by rfl⟩) R127037
theorem R52303 : Reach 52303 := rs (se 1 (by rfl) ⟨39227, by rfl⟩) R78455
theorem R118007 : Reach 118007 := rs (se 1 (by rfl) ⟨88505, by rfl⟩) R177011
theorem R52663 : Reach 52663 := rs (se 1 (by rfl) ⟨39497, by rfl⟩) R78995
theorem R52699 : Reach 52699 := rs (se 1 (by rfl) ⟨39524, by rfl⟩) R79049
theorem R85627 : Reach 85627 := rs (se 1 (by rfl) ⟨64220, by rfl⟩) R128441
theorem R85855 : Reach 85855 := rs (se 1 (by rfl) ⟨64391, by rfl⟩) R128783
theorem R151415 : Reach 151415 := rs (se 1 (by rfl) ⟨113561, by rfl⟩) R227123
theorem R282503 : Reach 282503 := rs (se 1 (by rfl) ⟨211877, by rfl⟩) R423755
theorem R151631 : Reach 151631 := rs (se 1 (by rfl) ⟨113723, by rfl⟩) R227447
theorem R86113 : Reach 86113 := rs (se 2 (by rfl) ⟨32292, by rfl⟩) R64585
theorem R4837637 : Reach 4837637 := rs (se 4 (by rfl) ⟨453528, by rfl⟩) R907057
theorem R86447 : Reach 86447 := rs (se 1 (by rfl) ⟨64835, by rfl⟩) R129671
theorem R152009 : Reach 152009 := rs (se 2 (by rfl) ⟨57003, by rfl⟩) R114007
theorem R152027 : Reach 152027 := rs (se 1 (by rfl) ⟨114020, by rfl⟩) R228041
theorem R152279 : Reach 152279 := rs (se 1 (by rfl) ⟨114209, by rfl⟩) R228419
theorem R316163 : Reach 316163 := rs (se 1 (by rfl) ⟨237122, by rfl⟩) R474245
theorem R119713 : Reach 119713 := rs (se 2 (by rfl) ⟨44892, by rfl⟩) R89785
theorem R152495 : Reach 152495 := rs (se 1 (by rfl) ⟨114371, by rfl⟩) R228743
theorem R316381 : Reach 316381 := rs (se 3 (by rfl) ⟨59321, by rfl⟩) R118643
theorem R1692737 : Reach 1692737 := rs (se 2 (by rfl) ⟨634776, by rfl⟩) R1269553
theorem R284147 : Reach 284147 := rs (se 1 (by rfl) ⟨213110, by rfl⟩) R426221
theorem R87571 : Reach 87571 := rs (se 1 (by rfl) ⟨65678, by rfl⟩) R131357
theorem R87799 : Reach 87799 := rs (se 1 (by rfl) ⟨65849, by rfl⟩) R131699
theorem R88103 : Reach 88103 := rs (se 1 (by rfl) ⟨66077, by rfl⟩) R132155
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R55495 : Reach 55495 := rs (se 1 (by rfl) ⟨41621, by rfl⟩) R83243
theorem R711017 : Reach 711017 := rs (se 2 (by rfl) ⟨266631, by rfl⟩) R533263
theorem R809453 : Reach 809453 := rs (se 3 (by rfl) ⟨151772, by rfl⟩) R303545
theorem R88699 : Reach 88699 := rs (se 1 (by rfl) ⟨66524, by rfl⟩) R133049
theorem R219833 : Reach 219833 := rs (se 2 (by rfl) ⟨82437, by rfl⟩) R164875
theorem R580445 : Reach 580445 := rs (se 3 (by rfl) ⟨108833, by rfl⟩) R217667
theorem R711665 : Reach 711665 := rs (se 2 (by rfl) ⟨266874, by rfl⟩) R533749
theorem R154871 : Reach 154871 := rs (se 1 (by rfl) ⟨116153, by rfl⟩) R232307
theorem R1072397 : Reach 1072397 := rs (se 3 (by rfl) ⟨201074, by rfl⟩) R402149
theorem R89417 : Reach 89417 := rs (se 2 (by rfl) ⟨33531, by rfl⟩) R67063
theorem R253327 : Reach 253327 := rs (se 1 (by rfl) ⟨189995, by rfl⟩) R379991
theorem R155195 : Reach 155195 := rs (se 1 (by rfl) ⟨116396, by rfl⟩) R232793
theorem R220819 : Reach 220819 := rs (se 1 (by rfl) ⟨165614, by rfl⟩) R331229
theorem R351959 : Reach 351959 := rs (se 1 (by rfl) ⟨263969, by rfl⟩) R527939
theorem R286429 : Reach 286429 := rs (se 3 (by rfl) ⟨53705, by rfl⟩) R107411
theorem R188203 : Reach 188203 := rs (se 1 (by rfl) ⟨141152, by rfl⟩) R282305
theorem R155465 : Reach 155465 := rs (se 2 (by rfl) ⟨58299, by rfl⟩) R116599
theorem R286651 : Reach 286651 := rs (se 1 (by rfl) ⟨214988, by rfl⟩) R429977
theorem R90209 : Reach 90209 := rs (se 2 (by rfl) ⟨33828, by rfl⟩) R67657
theorem R155843 : Reach 155843 := rs (se 1 (by rfl) ⟨116882, by rfl⟩) R233765
theorem R155915 : Reach 155915 := rs (se 1 (by rfl) ⟨116936, by rfl⟩) R233873
theorem R549179 : Reach 549179 := rs (se 1 (by rfl) ⟨411884, by rfl⟩) R823769
theorem R778571 : Reach 778571 := rs (se 1 (by rfl) ⟨583928, by rfl⟩) R1167857
theorem R188801 : Reach 188801 := rs (se 2 (by rfl) ⟨70800, by rfl⟩) R141601
theorem R57935 : Reach 57935 := rs (se 1 (by rfl) ⟨43451, by rfl⟩) R86903
theorem R156599 : Reach 156599 := rs (se 1 (by rfl) ⟨117449, by rfl⟩) R234899
theorem R91535 : Reach 91535 := rs (se 1 (by rfl) ⟨68651, by rfl⟩) R137303
theorem R58843 : Reach 58843 := rs (se 1 (by rfl) ⟨44132, by rfl⟩) R88265
theorem R157193 : Reach 157193 := rs (se 2 (by rfl) ⟨58947, by rfl⟩) R117895
theorem R190201 : Reach 190201 := rs (se 2 (by rfl) ⟨71325, by rfl⟩) R142651
theorem R59231 : Reach 59231 := rs (se 1 (by rfl) ⟨44423, by rfl⟩) R88847
theorem R157601 : Reach 157601 := rs (se 2 (by rfl) ⟨59100, by rfl⟩) R118201
theorem R157715 : Reach 157715 := rs (se 1 (by rfl) ⟨118286, by rfl⟩) R236573
theorem R747863 : Reach 747863 := rs (se 1 (by rfl) ⟨560897, by rfl⟩) R1121795
theorem R158057 : Reach 158057 := rs (se 2 (by rfl) ⟨59271, by rfl⟩) R118543
theorem R125479 : Reach 125479 := rs (se 1 (by rfl) ⟨94109, by rfl⟩) R188219
theorem R125651 : Reach 125651 := rs (se 1 (by rfl) ⟨94238, by rfl⟩) R188477
theorem R191261 : Reach 191261 := rs (se 3 (by rfl) ⟨35861, by rfl⟩) R71723
theorem R1207223 : Reach 1207223 := rs (se 1 (by rfl) ⟨905417, by rfl⟩) R1810835
theorem R158651 : Reach 158651 := rs (se 1 (by rfl) ⟨118988, by rfl⟩) R237977
theorem R225017 : Reach 225017 := rs (se 2 (by rfl) ⟨84381, by rfl⟩) R168763
theorem R61177 : Reach 61177 := rs (se 2 (by rfl) ⟨22941, by rfl⟩) R45883
theorem R126983 : Reach 126983 := rs (se 1 (by rfl) ⟨95237, by rfl⟩) R190475
theorem R192593 : Reach 192593 := rs (se 2 (by rfl) ⟨72222, by rfl⟩) R144445
theorem R225665 : Reach 225665 := rs (se 2 (by rfl) ⟨84624, by rfl⟩) R169249
theorem R881425 : Reach 881425 := rs (se 2 (by rfl) ⟨330534, by rfl⟩) R661069
theorem R62303 : Reach 62303 := rs (se 1 (by rfl) ⟨46727, by rfl⟩) R93455
theorem R914327 : Reach 914327 := rs (se 1 (by rfl) ⟨685745, by rfl⟩) R1371491
theorem R226475 : Reach 226475 := rs (se 1 (by rfl) ⟨169856, by rfl⟩) R339713
theorem R554201 : Reach 554201 := rs (se 2 (by rfl) ⟨207825, by rfl⟩) R415651
theorem R587209 : Reach 587209 := rs (se 2 (by rfl) ⟨220203, by rfl⟩) R440407
theorem R226961 : Reach 226961 := rs (se 2 (by rfl) ⟨85110, by rfl⟩) R170221
theorem R194575 : Reach 194575 := rs (se 1 (by rfl) ⟨145931, by rfl⟩) R291863
theorem R1112453 : Reach 1112453 := rs (se 4 (by rfl) ⟨104292, by rfl⟩) R208585
theorem R588185 : Reach 588185 := rs (se 2 (by rfl) ⟨220569, by rfl⟩) R441139
theorem R63919 : Reach 63919 := rs (se 1 (by rfl) ⟨47939, by rfl⟩) R95879
theorem R260617 : Reach 260617 := rs (se 2 (by rfl) ⟨97731, by rfl⟩) R195463
theorem R2423317 : Reach 2423317 := rs (se 6 (by rfl) ⟨56796, by rfl⟩) R113593
theorem R359113 : Reach 359113 := rs (se 2 (by rfl) ⟨134667, by rfl⟩) R269335
theorem R654155 : Reach 654155 := rs (se 1 (by rfl) ⟨490616, by rfl⟩) R981233
theorem R129899 : Reach 129899 := rs (se 1 (by rfl) ⟨97424, by rfl⟩) R194849
theorem R359315 : Reach 359315 := rs (se 1 (by rfl) ⟨269486, by rfl⟩) R538973
theorem R97199 : Reach 97199 := rs (se 1 (by rfl) ⟨72899, by rfl⟩) R145799
theorem R97451 : Reach 97451 := rs (se 1 (by rfl) ⟨73088, by rfl⟩) R146177
theorem R64943 : Reach 64943 := rs (se 1 (by rfl) ⟨48707, by rfl⟩) R97415
theorem R65033 : Reach 65033 := rs (se 2 (by rfl) ⟨24387, by rfl⟩) R48775
theorem R65063 : Reach 65063 := rs (se 1 (by rfl) ⟨48797, by rfl⟩) R97595
theorem R65147 : Reach 65147 := rs (se 1 (by rfl) ⟨48860, by rfl⟩) R97721
theorem R360125 : Reach 360125 := rs (se 3 (by rfl) ⟨67523, by rfl⟩) R135047
theorem R97991 : Reach 97991 := rs (se 1 (by rfl) ⟨73493, by rfl⟩) R146987
theorem R65273 : Reach 65273 := rs (se 2 (by rfl) ⟨24477, by rfl⟩) R48955
theorem R65375 : Reach 65375 := rs (se 1 (by rfl) ⟨49031, by rfl⟩) R98063
theorem R65387 : Reach 65387 := rs (se 1 (by rfl) ⟨49040, by rfl⟩) R98081
theorem R229229 : Reach 229229 := rs (se 3 (by rfl) ⟨42980, by rfl⟩) R85961
theorem R262075 : Reach 262075 := rs (se 1 (by rfl) ⟨196556, by rfl⟩) R393113
theorem R65801 : Reach 65801 := rs (se 2 (by rfl) ⟨24675, by rfl⟩) R49351
theorem R65903 : Reach 65903 := rs (se 1 (by rfl) ⟨49427, by rfl⟩) R98855
theorem R262601 : Reach 262601 := rs (se 2 (by rfl) ⟨98475, by rfl⟩) R196951
theorem R66043 : Reach 66043 := rs (se 1 (by rfl) ⟨49532, by rfl⟩) R99065
theorem R66119 : Reach 66119 := rs (se 1 (by rfl) ⟨49589, by rfl⟩) R99179
theorem R66155 : Reach 66155 := rs (se 1 (by rfl) ⟨49616, by rfl⟩) R99233
theorem R98999 : Reach 98999 := rs (se 1 (by rfl) ⟨74249, by rfl⟩) R148499
theorem R66271 : Reach 66271 := rs (se 1 (by rfl) ⟨49703, by rfl⟩) R99407
theorem R66383 : Reach 66383 := rs (se 1 (by rfl) ⟨49787, by rfl⟩) R99575
theorem R3343193 : Reach 3343193 := rs (se 2 (by rfl) ⟨1253697, by rfl⟩) R2507395
theorem R99215 : Reach 99215 := rs (se 1 (by rfl) ⟨74411, by rfl⟩) R148823
theorem R230363 : Reach 230363 := rs (se 1 (by rfl) ⟨172772, by rfl⟩) R345545
theorem R230525 : Reach 230525 := rs (se 3 (by rfl) ⟨43223, by rfl⟩) R86447
theorem R66779 : Reach 66779 := rs (se 1 (by rfl) ⟨50084, by rfl⟩) R100169
theorem R1115369 : Reach 1115369 := rs (se 2 (by rfl) ⟨418263, by rfl⟩) R836527
theorem R99577 : Reach 99577 := rs (se 2 (by rfl) ⟨37341, by rfl⟩) R74683
theorem R99623 : Reach 99623 := rs (se 1 (by rfl) ⟨74717, by rfl⟩) R149435
theorem R165215 : Reach 165215 := rs (se 1 (by rfl) ⟨123911, by rfl⟩) R247823
theorem R263533 : Reach 263533 := rs (se 3 (by rfl) ⟨49412, by rfl⟩) R98825
theorem R66953 : Reach 66953 := rs (se 2 (by rfl) ⟨25107, by rfl⟩) R50215
theorem R230849 : Reach 230849 := rs (se 2 (by rfl) ⟨86568, by rfl⟩) R173137
theorem R99935 : Reach 99935 := rs (se 1 (by rfl) ⟨74951, by rfl⟩) R149903
theorem R67307 : Reach 67307 := rs (se 1 (by rfl) ⟨50480, by rfl⟩) R100961
theorem R100151 : Reach 100151 := rs (se 1 (by rfl) ⟨75113, by rfl⟩) R150227
theorem R722819 : Reach 722819 := rs (se 1 (by rfl) ⟨542114, by rfl⟩) R1084229
theorem R67535 : Reach 67535 := rs (se 1 (by rfl) ⟨50651, by rfl⟩) R101303
theorem R198607 : Reach 198607 := rs (se 1 (by rfl) ⟨148955, by rfl⟩) R297911
theorem R395279 : Reach 395279 := rs (se 1 (by rfl) ⟨296459, by rfl⟩) R592919
theorem R100457 : Reach 100457 := rs (se 2 (by rfl) ⟨37671, by rfl⟩) R75343
theorem R166141 : Reach 166141 := rs (se 3 (by rfl) ⟨31151, by rfl⟩) R62303
theorem R329993 : Reach 329993 := rs (se 2 (by rfl) ⟨123747, by rfl⟩) R247495
theorem R67931 : Reach 67931 := rs (se 1 (by rfl) ⟨50948, by rfl⟩) R101897
theorem R68159 : Reach 68159 := rs (se 1 (by rfl) ⟨51119, by rfl⟩) R102239
theorem R100943 : Reach 100943 := rs (se 1 (by rfl) ⟨75707, by rfl⟩) R151415
theorem R68279 : Reach 68279 := rs (se 1 (by rfl) ⟨51209, by rfl⟩) R102419
theorem R101087 : Reach 101087 := rs (se 1 (by rfl) ⟨75815, by rfl⟩) R151631
theorem R68507 : Reach 68507 := rs (se 1 (by rfl) ⟨51380, by rfl⟩) R102761
theorem R101339 : Reach 101339 := rs (se 1 (by rfl) ⟨76004, by rfl⟩) R152009
theorem R101351 : Reach 101351 := rs (se 1 (by rfl) ⟨76013, by rfl⟩) R152027
theorem R199667 : Reach 199667 := rs (se 1 (by rfl) ⟨149750, by rfl⟩) R299501
theorem R363521 : Reach 363521 := rs (se 2 (by rfl) ⟨136320, by rfl⟩) R272641
theorem R101519 : Reach 101519 := rs (se 1 (by rfl) ⟨76139, by rfl⟩) R152279
theorem R101609 : Reach 101609 := rs (se 2 (by rfl) ⟨38103, by rfl⟩) R76207
theorem R101663 : Reach 101663 := rs (se 1 (by rfl) ⟨76247, by rfl⟩) R152495
theorem R68903 : Reach 68903 := rs (se 1 (by rfl) ⟨51677, by rfl⟩) R103355
theorem R68987 : Reach 68987 := rs (se 1 (by rfl) ⟨51740, by rfl⟩) R103481
theorem R167305 : Reach 167305 := rs (se 2 (by rfl) ⟨62739, by rfl⟩) R125479
theorem R69113 : Reach 69113 := rs (se 2 (by rfl) ⟨25917, by rfl⟩) R51835
theorem R69215 : Reach 69215 := rs (se 1 (by rfl) ⟨51911, by rfl⟩) R103823
theorem R265837 : Reach 265837 := rs (se 3 (by rfl) ⟨49844, by rfl⟩) R99689
theorem R69383 : Reach 69383 := rs (se 1 (by rfl) ⟨52037, by rfl⟩) R104075
theorem R102185 : Reach 102185 := rs (se 2 (by rfl) ⟨38319, by rfl⟩) R76639
theorem R69431 : Reach 69431 := rs (se 1 (by rfl) ⟨52073, by rfl⟩) R104147
theorem R69737 : Reach 69737 := rs (se 2 (by rfl) ⟨26151, by rfl⟩) R52303
theorem R1249667 : Reach 1249667 := rs (se 1 (by rfl) ⟨937250, by rfl⟩) R1874501
theorem R70055 : Reach 70055 := rs (se 1 (by rfl) ⟨52541, by rfl⟩) R105083
theorem R70139 : Reach 70139 := rs (se 1 (by rfl) ⟨52604, by rfl⟩) R105209
theorem R70217 : Reach 70217 := rs (se 2 (by rfl) ⟨26331, by rfl⟩) R52663
theorem R70265 : Reach 70265 := rs (se 2 (by rfl) ⟨26349, by rfl⟩) R52699
theorem R70319 : Reach 70319 := rs (se 1 (by rfl) ⟨52739, by rfl⟩) R105479
theorem R266975 : Reach 266975 := rs (se 1 (by rfl) ⟨200231, by rfl⟩) R400463
theorem R70367 : Reach 70367 := rs (se 1 (by rfl) ⟨52775, by rfl⟩) R105551
theorem R103247 : Reach 103247 := rs (se 1 (by rfl) ⟨77435, by rfl⟩) R154871
theorem R70571 : Reach 70571 := rs (se 1 (by rfl) ⟨52928, by rfl⟩) R105857
theorem R70631 : Reach 70631 := rs (se 1 (by rfl) ⟨52973, by rfl⟩) R105947
theorem R103463 : Reach 103463 := rs (se 1 (by rfl) ⟨77597, by rfl⟩) R155195
theorem R103643 : Reach 103643 := rs (se 1 (by rfl) ⟨77732, by rfl⟩) R155465
theorem R103841 : Reach 103841 := rs (se 2 (by rfl) ⟨38940, by rfl⟩) R77881
theorem R103895 : Reach 103895 := rs (se 1 (by rfl) ⟨77921, by rfl⟩) R155843
theorem R103943 : Reach 103943 := rs (se 1 (by rfl) ⟨77957, by rfl⟩) R155915
theorem R366119 : Reach 366119 := rs (se 1 (by rfl) ⟨274589, by rfl⟩) R549179
theorem R202427 : Reach 202427 := rs (se 1 (by rfl) ⟨151820, by rfl⟩) R303641
theorem R104399 : Reach 104399 := rs (se 1 (by rfl) ⟨78299, by rfl⟩) R156599
theorem R530711 : Reach 530711 := rs (se 1 (by rfl) ⟨398033, by rfl⟩) R796067
theorem R104777 : Reach 104777 := rs (se 2 (by rfl) ⟨39291, by rfl⟩) R78583
theorem R104795 : Reach 104795 := rs (se 1 (by rfl) ⟨78596, by rfl⟩) R157193
theorem R105067 : Reach 105067 := rs (se 1 (by rfl) ⟨78800, by rfl⟩) R157601
theorem R105143 : Reach 105143 := rs (se 1 (by rfl) ⟨78857, by rfl⟩) R157715
theorem R498575 : Reach 498575 := rs (se 1 (by rfl) ⟨373931, by rfl⟩) R747863
theorem R105371 : Reach 105371 := rs (se 1 (by rfl) ⟨79028, by rfl⟩) R158057
theorem R105569 : Reach 105569 := rs (se 2 (by rfl) ⟨39588, by rfl⟩) R79177
theorem R105767 : Reach 105767 := rs (se 1 (by rfl) ⟨79325, by rfl⟩) R158651
theorem R401111 : Reach 401111 := rs (se 1 (by rfl) ⟨300833, by rfl⟩) R601667
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R73993 : Reach 73993 := rs (se 2 (by rfl) ⟨27747, by rfl⟩) R55495
theorem R2859725 : Reach 2859725 := rs (se 3 (by rfl) ⟨536198, by rfl⟩) R1072397
theorem R369467 : Reach 369467 := rs (se 1 (by rfl) ⟨277100, by rfl⟩) R554201
theorem R75451 : Reach 75451 := rs (se 1 (by rfl) ⟨56588, by rfl⟩) R113177
theorem R337769 : Reach 337769 := rs (se 2 (by rfl) ⟨126663, by rfl⟩) R253327
theorem R436103 : Reach 436103 := rs (se 1 (by rfl) ⟨327077, by rfl⟩) R654155
theorem R239543 : Reach 239543 := rs (se 1 (by rfl) ⟨179657, by rfl⟩) R359315
theorem R43295 : Reach 43295 := rs (se 1 (by rfl) ⟨32471, by rfl⟩) R64943
theorem R43355 : Reach 43355 := rs (se 1 (by rfl) ⟨32516, by rfl⟩) R65033
theorem R43375 : Reach 43375 := rs (se 1 (by rfl) ⟨32531, by rfl⟩) R65063
theorem R43431 : Reach 43431 := rs (se 1 (by rfl) ⟨32573, by rfl⟩) R65147
theorem R207287 : Reach 207287 := rs (se 1 (by rfl) ⟨155465, by rfl⟩) R310931
theorem R240083 : Reach 240083 := rs (se 1 (by rfl) ⟨180062, by rfl⟩) R360125
theorem R43515 : Reach 43515 := rs (se 1 (by rfl) ⟨32636, by rfl⟩) R65273
theorem R43583 : Reach 43583 := rs (se 1 (by rfl) ⟨32687, by rfl⟩) R65375
theorem R43591 : Reach 43591 := rs (se 1 (by rfl) ⟨32693, by rfl⟩) R65387
theorem R43743 : Reach 43743 := rs (se 1 (by rfl) ⟨32807, by rfl⟩) R65615
theorem R76511 : Reach 76511 := rs (se 1 (by rfl) ⟨57383, by rfl⟩) R114767
theorem R240407 : Reach 240407 := rs (se 1 (by rfl) ⟨180305, by rfl⟩) R360611
theorem R43823 : Reach 43823 := rs (se 1 (by rfl) ⟨32867, by rfl⟩) R65735
theorem R404291 : Reach 404291 := rs (se 1 (by rfl) ⟨303218, by rfl⟩) R606437
theorem R43931 : Reach 43931 := rs (se 1 (by rfl) ⟨32948, by rfl⟩) R65897
theorem R43983 : Reach 43983 := rs (se 1 (by rfl) ⟨32987, by rfl⟩) R65975
theorem R44007 : Reach 44007 := rs (se 1 (by rfl) ⟨33005, by rfl⟩) R66011
theorem R76943 : Reach 76943 := rs (se 1 (by rfl) ⟨57707, by rfl⟩) R115415
theorem R44319 : Reach 44319 := rs (se 1 (by rfl) ⟨33239, by rfl⟩) R66479
theorem R44379 : Reach 44379 := rs (se 1 (by rfl) ⟨33284, by rfl⟩) R66569
theorem R44399 : Reach 44399 := rs (se 1 (by rfl) ⟨33299, by rfl⟩) R66599
theorem R77179 : Reach 77179 := rs (se 1 (by rfl) ⟨57884, by rfl⟩) R115769
theorem R44455 : Reach 44455 := rs (se 1 (by rfl) ⟨33341, by rfl⟩) R66683
theorem R44539 : Reach 44539 := rs (se 1 (by rfl) ⟨33404, by rfl⟩) R66809
theorem R44607 : Reach 44607 := rs (se 1 (by rfl) ⟨33455, by rfl⟩) R66911
theorem R44615 : Reach 44615 := rs (se 1 (by rfl) ⟨33461, by rfl⟩) R66923
theorem R77395 : Reach 77395 := rs (se 1 (by rfl) ⟨58046, by rfl⟩) R116093
theorem R44767 : Reach 44767 := rs (se 1 (by rfl) ⟨33575, by rfl⟩) R67151
theorem R44847 : Reach 44847 := rs (se 1 (by rfl) ⟨33635, by rfl⟩) R67271
theorem R110393 : Reach 110393 := rs (se 2 (by rfl) ⟨41397, by rfl⟩) R82795
theorem R44955 : Reach 44955 := rs (se 1 (by rfl) ⟨33716, by rfl⟩) R67433
theorem R45007 : Reach 45007 := rs (se 1 (by rfl) ⟨33755, by rfl⟩) R67511
theorem R45031 : Reach 45031 := rs (se 1 (by rfl) ⟨33773, by rfl⟩) R67547
theorem R340139 : Reach 340139 := rs (se 1 (by rfl) ⟨255104, by rfl⟩) R510209
theorem R45343 : Reach 45343 := rs (se 1 (by rfl) ⟨34007, by rfl⟩) R68015
theorem R45403 : Reach 45403 := rs (se 1 (by rfl) ⟨34052, by rfl⟩) R68105
theorem R45423 : Reach 45423 := rs (se 1 (by rfl) ⟨34067, by rfl⟩) R68135
theorem R45435 : Reach 45435 := rs (se 1 (by rfl) ⟨34076, by rfl⟩) R68153
theorem R45479 : Reach 45479 := rs (se 1 (by rfl) ⟨34109, by rfl⟩) R68219
theorem R45511 : Reach 45511 := rs (se 1 (by rfl) ⟨34133, by rfl⟩) R68267
theorem R45563 : Reach 45563 := rs (se 1 (by rfl) ⟨34172, by rfl⟩) R68345
theorem R45631 : Reach 45631 := rs (se 1 (by rfl) ⟨34223, by rfl⟩) R68447
theorem R45639 : Reach 45639 := rs (se 1 (by rfl) ⟨34229, by rfl⟩) R68459
theorem R45663 : Reach 45663 := rs (se 1 (by rfl) ⟨34247, by rfl⟩) R68495
theorem R78457 : Reach 78457 := rs (se 2 (by rfl) ⟨29421, by rfl⟩) R58843
theorem R45743 : Reach 45743 := rs (se 1 (by rfl) ⟨34307, by rfl⟩) R68615
theorem R45791 : Reach 45791 := rs (se 1 (by rfl) ⟨34343, by rfl⟩) R68687
theorem R45871 : Reach 45871 := rs (se 1 (by rfl) ⟨34403, by rfl⟩) R68807
theorem R176975 : Reach 176975 := rs (se 1 (by rfl) ⟨132731, by rfl⟩) R265463
theorem R45903 : Reach 45903 := rs (se 1 (by rfl) ⟨34427, by rfl⟩) R68855
theorem R78671 : Reach 78671 := rs (se 1 (by rfl) ⟨59003, by rfl⟩) R118007
theorem R45979 : Reach 45979 := rs (se 1 (by rfl) ⟨34484, by rfl⟩) R68969
theorem R46031 : Reach 46031 := rs (se 1 (by rfl) ⟨34523, by rfl⟩) R69047
theorem R46055 : Reach 46055 := rs (se 1 (by rfl) ⟨34541, by rfl⟩) R69083
theorem R111739 : Reach 111739 := rs (se 1 (by rfl) ⟨83804, by rfl⟩) R167609
theorem R177299 : Reach 177299 := rs (se 1 (by rfl) ⟨132974, by rfl⟩) R265949
theorem R46299 : Reach 46299 := rs (se 1 (by rfl) ⟨34724, by rfl⟩) R69449
theorem R46367 : Reach 46367 := rs (se 1 (by rfl) ⟨34775, by rfl⟩) R69551
theorem R46375 : Reach 46375 := rs (se 1 (by rfl) ⟨34781, by rfl⟩) R69563
theorem R46427 : Reach 46427 := rs (se 1 (by rfl) ⟨34820, by rfl⟩) R69641
theorem R46447 : Reach 46447 := rs (se 1 (by rfl) ⟨34835, by rfl⟩) R69671
theorem R46459 : Reach 46459 := rs (se 1 (by rfl) ⟨34844, by rfl⟩) R69689
theorem R46503 : Reach 46503 := rs (se 1 (by rfl) ⟨34877, by rfl⟩) R69755
theorem R46535 : Reach 46535 := rs (se 1 (by rfl) ⟨34901, by rfl⟩) R69803
theorem R374219 : Reach 374219 := rs (se 1 (by rfl) ⟨280664, by rfl⟩) R561329
theorem R46587 : Reach 46587 := rs (se 1 (by rfl) ⟨34940, by rfl⟩) R69881
theorem R3225091 : Reach 3225091 := rs (se 1 (by rfl) ⟨2418818, by rfl⟩) R4837637
theorem R46655 : Reach 46655 := rs (se 1 (by rfl) ⟨34991, by rfl⟩) R69983
theorem R46663 : Reach 46663 := rs (se 1 (by rfl) ⟨34997, by rfl⟩) R69995
theorem R46687 : Reach 46687 := rs (se 1 (by rfl) ⟨35015, by rfl⟩) R70031
theorem R46767 : Reach 46767 := rs (se 1 (by rfl) ⟨35075, by rfl⟩) R70151
theorem R46815 : Reach 46815 := rs (se 1 (by rfl) ⟨35111, by rfl⟩) R70223
theorem R46895 : Reach 46895 := rs (se 1 (by rfl) ⟨35171, by rfl⟩) R70343
theorem R46927 : Reach 46927 := rs (se 1 (by rfl) ⟨35195, by rfl⟩) R70391
theorem R210775 : Reach 210775 := rs (se 1 (by rfl) ⟨158081, by rfl⟩) R316163
theorem R47003 : Reach 47003 := rs (se 1 (by rfl) ⟨35252, by rfl⟩) R70505
theorem R47055 : Reach 47055 := rs (se 1 (by rfl) ⟨35291, by rfl⟩) R70583
theorem R47079 : Reach 47079 := rs (se 1 (by rfl) ⟨35309, by rfl⟩) R70619
theorem R1128491 : Reach 1128491 := rs (se 1 (by rfl) ⟨846368, by rfl⟩) R1692737
theorem R112921 : Reach 112921 := rs (se 2 (by rfl) ⟨42345, by rfl⟩) R84691
theorem R113147 : Reach 113147 := rs (se 1 (by rfl) ⟨84860, by rfl⟩) R169721
theorem R47687 : Reach 47687 := rs (se 1 (by rfl) ⟨35765, by rfl⟩) R71531
theorem R474011 : Reach 474011 := rs (se 1 (by rfl) ⟨355508, by rfl⟩) R711017
theorem R539635 : Reach 539635 := rs (se 1 (by rfl) ⟨404726, by rfl⟩) R809453
theorem R146555 : Reach 146555 := rs (se 1 (by rfl) ⟨109916, by rfl⟩) R219833
theorem R474443 : Reach 474443 := rs (se 1 (by rfl) ⟨355832, by rfl⟩) R711665
theorem R114043 : Reach 114043 := rs (se 1 (by rfl) ⟨85532, by rfl⟩) R171065
theorem R146825 : Reach 146825 := rs (se 2 (by rfl) ⟨55059, by rfl⟩) R110119
theorem R114119 : Reach 114119 := rs (se 1 (by rfl) ⟨85589, by rfl⟩) R171179
theorem R114169 : Reach 114169 := rs (se 2 (by rfl) ⟨42813, by rfl⟩) R85627
theorem R48703 : Reach 48703 := rs (se 1 (by rfl) ⟨36527, by rfl⟩) R73055
theorem R81569 : Reach 81569 := rs (se 2 (by rfl) ⟨30588, by rfl⟩) R61177
theorem R114473 : Reach 114473 := rs (se 2 (by rfl) ⟨42927, by rfl⟩) R85855
theorem R147257 : Reach 147257 := rs (se 2 (by rfl) ⟨55221, by rfl⟩) R110443
theorem R114817 : Reach 114817 := rs (se 2 (by rfl) ⟨43056, by rfl⟩) R86113
theorem R49447 : Reach 49447 := rs (se 1 (by rfl) ⟨37085, by rfl⟩) R74171
theorem R49531 : Reach 49531 := rs (se 1 (by rfl) ⟨37148, by rfl⟩) R74297
theorem R574087 : Reach 574087 := rs (se 1 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R148121 : Reach 148121 := rs (se 2 (by rfl) ⟨55545, by rfl⟩) R111091
theorem R49999 : Reach 49999 := rs (se 1 (by rfl) ⟨37499, by rfl⟩) R74999
theorem R115627 : Reach 115627 := rs (se 1 (by rfl) ⟨86720, by rfl⟩) R173441
theorem R115901 : Reach 115901 := rs (se 3 (by rfl) ⟨21731, by rfl⟩) R43463
theorem R50395 : Reach 50395 := rs (se 1 (by rfl) ⟨37796, by rfl⟩) R75593
theorem R115931 : Reach 115931 := rs (se 1 (by rfl) ⟨86948, by rfl⟩) R173897
theorem R116063 : Reach 116063 := rs (se 1 (by rfl) ⟨87047, by rfl⟩) R174095
theorem R50683 : Reach 50683 := rs (se 1 (by rfl) ⟨38012, by rfl⟩) R76025
theorem R50863 : Reach 50863 := rs (se 1 (by rfl) ⟨38147, by rfl⟩) R76295
theorem R83767 : Reach 83767 := rs (se 1 (by rfl) ⟨62825, by rfl⟩) R125651
theorem R739205 : Reach 739205 := rs (se 4 (by rfl) ⟨69300, by rfl⟩) R138601
theorem R51151 : Reach 51151 := rs (se 1 (by rfl) ⟨38363, by rfl⟩) R76727
theorem R804815 : Reach 804815 := rs (se 1 (by rfl) ⟨603611, by rfl⟩) R1207223
theorem R116761 : Reach 116761 := rs (se 2 (by rfl) ⟨43785, by rfl⟩) R87571
theorem R149633 : Reach 149633 := rs (se 2 (by rfl) ⟨56112, by rfl⟩) R112225
theorem R117065 : Reach 117065 := rs (se 2 (by rfl) ⟨43899, by rfl⟩) R87799
theorem R51547 : Reach 51547 := rs (se 1 (by rfl) ⟨38660, by rfl⟩) R77321
theorem R51655 : Reach 51655 := rs (se 1 (by rfl) ⟨38741, by rfl⟩) R77483
theorem R248293 : Reach 248293 := rs (se 4 (by rfl) ⟨23277, by rfl⟩) R46555
theorem R150011 : Reach 150011 := rs (se 1 (by rfl) ⟨112508, by rfl⟩) R225017
theorem R84655 : Reach 84655 := rs (se 1 (by rfl) ⟨63491, by rfl⟩) R126983
theorem R445175 : Reach 445175 := rs (se 1 (by rfl) ⟨333881, by rfl⟩) R667763
theorem R52015 : Reach 52015 := rs (se 1 (by rfl) ⟨39011, by rfl⟩) R78023
theorem R52123 : Reach 52123 := rs (se 1 (by rfl) ⟨39092, by rfl⟩) R78185
theorem R150443 : Reach 150443 := rs (se 1 (by rfl) ⟨112832, by rfl⟩) R225665
theorem R85225 : Reach 85225 := rs (se 2 (by rfl) ⟨31959, by rfl⟩) R63919
theorem R609551 : Reach 609551 := rs (se 1 (by rfl) ⟨457163, by rfl⟩) R914327
theorem R52519 : Reach 52519 := rs (se 1 (by rfl) ⟨39389, by rfl⟩) R78779
theorem R347489 : Reach 347489 := rs (se 2 (by rfl) ⟨130308, by rfl⟩) R260617
theorem R52591 : Reach 52591 := rs (se 1 (by rfl) ⟨39443, by rfl⟩) R78887
theorem R3231089 : Reach 3231089 := rs (se 2 (by rfl) ⟨1211658, by rfl⟩) R2423317
theorem R150983 : Reach 150983 := rs (se 1 (by rfl) ⟨113237, by rfl⟩) R226475
theorem R118265 : Reach 118265 := rs (se 2 (by rfl) ⟨44349, by rfl⟩) R88699
theorem R52807 : Reach 52807 := rs (se 1 (by rfl) ⟨39605, by rfl⟩) R79211
theorem R478817 : Reach 478817 := rs (se 2 (by rfl) ⟨179556, by rfl⟩) R359113
theorem R52843 : Reach 52843 := rs (se 1 (by rfl) ⟨39632, by rfl⟩) R79265
theorem R151307 : Reach 151307 := rs (se 1 (by rfl) ⟨113480, by rfl⟩) R226961
theorem R118685 : Reach 118685 := rs (se 3 (by rfl) ⟨22253, by rfl⟩) R44507
theorem R151577 : Reach 151577 := rs (se 2 (by rfl) ⟨56841, by rfl⟩) R113683
theorem R741635 : Reach 741635 := rs (se 1 (by rfl) ⟨556226, by rfl⟩) R1112453
theorem R938557 : Reach 938557 := rs (se 3 (by rfl) ⟨175979, by rfl⟩) R351959
theorem R86599 : Reach 86599 := rs (se 1 (by rfl) ⟨64949, by rfl⟩) R129899
theorem R381905 : Reach 381905 := rs (se 2 (by rfl) ⟨143214, by rfl⟩) R286429
theorem R250937 : Reach 250937 := rs (se 2 (by rfl) ⟨94101, by rfl⟩) R188203
theorem R152819 : Reach 152819 := rs (se 1 (by rfl) ⟨114614, by rfl⟩) R229229
theorem R382201 : Reach 382201 := rs (se 2 (by rfl) ⟨143325, by rfl⟩) R286651
theorem R349433 : Reach 349433 := rs (se 2 (by rfl) ⟨131037, by rfl⟩) R262075
theorem R152927 : Reach 152927 := rs (se 1 (by rfl) ⟨114695, by rfl⟩) R229391
theorem R87419 : Reach 87419 := rs (se 1 (by rfl) ⟨65564, by rfl⟩) R131129
theorem R54695 : Reach 54695 := rs (se 1 (by rfl) ⟨41021, by rfl⟩) R82043
theorem R54847 : Reach 54847 := rs (se 1 (by rfl) ⟨41135, by rfl⟩) R82271
theorem R55019 : Reach 55019 := rs (se 1 (by rfl) ⟨41264, by rfl⟩) R82529
theorem R186563 : Reach 186563 := rs (se 1 (by rfl) ⟨139922, by rfl⟩) R279845
theorem R186835 : Reach 186835 := rs (se 1 (by rfl) ⟨140126, by rfl⟩) R280253
theorem R55991 : Reach 55991 := rs (se 1 (by rfl) ⟨41993, by rfl⟩) R83987
theorem R56143 : Reach 56143 := rs (se 1 (by rfl) ⟨42107, by rfl⟩) R84215
theorem R154493 : Reach 154493 := rs (se 3 (by rfl) ⟨28967, by rfl⟩) R57935
theorem R252827 : Reach 252827 := rs (se 1 (by rfl) ⟨189620, by rfl⟩) R379241
theorem R154763 : Reach 154763 := rs (se 1 (by rfl) ⟨116072, by rfl⟩) R232145
theorem R220553 : Reach 220553 := rs (se 2 (by rfl) ⟨82707, by rfl⟩) R165415
theorem R253601 : Reach 253601 := rs (se 2 (by rfl) ⟨95100, by rfl⟩) R190201
theorem R188335 : Reach 188335 := rs (se 1 (by rfl) ⟨141251, by rfl⟩) R282503
theorem R286739 : Reach 286739 := rs (se 1 (by rfl) ⟨215054, by rfl⟩) R430109
theorem R319697 : Reach 319697 := rs (se 2 (by rfl) ⟨119886, by rfl⟩) R239773
theorem R221615 : Reach 221615 := rs (se 1 (by rfl) ⟨166211, by rfl⟩) R332423
theorem R221879 : Reach 221879 := rs (se 1 (by rfl) ⟨166409, by rfl⟩) R332819
theorem R156383 : Reach 156383 := rs (se 1 (by rfl) ⟨117287, by rfl⟩) R234575
theorem R58153 : Reach 58153 := rs (se 2 (by rfl) ⟨21807, by rfl⟩) R43615
theorem R189431 : Reach 189431 := rs (se 1 (by rfl) ⟨142073, by rfl⟩) R284147
theorem R156815 : Reach 156815 := rs (se 1 (by rfl) ⟨117611, by rfl⟩) R235223
theorem R222551 : Reach 222551 := rs (se 1 (by rfl) ⟨166913, by rfl⟩) R333827
theorem R58735 : Reach 58735 := rs (se 1 (by rfl) ⟨44051, by rfl⟩) R88103
theorem R222587 : Reach 222587 := rs (se 1 (by rfl) ⟨166940, by rfl⟩) R333881
theorem R976373 : Reach 976373 := rs (se 5 (by rfl) ⟨45767, by rfl⟩) R91535
theorem R452429 : Reach 452429 := rs (se 3 (by rfl) ⟨84830, by rfl⟩) R169661
theorem R92009 : Reach 92009 := rs (se 2 (by rfl) ⟨34503, by rfl⟩) R69007
theorem R386963 : Reach 386963 := rs (se 1 (by rfl) ⟨290222, by rfl⟩) R580445
theorem R59611 : Reach 59611 := rs (se 1 (by rfl) ⟨44708, by rfl⟩) R89417
theorem R157949 : Reach 157949 := rs (se 3 (by rfl) ⟨29615, by rfl⟩) R59231
theorem R92735 : Reach 92735 := rs (se 1 (by rfl) ⟨69551, by rfl⟩) R139103
theorem R289403 : Reach 289403 := rs (se 1 (by rfl) ⟨217052, by rfl⟩) R434105
theorem R223883 : Reach 223883 := rs (se 1 (by rfl) ⟨167912, by rfl⟩) R335825
theorem R60139 : Reach 60139 := rs (se 1 (by rfl) ⟨45104, by rfl⟩) R90209
theorem R519047 : Reach 519047 := rs (se 1 (by rfl) ⟨389285, by rfl⟩) R778571
theorem R125867 : Reach 125867 := rs (se 1 (by rfl) ⟨94400, by rfl⟩) R188801
theorem R158759 : Reach 158759 := rs (se 1 (by rfl) ⟨119069, by rfl⟩) R238139
theorem R93307 : Reach 93307 := rs (se 1 (by rfl) ⟨69980, by rfl⟩) R139961
theorem R93563 : Reach 93563 := rs (se 1 (by rfl) ⟨70172, by rfl⟩) R140345
theorem R159175 : Reach 159175 := rs (se 1 (by rfl) ⟨119381, by rfl⟩) R238763
theorem R1175233 : Reach 1175233 := rs (se 2 (by rfl) ⟨440712, by rfl⟩) R881425
theorem R94007 : Reach 94007 := rs (se 1 (by rfl) ⟨70505, by rfl⟩) R141011
theorem R159617 : Reach 159617 := rs (se 2 (by rfl) ⟨59856, by rfl⟩) R119713
theorem R421841 : Reach 421841 := rs (se 2 (by rfl) ⟨158190, by rfl⟩) R316381
theorem R421955 : Reach 421955 := rs (se 1 (by rfl) ⟨316466, by rfl⟩) R632933
theorem R1208591 : Reach 1208591 := rs (se 1 (by rfl) ⟨906443, by rfl⟩) R1812887
theorem R94537 : Reach 94537 := rs (se 2 (by rfl) ⟨35451, by rfl⟩) R70903
theorem R356723 : Reach 356723 := rs (se 1 (by rfl) ⟨267542, by rfl⟩) R535085
theorem R127507 : Reach 127507 := rs (se 1 (by rfl) ⟨95630, by rfl⟩) R191261
theorem R782945 : Reach 782945 := rs (se 2 (by rfl) ⟨293604, by rfl⟩) R587209
theorem R95195 : Reach 95195 := rs (se 1 (by rfl) ⟨71396, by rfl⟩) R142793
theorem R95431 : Reach 95431 := rs (se 1 (by rfl) ⟨71573, by rfl⟩) R143147
theorem R259433 : Reach 259433 := rs (se 2 (by rfl) ⟨97287, by rfl⟩) R194575
theorem R128395 : Reach 128395 := rs (se 1 (by rfl) ⟨96296, by rfl⟩) R192593
theorem R194233 : Reach 194233 := rs (se 2 (by rfl) ⟨72837, by rfl⟩) R145675
theorem R96041 : Reach 96041 := rs (se 2 (by rfl) ⟨36015, by rfl⟩) R72031
theorem R227609 : Reach 227609 := rs (se 2 (by rfl) ⟨85353, by rfl⟩) R170707
theorem R424723 : Reach 424723 := rs (se 1 (by rfl) ⟨318542, by rfl⟩) R637085
theorem R392123 : Reach 392123 := rs (se 1 (by rfl) ⟨294092, by rfl⟩) R588185
theorem R97271 : Reach 97271 := rs (se 1 (by rfl) ⟨72953, by rfl⟩) R145907
theorem R64745 : Reach 64745 := rs (se 2 (by rfl) ⟨24279, by rfl⟩) R48559
theorem R64799 : Reach 64799 := rs (se 1 (by rfl) ⟨48599, by rfl⟩) R97199
theorem R97631 : Reach 97631 := rs (se 1 (by rfl) ⟨73223, by rfl⟩) R146447
theorem R64967 : Reach 64967 := rs (se 1 (by rfl) ⟨48725, by rfl⟩) R97451
theorem R294425 : Reach 294425 := rs (se 2 (by rfl) ⟨110409, by rfl⟩) R220819
theorem R98027 : Reach 98027 := rs (se 1 (by rfl) ⟨73520, by rfl⟩) R147041
theorem R65321 : Reach 65321 := rs (se 2 (by rfl) ⟨24495, by rfl⟩) R48991
theorem R65327 : Reach 65327 := rs (se 1 (by rfl) ⟨48995, by rfl⟩) R97991
theorem R98153 : Reach 98153 := rs (se 2 (by rfl) ⟨36807, by rfl⟩) R73615
theorem R98657 : Reach 98657 := rs (se 2 (by rfl) ⟨36996, by rfl⟩) R73993
theorem R65929 : Reach 65929 := rs (se 2 (by rfl) ⟨24723, by rfl⟩) R49447
theorem R98747 : Reach 98747 := rs (se 1 (by rfl) ⟨74060, by rfl⟩) R148121
theorem R65999 : Reach 65999 := rs (se 1 (by rfl) ⟨49499, by rfl⟩) R98999
theorem R66041 : Reach 66041 := rs (se 2 (by rfl) ⟨24765, by rfl⟩) R49531
theorem R2228795 : Reach 2228795 := rs (se 1 (by rfl) ⟨1671596, by rfl⟩) R3343193
theorem R66143 : Reach 66143 := rs (se 1 (by rfl) ⟨49607, by rfl⟩) R99215
theorem R66415 : Reach 66415 := rs (se 1 (by rfl) ⟨49811, by rfl⟩) R99623
theorem R66623 : Reach 66623 := rs (se 1 (by rfl) ⟨49967, by rfl⟩) R99935
theorem R66665 : Reach 66665 := rs (se 2 (by rfl) ⟨24999, by rfl⟩) R49999
theorem R66767 : Reach 66767 := rs (se 1 (by rfl) ⟨50075, by rfl⟩) R100151
theorem R492803 : Reach 492803 := rs (se 1 (by rfl) ⟨369602, by rfl⟩) R739205
theorem R886085 : Reach 886085 := rs (se 4 (by rfl) ⟨83070, by rfl⟩) R166141
theorem R263519 : Reach 263519 := rs (se 1 (by rfl) ⟨197639, by rfl⟩) R395279
theorem R66971 : Reach 66971 := rs (se 1 (by rfl) ⟨50228, by rfl⟩) R100457
theorem R99755 : Reach 99755 := rs (se 1 (by rfl) ⟨74816, by rfl⟩) R149633
theorem R67193 : Reach 67193 := rs (se 2 (by rfl) ⟨25197, by rfl⟩) R50395
theorem R132769 : Reach 132769 := rs (se 2 (by rfl) ⟨49788, by rfl⟩) R99577
theorem R100007 : Reach 100007 := rs (se 1 (by rfl) ⟨75005, by rfl⟩) R150011
theorem R67295 : Reach 67295 := rs (se 1 (by rfl) ⟨50471, by rfl⟩) R100943
theorem R67391 : Reach 67391 := rs (se 1 (by rfl) ⟨50543, by rfl⟩) R101087
theorem R296783 : Reach 296783 := rs (se 1 (by rfl) ⟨222587, by rfl⟩) R445175
theorem R100295 : Reach 100295 := rs (se 1 (by rfl) ⟨75221, by rfl⟩) R150443
theorem R67559 : Reach 67559 := rs (se 1 (by rfl) ⟨50669, by rfl⟩) R101339
theorem R67567 : Reach 67567 := rs (se 1 (by rfl) ⟨50675, by rfl⟩) R101351
theorem R133111 : Reach 133111 := rs (se 1 (by rfl) ⟨99833, by rfl⟩) R199667
theorem R67577 : Reach 67577 := rs (se 2 (by rfl) ⟨25341, by rfl⟩) R50683
theorem R67679 : Reach 67679 := rs (se 1 (by rfl) ⟨50759, by rfl⟩) R101519
theorem R67739 : Reach 67739 := rs (se 1 (by rfl) ⟨50804, by rfl⟩) R101609
theorem R67775 : Reach 67775 := rs (se 1 (by rfl) ⟨50831, by rfl⟩) R101663
theorem R67817 : Reach 67817 := rs (se 2 (by rfl) ⟨25431, by rfl⟩) R50863
theorem R231659 : Reach 231659 := rs (se 1 (by rfl) ⟨173744, by rfl⟩) R347489
theorem R100601 : Reach 100601 := rs (se 2 (by rfl) ⟨37725, by rfl⟩) R75451
theorem R100655 : Reach 100655 := rs (se 1 (by rfl) ⟨75491, by rfl⟩) R150983
theorem R100871 : Reach 100871 := rs (se 1 (by rfl) ⟨75653, by rfl⟩) R151307
theorem R68123 : Reach 68123 := rs (se 1 (by rfl) ⟨51092, by rfl⟩) R102185
theorem R68201 : Reach 68201 := rs (se 2 (by rfl) ⟨25575, by rfl⟩) R51151
theorem R264809 : Reach 264809 := rs (se 2 (by rfl) ⟨99303, by rfl⟩) R198607
theorem R101051 : Reach 101051 := rs (se 1 (by rfl) ⟨75788, by rfl⟩) R151577
theorem R494423 : Reach 494423 := rs (se 1 (by rfl) ⟨370817, by rfl⟩) R741635
theorem R68729 : Reach 68729 := rs (se 2 (by rfl) ⟨25773, by rfl⟩) R51547
theorem R68831 : Reach 68831 := rs (se 1 (by rfl) ⟨51623, by rfl⟩) R103247
theorem R68873 : Reach 68873 := rs (se 2 (by rfl) ⟨25827, by rfl⟩) R51655
theorem R331057 : Reach 331057 := rs (se 2 (by rfl) ⟨124146, by rfl⟩) R248293
theorem R68975 : Reach 68975 := rs (se 1 (by rfl) ⟨51731, by rfl⟩) R103463
theorem R167291 : Reach 167291 := rs (se 1 (by rfl) ⟨125468, by rfl⟩) R250937
theorem R69095 : Reach 69095 := rs (se 1 (by rfl) ⟨51821, by rfl⟩) R103643
theorem R101879 : Reach 101879 := rs (se 1 (by rfl) ⟨76409, by rfl⟩) R152819
theorem R232955 : Reach 232955 := rs (se 1 (by rfl) ⟨174716, by rfl⟩) R349433
theorem R101951 : Reach 101951 := rs (se 1 (by rfl) ⟨76463, by rfl⟩) R152927
theorem R69227 : Reach 69227 := rs (se 1 (by rfl) ⟨51920, by rfl⟩) R103841
theorem R69263 : Reach 69263 := rs (se 1 (by rfl) ⟨51947, by rfl⟩) R103895
theorem R233117 : Reach 233117 := rs (se 3 (by rfl) ⟨43709, by rfl⟩) R87419
theorem R69353 : Reach 69353 := rs (se 2 (by rfl) ⟨26007, by rfl⟩) R52015
theorem R134951 : Reach 134951 := rs (se 1 (by rfl) ⟨101213, by rfl⟩) R202427
theorem R69497 : Reach 69497 := rs (se 2 (by rfl) ⟨26061, by rfl⟩) R52123
theorem R69599 : Reach 69599 := rs (se 1 (by rfl) ⟨52199, by rfl⟩) R104399
theorem R69851 : Reach 69851 := rs (se 1 (by rfl) ⟨52388, by rfl⟩) R104777
theorem R69863 : Reach 69863 := rs (se 1 (by rfl) ⟨52397, by rfl⟩) R104795
theorem R70025 : Reach 70025 := rs (se 2 (by rfl) ⟨26259, by rfl⟩) R52519
theorem R70121 : Reach 70121 := rs (se 2 (by rfl) ⟨26295, by rfl⟩) R52591
theorem R102905 : Reach 102905 := rs (se 2 (by rfl) ⟨38589, by rfl⟩) R77179
theorem R102995 : Reach 102995 := rs (se 1 (by rfl) ⟨77246, by rfl⟩) R154493
theorem R332383 : Reach 332383 := rs (se 1 (by rfl) ⟨249287, by rfl⟩) R498575
theorem R168551 : Reach 168551 := rs (se 1 (by rfl) ⟨126413, by rfl⟩) R252827
theorem R70247 : Reach 70247 := rs (se 1 (by rfl) ⟨52685, by rfl⟩) R105371
theorem R70379 : Reach 70379 := rs (se 1 (by rfl) ⟨52784, by rfl⟩) R105569
theorem R103175 : Reach 103175 := rs (se 1 (by rfl) ⟨77381, by rfl⟩) R154763
theorem R70409 : Reach 70409 := rs (se 2 (by rfl) ⟨26403, by rfl⟩) R52807
theorem R103193 : Reach 103193 := rs (se 2 (by rfl) ⟨38697, by rfl⟩) R77395
theorem R70457 : Reach 70457 := rs (se 2 (by rfl) ⟨26421, by rfl⟩) R52843
theorem R70511 : Reach 70511 := rs (se 1 (by rfl) ⟨52883, by rfl⟩) R105767
theorem R169067 : Reach 169067 := rs (se 1 (by rfl) ⟨126800, by rfl⟩) R253601
theorem R267407 : Reach 267407 := rs (se 1 (by rfl) ⟨200555, by rfl⟩) R401111
theorem R104255 : Reach 104255 := rs (se 1 (by rfl) ⟨78191, by rfl⟩) R156383
theorem R170009 : Reach 170009 := rs (se 2 (by rfl) ⟨63753, by rfl⟩) R127507
theorem R1251409 : Reach 1251409 := rs (se 2 (by rfl) ⟨469278, by rfl⟩) R938557
theorem R104543 : Reach 104543 := rs (se 1 (by rfl) ⟨78407, by rfl⟩) R156815
theorem R104609 : Reach 104609 := rs (se 2 (by rfl) ⟨39228, by rfl⟩) R78457
theorem R301619 : Reach 301619 := rs (se 1 (by rfl) ⟨226214, by rfl⟩) R452429
theorem R2038405 : Reach 2038405 := rs (se 4 (by rfl) ⟨191100, by rfl⟩) R382201
theorem R105299 : Reach 105299 := rs (se 1 (by rfl) ⟨78974, by rfl⟩) R157949
theorem R138191 : Reach 138191 := rs (se 1 (by rfl) ⟨103643, by rfl⟩) R207287
theorem R171193 : Reach 171193 := rs (se 2 (by rfl) ⟨64197, by rfl⟩) R128395
theorem R4300121 : Reach 4300121 := rs (se 2 (by rfl) ⟨1612545, by rfl⟩) R3225091
theorem R105839 : Reach 105839 := rs (se 1 (by rfl) ⟨79379, by rfl⟩) R158759
theorem R73129 : Reach 73129 := rs (se 2 (by rfl) ⟨27423, by rfl⟩) R54847
theorem R73595 : Reach 73595 := rs (se 1 (by rfl) ⟨55196, by rfl⟩) R110393
theorem R237815 : Reach 237815 := rs (se 1 (by rfl) ⟨178361, by rfl⟩) R356723
theorem R140089 : Reach 140089 := rs (se 2 (by rfl) ⟨52533, by rfl⟩) R105067
theorem R172955 : Reach 172955 := rs (se 1 (by rfl) ⟨129716, by rfl⟩) R259433
theorem R566297 : Reach 566297 := rs (se 2 (by rfl) ⟨212361, by rfl⟩) R424723
theorem R74857 : Reach 74857 := rs (se 2 (by rfl) ⟨28071, by rfl⟩) R56143
theorem R75431 : Reach 75431 := rs (se 1 (by rfl) ⟨56573, by rfl⟩) R113147
theorem R43163 : Reach 43163 := rs (se 1 (by rfl) ⟨32372, by rfl⟩) R64745
theorem R43199 : Reach 43199 := rs (se 1 (by rfl) ⟨32399, by rfl⟩) R64799
theorem R43311 : Reach 43311 := rs (se 1 (by rfl) ⟨32483, by rfl⟩) R64967
theorem R76079 : Reach 76079 := rs (se 1 (by rfl) ⟨57059, by rfl⟩) R114119
theorem R43547 : Reach 43547 := rs (se 1 (by rfl) ⟨32660, by rfl⟩) R65321
theorem R76315 : Reach 76315 := rs (se 1 (by rfl) ⟨57236, by rfl⟩) R114473
theorem R43551 : Reach 43551 := rs (se 1 (by rfl) ⟨32663, by rfl⟩) R65327
theorem R43867 : Reach 43867 := rs (se 1 (by rfl) ⟨32900, by rfl⟩) R65801
theorem R43935 : Reach 43935 := rs (se 1 (by rfl) ⟨32951, by rfl⟩) R65903
theorem R175067 : Reach 175067 := rs (se 1 (by rfl) ⟨131300, by rfl⟩) R262601
theorem R44079 : Reach 44079 := rs (se 1 (by rfl) ⟨33059, by rfl⟩) R66119
theorem R44103 : Reach 44103 := rs (se 1 (by rfl) ⟨33077, by rfl⟩) R66155
theorem R44255 : Reach 44255 := rs (se 1 (by rfl) ⟨33191, by rfl⟩) R66383
theorem R77267 : Reach 77267 := rs (se 1 (by rfl) ⟨57950, by rfl⟩) R115901
theorem R44519 : Reach 44519 := rs (se 1 (by rfl) ⟨33389, by rfl⟩) R66779
theorem R77287 : Reach 77287 := rs (se 1 (by rfl) ⟨57965, by rfl⟩) R115931
theorem R765449 : Reach 765449 := rs (se 2 (by rfl) ⟨287043, by rfl⟩) R574087
theorem R110143 : Reach 110143 := rs (se 1 (by rfl) ⟨82607, by rfl⟩) R165215
theorem R77375 : Reach 77375 := rs (se 1 (by rfl) ⟨58031, by rfl⟩) R116063
theorem R44635 : Reach 44635 := rs (se 1 (by rfl) ⟨33476, by rfl⟩) R66953
theorem R77537 : Reach 77537 := rs (se 2 (by rfl) ⟨29076, by rfl⟩) R58153
theorem R44871 : Reach 44871 := rs (se 1 (by rfl) ⟨33653, by rfl⟩) R67307
theorem R45023 : Reach 45023 := rs (se 1 (by rfl) ⟨33767, by rfl⟩) R67535
theorem R536543 : Reach 536543 := rs (se 1 (by rfl) ⟨402407, by rfl⟩) R804815
theorem R602245 : Reach 602245 := rs (se 4 (by rfl) ⟨56460, by rfl⟩) R112921
theorem R78043 : Reach 78043 := rs (se 1 (by rfl) ⟨58532, by rfl⟩) R117065
theorem R45287 : Reach 45287 := rs (se 1 (by rfl) ⟨33965, by rfl⟩) R67931
theorem R45439 : Reach 45439 := rs (se 1 (by rfl) ⟨34079, by rfl⟩) R68159
theorem R45519 : Reach 45519 := rs (se 1 (by rfl) ⟨34139, by rfl⟩) R68279
theorem R78313 : Reach 78313 := rs (se 2 (by rfl) ⟨29367, by rfl⟩) R58735
theorem R45671 : Reach 45671 := rs (se 1 (by rfl) ⟨34253, by rfl⟩) R68507
theorem R242347 : Reach 242347 := rs (se 1 (by rfl) ⟨181760, by rfl⟩) R363521
theorem R406367 : Reach 406367 := rs (se 1 (by rfl) ⟨304775, by rfl⟩) R609551
theorem R45935 : Reach 45935 := rs (se 1 (by rfl) ⟨34451, by rfl⟩) R68903
theorem R45991 : Reach 45991 := rs (se 1 (by rfl) ⟨34493, by rfl⟩) R68987
theorem R46075 : Reach 46075 := rs (se 1 (by rfl) ⟨34556, by rfl⟩) R69113
theorem R46143 : Reach 46143 := rs (se 1 (by rfl) ⟨34607, by rfl⟩) R69215
theorem R111689 : Reach 111689 := rs (se 2 (by rfl) ⟨41883, by rfl⟩) R83767
theorem R46255 : Reach 46255 := rs (se 1 (by rfl) ⟨34691, by rfl⟩) R69383
theorem R46287 : Reach 46287 := rs (se 1 (by rfl) ⟨34715, by rfl⟩) R69431
theorem R79123 : Reach 79123 := rs (se 1 (by rfl) ⟨59342, by rfl⟩) R118685
theorem R46491 : Reach 46491 := rs (se 1 (by rfl) ⟨34868, by rfl⟩) R69737
theorem R833111 : Reach 833111 := rs (se 1 (by rfl) ⟨624833, by rfl⟩) R1249667
theorem R46703 : Reach 46703 := rs (se 1 (by rfl) ⟨35027, by rfl⟩) R70055
theorem R79481 : Reach 79481 := rs (se 2 (by rfl) ⟨29805, by rfl⟩) R59611
theorem R46759 : Reach 46759 := rs (se 1 (by rfl) ⟨35069, by rfl⟩) R70139
theorem R46811 : Reach 46811 := rs (se 1 (by rfl) ⟨35108, by rfl⟩) R70217
theorem R46843 : Reach 46843 := rs (se 1 (by rfl) ⟨35132, by rfl⟩) R70265
theorem R46879 : Reach 46879 := rs (se 1 (by rfl) ⟨35159, by rfl⟩) R70319
theorem R177983 : Reach 177983 := rs (se 1 (by rfl) ⟨133487, by rfl⟩) R266975
theorem R46911 : Reach 46911 := rs (se 1 (by rfl) ⟨35183, by rfl⟩) R70367
theorem R47047 : Reach 47047 := rs (se 1 (by rfl) ⟨35285, by rfl⟩) R70571
theorem R47087 : Reach 47087 := rs (se 1 (by rfl) ⟨35315, by rfl⟩) R70631
theorem R112873 : Reach 112873 := rs (se 2 (by rfl) ⟨42327, by rfl⟩) R84655
theorem R80185 : Reach 80185 := rs (se 2 (by rfl) ⟨30069, by rfl⟩) R60139
theorem R244079 : Reach 244079 := rs (se 1 (by rfl) ⟨183059, by rfl⟩) R366119
theorem R145853 : Reach 145853 := rs (se 3 (by rfl) ⟨27347, by rfl⟩) R54695
theorem R277181 : Reach 277181 := rs (se 3 (by rfl) ⟨51971, by rfl⟩) R103943
theorem R113633 : Reach 113633 := rs (se 2 (by rfl) ⟨42612, by rfl⟩) R85225
theorem R146717 : Reach 146717 := rs (se 3 (by rfl) ⟨27509, by rfl⟩) R55019
theorem R147035 : Reach 147035 := rs (se 1 (by rfl) ⟨110276, by rfl⟩) R220553
theorem R213131 : Reach 213131 := rs (se 1 (by rfl) ⟨159848, by rfl⟩) R319697
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R147743 : Reach 147743 := rs (se 1 (by rfl) ⟨110807, by rfl⟩) R221615
theorem R147919 : Reach 147919 := rs (se 1 (by rfl) ⟨110939, by rfl⟩) R221879
theorem R246311 : Reach 246311 := rs (se 1 (by rfl) ⟨184733, by rfl⟩) R369467
theorem R115465 : Reach 115465 := rs (se 2 (by rfl) ⟨43299, by rfl⟩) R86599
theorem R148367 : Reach 148367 := rs (se 1 (by rfl) ⟨111275, by rfl⟩) R222551
theorem R148391 : Reach 148391 := rs (se 1 (by rfl) ⟨111293, by rfl⟩) R222587
theorem R148985 : Reach 148985 := rs (se 2 (by rfl) ⟨55869, by rfl⟩) R111739
theorem R149255 : Reach 149255 := rs (se 1 (by rfl) ⟨111941, by rfl⟩) R223883
theorem R280381 : Reach 280381 := rs (se 3 (by rfl) ⟨52571, by rfl⟩) R105143
theorem R149309 : Reach 149309 := rs (se 3 (by rfl) ⟨27995, by rfl⟩) R55991
theorem R51007 : Reach 51007 := rs (se 1 (by rfl) ⟨38255, by rfl⟩) R76511
theorem R346031 : Reach 346031 := rs (se 1 (by rfl) ⟨259523, by rfl⟩) R519047
theorem R83911 : Reach 83911 := rs (se 1 (by rfl) ⟨62933, by rfl⟩) R125867
theorem R247781 : Reach 247781 := rs (se 4 (by rfl) ⟨23229, by rfl⟩) R46459
theorem R51295 : Reach 51295 := rs (se 1 (by rfl) ⟨38471, by rfl⟩) R76943
theorem R281033 : Reach 281033 := rs (se 2 (by rfl) ⟨105387, by rfl⟩) R210775
theorem R281227 : Reach 281227 := rs (se 1 (by rfl) ⟨210920, by rfl⟩) R421841
theorem R281303 : Reach 281303 := rs (se 1 (by rfl) ⟨210977, by rfl⟩) R421955
theorem R805727 : Reach 805727 := rs (se 1 (by rfl) ⟨604295, by rfl⟩) R1208591
theorem R117983 : Reach 117983 := rs (se 1 (by rfl) ⟨88487, by rfl⟩) R176975
theorem R52447 : Reach 52447 := rs (se 1 (by rfl) ⟨39335, by rfl⟩) R78671
theorem R249113 : Reach 249113 := rs (se 2 (by rfl) ⟨93417, by rfl⟩) R186835
theorem R118199 : Reach 118199 := rs (se 1 (by rfl) ⟨88649, by rfl⟩) R177299
theorem R249479 : Reach 249479 := rs (se 1 (by rfl) ⟨187109, by rfl⟩) R374219
theorem R315373 : Reach 315373 := rs (se 3 (by rfl) ⟨59132, by rfl⟩) R118265
theorem R151739 : Reach 151739 := rs (se 1 (by rfl) ⟨113804, by rfl⟩) R227609
theorem R152057 : Reach 152057 := rs (se 2 (by rfl) ⟨57021, by rfl⟩) R114043
theorem R316007 : Reach 316007 := rs (se 1 (by rfl) ⟨237005, by rfl⟩) R474011
theorem R152225 : Reach 152225 := rs (se 2 (by rfl) ⟨57084, by rfl⟩) R114169
theorem R250685 : Reach 250685 := rs (se 3 (by rfl) ⟨47003, by rfl⟩) R94007
theorem R316295 : Reach 316295 := rs (se 1 (by rfl) ⟨237221, by rfl⟩) R474443
theorem R54379 : Reach 54379 := rs (se 1 (by rfl) ⟨40784, by rfl⟩) R81569
theorem R251113 : Reach 251113 := rs (se 2 (by rfl) ⟨94167, by rfl⟩) R188335
theorem R153089 : Reach 153089 := rs (se 2 (by rfl) ⟨57408, by rfl⟩) R114817
theorem R907037 : Reach 907037 := rs (se 3 (by rfl) ⟨170069, by rfl⟩) R340139
theorem R153575 : Reach 153575 := rs (se 1 (by rfl) ⟨115181, by rfl⟩) R230363
theorem R88057 : Reach 88057 := rs (se 2 (by rfl) ⟨33021, by rfl⟩) R66043
theorem R153683 : Reach 153683 := rs (se 1 (by rfl) ⟨115262, by rfl⟩) R230525
theorem R743579 : Reach 743579 := rs (se 1 (by rfl) ⟨557684, by rfl⟩) R1115369
theorem R88361 : Reach 88361 := rs (se 2 (by rfl) ⟨33135, by rfl⟩) R66271
theorem R153899 : Reach 153899 := rs (se 1 (by rfl) ⟨115424, by rfl⟩) R230849
theorem R154169 : Reach 154169 := rs (se 2 (by rfl) ⟨57813, by rfl⟩) R115627
theorem R481879 : Reach 481879 := rs (se 1 (by rfl) ⟨361409, by rfl⟩) R722819
theorem R219995 : Reach 219995 := rs (se 1 (by rfl) ⟨164996, by rfl⟩) R329993
theorem R351377 : Reach 351377 := rs (se 2 (by rfl) ⟨131766, by rfl⟩) R263533
theorem R7625933 : Reach 7625933 := rs (se 3 (by rfl) ⟨1429862, by rfl⟩) R2859725
theorem R2154059 : Reach 2154059 := rs (se 1 (by rfl) ⟨1615544, by rfl⟩) R3231089
theorem R319211 : Reach 319211 := rs (se 1 (by rfl) ⟨239408, by rfl⟩) R478817
theorem R253853 : Reach 253853 := rs (se 3 (by rfl) ⟨47597, by rfl⟩) R95195
theorem R155681 : Reach 155681 := rs (se 2 (by rfl) ⟨58380, by rfl⟩) R116761
theorem R254603 : Reach 254603 := rs (se 1 (by rfl) ⟨190952, by rfl⟩) R381905
theorem R124375 : Reach 124375 := rs (se 1 (by rfl) ⟨93281, by rfl⟩) R186563
theorem R124409 : Reach 124409 := rs (se 2 (by rfl) ⟨46653, by rfl⟩) R93307
theorem R353807 : Reach 353807 := rs (se 1 (by rfl) ⟨265355, by rfl⟩) R530711
theorem R223073 : Reach 223073 := rs (se 2 (by rfl) ⟨83652, by rfl⟩) R167305
theorem R354449 : Reach 354449 := rs (se 2 (by rfl) ⟨132918, by rfl⟩) R265837
theorem R1566977 : Reach 1566977 := rs (se 2 (by rfl) ⟨587616, by rfl⟩) R1175233
theorem R191159 : Reach 191159 := rs (se 1 (by rfl) ⟨143369, by rfl⟩) R286739
theorem R126049 : Reach 126049 := rs (se 2 (by rfl) ⟨47268, by rfl⟩) R94537
theorem R126287 : Reach 126287 := rs (se 1 (by rfl) ⟨94715, by rfl⟩) R189431
theorem R650915 : Reach 650915 := rs (se 1 (by rfl) ⟨488186, by rfl⟩) R976373
theorem R225179 : Reach 225179 := rs (se 1 (by rfl) ⟨168884, by rfl⟩) R337769
theorem R61339 : Reach 61339 := rs (se 1 (by rfl) ⟨46004, by rfl⟩) R92009
theorem R290735 : Reach 290735 := rs (se 1 (by rfl) ⟨218051, by rfl⟩) R436103
theorem R257975 : Reach 257975 := rs (se 1 (by rfl) ⟨193481, by rfl⟩) R386963
theorem R159695 : Reach 159695 := rs (se 1 (by rfl) ⟨119771, by rfl⟩) R239543
theorem R127165 : Reach 127165 := rs (se 3 (by rfl) ⟨23843, by rfl⟩) R47687
theorem R127241 : Reach 127241 := rs (se 2 (by rfl) ⟨47715, by rfl⟩) R95431
theorem R160055 : Reach 160055 := rs (se 1 (by rfl) ⟨120041, by rfl⟩) R240083
theorem R61823 : Reach 61823 := rs (se 1 (by rfl) ⟨46367, by rfl⟩) R92735
theorem R192935 : Reach 192935 := rs (se 1 (by rfl) ⟨144701, by rfl⟩) R289403
theorem R160271 : Reach 160271 := rs (se 1 (by rfl) ⟨120203, by rfl⟩) R240407
theorem R1078109 : Reach 1078109 := rs (se 3 (by rfl) ⟨202145, by rfl⟩) R404291
theorem R258977 : Reach 258977 := rs (se 2 (by rfl) ⟨97116, by rfl⟩) R194233
theorem R62375 : Reach 62375 := rs (se 1 (by rfl) ⟨46781, by rfl⟩) R93563
theorem R848933 : Reach 848933 := rs (se 4 (by rfl) ⟨79587, by rfl⟩) R159175
theorem R62569 : Reach 62569 := rs (se 2 (by rfl) ⟨23463, by rfl⟩) R46927
theorem R521963 : Reach 521963 := rs (se 1 (by rfl) ⟨391472, by rfl⟩) R782945
theorem R64027 : Reach 64027 := rs (se 1 (by rfl) ⟨48020, by rfl⟩) R96041
theorem R719513 : Reach 719513 := rs (se 2 (by rfl) ⟨269817, by rfl⟩) R539635
theorem R752327 : Reach 752327 := rs (se 1 (by rfl) ⟨564245, by rfl⟩) R1128491
theorem R261415 : Reach 261415 := rs (se 1 (by rfl) ⟨196061, by rfl⟩) R392123
theorem R64847 : Reach 64847 := rs (se 1 (by rfl) ⟨48635, by rfl⟩) R97271
theorem R97703 : Reach 97703 := rs (se 1 (by rfl) ⟨73277, by rfl⟩) R146555
theorem R64937 : Reach 64937 := rs (se 2 (by rfl) ⟨24351, by rfl⟩) R48703
theorem R65087 : Reach 65087 := rs (se 1 (by rfl) ⟨48815, by rfl⟩) R97631
theorem R97883 : Reach 97883 := rs (se 1 (by rfl) ⟨73412, by rfl⟩) R146825
theorem R425645 : Reach 425645 := rs (se 3 (by rfl) ⟨79808, by rfl⟩) R159617
theorem R196283 : Reach 196283 := rs (se 1 (by rfl) ⟨147212, by rfl⟩) R294425
theorem R65351 : Reach 65351 := rs (se 1 (by rfl) ⟨49013, by rfl⟩) R98027
theorem R98171 : Reach 98171 := rs (se 1 (by rfl) ⟨73628, by rfl⟩) R147257
theorem R65435 : Reach 65435 := rs (se 1 (by rfl) ⟨49076, by rfl⟩) R98153
theorem R98495 : Reach 98495 := rs (se 1 (by rfl) ⟨73871, by rfl⟩) R147743
theorem R65771 : Reach 65771 := rs (se 1 (by rfl) ⟨49328, by rfl⟩) R98657
theorem R65831 : Reach 65831 := rs (se 1 (by rfl) ⟨49373, by rfl⟩) R98747
theorem R164207 : Reach 164207 := rs (se 1 (by rfl) ⟨123155, by rfl⟩) R246311
theorem R98911 : Reach 98911 := rs (se 1 (by rfl) ⟨74183, by rfl⟩) R148367
theorem R197225 : Reach 197225 := rs (se 2 (by rfl) ⟨73959, by rfl⟩) R147919
theorem R98927 : Reach 98927 := rs (se 1 (by rfl) ⟨74195, by rfl⟩) R148391
theorem R3211973 : Reach 3211973 := rs (se 4 (by rfl) ⟨301122, by rfl⟩) R602245
theorem R328535 : Reach 328535 := rs (se 1 (by rfl) ⟨246401, by rfl⟩) R492803
theorem R590723 : Reach 590723 := rs (se 1 (by rfl) ⟨443042, by rfl⟩) R886085
theorem R66503 : Reach 66503 := rs (se 1 (by rfl) ⟨49877, by rfl⟩) R99755
theorem R99323 : Reach 99323 := rs (se 1 (by rfl) ⟨74492, by rfl⟩) R148985
theorem R164861 : Reach 164861 := rs (se 3 (by rfl) ⟨30911, by rfl⟩) R61823
theorem R66671 : Reach 66671 := rs (se 1 (by rfl) ⟨50003, by rfl⟩) R100007
theorem R99503 : Reach 99503 := rs (se 1 (by rfl) ⟨74627, by rfl⟩) R149255
theorem R99539 : Reach 99539 := rs (se 1 (by rfl) ⟨74654, by rfl⟩) R149309
theorem R197855 : Reach 197855 := rs (se 1 (by rfl) ⟨148391, by rfl⟩) R296783
theorem R230687 : Reach 230687 := rs (se 1 (by rfl) ⟨173015, by rfl⟩) R346031
theorem R66863 : Reach 66863 := rs (se 1 (by rfl) ⟨50147, by rfl⟩) R100295
theorem R165187 : Reach 165187 := rs (se 1 (by rfl) ⟨123890, by rfl⟩) R247781
theorem R99809 : Reach 99809 := rs (se 2 (by rfl) ⟨37428, by rfl⟩) R74857
theorem R67067 : Reach 67067 := rs (se 1 (by rfl) ⟨50300, by rfl⟩) R100601
theorem R67103 : Reach 67103 := rs (se 1 (by rfl) ⟨50327, by rfl⟩) R100655
theorem R67247 : Reach 67247 := rs (se 1 (by rfl) ⟨50435, by rfl⟩) R100871
theorem R67367 : Reach 67367 := rs (se 1 (by rfl) ⟨50525, by rfl⟩) R101051
theorem R329615 : Reach 329615 := rs (se 1 (by rfl) ⟨247211, by rfl⟩) R494423
theorem R165833 : Reach 165833 := rs (se 2 (by rfl) ⟨62187, by rfl⟩) R124375
theorem R67919 : Reach 67919 := rs (se 1 (by rfl) ⟨50939, by rfl⟩) R101879
theorem R67967 : Reach 67967 := rs (se 1 (by rfl) ⟨50975, by rfl⟩) R101951
theorem R68009 : Reach 68009 := rs (se 2 (by rfl) ⟨25503, by rfl⟩) R51007
theorem R166319 : Reach 166319 := rs (se 1 (by rfl) ⟨124739, by rfl⟩) R249479
theorem R166333 : Reach 166333 := rs (se 3 (by rfl) ⟨31187, by rfl⟩) R62375
theorem R16714421 : Reach 16714421 := rs (se 5 (by rfl) ⟨783488, by rfl⟩) R1566977
theorem R101159 : Reach 101159 := rs (se 1 (by rfl) ⟨75869, by rfl⟩) R151739
theorem R68393 : Reach 68393 := rs (se 2 (by rfl) ⟨25647, by rfl⟩) R51295
theorem R68603 : Reach 68603 := rs (se 1 (by rfl) ⟨51452, by rfl⟩) R102905
theorem R68663 : Reach 68663 := rs (se 1 (by rfl) ⟨51497, by rfl⟩) R102995
theorem R101483 : Reach 101483 := rs (se 1 (by rfl) ⟨76112, by rfl⟩) R152225
theorem R68783 : Reach 68783 := rs (se 1 (by rfl) ⟨51587, by rfl⟩) R103175
theorem R68795 : Reach 68795 := rs (se 1 (by rfl) ⟨51596, by rfl⟩) R103193
theorem R167123 : Reach 167123 := rs (se 1 (by rfl) ⟨125342, by rfl⟩) R250685
theorem R101753 : Reach 101753 := rs (se 2 (by rfl) ⟨38157, by rfl⟩) R76315
theorem R102059 : Reach 102059 := rs (se 1 (by rfl) ⟨76544, by rfl⟩) R153089
theorem R69503 : Reach 69503 := rs (se 1 (by rfl) ⟨52127, by rfl⟩) R104255
theorem R102383 : Reach 102383 := rs (se 1 (by rfl) ⟨76787, by rfl⟩) R153575
theorem R102455 : Reach 102455 := rs (se 1 (by rfl) ⟨76841, by rfl⟩) R153683
theorem R69695 : Reach 69695 := rs (se 1 (by rfl) ⟨52271, by rfl⟩) R104543
theorem R495719 : Reach 495719 := rs (se 1 (by rfl) ⟨371789, by rfl⟩) R743579
theorem R168065 : Reach 168065 := rs (se 2 (by rfl) ⟨63024, by rfl⟩) R126049
theorem R102599 : Reach 102599 := rs (se 1 (by rfl) ⟨76949, by rfl⟩) R153899
theorem R69929 : Reach 69929 := rs (se 2 (by rfl) ⟨26223, by rfl⟩) R52447
theorem R201079 : Reach 201079 := rs (se 1 (by rfl) ⟨150809, by rfl⟩) R301619
theorem R102779 : Reach 102779 := rs (se 1 (by rfl) ⟨77084, by rfl⟩) R154169
theorem R70199 : Reach 70199 := rs (se 1 (by rfl) ⟨52649, by rfl⟩) R105299
theorem R103049 : Reach 103049 := rs (se 2 (by rfl) ⟨38643, by rfl⟩) R77287
theorem R234251 : Reach 234251 := rs (se 1 (by rfl) ⟨175688, by rfl⟩) R351377
theorem R5083955 : Reach 5083955 := rs (se 1 (by rfl) ⟨3812966, by rfl⟩) R7625933
theorem R70559 : Reach 70559 := rs (se 1 (by rfl) ⟨52919, by rfl⟩) R105839
theorem R169235 : Reach 169235 := rs (se 1 (by rfl) ⟨126926, by rfl⟩) R253853
theorem R103787 : Reach 103787 := rs (se 1 (by rfl) ⟨77840, by rfl⟩) R155681
theorem R169553 : Reach 169553 := rs (se 2 (by rfl) ⟨63582, by rfl⟩) R127165
theorem R104057 : Reach 104057 := rs (se 2 (by rfl) ⟨39021, by rfl⟩) R78043
theorem R169735 : Reach 169735 := rs (se 1 (by rfl) ⟨127301, by rfl⟩) R254603
theorem R104417 : Reach 104417 := rs (se 2 (by rfl) ⟨39156, by rfl⟩) R78313
theorem R235871 : Reach 235871 := rs (se 1 (by rfl) ⟨176903, by rfl⟩) R353807
theorem R236299 : Reach 236299 := rs (se 1 (by rfl) ⟨177224, by rfl⟩) R354449
theorem R72505 : Reach 72505 := rs (se 2 (by rfl) ⟨27189, by rfl⟩) R54379
theorem R334817 : Reach 334817 := rs (se 2 (by rfl) ⟨125556, by rfl⟩) R251113
theorem R105497 : Reach 105497 := rs (se 2 (by rfl) ⟨39561, by rfl⟩) R79123
theorem R433943 : Reach 433943 := rs (se 1 (by rfl) ⟨325457, by rfl⟩) R650915
theorem R368509 : Reach 368509 := rs (se 3 (by rfl) ⟨69095, by rfl⟩) R138191
theorem R171983 : Reach 171983 := rs (se 1 (by rfl) ⟨128987, by rfl⟩) R257975
theorem R106463 : Reach 106463 := rs (se 1 (by rfl) ⟨79847, by rfl⟩) R159695
theorem R106703 : Reach 106703 := rs (se 1 (by rfl) ⟨80027, by rfl⟩) R160055
theorem R106847 : Reach 106847 := rs (se 1 (by rfl) ⟨80135, by rfl⟩) R160271
theorem R106913 : Reach 106913 := rs (se 2 (by rfl) ⟨40092, by rfl⟩) R80185
theorem R270911 : Reach 270911 := rs (se 1 (by rfl) ⟨203183, by rfl⟩) R406367
theorem R172651 : Reach 172651 := rs (se 1 (by rfl) ⟨129488, by rfl⟩) R258977
theorem R565955 : Reach 565955 := rs (se 1 (by rfl) ⟨424466, by rfl⟩) R848933
theorem R74459 : Reach 74459 := rs (se 1 (by rfl) ⟨55844, by rfl⟩) R111689
theorem R664301 : Reach 664301 := rs (se 3 (by rfl) ⟨124556, by rfl⟩) R249113
theorem R172925 : Reach 172925 := rs (se 3 (by rfl) ⟨32423, by rfl⟩) R64847
theorem R501551 : Reach 501551 := rs (se 1 (by rfl) ⟨376163, by rfl⟩) R752327
theorem R75755 : Reach 75755 := rs (se 1 (by rfl) ⟨56816, by rfl⟩) R113633
theorem R43231 : Reach 43231 := rs (se 1 (by rfl) ⟨32423, by rfl⟩) R64847
theorem R43291 : Reach 43291 := rs (se 1 (by rfl) ⟨32468, by rfl⟩) R64937
theorem R43391 : Reach 43391 := rs (se 1 (by rfl) ⟨32543, by rfl⟩) R65087
theorem R43567 : Reach 43567 := rs (se 1 (by rfl) ⟨32675, by rfl⟩) R65351
theorem R43623 : Reach 43623 := rs (se 1 (by rfl) ⟨32717, by rfl⟩) R65435
theorem R142087 : Reach 142087 := rs (se 1 (by rfl) ⟨106565, by rfl⟩) R213131
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R43999 : Reach 43999 := rs (se 1 (by rfl) ⟨32999, by rfl⟩) R65999
theorem R44027 : Reach 44027 := rs (se 1 (by rfl) ⟨33020, by rfl⟩) R66041
theorem R1485863 : Reach 1485863 := rs (se 1 (by rfl) ⟨1114397, by rfl⟩) R2228795
theorem R44095 : Reach 44095 := rs (se 1 (by rfl) ⟨33071, by rfl⟩) R66143
theorem R44415 : Reach 44415 := rs (se 1 (by rfl) ⟨33311, by rfl⟩) R66623
theorem R44443 : Reach 44443 := rs (se 1 (by rfl) ⟨33332, by rfl⟩) R66665
theorem R44511 : Reach 44511 := rs (se 1 (by rfl) ⟨33383, by rfl⟩) R66767
theorem R175679 : Reach 175679 := rs (se 1 (by rfl) ⟨131759, by rfl⟩) R263519
theorem R44647 : Reach 44647 := rs (se 1 (by rfl) ⟨33485, by rfl⟩) R66971
theorem R44795 : Reach 44795 := rs (se 1 (by rfl) ⟨33596, by rfl⟩) R67193
theorem R44863 : Reach 44863 := rs (se 1 (by rfl) ⟨33647, by rfl⟩) R67295
theorem R44927 : Reach 44927 := rs (se 1 (by rfl) ⟨33695, by rfl⟩) R67391
theorem R405485 : Reach 405485 := rs (se 3 (by rfl) ⟨76028, by rfl⟩) R152057
theorem R45039 : Reach 45039 := rs (se 1 (by rfl) ⟨33779, by rfl⟩) R67559
theorem R45051 : Reach 45051 := rs (se 1 (by rfl) ⟨33788, by rfl⟩) R67577
theorem R45119 : Reach 45119 := rs (se 1 (by rfl) ⟨33839, by rfl⟩) R67679
theorem R45159 : Reach 45159 := rs (se 1 (by rfl) ⟨33869, by rfl⟩) R67739
theorem R45183 : Reach 45183 := rs (se 1 (by rfl) ⟨33887, by rfl⟩) R67775
theorem R45211 : Reach 45211 := rs (se 1 (by rfl) ⟨33908, by rfl⟩) R67817
theorem R45415 : Reach 45415 := rs (se 1 (by rfl) ⟨34061, by rfl⟩) R68123
theorem R45467 : Reach 45467 := rs (se 1 (by rfl) ⟨34100, by rfl⟩) R68201
theorem R176539 : Reach 176539 := rs (se 1 (by rfl) ⟨132404, by rfl⟩) R264809
theorem R45819 : Reach 45819 := rs (se 1 (by rfl) ⟨34364, by rfl⟩) R68729
theorem R45887 : Reach 45887 := rs (se 1 (by rfl) ⟨34415, by rfl⟩) R68831
theorem R45915 : Reach 45915 := rs (se 1 (by rfl) ⟨34436, by rfl⟩) R68873
theorem R177025 : Reach 177025 := rs (se 2 (by rfl) ⟨66384, by rfl⟩) R132769
theorem R45983 : Reach 45983 := rs (se 1 (by rfl) ⟨34487, by rfl⟩) R68975
theorem R111527 : Reach 111527 := rs (se 1 (by rfl) ⟨83645, by rfl⟩) R167291
theorem R78799 : Reach 78799 := rs (se 1 (by rfl) ⟨59099, by rfl⟩) R118199
theorem R46063 : Reach 46063 := rs (se 1 (by rfl) ⟨34547, by rfl⟩) R69095
theorem R46151 : Reach 46151 := rs (se 1 (by rfl) ⟨34613, by rfl⟩) R69227
theorem R373841 : Reach 373841 := rs (se 2 (by rfl) ⟨140190, by rfl⟩) R280381
theorem R46175 : Reach 46175 := rs (se 1 (by rfl) ⟨34631, by rfl⟩) R69263
theorem R46235 : Reach 46235 := rs (se 1 (by rfl) ⟨34676, by rfl⟩) R69353
theorem R46331 : Reach 46331 := rs (se 1 (by rfl) ⟨34748, by rfl⟩) R69497
theorem R111881 : Reach 111881 := rs (se 2 (by rfl) ⟨41955, by rfl⟩) R83911
theorem R46399 : Reach 46399 := rs (se 1 (by rfl) ⟨34799, by rfl⟩) R69599
theorem R177481 : Reach 177481 := rs (se 2 (by rfl) ⟨66555, by rfl⟩) R133111
theorem R46567 : Reach 46567 := rs (se 1 (by rfl) ⟨34925, by rfl⟩) R69851
theorem R46575 : Reach 46575 := rs (se 1 (by rfl) ⟨34931, by rfl⟩) R69863
theorem R46683 : Reach 46683 := rs (se 1 (by rfl) ⟨35012, by rfl⟩) R70025
theorem R46747 : Reach 46747 := rs (se 1 (by rfl) ⟨35060, by rfl⟩) R70121
theorem R210671 : Reach 210671 := rs (se 1 (by rfl) ⟨158003, by rfl⟩) R316007
theorem R112367 : Reach 112367 := rs (se 1 (by rfl) ⟨84275, by rfl⟩) R168551
theorem R46831 : Reach 46831 := rs (se 1 (by rfl) ⟨35123, by rfl⟩) R70247
theorem R46919 : Reach 46919 := rs (se 1 (by rfl) ⟨35189, by rfl⟩) R70379
theorem R46939 : Reach 46939 := rs (se 1 (by rfl) ⟨35204, by rfl⟩) R70409
theorem R46971 : Reach 46971 := rs (se 1 (by rfl) ⟨35228, by rfl⟩) R70457
theorem R47007 : Reach 47007 := rs (se 1 (by rfl) ⟨35255, by rfl⟩) R70511
theorem R210863 : Reach 210863 := rs (se 1 (by rfl) ⟨158147, by rfl⟩) R316295
theorem R112711 : Reach 112711 := rs (se 1 (by rfl) ⟨84533, by rfl⟩) R169067
theorem R178271 : Reach 178271 := rs (se 1 (by rfl) ⟨133703, by rfl⟩) R267407
theorem R374969 : Reach 374969 := rs (se 2 (by rfl) ⟨140613, by rfl⟩) R281227
theorem R604691 : Reach 604691 := rs (se 1 (by rfl) ⟨453518, by rfl⟩) R907037
theorem R113339 : Reach 113339 := rs (se 1 (by rfl) ⟨85004, by rfl⟩) R170009
theorem R441409 : Reach 441409 := rs (se 2 (by rfl) ⟨165528, by rfl⟩) R331057
theorem R146663 : Reach 146663 := rs (se 1 (by rfl) ⟨109997, by rfl⟩) R219995
theorem R146857 : Reach 146857 := rs (se 2 (by rfl) ⟨55071, by rfl⟩) R110143
theorem R2866747 : Reach 2866747 := rs (se 1 (by rfl) ⟨2150060, by rfl⟩) R4300121
theorem R212807 : Reach 212807 := rs (se 1 (by rfl) ⟨159605, by rfl⟩) R319211
theorem R81785 : Reach 81785 := rs (se 2 (by rfl) ⟨30669, by rfl⟩) R61339
theorem R49063 : Reach 49063 := rs (se 1 (by rfl) ⟨36797, by rfl⟩) R73595
theorem R278957 : Reach 278957 := rs (se 3 (by rfl) ⟨52304, by rfl⟩) R104609
theorem R115303 : Reach 115303 := rs (se 1 (by rfl) ⟨86477, by rfl⟩) R172955
theorem R377531 : Reach 377531 := rs (se 1 (by rfl) ⟨283148, by rfl⟩) R566297
theorem R443177 : Reach 443177 := rs (se 2 (by rfl) ⟨166191, by rfl⟩) R332383
theorem R82939 : Reach 82939 := rs (se 1 (by rfl) ⟨62204, by rfl⟩) R124409
theorem R50287 : Reach 50287 := rs (se 1 (by rfl) ⟨37715, by rfl⟩) R75431
theorem R148715 : Reach 148715 := rs (se 1 (by rfl) ⟨111536, by rfl⟩) R223073
theorem R83425 : Reach 83425 := rs (se 2 (by rfl) ⟨31284, by rfl⟩) R62569
theorem R50719 : Reach 50719 := rs (se 1 (by rfl) ⟨38039, by rfl⟩) R76079
theorem R116711 : Reach 116711 := rs (se 1 (by rfl) ⟨87533, by rfl⟩) R175067
theorem R84191 : Reach 84191 := rs (se 1 (by rfl) ⟨63143, by rfl⟩) R126287
theorem R2148605 : Reach 2148605 := rs (se 3 (by rfl) ⟨402863, by rfl⟩) R805727
theorem R51511 : Reach 51511 := rs (se 1 (by rfl) ⟨38633, by rfl⟩) R77267
theorem R510299 : Reach 510299 := rs (se 1 (by rfl) ⟨382724, by rfl⟩) R765449
theorem R51583 : Reach 51583 := rs (se 1 (by rfl) ⟨38687, by rfl⟩) R77375
theorem R51691 : Reach 51691 := rs (se 1 (by rfl) ⟨38768, by rfl⟩) R77537
theorem R150119 : Reach 150119 := rs (se 1 (by rfl) ⟨112589, by rfl⟩) R225179
theorem R117409 : Reach 117409 := rs (se 2 (by rfl) ⟨44028, by rfl⟩) R88057
theorem R84827 : Reach 84827 := rs (se 1 (by rfl) ⟨63620, by rfl⟩) R127241
theorem R150497 : Reach 150497 := rs (se 2 (by rfl) ⟨56436, by rfl⟩) R112873
theorem R314621 : Reach 314621 := rs (se 3 (by rfl) ⟨58991, by rfl⟩) R117983
theorem R85369 : Reach 85369 := rs (se 2 (by rfl) ⟨32013, by rfl⟩) R64027
theorem R642505 : Reach 642505 := rs (se 2 (by rfl) ⟨240939, by rfl⟩) R481879
theorem R52987 : Reach 52987 := rs (se 1 (by rfl) ⟨39740, by rfl⟩) R79481
theorem R347975 : Reach 347975 := rs (se 1 (by rfl) ⟨260981, by rfl⟩) R521963
theorem R118655 : Reach 118655 := rs (se 1 (by rfl) ⟨88991, by rfl⟩) R177983
theorem R348553 : Reach 348553 := rs (se 2 (by rfl) ⟨130707, by rfl⟩) R261415
theorem R479675 : Reach 479675 := rs (se 1 (by rfl) ⟨359756, by rfl⟩) R719513
theorem R184787 : Reach 184787 := rs (se 1 (by rfl) ⟨138590, by rfl⟩) R277181
theorem R283763 : Reach 283763 := rs (se 1 (by rfl) ⟨212822, by rfl⟩) R425645
theorem R87905 : Reach 87905 := rs (se 2 (by rfl) ⟨32964, by rfl⟩) R65929
theorem R153953 : Reach 153953 := rs (se 2 (by rfl) ⟨57732, by rfl⟩) R115465
theorem R186785 : Reach 186785 := rs (se 2 (by rfl) ⟨70044, by rfl⟩) R140089
theorem R88553 : Reach 88553 := rs (se 2 (by rfl) ⟨33207, by rfl⟩) R66415
theorem R154439 : Reach 154439 := rs (se 1 (by rfl) ⟨115829, by rfl⟩) R231659
theorem R187355 : Reach 187355 := rs (se 1 (by rfl) ⟨140516, by rfl⟩) R281033
theorem R187535 : Reach 187535 := rs (se 1 (by rfl) ⟨140651, by rfl⟩) R281303
theorem R155303 : Reach 155303 := rs (se 1 (by rfl) ⟨116477, by rfl⟩) R232955
theorem R155411 : Reach 155411 := rs (se 1 (by rfl) ⟨116558, by rfl⟩) R233117
theorem R90089 : Reach 90089 := rs (se 2 (by rfl) ⟨33783, by rfl⟩) R67567
theorem R58907 : Reach 58907 := rs (se 1 (by rfl) ⟨44180, by rfl⟩) R88361
theorem R1436039 : Reach 1436039 := rs (se 1 (by rfl) ⟨1077029, by rfl⟩) R2154059
theorem R420497 : Reach 420497 := rs (se 2 (by rfl) ⟨157686, by rfl⟩) R315373
theorem R158543 : Reach 158543 := rs (se 1 (by rfl) ⟨118907, by rfl⟩) R237815
theorem R323129 : Reach 323129 := rs (se 2 (by rfl) ⟨121173, by rfl⟩) R242347
theorem R127439 : Reach 127439 := rs (se 1 (by rfl) ⟨95579, by rfl⟩) R191159
theorem R193823 : Reach 193823 := rs (se 1 (by rfl) ⟨145367, by rfl⟩) R290735
theorem R357695 : Reach 357695 := rs (se 1 (by rfl) ⟨268271, by rfl⟩) R536543
theorem R1668545 : Reach 1668545 := rs (se 2 (by rfl) ⟨625704, by rfl⟩) R1251409
theorem R128623 : Reach 128623 := rs (se 1 (by rfl) ⟨96467, by rfl⟩) R192935
theorem R718739 : Reach 718739 := rs (se 1 (by rfl) ⟨539054, by rfl⟩) R1078109
theorem R2717873 : Reach 2717873 := rs (se 2 (by rfl) ⟨1019202, by rfl⟩) R2038405
theorem R555407 : Reach 555407 := rs (se 1 (by rfl) ⟨416555, by rfl⟩) R833111
theorem R162719 : Reach 162719 := rs (se 1 (by rfl) ⟨122039, by rfl⟩) R244079
theorem R228257 : Reach 228257 := rs (se 2 (by rfl) ⟨85596, by rfl⟩) R171193
theorem R97235 : Reach 97235 := rs (se 1 (by rfl) ⟨72926, by rfl⟩) R145853
theorem R523421 : Reach 523421 := rs (se 3 (by rfl) ⟨98141, by rfl⟩) R196283
theorem R97505 : Reach 97505 := rs (se 2 (by rfl) ⟨36564, by rfl⟩) R73129
theorem R359869 : Reach 359869 := rs (se 3 (by rfl) ⟨67475, by rfl⟩) R134951
theorem R97811 : Reach 97811 := rs (se 1 (by rfl) ⟨73358, by rfl⟩) R146717
theorem R65135 : Reach 65135 := rs (se 1 (by rfl) ⟨48851, by rfl⟩) R97703
theorem R65255 : Reach 65255 := rs (se 1 (by rfl) ⟨48941, by rfl⟩) R97883
theorem R98023 : Reach 98023 := rs (se 1 (by rfl) ⟨73517, by rfl⟩) R147035
theorem R65447 : Reach 65447 := rs (se 1 (by rfl) ⟨49085, by rfl⟩) R98171
theorem R65663 : Reach 65663 := rs (se 1 (by rfl) ⟨49247, by rfl⟩) R98495
theorem R131483 : Reach 131483 := rs (se 1 (by rfl) ⟨98612, by rfl⟩) R197225
theorem R65951 : Reach 65951 := rs (se 1 (by rfl) ⟨49463, by rfl⟩) R98927
theorem R295451 : Reach 295451 := rs (se 1 (by rfl) ⟨221588, by rfl⟩) R443177
theorem R393815 : Reach 393815 := rs (se 1 (by rfl) ⟨295361, by rfl⟩) R590723
theorem R66215 : Reach 66215 := rs (se 1 (by rfl) ⟨49661, by rfl⟩) R99323
theorem R66335 : Reach 66335 := rs (se 1 (by rfl) ⟨49751, by rfl⟩) R99503
theorem R131881 : Reach 131881 := rs (se 2 (by rfl) ⟨49455, by rfl⟩) R98911
theorem R66359 : Reach 66359 := rs (se 1 (by rfl) ⟨49769, by rfl⟩) R99539
theorem R230201 : Reach 230201 := rs (se 2 (by rfl) ⟨86325, by rfl⟩) R172651
theorem R131903 : Reach 131903 := rs (se 1 (by rfl) ⟨98927, by rfl⟩) R197855
theorem R99143 : Reach 99143 := rs (se 1 (by rfl) ⟨74357, by rfl⟩) R148715
theorem R66539 : Reach 66539 := rs (se 1 (by rfl) ⟨49904, by rfl⟩) R99809
theorem R67049 : Reach 67049 := rs (se 2 (by rfl) ⟨25143, by rfl⟩) R50287
theorem R722429 : Reach 722429 := rs (se 3 (by rfl) ⟨135455, by rfl⟩) R270911
theorem R100079 : Reach 100079 := rs (se 1 (by rfl) ⟨75059, by rfl⟩) R150119
theorem R11142947 : Reach 11142947 := rs (se 1 (by rfl) ⟨8357210, by rfl⟩) R16714421
theorem R67439 : Reach 67439 := rs (se 1 (by rfl) ⟨50579, by rfl⟩) R101159
theorem R1771469 : Reach 1771469 := rs (se 3 (by rfl) ⟨332150, by rfl⟩) R664301
theorem R100331 : Reach 100331 := rs (se 1 (by rfl) ⟨75248, by rfl⟩) R150497
theorem R67625 : Reach 67625 := rs (se 2 (by rfl) ⟨25359, by rfl⟩) R50719
theorem R67655 : Reach 67655 := rs (se 1 (by rfl) ⟨50741, by rfl⟩) R101483
theorem R67835 : Reach 67835 := rs (se 1 (by rfl) ⟨50876, by rfl⟩) R101753
theorem R68039 : Reach 68039 := rs (se 1 (by rfl) ⟨51029, by rfl⟩) R102059
theorem R231983 : Reach 231983 := rs (se 1 (by rfl) ⟨173987, by rfl⟩) R347975
theorem R68255 : Reach 68255 := rs (se 1 (by rfl) ⟨51191, by rfl⟩) R102383
theorem R68303 : Reach 68303 := rs (se 1 (by rfl) ⟨51227, by rfl⟩) R102455
theorem R330479 : Reach 330479 := rs (se 1 (by rfl) ⟨247859, by rfl⟩) R495719
theorem R68399 : Reach 68399 := rs (se 1 (by rfl) ⟨51299, by rfl⟩) R102599
theorem R68519 : Reach 68519 := rs (se 1 (by rfl) ⟨51389, by rfl⟩) R102779
theorem R756701 : Reach 756701 := rs (se 3 (by rfl) ⟨141881, by rfl⟩) R283763
theorem R68681 : Reach 68681 := rs (se 2 (by rfl) ⟨25755, by rfl⟩) R51511
theorem R68699 : Reach 68699 := rs (se 1 (by rfl) ⟨51524, by rfl⟩) R103049
theorem R68777 : Reach 68777 := rs (se 2 (by rfl) ⟨25791, by rfl⟩) R51583
theorem R68921 : Reach 68921 := rs (se 2 (by rfl) ⟨25845, by rfl⟩) R51691
theorem R69191 : Reach 69191 := rs (se 1 (by rfl) ⟨51893, by rfl⟩) R103787
theorem R69371 : Reach 69371 := rs (se 1 (by rfl) ⟨52028, by rfl⟩) R104057
theorem R69611 : Reach 69611 := rs (se 1 (by rfl) ⟨52208, by rfl⟩) R104417
theorem R102635 : Reach 102635 := rs (se 1 (by rfl) ⟨76976, by rfl⟩) R153953
theorem R102959 : Reach 102959 := rs (se 1 (by rfl) ⟨77219, by rfl⟩) R154439
theorem R856673 : Reach 856673 := rs (se 2 (by rfl) ⟨321252, by rfl⟩) R642505
theorem R70331 : Reach 70331 := rs (se 1 (by rfl) ⟨52748, by rfl⟩) R105497
theorem R234413 : Reach 234413 := rs (se 3 (by rfl) ⟨43952, by rfl⟩) R87905
theorem R70649 : Reach 70649 := rs (se 2 (by rfl) ⟨26493, by rfl⟩) R52987
theorem R103535 : Reach 103535 := rs (se 1 (by rfl) ⟨77651, by rfl⟩) R155303
theorem R562301 : Reach 562301 := rs (se 3 (by rfl) ⟨105431, by rfl⟩) R210863
theorem R103607 : Reach 103607 := rs (se 1 (by rfl) ⟨77705, by rfl⟩) R155411
theorem R70975 : Reach 70975 := rs (se 1 (by rfl) ⟨53231, by rfl⟩) R106463
theorem R71135 : Reach 71135 := rs (se 1 (by rfl) ⟨53351, by rfl⟩) R106703
theorem R71231 : Reach 71231 := rs (se 1 (by rfl) ⟨53423, by rfl⟩) R106847
theorem R71275 : Reach 71275 := rs (se 1 (by rfl) ⟨53456, by rfl⟩) R106913
theorem R268105 : Reach 268105 := rs (se 2 (by rfl) ⟨100539, by rfl⟩) R201079
theorem R464737 : Reach 464737 := rs (se 2 (by rfl) ⟨174276, by rfl⟩) R348553
theorem R235385 : Reach 235385 := rs (se 2 (by rfl) ⟨88269, by rfl⟩) R176539
theorem R236033 : Reach 236033 := rs (se 2 (by rfl) ⟨88512, by rfl⟩) R177025
theorem R334367 : Reach 334367 := rs (se 1 (by rfl) ⟨250775, by rfl⟩) R501551
theorem R105065 : Reach 105065 := rs (se 2 (by rfl) ⟨39399, by rfl⟩) R78799
theorem R236141 : Reach 236141 := rs (se 3 (by rfl) ⟨44276, by rfl⟩) R88553
theorem R957359 : Reach 957359 := rs (se 1 (by rfl) ⟨718019, by rfl⟩) R1436039
theorem R236641 : Reach 236641 := rs (se 2 (by rfl) ⟨88740, by rfl⟩) R177481
theorem R105695 : Reach 105695 := rs (se 1 (by rfl) ⟨79271, by rfl⟩) R158543
theorem R990575 : Reach 990575 := rs (se 1 (by rfl) ⟨742931, by rfl⟩) R1485863
theorem R171497 : Reach 171497 := rs (se 2 (by rfl) ⟨64311, by rfl⟩) R128623
theorem R270323 : Reach 270323 := rs (se 1 (by rfl) ⟨202742, by rfl⟩) R405485
theorem R500093 : Reach 500093 := rs (se 3 (by rfl) ⟨93767, by rfl⟩) R187535
theorem R74351 : Reach 74351 := rs (se 1 (by rfl) ⟨55763, by rfl⟩) R111527
theorem R74587 : Reach 74587 := rs (se 1 (by rfl) ⟨55940, by rfl⟩) R111881
theorem R238463 : Reach 238463 := rs (se 1 (by rfl) ⟨178847, by rfl⟩) R357695
theorem R140447 : Reach 140447 := rs (se 1 (by rfl) ⟨105335, by rfl⟩) R210671
theorem R74911 : Reach 74911 := rs (se 1 (by rfl) ⟨56183, by rfl⟩) R112367
theorem R1811915 : Reach 1811915 := rs (se 1 (by rfl) ⟨1358936, by rfl⟩) R2717873
theorem R861677 : Reach 861677 := rs (se 3 (by rfl) ⟨161564, by rfl⟩) R323129
theorem R370271 : Reach 370271 := rs (se 1 (by rfl) ⟨277703, by rfl⟩) R555407
theorem R403127 : Reach 403127 := rs (se 1 (by rfl) ⟨302345, by rfl⟩) R604691
theorem R75559 : Reach 75559 := rs (se 1 (by rfl) ⟨56669, by rfl⟩) R113339
theorem R108479 : Reach 108479 := rs (se 1 (by rfl) ⟨81359, by rfl⟩) R162719
theorem R43423 : Reach 43423 := rs (se 1 (by rfl) ⟨32567, by rfl⟩) R65135
theorem R43503 : Reach 43503 := rs (se 1 (by rfl) ⟨32627, by rfl⟩) R65255
theorem R141871 : Reach 141871 := rs (se 1 (by rfl) ⟨106403, by rfl⟩) R212807
theorem R43631 : Reach 43631 := rs (se 1 (by rfl) ⟨32723, by rfl⟩) R65447
theorem R43847 : Reach 43847 := rs (se 1 (by rfl) ⟨32885, by rfl⟩) R65771
theorem R43887 : Reach 43887 := rs (se 1 (by rfl) ⟨32915, by rfl⟩) R65831
theorem R109471 : Reach 109471 := rs (se 1 (by rfl) ⟨82103, by rfl⟩) R164207
theorem R2141315 : Reach 2141315 := rs (se 1 (by rfl) ⟨1605986, by rfl⟩) R3211973
theorem R44335 : Reach 44335 := rs (se 1 (by rfl) ⟨33251, by rfl⟩) R66503
theorem R109907 : Reach 109907 := rs (se 1 (by rfl) ⟨82430, by rfl⟩) R164861
theorem R44447 : Reach 44447 := rs (se 1 (by rfl) ⟨33335, by rfl⟩) R66671
theorem R44575 : Reach 44575 := rs (se 1 (by rfl) ⟨33431, by rfl⟩) R66863
theorem R44711 : Reach 44711 := rs (se 1 (by rfl) ⟨33533, by rfl⟩) R67067
theorem R44735 : Reach 44735 := rs (se 1 (by rfl) ⟨33551, by rfl⟩) R67103
theorem R44831 : Reach 44831 := rs (se 1 (by rfl) ⟨33623, by rfl⟩) R67247
theorem R44911 : Reach 44911 := rs (se 1 (by rfl) ⟨33683, by rfl⟩) R67367
theorem R110555 : Reach 110555 := rs (se 1 (by rfl) ⟨82916, by rfl⟩) R165833
theorem R77807 : Reach 77807 := rs (se 1 (by rfl) ⟨58355, by rfl⟩) R116711
theorem R110585 : Reach 110585 := rs (se 2 (by rfl) ⟨41469, by rfl⟩) R82939
theorem R45279 : Reach 45279 := rs (se 1 (by rfl) ⟨33959, by rfl⟩) R67919
theorem R340199 : Reach 340199 := rs (se 1 (by rfl) ⟨255149, by rfl⟩) R510299
theorem R45311 : Reach 45311 := rs (se 1 (by rfl) ⟨33983, by rfl⟩) R67967
theorem R45339 : Reach 45339 := rs (se 1 (by rfl) ⟨34004, by rfl⟩) R68009
theorem R110879 : Reach 110879 := rs (se 1 (by rfl) ⟨83159, by rfl⟩) R166319
theorem R45595 : Reach 45595 := rs (se 1 (by rfl) ⟨34196, by rfl⟩) R68393
theorem R111233 : Reach 111233 := rs (se 2 (by rfl) ⟨41712, by rfl⟩) R83425
theorem R45735 : Reach 45735 := rs (se 1 (by rfl) ⟨34301, by rfl⟩) R68603
theorem R45775 : Reach 45775 := rs (se 1 (by rfl) ⟨34331, by rfl⟩) R68663
theorem R45855 : Reach 45855 := rs (se 1 (by rfl) ⟨34391, by rfl⟩) R68783
theorem R45863 : Reach 45863 := rs (se 1 (by rfl) ⟨34397, by rfl⟩) R68795
theorem R111415 : Reach 111415 := rs (se 1 (by rfl) ⟨83561, by rfl⟩) R167123
theorem R209747 : Reach 209747 := rs (se 1 (by rfl) ⟨157310, by rfl⟩) R314621
theorem R898037 : Reach 898037 := rs (se 5 (by rfl) ⟨42095, by rfl⟩) R84191
theorem R46335 : Reach 46335 := rs (se 1 (by rfl) ⟨34751, by rfl⟩) R69503
theorem R79103 : Reach 79103 := rs (se 1 (by rfl) ⟨59327, by rfl⟩) R118655
theorem R46463 : Reach 46463 := rs (se 1 (by rfl) ⟨34847, by rfl⟩) R69695
theorem R112043 : Reach 112043 := rs (se 1 (by rfl) ⟨84032, by rfl⟩) R168065
theorem R46619 : Reach 46619 := rs (se 1 (by rfl) ⟨34964, by rfl⟩) R69929
theorem R46799 : Reach 46799 := rs (se 1 (by rfl) ⟨35099, by rfl⟩) R70199
theorem R3389303 : Reach 3389303 := rs (se 1 (by rfl) ⟨2541977, by rfl⟩) R5083955
theorem R47039 : Reach 47039 := rs (se 1 (by rfl) ⟨35279, by rfl⟩) R70559
theorem R178301 : Reach 178301 := rs (se 3 (by rfl) ⟨33431, by rfl⟩) R66863
theorem R112823 : Reach 112823 := rs (se 1 (by rfl) ⟨84617, by rfl⟩) R169235
theorem R113035 : Reach 113035 := rs (se 1 (by rfl) ⟨84776, by rfl⟩) R169553
theorem R113825 : Reach 113825 := rs (se 2 (by rfl) ⟨42684, by rfl⟩) R85369
theorem R114655 : Reach 114655 := rs (se 1 (by rfl) ⟨85991, by rfl⟩) R171983
theorem R377303 : Reach 377303 := rs (se 1 (by rfl) ⟨282977, by rfl⟩) R565955
theorem R49639 : Reach 49639 := rs (se 1 (by rfl) ⟨37229, by rfl⟩) R74459
theorem R115283 : Reach 115283 := rs (se 1 (by rfl) ⟨86462, by rfl⟩) R172925
theorem R50503 : Reach 50503 := rs (se 1 (by rfl) ⟨37877, by rfl⟩) R75755
theorem R280331 : Reach 280331 := rs (se 1 (by rfl) ⟨210248, by rfl⟩) R420497
theorem R117119 : Reach 117119 := rs (se 1 (by rfl) ⟨87839, by rfl⟩) R175679
theorem R150281 : Reach 150281 := rs (se 2 (by rfl) ⟨56355, by rfl⟩) R112711
theorem R84959 : Reach 84959 := rs (se 1 (by rfl) ⟨63719, by rfl⟩) R127439
theorem R249227 : Reach 249227 := rs (se 1 (by rfl) ⟨186920, by rfl⟩) R373841
theorem R315065 : Reach 315065 := rs (se 2 (by rfl) ⟨118149, by rfl⟩) R236299
theorem R479159 : Reach 479159 := rs (se 1 (by rfl) ⟨359369, by rfl⟩) R718739
theorem R118847 : Reach 118847 := rs (se 1 (by rfl) ⟨89135, by rfl⟩) R178271
theorem R249979 : Reach 249979 := rs (se 1 (by rfl) ⟨187484, by rfl⟩) R374969
theorem R479825 : Reach 479825 := rs (se 2 (by rfl) ⟨179934, by rfl⟩) R359869
theorem R152171 : Reach 152171 := rs (se 1 (by rfl) ⟨114128, by rfl⟩) R228257
theorem R3822329 : Reach 3822329 := rs (se 2 (by rfl) ⟨1433373, by rfl⟩) R2866747
theorem R348947 : Reach 348947 := rs (se 1 (by rfl) ⟨261710, by rfl⟩) R523421
theorem R54523 : Reach 54523 := rs (se 1 (by rfl) ⟨40892, by rfl⟩) R81785
theorem R185971 : Reach 185971 := rs (se 1 (by rfl) ⟨139478, by rfl⟩) R278957
theorem R251687 : Reach 251687 := rs (se 1 (by rfl) ⟨188765, by rfl⟩) R377531
theorem R219023 : Reach 219023 := rs (se 1 (by rfl) ⟨164267, by rfl⟩) R328535
theorem R153737 : Reach 153737 := rs (se 2 (by rfl) ⟨57651, by rfl⟩) R115303
theorem R153791 : Reach 153791 := rs (se 1 (by rfl) ⟨115343, by rfl⟩) R230687
theorem R219743 : Reach 219743 := rs (se 1 (by rfl) ⟨164807, by rfl⟩) R329615
theorem R1432403 : Reach 1432403 := rs (se 1 (by rfl) ⟨1074302, by rfl⟩) R2148605
theorem R220249 : Reach 220249 := rs (se 2 (by rfl) ⟨82593, by rfl⟩) R165187
theorem R56551 : Reach 56551 := rs (se 1 (by rfl) ⟨42413, by rfl⟩) R84827
theorem R123133 : Reach 123133 := rs (se 3 (by rfl) ⟨23087, by rfl⟩) R46175
theorem R319783 : Reach 319783 := rs (se 1 (by rfl) ⟨239837, by rfl⟩) R479675
theorem R123191 : Reach 123191 := rs (se 1 (by rfl) ⟨92393, by rfl⟩) R184787
theorem R57721 : Reach 57721 := rs (se 2 (by rfl) ⟨21645, by rfl⟩) R43291
theorem R156167 : Reach 156167 := rs (se 1 (by rfl) ⟨117125, by rfl⟩) R234251
theorem R221777 : Reach 221777 := rs (se 2 (by rfl) ⟨83166, by rfl⟩) R166333
theorem R156545 : Reach 156545 := rs (se 2 (by rfl) ⟨58704, by rfl⟩) R117409
theorem R189449 : Reach 189449 := rs (se 2 (by rfl) ⟨71043, by rfl⟩) R142087
theorem R157085 : Reach 157085 := rs (se 3 (by rfl) ⟨29453, by rfl⟩) R58907
theorem R157247 : Reach 157247 := rs (se 1 (by rfl) ⟨117935, by rfl⟩) R235871
theorem R124523 : Reach 124523 := rs (se 1 (by rfl) ⟨93392, by rfl⟩) R186785
theorem R124903 : Reach 124903 := rs (se 1 (by rfl) ⟨93677, by rfl⟩) R187355
theorem R223211 : Reach 223211 := rs (se 1 (by rfl) ⟨167408, by rfl⟩) R334817
theorem R289295 : Reach 289295 := rs (se 1 (by rfl) ⟨216971, by rfl⟩) R433943
theorem R60059 : Reach 60059 := rs (se 1 (by rfl) ⟨45044, by rfl⟩) R90089
theorem R553661 : Reach 553661 := rs (se 3 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R226313 : Reach 226313 := rs (se 2 (by rfl) ⟨84867, by rfl⟩) R169735
theorem R129215 : Reach 129215 := rs (se 1 (by rfl) ⟨96911, by rfl⟩) R193823
theorem R1112363 : Reach 1112363 := rs (se 1 (by rfl) ⟨834272, by rfl⟩) R1668545
theorem R96673 : Reach 96673 := rs (se 2 (by rfl) ⟨36252, by rfl⟩) R72505
theorem R588545 : Reach 588545 := rs (se 2 (by rfl) ⟨220704, by rfl⟩) R441409
theorem R195809 : Reach 195809 := rs (se 2 (by rfl) ⟨73428, by rfl⟩) R146857
theorem R64823 : Reach 64823 := rs (se 1 (by rfl) ⟨48617, by rfl⟩) R97235
theorem R65003 : Reach 65003 := rs (se 1 (by rfl) ⟨48752, by rfl⟩) R97505
theorem R97775 : Reach 97775 := rs (se 1 (by rfl) ⟨73331, by rfl⟩) R146663
theorem R130697 : Reach 130697 := rs (se 2 (by rfl) ⟨49011, by rfl⟩) R98023
theorem R65207 : Reach 65207 := rs (se 1 (by rfl) ⟨48905, by rfl⟩) R97811
theorem R491345 : Reach 491345 := rs (se 2 (by rfl) ⟨184254, by rfl⟩) R368509
theorem R65417 : Reach 65417 := rs (se 2 (by rfl) ⟨24531, by rfl⟩) R49063
theorem R164177 : Reach 164177 := rs (se 2 (by rfl) ⟨61566, by rfl⟩) R123133
theorem R196967 : Reach 196967 := rs (se 1 (by rfl) ⟨147725, by rfl⟩) R295451
theorem R426377 : Reach 426377 := rs (se 2 (by rfl) ⟨159891, by rfl⟩) R319783
theorem R262543 : Reach 262543 := rs (se 1 (by rfl) ⟨196907, by rfl⟩) R393815
theorem R66095 : Reach 66095 := rs (se 1 (by rfl) ⟨49571, by rfl⟩) R99143
theorem R66185 : Reach 66185 := rs (se 2 (by rfl) ⟨24819, by rfl⟩) R49639
theorem R99449 : Reach 99449 := rs (se 2 (by rfl) ⟨37293, by rfl⟩) R74587
theorem R66719 : Reach 66719 := rs (se 1 (by rfl) ⟨50039, by rfl⟩) R100079
theorem R1180979 : Reach 1180979 := rs (se 1 (by rfl) ⟨885734, by rfl⟩) R1771469
theorem R66887 : Reach 66887 := rs (se 1 (by rfl) ⟨50165, by rfl⟩) R100331
theorem R99881 : Reach 99881 := rs (se 2 (by rfl) ⟨37455, by rfl⟩) R74911
theorem R67337 : Reach 67337 := rs (se 2 (by rfl) ⟨25251, by rfl⟩) R50503
theorem R100187 : Reach 100187 := rs (se 1 (by rfl) ⟨75140, by rfl⟩) R150281
theorem R10192877 : Reach 10192877 := rs (se 3 (by rfl) ⟨1911164, by rfl⟩) R3822329
theorem R559325 : Reach 559325 := rs (se 3 (by rfl) ⟨104873, by rfl⟩) R209747
theorem R166151 : Reach 166151 := rs (se 1 (by rfl) ⟨124613, by rfl⟩) R249227
theorem R100745 : Reach 100745 := rs (se 2 (by rfl) ⟨37779, by rfl⟩) R75559
theorem R166537 : Reach 166537 := rs (se 2 (by rfl) ⟨62451, by rfl⟩) R124903
theorem R68423 : Reach 68423 := rs (se 1 (by rfl) ⟨51317, by rfl⟩) R102635
theorem R68639 : Reach 68639 := rs (se 1 (by rfl) ⟨51479, by rfl⟩) R102959
theorem R101447 : Reach 101447 := rs (se 1 (by rfl) ⟨76085, by rfl⟩) R152171
theorem R232631 : Reach 232631 := rs (se 1 (by rfl) ⟨174473, by rfl⟩) R348947
theorem R69023 : Reach 69023 := rs (se 1 (by rfl) ⟨51767, by rfl⟩) R103535
theorem R69071 : Reach 69071 := rs (se 1 (by rfl) ⟨51803, by rfl⟩) R103607
theorem R167791 : Reach 167791 := rs (se 1 (by rfl) ⟨125843, by rfl⟩) R251687
theorem R102491 : Reach 102491 := rs (se 1 (by rfl) ⟨76868, by rfl⟩) R153737
theorem R102527 : Reach 102527 := rs (se 1 (by rfl) ⟨76895, by rfl⟩) R153791
theorem R70043 : Reach 70043 := rs (se 1 (by rfl) ⟨52532, by rfl⟩) R105065
theorem R954935 : Reach 954935 := rs (se 1 (by rfl) ⟨716201, by rfl⟩) R1432403
theorem R70463 : Reach 70463 := rs (se 1 (by rfl) ⟨52847, by rfl⟩) R105695
theorem R660383 : Reach 660383 := rs (se 1 (by rfl) ⟨495287, by rfl⟩) R990575
theorem R333305 : Reach 333305 := rs (se 2 (by rfl) ⟨124989, by rfl⟩) R249979
theorem R333395 : Reach 333395 := rs (se 1 (by rfl) ⟨250046, by rfl⟩) R500093
theorem R104111 : Reach 104111 := rs (se 1 (by rfl) ⟨78083, by rfl⟩) R156167
theorem R104363 : Reach 104363 := rs (se 1 (by rfl) ⟨78272, by rfl⟩) R156545
theorem R104723 : Reach 104723 := rs (se 1 (by rfl) ⟨78542, by rfl⟩) R157085
theorem R104831 : Reach 104831 := rs (se 1 (by rfl) ⟨78623, by rfl⟩) R157247
theorem R268751 : Reach 268751 := rs (se 1 (by rfl) ⟨201563, by rfl⟩) R403127
theorem R73271 : Reach 73271 := rs (se 1 (by rfl) ⟨54953, by rfl⟩) R109907
theorem R73703 : Reach 73703 := rs (se 1 (by rfl) ⟨55277, by rfl⟩) R110555
theorem R73723 : Reach 73723 := rs (se 1 (by rfl) ⟨55292, by rfl⟩) R110585
theorem R73919 : Reach 73919 := rs (se 1 (by rfl) ⟨55439, by rfl⟩) R110879
theorem R74155 : Reach 74155 := rs (se 1 (by rfl) ⟨55616, by rfl⟩) R111233
theorem R369107 : Reach 369107 := rs (se 1 (by rfl) ⟨276830, by rfl⟩) R553661
theorem R598691 : Reach 598691 := rs (se 1 (by rfl) ⟨449018, by rfl⟩) R898037
theorem R74695 : Reach 74695 := rs (se 1 (by rfl) ⟨56021, by rfl⟩) R112043
theorem R75215 : Reach 75215 := rs (se 1 (by rfl) ⟨56411, by rfl⟩) R112823
theorem R75401 : Reach 75401 := rs (se 2 (by rfl) ⟨28275, by rfl⟩) R56551
theorem R75883 : Reach 75883 := rs (se 1 (by rfl) ⟨56912, by rfl⟩) R113825
theorem R43215 : Reach 43215 := rs (se 1 (by rfl) ⟨32411, by rfl⟩) R64823
theorem R43335 : Reach 43335 := rs (se 1 (by rfl) ⟨32501, by rfl⟩) R65003
theorem R43471 : Reach 43471 := rs (se 1 (by rfl) ⟨32603, by rfl⟩) R65207
theorem R43611 : Reach 43611 := rs (se 1 (by rfl) ⟨32708, by rfl⟩) R65417
theorem R43775 : Reach 43775 := rs (se 1 (by rfl) ⟨32831, by rfl⟩) R65663
theorem R43967 : Reach 43967 := rs (se 1 (by rfl) ⟨32975, by rfl⟩) R65951
theorem R76855 : Reach 76855 := rs (se 1 (by rfl) ⟨57641, by rfl⟩) R115283
theorem R44143 : Reach 44143 := rs (se 1 (by rfl) ⟨33107, by rfl⟩) R66215
theorem R76961 : Reach 76961 := rs (se 2 (by rfl) ⟨28860, by rfl⟩) R57721
theorem R44223 : Reach 44223 := rs (se 1 (by rfl) ⟨33167, by rfl⟩) R66335
theorem R44239 : Reach 44239 := rs (se 1 (by rfl) ⟨33179, by rfl⟩) R66359
theorem R44359 : Reach 44359 := rs (se 1 (by rfl) ⟨33269, by rfl⟩) R66539
theorem R44699 : Reach 44699 := rs (se 1 (by rfl) ⟨33524, by rfl⟩) R67049
theorem R175841 : Reach 175841 := rs (se 2 (by rfl) ⟨65940, by rfl⟩) R131881
theorem R44959 : Reach 44959 := rs (se 1 (by rfl) ⟨33719, by rfl⟩) R67439
theorem R45083 : Reach 45083 := rs (se 1 (by rfl) ⟨33812, by rfl⟩) R67625
theorem R45103 : Reach 45103 := rs (se 1 (by rfl) ⟨33827, by rfl⟩) R67655
theorem R45223 : Reach 45223 := rs (se 1 (by rfl) ⟨33917, by rfl⟩) R67835
theorem R78079 : Reach 78079 := rs (se 1 (by rfl) ⟨58559, by rfl⟩) R117119
theorem R45359 : Reach 45359 := rs (se 1 (by rfl) ⟨34019, by rfl⟩) R68039
theorem R45503 : Reach 45503 := rs (se 1 (by rfl) ⟨34127, by rfl⟩) R68255
theorem R45535 : Reach 45535 := rs (se 1 (by rfl) ⟨34151, by rfl⟩) R68303
theorem R45599 : Reach 45599 := rs (se 1 (by rfl) ⟨34199, by rfl⟩) R68399
theorem R45679 : Reach 45679 := rs (se 1 (by rfl) ⟨34259, by rfl⟩) R68519
theorem R504467 : Reach 504467 := rs (se 1 (by rfl) ⟨378350, by rfl⟩) R756701
theorem R45787 : Reach 45787 := rs (se 1 (by rfl) ⟨34340, by rfl⟩) R68681
theorem R45799 : Reach 45799 := rs (se 1 (by rfl) ⟨34349, by rfl⟩) R68699
theorem R45851 : Reach 45851 := rs (se 1 (by rfl) ⟨34388, by rfl⟩) R68777
theorem R45947 : Reach 45947 := rs (se 1 (by rfl) ⟨34460, by rfl⟩) R68921
theorem R46127 : Reach 46127 := rs (se 1 (by rfl) ⟨34595, by rfl⟩) R69191
theorem R210043 : Reach 210043 := rs (se 1 (by rfl) ⟨157532, by rfl⟩) R315065
theorem R46247 : Reach 46247 := rs (se 1 (by rfl) ⟨34685, by rfl⟩) R69371
theorem R46407 : Reach 46407 := rs (se 1 (by rfl) ⟨34805, by rfl⟩) R69611
theorem R79231 : Reach 79231 := rs (se 1 (by rfl) ⟨59423, by rfl⟩) R118847
theorem R571115 : Reach 571115 := rs (se 1 (by rfl) ⟨428336, by rfl⟩) R856673
theorem R46887 : Reach 46887 := rs (se 1 (by rfl) ⟨35165, by rfl⟩) R70331
theorem R47099 : Reach 47099 := rs (se 1 (by rfl) ⟨35324, by rfl⟩) R70649
theorem R374867 : Reach 374867 := rs (se 1 (by rfl) ⟨281150, by rfl⟩) R562301
theorem R47423 : Reach 47423 := rs (se 1 (by rfl) ⟨35567, by rfl⟩) R71135
theorem R145961 : Reach 145961 := rs (se 2 (by rfl) ⟨54735, by rfl⟩) R109471
theorem R146015 : Reach 146015 := rs (se 1 (by rfl) ⟨109511, by rfl⟩) R219023
theorem R146495 : Reach 146495 := rs (se 1 (by rfl) ⟨109871, by rfl⟩) R219743
theorem R638239 : Reach 638239 := rs (se 1 (by rfl) ⟨478679, by rfl⟩) R957359
theorem R114331 : Reach 114331 := rs (se 1 (by rfl) ⟨85748, by rfl⟩) R171497
theorem R180215 : Reach 180215 := rs (se 1 (by rfl) ⟨135161, by rfl⟩) R270323
theorem R82127 : Reach 82127 := rs (se 1 (by rfl) ⟨61595, by rfl⟩) R123191
theorem R147851 : Reach 147851 := rs (se 1 (by rfl) ⟨110888, by rfl⟩) R221777
theorem R49567 : Reach 49567 := rs (se 1 (by rfl) ⟨37175, by rfl⟩) R74351
theorem R344573 : Reach 344573 := rs (se 3 (by rfl) ⟨64607, by rfl⟩) R129215
theorem R574451 : Reach 574451 := rs (se 1 (by rfl) ⟨430838, by rfl⟩) R861677
theorem R246847 : Reach 246847 := rs (se 1 (by rfl) ⟨185135, by rfl⟩) R370271
theorem R83015 : Reach 83015 := rs (se 1 (by rfl) ⟨62261, by rfl⟩) R124523
theorem R148553 : Reach 148553 := rs (se 2 (by rfl) ⟨55707, by rfl⟩) R111415
theorem R148807 : Reach 148807 := rs (se 1 (by rfl) ⟨111605, by rfl⟩) R223211
theorem R378533 : Reach 378533 := rs (se 4 (by rfl) ⟨35487, by rfl⟩) R70975
theorem R1427543 : Reach 1427543 := rs (se 1 (by rfl) ⟨1070657, by rfl⟩) R2141315
theorem R247961 : Reach 247961 := rs (se 2 (by rfl) ⟨92985, by rfl⟩) R185971
theorem R51871 : Reach 51871 := rs (se 1 (by rfl) ⟨38903, by rfl⟩) R77807
theorem R150713 : Reach 150713 := rs (se 2 (by rfl) ⟨56517, by rfl⟩) R113035
theorem R150875 : Reach 150875 := rs (se 1 (by rfl) ⟨113156, by rfl⟩) R226313
theorem R52735 : Reach 52735 := rs (se 1 (by rfl) ⟨39551, by rfl⟩) R79103
theorem R118867 : Reach 118867 := rs (se 1 (by rfl) ⟨89150, by rfl⟩) R178301
theorem R315521 : Reach 315521 := rs (se 2 (by rfl) ⟨118320, by rfl⟩) R236641
theorem R741575 : Reach 741575 := rs (se 1 (by rfl) ⟨556181, by rfl⟩) R1112363
theorem R87131 : Reach 87131 := rs (se 1 (by rfl) ⟨65348, by rfl⟩) R130697
theorem R152873 : Reach 152873 := rs (se 2 (by rfl) ⟨57327, by rfl⟩) R114655
theorem R87655 : Reach 87655 := rs (se 1 (by rfl) ⟨65741, by rfl⟩) R131483
theorem R153467 : Reach 153467 := rs (se 1 (by rfl) ⟨115100, by rfl⟩) R230201
theorem R87935 : Reach 87935 := rs (se 1 (by rfl) ⟨65951, by rfl⟩) R131903
theorem R481619 : Reach 481619 := rs (se 1 (by rfl) ⟨361214, by rfl⟩) R722429
theorem R186887 : Reach 186887 := rs (se 1 (by rfl) ⟨140165, by rfl⟩) R280331
theorem R7428631 : Reach 7428631 := rs (se 1 (by rfl) ⟨5571473, by rfl⟩) R11142947
theorem R1006141 : Reach 1006141 := rs (se 3 (by rfl) ⟨188651, by rfl⟩) R377303
theorem R154655 : Reach 154655 := rs (se 1 (by rfl) ⟨115991, by rfl⟩) R231983
theorem R220319 : Reach 220319 := rs (se 1 (by rfl) ⟨165239, by rfl⟩) R330479
theorem R56639 : Reach 56639 := rs (se 1 (by rfl) ⟨42479, by rfl⟩) R84959
theorem R2088629 : Reach 2088629 := rs (se 5 (by rfl) ⟨97904, by rfl⟩) R195809
theorem R319439 : Reach 319439 := rs (se 1 (by rfl) ⟨239579, by rfl⟩) R479159
theorem R319883 : Reach 319883 := rs (se 1 (by rfl) ⟨239912, by rfl⟩) R479825
theorem R156275 : Reach 156275 := rs (se 1 (by rfl) ⟨117206, by rfl⟩) R234413
theorem R189161 : Reach 189161 := rs (se 2 (by rfl) ⟨70935, by rfl⟩) R141871
theorem R156923 : Reach 156923 := rs (se 1 (by rfl) ⟨117692, by rfl⟩) R235385
theorem R189949 : Reach 189949 := rs (se 3 (by rfl) ⟨35615, by rfl⟩) R71231
theorem R157355 : Reach 157355 := rs (se 1 (by rfl) ⟨118016, by rfl⟩) R236033
theorem R222911 : Reach 222911 := rs (se 1 (by rfl) ⟨167183, by rfl⟩) R334367
theorem R157427 : Reach 157427 := rs (se 1 (by rfl) ⟨118070, by rfl⟩) R236141
theorem R9038141 : Reach 9038141 := rs (se 3 (by rfl) ⟨1694651, by rfl⟩) R3389303
theorem R289277 : Reach 289277 := rs (se 3 (by rfl) ⟨54239, by rfl⟩) R108479
theorem R158975 : Reach 158975 := rs (se 1 (by rfl) ⟨119231, by rfl⟩) R238463
theorem R126299 : Reach 126299 := rs (se 1 (by rfl) ⟨94724, by rfl⟩) R189449
theorem R93631 : Reach 93631 := rs (se 1 (by rfl) ⟨70223, by rfl⟩) R140447
theorem R1207943 : Reach 1207943 := rs (se 1 (by rfl) ⟨905957, by rfl⟩) R1811915
theorem R290789 : Reach 290789 := rs (se 4 (by rfl) ⟨27261, by rfl⟩) R54523
theorem R192863 : Reach 192863 := rs (se 1 (by rfl) ⟨144647, by rfl⟩) R289295
theorem R160157 : Reach 160157 := rs (se 3 (by rfl) ⟨30029, by rfl⟩) R60059
theorem R95033 : Reach 95033 := rs (se 2 (by rfl) ⟨35637, by rfl⟩) R71275
theorem R357473 : Reach 357473 := rs (se 2 (by rfl) ⟨134052, by rfl⟩) R268105
theorem R619649 : Reach 619649 := rs (se 2 (by rfl) ⟨232368, by rfl⟩) R464737
theorem R226799 : Reach 226799 := rs (se 1 (by rfl) ⟨170099, by rfl⟩) R340199
theorem R128897 : Reach 128897 := rs (se 2 (by rfl) ⟨48336, by rfl⟩) R96673
theorem R293665 : Reach 293665 := rs (se 2 (by rfl) ⟨110124, by rfl⟩) R220249
theorem R392363 : Reach 392363 := rs (se 1 (by rfl) ⟨294272, by rfl⟩) R588545
theorem R65183 : Reach 65183 := rs (se 1 (by rfl) ⟨48887, by rfl⟩) R97775
theorem R327563 : Reach 327563 := rs (se 1 (by rfl) ⟨245672, by rfl⟩) R491345
theorem R131311 : Reach 131311 := rs (se 1 (by rfl) ⟨98483, by rfl⟩) R196967
theorem R98567 : Reach 98567 := rs (se 1 (by rfl) ⟨73925, by rfl⟩) R147851
theorem R229715 : Reach 229715 := rs (se 1 (by rfl) ⟨172286, by rfl⟩) R344573
theorem R66089 : Reach 66089 := rs (se 2 (by rfl) ⟨24783, by rfl⟩) R49567
theorem R98873 : Reach 98873 := rs (se 2 (by rfl) ⟨37077, by rfl⟩) R74155
theorem R99035 : Reach 99035 := rs (se 1 (by rfl) ⟨74276, by rfl⟩) R148553
theorem R66299 : Reach 66299 := rs (se 1 (by rfl) ⟨49724, by rfl⟩) R99449
theorem R787319 : Reach 787319 := rs (se 1 (by rfl) ⟨590489, by rfl⟩) R1180979
theorem R66587 : Reach 66587 := rs (se 1 (by rfl) ⟨49940, by rfl⟩) R99881
theorem R853021 : Reach 853021 := rs (se 3 (by rfl) ⟨159941, by rfl⟩) R319883
theorem R66791 : Reach 66791 := rs (se 1 (by rfl) ⟨50093, by rfl⟩) R100187
theorem R99593 : Reach 99593 := rs (se 2 (by rfl) ⟨37347, by rfl⟩) R74695
theorem R951695 : Reach 951695 := rs (se 1 (by rfl) ⟨713771, by rfl⟩) R1427543
theorem R329129 : Reach 329129 := rs (se 2 (by rfl) ⟨123423, by rfl⟩) R246847
theorem R165307 : Reach 165307 := rs (se 1 (by rfl) ⟨123980, by rfl⟩) R247961
theorem R67163 : Reach 67163 := rs (se 1 (by rfl) ⟨50372, by rfl⟩) R100745
theorem R198409 : Reach 198409 := rs (se 2 (by rfl) ⟨74403, by rfl⟩) R148807
theorem R67631 : Reach 67631 := rs (se 1 (by rfl) ⟨50723, by rfl⟩) R101447
theorem R100475 : Reach 100475 := rs (se 1 (by rfl) ⟨75356, by rfl⟩) R150713
theorem R100583 : Reach 100583 := rs (se 1 (by rfl) ⟨75437, by rfl⟩) R150875
theorem R68327 : Reach 68327 := rs (se 1 (by rfl) ⟨51245, by rfl⟩) R102491
theorem R68351 : Reach 68351 := rs (se 1 (by rfl) ⟨51263, by rfl⟩) R102527
theorem R494383 : Reach 494383 := rs (se 1 (by rfl) ⟨370787, by rfl⟩) R741575
theorem R101177 : Reach 101177 := rs (se 2 (by rfl) ⟨37941, by rfl⟩) R75883
theorem R101915 : Reach 101915 := rs (se 1 (by rfl) ⟨76436, by rfl⟩) R152873
theorem R69161 : Reach 69161 := rs (se 2 (by rfl) ⟨25935, by rfl⟩) R51871
theorem R69407 : Reach 69407 := rs (se 1 (by rfl) ⟨52055, by rfl⟩) R104111
theorem R102311 : Reach 102311 := rs (se 1 (by rfl) ⟨76733, by rfl⟩) R153467
theorem R69575 : Reach 69575 := rs (se 1 (by rfl) ⟨52181, by rfl⟩) R104363
theorem R102473 : Reach 102473 := rs (se 2 (by rfl) ⟨38427, by rfl⟩) R76855
theorem R69815 : Reach 69815 := rs (se 1 (by rfl) ⟨52361, by rfl⟩) R104723
theorem R69887 : Reach 69887 := rs (se 1 (by rfl) ⟨52415, by rfl⟩) R104831
theorem R70313 : Reach 70313 := rs (se 2 (by rfl) ⟨26367, by rfl⟩) R52735
theorem R103103 : Reach 103103 := rs (se 1 (by rfl) ⟨77327, by rfl⟩) R154655
theorem R104105 : Reach 104105 := rs (se 2 (by rfl) ⟨39039, by rfl⟩) R78079
theorem R104183 : Reach 104183 := rs (se 1 (by rfl) ⟨78137, by rfl⟩) R156275
theorem R399127 : Reach 399127 := rs (se 1 (by rfl) ⟨299345, by rfl⟩) R598691
theorem R104615 : Reach 104615 := rs (se 1 (by rfl) ⟨78461, by rfl⟩) R156923
theorem R104903 : Reach 104903 := rs (se 1 (by rfl) ⟨78677, by rfl⟩) R157355
theorem R104951 : Reach 104951 := rs (se 1 (by rfl) ⟨78713, by rfl⟩) R157427
theorem R105641 : Reach 105641 := rs (se 2 (by rfl) ⟨39615, by rfl⟩) R79231
theorem R105983 : Reach 105983 := rs (se 1 (by rfl) ⟨79487, by rfl⟩) R158975
theorem R106771 : Reach 106771 := rs (se 1 (by rfl) ⟨80078, by rfl⟩) R160157
theorem R205229 : Reach 205229 := rs (se 3 (by rfl) ⟨38480, by rfl⟩) R76961
theorem R336311 : Reach 336311 := rs (se 1 (by rfl) ⟨252233, by rfl⟩) R504467
theorem R9904841 : Reach 9904841 := rs (se 2 (by rfl) ⟨3714315, by rfl⟩) R7428631
theorem R238315 : Reach 238315 := rs (se 1 (by rfl) ⟨178736, by rfl⟩) R357473
theorem R336797 : Reach 336797 := rs (se 3 (by rfl) ⟨63149, by rfl⟩) R126299
theorem R43455 : Reach 43455 := rs (se 1 (by rfl) ⟨32591, by rfl⟩) R65183
theorem R109451 : Reach 109451 := rs (se 1 (by rfl) ⟨82088, by rfl⟩) R164177
theorem R44063 : Reach 44063 := rs (se 1 (by rfl) ⟨33047, by rfl⟩) R66095
theorem R44123 : Reach 44123 := rs (se 1 (by rfl) ⟨33092, by rfl⟩) R66185
theorem R44479 : Reach 44479 := rs (se 1 (by rfl) ⟨33359, by rfl⟩) R66719
theorem R44591 : Reach 44591 := rs (se 1 (by rfl) ⟨33443, by rfl⟩) R66887
theorem R44891 : Reach 44891 := rs (se 1 (by rfl) ⟨33668, by rfl⟩) R67337
theorem R6795251 : Reach 6795251 := rs (se 1 (by rfl) ⟨5096438, by rfl⟩) R10192877
theorem R372883 : Reach 372883 := rs (se 1 (by rfl) ⟨279662, by rfl⟩) R559325
theorem R110767 : Reach 110767 := rs (se 1 (by rfl) ⟨83075, by rfl⟩) R166151
theorem R45615 : Reach 45615 := rs (se 1 (by rfl) ⟨34211, by rfl⟩) R68423
theorem R45759 : Reach 45759 := rs (se 1 (by rfl) ⟨34319, by rfl⟩) R68639
theorem R46015 : Reach 46015 := rs (se 1 (by rfl) ⟨34511, by rfl⟩) R69023
theorem R46047 : Reach 46047 := rs (se 1 (by rfl) ⟨34535, by rfl⟩) R69071
theorem R210347 : Reach 210347 := rs (se 1 (by rfl) ⟨157760, by rfl⟩) R315521
theorem R46695 : Reach 46695 := rs (se 1 (by rfl) ⟨35021, by rfl⟩) R70043
theorem R636623 : Reach 636623 := rs (se 1 (by rfl) ⟨477467, by rfl⟩) R954935
theorem R46975 : Reach 46975 := rs (se 1 (by rfl) ⟨35231, by rfl⟩) R70463
theorem R440255 : Reach 440255 := rs (se 1 (by rfl) ⟨330191, by rfl⟩) R660383
theorem R179167 : Reach 179167 := rs (se 1 (by rfl) ⟨134375, by rfl⟩) R268751
theorem R146879 : Reach 146879 := rs (se 1 (by rfl) ⟨110159, by rfl⟩) R220319
theorem R48847 : Reach 48847 := rs (se 1 (by rfl) ⟨36635, by rfl⟩) R73271
theorem R1392419 : Reach 1392419 := rs (se 1 (by rfl) ⟨1044314, by rfl⟩) R2088629
theorem R212959 : Reach 212959 := rs (se 1 (by rfl) ⟨159719, by rfl⟩) R319439
theorem R49135 : Reach 49135 := rs (se 1 (by rfl) ⟨36851, by rfl⟩) R73703
theorem R49279 : Reach 49279 := rs (se 1 (by rfl) ⟨36959, by rfl⟩) R73919
theorem R246071 : Reach 246071 := rs (se 1 (by rfl) ⟨184553, by rfl⟩) R369107
theorem R50143 : Reach 50143 := rs (se 1 (by rfl) ⟨37607, by rfl⟩) R75215
theorem R50267 : Reach 50267 := rs (se 1 (by rfl) ⟨37700, by rfl⟩) R75401
theorem R148607 : Reach 148607 := rs (se 1 (by rfl) ⟨111455, by rfl⟩) R222911
theorem R280057 : Reach 280057 := rs (se 2 (by rfl) ⟨105021, by rfl⟩) R210043
theorem R116873 : Reach 116873 := rs (se 2 (by rfl) ⟨43827, by rfl⟩) R87655
theorem R805295 : Reach 805295 := rs (se 1 (by rfl) ⟨603971, by rfl⟩) R1207943
theorem R117227 : Reach 117227 := rs (se 1 (by rfl) ⟨87920, by rfl⟩) R175841
theorem R413099 : Reach 413099 := rs (se 1 (by rfl) ⟨309824, by rfl⟩) R619649
theorem R151037 : Reach 151037 := rs (se 3 (by rfl) ⟨28319, by rfl⟩) R56639
theorem R151199 : Reach 151199 := rs (se 1 (by rfl) ⟨113399, by rfl⟩) R226799
theorem R380743 : Reach 380743 := rs (se 1 (by rfl) ⟨285557, by rfl⟩) R571115
theorem R85931 : Reach 85931 := rs (se 1 (by rfl) ⟨64448, by rfl⟩) R128897
theorem R937973 : Reach 937973 := rs (se 5 (by rfl) ⟨43967, by rfl⟩) R87935
theorem R249911 : Reach 249911 := rs (se 1 (by rfl) ⟨187433, by rfl⟩) R374867
theorem R152441 : Reach 152441 := rs (se 2 (by rfl) ⟨57165, by rfl⟩) R114331
theorem R218375 : Reach 218375 := rs (se 1 (by rfl) ⟨163781, by rfl⟩) R327563
theorem R120143 : Reach 120143 := rs (se 1 (by rfl) ⟨90107, by rfl⟩) R180215
theorem R54751 : Reach 54751 := rs (se 1 (by rfl) ⟨41063, by rfl⟩) R82127
theorem R284251 : Reach 284251 := rs (se 1 (by rfl) ⟨213188, by rfl⟩) R426377
theorem R350057 : Reach 350057 := rs (se 2 (by rfl) ⟨131271, by rfl⟩) R262543
theorem R382967 : Reach 382967 := rs (se 1 (by rfl) ⟨287225, by rfl⟩) R574451
theorem R55343 : Reach 55343 := rs (se 1 (by rfl) ⟨41507, by rfl⟩) R83015
theorem R252355 : Reach 252355 := rs (se 1 (by rfl) ⟨189266, by rfl⟩) R378533
theorem R253265 : Reach 253265 := rs (se 2 (by rfl) ⟨94974, by rfl⟩) R189949
theorem R155087 : Reach 155087 := rs (se 1 (by rfl) ⟨116315, by rfl⟩) R232631
theorem R58087 : Reach 58087 := rs (se 1 (by rfl) ⟨43565, by rfl⟩) R87131
theorem R222049 : Reach 222049 := rs (se 2 (by rfl) ⟨83268, by rfl⟩) R166537
theorem R222203 : Reach 222203 := rs (se 1 (by rfl) ⟨166652, by rfl⟩) R333305
theorem R222263 : Reach 222263 := rs (se 1 (by rfl) ⟨166697, by rfl⟩) R333395
theorem R321079 : Reach 321079 := rs (se 1 (by rfl) ⟨240809, by rfl⟩) R481619
theorem R124591 : Reach 124591 := rs (se 1 (by rfl) ⟨93443, by rfl⟩) R186887
theorem R124841 : Reach 124841 := rs (se 2 (by rfl) ⟨46815, by rfl⟩) R93631
theorem R223721 : Reach 223721 := rs (se 2 (by rfl) ⟨83895, by rfl⟩) R167791
theorem R158489 : Reach 158489 := rs (se 2 (by rfl) ⟨59433, by rfl⟩) R118867
theorem R126107 : Reach 126107 := rs (se 1 (by rfl) ⟨94580, by rfl⟩) R189161
theorem R126461 : Reach 126461 := rs (se 3 (by rfl) ⟨23711, by rfl⟩) R47423
theorem R6025427 : Reach 6025427 := rs (se 1 (by rfl) ⟨4519070, by rfl⟩) R9038141
theorem R192851 : Reach 192851 := rs (se 1 (by rfl) ⟨144638, by rfl⟩) R289277
theorem R193859 : Reach 193859 := rs (se 1 (by rfl) ⟨145394, by rfl⟩) R290789
theorem R390653 : Reach 390653 := rs (se 3 (by rfl) ⟨73247, by rfl⟩) R146495
theorem R128575 : Reach 128575 := rs (se 1 (by rfl) ⟨96431, by rfl⟩) R192863
theorem R63355 : Reach 63355 := rs (se 1 (by rfl) ⟨47516, by rfl⟩) R95033
theorem R1341521 : Reach 1341521 := rs (se 2 (by rfl) ⟨503070, by rfl⟩) R1006141
theorem R391553 : Reach 391553 := rs (se 2 (by rfl) ⟨146832, by rfl⟩) R293665
theorem R97307 : Reach 97307 := rs (se 1 (by rfl) ⟨72980, by rfl⟩) R145961
theorem R850985 : Reach 850985 := rs (se 2 (by rfl) ⟨319119, by rfl⟩) R638239
theorem R97343 : Reach 97343 := rs (se 1 (by rfl) ⟨73007, by rfl⟩) R146015
theorem R261575 : Reach 261575 := rs (se 1 (by rfl) ⟨196181, by rfl⟩) R392363
theorem R98297 : Reach 98297 := rs (se 2 (by rfl) ⟨36861, by rfl⟩) R73723
theorem R65705 : Reach 65705 := rs (se 2 (by rfl) ⟨24639, by rfl⟩) R49279
theorem R65711 : Reach 65711 := rs (se 1 (by rfl) ⟨49283, by rfl⟩) R98567
theorem R164047 : Reach 164047 := rs (se 1 (by rfl) ⟨123035, by rfl⟩) R246071
theorem R65915 : Reach 65915 := rs (se 1 (by rfl) ⟨49436, by rfl⟩) R98873
theorem R66023 : Reach 66023 := rs (se 1 (by rfl) ⟨49517, by rfl⟩) R99035
theorem R524879 : Reach 524879 := rs (se 1 (by rfl) ⟨393659, by rfl⟩) R787319
theorem R99071 : Reach 99071 := rs (se 1 (by rfl) ⟨74303, by rfl⟩) R148607
theorem R66395 : Reach 66395 := rs (se 1 (by rfl) ⟨49796, by rfl⟩) R99593
theorem R296065 : Reach 296065 := rs (se 2 (by rfl) ⟨111024, by rfl⟩) R222049
theorem R66857 : Reach 66857 := rs (se 2 (by rfl) ⟨25071, by rfl⟩) R50143
theorem R66983 : Reach 66983 := rs (se 1 (by rfl) ⟨50237, by rfl⟩) R100475
theorem R67055 : Reach 67055 := rs (se 1 (by rfl) ⟨50291, by rfl⟩) R100583
theorem R67451 : Reach 67451 := rs (se 1 (by rfl) ⟨50588, by rfl⟩) R101177
theorem R428105 : Reach 428105 := rs (se 2 (by rfl) ⟨160539, by rfl⟩) R321079
theorem R166121 : Reach 166121 := rs (se 2 (by rfl) ⟨62295, by rfl⟩) R124591
theorem R100691 : Reach 100691 := rs (se 1 (by rfl) ⟨75518, by rfl⟩) R151037
theorem R264545 : Reach 264545 := rs (se 2 (by rfl) ⟨99204, by rfl⟩) R198409
theorem R67943 : Reach 67943 := rs (se 1 (by rfl) ⟨50957, by rfl⟩) R101915
theorem R100799 : Reach 100799 := rs (se 1 (by rfl) ⟨75599, by rfl⟩) R151199
theorem R68207 : Reach 68207 := rs (se 1 (by rfl) ⟨51155, by rfl⟩) R102311
theorem R592541 : Reach 592541 := rs (se 3 (by rfl) ⟨111101, by rfl⟩) R222203
theorem R625315 : Reach 625315 := rs (se 1 (by rfl) ⟨468986, by rfl⟩) R937973
theorem R166607 : Reach 166607 := rs (se 1 (by rfl) ⟨124955, by rfl⟩) R249911
theorem R68315 : Reach 68315 := rs (se 1 (by rfl) ⟨51236, by rfl⟩) R102473
theorem R134045 : Reach 134045 := rs (se 3 (by rfl) ⟨25133, by rfl⟩) R50267
theorem R68735 : Reach 68735 := rs (se 1 (by rfl) ⟨51551, by rfl⟩) R103103
theorem R101627 : Reach 101627 := rs (se 1 (by rfl) ⟨76220, by rfl⟩) R152441
theorem R659177 : Reach 659177 := rs (se 2 (by rfl) ⟨247191, by rfl⟩) R494383
theorem R69455 : Reach 69455 := rs (se 1 (by rfl) ⟨52091, by rfl⟩) R104183
theorem R233371 : Reach 233371 := rs (se 1 (by rfl) ⟨175028, by rfl⟩) R350057
theorem R69743 : Reach 69743 := rs (se 1 (by rfl) ⟨52307, by rfl⟩) R104615
theorem R69935 : Reach 69935 := rs (se 1 (by rfl) ⟨52451, by rfl⟩) R104903
theorem R69967 : Reach 69967 := rs (se 1 (by rfl) ⟨52475, by rfl⟩) R104951
theorem R70427 : Reach 70427 := rs (se 1 (by rfl) ⟨52820, by rfl⟩) R105641
theorem R103391 : Reach 103391 := rs (se 1 (by rfl) ⟨77543, by rfl⟩) R155087
theorem R70655 : Reach 70655 := rs (se 1 (by rfl) ⟨52991, by rfl⟩) R105983
theorem R332909 : Reach 332909 := rs (se 3 (by rfl) ⟨62420, by rfl⟩) R124841
theorem R497177 : Reach 497177 := rs (se 2 (by rfl) ⟨186441, by rfl⟩) R372883
theorem R136819 : Reach 136819 := rs (se 1 (by rfl) ⟨102614, by rfl⟩) R205229
theorem R105659 : Reach 105659 := rs (se 1 (by rfl) ⟨79244, by rfl⟩) R158489
theorem R72967 : Reach 72967 := rs (se 1 (by rfl) ⟨54725, by rfl⟩) R109451
theorem R73001 : Reach 73001 := rs (se 2 (by rfl) ⟨27375, by rfl⟩) R54751
theorem R171433 : Reach 171433 := rs (se 2 (by rfl) ⟨64287, by rfl⟩) R128575
theorem R532169 : Reach 532169 := rs (se 2 (by rfl) ⟨199563, by rfl⟩) R399127
theorem R4530167 : Reach 4530167 := rs (se 1 (by rfl) ⟨3397625, by rfl⟩) R6795251
theorem R336473 : Reach 336473 := rs (se 2 (by rfl) ⟨126177, by rfl⟩) R252355
theorem R140231 : Reach 140231 := rs (se 1 (by rfl) ⟨105173, by rfl⟩) R210347
theorem R238889 : Reach 238889 := rs (se 2 (by rfl) ⟨89583, by rfl⟩) R179167
theorem R894347 : Reach 894347 := rs (se 1 (by rfl) ⟨670760, by rfl⟩) R1341521
theorem R567323 : Reach 567323 := rs (se 1 (by rfl) ⟨425492, by rfl⟩) R850985
theorem R174383 : Reach 174383 := rs (se 1 (by rfl) ⟨130787, by rfl⟩) R261575
theorem R928279 : Reach 928279 := rs (se 1 (by rfl) ⟨696209, by rfl⟩) R1392419
theorem R175081 : Reach 175081 := rs (se 2 (by rfl) ⟨65655, by rfl⟩) R131311
theorem R142361 : Reach 142361 := rs (se 2 (by rfl) ⟨53385, by rfl⟩) R106771
theorem R44059 : Reach 44059 := rs (se 1 (by rfl) ⟨33044, by rfl⟩) R66089
theorem R44199 : Reach 44199 := rs (se 1 (by rfl) ⟨33149, by rfl⟩) R66299
theorem R44391 : Reach 44391 := rs (se 1 (by rfl) ⟨33293, by rfl⟩) R66587
theorem R44527 : Reach 44527 := rs (se 1 (by rfl) ⟨33395, by rfl⟩) R66791
theorem R634463 : Reach 634463 := rs (se 1 (by rfl) ⟨475847, by rfl⟩) R951695
theorem R77449 : Reach 77449 := rs (se 2 (by rfl) ⟨29043, by rfl⟩) R58087
theorem R44775 : Reach 44775 := rs (se 1 (by rfl) ⟨33581, by rfl⟩) R67163
theorem R45087 : Reach 45087 := rs (se 1 (by rfl) ⟨33815, by rfl⟩) R67631
theorem R77915 : Reach 77915 := rs (se 1 (by rfl) ⟨58436, by rfl⟩) R116873
theorem R536863 : Reach 536863 := rs (se 1 (by rfl) ⟨402647, by rfl⟩) R805295
theorem R78151 : Reach 78151 := rs (se 1 (by rfl) ⟨58613, by rfl⟩) R117227
theorem R45551 : Reach 45551 := rs (se 1 (by rfl) ⟨34163, by rfl⟩) R68327
theorem R45567 : Reach 45567 := rs (se 1 (by rfl) ⟨34175, by rfl⟩) R68351
theorem R373409 : Reach 373409 := rs (se 2 (by rfl) ⟨140028, by rfl⟩) R280057
theorem R275399 : Reach 275399 := rs (se 1 (by rfl) ⟨206549, by rfl⟩) R413099
theorem R46107 : Reach 46107 := rs (se 1 (by rfl) ⟨34580, by rfl⟩) R69161
theorem R46271 : Reach 46271 := rs (se 1 (by rfl) ⟨34703, by rfl⟩) R69407
theorem R46383 : Reach 46383 := rs (se 1 (by rfl) ⟨34787, by rfl⟩) R69575
theorem R46543 : Reach 46543 := rs (se 1 (by rfl) ⟨34907, by rfl⟩) R69815
theorem R46591 : Reach 46591 := rs (se 1 (by rfl) ⟨34943, by rfl⟩) R69887
theorem R46875 : Reach 46875 := rs (se 1 (by rfl) ⟨35156, by rfl⟩) R70313
theorem R145583 : Reach 145583 := rs (se 1 (by rfl) ⟨109187, by rfl⟩) R218375
theorem R277613 : Reach 277613 := rs (se 3 (by rfl) ⟨52052, by rfl⟩) R104105
theorem R245413 : Reach 245413 := rs (se 4 (by rfl) ⟨23007, by rfl⟩) R46015
theorem R147581 : Reach 147581 := rs (se 3 (by rfl) ⟨27671, by rfl⟩) R55343
theorem R147689 : Reach 147689 := rs (se 2 (by rfl) ⟨55383, by rfl⟩) R110767
theorem R6603227 : Reach 6603227 := rs (se 1 (by rfl) ⟨4952420, by rfl⟩) R9904841
theorem R148175 : Reach 148175 := rs (se 1 (by rfl) ⟨111131, by rfl⟩) R222263
theorem R312605 : Reach 312605 := rs (se 3 (by rfl) ⟨58613, by rfl⟩) R117227
theorem R149147 : Reach 149147 := rs (se 1 (by rfl) ⟨111860, by rfl⟩) R223721
theorem R84071 : Reach 84071 := rs (se 1 (by rfl) ⟨63053, by rfl⟩) R126107
theorem R379001 : Reach 379001 := rs (se 2 (by rfl) ⟨142125, by rfl⟩) R284251
theorem R84307 : Reach 84307 := rs (se 1 (by rfl) ⟨63230, by rfl⟩) R126461
theorem R84473 : Reach 84473 := rs (se 2 (by rfl) ⟨31677, by rfl⟩) R63355
theorem R4016951 : Reach 4016951 := rs (se 1 (by rfl) ⟨3012713, by rfl⟩) R6025427
theorem R675373 : Reach 675373 := rs (se 3 (by rfl) ⟨126632, by rfl⟩) R253265
theorem R283945 : Reach 283945 := rs (se 2 (by rfl) ⟨106479, by rfl⟩) R212959
theorem R153143 : Reach 153143 := rs (se 1 (by rfl) ⟨114857, by rfl⟩) R229715
theorem R219419 : Reach 219419 := rs (se 1 (by rfl) ⟨164564, by rfl⟩) R329129
theorem R317753 : Reach 317753 := rs (se 2 (by rfl) ⟨119157, by rfl⟩) R238315
theorem R1137361 : Reach 1137361 := rs (se 2 (by rfl) ⟨426510, by rfl⟩) R853021
theorem R220409 : Reach 220409 := rs (se 2 (by rfl) ⟨82653, by rfl⟩) R165307
theorem R57287 : Reach 57287 := rs (se 1 (by rfl) ⟨42965, by rfl⟩) R85931
theorem R320381 : Reach 320381 := rs (se 3 (by rfl) ⟨60071, by rfl⟩) R120143
theorem R255311 : Reach 255311 := rs (se 1 (by rfl) ⟨191483, by rfl⟩) R382967
theorem R224207 : Reach 224207 := rs (se 1 (by rfl) ⟨168155, by rfl⟩) R336311
theorem R224531 : Reach 224531 := rs (se 1 (by rfl) ⟨168398, by rfl⟩) R336797
theorem R128567 : Reach 128567 := rs (se 1 (by rfl) ⟨96425, by rfl⟩) R192851
theorem R129239 : Reach 129239 := rs (se 1 (by rfl) ⟨96929, by rfl⟩) R193859
theorem R260435 : Reach 260435 := rs (se 1 (by rfl) ⟨195326, by rfl⟩) R390653
theorem R424415 : Reach 424415 := rs (se 1 (by rfl) ⟨318311, by rfl⟩) R636623
theorem R293503 : Reach 293503 := rs (se 1 (by rfl) ⟨220127, by rfl⟩) R440255
theorem R261035 : Reach 261035 := rs (se 1 (by rfl) ⟨195776, by rfl⟩) R391553
theorem R2030629 : Reach 2030629 := rs (se 4 (by rfl) ⟨190371, by rfl⟩) R380743
theorem R64871 : Reach 64871 := rs (se 1 (by rfl) ⟨48653, by rfl⟩) R97307
theorem R64895 : Reach 64895 := rs (se 1 (by rfl) ⟨48671, by rfl⟩) R97343
theorem R65129 : Reach 65129 := rs (se 2 (by rfl) ⟨24423, by rfl⟩) R48847
theorem R97919 : Reach 97919 := rs (se 1 (by rfl) ⟨73439, by rfl⟩) R146879
theorem R65513 : Reach 65513 := rs (se 2 (by rfl) ⟨24567, by rfl⟩) R49135
theorem R65531 : Reach 65531 := rs (se 1 (by rfl) ⟨49148, by rfl⟩) R98297
theorem R98387 : Reach 98387 := rs (se 1 (by rfl) ⟨73790, by rfl⟩) R147581
theorem R98459 : Reach 98459 := rs (se 1 (by rfl) ⟨73844, by rfl⟩) R147689
theorem R98783 : Reach 98783 := rs (se 1 (by rfl) ⟨74087, by rfl⟩) R148175
theorem R66047 : Reach 66047 := rs (se 1 (by rfl) ⟨49535, by rfl⟩) R99071
theorem R99431 : Reach 99431 := rs (se 1 (by rfl) ⟨74573, by rfl⟩) R149147
theorem R394753 : Reach 394753 := rs (se 2 (by rfl) ⟨148032, by rfl⟩) R296065
theorem R67127 : Reach 67127 := rs (se 1 (by rfl) ⟨50345, by rfl⟩) R100691
theorem R67199 : Reach 67199 := rs (se 1 (by rfl) ⟨50399, by rfl⟩) R100799
theorem R395027 : Reach 395027 := rs (se 1 (by rfl) ⟨296270, by rfl⟩) R592541
theorem R67751 : Reach 67751 := rs (se 1 (by rfl) ⟨50813, by rfl⟩) R101627
theorem R4950821 : Reach 4950821 := rs (se 4 (by rfl) ⟨464139, by rfl⟩) R928279
theorem R68927 : Reach 68927 := rs (se 1 (by rfl) ⟨51695, by rfl⟩) R103391
theorem R331451 : Reach 331451 := rs (se 1 (by rfl) ⟨248588, by rfl⟩) R497177
theorem R102095 : Reach 102095 := rs (se 1 (by rfl) ⟨76571, by rfl⟩) R153143
theorem R233441 : Reach 233441 := rs (se 2 (by rfl) ⟨87540, by rfl⟩) R175081
theorem R70439 : Reach 70439 := rs (se 1 (by rfl) ⟨52829, by rfl⟩) R105659
theorem R103265 : Reach 103265 := rs (se 2 (by rfl) ⟨38724, by rfl⟩) R77449
theorem R3020111 : Reach 3020111 := rs (se 1 (by rfl) ⟨2265083, by rfl⟩) R4530167
theorem R104201 : Reach 104201 := rs (se 2 (by rfl) ⟨39075, by rfl⟩) R78151
theorem R170207 : Reach 170207 := rs (se 1 (by rfl) ⟨127655, by rfl⟩) R255311
theorem R596231 : Reach 596231 := rs (se 1 (by rfl) ⟨447173, by rfl⟩) R894347
theorem R1516481 : Reach 1516481 := rs (se 2 (by rfl) ⟨568680, by rfl⟩) R1137361
theorem R173623 : Reach 173623 := rs (se 1 (by rfl) ⟨130217, by rfl⟩) R260435
theorem R174023 : Reach 174023 := rs (se 1 (by rfl) ⟨130517, by rfl⟩) R261035
theorem R43247 : Reach 43247 := rs (se 1 (by rfl) ⟨32435, by rfl⟩) R64871
theorem R43263 : Reach 43263 := rs (se 1 (by rfl) ⟨32447, by rfl⟩) R64895
theorem R43419 : Reach 43419 := rs (se 1 (by rfl) ⟨32564, by rfl⟩) R65129
theorem R43675 : Reach 43675 := rs (se 1 (by rfl) ⟨32756, by rfl⟩) R65513
theorem R43687 : Reach 43687 := rs (se 1 (by rfl) ⟨32765, by rfl⟩) R65531
theorem R43803 : Reach 43803 := rs (se 1 (by rfl) ⟨32852, by rfl⟩) R65705
theorem R43807 : Reach 43807 := rs (se 1 (by rfl) ⟨32855, by rfl⟩) R65711
theorem R43943 : Reach 43943 := rs (se 1 (by rfl) ⟨32957, by rfl⟩) R65915
theorem R4402151 : Reach 4402151 := rs (se 1 (by rfl) ⟨3301613, by rfl⟩) R6603227
theorem R44015 : Reach 44015 := rs (se 1 (by rfl) ⟨33011, by rfl⟩) R66023
theorem R44263 : Reach 44263 := rs (se 1 (by rfl) ⟨33197, by rfl⟩) R66395
theorem R208403 : Reach 208403 := rs (se 1 (by rfl) ⟨156302, by rfl⟩) R312605
theorem R44571 : Reach 44571 := rs (se 1 (by rfl) ⟨33428, by rfl⟩) R66857
theorem R44655 : Reach 44655 := rs (se 1 (by rfl) ⟨33491, by rfl⟩) R66983
theorem R44703 : Reach 44703 := rs (se 1 (by rfl) ⟨33527, by rfl⟩) R67055
theorem R44967 : Reach 44967 := rs (se 1 (by rfl) ⟨33725, by rfl⟩) R67451
theorem R110747 : Reach 110747 := rs (se 1 (by rfl) ⟨83060, by rfl⟩) R166121
theorem R176363 : Reach 176363 := rs (se 1 (by rfl) ⟨132272, by rfl⟩) R264545
theorem R45295 : Reach 45295 := rs (se 1 (by rfl) ⟨33971, by rfl⟩) R67943
theorem R45471 : Reach 45471 := rs (se 1 (by rfl) ⟨34103, by rfl⟩) R68207
theorem R373157 : Reach 373157 := rs (se 4 (by rfl) ⟨34983, by rfl⟩) R69967
theorem R111071 : Reach 111071 := rs (se 1 (by rfl) ⟨83303, by rfl⟩) R166607
theorem R45543 : Reach 45543 := rs (se 1 (by rfl) ⟨34157, by rfl⟩) R68315
theorem R45823 : Reach 45823 := rs (se 1 (by rfl) ⟨34367, by rfl⟩) R68735
theorem R439451 : Reach 439451 := rs (se 1 (by rfl) ⟨329588, by rfl⟩) R659177
theorem R46303 : Reach 46303 := rs (se 1 (by rfl) ⟨34727, by rfl⟩) R69455
theorem R46495 : Reach 46495 := rs (se 1 (by rfl) ⟨34871, by rfl⟩) R69743
theorem R46623 : Reach 46623 := rs (se 1 (by rfl) ⟨34967, by rfl⟩) R69935
theorem R112409 : Reach 112409 := rs (se 2 (by rfl) ⟨42153, by rfl⟩) R84307
theorem R46951 : Reach 46951 := rs (se 1 (by rfl) ⟨35213, by rfl⟩) R70427
theorem R47103 : Reach 47103 := rs (se 1 (by rfl) ⟨35327, by rfl⟩) R70655
theorem R833753 : Reach 833753 := rs (se 2 (by rfl) ⟨312657, by rfl⟩) R625315
theorem R146279 : Reach 146279 := rs (se 1 (by rfl) ⟨109709, by rfl⟩) R219419
theorem R211835 : Reach 211835 := rs (se 1 (by rfl) ⟨158876, by rfl⟩) R317753
theorem R900497 : Reach 900497 := rs (se 2 (by rfl) ⟨337686, by rfl⟩) R675373
theorem R146939 : Reach 146939 := rs (se 1 (by rfl) ⟨110204, by rfl⟩) R220409
theorem R48667 : Reach 48667 := rs (se 1 (by rfl) ⟨36500, by rfl⟩) R73001
theorem R213587 : Reach 213587 := rs (se 1 (by rfl) ⟨160190, by rfl⟩) R320381
theorem R378215 : Reach 378215 := rs (se 1 (by rfl) ⟨283661, by rfl⟩) R567323
theorem R116255 : Reach 116255 := rs (se 1 (by rfl) ⟨87191, by rfl⟩) R174383
theorem R378593 : Reach 378593 := rs (se 2 (by rfl) ⟨141972, by rfl⟩) R283945
theorem R149471 : Reach 149471 := rs (se 1 (by rfl) ⟨112103, by rfl⟩) R224207
theorem R182425 : Reach 182425 := rs (se 2 (by rfl) ⟨68409, by rfl⟩) R136819
theorem R149687 : Reach 149687 := rs (se 1 (by rfl) ⟨112265, by rfl⟩) R224531
theorem R51943 : Reach 51943 := rs (se 1 (by rfl) ⟨38957, by rfl⟩) R77915
theorem R248939 : Reach 248939 := rs (se 1 (by rfl) ⟨186704, by rfl⟩) R373409
theorem R183599 : Reach 183599 := rs (se 1 (by rfl) ⟨137699, by rfl⟩) R275399
theorem R85711 : Reach 85711 := rs (se 1 (by rfl) ⟨64283, by rfl⟩) R128567
theorem R2707505 : Reach 2707505 := rs (se 2 (by rfl) ⟨1015314, by rfl⟩) R2030629
theorem R86159 : Reach 86159 := rs (se 1 (by rfl) ⟨64619, by rfl⟩) R129239
theorem R282943 : Reach 282943 := rs (se 1 (by rfl) ⟨212207, by rfl⟩) R424415
theorem R185075 : Reach 185075 := rs (se 1 (by rfl) ⟨138806, by rfl⟩) R277613
theorem R152765 : Reach 152765 := rs (se 3 (by rfl) ⟨28643, by rfl⟩) R57287
theorem R218729 : Reach 218729 := rs (se 2 (by rfl) ⟨82023, by rfl⟩) R164047
theorem R349919 : Reach 349919 := rs (se 1 (by rfl) ⟨262439, by rfl⟩) R524879
theorem R56047 : Reach 56047 := rs (se 1 (by rfl) ⟨42035, by rfl⟩) R84071
theorem R252667 : Reach 252667 := rs (se 1 (by rfl) ⟨189500, by rfl⟩) R379001
theorem R56315 : Reach 56315 := rs (se 1 (by rfl) ⟨42236, by rfl⟩) R84473
theorem R2677967 : Reach 2677967 := rs (se 1 (by rfl) ⟨2008475, by rfl⟩) R4016951
theorem R89363 : Reach 89363 := rs (se 1 (by rfl) ⟨67022, by rfl⟩) R134045
theorem R221939 : Reach 221939 := rs (se 1 (by rfl) ⟨166454, by rfl⟩) R332909
theorem R58745 : Reach 58745 := rs (se 2 (by rfl) ⟨22029, by rfl⟩) R44059
theorem R354779 : Reach 354779 := rs (se 1 (by rfl) ⟨266084, by rfl⟩) R532169
theorem R1141613 : Reach 1141613 := rs (se 3 (by rfl) ⟨214052, by rfl⟩) R428105
theorem R715817 : Reach 715817 := rs (se 2 (by rfl) ⟨268431, by rfl⟩) R536863
theorem R224315 : Reach 224315 := rs (se 1 (by rfl) ⟨168236, by rfl⟩) R336473
theorem R93487 : Reach 93487 := rs (se 1 (by rfl) ⟨70115, by rfl⟩) R140231
theorem R159259 : Reach 159259 := rs (se 1 (by rfl) ⟨119444, by rfl⟩) R238889
theorem R94907 : Reach 94907 := rs (se 1 (by rfl) ⟨71180, by rfl⟩) R142361
theorem R422975 : Reach 422975 := rs (se 1 (by rfl) ⟨317231, by rfl⟩) R634463
theorem R391337 : Reach 391337 := rs (se 2 (by rfl) ⟨146751, by rfl⟩) R293503
theorem R1308869 : Reach 1308869 := rs (se 4 (by rfl) ⟨122706, by rfl⟩) R245413
theorem R97055 : Reach 97055 := rs (se 1 (by rfl) ⟨72791, by rfl⟩) R145583
theorem R97289 : Reach 97289 := rs (se 2 (by rfl) ⟨36483, by rfl⟩) R72967
theorem R228577 : Reach 228577 := rs (se 2 (by rfl) ⟨85716, by rfl⟩) R171433
theorem R1244645 : Reach 1244645 := rs (se 4 (by rfl) ⟨116685, by rfl⟩) R233371
theorem R65279 : Reach 65279 := rs (se 1 (by rfl) ⟨48959, by rfl⟩) R97919
theorem R65591 : Reach 65591 := rs (se 1 (by rfl) ⟨49193, by rfl⟩) R98387
theorem R65639 : Reach 65639 := rs (se 1 (by rfl) ⟨49229, by rfl⟩) R98459
theorem R65855 : Reach 65855 := rs (se 1 (by rfl) ⟨49391, by rfl⟩) R98783
theorem R66287 : Reach 66287 := rs (se 1 (by rfl) ⟨49715, by rfl⟩) R99431
theorem R263351 : Reach 263351 := rs (se 1 (by rfl) ⟨197513, by rfl⟩) R395027
theorem R99647 : Reach 99647 := rs (se 1 (by rfl) ⟨74735, by rfl⟩) R149471
theorem R99791 : Reach 99791 := rs (se 1 (by rfl) ⟨74843, by rfl⟩) R149687
theorem R526337 : Reach 526337 := rs (se 2 (by rfl) ⟨197376, by rfl⟩) R394753
theorem R165959 : Reach 165959 := rs (se 1 (by rfl) ⟨124469, by rfl⟩) R248939
theorem R231497 : Reach 231497 := rs (se 2 (by rfl) ⟨86811, by rfl⟩) R173623
theorem R68063 : Reach 68063 := rs (se 1 (by rfl) ⟨51047, by rfl⟩) R102095
theorem R1805003 : Reach 1805003 := rs (se 1 (by rfl) ⟨1353752, by rfl⟩) R2707505
theorem R68843 : Reach 68843 := rs (se 1 (by rfl) ⟨51632, by rfl⟩) R103265
theorem R101843 : Reach 101843 := rs (se 1 (by rfl) ⟨76382, by rfl⟩) R152765
theorem R69257 : Reach 69257 := rs (se 2 (by rfl) ⟨25971, by rfl⟩) R51943
theorem R233279 : Reach 233279 := rs (se 1 (by rfl) ⟨174959, by rfl⟩) R349919
theorem R69467 : Reach 69467 := rs (se 1 (by rfl) ⟨52100, by rfl⟩) R104201
theorem R397487 : Reach 397487 := rs (se 1 (by rfl) ⟨298115, by rfl⟩) R596231
theorem R236519 : Reach 236519 := rs (se 1 (by rfl) ⟨177389, by rfl⟩) R354779
theorem R761075 : Reach 761075 := rs (se 1 (by rfl) ⟨570806, by rfl⟩) R1141613
theorem R138935 : Reach 138935 := rs (se 1 (by rfl) ⟨104201, by rfl⟩) R208403
theorem R73831 : Reach 73831 := rs (se 1 (by rfl) ⟨55373, by rfl⟩) R110747
theorem R74047 : Reach 74047 := rs (se 1 (by rfl) ⟨55535, by rfl⟩) R111071
theorem R238301 : Reach 238301 := rs (se 3 (by rfl) ⟨44681, by rfl⟩) R89363
theorem R74729 : Reach 74729 := rs (se 2 (by rfl) ⟨28023, by rfl⟩) R56047
theorem R336889 : Reach 336889 := rs (se 2 (by rfl) ⟨126333, by rfl⟩) R252667
theorem R74939 : Reach 74939 := rs (se 1 (by rfl) ⟨56204, by rfl⟩) R112409
theorem R304769 : Reach 304769 := rs (se 2 (by rfl) ⟨114288, by rfl⟩) R228577
theorem R141223 : Reach 141223 := rs (se 1 (by rfl) ⟨105917, by rfl⟩) R211835
theorem R600331 : Reach 600331 := rs (se 1 (by rfl) ⟨450248, by rfl⟩) R900497
theorem R829763 : Reach 829763 := rs (se 1 (by rfl) ⟨622322, by rfl⟩) R1244645
theorem R43519 : Reach 43519 := rs (se 1 (by rfl) ⟨32639, by rfl⟩) R65279
theorem R44031 : Reach 44031 := rs (se 1 (by rfl) ⟨33023, by rfl⟩) R66047
theorem R142391 : Reach 142391 := rs (se 1 (by rfl) ⟨106793, by rfl⟩) R213587
theorem R77503 : Reach 77503 := rs (se 1 (by rfl) ⟨58127, by rfl⟩) R116255
theorem R44751 : Reach 44751 := rs (se 1 (by rfl) ⟨33563, by rfl⟩) R67127
theorem R44799 : Reach 44799 := rs (se 1 (by rfl) ⟨33599, by rfl⟩) R67199
theorem R45167 : Reach 45167 := rs (se 1 (by rfl) ⟨33875, by rfl⟩) R67751
theorem R45951 : Reach 45951 := rs (se 1 (by rfl) ⟨34463, by rfl⟩) R68927
theorem R243233 : Reach 243233 := rs (se 2 (by rfl) ⟨91212, by rfl⟩) R182425
theorem R46959 : Reach 46959 := rs (se 1 (by rfl) ⟨35219, by rfl⟩) R70439
theorem R2013407 : Reach 2013407 := rs (se 1 (by rfl) ⟨1510055, by rfl⟩) R3020111
theorem R145819 : Reach 145819 := rs (se 1 (by rfl) ⟨109364, by rfl⟩) R218729
theorem R113471 : Reach 113471 := rs (se 1 (by rfl) ⟨85103, by rfl⟩) R170207
theorem R212345 : Reach 212345 := rs (se 2 (by rfl) ⟨79629, by rfl⟩) R159259
theorem R1785311 : Reach 1785311 := rs (se 1 (by rfl) ⟨1338983, by rfl⟩) R2677967
theorem R114281 : Reach 114281 := rs (se 2 (by rfl) ⟨42855, by rfl⟩) R85711
theorem R377257 : Reach 377257 := rs (se 2 (by rfl) ⟨141471, by rfl⟩) R282943
theorem R147959 : Reach 147959 := rs (se 1 (by rfl) ⟨110969, by rfl⟩) R221939
theorem R116015 : Reach 116015 := rs (se 1 (by rfl) ⟨87011, by rfl⟩) R174023
theorem R2934767 : Reach 2934767 := rs (se 1 (by rfl) ⟨2201075, by rfl⟩) R4402151
theorem R477211 : Reach 477211 := rs (se 1 (by rfl) ⟨357908, by rfl⟩) R715817
theorem R149543 : Reach 149543 := rs (se 1 (by rfl) ⟨112157, by rfl⟩) R224315
theorem R150173 : Reach 150173 := rs (se 3 (by rfl) ⟨28157, by rfl⟩) R56315
theorem R117575 : Reach 117575 := rs (se 1 (by rfl) ⟨88181, by rfl⟩) R176363
theorem R248771 : Reach 248771 := rs (se 1 (by rfl) ⟨186578, by rfl⟩) R373157
theorem R281983 : Reach 281983 := rs (se 1 (by rfl) ⟨211487, by rfl⟩) R422975
theorem R872579 : Reach 872579 := rs (se 1 (by rfl) ⟨654434, by rfl⟩) R1308869
theorem R252143 : Reach 252143 := rs (se 1 (by rfl) ⟨189107, by rfl⟩) R378215
theorem R252395 : Reach 252395 := rs (se 1 (by rfl) ⟨189296, by rfl⟩) R378593
theorem R253085 : Reach 253085 := rs (se 3 (by rfl) ⟨47453, by rfl⟩) R94907
theorem R122399 : Reach 122399 := rs (se 1 (by rfl) ⟨91799, by rfl⟩) R183599
theorem R220967 : Reach 220967 := rs (se 1 (by rfl) ⟨165725, by rfl⟩) R331451
theorem R155627 : Reach 155627 := rs (se 1 (by rfl) ⟨116720, by rfl⟩) R233441
theorem R57439 : Reach 57439 := rs (se 1 (by rfl) ⟨43079, by rfl⟩) R86159
theorem R123383 : Reach 123383 := rs (se 1 (by rfl) ⟨92537, by rfl⟩) R185075
theorem R58249 : Reach 58249 := rs (se 2 (by rfl) ⟨21843, by rfl⟩) R43687
theorem R156653 : Reach 156653 := rs (se 3 (by rfl) ⟨29372, by rfl⟩) R58745
theorem R124649 : Reach 124649 := rs (se 2 (by rfl) ⟨46743, by rfl⟩) R93487
theorem R1010987 : Reach 1010987 := rs (se 1 (by rfl) ⟨758240, by rfl⟩) R1516481
theorem R716789 : Reach 716789 := rs (se 5 (by rfl) ⟨33599, by rfl⟩) R67199
theorem R13202189 : Reach 13202189 := rs (se 3 (by rfl) ⟨2475410, by rfl⟩) R4950821
theorem R292967 : Reach 292967 := rs (se 1 (by rfl) ⟨219725, by rfl⟩) R439451
theorem R391837 : Reach 391837 := rs (se 3 (by rfl) ⟨73469, by rfl⟩) R146939
theorem R260891 : Reach 260891 := rs (se 1 (by rfl) ⟨195668, by rfl⟩) R391337
theorem R555835 : Reach 555835 := rs (se 1 (by rfl) ⟨416876, by rfl⟩) R833753
theorem R64703 : Reach 64703 := rs (se 1 (by rfl) ⟨48527, by rfl⟩) R97055
theorem R97519 : Reach 97519 := rs (se 1 (by rfl) ⟨73139, by rfl⟩) R146279
theorem R64859 : Reach 64859 := rs (se 1 (by rfl) ⟨48644, by rfl⟩) R97289
theorem R64889 : Reach 64889 := rs (se 2 (by rfl) ⟨24333, by rfl⟩) R48667
theorem R98441 : Reach 98441 := rs (se 2 (by rfl) ⟨36915, by rfl⟩) R73831
theorem R98639 : Reach 98639 := rs (se 1 (by rfl) ⟨73979, by rfl⟩) R147959
theorem R2326877 : Reach 2326877 := rs (se 3 (by rfl) ⟨436289, by rfl⟩) R872579
theorem R98729 : Reach 98729 := rs (se 2 (by rfl) ⟨37023, by rfl⟩) R74047
theorem R66431 : Reach 66431 := rs (se 1 (by rfl) ⟨49823, by rfl⟩) R99647
theorem R66527 : Reach 66527 := rs (se 1 (by rfl) ⟨49895, by rfl⟩) R99791
theorem R329021 : Reach 329021 := rs (se 3 (by rfl) ⟨61691, by rfl⟩) R123383
theorem R99695 : Reach 99695 := rs (se 1 (by rfl) ⟨74771, by rfl⟩) R149543
theorem R100115 : Reach 100115 := rs (se 1 (by rfl) ⟨75086, by rfl⟩) R150173
theorem R165847 : Reach 165847 := rs (se 1 (by rfl) ⟨124385, by rfl⟩) R248771
theorem R67895 : Reach 67895 := rs (se 1 (by rfl) ⟨50921, by rfl⟩) R101843
theorem R264991 : Reach 264991 := rs (se 1 (by rfl) ⟨198743, by rfl⟩) R397487
theorem R199837 : Reach 199837 := rs (se 3 (by rfl) ⟨37469, by rfl⟩) R74939
theorem R168095 : Reach 168095 := rs (se 1 (by rfl) ⟨126071, by rfl⟩) R252143
theorem R168263 : Reach 168263 := rs (se 1 (by rfl) ⟨126197, by rfl⟩) R252395
theorem R103337 : Reach 103337 := rs (se 2 (by rfl) ⟨38751, by rfl⟩) R77503
theorem R103751 : Reach 103751 := rs (se 1 (by rfl) ⟨77813, by rfl⟩) R155627
theorem R104435 : Reach 104435 := rs (se 1 (by rfl) ⟨78326, by rfl⟩) R156653
theorem R370493 : Reach 370493 := rs (se 3 (by rfl) ⟨69467, by rfl⟩) R138935
theorem R173927 : Reach 173927 := rs (se 1 (by rfl) ⟨130445, by rfl⟩) R260891
theorem R75647 : Reach 75647 := rs (se 1 (by rfl) ⟨56735, by rfl⟩) R113471
theorem R43135 : Reach 43135 := rs (se 1 (by rfl) ⟨32351, by rfl⟩) R64703
theorem R43239 : Reach 43239 := rs (se 1 (by rfl) ⟨32429, by rfl⟩) R64859
theorem R43259 : Reach 43259 := rs (se 1 (by rfl) ⟨32444, by rfl⟩) R64889
theorem R141563 : Reach 141563 := rs (se 1 (by rfl) ⟨106172, by rfl⟩) R212345
theorem R1190207 : Reach 1190207 := rs (se 1 (by rfl) ⟨892655, by rfl⟩) R1785311
theorem R76187 : Reach 76187 := rs (se 1 (by rfl) ⟨57140, by rfl⟩) R114281
theorem R1911437 : Reach 1911437 := rs (se 3 (by rfl) ⟨358394, by rfl⟩) R716789
theorem R43727 : Reach 43727 := rs (se 1 (by rfl) ⟨32795, by rfl⟩) R65591
theorem R43759 : Reach 43759 := rs (se 1 (by rfl) ⟨32819, by rfl⟩) R65639
theorem R76585 : Reach 76585 := rs (se 2 (by rfl) ⟨28719, by rfl⟩) R57439
theorem R43903 : Reach 43903 := rs (se 1 (by rfl) ⟨32927, by rfl⟩) R65855
theorem R44191 : Reach 44191 := rs (se 1 (by rfl) ⟨33143, by rfl⟩) R66287
theorem R503009 : Reach 503009 := rs (se 2 (by rfl) ⟨188628, by rfl⟩) R377257
theorem R175567 : Reach 175567 := rs (se 1 (by rfl) ⟨131675, by rfl⟩) R263351
theorem R77665 : Reach 77665 := rs (se 2 (by rfl) ⟨29124, by rfl⟩) R58249
theorem R110639 : Reach 110639 := rs (se 1 (by rfl) ⟨82979, by rfl⟩) R165959
theorem R45375 : Reach 45375 := rs (se 1 (by rfl) ⟨34031, by rfl⟩) R68063
theorem R78383 : Reach 78383 := rs (se 1 (by rfl) ⟨58787, by rfl⟩) R117575
theorem R45895 : Reach 45895 := rs (se 1 (by rfl) ⟨34421, by rfl⟩) R68843
theorem R46171 : Reach 46171 := rs (se 1 (by rfl) ⟨34628, by rfl⟩) R69257
theorem R46311 : Reach 46311 := rs (se 1 (by rfl) ⟨34733, by rfl⟩) R69467
theorem R636281 : Reach 636281 := rs (se 2 (by rfl) ⟨238605, by rfl⟩) R477211
theorem R800441 : Reach 800441 := rs (se 2 (by rfl) ⟨300165, by rfl⟩) R600331
theorem R375977 : Reach 375977 := rs (se 2 (by rfl) ⟨140991, by rfl⟩) R281983
theorem R507383 : Reach 507383 := rs (se 1 (by rfl) ⟨380537, by rfl⟩) R761075
theorem R81599 : Reach 81599 := rs (se 1 (by rfl) ⟨61199, by rfl⟩) R122399
theorem R147311 : Reach 147311 := rs (se 1 (by rfl) ⟨110483, by rfl⟩) R220967
theorem R49819 : Reach 49819 := rs (se 1 (by rfl) ⟨37364, by rfl⟩) R74729
theorem R83099 : Reach 83099 := rs (se 1 (by rfl) ⟨62324, by rfl⟩) R124649
theorem R673991 : Reach 673991 := rs (se 1 (by rfl) ⟨505493, by rfl⟩) R1010987
theorem R674893 : Reach 674893 := rs (se 3 (by rfl) ⟨126542, by rfl⟩) R253085
theorem R8801459 : Reach 8801459 := rs (se 1 (by rfl) ⟨6601094, by rfl⟩) R13202189
theorem R741113 : Reach 741113 := rs (se 2 (by rfl) ⟨277917, by rfl⟩) R555835
theorem R1956511 : Reach 1956511 := rs (se 1 (by rfl) ⟨1467383, by rfl⟩) R2934767
theorem R449185 : Reach 449185 := rs (se 2 (by rfl) ⟨168444, by rfl⟩) R336889
theorem R350891 : Reach 350891 := rs (se 1 (by rfl) ⟨263168, by rfl⟩) R526337
theorem R154331 : Reach 154331 := rs (se 1 (by rfl) ⟨115748, by rfl⟩) R231497
theorem R1203335 : Reach 1203335 := rs (se 1 (by rfl) ⟨902501, by rfl⟩) R1805003
theorem R777701 : Reach 777701 := rs (se 4 (by rfl) ⟨72909, by rfl⟩) R145819
theorem R155519 : Reach 155519 := rs (se 1 (by rfl) ⟨116639, by rfl⟩) R233279
theorem R188297 : Reach 188297 := rs (se 2 (by rfl) ⟨70611, by rfl⟩) R141223
theorem R1237493 : Reach 1237493 := rs (se 5 (by rfl) ⟨58007, by rfl⟩) R116015
theorem R812717 : Reach 812717 := rs (se 3 (by rfl) ⟨152384, by rfl⟩) R304769
theorem R157679 : Reach 157679 := rs (se 1 (by rfl) ⟨118259, by rfl⟩) R236519
theorem R158867 : Reach 158867 := rs (se 1 (by rfl) ⟨119150, by rfl⟩) R238301
theorem R553175 : Reach 553175 := rs (se 1 (by rfl) ⟨414881, by rfl⟩) R829763
theorem R94927 : Reach 94927 := rs (se 1 (by rfl) ⟨71195, by rfl⟩) R142391
theorem R522449 : Reach 522449 := rs (se 2 (by rfl) ⟨195918, by rfl⟩) R391837
theorem R162155 : Reach 162155 := rs (se 1 (by rfl) ⟨121616, by rfl⟩) R243233
theorem R195311 : Reach 195311 := rs (se 1 (by rfl) ⟨146483, by rfl⟩) R292967
theorem R1342271 : Reach 1342271 := rs (se 1 (by rfl) ⟨1006703, by rfl⟩) R2013407
theorem R130025 : Reach 130025 := rs (se 2 (by rfl) ⟨48759, by rfl⟩) R97519
theorem R65627 : Reach 65627 := rs (se 1 (by rfl) ⟨49220, by rfl⟩) R98441
theorem R65759 : Reach 65759 := rs (se 1 (by rfl) ⟨49319, by rfl⟩) R98639
theorem R65819 : Reach 65819 := rs (se 1 (by rfl) ⟨49364, by rfl⟩) R98729
theorem R66425 : Reach 66425 := rs (se 2 (by rfl) ⟨24909, by rfl⟩) R49819
theorem R66463 : Reach 66463 := rs (se 1 (by rfl) ⟨49847, by rfl⟩) R99695
theorem R66743 : Reach 66743 := rs (se 1 (by rfl) ⟨50057, by rfl⟩) R100115
theorem R5867639 : Reach 5867639 := rs (se 1 (by rfl) ⟨4400729, by rfl⟩) R8801459
theorem R494075 : Reach 494075 := rs (se 1 (by rfl) ⟨370556, by rfl⟩) R741113
theorem R68891 : Reach 68891 := rs (se 1 (by rfl) ⟨51668, by rfl⟩) R103337
theorem R69167 : Reach 69167 := rs (se 1 (by rfl) ⟨51875, by rfl⟩) R103751
theorem R102113 : Reach 102113 := rs (se 2 (by rfl) ⟨38292, by rfl⟩) R76585
theorem R69623 : Reach 69623 := rs (se 1 (by rfl) ⟨52217, by rfl⟩) R104435
theorem R266449 : Reach 266449 := rs (se 2 (by rfl) ⟨99918, by rfl⟩) R199837
theorem R233927 : Reach 233927 := rs (se 1 (by rfl) ⟨175445, by rfl⟩) R350891
theorem R102887 : Reach 102887 := rs (se 1 (by rfl) ⟨77165, by rfl⟩) R154331
theorem R234089 : Reach 234089 := rs (se 2 (by rfl) ⟨87783, by rfl⟩) R175567
theorem R103553 : Reach 103553 := rs (se 2 (by rfl) ⟨38832, by rfl⟩) R77665
theorem R103679 : Reach 103679 := rs (se 1 (by rfl) ⟨77759, by rfl⟩) R155519
theorem R824995 : Reach 824995 := rs (se 1 (by rfl) ⟨618746, by rfl⟩) R1237493
theorem R105119 : Reach 105119 := rs (se 1 (by rfl) ⟨78839, by rfl⟩) R157679
theorem R793471 : Reach 793471 := rs (se 1 (by rfl) ⟨595103, by rfl⟩) R1190207
theorem R105911 : Reach 105911 := rs (se 1 (by rfl) ⟨79433, by rfl⟩) R158867
theorem R335339 : Reach 335339 := rs (se 1 (by rfl) ⟨251504, by rfl⟩) R503009
theorem R3579389 : Reach 3579389 := rs (se 3 (by rfl) ⟨671135, by rfl⟩) R1342271
theorem R73759 : Reach 73759 := rs (se 1 (by rfl) ⟨55319, by rfl⟩) R110639
theorem R368783 : Reach 368783 := rs (se 1 (by rfl) ⟨276587, by rfl⟩) R553175
theorem R598913 : Reach 598913 := rs (se 2 (by rfl) ⟨224592, by rfl⟩) R449185
theorem R533627 : Reach 533627 := rs (se 1 (by rfl) ⟨400220, by rfl⟩) R800441
theorem R108103 : Reach 108103 := rs (se 1 (by rfl) ⟨81077, by rfl⟩) R162155
theorem R338255 : Reach 338255 := rs (se 1 (by rfl) ⟨253691, by rfl⟩) R507383
theorem R1551251 : Reach 1551251 := rs (se 1 (by rfl) ⟨1163438, by rfl⟩) R2326877
theorem R44287 : Reach 44287 := rs (se 1 (by rfl) ⟨33215, by rfl⟩) R66431
theorem R44351 : Reach 44351 := rs (se 1 (by rfl) ⟨33263, by rfl⟩) R66527
theorem R45263 : Reach 45263 := rs (se 1 (by rfl) ⟨33947, by rfl⟩) R67895
theorem R112063 : Reach 112063 := rs (se 1 (by rfl) ⟨84047, by rfl⟩) R168095
theorem R112175 : Reach 112175 := rs (se 1 (by rfl) ⟨84131, by rfl⟩) R168263
theorem R899857 : Reach 899857 := rs (se 2 (by rfl) ⟨337446, by rfl⟩) R674893
theorem R802223 : Reach 802223 := rs (se 1 (by rfl) ⟨601667, by rfl⟩) R1203335
theorem R541811 : Reach 541811 := rs (se 1 (by rfl) ⟨406358, by rfl⟩) R812717
theorem R246995 : Reach 246995 := rs (se 1 (by rfl) ⟨185246, by rfl⟩) R370493
theorem R115951 : Reach 115951 := rs (se 1 (by rfl) ⟨86963, by rfl⟩) R173927
theorem R50431 : Reach 50431 := rs (se 1 (by rfl) ⟨37823, by rfl⟩) R75647
theorem R50791 : Reach 50791 := rs (se 1 (by rfl) ⟨38093, by rfl⟩) R76187
theorem R870389 : Reach 870389 := rs (se 5 (by rfl) ⟨40799, by rfl⟩) R81599
theorem R52255 : Reach 52255 := rs (se 1 (by rfl) ⟨39191, by rfl⟩) R78383
theorem R2608681 : Reach 2608681 := rs (se 2 (by rfl) ⟨978255, by rfl⟩) R1956511
theorem R348299 : Reach 348299 := rs (se 1 (by rfl) ⟨261224, by rfl⟩) R522449
theorem R86683 : Reach 86683 := rs (se 1 (by rfl) ⟨65012, by rfl⟩) R130025
theorem R250651 : Reach 250651 := rs (se 1 (by rfl) ⟨187988, by rfl⟩) R375977
theorem R448253 : Reach 448253 := rs (se 3 (by rfl) ⟨84047, by rfl⟩) R168095
theorem R55399 : Reach 55399 := rs (se 1 (by rfl) ⟨41549, by rfl⟩) R83099
theorem R219347 : Reach 219347 := rs (se 1 (by rfl) ⟨164510, by rfl⟩) R329021
theorem R449327 : Reach 449327 := rs (se 1 (by rfl) ⟨336995, by rfl⟩) R673991
theorem R221129 : Reach 221129 := rs (se 2 (by rfl) ⟨82923, by rfl⟩) R165847
theorem R353321 : Reach 353321 := rs (se 2 (by rfl) ⟨132495, by rfl⟩) R264991
theorem R518467 : Reach 518467 := rs (se 1 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R125531 : Reach 125531 := rs (se 1 (by rfl) ⟨94148, by rfl⟩) R188297
theorem R126569 : Reach 126569 := rs (se 2 (by rfl) ⟨47463, by rfl⟩) R94927
theorem R94375 : Reach 94375 := rs (se 1 (by rfl) ⟨70781, by rfl⟩) R141563
theorem R1274291 : Reach 1274291 := rs (se 1 (by rfl) ⟨955718, by rfl⟩) R1911437
theorem R424187 : Reach 424187 := rs (se 1 (by rfl) ⟨318140, by rfl⟩) R636281
theorem R130207 : Reach 130207 := rs (se 1 (by rfl) ⟨97655, by rfl⟩) R195311
theorem R98207 : Reach 98207 := rs (se 1 (by rfl) ⟨73655, by rfl⟩) R147311
theorem R98345 : Reach 98345 := rs (se 2 (by rfl) ⟨36879, by rfl⟩) R73759
theorem R361207 : Reach 361207 := rs (se 1 (by rfl) ⟨270905, by rfl⟩) R541811
theorem R164663 : Reach 164663 := rs (se 1 (by rfl) ⟨123497, by rfl⟩) R246995
theorem R329383 : Reach 329383 := rs (se 1 (by rfl) ⟨247037, by rfl⟩) R494075
theorem R67241 : Reach 67241 := rs (se 2 (by rfl) ⟨25215, by rfl⟩) R50431
theorem R67721 : Reach 67721 := rs (se 2 (by rfl) ⟨25395, by rfl⟩) R50791
theorem R68075 : Reach 68075 := rs (se 1 (by rfl) ⟨51056, by rfl⟩) R102113
theorem R232199 : Reach 232199 := rs (se 1 (by rfl) ⟨174149, by rfl⟩) R348299
theorem R68591 : Reach 68591 := rs (se 1 (by rfl) ⟨51443, by rfl⟩) R102887
theorem R691289 : Reach 691289 := rs (se 2 (by rfl) ⟨259233, by rfl⟩) R518467
theorem R69035 : Reach 69035 := rs (se 1 (by rfl) ⟨51776, by rfl⟩) R103553
theorem R69119 : Reach 69119 := rs (se 1 (by rfl) ⟨51839, by rfl⟩) R103679
theorem R298835 : Reach 298835 := rs (se 1 (by rfl) ⟨224126, by rfl⟩) R448253
theorem R69673 : Reach 69673 := rs (se 2 (by rfl) ⟨26127, by rfl⟩) R52255
theorem R70079 : Reach 70079 := rs (se 1 (by rfl) ⟨52559, by rfl⟩) R105119
theorem R299551 : Reach 299551 := rs (se 1 (by rfl) ⟨224663, by rfl⟩) R449327
theorem R3478241 : Reach 3478241 := rs (se 2 (by rfl) ⟨1304340, by rfl⟩) R2608681
theorem R70607 : Reach 70607 := rs (se 1 (by rfl) ⟨52955, by rfl⟩) R105911
theorem R399275 : Reach 399275 := rs (se 1 (by rfl) ⟨299456, by rfl⟩) R598913
theorem R235547 : Reach 235547 := rs (se 1 (by rfl) ⟨176660, by rfl⟩) R353321
theorem R334201 : Reach 334201 := rs (se 2 (by rfl) ⟨125325, by rfl⟩) R250651
theorem R73865 : Reach 73865 := rs (se 2 (by rfl) ⟨27699, by rfl⟩) R55399
theorem R74783 : Reach 74783 := rs (se 1 (by rfl) ⟨56087, by rfl⟩) R112175
theorem R1057961 : Reach 1057961 := rs (se 2 (by rfl) ⟨396735, by rfl⟩) R793471
theorem R173609 : Reach 173609 := rs (se 2 (by rfl) ⟨65103, by rfl⟩) R130207
theorem R337517 : Reach 337517 := rs (se 3 (by rfl) ⟨63284, by rfl⟩) R126569
theorem R534815 : Reach 534815 := rs (se 1 (by rfl) ⟨401111, by rfl⟩) R802223
theorem R43751 : Reach 43751 := rs (se 1 (by rfl) ⟨32813, by rfl⟩) R65627
theorem R43839 : Reach 43839 := rs (se 1 (by rfl) ⟨32879, by rfl⟩) R65759
theorem R43879 : Reach 43879 := rs (se 1 (by rfl) ⟨32909, by rfl⟩) R65819
theorem R44283 : Reach 44283 := rs (se 1 (by rfl) ⟨33212, by rfl⟩) R66425
theorem R44495 : Reach 44495 := rs (se 1 (by rfl) ⟨33371, by rfl⟩) R66743
theorem R3911759 : Reach 3911759 := rs (se 1 (by rfl) ⟨2933819, by rfl⟩) R5867639
theorem R144137 : Reach 144137 := rs (se 2 (by rfl) ⟨54051, by rfl⟩) R108103
theorem R45927 : Reach 45927 := rs (se 1 (by rfl) ⟨34445, by rfl⟩) R68891
theorem R46111 : Reach 46111 := rs (se 1 (by rfl) ⟨34583, by rfl⟩) R69167
theorem R46415 : Reach 46415 := rs (se 1 (by rfl) ⟨34811, by rfl⟩) R69623
theorem R146231 : Reach 146231 := rs (se 1 (by rfl) ⟨109673, by rfl⟩) R219347
theorem R147419 : Reach 147419 := rs (se 1 (by rfl) ⟨110564, by rfl⟩) R221129
theorem R245855 : Reach 245855 := rs (se 1 (by rfl) ⟨184391, by rfl⟩) R368783
theorem R115577 : Reach 115577 := rs (se 2 (by rfl) ⟨43341, by rfl⟩) R86683
theorem R83687 : Reach 83687 := rs (se 1 (by rfl) ⟨62765, by rfl⟩) R125531
theorem R149417 : Reach 149417 := rs (se 2 (by rfl) ⟨56031, by rfl⟩) R112063
theorem R1034167 : Reach 1034167 := rs (se 1 (by rfl) ⟨775625, by rfl⟩) R1551251
theorem R1099993 : Reach 1099993 := rs (se 2 (by rfl) ⟨412497, by rfl⟩) R824995
theorem R1199809 : Reach 1199809 := rs (se 2 (by rfl) ⟨449928, by rfl⟩) R899857
theorem R282791 : Reach 282791 := rs (se 1 (by rfl) ⟨212093, by rfl⟩) R424187
theorem R580259 : Reach 580259 := rs (se 1 (by rfl) ⟨435194, by rfl⟩) R870389
theorem R154601 : Reach 154601 := rs (se 2 (by rfl) ⟨57975, by rfl⟩) R115951
theorem R155951 : Reach 155951 := rs (se 1 (by rfl) ⟨116963, by rfl⟩) R233927
theorem R156059 : Reach 156059 := rs (se 1 (by rfl) ⟨117044, by rfl⟩) R234089
theorem R354469 : Reach 354469 := rs (se 4 (by rfl) ⟨33231, by rfl⟩) R66463
theorem R223559 : Reach 223559 := rs (se 1 (by rfl) ⟨167669, by rfl⟩) R335339
theorem R2386259 : Reach 2386259 := rs (se 1 (by rfl) ⟨1789694, by rfl⟩) R3579389
theorem R125833 : Reach 125833 := rs (se 2 (by rfl) ⟨47187, by rfl⟩) R94375
theorem R355265 : Reach 355265 := rs (se 2 (by rfl) ⟨133224, by rfl⟩) R266449
theorem R355751 : Reach 355751 := rs (se 1 (by rfl) ⟨266813, by rfl⟩) R533627
theorem R225503 : Reach 225503 := rs (se 1 (by rfl) ⟨169127, by rfl⟩) R338255
theorem R849527 : Reach 849527 := rs (se 1 (by rfl) ⟨637145, by rfl⟩) R1274291
theorem R65471 : Reach 65471 := rs (se 1 (by rfl) ⟨49103, by rfl⟩) R98207
theorem R163903 : Reach 163903 := rs (se 1 (by rfl) ⟨122927, by rfl⟩) R245855
theorem R262253 : Reach 262253 := rs (se 3 (by rfl) ⟨49172, by rfl⟩) R98345
theorem R99611 : Reach 99611 := rs (se 1 (by rfl) ⟨74708, by rfl⟩) R149417
theorem R9275309 : Reach 9275309 := rs (se 3 (by rfl) ⟨1739120, by rfl⟩) R3478241
theorem R460859 : Reach 460859 := rs (se 1 (by rfl) ⟨345644, by rfl⟩) R691289
theorem R199223 : Reach 199223 := rs (se 1 (by rfl) ⟨149417, by rfl⟩) R298835
theorem R1378889 : Reach 1378889 := rs (se 2 (by rfl) ⟨517083, by rfl⟩) R1034167
theorem R167777 : Reach 167777 := rs (se 2 (by rfl) ⟨62916, by rfl⟩) R125833
theorem R266183 : Reach 266183 := rs (se 1 (by rfl) ⟨199637, by rfl⟩) R399275
theorem R103067 : Reach 103067 := rs (se 1 (by rfl) ⟨77300, by rfl⟩) R154601
theorem R103967 : Reach 103967 := rs (se 1 (by rfl) ⟨77975, by rfl⟩) R155951
theorem R104039 : Reach 104039 := rs (se 1 (by rfl) ⟨78029, by rfl⟩) R156059
theorem R399401 : Reach 399401 := rs (se 2 (by rfl) ⟨149775, by rfl⟩) R299551
theorem R236843 : Reach 236843 := rs (se 1 (by rfl) ⟨177632, by rfl⟩) R355265
theorem R237167 : Reach 237167 := rs (se 1 (by rfl) ⟨177875, by rfl⟩) R355751
theorem R566351 : Reach 566351 := rs (se 1 (by rfl) ⟨424763, by rfl⟩) R849527
theorem R43647 : Reach 43647 := rs (se 1 (by rfl) ⟨32735, by rfl⟩) R65471
theorem R109775 : Reach 109775 := rs (se 1 (by rfl) ⟨82331, by rfl⟩) R164663
theorem R77051 : Reach 77051 := rs (se 1 (by rfl) ⟨57788, by rfl⟩) R115577
theorem R44827 : Reach 44827 := rs (se 1 (by rfl) ⟨33620, by rfl⟩) R67241
theorem R45147 : Reach 45147 := rs (se 1 (by rfl) ⟨33860, by rfl⟩) R67721
theorem R45383 : Reach 45383 := rs (se 1 (by rfl) ⟨34037, by rfl⟩) R68075
theorem R45727 : Reach 45727 := rs (se 1 (by rfl) ⟨34295, by rfl⟩) R68591
theorem R439177 : Reach 439177 := rs (se 2 (by rfl) ⟨164691, by rfl⟩) R329383
theorem R46023 : Reach 46023 := rs (se 1 (by rfl) ⟨34517, by rfl⟩) R69035
theorem R46079 : Reach 46079 := rs (se 1 (by rfl) ⟨34559, by rfl⟩) R69119
theorem R472625 : Reach 472625 := rs (se 2 (by rfl) ⟨177234, by rfl⟩) R354469
theorem R46719 : Reach 46719 := rs (se 1 (by rfl) ⟨35039, by rfl⟩) R70079
theorem R47071 : Reach 47071 := rs (se 1 (by rfl) ⟨35303, by rfl⟩) R70607
theorem R49243 : Reach 49243 := rs (se 1 (by rfl) ⟨36932, by rfl⟩) R73865
theorem R49855 : Reach 49855 := rs (se 1 (by rfl) ⟨37391, by rfl⟩) R74783
theorem R705307 : Reach 705307 := rs (se 1 (by rfl) ⟨528980, by rfl⟩) R1057961
theorem R115739 : Reach 115739 := rs (se 1 (by rfl) ⟨86804, by rfl⟩) R173609
theorem R149039 : Reach 149039 := rs (se 1 (by rfl) ⟨111779, by rfl⟩) R223559
theorem R1590839 : Reach 1590839 := rs (se 1 (by rfl) ⟨1193129, by rfl⟩) R2386259
theorem R2607839 : Reach 2607839 := rs (se 1 (by rfl) ⟨1955879, by rfl⟩) R3911759
theorem R150335 : Reach 150335 := rs (se 1 (by rfl) ⟨112751, by rfl⟩) R225503
theorem R445601 : Reach 445601 := rs (se 2 (by rfl) ⟨167100, by rfl⟩) R334201
theorem R481609 : Reach 481609 := rs (se 2 (by rfl) ⟨180603, by rfl⟩) R361207
theorem R154799 : Reach 154799 := rs (se 1 (by rfl) ⟨116099, by rfl⟩) R232199
theorem R384365 : Reach 384365 := rs (se 3 (by rfl) ⟨72068, by rfl⟩) R144137
theorem R188527 : Reach 188527 := rs (se 1 (by rfl) ⟨141395, by rfl⟩) R282791
theorem R1466657 : Reach 1466657 := rs (se 2 (by rfl) ⟨549996, by rfl⟩) R1099993
theorem R157031 : Reach 157031 := rs (se 1 (by rfl) ⟨117773, by rfl⟩) R235547
theorem R386839 : Reach 386839 := rs (se 1 (by rfl) ⟨290129, by rfl⟩) R580259
theorem R223165 : Reach 223165 := rs (se 3 (by rfl) ⟨41843, by rfl⟩) R83687
theorem R1599745 : Reach 1599745 := rs (se 2 (by rfl) ⟨599904, by rfl⟩) R1199809
theorem R92897 : Reach 92897 := rs (se 2 (by rfl) ⟨34836, by rfl⟩) R69673
theorem R225011 : Reach 225011 := rs (se 1 (by rfl) ⟨168758, by rfl⟩) R337517
theorem R356543 : Reach 356543 := rs (se 1 (by rfl) ⟨267407, by rfl⟩) R534815
theorem R97487 : Reach 97487 := rs (se 1 (by rfl) ⟨73115, by rfl⟩) R146231
theorem R98279 : Reach 98279 := rs (se 1 (by rfl) ⟨73709, by rfl⟩) R147419
theorem R65657 : Reach 65657 := rs (se 2 (by rfl) ⟨24621, by rfl⟩) R49243
theorem R4915829 : Reach 4915829 := rs (se 5 (by rfl) ⟨230429, by rfl⟩) R460859
theorem R66407 : Reach 66407 := rs (se 1 (by rfl) ⟨49805, by rfl⟩) R99611
theorem R66473 : Reach 66473 := rs (se 2 (by rfl) ⟨24927, by rfl⟩) R49855
theorem R99359 : Reach 99359 := rs (se 1 (by rfl) ⟨74519, by rfl⟩) R149039
theorem R132815 : Reach 132815 := rs (se 1 (by rfl) ⟨99611, by rfl⟩) R199223
theorem R919259 : Reach 919259 := rs (se 1 (by rfl) ⟨689444, by rfl⟩) R1378889
theorem R1738559 : Reach 1738559 := rs (se 1 (by rfl) ⟨1303919, by rfl⟩) R2607839
theorem R100223 : Reach 100223 := rs (se 1 (by rfl) ⟨75167, by rfl⟩) R150335
theorem R3803125 : Reach 3803125 := rs (se 5 (by rfl) ⟨178271, by rfl⟩) R356543
theorem R297067 : Reach 297067 := rs (se 1 (by rfl) ⟨222800, by rfl⟩) R445601
theorem R297553 : Reach 297553 := rs (se 2 (by rfl) ⟨111582, by rfl⟩) R223165
theorem R2132993 : Reach 2132993 := rs (se 2 (by rfl) ⟨799872, by rfl⟩) R1599745
theorem R68711 : Reach 68711 := rs (se 1 (by rfl) ⟨51533, by rfl⟩) R103067
theorem R69311 : Reach 69311 := rs (se 1 (by rfl) ⟨51983, by rfl⟩) R103967
theorem R69359 : Reach 69359 := rs (se 1 (by rfl) ⟨52019, by rfl⟩) R104039
theorem R266267 : Reach 266267 := rs (se 1 (by rfl) ⟨199700, by rfl⟩) R399401
theorem R103199 : Reach 103199 := rs (se 1 (by rfl) ⟨77399, by rfl⟩) R154799
theorem R104687 : Reach 104687 := rs (se 1 (by rfl) ⟨78515, by rfl⟩) R157031
theorem R73183 : Reach 73183 := rs (se 1 (by rfl) ⟨54887, by rfl⟩) R109775
theorem R174835 : Reach 174835 := rs (se 1 (by rfl) ⟨131126, by rfl⟩) R262253
theorem R77159 : Reach 77159 := rs (se 1 (by rfl) ⟨57869, by rfl⟩) R115739
theorem R1060559 : Reach 1060559 := rs (se 1 (by rfl) ⟨795419, by rfl⟩) R1590839
theorem R2568581 : Reach 2568581 := rs (se 4 (by rfl) ⟨240804, by rfl⟩) R481609
theorem R111851 : Reach 111851 := rs (se 1 (by rfl) ⟨83888, by rfl⟩) R167777
theorem R177455 : Reach 177455 := rs (se 1 (by rfl) ⟨133091, by rfl⟩) R266183
theorem R377567 : Reach 377567 := rs (se 1 (by rfl) ⟨283175, by rfl⟩) R566351
theorem R51367 : Reach 51367 := rs (se 1 (by rfl) ⟨38525, by rfl⟩) R77051
theorem R150007 : Reach 150007 := rs (se 1 (by rfl) ⟨112505, by rfl⟩) R225011
theorem R315083 : Reach 315083 := rs (se 1 (by rfl) ⟨236312, by rfl⟩) R472625
theorem R218537 : Reach 218537 := rs (se 2 (by rfl) ⟨81951, by rfl⟩) R163903
theorem R251369 : Reach 251369 := rs (se 2 (by rfl) ⟨94263, by rfl⟩) R188527
theorem R940409 : Reach 940409 := rs (se 2 (by rfl) ⟨352653, by rfl⟩) R705307
theorem R6183539 : Reach 6183539 := rs (se 1 (by rfl) ⟨4637654, by rfl⟩) R9275309
theorem R157895 : Reach 157895 := rs (se 1 (by rfl) ⟨118421, by rfl⟩) R236843
theorem R256243 : Reach 256243 := rs (se 1 (by rfl) ⟨192182, by rfl⟩) R384365
theorem R158111 : Reach 158111 := rs (se 1 (by rfl) ⟨118583, by rfl⟩) R237167
theorem R977771 : Reach 977771 := rs (se 1 (by rfl) ⟨733328, by rfl⟩) R1466657
theorem R585569 : Reach 585569 := rs (se 2 (by rfl) ⟨219588, by rfl⟩) R439177
theorem R61931 : Reach 61931 := rs (se 1 (by rfl) ⟨46448, by rfl⟩) R92897
theorem R2063141 : Reach 2063141 := rs (se 4 (by rfl) ⟨193419, by rfl⟩) R386839
theorem R64991 : Reach 64991 := rs (se 1 (by rfl) ⟨48743, by rfl⟩) R97487
theorem R65519 : Reach 65519 := rs (se 1 (by rfl) ⟨49139, by rfl⟩) R98279
theorem R3277219 : Reach 3277219 := rs (se 1 (by rfl) ⟨2457914, by rfl⟩) R4915829
theorem R66239 : Reach 66239 := rs (se 1 (by rfl) ⟨49679, by rfl⟩) R99359
theorem R66815 : Reach 66815 := rs (se 1 (by rfl) ⟨50111, by rfl⟩) R100223
theorem R165149 : Reach 165149 := rs (se 3 (by rfl) ⟨30965, by rfl⟩) R61931
theorem R396089 : Reach 396089 := rs (se 2 (by rfl) ⟨148533, by rfl⟩) R297067
theorem R68489 : Reach 68489 := rs (se 2 (by rfl) ⟨25683, by rfl⟩) R51367
theorem R200009 : Reach 200009 := rs (se 2 (by rfl) ⟨75003, by rfl⟩) R150007
theorem R396737 : Reach 396737 := rs (se 2 (by rfl) ⟨148776, by rfl⟩) R297553
theorem R233113 : Reach 233113 := rs (se 2 (by rfl) ⟨87417, by rfl⟩) R174835
theorem R167579 : Reach 167579 := rs (se 1 (by rfl) ⟨125684, by rfl⟩) R251369
theorem R69791 : Reach 69791 := rs (se 1 (by rfl) ⟨52343, by rfl⟩) R104687
theorem R626939 : Reach 626939 := rs (se 1 (by rfl) ⟨470204, by rfl⟩) R940409
theorem R105263 : Reach 105263 := rs (se 1 (by rfl) ⟨78947, by rfl⟩) R157895
theorem R105407 : Reach 105407 := rs (se 1 (by rfl) ⟨79055, by rfl⟩) R158111
theorem R1712387 : Reach 1712387 := rs (se 1 (by rfl) ⟨1284290, by rfl⟩) R2568581
theorem R74567 : Reach 74567 := rs (se 1 (by rfl) ⟨55925, by rfl⟩) R111851
theorem R43327 : Reach 43327 := rs (se 1 (by rfl) ⟨32495, by rfl⟩) R64991
theorem R43679 : Reach 43679 := rs (se 1 (by rfl) ⟨32759, by rfl⟩) R65519
theorem R43771 : Reach 43771 := rs (se 1 (by rfl) ⟨32828, by rfl⟩) R65657
theorem R44271 : Reach 44271 := rs (se 1 (by rfl) ⟨33203, by rfl⟩) R66407
theorem R44315 : Reach 44315 := rs (se 1 (by rfl) ⟨33236, by rfl⟩) R66473
theorem R1159039 : Reach 1159039 := rs (se 1 (by rfl) ⟨869279, by rfl⟩) R1738559
theorem R1421995 : Reach 1421995 := rs (se 1 (by rfl) ⟨1066496, by rfl⟩) R2132993
theorem R45807 : Reach 45807 := rs (se 1 (by rfl) ⟨34355, by rfl⟩) R68711
theorem R275197 : Reach 275197 := rs (se 3 (by rfl) ⟨51599, by rfl⟩) R103199
theorem R46207 : Reach 46207 := rs (se 1 (by rfl) ⟨34655, by rfl⟩) R69311
theorem R210055 : Reach 210055 := rs (se 1 (by rfl) ⟨157541, by rfl⟩) R315083
theorem R46239 : Reach 46239 := rs (se 1 (by rfl) ⟨34679, by rfl⟩) R69359
theorem R177511 : Reach 177511 := rs (se 1 (by rfl) ⟨133133, by rfl⟩) R266267
theorem R341657 : Reach 341657 := rs (se 2 (by rfl) ⟨128121, by rfl⟩) R256243
theorem R145691 : Reach 145691 := rs (se 1 (by rfl) ⟨109268, by rfl⟩) R218537
theorem R51439 : Reach 51439 := rs (se 1 (by rfl) ⟨38579, by rfl⟩) R77159
theorem R707039 : Reach 707039 := rs (se 1 (by rfl) ⟨530279, by rfl⟩) R1060559
theorem R118303 : Reach 118303 := rs (se 1 (by rfl) ⟨88727, by rfl⟩) R177455
theorem R251711 : Reach 251711 := rs (se 1 (by rfl) ⟨188783, by rfl⟩) R377567
theorem R88543 : Reach 88543 := rs (se 1 (by rfl) ⟨66407, by rfl⟩) R132815
theorem R612839 : Reach 612839 := rs (se 1 (by rfl) ⟨459629, by rfl⟩) R919259
theorem R5070833 : Reach 5070833 := rs (se 2 (by rfl) ⟨1901562, by rfl⟩) R3803125
theorem R4122359 : Reach 4122359 := rs (se 1 (by rfl) ⟨3091769, by rfl⟩) R6183539
theorem R651847 : Reach 651847 := rs (se 1 (by rfl) ⟨488885, by rfl⟩) R977771
theorem R390379 : Reach 390379 := rs (se 1 (by rfl) ⟨292784, by rfl⟩) R585569
theorem R1375427 : Reach 1375427 := rs (se 1 (by rfl) ⟨1031570, by rfl⟩) R2063141
theorem R97577 : Reach 97577 := rs (se 2 (by rfl) ⟨36591, by rfl⟩) R73183
theorem R264059 : Reach 264059 := rs (se 1 (by rfl) ⟨198044, by rfl⟩) R396089
theorem R133339 : Reach 133339 := rs (se 1 (by rfl) ⟨100004, by rfl⟩) R200009
theorem R264491 : Reach 264491 := rs (se 1 (by rfl) ⟨198368, by rfl⟩) R396737
theorem R68585 : Reach 68585 := rs (se 2 (by rfl) ⟨25719, by rfl⟩) R51439
theorem R167807 : Reach 167807 := rs (se 1 (by rfl) ⟨125855, by rfl⟩) R251711
theorem R70175 : Reach 70175 := rs (se 1 (by rfl) ⟨52631, by rfl⟩) R105263
theorem R70271 : Reach 70271 := rs (se 1 (by rfl) ⟨52703, by rfl⟩) R105407
theorem R3380555 : Reach 3380555 := rs (se 1 (by rfl) ⟨2535416, by rfl⟩) R5070833
theorem R366929 : Reach 366929 := rs (se 2 (by rfl) ⟨137598, by rfl⟩) R275197
theorem R236681 : Reach 236681 := rs (se 2 (by rfl) ⟨88755, by rfl⟩) R177511
theorem R630949 : Reach 630949 := rs (se 4 (by rfl) ⟨59151, by rfl⟩) R118303
theorem R44159 : Reach 44159 := rs (se 1 (by rfl) ⟨33119, by rfl⟩) R66239
theorem R4369625 : Reach 4369625 := rs (se 2 (by rfl) ⟨1638609, by rfl⟩) R3277219
theorem R4566365 : Reach 4566365 := rs (se 3 (by rfl) ⟨856193, by rfl⟩) R1712387
theorem R44543 : Reach 44543 := rs (se 1 (by rfl) ⟨33407, by rfl⟩) R66815
theorem R110099 : Reach 110099 := rs (se 1 (by rfl) ⟨82574, by rfl⟩) R165149
theorem R471359 : Reach 471359 := rs (se 1 (by rfl) ⟨353519, by rfl⟩) R707039
theorem R45659 : Reach 45659 := rs (se 1 (by rfl) ⟨34244, by rfl⟩) R68489
theorem R111719 : Reach 111719 := rs (se 1 (by rfl) ⟨83789, by rfl⟩) R167579
theorem R46527 : Reach 46527 := rs (se 1 (by rfl) ⟨34895, by rfl⟩) R69791
theorem R408559 : Reach 408559 := rs (se 1 (by rfl) ⟨306419, by rfl⟩) R612839
theorem R310817 : Reach 310817 := rs (se 2 (by rfl) ⟨116556, by rfl⟩) R233113
theorem R49711 : Reach 49711 := rs (se 1 (by rfl) ⟨37283, by rfl⟩) R74567
theorem R869129 : Reach 869129 := rs (se 2 (by rfl) ⟨325923, by rfl⟩) R651847
theorem R280073 : Reach 280073 := rs (se 2 (by rfl) ⟨105027, by rfl⟩) R210055
theorem R118057 : Reach 118057 := rs (se 2 (by rfl) ⟨44271, by rfl⟩) R88543
theorem R6181541 : Reach 6181541 := rs (se 4 (by rfl) ⟨579519, by rfl⟩) R1159039
theorem R417959 : Reach 417959 := rs (se 1 (by rfl) ⟨313469, by rfl⟩) R626939
theorem R1895993 : Reach 1895993 := rs (se 2 (by rfl) ⟨710997, by rfl⟩) R1421995
theorem R2748239 : Reach 2748239 := rs (se 1 (by rfl) ⟨2061179, by rfl⟩) R4122359
theorem R520505 : Reach 520505 := rs (se 2 (by rfl) ⟨195189, by rfl⟩) R390379
theorem R3667805 : Reach 3667805 := rs (se 3 (by rfl) ⟨687713, by rfl⟩) R1375427
theorem R227771 : Reach 227771 := rs (se 1 (by rfl) ⟨170828, by rfl⟩) R341657
theorem R97127 : Reach 97127 := rs (se 1 (by rfl) ⟨72845, by rfl⟩) R145691
theorem R65051 : Reach 65051 := rs (se 1 (by rfl) ⟨48788, by rfl⟩) R97577
theorem R66281 : Reach 66281 := rs (se 2 (by rfl) ⟨24855, by rfl⟩) R49711
theorem R73399 : Reach 73399 := rs (se 1 (by rfl) ⟨55049, by rfl⟩) R110099
theorem R74479 : Reach 74479 := rs (se 1 (by rfl) ⟨55859, by rfl⟩) R111719
theorem R43367 : Reach 43367 := rs (se 1 (by rfl) ⟨32525, by rfl⟩) R65051
theorem R207211 : Reach 207211 := rs (se 1 (by rfl) ⟨155408, by rfl⟩) R310817
theorem R1256957 : Reach 1256957 := rs (se 3 (by rfl) ⟨235679, by rfl⟩) R471359
theorem R176039 : Reach 176039 := rs (se 1 (by rfl) ⟨132029, by rfl⟩) R264059
theorem R176327 : Reach 176327 := rs (se 1 (by rfl) ⟨132245, by rfl⟩) R264491
theorem R45723 : Reach 45723 := rs (se 1 (by rfl) ⟨34292, by rfl⟩) R68585
theorem R111871 : Reach 111871 := rs (se 1 (by rfl) ⟨83903, by rfl⟩) R167807
theorem R177785 : Reach 177785 := rs (se 2 (by rfl) ⟨66669, by rfl⟩) R133339
theorem R46783 : Reach 46783 := rs (se 1 (by rfl) ⟨35087, by rfl⟩) R70175
theorem R46847 : Reach 46847 := rs (se 1 (by rfl) ⟨35135, by rfl⟩) R70271
theorem R244619 : Reach 244619 := rs (se 1 (by rfl) ⟨183464, by rfl⟩) R366929
theorem R278639 : Reach 278639 := rs (se 1 (by rfl) ⟨208979, by rfl⟩) R417959
theorem R1263995 : Reach 1263995 := rs (se 1 (by rfl) ⟨947996, by rfl⟩) R1895993
theorem R347003 : Reach 347003 := rs (se 1 (by rfl) ⟨260252, by rfl⟩) R520505
theorem R2445203 : Reach 2445203 := rs (se 1 (by rfl) ⟨1833902, by rfl⟩) R3667805
theorem R544745 : Reach 544745 := rs (se 2 (by rfl) ⟨204279, by rfl⟩) R408559
theorem R151847 : Reach 151847 := rs (se 1 (by rfl) ⟨113885, by rfl⟩) R227771
theorem R841265 : Reach 841265 := rs (se 2 (by rfl) ⟨315474, by rfl⟩) R630949
theorem R579419 : Reach 579419 := rs (se 1 (by rfl) ⟨434564, by rfl⟩) R869129
theorem R186715 : Reach 186715 := rs (se 1 (by rfl) ⟨140036, by rfl⟩) R280073
theorem R4121027 : Reach 4121027 := rs (se 1 (by rfl) ⟨3090770, by rfl⟩) R6181541
theorem R2253703 : Reach 2253703 := rs (se 1 (by rfl) ⟨1690277, by rfl⟩) R3380555
theorem R157409 : Reach 157409 := rs (se 2 (by rfl) ⟨59028, by rfl⟩) R118057
theorem R157787 : Reach 157787 := rs (se 1 (by rfl) ⟨118340, by rfl⟩) R236681
theorem R2913083 : Reach 2913083 := rs (se 1 (by rfl) ⟨2184812, by rfl⟩) R4369625
theorem R3044243 : Reach 3044243 := rs (se 1 (by rfl) ⟨2283182, by rfl⟩) R4566365
theorem R1832159 : Reach 1832159 := rs (se 1 (by rfl) ⟨1374119, by rfl⟩) R2748239
theorem R64751 : Reach 64751 := rs (se 1 (by rfl) ⟨48563, by rfl⟩) R97127
theorem R99305 : Reach 99305 := rs (se 2 (by rfl) ⟨37239, by rfl⟩) R74479
theorem R231335 : Reach 231335 := rs (se 1 (by rfl) ⟨173501, by rfl⟩) R347003
theorem R363163 : Reach 363163 := rs (se 1 (by rfl) ⟨272372, by rfl⟩) R544745
theorem R101231 : Reach 101231 := rs (se 1 (by rfl) ⟨75923, by rfl⟩) R151847
theorem R560843 : Reach 560843 := rs (se 1 (by rfl) ⟨420632, by rfl⟩) R841265
theorem R104939 : Reach 104939 := rs (se 1 (by rfl) ⟨78704, by rfl⟩) R157409
theorem R105191 : Reach 105191 := rs (se 1 (by rfl) ⟨78893, by rfl⟩) R157787
theorem R1942055 : Reach 1942055 := rs (se 1 (by rfl) ⟨1456541, by rfl⟩) R2913083
theorem R1221439 : Reach 1221439 := rs (se 1 (by rfl) ⟨916079, by rfl⟩) R1832159
theorem R43167 : Reach 43167 := rs (se 1 (by rfl) ⟨32375, by rfl⟩) R64751
theorem R44187 : Reach 44187 := rs (se 1 (by rfl) ⟨33140, by rfl⟩) R66281
theorem R276281 : Reach 276281 := rs (se 2 (by rfl) ⟨103605, by rfl⟩) R207211
theorem R149161 : Reach 149161 := rs (se 2 (by rfl) ⟨55935, by rfl⟩) R111871
theorem R837971 : Reach 837971 := rs (se 1 (by rfl) ⟨628478, by rfl⟩) R1256957
theorem R117359 : Reach 117359 := rs (se 1 (by rfl) ⟨88019, by rfl⟩) R176039
theorem R117551 : Reach 117551 := rs (se 1 (by rfl) ⟨88163, by rfl⟩) R176327
theorem R248953 : Reach 248953 := rs (se 2 (by rfl) ⟨93357, by rfl⟩) R186715
theorem R118523 : Reach 118523 := rs (se 1 (by rfl) ⟨88892, by rfl⟩) R177785
theorem R185759 : Reach 185759 := rs (se 1 (by rfl) ⟨139319, by rfl⟩) R278639
theorem R3004937 : Reach 3004937 := rs (se 2 (by rfl) ⟨1126851, by rfl⟩) R2253703
theorem R842663 : Reach 842663 := rs (se 1 (by rfl) ⟨631997, by rfl⟩) R1263995
theorem R1630135 : Reach 1630135 := rs (se 1 (by rfl) ⟨1222601, by rfl⟩) R2445203
theorem R386279 : Reach 386279 := rs (se 1 (by rfl) ⟨289709, by rfl⟩) R579419
theorem R2747351 : Reach 2747351 := rs (se 1 (by rfl) ⟨2060513, by rfl⟩) R4121027
theorem R2029495 : Reach 2029495 := rs (se 1 (by rfl) ⟨1522121, by rfl⟩) R3044243
theorem R163079 : Reach 163079 := rs (se 1 (by rfl) ⟨122309, by rfl⟩) R244619
theorem R97865 : Reach 97865 := rs (se 2 (by rfl) ⟨36699, by rfl⟩) R73399
theorem R66203 : Reach 66203 := rs (se 1 (by rfl) ⟨49652, by rfl⟩) R99305
theorem R558647 : Reach 558647 := rs (se 1 (by rfl) ⟨418985, by rfl⟩) R837971
theorem R67487 : Reach 67487 := rs (se 1 (by rfl) ⟨50615, by rfl⟩) R101231
theorem R198881 : Reach 198881 := rs (se 2 (by rfl) ⟨74580, by rfl⟩) R149161
theorem R331937 : Reach 331937 := rs (se 2 (by rfl) ⟨124476, by rfl⟩) R248953
theorem R69959 : Reach 69959 := rs (se 1 (by rfl) ⟨52469, by rfl⟩) R104939
theorem R2003291 : Reach 2003291 := rs (se 1 (by rfl) ⟨1502468, by rfl⟩) R3004937
theorem R70127 : Reach 70127 := rs (se 1 (by rfl) ⟨52595, by rfl⟩) R105191
theorem R561775 : Reach 561775 := rs (se 1 (by rfl) ⟨421331, by rfl⟩) R842663
theorem R108719 : Reach 108719 := rs (se 1 (by rfl) ⟨81539, by rfl⟩) R163079
theorem R2173513 : Reach 2173513 := rs (se 2 (by rfl) ⟨815067, by rfl⟩) R1630135
theorem R78239 : Reach 78239 := rs (se 1 (by rfl) ⟨58679, by rfl⟩) R117359
theorem R78367 : Reach 78367 := rs (se 1 (by rfl) ⟨58775, by rfl⟩) R117551
theorem R373895 : Reach 373895 := rs (se 1 (by rfl) ⟨280421, by rfl⟩) R560843
theorem R79015 : Reach 79015 := rs (se 1 (by rfl) ⟨59261, by rfl⟩) R118523
theorem R1294703 : Reach 1294703 := rs (se 1 (by rfl) ⟨971027, by rfl⟩) R1942055
theorem R2705993 : Reach 2705993 := rs (se 2 (by rfl) ⟨1014747, by rfl⟩) R2029495
theorem R184187 : Reach 184187 := rs (se 1 (by rfl) ⟨138140, by rfl⟩) R276281
theorem R1628585 : Reach 1628585 := rs (se 2 (by rfl) ⟨610719, by rfl⟩) R1221439
theorem R154223 : Reach 154223 := rs (se 1 (by rfl) ⟨115667, by rfl⟩) R231335
theorem R484217 : Reach 484217 := rs (se 2 (by rfl) ⟨181581, by rfl⟩) R363163
theorem R123839 : Reach 123839 := rs (se 1 (by rfl) ⟨92879, by rfl⟩) R185759
theorem R257519 : Reach 257519 := rs (se 1 (by rfl) ⟨193139, by rfl⟩) R386279
theorem R1831567 : Reach 1831567 := rs (se 1 (by rfl) ⟨1373675, by rfl⟩) R2747351
theorem R65243 : Reach 65243 := rs (se 1 (by rfl) ⟨48932, by rfl⟩) R97865
theorem R132587 : Reach 132587 := rs (se 1 (by rfl) ⟨99440, by rfl⟩) R198881
theorem R1803995 : Reach 1803995 := rs (se 1 (by rfl) ⟨1352996, by rfl⟩) R2705993
theorem R1085723 : Reach 1085723 := rs (se 1 (by rfl) ⟨814292, by rfl⟩) R1628585
theorem R102815 : Reach 102815 := rs (se 1 (by rfl) ⟨77111, by rfl⟩) R154223
theorem R104489 : Reach 104489 := rs (se 2 (by rfl) ⟨39183, by rfl⟩) R78367
theorem R72479 : Reach 72479 := rs (se 1 (by rfl) ⟨54359, by rfl⟩) R108719
theorem R105353 : Reach 105353 := rs (se 2 (by rfl) ⟨39507, by rfl⟩) R79015
theorem R171679 : Reach 171679 := rs (se 1 (by rfl) ⟨128759, by rfl⟩) R257519
theorem R43495 : Reach 43495 := rs (se 1 (by rfl) ⟨32621, by rfl⟩) R65243
theorem R863135 : Reach 863135 := rs (se 1 (by rfl) ⟨647351, by rfl⟩) R1294703
theorem R44135 : Reach 44135 := rs (se 1 (by rfl) ⟨33101, by rfl⟩) R66203
theorem R372431 : Reach 372431 := rs (se 1 (by rfl) ⟨279323, by rfl⟩) R558647
theorem R44991 : Reach 44991 := rs (se 1 (by rfl) ⟨33743, by rfl⟩) R67487
theorem R46639 : Reach 46639 := rs (se 1 (by rfl) ⟨34979, by rfl⟩) R69959
theorem R46751 : Reach 46751 := rs (se 1 (by rfl) ⟨35063, by rfl⟩) R70127
theorem R2898017 : Reach 2898017 := rs (se 2 (by rfl) ⟨1086756, by rfl⟩) R2173513
theorem R82559 : Reach 82559 := rs (se 1 (by rfl) ⟨61919, by rfl⟩) R123839
theorem R2442089 : Reach 2442089 := rs (se 2 (by rfl) ⟨915783, by rfl⟩) R1831567
theorem R52159 : Reach 52159 := rs (se 1 (by rfl) ⟨39119, by rfl⟩) R78239
theorem R249263 : Reach 249263 := rs (se 1 (by rfl) ⟨186947, by rfl⟩) R373895
theorem R122791 : Reach 122791 := rs (se 1 (by rfl) ⟨92093, by rfl⟩) R184187
theorem R221291 : Reach 221291 := rs (se 1 (by rfl) ⟨165968, by rfl⟩) R331937
theorem R1335527 : Reach 1335527 := rs (se 1 (by rfl) ⟨1001645, by rfl⟩) R2003291
theorem R322811 : Reach 322811 := rs (se 1 (by rfl) ⟨242108, by rfl⟩) R484217
theorem R749033 : Reach 749033 := rs (se 2 (by rfl) ⟨280887, by rfl⟩) R561775
theorem R166175 : Reach 166175 := rs (se 1 (by rfl) ⟨124631, by rfl⟩) R249263
theorem R723815 : Reach 723815 := rs (se 1 (by rfl) ⟨542861, by rfl⟩) R1085723
theorem R68543 : Reach 68543 := rs (se 1 (by rfl) ⟨51407, by rfl⟩) R102815
theorem R69545 : Reach 69545 := rs (se 2 (by rfl) ⟨26079, by rfl⟩) R52159
theorem R69659 : Reach 69659 := rs (se 1 (by rfl) ⟨52244, by rfl⟩) R104489
theorem R70235 : Reach 70235 := rs (se 1 (by rfl) ⟨52676, by rfl⟩) R105353
theorem R890351 : Reach 890351 := rs (se 1 (by rfl) ⟨667763, by rfl⟩) R1335527
theorem R499355 : Reach 499355 := rs (se 1 (by rfl) ⟨374516, by rfl⟩) R749033
theorem R48319 : Reach 48319 := rs (se 1 (by rfl) ⟨36239, by rfl⟩) R72479
theorem R147527 : Reach 147527 := rs (se 1 (by rfl) ⟨110645, by rfl⟩) R221291
theorem R575423 : Reach 575423 := rs (se 1 (by rfl) ⟨431567, by rfl⟩) R863135
theorem R215207 : Reach 215207 := rs (se 1 (by rfl) ⟨161405, by rfl⟩) R322811
theorem R248287 : Reach 248287 := rs (se 1 (by rfl) ⟨186215, by rfl⟩) R372431
theorem R1628059 : Reach 1628059 := rs (se 1 (by rfl) ⟨1221044, by rfl⟩) R2442089
theorem R88391 : Reach 88391 := rs (se 1 (by rfl) ⟨66293, by rfl⟩) R132587
theorem R1202663 : Reach 1202663 := rs (se 1 (by rfl) ⟨901997, by rfl⟩) R1803995
theorem R220157 : Reach 220157 := rs (se 3 (by rfl) ⟨41279, by rfl⟩) R82559
theorem R1932011 : Reach 1932011 := rs (se 1 (by rfl) ⟨1449008, by rfl⟩) R2898017
theorem R228905 : Reach 228905 := rs (se 2 (by rfl) ⟨85839, by rfl⟩) R171679
theorem R163721 : Reach 163721 := rs (se 2 (by rfl) ⟨61395, by rfl⟩) R122791
theorem R98351 : Reach 98351 := rs (se 1 (by rfl) ⟨73763, by rfl⟩) R147527
theorem R331049 : Reach 331049 := rs (se 2 (by rfl) ⟨124143, by rfl⟩) R248287
theorem R593567 : Reach 593567 := rs (se 1 (by rfl) ⟨445175, by rfl⟩) R890351
theorem R332903 : Reach 332903 := rs (se 1 (by rfl) ⟨249677, by rfl⟩) R499355
theorem R235709 : Reach 235709 := rs (se 3 (by rfl) ⟨44195, by rfl⟩) R88391
theorem R2170745 : Reach 2170745 := rs (se 2 (by rfl) ⟨814029, by rfl⟩) R1628059
theorem R1288007 : Reach 1288007 := rs (se 1 (by rfl) ⟨966005, by rfl⟩) R1932011
theorem R109147 : Reach 109147 := rs (se 1 (by rfl) ⟨81860, by rfl⟩) R163721
theorem R143471 : Reach 143471 := rs (se 1 (by rfl) ⟨107603, by rfl⟩) R215207
theorem R110783 : Reach 110783 := rs (se 1 (by rfl) ⟨83087, by rfl⟩) R166175
theorem R45695 : Reach 45695 := rs (se 1 (by rfl) ⟨34271, by rfl⟩) R68543
theorem R46363 : Reach 46363 := rs (se 1 (by rfl) ⟨34772, by rfl⟩) R69545
theorem R46439 : Reach 46439 := rs (se 1 (by rfl) ⟨34829, by rfl⟩) R69659
theorem R46823 : Reach 46823 := rs (se 1 (by rfl) ⟨35117, by rfl⟩) R70235
theorem R801775 : Reach 801775 := rs (se 1 (by rfl) ⟨601331, by rfl⟩) R1202663
theorem R146771 : Reach 146771 := rs (se 1 (by rfl) ⟨110078, by rfl⟩) R220157
theorem R152603 : Reach 152603 := rs (se 1 (by rfl) ⟨114452, by rfl⟩) R228905
theorem R383615 : Reach 383615 := rs (se 1 (by rfl) ⟨287711, by rfl⟩) R575423
theorem R482543 : Reach 482543 := rs (se 1 (by rfl) ⟨361907, by rfl⟩) R723815
theorem R257701 : Reach 257701 := rs (se 4 (by rfl) ⟨24159, by rfl⟩) R48319
theorem R65567 : Reach 65567 := rs (se 1 (by rfl) ⟨49175, by rfl⟩) R98351
theorem R395711 : Reach 395711 := rs (se 1 (by rfl) ⟨296783, by rfl⟩) R593567
theorem R101735 : Reach 101735 := rs (se 1 (by rfl) ⟨76301, by rfl⟩) R152603
theorem R1447163 : Reach 1447163 := rs (se 1 (by rfl) ⟨1085372, by rfl⟩) R2170745
theorem R858671 : Reach 858671 := rs (se 1 (by rfl) ⟨644003, by rfl⟩) R1288007
theorem R73855 : Reach 73855 := rs (se 1 (by rfl) ⟨55391, by rfl⟩) R110783
theorem R145529 : Reach 145529 := rs (se 2 (by rfl) ⟨54573, by rfl⟩) R109147
theorem R343601 : Reach 343601 := rs (se 2 (by rfl) ⟨128850, by rfl⟩) R257701
theorem R1069033 : Reach 1069033 := rs (se 2 (by rfl) ⟨400887, by rfl⟩) R801775
theorem R382589 : Reach 382589 := rs (se 3 (by rfl) ⟨71735, by rfl⟩) R143471
theorem R220699 : Reach 220699 := rs (se 1 (by rfl) ⟨165524, by rfl⟩) R331049
theorem R221935 : Reach 221935 := rs (se 1 (by rfl) ⟨166451, by rfl⟩) R332903
theorem R157139 : Reach 157139 := rs (se 1 (by rfl) ⟨117854, by rfl⟩) R235709
theorem R255743 : Reach 255743 := rs (se 1 (by rfl) ⟨191807, by rfl⟩) R383615
theorem R124861 : Reach 124861 := rs (se 3 (by rfl) ⟨23411, by rfl⟩) R46823
theorem R321695 : Reach 321695 := rs (se 1 (by rfl) ⟨241271, by rfl⟩) R482543
theorem R97847 : Reach 97847 := rs (se 1 (by rfl) ⟨73385, by rfl⟩) R146771
theorem R393893 : Reach 393893 := rs (se 4 (by rfl) ⟨36927, by rfl⟩) R73855
theorem R295913 : Reach 295913 := rs (se 2 (by rfl) ⟨110967, by rfl⟩) R221935
theorem R263807 : Reach 263807 := rs (se 1 (by rfl) ⟨197855, by rfl⟩) R395711
theorem R67823 : Reach 67823 := rs (se 1 (by rfl) ⟨50867, by rfl⟩) R101735
theorem R166481 : Reach 166481 := rs (se 2 (by rfl) ⟨62430, by rfl⟩) R124861
theorem R104759 : Reach 104759 := rs (se 1 (by rfl) ⟨78569, by rfl⟩) R157139
theorem R170495 : Reach 170495 := rs (se 1 (by rfl) ⟨127871, by rfl⟩) R255743
theorem R43711 : Reach 43711 := rs (se 1 (by rfl) ⟨32783, by rfl⟩) R65567
theorem R964775 : Reach 964775 := rs (se 1 (by rfl) ⟨723581, by rfl⟩) R1447163
theorem R572447 : Reach 572447 := rs (se 1 (by rfl) ⟨429335, by rfl⟩) R858671
theorem R1425377 : Reach 1425377 := rs (se 2 (by rfl) ⟨534516, by rfl⟩) R1069033
theorem R214463 : Reach 214463 := rs (se 1 (by rfl) ⟨160847, by rfl⟩) R321695
theorem R255059 : Reach 255059 := rs (se 1 (by rfl) ⟨191294, by rfl⟩) R382589
theorem R97019 : Reach 97019 := rs (se 1 (by rfl) ⟨72764, by rfl⟩) R145529
theorem R294265 : Reach 294265 := rs (se 2 (by rfl) ⟨110349, by rfl⟩) R220699
theorem R229067 : Reach 229067 := rs (se 1 (by rfl) ⟨171800, by rfl⟩) R343601
theorem R65231 : Reach 65231 := rs (se 1 (by rfl) ⟨48923, by rfl⟩) R97847
theorem R262595 : Reach 262595 := rs (se 1 (by rfl) ⟨196946, by rfl⟩) R393893
theorem R197275 : Reach 197275 := rs (se 1 (by rfl) ⟨147956, by rfl⟩) R295913
theorem R69839 : Reach 69839 := rs (se 1 (by rfl) ⟨52379, by rfl⟩) R104759
theorem R170039 : Reach 170039 := rs (se 1 (by rfl) ⟨127529, by rfl⟩) R255059
theorem R43487 : Reach 43487 := rs (se 1 (by rfl) ⟨32615, by rfl⟩) R65231
theorem R142975 : Reach 142975 := rs (se 1 (by rfl) ⟨107231, by rfl⟩) R214463
theorem R175871 : Reach 175871 := rs (se 1 (by rfl) ⟨131903, by rfl⟩) R263807
theorem R45215 : Reach 45215 := rs (se 1 (by rfl) ⟨33911, by rfl⟩) R67823
theorem R110987 : Reach 110987 := rs (se 1 (by rfl) ⟨83240, by rfl⟩) R166481
theorem R113663 : Reach 113663 := rs (se 1 (by rfl) ⟨85247, by rfl⟩) R170495
theorem R643183 : Reach 643183 := rs (se 1 (by rfl) ⟨482387, by rfl⟩) R964775
theorem R381631 : Reach 381631 := rs (se 1 (by rfl) ⟨286223, by rfl⟩) R572447
theorem R152711 : Reach 152711 := rs (se 1 (by rfl) ⟨114533, by rfl⟩) R229067
theorem R392353 : Reach 392353 := rs (se 2 (by rfl) ⟨147132, by rfl⟩) R294265
theorem R64679 : Reach 64679 := rs (se 1 (by rfl) ⟨48509, by rfl⟩) R97019
theorem R3801005 : Reach 3801005 := rs (se 3 (by rfl) ⟨712688, by rfl⟩) R1425377
theorem R263033 : Reach 263033 := rs (se 2 (by rfl) ⟨98637, by rfl⟩) R197275
theorem R101807 : Reach 101807 := rs (se 1 (by rfl) ⟨76355, by rfl⟩) R152711
theorem R73991 : Reach 73991 := rs (se 1 (by rfl) ⟨55493, by rfl⟩) R110987
theorem R762533 : Reach 762533 := rs (se 4 (by rfl) ⟨71487, by rfl⟩) R142975
theorem R75775 : Reach 75775 := rs (se 1 (by rfl) ⟨56831, by rfl⟩) R113663
theorem R43119 : Reach 43119 := rs (se 1 (by rfl) ⟨32339, by rfl⟩) R64679
theorem R2534003 : Reach 2534003 := rs (se 1 (by rfl) ⟨1900502, by rfl⟩) R3801005
theorem R175063 : Reach 175063 := rs (se 1 (by rfl) ⟨131297, by rfl⟩) R262595
theorem R46559 : Reach 46559 := rs (se 1 (by rfl) ⟨34919, by rfl⟩) R69839
theorem R113359 : Reach 113359 := rs (se 1 (by rfl) ⟨85019, by rfl⟩) R170039
theorem R508841 : Reach 508841 := rs (se 2 (by rfl) ⟨190815, by rfl⟩) R381631
theorem R117247 : Reach 117247 := rs (se 1 (by rfl) ⟨87935, by rfl⟩) R175871
theorem R13721237 : Reach 13721237 := rs (se 6 (by rfl) ⟨321591, by rfl⟩) R643183
theorem R2092549 : Reach 2092549 := rs (se 4 (by rfl) ⟨196176, by rfl⟩) R392353
theorem R197309 : Reach 197309 := rs (se 3 (by rfl) ⟨36995, by rfl⟩) R73991
theorem R67871 : Reach 67871 := rs (se 1 (by rfl) ⟨50903, by rfl⟩) R101807
theorem R101033 : Reach 101033 := rs (se 2 (by rfl) ⟨37887, by rfl⟩) R75775
theorem R233417 : Reach 233417 := rs (se 2 (by rfl) ⟨87531, by rfl⟩) R175063
theorem R2790065 : Reach 2790065 := rs (se 2 (by rfl) ⟨1046274, by rfl⟩) R2092549
theorem R9147491 : Reach 9147491 := rs (se 1 (by rfl) ⟨6860618, by rfl⟩) R13721237
theorem R175355 : Reach 175355 := rs (se 1 (by rfl) ⟨131516, by rfl⟩) R263033
theorem R339227 : Reach 339227 := rs (se 1 (by rfl) ⟨254420, by rfl⟩) R508841
theorem R508355 : Reach 508355 := rs (se 1 (by rfl) ⟨381266, by rfl⟩) R762533
theorem R1689335 : Reach 1689335 := rs (se 1 (by rfl) ⟨1267001, by rfl⟩) R2534003
theorem R151145 : Reach 151145 := rs (se 2 (by rfl) ⟨56679, by rfl⟩) R113359
theorem R156329 : Reach 156329 := rs (se 2 (by rfl) ⟨58623, by rfl⟩) R117247
theorem R131539 : Reach 131539 := rs (se 1 (by rfl) ⟨98654, by rfl⟩) R197309
theorem R67355 : Reach 67355 := rs (se 1 (by rfl) ⟨50516, by rfl⟩) R101033
theorem R7440173 : Reach 7440173 := rs (se 3 (by rfl) ⟨1395032, by rfl⟩) R2790065
theorem R100763 : Reach 100763 := rs (se 1 (by rfl) ⟨75572, by rfl⟩) R151145
theorem R6098327 : Reach 6098327 := rs (se 1 (by rfl) ⟨4573745, by rfl⟩) R9147491
theorem R104219 : Reach 104219 := rs (se 1 (by rfl) ⟨78164, by rfl⟩) R156329
theorem R338903 : Reach 338903 := rs (se 1 (by rfl) ⟨254177, by rfl⟩) R508355
theorem R1126223 : Reach 1126223 := rs (se 1 (by rfl) ⟨844667, by rfl⟩) R1689335
theorem R45247 : Reach 45247 := rs (se 1 (by rfl) ⟨33935, by rfl⟩) R67871
theorem R116903 : Reach 116903 := rs (se 1 (by rfl) ⟨87677, by rfl⟩) R175355
theorem R155611 : Reach 155611 := rs (se 1 (by rfl) ⟨116708, by rfl⟩) R233417
theorem R226151 : Reach 226151 := rs (se 1 (by rfl) ⟨169613, by rfl⟩) R339227
theorem R67175 : Reach 67175 := rs (se 1 (by rfl) ⟨50381, by rfl⟩) R100763
theorem R4065551 : Reach 4065551 := rs (se 1 (by rfl) ⟨3049163, by rfl⟩) R6098327
theorem R69479 : Reach 69479 := rs (se 1 (by rfl) ⟨52109, by rfl⟩) R104219
theorem R207481 : Reach 207481 := rs (se 2 (by rfl) ⟨77805, by rfl⟩) R155611
theorem R175385 : Reach 175385 := rs (se 2 (by rfl) ⟨65769, by rfl⟩) R131539
theorem R44903 : Reach 44903 := rs (se 1 (by rfl) ⟨33677, by rfl⟩) R67355
theorem R4960115 : Reach 4960115 := rs (se 1 (by rfl) ⟨3720086, by rfl⟩) R7440173
theorem R77935 : Reach 77935 := rs (se 1 (by rfl) ⟨58451, by rfl⟩) R116903
theorem R150767 : Reach 150767 := rs (se 1 (by rfl) ⟨113075, by rfl⟩) R226151
theorem R225935 : Reach 225935 := rs (se 1 (by rfl) ⟨169451, by rfl⟩) R338903
theorem R750815 : Reach 750815 := rs (se 1 (by rfl) ⟨563111, by rfl⟩) R1126223
theorem R100511 : Reach 100511 := rs (se 1 (by rfl) ⟨75383, by rfl⟩) R150767
theorem R103913 : Reach 103913 := rs (se 2 (by rfl) ⟨38967, by rfl⟩) R77935
theorem R500543 : Reach 500543 := rs (se 1 (by rfl) ⟨375407, by rfl⟩) R750815
theorem R44783 : Reach 44783 := rs (se 1 (by rfl) ⟨33587, by rfl⟩) R67175
theorem R46319 : Reach 46319 := rs (se 1 (by rfl) ⟨34739, by rfl⟩) R69479
theorem R276641 : Reach 276641 := rs (se 2 (by rfl) ⟨103740, by rfl⟩) R207481
theorem R116923 : Reach 116923 := rs (se 1 (by rfl) ⟨87692, by rfl⟩) R175385
theorem R150623 : Reach 150623 := rs (se 1 (by rfl) ⟨112967, by rfl⟩) R225935
theorem R2710367 : Reach 2710367 := rs (se 1 (by rfl) ⟨2032775, by rfl⟩) R4065551
theorem R3306743 : Reach 3306743 := rs (se 1 (by rfl) ⟨2480057, by rfl⟩) R4960115
theorem R67007 : Reach 67007 := rs (se 1 (by rfl) ⟨50255, by rfl⟩) R100511
theorem R100415 : Reach 100415 := rs (se 1 (by rfl) ⟨75311, by rfl⟩) R150623
theorem R69275 : Reach 69275 := rs (se 1 (by rfl) ⟨51956, by rfl⟩) R103913
theorem R1806911 : Reach 1806911 := rs (se 1 (by rfl) ⟨1355183, by rfl⟩) R2710367
theorem R333695 : Reach 333695 := rs (se 1 (by rfl) ⟨250271, by rfl⟩) R500543
theorem R2204495 : Reach 2204495 := rs (se 1 (by rfl) ⟨1653371, by rfl⟩) R3306743
theorem R184427 : Reach 184427 := rs (se 1 (by rfl) ⟨138320, by rfl⟩) R276641
theorem R155897 : Reach 155897 := rs (se 2 (by rfl) ⟨58461, by rfl⟩) R116923
theorem R66943 : Reach 66943 := rs (se 1 (by rfl) ⟨50207, by rfl⟩) R100415
theorem R103931 : Reach 103931 := rs (se 1 (by rfl) ⟨77948, by rfl⟩) R155897
theorem R44671 : Reach 44671 := rs (se 1 (by rfl) ⟨33503, by rfl⟩) R67007
theorem R46183 : Reach 46183 := rs (se 1 (by rfl) ⟨34637, by rfl⟩) R69275
theorem R122951 : Reach 122951 := rs (se 1 (by rfl) ⟨92213, by rfl⟩) R184427
theorem R1204607 : Reach 1204607 := rs (se 1 (by rfl) ⟨903455, by rfl⟩) R1806911
theorem R222463 : Reach 222463 := rs (se 1 (by rfl) ⟨166847, by rfl⟩) R333695
theorem R1469663 : Reach 1469663 := rs (se 1 (by rfl) ⟨1102247, by rfl⟩) R2204495
theorem R296617 : Reach 296617 := rs (se 2 (by rfl) ⟨111231, by rfl⟩) R222463
theorem R69287 : Reach 69287 := rs (se 1 (by rfl) ⟨51965, by rfl⟩) R103931
theorem R81967 : Reach 81967 := rs (se 1 (by rfl) ⟨61475, by rfl⟩) R122951
theorem R803071 : Reach 803071 := rs (se 1 (by rfl) ⟨602303, by rfl⟩) R1204607
theorem R89257 : Reach 89257 := rs (se 2 (by rfl) ⟨33471, by rfl⟩) R66943
theorem R979775 : Reach 979775 := rs (se 1 (by rfl) ⟨734831, by rfl⟩) R1469663
theorem R395489 : Reach 395489 := rs (se 2 (by rfl) ⟨148308, by rfl⟩) R296617
theorem R109289 : Reach 109289 := rs (se 2 (by rfl) ⟨40983, by rfl⟩) R81967
theorem R46191 : Reach 46191 := rs (se 1 (by rfl) ⟨34643, by rfl⟩) R69287
theorem R119009 : Reach 119009 := rs (se 2 (by rfl) ⟨44628, by rfl⟩) R89257
theorem R1070761 : Reach 1070761 := rs (se 2 (by rfl) ⟨401535, by rfl⟩) R803071
theorem R653183 : Reach 653183 := rs (se 1 (by rfl) ⟨489887, by rfl⟩) R979775
theorem R1054637 : Reach 1054637 := rs (se 3 (by rfl) ⟨197744, by rfl⟩) R395489
theorem R72859 : Reach 72859 := rs (se 1 (by rfl) ⟨54644, by rfl⟩) R109289
theorem R435455 : Reach 435455 := rs (se 1 (by rfl) ⟨326591, by rfl⟩) R653183
theorem R79339 : Reach 79339 := rs (se 1 (by rfl) ⟨59504, by rfl⟩) R119009
theorem R1427681 : Reach 1427681 := rs (se 2 (by rfl) ⟨535380, by rfl⟩) R1070761
theorem R951787 : Reach 951787 := rs (se 1 (by rfl) ⟨713840, by rfl⟩) R1427681
theorem R105785 : Reach 105785 := rs (se 2 (by rfl) ⟨39669, by rfl⟩) R79339
theorem R703091 : Reach 703091 := rs (se 1 (by rfl) ⟨527318, by rfl⟩) R1054637
theorem R290303 : Reach 290303 := rs (se 1 (by rfl) ⟨217727, by rfl⟩) R435455
theorem R97145 : Reach 97145 := rs (se 2 (by rfl) ⟨36429, by rfl⟩) R72859
theorem R70523 : Reach 70523 := rs (se 1 (by rfl) ⟨52892, by rfl⟩) R105785
theorem R1874909 : Reach 1874909 := rs (se 3 (by rfl) ⟨351545, by rfl⟩) R703091
theorem R1269049 : Reach 1269049 := rs (se 2 (by rfl) ⟨475893, by rfl⟩) R951787
theorem R193535 : Reach 193535 := rs (se 1 (by rfl) ⟨145151, by rfl⟩) R290303
theorem R64763 : Reach 64763 := rs (se 1 (by rfl) ⟨48572, by rfl⟩) R97145
theorem R1249939 : Reach 1249939 := rs (se 1 (by rfl) ⟨937454, by rfl⟩) R1874909
theorem R43175 : Reach 43175 := rs (se 1 (by rfl) ⟨32381, by rfl⟩) R64763
theorem R47015 : Reach 47015 := rs (se 1 (by rfl) ⟨35261, by rfl⟩) R70523
theorem R1692065 : Reach 1692065 := rs (se 2 (by rfl) ⟨634524, by rfl⟩) R1269049
theorem R129023 : Reach 129023 := rs (se 1 (by rfl) ⟨96767, by rfl⟩) R193535
theorem R1128043 : Reach 1128043 := rs (se 1 (by rfl) ⟨846032, by rfl⟩) R1692065
theorem R86015 : Reach 86015 := rs (se 1 (by rfl) ⟨64511, by rfl⟩) R129023
theorem R1666585 : Reach 1666585 := rs (se 2 (by rfl) ⟨624969, by rfl⟩) R1249939
theorem R57343 : Reach 57343 := rs (se 1 (by rfl) ⟨43007, by rfl⟩) R86015
theorem R2222113 : Reach 2222113 := rs (se 2 (by rfl) ⟨833292, by rfl⟩) R1666585
theorem R1504057 : Reach 1504057 := rs (se 2 (by rfl) ⟨564021, by rfl⟩) R1128043
theorem R2005409 : Reach 2005409 := rs (se 2 (by rfl) ⟨752028, by rfl⟩) R1504057
theorem R76457 : Reach 76457 := rs (se 2 (by rfl) ⟨28671, by rfl⟩) R57343
theorem R2962817 : Reach 2962817 := rs (se 2 (by rfl) ⟨1111056, by rfl⟩) R2222113
theorem R5347757 : Reach 5347757 := rs (se 3 (by rfl) ⟨1002704, by rfl⟩) R2005409
theorem R1975211 : Reach 1975211 := rs (se 1 (by rfl) ⟨1481408, by rfl⟩) R2962817
theorem R50971 : Reach 50971 := rs (se 1 (by rfl) ⟨38228, by rfl⟩) R76457
theorem R67961 : Reach 67961 := rs (se 2 (by rfl) ⟨25485, by rfl⟩) R50971
theorem R1316807 : Reach 1316807 := rs (se 1 (by rfl) ⟨987605, by rfl⟩) R1975211
theorem R3565171 : Reach 3565171 := rs (se 1 (by rfl) ⟨2673878, by rfl⟩) R5347757
theorem R4753561 : Reach 4753561 := rs (se 2 (by rfl) ⟨1782585, by rfl⟩) R3565171
theorem R45307 : Reach 45307 := rs (se 1 (by rfl) ⟨33980, by rfl⟩) R67961
theorem R877871 : Reach 877871 := rs (se 1 (by rfl) ⟨658403, by rfl⟩) R1316807
theorem R6338081 : Reach 6338081 := rs (se 2 (by rfl) ⟨2376780, by rfl⟩) R4753561
theorem R585247 : Reach 585247 := rs (se 1 (by rfl) ⟨438935, by rfl⟩) R877871
theorem R780329 : Reach 780329 := rs (se 2 (by rfl) ⟨292623, by rfl⟩) R585247
theorem R4225387 : Reach 4225387 := rs (se 1 (by rfl) ⟨3169040, by rfl⟩) R6338081
theorem R520219 : Reach 520219 := rs (se 1 (by rfl) ⟨390164, by rfl⟩) R780329
theorem R5633849 : Reach 5633849 := rs (se 2 (by rfl) ⟨2112693, by rfl⟩) R4225387
theorem R693625 : Reach 693625 := rs (se 2 (by rfl) ⟨260109, by rfl⟩) R520219
theorem R3755899 : Reach 3755899 := rs (se 1 (by rfl) ⟨2816924, by rfl⟩) R5633849
theorem R924833 : Reach 924833 := rs (se 2 (by rfl) ⟨346812, by rfl⟩) R693625
theorem R5007865 : Reach 5007865 := rs (se 2 (by rfl) ⟨1877949, by rfl⟩) R3755899
theorem R6677153 : Reach 6677153 := rs (se 2 (by rfl) ⟨2503932, by rfl⟩) R5007865
theorem R616555 : Reach 616555 := rs (se 1 (by rfl) ⟨462416, by rfl⟩) R924833
theorem R822073 : Reach 822073 := rs (se 2 (by rfl) ⟨308277, by rfl⟩) R616555
theorem R4451435 : Reach 4451435 := rs (se 1 (by rfl) ⟨3338576, by rfl⟩) R6677153
theorem R1096097 : Reach 1096097 := rs (se 2 (by rfl) ⟨411036, by rfl⟩) R822073
theorem R2967623 : Reach 2967623 := rs (se 1 (by rfl) ⟨2225717, by rfl⟩) R4451435
theorem R2922925 : Reach 2922925 := rs (se 3 (by rfl) ⟨548048, by rfl⟩) R1096097
theorem R1978415 : Reach 1978415 := rs (se 1 (by rfl) ⟨1483811, by rfl⟩) R2967623
theorem R1318943 : Reach 1318943 := rs (se 1 (by rfl) ⟨989207, by rfl⟩) R1978415
theorem R3897233 : Reach 3897233 := rs (se 2 (by rfl) ⟨1461462, by rfl⟩) R2922925
theorem R2598155 : Reach 2598155 := rs (se 1 (by rfl) ⟨1948616, by rfl⟩) R3897233
theorem R879295 : Reach 879295 := rs (se 1 (by rfl) ⟨659471, by rfl⟩) R1318943
theorem R1172393 : Reach 1172393 := rs (se 2 (by rfl) ⟨439647, by rfl⟩) R879295
theorem R1732103 : Reach 1732103 := rs (se 1 (by rfl) ⟨1299077, by rfl⟩) R2598155
theorem R1154735 : Reach 1154735 := rs (se 1 (by rfl) ⟨866051, by rfl⟩) R1732103
theorem R781595 : Reach 781595 := rs (se 1 (by rfl) ⟨586196, by rfl⟩) R1172393
theorem R769823 : Reach 769823 := rs (se 1 (by rfl) ⟨577367, by rfl⟩) R1154735
theorem R521063 : Reach 521063 := rs (se 1 (by rfl) ⟨390797, by rfl⟩) R781595
theorem R347375 : Reach 347375 := rs (se 1 (by rfl) ⟨260531, by rfl⟩) R521063
theorem R513215 : Reach 513215 := rs (se 1 (by rfl) ⟨384911, by rfl⟩) R769823
theorem R231583 : Reach 231583 := rs (se 1 (by rfl) ⟨173687, by rfl⟩) R347375
theorem R342143 : Reach 342143 := rs (se 1 (by rfl) ⟨256607, by rfl⟩) R513215
theorem R308777 : Reach 308777 := rs (se 2 (by rfl) ⟨115791, by rfl⟩) R231583
theorem R228095 : Reach 228095 := rs (se 1 (by rfl) ⟨171071, by rfl⟩) R342143
theorem R823405 : Reach 823405 := rs (se 3 (by rfl) ⟨154388, by rfl⟩) R308777
theorem R152063 : Reach 152063 := rs (se 1 (by rfl) ⟨114047, by rfl⟩) R228095
theorem R101375 : Reach 101375 := rs (se 1 (by rfl) ⟨76031, by rfl⟩) R152063
theorem R1097873 : Reach 1097873 := rs (se 2 (by rfl) ⟨411702, by rfl⟩) R823405
theorem R67583 : Reach 67583 := rs (se 1 (by rfl) ⟨50687, by rfl⟩) R101375
theorem R731915 : Reach 731915 := rs (se 1 (by rfl) ⟨548936, by rfl⟩) R1097873
theorem R45055 : Reach 45055 := rs (se 1 (by rfl) ⟨33791, by rfl⟩) R67583
theorem R487943 : Reach 487943 := rs (se 1 (by rfl) ⟨365957, by rfl⟩) R731915
theorem R325295 : Reach 325295 := rs (se 1 (by rfl) ⟨243971, by rfl⟩) R487943
theorem R216863 : Reach 216863 := rs (se 1 (by rfl) ⟨162647, by rfl⟩) R325295
theorem R144575 : Reach 144575 := rs (se 1 (by rfl) ⟨108431, by rfl⟩) R216863
theorem R96383 : Reach 96383 := rs (se 1 (by rfl) ⟨72287, by rfl⟩) R144575
theorem R64255 : Reach 64255 := rs (se 1 (by rfl) ⟨48191, by rfl⟩) R96383
theorem R85673 : Reach 85673 := rs (se 2 (by rfl) ⟨32127, by rfl⟩) R64255
theorem R57115 : Reach 57115 := rs (se 1 (by rfl) ⟨42836, by rfl⟩) R85673
theorem R76153 : Reach 76153 := rs (se 2 (by rfl) ⟨28557, by rfl⟩) R57115
theorem R101537 : Reach 101537 := rs (se 2 (by rfl) ⟨38076, by rfl⟩) R76153
theorem R67691 : Reach 67691 := rs (se 1 (by rfl) ⟨50768, by rfl⟩) R101537
theorem R45127 : Reach 45127 := rs (se 1 (by rfl) ⟨33845, by rfl⟩) R67691

theorem C0 (j : ℕ) (h1 : 21559 ≤ j) (h2 : j ≤ 22258) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R43119
  · exact R43121
  · exact R43123
  · exact R43125
  · exact R43127
  · exact R43129
  · exact R43131
  · exact R43133
  · exact R43135
  · exact R43137
  · exact R43139
  · exact R43141
  · exact R43143
  · exact R43145
  · exact R43147
  · exact R43149
  · exact R43151
  · exact R43153
  · exact R43155
  · exact R43157
  · exact R43159
  · exact R43161
  · exact R43163
  · exact R43165
  · exact R43167
  · exact R43169
  · exact R43171
  · exact R43173
  · exact R43175
  · exact R43177
  · exact R43179
  · exact R43181
  · exact R43183
  · exact R43185
  · exact R43187
  · exact R43189
  · exact R43191
  · exact R43193
  · exact R43195
  · exact R43197
  · exact R43199
  · exact R43201
  · exact R43203
  · exact R43205
  · exact R43207
  · exact R43209
  · exact R43211
  · exact R43213
  · exact R43215
  · exact R43217
  · exact R43219
  · exact R43221
  · exact R43223
  · exact R43225
  · exact R43227
  · exact R43229
  · exact R43231
  · exact R43233
  · exact R43235
  · exact R43237
  · exact R43239
  · exact R43241
  · exact R43243
  · exact R43245
  · exact R43247
  · exact R43249
  · exact R43251
  · exact R43253
  · exact R43255
  · exact R43257
  · exact R43259
  · exact R43261
  · exact R43263
  · exact R43265
  · exact R43267
  · exact R43269
  · exact R43271
  · exact R43273
  · exact R43275
  · exact R43277
  · exact R43279
  · exact R43281
  · exact R43283
  · exact R43285
  · exact R43287
  · exact R43289
  · exact R43291
  · exact R43293
  · exact R43295
  · exact R43297
  · exact R43299
  · exact R43301
  · exact R43303
  · exact R43305
  · exact R43307
  · exact R43309
  · exact R43311
  · exact R43313
  · exact R43315
  · exact R43317
  · exact R43319
  · exact R43321
  · exact R43323
  · exact R43325
  · exact R43327
  · exact R43329
  · exact R43331
  · exact R43333
  · exact R43335
  · exact R43337
  · exact R43339
  · exact R43341
  · exact R43343
  · exact R43345
  · exact R43347
  · exact R43349
  · exact R43351
  · exact R43353
  · exact R43355
  · exact R43357
  · exact R43359
  · exact R43361
  · exact R43363
  · exact R43365
  · exact R43367
  · exact R43369
  · exact R43371
  · exact R43373
  · exact R43375
  · exact R43377
  · exact R43379
  · exact R43381
  · exact R43383
  · exact R43385
  · exact R43387
  · exact R43389
  · exact R43391
  · exact R43393
  · exact R43395
  · exact R43397
  · exact R43399
  · exact R43401
  · exact R43403
  · exact R43405
  · exact R43407
  · exact R43409
  · exact R43411
  · exact R43413
  · exact R43415
  · exact R43417
  · exact R43419
  · exact R43421
  · exact R43423
  · exact R43425
  · exact R43427
  · exact R43429
  · exact R43431
  · exact R43433
  · exact R43435
  · exact R43437
  · exact R43439
  · exact R43441
  · exact R43443
  · exact R43445
  · exact R43447
  · exact R43449
  · exact R43451
  · exact R43453
  · exact R43455
  · exact R43457
  · exact R43459
  · exact R43461
  · exact R43463
  · exact R43465
  · exact R43467
  · exact R43469
  · exact R43471
  · exact R43473
  · exact R43475
  · exact R43477
  · exact R43479
  · exact R43481
  · exact R43483
  · exact R43485
  · exact R43487
  · exact R43489
  · exact R43491
  · exact R43493
  · exact R43495
  · exact R43497
  · exact R43499
  · exact R43501
  · exact R43503
  · exact R43505
  · exact R43507
  · exact R43509
  · exact R43511
  · exact R43513
  · exact R43515
  · exact R43517
  · exact R43519
  · exact R43521
  · exact R43523
  · exact R43525
  · exact R43527
  · exact R43529
  · exact R43531
  · exact R43533
  · exact R43535
  · exact R43537
  · exact R43539
  · exact R43541
  · exact R43543
  · exact R43545
  · exact R43547
  · exact R43549
  · exact R43551
  · exact R43553
  · exact R43555
  · exact R43557
  · exact R43559
  · exact R43561
  · exact R43563
  · exact R43565
  · exact R43567
  · exact R43569
  · exact R43571
  · exact R43573
  · exact R43575
  · exact R43577
  · exact R43579
  · exact R43581
  · exact R43583
  · exact R43585
  · exact R43587
  · exact R43589
  · exact R43591
  · exact R43593
  · exact R43595
  · exact R43597
  · exact R43599
  · exact R43601
  · exact R43603
  · exact R43605
  · exact R43607
  · exact R43609
  · exact R43611
  · exact R43613
  · exact R43615
  · exact R43617
  · exact R43619
  · exact R43621
  · exact R43623
  · exact R43625
  · exact R43627
  · exact R43629
  · exact R43631
  · exact R43633
  · exact R43635
  · exact R43637
  · exact R43639
  · exact R43641
  · exact R43643
  · exact R43645
  · exact R43647
  · exact R43649
  · exact R43651
  · exact R43653
  · exact R43655
  · exact R43657
  · exact R43659
  · exact R43661
  · exact R43663
  · exact R43665
  · exact R43667
  · exact R43669
  · exact R43671
  · exact R43673
  · exact R43675
  · exact R43677
  · exact R43679
  · exact R43681
  · exact R43683
  · exact R43685
  · exact R43687
  · exact R43689
  · exact R43691
  · exact R43693
  · exact R43695
  · exact R43697
  · exact R43699
  · exact R43701
  · exact R43703
  · exact R43705
  · exact R43707
  · exact R43709
  · exact R43711
  · exact R43713
  · exact R43715
  · exact R43717
  · exact R43719
  · exact R43721
  · exact R43723
  · exact R43725
  · exact R43727
  · exact R43729
  · exact R43731
  · exact R43733
  · exact R43735
  · exact R43737
  · exact R43739
  · exact R43741
  · exact R43743
  · exact R43745
  · exact R43747
  · exact R43749
  · exact R43751
  · exact R43753
  · exact R43755
  · exact R43757
  · exact R43759
  · exact R43761
  · exact R43763
  · exact R43765
  · exact R43767
  · exact R43769
  · exact R43771
  · exact R43773
  · exact R43775
  · exact R43777
  · exact R43779
  · exact R43781
  · exact R43783
  · exact R43785
  · exact R43787
  · exact R43789
  · exact R43791
  · exact R43793
  · exact R43795
  · exact R43797
  · exact R43799
  · exact R43801
  · exact R43803
  · exact R43805
  · exact R43807
  · exact R43809
  · exact R43811
  · exact R43813
  · exact R43815
  · exact R43817
  · exact R43819
  · exact R43821
  · exact R43823
  · exact R43825
  · exact R43827
  · exact R43829
  · exact R43831
  · exact R43833
  · exact R43835
  · exact R43837
  · exact R43839
  · exact R43841
  · exact R43843
  · exact R43845
  · exact R43847
  · exact R43849
  · exact R43851
  · exact R43853
  · exact R43855
  · exact R43857
  · exact R43859
  · exact R43861
  · exact R43863
  · exact R43865
  · exact R43867
  · exact R43869
  · exact R43871
  · exact R43873
  · exact R43875
  · exact R43877
  · exact R43879
  · exact R43881
  · exact R43883
  · exact R43885
  · exact R43887
  · exact R43889
  · exact R43891
  · exact R43893
  · exact R43895
  · exact R43897
  · exact R43899
  · exact R43901
  · exact R43903
  · exact R43905
  · exact R43907
  · exact R43909
  · exact R43911
  · exact R43913
  · exact R43915
  · exact R43917
  · exact R43919
  · exact R43921
  · exact R43923
  · exact R43925
  · exact R43927
  · exact R43929
  · exact R43931
  · exact R43933
  · exact R43935
  · exact R43937
  · exact R43939
  · exact R43941
  · exact R43943
  · exact R43945
  · exact R43947
  · exact R43949
  · exact R43951
  · exact R43953
  · exact R43955
  · exact R43957
  · exact R43959
  · exact R43961
  · exact R43963
  · exact R43965
  · exact R43967
  · exact R43969
  · exact R43971
  · exact R43973
  · exact R43975
  · exact R43977
  · exact R43979
  · exact R43981
  · exact R43983
  · exact R43985
  · exact R43987
  · exact R43989
  · exact R43991
  · exact R43993
  · exact R43995
  · exact R43997
  · exact R43999
  · exact R44001
  · exact R44003
  · exact R44005
  · exact R44007
  · exact R44009
  · exact R44011
  · exact R44013
  · exact R44015
  · exact R44017
  · exact R44019
  · exact R44021
  · exact R44023
  · exact R44025
  · exact R44027
  · exact R44029
  · exact R44031
  · exact R44033
  · exact R44035
  · exact R44037
  · exact R44039
  · exact R44041
  · exact R44043
  · exact R44045
  · exact R44047
  · exact R44049
  · exact R44051
  · exact R44053
  · exact R44055
  · exact R44057
  · exact R44059
  · exact R44061
  · exact R44063
  · exact R44065
  · exact R44067
  · exact R44069
  · exact R44071
  · exact R44073
  · exact R44075
  · exact R44077
  · exact R44079
  · exact R44081
  · exact R44083
  · exact R44085
  · exact R44087
  · exact R44089
  · exact R44091
  · exact R44093
  · exact R44095
  · exact R44097
  · exact R44099
  · exact R44101
  · exact R44103
  · exact R44105
  · exact R44107
  · exact R44109
  · exact R44111
  · exact R44113
  · exact R44115
  · exact R44117
  · exact R44119
  · exact R44121
  · exact R44123
  · exact R44125
  · exact R44127
  · exact R44129
  · exact R44131
  · exact R44133
  · exact R44135
  · exact R44137
  · exact R44139
  · exact R44141
  · exact R44143
  · exact R44145
  · exact R44147
  · exact R44149
  · exact R44151
  · exact R44153
  · exact R44155
  · exact R44157
  · exact R44159
  · exact R44161
  · exact R44163
  · exact R44165
  · exact R44167
  · exact R44169
  · exact R44171
  · exact R44173
  · exact R44175
  · exact R44177
  · exact R44179
  · exact R44181
  · exact R44183
  · exact R44185
  · exact R44187
  · exact R44189
  · exact R44191
  · exact R44193
  · exact R44195
  · exact R44197
  · exact R44199
  · exact R44201
  · exact R44203
  · exact R44205
  · exact R44207
  · exact R44209
  · exact R44211
  · exact R44213
  · exact R44215
  · exact R44217
  · exact R44219
  · exact R44221
  · exact R44223
  · exact R44225
  · exact R44227
  · exact R44229
  · exact R44231
  · exact R44233
  · exact R44235
  · exact R44237
  · exact R44239
  · exact R44241
  · exact R44243
  · exact R44245
  · exact R44247
  · exact R44249
  · exact R44251
  · exact R44253
  · exact R44255
  · exact R44257
  · exact R44259
  · exact R44261
  · exact R44263
  · exact R44265
  · exact R44267
  · exact R44269
  · exact R44271
  · exact R44273
  · exact R44275
  · exact R44277
  · exact R44279
  · exact R44281
  · exact R44283
  · exact R44285
  · exact R44287
  · exact R44289
  · exact R44291
  · exact R44293
  · exact R44295
  · exact R44297
  · exact R44299
  · exact R44301
  · exact R44303
  · exact R44305
  · exact R44307
  · exact R44309
  · exact R44311
  · exact R44313
  · exact R44315
  · exact R44317
  · exact R44319
  · exact R44321
  · exact R44323
  · exact R44325
  · exact R44327
  · exact R44329
  · exact R44331
  · exact R44333
  · exact R44335
  · exact R44337
  · exact R44339
  · exact R44341
  · exact R44343
  · exact R44345
  · exact R44347
  · exact R44349
  · exact R44351
  · exact R44353
  · exact R44355
  · exact R44357
  · exact R44359
  · exact R44361
  · exact R44363
  · exact R44365
  · exact R44367
  · exact R44369
  · exact R44371
  · exact R44373
  · exact R44375
  · exact R44377
  · exact R44379
  · exact R44381
  · exact R44383
  · exact R44385
  · exact R44387
  · exact R44389
  · exact R44391
  · exact R44393
  · exact R44395
  · exact R44397
  · exact R44399
  · exact R44401
  · exact R44403
  · exact R44405
  · exact R44407
  · exact R44409
  · exact R44411
  · exact R44413
  · exact R44415
  · exact R44417
  · exact R44419
  · exact R44421
  · exact R44423
  · exact R44425
  · exact R44427
  · exact R44429
  · exact R44431
  · exact R44433
  · exact R44435
  · exact R44437
  · exact R44439
  · exact R44441
  · exact R44443
  · exact R44445
  · exact R44447
  · exact R44449
  · exact R44451
  · exact R44453
  · exact R44455
  · exact R44457
  · exact R44459
  · exact R44461
  · exact R44463
  · exact R44465
  · exact R44467
  · exact R44469
  · exact R44471
  · exact R44473
  · exact R44475
  · exact R44477
  · exact R44479
  · exact R44481
  · exact R44483
  · exact R44485
  · exact R44487
  · exact R44489
  · exact R44491
  · exact R44493
  · exact R44495
  · exact R44497
  · exact R44499
  · exact R44501
  · exact R44503
  · exact R44505
  · exact R44507
  · exact R44509
  · exact R44511
  · exact R44513
  · exact R44515
  · exact R44517

theorem C1 (j : ℕ) (h1 : 22259 ≤ j) (h2 : j ≤ 22958) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R44519
  · exact R44521
  · exact R44523
  · exact R44525
  · exact R44527
  · exact R44529
  · exact R44531
  · exact R44533
  · exact R44535
  · exact R44537
  · exact R44539
  · exact R44541
  · exact R44543
  · exact R44545
  · exact R44547
  · exact R44549
  · exact R44551
  · exact R44553
  · exact R44555
  · exact R44557
  · exact R44559
  · exact R44561
  · exact R44563
  · exact R44565
  · exact R44567
  · exact R44569
  · exact R44571
  · exact R44573
  · exact R44575
  · exact R44577
  · exact R44579
  · exact R44581
  · exact R44583
  · exact R44585
  · exact R44587
  · exact R44589
  · exact R44591
  · exact R44593
  · exact R44595
  · exact R44597
  · exact R44599
  · exact R44601
  · exact R44603
  · exact R44605
  · exact R44607
  · exact R44609
  · exact R44611
  · exact R44613
  · exact R44615
  · exact R44617
  · exact R44619
  · exact R44621
  · exact R44623
  · exact R44625
  · exact R44627
  · exact R44629
  · exact R44631
  · exact R44633
  · exact R44635
  · exact R44637
  · exact R44639
  · exact R44641
  · exact R44643
  · exact R44645
  · exact R44647
  · exact R44649
  · exact R44651
  · exact R44653
  · exact R44655
  · exact R44657
  · exact R44659
  · exact R44661
  · exact R44663
  · exact R44665
  · exact R44667
  · exact R44669
  · exact R44671
  · exact R44673
  · exact R44675
  · exact R44677
  · exact R44679
  · exact R44681
  · exact R44683
  · exact R44685
  · exact R44687
  · exact R44689
  · exact R44691
  · exact R44693
  · exact R44695
  · exact R44697
  · exact R44699
  · exact R44701
  · exact R44703
  · exact R44705
  · exact R44707
  · exact R44709
  · exact R44711
  · exact R44713
  · exact R44715
  · exact R44717
  · exact R44719
  · exact R44721
  · exact R44723
  · exact R44725
  · exact R44727
  · exact R44729
  · exact R44731
  · exact R44733
  · exact R44735
  · exact R44737
  · exact R44739
  · exact R44741
  · exact R44743
  · exact R44745
  · exact R44747
  · exact R44749
  · exact R44751
  · exact R44753
  · exact R44755
  · exact R44757
  · exact R44759
  · exact R44761
  · exact R44763
  · exact R44765
  · exact R44767
  · exact R44769
  · exact R44771
  · exact R44773
  · exact R44775
  · exact R44777
  · exact R44779
  · exact R44781
  · exact R44783
  · exact R44785
  · exact R44787
  · exact R44789
  · exact R44791
  · exact R44793
  · exact R44795
  · exact R44797
  · exact R44799
  · exact R44801
  · exact R44803
  · exact R44805
  · exact R44807
  · exact R44809
  · exact R44811
  · exact R44813
  · exact R44815
  · exact R44817
  · exact R44819
  · exact R44821
  · exact R44823
  · exact R44825
  · exact R44827
  · exact R44829
  · exact R44831
  · exact R44833
  · exact R44835
  · exact R44837
  · exact R44839
  · exact R44841
  · exact R44843
  · exact R44845
  · exact R44847
  · exact R44849
  · exact R44851
  · exact R44853
  · exact R44855
  · exact R44857
  · exact R44859
  · exact R44861
  · exact R44863
  · exact R44865
  · exact R44867
  · exact R44869
  · exact R44871
  · exact R44873
  · exact R44875
  · exact R44877
  · exact R44879
  · exact R44881
  · exact R44883
  · exact R44885
  · exact R44887
  · exact R44889
  · exact R44891
  · exact R44893
  · exact R44895
  · exact R44897
  · exact R44899
  · exact R44901
  · exact R44903
  · exact R44905
  · exact R44907
  · exact R44909
  · exact R44911
  · exact R44913
  · exact R44915
  · exact R44917
  · exact R44919
  · exact R44921
  · exact R44923
  · exact R44925
  · exact R44927
  · exact R44929
  · exact R44931
  · exact R44933
  · exact R44935
  · exact R44937
  · exact R44939
  · exact R44941
  · exact R44943
  · exact R44945
  · exact R44947
  · exact R44949
  · exact R44951
  · exact R44953
  · exact R44955
  · exact R44957
  · exact R44959
  · exact R44961
  · exact R44963
  · exact R44965
  · exact R44967
  · exact R44969
  · exact R44971
  · exact R44973
  · exact R44975
  · exact R44977
  · exact R44979
  · exact R44981
  · exact R44983
  · exact R44985
  · exact R44987
  · exact R44989
  · exact R44991
  · exact R44993
  · exact R44995
  · exact R44997
  · exact R44999
  · exact R45001
  · exact R45003
  · exact R45005
  · exact R45007
  · exact R45009
  · exact R45011
  · exact R45013
  · exact R45015
  · exact R45017
  · exact R45019
  · exact R45021
  · exact R45023
  · exact R45025
  · exact R45027
  · exact R45029
  · exact R45031
  · exact R45033
  · exact R45035
  · exact R45037
  · exact R45039
  · exact R45041
  · exact R45043
  · exact R45045
  · exact R45047
  · exact R45049
  · exact R45051
  · exact R45053
  · exact R45055
  · exact R45057
  · exact R45059
  · exact R45061
  · exact R45063
  · exact R45065
  · exact R45067
  · exact R45069
  · exact R45071
  · exact R45073
  · exact R45075
  · exact R45077
  · exact R45079
  · exact R45081
  · exact R45083
  · exact R45085
  · exact R45087
  · exact R45089
  · exact R45091
  · exact R45093
  · exact R45095
  · exact R45097
  · exact R45099
  · exact R45101
  · exact R45103
  · exact R45105
  · exact R45107
  · exact R45109
  · exact R45111
  · exact R45113
  · exact R45115
  · exact R45117
  · exact R45119
  · exact R45121
  · exact R45123
  · exact R45125
  · exact R45127
  · exact R45129
  · exact R45131
  · exact R45133
  · exact R45135
  · exact R45137
  · exact R45139
  · exact R45141
  · exact R45143
  · exact R45145
  · exact R45147
  · exact R45149
  · exact R45151
  · exact R45153
  · exact R45155
  · exact R45157
  · exact R45159
  · exact R45161
  · exact R45163
  · exact R45165
  · exact R45167
  · exact R45169
  · exact R45171
  · exact R45173
  · exact R45175
  · exact R45177
  · exact R45179
  · exact R45181
  · exact R45183
  · exact R45185
  · exact R45187
  · exact R45189
  · exact R45191
  · exact R45193
  · exact R45195
  · exact R45197
  · exact R45199
  · exact R45201
  · exact R45203
  · exact R45205
  · exact R45207
  · exact R45209
  · exact R45211
  · exact R45213
  · exact R45215
  · exact R45217
  · exact R45219
  · exact R45221
  · exact R45223
  · exact R45225
  · exact R45227
  · exact R45229
  · exact R45231
  · exact R45233
  · exact R45235
  · exact R45237
  · exact R45239
  · exact R45241
  · exact R45243
  · exact R45245
  · exact R45247
  · exact R45249
  · exact R45251
  · exact R45253
  · exact R45255
  · exact R45257
  · exact R45259
  · exact R45261
  · exact R45263
  · exact R45265
  · exact R45267
  · exact R45269
  · exact R45271
  · exact R45273
  · exact R45275
  · exact R45277
  · exact R45279
  · exact R45281
  · exact R45283
  · exact R45285
  · exact R45287
  · exact R45289
  · exact R45291
  · exact R45293
  · exact R45295
  · exact R45297
  · exact R45299
  · exact R45301
  · exact R45303
  · exact R45305
  · exact R45307
  · exact R45309
  · exact R45311
  · exact R45313
  · exact R45315
  · exact R45317
  · exact R45319
  · exact R45321
  · exact R45323
  · exact R45325
  · exact R45327
  · exact R45329
  · exact R45331
  · exact R45333
  · exact R45335
  · exact R45337
  · exact R45339
  · exact R45341
  · exact R45343
  · exact R45345
  · exact R45347
  · exact R45349
  · exact R45351
  · exact R45353
  · exact R45355
  · exact R45357
  · exact R45359
  · exact R45361
  · exact R45363
  · exact R45365
  · exact R45367
  · exact R45369
  · exact R45371
  · exact R45373
  · exact R45375
  · exact R45377
  · exact R45379
  · exact R45381
  · exact R45383
  · exact R45385
  · exact R45387
  · exact R45389
  · exact R45391
  · exact R45393
  · exact R45395
  · exact R45397
  · exact R45399
  · exact R45401
  · exact R45403
  · exact R45405
  · exact R45407
  · exact R45409
  · exact R45411
  · exact R45413
  · exact R45415
  · exact R45417
  · exact R45419
  · exact R45421
  · exact R45423
  · exact R45425
  · exact R45427
  · exact R45429
  · exact R45431
  · exact R45433
  · exact R45435
  · exact R45437
  · exact R45439
  · exact R45441
  · exact R45443
  · exact R45445
  · exact R45447
  · exact R45449
  · exact R45451
  · exact R45453
  · exact R45455
  · exact R45457
  · exact R45459
  · exact R45461
  · exact R45463
  · exact R45465
  · exact R45467
  · exact R45469
  · exact R45471
  · exact R45473
  · exact R45475
  · exact R45477
  · exact R45479
  · exact R45481
  · exact R45483
  · exact R45485
  · exact R45487
  · exact R45489
  · exact R45491
  · exact R45493
  · exact R45495
  · exact R45497
  · exact R45499
  · exact R45501
  · exact R45503
  · exact R45505
  · exact R45507
  · exact R45509
  · exact R45511
  · exact R45513
  · exact R45515
  · exact R45517
  · exact R45519
  · exact R45521
  · exact R45523
  · exact R45525
  · exact R45527
  · exact R45529
  · exact R45531
  · exact R45533
  · exact R45535
  · exact R45537
  · exact R45539
  · exact R45541
  · exact R45543
  · exact R45545
  · exact R45547
  · exact R45549
  · exact R45551
  · exact R45553
  · exact R45555
  · exact R45557
  · exact R45559
  · exact R45561
  · exact R45563
  · exact R45565
  · exact R45567
  · exact R45569
  · exact R45571
  · exact R45573
  · exact R45575
  · exact R45577
  · exact R45579
  · exact R45581
  · exact R45583
  · exact R45585
  · exact R45587
  · exact R45589
  · exact R45591
  · exact R45593
  · exact R45595
  · exact R45597
  · exact R45599
  · exact R45601
  · exact R45603
  · exact R45605
  · exact R45607
  · exact R45609
  · exact R45611
  · exact R45613
  · exact R45615
  · exact R45617
  · exact R45619
  · exact R45621
  · exact R45623
  · exact R45625
  · exact R45627
  · exact R45629
  · exact R45631
  · exact R45633
  · exact R45635
  · exact R45637
  · exact R45639
  · exact R45641
  · exact R45643
  · exact R45645
  · exact R45647
  · exact R45649
  · exact R45651
  · exact R45653
  · exact R45655
  · exact R45657
  · exact R45659
  · exact R45661
  · exact R45663
  · exact R45665
  · exact R45667
  · exact R45669
  · exact R45671
  · exact R45673
  · exact R45675
  · exact R45677
  · exact R45679
  · exact R45681
  · exact R45683
  · exact R45685
  · exact R45687
  · exact R45689
  · exact R45691
  · exact R45693
  · exact R45695
  · exact R45697
  · exact R45699
  · exact R45701
  · exact R45703
  · exact R45705
  · exact R45707
  · exact R45709
  · exact R45711
  · exact R45713
  · exact R45715
  · exact R45717
  · exact R45719
  · exact R45721
  · exact R45723
  · exact R45725
  · exact R45727
  · exact R45729
  · exact R45731
  · exact R45733
  · exact R45735
  · exact R45737
  · exact R45739
  · exact R45741
  · exact R45743
  · exact R45745
  · exact R45747
  · exact R45749
  · exact R45751
  · exact R45753
  · exact R45755
  · exact R45757
  · exact R45759
  · exact R45761
  · exact R45763
  · exact R45765
  · exact R45767
  · exact R45769
  · exact R45771
  · exact R45773
  · exact R45775
  · exact R45777
  · exact R45779
  · exact R45781
  · exact R45783
  · exact R45785
  · exact R45787
  · exact R45789
  · exact R45791
  · exact R45793
  · exact R45795
  · exact R45797
  · exact R45799
  · exact R45801
  · exact R45803
  · exact R45805
  · exact R45807
  · exact R45809
  · exact R45811
  · exact R45813
  · exact R45815
  · exact R45817
  · exact R45819
  · exact R45821
  · exact R45823
  · exact R45825
  · exact R45827
  · exact R45829
  · exact R45831
  · exact R45833
  · exact R45835
  · exact R45837
  · exact R45839
  · exact R45841
  · exact R45843
  · exact R45845
  · exact R45847
  · exact R45849
  · exact R45851
  · exact R45853
  · exact R45855
  · exact R45857
  · exact R45859
  · exact R45861
  · exact R45863
  · exact R45865
  · exact R45867
  · exact R45869
  · exact R45871
  · exact R45873
  · exact R45875
  · exact R45877
  · exact R45879
  · exact R45881
  · exact R45883
  · exact R45885
  · exact R45887
  · exact R45889
  · exact R45891
  · exact R45893
  · exact R45895
  · exact R45897
  · exact R45899
  · exact R45901
  · exact R45903
  · exact R45905
  · exact R45907
  · exact R45909
  · exact R45911
  · exact R45913
  · exact R45915
  · exact R45917

theorem C2 (j : ℕ) (h1 : 22959 ≤ j) (h2 : j ≤ 23558) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R45919
  · exact R45921
  · exact R45923
  · exact R45925
  · exact R45927
  · exact R45929
  · exact R45931
  · exact R45933
  · exact R45935
  · exact R45937
  · exact R45939
  · exact R45941
  · exact R45943
  · exact R45945
  · exact R45947
  · exact R45949
  · exact R45951
  · exact R45953
  · exact R45955
  · exact R45957
  · exact R45959
  · exact R45961
  · exact R45963
  · exact R45965
  · exact R45967
  · exact R45969
  · exact R45971
  · exact R45973
  · exact R45975
  · exact R45977
  · exact R45979
  · exact R45981
  · exact R45983
  · exact R45985
  · exact R45987
  · exact R45989
  · exact R45991
  · exact R45993
  · exact R45995
  · exact R45997
  · exact R45999
  · exact R46001
  · exact R46003
  · exact R46005
  · exact R46007
  · exact R46009
  · exact R46011
  · exact R46013
  · exact R46015
  · exact R46017
  · exact R46019
  · exact R46021
  · exact R46023
  · exact R46025
  · exact R46027
  · exact R46029
  · exact R46031
  · exact R46033
  · exact R46035
  · exact R46037
  · exact R46039
  · exact R46041
  · exact R46043
  · exact R46045
  · exact R46047
  · exact R46049
  · exact R46051
  · exact R46053
  · exact R46055
  · exact R46057
  · exact R46059
  · exact R46061
  · exact R46063
  · exact R46065
  · exact R46067
  · exact R46069
  · exact R46071
  · exact R46073
  · exact R46075
  · exact R46077
  · exact R46079
  · exact R46081
  · exact R46083
  · exact R46085
  · exact R46087
  · exact R46089
  · exact R46091
  · exact R46093
  · exact R46095
  · exact R46097
  · exact R46099
  · exact R46101
  · exact R46103
  · exact R46105
  · exact R46107
  · exact R46109
  · exact R46111
  · exact R46113
  · exact R46115
  · exact R46117
  · exact R46119
  · exact R46121
  · exact R46123
  · exact R46125
  · exact R46127
  · exact R46129
  · exact R46131
  · exact R46133
  · exact R46135
  · exact R46137
  · exact R46139
  · exact R46141
  · exact R46143
  · exact R46145
  · exact R46147
  · exact R46149
  · exact R46151
  · exact R46153
  · exact R46155
  · exact R46157
  · exact R46159
  · exact R46161
  · exact R46163
  · exact R46165
  · exact R46167
  · exact R46169
  · exact R46171
  · exact R46173
  · exact R46175
  · exact R46177
  · exact R46179
  · exact R46181
  · exact R46183
  · exact R46185
  · exact R46187
  · exact R46189
  · exact R46191
  · exact R46193
  · exact R46195
  · exact R46197
  · exact R46199
  · exact R46201
  · exact R46203
  · exact R46205
  · exact R46207
  · exact R46209
  · exact R46211
  · exact R46213
  · exact R46215
  · exact R46217
  · exact R46219
  · exact R46221
  · exact R46223
  · exact R46225
  · exact R46227
  · exact R46229
  · exact R46231
  · exact R46233
  · exact R46235
  · exact R46237
  · exact R46239
  · exact R46241
  · exact R46243
  · exact R46245
  · exact R46247
  · exact R46249
  · exact R46251
  · exact R46253
  · exact R46255
  · exact R46257
  · exact R46259
  · exact R46261
  · exact R46263
  · exact R46265
  · exact R46267
  · exact R46269
  · exact R46271
  · exact R46273
  · exact R46275
  · exact R46277
  · exact R46279
  · exact R46281
  · exact R46283
  · exact R46285
  · exact R46287
  · exact R46289
  · exact R46291
  · exact R46293
  · exact R46295
  · exact R46297
  · exact R46299
  · exact R46301
  · exact R46303
  · exact R46305
  · exact R46307
  · exact R46309
  · exact R46311
  · exact R46313
  · exact R46315
  · exact R46317
  · exact R46319
  · exact R46321
  · exact R46323
  · exact R46325
  · exact R46327
  · exact R46329
  · exact R46331
  · exact R46333
  · exact R46335
  · exact R46337
  · exact R46339
  · exact R46341
  · exact R46343
  · exact R46345
  · exact R46347
  · exact R46349
  · exact R46351
  · exact R46353
  · exact R46355
  · exact R46357
  · exact R46359
  · exact R46361
  · exact R46363
  · exact R46365
  · exact R46367
  · exact R46369
  · exact R46371
  · exact R46373
  · exact R46375
  · exact R46377
  · exact R46379
  · exact R46381
  · exact R46383
  · exact R46385
  · exact R46387
  · exact R46389
  · exact R46391
  · exact R46393
  · exact R46395
  · exact R46397
  · exact R46399
  · exact R46401
  · exact R46403
  · exact R46405
  · exact R46407
  · exact R46409
  · exact R46411
  · exact R46413
  · exact R46415
  · exact R46417
  · exact R46419
  · exact R46421
  · exact R46423
  · exact R46425
  · exact R46427
  · exact R46429
  · exact R46431
  · exact R46433
  · exact R46435
  · exact R46437
  · exact R46439
  · exact R46441
  · exact R46443
  · exact R46445
  · exact R46447
  · exact R46449
  · exact R46451
  · exact R46453
  · exact R46455
  · exact R46457
  · exact R46459
  · exact R46461
  · exact R46463
  · exact R46465
  · exact R46467
  · exact R46469
  · exact R46471
  · exact R46473
  · exact R46475
  · exact R46477
  · exact R46479
  · exact R46481
  · exact R46483
  · exact R46485
  · exact R46487
  · exact R46489
  · exact R46491
  · exact R46493
  · exact R46495
  · exact R46497
  · exact R46499
  · exact R46501
  · exact R46503
  · exact R46505
  · exact R46507
  · exact R46509
  · exact R46511
  · exact R46513
  · exact R46515
  · exact R46517
  · exact R46519
  · exact R46521
  · exact R46523
  · exact R46525
  · exact R46527
  · exact R46529
  · exact R46531
  · exact R46533
  · exact R46535
  · exact R46537
  · exact R46539
  · exact R46541
  · exact R46543
  · exact R46545
  · exact R46547
  · exact R46549
  · exact R46551
  · exact R46553
  · exact R46555
  · exact R46557
  · exact R46559
  · exact R46561
  · exact R46563
  · exact R46565
  · exact R46567
  · exact R46569
  · exact R46571
  · exact R46573
  · exact R46575
  · exact R46577
  · exact R46579
  · exact R46581
  · exact R46583
  · exact R46585
  · exact R46587
  · exact R46589
  · exact R46591
  · exact R46593
  · exact R46595
  · exact R46597
  · exact R46599
  · exact R46601
  · exact R46603
  · exact R46605
  · exact R46607
  · exact R46609
  · exact R46611
  · exact R46613
  · exact R46615
  · exact R46617
  · exact R46619
  · exact R46621
  · exact R46623
  · exact R46625
  · exact R46627
  · exact R46629
  · exact R46631
  · exact R46633
  · exact R46635
  · exact R46637
  · exact R46639
  · exact R46641
  · exact R46643
  · exact R46645
  · exact R46647
  · exact R46649
  · exact R46651
  · exact R46653
  · exact R46655
  · exact R46657
  · exact R46659
  · exact R46661
  · exact R46663
  · exact R46665
  · exact R46667
  · exact R46669
  · exact R46671
  · exact R46673
  · exact R46675
  · exact R46677
  · exact R46679
  · exact R46681
  · exact R46683
  · exact R46685
  · exact R46687
  · exact R46689
  · exact R46691
  · exact R46693
  · exact R46695
  · exact R46697
  · exact R46699
  · exact R46701
  · exact R46703
  · exact R46705
  · exact R46707
  · exact R46709
  · exact R46711
  · exact R46713
  · exact R46715
  · exact R46717
  · exact R46719
  · exact R46721
  · exact R46723
  · exact R46725
  · exact R46727
  · exact R46729
  · exact R46731
  · exact R46733
  · exact R46735
  · exact R46737
  · exact R46739
  · exact R46741
  · exact R46743
  · exact R46745
  · exact R46747
  · exact R46749
  · exact R46751
  · exact R46753
  · exact R46755
  · exact R46757
  · exact R46759
  · exact R46761
  · exact R46763
  · exact R46765
  · exact R46767
  · exact R46769
  · exact R46771
  · exact R46773
  · exact R46775
  · exact R46777
  · exact R46779
  · exact R46781
  · exact R46783
  · exact R46785
  · exact R46787
  · exact R46789
  · exact R46791
  · exact R46793
  · exact R46795
  · exact R46797
  · exact R46799
  · exact R46801
  · exact R46803
  · exact R46805
  · exact R46807
  · exact R46809
  · exact R46811
  · exact R46813
  · exact R46815
  · exact R46817
  · exact R46819
  · exact R46821
  · exact R46823
  · exact R46825
  · exact R46827
  · exact R46829
  · exact R46831
  · exact R46833
  · exact R46835
  · exact R46837
  · exact R46839
  · exact R46841
  · exact R46843
  · exact R46845
  · exact R46847
  · exact R46849
  · exact R46851
  · exact R46853
  · exact R46855
  · exact R46857
  · exact R46859
  · exact R46861
  · exact R46863
  · exact R46865
  · exact R46867
  · exact R46869
  · exact R46871
  · exact R46873
  · exact R46875
  · exact R46877
  · exact R46879
  · exact R46881
  · exact R46883
  · exact R46885
  · exact R46887
  · exact R46889
  · exact R46891
  · exact R46893
  · exact R46895
  · exact R46897
  · exact R46899
  · exact R46901
  · exact R46903
  · exact R46905
  · exact R46907
  · exact R46909
  · exact R46911
  · exact R46913
  · exact R46915
  · exact R46917
  · exact R46919
  · exact R46921
  · exact R46923
  · exact R46925
  · exact R46927
  · exact R46929
  · exact R46931
  · exact R46933
  · exact R46935
  · exact R46937
  · exact R46939
  · exact R46941
  · exact R46943
  · exact R46945
  · exact R46947
  · exact R46949
  · exact R46951
  · exact R46953
  · exact R46955
  · exact R46957
  · exact R46959
  · exact R46961
  · exact R46963
  · exact R46965
  · exact R46967
  · exact R46969
  · exact R46971
  · exact R46973
  · exact R46975
  · exact R46977
  · exact R46979
  · exact R46981
  · exact R46983
  · exact R46985
  · exact R46987
  · exact R46989
  · exact R46991
  · exact R46993
  · exact R46995
  · exact R46997
  · exact R46999
  · exact R47001
  · exact R47003
  · exact R47005
  · exact R47007
  · exact R47009
  · exact R47011
  · exact R47013
  · exact R47015
  · exact R47017
  · exact R47019
  · exact R47021
  · exact R47023
  · exact R47025
  · exact R47027
  · exact R47029
  · exact R47031
  · exact R47033
  · exact R47035
  · exact R47037
  · exact R47039
  · exact R47041
  · exact R47043
  · exact R47045
  · exact R47047
  · exact R47049
  · exact R47051
  · exact R47053
  · exact R47055
  · exact R47057
  · exact R47059
  · exact R47061
  · exact R47063
  · exact R47065
  · exact R47067
  · exact R47069
  · exact R47071
  · exact R47073
  · exact R47075
  · exact R47077
  · exact R47079
  · exact R47081
  · exact R47083
  · exact R47085
  · exact R47087
  · exact R47089
  · exact R47091
  · exact R47093
  · exact R47095
  · exact R47097
  · exact R47099
  · exact R47101
  · exact R47103
  · exact R47105
  · exact R47107
  · exact R47109
  · exact R47111
  · exact R47113
  · exact R47115
  · exact R47117

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 47118) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 43118 with hlo | hlo
  · exact syracuse_reaches_one_below_43118 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 22259 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 22959 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
