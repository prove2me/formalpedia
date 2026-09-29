-- Prove2me | solution 1 for syracuse_reaches_one_below_63123
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T06:07:08.476933+00:00
-- url     : https://prove2.me/submissions/df3f6104-6594-4891-a863-82205f42016f

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_59122

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 59121) : Reach n :=
  syracuse_reaches_one_below_59122 n h1 h2 h3
theorem R65593 : Reach 65593 := rs (se 2 (by rfl) ⟨24597, by rfl⟩) (B 49195 (by norm_num) ⟨24597, by rfl⟩ (by norm_num))
theorem R131213 : Reach 131213 := rs (se 3 (by rfl) ⟨24602, by rfl⟩) (B 49205 (by norm_num) ⟨24602, by rfl⟩ (by norm_num))
theorem R65777 : Reach 65777 := rs (se 2 (by rfl) ⟨24666, by rfl⟩) (B 49333 (by norm_num) ⟨24666, by rfl⟩ (by norm_num))
theorem R131357 : Reach 131357 := rs (se 3 (by rfl) ⟨24629, by rfl⟩) (B 49259 (by norm_num) ⟨24629, by rfl⟩ (by norm_num))
theorem R196933 : Reach 196933 := rs (se 4 (by rfl) ⟨18462, by rfl⟩) (B 36925 (by norm_num) ⟨18462, by rfl⟩ (by norm_num))
theorem R98749 : Reach 98749 := rs (se 3 (by rfl) ⟨18515, by rfl⟩) (B 37031 (by norm_num) ⟨18515, by rfl⟩ (by norm_num))
theorem R131765 : Reach 131765 := rs (se 5 (by rfl) ⟨6176, by rfl⟩) (B 12353 (by norm_num) ⟨6176, by rfl⟩ (by norm_num))
theorem R262885 : Reach 262885 := rs (se 4 (by rfl) ⟨24645, by rfl⟩) (B 49291 (by norm_num) ⟨24645, by rfl⟩ (by norm_num))
theorem R66529 : Reach 66529 := rs (se 2 (by rfl) ⟨24948, by rfl⟩) (B 49897 (by norm_num) ⟨24948, by rfl⟩ (by norm_num))
theorem R66541 : Reach 66541 := rs (se 3 (by rfl) ⟨12476, by rfl⟩) (B 24953 (by norm_num) ⟨12476, by rfl⟩ (by norm_num))
theorem R132101 : Reach 132101 := rs (se 4 (by rfl) ⟨12384, by rfl⟩) (B 24769 (by norm_num) ⟨12384, by rfl⟩ (by norm_num))
theorem R66577 : Reach 66577 := rs (se 2 (by rfl) ⟨24966, by rfl⟩) (B 49933 (by norm_num) ⟨24966, by rfl⟩ (by norm_num))
theorem R66601 : Reach 66601 := rs (se 2 (by rfl) ⟨24975, by rfl⟩) (B 49951 (by norm_num) ⟨24975, by rfl⟩ (by norm_num))
theorem R66613 : Reach 66613 := rs (se 5 (by rfl) ⟨3122, by rfl⟩) (B 6245 (by norm_num) ⟨3122, by rfl⟩ (by norm_num))
theorem R99389 : Reach 99389 := rs (se 3 (by rfl) ⟨18635, by rfl⟩) (B 37271 (by norm_num) ⟨18635, by rfl⟩ (by norm_num))
theorem R230485 : Reach 230485 := rs (se 8 (by rfl) ⟨1350, by rfl⟩) (B 2701 (by norm_num) ⟨1350, by rfl⟩ (by norm_num))
theorem R66649 : Reach 66649 := rs (se 2 (by rfl) ⟨24993, by rfl⟩) (B 49987 (by norm_num) ⟨24993, by rfl⟩ (by norm_num))
theorem R66685 : Reach 66685 := rs (se 3 (by rfl) ⟨12503, by rfl⟩) (B 25007 (by norm_num) ⟨12503, by rfl⟩ (by norm_num))
theorem R66721 : Reach 66721 := rs (se 2 (by rfl) ⟨25020, by rfl⟩) (B 50041 (by norm_num) ⟨25020, by rfl⟩ (by norm_num))
theorem R66757 : Reach 66757 := rs (se 4 (by rfl) ⟨6258, by rfl⟩) (B 12517 (by norm_num) ⟨6258, by rfl⟩ (by norm_num))
theorem R66781 : Reach 66781 := rs (se 3 (by rfl) ⟨12521, by rfl⟩) (B 25043 (by norm_num) ⟨12521, by rfl⟩ (by norm_num))
theorem R66793 : Reach 66793 := rs (se 2 (by rfl) ⟨25047, by rfl⟩) (B 50095 (by norm_num) ⟨25047, by rfl⟩ (by norm_num))
theorem R165125 : Reach 165125 := rs (se 4 (by rfl) ⟨15480, by rfl⟩) (B 30961 (by norm_num) ⟨15480, by rfl⟩ (by norm_num))
theorem R66829 : Reach 66829 := rs (se 3 (by rfl) ⟨12530, by rfl⟩) (B 25061 (by norm_num) ⟨12530, by rfl⟩ (by norm_num))
theorem R66865 : Reach 66865 := rs (se 2 (by rfl) ⟨25074, by rfl⟩) (B 50149 (by norm_num) ⟨25074, by rfl⟩ (by norm_num))
theorem R66901 : Reach 66901 := rs (se 12 (by rfl) ⟨24, by rfl⟩) (B 49 (by norm_num) ⟨24, by rfl⟩ (by norm_num))
theorem R66937 : Reach 66937 := rs (se 2 (by rfl) ⟨25101, by rfl⟩) (B 50203 (by norm_num) ⟨25101, by rfl⟩ (by norm_num))
theorem R230789 : Reach 230789 := rs (se 4 (by rfl) ⟨21636, by rfl⟩) (B 43273 (by norm_num) ⟨21636, by rfl⟩ (by norm_num))
theorem R66973 : Reach 66973 := rs (se 3 (by rfl) ⟨12557, by rfl⟩) (B 25115 (by norm_num) ⟨12557, by rfl⟩ (by norm_num))
theorem R67009 : Reach 67009 := rs (se 2 (by rfl) ⟨25128, by rfl⟩) (B 50257 (by norm_num) ⟨25128, by rfl⟩ (by norm_num))
theorem R99805 : Reach 99805 := rs (se 3 (by rfl) ⟨18713, by rfl⟩) (B 37427 (by norm_num) ⟨18713, by rfl⟩ (by norm_num))
theorem R67045 : Reach 67045 := rs (se 4 (by rfl) ⟨6285, by rfl⟩) (B 12571 (by norm_num) ⟨6285, by rfl⟩ (by norm_num))
theorem R67081 : Reach 67081 := rs (se 2 (by rfl) ⟨25155, by rfl⟩) (B 50311 (by norm_num) ⟨25155, by rfl⟩ (by norm_num))
theorem R67117 : Reach 67117 := rs (se 3 (by rfl) ⟨12584, by rfl⟩) (B 25169 (by norm_num) ⟨12584, by rfl⟩ (by norm_num))
theorem R99893 : Reach 99893 := rs (se 5 (by rfl) ⟨4682, by rfl⟩) (B 9365 (by norm_num) ⟨4682, by rfl⟩ (by norm_num))
theorem R67153 : Reach 67153 := rs (se 2 (by rfl) ⟨25182, by rfl⟩) (B 50365 (by norm_num) ⟨25182, by rfl⟩ (by norm_num))
theorem R67189 : Reach 67189 := rs (se 5 (by rfl) ⟨3149, by rfl⟩) (B 6299 (by norm_num) ⟨3149, by rfl⟩ (by norm_num))
theorem R525973 : Reach 525973 := rs (se 6 (by rfl) ⟨12327, by rfl⟩) (B 24655 (by norm_num) ⟨12327, by rfl⟩ (by norm_num))
theorem R67225 : Reach 67225 := rs (se 2 (by rfl) ⟨25209, by rfl⟩) (B 50419 (by norm_num) ⟨25209, by rfl⟩ (by norm_num))
theorem R100021 : Reach 100021 := rs (se 5 (by rfl) ⟨4688, by rfl⟩) (B 9377 (by norm_num) ⟨4688, by rfl⟩ (by norm_num))
theorem R362165 : Reach 362165 := rs (se 5 (by rfl) ⟨16976, by rfl⟩) (B 33953 (by norm_num) ⟨16976, by rfl⟩ (by norm_num))
theorem R67261 : Reach 67261 := rs (se 3 (by rfl) ⟨12611, by rfl⟩) (B 25223 (by norm_num) ⟨12611, by rfl⟩ (by norm_num))
theorem R67297 : Reach 67297 := rs (se 2 (by rfl) ⟨25236, by rfl⟩) (B 50473 (by norm_num) ⟨25236, by rfl⟩ (by norm_num))
theorem R132853 : Reach 132853 := rs (se 5 (by rfl) ⟨6227, by rfl⟩) (B 12455 (by norm_num) ⟨6227, by rfl⟩ (by norm_num))
theorem R67333 : Reach 67333 := rs (se 4 (by rfl) ⟨6312, by rfl⟩) (B 12625 (by norm_num) ⟨6312, by rfl⟩ (by norm_num))
theorem R100109 : Reach 100109 := rs (se 3 (by rfl) ⟨18770, by rfl⟩) (B 37541 (by norm_num) ⟨18770, by rfl⟩ (by norm_num))
theorem R67349 : Reach 67349 := rs (se 6 (by rfl) ⟨1578, by rfl⟩) (B 3157 (by norm_num) ⟨1578, by rfl⟩ (by norm_num))
theorem R100133 : Reach 100133 := rs (se 4 (by rfl) ⟨9387, by rfl⟩) (B 18775 (by norm_num) ⟨9387, by rfl⟩ (by norm_num))
theorem R67369 : Reach 67369 := rs (se 2 (by rfl) ⟨25263, by rfl⟩) (B 50527 (by norm_num) ⟨25263, by rfl⟩ (by norm_num))
theorem R67405 : Reach 67405 := rs (se 3 (by rfl) ⟨12638, by rfl⟩) (B 25277 (by norm_num) ⟨12638, by rfl⟩ (by norm_num))
theorem R132949 : Reach 132949 := rs (se 9 (by rfl) ⟨389, by rfl⟩) (B 779 (by norm_num) ⟨389, by rfl⟩ (by norm_num))
theorem R67441 : Reach 67441 := rs (se 2 (by rfl) ⟨25290, by rfl⟩) (B 50581 (by norm_num) ⟨25290, by rfl⟩ (by norm_num))
theorem R132997 : Reach 132997 := rs (se 4 (by rfl) ⟨12468, by rfl⟩) (B 24937 (by norm_num) ⟨12468, by rfl⟩ (by norm_num))
theorem R100237 : Reach 100237 := rs (se 3 (by rfl) ⟨18794, by rfl⟩) (B 37589 (by norm_num) ⟨18794, by rfl⟩ (by norm_num))
theorem R67477 : Reach 67477 := rs (se 6 (by rfl) ⟨1581, by rfl⟩) (B 3163 (by norm_num) ⟨1581, by rfl⟩ (by norm_num))
theorem R133037 : Reach 133037 := rs (se 3 (by rfl) ⟨24944, by rfl⟩) (B 49889 (by norm_num) ⟨24944, by rfl⟩ (by norm_num))
theorem R67513 : Reach 67513 := rs (se 2 (by rfl) ⟨25317, by rfl⟩) (B 50635 (by norm_num) ⟨25317, by rfl⟩ (by norm_num))
theorem R755669 : Reach 755669 := rs (se 7 (by rfl) ⟨8855, by rfl⟩) (B 17711 (by norm_num) ⟨8855, by rfl⟩ (by norm_num))
theorem R67549 : Reach 67549 := rs (se 3 (by rfl) ⟨12665, by rfl⟩) (B 25331 (by norm_num) ⟨12665, by rfl⟩ (by norm_num))
theorem R100325 : Reach 100325 := rs (se 4 (by rfl) ⟨9405, by rfl⟩) (B 18811 (by norm_num) ⟨9405, by rfl⟩ (by norm_num))
theorem R133109 : Reach 133109 := rs (se 5 (by rfl) ⟨6239, by rfl⟩) (B 12479 (by norm_num) ⟨6239, by rfl⟩ (by norm_num))
theorem R67585 : Reach 67585 := rs (se 2 (by rfl) ⟨25344, by rfl⟩) (B 50689 (by norm_num) ⟨25344, by rfl⟩ (by norm_num))
theorem R67621 : Reach 67621 := rs (se 4 (by rfl) ⟨6339, by rfl⟩) (B 12679 (by norm_num) ⟨6339, by rfl⟩ (by norm_num))
theorem R133181 : Reach 133181 := rs (se 3 (by rfl) ⟨24971, by rfl⟩) (B 49943 (by norm_num) ⟨24971, by rfl⟩ (by norm_num))
theorem R67657 : Reach 67657 := rs (se 2 (by rfl) ⟨25371, by rfl⟩) (B 50743 (by norm_num) ⟨25371, by rfl⟩ (by norm_num))
theorem R100453 : Reach 100453 := rs (se 4 (by rfl) ⟨9417, by rfl⟩) (B 18835 (by norm_num) ⟨9417, by rfl⟩ (by norm_num))
theorem R67693 : Reach 67693 := rs (se 3 (by rfl) ⟨12692, by rfl⟩) (B 25385 (by norm_num) ⟨12692, by rfl⟩ (by norm_num))
theorem R133253 : Reach 133253 := rs (se 4 (by rfl) ⟨12492, by rfl⟩) (B 24985 (by norm_num) ⟨12492, by rfl⟩ (by norm_num))
theorem R67729 : Reach 67729 := rs (se 2 (by rfl) ⟨25398, by rfl⟩) (B 50797 (by norm_num) ⟨25398, by rfl⟩ (by norm_num))
theorem R67765 : Reach 67765 := rs (se 5 (by rfl) ⟨3176, by rfl⟩) (B 6353 (by norm_num) ⟨3176, by rfl⟩ (by norm_num))
theorem R100541 : Reach 100541 := rs (se 3 (by rfl) ⟨18851, by rfl⟩) (B 37703 (by norm_num) ⟨18851, by rfl⟩ (by norm_num))
theorem R133325 : Reach 133325 := rs (se 3 (by rfl) ⟨24998, by rfl⟩) (B 49997 (by norm_num) ⟨24998, by rfl⟩ (by norm_num))
theorem R592085 : Reach 592085 := rs (se 7 (by rfl) ⟨6938, by rfl⟩) (B 13877 (by norm_num) ⟨6938, by rfl⟩ (by norm_num))
theorem R67801 : Reach 67801 := rs (se 2 (by rfl) ⟨25425, by rfl⟩) (B 50851 (by norm_num) ⟨25425, by rfl⟩ (by norm_num))
theorem R67837 : Reach 67837 := rs (se 3 (by rfl) ⟨12719, by rfl⟩) (B 25439 (by norm_num) ⟨12719, by rfl⟩ (by norm_num))
theorem R133373 : Reach 133373 := rs (se 3 (by rfl) ⟨25007, by rfl⟩) (B 50015 (by norm_num) ⟨25007, by rfl⟩ (by norm_num))
theorem R133397 : Reach 133397 := rs (se 6 (by rfl) ⟨3126, by rfl⟩) (B 6253 (by norm_num) ⟨3126, by rfl⟩ (by norm_num))
theorem R67873 : Reach 67873 := rs (se 2 (by rfl) ⟨25452, by rfl⟩) (B 50905 (by norm_num) ⟨25452, by rfl⟩ (by norm_num))
theorem R264485 : Reach 264485 := rs (se 4 (by rfl) ⟨24795, by rfl⟩) (B 49591 (by norm_num) ⟨24795, by rfl⟩ (by norm_num))
theorem R100669 : Reach 100669 := rs (se 3 (by rfl) ⟨18875, by rfl⟩) (B 37751 (by norm_num) ⟨18875, by rfl⟩ (by norm_num))
theorem R67909 : Reach 67909 := rs (se 4 (by rfl) ⟨6366, by rfl⟩) (B 12733 (by norm_num) ⟨6366, by rfl⟩ (by norm_num))
theorem R133469 : Reach 133469 := rs (se 3 (by rfl) ⟨25025, by rfl⟩) (B 50051 (by norm_num) ⟨25025, by rfl⟩ (by norm_num))
theorem R67945 : Reach 67945 := rs (se 2 (by rfl) ⟨25479, by rfl⟩) (B 50959 (by norm_num) ⟨25479, by rfl⟩ (by norm_num))
theorem R67981 : Reach 67981 := rs (se 3 (by rfl) ⟨12746, by rfl⟩) (B 25493 (by norm_num) ⟨12746, by rfl⟩ (by norm_num))
theorem R100757 : Reach 100757 := rs (se 6 (by rfl) ⟨2361, by rfl⟩) (B 4723 (by norm_num) ⟨2361, by rfl⟩ (by norm_num))
theorem R133541 : Reach 133541 := rs (se 4 (by rfl) ⟨12519, by rfl⟩) (B 25039 (by norm_num) ⟨12519, by rfl⟩ (by norm_num))
theorem R68017 : Reach 68017 := rs (se 2 (by rfl) ⟨25506, by rfl⟩) (B 51013 (by norm_num) ⟨25506, by rfl⟩ (by norm_num))
theorem R68053 : Reach 68053 := rs (se 7 (by rfl) ⟨797, by rfl⟩) (B 1595 (by norm_num) ⟨797, by rfl⟩ (by norm_num))
theorem R133613 : Reach 133613 := rs (se 3 (by rfl) ⟨25052, by rfl⟩) (B 50105 (by norm_num) ⟨25052, by rfl⟩ (by norm_num))
theorem R395765 : Reach 395765 := rs (se 5 (by rfl) ⟨18551, by rfl⟩) (B 37103 (by norm_num) ⟨18551, by rfl⟩ (by norm_num))
theorem R68089 : Reach 68089 := rs (se 2 (by rfl) ⟨25533, by rfl⟩) (B 51067 (by norm_num) ⟨25533, by rfl⟩ (by norm_num))
theorem R100885 : Reach 100885 := rs (se 6 (by rfl) ⟨2364, by rfl⟩) (B 4729 (by norm_num) ⟨2364, by rfl⟩ (by norm_num))
theorem R68117 : Reach 68117 := rs (se 6 (by rfl) ⟨1596, by rfl⟩) (B 3193 (by norm_num) ⟨1596, by rfl⟩ (by norm_num))
theorem R68125 : Reach 68125 := rs (se 3 (by rfl) ⟨12773, by rfl⟩) (B 25547 (by norm_num) ⟨12773, by rfl⟩ (by norm_num))
theorem R133685 : Reach 133685 := rs (se 5 (by rfl) ⟨6266, by rfl⟩) (B 12533 (by norm_num) ⟨6266, by rfl⟩ (by norm_num))
theorem R68161 : Reach 68161 := rs (se 2 (by rfl) ⟨25560, by rfl⟩) (B 51121 (by norm_num) ⟨25560, by rfl⟩ (by norm_num))
theorem R68197 : Reach 68197 := rs (se 4 (by rfl) ⟨6393, by rfl⟩) (B 12787 (by norm_num) ⟨6393, by rfl⟩ (by norm_num))
theorem R100973 : Reach 100973 := rs (se 3 (by rfl) ⟨18932, by rfl⟩) (B 37865 (by norm_num) ⟨18932, by rfl⟩ (by norm_num))
theorem R133741 : Reach 133741 := rs (se 3 (by rfl) ⟨25076, by rfl⟩) (B 50153 (by norm_num) ⟨25076, by rfl⟩ (by norm_num))
theorem R133757 : Reach 133757 := rs (se 3 (by rfl) ⟨25079, by rfl⟩) (B 50159 (by norm_num) ⟨25079, by rfl⟩ (by norm_num))
theorem R68233 : Reach 68233 := rs (se 2 (by rfl) ⟨25587, by rfl⟩) (B 51175 (by norm_num) ⟨25587, by rfl⟩ (by norm_num))
theorem R68269 : Reach 68269 := rs (se 3 (by rfl) ⟨12800, by rfl⟩) (B 25601 (by norm_num) ⟨12800, by rfl⟩ (by norm_num))
theorem R133829 : Reach 133829 := rs (se 4 (by rfl) ⟨12546, by rfl⟩) (B 25093 (by norm_num) ⟨12546, by rfl⟩ (by norm_num))
theorem R68305 : Reach 68305 := rs (se 2 (by rfl) ⟨25614, by rfl⟩) (B 51229 (by norm_num) ⟨25614, by rfl⟩ (by norm_num))
theorem R101101 : Reach 101101 := rs (se 3 (by rfl) ⟨18956, by rfl⟩) (B 37913 (by norm_num) ⟨18956, by rfl⟩ (by norm_num))
theorem R68341 : Reach 68341 := rs (se 5 (by rfl) ⟨3203, by rfl⟩) (B 6407 (by norm_num) ⟨3203, by rfl⟩ (by norm_num))
theorem R133901 : Reach 133901 := rs (se 3 (by rfl) ⟨25106, by rfl⟩) (B 50213 (by norm_num) ⟨25106, by rfl⟩ (by norm_num))
theorem R68377 : Reach 68377 := rs (se 2 (by rfl) ⟨25641, by rfl⟩) (B 51283 (by norm_num) ⟨25641, by rfl⟩ (by norm_num))
theorem R68413 : Reach 68413 := rs (se 3 (by rfl) ⟨12827, by rfl⟩) (B 25655 (by norm_num) ⟨12827, by rfl⟩ (by norm_num))
theorem R101189 : Reach 101189 := rs (se 4 (by rfl) ⟨9486, by rfl⟩) (B 18973 (by norm_num) ⟨9486, by rfl⟩ (by norm_num))
theorem R133973 : Reach 133973 := rs (se 9 (by rfl) ⟨392, by rfl⟩) (B 785 (by norm_num) ⟨392, by rfl⟩ (by norm_num))
theorem R68449 : Reach 68449 := rs (se 2 (by rfl) ⟨25668, by rfl⟩) (B 51337 (by norm_num) ⟨25668, by rfl⟩ (by norm_num))
theorem R68485 : Reach 68485 := rs (se 4 (by rfl) ⟨6420, by rfl⟩) (B 12841 (by norm_num) ⟨6420, by rfl⟩ (by norm_num))
theorem R134045 : Reach 134045 := rs (se 3 (by rfl) ⟨25133, by rfl⟩) (B 50267 (by norm_num) ⟨25133, by rfl⟩ (by norm_num))
theorem R68521 : Reach 68521 := rs (se 2 (by rfl) ⟨25695, by rfl⟩) (B 51391 (by norm_num) ⟨25695, by rfl⟩ (by norm_num))
theorem R101317 : Reach 101317 := rs (se 4 (by rfl) ⟨9498, by rfl⟩) (B 18997 (by norm_num) ⟨9498, by rfl⟩ (by norm_num))
theorem R68557 : Reach 68557 := rs (se 3 (by rfl) ⟨12854, by rfl⟩) (B 25709 (by norm_num) ⟨12854, by rfl⟩ (by norm_num))
theorem R199637 : Reach 199637 := rs (se 7 (by rfl) ⟨2339, by rfl⟩) (B 4679 (by norm_num) ⟨2339, by rfl⟩ (by norm_num))
theorem R134117 : Reach 134117 := rs (se 4 (by rfl) ⟨12573, by rfl⟩) (B 25147 (by norm_num) ⟨12573, by rfl⟩ (by norm_num))
theorem R68593 : Reach 68593 := rs (se 2 (by rfl) ⟨25722, by rfl⟩) (B 51445 (by norm_num) ⟨25722, by rfl⟩ (by norm_num))
theorem R68629 : Reach 68629 := rs (se 6 (by rfl) ⟨1608, by rfl⟩) (B 3217 (by norm_num) ⟨1608, by rfl⟩ (by norm_num))
theorem R101405 : Reach 101405 := rs (se 3 (by rfl) ⟨19013, by rfl⟩) (B 38027 (by norm_num) ⟨19013, by rfl⟩ (by norm_num))
theorem R134189 : Reach 134189 := rs (se 3 (by rfl) ⟨25160, by rfl⟩) (B 50321 (by norm_num) ⟨25160, by rfl⟩ (by norm_num))
theorem R68665 : Reach 68665 := rs (se 2 (by rfl) ⟨25749, by rfl⟩) (B 51499 (by norm_num) ⟨25749, by rfl⟩ (by norm_num))
theorem R68677 : Reach 68677 := rs (se 4 (by rfl) ⟨6438, by rfl⟩) (B 12877 (by norm_num) ⟨6438, by rfl⟩ (by norm_num))
theorem R68701 : Reach 68701 := rs (se 3 (by rfl) ⟨12881, by rfl⟩) (B 25763 (by norm_num) ⟨12881, by rfl⟩ (by norm_num))
theorem R134261 : Reach 134261 := rs (se 5 (by rfl) ⟨6293, by rfl⟩) (B 12587 (by norm_num) ⟨6293, by rfl⟩ (by norm_num))
theorem R68737 : Reach 68737 := rs (se 2 (by rfl) ⟨25776, by rfl⟩) (B 51553 (by norm_num) ⟨25776, by rfl⟩ (by norm_num))
theorem R101533 : Reach 101533 := rs (se 3 (by rfl) ⟨19037, by rfl⟩) (B 38075 (by norm_num) ⟨19037, by rfl⟩ (by norm_num))
theorem R68773 : Reach 68773 := rs (se 4 (by rfl) ⟨6447, by rfl⟩) (B 12895 (by norm_num) ⟨6447, by rfl⟩ (by norm_num))
theorem R134333 : Reach 134333 := rs (se 3 (by rfl) ⟨25187, by rfl⟩) (B 50375 (by norm_num) ⟨25187, by rfl⟩ (by norm_num))
theorem R68797 : Reach 68797 := rs (se 3 (by rfl) ⟨12899, by rfl⟩) (B 25799 (by norm_num) ⟨12899, by rfl⟩ (by norm_num))
theorem R68809 : Reach 68809 := rs (se 2 (by rfl) ⟨25803, by rfl⟩) (B 51607 (by norm_num) ⟨25803, by rfl⟩ (by norm_num))
theorem R68845 : Reach 68845 := rs (se 3 (by rfl) ⟨12908, by rfl⟩) (B 25817 (by norm_num) ⟨12908, by rfl⟩ (by norm_num))
theorem R101621 : Reach 101621 := rs (se 5 (by rfl) ⟨4763, by rfl⟩) (B 9527 (by norm_num) ⟨4763, by rfl⟩ (by norm_num))
theorem R134389 : Reach 134389 := rs (se 5 (by rfl) ⟨6299, by rfl⟩) (B 12599 (by norm_num) ⟨6299, by rfl⟩ (by norm_num))
theorem R134405 : Reach 134405 := rs (se 4 (by rfl) ⟨12600, by rfl⟩) (B 25201 (by norm_num) ⟨12600, by rfl⟩ (by norm_num))
theorem R68881 : Reach 68881 := rs (se 2 (by rfl) ⟨25830, by rfl⟩) (B 51661 (by norm_num) ⟨25830, by rfl⟩ (by norm_num))
theorem R68917 : Reach 68917 := rs (se 5 (by rfl) ⟨3230, by rfl⟩) (B 6461 (by norm_num) ⟨3230, by rfl⟩ (by norm_num))
theorem R134477 : Reach 134477 := rs (se 3 (by rfl) ⟨25214, by rfl⟩) (B 50429 (by norm_num) ⟨25214, by rfl⟩ (by norm_num))
theorem R68953 : Reach 68953 := rs (se 2 (by rfl) ⟨25857, by rfl⟩) (B 51715 (by norm_num) ⟨25857, by rfl⟩ (by norm_num))
theorem R101749 : Reach 101749 := rs (se 5 (by rfl) ⟨4769, by rfl⟩) (B 9539 (by norm_num) ⟨4769, by rfl⟩ (by norm_num))
theorem R68989 : Reach 68989 := rs (se 3 (by rfl) ⟨12935, by rfl⟩) (B 25871 (by norm_num) ⟨12935, by rfl⟩ (by norm_num))
theorem R200069 : Reach 200069 := rs (se 4 (by rfl) ⟨18756, by rfl⟩) (B 37513 (by norm_num) ⟨18756, by rfl⟩ (by norm_num))
theorem R134549 : Reach 134549 := rs (se 6 (by rfl) ⟨3153, by rfl⟩) (B 6307 (by norm_num) ⟨3153, by rfl⟩ (by norm_num))
theorem R69025 : Reach 69025 := rs (se 2 (by rfl) ⟨25884, by rfl⟩) (B 51769 (by norm_num) ⟨25884, by rfl⟩ (by norm_num))
theorem R69061 : Reach 69061 := rs (se 4 (by rfl) ⟨6474, by rfl⟩) (B 12949 (by norm_num) ⟨6474, by rfl⟩ (by norm_num))
theorem R232901 : Reach 232901 := rs (se 4 (by rfl) ⟨21834, by rfl⟩) (B 43669 (by norm_num) ⟨21834, by rfl⟩ (by norm_num))
theorem R101837 : Reach 101837 := rs (se 3 (by rfl) ⟨19094, by rfl⟩) (B 38189 (by norm_num) ⟨19094, by rfl⟩ (by norm_num))
theorem R134621 : Reach 134621 := rs (se 3 (by rfl) ⟨25241, by rfl⟩) (B 50483 (by norm_num) ⟨25241, by rfl⟩ (by norm_num))
theorem R69097 : Reach 69097 := rs (se 2 (by rfl) ⟨25911, by rfl⟩) (B 51823 (by norm_num) ⟨25911, by rfl⟩ (by norm_num))
theorem R69133 : Reach 69133 := rs (se 3 (by rfl) ⟨12962, by rfl⟩) (B 25925 (by norm_num) ⟨12962, by rfl⟩ (by norm_num))
theorem R134693 : Reach 134693 := rs (se 4 (by rfl) ⟨12627, by rfl⟩) (B 25255 (by norm_num) ⟨12627, by rfl⟩ (by norm_num))
theorem R69169 : Reach 69169 := rs (se 2 (by rfl) ⟨25938, by rfl⟩) (B 51877 (by norm_num) ⟨25938, by rfl⟩ (by norm_num))
theorem R101965 : Reach 101965 := rs (se 3 (by rfl) ⟨19118, by rfl⟩) (B 38237 (by norm_num) ⟨19118, by rfl⟩ (by norm_num))
theorem R69205 : Reach 69205 := rs (se 8 (by rfl) ⟨405, by rfl⟩) (B 811 (by norm_num) ⟨405, by rfl⟩ (by norm_num))
theorem R527957 : Reach 527957 := rs (se 8 (by rfl) ⟨3093, by rfl⟩) (B 6187 (by norm_num) ⟨3093, by rfl⟩ (by norm_num))
theorem R134765 : Reach 134765 := rs (se 3 (by rfl) ⟨25268, by rfl⟩) (B 50537 (by norm_num) ⟨25268, by rfl⟩ (by norm_num))
theorem R69241 : Reach 69241 := rs (se 2 (by rfl) ⟨25965, by rfl⟩) (B 51931 (by norm_num) ⟨25965, by rfl⟩ (by norm_num))
theorem R69277 : Reach 69277 := rs (se 3 (by rfl) ⟨12989, by rfl⟩) (B 25979 (by norm_num) ⟨12989, by rfl⟩ (by norm_num))
theorem R102053 : Reach 102053 := rs (se 4 (by rfl) ⟨9567, by rfl⟩) (B 19135 (by norm_num) ⟨9567, by rfl⟩ (by norm_num))
theorem R134837 : Reach 134837 := rs (se 5 (by rfl) ⟨6320, by rfl⟩) (B 12641 (by norm_num) ⟨6320, by rfl⟩ (by norm_num))
theorem R69313 : Reach 69313 := rs (se 2 (by rfl) ⟨25992, by rfl⟩) (B 51985 (by norm_num) ⟨25992, by rfl⟩ (by norm_num))
theorem R233189 : Reach 233189 := rs (se 4 (by rfl) ⟨21861, by rfl⟩) (B 43723 (by norm_num) ⟨21861, by rfl⟩ (by norm_num))
theorem R69349 : Reach 69349 := rs (se 4 (by rfl) ⟨6501, by rfl⟩) (B 13003 (by norm_num) ⟨6501, by rfl⟩ (by norm_num))
theorem R134909 : Reach 134909 := rs (se 3 (by rfl) ⟨25295, by rfl⟩) (B 50591 (by norm_num) ⟨25295, by rfl⟩ (by norm_num))
theorem R102149 : Reach 102149 := rs (se 4 (by rfl) ⟨9576, by rfl⟩) (B 19153 (by norm_num) ⟨9576, by rfl⟩ (by norm_num))
theorem R69385 : Reach 69385 := rs (se 2 (by rfl) ⟨26019, by rfl⟩) (B 52039 (by norm_num) ⟨26019, by rfl⟩ (by norm_num))
theorem R102181 : Reach 102181 := rs (se 4 (by rfl) ⟨9579, by rfl⟩) (B 19159 (by norm_num) ⟨9579, by rfl⟩ (by norm_num))
theorem R69421 : Reach 69421 := rs (se 3 (by rfl) ⟨13016, by rfl⟩) (B 26033 (by norm_num) ⟨13016, by rfl⟩ (by norm_num))
theorem R200501 : Reach 200501 := rs (se 5 (by rfl) ⟨9398, by rfl⟩) (B 18797 (by norm_num) ⟨9398, by rfl⟩ (by norm_num))
theorem R134981 : Reach 134981 := rs (se 4 (by rfl) ⟨12654, by rfl⟩) (B 25309 (by norm_num) ⟨12654, by rfl⟩ (by norm_num))
theorem R69457 : Reach 69457 := rs (se 2 (by rfl) ⟨26046, by rfl⟩) (B 52093 (by norm_num) ⟨26046, by rfl⟩ (by norm_num))
theorem R69493 : Reach 69493 := rs (se 5 (by rfl) ⟨3257, by rfl⟩) (B 6515 (by norm_num) ⟨3257, by rfl⟩ (by norm_num))
theorem R102269 : Reach 102269 := rs (se 3 (by rfl) ⟨19175, by rfl⟩) (B 38351 (by norm_num) ⟨19175, by rfl⟩ (by norm_num))
theorem R135053 : Reach 135053 := rs (se 3 (by rfl) ⟨25322, by rfl⟩) (B 50645 (by norm_num) ⟨25322, by rfl⟩ (by norm_num))
theorem R69529 : Reach 69529 := rs (se 2 (by rfl) ⟨26073, by rfl⟩) (B 52147 (by norm_num) ⟨26073, by rfl⟩ (by norm_num))
theorem R69565 : Reach 69565 := rs (se 3 (by rfl) ⟨13043, by rfl⟩) (B 26087 (by norm_num) ⟨13043, by rfl⟩ (by norm_num))
theorem R135125 : Reach 135125 := rs (se 7 (by rfl) ⟨1583, by rfl⟩) (B 3167 (by norm_num) ⟨1583, by rfl⟩ (by norm_num))
theorem R69601 : Reach 69601 := rs (se 2 (by rfl) ⟨26100, by rfl⟩) (B 52201 (by norm_num) ⟨26100, by rfl⟩ (by norm_num))
theorem R102397 : Reach 102397 := rs (se 3 (by rfl) ⟨19199, by rfl⟩) (B 38399 (by norm_num) ⟨19199, by rfl⟩ (by norm_num))
theorem R69637 : Reach 69637 := rs (se 4 (by rfl) ⟨6528, by rfl⟩) (B 13057 (by norm_num) ⟨6528, by rfl⟩ (by norm_num))
theorem R135197 : Reach 135197 := rs (se 3 (by rfl) ⟨25349, by rfl⟩) (B 50699 (by norm_num) ⟨25349, by rfl⟩ (by norm_num))
theorem R69673 : Reach 69673 := rs (se 2 (by rfl) ⟨26127, by rfl⟩) (B 52255 (by norm_num) ⟨26127, by rfl⟩ (by norm_num))
theorem R69709 : Reach 69709 := rs (se 3 (by rfl) ⟨13070, by rfl⟩) (B 26141 (by norm_num) ⟨13070, by rfl⟩ (by norm_num))
theorem R102485 : Reach 102485 := rs (se 8 (by rfl) ⟨600, by rfl⟩) (B 1201 (by norm_num) ⟨600, by rfl⟩ (by norm_num))
theorem R135269 : Reach 135269 := rs (se 4 (by rfl) ⟨12681, by rfl⟩) (B 25363 (by norm_num) ⟨12681, by rfl⟩ (by norm_num))
theorem R69745 : Reach 69745 := rs (se 2 (by rfl) ⟨26154, by rfl⟩) (B 52309 (by norm_num) ⟨26154, by rfl⟩ (by norm_num))
theorem R69781 : Reach 69781 := rs (se 6 (by rfl) ⟨1635, by rfl⟩) (B 3271 (by norm_num) ⟨1635, by rfl⟩ (by norm_num))
theorem R135341 : Reach 135341 := rs (se 3 (by rfl) ⟨25376, by rfl⟩) (B 50753 (by norm_num) ⟨25376, by rfl⟩ (by norm_num))
theorem R69817 : Reach 69817 := rs (se 2 (by rfl) ⟨26181, by rfl⟩) (B 52363 (by norm_num) ⟨26181, by rfl⟩ (by norm_num))
theorem R102613 : Reach 102613 := rs (se 7 (by rfl) ⟨1202, by rfl⟩) (B 2405 (by norm_num) ⟨1202, by rfl⟩ (by norm_num))
theorem R69853 : Reach 69853 := rs (se 3 (by rfl) ⟨13097, by rfl⟩) (B 26195 (by norm_num) ⟨13097, by rfl⟩ (by norm_num))
theorem R200933 : Reach 200933 := rs (se 4 (by rfl) ⟨18837, by rfl⟩) (B 37675 (by norm_num) ⟨18837, by rfl⟩ (by norm_num))
theorem R135413 : Reach 135413 := rs (se 5 (by rfl) ⟨6347, by rfl⟩) (B 12695 (by norm_num) ⟨6347, by rfl⟩ (by norm_num))
theorem R69889 : Reach 69889 := rs (se 2 (by rfl) ⟨26208, by rfl⟩) (B 52417 (by norm_num) ⟨26208, by rfl⟩ (by norm_num))
theorem R299285 : Reach 299285 := rs (se 6 (by rfl) ⟨7014, by rfl⟩) (B 14029 (by norm_num) ⟨7014, by rfl⟩ (by norm_num))
theorem R69925 : Reach 69925 := rs (se 4 (by rfl) ⟨6555, by rfl⟩) (B 13111 (by norm_num) ⟨6555, by rfl⟩ (by norm_num))
theorem R102701 : Reach 102701 := rs (se 3 (by rfl) ⟨19256, by rfl⟩) (B 38513 (by norm_num) ⟨19256, by rfl⟩ (by norm_num))
theorem R463157 : Reach 463157 := rs (se 5 (by rfl) ⟨21710, by rfl⟩) (B 43421 (by norm_num) ⟨21710, by rfl⟩ (by norm_num))
theorem R135485 : Reach 135485 := rs (se 3 (by rfl) ⟨25403, by rfl⟩) (B 50807 (by norm_num) ⟨25403, by rfl⟩ (by norm_num))
theorem R69961 : Reach 69961 := rs (se 2 (by rfl) ⟨26235, by rfl⟩) (B 52471 (by norm_num) ⟨26235, by rfl⟩ (by norm_num))
theorem R69997 : Reach 69997 := rs (se 3 (by rfl) ⟨13124, by rfl⟩) (B 26249 (by norm_num) ⟨13124, by rfl⟩ (by norm_num))
theorem R135557 : Reach 135557 := rs (se 4 (by rfl) ⟨12708, by rfl⟩) (B 25417 (by norm_num) ⟨12708, by rfl⟩ (by norm_num))
theorem R102797 : Reach 102797 := rs (se 3 (by rfl) ⟨19274, by rfl⟩) (B 38549 (by norm_num) ⟨19274, by rfl⟩ (by norm_num))
theorem R70033 : Reach 70033 := rs (se 2 (by rfl) ⟨26262, by rfl⟩) (B 52525 (by norm_num) ⟨26262, by rfl⟩ (by norm_num))
theorem R102829 : Reach 102829 := rs (se 3 (by rfl) ⟨19280, by rfl⟩) (B 38561 (by norm_num) ⟨19280, by rfl⟩ (by norm_num))
theorem R70069 : Reach 70069 := rs (se 5 (by rfl) ⟨3284, by rfl⟩) (B 6569 (by norm_num) ⟨3284, by rfl⟩ (by norm_num))
theorem R168389 : Reach 168389 := rs (se 4 (by rfl) ⟨15786, by rfl⟩) (B 31573 (by norm_num) ⟨15786, by rfl⟩ (by norm_num))
theorem R135629 : Reach 135629 := rs (se 3 (by rfl) ⟨25430, by rfl⟩) (B 50861 (by norm_num) ⟨25430, by rfl⟩ (by norm_num))
theorem R70105 : Reach 70105 := rs (se 2 (by rfl) ⟨26289, by rfl⟩) (B 52579 (by norm_num) ⟨26289, by rfl⟩ (by norm_num))
theorem R70141 : Reach 70141 := rs (se 3 (by rfl) ⟨13151, by rfl⟩) (B 26303 (by norm_num) ⟨13151, by rfl⟩ (by norm_num))
theorem R102917 : Reach 102917 := rs (se 4 (by rfl) ⟨9648, by rfl⟩) (B 19297 (by norm_num) ⟨9648, by rfl⟩ (by norm_num))
theorem R135701 : Reach 135701 := rs (se 6 (by rfl) ⟨3180, by rfl⟩) (B 6361 (by norm_num) ⟨3180, by rfl⟩ (by norm_num))
theorem R70177 : Reach 70177 := rs (se 2 (by rfl) ⟨26316, by rfl⟩) (B 52633 (by norm_num) ⟨26316, by rfl⟩ (by norm_num))
theorem R70189 : Reach 70189 := rs (se 3 (by rfl) ⟨13160, by rfl⟩) (B 26321 (by norm_num) ⟨13160, by rfl⟩ (by norm_num))
theorem R135749 : Reach 135749 := rs (se 4 (by rfl) ⟨12726, by rfl⟩) (B 25453 (by norm_num) ⟨12726, by rfl⟩ (by norm_num))
theorem R70213 : Reach 70213 := rs (se 4 (by rfl) ⟨6582, by rfl⟩) (B 13165 (by norm_num) ⟨6582, by rfl⟩ (by norm_num))
theorem R135773 : Reach 135773 := rs (se 3 (by rfl) ⟨25457, by rfl⟩) (B 50915 (by norm_num) ⟨25457, by rfl⟩ (by norm_num))
theorem R70249 : Reach 70249 := rs (se 2 (by rfl) ⟨26343, by rfl⟩) (B 52687 (by norm_num) ⟨26343, by rfl⟩ (by norm_num))
theorem R168581 : Reach 168581 := rs (se 4 (by rfl) ⟨15804, by rfl⟩) (B 31609 (by norm_num) ⟨15804, by rfl⟩ (by norm_num))
theorem R103045 : Reach 103045 := rs (se 4 (by rfl) ⟨9660, by rfl⟩) (B 19321 (by norm_num) ⟨9660, by rfl⟩ (by norm_num))
theorem R135821 : Reach 135821 := rs (se 3 (by rfl) ⟨25466, by rfl⟩) (B 50933 (by norm_num) ⟨25466, by rfl⟩ (by norm_num))
theorem R70285 : Reach 70285 := rs (se 3 (by rfl) ⟨13178, by rfl⟩) (B 26357 (by norm_num) ⟨13178, by rfl⟩ (by norm_num))
theorem R201365 : Reach 201365 := rs (se 6 (by rfl) ⟨4719, by rfl⟩) (B 9439 (by norm_num) ⟨4719, by rfl⟩ (by norm_num))
theorem R135845 : Reach 135845 := rs (se 4 (by rfl) ⟨12735, by rfl⟩) (B 25471 (by norm_num) ⟨12735, by rfl⟩ (by norm_num))
theorem R70321 : Reach 70321 := rs (se 2 (by rfl) ⟨26370, by rfl⟩) (B 52741 (by norm_num) ⟨26370, by rfl⟩ (by norm_num))
theorem R70357 : Reach 70357 := rs (se 7 (by rfl) ⟨824, by rfl⟩) (B 1649 (by norm_num) ⟨824, by rfl⟩ (by norm_num))
theorem R103133 : Reach 103133 := rs (se 3 (by rfl) ⟨19337, by rfl⟩) (B 38675 (by norm_num) ⟨19337, by rfl⟩ (by norm_num))
theorem R135917 : Reach 135917 := rs (se 3 (by rfl) ⟨25484, by rfl⟩) (B 50969 (by norm_num) ⟨25484, by rfl⟩ (by norm_num))
theorem R70393 : Reach 70393 := rs (se 2 (by rfl) ⟨26397, by rfl⟩) (B 52795 (by norm_num) ⟨26397, by rfl⟩ (by norm_num))
theorem R70429 : Reach 70429 := rs (se 3 (by rfl) ⟨13205, by rfl⟩) (B 26411 (by norm_num) ⟨13205, by rfl⟩ (by norm_num))
theorem R135989 : Reach 135989 := rs (se 5 (by rfl) ⟨6374, by rfl⟩) (B 12749 (by norm_num) ⟨6374, by rfl⟩ (by norm_num))
theorem R70465 : Reach 70465 := rs (se 2 (by rfl) ⟨26424, by rfl⟩) (B 52849 (by norm_num) ⟨26424, by rfl⟩ (by norm_num))
theorem R299861 : Reach 299861 := rs (se 9 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R103261 : Reach 103261 := rs (se 3 (by rfl) ⟨19361, by rfl⟩) (B 38723 (by norm_num) ⟨19361, by rfl⟩ (by norm_num))
theorem R70501 : Reach 70501 := rs (se 4 (by rfl) ⟨6609, by rfl⟩) (B 13219 (by norm_num) ⟨6609, by rfl⟩ (by norm_num))
theorem R136061 : Reach 136061 := rs (se 3 (by rfl) ⟨25511, by rfl⟩) (B 51023 (by norm_num) ⟨25511, by rfl⟩ (by norm_num))
theorem R234373 : Reach 234373 := rs (se 4 (by rfl) ⟨21972, by rfl⟩) (B 43945 (by norm_num) ⟨21972, by rfl⟩ (by norm_num))
theorem R70537 : Reach 70537 := rs (se 2 (by rfl) ⟨26451, by rfl⟩) (B 52903 (by norm_num) ⟨26451, by rfl⟩ (by norm_num))
theorem R70573 : Reach 70573 := rs (se 3 (by rfl) ⟨13232, by rfl⟩) (B 26465 (by norm_num) ⟨13232, by rfl⟩ (by norm_num))
theorem R103349 : Reach 103349 := rs (se 5 (by rfl) ⟨4844, by rfl⟩) (B 9689 (by norm_num) ⟨4844, by rfl⟩ (by norm_num))
theorem R136133 : Reach 136133 := rs (se 4 (by rfl) ⟨12762, by rfl⟩) (B 25525 (by norm_num) ⟨12762, by rfl⟩ (by norm_num))
theorem R70609 : Reach 70609 := rs (se 2 (by rfl) ⟨26478, by rfl⟩) (B 52957 (by norm_num) ⟨26478, by rfl⟩ (by norm_num))
theorem R70645 : Reach 70645 := rs (se 5 (by rfl) ⟨3311, by rfl⟩) (B 6623 (by norm_num) ⟨3311, by rfl⟩ (by norm_num))
theorem R136205 : Reach 136205 := rs (se 3 (by rfl) ⟨25538, by rfl⟩) (B 51077 (by norm_num) ⟨25538, by rfl⟩ (by norm_num))
theorem R70681 : Reach 70681 := rs (se 2 (by rfl) ⟨26505, by rfl⟩) (B 53011 (by norm_num) ⟨26505, by rfl⟩ (by norm_num))
theorem R103477 : Reach 103477 := rs (se 5 (by rfl) ⟨4850, by rfl⟩) (B 9701 (by norm_num) ⟨4850, by rfl⟩ (by norm_num))
theorem R70717 : Reach 70717 := rs (se 3 (by rfl) ⟨13259, by rfl⟩) (B 26519 (by norm_num) ⟨13259, by rfl⟩ (by norm_num))
theorem R201797 : Reach 201797 := rs (se 4 (by rfl) ⟨18918, by rfl⟩) (B 37837 (by norm_num) ⟨18918, by rfl⟩ (by norm_num))
theorem R136277 : Reach 136277 := rs (se 8 (by rfl) ⟨798, by rfl⟩) (B 1597 (by norm_num) ⟨798, by rfl⟩ (by norm_num))
theorem R70753 : Reach 70753 := rs (se 2 (by rfl) ⟨26532, by rfl⟩) (B 53065 (by norm_num) ⟨26532, by rfl⟩ (by norm_num))
theorem R70789 : Reach 70789 := rs (se 4 (by rfl) ⟨6636, by rfl⟩) (B 13273 (by norm_num) ⟨6636, by rfl⟩ (by norm_num))
theorem R103565 : Reach 103565 := rs (se 3 (by rfl) ⟨19418, by rfl⟩) (B 38837 (by norm_num) ⟨19418, by rfl⟩ (by norm_num))
theorem R136349 : Reach 136349 := rs (se 3 (by rfl) ⟨25565, by rfl⟩) (B 51131 (by norm_num) ⟨25565, by rfl⟩ (by norm_num))
theorem R70825 : Reach 70825 := rs (se 2 (by rfl) ⟨26559, by rfl⟩) (B 53119 (by norm_num) ⟨26559, by rfl⟩ (by norm_num))
theorem R234677 : Reach 234677 := rs (se 5 (by rfl) ⟨11000, by rfl⟩) (B 22001 (by norm_num) ⟨11000, by rfl⟩ (by norm_num))
theorem R70861 : Reach 70861 := rs (se 3 (by rfl) ⟨13286, by rfl⟩) (B 26573 (by norm_num) ⟨13286, by rfl⟩ (by norm_num))
theorem R136421 : Reach 136421 := rs (se 4 (by rfl) ⟨12789, by rfl⟩) (B 25579 (by norm_num) ⟨12789, by rfl⟩ (by norm_num))
theorem R70897 : Reach 70897 := rs (se 2 (by rfl) ⟨26586, by rfl⟩) (B 53173 (by norm_num) ⟨26586, by rfl⟩ (by norm_num))
theorem R70921 : Reach 70921 := rs (se 2 (by rfl) ⟨26595, by rfl⟩) (B 53191 (by norm_num) ⟨26595, by rfl⟩ (by norm_num))
theorem R103693 : Reach 103693 := rs (se 3 (by rfl) ⟨19442, by rfl⟩) (B 38885 (by norm_num) ⟨19442, by rfl⟩ (by norm_num))
theorem R70933 : Reach 70933 := rs (se 6 (by rfl) ⟨1662, by rfl⟩) (B 3325 (by norm_num) ⟨1662, by rfl⟩ (by norm_num))
theorem R136493 : Reach 136493 := rs (se 3 (by rfl) ⟨25592, by rfl⟩) (B 51185 (by norm_num) ⟨25592, by rfl⟩ (by norm_num))
theorem R70969 : Reach 70969 := rs (se 2 (by rfl) ⟨26613, by rfl⟩) (B 53227 (by norm_num) ⟨26613, by rfl⟩ (by norm_num))
theorem R71005 : Reach 71005 := rs (se 3 (by rfl) ⟨13313, by rfl⟩) (B 26627 (by norm_num) ⟨13313, by rfl⟩ (by norm_num))
theorem R103781 : Reach 103781 := rs (se 4 (by rfl) ⟨9729, by rfl⟩) (B 19459 (by norm_num) ⟨9729, by rfl⟩ (by norm_num))
theorem R202085 : Reach 202085 := rs (se 4 (by rfl) ⟨18945, by rfl⟩) (B 37891 (by norm_num) ⟨18945, by rfl⟩ (by norm_num))
theorem R136565 : Reach 136565 := rs (se 5 (by rfl) ⟨6401, by rfl⟩) (B 12803 (by norm_num) ⟨6401, by rfl⟩ (by norm_num))
theorem R136637 : Reach 136637 := rs (se 3 (by rfl) ⟨25619, by rfl⟩) (B 51239 (by norm_num) ⟨25619, by rfl⟩ (by norm_num))
theorem R103909 : Reach 103909 := rs (se 4 (by rfl) ⟨9741, by rfl⟩) (B 19483 (by norm_num) ⟨9741, by rfl⟩ (by norm_num))
theorem R202229 : Reach 202229 := rs (se 5 (by rfl) ⟨9479, by rfl⟩) (B 18959 (by norm_num) ⟨9479, by rfl⟩ (by norm_num))
theorem R136709 : Reach 136709 := rs (se 4 (by rfl) ⟨12816, by rfl⟩) (B 25633 (by norm_num) ⟨12816, by rfl⟩ (by norm_num))
theorem R103997 : Reach 103997 := rs (se 3 (by rfl) ⟨19499, by rfl⟩) (B 38999 (by norm_num) ⟨19499, by rfl⟩ (by norm_num))
theorem R136781 : Reach 136781 := rs (se 3 (by rfl) ⟨25646, by rfl⟩) (B 51293 (by norm_num) ⟨25646, by rfl⟩ (by norm_num))
theorem R169573 : Reach 169573 := rs (se 4 (by rfl) ⟨15897, by rfl⟩) (B 31795 (by norm_num) ⟨15897, by rfl⟩ (by norm_num))
theorem R267893 : Reach 267893 := rs (se 5 (by rfl) ⟨12557, by rfl⟩) (B 25115 (by norm_num) ⟨12557, by rfl⟩ (by norm_num))
theorem R136853 : Reach 136853 := rs (se 6 (by rfl) ⟨3207, by rfl⟩) (B 6415 (by norm_num) ⟨3207, by rfl⟩ (by norm_num))
theorem R202405 : Reach 202405 := rs (se 4 (by rfl) ⟨18975, by rfl⟩) (B 37951 (by norm_num) ⟨18975, by rfl⟩ (by norm_num))
theorem R104125 : Reach 104125 := rs (se 3 (by rfl) ⟨19523, by rfl⟩) (B 39047 (by norm_num) ⟨19523, by rfl⟩ (by norm_num))
theorem R136925 : Reach 136925 := rs (se 3 (by rfl) ⟨25673, by rfl⟩) (B 51347 (by norm_num) ⟨25673, by rfl⟩ (by norm_num))
theorem R104213 : Reach 104213 := rs (se 6 (by rfl) ⟨2442, by rfl⟩) (B 4885 (by norm_num) ⟨2442, by rfl⟩ (by norm_num))
theorem R136997 : Reach 136997 := rs (se 4 (by rfl) ⟨12843, by rfl⟩) (B 25687 (by norm_num) ⟨12843, by rfl⟩ (by norm_num))
theorem R137069 : Reach 137069 := rs (se 3 (by rfl) ⟨25700, by rfl⟩) (B 51401 (by norm_num) ⟨25700, by rfl⟩ (by norm_num))
theorem R104341 : Reach 104341 := rs (se 6 (by rfl) ⟨2445, by rfl⟩) (B 4891 (by norm_num) ⟨2445, by rfl⟩ (by norm_num))
theorem R268181 : Reach 268181 := rs (se 6 (by rfl) ⟨6285, by rfl⟩) (B 12571 (by norm_num) ⟨6285, by rfl⟩ (by norm_num))
theorem R202661 : Reach 202661 := rs (se 4 (by rfl) ⟨18999, by rfl⟩) (B 37999 (by norm_num) ⟨18999, by rfl⟩ (by norm_num))
theorem R137141 : Reach 137141 := rs (se 5 (by rfl) ⟨6428, by rfl⟩) (B 12857 (by norm_num) ⟨6428, by rfl⟩ (by norm_num))
theorem R104429 : Reach 104429 := rs (se 3 (by rfl) ⟨19580, by rfl⟩) (B 39161 (by norm_num) ⟨19580, by rfl⟩ (by norm_num))
theorem R137213 : Reach 137213 := rs (se 3 (by rfl) ⟨25727, by rfl⟩) (B 51455 (by norm_num) ⟨25727, by rfl⟩ (by norm_num))
theorem R137285 : Reach 137285 := rs (se 4 (by rfl) ⟨12870, by rfl⟩) (B 25741 (by norm_num) ⟨12870, by rfl⟩ (by norm_num))
theorem R301157 : Reach 301157 := rs (se 4 (by rfl) ⟨28233, by rfl⟩) (B 56467 (by norm_num) ⟨28233, by rfl⟩ (by norm_num))
theorem R104557 : Reach 104557 := rs (se 3 (by rfl) ⟨19604, by rfl⟩) (B 39209 (by norm_num) ⟨19604, by rfl⟩ (by norm_num))
theorem R137357 : Reach 137357 := rs (se 3 (by rfl) ⟨25754, by rfl⟩) (B 51509 (by norm_num) ⟨25754, by rfl⟩ (by norm_num))
theorem R104645 : Reach 104645 := rs (se 4 (by rfl) ⟨9810, by rfl⟩) (B 19621 (by norm_num) ⟨9810, by rfl⟩ (by norm_num))
theorem R137429 : Reach 137429 := rs (se 7 (by rfl) ⟨1610, by rfl⟩) (B 3221 (by norm_num) ⟨1610, by rfl⟩ (by norm_num))
theorem R137501 : Reach 137501 := rs (se 3 (by rfl) ⟨25781, by rfl⟩) (B 51563 (by norm_num) ⟨25781, by rfl⟩ (by norm_num))
theorem R104773 : Reach 104773 := rs (se 4 (by rfl) ⟨9822, by rfl⟩) (B 19645 (by norm_num) ⟨9822, by rfl⟩ (by norm_num))
theorem R203093 : Reach 203093 := rs (se 10 (by rfl) ⟨297, by rfl⟩) (B 595 (by norm_num) ⟨297, by rfl⟩ (by norm_num))
theorem R137573 : Reach 137573 := rs (se 4 (by rfl) ⟨12897, by rfl⟩) (B 25795 (by norm_num) ⟨12897, by rfl⟩ (by norm_num))
theorem R104861 : Reach 104861 := rs (se 3 (by rfl) ⟨19661, by rfl⟩) (B 39323 (by norm_num) ⟨19661, by rfl⟩ (by norm_num))
theorem R72101 : Reach 72101 := rs (se 4 (by rfl) ⟨6759, by rfl⟩) (B 13519 (by norm_num) ⟨6759, by rfl⟩ (by norm_num))
theorem R137645 : Reach 137645 := rs (se 3 (by rfl) ⟨25808, by rfl⟩) (B 51617 (by norm_num) ⟨25808, by rfl⟩ (by norm_num))
theorem R137717 : Reach 137717 := rs (se 5 (by rfl) ⟨6455, by rfl⟩) (B 12911 (by norm_num) ⟨6455, by rfl⟩ (by norm_num))
theorem R104989 : Reach 104989 := rs (se 3 (by rfl) ⟨19685, by rfl⟩) (B 39371 (by norm_num) ⟨19685, by rfl⟩ (by norm_num))
theorem R137789 : Reach 137789 := rs (se 3 (by rfl) ⟨25835, by rfl⟩) (B 51671 (by norm_num) ⟨25835, by rfl⟩ (by norm_num))
theorem R105077 : Reach 105077 := rs (se 5 (by rfl) ⟨4925, by rfl⟩) (B 9851 (by norm_num) ⟨4925, by rfl⟩ (by norm_num))
theorem R137861 : Reach 137861 := rs (se 4 (by rfl) ⟨12924, by rfl⟩) (B 25849 (by norm_num) ⟨12924, by rfl⟩ (by norm_num))
theorem R268933 : Reach 268933 := rs (se 4 (by rfl) ⟨25212, by rfl⟩) (B 50425 (by norm_num) ⟨25212, by rfl⟩ (by norm_num))
theorem R72361 : Reach 72361 := rs (se 2 (by rfl) ⟨27135, by rfl⟩) (B 54271 (by norm_num) ⟨27135, by rfl⟩ (by norm_num))
theorem R170677 : Reach 170677 := rs (se 5 (by rfl) ⟨8000, by rfl⟩) (B 16001 (by norm_num) ⟨8000, by rfl⟩ (by norm_num))
theorem R137933 : Reach 137933 := rs (se 3 (by rfl) ⟨25862, by rfl⟩) (B 51725 (by norm_num) ⟨25862, by rfl⟩ (by norm_num))
theorem R72409 : Reach 72409 := rs (se 2 (by rfl) ⟨27153, by rfl⟩) (B 54307 (by norm_num) ⟨27153, by rfl⟩ (by norm_num))
theorem R105205 : Reach 105205 := rs (se 5 (by rfl) ⟨4931, by rfl⟩) (B 9863 (by norm_num) ⟨4931, by rfl⟩ (by norm_num))
theorem R203525 : Reach 203525 := rs (se 4 (by rfl) ⟨19080, by rfl⟩) (B 38161 (by norm_num) ⟨19080, by rfl⟩ (by norm_num))
theorem R138005 : Reach 138005 := rs (se 6 (by rfl) ⟨3234, by rfl⟩) (B 6469 (by norm_num) ⟨3234, by rfl⟩ (by norm_num))
theorem R72481 : Reach 72481 := rs (se 2 (by rfl) ⟨27180, by rfl⟩) (B 54361 (by norm_num) ⟨27180, by rfl⟩ (by norm_num))
theorem R138029 : Reach 138029 := rs (se 3 (by rfl) ⟨25880, by rfl⟩) (B 51761 (by norm_num) ⟨25880, by rfl⟩ (by norm_num))
theorem R105293 : Reach 105293 := rs (se 3 (by rfl) ⟨19742, by rfl⟩) (B 39485 (by norm_num) ⟨19742, by rfl⟩ (by norm_num))
theorem R138077 : Reach 138077 := rs (se 3 (by rfl) ⟨25889, by rfl⟩) (B 51779 (by norm_num) ⟨25889, by rfl⟩ (by norm_num))
theorem R138149 : Reach 138149 := rs (se 4 (by rfl) ⟨12951, by rfl⟩) (B 25903 (by norm_num) ⟨12951, by rfl⟩ (by norm_num))
theorem R105421 : Reach 105421 := rs (se 3 (by rfl) ⟨19766, by rfl⟩) (B 39533 (by norm_num) ⟨19766, by rfl⟩ (by norm_num))
theorem R138221 : Reach 138221 := rs (se 3 (by rfl) ⟨25916, by rfl⟩) (B 51833 (by norm_num) ⟨25916, by rfl⟩ (by norm_num))
theorem R105509 : Reach 105509 := rs (se 4 (by rfl) ⟨9891, by rfl⟩) (B 19783 (by norm_num) ⟨9891, by rfl⟩ (by norm_num))
theorem R138293 : Reach 138293 := rs (se 5 (by rfl) ⟨6482, by rfl⟩) (B 12965 (by norm_num) ⟨6482, by rfl⟩ (by norm_num))
theorem R138341 : Reach 138341 := rs (se 4 (by rfl) ⟨12969, by rfl⟩) (B 25939 (by norm_num) ⟨12969, by rfl⟩ (by norm_num))
theorem R138365 : Reach 138365 := rs (se 3 (by rfl) ⟨25943, by rfl⟩) (B 51887 (by norm_num) ⟨25943, by rfl⟩ (by norm_num))
theorem R105637 : Reach 105637 := rs (se 4 (by rfl) ⟨9903, by rfl⟩) (B 19807 (by norm_num) ⟨9903, by rfl⟩ (by norm_num))
theorem R203957 : Reach 203957 := rs (se 5 (by rfl) ⟨9560, by rfl⟩) (B 19121 (by norm_num) ⟨9560, by rfl⟩ (by norm_num))
theorem R138437 : Reach 138437 := rs (se 4 (by rfl) ⟨12978, by rfl⟩) (B 25957 (by norm_num) ⟨12978, by rfl⟩ (by norm_num))
theorem R204005 : Reach 204005 := rs (se 4 (by rfl) ⟨19125, by rfl⟩) (B 38251 (by norm_num) ⟨19125, by rfl⟩ (by norm_num))
theorem R236789 : Reach 236789 := rs (se 5 (by rfl) ⟨11099, by rfl⟩) (B 22199 (by norm_num) ⟨11099, by rfl⟩ (by norm_num))
theorem R105725 : Reach 105725 := rs (se 3 (by rfl) ⟨19823, by rfl⟩) (B 39647 (by norm_num) ⟨19823, by rfl⟩ (by norm_num))
theorem R138509 : Reach 138509 := rs (se 3 (by rfl) ⟨25970, by rfl⟩) (B 51941 (by norm_num) ⟨25970, by rfl⟩ (by norm_num))
theorem R138581 : Reach 138581 := rs (se 11 (by rfl) ⟨101, by rfl⟩) (B 203 (by norm_num) ⟨101, by rfl⟩ (by norm_num))
theorem R302453 : Reach 302453 := rs (se 5 (by rfl) ⟨14177, by rfl⟩) (B 28355 (by norm_num) ⟨14177, by rfl⟩ (by norm_num))
theorem R73081 : Reach 73081 := rs (se 2 (by rfl) ⟨27405, by rfl⟩) (B 54811 (by norm_num) ⟨27405, by rfl⟩ (by norm_num))
theorem R105853 : Reach 105853 := rs (se 3 (by rfl) ⟨19847, by rfl⟩) (B 39695 (by norm_num) ⟨19847, by rfl⟩ (by norm_num))
theorem R138653 : Reach 138653 := rs (se 3 (by rfl) ⟨25997, by rfl⟩) (B 51995 (by norm_num) ⟨25997, by rfl⟩ (by norm_num))
theorem R335285 : Reach 335285 := rs (se 5 (by rfl) ⟨15716, by rfl⟩) (B 31433 (by norm_num) ⟨15716, by rfl⟩ (by norm_num))
theorem R105941 : Reach 105941 := rs (se 7 (by rfl) ⟨1241, by rfl⟩) (B 2483 (by norm_num) ⟨1241, by rfl⟩ (by norm_num))
theorem R138725 : Reach 138725 := rs (se 4 (by rfl) ⟨13005, by rfl⟩) (B 26011 (by norm_num) ⟨13005, by rfl⟩ (by norm_num))
theorem R237077 : Reach 237077 := rs (se 6 (by rfl) ⟨5556, by rfl⟩) (B 11113 (by norm_num) ⟨5556, by rfl⟩ (by norm_num))
theorem R138797 : Reach 138797 := rs (se 3 (by rfl) ⟨26024, by rfl⟩) (B 52049 (by norm_num) ⟨26024, by rfl⟩ (by norm_num))
theorem R106069 : Reach 106069 := rs (se 8 (by rfl) ⟨621, by rfl⟩) (B 1243 (by norm_num) ⟨621, by rfl⟩ (by norm_num))
theorem R204389 : Reach 204389 := rs (se 4 (by rfl) ⟨19161, by rfl⟩) (B 38323 (by norm_num) ⟨19161, by rfl⟩ (by norm_num))
theorem R138869 : Reach 138869 := rs (se 5 (by rfl) ⟨6509, by rfl⟩) (B 13019 (by norm_num) ⟨6509, by rfl⟩ (by norm_num))
theorem R106157 : Reach 106157 := rs (se 3 (by rfl) ⟨19904, by rfl⟩) (B 39809 (by norm_num) ⟨19904, by rfl⟩ (by norm_num))
theorem R138941 : Reach 138941 := rs (se 3 (by rfl) ⟨26051, by rfl⟩) (B 52103 (by norm_num) ⟨26051, by rfl⟩ (by norm_num))
theorem R139013 : Reach 139013 := rs (se 4 (by rfl) ⟨13032, by rfl⟩) (B 26065 (by norm_num) ⟨13032, by rfl⟩ (by norm_num))
theorem R106285 : Reach 106285 := rs (se 3 (by rfl) ⟨19928, by rfl⟩) (B 39857 (by norm_num) ⟨19928, by rfl⟩ (by norm_num))
theorem R139085 : Reach 139085 := rs (se 3 (by rfl) ⟨26078, by rfl⟩) (B 52157 (by norm_num) ⟨26078, by rfl⟩ (by norm_num))
theorem R106373 : Reach 106373 := rs (se 4 (by rfl) ⟨9972, by rfl⟩) (B 19945 (by norm_num) ⟨9972, by rfl⟩ (by norm_num))
theorem R139157 : Reach 139157 := rs (se 6 (by rfl) ⟨3261, by rfl⟩) (B 6523 (by norm_num) ⟨3261, by rfl⟩ (by norm_num))
theorem R335765 : Reach 335765 := rs (se 6 (by rfl) ⟨7869, by rfl⟩) (B 15739 (by norm_num) ⟨7869, by rfl⟩ (by norm_num))
theorem R139229 : Reach 139229 := rs (se 3 (by rfl) ⟨26105, by rfl⟩) (B 52211 (by norm_num) ⟨26105, by rfl⟩ (by norm_num))
theorem R106501 : Reach 106501 := rs (se 4 (by rfl) ⟨9984, by rfl⟩) (B 19969 (by norm_num) ⟨9984, by rfl⟩ (by norm_num))
theorem R204821 : Reach 204821 := rs (se 6 (by rfl) ⟨4800, by rfl⟩) (B 9601 (by norm_num) ⟨4800, by rfl⟩ (by norm_num))
theorem R139301 : Reach 139301 := rs (se 4 (by rfl) ⟨13059, by rfl⟩) (B 26119 (by norm_num) ⟨13059, by rfl⟩ (by norm_num))
theorem R106565 : Reach 106565 := rs (se 4 (by rfl) ⟨9990, by rfl⟩) (B 19981 (by norm_num) ⟨9990, by rfl⟩ (by norm_num))
theorem R139373 : Reach 139373 := rs (se 3 (by rfl) ⟨26132, by rfl⟩) (B 52265 (by norm_num) ⟨26132, by rfl⟩ (by norm_num))
theorem R172181 : Reach 172181 := rs (se 6 (by rfl) ⟨4035, by rfl⟩) (B 8071 (by norm_num) ⟨4035, by rfl⟩ (by norm_num))
theorem R139445 : Reach 139445 := rs (se 5 (by rfl) ⟨6536, by rfl⟩) (B 13073 (by norm_num) ⟨6536, by rfl⟩ (by norm_num))
theorem R106733 : Reach 106733 := rs (se 3 (by rfl) ⟨20012, by rfl⟩) (B 40025 (by norm_num) ⟨20012, by rfl⟩ (by norm_num))
theorem R139517 : Reach 139517 := rs (se 3 (by rfl) ⟨26159, by rfl⟩) (B 52319 (by norm_num) ⟨26159, by rfl⟩ (by norm_num))
theorem R139589 : Reach 139589 := rs (se 4 (by rfl) ⟨13086, by rfl⟩) (B 26173 (by norm_num) ⟨13086, by rfl⟩ (by norm_num))
theorem R368981 : Reach 368981 := rs (se 10 (by rfl) ⟨540, by rfl⟩) (B 1081 (by norm_num) ⟨540, by rfl⟩ (by norm_num))
theorem R74081 : Reach 74081 := rs (se 2 (by rfl) ⟨27780, by rfl⟩) (B 55561 (by norm_num) ⟨27780, by rfl⟩ (by norm_num))
theorem R139661 : Reach 139661 := rs (se 3 (by rfl) ⟨26186, by rfl⟩) (B 52373 (by norm_num) ⟨26186, by rfl⟩ (by norm_num))
theorem R74153 : Reach 74153 := rs (se 2 (by rfl) ⟨27807, by rfl⟩) (B 55615 (by norm_num) ⟨27807, by rfl⟩ (by norm_num))
theorem R205253 : Reach 205253 := rs (se 4 (by rfl) ⟨19242, by rfl⟩) (B 38485 (by norm_num) ⟨19242, by rfl⟩ (by norm_num))
theorem R139733 : Reach 139733 := rs (se 7 (by rfl) ⟨1637, by rfl⟩) (B 3275 (by norm_num) ⟨1637, by rfl⟩ (by norm_num))
theorem R107021 : Reach 107021 := rs (se 3 (by rfl) ⟨20066, by rfl⟩) (B 40133 (by norm_num) ⟨20066, by rfl⟩ (by norm_num))
theorem R369173 : Reach 369173 := rs (se 6 (by rfl) ⟨8652, by rfl⟩) (B 17305 (by norm_num) ⟨8652, by rfl⟩ (by norm_num))
theorem R139805 : Reach 139805 := rs (se 3 (by rfl) ⟨26213, by rfl⟩) (B 52427 (by norm_num) ⟨26213, by rfl⟩ (by norm_num))
theorem R139877 : Reach 139877 := rs (se 4 (by rfl) ⟨13113, by rfl⟩) (B 26227 (by norm_num) ⟨13113, by rfl⟩ (by norm_num))
theorem R303749 : Reach 303749 := rs (se 4 (by rfl) ⟨28476, by rfl⟩) (B 56953 (by norm_num) ⟨28476, by rfl⟩ (by norm_num))
theorem R139909 : Reach 139909 := rs (se 4 (by rfl) ⟨13116, by rfl⟩) (B 26233 (by norm_num) ⟨13116, by rfl⟩ (by norm_num))
theorem R139949 : Reach 139949 := rs (se 3 (by rfl) ⟨26240, by rfl⟩) (B 52481 (by norm_num) ⟨26240, by rfl⟩ (by norm_num))
theorem R238261 : Reach 238261 := rs (se 5 (by rfl) ⟨11168, by rfl⟩) (B 22337 (by norm_num) ⟨11168, by rfl⟩ (by norm_num))
theorem R74461 : Reach 74461 := rs (se 3 (by rfl) ⟨13961, by rfl⟩) (B 27923 (by norm_num) ⟨13961, by rfl⟩ (by norm_num))
theorem R140021 : Reach 140021 := rs (se 5 (by rfl) ⟨6563, by rfl⟩) (B 13127 (by norm_num) ⟨6563, by rfl⟩ (by norm_num))
theorem R140093 : Reach 140093 := rs (se 3 (by rfl) ⟨26267, by rfl⟩) (B 52535 (by norm_num) ⟨26267, by rfl⟩ (by norm_num))
theorem R107365 : Reach 107365 := rs (se 4 (by rfl) ⟨10065, by rfl⟩) (B 20131 (by norm_num) ⟨10065, by rfl⟩ (by norm_num))
theorem R205685 : Reach 205685 := rs (se 5 (by rfl) ⟨9641, by rfl⟩) (B 19283 (by norm_num) ⟨9641, by rfl⟩ (by norm_num))
theorem R74629 : Reach 74629 := rs (se 4 (by rfl) ⟨6996, by rfl⟩) (B 13993 (by norm_num) ⟨6996, by rfl⟩ (by norm_num))
theorem R140165 : Reach 140165 := rs (se 4 (by rfl) ⟨13140, by rfl⟩) (B 26281 (by norm_num) ⟨13140, by rfl⟩ (by norm_num))
theorem R74677 : Reach 74677 := rs (se 5 (by rfl) ⟨3500, by rfl⟩) (B 7001 (by norm_num) ⟨3500, by rfl⟩ (by norm_num))
theorem R140237 : Reach 140237 := rs (se 3 (by rfl) ⟨26294, by rfl⟩) (B 52589 (by norm_num) ⟨26294, by rfl⟩ (by norm_num))
theorem R238565 : Reach 238565 := rs (se 4 (by rfl) ⟨22365, by rfl⟩) (B 44731 (by norm_num) ⟨22365, by rfl⟩ (by norm_num))
theorem R140293 : Reach 140293 := rs (se 4 (by rfl) ⟨13152, by rfl⟩) (B 26305 (by norm_num) ⟨13152, by rfl⟩ (by norm_num))
theorem R74773 : Reach 74773 := rs (se 6 (by rfl) ⟨1752, by rfl⟩) (B 3505 (by norm_num) ⟨1752, by rfl⟩ (by norm_num))
theorem R140309 : Reach 140309 := rs (se 6 (by rfl) ⟨3288, by rfl⟩) (B 6577 (by norm_num) ⟨3288, by rfl⟩ (by norm_num))
theorem R140381 : Reach 140381 := rs (se 3 (by rfl) ⟨26321, by rfl⟩) (B 52643 (by norm_num) ⟨26321, by rfl⟩ (by norm_num))
theorem R140453 : Reach 140453 := rs (se 4 (by rfl) ⟨13167, by rfl⟩) (B 26335 (by norm_num) ⟨13167, by rfl⟩ (by norm_num))
theorem R74945 : Reach 74945 := rs (se 2 (by rfl) ⟨28104, by rfl⟩) (B 56209 (by norm_num) ⟨28104, by rfl⟩ (by norm_num))
theorem R173285 : Reach 173285 := rs (se 4 (by rfl) ⟨16245, by rfl⟩) (B 32491 (by norm_num) ⟨16245, by rfl⟩ (by norm_num))
theorem R140525 : Reach 140525 := rs (se 3 (by rfl) ⟨26348, by rfl⟩) (B 52697 (by norm_num) ⟨26348, by rfl⟩ (by norm_num))
theorem R402677 : Reach 402677 := rs (se 5 (by rfl) ⟨18875, by rfl⟩) (B 37751 (by norm_num) ⟨18875, by rfl⟩ (by norm_num))
theorem R75001 : Reach 75001 := rs (se 2 (by rfl) ⟨28125, by rfl⟩) (B 56251 (by norm_num) ⟨28125, by rfl⟩ (by norm_num))
theorem R206117 : Reach 206117 := rs (se 4 (by rfl) ⟨19323, by rfl⟩) (B 38647 (by norm_num) ⟨19323, by rfl⟩ (by norm_num))
theorem R140597 : Reach 140597 := rs (se 5 (by rfl) ⟨6590, by rfl⟩) (B 13181 (by norm_num) ⟨6590, by rfl⟩ (by norm_num))
theorem R75097 : Reach 75097 := rs (se 2 (by rfl) ⟨28161, by rfl⟩) (B 56323 (by norm_num) ⟨28161, by rfl⟩ (by norm_num))
theorem R140669 : Reach 140669 := rs (se 3 (by rfl) ⟨26375, by rfl⟩) (B 52751 (by norm_num) ⟨26375, by rfl⟩ (by norm_num))
theorem R140741 : Reach 140741 := rs (se 4 (by rfl) ⟨13194, by rfl⟩) (B 26389 (by norm_num) ⟨13194, by rfl⟩ (by norm_num))
theorem R75269 : Reach 75269 := rs (se 4 (by rfl) ⟨7056, by rfl⟩) (B 14113 (by norm_num) ⟨7056, by rfl⟩ (by norm_num))
theorem R140813 : Reach 140813 := rs (se 3 (by rfl) ⟨26402, by rfl⟩) (B 52805 (by norm_num) ⟨26402, by rfl⟩ (by norm_num))
theorem R75325 : Reach 75325 := rs (se 3 (by rfl) ⟨14123, by rfl⟩) (B 28247 (by norm_num) ⟨14123, by rfl⟩ (by norm_num))
theorem R140885 : Reach 140885 := rs (se 8 (by rfl) ⟨825, by rfl⟩) (B 1651 (by norm_num) ⟨825, by rfl⟩ (by norm_num))
theorem R75349 : Reach 75349 := rs (se 8 (by rfl) ⟨441, by rfl⟩) (B 883 (by norm_num) ⟨441, by rfl⟩ (by norm_num))
theorem R75421 : Reach 75421 := rs (se 3 (by rfl) ⟨14141, by rfl⟩) (B 28283 (by norm_num) ⟨14141, by rfl⟩ (by norm_num))
theorem R140957 : Reach 140957 := rs (se 3 (by rfl) ⟨26429, by rfl⟩) (B 52859 (by norm_num) ⟨26429, by rfl⟩ (by norm_num))
theorem R173765 : Reach 173765 := rs (se 4 (by rfl) ⟨16290, by rfl⟩) (B 32581 (by norm_num) ⟨16290, by rfl⟩ (by norm_num))
theorem R206549 : Reach 206549 := rs (se 7 (by rfl) ⟨2420, by rfl⟩) (B 4841 (by norm_num) ⟨2420, by rfl⟩ (by norm_num))
theorem R108253 : Reach 108253 := rs (se 3 (by rfl) ⟨20297, by rfl⟩) (B 40595 (by norm_num) ⟨20297, by rfl⟩ (by norm_num))
theorem R141029 : Reach 141029 := rs (se 4 (by rfl) ⟨13221, by rfl⟩) (B 26443 (by norm_num) ⟨13221, by rfl⟩ (by norm_num))
theorem R141077 : Reach 141077 := rs (se 6 (by rfl) ⟨3306, by rfl⟩) (B 6613 (by norm_num) ⟨3306, by rfl⟩ (by norm_num))
theorem R108325 : Reach 108325 := rs (se 4 (by rfl) ⟨10155, by rfl⟩) (B 20311 (by norm_num) ⟨10155, by rfl⟩ (by norm_num))
theorem R141101 : Reach 141101 := rs (se 3 (by rfl) ⟨26456, by rfl⟩) (B 52913 (by norm_num) ⟨26456, by rfl⟩ (by norm_num))
theorem R75593 : Reach 75593 := rs (se 2 (by rfl) ⟨28347, by rfl⟩) (B 56695 (by norm_num) ⟨28347, by rfl⟩ (by norm_num))
theorem R141149 : Reach 141149 := rs (se 3 (by rfl) ⟨26465, by rfl⟩) (B 52931 (by norm_num) ⟨26465, by rfl⟩ (by norm_num))
theorem R141173 : Reach 141173 := rs (se 5 (by rfl) ⟨6617, by rfl⟩) (B 13235 (by norm_num) ⟨6617, by rfl⟩ (by norm_num))
theorem R75649 : Reach 75649 := rs (se 2 (by rfl) ⟨28368, by rfl⟩) (B 56737 (by norm_num) ⟨28368, by rfl⟩ (by norm_num))
theorem R305045 : Reach 305045 := rs (se 6 (by rfl) ⟨7149, by rfl⟩) (B 14299 (by norm_num) ⟨7149, by rfl⟩ (by norm_num))
theorem R108469 : Reach 108469 := rs (se 5 (by rfl) ⟨5084, by rfl⟩) (B 10169 (by norm_num) ⟨5084, by rfl⟩ (by norm_num))
theorem R141245 : Reach 141245 := rs (se 3 (by rfl) ⟨26483, by rfl⟩) (B 52967 (by norm_num) ⟨26483, by rfl⟩ (by norm_num))
theorem R75745 : Reach 75745 := rs (se 2 (by rfl) ⟨28404, by rfl⟩) (B 56809 (by norm_num) ⟨28404, by rfl⟩ (by norm_num))
theorem R141317 : Reach 141317 := rs (se 4 (by rfl) ⟨13248, by rfl⟩) (B 26497 (by norm_num) ⟨13248, by rfl⟩ (by norm_num))
theorem R141389 : Reach 141389 := rs (se 3 (by rfl) ⟨26510, by rfl⟩) (B 53021 (by norm_num) ⟨26510, by rfl⟩ (by norm_num))
theorem R206981 : Reach 206981 := rs (se 4 (by rfl) ⟨19404, by rfl⟩) (B 38809 (by norm_num) ⟨19404, by rfl⟩ (by norm_num))
theorem R75917 : Reach 75917 := rs (se 3 (by rfl) ⟨14234, by rfl⟩) (B 28469 (by norm_num) ⟨14234, by rfl⟩ (by norm_num))
theorem R141461 : Reach 141461 := rs (se 6 (by rfl) ⟨3315, by rfl⟩) (B 6631 (by norm_num) ⟨3315, by rfl⟩ (by norm_num))
theorem R75973 : Reach 75973 := rs (se 4 (by rfl) ⟨7122, by rfl⟩) (B 14245 (by norm_num) ⟨7122, by rfl⟩ (by norm_num))
theorem R141533 : Reach 141533 := rs (se 3 (by rfl) ⟨26537, by rfl⟩) (B 53075 (by norm_num) ⟨26537, by rfl⟩ (by norm_num))
theorem R338165 : Reach 338165 := rs (se 5 (by rfl) ⟨15851, by rfl⟩) (B 31703 (by norm_num) ⟨15851, by rfl⟩ (by norm_num))
theorem R698645 : Reach 698645 := rs (se 6 (by rfl) ⟨16374, by rfl⟩) (B 32749 (by norm_num) ⟨16374, by rfl⟩ (by norm_num))
theorem R207125 : Reach 207125 := rs (se 6 (by rfl) ⟨4854, by rfl⟩) (B 9709 (by norm_num) ⟨4854, by rfl⟩ (by norm_num))
theorem R76069 : Reach 76069 := rs (se 4 (by rfl) ⟨7131, by rfl⟩) (B 14263 (by norm_num) ⟨7131, by rfl⟩ (by norm_num))
theorem R141605 : Reach 141605 := rs (se 4 (by rfl) ⟨13275, by rfl⟩) (B 26551 (by norm_num) ⟨13275, by rfl⟩ (by norm_num))
theorem R174437 : Reach 174437 := rs (se 4 (by rfl) ⟨16353, by rfl⟩) (B 32707 (by norm_num) ⟨16353, by rfl⟩ (by norm_num))
theorem R141677 : Reach 141677 := rs (se 3 (by rfl) ⟨26564, by rfl⟩) (B 53129 (by norm_num) ⟨26564, by rfl⟩ (by norm_num))
theorem R108973 : Reach 108973 := rs (se 3 (by rfl) ⟨20432, by rfl⟩) (B 40865 (by norm_num) ⟨20432, by rfl⟩ (by norm_num))
theorem R141749 : Reach 141749 := rs (se 5 (by rfl) ⟨6644, by rfl⟩) (B 13289 (by norm_num) ⟨6644, by rfl⟩ (by norm_num))
theorem R76241 : Reach 76241 := rs (se 2 (by rfl) ⟨28590, by rfl⟩) (B 57181 (by norm_num) ⟨28590, by rfl⟩ (by norm_num))
theorem R141821 : Reach 141821 := rs (se 3 (by rfl) ⟨26591, by rfl⟩) (B 53183 (by norm_num) ⟨26591, by rfl⟩ (by norm_num))
theorem R76297 : Reach 76297 := rs (se 2 (by rfl) ⟨28611, by rfl⟩) (B 57223 (by norm_num) ⟨28611, by rfl⟩ (by norm_num))
theorem R207413 : Reach 207413 := rs (se 5 (by rfl) ⟨9722, by rfl⟩) (B 19445 (by norm_num) ⟨9722, by rfl⟩ (by norm_num))
theorem R404021 : Reach 404021 := rs (se 5 (by rfl) ⟨18938, by rfl⟩) (B 37877 (by norm_num) ⟨18938, by rfl⟩ (by norm_num))
theorem R141893 : Reach 141893 := rs (se 4 (by rfl) ⟨13302, by rfl⟩) (B 26605 (by norm_num) ⟨13302, by rfl⟩ (by norm_num))
theorem R76393 : Reach 76393 := rs (se 2 (by rfl) ⟨28647, by rfl⟩) (B 57295 (by norm_num) ⟨28647, by rfl⟩ (by norm_num))
theorem R141965 : Reach 141965 := rs (se 3 (by rfl) ⟨26618, by rfl⟩) (B 53237 (by norm_num) ⟨26618, by rfl⟩ (by norm_num))
theorem R76565 : Reach 76565 := rs (se 6 (by rfl) ⟨1794, by rfl⟩) (B 3589 (by norm_num) ⟨1794, by rfl⟩ (by norm_num))
theorem R109333 : Reach 109333 := rs (se 6 (by rfl) ⟨2562, by rfl⟩) (B 5125 (by norm_num) ⟨2562, by rfl⟩ (by norm_num))
theorem R174869 : Reach 174869 := rs (se 6 (by rfl) ⟨4098, by rfl⟩) (B 8197 (by norm_num) ⟨4098, by rfl⟩ (by norm_num))
theorem R76621 : Reach 76621 := rs (se 3 (by rfl) ⟨14366, by rfl⟩) (B 28733 (by norm_num) ⟨14366, by rfl⟩ (by norm_num))
theorem R797525 : Reach 797525 := rs (se 9 (by rfl) ⟨2336, by rfl⟩) (B 4673 (by norm_num) ⟨2336, by rfl⟩ (by norm_num))
theorem R109421 : Reach 109421 := rs (se 3 (by rfl) ⟨20516, by rfl⟩) (B 41033 (by norm_num) ⟨20516, by rfl⟩ (by norm_num))
theorem R76717 : Reach 76717 := rs (se 3 (by rfl) ⟨14384, by rfl⟩) (B 28769 (by norm_num) ⟨14384, by rfl⟩ (by norm_num))
theorem R207845 : Reach 207845 := rs (se 4 (by rfl) ⟨19485, by rfl⟩) (B 38971 (by norm_num) ⟨19485, by rfl⟩ (by norm_num))
theorem R142357 : Reach 142357 := rs (se 6 (by rfl) ⟨3336, by rfl⟩) (B 6673 (by norm_num) ⟨3336, by rfl⟩ (by norm_num))
theorem R76889 : Reach 76889 := rs (se 2 (by rfl) ⟨28833, by rfl⟩) (B 57667 (by norm_num) ⟨28833, by rfl⟩ (by norm_num))
theorem R76945 : Reach 76945 := rs (se 2 (by rfl) ⟨28854, by rfl⟩) (B 57709 (by norm_num) ⟨28854, by rfl⟩ (by norm_num))
theorem R306341 : Reach 306341 := rs (se 4 (by rfl) ⟨28719, by rfl⟩) (B 57439 (by norm_num) ⟨28719, by rfl⟩ (by norm_num))
theorem R77041 : Reach 77041 := rs (se 2 (by rfl) ⟨28890, by rfl⟩) (B 57781 (by norm_num) ⟨28890, by rfl⟩ (by norm_num))
theorem R109853 : Reach 109853 := rs (se 3 (by rfl) ⟨20597, by rfl⟩) (B 41195 (by norm_num) ⟨20597, by rfl⟩ (by norm_num))
theorem R339349 : Reach 339349 := rs (se 6 (by rfl) ⟨7953, by rfl⟩) (B 15907 (by norm_num) ⟨7953, by rfl⟩ (by norm_num))
theorem R208277 : Reach 208277 := rs (se 6 (by rfl) ⟨4881, by rfl⟩) (B 9763 (by norm_num) ⟨4881, by rfl⟩ (by norm_num))
theorem R77213 : Reach 77213 := rs (se 3 (by rfl) ⟨14477, by rfl⟩) (B 28955 (by norm_num) ⟨14477, by rfl⟩ (by norm_num))
theorem R77269 : Reach 77269 := rs (se 7 (by rfl) ⟨905, by rfl⟩) (B 1811 (by norm_num) ⟨905, by rfl⟩ (by norm_num))
theorem R175621 : Reach 175621 := rs (se 4 (by rfl) ⟨16464, by rfl⟩) (B 32929 (by norm_num) ⟨16464, by rfl⟩ (by norm_num))
theorem R142877 : Reach 142877 := rs (se 3 (by rfl) ⟨26789, by rfl⟩) (B 53579 (by norm_num) ⟨26789, by rfl⟩ (by norm_num))
theorem R77365 : Reach 77365 := rs (se 5 (by rfl) ⟨3626, by rfl⟩) (B 7253 (by norm_num) ⟨3626, by rfl⟩ (by norm_num))
theorem R110141 : Reach 110141 := rs (se 3 (by rfl) ⟨20651, by rfl⟩) (B 41303 (by norm_num) ⟨20651, by rfl⟩ (by norm_num))
theorem R77537 : Reach 77537 := rs (se 2 (by rfl) ⟨29076, by rfl⟩) (B 58153 (by norm_num) ⟨29076, by rfl⟩ (by norm_num))
theorem R77545 : Reach 77545 := rs (se 2 (by rfl) ⟨29079, by rfl⟩) (B 58159 (by norm_num) ⟨29079, by rfl⟩ (by norm_num))
theorem R77549 : Reach 77549 := rs (se 3 (by rfl) ⟨14540, by rfl⟩) (B 29081 (by norm_num) ⟨14540, by rfl⟩ (by norm_num))
theorem R77593 : Reach 77593 := rs (se 2 (by rfl) ⟨29097, by rfl⟩) (B 58195 (by norm_num) ⟨29097, by rfl⟩ (by norm_num))
theorem R208709 : Reach 208709 := rs (se 4 (by rfl) ⟨19566, by rfl⟩) (B 39133 (by norm_num) ⟨19566, by rfl⟩ (by norm_num))
theorem R77689 : Reach 77689 := rs (se 2 (by rfl) ⟨29133, by rfl⟩) (B 58267 (by norm_num) ⟨29133, by rfl⟩ (by norm_num))
theorem R470933 : Reach 470933 := rs (se 6 (by rfl) ⟨11037, by rfl⟩) (B 22075 (by norm_num) ⟨11037, by rfl⟩ (by norm_num))
theorem R143261 : Reach 143261 := rs (se 3 (by rfl) ⟨26861, by rfl⟩) (B 53723 (by norm_num) ⟨26861, by rfl⟩ (by norm_num))
theorem R143309 : Reach 143309 := rs (se 3 (by rfl) ⟨26870, by rfl⟩) (B 53741 (by norm_num) ⟨26870, by rfl⟩ (by norm_num))
theorem R143317 : Reach 143317 := rs (se 7 (by rfl) ⟨1679, by rfl⟩) (B 3359 (by norm_num) ⟨1679, by rfl⟩ (by norm_num))
theorem R77861 : Reach 77861 := rs (se 4 (by rfl) ⟨7299, by rfl⟩) (B 14599 (by norm_num) ⟨7299, by rfl⟩ (by norm_num))
theorem R77917 : Reach 77917 := rs (se 3 (by rfl) ⟨14609, by rfl⟩) (B 29219 (by norm_num) ⟨14609, by rfl⟩ (by norm_num))
theorem R307381 : Reach 307381 := rs (se 5 (by rfl) ⟨14408, by rfl⟩) (B 28817 (by norm_num) ⟨14408, by rfl⟩ (by norm_num))
theorem R78013 : Reach 78013 := rs (se 3 (by rfl) ⟨14627, by rfl⟩) (B 29255 (by norm_num) ⟨14627, by rfl⟩ (by norm_num))
theorem R209141 : Reach 209141 := rs (se 5 (by rfl) ⟨9803, by rfl⟩) (B 19607 (by norm_num) ⟨9803, by rfl⟩ (by norm_num))
theorem R78185 : Reach 78185 := rs (se 2 (by rfl) ⟨29319, by rfl⟩) (B 58639 (by norm_num) ⟨29319, by rfl⟩ (by norm_num))
theorem R78241 : Reach 78241 := rs (se 2 (by rfl) ⟨29340, by rfl⟩) (B 58681 (by norm_num) ⟨29340, by rfl⟩ (by norm_num))
theorem R307637 : Reach 307637 := rs (se 5 (by rfl) ⟨14420, by rfl⟩) (B 28841 (by norm_num) ⟨14420, by rfl⟩ (by norm_num))
theorem R766421 : Reach 766421 := rs (se 7 (by rfl) ⟨8981, by rfl⟩) (B 17963 (by norm_num) ⟨8981, by rfl⟩ (by norm_num))
theorem R78337 : Reach 78337 := rs (se 2 (by rfl) ⟨29376, by rfl⟩) (B 58753 (by norm_num) ⟨29376, by rfl⟩ (by norm_num))
theorem R209429 : Reach 209429 := rs (se 6 (by rfl) ⟨4908, by rfl⟩) (B 9817 (by norm_num) ⟨4908, by rfl⟩ (by norm_num))
theorem R209573 : Reach 209573 := rs (se 4 (by rfl) ⟨19647, by rfl⟩) (B 39295 (by norm_num) ⟨19647, by rfl⟩ (by norm_num))
theorem R78509 : Reach 78509 := rs (se 3 (by rfl) ⟨14720, by rfl⟩) (B 29441 (by norm_num) ⟨14720, by rfl⟩ (by norm_num))
theorem R78565 : Reach 78565 := rs (se 4 (by rfl) ⟨7365, by rfl⟩) (B 14731 (by norm_num) ⟨7365, by rfl⟩ (by norm_num))
theorem R78661 : Reach 78661 := rs (se 4 (by rfl) ⟨7374, by rfl⟩) (B 14749 (by norm_num) ⟨7374, by rfl⟩ (by norm_num))
theorem R144317 : Reach 144317 := rs (se 3 (by rfl) ⟨27059, by rfl⟩) (B 54119 (by norm_num) ⟨27059, by rfl⟩ (by norm_num))
theorem R210005 : Reach 210005 := rs (se 8 (by rfl) ⟨1230, by rfl⟩) (B 2461 (by norm_num) ⟨1230, by rfl⟩ (by norm_num))
theorem R144509 : Reach 144509 := rs (se 3 (by rfl) ⟨27095, by rfl⟩) (B 54191 (by norm_num) ⟨27095, by rfl⟩ (by norm_num))
theorem R79157 : Reach 79157 := rs (se 5 (by rfl) ⟨3710, by rfl⟩) (B 7421 (by norm_num) ⟨3710, by rfl⟩ (by norm_num))
theorem R341333 : Reach 341333 := rs (se 13 (by rfl) ⟨62, by rfl⟩) (B 125 (by norm_num) ⟨62, by rfl⟩ (by norm_num))
theorem R79213 : Reach 79213 := rs (se 3 (by rfl) ⟨14852, by rfl⟩) (B 29705 (by norm_num) ⟨14852, by rfl⟩ (by norm_num))
theorem R79309 : Reach 79309 := rs (se 3 (by rfl) ⟨14870, by rfl⟩) (B 29741 (by norm_num) ⟨14870, by rfl⟩ (by norm_num))
theorem R210437 : Reach 210437 := rs (se 4 (by rfl) ⟨19728, by rfl⟩) (B 39457 (by norm_num) ⟨19728, by rfl⟩ (by norm_num))
theorem R308933 : Reach 308933 := rs (se 4 (by rfl) ⟨28962, by rfl⟩) (B 57925 (by norm_num) ⟨28962, by rfl⟩ (by norm_num))
theorem R112357 : Reach 112357 := rs (se 4 (by rfl) ⟨10533, by rfl⟩) (B 21067 (by norm_num) ⟨10533, by rfl⟩ (by norm_num))
theorem R210869 : Reach 210869 := rs (se 5 (by rfl) ⟨9884, by rfl⟩) (B 19769 (by norm_num) ⟨9884, by rfl⟩ (by norm_num))
theorem R79805 : Reach 79805 := rs (se 3 (by rfl) ⟨14963, by rfl⟩) (B 29927 (by norm_num) ⟨14963, by rfl⟩ (by norm_num))
theorem R79861 : Reach 79861 := rs (se 5 (by rfl) ⟨3743, by rfl⟩) (B 7487 (by norm_num) ⟨3743, by rfl⟩ (by norm_num))
theorem R112661 : Reach 112661 := rs (se 6 (by rfl) ⟨2640, by rfl⟩) (B 5281 (by norm_num) ⟨2640, by rfl⟩ (by norm_num))
theorem R276517 : Reach 276517 := rs (se 4 (by rfl) ⟨25923, by rfl⟩) (B 51847 (by norm_num) ⟨25923, by rfl⟩ (by norm_num))
theorem R112765 : Reach 112765 := rs (se 3 (by rfl) ⟨21143, by rfl⟩) (B 42287 (by norm_num) ⟨21143, by rfl⟩ (by norm_num))
theorem R112909 : Reach 112909 := rs (se 3 (by rfl) ⟨21170, by rfl⟩) (B 42341 (by norm_num) ⟨21170, by rfl⟩ (by norm_num))
theorem R178469 : Reach 178469 := rs (se 4 (by rfl) ⟨16731, by rfl⟩) (B 33463 (by norm_num) ⟨16731, by rfl⟩ (by norm_num))
theorem R211285 : Reach 211285 := rs (se 10 (by rfl) ⟨309, by rfl⟩) (B 619 (by norm_num) ⟨309, by rfl⟩ (by norm_num))
theorem R211301 : Reach 211301 := rs (se 4 (by rfl) ⟨19809, by rfl⟩) (B 39619 (by norm_num) ⟨19809, by rfl⟩ (by norm_num))
theorem R80357 : Reach 80357 := rs (se 4 (by rfl) ⟨7533, by rfl⟩) (B 15067 (by norm_num) ⟨7533, by rfl⟩ (by norm_num))
theorem R113333 : Reach 113333 := rs (se 5 (by rfl) ⟨5312, by rfl⟩) (B 10625 (by norm_num) ⟨5312, by rfl⟩ (by norm_num))
theorem R113413 : Reach 113413 := rs (se 4 (by rfl) ⟨10632, by rfl⟩) (B 21265 (by norm_num) ⟨10632, by rfl⟩ (by norm_num))
theorem R211733 : Reach 211733 := rs (se 6 (by rfl) ⟨4962, by rfl⟩) (B 9925 (by norm_num) ⟨4962, by rfl⟩ (by norm_num))
theorem R80669 : Reach 80669 := rs (se 3 (by rfl) ⟨15125, by rfl⟩) (B 30251 (by norm_num) ⟨15125, by rfl⟩ (by norm_num))
theorem R113485 : Reach 113485 := rs (se 3 (by rfl) ⟨21278, by rfl⟩) (B 42557 (by norm_num) ⟨21278, by rfl⟩ (by norm_num))
theorem R113557 : Reach 113557 := rs (se 6 (by rfl) ⟨2661, by rfl⟩) (B 5323 (by norm_num) ⟨2661, by rfl⟩ (by norm_num))
theorem R506837 : Reach 506837 := rs (se 7 (by rfl) ⟨5939, by rfl⟩) (B 11879 (by norm_num) ⟨5939, by rfl⟩ (by norm_num))
theorem R310229 : Reach 310229 := rs (se 7 (by rfl) ⟨3635, by rfl⟩) (B 7271 (by norm_num) ⟨3635, by rfl⟩ (by norm_num))
theorem R146461 : Reach 146461 := rs (se 3 (by rfl) ⟨27461, by rfl⟩) (B 54923 (by norm_num) ⟨27461, by rfl⟩ (by norm_num))
theorem R80941 : Reach 80941 := rs (se 3 (by rfl) ⟨15176, by rfl⟩) (B 30353 (by norm_num) ⟨15176, by rfl⟩ (by norm_num))
theorem R113717 : Reach 113717 := rs (se 5 (by rfl) ⟨5330, by rfl⟩) (B 10661 (by norm_num) ⟨5330, by rfl⟩ (by norm_num))
theorem R179381 : Reach 179381 := rs (se 5 (by rfl) ⟨8408, by rfl⟩) (B 16817 (by norm_num) ⟨8408, by rfl⟩ (by norm_num))
theorem R113861 : Reach 113861 := rs (se 4 (by rfl) ⟨10674, by rfl⟩) (B 21349 (by norm_num) ⟨10674, by rfl⟩ (by norm_num))
theorem R212165 : Reach 212165 := rs (se 4 (by rfl) ⟨19890, by rfl⟩) (B 39781 (by norm_num) ⟨19890, by rfl⟩ (by norm_num))
theorem R572629 : Reach 572629 := rs (se 7 (by rfl) ⟨6710, by rfl⟩) (B 13421 (by norm_num) ⟨6710, by rfl⟩ (by norm_num))
theorem R179653 : Reach 179653 := rs (se 4 (by rfl) ⟨16842, by rfl⟩) (B 33685 (by norm_num) ⟨16842, by rfl⟩ (by norm_num))
theorem R114149 : Reach 114149 := rs (se 4 (by rfl) ⟨10701, by rfl⟩) (B 21403 (by norm_num) ⟨10701, by rfl⟩ (by norm_num))
theorem R343541 : Reach 343541 := rs (se 5 (by rfl) ⟨16103, by rfl⟩) (B 32207 (by norm_num) ⟨16103, by rfl⟩ (by norm_num))
theorem R605717 : Reach 605717 := rs (se 6 (by rfl) ⟨14196, by rfl⟩) (B 28393 (by norm_num) ⟨14196, by rfl⟩ (by norm_num))
theorem R212597 : Reach 212597 := rs (se 5 (by rfl) ⟨9965, by rfl⟩) (B 19931 (by norm_num) ⟨9965, by rfl⟩ (by norm_num))
theorem R114301 : Reach 114301 := rs (se 3 (by rfl) ⟨21431, by rfl⟩) (B 42863 (by norm_num) ⟨21431, by rfl⟩ (by norm_num))
theorem R245413 : Reach 245413 := rs (se 4 (by rfl) ⟨23007, by rfl⟩) (B 46015 (by norm_num) ⟨23007, by rfl⟩ (by norm_num))
theorem R704213 : Reach 704213 := rs (se 7 (by rfl) ⟨8252, by rfl⟩) (B 16505 (by norm_num) ⟨8252, by rfl⟩ (by norm_num))
theorem R540437 : Reach 540437 := rs (se 6 (by rfl) ⟨12666, by rfl⟩) (B 25333 (by norm_num) ⟨12666, by rfl⟩ (by norm_num))
theorem R180053 : Reach 180053 := rs (se 9 (by rfl) ⟨527, by rfl⟩) (B 1055 (by norm_num) ⟨527, by rfl⟩ (by norm_num))
theorem R114605 : Reach 114605 := rs (se 3 (by rfl) ⟨21488, by rfl⟩) (B 42977 (by norm_num) ⟨21488, by rfl⟩ (by norm_num))
theorem R507829 : Reach 507829 := rs (se 5 (by rfl) ⟨23804, by rfl⟩) (B 47609 (by norm_num) ⟨23804, by rfl⟩ (by norm_num))
theorem R147413 : Reach 147413 := rs (se 7 (by rfl) ⟨1727, by rfl⟩) (B 3455 (by norm_num) ⟨1727, by rfl⟩ (by norm_num))
theorem R147469 : Reach 147469 := rs (se 3 (by rfl) ⟨27650, by rfl⟩) (B 55301 (by norm_num) ⟨27650, by rfl⟩ (by norm_num))
theorem R213029 : Reach 213029 := rs (se 4 (by rfl) ⟨19971, by rfl⟩) (B 39943 (by norm_num) ⟨19971, by rfl⟩ (by norm_num))
theorem R311525 : Reach 311525 := rs (se 4 (by rfl) ⟨29205, by rfl⟩) (B 58411 (by norm_num) ⟨29205, by rfl⟩ (by norm_num))
theorem R540917 : Reach 540917 := rs (se 5 (by rfl) ⟨25355, by rfl⟩) (B 50711 (by norm_num) ⟨25355, by rfl⟩ (by norm_num))
theorem R147845 : Reach 147845 := rs (se 4 (by rfl) ⟨13860, by rfl⟩) (B 27721 (by norm_num) ⟨13860, by rfl⟩ (by norm_num))
theorem R148085 : Reach 148085 := rs (se 5 (by rfl) ⟨6941, by rfl⟩) (B 13883 (by norm_num) ⟨6941, by rfl⟩ (by norm_num))
theorem R115357 : Reach 115357 := rs (se 3 (by rfl) ⟨21629, by rfl⟩) (B 43259 (by norm_num) ⟨21629, by rfl⟩ (by norm_num))
theorem R180949 : Reach 180949 := rs (se 7 (by rfl) ⟨2120, by rfl⟩) (B 4241 (by norm_num) ⟨2120, by rfl⟩ (by norm_num))
theorem R115501 : Reach 115501 := rs (se 3 (by rfl) ⟨21656, by rfl⟩) (B 43313 (by norm_num) ⟨21656, by rfl⟩ (by norm_num))
theorem R148277 : Reach 148277 := rs (se 5 (by rfl) ⟨6950, by rfl⟩) (B 13901 (by norm_num) ⟨6950, by rfl⟩ (by norm_num))
theorem R115661 : Reach 115661 := rs (se 3 (by rfl) ⟨21686, by rfl⟩) (B 43373 (by norm_num) ⟨21686, by rfl⟩ (by norm_num))
theorem R115805 : Reach 115805 := rs (se 3 (by rfl) ⟨21713, by rfl⟩) (B 43427 (by norm_num) ⟨21713, by rfl⟩ (by norm_num))
theorem R83317 : Reach 83317 := rs (se 5 (by rfl) ⟨3905, by rfl⟩) (B 7811 (by norm_num) ⟨3905, by rfl⟩ (by norm_num))
theorem R247157 : Reach 247157 := rs (se 5 (by rfl) ⟨11585, by rfl⟩) (B 23171 (by norm_num) ⟨11585, by rfl⟩ (by norm_num))
theorem R116093 : Reach 116093 := rs (se 3 (by rfl) ⟨21767, by rfl⟩) (B 43535 (by norm_num) ⟨21767, by rfl⟩ (by norm_num))
theorem R312821 : Reach 312821 := rs (se 5 (by rfl) ⟨14663, by rfl⟩) (B 29327 (by norm_num) ⟨14663, by rfl⟩ (by norm_num))
theorem R116245 : Reach 116245 := rs (se 6 (by rfl) ⟨2724, by rfl⟩) (B 5449 (by norm_num) ⟨2724, by rfl⟩ (by norm_num))
theorem R214805 : Reach 214805 := rs (se 6 (by rfl) ⟨5034, by rfl⟩) (B 10069 (by norm_num) ⟨5034, by rfl⟩ (by norm_num))
theorem R116549 : Reach 116549 := rs (se 4 (by rfl) ⟨10926, by rfl⟩) (B 21853 (by norm_num) ⟨10926, by rfl⟩ (by norm_num))
theorem R509813 : Reach 509813 := rs (se 5 (by rfl) ⟨23897, by rfl⟩) (B 47795 (by norm_num) ⟨23897, by rfl⟩ (by norm_num))
theorem R313237 : Reach 313237 := rs (se 6 (by rfl) ⟨7341, by rfl⟩) (B 14683 (by norm_num) ⟨7341, by rfl⟩ (by norm_num))
theorem R247781 : Reach 247781 := rs (se 4 (by rfl) ⟨23229, by rfl⟩) (B 46459 (by norm_num) ⟨23229, by rfl⟩ (by norm_num))
theorem R215237 : Reach 215237 := rs (se 4 (by rfl) ⟨20178, by rfl⟩) (B 40357 (by norm_num) ⟨20178, by rfl⟩ (by norm_num))
theorem R84245 : Reach 84245 := rs (se 6 (by rfl) ⟨1974, by rfl⟩) (B 3949 (by norm_num) ⟨1974, by rfl⟩ (by norm_num))
theorem R149789 : Reach 149789 := rs (se 3 (by rfl) ⟨28085, by rfl⟩) (B 56171 (by norm_num) ⟨28085, by rfl⟩ (by norm_num))
theorem R117301 : Reach 117301 := rs (se 5 (by rfl) ⟨5498, by rfl⟩) (B 10997 (by norm_num) ⟨5498, by rfl⟩ (by norm_num))
theorem R150133 : Reach 150133 := rs (se 5 (by rfl) ⟨7037, by rfl⟩) (B 14075 (by norm_num) ⟨7037, by rfl⟩ (by norm_num))
theorem R248453 : Reach 248453 := rs (se 4 (by rfl) ⟨23292, by rfl⟩) (B 46585 (by norm_num) ⟨23292, by rfl⟩ (by norm_num))
theorem R117445 : Reach 117445 := rs (se 4 (by rfl) ⟨11010, by rfl⟩) (B 22021 (by norm_num) ⟨11010, by rfl⟩ (by norm_num))
theorem R150245 : Reach 150245 := rs (se 4 (by rfl) ⟨14085, by rfl⟩) (B 28171 (by norm_num) ⟨14085, by rfl⟩ (by norm_num))
theorem R314117 : Reach 314117 := rs (se 4 (by rfl) ⟨29448, by rfl⟩) (B 58897 (by norm_num) ⟨29448, by rfl⟩ (by norm_num))
theorem R117605 : Reach 117605 := rs (se 4 (by rfl) ⟨11025, by rfl⟩) (B 22051 (by norm_num) ⟨11025, by rfl⟩ (by norm_num))
theorem R150437 : Reach 150437 := rs (se 4 (by rfl) ⟨14103, by rfl⟩) (B 28207 (by norm_num) ⟨14103, by rfl⟩ (by norm_num))
theorem R117749 : Reach 117749 := rs (se 5 (by rfl) ⟨5519, by rfl⟩) (B 11039 (by norm_num) ⟨5519, by rfl⟩ (by norm_num))
theorem R84997 : Reach 84997 := rs (se 4 (by rfl) ⟨7968, by rfl⟩) (B 15937 (by norm_num) ⟨7968, by rfl⟩ (by norm_num))
theorem R150781 : Reach 150781 := rs (se 3 (by rfl) ⟨28271, by rfl⟩) (B 56543 (by norm_num) ⟨28271, by rfl⟩ (by norm_num))
theorem R118037 : Reach 118037 := rs (se 6 (by rfl) ⟨2766, by rfl⟩) (B 5533 (by norm_num) ⟨2766, by rfl⟩ (by norm_num))
theorem R150893 : Reach 150893 := rs (se 3 (by rfl) ⟨28292, by rfl⟩) (B 56585 (by norm_num) ⟨28292, by rfl⟩ (by norm_num))
theorem R118189 : Reach 118189 := rs (se 3 (by rfl) ⟨22160, by rfl⟩) (B 44321 (by norm_num) ⟨22160, by rfl⟩ (by norm_num))
theorem R478709 : Reach 478709 := rs (se 5 (by rfl) ⟨22439, by rfl⟩) (B 44879 (by norm_num) ⟨22439, by rfl⟩ (by norm_num))
theorem R151085 : Reach 151085 := rs (se 3 (by rfl) ⟨28328, by rfl⟩) (B 56657 (by norm_num) ⟨28328, by rfl⟩ (by norm_num))
theorem R380533 : Reach 380533 := rs (se 5 (by rfl) ⟨17837, by rfl⟩) (B 35675 (by norm_num) ⟨17837, by rfl⟩ (by norm_num))
theorem R151237 : Reach 151237 := rs (se 4 (by rfl) ⟨14178, by rfl⟩) (B 28357 (by norm_num) ⟨14178, by rfl⟩ (by norm_num))
theorem R118493 : Reach 118493 := rs (se 3 (by rfl) ⟨22217, by rfl⟩) (B 44435 (by norm_num) ⟨22217, by rfl⟩ (by norm_num))
theorem R216821 : Reach 216821 := rs (se 5 (by rfl) ⟨10163, by rfl⟩) (B 20327 (by norm_num) ⟨10163, by rfl⟩ (by norm_num))
theorem R85765 : Reach 85765 := rs (se 4 (by rfl) ⟨8040, by rfl⟩) (B 16081 (by norm_num) ⟨8040, by rfl⟩ (by norm_num))
theorem R85789 : Reach 85789 := rs (se 3 (by rfl) ⟨16085, by rfl⟩) (B 32171 (by norm_num) ⟨16085, by rfl⟩ (by norm_num))
theorem R151429 : Reach 151429 := rs (se 4 (by rfl) ⟨14196, by rfl⟩) (B 28393 (by norm_num) ⟨14196, by rfl⟩ (by norm_num))
theorem R282533 : Reach 282533 := rs (se 4 (by rfl) ⟨26487, by rfl⟩) (B 52975 (by norm_num) ⟨26487, by rfl⟩ (by norm_num))
theorem R249797 : Reach 249797 := rs (se 4 (by rfl) ⟨23418, by rfl⟩) (B 46837 (by norm_num) ⟨23418, by rfl⟩ (by norm_num))
theorem R151541 : Reach 151541 := rs (se 5 (by rfl) ⟨7103, by rfl⟩) (B 14207 (by norm_num) ⟨7103, by rfl⟩ (by norm_num))
theorem R315413 : Reach 315413 := rs (se 6 (by rfl) ⟨7392, by rfl⟩) (B 14785 (by norm_num) ⟨7392, by rfl⟩ (by norm_num))
theorem R86125 : Reach 86125 := rs (se 3 (by rfl) ⟨16148, by rfl⟩) (B 32297 (by norm_num) ⟨16148, by rfl⟩ (by norm_num))
theorem R151733 : Reach 151733 := rs (se 5 (by rfl) ⟨7112, by rfl⟩) (B 14225 (by norm_num) ⟨7112, by rfl⟩ (by norm_num))
theorem R86341 : Reach 86341 := rs (se 4 (by rfl) ⟨8094, by rfl⟩) (B 16189 (by norm_num) ⟨8094, by rfl⟩ (by norm_num))
theorem R119173 : Reach 119173 := rs (se 4 (by rfl) ⟨11172, by rfl⟩) (B 22345 (by norm_num) ⟨11172, by rfl⟩ (by norm_num))
theorem R119245 : Reach 119245 := rs (se 3 (by rfl) ⟨22358, by rfl⟩) (B 44717 (by norm_num) ⟨22358, by rfl⟩ (by norm_num))
theorem R152077 : Reach 152077 := rs (se 3 (by rfl) ⟨28514, by rfl⟩) (B 57029 (by norm_num) ⟨28514, by rfl⟩ (by norm_num))
theorem R119389 : Reach 119389 := rs (se 3 (by rfl) ⟨22385, by rfl⟩) (B 44771 (by norm_num) ⟨22385, by rfl⟩ (by norm_num))
theorem R152189 : Reach 152189 := rs (se 3 (by rfl) ⟨28535, by rfl⟩) (B 57071 (by norm_num) ⟨28535, by rfl⟩ (by norm_num))
theorem R86717 : Reach 86717 := rs (se 3 (by rfl) ⟨16259, by rfl⟩) (B 32519 (by norm_num) ⟨16259, by rfl⟩ (by norm_num))
theorem R119549 : Reach 119549 := rs (se 3 (by rfl) ⟨22415, by rfl⟩) (B 44831 (by norm_num) ⟨22415, by rfl⟩ (by norm_num))
theorem R152381 : Reach 152381 := rs (se 3 (by rfl) ⟨28571, by rfl⟩) (B 57143 (by norm_num) ⟨28571, by rfl⟩ (by norm_num))
theorem R119693 : Reach 119693 := rs (se 3 (by rfl) ⟨22442, by rfl⟩) (B 44885 (by norm_num) ⟨22442, by rfl⟩ (by norm_num))
theorem R1004501 : Reach 1004501 := rs (se 7 (by rfl) ⟨11771, by rfl⟩) (B 23543 (by norm_num) ⟨11771, by rfl⟩ (by norm_num))
theorem R152725 : Reach 152725 := rs (se 6 (by rfl) ⟨3579, by rfl⟩) (B 7159 (by norm_num) ⟨3579, by rfl⟩ (by norm_num))
theorem R152837 : Reach 152837 := rs (se 4 (by rfl) ⟨14328, by rfl⟩) (B 28657 (by norm_num) ⟨14328, by rfl⟩ (by norm_num))
theorem R153029 : Reach 153029 := rs (se 4 (by rfl) ⟨14346, by rfl⟩) (B 28693 (by norm_num) ⟨14346, by rfl⟩ (by norm_num))
theorem R153341 : Reach 153341 := rs (se 3 (by rfl) ⟨28751, by rfl⟩) (B 57503 (by norm_num) ⟨28751, by rfl⟩ (by norm_num))
theorem R153373 : Reach 153373 := rs (se 3 (by rfl) ⟨28757, by rfl⟩) (B 57515 (by norm_num) ⟨28757, by rfl⟩ (by norm_num))
theorem R153485 : Reach 153485 := rs (se 3 (by rfl) ⟨28778, by rfl⟩) (B 57557 (by norm_num) ⟨28778, by rfl⟩ (by norm_num))
theorem R153677 : Reach 153677 := rs (se 3 (by rfl) ⟨28814, by rfl⟩) (B 57629 (by norm_num) ⟨28814, by rfl⟩ (by norm_num))
theorem R88141 : Reach 88141 := rs (se 3 (by rfl) ⟨16526, by rfl⟩) (B 33053 (by norm_num) ⟨16526, by rfl⟩ (by norm_num))
theorem R284789 : Reach 284789 := rs (se 5 (by rfl) ⟨13349, by rfl⟩) (B 26699 (by norm_num) ⟨13349, by rfl⟩ (by norm_num))
theorem R154021 : Reach 154021 := rs (se 4 (by rfl) ⟨14439, by rfl⟩) (B 28879 (by norm_num) ⟨14439, by rfl⟩ (by norm_num))
theorem R154133 : Reach 154133 := rs (se 6 (by rfl) ⟨3612, by rfl⟩) (B 7225 (by norm_num) ⟨3612, by rfl⟩ (by norm_num))
theorem R318005 : Reach 318005 := rs (se 5 (by rfl) ⟨14906, by rfl⟩) (B 29813 (by norm_num) ⟨14906, by rfl⟩ (by norm_num))
theorem R88685 : Reach 88685 := rs (se 3 (by rfl) ⟨16628, by rfl⟩) (B 33257 (by norm_num) ⟨16628, by rfl⟩ (by norm_num))
theorem R88709 : Reach 88709 := rs (se 4 (by rfl) ⟨8316, by rfl⟩) (B 16633 (by norm_num) ⟨8316, by rfl⟩ (by norm_num))
theorem R88733 : Reach 88733 := rs (se 3 (by rfl) ⟨16637, by rfl⟩) (B 33275 (by norm_num) ⟨16637, by rfl⟩ (by norm_num))
theorem R88757 : Reach 88757 := rs (se 5 (by rfl) ⟨4160, by rfl⟩) (B 8321 (by norm_num) ⟨4160, by rfl⟩ (by norm_num))
theorem R88781 : Reach 88781 := rs (se 3 (by rfl) ⟨16646, by rfl⟩) (B 33293 (by norm_num) ⟨16646, by rfl⟩ (by norm_num))
theorem R154325 : Reach 154325 := rs (se 7 (by rfl) ⟨1808, by rfl⟩) (B 3617 (by norm_num) ⟨1808, by rfl⟩ (by norm_num))
theorem R88805 : Reach 88805 := rs (se 4 (by rfl) ⟨8325, by rfl⟩) (B 16651 (by norm_num) ⟨8325, by rfl⟩ (by norm_num))
theorem R88813 : Reach 88813 := rs (se 3 (by rfl) ⟨16652, by rfl⟩) (B 33305 (by norm_num) ⟨16652, by rfl⟩ (by norm_num))
theorem R88829 : Reach 88829 := rs (se 3 (by rfl) ⟨16655, by rfl⟩) (B 33311 (by norm_num) ⟨16655, by rfl⟩ (by norm_num))
theorem R88853 : Reach 88853 := rs (se 6 (by rfl) ⟨2082, by rfl⟩) (B 4165 (by norm_num) ⟨2082, by rfl⟩ (by norm_num))
theorem R88877 : Reach 88877 := rs (se 3 (by rfl) ⟨16664, by rfl⟩) (B 33329 (by norm_num) ⟨16664, by rfl⟩ (by norm_num))
theorem R88901 : Reach 88901 := rs (se 4 (by rfl) ⟨8334, by rfl⟩) (B 16669 (by norm_num) ⟨8334, by rfl⟩ (by norm_num))
theorem R88925 : Reach 88925 := rs (se 3 (by rfl) ⟨16673, by rfl⟩) (B 33347 (by norm_num) ⟨16673, by rfl⟩ (by norm_num))
theorem R154469 : Reach 154469 := rs (se 4 (by rfl) ⟨14481, by rfl⟩) (B 28963 (by norm_num) ⟨14481, by rfl⟩ (by norm_num))
theorem R88933 : Reach 88933 := rs (se 4 (by rfl) ⟨8337, by rfl⟩) (B 16675 (by norm_num) ⟨8337, by rfl⟩ (by norm_num))
theorem R88949 : Reach 88949 := rs (se 5 (by rfl) ⟨4169, by rfl⟩) (B 8339 (by norm_num) ⟨4169, by rfl⟩ (by norm_num))
theorem R88973 : Reach 88973 := rs (se 3 (by rfl) ⟨16682, by rfl⟩) (B 33365 (by norm_num) ⟨16682, by rfl⟩ (by norm_num))
theorem R88997 : Reach 88997 := rs (se 4 (by rfl) ⟨8343, by rfl⟩) (B 16687 (by norm_num) ⟨8343, by rfl⟩ (by norm_num))
theorem R89021 : Reach 89021 := rs (se 3 (by rfl) ⟨16691, by rfl⟩) (B 33383 (by norm_num) ⟨16691, by rfl⟩ (by norm_num))
theorem R89029 : Reach 89029 := rs (se 4 (by rfl) ⟨8346, by rfl⟩) (B 16693 (by norm_num) ⟨8346, by rfl⟩ (by norm_num))
theorem R89045 : Reach 89045 := rs (se 7 (by rfl) ⟨1043, by rfl⟩) (B 2087 (by norm_num) ⟨1043, by rfl⟩ (by norm_num))
theorem R89069 : Reach 89069 := rs (se 3 (by rfl) ⟨16700, by rfl⟩) (B 33401 (by norm_num) ⟨16700, by rfl⟩ (by norm_num))
theorem R89093 : Reach 89093 := rs (se 4 (by rfl) ⟨8352, by rfl⟩) (B 16705 (by norm_num) ⟨8352, by rfl⟩ (by norm_num))
theorem R89117 : Reach 89117 := rs (se 3 (by rfl) ⟨16709, by rfl⟩) (B 33419 (by norm_num) ⟨16709, by rfl⟩ (by norm_num))
theorem R154669 : Reach 154669 := rs (se 3 (by rfl) ⟨29000, by rfl⟩) (B 58001 (by norm_num) ⟨29000, by rfl⟩ (by norm_num))
theorem R89141 : Reach 89141 := rs (se 5 (by rfl) ⟨4178, by rfl⟩) (B 8357 (by norm_num) ⟨4178, by rfl⟩ (by norm_num))
theorem R89165 : Reach 89165 := rs (se 3 (by rfl) ⟨16718, by rfl⟩) (B 33437 (by norm_num) ⟨16718, by rfl⟩ (by norm_num))
theorem R89189 : Reach 89189 := rs (se 4 (by rfl) ⟨8361, by rfl⟩) (B 16723 (by norm_num) ⟨8361, by rfl⟩ (by norm_num))
theorem R89213 : Reach 89213 := rs (se 3 (by rfl) ⟨16727, by rfl⟩) (B 33455 (by norm_num) ⟨16727, by rfl⟩ (by norm_num))
theorem R89237 : Reach 89237 := rs (se 6 (by rfl) ⟨2091, by rfl⟩) (B 4183 (by norm_num) ⟨2091, by rfl⟩ (by norm_num))
theorem R154781 : Reach 154781 := rs (se 3 (by rfl) ⟨29021, by rfl⟩) (B 58043 (by norm_num) ⟨29021, by rfl⟩ (by norm_num))
theorem R89261 : Reach 89261 := rs (se 3 (by rfl) ⟨16736, by rfl⟩) (B 33473 (by norm_num) ⟨16736, by rfl⟩ (by norm_num))
theorem R89285 : Reach 89285 := rs (se 4 (by rfl) ⟨8370, by rfl⟩) (B 16741 (by norm_num) ⟨8370, by rfl⟩ (by norm_num))
theorem R89309 : Reach 89309 := rs (se 3 (by rfl) ⟨16745, by rfl⟩) (B 33491 (by norm_num) ⟨16745, by rfl⟩ (by norm_num))
theorem R89333 : Reach 89333 := rs (se 5 (by rfl) ⟨4187, by rfl⟩) (B 8375 (by norm_num) ⟨4187, by rfl⟩ (by norm_num))
theorem R89357 : Reach 89357 := rs (se 3 (by rfl) ⟨16754, by rfl⟩) (B 33509 (by norm_num) ⟨16754, by rfl⟩ (by norm_num))
theorem R89381 : Reach 89381 := rs (se 4 (by rfl) ⟨8379, by rfl⟩) (B 16759 (by norm_num) ⟨8379, by rfl⟩ (by norm_num))
theorem R89405 : Reach 89405 := rs (se 3 (by rfl) ⟨16763, by rfl⟩) (B 33527 (by norm_num) ⟨16763, by rfl⟩ (by norm_num))
theorem R89413 : Reach 89413 := rs (se 4 (by rfl) ⟨8382, by rfl⟩) (B 16765 (by norm_num) ⟨8382, by rfl⟩ (by norm_num))
theorem R89429 : Reach 89429 := rs (se 11 (by rfl) ⟨65, by rfl⟩) (B 131 (by norm_num) ⟨65, by rfl⟩ (by norm_num))
theorem R154973 : Reach 154973 := rs (se 3 (by rfl) ⟨29057, by rfl⟩) (B 58115 (by norm_num) ⟨29057, by rfl⟩ (by norm_num))
theorem R89453 : Reach 89453 := rs (se 3 (by rfl) ⟨16772, by rfl⟩) (B 33545 (by norm_num) ⟨16772, by rfl⟩ (by norm_num))
theorem R89477 : Reach 89477 := rs (se 4 (by rfl) ⟨8388, by rfl⟩) (B 16777 (by norm_num) ⟨8388, by rfl⟩ (by norm_num))
theorem R89501 : Reach 89501 := rs (se 3 (by rfl) ⟨16781, by rfl⟩) (B 33563 (by norm_num) ⟨16781, by rfl⟩ (by norm_num))
theorem R89525 : Reach 89525 := rs (se 5 (by rfl) ⟨4196, by rfl⟩) (B 8393 (by norm_num) ⟨4196, by rfl⟩ (by norm_num))
theorem R253381 : Reach 253381 := rs (se 4 (by rfl) ⟨23754, by rfl⟩) (B 47509 (by norm_num) ⟨23754, by rfl⟩ (by norm_num))
theorem R89549 : Reach 89549 := rs (se 3 (by rfl) ⟨16790, by rfl⟩) (B 33581 (by norm_num) ⟨16790, by rfl⟩ (by norm_num))
theorem R89573 : Reach 89573 := rs (se 4 (by rfl) ⟨8397, by rfl⟩) (B 16795 (by norm_num) ⟨8397, by rfl⟩ (by norm_num))
theorem R89597 : Reach 89597 := rs (se 3 (by rfl) ⟨16799, by rfl⟩) (B 33599 (by norm_num) ⟨16799, by rfl⟩ (by norm_num))
theorem R286213 : Reach 286213 := rs (se 4 (by rfl) ⟨26832, by rfl⟩) (B 53665 (by norm_num) ⟨26832, by rfl⟩ (by norm_num))
theorem R89621 : Reach 89621 := rs (se 6 (by rfl) ⟨2100, by rfl⟩) (B 4201 (by norm_num) ⟨2100, by rfl⟩ (by norm_num))
theorem R89645 : Reach 89645 := rs (se 3 (by rfl) ⟨16808, by rfl⟩) (B 33617 (by norm_num) ⟨16808, by rfl⟩ (by norm_num))
theorem R89669 : Reach 89669 := rs (se 4 (by rfl) ⟨8406, by rfl⟩) (B 16813 (by norm_num) ⟨8406, by rfl⟩ (by norm_num))
theorem R89693 : Reach 89693 := rs (se 3 (by rfl) ⟨16817, by rfl⟩) (B 33635 (by norm_num) ⟨16817, by rfl⟩ (by norm_num))
theorem R89717 : Reach 89717 := rs (se 5 (by rfl) ⟨4205, by rfl⟩) (B 8411 (by norm_num) ⟨4205, by rfl⟩ (by norm_num))
theorem R89741 : Reach 89741 := rs (se 3 (by rfl) ⟨16826, by rfl⟩) (B 33653 (by norm_num) ⟨16826, by rfl⟩ (by norm_num))
theorem R89765 : Reach 89765 := rs (se 4 (by rfl) ⟨8415, by rfl⟩) (B 16831 (by norm_num) ⟨8415, by rfl⟩ (by norm_num))
theorem R155317 : Reach 155317 := rs (se 5 (by rfl) ⟨7280, by rfl⟩) (B 14561 (by norm_num) ⟨7280, by rfl⟩ (by norm_num))
theorem R89789 : Reach 89789 := rs (se 3 (by rfl) ⟨16835, by rfl⟩) (B 33671 (by norm_num) ⟨16835, by rfl⟩ (by norm_num))
theorem R89813 : Reach 89813 := rs (se 7 (by rfl) ⟨1052, by rfl⟩) (B 2105 (by norm_num) ⟨1052, by rfl⟩ (by norm_num))
theorem R89837 : Reach 89837 := rs (se 3 (by rfl) ⟨16844, by rfl⟩) (B 33689 (by norm_num) ⟨16844, by rfl⟩ (by norm_num))
theorem R89861 : Reach 89861 := rs (se 4 (by rfl) ⟨8424, by rfl⟩) (B 16849 (by norm_num) ⟨8424, by rfl⟩ (by norm_num))
theorem R89885 : Reach 89885 := rs (se 3 (by rfl) ⟨16853, by rfl⟩) (B 33707 (by norm_num) ⟨16853, by rfl⟩ (by norm_num))
theorem R155429 : Reach 155429 := rs (se 4 (by rfl) ⟨14571, by rfl⟩) (B 29143 (by norm_num) ⟨14571, by rfl⟩ (by norm_num))
theorem R89909 : Reach 89909 := rs (se 5 (by rfl) ⟨4214, by rfl⟩) (B 8429 (by norm_num) ⟨4214, by rfl⟩ (by norm_num))
theorem R384821 : Reach 384821 := rs (se 5 (by rfl) ⟨18038, by rfl⟩) (B 36077 (by norm_num) ⟨18038, by rfl⟩ (by norm_num))
theorem R89933 : Reach 89933 := rs (se 3 (by rfl) ⟨16862, by rfl⟩) (B 33725 (by norm_num) ⟨16862, by rfl⟩ (by norm_num))
theorem R89957 : Reach 89957 := rs (se 4 (by rfl) ⟨8433, by rfl⟩) (B 16867 (by norm_num) ⟨8433, by rfl⟩ (by norm_num))
theorem R253813 : Reach 253813 := rs (se 5 (by rfl) ⟨11897, by rfl⟩) (B 23795 (by norm_num) ⟨11897, by rfl⟩ (by norm_num))
theorem R89981 : Reach 89981 := rs (se 3 (by rfl) ⟨16871, by rfl⟩) (B 33743 (by norm_num) ⟨16871, by rfl⟩ (by norm_num))
theorem R253829 : Reach 253829 := rs (se 4 (by rfl) ⟨23796, by rfl⟩) (B 47593 (by norm_num) ⟨23796, by rfl⟩ (by norm_num))
theorem R90005 : Reach 90005 := rs (se 6 (by rfl) ⟨2109, by rfl⟩) (B 4219 (by norm_num) ⟨2109, by rfl⟩ (by norm_num))
theorem R90029 : Reach 90029 := rs (se 3 (by rfl) ⟨16880, by rfl⟩) (B 33761 (by norm_num) ⟨16880, by rfl⟩ (by norm_num))
theorem R90053 : Reach 90053 := rs (se 4 (by rfl) ⟨8442, by rfl⟩) (B 16885 (by norm_num) ⟨8442, by rfl⟩ (by norm_num))
theorem R90077 : Reach 90077 := rs (se 3 (by rfl) ⟨16889, by rfl⟩) (B 33779 (by norm_num) ⟨16889, by rfl⟩ (by norm_num))
theorem R155621 : Reach 155621 := rs (se 4 (by rfl) ⟨14589, by rfl⟩) (B 29179 (by norm_num) ⟨14589, by rfl⟩ (by norm_num))
theorem R90101 : Reach 90101 := rs (se 5 (by rfl) ⟨4223, by rfl⟩) (B 8447 (by norm_num) ⟨4223, by rfl⟩ (by norm_num))
theorem R90125 : Reach 90125 := rs (se 3 (by rfl) ⟨16898, by rfl⟩) (B 33797 (by norm_num) ⟨16898, by rfl⟩ (by norm_num))
theorem R90149 : Reach 90149 := rs (se 4 (by rfl) ⟨8451, by rfl⟩) (B 16903 (by norm_num) ⟨8451, by rfl⟩ (by norm_num))
theorem R90173 : Reach 90173 := rs (se 3 (by rfl) ⟨16907, by rfl⟩) (B 33815 (by norm_num) ⟨16907, by rfl⟩ (by norm_num))
theorem R90197 : Reach 90197 := rs (se 8 (by rfl) ⟨528, by rfl⟩) (B 1057 (by norm_num) ⟨528, by rfl⟩ (by norm_num))
theorem R90221 : Reach 90221 := rs (se 3 (by rfl) ⟨16916, by rfl⟩) (B 33833 (by norm_num) ⟨16916, by rfl⟩ (by norm_num))
theorem R90245 : Reach 90245 := rs (se 4 (by rfl) ⟨8460, by rfl⟩) (B 16921 (by norm_num) ⟨8460, by rfl⟩ (by norm_num))
theorem R90269 : Reach 90269 := rs (se 3 (by rfl) ⟨16925, by rfl⟩) (B 33851 (by norm_num) ⟨16925, by rfl⟩ (by norm_num))
theorem R90293 : Reach 90293 := rs (se 5 (by rfl) ⟨4232, by rfl⟩) (B 8465 (by norm_num) ⟨4232, by rfl⟩ (by norm_num))
theorem R90317 : Reach 90317 := rs (se 3 (by rfl) ⟨16934, by rfl⟩) (B 33869 (by norm_num) ⟨16934, by rfl⟩ (by norm_num))
theorem R90341 : Reach 90341 := rs (se 4 (by rfl) ⟨8469, by rfl⟩) (B 16939 (by norm_num) ⟨8469, by rfl⟩ (by norm_num))
theorem R90365 : Reach 90365 := rs (se 3 (by rfl) ⟨16943, by rfl⟩) (B 33887 (by norm_num) ⟨16943, by rfl⟩ (by norm_num))
theorem R90389 : Reach 90389 := rs (se 6 (by rfl) ⟨2118, by rfl⟩) (B 4237 (by norm_num) ⟨2118, by rfl⟩ (by norm_num))
theorem R90413 : Reach 90413 := rs (se 3 (by rfl) ⟨16952, by rfl⟩) (B 33905 (by norm_num) ⟨16952, by rfl⟩ (by norm_num))
theorem R155965 : Reach 155965 := rs (se 3 (by rfl) ⟨29243, by rfl⟩) (B 58487 (by norm_num) ⟨29243, by rfl⟩ (by norm_num))
theorem R90437 : Reach 90437 := rs (se 4 (by rfl) ⟨8478, by rfl⟩) (B 16957 (by norm_num) ⟨8478, by rfl⟩ (by norm_num))
theorem R90445 : Reach 90445 := rs (se 3 (by rfl) ⟨16958, by rfl⟩) (B 33917 (by norm_num) ⟨16958, by rfl⟩ (by norm_num))
theorem R90461 : Reach 90461 := rs (se 3 (by rfl) ⟨16961, by rfl⟩) (B 33923 (by norm_num) ⟨16961, by rfl⟩ (by norm_num))
theorem R90485 : Reach 90485 := rs (se 5 (by rfl) ⟨4241, by rfl⟩) (B 8483 (by norm_num) ⟨4241, by rfl⟩ (by norm_num))
theorem R90509 : Reach 90509 := rs (se 3 (by rfl) ⟨16970, by rfl⟩) (B 33941 (by norm_num) ⟨16970, by rfl⟩ (by norm_num))
theorem R90533 : Reach 90533 := rs (se 4 (by rfl) ⟨8487, by rfl⟩) (B 16975 (by norm_num) ⟨8487, by rfl⟩ (by norm_num))
theorem R156077 : Reach 156077 := rs (se 3 (by rfl) ⟨29264, by rfl⟩) (B 58529 (by norm_num) ⟨29264, by rfl⟩ (by norm_num))
theorem R90557 : Reach 90557 := rs (se 3 (by rfl) ⟨16979, by rfl⟩) (B 33959 (by norm_num) ⟨16979, by rfl⟩ (by norm_num))
theorem R90581 : Reach 90581 := rs (se 7 (by rfl) ⟨1061, by rfl⟩) (B 2123 (by norm_num) ⟨1061, by rfl⟩ (by norm_num))
theorem R90605 : Reach 90605 := rs (se 3 (by rfl) ⟨16988, by rfl⟩) (B 33977 (by norm_num) ⟨16988, by rfl⟩ (by norm_num))
theorem R90629 : Reach 90629 := rs (se 4 (by rfl) ⟨8496, by rfl⟩) (B 16993 (by norm_num) ⟨8496, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R90653 : Reach 90653 := rs (se 3 (by rfl) ⟨16997, by rfl⟩) (B 33995 (by norm_num) ⟨16997, by rfl⟩ (by norm_num))
theorem R90677 : Reach 90677 := rs (se 5 (by rfl) ⟨4250, by rfl⟩) (B 8501 (by norm_num) ⟨4250, by rfl⟩ (by norm_num))
theorem R90701 : Reach 90701 := rs (se 3 (by rfl) ⟨17006, by rfl⟩) (B 34013 (by norm_num) ⟨17006, by rfl⟩ (by norm_num))
theorem R90725 : Reach 90725 := rs (se 4 (by rfl) ⟨8505, by rfl⟩) (B 17011 (by norm_num) ⟨8505, by rfl⟩ (by norm_num))
theorem R156269 : Reach 156269 := rs (se 3 (by rfl) ⟨29300, by rfl⟩) (B 58601 (by norm_num) ⟨29300, by rfl⟩ (by norm_num))
theorem R90749 : Reach 90749 := rs (se 3 (by rfl) ⟨17015, by rfl⟩) (B 34031 (by norm_num) ⟨17015, by rfl⟩ (by norm_num))
theorem R90773 : Reach 90773 := rs (se 6 (by rfl) ⟨2127, by rfl⟩) (B 4255 (by norm_num) ⟨2127, by rfl⟩ (by norm_num))
theorem R90797 : Reach 90797 := rs (se 3 (by rfl) ⟨17024, by rfl⟩) (B 34049 (by norm_num) ⟨17024, by rfl⟩ (by norm_num))
theorem R90821 : Reach 90821 := rs (se 4 (by rfl) ⟨8514, by rfl⟩) (B 17029 (by norm_num) ⟨8514, by rfl⟩ (by norm_num))
theorem R320213 : Reach 320213 := rs (se 7 (by rfl) ⟨3752, by rfl⟩) (B 7505 (by norm_num) ⟨3752, by rfl⟩ (by norm_num))
theorem R90845 : Reach 90845 := rs (se 3 (by rfl) ⟨17033, by rfl⟩) (B 34067 (by norm_num) ⟨17033, by rfl⟩ (by norm_num))
theorem R90869 : Reach 90869 := rs (se 5 (by rfl) ⟨4259, by rfl⟩) (B 8519 (by norm_num) ⟨4259, by rfl⟩ (by norm_num))
theorem R90893 : Reach 90893 := rs (se 3 (by rfl) ⟨17042, by rfl⟩) (B 34085 (by norm_num) ⟨17042, by rfl⟩ (by norm_num))
theorem R90917 : Reach 90917 := rs (se 4 (by rfl) ⟨8523, by rfl⟩) (B 17047 (by norm_num) ⟨8523, by rfl⟩ (by norm_num))
theorem R90941 : Reach 90941 := rs (se 3 (by rfl) ⟨17051, by rfl⟩) (B 34103 (by norm_num) ⟨17051, by rfl⟩ (by norm_num))
theorem R90965 : Reach 90965 := rs (se 9 (by rfl) ⟨266, by rfl⟩) (B 533 (by norm_num) ⟨266, by rfl⟩ (by norm_num))
theorem R90989 : Reach 90989 := rs (se 3 (by rfl) ⟨17060, by rfl⟩) (B 34121 (by norm_num) ⟨17060, by rfl⟩ (by norm_num))
theorem R91013 : Reach 91013 := rs (se 4 (by rfl) ⟨8532, by rfl⟩) (B 17065 (by norm_num) ⟨8532, by rfl⟩ (by norm_num))
theorem R91037 : Reach 91037 := rs (se 3 (by rfl) ⟨17069, by rfl⟩) (B 34139 (by norm_num) ⟨17069, by rfl⟩ (by norm_num))
theorem R91061 : Reach 91061 := rs (se 5 (by rfl) ⟨4268, by rfl⟩) (B 8537 (by norm_num) ⟨4268, by rfl⟩ (by norm_num))
theorem R156613 : Reach 156613 := rs (se 4 (by rfl) ⟨14682, by rfl⟩) (B 29365 (by norm_num) ⟨14682, by rfl⟩ (by norm_num))
theorem R91085 : Reach 91085 := rs (se 3 (by rfl) ⟨17078, by rfl⟩) (B 34157 (by norm_num) ⟨17078, by rfl⟩ (by norm_num))
theorem R91109 : Reach 91109 := rs (se 4 (by rfl) ⟨8541, by rfl⟩) (B 17083 (by norm_num) ⟨8541, by rfl⟩ (by norm_num))
theorem R91133 : Reach 91133 := rs (se 3 (by rfl) ⟨17087, by rfl⟩) (B 34175 (by norm_num) ⟨17087, by rfl⟩ (by norm_num))
theorem R91157 : Reach 91157 := rs (se 6 (by rfl) ⟨2136, by rfl⟩) (B 4273 (by norm_num) ⟨2136, by rfl⟩ (by norm_num))
theorem R91181 : Reach 91181 := rs (se 3 (by rfl) ⟨17096, by rfl⟩) (B 34193 (by norm_num) ⟨17096, by rfl⟩ (by norm_num))
theorem R156725 : Reach 156725 := rs (se 5 (by rfl) ⟨7346, by rfl⟩) (B 14693 (by norm_num) ⟨7346, by rfl⟩ (by norm_num))
theorem R91205 : Reach 91205 := rs (se 4 (by rfl) ⟨8550, by rfl⟩) (B 17101 (by norm_num) ⟨8550, by rfl⟩ (by norm_num))
theorem R91229 : Reach 91229 := rs (se 3 (by rfl) ⟨17105, by rfl⟩) (B 34211 (by norm_num) ⟨17105, by rfl⟩ (by norm_num))
theorem R91253 : Reach 91253 := rs (se 5 (by rfl) ⟨4277, by rfl⟩) (B 8555 (by norm_num) ⟨4277, by rfl⟩ (by norm_num))
theorem R91277 : Reach 91277 := rs (se 3 (by rfl) ⟨17114, by rfl⟩) (B 34229 (by norm_num) ⟨17114, by rfl⟩ (by norm_num))
theorem R353429 : Reach 353429 := rs (se 6 (by rfl) ⟨8283, by rfl⟩) (B 16567 (by norm_num) ⟨8283, by rfl⟩ (by norm_num))
theorem R91301 : Reach 91301 := rs (se 4 (by rfl) ⟨8559, by rfl⟩) (B 17119 (by norm_num) ⟨8559, by rfl⟩ (by norm_num))
theorem R91325 : Reach 91325 := rs (se 3 (by rfl) ⟨17123, by rfl⟩) (B 34247 (by norm_num) ⟨17123, by rfl⟩ (by norm_num))
theorem R91349 : Reach 91349 := rs (se 7 (by rfl) ⟨1070, by rfl⟩) (B 2141 (by norm_num) ⟨1070, by rfl⟩ (by norm_num))
theorem R91373 : Reach 91373 := rs (se 3 (by rfl) ⟨17132, by rfl⟩) (B 34265 (by norm_num) ⟨17132, by rfl⟩ (by norm_num))
theorem R156917 : Reach 156917 := rs (se 5 (by rfl) ⟨7355, by rfl⟩) (B 14711 (by norm_num) ⟨7355, by rfl⟩ (by norm_num))
theorem R91397 : Reach 91397 := rs (se 4 (by rfl) ⟨8568, by rfl⟩) (B 17137 (by norm_num) ⟨8568, by rfl⟩ (by norm_num))
theorem R91421 : Reach 91421 := rs (se 3 (by rfl) ⟨17141, by rfl⟩) (B 34283 (by norm_num) ⟨17141, by rfl⟩ (by norm_num))
theorem R517429 : Reach 517429 := rs (se 5 (by rfl) ⟨24254, by rfl⟩) (B 48509 (by norm_num) ⟨24254, by rfl⟩ (by norm_num))
theorem R91445 : Reach 91445 := rs (se 5 (by rfl) ⟨4286, by rfl⟩) (B 8573 (by norm_num) ⟨4286, by rfl⟩ (by norm_num))
theorem R222533 : Reach 222533 := rs (se 4 (by rfl) ⟨20862, by rfl⟩) (B 41725 (by norm_num) ⟨20862, by rfl⟩ (by norm_num))
theorem R91469 : Reach 91469 := rs (se 3 (by rfl) ⟨17150, by rfl⟩) (B 34301 (by norm_num) ⟨17150, by rfl⟩ (by norm_num))
theorem R451925 : Reach 451925 := rs (se 12 (by rfl) ⟨165, by rfl⟩) (B 331 (by norm_num) ⟨165, by rfl⟩ (by norm_num))
theorem R91493 : Reach 91493 := rs (se 4 (by rfl) ⟨8577, by rfl⟩) (B 17155 (by norm_num) ⟨8577, by rfl⟩ (by norm_num))
theorem R91517 : Reach 91517 := rs (se 3 (by rfl) ⟨17159, by rfl⟩) (B 34319 (by norm_num) ⟨17159, by rfl⟩ (by norm_num))
theorem R91541 : Reach 91541 := rs (se 6 (by rfl) ⟨2145, by rfl⟩) (B 4291 (by norm_num) ⟨2145, by rfl⟩ (by norm_num))
theorem R91565 : Reach 91565 := rs (se 3 (by rfl) ⟨17168, by rfl⟩) (B 34337 (by norm_num) ⟨17168, by rfl⟩ (by norm_num))
theorem R91589 : Reach 91589 := rs (se 4 (by rfl) ⟨8586, by rfl⟩) (B 17173 (by norm_num) ⟨8586, by rfl⟩ (by norm_num))
theorem R91613 : Reach 91613 := rs (se 3 (by rfl) ⟨17177, by rfl⟩) (B 34355 (by norm_num) ⟨17177, by rfl⟩ (by norm_num))
theorem R91637 : Reach 91637 := rs (se 5 (by rfl) ⟨4295, by rfl⟩) (B 8591 (by norm_num) ⟨4295, by rfl⟩ (by norm_num))
theorem R91661 : Reach 91661 := rs (se 3 (by rfl) ⟨17186, by rfl⟩) (B 34373 (by norm_num) ⟨17186, by rfl⟩ (by norm_num))
theorem R189989 : Reach 189989 := rs (se 4 (by rfl) ⟨17811, by rfl⟩) (B 35623 (by norm_num) ⟨17811, by rfl⟩ (by norm_num))
theorem R91685 : Reach 91685 := rs (se 4 (by rfl) ⟨8595, by rfl⟩) (B 17191 (by norm_num) ⟨8595, by rfl⟩ (by norm_num))
theorem R91709 : Reach 91709 := rs (se 3 (by rfl) ⟨17195, by rfl⟩) (B 34391 (by norm_num) ⟨17195, by rfl⟩ (by norm_num))
theorem R157261 : Reach 157261 := rs (se 3 (by rfl) ⟨29486, by rfl⟩) (B 58973 (by norm_num) ⟨29486, by rfl⟩ (by norm_num))
theorem R91733 : Reach 91733 := rs (se 8 (by rfl) ⟨537, by rfl⟩) (B 1075 (by norm_num) ⟨537, by rfl⟩ (by norm_num))
theorem R157277 : Reach 157277 := rs (se 3 (by rfl) ⟨29489, by rfl⟩) (B 58979 (by norm_num) ⟨29489, by rfl⟩ (by norm_num))
theorem R91757 : Reach 91757 := rs (se 3 (by rfl) ⟨17204, by rfl⟩) (B 34409 (by norm_num) ⟨17204, by rfl⟩ (by norm_num))
theorem R91781 : Reach 91781 := rs (se 4 (by rfl) ⟨8604, by rfl⟩) (B 17209 (by norm_num) ⟨8604, by rfl⟩ (by norm_num))
theorem R91805 : Reach 91805 := rs (se 3 (by rfl) ⟨17213, by rfl⟩) (B 34427 (by norm_num) ⟨17213, by rfl⟩ (by norm_num))
theorem R91829 : Reach 91829 := rs (se 5 (by rfl) ⟨4304, by rfl⟩) (B 8609 (by norm_num) ⟨4304, by rfl⟩ (by norm_num))
theorem R91837 : Reach 91837 := rs (se 3 (by rfl) ⟨17219, by rfl⟩) (B 34439 (by norm_num) ⟨17219, by rfl⟩ (by norm_num))
theorem R157373 : Reach 157373 := rs (se 3 (by rfl) ⟨29507, by rfl⟩) (B 59015 (by norm_num) ⟨29507, by rfl⟩ (by norm_num))
theorem R91853 : Reach 91853 := rs (se 3 (by rfl) ⟨17222, by rfl⟩) (B 34445 (by norm_num) ⟨17222, by rfl⟩ (by norm_num))
theorem R91877 : Reach 91877 := rs (se 4 (by rfl) ⟨8613, by rfl⟩) (B 17227 (by norm_num) ⟨8613, by rfl⟩ (by norm_num))
theorem R59125 : Reach 59125 := rs (se 5 (by rfl) ⟨2771, by rfl⟩) (B 5543 (by norm_num) ⟨2771, by rfl⟩ (by norm_num))
theorem R59129 : Reach 59129 := rs (se 2 (by rfl) ⟨22173, by rfl⟩) (B 44347 (by norm_num) ⟨22173, by rfl⟩ (by norm_num))
theorem R59133 : Reach 59133 := rs (se 3 (by rfl) ⟨11087, by rfl⟩) (B 22175 (by norm_num) ⟨11087, by rfl⟩ (by norm_num))
theorem R91901 : Reach 91901 := rs (se 3 (by rfl) ⟨17231, by rfl⟩) (B 34463 (by norm_num) ⟨17231, by rfl⟩ (by norm_num))
theorem R59137 : Reach 59137 := rs (se 2 (by rfl) ⟨22176, by rfl⟩) (B 44353 (by norm_num) ⟨22176, by rfl⟩ (by norm_num))
theorem R59141 : Reach 59141 := rs (se 4 (by rfl) ⟨5544, by rfl⟩) (B 11089 (by norm_num) ⟨5544, by rfl⟩ (by norm_num))
theorem R59145 : Reach 59145 := rs (se 2 (by rfl) ⟨22179, by rfl⟩) (B 44359 (by norm_num) ⟨22179, by rfl⟩ (by norm_num))
theorem R59149 : Reach 59149 := rs (se 3 (by rfl) ⟨11090, by rfl⟩) (B 22181 (by norm_num) ⟨11090, by rfl⟩ (by norm_num))
theorem R59153 : Reach 59153 := rs (se 2 (by rfl) ⟨22182, by rfl⟩) (B 44365 (by norm_num) ⟨22182, by rfl⟩ (by norm_num))
theorem R59157 : Reach 59157 := rs (se 6 (by rfl) ⟨1386, by rfl⟩) (B 2773 (by norm_num) ⟨1386, by rfl⟩ (by norm_num))
theorem R91925 : Reach 91925 := rs (se 6 (by rfl) ⟨2154, by rfl⟩) (B 4309 (by norm_num) ⟨2154, by rfl⟩ (by norm_num))
theorem R59161 : Reach 59161 := rs (se 2 (by rfl) ⟨22185, by rfl⟩) (B 44371 (by norm_num) ⟨22185, by rfl⟩ (by norm_num))
theorem R59165 : Reach 59165 := rs (se 3 (by rfl) ⟨11093, by rfl⟩) (B 22187 (by norm_num) ⟨11093, by rfl⟩ (by norm_num))
theorem R59169 : Reach 59169 := rs (se 2 (by rfl) ⟨22188, by rfl⟩) (B 44377 (by norm_num) ⟨22188, by rfl⟩ (by norm_num))
theorem R59173 : Reach 59173 := rs (se 4 (by rfl) ⟨5547, by rfl⟩) (B 11095 (by norm_num) ⟨5547, by rfl⟩ (by norm_num))
theorem R59177 : Reach 59177 := rs (se 2 (by rfl) ⟨22191, by rfl⟩) (B 44383 (by norm_num) ⟨22191, by rfl⟩ (by norm_num))
theorem R59181 : Reach 59181 := rs (se 3 (by rfl) ⟨11096, by rfl⟩) (B 22193 (by norm_num) ⟨11096, by rfl⟩ (by norm_num))
theorem R91949 : Reach 91949 := rs (se 3 (by rfl) ⟨17240, by rfl⟩) (B 34481 (by norm_num) ⟨17240, by rfl⟩ (by norm_num))
theorem R59185 : Reach 59185 := rs (se 2 (by rfl) ⟨22194, by rfl⟩) (B 44389 (by norm_num) ⟨22194, by rfl⟩ (by norm_num))
theorem R59189 : Reach 59189 := rs (se 5 (by rfl) ⟨2774, by rfl⟩) (B 5549 (by norm_num) ⟨2774, by rfl⟩ (by norm_num))
theorem R59193 : Reach 59193 := rs (se 2 (by rfl) ⟨22197, by rfl⟩) (B 44395 (by norm_num) ⟨22197, by rfl⟩ (by norm_num))
theorem R59197 : Reach 59197 := rs (se 3 (by rfl) ⟨11099, by rfl⟩) (B 22199 (by norm_num) ⟨11099, by rfl⟩ (by norm_num))
theorem R59201 : Reach 59201 := rs (se 2 (by rfl) ⟨22200, by rfl⟩) (B 44401 (by norm_num) ⟨22200, by rfl⟩ (by norm_num))
theorem R59205 : Reach 59205 := rs (se 4 (by rfl) ⟨5550, by rfl⟩) (B 11101 (by norm_num) ⟨5550, by rfl⟩ (by norm_num))
theorem R91973 : Reach 91973 := rs (se 4 (by rfl) ⟨8622, by rfl⟩) (B 17245 (by norm_num) ⟨8622, by rfl⟩ (by norm_num))
theorem R59209 : Reach 59209 := rs (se 2 (by rfl) ⟨22203, by rfl⟩) (B 44407 (by norm_num) ⟨22203, by rfl⟩ (by norm_num))
theorem R59213 : Reach 59213 := rs (se 3 (by rfl) ⟨11102, by rfl⟩) (B 22205 (by norm_num) ⟨11102, by rfl⟩ (by norm_num))
theorem R59217 : Reach 59217 := rs (se 2 (by rfl) ⟨22206, by rfl⟩) (B 44413 (by norm_num) ⟨22206, by rfl⟩ (by norm_num))
theorem R59221 : Reach 59221 := rs (se 9 (by rfl) ⟨173, by rfl⟩) (B 347 (by norm_num) ⟨173, by rfl⟩ (by norm_num))
theorem R59225 : Reach 59225 := rs (se 2 (by rfl) ⟨22209, by rfl⟩) (B 44419 (by norm_num) ⟨22209, by rfl⟩ (by norm_num))
theorem R59229 : Reach 59229 := rs (se 3 (by rfl) ⟨11105, by rfl⟩) (B 22211 (by norm_num) ⟨11105, by rfl⟩ (by norm_num))
theorem R91997 : Reach 91997 := rs (se 3 (by rfl) ⟨17249, by rfl⟩) (B 34499 (by norm_num) ⟨17249, by rfl⟩ (by norm_num))
theorem R59233 : Reach 59233 := rs (se 2 (by rfl) ⟨22212, by rfl⟩) (B 44425 (by norm_num) ⟨22212, by rfl⟩ (by norm_num))
theorem R59237 : Reach 59237 := rs (se 4 (by rfl) ⟨5553, by rfl⟩) (B 11107 (by norm_num) ⟨5553, by rfl⟩ (by norm_num))
theorem R59241 : Reach 59241 := rs (se 2 (by rfl) ⟨22215, by rfl⟩) (B 44431 (by norm_num) ⟨22215, by rfl⟩ (by norm_num))
theorem R59245 : Reach 59245 := rs (se 3 (by rfl) ⟨11108, by rfl⟩) (B 22217 (by norm_num) ⟨11108, by rfl⟩ (by norm_num))
theorem R59249 : Reach 59249 := rs (se 2 (by rfl) ⟨22218, by rfl⟩) (B 44437 (by norm_num) ⟨22218, by rfl⟩ (by norm_num))
theorem R59253 : Reach 59253 := rs (se 5 (by rfl) ⟨2777, by rfl⟩) (B 5555 (by norm_num) ⟨2777, by rfl⟩ (by norm_num))
theorem R92021 : Reach 92021 := rs (se 5 (by rfl) ⟨4313, by rfl⟩) (B 8627 (by norm_num) ⟨4313, by rfl⟩ (by norm_num))
theorem R59257 : Reach 59257 := rs (se 2 (by rfl) ⟨22221, by rfl⟩) (B 44443 (by norm_num) ⟨22221, by rfl⟩ (by norm_num))
theorem R59261 : Reach 59261 := rs (se 3 (by rfl) ⟨11111, by rfl⟩) (B 22223 (by norm_num) ⟨11111, by rfl⟩ (by norm_num))
theorem R157565 : Reach 157565 := rs (se 3 (by rfl) ⟨29543, by rfl⟩) (B 59087 (by norm_num) ⟨29543, by rfl⟩ (by norm_num))
theorem R59265 : Reach 59265 := rs (se 2 (by rfl) ⟨22224, by rfl⟩) (B 44449 (by norm_num) ⟨22224, by rfl⟩ (by norm_num))
theorem R59269 : Reach 59269 := rs (se 4 (by rfl) ⟨5556, by rfl⟩) (B 11113 (by norm_num) ⟨5556, by rfl⟩ (by norm_num))
theorem R59273 : Reach 59273 := rs (se 2 (by rfl) ⟨22227, by rfl⟩) (B 44455 (by norm_num) ⟨22227, by rfl⟩ (by norm_num))
theorem R59277 : Reach 59277 := rs (se 3 (by rfl) ⟨11114, by rfl⟩) (B 22229 (by norm_num) ⟨11114, by rfl⟩ (by norm_num))
theorem R92045 : Reach 92045 := rs (se 3 (by rfl) ⟨17258, by rfl⟩) (B 34517 (by norm_num) ⟨17258, by rfl⟩ (by norm_num))
theorem R59281 : Reach 59281 := rs (se 2 (by rfl) ⟨22230, by rfl⟩) (B 44461 (by norm_num) ⟨22230, by rfl⟩ (by norm_num))
theorem R59285 : Reach 59285 := rs (se 6 (by rfl) ⟨1389, by rfl⟩) (B 2779 (by norm_num) ⟨1389, by rfl⟩ (by norm_num))
theorem R59289 : Reach 59289 := rs (se 2 (by rfl) ⟨22233, by rfl⟩) (B 44467 (by norm_num) ⟨22233, by rfl⟩ (by norm_num))
theorem R59293 : Reach 59293 := rs (se 3 (by rfl) ⟨11117, by rfl⟩) (B 22235 (by norm_num) ⟨11117, by rfl⟩ (by norm_num))
theorem R59297 : Reach 59297 := rs (se 2 (by rfl) ⟨22236, by rfl⟩) (B 44473 (by norm_num) ⟨22236, by rfl⟩ (by norm_num))
theorem R59301 : Reach 59301 := rs (se 4 (by rfl) ⟨5559, by rfl⟩) (B 11119 (by norm_num) ⟨5559, by rfl⟩ (by norm_num))
theorem R92069 : Reach 92069 := rs (se 4 (by rfl) ⟨8631, by rfl⟩) (B 17263 (by norm_num) ⟨8631, by rfl⟩ (by norm_num))
theorem R59305 : Reach 59305 := rs (se 2 (by rfl) ⟨22239, by rfl⟩) (B 44479 (by norm_num) ⟨22239, by rfl⟩ (by norm_num))
theorem R59309 : Reach 59309 := rs (se 3 (by rfl) ⟨11120, by rfl⟩) (B 22241 (by norm_num) ⟨11120, by rfl⟩ (by norm_num))
theorem R59313 : Reach 59313 := rs (se 2 (by rfl) ⟨22242, by rfl⟩) (B 44485 (by norm_num) ⟨22242, by rfl⟩ (by norm_num))
theorem R59317 : Reach 59317 := rs (se 5 (by rfl) ⟨2780, by rfl⟩) (B 5561 (by norm_num) ⟨2780, by rfl⟩ (by norm_num))
theorem R59321 : Reach 59321 := rs (se 2 (by rfl) ⟨22245, by rfl⟩) (B 44491 (by norm_num) ⟨22245, by rfl⟩ (by norm_num))
theorem R59325 : Reach 59325 := rs (se 3 (by rfl) ⟨11123, by rfl⟩) (B 22247 (by norm_num) ⟨11123, by rfl⟩ (by norm_num))
theorem R92093 : Reach 92093 := rs (se 3 (by rfl) ⟨17267, by rfl⟩) (B 34535 (by norm_num) ⟨17267, by rfl⟩ (by norm_num))
theorem R59329 : Reach 59329 := rs (se 2 (by rfl) ⟨22248, by rfl⟩) (B 44497 (by norm_num) ⟨22248, by rfl⟩ (by norm_num))
theorem R59333 : Reach 59333 := rs (se 4 (by rfl) ⟨5562, by rfl⟩) (B 11125 (by norm_num) ⟨5562, by rfl⟩ (by norm_num))
theorem R59337 : Reach 59337 := rs (se 2 (by rfl) ⟨22251, by rfl⟩) (B 44503 (by norm_num) ⟨22251, by rfl⟩ (by norm_num))
theorem R59341 : Reach 59341 := rs (se 3 (by rfl) ⟨11126, by rfl⟩) (B 22253 (by norm_num) ⟨11126, by rfl⟩ (by norm_num))
theorem R59345 : Reach 59345 := rs (se 2 (by rfl) ⟨22254, by rfl⟩) (B 44509 (by norm_num) ⟨22254, by rfl⟩ (by norm_num))
theorem R59349 : Reach 59349 := rs (se 7 (by rfl) ⟨695, by rfl⟩) (B 1391 (by norm_num) ⟨695, by rfl⟩ (by norm_num))
theorem R92117 : Reach 92117 := rs (se 7 (by rfl) ⟨1079, by rfl⟩) (B 2159 (by norm_num) ⟨1079, by rfl⟩ (by norm_num))
theorem R59353 : Reach 59353 := rs (se 2 (by rfl) ⟨22257, by rfl⟩) (B 44515 (by norm_num) ⟨22257, by rfl⟩ (by norm_num))
theorem R59357 : Reach 59357 := rs (se 3 (by rfl) ⟨11129, by rfl⟩) (B 22259 (by norm_num) ⟨11129, by rfl⟩ (by norm_num))
theorem R59361 : Reach 59361 := rs (se 2 (by rfl) ⟨22260, by rfl⟩) (B 44521 (by norm_num) ⟨22260, by rfl⟩ (by norm_num))
theorem R59365 : Reach 59365 := rs (se 4 (by rfl) ⟨5565, by rfl⟩) (B 11131 (by norm_num) ⟨5565, by rfl⟩ (by norm_num))
theorem R59369 : Reach 59369 := rs (se 2 (by rfl) ⟨22263, by rfl⟩) (B 44527 (by norm_num) ⟨22263, by rfl⟩ (by norm_num))
theorem R59373 : Reach 59373 := rs (se 3 (by rfl) ⟨11132, by rfl⟩) (B 22265 (by norm_num) ⟨11132, by rfl⟩ (by norm_num))
theorem R92141 : Reach 92141 := rs (se 3 (by rfl) ⟨17276, by rfl⟩) (B 34553 (by norm_num) ⟨17276, by rfl⟩ (by norm_num))
theorem R59377 : Reach 59377 := rs (se 2 (by rfl) ⟨22266, by rfl⟩) (B 44533 (by norm_num) ⟨22266, by rfl⟩ (by norm_num))
theorem R59381 : Reach 59381 := rs (se 5 (by rfl) ⟨2783, by rfl⟩) (B 5567 (by norm_num) ⟨2783, by rfl⟩ (by norm_num))
theorem R59385 : Reach 59385 := rs (se 2 (by rfl) ⟨22269, by rfl⟩) (B 44539 (by norm_num) ⟨22269, by rfl⟩ (by norm_num))
theorem R59389 : Reach 59389 := rs (se 3 (by rfl) ⟨11135, by rfl⟩) (B 22271 (by norm_num) ⟨11135, by rfl⟩ (by norm_num))
theorem R59393 : Reach 59393 := rs (se 2 (by rfl) ⟨22272, by rfl⟩) (B 44545 (by norm_num) ⟨22272, by rfl⟩ (by norm_num))
theorem R59397 : Reach 59397 := rs (se 4 (by rfl) ⟨5568, by rfl⟩) (B 11137 (by norm_num) ⟨5568, by rfl⟩ (by norm_num))
theorem R92165 : Reach 92165 := rs (se 4 (by rfl) ⟨8640, by rfl⟩) (B 17281 (by norm_num) ⟨8640, by rfl⟩ (by norm_num))
theorem R59401 : Reach 59401 := rs (se 2 (by rfl) ⟨22275, by rfl⟩) (B 44551 (by norm_num) ⟨22275, by rfl⟩ (by norm_num))
theorem R59405 : Reach 59405 := rs (se 3 (by rfl) ⟨11138, by rfl⟩) (B 22277 (by norm_num) ⟨11138, by rfl⟩ (by norm_num))
theorem R59409 : Reach 59409 := rs (se 2 (by rfl) ⟨22278, by rfl⟩) (B 44557 (by norm_num) ⟨22278, by rfl⟩ (by norm_num))
theorem R59413 : Reach 59413 := rs (se 6 (by rfl) ⟨1392, by rfl⟩) (B 2785 (by norm_num) ⟨1392, by rfl⟩ (by norm_num))
theorem R157717 : Reach 157717 := rs (se 6 (by rfl) ⟨3696, by rfl⟩) (B 7393 (by norm_num) ⟨3696, by rfl⟩ (by norm_num))
theorem R59417 : Reach 59417 := rs (se 2 (by rfl) ⟨22281, by rfl⟩) (B 44563 (by norm_num) ⟨22281, by rfl⟩ (by norm_num))
theorem R59421 : Reach 59421 := rs (se 3 (by rfl) ⟨11141, by rfl⟩) (B 22283 (by norm_num) ⟨11141, by rfl⟩ (by norm_num))
theorem R92189 : Reach 92189 := rs (se 3 (by rfl) ⟨17285, by rfl⟩) (B 34571 (by norm_num) ⟨17285, by rfl⟩ (by norm_num))
theorem R59425 : Reach 59425 := rs (se 2 (by rfl) ⟨22284, by rfl⟩) (B 44569 (by norm_num) ⟨22284, by rfl⟩ (by norm_num))
theorem R59429 : Reach 59429 := rs (se 4 (by rfl) ⟨5571, by rfl⟩) (B 11143 (by norm_num) ⟨5571, by rfl⟩ (by norm_num))
theorem R59433 : Reach 59433 := rs (se 2 (by rfl) ⟨22287, by rfl⟩) (B 44575 (by norm_num) ⟨22287, by rfl⟩ (by norm_num))
theorem R59437 : Reach 59437 := rs (se 3 (by rfl) ⟨11144, by rfl⟩) (B 22289 (by norm_num) ⟨11144, by rfl⟩ (by norm_num))
theorem R59441 : Reach 59441 := rs (se 2 (by rfl) ⟨22290, by rfl⟩) (B 44581 (by norm_num) ⟨22290, by rfl⟩ (by norm_num))
theorem R59445 : Reach 59445 := rs (se 5 (by rfl) ⟨2786, by rfl⟩) (B 5573 (by norm_num) ⟨2786, by rfl⟩ (by norm_num))
theorem R92213 : Reach 92213 := rs (se 5 (by rfl) ⟨4322, by rfl⟩) (B 8645 (by norm_num) ⟨4322, by rfl⟩ (by norm_num))
theorem R59449 : Reach 59449 := rs (se 2 (by rfl) ⟨22293, by rfl⟩) (B 44587 (by norm_num) ⟨22293, by rfl⟩ (by norm_num))
theorem R59453 : Reach 59453 := rs (se 3 (by rfl) ⟨11147, by rfl⟩) (B 22295 (by norm_num) ⟨11147, by rfl⟩ (by norm_num))
theorem R59457 : Reach 59457 := rs (se 2 (by rfl) ⟨22296, by rfl⟩) (B 44593 (by norm_num) ⟨22296, by rfl⟩ (by norm_num))
theorem R59461 : Reach 59461 := rs (se 4 (by rfl) ⟨5574, by rfl⟩) (B 11149 (by norm_num) ⟨5574, by rfl⟩ (by norm_num))
theorem R59465 : Reach 59465 := rs (se 2 (by rfl) ⟨22299, by rfl⟩) (B 44599 (by norm_num) ⟨22299, by rfl⟩ (by norm_num))
theorem R59469 : Reach 59469 := rs (se 3 (by rfl) ⟨11150, by rfl⟩) (B 22301 (by norm_num) ⟨11150, by rfl⟩ (by norm_num))
theorem R92237 : Reach 92237 := rs (se 3 (by rfl) ⟨17294, by rfl⟩) (B 34589 (by norm_num) ⟨17294, by rfl⟩ (by norm_num))
theorem R59473 : Reach 59473 := rs (se 2 (by rfl) ⟨22302, by rfl⟩) (B 44605 (by norm_num) ⟨22302, by rfl⟩ (by norm_num))
theorem R59477 : Reach 59477 := rs (se 8 (by rfl) ⟨348, by rfl⟩) (B 697 (by norm_num) ⟨348, by rfl⟩ (by norm_num))
theorem R256085 : Reach 256085 := rs (se 8 (by rfl) ⟨1500, by rfl⟩) (B 3001 (by norm_num) ⟨1500, by rfl⟩ (by norm_num))
theorem R59481 : Reach 59481 := rs (se 2 (by rfl) ⟨22305, by rfl⟩) (B 44611 (by norm_num) ⟨22305, by rfl⟩ (by norm_num))
theorem R59485 : Reach 59485 := rs (se 3 (by rfl) ⟨11153, by rfl⟩) (B 22307 (by norm_num) ⟨11153, by rfl⟩ (by norm_num))
theorem R59489 : Reach 59489 := rs (se 2 (by rfl) ⟨22308, by rfl⟩) (B 44617 (by norm_num) ⟨22308, by rfl⟩ (by norm_num))
theorem R59493 : Reach 59493 := rs (se 4 (by rfl) ⟨5577, by rfl⟩) (B 11155 (by norm_num) ⟨5577, by rfl⟩ (by norm_num))
theorem R92261 : Reach 92261 := rs (se 4 (by rfl) ⟨8649, by rfl⟩) (B 17299 (by norm_num) ⟨8649, by rfl⟩ (by norm_num))
theorem R59497 : Reach 59497 := rs (se 2 (by rfl) ⟨22311, by rfl⟩) (B 44623 (by norm_num) ⟨22311, by rfl⟩ (by norm_num))
theorem R59501 : Reach 59501 := rs (se 3 (by rfl) ⟨11156, by rfl⟩) (B 22313 (by norm_num) ⟨11156, by rfl⟩ (by norm_num))
theorem R59505 : Reach 59505 := rs (se 2 (by rfl) ⟨22314, by rfl⟩) (B 44629 (by norm_num) ⟨22314, by rfl⟩ (by norm_num))
theorem R59509 : Reach 59509 := rs (se 5 (by rfl) ⟨2789, by rfl⟩) (B 5579 (by norm_num) ⟨2789, by rfl⟩ (by norm_num))
theorem R59513 : Reach 59513 := rs (se 2 (by rfl) ⟨22317, by rfl⟩) (B 44635 (by norm_num) ⟨22317, by rfl⟩ (by norm_num))
theorem R59517 : Reach 59517 := rs (se 3 (by rfl) ⟨11159, by rfl⟩) (B 22319 (by norm_num) ⟨11159, by rfl⟩ (by norm_num))
theorem R92285 : Reach 92285 := rs (se 3 (by rfl) ⟨17303, by rfl⟩) (B 34607 (by norm_num) ⟨17303, by rfl⟩ (by norm_num))
theorem R59521 : Reach 59521 := rs (se 2 (by rfl) ⟨22320, by rfl⟩) (B 44641 (by norm_num) ⟨22320, by rfl⟩ (by norm_num))
theorem R59525 : Reach 59525 := rs (se 4 (by rfl) ⟨5580, by rfl⟩) (B 11161 (by norm_num) ⟨5580, by rfl⟩ (by norm_num))
theorem R59529 : Reach 59529 := rs (se 2 (by rfl) ⟨22323, by rfl⟩) (B 44647 (by norm_num) ⟨22323, by rfl⟩ (by norm_num))
theorem R59533 : Reach 59533 := rs (se 3 (by rfl) ⟨11162, by rfl⟩) (B 22325 (by norm_num) ⟨11162, by rfl⟩ (by norm_num))
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) (B 46901 (by norm_num) ⟨23450, by rfl⟩ (by norm_num))
theorem R59537 : Reach 59537 := rs (se 2 (by rfl) ⟨22326, by rfl⟩) (B 44653 (by norm_num) ⟨22326, by rfl⟩ (by norm_num))
theorem R59541 : Reach 59541 := rs (se 6 (by rfl) ⟨1395, by rfl⟩) (B 2791 (by norm_num) ⟨1395, by rfl⟩ (by norm_num))
theorem R92309 : Reach 92309 := rs (se 6 (by rfl) ⟨2163, by rfl⟩) (B 4327 (by norm_num) ⟨2163, by rfl⟩ (by norm_num))
theorem R125077 : Reach 125077 := rs (se 6 (by rfl) ⟨2931, by rfl⟩) (B 5863 (by norm_num) ⟨2931, by rfl⟩ (by norm_num))
theorem R59545 : Reach 59545 := rs (se 2 (by rfl) ⟨22329, by rfl⟩) (B 44659 (by norm_num) ⟨22329, by rfl⟩ (by norm_num))
theorem R59549 : Reach 59549 := rs (se 3 (by rfl) ⟨11165, by rfl⟩) (B 22331 (by norm_num) ⟨11165, by rfl⟩ (by norm_num))
theorem R59553 : Reach 59553 := rs (se 2 (by rfl) ⟨22332, by rfl⟩) (B 44665 (by norm_num) ⟨22332, by rfl⟩ (by norm_num))
theorem R59557 : Reach 59557 := rs (se 4 (by rfl) ⟨5583, by rfl⟩) (B 11167 (by norm_num) ⟨5583, by rfl⟩ (by norm_num))
theorem R223397 : Reach 223397 := rs (se 4 (by rfl) ⟨20943, by rfl⟩) (B 41887 (by norm_num) ⟨20943, by rfl⟩ (by norm_num))
theorem R59561 : Reach 59561 := rs (se 2 (by rfl) ⟨22335, by rfl⟩) (B 44671 (by norm_num) ⟨22335, by rfl⟩ (by norm_num))
theorem R59565 : Reach 59565 := rs (se 3 (by rfl) ⟨11168, by rfl⟩) (B 22337 (by norm_num) ⟨11168, by rfl⟩ (by norm_num))
theorem R92333 : Reach 92333 := rs (se 3 (by rfl) ⟨17312, by rfl⟩) (B 34625 (by norm_num) ⟨17312, by rfl⟩ (by norm_num))
theorem R59569 : Reach 59569 := rs (se 2 (by rfl) ⟨22338, by rfl⟩) (B 44677 (by norm_num) ⟨22338, by rfl⟩ (by norm_num))
theorem R59573 : Reach 59573 := rs (se 5 (by rfl) ⟨2792, by rfl⟩) (B 5585 (by norm_num) ⟨2792, by rfl⟩ (by norm_num))
theorem R59577 : Reach 59577 := rs (se 2 (by rfl) ⟨22341, by rfl⟩) (B 44683 (by norm_num) ⟨22341, by rfl⟩ (by norm_num))
theorem R59581 : Reach 59581 := rs (se 3 (by rfl) ⟨11171, by rfl⟩) (B 22343 (by norm_num) ⟨11171, by rfl⟩ (by norm_num))
theorem R59585 : Reach 59585 := rs (se 2 (by rfl) ⟨22344, by rfl⟩) (B 44689 (by norm_num) ⟨22344, by rfl⟩ (by norm_num))
theorem R59589 : Reach 59589 := rs (se 4 (by rfl) ⟨5586, by rfl⟩) (B 11173 (by norm_num) ⟨5586, by rfl⟩ (by norm_num))
theorem R92357 : Reach 92357 := rs (se 4 (by rfl) ⟨8658, by rfl⟩) (B 17317 (by norm_num) ⟨8658, by rfl⟩ (by norm_num))
theorem R59593 : Reach 59593 := rs (se 2 (by rfl) ⟨22347, by rfl⟩) (B 44695 (by norm_num) ⟨22347, by rfl⟩ (by norm_num))
theorem R59597 : Reach 59597 := rs (se 3 (by rfl) ⟨11174, by rfl⟩) (B 22349 (by norm_num) ⟨11174, by rfl⟩ (by norm_num))
theorem R59601 : Reach 59601 := rs (se 2 (by rfl) ⟨22350, by rfl⟩) (B 44701 (by norm_num) ⟨22350, by rfl⟩ (by norm_num))
theorem R59605 : Reach 59605 := rs (se 7 (by rfl) ⟨698, by rfl⟩) (B 1397 (by norm_num) ⟨698, by rfl⟩ (by norm_num))
theorem R157909 : Reach 157909 := rs (se 7 (by rfl) ⟨1850, by rfl⟩) (B 3701 (by norm_num) ⟨1850, by rfl⟩ (by norm_num))
theorem R59609 : Reach 59609 := rs (se 2 (by rfl) ⟨22353, by rfl⟩) (B 44707 (by norm_num) ⟨22353, by rfl⟩ (by norm_num))
theorem R59613 : Reach 59613 := rs (se 3 (by rfl) ⟨11177, by rfl⟩) (B 22355 (by norm_num) ⟨11177, by rfl⟩ (by norm_num))
theorem R92381 : Reach 92381 := rs (se 3 (by rfl) ⟨17321, by rfl⟩) (B 34643 (by norm_num) ⟨17321, by rfl⟩ (by norm_num))
theorem R59617 : Reach 59617 := rs (se 2 (by rfl) ⟨22356, by rfl⟩) (B 44713 (by norm_num) ⟨22356, by rfl⟩ (by norm_num))
theorem R59621 : Reach 59621 := rs (se 4 (by rfl) ⟨5589, by rfl⟩) (B 11179 (by norm_num) ⟨5589, by rfl⟩ (by norm_num))
theorem R59625 : Reach 59625 := rs (se 2 (by rfl) ⟨22359, by rfl⟩) (B 44719 (by norm_num) ⟨22359, by rfl⟩ (by norm_num))
theorem R59629 : Reach 59629 := rs (se 3 (by rfl) ⟨11180, by rfl⟩) (B 22361 (by norm_num) ⟨11180, by rfl⟩ (by norm_num))
theorem R59633 : Reach 59633 := rs (se 2 (by rfl) ⟨22362, by rfl⟩) (B 44725 (by norm_num) ⟨22362, by rfl⟩ (by norm_num))
theorem R59637 : Reach 59637 := rs (se 5 (by rfl) ⟨2795, by rfl⟩) (B 5591 (by norm_num) ⟨2795, by rfl⟩ (by norm_num))
theorem R92405 : Reach 92405 := rs (se 5 (by rfl) ⟨4331, by rfl⟩) (B 8663 (by norm_num) ⟨4331, by rfl⟩ (by norm_num))
theorem R59641 : Reach 59641 := rs (se 2 (by rfl) ⟨22365, by rfl⟩) (B 44731 (by norm_num) ⟨22365, by rfl⟩ (by norm_num))
theorem R59645 : Reach 59645 := rs (se 3 (by rfl) ⟨11183, by rfl⟩) (B 22367 (by norm_num) ⟨11183, by rfl⟩ (by norm_num))
theorem R59649 : Reach 59649 := rs (se 2 (by rfl) ⟨22368, by rfl⟩) (B 44737 (by norm_num) ⟨22368, by rfl⟩ (by norm_num))
theorem R59653 : Reach 59653 := rs (se 4 (by rfl) ⟨5592, by rfl⟩) (B 11185 (by norm_num) ⟨5592, by rfl⟩ (by norm_num))
theorem R59657 : Reach 59657 := rs (se 2 (by rfl) ⟨22371, by rfl⟩) (B 44743 (by norm_num) ⟨22371, by rfl⟩ (by norm_num))
theorem R59661 : Reach 59661 := rs (se 3 (by rfl) ⟨11186, by rfl⟩) (B 22373 (by norm_num) ⟨11186, by rfl⟩ (by norm_num))
theorem R92429 : Reach 92429 := rs (se 3 (by rfl) ⟨17330, by rfl⟩) (B 34661 (by norm_num) ⟨17330, by rfl⟩ (by norm_num))
theorem R59665 : Reach 59665 := rs (se 2 (by rfl) ⟨22374, by rfl⟩) (B 44749 (by norm_num) ⟨22374, by rfl⟩ (by norm_num))
theorem R59669 : Reach 59669 := rs (se 6 (by rfl) ⟨1398, by rfl⟩) (B 2797 (by norm_num) ⟨1398, by rfl⟩ (by norm_num))
theorem R59673 : Reach 59673 := rs (se 2 (by rfl) ⟨22377, by rfl⟩) (B 44755 (by norm_num) ⟨22377, by rfl⟩ (by norm_num))
theorem R59677 : Reach 59677 := rs (se 3 (by rfl) ⟨11189, by rfl⟩) (B 22379 (by norm_num) ⟨11189, by rfl⟩ (by norm_num))
theorem R59681 : Reach 59681 := rs (se 2 (by rfl) ⟨22380, by rfl⟩) (B 44761 (by norm_num) ⟨22380, by rfl⟩ (by norm_num))
theorem R59685 : Reach 59685 := rs (se 4 (by rfl) ⟨5595, by rfl⟩) (B 11191 (by norm_num) ⟨5595, by rfl⟩ (by norm_num))
theorem R92453 : Reach 92453 := rs (se 4 (by rfl) ⟨8667, by rfl⟩) (B 17335 (by norm_num) ⟨8667, by rfl⟩ (by norm_num))
theorem R59689 : Reach 59689 := rs (se 2 (by rfl) ⟨22383, by rfl⟩) (B 44767 (by norm_num) ⟨22383, by rfl⟩ (by norm_num))
theorem R59693 : Reach 59693 := rs (se 3 (by rfl) ⟨11192, by rfl⟩) (B 22385 (by norm_num) ⟨11192, by rfl⟩ (by norm_num))
theorem R59697 : Reach 59697 := rs (se 2 (by rfl) ⟨22386, by rfl⟩) (B 44773 (by norm_num) ⟨22386, by rfl⟩ (by norm_num))
theorem R59701 : Reach 59701 := rs (se 5 (by rfl) ⟨2798, by rfl⟩) (B 5597 (by norm_num) ⟨2798, by rfl⟩ (by norm_num))
theorem R59705 : Reach 59705 := rs (se 2 (by rfl) ⟨22389, by rfl⟩) (B 44779 (by norm_num) ⟨22389, by rfl⟩ (by norm_num))
theorem R59709 : Reach 59709 := rs (se 3 (by rfl) ⟨11195, by rfl⟩) (B 22391 (by norm_num) ⟨11195, by rfl⟩ (by norm_num))
theorem R92477 : Reach 92477 := rs (se 3 (by rfl) ⟨17339, by rfl⟩) (B 34679 (by norm_num) ⟨17339, by rfl⟩ (by norm_num))
theorem R59713 : Reach 59713 := rs (se 2 (by rfl) ⟨22392, by rfl⟩) (B 44785 (by norm_num) ⟨22392, by rfl⟩ (by norm_num))
theorem R59717 : Reach 59717 := rs (se 4 (by rfl) ⟨5598, by rfl⟩) (B 11197 (by norm_num) ⟨5598, by rfl⟩ (by norm_num))
theorem R158021 : Reach 158021 := rs (se 4 (by rfl) ⟨14814, by rfl⟩) (B 29629 (by norm_num) ⟨14814, by rfl⟩ (by norm_num))
theorem R59721 : Reach 59721 := rs (se 2 (by rfl) ⟨22395, by rfl⟩) (B 44791 (by norm_num) ⟨22395, by rfl⟩ (by norm_num))
theorem R59725 : Reach 59725 := rs (se 3 (by rfl) ⟨11198, by rfl⟩) (B 22397 (by norm_num) ⟨11198, by rfl⟩ (by norm_num))
theorem R59729 : Reach 59729 := rs (se 2 (by rfl) ⟨22398, by rfl⟩) (B 44797 (by norm_num) ⟨22398, by rfl⟩ (by norm_num))
theorem R59733 : Reach 59733 := rs (se 10 (by rfl) ⟨87, by rfl⟩) (B 175 (by norm_num) ⟨87, by rfl⟩ (by norm_num))
theorem R92501 : Reach 92501 := rs (se 10 (by rfl) ⟨135, by rfl⟩) (B 271 (by norm_num) ⟨135, by rfl⟩ (by norm_num))
theorem R59737 : Reach 59737 := rs (se 2 (by rfl) ⟨22401, by rfl⟩) (B 44803 (by norm_num) ⟨22401, by rfl⟩ (by norm_num))
theorem R59741 : Reach 59741 := rs (se 3 (by rfl) ⟨11201, by rfl⟩) (B 22403 (by norm_num) ⟨11201, by rfl⟩ (by norm_num))
theorem R59745 : Reach 59745 := rs (se 2 (by rfl) ⟨22404, by rfl⟩) (B 44809 (by norm_num) ⟨22404, by rfl⟩ (by norm_num))
theorem R59749 : Reach 59749 := rs (se 4 (by rfl) ⟨5601, by rfl⟩) (B 11203 (by norm_num) ⟨5601, by rfl⟩ (by norm_num))
theorem R59753 : Reach 59753 := rs (se 2 (by rfl) ⟨22407, by rfl⟩) (B 44815 (by norm_num) ⟨22407, by rfl⟩ (by norm_num))
theorem R59757 : Reach 59757 := rs (se 3 (by rfl) ⟨11204, by rfl⟩) (B 22409 (by norm_num) ⟨11204, by rfl⟩ (by norm_num))
theorem R92525 : Reach 92525 := rs (se 3 (by rfl) ⟨17348, by rfl⟩) (B 34697 (by norm_num) ⟨17348, by rfl⟩ (by norm_num))
theorem R59761 : Reach 59761 := rs (se 2 (by rfl) ⟨22410, by rfl⟩) (B 44821 (by norm_num) ⟨22410, by rfl⟩ (by norm_num))
theorem R59765 : Reach 59765 := rs (se 5 (by rfl) ⟨2801, by rfl⟩) (B 5603 (by norm_num) ⟨2801, by rfl⟩ (by norm_num))
theorem R59769 : Reach 59769 := rs (se 2 (by rfl) ⟨22413, by rfl⟩) (B 44827 (by norm_num) ⟨22413, by rfl⟩ (by norm_num))
theorem R59773 : Reach 59773 := rs (se 3 (by rfl) ⟨11207, by rfl⟩) (B 22415 (by norm_num) ⟨11207, by rfl⟩ (by norm_num))
theorem R59777 : Reach 59777 := rs (se 2 (by rfl) ⟨22416, by rfl⟩) (B 44833 (by norm_num) ⟨22416, by rfl⟩ (by norm_num))
theorem R59781 : Reach 59781 := rs (se 4 (by rfl) ⟨5604, by rfl⟩) (B 11209 (by norm_num) ⟨5604, by rfl⟩ (by norm_num))
theorem R92549 : Reach 92549 := rs (se 4 (by rfl) ⟨8676, by rfl⟩) (B 17353 (by norm_num) ⟨8676, by rfl⟩ (by norm_num))
theorem R59785 : Reach 59785 := rs (se 2 (by rfl) ⟨22419, by rfl⟩) (B 44839 (by norm_num) ⟨22419, by rfl⟩ (by norm_num))
theorem R59789 : Reach 59789 := rs (se 3 (by rfl) ⟨11210, by rfl⟩) (B 22421 (by norm_num) ⟨11210, by rfl⟩ (by norm_num))
theorem R59793 : Reach 59793 := rs (se 2 (by rfl) ⟨22422, by rfl⟩) (B 44845 (by norm_num) ⟨22422, by rfl⟩ (by norm_num))
theorem R59797 : Reach 59797 := rs (se 6 (by rfl) ⟨1401, by rfl⟩) (B 2803 (by norm_num) ⟨1401, by rfl⟩ (by norm_num))
theorem R59801 : Reach 59801 := rs (se 2 (by rfl) ⟨22425, by rfl⟩) (B 44851 (by norm_num) ⟨22425, by rfl⟩ (by norm_num))
theorem R59805 : Reach 59805 := rs (se 3 (by rfl) ⟨11213, by rfl⟩) (B 22427 (by norm_num) ⟨11213, by rfl⟩ (by norm_num))
theorem R92573 : Reach 92573 := rs (se 3 (by rfl) ⟨17357, by rfl⟩) (B 34715 (by norm_num) ⟨17357, by rfl⟩ (by norm_num))
theorem R59809 : Reach 59809 := rs (se 2 (by rfl) ⟨22428, by rfl⟩) (B 44857 (by norm_num) ⟨22428, by rfl⟩ (by norm_num))
theorem R59813 : Reach 59813 := rs (se 4 (by rfl) ⟨5607, by rfl⟩) (B 11215 (by norm_num) ⟨5607, by rfl⟩ (by norm_num))
theorem R59817 : Reach 59817 := rs (se 2 (by rfl) ⟨22431, by rfl⟩) (B 44863 (by norm_num) ⟨22431, by rfl⟩ (by norm_num))
theorem R59821 : Reach 59821 := rs (se 3 (by rfl) ⟨11216, by rfl⟩) (B 22433 (by norm_num) ⟨11216, by rfl⟩ (by norm_num))
theorem R59825 : Reach 59825 := rs (se 2 (by rfl) ⟨22434, by rfl⟩) (B 44869 (by norm_num) ⟨22434, by rfl⟩ (by norm_num))
theorem R59829 : Reach 59829 := rs (se 5 (by rfl) ⟨2804, by rfl⟩) (B 5609 (by norm_num) ⟨2804, by rfl⟩ (by norm_num))
theorem R92597 : Reach 92597 := rs (se 5 (by rfl) ⟨4340, by rfl⟩) (B 8681 (by norm_num) ⟨4340, by rfl⟩ (by norm_num))
theorem R59833 : Reach 59833 := rs (se 2 (by rfl) ⟨22437, by rfl⟩) (B 44875 (by norm_num) ⟨22437, by rfl⟩ (by norm_num))
theorem R59837 : Reach 59837 := rs (se 3 (by rfl) ⟨11219, by rfl⟩) (B 22439 (by norm_num) ⟨11219, by rfl⟩ (by norm_num))
theorem R59841 : Reach 59841 := rs (se 2 (by rfl) ⟨22440, by rfl⟩) (B 44881 (by norm_num) ⟨22440, by rfl⟩ (by norm_num))
theorem R59845 : Reach 59845 := rs (se 4 (by rfl) ⟨5610, by rfl⟩) (B 11221 (by norm_num) ⟨5610, by rfl⟩ (by norm_num))
theorem R223685 : Reach 223685 := rs (se 4 (by rfl) ⟨20970, by rfl⟩) (B 41941 (by norm_num) ⟨20970, by rfl⟩ (by norm_num))
theorem R59849 : Reach 59849 := rs (se 2 (by rfl) ⟨22443, by rfl⟩) (B 44887 (by norm_num) ⟨22443, by rfl⟩ (by norm_num))
theorem R59853 : Reach 59853 := rs (se 3 (by rfl) ⟨11222, by rfl⟩) (B 22445 (by norm_num) ⟨11222, by rfl⟩ (by norm_num))
theorem R92621 : Reach 92621 := rs (se 3 (by rfl) ⟨17366, by rfl⟩) (B 34733 (by norm_num) ⟨17366, by rfl⟩ (by norm_num))
theorem R59857 : Reach 59857 := rs (se 2 (by rfl) ⟨22446, by rfl⟩) (B 44893 (by norm_num) ⟨22446, by rfl⟩ (by norm_num))
theorem R59861 : Reach 59861 := rs (se 7 (by rfl) ⟨701, by rfl⟩) (B 1403 (by norm_num) ⟨701, by rfl⟩ (by norm_num))
theorem R59865 : Reach 59865 := rs (se 2 (by rfl) ⟨22449, by rfl⟩) (B 44899 (by norm_num) ⟨22449, by rfl⟩ (by norm_num))
theorem R59869 : Reach 59869 := rs (se 3 (by rfl) ⟨11225, by rfl⟩) (B 22451 (by norm_num) ⟨11225, by rfl⟩ (by norm_num))
theorem R59873 : Reach 59873 := rs (se 2 (by rfl) ⟨22452, by rfl⟩) (B 44905 (by norm_num) ⟨22452, by rfl⟩ (by norm_num))
theorem R59877 : Reach 59877 := rs (se 4 (by rfl) ⟨5613, by rfl⟩) (B 11227 (by norm_num) ⟨5613, by rfl⟩ (by norm_num))
theorem R92645 : Reach 92645 := rs (se 4 (by rfl) ⟨8685, by rfl⟩) (B 17371 (by norm_num) ⟨8685, by rfl⟩ (by norm_num))
theorem R59881 : Reach 59881 := rs (se 2 (by rfl) ⟨22455, by rfl⟩) (B 44911 (by norm_num) ⟨22455, by rfl⟩ (by norm_num))
theorem R59885 : Reach 59885 := rs (se 3 (by rfl) ⟨11228, by rfl⟩) (B 22457 (by norm_num) ⟨11228, by rfl⟩ (by norm_num))
theorem R59889 : Reach 59889 := rs (se 2 (by rfl) ⟨22458, by rfl⟩) (B 44917 (by norm_num) ⟨22458, by rfl⟩ (by norm_num))
theorem R59893 : Reach 59893 := rs (se 5 (by rfl) ⟨2807, by rfl⟩) (B 5615 (by norm_num) ⟨2807, by rfl⟩ (by norm_num))
theorem R59897 : Reach 59897 := rs (se 2 (by rfl) ⟨22461, by rfl⟩) (B 44923 (by norm_num) ⟨22461, by rfl⟩ (by norm_num))
theorem R59901 : Reach 59901 := rs (se 3 (by rfl) ⟨11231, by rfl⟩) (B 22463 (by norm_num) ⟨11231, by rfl⟩ (by norm_num))
theorem R92669 : Reach 92669 := rs (se 3 (by rfl) ⟨17375, by rfl⟩) (B 34751 (by norm_num) ⟨17375, by rfl⟩ (by norm_num))
theorem R59905 : Reach 59905 := rs (se 2 (by rfl) ⟨22464, by rfl⟩) (B 44929 (by norm_num) ⟨22464, by rfl⟩ (by norm_num))
theorem R59909 : Reach 59909 := rs (se 4 (by rfl) ⟨5616, by rfl⟩) (B 11233 (by norm_num) ⟨5616, by rfl⟩ (by norm_num))
theorem R158213 : Reach 158213 := rs (se 4 (by rfl) ⟨14832, by rfl⟩) (B 29665 (by norm_num) ⟨14832, by rfl⟩ (by norm_num))
theorem R59913 : Reach 59913 := rs (se 2 (by rfl) ⟨22467, by rfl⟩) (B 44935 (by norm_num) ⟨22467, by rfl⟩ (by norm_num))
theorem R59917 : Reach 59917 := rs (se 3 (by rfl) ⟨11234, by rfl⟩) (B 22469 (by norm_num) ⟨11234, by rfl⟩ (by norm_num))
theorem R59921 : Reach 59921 := rs (se 2 (by rfl) ⟨22470, by rfl⟩) (B 44941 (by norm_num) ⟨22470, by rfl⟩ (by norm_num))
theorem R59925 : Reach 59925 := rs (se 6 (by rfl) ⟨1404, by rfl⟩) (B 2809 (by norm_num) ⟨1404, by rfl⟩ (by norm_num))
theorem R92693 : Reach 92693 := rs (se 6 (by rfl) ⟨2172, by rfl⟩) (B 4345 (by norm_num) ⟨2172, by rfl⟩ (by norm_num))
theorem R59929 : Reach 59929 := rs (se 2 (by rfl) ⟨22473, by rfl⟩) (B 44947 (by norm_num) ⟨22473, by rfl⟩ (by norm_num))
theorem R59933 : Reach 59933 := rs (se 3 (by rfl) ⟨11237, by rfl⟩) (B 22475 (by norm_num) ⟨11237, by rfl⟩ (by norm_num))
theorem R59937 : Reach 59937 := rs (se 2 (by rfl) ⟨22476, by rfl⟩) (B 44953 (by norm_num) ⟨22476, by rfl⟩ (by norm_num))
theorem R59941 : Reach 59941 := rs (se 4 (by rfl) ⟨5619, by rfl⟩) (B 11239 (by norm_num) ⟨5619, by rfl⟩ (by norm_num))
theorem R59945 : Reach 59945 := rs (se 2 (by rfl) ⟨22479, by rfl⟩) (B 44959 (by norm_num) ⟨22479, by rfl⟩ (by norm_num))
theorem R59949 : Reach 59949 := rs (se 3 (by rfl) ⟨11240, by rfl⟩) (B 22481 (by norm_num) ⟨11240, by rfl⟩ (by norm_num))
theorem R92717 : Reach 92717 := rs (se 3 (by rfl) ⟨17384, by rfl⟩) (B 34769 (by norm_num) ⟨17384, by rfl⟩ (by norm_num))
theorem R59953 : Reach 59953 := rs (se 2 (by rfl) ⟨22482, by rfl⟩) (B 44965 (by norm_num) ⟨22482, by rfl⟩ (by norm_num))
theorem R59957 : Reach 59957 := rs (se 5 (by rfl) ⟨2810, by rfl⟩) (B 5621 (by norm_num) ⟨2810, by rfl⟩ (by norm_num))
theorem R59961 : Reach 59961 := rs (se 2 (by rfl) ⟨22485, by rfl⟩) (B 44971 (by norm_num) ⟨22485, by rfl⟩ (by norm_num))
theorem R59965 : Reach 59965 := rs (se 3 (by rfl) ⟨11243, by rfl⟩) (B 22487 (by norm_num) ⟨11243, by rfl⟩ (by norm_num))
theorem R59969 : Reach 59969 := rs (se 2 (by rfl) ⟨22488, by rfl⟩) (B 44977 (by norm_num) ⟨22488, by rfl⟩ (by norm_num))
theorem R59973 : Reach 59973 := rs (se 4 (by rfl) ⟨5622, by rfl⟩) (B 11245 (by norm_num) ⟨5622, by rfl⟩ (by norm_num))
theorem R92741 : Reach 92741 := rs (se 4 (by rfl) ⟨8694, by rfl⟩) (B 17389 (by norm_num) ⟨8694, by rfl⟩ (by norm_num))
theorem R59977 : Reach 59977 := rs (se 2 (by rfl) ⟨22491, by rfl⟩) (B 44983 (by norm_num) ⟨22491, by rfl⟩ (by norm_num))
theorem R191045 : Reach 191045 := rs (se 4 (by rfl) ⟨17910, by rfl⟩) (B 35821 (by norm_num) ⟨17910, by rfl⟩ (by norm_num))
theorem R59981 : Reach 59981 := rs (se 3 (by rfl) ⟨11246, by rfl⟩) (B 22493 (by norm_num) ⟨11246, by rfl⟩ (by norm_num))
theorem R59985 : Reach 59985 := rs (se 2 (by rfl) ⟨22494, by rfl⟩) (B 44989 (by norm_num) ⟨22494, by rfl⟩ (by norm_num))
theorem R59989 : Reach 59989 := rs (se 8 (by rfl) ⟨351, by rfl⟩) (B 703 (by norm_num) ⟨351, by rfl⟩ (by norm_num))
theorem R59993 : Reach 59993 := rs (se 2 (by rfl) ⟨22497, by rfl⟩) (B 44995 (by norm_num) ⟨22497, by rfl⟩ (by norm_num))
theorem R59997 : Reach 59997 := rs (se 3 (by rfl) ⟨11249, by rfl⟩) (B 22499 (by norm_num) ⟨11249, by rfl⟩ (by norm_num))
theorem R92765 : Reach 92765 := rs (se 3 (by rfl) ⟨17393, by rfl⟩) (B 34787 (by norm_num) ⟨17393, by rfl⟩ (by norm_num))
theorem R60001 : Reach 60001 := rs (se 2 (by rfl) ⟨22500, by rfl⟩) (B 45001 (by norm_num) ⟨22500, by rfl⟩ (by norm_num))
theorem R60005 : Reach 60005 := rs (se 4 (by rfl) ⟨5625, by rfl⟩) (B 11251 (by norm_num) ⟨5625, by rfl⟩ (by norm_num))
theorem R60009 : Reach 60009 := rs (se 2 (by rfl) ⟨22503, by rfl⟩) (B 45007 (by norm_num) ⟨22503, by rfl⟩ (by norm_num))
theorem R60013 : Reach 60013 := rs (se 3 (by rfl) ⟨11252, by rfl⟩) (B 22505 (by norm_num) ⟨11252, by rfl⟩ (by norm_num))
theorem R60017 : Reach 60017 := rs (se 2 (by rfl) ⟨22506, by rfl⟩) (B 45013 (by norm_num) ⟨22506, by rfl⟩ (by norm_num))
theorem R60021 : Reach 60021 := rs (se 5 (by rfl) ⟨2813, by rfl⟩) (B 5627 (by norm_num) ⟨2813, by rfl⟩ (by norm_num))
theorem R92789 : Reach 92789 := rs (se 5 (by rfl) ⟨4349, by rfl⟩) (B 8699 (by norm_num) ⟨4349, by rfl⟩ (by norm_num))
theorem R60025 : Reach 60025 := rs (se 2 (by rfl) ⟨22509, by rfl⟩) (B 45019 (by norm_num) ⟨22509, by rfl⟩ (by norm_num))
theorem R60029 : Reach 60029 := rs (se 3 (by rfl) ⟨11255, by rfl⟩) (B 22511 (by norm_num) ⟨11255, by rfl⟩ (by norm_num))
theorem R60033 : Reach 60033 := rs (se 2 (by rfl) ⟨22512, by rfl⟩) (B 45025 (by norm_num) ⟨22512, by rfl⟩ (by norm_num))
theorem R60037 : Reach 60037 := rs (se 4 (by rfl) ⟨5628, by rfl⟩) (B 11257 (by norm_num) ⟨5628, by rfl⟩ (by norm_num))
theorem R60041 : Reach 60041 := rs (se 2 (by rfl) ⟨22515, by rfl⟩) (B 45031 (by norm_num) ⟨22515, by rfl⟩ (by norm_num))
theorem R60045 : Reach 60045 := rs (se 3 (by rfl) ⟨11258, by rfl⟩) (B 22517 (by norm_num) ⟨11258, by rfl⟩ (by norm_num))
theorem R92813 : Reach 92813 := rs (se 3 (by rfl) ⟨17402, by rfl⟩) (B 34805 (by norm_num) ⟨17402, by rfl⟩ (by norm_num))
theorem R60049 : Reach 60049 := rs (se 2 (by rfl) ⟨22518, by rfl⟩) (B 45037 (by norm_num) ⟨22518, by rfl⟩ (by norm_num))
theorem R60053 : Reach 60053 := rs (se 6 (by rfl) ⟨1407, by rfl⟩) (B 2815 (by norm_num) ⟨1407, by rfl⟩ (by norm_num))
theorem R60057 : Reach 60057 := rs (se 2 (by rfl) ⟨22521, by rfl⟩) (B 45043 (by norm_num) ⟨22521, by rfl⟩ (by norm_num))
theorem R60061 : Reach 60061 := rs (se 3 (by rfl) ⟨11261, by rfl⟩) (B 22523 (by norm_num) ⟨11261, by rfl⟩ (by norm_num))
theorem R60065 : Reach 60065 := rs (se 2 (by rfl) ⟨22524, by rfl⟩) (B 45049 (by norm_num) ⟨22524, by rfl⟩ (by norm_num))
theorem R92837 : Reach 92837 := rs (se 4 (by rfl) ⟨8703, by rfl⟩) (B 17407 (by norm_num) ⟨8703, by rfl⟩ (by norm_num))
theorem R60069 : Reach 60069 := rs (se 4 (by rfl) ⟨5631, by rfl⟩) (B 11263 (by norm_num) ⟨5631, by rfl⟩ (by norm_num))
theorem R60073 : Reach 60073 := rs (se 2 (by rfl) ⟨22527, by rfl⟩) (B 45055 (by norm_num) ⟨22527, by rfl⟩ (by norm_num))
theorem R60077 : Reach 60077 := rs (se 3 (by rfl) ⟨11264, by rfl⟩) (B 22529 (by norm_num) ⟨11264, by rfl⟩ (by norm_num))
theorem R60081 : Reach 60081 := rs (se 2 (by rfl) ⟨22530, by rfl⟩) (B 45061 (by norm_num) ⟨22530, by rfl⟩ (by norm_num))
theorem R60085 : Reach 60085 := rs (se 5 (by rfl) ⟨2816, by rfl⟩) (B 5633 (by norm_num) ⟨2816, by rfl⟩ (by norm_num))
theorem R60089 : Reach 60089 := rs (se 2 (by rfl) ⟨22533, by rfl⟩) (B 45067 (by norm_num) ⟨22533, by rfl⟩ (by norm_num))
theorem R92861 : Reach 92861 := rs (se 3 (by rfl) ⟨17411, by rfl⟩) (B 34823 (by norm_num) ⟨17411, by rfl⟩ (by norm_num))
theorem R60093 : Reach 60093 := rs (se 3 (by rfl) ⟨11267, by rfl⟩) (B 22535 (by norm_num) ⟨11267, by rfl⟩ (by norm_num))
theorem R60097 : Reach 60097 := rs (se 2 (by rfl) ⟨22536, by rfl⟩) (B 45073 (by norm_num) ⟨22536, by rfl⟩ (by norm_num))
theorem R60101 : Reach 60101 := rs (se 4 (by rfl) ⟨5634, by rfl⟩) (B 11269 (by norm_num) ⟨5634, by rfl⟩ (by norm_num))
theorem R60105 : Reach 60105 := rs (se 2 (by rfl) ⟨22539, by rfl⟩) (B 45079 (by norm_num) ⟨22539, by rfl⟩ (by norm_num))
theorem R60109 : Reach 60109 := rs (se 3 (by rfl) ⟨11270, by rfl⟩) (B 22541 (by norm_num) ⟨11270, by rfl⟩ (by norm_num))
theorem R60113 : Reach 60113 := rs (se 2 (by rfl) ⟨22542, by rfl⟩) (B 45085 (by norm_num) ⟨22542, by rfl⟩ (by norm_num))
theorem R60117 : Reach 60117 := rs (se 7 (by rfl) ⟨704, by rfl⟩) (B 1409 (by norm_num) ⟨704, by rfl⟩ (by norm_num))
theorem R92885 : Reach 92885 := rs (se 7 (by rfl) ⟨1088, by rfl⟩) (B 2177 (by norm_num) ⟨1088, by rfl⟩ (by norm_num))
theorem R60121 : Reach 60121 := rs (se 2 (by rfl) ⟨22545, by rfl⟩) (B 45091 (by norm_num) ⟨22545, by rfl⟩ (by norm_num))
theorem R60125 : Reach 60125 := rs (se 3 (by rfl) ⟨11273, by rfl⟩) (B 22547 (by norm_num) ⟨11273, by rfl⟩ (by norm_num))
theorem R60129 : Reach 60129 := rs (se 2 (by rfl) ⟨22548, by rfl⟩) (B 45097 (by norm_num) ⟨22548, by rfl⟩ (by norm_num))
theorem R60133 : Reach 60133 := rs (se 4 (by rfl) ⟨5637, by rfl⟩) (B 11275 (by norm_num) ⟨5637, by rfl⟩ (by norm_num))
theorem R60137 : Reach 60137 := rs (se 2 (by rfl) ⟨22551, by rfl⟩) (B 45103 (by norm_num) ⟨22551, by rfl⟩ (by norm_num))
theorem R60141 : Reach 60141 := rs (se 3 (by rfl) ⟨11276, by rfl⟩) (B 22553 (by norm_num) ⟨11276, by rfl⟩ (by norm_num))
theorem R92909 : Reach 92909 := rs (se 3 (by rfl) ⟨17420, by rfl⟩) (B 34841 (by norm_num) ⟨17420, by rfl⟩ (by norm_num))
theorem R60145 : Reach 60145 := rs (se 2 (by rfl) ⟨22554, by rfl⟩) (B 45109 (by norm_num) ⟨22554, by rfl⟩ (by norm_num))
theorem R60149 : Reach 60149 := rs (se 5 (by rfl) ⟨2819, by rfl⟩) (B 5639 (by norm_num) ⟨2819, by rfl⟩ (by norm_num))
theorem R60153 : Reach 60153 := rs (se 2 (by rfl) ⟨22557, by rfl⟩) (B 45115 (by norm_num) ⟨22557, by rfl⟩ (by norm_num))
theorem R60157 : Reach 60157 := rs (se 3 (by rfl) ⟨11279, by rfl⟩) (B 22559 (by norm_num) ⟨11279, by rfl⟩ (by norm_num))
theorem R60161 : Reach 60161 := rs (se 2 (by rfl) ⟨22560, by rfl⟩) (B 45121 (by norm_num) ⟨22560, by rfl⟩ (by norm_num))
theorem R60165 : Reach 60165 := rs (se 4 (by rfl) ⟨5640, by rfl⟩) (B 11281 (by norm_num) ⟨5640, by rfl⟩ (by norm_num))
theorem R92933 : Reach 92933 := rs (se 4 (by rfl) ⟨8712, by rfl⟩) (B 17425 (by norm_num) ⟨8712, by rfl⟩ (by norm_num))
theorem R60169 : Reach 60169 := rs (se 2 (by rfl) ⟨22563, by rfl⟩) (B 45127 (by norm_num) ⟨22563, by rfl⟩ (by norm_num))
theorem R60173 : Reach 60173 := rs (se 3 (by rfl) ⟨11282, by rfl⟩) (B 22565 (by norm_num) ⟨11282, by rfl⟩ (by norm_num))
theorem R60177 : Reach 60177 := rs (se 2 (by rfl) ⟨22566, by rfl⟩) (B 45133 (by norm_num) ⟨22566, by rfl⟩ (by norm_num))
theorem R60181 : Reach 60181 := rs (se 6 (by rfl) ⟨1410, by rfl⟩) (B 2821 (by norm_num) ⟨1410, by rfl⟩ (by norm_num))
theorem R60185 : Reach 60185 := rs (se 2 (by rfl) ⟨22569, by rfl⟩) (B 45139 (by norm_num) ⟨22569, by rfl⟩ (by norm_num))
theorem R60189 : Reach 60189 := rs (se 3 (by rfl) ⟨11285, by rfl⟩) (B 22571 (by norm_num) ⟨11285, by rfl⟩ (by norm_num))
theorem R92957 : Reach 92957 := rs (se 3 (by rfl) ⟨17429, by rfl⟩) (B 34859 (by norm_num) ⟨17429, by rfl⟩ (by norm_num))
theorem R60193 : Reach 60193 := rs (se 2 (by rfl) ⟨22572, by rfl⟩) (B 45145 (by norm_num) ⟨22572, by rfl⟩ (by norm_num))
theorem R60197 : Reach 60197 := rs (se 4 (by rfl) ⟨5643, by rfl⟩) (B 11287 (by norm_num) ⟨5643, by rfl⟩ (by norm_num))
theorem R60201 : Reach 60201 := rs (se 2 (by rfl) ⟨22575, by rfl⟩) (B 45151 (by norm_num) ⟨22575, by rfl⟩ (by norm_num))
theorem R60205 : Reach 60205 := rs (se 3 (by rfl) ⟨11288, by rfl⟩) (B 22577 (by norm_num) ⟨11288, by rfl⟩ (by norm_num))
theorem R60209 : Reach 60209 := rs (se 2 (by rfl) ⟨22578, by rfl⟩) (B 45157 (by norm_num) ⟨22578, by rfl⟩ (by norm_num))
theorem R60213 : Reach 60213 := rs (se 5 (by rfl) ⟨2822, by rfl⟩) (B 5645 (by norm_num) ⟨2822, by rfl⟩ (by norm_num))
theorem R92981 : Reach 92981 := rs (se 5 (by rfl) ⟨4358, by rfl⟩) (B 8717 (by norm_num) ⟨4358, by rfl⟩ (by norm_num))
theorem R60217 : Reach 60217 := rs (se 2 (by rfl) ⟨22581, by rfl⟩) (B 45163 (by norm_num) ⟨22581, by rfl⟩ (by norm_num))
theorem R60221 : Reach 60221 := rs (se 3 (by rfl) ⟨11291, by rfl⟩) (B 22583 (by norm_num) ⟨11291, by rfl⟩ (by norm_num))
theorem R60225 : Reach 60225 := rs (se 2 (by rfl) ⟨22584, by rfl⟩) (B 45169 (by norm_num) ⟨22584, by rfl⟩ (by norm_num))
theorem R60229 : Reach 60229 := rs (se 4 (by rfl) ⟨5646, by rfl⟩) (B 11293 (by norm_num) ⟨5646, by rfl⟩ (by norm_num))
theorem R60233 : Reach 60233 := rs (se 2 (by rfl) ⟨22587, by rfl⟩) (B 45175 (by norm_num) ⟨22587, by rfl⟩ (by norm_num))
theorem R60237 : Reach 60237 := rs (se 3 (by rfl) ⟨11294, by rfl⟩) (B 22589 (by norm_num) ⟨11294, by rfl⟩ (by norm_num))
theorem R93005 : Reach 93005 := rs (se 3 (by rfl) ⟨17438, by rfl⟩) (B 34877 (by norm_num) ⟨17438, by rfl⟩ (by norm_num))
theorem R60241 : Reach 60241 := rs (se 2 (by rfl) ⟨22590, by rfl⟩) (B 45181 (by norm_num) ⟨22590, by rfl⟩ (by norm_num))
theorem R60245 : Reach 60245 := rs (se 9 (by rfl) ⟨176, by rfl⟩) (B 353 (by norm_num) ⟨176, by rfl⟩ (by norm_num))
theorem R60249 : Reach 60249 := rs (se 2 (by rfl) ⟨22593, by rfl⟩) (B 45187 (by norm_num) ⟨22593, by rfl⟩ (by norm_num))
theorem R60253 : Reach 60253 := rs (se 3 (by rfl) ⟨11297, by rfl⟩) (B 22595 (by norm_num) ⟨11297, by rfl⟩ (by norm_num))
theorem R60257 : Reach 60257 := rs (se 2 (by rfl) ⟨22596, by rfl⟩) (B 45193 (by norm_num) ⟨22596, by rfl⟩ (by norm_num))
theorem R60261 : Reach 60261 := rs (se 4 (by rfl) ⟨5649, by rfl⟩) (B 11299 (by norm_num) ⟨5649, by rfl⟩ (by norm_num))
theorem R93029 : Reach 93029 := rs (se 4 (by rfl) ⟨8721, by rfl⟩) (B 17443 (by norm_num) ⟨8721, by rfl⟩ (by norm_num))
theorem R60265 : Reach 60265 := rs (se 2 (by rfl) ⟨22599, by rfl⟩) (B 45199 (by norm_num) ⟨22599, by rfl⟩ (by norm_num))
theorem R60269 : Reach 60269 := rs (se 3 (by rfl) ⟨11300, by rfl⟩) (B 22601 (by norm_num) ⟨11300, by rfl⟩ (by norm_num))
theorem R60273 : Reach 60273 := rs (se 2 (by rfl) ⟨22602, by rfl⟩) (B 45205 (by norm_num) ⟨22602, by rfl⟩ (by norm_num))
theorem R60277 : Reach 60277 := rs (se 5 (by rfl) ⟨2825, by rfl⟩) (B 5651 (by norm_num) ⟨2825, by rfl⟩ (by norm_num))
theorem R224117 : Reach 224117 := rs (se 5 (by rfl) ⟨10505, by rfl⟩) (B 21011 (by norm_num) ⟨10505, by rfl⟩ (by norm_num))
theorem R60281 : Reach 60281 := rs (se 2 (by rfl) ⟨22605, by rfl⟩) (B 45211 (by norm_num) ⟨22605, by rfl⟩ (by norm_num))
theorem R60285 : Reach 60285 := rs (se 3 (by rfl) ⟨11303, by rfl⟩) (B 22607 (by norm_num) ⟨11303, by rfl⟩ (by norm_num))
theorem R93053 : Reach 93053 := rs (se 3 (by rfl) ⟨17447, by rfl⟩) (B 34895 (by norm_num) ⟨17447, by rfl⟩ (by norm_num))
theorem R60289 : Reach 60289 := rs (se 2 (by rfl) ⟨22608, by rfl⟩) (B 45217 (by norm_num) ⟨22608, by rfl⟩ (by norm_num))
theorem R60293 : Reach 60293 := rs (se 4 (by rfl) ⟨5652, by rfl⟩) (B 11305 (by norm_num) ⟨5652, by rfl⟩ (by norm_num))
theorem R60297 : Reach 60297 := rs (se 2 (by rfl) ⟨22611, by rfl⟩) (B 45223 (by norm_num) ⟨22611, by rfl⟩ (by norm_num))
theorem R60301 : Reach 60301 := rs (se 3 (by rfl) ⟨11306, by rfl⟩) (B 22613 (by norm_num) ⟨11306, by rfl⟩ (by norm_num))
theorem R60305 : Reach 60305 := rs (se 2 (by rfl) ⟨22614, by rfl⟩) (B 45229 (by norm_num) ⟨22614, by rfl⟩ (by norm_num))
theorem R60309 : Reach 60309 := rs (se 6 (by rfl) ⟨1413, by rfl⟩) (B 2827 (by norm_num) ⟨1413, by rfl⟩ (by norm_num))
theorem R93077 : Reach 93077 := rs (se 6 (by rfl) ⟨2181, by rfl⟩) (B 4363 (by norm_num) ⟨2181, by rfl⟩ (by norm_num))
theorem R60313 : Reach 60313 := rs (se 2 (by rfl) ⟨22617, by rfl⟩) (B 45235 (by norm_num) ⟨22617, by rfl⟩ (by norm_num))
theorem R60317 : Reach 60317 := rs (se 3 (by rfl) ⟨11309, by rfl⟩) (B 22619 (by norm_num) ⟨11309, by rfl⟩ (by norm_num))
theorem R60321 : Reach 60321 := rs (se 2 (by rfl) ⟨22620, by rfl⟩) (B 45241 (by norm_num) ⟨22620, by rfl⟩ (by norm_num))
theorem R60325 : Reach 60325 := rs (se 4 (by rfl) ⟨5655, by rfl⟩) (B 11311 (by norm_num) ⟨5655, by rfl⟩ (by norm_num))
theorem R60329 : Reach 60329 := rs (se 2 (by rfl) ⟨22623, by rfl⟩) (B 45247 (by norm_num) ⟨22623, by rfl⟩ (by norm_num))
theorem R60333 : Reach 60333 := rs (se 3 (by rfl) ⟨11312, by rfl⟩) (B 22625 (by norm_num) ⟨11312, by rfl⟩ (by norm_num))
theorem R93101 : Reach 93101 := rs (se 3 (by rfl) ⟨17456, by rfl⟩) (B 34913 (by norm_num) ⟨17456, by rfl⟩ (by norm_num))
theorem R60337 : Reach 60337 := rs (se 2 (by rfl) ⟨22626, by rfl⟩) (B 45253 (by norm_num) ⟨22626, by rfl⟩ (by norm_num))
theorem R60341 : Reach 60341 := rs (se 5 (by rfl) ⟨2828, by rfl⟩) (B 5657 (by norm_num) ⟨2828, by rfl⟩ (by norm_num))
theorem R60345 : Reach 60345 := rs (se 2 (by rfl) ⟨22629, by rfl⟩) (B 45259 (by norm_num) ⟨22629, by rfl⟩ (by norm_num))
theorem R60349 : Reach 60349 := rs (se 3 (by rfl) ⟨11315, by rfl⟩) (B 22631 (by norm_num) ⟨11315, by rfl⟩ (by norm_num))
theorem R60353 : Reach 60353 := rs (se 2 (by rfl) ⟨22632, by rfl⟩) (B 45265 (by norm_num) ⟨22632, by rfl⟩ (by norm_num))
theorem R60357 : Reach 60357 := rs (se 4 (by rfl) ⟨5658, by rfl⟩) (B 11317 (by norm_num) ⟨5658, by rfl⟩ (by norm_num))
theorem R93125 : Reach 93125 := rs (se 4 (by rfl) ⟨8730, by rfl⟩) (B 17461 (by norm_num) ⟨8730, by rfl⟩ (by norm_num))
theorem R60361 : Reach 60361 := rs (se 2 (by rfl) ⟨22635, by rfl⟩) (B 45271 (by norm_num) ⟨22635, by rfl⟩ (by norm_num))
theorem R60365 : Reach 60365 := rs (se 3 (by rfl) ⟨11318, by rfl⟩) (B 22637 (by norm_num) ⟨11318, by rfl⟩ (by norm_num))
theorem R60369 : Reach 60369 := rs (se 2 (by rfl) ⟨22638, by rfl⟩) (B 45277 (by norm_num) ⟨22638, by rfl⟩ (by norm_num))
theorem R60373 : Reach 60373 := rs (se 7 (by rfl) ⟨707, by rfl⟩) (B 1415 (by norm_num) ⟨707, by rfl⟩ (by norm_num))
theorem R60377 : Reach 60377 := rs (se 2 (by rfl) ⟨22641, by rfl⟩) (B 45283 (by norm_num) ⟨22641, by rfl⟩ (by norm_num))
theorem R60381 : Reach 60381 := rs (se 3 (by rfl) ⟨11321, by rfl⟩) (B 22643 (by norm_num) ⟨11321, by rfl⟩ (by norm_num))
theorem R93149 : Reach 93149 := rs (se 3 (by rfl) ⟨17465, by rfl⟩) (B 34931 (by norm_num) ⟨17465, by rfl⟩ (by norm_num))
theorem R60385 : Reach 60385 := rs (se 2 (by rfl) ⟨22644, by rfl⟩) (B 45289 (by norm_num) ⟨22644, by rfl⟩ (by norm_num))
theorem R60389 : Reach 60389 := rs (se 4 (by rfl) ⟨5661, by rfl⟩) (B 11323 (by norm_num) ⟨5661, by rfl⟩ (by norm_num))
theorem R60393 : Reach 60393 := rs (se 2 (by rfl) ⟨22647, by rfl⟩) (B 45295 (by norm_num) ⟨22647, by rfl⟩ (by norm_num))
theorem R60397 : Reach 60397 := rs (se 3 (by rfl) ⟨11324, by rfl⟩) (B 22649 (by norm_num) ⟨11324, by rfl⟩ (by norm_num))
theorem R60401 : Reach 60401 := rs (se 2 (by rfl) ⟨22650, by rfl⟩) (B 45301 (by norm_num) ⟨22650, by rfl⟩ (by norm_num))
theorem R60405 : Reach 60405 := rs (se 5 (by rfl) ⟨2831, by rfl⟩) (B 5663 (by norm_num) ⟨2831, by rfl⟩ (by norm_num))
theorem R93173 : Reach 93173 := rs (se 5 (by rfl) ⟨4367, by rfl⟩) (B 8735 (by norm_num) ⟨4367, by rfl⟩ (by norm_num))
theorem R60409 : Reach 60409 := rs (se 2 (by rfl) ⟨22653, by rfl⟩) (B 45307 (by norm_num) ⟨22653, by rfl⟩ (by norm_num))
theorem R60413 : Reach 60413 := rs (se 3 (by rfl) ⟨11327, by rfl⟩) (B 22655 (by norm_num) ⟨11327, by rfl⟩ (by norm_num))
theorem R60417 : Reach 60417 := rs (se 2 (by rfl) ⟨22656, by rfl⟩) (B 45313 (by norm_num) ⟨22656, by rfl⟩ (by norm_num))
theorem R60421 : Reach 60421 := rs (se 4 (by rfl) ⟨5664, by rfl⟩) (B 11329 (by norm_num) ⟨5664, by rfl⟩ (by norm_num))
theorem R60425 : Reach 60425 := rs (se 2 (by rfl) ⟨22659, by rfl⟩) (B 45319 (by norm_num) ⟨22659, by rfl⟩ (by norm_num))
theorem R60429 : Reach 60429 := rs (se 3 (by rfl) ⟨11330, by rfl⟩) (B 22661 (by norm_num) ⟨11330, by rfl⟩ (by norm_num))
theorem R93197 : Reach 93197 := rs (se 3 (by rfl) ⟨17474, by rfl⟩) (B 34949 (by norm_num) ⟨17474, by rfl⟩ (by norm_num))
theorem R60433 : Reach 60433 := rs (se 2 (by rfl) ⟨22662, by rfl⟩) (B 45325 (by norm_num) ⟨22662, by rfl⟩ (by norm_num))
theorem R60437 : Reach 60437 := rs (se 6 (by rfl) ⟨1416, by rfl⟩) (B 2833 (by norm_num) ⟨1416, by rfl⟩ (by norm_num))
theorem R60441 : Reach 60441 := rs (se 2 (by rfl) ⟨22665, by rfl⟩) (B 45331 (by norm_num) ⟨22665, by rfl⟩ (by norm_num))
theorem R60445 : Reach 60445 := rs (se 3 (by rfl) ⟨11333, by rfl⟩) (B 22667 (by norm_num) ⟨11333, by rfl⟩ (by norm_num))
theorem R60449 : Reach 60449 := rs (se 2 (by rfl) ⟨22668, by rfl⟩) (B 45337 (by norm_num) ⟨22668, by rfl⟩ (by norm_num))
theorem R60453 : Reach 60453 := rs (se 4 (by rfl) ⟨5667, by rfl⟩) (B 11335 (by norm_num) ⟨5667, by rfl⟩ (by norm_num))
theorem R93221 : Reach 93221 := rs (se 4 (by rfl) ⟨8739, by rfl⟩) (B 17479 (by norm_num) ⟨8739, by rfl⟩ (by norm_num))
theorem R60457 : Reach 60457 := rs (se 2 (by rfl) ⟨22671, by rfl⟩) (B 45343 (by norm_num) ⟨22671, by rfl⟩ (by norm_num))
theorem R60461 : Reach 60461 := rs (se 3 (by rfl) ⟨11336, by rfl⟩) (B 22673 (by norm_num) ⟨11336, by rfl⟩ (by norm_num))
theorem R60465 : Reach 60465 := rs (se 2 (by rfl) ⟨22674, by rfl⟩) (B 45349 (by norm_num) ⟨22674, by rfl⟩ (by norm_num))
theorem R60469 : Reach 60469 := rs (se 5 (by rfl) ⟨2834, by rfl⟩) (B 5669 (by norm_num) ⟨2834, by rfl⟩ (by norm_num))
theorem R60473 : Reach 60473 := rs (se 2 (by rfl) ⟨22677, by rfl⟩) (B 45355 (by norm_num) ⟨22677, by rfl⟩ (by norm_num))
theorem R60477 : Reach 60477 := rs (se 3 (by rfl) ⟨11339, by rfl⟩) (B 22679 (by norm_num) ⟨11339, by rfl⟩ (by norm_num))
theorem R93245 : Reach 93245 := rs (se 3 (by rfl) ⟨17483, by rfl⟩) (B 34967 (by norm_num) ⟨17483, by rfl⟩ (by norm_num))
theorem R60481 : Reach 60481 := rs (se 2 (by rfl) ⟨22680, by rfl⟩) (B 45361 (by norm_num) ⟨22680, by rfl⟩ (by norm_num))
theorem R60485 : Reach 60485 := rs (se 4 (by rfl) ⟨5670, by rfl⟩) (B 11341 (by norm_num) ⟨5670, by rfl⟩ (by norm_num))
theorem R60489 : Reach 60489 := rs (se 2 (by rfl) ⟨22683, by rfl⟩) (B 45367 (by norm_num) ⟨22683, by rfl⟩ (by norm_num))
theorem R60493 : Reach 60493 := rs (se 3 (by rfl) ⟨11342, by rfl⟩) (B 22685 (by norm_num) ⟨11342, by rfl⟩ (by norm_num))
theorem R60497 : Reach 60497 := rs (se 2 (by rfl) ⟨22686, by rfl⟩) (B 45373 (by norm_num) ⟨22686, by rfl⟩ (by norm_num))
theorem R60501 : Reach 60501 := rs (se 8 (by rfl) ⟨354, by rfl⟩) (B 709 (by norm_num) ⟨354, by rfl⟩ (by norm_num))
theorem R93269 : Reach 93269 := rs (se 8 (by rfl) ⟨546, by rfl⟩) (B 1093 (by norm_num) ⟨546, by rfl⟩ (by norm_num))
theorem R60505 : Reach 60505 := rs (se 2 (by rfl) ⟨22689, by rfl⟩) (B 45379 (by norm_num) ⟨22689, by rfl⟩ (by norm_num))
theorem R60509 : Reach 60509 := rs (se 3 (by rfl) ⟨11345, by rfl⟩) (B 22691 (by norm_num) ⟨11345, by rfl⟩ (by norm_num))
theorem R60513 : Reach 60513 := rs (se 2 (by rfl) ⟨22692, by rfl⟩) (B 45385 (by norm_num) ⟨22692, by rfl⟩ (by norm_num))
theorem R60517 : Reach 60517 := rs (se 4 (by rfl) ⟨5673, by rfl⟩) (B 11347 (by norm_num) ⟨5673, by rfl⟩ (by norm_num))
theorem R60521 : Reach 60521 := rs (se 2 (by rfl) ⟨22695, by rfl⟩) (B 45391 (by norm_num) ⟨22695, by rfl⟩ (by norm_num))
theorem R60525 : Reach 60525 := rs (se 3 (by rfl) ⟨11348, by rfl⟩) (B 22697 (by norm_num) ⟨11348, by rfl⟩ (by norm_num))
theorem R93293 : Reach 93293 := rs (se 3 (by rfl) ⟨17492, by rfl⟩) (B 34985 (by norm_num) ⟨17492, by rfl⟩ (by norm_num))
theorem R60529 : Reach 60529 := rs (se 2 (by rfl) ⟨22698, by rfl⟩) (B 45397 (by norm_num) ⟨22698, by rfl⟩ (by norm_num))
theorem R60533 : Reach 60533 := rs (se 5 (by rfl) ⟨2837, by rfl⟩) (B 5675 (by norm_num) ⟨2837, by rfl⟩ (by norm_num))
theorem R60537 : Reach 60537 := rs (se 2 (by rfl) ⟨22701, by rfl⟩) (B 45403 (by norm_num) ⟨22701, by rfl⟩ (by norm_num))
theorem R60541 : Reach 60541 := rs (se 3 (by rfl) ⟨11351, by rfl⟩) (B 22703 (by norm_num) ⟨11351, by rfl⟩ (by norm_num))
theorem R60545 : Reach 60545 := rs (se 2 (by rfl) ⟨22704, by rfl⟩) (B 45409 (by norm_num) ⟨22704, by rfl⟩ (by norm_num))
theorem R60549 : Reach 60549 := rs (se 4 (by rfl) ⟨5676, by rfl⟩) (B 11353 (by norm_num) ⟨5676, by rfl⟩ (by norm_num))
theorem R93317 : Reach 93317 := rs (se 4 (by rfl) ⟨8748, by rfl⟩) (B 17497 (by norm_num) ⟨8748, by rfl⟩ (by norm_num))
theorem R60553 : Reach 60553 := rs (se 2 (by rfl) ⟨22707, by rfl⟩) (B 45415 (by norm_num) ⟨22707, by rfl⟩ (by norm_num))
theorem R60557 : Reach 60557 := rs (se 3 (by rfl) ⟨11354, by rfl⟩) (B 22709 (by norm_num) ⟨11354, by rfl⟩ (by norm_num))
theorem R60561 : Reach 60561 := rs (se 2 (by rfl) ⟨22710, by rfl⟩) (B 45421 (by norm_num) ⟨22710, by rfl⟩ (by norm_num))
theorem R60565 : Reach 60565 := rs (se 6 (by rfl) ⟨1419, by rfl⟩) (B 2839 (by norm_num) ⟨1419, by rfl⟩ (by norm_num))
theorem R60569 : Reach 60569 := rs (se 2 (by rfl) ⟨22713, by rfl⟩) (B 45427 (by norm_num) ⟨22713, by rfl⟩ (by norm_num))
theorem R60573 : Reach 60573 := rs (se 3 (by rfl) ⟨11357, by rfl⟩) (B 22715 (by norm_num) ⟨11357, by rfl⟩ (by norm_num))
theorem R93341 : Reach 93341 := rs (se 3 (by rfl) ⟨17501, by rfl⟩) (B 35003 (by norm_num) ⟨17501, by rfl⟩ (by norm_num))
theorem R60577 : Reach 60577 := rs (se 2 (by rfl) ⟨22716, by rfl⟩) (B 45433 (by norm_num) ⟨22716, by rfl⟩ (by norm_num))
theorem R60581 : Reach 60581 := rs (se 4 (by rfl) ⟨5679, by rfl⟩) (B 11359 (by norm_num) ⟨5679, by rfl⟩ (by norm_num))
theorem R60585 : Reach 60585 := rs (se 2 (by rfl) ⟨22719, by rfl⟩) (B 45439 (by norm_num) ⟨22719, by rfl⟩ (by norm_num))
theorem R60589 : Reach 60589 := rs (se 3 (by rfl) ⟨11360, by rfl⟩) (B 22721 (by norm_num) ⟨11360, by rfl⟩ (by norm_num))
theorem R60593 : Reach 60593 := rs (se 2 (by rfl) ⟨22722, by rfl⟩) (B 45445 (by norm_num) ⟨22722, by rfl⟩ (by norm_num))
theorem R60597 : Reach 60597 := rs (se 5 (by rfl) ⟨2840, by rfl⟩) (B 5681 (by norm_num) ⟨2840, by rfl⟩ (by norm_num))
theorem R93365 : Reach 93365 := rs (se 5 (by rfl) ⟨4376, by rfl⟩) (B 8753 (by norm_num) ⟨4376, by rfl⟩ (by norm_num))
theorem R60601 : Reach 60601 := rs (se 2 (by rfl) ⟨22725, by rfl⟩) (B 45451 (by norm_num) ⟨22725, by rfl⟩ (by norm_num))
theorem R60605 : Reach 60605 := rs (se 3 (by rfl) ⟨11363, by rfl⟩) (B 22727 (by norm_num) ⟨11363, by rfl⟩ (by norm_num))
theorem R60609 : Reach 60609 := rs (se 2 (by rfl) ⟨22728, by rfl⟩) (B 45457 (by norm_num) ⟨22728, by rfl⟩ (by norm_num))
theorem R60613 : Reach 60613 := rs (se 4 (by rfl) ⟨5682, by rfl⟩) (B 11365 (by norm_num) ⟨5682, by rfl⟩ (by norm_num))
theorem R60617 : Reach 60617 := rs (se 2 (by rfl) ⟨22731, by rfl⟩) (B 45463 (by norm_num) ⟨22731, by rfl⟩ (by norm_num))
theorem R60621 : Reach 60621 := rs (se 3 (by rfl) ⟨11366, by rfl⟩) (B 22733 (by norm_num) ⟨11366, by rfl⟩ (by norm_num))
theorem R93389 : Reach 93389 := rs (se 3 (by rfl) ⟨17510, by rfl⟩) (B 35021 (by norm_num) ⟨17510, by rfl⟩ (by norm_num))
theorem R60625 : Reach 60625 := rs (se 2 (by rfl) ⟨22734, by rfl⟩) (B 45469 (by norm_num) ⟨22734, by rfl⟩ (by norm_num))
theorem R60629 : Reach 60629 := rs (se 7 (by rfl) ⟨710, by rfl⟩) (B 1421 (by norm_num) ⟨710, by rfl⟩ (by norm_num))
theorem R60633 : Reach 60633 := rs (se 2 (by rfl) ⟨22737, by rfl⟩) (B 45475 (by norm_num) ⟨22737, by rfl⟩ (by norm_num))
theorem R60637 : Reach 60637 := rs (se 3 (by rfl) ⟨11369, by rfl⟩) (B 22739 (by norm_num) ⟨11369, by rfl⟩ (by norm_num))
theorem R60641 : Reach 60641 := rs (se 2 (by rfl) ⟨22740, by rfl⟩) (B 45481 (by norm_num) ⟨22740, by rfl⟩ (by norm_num))
theorem R60645 : Reach 60645 := rs (se 4 (by rfl) ⟨5685, by rfl⟩) (B 11371 (by norm_num) ⟨5685, by rfl⟩ (by norm_num))
theorem R93413 : Reach 93413 := rs (se 4 (by rfl) ⟨8757, by rfl⟩) (B 17515 (by norm_num) ⟨8757, by rfl⟩ (by norm_num))
theorem R60649 : Reach 60649 := rs (se 2 (by rfl) ⟨22743, by rfl⟩) (B 45487 (by norm_num) ⟨22743, by rfl⟩ (by norm_num))
theorem R60653 : Reach 60653 := rs (se 3 (by rfl) ⟨11372, by rfl⟩) (B 22745 (by norm_num) ⟨11372, by rfl⟩ (by norm_num))
theorem R60657 : Reach 60657 := rs (se 2 (by rfl) ⟨22746, by rfl⟩) (B 45493 (by norm_num) ⟨22746, by rfl⟩ (by norm_num))
theorem R60661 : Reach 60661 := rs (se 5 (by rfl) ⟨2843, by rfl⟩) (B 5687 (by norm_num) ⟨2843, by rfl⟩ (by norm_num))
theorem R60665 : Reach 60665 := rs (se 2 (by rfl) ⟨22749, by rfl⟩) (B 45499 (by norm_num) ⟨22749, by rfl⟩ (by norm_num))
theorem R60669 : Reach 60669 := rs (se 3 (by rfl) ⟨11375, by rfl⟩) (B 22751 (by norm_num) ⟨11375, by rfl⟩ (by norm_num))
theorem R93437 : Reach 93437 := rs (se 3 (by rfl) ⟨17519, by rfl⟩) (B 35039 (by norm_num) ⟨17519, by rfl⟩ (by norm_num))
theorem R60673 : Reach 60673 := rs (se 2 (by rfl) ⟨22752, by rfl⟩) (B 45505 (by norm_num) ⟨22752, by rfl⟩ (by norm_num))
theorem R60677 : Reach 60677 := rs (se 4 (by rfl) ⟨5688, by rfl⟩) (B 11377 (by norm_num) ⟨5688, by rfl⟩ (by norm_num))
theorem R60681 : Reach 60681 := rs (se 2 (by rfl) ⟨22755, by rfl⟩) (B 45511 (by norm_num) ⟨22755, by rfl⟩ (by norm_num))
theorem R60685 : Reach 60685 := rs (se 3 (by rfl) ⟨11378, by rfl⟩) (B 22757 (by norm_num) ⟨11378, by rfl⟩ (by norm_num))
theorem R60689 : Reach 60689 := rs (se 2 (by rfl) ⟨22758, by rfl⟩) (B 45517 (by norm_num) ⟨22758, by rfl⟩ (by norm_num))
theorem R60693 : Reach 60693 := rs (se 6 (by rfl) ⟨1422, by rfl⟩) (B 2845 (by norm_num) ⟨1422, by rfl⟩ (by norm_num))
theorem R93461 : Reach 93461 := rs (se 6 (by rfl) ⟨2190, by rfl⟩) (B 4381 (by norm_num) ⟨2190, by rfl⟩ (by norm_num))
theorem R60697 : Reach 60697 := rs (se 2 (by rfl) ⟨22761, by rfl⟩) (B 45523 (by norm_num) ⟨22761, by rfl⟩ (by norm_num))
theorem R60701 : Reach 60701 := rs (se 3 (by rfl) ⟨11381, by rfl⟩) (B 22763 (by norm_num) ⟨11381, by rfl⟩ (by norm_num))
theorem R60705 : Reach 60705 := rs (se 2 (by rfl) ⟨22764, by rfl⟩) (B 45529 (by norm_num) ⟨22764, by rfl⟩ (by norm_num))
theorem R60709 : Reach 60709 := rs (se 4 (by rfl) ⟨5691, by rfl⟩) (B 11383 (by norm_num) ⟨5691, by rfl⟩ (by norm_num))
theorem R60713 : Reach 60713 := rs (se 2 (by rfl) ⟨22767, by rfl⟩) (B 45535 (by norm_num) ⟨22767, by rfl⟩ (by norm_num))
theorem R93485 : Reach 93485 := rs (se 3 (by rfl) ⟨17528, by rfl⟩) (B 35057 (by norm_num) ⟨17528, by rfl⟩ (by norm_num))
theorem R60717 : Reach 60717 := rs (se 3 (by rfl) ⟨11384, by rfl⟩) (B 22769 (by norm_num) ⟨11384, by rfl⟩ (by norm_num))
theorem R60721 : Reach 60721 := rs (se 2 (by rfl) ⟨22770, by rfl⟩) (B 45541 (by norm_num) ⟨22770, by rfl⟩ (by norm_num))
theorem R60725 : Reach 60725 := rs (se 5 (by rfl) ⟨2846, by rfl⟩) (B 5693 (by norm_num) ⟨2846, by rfl⟩ (by norm_num))
theorem R60729 : Reach 60729 := rs (se 2 (by rfl) ⟨22773, by rfl⟩) (B 45547 (by norm_num) ⟨22773, by rfl⟩ (by norm_num))
theorem R60733 : Reach 60733 := rs (se 3 (by rfl) ⟨11387, by rfl⟩) (B 22775 (by norm_num) ⟨11387, by rfl⟩ (by norm_num))
theorem R60737 : Reach 60737 := rs (se 2 (by rfl) ⟨22776, by rfl⟩) (B 45553 (by norm_num) ⟨22776, by rfl⟩ (by norm_num))
theorem R60741 : Reach 60741 := rs (se 4 (by rfl) ⟨5694, by rfl⟩) (B 11389 (by norm_num) ⟨5694, by rfl⟩ (by norm_num))
theorem R93509 : Reach 93509 := rs (se 4 (by rfl) ⟨8766, by rfl⟩) (B 17533 (by norm_num) ⟨8766, by rfl⟩ (by norm_num))
theorem R60745 : Reach 60745 := rs (se 2 (by rfl) ⟨22779, by rfl⟩) (B 45559 (by norm_num) ⟨22779, by rfl⟩ (by norm_num))
theorem R60749 : Reach 60749 := rs (se 3 (by rfl) ⟨11390, by rfl⟩) (B 22781 (by norm_num) ⟨11390, by rfl⟩ (by norm_num))
theorem R60753 : Reach 60753 := rs (se 2 (by rfl) ⟨22782, by rfl⟩) (B 45565 (by norm_num) ⟨22782, by rfl⟩ (by norm_num))
theorem R60757 : Reach 60757 := rs (se 11 (by rfl) ⟨44, by rfl⟩) (B 89 (by norm_num) ⟨44, by rfl⟩ (by norm_num))
theorem R60761 : Reach 60761 := rs (se 2 (by rfl) ⟨22785, by rfl⟩) (B 45571 (by norm_num) ⟨22785, by rfl⟩ (by norm_num))
theorem R60765 : Reach 60765 := rs (se 3 (by rfl) ⟨11393, by rfl⟩) (B 22787 (by norm_num) ⟨11393, by rfl⟩ (by norm_num))
theorem R93533 : Reach 93533 := rs (se 3 (by rfl) ⟨17537, by rfl⟩) (B 35075 (by norm_num) ⟨17537, by rfl⟩ (by norm_num))
theorem R60769 : Reach 60769 := rs (se 2 (by rfl) ⟨22788, by rfl⟩) (B 45577 (by norm_num) ⟨22788, by rfl⟩ (by norm_num))
theorem R60773 : Reach 60773 := rs (se 4 (by rfl) ⟨5697, by rfl⟩) (B 11395 (by norm_num) ⟨5697, by rfl⟩ (by norm_num))
theorem R60777 : Reach 60777 := rs (se 2 (by rfl) ⟨22791, by rfl⟩) (B 45583 (by norm_num) ⟨22791, by rfl⟩ (by norm_num))
theorem R60781 : Reach 60781 := rs (se 3 (by rfl) ⟨11396, by rfl⟩) (B 22793 (by norm_num) ⟨11396, by rfl⟩ (by norm_num))
theorem R60785 : Reach 60785 := rs (se 2 (by rfl) ⟨22794, by rfl⟩) (B 45589 (by norm_num) ⟨22794, by rfl⟩ (by norm_num))
theorem R60789 : Reach 60789 := rs (se 5 (by rfl) ⟨2849, by rfl⟩) (B 5699 (by norm_num) ⟨2849, by rfl⟩ (by norm_num))
theorem R126325 : Reach 126325 := rs (se 5 (by rfl) ⟨5921, by rfl⟩) (B 11843 (by norm_num) ⟨5921, by rfl⟩ (by norm_num))
theorem R93557 : Reach 93557 := rs (se 5 (by rfl) ⟨4385, by rfl⟩) (B 8771 (by norm_num) ⟨4385, by rfl⟩ (by norm_num))
theorem R60793 : Reach 60793 := rs (se 2 (by rfl) ⟨22797, by rfl⟩) (B 45595 (by norm_num) ⟨22797, by rfl⟩ (by norm_num))
theorem R60797 : Reach 60797 := rs (se 3 (by rfl) ⟨11399, by rfl⟩) (B 22799 (by norm_num) ⟨11399, by rfl⟩ (by norm_num))
theorem R60801 : Reach 60801 := rs (se 2 (by rfl) ⟨22800, by rfl⟩) (B 45601 (by norm_num) ⟨22800, by rfl⟩ (by norm_num))
theorem R60805 : Reach 60805 := rs (se 4 (by rfl) ⟨5700, by rfl⟩) (B 11401 (by norm_num) ⟨5700, by rfl⟩ (by norm_num))
theorem R60809 : Reach 60809 := rs (se 2 (by rfl) ⟨22803, by rfl⟩) (B 45607 (by norm_num) ⟨22803, by rfl⟩ (by norm_num))
theorem R60813 : Reach 60813 := rs (se 3 (by rfl) ⟨11402, by rfl⟩) (B 22805 (by norm_num) ⟨11402, by rfl⟩ (by norm_num))
theorem R93581 : Reach 93581 := rs (se 3 (by rfl) ⟨17546, by rfl⟩) (B 35093 (by norm_num) ⟨17546, by rfl⟩ (by norm_num))
theorem R60817 : Reach 60817 := rs (se 2 (by rfl) ⟨22806, by rfl⟩) (B 45613 (by norm_num) ⟨22806, by rfl⟩ (by norm_num))
theorem R60821 : Reach 60821 := rs (se 6 (by rfl) ⟨1425, by rfl⟩) (B 2851 (by norm_num) ⟨1425, by rfl⟩ (by norm_num))
theorem R60825 : Reach 60825 := rs (se 2 (by rfl) ⟨22809, by rfl⟩) (B 45619 (by norm_num) ⟨22809, by rfl⟩ (by norm_num))
theorem R60829 : Reach 60829 := rs (se 3 (by rfl) ⟨11405, by rfl⟩) (B 22811 (by norm_num) ⟨11405, by rfl⟩ (by norm_num))
theorem R60833 : Reach 60833 := rs (se 2 (by rfl) ⟨22812, by rfl⟩) (B 45625 (by norm_num) ⟨22812, by rfl⟩ (by norm_num))
theorem R60837 : Reach 60837 := rs (se 4 (by rfl) ⟨5703, by rfl⟩) (B 11407 (by norm_num) ⟨5703, by rfl⟩ (by norm_num))
theorem R93605 : Reach 93605 := rs (se 4 (by rfl) ⟨8775, by rfl⟩) (B 17551 (by norm_num) ⟨8775, by rfl⟩ (by norm_num))
theorem R60841 : Reach 60841 := rs (se 2 (by rfl) ⟨22815, by rfl⟩) (B 45631 (by norm_num) ⟨22815, by rfl⟩ (by norm_num))
theorem R60845 : Reach 60845 := rs (se 3 (by rfl) ⟨11408, by rfl⟩) (B 22817 (by norm_num) ⟨11408, by rfl⟩ (by norm_num))
theorem R60849 : Reach 60849 := rs (se 2 (by rfl) ⟨22818, by rfl⟩) (B 45637 (by norm_num) ⟨22818, by rfl⟩ (by norm_num))
theorem R60853 : Reach 60853 := rs (se 5 (by rfl) ⟨2852, by rfl⟩) (B 5705 (by norm_num) ⟨2852, by rfl⟩ (by norm_num))
theorem R60857 : Reach 60857 := rs (se 2 (by rfl) ⟨22821, by rfl⟩) (B 45643 (by norm_num) ⟨22821, by rfl⟩ (by norm_num))
theorem R60861 : Reach 60861 := rs (se 3 (by rfl) ⟨11411, by rfl⟩) (B 22823 (by norm_num) ⟨11411, by rfl⟩ (by norm_num))
theorem R93629 : Reach 93629 := rs (se 3 (by rfl) ⟨17555, by rfl⟩) (B 35111 (by norm_num) ⟨17555, by rfl⟩ (by norm_num))
theorem R60865 : Reach 60865 := rs (se 2 (by rfl) ⟨22824, by rfl⟩) (B 45649 (by norm_num) ⟨22824, by rfl⟩ (by norm_num))
theorem R60869 : Reach 60869 := rs (se 4 (by rfl) ⟨5706, by rfl⟩) (B 11413 (by norm_num) ⟨5706, by rfl⟩ (by norm_num))
theorem R60873 : Reach 60873 := rs (se 2 (by rfl) ⟨22827, by rfl⟩) (B 45655 (by norm_num) ⟨22827, by rfl⟩ (by norm_num))
theorem R60877 : Reach 60877 := rs (se 3 (by rfl) ⟨11414, by rfl⟩) (B 22829 (by norm_num) ⟨11414, by rfl⟩ (by norm_num))
theorem R60881 : Reach 60881 := rs (se 2 (by rfl) ⟨22830, by rfl⟩) (B 45661 (by norm_num) ⟨22830, by rfl⟩ (by norm_num))
theorem R60885 : Reach 60885 := rs (se 7 (by rfl) ⟨713, by rfl⟩) (B 1427 (by norm_num) ⟨713, by rfl⟩ (by norm_num))
theorem R93653 : Reach 93653 := rs (se 7 (by rfl) ⟨1097, by rfl⟩) (B 2195 (by norm_num) ⟨1097, by rfl⟩ (by norm_num))
theorem R60889 : Reach 60889 := rs (se 2 (by rfl) ⟨22833, by rfl⟩) (B 45667 (by norm_num) ⟨22833, by rfl⟩ (by norm_num))
theorem R60893 : Reach 60893 := rs (se 3 (by rfl) ⟨11417, by rfl⟩) (B 22835 (by norm_num) ⟨11417, by rfl⟩ (by norm_num))
theorem R60897 : Reach 60897 := rs (se 2 (by rfl) ⟨22836, by rfl⟩) (B 45673 (by norm_num) ⟨22836, by rfl⟩ (by norm_num))
theorem R60901 : Reach 60901 := rs (se 4 (by rfl) ⟨5709, by rfl⟩) (B 11419 (by norm_num) ⟨5709, by rfl⟩ (by norm_num))
theorem R159205 : Reach 159205 := rs (se 4 (by rfl) ⟨14925, by rfl⟩) (B 29851 (by norm_num) ⟨14925, by rfl⟩ (by norm_num))
theorem R60905 : Reach 60905 := rs (se 2 (by rfl) ⟨22839, by rfl⟩) (B 45679 (by norm_num) ⟨22839, by rfl⟩ (by norm_num))
theorem R60909 : Reach 60909 := rs (se 3 (by rfl) ⟨11420, by rfl⟩) (B 22841 (by norm_num) ⟨11420, by rfl⟩ (by norm_num))
theorem R93677 : Reach 93677 := rs (se 3 (by rfl) ⟨17564, by rfl⟩) (B 35129 (by norm_num) ⟨17564, by rfl⟩ (by norm_num))
theorem R60913 : Reach 60913 := rs (se 2 (by rfl) ⟨22842, by rfl⟩) (B 45685 (by norm_num) ⟨22842, by rfl⟩ (by norm_num))
theorem R60917 : Reach 60917 := rs (se 5 (by rfl) ⟨2855, by rfl⟩) (B 5711 (by norm_num) ⟨2855, by rfl⟩ (by norm_num))
theorem R60921 : Reach 60921 := rs (se 2 (by rfl) ⟨22845, by rfl⟩) (B 45691 (by norm_num) ⟨22845, by rfl⟩ (by norm_num))
theorem R60925 : Reach 60925 := rs (se 3 (by rfl) ⟨11423, by rfl⟩) (B 22847 (by norm_num) ⟨11423, by rfl⟩ (by norm_num))
theorem R60929 : Reach 60929 := rs (se 2 (by rfl) ⟨22848, by rfl⟩) (B 45697 (by norm_num) ⟨22848, by rfl⟩ (by norm_num))
theorem R60933 : Reach 60933 := rs (se 4 (by rfl) ⟨5712, by rfl⟩) (B 11425 (by norm_num) ⟨5712, by rfl⟩ (by norm_num))
theorem R93701 : Reach 93701 := rs (se 4 (by rfl) ⟨8784, by rfl⟩) (B 17569 (by norm_num) ⟨8784, by rfl⟩ (by norm_num))
theorem R60937 : Reach 60937 := rs (se 2 (by rfl) ⟨22851, by rfl⟩) (B 45703 (by norm_num) ⟨22851, by rfl⟩ (by norm_num))
theorem R60941 : Reach 60941 := rs (se 3 (by rfl) ⟨11426, by rfl⟩) (B 22853 (by norm_num) ⟨11426, by rfl⟩ (by norm_num))
theorem R60945 : Reach 60945 := rs (se 2 (by rfl) ⟨22854, by rfl⟩) (B 45709 (by norm_num) ⟨22854, by rfl⟩ (by norm_num))
theorem R60949 : Reach 60949 := rs (se 6 (by rfl) ⟨1428, by rfl⟩) (B 2857 (by norm_num) ⟨1428, by rfl⟩ (by norm_num))
theorem R60953 : Reach 60953 := rs (se 2 (by rfl) ⟨22857, by rfl⟩) (B 45715 (by norm_num) ⟨22857, by rfl⟩ (by norm_num))
theorem R60957 : Reach 60957 := rs (se 3 (by rfl) ⟨11429, by rfl⟩) (B 22859 (by norm_num) ⟨11429, by rfl⟩ (by norm_num))
theorem R93725 : Reach 93725 := rs (se 3 (by rfl) ⟨17573, by rfl⟩) (B 35147 (by norm_num) ⟨17573, by rfl⟩ (by norm_num))
theorem R60961 : Reach 60961 := rs (se 2 (by rfl) ⟨22860, by rfl⟩) (B 45721 (by norm_num) ⟨22860, by rfl⟩ (by norm_num))
theorem R60965 : Reach 60965 := rs (se 4 (by rfl) ⟨5715, by rfl⟩) (B 11431 (by norm_num) ⟨5715, by rfl⟩ (by norm_num))
theorem R60969 : Reach 60969 := rs (se 2 (by rfl) ⟨22863, by rfl⟩) (B 45727 (by norm_num) ⟨22863, by rfl⟩ (by norm_num))
theorem R60973 : Reach 60973 := rs (se 3 (by rfl) ⟨11432, by rfl⟩) (B 22865 (by norm_num) ⟨11432, by rfl⟩ (by norm_num))
theorem R60977 : Reach 60977 := rs (se 2 (by rfl) ⟨22866, by rfl⟩) (B 45733 (by norm_num) ⟨22866, by rfl⟩ (by norm_num))
theorem R60981 : Reach 60981 := rs (se 5 (by rfl) ⟨2858, by rfl⟩) (B 5717 (by norm_num) ⟨2858, by rfl⟩ (by norm_num))
theorem R93749 : Reach 93749 := rs (se 5 (by rfl) ⟨4394, by rfl⟩) (B 8789 (by norm_num) ⟨4394, by rfl⟩ (by norm_num))
theorem R60985 : Reach 60985 := rs (se 2 (by rfl) ⟨22869, by rfl⟩) (B 45739 (by norm_num) ⟨22869, by rfl⟩ (by norm_num))
theorem R60989 : Reach 60989 := rs (se 3 (by rfl) ⟨11435, by rfl⟩) (B 22871 (by norm_num) ⟨11435, by rfl⟩ (by norm_num))
theorem R60993 : Reach 60993 := rs (se 2 (by rfl) ⟨22872, by rfl⟩) (B 45745 (by norm_num) ⟨22872, by rfl⟩ (by norm_num))
theorem R60997 : Reach 60997 := rs (se 4 (by rfl) ⟨5718, by rfl⟩) (B 11437 (by norm_num) ⟨5718, by rfl⟩ (by norm_num))
theorem R61001 : Reach 61001 := rs (se 2 (by rfl) ⟨22875, by rfl⟩) (B 45751 (by norm_num) ⟨22875, by rfl⟩ (by norm_num))
theorem R61005 : Reach 61005 := rs (se 3 (by rfl) ⟨11438, by rfl⟩) (B 22877 (by norm_num) ⟨11438, by rfl⟩ (by norm_num))
theorem R93773 : Reach 93773 := rs (se 3 (by rfl) ⟨17582, by rfl⟩) (B 35165 (by norm_num) ⟨17582, by rfl⟩ (by norm_num))
theorem R61009 : Reach 61009 := rs (se 2 (by rfl) ⟨22878, by rfl⟩) (B 45757 (by norm_num) ⟨22878, by rfl⟩ (by norm_num))
theorem R61013 : Reach 61013 := rs (se 8 (by rfl) ⟨357, by rfl⟩) (B 715 (by norm_num) ⟨357, by rfl⟩ (by norm_num))
theorem R159317 : Reach 159317 := rs (se 8 (by rfl) ⟨933, by rfl⟩) (B 1867 (by norm_num) ⟨933, by rfl⟩ (by norm_num))
theorem R61017 : Reach 61017 := rs (se 2 (by rfl) ⟨22881, by rfl⟩) (B 45763 (by norm_num) ⟨22881, by rfl⟩ (by norm_num))
theorem R61021 : Reach 61021 := rs (se 3 (by rfl) ⟨11441, by rfl⟩) (B 22883 (by norm_num) ⟨11441, by rfl⟩ (by norm_num))
theorem R61025 : Reach 61025 := rs (se 2 (by rfl) ⟨22884, by rfl⟩) (B 45769 (by norm_num) ⟨22884, by rfl⟩ (by norm_num))
theorem R61029 : Reach 61029 := rs (se 4 (by rfl) ⟨5721, by rfl⟩) (B 11443 (by norm_num) ⟨5721, by rfl⟩ (by norm_num))
theorem R224869 : Reach 224869 := rs (se 4 (by rfl) ⟨21081, by rfl⟩) (B 42163 (by norm_num) ⟨21081, by rfl⟩ (by norm_num))
theorem R93797 : Reach 93797 := rs (se 4 (by rfl) ⟨8793, by rfl⟩) (B 17587 (by norm_num) ⟨8793, by rfl⟩ (by norm_num))
theorem R61033 : Reach 61033 := rs (se 2 (by rfl) ⟨22887, by rfl⟩) (B 45775 (by norm_num) ⟨22887, by rfl⟩ (by norm_num))
theorem R61037 : Reach 61037 := rs (se 3 (by rfl) ⟨11444, by rfl⟩) (B 22889 (by norm_num) ⟨11444, by rfl⟩ (by norm_num))
theorem R61041 : Reach 61041 := rs (se 2 (by rfl) ⟨22890, by rfl⟩) (B 45781 (by norm_num) ⟨22890, by rfl⟩ (by norm_num))
theorem R61045 : Reach 61045 := rs (se 5 (by rfl) ⟨2861, by rfl⟩) (B 5723 (by norm_num) ⟨2861, by rfl⟩ (by norm_num))
theorem R61049 : Reach 61049 := rs (se 2 (by rfl) ⟨22893, by rfl⟩) (B 45787 (by norm_num) ⟨22893, by rfl⟩ (by norm_num))
theorem R61053 : Reach 61053 := rs (se 3 (by rfl) ⟨11447, by rfl⟩) (B 22895 (by norm_num) ⟨11447, by rfl⟩ (by norm_num))
theorem R93821 : Reach 93821 := rs (se 3 (by rfl) ⟨17591, by rfl⟩) (B 35183 (by norm_num) ⟨17591, by rfl⟩ (by norm_num))
theorem R61057 : Reach 61057 := rs (se 2 (by rfl) ⟨22896, by rfl⟩) (B 45793 (by norm_num) ⟨22896, by rfl⟩ (by norm_num))
theorem R61061 : Reach 61061 := rs (se 4 (by rfl) ⟨5724, by rfl⟩) (B 11449 (by norm_num) ⟨5724, by rfl⟩ (by norm_num))
theorem R61065 : Reach 61065 := rs (se 2 (by rfl) ⟨22899, by rfl⟩) (B 45799 (by norm_num) ⟨22899, by rfl⟩ (by norm_num))
theorem R61069 : Reach 61069 := rs (se 3 (by rfl) ⟨11450, by rfl⟩) (B 22901 (by norm_num) ⟨11450, by rfl⟩ (by norm_num))
theorem R61073 : Reach 61073 := rs (se 2 (by rfl) ⟨22902, by rfl⟩) (B 45805 (by norm_num) ⟨22902, by rfl⟩ (by norm_num))
theorem R61077 : Reach 61077 := rs (se 6 (by rfl) ⟨1431, by rfl⟩) (B 2863 (by norm_num) ⟨1431, by rfl⟩ (by norm_num))
theorem R192149 : Reach 192149 := rs (se 6 (by rfl) ⟨4503, by rfl⟩) (B 9007 (by norm_num) ⟨4503, by rfl⟩ (by norm_num))
theorem R93845 : Reach 93845 := rs (se 6 (by rfl) ⟨2199, by rfl⟩) (B 4399 (by norm_num) ⟨2199, by rfl⟩ (by norm_num))
theorem R61081 : Reach 61081 := rs (se 2 (by rfl) ⟨22905, by rfl⟩) (B 45811 (by norm_num) ⟨22905, by rfl⟩ (by norm_num))
theorem R61085 : Reach 61085 := rs (se 3 (by rfl) ⟨11453, by rfl⟩) (B 22907 (by norm_num) ⟨11453, by rfl⟩ (by norm_num))
theorem R61089 : Reach 61089 := rs (se 2 (by rfl) ⟨22908, by rfl⟩) (B 45817 (by norm_num) ⟨22908, by rfl⟩ (by norm_num))
theorem R61093 : Reach 61093 := rs (se 4 (by rfl) ⟨5727, by rfl⟩) (B 11455 (by norm_num) ⟨5727, by rfl⟩ (by norm_num))
theorem R61097 : Reach 61097 := rs (se 2 (by rfl) ⟨22911, by rfl⟩) (B 45823 (by norm_num) ⟨22911, by rfl⟩ (by norm_num))
theorem R61101 : Reach 61101 := rs (se 3 (by rfl) ⟨11456, by rfl⟩) (B 22913 (by norm_num) ⟨11456, by rfl⟩ (by norm_num))
theorem R93869 : Reach 93869 := rs (se 3 (by rfl) ⟨17600, by rfl⟩) (B 35201 (by norm_num) ⟨17600, by rfl⟩ (by norm_num))
theorem R61105 : Reach 61105 := rs (se 2 (by rfl) ⟨22914, by rfl⟩) (B 45829 (by norm_num) ⟨22914, by rfl⟩ (by norm_num))
theorem R61109 : Reach 61109 := rs (se 5 (by rfl) ⟨2864, by rfl⟩) (B 5729 (by norm_num) ⟨2864, by rfl⟩ (by norm_num))
theorem R61113 : Reach 61113 := rs (se 2 (by rfl) ⟨22917, by rfl⟩) (B 45835 (by norm_num) ⟨22917, by rfl⟩ (by norm_num))
theorem R61117 : Reach 61117 := rs (se 3 (by rfl) ⟨11459, by rfl⟩) (B 22919 (by norm_num) ⟨11459, by rfl⟩ (by norm_num))
theorem R61121 : Reach 61121 := rs (se 2 (by rfl) ⟨22920, by rfl⟩) (B 45841 (by norm_num) ⟨22920, by rfl⟩ (by norm_num))
theorem R61125 : Reach 61125 := rs (se 4 (by rfl) ⟨5730, by rfl⟩) (B 11461 (by norm_num) ⟨5730, by rfl⟩ (by norm_num))
theorem R93893 : Reach 93893 := rs (se 4 (by rfl) ⟨8802, by rfl⟩) (B 17605 (by norm_num) ⟨8802, by rfl⟩ (by norm_num))
theorem R61129 : Reach 61129 := rs (se 2 (by rfl) ⟨22923, by rfl⟩) (B 45847 (by norm_num) ⟨22923, by rfl⟩ (by norm_num))
theorem R61133 : Reach 61133 := rs (se 3 (by rfl) ⟨11462, by rfl⟩) (B 22925 (by norm_num) ⟨11462, by rfl⟩ (by norm_num))
theorem R61137 : Reach 61137 := rs (se 2 (by rfl) ⟨22926, by rfl⟩) (B 45853 (by norm_num) ⟨22926, by rfl⟩ (by norm_num))
theorem R61141 : Reach 61141 := rs (se 7 (by rfl) ⟨716, by rfl⟩) (B 1433 (by norm_num) ⟨716, by rfl⟩ (by norm_num))
theorem R61145 : Reach 61145 := rs (se 2 (by rfl) ⟨22929, by rfl⟩) (B 45859 (by norm_num) ⟨22929, by rfl⟩ (by norm_num))
theorem R61149 : Reach 61149 := rs (se 3 (by rfl) ⟨11465, by rfl⟩) (B 22931 (by norm_num) ⟨11465, by rfl⟩ (by norm_num))
theorem R93917 : Reach 93917 := rs (se 3 (by rfl) ⟨17609, by rfl⟩) (B 35219 (by norm_num) ⟨17609, by rfl⟩ (by norm_num))
theorem R61153 : Reach 61153 := rs (se 2 (by rfl) ⟨22932, by rfl⟩) (B 45865 (by norm_num) ⟨22932, by rfl⟩ (by norm_num))
theorem R61157 : Reach 61157 := rs (se 4 (by rfl) ⟨5733, by rfl⟩) (B 11467 (by norm_num) ⟨5733, by rfl⟩ (by norm_num))
theorem R61161 : Reach 61161 := rs (se 2 (by rfl) ⟨22935, by rfl⟩) (B 45871 (by norm_num) ⟨22935, by rfl⟩ (by norm_num))
theorem R61165 : Reach 61165 := rs (se 3 (by rfl) ⟨11468, by rfl⟩) (B 22937 (by norm_num) ⟨11468, by rfl⟩ (by norm_num))
theorem R61169 : Reach 61169 := rs (se 2 (by rfl) ⟨22938, by rfl⟩) (B 45877 (by norm_num) ⟨22938, by rfl⟩ (by norm_num))
theorem R61173 : Reach 61173 := rs (se 5 (by rfl) ⟨2867, by rfl⟩) (B 5735 (by norm_num) ⟨2867, by rfl⟩ (by norm_num))
theorem R93941 : Reach 93941 := rs (se 5 (by rfl) ⟨4403, by rfl⟩) (B 8807 (by norm_num) ⟨4403, by rfl⟩ (by norm_num))
theorem R61177 : Reach 61177 := rs (se 2 (by rfl) ⟨22941, by rfl⟩) (B 45883 (by norm_num) ⟨22941, by rfl⟩ (by norm_num))
theorem R61181 : Reach 61181 := rs (se 3 (by rfl) ⟨11471, by rfl⟩) (B 22943 (by norm_num) ⟨11471, by rfl⟩ (by norm_num))
theorem R61185 : Reach 61185 := rs (se 2 (by rfl) ⟨22944, by rfl⟩) (B 45889 (by norm_num) ⟨22944, by rfl⟩ (by norm_num))
theorem R61189 : Reach 61189 := rs (se 4 (by rfl) ⟨5736, by rfl⟩) (B 11473 (by norm_num) ⟨5736, by rfl⟩ (by norm_num))
theorem R61193 : Reach 61193 := rs (se 2 (by rfl) ⟨22947, by rfl⟩) (B 45895 (by norm_num) ⟨22947, by rfl⟩ (by norm_num))
theorem R61197 : Reach 61197 := rs (se 3 (by rfl) ⟨11474, by rfl⟩) (B 22949 (by norm_num) ⟨11474, by rfl⟩ (by norm_num))
theorem R93965 : Reach 93965 := rs (se 3 (by rfl) ⟨17618, by rfl⟩) (B 35237 (by norm_num) ⟨17618, by rfl⟩ (by norm_num))
theorem R61201 : Reach 61201 := rs (se 2 (by rfl) ⟨22950, by rfl⟩) (B 45901 (by norm_num) ⟨22950, by rfl⟩ (by norm_num))
theorem R61205 : Reach 61205 := rs (se 6 (by rfl) ⟨1434, by rfl⟩) (B 2869 (by norm_num) ⟨1434, by rfl⟩ (by norm_num))
theorem R159509 : Reach 159509 := rs (se 6 (by rfl) ⟨3738, by rfl⟩) (B 7477 (by norm_num) ⟨3738, by rfl⟩ (by norm_num))
theorem R61209 : Reach 61209 := rs (se 2 (by rfl) ⟨22953, by rfl⟩) (B 45907 (by norm_num) ⟨22953, by rfl⟩ (by norm_num))
theorem R61213 : Reach 61213 := rs (se 3 (by rfl) ⟨11477, by rfl⟩) (B 22955 (by norm_num) ⟨11477, by rfl⟩ (by norm_num))
theorem R61217 : Reach 61217 := rs (se 2 (by rfl) ⟨22956, by rfl⟩) (B 45913 (by norm_num) ⟨22956, by rfl⟩ (by norm_num))
theorem R61221 : Reach 61221 := rs (se 4 (by rfl) ⟨5739, by rfl⟩) (B 11479 (by norm_num) ⟨5739, by rfl⟩ (by norm_num))
theorem R93989 : Reach 93989 := rs (se 4 (by rfl) ⟨8811, by rfl⟩) (B 17623 (by norm_num) ⟨8811, by rfl⟩ (by norm_num))
theorem R61225 : Reach 61225 := rs (se 2 (by rfl) ⟨22959, by rfl⟩) (B 45919 (by norm_num) ⟨22959, by rfl⟩ (by norm_num))
theorem R61229 : Reach 61229 := rs (se 3 (by rfl) ⟨11480, by rfl⟩) (B 22961 (by norm_num) ⟨11480, by rfl⟩ (by norm_num))
theorem R61233 : Reach 61233 := rs (se 2 (by rfl) ⟨22962, by rfl⟩) (B 45925 (by norm_num) ⟨22962, by rfl⟩ (by norm_num))
theorem R61237 : Reach 61237 := rs (se 5 (by rfl) ⟨2870, by rfl⟩) (B 5741 (by norm_num) ⟨2870, by rfl⟩ (by norm_num))
theorem R61241 : Reach 61241 := rs (se 2 (by rfl) ⟨22965, by rfl⟩) (B 45931 (by norm_num) ⟨22965, by rfl⟩ (by norm_num))
theorem R61245 : Reach 61245 := rs (se 3 (by rfl) ⟨11483, by rfl⟩) (B 22967 (by norm_num) ⟨11483, by rfl⟩ (by norm_num))
theorem R94013 : Reach 94013 := rs (se 3 (by rfl) ⟨17627, by rfl⟩) (B 35255 (by norm_num) ⟨17627, by rfl⟩ (by norm_num))
theorem R61249 : Reach 61249 := rs (se 2 (by rfl) ⟨22968, by rfl⟩) (B 45937 (by norm_num) ⟨22968, by rfl⟩ (by norm_num))
theorem R61253 : Reach 61253 := rs (se 4 (by rfl) ⟨5742, by rfl⟩) (B 11485 (by norm_num) ⟨5742, by rfl⟩ (by norm_num))
theorem R61257 : Reach 61257 := rs (se 2 (by rfl) ⟨22971, by rfl⟩) (B 45943 (by norm_num) ⟨22971, by rfl⟩ (by norm_num))
theorem R61261 : Reach 61261 := rs (se 3 (by rfl) ⟨11486, by rfl⟩) (B 22973 (by norm_num) ⟨11486, by rfl⟩ (by norm_num))
theorem R61265 : Reach 61265 := rs (se 2 (by rfl) ⟨22974, by rfl⟩) (B 45949 (by norm_num) ⟨22974, by rfl⟩ (by norm_num))
theorem R61269 : Reach 61269 := rs (se 9 (by rfl) ⟨179, by rfl⟩) (B 359 (by norm_num) ⟨179, by rfl⟩ (by norm_num))
theorem R94037 : Reach 94037 := rs (se 9 (by rfl) ⟨275, by rfl⟩) (B 551 (by norm_num) ⟨275, by rfl⟩ (by norm_num))
theorem R61273 : Reach 61273 := rs (se 2 (by rfl) ⟨22977, by rfl⟩) (B 45955 (by norm_num) ⟨22977, by rfl⟩ (by norm_num))
theorem R61277 : Reach 61277 := rs (se 3 (by rfl) ⟨11489, by rfl⟩) (B 22979 (by norm_num) ⟨11489, by rfl⟩ (by norm_num))
theorem R61281 : Reach 61281 := rs (se 2 (by rfl) ⟨22980, by rfl⟩) (B 45961 (by norm_num) ⟨22980, by rfl⟩ (by norm_num))
theorem R225125 : Reach 225125 := rs (se 4 (by rfl) ⟨21105, by rfl⟩) (B 42211 (by norm_num) ⟨21105, by rfl⟩ (by norm_num))
theorem R61285 : Reach 61285 := rs (se 4 (by rfl) ⟨5745, by rfl⟩) (B 11491 (by norm_num) ⟨5745, by rfl⟩ (by norm_num))
theorem R126821 : Reach 126821 := rs (se 4 (by rfl) ⟨11889, by rfl⟩) (B 23779 (by norm_num) ⟨11889, by rfl⟩ (by norm_num))
theorem R61289 : Reach 61289 := rs (se 2 (by rfl) ⟨22983, by rfl⟩) (B 45967 (by norm_num) ⟨22983, by rfl⟩ (by norm_num))
theorem R61293 : Reach 61293 := rs (se 3 (by rfl) ⟨11492, by rfl⟩) (B 22985 (by norm_num) ⟨11492, by rfl⟩ (by norm_num))
theorem R94061 : Reach 94061 := rs (se 3 (by rfl) ⟨17636, by rfl⟩) (B 35273 (by norm_num) ⟨17636, by rfl⟩ (by norm_num))
theorem R61297 : Reach 61297 := rs (se 2 (by rfl) ⟨22986, by rfl⟩) (B 45973 (by norm_num) ⟨22986, by rfl⟩ (by norm_num))
theorem R61301 : Reach 61301 := rs (se 5 (by rfl) ⟨2873, by rfl⟩) (B 5747 (by norm_num) ⟨2873, by rfl⟩ (by norm_num))
theorem R61305 : Reach 61305 := rs (se 2 (by rfl) ⟨22989, by rfl⟩) (B 45979 (by norm_num) ⟨22989, by rfl⟩ (by norm_num))
theorem R61309 : Reach 61309 := rs (se 3 (by rfl) ⟨11495, by rfl⟩) (B 22991 (by norm_num) ⟨11495, by rfl⟩ (by norm_num))
theorem R61313 : Reach 61313 := rs (se 2 (by rfl) ⟨22992, by rfl⟩) (B 45985 (by norm_num) ⟨22992, by rfl⟩ (by norm_num))
theorem R61317 : Reach 61317 := rs (se 4 (by rfl) ⟨5748, by rfl⟩) (B 11497 (by norm_num) ⟨5748, by rfl⟩ (by norm_num))
theorem R94085 : Reach 94085 := rs (se 4 (by rfl) ⟨8820, by rfl⟩) (B 17641 (by norm_num) ⟨8820, by rfl⟩ (by norm_num))
theorem R61321 : Reach 61321 := rs (se 2 (by rfl) ⟨22995, by rfl⟩) (B 45991 (by norm_num) ⟨22995, by rfl⟩ (by norm_num))
theorem R61325 : Reach 61325 := rs (se 3 (by rfl) ⟨11498, by rfl⟩) (B 22997 (by norm_num) ⟨11498, by rfl⟩ (by norm_num))
theorem R61329 : Reach 61329 := rs (se 2 (by rfl) ⟨22998, by rfl⟩) (B 45997 (by norm_num) ⟨22998, by rfl⟩ (by norm_num))
theorem R61333 : Reach 61333 := rs (se 6 (by rfl) ⟨1437, by rfl⟩) (B 2875 (by norm_num) ⟨1437, by rfl⟩ (by norm_num))
theorem R61337 : Reach 61337 := rs (se 2 (by rfl) ⟨23001, by rfl⟩) (B 46003 (by norm_num) ⟨23001, by rfl⟩ (by norm_num))
theorem R61341 : Reach 61341 := rs (se 3 (by rfl) ⟨11501, by rfl⟩) (B 23003 (by norm_num) ⟨11501, by rfl⟩ (by norm_num))
theorem R94109 : Reach 94109 := rs (se 3 (by rfl) ⟨17645, by rfl⟩) (B 35291 (by norm_num) ⟨17645, by rfl⟩ (by norm_num))
theorem R61345 : Reach 61345 := rs (se 2 (by rfl) ⟨23004, by rfl⟩) (B 46009 (by norm_num) ⟨23004, by rfl⟩ (by norm_num))
theorem R61349 : Reach 61349 := rs (se 4 (by rfl) ⟨5751, by rfl⟩) (B 11503 (by norm_num) ⟨5751, by rfl⟩ (by norm_num))
theorem R61353 : Reach 61353 := rs (se 2 (by rfl) ⟨23007, by rfl⟩) (B 46015 (by norm_num) ⟨23007, by rfl⟩ (by norm_num))
theorem R61357 : Reach 61357 := rs (se 3 (by rfl) ⟨11504, by rfl⟩) (B 23009 (by norm_num) ⟨11504, by rfl⟩ (by norm_num))
theorem R126893 : Reach 126893 := rs (se 3 (by rfl) ⟨23792, by rfl⟩) (B 47585 (by norm_num) ⟨23792, by rfl⟩ (by norm_num))
theorem R61361 : Reach 61361 := rs (se 2 (by rfl) ⟨23010, by rfl⟩) (B 46021 (by norm_num) ⟨23010, by rfl⟩ (by norm_num))
theorem R61365 : Reach 61365 := rs (se 5 (by rfl) ⟨2876, by rfl⟩) (B 5753 (by norm_num) ⟨2876, by rfl⟩ (by norm_num))
theorem R94133 : Reach 94133 := rs (se 5 (by rfl) ⟨4412, by rfl⟩) (B 8825 (by norm_num) ⟨4412, by rfl⟩ (by norm_num))
theorem R61369 : Reach 61369 := rs (se 2 (by rfl) ⟨23013, by rfl⟩) (B 46027 (by norm_num) ⟨23013, by rfl⟩ (by norm_num))
theorem R61373 : Reach 61373 := rs (se 3 (by rfl) ⟨11507, by rfl⟩) (B 23015 (by norm_num) ⟨11507, by rfl⟩ (by norm_num))
theorem R61377 : Reach 61377 := rs (se 2 (by rfl) ⟨23016, by rfl⟩) (B 46033 (by norm_num) ⟨23016, by rfl⟩ (by norm_num))
theorem R61381 : Reach 61381 := rs (se 4 (by rfl) ⟨5754, by rfl⟩) (B 11509 (by norm_num) ⟨5754, by rfl⟩ (by norm_num))
theorem R61385 : Reach 61385 := rs (se 2 (by rfl) ⟨23019, by rfl⟩) (B 46039 (by norm_num) ⟨23019, by rfl⟩ (by norm_num))
theorem R61389 : Reach 61389 := rs (se 3 (by rfl) ⟨11510, by rfl⟩) (B 23021 (by norm_num) ⟨11510, by rfl⟩ (by norm_num))
theorem R94157 : Reach 94157 := rs (se 3 (by rfl) ⟨17654, by rfl⟩) (B 35309 (by norm_num) ⟨17654, by rfl⟩ (by norm_num))
theorem R61393 : Reach 61393 := rs (se 2 (by rfl) ⟨23022, by rfl⟩) (B 46045 (by norm_num) ⟨23022, by rfl⟩ (by norm_num))
theorem R61397 : Reach 61397 := rs (se 7 (by rfl) ⟨719, by rfl⟩) (B 1439 (by norm_num) ⟨719, by rfl⟩ (by norm_num))
theorem R61401 : Reach 61401 := rs (se 2 (by rfl) ⟨23025, by rfl⟩) (B 46051 (by norm_num) ⟨23025, by rfl⟩ (by norm_num))
theorem R61405 : Reach 61405 := rs (se 3 (by rfl) ⟨11513, by rfl⟩) (B 23027 (by norm_num) ⟨11513, by rfl⟩ (by norm_num))
theorem R61409 : Reach 61409 := rs (se 2 (by rfl) ⟨23028, by rfl⟩) (B 46057 (by norm_num) ⟨23028, by rfl⟩ (by norm_num))
theorem R126949 : Reach 126949 := rs (se 4 (by rfl) ⟨11901, by rfl⟩) (B 23803 (by norm_num) ⟨11901, by rfl⟩ (by norm_num))
theorem R61413 : Reach 61413 := rs (se 4 (by rfl) ⟨5757, by rfl⟩) (B 11515 (by norm_num) ⟨5757, by rfl⟩ (by norm_num))
theorem R94181 : Reach 94181 := rs (se 4 (by rfl) ⟨8829, by rfl⟩) (B 17659 (by norm_num) ⟨8829, by rfl⟩ (by norm_num))
theorem R61417 : Reach 61417 := rs (se 2 (by rfl) ⟨23031, by rfl⟩) (B 46063 (by norm_num) ⟨23031, by rfl⟩ (by norm_num))
theorem R61421 : Reach 61421 := rs (se 3 (by rfl) ⟨11516, by rfl⟩) (B 23033 (by norm_num) ⟨11516, by rfl⟩ (by norm_num))
theorem R61425 : Reach 61425 := rs (se 2 (by rfl) ⟨23034, by rfl⟩) (B 46069 (by norm_num) ⟨23034, by rfl⟩ (by norm_num))
theorem R61429 : Reach 61429 := rs (se 5 (by rfl) ⟨2879, by rfl⟩) (B 5759 (by norm_num) ⟨2879, by rfl⟩ (by norm_num))
theorem R61433 : Reach 61433 := rs (se 2 (by rfl) ⟨23037, by rfl⟩) (B 46075 (by norm_num) ⟨23037, by rfl⟩ (by norm_num))
theorem R61437 : Reach 61437 := rs (se 3 (by rfl) ⟨11519, by rfl⟩) (B 23039 (by norm_num) ⟨11519, by rfl⟩ (by norm_num))
theorem R94205 : Reach 94205 := rs (se 3 (by rfl) ⟨17663, by rfl⟩) (B 35327 (by norm_num) ⟨17663, by rfl⟩ (by norm_num))
theorem R61441 : Reach 61441 := rs (se 2 (by rfl) ⟨23040, by rfl⟩) (B 46081 (by norm_num) ⟨23040, by rfl⟩ (by norm_num))
theorem R61445 : Reach 61445 := rs (se 4 (by rfl) ⟨5760, by rfl⟩) (B 11521 (by norm_num) ⟨5760, by rfl⟩ (by norm_num))
theorem R61449 : Reach 61449 := rs (se 2 (by rfl) ⟨23043, by rfl⟩) (B 46087 (by norm_num) ⟨23043, by rfl⟩ (by norm_num))
theorem R61453 : Reach 61453 := rs (se 3 (by rfl) ⟨11522, by rfl⟩) (B 23045 (by norm_num) ⟨11522, by rfl⟩ (by norm_num))
theorem R61457 : Reach 61457 := rs (se 2 (by rfl) ⟨23046, by rfl⟩) (B 46093 (by norm_num) ⟨23046, by rfl⟩ (by norm_num))
theorem R61461 : Reach 61461 := rs (se 6 (by rfl) ⟨1440, by rfl⟩) (B 2881 (by norm_num) ⟨1440, by rfl⟩ (by norm_num))
theorem R94229 : Reach 94229 := rs (se 6 (by rfl) ⟨2208, by rfl⟩) (B 4417 (by norm_num) ⟨2208, by rfl⟩ (by norm_num))
theorem R61465 : Reach 61465 := rs (se 2 (by rfl) ⟨23049, by rfl⟩) (B 46099 (by norm_num) ⟨23049, by rfl⟩ (by norm_num))
theorem R61469 : Reach 61469 := rs (se 3 (by rfl) ⟨11525, by rfl⟩) (B 23051 (by norm_num) ⟨11525, by rfl⟩ (by norm_num))
theorem R61473 : Reach 61473 := rs (se 2 (by rfl) ⟨23052, by rfl⟩) (B 46105 (by norm_num) ⟨23052, by rfl⟩ (by norm_num))
theorem R61477 : Reach 61477 := rs (se 4 (by rfl) ⟨5763, by rfl⟩) (B 11527 (by norm_num) ⟨5763, by rfl⟩ (by norm_num))
theorem R61481 : Reach 61481 := rs (se 2 (by rfl) ⟨23055, by rfl⟩) (B 46111 (by norm_num) ⟨23055, by rfl⟩ (by norm_num))
theorem R61485 : Reach 61485 := rs (se 3 (by rfl) ⟨11528, by rfl⟩) (B 23057 (by norm_num) ⟨11528, by rfl⟩ (by norm_num))
theorem R94253 : Reach 94253 := rs (se 3 (by rfl) ⟨17672, by rfl⟩) (B 35345 (by norm_num) ⟨17672, by rfl⟩ (by norm_num))
theorem R61489 : Reach 61489 := rs (se 2 (by rfl) ⟨23058, by rfl⟩) (B 46117 (by norm_num) ⟨23058, by rfl⟩ (by norm_num))
theorem R61493 : Reach 61493 := rs (se 5 (by rfl) ⟨2882, by rfl⟩) (B 5765 (by norm_num) ⟨2882, by rfl⟩ (by norm_num))
theorem R61497 : Reach 61497 := rs (se 2 (by rfl) ⟨23061, by rfl⟩) (B 46123 (by norm_num) ⟨23061, by rfl⟩ (by norm_num))
theorem R61501 : Reach 61501 := rs (se 3 (by rfl) ⟨11531, by rfl⟩) (B 23063 (by norm_num) ⟨11531, by rfl⟩ (by norm_num))
theorem R61505 : Reach 61505 := rs (se 2 (by rfl) ⟨23064, by rfl⟩) (B 46129 (by norm_num) ⟨23064, by rfl⟩ (by norm_num))
theorem R61509 : Reach 61509 := rs (se 4 (by rfl) ⟨5766, by rfl⟩) (B 11533 (by norm_num) ⟨5766, by rfl⟩ (by norm_num))
theorem R94277 : Reach 94277 := rs (se 4 (by rfl) ⟨8838, by rfl⟩) (B 17677 (by norm_num) ⟨8838, by rfl⟩ (by norm_num))
theorem R61513 : Reach 61513 := rs (se 2 (by rfl) ⟨23067, by rfl⟩) (B 46135 (by norm_num) ⟨23067, by rfl⟩ (by norm_num))
theorem R61517 : Reach 61517 := rs (se 3 (by rfl) ⟨11534, by rfl⟩) (B 23069 (by norm_num) ⟨11534, by rfl⟩ (by norm_num))
theorem R61521 : Reach 61521 := rs (se 2 (by rfl) ⟨23070, by rfl⟩) (B 46141 (by norm_num) ⟨23070, by rfl⟩ (by norm_num))
theorem R61525 : Reach 61525 := rs (se 8 (by rfl) ⟨360, by rfl⟩) (B 721 (by norm_num) ⟨360, by rfl⟩ (by norm_num))
theorem R61529 : Reach 61529 := rs (se 2 (by rfl) ⟨23073, by rfl⟩) (B 46147 (by norm_num) ⟨23073, by rfl⟩ (by norm_num))
theorem R61533 : Reach 61533 := rs (se 3 (by rfl) ⟨11537, by rfl⟩) (B 23075 (by norm_num) ⟨11537, by rfl⟩ (by norm_num))
theorem R94301 : Reach 94301 := rs (se 3 (by rfl) ⟨17681, by rfl⟩) (B 35363 (by norm_num) ⟨17681, by rfl⟩ (by norm_num))
theorem R61537 : Reach 61537 := rs (se 2 (by rfl) ⟨23076, by rfl⟩) (B 46153 (by norm_num) ⟨23076, by rfl⟩ (by norm_num))
theorem R61541 : Reach 61541 := rs (se 4 (by rfl) ⟨5769, by rfl⟩) (B 11539 (by norm_num) ⟨5769, by rfl⟩ (by norm_num))
theorem R61545 : Reach 61545 := rs (se 2 (by rfl) ⟨23079, by rfl⟩) (B 46159 (by norm_num) ⟨23079, by rfl⟩ (by norm_num))
theorem R61549 : Reach 61549 := rs (se 3 (by rfl) ⟨11540, by rfl⟩) (B 23081 (by norm_num) ⟨11540, by rfl⟩ (by norm_num))
theorem R61553 : Reach 61553 := rs (se 2 (by rfl) ⟨23082, by rfl⟩) (B 46165 (by norm_num) ⟨23082, by rfl⟩ (by norm_num))
theorem R61557 : Reach 61557 := rs (se 5 (by rfl) ⟨2885, by rfl⟩) (B 5771 (by norm_num) ⟨2885, by rfl⟩ (by norm_num))
theorem R94325 : Reach 94325 := rs (se 5 (by rfl) ⟨4421, by rfl⟩) (B 8843 (by norm_num) ⟨4421, by rfl⟩ (by norm_num))
theorem R61561 : Reach 61561 := rs (se 2 (by rfl) ⟨23085, by rfl⟩) (B 46171 (by norm_num) ⟨23085, by rfl⟩ (by norm_num))
theorem R61565 : Reach 61565 := rs (se 3 (by rfl) ⟨11543, by rfl⟩) (B 23087 (by norm_num) ⟨11543, by rfl⟩ (by norm_num))
theorem R61569 : Reach 61569 := rs (se 2 (by rfl) ⟨23088, by rfl⟩) (B 46177 (by norm_num) ⟨23088, by rfl⟩ (by norm_num))
theorem R225413 : Reach 225413 := rs (se 4 (by rfl) ⟨21132, by rfl⟩) (B 42265 (by norm_num) ⟨21132, by rfl⟩ (by norm_num))
theorem R61573 : Reach 61573 := rs (se 4 (by rfl) ⟨5772, by rfl⟩) (B 11545 (by norm_num) ⟨5772, by rfl⟩ (by norm_num))
theorem R61577 : Reach 61577 := rs (se 2 (by rfl) ⟨23091, by rfl⟩) (B 46183 (by norm_num) ⟨23091, by rfl⟩ (by norm_num))
theorem R61581 : Reach 61581 := rs (se 3 (by rfl) ⟨11546, by rfl⟩) (B 23093 (by norm_num) ⟨11546, by rfl⟩ (by norm_num))
theorem R94349 : Reach 94349 := rs (se 3 (by rfl) ⟨17690, by rfl⟩) (B 35381 (by norm_num) ⟨17690, by rfl⟩ (by norm_num))
theorem R61585 : Reach 61585 := rs (se 2 (by rfl) ⟨23094, by rfl⟩) (B 46189 (by norm_num) ⟨23094, by rfl⟩ (by norm_num))
theorem R61589 : Reach 61589 := rs (se 6 (by rfl) ⟨1443, by rfl⟩) (B 2887 (by norm_num) ⟨1443, by rfl⟩ (by norm_num))
theorem R61593 : Reach 61593 := rs (se 2 (by rfl) ⟨23097, by rfl⟩) (B 46195 (by norm_num) ⟨23097, by rfl⟩ (by norm_num))
theorem R61597 : Reach 61597 := rs (se 3 (by rfl) ⟨11549, by rfl⟩) (B 23099 (by norm_num) ⟨11549, by rfl⟩ (by norm_num))
theorem R61601 : Reach 61601 := rs (se 2 (by rfl) ⟨23100, by rfl⟩) (B 46201 (by norm_num) ⟨23100, by rfl⟩ (by norm_num))
theorem R61605 : Reach 61605 := rs (se 4 (by rfl) ⟨5775, by rfl⟩) (B 11551 (by norm_num) ⟨5775, by rfl⟩ (by norm_num))
theorem R94373 : Reach 94373 := rs (se 4 (by rfl) ⟨8847, by rfl⟩) (B 17695 (by norm_num) ⟨8847, by rfl⟩ (by norm_num))
theorem R61609 : Reach 61609 := rs (se 2 (by rfl) ⟨23103, by rfl⟩) (B 46207 (by norm_num) ⟨23103, by rfl⟩ (by norm_num))
theorem R61613 : Reach 61613 := rs (se 3 (by rfl) ⟨11552, by rfl⟩) (B 23105 (by norm_num) ⟨11552, by rfl⟩ (by norm_num))
theorem R61617 : Reach 61617 := rs (se 2 (by rfl) ⟨23106, by rfl⟩) (B 46213 (by norm_num) ⟨23106, by rfl⟩ (by norm_num))
theorem R61621 : Reach 61621 := rs (se 5 (by rfl) ⟨2888, by rfl⟩) (B 5777 (by norm_num) ⟨2888, by rfl⟩ (by norm_num))
theorem R61625 : Reach 61625 := rs (se 2 (by rfl) ⟨23109, by rfl⟩) (B 46219 (by norm_num) ⟨23109, by rfl⟩ (by norm_num))
theorem R61629 : Reach 61629 := rs (se 3 (by rfl) ⟨11555, by rfl⟩) (B 23111 (by norm_num) ⟨11555, by rfl⟩ (by norm_num))
theorem R94397 : Reach 94397 := rs (se 3 (by rfl) ⟨17699, by rfl⟩) (B 35399 (by norm_num) ⟨17699, by rfl⟩ (by norm_num))
theorem R61633 : Reach 61633 := rs (se 2 (by rfl) ⟨23112, by rfl⟩) (B 46225 (by norm_num) ⟨23112, by rfl⟩ (by norm_num))
theorem R61637 : Reach 61637 := rs (se 4 (by rfl) ⟨5778, by rfl⟩) (B 11557 (by norm_num) ⟨5778, by rfl⟩ (by norm_num))
theorem R61641 : Reach 61641 := rs (se 2 (by rfl) ⟨23115, by rfl⟩) (B 46231 (by norm_num) ⟨23115, by rfl⟩ (by norm_num))
theorem R61645 : Reach 61645 := rs (se 3 (by rfl) ⟨11558, by rfl⟩) (B 23117 (by norm_num) ⟨11558, by rfl⟩ (by norm_num))
theorem R61649 : Reach 61649 := rs (se 2 (by rfl) ⟨23118, by rfl⟩) (B 46237 (by norm_num) ⟨23118, by rfl⟩ (by norm_num))
theorem R61653 : Reach 61653 := rs (se 7 (by rfl) ⟨722, by rfl⟩) (B 1445 (by norm_num) ⟨722, by rfl⟩ (by norm_num))
theorem R192725 : Reach 192725 := rs (se 7 (by rfl) ⟨2258, by rfl⟩) (B 4517 (by norm_num) ⟨2258, by rfl⟩ (by norm_num))
theorem R94421 : Reach 94421 := rs (se 7 (by rfl) ⟨1106, by rfl⟩) (B 2213 (by norm_num) ⟨1106, by rfl⟩ (by norm_num))
theorem R61657 : Reach 61657 := rs (se 2 (by rfl) ⟨23121, by rfl⟩) (B 46243 (by norm_num) ⟨23121, by rfl⟩ (by norm_num))
theorem R61661 : Reach 61661 := rs (se 3 (by rfl) ⟨11561, by rfl⟩) (B 23123 (by norm_num) ⟨11561, by rfl⟩ (by norm_num))
theorem R61665 : Reach 61665 := rs (se 2 (by rfl) ⟨23124, by rfl⟩) (B 46249 (by norm_num) ⟨23124, by rfl⟩ (by norm_num))
theorem R61669 : Reach 61669 := rs (se 4 (by rfl) ⟨5781, by rfl⟩) (B 11563 (by norm_num) ⟨5781, by rfl⟩ (by norm_num))
theorem R61673 : Reach 61673 := rs (se 2 (by rfl) ⟨23127, by rfl⟩) (B 46255 (by norm_num) ⟨23127, by rfl⟩ (by norm_num))
theorem R61677 : Reach 61677 := rs (se 3 (by rfl) ⟨11564, by rfl⟩) (B 23129 (by norm_num) ⟨11564, by rfl⟩ (by norm_num))
theorem R94445 : Reach 94445 := rs (se 3 (by rfl) ⟨17708, by rfl⟩) (B 35417 (by norm_num) ⟨17708, by rfl⟩ (by norm_num))
theorem R61681 : Reach 61681 := rs (se 2 (by rfl) ⟨23130, by rfl⟩) (B 46261 (by norm_num) ⟨23130, by rfl⟩ (by norm_num))
theorem R61685 : Reach 61685 := rs (se 5 (by rfl) ⟨2891, by rfl⟩) (B 5783 (by norm_num) ⟨2891, by rfl⟩ (by norm_num))
theorem R61689 : Reach 61689 := rs (se 2 (by rfl) ⟨23133, by rfl⟩) (B 46267 (by norm_num) ⟨23133, by rfl⟩ (by norm_num))
theorem R61693 : Reach 61693 := rs (se 3 (by rfl) ⟨11567, by rfl⟩) (B 23135 (by norm_num) ⟨11567, by rfl⟩ (by norm_num))
theorem R61697 : Reach 61697 := rs (se 2 (by rfl) ⟨23136, by rfl⟩) (B 46273 (by norm_num) ⟨23136, by rfl⟩ (by norm_num))
theorem R291077 : Reach 291077 := rs (se 4 (by rfl) ⟨27288, by rfl⟩) (B 54577 (by norm_num) ⟨27288, by rfl⟩ (by norm_num))
theorem R61701 : Reach 61701 := rs (se 4 (by rfl) ⟨5784, by rfl⟩) (B 11569 (by norm_num) ⟨5784, by rfl⟩ (by norm_num))
theorem R94469 : Reach 94469 := rs (se 4 (by rfl) ⟨8856, by rfl⟩) (B 17713 (by norm_num) ⟨8856, by rfl⟩ (by norm_num))
theorem R61705 : Reach 61705 := rs (se 2 (by rfl) ⟨23139, by rfl⟩) (B 46279 (by norm_num) ⟨23139, by rfl⟩ (by norm_num))
theorem R61709 : Reach 61709 := rs (se 3 (by rfl) ⟨11570, by rfl⟩) (B 23141 (by norm_num) ⟨11570, by rfl⟩ (by norm_num))
theorem R61713 : Reach 61713 := rs (se 2 (by rfl) ⟨23142, by rfl⟩) (B 46285 (by norm_num) ⟨23142, by rfl⟩ (by norm_num))
theorem R61717 : Reach 61717 := rs (se 6 (by rfl) ⟨1446, by rfl⟩) (B 2893 (by norm_num) ⟨1446, by rfl⟩ (by norm_num))
theorem R61721 : Reach 61721 := rs (se 2 (by rfl) ⟨23145, by rfl⟩) (B 46291 (by norm_num) ⟨23145, by rfl⟩ (by norm_num))
theorem R61725 : Reach 61725 := rs (se 3 (by rfl) ⟨11573, by rfl⟩) (B 23147 (by norm_num) ⟨11573, by rfl⟩ (by norm_num))
theorem R94493 : Reach 94493 := rs (se 3 (by rfl) ⟨17717, by rfl⟩) (B 35435 (by norm_num) ⟨17717, by rfl⟩ (by norm_num))
theorem R61729 : Reach 61729 := rs (se 2 (by rfl) ⟨23148, by rfl⟩) (B 46297 (by norm_num) ⟨23148, by rfl⟩ (by norm_num))
theorem R61733 : Reach 61733 := rs (se 4 (by rfl) ⟨5787, by rfl⟩) (B 11575 (by norm_num) ⟨5787, by rfl⟩ (by norm_num))
theorem R61737 : Reach 61737 := rs (se 2 (by rfl) ⟨23151, by rfl⟩) (B 46303 (by norm_num) ⟨23151, by rfl⟩ (by norm_num))
theorem R61741 : Reach 61741 := rs (se 3 (by rfl) ⟨11576, by rfl⟩) (B 23153 (by norm_num) ⟨11576, by rfl⟩ (by norm_num))
theorem R61745 : Reach 61745 := rs (se 2 (by rfl) ⟨23154, by rfl⟩) (B 46309 (by norm_num) ⟨23154, by rfl⟩ (by norm_num))
theorem R61749 : Reach 61749 := rs (se 5 (by rfl) ⟨2894, by rfl⟩) (B 5789 (by norm_num) ⟨2894, by rfl⟩ (by norm_num))
theorem R94517 : Reach 94517 := rs (se 5 (by rfl) ⟨4430, by rfl⟩) (B 8861 (by norm_num) ⟨4430, by rfl⟩ (by norm_num))
theorem R61753 : Reach 61753 := rs (se 2 (by rfl) ⟨23157, by rfl⟩) (B 46315 (by norm_num) ⟨23157, by rfl⟩ (by norm_num))
theorem R61757 : Reach 61757 := rs (se 3 (by rfl) ⟨11579, by rfl⟩) (B 23159 (by norm_num) ⟨11579, by rfl⟩ (by norm_num))
theorem R61761 : Reach 61761 := rs (se 2 (by rfl) ⟨23160, by rfl⟩) (B 46321 (by norm_num) ⟨23160, by rfl⟩ (by norm_num))
theorem R61765 : Reach 61765 := rs (se 4 (by rfl) ⟨5790, by rfl⟩) (B 11581 (by norm_num) ⟨5790, by rfl⟩ (by norm_num))
theorem R61769 : Reach 61769 := rs (se 2 (by rfl) ⟨23163, by rfl⟩) (B 46327 (by norm_num) ⟨23163, by rfl⟩ (by norm_num))
theorem R61773 : Reach 61773 := rs (se 3 (by rfl) ⟨11582, by rfl⟩) (B 23165 (by norm_num) ⟨11582, by rfl⟩ (by norm_num))
theorem R94541 : Reach 94541 := rs (se 3 (by rfl) ⟨17726, by rfl⟩) (B 35453 (by norm_num) ⟨17726, by rfl⟩ (by norm_num))
theorem R61777 : Reach 61777 := rs (se 2 (by rfl) ⟨23166, by rfl⟩) (B 46333 (by norm_num) ⟨23166, by rfl⟩ (by norm_num))
theorem R61781 : Reach 61781 := rs (se 10 (by rfl) ⟨90, by rfl⟩) (B 181 (by norm_num) ⟨90, by rfl⟩ (by norm_num))
theorem R61785 : Reach 61785 := rs (se 2 (by rfl) ⟨23169, by rfl⟩) (B 46339 (by norm_num) ⟨23169, by rfl⟩ (by norm_num))
theorem R127325 : Reach 127325 := rs (se 3 (by rfl) ⟨23873, by rfl⟩) (B 47747 (by norm_num) ⟨23873, by rfl⟩ (by norm_num))
theorem R61789 : Reach 61789 := rs (se 3 (by rfl) ⟨11585, by rfl⟩) (B 23171 (by norm_num) ⟨11585, by rfl⟩ (by norm_num))
theorem R61793 : Reach 61793 := rs (se 2 (by rfl) ⟨23172, by rfl⟩) (B 46345 (by norm_num) ⟨23172, by rfl⟩ (by norm_num))
theorem R61797 : Reach 61797 := rs (se 4 (by rfl) ⟨5793, by rfl⟩) (B 11587 (by norm_num) ⟨5793, by rfl⟩ (by norm_num))
theorem R94565 : Reach 94565 := rs (se 4 (by rfl) ⟨8865, by rfl⟩) (B 17731 (by norm_num) ⟨8865, by rfl⟩ (by norm_num))
theorem R61801 : Reach 61801 := rs (se 2 (by rfl) ⟨23175, by rfl⟩) (B 46351 (by norm_num) ⟨23175, by rfl⟩ (by norm_num))
theorem R61805 : Reach 61805 := rs (se 3 (by rfl) ⟨11588, by rfl⟩) (B 23177 (by norm_num) ⟨11588, by rfl⟩ (by norm_num))
theorem R61809 : Reach 61809 := rs (se 2 (by rfl) ⟨23178, by rfl⟩) (B 46357 (by norm_num) ⟨23178, by rfl⟩ (by norm_num))
theorem R61813 : Reach 61813 := rs (se 5 (by rfl) ⟨2897, by rfl⟩) (B 5795 (by norm_num) ⟨2897, by rfl⟩ (by norm_num))
theorem R61817 : Reach 61817 := rs (se 2 (by rfl) ⟨23181, by rfl⟩) (B 46363 (by norm_num) ⟨23181, by rfl⟩ (by norm_num))
theorem R61821 : Reach 61821 := rs (se 3 (by rfl) ⟨11591, by rfl⟩) (B 23183 (by norm_num) ⟨11591, by rfl⟩ (by norm_num))
theorem R94589 : Reach 94589 := rs (se 3 (by rfl) ⟨17735, by rfl⟩) (B 35471 (by norm_num) ⟨17735, by rfl⟩ (by norm_num))
theorem R61825 : Reach 61825 := rs (se 2 (by rfl) ⟨23184, by rfl⟩) (B 46369 (by norm_num) ⟨23184, by rfl⟩ (by norm_num))
theorem R61829 : Reach 61829 := rs (se 4 (by rfl) ⟨5796, by rfl⟩) (B 11593 (by norm_num) ⟨5796, by rfl⟩ (by norm_num))
theorem R61833 : Reach 61833 := rs (se 2 (by rfl) ⟨23187, by rfl⟩) (B 46375 (by norm_num) ⟨23187, by rfl⟩ (by norm_num))
theorem R61837 : Reach 61837 := rs (se 3 (by rfl) ⟨11594, by rfl⟩) (B 23189 (by norm_num) ⟨11594, by rfl⟩ (by norm_num))
theorem R61841 : Reach 61841 := rs (se 2 (by rfl) ⟨23190, by rfl⟩) (B 46381 (by norm_num) ⟨23190, by rfl⟩ (by norm_num))
theorem R61845 : Reach 61845 := rs (se 6 (by rfl) ⟨1449, by rfl⟩) (B 2899 (by norm_num) ⟨1449, by rfl⟩ (by norm_num))
theorem R94613 : Reach 94613 := rs (se 6 (by rfl) ⟨2217, by rfl⟩) (B 4435 (by norm_num) ⟨2217, by rfl⟩ (by norm_num))
theorem R61849 : Reach 61849 := rs (se 2 (by rfl) ⟨23193, by rfl⟩) (B 46387 (by norm_num) ⟨23193, by rfl⟩ (by norm_num))
theorem R61853 : Reach 61853 := rs (se 3 (by rfl) ⟨11597, by rfl⟩) (B 23195 (by norm_num) ⟨11597, by rfl⟩ (by norm_num))
theorem R61857 : Reach 61857 := rs (se 2 (by rfl) ⟨23196, by rfl⟩) (B 46393 (by norm_num) ⟨23196, by rfl⟩ (by norm_num))
theorem R61861 : Reach 61861 := rs (se 4 (by rfl) ⟨5799, by rfl⟩) (B 11599 (by norm_num) ⟨5799, by rfl⟩ (by norm_num))
theorem R61865 : Reach 61865 := rs (se 2 (by rfl) ⟨23199, by rfl⟩) (B 46399 (by norm_num) ⟨23199, by rfl⟩ (by norm_num))
theorem R61869 : Reach 61869 := rs (se 3 (by rfl) ⟨11600, by rfl⟩) (B 23201 (by norm_num) ⟨11600, by rfl⟩ (by norm_num))
theorem R94637 : Reach 94637 := rs (se 3 (by rfl) ⟨17744, by rfl⟩) (B 35489 (by norm_num) ⟨17744, by rfl⟩ (by norm_num))
theorem R61873 : Reach 61873 := rs (se 2 (by rfl) ⟨23202, by rfl⟩) (B 46405 (by norm_num) ⟨23202, by rfl⟩ (by norm_num))
theorem R61877 : Reach 61877 := rs (se 5 (by rfl) ⟨2900, by rfl⟩) (B 5801 (by norm_num) ⟨2900, by rfl⟩ (by norm_num))
theorem R61881 : Reach 61881 := rs (se 2 (by rfl) ⟨23205, by rfl⟩) (B 46411 (by norm_num) ⟨23205, by rfl⟩ (by norm_num))
theorem R61885 : Reach 61885 := rs (se 3 (by rfl) ⟨11603, by rfl⟩) (B 23207 (by norm_num) ⟨11603, by rfl⟩ (by norm_num))
theorem R61889 : Reach 61889 := rs (se 2 (by rfl) ⟨23208, by rfl⟩) (B 46417 (by norm_num) ⟨23208, by rfl⟩ (by norm_num))
theorem R61893 : Reach 61893 := rs (se 4 (by rfl) ⟨5802, by rfl⟩) (B 11605 (by norm_num) ⟨5802, by rfl⟩ (by norm_num))
theorem R94661 : Reach 94661 := rs (se 4 (by rfl) ⟨8874, by rfl⟩) (B 17749 (by norm_num) ⟨8874, by rfl⟩ (by norm_num))
theorem R61897 : Reach 61897 := rs (se 2 (by rfl) ⟨23211, by rfl⟩) (B 46423 (by norm_num) ⟨23211, by rfl⟩ (by norm_num))
theorem R61901 : Reach 61901 := rs (se 3 (by rfl) ⟨11606, by rfl⟩) (B 23213 (by norm_num) ⟨11606, by rfl⟩ (by norm_num))
theorem R61905 : Reach 61905 := rs (se 2 (by rfl) ⟨23214, by rfl⟩) (B 46429 (by norm_num) ⟨23214, by rfl⟩ (by norm_num))
theorem R61909 : Reach 61909 := rs (se 7 (by rfl) ⟨725, by rfl⟩) (B 1451 (by norm_num) ⟨725, by rfl⟩ (by norm_num))
theorem R61913 : Reach 61913 := rs (se 2 (by rfl) ⟨23217, by rfl⟩) (B 46435 (by norm_num) ⟨23217, by rfl⟩ (by norm_num))
theorem R61917 : Reach 61917 := rs (se 3 (by rfl) ⟨11609, by rfl⟩) (B 23219 (by norm_num) ⟨11609, by rfl⟩ (by norm_num))
theorem R61921 : Reach 61921 := rs (se 2 (by rfl) ⟨23220, by rfl⟩) (B 46441 (by norm_num) ⟨23220, by rfl⟩ (by norm_num))
theorem R61925 : Reach 61925 := rs (se 4 (by rfl) ⟨5805, by rfl⟩) (B 11611 (by norm_num) ⟨5805, by rfl⟩ (by norm_num))
theorem R61929 : Reach 61929 := rs (se 2 (by rfl) ⟨23223, by rfl⟩) (B 46447 (by norm_num) ⟨23223, by rfl⟩ (by norm_num))
theorem R61933 : Reach 61933 := rs (se 3 (by rfl) ⟨11612, by rfl⟩) (B 23225 (by norm_num) ⟨11612, by rfl⟩ (by norm_num))
theorem R61937 : Reach 61937 := rs (se 2 (by rfl) ⟨23226, by rfl⟩) (B 46453 (by norm_num) ⟨23226, by rfl⟩ (by norm_num))
theorem R61941 : Reach 61941 := rs (se 5 (by rfl) ⟨2903, by rfl⟩) (B 5807 (by norm_num) ⟨2903, by rfl⟩ (by norm_num))
theorem R61945 : Reach 61945 := rs (se 2 (by rfl) ⟨23229, by rfl⟩) (B 46459 (by norm_num) ⟨23229, by rfl⟩ (by norm_num))
theorem R61949 : Reach 61949 := rs (se 3 (by rfl) ⟨11615, by rfl⟩) (B 23231 (by norm_num) ⟨11615, by rfl⟩ (by norm_num))
theorem R61953 : Reach 61953 := rs (se 2 (by rfl) ⟨23232, by rfl⟩) (B 46465 (by norm_num) ⟨23232, by rfl⟩ (by norm_num))
theorem R61957 : Reach 61957 := rs (se 4 (by rfl) ⟨5808, by rfl⟩) (B 11617 (by norm_num) ⟨5808, by rfl⟩ (by norm_num))
theorem R61961 : Reach 61961 := rs (se 2 (by rfl) ⟨23235, by rfl⟩) (B 46471 (by norm_num) ⟨23235, by rfl⟩ (by norm_num))
theorem R61965 : Reach 61965 := rs (se 3 (by rfl) ⟨11618, by rfl⟩) (B 23237 (by norm_num) ⟨11618, by rfl⟩ (by norm_num))
theorem R61969 : Reach 61969 := rs (se 2 (by rfl) ⟨23238, by rfl⟩) (B 46477 (by norm_num) ⟨23238, by rfl⟩ (by norm_num))
theorem R61973 : Reach 61973 := rs (se 6 (by rfl) ⟨1452, by rfl⟩) (B 2905 (by norm_num) ⟨1452, by rfl⟩ (by norm_num))
theorem R61977 : Reach 61977 := rs (se 2 (by rfl) ⟨23241, by rfl⟩) (B 46483 (by norm_num) ⟨23241, by rfl⟩ (by norm_num))
theorem R61981 : Reach 61981 := rs (se 3 (by rfl) ⟨11621, by rfl⟩) (B 23243 (by norm_num) ⟨11621, by rfl⟩ (by norm_num))
theorem R61985 : Reach 61985 := rs (se 2 (by rfl) ⟨23244, by rfl⟩) (B 46489 (by norm_num) ⟨23244, by rfl⟩ (by norm_num))
theorem R61989 : Reach 61989 := rs (se 4 (by rfl) ⟨5811, by rfl⟩) (B 11623 (by norm_num) ⟨5811, by rfl⟩ (by norm_num))
theorem R61993 : Reach 61993 := rs (se 2 (by rfl) ⟨23247, by rfl⟩) (B 46495 (by norm_num) ⟨23247, by rfl⟩ (by norm_num))
theorem R61997 : Reach 61997 := rs (se 3 (by rfl) ⟨11624, by rfl⟩) (B 23249 (by norm_num) ⟨11624, by rfl⟩ (by norm_num))
theorem R62001 : Reach 62001 := rs (se 2 (by rfl) ⟨23250, by rfl⟩) (B 46501 (by norm_num) ⟨23250, by rfl⟩ (by norm_num))
theorem R62005 : Reach 62005 := rs (se 5 (by rfl) ⟨2906, by rfl⟩) (B 5813 (by norm_num) ⟨2906, by rfl⟩ (by norm_num))
theorem R62009 : Reach 62009 := rs (se 2 (by rfl) ⟨23253, by rfl⟩) (B 46507 (by norm_num) ⟨23253, by rfl⟩ (by norm_num))
theorem R62013 : Reach 62013 := rs (se 3 (by rfl) ⟨11627, by rfl⟩) (B 23255 (by norm_num) ⟨11627, by rfl⟩ (by norm_num))
theorem R62017 : Reach 62017 := rs (se 2 (by rfl) ⟨23256, by rfl⟩) (B 46513 (by norm_num) ⟨23256, by rfl⟩ (by norm_num))
theorem R62021 : Reach 62021 := rs (se 4 (by rfl) ⟨5814, by rfl⟩) (B 11629 (by norm_num) ⟨5814, by rfl⟩ (by norm_num))
theorem R62025 : Reach 62025 := rs (se 2 (by rfl) ⟨23259, by rfl⟩) (B 46519 (by norm_num) ⟨23259, by rfl⟩ (by norm_num))
theorem R62029 : Reach 62029 := rs (se 3 (by rfl) ⟨11630, by rfl⟩) (B 23261 (by norm_num) ⟨11630, by rfl⟩ (by norm_num))
theorem R62033 : Reach 62033 := rs (se 2 (by rfl) ⟨23262, by rfl⟩) (B 46525 (by norm_num) ⟨23262, by rfl⟩ (by norm_num))
theorem R62037 : Reach 62037 := rs (se 8 (by rfl) ⟨363, by rfl⟩) (B 727 (by norm_num) ⟨363, by rfl⟩ (by norm_num))
theorem R62041 : Reach 62041 := rs (se 2 (by rfl) ⟨23265, by rfl⟩) (B 46531 (by norm_num) ⟨23265, by rfl⟩ (by norm_num))
theorem R62045 : Reach 62045 := rs (se 3 (by rfl) ⟨11633, by rfl⟩) (B 23267 (by norm_num) ⟨11633, by rfl⟩ (by norm_num))
theorem R62049 : Reach 62049 := rs (se 2 (by rfl) ⟨23268, by rfl⟩) (B 46537 (by norm_num) ⟨23268, by rfl⟩ (by norm_num))
theorem R62053 : Reach 62053 := rs (se 4 (by rfl) ⟨5817, by rfl⟩) (B 11635 (by norm_num) ⟨5817, by rfl⟩ (by norm_num))
theorem R62057 : Reach 62057 := rs (se 2 (by rfl) ⟨23271, by rfl⟩) (B 46543 (by norm_num) ⟨23271, by rfl⟩ (by norm_num))
theorem R62061 : Reach 62061 := rs (se 3 (by rfl) ⟨11636, by rfl⟩) (B 23273 (by norm_num) ⟨11636, by rfl⟩ (by norm_num))
theorem R62065 : Reach 62065 := rs (se 2 (by rfl) ⟨23274, by rfl⟩) (B 46549 (by norm_num) ⟨23274, by rfl⟩ (by norm_num))
theorem R62069 : Reach 62069 := rs (se 5 (by rfl) ⟨2909, by rfl⟩) (B 5819 (by norm_num) ⟨2909, by rfl⟩ (by norm_num))
theorem R62073 : Reach 62073 := rs (se 2 (by rfl) ⟨23277, by rfl⟩) (B 46555 (by norm_num) ⟨23277, by rfl⟩ (by norm_num))
theorem R62077 : Reach 62077 := rs (se 3 (by rfl) ⟨11639, by rfl⟩) (B 23279 (by norm_num) ⟨11639, by rfl⟩ (by norm_num))
theorem R62081 : Reach 62081 := rs (se 2 (by rfl) ⟨23280, by rfl⟩) (B 46561 (by norm_num) ⟨23280, by rfl⟩ (by norm_num))
theorem R62085 : Reach 62085 := rs (se 4 (by rfl) ⟨5820, by rfl⟩) (B 11641 (by norm_num) ⟨5820, by rfl⟩ (by norm_num))
theorem R62089 : Reach 62089 := rs (se 2 (by rfl) ⟨23283, by rfl⟩) (B 46567 (by norm_num) ⟨23283, by rfl⟩ (by norm_num))
theorem R62093 : Reach 62093 := rs (se 3 (by rfl) ⟨11642, by rfl⟩) (B 23285 (by norm_num) ⟨11642, by rfl⟩ (by norm_num))
theorem R62097 : Reach 62097 := rs (se 2 (by rfl) ⟨23286, by rfl⟩) (B 46573 (by norm_num) ⟨23286, by rfl⟩ (by norm_num))
theorem R62101 : Reach 62101 := rs (se 6 (by rfl) ⟨1455, by rfl⟩) (B 2911 (by norm_num) ⟨1455, by rfl⟩ (by norm_num))
theorem R62105 : Reach 62105 := rs (se 2 (by rfl) ⟨23289, by rfl⟩) (B 46579 (by norm_num) ⟨23289, by rfl⟩ (by norm_num))
theorem R62109 : Reach 62109 := rs (se 3 (by rfl) ⟨11645, by rfl⟩) (B 23291 (by norm_num) ⟨11645, by rfl⟩ (by norm_num))
theorem R62113 : Reach 62113 := rs (se 2 (by rfl) ⟨23292, by rfl⟩) (B 46585 (by norm_num) ⟨23292, by rfl⟩ (by norm_num))
theorem R62117 : Reach 62117 := rs (se 4 (by rfl) ⟨5823, by rfl⟩) (B 11647 (by norm_num) ⟨5823, by rfl⟩ (by norm_num))
theorem R62121 : Reach 62121 := rs (se 2 (by rfl) ⟨23295, by rfl⟩) (B 46591 (by norm_num) ⟨23295, by rfl⟩ (by norm_num))
theorem R62125 : Reach 62125 := rs (se 3 (by rfl) ⟨11648, by rfl⟩) (B 23297 (by norm_num) ⟨11648, by rfl⟩ (by norm_num))
theorem R62129 : Reach 62129 := rs (se 2 (by rfl) ⟨23298, by rfl⟩) (B 46597 (by norm_num) ⟨23298, by rfl⟩ (by norm_num))
theorem R62133 : Reach 62133 := rs (se 5 (by rfl) ⟨2912, by rfl⟩) (B 5825 (by norm_num) ⟨2912, by rfl⟩ (by norm_num))
theorem R62137 : Reach 62137 := rs (se 2 (by rfl) ⟨23301, by rfl⟩) (B 46603 (by norm_num) ⟨23301, by rfl⟩ (by norm_num))
theorem R62141 : Reach 62141 := rs (se 3 (by rfl) ⟨11651, by rfl⟩) (B 23303 (by norm_num) ⟨11651, by rfl⟩ (by norm_num))
theorem R62145 : Reach 62145 := rs (se 2 (by rfl) ⟨23304, by rfl⟩) (B 46609 (by norm_num) ⟨23304, by rfl⟩ (by norm_num))
theorem R62149 : Reach 62149 := rs (se 4 (by rfl) ⟨5826, by rfl⟩) (B 11653 (by norm_num) ⟨5826, by rfl⟩ (by norm_num))
theorem R62153 : Reach 62153 := rs (se 2 (by rfl) ⟨23307, by rfl⟩) (B 46615 (by norm_num) ⟨23307, by rfl⟩ (by norm_num))
theorem R62157 : Reach 62157 := rs (se 3 (by rfl) ⟨11654, by rfl⟩) (B 23309 (by norm_num) ⟨11654, by rfl⟩ (by norm_num))
theorem R62161 : Reach 62161 := rs (se 2 (by rfl) ⟨23310, by rfl⟩) (B 46621 (by norm_num) ⟨23310, by rfl⟩ (by norm_num))
theorem R455381 : Reach 455381 := rs (se 7 (by rfl) ⟨5336, by rfl⟩) (B 10673 (by norm_num) ⟨5336, by rfl⟩ (by norm_num))
theorem R62165 : Reach 62165 := rs (se 7 (by rfl) ⟨728, by rfl⟩) (B 1457 (by norm_num) ⟨728, by rfl⟩ (by norm_num))
theorem R62169 : Reach 62169 := rs (se 2 (by rfl) ⟨23313, by rfl⟩) (B 46627 (by norm_num) ⟨23313, by rfl⟩ (by norm_num))
theorem R62173 : Reach 62173 := rs (se 3 (by rfl) ⟨11657, by rfl⟩) (B 23315 (by norm_num) ⟨11657, by rfl⟩ (by norm_num))
theorem R62177 : Reach 62177 := rs (se 2 (by rfl) ⟨23316, by rfl⟩) (B 46633 (by norm_num) ⟨23316, by rfl⟩ (by norm_num))
theorem R62181 : Reach 62181 := rs (se 4 (by rfl) ⟨5829, by rfl⟩) (B 11659 (by norm_num) ⟨5829, by rfl⟩ (by norm_num))
theorem R62185 : Reach 62185 := rs (se 2 (by rfl) ⟨23319, by rfl⟩) (B 46639 (by norm_num) ⟨23319, by rfl⟩ (by norm_num))
theorem R62189 : Reach 62189 := rs (se 3 (by rfl) ⟨11660, by rfl⟩) (B 23321 (by norm_num) ⟨11660, by rfl⟩ (by norm_num))
theorem R62193 : Reach 62193 := rs (se 2 (by rfl) ⟨23322, by rfl⟩) (B 46645 (by norm_num) ⟨23322, by rfl⟩ (by norm_num))
theorem R62197 : Reach 62197 := rs (se 5 (by rfl) ⟨2915, by rfl⟩) (B 5831 (by norm_num) ⟨2915, by rfl⟩ (by norm_num))
theorem R62201 : Reach 62201 := rs (se 2 (by rfl) ⟨23325, by rfl⟩) (B 46651 (by norm_num) ⟨23325, by rfl⟩ (by norm_num))
theorem R62205 : Reach 62205 := rs (se 3 (by rfl) ⟨11663, by rfl⟩) (B 23327 (by norm_num) ⟨11663, by rfl⟩ (by norm_num))
theorem R62209 : Reach 62209 := rs (se 2 (by rfl) ⟨23328, by rfl⟩) (B 46657 (by norm_num) ⟨23328, by rfl⟩ (by norm_num))
theorem R94981 : Reach 94981 := rs (se 4 (by rfl) ⟨8904, by rfl⟩) (B 17809 (by norm_num) ⟨8904, by rfl⟩ (by norm_num))
theorem R62213 : Reach 62213 := rs (se 4 (by rfl) ⟨5832, by rfl⟩) (B 11665 (by norm_num) ⟨5832, by rfl⟩ (by norm_num))
theorem R62217 : Reach 62217 := rs (se 2 (by rfl) ⟨23331, by rfl⟩) (B 46663 (by norm_num) ⟨23331, by rfl⟩ (by norm_num))
theorem R62221 : Reach 62221 := rs (se 3 (by rfl) ⟨11666, by rfl⟩) (B 23333 (by norm_num) ⟨11666, by rfl⟩ (by norm_num))
theorem R62225 : Reach 62225 := rs (se 2 (by rfl) ⟨23334, by rfl⟩) (B 46669 (by norm_num) ⟨23334, by rfl⟩ (by norm_num))
theorem R62229 : Reach 62229 := rs (se 6 (by rfl) ⟨1458, by rfl⟩) (B 2917 (by norm_num) ⟨1458, by rfl⟩ (by norm_num))
theorem R62233 : Reach 62233 := rs (se 2 (by rfl) ⟨23337, by rfl⟩) (B 46675 (by norm_num) ⟨23337, by rfl⟩ (by norm_num))
theorem R62237 : Reach 62237 := rs (se 3 (by rfl) ⟨11669, by rfl⟩) (B 23339 (by norm_num) ⟨11669, by rfl⟩ (by norm_num))
theorem R62241 : Reach 62241 := rs (se 2 (by rfl) ⟨23340, by rfl⟩) (B 46681 (by norm_num) ⟨23340, by rfl⟩ (by norm_num))
theorem R62245 : Reach 62245 := rs (se 4 (by rfl) ⟨5835, by rfl⟩) (B 11671 (by norm_num) ⟨5835, by rfl⟩ (by norm_num))
theorem R62249 : Reach 62249 := rs (se 2 (by rfl) ⟨23343, by rfl⟩) (B 46687 (by norm_num) ⟨23343, by rfl⟩ (by norm_num))
theorem R62253 : Reach 62253 := rs (se 3 (by rfl) ⟨11672, by rfl⟩) (B 23345 (by norm_num) ⟨11672, by rfl⟩ (by norm_num))
theorem R62257 : Reach 62257 := rs (se 2 (by rfl) ⟨23346, by rfl⟩) (B 46693 (by norm_num) ⟨23346, by rfl⟩ (by norm_num))
theorem R62261 : Reach 62261 := rs (se 5 (by rfl) ⟨2918, by rfl⟩) (B 5837 (by norm_num) ⟨2918, by rfl⟩ (by norm_num))
theorem R62265 : Reach 62265 := rs (se 2 (by rfl) ⟨23349, by rfl⟩) (B 46699 (by norm_num) ⟨23349, by rfl⟩ (by norm_num))
theorem R62269 : Reach 62269 := rs (se 3 (by rfl) ⟨11675, by rfl⟩) (B 23351 (by norm_num) ⟨11675, by rfl⟩ (by norm_num))
theorem R62273 : Reach 62273 := rs (se 2 (by rfl) ⟨23352, by rfl⟩) (B 46705 (by norm_num) ⟨23352, by rfl⟩ (by norm_num))
theorem R62277 : Reach 62277 := rs (se 4 (by rfl) ⟨5838, by rfl⟩) (B 11677 (by norm_num) ⟨5838, by rfl⟩ (by norm_num))
theorem R62281 : Reach 62281 := rs (se 2 (by rfl) ⟨23355, by rfl⟩) (B 46711 (by norm_num) ⟨23355, by rfl⟩ (by norm_num))
theorem R62285 : Reach 62285 := rs (se 3 (by rfl) ⟨11678, by rfl⟩) (B 23357 (by norm_num) ⟨11678, by rfl⟩ (by norm_num))
theorem R62289 : Reach 62289 := rs (se 2 (by rfl) ⟨23358, by rfl⟩) (B 46717 (by norm_num) ⟨23358, by rfl⟩ (by norm_num))
theorem R62293 : Reach 62293 := rs (se 9 (by rfl) ⟨182, by rfl⟩) (B 365 (by norm_num) ⟨182, by rfl⟩ (by norm_num))
theorem R62297 : Reach 62297 := rs (se 2 (by rfl) ⟨23361, by rfl⟩) (B 46723 (by norm_num) ⟨23361, by rfl⟩ (by norm_num))
theorem R62301 : Reach 62301 := rs (se 3 (by rfl) ⟨11681, by rfl⟩) (B 23363 (by norm_num) ⟨11681, by rfl⟩ (by norm_num))
theorem R62305 : Reach 62305 := rs (se 2 (by rfl) ⟨23364, by rfl⟩) (B 46729 (by norm_num) ⟨23364, by rfl⟩ (by norm_num))
theorem R62309 : Reach 62309 := rs (se 4 (by rfl) ⟨5841, by rfl⟩) (B 11683 (by norm_num) ⟨5841, by rfl⟩ (by norm_num))
theorem R62313 : Reach 62313 := rs (se 2 (by rfl) ⟨23367, by rfl⟩) (B 46735 (by norm_num) ⟨23367, by rfl⟩ (by norm_num))
theorem R62317 : Reach 62317 := rs (se 3 (by rfl) ⟨11684, by rfl⟩) (B 23369 (by norm_num) ⟨11684, by rfl⟩ (by norm_num))
theorem R62321 : Reach 62321 := rs (se 2 (by rfl) ⟨23370, by rfl⟩) (B 46741 (by norm_num) ⟨23370, by rfl⟩ (by norm_num))
theorem R62325 : Reach 62325 := rs (se 5 (by rfl) ⟨2921, by rfl⟩) (B 5843 (by norm_num) ⟨2921, by rfl⟩ (by norm_num))
theorem R62329 : Reach 62329 := rs (se 2 (by rfl) ⟨23373, by rfl⟩) (B 46747 (by norm_num) ⟨23373, by rfl⟩ (by norm_num))
theorem R62333 : Reach 62333 := rs (se 3 (by rfl) ⟨11687, by rfl⟩) (B 23375 (by norm_num) ⟨11687, by rfl⟩ (by norm_num))
theorem R62337 : Reach 62337 := rs (se 2 (by rfl) ⟨23376, by rfl⟩) (B 46753 (by norm_num) ⟨23376, by rfl⟩ (by norm_num))
theorem R62341 : Reach 62341 := rs (se 4 (by rfl) ⟨5844, by rfl⟩) (B 11689 (by norm_num) ⟨5844, by rfl⟩ (by norm_num))
theorem R62345 : Reach 62345 := rs (se 2 (by rfl) ⟨23379, by rfl⟩) (B 46759 (by norm_num) ⟨23379, by rfl⟩ (by norm_num))
theorem R62349 : Reach 62349 := rs (se 3 (by rfl) ⟨11690, by rfl⟩) (B 23381 (by norm_num) ⟨11690, by rfl⟩ (by norm_num))
theorem R62353 : Reach 62353 := rs (se 2 (by rfl) ⟨23382, by rfl⟩) (B 46765 (by norm_num) ⟨23382, by rfl⟩ (by norm_num))
theorem R62357 : Reach 62357 := rs (se 6 (by rfl) ⟨1461, by rfl⟩) (B 2923 (by norm_num) ⟨1461, by rfl⟩ (by norm_num))
theorem R62361 : Reach 62361 := rs (se 2 (by rfl) ⟨23385, by rfl⟩) (B 46771 (by norm_num) ⟨23385, by rfl⟩ (by norm_num))
theorem R62365 : Reach 62365 := rs (se 3 (by rfl) ⟨11693, by rfl⟩) (B 23387 (by norm_num) ⟨11693, by rfl⟩ (by norm_num))
theorem R62369 : Reach 62369 := rs (se 2 (by rfl) ⟨23388, by rfl⟩) (B 46777 (by norm_num) ⟨23388, by rfl⟩ (by norm_num))
theorem R62373 : Reach 62373 := rs (se 4 (by rfl) ⟨5847, by rfl⟩) (B 11695 (by norm_num) ⟨5847, by rfl⟩ (by norm_num))
theorem R62377 : Reach 62377 := rs (se 2 (by rfl) ⟨23391, by rfl⟩) (B 46783 (by norm_num) ⟨23391, by rfl⟩ (by norm_num))
theorem R62381 : Reach 62381 := rs (se 3 (by rfl) ⟨11696, by rfl⟩) (B 23393 (by norm_num) ⟨11696, by rfl⟩ (by norm_num))
theorem R62385 : Reach 62385 := rs (se 2 (by rfl) ⟨23394, by rfl⟩) (B 46789 (by norm_num) ⟨23394, by rfl⟩ (by norm_num))
theorem R62389 : Reach 62389 := rs (se 5 (by rfl) ⟨2924, by rfl⟩) (B 5849 (by norm_num) ⟨2924, by rfl⟩ (by norm_num))
theorem R62393 : Reach 62393 := rs (se 2 (by rfl) ⟨23397, by rfl⟩) (B 46795 (by norm_num) ⟨23397, by rfl⟩ (by norm_num))
theorem R62397 : Reach 62397 := rs (se 3 (by rfl) ⟨11699, by rfl⟩) (B 23399 (by norm_num) ⟨11699, by rfl⟩ (by norm_num))
theorem R62401 : Reach 62401 := rs (se 2 (by rfl) ⟨23400, by rfl⟩) (B 46801 (by norm_num) ⟨23400, by rfl⟩ (by norm_num))
theorem R62405 : Reach 62405 := rs (se 4 (by rfl) ⟨5850, by rfl⟩) (B 11701 (by norm_num) ⟨5850, by rfl⟩ (by norm_num))
theorem R62409 : Reach 62409 := rs (se 2 (by rfl) ⟨23403, by rfl⟩) (B 46807 (by norm_num) ⟨23403, by rfl⟩ (by norm_num))
theorem R62413 : Reach 62413 := rs (se 3 (by rfl) ⟨11702, by rfl⟩) (B 23405 (by norm_num) ⟨11702, by rfl⟩ (by norm_num))
theorem R62417 : Reach 62417 := rs (se 2 (by rfl) ⟨23406, by rfl⟩) (B 46813 (by norm_num) ⟨23406, by rfl⟩ (by norm_num))
theorem R62421 : Reach 62421 := rs (se 7 (by rfl) ⟨731, by rfl⟩) (B 1463 (by norm_num) ⟨731, by rfl⟩ (by norm_num))
theorem R62425 : Reach 62425 := rs (se 2 (by rfl) ⟨23409, by rfl⟩) (B 46819 (by norm_num) ⟨23409, by rfl⟩ (by norm_num))
theorem R62429 : Reach 62429 := rs (se 3 (by rfl) ⟨11705, by rfl⟩) (B 23411 (by norm_num) ⟨11705, by rfl⟩ (by norm_num))
theorem R62433 : Reach 62433 := rs (se 2 (by rfl) ⟨23412, by rfl⟩) (B 46825 (by norm_num) ⟨23412, by rfl⟩ (by norm_num))
theorem R62437 : Reach 62437 := rs (se 4 (by rfl) ⟨5853, by rfl⟩) (B 11707 (by norm_num) ⟨5853, by rfl⟩ (by norm_num))
theorem R62441 : Reach 62441 := rs (se 2 (by rfl) ⟨23415, by rfl⟩) (B 46831 (by norm_num) ⟨23415, by rfl⟩ (by norm_num))
theorem R62445 : Reach 62445 := rs (se 3 (by rfl) ⟨11708, by rfl⟩) (B 23417 (by norm_num) ⟨11708, by rfl⟩ (by norm_num))
theorem R62449 : Reach 62449 := rs (se 2 (by rfl) ⟨23418, by rfl⟩) (B 46837 (by norm_num) ⟨23418, by rfl⟩ (by norm_num))
theorem R62453 : Reach 62453 := rs (se 5 (by rfl) ⟨2927, by rfl⟩) (B 5855 (by norm_num) ⟨2927, by rfl⟩ (by norm_num))
theorem R62457 : Reach 62457 := rs (se 2 (by rfl) ⟨23421, by rfl⟩) (B 46843 (by norm_num) ⟨23421, by rfl⟩ (by norm_num))
theorem R62461 : Reach 62461 := rs (se 3 (by rfl) ⟨11711, by rfl⟩) (B 23423 (by norm_num) ⟨11711, by rfl⟩ (by norm_num))
theorem R62465 : Reach 62465 := rs (se 2 (by rfl) ⟨23424, by rfl⟩) (B 46849 (by norm_num) ⟨23424, by rfl⟩ (by norm_num))
theorem R62469 : Reach 62469 := rs (se 4 (by rfl) ⟨5856, by rfl⟩) (B 11713 (by norm_num) ⟨5856, by rfl⟩ (by norm_num))
theorem R226309 : Reach 226309 := rs (se 4 (by rfl) ⟨21216, by rfl⟩) (B 42433 (by norm_num) ⟨21216, by rfl⟩ (by norm_num))
theorem R62473 : Reach 62473 := rs (se 2 (by rfl) ⟨23427, by rfl⟩) (B 46855 (by norm_num) ⟨23427, by rfl⟩ (by norm_num))
theorem R62477 : Reach 62477 := rs (se 3 (by rfl) ⟨11714, by rfl⟩) (B 23429 (by norm_num) ⟨11714, by rfl⟩ (by norm_num))
theorem R62481 : Reach 62481 := rs (se 2 (by rfl) ⟨23430, by rfl⟩) (B 46861 (by norm_num) ⟨23430, by rfl⟩ (by norm_num))
theorem R62485 : Reach 62485 := rs (se 6 (by rfl) ⟨1464, by rfl⟩) (B 2929 (by norm_num) ⟨1464, by rfl⟩ (by norm_num))
theorem R62489 : Reach 62489 := rs (se 2 (by rfl) ⟨23433, by rfl⟩) (B 46867 (by norm_num) ⟨23433, by rfl⟩ (by norm_num))
theorem R62493 : Reach 62493 := rs (se 3 (by rfl) ⟨11717, by rfl⟩) (B 23435 (by norm_num) ⟨11717, by rfl⟩ (by norm_num))
theorem R62497 : Reach 62497 := rs (se 2 (by rfl) ⟨23436, by rfl⟩) (B 46873 (by norm_num) ⟨23436, by rfl⟩ (by norm_num))
theorem R62501 : Reach 62501 := rs (se 4 (by rfl) ⟨5859, by rfl⟩) (B 11719 (by norm_num) ⟨5859, by rfl⟩ (by norm_num))
theorem R62505 : Reach 62505 := rs (se 2 (by rfl) ⟨23439, by rfl⟩) (B 46879 (by norm_num) ⟨23439, by rfl⟩ (by norm_num))
theorem R62509 : Reach 62509 := rs (se 3 (by rfl) ⟨11720, by rfl⟩) (B 23441 (by norm_num) ⟨11720, by rfl⟩ (by norm_num))
theorem R62513 : Reach 62513 := rs (se 2 (by rfl) ⟨23442, by rfl⟩) (B 46885 (by norm_num) ⟨23442, by rfl⟩ (by norm_num))
theorem R62517 : Reach 62517 := rs (se 5 (by rfl) ⟨2930, by rfl⟩) (B 5861 (by norm_num) ⟨2930, by rfl⟩ (by norm_num))
theorem R62521 : Reach 62521 := rs (se 2 (by rfl) ⟨23445, by rfl⟩) (B 46891 (by norm_num) ⟨23445, by rfl⟩ (by norm_num))
theorem R62525 : Reach 62525 := rs (se 3 (by rfl) ⟨11723, by rfl⟩) (B 23447 (by norm_num) ⟨11723, by rfl⟩ (by norm_num))
theorem R62529 : Reach 62529 := rs (se 2 (by rfl) ⟨23448, by rfl⟩) (B 46897 (by norm_num) ⟨23448, by rfl⟩ (by norm_num))
theorem R62533 : Reach 62533 := rs (se 4 (by rfl) ⟨5862, by rfl⟩) (B 11725 (by norm_num) ⟨5862, by rfl⟩ (by norm_num))
theorem R62537 : Reach 62537 := rs (se 2 (by rfl) ⟨23451, by rfl⟩) (B 46903 (by norm_num) ⟨23451, by rfl⟩ (by norm_num))
theorem R62541 : Reach 62541 := rs (se 3 (by rfl) ⟨11726, by rfl⟩) (B 23453 (by norm_num) ⟨11726, by rfl⟩ (by norm_num))
theorem R62545 : Reach 62545 := rs (se 2 (by rfl) ⟨23454, by rfl⟩) (B 46909 (by norm_num) ⟨23454, by rfl⟩ (by norm_num))
theorem R62549 : Reach 62549 := rs (se 8 (by rfl) ⟨366, by rfl⟩) (B 733 (by norm_num) ⟨366, by rfl⟩ (by norm_num))
theorem R62553 : Reach 62553 := rs (se 2 (by rfl) ⟨23457, by rfl⟩) (B 46915 (by norm_num) ⟨23457, by rfl⟩ (by norm_num))
theorem R62557 : Reach 62557 := rs (se 3 (by rfl) ⟨11729, by rfl⟩) (B 23459 (by norm_num) ⟨11729, by rfl⟩ (by norm_num))
theorem R62561 : Reach 62561 := rs (se 2 (by rfl) ⟨23460, by rfl⟩) (B 46921 (by norm_num) ⟨23460, by rfl⟩ (by norm_num))
theorem R62565 : Reach 62565 := rs (se 4 (by rfl) ⟨5865, by rfl⟩) (B 11731 (by norm_num) ⟨5865, by rfl⟩ (by norm_num))
theorem R62569 : Reach 62569 := rs (se 2 (by rfl) ⟨23463, by rfl⟩) (B 46927 (by norm_num) ⟨23463, by rfl⟩ (by norm_num))
theorem R62573 : Reach 62573 := rs (se 3 (by rfl) ⟨11732, by rfl⟩) (B 23465 (by norm_num) ⟨11732, by rfl⟩ (by norm_num))
theorem R62577 : Reach 62577 := rs (se 2 (by rfl) ⟨23466, by rfl⟩) (B 46933 (by norm_num) ⟨23466, by rfl⟩ (by norm_num))
theorem R62581 : Reach 62581 := rs (se 5 (by rfl) ⟨2933, by rfl⟩) (B 5867 (by norm_num) ⟨2933, by rfl⟩ (by norm_num))
theorem R62585 : Reach 62585 := rs (se 2 (by rfl) ⟨23469, by rfl⟩) (B 46939 (by norm_num) ⟨23469, by rfl⟩ (by norm_num))
theorem R62589 : Reach 62589 := rs (se 3 (by rfl) ⟨11735, by rfl⟩) (B 23471 (by norm_num) ⟨11735, by rfl⟩ (by norm_num))
theorem R62593 : Reach 62593 := rs (se 2 (by rfl) ⟨23472, by rfl⟩) (B 46945 (by norm_num) ⟨23472, by rfl⟩ (by norm_num))
theorem R62597 : Reach 62597 := rs (se 4 (by rfl) ⟨5868, by rfl⟩) (B 11737 (by norm_num) ⟨5868, by rfl⟩ (by norm_num))
theorem R62601 : Reach 62601 := rs (se 2 (by rfl) ⟨23475, by rfl⟩) (B 46951 (by norm_num) ⟨23475, by rfl⟩ (by norm_num))
theorem R62605 : Reach 62605 := rs (se 3 (by rfl) ⟨11738, by rfl⟩) (B 23477 (by norm_num) ⟨11738, by rfl⟩ (by norm_num))
theorem R62609 : Reach 62609 := rs (se 2 (by rfl) ⟨23478, by rfl⟩) (B 46957 (by norm_num) ⟨23478, by rfl⟩ (by norm_num))
theorem R62613 : Reach 62613 := rs (se 6 (by rfl) ⟨1467, by rfl⟩) (B 2935 (by norm_num) ⟨1467, by rfl⟩ (by norm_num))
theorem R62617 : Reach 62617 := rs (se 2 (by rfl) ⟨23481, by rfl⟩) (B 46963 (by norm_num) ⟨23481, by rfl⟩ (by norm_num))
theorem R62621 : Reach 62621 := rs (se 3 (by rfl) ⟨11741, by rfl⟩) (B 23483 (by norm_num) ⟨11741, by rfl⟩ (by norm_num))
theorem R62625 : Reach 62625 := rs (se 2 (by rfl) ⟨23484, by rfl⟩) (B 46969 (by norm_num) ⟨23484, by rfl⟩ (by norm_num))
theorem R62629 : Reach 62629 := rs (se 4 (by rfl) ⟨5871, by rfl⟩) (B 11743 (by norm_num) ⟨5871, by rfl⟩ (by norm_num))
theorem R62633 : Reach 62633 := rs (se 2 (by rfl) ⟨23487, by rfl⟩) (B 46975 (by norm_num) ⟨23487, by rfl⟩ (by norm_num))
theorem R62637 : Reach 62637 := rs (se 3 (by rfl) ⟨11744, by rfl⟩) (B 23489 (by norm_num) ⟨11744, by rfl⟩ (by norm_num))
theorem R62641 : Reach 62641 := rs (se 2 (by rfl) ⟨23490, by rfl⟩) (B 46981 (by norm_num) ⟨23490, by rfl⟩ (by norm_num))
theorem R62645 : Reach 62645 := rs (se 5 (by rfl) ⟨2936, by rfl⟩) (B 5873 (by norm_num) ⟨2936, by rfl⟩ (by norm_num))
theorem R62649 : Reach 62649 := rs (se 2 (by rfl) ⟨23493, by rfl⟩) (B 46987 (by norm_num) ⟨23493, by rfl⟩ (by norm_num))
theorem R62653 : Reach 62653 := rs (se 3 (by rfl) ⟨11747, by rfl⟩) (B 23495 (by norm_num) ⟨11747, by rfl⟩ (by norm_num))
theorem R62657 : Reach 62657 := rs (se 2 (by rfl) ⟨23496, by rfl⟩) (B 46993 (by norm_num) ⟨23496, by rfl⟩ (by norm_num))
theorem R62661 : Reach 62661 := rs (se 4 (by rfl) ⟨5874, by rfl⟩) (B 11749 (by norm_num) ⟨5874, by rfl⟩ (by norm_num))
theorem R62665 : Reach 62665 := rs (se 2 (by rfl) ⟨23499, by rfl⟩) (B 46999 (by norm_num) ⟨23499, by rfl⟩ (by norm_num))
theorem R62669 : Reach 62669 := rs (se 3 (by rfl) ⟨11750, by rfl⟩) (B 23501 (by norm_num) ⟨11750, by rfl⟩ (by norm_num))
theorem R62673 : Reach 62673 := rs (se 2 (by rfl) ⟨23502, by rfl⟩) (B 47005 (by norm_num) ⟨23502, by rfl⟩ (by norm_num))
theorem R62677 : Reach 62677 := rs (se 7 (by rfl) ⟨734, by rfl⟩) (B 1469 (by norm_num) ⟨734, by rfl⟩ (by norm_num))
theorem R62681 : Reach 62681 := rs (se 2 (by rfl) ⟨23505, by rfl⟩) (B 47011 (by norm_num) ⟨23505, by rfl⟩ (by norm_num))
theorem R62685 : Reach 62685 := rs (se 3 (by rfl) ⟨11753, by rfl⟩) (B 23507 (by norm_num) ⟨11753, by rfl⟩ (by norm_num))
theorem R62689 : Reach 62689 := rs (se 2 (by rfl) ⟨23508, by rfl⟩) (B 47017 (by norm_num) ⟨23508, by rfl⟩ (by norm_num))
theorem R62693 : Reach 62693 := rs (se 4 (by rfl) ⟨5877, by rfl⟩) (B 11755 (by norm_num) ⟨5877, by rfl⟩ (by norm_num))
theorem R62697 : Reach 62697 := rs (se 2 (by rfl) ⟨23511, by rfl⟩) (B 47023 (by norm_num) ⟨23511, by rfl⟩ (by norm_num))
theorem R62701 : Reach 62701 := rs (se 3 (by rfl) ⟨11756, by rfl⟩) (B 23513 (by norm_num) ⟨11756, by rfl⟩ (by norm_num))
theorem R62705 : Reach 62705 := rs (se 2 (by rfl) ⟨23514, by rfl⟩) (B 47029 (by norm_num) ⟨23514, by rfl⟩ (by norm_num))
theorem R488693 : Reach 488693 := rs (se 5 (by rfl) ⟨22907, by rfl⟩) (B 45815 (by norm_num) ⟨22907, by rfl⟩ (by norm_num))
theorem R62709 : Reach 62709 := rs (se 5 (by rfl) ⟨2939, by rfl⟩) (B 5879 (by norm_num) ⟨2939, by rfl⟩ (by norm_num))
theorem R62713 : Reach 62713 := rs (se 2 (by rfl) ⟨23517, by rfl⟩) (B 47035 (by norm_num) ⟨23517, by rfl⟩ (by norm_num))
theorem R62717 : Reach 62717 := rs (se 3 (by rfl) ⟨11759, by rfl⟩) (B 23519 (by norm_num) ⟨11759, by rfl⟩ (by norm_num))
theorem R62721 : Reach 62721 := rs (se 2 (by rfl) ⟨23520, by rfl⟩) (B 47041 (by norm_num) ⟨23520, by rfl⟩ (by norm_num))
theorem R62725 : Reach 62725 := rs (se 4 (by rfl) ⟨5880, by rfl⟩) (B 11761 (by norm_num) ⟨5880, by rfl⟩ (by norm_num))
theorem R62729 : Reach 62729 := rs (se 2 (by rfl) ⟨23523, by rfl⟩) (B 47047 (by norm_num) ⟨23523, by rfl⟩ (by norm_num))
theorem R62733 : Reach 62733 := rs (se 3 (by rfl) ⟨11762, by rfl⟩) (B 23525 (by norm_num) ⟨11762, by rfl⟩ (by norm_num))
theorem R62737 : Reach 62737 := rs (se 2 (by rfl) ⟨23526, by rfl⟩) (B 47053 (by norm_num) ⟨23526, by rfl⟩ (by norm_num))
theorem R62741 : Reach 62741 := rs (se 6 (by rfl) ⟨1470, by rfl⟩) (B 2941 (by norm_num) ⟨1470, by rfl⟩ (by norm_num))
theorem R62745 : Reach 62745 := rs (se 2 (by rfl) ⟨23529, by rfl⟩) (B 47059 (by norm_num) ⟨23529, by rfl⟩ (by norm_num))
theorem R62749 : Reach 62749 := rs (se 3 (by rfl) ⟨11765, by rfl⟩) (B 23531 (by norm_num) ⟨11765, by rfl⟩ (by norm_num))
theorem R62753 : Reach 62753 := rs (se 2 (by rfl) ⟨23532, by rfl⟩) (B 47065 (by norm_num) ⟨23532, by rfl⟩ (by norm_num))
theorem R226597 : Reach 226597 := rs (se 4 (by rfl) ⟨21243, by rfl⟩) (B 42487 (by norm_num) ⟨21243, by rfl⟩ (by norm_num))
theorem R62757 : Reach 62757 := rs (se 4 (by rfl) ⟨5883, by rfl⟩) (B 11767 (by norm_num) ⟨5883, by rfl⟩ (by norm_num))
theorem R62761 : Reach 62761 := rs (se 2 (by rfl) ⟨23535, by rfl⟩) (B 47071 (by norm_num) ⟨23535, by rfl⟩ (by norm_num))
theorem R62765 : Reach 62765 := rs (se 3 (by rfl) ⟨11768, by rfl⟩) (B 23537 (by norm_num) ⟨11768, by rfl⟩ (by norm_num))
theorem R62769 : Reach 62769 := rs (se 2 (by rfl) ⟨23538, by rfl⟩) (B 47077 (by norm_num) ⟨23538, by rfl⟩ (by norm_num))
theorem R62773 : Reach 62773 := rs (se 5 (by rfl) ⟨2942, by rfl⟩) (B 5885 (by norm_num) ⟨2942, by rfl⟩ (by norm_num))
theorem R62777 : Reach 62777 := rs (se 2 (by rfl) ⟨23541, by rfl⟩) (B 47083 (by norm_num) ⟨23541, by rfl⟩ (by norm_num))
theorem R62781 : Reach 62781 := rs (se 3 (by rfl) ⟨11771, by rfl⟩) (B 23543 (by norm_num) ⟨11771, by rfl⟩ (by norm_num))
theorem R62785 : Reach 62785 := rs (se 2 (by rfl) ⟨23544, by rfl⟩) (B 47089 (by norm_num) ⟨23544, by rfl⟩ (by norm_num))
theorem R62789 : Reach 62789 := rs (se 4 (by rfl) ⟨5886, by rfl⟩) (B 11773 (by norm_num) ⟨5886, by rfl⟩ (by norm_num))
theorem R62793 : Reach 62793 := rs (se 2 (by rfl) ⟨23547, by rfl⟩) (B 47095 (by norm_num) ⟨23547, by rfl⟩ (by norm_num))
theorem R62797 : Reach 62797 := rs (se 3 (by rfl) ⟨11774, by rfl⟩) (B 23549 (by norm_num) ⟨11774, by rfl⟩ (by norm_num))
theorem R62801 : Reach 62801 := rs (se 2 (by rfl) ⟨23550, by rfl⟩) (B 47101 (by norm_num) ⟨23550, by rfl⟩ (by norm_num))
theorem R62805 : Reach 62805 := rs (se 13 (by rfl) ⟨11, by rfl⟩) (B 23 (by norm_num) ⟨11, by rfl⟩ (by norm_num))
theorem R62809 : Reach 62809 := rs (se 2 (by rfl) ⟨23553, by rfl⟩) (B 47107 (by norm_num) ⟨23553, by rfl⟩ (by norm_num))
theorem R62813 : Reach 62813 := rs (se 3 (by rfl) ⟨11777, by rfl⟩) (B 23555 (by norm_num) ⟨11777, by rfl⟩ (by norm_num))
theorem R62817 : Reach 62817 := rs (se 2 (by rfl) ⟨23556, by rfl⟩) (B 47113 (by norm_num) ⟨23556, by rfl⟩ (by norm_num))
theorem R62821 : Reach 62821 := rs (se 4 (by rfl) ⟨5889, by rfl⟩) (B 11779 (by norm_num) ⟨5889, by rfl⟩ (by norm_num))
theorem R62825 : Reach 62825 := rs (se 2 (by rfl) ⟨23559, by rfl⟩) (B 47119 (by norm_num) ⟨23559, by rfl⟩ (by norm_num))
theorem R62829 : Reach 62829 := rs (se 3 (by rfl) ⟨11780, by rfl⟩) (B 23561 (by norm_num) ⟨11780, by rfl⟩ (by norm_num))
theorem R62833 : Reach 62833 := rs (se 2 (by rfl) ⟨23562, by rfl⟩) (B 47125 (by norm_num) ⟨23562, by rfl⟩ (by norm_num))
theorem R193909 : Reach 193909 := rs (se 5 (by rfl) ⟨9089, by rfl⟩) (B 18179 (by norm_num) ⟨9089, by rfl⟩ (by norm_num))
theorem R62837 : Reach 62837 := rs (se 5 (by rfl) ⟨2945, by rfl⟩) (B 5891 (by norm_num) ⟨2945, by rfl⟩ (by norm_num))
theorem R62841 : Reach 62841 := rs (se 2 (by rfl) ⟨23565, by rfl⟩) (B 47131 (by norm_num) ⟨23565, by rfl⟩ (by norm_num))
theorem R62845 : Reach 62845 := rs (se 3 (by rfl) ⟨11783, by rfl⟩) (B 23567 (by norm_num) ⟨11783, by rfl⟩ (by norm_num))
theorem R62849 : Reach 62849 := rs (se 2 (by rfl) ⟨23568, by rfl⟩) (B 47137 (by norm_num) ⟨23568, by rfl⟩ (by norm_num))
theorem R62853 : Reach 62853 := rs (se 4 (by rfl) ⟨5892, by rfl⟩) (B 11785 (by norm_num) ⟨5892, by rfl⟩ (by norm_num))
theorem R62857 : Reach 62857 := rs (se 2 (by rfl) ⟨23571, by rfl⟩) (B 47143 (by norm_num) ⟨23571, by rfl⟩ (by norm_num))
theorem R62861 : Reach 62861 := rs (se 3 (by rfl) ⟨11786, by rfl⟩) (B 23573 (by norm_num) ⟨11786, by rfl⟩ (by norm_num))
theorem R62865 : Reach 62865 := rs (se 2 (by rfl) ⟨23574, by rfl⟩) (B 47149 (by norm_num) ⟨23574, by rfl⟩ (by norm_num))
theorem R62869 : Reach 62869 := rs (se 6 (by rfl) ⟨1473, by rfl⟩) (B 2947 (by norm_num) ⟨1473, by rfl⟩ (by norm_num))
theorem R62873 : Reach 62873 := rs (se 2 (by rfl) ⟨23577, by rfl⟩) (B 47155 (by norm_num) ⟨23577, by rfl⟩ (by norm_num))
theorem R62877 : Reach 62877 := rs (se 3 (by rfl) ⟨11789, by rfl⟩) (B 23579 (by norm_num) ⟨11789, by rfl⟩ (by norm_num))
theorem R62881 : Reach 62881 := rs (se 2 (by rfl) ⟨23580, by rfl⟩) (B 47161 (by norm_num) ⟨23580, by rfl⟩ (by norm_num))
theorem R62885 : Reach 62885 := rs (se 4 (by rfl) ⟨5895, by rfl⟩) (B 11791 (by norm_num) ⟨5895, by rfl⟩ (by norm_num))
theorem R62889 : Reach 62889 := rs (se 2 (by rfl) ⟨23583, by rfl⟩) (B 47167 (by norm_num) ⟨23583, by rfl⟩ (by norm_num))
theorem R62893 : Reach 62893 := rs (se 3 (by rfl) ⟨11792, by rfl⟩) (B 23585 (by norm_num) ⟨11792, by rfl⟩ (by norm_num))
theorem R62897 : Reach 62897 := rs (se 2 (by rfl) ⟨23586, by rfl⟩) (B 47173 (by norm_num) ⟨23586, by rfl⟩ (by norm_num))
theorem R62901 : Reach 62901 := rs (se 5 (by rfl) ⟨2948, by rfl⟩) (B 5897 (by norm_num) ⟨2948, by rfl⟩ (by norm_num))
theorem R62905 : Reach 62905 := rs (se 2 (by rfl) ⟨23589, by rfl⟩) (B 47179 (by norm_num) ⟨23589, by rfl⟩ (by norm_num))
theorem R62909 : Reach 62909 := rs (se 3 (by rfl) ⟨11795, by rfl⟩) (B 23591 (by norm_num) ⟨11795, by rfl⟩ (by norm_num))
theorem R62913 : Reach 62913 := rs (se 2 (by rfl) ⟨23592, by rfl⟩) (B 47185 (by norm_num) ⟨23592, by rfl⟩ (by norm_num))
theorem R62917 : Reach 62917 := rs (se 4 (by rfl) ⟨5898, by rfl⟩) (B 11797 (by norm_num) ⟨5898, by rfl⟩ (by norm_num))
theorem R62921 : Reach 62921 := rs (se 2 (by rfl) ⟨23595, by rfl⟩) (B 47191 (by norm_num) ⟨23595, by rfl⟩ (by norm_num))
theorem R62925 : Reach 62925 := rs (se 3 (by rfl) ⟨11798, by rfl⟩) (B 23597 (by norm_num) ⟨11798, by rfl⟩ (by norm_num))
theorem R62929 : Reach 62929 := rs (se 2 (by rfl) ⟨23598, by rfl⟩) (B 47197 (by norm_num) ⟨23598, by rfl⟩ (by norm_num))
theorem R62933 : Reach 62933 := rs (se 7 (by rfl) ⟨737, by rfl⟩) (B 1475 (by norm_num) ⟨737, by rfl⟩ (by norm_num))
theorem R62937 : Reach 62937 := rs (se 2 (by rfl) ⟨23601, by rfl⟩) (B 47203 (by norm_num) ⟨23601, by rfl⟩ (by norm_num))
theorem R62941 : Reach 62941 := rs (se 3 (by rfl) ⟨11801, by rfl⟩) (B 23603 (by norm_num) ⟨11801, by rfl⟩ (by norm_num))
theorem R62945 : Reach 62945 := rs (se 2 (by rfl) ⟨23604, by rfl⟩) (B 47209 (by norm_num) ⟨23604, by rfl⟩ (by norm_num))
theorem R62949 : Reach 62949 := rs (se 4 (by rfl) ⟨5901, by rfl⟩) (B 11803 (by norm_num) ⟨5901, by rfl⟩ (by norm_num))
theorem R62953 : Reach 62953 := rs (se 2 (by rfl) ⟨23607, by rfl⟩) (B 47215 (by norm_num) ⟨23607, by rfl⟩ (by norm_num))
theorem R62957 : Reach 62957 := rs (se 3 (by rfl) ⟨11804, by rfl⟩) (B 23609 (by norm_num) ⟨11804, by rfl⟩ (by norm_num))
theorem R62961 : Reach 62961 := rs (se 2 (by rfl) ⟨23610, by rfl⟩) (B 47221 (by norm_num) ⟨23610, by rfl⟩ (by norm_num))
theorem R62965 : Reach 62965 := rs (se 5 (by rfl) ⟨2951, by rfl⟩) (B 5903 (by norm_num) ⟨2951, by rfl⟩ (by norm_num))
theorem R62969 : Reach 62969 := rs (se 2 (by rfl) ⟨23613, by rfl⟩) (B 47227 (by norm_num) ⟨23613, by rfl⟩ (by norm_num))
theorem R62973 : Reach 62973 := rs (se 3 (by rfl) ⟨11807, by rfl⟩) (B 23615 (by norm_num) ⟨11807, by rfl⟩ (by norm_num))
theorem R62977 : Reach 62977 := rs (se 2 (by rfl) ⟨23616, by rfl⟩) (B 47233 (by norm_num) ⟨23616, by rfl⟩ (by norm_num))
theorem R62981 : Reach 62981 := rs (se 4 (by rfl) ⟨5904, by rfl⟩) (B 11809 (by norm_num) ⟨5904, by rfl⟩ (by norm_num))
theorem R62985 : Reach 62985 := rs (se 2 (by rfl) ⟨23619, by rfl⟩) (B 47239 (by norm_num) ⟨23619, by rfl⟩ (by norm_num))
theorem R62989 : Reach 62989 := rs (se 3 (by rfl) ⟨11810, by rfl⟩) (B 23621 (by norm_num) ⟨11810, by rfl⟩ (by norm_num))
theorem R62993 : Reach 62993 := rs (se 2 (by rfl) ⟨23622, by rfl⟩) (B 47245 (by norm_num) ⟨23622, by rfl⟩ (by norm_num))
theorem R62997 : Reach 62997 := rs (se 6 (by rfl) ⟨1476, by rfl⟩) (B 2953 (by norm_num) ⟨1476, by rfl⟩ (by norm_num))
theorem R63001 : Reach 63001 := rs (se 2 (by rfl) ⟨23625, by rfl⟩) (B 47251 (by norm_num) ⟨23625, by rfl⟩ (by norm_num))
theorem R63005 : Reach 63005 := rs (se 3 (by rfl) ⟨11813, by rfl⟩) (B 23627 (by norm_num) ⟨11813, by rfl⟩ (by norm_num))
theorem R63009 : Reach 63009 := rs (se 2 (by rfl) ⟨23628, by rfl⟩) (B 47257 (by norm_num) ⟨23628, by rfl⟩ (by norm_num))
theorem R63013 : Reach 63013 := rs (se 4 (by rfl) ⟨5907, by rfl⟩) (B 11815 (by norm_num) ⟨5907, by rfl⟩ (by norm_num))
theorem R63017 : Reach 63017 := rs (se 2 (by rfl) ⟨23631, by rfl⟩) (B 47263 (by norm_num) ⟨23631, by rfl⟩ (by norm_num))
theorem R63021 : Reach 63021 := rs (se 3 (by rfl) ⟨11816, by rfl⟩) (B 23633 (by norm_num) ⟨11816, by rfl⟩ (by norm_num))
theorem R63025 : Reach 63025 := rs (se 2 (by rfl) ⟨23634, by rfl⟩) (B 47269 (by norm_num) ⟨23634, by rfl⟩ (by norm_num))
theorem R63029 : Reach 63029 := rs (se 5 (by rfl) ⟨2954, by rfl⟩) (B 5909 (by norm_num) ⟨2954, by rfl⟩ (by norm_num))
theorem R63033 : Reach 63033 := rs (se 2 (by rfl) ⟨23637, by rfl⟩) (B 47275 (by norm_num) ⟨23637, by rfl⟩ (by norm_num))
theorem R63037 : Reach 63037 := rs (se 3 (by rfl) ⟨11819, by rfl⟩) (B 23639 (by norm_num) ⟨11819, by rfl⟩ (by norm_num))
theorem R63041 : Reach 63041 := rs (se 2 (by rfl) ⟨23640, by rfl⟩) (B 47281 (by norm_num) ⟨23640, by rfl⟩ (by norm_num))
theorem R63045 : Reach 63045 := rs (se 4 (by rfl) ⟨5910, by rfl⟩) (B 11821 (by norm_num) ⟨5910, by rfl⟩ (by norm_num))
theorem R63049 : Reach 63049 := rs (se 2 (by rfl) ⟨23643, by rfl⟩) (B 47287 (by norm_num) ⟨23643, by rfl⟩ (by norm_num))
theorem R63053 : Reach 63053 := rs (se 3 (by rfl) ⟨11822, by rfl⟩) (B 23645 (by norm_num) ⟨11822, by rfl⟩ (by norm_num))
theorem R63057 : Reach 63057 := rs (se 2 (by rfl) ⟨23646, by rfl⟩) (B 47293 (by norm_num) ⟨23646, by rfl⟩ (by norm_num))
theorem R226901 : Reach 226901 := rs (se 8 (by rfl) ⟨1329, by rfl⟩) (B 2659 (by norm_num) ⟨1329, by rfl⟩ (by norm_num))
theorem R63061 : Reach 63061 := rs (se 8 (by rfl) ⟨369, by rfl⟩) (B 739 (by norm_num) ⟨369, by rfl⟩ (by norm_num))
theorem R63065 : Reach 63065 := rs (se 2 (by rfl) ⟨23649, by rfl⟩) (B 47299 (by norm_num) ⟨23649, by rfl⟩ (by norm_num))
theorem R63069 : Reach 63069 := rs (se 3 (by rfl) ⟨11825, by rfl⟩) (B 23651 (by norm_num) ⟨11825, by rfl⟩ (by norm_num))
theorem R63073 : Reach 63073 := rs (se 2 (by rfl) ⟨23652, by rfl⟩) (B 47305 (by norm_num) ⟨23652, by rfl⟩ (by norm_num))
theorem R63077 : Reach 63077 := rs (se 4 (by rfl) ⟨5913, by rfl⟩) (B 11827 (by norm_num) ⟨5913, by rfl⟩ (by norm_num))
theorem R63081 : Reach 63081 := rs (se 2 (by rfl) ⟨23655, by rfl⟩) (B 47311 (by norm_num) ⟨23655, by rfl⟩ (by norm_num))
theorem R63085 : Reach 63085 := rs (se 3 (by rfl) ⟨11828, by rfl⟩) (B 23657 (by norm_num) ⟨11828, by rfl⟩ (by norm_num))
theorem R63089 : Reach 63089 := rs (se 2 (by rfl) ⟨23658, by rfl⟩) (B 47317 (by norm_num) ⟨23658, by rfl⟩ (by norm_num))
theorem R194165 : Reach 194165 := rs (se 5 (by rfl) ⟨9101, by rfl⟩) (B 18203 (by norm_num) ⟨9101, by rfl⟩ (by norm_num))
theorem R63093 : Reach 63093 := rs (se 5 (by rfl) ⟨2957, by rfl⟩) (B 5915 (by norm_num) ⟨2957, by rfl⟩ (by norm_num))
theorem R63097 : Reach 63097 := rs (se 2 (by rfl) ⟨23661, by rfl⟩) (B 47323 (by norm_num) ⟨23661, by rfl⟩ (by norm_num))
theorem R63101 : Reach 63101 := rs (se 3 (by rfl) ⟨11831, by rfl⟩) (B 23663 (by norm_num) ⟨11831, by rfl⟩ (by norm_num))
theorem R63105 : Reach 63105 := rs (se 2 (by rfl) ⟨23664, by rfl⟩) (B 47329 (by norm_num) ⟨23664, by rfl⟩ (by norm_num))
theorem R63109 : Reach 63109 := rs (se 4 (by rfl) ⟨5916, by rfl⟩) (B 11833 (by norm_num) ⟨5916, by rfl⟩ (by norm_num))
theorem R63113 : Reach 63113 := rs (se 2 (by rfl) ⟨23667, by rfl⟩) (B 47335 (by norm_num) ⟨23667, by rfl⟩ (by norm_num))
theorem R63117 : Reach 63117 := rs (se 3 (by rfl) ⟨11834, by rfl⟩) (B 23669 (by norm_num) ⟨11834, by rfl⟩ (by norm_num))
theorem R63121 : Reach 63121 := rs (se 2 (by rfl) ⟨23670, by rfl⟩) (B 47341 (by norm_num) ⟨23670, by rfl⟩ (by norm_num))
theorem R95917 : Reach 95917 := rs (se 3 (by rfl) ⟨17984, by rfl⟩) (B 35969 (by norm_num) ⟨17984, by rfl⟩ (by norm_num))
theorem R587573 : Reach 587573 := rs (se 5 (by rfl) ⟨27542, by rfl⟩) (B 55085 (by norm_num) ⟨27542, by rfl⟩ (by norm_num))
theorem R292709 : Reach 292709 := rs (se 4 (by rfl) ⟨27441, by rfl⟩) (B 54883 (by norm_num) ⟨27441, by rfl⟩ (by norm_num))
theorem R63349 : Reach 63349 := rs (se 5 (by rfl) ⟨2969, by rfl⟩) (B 5939 (by norm_num) ⟨2969, by rfl⟩ (by norm_num))
theorem R63389 : Reach 63389 := rs (se 3 (by rfl) ⟨11885, by rfl⟩) (B 23771 (by norm_num) ⟨11885, by rfl⟩ (by norm_num))
theorem R128965 : Reach 128965 := rs (se 4 (by rfl) ⟨12090, by rfl⟩) (B 24181 (by norm_num) ⟨12090, by rfl⟩ (by norm_num))
theorem R161797 : Reach 161797 := rs (se 4 (by rfl) ⟨15168, by rfl⟩) (B 30337 (by norm_num) ⟨15168, by rfl⟩ (by norm_num))
theorem R260117 : Reach 260117 := rs (se 6 (by rfl) ⟨6096, by rfl⟩) (B 12193 (by norm_num) ⟨6096, by rfl⟩ (by norm_num))
theorem R63833 : Reach 63833 := rs (se 2 (by rfl) ⟨23937, by rfl⟩) (B 47875 (by norm_num) ⟨23937, by rfl⟩ (by norm_num))
theorem R63865 : Reach 63865 := rs (se 2 (by rfl) ⟨23949, by rfl⟩) (B 47899 (by norm_num) ⟨23949, by rfl⟩ (by norm_num))
theorem R64081 : Reach 64081 := rs (se 2 (by rfl) ⟨24030, by rfl⟩) (B 48061 (by norm_num) ⟨24030, by rfl⟩ (by norm_num))
theorem R129853 : Reach 129853 := rs (se 3 (by rfl) ⟨24347, by rfl⟩) (B 48695 (by norm_num) ⟨24347, by rfl⟩ (by norm_num))
theorem R97109 : Reach 97109 := rs (se 9 (by rfl) ⟨284, by rfl⟩) (B 569 (by norm_num) ⟨284, by rfl⟩ (by norm_num))
theorem R64513 : Reach 64513 := rs (se 2 (by rfl) ⟨24192, by rfl⟩) (B 48385 (by norm_num) ⟨24192, by rfl⟩ (by norm_num))
theorem R97301 : Reach 97301 := rs (se 6 (by rfl) ⟨2280, by rfl⟩) (B 4561 (by norm_num) ⟨2280, by rfl⟩ (by norm_num))
theorem R64585 : Reach 64585 := rs (se 2 (by rfl) ⟨24219, by rfl⟩) (B 48439 (by norm_num) ⟨24219, by rfl⟩ (by norm_num))
theorem R457973 : Reach 457973 := rs (se 5 (by rfl) ⟨21467, by rfl⟩) (B 42935 (by norm_num) ⟨21467, by rfl⟩ (by norm_num))
theorem R130349 : Reach 130349 := rs (se 3 (by rfl) ⟨24440, by rfl⟩) (B 48881 (by norm_num) ⟨24440, by rfl⟩ (by norm_num))
theorem R64957 : Reach 64957 := rs (se 3 (by rfl) ⟨12179, by rfl⟩) (B 24359 (by norm_num) ⟨12179, by rfl⟩ (by norm_num))
theorem R65117 : Reach 65117 := rs (se 3 (by rfl) ⟨12209, by rfl⟩) (B 24419 (by norm_num) ⟨12209, by rfl⟩ (by norm_num))
theorem R229013 : Reach 229013 := rs (se 6 (by rfl) ⟨5367, by rfl⟩) (B 10735 (by norm_num) ⟨5367, by rfl⟩ (by norm_num))
theorem R491221 : Reach 491221 := rs (se 7 (by rfl) ⟨5756, by rfl⟩) (B 11513 (by norm_num) ⟨5756, by rfl⟩ (by norm_num))
theorem R261893 : Reach 261893 := rs (se 4 (by rfl) ⟨24552, by rfl⟩) (B 49105 (by norm_num) ⟨24552, by rfl⟩ (by norm_num))
theorem R65333 : Reach 65333 := rs (se 5 (by rfl) ⟨3062, by rfl⟩) (B 6125 (by norm_num) ⟨3062, by rfl⟩ (by norm_num))
theorem R1408853 : Reach 1408853 := rs (se 9 (by rfl) ⟨4127, by rfl⟩) (B 8255 (by norm_num) ⟨4127, by rfl⟩ (by norm_num))
theorem R65405 : Reach 65405 := rs (se 3 (by rfl) ⟨12263, by rfl⟩) (B 24527 (by norm_num) ⟨12263, by rfl⟩ (by norm_num))
theorem R229301 : Reach 229301 := rs (se 5 (by rfl) ⟨10748, by rfl⟩) (B 21497 (by norm_num) ⟨10748, by rfl⟩ (by norm_num))
theorem R196625 : Reach 196625 := rs (se 2 (by rfl) ⟨73734, by rfl⟩) R147469
theorem R360611 : Reach 360611 := rs (se 1 (by rfl) ⟨270458, by rfl⟩) R540917
theorem R1474757 : Reach 1474757 := rs (se 4 (by rfl) ⟨138258, by rfl⟩) R276517
theorem R98723 : Reach 98723 := rs (se 1 (by rfl) ⟨74042, by rfl⟩) R148085
theorem R262577 : Reach 262577 := rs (se 2 (by rfl) ⟨98466, by rfl⟩) R196933
theorem R98851 : Reach 98851 := rs (se 1 (by rfl) ⟨74138, by rfl⟩) R148277
theorem R131665 : Reach 131665 := rs (se 2 (by rfl) ⟨49374, by rfl⟩) R98749
theorem R164771 : Reach 164771 := rs (se 1 (by rfl) ⟨123578, by rfl⟩) R247157
theorem R197549 : Reach 197549 := rs (se 3 (by rfl) ⟨37040, by rfl⟩) R74081
theorem R99281 : Reach 99281 := rs (se 2 (by rfl) ⟨37230, by rfl⟩) R74461
theorem R394253 : Reach 394253 := rs (se 3 (by rfl) ⟨73922, by rfl⟩) R147845
theorem R66595 : Reach 66595 := rs (se 1 (by rfl) ⟨49946, by rfl⟩) R99893
theorem R197741 : Reach 197741 := rs (se 3 (by rfl) ⟨37076, by rfl⟩) R74153
theorem R99505 : Reach 99505 := rs (se 2 (by rfl) ⟨37314, by rfl⟩) R74629
theorem R66739 : Reach 66739 := rs (se 1 (by rfl) ⟨50054, by rfl⟩) R100109
theorem R66755 : Reach 66755 := rs (se 1 (by rfl) ⟨50066, by rfl⟩) R100133
theorem R99569 : Reach 99569 := rs (se 2 (by rfl) ⟨37338, by rfl⟩) R74677
theorem R656693 : Reach 656693 := rs (se 5 (by rfl) ⟨30782, by rfl⟩) R61565
theorem R66883 : Reach 66883 := rs (se 1 (by rfl) ⟨50162, by rfl⟩) R100325
theorem R165187 : Reach 165187 := rs (se 1 (by rfl) ⟨123890, by rfl⟩) R247781
theorem R99697 : Reach 99697 := rs (se 2 (by rfl) ⟨37386, by rfl⟩) R74773
theorem R67027 : Reach 67027 := rs (se 1 (by rfl) ⟨50270, by rfl⟩) R100541
theorem R394723 : Reach 394723 := rs (se 1 (by rfl) ⟨296042, by rfl⟩) R592085
theorem R99859 : Reach 99859 := rs (se 1 (by rfl) ⟨74894, by rfl⟩) R149789
theorem R67171 : Reach 67171 := rs (se 1 (by rfl) ⟨50378, by rfl⟩) R100757
theorem R100001 : Reach 100001 := rs (se 2 (by rfl) ⟨37500, by rfl⟩) R75001
theorem R263843 : Reach 263843 := rs (se 1 (by rfl) ⟨197882, by rfl⟩) R395765
theorem R689905 : Reach 689905 := rs (se 2 (by rfl) ⟨258714, by rfl⟩) R517429
theorem R67315 : Reach 67315 := rs (se 1 (by rfl) ⟨50486, by rfl⟩) R100973
theorem R165635 : Reach 165635 := rs (se 1 (by rfl) ⟨124226, by rfl⟩) R248453
theorem R100129 : Reach 100129 := rs (se 2 (by rfl) ⟨37548, by rfl⟩) R75097
theorem R100163 : Reach 100163 := rs (se 1 (by rfl) ⟨75122, by rfl⟩) R150245
theorem R231245 : Reach 231245 := rs (se 3 (by rfl) ⟨43358, by rfl⟩) R86717
theorem R67459 : Reach 67459 := rs (se 1 (by rfl) ⟨50594, by rfl⟩) R101189
theorem R853901 : Reach 853901 := rs (se 3 (by rfl) ⟨160106, by rfl⟩) R320213
theorem R100291 : Reach 100291 := rs (se 1 (by rfl) ⟨75218, by rfl⟩) R150437
theorem R133073 : Reach 133073 := rs (se 2 (by rfl) ⟨49902, by rfl⟩) R99805
theorem R133091 : Reach 133091 := rs (se 1 (by rfl) ⟨99818, by rfl⟩) R199637
theorem R67603 : Reach 67603 := rs (se 1 (by rfl) ⟨50702, by rfl⟩) R101405
theorem R100433 : Reach 100433 := rs (se 2 (by rfl) ⟨37662, by rfl⟩) R75325
theorem R67747 : Reach 67747 := rs (se 1 (by rfl) ⟨50810, by rfl⟩) R101621
theorem R100561 : Reach 100561 := rs (se 2 (by rfl) ⟨37710, by rfl⟩) R75421
theorem R133361 : Reach 133361 := rs (se 2 (by rfl) ⟨50010, by rfl⟩) R100021
theorem R100595 : Reach 100595 := rs (se 1 (by rfl) ⟨75446, by rfl⟩) R150893
theorem R133379 : Reach 133379 := rs (se 1 (by rfl) ⟨100034, by rfl⟩) R200069
theorem R67891 : Reach 67891 := rs (se 1 (by rfl) ⟨50918, by rfl⟩) R101837
theorem R100723 : Reach 100723 := rs (se 1 (by rfl) ⟨75542, by rfl⟩) R151085
theorem R68035 : Reach 68035 := rs (se 1 (by rfl) ⟨51026, by rfl⟩) R102053
theorem R100865 : Reach 100865 := rs (se 2 (by rfl) ⟨37824, by rfl⟩) R75649
theorem R68099 : Reach 68099 := rs (se 1 (by rfl) ⟨51074, by rfl⟩) R102149
theorem R133649 : Reach 133649 := rs (se 2 (by rfl) ⟨50118, by rfl⟩) R100237
theorem R133667 : Reach 133667 := rs (se 1 (by rfl) ⟨100250, by rfl⟩) R200501
theorem R68179 : Reach 68179 := rs (se 1 (by rfl) ⟨51134, by rfl⟩) R102269
theorem R100993 : Reach 100993 := rs (se 2 (by rfl) ⟨37872, by rfl⟩) R75745
theorem R166531 : Reach 166531 := rs (se 1 (by rfl) ⟨124898, by rfl⟩) R249797
theorem R101027 : Reach 101027 := rs (se 1 (by rfl) ⟨75770, by rfl⟩) R151541
theorem R68323 : Reach 68323 := rs (se 1 (by rfl) ⟨51242, by rfl⟩) R102485
theorem R101155 : Reach 101155 := rs (se 1 (by rfl) ⟨75866, by rfl⟩) R151733
theorem R133937 : Reach 133937 := rs (se 2 (by rfl) ⟨50226, by rfl⟩) R100453
theorem R133955 : Reach 133955 := rs (se 1 (by rfl) ⟨100466, by rfl⟩) R200933
theorem R265037 : Reach 265037 := rs (se 3 (by rfl) ⟨49694, by rfl⟩) R99389
theorem R199523 : Reach 199523 := rs (se 1 (by rfl) ⟨149642, by rfl⟩) R299285
theorem R166769 : Reach 166769 := rs (se 2 (by rfl) ⟨62538, by rfl⟩) R125077
theorem R68467 : Reach 68467 := rs (se 1 (by rfl) ⟨51350, by rfl⟩) R102701
theorem R101297 : Reach 101297 := rs (se 2 (by rfl) ⟨37986, by rfl⟩) R75973
theorem R68531 : Reach 68531 := rs (se 1 (by rfl) ⟨51398, by rfl⟩) R102797
theorem R68611 : Reach 68611 := rs (se 1 (by rfl) ⟨51458, by rfl⟩) R102917
theorem R101425 : Reach 101425 := rs (se 2 (by rfl) ⟨38034, by rfl⟩) R76069
theorem R134225 : Reach 134225 := rs (se 2 (by rfl) ⟨50334, by rfl⟩) R100669
theorem R101459 : Reach 101459 := rs (se 1 (by rfl) ⟨76094, by rfl⟩) R152189
theorem R134243 : Reach 134243 := rs (se 1 (by rfl) ⟨100682, by rfl⟩) R201365
theorem R68755 : Reach 68755 := rs (se 1 (by rfl) ⟨51566, by rfl⟩) R103133
theorem R199853 : Reach 199853 := rs (se 3 (by rfl) ⟨37472, by rfl⟩) R74945
theorem R101587 : Reach 101587 := rs (se 1 (by rfl) ⟨76190, by rfl⟩) R152381
theorem R199907 : Reach 199907 := rs (se 1 (by rfl) ⟨149930, by rfl⟩) R299861
theorem R68899 : Reach 68899 := rs (se 1 (by rfl) ⟨51674, by rfl⟩) R103349
theorem R101729 : Reach 101729 := rs (se 2 (by rfl) ⟨38148, by rfl⟩) R76297
theorem R134513 : Reach 134513 := rs (se 2 (by rfl) ⟨50442, by rfl⟩) R100885
theorem R134531 : Reach 134531 := rs (se 1 (by rfl) ⟨100898, by rfl⟩) R201797
theorem R69043 : Reach 69043 := rs (se 1 (by rfl) ⟨51782, by rfl⟩) R103565
theorem R101857 : Reach 101857 := rs (se 2 (by rfl) ⟨38196, by rfl⟩) R76393
theorem R200177 : Reach 200177 := rs (se 2 (by rfl) ⟨75066, by rfl⟩) R150133
theorem R101891 : Reach 101891 := rs (se 1 (by rfl) ⟨76418, by rfl⟩) R152837
theorem R69187 : Reach 69187 := rs (se 1 (by rfl) ⟨51890, by rfl⟩) R103781
theorem R134723 : Reach 134723 := rs (se 1 (by rfl) ⟨101042, by rfl⟩) R202085
theorem R102019 : Reach 102019 := rs (se 1 (by rfl) ⟨76514, by rfl⟩) R153029
theorem R134801 : Reach 134801 := rs (se 2 (by rfl) ⟨50550, by rfl⟩) R101101
theorem R134819 : Reach 134819 := rs (se 1 (by rfl) ⟨101114, by rfl⟩) R202229
theorem R69331 : Reach 69331 := rs (se 1 (by rfl) ⟨51998, by rfl⟩) R103997
theorem R102161 : Reach 102161 := rs (se 2 (by rfl) ⟨38310, by rfl⟩) R76621
theorem R102227 : Reach 102227 := rs (se 1 (by rfl) ⟨76670, by rfl⟩) R153341
theorem R69475 : Reach 69475 := rs (se 1 (by rfl) ⟨52106, by rfl⟩) R104213
theorem R102289 : Reach 102289 := rs (se 2 (by rfl) ⟨38358, by rfl⟩) R76717
theorem R135089 : Reach 135089 := rs (se 2 (by rfl) ⟨50658, by rfl⟩) R101317
theorem R102323 : Reach 102323 := rs (se 1 (by rfl) ⟨76742, by rfl⟩) R153485
theorem R135107 : Reach 135107 := rs (se 1 (by rfl) ⟨101330, by rfl⟩) R202661
theorem R69619 : Reach 69619 := rs (se 1 (by rfl) ⟨52214, by rfl⟩) R104429
theorem R200717 : Reach 200717 := rs (se 3 (by rfl) ⟨37634, by rfl⟩) R75269
theorem R102451 : Reach 102451 := rs (se 1 (by rfl) ⟨76838, by rfl⟩) R153677
theorem R200771 : Reach 200771 := rs (se 1 (by rfl) ⟨150578, by rfl⟩) R301157
theorem R69763 : Reach 69763 := rs (se 1 (by rfl) ⟨52322, by rfl⟩) R104645
theorem R102593 : Reach 102593 := rs (se 2 (by rfl) ⟨38472, by rfl⟩) R76945
theorem R135377 : Reach 135377 := rs (se 2 (by rfl) ⟨50766, by rfl⟩) R101533
theorem R135395 : Reach 135395 := rs (se 1 (by rfl) ⟨101546, by rfl⟩) R203093
theorem R69907 : Reach 69907 := rs (se 1 (by rfl) ⟨52430, by rfl⟩) R104861
theorem R102721 : Reach 102721 := rs (se 2 (by rfl) ⟨38520, by rfl⟩) R77041
theorem R692549 : Reach 692549 := rs (se 4 (by rfl) ⟨64926, by rfl⟩) R129853
theorem R201041 : Reach 201041 := rs (se 2 (by rfl) ⟨75390, by rfl⟩) R150781
theorem R102755 : Reach 102755 := rs (se 1 (by rfl) ⟨77066, by rfl⟩) R154133
theorem R70051 : Reach 70051 := rs (se 1 (by rfl) ⟨52538, by rfl⟩) R105077
theorem R102883 : Reach 102883 := rs (se 1 (by rfl) ⟨77162, by rfl⟩) R154325
theorem R135665 : Reach 135665 := rs (se 2 (by rfl) ⟨50874, by rfl⟩) R101749
theorem R135683 : Reach 135683 := rs (se 1 (by rfl) ⟨101762, by rfl⟩) R203525
theorem R70195 : Reach 70195 := rs (se 1 (by rfl) ⟨52646, by rfl⟩) R105293
theorem R102979 : Reach 102979 := rs (se 1 (by rfl) ⟨77234, by rfl⟩) R154469
theorem R103025 : Reach 103025 := rs (se 2 (by rfl) ⟨38634, by rfl⟩) R77269
theorem R234161 : Reach 234161 := rs (se 2 (by rfl) ⟨87810, by rfl⟩) R175621
theorem R70339 : Reach 70339 := rs (se 1 (by rfl) ⟨52754, by rfl⟩) R105509
theorem R103153 : Reach 103153 := rs (se 2 (by rfl) ⟨38682, by rfl⟩) R77365
theorem R135953 : Reach 135953 := rs (se 2 (by rfl) ⟨50982, by rfl⟩) R101965
theorem R103187 : Reach 103187 := rs (se 1 (by rfl) ⟨77390, by rfl⟩) R154781
theorem R135971 : Reach 135971 := rs (se 1 (by rfl) ⟨101978, by rfl⟩) R203957
theorem R299825 : Reach 299825 := rs (se 2 (by rfl) ⟨112434, by rfl⟩) R224869
theorem R70483 : Reach 70483 := rs (se 1 (by rfl) ⟨52862, by rfl⟩) R105725
theorem R201581 : Reach 201581 := rs (se 3 (by rfl) ⟨37796, by rfl⟩) R75593
theorem R103315 : Reach 103315 := rs (se 1 (by rfl) ⟨77486, by rfl⟩) R154973
theorem R201635 : Reach 201635 := rs (se 1 (by rfl) ⟨151226, by rfl⟩) R302453
theorem R201649 : Reach 201649 := rs (se 2 (by rfl) ⟨75618, by rfl⟩) R151237
theorem R103393 : Reach 103393 := rs (se 2 (by rfl) ⟨38772, by rfl⟩) R77545
theorem R70627 : Reach 70627 := rs (se 1 (by rfl) ⟨52970, by rfl⟩) R105941
theorem R103457 : Reach 103457 := rs (se 2 (by rfl) ⟨38796, by rfl⟩) R77593
theorem R136241 : Reach 136241 := rs (se 2 (by rfl) ⟨51090, by rfl⟩) R102181
theorem R136259 : Reach 136259 := rs (se 1 (by rfl) ⟨102194, by rfl⟩) R204389
theorem R169037 : Reach 169037 := rs (se 3 (by rfl) ⟨31694, by rfl⟩) R63389
theorem R70771 : Reach 70771 := rs (se 1 (by rfl) ⟨53078, by rfl⟩) R106157
theorem R103585 : Reach 103585 := rs (se 2 (by rfl) ⟨38844, by rfl⟩) R77689
theorem R201905 : Reach 201905 := rs (se 2 (by rfl) ⟨75714, by rfl⟩) R151429
theorem R103619 : Reach 103619 := rs (se 1 (by rfl) ⟨77714, by rfl⟩) R155429
theorem R169219 : Reach 169219 := rs (se 1 (by rfl) ⟨126914, by rfl⟩) R253829
theorem R70915 : Reach 70915 := rs (se 1 (by rfl) ⟨53186, by rfl⟩) R106373
theorem R267533 : Reach 267533 := rs (se 3 (by rfl) ⟨50162, by rfl⟩) R100325
theorem R169265 : Reach 169265 := rs (se 2 (by rfl) ⟨63474, by rfl⟩) R126949
theorem R103747 : Reach 103747 := rs (se 1 (by rfl) ⟨77810, by rfl⟩) R155621
theorem R136529 : Reach 136529 := rs (se 2 (by rfl) ⟨51198, by rfl⟩) R102397
theorem R136547 : Reach 136547 := rs (se 1 (by rfl) ⟨102410, by rfl⟩) R204821
theorem R103889 : Reach 103889 := rs (se 2 (by rfl) ⟨38958, by rfl⟩) R77917
theorem R71155 : Reach 71155 := rs (se 1 (by rfl) ⟨53366, by rfl⟩) R106733
theorem R104017 : Reach 104017 := rs (se 2 (by rfl) ⟨39006, by rfl⟩) R78013
theorem R136817 : Reach 136817 := rs (se 2 (by rfl) ⟨51306, by rfl⟩) R102613
theorem R104051 : Reach 104051 := rs (se 1 (by rfl) ⟨78038, by rfl⟩) R156077
theorem R136835 : Reach 136835 := rs (se 1 (by rfl) ⟨102626, by rfl⟩) R205253
theorem R366277 : Reach 366277 := rs (se 4 (by rfl) ⟨34338, by rfl⟩) R68677
theorem R202445 : Reach 202445 := rs (se 3 (by rfl) ⟨37958, by rfl⟩) R75917
theorem R104179 : Reach 104179 := rs (se 1 (by rfl) ⟨78134, by rfl⟩) R156269
theorem R202499 : Reach 202499 := rs (se 1 (by rfl) ⟨151874, by rfl⟩) R303749
theorem R104321 : Reach 104321 := rs (se 2 (by rfl) ⟨39120, by rfl⟩) R78241
theorem R137105 : Reach 137105 := rs (se 2 (by rfl) ⟨51414, by rfl⟩) R102829
theorem R137123 : Reach 137123 := rs (se 1 (by rfl) ⟨102842, by rfl⟩) R205685
theorem R104449 : Reach 104449 := rs (se 2 (by rfl) ⟨39168, by rfl⟩) R78337
theorem R202769 : Reach 202769 := rs (se 2 (by rfl) ⟨76038, by rfl⟩) R152077
theorem R104483 : Reach 104483 := rs (se 1 (by rfl) ⟨78362, by rfl⟩) R156725
theorem R235619 : Reach 235619 := rs (se 1 (by rfl) ⟨176714, by rfl⟩) R353429
theorem R104611 : Reach 104611 := rs (se 1 (by rfl) ⟨78458, by rfl⟩) R156917
theorem R268451 : Reach 268451 := rs (se 1 (by rfl) ⟨201338, by rfl⟩) R402677
theorem R137393 : Reach 137393 := rs (se 2 (by rfl) ⟨51522, by rfl⟩) R103045
theorem R137411 : Reach 137411 := rs (se 1 (by rfl) ⟨103058, by rfl⟩) R206117
theorem R301283 : Reach 301283 := rs (se 1 (by rfl) ⟨225962, by rfl⟩) R451925
theorem R104753 : Reach 104753 := rs (se 2 (by rfl) ⟨39282, by rfl⟩) R78565
theorem R104851 : Reach 104851 := rs (se 1 (by rfl) ⟨78638, by rfl⟩) R157277
theorem R104881 : Reach 104881 := rs (se 2 (by rfl) ⟨39330, by rfl⟩) R78661
theorem R137681 : Reach 137681 := rs (se 2 (by rfl) ⟨51630, by rfl⟩) R103261
theorem R104915 : Reach 104915 := rs (se 1 (by rfl) ⟨78686, by rfl⟩) R157373
theorem R137699 : Reach 137699 := rs (se 1 (by rfl) ⟨103274, by rfl⟩) R206549
theorem R203309 : Reach 203309 := rs (se 3 (by rfl) ⟨38120, by rfl⟩) R76241
theorem R105043 : Reach 105043 := rs (se 1 (by rfl) ⟨78782, by rfl⟩) R157565
theorem R203363 : Reach 203363 := rs (se 1 (by rfl) ⟨152522, by rfl⟩) R305045
theorem R301745 : Reach 301745 := rs (se 2 (by rfl) ⟨113154, by rfl⟩) R226309
theorem R170723 : Reach 170723 := rs (se 1 (by rfl) ⟨128042, by rfl⟩) R256085
theorem R137969 : Reach 137969 := rs (se 2 (by rfl) ⟨51738, by rfl⟩) R103477
theorem R137987 : Reach 137987 := rs (se 1 (by rfl) ⟨103490, by rfl⟩) R206981
theorem R465763 : Reach 465763 := rs (se 1 (by rfl) ⟨349322, by rfl⟩) R698645
theorem R138083 : Reach 138083 := rs (se 1 (by rfl) ⟨103562, by rfl⟩) R207125
theorem R203633 : Reach 203633 := rs (se 2 (by rfl) ⟨76362, by rfl⟩) R152725
theorem R105347 : Reach 105347 := rs (se 1 (by rfl) ⟨79010, by rfl⟩) R158021
theorem R105475 : Reach 105475 := rs (se 1 (by rfl) ⟨79106, by rfl⟩) R158213
theorem R138257 : Reach 138257 := rs (se 2 (by rfl) ⟨51846, by rfl⟩) R103693
theorem R138275 : Reach 138275 := rs (se 1 (by rfl) ⟨103706, by rfl⟩) R207413
theorem R269347 : Reach 269347 := rs (se 1 (by rfl) ⟨202010, by rfl⟩) R404021
theorem R302129 : Reach 302129 := rs (se 2 (by rfl) ⟨113298, by rfl⟩) R226597
theorem R236621 : Reach 236621 := rs (se 3 (by rfl) ⟨44366, by rfl⟩) R88733
theorem R302221 : Reach 302221 := rs (se 3 (by rfl) ⟨56666, by rfl⟩) R113333
theorem R105617 : Reach 105617 := rs (se 2 (by rfl) ⟨39606, by rfl⟩) R79213
theorem R531683 : Reach 531683 := rs (se 1 (by rfl) ⟨398762, by rfl⟩) R797525
theorem R72947 : Reach 72947 := rs (se 1 (by rfl) ⟨54710, by rfl⟩) R109421
theorem R105745 : Reach 105745 := rs (se 2 (by rfl) ⟨39654, by rfl⟩) R79309
theorem R138545 : Reach 138545 := rs (se 2 (by rfl) ⟨51954, by rfl⟩) R103909
theorem R138563 : Reach 138563 := rs (se 1 (by rfl) ⟨103922, by rfl⟩) R207845
theorem R204173 : Reach 204173 := rs (se 3 (by rfl) ⟨38282, by rfl⟩) R76565
theorem R204227 : Reach 204227 := rs (se 1 (by rfl) ⟨153170, by rfl⟩) R306341
theorem R368077 : Reach 368077 := rs (se 3 (by rfl) ⟨69014, by rfl⟩) R138029
theorem R73235 : Reach 73235 := rs (se 1 (by rfl) ⟨54926, by rfl⟩) R109853
theorem R269873 : Reach 269873 := rs (se 2 (by rfl) ⟨101202, by rfl⟩) R202405
theorem R138833 : Reach 138833 := rs (se 2 (by rfl) ⟨52062, by rfl⟩) R104125
theorem R138851 : Reach 138851 := rs (se 1 (by rfl) ⟨104138, by rfl⟩) R208277
theorem R204497 : Reach 204497 := rs (se 2 (by rfl) ⟨76686, by rfl⟩) R153373
theorem R73427 : Reach 73427 := rs (se 1 (by rfl) ⟨55070, by rfl⟩) R110141
theorem R106211 : Reach 106211 := rs (se 1 (by rfl) ⟨79658, by rfl⟩) R159317
theorem R106339 : Reach 106339 := rs (se 1 (by rfl) ⟨79754, by rfl⟩) R159509
theorem R139121 : Reach 139121 := rs (se 2 (by rfl) ⟨52170, by rfl⟩) R104341
theorem R139139 : Reach 139139 := rs (se 1 (by rfl) ⟨104354, by rfl⟩) R208709
theorem R171953 : Reach 171953 := rs (se 2 (by rfl) ⟨64482, by rfl⟩) R128965
theorem R106481 : Reach 106481 := rs (se 2 (by rfl) ⟨39930, by rfl⟩) R79861
theorem R139409 : Reach 139409 := rs (se 2 (by rfl) ⟨52278, by rfl⟩) R104557
theorem R139427 : Reach 139427 := rs (se 1 (by rfl) ⟨104570, by rfl⟩) R209141
theorem R205037 : Reach 205037 := rs (se 3 (by rfl) ⟨38444, by rfl⟩) R76889
theorem R205091 : Reach 205091 := rs (se 1 (by rfl) ⟨153818, by rfl⟩) R307637
theorem R139619 : Reach 139619 := rs (se 1 (by rfl) ⟨104714, by rfl⟩) R209429
theorem R139697 : Reach 139697 := rs (se 2 (by rfl) ⟨52386, by rfl⟩) R104773
theorem R139715 : Reach 139715 := rs (se 1 (by rfl) ⟨104786, by rfl⟩) R209573
theorem R401861 : Reach 401861 := rs (se 4 (by rfl) ⟨37674, by rfl⟩) R75349
theorem R303587 : Reach 303587 := rs (se 1 (by rfl) ⟨227690, by rfl⟩) R455381
theorem R205361 : Reach 205361 := rs (se 2 (by rfl) ⟨77010, by rfl⟩) R154021
theorem R139985 : Reach 139985 := rs (se 2 (by rfl) ⟨52494, by rfl⟩) R104989
theorem R140003 : Reach 140003 := rs (se 1 (by rfl) ⟨105002, by rfl⟩) R210005
theorem R140273 : Reach 140273 := rs (se 2 (by rfl) ⟨52602, by rfl⟩) R105205
theorem R140291 : Reach 140291 := rs (se 1 (by rfl) ⟨105218, by rfl⟩) R210437
theorem R205901 : Reach 205901 := rs (se 3 (by rfl) ⟨38606, by rfl⟩) R77213
theorem R205955 : Reach 205955 := rs (se 1 (by rfl) ⟨154466, by rfl⟩) R308933
theorem R238733 : Reach 238733 := rs (se 3 (by rfl) ⟨44762, by rfl⟩) R89525
theorem R304397 : Reach 304397 := rs (se 3 (by rfl) ⟨57074, by rfl⟩) R114149
theorem R140561 : Reach 140561 := rs (se 2 (by rfl) ⟨52710, by rfl⟩) R105421
theorem R140579 : Reach 140579 := rs (se 1 (by rfl) ⟨105434, by rfl⟩) R210869
theorem R75107 : Reach 75107 := rs (se 1 (by rfl) ⟨56330, by rfl⟩) R112661
theorem R173411 : Reach 173411 := rs (se 1 (by rfl) ⟨130058, by rfl⟩) R260117
theorem R107921 : Reach 107921 := rs (se 2 (by rfl) ⟨40470, by rfl⟩) R80941
theorem R206225 : Reach 206225 := rs (se 2 (by rfl) ⟨77334, by rfl⟩) R154669
theorem R140849 : Reach 140849 := rs (se 2 (by rfl) ⟨52818, by rfl⟩) R105637
theorem R140867 : Reach 140867 := rs (se 1 (by rfl) ⟨105650, by rfl⟩) R211301
theorem R173645 : Reach 173645 := rs (se 3 (by rfl) ⟨32558, by rfl⟩) R65117
theorem R763505 : Reach 763505 := rs (se 2 (by rfl) ⟨286314, by rfl⟩) R572629
theorem R141137 : Reach 141137 := rs (se 2 (by rfl) ⟨52926, by rfl⟩) R105853
theorem R141155 : Reach 141155 := rs (se 1 (by rfl) ⟨105866, by rfl⟩) R211733
theorem R206765 : Reach 206765 := rs (se 3 (by rfl) ⟨38768, by rfl⟩) R77537
theorem R337841 : Reach 337841 := rs (se 2 (by rfl) ⟨126690, by rfl⟩) R253381
theorem R239537 : Reach 239537 := rs (se 2 (by rfl) ⟨89826, by rfl⟩) R179653
theorem R337861 : Reach 337861 := rs (se 4 (by rfl) ⟨31674, by rfl⟩) R63349
theorem R206797 : Reach 206797 := rs (se 3 (by rfl) ⟨38774, by rfl⟩) R77549
theorem R206819 : Reach 206819 := rs (se 1 (by rfl) ⟨155114, by rfl⟩) R310229
theorem R337891 : Reach 337891 := rs (se 1 (by rfl) ⟨253418, by rfl⟩) R506837
theorem R698381 : Reach 698381 := rs (se 3 (by rfl) ⟨130946, by rfl⟩) R261893
theorem R75811 : Reach 75811 := rs (se 1 (by rfl) ⟨56858, by rfl⟩) R113717
theorem R141425 : Reach 141425 := rs (se 2 (by rfl) ⟨53034, by rfl⟩) R106069
theorem R75907 : Reach 75907 := rs (se 1 (by rfl) ⟨56930, by rfl⟩) R113861
theorem R141443 : Reach 141443 := rs (se 1 (by rfl) ⟨106082, by rfl⟩) R212165
theorem R174221 : Reach 174221 := rs (se 3 (by rfl) ⟨32666, by rfl⟩) R65333
theorem R305315 : Reach 305315 := rs (se 1 (by rfl) ⟨228986, by rfl⟩) R457973
theorem R207089 : Reach 207089 := rs (se 2 (by rfl) ⟨77658, by rfl⟩) R155317
theorem R174413 : Reach 174413 := rs (se 3 (by rfl) ⟨32702, by rfl⟩) R65405
theorem R403811 : Reach 403811 := rs (se 1 (by rfl) ⟨302858, by rfl⟩) R605717
theorem R895373 : Reach 895373 := rs (se 3 (by rfl) ⟨167882, by rfl⟩) R335765
theorem R141713 : Reach 141713 := rs (se 2 (by rfl) ⟨53142, by rfl⟩) R106285
theorem R141731 : Reach 141731 := rs (se 1 (by rfl) ⟨106298, by rfl⟩) R212597
theorem R469475 : Reach 469475 := rs (se 1 (by rfl) ⟨352106, by rfl⟩) R704213
theorem R338417 : Reach 338417 := rs (se 2 (by rfl) ⟨126906, by rfl⟩) R253813
theorem R76403 : Reach 76403 := rs (se 1 (by rfl) ⟨57302, by rfl⟩) R114605
theorem R142001 : Reach 142001 := rs (se 2 (by rfl) ⟨53250, by rfl⟩) R106501
theorem R142019 : Reach 142019 := rs (se 1 (by rfl) ⟨106514, by rfl⟩) R213029
theorem R207629 : Reach 207629 := rs (se 3 (by rfl) ⟨38930, by rfl⟩) R77861
theorem R207683 : Reach 207683 := rs (se 1 (by rfl) ⟨155762, by rfl⟩) R311525
theorem R207953 : Reach 207953 := rs (se 2 (by rfl) ⟨77982, by rfl⟩) R155965
theorem R175405 : Reach 175405 := rs (se 3 (by rfl) ⟨32888, by rfl⟩) R65777
theorem R77107 : Reach 77107 := rs (se 1 (by rfl) ⟨57830, by rfl⟩) R115661
theorem R77203 : Reach 77203 := rs (se 1 (by rfl) ⟨57902, by rfl⟩) R115805
theorem R110083 : Reach 110083 := rs (se 1 (by rfl) ⟨82562, by rfl⟩) R165125
theorem R208493 : Reach 208493 := rs (se 3 (by rfl) ⟨39092, by rfl⟩) R78185
theorem R241265 : Reach 241265 := rs (se 2 (by rfl) ⟨90474, by rfl⟩) R180949
theorem R208547 : Reach 208547 := rs (se 1 (by rfl) ⟨156410, by rfl⟩) R312821
theorem R143153 : Reach 143153 := rs (se 2 (by rfl) ⟨53682, by rfl⟩) R107365
theorem R143203 : Reach 143203 := rs (se 1 (by rfl) ⟨107402, by rfl⟩) R214805
theorem R77699 : Reach 77699 := rs (se 1 (by rfl) ⟨58274, by rfl⟩) R116549
theorem R339875 : Reach 339875 := rs (se 1 (by rfl) ⟨254906, by rfl⟩) R509813
theorem R208817 : Reach 208817 := rs (se 2 (by rfl) ⟨78306, by rfl⟩) R156613
theorem R307313 : Reach 307313 := rs (se 2 (by rfl) ⟨115242, by rfl⟩) R230485
theorem R209357 : Reach 209357 := rs (se 3 (by rfl) ⟨39254, by rfl⟩) R78509
theorem R111089 : Reach 111089 := rs (se 2 (by rfl) ⟨41658, by rfl⟩) R83317
theorem R209411 : Reach 209411 := rs (se 1 (by rfl) ⟨157058, by rfl⟩) R314117
theorem R78403 : Reach 78403 := rs (se 1 (by rfl) ⟨58802, by rfl⟩) R117605
theorem R78499 : Reach 78499 := rs (se 1 (by rfl) ⟨58874, by rfl⟩) R117749
theorem R209681 : Reach 209681 := rs (se 2 (by rfl) ⟨78630, by rfl⟩) R157261
theorem R701297 : Reach 701297 := rs (se 2 (by rfl) ⟨262986, by rfl⟩) R525973
theorem R144337 : Reach 144337 := rs (se 2 (by rfl) ⟨54126, by rfl⟩) R108253
theorem R177137 : Reach 177137 := rs (se 2 (by rfl) ⟨66426, by rfl⟩) R132853
theorem R78833 : Reach 78833 := rs (se 2 (by rfl) ⟨29562, by rfl⟩) R59125
theorem R144433 : Reach 144433 := rs (se 2 (by rfl) ⟨54162, by rfl⟩) R108325
theorem R177265 : Reach 177265 := rs (se 2 (by rfl) ⟨66474, by rfl⟩) R132949
theorem R78995 : Reach 78995 := rs (se 1 (by rfl) ⟨59246, by rfl⟩) R118493
theorem R144547 : Reach 144547 := rs (se 1 (by rfl) ⟨108410, by rfl⟩) R216821
theorem R177329 : Reach 177329 := rs (se 2 (by rfl) ⟨66498, by rfl⟩) R132997
theorem R144625 : Reach 144625 := rs (se 2 (by rfl) ⟨54234, by rfl⟩) R108469
theorem R210275 : Reach 210275 := rs (se 1 (by rfl) ⟨157706, by rfl⟩) R315413
theorem R210289 : Reach 210289 := rs (se 2 (by rfl) ⟨78858, by rfl⟩) R157717
theorem R308771 : Reach 308771 := rs (se 1 (by rfl) ⟨231578, by rfl⟩) R463157
theorem R374341 : Reach 374341 := rs (se 4 (by rfl) ⟨35094, by rfl⟩) R70189
theorem R210545 : Reach 210545 := rs (se 2 (by rfl) ⟨78954, by rfl⟩) R157909
theorem R112259 : Reach 112259 := rs (se 1 (by rfl) ⟨84194, by rfl⟩) R168389
theorem R79537 : Reach 79537 := rs (se 2 (by rfl) ⟨29826, by rfl⟩) R59653
theorem R341765 : Reach 341765 := rs (se 4 (by rfl) ⟨32040, by rfl⟩) R64081
theorem R79633 : Reach 79633 := rs (se 2 (by rfl) ⟨29862, by rfl⟩) R59725
theorem R79699 : Reach 79699 := rs (se 1 (by rfl) ⟨59774, by rfl⟩) R119549
theorem R145297 : Reach 145297 := rs (se 2 (by rfl) ⟨54486, by rfl⟩) R108973
theorem R79795 : Reach 79795 := rs (se 1 (by rfl) ⟨59846, by rfl⟩) R119693
theorem R669667 : Reach 669667 := rs (se 1 (by rfl) ⟨502250, by rfl⟩) R1004501
theorem R211085 : Reach 211085 := rs (se 3 (by rfl) ⟨39578, by rfl⟩) R79157
theorem R178321 : Reach 178321 := rs (se 2 (by rfl) ⟨66870, by rfl⟩) R133741
theorem R309581 : Reach 309581 := rs (se 3 (by rfl) ⟨58046, by rfl⟩) R116093
theorem R178595 : Reach 178595 := rs (se 1 (by rfl) ⟨133946, by rfl⟩) R267893
theorem R178787 : Reach 178787 := rs (se 1 (by rfl) ⟨134090, by rfl⟩) R268181
theorem R113329 : Reach 113329 := rs (se 2 (by rfl) ⟨42498, by rfl⟩) R84997
theorem R80833 : Reach 80833 := rs (se 2 (by rfl) ⟨30312, by rfl⟩) R60625
theorem R179185 : Reach 179185 := rs (se 2 (by rfl) ⟨67194, by rfl⟩) R134389
theorem R212003 : Reach 212003 := rs (se 1 (by rfl) ⟨159002, by rfl⟩) R318005
theorem R965773 : Reach 965773 := rs (se 3 (by rfl) ⟨181082, by rfl⟩) R362165
theorem R212273 : Reach 212273 := rs (se 2 (by rfl) ⟨79602, by rfl⟩) R159205
theorem R179597 : Reach 179597 := rs (se 3 (by rfl) ⟨33674, by rfl⟩) R67349
theorem R507377 : Reach 507377 := rs (se 2 (by rfl) ⟨190266, by rfl⟩) R380533
theorem R376397 : Reach 376397 := rs (se 3 (by rfl) ⟨70574, by rfl⟩) R141149
theorem R114353 : Reach 114353 := rs (se 2 (by rfl) ⟨42882, by rfl⟩) R85765
theorem R474821 : Reach 474821 := rs (se 4 (by rfl) ⟨44514, by rfl⟩) R89029
theorem R114385 : Reach 114385 := rs (se 2 (by rfl) ⟨42894, by rfl⟩) R85789
theorem R212813 : Reach 212813 := rs (se 3 (by rfl) ⟨39902, by rfl⟩) R79805
theorem R2015117 : Reach 2015117 := rs (se 3 (by rfl) ⟨377834, by rfl⟩) R755669
theorem R114787 : Reach 114787 := rs (se 1 (by rfl) ⟨86090, by rfl⟩) R172181
theorem R114833 : Reach 114833 := rs (se 2 (by rfl) ⟨43062, by rfl⟩) R86125
theorem R245987 : Reach 245987 := rs (se 1 (by rfl) ⟨184490, by rfl⟩) R368981
theorem R409841 : Reach 409841 := rs (se 2 (by rfl) ⟨153690, by rfl⟩) R307381
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R246115 : Reach 246115 := rs (se 1 (by rfl) ⟨184586, by rfl⟩) R369173
theorem R115121 : Reach 115121 := rs (se 2 (by rfl) ⟨43170, by rfl⟩) R86341
theorem R573965 : Reach 573965 := rs (se 3 (by rfl) ⟨107618, by rfl⟩) R215237
theorem R705293 : Reach 705293 := rs (se 3 (by rfl) ⟨132242, by rfl⟩) R264485
theorem R115523 : Reach 115523 := rs (se 1 (by rfl) ⟨86642, by rfl⟩) R173285
theorem R148355 : Reach 148355 := rs (se 1 (by rfl) ⟨111266, by rfl⟩) R222533
theorem R115843 : Reach 115843 := rs (se 1 (by rfl) ⟨86882, by rfl⟩) R173765
theorem R83089 : Reach 83089 := rs (se 2 (by rfl) ⟨31158, by rfl⟩) R62317
theorem R312497 : Reach 312497 := rs (se 2 (by rfl) ⟨117186, by rfl⟩) R234373
theorem R214285 : Reach 214285 := rs (se 3 (by rfl) ⟨40178, by rfl⟩) R80357
theorem R378245 : Reach 378245 := rs (se 4 (by rfl) ⟨35460, by rfl⟩) R70921
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) R68117
theorem R148931 : Reach 148931 := rs (se 1 (by rfl) ⟨111698, by rfl⟩) R223397
theorem R509453 : Reach 509453 := rs (se 3 (by rfl) ⟨95522, by rfl⟩) R191045
theorem R116291 : Reach 116291 := rs (se 1 (by rfl) ⟨87218, by rfl⟩) R174437
theorem R149123 : Reach 149123 := rs (se 1 (by rfl) ⟨111842, by rfl⟩) R223685
theorem R476869 : Reach 476869 := rs (se 4 (by rfl) ⟨44706, by rfl⟩) R89413
theorem R116579 : Reach 116579 := rs (se 1 (by rfl) ⟨87434, by rfl⟩) R174869
theorem R149411 : Reach 149411 := rs (se 1 (by rfl) ⟨112058, by rfl⟩) R224117
theorem R673733 : Reach 673733 := rs (se 4 (by rfl) ⟨63162, by rfl⟩) R126325
theorem R215117 : Reach 215117 := rs (se 3 (by rfl) ⟨40334, by rfl⟩) R80669
theorem R149809 : Reach 149809 := rs (se 2 (by rfl) ⟨56178, by rfl⟩) R112357
theorem R150083 : Reach 150083 := rs (se 1 (by rfl) ⟨112562, by rfl⟩) R225125
theorem R84547 : Reach 84547 := rs (se 1 (by rfl) ⟨63410, by rfl⟩) R126821
theorem R313955 : Reach 313955 := rs (se 1 (by rfl) ⟨235466, by rfl⟩) R470933
theorem R84595 : Reach 84595 := rs (se 1 (by rfl) ⟨63446, by rfl⟩) R126893
theorem R215729 : Reach 215729 := rs (se 2 (by rfl) ⟨80898, by rfl⟩) R161797
theorem R150275 : Reach 150275 := rs (se 1 (by rfl) ⟨112706, by rfl⟩) R225413
theorem R117521 : Reach 117521 := rs (se 2 (by rfl) ⟨44070, by rfl⟩) R88141
theorem R150353 : Reach 150353 := rs (se 2 (by rfl) ⟨56382, by rfl⟩) R112765
theorem R84883 : Reach 84883 := rs (se 1 (by rfl) ⟨63662, by rfl⟩) R127325
theorem R510947 : Reach 510947 := rs (se 1 (by rfl) ⟨383210, by rfl⟩) R766421
theorem R248845 : Reach 248845 := rs (se 3 (by rfl) ⟨46658, by rfl⟩) R93317
theorem R150545 : Reach 150545 := rs (se 2 (by rfl) ⟨56454, by rfl⟩) R112909
theorem R281713 : Reach 281713 := rs (se 2 (by rfl) ⟨105642, by rfl⟩) R211285
theorem R85153 : Reach 85153 := rs (se 2 (by rfl) ⟨31932, by rfl⟩) R63865
theorem R544013 : Reach 544013 := rs (se 3 (by rfl) ⟨102002, by rfl⟩) R204005
theorem R314765 : Reach 314765 := rs (se 3 (by rfl) ⟨59018, by rfl⟩) R118037
theorem R249293 : Reach 249293 := rs (se 3 (by rfl) ⟨46742, by rfl⟩) R93485
theorem R347597 : Reach 347597 := rs (se 3 (by rfl) ⟨65174, by rfl⟩) R130349
theorem R118417 : Reach 118417 := rs (se 2 (by rfl) ⟨44406, by rfl⟩) R88813
theorem R151217 : Reach 151217 := rs (se 2 (by rfl) ⟨56706, by rfl⟩) R113413
theorem R151267 : Reach 151267 := rs (se 1 (by rfl) ⟨113450, by rfl⟩) R226901
theorem R151313 : Reach 151313 := rs (se 2 (by rfl) ⟨56742, by rfl⟩) R113485
theorem R118577 : Reach 118577 := rs (se 2 (by rfl) ⟨44466, by rfl⟩) R88933
theorem R151409 : Reach 151409 := rs (se 2 (by rfl) ⟨56778, by rfl⟩) R113557
theorem R86017 : Reach 86017 := rs (se 2 (by rfl) ⟨32256, by rfl⟩) R64513
theorem R86113 : Reach 86113 := rs (se 2 (by rfl) ⟨32292, by rfl⟩) R64585
theorem R118979 : Reach 118979 := rs (se 1 (by rfl) ⟨89234, by rfl⟩) R178469
theorem R86609 : Reach 86609 := rs (se 2 (by rfl) ⟨32478, by rfl⟩) R64957
theorem R381617 : Reach 381617 := rs (se 2 (by rfl) ⟨143106, by rfl⟩) R286213
theorem R119587 : Reach 119587 := rs (se 1 (by rfl) ⟨89690, by rfl⟩) R179381
theorem R152401 : Reach 152401 := rs (se 2 (by rfl) ⟨57150, by rfl⟩) R114301
theorem R152675 : Reach 152675 := rs (se 1 (by rfl) ⟨114506, by rfl⟩) R229013
theorem R382157 : Reach 382157 := rs (se 3 (by rfl) ⟨71654, by rfl⟩) R143309
theorem R120035 : Reach 120035 := rs (se 1 (by rfl) ⟨90026, by rfl⟩) R180053
theorem R939235 : Reach 939235 := rs (se 1 (by rfl) ⟨704426, by rfl⟩) R1408853
theorem R677105 : Reach 677105 := rs (se 2 (by rfl) ⟨253914, by rfl⟩) R507829
theorem R152867 : Reach 152867 := rs (se 1 (by rfl) ⟨114650, by rfl⟩) R229301
theorem R87475 : Reach 87475 := rs (se 1 (by rfl) ⟨65606, by rfl⟩) R131213
theorem R87571 : Reach 87571 := rs (se 1 (by rfl) ⟨65678, by rfl⟩) R131357
theorem R349829 : Reach 349829 := rs (se 4 (by rfl) ⟨32796, by rfl⟩) R65593
theorem R120593 : Reach 120593 := rs (se 2 (by rfl) ⟨45222, by rfl⟩) R90445
theorem R88067 : Reach 88067 := rs (se 1 (by rfl) ⟨66050, by rfl⟩) R132101
theorem R1136693 : Reach 1136693 := rs (se 5 (by rfl) ⟨53282, by rfl⟩) R106565
theorem R186545 : Reach 186545 := rs (se 2 (by rfl) ⟨69954, by rfl⟩) R139909
theorem R153809 : Reach 153809 := rs (se 2 (by rfl) ⟨57678, by rfl⟩) R115357
theorem R317681 : Reach 317681 := rs (se 2 (by rfl) ⟨119130, by rfl⟩) R238261
theorem R153859 : Reach 153859 := rs (se 1 (by rfl) ⟨115394, by rfl⟩) R230789
theorem R350513 : Reach 350513 := rs (se 2 (by rfl) ⟨131442, by rfl⟩) R262885
theorem R154001 : Reach 154001 := rs (se 2 (by rfl) ⟨57750, by rfl⟩) R115501
theorem R88691 : Reach 88691 := rs (se 1 (by rfl) ⟨66518, by rfl⟩) R133037
theorem R88705 : Reach 88705 := rs (se 2 (by rfl) ⟨33264, by rfl⟩) R66529
theorem R88721 : Reach 88721 := rs (se 2 (by rfl) ⟨33270, by rfl⟩) R66541
theorem R88739 : Reach 88739 := rs (se 1 (by rfl) ⟨66554, by rfl⟩) R133109
theorem R187057 : Reach 187057 := rs (se 2 (by rfl) ⟨70146, by rfl⟩) R140293
theorem R88769 : Reach 88769 := rs (se 2 (by rfl) ⟨33288, by rfl⟩) R66577
theorem R285389 : Reach 285389 := rs (se 3 (by rfl) ⟨53510, by rfl⟩) R107021
theorem R88787 : Reach 88787 := rs (se 1 (by rfl) ⟨66590, by rfl⟩) R133181
theorem R88817 : Reach 88817 := rs (se 2 (by rfl) ⟨33306, by rfl⟩) R66613
theorem R88835 : Reach 88835 := rs (se 1 (by rfl) ⟨66626, by rfl⟩) R133253
theorem R88865 : Reach 88865 := rs (se 2 (by rfl) ⟨33324, by rfl⟩) R66649
theorem R88883 : Reach 88883 := rs (se 1 (by rfl) ⟨66662, by rfl⟩) R133325
theorem R1334069 : Reach 1334069 := rs (se 5 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R88913 : Reach 88913 := rs (se 2 (by rfl) ⟨33342, by rfl⟩) R66685
theorem R88931 : Reach 88931 := rs (se 1 (by rfl) ⟨66698, by rfl⟩) R133397
theorem R88961 : Reach 88961 := rs (se 2 (by rfl) ⟨33360, by rfl⟩) R66721
theorem R88979 : Reach 88979 := rs (se 1 (by rfl) ⟨66734, by rfl⟩) R133469
theorem R89009 : Reach 89009 := rs (se 2 (by rfl) ⟨33378, by rfl⟩) R66757
theorem R89027 : Reach 89027 := rs (se 1 (by rfl) ⟨66770, by rfl⟩) R133541
theorem R89041 : Reach 89041 := rs (se 2 (by rfl) ⟨33390, by rfl⟩) R66781
theorem R89057 : Reach 89057 := rs (se 2 (by rfl) ⟨33396, by rfl⟩) R66793
theorem R89075 : Reach 89075 := rs (se 1 (by rfl) ⟨66806, by rfl⟩) R133613
theorem R449549 : Reach 449549 := rs (se 3 (by rfl) ⟨84290, by rfl⟩) R168581
theorem R89105 : Reach 89105 := rs (se 2 (by rfl) ⟨33414, by rfl⟩) R66829
theorem R89123 : Reach 89123 := rs (se 1 (by rfl) ⟨66842, by rfl⟩) R133685
theorem R89153 : Reach 89153 := rs (se 2 (by rfl) ⟨33432, by rfl⟩) R66865
theorem R89171 : Reach 89171 := rs (se 1 (by rfl) ⟨66878, by rfl⟩) R133757
theorem R89201 : Reach 89201 := rs (se 2 (by rfl) ⟨33450, by rfl⟩) R66901
theorem R89219 : Reach 89219 := rs (se 1 (by rfl) ⟨66914, by rfl⟩) R133829
theorem R351373 : Reach 351373 := rs (se 3 (by rfl) ⟨65882, by rfl⟩) R131765
theorem R89249 : Reach 89249 := rs (se 2 (by rfl) ⟨33468, by rfl⟩) R66937
theorem R89267 : Reach 89267 := rs (se 1 (by rfl) ⟨66950, by rfl⟩) R133901
theorem R89297 : Reach 89297 := rs (se 2 (by rfl) ⟨33486, by rfl⟩) R66973
theorem R89315 : Reach 89315 := rs (se 1 (by rfl) ⟨66986, by rfl⟩) R133973
theorem R89345 : Reach 89345 := rs (se 2 (by rfl) ⟨33504, by rfl⟩) R67009
theorem R89363 : Reach 89363 := rs (se 1 (by rfl) ⟨67022, by rfl⟩) R134045
theorem R89393 : Reach 89393 := rs (se 2 (by rfl) ⟨33522, by rfl⟩) R67045
theorem R89411 : Reach 89411 := rs (se 1 (by rfl) ⟨67058, by rfl⟩) R134117
theorem R89441 : Reach 89441 := rs (se 2 (by rfl) ⟨33540, by rfl⟩) R67081
theorem R154993 : Reach 154993 := rs (se 2 (by rfl) ⟨58122, by rfl⟩) R116245
theorem R89459 : Reach 89459 := rs (se 1 (by rfl) ⟨67094, by rfl⟩) R134189
theorem R89489 : Reach 89489 := rs (se 2 (by rfl) ⟨33558, by rfl⟩) R67117
theorem R89507 : Reach 89507 := rs (se 1 (by rfl) ⟨67130, by rfl⟩) R134261
theorem R89537 : Reach 89537 := rs (se 2 (by rfl) ⟨33576, by rfl⟩) R67153
theorem R89555 : Reach 89555 := rs (se 1 (by rfl) ⟨67166, by rfl⟩) R134333
theorem R89585 : Reach 89585 := rs (se 2 (by rfl) ⟨33594, by rfl⟩) R67189
theorem R89603 : Reach 89603 := rs (se 1 (by rfl) ⟨67202, by rfl⟩) R134405
theorem R89633 : Reach 89633 := rs (se 2 (by rfl) ⟨33612, by rfl⟩) R67225
theorem R89651 : Reach 89651 := rs (se 1 (by rfl) ⟨67238, by rfl⟩) R134477
theorem R89681 : Reach 89681 := rs (se 2 (by rfl) ⟨33630, by rfl⟩) R67261
theorem R89699 : Reach 89699 := rs (se 1 (by rfl) ⟨67274, by rfl⟩) R134549
theorem R89729 : Reach 89729 := rs (se 2 (by rfl) ⟨33648, by rfl⟩) R67297
theorem R155267 : Reach 155267 := rs (se 1 (by rfl) ⟨116450, by rfl⟩) R232901
theorem R89747 : Reach 89747 := rs (se 1 (by rfl) ⟨67310, by rfl⟩) R134621
theorem R319139 : Reach 319139 := rs (se 1 (by rfl) ⟨239354, by rfl⟩) R478709
theorem R89777 : Reach 89777 := rs (se 2 (by rfl) ⟨33666, by rfl⟩) R67333
theorem R89795 : Reach 89795 := rs (se 1 (by rfl) ⟨67346, by rfl⟩) R134693
theorem R89825 : Reach 89825 := rs (se 2 (by rfl) ⟨33684, by rfl⟩) R67369
theorem R351971 : Reach 351971 := rs (se 1 (by rfl) ⟨263978, by rfl⟩) R527957
theorem R89843 : Reach 89843 := rs (se 1 (by rfl) ⟨67382, by rfl⟩) R134765
theorem R89873 : Reach 89873 := rs (se 2 (by rfl) ⟨33702, by rfl⟩) R67405
theorem R89891 : Reach 89891 := rs (se 1 (by rfl) ⟨67418, by rfl⟩) R134837
theorem R89921 : Reach 89921 := rs (se 2 (by rfl) ⟨33720, by rfl⟩) R67441
theorem R155459 : Reach 155459 := rs (se 1 (by rfl) ⟨116594, by rfl⟩) R233189
theorem R319301 : Reach 319301 := rs (se 4 (by rfl) ⟨29934, by rfl⟩) R59869
theorem R89939 : Reach 89939 := rs (se 1 (by rfl) ⟨67454, by rfl⟩) R134909
theorem R89969 : Reach 89969 := rs (se 2 (by rfl) ⟨33738, by rfl⟩) R67477
theorem R417649 : Reach 417649 := rs (se 2 (by rfl) ⟨156618, by rfl⟩) R313237
theorem R89987 : Reach 89987 := rs (se 1 (by rfl) ⟨67490, by rfl⟩) R134981
theorem R90017 : Reach 90017 := rs (se 2 (by rfl) ⟨33756, by rfl⟩) R67513
theorem R90035 : Reach 90035 := rs (se 1 (by rfl) ⟨67526, by rfl⟩) R135053
theorem R90065 : Reach 90065 := rs (se 2 (by rfl) ⟨33774, by rfl⟩) R67549
theorem R90083 : Reach 90083 := rs (se 1 (by rfl) ⟨67562, by rfl⟩) R135125
theorem R90113 : Reach 90113 := rs (se 2 (by rfl) ⟨33792, by rfl⟩) R67585
theorem R90131 : Reach 90131 := rs (se 1 (by rfl) ⟨67598, by rfl⟩) R135197
theorem R90161 : Reach 90161 := rs (se 2 (by rfl) ⟨33810, by rfl⟩) R67621
theorem R90179 : Reach 90179 := rs (se 1 (by rfl) ⟨67634, by rfl⟩) R135269
theorem R90209 : Reach 90209 := rs (se 2 (by rfl) ⟨33828, by rfl⟩) R67657
theorem R90227 : Reach 90227 := rs (se 1 (by rfl) ⟨67670, by rfl⟩) R135341
theorem R90257 : Reach 90257 := rs (se 2 (by rfl) ⟨33846, by rfl⟩) R67693
theorem R90275 : Reach 90275 := rs (se 1 (by rfl) ⟨67706, by rfl⟩) R135413
theorem R90305 : Reach 90305 := rs (se 2 (by rfl) ⟨33864, by rfl⟩) R67729
theorem R90323 : Reach 90323 := rs (se 1 (by rfl) ⟨67742, by rfl⟩) R135485
theorem R90353 : Reach 90353 := rs (se 2 (by rfl) ⟨33882, by rfl⟩) R67765
theorem R90371 : Reach 90371 := rs (se 1 (by rfl) ⟨67778, by rfl⟩) R135557
theorem R90401 : Reach 90401 := rs (se 2 (by rfl) ⟨33900, by rfl⟩) R67801
theorem R90419 : Reach 90419 := rs (se 1 (by rfl) ⟨67814, by rfl⟩) R135629
theorem R385357 : Reach 385357 := rs (se 3 (by rfl) ⟨72254, by rfl⟩) R144509
theorem R90449 : Reach 90449 := rs (se 2 (by rfl) ⟨33918, by rfl⟩) R67837
theorem R90467 : Reach 90467 := rs (se 1 (by rfl) ⟨67850, by rfl⟩) R135701
theorem R90497 : Reach 90497 := rs (se 2 (by rfl) ⟨33936, by rfl⟩) R67873
theorem R90499 : Reach 90499 := rs (se 1 (by rfl) ⟨67874, by rfl⟩) R135749
theorem R90515 : Reach 90515 := rs (se 1 (by rfl) ⟨67886, by rfl⟩) R135773
theorem R90545 : Reach 90545 := rs (se 2 (by rfl) ⟨33954, by rfl⟩) R67909
theorem R90547 : Reach 90547 := rs (se 1 (by rfl) ⟨67910, by rfl⟩) R135821
theorem R90563 : Reach 90563 := rs (se 1 (by rfl) ⟨67922, by rfl⟩) R135845
theorem R90593 : Reach 90593 := rs (se 2 (by rfl) ⟨33972, by rfl⟩) R67945
theorem R90611 : Reach 90611 := rs (se 1 (by rfl) ⟨67958, by rfl⟩) R135917
theorem R90641 : Reach 90641 := rs (se 2 (by rfl) ⟨33990, by rfl⟩) R67981
theorem R90659 : Reach 90659 := rs (se 1 (by rfl) ⟨67994, by rfl⟩) R135989
theorem R90689 : Reach 90689 := rs (se 2 (by rfl) ⟨34008, by rfl⟩) R68017
theorem R90707 : Reach 90707 := rs (se 1 (by rfl) ⟨68030, by rfl⟩) R136061
theorem R90737 : Reach 90737 := rs (se 2 (by rfl) ⟨34026, by rfl⟩) R68053
theorem R90755 : Reach 90755 := rs (se 1 (by rfl) ⟨68066, by rfl⟩) R136133
theorem R90785 : Reach 90785 := rs (se 2 (by rfl) ⟨34044, by rfl⟩) R68089
theorem R90803 : Reach 90803 := rs (se 1 (by rfl) ⟨68102, by rfl⟩) R136205
theorem R90833 : Reach 90833 := rs (se 2 (by rfl) ⟨34062, by rfl⟩) R68125
theorem R90851 : Reach 90851 := rs (se 1 (by rfl) ⟨68138, by rfl⟩) R136277
theorem R156401 : Reach 156401 := rs (se 2 (by rfl) ⟨58650, by rfl⟩) R117301
theorem R90881 : Reach 90881 := rs (se 2 (by rfl) ⟨34080, by rfl⟩) R68161
theorem R90899 : Reach 90899 := rs (se 1 (by rfl) ⟨68174, by rfl⟩) R136349
theorem R156451 : Reach 156451 := rs (se 1 (by rfl) ⟨117338, by rfl⟩) R234677
theorem R90929 : Reach 90929 := rs (se 2 (by rfl) ⟨34098, by rfl⟩) R68197
theorem R90947 : Reach 90947 := rs (se 1 (by rfl) ⟨68210, by rfl⟩) R136421
theorem R90977 : Reach 90977 := rs (se 2 (by rfl) ⟨34116, by rfl⟩) R68233
theorem R90995 : Reach 90995 := rs (se 1 (by rfl) ⟨68246, by rfl⟩) R136493
theorem R91025 : Reach 91025 := rs (se 2 (by rfl) ⟨34134, by rfl⟩) R68269
theorem R91043 : Reach 91043 := rs (se 1 (by rfl) ⟨68282, by rfl⟩) R136565
theorem R156593 : Reach 156593 := rs (se 2 (by rfl) ⟨58722, by rfl⟩) R117445
theorem R680885 : Reach 680885 := rs (se 5 (by rfl) ⟨31916, by rfl⟩) R63833
theorem R91073 : Reach 91073 := rs (se 2 (by rfl) ⟨34152, by rfl⟩) R68305
theorem R91091 : Reach 91091 := rs (se 1 (by rfl) ⟨68318, by rfl⟩) R136637
theorem R91121 : Reach 91121 := rs (se 2 (by rfl) ⟨34170, by rfl⟩) R68341
theorem R91139 : Reach 91139 := rs (se 1 (by rfl) ⟨68354, by rfl⟩) R136709
theorem R91169 : Reach 91169 := rs (se 2 (by rfl) ⟨34188, by rfl⟩) R68377
theorem R91187 : Reach 91187 := rs (se 1 (by rfl) ⟨68390, by rfl⟩) R136781
theorem R91217 : Reach 91217 := rs (se 2 (by rfl) ⟨34206, by rfl⟩) R68413
theorem R91235 : Reach 91235 := rs (se 1 (by rfl) ⟨68426, by rfl⟩) R136853
theorem R91265 : Reach 91265 := rs (se 2 (by rfl) ⟨34224, by rfl⟩) R68449
theorem R91283 : Reach 91283 := rs (se 1 (by rfl) ⟨68462, by rfl⟩) R136925
theorem R91313 : Reach 91313 := rs (se 2 (by rfl) ⟨34242, by rfl⟩) R68485
theorem R91331 : Reach 91331 := rs (se 1 (by rfl) ⟨68498, by rfl⟩) R136997
theorem R91361 : Reach 91361 := rs (se 2 (by rfl) ⟨34260, by rfl⟩) R68521
theorem R91379 : Reach 91379 := rs (se 1 (by rfl) ⟨68534, by rfl⟩) R137069
theorem R91409 : Reach 91409 := rs (se 2 (by rfl) ⟨34278, by rfl⟩) R68557
theorem R91427 : Reach 91427 := rs (se 1 (by rfl) ⟨68570, by rfl⟩) R137141
theorem R91457 : Reach 91457 := rs (se 2 (by rfl) ⟨34296, by rfl⟩) R68593
theorem R91475 : Reach 91475 := rs (se 1 (by rfl) ⟨68606, by rfl⟩) R137213
theorem R189809 : Reach 189809 := rs (se 2 (by rfl) ⟨71178, by rfl⟩) R142357
theorem R91505 : Reach 91505 := rs (se 2 (by rfl) ⟨34314, by rfl⟩) R68629
theorem R91523 : Reach 91523 := rs (se 1 (by rfl) ⟨68642, by rfl⟩) R137285
theorem R91553 : Reach 91553 := rs (se 2 (by rfl) ⟨34332, by rfl⟩) R68665
theorem R189859 : Reach 189859 := rs (se 1 (by rfl) ⟨142394, by rfl⟩) R284789
theorem R91571 : Reach 91571 := rs (se 1 (by rfl) ⟨68678, by rfl⟩) R137357
theorem R583109 : Reach 583109 := rs (se 4 (by rfl) ⟨54666, by rfl⟩) R109333
theorem R91601 : Reach 91601 := rs (se 2 (by rfl) ⟨34350, by rfl⟩) R68701
theorem R91619 : Reach 91619 := rs (se 1 (by rfl) ⟨68714, by rfl⟩) R137429
theorem R91649 : Reach 91649 := rs (se 2 (by rfl) ⟨34368, by rfl⟩) R68737
theorem R91667 : Reach 91667 := rs (se 1 (by rfl) ⟨68750, by rfl⟩) R137501
theorem R91697 : Reach 91697 := rs (se 2 (by rfl) ⟨34386, by rfl⟩) R68773
theorem R91715 : Reach 91715 := rs (se 1 (by rfl) ⟨68786, by rfl⟩) R137573
theorem R91729 : Reach 91729 := rs (se 2 (by rfl) ⟨34398, by rfl⟩) R68797
theorem R91745 : Reach 91745 := rs (se 2 (by rfl) ⟨34404, by rfl⟩) R68809
theorem R91763 : Reach 91763 := rs (se 1 (by rfl) ⟨68822, by rfl⟩) R137645
theorem R91793 : Reach 91793 := rs (se 2 (by rfl) ⟨34422, by rfl⟩) R68845
theorem R91811 : Reach 91811 := rs (se 1 (by rfl) ⟨68858, by rfl⟩) R137717
theorem R91841 : Reach 91841 := rs (se 2 (by rfl) ⟨34440, by rfl⟩) R68881
theorem R91859 : Reach 91859 := rs (se 1 (by rfl) ⟨68894, by rfl⟩) R137789
theorem R91889 : Reach 91889 := rs (se 2 (by rfl) ⟨34458, by rfl⟩) R68917
theorem R59123 : Reach 59123 := rs (se 1 (by rfl) ⟨44342, by rfl⟩) R88685
theorem R59139 : Reach 59139 := rs (se 1 (by rfl) ⟨44354, by rfl⟩) R88709
theorem R91907 : Reach 91907 := rs (se 1 (by rfl) ⟨68930, by rfl⟩) R137861
theorem R59155 : Reach 59155 := rs (se 1 (by rfl) ⟨44366, by rfl⟩) R88733
theorem R91937 : Reach 91937 := rs (se 2 (by rfl) ⟨34476, by rfl⟩) R68953
theorem R59171 : Reach 59171 := rs (se 1 (by rfl) ⟨44378, by rfl⟩) R88757
theorem R59187 : Reach 59187 := rs (se 1 (by rfl) ⟨44390, by rfl⟩) R88781
theorem R91955 : Reach 91955 := rs (se 1 (by rfl) ⟨68966, by rfl⟩) R137933
theorem R59203 : Reach 59203 := rs (se 1 (by rfl) ⟨44402, by rfl⟩) R88805
theorem R91985 : Reach 91985 := rs (se 2 (by rfl) ⟨34494, by rfl⟩) R68989
theorem R59219 : Reach 59219 := rs (se 1 (by rfl) ⟨44414, by rfl⟩) R88829
theorem R59235 : Reach 59235 := rs (se 1 (by rfl) ⟨44426, by rfl⟩) R88853
theorem R92003 : Reach 92003 := rs (se 1 (by rfl) ⟨69002, by rfl⟩) R138005
theorem R452465 : Reach 452465 := rs (se 2 (by rfl) ⟨169674, by rfl⟩) R339349
theorem R59251 : Reach 59251 := rs (se 1 (by rfl) ⟨44438, by rfl⟩) R88877
theorem R92033 : Reach 92033 := rs (se 2 (by rfl) ⟨34512, by rfl⟩) R69025
theorem R59267 : Reach 59267 := rs (se 1 (by rfl) ⟨44450, by rfl⟩) R88901
theorem R157585 : Reach 157585 := rs (se 2 (by rfl) ⟨59094, by rfl⟩) R118189
theorem R59283 : Reach 59283 := rs (se 1 (by rfl) ⟨44462, by rfl⟩) R88925
theorem R92051 : Reach 92051 := rs (se 1 (by rfl) ⟨69038, by rfl⟩) R138077
theorem R59299 : Reach 59299 := rs (se 1 (by rfl) ⟨44474, by rfl⟩) R88949
theorem R92081 : Reach 92081 := rs (se 2 (by rfl) ⟨34530, by rfl⟩) R69061
theorem R59315 : Reach 59315 := rs (se 1 (by rfl) ⟨44486, by rfl⟩) R88973
theorem R59331 : Reach 59331 := rs (se 1 (by rfl) ⟨44498, by rfl⟩) R88997
theorem R92099 : Reach 92099 := rs (se 1 (by rfl) ⟨69074, by rfl⟩) R138149
theorem R59347 : Reach 59347 := rs (se 1 (by rfl) ⟨44510, by rfl⟩) R89021
theorem R92129 : Reach 92129 := rs (se 2 (by rfl) ⟨34548, by rfl⟩) R69097
theorem R59363 : Reach 59363 := rs (se 1 (by rfl) ⟨44522, by rfl⟩) R89045
theorem R59379 : Reach 59379 := rs (se 1 (by rfl) ⟨44534, by rfl⟩) R89069
theorem R92147 : Reach 92147 := rs (se 1 (by rfl) ⟨69110, by rfl⟩) R138221
theorem R59395 : Reach 59395 := rs (se 1 (by rfl) ⟨44546, by rfl⟩) R89093
theorem R92177 : Reach 92177 := rs (se 2 (by rfl) ⟨34566, by rfl⟩) R69133
theorem R59411 : Reach 59411 := rs (se 1 (by rfl) ⟨44558, by rfl⟩) R89117
theorem R59427 : Reach 59427 := rs (se 1 (by rfl) ⟨44570, by rfl⟩) R89141
theorem R92195 : Reach 92195 := rs (se 1 (by rfl) ⟨69146, by rfl⟩) R138293
theorem R59443 : Reach 59443 := rs (se 1 (by rfl) ⟨44582, by rfl⟩) R89165
theorem R92225 : Reach 92225 := rs (se 2 (by rfl) ⟨34584, by rfl⟩) R69169
theorem R59459 : Reach 59459 := rs (se 1 (by rfl) ⟨44594, by rfl⟩) R89189
theorem R92227 : Reach 92227 := rs (se 1 (by rfl) ⟨69170, by rfl⟩) R138341
theorem R59475 : Reach 59475 := rs (se 1 (by rfl) ⟨44606, by rfl⟩) R89213
theorem R92243 : Reach 92243 := rs (se 1 (by rfl) ⟨69182, by rfl⟩) R138365
theorem R59491 : Reach 59491 := rs (se 1 (by rfl) ⟨44618, by rfl⟩) R89237
theorem R92273 : Reach 92273 := rs (se 2 (by rfl) ⟨34602, by rfl⟩) R69205
theorem R59507 : Reach 59507 := rs (se 1 (by rfl) ⟨44630, by rfl⟩) R89261
theorem R59523 : Reach 59523 := rs (se 1 (by rfl) ⟨44642, by rfl⟩) R89285
theorem R92291 : Reach 92291 := rs (se 1 (by rfl) ⟨69218, by rfl⟩) R138437
theorem R59539 : Reach 59539 := rs (se 1 (by rfl) ⟨44654, by rfl⟩) R89309
theorem R92321 : Reach 92321 := rs (se 2 (by rfl) ⟨34620, by rfl⟩) R69241
theorem R59555 : Reach 59555 := rs (se 1 (by rfl) ⟨44666, by rfl⟩) R89333
theorem R157859 : Reach 157859 := rs (se 1 (by rfl) ⟨118394, by rfl⟩) R236789
theorem R59571 : Reach 59571 := rs (se 1 (by rfl) ⟨44678, by rfl⟩) R89357
theorem R92339 : Reach 92339 := rs (se 1 (by rfl) ⟨69254, by rfl⟩) R138509
theorem R59587 : Reach 59587 := rs (se 1 (by rfl) ⟨44690, by rfl⟩) R89381
theorem R59603 : Reach 59603 := rs (se 1 (by rfl) ⟨44702, by rfl⟩) R89405
theorem R92369 : Reach 92369 := rs (se 2 (by rfl) ⟨34638, by rfl⟩) R69277
theorem R59619 : Reach 59619 := rs (se 1 (by rfl) ⟨44714, by rfl⟩) R89429
theorem R92387 : Reach 92387 := rs (se 1 (by rfl) ⟨69290, by rfl⟩) R138581
theorem R59635 : Reach 59635 := rs (se 1 (by rfl) ⟨44726, by rfl⟩) R89453
theorem R92417 : Reach 92417 := rs (se 2 (by rfl) ⟨34656, by rfl⟩) R69313
theorem R59651 : Reach 59651 := rs (se 1 (by rfl) ⟨44738, by rfl⟩) R89477
theorem R59667 : Reach 59667 := rs (se 1 (by rfl) ⟨44750, by rfl⟩) R89501
theorem R92435 : Reach 92435 := rs (se 1 (by rfl) ⟨69326, by rfl⟩) R138653
theorem R59683 : Reach 59683 := rs (se 1 (by rfl) ⟨44762, by rfl⟩) R89525
theorem R223523 : Reach 223523 := rs (se 1 (by rfl) ⟨167642, by rfl⟩) R335285
theorem R92465 : Reach 92465 := rs (se 2 (by rfl) ⟨34674, by rfl⟩) R69349
theorem R59699 : Reach 59699 := rs (se 1 (by rfl) ⟨44774, by rfl⟩) R89549
theorem R59715 : Reach 59715 := rs (se 1 (by rfl) ⟨44786, by rfl⟩) R89573
theorem R92483 : Reach 92483 := rs (se 1 (by rfl) ⟨69362, by rfl⟩) R138725
theorem R59731 : Reach 59731 := rs (se 1 (by rfl) ⟨44798, by rfl⟩) R89597
theorem R92513 : Reach 92513 := rs (se 2 (by rfl) ⟨34692, by rfl⟩) R69385
theorem R59747 : Reach 59747 := rs (se 1 (by rfl) ⟨44810, by rfl⟩) R89621
theorem R158051 : Reach 158051 := rs (se 1 (by rfl) ⟨118538, by rfl⟩) R237077
theorem R59763 : Reach 59763 := rs (se 1 (by rfl) ⟨44822, by rfl⟩) R89645
theorem R92531 : Reach 92531 := rs (se 1 (by rfl) ⟨69398, by rfl⟩) R138797
theorem R59779 : Reach 59779 := rs (se 1 (by rfl) ⟨44834, by rfl⟩) R89669
theorem R92561 : Reach 92561 := rs (se 2 (by rfl) ⟨34710, by rfl⟩) R69421
theorem R59795 : Reach 59795 := rs (se 1 (by rfl) ⟨44846, by rfl⟩) R89693
theorem R59811 : Reach 59811 := rs (se 1 (by rfl) ⟨44858, by rfl⟩) R89717
theorem R92579 : Reach 92579 := rs (se 1 (by rfl) ⟨69434, by rfl⟩) R138869
theorem R59827 : Reach 59827 := rs (se 1 (by rfl) ⟨44870, by rfl⟩) R89741
theorem R92609 : Reach 92609 := rs (se 2 (by rfl) ⟨34728, by rfl⟩) R69457
theorem R59843 : Reach 59843 := rs (se 1 (by rfl) ⟨44882, by rfl⟩) R89765
theorem R59859 : Reach 59859 := rs (se 1 (by rfl) ⟨44894, by rfl⟩) R89789
theorem R92627 : Reach 92627 := rs (se 1 (by rfl) ⟨69470, by rfl⟩) R138941
theorem R59875 : Reach 59875 := rs (se 1 (by rfl) ⟨44906, by rfl⟩) R89813
theorem R92657 : Reach 92657 := rs (se 2 (by rfl) ⟨34746, by rfl⟩) R69493
theorem R59891 : Reach 59891 := rs (se 1 (by rfl) ⟨44918, by rfl⟩) R89837
theorem R59907 : Reach 59907 := rs (se 1 (by rfl) ⟨44930, by rfl⟩) R89861
theorem R92675 : Reach 92675 := rs (se 1 (by rfl) ⟨69506, by rfl⟩) R139013
theorem R59923 : Reach 59923 := rs (se 1 (by rfl) ⟨44942, by rfl⟩) R89885
theorem R92705 : Reach 92705 := rs (se 2 (by rfl) ⟨34764, by rfl⟩) R69529
theorem R59939 : Reach 59939 := rs (se 1 (by rfl) ⟨44954, by rfl⟩) R89909
theorem R256547 : Reach 256547 := rs (se 1 (by rfl) ⟨192410, by rfl⟩) R384821
theorem R59955 : Reach 59955 := rs (se 1 (by rfl) ⟨44966, by rfl⟩) R89933
theorem R92723 : Reach 92723 := rs (se 1 (by rfl) ⟨69542, by rfl⟩) R139085
theorem R59971 : Reach 59971 := rs (se 1 (by rfl) ⟨44978, by rfl⟩) R89957
theorem R92753 : Reach 92753 := rs (se 2 (by rfl) ⟨34782, by rfl⟩) R69565
theorem R59987 : Reach 59987 := rs (se 1 (by rfl) ⟨44990, by rfl⟩) R89981
theorem R60003 : Reach 60003 := rs (se 1 (by rfl) ⟨45002, by rfl⟩) R90005
theorem R92771 : Reach 92771 := rs (se 1 (by rfl) ⟨69578, by rfl⟩) R139157
theorem R191089 : Reach 191089 := rs (se 2 (by rfl) ⟨71658, by rfl⟩) R143317
theorem R60019 : Reach 60019 := rs (se 1 (by rfl) ⟨45014, by rfl⟩) R90029
theorem R92801 : Reach 92801 := rs (se 2 (by rfl) ⟨34800, by rfl⟩) R69601
theorem R60035 : Reach 60035 := rs (se 1 (by rfl) ⟨45026, by rfl⟩) R90053
theorem R60051 : Reach 60051 := rs (se 1 (by rfl) ⟨45038, by rfl⟩) R90077
theorem R92819 : Reach 92819 := rs (se 1 (by rfl) ⟨69614, by rfl⟩) R139229
theorem R60067 : Reach 60067 := rs (se 1 (by rfl) ⟨45050, by rfl⟩) R90101
theorem R92849 : Reach 92849 := rs (se 2 (by rfl) ⟨34818, by rfl⟩) R69637
theorem R60083 : Reach 60083 := rs (se 1 (by rfl) ⟨45062, by rfl⟩) R90125
theorem R92867 : Reach 92867 := rs (se 1 (by rfl) ⟨69650, by rfl⟩) R139301
theorem R60099 : Reach 60099 := rs (se 1 (by rfl) ⟨45074, by rfl⟩) R90149
theorem R60115 : Reach 60115 := rs (se 1 (by rfl) ⟨45086, by rfl⟩) R90173
theorem R92897 : Reach 92897 := rs (se 2 (by rfl) ⟨34836, by rfl⟩) R69673
theorem R60131 : Reach 60131 := rs (se 1 (by rfl) ⟨45098, by rfl⟩) R90197
theorem R60147 : Reach 60147 := rs (se 1 (by rfl) ⟨45110, by rfl⟩) R90221
theorem R92915 : Reach 92915 := rs (se 1 (by rfl) ⟨69686, by rfl⟩) R139373
theorem R60163 : Reach 60163 := rs (se 1 (by rfl) ⟨45122, by rfl⟩) R90245
theorem R92945 : Reach 92945 := rs (se 2 (by rfl) ⟨34854, by rfl⟩) R69709
theorem R60179 : Reach 60179 := rs (se 1 (by rfl) ⟨45134, by rfl⟩) R90269
theorem R60195 : Reach 60195 := rs (se 1 (by rfl) ⟨45146, by rfl⟩) R90293
theorem R92963 : Reach 92963 := rs (se 1 (by rfl) ⟨69722, by rfl⟩) R139445
theorem R60211 : Reach 60211 := rs (se 1 (by rfl) ⟨45158, by rfl⟩) R90317
theorem R92993 : Reach 92993 := rs (se 2 (by rfl) ⟨34872, by rfl⟩) R69745
theorem R60227 : Reach 60227 := rs (se 1 (by rfl) ⟨45170, by rfl⟩) R90341
theorem R60243 : Reach 60243 := rs (se 1 (by rfl) ⟨45182, by rfl⟩) R90365
theorem R93011 : Reach 93011 := rs (se 1 (by rfl) ⟨69758, by rfl⟩) R139517
theorem R60259 : Reach 60259 := rs (se 1 (by rfl) ⟨45194, by rfl⟩) R90389
theorem R93041 : Reach 93041 := rs (se 2 (by rfl) ⟨34890, by rfl⟩) R69781
theorem R60275 : Reach 60275 := rs (se 1 (by rfl) ⟨45206, by rfl⟩) R90413
theorem R60291 : Reach 60291 := rs (se 1 (by rfl) ⟨45218, by rfl⟩) R90437
theorem R93059 : Reach 93059 := rs (se 1 (by rfl) ⟨69794, by rfl⟩) R139589
theorem R355205 : Reach 355205 := rs (se 4 (by rfl) ⟨33300, by rfl⟩) R66601
theorem R60307 : Reach 60307 := rs (se 1 (by rfl) ⟨45230, by rfl⟩) R90461
theorem R93089 : Reach 93089 := rs (se 2 (by rfl) ⟨34908, by rfl⟩) R69817
theorem R60323 : Reach 60323 := rs (se 1 (by rfl) ⟨45242, by rfl⟩) R90485
theorem R60339 : Reach 60339 := rs (se 1 (by rfl) ⟨45254, by rfl⟩) R90509
theorem R93107 : Reach 93107 := rs (se 1 (by rfl) ⟨69830, by rfl⟩) R139661
theorem R60355 : Reach 60355 := rs (se 1 (by rfl) ⟨45266, by rfl⟩) R90533
theorem R158669 : Reach 158669 := rs (se 3 (by rfl) ⟨29750, by rfl⟩) R59501
theorem R93137 : Reach 93137 := rs (se 2 (by rfl) ⟨34926, by rfl⟩) R69853
theorem R60371 : Reach 60371 := rs (se 1 (by rfl) ⟨45278, by rfl⟩) R90557
theorem R60387 : Reach 60387 := rs (se 1 (by rfl) ⟨45290, by rfl⟩) R90581
theorem R93155 : Reach 93155 := rs (se 1 (by rfl) ⟨69866, by rfl⟩) R139733
theorem R60403 : Reach 60403 := rs (se 1 (by rfl) ⟨45302, by rfl⟩) R90605
theorem R93185 : Reach 93185 := rs (se 2 (by rfl) ⟨34944, by rfl⟩) R69889
theorem R60419 : Reach 60419 := rs (se 1 (by rfl) ⟨45314, by rfl⟩) R90629
theorem R60435 : Reach 60435 := rs (se 1 (by rfl) ⟨45326, by rfl⟩) R90653
theorem R93203 : Reach 93203 := rs (se 1 (by rfl) ⟨69902, by rfl⟩) R139805
theorem R60451 : Reach 60451 := rs (se 1 (by rfl) ⟨45338, by rfl⟩) R90677
theorem R93233 : Reach 93233 := rs (se 2 (by rfl) ⟨34962, by rfl⟩) R69925
theorem R60467 : Reach 60467 := rs (se 1 (by rfl) ⟨45350, by rfl⟩) R90701
theorem R60483 : Reach 60483 := rs (se 1 (by rfl) ⟨45362, by rfl⟩) R90725
theorem R93251 : Reach 93251 := rs (se 1 (by rfl) ⟨69938, by rfl⟩) R139877
theorem R60499 : Reach 60499 := rs (se 1 (by rfl) ⟨45374, by rfl⟩) R90749
theorem R93281 : Reach 93281 := rs (se 2 (by rfl) ⟨34980, by rfl⟩) R69961
theorem R60515 : Reach 60515 := rs (se 1 (by rfl) ⟨45386, by rfl⟩) R90773
theorem R60531 : Reach 60531 := rs (se 1 (by rfl) ⟨45398, by rfl⟩) R90797
theorem R93299 : Reach 93299 := rs (se 1 (by rfl) ⟨69974, by rfl⟩) R139949
theorem R60547 : Reach 60547 := rs (se 1 (by rfl) ⟨45410, by rfl⟩) R90821
theorem R158861 : Reach 158861 := rs (se 3 (by rfl) ⟨29786, by rfl⟩) R59573
theorem R93329 : Reach 93329 := rs (se 2 (by rfl) ⟨34998, by rfl⟩) R69997
theorem R60563 : Reach 60563 := rs (se 1 (by rfl) ⟨45422, by rfl⟩) R90845
theorem R60579 : Reach 60579 := rs (se 1 (by rfl) ⟨45434, by rfl⟩) R90869
theorem R93347 : Reach 93347 := rs (se 1 (by rfl) ⟨70010, by rfl⟩) R140021
theorem R158897 : Reach 158897 := rs (se 2 (by rfl) ⟨59586, by rfl⟩) R119173
theorem R60595 : Reach 60595 := rs (se 1 (by rfl) ⟨45446, by rfl⟩) R90893
theorem R93377 : Reach 93377 := rs (se 2 (by rfl) ⟨35016, by rfl⟩) R70033
theorem R60611 : Reach 60611 := rs (se 1 (by rfl) ⟨45458, by rfl⟩) R90917
theorem R60627 : Reach 60627 := rs (se 1 (by rfl) ⟨45470, by rfl⟩) R90941
theorem R93395 : Reach 93395 := rs (se 1 (by rfl) ⟨70046, by rfl⟩) R140093
theorem R60643 : Reach 60643 := rs (se 1 (by rfl) ⟨45482, by rfl⟩) R90965
theorem R93425 : Reach 93425 := rs (se 2 (by rfl) ⟨35034, by rfl⟩) R70069
theorem R60659 : Reach 60659 := rs (se 1 (by rfl) ⟨45494, by rfl⟩) R90989
theorem R60675 : Reach 60675 := rs (se 1 (by rfl) ⟨45506, by rfl⟩) R91013
theorem R93443 : Reach 93443 := rs (se 1 (by rfl) ⟨70082, by rfl⟩) R140165
theorem R158993 : Reach 158993 := rs (se 2 (by rfl) ⟨59622, by rfl⟩) R119245
theorem R60691 : Reach 60691 := rs (se 1 (by rfl) ⟨45518, by rfl⟩) R91037
theorem R93473 : Reach 93473 := rs (se 2 (by rfl) ⟨35052, by rfl⟩) R70105
theorem R60707 : Reach 60707 := rs (se 1 (by rfl) ⟨45530, by rfl⟩) R91061
theorem R60723 : Reach 60723 := rs (se 1 (by rfl) ⟨45542, by rfl⟩) R91085
theorem R93491 : Reach 93491 := rs (se 1 (by rfl) ⟨70118, by rfl⟩) R140237
theorem R60739 : Reach 60739 := rs (se 1 (by rfl) ⟨45554, by rfl⟩) R91109
theorem R159043 : Reach 159043 := rs (se 1 (by rfl) ⟨119282, by rfl⟩) R238565
theorem R355661 : Reach 355661 := rs (se 3 (by rfl) ⟨66686, by rfl⟩) R133373
theorem R93521 : Reach 93521 := rs (se 2 (by rfl) ⟨35070, by rfl⟩) R70141
theorem R60755 : Reach 60755 := rs (se 1 (by rfl) ⟨45566, by rfl⟩) R91133
theorem R60771 : Reach 60771 := rs (se 1 (by rfl) ⟨45578, by rfl⟩) R91157
theorem R93539 : Reach 93539 := rs (se 1 (by rfl) ⟨70154, by rfl⟩) R140309
theorem R60787 : Reach 60787 := rs (se 1 (by rfl) ⟨45590, by rfl⟩) R91181
theorem R60803 : Reach 60803 := rs (se 1 (by rfl) ⟨45602, by rfl⟩) R91205
theorem R93569 : Reach 93569 := rs (se 2 (by rfl) ⟨35088, by rfl⟩) R70177
theorem R224653 : Reach 224653 := rs (se 3 (by rfl) ⟨42122, by rfl⟩) R84245
theorem R60819 : Reach 60819 := rs (se 1 (by rfl) ⟨45614, by rfl⟩) R91229
theorem R93587 : Reach 93587 := rs (se 1 (by rfl) ⟨70190, by rfl⟩) R140381
theorem R60835 : Reach 60835 := rs (se 1 (by rfl) ⟨45626, by rfl⟩) R91253
theorem R93617 : Reach 93617 := rs (se 2 (by rfl) ⟨35106, by rfl⟩) R70213
theorem R60851 : Reach 60851 := rs (se 1 (by rfl) ⟨45638, by rfl⟩) R91277
theorem R60867 : Reach 60867 := rs (se 1 (by rfl) ⟨45650, by rfl⟩) R91301
theorem R93635 : Reach 93635 := rs (se 1 (by rfl) ⟨70226, by rfl⟩) R140453
theorem R159185 : Reach 159185 := rs (se 2 (by rfl) ⟨59694, by rfl⟩) R119389
theorem R60883 : Reach 60883 := rs (se 1 (by rfl) ⟨45662, by rfl⟩) R91325
theorem R93665 : Reach 93665 := rs (se 2 (by rfl) ⟨35124, by rfl⟩) R70249
theorem R60899 : Reach 60899 := rs (se 1 (by rfl) ⟨45674, by rfl⟩) R91349
theorem R60915 : Reach 60915 := rs (se 1 (by rfl) ⟨45686, by rfl⟩) R91373
theorem R93683 : Reach 93683 := rs (se 1 (by rfl) ⟨70262, by rfl⟩) R140525
theorem R60931 : Reach 60931 := rs (se 1 (by rfl) ⟨45698, by rfl⟩) R91397
theorem R93713 : Reach 93713 := rs (se 2 (by rfl) ⟨35142, by rfl⟩) R70285
theorem R60947 : Reach 60947 := rs (se 1 (by rfl) ⟨45710, by rfl⟩) R91421
theorem R60963 : Reach 60963 := rs (se 1 (by rfl) ⟨45722, by rfl⟩) R91445
theorem R93731 : Reach 93731 := rs (se 1 (by rfl) ⟨70298, by rfl⟩) R140597
theorem R60979 : Reach 60979 := rs (se 1 (by rfl) ⟨45734, by rfl⟩) R91469
theorem R93761 : Reach 93761 := rs (se 2 (by rfl) ⟨35160, by rfl⟩) R70321
theorem R60995 : Reach 60995 := rs (se 1 (by rfl) ⟨45746, by rfl⟩) R91493
theorem R61011 : Reach 61011 := rs (se 1 (by rfl) ⟨45758, by rfl⟩) R91517
theorem R93779 : Reach 93779 := rs (se 1 (by rfl) ⟨70334, by rfl⟩) R140669
theorem R61027 : Reach 61027 := rs (se 1 (by rfl) ⟨45770, by rfl⟩) R91541
theorem R93809 : Reach 93809 := rs (se 2 (by rfl) ⟨35178, by rfl⟩) R70357
theorem R61043 : Reach 61043 := rs (se 1 (by rfl) ⟨45782, by rfl⟩) R91565
theorem R61059 : Reach 61059 := rs (se 1 (by rfl) ⟨45794, by rfl⟩) R91589
theorem R93827 : Reach 93827 := rs (se 1 (by rfl) ⟨70370, by rfl⟩) R140741
theorem R61075 : Reach 61075 := rs (se 1 (by rfl) ⟨45806, by rfl⟩) R91613
theorem R93857 : Reach 93857 := rs (se 2 (by rfl) ⟨35196, by rfl⟩) R70393
theorem R61091 : Reach 61091 := rs (se 1 (by rfl) ⟨45818, by rfl⟩) R91637
theorem R126641 : Reach 126641 := rs (se 2 (by rfl) ⟨47490, by rfl⟩) R94981
theorem R61107 : Reach 61107 := rs (se 1 (by rfl) ⟨45830, by rfl⟩) R91661
theorem R93875 : Reach 93875 := rs (se 1 (by rfl) ⟨70406, by rfl⟩) R140813
theorem R126659 : Reach 126659 := rs (se 1 (by rfl) ⟨94994, by rfl⟩) R189989
theorem R61123 : Reach 61123 := rs (se 1 (by rfl) ⟨45842, by rfl⟩) R91685
theorem R61139 : Reach 61139 := rs (se 1 (by rfl) ⟨45854, by rfl⟩) R91709
theorem R93905 : Reach 93905 := rs (se 2 (by rfl) ⟨35214, by rfl⟩) R70429
theorem R61155 : Reach 61155 := rs (se 1 (by rfl) ⟨45866, by rfl⟩) R91733
theorem R93923 : Reach 93923 := rs (se 1 (by rfl) ⟨70442, by rfl⟩) R140885
theorem R61171 : Reach 61171 := rs (se 1 (by rfl) ⟨45878, by rfl⟩) R91757
theorem R93953 : Reach 93953 := rs (se 2 (by rfl) ⟨35232, by rfl⟩) R70465
theorem R61187 : Reach 61187 := rs (se 1 (by rfl) ⟨45890, by rfl⟩) R91781
theorem R192269 : Reach 192269 := rs (se 3 (by rfl) ⟨36050, by rfl⟩) R72101
theorem R61203 : Reach 61203 := rs (se 1 (by rfl) ⟨45902, by rfl⟩) R91805
theorem R93971 : Reach 93971 := rs (se 1 (by rfl) ⟨70478, by rfl⟩) R140957
theorem R61219 : Reach 61219 := rs (se 1 (by rfl) ⟨45914, by rfl⟩) R91829
theorem R94001 : Reach 94001 := rs (se 2 (by rfl) ⟨35250, by rfl⟩) R70501
theorem R61235 : Reach 61235 := rs (se 1 (by rfl) ⟨45926, by rfl⟩) R91853
theorem R61251 : Reach 61251 := rs (se 1 (by rfl) ⟨45938, by rfl⟩) R91877
theorem R94019 : Reach 94019 := rs (se 1 (by rfl) ⟨70514, by rfl⟩) R141029
theorem R61267 : Reach 61267 := rs (se 1 (by rfl) ⟨45950, by rfl⟩) R91901
theorem R61283 : Reach 61283 := rs (se 1 (by rfl) ⟨45962, by rfl⟩) R91925
theorem R94051 : Reach 94051 := rs (se 1 (by rfl) ⟨70538, by rfl⟩) R141077
theorem R94049 : Reach 94049 := rs (se 2 (by rfl) ⟨35268, by rfl⟩) R70537
theorem R61299 : Reach 61299 := rs (se 1 (by rfl) ⟨45974, by rfl⟩) R91949
theorem R94067 : Reach 94067 := rs (se 1 (by rfl) ⟨70550, by rfl⟩) R141101
theorem R61315 : Reach 61315 := rs (se 1 (by rfl) ⟨45986, by rfl⟩) R91973
theorem R94097 : Reach 94097 := rs (se 2 (by rfl) ⟨35286, by rfl⟩) R70573
theorem R61331 : Reach 61331 := rs (se 1 (by rfl) ⟨45998, by rfl⟩) R91997
theorem R61347 : Reach 61347 := rs (se 1 (by rfl) ⟨46010, by rfl⟩) R92021
theorem R94115 : Reach 94115 := rs (se 1 (by rfl) ⟨70586, by rfl⟩) R141173
theorem R61363 : Reach 61363 := rs (se 1 (by rfl) ⟨46022, by rfl⟩) R92045
theorem R61379 : Reach 61379 := rs (se 1 (by rfl) ⟨46034, by rfl⟩) R92069
theorem R94145 : Reach 94145 := rs (se 2 (by rfl) ⟨35304, by rfl⟩) R70609
theorem R61395 : Reach 61395 := rs (se 1 (by rfl) ⟨46046, by rfl⟩) R92093
theorem R94163 : Reach 94163 := rs (se 1 (by rfl) ⟨70622, by rfl⟩) R141245
theorem R61411 : Reach 61411 := rs (se 1 (by rfl) ⟨46058, by rfl⟩) R92117
theorem R94193 : Reach 94193 := rs (se 2 (by rfl) ⟨35322, by rfl⟩) R70645
theorem R61427 : Reach 61427 := rs (se 1 (by rfl) ⟨46070, by rfl⟩) R92141
theorem R61443 : Reach 61443 := rs (se 1 (by rfl) ⟨46082, by rfl⟩) R92165
theorem R94211 : Reach 94211 := rs (se 1 (by rfl) ⟨70658, by rfl⟩) R141317
theorem R61459 : Reach 61459 := rs (se 1 (by rfl) ⟨46094, by rfl⟩) R92189
theorem R94241 : Reach 94241 := rs (se 2 (by rfl) ⟨35340, by rfl⟩) R70681
theorem R61475 : Reach 61475 := rs (se 1 (by rfl) ⟨46106, by rfl⟩) R92213
theorem R61491 : Reach 61491 := rs (se 1 (by rfl) ⟨46118, by rfl⟩) R92237
theorem R94259 : Reach 94259 := rs (se 1 (by rfl) ⟨70694, by rfl⟩) R141389
theorem R61507 : Reach 61507 := rs (se 1 (by rfl) ⟨46130, by rfl⟩) R92261
theorem R94289 : Reach 94289 := rs (se 2 (by rfl) ⟨35358, by rfl⟩) R70717
theorem R61523 : Reach 61523 := rs (se 1 (by rfl) ⟨46142, by rfl⟩) R92285
theorem R61539 : Reach 61539 := rs (se 1 (by rfl) ⟨46154, by rfl⟩) R92309
theorem R94307 : Reach 94307 := rs (se 1 (by rfl) ⟨70730, by rfl⟩) R141461
theorem R61555 : Reach 61555 := rs (se 1 (by rfl) ⟨46166, by rfl⟩) R92333
theorem R94337 : Reach 94337 := rs (se 2 (by rfl) ⟨35376, by rfl⟩) R70753
theorem R61571 : Reach 61571 := rs (se 1 (by rfl) ⟨46178, by rfl⟩) R92357
theorem R61587 : Reach 61587 := rs (se 1 (by rfl) ⟨46190, by rfl⟩) R92381
theorem R94355 : Reach 94355 := rs (se 1 (by rfl) ⟨70766, by rfl⟩) R141533
theorem R225443 : Reach 225443 := rs (se 1 (by rfl) ⟨169082, by rfl⟩) R338165
theorem R61603 : Reach 61603 := rs (se 1 (by rfl) ⟨46202, by rfl⟩) R92405
theorem R94385 : Reach 94385 := rs (se 2 (by rfl) ⟨35394, by rfl⟩) R70789
theorem R61619 : Reach 61619 := rs (se 1 (by rfl) ⟨46214, by rfl⟩) R92429
theorem R61635 : Reach 61635 := rs (se 1 (by rfl) ⟨46226, by rfl⟩) R92453
theorem R94403 : Reach 94403 := rs (se 1 (by rfl) ⟨70802, by rfl⟩) R141605
theorem R61651 : Reach 61651 := rs (se 1 (by rfl) ⟨46238, by rfl⟩) R92477
theorem R94433 : Reach 94433 := rs (se 2 (by rfl) ⟨35412, by rfl⟩) R70825
theorem R61667 : Reach 61667 := rs (se 1 (by rfl) ⟨46250, by rfl⟩) R92501
theorem R61683 : Reach 61683 := rs (se 1 (by rfl) ⟨46262, by rfl⟩) R92525
theorem R94451 : Reach 94451 := rs (se 1 (by rfl) ⟨70838, by rfl⟩) R141677
theorem R61699 : Reach 61699 := rs (se 1 (by rfl) ⟨46274, by rfl⟩) R92549
theorem R94481 : Reach 94481 := rs (se 2 (by rfl) ⟨35430, by rfl⟩) R70861
theorem R61715 : Reach 61715 := rs (se 1 (by rfl) ⟨46286, by rfl⟩) R92573
theorem R61731 : Reach 61731 := rs (se 1 (by rfl) ⟨46298, by rfl⟩) R92597
theorem R94499 : Reach 94499 := rs (se 1 (by rfl) ⟨70874, by rfl⟩) R141749
theorem R61747 : Reach 61747 := rs (se 1 (by rfl) ⟨46310, by rfl⟩) R92621
theorem R61763 : Reach 61763 := rs (se 1 (by rfl) ⟨46322, by rfl⟩) R92645
theorem R94529 : Reach 94529 := rs (se 2 (by rfl) ⟨35448, by rfl⟩) R70897
theorem R61779 : Reach 61779 := rs (se 1 (by rfl) ⟨46334, by rfl⟩) R92669
theorem R94547 : Reach 94547 := rs (se 1 (by rfl) ⟨70910, by rfl⟩) R141821
theorem R61795 : Reach 61795 := rs (se 1 (by rfl) ⟨46346, by rfl⟩) R92693
theorem R94577 : Reach 94577 := rs (se 2 (by rfl) ⟨35466, by rfl⟩) R70933
theorem R61811 : Reach 61811 := rs (se 1 (by rfl) ⟨46358, by rfl⟩) R92717
theorem R61827 : Reach 61827 := rs (se 1 (by rfl) ⟨46370, by rfl⟩) R92741
theorem R94595 : Reach 94595 := rs (se 1 (by rfl) ⟨70946, by rfl⟩) R141893
theorem R61843 : Reach 61843 := rs (se 1 (by rfl) ⟨46382, by rfl⟩) R92765
theorem R94625 : Reach 94625 := rs (se 2 (by rfl) ⟨35484, by rfl⟩) R70969
theorem R61859 : Reach 61859 := rs (se 1 (by rfl) ⟨46394, by rfl⟩) R92789
theorem R61875 : Reach 61875 := rs (se 1 (by rfl) ⟨46406, by rfl⟩) R92813
theorem R94643 : Reach 94643 := rs (se 1 (by rfl) ⟨70982, by rfl⟩) R141965
theorem R61891 : Reach 61891 := rs (se 1 (by rfl) ⟨46418, by rfl⟩) R92837
theorem R94673 : Reach 94673 := rs (se 2 (by rfl) ⟨35502, by rfl⟩) R71005
theorem R61907 : Reach 61907 := rs (se 1 (by rfl) ⟨46430, by rfl⟩) R92861
theorem R61923 : Reach 61923 := rs (se 1 (by rfl) ⟨46442, by rfl⟩) R92885
theorem R258545 : Reach 258545 := rs (se 2 (by rfl) ⟨96954, by rfl⟩) R193909
theorem R61939 : Reach 61939 := rs (se 1 (by rfl) ⟨46454, by rfl⟩) R92909
theorem R61955 : Reach 61955 := rs (se 1 (by rfl) ⟨46466, by rfl⟩) R92933
theorem R61971 : Reach 61971 := rs (se 1 (by rfl) ⟨46478, by rfl⟩) R92957
theorem R61987 : Reach 61987 := rs (se 1 (by rfl) ⟨46490, by rfl⟩) R92981
theorem R62003 : Reach 62003 := rs (se 1 (by rfl) ⟨46502, by rfl⟩) R93005
theorem R62019 : Reach 62019 := rs (se 1 (by rfl) ⟨46514, by rfl⟩) R93029
theorem R62035 : Reach 62035 := rs (se 1 (by rfl) ⟨46526, by rfl⟩) R93053
theorem R62051 : Reach 62051 := rs (se 1 (by rfl) ⟨46538, by rfl⟩) R93077
theorem R62067 : Reach 62067 := rs (se 1 (by rfl) ⟨46550, by rfl⟩) R93101
theorem R62083 : Reach 62083 := rs (se 1 (by rfl) ⟨46562, by rfl⟩) R93125
theorem R389765 : Reach 389765 := rs (se 4 (by rfl) ⟨36540, by rfl⟩) R73081
theorem R62099 : Reach 62099 := rs (se 1 (by rfl) ⟨46574, by rfl⟩) R93149
theorem R62115 : Reach 62115 := rs (se 1 (by rfl) ⟨46586, by rfl⟩) R93173
theorem R62131 : Reach 62131 := rs (se 1 (by rfl) ⟨46598, by rfl⟩) R93197
theorem R62147 : Reach 62147 := rs (se 1 (by rfl) ⟨46610, by rfl⟩) R93221
theorem R62163 : Reach 62163 := rs (se 1 (by rfl) ⟨46622, by rfl⟩) R93245
theorem R62179 : Reach 62179 := rs (se 1 (by rfl) ⟨46634, by rfl⟩) R93269
theorem R62195 : Reach 62195 := rs (se 1 (by rfl) ⟨46646, by rfl⟩) R93293
theorem R62211 : Reach 62211 := rs (se 1 (by rfl) ⟨46658, by rfl⟩) R93317
theorem R62227 : Reach 62227 := rs (se 1 (by rfl) ⟨46670, by rfl⟩) R93341
theorem R62243 : Reach 62243 := rs (se 1 (by rfl) ⟨46682, by rfl⟩) R93365
theorem R226097 : Reach 226097 := rs (se 2 (by rfl) ⟨84786, by rfl⟩) R169573
theorem R62259 : Reach 62259 := rs (se 1 (by rfl) ⟨46694, by rfl⟩) R93389
theorem R62275 : Reach 62275 := rs (se 1 (by rfl) ⟨46706, by rfl⟩) R93413
theorem R62291 : Reach 62291 := rs (se 1 (by rfl) ⟨46718, by rfl⟩) R93437
theorem R62307 : Reach 62307 := rs (se 1 (by rfl) ⟨46730, by rfl⟩) R93461
theorem R62323 : Reach 62323 := rs (se 1 (by rfl) ⟨46742, by rfl⟩) R93485
theorem R62339 : Reach 62339 := rs (se 1 (by rfl) ⟨46754, by rfl⟩) R93509
theorem R127889 : Reach 127889 := rs (se 2 (by rfl) ⟨47958, by rfl⟩) R95917
theorem R62355 : Reach 62355 := rs (se 1 (by rfl) ⟨46766, by rfl⟩) R93533
theorem R62371 : Reach 62371 := rs (se 1 (by rfl) ⟨46778, by rfl⟩) R93557
theorem R62387 : Reach 62387 := rs (se 1 (by rfl) ⟨46790, by rfl⟩) R93581
theorem R62403 : Reach 62403 := rs (se 1 (by rfl) ⟨46802, by rfl⟩) R93605
theorem R62419 : Reach 62419 := rs (se 1 (by rfl) ⟨46814, by rfl⟩) R93629
theorem R62435 : Reach 62435 := rs (se 1 (by rfl) ⟨46826, by rfl⟩) R93653
theorem R62451 : Reach 62451 := rs (se 1 (by rfl) ⟨46838, by rfl⟩) R93677
theorem R62467 : Reach 62467 := rs (se 1 (by rfl) ⟨46850, by rfl⟩) R93701
theorem R95251 : Reach 95251 := rs (se 1 (by rfl) ⟨71438, by rfl⟩) R142877
theorem R62483 : Reach 62483 := rs (se 1 (by rfl) ⟨46862, by rfl⟩) R93725
theorem R62499 : Reach 62499 := rs (se 1 (by rfl) ⟨46874, by rfl⟩) R93749
theorem R62515 : Reach 62515 := rs (se 1 (by rfl) ⟨46886, by rfl⟩) R93773
theorem R62531 : Reach 62531 := rs (se 1 (by rfl) ⟨46898, by rfl⟩) R93797
theorem R62547 : Reach 62547 := rs (se 1 (by rfl) ⟨46910, by rfl⟩) R93821
theorem R128099 : Reach 128099 := rs (se 1 (by rfl) ⟨96074, by rfl⟩) R192149
theorem R62563 : Reach 62563 := rs (se 1 (by rfl) ⟨46922, by rfl⟩) R93845
theorem R62579 : Reach 62579 := rs (se 1 (by rfl) ⟨46934, by rfl⟩) R93869
theorem R62595 : Reach 62595 := rs (se 1 (by rfl) ⟨46946, by rfl⟩) R93893
theorem R62611 : Reach 62611 := rs (se 1 (by rfl) ⟨46958, by rfl⟩) R93917
theorem R62627 : Reach 62627 := rs (se 1 (by rfl) ⟨46970, by rfl⟩) R93941
theorem R62643 : Reach 62643 := rs (se 1 (by rfl) ⟨46982, by rfl⟩) R93965
theorem R62659 : Reach 62659 := rs (se 1 (by rfl) ⟨46994, by rfl⟩) R93989
theorem R62675 : Reach 62675 := rs (se 1 (by rfl) ⟨47006, by rfl⟩) R94013
theorem R62691 : Reach 62691 := rs (se 1 (by rfl) ⟨47018, by rfl⟩) R94037
theorem R62707 : Reach 62707 := rs (se 1 (by rfl) ⟨47030, by rfl⟩) R94061
theorem R62723 : Reach 62723 := rs (se 1 (by rfl) ⟨47042, by rfl⟩) R94085
theorem R95507 : Reach 95507 := rs (se 1 (by rfl) ⟨71630, by rfl⟩) R143261
theorem R62739 : Reach 62739 := rs (se 1 (by rfl) ⟨47054, by rfl⟩) R94109
theorem R62755 : Reach 62755 := rs (se 1 (by rfl) ⟨47066, by rfl⟩) R94133
theorem R62771 : Reach 62771 := rs (se 1 (by rfl) ⟨47078, by rfl⟩) R94157
theorem R62787 : Reach 62787 := rs (se 1 (by rfl) ⟨47090, by rfl⟩) R94181
theorem R62803 : Reach 62803 := rs (se 1 (by rfl) ⟨47102, by rfl⟩) R94205
theorem R62819 : Reach 62819 := rs (se 1 (by rfl) ⟨47114, by rfl⟩) R94229
theorem R62835 : Reach 62835 := rs (se 1 (by rfl) ⟨47126, by rfl⟩) R94253
theorem R62851 : Reach 62851 := rs (se 1 (by rfl) ⟨47138, by rfl⟩) R94277
theorem R259469 : Reach 259469 := rs (se 3 (by rfl) ⟨48650, by rfl⟩) R97301
theorem R62867 : Reach 62867 := rs (se 1 (by rfl) ⟨47150, by rfl⟩) R94301
theorem R62883 : Reach 62883 := rs (se 1 (by rfl) ⟨47162, by rfl⟩) R94325
theorem R62899 : Reach 62899 := rs (se 1 (by rfl) ⟨47174, by rfl⟩) R94349
theorem R62915 : Reach 62915 := rs (se 1 (by rfl) ⟨47186, by rfl⟩) R94373
theorem R62931 : Reach 62931 := rs (se 1 (by rfl) ⟨47198, by rfl⟩) R94397
theorem R128483 : Reach 128483 := rs (se 1 (by rfl) ⟨96362, by rfl⟩) R192725
theorem R62947 : Reach 62947 := rs (se 1 (by rfl) ⟨47210, by rfl⟩) R94421
theorem R62963 : Reach 62963 := rs (se 1 (by rfl) ⟨47222, by rfl⟩) R94445
theorem R194051 : Reach 194051 := rs (se 1 (by rfl) ⟨145538, by rfl⟩) R291077
theorem R62979 : Reach 62979 := rs (se 1 (by rfl) ⟨47234, by rfl⟩) R94469
theorem R62995 : Reach 62995 := rs (se 1 (by rfl) ⟨47246, by rfl⟩) R94493
theorem R63011 : Reach 63011 := rs (se 1 (by rfl) ⟨47258, by rfl⟩) R94517
theorem R63027 : Reach 63027 := rs (se 1 (by rfl) ⟨47270, by rfl⟩) R94541
theorem R63043 : Reach 63043 := rs (se 1 (by rfl) ⟨47282, by rfl⟩) R94565
theorem R63059 : Reach 63059 := rs (se 1 (by rfl) ⟨47294, by rfl⟩) R94589
theorem R63075 : Reach 63075 := rs (se 1 (by rfl) ⟨47306, by rfl⟩) R94613
theorem R63091 : Reach 63091 := rs (se 1 (by rfl) ⟨47318, by rfl⟩) R94637
theorem R63107 : Reach 63107 := rs (se 1 (by rfl) ⟨47330, by rfl⟩) R94661
theorem R96211 : Reach 96211 := rs (se 1 (by rfl) ⟨72158, by rfl⟩) R144317
theorem R325795 : Reach 325795 := rs (se 1 (by rfl) ⟨244346, by rfl⟩) R488693
theorem R358577 : Reach 358577 := rs (se 2 (by rfl) ⟨134466, by rfl⟩) R268933
theorem R1308869 : Reach 1308869 := rs (se 4 (by rfl) ⟨122706, by rfl⟩) R245413
theorem R96481 : Reach 96481 := rs (se 2 (by rfl) ⟨36180, by rfl⟩) R72361
theorem R227555 : Reach 227555 := rs (se 1 (by rfl) ⟨170666, by rfl⟩) R341333
theorem R227569 : Reach 227569 := rs (se 2 (by rfl) ⟨85338, by rfl⟩) R170677
theorem R96545 : Reach 96545 := rs (se 2 (by rfl) ⟨36204, by rfl⟩) R72409
theorem R489797 : Reach 489797 := rs (se 4 (by rfl) ⟨45918, by rfl⟩) R91837
theorem R96641 : Reach 96641 := rs (se 2 (by rfl) ⟨36240, by rfl⟩) R72481
theorem R129443 : Reach 129443 := rs (se 1 (by rfl) ⟨97082, by rfl⟩) R194165
theorem R391715 : Reach 391715 := rs (se 1 (by rfl) ⟨293786, by rfl⟩) R587573
theorem R195139 : Reach 195139 := rs (se 1 (by rfl) ⟨146354, by rfl⟩) R292709
theorem R195281 : Reach 195281 := rs (se 2 (by rfl) ⟨73230, by rfl⟩) R146461
theorem R3013685 : Reach 3013685 := rs (se 5 (by rfl) ⟨141266, by rfl⟩) R282533
theorem R64739 : Reach 64739 := rs (se 1 (by rfl) ⟨48554, by rfl⟩) R97109
theorem R1441165 : Reach 1441165 := rs (se 3 (by rfl) ⟨270218, by rfl⟩) R540437
theorem R654961 : Reach 654961 := rs (se 2 (by rfl) ⟨245610, by rfl⟩) R491221
theorem R229027 : Reach 229027 := rs (se 1 (by rfl) ⟨171770, by rfl⟩) R343541
theorem R98275 : Reach 98275 := rs (se 1 (by rfl) ⟨73706, by rfl⟩) R147413
theorem R524333 : Reach 524333 := rs (se 3 (by rfl) ⟨98312, by rfl⟩) R196625
theorem R983171 : Reach 983171 := rs (se 1 (by rfl) ⟨737378, by rfl⟩) R1474757
theorem R163991 : Reach 163991 := rs (se 1 (by rfl) ⟨122993, by rfl⟩) R245987
theorem R65815 : Reach 65815 := rs (se 1 (by rfl) ⟨49361, by rfl⟩) R98723
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R328153 : Reach 328153 := rs (se 2 (by rfl) ⟨123057, by rfl⟩) R246115
theorem R459269 : Reach 459269 := rs (se 4 (by rfl) ⟨43056, by rfl⟩) R86113
theorem R98903 : Reach 98903 := rs (se 1 (by rfl) ⟨74177, by rfl⟩) R148355
theorem R131699 : Reach 131699 := rs (se 1 (by rfl) ⟨98774, by rfl⟩) R197549
theorem R66187 : Reach 66187 := rs (se 1 (by rfl) ⟨49640, by rfl⟩) R99281
theorem R262835 : Reach 262835 := rs (se 1 (by rfl) ⟨197126, by rfl⟩) R394253
theorem R131801 : Reach 131801 := rs (se 2 (by rfl) ⟨49425, by rfl⟩) R98851
theorem R99287 : Reach 99287 := rs (se 1 (by rfl) ⟨74465, by rfl⟩) R148931
theorem R99415 : Reach 99415 := rs (se 1 (by rfl) ⟨74561, by rfl⟩) R149123
theorem R66667 : Reach 66667 := rs (se 1 (by rfl) ⟨50000, by rfl⟩) R100001
theorem R66775 : Reach 66775 := rs (se 1 (by rfl) ⟨50081, by rfl⟩) R100163
theorem R66955 : Reach 66955 := rs (se 1 (by rfl) ⟨50216, by rfl⟩) R100433
theorem R165341 : Reach 165341 := rs (se 3 (by rfl) ⟨31001, by rfl⟩) R62003
theorem R67063 : Reach 67063 := rs (se 1 (by rfl) ⟨50297, by rfl⟩) R100595
theorem R230957 : Reach 230957 := rs (se 3 (by rfl) ⟨43304, by rfl⟩) R86609
theorem R132673 : Reach 132673 := rs (se 2 (by rfl) ⟨49752, by rfl⟩) R99505
theorem R67243 : Reach 67243 := rs (se 1 (by rfl) ⟨50432, by rfl⟩) R100865
theorem R100055 : Reach 100055 := rs (se 1 (by rfl) ⟨75041, by rfl⟩) R150083
theorem R67351 : Reach 67351 := rs (se 1 (by rfl) ⟨50513, by rfl⟩) R101027
theorem R132929 : Reach 132929 := rs (se 2 (by rfl) ⟨49848, by rfl⟩) R99697
theorem R100183 : Reach 100183 := rs (se 1 (by rfl) ⟨75137, by rfl⟩) R150275
theorem R100235 : Reach 100235 := rs (se 1 (by rfl) ⟨75176, by rfl⟩) R150353
theorem R133015 : Reach 133015 := rs (se 1 (by rfl) ⟨99761, by rfl⟩) R199523
theorem R67531 : Reach 67531 := rs (se 1 (by rfl) ⟨50648, by rfl⟩) R101297
theorem R526297 : Reach 526297 := rs (se 2 (by rfl) ⟨197361, by rfl⟩) R394723
theorem R100363 : Reach 100363 := rs (se 1 (by rfl) ⟨75272, by rfl⟩) R150545
theorem R133145 : Reach 133145 := rs (se 2 (by rfl) ⟨49929, by rfl⟩) R99859
theorem R67639 : Reach 67639 := rs (se 1 (by rfl) ⟨50729, by rfl⟩) R101459
theorem R133235 : Reach 133235 := rs (se 1 (by rfl) ⟨99926, by rfl⟩) R199853
theorem R133271 : Reach 133271 := rs (se 1 (by rfl) ⟨99953, by rfl⟩) R199907
theorem R362675 : Reach 362675 := rs (se 1 (by rfl) ⟨272006, by rfl⟩) R544013
theorem R67819 : Reach 67819 := rs (se 1 (by rfl) ⟨50864, by rfl⟩) R101729
theorem R166195 : Reach 166195 := rs (se 1 (by rfl) ⟨124646, by rfl⟩) R249293
theorem R231731 : Reach 231731 := rs (se 1 (by rfl) ⟨173798, by rfl⟩) R347597
theorem R919873 : Reach 919873 := rs (se 2 (by rfl) ⟨344952, by rfl⟩) R689905
theorem R133451 : Reach 133451 := rs (se 1 (by rfl) ⟨100088, by rfl⟩) R200177
theorem R67927 : Reach 67927 := rs (se 1 (by rfl) ⟨50945, by rfl⟩) R101891
theorem R133505 : Reach 133505 := rs (se 2 (by rfl) ⟨50064, by rfl⟩) R100129
theorem R100811 : Reach 100811 := rs (se 1 (by rfl) ⟨75608, by rfl⟩) R151217
theorem R68107 : Reach 68107 := rs (se 1 (by rfl) ⟨51080, by rfl⟩) R102161
theorem R100939 : Reach 100939 := rs (se 1 (by rfl) ⟨75704, by rfl⟩) R151409
theorem R133721 : Reach 133721 := rs (se 2 (by rfl) ⟨50145, by rfl⟩) R100291
theorem R68215 : Reach 68215 := rs (se 1 (by rfl) ⟨51161, by rfl⟩) R102323
theorem R133811 : Reach 133811 := rs (se 1 (by rfl) ⟨100358, by rfl⟩) R200717
theorem R133847 : Reach 133847 := rs (se 1 (by rfl) ⟨100385, by rfl⟩) R200771
theorem R101081 : Reach 101081 := rs (se 2 (by rfl) ⟨37905, by rfl⟩) R75811
theorem R68395 : Reach 68395 := rs (se 1 (by rfl) ⟨51296, by rfl⟩) R102593
theorem R101209 : Reach 101209 := rs (se 2 (by rfl) ⟨37953, by rfl⟩) R75907
theorem R461699 : Reach 461699 := rs (se 1 (by rfl) ⟨346274, by rfl⟩) R692549
theorem R134027 : Reach 134027 := rs (se 1 (by rfl) ⟨100520, by rfl⟩) R201041
theorem R68503 : Reach 68503 := rs (se 1 (by rfl) ⟨51377, by rfl⟩) R102755
theorem R134081 : Reach 134081 := rs (se 2 (by rfl) ⟨50280, by rfl⟩) R100561
theorem R527309 : Reach 527309 := rs (se 3 (by rfl) ⟨98870, by rfl⟩) R197741
theorem R199745 : Reach 199745 := rs (se 2 (by rfl) ⟨74904, by rfl⟩) R149809
theorem R68683 : Reach 68683 := rs (se 1 (by rfl) ⟨51512, by rfl⟩) R103025
theorem R134297 : Reach 134297 := rs (se 2 (by rfl) ⟨50361, by rfl⟩) R100723
theorem R68791 : Reach 68791 := rs (se 1 (by rfl) ⟨51593, by rfl⟩) R103187
theorem R199883 : Reach 199883 := rs (se 1 (by rfl) ⟨149912, by rfl⟩) R299825
theorem R134387 : Reach 134387 := rs (se 1 (by rfl) ⟨100790, by rfl⟩) R201581
theorem R1019141 : Reach 1019141 := rs (se 4 (by rfl) ⟨95544, by rfl⟩) R191089
theorem R134423 : Reach 134423 := rs (se 1 (by rfl) ⟨100817, by rfl⟩) R201635
theorem R265517 : Reach 265517 := rs (se 3 (by rfl) ⟨49784, by rfl⟩) R99569
theorem R68971 : Reach 68971 := rs (se 1 (by rfl) ⟨51728, by rfl⟩) R103457
theorem R101783 : Reach 101783 := rs (se 1 (by rfl) ⟨76337, by rfl⟩) R152675
theorem R134603 : Reach 134603 := rs (se 1 (by rfl) ⟨100952, by rfl⟩) R201905
theorem R69079 : Reach 69079 := rs (se 1 (by rfl) ⟨51809, by rfl⟩) R103619
theorem R134657 : Reach 134657 := rs (se 2 (by rfl) ⟨50496, by rfl⟩) R100993
theorem R101911 : Reach 101911 := rs (se 1 (by rfl) ⟨76433, by rfl⟩) R152867
theorem R200285 : Reach 200285 := rs (se 3 (by rfl) ⟨37553, by rfl⟩) R75107
theorem R69259 : Reach 69259 := rs (se 1 (by rfl) ⟨51944, by rfl⟩) R103889
theorem R134873 : Reach 134873 := rs (se 2 (by rfl) ⟨50577, by rfl⟩) R101155
theorem R69367 : Reach 69367 := rs (se 1 (by rfl) ⟨52025, by rfl⟩) R104051
theorem R233219 : Reach 233219 := rs (se 1 (by rfl) ⟨174914, by rfl⟩) R349829
theorem R134963 : Reach 134963 := rs (se 1 (by rfl) ⟨101222, by rfl⟩) R202445
theorem R134999 : Reach 134999 := rs (se 1 (by rfl) ⟨101249, by rfl⟩) R202499
theorem R69547 : Reach 69547 := rs (se 1 (by rfl) ⟨52160, by rfl⟩) R104321
theorem R135179 : Reach 135179 := rs (se 1 (by rfl) ⟨101384, by rfl⟩) R202769
theorem R331793 : Reach 331793 := rs (se 2 (by rfl) ⟨124422, by rfl⟩) R248845
theorem R69655 : Reach 69655 := rs (se 1 (by rfl) ⟨52241, by rfl⟩) R104483
theorem R757795 : Reach 757795 := rs (se 1 (by rfl) ⟨568346, by rfl⟩) R1136693
theorem R135233 : Reach 135233 := rs (se 2 (by rfl) ⟨50712, by rfl⟩) R101425
theorem R102539 : Reach 102539 := rs (se 1 (by rfl) ⟨76904, by rfl⟩) R153809
theorem R200855 : Reach 200855 := rs (se 1 (by rfl) ⟨150641, by rfl⟩) R301283
theorem R233675 : Reach 233675 := rs (se 1 (by rfl) ⟨175256, by rfl⟩) R350513
theorem R69835 : Reach 69835 := rs (se 1 (by rfl) ⟨52376, by rfl⟩) R104753
theorem R102667 : Reach 102667 := rs (se 1 (by rfl) ⟨77000, by rfl⟩) R154001
theorem R135449 : Reach 135449 := rs (se 2 (by rfl) ⟨50793, by rfl⟩) R101587
theorem R69943 : Reach 69943 := rs (se 1 (by rfl) ⟨52457, by rfl⟩) R104915
theorem R135539 : Reach 135539 := rs (se 1 (by rfl) ⟨101654, by rfl⟩) R203309
theorem R233873 : Reach 233873 := rs (se 2 (by rfl) ⟨87702, by rfl⟩) R175405
theorem R135575 : Reach 135575 := rs (se 1 (by rfl) ⟨101681, by rfl⟩) R203363
theorem R102809 : Reach 102809 := rs (se 2 (by rfl) ⟨38553, by rfl⟩) R77107
theorem R201163 : Reach 201163 := rs (se 1 (by rfl) ⟨150872, by rfl⟩) R301745
theorem R299537 : Reach 299537 := rs (se 2 (by rfl) ⟨112326, by rfl⟩) R224653
theorem R102937 : Reach 102937 := rs (se 2 (by rfl) ⟨38601, by rfl⟩) R77203
theorem R889379 : Reach 889379 := rs (se 1 (by rfl) ⟨667034, by rfl⟩) R1334069
theorem R135755 : Reach 135755 := rs (se 1 (by rfl) ⟨101816, by rfl⟩) R203633
theorem R70231 : Reach 70231 := rs (se 1 (by rfl) ⟨52673, by rfl⟩) R105347
theorem R135809 : Reach 135809 := rs (se 2 (by rfl) ⟨50928, by rfl⟩) R101857
theorem R299699 : Reach 299699 := rs (se 1 (by rfl) ⟨224774, by rfl⟩) R449549
theorem R201419 : Reach 201419 := rs (se 1 (by rfl) ⟨151064, by rfl⟩) R302129
theorem R70411 : Reach 70411 := rs (se 1 (by rfl) ⟨52808, by rfl⟩) R105617
theorem R136025 : Reach 136025 := rs (se 2 (by rfl) ⟨51009, by rfl⟩) R102019
theorem R136115 : Reach 136115 := rs (se 1 (by rfl) ⟨102086, by rfl⟩) R204173
theorem R136151 : Reach 136151 := rs (se 1 (by rfl) ⟨102113, by rfl⟩) R204227
theorem R201689 : Reach 201689 := rs (se 2 (by rfl) ⟨75633, by rfl⟩) R151267
theorem R103511 : Reach 103511 := rs (se 1 (by rfl) ⟨77633, by rfl⟩) R155267
theorem R398429 : Reach 398429 := rs (se 3 (by rfl) ⟨74705, by rfl⟩) R149411
theorem R136331 : Reach 136331 := rs (se 1 (by rfl) ⟨102248, by rfl⟩) R204497
theorem R234647 : Reach 234647 := rs (se 1 (by rfl) ⟨175985, by rfl⟩) R351971
theorem R70807 : Reach 70807 := rs (se 1 (by rfl) ⟨53105, by rfl⟩) R106211
theorem R136385 : Reach 136385 := rs (se 2 (by rfl) ⟨51144, by rfl⟩) R102289
theorem R103639 : Reach 103639 := rs (se 1 (by rfl) ⟨77729, by rfl⟩) R155459
theorem R70987 : Reach 70987 := rs (se 1 (by rfl) ⟨53240, by rfl⟩) R106481
theorem R234845 : Reach 234845 := rs (se 3 (by rfl) ⟨44033, by rfl⟩) R88067
theorem R136601 : Reach 136601 := rs (se 2 (by rfl) ⟨51225, by rfl⟩) R102451
theorem R136691 : Reach 136691 := rs (se 1 (by rfl) ⟨102518, by rfl⟩) R205037
theorem R136727 : Reach 136727 := rs (se 1 (by rfl) ⟨102545, by rfl⟩) R205091
theorem R202391 : Reach 202391 := rs (se 1 (by rfl) ⟨151793, by rfl⟩) R303587
theorem R136907 : Reach 136907 := rs (se 1 (by rfl) ⟨102680, by rfl⟩) R205361
theorem R136961 : Reach 136961 := rs (se 2 (by rfl) ⟨51360, by rfl⟩) R102721
theorem R104267 : Reach 104267 := rs (se 1 (by rfl) ⟨78200, by rfl⟩) R156401
theorem R104395 : Reach 104395 := rs (se 1 (by rfl) ⟨78296, by rfl⟩) R156593
theorem R137177 : Reach 137177 := rs (se 2 (by rfl) ⟨51441, by rfl⟩) R102883
theorem R137267 : Reach 137267 := rs (se 1 (by rfl) ⟨102950, by rfl⟩) R205901
theorem R5150789 : Reach 5150789 := rs (se 4 (by rfl) ⟨482886, by rfl⟩) R965773
theorem R137303 : Reach 137303 := rs (se 1 (by rfl) ⟨102977, by rfl⟩) R205955
theorem R137305 : Reach 137305 := rs (se 2 (by rfl) ⟨51489, by rfl⟩) R102979
theorem R104537 : Reach 104537 := rs (se 2 (by rfl) ⟨39201, by rfl⟩) R78403
theorem R202931 : Reach 202931 := rs (se 1 (by rfl) ⟨152198, by rfl⟩) R304397
theorem R465101 : Reach 465101 := rs (se 3 (by rfl) ⟨87206, by rfl⟩) R174413
theorem R104665 : Reach 104665 := rs (se 2 (by rfl) ⟨39249, by rfl⟩) R78499
theorem R71947 : Reach 71947 := rs (se 1 (by rfl) ⟨53960, by rfl⟩) R107921
theorem R137483 : Reach 137483 := rs (se 1 (by rfl) ⟨103112, by rfl⟩) R206225
theorem R137537 : Reach 137537 := rs (se 2 (by rfl) ⟨51576, by rfl⟩) R103153
theorem R203201 : Reach 203201 := rs (se 2 (by rfl) ⟨76200, by rfl⟩) R152401
theorem R137753 : Reach 137753 := rs (se 2 (by rfl) ⟨51657, by rfl⟩) R103315
theorem R268865 : Reach 268865 := rs (se 2 (by rfl) ⟨100824, by rfl⟩) R201649
theorem R301643 : Reach 301643 := rs (se 1 (by rfl) ⟨226232, by rfl⟩) R452465
theorem R137843 : Reach 137843 := rs (se 1 (by rfl) ⟨103382, by rfl⟩) R206765
theorem R137857 : Reach 137857 := rs (se 2 (by rfl) ⟨51696, by rfl⟩) R103393
theorem R137879 : Reach 137879 := rs (se 1 (by rfl) ⟨103409, by rfl⟩) R206819
theorem R465587 : Reach 465587 := rs (se 1 (by rfl) ⟨349190, by rfl⟩) R698381
theorem R203543 : Reach 203543 := rs (se 1 (by rfl) ⟨152657, by rfl⟩) R305315
theorem R105239 : Reach 105239 := rs (se 1 (by rfl) ⟨78929, by rfl⟩) R157859
theorem R138059 : Reach 138059 := rs (se 1 (by rfl) ⟨103544, by rfl⟩) R207089
theorem R138113 : Reach 138113 := rs (se 2 (by rfl) ⟨51792, by rfl⟩) R103585
theorem R105367 : Reach 105367 := rs (se 1 (by rfl) ⟨79025, by rfl⟩) R158051
theorem R269207 : Reach 269207 := rs (se 1 (by rfl) ⟨201905, by rfl⟩) R403811
theorem R596915 : Reach 596915 := rs (se 1 (by rfl) ⟨447686, by rfl⟩) R895373
theorem R1252313 : Reach 1252313 := rs (se 2 (by rfl) ⟨469617, by rfl⟩) R939235
theorem R203741 : Reach 203741 := rs (se 3 (by rfl) ⟨38201, by rfl⟩) R76403
theorem R171031 : Reach 171031 := rs (se 1 (by rfl) ⟨128273, by rfl⟩) R256547
theorem R138329 : Reach 138329 := rs (se 2 (by rfl) ⟨51873, by rfl⟩) R103747
theorem R138419 : Reach 138419 := rs (se 1 (by rfl) ⟨103814, by rfl⟩) R207629
theorem R138455 : Reach 138455 := rs (se 1 (by rfl) ⟨103841, by rfl⟩) R207683
theorem R236803 : Reach 236803 := rs (se 1 (by rfl) ⟨177602, by rfl⟩) R355205
theorem R105779 : Reach 105779 := rs (se 1 (by rfl) ⟨79334, by rfl⟩) R158669
theorem R138635 : Reach 138635 := rs (se 1 (by rfl) ⟨103976, by rfl⟩) R207953
theorem R499121 : Reach 499121 := rs (se 2 (by rfl) ⟨187170, by rfl⟩) R374341
theorem R105907 : Reach 105907 := rs (se 1 (by rfl) ⟨79430, by rfl⟩) R158861
theorem R138689 : Reach 138689 := rs (se 2 (by rfl) ⟨52008, by rfl⟩) R104017
theorem R105931 : Reach 105931 := rs (se 1 (by rfl) ⟨79448, by rfl⟩) R158897
theorem R105995 : Reach 105995 := rs (se 1 (by rfl) ⟨79496, by rfl⟩) R158993
theorem R237107 : Reach 237107 := rs (se 1 (by rfl) ⟨177830, by rfl⟩) R355661
theorem R106049 : Reach 106049 := rs (se 2 (by rfl) ⟨39768, by rfl⟩) R79537
theorem R368221 : Reach 368221 := rs (se 3 (by rfl) ⟨69041, by rfl⟩) R138083
theorem R106123 : Reach 106123 := rs (se 1 (by rfl) ⟨79592, by rfl⟩) R159185
theorem R138905 : Reach 138905 := rs (se 2 (by rfl) ⟨52089, by rfl⟩) R104179
theorem R106177 : Reach 106177 := rs (se 2 (by rfl) ⟨39816, by rfl⟩) R79633
theorem R138995 : Reach 138995 := rs (se 1 (by rfl) ⟨104246, by rfl⟩) R208493
theorem R139031 : Reach 139031 := rs (se 1 (by rfl) ⟨104273, by rfl⟩) R208547
theorem R106265 : Reach 106265 := rs (se 2 (by rfl) ⟨39849, by rfl⟩) R79699
theorem R106393 : Reach 106393 := rs (se 2 (by rfl) ⟨39897, by rfl⟩) R79795
theorem R139211 : Reach 139211 := rs (se 1 (by rfl) ⟨104408, by rfl⟩) R208817
theorem R892889 : Reach 892889 := rs (se 2 (by rfl) ⟨334833, by rfl⟩) R669667
theorem R139265 : Reach 139265 := rs (se 2 (by rfl) ⟨52224, by rfl⟩) R104449
theorem R204875 : Reach 204875 := rs (se 1 (by rfl) ⟨153656, by rfl⟩) R307313
theorem R467045 : Reach 467045 := rs (se 4 (by rfl) ⟨43785, by rfl⟩) R87571
theorem R1614005 : Reach 1614005 := rs (se 5 (by rfl) ⟨75656, by rfl⟩) R151313
theorem R237761 : Reach 237761 := rs (se 2 (by rfl) ⟨89160, by rfl⟩) R178321
theorem R434393 : Reach 434393 := rs (se 2 (by rfl) ⟨162897, by rfl⟩) R325795
theorem R139481 : Reach 139481 := rs (se 2 (by rfl) ⟨52305, by rfl⟩) R104611
theorem R139571 : Reach 139571 := rs (se 1 (by rfl) ⟨104678, by rfl⟩) R209357
theorem R303425 : Reach 303425 := rs (se 2 (by rfl) ⟨113784, by rfl⟩) R227569
theorem R74059 : Reach 74059 := rs (se 1 (by rfl) ⟨55544, by rfl⟩) R111089
theorem R172363 : Reach 172363 := rs (se 1 (by rfl) ⟨129272, by rfl⟩) R258545
theorem R139607 : Reach 139607 := rs (se 1 (by rfl) ⟨104705, by rfl⟩) R209411
theorem R205145 : Reach 205145 := rs (se 2 (by rfl) ⟨76929, by rfl⟩) R153859
theorem R139787 : Reach 139787 := rs (se 1 (by rfl) ⟨104840, by rfl⟩) R209681
theorem R139801 : Reach 139801 := rs (se 2 (by rfl) ⟨52425, by rfl⟩) R104851
theorem R139841 : Reach 139841 := rs (se 2 (by rfl) ⟨52440, by rfl⟩) R104881
theorem R467531 : Reach 467531 := rs (se 1 (by rfl) ⟨350648, by rfl⟩) R701297
theorem R172637 : Reach 172637 := rs (se 3 (by rfl) ⟨32369, by rfl⟩) R64739
theorem R140057 : Reach 140057 := rs (se 2 (by rfl) ⟨52521, by rfl⟩) R105043
theorem R140183 : Reach 140183 := rs (se 1 (by rfl) ⟨105137, by rfl⟩) R210275
theorem R172979 : Reach 172979 := rs (se 1 (by rfl) ⟨129734, by rfl⟩) R259469
theorem R205847 : Reach 205847 := rs (se 1 (by rfl) ⟨154385, by rfl⟩) R308771
theorem R140363 : Reach 140363 := rs (se 1 (by rfl) ⟨105272, by rfl⟩) R210545
theorem R74839 : Reach 74839 := rs (se 1 (by rfl) ⟨56129, by rfl⟩) R112259
theorem R107777 : Reach 107777 := rs (se 2 (by rfl) ⟨40416, by rfl⟩) R80833
theorem R238913 : Reach 238913 := rs (se 2 (by rfl) ⟨89592, by rfl⟩) R179185
theorem R140633 : Reach 140633 := rs (se 2 (by rfl) ⟨52737, by rfl⟩) R105475
theorem R239021 : Reach 239021 := rs (se 3 (by rfl) ⟨44816, by rfl⟩) R89633
theorem R140723 : Reach 140723 := rs (se 1 (by rfl) ⟨105542, by rfl⟩) R211085
theorem R239051 : Reach 239051 := rs (se 1 (by rfl) ⟨179288, by rfl⟩) R358577
theorem R468497 : Reach 468497 := rs (se 2 (by rfl) ⟨175686, by rfl⟩) R351373
theorem R402961 : Reach 402961 := rs (se 2 (by rfl) ⟨151110, by rfl⟩) R302221
theorem R206387 : Reach 206387 := rs (se 1 (by rfl) ⟨154790, by rfl⟩) R309581
theorem R140993 : Reach 140993 := rs (se 2 (by rfl) ⟨52872, by rfl⟩) R105745
theorem R337709 : Reach 337709 := rs (se 3 (by rfl) ⟨63320, by rfl⟩) R126641
theorem R206657 : Reach 206657 := rs (se 2 (by rfl) ⟨77496, by rfl⟩) R154993
theorem R141335 : Reach 141335 := rs (se 1 (by rfl) ⟨106001, by rfl⟩) R212003
theorem R2009123 : Reach 2009123 := rs (se 1 (by rfl) ⟨1506842, by rfl⟩) R3013685
theorem R141515 : Reach 141515 := rs (se 1 (by rfl) ⟨106136, by rfl⟩) R212273
theorem R305369 : Reach 305369 := rs (se 2 (by rfl) ⟨114513, by rfl⟩) R229027
theorem R272605 : Reach 272605 := rs (se 3 (by rfl) ⟨51113, by rfl⟩) R102227
theorem R338251 : Reach 338251 := rs (se 1 (by rfl) ⟨253688, by rfl⟩) R507377
theorem R207197 : Reach 207197 := rs (se 3 (by rfl) ⟨38849, by rfl⟩) R77699
theorem R76235 : Reach 76235 := rs (se 1 (by rfl) ⟨57176, by rfl⟩) R114353
theorem R141785 : Reach 141785 := rs (se 2 (by rfl) ⟨53169, by rfl⟩) R106339
theorem R141875 : Reach 141875 := rs (se 1 (by rfl) ⟨106406, by rfl⟩) R212813
theorem R76555 : Reach 76555 := rs (se 1 (by rfl) ⟨57416, by rfl⟩) R114833
theorem R240407 : Reach 240407 := rs (se 1 (by rfl) ⟨180305, by rfl⟩) R360611
theorem R273227 : Reach 273227 := rs (se 1 (by rfl) ⟨204920, by rfl⟩) R409841
theorem R175051 : Reach 175051 := rs (se 1 (by rfl) ⟨131288, by rfl⟩) R262577
theorem R470195 : Reach 470195 := rs (se 1 (by rfl) ⟨352646, by rfl⟩) R705293
theorem R77015 : Reach 77015 := rs (se 1 (by rfl) ⟨57761, by rfl⟩) R115523
theorem R109847 : Reach 109847 := rs (se 1 (by rfl) ⟨82385, by rfl⟩) R164771
theorem R175553 : Reach 175553 := rs (se 2 (by rfl) ⟨65832, by rfl⟩) R131665
theorem R208331 : Reach 208331 := rs (se 1 (by rfl) ⟨156248, by rfl⟩) R312497
theorem R437795 : Reach 437795 := rs (se 1 (by rfl) ⟨328346, by rfl⟩) R656693
theorem R339635 : Reach 339635 := rs (se 1 (by rfl) ⟨254726, by rfl⟩) R509453
theorem R77527 : Reach 77527 := rs (se 1 (by rfl) ⟨58145, by rfl⟩) R116291
theorem R208601 : Reach 208601 := rs (se 2 (by rfl) ⟨78225, by rfl⟩) R156451
theorem R175895 : Reach 175895 := rs (se 1 (by rfl) ⟨131921, by rfl⟩) R263843
theorem R306989 : Reach 306989 := rs (se 3 (by rfl) ⟨57560, by rfl⟩) R115121
theorem R110423 : Reach 110423 := rs (se 1 (by rfl) ⟨82817, by rfl⟩) R165635
theorem R241501 : Reach 241501 := rs (se 3 (by rfl) ⟨45281, by rfl⟩) R90563
theorem R569267 : Reach 569267 := rs (se 1 (by rfl) ⟨426950, by rfl⟩) R853901
theorem R143411 : Reach 143411 := rs (se 1 (by rfl) ⟨107558, by rfl⟩) R215117
theorem R209303 : Reach 209303 := rs (se 1 (by rfl) ⟨156977, by rfl⟩) R313955
theorem R143819 : Reach 143819 := rs (se 1 (by rfl) ⟨107864, by rfl⟩) R215729
theorem R78347 : Reach 78347 := rs (se 1 (by rfl) ⟨58760, by rfl⟩) R117521
theorem R111179 : Reach 111179 := rs (se 1 (by rfl) ⟨83384, by rfl⟩) R166769
theorem R340631 : Reach 340631 := rs (se 1 (by rfl) ⟨255473, by rfl⟩) R510947
theorem R635825 : Reach 635825 := rs (se 2 (by rfl) ⟨238434, by rfl⟩) R476869
theorem R209843 : Reach 209843 := rs (se 1 (by rfl) ⟨157382, by rfl⟩) R314765
theorem R210113 : Reach 210113 := rs (se 2 (by rfl) ⟨78792, by rfl⟩) R157585
theorem R79051 : Reach 79051 := rs (se 1 (by rfl) ⟨59288, by rfl⟩) R118577
theorem R275729 : Reach 275729 := rs (se 2 (by rfl) ⟨103398, by rfl⟩) R206797
theorem R210221 : Reach 210221 := rs (se 3 (by rfl) ⟨39416, by rfl⟩) R78833
theorem R79319 : Reach 79319 := rs (se 1 (by rfl) ⟨59489, by rfl⟩) R118979
theorem R341597 : Reach 341597 := rs (se 3 (by rfl) ⟨64049, by rfl⟩) R128099
theorem R210653 : Reach 210653 := rs (se 3 (by rfl) ⟨39497, by rfl⟩) R78995
theorem R472877 : Reach 472877 := rs (se 3 (by rfl) ⟨88664, by rfl⟩) R177329
theorem R178013 : Reach 178013 := rs (se 3 (by rfl) ⟨33377, by rfl⟩) R66755
theorem R79897 : Reach 79897 := rs (se 2 (by rfl) ⟨29961, by rfl⟩) R59923
theorem R112691 : Reach 112691 := rs (se 1 (by rfl) ⟨84518, by rfl⟩) R169037
theorem R79961 : Reach 79961 := rs (se 2 (by rfl) ⟨29985, by rfl⟩) R59971
theorem R80023 : Reach 80023 := rs (se 1 (by rfl) ⟨60017, by rfl⟩) R120035
theorem R112793 : Reach 112793 := rs (se 2 (by rfl) ⟨42297, by rfl⟩) R84595
theorem R178355 : Reach 178355 := rs (se 1 (by rfl) ⟨133766, by rfl⟩) R267533
theorem R112843 : Reach 112843 := rs (se 1 (by rfl) ⟨84632, by rfl⟩) R169265
theorem R80395 : Reach 80395 := rs (se 1 (by rfl) ⟨60296, by rfl⟩) R120593
theorem R113177 : Reach 113177 := rs (se 2 (by rfl) ⟨42441, by rfl⟩) R84883
theorem R178967 : Reach 178967 := rs (se 1 (by rfl) ⟨134225, by rfl⟩) R268451
theorem R375617 : Reach 375617 := rs (se 2 (by rfl) ⟨140856, by rfl⟩) R281713
theorem R211787 : Reach 211787 := rs (se 1 (by rfl) ⟨158840, by rfl⟩) R317681
theorem R113537 : Reach 113537 := rs (se 2 (by rfl) ⟨42576, by rfl⟩) R85153
theorem R212057 : Reach 212057 := rs (se 2 (by rfl) ⟨79521, by rfl⟩) R159043
theorem R113815 : Reach 113815 := rs (se 1 (by rfl) ⟨85361, by rfl⟩) R170723
theorem R146777 : Reach 146777 := rs (se 2 (by rfl) ⟨55041, by rfl⟩) R110083
theorem R310877 : Reach 310877 := rs (se 3 (by rfl) ⟨58289, by rfl⟩) R116579
theorem R179915 : Reach 179915 := rs (se 1 (by rfl) ⟨134936, by rfl⟩) R269873
theorem R212759 : Reach 212759 := rs (se 1 (by rfl) ⟨159569, by rfl⟩) R319139
theorem R212867 : Reach 212867 := rs (se 1 (by rfl) ⟨159650, by rfl⟩) R319301
theorem R114635 : Reach 114635 := rs (se 1 (by rfl) ⟨85976, by rfl⟩) R171953
theorem R114689 : Reach 114689 := rs (se 2 (by rfl) ⟨43008, by rfl⟩) R86017
theorem R443141 : Reach 443141 := rs (se 4 (by rfl) ⟨41544, by rfl⟩) R83089
theorem R770917 : Reach 770917 := rs (se 4 (by rfl) ⟨72273, by rfl⟩) R144547
theorem R115607 : Reach 115607 := rs (se 1 (by rfl) ⟨86705, by rfl⟩) R173411
theorem R115763 : Reach 115763 := rs (se 1 (by rfl) ⟨86822, by rfl⟩) R173645
theorem R509003 : Reach 509003 := rs (se 1 (by rfl) ⟨381752, by rfl⟩) R763505
theorem R345181 : Reach 345181 := rs (se 3 (by rfl) ⟨64721, by rfl⟩) R129443
theorem R181597 : Reach 181597 := rs (se 3 (by rfl) ⟨34049, by rfl⟩) R68099
theorem R116147 : Reach 116147 := rs (se 1 (by rfl) ⟨87110, by rfl⟩) R174221
theorem R149015 : Reach 149015 := rs (se 1 (by rfl) ⟨111761, by rfl⟩) R223523
theorem R476765 : Reach 476765 := rs (se 3 (by rfl) ⟨89393, by rfl⟩) R178787
theorem R312983 : Reach 312983 := rs (se 1 (by rfl) ⟨234737, by rfl⟩) R469475
theorem R280385 : Reach 280385 := rs (se 2 (by rfl) ⟨105144, by rfl⟩) R210289
theorem R116633 : Reach 116633 := rs (se 2 (by rfl) ⟨43737, by rfl⟩) R87475
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R247901 : Reach 247901 := rs (se 3 (by rfl) ⟨46481, by rfl⟩) R92963
theorem R247981 : Reach 247981 := rs (se 3 (by rfl) ⟨46496, by rfl⟩) R92993
theorem R706765 : Reach 706765 := rs (se 3 (by rfl) ⟨132518, by rfl⟩) R265037
theorem R84439 : Reach 84439 := rs (se 1 (by rfl) ⟨63329, by rfl⟩) R126659
theorem R182749 : Reach 182749 := rs (se 3 (by rfl) ⟨34265, by rfl⟩) R68531
theorem R150295 : Reach 150295 := rs (se 1 (by rfl) ⟨112721, by rfl⟩) R225443
theorem R150731 : Reach 150731 := rs (se 1 (by rfl) ⟨113048, by rfl⟩) R226097
theorem R85259 : Reach 85259 := rs (se 1 (by rfl) ⟨63944, by rfl⟩) R127889
theorem R118091 : Reach 118091 := rs (se 1 (by rfl) ⟨88568, by rfl⟩) R177137
theorem R118273 : Reach 118273 := rs (se 2 (by rfl) ⟨44352, by rfl⟩) R88705
theorem R151105 : Reach 151105 := rs (se 2 (by rfl) ⟨56664, by rfl⟩) R113329
theorem R249409 : Reach 249409 := rs (se 2 (by rfl) ⟨93528, by rfl⟩) R187057
theorem R85655 : Reach 85655 := rs (se 1 (by rfl) ⟨64241, by rfl⟩) R128483
theorem R118721 : Reach 118721 := rs (se 2 (by rfl) ⟨44520, by rfl⟩) R89041
theorem R872579 : Reach 872579 := rs (se 1 (by rfl) ⟨654434, by rfl⟩) R1308869
theorem R151703 : Reach 151703 := rs (se 1 (by rfl) ⟨113777, by rfl⟩) R227555
theorem R119063 : Reach 119063 := rs (se 1 (by rfl) ⟨89297, by rfl⟩) R178595
theorem R643373 : Reach 643373 := rs (se 3 (by rfl) ⟨120632, by rfl⟩) R241265
theorem R1921553 : Reach 1921553 := rs (se 2 (by rfl) ⟨720582, by rfl⟩) R1441165
theorem R774917 : Reach 774917 := rs (se 4 (by rfl) ⟨72648, by rfl⟩) R145297
theorem R873281 : Reach 873281 := rs (se 2 (by rfl) ⟨327480, by rfl⟩) R654961
theorem R119731 : Reach 119731 := rs (se 1 (by rfl) ⟨89798, by rfl⟩) R179597
theorem R152513 : Reach 152513 := rs (se 2 (by rfl) ⟨57192, by rfl⟩) R114385
theorem R250931 : Reach 250931 := rs (se 1 (by rfl) ⟨188198, by rfl⟩) R376397
theorem R513125 : Reach 513125 := rs (se 4 (by rfl) ⟨48105, by rfl⟩) R96211
theorem R316547 : Reach 316547 := rs (se 1 (by rfl) ⟨237410, by rfl⟩) R474821
theorem R153049 : Reach 153049 := rs (se 2 (by rfl) ⟨57393, by rfl⟩) R114787
theorem R382643 : Reach 382643 := rs (se 1 (by rfl) ⟨286982, by rfl⟩) R573965
theorem R513809 : Reach 513809 := rs (se 2 (by rfl) ⟨192678, by rfl⟩) R385357
theorem R120665 : Reach 120665 := rs (se 2 (by rfl) ⟨45249, by rfl⟩) R90499
theorem R252163 : Reach 252163 := rs (se 1 (by rfl) ⟨189122, by rfl⟩) R378245
theorem R1071629 : Reach 1071629 := rs (se 3 (by rfl) ⟨200930, by rfl⟩) R401861
theorem R154163 : Reach 154163 := rs (se 1 (by rfl) ⟨115622, by rfl⟩) R231245
theorem R449155 : Reach 449155 := rs (se 1 (by rfl) ⟨336866, by rfl⟩) R673733
theorem R88715 : Reach 88715 := rs (se 1 (by rfl) ⟨66536, by rfl⟩) R133073
theorem R88727 : Reach 88727 := rs (se 1 (by rfl) ⟨66545, by rfl⟩) R133091
theorem R88793 : Reach 88793 := rs (se 2 (by rfl) ⟨33297, by rfl⟩) R66595
theorem R88907 : Reach 88907 := rs (se 1 (by rfl) ⟨66680, by rfl⟩) R133361
theorem R88919 : Reach 88919 := rs (se 1 (by rfl) ⟨66689, by rfl⟩) R133379
theorem R154457 : Reach 154457 := rs (se 2 (by rfl) ⟨57921, by rfl⟩) R115843
theorem R88985 : Reach 88985 := rs (se 2 (by rfl) ⟨33369, by rfl⟩) R66739
theorem R89099 : Reach 89099 := rs (se 1 (by rfl) ⟨66824, by rfl⟩) R133649
theorem R285713 : Reach 285713 := rs (se 2 (by rfl) ⟨107142, by rfl⟩) R214285
theorem R89111 : Reach 89111 := rs (se 1 (by rfl) ⟨66833, by rfl⟩) R133667
theorem R89177 : Reach 89177 := rs (se 2 (by rfl) ⟨33441, by rfl⟩) R66883
theorem R220249 : Reach 220249 := rs (se 2 (by rfl) ⟨82593, by rfl⟩) R165187
theorem R89291 : Reach 89291 := rs (se 1 (by rfl) ⟨66968, by rfl⟩) R133937
theorem R89303 : Reach 89303 := rs (se 1 (by rfl) ⟨66977, by rfl⟩) R133955
theorem R253145 : Reach 253145 := rs (se 2 (by rfl) ⟨94929, by rfl⟩) R189859
theorem R89369 : Reach 89369 := rs (se 2 (by rfl) ⟨33513, by rfl⟩) R67027
theorem R89483 : Reach 89483 := rs (se 1 (by rfl) ⟨67112, by rfl⟩) R134225
theorem R89495 : Reach 89495 := rs (se 1 (by rfl) ⟨67121, by rfl⟩) R134243
theorem R122305 : Reach 122305 := rs (se 2 (by rfl) ⟨45864, by rfl⟩) R91729
theorem R89561 : Reach 89561 := rs (se 2 (by rfl) ⟨33585, by rfl⟩) R67171
theorem R89675 : Reach 89675 := rs (se 1 (by rfl) ⟨67256, by rfl⟩) R134513
theorem R89687 : Reach 89687 := rs (se 1 (by rfl) ⟨67265, by rfl⟩) R134531
theorem R482917 : Reach 482917 := rs (se 4 (by rfl) ⟨45273, by rfl⟩) R90547
theorem R89753 : Reach 89753 := rs (se 2 (by rfl) ⟨33657, by rfl⟩) R67315
theorem R89867 : Reach 89867 := rs (se 1 (by rfl) ⟨67400, by rfl⟩) R134801
theorem R89879 : Reach 89879 := rs (se 1 (by rfl) ⟨67409, by rfl⟩) R134819
theorem R89945 : Reach 89945 := rs (se 2 (by rfl) ⟨33729, by rfl⟩) R67459
theorem R450481 : Reach 450481 := rs (se 2 (by rfl) ⟨168930, by rfl⟩) R337861
theorem R90059 : Reach 90059 := rs (se 1 (by rfl) ⟨67544, by rfl⟩) R135089
theorem R90071 : Reach 90071 := rs (se 1 (by rfl) ⟨67553, by rfl⟩) R135107
theorem R450521 : Reach 450521 := rs (se 2 (by rfl) ⟨168945, by rfl⟩) R337891
theorem R90137 : Reach 90137 := rs (se 2 (by rfl) ⟨33801, by rfl⟩) R67603
theorem R122969 : Reach 122969 := rs (se 2 (by rfl) ⟨46113, by rfl⟩) R92227
theorem R90251 : Reach 90251 := rs (se 1 (by rfl) ⟨67688, by rfl⟩) R135377
theorem R90263 : Reach 90263 := rs (se 1 (by rfl) ⟨67697, by rfl⟩) R135395
theorem R90329 : Reach 90329 := rs (se 2 (by rfl) ⟨33873, by rfl⟩) R67747
theorem R90443 : Reach 90443 := rs (se 1 (by rfl) ⟨67832, by rfl⟩) R135665
theorem R90455 : Reach 90455 := rs (se 1 (by rfl) ⟨67841, by rfl⟩) R135683
theorem R450917 : Reach 450917 := rs (se 4 (by rfl) ⟨42273, by rfl⟩) R84547
theorem R90521 : Reach 90521 := rs (se 2 (by rfl) ⟨33945, by rfl⟩) R67891
theorem R254411 : Reach 254411 := rs (se 1 (by rfl) ⟨190808, by rfl⟩) R381617
theorem R156107 : Reach 156107 := rs (se 1 (by rfl) ⟨117080, by rfl⟩) R234161
theorem R90635 : Reach 90635 := rs (se 1 (by rfl) ⟨67976, by rfl⟩) R135953
theorem R90647 : Reach 90647 := rs (se 1 (by rfl) ⟨67985, by rfl⟩) R135971
theorem R90713 : Reach 90713 := rs (se 2 (by rfl) ⟨34017, by rfl⟩) R68035
theorem R90827 : Reach 90827 := rs (se 1 (by rfl) ⟨68120, by rfl⟩) R136241
theorem R90839 : Reach 90839 := rs (se 1 (by rfl) ⟨68129, by rfl⟩) R136259
theorem R90905 : Reach 90905 := rs (se 2 (by rfl) ⟨34089, by rfl⟩) R68179
theorem R254771 : Reach 254771 := rs (se 1 (by rfl) ⟨191078, by rfl⟩) R382157
theorem R451403 : Reach 451403 := rs (se 1 (by rfl) ⟨338552, by rfl⟩) R677105
theorem R222041 : Reach 222041 := rs (se 2 (by rfl) ⟨83265, by rfl⟩) R166531
theorem R91019 : Reach 91019 := rs (se 1 (by rfl) ⟨68264, by rfl⟩) R136529
theorem R91031 : Reach 91031 := rs (se 1 (by rfl) ⟨68273, by rfl⟩) R136547
theorem R91097 : Reach 91097 := rs (se 2 (by rfl) ⟨34161, by rfl⟩) R68323
theorem R91211 : Reach 91211 := rs (se 1 (by rfl) ⟨68408, by rfl⟩) R136817
theorem R91223 : Reach 91223 := rs (se 1 (by rfl) ⟨68417, by rfl⟩) R136835
theorem R91289 : Reach 91289 := rs (se 2 (by rfl) ⟨34233, by rfl⟩) R68467
theorem R91403 : Reach 91403 := rs (se 1 (by rfl) ⟨68552, by rfl⟩) R137105
theorem R91415 : Reach 91415 := rs (se 1 (by rfl) ⟨68561, by rfl⟩) R137123
theorem R91481 : Reach 91481 := rs (se 2 (by rfl) ⟨34305, by rfl⟩) R68611
theorem R157079 : Reach 157079 := rs (se 1 (by rfl) ⟨117809, by rfl⟩) R235619
theorem R91595 : Reach 91595 := rs (se 1 (by rfl) ⟨68696, by rfl⟩) R137393
theorem R124363 : Reach 124363 := rs (se 1 (by rfl) ⟨93272, by rfl⟩) R186545
theorem R91607 : Reach 91607 := rs (se 1 (by rfl) ⟨68705, by rfl⟩) R137411
theorem R91673 : Reach 91673 := rs (se 2 (by rfl) ⟨34377, by rfl⟩) R68755
theorem R91787 : Reach 91787 := rs (se 1 (by rfl) ⟨68840, by rfl⟩) R137681
theorem R91799 : Reach 91799 := rs (se 1 (by rfl) ⟨68849, by rfl⟩) R137699
theorem R91865 : Reach 91865 := rs (se 2 (by rfl) ⟨34449, by rfl⟩) R68899
theorem R59127 : Reach 59127 := rs (se 1 (by rfl) ⟨44345, by rfl⟩) R88691
theorem R59147 : Reach 59147 := rs (se 1 (by rfl) ⟨44360, by rfl⟩) R88721
theorem R59159 : Reach 59159 := rs (se 1 (by rfl) ⟨44369, by rfl⟩) R88739
theorem R59179 : Reach 59179 := rs (se 1 (by rfl) ⟨44384, by rfl⟩) R88769
theorem R190259 : Reach 190259 := rs (se 1 (by rfl) ⟨142694, by rfl⟩) R285389
theorem R59191 : Reach 59191 := rs (se 1 (by rfl) ⟨44393, by rfl⟩) R88787
theorem R59211 : Reach 59211 := rs (se 1 (by rfl) ⟨44408, by rfl⟩) R88817
theorem R91979 : Reach 91979 := rs (se 1 (by rfl) ⟨68984, by rfl⟩) R137969
theorem R59223 : Reach 59223 := rs (se 1 (by rfl) ⟨44417, by rfl⟩) R88835
theorem R91991 : Reach 91991 := rs (se 1 (by rfl) ⟨68993, by rfl⟩) R137987
theorem R59243 : Reach 59243 := rs (se 1 (by rfl) ⟨44432, by rfl⟩) R88865
theorem R59255 : Reach 59255 := rs (se 1 (by rfl) ⟨44441, by rfl⟩) R88883
theorem R59275 : Reach 59275 := rs (se 1 (by rfl) ⟨44456, by rfl⟩) R88913
theorem R59287 : Reach 59287 := rs (se 1 (by rfl) ⟨44465, by rfl⟩) R88931
theorem R92057 : Reach 92057 := rs (se 2 (by rfl) ⟨34521, by rfl⟩) R69043
theorem R59307 : Reach 59307 := rs (se 1 (by rfl) ⟨44480, by rfl⟩) R88961
theorem R59319 : Reach 59319 := rs (se 1 (by rfl) ⟨44489, by rfl⟩) R88979
theorem R59339 : Reach 59339 := rs (se 1 (by rfl) ⟨44504, by rfl⟩) R89009
theorem R59351 : Reach 59351 := rs (se 1 (by rfl) ⟨44513, by rfl⟩) R89027
theorem R59371 : Reach 59371 := rs (se 1 (by rfl) ⟨44528, by rfl⟩) R89057
theorem R59383 : Reach 59383 := rs (se 1 (by rfl) ⟨44537, by rfl⟩) R89075
theorem R59403 : Reach 59403 := rs (se 1 (by rfl) ⟨44552, by rfl⟩) R89105
theorem R92171 : Reach 92171 := rs (se 1 (by rfl) ⟨69128, by rfl⟩) R138257
theorem R59415 : Reach 59415 := rs (se 1 (by rfl) ⟨44561, by rfl⟩) R89123
theorem R92183 : Reach 92183 := rs (se 1 (by rfl) ⟨69137, by rfl⟩) R138275
theorem R59435 : Reach 59435 := rs (se 1 (by rfl) ⟨44576, by rfl⟩) R89153
theorem R157747 : Reach 157747 := rs (se 1 (by rfl) ⟨118310, by rfl⟩) R236621
theorem R59447 : Reach 59447 := rs (se 1 (by rfl) ⟨44585, by rfl⟩) R89171
theorem R59467 : Reach 59467 := rs (se 1 (by rfl) ⟨44600, by rfl⟩) R89201
theorem R59479 : Reach 59479 := rs (se 1 (by rfl) ⟨44609, by rfl⟩) R89219
theorem R92249 : Reach 92249 := rs (se 2 (by rfl) ⟨34593, by rfl⟩) R69187
theorem R59499 : Reach 59499 := rs (se 1 (by rfl) ⟨44624, by rfl⟩) R89249
theorem R59511 : Reach 59511 := rs (se 1 (by rfl) ⟨44633, by rfl⟩) R89267
theorem R59531 : Reach 59531 := rs (se 1 (by rfl) ⟨44648, by rfl⟩) R89297
theorem R59543 : Reach 59543 := rs (se 1 (by rfl) ⟨44657, by rfl⟩) R89315
theorem R354455 : Reach 354455 := rs (se 1 (by rfl) ⟨265841, by rfl⟩) R531683
theorem R59563 : Reach 59563 := rs (se 1 (by rfl) ⟨44672, by rfl⟩) R89345
theorem R59575 : Reach 59575 := rs (se 1 (by rfl) ⟨44681, by rfl⟩) R89363
theorem R157889 : Reach 157889 := rs (se 2 (by rfl) ⟨59208, by rfl⟩) R118417
theorem R59595 : Reach 59595 := rs (se 1 (by rfl) ⟨44696, by rfl⟩) R89393
theorem R92363 : Reach 92363 := rs (se 1 (by rfl) ⟨69272, by rfl⟩) R138545
theorem R59607 : Reach 59607 := rs (se 1 (by rfl) ⟨44705, by rfl⟩) R89411
theorem R92375 : Reach 92375 := rs (se 1 (by rfl) ⟨69281, by rfl⟩) R138563
theorem R59627 : Reach 59627 := rs (se 1 (by rfl) ⟨44720, by rfl⟩) R89441
theorem R59639 : Reach 59639 := rs (se 1 (by rfl) ⟨44729, by rfl⟩) R89459
theorem R59659 : Reach 59659 := rs (se 1 (by rfl) ⟨44744, by rfl⟩) R89489
theorem R59671 : Reach 59671 := rs (se 1 (by rfl) ⟨44753, by rfl⟩) R89507
theorem R92441 : Reach 92441 := rs (se 2 (by rfl) ⟨34665, by rfl⟩) R69331
theorem R59691 : Reach 59691 := rs (se 1 (by rfl) ⟨44768, by rfl⟩) R89537
theorem R59703 : Reach 59703 := rs (se 1 (by rfl) ⟨44777, by rfl⟩) R89555
theorem R59723 : Reach 59723 := rs (se 1 (by rfl) ⟨44792, by rfl⟩) R89585
theorem R59735 : Reach 59735 := rs (se 1 (by rfl) ⟨44801, by rfl⟩) R89603
theorem R59755 : Reach 59755 := rs (se 1 (by rfl) ⟨44816, by rfl⟩) R89633
theorem R59767 : Reach 59767 := rs (se 1 (by rfl) ⟨44825, by rfl⟩) R89651
theorem R59787 : Reach 59787 := rs (se 1 (by rfl) ⟨44840, by rfl⟩) R89681
theorem R92555 : Reach 92555 := rs (se 1 (by rfl) ⟨69416, by rfl⟩) R138833
theorem R59799 : Reach 59799 := rs (se 1 (by rfl) ⟨44849, by rfl⟩) R89699
theorem R92567 : Reach 92567 := rs (se 1 (by rfl) ⟨69425, by rfl⟩) R138851
theorem R59819 : Reach 59819 := rs (se 1 (by rfl) ⟨44864, by rfl⟩) R89729
theorem R59831 : Reach 59831 := rs (se 1 (by rfl) ⟨44873, by rfl⟩) R89747
theorem R59851 : Reach 59851 := rs (se 1 (by rfl) ⟨44888, by rfl⟩) R89777
theorem R59863 : Reach 59863 := rs (se 1 (by rfl) ⟨44897, by rfl⟩) R89795
theorem R125401 : Reach 125401 := rs (se 2 (by rfl) ⟨47025, by rfl⟩) R94051
theorem R190937 : Reach 190937 := rs (se 2 (by rfl) ⟨71601, by rfl⟩) R143203
theorem R92633 : Reach 92633 := rs (se 2 (by rfl) ⟨34737, by rfl⟩) R69475
theorem R59883 : Reach 59883 := rs (se 1 (by rfl) ⟨44912, by rfl⟩) R89825
theorem R59895 : Reach 59895 := rs (se 1 (by rfl) ⟨44921, by rfl⟩) R89843
theorem R59915 : Reach 59915 := rs (se 1 (by rfl) ⟨44936, by rfl⟩) R89873
theorem R59927 : Reach 59927 := rs (se 1 (by rfl) ⟨44945, by rfl⟩) R89891
theorem R59947 : Reach 59947 := rs (se 1 (by rfl) ⟨44960, by rfl⟩) R89921
theorem R59959 : Reach 59959 := rs (se 1 (by rfl) ⟨44969, by rfl⟩) R89939
theorem R59979 : Reach 59979 := rs (se 1 (by rfl) ⟨44984, by rfl⟩) R89969
theorem R92747 : Reach 92747 := rs (se 1 (by rfl) ⟨69560, by rfl⟩) R139121
theorem R59991 : Reach 59991 := rs (se 1 (by rfl) ⟨44993, by rfl⟩) R89987
theorem R92759 : Reach 92759 := rs (se 1 (by rfl) ⟨69569, by rfl⟩) R139139
theorem R60011 : Reach 60011 := rs (se 1 (by rfl) ⟨45008, by rfl⟩) R90017
theorem R60023 : Reach 60023 := rs (se 1 (by rfl) ⟨45017, by rfl⟩) R90035
theorem R60043 : Reach 60043 := rs (se 1 (by rfl) ⟨45032, by rfl⟩) R90065
theorem R60055 : Reach 60055 := rs (se 1 (by rfl) ⟨45041, by rfl⟩) R90083
theorem R92825 : Reach 92825 := rs (se 2 (by rfl) ⟨34809, by rfl⟩) R69619
theorem R60075 : Reach 60075 := rs (se 1 (by rfl) ⟨45056, by rfl⟩) R90113
theorem R60087 : Reach 60087 := rs (se 1 (by rfl) ⟨45065, by rfl⟩) R90131
theorem R60107 : Reach 60107 := rs (se 1 (by rfl) ⟨45080, by rfl⟩) R90161
theorem R60119 : Reach 60119 := rs (se 1 (by rfl) ⟨45089, by rfl⟩) R90179
theorem R60139 : Reach 60139 := rs (se 1 (by rfl) ⟨45104, by rfl⟩) R90209
theorem R60151 : Reach 60151 := rs (se 1 (by rfl) ⟨45113, by rfl⟩) R90227
theorem R60171 : Reach 60171 := rs (se 1 (by rfl) ⟨45128, by rfl⟩) R90257
theorem R92939 : Reach 92939 := rs (se 1 (by rfl) ⟨69704, by rfl⟩) R139409
theorem R60183 : Reach 60183 := rs (se 1 (by rfl) ⟨45137, by rfl⟩) R90275
theorem R92951 : Reach 92951 := rs (se 1 (by rfl) ⟨69713, by rfl⟩) R139427
theorem R60203 : Reach 60203 := rs (se 1 (by rfl) ⟨45152, by rfl⟩) R90305
theorem R60215 : Reach 60215 := rs (se 1 (by rfl) ⟨45161, by rfl⟩) R90323
theorem R60235 : Reach 60235 := rs (se 1 (by rfl) ⟨45176, by rfl⟩) R90353
theorem R60247 : Reach 60247 := rs (se 1 (by rfl) ⟨45185, by rfl⟩) R90371
theorem R93017 : Reach 93017 := rs (se 2 (by rfl) ⟨34881, by rfl⟩) R69763
theorem R158557 : Reach 158557 := rs (se 3 (by rfl) ⟨29729, by rfl⟩) R59459
theorem R60267 : Reach 60267 := rs (se 1 (by rfl) ⟨45200, by rfl⟩) R90401
theorem R60279 : Reach 60279 := rs (se 1 (by rfl) ⟨45209, by rfl⟩) R90419
theorem R60299 : Reach 60299 := rs (se 1 (by rfl) ⟨45224, by rfl⟩) R90449
theorem R60311 : Reach 60311 := rs (se 1 (by rfl) ⟨45233, by rfl⟩) R90467
theorem R93079 : Reach 93079 := rs (se 1 (by rfl) ⟨69809, by rfl⟩) R139619
theorem R60331 : Reach 60331 := rs (se 1 (by rfl) ⟨45248, by rfl⟩) R90497
theorem R60343 : Reach 60343 := rs (se 1 (by rfl) ⟨45257, by rfl⟩) R90515
theorem R60363 : Reach 60363 := rs (se 1 (by rfl) ⟨45272, by rfl⟩) R90545
theorem R93131 : Reach 93131 := rs (se 1 (by rfl) ⟨69848, by rfl⟩) R139697
theorem R60375 : Reach 60375 := rs (se 1 (by rfl) ⟨45281, by rfl⟩) R90563
theorem R93143 : Reach 93143 := rs (se 1 (by rfl) ⟨69857, by rfl⟩) R139715
theorem R60395 : Reach 60395 := rs (se 1 (by rfl) ⟨45296, by rfl⟩) R90593
theorem R60407 : Reach 60407 := rs (se 1 (by rfl) ⟨45305, by rfl⟩) R90611
theorem R60427 : Reach 60427 := rs (se 1 (by rfl) ⟨45320, by rfl⟩) R90641
theorem R60439 : Reach 60439 := rs (se 1 (by rfl) ⟨45329, by rfl⟩) R90659
theorem R93209 : Reach 93209 := rs (se 2 (by rfl) ⟨34953, by rfl⟩) R69907
theorem R60459 : Reach 60459 := rs (se 1 (by rfl) ⟨45344, by rfl⟩) R90689
theorem R60471 : Reach 60471 := rs (se 1 (by rfl) ⟨45353, by rfl⟩) R90707
theorem R60491 : Reach 60491 := rs (se 1 (by rfl) ⟨45368, by rfl⟩) R90737
theorem R60503 : Reach 60503 := rs (se 1 (by rfl) ⟨45377, by rfl⟩) R90755
theorem R60523 : Reach 60523 := rs (se 1 (by rfl) ⟨45392, by rfl⟩) R90785
theorem R60535 : Reach 60535 := rs (se 1 (by rfl) ⟨45401, by rfl⟩) R90803
theorem R60555 : Reach 60555 := rs (se 1 (by rfl) ⟨45416, by rfl⟩) R90833
theorem R93323 : Reach 93323 := rs (se 1 (by rfl) ⟨69992, by rfl⟩) R139985
theorem R60567 : Reach 60567 := rs (se 1 (by rfl) ⟨45425, by rfl⟩) R90851
theorem R93335 : Reach 93335 := rs (se 1 (by rfl) ⟨70001, by rfl⟩) R140003
theorem R60587 : Reach 60587 := rs (se 1 (by rfl) ⟨45440, by rfl⟩) R90881
theorem R60599 : Reach 60599 := rs (se 1 (by rfl) ⟨45449, by rfl⟩) R90899
theorem R60619 : Reach 60619 := rs (se 1 (by rfl) ⟨45464, by rfl⟩) R90929
theorem R60631 : Reach 60631 := rs (se 1 (by rfl) ⟨45473, by rfl⟩) R90947
theorem R93401 : Reach 93401 := rs (se 2 (by rfl) ⟨35025, by rfl⟩) R70051
theorem R60651 : Reach 60651 := rs (se 1 (by rfl) ⟨45488, by rfl⟩) R90977
theorem R60663 : Reach 60663 := rs (se 1 (by rfl) ⟨45497, by rfl⟩) R90995
theorem R945413 : Reach 945413 := rs (se 4 (by rfl) ⟨88632, by rfl⟩) R177265
theorem R60683 : Reach 60683 := rs (se 1 (by rfl) ⟨45512, by rfl⟩) R91025
theorem R60695 : Reach 60695 := rs (se 1 (by rfl) ⟨45521, by rfl⟩) R91043
theorem R453923 : Reach 453923 := rs (se 1 (by rfl) ⟨340442, by rfl⟩) R680885
theorem R60715 : Reach 60715 := rs (se 1 (by rfl) ⟨45536, by rfl⟩) R91073
theorem R60727 : Reach 60727 := rs (se 1 (by rfl) ⟨45545, by rfl⟩) R91091
theorem R60747 : Reach 60747 := rs (se 1 (by rfl) ⟨45560, by rfl⟩) R91121
theorem R93515 : Reach 93515 := rs (se 1 (by rfl) ⟨70136, by rfl⟩) R140273
theorem R60759 : Reach 60759 := rs (se 1 (by rfl) ⟨45569, by rfl⟩) R91139
theorem R93527 : Reach 93527 := rs (se 1 (by rfl) ⟨70145, by rfl⟩) R140291
theorem R60779 : Reach 60779 := rs (se 1 (by rfl) ⟨45584, by rfl⟩) R91169
theorem R60791 : Reach 60791 := rs (se 1 (by rfl) ⟨45593, by rfl⟩) R91187
theorem R60811 : Reach 60811 := rs (se 1 (by rfl) ⟨45608, by rfl⟩) R91217
theorem R60823 : Reach 60823 := rs (se 1 (by rfl) ⟨45617, by rfl⟩) R91235
theorem R93593 : Reach 93593 := rs (se 2 (by rfl) ⟨35097, by rfl⟩) R70195
theorem R60843 : Reach 60843 := rs (se 1 (by rfl) ⟨45632, by rfl⟩) R91265
theorem R159155 : Reach 159155 := rs (se 1 (by rfl) ⟨119366, by rfl⟩) R238733
theorem R60855 : Reach 60855 := rs (se 1 (by rfl) ⟨45641, by rfl⟩) R91283
theorem R60875 : Reach 60875 := rs (se 1 (by rfl) ⟨45656, by rfl⟩) R91313
theorem R60887 : Reach 60887 := rs (se 1 (by rfl) ⟨45665, by rfl⟩) R91331
theorem R60907 : Reach 60907 := rs (se 1 (by rfl) ⟨45680, by rfl⟩) R91361
theorem R60919 : Reach 60919 := rs (se 1 (by rfl) ⟨45689, by rfl⟩) R91379
theorem R60939 : Reach 60939 := rs (se 1 (by rfl) ⟨45704, by rfl⟩) R91409
theorem R93707 : Reach 93707 := rs (se 1 (by rfl) ⟨70280, by rfl⟩) R140561
theorem R60951 : Reach 60951 := rs (se 1 (by rfl) ⟨45713, by rfl⟩) R91427
theorem R93719 : Reach 93719 := rs (se 1 (by rfl) ⟨70289, by rfl⟩) R140579
theorem R60971 : Reach 60971 := rs (se 1 (by rfl) ⟨45728, by rfl⟩) R91457
theorem R60983 : Reach 60983 := rs (se 1 (by rfl) ⟨45737, by rfl⟩) R91475
theorem R126539 : Reach 126539 := rs (se 1 (by rfl) ⟨94904, by rfl⟩) R189809
theorem R61003 : Reach 61003 := rs (se 1 (by rfl) ⟨45752, by rfl⟩) R91505
theorem R61015 : Reach 61015 := rs (se 1 (by rfl) ⟨45761, by rfl⟩) R91523
theorem R93785 : Reach 93785 := rs (se 2 (by rfl) ⟨35169, by rfl⟩) R70339
theorem R61035 : Reach 61035 := rs (se 1 (by rfl) ⟨45776, by rfl⟩) R91553
theorem R61047 : Reach 61047 := rs (se 1 (by rfl) ⟨45785, by rfl⟩) R91571
theorem R388739 : Reach 388739 := rs (se 1 (by rfl) ⟨291554, by rfl⟩) R583109
theorem R61067 : Reach 61067 := rs (se 1 (by rfl) ⟨45800, by rfl⟩) R91601
theorem R61079 : Reach 61079 := rs (se 1 (by rfl) ⟨45809, by rfl⟩) R91619
theorem R61099 : Reach 61099 := rs (se 1 (by rfl) ⟨45824, by rfl⟩) R91649
theorem R61111 : Reach 61111 := rs (se 1 (by rfl) ⟨45833, by rfl⟩) R91667
theorem R61131 : Reach 61131 := rs (se 1 (by rfl) ⟨45848, by rfl⟩) R91697
theorem R93899 : Reach 93899 := rs (se 1 (by rfl) ⟨70424, by rfl⟩) R140849
theorem R61143 : Reach 61143 := rs (se 1 (by rfl) ⟨45857, by rfl⟩) R91715
theorem R93911 : Reach 93911 := rs (se 1 (by rfl) ⟨70433, by rfl⟩) R140867
theorem R159449 : Reach 159449 := rs (se 2 (by rfl) ⟨59793, by rfl⟩) R119587
theorem R61163 : Reach 61163 := rs (se 1 (by rfl) ⟨45872, by rfl⟩) R91745
theorem R61175 : Reach 61175 := rs (se 1 (by rfl) ⟨45881, by rfl⟩) R91763
theorem R61195 : Reach 61195 := rs (se 1 (by rfl) ⟨45896, by rfl⟩) R91793
theorem R61207 : Reach 61207 := rs (se 1 (by rfl) ⟨45905, by rfl⟩) R91811
theorem R93977 : Reach 93977 := rs (se 2 (by rfl) ⟨35241, by rfl⟩) R70483
theorem R61227 : Reach 61227 := rs (se 1 (by rfl) ⟨45920, by rfl⟩) R91841
theorem R61239 : Reach 61239 := rs (se 1 (by rfl) ⟨45929, by rfl⟩) R91859
theorem R61259 : Reach 61259 := rs (se 1 (by rfl) ⟨45944, by rfl⟩) R91889
theorem R61271 : Reach 61271 := rs (se 1 (by rfl) ⟨45953, by rfl⟩) R91907
theorem R61291 : Reach 61291 := rs (se 1 (by rfl) ⟨45968, by rfl⟩) R91937
theorem R61303 : Reach 61303 := rs (se 1 (by rfl) ⟨45977, by rfl⟩) R91955
theorem R61323 : Reach 61323 := rs (se 1 (by rfl) ⟨45992, by rfl⟩) R91985
theorem R94091 : Reach 94091 := rs (se 1 (by rfl) ⟨70568, by rfl⟩) R141137
theorem R61335 : Reach 61335 := rs (se 1 (by rfl) ⟨46001, by rfl⟩) R92003
theorem R94103 : Reach 94103 := rs (se 1 (by rfl) ⟨70577, by rfl⟩) R141155
theorem R61355 : Reach 61355 := rs (se 1 (by rfl) ⟨46016, by rfl⟩) R92033
theorem R61367 : Reach 61367 := rs (se 1 (by rfl) ⟨46025, by rfl⟩) R92051
theorem R192449 : Reach 192449 := rs (se 2 (by rfl) ⟨72168, by rfl⟩) R144337
theorem R61387 : Reach 61387 := rs (se 1 (by rfl) ⟨46040, by rfl⟩) R92081
theorem R225227 : Reach 225227 := rs (se 1 (by rfl) ⟨168920, by rfl⟩) R337841
theorem R159691 : Reach 159691 := rs (se 1 (by rfl) ⟨119768, by rfl⟩) R239537
theorem R61399 : Reach 61399 := rs (se 1 (by rfl) ⟨46049, by rfl⟩) R92099
theorem R94169 : Reach 94169 := rs (se 2 (by rfl) ⟨35313, by rfl⟩) R70627
theorem R61419 : Reach 61419 := rs (se 1 (by rfl) ⟨46064, by rfl⟩) R92129
theorem R61431 : Reach 61431 := rs (se 1 (by rfl) ⟨46073, by rfl⟩) R92147
theorem R61451 : Reach 61451 := rs (se 1 (by rfl) ⟨46088, by rfl⟩) R92177
theorem R61463 : Reach 61463 := rs (se 1 (by rfl) ⟨46097, by rfl⟩) R92195
theorem R127001 : Reach 127001 := rs (se 2 (by rfl) ⟨47625, by rfl⟩) R95251
theorem R61483 : Reach 61483 := rs (se 1 (by rfl) ⟨46112, by rfl⟩) R92225
theorem R61495 : Reach 61495 := rs (se 1 (by rfl) ⟨46121, by rfl⟩) R92243
theorem R192577 : Reach 192577 := rs (se 2 (by rfl) ⟨72216, by rfl⟩) R144433
theorem R61515 : Reach 61515 := rs (se 1 (by rfl) ⟨46136, by rfl⟩) R92273
theorem R94283 : Reach 94283 := rs (se 1 (by rfl) ⟨70712, by rfl⟩) R141425
theorem R61527 : Reach 61527 := rs (se 1 (by rfl) ⟨46145, by rfl⟩) R92291
theorem R94295 : Reach 94295 := rs (se 1 (by rfl) ⟨70721, by rfl⟩) R141443
theorem R61547 : Reach 61547 := rs (se 1 (by rfl) ⟨46160, by rfl⟩) R92321
theorem R61559 : Reach 61559 := rs (se 1 (by rfl) ⟨46169, by rfl⟩) R92339
theorem R61579 : Reach 61579 := rs (se 1 (by rfl) ⟨46184, by rfl⟩) R92369
theorem R61591 : Reach 61591 := rs (se 1 (by rfl) ⟨46193, by rfl⟩) R92387
theorem R94361 : Reach 94361 := rs (se 2 (by rfl) ⟨35385, by rfl⟩) R70771
theorem R61611 : Reach 61611 := rs (se 1 (by rfl) ⟨46208, by rfl⟩) R92417
theorem R61623 : Reach 61623 := rs (se 1 (by rfl) ⟨46217, by rfl⟩) R92435
theorem R61643 : Reach 61643 := rs (se 1 (by rfl) ⟨46232, by rfl⟩) R92465
theorem R61655 : Reach 61655 := rs (se 1 (by rfl) ⟨46241, by rfl⟩) R92483
theorem R61675 : Reach 61675 := rs (se 1 (by rfl) ⟨46256, by rfl⟩) R92513
theorem R61687 : Reach 61687 := rs (se 1 (by rfl) ⟨46265, by rfl⟩) R92531
theorem R61707 : Reach 61707 := rs (se 1 (by rfl) ⟨46280, by rfl⟩) R92561
theorem R94475 : Reach 94475 := rs (se 1 (by rfl) ⟨70856, by rfl⟩) R141713
theorem R61719 : Reach 61719 := rs (se 1 (by rfl) ⟨46289, by rfl⟩) R92579
theorem R94487 : Reach 94487 := rs (se 1 (by rfl) ⟨70865, by rfl⟩) R141731
theorem R61739 : Reach 61739 := rs (se 1 (by rfl) ⟨46304, by rfl⟩) R92609
theorem R61751 : Reach 61751 := rs (se 1 (by rfl) ⟨46313, by rfl⟩) R92627
theorem R192833 : Reach 192833 := rs (se 2 (by rfl) ⟨72312, by rfl⟩) R144625
theorem R225611 : Reach 225611 := rs (se 1 (by rfl) ⟨169208, by rfl⟩) R338417
theorem R61771 : Reach 61771 := rs (se 1 (by rfl) ⟨46328, by rfl⟩) R92657
theorem R61783 : Reach 61783 := rs (se 1 (by rfl) ⟨46337, by rfl⟩) R92675
theorem R225625 : Reach 225625 := rs (se 2 (by rfl) ⟨84609, by rfl⟩) R169219
theorem R94553 : Reach 94553 := rs (se 2 (by rfl) ⟨35457, by rfl⟩) R70915
theorem R61803 : Reach 61803 := rs (se 1 (by rfl) ⟨46352, by rfl⟩) R92705
theorem R61815 : Reach 61815 := rs (se 1 (by rfl) ⟨46361, by rfl⟩) R92723
theorem R61835 : Reach 61835 := rs (se 1 (by rfl) ⟨46376, by rfl⟩) R92753
theorem R61847 : Reach 61847 := rs (se 1 (by rfl) ⟨46385, by rfl⟩) R92771
theorem R61867 : Reach 61867 := rs (se 1 (by rfl) ⟨46400, by rfl⟩) R92801
theorem R61879 : Reach 61879 := rs (se 1 (by rfl) ⟨46409, by rfl⟩) R92819
theorem R61899 : Reach 61899 := rs (se 1 (by rfl) ⟨46424, by rfl⟩) R92849
theorem R94667 : Reach 94667 := rs (se 1 (by rfl) ⟨71000, by rfl⟩) R142001
theorem R61911 : Reach 61911 := rs (se 1 (by rfl) ⟨46433, by rfl⟩) R92867
theorem R94679 : Reach 94679 := rs (se 1 (by rfl) ⟨71009, by rfl⟩) R142019
theorem R61931 : Reach 61931 := rs (se 1 (by rfl) ⟨46448, by rfl⟩) R92897
theorem R61943 : Reach 61943 := rs (se 1 (by rfl) ⟨46457, by rfl⟩) R92915
theorem R61963 : Reach 61963 := rs (se 1 (by rfl) ⟨46472, by rfl⟩) R92945
theorem R61975 : Reach 61975 := rs (se 1 (by rfl) ⟨46481, by rfl⟩) R92963
theorem R61995 : Reach 61995 := rs (se 1 (by rfl) ⟨46496, by rfl⟩) R92993
theorem R62007 : Reach 62007 := rs (se 1 (by rfl) ⟨46505, by rfl⟩) R93011
theorem R62027 : Reach 62027 := rs (se 1 (by rfl) ⟨46520, by rfl⟩) R93041
theorem R62039 : Reach 62039 := rs (se 1 (by rfl) ⟨46529, by rfl⟩) R93059
theorem R62059 : Reach 62059 := rs (se 1 (by rfl) ⟨46544, by rfl⟩) R93089
theorem R62071 : Reach 62071 := rs (se 1 (by rfl) ⟨46553, by rfl⟩) R93107
theorem R62091 : Reach 62091 := rs (se 1 (by rfl) ⟨46568, by rfl⟩) R93137
theorem R62103 : Reach 62103 := rs (se 1 (by rfl) ⟨46577, by rfl⟩) R93155
theorem R94873 : Reach 94873 := rs (se 2 (by rfl) ⟨35577, by rfl⟩) R71155
theorem R62123 : Reach 62123 := rs (se 1 (by rfl) ⟨46592, by rfl⟩) R93185
theorem R62135 : Reach 62135 := rs (se 1 (by rfl) ⟨46601, by rfl⟩) R93203
theorem R62155 : Reach 62155 := rs (se 1 (by rfl) ⟨46616, by rfl⟩) R93233
theorem R62167 : Reach 62167 := rs (se 1 (by rfl) ⟨46625, by rfl⟩) R93251
theorem R62187 : Reach 62187 := rs (se 1 (by rfl) ⟨46640, by rfl⟩) R93281
theorem R62199 : Reach 62199 := rs (se 1 (by rfl) ⟨46649, by rfl⟩) R93299
theorem R62219 : Reach 62219 := rs (se 1 (by rfl) ⟨46664, by rfl⟩) R93329
theorem R62231 : Reach 62231 := rs (se 1 (by rfl) ⟨46673, by rfl⟩) R93347
theorem R62251 : Reach 62251 := rs (se 1 (by rfl) ⟨46688, by rfl⟩) R93377
theorem R62263 : Reach 62263 := rs (se 1 (by rfl) ⟨46697, by rfl⟩) R93395
theorem R62283 : Reach 62283 := rs (se 1 (by rfl) ⟨46712, by rfl⟩) R93425
theorem R62295 : Reach 62295 := rs (se 1 (by rfl) ⟨46721, by rfl⟩) R93443
theorem R62315 : Reach 62315 := rs (se 1 (by rfl) ⟨46736, by rfl⟩) R93473
theorem R62327 : Reach 62327 := rs (se 1 (by rfl) ⟨46745, by rfl⟩) R93491
theorem R62347 : Reach 62347 := rs (se 1 (by rfl) ⟨46760, by rfl⟩) R93521
theorem R62359 : Reach 62359 := rs (se 1 (by rfl) ⟨46769, by rfl⟩) R93539
theorem R62379 : Reach 62379 := rs (se 1 (by rfl) ⟨46784, by rfl⟩) R93569
theorem R488369 : Reach 488369 := rs (se 2 (by rfl) ⟨183138, by rfl⟩) R366277
theorem R62391 : Reach 62391 := rs (se 1 (by rfl) ⟨46793, by rfl⟩) R93587
theorem R62411 : Reach 62411 := rs (se 1 (by rfl) ⟨46808, by rfl⟩) R93617
theorem R62423 : Reach 62423 := rs (se 1 (by rfl) ⟨46817, by rfl⟩) R93635
theorem R62443 : Reach 62443 := rs (se 1 (by rfl) ⟨46832, by rfl⟩) R93665
theorem R62455 : Reach 62455 := rs (se 1 (by rfl) ⟨46841, by rfl⟩) R93683
theorem R62475 : Reach 62475 := rs (se 1 (by rfl) ⟨46856, by rfl⟩) R93713
theorem R62487 : Reach 62487 := rs (se 1 (by rfl) ⟨46865, by rfl⟩) R93731
theorem R62507 : Reach 62507 := rs (se 1 (by rfl) ⟨46880, by rfl⟩) R93761
theorem R62519 : Reach 62519 := rs (se 1 (by rfl) ⟨46889, by rfl⟩) R93779
theorem R62539 : Reach 62539 := rs (se 1 (by rfl) ⟨46904, by rfl⟩) R93809
theorem R62551 : Reach 62551 := rs (se 1 (by rfl) ⟨46913, by rfl⟩) R93827
theorem R62571 : Reach 62571 := rs (se 1 (by rfl) ⟨46928, by rfl⟩) R93857
theorem R62583 : Reach 62583 := rs (se 1 (by rfl) ⟨46937, by rfl⟩) R93875
theorem R62603 : Reach 62603 := rs (se 1 (by rfl) ⟨46952, by rfl⟩) R93905
theorem R62615 : Reach 62615 := rs (se 1 (by rfl) ⟨46961, by rfl⟩) R93923
theorem R62635 : Reach 62635 := rs (se 1 (by rfl) ⟨46976, by rfl⟩) R93953
theorem R128179 : Reach 128179 := rs (se 1 (by rfl) ⟨96134, by rfl⟩) R192269
theorem R62647 : Reach 62647 := rs (se 1 (by rfl) ⟨46985, by rfl⟩) R93971
theorem R95435 : Reach 95435 := rs (se 1 (by rfl) ⟨71576, by rfl⟩) R143153
theorem R62667 : Reach 62667 := rs (se 1 (by rfl) ⟨47000, by rfl⟩) R94001
theorem R62679 : Reach 62679 := rs (se 1 (by rfl) ⟨47009, by rfl⟩) R94019
theorem R62699 : Reach 62699 := rs (se 1 (by rfl) ⟨47024, by rfl⟩) R94049
theorem R62711 : Reach 62711 := rs (se 1 (by rfl) ⟨47033, by rfl⟩) R94067
theorem R62731 : Reach 62731 := rs (se 1 (by rfl) ⟨47048, by rfl⟩) R94097
theorem R226583 : Reach 226583 := rs (se 1 (by rfl) ⟨169937, by rfl⟩) R339875
theorem R62743 : Reach 62743 := rs (se 1 (by rfl) ⟨47057, by rfl⟩) R94115
theorem R62763 : Reach 62763 := rs (se 1 (by rfl) ⟨47072, by rfl⟩) R94145
theorem R62775 : Reach 62775 := rs (se 1 (by rfl) ⟨47081, by rfl⟩) R94163
theorem R62795 : Reach 62795 := rs (se 1 (by rfl) ⟨47096, by rfl⟩) R94193
theorem R62807 : Reach 62807 := rs (se 1 (by rfl) ⟨47105, by rfl⟩) R94211
theorem R62827 : Reach 62827 := rs (se 1 (by rfl) ⟨47120, by rfl⟩) R94241
theorem R62839 : Reach 62839 := rs (se 1 (by rfl) ⟨47129, by rfl⟩) R94259
theorem R62859 : Reach 62859 := rs (se 1 (by rfl) ⟨47144, by rfl⟩) R94289
theorem R62871 : Reach 62871 := rs (se 1 (by rfl) ⟨47153, by rfl⟩) R94307
theorem R62891 : Reach 62891 := rs (se 1 (by rfl) ⟨47168, by rfl⟩) R94337
theorem R62903 : Reach 62903 := rs (se 1 (by rfl) ⟨47177, by rfl⟩) R94355
theorem R62923 : Reach 62923 := rs (se 1 (by rfl) ⟨47192, by rfl⟩) R94385
theorem R62935 : Reach 62935 := rs (se 1 (by rfl) ⟨47201, by rfl⟩) R94403
theorem R62955 : Reach 62955 := rs (se 1 (by rfl) ⟨47216, by rfl⟩) R94433
theorem R62967 : Reach 62967 := rs (se 1 (by rfl) ⟨47225, by rfl⟩) R94451
theorem R62987 : Reach 62987 := rs (se 1 (by rfl) ⟨47240, by rfl⟩) R94481
theorem R62999 : Reach 62999 := rs (se 1 (by rfl) ⟨47249, by rfl⟩) R94499
theorem R63019 : Reach 63019 := rs (se 1 (by rfl) ⟨47264, by rfl⟩) R94529
theorem R63031 : Reach 63031 := rs (se 1 (by rfl) ⟨47273, by rfl⟩) R94547
theorem R63051 : Reach 63051 := rs (se 1 (by rfl) ⟨47288, by rfl⟩) R94577
theorem R63063 : Reach 63063 := rs (se 1 (by rfl) ⟨47297, by rfl⟩) R94595
theorem R63083 : Reach 63083 := rs (se 1 (by rfl) ⟨47312, by rfl⟩) R94625
theorem R63095 : Reach 63095 := rs (se 1 (by rfl) ⟨47321, by rfl⟩) R94643
theorem R128641 : Reach 128641 := rs (se 2 (by rfl) ⟨48240, by rfl⟩) R96481
theorem R63115 : Reach 63115 := rs (se 1 (by rfl) ⟨47336, by rfl⟩) R94673
theorem R259843 : Reach 259843 := rs (se 1 (by rfl) ⟨194882, by rfl⟩) R389765
theorem R194525 : Reach 194525 := rs (se 3 (by rfl) ⟨36473, by rfl⟩) R72947
theorem R260185 : Reach 260185 := rs (se 2 (by rfl) ⟨97569, by rfl⟩) R195139
theorem R63671 : Reach 63671 := rs (se 1 (by rfl) ⟨47753, by rfl⟩) R95507
theorem R129367 : Reach 129367 := rs (se 1 (by rfl) ⟨97025, by rfl⟩) R194051
theorem R621017 : Reach 621017 := rs (se 2 (by rfl) ⟨232881, by rfl⟩) R465763
theorem R227843 : Reach 227843 := rs (se 1 (by rfl) ⟨170882, by rfl⟩) R341765
theorem R359129 : Reach 359129 := rs (se 2 (by rfl) ⟨134673, by rfl⟩) R269347
theorem R195293 : Reach 195293 := rs (se 3 (by rfl) ⟨36617, by rfl⟩) R73235
theorem R359261 : Reach 359261 := rs (se 3 (by rfl) ⟨67361, by rfl⟩) R134723
theorem R64363 : Reach 64363 := rs (se 1 (by rfl) ⟨48272, by rfl⟩) R96545
theorem R326531 : Reach 326531 := rs (se 1 (by rfl) ⟨244898, by rfl⟩) R489797
theorem R64427 : Reach 64427 := rs (se 1 (by rfl) ⟨48320, by rfl⟩) R96641
theorem R261143 : Reach 261143 := rs (se 1 (by rfl) ⟨195857, by rfl⟩) R391715
theorem R130187 : Reach 130187 := rs (se 1 (by rfl) ⟨97640, by rfl⟩) R195281
theorem R195805 : Reach 195805 := rs (se 3 (by rfl) ⟨36713, by rfl⟩) R73427
theorem R490769 : Reach 490769 := rs (se 2 (by rfl) ⟨184038, by rfl⟩) R368077
theorem R556865 : Reach 556865 := rs (se 2 (by rfl) ⟨208824, by rfl⟩) R417649
theorem R1343411 : Reach 1343411 := rs (se 1 (by rfl) ⟨1007558, by rfl⟩) R2015117
theorem R131033 : Reach 131033 := rs (se 2 (by rfl) ⟨49137, by rfl⟩) R98275
theorem R655447 : Reach 655447 := rs (se 1 (by rfl) ⟨491585, by rfl⟩) R983171
theorem R40337621 : Reach 40337621 := rs (se 7 (by rfl) ⟨472706, by rfl⟩) R945413
theorem R327917 : Reach 327917 := rs (se 3 (by rfl) ⟨61484, by rfl⟩) R122969
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R2326877 : Reach 2326877 := rs (se 3 (by rfl) ⟨436289, by rfl⟩) R872579
theorem R65935 : Reach 65935 := rs (se 1 (by rfl) ⟨49451, by rfl⟩) R98903
theorem R229817 : Reach 229817 := rs (se 2 (by rfl) ⟨86181, by rfl⟩) R172363
theorem R295427 : Reach 295427 := rs (se 1 (by rfl) ⟨221570, by rfl⟩) R443141
theorem R66191 : Reach 66191 := rs (se 1 (by rfl) ⟨49643, by rfl⟩) R99287
theorem R99343 : Reach 99343 := rs (se 1 (by rfl) ⟨74507, by rfl⟩) R149015
theorem R66703 : Reach 66703 := rs (se 1 (by rfl) ⟨50027, by rfl⟩) R100055
theorem R165149 : Reach 165149 := rs (se 3 (by rfl) ⟨30965, by rfl⟩) R61931
theorem R1344869 : Reach 1344869 := rs (se 4 (by rfl) ⟨126081, by rfl⟩) R252163
theorem R99785 : Reach 99785 := rs (se 2 (by rfl) ⟨37419, by rfl⟩) R74839
theorem R132553 : Reach 132553 := rs (se 2 (by rfl) ⟨49707, by rfl⟩) R99415
theorem R460241 : Reach 460241 := rs (se 2 (by rfl) ⟨172590, by rfl⟩) R345181
theorem R886373 : Reach 886373 := rs (se 4 (by rfl) ⟨83097, by rfl⟩) R166195
theorem R67207 : Reach 67207 := rs (se 1 (by rfl) ⟨50405, by rfl⟩) R100811
theorem R67387 : Reach 67387 := rs (se 1 (by rfl) ⟨50540, by rfl⟩) R101081
theorem R165817 : Reach 165817 := rs (se 2 (by rfl) ⟨62181, by rfl⟩) R124363
theorem R133163 : Reach 133163 := rs (se 1 (by rfl) ⟨99872, by rfl⟩) R199745
theorem R100487 : Reach 100487 := rs (se 1 (by rfl) ⟨75365, by rfl⟩) R150731
theorem R133255 : Reach 133255 := rs (se 1 (by rfl) ⟨99941, by rfl⟩) R199883
theorem R592109 : Reach 592109 := rs (se 3 (by rfl) ⟨111020, by rfl⟩) R222041
theorem R67855 : Reach 67855 := rs (se 1 (by rfl) ⟨50891, by rfl⟩) R101783
theorem R133523 : Reach 133523 := rs (se 1 (by rfl) ⟨100142, by rfl⟩) R200285
theorem R133577 : Reach 133577 := rs (se 2 (by rfl) ⟨50091, by rfl⟩) R100183
theorem R133817 : Reach 133817 := rs (se 2 (by rfl) ⟨50181, by rfl⟩) R100363
theorem R428773 : Reach 428773 := rs (se 4 (by rfl) ⟨40197, by rfl⟩) R80395
theorem R68359 : Reach 68359 := rs (se 1 (by rfl) ⟨51269, by rfl⟩) R102539
theorem R101135 : Reach 101135 := rs (se 1 (by rfl) ⟨75851, by rfl⟩) R151703
theorem R133903 : Reach 133903 := rs (se 1 (by rfl) ⟨100427, by rfl⟩) R200855
theorem R428915 : Reach 428915 := rs (se 1 (by rfl) ⟨321686, by rfl⟩) R643373
theorem R330641 : Reach 330641 := rs (se 2 (by rfl) ⟨123990, by rfl⟩) R247981
theorem R68539 : Reach 68539 := rs (se 1 (by rfl) ⟨51404, by rfl⟩) R102809
theorem R363473 : Reach 363473 := rs (se 2 (by rfl) ⟨136302, by rfl⟩) R272605
theorem R199691 : Reach 199691 := rs (se 1 (by rfl) ⟨149768, by rfl⟩) R299537
theorem R1281035 : Reach 1281035 := rs (se 1 (by rfl) ⟨960776, by rfl⟩) R1921553
theorem R592919 : Reach 592919 := rs (se 1 (by rfl) ⟨444689, by rfl⟩) R889379
theorem R199799 : Reach 199799 := rs (se 1 (by rfl) ⟨149849, by rfl⟩) R299699
theorem R134279 : Reach 134279 := rs (se 1 (by rfl) ⟨100709, by rfl⟩) R201419
theorem R167201 : Reach 167201 := rs (se 2 (by rfl) ⟨62700, by rfl⟩) R125401
theorem R101675 : Reach 101675 := rs (se 1 (by rfl) ⟨76256, by rfl⟩) R152513
theorem R134459 : Reach 134459 := rs (se 1 (by rfl) ⟨100844, by rfl⟩) R201689
theorem R167287 : Reach 167287 := rs (se 1 (by rfl) ⟨125465, by rfl⟩) R250931
theorem R69007 : Reach 69007 := rs (se 1 (by rfl) ⟨51755, by rfl⟩) R103511
theorem R265619 : Reach 265619 := rs (se 1 (by rfl) ⟨199214, by rfl⟩) R398429
theorem R134585 : Reach 134585 := rs (se 2 (by rfl) ⟨50469, by rfl⟩) R100939
theorem R102073 : Reach 102073 := rs (se 2 (by rfl) ⟨38277, by rfl⟩) R76555
theorem R200393 : Reach 200393 := rs (se 2 (by rfl) ⟨75147, by rfl⟩) R150295
theorem R134927 : Reach 134927 := rs (se 1 (by rfl) ⟨101195, by rfl⟩) R202391
theorem R134945 : Reach 134945 := rs (se 2 (by rfl) ⟨50604, by rfl⟩) R101209
theorem R69511 : Reach 69511 := rs (se 1 (by rfl) ⟨52133, by rfl⟩) R104267
theorem R233401 : Reach 233401 := rs (se 2 (by rfl) ⟨87525, by rfl⟩) R175051
theorem R69691 : Reach 69691 := rs (se 1 (by rfl) ⟨52268, by rfl⟩) R104537
theorem R135287 : Reach 135287 := rs (se 1 (by rfl) ⟨101465, by rfl⟩) R202931
theorem R135467 : Reach 135467 := rs (se 1 (by rfl) ⟨101600, by rfl⟩) R203201
theorem R102775 : Reach 102775 := rs (se 1 (by rfl) ⟨77081, by rfl⟩) R154163
theorem R201095 : Reach 201095 := rs (se 1 (by rfl) ⟨150821, by rfl⟩) R301643
theorem R135695 : Reach 135695 := rs (se 1 (by rfl) ⟨101771, by rfl⟩) R203543
theorem R70159 : Reach 70159 := rs (se 1 (by rfl) ⟨52619, by rfl⟩) R105239
theorem R102971 : Reach 102971 := rs (se 1 (by rfl) ⟨77228, by rfl⟩) R154457
theorem R397943 : Reach 397943 := rs (se 1 (by rfl) ⟨298457, by rfl⟩) R596915
theorem R135827 : Reach 135827 := rs (se 1 (by rfl) ⟨101870, by rfl⟩) R203741
theorem R135881 : Reach 135881 := rs (se 2 (by rfl) ⟨50955, by rfl⟩) R101911
theorem R201473 : Reach 201473 := rs (se 2 (by rfl) ⟨75552, by rfl⟩) R151105
theorem R332545 : Reach 332545 := rs (se 2 (by rfl) ⟨124704, by rfl⟩) R249409
theorem R70519 : Reach 70519 := rs (se 1 (by rfl) ⟨52889, by rfl⟩) R105779
theorem R103369 : Reach 103369 := rs (se 2 (by rfl) ⟨38763, by rfl⟩) R77527
theorem R332747 : Reach 332747 := rs (se 1 (by rfl) ⟨249560, by rfl⟩) R499121
theorem R70663 : Reach 70663 := rs (se 1 (by rfl) ⟨52997, by rfl⟩) R105995
theorem R267293 : Reach 267293 := rs (se 3 (by rfl) ⟨50117, by rfl⟩) R100235
theorem R70699 : Reach 70699 := rs (se 1 (by rfl) ⟨53024, by rfl⟩) R106049
theorem R70843 : Reach 70843 := rs (se 1 (by rfl) ⟨53132, by rfl⟩) R106265
theorem R300347 : Reach 300347 := rs (se 1 (by rfl) ⟨225260, by rfl⟩) R450521
theorem R595259 : Reach 595259 := rs (se 1 (by rfl) ⟨446444, by rfl⟩) R892889
theorem R136583 : Reach 136583 := rs (se 1 (by rfl) ⟨102437, by rfl⟩) R204875
theorem R300509 : Reach 300509 := rs (se 3 (by rfl) ⟨56345, by rfl⟩) R112691
theorem R202283 : Reach 202283 := rs (se 1 (by rfl) ⟨151712, by rfl⟩) R303425
theorem R136763 : Reach 136763 := rs (se 1 (by rfl) ⟨102572, by rfl⟩) R205145
theorem R300611 : Reach 300611 := rs (se 1 (by rfl) ⟨225458, by rfl⟩) R450917
theorem R661069 : Reach 661069 := rs (se 3 (by rfl) ⟨123950, by rfl⟩) R247901
theorem R169607 : Reach 169607 := rs (se 1 (by rfl) ⟨127205, by rfl⟩) R254411
theorem R104071 : Reach 104071 := rs (se 1 (by rfl) ⟨78053, by rfl⟩) R156107
theorem R136889 : Reach 136889 := rs (se 2 (by rfl) ⟨51333, by rfl⟩) R102667
theorem R300781 : Reach 300781 := rs (se 3 (by rfl) ⟨56396, by rfl⟩) R112793
theorem R300833 : Reach 300833 := rs (se 2 (by rfl) ⟨112812, by rfl⟩) R225625
theorem R169789 : Reach 169789 := rs (se 3 (by rfl) ⟨31835, by rfl⟩) R63671
theorem R169847 : Reach 169847 := rs (se 1 (by rfl) ⟨127385, by rfl⟩) R254771
theorem R300935 : Reach 300935 := rs (se 1 (by rfl) ⟨225701, by rfl⟩) R451403
theorem R268217 : Reach 268217 := rs (se 2 (by rfl) ⟨100581, by rfl⟩) R201163
theorem R137231 : Reach 137231 := rs (se 1 (by rfl) ⟨102923, by rfl⟩) R205847
theorem R137249 : Reach 137249 := rs (se 2 (by rfl) ⟨51468, by rfl⟩) R102937
theorem R71851 : Reach 71851 := rs (se 1 (by rfl) ⟨53888, by rfl⟩) R107777
theorem R104719 : Reach 104719 := rs (se 1 (by rfl) ⟨78539, by rfl⟩) R157079
theorem R137591 : Reach 137591 := rs (se 1 (by rfl) ⟨103193, by rfl⟩) R206387
theorem R203293 : Reach 203293 := rs (se 3 (by rfl) ⟨38117, by rfl⟩) R76235
theorem R137771 : Reach 137771 := rs (se 1 (by rfl) ⟨103328, by rfl⟩) R206657
theorem R301805 : Reach 301805 := rs (se 3 (by rfl) ⟨56588, by rfl⟩) R113177
theorem R236303 : Reach 236303 := rs (se 1 (by rfl) ⟨177227, by rfl⟩) R354455
theorem R105259 : Reach 105259 := rs (se 1 (by rfl) ⟨78944, by rfl⟩) R157889
theorem R203579 : Reach 203579 := rs (se 1 (by rfl) ⟨152684, by rfl⟩) R305369
theorem R138131 : Reach 138131 := rs (se 1 (by rfl) ⟨103598, by rfl⟩) R207197
theorem R1579925 : Reach 1579925 := rs (se 6 (by rfl) ⟨37029, by rfl⟩) R74059
theorem R170905 : Reach 170905 := rs (se 2 (by rfl) ⟨64089, by rfl⟩) R128179
theorem R105401 : Reach 105401 := rs (se 2 (by rfl) ⟨39525, by rfl⟩) R79051
theorem R138185 : Reach 138185 := rs (se 2 (by rfl) ⟨51819, by rfl⟩) R103639
theorem R204065 : Reach 204065 := rs (se 2 (by rfl) ⟨76524, by rfl⟩) R153049
theorem R171521 : Reach 171521 := rs (se 2 (by rfl) ⟨64320, by rfl⟩) R128641
theorem R302615 : Reach 302615 := rs (se 1 (by rfl) ⟨226961, by rfl⟩) R453923
theorem R728605 : Reach 728605 := rs (se 3 (by rfl) ⟨136613, by rfl⟩) R273227
theorem R106103 : Reach 106103 := rs (se 1 (by rfl) ⟨79577, by rfl⟩) R159155
theorem R138887 : Reach 138887 := rs (se 1 (by rfl) ⟨104165, by rfl⟩) R208331
theorem R564965 : Reach 564965 := rs (se 4 (by rfl) ⟨52965, by rfl⟩) R105931
theorem R171805 : Reach 171805 := rs (se 3 (by rfl) ⟨32213, by rfl⟩) R64427
theorem R139067 : Reach 139067 := rs (se 1 (by rfl) ⟨104300, by rfl⟩) R208601
theorem R204659 : Reach 204659 := rs (se 1 (by rfl) ⟨153494, by rfl⟩) R306989
theorem R139193 : Reach 139193 := rs (se 2 (by rfl) ⟨52197, by rfl⟩) R104395
theorem R106529 : Reach 106529 := rs (se 2 (by rfl) ⟨39948, by rfl⟩) R79897
theorem R106697 : Reach 106697 := rs (se 2 (by rfl) ⟨40011, by rfl⟩) R80023
theorem R139535 : Reach 139535 := rs (se 1 (by rfl) ⟨104651, by rfl⟩) R209303
theorem R139553 : Reach 139553 := rs (se 2 (by rfl) ⟨52332, by rfl⟩) R104665
theorem R74119 : Reach 74119 := rs (se 1 (by rfl) ⟨55589, by rfl⟩) R111179
theorem R172489 : Reach 172489 := rs (se 2 (by rfl) ⟨64683, by rfl⟩) R129367
theorem R205373 : Reach 205373 := rs (se 3 (by rfl) ⟨38507, by rfl⟩) R77015
theorem R139895 : Reach 139895 := rs (se 1 (by rfl) ⟨104921, by rfl⟩) R209843
theorem R140075 : Reach 140075 := rs (se 1 (by rfl) ⟨105056, by rfl⟩) R210113
theorem R598873 : Reach 598873 := rs (se 2 (by rfl) ⟨224577, by rfl⟩) R449155
theorem R140147 : Reach 140147 := rs (se 1 (by rfl) ⟨105110, by rfl⟩) R210221
theorem R140435 : Reach 140435 := rs (se 1 (by rfl) ⟨105326, by rfl⟩) R210653
theorem R140489 : Reach 140489 := rs (se 2 (by rfl) ⟨52683, by rfl⟩) R105367
theorem R239419 : Reach 239419 := rs (se 1 (by rfl) ⟨179564, by rfl⟩) R359129
theorem R141191 : Reach 141191 := rs (se 1 (by rfl) ⟨105893, by rfl⟩) R211787
theorem R239507 : Reach 239507 := rs (se 1 (by rfl) ⟨179630, by rfl⟩) R359261
theorem R141209 : Reach 141209 := rs (se 2 (by rfl) ⟨52953, by rfl⟩) R105907
theorem R75691 : Reach 75691 := rs (se 1 (by rfl) ⟨56768, by rfl⟩) R113537
theorem R174095 : Reach 174095 := rs (se 1 (by rfl) ⟨130571, by rfl⟩) R261143
theorem R141371 : Reach 141371 := rs (se 1 (by rfl) ⟨106028, by rfl⟩) R212057
theorem R141497 : Reach 141497 := rs (se 2 (by rfl) ⟨53061, by rfl⟩) R106123
theorem R141569 : Reach 141569 := rs (se 2 (by rfl) ⟨53088, by rfl⟩) R106177
theorem R207251 : Reach 207251 := rs (se 1 (by rfl) ⟨155438, by rfl⟩) R310877
theorem R141839 : Reach 141839 := rs (se 1 (by rfl) ⟨106379, by rfl⟩) R212759
theorem R305693 : Reach 305693 := rs (se 3 (by rfl) ⟨57317, by rfl⟩) R114635
theorem R600605 : Reach 600605 := rs (se 3 (by rfl) ⟨112613, by rfl⟩) R225227
theorem R141857 : Reach 141857 := rs (se 2 (by rfl) ⟨53196, by rfl⟩) R106393
theorem R371243 : Reach 371243 := rs (se 1 (by rfl) ⟨278432, by rfl⟩) R556865
theorem R600641 : Reach 600641 := rs (se 2 (by rfl) ⟨225240, by rfl⟩) R450481
theorem R141911 : Reach 141911 := rs (se 1 (by rfl) ⟨106433, by rfl⟩) R212867
theorem R895607 : Reach 895607 := rs (se 1 (by rfl) ⟨671705, by rfl⟩) R1343411
theorem R76459 : Reach 76459 := rs (se 1 (by rfl) ⟨57344, by rfl⟩) R114689
theorem R306179 : Reach 306179 := rs (se 1 (by rfl) ⟨229634, by rfl⟩) R459269
theorem R437309 : Reach 437309 := rs (se 3 (by rfl) ⟨81995, by rfl⟩) R163991
theorem R175223 : Reach 175223 := rs (se 1 (by rfl) ⟨131417, by rfl⟩) R262835
theorem R437537 : Reach 437537 := rs (se 2 (by rfl) ⟨164076, by rfl⟩) R328153
theorem R339335 : Reach 339335 := rs (se 1 (by rfl) ⟨254501, by rfl⟩) R509003
theorem R77431 : Reach 77431 := rs (se 1 (by rfl) ⟨58073, by rfl⟩) R116147
theorem R208655 : Reach 208655 := rs (se 1 (by rfl) ⟨156491, by rfl⟩) R312983
theorem R1027889 : Reach 1027889 := rs (se 2 (by rfl) ⟨385458, by rfl⟩) R770917
theorem R77755 : Reach 77755 := rs (se 1 (by rfl) ⟨58316, by rfl⟩) R116633
theorem R208925 : Reach 208925 := rs (se 3 (by rfl) ⟨39173, by rfl⟩) R78347
theorem R242129 : Reach 242129 := rs (se 2 (by rfl) ⟨90798, by rfl⟩) R181597
theorem R307799 : Reach 307799 := rs (se 1 (by rfl) ⟨230849, by rfl⟩) R461699
theorem R537281 : Reach 537281 := rs (se 2 (by rfl) ⟨201480, by rfl⟩) R402961
theorem R176897 : Reach 176897 := rs (se 2 (by rfl) ⟨66336, by rfl⟩) R132673
theorem R177011 : Reach 177011 := rs (se 1 (by rfl) ⟨132758, by rfl⟩) R265517
theorem R78727 : Reach 78727 := rs (se 1 (by rfl) ⟨59045, by rfl⟩) R118091
theorem R308285 : Reach 308285 := rs (se 3 (by rfl) ⟨57803, by rfl⟩) R115607
theorem R177353 : Reach 177353 := rs (se 2 (by rfl) ⟨66507, by rfl⟩) R133015
theorem R701729 : Reach 701729 := rs (se 2 (by rfl) ⟨263148, by rfl⟩) R526297
theorem R79147 : Reach 79147 := rs (se 1 (by rfl) ⟨59360, by rfl⟩) R118721
theorem R210329 : Reach 210329 := rs (se 2 (by rfl) ⟨78873, by rfl⟩) R157747
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R308701 : Reach 308701 := rs (se 3 (by rfl) ⟨57881, by rfl⟩) R115763
theorem R79375 : Reach 79375 := rs (se 1 (by rfl) ⟨59531, by rfl⟩) R119063
theorem R1226497 : Reach 1226497 := rs (se 2 (by rfl) ⟨459936, by rfl⟩) R919873
theorem R112585 : Reach 112585 := rs (se 2 (by rfl) ⟨42219, by rfl⟩) R84439
theorem R243665 : Reach 243665 := rs (se 2 (by rfl) ⟨91374, by rfl⟩) R182749
theorem R735277 : Reach 735277 := rs (se 3 (by rfl) ⟨137864, by rfl⟩) R275729
theorem R342083 : Reach 342083 := rs (se 1 (by rfl) ⟨256562, by rfl⟩) R513125
theorem R211031 : Reach 211031 := rs (se 1 (by rfl) ⟨158273, by rfl⟩) R316547
theorem R211409 : Reach 211409 := rs (se 2 (by rfl) ⟨79278, by rfl⟩) R158557
theorem R342539 : Reach 342539 := rs (se 1 (by rfl) ⟨256904, by rfl⟩) R513809
theorem R80443 : Reach 80443 := rs (se 1 (by rfl) ⟨60332, by rfl⟩) R120665
theorem R211517 : Reach 211517 := rs (se 3 (by rfl) ⟨39659, by rfl⟩) R79319
theorem R440909 : Reach 440909 := rs (se 3 (by rfl) ⟨82670, by rfl⟩) R165341
theorem R310067 : Reach 310067 := rs (se 1 (by rfl) ⟨232550, by rfl⟩) R465101
theorem R179243 : Reach 179243 := rs (se 1 (by rfl) ⟨134432, by rfl⟩) R268865
theorem R310391 : Reach 310391 := rs (se 1 (by rfl) ⟨232793, by rfl⟩) R465587
theorem R179471 : Reach 179471 := rs (se 1 (by rfl) ⟨134603, by rfl⟩) R269207
theorem R834875 : Reach 834875 := rs (se 1 (by rfl) ⟨626156, by rfl⟩) R1252313
theorem R212921 : Reach 212921 := rs (se 2 (by rfl) ⟨79845, by rfl⟩) R159691
theorem R311363 : Reach 311363 := rs (se 1 (by rfl) ⟨233522, by rfl⟩) R467045
theorem R213229 : Reach 213229 := rs (se 3 (by rfl) ⟨39980, by rfl⟩) R79961
theorem R311687 : Reach 311687 := rs (se 1 (by rfl) ⟨233765, by rfl⟩) R467531
theorem R115091 : Reach 115091 := rs (se 1 (by rfl) ⟨86318, by rfl⟩) R172637
theorem R967133 : Reach 967133 := rs (se 3 (by rfl) ⟨181337, by rfl⟩) R362675
theorem R115319 : Reach 115319 := rs (se 1 (by rfl) ⟨86489, by rfl⟩) R172979
theorem R312331 : Reach 312331 := rs (se 1 (by rfl) ⟨234248, by rfl⟩) R468497
theorem R477245 : Reach 477245 := rs (se 3 (by rfl) ⟨89483, by rfl⟩) R178967
theorem R313463 : Reach 313463 := rs (se 1 (by rfl) ⟨235097, by rfl⟩) R470195
theorem R1001645 : Reach 1001645 := rs (se 3 (by rfl) ⟨187808, by rfl⟩) R375617
theorem R117035 : Reach 117035 := rs (se 1 (by rfl) ⟨87776, by rfl⟩) R175553
theorem R346457 : Reach 346457 := rs (se 2 (by rfl) ⟨129921, by rfl⟩) R259843
theorem R84359 : Reach 84359 := rs (se 1 (by rfl) ⟨63269, by rfl⟩) R126539
theorem R117263 : Reach 117263 := rs (se 1 (by rfl) ⟨87947, by rfl⟩) R175895
theorem R379511 : Reach 379511 := rs (se 1 (by rfl) ⟨284633, by rfl⟩) R569267
theorem R84667 : Reach 84667 := rs (se 1 (by rfl) ⟨63500, by rfl⟩) R127001
theorem R183073 : Reach 183073 := rs (se 2 (by rfl) ⟨68652, by rfl⟩) R137305
theorem R346913 : Reach 346913 := rs (se 2 (by rfl) ⟨130092, by rfl⟩) R260185
theorem R150407 : Reach 150407 := rs (se 1 (by rfl) ⟨112805, by rfl⟩) R225611
theorem R150457 : Reach 150457 := rs (se 2 (by rfl) ⟨56421, by rfl⟩) R112843
theorem R347165 : Reach 347165 := rs (se 3 (by rfl) ⟨65093, by rfl⟩) R130187
theorem R675053 : Reach 675053 := rs (se 3 (by rfl) ⟨126572, by rfl⟩) R253145
theorem R183809 : Reach 183809 := rs (se 2 (by rfl) ⟨68928, by rfl⟩) R137857
theorem R151055 : Reach 151055 := rs (se 1 (by rfl) ⟨113291, by rfl⟩) R226583
theorem R85817 : Reach 85817 := rs (se 2 (by rfl) ⟨32181, by rfl⟩) R64363
theorem R315251 : Reach 315251 := rs (se 1 (by rfl) ⟨236438, by rfl⟩) R472877
theorem R118675 : Reach 118675 := rs (se 1 (by rfl) ⟨89006, by rfl⟩) R178013
theorem R118903 : Reach 118903 := rs (se 1 (by rfl) ⟨89177, by rfl⟩) R178355
theorem R151753 : Reach 151753 := rs (se 2 (by rfl) ⟨56907, by rfl⟩) R113815
theorem R414011 : Reach 414011 := rs (se 1 (by rfl) ⟨310508, by rfl⟩) R621017
theorem R151895 : Reach 151895 := rs (se 1 (by rfl) ⟨113921, by rfl⟩) R227843
theorem R315737 : Reach 315737 := rs (se 2 (by rfl) ⟨118401, by rfl⟩) R236803
theorem R1036637 : Reach 1036637 := rs (se 3 (by rfl) ⟨194369, by rfl⟩) R388739
theorem R479773 : Reach 479773 := rs (se 3 (by rfl) ⟨89957, by rfl⟩) R179915
theorem R217687 : Reach 217687 := rs (se 1 (by rfl) ⟨163265, by rfl⟩) R326531
theorem R643889 : Reach 643889 := rs (se 2 (by rfl) ⟨241458, by rfl⟩) R482917
theorem R316709 : Reach 316709 := rs (se 4 (by rfl) ⟨29691, by rfl⟩) R59383
theorem R87355 : Reach 87355 := rs (se 1 (by rfl) ⟨65516, by rfl⟩) R131033
theorem R349555 : Reach 349555 := rs (se 1 (by rfl) ⟨262166, by rfl⟩) R524333
theorem R382429 : Reach 382429 := rs (se 3 (by rfl) ⟨71705, by rfl⟩) R143411
theorem R87799 : Reach 87799 := rs (se 1 (by rfl) ⟨65849, by rfl⟩) R131699
theorem R186401 : Reach 186401 := rs (se 2 (by rfl) ⟨69900, by rfl⟩) R139801
theorem R153971 : Reach 153971 := rs (se 1 (by rfl) ⟨115478, by rfl⟩) R230957
theorem R317843 : Reach 317843 := rs (se 1 (by rfl) ⟨238382, by rfl⟩) R476765
theorem R186923 : Reach 186923 := rs (se 1 (by rfl) ⟨140192, by rfl⟩) R280385
theorem R88619 : Reach 88619 := rs (se 1 (by rfl) ⟨66464, by rfl⟩) R132929
theorem R88763 : Reach 88763 := rs (se 1 (by rfl) ⟨66572, by rfl⟩) R133145
theorem R383717 : Reach 383717 := rs (se 4 (by rfl) ⟨35973, by rfl⟩) R71947
theorem R88823 : Reach 88823 := rs (se 1 (by rfl) ⟨66617, by rfl⟩) R133235
theorem R88847 : Reach 88847 := rs (se 1 (by rfl) ⟨66635, by rfl⟩) R133271
theorem R351013 : Reach 351013 := rs (se 4 (by rfl) ⟨32907, by rfl⟩) R65815
theorem R88889 : Reach 88889 := rs (se 2 (by rfl) ⟨33333, by rfl⟩) R66667
theorem R154487 : Reach 154487 := rs (se 1 (by rfl) ⟨115865, by rfl⟩) R231731
theorem R88967 : Reach 88967 := rs (se 1 (by rfl) ⟨66725, by rfl⟩) R133451
theorem R89003 : Reach 89003 := rs (se 1 (by rfl) ⟨66752, by rfl⟩) R133505
theorem R89033 : Reach 89033 := rs (se 2 (by rfl) ⟨33387, by rfl⟩) R66775
theorem R89147 : Reach 89147 := rs (se 1 (by rfl) ⟨66860, by rfl⟩) R133721
theorem R89207 : Reach 89207 := rs (se 1 (by rfl) ⟨66905, by rfl⟩) R133811
theorem R89231 : Reach 89231 := rs (se 1 (by rfl) ⟨66923, by rfl⟩) R133847
theorem R89273 : Reach 89273 := rs (se 2 (by rfl) ⟨33477, by rfl⟩) R66955
theorem R351469 : Reach 351469 := rs (se 3 (by rfl) ⟨65900, by rfl⟩) R131801
theorem R89351 : Reach 89351 := rs (se 1 (by rfl) ⟨67013, by rfl⟩) R134027
theorem R89387 : Reach 89387 := rs (se 1 (by rfl) ⟨67040, by rfl⟩) R134081
theorem R351539 : Reach 351539 := rs (se 1 (by rfl) ⟨263654, by rfl⟩) R527309
theorem R89417 : Reach 89417 := rs (se 2 (by rfl) ⟨33531, by rfl⟩) R67063
theorem R89531 : Reach 89531 := rs (se 1 (by rfl) ⟨67148, by rfl⟩) R134297
theorem R89591 : Reach 89591 := rs (se 1 (by rfl) ⟨67193, by rfl⟩) R134387
theorem R679427 : Reach 679427 := rs (se 1 (by rfl) ⟨509570, by rfl⟩) R1019141
theorem R89615 : Reach 89615 := rs (se 1 (by rfl) ⟨67211, by rfl⟩) R134423
theorem R89657 : Reach 89657 := rs (se 2 (by rfl) ⟨33621, by rfl⟩) R67243
theorem R89735 : Reach 89735 := rs (se 1 (by rfl) ⟨67301, by rfl⟩) R134603
theorem R89771 : Reach 89771 := rs (se 1 (by rfl) ⟨67328, by rfl⟩) R134657
theorem R89801 : Reach 89801 := rs (se 2 (by rfl) ⟨33675, by rfl⟩) R67351
theorem R89915 : Reach 89915 := rs (se 1 (by rfl) ⟨67436, by rfl⟩) R134873
theorem R155479 : Reach 155479 := rs (se 1 (by rfl) ⟨116609, by rfl⟩) R233219
theorem R89975 : Reach 89975 := rs (se 1 (by rfl) ⟨67481, by rfl⟩) R134963
theorem R89999 : Reach 89999 := rs (se 1 (by rfl) ⟨67499, by rfl⟩) R134999
theorem R90041 : Reach 90041 := rs (se 2 (by rfl) ⟨33765, by rfl⟩) R67531
theorem R90119 : Reach 90119 := rs (se 1 (by rfl) ⟨67589, by rfl⟩) R135179
theorem R221195 : Reach 221195 := rs (se 1 (by rfl) ⟨165896, by rfl⟩) R331793
theorem R90155 : Reach 90155 := rs (se 1 (by rfl) ⟨67616, by rfl⟩) R135233
theorem R90185 : Reach 90185 := rs (se 2 (by rfl) ⟨33819, by rfl⟩) R67639
theorem R155783 : Reach 155783 := rs (se 1 (by rfl) ⟨116837, by rfl⟩) R233675
theorem R90299 : Reach 90299 := rs (se 1 (by rfl) ⟨67724, by rfl⟩) R135449
theorem R90359 : Reach 90359 := rs (se 1 (by rfl) ⟨67769, by rfl⟩) R135539
theorem R155915 : Reach 155915 := rs (se 1 (by rfl) ⟨116936, by rfl⟩) R233873
theorem R90383 : Reach 90383 := rs (se 1 (by rfl) ⟨67787, by rfl⟩) R135575
theorem R942353 : Reach 942353 := rs (se 2 (by rfl) ⟨353382, by rfl⟩) R706765
theorem R90425 : Reach 90425 := rs (se 2 (by rfl) ⟨33909, by rfl⟩) R67819
theorem R90503 : Reach 90503 := rs (se 1 (by rfl) ⟨67877, by rfl⟩) R135755
theorem R90539 : Reach 90539 := rs (se 1 (by rfl) ⟨67904, by rfl⟩) R135809
theorem R451001 : Reach 451001 := rs (se 2 (by rfl) ⟨169125, by rfl⟩) R338251
theorem R90569 : Reach 90569 := rs (se 2 (by rfl) ⟨33963, by rfl⟩) R67927
theorem R516611 : Reach 516611 := rs (se 1 (by rfl) ⟨387458, by rfl⟩) R774917
theorem R582187 : Reach 582187 := rs (se 1 (by rfl) ⟨436640, by rfl⟩) R873281
theorem R90683 : Reach 90683 := rs (se 1 (by rfl) ⟨68012, by rfl⟩) R136025
theorem R90743 : Reach 90743 := rs (se 1 (by rfl) ⟨68057, by rfl⟩) R136115
theorem R90767 : Reach 90767 := rs (se 1 (by rfl) ⟨68075, by rfl⟩) R136151
theorem R90809 : Reach 90809 := rs (se 2 (by rfl) ⟨34053, by rfl⟩) R68107
theorem R352997 : Reach 352997 := rs (se 4 (by rfl) ⟨33093, by rfl⟩) R66187
theorem R90887 : Reach 90887 := rs (se 1 (by rfl) ⟨68165, by rfl⟩) R136331
theorem R156431 : Reach 156431 := rs (se 1 (by rfl) ⟨117323, by rfl⟩) R234647
theorem R90923 : Reach 90923 := rs (se 1 (by rfl) ⟨68192, by rfl⟩) R136385
theorem R90953 : Reach 90953 := rs (se 2 (by rfl) ⟨34107, by rfl⟩) R68215
theorem R156563 : Reach 156563 := rs (se 1 (by rfl) ⟨117422, by rfl⟩) R234845
theorem R91067 : Reach 91067 := rs (se 1 (by rfl) ⟨68300, by rfl⟩) R136601
theorem R91127 : Reach 91127 := rs (se 1 (by rfl) ⟨68345, by rfl⟩) R136691
theorem R91151 : Reach 91151 := rs (se 1 (by rfl) ⟨68363, by rfl⟩) R136727
theorem R91193 : Reach 91193 := rs (se 2 (by rfl) ⟨34197, by rfl⟩) R68395
theorem R255095 : Reach 255095 := rs (se 1 (by rfl) ⟨191321, by rfl⟩) R382643
theorem R91271 : Reach 91271 := rs (se 1 (by rfl) ⟨68453, by rfl⟩) R136907
theorem R91307 : Reach 91307 := rs (se 1 (by rfl) ⟨68480, by rfl⟩) R136961
theorem R91337 : Reach 91337 := rs (se 2 (by rfl) ⟨34251, by rfl⟩) R68503
theorem R124105 : Reach 124105 := rs (se 2 (by rfl) ⟨46539, by rfl⟩) R93079
theorem R91451 : Reach 91451 := rs (se 1 (by rfl) ⟨68588, by rfl⟩) R137177
theorem R91511 : Reach 91511 := rs (se 1 (by rfl) ⟨68633, by rfl⟩) R137267
theorem R3433859 : Reach 3433859 := rs (se 1 (by rfl) ⟨2575394, by rfl⟩) R5150789
theorem R91535 : Reach 91535 := rs (se 1 (by rfl) ⟨68651, by rfl⟩) R137303
theorem R91577 : Reach 91577 := rs (se 2 (by rfl) ⟨34341, by rfl⟩) R68683
theorem R91655 : Reach 91655 := rs (se 1 (by rfl) ⟨68741, by rfl⟩) R137483
theorem R91691 : Reach 91691 := rs (se 1 (by rfl) ⟨68768, by rfl⟩) R137537
theorem R91721 : Reach 91721 := rs (se 2 (by rfl) ⟨34395, by rfl⟩) R68791
theorem R714419 : Reach 714419 := rs (se 1 (by rfl) ⟨535814, by rfl⟩) R1071629
theorem R91835 : Reach 91835 := rs (se 1 (by rfl) ⟨68876, by rfl⟩) R137753
theorem R91895 : Reach 91895 := rs (se 1 (by rfl) ⟨68921, by rfl⟩) R137843
theorem R59143 : Reach 59143 := rs (se 1 (by rfl) ⟨44357, by rfl⟩) R88715
theorem R59151 : Reach 59151 := rs (se 1 (by rfl) ⟨44363, by rfl⟩) R88727
theorem R91919 : Reach 91919 := rs (se 1 (by rfl) ⟨68939, by rfl⟩) R137879
theorem R91961 : Reach 91961 := rs (se 2 (by rfl) ⟨34485, by rfl⟩) R68971
theorem R59195 : Reach 59195 := rs (se 1 (by rfl) ⟨44396, by rfl⟩) R88793
theorem R59271 : Reach 59271 := rs (se 1 (by rfl) ⟨44453, by rfl⟩) R88907
theorem R92039 : Reach 92039 := rs (se 1 (by rfl) ⟨69029, by rfl⟩) R138059
theorem R59279 : Reach 59279 := rs (se 1 (by rfl) ⟨44459, by rfl⟩) R88919
theorem R92075 : Reach 92075 := rs (se 1 (by rfl) ⟨69056, by rfl⟩) R138113
theorem R59323 : Reach 59323 := rs (se 1 (by rfl) ⟨44492, by rfl⟩) R88985
theorem R92105 : Reach 92105 := rs (se 2 (by rfl) ⟨34539, by rfl⟩) R69079
theorem R157697 : Reach 157697 := rs (se 2 (by rfl) ⟨59136, by rfl⟩) R118273
theorem R59399 : Reach 59399 := rs (se 1 (by rfl) ⟨44549, by rfl⟩) R89099
theorem R190475 : Reach 190475 := rs (se 1 (by rfl) ⟨142856, by rfl⟩) R285713
theorem R59407 : Reach 59407 := rs (se 1 (by rfl) ⟨44555, by rfl⟩) R89111
theorem R59451 : Reach 59451 := rs (se 1 (by rfl) ⟨44588, by rfl⟩) R89177
theorem R92219 : Reach 92219 := rs (se 1 (by rfl) ⟨69164, by rfl⟩) R138329
theorem R92279 : Reach 92279 := rs (se 1 (by rfl) ⟨69209, by rfl⟩) R138419
theorem R59527 : Reach 59527 := rs (se 1 (by rfl) ⟨44645, by rfl⟩) R89291
theorem R59535 : Reach 59535 := rs (se 1 (by rfl) ⟨44651, by rfl⟩) R89303
theorem R92303 : Reach 92303 := rs (se 1 (by rfl) ⟨69227, by rfl⟩) R138455
theorem R92345 : Reach 92345 := rs (se 2 (by rfl) ⟨34629, by rfl⟩) R69259
theorem R59579 : Reach 59579 := rs (se 1 (by rfl) ⟨44684, by rfl⟩) R89369
theorem R59655 : Reach 59655 := rs (se 1 (by rfl) ⟨44741, by rfl⟩) R89483
theorem R92423 : Reach 92423 := rs (se 1 (by rfl) ⟨69317, by rfl⟩) R138635
theorem R59663 : Reach 59663 := rs (se 1 (by rfl) ⟨44747, by rfl⟩) R89495
theorem R92459 : Reach 92459 := rs (se 1 (by rfl) ⟨69344, by rfl⟩) R138689
theorem R59707 : Reach 59707 := rs (se 1 (by rfl) ⟨44780, by rfl⟩) R89561
theorem R92489 : Reach 92489 := rs (se 2 (by rfl) ⟨34683, by rfl⟩) R69367
theorem R158071 : Reach 158071 := rs (se 1 (by rfl) ⟨118553, by rfl⟩) R237107
theorem R59783 : Reach 59783 := rs (se 1 (by rfl) ⟨44837, by rfl⟩) R89675
theorem R59791 : Reach 59791 := rs (se 1 (by rfl) ⟨44843, by rfl⟩) R89687
theorem R59835 : Reach 59835 := rs (se 1 (by rfl) ⟨44876, by rfl⟩) R89753
theorem R92603 : Reach 92603 := rs (se 1 (by rfl) ⟨69452, by rfl⟩) R138905
theorem R322001 : Reach 322001 := rs (se 2 (by rfl) ⟨120750, by rfl⟩) R241501
theorem R92663 : Reach 92663 := rs (se 1 (by rfl) ⟨69497, by rfl⟩) R138995
theorem R59911 : Reach 59911 := rs (se 1 (by rfl) ⟨44933, by rfl⟩) R89867
theorem R59919 : Reach 59919 := rs (se 1 (by rfl) ⟨44939, by rfl⟩) R89879
theorem R92687 : Reach 92687 := rs (se 1 (by rfl) ⟨69515, by rfl⟩) R139031
theorem R92729 : Reach 92729 := rs (se 2 (by rfl) ⟨34773, by rfl⟩) R69547
theorem R59963 : Reach 59963 := rs (se 1 (by rfl) ⟨44972, by rfl⟩) R89945
theorem R60039 : Reach 60039 := rs (se 1 (by rfl) ⟨45029, by rfl⟩) R90059
theorem R92807 : Reach 92807 := rs (se 1 (by rfl) ⟨69605, by rfl⟩) R139211
theorem R60047 : Reach 60047 := rs (se 1 (by rfl) ⟨45035, by rfl⟩) R90071
theorem R92843 : Reach 92843 := rs (se 1 (by rfl) ⟨69632, by rfl⟩) R139265
theorem R60091 : Reach 60091 := rs (se 1 (by rfl) ⟨45068, by rfl⟩) R90137
theorem R92873 : Reach 92873 := rs (se 2 (by rfl) ⟨34827, by rfl⟩) R69655
theorem R1010393 : Reach 1010393 := rs (se 2 (by rfl) ⟨378897, by rfl⟩) R757795
theorem R256769 : Reach 256769 := rs (se 2 (by rfl) ⟨96288, by rfl⟩) R192577
theorem R60167 : Reach 60167 := rs (se 1 (by rfl) ⟨45125, by rfl⟩) R90251
theorem R60175 : Reach 60175 := rs (se 1 (by rfl) ⟨45131, by rfl⟩) R90263
theorem R1076003 : Reach 1076003 := rs (se 1 (by rfl) ⟨807002, by rfl⟩) R1614005
theorem R158507 : Reach 158507 := rs (se 1 (by rfl) ⟨118880, by rfl⟩) R237761
theorem R60219 : Reach 60219 := rs (se 1 (by rfl) ⟨45164, by rfl⟩) R90329
theorem R289595 : Reach 289595 := rs (se 1 (by rfl) ⟨217196, by rfl⟩) R434393
theorem R92987 : Reach 92987 := rs (se 1 (by rfl) ⟨69740, by rfl⟩) R139481
theorem R93047 : Reach 93047 := rs (se 1 (by rfl) ⟨69785, by rfl⟩) R139571
theorem R60295 : Reach 60295 := rs (se 1 (by rfl) ⟨45221, by rfl⟩) R90443
theorem R60303 : Reach 60303 := rs (se 1 (by rfl) ⟨45227, by rfl⟩) R90455
theorem R93071 : Reach 93071 := rs (se 1 (by rfl) ⟨69803, by rfl⟩) R139607
theorem R93113 : Reach 93113 := rs (se 2 (by rfl) ⟨34917, by rfl⟩) R69835
theorem R60347 : Reach 60347 := rs (se 1 (by rfl) ⟨45260, by rfl⟩) R90521
theorem R60423 : Reach 60423 := rs (se 1 (by rfl) ⟨45317, by rfl⟩) R90635
theorem R93191 : Reach 93191 := rs (se 1 (by rfl) ⟨69893, by rfl⟩) R139787
theorem R60431 : Reach 60431 := rs (se 1 (by rfl) ⟨45323, by rfl⟩) R90647
theorem R93227 : Reach 93227 := rs (se 1 (by rfl) ⟨69920, by rfl⟩) R139841
theorem R60475 : Reach 60475 := rs (se 1 (by rfl) ⟨45356, by rfl⟩) R90713
theorem R93257 : Reach 93257 := rs (se 2 (by rfl) ⟨34971, by rfl⟩) R69943
theorem R60551 : Reach 60551 := rs (se 1 (by rfl) ⟨45413, by rfl⟩) R90827
theorem R60559 : Reach 60559 := rs (se 1 (by rfl) ⟨45419, by rfl⟩) R90839
theorem R60603 : Reach 60603 := rs (se 1 (by rfl) ⟨45452, by rfl⟩) R90905
theorem R93371 : Reach 93371 := rs (se 1 (by rfl) ⟨70028, by rfl⟩) R140057
theorem R60679 : Reach 60679 := rs (se 1 (by rfl) ⟨45509, by rfl⟩) R91019
theorem R60687 : Reach 60687 := rs (se 1 (by rfl) ⟨45515, by rfl⟩) R91031
theorem R93455 : Reach 93455 := rs (se 1 (by rfl) ⟨70091, by rfl⟩) R140183
theorem R60731 : Reach 60731 := rs (se 1 (by rfl) ⟨45548, by rfl⟩) R91097
theorem R60807 : Reach 60807 := rs (se 1 (by rfl) ⟨45605, by rfl⟩) R91211
theorem R93575 : Reach 93575 := rs (se 1 (by rfl) ⟨70181, by rfl⟩) R140363
theorem R60815 : Reach 60815 := rs (se 1 (by rfl) ⟨45611, by rfl⟩) R91223
theorem R60859 : Reach 60859 := rs (se 1 (by rfl) ⟨45644, by rfl⟩) R91289
theorem R93641 : Reach 93641 := rs (se 2 (by rfl) ⟨35115, by rfl⟩) R70231
theorem R60935 : Reach 60935 := rs (se 1 (by rfl) ⟨45701, by rfl⟩) R91403
theorem R60943 : Reach 60943 := rs (se 1 (by rfl) ⟨45707, by rfl⟩) R91415
theorem R126497 : Reach 126497 := rs (se 2 (by rfl) ⟨47436, by rfl⟩) R94873
theorem R159275 : Reach 159275 := rs (se 1 (by rfl) ⟨119456, by rfl⟩) R238913
theorem R60987 : Reach 60987 := rs (se 1 (by rfl) ⟨45740, by rfl⟩) R91481
theorem R93755 : Reach 93755 := rs (se 1 (by rfl) ⟨70316, by rfl⟩) R140633
theorem R159347 : Reach 159347 := rs (se 1 (by rfl) ⟨119510, by rfl⟩) R239021
theorem R93815 : Reach 93815 := rs (se 1 (by rfl) ⟨70361, by rfl⟩) R140723
theorem R61063 : Reach 61063 := rs (se 1 (by rfl) ⟨45797, by rfl⟩) R91595
theorem R159367 : Reach 159367 := rs (se 1 (by rfl) ⟨119525, by rfl⟩) R239051
theorem R61071 : Reach 61071 := rs (se 1 (by rfl) ⟨45803, by rfl⟩) R91607
theorem R93881 : Reach 93881 := rs (se 2 (by rfl) ⟨35205, by rfl⟩) R70411
theorem R61115 : Reach 61115 := rs (se 1 (by rfl) ⟨45836, by rfl⟩) R91673
theorem R61191 : Reach 61191 := rs (se 1 (by rfl) ⟨45893, by rfl⟩) R91787
theorem R61199 : Reach 61199 := rs (se 1 (by rfl) ⟨45899, by rfl⟩) R91799
theorem R93995 : Reach 93995 := rs (se 1 (by rfl) ⟨70496, by rfl⟩) R140993
theorem R61243 : Reach 61243 := rs (se 1 (by rfl) ⟨45932, by rfl⟩) R91865
theorem R225139 : Reach 225139 := rs (se 1 (by rfl) ⟨168854, by rfl⟩) R337709
theorem R126839 : Reach 126839 := rs (se 1 (by rfl) ⟨95129, by rfl⟩) R190259
theorem R61319 : Reach 61319 := rs (se 1 (by rfl) ⟨45989, by rfl⟩) R91979
theorem R61327 : Reach 61327 := rs (se 1 (by rfl) ⟨45995, by rfl⟩) R91991
theorem R159641 : Reach 159641 := rs (se 2 (by rfl) ⟨59865, by rfl⟩) R119731
theorem R61371 : Reach 61371 := rs (se 1 (by rfl) ⟨46028, by rfl⟩) R92057
theorem R61447 : Reach 61447 := rs (se 1 (by rfl) ⟨46085, by rfl⟩) R92171
theorem R61455 : Reach 61455 := rs (se 1 (by rfl) ⟨46091, by rfl⟩) R92183
theorem R94223 : Reach 94223 := rs (se 1 (by rfl) ⟨70667, by rfl⟩) R141335
theorem R1339415 : Reach 1339415 := rs (se 1 (by rfl) ⟨1004561, by rfl⟩) R2009123
theorem R61499 : Reach 61499 := rs (se 1 (by rfl) ⟨46124, by rfl⟩) R92249
theorem R61575 : Reach 61575 := rs (se 1 (by rfl) ⟨46181, by rfl⟩) R92363
theorem R94343 : Reach 94343 := rs (se 1 (by rfl) ⟨70757, by rfl⟩) R141515
theorem R61583 : Reach 61583 := rs (se 1 (by rfl) ⟨46187, by rfl⟩) R92375
theorem R61627 : Reach 61627 := rs (se 1 (by rfl) ⟨46220, by rfl⟩) R92441
theorem R94409 : Reach 94409 := rs (se 2 (by rfl) ⟨35403, by rfl⟩) R70807
theorem R61703 : Reach 61703 := rs (se 1 (by rfl) ⟨46277, by rfl⟩) R92555
theorem R61711 : Reach 61711 := rs (se 1 (by rfl) ⟨46283, by rfl⟩) R92567
theorem R127291 : Reach 127291 := rs (se 1 (by rfl) ⟨95468, by rfl⟩) R190937
theorem R61755 : Reach 61755 := rs (se 1 (by rfl) ⟨46316, by rfl⟩) R92633
theorem R94523 : Reach 94523 := rs (se 1 (by rfl) ⟨70892, by rfl⟩) R141785
theorem R94583 : Reach 94583 := rs (se 1 (by rfl) ⟨70937, by rfl⟩) R141875
theorem R61831 : Reach 61831 := rs (se 1 (by rfl) ⟨46373, by rfl⟩) R92747
theorem R61839 : Reach 61839 := rs (se 1 (by rfl) ⟨46379, by rfl⟩) R92759
theorem R94649 : Reach 94649 := rs (se 2 (by rfl) ⟨35493, by rfl⟩) R70987
theorem R61883 : Reach 61883 := rs (se 1 (by rfl) ⟨46412, by rfl⟩) R92825
theorem R61959 : Reach 61959 := rs (se 1 (by rfl) ⟨46469, by rfl⟩) R92939
theorem R61967 : Reach 61967 := rs (se 1 (by rfl) ⟨46475, by rfl⟩) R92951
theorem R160271 : Reach 160271 := rs (se 1 (by rfl) ⟨120203, by rfl⟩) R240407
theorem R62011 : Reach 62011 := rs (se 1 (by rfl) ⟨46508, by rfl⟩) R93017
theorem R62087 : Reach 62087 := rs (se 1 (by rfl) ⟨46565, by rfl⟩) R93131
theorem R62095 : Reach 62095 := rs (se 1 (by rfl) ⟨46571, by rfl⟩) R93143
theorem R62139 : Reach 62139 := rs (se 1 (by rfl) ⟨46604, by rfl⟩) R93209
theorem R62215 : Reach 62215 := rs (se 1 (by rfl) ⟨46661, by rfl⟩) R93323
theorem R62223 : Reach 62223 := rs (se 1 (by rfl) ⟨46667, by rfl⟩) R93335
theorem R62267 : Reach 62267 := rs (se 1 (by rfl) ⟨46700, by rfl⟩) R93401
theorem R62343 : Reach 62343 := rs (se 1 (by rfl) ⟨46757, by rfl⟩) R93515
theorem R62351 : Reach 62351 := rs (se 1 (by rfl) ⟨46763, by rfl⟩) R93527
theorem R62395 : Reach 62395 := rs (se 1 (by rfl) ⟨46796, by rfl⟩) R93593
theorem R62471 : Reach 62471 := rs (se 1 (by rfl) ⟨46853, by rfl⟩) R93707
theorem R62479 : Reach 62479 := rs (se 1 (by rfl) ⟨46859, by rfl⟩) R93719
theorem R291863 : Reach 291863 := rs (se 1 (by rfl) ⟨218897, by rfl⟩) R437795
theorem R62523 : Reach 62523 := rs (se 1 (by rfl) ⟨46892, by rfl⟩) R93785
theorem R226423 : Reach 226423 := rs (se 1 (by rfl) ⟨169817, by rfl⟩) R339635
theorem R62599 : Reach 62599 := rs (se 1 (by rfl) ⟨46949, by rfl⟩) R93899
theorem R62607 : Reach 62607 := rs (se 1 (by rfl) ⟨46955, by rfl⟩) R93911
theorem R62651 : Reach 62651 := rs (se 1 (by rfl) ⟨46988, by rfl⟩) R93977
theorem R62727 : Reach 62727 := rs (se 1 (by rfl) ⟨47045, by rfl⟩) R94091
theorem R62735 : Reach 62735 := rs (se 1 (by rfl) ⟨47051, by rfl⟩) R94103
theorem R128299 : Reach 128299 := rs (se 1 (by rfl) ⟨96224, by rfl⟩) R192449
theorem R62779 : Reach 62779 := rs (se 1 (by rfl) ⟨47084, by rfl⟩) R94169
theorem R62855 : Reach 62855 := rs (se 1 (by rfl) ⟨47141, by rfl⟩) R94283
theorem R62863 : Reach 62863 := rs (se 1 (by rfl) ⟨47147, by rfl⟩) R94295
theorem R62907 : Reach 62907 := rs (se 1 (by rfl) ⟨47180, by rfl⟩) R94361
theorem R62983 : Reach 62983 := rs (se 1 (by rfl) ⟨47237, by rfl⟩) R94475
theorem R62991 : Reach 62991 := rs (se 1 (by rfl) ⟨47243, by rfl⟩) R94487
theorem R128555 : Reach 128555 := rs (se 1 (by rfl) ⟨96416, by rfl⟩) R192833
theorem R63035 : Reach 63035 := rs (se 1 (by rfl) ⟨47276, by rfl⟩) R94553
theorem R95879 : Reach 95879 := rs (se 1 (by rfl) ⟨71909, by rfl⟩) R143819
theorem R63111 : Reach 63111 := rs (se 1 (by rfl) ⟨47333, by rfl⟩) R94667
theorem R63119 : Reach 63119 := rs (se 1 (by rfl) ⟨47339, by rfl⟩) R94679
theorem R227087 : Reach 227087 := rs (se 1 (by rfl) ⟨170315, by rfl⟩) R340631
theorem R325579 : Reach 325579 := rs (se 1 (by rfl) ⟨244184, by rfl⟩) R488369
theorem R423883 : Reach 423883 := rs (se 1 (by rfl) ⟨317912, by rfl⟩) R635825
theorem R227357 : Reach 227357 := rs (se 3 (by rfl) ⟨42629, by rfl⟩) R85259
theorem R292925 : Reach 292925 := rs (se 3 (by rfl) ⟨54923, by rfl⟩) R109847
theorem R63623 : Reach 63623 := rs (se 1 (by rfl) ⟨47717, by rfl⟩) R95435
theorem R391405 : Reach 391405 := rs (se 3 (by rfl) ⟨73388, by rfl⟩) R146777
theorem R227731 : Reach 227731 := rs (se 1 (by rfl) ⟨170798, by rfl⟩) R341597
theorem R129683 : Reach 129683 := rs (se 1 (by rfl) ⟨97262, by rfl⟩) R194525
theorem R228041 : Reach 228041 := rs (se 2 (by rfl) ⟨85515, by rfl⟩) R171031
theorem R293665 : Reach 293665 := rs (se 2 (by rfl) ⟨110124, by rfl⟩) R220249
theorem R261073 : Reach 261073 := rs (se 2 (by rfl) ⟨97902, by rfl⟩) R195805
theorem R228413 : Reach 228413 := rs (se 3 (by rfl) ⟨42827, by rfl⟩) R85655
theorem R130195 : Reach 130195 := rs (se 1 (by rfl) ⟨97646, by rfl⟩) R195293
theorem R425197 : Reach 425197 := rs (se 3 (by rfl) ⟨79724, by rfl⟩) R159449
theorem R163073 : Reach 163073 := rs (se 2 (by rfl) ⟨61152, by rfl⟩) R122305
theorem R490961 : Reach 490961 := rs (se 2 (by rfl) ⟨184110, by rfl⟩) R368221
theorem R327179 : Reach 327179 := rs (se 1 (by rfl) ⟨245384, by rfl⟩) R490769
theorem R294461 : Reach 294461 := rs (se 3 (by rfl) ⟨55211, by rfl⟩) R110423
theorem R589853 : Reach 589853 := rs (se 3 (by rfl) ⟨110597, by rfl⟩) R221195
theorem R196951 : Reach 196951 := rs (se 1 (by rfl) ⟨147713, by rfl⟩) R295427
theorem R98825 : Reach 98825 := rs (se 2 (by rfl) ⟨37059, by rfl⟩) R74119
theorem R229985 : Reach 229985 := rs (se 2 (by rfl) ⟨86244, by rfl⟩) R172489
theorem R66523 : Reach 66523 := rs (se 1 (by rfl) ⟨49892, by rfl⟩) R99785
theorem R590915 : Reach 590915 := rs (se 1 (by rfl) ⟨443186, by rfl⟩) R886373
theorem R132457 : Reach 132457 := rs (se 2 (by rfl) ⟨49671, by rfl⟩) R99343
theorem R66991 : Reach 66991 := rs (se 1 (by rfl) ⟨50243, by rfl⟩) R100487
theorem R394739 : Reach 394739 := rs (se 1 (by rfl) ⟨296054, by rfl⟩) R592109
theorem R230971 : Reach 230971 := rs (se 1 (by rfl) ⟨173228, by rfl⟩) R346457
theorem R165473 : Reach 165473 := rs (se 2 (by rfl) ⟨62052, by rfl⟩) R124105
theorem R67423 : Reach 67423 := rs (se 1 (by rfl) ⟨50567, by rfl⟩) R101135
theorem R231275 : Reach 231275 := rs (se 1 (by rfl) ⟨173456, by rfl⟩) R346913
theorem R100271 : Reach 100271 := rs (se 1 (by rfl) ⟨75203, by rfl⟩) R150407
theorem R133127 : Reach 133127 := rs (se 1 (by rfl) ⟨99845, by rfl⟩) R199691
theorem R854023 : Reach 854023 := rs (se 1 (by rfl) ⟨640517, by rfl⟩) R1281035
theorem R395279 : Reach 395279 := rs (se 1 (by rfl) ⟨296459, by rfl⟩) R592919
theorem R231443 : Reach 231443 := rs (se 1 (by rfl) ⟨173582, by rfl⟩) R347165
theorem R133199 : Reach 133199 := rs (se 1 (by rfl) ⟨99899, by rfl⟩) R199799
theorem R67783 : Reach 67783 := rs (se 1 (by rfl) ⟨50837, by rfl⟩) R101675
theorem R100703 : Reach 100703 := rs (se 1 (by rfl) ⟨75527, by rfl⟩) R151055
theorem R133595 : Reach 133595 := rs (se 1 (by rfl) ⟨100196, by rfl⟩) R200393
theorem R100921 : Reach 100921 := rs (se 2 (by rfl) ⟨37845, by rfl⟩) R75691
theorem R2558789 : Reach 2558789 := rs (se 4 (by rfl) ⟨239886, by rfl⟩) R479773
theorem R1084229 : Reach 1084229 := rs (se 4 (by rfl) ⟨101646, by rfl⟩) R203293
theorem R101263 : Reach 101263 := rs (se 1 (by rfl) ⟨75947, by rfl⟩) R151895
theorem R691091 : Reach 691091 := rs (se 1 (by rfl) ⟨518318, by rfl⟩) R1036637
theorem R134063 : Reach 134063 := rs (se 1 (by rfl) ⟨100547, by rfl⟩) R201095
theorem R429029 : Reach 429029 := rs (se 4 (by rfl) ⟨40221, by rfl⟩) R80443
theorem R330725 : Reach 330725 := rs (se 4 (by rfl) ⟨31005, by rfl⟩) R62011
theorem R68647 : Reach 68647 := rs (se 1 (by rfl) ⟨51485, by rfl⟩) R102971
theorem R265295 : Reach 265295 := rs (se 1 (by rfl) ⟨198971, by rfl⟩) R397943
theorem R134315 : Reach 134315 := rs (se 1 (by rfl) ⟨100736, by rfl⟩) R201473
theorem R200231 : Reach 200231 := rs (se 1 (by rfl) ⟨150173, by rfl⟩) R300347
theorem R396839 : Reach 396839 := rs (se 1 (by rfl) ⟨297629, by rfl⟩) R595259
theorem R101945 : Reach 101945 := rs (se 2 (by rfl) ⟨38229, by rfl⟩) R76459
theorem R200339 : Reach 200339 := rs (se 1 (by rfl) ⟨150254, by rfl⟩) R300509
theorem R134855 : Reach 134855 := rs (se 1 (by rfl) ⟨101141, by rfl⟩) R202283
theorem R200407 : Reach 200407 := rs (se 1 (by rfl) ⟨150305, by rfl⟩) R300611
theorem R200555 : Reach 200555 := rs (se 1 (by rfl) ⟨150416, by rfl⟩) R300833
theorem R200609 : Reach 200609 := rs (se 2 (by rfl) ⟨75228, by rfl⟩) R150457
theorem R102647 : Reach 102647 := rs (se 1 (by rfl) ⟨76985, by rfl⟩) R153971
theorem R201203 : Reach 201203 := rs (se 1 (by rfl) ⟨150902, by rfl⟩) R301805
theorem R135719 : Reach 135719 := rs (se 1 (by rfl) ⟨101789, by rfl⟩) R203579
theorem R102991 : Reach 102991 := rs (se 1 (by rfl) ⟨77243, by rfl⟩) R154487
theorem R1053283 : Reach 1053283 := rs (se 1 (by rfl) ⟨789962, by rfl⟩) R1579925
theorem R70267 : Reach 70267 := rs (se 1 (by rfl) ⟨52700, by rfl⟩) R105401
theorem R103241 : Reach 103241 := rs (se 2 (by rfl) ⟨38715, by rfl⟩) R77431
theorem R136043 : Reach 136043 := rs (se 1 (by rfl) ⟨102032, by rfl⟩) R204065
theorem R234359 : Reach 234359 := rs (se 1 (by rfl) ⟨175769, by rfl⟩) R351539
theorem R136097 : Reach 136097 := rs (se 2 (by rfl) ⟨51036, by rfl⟩) R102073
theorem R201743 : Reach 201743 := rs (se 1 (by rfl) ⟨151307, by rfl⟩) R302615
theorem R70735 : Reach 70735 := rs (se 1 (by rfl) ⟨53051, by rfl⟩) R106103
theorem R300185 : Reach 300185 := rs (se 2 (by rfl) ⟨112569, by rfl⟩) R225139
theorem R136439 : Reach 136439 := rs (se 1 (by rfl) ⟨102329, by rfl⟩) R204659
theorem R103673 : Reach 103673 := rs (se 2 (by rfl) ⟨38877, by rfl⟩) R77755
theorem R103855 : Reach 103855 := rs (se 1 (by rfl) ⟨77891, by rfl⟩) R155783
theorem R71131 : Reach 71131 := rs (se 1 (by rfl) ⟨53348, by rfl⟩) R106697
theorem R103943 : Reach 103943 := rs (se 1 (by rfl) ⟨77957, by rfl⟩) R155915
theorem R628235 : Reach 628235 := rs (se 1 (by rfl) ⟨471176, by rfl⟩) R942353
theorem R202337 : Reach 202337 := rs (se 2 (by rfl) ⟨75876, by rfl⟩) R151753
theorem R300667 : Reach 300667 := rs (se 1 (by rfl) ⟨225500, by rfl⟩) R451001
theorem R169661 : Reach 169661 := rs (se 3 (by rfl) ⟨31811, by rfl⟩) R63623
theorem R169721 : Reach 169721 := rs (se 2 (by rfl) ⟨63645, by rfl⟩) R127291
theorem R235331 : Reach 235331 := rs (se 1 (by rfl) ⟨176498, by rfl⟩) R352997
theorem R137033 : Reach 137033 := rs (se 2 (by rfl) ⟨51387, by rfl⟩) R102775
theorem R104287 : Reach 104287 := rs (se 1 (by rfl) ⟨78215, by rfl⟩) R156431
theorem R104375 : Reach 104375 := rs (se 1 (by rfl) ⟨78281, by rfl⟩) R156563
theorem R170063 : Reach 170063 := rs (se 1 (by rfl) ⟨127547, by rfl⟩) R255095
theorem R104969 : Reach 104969 := rs (se 2 (by rfl) ⟨39363, by rfl⟩) R78727
theorem R1874501 : Reach 1874501 := rs (se 4 (by rfl) ⟨175734, by rfl⟩) R351469
theorem R137825 : Reach 137825 := rs (se 2 (by rfl) ⟨51684, by rfl⟩) R103369
theorem R105131 : Reach 105131 := rs (se 1 (by rfl) ⟨78848, by rfl⟩) R157697
theorem R236317 : Reach 236317 := rs (se 3 (by rfl) ⟨44309, by rfl⟩) R88619
theorem R301897 : Reach 301897 := rs (se 2 (by rfl) ⟨113211, by rfl⟩) R226423
theorem R138167 : Reach 138167 := rs (se 1 (by rfl) ⟨103625, by rfl⟩) R207251
theorem R203795 : Reach 203795 := rs (se 1 (by rfl) ⟨152846, by rfl⟩) R305693
theorem R400403 : Reach 400403 := rs (se 1 (by rfl) ⟨300302, by rfl⟩) R600605
theorem R400427 : Reach 400427 := rs (se 1 (by rfl) ⟨300320, by rfl⟩) R600641
theorem R171065 : Reach 171065 := rs (se 2 (by rfl) ⟨64149, by rfl⟩) R128299
theorem R105529 : Reach 105529 := rs (se 2 (by rfl) ⟨39573, by rfl⟩) R79147
theorem R597071 : Reach 597071 := rs (se 1 (by rfl) ⟨447803, by rfl⟩) R895607
theorem R466073 : Reach 466073 := rs (se 2 (by rfl) ⟨174777, by rfl⟩) R349555
theorem R171179 : Reach 171179 := rs (se 1 (by rfl) ⟨128384, by rfl⟩) R256769
theorem R105671 : Reach 105671 := rs (se 1 (by rfl) ⟨79253, by rfl⟩) R158507
theorem R204119 : Reach 204119 := rs (se 1 (by rfl) ⟨153089, by rfl⟩) R306179
theorem R105833 : Reach 105833 := rs (se 2 (by rfl) ⟨39687, by rfl⟩) R79375
theorem R138761 : Reach 138761 := rs (se 2 (by rfl) ⟨52035, by rfl⟩) R104071
theorem R401041 : Reach 401041 := rs (se 2 (by rfl) ⟨150390, by rfl⟩) R300781
theorem R106183 : Reach 106183 := rs (se 1 (by rfl) ⟨79637, by rfl⟩) R159275
theorem R106231 : Reach 106231 := rs (se 1 (by rfl) ⟨79673, by rfl⟩) R159347
theorem R139103 : Reach 139103 := rs (se 1 (by rfl) ⟨104327, by rfl⟩) R208655
theorem R434105 : Reach 434105 := rs (se 2 (by rfl) ⟨162789, by rfl⟩) R325579
theorem R565177 : Reach 565177 := rs (se 2 (by rfl) ⟨211941, by rfl⟩) R423883
theorem R106427 : Reach 106427 := rs (se 1 (by rfl) ⟨79820, by rfl⟩) R159641
theorem R892943 : Reach 892943 := rs (se 1 (by rfl) ⟨669707, by rfl⟩) R1339415
theorem R139283 : Reach 139283 := rs (se 1 (by rfl) ⟨104462, by rfl⟩) R208925
theorem R106847 : Reach 106847 := rs (se 1 (by rfl) ⟨80135, by rfl⟩) R160271
theorem R139625 : Reach 139625 := rs (se 2 (by rfl) ⟨52359, by rfl⟩) R104719
theorem R205199 : Reach 205199 := rs (se 1 (by rfl) ⟨153899, by rfl⟩) R307799
theorem R303641 : Reach 303641 := rs (se 2 (by rfl) ⟨113865, by rfl⟩) R227731
theorem R205523 : Reach 205523 := rs (se 1 (by rfl) ⟨154142, by rfl⟩) R308285
theorem R467819 : Reach 467819 := rs (se 1 (by rfl) ⟨350864, by rfl⟩) R701729
theorem R140219 : Reach 140219 := rs (se 1 (by rfl) ⟨105164, by rfl⟩) R210329
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R468017 : Reach 468017 := rs (se 2 (by rfl) ⟨175506, by rfl⟩) R351013
theorem R140345 : Reach 140345 := rs (se 2 (by rfl) ⟨52629, by rfl⟩) R105259
theorem R140687 : Reach 140687 := rs (se 1 (by rfl) ⟨105515, by rfl⟩) R211031
theorem R173593 : Reach 173593 := rs (se 2 (by rfl) ⟨65097, by rfl⟩) R130195
theorem R140939 : Reach 140939 := rs (se 1 (by rfl) ⟨105704, by rfl⟩) R211409
theorem R566929 : Reach 566929 := rs (se 2 (by rfl) ⟨212598, by rfl⟩) R425197
theorem R141011 : Reach 141011 := rs (se 1 (by rfl) ⟨105758, by rfl⟩) R211517
theorem R206711 : Reach 206711 := rs (se 1 (by rfl) ⟨155033, by rfl⟩) R310067
theorem R206927 : Reach 206927 := rs (se 1 (by rfl) ⟨155195, by rfl⟩) R310391
theorem R108715 : Reach 108715 := rs (se 1 (by rfl) ⟨81536, by rfl⟩) R163073
theorem R207305 : Reach 207305 := rs (se 2 (by rfl) ⟨77739, by rfl⟩) R155479
theorem R141947 : Reach 141947 := rs (se 1 (by rfl) ⟨106460, by rfl⟩) R212921
theorem R240317 : Reach 240317 := rs (se 3 (by rfl) ⟨45059, by rfl⟩) R90119
theorem R207575 : Reach 207575 := rs (se 1 (by rfl) ⟨155681, by rfl⟩) R311363
theorem R1551251 : Reach 1551251 := rs (se 1 (by rfl) ⟨1163438, by rfl⟩) R2326877
theorem R207791 : Reach 207791 := rs (se 1 (by rfl) ⟨155843, by rfl⟩) R311687
theorem R76727 : Reach 76727 := rs (se 1 (by rfl) ⟨57545, by rfl⟩) R115091
theorem R76879 : Reach 76879 := rs (se 1 (by rfl) ⟨57659, by rfl⟩) R115319
theorem R110099 : Reach 110099 := rs (se 1 (by rfl) ⟨82574, by rfl⟩) R165149
theorem R896579 : Reach 896579 := rs (se 1 (by rfl) ⟨672434, by rfl⟩) R1344869
theorem R306827 : Reach 306827 := rs (se 1 (by rfl) ⟨230120, by rfl⟩) R460241
theorem R798497 : Reach 798497 := rs (se 2 (by rfl) ⟨299436, by rfl⟩) R598873
theorem R208975 : Reach 208975 := rs (se 1 (by rfl) ⟨156731, by rfl⟩) R313463
theorem R667763 : Reach 667763 := rs (se 1 (by rfl) ⟨500822, by rfl⟩) R1001645
theorem R78023 : Reach 78023 := rs (se 1 (by rfl) ⟨58517, by rfl⟩) R117035
theorem R78175 : Reach 78175 := rs (se 1 (by rfl) ⟨58631, by rfl⟩) R117263
theorem R176509 : Reach 176509 := rs (se 3 (by rfl) ⟨33095, by rfl⟩) R66191
theorem R176737 : Reach 176737 := rs (se 2 (by rfl) ⟨66276, by rfl⟩) R132553
theorem R242315 : Reach 242315 := rs (se 1 (by rfl) ⟨181736, by rfl⟩) R363473
theorem R1717037 : Reach 1717037 := rs (se 3 (by rfl) ⟨321944, by rfl⟩) R643889
theorem R111467 : Reach 111467 := rs (se 1 (by rfl) ⟨83600, by rfl⟩) R167201
theorem R177079 : Reach 177079 := rs (se 1 (by rfl) ⟨132809, by rfl⟩) R265619
theorem R210167 : Reach 210167 := rs (se 1 (by rfl) ⟨157625, by rfl⟩) R315251
theorem R276007 : Reach 276007 := rs (se 1 (by rfl) ⟨207005, by rfl⟩) R414011
theorem R210491 : Reach 210491 := rs (se 1 (by rfl) ⟨157868, by rfl⟩) R315737
theorem R210761 : Reach 210761 := rs (se 2 (by rfl) ⟨79035, by rfl⟩) R158071
theorem R178195 : Reach 178195 := rs (se 1 (by rfl) ⟨133646, by rfl⟩) R267293
theorem R211139 : Reach 211139 := rs (se 1 (by rfl) ⟨158354, by rfl⟩) R316709
theorem R112889 : Reach 112889 := rs (se 2 (by rfl) ⟨42333, by rfl⟩) R84667
theorem R571697 : Reach 571697 := rs (se 2 (by rfl) ⟨214386, by rfl⟩) R428773
theorem R178537 : Reach 178537 := rs (se 2 (by rfl) ⟨66951, by rfl⟩) R133903
theorem R244097 : Reach 244097 := rs (se 2 (by rfl) ⟨91536, by rfl⟩) R183073
theorem R113071 : Reach 113071 := rs (se 1 (by rfl) ⟨84803, by rfl⟩) R169607
theorem R113231 : Reach 113231 := rs (se 1 (by rfl) ⟨84923, by rfl⟩) R169847
theorem R178811 : Reach 178811 := rs (se 1 (by rfl) ⟨134108, by rfl⟩) R268217
theorem R211895 : Reach 211895 := rs (se 1 (by rfl) ⟨158921, by rfl⟩) R317843
theorem R212489 : Reach 212489 := rs (se 2 (by rfl) ⟨79683, by rfl⟩) R159367
theorem R114347 : Reach 114347 := rs (se 1 (by rfl) ⟨85760, by rfl⟩) R171521
theorem R802493 : Reach 802493 := rs (se 3 (by rfl) ⟨150467, by rfl⟩) R300935
theorem R376643 : Reach 376643 := rs (se 1 (by rfl) ⟨282482, by rfl⟩) R564965
theorem R311201 : Reach 311201 := rs (se 2 (by rfl) ⟨116700, by rfl⟩) R233401
theorem R344407 : Reach 344407 := rs (se 1 (by rfl) ⟨258305, by rfl⟩) R516611
theorem R443393 : Reach 443393 := rs (se 2 (by rfl) ⟨166272, by rfl⟩) R332545
theorem R476279 : Reach 476279 := rs (se 1 (by rfl) ⟨357209, by rfl⟩) R714419
theorem R116063 : Reach 116063 := rs (se 1 (by rfl) ⟨87047, by rfl⟩) R174095
theorem R214667 : Reach 214667 := rs (se 1 (by rfl) ⟨161000, by rfl⟩) R322001
theorem R247495 : Reach 247495 := rs (se 1 (by rfl) ⟨185621, by rfl⟩) R371243
theorem R116473 : Reach 116473 := rs (se 2 (by rfl) ⟨43677, by rfl⟩) R87355
theorem R673595 : Reach 673595 := rs (se 1 (by rfl) ⟨505196, by rfl⟩) R1010393
theorem R411601 : Reach 411601 := rs (se 2 (by rfl) ⟨154350, by rfl⟩) R308701
theorem R509905 : Reach 509905 := rs (se 2 (by rfl) ⟨191214, by rfl⟩) R382429
theorem R116815 : Reach 116815 := rs (se 1 (by rfl) ⟨87611, by rfl⟩) R175223
theorem R772253 : Reach 772253 := rs (se 3 (by rfl) ⟨144797, by rfl⟩) R289595
theorem R117065 : Reach 117065 := rs (se 2 (by rfl) ⟨43899, by rfl⟩) R87799
theorem R84331 : Reach 84331 := rs (se 1 (by rfl) ⟨63248, by rfl⟩) R126497
theorem R84559 : Reach 84559 := rs (se 1 (by rfl) ⟨63419, by rfl⟩) R126839
theorem R150113 : Reach 150113 := rs (se 2 (by rfl) ⟨56292, by rfl⟩) R112585
theorem R117931 : Reach 117931 := rs (se 1 (by rfl) ⟨88448, by rfl⟩) R176897
theorem R118007 : Reach 118007 := rs (se 1 (by rfl) ⟨88505, by rfl⟩) R177011
theorem R118235 : Reach 118235 := rs (se 1 (by rfl) ⟨88676, by rfl⟩) R177353
theorem R85703 : Reach 85703 := rs (se 1 (by rfl) ⟨64277, by rfl⟩) R128555
theorem R151391 : Reach 151391 := rs (se 1 (by rfl) ⟨113543, by rfl⟩) R227087
theorem R348097 : Reach 348097 := rs (se 2 (by rfl) ⟨130536, by rfl⟩) R261073
theorem R151571 : Reach 151571 := rs (se 1 (by rfl) ⟨113678, by rfl⟩) R227357
theorem R872477 : Reach 872477 := rs (se 3 (by rfl) ⟨163589, by rfl⟩) R327179
theorem R86455 : Reach 86455 := rs (se 1 (by rfl) ⟨64841, by rfl⟩) R129683
theorem R152027 : Reach 152027 := rs (se 1 (by rfl) ⟨114020, by rfl⟩) R228041
theorem R119495 : Reach 119495 := rs (se 1 (by rfl) ⟨89621, by rfl⟩) R179243
theorem R971473 : Reach 971473 := rs (se 2 (by rfl) ⟨364302, by rfl⟩) R728605
theorem R152275 : Reach 152275 := rs (se 1 (by rfl) ⟨114206, by rfl⟩) R228413
theorem R119647 : Reach 119647 := rs (se 1 (by rfl) ⟨89735, by rfl⟩) R179471
theorem R284077 : Reach 284077 := rs (se 3 (by rfl) ⟨53264, by rfl⟩) R106529
theorem R873929 : Reach 873929 := rs (se 2 (by rfl) ⟨327723, by rfl⟩) R655447
theorem R26891747 : Reach 26891747 := rs (se 1 (by rfl) ⟨20168810, by rfl⟩) R40337621
theorem R218611 : Reach 218611 := rs (se 1 (by rfl) ⟨163958, by rfl⟩) R327917
theorem R153211 : Reach 153211 := rs (se 1 (by rfl) ⟨114908, by rfl⟩) R229817
theorem R284305 : Reach 284305 := rs (se 2 (by rfl) ⟨106614, by rfl⟩) R213229
theorem R644755 : Reach 644755 := rs (se 1 (by rfl) ⟨483566, by rfl⟩) R967133
theorem R87913 : Reach 87913 := rs (se 2 (by rfl) ⟨32967, by rfl⟩) R65935
theorem R710693 : Reach 710693 := rs (se 4 (by rfl) ⟨66627, by rfl⟩) R133255
theorem R776249 : Reach 776249 := rs (se 2 (by rfl) ⟨291093, by rfl⟩) R582187
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R645677 : Reach 645677 := rs (se 3 (by rfl) ⟨121064, by rfl⟩) R242129
theorem R416441 : Reach 416441 := rs (se 2 (by rfl) ⟨156165, by rfl⟩) R312331
theorem R88775 : Reach 88775 := rs (se 1 (by rfl) ⟨66581, by rfl⟩) R133163
theorem R318163 : Reach 318163 := rs (se 1 (by rfl) ⟨238622, by rfl⟩) R477245
theorem R547661 : Reach 547661 := rs (se 3 (by rfl) ⟨102686, by rfl⟩) R205373
theorem R88937 : Reach 88937 := rs (se 2 (by rfl) ⟨33351, by rfl⟩) R66703
theorem R89015 : Reach 89015 := rs (se 1 (by rfl) ⟨66761, by rfl⟩) R133523
theorem R89051 : Reach 89051 := rs (se 1 (by rfl) ⟨66788, by rfl⟩) R133577
theorem R253007 : Reach 253007 := rs (se 1 (by rfl) ⟨189755, by rfl⟩) R379511
theorem R285943 : Reach 285943 := rs (se 1 (by rfl) ⟨214457, by rfl⟩) R428915
theorem R220427 : Reach 220427 := rs (se 1 (by rfl) ⟨165320, by rfl⟩) R330641
theorem R89519 : Reach 89519 := rs (se 1 (by rfl) ⟨67139, by rfl⟩) R134279
theorem R450035 : Reach 450035 := rs (se 1 (by rfl) ⟨337526, by rfl⟩) R675053
theorem R89609 : Reach 89609 := rs (se 2 (by rfl) ⟨33603, by rfl⟩) R67207
theorem R89639 : Reach 89639 := rs (se 1 (by rfl) ⟨67229, by rfl⟩) R134459
theorem R89723 : Reach 89723 := rs (se 1 (by rfl) ⟨67292, by rfl⟩) R134585
theorem R122539 : Reach 122539 := rs (se 1 (by rfl) ⟨91904, by rfl⟩) R183809
theorem R89849 : Reach 89849 := rs (se 2 (by rfl) ⟨33693, by rfl⟩) R67387
theorem R89951 : Reach 89951 := rs (se 1 (by rfl) ⟨67463, by rfl⟩) R134927
theorem R89963 : Reach 89963 := rs (se 1 (by rfl) ⟨67472, by rfl⟩) R134945
theorem R221089 : Reach 221089 := rs (se 2 (by rfl) ⟨82908, by rfl⟩) R165817
theorem R90191 : Reach 90191 := rs (se 1 (by rfl) ⟨67643, by rfl⟩) R135287
theorem R90311 : Reach 90311 := rs (se 1 (by rfl) ⟨67733, by rfl⟩) R135467
theorem R90463 : Reach 90463 := rs (se 1 (by rfl) ⟨67847, by rfl⟩) R135695
theorem R90473 : Reach 90473 := rs (se 2 (by rfl) ⟨33927, by rfl⟩) R67855
theorem R90551 : Reach 90551 := rs (se 1 (by rfl) ⟨67913, by rfl⟩) R135827
theorem R90587 : Reach 90587 := rs (se 1 (by rfl) ⟨67940, by rfl⟩) R135881
theorem R221831 : Reach 221831 := rs (se 1 (by rfl) ⟨166373, by rfl⟩) R332747
theorem R91055 : Reach 91055 := rs (se 1 (by rfl) ⟨68291, by rfl⟩) R136583
theorem R91145 : Reach 91145 := rs (se 2 (by rfl) ⟨34179, by rfl⟩) R68359
theorem R91175 : Reach 91175 := rs (se 1 (by rfl) ⟨68381, by rfl⟩) R136763
theorem R91259 : Reach 91259 := rs (se 1 (by rfl) ⟨68444, by rfl⟩) R136889
theorem R91385 : Reach 91385 := rs (se 2 (by rfl) ⟨34269, by rfl⟩) R68539
theorem R91487 : Reach 91487 := rs (se 1 (by rfl) ⟨68615, by rfl⟩) R137231
theorem R91499 : Reach 91499 := rs (se 1 (by rfl) ⟨68624, by rfl⟩) R137249
theorem R124267 : Reach 124267 := rs (se 1 (by rfl) ⟨93200, by rfl⟩) R186401
theorem R91727 : Reach 91727 := rs (se 1 (by rfl) ⟨68795, by rfl⟩) R137591
theorem R91847 : Reach 91847 := rs (se 1 (by rfl) ⟨68885, by rfl⟩) R137771
theorem R124615 : Reach 124615 := rs (se 1 (by rfl) ⟨93461, by rfl⟩) R186923
theorem R59175 : Reach 59175 := rs (se 1 (by rfl) ⟨44381, by rfl⟩) R88763
theorem R255811 : Reach 255811 := rs (se 1 (by rfl) ⟨191858, by rfl⟩) R383717
theorem R223049 : Reach 223049 := rs (se 2 (by rfl) ⟨83643, by rfl⟩) R167287
theorem R59215 : Reach 59215 := rs (se 1 (by rfl) ⟨44411, by rfl⟩) R88823
theorem R59231 : Reach 59231 := rs (se 1 (by rfl) ⟨44423, by rfl⟩) R88847
theorem R157535 : Reach 157535 := rs (se 1 (by rfl) ⟨118151, by rfl⟩) R236303
theorem R92009 : Reach 92009 := rs (se 2 (by rfl) ⟨34503, by rfl⟩) R69007
theorem R59259 : Reach 59259 := rs (se 1 (by rfl) ⟨44444, by rfl⟩) R88889
theorem R59311 : Reach 59311 := rs (se 1 (by rfl) ⟨44483, by rfl⟩) R88967
theorem R92087 : Reach 92087 := rs (se 1 (by rfl) ⟨69065, by rfl⟩) R138131
theorem R59335 : Reach 59335 := rs (se 1 (by rfl) ⟨44501, by rfl⟩) R89003
theorem R59355 : Reach 59355 := rs (se 1 (by rfl) ⟨44516, by rfl⟩) R89033
theorem R92123 : Reach 92123 := rs (se 1 (by rfl) ⟨69092, by rfl⟩) R138185
theorem R59431 : Reach 59431 := rs (se 1 (by rfl) ⟨44573, by rfl⟩) R89147
theorem R59471 : Reach 59471 := rs (se 1 (by rfl) ⟨44603, by rfl⟩) R89207
theorem R59487 : Reach 59487 := rs (se 1 (by rfl) ⟨44615, by rfl⟩) R89231
theorem R59515 : Reach 59515 := rs (se 1 (by rfl) ⟨44636, by rfl⟩) R89273
theorem R59567 : Reach 59567 := rs (se 1 (by rfl) ⟨44675, by rfl⟩) R89351
theorem R59591 : Reach 59591 := rs (se 1 (by rfl) ⟨44693, by rfl⟩) R89387
theorem R59611 : Reach 59611 := rs (se 1 (by rfl) ⟨44708, by rfl⟩) R89417
theorem R59687 : Reach 59687 := rs (se 1 (by rfl) ⟨44765, by rfl⟩) R89531
theorem R59727 : Reach 59727 := rs (se 1 (by rfl) ⟨44795, by rfl⟩) R89591
theorem R452951 : Reach 452951 := rs (se 1 (by rfl) ⟨339713, by rfl⟩) R679427
theorem R59743 : Reach 59743 := rs (se 1 (by rfl) ⟨44807, by rfl⟩) R89615
theorem R59771 : Reach 59771 := rs (se 1 (by rfl) ⟨44828, by rfl⟩) R89657
theorem R59823 : Reach 59823 := rs (se 1 (by rfl) ⟨44867, by rfl⟩) R89735
theorem R92591 : Reach 92591 := rs (se 1 (by rfl) ⟨69443, by rfl⟩) R138887
theorem R59847 : Reach 59847 := rs (se 1 (by rfl) ⟨44885, by rfl⟩) R89771
theorem R59867 : Reach 59867 := rs (se 1 (by rfl) ⟨44900, by rfl⟩) R89801
theorem R92681 : Reach 92681 := rs (se 2 (by rfl) ⟨34755, by rfl⟩) R69511
theorem R158233 : Reach 158233 := rs (se 2 (by rfl) ⟨59337, by rfl⟩) R118675
theorem R59943 : Reach 59943 := rs (se 1 (by rfl) ⟨44957, by rfl⟩) R89915
theorem R92711 : Reach 92711 := rs (se 1 (by rfl) ⟨69533, by rfl⟩) R139067
theorem R59983 : Reach 59983 := rs (se 1 (by rfl) ⟨44987, by rfl⟩) R89975
theorem R59999 : Reach 59999 := rs (se 1 (by rfl) ⟨44999, by rfl⟩) R89999
theorem R60027 : Reach 60027 := rs (se 1 (by rfl) ⟨45020, by rfl⟩) R90041
theorem R92795 : Reach 92795 := rs (se 1 (by rfl) ⟨69596, by rfl⟩) R139193
theorem R60079 : Reach 60079 := rs (se 1 (by rfl) ⟨45059, by rfl⟩) R90119
theorem R60103 : Reach 60103 := rs (se 1 (by rfl) ⟨45077, by rfl⟩) R90155
theorem R60123 : Reach 60123 := rs (se 1 (by rfl) ⟨45092, by rfl⟩) R90185
theorem R92921 : Reach 92921 := rs (se 2 (by rfl) ⟨34845, by rfl⟩) R69691
theorem R60199 : Reach 60199 := rs (se 1 (by rfl) ⟨45149, by rfl⟩) R90299
theorem R158537 : Reach 158537 := rs (se 2 (by rfl) ⟨59451, by rfl⟩) R118903
theorem R60239 : Reach 60239 := rs (se 1 (by rfl) ⟨45179, by rfl⟩) R90359
theorem R60255 : Reach 60255 := rs (se 1 (by rfl) ⟨45191, by rfl⟩) R90383
theorem R93023 : Reach 93023 := rs (se 1 (by rfl) ⟨69767, by rfl⟩) R139535
theorem R93035 : Reach 93035 := rs (se 1 (by rfl) ⟨69776, by rfl⟩) R139553
theorem R60283 : Reach 60283 := rs (se 1 (by rfl) ⟨45212, by rfl⟩) R90425
theorem R60335 : Reach 60335 := rs (se 1 (by rfl) ⟨45251, by rfl⟩) R90503
theorem R60359 : Reach 60359 := rs (se 1 (by rfl) ⟨45269, by rfl⟩) R90539
theorem R60379 : Reach 60379 := rs (se 1 (by rfl) ⟨45284, by rfl⟩) R90569
theorem R60455 : Reach 60455 := rs (se 1 (by rfl) ⟨45341, by rfl⟩) R90683
theorem R60495 : Reach 60495 := rs (se 1 (by rfl) ⟨45371, by rfl⟩) R90743
theorem R93263 : Reach 93263 := rs (se 1 (by rfl) ⟨69947, by rfl⟩) R139895
theorem R60511 : Reach 60511 := rs (se 1 (by rfl) ⟨45383, by rfl⟩) R90767
theorem R60539 : Reach 60539 := rs (se 1 (by rfl) ⟨45404, by rfl⟩) R90809
theorem R60591 : Reach 60591 := rs (se 1 (by rfl) ⟨45443, by rfl⟩) R90887
theorem R60615 : Reach 60615 := rs (se 1 (by rfl) ⟨45461, by rfl⟩) R90923
theorem R93383 : Reach 93383 := rs (se 1 (by rfl) ⟨70037, by rfl⟩) R140075
theorem R60635 : Reach 60635 := rs (se 1 (by rfl) ⟨45476, by rfl⟩) R90953
theorem R93431 : Reach 93431 := rs (se 1 (by rfl) ⟨70073, by rfl⟩) R140147
theorem R3665173 : Reach 3665173 := rs (se 6 (by rfl) ⟨85902, by rfl⟩) R171805
theorem R60711 : Reach 60711 := rs (se 1 (by rfl) ⟨45533, by rfl⟩) R91067
theorem R60751 : Reach 60751 := rs (se 1 (by rfl) ⟨45563, by rfl⟩) R91127
theorem R60767 : Reach 60767 := rs (se 1 (by rfl) ⟨45575, by rfl⟩) R91151
theorem R93545 : Reach 93545 := rs (se 2 (by rfl) ⟨35079, by rfl⟩) R70159
theorem R60795 : Reach 60795 := rs (se 1 (by rfl) ⟨45596, by rfl⟩) R91193
theorem R60847 : Reach 60847 := rs (se 1 (by rfl) ⟨45635, by rfl⟩) R91271
theorem R93623 : Reach 93623 := rs (se 1 (by rfl) ⟨70217, by rfl⟩) R140435
theorem R60871 : Reach 60871 := rs (se 1 (by rfl) ⟨45653, by rfl⟩) R91307
theorem R290249 : Reach 290249 := rs (se 2 (by rfl) ⟨108843, by rfl⟩) R217687
theorem R60891 : Reach 60891 := rs (se 1 (by rfl) ⟨45668, by rfl⟩) R91337
theorem R93659 : Reach 93659 := rs (se 1 (by rfl) ⟨70244, by rfl⟩) R140489
theorem R60967 : Reach 60967 := rs (se 1 (by rfl) ⟨45725, by rfl⟩) R91451
theorem R61007 : Reach 61007 := rs (se 1 (by rfl) ⟨45755, by rfl⟩) R91511
theorem R2289239 : Reach 2289239 := rs (se 1 (by rfl) ⟨1716929, by rfl⟩) R3433859
theorem R61023 : Reach 61023 := rs (se 1 (by rfl) ⟨45767, by rfl⟩) R91535
theorem R61051 : Reach 61051 := rs (se 1 (by rfl) ⟨45788, by rfl⟩) R91577
theorem R61103 : Reach 61103 := rs (se 1 (by rfl) ⟨45827, by rfl⟩) R91655
theorem R224957 : Reach 224957 := rs (se 3 (by rfl) ⟨42179, by rfl⟩) R84359
theorem R61127 : Reach 61127 := rs (se 1 (by rfl) ⟨45845, by rfl⟩) R91691
theorem R61147 : Reach 61147 := rs (se 1 (by rfl) ⟨45860, by rfl⟩) R91721
theorem R61223 : Reach 61223 := rs (se 1 (by rfl) ⟨45917, by rfl⟩) R91835
theorem R94025 : Reach 94025 := rs (se 2 (by rfl) ⟨35259, by rfl⟩) R70519
theorem R61263 : Reach 61263 := rs (se 1 (by rfl) ⟨45947, by rfl⟩) R91895
theorem R61279 : Reach 61279 := rs (se 1 (by rfl) ⟨45959, by rfl⟩) R91919
theorem R61307 : Reach 61307 := rs (se 1 (by rfl) ⟨45980, by rfl⟩) R91961
theorem R61359 : Reach 61359 := rs (se 1 (by rfl) ⟨46019, by rfl⟩) R92039
theorem R94127 : Reach 94127 := rs (se 1 (by rfl) ⟨70595, by rfl⟩) R141191
theorem R159671 : Reach 159671 := rs (se 1 (by rfl) ⟨119753, by rfl⟩) R239507
theorem R94139 : Reach 94139 := rs (se 1 (by rfl) ⟨70604, by rfl⟩) R141209
theorem R61383 : Reach 61383 := rs (se 1 (by rfl) ⟨46037, by rfl⟩) R92075
theorem R61403 : Reach 61403 := rs (se 1 (by rfl) ⟨46052, by rfl⟩) R92105
theorem R126983 : Reach 126983 := rs (se 1 (by rfl) ⟨95237, by rfl⟩) R190475
theorem R94217 : Reach 94217 := rs (se 2 (by rfl) ⟨35331, by rfl⟩) R70663
theorem R61479 : Reach 61479 := rs (se 1 (by rfl) ⟨46109, by rfl⟩) R92219
theorem R94247 : Reach 94247 := rs (se 1 (by rfl) ⟨70685, by rfl⟩) R141371
theorem R94265 : Reach 94265 := rs (se 2 (by rfl) ⟨35349, by rfl⟩) R70699
theorem R61519 : Reach 61519 := rs (se 1 (by rfl) ⟨46139, by rfl⟩) R92279
theorem R61535 : Reach 61535 := rs (se 1 (by rfl) ⟨46151, by rfl⟩) R92303
theorem R61563 : Reach 61563 := rs (se 1 (by rfl) ⟨46172, by rfl⟩) R92345
theorem R94331 : Reach 94331 := rs (se 1 (by rfl) ⟨70748, by rfl⟩) R141497
theorem R94379 : Reach 94379 := rs (se 1 (by rfl) ⟨70784, by rfl⟩) R141569
theorem R61615 : Reach 61615 := rs (se 1 (by rfl) ⟨46211, by rfl⟩) R92423
theorem R61639 : Reach 61639 := rs (se 1 (by rfl) ⟨46229, by rfl⟩) R92459
theorem R61659 : Reach 61659 := rs (se 1 (by rfl) ⟨46244, by rfl⟩) R92489
theorem R94457 : Reach 94457 := rs (se 2 (by rfl) ⟨35421, by rfl⟩) R70843
theorem R61735 : Reach 61735 := rs (se 1 (by rfl) ⟨46301, by rfl⟩) R92603
theorem R61775 : Reach 61775 := rs (se 1 (by rfl) ⟨46331, by rfl⟩) R92663
theorem R61791 : Reach 61791 := rs (se 1 (by rfl) ⟨46343, by rfl⟩) R92687
theorem R94559 : Reach 94559 := rs (se 1 (by rfl) ⟨70919, by rfl⟩) R141839
theorem R94571 : Reach 94571 := rs (se 1 (by rfl) ⟨70928, by rfl⟩) R141857
theorem R61819 : Reach 61819 := rs (se 1 (by rfl) ⟨46364, by rfl⟩) R92729
theorem R94607 : Reach 94607 := rs (se 1 (by rfl) ⟨70955, by rfl⟩) R141911
theorem R61871 : Reach 61871 := rs (se 1 (by rfl) ⟨46403, by rfl⟩) R92807
theorem R61895 : Reach 61895 := rs (se 1 (by rfl) ⟨46421, by rfl⟩) R92843
theorem R61915 : Reach 61915 := rs (se 1 (by rfl) ⟨46436, by rfl⟩) R92873
theorem R356845 : Reach 356845 := rs (se 3 (by rfl) ⟨66908, by rfl⟩) R133817
theorem R717335 : Reach 717335 := rs (se 1 (by rfl) ⟨538001, by rfl⟩) R1076003
theorem R61991 : Reach 61991 := rs (se 1 (by rfl) ⟨46493, by rfl⟩) R92987
theorem R62031 : Reach 62031 := rs (se 1 (by rfl) ⟨46523, by rfl⟩) R93047
theorem R62047 : Reach 62047 := rs (se 1 (by rfl) ⟨46535, by rfl⟩) R93071
theorem R62075 : Reach 62075 := rs (se 1 (by rfl) ⟨46556, by rfl⟩) R93113
theorem R62127 : Reach 62127 := rs (se 1 (by rfl) ⟨46595, by rfl⟩) R93191
theorem R62151 : Reach 62151 := rs (se 1 (by rfl) ⟨46613, by rfl⟩) R93227
theorem R291539 : Reach 291539 := rs (se 1 (by rfl) ⟨218654, by rfl⟩) R437309
theorem R62171 : Reach 62171 := rs (se 1 (by rfl) ⟨46628, by rfl⟩) R93257
theorem R881425 : Reach 881425 := rs (se 2 (by rfl) ⟨330534, by rfl⟩) R661069
theorem R62247 : Reach 62247 := rs (se 1 (by rfl) ⟨46685, by rfl⟩) R93371
theorem R62303 : Reach 62303 := rs (se 1 (by rfl) ⟨46727, by rfl⟩) R93455
theorem R291691 : Reach 291691 := rs (se 1 (by rfl) ⟨218768, by rfl⟩) R437537
theorem R62383 : Reach 62383 := rs (se 1 (by rfl) ⟨46787, by rfl⟩) R93575
theorem R226223 : Reach 226223 := rs (se 1 (by rfl) ⟨169667, by rfl⟩) R339335
theorem R62427 : Reach 62427 := rs (se 1 (by rfl) ⟨46820, by rfl⟩) R93641
theorem R1635329 : Reach 1635329 := rs (se 2 (by rfl) ⟨613248, by rfl⟩) R1226497
theorem R62503 : Reach 62503 := rs (se 1 (by rfl) ⟨46877, by rfl⟩) R93755
theorem R62543 : Reach 62543 := rs (se 1 (by rfl) ⟨46907, by rfl⟩) R93815
theorem R226385 : Reach 226385 := rs (se 2 (by rfl) ⟨84894, by rfl⟩) R169789
theorem R62587 : Reach 62587 := rs (se 1 (by rfl) ⟨46940, by rfl⟩) R93881
theorem R62663 : Reach 62663 := rs (se 1 (by rfl) ⟨46997, by rfl⟩) R93995
theorem R685259 : Reach 685259 := rs (se 1 (by rfl) ⟨513944, by rfl⟩) R1027889
theorem R62815 : Reach 62815 := rs (se 1 (by rfl) ⟨47111, by rfl⟩) R94223
theorem R980369 : Reach 980369 := rs (se 2 (by rfl) ⟨367638, by rfl⟩) R735277
theorem R62895 : Reach 62895 := rs (se 1 (by rfl) ⟨47171, by rfl⟩) R94343
theorem R62939 : Reach 62939 := rs (se 1 (by rfl) ⟨47204, by rfl⟩) R94409
theorem R63015 : Reach 63015 := rs (se 1 (by rfl) ⟨47261, by rfl⟩) R94523
theorem R95801 : Reach 95801 := rs (se 2 (by rfl) ⟨35925, by rfl⟩) R71851
theorem R63055 : Reach 63055 := rs (se 1 (by rfl) ⟨47291, by rfl⟩) R94583
theorem R63099 : Reach 63099 := rs (se 1 (by rfl) ⟨47324, by rfl⟩) R94649
theorem R521873 : Reach 521873 := rs (se 2 (by rfl) ⟨195702, by rfl⟩) R391405
theorem R358187 : Reach 358187 := rs (se 1 (by rfl) ⟨268640, by rfl⟩) R537281
theorem R194575 : Reach 194575 := rs (se 1 (by rfl) ⟨145931, by rfl⟩) R291863
theorem R391553 : Reach 391553 := rs (se 2 (by rfl) ⟨146832, by rfl⟩) R293665
theorem R63919 : Reach 63919 := rs (se 1 (by rfl) ⟨47939, by rfl⟩) R95879
theorem R227873 : Reach 227873 := rs (se 2 (by rfl) ⟨85452, by rfl⟩) R170905
theorem R1309229 : Reach 1309229 := rs (se 3 (by rfl) ⟨245480, by rfl⟩) R490961
theorem R162443 : Reach 162443 := rs (se 1 (by rfl) ⟨121832, by rfl⟩) R243665
theorem R195283 : Reach 195283 := rs (se 1 (by rfl) ⟨146462, by rfl⟩) R292925
theorem R228055 : Reach 228055 := rs (se 1 (by rfl) ⟨171041, by rfl⟩) R342083
theorem R1276901 : Reach 1276901 := rs (se 4 (by rfl) ⟨119709, by rfl⟩) R239419
theorem R228359 : Reach 228359 := rs (se 1 (by rfl) ⟨171269, by rfl⟩) R342539
theorem R293939 : Reach 293939 := rs (se 1 (by rfl) ⟨220454, by rfl⟩) R440909
theorem R228845 : Reach 228845 := rs (se 3 (by rfl) ⟨42908, by rfl⟩) R85817
theorem R556583 : Reach 556583 := rs (se 1 (by rfl) ⟨417437, by rfl⟩) R834875
theorem R196307 : Reach 196307 := rs (se 1 (by rfl) ⟨147230, by rfl⟩) R294461
theorem R1572941 : Reach 1572941 := rs (se 3 (by rfl) ⟨294926, by rfl⟩) R589853
theorem R262601 : Reach 262601 := rs (se 2 (by rfl) ⟨98475, by rfl⟩) R196951
theorem R459209 : Reach 459209 := rs (se 2 (by rfl) ⟨172203, by rfl⟩) R344407
theorem R295595 : Reach 295595 := rs (se 1 (by rfl) ⟨221696, by rfl⟩) R443393
theorem R393943 : Reach 393943 := rs (se 1 (by rfl) ⟨295457, by rfl⟩) R590915
theorem R263159 : Reach 263159 := rs (se 1 (by rfl) ⟨197369, by rfl⟩) R394739
theorem R66847 : Reach 66847 := rs (se 1 (by rfl) ⟨50135, by rfl⟩) R100271
theorem R263519 : Reach 263519 := rs (se 1 (by rfl) ⟨197639, by rfl⟩) R395279
theorem R67135 : Reach 67135 := rs (se 1 (by rfl) ⟨50351, by rfl⟩) R100703
theorem R100075 : Reach 100075 := rs (se 1 (by rfl) ⟨75056, by rfl⟩) R150113
theorem R165689 : Reach 165689 := rs (se 2 (by rfl) ⟨62133, by rfl⟩) R124267
theorem R1705859 : Reach 1705859 := rs (se 1 (by rfl) ⟨1279394, by rfl⟩) R2558789
theorem R722819 : Reach 722819 := rs (se 1 (by rfl) ⟨542114, by rfl⟩) R1084229
theorem R460727 : Reach 460727 := rs (se 1 (by rfl) ⟨345545, by rfl⟩) R691091
theorem R231457 : Reach 231457 := rs (se 2 (by rfl) ⟨86796, by rfl⟩) R173593
theorem R755905 : Reach 755905 := rs (se 2 (by rfl) ⟨283464, by rfl⟩) R566929
theorem R329993 : Reach 329993 := rs (se 2 (by rfl) ⟨123747, by rfl⟩) R247495
theorem R166153 : Reach 166153 := rs (se 2 (by rfl) ⟨62307, by rfl⟩) R124615
theorem R297245 : Reach 297245 := rs (se 3 (by rfl) ⟨55733, by rfl⟩) R111467
theorem R133487 : Reach 133487 := rs (se 1 (by rfl) ⟨100115, by rfl⟩) R200231
theorem R264559 : Reach 264559 := rs (se 1 (by rfl) ⟨198419, by rfl⟩) R396839
theorem R67963 : Reach 67963 := rs (se 1 (by rfl) ⟨50972, by rfl⟩) R101945
theorem R133559 : Reach 133559 := rs (se 1 (by rfl) ⟨100169, by rfl⟩) R200339
theorem R2296349 : Reach 2296349 := rs (se 3 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R100927 : Reach 100927 := rs (se 1 (by rfl) ⟨75695, by rfl⟩) R151391
theorem R133703 : Reach 133703 := rs (se 1 (by rfl) ⟨100277, by rfl⟩) R200555
theorem R133739 : Reach 133739 := rs (se 1 (by rfl) ⟨100304, by rfl⟩) R200609
theorem R101047 : Reach 101047 := rs (se 1 (by rfl) ⟨75785, by rfl⟩) R151571
theorem R68431 : Reach 68431 := rs (se 1 (by rfl) ⟨51323, by rfl⟩) R102647
theorem R101351 : Reach 101351 := rs (se 1 (by rfl) ⟨76013, by rfl⟩) R152027
theorem R134135 : Reach 134135 := rs (se 1 (by rfl) ⟨100601, by rfl⟩) R201203
theorem R68827 : Reach 68827 := rs (se 1 (by rfl) ⟨51620, by rfl⟩) R103241
theorem R134495 : Reach 134495 := rs (se 1 (by rfl) ⟨100871, by rfl⟩) R201743
theorem R134561 : Reach 134561 := rs (se 2 (by rfl) ⟨50460, by rfl⟩) R100921
theorem R200123 : Reach 200123 := rs (se 1 (by rfl) ⟨150092, by rfl⟩) R300185
theorem R69115 : Reach 69115 := rs (se 1 (by rfl) ⟨51836, by rfl⟩) R103673
theorem R17927831 : Reach 17927831 := rs (se 1 (by rfl) ⟨13445873, by rfl⟩) R26891747
theorem R69295 : Reach 69295 := rs (se 1 (by rfl) ⟨51971, by rfl⟩) R103943
theorem R134891 : Reach 134891 := rs (se 1 (by rfl) ⟨101168, by rfl⟩) R202337
theorem R135017 : Reach 135017 := rs (se 2 (by rfl) ⟨50631, by rfl⟩) R101263
theorem R2330477 : Reach 2330477 := rs (se 3 (by rfl) ⟨436964, by rfl⟩) R873929
theorem R69583 : Reach 69583 := rs (se 1 (by rfl) ⟨52187, by rfl⟩) R104375
theorem R102505 : Reach 102505 := rs (se 2 (by rfl) ⟨38439, by rfl⟩) R76879
theorem R69979 : Reach 69979 := rs (se 1 (by rfl) ⟨52484, by rfl⟩) R104969
theorem R4886897 : Reach 4886897 := rs (se 2 (by rfl) ⟨1832586, by rfl⟩) R3665173
theorem R430451 : Reach 430451 := rs (se 1 (by rfl) ⟨322838, by rfl⟩) R645677
theorem R1249667 : Reach 1249667 := rs (se 1 (by rfl) ⟨937250, by rfl⟩) R1874501
theorem R70087 : Reach 70087 := rs (se 1 (by rfl) ⟨52565, by rfl⟩) R105131
theorem R135863 : Reach 135863 := rs (se 1 (by rfl) ⟨101897, by rfl⟩) R203795
theorem R266935 : Reach 266935 := rs (se 1 (by rfl) ⟨200201, by rfl⟩) R400403
theorem R266951 : Reach 266951 := rs (se 1 (by rfl) ⟨200213, by rfl⟩) R400427
theorem R398047 : Reach 398047 := rs (se 1 (by rfl) ⟨298535, by rfl⟩) R597071
theorem R168671 : Reach 168671 := rs (se 1 (by rfl) ⟨126503, by rfl⟩) R253007
theorem R955165 : Reach 955165 := rs (se 3 (by rfl) ⟨179093, by rfl⟩) R358187
theorem R70447 : Reach 70447 := rs (se 1 (by rfl) ⟨52835, by rfl⟩) R105671
theorem R136079 : Reach 136079 := rs (se 1 (by rfl) ⟨102059, by rfl⟩) R204119
theorem R70555 : Reach 70555 := rs (se 1 (by rfl) ⟨52916, by rfl⟩) R105833
theorem R267209 : Reach 267209 := rs (se 2 (by rfl) ⟨100203, by rfl⟩) R200407
theorem R300023 : Reach 300023 := rs (se 1 (by rfl) ⟨225017, by rfl⟩) R450035
theorem R464129 : Reach 464129 := rs (se 2 (by rfl) ⟨174048, by rfl⟩) R348097
theorem R70951 : Reach 70951 := rs (se 1 (by rfl) ⟨53213, by rfl⟩) R106427
theorem R595295 : Reach 595295 := rs (se 1 (by rfl) ⟨446471, by rfl⟩) R892943
theorem R1054133 : Reach 1054133 := rs (se 5 (by rfl) ⟨49412, by rfl⟩) R98825
theorem R71231 : Reach 71231 := rs (se 1 (by rfl) ⟨53423, by rfl⟩) R106847
theorem R136799 : Reach 136799 := rs (se 1 (by rfl) ⟨102599, by rfl⟩) R205199
theorem R202427 : Reach 202427 := rs (se 1 (by rfl) ⟨151820, by rfl⟩) R303641
theorem R5936885 : Reach 5936885 := rs (se 5 (by rfl) ⟨278291, by rfl⟩) R556583
theorem R104233 : Reach 104233 := rs (se 2 (by rfl) ⟨39087, by rfl⟩) R78175
theorem R137015 : Reach 137015 := rs (se 1 (by rfl) ⟨102761, by rfl⟩) R205523
theorem R235345 : Reach 235345 := rs (se 2 (by rfl) ⟨88254, by rfl⟩) R176509
theorem R137321 : Reach 137321 := rs (se 2 (by rfl) ⟨51495, by rfl⟩) R102991
theorem R235649 : Reach 235649 := rs (se 2 (by rfl) ⟨88368, by rfl⟩) R176737
theorem R203033 : Reach 203033 := rs (se 2 (by rfl) ⟨76137, by rfl⟩) R152275
theorem R105023 : Reach 105023 := rs (se 1 (by rfl) ⟨78767, by rfl⟩) R157535
theorem R236105 : Reach 236105 := rs (se 2 (by rfl) ⟨88539, by rfl⟩) R177079
theorem R137807 : Reach 137807 := rs (se 1 (by rfl) ⟨103355, by rfl⟩) R206711
theorem R137951 : Reach 137951 := rs (se 1 (by rfl) ⟨103463, by rfl⟩) R206927
theorem R301967 : Reach 301967 := rs (se 1 (by rfl) ⟨226475, by rfl⟩) R452951
theorem R138203 : Reach 138203 := rs (se 1 (by rfl) ⟨103652, by rfl⟩) R207305
theorem R433181 : Reach 433181 := rs (se 3 (by rfl) ⟨81221, by rfl⟩) R162443
theorem R138383 : Reach 138383 := rs (se 1 (by rfl) ⟨103787, by rfl⟩) R207575
theorem R105691 : Reach 105691 := rs (se 1 (by rfl) ⟨79268, by rfl⟩) R158537
theorem R138473 : Reach 138473 := rs (se 2 (by rfl) ⟨51927, by rfl⟩) R103855
theorem R138527 : Reach 138527 := rs (se 1 (by rfl) ⟨103895, by rfl⟩) R207791
theorem R368009 : Reach 368009 := rs (se 2 (by rfl) ⟨138003, by rfl⟩) R276007
theorem R204281 : Reach 204281 := rs (se 2 (by rfl) ⟨76605, by rfl⟩) R153211
theorem R400889 : Reach 400889 := rs (se 2 (by rfl) ⟨150333, by rfl⟩) R300667
theorem R859673 : Reach 859673 := rs (se 2 (by rfl) ⟨322377, by rfl⟩) R644755
theorem R73399 : Reach 73399 := rs (se 1 (by rfl) ⟨55049, by rfl⟩) R110099
theorem R597719 : Reach 597719 := rs (se 1 (by rfl) ⟨448289, by rfl⟩) R896579
theorem R204551 : Reach 204551 := rs (se 1 (by rfl) ⟨153413, by rfl⟩) R306827
theorem R139049 : Reach 139049 := rs (se 2 (by rfl) ⟨52143, by rfl⟩) R104287
theorem R204605 : Reach 204605 := rs (se 3 (by rfl) ⟨38363, by rfl⟩) R76727
theorem R532331 : Reach 532331 := rs (se 1 (by rfl) ⟨399248, by rfl⟩) R798497
theorem R106447 : Reach 106447 := rs (se 1 (by rfl) ⟨79835, by rfl⟩) R159671
theorem R237593 : Reach 237593 := rs (se 2 (by rfl) ⟨89097, by rfl⟩) R178195
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R238049 : Reach 238049 := rs (se 2 (by rfl) ⟨89268, by rfl⟩) R178537
theorem R1090219 : Reach 1090219 := rs (se 1 (by rfl) ⟨817664, by rfl⟩) R1635329
theorem R140111 : Reach 140111 := rs (se 1 (by rfl) ⟨105083, by rfl⟩) R210167
theorem R304073 : Reach 304073 := rs (se 2 (by rfl) ⟨114027, by rfl⟩) R228055
theorem R140327 : Reach 140327 := rs (se 1 (by rfl) ⟨105245, by rfl⟩) R210491
theorem R402529 : Reach 402529 := rs (se 2 (by rfl) ⟨150948, by rfl⟩) R301897
theorem R140507 : Reach 140507 := rs (se 1 (by rfl) ⟨105380, by rfl⟩) R210761
theorem R140705 : Reach 140705 := rs (se 2 (by rfl) ⟨52764, by rfl⟩) R105529
theorem R140759 : Reach 140759 := rs (se 1 (by rfl) ⟨105569, by rfl⟩) R211139
theorem R75259 : Reach 75259 := rs (se 1 (by rfl) ⟨56444, by rfl⟩) R112889
theorem R75487 : Reach 75487 := rs (se 1 (by rfl) ⟨56615, by rfl⟩) R113231
theorem R141263 : Reach 141263 := rs (se 1 (by rfl) ⟨105947, by rfl⟩) R211895
theorem R534721 : Reach 534721 := rs (se 2 (by rfl) ⟨200520, by rfl⟩) R401041
theorem R141577 : Reach 141577 := rs (se 2 (by rfl) ⟨53091, by rfl⟩) R106183
theorem R141641 : Reach 141641 := rs (se 2 (by rfl) ⟨53115, by rfl⟩) R106231
theorem R141659 : Reach 141659 := rs (se 1 (by rfl) ⟨106244, by rfl⟩) R212489
theorem R76231 : Reach 76231 := rs (se 1 (by rfl) ⟨57173, by rfl⟩) R114347
theorem R534995 : Reach 534995 := rs (se 1 (by rfl) ⟨401246, by rfl⟩) R802493
theorem R207467 : Reach 207467 := rs (se 1 (by rfl) ⟨155600, by rfl⟩) R311201
theorem R208061 : Reach 208061 := rs (se 3 (by rfl) ⟨39011, by rfl⟩) R78023
theorem R77375 : Reach 77375 := rs (se 1 (by rfl) ⟨58031, by rfl⟩) R116063
theorem R110315 : Reach 110315 := rs (se 1 (by rfl) ⟨82736, by rfl⟩) R165473
theorem R143111 : Reach 143111 := rs (se 1 (by rfl) ⟨107333, by rfl⟩) R214667
theorem R176609 : Reach 176609 := rs (se 2 (by rfl) ⟨66228, by rfl⟩) R132457
theorem R176863 : Reach 176863 := rs (se 1 (by rfl) ⟨132647, by rfl⟩) R265295
theorem R307961 : Reach 307961 := rs (se 2 (by rfl) ⟨115485, by rfl⟩) R230971
theorem R78671 : Reach 78671 := rs (se 1 (by rfl) ⟨59003, by rfl⟩) R118007
theorem R78823 : Reach 78823 := rs (se 1 (by rfl) ⟨59117, by rfl⟩) R118235
theorem R341081 : Reach 341081 := rs (se 2 (by rfl) ⟨127905, by rfl⟩) R255811
theorem R144953 : Reach 144953 := rs (se 2 (by rfl) ⟨54357, by rfl⟩) R108715
theorem R79481 : Reach 79481 := rs (se 2 (by rfl) ⟨29805, by rfl⟩) R59611
theorem R112441 : Reach 112441 := rs (se 2 (by rfl) ⟨42165, by rfl⟩) R84331
theorem R210977 : Reach 210977 := rs (se 2 (by rfl) ⟨79116, by rfl⟩) R158233
theorem R112745 : Reach 112745 := rs (se 2 (by rfl) ⟨42279, by rfl⟩) R84559
theorem R113147 : Reach 113147 := rs (se 1 (by rfl) ⟨84860, by rfl⟩) R169721
theorem R473795 : Reach 473795 := rs (se 1 (by rfl) ⟨355346, by rfl⟩) R710693
theorem R113375 : Reach 113375 := rs (se 1 (by rfl) ⟨85031, by rfl⟩) R170063
theorem R277627 : Reach 277627 := rs (se 1 (by rfl) ⟨208220, by rfl⟩) R416441
theorem R114043 : Reach 114043 := rs (se 1 (by rfl) ⟨85532, by rfl⟩) R171065
theorem R310715 : Reach 310715 := rs (se 1 (by rfl) ⟨233036, by rfl⟩) R466073
theorem R114119 : Reach 114119 := rs (se 1 (by rfl) ⟨85589, by rfl⟩) R171179
theorem R146951 : Reach 146951 := rs (se 1 (by rfl) ⟨110213, by rfl⟩) R220427
theorem R278633 : Reach 278633 := rs (se 2 (by rfl) ⟨104487, by rfl⟩) R208975
theorem R147887 : Reach 147887 := rs (se 1 (by rfl) ⟨110915, by rfl⟩) R221831
theorem R311879 : Reach 311879 := rs (se 1 (by rfl) ⟨233909, by rfl⟩) R467819
theorem R115273 : Reach 115273 := rs (se 2 (by rfl) ⟨43227, by rfl⟩) R86455
theorem R475793 : Reach 475793 := rs (se 2 (by rfl) ⟨178422, by rfl⟩) R356845
theorem R312011 : Reach 312011 := rs (se 1 (by rfl) ⟨234008, by rfl⟩) R468017
theorem R312173 : Reach 312173 := rs (se 3 (by rfl) ⟨58532, by rfl⟩) R117065
theorem R1295297 : Reach 1295297 := rs (se 2 (by rfl) ⟨485736, by rfl⟩) R971473
theorem R148699 : Reach 148699 := rs (se 1 (by rfl) ⟨111524, by rfl⟩) R223049
theorem R378769 : Reach 378769 := rs (se 2 (by rfl) ⟨142038, by rfl⟩) R284077
theorem R1034167 : Reach 1034167 := rs (se 1 (by rfl) ⟨775625, by rfl⟩) R1551251
theorem R379073 : Reach 379073 := rs (se 2 (by rfl) ⟨142152, by rfl⟩) R284305
theorem R1460429 : Reach 1460429 := rs (se 3 (by rfl) ⟨273830, by rfl⟩) R547661
theorem R1526159 : Reach 1526159 := rs (se 1 (by rfl) ⟨1144619, by rfl⟩) R2289239
theorem R149971 : Reach 149971 := rs (se 1 (by rfl) ⟨112478, by rfl⟩) R224957
theorem R117217 : Reach 117217 := rs (se 2 (by rfl) ⟨43956, by rfl⟩) R87913
theorem R84655 : Reach 84655 := rs (se 1 (by rfl) ⟨63491, by rfl⟩) R126983
theorem R445175 : Reach 445175 := rs (se 1 (by rfl) ⟨333881, by rfl⟩) R667763
theorem R478223 : Reach 478223 := rs (se 1 (by rfl) ⟨358667, by rfl⟩) R717335
theorem R150761 : Reach 150761 := rs (se 2 (by rfl) ⟨56535, by rfl⟩) R113071
theorem R85225 : Reach 85225 := rs (se 2 (by rfl) ⟨31959, by rfl⟩) R63919
theorem R150815 : Reach 150815 := rs (se 1 (by rfl) ⟨113111, by rfl⟩) R226223
theorem R150923 : Reach 150923 := rs (se 1 (by rfl) ⟨113192, by rfl⟩) R226385
theorem R315089 : Reach 315089 := rs (se 2 (by rfl) ⟨118158, by rfl⟩) R236317
theorem R347915 : Reach 347915 := rs (se 1 (by rfl) ⟨260936, by rfl⟩) R521873
theorem R381131 : Reach 381131 := rs (se 1 (by rfl) ⟨285848, by rfl⟩) R571697
theorem R381257 : Reach 381257 := rs (se 2 (by rfl) ⟨142971, by rfl⟩) R285943
theorem R151915 : Reach 151915 := rs (se 1 (by rfl) ⟨113936, by rfl⟩) R227873
theorem R872819 : Reach 872819 := rs (se 1 (by rfl) ⟨654614, by rfl⟩) R1309229
theorem R119207 : Reach 119207 := rs (se 1 (by rfl) ⟨89405, by rfl⟩) R178811
theorem R152239 : Reach 152239 := rs (se 1 (by rfl) ⟨114179, by rfl⟩) R228359
theorem R152563 : Reach 152563 := rs (se 1 (by rfl) ⟨114422, by rfl⟩) R228845
theorem R251095 : Reach 251095 := rs (se 1 (by rfl) ⟨188321, by rfl⟩) R376643
theorem R153323 : Reach 153323 := rs (se 1 (by rfl) ⟨114992, by rfl⟩) R229985
theorem R120617 : Reach 120617 := rs (se 2 (by rfl) ⟨45231, by rfl⟩) R90463
theorem R317519 : Reach 317519 := rs (se 1 (by rfl) ⟨238139, by rfl⟩) R476279
theorem R449063 : Reach 449063 := rs (se 1 (by rfl) ⟨336797, by rfl⟩) R673595
theorem R154183 : Reach 154183 := rs (se 1 (by rfl) ⟨115637, by rfl⟩) R231275
theorem R88697 : Reach 88697 := rs (se 2 (by rfl) ⟨33261, by rfl⟩) R66523
theorem R88751 : Reach 88751 := rs (se 1 (by rfl) ⟨66563, by rfl⟩) R133127
theorem R154295 : Reach 154295 := rs (se 1 (by rfl) ⟨115721, by rfl⟩) R231443
theorem R88799 : Reach 88799 := rs (se 1 (by rfl) ⟨66599, by rfl⟩) R133199
theorem R514835 : Reach 514835 := rs (se 1 (by rfl) ⟨386126, by rfl⟩) R772253
theorem R89063 : Reach 89063 := rs (se 1 (by rfl) ⟨66797, by rfl⟩) R133595
theorem R318653 : Reach 318653 := rs (se 3 (by rfl) ⟨59747, by rfl⟩) R119495
theorem R89321 : Reach 89321 := rs (se 2 (by rfl) ⟨33495, by rfl⟩) R66991
theorem R89375 : Reach 89375 := rs (se 1 (by rfl) ⟨67031, by rfl⟩) R134063
theorem R286019 : Reach 286019 := rs (se 1 (by rfl) ⟨214514, by rfl⟩) R429029
theorem R220483 : Reach 220483 := rs (se 1 (by rfl) ⟨165362, by rfl⟩) R330725
theorem R89543 : Reach 89543 := rs (se 1 (by rfl) ⟨67157, by rfl⟩) R134315
theorem R155297 : Reach 155297 := rs (se 2 (by rfl) ⟨58236, by rfl⟩) R116473
theorem R89897 : Reach 89897 := rs (se 2 (by rfl) ⟨33711, by rfl⟩) R67423
theorem R89903 : Reach 89903 := rs (se 1 (by rfl) ⟨67427, by rfl⟩) R134855
theorem R548801 : Reach 548801 := rs (se 2 (by rfl) ⟨205800, by rfl⟩) R411601
theorem R679873 : Reach 679873 := rs (se 2 (by rfl) ⟨254952, by rfl⟩) R509905
theorem R1138697 : Reach 1138697 := rs (se 2 (by rfl) ⟨427011, by rfl⟩) R854023
theorem R581651 : Reach 581651 := rs (se 1 (by rfl) ⟨436238, by rfl⟩) R872477
theorem R155753 : Reach 155753 := rs (se 2 (by rfl) ⟨58407, by rfl⟩) R116815
theorem R90377 : Reach 90377 := rs (se 2 (by rfl) ⟨33891, by rfl⟩) R67783
theorem R90479 : Reach 90479 := rs (se 1 (by rfl) ⟨67859, by rfl⟩) R135719
theorem R90695 : Reach 90695 := rs (se 1 (by rfl) ⟨68021, by rfl⟩) R136043
theorem R156239 : Reach 156239 := rs (se 1 (by rfl) ⟨117179, by rfl⟩) R234359
theorem R90731 : Reach 90731 := rs (se 1 (by rfl) ⟨68048, by rfl⟩) R136097
theorem R90959 : Reach 90959 := rs (se 1 (by rfl) ⟨68219, by rfl⟩) R136439
theorem R418823 : Reach 418823 := rs (se 1 (by rfl) ⟨314117, by rfl⟩) R628235
theorem R156887 : Reach 156887 := rs (se 1 (by rfl) ⟨117665, by rfl⟩) R235331
theorem R91355 : Reach 91355 := rs (se 1 (by rfl) ⟨68516, by rfl⟩) R137033
theorem R517499 : Reach 517499 := rs (se 1 (by rfl) ⟨388124, by rfl⟩) R776249
theorem R91529 : Reach 91529 := rs (se 2 (by rfl) ⟨34323, by rfl⟩) R68647
theorem R255469 : Reach 255469 := rs (se 3 (by rfl) ⟨47900, by rfl⟩) R95801
theorem R157241 : Reach 157241 := rs (se 2 (by rfl) ⟨58965, by rfl⟩) R117931
theorem R91883 : Reach 91883 := rs (se 1 (by rfl) ⟨68912, by rfl⟩) R137825
theorem R59183 : Reach 59183 := rs (se 1 (by rfl) ⟨44387, by rfl⟩) R88775
theorem R452429 : Reach 452429 := rs (se 3 (by rfl) ⟨84830, by rfl⟩) R169661
theorem R59291 : Reach 59291 := rs (se 1 (by rfl) ⟨44468, by rfl⟩) R88937
theorem R59343 : Reach 59343 := rs (se 1 (by rfl) ⟨44507, by rfl⟩) R89015
theorem R92111 : Reach 92111 := rs (se 1 (by rfl) ⟨69083, by rfl⟩) R138167
theorem R59367 : Reach 59367 := rs (se 1 (by rfl) ⟨44525, by rfl⟩) R89051
theorem R59679 : Reach 59679 := rs (se 1 (by rfl) ⟨44759, by rfl⟩) R89519
theorem R59739 : Reach 59739 := rs (se 1 (by rfl) ⟨44804, by rfl⟩) R89609
theorem R92507 : Reach 92507 := rs (se 1 (by rfl) ⟨69380, by rfl⟩) R138761
theorem R59759 : Reach 59759 := rs (se 1 (by rfl) ⟨44819, by rfl⟩) R89639
theorem R59815 : Reach 59815 := rs (se 1 (by rfl) ⟨44861, by rfl⟩) R89723
theorem R59899 : Reach 59899 := rs (se 1 (by rfl) ⟨44924, by rfl⟩) R89849
theorem R59967 : Reach 59967 := rs (se 1 (by rfl) ⟨44975, by rfl⟩) R89951
theorem R92735 : Reach 92735 := rs (se 1 (by rfl) ⟨69551, by rfl⟩) R139103
theorem R59975 : Reach 59975 := rs (se 1 (by rfl) ⟨44981, by rfl⟩) R89963
theorem R289403 : Reach 289403 := rs (se 1 (by rfl) ⟨217052, by rfl⟩) R434105
theorem R92855 : Reach 92855 := rs (se 1 (by rfl) ⟨69641, by rfl⟩) R139283
theorem R60127 : Reach 60127 := rs (se 1 (by rfl) ⟨45095, by rfl⟩) R90191
theorem R60207 : Reach 60207 := rs (se 1 (by rfl) ⟨45155, by rfl⟩) R90311
theorem R60315 : Reach 60315 := rs (se 1 (by rfl) ⟨45236, by rfl⟩) R90473
theorem R93083 : Reach 93083 := rs (se 1 (by rfl) ⟨69812, by rfl⟩) R139625
theorem R60367 : Reach 60367 := rs (se 1 (by rfl) ⟨45275, by rfl⟩) R90551
theorem R60391 : Reach 60391 := rs (se 1 (by rfl) ⟨45293, by rfl⟩) R90587
theorem R60703 : Reach 60703 := rs (se 1 (by rfl) ⟨45527, by rfl⟩) R91055
theorem R93479 : Reach 93479 := rs (se 1 (by rfl) ⟨70109, by rfl⟩) R140219
theorem R60763 : Reach 60763 := rs (se 1 (by rfl) ⟨45572, by rfl⟩) R91145
theorem R60783 : Reach 60783 := rs (se 1 (by rfl) ⟨45587, by rfl⟩) R91175
theorem R93563 : Reach 93563 := rs (se 1 (by rfl) ⟨70172, by rfl⟩) R140345
theorem R60839 : Reach 60839 := rs (se 1 (by rfl) ⟨45629, by rfl⟩) R91259
theorem R1404377 : Reach 1404377 := rs (se 2 (by rfl) ⟨526641, by rfl⟩) R1053283
theorem R93689 : Reach 93689 := rs (se 2 (by rfl) ⟨35133, by rfl⟩) R70267
theorem R60923 : Reach 60923 := rs (se 1 (by rfl) ⟨45692, by rfl⟩) R91385
theorem R60991 : Reach 60991 := rs (se 1 (by rfl) ⟨45743, by rfl⟩) R91487
theorem R60999 : Reach 60999 := rs (se 1 (by rfl) ⟨45749, by rfl⟩) R91499
theorem R93791 : Reach 93791 := rs (se 1 (by rfl) ⟨70343, by rfl⟩) R140687
theorem R1175233 : Reach 1175233 := rs (se 2 (by rfl) ⟨440712, by rfl⟩) R881425
theorem R61151 : Reach 61151 := rs (se 1 (by rfl) ⟨45863, by rfl⟩) R91727
theorem R93959 : Reach 93959 := rs (se 1 (by rfl) ⟨70469, by rfl⟩) R140939
theorem R159529 : Reach 159529 := rs (se 2 (by rfl) ⟨59823, by rfl⟩) R119647
theorem R61231 : Reach 61231 := rs (se 1 (by rfl) ⟨45923, by rfl⟩) R91847
theorem R94007 : Reach 94007 := rs (se 1 (by rfl) ⟨70505, by rfl⟩) R141011
theorem R388921 : Reach 388921 := rs (se 2 (by rfl) ⟨145845, by rfl⟩) R291691
theorem R61339 : Reach 61339 := rs (se 1 (by rfl) ⟨46004, by rfl⟩) R92009
theorem R61391 : Reach 61391 := rs (se 1 (by rfl) ⟨46043, by rfl⟩) R92087
theorem R61415 : Reach 61415 := rs (se 1 (by rfl) ⟨46061, by rfl⟩) R92123
theorem R94313 : Reach 94313 := rs (se 2 (by rfl) ⟨35367, by rfl⟩) R70735
theorem R61727 : Reach 61727 := rs (se 1 (by rfl) ⟨46295, by rfl⟩) R92591
theorem R61787 : Reach 61787 := rs (se 1 (by rfl) ⟨46340, by rfl⟩) R92681
theorem R61807 : Reach 61807 := rs (se 1 (by rfl) ⟨46355, by rfl⟩) R92711
theorem R61863 : Reach 61863 := rs (se 1 (by rfl) ⟨46397, by rfl⟩) R92795
theorem R94631 : Reach 94631 := rs (se 1 (by rfl) ⟨70973, by rfl⟩) R141947
theorem R160211 : Reach 160211 := rs (se 1 (by rfl) ⟨120158, by rfl⟩) R240317
theorem R61947 : Reach 61947 := rs (se 1 (by rfl) ⟨46460, by rfl⟩) R92921
theorem R62015 : Reach 62015 := rs (se 1 (by rfl) ⟨46511, by rfl⟩) R93023
theorem R62023 : Reach 62023 := rs (se 1 (by rfl) ⟨46517, by rfl⟩) R93035
theorem R94841 : Reach 94841 := rs (se 2 (by rfl) ⟨35565, by rfl⟩) R71131
theorem R291481 : Reach 291481 := rs (se 2 (by rfl) ⟨109305, by rfl⟩) R218611
theorem R62175 : Reach 62175 := rs (se 1 (by rfl) ⟨46631, by rfl⟩) R93263
theorem R62255 : Reach 62255 := rs (se 1 (by rfl) ⟨46691, by rfl⟩) R93383
theorem R62287 : Reach 62287 := rs (se 1 (by rfl) ⟨46715, by rfl⟩) R93431
theorem R62363 : Reach 62363 := rs (se 1 (by rfl) ⟨46772, by rfl⟩) R93545
theorem R62415 : Reach 62415 := rs (se 1 (by rfl) ⟨46811, by rfl⟩) R93623
theorem R193499 : Reach 193499 := rs (se 1 (by rfl) ⟨145124, by rfl⟩) R290249
theorem R62439 : Reach 62439 := rs (se 1 (by rfl) ⟨46829, by rfl⟩) R93659
theorem R62683 : Reach 62683 := rs (se 1 (by rfl) ⟨47012, by rfl⟩) R94025
theorem R62751 : Reach 62751 := rs (se 1 (by rfl) ⟨47063, by rfl⟩) R94127
theorem R62759 : Reach 62759 := rs (se 1 (by rfl) ⟨47069, by rfl⟩) R94139
theorem R62811 : Reach 62811 := rs (se 1 (by rfl) ⟨47108, by rfl⟩) R94217
theorem R259433 : Reach 259433 := rs (se 2 (by rfl) ⟨97287, by rfl⟩) R194575
theorem R62831 : Reach 62831 := rs (se 1 (by rfl) ⟨47123, by rfl⟩) R94247
theorem R62843 : Reach 62843 := rs (se 1 (by rfl) ⟨47132, by rfl⟩) R94265
theorem R62887 : Reach 62887 := rs (se 1 (by rfl) ⟨47165, by rfl⟩) R94331
theorem R62919 : Reach 62919 := rs (se 1 (by rfl) ⟨47189, by rfl⟩) R94379
theorem R62971 : Reach 62971 := rs (se 1 (by rfl) ⟨47228, by rfl⟩) R94457
theorem R63039 : Reach 63039 := rs (se 1 (by rfl) ⟨47279, by rfl⟩) R94559
theorem R63047 : Reach 63047 := rs (se 1 (by rfl) ⟨47285, by rfl⟩) R94571
theorem R63071 : Reach 63071 := rs (se 1 (by rfl) ⟨47303, by rfl⟩) R94607
theorem R161543 : Reach 161543 := rs (se 1 (by rfl) ⟨121157, by rfl⟩) R242315
theorem R194359 : Reach 194359 := rs (se 1 (by rfl) ⟨145769, by rfl⟩) R291539
theorem R1144691 : Reach 1144691 := rs (se 1 (by rfl) ⟨858518, by rfl⟩) R1717037
theorem R456839 : Reach 456839 := rs (se 1 (by rfl) ⟨342629, by rfl⟩) R685259
theorem R653579 : Reach 653579 := rs (se 1 (by rfl) ⟨490184, by rfl⟩) R980369
theorem R260377 : Reach 260377 := rs (se 2 (by rfl) ⟨97641, by rfl⟩) R195283
theorem R424217 : Reach 424217 := rs (se 2 (by rfl) ⟨159081, by rfl⟩) R318163
theorem R162731 : Reach 162731 := rs (se 1 (by rfl) ⟨122048, by rfl⟩) R244097
theorem R261035 : Reach 261035 := rs (se 1 (by rfl) ⟨195776, by rfl⟩) R391553
theorem R228541 : Reach 228541 := rs (se 3 (by rfl) ⟨42851, by rfl⟩) R85703
theorem R851267 : Reach 851267 := rs (se 1 (by rfl) ⟨638450, by rfl⟩) R1276901
theorem R195959 : Reach 195959 := rs (se 1 (by rfl) ⟨146969, by rfl⟩) R293939
theorem R163385 : Reach 163385 := rs (se 2 (by rfl) ⟨61269, by rfl⟩) R122539
theorem R130871 : Reach 130871 := rs (se 1 (by rfl) ⟨98153, by rfl⟩) R196307
theorem R294785 : Reach 294785 := rs (se 2 (by rfl) ⟨110544, by rfl⟩) R221089
theorem R753569 : Reach 753569 := rs (se 2 (by rfl) ⟨282588, by rfl⟩) R565177
theorem R1048627 : Reach 1048627 := rs (se 1 (by rfl) ⟨786470, by rfl⟩) R1572941
theorem R98591 : Reach 98591 := rs (se 1 (by rfl) ⟨73943, by rfl⟩) R147887
theorem R197063 : Reach 197063 := rs (se 1 (by rfl) ⟨147797, by rfl⟩) R295595
theorem R525257 : Reach 525257 := rs (se 2 (by rfl) ⟨196971, by rfl⟩) R393943
theorem R755077 : Reach 755077 := rs (se 4 (by rfl) ⟨70788, by rfl⟩) R141577
theorem R198163 : Reach 198163 := rs (se 1 (by rfl) ⟨148622, by rfl⟩) R297245
theorem R296783 : Reach 296783 := rs (se 1 (by rfl) ⟨222587, by rfl⟩) R445175
theorem R67567 : Reach 67567 := rs (se 1 (by rfl) ⟨50675, by rfl⟩) R101351
theorem R100345 : Reach 100345 := rs (se 2 (by rfl) ⟨37629, by rfl⟩) R75259
theorem R100507 : Reach 100507 := rs (se 1 (by rfl) ⟨75380, by rfl⟩) R150761
theorem R100543 : Reach 100543 := rs (se 1 (by rfl) ⟨75407, by rfl⟩) R150815
theorem R100615 : Reach 100615 := rs (se 1 (by rfl) ⟨75461, by rfl⟩) R150923
theorem R133415 : Reach 133415 := rs (se 1 (by rfl) ⟨100061, by rfl⟩) R200123
theorem R100649 : Reach 100649 := rs (se 2 (by rfl) ⟨37743, by rfl⟩) R75487
theorem R133433 : Reach 133433 := rs (se 2 (by rfl) ⟨50037, by rfl⟩) R100075
theorem R231943 : Reach 231943 := rs (se 1 (by rfl) ⟨173957, by rfl⟩) R347915
theorem R1378889 : Reach 1378889 := rs (se 2 (by rfl) ⟨517083, by rfl⟩) R1034167
theorem R101641 : Reach 101641 := rs (se 2 (by rfl) ⟨38115, by rfl⟩) R76231
theorem R199961 : Reach 199961 := rs (se 2 (by rfl) ⟨74985, by rfl⟩) R149971
theorem R200015 : Reach 200015 := rs (se 1 (by rfl) ⟨150011, by rfl⟩) R300023
theorem R134569 : Reach 134569 := rs (se 2 (by rfl) ⟨50463, by rfl⟩) R100927
theorem R396863 : Reach 396863 := rs (se 1 (by rfl) ⟨297647, by rfl⟩) R595295
theorem R134729 : Reach 134729 := rs (se 2 (by rfl) ⟨50523, by rfl⟩) R101047
theorem R134951 : Reach 134951 := rs (se 1 (by rfl) ⟨101213, by rfl⟩) R202427
theorem R102215 : Reach 102215 := rs (se 1 (by rfl) ⟨76661, by rfl⟩) R153323
theorem R135355 : Reach 135355 := rs (se 1 (by rfl) ⟨101516, by rfl⟩) R203033
theorem R299375 : Reach 299375 := rs (se 1 (by rfl) ⟨224531, by rfl⟩) R449063
theorem R70015 : Reach 70015 := rs (se 1 (by rfl) ⟨52511, by rfl⟩) R105023
theorem R102863 : Reach 102863 := rs (se 1 (by rfl) ⟨77147, by rfl⟩) R154295
theorem R201311 : Reach 201311 := rs (se 1 (by rfl) ⟨150983, by rfl⟩) R301967
theorem R136187 : Reach 136187 := rs (se 1 (by rfl) ⟨102140, by rfl⟩) R204281
theorem R267259 : Reach 267259 := rs (se 1 (by rfl) ⟨200444, by rfl⟩) R400889
theorem R103531 : Reach 103531 := rs (se 1 (by rfl) ⟨77648, by rfl⟩) R155297
theorem R398479 : Reach 398479 := rs (se 1 (by rfl) ⟨298859, by rfl⟩) R597719
theorem R136367 : Reach 136367 := rs (se 1 (by rfl) ⟨102275, by rfl⟩) R204551
theorem R136403 : Reach 136403 := rs (se 1 (by rfl) ⟨102302, by rfl⟩) R204605
theorem R365867 : Reach 365867 := rs (se 1 (by rfl) ⟨274400, by rfl⟩) R548801
theorem R759131 : Reach 759131 := rs (se 1 (by rfl) ⟨569348, by rfl⟩) R1138697
theorem R103835 : Reach 103835 := rs (se 1 (by rfl) ⟨77876, by rfl⟩) R155753
theorem R136673 : Reach 136673 := rs (se 2 (by rfl) ⟨51252, by rfl⟩) R102505
theorem R104159 : Reach 104159 := rs (se 1 (by rfl) ⟨78119, by rfl⟩) R156239
theorem R202553 : Reach 202553 := rs (se 2 (by rfl) ⟨75957, by rfl⟩) R151915
theorem R202715 : Reach 202715 := rs (se 1 (by rfl) ⟨152036, by rfl⟩) R304073
theorem R104591 : Reach 104591 := rs (se 1 (by rfl) ⟨78443, by rfl⟩) R156887
theorem R202985 : Reach 202985 := rs (se 2 (by rfl) ⟨76119, by rfl⟩) R152239
theorem R530729 : Reach 530729 := rs (se 2 (by rfl) ⟨199023, by rfl⟩) R398047
theorem R235817 : Reach 235817 := rs (se 2 (by rfl) ⟨88431, by rfl⟩) R176863
theorem R104827 : Reach 104827 := rs (se 1 (by rfl) ⟨78620, by rfl⟩) R157241
theorem R4069757 : Reach 4069757 := rs (se 3 (by rfl) ⟨763079, by rfl⟩) R1526159
theorem R793061 : Reach 793061 := rs (se 4 (by rfl) ⟨74349, by rfl⟩) R148699
theorem R301619 : Reach 301619 := rs (se 1 (by rfl) ⟨226214, by rfl⟩) R452429
theorem R105097 : Reach 105097 := rs (se 2 (by rfl) ⟨39411, by rfl⟩) R78823
theorem R203417 : Reach 203417 := rs (se 2 (by rfl) ⟨76281, by rfl⟩) R152563
theorem R334793 : Reach 334793 := rs (se 2 (by rfl) ⟨125547, by rfl⟩) R251095
theorem R138311 : Reach 138311 := rs (se 1 (by rfl) ⟨103733, by rfl⟩) R207467
theorem R138707 : Reach 138707 := rs (se 1 (by rfl) ⟨104030, by rfl⟩) R208061
theorem R138977 : Reach 138977 := rs (se 2 (by rfl) ⟨52116, by rfl⟩) R104233
theorem R73543 : Reach 73543 := rs (se 1 (by rfl) ⟨55157, by rfl⟩) R110315
theorem R106807 : Reach 106807 := rs (se 1 (by rfl) ⟨80105, by rfl⟩) R160211
theorem R205307 : Reach 205307 := rs (se 1 (by rfl) ⟨153980, by rfl⟩) R307961
theorem R205577 : Reach 205577 := rs (se 2 (by rfl) ⟨77091, by rfl⟩) R154183
theorem R2270045 : Reach 2270045 := rs (se 3 (by rfl) ⟨425633, by rfl⟩) R851267
theorem R172955 : Reach 172955 := rs (se 1 (by rfl) ⟨129716, by rfl⟩) R259433
theorem R107695 : Reach 107695 := rs (se 1 (by rfl) ⟨80771, by rfl⟩) R161543
theorem R763127 : Reach 763127 := rs (se 1 (by rfl) ⟨572345, by rfl⟩) R1144691
theorem R140651 : Reach 140651 := rs (se 1 (by rfl) ⟨105488, by rfl⟩) R210977
theorem R75163 : Reach 75163 := rs (se 1 (by rfl) ⟨56372, by rfl⟩) R112745
theorem R304559 : Reach 304559 := rs (se 1 (by rfl) ⟨228419, by rfl⟩) R456839
theorem R370169 : Reach 370169 := rs (se 2 (by rfl) ⟨138813, by rfl⟩) R277627
theorem R206333 : Reach 206333 := rs (se 3 (by rfl) ⟨38687, by rfl⟩) R77375
theorem R435719 : Reach 435719 := rs (se 1 (by rfl) ⟨326789, by rfl⟩) R653579
theorem R304721 : Reach 304721 := rs (se 2 (by rfl) ⟨114270, by rfl⟩) R228541
theorem R140921 : Reach 140921 := rs (se 2 (by rfl) ⟨52845, by rfl⟩) R105691
theorem R75431 : Reach 75431 := rs (se 1 (by rfl) ⟨56573, by rfl⟩) R113147
theorem R75583 : Reach 75583 := rs (se 1 (by rfl) ⟨56687, by rfl⟩) R113375
theorem R108487 : Reach 108487 := rs (se 1 (by rfl) ⟨81365, by rfl⟩) R162731
theorem R174023 : Reach 174023 := rs (se 1 (by rfl) ⟨130517, by rfl⟩) R261035
theorem R207143 : Reach 207143 := rs (se 1 (by rfl) ⟨155357, by rfl⟩) R310715
theorem R76079 : Reach 76079 := rs (se 1 (by rfl) ⟨57059, by rfl⟩) R114119
theorem R108923 : Reach 108923 := rs (se 1 (by rfl) ⟨81692, by rfl⟩) R163385
theorem R141929 : Reach 141929 := rs (se 2 (by rfl) ⟨53223, by rfl⟩) R106447
theorem R502379 : Reach 502379 := rs (se 1 (by rfl) ⟨376784, by rfl⟩) R753569
theorem R175067 : Reach 175067 := rs (se 1 (by rfl) ⟨131300, by rfl⟩) R262601
theorem R306139 : Reach 306139 := rs (se 1 (by rfl) ⟨229604, by rfl⟩) R459209
theorem R207919 : Reach 207919 := rs (se 1 (by rfl) ⟨155939, by rfl⟩) R311879
theorem R208007 : Reach 208007 := rs (se 1 (by rfl) ⟨156005, by rfl⟩) R312011
theorem R208115 : Reach 208115 := rs (se 1 (by rfl) ⟨156086, by rfl⟩) R312173
theorem R863531 : Reach 863531 := rs (se 1 (by rfl) ⟨647648, by rfl⟩) R1295297
theorem R175439 : Reach 175439 := rs (se 1 (by rfl) ⟨131579, by rfl⟩) R263159
theorem R1453625 : Reach 1453625 := rs (se 2 (by rfl) ⟨545109, by rfl⟩) R1090219
theorem R175679 : Reach 175679 := rs (se 1 (by rfl) ⟨131759, by rfl⟩) R263519
theorem R110459 : Reach 110459 := rs (se 1 (by rfl) ⟨82844, by rfl⟩) R165689
theorem R307151 : Reach 307151 := rs (se 1 (by rfl) ⟨230363, by rfl⟩) R460727
theorem R536705 : Reach 536705 := rs (se 2 (by rfl) ⟨201264, by rfl⟩) R402529
theorem R1388677 : Reach 1388677 := rs (se 4 (by rfl) ⟨130188, by rfl⟩) R260377
theorem R340625 : Reach 340625 := rs (se 2 (by rfl) ⟨127734, by rfl⟩) R255469
theorem R209789 : Reach 209789 := rs (se 3 (by rfl) ⟨39335, by rfl⟩) R78671
theorem R210059 : Reach 210059 := rs (se 1 (by rfl) ⟨157544, by rfl⟩) R315089
theorem R505025 : Reach 505025 := rs (se 2 (by rfl) ⟨189384, by rfl⟩) R378769
theorem R1553651 : Reach 1553651 := rs (se 1 (by rfl) ⟨1165238, by rfl⟩) R2330477
theorem R308609 : Reach 308609 := rs (se 2 (by rfl) ⟨115728, by rfl⟩) R231457
theorem R833111 : Reach 833111 := rs (se 1 (by rfl) ⟨624833, by rfl⟩) R1249667
theorem R79471 : Reach 79471 := rs (se 1 (by rfl) ⟨59603, by rfl⟩) R119207
theorem R177967 : Reach 177967 := rs (se 1 (by rfl) ⟨133475, by rfl⟩) R266951
theorem R112447 : Reach 112447 := rs (se 1 (by rfl) ⟨84335, by rfl⟩) R168671
theorem R178139 : Reach 178139 := rs (se 1 (by rfl) ⟨133604, by rfl⟩) R267209
theorem R1554565 : Reach 1554565 := rs (se 4 (by rfl) ⟨145740, by rfl⟩) R291481
theorem R309419 : Reach 309419 := rs (se 1 (by rfl) ⟨232064, by rfl⟩) R464129
theorem R702755 : Reach 702755 := rs (se 1 (by rfl) ⟨527066, by rfl⟩) R1054133
theorem R80411 : Reach 80411 := rs (se 1 (by rfl) ⟨60308, by rfl⟩) R120617
theorem R211679 : Reach 211679 := rs (se 1 (by rfl) ⟨158759, by rfl⟩) R317519
theorem R113633 : Reach 113633 := rs (se 2 (by rfl) ⟨42612, by rfl⟩) R85225
theorem R211949 : Reach 211949 := rs (se 3 (by rfl) ⟨39740, by rfl⟩) R79481
theorem R343223 : Reach 343223 := rs (se 1 (by rfl) ⟨257417, by rfl⟩) R514835
theorem R212435 : Reach 212435 := rs (se 1 (by rfl) ⟨159326, by rfl⟩) R318653
theorem R245339 : Reach 245339 := rs (se 1 (by rfl) ⟨184004, by rfl⟩) R368009
theorem R573115 : Reach 573115 := rs (se 1 (by rfl) ⟨429836, by rfl⟩) R859673
theorem R212705 : Reach 212705 := rs (se 2 (by rfl) ⟨79764, by rfl⟩) R159529
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R279215 : Reach 279215 := rs (se 1 (by rfl) ⟨209411, by rfl⟩) R418823
theorem R344999 : Reach 344999 := rs (se 1 (by rfl) ⟨258749, by rfl⟩) R517499
theorem R936251 : Reach 936251 := rs (se 1 (by rfl) ⟨702188, by rfl⟩) R1404377
theorem R149921 : Reach 149921 := rs (se 2 (by rfl) ⟨56220, by rfl⟩) R112441
theorem R313793 : Reach 313793 := rs (se 2 (by rfl) ⟨117672, by rfl⟩) R235345
theorem R117739 : Reach 117739 := rs (se 1 (by rfl) ⟨88304, by rfl⟩) R176609
theorem R282811 : Reach 282811 := rs (se 1 (by rfl) ⟨212108, by rfl⟩) R424217
theorem R315863 : Reach 315863 := rs (se 1 (by rfl) ⟨236897, by rfl⟩) R473795
theorem R152057 : Reach 152057 := rs (se 2 (by rfl) ⟨57021, by rfl⟩) R114043
theorem R87247 : Reach 87247 := rs (se 1 (by rfl) ⟨65435, by rfl⟩) R130871
theorem R906497 : Reach 906497 := rs (se 2 (by rfl) ⟨339936, by rfl⟩) R679873
theorem R185755 : Reach 185755 := rs (se 1 (by rfl) ⟨139316, by rfl⟩) R278633
theorem R317195 : Reach 317195 := rs (se 1 (by rfl) ⟨237896, by rfl⟩) R475793
theorem R153697 : Reach 153697 := rs (se 2 (by rfl) ⟨57636, by rfl⟩) R115273
theorem R13031725 : Reach 13031725 := rs (se 3 (by rfl) ⟨2443448, by rfl⟩) R4886897
theorem R1137239 : Reach 1137239 := rs (se 1 (by rfl) ⟨852929, by rfl⟩) R1705859
theorem R481879 : Reach 481879 := rs (se 1 (by rfl) ⟨361409, by rfl⟩) R722819
theorem R252715 : Reach 252715 := rs (se 1 (by rfl) ⟨189536, by rfl⟩) R379073
theorem R973619 : Reach 973619 := rs (se 1 (by rfl) ⟨730214, by rfl⟩) R1460429
theorem R219995 : Reach 219995 := rs (se 1 (by rfl) ⟨164996, by rfl⟩) R329993
theorem R88991 : Reach 88991 := rs (se 1 (by rfl) ⟨66743, by rfl⟩) R133487
theorem R89039 : Reach 89039 := rs (se 1 (by rfl) ⟨66779, by rfl⟩) R133559
theorem R1530899 : Reach 1530899 := rs (se 1 (by rfl) ⟨1148174, by rfl⟩) R2296349
theorem R89129 : Reach 89129 := rs (se 2 (by rfl) ⟨33423, by rfl⟩) R66847
theorem R89135 : Reach 89135 := rs (se 1 (by rfl) ⟨66851, by rfl⟩) R133703
theorem R89159 : Reach 89159 := rs (se 1 (by rfl) ⟨66869, by rfl⟩) R133739
theorem R89423 : Reach 89423 := rs (se 1 (by rfl) ⟨67067, by rfl⟩) R134135
theorem R318815 : Reach 318815 := rs (se 1 (by rfl) ⟨239111, by rfl⟩) R478223
theorem R89513 : Reach 89513 := rs (se 2 (by rfl) ⟨33567, by rfl⟩) R67135
theorem R89663 : Reach 89663 := rs (se 1 (by rfl) ⟨67247, by rfl⟩) R134495
theorem R11951887 : Reach 11951887 := rs (se 1 (by rfl) ⟨8963915, by rfl⟩) R17927831
theorem R89927 : Reach 89927 := rs (se 1 (by rfl) ⟨67445, by rfl⟩) R134891
theorem R90011 : Reach 90011 := rs (se 1 (by rfl) ⟨67508, by rfl⟩) R135017
theorem R254087 : Reach 254087 := rs (se 1 (by rfl) ⟨190565, by rfl⟩) R381131
theorem R254171 : Reach 254171 := rs (se 1 (by rfl) ⟨190628, by rfl⟩) R381257
theorem R581879 : Reach 581879 := rs (se 1 (by rfl) ⟨436409, by rfl⟩) R872819
theorem R286967 : Reach 286967 := rs (se 1 (by rfl) ⟨215225, by rfl⟩) R430451
theorem R1007873 : Reach 1007873 := rs (se 2 (by rfl) ⟨377952, by rfl⟩) R755905
theorem R712961 : Reach 712961 := rs (se 2 (by rfl) ⟨267360, by rfl⟩) R534721
theorem R221537 : Reach 221537 := rs (se 2 (by rfl) ⟨83076, by rfl⟩) R166153
theorem R90575 : Reach 90575 := rs (se 1 (by rfl) ⟨67931, by rfl⟩) R135863
theorem R352745 : Reach 352745 := rs (se 2 (by rfl) ⟨132279, by rfl⟩) R264559
theorem R90617 : Reach 90617 := rs (se 2 (by rfl) ⟨33981, by rfl⟩) R67963
theorem R90719 : Reach 90719 := rs (se 1 (by rfl) ⟨68039, by rfl⟩) R136079
theorem R156289 : Reach 156289 := rs (se 2 (by rfl) ⟨58608, by rfl⟩) R117217
theorem R451493 : Reach 451493 := rs (se 4 (by rfl) ⟨42327, by rfl⟩) R84655
theorem R91199 : Reach 91199 := rs (se 1 (by rfl) ⟨68399, by rfl⟩) R136799
theorem R91241 : Reach 91241 := rs (se 2 (by rfl) ⟨34215, by rfl⟩) R68431
theorem R3957923 : Reach 3957923 := rs (se 1 (by rfl) ⟨2968442, by rfl⟩) R5936885
theorem R91343 : Reach 91343 := rs (se 1 (by rfl) ⟨68507, by rfl⟩) R137015
theorem R91547 : Reach 91547 := rs (se 1 (by rfl) ⟨68660, by rfl⟩) R137321
theorem R157099 : Reach 157099 := rs (se 1 (by rfl) ⟨117824, by rfl⟩) R235649
theorem R189949 : Reach 189949 := rs (se 3 (by rfl) ⟨35615, by rfl⟩) R71231
theorem R91769 : Reach 91769 := rs (se 2 (by rfl) ⟨34413, by rfl⟩) R68827
theorem R157403 : Reach 157403 := rs (se 1 (by rfl) ⟨118052, by rfl⟩) R236105
theorem R91871 : Reach 91871 := rs (se 1 (by rfl) ⟨68903, by rfl⟩) R137807
theorem R59131 : Reach 59131 := rs (se 1 (by rfl) ⟨44348, by rfl⟩) R88697
theorem R59167 : Reach 59167 := rs (se 1 (by rfl) ⟨44375, by rfl⟩) R88751
theorem R59199 : Reach 59199 := rs (se 1 (by rfl) ⟨44399, by rfl⟩) R88799
theorem R91967 : Reach 91967 := rs (se 1 (by rfl) ⟨68975, by rfl⟩) R137951
theorem R92135 : Reach 92135 := rs (se 1 (by rfl) ⟨69101, by rfl⟩) R138203
theorem R59375 : Reach 59375 := rs (se 1 (by rfl) ⟨44531, by rfl⟩) R89063
theorem R92153 : Reach 92153 := rs (se 2 (by rfl) ⟨34557, by rfl⟩) R69115
theorem R288787 : Reach 288787 := rs (se 1 (by rfl) ⟨216590, by rfl⟩) R433181
theorem R92255 : Reach 92255 := rs (se 1 (by rfl) ⟨69191, by rfl⟩) R138383
theorem R59547 : Reach 59547 := rs (se 1 (by rfl) ⟨44660, by rfl⟩) R89321
theorem R92315 : Reach 92315 := rs (se 1 (by rfl) ⟨69236, by rfl⟩) R138473
theorem R59583 : Reach 59583 := rs (se 1 (by rfl) ⟨44687, by rfl⟩) R89375
theorem R92351 : Reach 92351 := rs (se 1 (by rfl) ⟨69263, by rfl⟩) R138527
theorem R190679 : Reach 190679 := rs (se 1 (by rfl) ⟨143009, by rfl⟩) R286019
theorem R92393 : Reach 92393 := rs (se 2 (by rfl) ⟨34647, by rfl⟩) R69295
theorem R1566977 : Reach 1566977 := rs (se 2 (by rfl) ⟨587616, by rfl⟩) R1175233
theorem R59695 : Reach 59695 := rs (se 1 (by rfl) ⟨44771, by rfl⟩) R89543
theorem R518561 : Reach 518561 := rs (se 2 (by rfl) ⟨194460, by rfl⟩) R388921
theorem R59931 : Reach 59931 := rs (se 1 (by rfl) ⟨44948, by rfl⟩) R89897
theorem R92699 : Reach 92699 := rs (se 1 (by rfl) ⟨69524, by rfl⟩) R139049
theorem R59935 : Reach 59935 := rs (se 1 (by rfl) ⟨44951, by rfl⟩) R89903
theorem R354887 : Reach 354887 := rs (se 1 (by rfl) ⟨266165, by rfl⟩) R532331
theorem R92777 : Reach 92777 := rs (se 2 (by rfl) ⟨34791, by rfl⟩) R69583
theorem R387767 : Reach 387767 := rs (se 1 (by rfl) ⟨290825, by rfl⟩) R581651
theorem R158395 : Reach 158395 := rs (se 1 (by rfl) ⟨118796, by rfl⟩) R237593
theorem R60251 : Reach 60251 := rs (se 1 (by rfl) ⟨45188, by rfl⟩) R90377
theorem R60319 : Reach 60319 := rs (se 1 (by rfl) ⟨45239, by rfl⟩) R90479
theorem R158699 : Reach 158699 := rs (se 1 (by rfl) ⟨119024, by rfl⟩) R238049
theorem R60463 : Reach 60463 := rs (se 1 (by rfl) ⟨45347, by rfl⟩) R90695
theorem R60487 : Reach 60487 := rs (se 1 (by rfl) ⟨45365, by rfl⟩) R90731
theorem R93305 : Reach 93305 := rs (se 2 (by rfl) ⟨34989, by rfl⟩) R69979
theorem R60639 : Reach 60639 := rs (se 1 (by rfl) ⟨45479, by rfl⟩) R90959
theorem R93407 : Reach 93407 := rs (se 1 (by rfl) ⟨70055, by rfl⟩) R140111
theorem R93449 : Reach 93449 := rs (se 2 (by rfl) ⟨35043, by rfl⟩) R70087
theorem R93551 : Reach 93551 := rs (se 1 (by rfl) ⟨70163, by rfl⟩) R140327
theorem R60903 : Reach 60903 := rs (se 1 (by rfl) ⟨45677, by rfl⟩) R91355
theorem R93671 : Reach 93671 := rs (se 1 (by rfl) ⟨70253, by rfl⟩) R140507
theorem R355913 : Reach 355913 := rs (se 2 (by rfl) ⟨133467, by rfl⟩) R266935
theorem R61019 : Reach 61019 := rs (se 1 (by rfl) ⟨45764, by rfl⟩) R91529
theorem R93803 : Reach 93803 := rs (se 1 (by rfl) ⟨70352, by rfl⟩) R140705
theorem R93839 : Reach 93839 := rs (se 1 (by rfl) ⟨70379, by rfl⟩) R140759
theorem R1273553 : Reach 1273553 := rs (se 2 (by rfl) ⟨477582, by rfl⟩) R955165
theorem R93929 : Reach 93929 := rs (se 2 (by rfl) ⟨35223, by rfl⟩) R70447
theorem R61255 : Reach 61255 := rs (se 1 (by rfl) ⟨45941, by rfl⟩) R91883
theorem R94073 : Reach 94073 := rs (se 2 (by rfl) ⟨35277, by rfl⟩) R70555
theorem R61407 : Reach 61407 := rs (se 1 (by rfl) ⟨46055, by rfl⟩) R92111
theorem R94175 : Reach 94175 := rs (se 1 (by rfl) ⟨70631, by rfl⟩) R141263
theorem R94427 : Reach 94427 := rs (se 1 (by rfl) ⟨70820, by rfl⟩) R141641
theorem R61671 : Reach 61671 := rs (se 1 (by rfl) ⟨46253, by rfl⟩) R92507
theorem R94439 : Reach 94439 := rs (se 1 (by rfl) ⟨70829, by rfl⟩) R141659
theorem R356663 : Reach 356663 := rs (se 1 (by rfl) ⟨267497, by rfl⟩) R534995
theorem R61823 : Reach 61823 := rs (se 1 (by rfl) ⟨46367, by rfl⟩) R92735
theorem R94601 : Reach 94601 := rs (se 2 (by rfl) ⟨35475, by rfl⟩) R70951
theorem R192935 : Reach 192935 := rs (se 1 (by rfl) ⟨144701, by rfl⟩) R289403
theorem R61903 : Reach 61903 := rs (se 1 (by rfl) ⟨46427, by rfl⟩) R92855
theorem R62055 : Reach 62055 := rs (se 1 (by rfl) ⟨46541, by rfl⟩) R93083
theorem R62319 : Reach 62319 := rs (se 1 (by rfl) ⟨46739, by rfl⟩) R93479
theorem R62375 : Reach 62375 := rs (se 1 (by rfl) ⟨46781, by rfl⟩) R93563
theorem R62459 : Reach 62459 := rs (se 1 (by rfl) ⟨46844, by rfl⟩) R93689
theorem R62527 : Reach 62527 := rs (se 1 (by rfl) ⟨46895, by rfl⟩) R93791
theorem R259145 : Reach 259145 := rs (se 2 (by rfl) ⟨97179, by rfl⟩) R194359
theorem R62639 : Reach 62639 := rs (se 1 (by rfl) ⟨46979, by rfl⟩) R93959
theorem R95407 : Reach 95407 := rs (se 1 (by rfl) ⟨71555, by rfl⟩) R143111
theorem R62671 : Reach 62671 := rs (se 1 (by rfl) ⟨47003, by rfl⟩) R94007
theorem R62875 : Reach 62875 := rs (se 1 (by rfl) ⟨47156, by rfl⟩) R94313
theorem R63087 : Reach 63087 := rs (se 1 (by rfl) ⟨47315, by rfl⟩) R94631
theorem R63227 : Reach 63227 := rs (se 1 (by rfl) ⟨47420, by rfl⟩) R94841
theorem R128999 : Reach 128999 := rs (se 1 (by rfl) ⟨96749, by rfl⟩) R193499
theorem R227387 : Reach 227387 := rs (se 1 (by rfl) ⟨170540, by rfl⟩) R341081
theorem R522557 : Reach 522557 := rs (se 3 (by rfl) ⟨97979, by rfl⟩) R195959
theorem R96635 : Reach 96635 := rs (se 1 (by rfl) ⟨72476, by rfl⟩) R144953
theorem R358829 : Reach 358829 := rs (se 3 (by rfl) ⟨67280, by rfl⟩) R134561
theorem R293977 : Reach 293977 := rs (se 2 (by rfl) ⟨110241, by rfl⟩) R220483
theorem R97865 : Reach 97865 := rs (se 2 (by rfl) ⟨36699, by rfl⟩) R73399
theorem R97967 : Reach 97967 := rs (se 1 (by rfl) ⟨73475, by rfl⟩) R146951
theorem R196523 : Reach 196523 := rs (se 1 (by rfl) ⟨147392, by rfl⟩) R294785
theorem R131375 : Reach 131375 := rs (se 1 (by rfl) ⟨98531, by rfl⟩) R197063
theorem R229999 : Reach 229999 := rs (se 1 (by rfl) ⟨172499, by rfl⟩) R344999
theorem R262909 : Reach 262909 := rs (se 3 (by rfl) ⟨49295, by rfl⟩) R98591
theorem R197855 : Reach 197855 := rs (se 1 (by rfl) ⟨148391, by rfl⟩) R296783
theorem R67099 : Reach 67099 := rs (se 1 (by rfl) ⟨50324, by rfl⟩) R100649
theorem R624167 : Reach 624167 := rs (se 1 (by rfl) ⟨468125, by rfl⟩) R936251
theorem R99947 : Reach 99947 := rs (se 1 (by rfl) ⟨74960, by rfl⟩) R149921
theorem R919259 : Reach 919259 := rs (se 1 (by rfl) ⟨689444, by rfl⟩) R1378889
theorem R100217 : Reach 100217 := rs (se 2 (by rfl) ⟨37581, by rfl⟩) R75163
theorem R264217 : Reach 264217 := rs (se 2 (by rfl) ⟨99081, by rfl⟩) R198163
theorem R133307 : Reach 133307 := rs (se 1 (by rfl) ⟨99980, by rfl⟩) R199961
theorem R133343 : Reach 133343 := rs (se 1 (by rfl) ⟨100007, by rfl⟩) R200015
theorem R264575 : Reach 264575 := rs (se 1 (by rfl) ⟨198431, by rfl⟩) R396863
theorem R461213 : Reach 461213 := rs (se 3 (by rfl) ⟨86477, by rfl⟩) R172955
theorem R100777 : Reach 100777 := rs (se 2 (by rfl) ⟨37791, by rfl⟩) R75583
theorem R68143 : Reach 68143 := rs (se 1 (by rfl) ⟨51107, by rfl⟩) R102215
theorem R133793 : Reach 133793 := rs (se 2 (by rfl) ⟨50172, by rfl⟩) R100345
theorem R16714421 : Reach 16714421 := rs (se 5 (by rfl) ⟨783488, by rfl⟩) R1566977
theorem R134009 : Reach 134009 := rs (se 2 (by rfl) ⟨50253, by rfl⟩) R100507
theorem R199583 : Reach 199583 := rs (se 1 (by rfl) ⟨149687, by rfl⟩) R299375
theorem R134057 : Reach 134057 := rs (se 2 (by rfl) ⟨50271, by rfl⟩) R100543
theorem R68575 : Reach 68575 := rs (se 1 (by rfl) ⟨51431, by rfl⟩) R102863
theorem R101371 : Reach 101371 := rs (se 1 (by rfl) ⟨76028, by rfl⟩) R152057
theorem R134153 : Reach 134153 := rs (se 2 (by rfl) ⟨50307, by rfl⟩) R100615
theorem R134207 : Reach 134207 := rs (se 1 (by rfl) ⟨100655, by rfl⟩) R201311
theorem R69223 : Reach 69223 := rs (se 1 (by rfl) ⟨51917, by rfl⟩) R103835
theorem R69439 : Reach 69439 := rs (se 1 (by rfl) ⟨52079, by rfl⟩) R104159
theorem R135035 : Reach 135035 := rs (se 1 (by rfl) ⟨101276, by rfl⟩) R202553
theorem R135143 : Reach 135143 := rs (se 1 (by rfl) ⟨101357, by rfl⟩) R202715
theorem R69727 : Reach 69727 := rs (se 1 (by rfl) ⟨52295, by rfl⟩) R104591
theorem R135323 : Reach 135323 := rs (se 1 (by rfl) ⟨101492, by rfl⟩) R202985
theorem R528707 : Reach 528707 := rs (se 1 (by rfl) ⟨396530, by rfl⟩) R793061
theorem R135521 : Reach 135521 := rs (se 2 (by rfl) ⟨50820, by rfl⟩) R101641
theorem R201079 : Reach 201079 := rs (se 1 (by rfl) ⟨150809, by rfl⟩) R301619
theorem R758159 : Reach 758159 := rs (se 1 (by rfl) ⟨568619, by rfl⟩) R1137239
theorem R135611 : Reach 135611 := rs (se 1 (by rfl) ⟨101708, by rfl⟩) R203417
theorem R201149 : Reach 201149 := rs (se 3 (by rfl) ⟨37715, by rfl⟩) R75431
theorem R168605 : Reach 168605 := rs (se 3 (by rfl) ⟨31613, by rfl⟩) R63227
theorem R1020599 : Reach 1020599 := rs (se 1 (by rfl) ⟨765449, by rfl⟩) R1530899
theorem R627941 : Reach 627941 := rs (se 4 (by rfl) ⟨58869, by rfl⟩) R117739
theorem R169391 : Reach 169391 := rs (se 1 (by rfl) ⟨127043, by rfl⟩) R254087
theorem R169447 : Reach 169447 := rs (se 1 (by rfl) ⟨127085, by rfl⟩) R254171
theorem R235163 : Reach 235163 := rs (se 1 (by rfl) ⟨176372, by rfl⟩) R352745
theorem R136871 : Reach 136871 := rs (se 1 (by rfl) ⟨102653, by rfl⟩) R205307
theorem R137051 : Reach 137051 := rs (se 1 (by rfl) ⟨102788, by rfl⟩) R205577
theorem R1513363 : Reach 1513363 := rs (se 1 (by rfl) ⟨1135022, by rfl⟩) R2270045
theorem R300995 : Reach 300995 := rs (se 1 (by rfl) ⟨225746, by rfl⟩) R451493
theorem R202877 : Reach 202877 := rs (se 3 (by rfl) ⟨38039, by rfl⟩) R76079
theorem R203039 : Reach 203039 := rs (se 1 (by rfl) ⟨152279, by rfl⟩) R304559
theorem R137555 : Reach 137555 := rs (se 1 (by rfl) ⟨103166, by rfl⟩) R206333
theorem R203147 : Reach 203147 := rs (se 1 (by rfl) ⟨152360, by rfl⟩) R304721
theorem R104935 : Reach 104935 := rs (se 1 (by rfl) ⟨78701, by rfl⟩) R157403
theorem R138041 : Reach 138041 := rs (se 2 (by rfl) ⟨51765, by rfl⟩) R103531
theorem R531305 : Reach 531305 := rs (se 2 (by rfl) ⟨199239, by rfl⟩) R398479
theorem R138095 : Reach 138095 := rs (se 1 (by rfl) ⟨103571, by rfl⟩) R207143
theorem R236591 : Reach 236591 := rs (se 1 (by rfl) ⟨177443, by rfl⟩) R354887
theorem R334919 : Reach 334919 := rs (se 1 (by rfl) ⟨251189, by rfl⟩) R502379
theorem R105799 : Reach 105799 := rs (se 1 (by rfl) ⟨79349, by rfl⟩) R158699
theorem R138671 : Reach 138671 := rs (se 1 (by rfl) ⟨104003, by rfl⟩) R208007
theorem R105961 : Reach 105961 := rs (se 2 (by rfl) ⟨39735, by rfl⟩) R79471
theorem R138743 : Reach 138743 := rs (se 1 (by rfl) ⟨104057, by rfl⟩) R208115
theorem R237275 : Reach 237275 := rs (se 1 (by rfl) ⟨177956, by rfl⟩) R355913
theorem R237289 : Reach 237289 := rs (se 2 (by rfl) ⟨88983, by rfl⟩) R177967
theorem R73639 : Reach 73639 := rs (se 1 (by rfl) ⟨55229, by rfl⟩) R110459
theorem R204767 : Reach 204767 := rs (se 1 (by rfl) ⟨153575, by rfl⟩) R307151
theorem R204929 : Reach 204929 := rs (se 2 (by rfl) ⟨76848, by rfl⟩) R153697
theorem R2072753 : Reach 2072753 := rs (se 2 (by rfl) ⟨777282, by rfl⟩) R1554565
theorem R237775 : Reach 237775 := rs (se 1 (by rfl) ⟨178331, by rfl⟩) R356663
theorem R17375633 : Reach 17375633 := rs (se 2 (by rfl) ⟨6515862, by rfl⟩) R13031725
theorem R139769 : Reach 139769 := rs (se 2 (by rfl) ⟨52413, by rfl⟩) R104827
theorem R139859 : Reach 139859 := rs (se 1 (by rfl) ⟨104894, by rfl⟩) R209789
theorem R172763 : Reach 172763 := rs (se 1 (by rfl) ⟨129572, by rfl⟩) R259145
theorem R140039 : Reach 140039 := rs (se 1 (by rfl) ⟨105029, by rfl⟩) R210059
theorem R336683 : Reach 336683 := rs (se 1 (by rfl) ⟨252512, by rfl⟩) R505025
theorem R140129 : Reach 140129 := rs (se 2 (by rfl) ⟨52548, by rfl⟩) R105097
theorem R205739 : Reach 205739 := rs (se 1 (by rfl) ⟨154304, by rfl⟩) R308609
theorem R336953 : Reach 336953 := rs (se 2 (by rfl) ⟨126357, by rfl⟩) R252715
theorem R206279 : Reach 206279 := rs (se 1 (by rfl) ⟨154709, by rfl⟩) R309419
theorem R468503 : Reach 468503 := rs (se 1 (by rfl) ⟨351377, by rfl⟩) R702755
theorem R239219 : Reach 239219 := rs (se 1 (by rfl) ⟨179414, by rfl⟩) R358829
theorem R599717 : Reach 599717 := rs (se 4 (by rfl) ⟨56223, by rfl⟩) R112447
theorem R141119 : Reach 141119 := rs (se 1 (by rfl) ⟨105839, by rfl⟩) R211679
theorem R75755 : Reach 75755 := rs (se 1 (by rfl) ⟨56816, by rfl⟩) R113633
theorem R141299 : Reach 141299 := rs (se 1 (by rfl) ⟨105974, by rfl⟩) R211949
theorem R764153 : Reach 764153 := rs (se 2 (by rfl) ⟨286557, by rfl⟩) R573115
theorem R141623 : Reach 141623 := rs (se 1 (by rfl) ⟨106217, by rfl⟩) R212435
theorem R15935849 : Reach 15935849 := rs (se 2 (by rfl) ⟨5975943, by rfl⟩) R11951887
theorem R141803 : Reach 141803 := rs (se 1 (by rfl) ⟨106352, by rfl⟩) R212705
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R142409 : Reach 142409 := rs (se 2 (by rfl) ⟨53403, by rfl⟩) R106807
theorem R765245 : Reach 765245 := rs (se 3 (by rfl) ⟨143483, by rfl⟩) R286967
theorem R208385 : Reach 208385 := rs (se 2 (by rfl) ⟨78144, by rfl⟩) R156289
theorem R405485 : Reach 405485 := rs (se 3 (by rfl) ⟨76028, by rfl⟩) R152057
theorem R209195 : Reach 209195 := rs (se 1 (by rfl) ⟨156896, by rfl⟩) R313793
theorem R209465 : Reach 209465 := rs (se 2 (by rfl) ⟨78549, by rfl⟩) R157099
theorem R78889 : Reach 78889 := rs (se 2 (by rfl) ⟨29583, by rfl⟩) R59167
theorem R144649 : Reach 144649 := rs (se 2 (by rfl) ⟨54243, by rfl⟩) R108487
theorem R210575 : Reach 210575 := rs (se 1 (by rfl) ⟨157931, by rfl⟩) R315863
theorem R309257 : Reach 309257 := rs (se 2 (by rfl) ⟨115971, by rfl⟩) R231943
theorem R604331 : Reach 604331 := rs (se 1 (by rfl) ⟨453248, by rfl⟩) R906497
theorem R243911 : Reach 243911 := rs (se 1 (by rfl) ⟨182933, by rfl⟩) R365867
theorem R506087 : Reach 506087 := rs (se 1 (by rfl) ⟨379565, by rfl⟩) R759131
theorem R211193 : Reach 211193 := rs (se 2 (by rfl) ⟨79197, by rfl⟩) R158395
theorem R211463 : Reach 211463 := rs (se 1 (by rfl) ⟨158597, by rfl⟩) R317195
theorem R408185 : Reach 408185 := rs (se 2 (by rfl) ⟨153069, by rfl⟩) R306139
theorem R277225 : Reach 277225 := rs (se 2 (by rfl) ⟨103959, by rfl⟩) R207919
theorem R179425 : Reach 179425 := rs (se 2 (by rfl) ⟨67284, by rfl⟩) R134569
theorem R146663 : Reach 146663 := rs (se 1 (by rfl) ⟨109997, by rfl⟩) R219995
theorem R212543 : Reach 212543 := rs (se 1 (by rfl) ⟨159407, by rfl⟩) R318815
theorem R343997 : Reach 343997 := rs (se 3 (by rfl) ⟨64499, by rfl⟩) R128999
theorem R671915 : Reach 671915 := rs (se 1 (by rfl) ⟨503936, by rfl⟩) R1007873
theorem R475307 : Reach 475307 := rs (se 1 (by rfl) ⟨356480, by rfl⟩) R712961
theorem R1851569 : Reach 1851569 := rs (se 2 (by rfl) ⟨694338, by rfl⟩) R1388677
theorem R147691 : Reach 147691 := rs (se 1 (by rfl) ⟨110768, by rfl⟩) R221537
theorem R180473 : Reach 180473 := rs (se 2 (by rfl) ⟨67677, by rfl⟩) R135355
theorem R377081 : Reach 377081 := rs (se 2 (by rfl) ⟨141405, by rfl⟩) R282811
theorem R508477 : Reach 508477 := rs (se 3 (by rfl) ⟨95339, by rfl⟩) R190679
theorem R2638615 : Reach 2638615 := rs (se 1 (by rfl) ⟨1978961, by rfl⟩) R3957923
theorem R508751 : Reach 508751 := rs (se 1 (by rfl) ⟨381563, by rfl⟩) R763127
theorem R574373 : Reach 574373 := rs (se 4 (by rfl) ⟨53847, by rfl⟩) R107695
theorem R508837 : Reach 508837 := rs (se 4 (by rfl) ⟨47703, by rfl⟩) R95407
theorem R246779 : Reach 246779 := rs (se 1 (by rfl) ⟨185084, by rfl⟩) R370169
theorem R116015 : Reach 116015 := rs (se 1 (by rfl) ⟨87011, by rfl⟩) R174023
theorem R214429 : Reach 214429 := rs (se 3 (by rfl) ⟨40205, by rfl⟩) R80411
theorem R116329 : Reach 116329 := rs (se 2 (by rfl) ⟨43623, by rfl⟩) R87247
theorem R345707 : Reach 345707 := rs (se 1 (by rfl) ⟨259280, by rfl⟩) R518561
theorem R247673 : Reach 247673 := rs (se 2 (by rfl) ⟨92877, by rfl⟩) R185755
theorem R116711 : Reach 116711 := rs (se 1 (by rfl) ⟨87533, by rfl⟩) R175067
theorem R575687 : Reach 575687 := rs (se 1 (by rfl) ⟨431765, by rfl⟩) R863531
theorem R116959 : Reach 116959 := rs (se 1 (by rfl) ⟨87719, by rfl⟩) R175439
theorem R969083 : Reach 969083 := rs (se 1 (by rfl) ⟨726812, by rfl⟩) R1453625
theorem R117119 : Reach 117119 := rs (se 1 (by rfl) ⟨87839, by rfl⟩) R175679
theorem R642505 : Reach 642505 := rs (se 2 (by rfl) ⟨240939, by rfl⟩) R481879
theorem R1035767 : Reach 1035767 := rs (se 1 (by rfl) ⟨776825, by rfl⟩) R1553651
theorem R118759 : Reach 118759 := rs (se 1 (by rfl) ⟨89069, by rfl⟩) R178139
theorem R151591 : Reach 151591 := rs (se 1 (by rfl) ⟨113693, by rfl⟩) R227387
theorem R348371 : Reach 348371 := rs (se 1 (by rfl) ⟨261278, by rfl⟩) R522557
theorem R1398169 : Reach 1398169 := rs (se 2 (by rfl) ⟨524313, by rfl⟩) R1048627
theorem R186143 : Reach 186143 := rs (se 1 (by rfl) ⟨139607, by rfl⟩) R279215
theorem R350171 : Reach 350171 := rs (se 1 (by rfl) ⟨262628, by rfl⟩) R525257
theorem R88943 : Reach 88943 := rs (se 1 (by rfl) ⟨66707, by rfl⟩) R133415
theorem R88955 : Reach 88955 := rs (se 1 (by rfl) ⟨66716, by rfl⟩) R133433
theorem R1006769 : Reach 1006769 := rs (se 2 (by rfl) ⟨377538, by rfl⟩) R755077
theorem R253265 : Reach 253265 := rs (se 2 (by rfl) ⟨94974, by rfl⟩) R189949
theorem R89819 : Reach 89819 := rs (se 1 (by rfl) ⟨67364, by rfl⟩) R134729
theorem R90089 : Reach 90089 := rs (se 2 (by rfl) ⟨33783, by rfl⟩) R67567
theorem R385049 : Reach 385049 := rs (se 2 (by rfl) ⟨144393, by rfl⟩) R288787
theorem R90791 : Reach 90791 := rs (se 1 (by rfl) ⟨68093, by rfl⟩) R136187
theorem R90911 : Reach 90911 := rs (se 1 (by rfl) ⟨68183, by rfl⟩) R136367
theorem R90935 : Reach 90935 := rs (se 1 (by rfl) ⟨68201, by rfl⟩) R136403
theorem R91115 : Reach 91115 := rs (se 1 (by rfl) ⟨68336, by rfl⟩) R136673
theorem R353819 : Reach 353819 := rs (se 1 (by rfl) ⟨265364, by rfl⟩) R530729
theorem R157211 : Reach 157211 := rs (se 1 (by rfl) ⟨117908, by rfl⟩) R235817
theorem R2713171 : Reach 2713171 := rs (se 1 (by rfl) ⟨2034878, by rfl⟩) R4069757
theorem R649079 : Reach 649079 := rs (se 1 (by rfl) ⟨486809, by rfl⟩) R973619
theorem R59327 : Reach 59327 := rs (se 1 (by rfl) ⟨44495, by rfl⟩) R88991
theorem R223195 : Reach 223195 := rs (se 1 (by rfl) ⟨167396, by rfl⟩) R334793
theorem R59359 : Reach 59359 := rs (se 1 (by rfl) ⟨44519, by rfl⟩) R89039
theorem R59419 : Reach 59419 := rs (se 1 (by rfl) ⟨44564, by rfl⟩) R89129
theorem R59423 : Reach 59423 := rs (se 1 (by rfl) ⟨44567, by rfl⟩) R89135
theorem R59439 : Reach 59439 := rs (se 1 (by rfl) ⟨44579, by rfl⟩) R89159
theorem R92207 : Reach 92207 := rs (se 1 (by rfl) ⟨69155, by rfl⟩) R138311
theorem R59615 : Reach 59615 := rs (se 1 (by rfl) ⟨44711, by rfl⟩) R89423
theorem R59675 : Reach 59675 := rs (se 1 (by rfl) ⟨44756, by rfl⟩) R89513
theorem R92471 : Reach 92471 := rs (se 1 (by rfl) ⟨69353, by rfl⟩) R138707
theorem R59775 : Reach 59775 := rs (se 1 (by rfl) ⟨44831, by rfl⟩) R89663
theorem R92651 : Reach 92651 := rs (se 1 (by rfl) ⟨69488, by rfl⟩) R138977
theorem R59951 : Reach 59951 := rs (se 1 (by rfl) ⟨44963, by rfl⟩) R89927
theorem R60007 : Reach 60007 := rs (se 1 (by rfl) ⟨45005, by rfl⟩) R90011
theorem R387919 : Reach 387919 := rs (se 1 (by rfl) ⟨290939, by rfl⟩) R581879
theorem R60383 : Reach 60383 := rs (se 1 (by rfl) ⟨45287, by rfl⟩) R90575
theorem R60411 : Reach 60411 := rs (se 1 (by rfl) ⟨45308, by rfl⟩) R90617
theorem R60479 : Reach 60479 := rs (se 1 (by rfl) ⟨45359, by rfl⟩) R90719
theorem R93353 : Reach 93353 := rs (se 2 (by rfl) ⟨35007, by rfl⟩) R70015
theorem R60799 : Reach 60799 := rs (se 1 (by rfl) ⟨45599, by rfl⟩) R91199
theorem R60827 : Reach 60827 := rs (se 1 (by rfl) ⟨45620, by rfl⟩) R91241
theorem R60895 : Reach 60895 := rs (se 1 (by rfl) ⟨45671, by rfl⟩) R91343
theorem R93767 : Reach 93767 := rs (se 1 (by rfl) ⟨70325, by rfl⟩) R140651
theorem R61031 : Reach 61031 := rs (se 1 (by rfl) ⟨45773, by rfl⟩) R91547
theorem R290461 : Reach 290461 := rs (se 3 (by rfl) ⟨54461, by rfl⟩) R108923
theorem R290479 : Reach 290479 := rs (se 1 (by rfl) ⟨217859, by rfl⟩) R435719
theorem R61179 : Reach 61179 := rs (se 1 (by rfl) ⟨45884, by rfl⟩) R91769
theorem R93947 : Reach 93947 := rs (se 1 (by rfl) ⟨70460, by rfl⟩) R140921
theorem R61247 : Reach 61247 := rs (se 1 (by rfl) ⟨45935, by rfl⟩) R91871
theorem R61311 : Reach 61311 := rs (se 1 (by rfl) ⟨45983, by rfl⟩) R91967
theorem R61423 : Reach 61423 := rs (se 1 (by rfl) ⟨46067, by rfl⟩) R92135
theorem R356345 : Reach 356345 := rs (se 2 (by rfl) ⟨133629, by rfl⟩) R267259
theorem R61435 : Reach 61435 := rs (se 1 (by rfl) ⟨46076, by rfl⟩) R92153
theorem R61503 : Reach 61503 := rs (se 1 (by rfl) ⟨46127, by rfl⟩) R92255
theorem R61543 : Reach 61543 := rs (se 1 (by rfl) ⟨46157, by rfl⟩) R92315
theorem R61567 : Reach 61567 := rs (se 1 (by rfl) ⟨46175, by rfl⟩) R92351
theorem R61595 : Reach 61595 := rs (se 1 (by rfl) ⟨46196, by rfl⟩) R92393
theorem R61799 : Reach 61799 := rs (se 1 (by rfl) ⟨46349, by rfl⟩) R92699
theorem R61851 : Reach 61851 := rs (se 1 (by rfl) ⟨46388, by rfl⟩) R92777
theorem R94619 : Reach 94619 := rs (se 1 (by rfl) ⟨70964, by rfl⟩) R141929
theorem R258511 : Reach 258511 := rs (se 1 (by rfl) ⟨193883, by rfl⟩) R387767
theorem R62203 : Reach 62203 := rs (se 1 (by rfl) ⟨46652, by rfl⟩) R93305
theorem R62271 : Reach 62271 := rs (se 1 (by rfl) ⟨46703, by rfl⟩) R93407
theorem R62299 : Reach 62299 := rs (se 1 (by rfl) ⟨46724, by rfl⟩) R93449
theorem R62367 : Reach 62367 := rs (se 1 (by rfl) ⟨46775, by rfl⟩) R93551
theorem R62447 : Reach 62447 := rs (se 1 (by rfl) ⟨46835, by rfl⟩) R93671
theorem R62535 : Reach 62535 := rs (se 1 (by rfl) ⟨46901, by rfl⟩) R93803
theorem R62559 : Reach 62559 := rs (se 1 (by rfl) ⟨46919, by rfl⟩) R93839
theorem R849035 : Reach 849035 := rs (se 1 (by rfl) ⟨636776, by rfl⟩) R1273553
theorem R62619 : Reach 62619 := rs (se 1 (by rfl) ⟨46964, by rfl⟩) R93929
theorem R62715 : Reach 62715 := rs (se 1 (by rfl) ⟨47036, by rfl⟩) R94073
theorem R62783 : Reach 62783 := rs (se 1 (by rfl) ⟨47087, by rfl⟩) R94175
theorem R357803 : Reach 357803 := rs (se 1 (by rfl) ⟨268352, by rfl⟩) R536705
theorem R62951 : Reach 62951 := rs (se 1 (by rfl) ⟨47213, by rfl⟩) R94427
theorem R62959 : Reach 62959 := rs (se 1 (by rfl) ⟨47219, by rfl⟩) R94439
theorem R63067 : Reach 63067 := rs (se 1 (by rfl) ⟨47300, by rfl⟩) R94601
theorem R128623 : Reach 128623 := rs (se 1 (by rfl) ⟨96467, by rfl⟩) R192935
theorem R227083 : Reach 227083 := rs (se 1 (by rfl) ⟨170312, by rfl⟩) R340625
theorem R555407 : Reach 555407 := rs (se 1 (by rfl) ⟨416555, by rfl⟩) R833111
theorem R391969 : Reach 391969 := rs (se 2 (by rfl) ⟨146988, by rfl⟩) R293977
theorem R64423 : Reach 64423 := rs (se 1 (by rfl) ⟨48317, by rfl⟩) R96635
theorem R261245 : Reach 261245 := rs (se 3 (by rfl) ⟨48983, by rfl⟩) R97967
theorem R359869 : Reach 359869 := rs (se 3 (by rfl) ⟨67475, by rfl⟩) R134951
theorem R228815 : Reach 228815 := rs (se 1 (by rfl) ⟨171611, by rfl⟩) R343223
theorem R65243 : Reach 65243 := rs (se 1 (by rfl) ⟨48932, by rfl⟩) R97865
theorem R163559 : Reach 163559 := rs (se 1 (by rfl) ⟨122669, by rfl⟩) R245339
theorem R98057 : Reach 98057 := rs (se 2 (by rfl) ⟨36771, by rfl⟩) R73543
theorem R131015 : Reach 131015 := rs (se 1 (by rfl) ⟨98261, by rfl⟩) R196523
theorem R196921 : Reach 196921 := rs (se 2 (by rfl) ⟨73845, by rfl⟩) R147691
theorem R164519 : Reach 164519 := rs (se 1 (by rfl) ⟨123389, by rfl⟩) R246779
theorem R131903 : Reach 131903 := rs (se 1 (by rfl) ⟨98927, by rfl⟩) R197855
theorem R66631 : Reach 66631 := rs (se 1 (by rfl) ⟨49973, by rfl⟩) R99947
theorem R230471 : Reach 230471 := rs (se 1 (by rfl) ⟨172853, by rfl⟩) R345707
theorem R66811 : Reach 66811 := rs (se 1 (by rfl) ⟨50108, by rfl⟩) R100217
theorem R165115 : Reach 165115 := rs (se 1 (by rfl) ⟨123836, by rfl⟩) R247673
theorem R11142947 : Reach 11142947 := rs (se 1 (by rfl) ⟨8357210, by rfl⟩) R16714421
theorem R133055 : Reach 133055 := rs (se 1 (by rfl) ⟨99791, by rfl⟩) R199583
theorem R297593 : Reach 297593 := rs (se 2 (by rfl) ⟨111597, by rfl⟩) R223195
theorem R232247 : Reach 232247 := rs (se 1 (by rfl) ⟨174185, by rfl⟩) R348371
theorem R134099 : Reach 134099 := rs (se 1 (by rfl) ⟨100574, by rfl⟩) R201149
theorem R134369 : Reach 134369 := rs (se 2 (by rfl) ⟨50388, by rfl⟩) R100777
theorem R1478533 : Reach 1478533 := rs (se 4 (by rfl) ⟨138612, by rfl⟩) R277225
theorem R200663 : Reach 200663 := rs (se 1 (by rfl) ⟨150497, by rfl⟩) R300995
theorem R233447 : Reach 233447 := rs (se 1 (by rfl) ⟨175085, by rfl⟩) R350171
theorem R135161 : Reach 135161 := rs (se 2 (by rfl) ⟨50685, by rfl⟩) R101371
theorem R135251 : Reach 135251 := rs (se 1 (by rfl) ⟨101438, by rfl⟩) R202877
theorem R135359 : Reach 135359 := rs (se 1 (by rfl) ⟨101519, by rfl⟩) R203039
theorem R135431 : Reach 135431 := rs (se 1 (by rfl) ⟨101573, by rfl⟩) R203147
theorem R856673 : Reach 856673 := rs (se 2 (by rfl) ⟨321252, by rfl⟩) R642505
theorem R496381 : Reach 496381 := rs (se 3 (by rfl) ⟨93071, by rfl⟩) R186143
theorem R202013 : Reach 202013 := rs (se 3 (by rfl) ⟨37877, by rfl⟩) R75755
theorem R136511 : Reach 136511 := rs (se 1 (by rfl) ⟨102383, by rfl⟩) R204767
theorem R202121 : Reach 202121 := rs (se 2 (by rfl) ⟨75795, by rfl⟩) R151591
theorem R136619 : Reach 136619 := rs (se 1 (by rfl) ⟨102464, by rfl⟩) R204929
theorem R1381835 : Reach 1381835 := rs (se 1 (by rfl) ⟨1036376, by rfl⟩) R2072753
theorem R268105 : Reach 268105 := rs (se 2 (by rfl) ⟨100539, by rfl⟩) R201079
theorem R137159 : Reach 137159 := rs (se 1 (by rfl) ⟨102869, by rfl⟩) R205739
theorem R137519 : Reach 137519 := rs (se 1 (by rfl) ⟨103139, by rfl⟩) R206279
theorem R235879 : Reach 235879 := rs (se 1 (by rfl) ⟨176909, by rfl⟩) R353819
theorem R104807 : Reach 104807 := rs (se 1 (by rfl) ⟨78605, by rfl⟩) R157211
theorem R399811 : Reach 399811 := rs (se 1 (by rfl) ⟨299858, by rfl⟩) R599717
theorem R432719 : Reach 432719 := rs (se 1 (by rfl) ⟨324539, by rfl⟩) R649079
theorem R105185 : Reach 105185 := rs (se 2 (by rfl) ⟨39444, by rfl⟩) R78889
theorem R10623899 : Reach 10623899 := rs (se 1 (by rfl) ⟨7967924, by rfl⟩) R15935849
theorem R171497 : Reach 171497 := rs (se 2 (by rfl) ⟨64311, by rfl⟩) R128623
theorem R138923 : Reach 138923 := rs (se 1 (by rfl) ⟨104192, by rfl⟩) R208385
theorem R302777 : Reach 302777 := rs (se 2 (by rfl) ⟨113541, by rfl⟩) R227083
theorem R270323 : Reach 270323 := rs (se 1 (by rfl) ⟨202742, by rfl⟩) R405485
theorem R237563 : Reach 237563 := rs (se 1 (by rfl) ⟨178172, by rfl⟩) R356345
theorem R139463 : Reach 139463 := rs (se 1 (by rfl) ⟨104597, by rfl⟩) R209195
theorem R139643 : Reach 139643 := rs (se 1 (by rfl) ⟨104732, by rfl⟩) R209465
theorem R139913 : Reach 139913 := rs (se 2 (by rfl) ⟨52467, by rfl⟩) R104935
theorem R566023 : Reach 566023 := rs (se 1 (by rfl) ⟨424517, by rfl⟩) R849035
theorem R2040653 : Reach 2040653 := rs (se 3 (by rfl) ⟨382622, by rfl⟩) R765245
theorem R238535 : Reach 238535 := rs (se 1 (by rfl) ⟨178901, by rfl⟩) R357803
theorem R140383 : Reach 140383 := rs (se 1 (by rfl) ⟨105287, by rfl⟩) R210575
theorem R2762045 : Reach 2762045 := rs (se 3 (by rfl) ⟨517883, by rfl⟩) R1035767
theorem R206171 : Reach 206171 := rs (se 1 (by rfl) ⟨154628, by rfl⟩) R309257
theorem R402887 : Reach 402887 := rs (se 1 (by rfl) ⟨302165, by rfl⟩) R604331
theorem R337391 : Reach 337391 := rs (se 1 (by rfl) ⟨253043, by rfl⟩) R506087
theorem R140795 : Reach 140795 := rs (se 1 (by rfl) ⟨105596, by rfl⟩) R211193
theorem R370271 : Reach 370271 := rs (se 1 (by rfl) ⟨277703, by rfl⟩) R555407
theorem R239233 : Reach 239233 := rs (se 2 (by rfl) ⟨89712, by rfl⟩) R179425
theorem R140975 : Reach 140975 := rs (se 1 (by rfl) ⟨105731, by rfl⟩) R211463
theorem R272123 : Reach 272123 := rs (se 1 (by rfl) ⟨204092, by rfl⟩) R408185
theorem R141065 : Reach 141065 := rs (se 2 (by rfl) ⟨52899, by rfl⟩) R105799
theorem R173981 : Reach 173981 := rs (se 3 (by rfl) ⟨32621, by rfl⟩) R65243
theorem R141281 : Reach 141281 := rs (se 2 (by rfl) ⟨52980, by rfl⟩) R105961
theorem R174163 : Reach 174163 := rs (se 1 (by rfl) ⟨130622, by rfl⟩) R261245
theorem R141695 : Reach 141695 := rs (se 1 (by rfl) ⟨106271, by rfl⟩) R212543
theorem R109039 : Reach 109039 := rs (se 1 (by rfl) ⟨81779, by rfl⟩) R163559
theorem R339167 : Reach 339167 := rs (se 1 (by rfl) ⟨254375, by rfl⟩) R508751
theorem R306665 : Reach 306665 := rs (se 2 (by rfl) ⟨114999, by rfl⟩) R229999
theorem R3518153 : Reach 3518153 := rs (se 2 (by rfl) ⟨1319307, by rfl⟩) R2638615
theorem R77807 : Reach 77807 := rs (se 1 (by rfl) ⟨58355, by rfl⟩) R116711
theorem R176383 : Reach 176383 := rs (se 1 (by rfl) ⟨132287, by rfl⟩) R264575
theorem R78079 : Reach 78079 := rs (se 1 (by rfl) ⟨58559, by rfl⟩) R117119
theorem R307475 : Reach 307475 := rs (se 1 (by rfl) ⟨230606, by rfl⟩) R461213
theorem R3617561 : Reach 3617561 := rs (se 2 (by rfl) ⟨1356585, by rfl⟩) R2713171
theorem R897821 : Reach 897821 := rs (se 3 (by rfl) ⟨168341, by rfl⟩) R336683
theorem R505439 : Reach 505439 := rs (se 1 (by rfl) ⟨379079, by rfl⟩) R758159
theorem R112403 : Reach 112403 := rs (se 1 (by rfl) ⟨84302, by rfl⟩) R168605
theorem R112927 : Reach 112927 := rs (se 1 (by rfl) ⟨84695, by rfl⟩) R169391
theorem R671179 : Reach 671179 := rs (se 1 (by rfl) ⟨503384, by rfl⟩) R1006769
theorem R11583755 : Reach 11583755 := rs (se 1 (by rfl) ⟨8687816, by rfl⟩) R17375633
theorem R115175 : Reach 115175 := rs (se 1 (by rfl) ⟨86381, by rfl⟩) R172763
theorem R344681 : Reach 344681 := rs (se 2 (by rfl) ⟨129255, by rfl⟩) R258511
theorem R312335 : Reach 312335 := rs (se 1 (by rfl) ⟨234251, by rfl⟩) R468503
theorem R771461 : Reach 771461 := rs (se 4 (by rfl) ⟨72324, by rfl⟩) R144649
theorem R509435 : Reach 509435 := rs (se 1 (by rfl) ⟨382076, by rfl⟩) R764153
theorem R2017817 : Reach 2017817 := rs (se 2 (by rfl) ⟨756681, by rfl⟩) R1513363
theorem R675373 : Reach 675373 := rs (se 3 (by rfl) ⟨126632, by rfl⟩) R253265
theorem R85897 : Reach 85897 := rs (se 2 (by rfl) ⟨32211, by rfl⟩) R64423
theorem R479825 : Reach 479825 := rs (se 2 (by rfl) ⟨179934, by rfl⟩) R359869
theorem R152543 : Reach 152543 := rs (se 1 (by rfl) ⟨114407, by rfl⟩) R228815
theorem R316385 : Reach 316385 := rs (se 2 (by rfl) ⟨118644, by rfl⟩) R237289
theorem R349373 : Reach 349373 := rs (se 3 (by rfl) ⟨65507, by rfl⟩) R131015
theorem R447943 : Reach 447943 := rs (se 1 (by rfl) ⟨335957, by rfl⟩) R671915
theorem R316871 : Reach 316871 := rs (se 1 (by rfl) ⟨237653, by rfl⟩) R475307
theorem R1234379 : Reach 1234379 := rs (se 1 (by rfl) ⟨925784, by rfl⟩) R1851569
theorem R251387 : Reach 251387 := rs (se 1 (by rfl) ⟨188540, by rfl⟩) R377081
theorem R87583 : Reach 87583 := rs (se 1 (by rfl) ⟨65687, by rfl⟩) R131375
theorem R317033 : Reach 317033 := rs (se 2 (by rfl) ⟨118887, by rfl⟩) R237775
theorem R382915 : Reach 382915 := rs (se 1 (by rfl) ⟨287186, by rfl⟩) R574373
theorem R481261 : Reach 481261 := rs (se 3 (by rfl) ⟨90236, by rfl⟩) R180473
theorem R677969 : Reach 677969 := rs (se 2 (by rfl) ⟨254238, by rfl⟩) R508477
theorem R416111 : Reach 416111 := rs (se 1 (by rfl) ⟨312083, by rfl⟩) R624167
theorem R612839 : Reach 612839 := rs (se 1 (by rfl) ⟨459629, by rfl⟩) R919259
theorem R678449 : Reach 678449 := rs (se 2 (by rfl) ⟨254418, by rfl⟩) R508837
theorem R88871 : Reach 88871 := rs (se 1 (by rfl) ⟨66653, by rfl⟩) R133307
theorem R383791 : Reach 383791 := rs (se 1 (by rfl) ⟨287843, by rfl⟩) R575687
theorem R88895 : Reach 88895 := rs (se 1 (by rfl) ⟨66671, by rfl⟩) R133343
theorem R646055 : Reach 646055 := rs (se 1 (by rfl) ⟨484541, by rfl⟩) R969083
theorem R89195 : Reach 89195 := rs (se 1 (by rfl) ⟨66896, by rfl⟩) R133793
theorem R285905 : Reach 285905 := rs (se 2 (by rfl) ⟨107214, by rfl⟩) R214429
theorem R89339 : Reach 89339 := rs (se 1 (by rfl) ⟨67004, by rfl⟩) R134009
theorem R89371 : Reach 89371 := rs (se 1 (by rfl) ⟨67028, by rfl⟩) R134057
theorem R89435 : Reach 89435 := rs (se 1 (by rfl) ⟨67076, by rfl⟩) R134153
theorem R89465 : Reach 89465 := rs (se 2 (by rfl) ⟨33549, by rfl⟩) R67099
theorem R89471 : Reach 89471 := rs (se 1 (by rfl) ⟨67103, by rfl⟩) R134207
theorem R155105 : Reach 155105 := rs (se 2 (by rfl) ⟨58164, by rfl⟩) R116329
theorem R90023 : Reach 90023 := rs (se 1 (by rfl) ⟨67517, by rfl⟩) R135035
theorem R90095 : Reach 90095 := rs (se 1 (by rfl) ⟨67571, by rfl⟩) R135143
theorem R352289 : Reach 352289 := rs (se 2 (by rfl) ⟨132108, by rfl⟩) R264217
theorem R90215 : Reach 90215 := rs (se 1 (by rfl) ⟨67661, by rfl⟩) R135323
theorem R352471 : Reach 352471 := rs (se 1 (by rfl) ⟨264353, by rfl⟩) R528707
theorem R90347 : Reach 90347 := rs (se 1 (by rfl) ⟨67760, by rfl⟩) R135521
theorem R90407 : Reach 90407 := rs (se 1 (by rfl) ⟨67805, by rfl⟩) R135611
theorem R155945 : Reach 155945 := rs (se 2 (by rfl) ⟨58479, by rfl⟩) R116959
theorem R680399 : Reach 680399 := rs (se 1 (by rfl) ⟨510299, by rfl⟩) R1020599
theorem R1237493 : Reach 1237493 := rs (se 5 (by rfl) ⟨58007, by rfl⟩) R116015
theorem R90857 : Reach 90857 := rs (se 2 (by rfl) ⟨34071, by rfl⟩) R68143
theorem R418627 : Reach 418627 := rs (se 1 (by rfl) ⟨313970, by rfl⟩) R627941
theorem R156775 : Reach 156775 := rs (se 1 (by rfl) ⟨117581, by rfl⟩) R235163
theorem R517225 : Reach 517225 := rs (se 2 (by rfl) ⟨193959, by rfl⟩) R387919
theorem R91247 : Reach 91247 := rs (se 1 (by rfl) ⟨68435, by rfl⟩) R136871
theorem R91367 : Reach 91367 := rs (se 1 (by rfl) ⟨68525, by rfl⟩) R137051
theorem R91433 : Reach 91433 := rs (se 2 (by rfl) ⟨34287, by rfl⟩) R68575
theorem R1402181 : Reach 1402181 := rs (se 4 (by rfl) ⟨131454, by rfl⟩) R262909
theorem R91703 : Reach 91703 := rs (se 1 (by rfl) ⟨68777, by rfl⟩) R137555
theorem R92027 : Reach 92027 := rs (se 1 (by rfl) ⟨69020, by rfl⟩) R138041
theorem R354203 : Reach 354203 := rs (se 1 (by rfl) ⟨265652, by rfl⟩) R531305
theorem R59295 : Reach 59295 := rs (se 1 (by rfl) ⟨44471, by rfl⟩) R88943
theorem R92063 : Reach 92063 := rs (se 1 (by rfl) ⟨69047, by rfl⟩) R138095
theorem R59303 : Reach 59303 := rs (se 1 (by rfl) ⟨44477, by rfl⟩) R88955
theorem R157727 : Reach 157727 := rs (se 1 (by rfl) ⟨118295, by rfl⟩) R236591
theorem R223279 : Reach 223279 := rs (se 1 (by rfl) ⟨167459, by rfl⟩) R334919
theorem R92297 : Reach 92297 := rs (se 2 (by rfl) ⟨34611, by rfl⟩) R69223
theorem R387281 : Reach 387281 := rs (se 2 (by rfl) ⟨145230, by rfl⟩) R290461
theorem R387305 : Reach 387305 := rs (se 2 (by rfl) ⟨145239, by rfl⟩) R290479
theorem R92447 : Reach 92447 := rs (se 1 (by rfl) ⟨69335, by rfl⟩) R138671
theorem R92495 : Reach 92495 := rs (se 1 (by rfl) ⟨69371, by rfl⟩) R138743
theorem R92585 : Reach 92585 := rs (se 2 (by rfl) ⟨34719, by rfl⟩) R69439
theorem R59879 : Reach 59879 := rs (se 1 (by rfl) ⟨44909, by rfl⟩) R89819
theorem R158183 : Reach 158183 := rs (se 1 (by rfl) ⟨118637, by rfl⟩) R237275
theorem R158345 : Reach 158345 := rs (se 2 (by rfl) ⟨59379, by rfl⟩) R118759
theorem R60059 : Reach 60059 := rs (se 1 (by rfl) ⟨45044, by rfl⟩) R90089
theorem R256699 : Reach 256699 := rs (se 1 (by rfl) ⟨192524, by rfl⟩) R385049
theorem R92969 : Reach 92969 := rs (se 2 (by rfl) ⟨34863, by rfl⟩) R69727
theorem R93179 : Reach 93179 := rs (se 1 (by rfl) ⟨69884, by rfl⟩) R139769
theorem R93239 : Reach 93239 := rs (se 1 (by rfl) ⟨69929, by rfl⟩) R139859
theorem R60527 : Reach 60527 := rs (se 1 (by rfl) ⟨45395, by rfl⟩) R90791
theorem R93359 : Reach 93359 := rs (se 1 (by rfl) ⟨70019, by rfl⟩) R140039
theorem R650429 : Reach 650429 := rs (se 3 (by rfl) ⟨121955, by rfl⟩) R243911
theorem R60607 : Reach 60607 := rs (se 1 (by rfl) ⟨45455, by rfl⟩) R90911
theorem R60623 : Reach 60623 := rs (se 1 (by rfl) ⟨45467, by rfl⟩) R90935
theorem R93419 : Reach 93419 := rs (se 1 (by rfl) ⟨70064, by rfl⟩) R140129
theorem R60743 : Reach 60743 := rs (se 1 (by rfl) ⟨45557, by rfl⟩) R91115
theorem R224635 : Reach 224635 := rs (se 1 (by rfl) ⟨168476, by rfl⟩) R336953
theorem R159479 : Reach 159479 := rs (se 1 (by rfl) ⟨119609, by rfl⟩) R239219
theorem R94079 : Reach 94079 := rs (se 1 (by rfl) ⟨70559, by rfl⟩) R141119
theorem R94199 : Reach 94199 := rs (se 1 (by rfl) ⟨70649, by rfl⟩) R141299
theorem R61471 : Reach 61471 := rs (se 1 (by rfl) ⟨46103, by rfl⟩) R92207
theorem R61647 : Reach 61647 := rs (se 1 (by rfl) ⟨46235, by rfl⟩) R92471
theorem R94415 : Reach 94415 := rs (se 1 (by rfl) ⟨70811, by rfl⟩) R141623
theorem R61767 : Reach 61767 := rs (se 1 (by rfl) ⟨46325, by rfl⟩) R92651
theorem R94535 : Reach 94535 := rs (se 1 (by rfl) ⟨70901, by rfl⟩) R141803
theorem R1864225 : Reach 1864225 := rs (se 2 (by rfl) ⟨699084, by rfl⟩) R1398169
theorem R225929 : Reach 225929 := rs (se 2 (by rfl) ⟨84723, by rfl⟩) R169447
theorem R553661 : Reach 553661 := rs (se 3 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R94939 : Reach 94939 := rs (se 1 (by rfl) ⟨71204, by rfl⟩) R142409
theorem R62235 : Reach 62235 := rs (se 1 (by rfl) ⟨46676, by rfl⟩) R93353
theorem R62511 : Reach 62511 := rs (se 1 (by rfl) ⟨46883, by rfl⟩) R93767
theorem R62631 : Reach 62631 := rs (se 1 (by rfl) ⟨46973, by rfl⟩) R93947
theorem R63079 : Reach 63079 := rs (se 1 (by rfl) ⟨47309, by rfl⟩) R94619
theorem R522625 : Reach 522625 := rs (se 2 (by rfl) ⟨195984, by rfl⟩) R391969
theorem R97775 : Reach 97775 := rs (se 1 (by rfl) ⟨73331, by rfl⟩) R146663
theorem R65371 : Reach 65371 := rs (se 1 (by rfl) ⟨49028, by rfl⟩) R98057
theorem R98185 : Reach 98185 := rs (se 2 (by rfl) ⟨36819, by rfl⟩) R73639
theorem R229331 : Reach 229331 := rs (se 1 (by rfl) ⟨171998, by rfl⟩) R343997
theorem R229787 : Reach 229787 := rs (se 1 (by rfl) ⟨172340, by rfl⟩) R344681
theorem R262561 : Reach 262561 := rs (se 2 (by rfl) ⟨98460, by rfl⟩) R196921
theorem R754697 : Reach 754697 := rs (se 2 (by rfl) ⟨283011, by rfl⟩) R566023
theorem R689633 : Reach 689633 := rs (se 2 (by rfl) ⟨258612, by rfl⟩) R517225
theorem R1345211 : Reach 1345211 := rs (se 1 (by rfl) ⟨1008908, by rfl⟩) R2017817
theorem R198395 : Reach 198395 := rs (se 1 (by rfl) ⟨148796, by rfl⟩) R297593
theorem R133775 : Reach 133775 := rs (se 1 (by rfl) ⟨100331, by rfl⟩) R200663
theorem R232217 : Reach 232217 := rs (se 2 (by rfl) ⟨87081, by rfl⟩) R174163
theorem R101695 : Reach 101695 := rs (se 1 (by rfl) ⟨76271, by rfl⟩) R152543
theorem R232915 : Reach 232915 := rs (se 1 (by rfl) ⟨174686, by rfl⟩) R349373
theorem R134675 : Reach 134675 := rs (se 1 (by rfl) ⟨101006, by rfl⟩) R202013
theorem R134747 : Reach 134747 := rs (se 1 (by rfl) ⟨101060, by rfl⟩) R202121
theorem R921223 : Reach 921223 := rs (se 1 (by rfl) ⟨690917, by rfl⟩) R1381835
theorem R167591 : Reach 167591 := rs (se 1 (by rfl) ⟨125693, by rfl⟩) R251387
theorem R69871 : Reach 69871 := rs (se 1 (by rfl) ⟨52403, by rfl⟩) R104807
theorem R2232677 : Reach 2232677 := rs (se 4 (by rfl) ⟨209313, by rfl⟩) R418627
theorem R70123 : Reach 70123 := rs (se 1 (by rfl) ⟨52592, by rfl⟩) R105185
theorem R299513 : Reach 299513 := rs (se 2 (by rfl) ⟨112317, by rfl⟩) R224635
theorem R7082599 : Reach 7082599 := rs (se 1 (by rfl) ⟨5311949, by rfl⟩) R10623899
theorem R430703 : Reach 430703 := rs (se 1 (by rfl) ⟨323027, by rfl⟩) R646055
theorem R103403 : Reach 103403 := rs (se 1 (by rfl) ⟨77552, by rfl⟩) R155105
theorem R201851 : Reach 201851 := rs (se 1 (by rfl) ⟨151388, by rfl⟩) R302777
theorem R1971377 : Reach 1971377 := rs (se 2 (by rfl) ⟨739266, by rfl⟩) R1478533
theorem R234859 : Reach 234859 := rs (se 1 (by rfl) ⟨176144, by rfl⟩) R352289
theorem R103963 : Reach 103963 := rs (se 1 (by rfl) ⟨77972, by rfl⟩) R155945
theorem R824995 : Reach 824995 := rs (se 1 (by rfl) ⟨618746, by rfl⟩) R1237493
theorem R104105 : Reach 104105 := rs (se 2 (by rfl) ⟨39039, by rfl⟩) R78079
theorem R1841363 : Reach 1841363 := rs (se 1 (by rfl) ⟨1381022, by rfl⟩) R2762045
theorem R137447 : Reach 137447 := rs (se 1 (by rfl) ⟨103085, by rfl⟩) R206171
theorem R268591 : Reach 268591 := rs (se 1 (by rfl) ⟨201443, by rfl⟩) R402887
theorem R661841 : Reach 661841 := rs (se 2 (by rfl) ⟨248190, by rfl⟩) R496381
theorem R236135 : Reach 236135 := rs (se 1 (by rfl) ⟨177101, by rfl⟩) R354203
theorem R105151 : Reach 105151 := rs (se 1 (by rfl) ⟨78863, by rfl⟩) R157727
theorem R105455 : Reach 105455 := rs (se 1 (by rfl) ⟨79091, by rfl⟩) R158183
theorem R105563 : Reach 105563 := rs (se 1 (by rfl) ⟨79172, by rfl⟩) R158345
theorem R597257 : Reach 597257 := rs (se 2 (by rfl) ⟨223971, by rfl⟩) R447943
theorem R433619 : Reach 433619 := rs (se 1 (by rfl) ⟨325214, by rfl⟩) R650429
theorem R204443 : Reach 204443 := rs (se 1 (by rfl) ⟨153332, by rfl⟩) R306665
theorem R106319 : Reach 106319 := rs (se 1 (by rfl) ⟨79739, by rfl⟩) R159479
theorem R204983 : Reach 204983 := rs (se 1 (by rfl) ⟨153737, by rfl⟩) R307475
theorem R369107 : Reach 369107 := rs (se 1 (by rfl) ⟨276830, by rfl⟩) R553661
theorem R696833 : Reach 696833 := rs (se 2 (by rfl) ⟨261312, by rfl⟩) R522625
theorem R598547 : Reach 598547 := rs (se 1 (by rfl) ⟨448910, by rfl⟩) R897821
theorem R533081 : Reach 533081 := rs (se 2 (by rfl) ⟨199905, by rfl⟩) R399811
theorem R336959 : Reach 336959 := rs (se 1 (by rfl) ⟨252719, by rfl⟩) R505439
theorem R74935 : Reach 74935 := rs (se 1 (by rfl) ⟨56201, by rfl⟩) R112403
theorem R894905 : Reach 894905 := rs (se 2 (by rfl) ⟨335589, by rfl⟩) R671179
theorem R207485 : Reach 207485 := rs (se 3 (by rfl) ⟨38903, by rfl⟩) R77807
theorem R1190821 : Reach 1190821 := rs (se 4 (by rfl) ⟨111639, by rfl⟩) R223279
theorem R469961 : Reach 469961 := rs (se 2 (by rfl) ⟨176235, by rfl⟩) R352471
theorem R76783 : Reach 76783 := rs (se 1 (by rfl) ⟨57587, by rfl⟩) R115175
theorem R109679 : Reach 109679 := rs (se 1 (by rfl) ⟨82259, by rfl⟩) R164519
theorem R208223 : Reach 208223 := rs (se 1 (by rfl) ⟨156167, by rfl⟩) R312335
theorem R339623 : Reach 339623 := rs (se 1 (by rfl) ⟨254717, by rfl⟩) R509435
theorem R209033 : Reach 209033 := rs (se 2 (by rfl) ⟨78387, by rfl⟩) R156775
theorem R1258021 : Reach 1258021 := rs (se 4 (by rfl) ⟨117939, by rfl⟩) R235879
theorem R571115 : Reach 571115 := rs (se 1 (by rfl) ⟨428336, by rfl⟩) R856673
theorem R145385 : Reach 145385 := rs (se 2 (by rfl) ⟨54519, by rfl⟩) R109039
theorem R210923 : Reach 210923 := rs (se 1 (by rfl) ⟨158192, by rfl⟩) R316385
theorem R14956597 : Reach 14956597 := rs (se 5 (by rfl) ⟨701090, by rfl⟩) R1402181
theorem R342265 : Reach 342265 := rs (se 2 (by rfl) ⟨128349, by rfl⟩) R256699
theorem R211247 : Reach 211247 := rs (se 1 (by rfl) ⟨158435, by rfl⟩) R316871
theorem R211355 : Reach 211355 := rs (se 1 (by rfl) ⟨158516, by rfl⟩) R317033
theorem R506341 : Reach 506341 := rs (se 4 (by rfl) ⟨47469, by rfl⟩) R94939
theorem R3291677 : Reach 3291677 := rs (se 3 (by rfl) ⟨617189, by rfl⟩) R1234379
theorem R408559 : Reach 408559 := rs (se 1 (by rfl) ⟨306419, by rfl⟩) R612839
theorem R900497 : Reach 900497 := rs (se 2 (by rfl) ⟨337686, by rfl⟩) R675373
theorem R114529 : Reach 114529 := rs (se 2 (by rfl) ⟨42948, by rfl⟩) R85897
theorem R180215 : Reach 180215 := rs (se 1 (by rfl) ⟨135161, by rfl⟩) R270323
theorem R1360435 : Reach 1360435 := rs (se 1 (by rfl) ⟨1020326, by rfl⟩) R2040653
theorem R246847 : Reach 246847 := rs (se 1 (by rfl) ⟨185135, by rfl⟩) R370271
theorem R181415 : Reach 181415 := rs (se 1 (by rfl) ⟨136061, by rfl⟩) R272123
theorem R115987 : Reach 115987 := rs (se 1 (by rfl) ⟨86990, by rfl⟩) R173981
theorem R116777 : Reach 116777 := rs (se 2 (by rfl) ⟨43791, by rfl⟩) R87583
theorem R2345435 : Reach 2345435 := rs (se 1 (by rfl) ⟨1759076, by rfl⟩) R3518153
theorem R510553 : Reach 510553 := rs (se 2 (by rfl) ⟨191457, by rfl⟩) R382915
theorem R641681 : Reach 641681 := rs (se 2 (by rfl) ⟨240630, by rfl⟩) R481261
theorem R150569 : Reach 150569 := rs (se 2 (by rfl) ⟨56463, by rfl⟩) R112927
theorem R150619 : Reach 150619 := rs (se 1 (by rfl) ⟨112964, by rfl⟩) R225929
theorem R2411707 : Reach 2411707 := rs (se 1 (by rfl) ⟨1808780, by rfl⟩) R3617561
theorem R511721 : Reach 511721 := rs (se 2 (by rfl) ⟨191895, by rfl⟩) R383791
theorem R119161 : Reach 119161 := rs (se 2 (by rfl) ⟨44685, by rfl⟩) R89371
theorem R87161 : Reach 87161 := rs (se 2 (by rfl) ⟨32685, by rfl⟩) R65371
theorem R152887 : Reach 152887 := rs (se 1 (by rfl) ⟨114665, by rfl⟩) R229331
theorem R7722503 : Reach 7722503 := rs (se 1 (by rfl) ⟨5791877, by rfl⟩) R11583755
theorem R87935 : Reach 87935 := rs (se 1 (by rfl) ⟨65951, by rfl⟩) R131903
theorem R153647 : Reach 153647 := rs (se 1 (by rfl) ⟨115235, by rfl⟩) R230471
theorem R514307 : Reach 514307 := rs (se 1 (by rfl) ⟨385730, by rfl⟩) R771461
theorem R7428631 : Reach 7428631 := rs (se 1 (by rfl) ⟨5571473, by rfl⟩) R11142947
theorem R88703 : Reach 88703 := rs (se 1 (by rfl) ⟨66527, by rfl⟩) R133055
theorem R940709 : Reach 940709 := rs (se 4 (by rfl) ⟨88191, by rfl⟩) R176383
theorem R88841 : Reach 88841 := rs (se 2 (by rfl) ⟨33315, by rfl⟩) R66631
theorem R187177 : Reach 187177 := rs (se 2 (by rfl) ⟨70191, by rfl⟩) R140383
theorem R89081 : Reach 89081 := rs (se 2 (by rfl) ⟨33405, by rfl⟩) R66811
theorem R220153 : Reach 220153 := rs (se 2 (by rfl) ⟨82557, by rfl⟩) R165115
theorem R154831 : Reach 154831 := rs (se 1 (by rfl) ⟨116123, by rfl⟩) R232247
theorem R89399 : Reach 89399 := rs (se 1 (by rfl) ⟨67049, by rfl⟩) R134099
theorem R89579 : Reach 89579 := rs (se 1 (by rfl) ⟨67184, by rfl⟩) R134369
theorem R318977 : Reach 318977 := rs (se 2 (by rfl) ⟨119616, by rfl⟩) R239233
theorem R90107 : Reach 90107 := rs (se 1 (by rfl) ⟨67580, by rfl⟩) R135161
theorem R90167 : Reach 90167 := rs (se 1 (by rfl) ⟨67625, by rfl⟩) R135251
theorem R90239 : Reach 90239 := rs (se 1 (by rfl) ⟨67679, by rfl⟩) R135359
theorem R90287 : Reach 90287 := rs (se 1 (by rfl) ⟨67715, by rfl⟩) R135431
theorem R319883 : Reach 319883 := rs (se 1 (by rfl) ⟨239912, by rfl⟩) R479825
theorem R91007 : Reach 91007 := rs (se 1 (by rfl) ⟨68255, by rfl⟩) R136511
theorem R91079 : Reach 91079 := rs (se 1 (by rfl) ⟨68309, by rfl⟩) R136619
theorem R91439 : Reach 91439 := rs (se 1 (by rfl) ⟨68579, by rfl⟩) R137159
theorem R451979 : Reach 451979 := rs (se 1 (by rfl) ⟨338984, by rfl⟩) R677969
theorem R91679 : Reach 91679 := rs (se 1 (by rfl) ⟨68759, by rfl⟩) R137519
theorem R452299 : Reach 452299 := rs (se 1 (by rfl) ⟨339224, by rfl⟩) R678449
theorem R288479 : Reach 288479 := rs (se 1 (by rfl) ⟨216359, by rfl⟩) R432719
theorem R59247 : Reach 59247 := rs (se 1 (by rfl) ⟨44435, by rfl⟩) R88871
theorem R59263 : Reach 59263 := rs (se 1 (by rfl) ⟨44447, by rfl⟩) R88895
theorem R59463 : Reach 59463 := rs (se 1 (by rfl) ⟨44597, by rfl⟩) R89195
theorem R190603 : Reach 190603 := rs (se 1 (by rfl) ⟨142952, by rfl⟩) R285905
theorem R59559 : Reach 59559 := rs (se 1 (by rfl) ⟨44669, by rfl⟩) R89339
theorem R59623 : Reach 59623 := rs (se 1 (by rfl) ⟨44717, by rfl⟩) R89435
theorem R59643 : Reach 59643 := rs (se 1 (by rfl) ⟨44732, by rfl⟩) R89465
theorem R59647 : Reach 59647 := rs (se 1 (by rfl) ⟨44735, by rfl⟩) R89471
theorem R92615 : Reach 92615 := rs (se 1 (by rfl) ⟨69461, by rfl⟩) R138923
theorem R60015 : Reach 60015 := rs (se 1 (by rfl) ⟨45011, by rfl⟩) R90023
theorem R60063 : Reach 60063 := rs (se 1 (by rfl) ⟨45047, by rfl⟩) R90095
theorem R158375 : Reach 158375 := rs (se 1 (by rfl) ⟨118781, by rfl⟩) R237563
theorem R60143 : Reach 60143 := rs (se 1 (by rfl) ⟨45107, by rfl⟩) R90215
theorem R92975 : Reach 92975 := rs (se 1 (by rfl) ⟨69731, by rfl⟩) R139463
theorem R60231 : Reach 60231 := rs (se 1 (by rfl) ⟨45173, by rfl⟩) R90347
theorem R60271 : Reach 60271 := rs (se 1 (by rfl) ⟨45203, by rfl⟩) R90407
theorem R93095 : Reach 93095 := rs (se 1 (by rfl) ⟨69821, by rfl⟩) R139643
theorem R453599 : Reach 453599 := rs (se 1 (by rfl) ⟨340199, by rfl⟩) R680399
theorem R93275 : Reach 93275 := rs (se 1 (by rfl) ⟨69956, by rfl⟩) R139913
theorem R60571 : Reach 60571 := rs (se 1 (by rfl) ⟨45428, by rfl⟩) R90857
theorem R159023 : Reach 159023 := rs (se 1 (by rfl) ⟨119267, by rfl⟩) R238535
theorem R2485633 : Reach 2485633 := rs (se 2 (by rfl) ⟨932112, by rfl⟩) R1864225
theorem R60831 : Reach 60831 := rs (se 1 (by rfl) ⟨45623, by rfl⟩) R91247
theorem R60911 : Reach 60911 := rs (se 1 (by rfl) ⟨45683, by rfl⟩) R91367
theorem R60955 : Reach 60955 := rs (se 1 (by rfl) ⟨45716, by rfl⟩) R91433
theorem R1109629 : Reach 1109629 := rs (se 3 (by rfl) ⟨208055, by rfl⟩) R416111
theorem R224927 : Reach 224927 := rs (se 1 (by rfl) ⟨168695, by rfl⟩) R337391
theorem R93863 : Reach 93863 := rs (se 1 (by rfl) ⟨70397, by rfl⟩) R140795
theorem R61135 : Reach 61135 := rs (se 1 (by rfl) ⟨45851, by rfl⟩) R91703
theorem R93983 : Reach 93983 := rs (se 1 (by rfl) ⟨70487, by rfl⟩) R140975
theorem R94043 : Reach 94043 := rs (se 1 (by rfl) ⟨70532, by rfl⟩) R141065
theorem R61351 : Reach 61351 := rs (se 1 (by rfl) ⟨46013, by rfl⟩) R92027
theorem R61375 : Reach 61375 := rs (se 1 (by rfl) ⟨46031, by rfl⟩) R92063
theorem R94187 : Reach 94187 := rs (se 1 (by rfl) ⟨70640, by rfl⟩) R141281
theorem R61531 : Reach 61531 := rs (se 1 (by rfl) ⟨46148, by rfl⟩) R92297
theorem R258187 : Reach 258187 := rs (se 1 (by rfl) ⟨193640, by rfl⟩) R387281
theorem R258203 : Reach 258203 := rs (se 1 (by rfl) ⟨193652, by rfl⟩) R387305
theorem R61631 : Reach 61631 := rs (se 1 (by rfl) ⟨46223, by rfl⟩) R92447
theorem R61663 : Reach 61663 := rs (se 1 (by rfl) ⟨46247, by rfl⟩) R92495
theorem R94463 : Reach 94463 := rs (se 1 (by rfl) ⟨70847, by rfl⟩) R141695
theorem R61723 : Reach 61723 := rs (se 1 (by rfl) ⟨46292, by rfl⟩) R92585
theorem R61979 : Reach 61979 := rs (se 1 (by rfl) ⟨46484, by rfl⟩) R92969
theorem R62119 : Reach 62119 := rs (se 1 (by rfl) ⟨46589, by rfl⟩) R93179
theorem R62159 : Reach 62159 := rs (se 1 (by rfl) ⟨46619, by rfl⟩) R93239
theorem R62239 : Reach 62239 := rs (se 1 (by rfl) ⟨46679, by rfl⟩) R93359
theorem R226111 : Reach 226111 := rs (se 1 (by rfl) ⟨169583, by rfl⟩) R339167
theorem R62279 : Reach 62279 := rs (se 1 (by rfl) ⟨46709, by rfl⟩) R93419
theorem R357473 : Reach 357473 := rs (se 2 (by rfl) ⟨134052, by rfl⟩) R268105
theorem R62719 : Reach 62719 := rs (se 1 (by rfl) ⟨47039, by rfl⟩) R94079
theorem R62799 : Reach 62799 := rs (se 1 (by rfl) ⟨47099, by rfl⟩) R94199
theorem R62943 : Reach 62943 := rs (se 1 (by rfl) ⟨47207, by rfl⟩) R94415
theorem R63023 : Reach 63023 := rs (se 1 (by rfl) ⟨47267, by rfl⟩) R94535
theorem R457325 : Reach 457325 := rs (se 3 (by rfl) ⟨85748, by rfl⟩) R171497
theorem R65183 : Reach 65183 := rs (se 1 (by rfl) ⟨48887, by rfl⟩) R97775
theorem R130913 : Reach 130913 := rs (se 2 (by rfl) ⟨49092, by rfl⟩) R98185
theorem R622525 : Reach 622525 := rs (se 3 (by rfl) ⟨116723, by rfl⟩) R233447
theorem R459755 : Reach 459755 := rs (se 1 (by rfl) ⟨344816, by rfl⟩) R689633
theorem R853021 : Reach 853021 := rs (se 3 (by rfl) ⟨159941, by rfl⟩) R319883
theorem R132263 : Reach 132263 := rs (se 1 (by rfl) ⟨99197, by rfl⟩) R198395
theorem R329129 : Reach 329129 := rs (se 2 (by rfl) ⟨123423, by rfl⟩) R246847
theorem R99913 : Reach 99913 := rs (se 2 (by rfl) ⟨37467, by rfl⟩) R74935
theorem R427787 : Reach 427787 := rs (se 1 (by rfl) ⟨320840, by rfl⟩) R641681
theorem R100379 : Reach 100379 := rs (se 1 (by rfl) ⟨75284, by rfl⟩) R150569
theorem R232429 : Reach 232429 := rs (se 3 (by rfl) ⟨43580, by rfl⟩) R87161
theorem R199675 : Reach 199675 := rs (se 1 (by rfl) ⟨149756, by rfl⟩) R299513
theorem R68935 : Reach 68935 := rs (se 1 (by rfl) ⟨51701, by rfl⟩) R103403
theorem R134567 : Reach 134567 := rs (se 1 (by rfl) ⟨100925, by rfl⟩) R201851
theorem R1314251 : Reach 1314251 := rs (se 1 (by rfl) ⟨985688, by rfl⟩) R1971377
theorem R5148335 : Reach 5148335 := rs (se 1 (by rfl) ⟨3861251, by rfl⟩) R7722503
theorem R69403 : Reach 69403 := rs (se 1 (by rfl) ⟨52052, by rfl⟩) R104105
theorem R102377 : Reach 102377 := rs (se 2 (by rfl) ⟨38391, by rfl⟩) R76783
theorem R102431 : Reach 102431 := rs (se 1 (by rfl) ⟨76823, by rfl⟩) R153647
theorem R200825 : Reach 200825 := rs (se 2 (by rfl) ⟨75309, by rfl⟩) R150619
theorem R3215609 : Reach 3215609 := rs (se 2 (by rfl) ⟨1205853, by rfl⟩) R2411707
theorem R135593 : Reach 135593 := rs (se 2 (by rfl) ⟨50847, by rfl⟩) R101695
theorem R627139 : Reach 627139 := rs (se 1 (by rfl) ⟨470354, by rfl⟩) R940709
theorem R3314177 : Reach 3314177 := rs (se 2 (by rfl) ⟨1242816, by rfl⟩) R2485633
theorem R70303 : Reach 70303 := rs (se 1 (by rfl) ⟨52727, by rfl⟩) R105455
theorem R70375 : Reach 70375 := rs (se 1 (by rfl) ⟨52781, by rfl⟩) R105563
theorem R1479505 : Reach 1479505 := rs (se 2 (by rfl) ⟨554814, by rfl⟩) R1109629
theorem R398171 : Reach 398171 := rs (se 1 (by rfl) ⟨298628, by rfl⟩) R597257
theorem R136295 : Reach 136295 := rs (se 1 (by rfl) ⟨102221, by rfl⟩) R204443
theorem R70879 : Reach 70879 := rs (se 1 (by rfl) ⟨53159, by rfl⟩) R106319
theorem R136655 : Reach 136655 := rs (se 1 (by rfl) ⟨102491, by rfl⟩) R204983
theorem R464555 : Reach 464555 := rs (se 1 (by rfl) ⟨348416, by rfl⟩) R696833
theorem R1677361 : Reach 1677361 := rs (se 2 (by rfl) ⟨629010, by rfl⟩) R1258021
theorem R9443465 : Reach 9443465 := rs (se 2 (by rfl) ⟨3541299, by rfl⟩) R7082599
theorem R301319 : Reach 301319 := rs (se 1 (by rfl) ⟨225989, by rfl⟩) R451979
theorem R301481 : Reach 301481 := rs (se 2 (by rfl) ⟨113055, by rfl⟩) R226111
theorem R596603 : Reach 596603 := rs (se 1 (by rfl) ⟨447452, by rfl⟩) R894905
theorem R203849 : Reach 203849 := rs (se 2 (by rfl) ⟨76443, by rfl⟩) R152887
theorem R138323 : Reach 138323 := rs (se 1 (by rfl) ⟨103742, by rfl⟩) R207485
theorem R105583 : Reach 105583 := rs (se 1 (by rfl) ⟨79187, by rfl⟩) R158375
theorem R302399 : Reach 302399 := rs (se 1 (by rfl) ⟨226799, by rfl⟩) R453599
theorem R138617 : Reach 138617 := rs (se 2 (by rfl) ⟨51981, by rfl⟩) R103963
theorem R106015 : Reach 106015 := rs (se 1 (by rfl) ⟨79511, by rfl⟩) R159023
theorem R138815 : Reach 138815 := rs (se 1 (by rfl) ⟨104111, by rfl⟩) R208223
theorem R139355 : Reach 139355 := rs (se 1 (by rfl) ⟨104516, by rfl⟩) R209033
theorem R172135 : Reach 172135 := rs (se 1 (by rfl) ⟨129101, by rfl⟩) R258203
theorem R9904841 : Reach 9904841 := rs (se 2 (by rfl) ⟨3714315, by rfl⟩) R7428631
theorem R238315 : Reach 238315 := rs (se 1 (by rfl) ⟨178736, by rfl⟩) R357473
theorem R140201 : Reach 140201 := rs (se 2 (by rfl) ⟨52575, by rfl⟩) R105151
theorem R2401325 : Reach 2401325 := rs (se 3 (by rfl) ⟨450248, by rfl⟩) R900497
theorem R140615 : Reach 140615 := rs (se 1 (by rfl) ⟨105461, by rfl⟩) R210923
theorem R140831 : Reach 140831 := rs (se 1 (by rfl) ⟨105623, by rfl⟩) R211247
theorem R140903 : Reach 140903 := rs (se 1 (by rfl) ⟨105677, by rfl⟩) R211355
theorem R206441 : Reach 206441 := rs (se 2 (by rfl) ⟨77415, by rfl⟩) R154831
theorem R304883 : Reach 304883 := rs (se 1 (by rfl) ⟨228662, by rfl⟩) R457325
theorem R173821 : Reach 173821 := rs (se 3 (by rfl) ⟨32591, by rfl⟩) R65183
theorem R830033 : Reach 830033 := rs (se 2 (by rfl) ⟨311262, by rfl⟩) R622525
theorem R503131 : Reach 503131 := rs (se 1 (by rfl) ⟨377348, by rfl⟩) R754697
theorem R1813913 : Reach 1813913 := rs (se 2 (by rfl) ⟨680217, by rfl⟩) R1360435
theorem R896807 : Reach 896807 := rs (se 1 (by rfl) ⟨672605, by rfl⟩) R1345211
theorem R77851 : Reach 77851 := rs (se 1 (by rfl) ⟨58388, by rfl⟩) R116777
theorem R603065 : Reach 603065 := rs (se 2 (by rfl) ⟨226149, by rfl⟩) R452299
theorem R111727 : Reach 111727 := rs (se 1 (by rfl) ⟨83795, by rfl⟩) R167591
theorem R341147 : Reach 341147 := rs (se 1 (by rfl) ⟨255860, by rfl⟩) R511721
theorem R2700485 : Reach 2700485 := rs (se 4 (by rfl) ⟨253170, by rfl⟩) R506341
theorem R1488451 : Reach 1488451 := rs (se 1 (by rfl) ⟨1116338, by rfl⟩) R2232677
theorem R1587761 : Reach 1587761 := rs (se 2 (by rfl) ⟨595410, by rfl⟩) R1190821
theorem R1227575 : Reach 1227575 := rs (se 1 (by rfl) ⟨920681, by rfl⟩) R1841363
theorem R441227 : Reach 441227 := rs (se 1 (by rfl) ⟨330920, by rfl⟩) R661841
theorem R769277 : Reach 769277 := rs (se 3 (by rfl) ⟨144239, by rfl⟩) R288479
theorem R310553 : Reach 310553 := rs (se 2 (by rfl) ⟨116457, by rfl⟩) R232915
theorem R1228297 : Reach 1228297 := rs (se 2 (by rfl) ⟨460611, by rfl⟩) R921223
theorem R212651 : Reach 212651 := rs (se 1 (by rfl) ⟨159488, by rfl⟩) R318977
theorem R344249 : Reach 344249 := rs (se 2 (by rfl) ⟨129093, by rfl⟩) R258187
theorem R246071 : Reach 246071 := rs (se 1 (by rfl) ⟨184553, by rfl⟩) R369107
theorem R313145 : Reach 313145 := rs (se 2 (by rfl) ⟨117429, by rfl⟩) R234859
theorem R313307 : Reach 313307 := rs (se 1 (by rfl) ⟨234980, by rfl⟩) R469961
theorem R1099993 : Reach 1099993 := rs (se 2 (by rfl) ⟨412497, by rfl⟩) R824995
theorem R149951 : Reach 149951 := rs (se 1 (by rfl) ⟨112463, by rfl⟩) R224927
theorem R19942129 : Reach 19942129 := rs (se 2 (by rfl) ⟨7478298, by rfl⟩) R14956597
theorem R249569 : Reach 249569 := rs (se 2 (by rfl) ⟨93588, by rfl⟩) R187177
theorem R380743 : Reach 380743 := rs (se 1 (by rfl) ⟨285557, by rfl⟩) R571115
theorem R544745 : Reach 544745 := rs (se 2 (by rfl) ⟨204279, by rfl⟩) R408559
theorem R937973 : Reach 937973 := rs (se 5 (by rfl) ⟨43967, by rfl⟩) R87935
theorem R152705 : Reach 152705 := rs (se 2 (by rfl) ⟨57264, by rfl⟩) R114529
theorem R87275 : Reach 87275 := rs (se 1 (by rfl) ⟨65456, by rfl⟩) R130913
theorem R120143 : Reach 120143 := rs (se 1 (by rfl) ⟨90107, by rfl⟩) R180215
theorem R153191 : Reach 153191 := rs (se 1 (by rfl) ⟨114893, by rfl⟩) R229787
theorem R350081 : Reach 350081 := rs (se 2 (by rfl) ⟨131280, by rfl⟩) R262561
theorem R120943 : Reach 120943 := rs (se 1 (by rfl) ⟨90707, by rfl⟩) R181415
theorem R1169909 : Reach 1169909 := rs (se 5 (by rfl) ⟨54839, by rfl⟩) R109679
theorem R1596125 : Reach 1596125 := rs (se 3 (by rfl) ⟨299273, by rfl⟩) R598547
theorem R1563623 : Reach 1563623 := rs (se 1 (by rfl) ⟨1172717, by rfl⟩) R2345435
theorem R154649 : Reach 154649 := rs (se 2 (by rfl) ⟨57993, by rfl⟩) R115987
theorem R89183 : Reach 89183 := rs (se 1 (by rfl) ⟨66887, by rfl⟩) R133775
theorem R154811 : Reach 154811 := rs (se 1 (by rfl) ⟨116108, by rfl⟩) R232217
theorem R89783 : Reach 89783 := rs (se 1 (by rfl) ⟨67337, by rfl⟩) R134675
theorem R89831 : Reach 89831 := rs (se 1 (by rfl) ⟨67373, by rfl⟩) R134747
theorem R254137 : Reach 254137 := rs (se 2 (by rfl) ⟨95301, by rfl⟩) R190603
theorem R287135 : Reach 287135 := rs (se 1 (by rfl) ⟨215351, by rfl⟩) R430703
theorem R680737 : Reach 680737 := rs (se 2 (by rfl) ⟨255276, by rfl⟩) R510553
theorem R91631 : Reach 91631 := rs (se 1 (by rfl) ⟨68723, by rfl⟩) R137447
theorem R157423 : Reach 157423 := rs (se 1 (by rfl) ⟨118067, by rfl⟩) R236135
theorem R59135 : Reach 59135 := rs (se 1 (by rfl) ⟨44351, by rfl⟩) R88703
theorem R59227 : Reach 59227 := rs (se 1 (by rfl) ⟨44420, by rfl⟩) R88841
theorem R59387 : Reach 59387 := rs (se 1 (by rfl) ⟨44540, by rfl⟩) R89081
theorem R59599 : Reach 59599 := rs (se 1 (by rfl) ⟨44699, by rfl⟩) R89399
theorem R289079 : Reach 289079 := rs (se 1 (by rfl) ⟨216809, by rfl⟩) R433619
theorem R59719 : Reach 59719 := rs (se 1 (by rfl) ⟨44789, by rfl⟩) R89579
theorem R60071 : Reach 60071 := rs (se 1 (by rfl) ⟨45053, by rfl⟩) R90107
theorem R60111 : Reach 60111 := rs (se 1 (by rfl) ⟨45083, by rfl⟩) R90167
theorem R60159 : Reach 60159 := rs (se 1 (by rfl) ⟨45119, by rfl⟩) R90239
theorem R60191 : Reach 60191 := rs (se 1 (by rfl) ⟨45143, by rfl⟩) R90287
theorem R93161 : Reach 93161 := rs (se 2 (by rfl) ⟨34935, by rfl⟩) R69871
theorem R355387 : Reach 355387 := rs (se 1 (by rfl) ⟨266540, by rfl⟩) R533081
theorem R158881 : Reach 158881 := rs (se 2 (by rfl) ⟨59580, by rfl⟩) R119161
theorem R60671 : Reach 60671 := rs (se 1 (by rfl) ⟨45503, by rfl⟩) R91007
theorem R60719 : Reach 60719 := rs (se 1 (by rfl) ⟨45539, by rfl⟩) R91079
theorem R93497 : Reach 93497 := rs (se 2 (by rfl) ⟨35061, by rfl⟩) R70123
theorem R1371485 : Reach 1371485 := rs (se 3 (by rfl) ⟨257153, by rfl⟩) R514307
theorem R224639 : Reach 224639 := rs (se 1 (by rfl) ⟨168479, by rfl⟩) R336959
theorem R60959 : Reach 60959 := rs (se 1 (by rfl) ⟨45719, by rfl⟩) R91439
theorem R61119 : Reach 61119 := rs (se 1 (by rfl) ⟨45839, by rfl⟩) R91679
theorem R61743 : Reach 61743 := rs (se 1 (by rfl) ⟨46307, by rfl⟩) R92615
theorem R61983 : Reach 61983 := rs (se 1 (by rfl) ⟨46487, by rfl⟩) R92975
theorem R62063 : Reach 62063 := rs (se 1 (by rfl) ⟨46547, by rfl⟩) R93095
theorem R62183 : Reach 62183 := rs (se 1 (by rfl) ⟨46637, by rfl⟩) R93275
theorem R226415 : Reach 226415 := rs (se 1 (by rfl) ⟨169811, by rfl⟩) R339623
theorem R62575 : Reach 62575 := rs (se 1 (by rfl) ⟨46931, by rfl⟩) R93863
theorem R62655 : Reach 62655 := rs (se 1 (by rfl) ⟨46991, by rfl⟩) R93983
theorem R62695 : Reach 62695 := rs (se 1 (by rfl) ⟨47021, by rfl⟩) R94043
theorem R62791 : Reach 62791 := rs (se 1 (by rfl) ⟨47093, by rfl⟩) R94187
theorem R62975 : Reach 62975 := rs (se 1 (by rfl) ⟨47231, by rfl⟩) R94463
theorem R456353 : Reach 456353 := rs (se 2 (by rfl) ⟨171132, by rfl⟩) R342265
theorem R358121 : Reach 358121 := rs (se 2 (by rfl) ⟨134295, by rfl⟩) R268591
theorem R96923 : Reach 96923 := rs (se 1 (by rfl) ⟨72692, by rfl⟩) R145385
theorem R293537 : Reach 293537 := rs (se 2 (by rfl) ⟨110076, by rfl⟩) R220153
theorem R2194451 : Reach 2194451 := rs (se 1 (by rfl) ⟨1645838, by rfl⟩) R3291677
theorem R229499 : Reach 229499 := rs (se 1 (by rfl) ⟨172124, by rfl⟩) R344249
theorem R229513 : Reach 229513 := rs (se 2 (by rfl) ⟨86067, by rfl⟩) R172135
theorem R164047 : Reach 164047 := rs (se 1 (by rfl) ⟨123035, by rfl⟩) R246071
theorem R66919 : Reach 66919 := rs (se 1 (by rfl) ⟨50189, by rfl⟩) R100379
theorem R99967 : Reach 99967 := rs (se 1 (by rfl) ⟨74975, by rfl⟩) R149951
theorem R133217 : Reach 133217 := rs (se 2 (by rfl) ⟨49956, by rfl⟩) R99913
theorem R231761 : Reach 231761 := rs (se 2 (by rfl) ⟨86910, by rfl⟩) R173821
theorem R166379 : Reach 166379 := rs (se 1 (by rfl) ⟨124784, by rfl⟩) R249569
theorem R363163 : Reach 363163 := rs (se 1 (by rfl) ⟨272372, by rfl⟩) R544745
theorem R68251 : Reach 68251 := rs (se 1 (by rfl) ⟨51188, by rfl⟩) R102377
theorem R625315 : Reach 625315 := rs (se 1 (by rfl) ⟨468986, by rfl⟩) R937973
theorem R68287 : Reach 68287 := rs (se 1 (by rfl) ⟨51215, by rfl⟩) R102431
theorem R133883 : Reach 133883 := rs (se 1 (by rfl) ⟨100412, by rfl⟩) R200825
theorem R265447 : Reach 265447 := rs (se 1 (by rfl) ⟨199085, by rfl⟩) R398171
theorem R232733 : Reach 232733 := rs (se 3 (by rfl) ⟨43637, by rfl⟩) R87275
theorem R101803 : Reach 101803 := rs (se 1 (by rfl) ⟨76352, by rfl⟩) R152705
theorem R102127 : Reach 102127 := rs (se 1 (by rfl) ⟨76595, by rfl⟩) R153191
theorem R233387 : Reach 233387 := rs (se 1 (by rfl) ⟨175040, by rfl⟩) R350081
theorem R6295643 : Reach 6295643 := rs (se 1 (by rfl) ⟨4721732, by rfl⟩) R9443465
theorem R200879 : Reach 200879 := rs (se 1 (by rfl) ⟨150659, by rfl⟩) R301319
theorem R200987 : Reach 200987 := rs (se 1 (by rfl) ⟨150740, by rfl⟩) R301481
theorem R397735 : Reach 397735 := rs (se 1 (by rfl) ⟨298301, by rfl⟩) R596603
theorem R103099 : Reach 103099 := rs (se 1 (by rfl) ⟨77324, by rfl⟩) R154649
theorem R135899 : Reach 135899 := rs (se 1 (by rfl) ⟨101924, by rfl⟩) R203849
theorem R103207 : Reach 103207 := rs (se 1 (by rfl) ⟨77405, by rfl⟩) R154811
theorem R201599 : Reach 201599 := rs (se 1 (by rfl) ⟨151199, by rfl⟩) R302399
theorem R103801 : Reach 103801 := rs (se 2 (by rfl) ⟨38925, by rfl⟩) R77851
theorem R137627 : Reach 137627 := rs (se 1 (by rfl) ⟨103220, by rfl⟩) R206441
theorem R1972673 : Reach 1972673 := rs (se 2 (by rfl) ⟨739752, by rfl⟩) R1479505
theorem R203255 : Reach 203255 := rs (se 1 (by rfl) ⟨152441, by rfl⟩) R304883
theorem R597871 : Reach 597871 := rs (se 1 (by rfl) ⟨448403, by rfl⟩) R896807
theorem R2236481 : Reach 2236481 := rs (se 2 (by rfl) ⟨838680, by rfl⟩) R1677361
theorem R402043 : Reach 402043 := rs (se 1 (by rfl) ⟨301532, by rfl⟩) R603065
theorem R304235 : Reach 304235 := rs (se 1 (by rfl) ⟨228176, by rfl⟩) R456353
theorem R238747 : Reach 238747 := rs (se 1 (by rfl) ⟨179060, by rfl⟩) R358121
theorem R140777 : Reach 140777 := rs (se 2 (by rfl) ⟨52791, by rfl⟩) R105583
theorem R1058507 : Reach 1058507 := rs (se 1 (by rfl) ⟨793880, by rfl⟩) R1587761
theorem R141353 : Reach 141353 := rs (se 2 (by rfl) ⟨53007, by rfl⟩) R106015
theorem R207035 : Reach 207035 := rs (se 1 (by rfl) ⟨155276, by rfl⟩) R310553
theorem R141767 : Reach 141767 := rs (se 1 (by rfl) ⟨106325, by rfl⟩) R212651
theorem R338849 : Reach 338849 := rs (se 2 (by rfl) ⟨127068, by rfl⟩) R254137
theorem R306503 : Reach 306503 := rs (se 1 (by rfl) ⟨229877, by rfl⟩) R459755
theorem R208763 : Reach 208763 := rs (se 1 (by rfl) ⟨156572, by rfl⟩) R313145
theorem R208871 : Reach 208871 := rs (se 1 (by rfl) ⟨156653, by rfl⟩) R313307
theorem R209897 : Reach 209897 := rs (se 2 (by rfl) ⟨78711, by rfl⟩) R157423
theorem R2143739 : Reach 2143739 := rs (se 1 (by rfl) ⟨1607804, by rfl⟩) R3215609
theorem R2209451 : Reach 2209451 := rs (se 1 (by rfl) ⟨1657088, by rfl⟩) R3314177
theorem R26589505 : Reach 26589505 := rs (se 2 (by rfl) ⟨9971064, by rfl⟩) R19942129
theorem R309905 : Reach 309905 := rs (se 2 (by rfl) ⟨116214, by rfl⟩) R232429
theorem R473849 : Reach 473849 := rs (se 2 (by rfl) ⟨177693, by rfl⟩) R355387
theorem R211841 : Reach 211841 := rs (se 2 (by rfl) ⟨79440, by rfl⟩) R158881
theorem R670841 : Reach 670841 := rs (se 2 (by rfl) ⟨251565, by rfl⟩) R503131
theorem R1064083 : Reach 1064083 := rs (se 1 (by rfl) ⟨798062, by rfl⟩) R1596125
theorem R1064933 : Reach 1064933 := rs (se 4 (by rfl) ⟨99837, by rfl⟩) R199675
theorem R6603227 : Reach 6603227 := rs (se 1 (by rfl) ⟨4952420, by rfl⟩) R9904841
theorem R836185 : Reach 836185 := rs (se 2 (by rfl) ⟨313569, by rfl⟩) R627139
theorem R148969 : Reach 148969 := rs (se 2 (by rfl) ⟨55863, by rfl⟩) R111727
theorem R1984601 : Reach 1984601 := rs (se 2 (by rfl) ⟨744225, by rfl⟩) R1488451
theorem R149759 : Reach 149759 := rs (se 1 (by rfl) ⟨112319, by rfl⟩) R224639
theorem R150943 : Reach 150943 := rs (se 1 (by rfl) ⟨113207, by rfl⟩) R226415
theorem R1462967 : Reach 1462967 := rs (se 1 (by rfl) ⟨1097225, by rfl⟩) R2194451
theorem R512851 : Reach 512851 := rs (se 1 (by rfl) ⟨384638, by rfl⟩) R769277
theorem R645029 : Reach 645029 := rs (se 4 (by rfl) ⟨60471, by rfl⟩) R120943
theorem R88175 : Reach 88175 := rs (se 1 (by rfl) ⟨66131, by rfl⟩) R132263
theorem R219419 : Reach 219419 := rs (se 1 (by rfl) ⟨164564, by rfl⟩) R329129
theorem R317753 : Reach 317753 := rs (se 2 (by rfl) ⟨119157, by rfl⟩) R238315
theorem R907649 : Reach 907649 := rs (se 2 (by rfl) ⟨340368, by rfl⟩) R680737
theorem R285191 : Reach 285191 := rs (se 1 (by rfl) ⟨213893, by rfl⟩) R427787
theorem R1137361 : Reach 1137361 := rs (se 2 (by rfl) ⟨426510, by rfl⟩) R853021
theorem R89711 : Reach 89711 := rs (se 1 (by rfl) ⟨67283, by rfl⟩) R134567
theorem R876167 : Reach 876167 := rs (se 1 (by rfl) ⟨657125, by rfl⟩) R1314251
theorem R3432223 : Reach 3432223 := rs (se 1 (by rfl) ⟨2574167, by rfl⟩) R5148335
theorem R90395 : Reach 90395 := rs (se 1 (by rfl) ⟨67796, by rfl⟩) R135593
theorem R1466657 : Reach 1466657 := rs (se 2 (by rfl) ⟨549996, by rfl⟩) R1099993
theorem R90863 : Reach 90863 := rs (se 1 (by rfl) ⟨68147, by rfl⟩) R136295
theorem R320381 : Reach 320381 := rs (se 3 (by rfl) ⟨60071, by rfl⟩) R120143
theorem R91103 : Reach 91103 := rs (se 1 (by rfl) ⟨68327, by rfl⟩) R136655
theorem R779939 : Reach 779939 := rs (se 1 (by rfl) ⟨584954, by rfl⟩) R1169909
theorem R91913 : Reach 91913 := rs (se 2 (by rfl) ⟨34467, by rfl⟩) R68935
theorem R1238813 : Reach 1238813 := rs (se 3 (by rfl) ⟨232277, by rfl⟩) R464555
theorem R1042415 : Reach 1042415 := rs (se 1 (by rfl) ⟨781811, by rfl⟩) R1563623
theorem R92215 : Reach 92215 := rs (se 1 (by rfl) ⟨69161, by rfl⟩) R138323
theorem R59455 : Reach 59455 := rs (se 1 (by rfl) ⟨44591, by rfl⟩) R89183
theorem R92411 : Reach 92411 := rs (se 1 (by rfl) ⟨69308, by rfl⟩) R138617
theorem R92537 : Reach 92537 := rs (se 2 (by rfl) ⟨34701, by rfl⟩) R69403
theorem R92543 : Reach 92543 := rs (se 1 (by rfl) ⟨69407, by rfl⟩) R138815
theorem R59855 : Reach 59855 := rs (se 1 (by rfl) ⟨44891, by rfl⟩) R89783
theorem R59887 : Reach 59887 := rs (se 1 (by rfl) ⟨44915, by rfl⟩) R89831
theorem R92903 : Reach 92903 := rs (se 1 (by rfl) ⟨69677, by rfl⟩) R139355
theorem R191423 : Reach 191423 := rs (se 1 (by rfl) ⟨143567, by rfl⟩) R287135
theorem R93467 : Reach 93467 := rs (se 1 (by rfl) ⟨70100, by rfl⟩) R140201
theorem R1600883 : Reach 1600883 := rs (se 1 (by rfl) ⟨1200662, by rfl⟩) R2401325
theorem R93737 : Reach 93737 := rs (se 2 (by rfl) ⟨35151, by rfl⟩) R70303
theorem R93743 : Reach 93743 := rs (se 1 (by rfl) ⟨70307, by rfl⟩) R140615
theorem R93833 : Reach 93833 := rs (se 2 (by rfl) ⟨35187, by rfl⟩) R70375
theorem R61087 : Reach 61087 := rs (se 1 (by rfl) ⟨45815, by rfl⟩) R91631
theorem R93887 : Reach 93887 := rs (se 1 (by rfl) ⟨70415, by rfl⟩) R140831
theorem R93935 : Reach 93935 := rs (se 1 (by rfl) ⟨70451, by rfl⟩) R140903
theorem R192719 : Reach 192719 := rs (se 1 (by rfl) ⟨144539, by rfl⟩) R289079
theorem R94505 : Reach 94505 := rs (se 2 (by rfl) ⟨35439, by rfl⟩) R70879
theorem R553355 : Reach 553355 := rs (se 1 (by rfl) ⟨415016, by rfl⟩) R830033
theorem R258461 : Reach 258461 := rs (se 3 (by rfl) ⟨48461, by rfl⟩) R96923
theorem R62107 : Reach 62107 := rs (se 1 (by rfl) ⟨46580, by rfl⟩) R93161
theorem R62331 : Reach 62331 := rs (se 1 (by rfl) ⟨46748, by rfl⟩) R93497
theorem R914323 : Reach 914323 := rs (se 1 (by rfl) ⟨685742, by rfl⟩) R1371485
theorem R1209275 : Reach 1209275 := rs (se 1 (by rfl) ⟨906956, by rfl⟩) R1813913
theorem R1176605 : Reach 1176605 := rs (se 3 (by rfl) ⟨220613, by rfl⟩) R441227
theorem R227431 : Reach 227431 := rs (se 1 (by rfl) ⟨170573, by rfl⟩) R341147
theorem R1800323 : Reach 1800323 := rs (se 1 (by rfl) ⟨1350242, by rfl⟩) R2700485
theorem R2030629 : Reach 2030629 := rs (se 4 (by rfl) ⟨190371, by rfl⟩) R380743
theorem R195691 : Reach 195691 := rs (se 1 (by rfl) ⟨146768, by rfl⟩) R293537
theorem R818383 : Reach 818383 := rs (se 1 (by rfl) ⟨613787, by rfl⟩) R1227575
theorem R1637729 : Reach 1637729 := rs (se 2 (by rfl) ⟨614148, by rfl⟩) R1228297
theorem R1212965 : Reach 1212965 := rs (se 4 (by rfl) ⟨113715, by rfl⟩) R227431
theorem R1114913 : Reach 1114913 := rs (se 2 (by rfl) ⟨418092, by rfl⟩) R836185
theorem R99839 : Reach 99839 := rs (se 1 (by rfl) ⟨74879, by rfl⟩) R149759
theorem R198625 : Reach 198625 := rs (se 2 (by rfl) ⟨74484, by rfl⟩) R148969
theorem R133289 : Reach 133289 := rs (se 2 (by rfl) ⟨49983, by rfl⟩) R99967
theorem R4197095 : Reach 4197095 := rs (se 1 (by rfl) ⟨3147821, by rfl⟩) R6295643
theorem R133919 : Reach 133919 := rs (se 1 (by rfl) ⟨100439, by rfl⟩) R200879
theorem R133991 : Reach 133991 := rs (se 1 (by rfl) ⟨100493, by rfl⟩) R200987
theorem R134399 : Reach 134399 := rs (se 1 (by rfl) ⟨100799, by rfl⟩) R201599
theorem R430019 : Reach 430019 := rs (se 1 (by rfl) ⟨322514, by rfl⟩) R645029
theorem R1315115 : Reach 1315115 := rs (se 1 (by rfl) ⟨986336, by rfl⟩) R1972673
theorem R135503 : Reach 135503 := rs (se 1 (by rfl) ⟨101627, by rfl⟩) R203255
theorem R201257 : Reach 201257 := rs (se 2 (by rfl) ⟨75471, by rfl⟩) R150943
theorem R135737 : Reach 135737 := rs (se 2 (by rfl) ⟨50901, by rfl⟩) R101803
theorem R136169 : Reach 136169 := rs (se 2 (by rfl) ⟨51063, by rfl⟩) R102127
theorem R235133 : Reach 235133 := rs (se 3 (by rfl) ⟨44087, by rfl⟩) R88175
theorem R202823 : Reach 202823 := rs (se 1 (by rfl) ⟨152117, by rfl⟩) R304235
theorem R137465 : Reach 137465 := rs (se 2 (by rfl) ⟨51549, by rfl⟩) R103099
theorem R137609 : Reach 137609 := rs (se 2 (by rfl) ⟨51603, by rfl⟩) R103207
theorem R825875 : Reach 825875 := rs (se 1 (by rfl) ⟨619406, by rfl⟩) R1238813
theorem R1219097 : Reach 1219097 := rs (se 2 (by rfl) ⟨457161, by rfl⟩) R914323
theorem R694943 : Reach 694943 := rs (se 1 (by rfl) ⟨521207, by rfl⟩) R1042415
theorem R138023 : Reach 138023 := rs (se 1 (by rfl) ⟨103517, by rfl⟩) R207035
theorem R138401 : Reach 138401 := rs (se 2 (by rfl) ⟨51900, by rfl⟩) R103801
theorem R204335 : Reach 204335 := rs (se 1 (by rfl) ⟨153251, by rfl⟩) R306503
theorem R139175 : Reach 139175 := rs (se 1 (by rfl) ⟨104381, by rfl⟩) R208763
theorem R139247 : Reach 139247 := rs (se 1 (by rfl) ⟨104435, by rfl⟩) R208871
theorem R368903 : Reach 368903 := rs (se 1 (by rfl) ⟨276677, by rfl⟩) R553355
theorem R172307 : Reach 172307 := rs (se 1 (by rfl) ⟨129230, by rfl⟩) R258461
theorem R139931 : Reach 139931 := rs (se 1 (by rfl) ⟨104948, by rfl⟩) R209897
theorem R1516481 : Reach 1516481 := rs (se 2 (by rfl) ⟨568680, by rfl⟩) R1137361
theorem R1418777 : Reach 1418777 := rs (se 2 (by rfl) ⟨532041, by rfl⟩) R1064083
theorem R1091177 : Reach 1091177 := rs (se 2 (by rfl) ⟨409191, by rfl⟩) R818383
theorem R206603 : Reach 206603 := rs (se 1 (by rfl) ⟨154952, by rfl⟩) R309905
theorem R141227 : Reach 141227 := rs (se 1 (by rfl) ⟨105920, by rfl⟩) R211841
theorem R1091819 : Reach 1091819 := rs (se 1 (by rfl) ⟨818864, by rfl⟩) R1637729
theorem R797161 : Reach 797161 := rs (se 2 (by rfl) ⟨298935, by rfl⟩) R597871
theorem R306017 : Reach 306017 := rs (se 2 (by rfl) ⟨114756, by rfl⟩) R229513
theorem R4402151 : Reach 4402151 := rs (se 1 (by rfl) ⟨3301613, by rfl⟩) R6603227
theorem R536057 : Reach 536057 := rs (se 2 (by rfl) ⟨201021, by rfl⟩) R402043
theorem R1323067 : Reach 1323067 := rs (se 1 (by rfl) ⟨992300, by rfl⟩) R1984601
theorem R833753 : Reach 833753 := rs (se 2 (by rfl) ⟨312657, by rfl⟩) R625315
theorem R146279 : Reach 146279 := rs (se 1 (by rfl) ⟨109709, by rfl⟩) R219419
theorem R211835 : Reach 211835 := rs (se 1 (by rfl) ⟨158876, by rfl⟩) R317753
theorem R605099 : Reach 605099 := rs (se 1 (by rfl) ⟨453824, by rfl⟩) R907649
theorem R1490987 : Reach 1490987 := rs (se 1 (by rfl) ⟨1118240, by rfl⟩) R2236481
theorem R213587 : Reach 213587 := rs (se 1 (by rfl) ⟨160190, by rfl⟩) R320381
theorem R705671 : Reach 705671 := rs (se 1 (by rfl) ⟨529253, by rfl⟩) R1058507
theorem R443677 : Reach 443677 := rs (se 3 (by rfl) ⟨83189, by rfl⟩) R166379
theorem R1067255 : Reach 1067255 := rs (se 1 (by rfl) ⟨800441, by rfl⟩) R1600883
theorem R510461 : Reach 510461 := rs (se 3 (by rfl) ⟨95711, by rfl⟩) R191423
theorem R806183 : Reach 806183 := rs (se 1 (by rfl) ⟨604637, by rfl⟩) R1209275
theorem R1429159 : Reach 1429159 := rs (se 1 (by rfl) ⟨1071869, by rfl⟩) R2143739
theorem R2707505 : Reach 2707505 := rs (se 2 (by rfl) ⟨1015314, by rfl⟩) R2030629
theorem R1200215 : Reach 1200215 := rs (se 1 (by rfl) ⟨900161, by rfl⟩) R1800323
theorem R315899 : Reach 315899 := rs (se 1 (by rfl) ⟨236924, by rfl⟩) R473849
theorem R447227 : Reach 447227 := rs (se 1 (by rfl) ⟨335420, by rfl⟩) R670841
theorem R4576297 : Reach 4576297 := rs (se 2 (by rfl) ⟨1716111, by rfl⟩) R3432223
theorem R709955 : Reach 709955 := rs (se 1 (by rfl) ⟨532466, by rfl⟩) R1064933
theorem R152999 : Reach 152999 := rs (se 1 (by rfl) ⟨114749, by rfl⟩) R229499
theorem R218729 : Reach 218729 := rs (se 2 (by rfl) ⟨82023, by rfl⟩) R164047
theorem R88811 : Reach 88811 := rs (se 1 (by rfl) ⟨66608, by rfl⟩) R133217
theorem R318329 : Reach 318329 := rs (se 2 (by rfl) ⟨119373, by rfl⟩) R238747
theorem R154507 : Reach 154507 := rs (se 1 (by rfl) ⟨115880, by rfl⟩) R231761
theorem R89225 : Reach 89225 := rs (se 2 (by rfl) ⟨33459, by rfl⟩) R66919
theorem R89255 : Reach 89255 := rs (se 1 (by rfl) ⟨66941, by rfl⟩) R133883
theorem R155155 : Reach 155155 := rs (se 1 (by rfl) ⟨116366, by rfl⟩) R232733
theorem R155591 : Reach 155591 := rs (se 1 (by rfl) ⟨116693, by rfl⟩) R233387
theorem R122953 : Reach 122953 := rs (se 2 (by rfl) ⟨46107, by rfl⟩) R92215
theorem R975311 : Reach 975311 := rs (se 1 (by rfl) ⟨731483, by rfl⟩) R1462967
theorem R90599 : Reach 90599 := rs (se 1 (by rfl) ⟨67949, by rfl⟩) R135899
theorem R484217 : Reach 484217 := rs (se 2 (by rfl) ⟨181581, by rfl⟩) R363163
theorem R91001 : Reach 91001 := rs (se 2 (by rfl) ⟨34125, by rfl⟩) R68251
theorem R91049 : Reach 91049 := rs (se 2 (by rfl) ⟨34143, by rfl⟩) R68287
theorem R91751 : Reach 91751 := rs (se 1 (by rfl) ⟨68813, by rfl⟩) R137627
theorem R353929 : Reach 353929 := rs (se 2 (by rfl) ⟨132723, by rfl⟩) R265447
theorem R190127 : Reach 190127 := rs (se 1 (by rfl) ⟨142595, by rfl⟩) R285191
theorem R5891869 : Reach 5891869 := rs (se 3 (by rfl) ⟨1104725, by rfl⟩) R2209451
theorem R59807 : Reach 59807 := rs (se 1 (by rfl) ⟨44855, by rfl⟩) R89711
theorem R584111 : Reach 584111 := rs (se 1 (by rfl) ⟨438083, by rfl⟩) R876167
theorem R60263 : Reach 60263 := rs (se 1 (by rfl) ⟨45197, by rfl⟩) R90395
theorem R977771 : Reach 977771 := rs (se 1 (by rfl) ⟨733328, by rfl⟩) R1466657
theorem R60575 : Reach 60575 := rs (se 1 (by rfl) ⟨45431, by rfl⟩) R90863
theorem R60735 : Reach 60735 := rs (se 1 (by rfl) ⟨45551, by rfl⟩) R91103
theorem R93851 : Reach 93851 := rs (se 1 (by rfl) ⟨70388, by rfl⟩) R140777
theorem R519959 : Reach 519959 := rs (se 1 (by rfl) ⟨389969, by rfl⟩) R779939
theorem R683801 : Reach 683801 := rs (se 2 (by rfl) ⟨256425, by rfl⟩) R512851
theorem R61275 : Reach 61275 := rs (se 1 (by rfl) ⟨45956, by rfl⟩) R91913
theorem R94235 : Reach 94235 := rs (se 1 (by rfl) ⟨70676, by rfl⟩) R141353
theorem R61607 : Reach 61607 := rs (se 1 (by rfl) ⟨46205, by rfl⟩) R92411
theorem R61691 : Reach 61691 := rs (se 1 (by rfl) ⟨46268, by rfl⟩) R92537
theorem R61695 : Reach 61695 := rs (se 1 (by rfl) ⟨46271, by rfl⟩) R92543
theorem R94511 : Reach 94511 := rs (se 1 (by rfl) ⟨70883, by rfl⟩) R141767
theorem R61935 : Reach 61935 := rs (se 1 (by rfl) ⟨46451, by rfl⟩) R92903
theorem R225899 : Reach 225899 := rs (se 1 (by rfl) ⟨169424, by rfl⟩) R338849
theorem R62311 : Reach 62311 := rs (se 1 (by rfl) ⟨46733, by rfl⟩) R93467
theorem R62491 : Reach 62491 := rs (se 1 (by rfl) ⟨46868, by rfl⟩) R93737
theorem R62495 : Reach 62495 := rs (se 1 (by rfl) ⟨46871, by rfl⟩) R93743
theorem R62555 : Reach 62555 := rs (se 1 (by rfl) ⟨46916, by rfl⟩) R93833
theorem R62591 : Reach 62591 := rs (se 1 (by rfl) ⟨46943, by rfl⟩) R93887
theorem R62623 : Reach 62623 := rs (se 1 (by rfl) ⟨46967, by rfl⟩) R93935
theorem R128479 : Reach 128479 := rs (se 1 (by rfl) ⟨96359, by rfl⟩) R192719
theorem R63003 : Reach 63003 := rs (se 1 (by rfl) ⟨47252, by rfl⟩) R94505
theorem R35452673 : Reach 35452673 := rs (se 2 (by rfl) ⟨13294752, by rfl⟩) R26589505
theorem R784403 : Reach 784403 := rs (se 1 (by rfl) ⟨588302, by rfl⟩) R1176605
theorem R8485013 : Reach 8485013 := rs (se 6 (by rfl) ⟨198867, by rfl⟩) R397735
theorem R260921 : Reach 260921 := rs (se 2 (by rfl) ⟨97845, by rfl⟩) R195691
theorem R163937 : Reach 163937 := rs (se 2 (by rfl) ⟨61476, by rfl⟩) R122953
theorem R66559 : Reach 66559 := rs (se 1 (by rfl) ⟨49919, by rfl⟩) R99839
theorem R591569 : Reach 591569 := rs (se 2 (by rfl) ⟨221838, by rfl⟩) R443677
theorem R264833 : Reach 264833 := rs (se 2 (by rfl) ⟨99312, by rfl⟩) R198625
theorem R1805003 : Reach 1805003 := rs (se 1 (by rfl) ⟨1353752, by rfl⟩) R2707505
theorem R134171 : Reach 134171 := rs (se 1 (by rfl) ⟨100628, by rfl⟩) R201257
theorem R298151 : Reach 298151 := rs (se 1 (by rfl) ⟨223613, by rfl⟩) R447227
theorem R101999 : Reach 101999 := rs (se 1 (by rfl) ⟨76499, by rfl⟩) R152999
theorem R135215 : Reach 135215 := rs (se 1 (by rfl) ⟨101411, by rfl⟩) R202823
theorem R463295 : Reach 463295 := rs (se 1 (by rfl) ⟨347471, by rfl⟩) R694943
theorem R1905545 : Reach 1905545 := rs (se 2 (by rfl) ⟨714579, by rfl⟩) R1429159
theorem R136223 : Reach 136223 := rs (se 1 (by rfl) ⟨102167, by rfl⟩) R204335
theorem R103727 : Reach 103727 := rs (se 1 (by rfl) ⟨77795, by rfl⟩) R155591
theorem R727451 : Reach 727451 := rs (se 1 (by rfl) ⟨545588, by rfl⟩) R1091177
theorem R137735 : Reach 137735 := rs (se 1 (by rfl) ⟨103301, by rfl⟩) R206603
theorem R6101729 : Reach 6101729 := rs (se 2 (by rfl) ⟨2288148, by rfl⟩) R4576297
theorem R3250925 : Reach 3250925 := rs (se 3 (by rfl) ⟨609548, by rfl⟩) R1219097
theorem R727879 : Reach 727879 := rs (se 1 (by rfl) ⟨545909, by rfl⟩) R1091819
theorem R204011 : Reach 204011 := rs (se 1 (by rfl) ⟨153008, by rfl⟩) R306017
theorem R171305 : Reach 171305 := rs (se 2 (by rfl) ⟨64239, by rfl⟩) R128479
theorem R23635115 : Reach 23635115 := rs (se 1 (by rfl) ⟨17726336, by rfl⟩) R35452673
theorem R206009 : Reach 206009 := rs (se 2 (by rfl) ⟨77253, by rfl⟩) R154507
theorem R173947 : Reach 173947 := rs (se 1 (by rfl) ⟨130460, by rfl⟩) R260921
theorem R141223 : Reach 141223 := rs (se 1 (by rfl) ⟨105917, by rfl⟩) R211835
theorem R403399 : Reach 403399 := rs (se 1 (by rfl) ⟨302549, by rfl⟩) R605099
theorem R206873 : Reach 206873 := rs (se 2 (by rfl) ⟨77577, by rfl⟩) R155155
theorem R3975965 : Reach 3975965 := rs (se 3 (by rfl) ⟨745493, by rfl⟩) R1490987
theorem R142391 : Reach 142391 := rs (se 1 (by rfl) ⟨106793, by rfl⟩) R213587
theorem R470447 : Reach 470447 := rs (se 1 (by rfl) ⟨352835, by rfl⟩) R705671
theorem R340307 : Reach 340307 := rs (se 1 (by rfl) ⟨255230, by rfl⟩) R510461
theorem R2798063 : Reach 2798063 := rs (se 1 (by rfl) ⟨2098547, by rfl⟩) R4197095
theorem R471905 : Reach 471905 := rs (se 2 (by rfl) ⟨176964, by rfl⟩) R353929
theorem R537455 : Reach 537455 := rs (se 1 (by rfl) ⟨403091, by rfl⟩) R806183
theorem R210599 : Reach 210599 := rs (se 1 (by rfl) ⟨157949, by rfl⟩) R315899
theorem R1062881 : Reach 1062881 := rs (se 2 (by rfl) ⟨398580, by rfl⟩) R797161
theorem R473303 : Reach 473303 := rs (se 1 (by rfl) ⟨354977, by rfl⟩) R709955
theorem R145819 : Reach 145819 := rs (se 1 (by rfl) ⟨109364, by rfl⟩) R218729
theorem R507005 : Reach 507005 := rs (se 3 (by rfl) ⟨95063, by rfl⟩) R190127
theorem R212219 : Reach 212219 := rs (se 1 (by rfl) ⟨159164, by rfl⟩) R318329
theorem R245935 : Reach 245935 := rs (se 1 (by rfl) ⟨184451, by rfl⟩) R368903
theorem R114871 : Reach 114871 := rs (se 1 (by rfl) ⟨86153, by rfl⟩) R172307
theorem R2934767 : Reach 2934767 := rs (se 1 (by rfl) ⟨2201075, by rfl⟩) R4402151
theorem R346639 : Reach 346639 := rs (se 1 (by rfl) ⟨259979, by rfl⟩) R519959
theorem R150599 : Reach 150599 := rs (se 1 (by rfl) ⟨112949, by rfl⟩) R225899
theorem R5656675 : Reach 5656675 := rs (se 1 (by rfl) ⟨4242506, by rfl⟩) R8485013
theorem R3200573 : Reach 3200573 := rs (se 3 (by rfl) ⟨600107, by rfl⟩) R1200215
theorem R808643 : Reach 808643 := rs (se 1 (by rfl) ⟨606482, by rfl⟩) R1212965
theorem R743275 : Reach 743275 := rs (se 1 (by rfl) ⟨557456, by rfl⟩) R1114913
theorem R88859 : Reach 88859 := rs (se 1 (by rfl) ⟨66644, by rfl⟩) R133289
theorem R711503 : Reach 711503 := rs (se 1 (by rfl) ⟨533627, by rfl⟩) R1067255
theorem R89279 : Reach 89279 := rs (se 1 (by rfl) ⟨66959, by rfl⟩) R133919
theorem R89327 : Reach 89327 := rs (se 1 (by rfl) ⟨66995, by rfl⟩) R133991
theorem R89599 : Reach 89599 := rs (se 1 (by rfl) ⟨67199, by rfl⟩) R134399
theorem R7855825 : Reach 7855825 := rs (se 2 (by rfl) ⟨2945934, by rfl⟩) R5891869
theorem R286679 : Reach 286679 := rs (se 1 (by rfl) ⟨215009, by rfl⟩) R430019
theorem R876743 : Reach 876743 := rs (se 1 (by rfl) ⟨657557, by rfl⟩) R1315115
theorem R90335 : Reach 90335 := rs (se 1 (by rfl) ⟨67751, by rfl⟩) R135503
theorem R90491 : Reach 90491 := rs (se 1 (by rfl) ⟨67868, by rfl⟩) R135737
theorem R90779 : Reach 90779 := rs (se 1 (by rfl) ⟨68084, by rfl⟩) R136169
theorem R156755 : Reach 156755 := rs (se 1 (by rfl) ⟨117566, by rfl⟩) R235133
theorem R91643 : Reach 91643 := rs (se 1 (by rfl) ⟨68732, by rfl⟩) R137465
theorem R91739 : Reach 91739 := rs (se 1 (by rfl) ⟨68804, by rfl⟩) R137609
theorem R550583 : Reach 550583 := rs (se 1 (by rfl) ⟨412937, by rfl⟩) R825875
theorem R59207 : Reach 59207 := rs (se 1 (by rfl) ⟨44405, by rfl⟩) R88811
theorem R92015 : Reach 92015 := rs (se 1 (by rfl) ⟨69011, by rfl⟩) R138023
theorem R59483 : Reach 59483 := rs (se 1 (by rfl) ⟨44612, by rfl⟩) R89225
theorem R92267 : Reach 92267 := rs (se 1 (by rfl) ⟨69200, by rfl⟩) R138401
theorem R59503 : Reach 59503 := rs (se 1 (by rfl) ⟨44627, by rfl⟩) R89255
theorem R92783 : Reach 92783 := rs (se 1 (by rfl) ⟨69587, by rfl⟩) R139175
theorem R92831 : Reach 92831 := rs (se 1 (by rfl) ⟨69623, by rfl⟩) R139247
theorem R1764089 : Reach 1764089 := rs (se 2 (by rfl) ⟨661533, by rfl⟩) R1323067
theorem R650207 : Reach 650207 := rs (se 1 (by rfl) ⟨487655, by rfl⟩) R975311
theorem R60399 : Reach 60399 := rs (se 1 (by rfl) ⟨45299, by rfl⟩) R90599
theorem R93287 : Reach 93287 := rs (se 1 (by rfl) ⟨69965, by rfl⟩) R139931
theorem R322811 : Reach 322811 := rs (se 1 (by rfl) ⟨242108, by rfl⟩) R484217
theorem R60667 : Reach 60667 := rs (se 1 (by rfl) ⟨45500, by rfl⟩) R91001
theorem R60699 : Reach 60699 := rs (se 1 (by rfl) ⟨45524, by rfl⟩) R91049
theorem R1010987 : Reach 1010987 := rs (se 1 (by rfl) ⟨758240, by rfl⟩) R1516481
theorem R945851 : Reach 945851 := rs (se 1 (by rfl) ⟨709388, by rfl⟩) R1418777
theorem R61167 : Reach 61167 := rs (se 1 (by rfl) ⟨45875, by rfl⟩) R91751
theorem R94151 : Reach 94151 := rs (se 1 (by rfl) ⟨70613, by rfl⟩) R141227
theorem R389407 : Reach 389407 := rs (se 1 (by rfl) ⟨292055, by rfl⟩) R584111
theorem R651847 : Reach 651847 := rs (se 1 (by rfl) ⟨488885, by rfl⟩) R977771
theorem R357371 : Reach 357371 := rs (se 1 (by rfl) ⟨268028, by rfl⟩) R536057
theorem R62567 : Reach 62567 := rs (se 1 (by rfl) ⟨46925, by rfl⟩) R93851
theorem R455867 : Reach 455867 := rs (se 1 (by rfl) ⟨341900, by rfl⟩) R683801
theorem R62823 : Reach 62823 := rs (se 1 (by rfl) ⟨47117, by rfl⟩) R94235
theorem R63007 : Reach 63007 := rs (se 1 (by rfl) ⟨47255, by rfl⟩) R94511
theorem R522935 : Reach 522935 := rs (se 1 (by rfl) ⟨392201, by rfl⟩) R784403
theorem R555835 : Reach 555835 := rs (se 1 (by rfl) ⟨416876, by rfl⟩) R833753
theorem R97519 : Reach 97519 := rs (se 1 (by rfl) ⟨73139, by rfl⟩) R146279
theorem R1311653 : Reach 1311653 := rs (se 4 (by rfl) ⟨122967, by rfl⟩) R245935
theorem R394379 : Reach 394379 := rs (se 1 (by rfl) ⟨295784, by rfl⟩) R591569
theorem R100399 : Reach 100399 := rs (se 1 (by rfl) ⟨75299, by rfl⟩) R150599
theorem R198767 : Reach 198767 := rs (se 1 (by rfl) ⟨149075, by rfl⟩) R298151
theorem R67999 : Reach 67999 := rs (se 1 (by rfl) ⟨50999, by rfl⟩) R101999
theorem R231929 : Reach 231929 := rs (se 2 (by rfl) ⟨86973, by rfl⟩) R173947
theorem R462185 : Reach 462185 := rs (se 2 (by rfl) ⟨173319, by rfl⟩) R346639
theorem R69151 : Reach 69151 := rs (se 1 (by rfl) ⟨51863, by rfl⟩) R103727
theorem R2133715 : Reach 2133715 := rs (se 1 (by rfl) ⟨1600286, by rfl⟩) R3200573
theorem R4067819 : Reach 4067819 := rs (se 1 (by rfl) ⟨3050864, by rfl⟩) R6101729
theorem R2167283 : Reach 2167283 := rs (se 1 (by rfl) ⟨1625462, by rfl⟩) R3250925
theorem R136007 : Reach 136007 := rs (se 1 (by rfl) ⟨102005, by rfl⟩) R204011
theorem R7542233 : Reach 7542233 := rs (se 2 (by rfl) ⟨2828337, by rfl⟩) R5656675
theorem R104503 : Reach 104503 := rs (se 1 (by rfl) ⟨78377, by rfl⟩) R156755
theorem R137339 : Reach 137339 := rs (se 1 (by rfl) ⟨103004, by rfl⟩) R206009
theorem R367055 : Reach 367055 := rs (se 1 (by rfl) ⟨275291, by rfl⟩) R550583
theorem R137915 : Reach 137915 := rs (se 1 (by rfl) ⟨103436, by rfl⟩) R206873
theorem R433471 : Reach 433471 := rs (se 1 (by rfl) ⟨325103, by rfl⟩) R650207
theorem R991033 : Reach 991033 := rs (se 2 (by rfl) ⟨371637, by rfl⟩) R743275
theorem R238247 : Reach 238247 := rs (se 1 (by rfl) ⟨178685, by rfl⟩) R357371
theorem R303911 : Reach 303911 := rs (se 1 (by rfl) ⟨227933, by rfl⟩) R455867
theorem R140399 : Reach 140399 := rs (se 1 (by rfl) ⟨105299, by rfl⟩) R210599
theorem R338003 : Reach 338003 := rs (se 1 (by rfl) ⟨253502, by rfl⟩) R507005
theorem R141479 : Reach 141479 := rs (se 1 (by rfl) ⟨106109, by rfl⟩) R212219
theorem R109291 : Reach 109291 := rs (se 1 (by rfl) ⟨81968, by rfl⟩) R163937
theorem R176555 : Reach 176555 := rs (se 1 (by rfl) ⟨132416, by rfl⟩) R264833
theorem R308863 : Reach 308863 := rs (se 1 (by rfl) ⟨231647, by rfl⟩) R463295
theorem R539095 : Reach 539095 := rs (se 1 (by rfl) ⟨404321, by rfl⟩) R808643
theorem R474335 : Reach 474335 := rs (se 1 (by rfl) ⟨355751, by rfl⟩) R711503
theorem R114203 : Reach 114203 := rs (se 1 (by rfl) ⟨85652, by rfl⟩) R171305
theorem R1262141 : Reach 1262141 := rs (se 3 (by rfl) ⟨236651, by rfl⟩) R473303
theorem R869129 : Reach 869129 := rs (se 2 (by rfl) ⟨325923, by rfl⟩) R651847
theorem R215207 : Reach 215207 := rs (se 1 (by rfl) ⟨161405, by rfl⟩) R322811
theorem R673991 : Reach 673991 := rs (se 1 (by rfl) ⟨505493, by rfl⟩) R1010987
theorem R313631 : Reach 313631 := rs (se 1 (by rfl) ⟨235223, by rfl⟩) R470447
theorem R314603 : Reach 314603 := rs (se 1 (by rfl) ⟨235952, by rfl⟩) R471905
theorem R741113 : Reach 741113 := rs (se 2 (by rfl) ⟨277917, by rfl⟩) R555835
theorem R970505 : Reach 970505 := rs (se 2 (by rfl) ⟨363939, by rfl⟩) R727879
theorem R708587 : Reach 708587 := rs (se 1 (by rfl) ⟨531440, by rfl⟩) R1062881
theorem R348623 : Reach 348623 := rs (se 1 (by rfl) ⟨261467, by rfl⟩) R522935
theorem R119465 : Reach 119465 := rs (se 2 (by rfl) ⟨44799, by rfl⟩) R89599
theorem R10474433 : Reach 10474433 := rs (se 2 (by rfl) ⟨3927912, by rfl⟩) R7855825
theorem R2151461 : Reach 2151461 := rs (se 4 (by rfl) ⟨201699, by rfl⟩) R403399
theorem R153161 : Reach 153161 := rs (se 2 (by rfl) ⟨57435, by rfl⟩) R114871
theorem R1956511 : Reach 1956511 := rs (se 1 (by rfl) ⟨1467383, by rfl⟩) R2934767
theorem R88745 : Reach 88745 := rs (se 2 (by rfl) ⟨33279, by rfl⟩) R66559
theorem R1203335 : Reach 1203335 := rs (se 1 (by rfl) ⟨902501, by rfl⟩) R1805003
theorem R89447 : Reach 89447 := rs (se 1 (by rfl) ⟨67085, by rfl⟩) R134171
theorem R777701 : Reach 777701 := rs (se 4 (by rfl) ⟨72909, by rfl⟩) R145819
theorem R188297 : Reach 188297 := rs (se 2 (by rfl) ⟨70611, by rfl⟩) R141223
theorem R90143 : Reach 90143 := rs (se 1 (by rfl) ⟨67607, by rfl⟩) R135215
theorem R1270363 : Reach 1270363 := rs (se 1 (by rfl) ⟨952772, by rfl⟩) R1905545
theorem R90815 : Reach 90815 := rs (se 1 (by rfl) ⟨68111, by rfl⟩) R136223
theorem R484967 : Reach 484967 := rs (se 1 (by rfl) ⟨363725, by rfl⟩) R727451
theorem R91823 : Reach 91823 := rs (se 1 (by rfl) ⟨68867, by rfl⟩) R137735
theorem R59239 : Reach 59239 := rs (se 1 (by rfl) ⟨44429, by rfl⟩) R88859
theorem R59519 : Reach 59519 := rs (se 1 (by rfl) ⟨44639, by rfl⟩) R89279
theorem R59551 : Reach 59551 := rs (se 1 (by rfl) ⟨44663, by rfl⟩) R89327
theorem R191119 : Reach 191119 := rs (se 1 (by rfl) ⟨143339, by rfl⟩) R286679
theorem R584495 : Reach 584495 := rs (se 1 (by rfl) ⟨438371, by rfl⟩) R876743
theorem R60223 : Reach 60223 := rs (se 1 (by rfl) ⟨45167, by rfl⟩) R90335
theorem R60327 : Reach 60327 := rs (se 1 (by rfl) ⟨45245, by rfl⟩) R90491
theorem R519209 : Reach 519209 := rs (se 2 (by rfl) ⟨194703, by rfl⟩) R389407
theorem R60519 : Reach 60519 := rs (se 1 (by rfl) ⟨45389, by rfl⟩) R90779
theorem R15756743 : Reach 15756743 := rs (se 1 (by rfl) ⟨11817557, by rfl⟩) R23635115
theorem R61095 : Reach 61095 := rs (se 1 (by rfl) ⟨45821, by rfl⟩) R91643
theorem R61159 : Reach 61159 := rs (se 1 (by rfl) ⟨45869, by rfl⟩) R91739
theorem R61343 : Reach 61343 := rs (se 1 (by rfl) ⟨46007, by rfl⟩) R92015
theorem R61511 : Reach 61511 := rs (se 1 (by rfl) ⟨46133, by rfl⟩) R92267
theorem R61855 : Reach 61855 := rs (se 1 (by rfl) ⟨46391, by rfl⟩) R92783
theorem R61887 : Reach 61887 := rs (se 1 (by rfl) ⟨46415, by rfl⟩) R92831
theorem R1176059 : Reach 1176059 := rs (se 1 (by rfl) ⟨882044, by rfl⟩) R1764089
theorem R2650643 : Reach 2650643 := rs (se 1 (by rfl) ⟨1987982, by rfl⟩) R3975965
theorem R94927 : Reach 94927 := rs (se 1 (by rfl) ⟨71195, by rfl⟩) R142391
theorem R62191 : Reach 62191 := rs (se 1 (by rfl) ⟨46643, by rfl⟩) R93287
theorem R62767 : Reach 62767 := rs (se 1 (by rfl) ⟨47075, by rfl⟩) R94151
theorem R226871 : Reach 226871 := rs (se 1 (by rfl) ⟨170153, by rfl⟩) R340307
theorem R1865375 : Reach 1865375 := rs (se 1 (by rfl) ⟨1399031, by rfl⟩) R2798063
theorem R358303 : Reach 358303 := rs (se 1 (by rfl) ⟨268727, by rfl⟩) R537455
theorem R130025 : Reach 130025 := rs (se 2 (by rfl) ⟨48759, by rfl⟩) R97519
theorem R2522269 : Reach 2522269 := rs (se 3 (by rfl) ⟨472925, by rfl⟩) R945851
theorem R262919 : Reach 262919 := rs (se 1 (by rfl) ⟨197189, by rfl⟩) R394379
theorem R132511 : Reach 132511 := rs (se 1 (by rfl) ⟨99383, by rfl⟩) R198767
theorem R494075 : Reach 494075 := rs (se 1 (by rfl) ⟨370556, by rfl⟩) R741113
theorem R133865 : Reach 133865 := rs (se 2 (by rfl) ⟨50199, by rfl⟩) R100399
theorem R232415 : Reach 232415 := rs (se 1 (by rfl) ⟨174311, by rfl⟩) R348623
theorem R6982955 : Reach 6982955 := rs (se 1 (by rfl) ⟨5237216, by rfl⟩) R10474433
theorem R102107 : Reach 102107 := rs (se 1 (by rfl) ⟨76580, by rfl⟩) R153161
theorem R202607 : Reach 202607 := rs (se 1 (by rfl) ⟨151955, by rfl⟩) R303911
theorem R21142037 : Reach 21142037 := rs (se 6 (by rfl) ⟨495516, by rfl⟩) R991033
theorem R139337 : Reach 139337 := rs (se 2 (by rfl) ⟨52251, by rfl⟩) R104503
theorem R76135 : Reach 76135 := rs (se 1 (by rfl) ⟨57101, by rfl⟩) R114203
theorem R5779421 : Reach 5779421 := rs (se 3 (by rfl) ⟨1083641, by rfl⟩) R2167283
theorem R143471 : Reach 143471 := rs (se 1 (by rfl) ⟨107603, by rfl⟩) R215207
theorem R209087 : Reach 209087 := rs (se 1 (by rfl) ⟨156815, by rfl⟩) R313631
theorem R209735 : Reach 209735 := rs (se 1 (by rfl) ⟨157301, by rfl⟩) R314603
theorem R308123 : Reach 308123 := rs (se 1 (by rfl) ⟨231092, by rfl⟩) R462185
theorem R78985 : Reach 78985 := rs (se 2 (by rfl) ⟨29619, by rfl⟩) R59239
theorem R472391 : Reach 472391 := rs (se 1 (by rfl) ⟨354293, by rfl⟩) R708587
theorem R79643 : Reach 79643 := rs (se 1 (by rfl) ⟨59732, by rfl⟩) R119465
theorem R145721 : Reach 145721 := rs (se 2 (by rfl) ⟨54645, by rfl⟩) R109291
theorem R5028155 : Reach 5028155 := rs (se 1 (by rfl) ⟨3771116, by rfl⟩) R7542233
theorem R244703 : Reach 244703 := rs (se 1 (by rfl) ⟨183527, by rfl⟩) R367055
theorem R802223 : Reach 802223 := rs (se 1 (by rfl) ⟨601667, by rfl⟩) R1203335
theorem R13452101 : Reach 13452101 := rs (se 4 (by rfl) ⟨1261134, by rfl⟩) R2522269
theorem R346139 : Reach 346139 := rs (se 1 (by rfl) ⟨259604, by rfl⟩) R519209
theorem R411817 : Reach 411817 := rs (se 2 (by rfl) ⟨154431, by rfl⟩) R308863
theorem R10504495 : Reach 10504495 := rs (se 1 (by rfl) ⟨7878371, by rfl⟩) R15756743
theorem R477737 : Reach 477737 := rs (se 2 (by rfl) ⟨179151, by rfl⟩) R358303
theorem R117703 : Reach 117703 := rs (se 1 (by rfl) ⟨88277, by rfl⟩) R176555
theorem R2608681 : Reach 2608681 := rs (se 2 (by rfl) ⟨978255, by rfl⟩) R1956511
theorem R151247 : Reach 151247 := rs (se 1 (by rfl) ⟨113435, by rfl⟩) R226871
theorem R577961 : Reach 577961 := rs (se 2 (by rfl) ⟨216735, by rfl⟩) R433471
theorem R86683 : Reach 86683 := rs (se 1 (by rfl) ⟨65012, by rfl⟩) R130025
theorem R316223 : Reach 316223 := rs (se 1 (by rfl) ⟨237167, by rfl⟩) R474335
theorem R841427 : Reach 841427 := rs (se 1 (by rfl) ⟨631070, by rfl⟩) R1262141
theorem R579419 : Reach 579419 := rs (se 1 (by rfl) ⟨434564, by rfl⟩) R869129
theorem R874435 : Reach 874435 := rs (se 1 (by rfl) ⟨655826, by rfl⟩) R1311653
theorem R1693817 : Reach 1693817 := rs (se 2 (by rfl) ⟨635181, by rfl⟩) R1270363
theorem R449327 : Reach 449327 := rs (se 1 (by rfl) ⟨336995, by rfl⟩) R673991
theorem R154619 : Reach 154619 := rs (se 1 (by rfl) ⟨115964, by rfl⟩) R231929
theorem R647003 : Reach 647003 := rs (se 1 (by rfl) ⟨485252, by rfl⟩) R970505
theorem R2711879 : Reach 2711879 := rs (se 1 (by rfl) ⟨2033909, by rfl⟩) R4067819
theorem R90665 : Reach 90665 := rs (se 2 (by rfl) ⟨33999, by rfl⟩) R67999
theorem R90671 : Reach 90671 := rs (se 1 (by rfl) ⟨68003, by rfl⟩) R136007
theorem R1434307 : Reach 1434307 := rs (se 1 (by rfl) ⟨1075730, by rfl⟩) R2151461
theorem R254825 : Reach 254825 := rs (se 2 (by rfl) ⟨95559, by rfl⟩) R191119
theorem R91559 : Reach 91559 := rs (se 1 (by rfl) ⟨68669, by rfl⟩) R137339
theorem R59163 : Reach 59163 := rs (se 1 (by rfl) ⟨44372, by rfl⟩) R88745
theorem R91943 : Reach 91943 := rs (se 1 (by rfl) ⟨68957, by rfl⟩) R137915
theorem R92201 : Reach 92201 := rs (se 2 (by rfl) ⟨34575, by rfl⟩) R69151
theorem R59631 : Reach 59631 := rs (se 1 (by rfl) ⟨44723, by rfl⟩) R89447
theorem R2844953 : Reach 2844953 := rs (se 2 (by rfl) ⟨1066857, by rfl⟩) R2133715
theorem R518467 : Reach 518467 := rs (se 1 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R125531 : Reach 125531 := rs (se 1 (by rfl) ⟨94148, by rfl⟩) R188297
theorem R60095 : Reach 60095 := rs (se 1 (by rfl) ⟨45071, by rfl⟩) R90143
theorem R158831 : Reach 158831 := rs (se 1 (by rfl) ⟨119123, by rfl⟩) R238247
theorem R60543 : Reach 60543 := rs (se 1 (by rfl) ⟨45407, by rfl⟩) R90815
theorem R93599 : Reach 93599 := rs (se 1 (by rfl) ⟨70199, by rfl⟩) R140399
theorem R126569 : Reach 126569 := rs (se 2 (by rfl) ⟨47463, by rfl⟩) R94927
theorem R323311 : Reach 323311 := rs (se 1 (by rfl) ⟨242483, by rfl⟩) R484967
theorem R61215 : Reach 61215 := rs (se 1 (by rfl) ⟨45911, by rfl⟩) R91823
theorem R225335 : Reach 225335 := rs (se 1 (by rfl) ⟨169001, by rfl⟩) R338003
theorem R94319 : Reach 94319 := rs (se 1 (by rfl) ⟨70739, by rfl⟩) R141479
theorem R389663 : Reach 389663 := rs (se 1 (by rfl) ⟨292247, by rfl⟩) R584495
theorem R784039 : Reach 784039 := rs (se 1 (by rfl) ⟨588029, by rfl⟩) R1176059
theorem R1767095 : Reach 1767095 := rs (se 1 (by rfl) ⟨1325321, by rfl⟩) R2650643
theorem R718793 : Reach 718793 := rs (se 2 (by rfl) ⟨269547, by rfl⟩) R539095
theorem R1243583 : Reach 1243583 := rs (se 1 (by rfl) ⟨932687, by rfl⟩) R1865375
theorem R230759 : Reach 230759 := rs (se 1 (by rfl) ⟨173069, by rfl⟩) R346139
theorem R329383 : Reach 329383 := rs (se 1 (by rfl) ⟨247037, by rfl⟩) R494075
theorem R4655303 : Reach 4655303 := rs (se 1 (by rfl) ⟨3491477, by rfl⟩) R6982955
theorem R100831 : Reach 100831 := rs (se 1 (by rfl) ⟨75623, by rfl⟩) R151247
theorem R68071 : Reach 68071 := rs (se 1 (by rfl) ⟨51053, by rfl⟩) R102107
theorem R691289 : Reach 691289 := rs (se 2 (by rfl) ⟨259233, by rfl⟩) R518467
theorem R101513 : Reach 101513 := rs (se 2 (by rfl) ⟨38067, by rfl⟩) R76135
theorem R560951 : Reach 560951 := rs (se 1 (by rfl) ⟨420713, by rfl⟩) R841427
theorem R135071 : Reach 135071 := rs (se 1 (by rfl) ⟨101303, by rfl⟩) R202607
theorem R14094691 : Reach 14094691 := rs (se 1 (by rfl) ⟨10571018, by rfl⟩) R21142037
theorem R299551 : Reach 299551 := rs (se 1 (by rfl) ⟨224663, by rfl⟩) R449327
theorem R103079 : Reach 103079 := rs (se 1 (by rfl) ⟨77309, by rfl⟩) R154619
theorem R3478241 : Reach 3478241 := rs (se 2 (by rfl) ⟨1304340, by rfl⟩) R2608681
theorem R431081 : Reach 431081 := rs (se 2 (by rfl) ⟨161655, by rfl⟩) R323311
theorem R431335 : Reach 431335 := rs (se 1 (by rfl) ⟨323501, by rfl⟩) R647003
theorem R1807919 : Reach 1807919 := rs (se 1 (by rfl) ⟨1355939, by rfl⟩) R2711879
theorem R169883 : Reach 169883 := rs (se 1 (by rfl) ⟨127412, by rfl⟩) R254825
theorem R105313 : Reach 105313 := rs (se 2 (by rfl) ⟨39492, by rfl⟩) R78985
theorem R105887 : Reach 105887 := rs (se 1 (by rfl) ⟨79415, by rfl⟩) R158831
theorem R139391 : Reach 139391 := rs (se 1 (by rfl) ⟨104543, by rfl⟩) R209087
theorem R139823 : Reach 139823 := rs (se 1 (by rfl) ⟨104867, by rfl⟩) R209735
theorem R205415 : Reach 205415 := rs (se 1 (by rfl) ⟨154061, by rfl⟩) R308123
theorem R3352103 : Reach 3352103 := rs (se 1 (by rfl) ⟨2514077, by rfl⟩) R5028155
theorem R337517 : Reach 337517 := rs (se 3 (by rfl) ⟨63284, by rfl⟩) R126569
theorem R829055 : Reach 829055 := rs (se 1 (by rfl) ⟨621791, by rfl⟩) R1243583
theorem R534815 : Reach 534815 := rs (se 1 (by rfl) ⟨401111, by rfl⟩) R802223
theorem R175279 : Reach 175279 := rs (se 1 (by rfl) ⟨131459, by rfl⟩) R262919
theorem R1912409 : Reach 1912409 := rs (se 2 (by rfl) ⟨717153, by rfl⟩) R1434307
theorem R176681 : Reach 176681 := rs (se 2 (by rfl) ⟨66255, by rfl⟩) R132511
theorem R14005993 : Reach 14005993 := rs (se 2 (by rfl) ⟨5252247, by rfl⟩) R10504495
theorem R210815 : Reach 210815 := rs (se 1 (by rfl) ⟨158111, by rfl⟩) R316223
theorem R1129211 : Reach 1129211 := rs (se 1 (by rfl) ⟨846908, by rfl⟩) R1693817
theorem R212381 : Reach 212381 := rs (se 3 (by rfl) ⟨39821, by rfl⟩) R79643
theorem R115577 : Reach 115577 := rs (se 2 (by rfl) ⟨43341, by rfl⟩) R86683
theorem R83687 : Reach 83687 := rs (se 1 (by rfl) ⟨62765, by rfl⟩) R125531
theorem R1165913 : Reach 1165913 := rs (se 2 (by rfl) ⟨437217, by rfl⟩) R874435
theorem R3852947 : Reach 3852947 := rs (se 1 (by rfl) ⟨2889710, by rfl⟩) R5779421
theorem R150223 : Reach 150223 := rs (se 1 (by rfl) ⟨112667, by rfl⟩) R225335
theorem R314927 : Reach 314927 := rs (se 1 (by rfl) ⟨236195, by rfl⟩) R472391
theorem R479195 : Reach 479195 := rs (se 1 (by rfl) ⟨359396, by rfl⟩) R718793
theorem R382589 : Reach 382589 := rs (se 3 (by rfl) ⟨71735, by rfl⟩) R143471
theorem R8968067 : Reach 8968067 := rs (se 1 (by rfl) ⟨6726050, by rfl⟩) R13452101
theorem R318491 : Reach 318491 := rs (se 1 (by rfl) ⟨238868, by rfl⟩) R477737
theorem R89243 : Reach 89243 := rs (se 1 (by rfl) ⟨66932, by rfl⟩) R133865
theorem R154943 : Reach 154943 := rs (se 1 (by rfl) ⟨116207, by rfl⟩) R232415
theorem R549089 : Reach 549089 := rs (se 2 (by rfl) ⟨205908, by rfl⟩) R411817
theorem R385307 : Reach 385307 := rs (se 1 (by rfl) ⟨288980, by rfl⟩) R577961
theorem R386279 : Reach 386279 := rs (se 1 (by rfl) ⟨289709, by rfl⟩) R579419
theorem R156937 : Reach 156937 := rs (se 2 (by rfl) ⟨58851, by rfl⟩) R117703
theorem R92891 : Reach 92891 := rs (se 1 (by rfl) ⟨69668, by rfl⟩) R139337
theorem R60443 : Reach 60443 := rs (se 1 (by rfl) ⟨45332, by rfl⟩) R90665
theorem R60447 : Reach 60447 := rs (se 1 (by rfl) ⟨45335, by rfl⟩) R90671
theorem R61039 : Reach 61039 := rs (se 1 (by rfl) ⟨45779, by rfl⟩) R91559
theorem R61295 : Reach 61295 := rs (se 1 (by rfl) ⟨45971, by rfl⟩) R91943
theorem R61467 : Reach 61467 := rs (se 1 (by rfl) ⟨46100, by rfl⟩) R92201
theorem R1896635 : Reach 1896635 := rs (se 1 (by rfl) ⟨1422476, by rfl⟩) R2844953
theorem R1045385 : Reach 1045385 := rs (se 2 (by rfl) ⟨392019, by rfl⟩) R784039
theorem R62399 : Reach 62399 := rs (se 1 (by rfl) ⟨46799, by rfl⟩) R93599
theorem R62879 : Reach 62879 := rs (se 1 (by rfl) ⟨47159, by rfl⟩) R94319
theorem R259775 : Reach 259775 := rs (se 1 (by rfl) ⟨194831, by rfl⟩) R389663
theorem R1178063 : Reach 1178063 := rs (se 1 (by rfl) ⟨883547, by rfl⟩) R1767095
theorem R97147 : Reach 97147 := rs (se 1 (by rfl) ⟨72860, by rfl⟩) R145721
theorem R163135 : Reach 163135 := rs (se 1 (by rfl) ⟨122351, by rfl⟩) R244703
theorem R75171685 : Reach 75171685 := rs (se 4 (by rfl) ⟨7047345, by rfl⟩) R14094691
theorem R9275309 : Reach 9275309 := rs (se 3 (by rfl) ⟨1739120, by rfl⟩) R3478241
theorem R460859 : Reach 460859 := rs (se 1 (by rfl) ⟨345644, by rfl⟩) R691289
theorem R67675 : Reach 67675 := rs (se 1 (by rfl) ⟨50756, by rfl⟩) R101513
theorem R68719 : Reach 68719 := rs (se 1 (by rfl) ⟨51539, by rfl⟩) R103079
theorem R134441 : Reach 134441 := rs (se 2 (by rfl) ⟨50415, by rfl⟩) R100831
theorem R200297 : Reach 200297 := rs (se 2 (by rfl) ⟨75111, by rfl⟩) R150223
theorem R233705 : Reach 233705 := rs (se 2 (by rfl) ⟨87639, by rfl⟩) R175279
theorem R103295 : Reach 103295 := rs (se 1 (by rfl) ⟨77471, by rfl⟩) R154943
theorem R70591 : Reach 70591 := rs (se 1 (by rfl) ⟨52943, by rfl⟩) R105887
theorem R366059 : Reach 366059 := rs (se 1 (by rfl) ⟨274544, by rfl⟩) R549089
theorem R136943 : Reach 136943 := rs (se 1 (by rfl) ⟨102707, by rfl⟩) R205415
theorem R399401 : Reach 399401 := rs (se 2 (by rfl) ⟨149775, by rfl⟩) R299551
theorem R2234735 : Reach 2234735 := rs (se 1 (by rfl) ⟨1676051, by rfl⟩) R3352103
theorem R696923 : Reach 696923 := rs (se 1 (by rfl) ⟨522692, by rfl⟩) R1045385
theorem R173183 : Reach 173183 := rs (se 1 (by rfl) ⟨129887, by rfl⟩) R259775
theorem R140417 : Reach 140417 := rs (se 2 (by rfl) ⟨52656, by rfl⟩) R105313
theorem R140543 : Reach 140543 := rs (se 1 (by rfl) ⟨105407, by rfl⟩) R210815
theorem R141587 : Reach 141587 := rs (se 1 (by rfl) ⟨106190, by rfl⟩) R212381
theorem R77051 : Reach 77051 := rs (se 1 (by rfl) ⟨57788, by rfl⟩) R115577
theorem R209249 : Reach 209249 := rs (se 2 (by rfl) ⟨78468, by rfl⟩) R156937
theorem R2568631 : Reach 2568631 := rs (se 1 (by rfl) ⟨1926473, by rfl⟩) R3852947
theorem R439177 : Reach 439177 := rs (se 2 (by rfl) ⟨164691, by rfl⟩) R329383
theorem R209951 : Reach 209951 := rs (se 1 (by rfl) ⟨157463, by rfl⟩) R314927
theorem R373967 : Reach 373967 := rs (se 1 (by rfl) ⟨280475, by rfl⟩) R560951
theorem R5978711 : Reach 5978711 := rs (se 1 (by rfl) ⟨4484033, by rfl⟩) R8968067
theorem R113255 : Reach 113255 := rs (se 1 (by rfl) ⟨84941, by rfl⟩) R169883
theorem R212327 : Reach 212327 := rs (se 1 (by rfl) ⟨159245, by rfl⟩) R318491
theorem R575113 : Reach 575113 := rs (se 2 (by rfl) ⟨215667, by rfl⟩) R431335
theorem R1264423 : Reach 1264423 := rs (se 1 (by rfl) ⟨948317, by rfl⟩) R1896635
theorem R117787 : Reach 117787 := rs (se 1 (by rfl) ⟨88340, by rfl⟩) R176681
theorem R217513 : Reach 217513 := rs (se 2 (by rfl) ⟨81567, by rfl⟩) R163135
theorem R153839 : Reach 153839 := rs (se 1 (by rfl) ⟨115379, by rfl⟩) R230759
theorem R3103535 : Reach 3103535 := rs (se 1 (by rfl) ⟨2327651, by rfl⟩) R4655303
theorem R777275 : Reach 777275 := rs (se 1 (by rfl) ⟨582956, by rfl⟩) R1165913
theorem R90047 : Reach 90047 := rs (se 1 (by rfl) ⟨67535, by rfl⟩) R135071
theorem R319463 : Reach 319463 := rs (se 1 (by rfl) ⟨239597, by rfl⟩) R479195
theorem R90761 : Reach 90761 := rs (se 2 (by rfl) ⟨34035, by rfl⟩) R68071
theorem R287387 : Reach 287387 := rs (se 1 (by rfl) ⟨215540, by rfl⟩) R431081
theorem R1205279 : Reach 1205279 := rs (se 1 (by rfl) ⟨903959, by rfl⟩) R1807919
theorem R255059 : Reach 255059 := rs (se 1 (by rfl) ⟨191294, by rfl⟩) R382589
theorem R223165 : Reach 223165 := rs (se 3 (by rfl) ⟨41843, by rfl⟩) R83687
theorem R59495 : Reach 59495 := rs (se 1 (by rfl) ⟨44621, by rfl⟩) R89243
theorem R92927 : Reach 92927 := rs (se 1 (by rfl) ⟨69695, by rfl⟩) R139391
theorem R256871 : Reach 256871 := rs (se 1 (by rfl) ⟨192653, by rfl⟩) R385307
theorem R93215 : Reach 93215 := rs (se 1 (by rfl) ⟨69911, by rfl⟩) R139823
theorem R257519 : Reach 257519 := rs (se 1 (by rfl) ⟨193139, by rfl⟩) R386279
theorem R225011 : Reach 225011 := rs (se 1 (by rfl) ⟨168758, by rfl⟩) R337517
theorem R552703 : Reach 552703 := rs (se 1 (by rfl) ⟨414527, by rfl⟩) R829055
theorem R356543 : Reach 356543 := rs (se 1 (by rfl) ⟨267407, by rfl⟩) R534815
theorem R61927 : Reach 61927 := rs (se 1 (by rfl) ⟨46445, by rfl⟩) R92891
theorem R18674657 : Reach 18674657 := rs (se 2 (by rfl) ⟨7002996, by rfl⟩) R14005993
theorem R1274939 : Reach 1274939 := rs (se 1 (by rfl) ⟨956204, by rfl⟩) R1912409
theorem R129529 : Reach 129529 := rs (se 2 (by rfl) ⟨48573, by rfl⟩) R97147
theorem R785375 : Reach 785375 := rs (se 1 (by rfl) ⟨589031, by rfl⟩) R1178063
theorem R752807 : Reach 752807 := rs (se 1 (by rfl) ⟨564605, by rfl⟩) R1129211
theorem R4915829 : Reach 4915829 := rs (se 5 (by rfl) ⟨230429, by rfl⟩) R460859
theorem R3803125 : Reach 3803125 := rs (se 5 (by rfl) ⟨178271, by rfl⟩) R356543
theorem R133531 : Reach 133531 := rs (se 1 (by rfl) ⟨100148, by rfl⟩) R200297
theorem R297553 : Reach 297553 := rs (se 2 (by rfl) ⟨111582, by rfl⟩) R223165
theorem R68863 : Reach 68863 := rs (se 1 (by rfl) ⟨51647, by rfl⟩) R103295
theorem R266267 : Reach 266267 := rs (se 1 (by rfl) ⟨199700, by rfl⟩) R399401
theorem R102559 : Reach 102559 := rs (se 1 (by rfl) ⟨76919, by rfl⟩) R153839
theorem R2069023 : Reach 2069023 := rs (se 1 (by rfl) ⟨1551767, by rfl⟩) R3103535
theorem R464615 : Reach 464615 := rs (se 1 (by rfl) ⟨348461, by rfl⟩) R696923
theorem R170039 : Reach 170039 := rs (se 1 (by rfl) ⟨127529, by rfl⟩) R255059
theorem R171247 : Reach 171247 := rs (se 1 (by rfl) ⟨128435, by rfl⟩) R256871
theorem R139499 : Reach 139499 := rs (se 1 (by rfl) ⟨104624, by rfl⟩) R209249
theorem R205469 : Reach 205469 := rs (se 3 (by rfl) ⟨38525, by rfl⟩) R77051
theorem R172705 : Reach 172705 := rs (se 2 (by rfl) ⟨64764, by rfl⟩) R129529
theorem R139967 : Reach 139967 := rs (se 1 (by rfl) ⟨104975, by rfl⟩) R209951
theorem R75503 : Reach 75503 := rs (se 1 (by rfl) ⟨56627, by rfl⟩) R113255
theorem R501871 : Reach 501871 := rs (se 1 (by rfl) ⟨376403, by rfl⟩) R752807
theorem R141551 : Reach 141551 := rs (se 1 (by rfl) ⟨106163, by rfl⟩) R212327
theorem R1847285 : Reach 1847285 := rs (se 5 (by rfl) ⟨86591, by rfl⟩) R173183
theorem R766817 : Reach 766817 := rs (se 2 (by rfl) ⟨287556, by rfl⟩) R575113
theorem R244039 : Reach 244039 := rs (se 1 (by rfl) ⟨183029, by rfl⟩) R366059
theorem R1685897 : Reach 1685897 := rs (se 2 (by rfl) ⟨632211, by rfl⟩) R1264423
theorem R1489823 : Reach 1489823 := rs (se 1 (by rfl) ⟨1117367, by rfl⟩) R2234735
theorem R736937 : Reach 736937 := rs (se 2 (by rfl) ⟨276351, by rfl⟩) R552703
theorem R212975 : Reach 212975 := rs (se 1 (by rfl) ⟨159731, by rfl⟩) R319463
theorem R3424841 : Reach 3424841 := rs (se 2 (by rfl) ⟨1284315, by rfl⟩) R2568631
theorem R803519 : Reach 803519 := rs (se 1 (by rfl) ⟨602639, by rfl⟩) R1205279
theorem R150007 : Reach 150007 := rs (se 1 (by rfl) ⟨112505, by rfl⟩) R225011
theorem R249311 : Reach 249311 := rs (se 1 (by rfl) ⟨186983, by rfl⟩) R373967
theorem R3985807 : Reach 3985807 := rs (se 1 (by rfl) ⟨2989355, by rfl⟩) R5978711
theorem R6183539 : Reach 6183539 := rs (se 1 (by rfl) ⟨4637654, by rfl⟩) R9275309
theorem R89627 : Reach 89627 := rs (se 1 (by rfl) ⟨67220, by rfl⟩) R134441
theorem R100228913 : Reach 100228913 := rs (se 2 (by rfl) ⟨37585842, by rfl⟩) R75171685
theorem R90233 : Reach 90233 := rs (se 2 (by rfl) ⟨33837, by rfl⟩) R67675
theorem R155803 : Reach 155803 := rs (se 1 (by rfl) ⟨116852, by rfl⟩) R233705
theorem R91295 : Reach 91295 := rs (se 1 (by rfl) ⟨68471, by rfl⟩) R136943
theorem R157049 : Reach 157049 := rs (se 2 (by rfl) ⟨58893, by rfl⟩) R117787
theorem R91625 : Reach 91625 := rs (se 2 (by rfl) ⟨34359, by rfl⟩) R68719
theorem R518183 : Reach 518183 := rs (se 1 (by rfl) ⟨388637, by rfl⟩) R777275
theorem R60031 : Reach 60031 := rs (se 1 (by rfl) ⟨45023, by rfl⟩) R90047
theorem R60507 : Reach 60507 := rs (se 1 (by rfl) ⟨45380, by rfl⟩) R90761
theorem R191591 : Reach 191591 := rs (se 1 (by rfl) ⟨143693, by rfl⟩) R287387
theorem R290017 : Reach 290017 := rs (se 2 (by rfl) ⟨108756, by rfl⟩) R217513
theorem R93611 : Reach 93611 := rs (se 1 (by rfl) ⟨70208, by rfl⟩) R140417
theorem R93695 : Reach 93695 := rs (se 1 (by rfl) ⟨70271, by rfl⟩) R140543
theorem R585569 : Reach 585569 := rs (se 2 (by rfl) ⟨219588, by rfl⟩) R439177
theorem R94121 : Reach 94121 := rs (se 2 (by rfl) ⟨35295, by rfl⟩) R70591
theorem R94391 : Reach 94391 := rs (se 1 (by rfl) ⟨70793, by rfl⟩) R141587
theorem R61951 : Reach 61951 := rs (se 1 (by rfl) ⟨46463, by rfl⟩) R92927
theorem R62143 : Reach 62143 := rs (se 1 (by rfl) ⟨46607, by rfl⟩) R93215
theorem R12449771 : Reach 12449771 := rs (se 1 (by rfl) ⟨9337328, by rfl⟩) R18674657
theorem R849959 : Reach 849959 := rs (se 1 (by rfl) ⟨637469, by rfl⟩) R1274939
theorem R686717 : Reach 686717 := rs (se 3 (by rfl) ⟨128759, by rfl⟩) R257519
theorem R523583 : Reach 523583 := rs (se 1 (by rfl) ⟨392687, by rfl⟩) R785375
theorem R3277219 : Reach 3277219 := rs (se 1 (by rfl) ⟨2457914, by rfl⟩) R4915829
theorem R230273 : Reach 230273 := rs (se 2 (by rfl) ⟨86352, by rfl⟩) R172705
theorem R166207 : Reach 166207 := rs (se 1 (by rfl) ⟨124655, by rfl⟩) R249311
theorem R200009 : Reach 200009 := rs (se 2 (by rfl) ⟨75003, by rfl⟩) R150007
theorem R396737 : Reach 396737 := rs (se 2 (by rfl) ⟨148776, by rfl⟩) R297553
theorem R201341 : Reach 201341 := rs (se 3 (by rfl) ⟨37751, by rfl⟩) R75503
theorem R66819275 : Reach 66819275 := rs (se 1 (by rfl) ⟨50114456, by rfl⟩) R100228913
theorem R136745 : Reach 136745 := rs (se 2 (by rfl) ⟨51279, by rfl⟩) R102559
theorem R136979 : Reach 136979 := rs (se 1 (by rfl) ⟨102734, by rfl⟩) R205469
theorem R5314409 : Reach 5314409 := rs (se 2 (by rfl) ⟨1992903, by rfl⟩) R3985807
theorem R2758697 : Reach 2758697 := rs (se 2 (by rfl) ⟨1034511, by rfl⟩) R2069023
theorem R104699 : Reach 104699 := rs (se 1 (by rfl) ⟨78524, by rfl⟩) R157049
theorem R8299847 : Reach 8299847 := rs (se 1 (by rfl) ⟨6224885, by rfl⟩) R12449771
theorem R566639 : Reach 566639 := rs (se 1 (by rfl) ⟨424979, by rfl⟩) R849959
theorem R1123931 : Reach 1123931 := rs (se 1 (by rfl) ⟨842948, by rfl⟩) R1685897
theorem R993215 : Reach 993215 := rs (se 1 (by rfl) ⟨744911, by rfl⟩) R1489823
theorem R141983 : Reach 141983 := rs (se 1 (by rfl) ⟨106487, by rfl⟩) R212975
theorem R207737 : Reach 207737 := rs (se 2 (by rfl) ⟨77901, by rfl⟩) R155803
theorem R535679 : Reach 535679 := rs (se 1 (by rfl) ⟨401759, by rfl⟩) R803519
theorem R669161 : Reach 669161 := rs (se 2 (by rfl) ⟨250935, by rfl⟩) R501871
theorem R309743 : Reach 309743 := rs (se 1 (by rfl) ⟨232307, by rfl⟩) R464615
theorem R345455 : Reach 345455 := rs (se 1 (by rfl) ⟨259091, by rfl⟩) R518183
theorem R1231523 : Reach 1231523 := rs (se 1 (by rfl) ⟨923642, by rfl⟩) R1847285
theorem R511211 : Reach 511211 := rs (se 1 (by rfl) ⟨383408, by rfl⟩) R766817
theorem R349055 : Reach 349055 := rs (se 1 (by rfl) ⟨261791, by rfl⟩) R523583
theorem R1561517 : Reach 1561517 := rs (se 3 (by rfl) ⟨292784, by rfl⟩) R585569
theorem R710045 : Reach 710045 := rs (se 3 (by rfl) ⟨133133, by rfl⟩) R266267
theorem R2283227 : Reach 2283227 := rs (se 1 (by rfl) ⟨1712420, by rfl⟩) R3424841
theorem R712165 : Reach 712165 := rs (se 4 (by rfl) ⟨66765, by rfl⟩) R133531
theorem R5070833 : Reach 5070833 := rs (se 2 (by rfl) ⟨1901562, by rfl⟩) R3803125
theorem R386689 : Reach 386689 := rs (se 2 (by rfl) ⟨145008, by rfl⟩) R290017
theorem R91817 : Reach 91817 := rs (se 2 (by rfl) ⟨34431, by rfl⟩) R68863
theorem R4122359 : Reach 4122359 := rs (se 1 (by rfl) ⟨3091769, by rfl⟩) R6183539
theorem R59751 : Reach 59751 := rs (se 1 (by rfl) ⟨44813, by rfl⟩) R89627
theorem R60155 : Reach 60155 := rs (se 1 (by rfl) ⟨45116, by rfl⟩) R90233
theorem R453437 : Reach 453437 := rs (se 3 (by rfl) ⟨85019, by rfl⟩) R170039
theorem R92999 : Reach 92999 := rs (se 1 (by rfl) ⟨69749, by rfl⟩) R139499
theorem R93311 : Reach 93311 := rs (se 1 (by rfl) ⟨69983, by rfl⟩) R139967
theorem R60863 : Reach 60863 := rs (se 1 (by rfl) ⟨45647, by rfl⟩) R91295
theorem R61083 : Reach 61083 := rs (se 1 (by rfl) ⟨45812, by rfl⟩) R91625
theorem R94367 : Reach 94367 := rs (se 1 (by rfl) ⟨70775, by rfl⟩) R141551
theorem R127727 : Reach 127727 := rs (se 1 (by rfl) ⟨95795, by rfl⟩) R191591
theorem R62407 : Reach 62407 := rs (se 1 (by rfl) ⟨46805, by rfl⟩) R93611
theorem R62463 : Reach 62463 := rs (se 1 (by rfl) ⟨46847, by rfl⟩) R93695
theorem R62747 : Reach 62747 := rs (se 1 (by rfl) ⟨47060, by rfl⟩) R94121
theorem R62927 : Reach 62927 := rs (se 1 (by rfl) ⟨47195, by rfl⟩) R94391
theorem R325385 : Reach 325385 := rs (se 2 (by rfl) ⟨122019, by rfl⟩) R244039
theorem R228329 : Reach 228329 := rs (se 2 (by rfl) ⟨85623, by rfl⟩) R171247
theorem R457811 : Reach 457811 := rs (se 1 (by rfl) ⟨343358, by rfl⟩) R686717
theorem R491291 : Reach 491291 := rs (se 1 (by rfl) ⟨368468, by rfl⟩) R736937
theorem R230303 : Reach 230303 := rs (se 1 (by rfl) ⟨172727, by rfl⟩) R345455
theorem R821015 : Reach 821015 := rs (se 1 (by rfl) ⟨615761, by rfl⟩) R1231523
theorem R133339 : Reach 133339 := rs (se 1 (by rfl) ⟨100004, by rfl⟩) R200009
theorem R264491 : Reach 264491 := rs (se 1 (by rfl) ⟨198368, by rfl⟩) R396737
theorem R134227 : Reach 134227 := rs (se 1 (by rfl) ⟨100670, by rfl⟩) R201341
theorem R232703 : Reach 232703 := rs (se 1 (by rfl) ⟨174527, by rfl⟩) R349055
theorem R3542939 : Reach 3542939 := rs (se 1 (by rfl) ⟨2657204, by rfl⟩) R5314409
theorem R1839131 : Reach 1839131 := rs (se 1 (by rfl) ⟨1379348, by rfl⟩) R2758697
theorem R69799 : Reach 69799 := rs (se 1 (by rfl) ⟨52349, by rfl⟩) R104699
theorem R3380555 : Reach 3380555 := rs (se 1 (by rfl) ⟨2535416, by rfl⟩) R5070833
theorem R662143 : Reach 662143 := rs (se 1 (by rfl) ⟨496607, by rfl⟩) R993215
theorem R302291 : Reach 302291 := rs (se 1 (by rfl) ⟨226718, by rfl⟩) R453437
theorem R138491 : Reach 138491 := rs (se 1 (by rfl) ⟨103868, by rfl⟩) R207737
theorem R206495 : Reach 206495 := rs (se 1 (by rfl) ⟨154871, by rfl⟩) R309743
theorem R305207 : Reach 305207 := rs (se 1 (by rfl) ⟨228905, by rfl⟩) R457811
theorem R4369625 : Reach 4369625 := rs (se 2 (by rfl) ⟨1638609, by rfl⟩) R3277219
theorem R340807 : Reach 340807 := rs (se 1 (by rfl) ⟨255605, by rfl⟩) R511211
theorem R44546183 : Reach 44546183 := rs (se 1 (by rfl) ⟨33409637, by rfl⟩) R66819275
theorem R473363 : Reach 473363 := rs (se 1 (by rfl) ⟨355022, by rfl⟩) R710045
theorem R1522151 : Reach 1522151 := rs (se 1 (by rfl) ⟨1141613, by rfl⟩) R2283227
theorem R377759 : Reach 377759 := rs (se 1 (by rfl) ⟨283319, by rfl⟩) R566639
theorem R85151 : Reach 85151 := rs (se 1 (by rfl) ⟨63863, by rfl⟩) R127727
theorem R446107 : Reach 446107 := rs (se 1 (by rfl) ⟨334580, by rfl⟩) R669161
theorem R216923 : Reach 216923 := rs (se 1 (by rfl) ⟨162692, by rfl⟩) R325385
theorem R152219 : Reach 152219 := rs (se 1 (by rfl) ⟨114164, by rfl⟩) R228329
theorem R153515 : Reach 153515 := rs (se 1 (by rfl) ⟨115136, by rfl⟩) R230273
theorem R515585 : Reach 515585 := rs (se 2 (by rfl) ⟨193344, by rfl⟩) R386689
theorem R221609 : Reach 221609 := rs (se 2 (by rfl) ⟨83103, by rfl⟩) R166207
theorem R1041011 : Reach 1041011 := rs (se 1 (by rfl) ⟨780758, by rfl⟩) R1561517
theorem R91163 : Reach 91163 := rs (se 1 (by rfl) ⟨68372, by rfl⟩) R136745
theorem R91319 : Reach 91319 := rs (se 1 (by rfl) ⟨68489, by rfl⟩) R136979
theorem R5533231 : Reach 5533231 := rs (se 1 (by rfl) ⟨4149923, by rfl⟩) R8299847
theorem R749287 : Reach 749287 := rs (se 1 (by rfl) ⟨561965, by rfl⟩) R1123931
theorem R61211 : Reach 61211 := rs (se 1 (by rfl) ⟨45908, by rfl⟩) R91817
theorem R2748239 : Reach 2748239 := rs (se 1 (by rfl) ⟨2061179, by rfl⟩) R4122359
theorem R94655 : Reach 94655 := rs (se 1 (by rfl) ⟨70991, by rfl⟩) R141983
theorem R61999 : Reach 61999 := rs (se 1 (by rfl) ⟨46499, by rfl⟩) R92999
theorem R62207 : Reach 62207 := rs (se 1 (by rfl) ⟨46655, by rfl⟩) R93311
theorem R357119 : Reach 357119 := rs (se 1 (by rfl) ⟨267839, by rfl⟩) R535679
theorem R62911 : Reach 62911 := rs (se 1 (by rfl) ⟨47183, by rfl⟩) R94367
theorem R949553 : Reach 949553 := rs (se 2 (by rfl) ⟨356082, by rfl⟩) R712165
theorem R327527 : Reach 327527 := rs (se 1 (by rfl) ⟨245645, by rfl⟩) R491291
theorem R2361959 : Reach 2361959 := rs (se 1 (by rfl) ⟨1771469, by rfl⟩) R3542939
theorem R101479 : Reach 101479 := rs (se 1 (by rfl) ⟨76109, by rfl⟩) R152219
theorem R102343 : Reach 102343 := rs (se 1 (by rfl) ⟨76757, by rfl⟩) R153515
theorem R7377641 : Reach 7377641 := rs (se 2 (by rfl) ⟨2766615, by rfl⟩) R5533231
theorem R201527 : Reach 201527 := rs (se 1 (by rfl) ⟨151145, by rfl⟩) R302291
theorem R594809 : Reach 594809 := rs (se 2 (by rfl) ⟨223053, by rfl⟩) R446107
theorem R694007 : Reach 694007 := rs (se 1 (by rfl) ⟨520505, by rfl⟩) R1041011
theorem R137663 : Reach 137663 := rs (se 1 (by rfl) ⟨103247, by rfl⟩) R206495
theorem R203471 : Reach 203471 := rs (se 1 (by rfl) ⟨152603, by rfl⟩) R305207
theorem R238079 : Reach 238079 := rs (se 1 (by rfl) ⟨178559, by rfl⟩) R357119
theorem R29697455 : Reach 29697455 := rs (se 1 (by rfl) ⟨22273091, by rfl⟩) R44546183
theorem R633035 : Reach 633035 := rs (se 1 (by rfl) ⟨474776, by rfl⟩) R949553
theorem R176327 : Reach 176327 := rs (se 1 (by rfl) ⟨132245, by rfl⟩) R264491
theorem R1226087 : Reach 1226087 := rs (se 1 (by rfl) ⟨919565, by rfl⟩) R1839131
theorem R177785 : Reach 177785 := rs (se 2 (by rfl) ⟨66669, by rfl⟩) R133339
theorem R999049 : Reach 999049 := rs (se 2 (by rfl) ⟨374643, by rfl⟩) R749287
theorem R343723 : Reach 343723 := rs (se 1 (by rfl) ⟨257792, by rfl⟩) R515585
theorem R147739 : Reach 147739 := rs (se 1 (by rfl) ⟨110804, by rfl⟩) R221609
theorem R315575 : Reach 315575 := rs (se 1 (by rfl) ⟨236681, by rfl⟩) R473363
theorem R578461 : Reach 578461 := rs (se 3 (by rfl) ⟨108461, by rfl⟩) R216923
theorem R218351 : Reach 218351 := rs (se 1 (by rfl) ⟨163763, by rfl⟩) R327527
theorem R153535 : Reach 153535 := rs (se 1 (by rfl) ⟨115151, by rfl⟩) R230303
theorem R251839 : Reach 251839 := rs (se 1 (by rfl) ⟨188879, by rfl⟩) R377759
theorem R547343 : Reach 547343 := rs (se 1 (by rfl) ⟨410507, by rfl⟩) R821015
theorem R155135 : Reach 155135 := rs (se 1 (by rfl) ⟨116351, by rfl⟩) R232703
theorem R2253703 : Reach 2253703 := rs (se 1 (by rfl) ⟨1690277, by rfl⟩) R3380555
theorem R92327 : Reach 92327 := rs (se 1 (by rfl) ⟨69245, by rfl⟩) R138491
theorem R93065 : Reach 93065 := rs (se 2 (by rfl) ⟨34899, by rfl⟩) R69799
theorem R715877 : Reach 715877 := rs (se 4 (by rfl) ⟨67113, by rfl⟩) R134227
theorem R60775 : Reach 60775 := rs (se 1 (by rfl) ⟨45581, by rfl⟩) R91163
theorem R60879 : Reach 60879 := rs (se 1 (by rfl) ⟨45659, by rfl⟩) R91319
theorem R454409 : Reach 454409 := rs (se 2 (by rfl) ⟨170403, by rfl⟩) R340807
theorem R2913083 : Reach 2913083 := rs (se 1 (by rfl) ⟨2184812, by rfl⟩) R4369625
theorem R1832159 : Reach 1832159 := rs (se 1 (by rfl) ⟨1374119, by rfl⟩) R2748239
theorem R63103 : Reach 63103 := rs (se 1 (by rfl) ⟨47327, by rfl⟩) R94655
theorem R227069 : Reach 227069 := rs (se 3 (by rfl) ⟨42575, by rfl⟩) R85151
theorem R882857 : Reach 882857 := rs (se 2 (by rfl) ⟨331071, by rfl⟩) R662143
theorem R1014767 : Reach 1014767 := rs (se 1 (by rfl) ⟨761075, by rfl⟩) R1522151
theorem R196985 : Reach 196985 := rs (se 2 (by rfl) ⟨73869, by rfl⟩) R147739
theorem R1574639 : Reach 1574639 := rs (se 1 (by rfl) ⟨1180979, by rfl⟩) R2361959
theorem R4918427 : Reach 4918427 := rs (se 1 (by rfl) ⟨3688820, by rfl⟩) R7377641
theorem R134351 : Reach 134351 := rs (se 1 (by rfl) ⟨100763, by rfl⟩) R201527
theorem R396539 : Reach 396539 := rs (se 1 (by rfl) ⟨297404, by rfl⟩) R594809
theorem R462671 : Reach 462671 := rs (se 1 (by rfl) ⟨347003, by rfl⟩) R694007
theorem R135305 : Reach 135305 := rs (se 2 (by rfl) ⟨50739, by rfl⟩) R101479
theorem R364895 : Reach 364895 := rs (se 1 (by rfl) ⟨273671, by rfl⟩) R547343
theorem R135647 : Reach 135647 := rs (se 1 (by rfl) ⟨101735, by rfl⟩) R203471
theorem R103423 : Reach 103423 := rs (se 1 (by rfl) ⟨77567, by rfl⟩) R155135
theorem R136457 : Reach 136457 := rs (se 2 (by rfl) ⟨51171, by rfl⟩) R102343
theorem R302939 : Reach 302939 := rs (se 1 (by rfl) ⟨227204, by rfl⟩) R454409
theorem R204713 : Reach 204713 := rs (se 2 (by rfl) ⟨76767, by rfl⟩) R153535
theorem R335785 : Reach 335785 := rs (se 2 (by rfl) ⟨125919, by rfl⟩) R251839
theorem R1942055 : Reach 1942055 := rs (se 1 (by rfl) ⟨1456541, by rfl⟩) R2913083
theorem R1221439 : Reach 1221439 := rs (se 1 (by rfl) ⟨916079, by rfl⟩) R1832159
theorem R210383 : Reach 210383 := rs (se 1 (by rfl) ⟨157787, by rfl⟩) R315575
theorem R145567 : Reach 145567 := rs (se 1 (by rfl) ⟨109175, by rfl⟩) R218351
theorem R771281 : Reach 771281 := rs (se 2 (by rfl) ⟨289230, by rfl⟩) R578461
theorem R477251 : Reach 477251 := rs (se 1 (by rfl) ⟨357938, by rfl⟩) R715877
theorem R117551 : Reach 117551 := rs (se 1 (by rfl) ⟨88163, by rfl⟩) R176327
theorem R118523 : Reach 118523 := rs (se 1 (by rfl) ⟨88892, by rfl⟩) R177785
theorem R151379 : Reach 151379 := rs (se 1 (by rfl) ⟨113534, by rfl⟩) R227069
theorem R676511 : Reach 676511 := rs (se 1 (by rfl) ⟨507383, by rfl⟩) R1014767
theorem R1332065 : Reach 1332065 := rs (se 2 (by rfl) ⟨499524, by rfl⟩) R999049
theorem R3004937 : Reach 3004937 := rs (se 2 (by rfl) ⟨1126851, by rfl⟩) R2253703
theorem R79193213 : Reach 79193213 := rs (se 3 (by rfl) ⟨14848727, by rfl⟩) R29697455
theorem R91775 : Reach 91775 := rs (se 1 (by rfl) ⟨68831, by rfl⟩) R137663
theorem R158719 : Reach 158719 := rs (se 1 (by rfl) ⟨119039, by rfl⟩) R238079
theorem R2354285 : Reach 2354285 := rs (se 3 (by rfl) ⟨441428, by rfl⟩) R882857
theorem R61551 : Reach 61551 := rs (se 1 (by rfl) ⟨46163, by rfl⟩) R92327
theorem R422023 : Reach 422023 := rs (se 1 (by rfl) ⟨316517, by rfl⟩) R633035
theorem R62043 : Reach 62043 := rs (se 1 (by rfl) ⟨46532, by rfl⟩) R93065
theorem R817391 : Reach 817391 := rs (se 1 (by rfl) ⟨613043, by rfl⟩) R1226087
theorem R458297 : Reach 458297 := rs (se 2 (by rfl) ⟨171861, by rfl⟩) R343723
theorem R131323 : Reach 131323 := rs (se 1 (by rfl) ⟨98492, by rfl⟩) R196985
theorem R1049759 : Reach 1049759 := rs (se 1 (by rfl) ⟨787319, by rfl⟩) R1574639
theorem R3278951 : Reach 3278951 := rs (se 1 (by rfl) ⟨2459213, by rfl⟩) R4918427
theorem R264359 : Reach 264359 := rs (se 1 (by rfl) ⟨198269, by rfl⟩) R396539
theorem R100919 : Reach 100919 := rs (se 1 (by rfl) ⟨75689, by rfl⟩) R151379
theorem R888043 : Reach 888043 := rs (se 1 (by rfl) ⟨666032, by rfl⟩) R1332065
theorem R2003291 : Reach 2003291 := rs (se 1 (by rfl) ⟨1502468, by rfl⟩) R3004937
theorem R201959 : Reach 201959 := rs (se 1 (by rfl) ⟨151469, by rfl⟩) R302939
theorem R136475 : Reach 136475 := rs (se 1 (by rfl) ⟨102356, by rfl⟩) R204713
theorem R562697 : Reach 562697 := rs (se 2 (by rfl) ⟨211011, by rfl⟩) R422023
theorem R52795475 : Reach 52795475 := rs (se 1 (by rfl) ⟨39596606, by rfl⟩) R79193213
theorem R137897 : Reach 137897 := rs (se 2 (by rfl) ⟨51711, by rfl⟩) R103423
theorem R140255 : Reach 140255 := rs (se 1 (by rfl) ⟨105191, by rfl⟩) R210383
theorem R305531 : Reach 305531 := rs (se 1 (by rfl) ⟨229148, by rfl⟩) R458297
theorem R308447 : Reach 308447 := rs (se 1 (by rfl) ⟨231335, by rfl⟩) R462671
theorem R243263 : Reach 243263 := rs (se 1 (by rfl) ⟨182447, by rfl⟩) R364895
theorem R211625 : Reach 211625 := rs (se 2 (by rfl) ⟨79359, by rfl⟩) R158719
theorem R1294703 : Reach 1294703 := rs (se 1 (by rfl) ⟨971027, by rfl⟩) R1942055
theorem R2179709 : Reach 2179709 := rs (se 3 (by rfl) ⟨408695, by rfl⟩) R817391
theorem R313469 : Reach 313469 := rs (se 3 (by rfl) ⟨58775, by rfl⟩) R117551
theorem R6278093 : Reach 6278093 := rs (se 3 (by rfl) ⟨1177142, by rfl⟩) R2354285
theorem R316061 : Reach 316061 := rs (se 3 (by rfl) ⟨59261, by rfl⟩) R118523
theorem R447713 : Reach 447713 := rs (se 2 (by rfl) ⟨167892, by rfl⟩) R335785
theorem R514187 : Reach 514187 := rs (se 1 (by rfl) ⟨385640, by rfl⟩) R771281
theorem R1628585 : Reach 1628585 := rs (se 2 (by rfl) ⟨610719, by rfl⟩) R1221439
theorem R318167 : Reach 318167 := rs (se 1 (by rfl) ⟨238625, by rfl⟩) R477251
theorem R89567 : Reach 89567 := rs (se 1 (by rfl) ⟨67175, by rfl⟩) R134351
theorem R90203 : Reach 90203 := rs (se 1 (by rfl) ⟨67652, by rfl⟩) R135305
theorem R90431 : Reach 90431 := rs (se 1 (by rfl) ⟨67823, by rfl⟩) R135647
theorem R451007 : Reach 451007 := rs (se 1 (by rfl) ⟨338255, by rfl⟩) R676511
theorem R90971 : Reach 90971 := rs (se 1 (by rfl) ⟨68228, by rfl⟩) R136457
theorem R61183 : Reach 61183 := rs (se 1 (by rfl) ⟨45887, by rfl⟩) R91775
theorem R194089 : Reach 194089 := rs (se 2 (by rfl) ⟨72783, by rfl⟩) R145567
theorem R67279 : Reach 67279 := rs (se 1 (by rfl) ⟨50459, by rfl⟩) R100919
theorem R298475 : Reach 298475 := rs (se 1 (by rfl) ⟨223856, by rfl⟩) R447713
theorem R134639 : Reach 134639 := rs (se 1 (by rfl) ⟨100979, by rfl⟩) R201959
theorem R35196983 : Reach 35196983 := rs (se 1 (by rfl) ⟨26397737, by rfl⟩) R52795475
theorem R1085723 : Reach 1085723 := rs (se 1 (by rfl) ⟨814292, by rfl⟩) R1628585
theorem R1184057 : Reach 1184057 := rs (se 2 (by rfl) ⟨444021, by rfl⟩) R888043
theorem R300671 : Reach 300671 := rs (se 1 (by rfl) ⟨225503, by rfl⟩) R451007
theorem R203687 : Reach 203687 := rs (se 1 (by rfl) ⟨152765, by rfl⟩) R305531
theorem R205631 : Reach 205631 := rs (se 1 (by rfl) ⟨154223, by rfl⟩) R308447
theorem R141083 : Reach 141083 := rs (se 1 (by rfl) ⟨105812, by rfl⟩) R211625
theorem R863135 : Reach 863135 := rs (se 1 (by rfl) ⟨647351, by rfl⟩) R1294703
theorem R175097 : Reach 175097 := rs (se 2 (by rfl) ⟨65661, by rfl⟩) R131323
theorem R1453139 : Reach 1453139 := rs (se 1 (by rfl) ⟨1089854, by rfl⟩) R2179709
theorem R699839 : Reach 699839 := rs (se 1 (by rfl) ⟨524879, by rfl⟩) R1049759
theorem R208979 : Reach 208979 := rs (se 1 (by rfl) ⟨156734, by rfl⟩) R313469
theorem R176239 : Reach 176239 := rs (se 1 (by rfl) ⟨132179, by rfl⟩) R264359
theorem R210707 : Reach 210707 := rs (se 1 (by rfl) ⟨158030, by rfl⟩) R316061
theorem R375131 : Reach 375131 := rs (se 1 (by rfl) ⟨281348, by rfl⟩) R562697
theorem R342791 : Reach 342791 := rs (se 1 (by rfl) ⟨257093, by rfl⟩) R514187
theorem R212111 : Reach 212111 := rs (se 1 (by rfl) ⟨159083, by rfl⟩) R318167
theorem R2185967 : Reach 2185967 := rs (se 1 (by rfl) ⟨1639475, by rfl⟩) R3278951
theorem R4185395 : Reach 4185395 := rs (se 1 (by rfl) ⟨3139046, by rfl⟩) R6278093
theorem R1335527 : Reach 1335527 := rs (se 1 (by rfl) ⟨1001645, by rfl⟩) R2003291
theorem R90983 : Reach 90983 := rs (se 1 (by rfl) ⟨68237, by rfl⟩) R136475
theorem R91931 : Reach 91931 := rs (se 1 (by rfl) ⟨68948, by rfl⟩) R137897
theorem R59711 : Reach 59711 := rs (se 1 (by rfl) ⟨44783, by rfl⟩) R89567
theorem R60135 : Reach 60135 := rs (se 1 (by rfl) ⟨45101, by rfl⟩) R90203
theorem R60287 : Reach 60287 := rs (se 1 (by rfl) ⟨45215, by rfl⟩) R90431
theorem R60647 : Reach 60647 := rs (se 1 (by rfl) ⟨45485, by rfl⟩) R90971
theorem R93503 : Reach 93503 := rs (se 1 (by rfl) ⟨70127, by rfl⟩) R140255
theorem R258785 : Reach 258785 := rs (se 2 (by rfl) ⟨97044, by rfl⟩) R194089
theorem R162175 : Reach 162175 := rs (se 1 (by rfl) ⟨121631, by rfl⟩) R243263
theorem R198983 : Reach 198983 := rs (se 1 (by rfl) ⟨149237, by rfl⟩) R298475
theorem R23464655 : Reach 23464655 := rs (se 1 (by rfl) ⟨17598491, by rfl⟩) R35196983
theorem R723815 : Reach 723815 := rs (se 1 (by rfl) ⟨542861, by rfl⟩) R1085723
theorem R789371 : Reach 789371 := rs (se 1 (by rfl) ⟨592028, by rfl⟩) R1184057
theorem R200447 : Reach 200447 := rs (se 1 (by rfl) ⟨150335, by rfl⟩) R300671
theorem R135791 : Reach 135791 := rs (se 1 (by rfl) ⟨101843, by rfl⟩) R203687
theorem R2790263 : Reach 2790263 := rs (se 1 (by rfl) ⟨2092697, by rfl⟩) R4185395
theorem R890351 : Reach 890351 := rs (se 1 (by rfl) ⟨667763, by rfl⟩) R1335527
theorem R137087 : Reach 137087 := rs (se 1 (by rfl) ⟨102815, by rfl⟩) R205631
theorem R466559 : Reach 466559 := rs (se 1 (by rfl) ⟨349919, by rfl⟩) R699839
theorem R139319 : Reach 139319 := rs (se 1 (by rfl) ⟨104489, by rfl⟩) R208979
theorem R172523 : Reach 172523 := rs (se 1 (by rfl) ⟨129392, by rfl⟩) R258785
theorem R140471 : Reach 140471 := rs (se 1 (by rfl) ⟨105353, by rfl⟩) R210707
theorem R141407 : Reach 141407 := rs (se 1 (by rfl) ⟨106055, by rfl⟩) R212111
theorem R1000349 : Reach 1000349 := rs (se 3 (by rfl) ⟨187565, by rfl⟩) R375131
theorem R575423 : Reach 575423 := rs (se 1 (by rfl) ⟨431567, by rfl⟩) R863135
theorem R116731 : Reach 116731 := rs (se 1 (by rfl) ⟨87548, by rfl⟩) R175097
theorem R968759 : Reach 968759 := rs (se 1 (by rfl) ⟨726569, by rfl⟩) R1453139
theorem R216233 : Reach 216233 := rs (se 2 (by rfl) ⟨81087, by rfl⟩) R162175
theorem R939941 : Reach 939941 := rs (se 4 (by rfl) ⟨88119, by rfl⟩) R176239
theorem R89705 : Reach 89705 := rs (se 2 (by rfl) ⟨33639, by rfl⟩) R67279
theorem R89759 : Reach 89759 := rs (se 1 (by rfl) ⟨67319, by rfl⟩) R134639
theorem R60655 : Reach 60655 := rs (se 1 (by rfl) ⟨45491, by rfl⟩) R90983
theorem R61287 : Reach 61287 := rs (se 1 (by rfl) ⟨45965, by rfl⟩) R91931
theorem R94055 : Reach 94055 := rs (se 1 (by rfl) ⟨70541, by rfl⟩) R141083
theorem R5829245 : Reach 5829245 := rs (se 3 (by rfl) ⟨1092983, by rfl⟩) R2185967
theorem R62335 : Reach 62335 := rs (se 1 (by rfl) ⟨46751, by rfl⟩) R93503
theorem R228527 : Reach 228527 := rs (se 1 (by rfl) ⟨171395, by rfl⟩) R342791
theorem R526247 : Reach 526247 := rs (se 1 (by rfl) ⟨394685, by rfl⟩) R789371
theorem R133631 : Reach 133631 := rs (se 1 (by rfl) ⟨100223, by rfl⟩) R200447
theorem R593567 : Reach 593567 := rs (se 1 (by rfl) ⟨445175, by rfl⟩) R890351
theorem R626627 : Reach 626627 := rs (se 1 (by rfl) ⟨469970, by rfl⟩) R939941
theorem R530621 : Reach 530621 := rs (se 3 (by rfl) ⟨99491, by rfl⟩) R198983
theorem R666899 : Reach 666899 := rs (se 1 (by rfl) ⟨500174, by rfl⟩) R1000349
theorem R15643103 : Reach 15643103 := rs (se 1 (by rfl) ⟨11732327, by rfl⟩) R23464655
theorem R144155 : Reach 144155 := rs (se 1 (by rfl) ⟨108116, by rfl⟩) R216233
theorem R311039 : Reach 311039 := rs (se 1 (by rfl) ⟨233279, by rfl⟩) R466559
theorem R115015 : Reach 115015 := rs (se 1 (by rfl) ⟨86261, by rfl⟩) R172523
theorem R3886163 : Reach 3886163 := rs (se 1 (by rfl) ⟨2914622, by rfl⟩) R5829245
theorem R152351 : Reach 152351 := rs (se 1 (by rfl) ⟨114263, by rfl⟩) R228527
theorem R383615 : Reach 383615 := rs (se 1 (by rfl) ⟨287711, by rfl⟩) R575423
theorem R645839 : Reach 645839 := rs (se 1 (by rfl) ⟨484379, by rfl⟩) R968759
theorem R482543 : Reach 482543 := rs (se 1 (by rfl) ⟨361907, by rfl⟩) R723815
theorem R155641 : Reach 155641 := rs (se 2 (by rfl) ⟨58365, by rfl⟩) R116731
theorem R90527 : Reach 90527 := rs (se 1 (by rfl) ⟨67895, by rfl⟩) R135791
theorem R1860175 : Reach 1860175 := rs (se 1 (by rfl) ⟨1395131, by rfl⟩) R2790263
theorem R91391 : Reach 91391 := rs (se 1 (by rfl) ⟨68543, by rfl⟩) R137087
theorem R59803 : Reach 59803 := rs (se 1 (by rfl) ⟨44852, by rfl⟩) R89705
theorem R59839 : Reach 59839 := rs (se 1 (by rfl) ⟨44879, by rfl⟩) R89759
theorem R92879 : Reach 92879 := rs (se 1 (by rfl) ⟨69659, by rfl⟩) R139319
theorem R93647 : Reach 93647 := rs (se 1 (by rfl) ⟨70235, by rfl⟩) R140471
theorem R94271 : Reach 94271 := rs (se 1 (by rfl) ⟨70703, by rfl⟩) R141407
theorem R62703 : Reach 62703 := rs (se 1 (by rfl) ⟨47027, by rfl⟩) R94055
theorem R41714941 : Reach 41714941 := rs (se 3 (by rfl) ⟨7821551, by rfl⟩) R15643103
theorem R2590775 : Reach 2590775 := rs (se 1 (by rfl) ⟨1943081, by rfl⟩) R3886163
theorem R395711 : Reach 395711 := rs (se 1 (by rfl) ⟨296783, by rfl⟩) R593567
theorem R101567 : Reach 101567 := rs (se 1 (by rfl) ⟨76175, by rfl⟩) R152351
theorem R430559 : Reach 430559 := rs (se 1 (by rfl) ⟨322919, by rfl⟩) R645839
theorem R207359 : Reach 207359 := rs (se 1 (by rfl) ⟨155519, by rfl⟩) R311039
theorem R207521 : Reach 207521 := rs (se 2 (by rfl) ⟨77820, by rfl⟩) R155641
theorem R444599 : Reach 444599 := rs (se 1 (by rfl) ⟨333449, by rfl⟩) R666899
theorem R153353 : Reach 153353 := rs (se 2 (by rfl) ⟨57507, by rfl⟩) R115015
theorem R2480233 : Reach 2480233 := rs (se 2 (by rfl) ⟨930087, by rfl⟩) R1860175
theorem R350831 : Reach 350831 := rs (se 1 (by rfl) ⟨263123, by rfl⟩) R526247
theorem R89087 : Reach 89087 := rs (se 1 (by rfl) ⟨66815, by rfl⟩) R133631
theorem R353747 : Reach 353747 := rs (se 1 (by rfl) ⟨265310, by rfl⟩) R530621
theorem R255743 : Reach 255743 := rs (se 1 (by rfl) ⟨191807, by rfl⟩) R383615
theorem R321695 : Reach 321695 := rs (se 1 (by rfl) ⟨241271, by rfl⟩) R482543
theorem R60351 : Reach 60351 := rs (se 1 (by rfl) ⟨45263, by rfl⟩) R90527
theorem R60927 : Reach 60927 := rs (se 1 (by rfl) ⟨45695, by rfl⟩) R91391
theorem R61919 : Reach 61919 := rs (se 1 (by rfl) ⟨46439, by rfl⟩) R92879
theorem R62431 : Reach 62431 := rs (se 1 (by rfl) ⟨46823, by rfl⟩) R93647
theorem R62847 : Reach 62847 := rs (se 1 (by rfl) ⟨47135, by rfl⟩) R94271
theorem R96103 : Reach 96103 := rs (se 1 (by rfl) ⟨72077, by rfl⟩) R144155
theorem R1671005 : Reach 1671005 := rs (se 3 (by rfl) ⟨313313, by rfl⟩) R626627
theorem R296399 : Reach 296399 := rs (se 1 (by rfl) ⟨222299, by rfl⟩) R444599
theorem R263807 : Reach 263807 := rs (se 1 (by rfl) ⟨197855, by rfl⟩) R395711
theorem R67711 : Reach 67711 := rs (se 1 (by rfl) ⟨50783, by rfl⟩) R101567
theorem R102235 : Reach 102235 := rs (se 1 (by rfl) ⟨76676, by rfl⟩) R153353
theorem R233887 : Reach 233887 := rs (se 1 (by rfl) ⟨175415, by rfl⟩) R350831
theorem R235831 : Reach 235831 := rs (se 1 (by rfl) ⟨176873, by rfl⟩) R353747
theorem R170495 : Reach 170495 := rs (se 1 (by rfl) ⟨127871, by rfl⟩) R255743
theorem R138239 : Reach 138239 := rs (se 1 (by rfl) ⟨103679, by rfl⟩) R207359
theorem R138347 : Reach 138347 := rs (se 1 (by rfl) ⟨103760, by rfl⟩) R207521
theorem R55619921 : Reach 55619921 := rs (se 2 (by rfl) ⟨20857470, by rfl⟩) R41714941
theorem R214463 : Reach 214463 := rs (se 1 (by rfl) ⟨160847, by rfl⟩) R321695
theorem R1727183 : Reach 1727183 := rs (se 1 (by rfl) ⟨1295387, by rfl⟩) R2590775
theorem R287039 : Reach 287039 := rs (se 1 (by rfl) ⟨215279, by rfl⟩) R430559
theorem R59391 : Reach 59391 := rs (se 1 (by rfl) ⟨44543, by rfl⟩) R89087
theorem R128137 : Reach 128137 := rs (se 2 (by rfl) ⟨48051, by rfl⟩) R96103
theorem R3306977 : Reach 3306977 := rs (se 2 (by rfl) ⟨1240116, by rfl⟩) R2480233
theorem R1114003 : Reach 1114003 := rs (se 1 (by rfl) ⟨835502, by rfl⟩) R1671005
theorem R790397 : Reach 790397 := rs (se 3 (by rfl) ⟨148199, by rfl⟩) R296399
theorem R1151455 : Reach 1151455 := rs (se 1 (by rfl) ⟨863591, by rfl⟩) R1727183
theorem R136313 : Reach 136313 := rs (se 2 (by rfl) ⟨51117, by rfl⟩) R102235
theorem R170849 : Reach 170849 := rs (se 2 (by rfl) ⟨64068, by rfl⟩) R128137
theorem R2204651 : Reach 2204651 := rs (se 1 (by rfl) ⟨1653488, by rfl⟩) R3306977
theorem R5941349 : Reach 5941349 := rs (se 4 (by rfl) ⟨557001, by rfl⟩) R1114003
theorem R142975 : Reach 142975 := rs (se 1 (by rfl) ⟨107231, by rfl⟩) R214463
theorem R175871 : Reach 175871 := rs (se 1 (by rfl) ⟨131903, by rfl⟩) R263807
theorem R113663 : Reach 113663 := rs (se 1 (by rfl) ⟨85247, by rfl⟩) R170495
theorem R311849 : Reach 311849 := rs (se 2 (by rfl) ⟨116943, by rfl⟩) R233887
theorem R37079947 : Reach 37079947 := rs (se 1 (by rfl) ⟨27809960, by rfl⟩) R55619921
theorem R314441 : Reach 314441 := rs (se 2 (by rfl) ⟨117915, by rfl⟩) R235831
theorem R90281 : Reach 90281 := rs (se 2 (by rfl) ⟨33855, by rfl⟩) R67711
theorem R92159 : Reach 92159 := rs (se 1 (by rfl) ⟨69119, by rfl⟩) R138239
theorem R92231 : Reach 92231 := rs (se 1 (by rfl) ⟨69173, by rfl⟩) R138347
theorem R191359 : Reach 191359 := rs (se 1 (by rfl) ⟨143519, by rfl⟩) R287039
theorem R526931 : Reach 526931 := rs (se 1 (by rfl) ⟨395198, by rfl⟩) R790397
theorem R197759717 : Reach 197759717 := rs (se 4 (by rfl) ⟨18539973, by rfl⟩) R37079947
theorem R303101 : Reach 303101 := rs (se 3 (by rfl) ⟨56831, by rfl⟩) R113663
theorem R762533 : Reach 762533 := rs (se 4 (by rfl) ⟨71487, by rfl⟩) R142975
theorem R468989 : Reach 468989 := rs (se 3 (by rfl) ⟨87935, by rfl⟩) R175871
theorem R207899 : Reach 207899 := rs (se 1 (by rfl) ⟨155924, by rfl⟩) R311849
theorem R209627 : Reach 209627 := rs (se 1 (by rfl) ⟨157220, by rfl⟩) R314441
theorem R113899 : Reach 113899 := rs (se 1 (by rfl) ⟨85424, by rfl⟩) R170849
theorem R90875 : Reach 90875 := rs (se 1 (by rfl) ⟨68156, by rfl⟩) R136313
theorem R255145 : Reach 255145 := rs (se 2 (by rfl) ⟨95679, by rfl⟩) R191359
theorem R60187 : Reach 60187 := rs (se 1 (by rfl) ⟨45140, by rfl⟩) R90281
theorem R1535273 : Reach 1535273 := rs (se 2 (by rfl) ⟨575727, by rfl⟩) R1151455
theorem R1469767 : Reach 1469767 := rs (se 1 (by rfl) ⟨1102325, by rfl⟩) R2204651
theorem R61439 : Reach 61439 := rs (se 1 (by rfl) ⟨46079, by rfl⟩) R92159
theorem R61487 : Reach 61487 := rs (se 1 (by rfl) ⟨46115, by rfl⟩) R92231
theorem R3960899 : Reach 3960899 := rs (se 1 (by rfl) ⟨2970674, by rfl⟩) R5941349
theorem R202067 : Reach 202067 := rs (se 1 (by rfl) ⟨151550, by rfl⟩) R303101
theorem R138599 : Reach 138599 := rs (se 1 (by rfl) ⟨103949, by rfl⟩) R207899
theorem R1023515 : Reach 1023515 := rs (se 1 (by rfl) ⟨767636, by rfl⟩) R1535273
theorem R139751 : Reach 139751 := rs (se 1 (by rfl) ⟨104813, by rfl⟩) R209627
theorem R340193 : Reach 340193 := rs (se 2 (by rfl) ⟨127572, by rfl⟩) R255145
theorem R131839811 : Reach 131839811 := rs (se 1 (by rfl) ⟨98879858, by rfl⟩) R197759717
theorem R508355 : Reach 508355 := rs (se 1 (by rfl) ⟨381266, by rfl⟩) R762533
theorem R312659 : Reach 312659 := rs (se 1 (by rfl) ⟨234494, by rfl⟩) R468989
theorem R2640599 : Reach 2640599 := rs (se 1 (by rfl) ⟨1980449, by rfl⟩) R3960899
theorem R151865 : Reach 151865 := rs (se 2 (by rfl) ⟨56949, by rfl⟩) R113899
theorem R351287 : Reach 351287 := rs (se 1 (by rfl) ⟨263465, by rfl⟩) R526931
theorem R1959689 : Reach 1959689 := rs (se 2 (by rfl) ⟨734883, by rfl⟩) R1469767
theorem R60583 : Reach 60583 := rs (se 1 (by rfl) ⟨45437, by rfl⟩) R90875
theorem R101243 : Reach 101243 := rs (se 1 (by rfl) ⟨75932, by rfl⟩) R151865
theorem R134711 : Reach 134711 := rs (se 1 (by rfl) ⟨101033, by rfl⟩) R202067
theorem R234191 : Reach 234191 := rs (se 1 (by rfl) ⟨175643, by rfl⟩) R351287
theorem R87893207 : Reach 87893207 := rs (se 1 (by rfl) ⟨65919905, by rfl⟩) R131839811
theorem R338903 : Reach 338903 := rs (se 1 (by rfl) ⟨254177, by rfl⟩) R508355
theorem R208439 : Reach 208439 := rs (se 1 (by rfl) ⟨156329, by rfl⟩) R312659
theorem R1760399 : Reach 1760399 := rs (se 1 (by rfl) ⟨1320299, by rfl⟩) R2640599
theorem R92399 : Reach 92399 := rs (se 1 (by rfl) ⟨69299, by rfl⟩) R138599
theorem R682343 : Reach 682343 := rs (se 1 (by rfl) ⟨511757, by rfl⟩) R1023515
theorem R93167 : Reach 93167 := rs (se 1 (by rfl) ⟨69875, by rfl⟩) R139751
theorem R1306459 : Reach 1306459 := rs (se 1 (by rfl) ⟨979844, by rfl⟩) R1959689
theorem R226795 : Reach 226795 := rs (se 1 (by rfl) ⟨170096, by rfl⟩) R340193
theorem R67495 : Reach 67495 := rs (se 1 (by rfl) ⟨50621, by rfl⟩) R101243
theorem R1741945 : Reach 1741945 := rs (se 2 (by rfl) ⟨653229, by rfl⟩) R1306459
theorem R58595471 : Reach 58595471 := rs (se 1 (by rfl) ⟨43946603, by rfl⟩) R87893207
theorem R302393 : Reach 302393 := rs (se 2 (by rfl) ⟨113397, by rfl⟩) R226795
theorem R138959 : Reach 138959 := rs (se 1 (by rfl) ⟨104219, by rfl⟩) R208439
theorem R89807 : Reach 89807 := rs (se 1 (by rfl) ⟨67355, by rfl⟩) R134711
theorem R156127 : Reach 156127 := rs (se 1 (by rfl) ⟨117095, by rfl⟩) R234191
theorem R1173599 : Reach 1173599 := rs (se 1 (by rfl) ⟨880199, by rfl⟩) R1760399
theorem R61599 : Reach 61599 := rs (se 1 (by rfl) ⟨46199, by rfl⟩) R92399
theorem R454895 : Reach 454895 := rs (se 1 (by rfl) ⟨341171, by rfl⟩) R682343
theorem R225935 : Reach 225935 := rs (se 1 (by rfl) ⟨169451, by rfl⟩) R338903
theorem R62111 : Reach 62111 := rs (se 1 (by rfl) ⟨46583, by rfl⟩) R93167
theorem R39063647 : Reach 39063647 := rs (se 1 (by rfl) ⟨29297735, by rfl⟩) R58595471
theorem R303263 : Reach 303263 := rs (se 1 (by rfl) ⟨227447, by rfl⟩) R454895
theorem R208169 : Reach 208169 := rs (se 2 (by rfl) ⟨78063, by rfl⟩) R156127
theorem R150623 : Reach 150623 := rs (se 1 (by rfl) ⟨112967, by rfl⟩) R225935
theorem R806381 : Reach 806381 := rs (se 3 (by rfl) ⟨151196, by rfl⟩) R302393
theorem R89993 : Reach 89993 := rs (se 2 (by rfl) ⟨33747, by rfl⟩) R67495
theorem R59871 : Reach 59871 := rs (se 1 (by rfl) ⟨44903, by rfl⟩) R89807
theorem R92639 : Reach 92639 := rs (se 1 (by rfl) ⟨69479, by rfl⟩) R138959
theorem R782399 : Reach 782399 := rs (se 1 (by rfl) ⟨586799, by rfl⟩) R1173599
theorem R2322593 : Reach 2322593 := rs (se 2 (by rfl) ⟨870972, by rfl⟩) R1741945
theorem R100415 : Reach 100415 := rs (se 1 (by rfl) ⟨75311, by rfl⟩) R150623
theorem R202175 : Reach 202175 := rs (se 1 (by rfl) ⟨151631, by rfl⟩) R303263
theorem R138779 : Reach 138779 := rs (se 1 (by rfl) ⟨104084, by rfl⟩) R208169
theorem R1548395 : Reach 1548395 := rs (se 1 (by rfl) ⟨1161296, by rfl⟩) R2322593
theorem R537587 : Reach 537587 := rs (se 1 (by rfl) ⟨403190, by rfl⟩) R806381
theorem R26042431 : Reach 26042431 := rs (se 1 (by rfl) ⟨19531823, by rfl⟩) R39063647
theorem R59995 : Reach 59995 := rs (se 1 (by rfl) ⟨44996, by rfl⟩) R89993
theorem R61759 : Reach 61759 := rs (se 1 (by rfl) ⟨46319, by rfl⟩) R92639
theorem R521599 : Reach 521599 := rs (se 1 (by rfl) ⟨391199, by rfl⟩) R782399
theorem R66943 : Reach 66943 := rs (se 1 (by rfl) ⟨50207, by rfl⟩) R100415
theorem R134783 : Reach 134783 := rs (se 1 (by rfl) ⟨101087, by rfl⟩) R202175
theorem R695465 : Reach 695465 := rs (se 2 (by rfl) ⟨260799, by rfl⟩) R521599
theorem R1032263 : Reach 1032263 := rs (se 1 (by rfl) ⟨774197, by rfl⟩) R1548395
theorem R34723241 : Reach 34723241 := rs (se 2 (by rfl) ⟨13021215, by rfl⟩) R26042431
theorem R92519 : Reach 92519 := rs (se 1 (by rfl) ⟨69389, by rfl⟩) R138779
theorem R358391 : Reach 358391 := rs (se 1 (by rfl) ⟨268793, by rfl⟩) R537587
theorem R688175 : Reach 688175 := rs (se 1 (by rfl) ⟨516131, by rfl⟩) R1032263
theorem R463643 : Reach 463643 := rs (se 1 (by rfl) ⟨347732, by rfl⟩) R695465
theorem R955709 : Reach 955709 := rs (se 3 (by rfl) ⟨179195, by rfl⟩) R358391
theorem R23148827 : Reach 23148827 := rs (se 1 (by rfl) ⟨17361620, by rfl⟩) R34723241
theorem R89257 : Reach 89257 := rs (se 2 (by rfl) ⟨33471, by rfl⟩) R66943
theorem R89855 : Reach 89855 := rs (se 1 (by rfl) ⟨67391, by rfl⟩) R134783
theorem R61679 : Reach 61679 := rs (se 1 (by rfl) ⟨46259, by rfl⟩) R92519
theorem R458783 : Reach 458783 := rs (se 1 (by rfl) ⟨344087, by rfl⟩) R688175
theorem R309095 : Reach 309095 := rs (se 1 (by rfl) ⟨231821, by rfl⟩) R463643
theorem R637139 : Reach 637139 := rs (se 1 (by rfl) ⟨477854, by rfl⟩) R955709
theorem R119009 : Reach 119009 := rs (se 2 (by rfl) ⟨44628, by rfl⟩) R89257
theorem R59903 : Reach 59903 := rs (se 1 (by rfl) ⟨44927, by rfl⟩) R89855
theorem R15432551 : Reach 15432551 := rs (se 1 (by rfl) ⟨11574413, by rfl⟩) R23148827
theorem R206063 : Reach 206063 := rs (se 1 (by rfl) ⟨154547, by rfl⟩) R309095
theorem R305855 : Reach 305855 := rs (se 1 (by rfl) ⟨229391, by rfl⟩) R458783
theorem R317357 : Reach 317357 := rs (se 3 (by rfl) ⟨59504, by rfl⟩) R119009
theorem R424759 : Reach 424759 := rs (se 1 (by rfl) ⟨318569, by rfl⟩) R637139
theorem R10288367 : Reach 10288367 := rs (se 1 (by rfl) ⟨7716275, by rfl⟩) R15432551
theorem R137375 : Reach 137375 := rs (se 1 (by rfl) ⟨103031, by rfl⟩) R206063
theorem R203903 : Reach 203903 := rs (se 1 (by rfl) ⟨152927, by rfl⟩) R305855
theorem R566345 : Reach 566345 := rs (se 2 (by rfl) ⟨212379, by rfl⟩) R424759
theorem R6858911 : Reach 6858911 := rs (se 1 (by rfl) ⟨5144183, by rfl⟩) R10288367
theorem R211571 : Reach 211571 := rs (se 1 (by rfl) ⟨158678, by rfl⟩) R317357
theorem R135935 : Reach 135935 := rs (se 1 (by rfl) ⟨101951, by rfl⟩) R203903
theorem R141047 : Reach 141047 := rs (se 1 (by rfl) ⟨105785, by rfl⟩) R211571
theorem R377563 : Reach 377563 := rs (se 1 (by rfl) ⟨283172, by rfl⟩) R566345
theorem R4572607 : Reach 4572607 := rs (se 1 (by rfl) ⟨3429455, by rfl⟩) R6858911
theorem R91583 : Reach 91583 := rs (se 1 (by rfl) ⟨68687, by rfl⟩) R137375
theorem R6096809 : Reach 6096809 := rs (se 2 (by rfl) ⟨2286303, by rfl⟩) R4572607
theorem R503417 : Reach 503417 := rs (se 2 (by rfl) ⟨188781, by rfl⟩) R377563
theorem R90623 : Reach 90623 := rs (se 1 (by rfl) ⟨67967, by rfl⟩) R135935
theorem R61055 : Reach 61055 := rs (se 1 (by rfl) ⟨45791, by rfl⟩) R91583
theorem R94031 : Reach 94031 := rs (se 1 (by rfl) ⟨70523, by rfl⟩) R141047
theorem R16258157 : Reach 16258157 := rs (se 3 (by rfl) ⟨3048404, by rfl⟩) R6096809
theorem R335611 : Reach 335611 := rs (se 1 (by rfl) ⟨251708, by rfl⟩) R503417
theorem R60415 : Reach 60415 := rs (se 1 (by rfl) ⟨45311, by rfl⟩) R90623
theorem R62687 : Reach 62687 := rs (se 1 (by rfl) ⟨47015, by rfl⟩) R94031
theorem R447481 : Reach 447481 := rs (se 2 (by rfl) ⟨167805, by rfl⟩) R335611
theorem R10838771 : Reach 10838771 := rs (se 1 (by rfl) ⟨8129078, by rfl⟩) R16258157
theorem R596641 : Reach 596641 := rs (se 2 (by rfl) ⟨223740, by rfl⟩) R447481
theorem R7225847 : Reach 7225847 := rs (se 1 (by rfl) ⟨5419385, by rfl⟩) R10838771
theorem R4817231 : Reach 4817231 := rs (se 1 (by rfl) ⟨3612923, by rfl⟩) R7225847
theorem R795521 : Reach 795521 := rs (se 2 (by rfl) ⟨298320, by rfl⟩) R596641
theorem R3211487 : Reach 3211487 := rs (se 1 (by rfl) ⟨2408615, by rfl⟩) R4817231
theorem R530347 : Reach 530347 := rs (se 1 (by rfl) ⟨397760, by rfl⟩) R795521
theorem R2140991 : Reach 2140991 := rs (se 1 (by rfl) ⟨1605743, by rfl⟩) R3211487
theorem R707129 : Reach 707129 := rs (se 2 (by rfl) ⟨265173, by rfl⟩) R530347
theorem R471419 : Reach 471419 := rs (se 1 (by rfl) ⟨353564, by rfl⟩) R707129
theorem R1427327 : Reach 1427327 := rs (se 1 (by rfl) ⟨1070495, by rfl⟩) R2140991
theorem R951551 : Reach 951551 := rs (se 1 (by rfl) ⟨713663, by rfl⟩) R1427327
theorem R314279 : Reach 314279 := rs (se 1 (by rfl) ⟨235709, by rfl⟩) R471419
theorem R634367 : Reach 634367 := rs (se 1 (by rfl) ⟨475775, by rfl⟩) R951551
theorem R209519 : Reach 209519 := rs (se 1 (by rfl) ⟨157139, by rfl⟩) R314279
theorem R139679 : Reach 139679 := rs (se 1 (by rfl) ⟨104759, by rfl⟩) R209519
theorem R422911 : Reach 422911 := rs (se 1 (by rfl) ⟨317183, by rfl⟩) R634367
theorem R563881 : Reach 563881 := rs (se 2 (by rfl) ⟨211455, by rfl⟩) R422911
theorem R93119 : Reach 93119 := rs (se 1 (by rfl) ⟨69839, by rfl⟩) R139679
theorem R62079 : Reach 62079 := rs (se 1 (by rfl) ⟨46559, by rfl⟩) R93119
theorem R751841 : Reach 751841 := rs (se 2 (by rfl) ⟨281940, by rfl⟩) R563881
theorem R501227 : Reach 501227 := rs (se 1 (by rfl) ⟨375920, by rfl⟩) R751841
theorem R334151 : Reach 334151 := rs (se 1 (by rfl) ⟨250613, by rfl⟩) R501227
theorem R222767 : Reach 222767 := rs (se 1 (by rfl) ⟨167075, by rfl⟩) R334151
theorem R148511 : Reach 148511 := rs (se 1 (by rfl) ⟨111383, by rfl⟩) R222767
theorem R396029 : Reach 396029 := rs (se 3 (by rfl) ⟨74255, by rfl⟩) R148511
theorem R264019 : Reach 264019 := rs (se 1 (by rfl) ⟨198014, by rfl⟩) R396029
theorem R352025 : Reach 352025 := rs (se 2 (by rfl) ⟨132009, by rfl⟩) R264019
theorem R234683 : Reach 234683 := rs (se 1 (by rfl) ⟨176012, by rfl⟩) R352025
theorem R156455 : Reach 156455 := rs (se 1 (by rfl) ⟨117341, by rfl⟩) R234683
theorem R104303 : Reach 104303 := rs (se 1 (by rfl) ⟨78227, by rfl⟩) R156455
theorem R69535 : Reach 69535 := rs (se 1 (by rfl) ⟨52151, by rfl⟩) R104303
theorem R92713 : Reach 92713 := rs (se 2 (by rfl) ⟨34767, by rfl⟩) R69535
theorem R123617 : Reach 123617 := rs (se 2 (by rfl) ⟨46356, by rfl⟩) R92713
theorem R329645 : Reach 329645 := rs (se 3 (by rfl) ⟨61808, by rfl⟩) R123617
theorem R219763 : Reach 219763 := rs (se 1 (by rfl) ⟨164822, by rfl⟩) R329645
theorem R293017 : Reach 293017 := rs (se 2 (by rfl) ⟨109881, by rfl⟩) R219763
theorem R390689 : Reach 390689 := rs (se 2 (by rfl) ⟨146508, by rfl⟩) R293017
theorem R260459 : Reach 260459 := rs (se 1 (by rfl) ⟨195344, by rfl⟩) R390689
theorem R173639 : Reach 173639 := rs (se 1 (by rfl) ⟨130229, by rfl⟩) R260459
theorem R115759 : Reach 115759 := rs (se 1 (by rfl) ⟨86819, by rfl⟩) R173639
theorem R154345 : Reach 154345 := rs (se 2 (by rfl) ⟨57879, by rfl⟩) R115759
theorem R205793 : Reach 205793 := rs (se 2 (by rfl) ⟨77172, by rfl⟩) R154345
theorem R137195 : Reach 137195 := rs (se 1 (by rfl) ⟨102896, by rfl⟩) R205793
theorem R91463 : Reach 91463 := rs (se 1 (by rfl) ⟨68597, by rfl⟩) R137195
theorem R60975 : Reach 60975 := rs (se 1 (by rfl) ⟨45731, by rfl⟩) R91463

theorem C0 (j : ℕ) (h1 : 29561 ≤ j) (h2 : j ≤ 30260) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R59123
  · exact R59125
  · exact R59127
  · exact R59129
  · exact R59131
  · exact R59133
  · exact R59135
  · exact R59137
  · exact R59139
  · exact R59141
  · exact R59143
  · exact R59145
  · exact R59147
  · exact R59149
  · exact R59151
  · exact R59153
  · exact R59155
  · exact R59157
  · exact R59159
  · exact R59161
  · exact R59163
  · exact R59165
  · exact R59167
  · exact R59169
  · exact R59171
  · exact R59173
  · exact R59175
  · exact R59177
  · exact R59179
  · exact R59181
  · exact R59183
  · exact R59185
  · exact R59187
  · exact R59189
  · exact R59191
  · exact R59193
  · exact R59195
  · exact R59197
  · exact R59199
  · exact R59201
  · exact R59203
  · exact R59205
  · exact R59207
  · exact R59209
  · exact R59211
  · exact R59213
  · exact R59215
  · exact R59217
  · exact R59219
  · exact R59221
  · exact R59223
  · exact R59225
  · exact R59227
  · exact R59229
  · exact R59231
  · exact R59233
  · exact R59235
  · exact R59237
  · exact R59239
  · exact R59241
  · exact R59243
  · exact R59245
  · exact R59247
  · exact R59249
  · exact R59251
  · exact R59253
  · exact R59255
  · exact R59257
  · exact R59259
  · exact R59261
  · exact R59263
  · exact R59265
  · exact R59267
  · exact R59269
  · exact R59271
  · exact R59273
  · exact R59275
  · exact R59277
  · exact R59279
  · exact R59281
  · exact R59283
  · exact R59285
  · exact R59287
  · exact R59289
  · exact R59291
  · exact R59293
  · exact R59295
  · exact R59297
  · exact R59299
  · exact R59301
  · exact R59303
  · exact R59305
  · exact R59307
  · exact R59309
  · exact R59311
  · exact R59313
  · exact R59315
  · exact R59317
  · exact R59319
  · exact R59321
  · exact R59323
  · exact R59325
  · exact R59327
  · exact R59329
  · exact R59331
  · exact R59333
  · exact R59335
  · exact R59337
  · exact R59339
  · exact R59341
  · exact R59343
  · exact R59345
  · exact R59347
  · exact R59349
  · exact R59351
  · exact R59353
  · exact R59355
  · exact R59357
  · exact R59359
  · exact R59361
  · exact R59363
  · exact R59365
  · exact R59367
  · exact R59369
  · exact R59371
  · exact R59373
  · exact R59375
  · exact R59377
  · exact R59379
  · exact R59381
  · exact R59383
  · exact R59385
  · exact R59387
  · exact R59389
  · exact R59391
  · exact R59393
  · exact R59395
  · exact R59397
  · exact R59399
  · exact R59401
  · exact R59403
  · exact R59405
  · exact R59407
  · exact R59409
  · exact R59411
  · exact R59413
  · exact R59415
  · exact R59417
  · exact R59419
  · exact R59421
  · exact R59423
  · exact R59425
  · exact R59427
  · exact R59429
  · exact R59431
  · exact R59433
  · exact R59435
  · exact R59437
  · exact R59439
  · exact R59441
  · exact R59443
  · exact R59445
  · exact R59447
  · exact R59449
  · exact R59451
  · exact R59453
  · exact R59455
  · exact R59457
  · exact R59459
  · exact R59461
  · exact R59463
  · exact R59465
  · exact R59467
  · exact R59469
  · exact R59471
  · exact R59473
  · exact R59475
  · exact R59477
  · exact R59479
  · exact R59481
  · exact R59483
  · exact R59485
  · exact R59487
  · exact R59489
  · exact R59491
  · exact R59493
  · exact R59495
  · exact R59497
  · exact R59499
  · exact R59501
  · exact R59503
  · exact R59505
  · exact R59507
  · exact R59509
  · exact R59511
  · exact R59513
  · exact R59515
  · exact R59517
  · exact R59519
  · exact R59521
  · exact R59523
  · exact R59525
  · exact R59527
  · exact R59529
  · exact R59531
  · exact R59533
  · exact R59535
  · exact R59537
  · exact R59539
  · exact R59541
  · exact R59543
  · exact R59545
  · exact R59547
  · exact R59549
  · exact R59551
  · exact R59553
  · exact R59555
  · exact R59557
  · exact R59559
  · exact R59561
  · exact R59563
  · exact R59565
  · exact R59567
  · exact R59569
  · exact R59571
  · exact R59573
  · exact R59575
  · exact R59577
  · exact R59579
  · exact R59581
  · exact R59583
  · exact R59585
  · exact R59587
  · exact R59589
  · exact R59591
  · exact R59593
  · exact R59595
  · exact R59597
  · exact R59599
  · exact R59601
  · exact R59603
  · exact R59605
  · exact R59607
  · exact R59609
  · exact R59611
  · exact R59613
  · exact R59615
  · exact R59617
  · exact R59619
  · exact R59621
  · exact R59623
  · exact R59625
  · exact R59627
  · exact R59629
  · exact R59631
  · exact R59633
  · exact R59635
  · exact R59637
  · exact R59639
  · exact R59641
  · exact R59643
  · exact R59645
  · exact R59647
  · exact R59649
  · exact R59651
  · exact R59653
  · exact R59655
  · exact R59657
  · exact R59659
  · exact R59661
  · exact R59663
  · exact R59665
  · exact R59667
  · exact R59669
  · exact R59671
  · exact R59673
  · exact R59675
  · exact R59677
  · exact R59679
  · exact R59681
  · exact R59683
  · exact R59685
  · exact R59687
  · exact R59689
  · exact R59691
  · exact R59693
  · exact R59695
  · exact R59697
  · exact R59699
  · exact R59701
  · exact R59703
  · exact R59705
  · exact R59707
  · exact R59709
  · exact R59711
  · exact R59713
  · exact R59715
  · exact R59717
  · exact R59719
  · exact R59721
  · exact R59723
  · exact R59725
  · exact R59727
  · exact R59729
  · exact R59731
  · exact R59733
  · exact R59735
  · exact R59737
  · exact R59739
  · exact R59741
  · exact R59743
  · exact R59745
  · exact R59747
  · exact R59749
  · exact R59751
  · exact R59753
  · exact R59755
  · exact R59757
  · exact R59759
  · exact R59761
  · exact R59763
  · exact R59765
  · exact R59767
  · exact R59769
  · exact R59771
  · exact R59773
  · exact R59775
  · exact R59777
  · exact R59779
  · exact R59781
  · exact R59783
  · exact R59785
  · exact R59787
  · exact R59789
  · exact R59791
  · exact R59793
  · exact R59795
  · exact R59797
  · exact R59799
  · exact R59801
  · exact R59803
  · exact R59805
  · exact R59807
  · exact R59809
  · exact R59811
  · exact R59813
  · exact R59815
  · exact R59817
  · exact R59819
  · exact R59821
  · exact R59823
  · exact R59825
  · exact R59827
  · exact R59829
  · exact R59831
  · exact R59833
  · exact R59835
  · exact R59837
  · exact R59839
  · exact R59841
  · exact R59843
  · exact R59845
  · exact R59847
  · exact R59849
  · exact R59851
  · exact R59853
  · exact R59855
  · exact R59857
  · exact R59859
  · exact R59861
  · exact R59863
  · exact R59865
  · exact R59867
  · exact R59869
  · exact R59871
  · exact R59873
  · exact R59875
  · exact R59877
  · exact R59879
  · exact R59881
  · exact R59883
  · exact R59885
  · exact R59887
  · exact R59889
  · exact R59891
  · exact R59893
  · exact R59895
  · exact R59897
  · exact R59899
  · exact R59901
  · exact R59903
  · exact R59905
  · exact R59907
  · exact R59909
  · exact R59911
  · exact R59913
  · exact R59915
  · exact R59917
  · exact R59919
  · exact R59921
  · exact R59923
  · exact R59925
  · exact R59927
  · exact R59929
  · exact R59931
  · exact R59933
  · exact R59935
  · exact R59937
  · exact R59939
  · exact R59941
  · exact R59943
  · exact R59945
  · exact R59947
  · exact R59949
  · exact R59951
  · exact R59953
  · exact R59955
  · exact R59957
  · exact R59959
  · exact R59961
  · exact R59963
  · exact R59965
  · exact R59967
  · exact R59969
  · exact R59971
  · exact R59973
  · exact R59975
  · exact R59977
  · exact R59979
  · exact R59981
  · exact R59983
  · exact R59985
  · exact R59987
  · exact R59989
  · exact R59991
  · exact R59993
  · exact R59995
  · exact R59997
  · exact R59999
  · exact R60001
  · exact R60003
  · exact R60005
  · exact R60007
  · exact R60009
  · exact R60011
  · exact R60013
  · exact R60015
  · exact R60017
  · exact R60019
  · exact R60021
  · exact R60023
  · exact R60025
  · exact R60027
  · exact R60029
  · exact R60031
  · exact R60033
  · exact R60035
  · exact R60037
  · exact R60039
  · exact R60041
  · exact R60043
  · exact R60045
  · exact R60047
  · exact R60049
  · exact R60051
  · exact R60053
  · exact R60055
  · exact R60057
  · exact R60059
  · exact R60061
  · exact R60063
  · exact R60065
  · exact R60067
  · exact R60069
  · exact R60071
  · exact R60073
  · exact R60075
  · exact R60077
  · exact R60079
  · exact R60081
  · exact R60083
  · exact R60085
  · exact R60087
  · exact R60089
  · exact R60091
  · exact R60093
  · exact R60095
  · exact R60097
  · exact R60099
  · exact R60101
  · exact R60103
  · exact R60105
  · exact R60107
  · exact R60109
  · exact R60111
  · exact R60113
  · exact R60115
  · exact R60117
  · exact R60119
  · exact R60121
  · exact R60123
  · exact R60125
  · exact R60127
  · exact R60129
  · exact R60131
  · exact R60133
  · exact R60135
  · exact R60137
  · exact R60139
  · exact R60141
  · exact R60143
  · exact R60145
  · exact R60147
  · exact R60149
  · exact R60151
  · exact R60153
  · exact R60155
  · exact R60157
  · exact R60159
  · exact R60161
  · exact R60163
  · exact R60165
  · exact R60167
  · exact R60169
  · exact R60171
  · exact R60173
  · exact R60175
  · exact R60177
  · exact R60179
  · exact R60181
  · exact R60183
  · exact R60185
  · exact R60187
  · exact R60189
  · exact R60191
  · exact R60193
  · exact R60195
  · exact R60197
  · exact R60199
  · exact R60201
  · exact R60203
  · exact R60205
  · exact R60207
  · exact R60209
  · exact R60211
  · exact R60213
  · exact R60215
  · exact R60217
  · exact R60219
  · exact R60221
  · exact R60223
  · exact R60225
  · exact R60227
  · exact R60229
  · exact R60231
  · exact R60233
  · exact R60235
  · exact R60237
  · exact R60239
  · exact R60241
  · exact R60243
  · exact R60245
  · exact R60247
  · exact R60249
  · exact R60251
  · exact R60253
  · exact R60255
  · exact R60257
  · exact R60259
  · exact R60261
  · exact R60263
  · exact R60265
  · exact R60267
  · exact R60269
  · exact R60271
  · exact R60273
  · exact R60275
  · exact R60277
  · exact R60279
  · exact R60281
  · exact R60283
  · exact R60285
  · exact R60287
  · exact R60289
  · exact R60291
  · exact R60293
  · exact R60295
  · exact R60297
  · exact R60299
  · exact R60301
  · exact R60303
  · exact R60305
  · exact R60307
  · exact R60309
  · exact R60311
  · exact R60313
  · exact R60315
  · exact R60317
  · exact R60319
  · exact R60321
  · exact R60323
  · exact R60325
  · exact R60327
  · exact R60329
  · exact R60331
  · exact R60333
  · exact R60335
  · exact R60337
  · exact R60339
  · exact R60341
  · exact R60343
  · exact R60345
  · exact R60347
  · exact R60349
  · exact R60351
  · exact R60353
  · exact R60355
  · exact R60357
  · exact R60359
  · exact R60361
  · exact R60363
  · exact R60365
  · exact R60367
  · exact R60369
  · exact R60371
  · exact R60373
  · exact R60375
  · exact R60377
  · exact R60379
  · exact R60381
  · exact R60383
  · exact R60385
  · exact R60387
  · exact R60389
  · exact R60391
  · exact R60393
  · exact R60395
  · exact R60397
  · exact R60399
  · exact R60401
  · exact R60403
  · exact R60405
  · exact R60407
  · exact R60409
  · exact R60411
  · exact R60413
  · exact R60415
  · exact R60417
  · exact R60419
  · exact R60421
  · exact R60423
  · exact R60425
  · exact R60427
  · exact R60429
  · exact R60431
  · exact R60433
  · exact R60435
  · exact R60437
  · exact R60439
  · exact R60441
  · exact R60443
  · exact R60445
  · exact R60447
  · exact R60449
  · exact R60451
  · exact R60453
  · exact R60455
  · exact R60457
  · exact R60459
  · exact R60461
  · exact R60463
  · exact R60465
  · exact R60467
  · exact R60469
  · exact R60471
  · exact R60473
  · exact R60475
  · exact R60477
  · exact R60479
  · exact R60481
  · exact R60483
  · exact R60485
  · exact R60487
  · exact R60489
  · exact R60491
  · exact R60493
  · exact R60495
  · exact R60497
  · exact R60499
  · exact R60501
  · exact R60503
  · exact R60505
  · exact R60507
  · exact R60509
  · exact R60511
  · exact R60513
  · exact R60515
  · exact R60517
  · exact R60519
  · exact R60521

theorem C1 (j : ℕ) (h1 : 30261 ≤ j) (h2 : j ≤ 30960) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R60523
  · exact R60525
  · exact R60527
  · exact R60529
  · exact R60531
  · exact R60533
  · exact R60535
  · exact R60537
  · exact R60539
  · exact R60541
  · exact R60543
  · exact R60545
  · exact R60547
  · exact R60549
  · exact R60551
  · exact R60553
  · exact R60555
  · exact R60557
  · exact R60559
  · exact R60561
  · exact R60563
  · exact R60565
  · exact R60567
  · exact R60569
  · exact R60571
  · exact R60573
  · exact R60575
  · exact R60577
  · exact R60579
  · exact R60581
  · exact R60583
  · exact R60585
  · exact R60587
  · exact R60589
  · exact R60591
  · exact R60593
  · exact R60595
  · exact R60597
  · exact R60599
  · exact R60601
  · exact R60603
  · exact R60605
  · exact R60607
  · exact R60609
  · exact R60611
  · exact R60613
  · exact R60615
  · exact R60617
  · exact R60619
  · exact R60621
  · exact R60623
  · exact R60625
  · exact R60627
  · exact R60629
  · exact R60631
  · exact R60633
  · exact R60635
  · exact R60637
  · exact R60639
  · exact R60641
  · exact R60643
  · exact R60645
  · exact R60647
  · exact R60649
  · exact R60651
  · exact R60653
  · exact R60655
  · exact R60657
  · exact R60659
  · exact R60661
  · exact R60663
  · exact R60665
  · exact R60667
  · exact R60669
  · exact R60671
  · exact R60673
  · exact R60675
  · exact R60677
  · exact R60679
  · exact R60681
  · exact R60683
  · exact R60685
  · exact R60687
  · exact R60689
  · exact R60691
  · exact R60693
  · exact R60695
  · exact R60697
  · exact R60699
  · exact R60701
  · exact R60703
  · exact R60705
  · exact R60707
  · exact R60709
  · exact R60711
  · exact R60713
  · exact R60715
  · exact R60717
  · exact R60719
  · exact R60721
  · exact R60723
  · exact R60725
  · exact R60727
  · exact R60729
  · exact R60731
  · exact R60733
  · exact R60735
  · exact R60737
  · exact R60739
  · exact R60741
  · exact R60743
  · exact R60745
  · exact R60747
  · exact R60749
  · exact R60751
  · exact R60753
  · exact R60755
  · exact R60757
  · exact R60759
  · exact R60761
  · exact R60763
  · exact R60765
  · exact R60767
  · exact R60769
  · exact R60771
  · exact R60773
  · exact R60775
  · exact R60777
  · exact R60779
  · exact R60781
  · exact R60783
  · exact R60785
  · exact R60787
  · exact R60789
  · exact R60791
  · exact R60793
  · exact R60795
  · exact R60797
  · exact R60799
  · exact R60801
  · exact R60803
  · exact R60805
  · exact R60807
  · exact R60809
  · exact R60811
  · exact R60813
  · exact R60815
  · exact R60817
  · exact R60819
  · exact R60821
  · exact R60823
  · exact R60825
  · exact R60827
  · exact R60829
  · exact R60831
  · exact R60833
  · exact R60835
  · exact R60837
  · exact R60839
  · exact R60841
  · exact R60843
  · exact R60845
  · exact R60847
  · exact R60849
  · exact R60851
  · exact R60853
  · exact R60855
  · exact R60857
  · exact R60859
  · exact R60861
  · exact R60863
  · exact R60865
  · exact R60867
  · exact R60869
  · exact R60871
  · exact R60873
  · exact R60875
  · exact R60877
  · exact R60879
  · exact R60881
  · exact R60883
  · exact R60885
  · exact R60887
  · exact R60889
  · exact R60891
  · exact R60893
  · exact R60895
  · exact R60897
  · exact R60899
  · exact R60901
  · exact R60903
  · exact R60905
  · exact R60907
  · exact R60909
  · exact R60911
  · exact R60913
  · exact R60915
  · exact R60917
  · exact R60919
  · exact R60921
  · exact R60923
  · exact R60925
  · exact R60927
  · exact R60929
  · exact R60931
  · exact R60933
  · exact R60935
  · exact R60937
  · exact R60939
  · exact R60941
  · exact R60943
  · exact R60945
  · exact R60947
  · exact R60949
  · exact R60951
  · exact R60953
  · exact R60955
  · exact R60957
  · exact R60959
  · exact R60961
  · exact R60963
  · exact R60965
  · exact R60967
  · exact R60969
  · exact R60971
  · exact R60973
  · exact R60975
  · exact R60977
  · exact R60979
  · exact R60981
  · exact R60983
  · exact R60985
  · exact R60987
  · exact R60989
  · exact R60991
  · exact R60993
  · exact R60995
  · exact R60997
  · exact R60999
  · exact R61001
  · exact R61003
  · exact R61005
  · exact R61007
  · exact R61009
  · exact R61011
  · exact R61013
  · exact R61015
  · exact R61017
  · exact R61019
  · exact R61021
  · exact R61023
  · exact R61025
  · exact R61027
  · exact R61029
  · exact R61031
  · exact R61033
  · exact R61035
  · exact R61037
  · exact R61039
  · exact R61041
  · exact R61043
  · exact R61045
  · exact R61047
  · exact R61049
  · exact R61051
  · exact R61053
  · exact R61055
  · exact R61057
  · exact R61059
  · exact R61061
  · exact R61063
  · exact R61065
  · exact R61067
  · exact R61069
  · exact R61071
  · exact R61073
  · exact R61075
  · exact R61077
  · exact R61079
  · exact R61081
  · exact R61083
  · exact R61085
  · exact R61087
  · exact R61089
  · exact R61091
  · exact R61093
  · exact R61095
  · exact R61097
  · exact R61099
  · exact R61101
  · exact R61103
  · exact R61105
  · exact R61107
  · exact R61109
  · exact R61111
  · exact R61113
  · exact R61115
  · exact R61117
  · exact R61119
  · exact R61121
  · exact R61123
  · exact R61125
  · exact R61127
  · exact R61129
  · exact R61131
  · exact R61133
  · exact R61135
  · exact R61137
  · exact R61139
  · exact R61141
  · exact R61143
  · exact R61145
  · exact R61147
  · exact R61149
  · exact R61151
  · exact R61153
  · exact R61155
  · exact R61157
  · exact R61159
  · exact R61161
  · exact R61163
  · exact R61165
  · exact R61167
  · exact R61169
  · exact R61171
  · exact R61173
  · exact R61175
  · exact R61177
  · exact R61179
  · exact R61181
  · exact R61183
  · exact R61185
  · exact R61187
  · exact R61189
  · exact R61191
  · exact R61193
  · exact R61195
  · exact R61197
  · exact R61199
  · exact R61201
  · exact R61203
  · exact R61205
  · exact R61207
  · exact R61209
  · exact R61211
  · exact R61213
  · exact R61215
  · exact R61217
  · exact R61219
  · exact R61221
  · exact R61223
  · exact R61225
  · exact R61227
  · exact R61229
  · exact R61231
  · exact R61233
  · exact R61235
  · exact R61237
  · exact R61239
  · exact R61241
  · exact R61243
  · exact R61245
  · exact R61247
  · exact R61249
  · exact R61251
  · exact R61253
  · exact R61255
  · exact R61257
  · exact R61259
  · exact R61261
  · exact R61263
  · exact R61265
  · exact R61267
  · exact R61269
  · exact R61271
  · exact R61273
  · exact R61275
  · exact R61277
  · exact R61279
  · exact R61281
  · exact R61283
  · exact R61285
  · exact R61287
  · exact R61289
  · exact R61291
  · exact R61293
  · exact R61295
  · exact R61297
  · exact R61299
  · exact R61301
  · exact R61303
  · exact R61305
  · exact R61307
  · exact R61309
  · exact R61311
  · exact R61313
  · exact R61315
  · exact R61317
  · exact R61319
  · exact R61321
  · exact R61323
  · exact R61325
  · exact R61327
  · exact R61329
  · exact R61331
  · exact R61333
  · exact R61335
  · exact R61337
  · exact R61339
  · exact R61341
  · exact R61343
  · exact R61345
  · exact R61347
  · exact R61349
  · exact R61351
  · exact R61353
  · exact R61355
  · exact R61357
  · exact R61359
  · exact R61361
  · exact R61363
  · exact R61365
  · exact R61367
  · exact R61369
  · exact R61371
  · exact R61373
  · exact R61375
  · exact R61377
  · exact R61379
  · exact R61381
  · exact R61383
  · exact R61385
  · exact R61387
  · exact R61389
  · exact R61391
  · exact R61393
  · exact R61395
  · exact R61397
  · exact R61399
  · exact R61401
  · exact R61403
  · exact R61405
  · exact R61407
  · exact R61409
  · exact R61411
  · exact R61413
  · exact R61415
  · exact R61417
  · exact R61419
  · exact R61421
  · exact R61423
  · exact R61425
  · exact R61427
  · exact R61429
  · exact R61431
  · exact R61433
  · exact R61435
  · exact R61437
  · exact R61439
  · exact R61441
  · exact R61443
  · exact R61445
  · exact R61447
  · exact R61449
  · exact R61451
  · exact R61453
  · exact R61455
  · exact R61457
  · exact R61459
  · exact R61461
  · exact R61463
  · exact R61465
  · exact R61467
  · exact R61469
  · exact R61471
  · exact R61473
  · exact R61475
  · exact R61477
  · exact R61479
  · exact R61481
  · exact R61483
  · exact R61485
  · exact R61487
  · exact R61489
  · exact R61491
  · exact R61493
  · exact R61495
  · exact R61497
  · exact R61499
  · exact R61501
  · exact R61503
  · exact R61505
  · exact R61507
  · exact R61509
  · exact R61511
  · exact R61513
  · exact R61515
  · exact R61517
  · exact R61519
  · exact R61521
  · exact R61523
  · exact R61525
  · exact R61527
  · exact R61529
  · exact R61531
  · exact R61533
  · exact R61535
  · exact R61537
  · exact R61539
  · exact R61541
  · exact R61543
  · exact R61545
  · exact R61547
  · exact R61549
  · exact R61551
  · exact R61553
  · exact R61555
  · exact R61557
  · exact R61559
  · exact R61561
  · exact R61563
  · exact R61565
  · exact R61567
  · exact R61569
  · exact R61571
  · exact R61573
  · exact R61575
  · exact R61577
  · exact R61579
  · exact R61581
  · exact R61583
  · exact R61585
  · exact R61587
  · exact R61589
  · exact R61591
  · exact R61593
  · exact R61595
  · exact R61597
  · exact R61599
  · exact R61601
  · exact R61603
  · exact R61605
  · exact R61607
  · exact R61609
  · exact R61611
  · exact R61613
  · exact R61615
  · exact R61617
  · exact R61619
  · exact R61621
  · exact R61623
  · exact R61625
  · exact R61627
  · exact R61629
  · exact R61631
  · exact R61633
  · exact R61635
  · exact R61637
  · exact R61639
  · exact R61641
  · exact R61643
  · exact R61645
  · exact R61647
  · exact R61649
  · exact R61651
  · exact R61653
  · exact R61655
  · exact R61657
  · exact R61659
  · exact R61661
  · exact R61663
  · exact R61665
  · exact R61667
  · exact R61669
  · exact R61671
  · exact R61673
  · exact R61675
  · exact R61677
  · exact R61679
  · exact R61681
  · exact R61683
  · exact R61685
  · exact R61687
  · exact R61689
  · exact R61691
  · exact R61693
  · exact R61695
  · exact R61697
  · exact R61699
  · exact R61701
  · exact R61703
  · exact R61705
  · exact R61707
  · exact R61709
  · exact R61711
  · exact R61713
  · exact R61715
  · exact R61717
  · exact R61719
  · exact R61721
  · exact R61723
  · exact R61725
  · exact R61727
  · exact R61729
  · exact R61731
  · exact R61733
  · exact R61735
  · exact R61737
  · exact R61739
  · exact R61741
  · exact R61743
  · exact R61745
  · exact R61747
  · exact R61749
  · exact R61751
  · exact R61753
  · exact R61755
  · exact R61757
  · exact R61759
  · exact R61761
  · exact R61763
  · exact R61765
  · exact R61767
  · exact R61769
  · exact R61771
  · exact R61773
  · exact R61775
  · exact R61777
  · exact R61779
  · exact R61781
  · exact R61783
  · exact R61785
  · exact R61787
  · exact R61789
  · exact R61791
  · exact R61793
  · exact R61795
  · exact R61797
  · exact R61799
  · exact R61801
  · exact R61803
  · exact R61805
  · exact R61807
  · exact R61809
  · exact R61811
  · exact R61813
  · exact R61815
  · exact R61817
  · exact R61819
  · exact R61821
  · exact R61823
  · exact R61825
  · exact R61827
  · exact R61829
  · exact R61831
  · exact R61833
  · exact R61835
  · exact R61837
  · exact R61839
  · exact R61841
  · exact R61843
  · exact R61845
  · exact R61847
  · exact R61849
  · exact R61851
  · exact R61853
  · exact R61855
  · exact R61857
  · exact R61859
  · exact R61861
  · exact R61863
  · exact R61865
  · exact R61867
  · exact R61869
  · exact R61871
  · exact R61873
  · exact R61875
  · exact R61877
  · exact R61879
  · exact R61881
  · exact R61883
  · exact R61885
  · exact R61887
  · exact R61889
  · exact R61891
  · exact R61893
  · exact R61895
  · exact R61897
  · exact R61899
  · exact R61901
  · exact R61903
  · exact R61905
  · exact R61907
  · exact R61909
  · exact R61911
  · exact R61913
  · exact R61915
  · exact R61917
  · exact R61919
  · exact R61921

theorem C2 (j : ℕ) (h1 : 30961 ≤ j) (h2 : j ≤ 31560) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R61923
  · exact R61925
  · exact R61927
  · exact R61929
  · exact R61931
  · exact R61933
  · exact R61935
  · exact R61937
  · exact R61939
  · exact R61941
  · exact R61943
  · exact R61945
  · exact R61947
  · exact R61949
  · exact R61951
  · exact R61953
  · exact R61955
  · exact R61957
  · exact R61959
  · exact R61961
  · exact R61963
  · exact R61965
  · exact R61967
  · exact R61969
  · exact R61971
  · exact R61973
  · exact R61975
  · exact R61977
  · exact R61979
  · exact R61981
  · exact R61983
  · exact R61985
  · exact R61987
  · exact R61989
  · exact R61991
  · exact R61993
  · exact R61995
  · exact R61997
  · exact R61999
  · exact R62001
  · exact R62003
  · exact R62005
  · exact R62007
  · exact R62009
  · exact R62011
  · exact R62013
  · exact R62015
  · exact R62017
  · exact R62019
  · exact R62021
  · exact R62023
  · exact R62025
  · exact R62027
  · exact R62029
  · exact R62031
  · exact R62033
  · exact R62035
  · exact R62037
  · exact R62039
  · exact R62041
  · exact R62043
  · exact R62045
  · exact R62047
  · exact R62049
  · exact R62051
  · exact R62053
  · exact R62055
  · exact R62057
  · exact R62059
  · exact R62061
  · exact R62063
  · exact R62065
  · exact R62067
  · exact R62069
  · exact R62071
  · exact R62073
  · exact R62075
  · exact R62077
  · exact R62079
  · exact R62081
  · exact R62083
  · exact R62085
  · exact R62087
  · exact R62089
  · exact R62091
  · exact R62093
  · exact R62095
  · exact R62097
  · exact R62099
  · exact R62101
  · exact R62103
  · exact R62105
  · exact R62107
  · exact R62109
  · exact R62111
  · exact R62113
  · exact R62115
  · exact R62117
  · exact R62119
  · exact R62121
  · exact R62123
  · exact R62125
  · exact R62127
  · exact R62129
  · exact R62131
  · exact R62133
  · exact R62135
  · exact R62137
  · exact R62139
  · exact R62141
  · exact R62143
  · exact R62145
  · exact R62147
  · exact R62149
  · exact R62151
  · exact R62153
  · exact R62155
  · exact R62157
  · exact R62159
  · exact R62161
  · exact R62163
  · exact R62165
  · exact R62167
  · exact R62169
  · exact R62171
  · exact R62173
  · exact R62175
  · exact R62177
  · exact R62179
  · exact R62181
  · exact R62183
  · exact R62185
  · exact R62187
  · exact R62189
  · exact R62191
  · exact R62193
  · exact R62195
  · exact R62197
  · exact R62199
  · exact R62201
  · exact R62203
  · exact R62205
  · exact R62207
  · exact R62209
  · exact R62211
  · exact R62213
  · exact R62215
  · exact R62217
  · exact R62219
  · exact R62221
  · exact R62223
  · exact R62225
  · exact R62227
  · exact R62229
  · exact R62231
  · exact R62233
  · exact R62235
  · exact R62237
  · exact R62239
  · exact R62241
  · exact R62243
  · exact R62245
  · exact R62247
  · exact R62249
  · exact R62251
  · exact R62253
  · exact R62255
  · exact R62257
  · exact R62259
  · exact R62261
  · exact R62263
  · exact R62265
  · exact R62267
  · exact R62269
  · exact R62271
  · exact R62273
  · exact R62275
  · exact R62277
  · exact R62279
  · exact R62281
  · exact R62283
  · exact R62285
  · exact R62287
  · exact R62289
  · exact R62291
  · exact R62293
  · exact R62295
  · exact R62297
  · exact R62299
  · exact R62301
  · exact R62303
  · exact R62305
  · exact R62307
  · exact R62309
  · exact R62311
  · exact R62313
  · exact R62315
  · exact R62317
  · exact R62319
  · exact R62321
  · exact R62323
  · exact R62325
  · exact R62327
  · exact R62329
  · exact R62331
  · exact R62333
  · exact R62335
  · exact R62337
  · exact R62339
  · exact R62341
  · exact R62343
  · exact R62345
  · exact R62347
  · exact R62349
  · exact R62351
  · exact R62353
  · exact R62355
  · exact R62357
  · exact R62359
  · exact R62361
  · exact R62363
  · exact R62365
  · exact R62367
  · exact R62369
  · exact R62371
  · exact R62373
  · exact R62375
  · exact R62377
  · exact R62379
  · exact R62381
  · exact R62383
  · exact R62385
  · exact R62387
  · exact R62389
  · exact R62391
  · exact R62393
  · exact R62395
  · exact R62397
  · exact R62399
  · exact R62401
  · exact R62403
  · exact R62405
  · exact R62407
  · exact R62409
  · exact R62411
  · exact R62413
  · exact R62415
  · exact R62417
  · exact R62419
  · exact R62421
  · exact R62423
  · exact R62425
  · exact R62427
  · exact R62429
  · exact R62431
  · exact R62433
  · exact R62435
  · exact R62437
  · exact R62439
  · exact R62441
  · exact R62443
  · exact R62445
  · exact R62447
  · exact R62449
  · exact R62451
  · exact R62453
  · exact R62455
  · exact R62457
  · exact R62459
  · exact R62461
  · exact R62463
  · exact R62465
  · exact R62467
  · exact R62469
  · exact R62471
  · exact R62473
  · exact R62475
  · exact R62477
  · exact R62479
  · exact R62481
  · exact R62483
  · exact R62485
  · exact R62487
  · exact R62489
  · exact R62491
  · exact R62493
  · exact R62495
  · exact R62497
  · exact R62499
  · exact R62501
  · exact R62503
  · exact R62505
  · exact R62507
  · exact R62509
  · exact R62511
  · exact R62513
  · exact R62515
  · exact R62517
  · exact R62519
  · exact R62521
  · exact R62523
  · exact R62525
  · exact R62527
  · exact R62529
  · exact R62531
  · exact R62533
  · exact R62535
  · exact R62537
  · exact R62539
  · exact R62541
  · exact R62543
  · exact R62545
  · exact R62547
  · exact R62549
  · exact R62551
  · exact R62553
  · exact R62555
  · exact R62557
  · exact R62559
  · exact R62561
  · exact R62563
  · exact R62565
  · exact R62567
  · exact R62569
  · exact R62571
  · exact R62573
  · exact R62575
  · exact R62577
  · exact R62579
  · exact R62581
  · exact R62583
  · exact R62585
  · exact R62587
  · exact R62589
  · exact R62591
  · exact R62593
  · exact R62595
  · exact R62597
  · exact R62599
  · exact R62601
  · exact R62603
  · exact R62605
  · exact R62607
  · exact R62609
  · exact R62611
  · exact R62613
  · exact R62615
  · exact R62617
  · exact R62619
  · exact R62621
  · exact R62623
  · exact R62625
  · exact R62627
  · exact R62629
  · exact R62631
  · exact R62633
  · exact R62635
  · exact R62637
  · exact R62639
  · exact R62641
  · exact R62643
  · exact R62645
  · exact R62647
  · exact R62649
  · exact R62651
  · exact R62653
  · exact R62655
  · exact R62657
  · exact R62659
  · exact R62661
  · exact R62663
  · exact R62665
  · exact R62667
  · exact R62669
  · exact R62671
  · exact R62673
  · exact R62675
  · exact R62677
  · exact R62679
  · exact R62681
  · exact R62683
  · exact R62685
  · exact R62687
  · exact R62689
  · exact R62691
  · exact R62693
  · exact R62695
  · exact R62697
  · exact R62699
  · exact R62701
  · exact R62703
  · exact R62705
  · exact R62707
  · exact R62709
  · exact R62711
  · exact R62713
  · exact R62715
  · exact R62717
  · exact R62719
  · exact R62721
  · exact R62723
  · exact R62725
  · exact R62727
  · exact R62729
  · exact R62731
  · exact R62733
  · exact R62735
  · exact R62737
  · exact R62739
  · exact R62741
  · exact R62743
  · exact R62745
  · exact R62747
  · exact R62749
  · exact R62751
  · exact R62753
  · exact R62755
  · exact R62757
  · exact R62759
  · exact R62761
  · exact R62763
  · exact R62765
  · exact R62767
  · exact R62769
  · exact R62771
  · exact R62773
  · exact R62775
  · exact R62777
  · exact R62779
  · exact R62781
  · exact R62783
  · exact R62785
  · exact R62787
  · exact R62789
  · exact R62791
  · exact R62793
  · exact R62795
  · exact R62797
  · exact R62799
  · exact R62801
  · exact R62803
  · exact R62805
  · exact R62807
  · exact R62809
  · exact R62811
  · exact R62813
  · exact R62815
  · exact R62817
  · exact R62819
  · exact R62821
  · exact R62823
  · exact R62825
  · exact R62827
  · exact R62829
  · exact R62831
  · exact R62833
  · exact R62835
  · exact R62837
  · exact R62839
  · exact R62841
  · exact R62843
  · exact R62845
  · exact R62847
  · exact R62849
  · exact R62851
  · exact R62853
  · exact R62855
  · exact R62857
  · exact R62859
  · exact R62861
  · exact R62863
  · exact R62865
  · exact R62867
  · exact R62869
  · exact R62871
  · exact R62873
  · exact R62875
  · exact R62877
  · exact R62879
  · exact R62881
  · exact R62883
  · exact R62885
  · exact R62887
  · exact R62889
  · exact R62891
  · exact R62893
  · exact R62895
  · exact R62897
  · exact R62899
  · exact R62901
  · exact R62903
  · exact R62905
  · exact R62907
  · exact R62909
  · exact R62911
  · exact R62913
  · exact R62915
  · exact R62917
  · exact R62919
  · exact R62921
  · exact R62923
  · exact R62925
  · exact R62927
  · exact R62929
  · exact R62931
  · exact R62933
  · exact R62935
  · exact R62937
  · exact R62939
  · exact R62941
  · exact R62943
  · exact R62945
  · exact R62947
  · exact R62949
  · exact R62951
  · exact R62953
  · exact R62955
  · exact R62957
  · exact R62959
  · exact R62961
  · exact R62963
  · exact R62965
  · exact R62967
  · exact R62969
  · exact R62971
  · exact R62973
  · exact R62975
  · exact R62977
  · exact R62979
  · exact R62981
  · exact R62983
  · exact R62985
  · exact R62987
  · exact R62989
  · exact R62991
  · exact R62993
  · exact R62995
  · exact R62997
  · exact R62999
  · exact R63001
  · exact R63003
  · exact R63005
  · exact R63007
  · exact R63009
  · exact R63011
  · exact R63013
  · exact R63015
  · exact R63017
  · exact R63019
  · exact R63021
  · exact R63023
  · exact R63025
  · exact R63027
  · exact R63029
  · exact R63031
  · exact R63033
  · exact R63035
  · exact R63037
  · exact R63039
  · exact R63041
  · exact R63043
  · exact R63045
  · exact R63047
  · exact R63049
  · exact R63051
  · exact R63053
  · exact R63055
  · exact R63057
  · exact R63059
  · exact R63061
  · exact R63063
  · exact R63065
  · exact R63067
  · exact R63069
  · exact R63071
  · exact R63073
  · exact R63075
  · exact R63077
  · exact R63079
  · exact R63081
  · exact R63083
  · exact R63085
  · exact R63087
  · exact R63089
  · exact R63091
  · exact R63093
  · exact R63095
  · exact R63097
  · exact R63099
  · exact R63101
  · exact R63103
  · exact R63105
  · exact R63107
  · exact R63109
  · exact R63111
  · exact R63113
  · exact R63115
  · exact R63117
  · exact R63119
  · exact R63121

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 63122) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 59122 with hlo | hlo
  · exact syracuse_reaches_one_below_59122 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 30261 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 30961 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
