-- Prove2me | solution 1 for syracuse_descends_range_1536465_1538465
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:56.127896+00:00
-- url     : https://prove2.me/submissions/4a29b1b0-398b-42c7-8aa6-ff7cf6726bb9

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

/-- Half of all odd numbers descend in a single Syracuse step, uniformly. -/
theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- `Blo L x` : some Syracuse iterate of `x` drops below `L`. -/
abbrev Blo (L x : ℕ) : Prop := ∃ t : ℕ, syracuseStep^[t] x < L

theorem bbase {L x y : ℕ} (h : syracuseStep x = y) (hy : y < L) : Blo L x :=
  ⟨1, by rw [Function.iterate_one, h]; exact hy⟩

theorem bstep {L x y : ℕ} (h : syracuseStep x = y) (hy : Blo L y) : Blo L x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact ht⟩

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


theorem B3457061 : Blo 1536465 3457061 := bbase (se 4 (by rfl) ⟨324099, by rfl⟩ : syracuseStep 3457061 = 648199) (by norm_num)
theorem B3285029 : Blo 1536465 3285029 := bbase (se 4 (by rfl) ⟨307971, by rfl⟩ : syracuseStep 3285029 = 615943) (by norm_num)
theorem B1728553 : Blo 1536465 1728553 := bbase (se 2 (by rfl) ⟨648207, by rfl⟩ : syracuseStep 1728553 = 1296415) (by norm_num)
theorem B1728589 : Blo 1536465 1728589 := bbase (se 3 (by rfl) ⟨324110, by rfl⟩ : syracuseStep 1728589 = 648221) (by norm_num)
theorem B3457133 : Blo 1536465 3457133 := bbase (se 3 (by rfl) ⟨648212, by rfl⟩ : syracuseStep 3457133 = 1296425) (by norm_num)
theorem B1728625 : Blo 1536465 1728625 := bbase (se 2 (by rfl) ⟨648234, by rfl⟩ : syracuseStep 1728625 = 1296469) (by norm_num)
theorem B3891341 : Blo 1536465 3891341 := bbase (se 3 (by rfl) ⟨729626, by rfl⟩ : syracuseStep 3891341 = 1459253) (by norm_num)
theorem B1728661 : Blo 1536465 1728661 := bbase (se 6 (by rfl) ⟨40515, by rfl⟩ : syracuseStep 1728661 = 81031) (by norm_num)
theorem B3457205 : Blo 1536465 3457205 := bbase (se 5 (by rfl) ⟨162056, by rfl⟩ : syracuseStep 3457205 = 324113) (by norm_num)
theorem B1728697 : Blo 1536465 1728697 := bbase (se 2 (by rfl) ⟨648261, by rfl⟩ : syracuseStep 1728697 = 1296523) (by norm_num)
theorem B29941973 : Blo 1536465 29941973 := bbase (se 7 (by rfl) ⟨350882, by rfl⟩ : syracuseStep 29941973 = 701765) (by norm_num)
theorem B1728733 : Blo 1536465 1728733 := bbase (se 3 (by rfl) ⟨324137, by rfl⟩ : syracuseStep 1728733 = 648275) (by norm_num)
theorem B5185781 : Blo 1536465 5185781 := bbase (se 5 (by rfl) ⟨243083, by rfl⟩ : syracuseStep 5185781 = 486167) (by norm_num)
theorem B3457277 : Blo 1536465 3457277 := bbase (se 3 (by rfl) ⟨648239, by rfl⟩ : syracuseStep 3457277 = 1296479) (by norm_num)
theorem B2769149 : Blo 1536465 2769149 := bbase (se 3 (by rfl) ⟨519215, by rfl⟩ : syracuseStep 2769149 = 1038431) (by norm_num)
theorem B1728769 : Blo 1536465 1728769 := bbase (se 2 (by rfl) ⟨648288, by rfl⟩ : syracuseStep 1728769 = 1296577) (by norm_num)
theorem B5841173 : Blo 1536465 5841173 := bbase (se 6 (by rfl) ⟨136902, by rfl⟩ : syracuseStep 5841173 = 273805) (by norm_num)
theorem B1728805 : Blo 1536465 1728805 := bbase (se 4 (by rfl) ⟨162075, by rfl⟩ : syracuseStep 1728805 = 324151) (by norm_num)
theorem B3457349 : Blo 1536465 3457349 := bbase (se 4 (by rfl) ⟨324126, by rfl⟩ : syracuseStep 3457349 = 648253) (by norm_num)
theorem B2769221 : Blo 1536465 2769221 := bbase (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) (by norm_num)
theorem B1728841 : Blo 1536465 1728841 := bbase (se 2 (by rfl) ⟨648315, by rfl⟩ : syracuseStep 1728841 = 1296631) (by norm_num)
theorem B1728877 : Blo 1536465 1728877 := bbase (se 3 (by rfl) ⟨324164, by rfl⟩ : syracuseStep 1728877 = 648329) (by norm_num)
theorem B3457421 : Blo 1536465 3457421 := bbase (se 3 (by rfl) ⟨648266, by rfl⟩ : syracuseStep 3457421 = 1296533) (by norm_num)
theorem B1728913 : Blo 1536465 1728913 := bbase (se 2 (by rfl) ⟨648342, by rfl⟩ : syracuseStep 1728913 = 1296685) (by norm_num)
theorem B1728949 : Blo 1536465 1728949 := bbase (se 5 (by rfl) ⟨81044, by rfl⟩ : syracuseStep 1728949 = 162089) (by norm_num)
theorem B3457493 : Blo 1536465 3457493 := bbase (se 7 (by rfl) ⟨40517, by rfl⟩ : syracuseStep 3457493 = 81035) (by norm_num)
theorem B2769365 : Blo 1536465 2769365 := bbase (se 7 (by rfl) ⟨32453, by rfl⟩ : syracuseStep 2769365 = 64907) (by norm_num)
theorem B1728985 : Blo 1536465 1728985 := bbase (se 2 (by rfl) ⟨648369, by rfl⟩ : syracuseStep 1728985 = 1296739) (by norm_num)
theorem B3891685 : Blo 1536465 3891685 := bbase (se 4 (by rfl) ⟨364845, by rfl⟩ : syracuseStep 3891685 = 729691) (by norm_num)
theorem B1729021 : Blo 1536465 1729021 := bbase (se 3 (by rfl) ⟨324191, by rfl⟩ : syracuseStep 1729021 = 648383) (by norm_num)
theorem B3457565 : Blo 1536465 3457565 := bbase (se 3 (by rfl) ⟨648293, by rfl⟩ : syracuseStep 3457565 = 1296587) (by norm_num)
theorem B2769437 : Blo 1536465 2769437 := bbase (se 3 (by rfl) ⟨519269, by rfl⟩ : syracuseStep 2769437 = 1038539) (by norm_num)
theorem B1729057 : Blo 1536465 1729057 := bbase (se 2 (by rfl) ⟨648396, by rfl⟩ : syracuseStep 1729057 = 1296793) (by norm_num)
theorem B7782965 : Blo 1536465 7782965 := bbase (se 5 (by rfl) ⟨364826, by rfl⟩ : syracuseStep 7782965 = 729653) (by norm_num)
theorem B1729093 : Blo 1536465 1729093 := bbase (se 4 (by rfl) ⟨162102, by rfl⟩ : syracuseStep 1729093 = 324205) (by norm_num)
theorem B5997125 : Blo 1536465 5997125 := bbase (se 4 (by rfl) ⟨562230, by rfl⟩ : syracuseStep 5997125 = 1124461) (by norm_num)
theorem B3891797 : Blo 1536465 3891797 := bbase (se 8 (by rfl) ⟨22803, by rfl⟩ : syracuseStep 3891797 = 45607) (by norm_num)
theorem B2916965 : Blo 1536465 2916965 := bbase (se 4 (by rfl) ⟨273465, by rfl⟩ : syracuseStep 2916965 = 546931) (by norm_num)
theorem B3457637 : Blo 1536465 3457637 := bbase (se 4 (by rfl) ⟨324153, by rfl⟩ : syracuseStep 3457637 = 648307) (by norm_num)
theorem B1729129 : Blo 1536465 1729129 := bbase (se 2 (by rfl) ⟨648423, by rfl⟩ : syracuseStep 1729129 = 1296847) (by norm_num)
theorem B2564717 : Blo 1536465 2564717 := bbase (se 3 (by rfl) ⟨480884, by rfl⟩ : syracuseStep 2564717 = 961769) (by norm_num)
theorem B1729165 : Blo 1536465 1729165 := bbase (se 3 (by rfl) ⟨324218, by rfl⟩ : syracuseStep 1729165 = 648437) (by norm_num)
theorem B9355925 : Blo 1536465 9355925 := bbase (se 6 (by rfl) ⟨219279, by rfl⟩ : syracuseStep 9355925 = 438559) (by norm_num)
theorem B5186213 : Blo 1536465 5186213 := bbase (se 4 (by rfl) ⟨486207, by rfl⟩ : syracuseStep 5186213 = 972415) (by norm_num)
theorem B3457709 : Blo 1536465 3457709 := bbase (se 3 (by rfl) ⟨648320, by rfl⟩ : syracuseStep 3457709 = 1296641) (by norm_num)
theorem B1729201 : Blo 1536465 1729201 := bbase (se 2 (by rfl) ⟨648450, by rfl⟩ : syracuseStep 1729201 = 1296901) (by norm_num)
theorem B1729237 : Blo 1536465 1729237 := bbase (se 7 (by rfl) ⟨20264, by rfl⟩ : syracuseStep 1729237 = 40529) (by norm_num)
theorem B9855701 : Blo 1536465 9855701 := bbase (se 7 (by rfl) ⟨115496, by rfl⟩ : syracuseStep 9855701 = 230993) (by norm_num)
theorem B2917109 : Blo 1536465 2917109 := bbase (se 5 (by rfl) ⟨136739, by rfl⟩ : syracuseStep 2917109 = 273479) (by norm_num)
theorem B3457781 : Blo 1536465 3457781 := bbase (se 5 (by rfl) ⟨162083, by rfl⟩ : syracuseStep 3457781 = 324167) (by norm_num)
theorem B2630389 : Blo 1536465 2630389 := bbase (se 5 (by rfl) ⟨123299, by rfl⟩ : syracuseStep 2630389 = 246599) (by norm_num)
theorem B1729273 : Blo 1536465 1729273 := bbase (se 2 (by rfl) ⟨648477, by rfl⟩ : syracuseStep 1729273 = 1296955) (by norm_num)
theorem B15770389 : Blo 1536465 15770389 := bbase (se 6 (by rfl) ⟨369618, by rfl⟩ : syracuseStep 15770389 = 739237) (by norm_num)
theorem B3891989 : Blo 1536465 3891989 := bbase (se 6 (by rfl) ⟨91218, by rfl⟩ : syracuseStep 3891989 = 182437) (by norm_num)
theorem B1729309 : Blo 1536465 1729309 := bbase (se 3 (by rfl) ⟨324245, by rfl⟩ : syracuseStep 1729309 = 648491) (by norm_num)
theorem B3457853 : Blo 1536465 3457853 := bbase (se 3 (by rfl) ⟨648347, by rfl⟩ : syracuseStep 3457853 = 1296695) (by norm_num)
theorem B1729345 : Blo 1536465 1729345 := bbase (se 2 (by rfl) ⟨648504, by rfl⟩ : syracuseStep 1729345 = 1297009) (by norm_num)
theorem B1729381 : Blo 1536465 1729381 := bbase (se 4 (by rfl) ⟨162129, by rfl⟩ : syracuseStep 1729381 = 324259) (by norm_num)
theorem B3457925 : Blo 1536465 3457925 := bbase (se 4 (by rfl) ⟨324180, by rfl⟩ : syracuseStep 3457925 = 648361) (by norm_num)
theorem B2999173 : Blo 1536465 2999173 := bbase (se 4 (by rfl) ⟨281172, by rfl⟩ : syracuseStep 2999173 = 562345) (by norm_num)
theorem B1729417 : Blo 1536465 1729417 := bbase (se 2 (by rfl) ⟨648531, by rfl⟩ : syracuseStep 1729417 = 1297063) (by norm_num)
theorem B1729453 : Blo 1536465 1729453 := bbase (se 3 (by rfl) ⟨324272, by rfl⟩ : syracuseStep 1729453 = 648545) (by norm_num)
theorem B11076533 : Blo 1536465 11076533 := bbase (se 5 (by rfl) ⟨519212, by rfl⟩ : syracuseStep 11076533 = 1038425) (by norm_num)
theorem B3457997 : Blo 1536465 3457997 := bbase (se 3 (by rfl) ⟨648374, by rfl⟩ : syracuseStep 3457997 = 1296749) (by norm_num)
theorem B1729489 : Blo 1536465 1729489 := bbase (se 2 (by rfl) ⟨648558, by rfl⟩ : syracuseStep 1729489 = 1297117) (by norm_num)
theorem B2188253 : Blo 1536465 2188253 := bbase (se 3 (by rfl) ⟨410297, by rfl⟩ : syracuseStep 2188253 = 820595) (by norm_num)
theorem B1729525 : Blo 1536465 1729525 := bbase (se 5 (by rfl) ⟨81071, by rfl⟩ : syracuseStep 1729525 = 162143) (by norm_num)
theorem B1663997 : Blo 1536465 1663997 := bbase (se 3 (by rfl) ⟨311999, by rfl⟩ : syracuseStep 1663997 = 623999) (by norm_num)
theorem B1557505 : Blo 1536465 1557505 := bbase (se 2 (by rfl) ⟨584064, by rfl⟩ : syracuseStep 1557505 = 1168129) (by norm_num)
theorem B2917397 : Blo 1536465 2917397 := bbase (se 6 (by rfl) ⟨68376, by rfl⟩ : syracuseStep 2917397 = 136753) (by norm_num)
theorem B3458069 : Blo 1536465 3458069 := bbase (se 6 (by rfl) ⟨81048, by rfl⟩ : syracuseStep 3458069 = 162097) (by norm_num)
theorem B1729561 : Blo 1536465 1729561 := bbase (se 2 (by rfl) ⟨648585, by rfl⟩ : syracuseStep 1729561 = 1297171) (by norm_num)
theorem B2188333 : Blo 1536465 2188333 := bbase (se 3 (by rfl) ⟨410312, by rfl⟩ : syracuseStep 2188333 = 820625) (by norm_num)
theorem B1729597 : Blo 1536465 1729597 := bbase (se 3 (by rfl) ⟨324299, by rfl⟩ : syracuseStep 1729597 = 648599) (by norm_num)
theorem B7390277 : Blo 1536465 7390277 := bbase (se 4 (by rfl) ⟨692838, by rfl⟩ : syracuseStep 7390277 = 1385677) (by norm_num)
theorem B5186645 : Blo 1536465 5186645 := bbase (se 8 (by rfl) ⟨30390, by rfl⟩ : syracuseStep 5186645 = 60781) (by norm_num)
theorem B3458141 : Blo 1536465 3458141 := bbase (se 3 (by rfl) ⟨648401, by rfl⟩ : syracuseStep 3458141 = 1296803) (by norm_num)
theorem B1729633 : Blo 1536465 1729633 := bbase (se 2 (by rfl) ⟨648612, by rfl⟩ : syracuseStep 1729633 = 1297225) (by norm_num)
theorem B1557605 : Blo 1536465 1557605 := bbase (se 4 (by rfl) ⟨146025, by rfl⟩ : syracuseStep 1557605 = 292051) (by norm_num)
theorem B3892333 : Blo 1536465 3892333 := bbase (se 3 (by rfl) ⟨729812, by rfl⟩ : syracuseStep 3892333 = 1459625) (by norm_num)
theorem B9978997 : Blo 1536465 9978997 := bbase (se 5 (by rfl) ⟨467765, by rfl⟩ : syracuseStep 9978997 = 935531) (by norm_num)
theorem B1729669 : Blo 1536465 1729669 := bbase (se 4 (by rfl) ⟨162156, by rfl⟩ : syracuseStep 1729669 = 324313) (by norm_num)
theorem B8316053 : Blo 1536465 8316053 := bbase (se 6 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 8316053 = 389815) (by norm_num)
theorem B3458213 : Blo 1536465 3458213 := bbase (se 4 (by rfl) ⟨324207, by rfl⟩ : syracuseStep 3458213 = 648415) (by norm_num)
theorem B2188453 : Blo 1536465 2188453 := bbase (se 4 (by rfl) ⟨205167, by rfl⟩ : syracuseStep 2188453 = 410335) (by norm_num)
theorem B1729705 : Blo 1536465 1729705 := bbase (se 2 (by rfl) ⟨648639, by rfl⟩ : syracuseStep 1729705 = 1297279) (by norm_num)
theorem B2917549 : Blo 1536465 2917549 := bbase (se 3 (by rfl) ⟨547040, by rfl⟩ : syracuseStep 2917549 = 1094081) (by norm_num)
theorem B1729741 : Blo 1536465 1729741 := bbase (se 3 (by rfl) ⟨324326, by rfl⟩ : syracuseStep 1729741 = 648653) (by norm_num)
theorem B3892445 : Blo 1536465 3892445 := bbase (se 3 (by rfl) ⟨729833, by rfl⟩ : syracuseStep 3892445 = 1459667) (by norm_num)
theorem B3458285 : Blo 1536465 3458285 := bbase (se 3 (by rfl) ⟨648428, by rfl⟩ : syracuseStep 3458285 = 1296857) (by norm_num)
theorem B1729777 : Blo 1536465 1729777 := bbase (se 2 (by rfl) ⟨648666, by rfl⟩ : syracuseStep 1729777 = 1297333) (by norm_num)
theorem B2188549 : Blo 1536465 2188549 := bbase (se 4 (by rfl) ⟨205176, by rfl⟩ : syracuseStep 2188549 = 410353) (by norm_num)
theorem B14771477 : Blo 1536465 14771477 := bbase (se 6 (by rfl) ⟨346206, by rfl⟩ : syracuseStep 14771477 = 692413) (by norm_num)
theorem B1729813 : Blo 1536465 1729813 := bbase (se 6 (by rfl) ⟨40542, by rfl⟩ : syracuseStep 1729813 = 81085) (by norm_num)
theorem B3458357 : Blo 1536465 3458357 := bbase (se 5 (by rfl) ⟨162110, by rfl⟩ : syracuseStep 3458357 = 324221) (by norm_num)
theorem B2770229 : Blo 1536465 2770229 := bbase (se 5 (by rfl) ⟨129854, by rfl⟩ : syracuseStep 2770229 = 259709) (by norm_num)
theorem B1729849 : Blo 1536465 1729849 := bbase (se 2 (by rfl) ⟨648693, by rfl⟩ : syracuseStep 1729849 = 1297387) (by norm_num)
theorem B1729885 : Blo 1536465 1729885 := bbase (se 3 (by rfl) ⟨324353, by rfl⟩ : syracuseStep 1729885 = 648707) (by norm_num)
theorem B3458429 : Blo 1536465 3458429 := bbase (se 3 (by rfl) ⟨648455, by rfl⟩ : syracuseStep 3458429 = 1296911) (by norm_num)
theorem B1729921 : Blo 1536465 1729921 := bbase (se 2 (by rfl) ⟨648720, by rfl⟩ : syracuseStep 1729921 = 1297441) (by norm_num)
theorem B3892637 : Blo 1536465 3892637 := bbase (se 3 (by rfl) ⟨729869, by rfl⟩ : syracuseStep 3892637 = 1459739) (by norm_num)
theorem B1729957 : Blo 1536465 1729957 := bbase (se 4 (by rfl) ⟨162183, by rfl⟩ : syracuseStep 1729957 = 324367) (by norm_num)
theorem B3458501 : Blo 1536465 3458501 := bbase (se 4 (by rfl) ⟨324234, by rfl⟩ : syracuseStep 3458501 = 648469) (by norm_num)
theorem B1729993 : Blo 1536465 1729993 := bbase (se 2 (by rfl) ⟨648747, by rfl⟩ : syracuseStep 1729993 = 1297495) (by norm_num)
theorem B2336213 : Blo 1536465 2336213 := bbase (se 7 (by rfl) ⟨27377, by rfl⟩ : syracuseStep 2336213 = 54755) (by norm_num)
theorem B2917853 : Blo 1536465 2917853 := bbase (se 3 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 2917853 = 1094195) (by norm_num)
theorem B1730029 : Blo 1536465 1730029 := bbase (se 3 (by rfl) ⟨324380, by rfl⟩ : syracuseStep 1730029 = 648761) (by norm_num)
theorem B5187077 : Blo 1536465 5187077 := bbase (se 4 (by rfl) ⟨486288, by rfl⟩ : syracuseStep 5187077 = 972577) (by norm_num)
theorem B6571525 : Blo 1536465 6571525 := bbase (se 4 (by rfl) ⟨616080, by rfl⟩ : syracuseStep 6571525 = 1232161) (by norm_num)
theorem B3458573 : Blo 1536465 3458573 := bbase (se 3 (by rfl) ⟨648482, by rfl⟩ : syracuseStep 3458573 = 1296965) (by norm_num)
theorem B1730065 : Blo 1536465 1730065 := bbase (se 2 (by rfl) ⟨648774, by rfl⟩ : syracuseStep 1730065 = 1297549) (by norm_num)
theorem B4154933 : Blo 1536465 4154933 := bbase (se 5 (by rfl) ⟨194762, by rfl⟩ : syracuseStep 4154933 = 389525) (by norm_num)
theorem B1730101 : Blo 1536465 1730101 := bbase (se 5 (by rfl) ⟨81098, by rfl⟩ : syracuseStep 1730101 = 162197) (by norm_num)
theorem B3458645 : Blo 1536465 3458645 := bbase (se 8 (by rfl) ⟨20265, by rfl⟩ : syracuseStep 3458645 = 40531) (by norm_num)
theorem B1730137 : Blo 1536465 1730137 := bbase (se 2 (by rfl) ⟨648801, by rfl⟩ : syracuseStep 1730137 = 1297603) (by norm_num)
theorem B1730173 : Blo 1536465 1730173 := bbase (se 3 (by rfl) ⟨324407, by rfl⟩ : syracuseStep 1730173 = 648815) (by norm_num)
theorem B3458717 : Blo 1536465 3458717 := bbase (se 3 (by rfl) ⟨648509, by rfl⟩ : syracuseStep 3458717 = 1297019) (by norm_num)
theorem B1730209 : Blo 1536465 1730209 := bbase (se 2 (by rfl) ⟨648828, by rfl⟩ : syracuseStep 1730209 = 1297657) (by norm_num)
theorem B1730245 : Blo 1536465 1730245 := bbase (se 4 (by rfl) ⟨162210, by rfl⟩ : syracuseStep 1730245 = 324421) (by norm_num)
theorem B3696349 : Blo 1536465 3696349 := bbase (se 3 (by rfl) ⟨693065, by rfl⟩ : syracuseStep 3696349 = 1386131) (by norm_num)
theorem B3458789 : Blo 1536465 3458789 := bbase (se 4 (by rfl) ⟨324261, by rfl⟩ : syracuseStep 3458789 = 648523) (by norm_num)
theorem B1730281 : Blo 1536465 1730281 := bbase (se 2 (by rfl) ⟨648855, by rfl⟩ : syracuseStep 1730281 = 1297711) (by norm_num)
theorem B2189045 : Blo 1536465 2189045 := bbase (se 5 (by rfl) ⟨102611, by rfl⟩ : syracuseStep 2189045 = 205223) (by norm_num)
theorem B3892981 : Blo 1536465 3892981 := bbase (se 5 (by rfl) ⟨182483, by rfl⟩ : syracuseStep 3892981 = 364967) (by norm_num)
theorem B1730317 : Blo 1536465 1730317 := bbase (se 3 (by rfl) ⟨324434, by rfl⟩ : syracuseStep 1730317 = 648869) (by norm_num)
theorem B3458861 : Blo 1536465 3458861 := bbase (se 3 (by rfl) ⟨648536, by rfl⟩ : syracuseStep 3458861 = 1297073) (by norm_num)
theorem B1730353 : Blo 1536465 1730353 := bbase (se 2 (by rfl) ⟨648882, by rfl⟩ : syracuseStep 1730353 = 1297765) (by norm_num)
theorem B5539637 : Blo 1536465 5539637 := bbase (se 5 (by rfl) ⟨259670, by rfl⟩ : syracuseStep 5539637 = 519341) (by norm_num)
theorem B7784261 : Blo 1536465 7784261 := bbase (se 4 (by rfl) ⟨729774, by rfl⟩ : syracuseStep 7784261 = 1459549) (by norm_num)
theorem B1730389 : Blo 1536465 1730389 := bbase (se 9 (by rfl) ⟨5069, by rfl⟩ : syracuseStep 1730389 = 10139) (by norm_num)
theorem B3893093 : Blo 1536465 3893093 := bbase (se 4 (by rfl) ⟨364977, by rfl⟩ : syracuseStep 3893093 = 729955) (by norm_num)
theorem B3458933 : Blo 1536465 3458933 := bbase (se 5 (by rfl) ⟨162137, by rfl⟩ : syracuseStep 3458933 = 324275) (by norm_num)
theorem B1730425 : Blo 1536465 1730425 := bbase (se 2 (by rfl) ⟨648909, by rfl⟩ : syracuseStep 1730425 = 1297819) (by norm_num)
theorem B1730461 : Blo 1536465 1730461 := bbase (se 3 (by rfl) ⟨324461, by rfl⟩ : syracuseStep 1730461 = 648923) (by norm_num)
theorem B5187509 : Blo 1536465 5187509 := bbase (se 5 (by rfl) ⟨243164, by rfl⟩ : syracuseStep 5187509 = 486329) (by norm_num)
theorem B3459005 : Blo 1536465 3459005 := bbase (se 3 (by rfl) ⟨648563, by rfl⟩ : syracuseStep 3459005 = 1297127) (by norm_num)
theorem B1730497 : Blo 1536465 1730497 := bbase (se 2 (by rfl) ⟨648936, by rfl⟩ : syracuseStep 1730497 = 1297873) (by norm_num)
theorem B1730533 : Blo 1536465 1730533 := bbase (se 4 (by rfl) ⟨162237, by rfl⟩ : syracuseStep 1730533 = 324475) (by norm_num)
theorem B8316917 : Blo 1536465 8316917 := bbase (se 5 (by rfl) ⟨389855, by rfl⟩ : syracuseStep 8316917 = 779711) (by norm_num)
theorem B3459077 : Blo 1536465 3459077 := bbase (se 4 (by rfl) ⟨324288, by rfl⟩ : syracuseStep 3459077 = 648577) (by norm_num)
theorem B1730569 : Blo 1536465 1730569 := bbase (se 2 (by rfl) ⟨648963, by rfl⟩ : syracuseStep 1730569 = 1297927) (by norm_num)
theorem B2336797 : Blo 1536465 2336797 := bbase (se 3 (by rfl) ⟨438149, by rfl⟩ : syracuseStep 2336797 = 876299) (by norm_num)
theorem B3893285 : Blo 1536465 3893285 := bbase (se 4 (by rfl) ⟨364995, by rfl⟩ : syracuseStep 3893285 = 729991) (by norm_num)
theorem B1730605 : Blo 1536465 1730605 := bbase (se 3 (by rfl) ⟨324488, by rfl⟩ : syracuseStep 1730605 = 648977) (by norm_num)
theorem B3459149 : Blo 1536465 3459149 := bbase (se 3 (by rfl) ⟨648590, by rfl⟩ : syracuseStep 3459149 = 1297181) (by norm_num)
theorem B1730641 : Blo 1536465 1730641 := bbase (se 2 (by rfl) ⟨648990, by rfl⟩ : syracuseStep 1730641 = 1297981) (by norm_num)
theorem B6236261 : Blo 1536465 6236261 := bbase (se 4 (by rfl) ⟨584649, by rfl⟩ : syracuseStep 6236261 = 1169299) (by norm_num)
theorem B1730677 : Blo 1536465 1730677 := bbase (se 5 (by rfl) ⟨81125, by rfl⟩ : syracuseStep 1730677 = 162251) (by norm_num)
theorem B3459221 : Blo 1536465 3459221 := bbase (se 6 (by rfl) ⟨81075, by rfl⟩ : syracuseStep 3459221 = 162151) (by norm_num)
theorem B2435221 : Blo 1536465 2435221 := bbase (se 6 (by rfl) ⟨57075, by rfl⟩ : syracuseStep 2435221 = 114151) (by norm_num)
theorem B1730713 : Blo 1536465 1730713 := bbase (se 2 (by rfl) ⟨649017, by rfl⟩ : syracuseStep 1730713 = 1298035) (by norm_num)
theorem B1665193 : Blo 1536465 1665193 := bbase (se 2 (by rfl) ⟨624447, by rfl⟩ : syracuseStep 1665193 = 1248895) (by norm_num)
theorem B1730749 : Blo 1536465 1730749 := bbase (se 3 (by rfl) ⟨324515, by rfl⟩ : syracuseStep 1730749 = 649031) (by norm_num)
theorem B2918605 : Blo 1536465 2918605 := bbase (se 3 (by rfl) ⟨547238, by rfl⟩ : syracuseStep 2918605 = 1094477) (by norm_num)
theorem B3459293 : Blo 1536465 3459293 := bbase (se 3 (by rfl) ⟨648617, by rfl⟩ : syracuseStep 3459293 = 1297235) (by norm_num)
theorem B1665293 : Blo 1536465 1665293 := bbase (se 3 (by rfl) ⟨312242, by rfl⟩ : syracuseStep 1665293 = 624485) (by norm_num)
theorem B8759573 : Blo 1536465 8759573 := bbase (se 6 (by rfl) ⟨205302, by rfl⟩ : syracuseStep 8759573 = 410605) (by norm_num)
theorem B2189597 : Blo 1536465 2189597 := bbase (se 3 (by rfl) ⟨410549, by rfl⟩ : syracuseStep 2189597 = 821099) (by norm_num)
theorem B3459365 : Blo 1536465 3459365 := bbase (se 4 (by rfl) ⟨324315, by rfl⟩ : syracuseStep 3459365 = 648631) (by norm_num)
theorem B2918749 : Blo 1536465 2918749 := bbase (se 3 (by rfl) ⟨547265, by rfl⟩ : syracuseStep 2918749 = 1094531) (by norm_num)
theorem B5187941 : Blo 1536465 5187941 := bbase (se 4 (by rfl) ⟨486369, by rfl⟩ : syracuseStep 5187941 = 972739) (by norm_num)
theorem B3459437 : Blo 1536465 3459437 := bbase (se 3 (by rfl) ⟨648644, by rfl⟩ : syracuseStep 3459437 = 1297289) (by norm_num)
theorem B3893629 : Blo 1536465 3893629 := bbase (se 3 (by rfl) ⟨730055, by rfl⟩ : syracuseStep 3893629 = 1460111) (by norm_num)
theorem B8751509 : Blo 1536465 8751509 := bbase (se 6 (by rfl) ⟨205113, by rfl⟩ : syracuseStep 8751509 = 410227) (by norm_num)
theorem B3459509 : Blo 1536465 3459509 := bbase (se 5 (by rfl) ⟨162164, by rfl⟩ : syracuseStep 3459509 = 324329) (by norm_num)
theorem B3893741 : Blo 1536465 3893741 := bbase (se 3 (by rfl) ⟨730076, by rfl⟩ : syracuseStep 3893741 = 1460153) (by norm_num)
theorem B11676149 : Blo 1536465 11676149 := bbase (se 5 (by rfl) ⟨547319, by rfl⟩ : syracuseStep 11676149 = 1094639) (by norm_num)
theorem B2918909 : Blo 1536465 2918909 := bbase (se 3 (by rfl) ⟨547295, by rfl⟩ : syracuseStep 2918909 = 1094591) (by norm_num)
theorem B3459581 : Blo 1536465 3459581 := bbase (se 3 (by rfl) ⟨648671, by rfl⟩ : syracuseStep 3459581 = 1297343) (by norm_num)
theorem B4926005 : Blo 1536465 4926005 := bbase (se 5 (by rfl) ⟨230906, by rfl⟩ : syracuseStep 4926005 = 461813) (by norm_num)
theorem B3459653 : Blo 1536465 3459653 := bbase (se 4 (by rfl) ⟨324342, by rfl⟩ : syracuseStep 3459653 = 648685) (by norm_num)
theorem B2959973 : Blo 1536465 2959973 := bbase (se 4 (by rfl) ⟨277497, by rfl⟩ : syracuseStep 2959973 = 554995) (by norm_num)
theorem B2919053 : Blo 1536465 2919053 := bbase (se 3 (by rfl) ⟨547322, by rfl⟩ : syracuseStep 2919053 = 1094645) (by norm_num)
theorem B3459725 : Blo 1536465 3459725 := bbase (se 3 (by rfl) ⟨648698, by rfl⟩ : syracuseStep 3459725 = 1297397) (by norm_num)
theorem B3893933 : Blo 1536465 3893933 := bbase (se 3 (by rfl) ⟨730112, by rfl⟩ : syracuseStep 3893933 = 1460225) (by norm_num)
theorem B2304701 : Blo 1536465 2304701 := bbase (se 3 (by rfl) ⟨432131, by rfl⟩ : syracuseStep 2304701 = 864263) (by norm_num)
theorem B1641169 : Blo 1536465 1641169 := bbase (se 2 (by rfl) ⟨615438, by rfl⟩ : syracuseStep 1641169 = 1230877) (by norm_num)
theorem B2304725 : Blo 1536465 2304725 := bbase (se 7 (by rfl) ⟨27008, by rfl⟩ : syracuseStep 2304725 = 54017) (by norm_num)
theorem B3459797 : Blo 1536465 3459797 := bbase (se 7 (by rfl) ⟨40544, by rfl⟩ : syracuseStep 3459797 = 81089) (by norm_num)
theorem B2304749 : Blo 1536465 2304749 := bbase (se 3 (by rfl) ⟨432140, by rfl⟩ : syracuseStep 2304749 = 864281) (by norm_num)
theorem B5835509 : Blo 1536465 5835509 := bbase (se 5 (by rfl) ⟨273539, by rfl⟩ : syracuseStep 5835509 = 547079) (by norm_num)
theorem B2304773 : Blo 1536465 2304773 := bbase (se 4 (by rfl) ⟨216072, by rfl⟩ : syracuseStep 2304773 = 432145) (by norm_num)
theorem B5188373 : Blo 1536465 5188373 := bbase (se 6 (by rfl) ⟨121602, by rfl⟩ : syracuseStep 5188373 = 243205) (by norm_num)
theorem B1641241 : Blo 1536465 1641241 := bbase (se 2 (by rfl) ⟨615465, by rfl⟩ : syracuseStep 1641241 = 1230931) (by norm_num)
theorem B2304797 : Blo 1536465 2304797 := bbase (se 3 (by rfl) ⟨432149, by rfl⟩ : syracuseStep 2304797 = 864299) (by norm_num)
theorem B3459869 : Blo 1536465 3459869 := bbase (se 3 (by rfl) ⟨648725, by rfl⟩ : syracuseStep 3459869 = 1297451) (by norm_num)
theorem B2304821 : Blo 1536465 2304821 := bbase (se 5 (by rfl) ⟨108038, by rfl⟩ : syracuseStep 2304821 = 216077) (by norm_num)
theorem B2304845 : Blo 1536465 2304845 := bbase (se 3 (by rfl) ⟨432158, by rfl⟩ : syracuseStep 2304845 = 864317) (by norm_num)
theorem B2304869 : Blo 1536465 2304869 := bbase (se 4 (by rfl) ⟨216081, by rfl⟩ : syracuseStep 2304869 = 432163) (by norm_num)
theorem B3459941 : Blo 1536465 3459941 := bbase (se 4 (by rfl) ⟨324369, by rfl⟩ : syracuseStep 3459941 = 648739) (by norm_num)
theorem B2304893 : Blo 1536465 2304893 := bbase (se 3 (by rfl) ⟨432167, by rfl⟩ : syracuseStep 2304893 = 864335) (by norm_num)
theorem B11668373 : Blo 1536465 11668373 := bbase (se 6 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 11668373 = 546955) (by norm_num)
theorem B2304917 : Blo 1536465 2304917 := bbase (se 6 (by rfl) ⟨54021, by rfl⟩ : syracuseStep 2304917 = 108043) (by norm_num)
theorem B3115925 : Blo 1536465 3115925 := bbase (se 6 (by rfl) ⟨73029, by rfl⟩ : syracuseStep 3115925 = 146059) (by norm_num)
theorem B4377509 : Blo 1536465 4377509 := bbase (se 4 (by rfl) ⟨410391, by rfl⟩ : syracuseStep 4377509 = 820783) (by norm_num)
theorem B2304941 : Blo 1536465 2304941 := bbase (se 3 (by rfl) ⟨432176, by rfl⟩ : syracuseStep 2304941 = 864353) (by norm_num)
theorem B2919341 : Blo 1536465 2919341 := bbase (se 3 (by rfl) ⟨547376, by rfl⟩ : syracuseStep 2919341 = 1094753) (by norm_num)
theorem B3460013 : Blo 1536465 3460013 := bbase (se 3 (by rfl) ⟨648752, by rfl⟩ : syracuseStep 3460013 = 1297505) (by norm_num)
theorem B7392181 : Blo 1536465 7392181 := bbase (se 5 (by rfl) ⟨346508, by rfl⟩ : syracuseStep 7392181 = 693017) (by norm_num)
theorem B2304965 : Blo 1536465 2304965 := bbase (se 4 (by rfl) ⟨216090, by rfl⟩ : syracuseStep 2304965 = 432181) (by norm_num)
theorem B7392197 : Blo 1536465 7392197 := bbase (se 4 (by rfl) ⟨693018, by rfl⟩ : syracuseStep 7392197 = 1386037) (by norm_num)
theorem B1641421 : Blo 1536465 1641421 := bbase (se 3 (by rfl) ⟨307766, by rfl⟩ : syracuseStep 1641421 = 615533) (by norm_num)
theorem B2304989 : Blo 1536465 2304989 := bbase (se 3 (by rfl) ⟨432185, by rfl⟩ : syracuseStep 2304989 = 864371) (by norm_num)
theorem B2305013 : Blo 1536465 2305013 := bbase (se 5 (by rfl) ⟨108047, by rfl⟩ : syracuseStep 2305013 = 216095) (by norm_num)
theorem B3460085 : Blo 1536465 3460085 := bbase (se 5 (by rfl) ⟨162191, by rfl⟩ : syracuseStep 3460085 = 324383) (by norm_num)
theorem B2305037 : Blo 1536465 2305037 := bbase (se 3 (by rfl) ⟨432194, by rfl⟩ : syracuseStep 2305037 = 864389) (by norm_num)
theorem B2190349 : Blo 1536465 2190349 := bbase (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) (by norm_num)
theorem B5835797 : Blo 1536465 5835797 := bbase (se 6 (by rfl) ⟨136776, by rfl⟩ : syracuseStep 5835797 = 273553) (by norm_num)
theorem B2305061 : Blo 1536465 2305061 := bbase (se 4 (by rfl) ⟨216099, by rfl⟩ : syracuseStep 2305061 = 432199) (by norm_num)
theorem B2305085 : Blo 1536465 2305085 := bbase (se 3 (by rfl) ⟨432203, by rfl⟩ : syracuseStep 2305085 = 864407) (by norm_num)
theorem B3460157 : Blo 1536465 3460157 := bbase (se 3 (by rfl) ⟨648779, by rfl⟩ : syracuseStep 3460157 = 1297559) (by norm_num)
theorem B2919493 : Blo 1536465 2919493 := bbase (se 4 (by rfl) ⟨273702, by rfl⟩ : syracuseStep 2919493 = 547405) (by norm_num)
theorem B2370629 : Blo 1536465 2370629 := bbase (se 4 (by rfl) ⟨222246, by rfl⟩ : syracuseStep 2370629 = 444493) (by norm_num)
theorem B2305109 : Blo 1536465 2305109 := bbase (se 8 (by rfl) ⟨13506, by rfl⟩ : syracuseStep 2305109 = 27013) (by norm_num)
theorem B7785557 : Blo 1536465 7785557 := bbase (se 8 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 7785557 = 91237) (by norm_num)
theorem B2305133 : Blo 1536465 2305133 := bbase (se 3 (by rfl) ⟨432212, by rfl⟩ : syracuseStep 2305133 = 864425) (by norm_num)
theorem B2305157 : Blo 1536465 2305157 := bbase (se 4 (by rfl) ⟨216108, by rfl⟩ : syracuseStep 2305157 = 432217) (by norm_num)
theorem B3460229 : Blo 1536465 3460229 := bbase (se 4 (by rfl) ⟨324396, by rfl⟩ : syracuseStep 3460229 = 648793) (by norm_num)
theorem B2305181 : Blo 1536465 2305181 := bbase (se 3 (by rfl) ⟨432221, by rfl⟩ : syracuseStep 2305181 = 864443) (by norm_num)
theorem B1944749 : Blo 1536465 1944749 := bbase (se 3 (by rfl) ⟨364640, by rfl⟩ : syracuseStep 1944749 = 729281) (by norm_num)
theorem B2337965 : Blo 1536465 2337965 := bbase (se 3 (by rfl) ⟨438368, by rfl⟩ : syracuseStep 2337965 = 876737) (by norm_num)
theorem B2305205 : Blo 1536465 2305205 := bbase (se 5 (by rfl) ⟨108056, by rfl⟩ : syracuseStep 2305205 = 216113) (by norm_num)
theorem B5188805 : Blo 1536465 5188805 := bbase (se 4 (by rfl) ⟨486450, by rfl⟩ : syracuseStep 5188805 = 972901) (by norm_num)
theorem B2305229 : Blo 1536465 2305229 := bbase (se 3 (by rfl) ⟨432230, by rfl⟩ : syracuseStep 2305229 = 864461) (by norm_num)
theorem B3460301 : Blo 1536465 3460301 := bbase (se 3 (by rfl) ⟨648806, by rfl⟩ : syracuseStep 3460301 = 1297613) (by norm_num)
theorem B1944805 : Blo 1536465 1944805 := bbase (se 4 (by rfl) ⟨182325, by rfl⟩ : syracuseStep 1944805 = 364651) (by norm_num)
theorem B2305253 : Blo 1536465 2305253 := bbase (se 4 (by rfl) ⟨216117, by rfl⟩ : syracuseStep 2305253 = 432235) (by norm_num)
theorem B2305277 : Blo 1536465 2305277 := bbase (se 3 (by rfl) ⟨432239, by rfl⟩ : syracuseStep 2305277 = 864479) (by norm_num)
theorem B2305301 : Blo 1536465 2305301 := bbase (se 6 (by rfl) ⟨54030, by rfl⟩ : syracuseStep 2305301 = 108061) (by norm_num)
theorem B3460373 : Blo 1536465 3460373 := bbase (se 6 (by rfl) ⟨81102, by rfl⟩ : syracuseStep 3460373 = 162205) (by norm_num)
theorem B6237461 : Blo 1536465 6237461 := bbase (se 6 (by rfl) ⟨146190, by rfl⟩ : syracuseStep 6237461 = 292381) (by norm_num)
theorem B2305325 : Blo 1536465 2305325 := bbase (se 3 (by rfl) ⟨432248, by rfl⟩ : syracuseStep 2305325 = 864497) (by norm_num)
theorem B1944901 : Blo 1536465 1944901 := bbase (se 4 (by rfl) ⟨182334, by rfl⟩ : syracuseStep 1944901 = 364669) (by norm_num)
theorem B2305349 : Blo 1536465 2305349 := bbase (se 4 (by rfl) ⟨216126, by rfl⟩ : syracuseStep 2305349 = 432253) (by norm_num)
theorem B2305373 : Blo 1536465 2305373 := bbase (se 3 (by rfl) ⟨432257, by rfl⟩ : syracuseStep 2305373 = 864515) (by norm_num)
theorem B3460445 : Blo 1536465 3460445 := bbase (se 3 (by rfl) ⟨648833, by rfl⟩ : syracuseStep 3460445 = 1297667) (by norm_num)
theorem B2305397 : Blo 1536465 2305397 := bbase (se 5 (by rfl) ⟨108065, by rfl⟩ : syracuseStep 2305397 = 216131) (by norm_num)
theorem B2919797 : Blo 1536465 2919797 := bbase (se 5 (by rfl) ⟨136865, by rfl⟩ : syracuseStep 2919797 = 273731) (by norm_num)
theorem B1641865 : Blo 1536465 1641865 := bbase (se 2 (by rfl) ⟨615699, by rfl⟩ : syracuseStep 1641865 = 1231399) (by norm_num)
theorem B2305421 : Blo 1536465 2305421 := bbase (se 3 (by rfl) ⟨432266, by rfl⟩ : syracuseStep 2305421 = 864533) (by norm_num)
theorem B2305445 : Blo 1536465 2305445 := bbase (se 4 (by rfl) ⟨216135, by rfl⟩ : syracuseStep 2305445 = 432271) (by norm_num)
theorem B3460517 : Blo 1536465 3460517 := bbase (se 4 (by rfl) ⟨324423, by rfl⟩ : syracuseStep 3460517 = 648847) (by norm_num)
theorem B4926901 : Blo 1536465 4926901 := bbase (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) (by norm_num)
theorem B8760757 : Blo 1536465 8760757 := bbase (se 5 (by rfl) ⟨410660, by rfl⟩ : syracuseStep 8760757 = 821321) (by norm_num)
theorem B2305469 : Blo 1536465 2305469 := bbase (se 3 (by rfl) ⟨432275, by rfl⟩ : syracuseStep 2305469 = 864551) (by norm_num)
theorem B2305493 : Blo 1536465 2305493 := bbase (se 7 (by rfl) ⟨27017, by rfl⟩ : syracuseStep 2305493 = 54035) (by norm_num)
theorem B23662037 : Blo 1536465 23662037 := bbase (se 7 (by rfl) ⟨277289, by rfl⟩ : syracuseStep 23662037 = 554579) (by norm_num)
theorem B2305517 : Blo 1536465 2305517 := bbase (se 3 (by rfl) ⟨432284, by rfl⟩ : syracuseStep 2305517 = 864569) (by norm_num)
theorem B3460589 : Blo 1536465 3460589 := bbase (se 3 (by rfl) ⟨648860, by rfl⟩ : syracuseStep 3460589 = 1297721) (by norm_num)
theorem B1945073 : Blo 1536465 1945073 := bbase (se 2 (by rfl) ⟨729402, by rfl⟩ : syracuseStep 1945073 = 1458805) (by norm_num)
theorem B8424949 : Blo 1536465 8424949 := bbase (se 5 (by rfl) ⟨394919, by rfl⟩ : syracuseStep 8424949 = 789839) (by norm_num)
theorem B2305541 : Blo 1536465 2305541 := bbase (se 4 (by rfl) ⟨216144, by rfl⟩ : syracuseStep 2305541 = 432289) (by norm_num)
theorem B1641989 : Blo 1536465 1641989 := bbase (se 4 (by rfl) ⟨153936, by rfl⟩ : syracuseStep 1641989 = 307873) (by norm_num)
theorem B2305565 : Blo 1536465 2305565 := bbase (se 3 (by rfl) ⟨432293, by rfl⟩ : syracuseStep 2305565 = 864587) (by norm_num)
theorem B1945129 : Blo 1536465 1945129 := bbase (se 2 (by rfl) ⟨729423, by rfl⟩ : syracuseStep 1945129 = 1458847) (by norm_num)
theorem B2305589 : Blo 1536465 2305589 := bbase (se 5 (by rfl) ⟨108074, by rfl⟩ : syracuseStep 2305589 = 216149) (by norm_num)
theorem B3460661 : Blo 1536465 3460661 := bbase (se 5 (by rfl) ⟨162218, by rfl⟩ : syracuseStep 3460661 = 324437) (by norm_num)
theorem B2305613 : Blo 1536465 2305613 := bbase (se 3 (by rfl) ⟨432302, by rfl⟩ : syracuseStep 2305613 = 864605) (by norm_num)
theorem B2305637 : Blo 1536465 2305637 := bbase (se 4 (by rfl) ⟨216153, by rfl⟩ : syracuseStep 2305637 = 432307) (by norm_num)
theorem B5189237 : Blo 1536465 5189237 := bbase (se 5 (by rfl) ⟨243245, by rfl⟩ : syracuseStep 5189237 = 486491) (by norm_num)
theorem B2305661 : Blo 1536465 2305661 := bbase (se 3 (by rfl) ⟨432311, by rfl⟩ : syracuseStep 2305661 = 864623) (by norm_num)
theorem B3460733 : Blo 1536465 3460733 := bbase (se 3 (by rfl) ⟨648887, by rfl⟩ : syracuseStep 3460733 = 1297775) (by norm_num)
theorem B1945225 : Blo 1536465 1945225 := bbase (se 2 (by rfl) ⟨729459, by rfl⟩ : syracuseStep 1945225 = 1458919) (by norm_num)
theorem B2305685 : Blo 1536465 2305685 := bbase (se 6 (by rfl) ⟨54039, by rfl⟩ : syracuseStep 2305685 = 108079) (by norm_num)
theorem B2305709 : Blo 1536465 2305709 := bbase (se 3 (by rfl) ⟨432320, by rfl⟩ : syracuseStep 2305709 = 864641) (by norm_num)
theorem B1846973 : Blo 1536465 1846973 := bbase (se 3 (by rfl) ⟨346307, by rfl⟩ : syracuseStep 1846973 = 692615) (by norm_num)
theorem B2305733 : Blo 1536465 2305733 := bbase (se 4 (by rfl) ⟨216162, by rfl⟩ : syracuseStep 2305733 = 432325) (by norm_num)
theorem B3460805 : Blo 1536465 3460805 := bbase (se 4 (by rfl) ⟨324450, by rfl⟩ : syracuseStep 3460805 = 648901) (by norm_num)
theorem B2305757 : Blo 1536465 2305757 := bbase (se 3 (by rfl) ⟨432329, by rfl⟩ : syracuseStep 2305757 = 864659) (by norm_num)
theorem B2305781 : Blo 1536465 2305781 := bbase (se 5 (by rfl) ⟨108083, by rfl⟩ : syracuseStep 2305781 = 216167) (by norm_num)
theorem B1642241 : Blo 1536465 1642241 := bbase (se 2 (by rfl) ⟨615840, by rfl⟩ : syracuseStep 1642241 = 1231681) (by norm_num)
theorem B2305805 : Blo 1536465 2305805 := bbase (se 3 (by rfl) ⟨432338, by rfl⟩ : syracuseStep 2305805 = 864677) (by norm_num)
theorem B3460877 : Blo 1536465 3460877 := bbase (se 3 (by rfl) ⟨648914, by rfl⟩ : syracuseStep 3460877 = 1297829) (by norm_num)
theorem B2305829 : Blo 1536465 2305829 := bbase (se 4 (by rfl) ⟨216171, by rfl⟩ : syracuseStep 2305829 = 432343) (by norm_num)
theorem B1945397 : Blo 1536465 1945397 := bbase (se 5 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 1945397 = 182381) (by norm_num)
theorem B2305853 : Blo 1536465 2305853 := bbase (se 3 (by rfl) ⟨432347, by rfl⟩ : syracuseStep 2305853 = 864695) (by norm_num)
theorem B4927301 : Blo 1536465 4927301 := bbase (se 4 (by rfl) ⟨461934, by rfl⟩ : syracuseStep 4927301 = 923869) (by norm_num)
theorem B2305877 : Blo 1536465 2305877 := bbase (se 9 (by rfl) ⟨6755, by rfl⟩ : syracuseStep 2305877 = 13511) (by norm_num)
theorem B3460949 : Blo 1536465 3460949 := bbase (se 9 (by rfl) ⟨10139, by rfl⟩ : syracuseStep 3460949 = 20279) (by norm_num)
theorem B1945453 : Blo 1536465 1945453 := bbase (se 3 (by rfl) ⟨364772, by rfl⟩ : syracuseStep 1945453 = 729545) (by norm_num)
theorem B2305901 : Blo 1536465 2305901 := bbase (se 3 (by rfl) ⟨432356, by rfl⟩ : syracuseStep 2305901 = 864713) (by norm_num)
theorem B1847161 : Blo 1536465 1847161 := bbase (se 2 (by rfl) ⟨692685, by rfl⟩ : syracuseStep 1847161 = 1385371) (by norm_num)
theorem B2305925 : Blo 1536465 2305925 := bbase (se 4 (by rfl) ⟨216180, by rfl⟩ : syracuseStep 2305925 = 432361) (by norm_num)
theorem B2305949 : Blo 1536465 2305949 := bbase (se 3 (by rfl) ⟨432365, by rfl⟩ : syracuseStep 2305949 = 864731) (by norm_num)
theorem B3461021 : Blo 1536465 3461021 := bbase (se 3 (by rfl) ⟨648941, by rfl⟩ : syracuseStep 3461021 = 1297883) (by norm_num)
theorem B6655925 : Blo 1536465 6655925 := bbase (se 5 (by rfl) ⟨311996, by rfl⟩ : syracuseStep 6655925 = 623993) (by norm_num)
theorem B2305973 : Blo 1536465 2305973 := bbase (se 5 (by rfl) ⟨108092, by rfl⟩ : syracuseStep 2305973 = 216185) (by norm_num)
theorem B1945549 : Blo 1536465 1945549 := bbase (se 3 (by rfl) ⟨364790, by rfl⟩ : syracuseStep 1945549 = 729581) (by norm_num)
theorem B2305997 : Blo 1536465 2305997 := bbase (se 3 (by rfl) ⟨432374, by rfl⟩ : syracuseStep 2305997 = 864749) (by norm_num)
theorem B2306021 : Blo 1536465 2306021 := bbase (se 4 (by rfl) ⟨216189, by rfl⟩ : syracuseStep 2306021 = 432379) (by norm_num)
theorem B3461093 : Blo 1536465 3461093 := bbase (se 4 (by rfl) ⟨324477, by rfl⟩ : syracuseStep 3461093 = 648955) (by norm_num)
theorem B2306045 : Blo 1536465 2306045 := bbase (se 3 (by rfl) ⟨432383, by rfl⟩ : syracuseStep 2306045 = 864767) (by norm_num)
theorem B2306069 : Blo 1536465 2306069 := bbase (se 6 (by rfl) ⟨54048, by rfl⟩ : syracuseStep 2306069 = 108097) (by norm_num)
theorem B5189669 : Blo 1536465 5189669 := bbase (se 4 (by rfl) ⟨486531, by rfl⟩ : syracuseStep 5189669 = 973063) (by norm_num)
theorem B2306093 : Blo 1536465 2306093 := bbase (se 3 (by rfl) ⟨432392, by rfl⟩ : syracuseStep 2306093 = 864785) (by norm_num)
theorem B3461165 : Blo 1536465 3461165 := bbase (se 3 (by rfl) ⟨648968, by rfl⟩ : syracuseStep 3461165 = 1297937) (by norm_num)
theorem B2306117 : Blo 1536465 2306117 := bbase (se 4 (by rfl) ⟨216198, by rfl⟩ : syracuseStep 2306117 = 432397) (by norm_num)
theorem B3117125 : Blo 1536465 3117125 := bbase (se 4 (by rfl) ⟨292230, by rfl⟩ : syracuseStep 3117125 = 584461) (by norm_num)
theorem B4378693 : Blo 1536465 4378693 := bbase (se 4 (by rfl) ⟨410502, by rfl⟩ : syracuseStep 4378693 = 821005) (by norm_num)
theorem B1847377 : Blo 1536465 1847377 := bbase (se 2 (by rfl) ⟨692766, by rfl⟩ : syracuseStep 1847377 = 1385533) (by norm_num)
theorem B2306141 : Blo 1536465 2306141 := bbase (se 3 (by rfl) ⟨432401, by rfl⟩ : syracuseStep 2306141 = 864803) (by norm_num)
theorem B2920549 : Blo 1536465 2920549 := bbase (se 4 (by rfl) ⟨273801, by rfl⟩ : syracuseStep 2920549 = 547603) (by norm_num)
theorem B2592877 : Blo 1536465 2592877 := bbase (se 3 (by rfl) ⟨486164, by rfl⟩ : syracuseStep 2592877 = 972329) (by norm_num)
theorem B10514549 : Blo 1536465 10514549 := bbase (se 5 (by rfl) ⟨492869, by rfl⟩ : syracuseStep 10514549 = 985739) (by norm_num)
theorem B2306165 : Blo 1536465 2306165 := bbase (se 5 (by rfl) ⟨108101, by rfl⟩ : syracuseStep 2306165 = 216203) (by norm_num)
theorem B3461237 : Blo 1536465 3461237 := bbase (se 5 (by rfl) ⟨162245, by rfl⟩ : syracuseStep 3461237 = 324491) (by norm_num)
theorem B1945721 : Blo 1536465 1945721 := bbase (se 2 (by rfl) ⟨729645, by rfl⟩ : syracuseStep 1945721 = 1459291) (by norm_num)
theorem B2306189 : Blo 1536465 2306189 := bbase (se 3 (by rfl) ⟨432410, by rfl⟩ : syracuseStep 2306189 = 864821) (by norm_num)
theorem B2306213 : Blo 1536465 2306213 := bbase (se 4 (by rfl) ⟨216207, by rfl⟩ : syracuseStep 2306213 = 432415) (by norm_num)
theorem B2076845 : Blo 1536465 2076845 := bbase (se 3 (by rfl) ⟨389408, by rfl⟩ : syracuseStep 2076845 = 778817) (by norm_num)
theorem B1945777 : Blo 1536465 1945777 := bbase (se 2 (by rfl) ⟨729666, by rfl⟩ : syracuseStep 1945777 = 1459333) (by norm_num)
theorem B5836981 : Blo 1536465 5836981 := bbase (se 5 (by rfl) ⟨273608, by rfl⟩ : syracuseStep 5836981 = 547217) (by norm_num)
theorem B2306237 : Blo 1536465 2306237 := bbase (se 3 (by rfl) ⟨432419, by rfl⟩ : syracuseStep 2306237 = 864839) (by norm_num)
theorem B1642685 : Blo 1536465 1642685 := bbase (se 3 (by rfl) ⟨308003, by rfl⟩ : syracuseStep 1642685 = 616007) (by norm_num)
theorem B3461309 : Blo 1536465 3461309 := bbase (se 3 (by rfl) ⟨648995, by rfl⟩ : syracuseStep 3461309 = 1297991) (by norm_num)
theorem B2592965 : Blo 1536465 2592965 := bbase (se 4 (by rfl) ⟨243090, by rfl⟩ : syracuseStep 2592965 = 486181) (by norm_num)
theorem B2306261 : Blo 1536465 2306261 := bbase (se 7 (by rfl) ⟨27026, by rfl⟩ : syracuseStep 2306261 = 54053) (by norm_num)
theorem B4378853 : Blo 1536465 4378853 := bbase (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) (by norm_num)
theorem B2306285 : Blo 1536465 2306285 := bbase (se 3 (by rfl) ⟨432428, by rfl⟩ : syracuseStep 2306285 = 864857) (by norm_num)
theorem B2306309 : Blo 1536465 2306309 := bbase (se 4 (by rfl) ⟨216216, by rfl⟩ : syracuseStep 2306309 = 432433) (by norm_num)
theorem B3461381 : Blo 1536465 3461381 := bbase (se 4 (by rfl) ⟨324504, by rfl⟩ : syracuseStep 3461381 = 649009) (by norm_num)
theorem B1945873 : Blo 1536465 1945873 := bbase (se 2 (by rfl) ⟨729702, by rfl⟩ : syracuseStep 1945873 = 1459405) (by norm_num)
theorem B2306333 : Blo 1536465 2306333 := bbase (se 3 (by rfl) ⟨432437, by rfl⟩ : syracuseStep 2306333 = 864875) (by norm_num)
theorem B2306357 : Blo 1536465 2306357 := bbase (se 5 (by rfl) ⟨108110, by rfl⟩ : syracuseStep 2306357 = 216221) (by norm_num)
theorem B11088181 : Blo 1536465 11088181 := bbase (se 5 (by rfl) ⟨519758, by rfl⟩ : syracuseStep 11088181 = 1039517) (by norm_num)
theorem B2593093 : Blo 1536465 2593093 := bbase (se 4 (by rfl) ⟨243102, by rfl⟩ : syracuseStep 2593093 = 486205) (by norm_num)
theorem B2306381 : Blo 1536465 2306381 := bbase (se 3 (by rfl) ⟨432446, by rfl⟩ : syracuseStep 2306381 = 864893) (by norm_num)
theorem B3461453 : Blo 1536465 3461453 := bbase (se 3 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 3461453 = 1298045) (by norm_num)
theorem B2306405 : Blo 1536465 2306405 := bbase (se 4 (by rfl) ⟨216225, by rfl⟩ : syracuseStep 2306405 = 432451) (by norm_num)
theorem B7786853 : Blo 1536465 7786853 := bbase (se 4 (by rfl) ⟨730017, by rfl⟩ : syracuseStep 7786853 = 1460035) (by norm_num)
theorem B1847665 : Blo 1536465 1847665 := bbase (se 2 (by rfl) ⟨692874, by rfl⟩ : syracuseStep 1847665 = 1385749) (by norm_num)
theorem B2306429 : Blo 1536465 2306429 := bbase (se 3 (by rfl) ⟨432455, by rfl⟩ : syracuseStep 2306429 = 864911) (by norm_num)
theorem B2462093 : Blo 1536465 2462093 := bbase (se 3 (by rfl) ⟨461642, by rfl⟩ : syracuseStep 2462093 = 923285) (by norm_num)
theorem B2306453 : Blo 1536465 2306453 := bbase (se 6 (by rfl) ⟨54057, by rfl⟩ : syracuseStep 2306453 = 108115) (by norm_num)
theorem B3461525 : Blo 1536465 3461525 := bbase (se 6 (by rfl) ⟨81129, by rfl⟩ : syracuseStep 3461525 = 162259) (by norm_num)
theorem B2593181 : Blo 1536465 2593181 := bbase (se 3 (by rfl) ⟨486221, by rfl⟩ : syracuseStep 2593181 = 972443) (by norm_num)
theorem B2306477 : Blo 1536465 2306477 := bbase (se 3 (by rfl) ⟨432464, by rfl⟩ : syracuseStep 2306477 = 864929) (by norm_num)
theorem B1946045 : Blo 1536465 1946045 := bbase (se 3 (by rfl) ⟨364883, by rfl⟩ : syracuseStep 1946045 = 729767) (by norm_num)
theorem B2306501 : Blo 1536465 2306501 := bbase (se 4 (by rfl) ⟨216234, by rfl⟩ : syracuseStep 2306501 = 432469) (by norm_num)
theorem B4379093 : Blo 1536465 4379093 := bbase (se 7 (by rfl) ⟨51317, by rfl⟩ : syracuseStep 4379093 = 102635) (by norm_num)
theorem B5190101 : Blo 1536465 5190101 := bbase (se 7 (by rfl) ⟨60821, by rfl⟩ : syracuseStep 5190101 = 121643) (by norm_num)
theorem B2306525 : Blo 1536465 2306525 := bbase (se 3 (by rfl) ⟨432473, by rfl⟩ : syracuseStep 2306525 = 864947) (by norm_num)
theorem B5837285 : Blo 1536465 5837285 := bbase (se 4 (by rfl) ⟨547245, by rfl⟩ : syracuseStep 5837285 = 1094491) (by norm_num)
theorem B1946101 : Blo 1536465 1946101 := bbase (se 5 (by rfl) ⟨91223, by rfl⟩ : syracuseStep 1946101 = 182447) (by norm_num)
theorem B2306549 : Blo 1536465 2306549 := bbase (se 5 (by rfl) ⟨108119, by rfl⟩ : syracuseStep 2306549 = 216239) (by norm_num)
theorem B2306573 : Blo 1536465 2306573 := bbase (se 3 (by rfl) ⟨432482, by rfl⟩ : syracuseStep 2306573 = 864965) (by norm_num)
theorem B2593309 : Blo 1536465 2593309 := bbase (se 3 (by rfl) ⟨486245, by rfl⟩ : syracuseStep 2593309 = 972491) (by norm_num)
theorem B2306597 : Blo 1536465 2306597 := bbase (se 4 (by rfl) ⟨216243, by rfl⟩ : syracuseStep 2306597 = 432487) (by norm_num)
theorem B6566453 : Blo 1536465 6566453 := bbase (se 5 (by rfl) ⟨307802, by rfl⟩ : syracuseStep 6566453 = 615605) (by norm_num)
theorem B2306621 : Blo 1536465 2306621 := bbase (se 3 (by rfl) ⟨432491, by rfl⟩ : syracuseStep 2306621 = 864983) (by norm_num)
theorem B2462285 : Blo 1536465 2462285 := bbase (se 3 (by rfl) ⟨461678, by rfl⟩ : syracuseStep 2462285 = 923357) (by norm_num)
theorem B1946197 : Blo 1536465 1946197 := bbase (se 8 (by rfl) ⟨11403, by rfl⟩ : syracuseStep 1946197 = 22807) (by norm_num)
theorem B2306645 : Blo 1536465 2306645 := bbase (se 8 (by rfl) ⟨13515, by rfl⟩ : syracuseStep 2306645 = 27031) (by norm_num)
theorem B2306669 : Blo 1536465 2306669 := bbase (se 3 (by rfl) ⟨432500, by rfl⟩ : syracuseStep 2306669 = 865001) (by norm_num)
theorem B2593397 : Blo 1536465 2593397 := bbase (se 5 (by rfl) ⟨121565, by rfl⟩ : syracuseStep 2593397 = 243131) (by norm_num)
theorem B2306693 : Blo 1536465 2306693 := bbase (se 4 (by rfl) ⟨216252, by rfl⟩ : syracuseStep 2306693 = 432505) (by norm_num)
theorem B4379285 : Blo 1536465 4379285 := bbase (se 6 (by rfl) ⟨102639, by rfl⟩ : syracuseStep 4379285 = 205279) (by norm_num)
theorem B2306717 : Blo 1536465 2306717 := bbase (se 3 (by rfl) ⟨432509, by rfl⟩ : syracuseStep 2306717 = 865019) (by norm_num)
theorem B2306741 : Blo 1536465 2306741 := bbase (se 5 (by rfl) ⟨108128, by rfl⟩ : syracuseStep 2306741 = 216257) (by norm_num)
theorem B3117757 : Blo 1536465 3117757 := bbase (se 3 (by rfl) ⟨584579, by rfl⟩ : syracuseStep 3117757 = 1169159) (by norm_num)
theorem B2306765 : Blo 1536465 2306765 := bbase (se 3 (by rfl) ⟨432518, by rfl⟩ : syracuseStep 2306765 = 865037) (by norm_num)
theorem B2306789 : Blo 1536465 2306789 := bbase (se 4 (by rfl) ⟨216261, by rfl⟩ : syracuseStep 2306789 = 432523) (by norm_num)
theorem B2593525 : Blo 1536465 2593525 := bbase (se 5 (by rfl) ⟨121571, by rfl⟩ : syracuseStep 2593525 = 243143) (by norm_num)
theorem B2306813 : Blo 1536465 2306813 := bbase (se 3 (by rfl) ⟨432527, by rfl⟩ : syracuseStep 2306813 = 865055) (by norm_num)
theorem B1946369 : Blo 1536465 1946369 := bbase (se 2 (by rfl) ⟨729888, by rfl⟩ : syracuseStep 1946369 = 1459777) (by norm_num)
theorem B7779077 : Blo 1536465 7779077 := bbase (se 4 (by rfl) ⟨729288, by rfl⟩ : syracuseStep 7779077 = 1458577) (by norm_num)
theorem B2306837 : Blo 1536465 2306837 := bbase (se 6 (by rfl) ⟨54066, by rfl⟩ : syracuseStep 2306837 = 108133) (by norm_num)
theorem B2306861 : Blo 1536465 2306861 := bbase (se 3 (by rfl) ⟨432536, by rfl⟩ : syracuseStep 2306861 = 865073) (by norm_num)
theorem B1946425 : Blo 1536465 1946425 := bbase (se 2 (by rfl) ⟨729909, by rfl⟩ : syracuseStep 1946425 = 1459819) (by norm_num)
theorem B2306885 : Blo 1536465 2306885 := bbase (se 4 (by rfl) ⟨216270, by rfl⟩ : syracuseStep 2306885 = 432541) (by norm_num)
theorem B2593613 : Blo 1536465 2593613 := bbase (se 3 (by rfl) ⟨486302, by rfl⟩ : syracuseStep 2593613 = 972605) (by norm_num)
theorem B6566741 : Blo 1536465 6566741 := bbase (se 9 (by rfl) ⟨19238, by rfl⟩ : syracuseStep 6566741 = 38477) (by norm_num)
theorem B2306909 : Blo 1536465 2306909 := bbase (se 3 (by rfl) ⟨432545, by rfl⟩ : syracuseStep 2306909 = 865091) (by norm_num)
theorem B2306933 : Blo 1536465 2306933 := bbase (se 5 (by rfl) ⟨108137, by rfl⟩ : syracuseStep 2306933 = 216275) (by norm_num)
theorem B5190533 : Blo 1536465 5190533 := bbase (se 4 (by rfl) ⟨486612, by rfl⟩ : syracuseStep 5190533 = 973225) (by norm_num)
theorem B2306957 : Blo 1536465 2306957 := bbase (se 3 (by rfl) ⟨432554, by rfl⟩ : syracuseStep 2306957 = 865109) (by norm_num)
theorem B1946521 : Blo 1536465 1946521 := bbase (se 2 (by rfl) ⟨729945, by rfl⟩ : syracuseStep 1946521 = 1459891) (by norm_num)
theorem B2306981 : Blo 1536465 2306981 := bbase (se 4 (by rfl) ⟨216279, by rfl⟩ : syracuseStep 2306981 = 432559) (by norm_num)
theorem B2307005 : Blo 1536465 2307005 := bbase (se 3 (by rfl) ⟨432563, by rfl⟩ : syracuseStep 2307005 = 865127) (by norm_num)
theorem B2593741 : Blo 1536465 2593741 := bbase (se 3 (by rfl) ⟨486326, by rfl⟩ : syracuseStep 2593741 = 972653) (by norm_num)
theorem B2307029 : Blo 1536465 2307029 := bbase (se 7 (by rfl) ⟨27035, by rfl⟩ : syracuseStep 2307029 = 54071) (by norm_num)
theorem B2307053 : Blo 1536465 2307053 := bbase (se 3 (by rfl) ⟨432572, by rfl⟩ : syracuseStep 2307053 = 865145) (by norm_num)
theorem B2307077 : Blo 1536465 2307077 := bbase (se 4 (by rfl) ⟨216288, by rfl⟩ : syracuseStep 2307077 = 432577) (by norm_num)
theorem B2307101 : Blo 1536465 2307101 := bbase (se 3 (by rfl) ⟨432581, by rfl⟩ : syracuseStep 2307101 = 865163) (by norm_num)
theorem B2593829 : Blo 1536465 2593829 := bbase (se 4 (by rfl) ⟨243171, by rfl⟩ : syracuseStep 2593829 = 486343) (by norm_num)
theorem B2307125 : Blo 1536465 2307125 := bbase (se 5 (by rfl) ⟨108146, by rfl⟩ : syracuseStep 2307125 = 216293) (by norm_num)
theorem B1946693 : Blo 1536465 1946693 := bbase (se 4 (by rfl) ⟨182502, by rfl⟩ : syracuseStep 1946693 = 365005) (by norm_num)
theorem B2307149 : Blo 1536465 2307149 := bbase (se 3 (by rfl) ⟨432590, by rfl⟩ : syracuseStep 2307149 = 865181) (by norm_num)
theorem B2307173 : Blo 1536465 2307173 := bbase (se 4 (by rfl) ⟨216297, by rfl⟩ : syracuseStep 2307173 = 432595) (by norm_num)
theorem B2307197 : Blo 1536465 2307197 := bbase (se 3 (by rfl) ⟨432599, by rfl⟩ : syracuseStep 2307197 = 865199) (by norm_num)
theorem B1946749 : Blo 1536465 1946749 := bbase (se 3 (by rfl) ⟨365015, by rfl⟩ : syracuseStep 1946749 = 730031) (by norm_num)
theorem B2307221 : Blo 1536465 2307221 := bbase (se 6 (by rfl) ⟨54075, by rfl⟩ : syracuseStep 2307221 = 108151) (by norm_num)
theorem B2593957 : Blo 1536465 2593957 := bbase (se 4 (by rfl) ⟨243183, by rfl⟩ : syracuseStep 2593957 = 486367) (by norm_num)
theorem B2307245 : Blo 1536465 2307245 := bbase (se 3 (by rfl) ⟨432608, by rfl⟩ : syracuseStep 2307245 = 865217) (by norm_num)
theorem B3118277 : Blo 1536465 3118277 := bbase (se 4 (by rfl) ⟨292338, by rfl⟩ : syracuseStep 3118277 = 584677) (by norm_num)
theorem B2307269 : Blo 1536465 2307269 := bbase (se 4 (by rfl) ⟨216306, by rfl⟩ : syracuseStep 2307269 = 432613) (by norm_num)
theorem B3282133 : Blo 1536465 3282133 := bbase (se 7 (by rfl) ⟨38462, by rfl⟩ : syracuseStep 3282133 = 76925) (by norm_num)
theorem B2307293 : Blo 1536465 2307293 := bbase (se 3 (by rfl) ⟨432617, by rfl⟩ : syracuseStep 2307293 = 865235) (by norm_num)
theorem B1946845 : Blo 1536465 1946845 := bbase (se 3 (by rfl) ⟨365033, by rfl⟩ : syracuseStep 1946845 = 730067) (by norm_num)
theorem B2307317 : Blo 1536465 2307317 := bbase (se 5 (by rfl) ⟨108155, by rfl⟩ : syracuseStep 2307317 = 216311) (by norm_num)
theorem B2594045 : Blo 1536465 2594045 := bbase (se 3 (by rfl) ⟨486383, by rfl⟩ : syracuseStep 2594045 = 972767) (by norm_num)
theorem B2307341 : Blo 1536465 2307341 := bbase (se 3 (by rfl) ⟨432626, by rfl⟩ : syracuseStep 2307341 = 865253) (by norm_num)
theorem B13137173 : Blo 1536465 13137173 := bbase (se 6 (by rfl) ⟨307902, by rfl⟩ : syracuseStep 13137173 = 615805) (by norm_num)
theorem B2307365 : Blo 1536465 2307365 := bbase (se 4 (by rfl) ⟨216315, by rfl⟩ : syracuseStep 2307365 = 432631) (by norm_num)
theorem B5190965 : Blo 1536465 5190965 := bbase (se 5 (by rfl) ⟨243326, by rfl⟩ : syracuseStep 5190965 = 486653) (by norm_num)
theorem B2307389 : Blo 1536465 2307389 := bbase (se 3 (by rfl) ⟨432635, by rfl⟩ : syracuseStep 2307389 = 865271) (by norm_num)
theorem B2307413 : Blo 1536465 2307413 := bbase (se 13 (by rfl) ⟨422, by rfl⟩ : syracuseStep 2307413 = 845) (by norm_num)
theorem B3282277 : Blo 1536465 3282277 := bbase (se 4 (by rfl) ⟨307713, by rfl⟩ : syracuseStep 3282277 = 615427) (by norm_num)
theorem B2307437 : Blo 1536465 2307437 := bbase (se 3 (by rfl) ⟨432644, by rfl⟩ : syracuseStep 2307437 = 865289) (by norm_num)
theorem B2594173 : Blo 1536465 2594173 := bbase (se 3 (by rfl) ⟨486407, by rfl⟩ : syracuseStep 2594173 = 972815) (by norm_num)
theorem B3691909 : Blo 1536465 3691909 := bbase (se 4 (by rfl) ⟨346116, by rfl⟩ : syracuseStep 3691909 = 692233) (by norm_num)
theorem B2307461 : Blo 1536465 2307461 := bbase (se 4 (by rfl) ⟨216324, by rfl⟩ : syracuseStep 2307461 = 432649) (by norm_num)
theorem B1947017 : Blo 1536465 1947017 := bbase (se 2 (by rfl) ⟨730131, by rfl⟩ : syracuseStep 1947017 = 1460263) (by norm_num)
theorem B2307485 : Blo 1536465 2307485 := bbase (se 3 (by rfl) ⟨432653, by rfl⟩ : syracuseStep 2307485 = 865307) (by norm_num)
theorem B2307509 : Blo 1536465 2307509 := bbase (se 5 (by rfl) ⟨108164, by rfl⟩ : syracuseStep 2307509 = 216329) (by norm_num)
theorem B1947073 : Blo 1536465 1947073 := bbase (se 2 (by rfl) ⟨730152, by rfl⟩ : syracuseStep 1947073 = 1460305) (by norm_num)
theorem B2307533 : Blo 1536465 2307533 := bbase (se 3 (by rfl) ⟨432662, by rfl⟩ : syracuseStep 2307533 = 865325) (by norm_num)
theorem B2594261 : Blo 1536465 2594261 := bbase (se 7 (by rfl) ⟨30401, by rfl⟩ : syracuseStep 2594261 = 60803) (by norm_num)
theorem B2307557 : Blo 1536465 2307557 := bbase (se 4 (by rfl) ⟨216333, by rfl⟩ : syracuseStep 2307557 = 432667) (by norm_num)
theorem B2307581 : Blo 1536465 2307581 := bbase (se 3 (by rfl) ⟨432671, by rfl⟩ : syracuseStep 2307581 = 865343) (by norm_num)
theorem B2307605 : Blo 1536465 2307605 := bbase (se 6 (by rfl) ⟨54084, by rfl⟩ : syracuseStep 2307605 = 108169) (by norm_num)
theorem B7386661 : Blo 1536465 7386661 := bbase (se 4 (by rfl) ⟨692499, by rfl⟩ : syracuseStep 7386661 = 1384999) (by norm_num)
theorem B2307629 : Blo 1536465 2307629 := bbase (se 3 (by rfl) ⟨432680, by rfl⟩ : syracuseStep 2307629 = 865361) (by norm_num)
theorem B6567493 : Blo 1536465 6567493 := bbase (se 4 (by rfl) ⟨615702, by rfl⟩ : syracuseStep 6567493 = 1231405) (by norm_num)
theorem B2307653 : Blo 1536465 2307653 := bbase (se 4 (by rfl) ⟨216342, by rfl⟩ : syracuseStep 2307653 = 432685) (by norm_num)
theorem B2594389 : Blo 1536465 2594389 := bbase (se 8 (by rfl) ⟨15201, by rfl⟩ : syracuseStep 2594389 = 30403) (by norm_num)
theorem B2307677 : Blo 1536465 2307677 := bbase (se 3 (by rfl) ⟨432689, by rfl⟩ : syracuseStep 2307677 = 865379) (by norm_num)
theorem B8001125 : Blo 1536465 8001125 := bbase (se 4 (by rfl) ⟨750105, by rfl⟩ : syracuseStep 8001125 = 1500211) (by norm_num)
theorem B4806245 : Blo 1536465 4806245 := bbase (se 4 (by rfl) ⟨450585, by rfl⟩ : syracuseStep 4806245 = 901171) (by norm_num)
theorem B4380277 : Blo 1536465 4380277 := bbase (se 5 (by rfl) ⟨205325, by rfl⟩ : syracuseStep 4380277 = 410651) (by norm_num)
theorem B7788149 : Blo 1536465 7788149 := bbase (se 5 (by rfl) ⟨365069, by rfl⟩ : syracuseStep 7788149 = 730139) (by norm_num)
theorem B5060245 : Blo 1536465 5060245 := bbase (se 6 (by rfl) ⟨118599, by rfl⟩ : syracuseStep 5060245 = 237199) (by norm_num)
theorem B2594477 : Blo 1536465 2594477 := bbase (se 3 (by rfl) ⟨486464, by rfl⟩ : syracuseStep 2594477 = 972929) (by norm_num)
theorem B3282653 : Blo 1536465 3282653 := bbase (se 3 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 3282653 = 1230995) (by norm_num)
theorem B5191397 : Blo 1536465 5191397 := bbase (se 4 (by rfl) ⟨486693, by rfl⟩ : syracuseStep 5191397 = 973387) (by norm_num)
theorem B2594605 : Blo 1536465 2594605 := bbase (se 3 (by rfl) ⟨486488, by rfl⟩ : syracuseStep 2594605 = 972977) (by norm_num)
theorem B7305061 : Blo 1536465 7305061 := bbase (se 4 (by rfl) ⟨684849, by rfl⟩ : syracuseStep 7305061 = 1369699) (by norm_num)
theorem B4675445 : Blo 1536465 4675445 := bbase (se 5 (by rfl) ⟨219161, by rfl⟩ : syracuseStep 4675445 = 438323) (by norm_num)
theorem B2463605 : Blo 1536465 2463605 := bbase (se 5 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 2463605 = 230963) (by norm_num)
theorem B2594693 : Blo 1536465 2594693 := bbase (se 4 (by rfl) ⟨243252, by rfl⟩ : syracuseStep 2594693 = 486505) (by norm_num)
theorem B4437925 : Blo 1536465 4437925 := bbase (se 4 (by rfl) ⟨416055, by rfl⟩ : syracuseStep 4437925 = 832111) (by norm_num)
theorem B2463701 : Blo 1536465 2463701 := bbase (se 7 (by rfl) ⟨28871, by rfl⟩ : syracuseStep 2463701 = 57743) (by norm_num)
theorem B2463733 : Blo 1536465 2463733 := bbase (se 5 (by rfl) ⟨115487, by rfl⟩ : syracuseStep 2463733 = 230975) (by norm_num)
theorem B2594821 : Blo 1536465 2594821 := bbase (se 4 (by rfl) ⟨243264, by rfl⟩ : syracuseStep 2594821 = 486529) (by norm_num)
theorem B7780373 : Blo 1536465 7780373 := bbase (se 6 (by rfl) ⟨182352, by rfl⟩ : syracuseStep 7780373 = 364705) (by norm_num)
theorem B3889205 : Blo 1536465 3889205 := bbase (se 5 (by rfl) ⟨182306, by rfl⟩ : syracuseStep 3889205 = 364613) (by norm_num)
theorem B3283021 : Blo 1536465 3283021 := bbase (se 3 (by rfl) ⟨615566, by rfl⟩ : syracuseStep 3283021 = 1231133) (by norm_num)
theorem B2078797 : Blo 1536465 2078797 := bbase (se 3 (by rfl) ⟨389774, by rfl⟩ : syracuseStep 2078797 = 779549) (by norm_num)
theorem B2594909 : Blo 1536465 2594909 := bbase (se 3 (by rfl) ⟨486545, by rfl⟩ : syracuseStep 2594909 = 973091) (by norm_num)
theorem B5191829 : Blo 1536465 5191829 := bbase (se 6 (by rfl) ⟨121683, by rfl⟩ : syracuseStep 5191829 = 243367) (by norm_num)
theorem B2595037 : Blo 1536465 2595037 := bbase (se 3 (by rfl) ⟨486569, by rfl⟩ : syracuseStep 2595037 = 973139) (by norm_num)
theorem B3889397 : Blo 1536465 3889397 := bbase (se 5 (by rfl) ⟨182315, by rfl⟩ : syracuseStep 3889397 = 364631) (by norm_num)
theorem B6568229 : Blo 1536465 6568229 := bbase (se 4 (by rfl) ⟨615771, by rfl⟩ : syracuseStep 6568229 = 1231543) (by norm_num)
theorem B2595125 : Blo 1536465 2595125 := bbase (se 5 (by rfl) ⟨121646, by rfl⟩ : syracuseStep 2595125 = 243293) (by norm_num)
theorem B2496853 : Blo 1536465 2496853 := bbase (se 10 (by rfl) ⟨3657, by rfl⟩ : syracuseStep 2496853 = 7315) (by norm_num)
theorem B2595253 : Blo 1536465 2595253 := bbase (se 5 (by rfl) ⟨121652, by rfl⟩ : syracuseStep 2595253 = 243305) (by norm_num)
theorem B1972741 : Blo 1536465 1972741 := bbase (se 4 (by rfl) ⟨184944, by rfl⟩ : syracuseStep 1972741 = 369889) (by norm_num)
theorem B2595341 : Blo 1536465 2595341 := bbase (se 3 (by rfl) ⟨486626, by rfl⟩ : syracuseStep 2595341 = 973253) (by norm_num)
theorem B5839397 : Blo 1536465 5839397 := bbase (se 4 (by rfl) ⟨547443, by rfl⟩ : syracuseStep 5839397 = 1094887) (by norm_num)
theorem B5192261 : Blo 1536465 5192261 := bbase (se 4 (by rfl) ⟨486774, by rfl⟩ : syracuseStep 5192261 = 973549) (by norm_num)
theorem B3889741 : Blo 1536465 3889741 := bbase (se 3 (by rfl) ⟨729326, by rfl⟩ : syracuseStep 3889741 = 1458653) (by norm_num)
theorem B2595469 : Blo 1536465 2595469 := bbase (se 3 (by rfl) ⟨486650, by rfl⟩ : syracuseStep 2595469 = 973301) (by norm_num)
theorem B3889853 : Blo 1536465 3889853 := bbase (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) (by norm_num)
theorem B2595557 : Blo 1536465 2595557 := bbase (se 4 (by rfl) ⟨243333, by rfl⟩ : syracuseStep 2595557 = 486667) (by norm_num)
theorem B1776361 : Blo 1536465 1776361 := bbase (se 2 (by rfl) ⟨666135, by rfl⟩ : syracuseStep 1776361 = 1332271) (by norm_num)
theorem B3693293 : Blo 1536465 3693293 := bbase (se 3 (by rfl) ⟨692492, by rfl⟩ : syracuseStep 3693293 = 1384985) (by norm_num)
theorem B2218757 : Blo 1536465 2218757 := bbase (se 4 (by rfl) ⟨208008, by rfl⟩ : syracuseStep 2218757 = 416017) (by norm_num)
theorem B5839685 : Blo 1536465 5839685 := bbase (se 4 (by rfl) ⟨547470, by rfl⟩ : syracuseStep 5839685 = 1094941) (by norm_num)
theorem B2218837 : Blo 1536465 2218837 := bbase (se 9 (by rfl) ⟨6500, by rfl⟩ : syracuseStep 2218837 = 13001) (by norm_num)
theorem B2595685 : Blo 1536465 2595685 := bbase (se 4 (by rfl) ⟨243345, by rfl⟩ : syracuseStep 2595685 = 486691) (by norm_num)
theorem B3890045 : Blo 1536465 3890045 := bbase (se 3 (by rfl) ⟨729383, by rfl⟩ : syracuseStep 3890045 = 1458767) (by norm_num)
theorem B3693485 : Blo 1536465 3693485 := bbase (se 3 (by rfl) ⟨692528, by rfl⟩ : syracuseStep 3693485 = 1385057) (by norm_num)
theorem B2595773 : Blo 1536465 2595773 := bbase (se 3 (by rfl) ⟨486707, by rfl⟩ : syracuseStep 2595773 = 973415) (by norm_num)
theorem B3505141 : Blo 1536465 3505141 := bbase (se 5 (by rfl) ⟨164303, by rfl⟩ : syracuseStep 3505141 = 328607) (by norm_num)
theorem B2595901 : Blo 1536465 2595901 := bbase (se 3 (by rfl) ⟨486731, by rfl⟩ : syracuseStep 2595901 = 973463) (by norm_num)
theorem B7011397 : Blo 1536465 7011397 := bbase (se 4 (by rfl) ⟨657318, by rfl⟩ : syracuseStep 7011397 = 1314637) (by norm_num)
theorem B1686613 : Blo 1536465 1686613 := bbase (se 8 (by rfl) ⟨9882, by rfl⟩ : syracuseStep 1686613 = 19765) (by norm_num)
theorem B1752197 : Blo 1536465 1752197 := bbase (se 4 (by rfl) ⟨164268, by rfl⟩ : syracuseStep 1752197 = 328537) (by norm_num)
theorem B2595989 : Blo 1536465 2595989 := bbase (se 6 (by rfl) ⟨60843, by rfl⟩ : syracuseStep 2595989 = 121687) (by norm_num)
theorem B3890389 : Blo 1536465 3890389 := bbase (se 7 (by rfl) ⟨45590, by rfl⟩ : syracuseStep 3890389 = 91181) (by norm_num)
theorem B8428789 : Blo 1536465 8428789 := bbase (se 5 (by rfl) ⟨395099, by rfl⟩ : syracuseStep 8428789 = 790199) (by norm_num)
theorem B2596117 : Blo 1536465 2596117 := bbase (se 6 (by rfl) ⟨60846, by rfl⟩ : syracuseStep 2596117 = 121693) (by norm_num)
theorem B7781669 : Blo 1536465 7781669 := bbase (se 4 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 7781669 = 1459063) (by norm_num)
theorem B3890501 : Blo 1536465 3890501 := bbase (se 4 (by rfl) ⟨364734, by rfl⟩ : syracuseStep 3890501 = 729469) (by norm_num)
theorem B5913973 : Blo 1536465 5913973 := bbase (se 5 (by rfl) ⟨277217, by rfl⟩ : syracuseStep 5913973 = 554435) (by norm_num)
theorem B2956709 : Blo 1536465 2956709 := bbase (se 4 (by rfl) ⟨277191, by rfl⟩ : syracuseStep 2956709 = 554383) (by norm_num)
theorem B3890693 : Blo 1536465 3890693 := bbase (se 4 (by rfl) ⟨364752, by rfl⟩ : syracuseStep 3890693 = 729505) (by norm_num)
theorem B3284525 : Blo 1536465 3284525 := bbase (se 3 (by rfl) ⟨615848, by rfl⟩ : syracuseStep 3284525 = 1231697) (by norm_num)
theorem B8420917 : Blo 1536465 8420917 := bbase (se 5 (by rfl) ⟨394730, by rfl⟩ : syracuseStep 8420917 = 789461) (by norm_num)
theorem B7593589 : Blo 1536465 7593589 := bbase (se 5 (by rfl) ⟨355949, by rfl⟩ : syracuseStep 7593589 = 711899) (by norm_num)
theorem B19693205 : Blo 1536465 19693205 := bbase (se 6 (by rfl) ⟨461559, by rfl⟩ : syracuseStep 19693205 = 923119) (by norm_num)
theorem B3694253 : Blo 1536465 3694253 := bbase (se 3 (by rfl) ⟨692672, by rfl⟩ : syracuseStep 3694253 = 1385345) (by norm_num)
theorem B3284669 : Blo 1536465 3284669 := bbase (se 3 (by rfl) ⟨615875, by rfl⟩ : syracuseStep 3284669 = 1231751) (by norm_num)
theorem B1752781 : Blo 1536465 1752781 := bbase (se 3 (by rfl) ⟨328646, by rfl⟩ : syracuseStep 1752781 = 657293) (by norm_num)
theorem B6233861 : Blo 1536465 6233861 := bbase (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) (by norm_num)
theorem B5537605 : Blo 1536465 5537605 := bbase (se 4 (by rfl) ⟨519150, by rfl⟩ : syracuseStep 5537605 = 1038301) (by norm_num)
theorem B33259349 : Blo 1536465 33259349 := bbase (se 9 (by rfl) ⟨97439, by rfl⟩ : syracuseStep 33259349 = 194879) (by norm_num)
theorem B3891037 : Blo 1536465 3891037 := bbase (se 3 (by rfl) ⟨729569, by rfl⟩ : syracuseStep 3891037 = 1459139) (by norm_num)
theorem B3891149 : Blo 1536465 3891149 := bbase (se 3 (by rfl) ⟨729590, by rfl⟩ : syracuseStep 3891149 = 1459181) (by norm_num)
theorem B5840869 : Blo 1536465 5840869 := bbase (se 4 (by rfl) ⟨547581, by rfl⟩ : syracuseStep 5840869 = 1095163) (by norm_num)
theorem B1728643 : Blo 1536465 1728643 := bstep (se 1 (by rfl) ⟨1296482, by rfl⟩ : syracuseStep 1728643 = 2592965) B2592965
theorem B3457169 : Blo 1536465 3457169 := bstep (se 2 (by rfl) ⟨1296438, by rfl⟩ : syracuseStep 3457169 = 2592877) B2592877
theorem B3457187 : Blo 1536465 3457187 := bstep (se 1 (by rfl) ⟨2592890, by rfl⟩ : syracuseStep 3457187 = 5185781) B5185781
theorem B2220257 : Blo 1536465 2220257 := bstep (se 2 (by rfl) ⟨832596, by rfl⟩ : syracuseStep 2220257 = 1665193) B1665193
theorem B7782641 : Blo 1536465 7782641 := bstep (se 2 (by rfl) ⟨2918490, by rfl⟩ : syracuseStep 7782641 = 5836981) B5836981
theorem B4153613 : Blo 1536465 4153613 := bstep (se 3 (by rfl) ⟨778802, by rfl⟩ : syracuseStep 4153613 = 1557605) B1557605
theorem B3891473 : Blo 1536465 3891473 := bstep (se 2 (by rfl) ⟨1459302, by rfl⟩ : syracuseStep 3891473 = 2918605) B2918605
theorem B1728787 : Blo 1536465 1728787 := bstep (se 1 (by rfl) ⟨1296590, by rfl⟩ : syracuseStep 1728787 = 2593181) B2593181
theorem B3891523 : Blo 1536465 3891523 := bstep (se 1 (by rfl) ⟨2918642, by rfl⟩ : syracuseStep 3891523 = 5837285) B5837285
theorem B1728931 : Blo 1536465 1728931 := bstep (se 1 (by rfl) ⟨1296698, by rfl⟩ : syracuseStep 1728931 = 2593397) B2593397
theorem B3457457 : Blo 1536465 3457457 := bstep (se 2 (by rfl) ⟨1296546, by rfl⟩ : syracuseStep 3457457 = 2593093) B2593093
theorem B3457475 : Blo 1536465 3457475 := bstep (se 1 (by rfl) ⟨2593106, by rfl⟩ : syracuseStep 3457475 = 5186213) B5186213
theorem B5185997 : Blo 1536465 5185997 := bstep (se 3 (by rfl) ⟨972374, by rfl⟩ : syracuseStep 5185997 = 1944749) B1944749
theorem B3891665 : Blo 1536465 3891665 := bstep (se 2 (by rfl) ⟨1459374, by rfl⟩ : syracuseStep 3891665 = 2918749) B2918749
theorem B6570467 : Blo 1536465 6570467 := bstep (se 1 (by rfl) ⟨4927850, by rfl⟩ : syracuseStep 6570467 = 9855701) B9855701
theorem B5186051 : Blo 1536465 5186051 := bstep (se 1 (by rfl) ⟨3889538, by rfl⟩ : syracuseStep 5186051 = 7779077) B7779077
theorem B1729075 : Blo 1536465 1729075 := bstep (se 1 (by rfl) ⟨1296806, by rfl⟩ : syracuseStep 1729075 = 2593613) B2593613
theorem B2630321 : Blo 1536465 2630321 := bstep (se 2 (by rfl) ⟨986370, by rfl⟩ : syracuseStep 2630321 = 1972741) B1972741
theorem B1729219 : Blo 1536465 1729219 := bstep (se 1 (by rfl) ⟨1296914, by rfl⟩ : syracuseStep 1729219 = 2593829) B2593829
theorem B4440781 : Blo 1536465 4440781 := bstep (se 3 (by rfl) ⟨832646, by rfl⟩ : syracuseStep 4440781 = 1665293) B1665293
theorem B3457745 : Blo 1536465 3457745 := bstep (se 2 (by rfl) ⟨1296654, by rfl⟩ : syracuseStep 3457745 = 2593309) B2593309
theorem B3457763 : Blo 1536465 3457763 := bstep (se 1 (by rfl) ⟨2593322, by rfl⟩ : syracuseStep 3457763 = 5186645) B5186645
theorem B5186321 : Blo 1536465 5186321 := bstep (se 2 (by rfl) ⟨1944870, by rfl⟩ : syracuseStep 5186321 = 3889741) B3889741
theorem B1729363 : Blo 1536465 1729363 := bstep (se 1 (by rfl) ⟨1297022, by rfl⟩ : syracuseStep 1729363 = 2594045) B2594045
theorem B9847651 : Blo 1536465 9847651 := bstep (se 1 (by rfl) ⟨7385738, by rfl⟩ : syracuseStep 9847651 = 14771477) B14771477
theorem B8758115 : Blo 1536465 8758115 := bstep (se 1 (by rfl) ⟨6568586, by rfl⟩ : syracuseStep 8758115 = 13137173) B13137173
theorem B2188225 : Blo 1536465 2188225 := bstep (se 2 (by rfl) ⟨820584, by rfl⟩ : syracuseStep 2188225 = 1641169) B1641169
theorem B2368481 : Blo 1536465 2368481 := bstep (se 2 (by rfl) ⟨888180, by rfl⟩ : syracuseStep 2368481 = 1776361) B1776361
theorem B1729507 : Blo 1536465 1729507 := bstep (se 1 (by rfl) ⟨1297130, by rfl⟩ : syracuseStep 1729507 = 2594261) B2594261
theorem B3458033 : Blo 1536465 3458033 := bstep (se 2 (by rfl) ⟨1296762, by rfl⟩ : syracuseStep 3458033 = 2593525) B2593525
theorem B3507185 : Blo 1536465 3507185 := bstep (se 2 (by rfl) ⟨1315194, by rfl⟩ : syracuseStep 3507185 = 2630389) B2630389
theorem B3458051 : Blo 1536465 3458051 := bstep (se 1 (by rfl) ⟨2593538, by rfl⟩ : syracuseStep 3458051 = 5187077) B5187077
theorem B5334083 : Blo 1536465 5334083 := bstep (se 1 (by rfl) ⟨4000562, by rfl⟩ : syracuseStep 5334083 = 8001125) B8001125
theorem B3204163 : Blo 1536465 3204163 := bstep (se 1 (by rfl) ⟨2403122, by rfl⟩ : syracuseStep 3204163 = 4806245) B4806245
theorem B2958449 : Blo 1536465 2958449 := bstep (se 2 (by rfl) ⟨1109418, by rfl⟩ : syracuseStep 2958449 = 2218837) B2218837
theorem B1729651 : Blo 1536465 1729651 := bstep (se 1 (by rfl) ⟨1297238, by rfl⟩ : syracuseStep 1729651 = 2594477) B2594477
theorem B3998897 : Blo 1536465 3998897 := bstep (se 2 (by rfl) ⟨1499586, by rfl⟩ : syracuseStep 3998897 = 2999173) B2999173
theorem B9856241 : Blo 1536465 9856241 := bstep (se 2 (by rfl) ⟨3696090, by rfl⟩ : syracuseStep 9856241 = 7392181) B7392181
theorem B1729795 : Blo 1536465 1729795 := bstep (se 1 (by rfl) ⟨1297346, by rfl⟩ : syracuseStep 1729795 = 2594693) B2594693
theorem B3458321 : Blo 1536465 3458321 := bstep (se 2 (by rfl) ⟨1296870, by rfl⟩ : syracuseStep 3458321 = 2593741) B2593741
theorem B2188561 : Blo 1536465 2188561 := bstep (se 2 (by rfl) ⟨820710, by rfl⟩ : syracuseStep 2188561 = 1641421) B1641421
theorem B3458339 : Blo 1536465 3458339 := bstep (se 1 (by rfl) ⟨2593754, by rfl⟩ : syracuseStep 3458339 = 5187509) B5187509
theorem B5186861 : Blo 1536465 5186861 := bstep (se 3 (by rfl) ⟨972536, by rfl⟩ : syracuseStep 5186861 = 1945073) B1945073
theorem B5186915 : Blo 1536465 5186915 := bstep (se 1 (by rfl) ⟨3890186, by rfl⟩ : syracuseStep 5186915 = 7780373) B7780373
theorem B2917777 : Blo 1536465 2917777 := bstep (se 2 (by rfl) ⟨1094166, by rfl⟩ : syracuseStep 2917777 = 2188333) B2188333
theorem B1729939 : Blo 1536465 1729939 := bstep (se 1 (by rfl) ⟨1297454, by rfl⟩ : syracuseStep 1729939 = 2594909) B2594909
theorem B9348529 : Blo 1536465 9348529 := bstep (se 2 (by rfl) ⟨3505698, by rfl⟩ : syracuseStep 9348529 = 7011397) B7011397
theorem B3892657 : Blo 1536465 3892657 := bstep (se 2 (by rfl) ⟨1459746, by rfl⟩ : syracuseStep 3892657 = 2919493) B2919493
theorem B13305329 : Blo 1536465 13305329 := bstep (se 2 (by rfl) ⟨4989498, by rfl⟩ : syracuseStep 13305329 = 9978997) B9978997
theorem B15992333 : Blo 1536465 15992333 := bstep (se 3 (by rfl) ⟨2998562, by rfl⟩ : syracuseStep 15992333 = 5997125) B5997125
theorem B1730083 : Blo 1536465 1730083 := bstep (se 1 (by rfl) ⟨1297562, by rfl⟩ : syracuseStep 1730083 = 2595125) B2595125
theorem B2917937 : Blo 1536465 2917937 := bstep (se 2 (by rfl) ⟨1094226, by rfl⟩ : syracuseStep 2917937 = 2188453) B2188453
theorem B3458609 : Blo 1536465 3458609 := bstep (se 2 (by rfl) ⟨1296978, by rfl⟩ : syracuseStep 3458609 = 2593957) B2593957
theorem B3458627 : Blo 1536465 3458627 := bstep (se 1 (by rfl) ⟨2593970, by rfl⟩ : syracuseStep 3458627 = 5187941) B5187941
theorem B5834339 : Blo 1536465 5834339 := bstep (se 1 (by rfl) ⟨4375754, by rfl⟩ : syracuseStep 5834339 = 8751509) B8751509
theorem B4376177 : Blo 1536465 4376177 := bstep (se 2 (by rfl) ⟨1641066, by rfl⟩ : syracuseStep 4376177 = 3282133) B3282133
theorem B5187185 : Blo 1536465 5187185 := bstep (se 2 (by rfl) ⟨1945194, by rfl⟩ : syracuseStep 5187185 = 3890389) B3890389
theorem B7784099 : Blo 1536465 7784099 := bstep (se 1 (by rfl) ⟨5838074, by rfl⟩ : syracuseStep 7784099 = 11676149) B11676149
theorem B1730227 : Blo 1536465 1730227 := bstep (se 1 (by rfl) ⟨1297670, by rfl⟩ : syracuseStep 1730227 = 2595341) B2595341
theorem B3892931 : Blo 1536465 3892931 := bstep (se 1 (by rfl) ⟨2919698, by rfl⟩ : syracuseStep 3892931 = 5839397) B5839397
theorem B4376369 : Blo 1536465 4376369 := bstep (se 2 (by rfl) ⟨1641138, by rfl⟩ : syracuseStep 4376369 = 3282277) B3282277
theorem B22153013 : Blo 1536465 22153013 := bstep (se 5 (by rfl) ⟨1038422, by rfl⟩ : syracuseStep 22153013 = 2076845) B2076845
theorem B39405365 : Blo 1536465 39405365 := bstep (se 5 (by rfl) ⟨1847126, by rfl⟩ : syracuseStep 39405365 = 3694253) B3694253
theorem B1730371 : Blo 1536465 1730371 := bstep (se 1 (by rfl) ⟨1297778, by rfl⟩ : syracuseStep 1730371 = 2595557) B2595557
theorem B4925261 : Blo 1536465 4925261 := bstep (se 3 (by rfl) ⟨923486, by rfl⟩ : syracuseStep 4925261 = 1846973) B1846973
theorem B8759117 : Blo 1536465 8759117 := bstep (se 3 (by rfl) ⟨1642334, by rfl⟩ : syracuseStep 8759117 = 3284669) B3284669
theorem B3458897 : Blo 1536465 3458897 := bstep (se 2 (by rfl) ⟨1297086, by rfl⟩ : syracuseStep 3458897 = 2594173) B2594173
theorem B2189153 : Blo 1536465 2189153 := bstep (se 2 (by rfl) ⟨820932, by rfl⟩ : syracuseStep 2189153 = 1641865) B1641865
theorem B3458915 : Blo 1536465 3458915 := bstep (se 1 (by rfl) ⟨2594186, by rfl⟩ : syracuseStep 3458915 = 5188373) B5188373
theorem B3893123 : Blo 1536465 3893123 := bstep (se 1 (by rfl) ⟨2919842, by rfl⟩ : syracuseStep 3893123 = 5839685) B5839685
theorem B2918339 : Blo 1536465 2918339 := bstep (se 1 (by rfl) ⟨2188754, by rfl⟩ : syracuseStep 2918339 = 4377509) B4377509
theorem B1730515 : Blo 1536465 1730515 := bstep (se 1 (by rfl) ⟨1297886, by rfl⟩ : syracuseStep 1730515 = 2595773) B2595773
theorem B11233265 : Blo 1536465 11233265 := bstep (se 2 (by rfl) ⟨4212474, by rfl⟩ : syracuseStep 11233265 = 8424949) B8424949
theorem B5916685 : Blo 1536465 5916685 := bstep (se 3 (by rfl) ⟨1109378, by rfl⟩ : syracuseStep 5916685 = 2218757) B2218757
theorem B16623629 : Blo 1536465 16623629 := bstep (se 3 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 16623629 = 6233861) B6233861
theorem B9848881 : Blo 1536465 9848881 := bstep (se 2 (by rfl) ⟨3693330, by rfl⟩ : syracuseStep 9848881 = 7386661) B7386661
theorem B1730659 : Blo 1536465 1730659 := bstep (se 1 (by rfl) ⟨1297994, by rfl⟩ : syracuseStep 1730659 = 2595989) B2595989
theorem B3459185 : Blo 1536465 3459185 := bstep (se 2 (by rfl) ⟨1297194, by rfl⟩ : syracuseStep 3459185 = 2594389) B2594389
theorem B1558643 : Blo 1536465 1558643 := bstep (se 1 (by rfl) ⟨1168982, by rfl⟩ : syracuseStep 1558643 = 2337965) B2337965
theorem B3459203 : Blo 1536465 3459203 := bstep (se 1 (by rfl) ⟨2594402, by rfl⟩ : syracuseStep 3459203 = 5188805) B5188805
theorem B14772365 : Blo 1536465 14772365 := bstep (se 3 (by rfl) ⟨2769818, by rfl⟩ : syracuseStep 14772365 = 5539637) B5539637
theorem B5187725 : Blo 1536465 5187725 := bstep (se 3 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 5187725 = 1945397) B1945397
theorem B5187779 : Blo 1536465 5187779 := bstep (se 1 (by rfl) ⟨3890834, by rfl⟩ : syracuseStep 5187779 = 7781669) B7781669
theorem B23668933 : Blo 1536465 23668933 := bstep (se 4 (by rfl) ⟨2218962, by rfl⟩ : syracuseStep 23668933 = 4437925) B4437925
theorem B2337041 : Blo 1536465 2337041 := bstep (se 2 (by rfl) ⟨876390, by rfl⟩ : syracuseStep 2337041 = 1752781) B1752781
theorem B2189683 : Blo 1536465 2189683 := bstep (se 1 (by rfl) ⟨1642262, by rfl⟩ : syracuseStep 2189683 = 3284525) B3284525
theorem B3459473 : Blo 1536465 3459473 := bstep (se 2 (by rfl) ⟨1297302, by rfl⟩ : syracuseStep 3459473 = 2594605) B2594605
theorem B3459491 : Blo 1536465 3459491 := bstep (se 1 (by rfl) ⟨2594618, by rfl⟩ : syracuseStep 3459491 = 5189237) B5189237
theorem B7383473 : Blo 1536465 7383473 := bstep (se 2 (by rfl) ⟨2768802, by rfl⟩ : syracuseStep 7383473 = 5537605) B5537605
theorem B7784909 : Blo 1536465 7784909 := bstep (se 3 (by rfl) ⟨1459670, by rfl⟩ : syracuseStep 7784909 = 2919341) B2919341
theorem B5188049 : Blo 1536465 5188049 := bstep (se 2 (by rfl) ⟨1945518, by rfl⟩ : syracuseStep 5188049 = 3891037) B3891037
theorem B5835341 : Blo 1536465 5835341 := bstep (se 3 (by rfl) ⟨1094126, by rfl⟩ : syracuseStep 5835341 = 2188253) B2188253
theorem B3459761 : Blo 1536465 3459761 := bstep (se 2 (by rfl) ⟨1297410, by rfl⟩ : syracuseStep 3459761 = 2594821) B2594821
theorem B2304707 : Blo 1536465 2304707 := bstep (se 1 (by rfl) ⟨1728530, by rfl⟩ : syracuseStep 2304707 = 3457061) B3457061
theorem B3459779 : Blo 1536465 3459779 := bstep (se 1 (by rfl) ⟨2594834, by rfl⟩ : syracuseStep 3459779 = 5189669) B5189669
theorem B2190019 : Blo 1536465 2190019 := bstep (se 1 (by rfl) ⟨1642514, by rfl⟩ : syracuseStep 2190019 = 3285029) B3285029
theorem B3115729 : Blo 1536465 3115729 := bstep (se 2 (by rfl) ⟨1168398, by rfl⟩ : syracuseStep 3115729 = 2336797) B2336797
theorem B2304737 : Blo 1536465 2304737 := bstep (se 2 (by rfl) ⟨864276, by rfl⟩ : syracuseStep 2304737 = 1728553) B1728553
theorem B2304755 : Blo 1536465 2304755 := bstep (se 1 (by rfl) ⟨1728566, by rfl⟩ : syracuseStep 2304755 = 3457133) B3457133
theorem B2304785 : Blo 1536465 2304785 := bstep (se 2 (by rfl) ⟨864294, by rfl⟩ : syracuseStep 2304785 = 1728589) B1728589
theorem B4377361 : Blo 1536465 4377361 := bstep (se 2 (by rfl) ⟨1641510, by rfl⟩ : syracuseStep 4377361 = 3283021) B3283021
theorem B2771729 : Blo 1536465 2771729 := bstep (se 2 (by rfl) ⟨1039398, by rfl⟩ : syracuseStep 2771729 = 2078797) B2078797
theorem B2304803 : Blo 1536465 2304803 := bstep (se 1 (by rfl) ⟨1728602, by rfl⟩ : syracuseStep 2304803 = 3457205) B3457205
theorem B3894065 : Blo 1536465 3894065 := bstep (se 2 (by rfl) ⟨1460274, by rfl⟩ : syracuseStep 3894065 = 2920549) B2920549
theorem B2304833 : Blo 1536465 2304833 := bstep (se 2 (by rfl) ⟨864312, by rfl⟩ : syracuseStep 2304833 = 1728625) B1728625
theorem B2919235 : Blo 1536465 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B2304851 : Blo 1536465 2304851 := bstep (se 1 (by rfl) ⟨1728638, by rfl⟩ : syracuseStep 2304851 = 3457277) B3457277
theorem B1846099 : Blo 1536465 1846099 := bstep (se 1 (by rfl) ⟨1384574, by rfl⟩ : syracuseStep 1846099 = 2769149) B2769149
theorem B3894115 : Blo 1536465 3894115 := bstep (se 1 (by rfl) ⟨2920586, by rfl⟩ : syracuseStep 3894115 = 5841173) B5841173
theorem B2304881 : Blo 1536465 2304881 := bstep (se 2 (by rfl) ⟨864330, by rfl⟩ : syracuseStep 2304881 = 1728661) B1728661
theorem B3246961 : Blo 1536465 3246961 := bstep (se 2 (by rfl) ⟨1217610, by rfl⟩ : syracuseStep 3246961 = 2435221) B2435221
theorem B2304899 : Blo 1536465 2304899 := bstep (se 1 (by rfl) ⟨1728674, by rfl⟩ : syracuseStep 2304899 = 3457349) B3457349
theorem B1846147 : Blo 1536465 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B2304929 : Blo 1536465 2304929 := bstep (se 2 (by rfl) ⟨864348, by rfl⟩ : syracuseStep 2304929 = 1728697) B1728697
theorem B2304947 : Blo 1536465 2304947 := bstep (se 1 (by rfl) ⟨1728710, by rfl⟩ : syracuseStep 2304947 = 3457421) B3457421
theorem B1641395 : Blo 1536465 1641395 := bstep (se 1 (by rfl) ⟨1231046, by rfl⟩ : syracuseStep 1641395 = 2462093) B2462093
theorem B2304977 : Blo 1536465 2304977 := bstep (se 2 (by rfl) ⟨864366, by rfl⟩ : syracuseStep 2304977 = 1728733) B1728733
theorem B3460049 : Blo 1536465 3460049 := bstep (se 2 (by rfl) ⟨1297518, by rfl⟩ : syracuseStep 3460049 = 2595037) B2595037
theorem B2304995 : Blo 1536465 2304995 := bstep (se 1 (by rfl) ⟨1728746, by rfl⟩ : syracuseStep 2304995 = 3457493) B3457493
theorem B1846243 : Blo 1536465 1846243 := bstep (se 1 (by rfl) ⟨1384682, by rfl⟩ : syracuseStep 1846243 = 2769365) B2769365
theorem B2919395 : Blo 1536465 2919395 := bstep (se 1 (by rfl) ⟨2189546, by rfl⟩ : syracuseStep 2919395 = 4379093) B4379093
theorem B3460067 : Blo 1536465 3460067 := bstep (se 1 (by rfl) ⟨2595050, by rfl⟩ : syracuseStep 3460067 = 5190101) B5190101
theorem B5188589 : Blo 1536465 5188589 := bstep (se 3 (by rfl) ⟨972860, by rfl⟩ : syracuseStep 5188589 = 1945721) B1945721
theorem B2305025 : Blo 1536465 2305025 := bstep (se 2 (by rfl) ⟨864384, by rfl⟩ : syracuseStep 2305025 = 1728769) B1728769
theorem B2305043 : Blo 1536465 2305043 := bstep (se 1 (by rfl) ⟨1728782, by rfl⟩ : syracuseStep 2305043 = 3457565) B3457565
theorem B4377635 : Blo 1536465 4377635 := bstep (se 1 (by rfl) ⟨3283226, by rfl⟩ : syracuseStep 4377635 = 6566453) B6566453
theorem B5188643 : Blo 1536465 5188643 := bstep (se 1 (by rfl) ⟨3891482, by rfl⟩ : syracuseStep 5188643 = 7782965) B7782965
theorem B2305073 : Blo 1536465 2305073 := bstep (se 2 (by rfl) ⟨864402, by rfl⟩ : syracuseStep 2305073 = 1728805) B1728805
theorem B1944643 : Blo 1536465 1944643 := bstep (se 1 (by rfl) ⟨1458482, by rfl⟩ : syracuseStep 1944643 = 2916965) B2916965
theorem B2305091 : Blo 1536465 2305091 := bstep (se 1 (by rfl) ⟨1728818, by rfl⟩ : syracuseStep 2305091 = 3457637) B3457637
theorem B2305121 : Blo 1536465 2305121 := bstep (se 2 (by rfl) ⟨864420, by rfl⟩ : syracuseStep 2305121 = 1728841) B1728841
theorem B6237283 : Blo 1536465 6237283 := bstep (se 1 (by rfl) ⟨4677962, by rfl⟩ : syracuseStep 6237283 = 9355925) B9355925
theorem B3329137 : Blo 1536465 3329137 := bstep (se 2 (by rfl) ⟨1248426, by rfl⟩ : syracuseStep 3329137 = 2496853) B2496853
theorem B2305139 : Blo 1536465 2305139 := bstep (se 1 (by rfl) ⟨1728854, by rfl⟩ : syracuseStep 2305139 = 3457709) B3457709
theorem B2305169 : Blo 1536465 2305169 := bstep (se 2 (by rfl) ⟨864438, by rfl⟩ : syracuseStep 2305169 = 1728877) B1728877
theorem B1944739 : Blo 1536465 1944739 := bstep (se 1 (by rfl) ⟨1458554, by rfl⟩ : syracuseStep 1944739 = 2917109) B2917109
theorem B2305187 : Blo 1536465 2305187 := bstep (se 1 (by rfl) ⟨1728890, by rfl⟩ : syracuseStep 2305187 = 3457781) B3457781
theorem B2305217 : Blo 1536465 2305217 := bstep (se 2 (by rfl) ⟨864456, by rfl⟩ : syracuseStep 2305217 = 1728913) B1728913
theorem B2305235 : Blo 1536465 2305235 := bstep (se 1 (by rfl) ⟨1728926, by rfl⟩ : syracuseStep 2305235 = 3457853) B3457853
theorem B4377827 : Blo 1536465 4377827 := bstep (se 1 (by rfl) ⟨3283370, by rfl⟩ : syracuseStep 4377827 = 6566741) B6566741
theorem B2305265 : Blo 1536465 2305265 := bstep (se 2 (by rfl) ⟨864474, by rfl⟩ : syracuseStep 2305265 = 1728949) B1728949
theorem B3460337 : Blo 1536465 3460337 := bstep (se 2 (by rfl) ⟨1297626, by rfl⟩ : syracuseStep 3460337 = 2595253) B2595253
theorem B2305283 : Blo 1536465 2305283 := bstep (se 1 (by rfl) ⟨1728962, by rfl⟩ : syracuseStep 2305283 = 3457925) B3457925
theorem B3460355 : Blo 1536465 3460355 := bstep (se 1 (by rfl) ⟨2595266, by rfl⟩ : syracuseStep 3460355 = 5190533) B5190533
theorem B2305313 : Blo 1536465 2305313 := bstep (se 2 (by rfl) ⟨864492, by rfl⟩ : syracuseStep 2305313 = 1728985) B1728985
theorem B7384355 : Blo 1536465 7384355 := bstep (se 1 (by rfl) ⟨5538266, by rfl⟩ : syracuseStep 7384355 = 11076533) B11076533
theorem B5188913 : Blo 1536465 5188913 := bstep (se 2 (by rfl) ⟨1945842, by rfl⟩ : syracuseStep 5188913 = 3891685) B3891685
theorem B2305331 : Blo 1536465 2305331 := bstep (se 1 (by rfl) ⟨1728998, by rfl⟩ : syracuseStep 2305331 = 3457997) B3457997
theorem B2305361 : Blo 1536465 2305361 := bstep (se 2 (by rfl) ⟨864510, by rfl⟩ : syracuseStep 2305361 = 1729021) B1729021
theorem B2305379 : Blo 1536465 2305379 := bstep (se 1 (by rfl) ⟨1729034, by rfl⟩ : syracuseStep 2305379 = 3458069) B3458069
theorem B2305409 : Blo 1536465 2305409 := bstep (se 2 (by rfl) ⟨864528, by rfl⟩ : syracuseStep 2305409 = 1729057) B1729057
theorem B4926851 : Blo 1536465 4926851 := bstep (se 1 (by rfl) ⟨3695138, by rfl⟩ : syracuseStep 4926851 = 7390277) B7390277
theorem B2305427 : Blo 1536465 2305427 := bstep (se 1 (by rfl) ⟨1729070, by rfl⟩ : syracuseStep 2305427 = 3458141) B3458141
theorem B2305457 : Blo 1536465 2305457 := bstep (se 2 (by rfl) ⟨864546, by rfl⟩ : syracuseStep 2305457 = 1729093) B1729093
theorem B2305475 : Blo 1536465 2305475 := bstep (se 1 (by rfl) ⟨1729106, by rfl⟩ : syracuseStep 2305475 = 3458213) B3458213
theorem B2305505 : Blo 1536465 2305505 := bstep (se 2 (by rfl) ⟨864564, by rfl⟩ : syracuseStep 2305505 = 1729129) B1729129
theorem B2305523 : Blo 1536465 2305523 := bstep (se 1 (by rfl) ⟨1729142, by rfl⟩ : syracuseStep 2305523 = 3458285) B3458285
theorem B2305553 : Blo 1536465 2305553 := bstep (se 2 (by rfl) ⟨864582, by rfl⟩ : syracuseStep 2305553 = 1729165) B1729165
theorem B3460625 : Blo 1536465 3460625 := bstep (se 2 (by rfl) ⟨1297734, by rfl⟩ : syracuseStep 3460625 = 2595469) B2595469
theorem B2305571 : Blo 1536465 2305571 := bstep (se 1 (by rfl) ⟨1729178, by rfl⟩ : syracuseStep 2305571 = 3458357) B3458357
theorem B1846819 : Blo 1536465 1846819 := bstep (se 1 (by rfl) ⟨1385114, by rfl⟩ : syracuseStep 1846819 = 2770229) B2770229
theorem B3460643 : Blo 1536465 3460643 := bstep (se 1 (by rfl) ⟨2595482, by rfl⟩ : syracuseStep 3460643 = 5190965) B5190965
theorem B2305601 : Blo 1536465 2305601 := bstep (se 2 (by rfl) ⟨864600, by rfl⟩ : syracuseStep 2305601 = 1729201) B1729201
theorem B4157009 : Blo 1536465 4157009 := bstep (se 2 (by rfl) ⟨1558878, by rfl⟩ : syracuseStep 4157009 = 3117757) B3117757
theorem B2305619 : Blo 1536465 2305619 := bstep (se 1 (by rfl) ⟨1729214, by rfl⟩ : syracuseStep 2305619 = 3458429) B3458429
theorem B2305649 : Blo 1536465 2305649 := bstep (se 2 (by rfl) ⟨864618, by rfl⟩ : syracuseStep 2305649 = 1729237) B1729237
theorem B2305667 : Blo 1536465 2305667 := bstep (se 1 (by rfl) ⟨1729250, by rfl⟩ : syracuseStep 2305667 = 3458501) B3458501
theorem B1945235 : Blo 1536465 1945235 := bstep (se 1 (by rfl) ⟨1458926, by rfl⟩ : syracuseStep 1945235 = 2917853) B2917853
theorem B2305697 : Blo 1536465 2305697 := bstep (se 2 (by rfl) ⟨864636, by rfl⟩ : syracuseStep 2305697 = 1729273) B1729273
theorem B2305715 : Blo 1536465 2305715 := bstep (se 1 (by rfl) ⟨1729286, by rfl⟩ : syracuseStep 2305715 = 3458573) B3458573
theorem B2305745 : Blo 1536465 2305745 := bstep (se 2 (by rfl) ⟨864654, by rfl⟩ : syracuseStep 2305745 = 1729309) B1729309
theorem B2305763 : Blo 1536465 2305763 := bstep (se 1 (by rfl) ⟨1729322, by rfl⟩ : syracuseStep 2305763 = 3458645) B3458645
theorem B2305793 : Blo 1536465 2305793 := bstep (se 2 (by rfl) ⟨864672, by rfl⟩ : syracuseStep 2305793 = 1729345) B1729345
theorem B7884557 : Blo 1536465 7884557 := bstep (se 3 (by rfl) ⟨1478354, by rfl⟩ : syracuseStep 7884557 = 2956709) B2956709
theorem B2305811 : Blo 1536465 2305811 := bstep (se 1 (by rfl) ⟨1729358, by rfl⟩ : syracuseStep 2305811 = 3458717) B3458717
theorem B2305841 : Blo 1536465 2305841 := bstep (se 2 (by rfl) ⟨864690, by rfl⟩ : syracuseStep 2305841 = 1729381) B1729381
theorem B3460913 : Blo 1536465 3460913 := bstep (se 2 (by rfl) ⟨1297842, by rfl⟩ : syracuseStep 3460913 = 2595685) B2595685
theorem B2305859 : Blo 1536465 2305859 := bstep (se 1 (by rfl) ⟨1729394, by rfl⟩ : syracuseStep 2305859 = 3458789) B3458789
theorem B3460931 : Blo 1536465 3460931 := bstep (se 1 (by rfl) ⟨2595698, by rfl⟩ : syracuseStep 3460931 = 5191397) B5191397
theorem B5189453 : Blo 1536465 5189453 := bstep (se 3 (by rfl) ⟨973022, by rfl⟩ : syracuseStep 5189453 = 1946045) B1946045
theorem B2305889 : Blo 1536465 2305889 := bstep (se 2 (by rfl) ⟨864708, by rfl⟩ : syracuseStep 2305889 = 1729417) B1729417
theorem B2305907 : Blo 1536465 2305907 := bstep (se 1 (by rfl) ⟨1729430, by rfl⟩ : syracuseStep 2305907 = 3458861) B3458861
theorem B5189507 : Blo 1536465 5189507 := bstep (se 1 (by rfl) ⟨3892130, by rfl⟩ : syracuseStep 5189507 = 7784261) B7784261
theorem B6229901 : Blo 1536465 6229901 := bstep (se 3 (by rfl) ⟨1168106, by rfl⟩ : syracuseStep 6229901 = 2336213) B2336213
theorem B2305937 : Blo 1536465 2305937 := bstep (se 2 (by rfl) ⟨864726, by rfl⟩ : syracuseStep 2305937 = 1729453) B1729453
theorem B2305955 : Blo 1536465 2305955 := bstep (se 1 (by rfl) ⟨1729466, by rfl⟩ : syracuseStep 2305955 = 3458933) B3458933
theorem B3116963 : Blo 1536465 3116963 := bstep (se 1 (by rfl) ⟨2337722, by rfl⟩ : syracuseStep 3116963 = 4675445) B4675445
theorem B1642403 : Blo 1536465 1642403 := bstep (se 1 (by rfl) ⟨1231802, by rfl⟩ : syracuseStep 1642403 = 2463605) B2463605
theorem B2305985 : Blo 1536465 2305985 := bstep (se 2 (by rfl) ⟨864744, by rfl⟩ : syracuseStep 2305985 = 1729489) B1729489
theorem B2306003 : Blo 1536465 2306003 := bstep (se 1 (by rfl) ⟨1729502, by rfl⟩ : syracuseStep 2306003 = 3459005) B3459005
theorem B4673521 : Blo 1536465 4673521 := bstep (se 2 (by rfl) ⟨1752570, by rfl⟩ : syracuseStep 4673521 = 3505141) B3505141
theorem B2306033 : Blo 1536465 2306033 := bstep (se 2 (by rfl) ⟨864762, by rfl⟩ : syracuseStep 2306033 = 1729525) B1729525
theorem B2076673 : Blo 1536465 2076673 := bstep (se 2 (by rfl) ⟨778752, by rfl⟩ : syracuseStep 2076673 = 1557505) B1557505
theorem B2306051 : Blo 1536465 2306051 := bstep (se 1 (by rfl) ⟨1729538, by rfl⟩ : syracuseStep 2306051 = 3459077) B3459077
theorem B4378637 : Blo 1536465 4378637 := bstep (se 3 (by rfl) ⟨820994, by rfl⟩ : syracuseStep 4378637 = 1641989) B1641989
theorem B2920465 : Blo 1536465 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B2306081 : Blo 1536465 2306081 := bstep (se 2 (by rfl) ⟨864780, by rfl⟩ : syracuseStep 2306081 = 1729561) B1729561
theorem B2592803 : Blo 1536465 2592803 := bstep (se 1 (by rfl) ⟨1944602, by rfl⟩ : syracuseStep 2592803 = 3889205) B3889205
theorem B2306099 : Blo 1536465 2306099 := bstep (se 1 (by rfl) ⟨1729574, by rfl⟩ : syracuseStep 2306099 = 3459149) B3459149
theorem B18690101 : Blo 1536465 18690101 := bstep (se 5 (by rfl) ⟨876098, by rfl⟩ : syracuseStep 18690101 = 1752197) B1752197
theorem B4157507 : Blo 1536465 4157507 := bstep (se 1 (by rfl) ⟨3118130, by rfl⟩ : syracuseStep 4157507 = 6236261) B6236261
theorem B7385165 : Blo 1536465 7385165 := bstep (se 3 (by rfl) ⟨1384718, by rfl⟩ : syracuseStep 7385165 = 2769437) B2769437
theorem B2306129 : Blo 1536465 2306129 := bstep (se 2 (by rfl) ⟨864798, by rfl⟩ : syracuseStep 2306129 = 1729597) B1729597
theorem B3461201 : Blo 1536465 3461201 := bstep (se 2 (by rfl) ⟨1297950, by rfl⟩ : syracuseStep 3461201 = 2595901) B2595901
theorem B2306147 : Blo 1536465 2306147 := bstep (se 1 (by rfl) ⟨1729610, by rfl⟩ : syracuseStep 2306147 = 3459221) B3459221
theorem B3461219 : Blo 1536465 3461219 := bstep (se 1 (by rfl) ⟨2595914, by rfl⟩ : syracuseStep 3461219 = 5191829) B5191829
theorem B2248817 : Blo 1536465 2248817 := bstep (se 2 (by rfl) ⟨843306, by rfl⟩ : syracuseStep 2248817 = 1686613) B1686613
theorem B2306177 : Blo 1536465 2306177 := bstep (se 2 (by rfl) ⟨864816, by rfl⟩ : syracuseStep 2306177 = 1729633) B1729633
theorem B8753285 : Blo 1536465 8753285 := bstep (se 4 (by rfl) ⟨820620, by rfl⟩ : syracuseStep 8753285 = 1641241) B1641241
theorem B11079821 : Blo 1536465 11079821 := bstep (se 3 (by rfl) ⟨2077466, by rfl⟩ : syracuseStep 11079821 = 4154933) B4154933
theorem B5189777 : Blo 1536465 5189777 := bstep (se 2 (by rfl) ⟨1946166, by rfl⟩ : syracuseStep 5189777 = 3892333) B3892333
theorem B2306195 : Blo 1536465 2306195 := bstep (se 1 (by rfl) ⟨1729646, by rfl⟩ : syracuseStep 2306195 = 3459293) B3459293
theorem B2592931 : Blo 1536465 2592931 := bstep (se 1 (by rfl) ⟨1944698, by rfl⟩ : syracuseStep 2592931 = 3889397) B3889397
theorem B2306225 : Blo 1536465 2306225 := bstep (se 2 (by rfl) ⟨864834, by rfl⟩ : syracuseStep 2306225 = 1729669) B1729669
theorem B2306243 : Blo 1536465 2306243 := bstep (se 1 (by rfl) ⟨1729682, by rfl⟩ : syracuseStep 2306243 = 3459365) B3459365
theorem B4378819 : Blo 1536465 4378819 := bstep (se 1 (by rfl) ⟨3284114, by rfl⟩ : syracuseStep 4378819 = 6568229) B6568229
theorem B6566093 : Blo 1536465 6566093 := bstep (se 3 (by rfl) ⟨1231142, by rfl⟩ : syracuseStep 6566093 = 2462285) B2462285
theorem B2306273 : Blo 1536465 2306273 := bstep (se 2 (by rfl) ⟨864852, by rfl⟩ : syracuseStep 2306273 = 1729705) B1729705
theorem B2306291 : Blo 1536465 2306291 := bstep (se 1 (by rfl) ⟨1729718, by rfl⟩ : syracuseStep 2306291 = 3459437) B3459437
theorem B2306321 : Blo 1536465 2306321 := bstep (se 2 (by rfl) ⟨864870, by rfl⟩ : syracuseStep 2306321 = 1729741) B1729741
theorem B2306339 : Blo 1536465 2306339 := bstep (se 1 (by rfl) ⟨1729754, by rfl⟩ : syracuseStep 2306339 = 3459509) B3459509
theorem B2593073 : Blo 1536465 2593073 := bstep (se 2 (by rfl) ⟨972402, by rfl⟩ : syracuseStep 2593073 = 1944805) B1944805
theorem B2306369 : Blo 1536465 2306369 := bstep (se 2 (by rfl) ⟨864888, by rfl⟩ : syracuseStep 2306369 = 1729777) B1729777
theorem B1945939 : Blo 1536465 1945939 := bstep (se 1 (by rfl) ⟨1459454, by rfl⟩ : syracuseStep 1945939 = 2918909) B2918909
theorem B2306387 : Blo 1536465 2306387 := bstep (se 1 (by rfl) ⟨1729790, by rfl⟩ : syracuseStep 2306387 = 3459581) B3459581
theorem B2306417 : Blo 1536465 2306417 := bstep (se 2 (by rfl) ⟨864906, by rfl⟩ : syracuseStep 2306417 = 1729813) B1729813
theorem B3461489 : Blo 1536465 3461489 := bstep (se 2 (by rfl) ⟨1298058, by rfl⟩ : syracuseStep 3461489 = 2596117) B2596117
theorem B2306435 : Blo 1536465 2306435 := bstep (se 1 (by rfl) ⟨1729826, by rfl⟩ : syracuseStep 2306435 = 3459653) B3459653
theorem B3461507 : Blo 1536465 3461507 := bstep (se 1 (by rfl) ⟨2596130, by rfl⟩ : syracuseStep 3461507 = 5192261) B5192261
theorem B11678093 : Blo 1536465 11678093 := bstep (se 3 (by rfl) ⟨2189642, by rfl⟩ : syracuseStep 11678093 = 4379285) B4379285
theorem B2306465 : Blo 1536465 2306465 := bstep (se 2 (by rfl) ⟨864924, by rfl⟩ : syracuseStep 2306465 = 1729849) B1729849
theorem B2593201 : Blo 1536465 2593201 := bstep (se 2 (by rfl) ⟨972450, by rfl⟩ : syracuseStep 2593201 = 1944901) B1944901
theorem B1946035 : Blo 1536465 1946035 := bstep (se 1 (by rfl) ⟨1459526, by rfl⟩ : syracuseStep 1946035 = 2919053) B2919053
theorem B2306483 : Blo 1536465 2306483 := bstep (se 1 (by rfl) ⟨1729862, by rfl⟩ : syracuseStep 2306483 = 3459725) B3459725
theorem B2306513 : Blo 1536465 2306513 := bstep (se 2 (by rfl) ⟨864942, by rfl⟩ : syracuseStep 2306513 = 1729885) B1729885
theorem B1536467 : Blo 1536465 1536467 := bstep (se 1 (by rfl) ⟨1152350, by rfl⟩ : syracuseStep 1536467 = 2304701) B2304701
theorem B2593235 : Blo 1536465 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B1536483 : Blo 1536465 1536483 := bstep (se 1 (by rfl) ⟨1152362, by rfl⟩ : syracuseStep 1536483 = 2304725) B2304725
theorem B2306531 : Blo 1536465 2306531 := bstep (se 1 (by rfl) ⟨1729898, by rfl⟩ : syracuseStep 2306531 = 3459797) B3459797
theorem B7885297 : Blo 1536465 7885297 := bstep (se 2 (by rfl) ⟨2956986, by rfl⟩ : syracuseStep 7885297 = 5913973) B5913973
theorem B1536499 : Blo 1536465 1536499 := bstep (se 1 (by rfl) ⟨1152374, by rfl⟩ : syracuseStep 1536499 = 2304749) B2304749
theorem B2462195 : Blo 1536465 2462195 := bstep (se 1 (by rfl) ⟨1846646, by rfl⟩ : syracuseStep 2462195 = 3693293) B3693293
theorem B2306561 : Blo 1536465 2306561 := bstep (se 2 (by rfl) ⟨864960, by rfl⟩ : syracuseStep 2306561 = 1729921) B1729921
theorem B1536515 : Blo 1536465 1536515 := bstep (se 1 (by rfl) ⟨1152386, by rfl⟩ : syracuseStep 1536515 = 2304773) B2304773
theorem B1536531 : Blo 1536465 1536531 := bstep (se 1 (by rfl) ⟨1152398, by rfl⟩ : syracuseStep 1536531 = 2304797) B2304797
theorem B2306579 : Blo 1536465 2306579 := bstep (se 1 (by rfl) ⟨1729934, by rfl⟩ : syracuseStep 2306579 = 3459869) B3459869
theorem B1536547 : Blo 1536465 1536547 := bstep (se 1 (by rfl) ⟨1152410, by rfl⟩ : syracuseStep 1536547 = 2304821) B2304821
theorem B2306609 : Blo 1536465 2306609 := bstep (se 2 (by rfl) ⟨864978, by rfl⟩ : syracuseStep 2306609 = 1729957) B1729957
theorem B1536563 : Blo 1536465 1536563 := bstep (se 1 (by rfl) ⟨1152422, by rfl⟩ : syracuseStep 1536563 = 2304845) B2304845
theorem B1536579 : Blo 1536465 1536579 := bstep (se 1 (by rfl) ⟨1152434, by rfl⟩ : syracuseStep 1536579 = 2304869) B2304869
theorem B2306627 : Blo 1536465 2306627 := bstep (se 1 (by rfl) ⟨1729970, by rfl⟩ : syracuseStep 2306627 = 3459941) B3459941
theorem B8753741 : Blo 1536465 8753741 := bstep (se 3 (by rfl) ⟨1641326, by rfl⟩ : syracuseStep 8753741 = 3282653) B3282653
theorem B1536595 : Blo 1536465 1536595 := bstep (se 1 (by rfl) ⟨1152446, by rfl⟩ : syracuseStep 1536595 = 2304893) B2304893
theorem B2593363 : Blo 1536465 2593363 := bstep (se 1 (by rfl) ⟨1945022, by rfl⟩ : syracuseStep 2593363 = 3890045) B3890045
theorem B2306657 : Blo 1536465 2306657 := bstep (se 2 (by rfl) ⟨864996, by rfl⟩ : syracuseStep 2306657 = 1729993) B1729993
theorem B7778915 : Blo 1536465 7778915 := bstep (se 1 (by rfl) ⟨5834186, by rfl⟩ : syracuseStep 7778915 = 11668373) B11668373
theorem B1536611 : Blo 1536465 1536611 := bstep (se 1 (by rfl) ⟨1152458, by rfl⟩ : syracuseStep 1536611 = 2304917) B2304917
theorem B2077283 : Blo 1536465 2077283 := bstep (se 1 (by rfl) ⟨1557962, by rfl⟩ : syracuseStep 2077283 = 3115925) B3115925
theorem B1536627 : Blo 1536465 1536627 := bstep (se 1 (by rfl) ⟨1152470, by rfl⟩ : syracuseStep 1536627 = 2304941) B2304941
theorem B2462323 : Blo 1536465 2462323 := bstep (se 1 (by rfl) ⟨1846742, by rfl⟩ : syracuseStep 2462323 = 3693485) B3693485
theorem B2306675 : Blo 1536465 2306675 := bstep (se 1 (by rfl) ⟨1730006, by rfl⟩ : syracuseStep 2306675 = 3460013) B3460013
theorem B1536643 : Blo 1536465 1536643 := bstep (se 1 (by rfl) ⟨1152482, by rfl⟩ : syracuseStep 1536643 = 2304965) B2304965
theorem B4928131 : Blo 1536465 4928131 := bstep (se 1 (by rfl) ⟨3696098, by rfl⟩ : syracuseStep 4928131 = 7392197) B7392197
theorem B5837453 : Blo 1536465 5837453 := bstep (se 3 (by rfl) ⟨1094522, by rfl⟩ : syracuseStep 5837453 = 2189045) B2189045
theorem B2306705 : Blo 1536465 2306705 := bstep (se 2 (by rfl) ⟨865014, by rfl⟩ : syracuseStep 2306705 = 1730029) B1730029
theorem B1536659 : Blo 1536465 1536659 := bstep (se 1 (by rfl) ⟨1152494, by rfl⟩ : syracuseStep 1536659 = 2304989) B2304989
theorem B1536675 : Blo 1536465 1536675 := bstep (se 1 (by rfl) ⟨1152506, by rfl⟩ : syracuseStep 1536675 = 2305013) B2305013
theorem B2306723 : Blo 1536465 2306723 := bstep (se 1 (by rfl) ⟨1730042, by rfl⟩ : syracuseStep 2306723 = 3460085) B3460085
theorem B4379309 : Blo 1536465 4379309 := bstep (se 3 (by rfl) ⟨821120, by rfl⟩ : syracuseStep 4379309 = 1642241) B1642241
theorem B5190317 : Blo 1536465 5190317 := bstep (se 3 (by rfl) ⟨973184, by rfl⟩ : syracuseStep 5190317 = 1946369) B1946369
theorem B1536691 : Blo 1536465 1536691 := bstep (se 1 (by rfl) ⟨1152518, by rfl⟩ : syracuseStep 1536691 = 2305037) B2305037
theorem B8762033 : Blo 1536465 8762033 := bstep (se 2 (by rfl) ⟨3285762, by rfl⟩ : syracuseStep 8762033 = 6571525) B6571525
theorem B2306753 : Blo 1536465 2306753 := bstep (se 2 (by rfl) ⟨865032, by rfl⟩ : syracuseStep 2306753 = 1730065) B1730065
theorem B1536707 : Blo 1536465 1536707 := bstep (se 1 (by rfl) ⟨1152530, by rfl⟩ : syracuseStep 1536707 = 2305061) B2305061
theorem B1536723 : Blo 1536465 1536723 := bstep (se 1 (by rfl) ⟨1152542, by rfl⟩ : syracuseStep 1536723 = 2305085) B2305085
theorem B2306771 : Blo 1536465 2306771 := bstep (se 1 (by rfl) ⟨1730078, by rfl⟩ : syracuseStep 2306771 = 3460157) B3460157
theorem B2593505 : Blo 1536465 2593505 := bstep (se 2 (by rfl) ⟨972564, by rfl⟩ : syracuseStep 2593505 = 1945129) B1945129
theorem B1536739 : Blo 1536465 1536739 := bstep (se 1 (by rfl) ⟨1152554, by rfl⟩ : syracuseStep 1536739 = 2305109) B2305109
theorem B5190371 : Blo 1536465 5190371 := bstep (se 1 (by rfl) ⟨3892778, by rfl⟩ : syracuseStep 5190371 = 7785557) B7785557
theorem B11227889 : Blo 1536465 11227889 := bstep (se 2 (by rfl) ⟨4210458, by rfl⟩ : syracuseStep 11227889 = 8420917) B8420917
theorem B2306801 : Blo 1536465 2306801 := bstep (se 2 (by rfl) ⟨865050, by rfl⟩ : syracuseStep 2306801 = 1730101) B1730101
theorem B1536755 : Blo 1536465 1536755 := bstep (se 1 (by rfl) ⟨1152566, by rfl⟩ : syracuseStep 1536755 = 2305133) B2305133
theorem B1536771 : Blo 1536465 1536771 := bstep (se 1 (by rfl) ⟨1152578, by rfl⟩ : syracuseStep 1536771 = 2305157) B2305157
theorem B2306819 : Blo 1536465 2306819 := bstep (se 1 (by rfl) ⟨1730114, by rfl⟩ : syracuseStep 2306819 = 3460229) B3460229
theorem B1536787 : Blo 1536465 1536787 := bstep (se 1 (by rfl) ⟨1152590, by rfl⟩ : syracuseStep 1536787 = 2305181) B2305181
theorem B2306849 : Blo 1536465 2306849 := bstep (se 2 (by rfl) ⟨865068, by rfl⟩ : syracuseStep 2306849 = 1730137) B1730137
theorem B1536803 : Blo 1536465 1536803 := bstep (se 1 (by rfl) ⟨1152602, by rfl⟩ : syracuseStep 1536803 = 2305205) B2305205
theorem B1536819 : Blo 1536465 1536819 := bstep (se 1 (by rfl) ⟨1152614, by rfl⟩ : syracuseStep 1536819 = 2305229) B2305229
theorem B2306867 : Blo 1536465 2306867 := bstep (se 1 (by rfl) ⟨1730150, by rfl⟩ : syracuseStep 2306867 = 3460301) B3460301
theorem B1536835 : Blo 1536465 1536835 := bstep (se 1 (by rfl) ⟨1152626, by rfl⟩ : syracuseStep 1536835 = 2305253) B2305253
theorem B2306897 : Blo 1536465 2306897 := bstep (se 2 (by rfl) ⟨865086, by rfl⟩ : syracuseStep 2306897 = 1730173) B1730173
theorem B1536851 : Blo 1536465 1536851 := bstep (se 1 (by rfl) ⟨1152638, by rfl⟩ : syracuseStep 1536851 = 2305277) B2305277
theorem B2593633 : Blo 1536465 2593633 := bstep (se 2 (by rfl) ⟨972612, by rfl⟩ : syracuseStep 2593633 = 1945225) B1945225
theorem B1536867 : Blo 1536465 1536867 := bstep (se 1 (by rfl) ⟨1152650, by rfl⟩ : syracuseStep 1536867 = 2305301) B2305301
theorem B2306915 : Blo 1536465 2306915 := bstep (se 1 (by rfl) ⟨1730186, by rfl⟩ : syracuseStep 2306915 = 3460373) B3460373
theorem B4158307 : Blo 1536465 4158307 := bstep (se 1 (by rfl) ⟨3118730, by rfl⟩ : syracuseStep 4158307 = 6237461) B6237461
theorem B6746993 : Blo 1536465 6746993 := bstep (se 2 (by rfl) ⟨2530122, by rfl⟩ : syracuseStep 6746993 = 5060245) B5060245
theorem B1536883 : Blo 1536465 1536883 := bstep (se 1 (by rfl) ⟨1152662, by rfl⟩ : syracuseStep 1536883 = 2305325) B2305325
theorem B2306945 : Blo 1536465 2306945 := bstep (se 2 (by rfl) ⟨865104, by rfl⟩ : syracuseStep 2306945 = 1730209) B1730209
theorem B1536899 : Blo 1536465 1536899 := bstep (se 1 (by rfl) ⟨1152674, by rfl⟩ : syracuseStep 1536899 = 2305349) B2305349
theorem B2593667 : Blo 1536465 2593667 := bstep (se 1 (by rfl) ⟨1945250, by rfl⟩ : syracuseStep 2593667 = 3890501) B3890501
theorem B88691597 : Blo 1536465 88691597 := bstep (se 3 (by rfl) ⟨16629674, by rfl⟩ : syracuseStep 88691597 = 33259349) B33259349
theorem B1536915 : Blo 1536465 1536915 := bstep (se 1 (by rfl) ⟨1152686, by rfl⟩ : syracuseStep 1536915 = 2305373) B2305373
theorem B2306963 : Blo 1536465 2306963 := bstep (se 1 (by rfl) ⟨1730222, by rfl⟩ : syracuseStep 2306963 = 3460445) B3460445
theorem B1536931 : Blo 1536465 1536931 := bstep (se 1 (by rfl) ⟨1152698, by rfl⟩ : syracuseStep 1536931 = 2305397) B2305397
theorem B1946531 : Blo 1536465 1946531 := bstep (se 1 (by rfl) ⟨1459898, by rfl⟩ : syracuseStep 1946531 = 2919797) B2919797
theorem B2306993 : Blo 1536465 2306993 := bstep (se 2 (by rfl) ⟨865122, by rfl⟩ : syracuseStep 2306993 = 1730245) B1730245
theorem B1536947 : Blo 1536465 1536947 := bstep (se 1 (by rfl) ⟨1152710, by rfl⟩ : syracuseStep 1536947 = 2305421) B2305421
theorem B1536963 : Blo 1536465 1536963 := bstep (se 1 (by rfl) ⟨1152722, by rfl⟩ : syracuseStep 1536963 = 2305445) B2305445
theorem B2307011 : Blo 1536465 2307011 := bstep (se 1 (by rfl) ⟨1730258, by rfl⟩ : syracuseStep 2307011 = 3460517) B3460517
theorem B4928465 : Blo 1536465 4928465 := bstep (se 2 (by rfl) ⟨1848174, by rfl⟩ : syracuseStep 4928465 = 3696349) B3696349
theorem B1536979 : Blo 1536465 1536979 := bstep (se 1 (by rfl) ⟨1152734, by rfl⟩ : syracuseStep 1536979 = 2305469) B2305469
theorem B2307041 : Blo 1536465 2307041 := bstep (se 2 (by rfl) ⟨865140, by rfl⟩ : syracuseStep 2307041 = 1730281) B1730281
theorem B1536995 : Blo 1536465 1536995 := bstep (se 1 (by rfl) ⟨1152746, by rfl⟩ : syracuseStep 1536995 = 2305493) B2305493
theorem B15774691 : Blo 1536465 15774691 := bstep (se 1 (by rfl) ⟨11831018, by rfl⟩ : syracuseStep 15774691 = 23662037) B23662037
theorem B5190641 : Blo 1536465 5190641 := bstep (se 2 (by rfl) ⟨1946490, by rfl⟩ : syracuseStep 5190641 = 3892981) B3892981
theorem B1537011 : Blo 1536465 1537011 := bstep (se 1 (by rfl) ⟨1152758, by rfl⟩ : syracuseStep 1537011 = 2305517) B2305517
theorem B2307059 : Blo 1536465 2307059 := bstep (se 1 (by rfl) ⟨1730294, by rfl⟩ : syracuseStep 2307059 = 3460589) B3460589
theorem B1537027 : Blo 1536465 1537027 := bstep (se 1 (by rfl) ⟨1152770, by rfl⟩ : syracuseStep 1537027 = 2305541) B2305541
theorem B2593795 : Blo 1536465 2593795 := bstep (se 1 (by rfl) ⟨1945346, by rfl⟩ : syracuseStep 2593795 = 3890693) B3890693
theorem B2307089 : Blo 1536465 2307089 := bstep (se 2 (by rfl) ⟨865158, by rfl⟩ : syracuseStep 2307089 = 1730317) B1730317
theorem B1537043 : Blo 1536465 1537043 := bstep (se 1 (by rfl) ⟨1152782, by rfl⟩ : syracuseStep 1537043 = 2305565) B2305565
theorem B1537059 : Blo 1536465 1537059 := bstep (se 1 (by rfl) ⟨1152794, by rfl⟩ : syracuseStep 1537059 = 2305589) B2305589
theorem B2307107 : Blo 1536465 2307107 := bstep (se 1 (by rfl) ⟨1730330, by rfl⟩ : syracuseStep 2307107 = 3460661) B3460661
theorem B1537075 : Blo 1536465 1537075 := bstep (se 1 (by rfl) ⟨1152806, by rfl⟩ : syracuseStep 1537075 = 2305613) B2305613
theorem B2307137 : Blo 1536465 2307137 := bstep (se 2 (by rfl) ⟨865176, by rfl⟩ : syracuseStep 2307137 = 1730353) B1730353
theorem B1537091 : Blo 1536465 1537091 := bstep (se 1 (by rfl) ⟨1152818, by rfl⟩ : syracuseStep 1537091 = 2305637) B2305637
theorem B1537107 : Blo 1536465 1537107 := bstep (se 1 (by rfl) ⟨1152830, by rfl⟩ : syracuseStep 1537107 = 2305661) B2305661
theorem B2307155 : Blo 1536465 2307155 := bstep (se 1 (by rfl) ⟨1730366, by rfl⟩ : syracuseStep 2307155 = 3460733) B3460733
theorem B13128803 : Blo 1536465 13128803 := bstep (se 1 (by rfl) ⟨9846602, by rfl⟩ : syracuseStep 13128803 = 19693205) B19693205
theorem B1537123 : Blo 1536465 1537123 := bstep (se 1 (by rfl) ⟨1152842, by rfl⟩ : syracuseStep 1537123 = 2305685) B2305685
theorem B2307185 : Blo 1536465 2307185 := bstep (se 2 (by rfl) ⟨865194, by rfl⟩ : syracuseStep 2307185 = 1730389) B1730389
theorem B1537139 : Blo 1536465 1537139 := bstep (se 1 (by rfl) ⟨1152854, by rfl⟩ : syracuseStep 1537139 = 2305709) B2305709
theorem B1537155 : Blo 1536465 1537155 := bstep (se 1 (by rfl) ⟨1152866, by rfl⟩ : syracuseStep 1537155 = 2305733) B2305733
theorem B2307203 : Blo 1536465 2307203 := bstep (se 1 (by rfl) ⟨1730402, by rfl⟩ : syracuseStep 2307203 = 3460805) B3460805
theorem B2593937 : Blo 1536465 2593937 := bstep (se 2 (by rfl) ⟨972726, by rfl⟩ : syracuseStep 2593937 = 1945453) B1945453
theorem B1537171 : Blo 1536465 1537171 := bstep (se 1 (by rfl) ⟨1152878, by rfl⟩ : syracuseStep 1537171 = 2305757) B2305757
theorem B2462881 : Blo 1536465 2462881 := bstep (se 2 (by rfl) ⟨923580, by rfl⟩ : syracuseStep 2462881 = 1847161) B1847161
theorem B2307233 : Blo 1536465 2307233 := bstep (se 2 (by rfl) ⟨865212, by rfl⟩ : syracuseStep 2307233 = 1730425) B1730425
theorem B1537187 : Blo 1536465 1537187 := bstep (se 1 (by rfl) ⟨1152890, by rfl⟩ : syracuseStep 1537187 = 2305781) B2305781
theorem B1537203 : Blo 1536465 1537203 := bstep (se 1 (by rfl) ⟨1152902, by rfl⟩ : syracuseStep 1537203 = 2305805) B2305805
theorem B2307251 : Blo 1536465 2307251 := bstep (se 1 (by rfl) ⟨1730438, by rfl⟩ : syracuseStep 2307251 = 3460877) B3460877
theorem B1537219 : Blo 1536465 1537219 := bstep (se 1 (by rfl) ⟨1152914, by rfl⟩ : syracuseStep 1537219 = 2305829) B2305829
theorem B2307281 : Blo 1536465 2307281 := bstep (se 2 (by rfl) ⟨865230, by rfl⟩ : syracuseStep 2307281 = 1730461) B1730461
theorem B1537235 : Blo 1536465 1537235 := bstep (se 1 (by rfl) ⟨1152926, by rfl⟩ : syracuseStep 1537235 = 2305853) B2305853
theorem B1537251 : Blo 1536465 1537251 := bstep (se 1 (by rfl) ⟨1152938, by rfl⟩ : syracuseStep 1537251 = 2305877) B2305877
theorem B2307299 : Blo 1536465 2307299 := bstep (se 1 (by rfl) ⟨1730474, by rfl⟩ : syracuseStep 2307299 = 3460949) B3460949
theorem B1537267 : Blo 1536465 1537267 := bstep (se 1 (by rfl) ⟨1152950, by rfl⟩ : syracuseStep 1537267 = 2305901) B2305901
theorem B2307329 : Blo 1536465 2307329 := bstep (se 2 (by rfl) ⟨865248, by rfl⟩ : syracuseStep 2307329 = 1730497) B1730497
theorem B1537283 : Blo 1536465 1537283 := bstep (se 1 (by rfl) ⟨1152962, by rfl⟩ : syracuseStep 1537283 = 2305925) B2305925
theorem B2594065 : Blo 1536465 2594065 := bstep (se 2 (by rfl) ⟨972774, by rfl⟩ : syracuseStep 2594065 = 1945549) B1945549
theorem B1537299 : Blo 1536465 1537299 := bstep (se 1 (by rfl) ⟨1152974, by rfl⟩ : syracuseStep 1537299 = 2305949) B2305949
theorem B2307347 : Blo 1536465 2307347 := bstep (se 1 (by rfl) ⟨1730510, by rfl⟩ : syracuseStep 2307347 = 3461021) B3461021
theorem B4437283 : Blo 1536465 4437283 := bstep (se 1 (by rfl) ⟨3327962, by rfl⟩ : syracuseStep 4437283 = 6655925) B6655925
theorem B1537315 : Blo 1536465 1537315 := bstep (se 1 (by rfl) ⟨1152986, by rfl⟩ : syracuseStep 1537315 = 2305973) B2305973
theorem B2307377 : Blo 1536465 2307377 := bstep (se 2 (by rfl) ⟨865266, by rfl⟩ : syracuseStep 2307377 = 1730533) B1730533
theorem B7787825 : Blo 1536465 7787825 := bstep (se 2 (by rfl) ⟨2920434, by rfl⟩ : syracuseStep 7787825 = 5840869) B5840869
theorem B2594099 : Blo 1536465 2594099 := bstep (se 1 (by rfl) ⟨1945574, by rfl⟩ : syracuseStep 2594099 = 3891149) B3891149
theorem B1537331 : Blo 1536465 1537331 := bstep (se 1 (by rfl) ⟨1152998, by rfl⟩ : syracuseStep 1537331 = 2305997) B2305997
theorem B1537347 : Blo 1536465 1537347 := bstep (se 1 (by rfl) ⟨1153010, by rfl⟩ : syracuseStep 1537347 = 2306021) B2306021
theorem B2307395 : Blo 1536465 2307395 := bstep (se 1 (by rfl) ⟨1730546, by rfl⟩ : syracuseStep 2307395 = 3461093) B3461093
theorem B4437325 : Blo 1536465 4437325 := bstep (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) B1663997
theorem B1537363 : Blo 1536465 1537363 := bstep (se 1 (by rfl) ⟨1153022, by rfl⟩ : syracuseStep 1537363 = 2306045) B2306045
theorem B2307425 : Blo 1536465 2307425 := bstep (se 2 (by rfl) ⟨865284, by rfl⟩ : syracuseStep 2307425 = 1730569) B1730569
theorem B1537379 : Blo 1536465 1537379 := bstep (se 1 (by rfl) ⟨1153034, by rfl⟩ : syracuseStep 1537379 = 2306069) B2306069
theorem B1537395 : Blo 1536465 1537395 := bstep (se 1 (by rfl) ⟨1153046, by rfl⟩ : syracuseStep 1537395 = 2306093) B2306093
theorem B2307443 : Blo 1536465 2307443 := bstep (se 1 (by rfl) ⟨1730582, by rfl⟩ : syracuseStep 2307443 = 3461165) B3461165
theorem B1537411 : Blo 1536465 1537411 := bstep (se 1 (by rfl) ⟨1153058, by rfl⟩ : syracuseStep 1537411 = 2306117) B2306117
theorem B2078083 : Blo 1536465 2078083 := bstep (se 1 (by rfl) ⟨1558562, by rfl⟩ : syracuseStep 2078083 = 3117125) B3117125
theorem B7779725 : Blo 1536465 7779725 := bstep (se 3 (by rfl) ⟨1458698, by rfl⟩ : syracuseStep 7779725 = 2917397) B2917397
theorem B2307473 : Blo 1536465 2307473 := bstep (se 2 (by rfl) ⟨865302, by rfl⟩ : syracuseStep 2307473 = 1730605) B1730605
theorem B1537427 : Blo 1536465 1537427 := bstep (se 1 (by rfl) ⟨1153070, by rfl⟩ : syracuseStep 1537427 = 2306141) B2306141
theorem B1537443 : Blo 1536465 1537443 := bstep (se 1 (by rfl) ⟨1153082, by rfl⟩ : syracuseStep 1537443 = 2306165) B2306165
theorem B2307491 : Blo 1536465 2307491 := bstep (se 1 (by rfl) ⟨1730618, by rfl⟩ : syracuseStep 2307491 = 3461237) B3461237
theorem B5838257 : Blo 1536465 5838257 := bstep (se 2 (by rfl) ⟨2189346, by rfl⟩ : syracuseStep 5838257 = 4378693) B4378693
theorem B2594227 : Blo 1536465 2594227 := bstep (se 1 (by rfl) ⟨1945670, by rfl⟩ : syracuseStep 2594227 = 3891341) B3891341
theorem B1537459 : Blo 1536465 1537459 := bstep (se 1 (by rfl) ⟨1153094, by rfl⟩ : syracuseStep 1537459 = 2306189) B2306189
theorem B2307521 : Blo 1536465 2307521 := bstep (se 2 (by rfl) ⟨865320, by rfl⟩ : syracuseStep 2307521 = 1730641) B1730641
theorem B1537475 : Blo 1536465 1537475 := bstep (se 1 (by rfl) ⟨1153106, by rfl⟩ : syracuseStep 1537475 = 2306213) B2306213
theorem B1537491 : Blo 1536465 1537491 := bstep (se 1 (by rfl) ⟨1153118, by rfl⟩ : syracuseStep 1537491 = 2306237) B2306237
theorem B2307539 : Blo 1536465 2307539 := bstep (se 1 (by rfl) ⟨1730654, by rfl⟩ : syracuseStep 2307539 = 3461309) B3461309
theorem B19961315 : Blo 1536465 19961315 := bstep (se 1 (by rfl) ⟨14970986, by rfl⟩ : syracuseStep 19961315 = 29941973) B29941973
theorem B1537507 : Blo 1536465 1537507 := bstep (se 1 (by rfl) ⟨1153130, by rfl⟩ : syracuseStep 1537507 = 2306261) B2306261
theorem B2307569 : Blo 1536465 2307569 := bstep (se 2 (by rfl) ⟨865338, by rfl⟩ : syracuseStep 2307569 = 1730677) B1730677
theorem B1537523 : Blo 1536465 1537523 := bstep (se 1 (by rfl) ⟨1153142, by rfl⟩ : syracuseStep 1537523 = 2306285) B2306285
theorem B1537539 : Blo 1536465 1537539 := bstep (se 1 (by rfl) ⟨1153154, by rfl⟩ : syracuseStep 1537539 = 2306309) B2306309
theorem B2307587 : Blo 1536465 2307587 := bstep (se 1 (by rfl) ⟨1730690, by rfl⟩ : syracuseStep 2307587 = 3461381) B3461381
theorem B5191181 : Blo 1536465 5191181 := bstep (se 3 (by rfl) ⟨973346, by rfl⟩ : syracuseStep 5191181 = 1946693) B1946693
theorem B1537555 : Blo 1536465 1537555 := bstep (se 1 (by rfl) ⟨1153166, by rfl⟩ : syracuseStep 1537555 = 2306333) B2306333
theorem B2307617 : Blo 1536465 2307617 := bstep (se 2 (by rfl) ⟨865356, by rfl⟩ : syracuseStep 2307617 = 1730713) B1730713
theorem B1537571 : Blo 1536465 1537571 := bstep (se 1 (by rfl) ⟨1153178, by rfl⟩ : syracuseStep 1537571 = 2306357) B2306357
theorem B1537587 : Blo 1536465 1537587 := bstep (se 1 (by rfl) ⟨1153190, by rfl⟩ : syracuseStep 1537587 = 2306381) B2306381
theorem B2307635 : Blo 1536465 2307635 := bstep (se 1 (by rfl) ⟨1730726, by rfl⟩ : syracuseStep 2307635 = 3461453) B3461453
theorem B2594369 : Blo 1536465 2594369 := bstep (se 2 (by rfl) ⟨972888, by rfl⟩ : syracuseStep 2594369 = 1945777) B1945777
theorem B1537603 : Blo 1536465 1537603 := bstep (se 1 (by rfl) ⟨1153202, by rfl⟩ : syracuseStep 1537603 = 2306405) B2306405
theorem B5191235 : Blo 1536465 5191235 := bstep (se 1 (by rfl) ⟨3893426, by rfl⟩ : syracuseStep 5191235 = 7786853) B7786853
theorem B2307665 : Blo 1536465 2307665 := bstep (se 2 (by rfl) ⟨865374, by rfl⟩ : syracuseStep 2307665 = 1730749) B1730749
theorem B1537619 : Blo 1536465 1537619 := bstep (se 1 (by rfl) ⟨1153214, by rfl⟩ : syracuseStep 1537619 = 2306429) B2306429
theorem B1537635 : Blo 1536465 1537635 := bstep (se 1 (by rfl) ⟨1153226, by rfl⟩ : syracuseStep 1537635 = 2306453) B2306453
theorem B2307683 : Blo 1536465 2307683 := bstep (se 1 (by rfl) ⟨1730762, by rfl⟩ : syracuseStep 2307683 = 3461525) B3461525
theorem B1537651 : Blo 1536465 1537651 := bstep (se 1 (by rfl) ⟨1153238, by rfl⟩ : syracuseStep 1537651 = 2306477) B2306477
theorem B1537667 : Blo 1536465 1537667 := bstep (se 1 (by rfl) ⟨1153250, by rfl⟩ : syracuseStep 1537667 = 2306501) B2306501
theorem B28038797 : Blo 1536465 28038797 := bstep (se 3 (by rfl) ⟨5257274, by rfl⟩ : syracuseStep 28038797 = 10514549) B10514549
theorem B1537683 : Blo 1536465 1537683 := bstep (se 1 (by rfl) ⟨1153262, by rfl⟩ : syracuseStep 1537683 = 2306525) B2306525
theorem B1537699 : Blo 1536465 1537699 := bstep (se 1 (by rfl) ⟨1153274, by rfl⟩ : syracuseStep 1537699 = 2306549) B2306549
theorem B1537715 : Blo 1536465 1537715 := bstep (se 1 (by rfl) ⟨1153286, by rfl⟩ : syracuseStep 1537715 = 2306573) B2306573
theorem B2594497 : Blo 1536465 2594497 := bstep (se 2 (by rfl) ⟨972936, by rfl⟩ : syracuseStep 2594497 = 1945873) B1945873
theorem B1537731 : Blo 1536465 1537731 := bstep (se 1 (by rfl) ⟨1153298, by rfl⟩ : syracuseStep 1537731 = 2306597) B2306597
theorem B1537747 : Blo 1536465 1537747 := bstep (se 1 (by rfl) ⟨1153310, by rfl⟩ : syracuseStep 1537747 = 2306621) B2306621
theorem B2594531 : Blo 1536465 2594531 := bstep (se 1 (by rfl) ⟨1945898, by rfl⟩ : syracuseStep 2594531 = 3891797) B3891797
theorem B1537763 : Blo 1536465 1537763 := bstep (se 1 (by rfl) ⟨1153322, by rfl⟩ : syracuseStep 1537763 = 2306645) B2306645
theorem B14784241 : Blo 1536465 14784241 := bstep (se 2 (by rfl) ⟨5544090, by rfl⟩ : syracuseStep 14784241 = 11088181) B11088181
theorem B1537779 : Blo 1536465 1537779 := bstep (se 1 (by rfl) ⟨1153334, by rfl⟩ : syracuseStep 1537779 = 2306669) B2306669
theorem B1537795 : Blo 1536465 1537795 := bstep (se 1 (by rfl) ⟨1153346, by rfl⟩ : syracuseStep 1537795 = 2306693) B2306693
theorem B9852677 : Blo 1536465 9852677 := bstep (se 4 (by rfl) ⟨923688, by rfl⟩ : syracuseStep 9852677 = 1847377) B1847377
theorem B1537811 : Blo 1536465 1537811 := bstep (se 1 (by rfl) ⟨1153358, by rfl⟩ : syracuseStep 1537811 = 2306717) B2306717
theorem B1537827 : Blo 1536465 1537827 := bstep (se 1 (by rfl) ⟨1153370, by rfl⟩ : syracuseStep 1537827 = 2306741) B2306741
theorem B1537843 : Blo 1536465 1537843 := bstep (se 1 (by rfl) ⟨1153382, by rfl⟩ : syracuseStep 1537843 = 2306765) B2306765
theorem B2463553 : Blo 1536465 2463553 := bstep (se 2 (by rfl) ⟨923832, by rfl⟩ : syracuseStep 2463553 = 1847665) B1847665
theorem B1537859 : Blo 1536465 1537859 := bstep (se 1 (by rfl) ⟨1153394, by rfl⟩ : syracuseStep 1537859 = 2306789) B2306789
theorem B4380493 : Blo 1536465 4380493 := bstep (se 3 (by rfl) ⟨821342, by rfl⟩ : syracuseStep 4380493 = 1642685) B1642685
theorem B5191505 : Blo 1536465 5191505 := bstep (se 2 (by rfl) ⟨1946814, by rfl⟩ : syracuseStep 5191505 = 3893629) B3893629
theorem B1537875 : Blo 1536465 1537875 := bstep (se 1 (by rfl) ⟨1153406, by rfl⟩ : syracuseStep 1537875 = 2306813) B2306813
theorem B2594659 : Blo 1536465 2594659 := bstep (se 1 (by rfl) ⟨1945994, by rfl⟩ : syracuseStep 2594659 = 3891989) B3891989
theorem B1537891 : Blo 1536465 1537891 := bstep (se 1 (by rfl) ⟨1153418, by rfl⟩ : syracuseStep 1537891 = 2306837) B2306837
theorem B1537907 : Blo 1536465 1537907 := bstep (se 1 (by rfl) ⟨1153430, by rfl⟩ : syracuseStep 1537907 = 2306861) B2306861
theorem B1537923 : Blo 1536465 1537923 := bstep (se 1 (by rfl) ⟨1153442, by rfl⟩ : syracuseStep 1537923 = 2306885) B2306885
theorem B1537939 : Blo 1536465 1537939 := bstep (se 1 (by rfl) ⟨1153454, by rfl⟩ : syracuseStep 1537939 = 2306909) B2306909
theorem B1537955 : Blo 1536465 1537955 := bstep (se 1 (by rfl) ⟨1153466, by rfl⟩ : syracuseStep 1537955 = 2306933) B2306933
theorem B1537971 : Blo 1536465 1537971 := bstep (se 1 (by rfl) ⟨1153478, by rfl⟩ : syracuseStep 1537971 = 2306957) B2306957
theorem B1537987 : Blo 1536465 1537987 := bstep (se 1 (by rfl) ⟨1153490, by rfl⟩ : syracuseStep 1537987 = 2306981) B2306981
theorem B1538003 : Blo 1536465 1538003 := bstep (se 1 (by rfl) ⟨1153502, by rfl⟩ : syracuseStep 1538003 = 2307005) B2307005
theorem B1538019 : Blo 1536465 1538019 := bstep (se 1 (by rfl) ⟨1153514, by rfl⟩ : syracuseStep 1538019 = 2307029) B2307029
theorem B2594801 : Blo 1536465 2594801 := bstep (se 2 (by rfl) ⟨973050, by rfl⟩ : syracuseStep 2594801 = 1946101) B1946101
theorem B1538035 : Blo 1536465 1538035 := bstep (se 1 (by rfl) ⟨1153526, by rfl⟩ : syracuseStep 1538035 = 2307053) B2307053
theorem B1538051 : Blo 1536465 1538051 := bstep (se 1 (by rfl) ⟨1153538, by rfl⟩ : syracuseStep 1538051 = 2307077) B2307077
theorem B1538067 : Blo 1536465 1538067 := bstep (se 1 (by rfl) ⟨1153550, by rfl⟩ : syracuseStep 1538067 = 2307101) B2307101
theorem B1538083 : Blo 1536465 1538083 := bstep (se 1 (by rfl) ⟨1153562, by rfl⟩ : syracuseStep 1538083 = 2307125) B2307125
theorem B1538099 : Blo 1536465 1538099 := bstep (se 1 (by rfl) ⟨1153574, by rfl⟩ : syracuseStep 1538099 = 2307149) B2307149
theorem B1538115 : Blo 1536465 1538115 := bstep (se 1 (by rfl) ⟨1153586, by rfl⟩ : syracuseStep 1538115 = 2307173) B2307173
theorem B5838925 : Blo 1536465 5838925 := bstep (se 3 (by rfl) ⟨1094798, by rfl⟩ : syracuseStep 5838925 = 2189597) B2189597
theorem B1538131 : Blo 1536465 1538131 := bstep (se 1 (by rfl) ⟨1153598, by rfl⟩ : syracuseStep 1538131 = 2307197) B2307197
theorem B1538147 : Blo 1536465 1538147 := bstep (se 1 (by rfl) ⟨1153610, by rfl⟩ : syracuseStep 1538147 = 2307221) B2307221
theorem B5544035 : Blo 1536465 5544035 := bstep (se 1 (by rfl) ⟨4158026, by rfl⟩ : syracuseStep 5544035 = 8316053) B8316053
theorem B2594929 : Blo 1536465 2594929 := bstep (se 2 (by rfl) ⟨973098, by rfl⟩ : syracuseStep 2594929 = 1946197) B1946197
theorem B1538163 : Blo 1536465 1538163 := bstep (se 1 (by rfl) ⟨1153622, by rfl⟩ : syracuseStep 1538163 = 2307245) B2307245
theorem B2078851 : Blo 1536465 2078851 := bstep (se 1 (by rfl) ⟨1559138, by rfl⟩ : syracuseStep 2078851 = 3118277) B3118277
theorem B1538179 : Blo 1536465 1538179 := bstep (se 1 (by rfl) ⟨1153634, by rfl⟩ : syracuseStep 1538179 = 2307269) B2307269
theorem B2594963 : Blo 1536465 2594963 := bstep (se 1 (by rfl) ⟨1946222, by rfl⟩ : syracuseStep 2594963 = 3892445) B3892445
theorem B1538195 : Blo 1536465 1538195 := bstep (se 1 (by rfl) ⟨1153646, by rfl⟩ : syracuseStep 1538195 = 2307293) B2307293
theorem B1538211 : Blo 1536465 1538211 := bstep (se 1 (by rfl) ⟨1153658, by rfl⟩ : syracuseStep 1538211 = 2307317) B2307317
theorem B1538227 : Blo 1536465 1538227 := bstep (se 1 (by rfl) ⟨1153670, by rfl⟩ : syracuseStep 1538227 = 2307341) B2307341
theorem B1538243 : Blo 1536465 1538243 := bstep (se 1 (by rfl) ⟨1153682, by rfl⟩ : syracuseStep 1538243 = 2307365) B2307365
theorem B1538259 : Blo 1536465 1538259 := bstep (se 1 (by rfl) ⟨1153694, by rfl⟩ : syracuseStep 1538259 = 2307389) B2307389
theorem B1538275 : Blo 1536465 1538275 := bstep (se 1 (by rfl) ⟨1153706, by rfl⟩ : syracuseStep 1538275 = 2307413) B2307413
theorem B1538291 : Blo 1536465 1538291 := bstep (se 1 (by rfl) ⟨1153718, by rfl⟩ : syracuseStep 1538291 = 2307437) B2307437
theorem B1538307 : Blo 1536465 1538307 := bstep (se 1 (by rfl) ⟨1153730, by rfl⟩ : syracuseStep 1538307 = 2307461) B2307461
theorem B2595091 : Blo 1536465 2595091 := bstep (se 1 (by rfl) ⟨1946318, by rfl⟩ : syracuseStep 2595091 = 3892637) B3892637
theorem B1538323 : Blo 1536465 1538323 := bstep (se 1 (by rfl) ⟨1153742, by rfl⟩ : syracuseStep 1538323 = 2307485) B2307485
theorem B1538339 : Blo 1536465 1538339 := bstep (se 1 (by rfl) ⟨1153754, by rfl⟩ : syracuseStep 1538339 = 2307509) B2307509
theorem B1538355 : Blo 1536465 1538355 := bstep (se 1 (by rfl) ⟨1153766, by rfl⟩ : syracuseStep 1538355 = 2307533) B2307533
theorem B1538371 : Blo 1536465 1538371 := bstep (se 1 (by rfl) ⟨1153778, by rfl⟩ : syracuseStep 1538371 = 2307557) B2307557
theorem B1538387 : Blo 1536465 1538387 := bstep (se 1 (by rfl) ⟨1153790, by rfl⟩ : syracuseStep 1538387 = 2307581) B2307581
theorem B1538403 : Blo 1536465 1538403 := bstep (se 1 (by rfl) ⟨1153802, by rfl⟩ : syracuseStep 1538403 = 2307605) B2307605
theorem B5192045 : Blo 1536465 5192045 := bstep (se 3 (by rfl) ⟨973508, by rfl⟩ : syracuseStep 5192045 = 1947017) B1947017
theorem B21027185 : Blo 1536465 21027185 := bstep (se 2 (by rfl) ⟨7885194, by rfl⟩ : syracuseStep 21027185 = 15770389) B15770389
theorem B1538419 : Blo 1536465 1538419 := bstep (se 1 (by rfl) ⟨1153814, by rfl⟩ : syracuseStep 1538419 = 2307629) B2307629
theorem B1538435 : Blo 1536465 1538435 := bstep (se 1 (by rfl) ⟨1153826, by rfl⟩ : syracuseStep 1538435 = 2307653) B2307653
theorem B1538451 : Blo 1536465 1538451 := bstep (se 1 (by rfl) ⟨1153838, by rfl⟩ : syracuseStep 1538451 = 2307677) B2307677
theorem B2595233 : Blo 1536465 2595233 := bstep (se 2 (by rfl) ⟨973212, by rfl⟩ : syracuseStep 2595233 = 1946425) B1946425
theorem B5192099 : Blo 1536465 5192099 := bstep (se 1 (by rfl) ⟨3894074, by rfl⟩ : syracuseStep 5192099 = 7788149) B7788149
theorem B2595361 : Blo 1536465 2595361 := bstep (se 2 (by rfl) ⟨973260, by rfl⟩ : syracuseStep 2595361 = 1946521) B1946521
theorem B2595395 : Blo 1536465 2595395 := bstep (se 1 (by rfl) ⟨1946546, by rfl⟩ : syracuseStep 2595395 = 3893093) B3893093
theorem B5544611 : Blo 1536465 5544611 := bstep (se 1 (by rfl) ⟨4158458, by rfl⟩ : syracuseStep 5544611 = 8316917) B8316917
theorem B2595523 : Blo 1536465 2595523 := bstep (se 1 (by rfl) ⟨1946642, by rfl⟩ : syracuseStep 2595523 = 3893285) B3893285
theorem B11672261 : Blo 1536465 11672261 := bstep (se 4 (by rfl) ⟨1094274, by rfl⟩ : syracuseStep 11672261 = 2188549) B2188549
theorem B2595665 : Blo 1536465 2595665 := bstep (se 2 (by rfl) ⟨973374, by rfl⟩ : syracuseStep 2595665 = 1946749) B1946749
theorem B5839715 : Blo 1536465 5839715 := bstep (se 1 (by rfl) ⟨4379786, by rfl⟩ : syracuseStep 5839715 = 8759573) B8759573
theorem B3890065 : Blo 1536465 3890065 := bstep (se 2 (by rfl) ⟨1458774, by rfl⟩ : syracuseStep 3890065 = 2917549) B2917549
theorem B6839245 : Blo 1536465 6839245 := bstep (se 3 (by rfl) ⟨1282358, by rfl⟩ : syracuseStep 6839245 = 2564717) B2564717
theorem B2595793 : Blo 1536465 2595793 := bstep (se 2 (by rfl) ⟨973422, by rfl⟩ : syracuseStep 2595793 = 1946845) B1946845
theorem B11238385 : Blo 1536465 11238385 := bstep (se 2 (by rfl) ⟨4214394, by rfl⟩ : syracuseStep 11238385 = 8428789) B8428789
theorem B2595827 : Blo 1536465 2595827 := bstep (se 1 (by rfl) ⟨1946870, by rfl⟩ : syracuseStep 2595827 = 3893741) B3893741
theorem B3284003 : Blo 1536465 3284003 := bstep (se 1 (by rfl) ⟨2463002, by rfl⟩ : syracuseStep 3284003 = 4926005) B4926005
theorem B1973315 : Blo 1536465 1973315 := bstep (se 1 (by rfl) ⟨1479986, by rfl⟩ : syracuseStep 1973315 = 2959973) B2959973
theorem B2595955 : Blo 1536465 2595955 := bstep (se 1 (by rfl) ⟨1946966, by rfl⟩ : syracuseStep 2595955 = 3893933) B3893933
theorem B3890339 : Blo 1536465 3890339 := bstep (se 1 (by rfl) ⟨2917754, by rfl⟩ : syracuseStep 3890339 = 5835509) B5835509
theorem B4922545 : Blo 1536465 4922545 := bstep (se 2 (by rfl) ⟨1845954, by rfl⟩ : syracuseStep 4922545 = 3691909) B3691909
theorem B6569201 : Blo 1536465 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B11681009 : Blo 1536465 11681009 := bstep (se 2 (by rfl) ⟨4380378, by rfl⟩ : syracuseStep 11681009 = 8760757) B8760757
theorem B2596097 : Blo 1536465 2596097 := bstep (se 2 (by rfl) ⟨973536, by rfl⟩ : syracuseStep 2596097 = 1947073) B1947073
theorem B3890531 : Blo 1536465 3890531 := bstep (se 1 (by rfl) ⟨2917898, by rfl⟩ : syracuseStep 3890531 = 5835797) B5835797
theorem B1580419 : Blo 1536465 1580419 := bstep (se 1 (by rfl) ⟨1185314, by rfl⟩ : syracuseStep 1580419 = 2370629) B2370629
theorem B8756657 : Blo 1536465 8756657 := bstep (se 2 (by rfl) ⟨3283746, by rfl⟩ : syracuseStep 8756657 = 6567493) B6567493
theorem B10124785 : Blo 1536465 10124785 := bstep (se 2 (by rfl) ⟨3796794, by rfl⟩ : syracuseStep 10124785 = 7593589) B7593589
theorem B5840369 : Blo 1536465 5840369 := bstep (se 2 (by rfl) ⟨2190138, by rfl⟩ : syracuseStep 5840369 = 4380277) B4380277
theorem B9740081 : Blo 1536465 9740081 := bstep (se 2 (by rfl) ⟨3652530, by rfl⟩ : syracuseStep 9740081 = 7305061) B7305061
theorem B3284867 : Blo 1536465 3284867 := bstep (se 1 (by rfl) ⟨2463650, by rfl⟩ : syracuseStep 3284867 = 4927301) B4927301
theorem B6569869 : Blo 1536465 6569869 := bstep (se 3 (by rfl) ⟨1231850, by rfl⟩ : syracuseStep 6569869 = 2463701) B2463701
theorem B3284977 : Blo 1536465 3284977 := bstep (se 2 (by rfl) ⟨1231866, by rfl⟩ : syracuseStep 3284977 = 2463733) B2463733
theorem B2768897 : Blo 1536465 2768897 := bstep (se 2 (by rfl) ⟨1038336, by rfl⟩ : syracuseStep 2768897 = 2076673) B2076673
theorem B7888913 : Blo 1536465 7888913 := bstep (se 2 (by rfl) ⟨2958342, by rfl⟩ : syracuseStep 7888913 = 5916685) B5916685
theorem B1728535 : Blo 1536465 1728535 := bstep (se 1 (by rfl) ⟨1296401, by rfl⟩ : syracuseStep 1728535 = 2592803) B2592803
theorem B12460067 : Blo 1536465 12460067 := bstep (se 1 (by rfl) ⟨9345050, by rfl⟩ : syracuseStep 12460067 = 18690101) B18690101
theorem B4923443 : Blo 1536465 4923443 := bstep (se 1 (by rfl) ⟨3692582, by rfl⟩ : syracuseStep 4923443 = 7385165) B7385165
theorem B13131841 : Blo 1536465 13131841 := bstep (se 2 (by rfl) ⟨4924440, by rfl⟩ : syracuseStep 13131841 = 9848881) B9848881
theorem B8757341 : Blo 1536465 8757341 := bstep (se 3 (by rfl) ⟨1642001, by rfl⟩ : syracuseStep 8757341 = 3284003) B3284003
theorem B1728715 : Blo 1536465 1728715 := bstep (se 1 (by rfl) ⟨1296536, by rfl⟩ : syracuseStep 1728715 = 2593073) B2593073
theorem B3457241 : Blo 1536465 3457241 := bstep (se 2 (by rfl) ⟨1296465, by rfl⟩ : syracuseStep 3457241 = 2592931) B2592931
theorem B5996845 : Blo 1536465 5996845 := bstep (se 3 (by rfl) ⟨1124408, by rfl⟩ : syracuseStep 5996845 = 2248817) B2248817
theorem B7889197 : Blo 1536465 7889197 := bstep (se 3 (by rfl) ⟨1479224, by rfl⟩ : syracuseStep 7889197 = 2958449) B2958449
theorem B3457331 : Blo 1536465 3457331 := bstep (se 1 (by rfl) ⟨2592998, by rfl⟩ : syracuseStep 3457331 = 5185997) B5185997
theorem B1728823 : Blo 1536465 1728823 := bstep (se 1 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 1728823 = 2593235) B2593235
theorem B3457367 : Blo 1536465 3457367 := bstep (se 1 (by rfl) ⟨2593025, by rfl⟩ : syracuseStep 3457367 = 5186051) B5186051
theorem B17088869 : Blo 1536465 17088869 := bstep (se 4 (by rfl) ⟨1602081, by rfl⟩ : syracuseStep 17088869 = 3204163) B3204163
theorem B5185943 : Blo 1536465 5185943 := bstep (se 1 (by rfl) ⟨3889457, by rfl⟩ : syracuseStep 5185943 = 7778915) B7778915
theorem B3891635 : Blo 1536465 3891635 := bstep (se 1 (by rfl) ⟨2918726, by rfl⟩ : syracuseStep 3891635 = 5837453) B5837453
theorem B1753547 : Blo 1536465 1753547 := bstep (se 1 (by rfl) ⟨1315160, by rfl⟩ : syracuseStep 1753547 = 2630321) B2630321
theorem B5841355 : Blo 1536465 5841355 := bstep (se 1 (by rfl) ⟨4381016, by rfl⟩ : syracuseStep 5841355 = 8762033) B8762033
theorem B1729003 : Blo 1536465 1729003 := bstep (se 1 (by rfl) ⟨1296752, by rfl⟩ : syracuseStep 1729003 = 2593505) B2593505
theorem B3457547 : Blo 1536465 3457547 := bstep (se 1 (by rfl) ⟨2593160, by rfl⟩ : syracuseStep 3457547 = 5186321) B5186321
theorem B3457601 : Blo 1536465 3457601 := bstep (se 2 (by rfl) ⟨1296600, by rfl⟩ : syracuseStep 3457601 = 2593201) B2593201
theorem B4497995 : Blo 1536465 4497995 := bstep (se 1 (by rfl) ⟨3373496, by rfl⟩ : syracuseStep 4497995 = 6746993) B6746993
theorem B1729111 : Blo 1536465 1729111 := bstep (se 1 (by rfl) ⟨1296833, by rfl⟩ : syracuseStep 1729111 = 2593667) B2593667
theorem B11674205 : Blo 1536465 11674205 := bstep (se 3 (by rfl) ⟨2188913, by rfl⟩ : syracuseStep 11674205 = 4377827) B4377827
theorem B11076301 : Blo 1536465 11076301 := bstep (se 3 (by rfl) ⟨2076806, by rfl⟩ : syracuseStep 11076301 = 4153613) B4153613
theorem B3556055 : Blo 1536465 3556055 := bstep (se 1 (by rfl) ⟨2667041, by rfl⟩ : syracuseStep 3556055 = 5334083) B5334083
theorem B1729291 : Blo 1536465 1729291 := bstep (se 1 (by rfl) ⟨1296968, by rfl⟩ : syracuseStep 1729291 = 2593937) B2593937
theorem B3457817 : Blo 1536465 3457817 := bstep (se 2 (by rfl) ⟨1296681, by rfl⟩ : syracuseStep 3457817 = 2593363) B2593363
theorem B6570827 : Blo 1536465 6570827 := bstep (se 1 (by rfl) ⟨4928120, by rfl⟩ : syracuseStep 6570827 = 9856241) B9856241
theorem B3457907 : Blo 1536465 3457907 := bstep (se 1 (by rfl) ⟨2593430, by rfl⟩ : syracuseStep 3457907 = 5186861) B5186861
theorem B1729399 : Blo 1536465 1729399 := bstep (se 1 (by rfl) ⟨1297049, by rfl⟩ : syracuseStep 1729399 = 2594099) B2594099
theorem B3457943 : Blo 1536465 3457943 := bstep (se 1 (by rfl) ⟨2593457, by rfl⟩ : syracuseStep 3457943 = 5186915) B5186915
theorem B5186483 : Blo 1536465 5186483 := bstep (se 1 (by rfl) ⟨3889862, by rfl⟩ : syracuseStep 5186483 = 7779725) B7779725
theorem B3892171 : Blo 1536465 3892171 := bstep (se 1 (by rfl) ⟨2919128, by rfl⟩ : syracuseStep 3892171 = 5838257) B5838257
theorem B1729579 : Blo 1536465 1729579 := bstep (se 1 (by rfl) ⟨1297184, by rfl⟩ : syracuseStep 1729579 = 2594369) B2594369
theorem B2917451 : Blo 1536465 2917451 := bstep (se 1 (by rfl) ⟨2188088, by rfl⟩ : syracuseStep 2917451 = 4376177) B4376177
theorem B3458123 : Blo 1536465 3458123 := bstep (se 1 (by rfl) ⟨2593592, by rfl⟩ : syracuseStep 3458123 = 5187185) B5187185
theorem B3892313 : Blo 1536465 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B3458177 : Blo 1536465 3458177 := bstep (se 2 (by rfl) ⟨1296816, by rfl⟩ : syracuseStep 3458177 = 2593633) B2593633
theorem B1729687 : Blo 1536465 1729687 := bstep (se 1 (by rfl) ⟨1297265, by rfl⟩ : syracuseStep 1729687 = 2594531) B2594531
theorem B5186753 : Blo 1536465 5186753 := bstep (se 2 (by rfl) ⟨1945032, by rfl⟩ : syracuseStep 5186753 = 3890065) B3890065
theorem B2917633 : Blo 1536465 2917633 := bstep (se 2 (by rfl) ⟨1094112, by rfl⟩ : syracuseStep 2917633 = 2188225) B2188225
theorem B9118993 : Blo 1536465 9118993 := bstep (se 2 (by rfl) ⟨3419622, by rfl⟩ : syracuseStep 9118993 = 6839245) B6839245
theorem B14984513 : Blo 1536465 14984513 := bstep (se 2 (by rfl) ⟨5619192, by rfl⟩ : syracuseStep 14984513 = 11238385) B11238385
theorem B1729867 : Blo 1536465 1729867 := bstep (se 1 (by rfl) ⟨1297400, by rfl⟩ : syracuseStep 1729867 = 2594801) B2594801
theorem B3458393 : Blo 1536465 3458393 := bstep (se 2 (by rfl) ⟨1296897, by rfl⟩ : syracuseStep 3458393 = 2593795) B2593795
theorem B3696023 : Blo 1536465 3696023 := bstep (se 1 (by rfl) ⟨2772017, by rfl⟩ : syracuseStep 3696023 = 5544035) B5544035
theorem B9848243 : Blo 1536465 9848243 := bstep (se 1 (by rfl) ⟨7386182, by rfl⟩ : syracuseStep 9848243 = 14772365) B14772365
theorem B3458483 : Blo 1536465 3458483 := bstep (se 1 (by rfl) ⟨2593862, by rfl⟩ : syracuseStep 3458483 = 5187725) B5187725
theorem B1729975 : Blo 1536465 1729975 := bstep (se 1 (by rfl) ⟨1297481, by rfl⟩ : syracuseStep 1729975 = 2594963) B2594963
theorem B3458519 : Blo 1536465 3458519 := bstep (se 1 (by rfl) ⟨2593889, by rfl⟩ : syracuseStep 3458519 = 5187779) B5187779
theorem B8316377 : Blo 1536465 8316377 := bstep (se 2 (by rfl) ⟨3118641, by rfl⟩ : syracuseStep 8316377 = 6237283) B6237283
theorem B1558027 : Blo 1536465 1558027 := bstep (se 1 (by rfl) ⟨1168520, by rfl⟩ : syracuseStep 1558027 = 2337041) B2337041
theorem B6563393 : Blo 1536465 6563393 := bstep (se 2 (by rfl) ⟨2461272, by rfl⟩ : syracuseStep 6563393 = 4922545) B4922545
theorem B14018123 : Blo 1536465 14018123 := bstep (se 1 (by rfl) ⟨10513592, by rfl⟩ : syracuseStep 14018123 = 21027185) B21027185
theorem B5539421 : Blo 1536465 5539421 := bstep (se 3 (by rfl) ⟨1038641, by rfl⟩ : syracuseStep 5539421 = 2077283) B2077283
theorem B1730155 : Blo 1536465 1730155 := bstep (se 1 (by rfl) ⟨1297616, by rfl⟩ : syracuseStep 1730155 = 2595233) B2595233
theorem B3458699 : Blo 1536465 3458699 := bstep (se 1 (by rfl) ⟨2594024, by rfl⟩ : syracuseStep 3458699 = 5188049) B5188049
theorem B2918081 : Blo 1536465 2918081 := bstep (se 2 (by rfl) ⟨1094280, by rfl⟩ : syracuseStep 2918081 = 2188561) B2188561
theorem B3458753 : Blo 1536465 3458753 := bstep (se 2 (by rfl) ⟨1297032, by rfl⟩ : syracuseStep 3458753 = 2594065) B2594065
theorem B1730263 : Blo 1536465 1730263 := bstep (se 1 (by rfl) ⟨1297697, by rfl⟩ : syracuseStep 1730263 = 2595395) B2595395
theorem B5916377 : Blo 1536465 5916377 := bstep (se 2 (by rfl) ⟨2218641, by rfl⟩ : syracuseStep 5916377 = 4437283) B4437283
theorem B5187293 : Blo 1536465 5187293 := bstep (se 3 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 5187293 = 1945235) B1945235
theorem B5916433 : Blo 1536465 5916433 := bstep (se 2 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 5916433 = 4437325) B4437325
theorem B3696407 : Blo 1536465 3696407 := bstep (se 1 (by rfl) ⟨2772305, by rfl⟩ : syracuseStep 3696407 = 5544611) B5544611
theorem B2770777 : Blo 1536465 2770777 := bstep (se 2 (by rfl) ⟨1039041, by rfl⟩ : syracuseStep 2770777 = 2078083) B2078083
theorem B2107225 : Blo 1536465 2107225 := bstep (se 2 (by rfl) ⟨790209, by rfl⟩ : syracuseStep 2107225 = 1580419) B1580419
theorem B22177637 : Blo 1536465 22177637 := bstep (se 4 (by rfl) ⟨2079153, by rfl⟩ : syracuseStep 22177637 = 4158307) B4158307
theorem B1730443 : Blo 1536465 1730443 := bstep (se 1 (by rfl) ⟨1297832, by rfl⟩ : syracuseStep 1730443 = 2595665) B2595665
theorem B3893143 : Blo 1536465 3893143 := bstep (se 1 (by rfl) ⟨2919857, by rfl⟩ : syracuseStep 3893143 = 5839715) B5839715
theorem B3458969 : Blo 1536465 3458969 := bstep (se 2 (by rfl) ⟨1297113, by rfl⟩ : syracuseStep 3458969 = 2594227) B2594227
theorem B3459059 : Blo 1536465 3459059 := bstep (se 1 (by rfl) ⟨2594294, by rfl⟩ : syracuseStep 3459059 = 5188589) B5188589
theorem B1730551 : Blo 1536465 1730551 := bstep (se 1 (by rfl) ⟨1297913, by rfl⟩ : syracuseStep 1730551 = 2595827) B2595827
theorem B2918423 : Blo 1536465 2918423 := bstep (se 1 (by rfl) ⟨2188817, by rfl⟩ : syracuseStep 2918423 = 4377635) B4377635
theorem B3459095 : Blo 1536465 3459095 := bstep (se 1 (by rfl) ⟨2594321, by rfl⟩ : syracuseStep 3459095 = 5188643) B5188643
theorem B1730731 : Blo 1536465 1730731 := bstep (se 1 (by rfl) ⟨1298048, by rfl⟩ : syracuseStep 1730731 = 2596097) B2596097
theorem B3459275 : Blo 1536465 3459275 := bstep (se 1 (by rfl) ⟨2594456, by rfl⟩ : syracuseStep 3459275 = 5188913) B5188913
theorem B3459329 : Blo 1536465 3459329 := bstep (se 2 (by rfl) ⟨1297248, by rfl⟩ : syracuseStep 3459329 = 2594497) B2594497
theorem B19712321 : Blo 1536465 19712321 := bstep (se 2 (by rfl) ⟨7392120, by rfl⟩ : syracuseStep 19712321 = 14784241) B14784241
theorem B3893579 : Blo 1536465 3893579 := bstep (se 1 (by rfl) ⟨2920184, by rfl⟩ : syracuseStep 3893579 = 5840369) B5840369
theorem B2771339 : Blo 1536465 2771339 := bstep (se 1 (by rfl) ⟨2078504, by rfl⟩ : syracuseStep 2771339 = 4157009) B4157009
theorem B3459545 : Blo 1536465 3459545 := bstep (se 2 (by rfl) ⟨1297329, by rfl⟩ : syracuseStep 3459545 = 2594659) B2594659
theorem B4377053 : Blo 1536465 4377053 := bstep (se 3 (by rfl) ⟨820697, by rfl⟩ : syracuseStep 4377053 = 1641395) B1641395
theorem B8759825 : Blo 1536465 8759825 := bstep (se 2 (by rfl) ⟨3284934, by rfl⟩ : syracuseStep 8759825 = 6569869) B6569869
theorem B13142573 : Blo 1536465 13142573 := bstep (se 3 (by rfl) ⟨2464232, by rfl⟩ : syracuseStep 13142573 = 4928465) B4928465
theorem B3459635 : Blo 1536465 3459635 := bstep (se 1 (by rfl) ⟨2594726, by rfl⟩ : syracuseStep 3459635 = 5189453) B5189453
theorem B3459671 : Blo 1536465 3459671 := bstep (se 1 (by rfl) ⟨2594753, by rfl⟩ : syracuseStep 3459671 = 5189507) B5189507
theorem B2189911 : Blo 1536465 2189911 := bstep (se 1 (by rfl) ⟨1642433, by rfl⟩ : syracuseStep 2189911 = 3284867) B3284867
theorem B2919091 : Blo 1536465 2919091 := bstep (se 1 (by rfl) ⟨2189318, by rfl⟩ : syracuseStep 2919091 = 4378637) B4378637
theorem B3893953 : Blo 1536465 3893953 := bstep (se 2 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 3893953 = 2920465) B2920465
theorem B2771671 : Blo 1536465 2771671 := bstep (se 1 (by rfl) ⟨2078753, by rfl⟩ : syracuseStep 2771671 = 4157507) B4157507
theorem B5835523 : Blo 1536465 5835523 := bstep (se 1 (by rfl) ⟨4376642, by rfl⟩ : syracuseStep 5835523 = 8753285) B8753285
theorem B2304779 : Blo 1536465 2304779 := bstep (se 1 (by rfl) ⟨1728584, by rfl⟩ : syracuseStep 2304779 = 3457169) B3457169
theorem B3459851 : Blo 1536465 3459851 := bstep (se 1 (by rfl) ⟨2594888, by rfl⟩ : syracuseStep 3459851 = 5189777) B5189777
theorem B7785233 : Blo 1536465 7785233 := bstep (se 2 (by rfl) ⟨2919462, by rfl⟩ : syracuseStep 7785233 = 5838925) B5838925
theorem B2304791 : Blo 1536465 2304791 := bstep (se 1 (by rfl) ⟨1728593, by rfl⟩ : syracuseStep 2304791 = 3457187) B3457187
theorem B4377395 : Blo 1536465 4377395 := bstep (se 1 (by rfl) ⟨3283046, by rfl⟩ : syracuseStep 4377395 = 6566093) B6566093
theorem B3459905 : Blo 1536465 3459905 := bstep (se 2 (by rfl) ⟨1297464, by rfl⟩ : syracuseStep 3459905 = 2594929) B2594929
theorem B5188427 : Blo 1536465 5188427 := bstep (se 1 (by rfl) ⟨3891320, by rfl⟩ : syracuseStep 5188427 = 7782641) B7782641
theorem B2304857 : Blo 1536465 2304857 := bstep (se 2 (by rfl) ⟨864321, by rfl⟩ : syracuseStep 2304857 = 1728643) B1728643
theorem B2771801 : Blo 1536465 2771801 := bstep (se 2 (by rfl) ⟨1039425, by rfl⟩ : syracuseStep 2771801 = 2078851) B2078851
theorem B5262173 : Blo 1536465 5262173 := bstep (se 3 (by rfl) ⟨986657, by rfl⟩ : syracuseStep 5262173 = 1973315) B1973315
theorem B9849701 : Blo 1536465 9849701 := bstep (se 4 (by rfl) ⟨923409, by rfl⟩ : syracuseStep 9849701 = 1846819) B1846819
theorem B31558577 : Blo 1536465 31558577 := bstep (se 2 (by rfl) ⟨11834466, by rfl⟩ : syracuseStep 31558577 = 23668933) B23668933
theorem B7785395 : Blo 1536465 7785395 := bstep (se 1 (by rfl) ⟨5839046, by rfl⟩ : syracuseStep 7785395 = 11678093) B11678093
theorem B2304971 : Blo 1536465 2304971 := bstep (se 1 (by rfl) ⟨1728728, by rfl⟩ : syracuseStep 2304971 = 3457457) B3457457
theorem B2304983 : Blo 1536465 2304983 := bstep (se 1 (by rfl) ⟨1728737, by rfl⟩ : syracuseStep 2304983 = 3457475) B3457475
theorem B4156381 : Blo 1536465 4156381 := bstep (se 3 (by rfl) ⟨779321, by rfl⟩ : syracuseStep 4156381 = 1558643) B1558643
theorem B2305049 : Blo 1536465 2305049 := bstep (se 2 (by rfl) ⟨864393, by rfl⟩ : syracuseStep 2305049 = 1728787) B1728787
theorem B3460121 : Blo 1536465 3460121 := bstep (se 2 (by rfl) ⟨1297545, by rfl⟩ : syracuseStep 3460121 = 2595091) B2595091
theorem B5835827 : Blo 1536465 5835827 := bstep (se 1 (by rfl) ⟨4376870, by rfl⟩ : syracuseStep 5835827 = 8753741) B8753741
theorem B5188697 : Blo 1536465 5188697 := bstep (se 2 (by rfl) ⟨1945761, by rfl⟩ : syracuseStep 5188697 = 3891523) B3891523
theorem B2919539 : Blo 1536465 2919539 := bstep (se 1 (by rfl) ⟨2189654, by rfl⟩ : syracuseStep 2919539 = 4379309) B4379309
theorem B3460211 : Blo 1536465 3460211 := bstep (se 1 (by rfl) ⟨2595158, by rfl⟩ : syracuseStep 3460211 = 5190317) B5190317
theorem B2305163 : Blo 1536465 2305163 := bstep (se 1 (by rfl) ⟨1728872, by rfl⟩ : syracuseStep 2305163 = 3457745) B3457745
theorem B2305175 : Blo 1536465 2305175 := bstep (se 1 (by rfl) ⟨1728881, by rfl⟩ : syracuseStep 2305175 = 3457763) B3457763
theorem B3460247 : Blo 1536465 3460247 := bstep (se 1 (by rfl) ⟨2595185, by rfl⟩ : syracuseStep 3460247 = 5190371) B5190371
theorem B2919577 : Blo 1536465 2919577 := bstep (se 2 (by rfl) ⟨1094841, by rfl⟩ : syracuseStep 2919577 = 2189683) B2189683
theorem B2305241 : Blo 1536465 2305241 := bstep (se 2 (by rfl) ⟨864465, by rfl⟩ : syracuseStep 2305241 = 1728931) B1728931
theorem B17517869 : Blo 1536465 17517869 := bstep (se 3 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 17517869 = 6569201) B6569201
theorem B10513729 : Blo 1536465 10513729 := bstep (se 2 (by rfl) ⟨3942648, by rfl⟩ : syracuseStep 10513729 = 7885297) B7885297
theorem B2305355 : Blo 1536465 2305355 := bstep (se 1 (by rfl) ⟨1729016, by rfl⟩ : syracuseStep 2305355 = 3458033) B3458033
theorem B3460427 : Blo 1536465 3460427 := bstep (se 1 (by rfl) ⟨2595320, by rfl⟩ : syracuseStep 3460427 = 5190641) B5190641
theorem B2305367 : Blo 1536465 2305367 := bstep (se 1 (by rfl) ⟨1729025, by rfl⟩ : syracuseStep 2305367 = 3458051) B3458051
theorem B26283365 : Blo 1536465 26283365 := bstep (se 4 (by rfl) ⟨2464065, by rfl⟩ : syracuseStep 26283365 = 4928131) B4928131
theorem B3460481 : Blo 1536465 3460481 := bstep (se 2 (by rfl) ⟨1297680, by rfl⟩ : syracuseStep 3460481 = 2595361) B2595361
theorem B8752535 : Blo 1536465 8752535 := bstep (se 1 (by rfl) ⟨6564401, by rfl⟩ : syracuseStep 8752535 = 13128803) B13128803
theorem B2305433 : Blo 1536465 2305433 := bstep (se 2 (by rfl) ⟨864537, by rfl⟩ : syracuseStep 2305433 = 1729075) B1729075
theorem B2665931 : Blo 1536465 2665931 := bstep (se 1 (by rfl) ⟨1999448, by rfl⟩ : syracuseStep 2665931 = 3998897) B3998897
theorem B2305547 : Blo 1536465 2305547 := bstep (se 1 (by rfl) ⟨1729160, by rfl⟩ : syracuseStep 2305547 = 3458321) B3458321
theorem B2305559 : Blo 1536465 2305559 := bstep (se 1 (by rfl) ⟨1729169, by rfl⟩ : syracuseStep 2305559 = 3458339) B3458339
theorem B2305625 : Blo 1536465 2305625 := bstep (se 2 (by rfl) ⟨864609, by rfl⟩ : syracuseStep 2305625 = 1729219) B1729219
theorem B3460697 : Blo 1536465 3460697 := bstep (se 2 (by rfl) ⟨1297761, by rfl⟩ : syracuseStep 3460697 = 2595523) B2595523
theorem B2920025 : Blo 1536465 2920025 := bstep (se 2 (by rfl) ⟨1095009, by rfl⟩ : syracuseStep 2920025 = 2190019) B2190019
theorem B13307543 : Blo 1536465 13307543 := bstep (se 1 (by rfl) ⟨9980657, by rfl⟩ : syracuseStep 13307543 = 19961315) B19961315
theorem B10661555 : Blo 1536465 10661555 := bstep (se 1 (by rfl) ⟨7996166, by rfl⟩ : syracuseStep 10661555 = 15992333) B15992333
theorem B3460787 : Blo 1536465 3460787 := bstep (se 1 (by rfl) ⟨2595590, by rfl⟩ : syracuseStep 3460787 = 5191181) B5191181
theorem B5836481 : Blo 1536465 5836481 := bstep (se 2 (by rfl) ⟨2188680, by rfl⟩ : syracuseStep 5836481 = 4377361) B4377361
theorem B1945291 : Blo 1536465 1945291 := bstep (se 1 (by rfl) ⟨1458968, by rfl⟩ : syracuseStep 1945291 = 2917937) B2917937
theorem B2305739 : Blo 1536465 2305739 := bstep (se 1 (by rfl) ⟨1729304, by rfl⟩ : syracuseStep 2305739 = 3458609) B3458609
theorem B2305751 : Blo 1536465 2305751 := bstep (se 1 (by rfl) ⟨1729313, by rfl⟩ : syracuseStep 2305751 = 3458627) B3458627
theorem B3460823 : Blo 1536465 3460823 := bstep (se 1 (by rfl) ⟨2595617, by rfl⟩ : syracuseStep 3460823 = 5191235) B5191235
theorem B16617221 : Blo 1536465 16617221 := bstep (se 4 (by rfl) ⟨1557864, by rfl⟩ : syracuseStep 16617221 = 3115729) B3115729
theorem B5189399 : Blo 1536465 5189399 := bstep (se 1 (by rfl) ⟨3892049, by rfl⟩ : syracuseStep 5189399 = 7784099) B7784099
theorem B2461465 : Blo 1536465 2461465 := bstep (se 2 (by rfl) ⟨923049, by rfl⟩ : syracuseStep 2461465 = 1846099) B1846099
theorem B2305817 : Blo 1536465 2305817 := bstep (se 2 (by rfl) ⟨864681, by rfl⟩ : syracuseStep 2305817 = 1729363) B1729363
theorem B4329281 : Blo 1536465 4329281 := bstep (se 2 (by rfl) ⟨1623480, by rfl⟩ : syracuseStep 4329281 = 3246961) B3246961
theorem B2461529 : Blo 1536465 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B2305931 : Blo 1536465 2305931 := bstep (se 1 (by rfl) ⟨1729448, by rfl⟩ : syracuseStep 2305931 = 3458897) B3458897
theorem B3461003 : Blo 1536465 3461003 := bstep (se 1 (by rfl) ⟨2595752, by rfl⟩ : syracuseStep 3461003 = 5191505) B5191505
theorem B2305943 : Blo 1536465 2305943 := bstep (se 1 (by rfl) ⟨1729457, by rfl⟩ : syracuseStep 2305943 = 3458915) B3458915
theorem B3461057 : Blo 1536465 3461057 := bstep (se 2 (by rfl) ⟨1297896, by rfl⟩ : syracuseStep 3461057 = 2595793) B2595793
theorem B1945559 : Blo 1536465 1945559 := bstep (se 1 (by rfl) ⟨1459169, by rfl⟩ : syracuseStep 1945559 = 2918339) B2918339
theorem B2461657 : Blo 1536465 2461657 := bstep (se 2 (by rfl) ⟨923121, by rfl⟩ : syracuseStep 2461657 = 1846243) B1846243
theorem B21032921 : Blo 1536465 21032921 := bstep (se 2 (by rfl) ⟨7887345, by rfl⟩ : syracuseStep 21032921 = 15774691) B15774691
theorem B2306009 : Blo 1536465 2306009 := bstep (se 2 (by rfl) ⟨864753, by rfl⟩ : syracuseStep 2306009 = 1729507) B1729507
theorem B6565853 : Blo 1536465 6565853 := bstep (se 3 (by rfl) ⟨1231097, by rfl⟩ : syracuseStep 6565853 = 2462195) B2462195
theorem B2306123 : Blo 1536465 2306123 := bstep (se 1 (by rfl) ⟨1729592, by rfl⟩ : syracuseStep 2306123 = 3459185) B3459185
theorem B2306135 : Blo 1536465 2306135 := bstep (se 1 (by rfl) ⟨1729601, by rfl⟩ : syracuseStep 2306135 = 3459203) B3459203
theorem B2592857 : Blo 1536465 2592857 := bstep (se 2 (by rfl) ⟨972321, by rfl⟩ : syracuseStep 2592857 = 1944643) B1944643
theorem B2306201 : Blo 1536465 2306201 := bstep (se 2 (by rfl) ⟨864825, by rfl⟩ : syracuseStep 2306201 = 1729651) B1729651
theorem B3461273 : Blo 1536465 3461273 := bstep (se 2 (by rfl) ⟨1297977, by rfl⟩ : syracuseStep 3461273 = 2595955) B2595955
theorem B2592985 : Blo 1536465 2592985 := bstep (se 2 (by rfl) ⟨972369, by rfl⟩ : syracuseStep 2592985 = 1944739) B1944739
theorem B3461363 : Blo 1536465 3461363 := bstep (se 1 (by rfl) ⟨2596022, by rfl⟩ : syracuseStep 3461363 = 5192045) B5192045
theorem B2306315 : Blo 1536465 2306315 := bstep (se 1 (by rfl) ⟨1729736, by rfl⟩ : syracuseStep 2306315 = 3459473) B3459473
theorem B2306327 : Blo 1536465 2306327 := bstep (se 1 (by rfl) ⟨1729745, by rfl⟩ : syracuseStep 2306327 = 3459491) B3459491
theorem B3461399 : Blo 1536465 3461399 := bstep (se 1 (by rfl) ⟨2596049, by rfl⟩ : syracuseStep 3461399 = 5192099) B5192099
theorem B5189939 : Blo 1536465 5189939 := bstep (se 1 (by rfl) ⟨3892454, by rfl⟩ : syracuseStep 5189939 = 7784909) B7784909
theorem B2306393 : Blo 1536465 2306393 := bstep (se 2 (by rfl) ⟨864897, by rfl⟩ : syracuseStep 2306393 = 1729795) B1729795
theorem B2306507 : Blo 1536465 2306507 := bstep (se 1 (by rfl) ⟨1729880, by rfl⟩ : syracuseStep 2306507 = 3459761) B3459761
theorem B1536471 : Blo 1536465 1536471 := bstep (se 1 (by rfl) ⟨1152353, by rfl⟩ : syracuseStep 1536471 = 2304707) B2304707
theorem B2306519 : Blo 1536465 2306519 := bstep (se 1 (by rfl) ⟨1729889, by rfl⟩ : syracuseStep 2306519 = 3459779) B3459779
theorem B1536491 : Blo 1536465 1536491 := bstep (se 1 (by rfl) ⟨1152368, by rfl⟩ : syracuseStep 1536491 = 2304737) B2304737
theorem B1536503 : Blo 1536465 1536503 := bstep (se 1 (by rfl) ⟨1152377, by rfl⟩ : syracuseStep 1536503 = 2304755) B2304755
theorem B1536523 : Blo 1536465 1536523 := bstep (se 1 (by rfl) ⟨1152392, by rfl⟩ : syracuseStep 1536523 = 2304785) B2304785
theorem B1847819 : Blo 1536465 1847819 := bstep (se 1 (by rfl) ⟨1385864, by rfl⟩ : syracuseStep 1847819 = 2771729) B2771729
theorem B1536535 : Blo 1536465 1536535 := bstep (se 1 (by rfl) ⟨1152401, by rfl⟩ : syracuseStep 1536535 = 2304803) B2304803
theorem B2306585 : Blo 1536465 2306585 := bstep (se 2 (by rfl) ⟨864969, by rfl⟩ : syracuseStep 2306585 = 1729939) B1729939
theorem B1536555 : Blo 1536465 1536555 := bstep (se 1 (by rfl) ⟨1152416, by rfl⟩ : syracuseStep 1536555 = 2304833) B2304833
theorem B1536567 : Blo 1536465 1536567 := bstep (se 1 (by rfl) ⟨1152425, by rfl⟩ : syracuseStep 1536567 = 2304851) B2304851
theorem B12464705 : Blo 1536465 12464705 := bstep (se 2 (by rfl) ⟨4674264, by rfl⟩ : syracuseStep 12464705 = 9348529) B9348529
theorem B5190209 : Blo 1536465 5190209 := bstep (se 2 (by rfl) ⟨1946328, by rfl⟩ : syracuseStep 5190209 = 3892657) B3892657
theorem B1536587 : Blo 1536465 1536587 := bstep (se 1 (by rfl) ⟨1152440, by rfl⟩ : syracuseStep 1536587 = 2304881) B2304881
theorem B1536599 : Blo 1536465 1536599 := bstep (se 1 (by rfl) ⟨1152449, by rfl⟩ : syracuseStep 1536599 = 2304899) B2304899
theorem B1536619 : Blo 1536465 1536619 := bstep (se 1 (by rfl) ⟨1152464, by rfl⟩ : syracuseStep 1536619 = 2304929) B2304929
theorem B1536631 : Blo 1536465 1536631 := bstep (se 1 (by rfl) ⟨1152473, by rfl⟩ : syracuseStep 1536631 = 2304947) B2304947
theorem B1536651 : Blo 1536465 1536651 := bstep (se 1 (by rfl) ⟨1152488, by rfl⟩ : syracuseStep 1536651 = 2304977) B2304977
theorem B2306699 : Blo 1536465 2306699 := bstep (se 1 (by rfl) ⟨1730024, by rfl⟩ : syracuseStep 2306699 = 3460049) B3460049
theorem B1536663 : Blo 1536465 1536663 := bstep (se 1 (by rfl) ⟨1152497, by rfl⟩ : syracuseStep 1536663 = 2304995) B2304995
theorem B1946263 : Blo 1536465 1946263 := bstep (se 1 (by rfl) ⟨1459697, by rfl⟩ : syracuseStep 1946263 = 2919395) B2919395
theorem B2306711 : Blo 1536465 2306711 := bstep (se 1 (by rfl) ⟨1730033, by rfl⟩ : syracuseStep 2306711 = 3460067) B3460067
theorem B1536683 : Blo 1536465 1536683 := bstep (se 1 (by rfl) ⟨1152512, by rfl⟩ : syracuseStep 1536683 = 2305025) B2305025
theorem B1536695 : Blo 1536465 1536695 := bstep (se 1 (by rfl) ⟨1152521, by rfl⟩ : syracuseStep 1536695 = 2305043) B2305043
theorem B1536715 : Blo 1536465 1536715 := bstep (se 1 (by rfl) ⟨1152536, by rfl⟩ : syracuseStep 1536715 = 2305073) B2305073
theorem B1536727 : Blo 1536465 1536727 := bstep (se 1 (by rfl) ⟨1152545, by rfl⟩ : syracuseStep 1536727 = 2305091) B2305091
theorem B2306777 : Blo 1536465 2306777 := bstep (se 2 (by rfl) ⟨865041, by rfl⟩ : syracuseStep 2306777 = 1730083) B1730083
theorem B1536747 : Blo 1536465 1536747 := bstep (se 1 (by rfl) ⟨1152560, by rfl⟩ : syracuseStep 1536747 = 2305121) B2305121
theorem B1536759 : Blo 1536465 1536759 := bstep (se 1 (by rfl) ⟨1152569, by rfl⟩ : syracuseStep 1536759 = 2305139) B2305139
theorem B1536779 : Blo 1536465 1536779 := bstep (se 1 (by rfl) ⟨1152584, by rfl⟩ : syracuseStep 1536779 = 2305169) B2305169
theorem B1536791 : Blo 1536465 1536791 := bstep (se 1 (by rfl) ⟨1152593, by rfl⟩ : syracuseStep 1536791 = 2305187) B2305187
theorem B2593559 : Blo 1536465 2593559 := bstep (se 1 (by rfl) ⟨1945169, by rfl⟩ : syracuseStep 2593559 = 3890339) B3890339
theorem B1536811 : Blo 1536465 1536811 := bstep (se 1 (by rfl) ⟨1152608, by rfl⟩ : syracuseStep 1536811 = 2305217) B2305217
theorem B11670317 : Blo 1536465 11670317 := bstep (se 3 (by rfl) ⟨2188184, by rfl⟩ : syracuseStep 11670317 = 4376369) B4376369
theorem B1536823 : Blo 1536465 1536823 := bstep (se 1 (by rfl) ⟨1152617, by rfl⟩ : syracuseStep 1536823 = 2305235) B2305235
theorem B1536843 : Blo 1536465 1536843 := bstep (se 1 (by rfl) ⟨1152632, by rfl⟩ : syracuseStep 1536843 = 2305265) B2305265
theorem B2306891 : Blo 1536465 2306891 := bstep (se 1 (by rfl) ⟨1730168, by rfl⟩ : syracuseStep 2306891 = 3460337) B3460337
theorem B7787339 : Blo 1536465 7787339 := bstep (se 1 (by rfl) ⟨5840504, by rfl⟩ : syracuseStep 7787339 = 11681009) B11681009
theorem B1536855 : Blo 1536465 1536855 := bstep (se 1 (by rfl) ⟨1152641, by rfl⟩ : syracuseStep 1536855 = 2305283) B2305283
theorem B2306903 : Blo 1536465 2306903 := bstep (se 1 (by rfl) ⟨1730177, by rfl⟩ : syracuseStep 2306903 = 3460355) B3460355
theorem B1536875 : Blo 1536465 1536875 := bstep (se 1 (by rfl) ⟨1152656, by rfl⟩ : syracuseStep 1536875 = 2305313) B2305313
theorem B1536887 : Blo 1536465 1536887 := bstep (se 1 (by rfl) ⟨1152665, by rfl⟩ : syracuseStep 1536887 = 2305331) B2305331
theorem B1536907 : Blo 1536465 1536907 := bstep (se 1 (by rfl) ⟨1152680, by rfl⟩ : syracuseStep 1536907 = 2305361) B2305361
theorem B1536919 : Blo 1536465 1536919 := bstep (se 1 (by rfl) ⟨1152689, by rfl⟩ : syracuseStep 1536919 = 2305379) B2305379
theorem B2593687 : Blo 1536465 2593687 := bstep (se 1 (by rfl) ⟨1945265, by rfl⟩ : syracuseStep 2593687 = 3890531) B3890531
theorem B2306969 : Blo 1536465 2306969 := bstep (se 2 (by rfl) ⟨865113, by rfl⟩ : syracuseStep 2306969 = 1730227) B1730227
theorem B1536939 : Blo 1536465 1536939 := bstep (se 1 (by rfl) ⟨1152704, by rfl⟩ : syracuseStep 1536939 = 2305409) B2305409
theorem B5837741 : Blo 1536465 5837741 := bstep (se 3 (by rfl) ⟨1094576, by rfl⟩ : syracuseStep 5837741 = 2189153) B2189153
theorem B1536951 : Blo 1536465 1536951 := bstep (se 1 (by rfl) ⟨1152713, by rfl⟩ : syracuseStep 1536951 = 2305427) B2305427
theorem B1536971 : Blo 1536465 1536971 := bstep (se 1 (by rfl) ⟨1152728, by rfl⟩ : syracuseStep 1536971 = 2305457) B2305457
theorem B5837771 : Blo 1536465 5837771 := bstep (se 1 (by rfl) ⟨4378328, by rfl⟩ : syracuseStep 5837771 = 8756657) B8756657
theorem B1536983 : Blo 1536465 1536983 := bstep (se 1 (by rfl) ⟨1152737, by rfl⟩ : syracuseStep 1536983 = 2305475) B2305475
theorem B1537003 : Blo 1536465 1537003 := bstep (se 1 (by rfl) ⟨1152752, by rfl⟩ : syracuseStep 1537003 = 2305505) B2305505
theorem B1537015 : Blo 1536465 1537015 := bstep (se 1 (by rfl) ⟨1152761, by rfl⟩ : syracuseStep 1537015 = 2305523) B2305523
theorem B1537035 : Blo 1536465 1537035 := bstep (se 1 (by rfl) ⟨1152776, by rfl⟩ : syracuseStep 1537035 = 2305553) B2305553
theorem B2307083 : Blo 1536465 2307083 := bstep (se 1 (by rfl) ⟨1730312, by rfl⟩ : syracuseStep 2307083 = 3460625) B3460625
theorem B1537047 : Blo 1536465 1537047 := bstep (se 1 (by rfl) ⟨1152785, by rfl⟩ : syracuseStep 1537047 = 2305571) B2305571
theorem B2307095 : Blo 1536465 2307095 := bstep (se 1 (by rfl) ⟨1730321, by rfl⟩ : syracuseStep 2307095 = 3460643) B3460643
theorem B1537067 : Blo 1536465 1537067 := bstep (se 1 (by rfl) ⟨1152800, by rfl⟩ : syracuseStep 1537067 = 2305601) B2305601
theorem B1537079 : Blo 1536465 1537079 := bstep (se 1 (by rfl) ⟨1152809, by rfl⟩ : syracuseStep 1537079 = 2305619) B2305619
theorem B1537099 : Blo 1536465 1537099 := bstep (se 1 (by rfl) ⟨1152824, by rfl⟩ : syracuseStep 1537099 = 2305649) B2305649
theorem B1537111 : Blo 1536465 1537111 := bstep (se 1 (by rfl) ⟨1152833, by rfl⟩ : syracuseStep 1537111 = 2305667) B2305667
theorem B2307161 : Blo 1536465 2307161 := bstep (se 2 (by rfl) ⟨865185, by rfl⟩ : syracuseStep 2307161 = 1730371) B1730371
theorem B5190749 : Blo 1536465 5190749 := bstep (se 3 (by rfl) ⟨973265, by rfl⟩ : syracuseStep 5190749 = 1946531) B1946531
theorem B4379741 : Blo 1536465 4379741 := bstep (se 3 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 4379741 = 1642403) B1642403
theorem B1537131 : Blo 1536465 1537131 := bstep (se 1 (by rfl) ⟨1152848, by rfl⟩ : syracuseStep 1537131 = 2305697) B2305697
theorem B1537143 : Blo 1536465 1537143 := bstep (se 1 (by rfl) ⟨1152857, by rfl⟩ : syracuseStep 1537143 = 2305715) B2305715
theorem B1537163 : Blo 1536465 1537163 := bstep (se 1 (by rfl) ⟨1152872, by rfl⟩ : syracuseStep 1537163 = 2305745) B2305745
theorem B1537175 : Blo 1536465 1537175 := bstep (se 1 (by rfl) ⟨1152881, by rfl⟩ : syracuseStep 1537175 = 2305763) B2305763
theorem B1537195 : Blo 1536465 1537195 := bstep (se 1 (by rfl) ⟨1152896, by rfl⟩ : syracuseStep 1537195 = 2305793) B2305793
theorem B5256371 : Blo 1536465 5256371 := bstep (se 1 (by rfl) ⟨3942278, by rfl⟩ : syracuseStep 5256371 = 7884557) B7884557
theorem B119821493 : Blo 1536465 119821493 := bstep (se 5 (by rfl) ⟨5616632, by rfl⟩ : syracuseStep 119821493 = 11233265) B11233265
theorem B1537207 : Blo 1536465 1537207 := bstep (se 1 (by rfl) ⟨1152905, by rfl⟩ : syracuseStep 1537207 = 2305811) B2305811
theorem B1537227 : Blo 1536465 1537227 := bstep (se 1 (by rfl) ⟨1152920, by rfl⟩ : syracuseStep 1537227 = 2305841) B2305841
theorem B6493387 : Blo 1536465 6493387 := bstep (se 1 (by rfl) ⟨4870040, by rfl⟩ : syracuseStep 6493387 = 9740081) B9740081
theorem B2307275 : Blo 1536465 2307275 := bstep (se 1 (by rfl) ⟨1730456, by rfl⟩ : syracuseStep 2307275 = 3460913) B3460913
theorem B1537239 : Blo 1536465 1537239 := bstep (se 1 (by rfl) ⟨1152929, by rfl⟩ : syracuseStep 1537239 = 2305859) B2305859
theorem B2307287 : Blo 1536465 2307287 := bstep (se 1 (by rfl) ⟨1730465, by rfl⟩ : syracuseStep 2307287 = 3460931) B3460931
theorem B1537259 : Blo 1536465 1537259 := bstep (se 1 (by rfl) ⟨1152944, by rfl⟩ : syracuseStep 1537259 = 2305889) B2305889
theorem B1537271 : Blo 1536465 1537271 := bstep (se 1 (by rfl) ⟨1152953, by rfl⟩ : syracuseStep 1537271 = 2305907) B2305907
theorem B24925445 : Blo 1536465 24925445 := bstep (se 4 (by rfl) ⟨2336760, by rfl⟩ : syracuseStep 24925445 = 4673521) B4673521
theorem B1537291 : Blo 1536465 1537291 := bstep (se 1 (by rfl) ⟨1152968, by rfl⟩ : syracuseStep 1537291 = 2305937) B2305937
theorem B1537303 : Blo 1536465 1537303 := bstep (se 1 (by rfl) ⟨1152977, by rfl⟩ : syracuseStep 1537303 = 2305955) B2305955
theorem B2077975 : Blo 1536465 2077975 := bstep (se 1 (by rfl) ⟨1558481, by rfl⟩ : syracuseStep 2077975 = 3116963) B3116963
theorem B2307353 : Blo 1536465 2307353 := bstep (se 2 (by rfl) ⟨865257, by rfl⟩ : syracuseStep 2307353 = 1730515) B1730515
theorem B1537323 : Blo 1536465 1537323 := bstep (se 1 (by rfl) ⟨1152992, by rfl⟩ : syracuseStep 1537323 = 2305985) B2305985
theorem B9352493 : Blo 1536465 9352493 := bstep (se 3 (by rfl) ⟨1753592, by rfl⟩ : syracuseStep 9352493 = 3507185) B3507185
theorem B1537335 : Blo 1536465 1537335 := bstep (se 1 (by rfl) ⟨1153001, by rfl⟩ : syracuseStep 1537335 = 2306003) B2306003
theorem B4379969 : Blo 1536465 4379969 := bstep (se 2 (by rfl) ⟨1642488, by rfl⟩ : syracuseStep 4379969 = 3284977) B3284977
theorem B1537355 : Blo 1536465 1537355 := bstep (se 1 (by rfl) ⟨1153016, by rfl⟩ : syracuseStep 1537355 = 2306033) B2306033
theorem B1537367 : Blo 1536465 1537367 := bstep (se 1 (by rfl) ⟨1153025, by rfl⟩ : syracuseStep 1537367 = 2306051) B2306051
theorem B1537387 : Blo 1536465 1537387 := bstep (se 1 (by rfl) ⟨1153040, by rfl⟩ : syracuseStep 1537387 = 2306081) B2306081
theorem B1537399 : Blo 1536465 1537399 := bstep (se 1 (by rfl) ⟨1153049, by rfl⟩ : syracuseStep 1537399 = 2306099) B2306099
theorem B1537419 : Blo 1536465 1537419 := bstep (se 1 (by rfl) ⟨1153064, by rfl⟩ : syracuseStep 1537419 = 2306129) B2306129
theorem B2307467 : Blo 1536465 2307467 := bstep (se 1 (by rfl) ⟨1730600, by rfl⟩ : syracuseStep 2307467 = 3461201) B3461201
theorem B1537431 : Blo 1536465 1537431 := bstep (se 1 (by rfl) ⟨1153073, by rfl⟩ : syracuseStep 1537431 = 2306147) B2306147
theorem B2307479 : Blo 1536465 2307479 := bstep (se 1 (by rfl) ⟨1730609, by rfl⟩ : syracuseStep 2307479 = 3461219) B3461219
theorem B1537451 : Blo 1536465 1537451 := bstep (se 1 (by rfl) ⟨1153088, by rfl⟩ : syracuseStep 1537451 = 2306177) B2306177
theorem B7386547 : Blo 1536465 7386547 := bstep (se 1 (by rfl) ⟨5539910, by rfl⟩ : syracuseStep 7386547 = 11079821) B11079821
theorem B1537463 : Blo 1536465 1537463 := bstep (se 1 (by rfl) ⟨1153097, by rfl⟩ : syracuseStep 1537463 = 2306195) B2306195
theorem B1537483 : Blo 1536465 1537483 := bstep (se 1 (by rfl) ⟨1153112, by rfl⟩ : syracuseStep 1537483 = 2306225) B2306225
theorem B1537495 : Blo 1536465 1537495 := bstep (se 1 (by rfl) ⟨1153121, by rfl⟩ : syracuseStep 1537495 = 2306243) B2306243
theorem B2307545 : Blo 1536465 2307545 := bstep (se 2 (by rfl) ⟨865329, by rfl⟩ : syracuseStep 2307545 = 1730659) B1730659
theorem B1537515 : Blo 1536465 1537515 := bstep (se 1 (by rfl) ⟨1153136, by rfl⟩ : syracuseStep 1537515 = 2306273) B2306273
theorem B1537527 : Blo 1536465 1537527 := bstep (se 1 (by rfl) ⟨1153145, by rfl⟩ : syracuseStep 1537527 = 2306291) B2306291
theorem B2594315 : Blo 1536465 2594315 := bstep (se 1 (by rfl) ⟨1945736, by rfl⟩ : syracuseStep 2594315 = 3891473) B3891473
theorem B1537547 : Blo 1536465 1537547 := bstep (se 1 (by rfl) ⟨1153160, by rfl⟩ : syracuseStep 1537547 = 2306321) B2306321
theorem B1537559 : Blo 1536465 1537559 := bstep (se 1 (by rfl) ⟨1153169, by rfl⟩ : syracuseStep 1537559 = 2306339) B2306339
theorem B1537579 : Blo 1536465 1537579 := bstep (se 1 (by rfl) ⟨1153184, by rfl⟩ : syracuseStep 1537579 = 2306369) B2306369
theorem B1537591 : Blo 1536465 1537591 := bstep (se 1 (by rfl) ⟨1153193, by rfl⟩ : syracuseStep 1537591 = 2306387) B2306387
theorem B1537611 : Blo 1536465 1537611 := bstep (se 1 (by rfl) ⟨1153208, by rfl⟩ : syracuseStep 1537611 = 2306417) B2306417
theorem B2307659 : Blo 1536465 2307659 := bstep (se 1 (by rfl) ⟨1730744, by rfl⟩ : syracuseStep 2307659 = 3461489) B3461489
theorem B1537623 : Blo 1536465 1537623 := bstep (se 1 (by rfl) ⟨1153217, by rfl⟩ : syracuseStep 1537623 = 2306435) B2306435
theorem B2307671 : Blo 1536465 2307671 := bstep (se 1 (by rfl) ⟨1730753, by rfl⟩ : syracuseStep 2307671 = 3461507) B3461507
theorem B5838425 : Blo 1536465 5838425 := bstep (se 2 (by rfl) ⟨2189409, by rfl⟩ : syracuseStep 5838425 = 4378819) B4378819
theorem B1537643 : Blo 1536465 1537643 := bstep (se 1 (by rfl) ⟨1153232, by rfl⟩ : syracuseStep 1537643 = 2306465) B2306465
theorem B1537655 : Blo 1536465 1537655 := bstep (se 1 (by rfl) ⟨1153241, by rfl⟩ : syracuseStep 1537655 = 2306483) B2306483
theorem B2594443 : Blo 1536465 2594443 := bstep (se 1 (by rfl) ⟨1945832, by rfl⟩ : syracuseStep 2594443 = 3891665) B3891665
theorem B1537675 : Blo 1536465 1537675 := bstep (se 1 (by rfl) ⟨1153256, by rfl⟩ : syracuseStep 1537675 = 2306513) B2306513
theorem B1537687 : Blo 1536465 1537687 := bstep (se 1 (by rfl) ⟨1153265, by rfl⟩ : syracuseStep 1537687 = 2306531) B2306531
theorem B4380311 : Blo 1536465 4380311 := bstep (se 1 (by rfl) ⟨3285233, by rfl⟩ : syracuseStep 4380311 = 6570467) B6570467
theorem B1537707 : Blo 1536465 1537707 := bstep (se 1 (by rfl) ⟨1153280, by rfl⟩ : syracuseStep 1537707 = 2306561) B2306561
theorem B1537719 : Blo 1536465 1537719 := bstep (se 1 (by rfl) ⟨1153289, by rfl⟩ : syracuseStep 1537719 = 2306579) B2306579
theorem B1537739 : Blo 1536465 1537739 := bstep (se 1 (by rfl) ⟨1153304, by rfl⟩ : syracuseStep 1537739 = 2306609) B2306609
theorem B1537751 : Blo 1536465 1537751 := bstep (se 1 (by rfl) ⟨1153313, by rfl⟩ : syracuseStep 1537751 = 2306627) B2306627
theorem B1537771 : Blo 1536465 1537771 := bstep (se 1 (by rfl) ⟨1153328, by rfl⟩ : syracuseStep 1537771 = 2306657) B2306657
theorem B1537783 : Blo 1536465 1537783 := bstep (se 1 (by rfl) ⟨1153337, by rfl⟩ : syracuseStep 1537783 = 2306675) B2306675
theorem B1537803 : Blo 1536465 1537803 := bstep (se 1 (by rfl) ⟨1153352, by rfl⟩ : syracuseStep 1537803 = 2306705) B2306705
theorem B1537815 : Blo 1536465 1537815 := bstep (se 1 (by rfl) ⟨1153361, by rfl⟩ : syracuseStep 1537815 = 2306723) B2306723
theorem B2594585 : Blo 1536465 2594585 := bstep (se 2 (by rfl) ⟨972969, by rfl⟩ : syracuseStep 2594585 = 1945939) B1945939
theorem B1537835 : Blo 1536465 1537835 := bstep (se 1 (by rfl) ⟨1153376, by rfl⟩ : syracuseStep 1537835 = 2306753) B2306753
theorem B1537847 : Blo 1536465 1537847 := bstep (se 1 (by rfl) ⟨1153385, by rfl⟩ : syracuseStep 1537847 = 2306771) B2306771
theorem B7485259 : Blo 1536465 7485259 := bstep (se 1 (by rfl) ⟨5613944, by rfl⟩ : syracuseStep 7485259 = 11227889) B11227889
theorem B1537867 : Blo 1536465 1537867 := bstep (se 1 (by rfl) ⟨1153400, by rfl⟩ : syracuseStep 1537867 = 2306801) B2306801
theorem B1537879 : Blo 1536465 1537879 := bstep (se 1 (by rfl) ⟨1153409, by rfl⟩ : syracuseStep 1537879 = 2306819) B2306819
theorem B1537899 : Blo 1536465 1537899 := bstep (se 1 (by rfl) ⟨1153424, by rfl⟩ : syracuseStep 1537899 = 2306849) B2306849
theorem B1537911 : Blo 1536465 1537911 := bstep (se 1 (by rfl) ⟨1153433, by rfl⟩ : syracuseStep 1537911 = 2306867) B2306867
theorem B1537931 : Blo 1536465 1537931 := bstep (se 1 (by rfl) ⟨1153448, by rfl⟩ : syracuseStep 1537931 = 2306897) B2306897
theorem B5838743 : Blo 1536465 5838743 := bstep (se 1 (by rfl) ⟨4379057, by rfl⟩ : syracuseStep 5838743 = 8758115) B8758115
theorem B1537943 : Blo 1536465 1537943 := bstep (se 1 (by rfl) ⟨1153457, by rfl⟩ : syracuseStep 1537943 = 2306915) B2306915
theorem B2594713 : Blo 1536465 2594713 := bstep (se 2 (by rfl) ⟨973017, by rfl⟩ : syracuseStep 2594713 = 1946035) B1946035
theorem B1537963 : Blo 1536465 1537963 := bstep (se 1 (by rfl) ⟨1153472, by rfl⟩ : syracuseStep 1537963 = 2306945) B2306945
theorem B5920685 : Blo 1536465 5920685 := bstep (se 3 (by rfl) ⟨1110128, by rfl⟩ : syracuseStep 5920685 = 2220257) B2220257
theorem B59127731 : Blo 1536465 59127731 := bstep (se 1 (by rfl) ⟨44345798, by rfl⟩ : syracuseStep 59127731 = 88691597) B88691597
theorem B1537975 : Blo 1536465 1537975 := bstep (se 1 (by rfl) ⟨1153481, by rfl⟩ : syracuseStep 1537975 = 2306963) B2306963
theorem B1537995 : Blo 1536465 1537995 := bstep (se 1 (by rfl) ⟨1153496, by rfl⟩ : syracuseStep 1537995 = 2306993) B2306993
theorem B1538007 : Blo 1536465 1538007 := bstep (se 1 (by rfl) ⟨1153505, by rfl⟩ : syracuseStep 1538007 = 2307011) B2307011
theorem B1538027 : Blo 1536465 1538027 := bstep (se 1 (by rfl) ⟨1153520, by rfl⟩ : syracuseStep 1538027 = 2307041) B2307041
theorem B1538039 : Blo 1536465 1538039 := bstep (se 1 (by rfl) ⟨1153529, by rfl⟩ : syracuseStep 1538039 = 2307059) B2307059
theorem B1538059 : Blo 1536465 1538059 := bstep (se 1 (by rfl) ⟨1153544, by rfl⟩ : syracuseStep 1538059 = 2307089) B2307089
theorem B1538071 : Blo 1536465 1538071 := bstep (se 1 (by rfl) ⟨1153553, by rfl⟩ : syracuseStep 1538071 = 2307107) B2307107
theorem B1538091 : Blo 1536465 1538091 := bstep (se 1 (by rfl) ⟨1153568, by rfl⟩ : syracuseStep 1538091 = 2307137) B2307137
theorem B1538103 : Blo 1536465 1538103 := bstep (se 1 (by rfl) ⟨1153577, by rfl⟩ : syracuseStep 1538103 = 2307155) B2307155
theorem B1538123 : Blo 1536465 1538123 := bstep (se 1 (by rfl) ⟨1153592, by rfl⟩ : syracuseStep 1538123 = 2307185) B2307185
theorem B1538135 : Blo 1536465 1538135 := bstep (se 1 (by rfl) ⟨1153601, by rfl⟩ : syracuseStep 1538135 = 2307203) B2307203
theorem B1538155 : Blo 1536465 1538155 := bstep (se 1 (by rfl) ⟨1153616, by rfl⟩ : syracuseStep 1538155 = 2307233) B2307233
theorem B1538167 : Blo 1536465 1538167 := bstep (se 1 (by rfl) ⟨1153625, by rfl⟩ : syracuseStep 1538167 = 2307251) B2307251
theorem B1538187 : Blo 1536465 1538187 := bstep (se 1 (by rfl) ⟨1153640, by rfl⟩ : syracuseStep 1538187 = 2307281) B2307281
theorem B1538199 : Blo 1536465 1538199 := bstep (se 1 (by rfl) ⟨1153649, by rfl⟩ : syracuseStep 1538199 = 2307299) B2307299
theorem B3283097 : Blo 1536465 3283097 := bstep (se 2 (by rfl) ⟨1231161, by rfl⟩ : syracuseStep 3283097 = 2462323) B2462323
theorem B1538219 : Blo 1536465 1538219 := bstep (se 1 (by rfl) ⟨1153664, by rfl⟩ : syracuseStep 1538219 = 2307329) B2307329
theorem B1538231 : Blo 1536465 1538231 := bstep (se 1 (by rfl) ⟨1153673, by rfl⟩ : syracuseStep 1538231 = 2307347) B2307347
theorem B1538251 : Blo 1536465 1538251 := bstep (se 1 (by rfl) ⟨1153688, by rfl⟩ : syracuseStep 1538251 = 2307377) B2307377
theorem B5191883 : Blo 1536465 5191883 := bstep (se 1 (by rfl) ⟨3893912, by rfl⟩ : syracuseStep 5191883 = 7787825) B7787825
theorem B1538263 : Blo 1536465 1538263 := bstep (se 1 (by rfl) ⟨1153697, by rfl⟩ : syracuseStep 1538263 = 2307395) B2307395
theorem B1538283 : Blo 1536465 1538283 := bstep (se 1 (by rfl) ⟨1153712, by rfl⟩ : syracuseStep 1538283 = 2307425) B2307425
theorem B1538295 : Blo 1536465 1538295 := bstep (se 1 (by rfl) ⟨1153721, by rfl⟩ : syracuseStep 1538295 = 2307443) B2307443
theorem B1538315 : Blo 1536465 1538315 := bstep (se 1 (by rfl) ⟨1153736, by rfl⟩ : syracuseStep 1538315 = 2307473) B2307473
theorem B5921041 : Blo 1536465 5921041 := bstep (se 2 (by rfl) ⟨2220390, by rfl⟩ : syracuseStep 5921041 = 4440781) B4440781
theorem B1538327 : Blo 1536465 1538327 := bstep (se 1 (by rfl) ⟨1153745, by rfl⟩ : syracuseStep 1538327 = 2307491) B2307491
theorem B1538347 : Blo 1536465 1538347 := bstep (se 1 (by rfl) ⟨1153760, by rfl⟩ : syracuseStep 1538347 = 2307521) B2307521
theorem B1538359 : Blo 1536465 1538359 := bstep (se 1 (by rfl) ⟨1153769, by rfl⟩ : syracuseStep 1538359 = 2307539) B2307539
theorem B8870219 : Blo 1536465 8870219 := bstep (se 1 (by rfl) ⟨6652664, by rfl⟩ : syracuseStep 8870219 = 13305329) B13305329
theorem B1538379 : Blo 1536465 1538379 := bstep (se 1 (by rfl) ⟨1153784, by rfl⟩ : syracuseStep 1538379 = 2307569) B2307569
theorem B1538391 : Blo 1536465 1538391 := bstep (se 1 (by rfl) ⟨1153793, by rfl⟩ : syracuseStep 1538391 = 2307587) B2307587
theorem B1538411 : Blo 1536465 1538411 := bstep (se 1 (by rfl) ⟨1153808, by rfl⟩ : syracuseStep 1538411 = 2307617) B2307617
theorem B1538423 : Blo 1536465 1538423 := bstep (se 1 (by rfl) ⟨1153817, by rfl⟩ : syracuseStep 1538423 = 2307635) B2307635
theorem B1538443 : Blo 1536465 1538443 := bstep (se 1 (by rfl) ⟨1153832, by rfl⟩ : syracuseStep 1538443 = 2307665) B2307665
theorem B3889559 : Blo 1536465 3889559 := bstep (se 1 (by rfl) ⟨2917169, by rfl⟩ : syracuseStep 3889559 = 5834339) B5834339
theorem B1538455 : Blo 1536465 1538455 := bstep (se 1 (by rfl) ⟨1153841, by rfl⟩ : syracuseStep 1538455 = 2307683) B2307683
theorem B18692531 : Blo 1536465 18692531 := bstep (se 1 (by rfl) ⟨14019398, by rfl⟩ : syracuseStep 18692531 = 28038797) B28038797
theorem B2595287 : Blo 1536465 2595287 := bstep (se 1 (by rfl) ⟨1946465, by rfl⟩ : syracuseStep 2595287 = 3892931) B3892931
theorem B13130201 : Blo 1536465 13130201 := bstep (se 2 (by rfl) ⟨4923825, by rfl⟩ : syracuseStep 13130201 = 9847651) B9847651
theorem B5192153 : Blo 1536465 5192153 := bstep (se 2 (by rfl) ⟨1947057, by rfl⟩ : syracuseStep 5192153 = 3894115) B3894115
theorem B6568451 : Blo 1536465 6568451 := bstep (se 1 (by rfl) ⟨4926338, by rfl⟩ : syracuseStep 6568451 = 9852677) B9852677
theorem B14768675 : Blo 1536465 14768675 := bstep (se 1 (by rfl) ⟨11076506, by rfl⟩ : syracuseStep 14768675 = 22153013) B22153013
theorem B26270243 : Blo 1536465 26270243 := bstep (se 1 (by rfl) ⟨19702682, by rfl⟩ : syracuseStep 26270243 = 39405365) B39405365
theorem B3283507 : Blo 1536465 3283507 := bstep (se 1 (by rfl) ⟨2462630, by rfl⟩ : syracuseStep 3283507 = 4925261) B4925261
theorem B5839411 : Blo 1536465 5839411 := bstep (se 1 (by rfl) ⟨4379558, by rfl⟩ : syracuseStep 5839411 = 8759117) B8759117
theorem B2595415 : Blo 1536465 2595415 := bstep (se 1 (by rfl) ⟨1946561, by rfl⟩ : syracuseStep 2595415 = 3893123) B3893123
theorem B11082419 : Blo 1536465 11082419 := bstep (se 1 (by rfl) ⟨8311814, by rfl⟩ : syracuseStep 11082419 = 16623629) B16623629
theorem B4438849 : Blo 1536465 4438849 := bstep (se 2 (by rfl) ⟨1664568, by rfl⟩ : syracuseStep 4438849 = 3329137) B3329137
theorem B3283841 : Blo 1536465 3283841 := bstep (se 2 (by rfl) ⟨1231440, by rfl⟩ : syracuseStep 3283841 = 2462881) B2462881
theorem B4922315 : Blo 1536465 4922315 := bstep (se 1 (by rfl) ⟨3691736, by rfl⟩ : syracuseStep 4922315 = 7383473) B7383473
theorem B13138949 : Blo 1536465 13138949 := bstep (se 4 (by rfl) ⟨1231776, by rfl⟩ : syracuseStep 13138949 = 2463553) B2463553
theorem B3890227 : Blo 1536465 3890227 := bstep (se 1 (by rfl) ⟨2917670, by rfl⟩ : syracuseStep 3890227 = 5835341) B5835341
theorem B7781507 : Blo 1536465 7781507 := bstep (se 1 (by rfl) ⟨5836130, by rfl⟩ : syracuseStep 7781507 = 11672261) B11672261
theorem B3890369 : Blo 1536465 3890369 := bstep (se 2 (by rfl) ⟨1458888, by rfl⟩ : syracuseStep 3890369 = 2917777) B2917777
theorem B2596043 : Blo 1536465 2596043 := bstep (se 1 (by rfl) ⟨1947032, by rfl⟩ : syracuseStep 2596043 = 3894065) B3894065
theorem B13499713 : Blo 1536465 13499713 := bstep (se 2 (by rfl) ⟨5062392, by rfl⟩ : syracuseStep 13499713 = 10124785) B10124785
theorem B4922903 : Blo 1536465 4922903 := bstep (se 1 (by rfl) ⟨3692177, by rfl⟩ : syracuseStep 4922903 = 7384355) B7384355
theorem B3284567 : Blo 1536465 3284567 := bstep (se 1 (by rfl) ⟨2463425, by rfl⟩ : syracuseStep 3284567 = 4926851) B4926851
theorem B25263797 : Blo 1536465 25263797 := bstep (se 5 (by rfl) ⟨1184240, by rfl⟩ : syracuseStep 25263797 = 2368481) B2368481
theorem B5840657 : Blo 1536465 5840657 := bstep (se 2 (by rfl) ⟨2190246, by rfl⟩ : syracuseStep 5840657 = 4380493) B4380493
theorem B4153267 : Blo 1536465 4153267 := bstep (se 1 (by rfl) ⟨3114950, by rfl⟩ : syracuseStep 4153267 = 6229901) B6229901
theorem B5259275 : Blo 1536465 5259275 := bstep (se 1 (by rfl) ⟨3944456, by rfl⟩ : syracuseStep 5259275 = 7888913) B7888913
theorem B8306711 : Blo 1536465 8306711 := bstep (se 1 (by rfl) ⟨6230033, by rfl⟩ : syracuseStep 8306711 = 12460067) B12460067
theorem B1728571 : Blo 1536465 1728571 := bstep (se 1 (by rfl) ⟨1296428, by rfl⟩ : syracuseStep 1728571 = 2592857) B2592857
theorem B3457295 : Blo 1536465 3457295 := bstep (se 1 (by rfl) ⟨2592971, by rfl⟩ : syracuseStep 3457295 = 5185943) B5185943
theorem B3457313 : Blo 1536465 3457313 := bstep (se 2 (by rfl) ⟨1296492, by rfl⟩ : syracuseStep 3457313 = 2592985) B2592985
theorem B2998663 : Blo 1536465 2998663 := bstep (se 1 (by rfl) ⟨2248997, by rfl⟩ : syracuseStep 2998663 = 4497995) B4497995
theorem B7995793 : Blo 1536465 7995793 := bstep (se 2 (by rfl) ⟨2998422, by rfl⟩ : syracuseStep 7995793 = 5996845) B5996845
theorem B7782803 : Blo 1536465 7782803 := bstep (se 1 (by rfl) ⟨5837102, by rfl⟩ : syracuseStep 7782803 = 11674205) B11674205
theorem B10518929 : Blo 1536465 10518929 := bstep (se 2 (by rfl) ⟨3944598, by rfl⟩ : syracuseStep 10518929 = 7889197) B7889197
theorem B14016989 : Blo 1536465 14016989 := bstep (se 3 (by rfl) ⟨2628185, by rfl⟩ : syracuseStep 14016989 = 5256371) B5256371
theorem B1729039 : Blo 1536465 1729039 := bstep (se 1 (by rfl) ⟨1296779, by rfl⟩ : syracuseStep 1729039 = 2593559) B2593559
theorem B3891827 : Blo 1536465 3891827 := bstep (se 1 (by rfl) ⟨2918870, by rfl⟩ : syracuseStep 3891827 = 5837741) B5837741
theorem B3457655 : Blo 1536465 3457655 := bstep (se 1 (by rfl) ⟨2593241, by rfl⟩ : syracuseStep 3457655 = 5186483) B5186483
theorem B3891847 : Blo 1536465 3891847 := bstep (se 1 (by rfl) ⟨2918885, by rfl⟩ : syracuseStep 3891847 = 5837771) B5837771
theorem B79880995 : Blo 1536465 79880995 := bstep (se 1 (by rfl) ⟨59910746, by rfl⟩ : syracuseStep 79880995 = 119821493) B119821493
theorem B3457835 : Blo 1536465 3457835 := bstep (se 1 (by rfl) ⟨2593376, by rfl⟩ : syracuseStep 3457835 = 5186753) B5186753
theorem B6234995 : Blo 1536465 6234995 := bstep (se 1 (by rfl) ⟨4676246, by rfl⟩ : syracuseStep 6234995 = 9352493) B9352493
theorem B3892121 : Blo 1536465 3892121 := bstep (se 2 (by rfl) ⟨1459545, by rfl⟩ : syracuseStep 3892121 = 2919091) B2919091
theorem B3695561 : Blo 1536465 3695561 := bstep (se 2 (by rfl) ⟨1385835, by rfl⟩ : syracuseStep 3695561 = 2771671) B2771671
theorem B1729543 : Blo 1536465 1729543 := bstep (se 1 (by rfl) ⟨1297157, by rfl⟩ : syracuseStep 1729543 = 2594315) B2594315
theorem B4375595 : Blo 1536465 4375595 := bstep (se 1 (by rfl) ⟨3281696, by rfl⟩ : syracuseStep 4375595 = 6563393) B6563393
theorem B3892283 : Blo 1536465 3892283 := bstep (se 1 (by rfl) ⟨2919212, by rfl⟩ : syracuseStep 3892283 = 5838425) B5838425
theorem B3458195 : Blo 1536465 3458195 := bstep (se 1 (by rfl) ⟨2593646, by rfl⟩ : syracuseStep 3458195 = 5187293) B5187293
theorem B1729723 : Blo 1536465 1729723 := bstep (se 1 (by rfl) ⟨1297292, by rfl⟩ : syracuseStep 1729723 = 2594585) B2594585
theorem B3458249 : Blo 1536465 3458249 := bstep (se 2 (by rfl) ⟨1296843, by rfl⟩ : syracuseStep 3458249 = 2593687) B2593687
theorem B3892495 : Blo 1536465 3892495 := bstep (se 1 (by rfl) ⟨2919371, by rfl⟩ : syracuseStep 3892495 = 5838743) B5838743
theorem B5186969 : Blo 1536465 5186969 := bstep (se 2 (by rfl) ⟨1945113, by rfl⟩ : syracuseStep 5186969 = 3890227) B3890227
theorem B37381661 : Blo 1536465 37381661 := bstep (se 3 (by rfl) ⟨7009061, by rfl⟩ : syracuseStep 37381661 = 14018123) B14018123
theorem B3892769 : Blo 1536465 3892769 := bstep (se 2 (by rfl) ⟨1459788, by rfl⟩ : syracuseStep 3892769 = 2919577) B2919577
theorem B13141547 : Blo 1536465 13141547 := bstep (se 1 (by rfl) ⟨9856160, by rfl⟩ : syracuseStep 13141547 = 19712321) B19712321
theorem B12461687 : Blo 1536465 12461687 := bstep (se 1 (by rfl) ⟨9346265, by rfl⟩ : syracuseStep 12461687 = 18692531) B18692531
theorem B1730191 : Blo 1536465 1730191 := bstep (se 1 (by rfl) ⟨1297643, by rfl⟩ : syracuseStep 1730191 = 2595287) B2595287
theorem B2918035 : Blo 1536465 2918035 := bstep (se 1 (by rfl) ⟨2188526, by rfl⟩ : syracuseStep 2918035 = 4377053) B4377053
theorem B12158657 : Blo 1536465 12158657 := bstep (se 2 (by rfl) ⟨4559496, by rfl⟩ : syracuseStep 12158657 = 9118993) B9118993
theorem B2770633 : Blo 1536465 2770633 := bstep (se 2 (by rfl) ⟨1038987, by rfl⟩ : syracuseStep 2770633 = 2077975) B2077975
theorem B14018305 : Blo 1536465 14018305 := bstep (se 2 (by rfl) ⟨5256864, by rfl⟩ : syracuseStep 14018305 = 10513729) B10513729
theorem B17999617 : Blo 1536465 17999617 := bstep (se 2 (by rfl) ⟨6749856, by rfl⟩ : syracuseStep 17999617 = 13499713) B13499713
theorem B2918263 : Blo 1536465 2918263 := bstep (se 1 (by rfl) ⟨2188697, by rfl⟩ : syracuseStep 2918263 = 4377395) B4377395
theorem B3458951 : Blo 1536465 3458951 := bstep (se 1 (by rfl) ⟨2594213, by rfl⟩ : syracuseStep 3458951 = 5188427) B5188427
theorem B3508115 : Blo 1536465 3508115 := bstep (se 1 (by rfl) ⟨2631086, by rfl⟩ : syracuseStep 3508115 = 5262173) B5262173
theorem B9848729 : Blo 1536465 9848729 := bstep (se 2 (by rfl) ⟨3693273, by rfl⟩ : syracuseStep 9848729 = 7386547) B7386547
theorem B8759299 : Blo 1536465 8759299 := bstep (se 1 (by rfl) ⟨6569474, by rfl⟩ : syracuseStep 8759299 = 13138949) B13138949
theorem B3459131 : Blo 1536465 3459131 := bstep (se 1 (by rfl) ⟨2594348, by rfl⟩ : syracuseStep 3459131 = 5188697) B5188697
theorem B5187671 : Blo 1536465 5187671 := bstep (se 1 (by rfl) ⟨3890753, by rfl⟩ : syracuseStep 5187671 = 7781507) B7781507
theorem B1730695 : Blo 1536465 1730695 := bstep (se 1 (by rfl) ⟨1298021, by rfl⟩ : syracuseStep 1730695 = 2596043) B2596043
theorem B3459257 : Blo 1536465 3459257 := bstep (se 2 (by rfl) ⟨1297221, by rfl⟩ : syracuseStep 3459257 = 2594443) B2594443
theorem B6564077 : Blo 1536465 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B26265869 : Blo 1536465 26265869 := bstep (se 3 (by rfl) ⟨4924850, by rfl⟩ : syracuseStep 26265869 = 9849701) B9849701
theorem B5835023 : Blo 1536465 5835023 := bstep (se 1 (by rfl) ⟨4376267, by rfl⟩ : syracuseStep 5835023 = 8752535) B8752535
theorem B2189711 : Blo 1536465 2189711 := bstep (se 1 (by rfl) ⟨1642283, by rfl⟩ : syracuseStep 2189711 = 3284567) B3284567
theorem B9980345 : Blo 1536465 9980345 := bstep (se 2 (by rfl) ⟨3742629, by rfl⟩ : syracuseStep 9980345 = 7485259) B7485259
theorem B11078147 : Blo 1536465 11078147 := bstep (se 1 (by rfl) ⟨8308610, by rfl⟩ : syracuseStep 11078147 = 16617221) B16617221
theorem B3893771 : Blo 1536465 3893771 := bstep (se 1 (by rfl) ⟨2920328, by rfl⟩ : syracuseStep 3893771 = 5840657) B5840657
theorem B3459599 : Blo 1536465 3459599 := bstep (se 1 (by rfl) ⟨2594699, by rfl⟩ : syracuseStep 3459599 = 5189399) B5189399
theorem B3459617 : Blo 1536465 3459617 := bstep (se 2 (by rfl) ⟨1297356, by rfl⟩ : syracuseStep 3459617 = 2594713) B2594713
theorem B2886187 : Blo 1536465 2886187 := bstep (se 1 (by rfl) ⟨2164640, by rfl⟩ : syracuseStep 2886187 = 4329281) B4329281
theorem B5188157 : Blo 1536465 5188157 := bstep (se 3 (by rfl) ⟨972779, by rfl⟩ : syracuseStep 5188157 = 1945559) B1945559
theorem B4377235 : Blo 1536465 4377235 := bstep (se 1 (by rfl) ⟨3282926, by rfl⟩ : syracuseStep 4377235 = 6565853) B6565853
theorem B1845931 : Blo 1536465 1845931 := bstep (se 1 (by rfl) ⟨1384448, by rfl⟩ : syracuseStep 1845931 = 2768897) B2768897
theorem B2304713 : Blo 1536465 2304713 := bstep (se 2 (by rfl) ⟨864267, by rfl⟩ : syracuseStep 2304713 = 1728535) B1728535
theorem B17509121 : Blo 1536465 17509121 := bstep (se 2 (by rfl) ⟨6565920, by rfl⟩ : syracuseStep 17509121 = 13131841) B13131841
theorem B2304827 : Blo 1536465 2304827 := bstep (se 1 (by rfl) ⟨1728620, by rfl⟩ : syracuseStep 2304827 = 3457241) B3457241
theorem B2304887 : Blo 1536465 2304887 := bstep (se 1 (by rfl) ⟨1728665, by rfl⟩ : syracuseStep 2304887 = 3457331) B3457331
theorem B3459959 : Blo 1536465 3459959 := bstep (se 1 (by rfl) ⟨2594969, by rfl⟩ : syracuseStep 3459959 = 5189939) B5189939
theorem B2304911 : Blo 1536465 2304911 := bstep (se 1 (by rfl) ⟨1728683, by rfl⟩ : syracuseStep 2304911 = 3457367) B3457367
theorem B2304953 : Blo 1536465 2304953 := bstep (se 2 (by rfl) ⟨864357, by rfl⟩ : syracuseStep 2304953 = 1728715) B1728715
theorem B2305031 : Blo 1536465 2305031 := bstep (se 1 (by rfl) ⟨1728773, by rfl⟩ : syracuseStep 2305031 = 3457547) B3457547
theorem B2305067 : Blo 1536465 2305067 := bstep (se 1 (by rfl) ⟨1728800, by rfl⟩ : syracuseStep 2305067 = 3457601) B3457601
theorem B8309803 : Blo 1536465 8309803 := bstep (se 1 (by rfl) ⟨6232352, by rfl⟩ : syracuseStep 8309803 = 12464705) B12464705
theorem B3460139 : Blo 1536465 3460139 := bstep (se 1 (by rfl) ⟨2595104, by rfl⟩ : syracuseStep 3460139 = 5190209) B5190209
theorem B2305097 : Blo 1536465 2305097 := bstep (se 2 (by rfl) ⟨864411, by rfl⟩ : syracuseStep 2305097 = 1728823) B1728823
theorem B2370703 : Blo 1536465 2370703 := bstep (se 1 (by rfl) ⟨1778027, by rfl⟩ : syracuseStep 2370703 = 3556055) B3556055
theorem B2305211 : Blo 1536465 2305211 := bstep (se 1 (by rfl) ⟨1728908, by rfl⟩ : syracuseStep 2305211 = 3457817) B3457817
theorem B2305271 : Blo 1536465 2305271 := bstep (se 1 (by rfl) ⟨1728953, by rfl⟩ : syracuseStep 2305271 = 3457907) B3457907
theorem B2305295 : Blo 1536465 2305295 := bstep (se 1 (by rfl) ⟨1728971, by rfl⟩ : syracuseStep 2305295 = 3457943) B3457943
theorem B2305337 : Blo 1536465 2305337 := bstep (se 2 (by rfl) ⟨864501, by rfl⟩ : syracuseStep 2305337 = 1729003) B1729003
theorem B1944967 : Blo 1536465 1944967 := bstep (se 1 (by rfl) ⟨1458725, by rfl⟩ : syracuseStep 1944967 = 2917451) B2917451
theorem B2305415 : Blo 1536465 2305415 := bstep (se 1 (by rfl) ⟨1729061, by rfl⟩ : syracuseStep 2305415 = 3458123) B3458123
theorem B3460499 : Blo 1536465 3460499 := bstep (se 1 (by rfl) ⟨2595374, by rfl⟩ : syracuseStep 3460499 = 5190749) B5190749
theorem B2919827 : Blo 1536465 2919827 := bstep (se 1 (by rfl) ⟨2189870, by rfl⟩ : syracuseStep 2919827 = 4379741) B4379741
theorem B7785881 : Blo 1536465 7785881 := bstep (se 2 (by rfl) ⟨2919705, by rfl⟩ : syracuseStep 7785881 = 5839411) B5839411
theorem B2305451 : Blo 1536465 2305451 := bstep (se 1 (by rfl) ⟨1729088, by rfl⟩ : syracuseStep 2305451 = 3458177) B3458177
theorem B2305481 : Blo 1536465 2305481 := bstep (se 2 (by rfl) ⟨864555, by rfl⟩ : syracuseStep 2305481 = 1729111) B1729111
theorem B3460553 : Blo 1536465 3460553 := bstep (se 2 (by rfl) ⟨1297707, by rfl⟩ : syracuseStep 3460553 = 2595415) B2595415
theorem B2919881 : Blo 1536465 2919881 := bstep (se 2 (by rfl) ⟨1094955, by rfl⟩ : syracuseStep 2919881 = 2189911) B2189911
theorem B16616963 : Blo 1536465 16616963 := bstep (se 1 (by rfl) ⟨12462722, by rfl⟩ : syracuseStep 16616963 = 24925445) B24925445
theorem B2919979 : Blo 1536465 2919979 := bstep (se 1 (by rfl) ⟨2189984, by rfl⟩ : syracuseStep 2919979 = 4379969) B4379969
theorem B9989675 : Blo 1536465 9989675 := bstep (se 1 (by rfl) ⟨7492256, by rfl⟩ : syracuseStep 9989675 = 14984513) B14984513
theorem B2305595 : Blo 1536465 2305595 := bstep (se 1 (by rfl) ⟨1729196, by rfl⟩ : syracuseStep 2305595 = 3458393) B3458393
theorem B6565495 : Blo 1536465 6565495 := bstep (se 1 (by rfl) ⟨4924121, by rfl⟩ : syracuseStep 6565495 = 9848243) B9848243
theorem B2305655 : Blo 1536465 2305655 := bstep (se 1 (by rfl) ⟨1729241, by rfl⟩ : syracuseStep 2305655 = 3458483) B3458483
theorem B2305679 : Blo 1536465 2305679 := bstep (se 1 (by rfl) ⟨1729259, by rfl⟩ : syracuseStep 2305679 = 3458519) B3458519
theorem B2305721 : Blo 1536465 2305721 := bstep (se 2 (by rfl) ⟨864645, by rfl⟩ : syracuseStep 2305721 = 1729291) B1729291
theorem B5918465 : Blo 1536465 5918465 := bstep (se 2 (by rfl) ⟨2219424, by rfl⟩ : syracuseStep 5918465 = 4438849) B4438849
theorem B2305799 : Blo 1536465 2305799 := bstep (se 1 (by rfl) ⟨1729349, by rfl⟩ : syracuseStep 2305799 = 3458699) B3458699
theorem B2920207 : Blo 1536465 2920207 := bstep (se 1 (by rfl) ⟨2190155, by rfl⟩ : syracuseStep 2920207 = 4380311) B4380311
theorem B1945387 : Blo 1536465 1945387 := bstep (se 1 (by rfl) ⟨1459040, by rfl⟩ : syracuseStep 1945387 = 2918081) B2918081
theorem B2305835 : Blo 1536465 2305835 := bstep (se 1 (by rfl) ⟨1729376, by rfl⟩ : syracuseStep 2305835 = 3458753) B3458753
theorem B3944251 : Blo 1536465 3944251 := bstep (se 1 (by rfl) ⟨2958188, by rfl⟩ : syracuseStep 3944251 = 5916377) B5916377
theorem B2305865 : Blo 1536465 2305865 := bstep (se 2 (by rfl) ⟨864699, by rfl⟩ : syracuseStep 2305865 = 1729399) B1729399
theorem B5189561 : Blo 1536465 5189561 := bstep (se 2 (by rfl) ⟨1946085, by rfl⟩ : syracuseStep 5189561 = 3892171) B3892171
theorem B2305979 : Blo 1536465 2305979 := bstep (se 1 (by rfl) ⟨1729484, by rfl⟩ : syracuseStep 2305979 = 3458969) B3458969
theorem B5541841 : Blo 1536465 5541841 := bstep (se 2 (by rfl) ⟨2078190, by rfl⟩ : syracuseStep 5541841 = 4156381) B4156381
theorem B2306039 : Blo 1536465 2306039 := bstep (se 1 (by rfl) ⟨1729529, by rfl⟩ : syracuseStep 2306039 = 3459059) B3459059
theorem B1945615 : Blo 1536465 1945615 := bstep (se 1 (by rfl) ⟨1459211, by rfl⟩ : syracuseStep 1945615 = 2918423) B2918423
theorem B2306063 : Blo 1536465 2306063 := bstep (se 1 (by rfl) ⟨1729547, by rfl⟩ : syracuseStep 2306063 = 3459095) B3459095
theorem B4927517 : Blo 1536465 4927517 := bstep (se 3 (by rfl) ⟨923909, by rfl⟩ : syracuseStep 4927517 = 1847819) B1847819
theorem B2306105 : Blo 1536465 2306105 := bstep (se 2 (by rfl) ⟨864789, by rfl⟩ : syracuseStep 2306105 = 1729579) B1729579
theorem B13127741 : Blo 1536465 13127741 := bstep (se 3 (by rfl) ⟨2461451, by rfl⟩ : syracuseStep 13127741 = 4922903) B4922903
theorem B504868949 : Blo 1536465 504868949 := bstep (se 8 (by rfl) ⟨2958216, by rfl⟩ : syracuseStep 504868949 = 5916433) B5916433
theorem B29560949 : Blo 1536465 29560949 := bstep (se 5 (by rfl) ⟨1385669, by rfl⟩ : syracuseStep 29560949 = 2771339) B2771339
theorem B2306183 : Blo 1536465 2306183 := bstep (se 1 (by rfl) ⟨1729637, by rfl⟩ : syracuseStep 2306183 = 3459275) B3459275
theorem B3461255 : Blo 1536465 3461255 := bstep (se 1 (by rfl) ⟨2595941, by rfl⟩ : syracuseStep 3461255 = 5191883) B5191883
theorem B2306219 : Blo 1536465 2306219 := bstep (se 1 (by rfl) ⟨1729664, by rfl⟩ : syracuseStep 2306219 = 3459329) B3459329
theorem B2306249 : Blo 1536465 2306249 := bstep (se 2 (by rfl) ⟨864843, by rfl⟩ : syracuseStep 2306249 = 1729687) B1729687
theorem B2593039 : Blo 1536465 2593039 := bstep (se 1 (by rfl) ⟨1944779, by rfl⟩ : syracuseStep 2593039 = 3889559) B3889559
theorem B8753467 : Blo 1536465 8753467 := bstep (se 1 (by rfl) ⟨6565100, by rfl⟩ : syracuseStep 8753467 = 13130201) B13130201
theorem B2306363 : Blo 1536465 2306363 := bstep (se 1 (by rfl) ⟨1729772, by rfl⟩ : syracuseStep 2306363 = 3459545) B3459545
theorem B3461435 : Blo 1536465 3461435 := bstep (se 1 (by rfl) ⟨2596076, by rfl⟩ : syracuseStep 3461435 = 5192153) B5192153
theorem B4378967 : Blo 1536465 4378967 := bstep (se 1 (by rfl) ⟨3284225, by rfl⟩ : syracuseStep 4378967 = 6568451) B6568451
theorem B8761715 : Blo 1536465 8761715 := bstep (se 1 (by rfl) ⟨6571286, by rfl⟩ : syracuseStep 8761715 = 13142573) B13142573
theorem B2306423 : Blo 1536465 2306423 := bstep (se 1 (by rfl) ⟨1729817, by rfl⟩ : syracuseStep 2306423 = 3459635) B3459635
theorem B2306447 : Blo 1536465 2306447 := bstep (se 1 (by rfl) ⟨1729835, by rfl⟩ : syracuseStep 2306447 = 3459671) B3459671
theorem B2306489 : Blo 1536465 2306489 := bstep (se 2 (by rfl) ⟨864933, by rfl⟩ : syracuseStep 2306489 = 1729867) B1729867
theorem B28430813 : Blo 1536465 28430813 := bstep (se 3 (by rfl) ⟨5330777, by rfl⟩ : syracuseStep 28430813 = 10661555) B10661555
theorem B1536519 : Blo 1536465 1536519 := bstep (se 1 (by rfl) ⟨1152389, by rfl⟩ : syracuseStep 1536519 = 2304779) B2304779
theorem B2306567 : Blo 1536465 2306567 := bstep (se 1 (by rfl) ⟨1729925, by rfl⟩ : syracuseStep 2306567 = 3459851) B3459851
theorem B5190155 : Blo 1536465 5190155 := bstep (se 1 (by rfl) ⟨3892616, by rfl⟩ : syracuseStep 5190155 = 7785233) B7785233
theorem B1536527 : Blo 1536465 1536527 := bstep (se 1 (by rfl) ⟨1152395, by rfl⟩ : syracuseStep 1536527 = 2304791) B2304791
theorem B2306603 : Blo 1536465 2306603 := bstep (se 1 (by rfl) ⟨1729952, by rfl⟩ : syracuseStep 2306603 = 3459905) B3459905
theorem B1536571 : Blo 1536465 1536571 := bstep (se 1 (by rfl) ⟨1152428, by rfl⟩ : syracuseStep 1536571 = 2304857) B2304857
theorem B1847867 : Blo 1536465 1847867 := bstep (se 1 (by rfl) ⟨1385900, by rfl⟩ : syracuseStep 1847867 = 2771801) B2771801
theorem B2306633 : Blo 1536465 2306633 := bstep (se 2 (by rfl) ⟨864987, by rfl⟩ : syracuseStep 2306633 = 1729975) B1729975
theorem B5190263 : Blo 1536465 5190263 := bstep (se 1 (by rfl) ⟨3892697, by rfl⟩ : syracuseStep 5190263 = 7785395) B7785395
theorem B3281543 : Blo 1536465 3281543 := bstep (se 1 (by rfl) ⟨2461157, by rfl⟩ : syracuseStep 3281543 = 4922315) B4922315
theorem B1536647 : Blo 1536465 1536647 := bstep (se 1 (by rfl) ⟨1152485, by rfl⟩ : syracuseStep 1536647 = 2304971) B2304971
theorem B1536655 : Blo 1536465 1536655 := bstep (se 1 (by rfl) ⟨1152491, by rfl⟩ : syracuseStep 1536655 = 2304983) B2304983
theorem B2077369 : Blo 1536465 2077369 := bstep (se 2 (by rfl) ⟨779013, by rfl⟩ : syracuseStep 2077369 = 1558027) B1558027
theorem B1536699 : Blo 1536465 1536699 := bstep (se 1 (by rfl) ⟨1152524, by rfl⟩ : syracuseStep 1536699 = 2305049) B2305049
theorem B2306747 : Blo 1536465 2306747 := bstep (se 1 (by rfl) ⟨1730060, by rfl⟩ : syracuseStep 2306747 = 3460121) B3460121
theorem B1946359 : Blo 1536465 1946359 := bstep (se 1 (by rfl) ⟨1459769, by rfl⟩ : syracuseStep 1946359 = 2919539) B2919539
theorem B2306807 : Blo 1536465 2306807 := bstep (se 1 (by rfl) ⟨1730105, by rfl⟩ : syracuseStep 2306807 = 3460211) B3460211
theorem B1536775 : Blo 1536465 1536775 := bstep (se 1 (by rfl) ⟨1152581, by rfl⟩ : syracuseStep 1536775 = 2305163) B2305163
theorem B1536783 : Blo 1536465 1536783 := bstep (se 1 (by rfl) ⟨1152587, by rfl⟩ : syracuseStep 1536783 = 2305175) B2305175
theorem B2306831 : Blo 1536465 2306831 := bstep (se 1 (by rfl) ⟨1730123, by rfl⟩ : syracuseStep 2306831 = 3460247) B3460247
theorem B2593579 : Blo 1536465 2593579 := bstep (se 1 (by rfl) ⟨1945184, by rfl⟩ : syracuseStep 2593579 = 3890369) B3890369
theorem B2306873 : Blo 1536465 2306873 := bstep (se 2 (by rfl) ⟨865077, by rfl⟩ : syracuseStep 2306873 = 1730155) B1730155
theorem B1536827 : Blo 1536465 1536827 := bstep (se 1 (by rfl) ⟨1152620, by rfl⟩ : syracuseStep 1536827 = 2305241) B2305241
theorem B11678579 : Blo 1536465 11678579 := bstep (se 1 (by rfl) ⟨8758934, by rfl⟩ : syracuseStep 11678579 = 17517869) B17517869
theorem B1536903 : Blo 1536465 1536903 := bstep (se 1 (by rfl) ⟨1152677, by rfl⟩ : syracuseStep 1536903 = 2305355) B2305355
theorem B2306951 : Blo 1536465 2306951 := bstep (se 1 (by rfl) ⟨1730213, by rfl⟩ : syracuseStep 2306951 = 3460427) B3460427
theorem B1536911 : Blo 1536465 1536911 := bstep (se 1 (by rfl) ⟨1152683, by rfl⟩ : syracuseStep 1536911 = 2305367) B2305367
theorem B2306987 : Blo 1536465 2306987 := bstep (se 1 (by rfl) ⟨1730240, by rfl⟩ : syracuseStep 2306987 = 3460481) B3460481
theorem B2593721 : Blo 1536465 2593721 := bstep (se 2 (by rfl) ⟨972645, by rfl⟩ : syracuseStep 2593721 = 1945291) B1945291
theorem B1536955 : Blo 1536465 1536955 := bstep (se 1 (by rfl) ⟨1152716, by rfl⟩ : syracuseStep 1536955 = 2305433) B2305433
theorem B2307017 : Blo 1536465 2307017 := bstep (se 2 (by rfl) ⟨865131, by rfl⟩ : syracuseStep 2307017 = 1730263) B1730263
theorem B1537031 : Blo 1536465 1537031 := bstep (se 1 (by rfl) ⟨1152773, by rfl⟩ : syracuseStep 1537031 = 2305547) B2305547
theorem B1537039 : Blo 1536465 1537039 := bstep (se 1 (by rfl) ⟨1152779, by rfl⟩ : syracuseStep 1537039 = 2305559) B2305559
theorem B3281953 : Blo 1536465 3281953 := bstep (se 2 (by rfl) ⟨1230732, by rfl⟩ : syracuseStep 3281953 = 2461465) B2461465
theorem B1537083 : Blo 1536465 1537083 := bstep (se 1 (by rfl) ⟨1152812, by rfl⟩ : syracuseStep 1537083 = 2305625) B2305625
theorem B2307131 : Blo 1536465 2307131 := bstep (se 1 (by rfl) ⟨1730348, by rfl⟩ : syracuseStep 2307131 = 3460697) B3460697
theorem B1946683 : Blo 1536465 1946683 := bstep (se 1 (by rfl) ⟨1460012, by rfl⟩ : syracuseStep 1946683 = 2920025) B2920025
theorem B2307191 : Blo 1536465 2307191 := bstep (se 1 (by rfl) ⟨1730393, by rfl⟩ : syracuseStep 2307191 = 3460787) B3460787
theorem B1537159 : Blo 1536465 1537159 := bstep (se 1 (by rfl) ⟨1152869, by rfl⟩ : syracuseStep 1537159 = 2305739) B2305739
theorem B1537167 : Blo 1536465 1537167 := bstep (se 1 (by rfl) ⟨1152875, by rfl⟩ : syracuseStep 1537167 = 2305751) B2305751
theorem B2307215 : Blo 1536465 2307215 := bstep (se 1 (by rfl) ⟨1730411, by rfl⟩ : syracuseStep 2307215 = 3460823) B3460823
theorem B2307257 : Blo 1536465 2307257 := bstep (se 2 (by rfl) ⟨865221, by rfl⟩ : syracuseStep 2307257 = 1730443) B1730443
theorem B1537211 : Blo 1536465 1537211 := bstep (se 1 (by rfl) ⟨1152908, by rfl⟩ : syracuseStep 1537211 = 2305817) B2305817
theorem B5190857 : Blo 1536465 5190857 := bstep (se 2 (by rfl) ⟨1946571, by rfl⟩ : syracuseStep 5190857 = 3893143) B3893143
theorem B1537287 : Blo 1536465 1537287 := bstep (se 1 (by rfl) ⟨1152965, by rfl⟩ : syracuseStep 1537287 = 2305931) B2305931
theorem B2307335 : Blo 1536465 2307335 := bstep (se 1 (by rfl) ⟨1730501, by rfl⟩ : syracuseStep 2307335 = 3461003) B3461003
theorem B1537295 : Blo 1536465 1537295 := bstep (se 1 (by rfl) ⟨1152971, by rfl⟩ : syracuseStep 1537295 = 2305943) B2305943
theorem B3282209 : Blo 1536465 3282209 := bstep (se 2 (by rfl) ⟨1230828, by rfl⟩ : syracuseStep 3282209 = 2461657) B2461657
theorem B2307371 : Blo 1536465 2307371 := bstep (se 1 (by rfl) ⟨1730528, by rfl⟩ : syracuseStep 2307371 = 3461057) B3461057
theorem B14021947 : Blo 1536465 14021947 := bstep (se 1 (by rfl) ⟨10516460, by rfl⟩ : syracuseStep 14021947 = 21032921) B21032921
theorem B1537339 : Blo 1536465 1537339 := bstep (se 1 (by rfl) ⟨1153004, by rfl⟩ : syracuseStep 1537339 = 2306009) B2306009
theorem B2307401 : Blo 1536465 2307401 := bstep (se 2 (by rfl) ⟨865275, by rfl⟩ : syracuseStep 2307401 = 1730551) B1730551
theorem B3282295 : Blo 1536465 3282295 := bstep (se 1 (by rfl) ⟨2461721, by rfl⟩ : syracuseStep 3282295 = 4923443) B4923443
theorem B1537415 : Blo 1536465 1537415 := bstep (se 1 (by rfl) ⟨1153061, by rfl⟩ : syracuseStep 1537415 = 2306123) B2306123
theorem B1537423 : Blo 1536465 1537423 := bstep (se 1 (by rfl) ⟨1153067, by rfl⟩ : syracuseStep 1537423 = 2306135) B2306135
theorem B5838227 : Blo 1536465 5838227 := bstep (se 1 (by rfl) ⟨4378670, by rfl⟩ : syracuseStep 5838227 = 8757341) B8757341
theorem B1537467 : Blo 1536465 1537467 := bstep (se 1 (by rfl) ⟨1153100, by rfl⟩ : syracuseStep 1537467 = 2306201) B2306201
theorem B2307515 : Blo 1536465 2307515 := bstep (se 1 (by rfl) ⟨1730636, by rfl⟩ : syracuseStep 2307515 = 3461273) B3461273
theorem B2307575 : Blo 1536465 2307575 := bstep (se 1 (by rfl) ⟨1730681, by rfl⟩ : syracuseStep 2307575 = 3461363) B3461363
theorem B1537543 : Blo 1536465 1537543 := bstep (se 1 (by rfl) ⟨1153157, by rfl⟩ : syracuseStep 1537543 = 2306315) B2306315
theorem B1537551 : Blo 1536465 1537551 := bstep (se 1 (by rfl) ⟨1153163, by rfl⟩ : syracuseStep 1537551 = 2306327) B2306327
theorem B2307599 : Blo 1536465 2307599 := bstep (se 1 (by rfl) ⟨1730699, by rfl⟩ : syracuseStep 2307599 = 3461399) B3461399
theorem B2307641 : Blo 1536465 2307641 := bstep (se 2 (by rfl) ⟨865365, by rfl⟩ : syracuseStep 2307641 = 1730731) B1730731
theorem B1537595 : Blo 1536465 1537595 := bstep (se 1 (by rfl) ⟨1153196, by rfl⟩ : syracuseStep 1537595 = 2306393) B2306393
theorem B11392579 : Blo 1536465 11392579 := bstep (se 1 (by rfl) ⟨8544434, by rfl⟩ : syracuseStep 11392579 = 17088869) B17088869
theorem B17512037 : Blo 1536465 17512037 := bstep (se 4 (by rfl) ⟨1641753, by rfl⟩ : syracuseStep 17512037 = 3283507) B3283507
theorem B2594423 : Blo 1536465 2594423 := bstep (se 1 (by rfl) ⟨1945817, by rfl⟩ : syracuseStep 2594423 = 3891635) B3891635
theorem B1537671 : Blo 1536465 1537671 := bstep (se 1 (by rfl) ⟨1153253, by rfl⟩ : syracuseStep 1537671 = 2306507) B2306507
theorem B1537679 : Blo 1536465 1537679 := bstep (se 1 (by rfl) ⟨1153259, by rfl⟩ : syracuseStep 1537679 = 2306519) B2306519
theorem B1537723 : Blo 1536465 1537723 := bstep (se 1 (by rfl) ⟨1153292, by rfl⟩ : syracuseStep 1537723 = 2306585) B2306585
theorem B7894721 : Blo 1536465 7894721 := bstep (se 2 (by rfl) ⟨2960520, by rfl⟩ : syracuseStep 7894721 = 5921041) B5921041
theorem B8754925 : Blo 1536465 8754925 := bstep (se 3 (by rfl) ⟨1641548, by rfl⟩ : syracuseStep 8754925 = 3283097) B3283097
theorem B1537799 : Blo 1536465 1537799 := bstep (se 1 (by rfl) ⟨1153349, by rfl⟩ : syracuseStep 1537799 = 2306699) B2306699
theorem B1537807 : Blo 1536465 1537807 := bstep (se 1 (by rfl) ⟨1153355, by rfl⟩ : syracuseStep 1537807 = 2306711) B2306711
theorem B1537851 : Blo 1536465 1537851 := bstep (se 1 (by rfl) ⟨1153388, by rfl⟩ : syracuseStep 1537851 = 2306777) B2306777
theorem B7780211 : Blo 1536465 7780211 := bstep (se 1 (by rfl) ⟨5835158, by rfl⟩ : syracuseStep 7780211 = 11670317) B11670317
theorem B1537927 : Blo 1536465 1537927 := bstep (se 1 (by rfl) ⟨1153445, by rfl⟩ : syracuseStep 1537927 = 2306891) B2306891
theorem B5191559 : Blo 1536465 5191559 := bstep (se 1 (by rfl) ⟨3893669, by rfl⟩ : syracuseStep 5191559 = 7787339) B7787339
theorem B4380551 : Blo 1536465 4380551 := bstep (se 1 (by rfl) ⟨3285413, by rfl⟩ : syracuseStep 4380551 = 6570827) B6570827
theorem B1537935 : Blo 1536465 1537935 := bstep (se 1 (by rfl) ⟨1153451, by rfl⟩ : syracuseStep 1537935 = 2306903) B2306903
theorem B7788473 : Blo 1536465 7788473 := bstep (se 2 (by rfl) ⟨2920677, by rfl⟩ : syracuseStep 7788473 = 5841355) B5841355
theorem B1537979 : Blo 1536465 1537979 := bstep (se 1 (by rfl) ⟨1153484, by rfl⟩ : syracuseStep 1537979 = 2306969) B2306969
theorem B1538055 : Blo 1536465 1538055 := bstep (se 1 (by rfl) ⟨1153541, by rfl⟩ : syracuseStep 1538055 = 2307083) B2307083
theorem B1538063 : Blo 1536465 1538063 := bstep (se 1 (by rfl) ⟨1153547, by rfl⟩ : syracuseStep 1538063 = 2307095) B2307095
theorem B2594875 : Blo 1536465 2594875 := bstep (se 1 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 2594875 = 3892313) B3892313
theorem B1538107 : Blo 1536465 1538107 := bstep (se 1 (by rfl) ⟨1153580, by rfl⟩ : syracuseStep 1538107 = 2307161) B2307161
theorem B1538183 : Blo 1536465 1538183 := bstep (se 1 (by rfl) ⟨1153637, by rfl⟩ : syracuseStep 1538183 = 2307275) B2307275
theorem B1538191 : Blo 1536465 1538191 := bstep (se 1 (by rfl) ⟨1153643, by rfl⟩ : syracuseStep 1538191 = 2307287) B2307287
theorem B1538235 : Blo 1536465 1538235 := bstep (se 1 (by rfl) ⟨1153676, by rfl⟩ : syracuseStep 1538235 = 2307353) B2307353
theorem B2595017 : Blo 1536465 2595017 := bstep (se 2 (by rfl) ⟨973131, by rfl⟩ : syracuseStep 2595017 = 1946263) B1946263
theorem B5191937 : Blo 1536465 5191937 := bstep (se 2 (by rfl) ⟨1946976, by rfl⟩ : syracuseStep 5191937 = 3893953) B3893953
theorem B1538311 : Blo 1536465 1538311 := bstep (se 1 (by rfl) ⟨1153733, by rfl⟩ : syracuseStep 1538311 = 2307467) B2307467
theorem B2464015 : Blo 1536465 2464015 := bstep (se 1 (by rfl) ⟨1848011, by rfl⟩ : syracuseStep 2464015 = 3696023) B3696023
theorem B1538319 : Blo 1536465 1538319 := bstep (se 1 (by rfl) ⟨1153739, by rfl⟩ : syracuseStep 1538319 = 2307479) B2307479
theorem B14768401 : Blo 1536465 14768401 := bstep (se 2 (by rfl) ⟨5538150, by rfl⟩ : syracuseStep 14768401 = 11076301) B11076301
theorem B5544251 : Blo 1536465 5544251 := bstep (se 1 (by rfl) ⟨4158188, by rfl⟩ : syracuseStep 5544251 = 8316377) B8316377
theorem B1538363 : Blo 1536465 1538363 := bstep (se 1 (by rfl) ⟨1153772, by rfl⟩ : syracuseStep 1538363 = 2307545) B2307545
theorem B7780697 : Blo 1536465 7780697 := bstep (se 2 (by rfl) ⟨2917761, by rfl⟩ : syracuseStep 7780697 = 5835523) B5835523
theorem B1538439 : Blo 1536465 1538439 := bstep (se 1 (by rfl) ⟨1153829, by rfl⟩ : syracuseStep 1538439 = 2307659) B2307659
theorem B1538447 : Blo 1536465 1538447 := bstep (se 1 (by rfl) ⟨1153835, by rfl⟩ : syracuseStep 1538447 = 2307671) B2307671
theorem B3692947 : Blo 1536465 3692947 := bstep (se 1 (by rfl) ⟨2769710, by rfl⟩ : syracuseStep 3692947 = 5539421) B5539421
theorem B2464271 : Blo 1536465 2464271 := bstep (se 1 (by rfl) ⟨1848203, by rfl⟩ : syracuseStep 2464271 = 3696407) B3696407
theorem B7109149 : Blo 1536465 7109149 := bstep (se 3 (by rfl) ⟨1332965, by rfl⟩ : syracuseStep 7109149 = 2665931) B2665931
theorem B4676125 : Blo 1536465 4676125 := bstep (se 3 (by rfl) ⟨876773, by rfl⟩ : syracuseStep 4676125 = 1753547) B1753547
theorem B14785091 : Blo 1536465 14785091 := bstep (se 1 (by rfl) ⟨11088818, by rfl⟩ : syracuseStep 14785091 = 22177637) B22177637
theorem B3947123 : Blo 1536465 3947123 := bstep (se 1 (by rfl) ⟨2960342, by rfl⟩ : syracuseStep 3947123 = 5920685) B5920685
theorem B39418487 : Blo 1536465 39418487 := bstep (se 1 (by rfl) ⟨29563865, by rfl⟩ : syracuseStep 39418487 = 59127731) B59127731
theorem B5913479 : Blo 1536465 5913479 := bstep (se 1 (by rfl) ⟨4435109, by rfl⟩ : syracuseStep 5913479 = 8870219) B8870219
theorem B2595719 : Blo 1536465 2595719 := bstep (se 1 (by rfl) ⟨1946789, by rfl⟩ : syracuseStep 2595719 = 3893579) B3893579
theorem B8657849 : Blo 1536465 8657849 := bstep (se 2 (by rfl) ⟨3246693, by rfl⟩ : syracuseStep 8657849 = 6493387) B6493387
theorem B3890177 : Blo 1536465 3890177 := bstep (se 2 (by rfl) ⟨1458816, by rfl⟩ : syracuseStep 3890177 = 2917633) B2917633
theorem B5839883 : Blo 1536465 5839883 := bstep (se 1 (by rfl) ⟨4379912, by rfl⟩ : syracuseStep 5839883 = 8759825) B8759825
theorem B9845783 : Blo 1536465 9845783 := bstep (se 1 (by rfl) ⟨7384337, by rfl⟩ : syracuseStep 9845783 = 14768675) B14768675
theorem B17513495 : Blo 1536465 17513495 := bstep (se 1 (by rfl) ⟨13135121, by rfl⟩ : syracuseStep 17513495 = 26270243) B26270243
theorem B7388279 : Blo 1536465 7388279 := bstep (se 1 (by rfl) ⟨5541209, by rfl⟩ : syracuseStep 7388279 = 11082419) B11082419
theorem B14777477 : Blo 1536465 14777477 := bstep (se 4 (by rfl) ⟨1385388, by rfl⟩ : syracuseStep 14777477 = 2770777) B2770777
theorem B11238533 : Blo 1536465 11238533 := bstep (se 4 (by rfl) ⟨1053612, by rfl⟩ : syracuseStep 11238533 = 2107225) B2107225
theorem B67370125 : Blo 1536465 67370125 := bstep (se 3 (by rfl) ⟨12631898, by rfl⟩ : syracuseStep 67370125 = 25263797) B25263797
theorem B3890551 : Blo 1536465 3890551 := bstep (se 1 (by rfl) ⟨2917913, by rfl⟩ : syracuseStep 3890551 = 5835827) B5835827
theorem B17522243 : Blo 1536465 17522243 := bstep (se 1 (by rfl) ⟨13141682, by rfl⟩ : syracuseStep 17522243 = 26283365) B26283365
theorem B8756909 : Blo 1536465 8756909 := bstep (se 3 (by rfl) ⟨1641920, by rfl⟩ : syracuseStep 8756909 = 3283841) B3283841
theorem B8871695 : Blo 1536465 8871695 := bstep (se 1 (by rfl) ⟨6653771, by rfl⟩ : syracuseStep 8871695 = 13307543) B13307543
theorem B3890987 : Blo 1536465 3890987 := bstep (se 1 (by rfl) ⟨2918240, by rfl⟩ : syracuseStep 3890987 = 5836481) B5836481
theorem B84156205 : Blo 1536465 84156205 := bstep (se 3 (by rfl) ⟨15779288, by rfl⟩ : syracuseStep 84156205 = 31558577) B31558577
theorem B5537689 : Blo 1536465 5537689 := bstep (se 2 (by rfl) ⟨2076633, by rfl⟩ : syracuseStep 5537689 = 4153267) B4153267
theorem B3506183 : Blo 1536465 3506183 := bstep (se 1 (by rfl) ⟨2629637, by rfl⟩ : syracuseStep 3506183 = 5259275) B5259275
theorem B5537807 : Blo 1536465 5537807 := bstep (se 1 (by rfl) ⟨4153355, by rfl⟩ : syracuseStep 5537807 = 8306711) B8306711
theorem B3285011 : Blo 1536465 3285011 := bstep (se 1 (by rfl) ⟨2463758, by rfl⟩ : syracuseStep 3285011 = 4927517) B4927517
theorem B63971477 : Blo 1536465 63971477 := bstep (se 6 (by rfl) ⟨1499331, by rfl⟩ : syracuseStep 63971477 = 2998663) B2998663
theorem B5841143 : Blo 1536465 5841143 := bstep (se 1 (by rfl) ⟨4380857, by rfl⟩ : syracuseStep 5841143 = 8761715) B8761715
theorem B7012619 : Blo 1536465 7012619 := bstep (se 1 (by rfl) ⟨5259464, by rfl⟩ : syracuseStep 7012619 = 10518929) B10518929
theorem B3457385 : Blo 1536465 3457385 := bstep (se 2 (by rfl) ⟨1296519, by rfl⟩ : syracuseStep 3457385 = 2593039) B2593039
theorem B3285353 : Blo 1536465 3285353 := bstep (se 2 (by rfl) ⟨1232007, by rfl⟩ : syracuseStep 3285353 = 2464015) B2464015
theorem B2187695 : Blo 1536465 2187695 := bstep (se 1 (by rfl) ⟨1640771, by rfl⟩ : syracuseStep 2187695 = 3281543) B3281543
theorem B4923929 : Blo 1536465 4923929 := bstep (se 2 (by rfl) ⟨1846473, by rfl⟩ : syracuseStep 4923929 = 3692947) B3692947
theorem B1729147 : Blo 1536465 1729147 := bstep (se 1 (by rfl) ⟨1296860, by rfl⟩ : syracuseStep 1729147 = 2593721) B2593721
theorem B2917063 : Blo 1536465 2917063 := bstep (se 1 (by rfl) ⟨2187797, by rfl⟩ : syracuseStep 2917063 = 4375595) B4375595
theorem B9478865 : Blo 1536465 9478865 := bstep (se 2 (by rfl) ⟨3554574, by rfl⟩ : syracuseStep 9478865 = 7109149) B7109149
theorem B6234833 : Blo 1536465 6234833 := bstep (se 2 (by rfl) ⟨2338062, by rfl⟩ : syracuseStep 6234833 = 4676125) B4676125
theorem B2188139 : Blo 1536465 2188139 := bstep (se 1 (by rfl) ⟨1641104, by rfl⟩ : syracuseStep 2188139 = 3282209) B3282209
theorem B3892151 : Blo 1536465 3892151 := bstep (se 1 (by rfl) ⟨2919113, by rfl⟩ : syracuseStep 3892151 = 5838227) B5838227
theorem B3457979 : Blo 1536465 3457979 := bstep (se 1 (by rfl) ⟨2593484, by rfl⟩ : syracuseStep 3457979 = 5186969) B5186969
theorem B24921107 : Blo 1536465 24921107 := bstep (se 1 (by rfl) ⟨18690830, by rfl⟩ : syracuseStep 24921107 = 37381661) B37381661
theorem B3458105 : Blo 1536465 3458105 := bstep (se 2 (by rfl) ⟨1296789, by rfl⟩ : syracuseStep 3458105 = 2593579) B2593579
theorem B11674691 : Blo 1536465 11674691 := bstep (se 1 (by rfl) ⟨8756018, by rfl⟩ : syracuseStep 11674691 = 17512037) B17512037
theorem B8307791 : Blo 1536465 8307791 := bstep (se 1 (by rfl) ⟨6230843, by rfl⟩ : syracuseStep 8307791 = 12461687) B12461687
theorem B1729615 : Blo 1536465 1729615 := bstep (se 1 (by rfl) ⟨1297211, by rfl⟩ : syracuseStep 1729615 = 2594423) B2594423
theorem B5186807 : Blo 1536465 5186807 := bstep (se 1 (by rfl) ⟨3890105, by rfl⟩ : syracuseStep 5186807 = 7780211) B7780211
theorem B4375937 : Blo 1536465 4375937 := bstep (se 2 (by rfl) ⟨1640976, by rfl⟩ : syracuseStep 4375937 = 3281953) B3281953
theorem B3458447 : Blo 1536465 3458447 := bstep (se 1 (by rfl) ⟨2593835, by rfl⟩ : syracuseStep 3458447 = 5187671) B5187671
theorem B1730011 : Blo 1536465 1730011 := bstep (se 1 (by rfl) ⟨1297508, by rfl⟩ : syracuseStep 1730011 = 2595017) B2595017
theorem B4376051 : Blo 1536465 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B89826833 : Blo 1536465 89826833 := bstep (se 2 (by rfl) ⟨33685062, by rfl⟩ : syracuseStep 89826833 = 67370125) B67370125
theorem B3696167 : Blo 1536465 3696167 := bstep (se 1 (by rfl) ⟨2772125, by rfl⟩ : syracuseStep 3696167 = 5544251) B5544251
theorem B5187131 : Blo 1536465 5187131 := bstep (se 1 (by rfl) ⟨3890348, by rfl⟩ : syracuseStep 5187131 = 7780697) B7780697
theorem B3458771 : Blo 1536465 3458771 := bstep (se 1 (by rfl) ⟨2594078, by rfl⟩ : syracuseStep 3458771 = 5188157) B5188157
theorem B9856727 : Blo 1536465 9856727 := bstep (se 1 (by rfl) ⟨7392545, by rfl⟩ : syracuseStep 9856727 = 14785091) B14785091
theorem B2631415 : Blo 1536465 2631415 := bstep (se 1 (by rfl) ⟨1973561, by rfl⟩ : syracuseStep 2631415 = 3947123) B3947123
theorem B18695929 : Blo 1536465 18695929 := bstep (se 2 (by rfl) ⟨7010973, by rfl⟩ : syracuseStep 18695929 = 14021947) B14021947
theorem B4376393 : Blo 1536465 4376393 := bstep (se 2 (by rfl) ⟨1641147, by rfl⟩ : syracuseStep 4376393 = 3282295) B3282295
theorem B5187401 : Blo 1536465 5187401 := bstep (se 2 (by rfl) ⟨1945275, by rfl⟩ : syracuseStep 5187401 = 3890551) B3890551
theorem B3942319 : Blo 1536465 3942319 := bstep (se 1 (by rfl) ⟨2956739, by rfl⟩ : syracuseStep 3942319 = 5913479) B5913479
theorem B1730479 : Blo 1536465 1730479 := bstep (se 1 (by rfl) ⟨1297859, by rfl⟩ : syracuseStep 1730479 = 2595719) B2595719
theorem B3893255 : Blo 1536465 3893255 := bstep (se 1 (by rfl) ⟨2919941, by rfl⟩ : syracuseStep 3893255 = 5839883) B5839883
theorem B6563855 : Blo 1536465 6563855 := bstep (se 1 (by rfl) ⟨4922891, by rfl⟩ : syracuseStep 6563855 = 9845783) B9845783
theorem B11675663 : Blo 1536465 11675663 := bstep (se 1 (by rfl) ⟨8756747, by rfl⟩ : syracuseStep 11675663 = 17513495) B17513495
theorem B3893305 : Blo 1536465 3893305 := bstep (se 2 (by rfl) ⟨1459989, by rfl⟩ : syracuseStep 3893305 = 2919979) B2919979
theorem B4925519 : Blo 1536465 4925519 := bstep (se 1 (by rfl) ⟨3694139, by rfl⟩ : syracuseStep 4925519 = 7388279) B7388279
theorem B15190105 : Blo 1536465 15190105 := bstep (se 2 (by rfl) ⟨5696289, by rfl⟩ : syracuseStep 15190105 = 11392579) B11392579
theorem B29534341 : Blo 1536465 29534341 := bstep (se 4 (by rfl) ⟨2768844, by rfl⟩ : syracuseStep 29534341 = 5537689) B5537689
theorem B11077975 : Blo 1536465 11077975 := bstep (se 1 (by rfl) ⟨8308481, by rfl⟩ : syracuseStep 11077975 = 16616963) B16616963
theorem B3893609 : Blo 1536465 3893609 := bstep (se 2 (by rfl) ⟨1460103, by rfl⟩ : syracuseStep 3893609 = 2920207) B2920207
theorem B112208273 : Blo 1536465 112208273 := bstep (se 2 (by rfl) ⟨42078102, by rfl⟩ : syracuseStep 112208273 = 84156205) B84156205
theorem B23087597 : Blo 1536465 23087597 := bstep (se 3 (by rfl) ⟨4328924, by rfl⟩ : syracuseStep 23087597 = 8657849) B8657849
theorem B3459707 : Blo 1536465 3459707 := bstep (se 1 (by rfl) ⟨2594780, by rfl⟩ : syracuseStep 3459707 = 5189561) B5189561
theorem B8751827 : Blo 1536465 8751827 := bstep (se 1 (by rfl) ⟨6563870, by rfl⟩ : syracuseStep 8751827 = 13127741) B13127741
theorem B336579299 : Blo 1536465 336579299 := bstep (se 1 (by rfl) ⟨252434474, by rfl⟩ : syracuseStep 336579299 = 504868949) B504868949
theorem B2304761 : Blo 1536465 2304761 := bstep (se 2 (by rfl) ⟨864285, by rfl⟩ : syracuseStep 2304761 = 1728571) B1728571
theorem B3459833 : Blo 1536465 3459833 := bstep (se 2 (by rfl) ⟨1297437, by rfl⟩ : syracuseStep 3459833 = 2594875) B2594875
theorem B2304863 : Blo 1536465 2304863 := bstep (se 1 (by rfl) ⟨1728647, by rfl⟩ : syracuseStep 2304863 = 3457295) B3457295
theorem B2304875 : Blo 1536465 2304875 := bstep (se 1 (by rfl) ⟨1728656, by rfl⟩ : syracuseStep 2304875 = 3457313) B3457313
theorem B2919311 : Blo 1536465 2919311 := bstep (se 1 (by rfl) ⟨2189483, by rfl⟩ : syracuseStep 2919311 = 4378967) B4378967
theorem B5188535 : Blo 1536465 5188535 := bstep (se 1 (by rfl) ⟨3891401, by rfl⟩ : syracuseStep 5188535 = 7782803) B7782803
theorem B3460103 : Blo 1536465 3460103 := bstep (se 1 (by rfl) ⟨2595077, by rfl⟩ : syracuseStep 3460103 = 5190155) B5190155
theorem B2305103 : Blo 1536465 2305103 := bstep (se 1 (by rfl) ⟨1728827, by rfl⟩ : syracuseStep 2305103 = 3457655) B3457655
theorem B3460175 : Blo 1536465 3460175 := bstep (se 1 (by rfl) ⟨2595131, by rfl⟩ : syracuseStep 3460175 = 5190263) B5190263
theorem B10661057 : Blo 1536465 10661057 := bstep (se 2 (by rfl) ⟨3997896, by rfl⟩ : syracuseStep 10661057 = 7995793) B7995793
theorem B2305223 : Blo 1536465 2305223 := bstep (se 1 (by rfl) ⟨1728917, by rfl⟩ : syracuseStep 2305223 = 3457835) B3457835
theorem B7785719 : Blo 1536465 7785719 := bstep (se 1 (by rfl) ⟨5839289, by rfl⟩ : syracuseStep 7785719 = 11678579) B11678579
theorem B2305385 : Blo 1536465 2305385 := bstep (se 2 (by rfl) ⟨864519, by rfl⟩ : syracuseStep 2305385 = 1729039) B1729039
theorem B2305463 : Blo 1536465 2305463 := bstep (se 1 (by rfl) ⟨1729097, by rfl⟩ : syracuseStep 2305463 = 3458195) B3458195
theorem B2305499 : Blo 1536465 2305499 := bstep (se 1 (by rfl) ⟨1729124, by rfl⟩ : syracuseStep 2305499 = 3458249) B3458249
theorem B3460571 : Blo 1536465 3460571 := bstep (se 1 (by rfl) ⟨2595428, by rfl⟩ : syracuseStep 3460571 = 5190857) B5190857
theorem B5189129 : Blo 1536465 5189129 := bstep (se 2 (by rfl) ⟨1945923, by rfl⟩ : syracuseStep 5189129 = 3891847) B3891847
theorem B5836313 : Blo 1536465 5836313 := bstep (se 2 (by rfl) ⟨2188617, by rfl⟩ : syracuseStep 5836313 = 4377235) B4377235
theorem B2461241 : Blo 1536465 2461241 := bstep (se 2 (by rfl) ⟨922965, by rfl⟩ : syracuseStep 2461241 = 1845931) B1845931
theorem B11079301 : Blo 1536465 11079301 := bstep (se 4 (by rfl) ⟨1038684, by rfl⟩ : syracuseStep 11079301 = 2077369) B2077369
theorem B8761031 : Blo 1536465 8761031 := bstep (se 1 (by rfl) ⟨6570773, by rfl⟩ : syracuseStep 8761031 = 13141547) B13141547
theorem B7786205 : Blo 1536465 7786205 := bstep (se 3 (by rfl) ⟨1459913, by rfl⟩ : syracuseStep 7786205 = 2919827) B2919827
theorem B8105771 : Blo 1536465 8105771 := bstep (se 1 (by rfl) ⟨6079328, by rfl⟩ : syracuseStep 8105771 = 12158657) B12158657
theorem B5263147 : Blo 1536465 5263147 := bstep (se 1 (by rfl) ⟨3947360, by rfl⟩ : syracuseStep 5263147 = 7894721) B7894721
theorem B2305967 : Blo 1536465 2305967 := bstep (se 1 (by rfl) ⟨1729475, by rfl⟩ : syracuseStep 2305967 = 3458951) B3458951
theorem B3461039 : Blo 1536465 3461039 := bstep (se 1 (by rfl) ⟨2595779, by rfl⟩ : syracuseStep 3461039 = 5191559) B5191559
theorem B2920367 : Blo 1536465 2920367 := bstep (se 1 (by rfl) ⟨2190275, by rfl⟩ : syracuseStep 2920367 = 4380551) B4380551
theorem B6565819 : Blo 1536465 6565819 := bstep (se 1 (by rfl) ⟨4924364, by rfl⟩ : syracuseStep 6565819 = 9848729) B9848729
theorem B2306057 : Blo 1536465 2306057 := bstep (se 2 (by rfl) ⟨864771, by rfl⟩ : syracuseStep 2306057 = 1729543) B1729543
theorem B2306087 : Blo 1536465 2306087 := bstep (se 1 (by rfl) ⟨1729565, by rfl⟩ : syracuseStep 2306087 = 3459131) B3459131
theorem B11079737 : Blo 1536465 11079737 := bstep (se 2 (by rfl) ⟨4154901, by rfl⟩ : syracuseStep 11079737 = 8309803) B8309803
theorem B2306171 : Blo 1536465 2306171 := bstep (se 1 (by rfl) ⟨1729628, by rfl⟩ : syracuseStep 2306171 = 3459257) B3459257
theorem B4927645 : Blo 1536465 4927645 := bstep (se 3 (by rfl) ⟨923933, by rfl⟩ : syracuseStep 4927645 = 1847867) B1847867
theorem B3461291 : Blo 1536465 3461291 := bstep (se 1 (by rfl) ⟨2595968, by rfl⟩ : syracuseStep 3461291 = 5191937) B5191937
theorem B17510579 : Blo 1536465 17510579 := bstep (se 1 (by rfl) ⟨13132934, by rfl⟩ : syracuseStep 17510579 = 26265869) B26265869
theorem B2306297 : Blo 1536465 2306297 := bstep (se 2 (by rfl) ⟨864861, by rfl⟩ : syracuseStep 2306297 = 1729723) B1729723
theorem B7385431 : Blo 1536465 7385431 := bstep (se 1 (by rfl) ⟨5539073, by rfl⟩ : syracuseStep 7385431 = 11078147) B11078147
theorem B2306399 : Blo 1536465 2306399 := bstep (se 1 (by rfl) ⟨1729799, by rfl⟩ : syracuseStep 2306399 = 3459599) B3459599
theorem B1642847 : Blo 1536465 1642847 := bstep (se 1 (by rfl) ⟨1232135, by rfl⟩ : syracuseStep 1642847 = 2464271) B2464271
theorem B5189993 : Blo 1536465 5189993 := bstep (se 2 (by rfl) ⟨1946247, by rfl⟩ : syracuseStep 5189993 = 3892495) B3892495
theorem B2306411 : Blo 1536465 2306411 := bstep (se 1 (by rfl) ⟨1729808, by rfl⟩ : syracuseStep 2306411 = 3459617) B3459617
theorem B1536475 : Blo 1536465 1536475 := bstep (se 1 (by rfl) ⟨1152356, by rfl⟩ : syracuseStep 1536475 = 2304713) B2304713
theorem B2593289 : Blo 1536465 2593289 := bstep (se 2 (by rfl) ⟨972483, by rfl⟩ : syracuseStep 2593289 = 1944967) B1944967
theorem B1536551 : Blo 1536465 1536551 := bstep (se 1 (by rfl) ⟨1152413, by rfl⟩ : syracuseStep 1536551 = 2304827) B2304827
theorem B1536591 : Blo 1536465 1536591 := bstep (se 1 (by rfl) ⟨1152443, by rfl⟩ : syracuseStep 1536591 = 2304887) B2304887
theorem B2306639 : Blo 1536465 2306639 := bstep (se 1 (by rfl) ⟨1729979, by rfl⟩ : syracuseStep 2306639 = 3459959) B3459959
theorem B1536607 : Blo 1536465 1536607 := bstep (se 1 (by rfl) ⟨1152455, by rfl⟩ : syracuseStep 1536607 = 2304911) B2304911
theorem B1536635 : Blo 1536465 1536635 := bstep (se 1 (by rfl) ⟨1152476, by rfl⟩ : syracuseStep 1536635 = 2304953) B2304953
theorem B2593451 : Blo 1536465 2593451 := bstep (se 1 (by rfl) ⟨1945088, by rfl⟩ : syracuseStep 2593451 = 3890177) B3890177
theorem B15782573 : Blo 1536465 15782573 := bstep (se 3 (by rfl) ⟨2959232, by rfl⟩ : syracuseStep 15782573 = 5918465) B5918465
theorem B1536687 : Blo 1536465 1536687 := bstep (se 1 (by rfl) ⟨1152515, by rfl⟩ : syracuseStep 1536687 = 2305031) B2305031
theorem B1536711 : Blo 1536465 1536711 := bstep (se 1 (by rfl) ⟨1152533, by rfl⟩ : syracuseStep 1536711 = 2305067) B2305067
theorem B2306759 : Blo 1536465 2306759 := bstep (se 1 (by rfl) ⟨1730069, by rfl⟩ : syracuseStep 2306759 = 3460139) B3460139
theorem B1536731 : Blo 1536465 1536731 := bstep (se 1 (by rfl) ⟨1152548, by rfl⟩ : syracuseStep 1536731 = 2305097) B2305097
theorem B9851651 : Blo 1536465 9851651 := bstep (se 1 (by rfl) ⟨7388738, by rfl⟩ : syracuseStep 9851651 = 14777477) B14777477
theorem B7492355 : Blo 1536465 7492355 := bstep (se 1 (by rfl) ⟨5619266, by rfl⟩ : syracuseStep 7492355 = 11238533) B11238533
theorem B1536807 : Blo 1536465 1536807 := bstep (se 1 (by rfl) ⟨1152605, by rfl⟩ : syracuseStep 1536807 = 2305211) B2305211
theorem B8753993 : Blo 1536465 8753993 := bstep (se 2 (by rfl) ⟨3282747, by rfl⟩ : syracuseStep 8753993 = 6565495) B6565495
theorem B1536847 : Blo 1536465 1536847 := bstep (se 1 (by rfl) ⟨1152635, by rfl⟩ : syracuseStep 1536847 = 2305271) B2305271
theorem B1536863 : Blo 1536465 1536863 := bstep (se 1 (by rfl) ⟨1152647, by rfl⟩ : syracuseStep 1536863 = 2305295) B2305295
theorem B2306921 : Blo 1536465 2306921 := bstep (se 2 (by rfl) ⟨865095, by rfl⟩ : syracuseStep 2306921 = 1730191) B1730191
theorem B1536891 : Blo 1536465 1536891 := bstep (se 1 (by rfl) ⟨1152668, by rfl⟩ : syracuseStep 1536891 = 2305337) B2305337
theorem B1536943 : Blo 1536465 1536943 := bstep (se 1 (by rfl) ⟨1152707, by rfl⟩ : syracuseStep 1536943 = 2305415) B2305415
theorem B2306999 : Blo 1536465 2306999 := bstep (se 1 (by rfl) ⟨1730249, by rfl⟩ : syracuseStep 2306999 = 3460499) B3460499
theorem B5190587 : Blo 1536465 5190587 := bstep (se 1 (by rfl) ⟨3892940, by rfl⟩ : syracuseStep 5190587 = 7785881) B7785881
theorem B1536967 : Blo 1536465 1536967 := bstep (se 1 (by rfl) ⟨1152725, by rfl⟩ : syracuseStep 1536967 = 2305451) B2305451
theorem B1536987 : Blo 1536465 1536987 := bstep (se 1 (by rfl) ⟨1152740, by rfl⟩ : syracuseStep 1536987 = 2305481) B2305481
theorem B2307035 : Blo 1536465 2307035 := bstep (se 1 (by rfl) ⟨1730276, by rfl⟩ : syracuseStep 2307035 = 3460553) B3460553
theorem B16626653 : Blo 1536465 16626653 := bstep (se 3 (by rfl) ⟨3117497, by rfl⟩ : syracuseStep 16626653 = 6234995) B6234995
theorem B1946587 : Blo 1536465 1946587 := bstep (se 1 (by rfl) ⟨1459940, by rfl⟩ : syracuseStep 1946587 = 2919881) B2919881
theorem B18691073 : Blo 1536465 18691073 := bstep (se 2 (by rfl) ⟨7009152, by rfl⟩ : syracuseStep 18691073 = 14018305) B14018305
theorem B23999489 : Blo 1536465 23999489 := bstep (se 2 (by rfl) ⟨8999808, by rfl⟩ : syracuseStep 23999489 = 17999617) B17999617
theorem B1537063 : Blo 1536465 1537063 := bstep (se 1 (by rfl) ⟨1152797, by rfl⟩ : syracuseStep 1537063 = 2305595) B2305595
theorem B2593849 : Blo 1536465 2593849 := bstep (se 2 (by rfl) ⟨972693, by rfl⟩ : syracuseStep 2593849 = 1945387) B1945387
theorem B1537103 : Blo 1536465 1537103 := bstep (se 1 (by rfl) ⟨1152827, by rfl⟩ : syracuseStep 1537103 = 2305655) B2305655
theorem B1537119 : Blo 1536465 1537119 := bstep (se 1 (by rfl) ⟨1152839, by rfl⟩ : syracuseStep 1537119 = 2305679) B2305679
theorem B5837939 : Blo 1536465 5837939 := bstep (se 1 (by rfl) ⟨4378454, by rfl⟩ : syracuseStep 5837939 = 8756909) B8756909
theorem B1537147 : Blo 1536465 1537147 := bstep (se 1 (by rfl) ⟨1152860, by rfl⟩ : syracuseStep 1537147 = 2305721) B2305721
theorem B1537199 : Blo 1536465 1537199 := bstep (se 1 (by rfl) ⟨1152899, by rfl⟩ : syracuseStep 1537199 = 2305799) B2305799
theorem B2593991 : Blo 1536465 2593991 := bstep (se 1 (by rfl) ⟨1945493, by rfl⟩ : syracuseStep 2593991 = 3890987) B3890987
theorem B1537223 : Blo 1536465 1537223 := bstep (se 1 (by rfl) ⟨1152917, by rfl⟩ : syracuseStep 1537223 = 2305835) B2305835
theorem B1537243 : Blo 1536465 1537243 := bstep (se 1 (by rfl) ⟨1152932, by rfl⟩ : syracuseStep 1537243 = 2305865) B2305865
theorem B1537319 : Blo 1536465 1537319 := bstep (se 1 (by rfl) ⟨1152989, by rfl⟩ : syracuseStep 1537319 = 2305979) B2305979
theorem B1537359 : Blo 1536465 1537359 := bstep (se 1 (by rfl) ⟨1153019, by rfl⟩ : syracuseStep 1537359 = 2306039) B2306039
theorem B11679065 : Blo 1536465 11679065 := bstep (se 2 (by rfl) ⟨4379649, by rfl⟩ : syracuseStep 11679065 = 8759299) B8759299
theorem B1537375 : Blo 1536465 1537375 := bstep (se 1 (by rfl) ⟨1153031, by rfl⟩ : syracuseStep 1537375 = 2306063) B2306063
theorem B2594153 : Blo 1536465 2594153 := bstep (se 2 (by rfl) ⟨972807, by rfl⟩ : syracuseStep 2594153 = 1945615) B1945615
theorem B1537403 : Blo 1536465 1537403 := bstep (se 1 (by rfl) ⟨1153052, by rfl⟩ : syracuseStep 1537403 = 2306105) B2306105
theorem B19707299 : Blo 1536465 19707299 := bstep (se 1 (by rfl) ⟨14780474, by rfl⟩ : syracuseStep 19707299 = 29560949) B29560949
theorem B1537455 : Blo 1536465 1537455 := bstep (se 1 (by rfl) ⟨1153091, by rfl⟩ : syracuseStep 1537455 = 2306183) B2306183
theorem B2307503 : Blo 1536465 2307503 := bstep (se 1 (by rfl) ⟨1730627, by rfl⟩ : syracuseStep 2307503 = 3461255) B3461255
theorem B1537479 : Blo 1536465 1537479 := bstep (se 1 (by rfl) ⟨1153109, by rfl⟩ : syracuseStep 1537479 = 2306219) B2306219
theorem B1537499 : Blo 1536465 1537499 := bstep (se 1 (by rfl) ⟨1153124, by rfl⟩ : syracuseStep 1537499 = 2306249) B2306249
theorem B2307593 : Blo 1536465 2307593 := bstep (se 2 (by rfl) ⟨865347, by rfl⟩ : syracuseStep 2307593 = 1730695) B1730695
theorem B1537575 : Blo 1536465 1537575 := bstep (se 1 (by rfl) ⟨1153181, by rfl⟩ : syracuseStep 1537575 = 2306363) B2306363
theorem B2307623 : Blo 1536465 2307623 := bstep (se 1 (by rfl) ⟨1730717, by rfl⟩ : syracuseStep 2307623 = 3461435) B3461435
theorem B1537615 : Blo 1536465 1537615 := bstep (se 1 (by rfl) ⟨1153211, by rfl⟩ : syracuseStep 1537615 = 2306423) B2306423
theorem B1537631 : Blo 1536465 1537631 := bstep (se 1 (by rfl) ⟨1153223, by rfl⟩ : syracuseStep 1537631 = 2306447) B2306447
theorem B1537659 : Blo 1536465 1537659 := bstep (se 1 (by rfl) ⟨1153244, by rfl⟩ : syracuseStep 1537659 = 2306489) B2306489
theorem B9344659 : Blo 1536465 9344659 := bstep (se 1 (by rfl) ⟨7008494, by rfl⟩ : syracuseStep 9344659 = 14016989) B14016989
theorem B18953875 : Blo 1536465 18953875 := bstep (se 1 (by rfl) ⟨14215406, by rfl⟩ : syracuseStep 18953875 = 28430813) B28430813
theorem B1537711 : Blo 1536465 1537711 := bstep (se 1 (by rfl) ⟨1153283, by rfl⟩ : syracuseStep 1537711 = 2306567) B2306567
theorem B19691201 : Blo 1536465 19691201 := bstep (se 2 (by rfl) ⟨7384200, by rfl⟩ : syracuseStep 19691201 = 14768401) B14768401
theorem B1537735 : Blo 1536465 1537735 := bstep (se 1 (by rfl) ⟨1153301, by rfl⟩ : syracuseStep 1537735 = 2306603) B2306603
theorem B1537755 : Blo 1536465 1537755 := bstep (se 1 (by rfl) ⟨1153316, by rfl⟩ : syracuseStep 1537755 = 2306633) B2306633
theorem B2594551 : Blo 1536465 2594551 := bstep (se 1 (by rfl) ⟨1945913, by rfl⟩ : syracuseStep 2594551 = 3891827) B3891827
theorem B11671289 : Blo 1536465 11671289 := bstep (se 2 (by rfl) ⟨4376733, by rfl⟩ : syracuseStep 11671289 = 8753467) B8753467
theorem B1537831 : Blo 1536465 1537831 := bstep (se 1 (by rfl) ⟨1153373, by rfl⟩ : syracuseStep 1537831 = 2306747) B2306747
theorem B1537871 : Blo 1536465 1537871 := bstep (se 1 (by rfl) ⟨1153403, by rfl⟩ : syracuseStep 1537871 = 2306807) B2306807
theorem B1537887 : Blo 1536465 1537887 := bstep (se 1 (by rfl) ⟨1153415, by rfl⟩ : syracuseStep 1537887 = 2306831) B2306831
theorem B1537915 : Blo 1536465 1537915 := bstep (se 1 (by rfl) ⟨1153436, by rfl⟩ : syracuseStep 1537915 = 2306873) B2306873
theorem B1537967 : Blo 1536465 1537967 := bstep (se 1 (by rfl) ⟨1153475, by rfl⟩ : syracuseStep 1537967 = 2306951) B2306951
theorem B2594747 : Blo 1536465 2594747 := bstep (se 1 (by rfl) ⟨1946060, by rfl⟩ : syracuseStep 2594747 = 3892121) B3892121
theorem B1537991 : Blo 1536465 1537991 := bstep (se 1 (by rfl) ⟨1153493, by rfl⟩ : syracuseStep 1537991 = 2306987) B2306987
theorem B1538011 : Blo 1536465 1538011 := bstep (se 1 (by rfl) ⟨1153508, by rfl⟩ : syracuseStep 1538011 = 2307017) B2307017
theorem B2463707 : Blo 1536465 2463707 := bstep (se 1 (by rfl) ⟨1847780, by rfl⟩ : syracuseStep 2463707 = 3695561) B3695561
theorem B2594855 : Blo 1536465 2594855 := bstep (se 1 (by rfl) ⟨1946141, by rfl⟩ : syracuseStep 2594855 = 3892283) B3892283
theorem B1538087 : Blo 1536465 1538087 := bstep (se 1 (by rfl) ⟨1153565, by rfl⟩ : syracuseStep 1538087 = 2307131) B2307131
theorem B3848249 : Blo 1536465 3848249 := bstep (se 2 (by rfl) ⟨1443093, by rfl⟩ : syracuseStep 3848249 = 2886187) B2886187
theorem B1538127 : Blo 1536465 1538127 := bstep (se 1 (by rfl) ⟨1153595, by rfl⟩ : syracuseStep 1538127 = 2307191) B2307191
theorem B1538143 : Blo 1536465 1538143 := bstep (se 1 (by rfl) ⟨1153607, by rfl⟩ : syracuseStep 1538143 = 2307215) B2307215
theorem B1538171 : Blo 1536465 1538171 := bstep (se 1 (by rfl) ⟨1153628, by rfl⟩ : syracuseStep 1538171 = 2307257) B2307257
theorem B1538223 : Blo 1536465 1538223 := bstep (se 1 (by rfl) ⟨1153667, by rfl⟩ : syracuseStep 1538223 = 2307335) B2307335
theorem B1538247 : Blo 1536465 1538247 := bstep (se 1 (by rfl) ⟨1153685, by rfl⟩ : syracuseStep 1538247 = 2307371) B2307371
theorem B1538267 : Blo 1536465 1538267 := bstep (se 1 (by rfl) ⟨1153700, by rfl⟩ : syracuseStep 1538267 = 2307401) B2307401
theorem B1538343 : Blo 1536465 1538343 := bstep (se 1 (by rfl) ⟨1153757, by rfl⟩ : syracuseStep 1538343 = 2307515) B2307515
theorem B2595145 : Blo 1536465 2595145 := bstep (se 2 (by rfl) ⟨973179, by rfl⟩ : syracuseStep 2595145 = 1946359) B1946359
theorem B1538383 : Blo 1536465 1538383 := bstep (se 1 (by rfl) ⟨1153787, by rfl⟩ : syracuseStep 1538383 = 2307575) B2307575
theorem B1538399 : Blo 1536465 1538399 := bstep (se 1 (by rfl) ⟨1153799, by rfl⟩ : syracuseStep 1538399 = 2307599) B2307599
theorem B2595179 : Blo 1536465 2595179 := bstep (se 1 (by rfl) ⟨1946384, by rfl⟩ : syracuseStep 2595179 = 3892769) B3892769
theorem B1538427 : Blo 1536465 1538427 := bstep (se 1 (by rfl) ⟨1153820, by rfl⟩ : syracuseStep 1538427 = 2307641) B2307641
theorem B5839229 : Blo 1536465 5839229 := bstep (se 3 (by rfl) ⟨1094855, by rfl⟩ : syracuseStep 5839229 = 2189711) B2189711
theorem B26614253 : Blo 1536465 26614253 := bstep (se 3 (by rfl) ⟨4990172, by rfl⟩ : syracuseStep 26614253 = 9980345) B9980345
theorem B5192315 : Blo 1536465 5192315 := bstep (se 1 (by rfl) ⟨3894236, by rfl⟩ : syracuseStep 5192315 = 7788473) B7788473
theorem B2595577 : Blo 1536465 2595577 := bstep (se 2 (by rfl) ⟨973341, by rfl⟩ : syracuseStep 2595577 = 1946683) B1946683
theorem B3890015 : Blo 1536465 3890015 := bstep (se 1 (by rfl) ⟨2917511, by rfl⟩ : syracuseStep 3890015 = 5835023) B5835023
theorem B426031973 : Blo 1536465 426031973 := bstep (se 4 (by rfl) ⟨39940497, by rfl⟩ : syracuseStep 426031973 = 79880995) B79880995
theorem B3160937 : Blo 1536465 3160937 := bstep (se 2 (by rfl) ⟨1185351, by rfl⟩ : syracuseStep 3160937 = 2370703) B2370703
theorem B2595847 : Blo 1536465 2595847 := bstep (se 1 (by rfl) ⟨1946885, by rfl⟩ : syracuseStep 2595847 = 3893771) B3893771
theorem B26278991 : Blo 1536465 26278991 := bstep (se 1 (by rfl) ⟨19709243, by rfl⟩ : syracuseStep 26278991 = 39418487) B39418487
theorem B11672747 : Blo 1536465 11672747 := bstep (se 1 (by rfl) ⟨8754560, by rfl⟩ : syracuseStep 11672747 = 17509121) B17509121
theorem B3890713 : Blo 1536465 3890713 := bstep (se 2 (by rfl) ⟨1459017, by rfl⟩ : syracuseStep 3890713 = 2918035) B2918035
theorem B3694177 : Blo 1536465 3694177 := bstep (se 2 (by rfl) ⟨1385316, by rfl⟩ : syracuseStep 3694177 = 2770633) B2770633
theorem B11673233 : Blo 1536465 11673233 := bstep (se 2 (by rfl) ⟨4377462, by rfl⟩ : syracuseStep 11673233 = 8754925) B8754925
theorem B6659783 : Blo 1536465 6659783 := bstep (se 1 (by rfl) ⟨4994837, by rfl⟩ : syracuseStep 6659783 = 9989675) B9989675
theorem B11681495 : Blo 1536465 11681495 := bstep (se 1 (by rfl) ⟨8761121, by rfl⟩ : syracuseStep 11681495 = 17522243) B17522243
theorem B9354973 : Blo 1536465 9354973 := bstep (se 3 (by rfl) ⟨1754057, by rfl⟩ : syracuseStep 9354973 = 3508115) B3508115
theorem B5259001 : Blo 1536465 5259001 := bstep (se 2 (by rfl) ⟨1972125, by rfl⟩ : syracuseStep 5259001 = 3944251) B3944251
theorem B29556485 : Blo 1536465 29556485 := bstep (se 4 (by rfl) ⟨2770920, by rfl⟩ : syracuseStep 29556485 = 5541841) B5541841
theorem B3891017 : Blo 1536465 3891017 := bstep (se 2 (by rfl) ⟨1459131, by rfl⟩ : syracuseStep 3891017 = 2918263) B2918263
theorem B5914463 : Blo 1536465 5914463 := bstep (se 1 (by rfl) ⟨4435847, by rfl⟩ : syracuseStep 5914463 = 8871695) B8871695
theorem B42647651 : Blo 1536465 42647651 := bstep (se 1 (by rfl) ⟨31985738, by rfl⟩ : syracuseStep 42647651 = 63971477) B63971477
theorem B11673719 : Blo 1536465 11673719 := bstep (se 1 (by rfl) ⟨8755289, by rfl⟩ : syracuseStep 11673719 = 17510579) B17510579
theorem B39379121 : Blo 1536465 39379121 := bstep (se 2 (by rfl) ⟨14767170, by rfl⟩ : syracuseStep 39379121 = 29534341) B29534341
theorem B6570193 : Blo 1536465 6570193 := bstep (se 2 (by rfl) ⟨2463822, by rfl⟩ : syracuseStep 6570193 = 4927645) B4927645
theorem B1728859 : Blo 1536465 1728859 := bstep (se 1 (by rfl) ⟨1296644, by rfl⟩ : syracuseStep 1728859 = 2593289) B2593289
theorem B1728967 : Blo 1536465 1728967 := bstep (se 1 (by rfl) ⟨1296725, by rfl⟩ : syracuseStep 1728967 = 2593451) B2593451
theorem B14770633 : Blo 1536465 14770633 := bstep (se 2 (by rfl) ⟨5538987, by rfl⟩ : syracuseStep 14770633 = 11077975) B11077975
theorem B9847241 : Blo 1536465 9847241 := bstep (se 2 (by rfl) ⟨3692715, by rfl⟩ : syracuseStep 9847241 = 7385431) B7385431
theorem B11084435 : Blo 1536465 11084435 := bstep (se 1 (by rfl) ⟨8313326, by rfl⟩ : syracuseStep 11084435 = 16626653) B16626653
theorem B12460715 : Blo 1536465 12460715 := bstep (se 1 (by rfl) ⟨9345536, by rfl⟩ : syracuseStep 12460715 = 18691073) B18691073
theorem B15999659 : Blo 1536465 15999659 := bstep (se 1 (by rfl) ⟨11999744, by rfl⟩ : syracuseStep 15999659 = 23999489) B23999489
theorem B16614071 : Blo 1536465 16614071 := bstep (se 1 (by rfl) ⟨12460553, by rfl⟩ : syracuseStep 16614071 = 24921107) B24921107
theorem B7783127 : Blo 1536465 7783127 := bstep (se 1 (by rfl) ⟨5837345, by rfl⟩ : syracuseStep 7783127 = 11674691) B11674691
theorem B5538527 : Blo 1536465 5538527 := bstep (se 1 (by rfl) ⟨4153895, by rfl⟩ : syracuseStep 5538527 = 8307791) B8307791
theorem B3891959 : Blo 1536465 3891959 := bstep (se 1 (by rfl) ⟨2918969, by rfl⟩ : syracuseStep 3891959 = 5837939) B5837939
theorem B1729327 : Blo 1536465 1729327 := bstep (se 1 (by rfl) ⟨1296995, by rfl⟩ : syracuseStep 1729327 = 2593991) B2593991
theorem B3457871 : Blo 1536465 3457871 := bstep (se 1 (by rfl) ⟨2593403, by rfl⟩ : syracuseStep 3457871 = 5186807) B5186807
theorem B1729435 : Blo 1536465 1729435 := bstep (se 1 (by rfl) ⟨1297076, by rfl⟩ : syracuseStep 1729435 = 2594153) B2594153
theorem B2917291 : Blo 1536465 2917291 := bstep (se 1 (by rfl) ⟨2187968, by rfl⟩ : syracuseStep 2917291 = 4375937) B4375937
theorem B63087605 : Blo 1536465 63087605 := bstep (se 5 (by rfl) ⟨2957231, by rfl⟩ : syracuseStep 63087605 = 5914463) B5914463
theorem B2917367 : Blo 1536465 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B17523701 : Blo 1536465 17523701 := bstep (se 5 (by rfl) ⟨821423, by rfl⟩ : syracuseStep 17523701 = 1642847) B1642847
theorem B59884555 : Blo 1536465 59884555 := bstep (se 1 (by rfl) ⟨44913416, by rfl⟩ : syracuseStep 59884555 = 89826833) B89826833
theorem B3458087 : Blo 1536465 3458087 := bstep (se 1 (by rfl) ⟨2593565, by rfl⟩ : syracuseStep 3458087 = 5187131) B5187131
theorem B5833853 : Blo 1536465 5833853 := bstep (se 3 (by rfl) ⟨1093847, by rfl⟩ : syracuseStep 5833853 = 2187695) B2187695
theorem B6571151 : Blo 1536465 6571151 := bstep (se 1 (by rfl) ⟨4928363, by rfl⟩ : syracuseStep 6571151 = 9856727) B9856727
theorem B2917595 : Blo 1536465 2917595 := bstep (se 1 (by rfl) ⟨2188196, by rfl⟩ : syracuseStep 2917595 = 4376393) B4376393
theorem B3458267 : Blo 1536465 3458267 := bstep (se 1 (by rfl) ⟨2593700, by rfl⟩ : syracuseStep 3458267 = 5187401) B5187401
theorem B1729831 : Blo 1536465 1729831 := bstep (se 1 (by rfl) ⟨1297373, by rfl⟩ : syracuseStep 1729831 = 2594747) B2594747
theorem B4375903 : Blo 1536465 4375903 := bstep (se 1 (by rfl) ⟨3281927, by rfl⟩ : syracuseStep 4375903 = 6563855) B6563855
theorem B7783775 : Blo 1536465 7783775 := bstep (se 1 (by rfl) ⟨5837831, by rfl⟩ : syracuseStep 7783775 = 11675663) B11675663
theorem B1729903 : Blo 1536465 1729903 := bstep (se 1 (by rfl) ⟨1297427, by rfl⟩ : syracuseStep 1729903 = 2594855) B2594855
theorem B3458465 : Blo 1536465 3458465 := bstep (se 2 (by rfl) ⟨1296924, by rfl⟩ : syracuseStep 3458465 = 2593849) B2593849
theorem B1730119 : Blo 1536465 1730119 := bstep (se 1 (by rfl) ⟨1297589, by rfl⟩ : syracuseStep 1730119 = 2595179) B2595179
theorem B3892819 : Blo 1536465 3892819 := bstep (se 1 (by rfl) ⟨2919614, by rfl⟩ : syracuseStep 3892819 = 5839229) B5839229
theorem B5834551 : Blo 1536465 5834551 := bstep (se 1 (by rfl) ⟨4375913, by rfl⟩ : syracuseStep 5834551 = 8751827) B8751827
theorem B2107291 : Blo 1536465 2107291 := bstep (se 1 (by rfl) ⟨1580468, by rfl⟩ : syracuseStep 2107291 = 3160937) B3160937
theorem B3459023 : Blo 1536465 3459023 := bstep (se 1 (by rfl) ⟨2594267, by rfl⟩ : syracuseStep 3459023 = 5188535) B5188535
theorem B5187617 : Blo 1536465 5187617 := bstep (se 2 (by rfl) ⟨1945356, by rfl⟩ : syracuseStep 5187617 = 3890713) B3890713
theorem B4925569 : Blo 1536465 4925569 := bstep (se 2 (by rfl) ⟨1847088, by rfl⟩ : syracuseStep 4925569 = 3694177) B3694177
theorem B14772401 : Blo 1536465 14772401 := bstep (se 2 (by rfl) ⟨5539650, by rfl⟩ : syracuseStep 14772401 = 11079301) B11079301
theorem B5835037 : Blo 1536465 5835037 := bstep (se 3 (by rfl) ⟨1094069, by rfl⟩ : syracuseStep 5835037 = 2188139) B2188139
theorem B3459401 : Blo 1536465 3459401 := bstep (se 2 (by rfl) ⟨1297275, by rfl⟩ : syracuseStep 3459401 = 2594551) B2594551
theorem B3508553 : Blo 1536465 3508553 := bstep (se 2 (by rfl) ⟨1315707, by rfl⟩ : syracuseStep 3508553 = 2631415) B2631415
theorem B3459419 : Blo 1536465 3459419 := bstep (se 1 (by rfl) ⟨2594564, by rfl⟩ : syracuseStep 3459419 = 5189129) B5189129
theorem B1640827 : Blo 1536465 1640827 := bstep (se 1 (by rfl) ⟨1230620, by rfl⟩ : syracuseStep 1640827 = 2461241) B2461241
theorem B19704323 : Blo 1536465 19704323 := bstep (se 1 (by rfl) ⟨14778242, by rfl⟩ : syracuseStep 19704323 = 29556485) B29556485
theorem B2337455 : Blo 1536465 2337455 := bstep (se 1 (by rfl) ⟨1753091, by rfl⟩ : syracuseStep 2337455 = 3506183) B3506183
theorem B2190007 : Blo 1536465 2190007 := bstep (se 1 (by rfl) ⟨1642505, by rfl⟩ : syracuseStep 2190007 = 3285011) B3285011
theorem B20253473 : Blo 1536465 20253473 := bstep (se 2 (by rfl) ⟨7595052, by rfl⟩ : syracuseStep 20253473 = 15190105) B15190105
theorem B3894095 : Blo 1536465 3894095 := bstep (se 1 (by rfl) ⟨2920571, by rfl⟩ : syracuseStep 3894095 = 5841143) B5841143
theorem B2304923 : Blo 1536465 2304923 := bstep (se 1 (by rfl) ⟨1728692, by rfl⟩ : syracuseStep 2304923 = 3457385) B3457385
theorem B3459995 : Blo 1536465 3459995 := bstep (se 1 (by rfl) ⟨2594996, by rfl⟩ : syracuseStep 3459995 = 5189993) B5189993
theorem B2190235 : Blo 1536465 2190235 := bstep (se 1 (by rfl) ⟨1642676, by rfl⟩ : syracuseStep 2190235 = 3285353) B3285353
theorem B3460193 : Blo 1536465 3460193 := bstep (se 2 (by rfl) ⟨1297572, by rfl⟩ : syracuseStep 3460193 = 2595145) B2595145
theorem B6319243 : Blo 1536465 6319243 := bstep (se 1 (by rfl) ⟨4739432, by rfl⟩ : syracuseStep 6319243 = 9478865) B9478865
theorem B4156555 : Blo 1536465 4156555 := bstep (se 1 (by rfl) ⟨3117416, by rfl⟩ : syracuseStep 4156555 = 6234833) B6234833
theorem B5835995 : Blo 1536465 5835995 := bstep (se 1 (by rfl) ⟨4376996, by rfl⟩ : syracuseStep 5835995 = 8753993) B8753993
theorem B2305319 : Blo 1536465 2305319 := bstep (se 1 (by rfl) ⟨1728989, by rfl⟩ : syracuseStep 2305319 = 3457979) B3457979
theorem B3460391 : Blo 1536465 3460391 := bstep (se 1 (by rfl) ⟨2595293, by rfl⟩ : syracuseStep 3460391 = 5190587) B5190587
theorem B2305403 : Blo 1536465 2305403 := bstep (se 1 (by rfl) ⟨1729052, by rfl⟩ : syracuseStep 2305403 = 3458105) B3458105
theorem B2305529 : Blo 1536465 2305529 := bstep (se 2 (by rfl) ⟨864573, by rfl⟩ : syracuseStep 2305529 = 1729147) B1729147
theorem B7786043 : Blo 1536465 7786043 := bstep (se 1 (by rfl) ⟨5839532, by rfl⟩ : syracuseStep 7786043 = 11679065) B11679065
theorem B2305631 : Blo 1536465 2305631 := bstep (se 1 (by rfl) ⟨1729223, by rfl⟩ : syracuseStep 2305631 = 3458447) B3458447
theorem B3460769 : Blo 1536465 3460769 := bstep (se 2 (by rfl) ⟨1297788, by rfl⟩ : syracuseStep 3460769 = 2595577) B2595577
theorem B13127467 : Blo 1536465 13127467 := bstep (se 1 (by rfl) ⟨9845600, by rfl⟩ : syracuseStep 13127467 = 19691201) B19691201
theorem B2305847 : Blo 1536465 2305847 := bstep (se 1 (by rfl) ⟨1729385, by rfl⟩ : syracuseStep 2305847 = 3458771) B3458771
theorem B3461129 : Blo 1536465 3461129 := bstep (se 2 (by rfl) ⟨1297923, by rfl⟩ : syracuseStep 3461129 = 2595847) B2595847
theorem B2306153 : Blo 1536465 2306153 := bstep (se 2 (by rfl) ⟨864807, by rfl⟩ : syracuseStep 2306153 = 1729615) B1729615
theorem B74805515 : Blo 1536465 74805515 := bstep (se 1 (by rfl) ⟨56104136, by rfl⟩ : syracuseStep 74805515 = 112208273) B112208273
theorem B2306471 : Blo 1536465 2306471 := bstep (se 1 (by rfl) ⟨1729853, by rfl⟩ : syracuseStep 2306471 = 3459707) B3459707
theorem B3461543 : Blo 1536465 3461543 := bstep (se 1 (by rfl) ⟨2596157, by rfl⟩ : syracuseStep 3461543 = 5192315) B5192315
theorem B42086861 : Blo 1536465 42086861 := bstep (se 3 (by rfl) ⟨7891286, by rfl⟩ : syracuseStep 42086861 = 15782573) B15782573
theorem B1536507 : Blo 1536465 1536507 := bstep (se 1 (by rfl) ⟨1152380, by rfl⟩ : syracuseStep 1536507 = 2304761) B2304761
theorem B2306555 : Blo 1536465 2306555 := bstep (se 1 (by rfl) ⟨1729916, by rfl⟩ : syracuseStep 2306555 = 3459833) B3459833
theorem B1536575 : Blo 1536465 1536575 := bstep (se 1 (by rfl) ⟨1152431, by rfl⟩ : syracuseStep 1536575 = 2304863) B2304863
theorem B2593343 : Blo 1536465 2593343 := bstep (se 1 (by rfl) ⟨1945007, by rfl⟩ : syracuseStep 2593343 = 3890015) B3890015
theorem B284021315 : Blo 1536465 284021315 := bstep (se 1 (by rfl) ⟨213015986, by rfl⟩ : syracuseStep 284021315 = 426031973) B426031973
theorem B1536583 : Blo 1536465 1536583 := bstep (se 1 (by rfl) ⟨1152437, by rfl⟩ : syracuseStep 1536583 = 2304875) B2304875
theorem B1946207 : Blo 1536465 1946207 := bstep (se 1 (by rfl) ⟨1459655, by rfl⟩ : syracuseStep 1946207 = 2919311) B2919311
theorem B2306681 : Blo 1536465 2306681 := bstep (se 2 (by rfl) ⟨865005, by rfl⟩ : syracuseStep 2306681 = 1730011) B1730011
theorem B2306735 : Blo 1536465 2306735 := bstep (se 1 (by rfl) ⟨1730051, by rfl⟩ : syracuseStep 2306735 = 3460103) B3460103
theorem B1536735 : Blo 1536465 1536735 := bstep (se 1 (by rfl) ⟨1152551, by rfl⟩ : syracuseStep 1536735 = 2305103) B2305103
theorem B2306783 : Blo 1536465 2306783 := bstep (se 1 (by rfl) ⟨1730087, by rfl⟩ : syracuseStep 2306783 = 3460175) B3460175
theorem B17519327 : Blo 1536465 17519327 := bstep (se 1 (by rfl) ⟨13139495, by rfl⟩ : syracuseStep 17519327 = 26278991) B26278991
theorem B7107371 : Blo 1536465 7107371 := bstep (se 1 (by rfl) ⟨5330528, by rfl⟩ : syracuseStep 7107371 = 10661057) B10661057
theorem B1536815 : Blo 1536465 1536815 := bstep (se 1 (by rfl) ⟨1152611, by rfl⟩ : syracuseStep 1536815 = 2305223) B2305223
theorem B5190479 : Blo 1536465 5190479 := bstep (se 1 (by rfl) ⟨3892859, by rfl⟩ : syracuseStep 5190479 = 7785719) B7785719
theorem B1536923 : Blo 1536465 1536923 := bstep (se 1 (by rfl) ⟨1152692, by rfl⟩ : syracuseStep 1536923 = 2305385) B2305385
theorem B1536975 : Blo 1536465 1536975 := bstep (se 1 (by rfl) ⟨1152731, by rfl⟩ : syracuseStep 1536975 = 2305463) B2305463
theorem B12473297 : Blo 1536465 12473297 := bstep (se 2 (by rfl) ⟨4677486, by rfl⟩ : syracuseStep 12473297 = 9354973) B9354973
theorem B1536999 : Blo 1536465 1536999 := bstep (se 1 (by rfl) ⟨1152749, by rfl⟩ : syracuseStep 1536999 = 2305499) B2305499
theorem B2307047 : Blo 1536465 2307047 := bstep (se 1 (by rfl) ⟨1730285, by rfl⟩ : syracuseStep 2307047 = 3460571) B3460571
theorem B7017529 : Blo 1536465 7017529 := bstep (se 2 (by rfl) ⟨2631573, by rfl⟩ : syracuseStep 7017529 = 5263147) B5263147
theorem B7787663 : Blo 1536465 7787663 := bstep (se 1 (by rfl) ⟨5840747, by rfl⟩ : syracuseStep 7787663 = 11681495) B11681495
theorem B5190803 : Blo 1536465 5190803 := bstep (se 1 (by rfl) ⟨3893102, by rfl⟩ : syracuseStep 5190803 = 7786205) B7786205
theorem B5403847 : Blo 1536465 5403847 := bstep (se 1 (by rfl) ⟨4052885, by rfl⟩ : syracuseStep 5403847 = 8105771) B8105771
theorem B2594011 : Blo 1536465 2594011 := bstep (se 1 (by rfl) ⟨1945508, by rfl⟩ : syracuseStep 2594011 = 3891017) B3891017
theorem B5256425 : Blo 1536465 5256425 := bstep (se 2 (by rfl) ⟨1971159, by rfl⟩ : syracuseStep 5256425 = 3942319) B3942319
theorem B2307305 : Blo 1536465 2307305 := bstep (se 2 (by rfl) ⟨865239, by rfl⟩ : syracuseStep 2307305 = 1730479) B1730479
theorem B8754425 : Blo 1536465 8754425 := bstep (se 2 (by rfl) ⟨3282909, by rfl⟩ : syracuseStep 8754425 = 6565819) B6565819
theorem B1537311 : Blo 1536465 1537311 := bstep (se 1 (by rfl) ⟨1152983, by rfl⟩ : syracuseStep 1537311 = 2305967) B2305967
theorem B2307359 : Blo 1536465 2307359 := bstep (se 1 (by rfl) ⟨1730519, by rfl⟩ : syracuseStep 2307359 = 3461039) B3461039
theorem B1946911 : Blo 1536465 1946911 := bstep (se 1 (by rfl) ⟨1460183, by rfl⟩ : syracuseStep 1946911 = 2920367) B2920367
theorem B1537371 : Blo 1536465 1537371 := bstep (se 1 (by rfl) ⟨1153028, by rfl⟩ : syracuseStep 1537371 = 2306057) B2306057
theorem B3691871 : Blo 1536465 3691871 := bstep (se 1 (by rfl) ⟨2768903, by rfl⟩ : syracuseStep 3691871 = 5537807) B5537807
theorem B1537391 : Blo 1536465 1537391 := bstep (se 1 (by rfl) ⟨1153043, by rfl⟩ : syracuseStep 1537391 = 2306087) B2306087
theorem B7386491 : Blo 1536465 7386491 := bstep (se 1 (by rfl) ⟨5539868, by rfl⟩ : syracuseStep 7386491 = 11079737) B11079737
theorem B5191073 : Blo 1536465 5191073 := bstep (se 2 (by rfl) ⟨1946652, by rfl⟩ : syracuseStep 5191073 = 3893305) B3893305
theorem B1537447 : Blo 1536465 1537447 := bstep (se 1 (by rfl) ⟨1153085, by rfl⟩ : syracuseStep 1537447 = 2306171) B2306171
theorem B2307527 : Blo 1536465 2307527 := bstep (se 1 (by rfl) ⟨1730645, by rfl⟩ : syracuseStep 2307527 = 3461291) B3461291
theorem B10261997 : Blo 1536465 10261997 := bstep (se 3 (by rfl) ⟨1924124, by rfl⟩ : syracuseStep 10261997 = 3848249) B3848249
theorem B1537531 : Blo 1536465 1537531 := bstep (se 1 (by rfl) ⟨1153148, by rfl⟩ : syracuseStep 1537531 = 2306297) B2306297
theorem B4675079 : Blo 1536465 4675079 := bstep (se 1 (by rfl) ⟨3506309, by rfl⟩ : syracuseStep 4675079 = 7012619) B7012619
theorem B1537599 : Blo 1536465 1537599 := bstep (se 1 (by rfl) ⟨1153199, by rfl⟩ : syracuseStep 1537599 = 2306399) B2306399
theorem B1537607 : Blo 1536465 1537607 := bstep (se 1 (by rfl) ⟨1153205, by rfl⟩ : syracuseStep 1537607 = 2306411) B2306411
theorem B3282619 : Blo 1536465 3282619 := bstep (se 1 (by rfl) ⟨2461964, by rfl⟩ : syracuseStep 3282619 = 4923929) B4923929
theorem B1537759 : Blo 1536465 1537759 := bstep (se 1 (by rfl) ⟨1153319, by rfl⟩ : syracuseStep 1537759 = 2306639) B2306639
theorem B1537839 : Blo 1536465 1537839 := bstep (se 1 (by rfl) ⟨1153379, by rfl⟩ : syracuseStep 1537839 = 2306759) B2306759
theorem B6567767 : Blo 1536465 6567767 := bstep (se 1 (by rfl) ⟨4925825, by rfl⟩ : syracuseStep 6567767 = 9851651) B9851651
theorem B4994903 : Blo 1536465 4994903 := bstep (se 1 (by rfl) ⟨3746177, by rfl⟩ : syracuseStep 4994903 = 7492355) B7492355
theorem B1537947 : Blo 1536465 1537947 := bstep (se 1 (by rfl) ⟨1153460, by rfl⟩ : syracuseStep 1537947 = 2306921) B2306921
theorem B2594767 : Blo 1536465 2594767 := bstep (se 1 (by rfl) ⟨1946075, by rfl⟩ : syracuseStep 2594767 = 3892151) B3892151
theorem B1537999 : Blo 1536465 1537999 := bstep (se 1 (by rfl) ⟨1153499, by rfl⟩ : syracuseStep 1537999 = 2306999) B2306999
theorem B1538023 : Blo 1536465 1538023 := bstep (se 1 (by rfl) ⟨1153517, by rfl⟩ : syracuseStep 1538023 = 2307035) B2307035
theorem B3889417 : Blo 1536465 3889417 := bstep (se 2 (by rfl) ⟨1458531, by rfl⟩ : syracuseStep 3889417 = 2917063) B2917063
theorem B13138199 : Blo 1536465 13138199 := bstep (se 1 (by rfl) ⟨9853649, by rfl⟩ : syracuseStep 13138199 = 19707299) B19707299
theorem B1538335 : Blo 1536465 1538335 := bstep (se 1 (by rfl) ⟨1153751, by rfl⟩ : syracuseStep 1538335 = 2307503) B2307503
theorem B1538395 : Blo 1536465 1538395 := bstep (se 1 (by rfl) ⟨1153796, by rfl⟩ : syracuseStep 1538395 = 2307593) B2307593
theorem B2464111 : Blo 1536465 2464111 := bstep (se 1 (by rfl) ⟨1848083, by rfl⟩ : syracuseStep 2464111 = 3696167) B3696167
theorem B1538415 : Blo 1536465 1538415 := bstep (se 1 (by rfl) ⟨1153811, by rfl⟩ : syracuseStep 1538415 = 2307623) B2307623
theorem B7780859 : Blo 1536465 7780859 := bstep (se 1 (by rfl) ⟨5835644, by rfl⟩ : syracuseStep 7780859 = 11671289) B11671289
theorem B2595449 : Blo 1536465 2595449 := bstep (se 2 (by rfl) ⟨973293, by rfl⟩ : syracuseStep 2595449 = 1946587) B1946587
theorem B2595503 : Blo 1536465 2595503 := bstep (se 1 (by rfl) ⟨1946627, by rfl⟩ : syracuseStep 2595503 = 3893255) B3893255
theorem B3283679 : Blo 1536465 3283679 := bstep (se 1 (by rfl) ⟨2462759, by rfl⟩ : syracuseStep 3283679 = 4925519) B4925519
theorem B2595739 : Blo 1536465 2595739 := bstep (se 1 (by rfl) ⟨1946804, by rfl⟩ : syracuseStep 2595739 = 3893609) B3893609
theorem B17742835 : Blo 1536465 17742835 := bstep (se 1 (by rfl) ⟨13307126, by rfl⟩ : syracuseStep 17742835 = 26614253) B26614253
theorem B224386199 : Blo 1536465 224386199 := bstep (se 1 (by rfl) ⟨168289649, by rfl⟩ : syracuseStep 224386199 = 336579299) B336579299
theorem B7781831 : Blo 1536465 7781831 := bstep (se 1 (by rfl) ⟨5836373, by rfl⟩ : syracuseStep 7781831 = 11672747) B11672747
theorem B12459545 : Blo 1536465 12459545 := bstep (se 2 (by rfl) ⟨4672329, by rfl⟩ : syracuseStep 12459545 = 9344659) B9344659
theorem B25271833 : Blo 1536465 25271833 := bstep (se 2 (by rfl) ⟨9476937, by rfl⟩ : syracuseStep 25271833 = 18953875) B18953875
theorem B24927905 : Blo 1536465 24927905 := bstep (se 2 (by rfl) ⟨9347964, by rfl⟩ : syracuseStep 24927905 = 18695929) B18695929
theorem B7012001 : Blo 1536465 7012001 := bstep (se 2 (by rfl) ⟨2629500, by rfl⟩ : syracuseStep 7012001 = 5259001) B5259001
theorem B3890875 : Blo 1536465 3890875 := bstep (se 1 (by rfl) ⟨2918156, by rfl⟩ : syracuseStep 3890875 = 5836313) B5836313
theorem B7782155 : Blo 1536465 7782155 := bstep (se 1 (by rfl) ⟨5836616, by rfl⟩ : syracuseStep 7782155 = 11673233) B11673233
theorem B4439855 : Blo 1536465 4439855 := bstep (se 1 (by rfl) ⟨3329891, by rfl⟩ : syracuseStep 4439855 = 6659783) B6659783
theorem B5840687 : Blo 1536465 5840687 := bstep (se 1 (by rfl) ⟨4380515, by rfl⟩ : syracuseStep 5840687 = 8761031) B8761031
theorem B246267701 : Blo 1536465 246267701 := bstep (se 5 (by rfl) ⟨11543798, by rfl⟩ : syracuseStep 246267701 = 23087597) B23087597
theorem B6569885 : Blo 1536465 6569885 := bstep (se 3 (by rfl) ⟨1231853, by rfl⟩ : syracuseStep 6569885 = 2463707) B2463707
theorem B7782479 : Blo 1536465 7782479 := bstep (se 1 (by rfl) ⟨5836859, by rfl⟩ : syracuseStep 7782479 = 11673719) B11673719
theorem B28057907 : Blo 1536465 28057907 := bstep (se 1 (by rfl) ⟨21043430, by rfl⟩ : syracuseStep 28057907 = 42086861) B42086861
theorem B5185889 : Blo 1536465 5185889 := bstep (se 2 (by rfl) ⟨1944708, by rfl⟩ : syracuseStep 5185889 = 3889417) B3889417
theorem B1728895 : Blo 1536465 1728895 := bstep (se 1 (by rfl) ⟨1296671, by rfl⟩ : syracuseStep 1728895 = 2593343) B2593343
theorem B7389623 : Blo 1536465 7389623 := bstep (se 1 (by rfl) ⟨5542217, by rfl⟩ : syracuseStep 7389623 = 11084435) B11084435
theorem B8307143 : Blo 1536465 8307143 := bstep (se 1 (by rfl) ⟨6230357, by rfl⟩ : syracuseStep 8307143 = 12460715) B12460715
theorem B10666439 : Blo 1536465 10666439 := bstep (se 1 (by rfl) ⟨7999829, by rfl⟩ : syracuseStep 10666439 = 15999659) B15999659
theorem B11076047 : Blo 1536465 11076047 := bstep (se 1 (by rfl) ⟨8307035, by rfl⟩ : syracuseStep 11076047 = 16614071) B16614071
theorem B19694177 : Blo 1536465 19694177 := bstep (se 2 (by rfl) ⟨7385316, by rfl⟩ : syracuseStep 19694177 = 14770633) B14770633
theorem B14017133 : Blo 1536465 14017133 := bstep (se 3 (by rfl) ⟨2628212, by rfl⟩ : syracuseStep 14017133 = 5256425) B5256425
theorem B8315531 : Blo 1536465 8315531 := bstep (se 1 (by rfl) ⟨6236648, by rfl⟩ : syracuseStep 8315531 = 12473297) B12473297
theorem B42058403 : Blo 1536465 42058403 := bstep (se 1 (by rfl) ⟨31543802, by rfl⟩ : syracuseStep 42058403 = 63087605) B63087605
theorem B11682467 : Blo 1536465 11682467 := bstep (se 1 (by rfl) ⟨8761850, by rfl⟩ : syracuseStep 11682467 = 17523701) B17523701
theorem B9356141 : Blo 1536465 9356141 := bstep (se 3 (by rfl) ⟨1754276, by rfl⟩ : syracuseStep 9356141 = 3508553) B3508553
theorem B4924327 : Blo 1536465 4924327 := bstep (se 1 (by rfl) ⟨3693245, by rfl⟩ : syracuseStep 4924327 = 7386491) B7386491
theorem B6841331 : Blo 1536465 6841331 := bstep (se 1 (by rfl) ⟨5130998, by rfl⟩ : syracuseStep 6841331 = 10261997) B10261997
theorem B3458411 : Blo 1536465 3458411 := bstep (se 1 (by rfl) ⟨2593808, by rfl⟩ : syracuseStep 3458411 = 5187617) B5187617
theorem B9356705 : Blo 1536465 9356705 := bstep (se 2 (by rfl) ⟨3508764, by rfl⟩ : syracuseStep 9356705 = 7017529) B7017529
theorem B9848267 : Blo 1536465 9848267 := bstep (se 1 (by rfl) ⟨7386200, by rfl⟩ : syracuseStep 9848267 = 14772401) B14772401
theorem B8758799 : Blo 1536465 8758799 := bstep (se 1 (by rfl) ⟨6569099, by rfl⟩ : syracuseStep 8758799 = 13138199) B13138199
theorem B3458681 : Blo 1536465 3458681 := bstep (se 2 (by rfl) ⟨1297005, by rfl⟩ : syracuseStep 3458681 = 2594011) B2594011
theorem B5187239 : Blo 1536465 5187239 := bstep (se 1 (by rfl) ⟨3890429, by rfl⟩ : syracuseStep 5187239 = 7780859) B7780859
theorem B1730299 : Blo 1536465 1730299 := bstep (se 1 (by rfl) ⟨1297724, by rfl⟩ : syracuseStep 1730299 = 2595449) B2595449
theorem B1730335 : Blo 1536465 1730335 := bstep (se 1 (by rfl) ⟨1297751, by rfl⟩ : syracuseStep 1730335 = 2595503) B2595503
theorem B5834537 : Blo 1536465 5834537 := bstep (se 2 (by rfl) ⟨2187951, by rfl⟩ : syracuseStep 5834537 = 4375903) B4375903
theorem B2189119 : Blo 1536465 2189119 := bstep (se 1 (by rfl) ⟨1641839, by rfl⟩ : syracuseStep 2189119 = 3283679) B3283679
theorem B13502315 : Blo 1536465 13502315 := bstep (se 1 (by rfl) ⟨10126736, by rfl⟩ : syracuseStep 13502315 = 20253473) B20253473
theorem B13141925 : Blo 1536465 13141925 := bstep (se 4 (by rfl) ⟨1232055, by rfl⟩ : syracuseStep 13141925 = 2464111) B2464111
theorem B8751077 : Blo 1536465 8751077 := bstep (se 4 (by rfl) ⟨820413, by rfl⟩ : syracuseStep 8751077 = 1640827) B1640827
theorem B33695777 : Blo 1536465 33695777 := bstep (se 2 (by rfl) ⟨12635916, by rfl⟩ : syracuseStep 33695777 = 25271833) B25271833
theorem B11839613 : Blo 1536465 11839613 := bstep (se 3 (by rfl) ⟨2219927, by rfl⟩ : syracuseStep 11839613 = 4439855) B4439855
theorem B4376825 : Blo 1536465 4376825 := bstep (se 2 (by rfl) ⟨1641309, by rfl⟩ : syracuseStep 4376825 = 3282619) B3282619
theorem B5187833 : Blo 1536465 5187833 := bstep (se 2 (by rfl) ⟨1945437, by rfl⟩ : syracuseStep 5187833 = 3890875) B3890875
theorem B5187887 : Blo 1536465 5187887 := bstep (se 1 (by rfl) ⟨3890915, by rfl⟩ : syracuseStep 5187887 = 7781831) B7781831
theorem B5188103 : Blo 1536465 5188103 := bstep (se 1 (by rfl) ⟨3891077, by rfl⟩ : syracuseStep 5188103 = 7782155) B7782155
theorem B3893791 : Blo 1536465 3893791 := bstep (se 1 (by rfl) ⟨2920343, by rfl⟩ : syracuseStep 3893791 = 5840687) B5840687
theorem B164178467 : Blo 1536465 164178467 := bstep (se 1 (by rfl) ⟨123133850, by rfl⟩ : syracuseStep 164178467 = 246267701) B246267701
theorem B3459689 : Blo 1536465 3459689 := bstep (se 2 (by rfl) ⟨1297383, by rfl⟩ : syracuseStep 3459689 = 2594767) B2594767
theorem B8760257 : Blo 1536465 8760257 := bstep (se 2 (by rfl) ⟨3285096, by rfl⟩ : syracuseStep 8760257 = 6570193) B6570193
theorem B6564827 : Blo 1536465 6564827 := bstep (se 1 (by rfl) ⟨4923620, by rfl⟩ : syracuseStep 6564827 = 9847241) B9847241
theorem B2305145 : Blo 1536465 2305145 := bstep (se 2 (by rfl) ⟨864429, by rfl⟩ : syracuseStep 2305145 = 1728859) B1728859
theorem B5188751 : Blo 1536465 5188751 := bstep (se 1 (by rfl) ⟨3891563, by rfl⟩ : syracuseStep 5188751 = 7783127) B7783127
theorem B4738247 : Blo 1536465 4738247 := bstep (se 1 (by rfl) ⟨3553685, by rfl⟩ : syracuseStep 4738247 = 7107371) B7107371
theorem B2305247 : Blo 1536465 2305247 := bstep (se 1 (by rfl) ⟨1728935, by rfl⟩ : syracuseStep 2305247 = 3457871) B3457871
theorem B3460319 : Blo 1536465 3460319 := bstep (se 1 (by rfl) ⟨2595239, by rfl⟩ : syracuseStep 3460319 = 5190479) B5190479
theorem B2305289 : Blo 1536465 2305289 := bstep (se 2 (by rfl) ⟨864483, by rfl⟩ : syracuseStep 2305289 = 1728967) B1728967
theorem B1944911 : Blo 1536465 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B2305391 : Blo 1536465 2305391 := bstep (se 1 (by rfl) ⟨1729043, by rfl⟩ : syracuseStep 2305391 = 3458087) B3458087
theorem B3460535 : Blo 1536465 3460535 := bstep (se 1 (by rfl) ⟨2595401, by rfl⟩ : syracuseStep 3460535 = 5190803) B5190803
theorem B1945063 : Blo 1536465 1945063 := bstep (se 1 (by rfl) ⟨1458797, by rfl⟩ : syracuseStep 1945063 = 2917595) B2917595
theorem B2305511 : Blo 1536465 2305511 := bstep (se 1 (by rfl) ⟨1729133, by rfl⟩ : syracuseStep 2305511 = 3458267) B3458267
theorem B5836283 : Blo 1536465 5836283 := bstep (se 1 (by rfl) ⟨4377212, by rfl⟩ : syracuseStep 5836283 = 8754425) B8754425
theorem B2461247 : Blo 1536465 2461247 := bstep (se 1 (by rfl) ⟨1845935, by rfl⟩ : syracuseStep 2461247 = 3691871) B3691871
theorem B5189183 : Blo 1536465 5189183 := bstep (se 1 (by rfl) ⟨3891887, by rfl⟩ : syracuseStep 5189183 = 7783775) B7783775
theorem B2305643 : Blo 1536465 2305643 := bstep (se 1 (by rfl) ⟨1729232, by rfl⟩ : syracuseStep 2305643 = 3458465) B3458465
theorem B3460715 : Blo 1536465 3460715 := bstep (se 1 (by rfl) ⟨2595536, by rfl⟩ : syracuseStep 3460715 = 5191073) B5191073
theorem B3116719 : Blo 1536465 3116719 := bstep (se 1 (by rfl) ⟨2337539, by rfl⟩ : syracuseStep 3116719 = 4675079) B4675079
theorem B2305769 : Blo 1536465 2305769 := bstep (se 2 (by rfl) ⟨864663, by rfl⟩ : syracuseStep 2305769 = 1729327) B1729327
theorem B2305913 : Blo 1536465 2305913 := bstep (se 2 (by rfl) ⟨864717, by rfl⟩ : syracuseStep 2305913 = 1729435) B1729435
theorem B3460985 : Blo 1536465 3460985 := bstep (se 2 (by rfl) ⟨1297869, by rfl⟩ : syracuseStep 3460985 = 2595739) B2595739
theorem B2920313 : Blo 1536465 2920313 := bstep (se 2 (by rfl) ⟨1095117, by rfl⟩ : syracuseStep 2920313 = 2190235) B2190235
theorem B4378511 : Blo 1536465 4378511 := bstep (se 1 (by rfl) ⟨3283883, by rfl⟩ : syracuseStep 4378511 = 6567767) B6567767
theorem B2306015 : Blo 1536465 2306015 := bstep (se 1 (by rfl) ⟨1729511, by rfl⟩ : syracuseStep 2306015 = 3459023) B3459023
theorem B8425657 : Blo 1536465 8425657 := bstep (se 2 (by rfl) ⟨3159621, by rfl⟩ : syracuseStep 8425657 = 6319243) B6319243
theorem B5542073 : Blo 1536465 5542073 := bstep (se 2 (by rfl) ⟨2078277, by rfl⟩ : syracuseStep 5542073 = 4156555) B4156555
theorem B2306267 : Blo 1536465 2306267 := bstep (se 1 (by rfl) ⟨1729700, by rfl⟩ : syracuseStep 2306267 = 3459401) B3459401
theorem B2306279 : Blo 1536465 2306279 := bstep (se 1 (by rfl) ⟨1729709, by rfl⟩ : syracuseStep 2306279 = 3459419) B3459419
theorem B5189885 : Blo 1536465 5189885 := bstep (se 3 (by rfl) ⟨973103, by rfl⟩ : syracuseStep 5189885 = 1946207) B1946207
theorem B7205129 : Blo 1536465 7205129 := bstep (se 2 (by rfl) ⟨2701923, by rfl⟩ : syracuseStep 7205129 = 5403847) B5403847
theorem B13136215 : Blo 1536465 13136215 := bstep (se 1 (by rfl) ⟨9852161, by rfl⟩ : syracuseStep 13136215 = 19704323) B19704323
theorem B2306441 : Blo 1536465 2306441 := bstep (se 2 (by rfl) ⟨864915, by rfl⟩ : syracuseStep 2306441 = 1729831) B1729831
theorem B2306537 : Blo 1536465 2306537 := bstep (se 2 (by rfl) ⟨864951, by rfl⟩ : syracuseStep 2306537 = 1729903) B1729903
theorem B1536615 : Blo 1536465 1536615 := bstep (se 1 (by rfl) ⟨1152461, by rfl⟩ : syracuseStep 1536615 = 2304923) B2304923
theorem B2306663 : Blo 1536465 2306663 := bstep (se 1 (by rfl) ⟨1729997, by rfl⟩ : syracuseStep 2306663 = 3459995) B3459995
theorem B2306795 : Blo 1536465 2306795 := bstep (se 1 (by rfl) ⟨1730096, by rfl⟩ : syracuseStep 2306795 = 3460193) B3460193
theorem B2306825 : Blo 1536465 2306825 := bstep (se 2 (by rfl) ⟨865059, by rfl⟩ : syracuseStep 2306825 = 1730119) B1730119
theorem B149590799 : Blo 1536465 149590799 := bstep (se 1 (by rfl) ⟨112193099, by rfl⟩ : syracuseStep 149590799 = 224386199) B224386199
theorem B5190425 : Blo 1536465 5190425 := bstep (se 2 (by rfl) ⟨1946409, by rfl⟩ : syracuseStep 5190425 = 3892819) B3892819
theorem B1536879 : Blo 1536465 1536879 := bstep (se 1 (by rfl) ⟨1152659, by rfl⟩ : syracuseStep 1536879 = 2305319) B2305319
theorem B2306927 : Blo 1536465 2306927 := bstep (se 1 (by rfl) ⟨1730195, by rfl⟩ : syracuseStep 2306927 = 3460391) B3460391
theorem B1536935 : Blo 1536465 1536935 := bstep (se 1 (by rfl) ⟨1152701, by rfl⟩ : syracuseStep 1536935 = 2305403) B2305403
theorem B1537019 : Blo 1536465 1537019 := bstep (se 1 (by rfl) ⟨1152764, by rfl⟩ : syracuseStep 1537019 = 2305529) B2305529
theorem B5190695 : Blo 1536465 5190695 := bstep (se 1 (by rfl) ⟨3893021, by rfl⟩ : syracuseStep 5190695 = 7786043) B7786043
theorem B17503289 : Blo 1536465 17503289 := bstep (se 2 (by rfl) ⟨6563733, by rfl⟩ : syracuseStep 17503289 = 13127467) B13127467
theorem B1537087 : Blo 1536465 1537087 := bstep (se 1 (by rfl) ⟨1152815, by rfl⟩ : syracuseStep 1537087 = 2305631) B2305631
theorem B7779401 : Blo 1536465 7779401 := bstep (se 2 (by rfl) ⟨2917275, by rfl⟩ : syracuseStep 7779401 = 5834551) B5834551
theorem B16618603 : Blo 1536465 16618603 := bstep (se 1 (by rfl) ⟨12463952, by rfl⟩ : syracuseStep 16618603 = 24927905) B24927905
theorem B4674667 : Blo 1536465 4674667 := bstep (se 1 (by rfl) ⟨3506000, by rfl⟩ : syracuseStep 4674667 = 7012001) B7012001
theorem B2307179 : Blo 1536465 2307179 := bstep (se 1 (by rfl) ⟨1730384, by rfl⟩ : syracuseStep 2307179 = 3460769) B3460769
theorem B1537231 : Blo 1536465 1537231 := bstep (se 1 (by rfl) ⟨1152923, by rfl⟩ : syracuseStep 1537231 = 2305847) B2305847
theorem B4379923 : Blo 1536465 4379923 := bstep (se 1 (by rfl) ⟨3284942, by rfl⟩ : syracuseStep 4379923 = 6569885) B6569885
theorem B2307419 : Blo 1536465 2307419 := bstep (se 1 (by rfl) ⟨1730564, by rfl⟩ : syracuseStep 2307419 = 3461129) B3461129
theorem B28431767 : Blo 1536465 28431767 := bstep (se 1 (by rfl) ⟨21323825, by rfl⟩ : syracuseStep 28431767 = 42647651) B42647651
theorem B1537435 : Blo 1536465 1537435 := bstep (se 1 (by rfl) ⟨1153076, by rfl⟩ : syracuseStep 1537435 = 2306153) B2306153
theorem B26252747 : Blo 1536465 26252747 := bstep (se 1 (by rfl) ⟨19689560, by rfl⟩ : syracuseStep 26252747 = 39379121) B39379121
theorem B6567425 : Blo 1536465 6567425 := bstep (se 2 (by rfl) ⟨2462784, by rfl⟩ : syracuseStep 6567425 = 4925569) B4925569
theorem B49870343 : Blo 1536465 49870343 := bstep (se 1 (by rfl) ⟨37402757, by rfl⟩ : syracuseStep 49870343 = 74805515) B74805515
theorem B1537647 : Blo 1536465 1537647 := bstep (se 1 (by rfl) ⟨1153235, by rfl⟩ : syracuseStep 1537647 = 2306471) B2306471
theorem B2307695 : Blo 1536465 2307695 := bstep (se 1 (by rfl) ⟨1730771, by rfl⟩ : syracuseStep 2307695 = 3461543) B3461543
theorem B1537703 : Blo 1536465 1537703 := bstep (se 1 (by rfl) ⟨1153277, by rfl⟩ : syracuseStep 1537703 = 2306555) B2306555
theorem B7780049 : Blo 1536465 7780049 := bstep (se 2 (by rfl) ⟨2917518, by rfl⟩ : syracuseStep 7780049 = 5835037) B5835037
theorem B189347543 : Blo 1536465 189347543 := bstep (se 1 (by rfl) ⟨142010657, by rfl⟩ : syracuseStep 189347543 = 284021315) B284021315
theorem B1537787 : Blo 1536465 1537787 := bstep (se 1 (by rfl) ⟨1153340, by rfl⟩ : syracuseStep 1537787 = 2306681) B2306681
theorem B1537823 : Blo 1536465 1537823 := bstep (se 1 (by rfl) ⟨1153367, by rfl⟩ : syracuseStep 1537823 = 2306735) B2306735
theorem B3692351 : Blo 1536465 3692351 := bstep (se 1 (by rfl) ⟨2769263, by rfl⟩ : syracuseStep 3692351 = 5538527) B5538527
theorem B1537855 : Blo 1536465 1537855 := bstep (se 1 (by rfl) ⟨1153391, by rfl⟩ : syracuseStep 1537855 = 2306783) B2306783
theorem B11679551 : Blo 1536465 11679551 := bstep (se 1 (by rfl) ⟨8759663, by rfl⟩ : syracuseStep 11679551 = 17519327) B17519327
theorem B2594639 : Blo 1536465 2594639 := bstep (se 1 (by rfl) ⟨1945979, by rfl⟩ : syracuseStep 2594639 = 3891959) B3891959
theorem B1538031 : Blo 1536465 1538031 := bstep (se 1 (by rfl) ⟨1153523, by rfl⟩ : syracuseStep 1538031 = 2307047) B2307047
theorem B3889235 : Blo 1536465 3889235 := bstep (se 1 (by rfl) ⟨2916926, by rfl⟩ : syracuseStep 3889235 = 5833853) B5833853
theorem B5191775 : Blo 1536465 5191775 := bstep (se 1 (by rfl) ⟨3893831, by rfl⟩ : syracuseStep 5191775 = 7787663) B7787663
theorem B4380767 : Blo 1536465 4380767 := bstep (se 1 (by rfl) ⟨3285575, by rfl⟩ : syracuseStep 4380767 = 6571151) B6571151
theorem B1538203 : Blo 1536465 1538203 := bstep (se 1 (by rfl) ⟨1153652, by rfl⟩ : syracuseStep 1538203 = 2307305) B2307305
theorem B1538239 : Blo 1536465 1538239 := bstep (se 1 (by rfl) ⟨1153679, by rfl⟩ : syracuseStep 1538239 = 2307359) B2307359
theorem B11680037 : Blo 1536465 11680037 := bstep (se 4 (by rfl) ⟨1095003, by rfl⟩ : syracuseStep 11680037 = 2190007) B2190007
theorem B1538351 : Blo 1536465 1538351 := bstep (se 1 (by rfl) ⟨1153763, by rfl⟩ : syracuseStep 1538351 = 2307527) B2307527
theorem B3889721 : Blo 1536465 3889721 := bstep (se 2 (by rfl) ⟨1458645, by rfl⟩ : syracuseStep 3889721 = 2917291) B2917291
theorem B23657113 : Blo 1536465 23657113 := bstep (se 2 (by rfl) ⟨8871417, by rfl⟩ : syracuseStep 23657113 = 17742835) B17742835
theorem B79846073 : Blo 1536465 79846073 := bstep (se 2 (by rfl) ⟨29942277, by rfl⟩ : syracuseStep 79846073 = 59884555) B59884555
theorem B2595881 : Blo 1536465 2595881 := bstep (se 2 (by rfl) ⟨973455, by rfl⟩ : syracuseStep 2595881 = 1946911) B1946911
theorem B6233213 : Blo 1536465 6233213 := bstep (se 3 (by rfl) ⟨1168727, by rfl⟩ : syracuseStep 6233213 = 2337455) B2337455
theorem B2596063 : Blo 1536465 2596063 := bstep (se 1 (by rfl) ⟨1947047, by rfl⟩ : syracuseStep 2596063 = 3894095) B3894095
theorem B3890663 : Blo 1536465 3890663 := bstep (se 1 (by rfl) ⟨2917997, by rfl⟩ : syracuseStep 3890663 = 5835995) B5835995
theorem B13319741 : Blo 1536465 13319741 := bstep (se 3 (by rfl) ⟨2497451, by rfl⟩ : syracuseStep 13319741 = 4994903) B4994903
theorem B8306363 : Blo 1536465 8306363 := bstep (se 1 (by rfl) ⟨6229772, by rfl⟩ : syracuseStep 8306363 = 12459545) B12459545
theorem B2809721 : Blo 1536465 2809721 := bstep (se 2 (by rfl) ⟨1053645, by rfl⟩ : syracuseStep 2809721 = 2107291) B2107291
theorem B3694715 : Blo 1536465 3694715 := bstep (se 1 (by rfl) ⟨2771036, by rfl⟩ : syracuseStep 3694715 = 5542073) B5542073
theorem B3457259 : Blo 1536465 3457259 := bstep (se 1 (by rfl) ⟨2592944, by rfl⟩ : syracuseStep 3457259 = 5185889) B5185889
theorem B5538095 : Blo 1536465 5538095 := bstep (se 1 (by rfl) ⟨4153571, by rfl⟩ : syracuseStep 5538095 = 8307143) B8307143
theorem B7110959 : Blo 1536465 7110959 := bstep (se 1 (by rfl) ⟨5333219, by rfl⟩ : syracuseStep 7110959 = 10666439) B10666439
theorem B17514953 : Blo 1536465 17514953 := bstep (se 2 (by rfl) ⟨6568107, by rfl⟩ : syracuseStep 17514953 = 13136215) B13136215
theorem B5186267 : Blo 1536465 5186267 := bstep (se 1 (by rfl) ⟨3889700, by rfl⟩ : syracuseStep 5186267 = 7779401) B7779401
theorem B5186429 : Blo 1536465 5186429 := bstep (se 3 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 5186429 = 1944911) B1944911
theorem B75818045 : Blo 1536465 75818045 := bstep (se 3 (by rfl) ⟨14215883, by rfl⟩ : syracuseStep 75818045 = 28431767) B28431767
theorem B3458159 : Blo 1536465 3458159 := bstep (se 1 (by rfl) ⟨2593619, by rfl⟩ : syracuseStep 3458159 = 5187239) B5187239
theorem B5186699 : Blo 1536465 5186699 := bstep (se 1 (by rfl) ⟨3890024, by rfl⟩ : syracuseStep 5186699 = 7780049) B7780049
theorem B126231695 : Blo 1536465 126231695 := bstep (se 1 (by rfl) ⟨94673771, by rfl⟩ : syracuseStep 126231695 = 189347543) B189347543
theorem B1729759 : Blo 1536465 1729759 := bstep (se 1 (by rfl) ⟨1297319, by rfl⟩ : syracuseStep 1729759 = 2594639) B2594639
theorem B126289205 : Blo 1536465 126289205 := bstep (se 5 (by rfl) ⟨5919806, by rfl⟩ : syracuseStep 126289205 = 11839613) B11839613
theorem B5834051 : Blo 1536465 5834051 := bstep (se 1 (by rfl) ⟨4375538, by rfl⟩ : syracuseStep 5834051 = 8751077) B8751077
theorem B22463851 : Blo 1536465 22463851 := bstep (se 1 (by rfl) ⟨16847888, by rfl⟩ : syracuseStep 22463851 = 33695777) B33695777
theorem B2917883 : Blo 1536465 2917883 := bstep (se 1 (by rfl) ⟨2188412, by rfl⟩ : syracuseStep 2917883 = 4376825) B4376825
theorem B3458555 : Blo 1536465 3458555 := bstep (se 1 (by rfl) ⟨2593916, by rfl⟩ : syracuseStep 3458555 = 5187833) B5187833
theorem B3458591 : Blo 1536465 3458591 := bstep (se 1 (by rfl) ⟨2593943, by rfl⟩ : syracuseStep 3458591 = 5187887) B5187887
theorem B3458735 : Blo 1536465 3458735 := bstep (se 1 (by rfl) ⟨2594051, by rfl⟩ : syracuseStep 3458735 = 5188103) B5188103
theorem B1730587 : Blo 1536465 1730587 := bstep (se 1 (by rfl) ⟨1297940, by rfl⟩ : syracuseStep 1730587 = 2595881) B2595881
theorem B4155475 : Blo 1536465 4155475 := bstep (se 1 (by rfl) ⟨3116606, by rfl⟩ : syracuseStep 4155475 = 6233213) B6233213
theorem B3459167 : Blo 1536465 3459167 := bstep (se 1 (by rfl) ⟨2594375, by rfl⟩ : syracuseStep 3459167 = 5188751) B5188751
theorem B4155625 : Blo 1536465 4155625 := bstep (se 2 (by rfl) ⟨1558359, by rfl⟩ : syracuseStep 4155625 = 3116719) B3116719
theorem B1640831 : Blo 1536465 1640831 := bstep (se 1 (by rfl) ⟨1230623, by rfl⟩ : syracuseStep 1640831 = 2461247) B2461247
theorem B3459455 : Blo 1536465 3459455 := bstep (se 1 (by rfl) ⟨2594591, by rfl⟩ : syracuseStep 3459455 = 5189183) B5189183
theorem B2918825 : Blo 1536465 2918825 := bstep (se 2 (by rfl) ⟨1094559, by rfl⟩ : syracuseStep 2918825 = 2189119) B2189119
theorem B2919007 : Blo 1536465 2919007 := bstep (se 1 (by rfl) ⟨2189255, by rfl⟩ : syracuseStep 2919007 = 4378511) B4378511
theorem B5188319 : Blo 1536465 5188319 := bstep (se 1 (by rfl) ⟨3891239, by rfl⟩ : syracuseStep 5188319 = 7782479) B7782479
theorem B3459923 : Blo 1536465 3459923 := bstep (se 1 (by rfl) ⟨2594942, by rfl⟩ : syracuseStep 3459923 = 5189885) B5189885
theorem B4803419 : Blo 1536465 4803419 := bstep (se 1 (by rfl) ⟨3602564, by rfl⟩ : syracuseStep 4803419 = 7205129) B7205129
theorem B18705271 : Blo 1536465 18705271 := bstep (se 1 (by rfl) ⟨14028953, by rfl⟩ : syracuseStep 18705271 = 28057907) B28057907
theorem B11234209 : Blo 1536465 11234209 := bstep (se 2 (by rfl) ⟨4212828, by rfl⟩ : syracuseStep 11234209 = 8425657) B8425657
theorem B4926415 : Blo 1536465 4926415 := bstep (se 1 (by rfl) ⟨3694811, by rfl⟩ : syracuseStep 4926415 = 7389623) B7389623
theorem B7384031 : Blo 1536465 7384031 := bstep (se 1 (by rfl) ⟨5538023, by rfl⟩ : syracuseStep 7384031 = 11076047) B11076047
theorem B2305193 : Blo 1536465 2305193 := bstep (se 2 (by rfl) ⟨864447, by rfl⟩ : syracuseStep 2305193 = 1728895) B1728895
theorem B3460283 : Blo 1536465 3460283 := bstep (se 1 (by rfl) ⟨2595212, by rfl⟩ : syracuseStep 3460283 = 5190425) B5190425
theorem B6237427 : Blo 1536465 6237427 := bstep (se 1 (by rfl) ⟨4678070, by rfl⟩ : syracuseStep 6237427 = 9356141) B9356141
theorem B3460463 : Blo 1536465 3460463 := bstep (se 1 (by rfl) ⟨2595347, by rfl⟩ : syracuseStep 3460463 = 5190695) B5190695
theorem B11668859 : Blo 1536465 11668859 := bstep (se 1 (by rfl) ⟨8751644, by rfl⟩ : syracuseStep 11668859 = 17503289) B17503289
theorem B31542817 : Blo 1536465 31542817 := bstep (se 2 (by rfl) ⟨11828556, by rfl⟩ : syracuseStep 31542817 = 23657113) B23657113
theorem B2305607 : Blo 1536465 2305607 := bstep (se 1 (by rfl) ⟨1729205, by rfl⟩ : syracuseStep 2305607 = 3458411) B3458411
theorem B6237803 : Blo 1536465 6237803 := bstep (se 1 (by rfl) ⟨4678352, by rfl⟩ : syracuseStep 6237803 = 9356705) B9356705
theorem B17501831 : Blo 1536465 17501831 := bstep (se 1 (by rfl) ⟨13126373, by rfl⟩ : syracuseStep 17501831 = 26252747) B26252747
theorem B6565511 : Blo 1536465 6565511 := bstep (se 1 (by rfl) ⟨4924133, by rfl⟩ : syracuseStep 6565511 = 9848267) B9848267
theorem B4378283 : Blo 1536465 4378283 := bstep (se 1 (by rfl) ⟨3283712, by rfl⟩ : syracuseStep 4378283 = 6567425) B6567425
theorem B33246895 : Blo 1536465 33246895 := bstep (se 1 (by rfl) ⟨24935171, by rfl⟩ : syracuseStep 33246895 = 49870343) B49870343
theorem B2305787 : Blo 1536465 2305787 := bstep (se 1 (by rfl) ⟨1729340, by rfl⟩ : syracuseStep 2305787 = 3458681) B3458681
theorem B7786367 : Blo 1536465 7786367 := bstep (se 1 (by rfl) ⟨5839775, by rfl⟩ : syracuseStep 7786367 = 11679551) B11679551
theorem B6565769 : Blo 1536465 6565769 := bstep (se 2 (by rfl) ⟨2462163, by rfl⟩ : syracuseStep 6565769 = 4924327) B4924327
theorem B8761283 : Blo 1536465 8761283 := bstep (se 1 (by rfl) ⟨6570962, by rfl⟩ : syracuseStep 8761283 = 13141925) B13141925
theorem B2592823 : Blo 1536465 2592823 := bstep (se 1 (by rfl) ⟨1944617, by rfl⟩ : syracuseStep 2592823 = 3889235) B3889235
theorem B3461183 : Blo 1536465 3461183 := bstep (se 1 (by rfl) ⟨2595887, by rfl⟩ : syracuseStep 3461183 = 5191775) B5191775
theorem B2920511 : Blo 1536465 2920511 := bstep (se 1 (by rfl) ⟨2190383, by rfl⟩ : syracuseStep 2920511 = 4380767) B4380767
theorem B7786691 : Blo 1536465 7786691 := bstep (se 1 (by rfl) ⟨5840018, by rfl⟩ : syracuseStep 7786691 = 11680037) B11680037
theorem B3461417 : Blo 1536465 3461417 := bstep (se 2 (by rfl) ⟨1298031, by rfl⟩ : syracuseStep 3461417 = 2596063) B2596063
theorem B2593147 : Blo 1536465 2593147 := bstep (se 1 (by rfl) ⟨1944860, by rfl⟩ : syracuseStep 2593147 = 3889721) B3889721
theorem B2306459 : Blo 1536465 2306459 := bstep (se 1 (by rfl) ⟨1729844, by rfl⟩ : syracuseStep 2306459 = 3459689) B3459689
theorem B2593417 : Blo 1536465 2593417 := bstep (se 2 (by rfl) ⟨972531, by rfl⟩ : syracuseStep 2593417 = 1945063) B1945063
theorem B1536763 : Blo 1536465 1536763 := bstep (se 1 (by rfl) ⟨1152572, by rfl⟩ : syracuseStep 1536763 = 2305145) B2305145
theorem B3158831 : Blo 1536465 3158831 := bstep (se 1 (by rfl) ⟨2369123, by rfl⟩ : syracuseStep 3158831 = 4738247) B4738247
theorem B1536831 : Blo 1536465 1536831 := bstep (se 1 (by rfl) ⟨1152623, by rfl⟩ : syracuseStep 1536831 = 2305247) B2305247
theorem B2306879 : Blo 1536465 2306879 := bstep (se 1 (by rfl) ⟨1730159, by rfl⟩ : syracuseStep 2306879 = 3460319) B3460319
theorem B1536859 : Blo 1536465 1536859 := bstep (se 1 (by rfl) ⟨1152644, by rfl⟩ : syracuseStep 1536859 = 2305289) B2305289
theorem B1536927 : Blo 1536465 1536927 := bstep (se 1 (by rfl) ⟨1152695, by rfl⟩ : syracuseStep 1536927 = 2305391) B2305391
theorem B2307023 : Blo 1536465 2307023 := bstep (se 1 (by rfl) ⟨1730267, by rfl⟩ : syracuseStep 2307023 = 3460535) B3460535
theorem B7787501 : Blo 1536465 7787501 := bstep (se 3 (by rfl) ⟨1460156, by rfl⟩ : syracuseStep 7787501 = 2920313) B2920313
theorem B1537007 : Blo 1536465 1537007 := bstep (se 1 (by rfl) ⟨1152755, by rfl⟩ : syracuseStep 1537007 = 2305511) B2305511
theorem B2593775 : Blo 1536465 2593775 := bstep (se 1 (by rfl) ⟨1945331, by rfl⟩ : syracuseStep 2593775 = 3890663) B3890663
theorem B2307065 : Blo 1536465 2307065 := bstep (se 2 (by rfl) ⟨865149, by rfl⟩ : syracuseStep 2307065 = 1730299) B1730299
theorem B2307113 : Blo 1536465 2307113 := bstep (se 2 (by rfl) ⟨865167, by rfl⟩ : syracuseStep 2307113 = 1730335) B1730335
theorem B1537095 : Blo 1536465 1537095 := bstep (se 1 (by rfl) ⟨1152821, by rfl⟩ : syracuseStep 1537095 = 2305643) B2305643
theorem B2307143 : Blo 1536465 2307143 := bstep (se 1 (by rfl) ⟨1730357, by rfl⟩ : syracuseStep 2307143 = 3460715) B3460715
theorem B1537179 : Blo 1536465 1537179 := bstep (se 1 (by rfl) ⟨1152884, by rfl⟩ : syracuseStep 1537179 = 2305769) B2305769
theorem B1537275 : Blo 1536465 1537275 := bstep (se 1 (by rfl) ⟨1152956, by rfl⟩ : syracuseStep 1537275 = 2305913) B2305913
theorem B1873147 : Blo 1536465 1873147 := bstep (se 1 (by rfl) ⟨1404860, by rfl⟩ : syracuseStep 1873147 = 2809721) B2809721
theorem B2307323 : Blo 1536465 2307323 := bstep (se 1 (by rfl) ⟨1730492, by rfl⟩ : syracuseStep 2307323 = 3460985) B3460985
theorem B1537343 : Blo 1536465 1537343 := bstep (se 1 (by rfl) ⟨1153007, by rfl⟩ : syracuseStep 1537343 = 2306015) B2306015
theorem B1537511 : Blo 1536465 1537511 := bstep (se 1 (by rfl) ⟨1153133, by rfl⟩ : syracuseStep 1537511 = 2306267) B2306267
theorem B1537519 : Blo 1536465 1537519 := bstep (se 1 (by rfl) ⟨1153139, by rfl⟩ : syracuseStep 1537519 = 2306279) B2306279
theorem B1537627 : Blo 1536465 1537627 := bstep (se 1 (by rfl) ⟨1153220, by rfl⟩ : syracuseStep 1537627 = 2306441) B2306441
theorem B1537691 : Blo 1536465 1537691 := bstep (se 1 (by rfl) ⟨1153268, by rfl⟩ : syracuseStep 1537691 = 2306537) B2306537
theorem B13129451 : Blo 1536465 13129451 := bstep (se 1 (by rfl) ⟨9847088, by rfl⟩ : syracuseStep 13129451 = 19694177) B19694177
theorem B1537775 : Blo 1536465 1537775 := bstep (se 1 (by rfl) ⟨1153331, by rfl⟩ : syracuseStep 1537775 = 2306663) B2306663
theorem B9344755 : Blo 1536465 9344755 := bstep (se 1 (by rfl) ⟨7008566, by rfl⟩ : syracuseStep 9344755 = 14017133) B14017133
theorem B5543687 : Blo 1536465 5543687 := bstep (se 1 (by rfl) ⟨4157765, by rfl⟩ : syracuseStep 5543687 = 8315531) B8315531
theorem B28038935 : Blo 1536465 28038935 := bstep (se 1 (by rfl) ⟨21029201, by rfl⟩ : syracuseStep 28038935 = 42058403) B42058403
theorem B7788311 : Blo 1536465 7788311 := bstep (se 1 (by rfl) ⟨5841233, by rfl⟩ : syracuseStep 7788311 = 11682467) B11682467
theorem B1537863 : Blo 1536465 1537863 := bstep (se 1 (by rfl) ⟨1153397, by rfl⟩ : syracuseStep 1537863 = 2306795) B2306795
theorem B1537883 : Blo 1536465 1537883 := bstep (se 1 (by rfl) ⟨1153412, by rfl⟩ : syracuseStep 1537883 = 2306825) B2306825
theorem B99727199 : Blo 1536465 99727199 := bstep (se 1 (by rfl) ⟨74795399, by rfl⟩ : syracuseStep 99727199 = 149590799) B149590799
theorem B1537951 : Blo 1536465 1537951 := bstep (se 1 (by rfl) ⟨1153463, by rfl⟩ : syracuseStep 1537951 = 2306927) B2306927
theorem B4560887 : Blo 1536465 4560887 := bstep (se 1 (by rfl) ⟨3420665, by rfl⟩ : syracuseStep 4560887 = 6841331) B6841331
theorem B5191721 : Blo 1536465 5191721 := bstep (se 2 (by rfl) ⟨1946895, by rfl⟩ : syracuseStep 5191721 = 3893791) B3893791
theorem B1538119 : Blo 1536465 1538119 := bstep (se 1 (by rfl) ⟨1153589, by rfl⟩ : syracuseStep 1538119 = 2307179) B2307179
theorem B1538279 : Blo 1536465 1538279 := bstep (se 1 (by rfl) ⟨1153709, by rfl⟩ : syracuseStep 1538279 = 2307419) B2307419
theorem B5839199 : Blo 1536465 5839199 := bstep (se 1 (by rfl) ⟨4379399, by rfl⟩ : syracuseStep 5839199 = 8758799) B8758799
theorem B1538463 : Blo 1536465 1538463 := bstep (se 1 (by rfl) ⟨1153847, by rfl⟩ : syracuseStep 1538463 = 2307695) B2307695
theorem B3889691 : Blo 1536465 3889691 := bstep (se 1 (by rfl) ⟨2917268, by rfl⟩ : syracuseStep 3889691 = 5834537) B5834537
theorem B9001543 : Blo 1536465 9001543 := bstep (se 1 (by rfl) ⟨6751157, by rfl⟩ : syracuseStep 9001543 = 13502315) B13502315
theorem B22158137 : Blo 1536465 22158137 := bstep (se 2 (by rfl) ⟨8309301, by rfl⟩ : syracuseStep 22158137 = 16618603) B16618603
theorem B6232889 : Blo 1536465 6232889 := bstep (se 2 (by rfl) ⟨2337333, by rfl⟩ : syracuseStep 6232889 = 4674667) B4674667
theorem B35519309 : Blo 1536465 35519309 := bstep (se 3 (by rfl) ⟨6659870, by rfl⟩ : syracuseStep 35519309 = 13319741) B13319741
theorem B109452311 : Blo 1536465 109452311 := bstep (se 1 (by rfl) ⟨82089233, by rfl⟩ : syracuseStep 109452311 = 164178467) B164178467
theorem B5839897 : Blo 1536465 5839897 := bstep (se 2 (by rfl) ⟨2189961, by rfl⟩ : syracuseStep 5839897 = 4379923) B4379923
theorem B53230715 : Blo 1536465 53230715 := bstep (se 1 (by rfl) ⟨39923036, by rfl⟩ : syracuseStep 53230715 = 79846073) B79846073
theorem B5840171 : Blo 1536465 5840171 := bstep (se 1 (by rfl) ⟨4380128, by rfl⟩ : syracuseStep 5840171 = 8760257) B8760257
theorem B9846269 : Blo 1536465 9846269 := bstep (se 3 (by rfl) ⟨1846175, by rfl⟩ : syracuseStep 9846269 = 3692351) B3692351
theorem B3890855 : Blo 1536465 3890855 := bstep (se 1 (by rfl) ⟨2918141, by rfl⟩ : syracuseStep 3890855 = 5836283) B5836283
theorem B5537575 : Blo 1536465 5537575 := bstep (se 1 (by rfl) ⟨4153181, by rfl⟩ : syracuseStep 5537575 = 8306363) B8306363
theorem B17506205 : Blo 1536465 17506205 := bstep (se 3 (by rfl) ⟨3282413, by rfl⟩ : syracuseStep 17506205 = 6564827) B6564827
theorem B3457097 : Blo 1536465 3457097 := bstep (se 2 (by rfl) ⟨1296411, by rfl⟩ : syracuseStep 3457097 = 2592823) B2592823
theorem B3457511 : Blo 1536465 3457511 := bstep (se 1 (by rfl) ⟨2593133, by rfl⟩ : syracuseStep 3457511 = 5186267) B5186267
theorem B75850229 : Blo 1536465 75850229 := bstep (se 5 (by rfl) ⟨3555479, by rfl⟩ : syracuseStep 75850229 = 7110959) B7110959
theorem B3457529 : Blo 1536465 3457529 := bstep (se 2 (by rfl) ⟨1296573, by rfl⟩ : syracuseStep 3457529 = 2593147) B2593147
theorem B2105887 : Blo 1536465 2105887 := bstep (se 1 (by rfl) ⟨1579415, by rfl⟩ : syracuseStep 2105887 = 3158831) B3158831
theorem B3457619 : Blo 1536465 3457619 := bstep (se 1 (by rfl) ⟨2593214, by rfl⟩ : syracuseStep 3457619 = 5186429) B5186429
theorem B1729183 : Blo 1536465 1729183 := bstep (se 1 (by rfl) ⟨1296887, by rfl⟩ : syracuseStep 1729183 = 2593775) B2593775
theorem B3457799 : Blo 1536465 3457799 := bstep (se 1 (by rfl) ⟨2593349, by rfl⟩ : syracuseStep 3457799 = 5186699) B5186699
theorem B12002057 : Blo 1536465 12002057 := bstep (se 2 (by rfl) ⟨4500771, by rfl⟩ : syracuseStep 12002057 = 9001543) B9001543
theorem B3892009 : Blo 1536465 3892009 := bstep (se 2 (by rfl) ⟨1459503, by rfl⟩ : syracuseStep 3892009 = 2919007) B2919007
theorem B3457889 : Blo 1536465 3457889 := bstep (se 2 (by rfl) ⟨1296708, by rfl⟩ : syracuseStep 3457889 = 2593417) B2593417
theorem B4375549 : Blo 1536465 4375549 := bstep (se 3 (by rfl) ⟨820415, by rfl⟩ : syracuseStep 4375549 = 1640831) B1640831
theorem B3695791 : Blo 1536465 3695791 := bstep (se 1 (by rfl) ⟨2771843, by rfl⟩ : syracuseStep 3695791 = 5543687) B5543687
theorem B3040591 : Blo 1536465 3040591 := bstep (se 1 (by rfl) ⟨2280443, by rfl⟩ : syracuseStep 3040591 = 4560887) B4560887
theorem B3892799 : Blo 1536465 3892799 := bstep (se 1 (by rfl) ⟨2919599, by rfl⟩ : syracuseStep 3892799 = 5839199) B5839199
theorem B8316569 : Blo 1536465 8316569 := bstep (se 2 (by rfl) ⟨3118713, by rfl⟩ : syracuseStep 8316569 = 6237427) B6237427
theorem B29951801 : Blo 1536465 29951801 := bstep (se 2 (by rfl) ⟨11231925, by rfl⟩ : syracuseStep 29951801 = 22463851) B22463851
theorem B3458879 : Blo 1536465 3458879 := bstep (se 1 (by rfl) ⟨2594159, by rfl⟩ : syracuseStep 3458879 = 5188319) B5188319
theorem B4155259 : Blo 1536465 4155259 := bstep (se 1 (by rfl) ⟨3116444, by rfl⟩ : syracuseStep 4155259 = 6232889) B6232889
theorem B72968207 : Blo 1536465 72968207 := bstep (se 1 (by rfl) ⟨54726155, by rfl⟩ : syracuseStep 72968207 = 109452311) B109452311
theorem B3893447 : Blo 1536465 3893447 := bstep (se 1 (by rfl) ⟨2920085, by rfl⟩ : syracuseStep 3893447 = 5840171) B5840171
theorem B44329193 : Blo 1536465 44329193 := bstep (se 2 (by rfl) ⟨16623447, by rfl⟩ : syracuseStep 44329193 = 33246895) B33246895
theorem B6564179 : Blo 1536465 6564179 := bstep (se 1 (by rfl) ⟨4923134, by rfl⟩ : syracuseStep 6564179 = 9846269) B9846269
theorem B7383433 : Blo 1536465 7383433 := bstep (se 2 (by rfl) ⟨2768787, by rfl⟩ : syracuseStep 7383433 = 5537575) B5537575
theorem B11667887 : Blo 1536465 11667887 := bstep (se 1 (by rfl) ⟨8750915, by rfl⟩ : syracuseStep 11667887 = 17501831) B17501831
theorem B4377007 : Blo 1536465 4377007 := bstep (se 1 (by rfl) ⟨3282755, by rfl⟩ : syracuseStep 4377007 = 6565511) B6565511
theorem B2918855 : Blo 1536465 2918855 := bstep (se 1 (by rfl) ⟨2189141, by rfl⟩ : syracuseStep 2918855 = 4378283) B4378283
theorem B4377179 : Blo 1536465 4377179 := bstep (se 1 (by rfl) ⟨3282884, by rfl⟩ : syracuseStep 4377179 = 6565769) B6565769
theorem B5540633 : Blo 1536465 5540633 := bstep (se 2 (by rfl) ⟨2077737, by rfl⟩ : syracuseStep 5540633 = 4155475) B4155475
theorem B2304839 : Blo 1536465 2304839 := bstep (se 1 (by rfl) ⟨1728629, by rfl⟩ : syracuseStep 2304839 = 3457259) B3457259
theorem B202181453 : Blo 1536465 202181453 := bstep (se 3 (by rfl) ⟨37909022, by rfl⟩ : syracuseStep 202181453 = 75818045) B75818045
theorem B11676635 : Blo 1536465 11676635 := bstep (se 1 (by rfl) ⟨8757476, by rfl⟩ : syracuseStep 11676635 = 17514953) B17514953
theorem B5540833 : Blo 1536465 5540833 := bstep (se 2 (by rfl) ⟨2077812, by rfl⟩ : syracuseStep 5540833 = 4155625) B4155625
theorem B2305439 : Blo 1536465 2305439 := bstep (se 1 (by rfl) ⟨1729079, by rfl⟩ : syracuseStep 2305439 = 3458159) B3458159
theorem B84192803 : Blo 1536465 84192803 := bstep (se 1 (by rfl) ⟨63144602, by rfl⟩ : syracuseStep 84192803 = 126289205) B126289205
theorem B2305703 : Blo 1536465 2305703 := bstep (se 1 (by rfl) ⟨1729277, by rfl⟩ : syracuseStep 2305703 = 3458555) B3458555
theorem B2305727 : Blo 1536465 2305727 := bstep (se 1 (by rfl) ⟨1729295, by rfl⟩ : syracuseStep 2305727 = 3458591) B3458591
theorem B2305823 : Blo 1536465 2305823 := bstep (se 1 (by rfl) ⟨1729367, by rfl⟩ : syracuseStep 2305823 = 3458735) B3458735
theorem B8752967 : Blo 1536465 8752967 := bstep (se 1 (by rfl) ⟨6564725, by rfl⟩ : syracuseStep 8752967 = 13129451) B13129451
theorem B24940361 : Blo 1536465 24940361 := bstep (se 2 (by rfl) ⟨9352635, by rfl⟩ : syracuseStep 24940361 = 18705271) B18705271
theorem B14978945 : Blo 1536465 14978945 := bstep (se 2 (by rfl) ⟨5617104, by rfl⟩ : syracuseStep 14978945 = 11234209) B11234209
theorem B3461147 : Blo 1536465 3461147 := bstep (se 1 (by rfl) ⟨2595860, by rfl⟩ : syracuseStep 3461147 = 5191721) B5191721
theorem B7786529 : Blo 1536465 7786529 := bstep (se 2 (by rfl) ⟨2919948, by rfl⟩ : syracuseStep 7786529 = 5839897) B5839897
theorem B2306111 : Blo 1536465 2306111 := bstep (se 1 (by rfl) ⟨1729583, by rfl⟩ : syracuseStep 2306111 = 3459167) B3459167
theorem B2306303 : Blo 1536465 2306303 := bstep (se 1 (by rfl) ⟨1729727, by rfl⟩ : syracuseStep 2306303 = 3459455) B3459455
theorem B1945883 : Blo 1536465 1945883 := bstep (se 1 (by rfl) ⟨1459412, by rfl⟩ : syracuseStep 1945883 = 2918825) B2918825
theorem B2306345 : Blo 1536465 2306345 := bstep (se 2 (by rfl) ⟨864879, by rfl⟩ : syracuseStep 2306345 = 1729759) B1729759
theorem B2593127 : Blo 1536465 2593127 := bstep (se 1 (by rfl) ⟨1944845, by rfl⟩ : syracuseStep 2593127 = 3889691) B3889691
theorem B23679539 : Blo 1536465 23679539 := bstep (se 1 (by rfl) ⟨17759654, by rfl⟩ : syracuseStep 23679539 = 35519309) B35519309
theorem B2306615 : Blo 1536465 2306615 := bstep (se 1 (by rfl) ⟨1729961, by rfl⟩ : syracuseStep 2306615 = 3459923) B3459923
theorem B1536795 : Blo 1536465 1536795 := bstep (se 1 (by rfl) ⟨1152596, by rfl⟩ : syracuseStep 1536795 = 2305193) B2305193
theorem B2306855 : Blo 1536465 2306855 := bstep (se 1 (by rfl) ⟨1730141, by rfl⟩ : syracuseStep 2306855 = 3460283) B3460283
theorem B12809117 : Blo 1536465 12809117 := bstep (se 3 (by rfl) ⟨2401709, by rfl⟩ : syracuseStep 12809117 = 4803419) B4803419
theorem B2306975 : Blo 1536465 2306975 := bstep (se 1 (by rfl) ⟨1730231, by rfl⟩ : syracuseStep 2306975 = 3460463) B3460463
theorem B7779239 : Blo 1536465 7779239 := bstep (se 1 (by rfl) ⟨5834429, by rfl⟩ : syracuseStep 7779239 = 11668859) B11668859
theorem B1537071 : Blo 1536465 1537071 := bstep (se 1 (by rfl) ⟨1152803, by rfl⟩ : syracuseStep 1537071 = 2305607) B2305607
theorem B4158535 : Blo 1536465 4158535 := bstep (se 1 (by rfl) ⟨3118901, by rfl⟩ : syracuseStep 4158535 = 6237803) B6237803
theorem B2593903 : Blo 1536465 2593903 := bstep (se 1 (by rfl) ⟨1945427, by rfl⟩ : syracuseStep 2593903 = 3890855) B3890855
theorem B1537191 : Blo 1536465 1537191 := bstep (se 1 (by rfl) ⟨1152893, by rfl⟩ : syracuseStep 1537191 = 2305787) B2305787
theorem B5190911 : Blo 1536465 5190911 := bstep (se 1 (by rfl) ⟨3893183, by rfl⟩ : syracuseStep 5190911 = 7786367) B7786367
theorem B11670803 : Blo 1536465 11670803 := bstep (se 1 (by rfl) ⟨8753102, by rfl⟩ : syracuseStep 11670803 = 17506205) B17506205
theorem B2307449 : Blo 1536465 2307449 := bstep (se 2 (by rfl) ⟨865293, by rfl⟩ : syracuseStep 2307449 = 1730587) B1730587
theorem B2307455 : Blo 1536465 2307455 := bstep (se 1 (by rfl) ⟨1730591, by rfl⟩ : syracuseStep 2307455 = 3461183) B3461183
theorem B1947007 : Blo 1536465 1947007 := bstep (se 1 (by rfl) ⟨1460255, by rfl⟩ : syracuseStep 1947007 = 2920511) B2920511
theorem B2463143 : Blo 1536465 2463143 := bstep (se 1 (by rfl) ⟨1847357, by rfl⟩ : syracuseStep 2463143 = 3694715) B3694715
theorem B5191127 : Blo 1536465 5191127 := bstep (se 1 (by rfl) ⟨3893345, by rfl⟩ : syracuseStep 5191127 = 7786691) B7786691
theorem B2307611 : Blo 1536465 2307611 := bstep (se 1 (by rfl) ⟨1730708, by rfl⟩ : syracuseStep 2307611 = 3461417) B3461417
theorem B3692063 : Blo 1536465 3692063 := bstep (se 1 (by rfl) ⟨2769047, by rfl⟩ : syracuseStep 3692063 = 5538095) B5538095
theorem B1537639 : Blo 1536465 1537639 := bstep (se 1 (by rfl) ⟨1153229, by rfl⟩ : syracuseStep 1537639 = 2306459) B2306459
theorem B1537919 : Blo 1536465 1537919 := bstep (se 1 (by rfl) ⟨1153439, by rfl⟩ : syracuseStep 1537919 = 2306879) B2306879
theorem B1538015 : Blo 1536465 1538015 := bstep (se 1 (by rfl) ⟨1153511, by rfl⟩ : syracuseStep 1538015 = 2307023) B2307023
theorem B5191667 : Blo 1536465 5191667 := bstep (se 1 (by rfl) ⟨3893750, by rfl⟩ : syracuseStep 5191667 = 7787501) B7787501
theorem B1538043 : Blo 1536465 1538043 := bstep (se 1 (by rfl) ⟨1153532, by rfl⟩ : syracuseStep 1538043 = 2307065) B2307065
theorem B1538075 : Blo 1536465 1538075 := bstep (se 1 (by rfl) ⟨1153556, by rfl⟩ : syracuseStep 1538075 = 2307113) B2307113
theorem B1538095 : Blo 1536465 1538095 := bstep (se 1 (by rfl) ⟨1153571, by rfl⟩ : syracuseStep 1538095 = 2307143) B2307143
theorem B84154463 : Blo 1536465 84154463 := bstep (se 1 (by rfl) ⟨63115847, by rfl⟩ : syracuseStep 84154463 = 126231695) B126231695
theorem B1538215 : Blo 1536465 1538215 := bstep (se 1 (by rfl) ⟨1153661, by rfl⟩ : syracuseStep 1538215 = 2307323) B2307323
theorem B3889367 : Blo 1536465 3889367 := bstep (se 1 (by rfl) ⟨2917025, by rfl⟩ : syracuseStep 3889367 = 5834051) B5834051
theorem B18692623 : Blo 1536465 18692623 := bstep (se 1 (by rfl) ⟨14019467, by rfl⟩ : syracuseStep 18692623 = 28038935) B28038935
theorem B5192207 : Blo 1536465 5192207 := bstep (se 1 (by rfl) ⟨3894155, by rfl⟩ : syracuseStep 5192207 = 7788311) B7788311
theorem B66484799 : Blo 1536465 66484799 := bstep (se 1 (by rfl) ⟨49863599, by rfl⟩ : syracuseStep 66484799 = 99727199) B99727199
theorem B6568553 : Blo 1536465 6568553 := bstep (se 2 (by rfl) ⟨2463207, by rfl⟩ : syracuseStep 6568553 = 4926415) B4926415
theorem B7781021 : Blo 1536465 7781021 := bstep (se 3 (by rfl) ⟨1458941, by rfl⟩ : syracuseStep 7781021 = 2917883) B2917883
theorem B2497529 : Blo 1536465 2497529 := bstep (se 2 (by rfl) ⟨936573, by rfl⟩ : syracuseStep 2497529 = 1873147) B1873147
theorem B4922687 : Blo 1536465 4922687 := bstep (se 1 (by rfl) ⟨3692015, by rfl⟩ : syracuseStep 4922687 = 7384031) B7384031
theorem B42057089 : Blo 1536465 42057089 := bstep (se 2 (by rfl) ⟨15771408, by rfl⟩ : syracuseStep 42057089 = 31542817) B31542817
theorem B35487143 : Blo 1536465 35487143 := bstep (se 1 (by rfl) ⟨26615357, by rfl⟩ : syracuseStep 35487143 = 53230715) B53230715
theorem B59088365 : Blo 1536465 59088365 := bstep (se 3 (by rfl) ⟨11079068, by rfl⟩ : syracuseStep 59088365 = 22158137) B22158137
theorem B12459673 : Blo 1536465 12459673 := bstep (se 2 (by rfl) ⟨4672377, by rfl⟩ : syracuseStep 12459673 = 9344755) B9344755
theorem B5840855 : Blo 1536465 5840855 := bstep (se 1 (by rfl) ⟨4380641, by rfl⟩ : syracuseStep 5840855 = 8761283) B8761283
theorem B1728751 : Blo 1536465 1728751 := bstep (se 1 (by rfl) ⟨1296563, by rfl⟩ : syracuseStep 1728751 = 2593127) B2593127
theorem B15786359 : Blo 1536465 15786359 := bstep (se 1 (by rfl) ⟨11839769, by rfl⟩ : syracuseStep 15786359 = 23679539) B23679539
theorem B5186159 : Blo 1536465 5186159 := bstep (se 1 (by rfl) ⟨3889619, by rfl⟩ : syracuseStep 5186159 = 7779239) B7779239
theorem B7783613 : Blo 1536465 7783613 := bstep (se 3 (by rfl) ⟨1459427, by rfl⟩ : syracuseStep 7783613 = 2918855) B2918855
theorem B5834065 : Blo 1536465 5834065 := bstep (se 2 (by rfl) ⟨2187774, by rfl⟩ : syracuseStep 5834065 = 4375549) B4375549
theorem B3458537 : Blo 1536465 3458537 := bstep (se 2 (by rfl) ⟨1296951, by rfl⟩ : syracuseStep 3458537 = 2593903) B2593903
theorem B4376119 : Blo 1536465 4376119 := bstep (se 1 (by rfl) ⟨3282089, by rfl⟩ : syracuseStep 4376119 = 6564179) B6564179
theorem B2918119 : Blo 1536465 2918119 := bstep (se 1 (by rfl) ⟨2188589, by rfl⟩ : syracuseStep 2918119 = 4377179) B4377179
theorem B5187347 : Blo 1536465 5187347 := bstep (se 1 (by rfl) ⟨3890510, by rfl⟩ : syracuseStep 5187347 = 7781021) B7781021
theorem B7784423 : Blo 1536465 7784423 := bstep (se 1 (by rfl) ⟨5838317, by rfl⟩ : syracuseStep 7784423 = 11676635) B11676635
theorem B1665019 : Blo 1536465 1665019 := bstep (se 1 (by rfl) ⟨1248764, by rfl⟩ : syracuseStep 1665019 = 2497529) B2497529
theorem B5540345 : Blo 1536465 5540345 := bstep (se 2 (by rfl) ⟨2077629, by rfl⟩ : syracuseStep 5540345 = 4155259) B4155259
theorem B5835311 : Blo 1536465 5835311 := bstep (se 1 (by rfl) ⟨4376483, by rfl⟩ : syracuseStep 5835311 = 8752967) B8752967
theorem B3893903 : Blo 1536465 3893903 := bstep (se 1 (by rfl) ⟨2920427, by rfl⟩ : syracuseStep 3893903 = 5840855) B5840855
theorem B2304731 : Blo 1536465 2304731 := bstep (se 1 (by rfl) ⟨1728548, by rfl⟩ : syracuseStep 2304731 = 3457097) B3457097
theorem B2305007 : Blo 1536465 2305007 := bstep (se 1 (by rfl) ⟨1728755, by rfl⟩ : syracuseStep 2305007 = 3457511) B3457511
theorem B2305019 : Blo 1536465 2305019 := bstep (se 1 (by rfl) ⟨1728764, by rfl⟩ : syracuseStep 2305019 = 3457529) B3457529
theorem B2305079 : Blo 1536465 2305079 := bstep (se 1 (by rfl) ⟨1728809, by rfl⟩ : syracuseStep 2305079 = 3457619) B3457619
theorem B2305199 : Blo 1536465 2305199 := bstep (se 1 (by rfl) ⟨1728899, by rfl⟩ : syracuseStep 2305199 = 3457799) B3457799
theorem B5836009 : Blo 1536465 5836009 := bstep (se 2 (by rfl) ⟨2188503, by rfl⟩ : syracuseStep 5836009 = 4377007) B4377007
theorem B2305259 : Blo 1536465 2305259 := bstep (se 1 (by rfl) ⟨1728944, by rfl⟩ : syracuseStep 2305259 = 3457889) B3457889
theorem B24923497 : Blo 1536465 24923497 := bstep (se 2 (by rfl) ⟨9346311, by rfl⟩ : syracuseStep 24923497 = 18692623) B18692623
theorem B5189021 : Blo 1536465 5189021 := bstep (se 3 (by rfl) ⟨972941, by rfl⟩ : syracuseStep 5189021 = 1945883) B1945883
theorem B3460607 : Blo 1536465 3460607 := bstep (se 1 (by rfl) ⟨2595455, by rfl⟩ : syracuseStep 3460607 = 5190911) B5190911
theorem B2305577 : Blo 1536465 2305577 := bstep (se 2 (by rfl) ⟨864591, by rfl⟩ : syracuseStep 2305577 = 1729183) B1729183
theorem B3460751 : Blo 1536465 3460751 := bstep (se 1 (by rfl) ⟨2595563, by rfl⟩ : syracuseStep 3460751 = 5191127) B5191127
theorem B2461375 : Blo 1536465 2461375 := bstep (se 1 (by rfl) ⟨1846031, by rfl⟩ : syracuseStep 2461375 = 3692063) B3692063
theorem B5189345 : Blo 1536465 5189345 := bstep (se 2 (by rfl) ⟨1946004, by rfl⟩ : syracuseStep 5189345 = 3892009) B3892009
theorem B19967867 : Blo 1536465 19967867 := bstep (se 1 (by rfl) ⟨14975900, by rfl⟩ : syracuseStep 19967867 = 29951801) B29951801
theorem B2305919 : Blo 1536465 2305919 := bstep (se 1 (by rfl) ⟨1729439, by rfl⟩ : syracuseStep 2305919 = 3458879) B3458879
theorem B3461111 : Blo 1536465 3461111 := bstep (se 1 (by rfl) ⟨2595833, by rfl⟩ : syracuseStep 3461111 = 5191667) B5191667
theorem B56102975 : Blo 1536465 56102975 := bstep (se 1 (by rfl) ⟨42077231, by rfl⟩ : syracuseStep 56102975 = 84154463) B84154463
theorem B2592911 : Blo 1536465 2592911 := bstep (se 1 (by rfl) ⟨1944683, by rfl⟩ : syracuseStep 2592911 = 3889367) B3889367
theorem B29552795 : Blo 1536465 29552795 := bstep (se 1 (by rfl) ⟨22164596, by rfl⟩ : syracuseStep 29552795 = 44329193) B44329193
theorem B4927721 : Blo 1536465 4927721 := bstep (se 2 (by rfl) ⟨1847895, by rfl⟩ : syracuseStep 4927721 = 3695791) B3695791
theorem B7778591 : Blo 1536465 7778591 := bstep (se 1 (by rfl) ⟨5833943, by rfl⟩ : syracuseStep 7778591 = 11667887) B11667887
theorem B3461471 : Blo 1536465 3461471 := bstep (se 1 (by rfl) ⟨2596103, by rfl⟩ : syracuseStep 3461471 = 5192207) B5192207
theorem B44323199 : Blo 1536465 44323199 := bstep (se 1 (by rfl) ⟨33242399, by rfl⟩ : syracuseStep 44323199 = 66484799) B66484799
theorem B4379035 : Blo 1536465 4379035 := bstep (se 1 (by rfl) ⟨3284276, by rfl⟩ : syracuseStep 4379035 = 6568553) B6568553
theorem B1536559 : Blo 1536465 1536559 := bstep (se 1 (by rfl) ⟨1152419, by rfl⟩ : syracuseStep 1536559 = 2304839) B2304839
theorem B134787635 : Blo 1536465 134787635 := bstep (se 1 (by rfl) ⟨101090726, by rfl⟩ : syracuseStep 134787635 = 202181453) B202181453
theorem B3281791 : Blo 1536465 3281791 := bstep (se 1 (by rfl) ⟨2461343, by rfl⟩ : syracuseStep 3281791 = 4922687) B4922687
theorem B28038059 : Blo 1536465 28038059 := bstep (se 1 (by rfl) ⟨21028544, by rfl⟩ : syracuseStep 28038059 = 42057089) B42057089
theorem B1536959 : Blo 1536465 1536959 := bstep (se 1 (by rfl) ⟨1152719, by rfl⟩ : syracuseStep 1536959 = 2305439) B2305439
theorem B39392243 : Blo 1536465 39392243 := bstep (se 1 (by rfl) ⟨29544182, by rfl⟩ : syracuseStep 39392243 = 59088365) B59088365
theorem B56128535 : Blo 1536465 56128535 := bstep (se 1 (by rfl) ⟨42096401, by rfl⟩ : syracuseStep 56128535 = 84192803) B84192803
theorem B34157645 : Blo 1536465 34157645 := bstep (se 3 (by rfl) ⟨6404558, by rfl⟩ : syracuseStep 34157645 = 12809117) B12809117
theorem B1537135 : Blo 1536465 1537135 := bstep (se 1 (by rfl) ⟨1152851, by rfl⟩ : syracuseStep 1537135 = 2305703) B2305703
theorem B1537151 : Blo 1536465 1537151 := bstep (se 1 (by rfl) ⟨1152863, by rfl⟩ : syracuseStep 1537151 = 2305727) B2305727
theorem B1537215 : Blo 1536465 1537215 := bstep (se 1 (by rfl) ⟨1152911, by rfl⟩ : syracuseStep 1537215 = 2305823) B2305823
theorem B16626907 : Blo 1536465 16626907 := bstep (se 1 (by rfl) ⟨12470180, by rfl⟩ : syracuseStep 16626907 = 24940361) B24940361
theorem B2307431 : Blo 1536465 2307431 := bstep (se 1 (by rfl) ⟨1730573, by rfl⟩ : syracuseStep 2307431 = 3461147) B3461147
theorem B5191019 : Blo 1536465 5191019 := bstep (se 1 (by rfl) ⟨3893264, by rfl⟩ : syracuseStep 5191019 = 7786529) B7786529
theorem B194581885 : Blo 1536465 194581885 := bstep (se 3 (by rfl) ⟨36484103, by rfl⟩ : syracuseStep 194581885 = 72968207) B72968207
theorem B1537407 : Blo 1536465 1537407 := bstep (se 1 (by rfl) ⟨1153055, by rfl⟩ : syracuseStep 1537407 = 2306111) B2306111
theorem B1537535 : Blo 1536465 1537535 := bstep (se 1 (by rfl) ⟨1153151, by rfl⟩ : syracuseStep 1537535 = 2306303) B2306303
theorem B1537563 : Blo 1536465 1537563 := bstep (se 1 (by rfl) ⟨1153172, by rfl⟩ : syracuseStep 1537563 = 2306345) B2306345
theorem B1537743 : Blo 1536465 1537743 := bstep (se 1 (by rfl) ⟨1153307, by rfl⟩ : syracuseStep 1537743 = 2306615) B2306615
theorem B8001371 : Blo 1536465 8001371 := bstep (se 1 (by rfl) ⟨6001028, by rfl⟩ : syracuseStep 8001371 = 12002057) B12002057
theorem B9844577 : Blo 1536465 9844577 := bstep (se 2 (by rfl) ⟨3691716, by rfl⟩ : syracuseStep 9844577 = 7383433) B7383433
theorem B1537903 : Blo 1536465 1537903 := bstep (se 1 (by rfl) ⟨1153427, by rfl⟩ : syracuseStep 1537903 = 2306855) B2306855
theorem B1537983 : Blo 1536465 1537983 := bstep (se 1 (by rfl) ⟨1153487, by rfl⟩ : syracuseStep 1537983 = 2306975) B2306975
theorem B2807849 : Blo 1536465 2807849 := bstep (se 2 (by rfl) ⟨1052943, by rfl⟩ : syracuseStep 2807849 = 2105887) B2105887
theorem B7780535 : Blo 1536465 7780535 := bstep (se 1 (by rfl) ⟨5835401, by rfl⟩ : syracuseStep 7780535 = 11670803) B11670803
theorem B1538299 : Blo 1536465 1538299 := bstep (se 1 (by rfl) ⟨1153724, by rfl⟩ : syracuseStep 1538299 = 2307449) B2307449
theorem B1538303 : Blo 1536465 1538303 := bstep (se 1 (by rfl) ⟨1153727, by rfl⟩ : syracuseStep 1538303 = 2307455) B2307455
theorem B1538407 : Blo 1536465 1538407 := bstep (se 1 (by rfl) ⟨1153805, by rfl⟩ : syracuseStep 1538407 = 2307611) B2307611
theorem B2595199 : Blo 1536465 2595199 := bstep (se 1 (by rfl) ⟨1946399, by rfl⟩ : syracuseStep 2595199 = 3892799) B3892799
theorem B5544379 : Blo 1536465 5544379 := bstep (se 1 (by rfl) ⟨4158284, by rfl⟩ : syracuseStep 5544379 = 8316569) B8316569
theorem B6568381 : Blo 1536465 6568381 := bstep (se 3 (by rfl) ⟨1231571, by rfl⟩ : syracuseStep 6568381 = 2463143) B2463143
theorem B7387777 : Blo 1536465 7387777 := bstep (se 2 (by rfl) ⟨2770416, by rfl⟩ : syracuseStep 7387777 = 5540833) B5540833
theorem B202267277 : Blo 1536465 202267277 := bstep (se 3 (by rfl) ⟨37925114, by rfl⟩ : syracuseStep 202267277 = 75850229) B75850229
theorem B5544713 : Blo 1536465 5544713 := bstep (se 2 (by rfl) ⟨2079267, by rfl⟩ : syracuseStep 5544713 = 4158535) B4158535
theorem B2595631 : Blo 1536465 2595631 := bstep (se 1 (by rfl) ⟨1946723, by rfl⟩ : syracuseStep 2595631 = 3893447) B3893447
theorem B4054121 : Blo 1536465 4054121 := bstep (se 2 (by rfl) ⟨1520295, by rfl⟩ : syracuseStep 4054121 = 3040591) B3040591
theorem B2596009 : Blo 1536465 2596009 := bstep (se 2 (by rfl) ⟨973503, by rfl⟩ : syracuseStep 2596009 = 1947007) B1947007
theorem B3693755 : Blo 1536465 3693755 := bstep (se 1 (by rfl) ⟨2770316, by rfl⟩ : syracuseStep 3693755 = 5540633) B5540633
theorem B16612897 : Blo 1536465 16612897 := bstep (se 2 (by rfl) ⟨6229836, by rfl⟩ : syracuseStep 16612897 = 12459673) B12459673
theorem B23658095 : Blo 1536465 23658095 := bstep (se 1 (by rfl) ⟨17743571, by rfl⟩ : syracuseStep 23658095 = 35487143) B35487143
theorem B9985963 : Blo 1536465 9985963 := bstep (se 1 (by rfl) ⟨7489472, by rfl⟩ : syracuseStep 9985963 = 14978945) B14978945
theorem B1728607 : Blo 1536465 1728607 := bstep (se 1 (by rfl) ⟨1296455, by rfl⟩ : syracuseStep 1728607 = 2592911) B2592911
theorem B19701863 : Blo 1536465 19701863 := bstep (se 1 (by rfl) ⟨14776397, by rfl⟩ : syracuseStep 19701863 = 29552795) B29552795
theorem B7487597 : Blo 1536465 7487597 := bstep (se 3 (by rfl) ⟨1403924, by rfl⟩ : syracuseStep 7487597 = 2807849) B2807849
theorem B5185727 : Blo 1536465 5185727 := bstep (se 1 (by rfl) ⟨3889295, by rfl⟩ : syracuseStep 5185727 = 7778591) B7778591
theorem B29548799 : Blo 1536465 29548799 := bstep (se 1 (by rfl) ⟨22161599, by rfl⟩ : syracuseStep 29548799 = 44323199) B44323199
theorem B89858423 : Blo 1536465 89858423 := bstep (se 1 (by rfl) ⟨67393817, by rfl⟩ : syracuseStep 89858423 = 134787635) B134787635
theorem B3457439 : Blo 1536465 3457439 := bstep (se 1 (by rfl) ⟨2593079, by rfl⟩ : syracuseStep 3457439 = 5186159) B5186159
theorem B8757841 : Blo 1536465 8757841 := bstep (se 2 (by rfl) ⟨3284190, by rfl⟩ : syracuseStep 8757841 = 6568381) B6568381
theorem B13140589 : Blo 1536465 13140589 := bstep (se 3 (by rfl) ⟨2463860, by rfl⟩ : syracuseStep 13140589 = 4927721) B4927721
theorem B4375721 : Blo 1536465 4375721 := bstep (se 2 (by rfl) ⟨1640895, by rfl⟩ : syracuseStep 4375721 = 3281791) B3281791
theorem B3458231 : Blo 1536465 3458231 := bstep (se 1 (by rfl) ⟨2593673, by rfl⟩ : syracuseStep 3458231 = 5187347) B5187347
theorem B5334247 : Blo 1536465 5334247 := bstep (se 1 (by rfl) ⟨4000685, by rfl⟩ : syracuseStep 5334247 = 8001371) B8001371
theorem B6563051 : Blo 1536465 6563051 := bstep (se 1 (by rfl) ⟨4922288, by rfl⟩ : syracuseStep 6563051 = 9844577) B9844577
theorem B5187023 : Blo 1536465 5187023 := bstep (se 1 (by rfl) ⟨3890267, by rfl⟩ : syracuseStep 5187023 = 7780535) B7780535
theorem B22169209 : Blo 1536465 22169209 := bstep (se 2 (by rfl) ⟨8313453, by rfl⟩ : syracuseStep 22169209 = 16626907) B16626907
theorem B63088253 : Blo 1536465 63088253 := bstep (se 3 (by rfl) ⟨11829047, by rfl⟩ : syracuseStep 63088253 = 23658095) B23658095
theorem B259442513 : Blo 1536465 259442513 := bstep (se 2 (by rfl) ⟨97290942, by rfl⟩ : syracuseStep 259442513 = 194581885) B194581885
theorem B3696475 : Blo 1536465 3696475 := bstep (se 1 (by rfl) ⟨2772356, by rfl⟩ : syracuseStep 3696475 = 5544713) B5544713
theorem B5834825 : Blo 1536465 5834825 := bstep (se 2 (by rfl) ⟨2188059, by rfl⟩ : syracuseStep 5834825 = 4376119) B4376119
theorem B3459347 : Blo 1536465 3459347 := bstep (se 1 (by rfl) ⟨2594510, by rfl⟩ : syracuseStep 3459347 = 5189021) B5189021
theorem B3459563 : Blo 1536465 3459563 := bstep (se 1 (by rfl) ⟨2594672, by rfl⟩ : syracuseStep 3459563 = 5189345) B5189345
theorem B13314617 : Blo 1536465 13314617 := bstep (se 2 (by rfl) ⟨4992981, by rfl⟩ : syracuseStep 13314617 = 9985963) B9985963
theorem B2305001 : Blo 1536465 2305001 := bstep (se 2 (by rfl) ⟨864375, by rfl⟩ : syracuseStep 2305001 = 1728751) B1728751
theorem B3460265 : Blo 1536465 3460265 := bstep (se 2 (by rfl) ⟨1297599, by rfl⟩ : syracuseStep 3460265 = 2595199) B2595199
theorem B7392505 : Blo 1536465 7392505 := bstep (se 2 (by rfl) ⟨2772189, by rfl⟩ : syracuseStep 7392505 = 5544379) B5544379
theorem B5189075 : Blo 1536465 5189075 := bstep (se 1 (by rfl) ⟨3891806, by rfl⟩ : syracuseStep 5189075 = 7783613) B7783613
theorem B9850369 : Blo 1536465 9850369 := bstep (se 2 (by rfl) ⟨3693888, by rfl⟩ : syracuseStep 9850369 = 7387777) B7387777
theorem B3460679 : Blo 1536465 3460679 := bstep (se 1 (by rfl) ⟨2595509, by rfl⟩ : syracuseStep 3460679 = 5191019) B5191019
theorem B2305691 : Blo 1536465 2305691 := bstep (se 1 (by rfl) ⟨1729268, by rfl⟩ : syracuseStep 2305691 = 3458537) B3458537
theorem B3460841 : Blo 1536465 3460841 := bstep (se 2 (by rfl) ⟨1297815, by rfl⟩ : syracuseStep 3460841 = 2595631) B2595631
theorem B5189615 : Blo 1536465 5189615 := bstep (se 1 (by rfl) ⟨3892211, by rfl⟩ : syracuseStep 5189615 = 7784423) B7784423
theorem B3461345 : Blo 1536465 3461345 := bstep (se 2 (by rfl) ⟨1298004, by rfl⟩ : syracuseStep 3461345 = 2596009) B2596009
theorem B134844851 : Blo 1536465 134844851 := bstep (se 1 (by rfl) ⟨101133638, by rfl⟩ : syracuseStep 134844851 = 202267277) B202267277
theorem B7778753 : Blo 1536465 7778753 := bstep (se 2 (by rfl) ⟨2917032, by rfl⟩ : syracuseStep 7778753 = 5834065) B5834065
theorem B33231329 : Blo 1536465 33231329 := bstep (se 2 (by rfl) ⟨12461748, by rfl⟩ : syracuseStep 33231329 = 24923497) B24923497
theorem B1536487 : Blo 1536465 1536487 := bstep (se 1 (by rfl) ⟨1152365, by rfl⟩ : syracuseStep 1536487 = 2304731) B2304731
theorem B1536671 : Blo 1536465 1536671 := bstep (se 1 (by rfl) ⟨1152503, by rfl⟩ : syracuseStep 1536671 = 2305007) B2305007
theorem B1536679 : Blo 1536465 1536679 := bstep (se 1 (by rfl) ⟨1152509, by rfl⟩ : syracuseStep 1536679 = 2305019) B2305019
theorem B1536719 : Blo 1536465 1536719 := bstep (se 1 (by rfl) ⟨1152539, by rfl⟩ : syracuseStep 1536719 = 2305079) B2305079
theorem B1536799 : Blo 1536465 1536799 := bstep (se 1 (by rfl) ⟨1152599, by rfl⟩ : syracuseStep 1536799 = 2305199) B2305199
theorem B2462503 : Blo 1536465 2462503 := bstep (se 1 (by rfl) ⟨1846877, by rfl⟩ : syracuseStep 2462503 = 3693755) B3693755
theorem B1536839 : Blo 1536465 1536839 := bstep (se 1 (by rfl) ⟨1152629, by rfl⟩ : syracuseStep 1536839 = 2305259) B2305259
theorem B3281833 : Blo 1536465 3281833 := bstep (se 2 (by rfl) ⟨1230687, by rfl⟩ : syracuseStep 3281833 = 2461375) B2461375
theorem B2307071 : Blo 1536465 2307071 := bstep (se 1 (by rfl) ⟨1730303, by rfl⟩ : syracuseStep 2307071 = 3460607) B3460607
theorem B1537051 : Blo 1536465 1537051 := bstep (se 1 (by rfl) ⟨1152788, by rfl⟩ : syracuseStep 1537051 = 2305577) B2305577
theorem B2307167 : Blo 1536465 2307167 := bstep (se 1 (by rfl) ⟨1730375, by rfl⟩ : syracuseStep 2307167 = 3460751) B3460751
theorem B1537279 : Blo 1536465 1537279 := bstep (se 1 (by rfl) ⟨1152959, by rfl⟩ : syracuseStep 1537279 = 2305919) B2305919
theorem B2307407 : Blo 1536465 2307407 := bstep (se 1 (by rfl) ⟨1730555, by rfl⟩ : syracuseStep 2307407 = 3461111) B3461111
theorem B37401983 : Blo 1536465 37401983 := bstep (se 1 (by rfl) ⟨28051487, by rfl⟩ : syracuseStep 37401983 = 56102975) B56102975
theorem B2307647 : Blo 1536465 2307647 := bstep (se 1 (by rfl) ⟨1730735, by rfl⟩ : syracuseStep 2307647 = 3461471) B3461471
theorem B10524239 : Blo 1536465 10524239 := bstep (se 1 (by rfl) ⟨7893179, by rfl⟩ : syracuseStep 10524239 = 15786359) B15786359
theorem B5838713 : Blo 1536465 5838713 := bstep (se 2 (by rfl) ⟨2189517, by rfl⟩ : syracuseStep 5838713 = 4379035) B4379035
theorem B18692039 : Blo 1536465 18692039 := bstep (se 1 (by rfl) ⟨14019029, by rfl⟩ : syracuseStep 18692039 = 28038059) B28038059
theorem B26261495 : Blo 1536465 26261495 := bstep (se 1 (by rfl) ⟨19696121, by rfl⟩ : syracuseStep 26261495 = 39392243) B39392243
theorem B37419023 : Blo 1536465 37419023 := bstep (se 1 (by rfl) ⟨28064267, by rfl⟩ : syracuseStep 37419023 = 56128535) B56128535
theorem B22771763 : Blo 1536465 22771763 := bstep (se 1 (by rfl) ⟨17078822, by rfl⟩ : syracuseStep 22771763 = 34157645) B34157645
theorem B1538287 : Blo 1536465 1538287 := bstep (se 1 (by rfl) ⟨1153715, by rfl⟩ : syracuseStep 1538287 = 2307431) B2307431
theorem B7781345 : Blo 1536465 7781345 := bstep (se 2 (by rfl) ⟨2918004, by rfl⟩ : syracuseStep 7781345 = 5836009) B5836009
theorem B3693563 : Blo 1536465 3693563 := bstep (se 1 (by rfl) ⟨2770172, by rfl⟩ : syracuseStep 3693563 = 5540345) B5540345
theorem B3890207 : Blo 1536465 3890207 := bstep (se 1 (by rfl) ⟨2917655, by rfl⟩ : syracuseStep 3890207 = 5835311) B5835311
theorem B2595935 : Blo 1536465 2595935 := bstep (se 1 (by rfl) ⟨1946951, by rfl⟩ : syracuseStep 2595935 = 3893903) B3893903
theorem B22150529 : Blo 1536465 22150529 := bstep (se 2 (by rfl) ⟨8306448, by rfl⟩ : syracuseStep 22150529 = 16612897) B16612897
theorem B2702747 : Blo 1536465 2702747 := bstep (se 1 (by rfl) ⟨2027060, by rfl⟩ : syracuseStep 2702747 = 4054121) B4054121
theorem B3890825 : Blo 1536465 3890825 := bstep (se 2 (by rfl) ⟨1459059, by rfl⟩ : syracuseStep 3890825 = 2918119) B2918119
theorem B13311911 : Blo 1536465 13311911 := bstep (se 1 (by rfl) ⟨9983933, by rfl⟩ : syracuseStep 13311911 = 19967867) B19967867
theorem B2220025 : Blo 1536465 2220025 := bstep (se 2 (by rfl) ⟨832509, by rfl⟩ : syracuseStep 2220025 = 1665019) B1665019
theorem B3457151 : Blo 1536465 3457151 := bstep (se 1 (by rfl) ⟨2592863, by rfl⟩ : syracuseStep 3457151 = 5185727) B5185727
theorem B5185835 : Blo 1536465 5185835 := bstep (se 1 (by rfl) ⟨3889376, by rfl⟩ : syracuseStep 5185835 = 7778753) B7778753
theorem B2917147 : Blo 1536465 2917147 := bstep (se 1 (by rfl) ⟨2187860, by rfl⟩ : syracuseStep 2917147 = 4375721) B4375721
theorem B4375367 : Blo 1536465 4375367 := bstep (se 1 (by rfl) ⟨3281525, by rfl⟩ : syracuseStep 4375367 = 6563051) B6563051
theorem B3458015 : Blo 1536465 3458015 := bstep (se 1 (by rfl) ⟨2593511, by rfl⟩ : syracuseStep 3458015 = 5187023) B5187023
theorem B42058835 : Blo 1536465 42058835 := bstep (se 1 (by rfl) ⟨31544126, by rfl⟩ : syracuseStep 42058835 = 63088253) B63088253
theorem B4375777 : Blo 1536465 4375777 := bstep (se 2 (by rfl) ⟨1640916, by rfl⟩ : syracuseStep 4375777 = 3281833) B3281833
theorem B3892475 : Blo 1536465 3892475 := bstep (se 1 (by rfl) ⟨2919356, by rfl⟩ : syracuseStep 3892475 = 5838713) B5838713
theorem B12461359 : Blo 1536465 12461359 := bstep (se 1 (by rfl) ⟨9346019, by rfl⟩ : syracuseStep 12461359 = 18692039) B18692039
theorem B17507663 : Blo 1536465 17507663 := bstep (se 1 (by rfl) ⟨13130747, by rfl⟩ : syracuseStep 17507663 = 26261495) B26261495
theorem B24946015 : Blo 1536465 24946015 := bstep (se 1 (by rfl) ⟨18709511, by rfl⟩ : syracuseStep 24946015 = 37419023) B37419023
theorem B15181175 : Blo 1536465 15181175 := bstep (se 1 (by rfl) ⟨11385881, by rfl⟩ : syracuseStep 15181175 = 22771763) B22771763
theorem B7112329 : Blo 1536465 7112329 := bstep (se 2 (by rfl) ⟨2667123, by rfl⟩ : syracuseStep 7112329 = 5334247) B5334247
theorem B9856673 : Blo 1536465 9856673 := bstep (se 2 (by rfl) ⟨3696252, by rfl⟩ : syracuseStep 9856673 = 7392505) B7392505
theorem B5187563 : Blo 1536465 5187563 := bstep (se 1 (by rfl) ⟨3890672, by rfl⟩ : syracuseStep 5187563 = 7781345) B7781345
theorem B13133825 : Blo 1536465 13133825 := bstep (se 2 (by rfl) ⟨4925184, by rfl⟩ : syracuseStep 13133825 = 9850369) B9850369
theorem B1730623 : Blo 1536465 1730623 := bstep (se 1 (by rfl) ⟨1297967, by rfl⟩ : syracuseStep 1730623 = 2595935) B2595935
theorem B29558945 : Blo 1536465 29558945 := bstep (se 2 (by rfl) ⟨11084604, by rfl⟩ : syracuseStep 29558945 = 22169209) B22169209
theorem B3459383 : Blo 1536465 3459383 := bstep (se 1 (by rfl) ⟨2594537, by rfl⟩ : syracuseStep 3459383 = 5189075) B5189075
theorem B8874607 : Blo 1536465 8874607 := bstep (se 1 (by rfl) ⟨6655955, by rfl⟩ : syracuseStep 8874607 = 13311911) B13311911
theorem B3459743 : Blo 1536465 3459743 := bstep (se 1 (by rfl) ⟨2594807, by rfl⟩ : syracuseStep 3459743 = 5189615) B5189615
theorem B2960033 : Blo 1536465 2960033 := bstep (se 2 (by rfl) ⟨1110012, by rfl⟩ : syracuseStep 2960033 = 2220025) B2220025
theorem B13134575 : Blo 1536465 13134575 := bstep (se 1 (by rfl) ⟨9850931, by rfl⟩ : syracuseStep 13134575 = 19701863) B19701863
theorem B2304809 : Blo 1536465 2304809 := bstep (se 2 (by rfl) ⟨864303, by rfl⟩ : syracuseStep 2304809 = 1728607) B1728607
theorem B2304959 : Blo 1536465 2304959 := bstep (se 1 (by rfl) ⟨1728719, by rfl⟩ : syracuseStep 2304959 = 3457439) B3457439
theorem B19966925 : Blo 1536465 19966925 := bstep (se 3 (by rfl) ⟨3743798, by rfl⟩ : syracuseStep 19966925 = 7487597) B7487597
theorem B22154219 : Blo 1536465 22154219 := bstep (se 1 (by rfl) ⟨16615664, by rfl⟩ : syracuseStep 22154219 = 33231329) B33231329
theorem B11677121 : Blo 1536465 11677121 := bstep (se 2 (by rfl) ⟨4378920, by rfl⟩ : syracuseStep 11677121 = 8757841) B8757841
theorem B2305487 : Blo 1536465 2305487 := bstep (se 1 (by rfl) ⟨1729115, by rfl⟩ : syracuseStep 2305487 = 3458231) B3458231
theorem B7016159 : Blo 1536465 7016159 := bstep (se 1 (by rfl) ⟨5262119, by rfl⟩ : syracuseStep 7016159 = 10524239) B10524239
theorem B172961675 : Blo 1536465 172961675 := bstep (se 1 (by rfl) ⟨129721256, by rfl⟩ : syracuseStep 172961675 = 259442513) B259442513
theorem B2306231 : Blo 1536465 2306231 := bstep (se 1 (by rfl) ⟨1729673, by rfl⟩ : syracuseStep 2306231 = 3459347) B3459347
theorem B2306375 : Blo 1536465 2306375 := bstep (se 1 (by rfl) ⟨1729781, by rfl⟩ : syracuseStep 2306375 = 3459563) B3459563
theorem B8876411 : Blo 1536465 8876411 := bstep (se 1 (by rfl) ⟨6657308, by rfl⟩ : syracuseStep 8876411 = 13314617) B13314617
theorem B1536667 : Blo 1536465 1536667 := bstep (se 1 (by rfl) ⟨1152500, by rfl⟩ : syracuseStep 1536667 = 2305001) B2305001
theorem B2462375 : Blo 1536465 2462375 := bstep (se 1 (by rfl) ⟨1846781, by rfl⟩ : syracuseStep 2462375 = 3693563) B3693563
theorem B2593471 : Blo 1536465 2593471 := bstep (se 1 (by rfl) ⟨1945103, by rfl⟩ : syracuseStep 2593471 = 3890207) B3890207
theorem B2306843 : Blo 1536465 2306843 := bstep (se 1 (by rfl) ⟨1730132, by rfl⟩ : syracuseStep 2306843 = 3460265) B3460265
theorem B14767019 : Blo 1536465 14767019 := bstep (se 1 (by rfl) ⟨11075264, by rfl⟩ : syracuseStep 14767019 = 22150529) B22150529
theorem B2307119 : Blo 1536465 2307119 := bstep (se 1 (by rfl) ⟨1730339, by rfl⟩ : syracuseStep 2307119 = 3460679) B3460679
theorem B2593883 : Blo 1536465 2593883 := bstep (se 1 (by rfl) ⟨1945412, by rfl⟩ : syracuseStep 2593883 = 3890825) B3890825
theorem B1537127 : Blo 1536465 1537127 := bstep (se 1 (by rfl) ⟨1152845, by rfl⟩ : syracuseStep 1537127 = 2305691) B2305691
theorem B4928633 : Blo 1536465 4928633 := bstep (se 2 (by rfl) ⟨1848237, by rfl⟩ : syracuseStep 4928633 = 3696475) B3696475
theorem B2307227 : Blo 1536465 2307227 := bstep (se 1 (by rfl) ⟨1730420, by rfl⟩ : syracuseStep 2307227 = 3460841) B3460841
theorem B2307563 : Blo 1536465 2307563 := bstep (se 1 (by rfl) ⟨1730672, by rfl⟩ : syracuseStep 2307563 = 3461345) B3461345
theorem B19699199 : Blo 1536465 19699199 := bstep (se 1 (by rfl) ⟨14774399, by rfl⟩ : syracuseStep 19699199 = 29548799) B29548799
theorem B89896567 : Blo 1536465 89896567 := bstep (se 1 (by rfl) ⟨67422425, by rfl⟩ : syracuseStep 89896567 = 134844851) B134844851
theorem B1538047 : Blo 1536465 1538047 := bstep (se 1 (by rfl) ⟨1153535, by rfl⟩ : syracuseStep 1538047 = 2307071) B2307071
theorem B1538111 : Blo 1536465 1538111 := bstep (se 1 (by rfl) ⟨1153583, by rfl⟩ : syracuseStep 1538111 = 2307167) B2307167
theorem B17520785 : Blo 1536465 17520785 := bstep (se 2 (by rfl) ⟨6570294, by rfl⟩ : syracuseStep 17520785 = 13140589) B13140589
theorem B1538271 : Blo 1536465 1538271 := bstep (se 1 (by rfl) ⟨1153703, by rfl⟩ : syracuseStep 1538271 = 2307407) B2307407
theorem B24934655 : Blo 1536465 24934655 := bstep (se 1 (by rfl) ⟨18700991, by rfl⟩ : syracuseStep 24934655 = 37401983) B37401983
theorem B239622461 : Blo 1536465 239622461 := bstep (se 3 (by rfl) ⟨44929211, by rfl⟩ : syracuseStep 239622461 = 89858423) B89858423
theorem B1538431 : Blo 1536465 1538431 := bstep (se 1 (by rfl) ⟨1153823, by rfl⟩ : syracuseStep 1538431 = 2307647) B2307647
theorem B3283337 : Blo 1536465 3283337 := bstep (se 2 (by rfl) ⟨1231251, by rfl⟩ : syracuseStep 3283337 = 2462503) B2462503
theorem B3889883 : Blo 1536465 3889883 := bstep (se 1 (by rfl) ⟨2917412, by rfl⟩ : syracuseStep 3889883 = 5834825) B5834825
theorem B1801831 : Blo 1536465 1801831 := bstep (se 1 (by rfl) ⟨1351373, by rfl⟩ : syracuseStep 1801831 = 2702747) B2702747
theorem B3457223 : Blo 1536465 3457223 := bstep (se 1 (by rfl) ⟨2592917, by rfl⟩ : syracuseStep 3457223 = 5185835) B5185835
theorem B2916911 : Blo 1536465 2916911 := bstep (se 1 (by rfl) ⟨2187683, by rfl⟩ : syracuseStep 2916911 = 4375367) B4375367
theorem B1729255 : Blo 1536465 1729255 := bstep (se 1 (by rfl) ⟨1296941, by rfl⟩ : syracuseStep 1729255 = 2593883) B2593883
theorem B3285755 : Blo 1536465 3285755 := bstep (se 1 (by rfl) ⟨2464316, by rfl⟩ : syracuseStep 3285755 = 4928633) B4928633
theorem B3457961 : Blo 1536465 3457961 := bstep (se 2 (by rfl) ⟨1296735, by rfl⟩ : syracuseStep 3457961 = 2593471) B2593471
theorem B13132799 : Blo 1536465 13132799 := bstep (se 1 (by rfl) ⟨9849599, by rfl⟩ : syracuseStep 13132799 = 19699199) B19699199
theorem B6571115 : Blo 1536465 6571115 := bstep (se 1 (by rfl) ⟨4928336, by rfl⟩ : syracuseStep 6571115 = 9856673) B9856673
theorem B3458375 : Blo 1536465 3458375 := bstep (se 1 (by rfl) ⟨2593781, by rfl⟩ : syracuseStep 3458375 = 5187563) B5187563
theorem B16623103 : Blo 1536465 16623103 := bstep (se 1 (by rfl) ⟨12467327, by rfl⟩ : syracuseStep 16623103 = 24934655) B24934655
theorem B2188891 : Blo 1536465 2188891 := bstep (se 1 (by rfl) ⟨1641668, by rfl⟩ : syracuseStep 2188891 = 3283337) B3283337
theorem B5834369 : Blo 1536465 5834369 := bstep (se 2 (by rfl) ⟨2187888, by rfl⟩ : syracuseStep 5834369 = 4375777) B4375777
theorem B31573685 : Blo 1536465 31573685 := bstep (se 5 (by rfl) ⟨1480016, by rfl⟩ : syracuseStep 31573685 = 2960033) B2960033
theorem B16615145 : Blo 1536465 16615145 := bstep (se 2 (by rfl) ⟨6230679, by rfl⟩ : syracuseStep 16615145 = 12461359) B12461359
theorem B33261353 : Blo 1536465 33261353 := bstep (se 2 (by rfl) ⟨12473007, by rfl⟩ : syracuseStep 33261353 = 24946015) B24946015
theorem B2402441 : Blo 1536465 2402441 := bstep (se 2 (by rfl) ⟨900915, by rfl⟩ : syracuseStep 2402441 = 1801831) B1801831
theorem B7784747 : Blo 1536465 7784747 := bstep (se 1 (by rfl) ⟨5838560, by rfl⟩ : syracuseStep 7784747 = 11677121) B11677121
theorem B2304767 : Blo 1536465 2304767 := bstep (se 1 (by rfl) ⟨1728575, by rfl⟩ : syracuseStep 2304767 = 3457151) B3457151
theorem B5917607 : Blo 1536465 5917607 := bstep (se 1 (by rfl) ⟨4438205, by rfl⟩ : syracuseStep 5917607 = 8876411) B8876411
theorem B1641583 : Blo 1536465 1641583 := bstep (se 1 (by rfl) ⟨1231187, by rfl⟩ : syracuseStep 1641583 = 2462375) B2462375
theorem B2305343 : Blo 1536465 2305343 := bstep (se 1 (by rfl) ⟨1729007, by rfl⟩ : syracuseStep 2305343 = 3458015) B3458015
theorem B37932421 : Blo 1536465 37932421 := bstep (se 4 (by rfl) ⟨3556164, by rfl⟩ : syracuseStep 37932421 = 7112329) B7112329
theorem B11832809 : Blo 1536465 11832809 := bstep (se 2 (by rfl) ⟨4437303, by rfl⟩ : syracuseStep 11832809 = 8874607) B8874607
theorem B10120783 : Blo 1536465 10120783 := bstep (se 1 (by rfl) ⟨7590587, by rfl⟩ : syracuseStep 10120783 = 15181175) B15181175
theorem B19705963 : Blo 1536465 19705963 := bstep (se 1 (by rfl) ⟨14779472, by rfl⟩ : syracuseStep 19705963 = 29558945) B29558945
theorem B2306255 : Blo 1536465 2306255 := bstep (se 1 (by rfl) ⟨1729691, by rfl⟩ : syracuseStep 2306255 = 3459383) B3459383
theorem B159748307 : Blo 1536465 159748307 := bstep (se 1 (by rfl) ⟨119811230, by rfl⟩ : syracuseStep 159748307 = 239622461) B239622461
theorem B2306495 : Blo 1536465 2306495 := bstep (se 1 (by rfl) ⟨1729871, by rfl⟩ : syracuseStep 2306495 = 3459743) B3459743
theorem B2593255 : Blo 1536465 2593255 := bstep (se 1 (by rfl) ⟨1944941, by rfl⟩ : syracuseStep 2593255 = 3889883) B3889883
theorem B1536539 : Blo 1536465 1536539 := bstep (se 1 (by rfl) ⟨1152404, by rfl⟩ : syracuseStep 1536539 = 2304809) B2304809
theorem B1536639 : Blo 1536465 1536639 := bstep (se 1 (by rfl) ⟨1152479, by rfl⟩ : syracuseStep 1536639 = 2304959) B2304959
theorem B119862089 : Blo 1536465 119862089 := bstep (se 2 (by rfl) ⟨44948283, by rfl⟩ : syracuseStep 119862089 = 89896567) B89896567
theorem B1536991 : Blo 1536465 1536991 := bstep (se 1 (by rfl) ⟨1152743, by rfl⟩ : syracuseStep 1536991 = 2305487) B2305487
theorem B115307783 : Blo 1536465 115307783 := bstep (se 1 (by rfl) ⟨86480837, by rfl⟩ : syracuseStep 115307783 = 172961675) B172961675
theorem B2307497 : Blo 1536465 2307497 := bstep (se 2 (by rfl) ⟨865311, by rfl⟩ : syracuseStep 2307497 = 1730623) B1730623
theorem B1537487 : Blo 1536465 1537487 := bstep (se 1 (by rfl) ⟨1153115, by rfl⟩ : syracuseStep 1537487 = 2306231) B2306231
theorem B1537583 : Blo 1536465 1537583 := bstep (se 1 (by rfl) ⟨1153187, by rfl⟩ : syracuseStep 1537583 = 2306375) B2306375
theorem B1537895 : Blo 1536465 1537895 := bstep (se 1 (by rfl) ⟨1153421, by rfl⟩ : syracuseStep 1537895 = 2306843) B2306843
theorem B9844679 : Blo 1536465 9844679 := bstep (se 1 (by rfl) ⟨7383509, by rfl⟩ : syracuseStep 9844679 = 14767019) B14767019
theorem B1538079 : Blo 1536465 1538079 := bstep (se 1 (by rfl) ⟨1153559, by rfl⟩ : syracuseStep 1538079 = 2307119) B2307119
theorem B28039223 : Blo 1536465 28039223 := bstep (se 1 (by rfl) ⟨21029417, by rfl⟩ : syracuseStep 28039223 = 42058835) B42058835
theorem B1538151 : Blo 1536465 1538151 := bstep (se 1 (by rfl) ⟨1153613, by rfl⟩ : syracuseStep 1538151 = 2307227) B2307227
theorem B2594983 : Blo 1536465 2594983 := bstep (se 1 (by rfl) ⟨1946237, by rfl⟩ : syracuseStep 2594983 = 3892475) B3892475
theorem B11671775 : Blo 1536465 11671775 := bstep (se 1 (by rfl) ⟨8753831, by rfl⟩ : syracuseStep 11671775 = 17507663) B17507663
theorem B1538375 : Blo 1536465 1538375 := bstep (se 1 (by rfl) ⟨1153781, by rfl⟩ : syracuseStep 1538375 = 2307563) B2307563
theorem B3889529 : Blo 1536465 3889529 := bstep (se 2 (by rfl) ⟨1458573, by rfl⟩ : syracuseStep 3889529 = 2917147) B2917147
theorem B8755883 : Blo 1536465 8755883 := bstep (se 1 (by rfl) ⟨6566912, by rfl⟩ : syracuseStep 8755883 = 13133825) B13133825
theorem B11680523 : Blo 1536465 11680523 := bstep (se 1 (by rfl) ⟨8760392, by rfl⟩ : syracuseStep 11680523 = 17520785) B17520785
theorem B8756383 : Blo 1536465 8756383 := bstep (se 1 (by rfl) ⟨6567287, by rfl⟩ : syracuseStep 8756383 = 13134575) B13134575
theorem B13311283 : Blo 1536465 13311283 := bstep (se 1 (by rfl) ⟨9983462, by rfl⟩ : syracuseStep 13311283 = 19966925) B19966925
theorem B14769479 : Blo 1536465 14769479 := bstep (se 1 (by rfl) ⟨11077109, by rfl⟩ : syracuseStep 14769479 = 22154219) B22154219
theorem B4677439 : Blo 1536465 4677439 := bstep (se 1 (by rfl) ⟨3508079, by rfl⟩ : syracuseStep 4677439 = 7016159) B7016159
theorem B3457673 : Blo 1536465 3457673 := bstep (se 2 (by rfl) ⟨1296627, by rfl⟩ : syracuseStep 3457673 = 2593255) B2593255
theorem B11076763 : Blo 1536465 11076763 := bstep (se 1 (by rfl) ⟨8307572, by rfl⟩ : syracuseStep 11076763 = 16615145) B16615145
theorem B6563119 : Blo 1536465 6563119 := bstep (se 1 (by rfl) ⟨4922339, by rfl⟩ : syracuseStep 6563119 = 9844679) B9844679
theorem B2188777 : Blo 1536465 2188777 := bstep (se 2 (by rfl) ⟨820791, by rfl⟩ : syracuseStep 2188777 = 1641583) B1641583
theorem B11675177 : Blo 1536465 11675177 := bstep (se 2 (by rfl) ⟨4378191, by rfl⟩ : syracuseStep 11675177 = 8756383) B8756383
theorem B13494377 : Blo 1536465 13494377 := bstep (se 2 (by rfl) ⟨5060391, by rfl⟩ : syracuseStep 13494377 = 10120783) B10120783
theorem B2918521 : Blo 1536465 2918521 := bstep (se 2 (by rfl) ⟨1094445, by rfl⟩ : syracuseStep 2918521 = 2188891) B2188891
theorem B6236585 : Blo 1536465 6236585 := bstep (se 2 (by rfl) ⟨2338719, by rfl⟩ : syracuseStep 6236585 = 4677439) B4677439
theorem B2304815 : Blo 1536465 2304815 := bstep (se 1 (by rfl) ⟨1728611, by rfl⟩ : syracuseStep 2304815 = 3457223) B3457223
theorem B106498871 : Blo 1536465 106498871 := bstep (se 1 (by rfl) ⟨79874153, by rfl⟩ : syracuseStep 106498871 = 159748307) B159748307
theorem B26274617 : Blo 1536465 26274617 := bstep (se 2 (by rfl) ⟨9852981, by rfl⟩ : syracuseStep 26274617 = 19705963) B19705963
theorem B74771261 : Blo 1536465 74771261 := bstep (se 3 (by rfl) ⟨14019611, by rfl⟩ : syracuseStep 74771261 = 28039223) B28039223
theorem B3459977 : Blo 1536465 3459977 := bstep (se 2 (by rfl) ⟨1297491, by rfl⟩ : syracuseStep 3459977 = 2594983) B2594983
theorem B2190503 : Blo 1536465 2190503 := bstep (se 1 (by rfl) ⟨1642877, by rfl⟩ : syracuseStep 2190503 = 3285755) B3285755
theorem B79908059 : Blo 1536465 79908059 := bstep (se 1 (by rfl) ⟨59931044, by rfl⟩ : syracuseStep 79908059 = 119862089) B119862089
theorem B2305307 : Blo 1536465 2305307 := bstep (se 1 (by rfl) ⟨1728980, by rfl⟩ : syracuseStep 2305307 = 3457961) B3457961
theorem B2305583 : Blo 1536465 2305583 := bstep (se 1 (by rfl) ⟨1729187, by rfl⟩ : syracuseStep 2305583 = 3458375) B3458375
theorem B2305673 : Blo 1536465 2305673 := bstep (se 2 (by rfl) ⟨864627, by rfl⟩ : syracuseStep 2305673 = 1729255) B1729255
theorem B1601627 : Blo 1536465 1601627 := bstep (se 1 (by rfl) ⟨1201220, by rfl⟩ : syracuseStep 1601627 = 2402441) B2402441
theorem B7778429 : Blo 1536465 7778429 := bstep (se 3 (by rfl) ⟨1458455, by rfl⟩ : syracuseStep 7778429 = 2916911) B2916911
theorem B5189831 : Blo 1536465 5189831 := bstep (se 1 (by rfl) ⟨3892373, by rfl⟩ : syracuseStep 5189831 = 7784747) B7784747
theorem B2593019 : Blo 1536465 2593019 := bstep (se 1 (by rfl) ⟨1944764, by rfl⟩ : syracuseStep 2593019 = 3889529) B3889529
theorem B17748377 : Blo 1536465 17748377 := bstep (se 2 (by rfl) ⟨6655641, by rfl⟩ : syracuseStep 17748377 = 13311283) B13311283
theorem B5837255 : Blo 1536465 5837255 := bstep (se 1 (by rfl) ⟨4377941, by rfl⟩ : syracuseStep 5837255 = 8755883) B8755883
theorem B1536511 : Blo 1536465 1536511 := bstep (se 1 (by rfl) ⟨1152383, by rfl⟩ : syracuseStep 1536511 = 2304767) B2304767
theorem B7787015 : Blo 1536465 7787015 := bstep (se 1 (by rfl) ⟨5840261, by rfl⟩ : syracuseStep 7787015 = 11680523) B11680523
theorem B3945071 : Blo 1536465 3945071 := bstep (se 1 (by rfl) ⟨2958803, by rfl⟩ : syracuseStep 3945071 = 5917607) B5917607
theorem B22164137 : Blo 1536465 22164137 := bstep (se 2 (by rfl) ⟨8311551, by rfl⟩ : syracuseStep 22164137 = 16623103) B16623103
theorem B1536895 : Blo 1536465 1536895 := bstep (se 1 (by rfl) ⟨1152671, by rfl⟩ : syracuseStep 1536895 = 2305343) B2305343
theorem B1537503 : Blo 1536465 1537503 := bstep (se 1 (by rfl) ⟨1153127, by rfl⟩ : syracuseStep 1537503 = 2306255) B2306255
theorem B1537663 : Blo 1536465 1537663 := bstep (se 1 (by rfl) ⟨1153247, by rfl⟩ : syracuseStep 1537663 = 2306495) B2306495
theorem B8755199 : Blo 1536465 8755199 := bstep (se 1 (by rfl) ⟨6566399, by rfl⟩ : syracuseStep 8755199 = 13132799) B13132799
theorem B4380743 : Blo 1536465 4380743 := bstep (se 1 (by rfl) ⟨3285557, by rfl⟩ : syracuseStep 4380743 = 6571115) B6571115
theorem B76871855 : Blo 1536465 76871855 := bstep (se 1 (by rfl) ⟨57653891, by rfl⟩ : syracuseStep 76871855 = 115307783) B115307783
theorem B1538331 : Blo 1536465 1538331 := bstep (se 1 (by rfl) ⟨1153748, by rfl⟩ : syracuseStep 1538331 = 2307497) B2307497
theorem B3889579 : Blo 1536465 3889579 := bstep (se 1 (by rfl) ⟨2917184, by rfl⟩ : syracuseStep 3889579 = 5834369) B5834369
theorem B22174235 : Blo 1536465 22174235 := bstep (se 1 (by rfl) ⟨16630676, by rfl⟩ : syracuseStep 22174235 = 33261353) B33261353
theorem B31554157 : Blo 1536465 31554157 := bstep (se 3 (by rfl) ⟨5916404, by rfl⟩ : syracuseStep 31554157 = 11832809) B11832809
theorem B7781183 : Blo 1536465 7781183 := bstep (se 1 (by rfl) ⟨5835887, by rfl⟩ : syracuseStep 7781183 = 11671775) B11671775
theorem B84196493 : Blo 1536465 84196493 := bstep (se 3 (by rfl) ⟨15786842, by rfl⟩ : syracuseStep 84196493 = 31573685) B31573685
theorem B50576561 : Blo 1536465 50576561 := bstep (se 2 (by rfl) ⟨18966210, by rfl⟩ : syracuseStep 50576561 = 37932421) B37932421
theorem B9846319 : Blo 1536465 9846319 := bstep (se 1 (by rfl) ⟨7384739, by rfl⟩ : syracuseStep 9846319 = 14769479) B14769479
theorem B5185619 : Blo 1536465 5185619 := bstep (se 1 (by rfl) ⟨3889214, by rfl⟩ : syracuseStep 5185619 = 7778429) B7778429
theorem B3891361 : Blo 1536465 3891361 := bstep (se 2 (by rfl) ⟨1459260, by rfl⟩ : syracuseStep 3891361 = 2918521) B2918521
theorem B1728679 : Blo 1536465 1728679 := bstep (se 1 (by rfl) ⟨1296509, by rfl⟩ : syracuseStep 1728679 = 2593019) B2593019
theorem B11681981 : Blo 1536465 11681981 := bstep (se 3 (by rfl) ⟨2190371, by rfl⟩ : syracuseStep 11681981 = 4380743) B4380743
theorem B3891503 : Blo 1536465 3891503 := bstep (se 1 (by rfl) ⟨2918627, by rfl⟩ : syracuseStep 3891503 = 5837255) B5837255
theorem B5841341 : Blo 1536465 5841341 := bstep (se 3 (by rfl) ⟨1095251, by rfl⟩ : syracuseStep 5841341 = 2190503) B2190503
theorem B5186105 : Blo 1536465 5186105 := bstep (se 2 (by rfl) ⟨1944789, by rfl⟩ : syracuseStep 5186105 = 3889579) B3889579
theorem B7783451 : Blo 1536465 7783451 := bstep (se 1 (by rfl) ⟨5837588, by rfl⟩ : syracuseStep 7783451 = 11675177) B11675177
theorem B10520189 : Blo 1536465 10520189 := bstep (se 3 (by rfl) ⟨1972535, by rfl⟩ : syracuseStep 10520189 = 3945071) B3945071
theorem B8750825 : Blo 1536465 8750825 := bstep (se 2 (by rfl) ⟨3281559, by rfl⟩ : syracuseStep 8750825 = 6563119) B6563119
theorem B17516411 : Blo 1536465 17516411 := bstep (se 1 (by rfl) ⟨13137308, by rfl⟩ : syracuseStep 17516411 = 26274617) B26274617
theorem B5187455 : Blo 1536465 5187455 := bstep (se 1 (by rfl) ⟨3890591, by rfl⟩ : syracuseStep 5187455 = 7781183) B7781183
theorem B2918369 : Blo 1536465 2918369 := bstep (se 2 (by rfl) ⟨1094388, by rfl⟩ : syracuseStep 2918369 = 2188777) B2188777
theorem B3459887 : Blo 1536465 3459887 := bstep (se 1 (by rfl) ⟨2594915, by rfl⟩ : syracuseStep 3459887 = 5189831) B5189831
theorem B4271005 : Blo 1536465 4271005 := bstep (se 3 (by rfl) ⟨800813, by rfl⟩ : syracuseStep 4271005 = 1601627) B1601627
theorem B11832251 : Blo 1536465 11832251 := bstep (se 1 (by rfl) ⟨8874188, by rfl⟩ : syracuseStep 11832251 = 17748377) B17748377
theorem B2305115 : Blo 1536465 2305115 := bstep (se 1 (by rfl) ⟨1728836, by rfl⟩ : syracuseStep 2305115 = 3457673) B3457673
theorem B5836799 : Blo 1536465 5836799 := bstep (se 1 (by rfl) ⟨4377599, by rfl⟩ : syracuseStep 5836799 = 8755199) B8755199
theorem B4157723 : Blo 1536465 4157723 := bstep (se 1 (by rfl) ⟨3118292, by rfl⟩ : syracuseStep 4157723 = 6236585) B6236585
theorem B14782823 : Blo 1536465 14782823 := bstep (se 1 (by rfl) ⟨11087117, by rfl⟩ : syracuseStep 14782823 = 22174235) B22174235
theorem B1536543 : Blo 1536465 1536543 := bstep (se 1 (by rfl) ⟨1152407, by rfl⟩ : syracuseStep 1536543 = 2304815) B2304815
theorem B2306651 : Blo 1536465 2306651 := bstep (se 1 (by rfl) ⟨1729988, by rfl⟩ : syracuseStep 2306651 = 3459977) B3459977
theorem B13128425 : Blo 1536465 13128425 := bstep (se 2 (by rfl) ⟨4923159, by rfl⟩ : syracuseStep 13128425 = 9846319) B9846319
theorem B1536871 : Blo 1536465 1536871 := bstep (se 1 (by rfl) ⟨1152653, by rfl⟩ : syracuseStep 1536871 = 2305307) B2305307
theorem B1537055 : Blo 1536465 1537055 := bstep (se 1 (by rfl) ⟨1152791, by rfl⟩ : syracuseStep 1537055 = 2305583) B2305583
theorem B1537115 : Blo 1536465 1537115 := bstep (se 1 (by rfl) ⟨1152836, by rfl⟩ : syracuseStep 1537115 = 2305673) B2305673
theorem B35985005 : Blo 1536465 35985005 := bstep (se 3 (by rfl) ⟨6747188, by rfl⟩ : syracuseStep 35985005 = 13494377) B13494377
theorem B5191343 : Blo 1536465 5191343 := bstep (se 1 (by rfl) ⟨3893507, by rfl⟩ : syracuseStep 5191343 = 7787015) B7787015
theorem B14776091 : Blo 1536465 14776091 := bstep (se 1 (by rfl) ⟨11082068, by rfl⟩ : syracuseStep 14776091 = 22164137) B22164137
theorem B42072209 : Blo 1536465 42072209 := bstep (se 2 (by rfl) ⟨15777078, by rfl⟩ : syracuseStep 42072209 = 31554157) B31554157
theorem B51247903 : Blo 1536465 51247903 := bstep (se 1 (by rfl) ⟨38435927, by rfl⟩ : syracuseStep 51247903 = 76871855) B76871855
theorem B14769017 : Blo 1536465 14769017 := bstep (se 2 (by rfl) ⟨5538381, by rfl⟩ : syracuseStep 14769017 = 11076763) B11076763
theorem B70999247 : Blo 1536465 70999247 := bstep (se 1 (by rfl) ⟨53249435, by rfl⟩ : syracuseStep 70999247 = 106498871) B106498871
theorem B49847507 : Blo 1536465 49847507 := bstep (se 1 (by rfl) ⟨37385630, by rfl⟩ : syracuseStep 49847507 = 74771261) B74771261
theorem B56130995 : Blo 1536465 56130995 := bstep (se 1 (by rfl) ⟨42098246, by rfl⟩ : syracuseStep 56130995 = 84196493) B84196493
theorem B33717707 : Blo 1536465 33717707 := bstep (se 1 (by rfl) ⟨25288280, by rfl⟩ : syracuseStep 33717707 = 50576561) B50576561
theorem B53272039 : Blo 1536465 53272039 := bstep (se 1 (by rfl) ⟨39954029, by rfl⟩ : syracuseStep 53272039 = 79908059) B79908059
theorem B3457079 : Blo 1536465 3457079 := bstep (se 1 (by rfl) ⟨2592809, by rfl⟩ : syracuseStep 3457079 = 5185619) B5185619
theorem B9855215 : Blo 1536465 9855215 := bstep (se 1 (by rfl) ⟨7391411, by rfl⟩ : syracuseStep 9855215 = 14782823) B14782823
theorem B3457403 : Blo 1536465 3457403 := bstep (se 1 (by rfl) ⟨2593052, by rfl⟩ : syracuseStep 3457403 = 5186105) B5186105
theorem B68330537 : Blo 1536465 68330537 := bstep (se 2 (by rfl) ⟨25623951, by rfl⟩ : syracuseStep 68330537 = 51247903) B51247903
theorem B7013459 : Blo 1536465 7013459 := bstep (se 1 (by rfl) ⟨5260094, by rfl⟩ : syracuseStep 7013459 = 10520189) B10520189
theorem B5833883 : Blo 1536465 5833883 := bstep (se 1 (by rfl) ⟨4375412, by rfl⟩ : syracuseStep 5833883 = 8750825) B8750825
theorem B5694673 : Blo 1536465 5694673 := bstep (se 2 (by rfl) ⟨2135502, by rfl⟩ : syracuseStep 5694673 = 4271005) B4271005
theorem B3458303 : Blo 1536465 3458303 := bstep (se 1 (by rfl) ⟨2593727, by rfl⟩ : syracuseStep 3458303 = 5187455) B5187455
theorem B2771815 : Blo 1536465 2771815 := bstep (se 1 (by rfl) ⟨2078861, by rfl⟩ : syracuseStep 2771815 = 4157723) B4157723
theorem B5188481 : Blo 1536465 5188481 := bstep (se 2 (by rfl) ⟨1945680, by rfl⟩ : syracuseStep 5188481 = 3891361) B3891361
theorem B2304905 : Blo 1536465 2304905 := bstep (se 2 (by rfl) ⟨864339, by rfl⟩ : syracuseStep 2304905 = 1728679) B1728679
theorem B3894227 : Blo 1536465 3894227 := bstep (se 1 (by rfl) ⟨2920670, by rfl⟩ : syracuseStep 3894227 = 5841341) B5841341
theorem B8752283 : Blo 1536465 8752283 := bstep (se 1 (by rfl) ⟨6564212, by rfl⟩ : syracuseStep 8752283 = 13128425) B13128425
theorem B5188967 : Blo 1536465 5188967 := bstep (se 1 (by rfl) ⟨3891725, by rfl⟩ : syracuseStep 5188967 = 7783451) B7783451
theorem B23990003 : Blo 1536465 23990003 := bstep (se 1 (by rfl) ⟨17992502, by rfl⟩ : syracuseStep 23990003 = 35985005) B35985005
theorem B3460895 : Blo 1536465 3460895 := bstep (se 1 (by rfl) ⟨2595671, by rfl⟩ : syracuseStep 3460895 = 5191343) B5191343
theorem B9850727 : Blo 1536465 9850727 := bstep (se 1 (by rfl) ⟨7388045, by rfl⟩ : syracuseStep 9850727 = 14776091) B14776091
theorem B11677607 : Blo 1536465 11677607 := bstep (se 1 (by rfl) ⟨8758205, by rfl⟩ : syracuseStep 11677607 = 17516411) B17516411
theorem B2306591 : Blo 1536465 2306591 := bstep (se 1 (by rfl) ⟨1729943, by rfl⟩ : syracuseStep 2306591 = 3459887) B3459887
theorem B71029385 : Blo 1536465 71029385 := bstep (se 2 (by rfl) ⟨26636019, by rfl⟩ : syracuseStep 71029385 = 53272039) B53272039
theorem B1536743 : Blo 1536465 1536743 := bstep (se 1 (by rfl) ⟨1152557, by rfl⟩ : syracuseStep 1536743 = 2305115) B2305115
theorem B33231671 : Blo 1536465 33231671 := bstep (se 1 (by rfl) ⟨24923753, by rfl⟩ : syracuseStep 33231671 = 49847507) B49847507
theorem B31552669 : Blo 1536465 31552669 := bstep (se 3 (by rfl) ⟨5916125, by rfl⟩ : syracuseStep 31552669 = 11832251) B11832251
theorem B7787987 : Blo 1536465 7787987 := bstep (se 1 (by rfl) ⟨5840990, by rfl⟩ : syracuseStep 7787987 = 11681981) B11681981
theorem B2594335 : Blo 1536465 2594335 := bstep (se 1 (by rfl) ⟨1945751, by rfl⟩ : syracuseStep 2594335 = 3891503) B3891503
theorem B1537767 : Blo 1536465 1537767 := bstep (se 1 (by rfl) ⟨1153325, by rfl⟩ : syracuseStep 1537767 = 2306651) B2306651
theorem B149682653 : Blo 1536465 149682653 := bstep (se 3 (by rfl) ⟨28065497, by rfl⟩ : syracuseStep 149682653 = 56130995) B56130995
theorem B28048139 : Blo 1536465 28048139 := bstep (se 1 (by rfl) ⟨21036104, by rfl⟩ : syracuseStep 28048139 = 42072209) B42072209
theorem B9846011 : Blo 1536465 9846011 := bstep (se 1 (by rfl) ⟨7384508, by rfl⟩ : syracuseStep 9846011 = 14769017) B14769017
theorem B47332831 : Blo 1536465 47332831 := bstep (se 1 (by rfl) ⟨35499623, by rfl⟩ : syracuseStep 47332831 = 70999247) B70999247
theorem B22478471 : Blo 1536465 22478471 := bstep (se 1 (by rfl) ⟨16858853, by rfl⟩ : syracuseStep 22478471 = 33717707) B33717707
theorem B7782317 : Blo 1536465 7782317 := bstep (se 3 (by rfl) ⟨1459184, by rfl⟩ : syracuseStep 7782317 = 2918369) B2918369
theorem B3891199 : Blo 1536465 3891199 := bstep (se 1 (by rfl) ⟨2918399, by rfl⟩ : syracuseStep 3891199 = 5836799) B5836799
theorem B6570143 : Blo 1536465 6570143 := bstep (se 1 (by rfl) ⟨4927607, by rfl⟩ : syracuseStep 6570143 = 9855215) B9855215
theorem B3695753 : Blo 1536465 3695753 := bstep (se 2 (by rfl) ⟨1385907, by rfl⟩ : syracuseStep 3695753 = 2771815) B2771815
theorem B99788435 : Blo 1536465 99788435 := bstep (se 1 (by rfl) ⟨74841326, by rfl⟩ : syracuseStep 99788435 = 149682653) B149682653
theorem B3458987 : Blo 1536465 3458987 := bstep (se 1 (by rfl) ⟨2594240, by rfl⟩ : syracuseStep 3458987 = 5188481) B5188481
theorem B3459113 : Blo 1536465 3459113 := bstep (se 2 (by rfl) ⟨1297167, by rfl⟩ : syracuseStep 3459113 = 2594335) B2594335
theorem B5834855 : Blo 1536465 5834855 := bstep (se 1 (by rfl) ⟨4376141, by rfl⟩ : syracuseStep 5834855 = 8752283) B8752283
theorem B6564007 : Blo 1536465 6564007 := bstep (se 1 (by rfl) ⟨4923005, by rfl⟩ : syracuseStep 6564007 = 9846011) B9846011
theorem B3459311 : Blo 1536465 3459311 := bstep (se 1 (by rfl) ⟨2594483, by rfl⟩ : syracuseStep 3459311 = 5188967) B5188967
theorem B14985647 : Blo 1536465 14985647 := bstep (se 1 (by rfl) ⟨11239235, by rfl⟩ : syracuseStep 14985647 = 22478471) B22478471
theorem B15993335 : Blo 1536465 15993335 := bstep (se 1 (by rfl) ⟨11995001, by rfl⟩ : syracuseStep 15993335 = 23990003) B23990003
theorem B7785071 : Blo 1536465 7785071 := bstep (se 1 (by rfl) ⟨5838803, by rfl⟩ : syracuseStep 7785071 = 11677607) B11677607
theorem B5188211 : Blo 1536465 5188211 := bstep (se 1 (by rfl) ⟨3891158, by rfl⟩ : syracuseStep 5188211 = 7782317) B7782317
theorem B5188265 : Blo 1536465 5188265 := bstep (se 2 (by rfl) ⟨1945599, by rfl⟩ : syracuseStep 5188265 = 3891199) B3891199
theorem B2304719 : Blo 1536465 2304719 := bstep (se 1 (by rfl) ⟨1728539, by rfl⟩ : syracuseStep 2304719 = 3457079) B3457079
theorem B2304935 : Blo 1536465 2304935 := bstep (se 1 (by rfl) ⟨1728701, by rfl⟩ : syracuseStep 2304935 = 3457403) B3457403
theorem B47352923 : Blo 1536465 47352923 := bstep (se 1 (by rfl) ⟨35514692, by rfl⟩ : syracuseStep 47352923 = 71029385) B71029385
theorem B22154447 : Blo 1536465 22154447 := bstep (se 1 (by rfl) ⟨16615835, by rfl⟩ : syracuseStep 22154447 = 33231671) B33231671
theorem B2305535 : Blo 1536465 2305535 := bstep (se 1 (by rfl) ⟨1729151, by rfl⟩ : syracuseStep 2305535 = 3458303) B3458303
theorem B42070225 : Blo 1536465 42070225 := bstep (se 2 (by rfl) ⟨15776334, by rfl⟩ : syracuseStep 42070225 = 31552669) B31552669
theorem B18698759 : Blo 1536465 18698759 := bstep (se 1 (by rfl) ⟨14024069, by rfl⟩ : syracuseStep 18698759 = 28048139) B28048139
theorem B1536603 : Blo 1536465 1536603 := bstep (se 1 (by rfl) ⟨1152452, by rfl⟩ : syracuseStep 1536603 = 2304905) B2304905
theorem B2307263 : Blo 1536465 2307263 := bstep (se 1 (by rfl) ⟨1730447, by rfl⟩ : syracuseStep 2307263 = 3460895) B3460895
theorem B6567151 : Blo 1536465 6567151 := bstep (se 1 (by rfl) ⟨4925363, by rfl⟩ : syracuseStep 6567151 = 9850727) B9850727
theorem B1537727 : Blo 1536465 1537727 := bstep (se 1 (by rfl) ⟨1153295, by rfl⟩ : syracuseStep 1537727 = 2306591) B2306591
theorem B45553691 : Blo 1536465 45553691 := bstep (se 1 (by rfl) ⟨34165268, by rfl⟩ : syracuseStep 45553691 = 68330537) B68330537
theorem B4675639 : Blo 1536465 4675639 := bstep (se 1 (by rfl) ⟨3506729, by rfl⟩ : syracuseStep 4675639 = 7013459) B7013459
theorem B3889255 : Blo 1536465 3889255 := bstep (se 1 (by rfl) ⟨2916941, by rfl⟩ : syracuseStep 3889255 = 5833883) B5833883
theorem B5191991 : Blo 1536465 5191991 := bstep (se 1 (by rfl) ⟨3893993, by rfl⟩ : syracuseStep 5191991 = 7787987) B7787987
theorem B7592897 : Blo 1536465 7592897 := bstep (se 2 (by rfl) ⟨2847336, by rfl⟩ : syracuseStep 7592897 = 5694673) B5694673
theorem B63110441 : Blo 1536465 63110441 := bstep (se 2 (by rfl) ⟨23666415, by rfl⟩ : syracuseStep 63110441 = 47332831) B47332831
theorem B2596151 : Blo 1536465 2596151 := bstep (se 1 (by rfl) ⟨1947113, by rfl⟩ : syracuseStep 2596151 = 3894227) B3894227
theorem B6234185 : Blo 1536465 6234185 := bstep (se 2 (by rfl) ⟨2337819, by rfl⟩ : syracuseStep 6234185 = 4675639) B4675639
theorem B5185673 : Blo 1536465 5185673 := bstep (se 2 (by rfl) ⟨1944627, by rfl⟩ : syracuseStep 5185673 = 3889255) B3889255
theorem B9855341 : Blo 1536465 9855341 := bstep (se 3 (by rfl) ⟨1847876, by rfl⟩ : syracuseStep 9855341 = 3695753) B3695753
theorem B42648893 : Blo 1536465 42648893 := bstep (se 3 (by rfl) ⟨7996667, by rfl⟩ : syracuseStep 42648893 = 15993335) B15993335
theorem B30369127 : Blo 1536465 30369127 := bstep (se 1 (by rfl) ⟨22776845, by rfl⟩ : syracuseStep 30369127 = 45553691) B45553691
theorem B3458807 : Blo 1536465 3458807 := bstep (se 1 (by rfl) ⟨2594105, by rfl⟩ : syracuseStep 3458807 = 5188211) B5188211
theorem B3458843 : Blo 1536465 3458843 := bstep (se 1 (by rfl) ⟨2594132, by rfl⟩ : syracuseStep 3458843 = 5188265) B5188265
theorem B1730767 : Blo 1536465 1730767 := bstep (se 1 (by rfl) ⟨1298075, by rfl⟩ : syracuseStep 1730767 = 2596151) B2596151
theorem B8752009 : Blo 1536465 8752009 := bstep (se 2 (by rfl) ⟨3282003, by rfl⟩ : syracuseStep 8752009 = 6564007) B6564007
theorem B56093633 : Blo 1536465 56093633 := bstep (se 2 (by rfl) ⟨21035112, by rfl⟩ : syracuseStep 56093633 = 42070225) B42070225
theorem B2305991 : Blo 1536465 2305991 := bstep (se 1 (by rfl) ⟨1729493, by rfl⟩ : syracuseStep 2305991 = 3458987) B3458987
theorem B2306075 : Blo 1536465 2306075 := bstep (se 1 (by rfl) ⟨1729556, by rfl⟩ : syracuseStep 2306075 = 3459113) B3459113
theorem B2306207 : Blo 1536465 2306207 := bstep (se 1 (by rfl) ⟨1729655, by rfl⟩ : syracuseStep 2306207 = 3459311) B3459311
theorem B3461327 : Blo 1536465 3461327 := bstep (se 1 (by rfl) ⟨2595995, by rfl⟩ : syracuseStep 3461327 = 5191991) B5191991
theorem B9990431 : Blo 1536465 9990431 := bstep (se 1 (by rfl) ⟨7492823, by rfl⟩ : syracuseStep 9990431 = 14985647) B14985647
theorem B5190047 : Blo 1536465 5190047 := bstep (se 1 (by rfl) ⟨3892535, by rfl⟩ : syracuseStep 5190047 = 7785071) B7785071
theorem B1536479 : Blo 1536465 1536479 := bstep (se 1 (by rfl) ⟨1152359, by rfl⟩ : syracuseStep 1536479 = 2304719) B2304719
theorem B1536623 : Blo 1536465 1536623 := bstep (se 1 (by rfl) ⟨1152467, by rfl⟩ : syracuseStep 1536623 = 2304935) B2304935
theorem B31568615 : Blo 1536465 31568615 := bstep (se 1 (by rfl) ⟨23676461, by rfl⟩ : syracuseStep 31568615 = 47352923) B47352923
theorem B1537023 : Blo 1536465 1537023 := bstep (se 1 (by rfl) ⟨1152767, by rfl⟩ : syracuseStep 1537023 = 2305535) B2305535
theorem B20247725 : Blo 1536465 20247725 := bstep (se 3 (by rfl) ⟨3796448, by rfl⟩ : syracuseStep 20247725 = 7592897) B7592897
theorem B4380095 : Blo 1536465 4380095 := bstep (se 1 (by rfl) ⟨3285071, by rfl⟩ : syracuseStep 4380095 = 6570143) B6570143
theorem B12465839 : Blo 1536465 12465839 := bstep (se 1 (by rfl) ⟨9349379, by rfl⟩ : syracuseStep 12465839 = 18698759) B18698759
theorem B1538175 : Blo 1536465 1538175 := bstep (se 1 (by rfl) ⟨1153631, by rfl⟩ : syracuseStep 1538175 = 2307263) B2307263
theorem B66525623 : Blo 1536465 66525623 := bstep (se 1 (by rfl) ⟨49894217, by rfl⟩ : syracuseStep 66525623 = 99788435) B99788435
theorem B3889903 : Blo 1536465 3889903 := bstep (se 1 (by rfl) ⟨2917427, by rfl⟩ : syracuseStep 3889903 = 5834855) B5834855
theorem B8756201 : Blo 1536465 8756201 := bstep (se 2 (by rfl) ⟨3283575, by rfl⟩ : syracuseStep 8756201 = 6567151) B6567151
theorem B14769631 : Blo 1536465 14769631 := bstep (se 1 (by rfl) ⟨11077223, by rfl⟩ : syracuseStep 14769631 = 22154447) B22154447
theorem B42073627 : Blo 1536465 42073627 := bstep (se 1 (by rfl) ⟨31555220, by rfl⟩ : syracuseStep 42073627 = 63110441) B63110441
theorem B3457115 : Blo 1536465 3457115 := bstep (se 1 (by rfl) ⟨2592836, by rfl⟩ : syracuseStep 3457115 = 5185673) B5185673
theorem B6660287 : Blo 1536465 6660287 := bstep (se 1 (by rfl) ⟨4995215, by rfl⟩ : syracuseStep 6660287 = 9990431) B9990431
theorem B6570227 : Blo 1536465 6570227 := bstep (se 1 (by rfl) ⟨4927670, by rfl⟩ : syracuseStep 6570227 = 9855341) B9855341
theorem B21045743 : Blo 1536465 21045743 := bstep (se 1 (by rfl) ⟨15784307, by rfl⟩ : syracuseStep 21045743 = 31568615) B31568615
theorem B5186537 : Blo 1536465 5186537 := bstep (se 2 (by rfl) ⟨1944951, by rfl⟩ : syracuseStep 5186537 = 3889903) B3889903
theorem B4156123 : Blo 1536465 4156123 := bstep (se 1 (by rfl) ⟨3117092, by rfl⟩ : syracuseStep 4156123 = 6234185) B6234185
theorem B3460031 : Blo 1536465 3460031 := bstep (se 1 (by rfl) ⟨2595023, by rfl⟩ : syracuseStep 3460031 = 5190047) B5190047
theorem B2920063 : Blo 1536465 2920063 := bstep (se 1 (by rfl) ⟨2190047, by rfl⟩ : syracuseStep 2920063 = 4380095) B4380095
theorem B8310559 : Blo 1536465 8310559 := bstep (se 1 (by rfl) ⟨6232919, by rfl⟩ : syracuseStep 8310559 = 12465839) B12465839
theorem B2305871 : Blo 1536465 2305871 := bstep (se 1 (by rfl) ⟨1729403, by rfl⟩ : syracuseStep 2305871 = 3458807) B3458807
theorem B11669345 : Blo 1536465 11669345 := bstep (se 2 (by rfl) ⟨4376004, by rfl⟩ : syracuseStep 11669345 = 8752009) B8752009
theorem B2305895 : Blo 1536465 2305895 := bstep (se 1 (by rfl) ⟨1729421, by rfl⟩ : syracuseStep 2305895 = 3458843) B3458843
theorem B5837467 : Blo 1536465 5837467 := bstep (se 1 (by rfl) ⟨4378100, by rfl⟩ : syracuseStep 5837467 = 8756201) B8756201
theorem B1537327 : Blo 1536465 1537327 := bstep (se 1 (by rfl) ⟨1152995, by rfl⟩ : syracuseStep 1537327 = 2305991) B2305991
theorem B1537383 : Blo 1536465 1537383 := bstep (se 1 (by rfl) ⟨1153037, by rfl⟩ : syracuseStep 1537383 = 2306075) B2306075
theorem B1537471 : Blo 1536465 1537471 := bstep (se 1 (by rfl) ⟨1153103, by rfl⟩ : syracuseStep 1537471 = 2306207) B2306207
theorem B2307551 : Blo 1536465 2307551 := bstep (se 1 (by rfl) ⟨1730663, by rfl⟩ : syracuseStep 2307551 = 3461327) B3461327
theorem B2307689 : Blo 1536465 2307689 := bstep (se 2 (by rfl) ⟨865383, by rfl⟩ : syracuseStep 2307689 = 1730767) B1730767
theorem B13498483 : Blo 1536465 13498483 := bstep (se 1 (by rfl) ⟨10123862, by rfl⟩ : syracuseStep 13498483 = 20247725) B20247725
theorem B28432595 : Blo 1536465 28432595 := bstep (se 1 (by rfl) ⟨21324446, by rfl⟩ : syracuseStep 28432595 = 42648893) B42648893
theorem B44350415 : Blo 1536465 44350415 := bstep (se 1 (by rfl) ⟨33262811, by rfl⟩ : syracuseStep 44350415 = 66525623) B66525623
theorem B40492169 : Blo 1536465 40492169 := bstep (se 2 (by rfl) ⟨15184563, by rfl⟩ : syracuseStep 40492169 = 30369127) B30369127
theorem B19692841 : Blo 1536465 19692841 := bstep (se 2 (by rfl) ⟨7384815, by rfl⟩ : syracuseStep 19692841 = 14769631) B14769631
theorem B37395755 : Blo 1536465 37395755 := bstep (se 1 (by rfl) ⟨28046816, by rfl⟩ : syracuseStep 37395755 = 56093633) B56093633
theorem B56098169 : Blo 1536465 56098169 := bstep (se 2 (by rfl) ⟨21036813, by rfl⟩ : syracuseStep 56098169 = 42073627) B42073627
theorem B4440191 : Blo 1536465 4440191 := bstep (se 1 (by rfl) ⟨3330143, by rfl⟩ : syracuseStep 4440191 = 6660287) B6660287
theorem B17997977 : Blo 1536465 17997977 := bstep (se 2 (by rfl) ⟨6749241, by rfl⟩ : syracuseStep 17997977 = 13498483) B13498483
theorem B3457691 : Blo 1536465 3457691 := bstep (se 1 (by rfl) ⟨2593268, by rfl⟩ : syracuseStep 3457691 = 5186537) B5186537
theorem B7783289 : Blo 1536465 7783289 := bstep (se 2 (by rfl) ⟨2918733, by rfl⟩ : syracuseStep 7783289 = 5837467) B5837467
theorem B26257121 : Blo 1536465 26257121 := bstep (se 2 (by rfl) ⟨9846420, by rfl⟩ : syracuseStep 26257121 = 19692841) B19692841
theorem B29566943 : Blo 1536465 29566943 := bstep (se 1 (by rfl) ⟨22175207, by rfl⟩ : syracuseStep 29566943 = 44350415) B44350415
theorem B26994779 : Blo 1536465 26994779 := bstep (se 1 (by rfl) ⟨20246084, by rfl⟩ : syracuseStep 26994779 = 40492169) B40492169
theorem B3893417 : Blo 1536465 3893417 := bstep (se 2 (by rfl) ⟨1460031, by rfl⟩ : syracuseStep 3893417 = 2920063) B2920063
theorem B24930503 : Blo 1536465 24930503 := bstep (se 1 (by rfl) ⟨18697877, by rfl⟩ : syracuseStep 24930503 = 37395755) B37395755
theorem B37398779 : Blo 1536465 37398779 := bstep (se 1 (by rfl) ⟨28049084, by rfl⟩ : syracuseStep 37398779 = 56098169) B56098169
theorem B2304743 : Blo 1536465 2304743 := bstep (se 1 (by rfl) ⟨1728557, by rfl⟩ : syracuseStep 2304743 = 3457115) B3457115
theorem B5541497 : Blo 1536465 5541497 := bstep (se 2 (by rfl) ⟨2078061, by rfl⟩ : syracuseStep 5541497 = 4156123) B4156123
theorem B2306687 : Blo 1536465 2306687 := bstep (se 1 (by rfl) ⟨1730015, by rfl⟩ : syracuseStep 2306687 = 3460031) B3460031
theorem B11080745 : Blo 1536465 11080745 := bstep (se 2 (by rfl) ⟨4155279, by rfl⟩ : syracuseStep 11080745 = 8310559) B8310559
theorem B1537247 : Blo 1536465 1537247 := bstep (se 1 (by rfl) ⟨1152935, by rfl⟩ : syracuseStep 1537247 = 2305871) B2305871
theorem B7779563 : Blo 1536465 7779563 := bstep (se 1 (by rfl) ⟨5834672, by rfl⟩ : syracuseStep 7779563 = 11669345) B11669345
theorem B1537263 : Blo 1536465 1537263 := bstep (se 1 (by rfl) ⟨1152947, by rfl⟩ : syracuseStep 1537263 = 2305895) B2305895
theorem B4380151 : Blo 1536465 4380151 := bstep (se 1 (by rfl) ⟨3285113, by rfl⟩ : syracuseStep 4380151 = 6570227) B6570227
theorem B14030495 : Blo 1536465 14030495 := bstep (se 1 (by rfl) ⟨10522871, by rfl⟩ : syracuseStep 14030495 = 21045743) B21045743
theorem B1538367 : Blo 1536465 1538367 := bstep (se 1 (by rfl) ⟨1153775, by rfl⟩ : syracuseStep 1538367 = 2307551) B2307551
theorem B1538459 : Blo 1536465 1538459 := bstep (se 1 (by rfl) ⟨1153844, by rfl⟩ : syracuseStep 1538459 = 2307689) B2307689
theorem B18955063 : Blo 1536465 18955063 := bstep (se 1 (by rfl) ⟨14216297, by rfl⟩ : syracuseStep 18955063 = 28432595) B28432595
theorem B5186375 : Blo 1536465 5186375 := bstep (se 1 (by rfl) ⟨3889781, by rfl⟩ : syracuseStep 5186375 = 7779563) B7779563
theorem B25273417 : Blo 1536465 25273417 := bstep (se 2 (by rfl) ⟨9477531, by rfl⟩ : syracuseStep 25273417 = 18955063) B18955063
theorem B19711295 : Blo 1536465 19711295 := bstep (se 1 (by rfl) ⟨14783471, by rfl⟩ : syracuseStep 19711295 = 29566943) B29566943
theorem B11840509 : Blo 1536465 11840509 := bstep (se 3 (by rfl) ⟨2220095, by rfl⟩ : syracuseStep 11840509 = 4440191) B4440191
theorem B2305127 : Blo 1536465 2305127 := bstep (se 1 (by rfl) ⟨1728845, by rfl⟩ : syracuseStep 2305127 = 3457691) B3457691
theorem B5188859 : Blo 1536465 5188859 := bstep (se 1 (by rfl) ⟨3891644, by rfl⟩ : syracuseStep 5188859 = 7783289) B7783289
theorem B24932519 : Blo 1536465 24932519 := bstep (se 1 (by rfl) ⟨18699389, by rfl⟩ : syracuseStep 24932519 = 37398779) B37398779
theorem B1536495 : Blo 1536465 1536495 := bstep (se 1 (by rfl) ⟨1152371, by rfl⟩ : syracuseStep 1536495 = 2304743) B2304743
theorem B47994605 : Blo 1536465 47994605 := bstep (se 3 (by rfl) ⟨8998988, by rfl⟩ : syracuseStep 47994605 = 17997977) B17997977
theorem B1537791 : Blo 1536465 1537791 := bstep (se 1 (by rfl) ⟨1153343, by rfl⟩ : syracuseStep 1537791 = 2306687) B2306687
theorem B7387163 : Blo 1536465 7387163 := bstep (se 1 (by rfl) ⟨5540372, by rfl⟩ : syracuseStep 7387163 = 11080745) B11080745
theorem B9353663 : Blo 1536465 9353663 := bstep (se 1 (by rfl) ⟨7015247, by rfl⟩ : syracuseStep 9353663 = 14030495) B14030495
theorem B17504747 : Blo 1536465 17504747 := bstep (se 1 (by rfl) ⟨13128560, by rfl⟩ : syracuseStep 17504747 = 26257121) B26257121
theorem B17996519 : Blo 1536465 17996519 := bstep (se 1 (by rfl) ⟨13497389, by rfl⟩ : syracuseStep 17996519 = 26994779) B26994779
theorem B2595611 : Blo 1536465 2595611 := bstep (se 1 (by rfl) ⟨1946708, by rfl⟩ : syracuseStep 2595611 = 3893417) B3893417
theorem B16620335 : Blo 1536465 16620335 := bstep (se 1 (by rfl) ⟨12465251, by rfl⟩ : syracuseStep 16620335 = 24930503) B24930503
theorem B5840201 : Blo 1536465 5840201 := bstep (se 2 (by rfl) ⟨2190075, by rfl⟩ : syracuseStep 5840201 = 4380151) B4380151
theorem B3694331 : Blo 1536465 3694331 := bstep (se 1 (by rfl) ⟨2770748, by rfl⟩ : syracuseStep 3694331 = 5541497) B5541497
theorem B16621679 : Blo 1536465 16621679 := bstep (se 1 (by rfl) ⟨12466259, by rfl⟩ : syracuseStep 16621679 = 24932519) B24932519
theorem B3457583 : Blo 1536465 3457583 := bstep (se 1 (by rfl) ⟨2593187, by rfl⟩ : syracuseStep 3457583 = 5186375) B5186375
theorem B13140863 : Blo 1536465 13140863 := bstep (se 1 (by rfl) ⟨9855647, by rfl⟩ : syracuseStep 13140863 = 19711295) B19711295
theorem B15787345 : Blo 1536465 15787345 := bstep (se 2 (by rfl) ⟨5920254, by rfl⟩ : syracuseStep 15787345 = 11840509) B11840509
theorem B4924775 : Blo 1536465 4924775 := bstep (se 1 (by rfl) ⟨3693581, by rfl⟩ : syracuseStep 4924775 = 7387163) B7387163
theorem B6235775 : Blo 1536465 6235775 := bstep (se 1 (by rfl) ⟨4676831, by rfl⟩ : syracuseStep 6235775 = 9353663) B9353663
theorem B1730407 : Blo 1536465 1730407 := bstep (se 1 (by rfl) ⟨1297805, by rfl⟩ : syracuseStep 1730407 = 2595611) B2595611
theorem B3459239 : Blo 1536465 3459239 := bstep (se 1 (by rfl) ⟨2594429, by rfl⟩ : syracuseStep 3459239 = 5188859) B5188859
theorem B3893467 : Blo 1536465 3893467 := bstep (se 1 (by rfl) ⟨2920100, by rfl⟩ : syracuseStep 3893467 = 5840201) B5840201
theorem B33697889 : Blo 1536465 33697889 := bstep (se 2 (by rfl) ⟨12636708, by rfl⟩ : syracuseStep 33697889 = 25273417) B25273417
theorem B11669831 : Blo 1536465 11669831 := bstep (se 1 (by rfl) ⟨8752373, by rfl⟩ : syracuseStep 11669831 = 17504747) B17504747
theorem B11997679 : Blo 1536465 11997679 := bstep (se 1 (by rfl) ⟨8998259, by rfl⟩ : syracuseStep 11997679 = 17996519) B17996519
theorem B11080223 : Blo 1536465 11080223 := bstep (se 1 (by rfl) ⟨8310167, by rfl⟩ : syracuseStep 11080223 = 16620335) B16620335
theorem B1536751 : Blo 1536465 1536751 := bstep (se 1 (by rfl) ⟨1152563, by rfl⟩ : syracuseStep 1536751 = 2305127) B2305127
theorem B2462887 : Blo 1536465 2462887 := bstep (se 1 (by rfl) ⟨1847165, by rfl⟩ : syracuseStep 2462887 = 3694331) B3694331
theorem B31996403 : Blo 1536465 31996403 := bstep (se 1 (by rfl) ⟨23997302, by rfl⟩ : syracuseStep 31996403 = 47994605) B47994605
theorem B22465259 : Blo 1536465 22465259 := bstep (se 1 (by rfl) ⟨16848944, by rfl⟩ : syracuseStep 22465259 = 33697889) B33697889
theorem B2305055 : Blo 1536465 2305055 := bstep (se 1 (by rfl) ⟨1728791, by rfl⟩ : syracuseStep 2305055 = 3457583) B3457583
theorem B8760575 : Blo 1536465 8760575 := bstep (se 1 (by rfl) ⟨6570431, by rfl⟩ : syracuseStep 8760575 = 13140863) B13140863
theorem B4157183 : Blo 1536465 4157183 := bstep (se 1 (by rfl) ⟨3117887, by rfl⟩ : syracuseStep 4157183 = 6235775) B6235775
theorem B2306159 : Blo 1536465 2306159 := bstep (se 1 (by rfl) ⟨1729619, by rfl⟩ : syracuseStep 2306159 = 3459239) B3459239
theorem B21049793 : Blo 1536465 21049793 := bstep (se 2 (by rfl) ⟨7893672, by rfl⟩ : syracuseStep 21049793 = 15787345) B15787345
theorem B2307209 : Blo 1536465 2307209 := bstep (se 2 (by rfl) ⟨865203, by rfl⟩ : syracuseStep 2307209 = 1730407) B1730407
theorem B11081119 : Blo 1536465 11081119 := bstep (se 1 (by rfl) ⟨8310839, by rfl⟩ : syracuseStep 11081119 = 16621679) B16621679
theorem B7779887 : Blo 1536465 7779887 := bstep (se 1 (by rfl) ⟨5834915, by rfl⟩ : syracuseStep 7779887 = 11669831) B11669831
theorem B5191289 : Blo 1536465 5191289 := bstep (se 2 (by rfl) ⟨1946733, by rfl⟩ : syracuseStep 5191289 = 3893467) B3893467
theorem B7386815 : Blo 1536465 7386815 := bstep (se 1 (by rfl) ⟨5540111, by rfl⟩ : syracuseStep 7386815 = 11080223) B11080223
theorem B15996905 : Blo 1536465 15996905 := bstep (se 2 (by rfl) ⟨5998839, by rfl⟩ : syracuseStep 15996905 = 11997679) B11997679
theorem B3283183 : Blo 1536465 3283183 := bstep (se 1 (by rfl) ⟨2462387, by rfl⟩ : syracuseStep 3283183 = 4924775) B4924775
theorem B3283849 : Blo 1536465 3283849 := bstep (se 2 (by rfl) ⟨1231443, by rfl⟩ : syracuseStep 3283849 = 2462887) B2462887
theorem B21330935 : Blo 1536465 21330935 := bstep (se 1 (by rfl) ⟨15998201, by rfl⟩ : syracuseStep 21330935 = 31996403) B31996403
theorem B14033195 : Blo 1536465 14033195 := bstep (se 1 (by rfl) ⟨10524896, by rfl⟩ : syracuseStep 14033195 = 21049793) B21049793
theorem B5186591 : Blo 1536465 5186591 := bstep (se 1 (by rfl) ⟨3889943, by rfl⟩ : syracuseStep 5186591 = 7779887) B7779887
theorem B14976839 : Blo 1536465 14976839 := bstep (se 1 (by rfl) ⟨11232629, by rfl⟩ : syracuseStep 14976839 = 22465259) B22465259
theorem B11085821 : Blo 1536465 11085821 := bstep (se 3 (by rfl) ⟨2078591, by rfl⟩ : syracuseStep 11085821 = 4157183) B4157183
theorem B4377577 : Blo 1536465 4377577 := bstep (se 2 (by rfl) ⟨1641591, by rfl⟩ : syracuseStep 4377577 = 3283183) B3283183
theorem B3460859 : Blo 1536465 3460859 := bstep (se 1 (by rfl) ⟨2595644, by rfl⟩ : syracuseStep 3460859 = 5191289) B5191289
theorem B4378465 : Blo 1536465 4378465 := bstep (se 2 (by rfl) ⟨1641924, by rfl⟩ : syracuseStep 4378465 = 3283849) B3283849
theorem B19698173 : Blo 1536465 19698173 := bstep (se 3 (by rfl) ⟨3693407, by rfl⟩ : syracuseStep 19698173 = 7386815) B7386815
theorem B14774825 : Blo 1536465 14774825 := bstep (se 2 (by rfl) ⟨5540559, by rfl⟩ : syracuseStep 14774825 = 11081119) B11081119
theorem B1536703 : Blo 1536465 1536703 := bstep (se 1 (by rfl) ⟨1152527, by rfl⟩ : syracuseStep 1536703 = 2305055) B2305055
theorem B1537439 : Blo 1536465 1537439 := bstep (se 1 (by rfl) ⟨1153079, by rfl⟩ : syracuseStep 1537439 = 2306159) B2306159
theorem B1538139 : Blo 1536465 1538139 := bstep (se 1 (by rfl) ⟨1153604, by rfl⟩ : syracuseStep 1538139 = 2307209) B2307209
theorem B10664603 : Blo 1536465 10664603 := bstep (se 1 (by rfl) ⟨7998452, by rfl⟩ : syracuseStep 10664603 = 15996905) B15996905
theorem B14220623 : Blo 1536465 14220623 := bstep (se 1 (by rfl) ⟨10665467, by rfl⟩ : syracuseStep 14220623 = 21330935) B21330935
theorem B5840383 : Blo 1536465 5840383 := bstep (se 1 (by rfl) ⟨4380287, by rfl⟩ : syracuseStep 5840383 = 8760575) B8760575
theorem B9355463 : Blo 1536465 9355463 := bstep (se 1 (by rfl) ⟨7016597, by rfl⟩ : syracuseStep 9355463 = 14033195) B14033195
theorem B13132115 : Blo 1536465 13132115 := bstep (se 1 (by rfl) ⟨9849086, by rfl⟩ : syracuseStep 13132115 = 19698173) B19698173
theorem B3457727 : Blo 1536465 3457727 := bstep (se 1 (by rfl) ⟨2593295, by rfl⟩ : syracuseStep 3457727 = 5186591) B5186591
theorem B7390547 : Blo 1536465 7390547 := bstep (se 1 (by rfl) ⟨5542910, by rfl⟩ : syracuseStep 7390547 = 11085821) B11085821
theorem B9480415 : Blo 1536465 9480415 := bstep (se 1 (by rfl) ⟨7110311, by rfl⟩ : syracuseStep 9480415 = 14220623) B14220623
theorem B9849883 : Blo 1536465 9849883 := bstep (se 1 (by rfl) ⟨7387412, by rfl⟩ : syracuseStep 9849883 = 14774825) B14774825
theorem B5836769 : Blo 1536465 5836769 := bstep (se 2 (by rfl) ⟨2188788, by rfl⟩ : syracuseStep 5836769 = 4377577) B4377577
theorem B7787177 : Blo 1536465 7787177 := bstep (se 2 (by rfl) ⟨2920191, by rfl⟩ : syracuseStep 7787177 = 5840383) B5840383
theorem B5837953 : Blo 1536465 5837953 := bstep (se 2 (by rfl) ⟨2189232, by rfl⟩ : syracuseStep 5837953 = 4378465) B4378465
theorem B2307239 : Blo 1536465 2307239 := bstep (se 1 (by rfl) ⟨1730429, by rfl⟩ : syracuseStep 2307239 = 3460859) B3460859
theorem B9984559 : Blo 1536465 9984559 := bstep (se 1 (by rfl) ⟨7488419, by rfl⟩ : syracuseStep 9984559 = 14976839) B14976839
theorem B7109735 : Blo 1536465 7109735 := bstep (se 1 (by rfl) ⟨5332301, by rfl⟩ : syracuseStep 7109735 = 10664603) B10664603
theorem B12640553 : Blo 1536465 12640553 := bstep (se 2 (by rfl) ⟨4740207, by rfl⟩ : syracuseStep 12640553 = 9480415) B9480415
theorem B13312745 : Blo 1536465 13312745 := bstep (se 2 (by rfl) ⟨4992279, by rfl⟩ : syracuseStep 13312745 = 9984559) B9984559
theorem B13133177 : Blo 1536465 13133177 := bstep (se 2 (by rfl) ⟨4924941, by rfl⟩ : syracuseStep 13133177 = 9849883) B9849883
theorem B7783937 : Blo 1536465 7783937 := bstep (se 2 (by rfl) ⟨2918976, by rfl⟩ : syracuseStep 7783937 = 5837953) B5837953
theorem B6236975 : Blo 1536465 6236975 := bstep (se 1 (by rfl) ⟨4677731, by rfl⟩ : syracuseStep 6236975 = 9355463) B9355463
theorem B18959293 : Blo 1536465 18959293 := bstep (se 3 (by rfl) ⟨3554867, by rfl⟩ : syracuseStep 18959293 = 7109735) B7109735
theorem B2305151 : Blo 1536465 2305151 := bstep (se 1 (by rfl) ⟨1728863, by rfl⟩ : syracuseStep 2305151 = 3457727) B3457727
theorem B4927031 : Blo 1536465 4927031 := bstep (se 1 (by rfl) ⟨3695273, by rfl⟩ : syracuseStep 4927031 = 7390547) B7390547
theorem B8754743 : Blo 1536465 8754743 := bstep (se 1 (by rfl) ⟨6566057, by rfl⟩ : syracuseStep 8754743 = 13132115) B13132115
theorem B5191451 : Blo 1536465 5191451 := bstep (se 1 (by rfl) ⟨3893588, by rfl⟩ : syracuseStep 5191451 = 7787177) B7787177
theorem B1538159 : Blo 1536465 1538159 := bstep (se 1 (by rfl) ⟨1153619, by rfl⟩ : syracuseStep 1538159 = 2307239) B2307239
theorem B3891179 : Blo 1536465 3891179 := bstep (se 1 (by rfl) ⟨2918384, by rfl⟩ : syracuseStep 3891179 = 5836769) B5836769
theorem B8875163 : Blo 1536465 8875163 := bstep (se 1 (by rfl) ⟨6656372, by rfl⟩ : syracuseStep 8875163 = 13312745) B13312745
theorem B5189291 : Blo 1536465 5189291 := bstep (se 1 (by rfl) ⟨3891968, by rfl⟩ : syracuseStep 5189291 = 7783937) B7783937
theorem B5836495 : Blo 1536465 5836495 := bstep (se 1 (by rfl) ⟨4377371, by rfl⟩ : syracuseStep 5836495 = 8754743) B8754743
theorem B3460967 : Blo 1536465 3460967 := bstep (se 1 (by rfl) ⟨2595725, by rfl⟩ : syracuseStep 3460967 = 5191451) B5191451
theorem B4157983 : Blo 1536465 4157983 := bstep (se 1 (by rfl) ⟨3118487, by rfl⟩ : syracuseStep 4157983 = 6236975) B6236975
theorem B1536767 : Blo 1536465 1536767 := bstep (se 1 (by rfl) ⟨1152575, by rfl⟩ : syracuseStep 1536767 = 2305151) B2305151
theorem B2594119 : Blo 1536465 2594119 := bstep (se 1 (by rfl) ⟨1945589, by rfl⟩ : syracuseStep 2594119 = 3891179) B3891179
theorem B8427035 : Blo 1536465 8427035 := bstep (se 1 (by rfl) ⟨6320276, by rfl⟩ : syracuseStep 8427035 = 12640553) B12640553
theorem B8755451 : Blo 1536465 8755451 := bstep (se 1 (by rfl) ⟨6566588, by rfl⟩ : syracuseStep 8755451 = 13133177) B13133177
theorem B25279057 : Blo 1536465 25279057 := bstep (se 2 (by rfl) ⟨9479646, by rfl⟩ : syracuseStep 25279057 = 18959293) B18959293
theorem B3284687 : Blo 1536465 3284687 := bstep (se 1 (by rfl) ⟨2463515, by rfl⟩ : syracuseStep 3284687 = 4927031) B4927031
theorem B22472093 : Blo 1536465 22472093 := bstep (se 3 (by rfl) ⟨4213517, by rfl⟩ : syracuseStep 22472093 = 8427035) B8427035
theorem B3458825 : Blo 1536465 3458825 := bstep (se 2 (by rfl) ⟨1297059, by rfl⟩ : syracuseStep 3458825 = 2594119) B2594119
theorem B5916775 : Blo 1536465 5916775 := bstep (se 1 (by rfl) ⟨4437581, by rfl⟩ : syracuseStep 5916775 = 8875163) B8875163
theorem B3459527 : Blo 1536465 3459527 := bstep (se 1 (by rfl) ⟨2594645, by rfl⟩ : syracuseStep 3459527 = 5189291) B5189291
theorem B2189791 : Blo 1536465 2189791 := bstep (se 1 (by rfl) ⟨1642343, by rfl⟩ : syracuseStep 2189791 = 3284687) B3284687
theorem B33705409 : Blo 1536465 33705409 := bstep (se 2 (by rfl) ⟨12639528, by rfl⟩ : syracuseStep 33705409 = 25279057) B25279057
theorem B5836967 : Blo 1536465 5836967 := bstep (se 1 (by rfl) ⟨4377725, by rfl⟩ : syracuseStep 5836967 = 8755451) B8755451
theorem B2307311 : Blo 1536465 2307311 := bstep (se 1 (by rfl) ⟨1730483, by rfl⟩ : syracuseStep 2307311 = 3460967) B3460967
theorem B5543977 : Blo 1536465 5543977 := bstep (se 2 (by rfl) ⟨2078991, by rfl⟩ : syracuseStep 5543977 = 4157983) B4157983
theorem B7781993 : Blo 1536465 7781993 := bstep (se 2 (by rfl) ⟨2918247, by rfl⟩ : syracuseStep 7781993 = 5836495) B5836495
theorem B3891311 : Blo 1536465 3891311 := bstep (se 1 (by rfl) ⟨2918483, by rfl⟩ : syracuseStep 3891311 = 5836967) B5836967
theorem B7889033 : Blo 1536465 7889033 := bstep (se 2 (by rfl) ⟨2958387, by rfl⟩ : syracuseStep 7889033 = 5916775) B5916775
theorem B5187995 : Blo 1536465 5187995 := bstep (se 1 (by rfl) ⟨3890996, by rfl⟩ : syracuseStep 5187995 = 7781993) B7781993
theorem B7391969 : Blo 1536465 7391969 := bstep (se 2 (by rfl) ⟨2771988, by rfl⟩ : syracuseStep 7391969 = 5543977) B5543977
theorem B2919721 : Blo 1536465 2919721 := bstep (se 2 (by rfl) ⟨1094895, by rfl⟩ : syracuseStep 2919721 = 2189791) B2189791
theorem B2305883 : Blo 1536465 2305883 := bstep (se 1 (by rfl) ⟨1729412, by rfl⟩ : syracuseStep 2305883 = 3458825) B3458825
theorem B2306351 : Blo 1536465 2306351 := bstep (se 1 (by rfl) ⟨1729763, by rfl⟩ : syracuseStep 2306351 = 3459527) B3459527
theorem B1538207 : Blo 1536465 1538207 := bstep (se 1 (by rfl) ⟨1153655, by rfl⟩ : syracuseStep 1538207 = 2307311) B2307311
theorem B14981395 : Blo 1536465 14981395 := bstep (se 1 (by rfl) ⟨11236046, by rfl⟩ : syracuseStep 14981395 = 22472093) B22472093
theorem B44940545 : Blo 1536465 44940545 := bstep (se 2 (by rfl) ⟨16852704, by rfl⟩ : syracuseStep 44940545 = 33705409) B33705409
theorem B21037421 : Blo 1536465 21037421 := bstep (se 3 (by rfl) ⟨3944516, by rfl⟩ : syracuseStep 21037421 = 7889033) B7889033
theorem B3458663 : Blo 1536465 3458663 := bstep (se 1 (by rfl) ⟨2593997, by rfl⟩ : syracuseStep 3458663 = 5187995) B5187995
theorem B3892961 : Blo 1536465 3892961 := bstep (se 2 (by rfl) ⟨1459860, by rfl⟩ : syracuseStep 3892961 = 2919721) B2919721
theorem B29960363 : Blo 1536465 29960363 := bstep (se 1 (by rfl) ⟨22470272, by rfl⟩ : syracuseStep 29960363 = 44940545) B44940545
theorem B19975193 : Blo 1536465 19975193 := bstep (se 2 (by rfl) ⟨7490697, by rfl⟩ : syracuseStep 19975193 = 14981395) B14981395
theorem B4927979 : Blo 1536465 4927979 := bstep (se 1 (by rfl) ⟨3695984, by rfl⟩ : syracuseStep 4927979 = 7391969) B7391969
theorem B1537255 : Blo 1536465 1537255 := bstep (se 1 (by rfl) ⟨1152941, by rfl⟩ : syracuseStep 1537255 = 2305883) B2305883
theorem B2594207 : Blo 1536465 2594207 := bstep (se 1 (by rfl) ⟨1945655, by rfl⟩ : syracuseStep 2594207 = 3891311) B3891311
theorem B1537567 : Blo 1536465 1537567 := bstep (se 1 (by rfl) ⟨1153175, by rfl⟩ : syracuseStep 1537567 = 2306351) B2306351
theorem B14024947 : Blo 1536465 14024947 := bstep (se 1 (by rfl) ⟨10518710, by rfl⟩ : syracuseStep 14024947 = 21037421) B21037421
theorem B3285319 : Blo 1536465 3285319 := bstep (se 1 (by rfl) ⟨2463989, by rfl⟩ : syracuseStep 3285319 = 4927979) B4927979
theorem B1729471 : Blo 1536465 1729471 := bstep (se 1 (by rfl) ⟨1297103, by rfl⟩ : syracuseStep 1729471 = 2594207) B2594207
theorem B19973575 : Blo 1536465 19973575 := bstep (se 1 (by rfl) ⟨14980181, by rfl⟩ : syracuseStep 19973575 = 29960363) B29960363
theorem B2305775 : Blo 1536465 2305775 := bstep (se 1 (by rfl) ⟨1729331, by rfl⟩ : syracuseStep 2305775 = 3458663) B3458663
theorem B13316795 : Blo 1536465 13316795 := bstep (se 1 (by rfl) ⟨9987596, by rfl⟩ : syracuseStep 13316795 = 19975193) B19975193
theorem B2595307 : Blo 1536465 2595307 := bstep (se 1 (by rfl) ⟨1946480, by rfl⟩ : syracuseStep 2595307 = 3892961) B3892961
theorem B3460409 : Blo 1536465 3460409 := bstep (se 2 (by rfl) ⟨1297653, by rfl⟩ : syracuseStep 3460409 = 2595307) B2595307
theorem B2305961 : Blo 1536465 2305961 := bstep (se 2 (by rfl) ⟨864735, by rfl⟩ : syracuseStep 2305961 = 1729471) B1729471
theorem B1537183 : Blo 1536465 1537183 := bstep (se 1 (by rfl) ⟨1152887, by rfl⟩ : syracuseStep 1537183 = 2305775) B2305775
theorem B18699929 : Blo 1536465 18699929 := bstep (se 2 (by rfl) ⟨7012473, by rfl⟩ : syracuseStep 18699929 = 14024947) B14024947
theorem B4380425 : Blo 1536465 4380425 := bstep (se 2 (by rfl) ⟨1642659, by rfl⟩ : syracuseStep 4380425 = 3285319) B3285319
theorem B8877863 : Blo 1536465 8877863 := bstep (se 1 (by rfl) ⟨6658397, by rfl⟩ : syracuseStep 8877863 = 13316795) B13316795
theorem B26631433 : Blo 1536465 26631433 := bstep (se 2 (by rfl) ⟨9986787, by rfl⟩ : syracuseStep 26631433 = 19973575) B19973575
theorem B2920283 : Blo 1536465 2920283 := bstep (se 1 (by rfl) ⟨2190212, by rfl⟩ : syracuseStep 2920283 = 4380425) B4380425
theorem B5918575 : Blo 1536465 5918575 := bstep (se 1 (by rfl) ⟨4438931, by rfl⟩ : syracuseStep 5918575 = 8877863) B8877863
theorem B35508577 : Blo 1536465 35508577 := bstep (se 2 (by rfl) ⟨13315716, by rfl⟩ : syracuseStep 35508577 = 26631433) B26631433
theorem B2306939 : Blo 1536465 2306939 := bstep (se 1 (by rfl) ⟨1730204, by rfl⟩ : syracuseStep 2306939 = 3460409) B3460409
theorem B1537307 : Blo 1536465 1537307 := bstep (se 1 (by rfl) ⟨1152980, by rfl⟩ : syracuseStep 1537307 = 2305961) B2305961
theorem B12466619 : Blo 1536465 12466619 := bstep (se 1 (by rfl) ⟨9349964, by rfl⟩ : syracuseStep 12466619 = 18699929) B18699929
theorem B7891433 : Blo 1536465 7891433 := bstep (se 2 (by rfl) ⟨2959287, by rfl⟩ : syracuseStep 7891433 = 5918575) B5918575
theorem B47344769 : Blo 1536465 47344769 := bstep (se 2 (by rfl) ⟨17754288, by rfl⟩ : syracuseStep 47344769 = 35508577) B35508577
theorem B8311079 : Blo 1536465 8311079 := bstep (se 1 (by rfl) ⟨6233309, by rfl⟩ : syracuseStep 8311079 = 12466619) B12466619
theorem B1946855 : Blo 1536465 1946855 := bstep (se 1 (by rfl) ⟨1460141, by rfl⟩ : syracuseStep 1946855 = 2920283) B2920283
theorem B1537959 : Blo 1536465 1537959 := bstep (se 1 (by rfl) ⟨1153469, by rfl⟩ : syracuseStep 1537959 = 2306939) B2306939
theorem B5260955 : Blo 1536465 5260955 := bstep (se 1 (by rfl) ⟨3945716, by rfl⟩ : syracuseStep 5260955 = 7891433) B7891433
theorem B5540719 : Blo 1536465 5540719 := bstep (se 1 (by rfl) ⟨4155539, by rfl⟩ : syracuseStep 5540719 = 8311079) B8311079
theorem B5191613 : Blo 1536465 5191613 := bstep (se 3 (by rfl) ⟨973427, by rfl⟩ : syracuseStep 5191613 = 1946855) B1946855
theorem B31563179 : Blo 1536465 31563179 := bstep (se 1 (by rfl) ⟨23672384, by rfl⟩ : syracuseStep 31563179 = 47344769) B47344769
theorem B3461075 : Blo 1536465 3461075 := bstep (se 1 (by rfl) ⟨2595806, by rfl⟩ : syracuseStep 3461075 = 5191613) B5191613
theorem B14029213 : Blo 1536465 14029213 := bstep (se 3 (by rfl) ⟨2630477, by rfl⟩ : syracuseStep 14029213 = 5260955) B5260955
theorem B21042119 : Blo 1536465 21042119 := bstep (se 1 (by rfl) ⟨15781589, by rfl⟩ : syracuseStep 21042119 = 31563179) B31563179
theorem B7387625 : Blo 1536465 7387625 := bstep (se 2 (by rfl) ⟨2770359, by rfl⟩ : syracuseStep 7387625 = 5540719) B5540719
theorem B4925083 : Blo 1536465 4925083 := bstep (se 1 (by rfl) ⟨3693812, by rfl⟩ : syracuseStep 4925083 = 7387625) B7387625
theorem B18705617 : Blo 1536465 18705617 := bstep (se 2 (by rfl) ⟨7014606, by rfl⟩ : syracuseStep 18705617 = 14029213) B14029213
theorem B14028079 : Blo 1536465 14028079 := bstep (se 1 (by rfl) ⟨10521059, by rfl⟩ : syracuseStep 14028079 = 21042119) B21042119
theorem B2307383 : Blo 1536465 2307383 := bstep (se 1 (by rfl) ⟨1730537, by rfl⟩ : syracuseStep 2307383 = 3461075) B3461075
theorem B18704105 : Blo 1536465 18704105 := bstep (se 2 (by rfl) ⟨7014039, by rfl⟩ : syracuseStep 18704105 = 14028079) B14028079
theorem B12470411 : Blo 1536465 12470411 := bstep (se 1 (by rfl) ⟨9352808, by rfl⟩ : syracuseStep 12470411 = 18705617) B18705617
theorem B6566777 : Blo 1536465 6566777 := bstep (se 2 (by rfl) ⟨2462541, by rfl⟩ : syracuseStep 6566777 = 4925083) B4925083
theorem B1538255 : Blo 1536465 1538255 := bstep (se 1 (by rfl) ⟨1153691, by rfl⟩ : syracuseStep 1538255 = 2307383) B2307383
theorem B12469403 : Blo 1536465 12469403 := bstep (se 1 (by rfl) ⟨9352052, by rfl⟩ : syracuseStep 12469403 = 18704105) B18704105
theorem B4377851 : Blo 1536465 4377851 := bstep (se 1 (by rfl) ⟨3283388, by rfl⟩ : syracuseStep 4377851 = 6566777) B6566777
theorem B8313607 : Blo 1536465 8313607 := bstep (se 1 (by rfl) ⟨6235205, by rfl⟩ : syracuseStep 8313607 = 12470411) B12470411
theorem B33251741 : Blo 1536465 33251741 := bstep (se 3 (by rfl) ⟨6234701, by rfl⟩ : syracuseStep 33251741 = 12469403) B12469403
theorem B2918567 : Blo 1536465 2918567 := bstep (se 1 (by rfl) ⟨2188925, by rfl⟩ : syracuseStep 2918567 = 4377851) B4377851
theorem B44339237 : Blo 1536465 44339237 := bstep (se 4 (by rfl) ⟨4156803, by rfl⟩ : syracuseStep 44339237 = 8313607) B8313607
theorem B22167827 : Blo 1536465 22167827 := bstep (se 1 (by rfl) ⟨16625870, by rfl⟩ : syracuseStep 22167827 = 33251741) B33251741
theorem B29559491 : Blo 1536465 29559491 := bstep (se 1 (by rfl) ⟨22169618, by rfl⟩ : syracuseStep 29559491 = 44339237) B44339237
theorem B1945711 : Blo 1536465 1945711 := bstep (se 1 (by rfl) ⟨1459283, by rfl⟩ : syracuseStep 1945711 = 2918567) B2918567
theorem B14778551 : Blo 1536465 14778551 := bstep (se 1 (by rfl) ⟨11083913, by rfl⟩ : syracuseStep 14778551 = 22167827) B22167827
theorem B19706327 : Blo 1536465 19706327 := bstep (se 1 (by rfl) ⟨14779745, by rfl⟩ : syracuseStep 19706327 = 29559491) B29559491
theorem B2594281 : Blo 1536465 2594281 := bstep (se 2 (by rfl) ⟨972855, by rfl⟩ : syracuseStep 2594281 = 1945711) B1945711
theorem B3459041 : Blo 1536465 3459041 := bstep (se 2 (by rfl) ⟨1297140, by rfl⟩ : syracuseStep 3459041 = 2594281) B2594281
theorem B9852367 : Blo 1536465 9852367 := bstep (se 1 (by rfl) ⟨7389275, by rfl⟩ : syracuseStep 9852367 = 14778551) B14778551
theorem B13137551 : Blo 1536465 13137551 := bstep (se 1 (by rfl) ⟨9853163, by rfl⟩ : syracuseStep 13137551 = 19706327) B19706327
theorem B8758367 : Blo 1536465 8758367 := bstep (se 1 (by rfl) ⟨6568775, by rfl⟩ : syracuseStep 8758367 = 13137551) B13137551
theorem B2306027 : Blo 1536465 2306027 := bstep (se 1 (by rfl) ⟨1729520, by rfl⟩ : syracuseStep 2306027 = 3459041) B3459041
theorem B13136489 : Blo 1536465 13136489 := bstep (se 2 (by rfl) ⟨4926183, by rfl⟩ : syracuseStep 13136489 = 9852367) B9852367
theorem B8757659 : Blo 1536465 8757659 := bstep (se 1 (by rfl) ⟨6568244, by rfl⟩ : syracuseStep 8757659 = 13136489) B13136489
theorem B1537351 : Blo 1536465 1537351 := bstep (se 1 (by rfl) ⟨1153013, by rfl⟩ : syracuseStep 1537351 = 2306027) B2306027
theorem B5838911 : Blo 1536465 5838911 := bstep (se 1 (by rfl) ⟨4379183, by rfl⟩ : syracuseStep 5838911 = 8758367) B8758367
theorem B3892607 : Blo 1536465 3892607 := bstep (se 1 (by rfl) ⟨2919455, by rfl⟩ : syracuseStep 3892607 = 5838911) B5838911
theorem B5838439 : Blo 1536465 5838439 := bstep (se 1 (by rfl) ⟨4378829, by rfl⟩ : syracuseStep 5838439 = 8757659) B8757659
theorem B7784585 : Blo 1536465 7784585 := bstep (se 2 (by rfl) ⟨2919219, by rfl⟩ : syracuseStep 7784585 = 5838439) B5838439
theorem B2595071 : Blo 1536465 2595071 := bstep (se 1 (by rfl) ⟨1946303, by rfl⟩ : syracuseStep 2595071 = 3892607) B3892607
theorem B1730047 : Blo 1536465 1730047 := bstep (se 1 (by rfl) ⟨1297535, by rfl⟩ : syracuseStep 1730047 = 2595071) B2595071
theorem B5189723 : Blo 1536465 5189723 := bstep (se 1 (by rfl) ⟨3892292, by rfl⟩ : syracuseStep 5189723 = 7784585) B7784585
theorem B3459815 : Blo 1536465 3459815 := bstep (se 1 (by rfl) ⟨2594861, by rfl⟩ : syracuseStep 3459815 = 5189723) B5189723
theorem B2306729 : Blo 1536465 2306729 := bstep (se 2 (by rfl) ⟨865023, by rfl⟩ : syracuseStep 2306729 = 1730047) B1730047
theorem B2306543 : Blo 1536465 2306543 := bstep (se 1 (by rfl) ⟨1729907, by rfl⟩ : syracuseStep 2306543 = 3459815) B3459815
theorem B1537819 : Blo 1536465 1537819 := bstep (se 1 (by rfl) ⟨1153364, by rfl⟩ : syracuseStep 1537819 = 2306729) B2306729
theorem B1537695 : Blo 1536465 1537695 := bstep (se 1 (by rfl) ⟨1153271, by rfl⟩ : syracuseStep 1537695 = 2306543) B2306543

theorem C0 (j : ℕ) (h1 : 384116 ≤ j) (h2 : j ≤ 384615) : Blo 1536465 (4 * j + 3) := by
  interval_cases j
  · exact B1536467
  · exact B1536471
  · exact B1536475
  · exact B1536479
  · exact B1536483
  · exact B1536487
  · exact B1536491
  · exact B1536495
  · exact B1536499
  · exact B1536503
  · exact B1536507
  · exact B1536511
  · exact B1536515
  · exact B1536519
  · exact B1536523
  · exact B1536527
  · exact B1536531
  · exact B1536535
  · exact B1536539
  · exact B1536543
  · exact B1536547
  · exact B1536551
  · exact B1536555
  · exact B1536559
  · exact B1536563
  · exact B1536567
  · exact B1536571
  · exact B1536575
  · exact B1536579
  · exact B1536583
  · exact B1536587
  · exact B1536591
  · exact B1536595
  · exact B1536599
  · exact B1536603
  · exact B1536607
  · exact B1536611
  · exact B1536615
  · exact B1536619
  · exact B1536623
  · exact B1536627
  · exact B1536631
  · exact B1536635
  · exact B1536639
  · exact B1536643
  · exact B1536647
  · exact B1536651
  · exact B1536655
  · exact B1536659
  · exact B1536663
  · exact B1536667
  · exact B1536671
  · exact B1536675
  · exact B1536679
  · exact B1536683
  · exact B1536687
  · exact B1536691
  · exact B1536695
  · exact B1536699
  · exact B1536703
  · exact B1536707
  · exact B1536711
  · exact B1536715
  · exact B1536719
  · exact B1536723
  · exact B1536727
  · exact B1536731
  · exact B1536735
  · exact B1536739
  · exact B1536743
  · exact B1536747
  · exact B1536751
  · exact B1536755
  · exact B1536759
  · exact B1536763
  · exact B1536767
  · exact B1536771
  · exact B1536775
  · exact B1536779
  · exact B1536783
  · exact B1536787
  · exact B1536791
  · exact B1536795
  · exact B1536799
  · exact B1536803
  · exact B1536807
  · exact B1536811
  · exact B1536815
  · exact B1536819
  · exact B1536823
  · exact B1536827
  · exact B1536831
  · exact B1536835
  · exact B1536839
  · exact B1536843
  · exact B1536847
  · exact B1536851
  · exact B1536855
  · exact B1536859
  · exact B1536863
  · exact B1536867
  · exact B1536871
  · exact B1536875
  · exact B1536879
  · exact B1536883
  · exact B1536887
  · exact B1536891
  · exact B1536895
  · exact B1536899
  · exact B1536903
  · exact B1536907
  · exact B1536911
  · exact B1536915
  · exact B1536919
  · exact B1536923
  · exact B1536927
  · exact B1536931
  · exact B1536935
  · exact B1536939
  · exact B1536943
  · exact B1536947
  · exact B1536951
  · exact B1536955
  · exact B1536959
  · exact B1536963
  · exact B1536967
  · exact B1536971
  · exact B1536975
  · exact B1536979
  · exact B1536983
  · exact B1536987
  · exact B1536991
  · exact B1536995
  · exact B1536999
  · exact B1537003
  · exact B1537007
  · exact B1537011
  · exact B1537015
  · exact B1537019
  · exact B1537023
  · exact B1537027
  · exact B1537031
  · exact B1537035
  · exact B1537039
  · exact B1537043
  · exact B1537047
  · exact B1537051
  · exact B1537055
  · exact B1537059
  · exact B1537063
  · exact B1537067
  · exact B1537071
  · exact B1537075
  · exact B1537079
  · exact B1537083
  · exact B1537087
  · exact B1537091
  · exact B1537095
  · exact B1537099
  · exact B1537103
  · exact B1537107
  · exact B1537111
  · exact B1537115
  · exact B1537119
  · exact B1537123
  · exact B1537127
  · exact B1537131
  · exact B1537135
  · exact B1537139
  · exact B1537143
  · exact B1537147
  · exact B1537151
  · exact B1537155
  · exact B1537159
  · exact B1537163
  · exact B1537167
  · exact B1537171
  · exact B1537175
  · exact B1537179
  · exact B1537183
  · exact B1537187
  · exact B1537191
  · exact B1537195
  · exact B1537199
  · exact B1537203
  · exact B1537207
  · exact B1537211
  · exact B1537215
  · exact B1537219
  · exact B1537223
  · exact B1537227
  · exact B1537231
  · exact B1537235
  · exact B1537239
  · exact B1537243
  · exact B1537247
  · exact B1537251
  · exact B1537255
  · exact B1537259
  · exact B1537263
  · exact B1537267
  · exact B1537271
  · exact B1537275
  · exact B1537279
  · exact B1537283
  · exact B1537287
  · exact B1537291
  · exact B1537295
  · exact B1537299
  · exact B1537303
  · exact B1537307
  · exact B1537311
  · exact B1537315
  · exact B1537319
  · exact B1537323
  · exact B1537327
  · exact B1537331
  · exact B1537335
  · exact B1537339
  · exact B1537343
  · exact B1537347
  · exact B1537351
  · exact B1537355
  · exact B1537359
  · exact B1537363
  · exact B1537367
  · exact B1537371
  · exact B1537375
  · exact B1537379
  · exact B1537383
  · exact B1537387
  · exact B1537391
  · exact B1537395
  · exact B1537399
  · exact B1537403
  · exact B1537407
  · exact B1537411
  · exact B1537415
  · exact B1537419
  · exact B1537423
  · exact B1537427
  · exact B1537431
  · exact B1537435
  · exact B1537439
  · exact B1537443
  · exact B1537447
  · exact B1537451
  · exact B1537455
  · exact B1537459
  · exact B1537463
  · exact B1537467
  · exact B1537471
  · exact B1537475
  · exact B1537479
  · exact B1537483
  · exact B1537487
  · exact B1537491
  · exact B1537495
  · exact B1537499
  · exact B1537503
  · exact B1537507
  · exact B1537511
  · exact B1537515
  · exact B1537519
  · exact B1537523
  · exact B1537527
  · exact B1537531
  · exact B1537535
  · exact B1537539
  · exact B1537543
  · exact B1537547
  · exact B1537551
  · exact B1537555
  · exact B1537559
  · exact B1537563
  · exact B1537567
  · exact B1537571
  · exact B1537575
  · exact B1537579
  · exact B1537583
  · exact B1537587
  · exact B1537591
  · exact B1537595
  · exact B1537599
  · exact B1537603
  · exact B1537607
  · exact B1537611
  · exact B1537615
  · exact B1537619
  · exact B1537623
  · exact B1537627
  · exact B1537631
  · exact B1537635
  · exact B1537639
  · exact B1537643
  · exact B1537647
  · exact B1537651
  · exact B1537655
  · exact B1537659
  · exact B1537663
  · exact B1537667
  · exact B1537671
  · exact B1537675
  · exact B1537679
  · exact B1537683
  · exact B1537687
  · exact B1537691
  · exact B1537695
  · exact B1537699
  · exact B1537703
  · exact B1537707
  · exact B1537711
  · exact B1537715
  · exact B1537719
  · exact B1537723
  · exact B1537727
  · exact B1537731
  · exact B1537735
  · exact B1537739
  · exact B1537743
  · exact B1537747
  · exact B1537751
  · exact B1537755
  · exact B1537759
  · exact B1537763
  · exact B1537767
  · exact B1537771
  · exact B1537775
  · exact B1537779
  · exact B1537783
  · exact B1537787
  · exact B1537791
  · exact B1537795
  · exact B1537799
  · exact B1537803
  · exact B1537807
  · exact B1537811
  · exact B1537815
  · exact B1537819
  · exact B1537823
  · exact B1537827
  · exact B1537831
  · exact B1537835
  · exact B1537839
  · exact B1537843
  · exact B1537847
  · exact B1537851
  · exact B1537855
  · exact B1537859
  · exact B1537863
  · exact B1537867
  · exact B1537871
  · exact B1537875
  · exact B1537879
  · exact B1537883
  · exact B1537887
  · exact B1537891
  · exact B1537895
  · exact B1537899
  · exact B1537903
  · exact B1537907
  · exact B1537911
  · exact B1537915
  · exact B1537919
  · exact B1537923
  · exact B1537927
  · exact B1537931
  · exact B1537935
  · exact B1537939
  · exact B1537943
  · exact B1537947
  · exact B1537951
  · exact B1537955
  · exact B1537959
  · exact B1537963
  · exact B1537967
  · exact B1537971
  · exact B1537975
  · exact B1537979
  · exact B1537983
  · exact B1537987
  · exact B1537991
  · exact B1537995
  · exact B1537999
  · exact B1538003
  · exact B1538007
  · exact B1538011
  · exact B1538015
  · exact B1538019
  · exact B1538023
  · exact B1538027
  · exact B1538031
  · exact B1538035
  · exact B1538039
  · exact B1538043
  · exact B1538047
  · exact B1538051
  · exact B1538055
  · exact B1538059
  · exact B1538063
  · exact B1538067
  · exact B1538071
  · exact B1538075
  · exact B1538079
  · exact B1538083
  · exact B1538087
  · exact B1538091
  · exact B1538095
  · exact B1538099
  · exact B1538103
  · exact B1538107
  · exact B1538111
  · exact B1538115
  · exact B1538119
  · exact B1538123
  · exact B1538127
  · exact B1538131
  · exact B1538135
  · exact B1538139
  · exact B1538143
  · exact B1538147
  · exact B1538151
  · exact B1538155
  · exact B1538159
  · exact B1538163
  · exact B1538167
  · exact B1538171
  · exact B1538175
  · exact B1538179
  · exact B1538183
  · exact B1538187
  · exact B1538191
  · exact B1538195
  · exact B1538199
  · exact B1538203
  · exact B1538207
  · exact B1538211
  · exact B1538215
  · exact B1538219
  · exact B1538223
  · exact B1538227
  · exact B1538231
  · exact B1538235
  · exact B1538239
  · exact B1538243
  · exact B1538247
  · exact B1538251
  · exact B1538255
  · exact B1538259
  · exact B1538263
  · exact B1538267
  · exact B1538271
  · exact B1538275
  · exact B1538279
  · exact B1538283
  · exact B1538287
  · exact B1538291
  · exact B1538295
  · exact B1538299
  · exact B1538303
  · exact B1538307
  · exact B1538311
  · exact B1538315
  · exact B1538319
  · exact B1538323
  · exact B1538327
  · exact B1538331
  · exact B1538335
  · exact B1538339
  · exact B1538343
  · exact B1538347
  · exact B1538351
  · exact B1538355
  · exact B1538359
  · exact B1538363
  · exact B1538367
  · exact B1538371
  · exact B1538375
  · exact B1538379
  · exact B1538383
  · exact B1538387
  · exact B1538391
  · exact B1538395
  · exact B1538399
  · exact B1538403
  · exact B1538407
  · exact B1538411
  · exact B1538415
  · exact B1538419
  · exact B1538423
  · exact B1538427
  · exact B1538431
  · exact B1538435
  · exact B1538439
  · exact B1538443
  · exact B1538447
  · exact B1538451
  · exact B1538455
  · exact B1538459
  · exact B1538463

theorem solution (m : ℕ) (hlo : 1536465 ≤ m) (hhi : m ≤ 1538465) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 384116 ≤ j := by omega
    have hj2 : j ≤ 384615 := by omega
    have hb : Blo 1536465 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
