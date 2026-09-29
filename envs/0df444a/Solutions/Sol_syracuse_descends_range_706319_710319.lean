-- Prove2me | solution 1 for syracuse_descends_range_706319_710319
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:00.539603+00:00
-- url     : https://prove2.me/submissions/6401d212-27f1-44f7-bd50-0830f9d11832

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


theorem B2392469 : Blo 706319 2392469 := bbase (se 6 (by rfl) ⟨56073, by rfl⟩ : syracuseStep 2392469 = 112147) (by norm_num)
theorem B1343965 : Blo 706319 1343965 := bbase (se 3 (by rfl) ⟨251993, by rfl⟩ : syracuseStep 1343965 = 503987) (by norm_num)
theorem B3408389 : Blo 706319 3408389 := bbase (se 4 (by rfl) ⟨319536, by rfl⟩ : syracuseStep 3408389 = 639073) (by norm_num)
theorem B1704493 : Blo 706319 1704493 := bbase (se 3 (by rfl) ⟨319592, by rfl⟩ : syracuseStep 1704493 = 639185) (by norm_num)
theorem B1344109 : Blo 706319 1344109 := bbase (se 3 (by rfl) ⟨252020, by rfl⟩ : syracuseStep 1344109 = 504041) (by norm_num)
theorem B6128245 : Blo 706319 6128245 := bbase (se 5 (by rfl) ⟨287261, by rfl⟩ : syracuseStep 6128245 = 574523) (by norm_num)
theorem B3834485 : Blo 706319 3834485 := bbase (se 5 (by rfl) ⟨179741, by rfl⟩ : syracuseStep 3834485 = 359483) (by norm_num)
theorem B2687701 : Blo 706319 2687701 := bbase (se 7 (by rfl) ⟨31496, by rfl⟩ : syracuseStep 2687701 = 62993) (by norm_num)
theorem B6816469 : Blo 706319 6816469 := bbase (se 7 (by rfl) ⟨79880, by rfl⟩ : syracuseStep 6816469 = 159761) (by norm_num)
theorem B1344269 : Blo 706319 1344269 := bbase (se 3 (by rfl) ⟨252050, by rfl⟩ : syracuseStep 1344269 = 504101) (by norm_num)
theorem B754481 : Blo 706319 754481 := bbase (se 2 (by rfl) ⟨282930, by rfl⟩ : syracuseStep 754481 = 565861) (by norm_num)
theorem B2392901 : Blo 706319 2392901 := bbase (se 4 (by rfl) ⟨224334, by rfl⟩ : syracuseStep 2392901 = 448669) (by norm_num)
theorem B1344413 : Blo 706319 1344413 := bbase (se 3 (by rfl) ⟨252077, by rfl⟩ : syracuseStep 1344413 = 504155) (by norm_num)
theorem B2688005 : Blo 706319 2688005 := bbase (se 4 (by rfl) ⟨252000, by rfl⟩ : syracuseStep 2688005 = 504001) (by norm_num)
theorem B2557013 : Blo 706319 2557013 := bbase (se 8 (by rfl) ⟨14982, by rfl⟩ : syracuseStep 2557013 = 29965) (by norm_num)
theorem B853097 : Blo 706319 853097 := bbase (se 2 (by rfl) ⟨319911, by rfl⟩ : syracuseStep 853097 = 639823) (by norm_num)
theorem B1344701 : Blo 706319 1344701 := bbase (se 3 (by rfl) ⟨252131, by rfl⟩ : syracuseStep 1344701 = 504263) (by norm_num)
theorem B1705157 : Blo 706319 1705157 := bbase (se 4 (by rfl) ⟨159858, by rfl⟩ : syracuseStep 1705157 = 319717) (by norm_num)
theorem B754925 : Blo 706319 754925 := bbase (se 3 (by rfl) ⟨141548, by rfl⟩ : syracuseStep 754925 = 283097) (by norm_num)
theorem B2393333 : Blo 706319 2393333 := bbase (se 5 (by rfl) ⟨112187, by rfl⟩ : syracuseStep 2393333 = 224375) (by norm_num)
theorem B1344853 : Blo 706319 1344853 := bbase (se 12 (by rfl) ⟨492, by rfl⟩ : syracuseStep 1344853 = 985) (by norm_num)
theorem B755173 : Blo 706319 755173 := bbase (se 4 (by rfl) ⟨70797, by rfl⟩ : syracuseStep 755173 = 141595) (by norm_num)
theorem B1705445 : Blo 706319 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B1148509 : Blo 706319 1148509 := bbase (se 3 (by rfl) ⟨215345, by rfl⟩ : syracuseStep 1148509 = 430691) (by norm_num)
theorem B1345157 : Blo 706319 1345157 := bbase (se 4 (by rfl) ⟨126108, by rfl⟩ : syracuseStep 1345157 = 252217) (by norm_num)
theorem B1312405 : Blo 706319 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B2393765 : Blo 706319 2393765 := bbase (se 4 (by rfl) ⟨224415, by rfl⟩ : syracuseStep 2393765 = 448831) (by norm_num)
theorem B1214117 : Blo 706319 1214117 := bbase (se 4 (by rfl) ⟨113823, by rfl⟩ : syracuseStep 1214117 = 227647) (by norm_num)
theorem B1148645 : Blo 706319 1148645 := bbase (se 4 (by rfl) ⟨107685, by rfl⟩ : syracuseStep 1148645 = 215371) (by norm_num)
theorem B1509133 : Blo 706319 1509133 := bbase (se 3 (by rfl) ⟨282962, by rfl⟩ : syracuseStep 1509133 = 565925) (by norm_num)
theorem B1148773 : Blo 706319 1148773 := bbase (se 4 (by rfl) ⟨107697, by rfl⟩ : syracuseStep 1148773 = 215395) (by norm_num)
theorem B755605 : Blo 706319 755605 := bbase (se 6 (by rfl) ⟨17709, by rfl⟩ : syracuseStep 755605 = 35419) (by norm_num)
theorem B755677 : Blo 706319 755677 := bbase (se 3 (by rfl) ⟨141689, by rfl⟩ : syracuseStep 755677 = 283379) (by norm_num)
theorem B2394197 : Blo 706319 2394197 := bbase (se 8 (by rfl) ⟨14028, by rfl⟩ : syracuseStep 2394197 = 28057) (by norm_num)
theorem B1509509 : Blo 706319 1509509 := bbase (se 4 (by rfl) ⟨141516, by rfl⟩ : syracuseStep 1509509 = 283033) (by norm_num)
theorem B1149085 : Blo 706319 1149085 := bbase (se 3 (by rfl) ⟨215453, by rfl⟩ : syracuseStep 1149085 = 430907) (by norm_num)
theorem B756049 : Blo 706319 756049 := bbase (se 2 (by rfl) ⟨283518, by rfl⟩ : syracuseStep 756049 = 567037) (by norm_num)
theorem B1345909 : Blo 706319 1345909 := bbase (se 5 (by rfl) ⟨63089, by rfl⟩ : syracuseStep 1345909 = 126179) (by norm_num)
theorem B1346053 : Blo 706319 1346053 := bbase (se 4 (by rfl) ⟨126192, by rfl⟩ : syracuseStep 1346053 = 252385) (by norm_num)
theorem B2394629 : Blo 706319 2394629 := bbase (se 4 (by rfl) ⟨224496, by rfl⟩ : syracuseStep 2394629 = 448993) (by norm_num)
theorem B2722405 : Blo 706319 2722405 := bbase (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) (by norm_num)
theorem B3410581 : Blo 706319 3410581 := bbase (se 6 (by rfl) ⟨79935, by rfl⟩ : syracuseStep 3410581 = 159871) (by norm_num)
theorem B1346213 : Blo 706319 1346213 := bbase (se 4 (by rfl) ⟨126207, by rfl⟩ : syracuseStep 1346213 = 252415) (by norm_num)
theorem B756425 : Blo 706319 756425 := bbase (se 2 (by rfl) ⟨283659, by rfl⟩ : syracuseStep 756425 = 567319) (by norm_num)
theorem B756497 : Blo 706319 756497 := bbase (se 2 (by rfl) ⟨283686, by rfl⟩ : syracuseStep 756497 = 567373) (by norm_num)
theorem B1346357 : Blo 706319 1346357 := bbase (se 5 (by rfl) ⟨63110, by rfl⟩ : syracuseStep 1346357 = 126221) (by norm_num)
theorem B3640133 : Blo 706319 3640133 := bbase (se 4 (by rfl) ⟨341262, by rfl⟩ : syracuseStep 3640133 = 682525) (by norm_num)
theorem B2395061 : Blo 706319 2395061 := bbase (se 5 (by rfl) ⟨112268, by rfl⟩ : syracuseStep 2395061 = 224537) (by norm_num)
theorem B756685 : Blo 706319 756685 := bbase (se 3 (by rfl) ⟨141878, by rfl⟩ : syracuseStep 756685 = 283757) (by norm_num)
theorem B2690117 : Blo 706319 2690117 := bbase (se 4 (by rfl) ⟨252198, by rfl⟩ : syracuseStep 2690117 = 504397) (by norm_num)
theorem B1346645 : Blo 706319 1346645 := bbase (se 8 (by rfl) ⟨7890, by rfl⟩ : syracuseStep 1346645 = 15781) (by norm_num)
theorem B756869 : Blo 706319 756869 := bbase (se 4 (by rfl) ⟨70956, by rfl⟩ : syracuseStep 756869 = 141913) (by norm_num)
theorem B2264213 : Blo 706319 2264213 := bbase (se 6 (by rfl) ⟨53067, by rfl⟩ : syracuseStep 2264213 = 106135) (by norm_num)
theorem B1346797 : Blo 706319 1346797 := bbase (se 3 (by rfl) ⟨252524, by rfl⟩ : syracuseStep 1346797 = 505049) (by norm_num)
theorem B2690405 : Blo 706319 2690405 := bbase (se 4 (by rfl) ⟨252225, by rfl⟩ : syracuseStep 2690405 = 504451) (by norm_num)
theorem B2395493 : Blo 706319 2395493 := bbase (se 4 (by rfl) ⟨224577, by rfl⟩ : syracuseStep 2395493 = 449155) (by norm_num)
theorem B3018181 : Blo 706319 3018181 := bbase (se 4 (by rfl) ⟨282954, by rfl⟩ : syracuseStep 3018181 = 565909) (by norm_num)
theorem B3018197 : Blo 706319 3018197 := bbase (se 7 (by rfl) ⟨35369, by rfl⟩ : syracuseStep 3018197 = 70739) (by norm_num)
theorem B2559509 : Blo 706319 2559509 := bbase (se 6 (by rfl) ⟨59988, by rfl⟩ : syracuseStep 2559509 = 119977) (by norm_num)
theorem B1347101 : Blo 706319 1347101 := bbase (se 3 (by rfl) ⟨252581, by rfl⟩ : syracuseStep 1347101 = 505163) (by norm_num)
theorem B2068021 : Blo 706319 2068021 := bbase (se 5 (by rfl) ⟨96938, by rfl⟩ : syracuseStep 2068021 = 193877) (by norm_num)
theorem B5377589 : Blo 706319 5377589 := bbase (se 5 (by rfl) ⟨252074, by rfl⟩ : syracuseStep 5377589 = 504149) (by norm_num)
theorem B5738165 : Blo 706319 5738165 := bbase (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) (by norm_num)
theorem B1511149 : Blo 706319 1511149 := bbase (se 3 (by rfl) ⟨283340, by rfl⟩ : syracuseStep 1511149 = 566681) (by norm_num)
theorem B2395925 : Blo 706319 2395925 := bbase (se 6 (by rfl) ⟨56154, by rfl⟩ : syracuseStep 2395925 = 112309) (by norm_num)
theorem B757621 : Blo 706319 757621 := bbase (se 5 (by rfl) ⟨35513, by rfl⟩ : syracuseStep 757621 = 71027) (by norm_num)
theorem B757693 : Blo 706319 757693 := bbase (se 3 (by rfl) ⟨142067, by rfl⟩ : syracuseStep 757693 = 284135) (by norm_num)
theorem B1019989 : Blo 706319 1019989 := bbase (se 8 (by rfl) ⟨5976, by rfl⟩ : syracuseStep 1019989 = 11953) (by norm_num)
theorem B757873 : Blo 706319 757873 := bbase (se 2 (by rfl) ⟨284202, by rfl⟩ : syracuseStep 757873 = 568405) (by norm_num)
theorem B2396357 : Blo 706319 2396357 := bbase (se 4 (by rfl) ⟨224658, by rfl⟩ : syracuseStep 2396357 = 449317) (by norm_num)
theorem B1347853 : Blo 706319 1347853 := bbase (se 3 (by rfl) ⟨252722, by rfl⟩ : syracuseStep 1347853 = 505445) (by norm_num)
theorem B3576149 : Blo 706319 3576149 := bbase (se 10 (by rfl) ⟨5238, by rfl⟩ : syracuseStep 3576149 = 10477) (by norm_num)
theorem B1347997 : Blo 706319 1347997 := bbase (se 3 (by rfl) ⟨252749, by rfl⟩ : syracuseStep 1347997 = 505499) (by norm_num)
theorem B922097 : Blo 706319 922097 := bbase (se 2 (by rfl) ⟨345786, by rfl⟩ : syracuseStep 922097 = 691573) (by norm_num)
theorem B2691589 : Blo 706319 2691589 := bbase (se 4 (by rfl) ⟨252336, by rfl⟩ : syracuseStep 2691589 = 504673) (by norm_num)
theorem B758317 : Blo 706319 758317 := bbase (se 3 (by rfl) ⟨142184, by rfl⟩ : syracuseStep 758317 = 284369) (by norm_num)
theorem B1348157 : Blo 706319 1348157 := bbase (se 3 (by rfl) ⟨252779, by rfl⟩ : syracuseStep 1348157 = 505559) (by norm_num)
theorem B1020485 : Blo 706319 1020485 := bbase (se 4 (by rfl) ⟨95670, by rfl⟩ : syracuseStep 1020485 = 191341) (by norm_num)
theorem B1512037 : Blo 706319 1512037 := bbase (se 4 (by rfl) ⟨141753, by rfl⟩ : syracuseStep 1512037 = 283507) (by norm_num)
theorem B6820469 : Blo 706319 6820469 := bbase (se 5 (by rfl) ⟨319709, by rfl⟩ : syracuseStep 6820469 = 639419) (by norm_num)
theorem B2396789 : Blo 706319 2396789 := bbase (se 5 (by rfl) ⟨112349, by rfl⟩ : syracuseStep 2396789 = 224699) (by norm_num)
theorem B758441 : Blo 706319 758441 := bbase (se 2 (by rfl) ⟨284415, by rfl⟩ : syracuseStep 758441 = 568831) (by norm_num)
theorem B955085 : Blo 706319 955085 := bbase (se 3 (by rfl) ⟨179078, by rfl⟩ : syracuseStep 955085 = 358157) (by norm_num)
theorem B1348301 : Blo 706319 1348301 := bbase (se 3 (by rfl) ⟨252806, by rfl⟩ : syracuseStep 1348301 = 505613) (by norm_num)
theorem B2691893 : Blo 706319 2691893 := bbase (se 5 (by rfl) ⟨126182, by rfl⟩ : syracuseStep 2691893 = 252365) (by norm_num)
theorem B725969 : Blo 706319 725969 := bbase (se 2 (by rfl) ⟨272238, by rfl⟩ : syracuseStep 725969 = 544477) (by norm_num)
theorem B2397221 : Blo 706319 2397221 := bbase (se 4 (by rfl) ⟨224739, by rfl⟩ : syracuseStep 2397221 = 449479) (by norm_num)
theorem B1512533 : Blo 706319 1512533 := bbase (se 8 (by rfl) ⟨8862, by rfl⟩ : syracuseStep 1512533 = 17725) (by norm_num)
theorem B955837 : Blo 706319 955837 := bbase (se 3 (by rfl) ⟨179219, by rfl⟩ : syracuseStep 955837 = 358439) (by norm_num)
theorem B955885 : Blo 706319 955885 := bbase (se 3 (by rfl) ⟨179228, by rfl⟩ : syracuseStep 955885 = 358457) (by norm_num)
theorem B3577445 : Blo 706319 3577445 := bbase (se 4 (by rfl) ⟨335385, by rfl⟩ : syracuseStep 3577445 = 670771) (by norm_num)
theorem B3020453 : Blo 706319 3020453 := bbase (se 4 (by rfl) ⟨283167, by rfl⟩ : syracuseStep 3020453 = 566335) (by norm_num)
theorem B5117717 : Blo 706319 5117717 := bbase (se 6 (by rfl) ⟨119946, by rfl⟩ : syracuseStep 5117717 = 239893) (by norm_num)
theorem B956317 : Blo 706319 956317 := bbase (se 3 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 956317 = 358619) (by norm_num)
theorem B1513397 : Blo 706319 1513397 := bbase (se 5 (by rfl) ⟨70940, by rfl⟩ : syracuseStep 1513397 = 141881) (by norm_num)
theorem B1513541 : Blo 706319 1513541 := bbase (se 4 (by rfl) ⟨141894, by rfl⟩ : syracuseStep 1513541 = 283789) (by norm_num)
theorem B6035573 : Blo 706319 6035573 := bbase (se 5 (by rfl) ⟨282917, by rfl⟩ : syracuseStep 6035573 = 565835) (by norm_num)
theorem B2267365 : Blo 706319 2267365 := bbase (se 4 (by rfl) ⟨212565, by rfl⟩ : syracuseStep 2267365 = 425131) (by norm_num)
theorem B7281173 : Blo 706319 7281173 := bbase (se 6 (by rfl) ⟨170652, by rfl⟩ : syracuseStep 7281173 = 341305) (by norm_num)
theorem B957053 : Blo 706319 957053 := bbase (se 3 (by rfl) ⟨179447, by rfl⟩ : syracuseStep 957053 = 358895) (by norm_num)
theorem B1514285 : Blo 706319 1514285 := bbase (se 3 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 1514285 = 567857) (by norm_num)
theorem B957269 : Blo 706319 957269 := bbase (se 9 (by rfl) ⟨2804, by rfl⟩ : syracuseStep 957269 = 5609) (by norm_num)
theorem B3578741 : Blo 706319 3578741 := bbase (se 5 (by rfl) ⟨167753, by rfl⟩ : syracuseStep 3578741 = 335507) (by norm_num)
theorem B2694005 : Blo 706319 2694005 := bbase (se 5 (by rfl) ⟨126281, by rfl⟩ : syracuseStep 2694005 = 252563) (by norm_num)
theorem B2726837 : Blo 706319 2726837 := bbase (se 5 (by rfl) ⟨127820, by rfl⟩ : syracuseStep 2726837 = 255641) (by norm_num)
theorem B4529141 : Blo 706319 4529141 := bbase (se 5 (by rfl) ⟨212303, by rfl⟩ : syracuseStep 4529141 = 424607) (by norm_num)
theorem B4299925 : Blo 706319 4299925 := bbase (se 6 (by rfl) ⟨100779, by rfl⟩ : syracuseStep 4299925 = 201559) (by norm_num)
theorem B2694293 : Blo 706319 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B957853 : Blo 706319 957853 := bbase (se 3 (by rfl) ⟨179597, by rfl⟩ : syracuseStep 957853 = 359195) (by norm_num)
theorem B1515037 : Blo 706319 1515037 := bbase (se 3 (by rfl) ⟨284069, by rfl⟩ : syracuseStep 1515037 = 568139) (by norm_num)
theorem B1515181 : Blo 706319 1515181 := bbase (se 3 (by rfl) ⟨284096, by rfl⟩ : syracuseStep 1515181 = 568193) (by norm_num)
theorem B5119733 : Blo 706319 5119733 := bbase (se 5 (by rfl) ⟨239987, by rfl⟩ : syracuseStep 5119733 = 479975) (by norm_num)
theorem B794641 : Blo 706319 794641 := bbase (se 2 (by rfl) ⟨297990, by rfl⟩ : syracuseStep 794641 = 595981) (by norm_num)
theorem B1515557 : Blo 706319 1515557 := bbase (se 4 (by rfl) ⟨142083, by rfl⟩ : syracuseStep 1515557 = 284167) (by norm_num)
theorem B794677 : Blo 706319 794677 := bbase (se 5 (by rfl) ⟨37250, by rfl⟩ : syracuseStep 794677 = 74501) (by norm_num)
theorem B39297109 : Blo 706319 39297109 := bbase (se 8 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 39297109 = 460513) (by norm_num)
theorem B794713 : Blo 706319 794713 := bbase (se 2 (by rfl) ⟨298017, by rfl⟩ : syracuseStep 794713 = 596035) (by norm_num)
theorem B794749 : Blo 706319 794749 := bbase (se 3 (by rfl) ⟨149015, by rfl⟩ : syracuseStep 794749 = 298031) (by norm_num)
theorem B3580037 : Blo 706319 3580037 := bbase (se 4 (by rfl) ⟨335628, by rfl⟩ : syracuseStep 3580037 = 671257) (by norm_num)
theorem B860305 : Blo 706319 860305 := bbase (se 2 (by rfl) ⟨322614, by rfl⟩ : syracuseStep 860305 = 645229) (by norm_num)
theorem B794785 : Blo 706319 794785 := bbase (se 2 (by rfl) ⟨298044, by rfl⟩ : syracuseStep 794785 = 596089) (by norm_num)
theorem B794821 : Blo 706319 794821 := bbase (se 4 (by rfl) ⟨74514, by rfl⟩ : syracuseStep 794821 = 149029) (by norm_num)
theorem B794857 : Blo 706319 794857 := bbase (se 2 (by rfl) ⟨298071, by rfl⟩ : syracuseStep 794857 = 596143) (by norm_num)
theorem B794893 : Blo 706319 794893 := bbase (se 3 (by rfl) ⟨149042, by rfl⟩ : syracuseStep 794893 = 298085) (by norm_num)
theorem B794929 : Blo 706319 794929 := bbase (se 2 (by rfl) ⟨298098, by rfl⟩ : syracuseStep 794929 = 596197) (by norm_num)
theorem B2695477 : Blo 706319 2695477 := bbase (se 5 (by rfl) ⟨126350, by rfl⟩ : syracuseStep 2695477 = 252701) (by norm_num)
theorem B794965 : Blo 706319 794965 := bbase (se 10 (by rfl) ⟨1164, by rfl⟩ : syracuseStep 794965 = 2329) (by norm_num)
theorem B795001 : Blo 706319 795001 := bbase (se 2 (by rfl) ⟨298125, by rfl⟩ : syracuseStep 795001 = 596251) (by norm_num)
theorem B1515925 : Blo 706319 1515925 := bbase (se 6 (by rfl) ⟨35529, by rfl⟩ : syracuseStep 1515925 = 71059) (by norm_num)
theorem B795037 : Blo 706319 795037 := bbase (se 3 (by rfl) ⟨149069, by rfl⟩ : syracuseStep 795037 = 298139) (by norm_num)
theorem B795073 : Blo 706319 795073 := bbase (se 2 (by rfl) ⟨298152, by rfl⟩ : syracuseStep 795073 = 596305) (by norm_num)
theorem B795109 : Blo 706319 795109 := bbase (se 4 (by rfl) ⟨74541, by rfl⟩ : syracuseStep 795109 = 149083) (by norm_num)
theorem B795145 : Blo 706319 795145 := bbase (se 2 (by rfl) ⟨298179, by rfl⟩ : syracuseStep 795145 = 596359) (by norm_num)
theorem B795181 : Blo 706319 795181 := bbase (se 3 (by rfl) ⟨149096, by rfl⟩ : syracuseStep 795181 = 298193) (by norm_num)
theorem B795217 : Blo 706319 795217 := bbase (se 2 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 795217 = 596413) (by norm_num)
theorem B4039253 : Blo 706319 4039253 := bbase (se 8 (by rfl) ⟨23667, by rfl⟩ : syracuseStep 4039253 = 47335) (by norm_num)
theorem B2695781 : Blo 706319 2695781 := bbase (se 4 (by rfl) ⟨252729, by rfl⟩ : syracuseStep 2695781 = 505459) (by norm_num)
theorem B795253 : Blo 706319 795253 := bbase (se 5 (by rfl) ⟨37277, by rfl⟩ : syracuseStep 795253 = 74555) (by norm_num)
theorem B795289 : Blo 706319 795289 := bbase (se 2 (by rfl) ⟨298233, by rfl⟩ : syracuseStep 795289 = 596467) (by norm_num)
theorem B795325 : Blo 706319 795325 := bbase (se 3 (by rfl) ⟨149123, by rfl⟩ : syracuseStep 795325 = 298247) (by norm_num)
theorem B795361 : Blo 706319 795361 := bbase (se 2 (by rfl) ⟨298260, by rfl⟩ : syracuseStep 795361 = 596521) (by norm_num)
theorem B795397 : Blo 706319 795397 := bbase (se 4 (by rfl) ⟨74568, by rfl⟩ : syracuseStep 795397 = 149137) (by norm_num)
theorem B795433 : Blo 706319 795433 := bbase (se 2 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 795433 = 596575) (by norm_num)
theorem B795469 : Blo 706319 795469 := bbase (se 3 (by rfl) ⟨149150, by rfl⟩ : syracuseStep 795469 = 298301) (by norm_num)
theorem B795505 : Blo 706319 795505 := bbase (se 2 (by rfl) ⟨298314, by rfl⟩ : syracuseStep 795505 = 596629) (by norm_num)
theorem B795541 : Blo 706319 795541 := bbase (se 6 (by rfl) ⟨18645, by rfl⟩ : syracuseStep 795541 = 37291) (by norm_num)
theorem B3449749 : Blo 706319 3449749 := bbase (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) (by norm_num)
theorem B795577 : Blo 706319 795577 := bbase (se 2 (by rfl) ⟨298341, by rfl⟩ : syracuseStep 795577 = 596683) (by norm_num)
theorem B795613 : Blo 706319 795613 := bbase (se 3 (by rfl) ⟨149177, by rfl⟩ : syracuseStep 795613 = 298355) (by norm_num)
theorem B2270197 : Blo 706319 2270197 := bbase (se 5 (by rfl) ⟨106415, by rfl⟩ : syracuseStep 2270197 = 212831) (by norm_num)
theorem B795649 : Blo 706319 795649 := bbase (se 2 (by rfl) ⟨298368, by rfl⟩ : syracuseStep 795649 = 596737) (by norm_num)
theorem B6038549 : Blo 706319 6038549 := bbase (se 6 (by rfl) ⟨141528, by rfl⟩ : syracuseStep 6038549 = 283057) (by norm_num)
theorem B795685 : Blo 706319 795685 := bbase (se 4 (by rfl) ⟨74595, by rfl⟩ : syracuseStep 795685 = 149191) (by norm_num)
theorem B2270261 : Blo 706319 2270261 := bbase (se 5 (by rfl) ⟨106418, by rfl⟩ : syracuseStep 2270261 = 212837) (by norm_num)
theorem B894017 : Blo 706319 894017 := bbase (se 2 (by rfl) ⟨335256, by rfl⟩ : syracuseStep 894017 = 670513) (by norm_num)
theorem B795721 : Blo 706319 795721 := bbase (se 2 (by rfl) ⟨298395, by rfl⟩ : syracuseStep 795721 = 596791) (by norm_num)
theorem B795757 : Blo 706319 795757 := bbase (se 3 (by rfl) ⟨149204, by rfl⟩ : syracuseStep 795757 = 298409) (by norm_num)
theorem B894073 : Blo 706319 894073 := bbase (se 2 (by rfl) ⟨335277, by rfl⟩ : syracuseStep 894073 = 670555) (by norm_num)
theorem B795793 : Blo 706319 795793 := bbase (se 2 (by rfl) ⟨298422, by rfl⟩ : syracuseStep 795793 = 596845) (by norm_num)
theorem B795829 : Blo 706319 795829 := bbase (se 5 (by rfl) ⟨37304, by rfl⟩ : syracuseStep 795829 = 74609) (by norm_num)
theorem B9086165 : Blo 706319 9086165 := bbase (se 7 (by rfl) ⟨106478, by rfl⟩ : syracuseStep 9086165 = 212957) (by norm_num)
theorem B894169 : Blo 706319 894169 := bbase (se 2 (by rfl) ⟨335313, by rfl⟩ : syracuseStep 894169 = 670627) (by norm_num)
theorem B795865 : Blo 706319 795865 := bbase (se 2 (by rfl) ⟨298449, by rfl⟩ : syracuseStep 795865 = 596899) (by norm_num)
theorem B795901 : Blo 706319 795901 := bbase (se 3 (by rfl) ⟨149231, by rfl⟩ : syracuseStep 795901 = 298463) (by norm_num)
theorem B795937 : Blo 706319 795937 := bbase (se 2 (by rfl) ⟨298476, by rfl⟩ : syracuseStep 795937 = 596953) (by norm_num)
theorem B795973 : Blo 706319 795973 := bbase (se 4 (by rfl) ⟨74622, by rfl⟩ : syracuseStep 795973 = 149245) (by norm_num)
theorem B1910117 : Blo 706319 1910117 := bbase (se 4 (by rfl) ⟨179073, by rfl⟩ : syracuseStep 1910117 = 358147) (by norm_num)
theorem B796009 : Blo 706319 796009 := bbase (se 2 (by rfl) ⟨298503, by rfl⟩ : syracuseStep 796009 = 597007) (by norm_num)
theorem B894341 : Blo 706319 894341 := bbase (se 4 (by rfl) ⟨83844, by rfl⟩ : syracuseStep 894341 = 167689) (by norm_num)
theorem B796045 : Blo 706319 796045 := bbase (se 3 (by rfl) ⟨149258, by rfl⟩ : syracuseStep 796045 = 298517) (by norm_num)
theorem B3581333 : Blo 706319 3581333 := bbase (se 6 (by rfl) ⟨83937, by rfl⟩ : syracuseStep 3581333 = 167875) (by norm_num)
theorem B796081 : Blo 706319 796081 := bbase (se 2 (by rfl) ⟨298530, by rfl⟩ : syracuseStep 796081 = 597061) (by norm_num)
theorem B894397 : Blo 706319 894397 := bbase (se 3 (by rfl) ⟨167699, by rfl⟩ : syracuseStep 894397 = 335399) (by norm_num)
theorem B1910213 : Blo 706319 1910213 := bbase (se 4 (by rfl) ⟨179082, by rfl⟩ : syracuseStep 1910213 = 358165) (by norm_num)
theorem B796117 : Blo 706319 796117 := bbase (se 7 (by rfl) ⟨9329, by rfl⟩ : syracuseStep 796117 = 18659) (by norm_num)
theorem B796153 : Blo 706319 796153 := bbase (se 2 (by rfl) ⟨298557, by rfl⟩ : syracuseStep 796153 = 597115) (by norm_num)
theorem B894493 : Blo 706319 894493 := bbase (se 3 (by rfl) ⟨167717, by rfl⟩ : syracuseStep 894493 = 335435) (by norm_num)
theorem B796189 : Blo 706319 796189 := bbase (se 3 (by rfl) ⟨149285, by rfl⟩ : syracuseStep 796189 = 298571) (by norm_num)
theorem B796225 : Blo 706319 796225 := bbase (se 2 (by rfl) ⟨298584, by rfl⟩ : syracuseStep 796225 = 597169) (by norm_num)
theorem B796261 : Blo 706319 796261 := bbase (se 4 (by rfl) ⟨74649, by rfl⟩ : syracuseStep 796261 = 149299) (by norm_num)
theorem B3024485 : Blo 706319 3024485 := bbase (se 4 (by rfl) ⟨283545, by rfl⟩ : syracuseStep 3024485 = 567091) (by norm_num)
theorem B796297 : Blo 706319 796297 := bbase (se 2 (by rfl) ⟨298611, by rfl⟩ : syracuseStep 796297 = 597223) (by norm_num)
theorem B796333 : Blo 706319 796333 := bbase (se 3 (by rfl) ⟨149312, by rfl⟩ : syracuseStep 796333 = 298625) (by norm_num)
theorem B894665 : Blo 706319 894665 := bbase (se 2 (by rfl) ⟨335499, by rfl⟩ : syracuseStep 894665 = 670999) (by norm_num)
theorem B796369 : Blo 706319 796369 := bbase (se 2 (by rfl) ⟨298638, by rfl⟩ : syracuseStep 796369 = 597277) (by norm_num)
theorem B796405 : Blo 706319 796405 := bbase (se 5 (by rfl) ⟨37331, by rfl⟩ : syracuseStep 796405 = 74663) (by norm_num)
theorem B894721 : Blo 706319 894721 := bbase (se 2 (by rfl) ⟨335520, by rfl⟩ : syracuseStep 894721 = 671041) (by norm_num)
theorem B796441 : Blo 706319 796441 := bbase (se 2 (by rfl) ⟨298665, by rfl⟩ : syracuseStep 796441 = 597331) (by norm_num)
theorem B796477 : Blo 706319 796477 := bbase (se 3 (by rfl) ⟨149339, by rfl⟩ : syracuseStep 796477 = 298679) (by norm_num)
theorem B894817 : Blo 706319 894817 := bbase (se 2 (by rfl) ⟨335556, by rfl⟩ : syracuseStep 894817 = 671113) (by norm_num)
theorem B796513 : Blo 706319 796513 := bbase (se 2 (by rfl) ⟨298692, by rfl⟩ : syracuseStep 796513 = 597385) (by norm_num)
theorem B796549 : Blo 706319 796549 := bbase (se 4 (by rfl) ⟨74676, by rfl⟩ : syracuseStep 796549 = 149353) (by norm_num)
theorem B796585 : Blo 706319 796585 := bbase (se 2 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 796585 = 597439) (by norm_num)
theorem B796621 : Blo 706319 796621 := bbase (se 3 (by rfl) ⟨149366, by rfl⟩ : syracuseStep 796621 = 298733) (by norm_num)
theorem B862165 : Blo 706319 862165 := bbase (se 7 (by rfl) ⟨10103, by rfl⟩ : syracuseStep 862165 = 20207) (by norm_num)
theorem B796657 : Blo 706319 796657 := bbase (se 2 (by rfl) ⟨298746, by rfl⟩ : syracuseStep 796657 = 597493) (by norm_num)
theorem B894989 : Blo 706319 894989 := bbase (se 3 (by rfl) ⟨167810, by rfl⟩ : syracuseStep 894989 = 335621) (by norm_num)
theorem B796693 : Blo 706319 796693 := bbase (se 6 (by rfl) ⟨18672, by rfl⟩ : syracuseStep 796693 = 37345) (by norm_num)
theorem B796729 : Blo 706319 796729 := bbase (se 2 (by rfl) ⟨298773, by rfl⟩ : syracuseStep 796729 = 597547) (by norm_num)
theorem B895045 : Blo 706319 895045 := bbase (se 4 (by rfl) ⟨83910, by rfl⟩ : syracuseStep 895045 = 167821) (by norm_num)
theorem B796765 : Blo 706319 796765 := bbase (se 3 (by rfl) ⟨149393, by rfl⟩ : syracuseStep 796765 = 298787) (by norm_num)
theorem B796801 : Blo 706319 796801 := bbase (se 2 (by rfl) ⟨298800, by rfl⟩ : syracuseStep 796801 = 597601) (by norm_num)
theorem B895141 : Blo 706319 895141 := bbase (se 4 (by rfl) ⟨83919, by rfl⟩ : syracuseStep 895141 = 167839) (by norm_num)
theorem B796837 : Blo 706319 796837 := bbase (se 4 (by rfl) ⟨74703, by rfl⟩ : syracuseStep 796837 = 149407) (by norm_num)
theorem B796873 : Blo 706319 796873 := bbase (se 2 (by rfl) ⟨298827, by rfl⟩ : syracuseStep 796873 = 597655) (by norm_num)
theorem B796909 : Blo 706319 796909 := bbase (se 3 (by rfl) ⟨149420, by rfl⟩ : syracuseStep 796909 = 298841) (by norm_num)
theorem B796945 : Blo 706319 796945 := bbase (se 2 (by rfl) ⟨298854, by rfl⟩ : syracuseStep 796945 = 597709) (by norm_num)
theorem B796981 : Blo 706319 796981 := bbase (se 5 (by rfl) ⟨37358, by rfl⟩ : syracuseStep 796981 = 74717) (by norm_num)
theorem B895313 : Blo 706319 895313 := bbase (se 2 (by rfl) ⟨335742, by rfl⟩ : syracuseStep 895313 = 671485) (by norm_num)
theorem B797017 : Blo 706319 797017 := bbase (se 2 (by rfl) ⟨298881, by rfl⟩ : syracuseStep 797017 = 597763) (by norm_num)
theorem B1845605 : Blo 706319 1845605 := bbase (se 4 (by rfl) ⟨173025, by rfl⟩ : syracuseStep 1845605 = 346051) (by norm_num)
theorem B797053 : Blo 706319 797053 := bbase (se 3 (by rfl) ⟨149447, by rfl⟩ : syracuseStep 797053 = 298895) (by norm_num)
theorem B895369 : Blo 706319 895369 := bbase (se 2 (by rfl) ⟨335763, by rfl⟩ : syracuseStep 895369 = 671527) (by norm_num)
theorem B797089 : Blo 706319 797089 := bbase (se 2 (by rfl) ⟨298908, by rfl⟩ : syracuseStep 797089 = 597817) (by norm_num)
theorem B797125 : Blo 706319 797125 := bbase (se 4 (by rfl) ⟨74730, by rfl⟩ : syracuseStep 797125 = 149461) (by norm_num)
theorem B895465 : Blo 706319 895465 := bbase (se 2 (by rfl) ⟨335799, by rfl⟩ : syracuseStep 895465 = 671599) (by norm_num)
theorem B797161 : Blo 706319 797161 := bbase (se 2 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 797161 = 597871) (by norm_num)
theorem B797197 : Blo 706319 797197 := bbase (se 3 (by rfl) ⟨149474, by rfl⟩ : syracuseStep 797197 = 298949) (by norm_num)
theorem B797233 : Blo 706319 797233 := bbase (se 2 (by rfl) ⟨298962, by rfl⟩ : syracuseStep 797233 = 597925) (by norm_num)
theorem B797269 : Blo 706319 797269 := bbase (se 8 (by rfl) ⟨4671, by rfl⟩ : syracuseStep 797269 = 9343) (by norm_num)
theorem B797305 : Blo 706319 797305 := bbase (se 2 (by rfl) ⟨298989, by rfl⟩ : syracuseStep 797305 = 597979) (by norm_num)
theorem B895637 : Blo 706319 895637 := bbase (se 6 (by rfl) ⟨20991, by rfl⟩ : syracuseStep 895637 = 41983) (by norm_num)
theorem B1059485 : Blo 706319 1059485 := bbase (se 3 (by rfl) ⟨198653, by rfl⟩ : syracuseStep 1059485 = 397307) (by norm_num)
theorem B797341 : Blo 706319 797341 := bbase (se 3 (by rfl) ⟨149501, by rfl⟩ : syracuseStep 797341 = 299003) (by norm_num)
theorem B3582629 : Blo 706319 3582629 := bbase (se 4 (by rfl) ⟨335871, by rfl⟩ : syracuseStep 3582629 = 671743) (by norm_num)
theorem B1059509 : Blo 706319 1059509 := bbase (se 5 (by rfl) ⟨49664, by rfl⟩ : syracuseStep 1059509 = 99329) (by norm_num)
theorem B797377 : Blo 706319 797377 := bbase (se 2 (by rfl) ⟨299016, by rfl⟩ : syracuseStep 797377 = 598033) (by norm_num)
theorem B1059533 : Blo 706319 1059533 := bbase (se 3 (by rfl) ⟨198662, by rfl⟩ : syracuseStep 1059533 = 397325) (by norm_num)
theorem B895693 : Blo 706319 895693 := bbase (se 3 (by rfl) ⟨167942, by rfl⟩ : syracuseStep 895693 = 335885) (by norm_num)
theorem B1059557 : Blo 706319 1059557 := bbase (se 4 (by rfl) ⟨99333, by rfl⟩ : syracuseStep 1059557 = 198667) (by norm_num)
theorem B797413 : Blo 706319 797413 := bbase (se 4 (by rfl) ⟨74757, by rfl⟩ : syracuseStep 797413 = 149515) (by norm_num)
theorem B1059581 : Blo 706319 1059581 := bbase (se 3 (by rfl) ⟨198671, by rfl⟩ : syracuseStep 1059581 = 397343) (by norm_num)
theorem B797449 : Blo 706319 797449 := bbase (se 2 (by rfl) ⟨299043, by rfl⟩ : syracuseStep 797449 = 598087) (by norm_num)
theorem B1059605 : Blo 706319 1059605 := bbase (se 6 (by rfl) ⟨24834, by rfl⟩ : syracuseStep 1059605 = 49669) (by norm_num)
theorem B1059629 : Blo 706319 1059629 := bbase (se 3 (by rfl) ⟨198680, by rfl⟩ : syracuseStep 1059629 = 397361) (by norm_num)
theorem B895789 : Blo 706319 895789 := bbase (se 3 (by rfl) ⟨167960, by rfl⟩ : syracuseStep 895789 = 335921) (by norm_num)
theorem B797485 : Blo 706319 797485 := bbase (se 3 (by rfl) ⟨149528, by rfl⟩ : syracuseStep 797485 = 299057) (by norm_num)
theorem B2304821 : Blo 706319 2304821 := bbase (se 5 (by rfl) ⟨108038, by rfl⟩ : syracuseStep 2304821 = 216077) (by norm_num)
theorem B1059653 : Blo 706319 1059653 := bbase (se 4 (by rfl) ⟨99342, by rfl⟩ : syracuseStep 1059653 = 198685) (by norm_num)
theorem B797521 : Blo 706319 797521 := bbase (se 2 (by rfl) ⟨299070, by rfl⟩ : syracuseStep 797521 = 598141) (by norm_num)
theorem B1059677 : Blo 706319 1059677 := bbase (se 3 (by rfl) ⟨198689, by rfl⟩ : syracuseStep 1059677 = 397379) (by norm_num)
theorem B1059701 : Blo 706319 1059701 := bbase (se 5 (by rfl) ⟨49673, by rfl⟩ : syracuseStep 1059701 = 99347) (by norm_num)
theorem B797557 : Blo 706319 797557 := bbase (se 5 (by rfl) ⟨37385, by rfl⟩ : syracuseStep 797557 = 74771) (by norm_num)
theorem B1059725 : Blo 706319 1059725 := bbase (se 3 (by rfl) ⟨198698, by rfl⟩ : syracuseStep 1059725 = 397397) (by norm_num)
theorem B797593 : Blo 706319 797593 := bbase (se 2 (by rfl) ⟨299097, by rfl⟩ : syracuseStep 797593 = 598195) (by norm_num)
theorem B1092509 : Blo 706319 1092509 := bbase (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) (by norm_num)
theorem B1059749 : Blo 706319 1059749 := bbase (se 4 (by rfl) ⟨99351, by rfl⟩ : syracuseStep 1059749 = 198703) (by norm_num)
theorem B1059773 : Blo 706319 1059773 := bbase (se 3 (by rfl) ⟨198707, by rfl⟩ : syracuseStep 1059773 = 397415) (by norm_num)
theorem B797629 : Blo 706319 797629 := bbase (se 3 (by rfl) ⟨149555, by rfl⟩ : syracuseStep 797629 = 299111) (by norm_num)
theorem B1059797 : Blo 706319 1059797 := bbase (se 7 (by rfl) ⟨12419, by rfl⟩ : syracuseStep 1059797 = 24839) (by norm_num)
theorem B895961 : Blo 706319 895961 := bbase (se 2 (by rfl) ⟨335985, by rfl⟩ : syracuseStep 895961 = 671971) (by norm_num)
theorem B797665 : Blo 706319 797665 := bbase (se 2 (by rfl) ⟨299124, by rfl⟩ : syracuseStep 797665 = 598249) (by norm_num)
theorem B1059821 : Blo 706319 1059821 := bbase (se 3 (by rfl) ⟨198716, by rfl⟩ : syracuseStep 1059821 = 397433) (by norm_num)
theorem B1059845 : Blo 706319 1059845 := bbase (se 4 (by rfl) ⟨99360, by rfl⟩ : syracuseStep 1059845 = 198721) (by norm_num)
theorem B797701 : Blo 706319 797701 := bbase (se 4 (by rfl) ⟨74784, by rfl⟩ : syracuseStep 797701 = 149569) (by norm_num)
theorem B896017 : Blo 706319 896017 := bbase (se 2 (by rfl) ⟨336006, by rfl⟩ : syracuseStep 896017 = 672013) (by norm_num)
theorem B1059869 : Blo 706319 1059869 := bbase (se 3 (by rfl) ⟨198725, by rfl⟩ : syracuseStep 1059869 = 397451) (by norm_num)
theorem B797737 : Blo 706319 797737 := bbase (se 2 (by rfl) ⟨299151, by rfl⟩ : syracuseStep 797737 = 598303) (by norm_num)
theorem B1059893 : Blo 706319 1059893 := bbase (se 5 (by rfl) ⟨49682, by rfl⟩ : syracuseStep 1059893 = 99365) (by norm_num)
theorem B1059917 : Blo 706319 1059917 := bbase (se 3 (by rfl) ⟨198734, by rfl⟩ : syracuseStep 1059917 = 397469) (by norm_num)
theorem B797773 : Blo 706319 797773 := bbase (se 3 (by rfl) ⟨149582, by rfl⟩ : syracuseStep 797773 = 299165) (by norm_num)
theorem B1059941 : Blo 706319 1059941 := bbase (se 4 (by rfl) ⟨99369, by rfl⟩ : syracuseStep 1059941 = 198739) (by norm_num)
theorem B896113 : Blo 706319 896113 := bbase (se 2 (by rfl) ⟨336042, by rfl⟩ : syracuseStep 896113 = 672085) (by norm_num)
theorem B797809 : Blo 706319 797809 := bbase (se 2 (by rfl) ⟨299178, by rfl⟩ : syracuseStep 797809 = 598357) (by norm_num)
theorem B1059965 : Blo 706319 1059965 := bbase (se 3 (by rfl) ⟨198743, by rfl⟩ : syracuseStep 1059965 = 397487) (by norm_num)
theorem B1059989 : Blo 706319 1059989 := bbase (se 6 (by rfl) ⟨24843, by rfl⟩ : syracuseStep 1059989 = 49687) (by norm_num)
theorem B5385365 : Blo 706319 5385365 := bbase (se 6 (by rfl) ⟨126219, by rfl⟩ : syracuseStep 5385365 = 252439) (by norm_num)
theorem B797845 : Blo 706319 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B1060013 : Blo 706319 1060013 := bbase (se 3 (by rfl) ⟨198752, by rfl⟩ : syracuseStep 1060013 = 397505) (by norm_num)
theorem B797881 : Blo 706319 797881 := bbase (se 2 (by rfl) ⟨299205, by rfl⟩ : syracuseStep 797881 = 598411) (by norm_num)
theorem B1060037 : Blo 706319 1060037 := bbase (se 4 (by rfl) ⟨99378, by rfl⟩ : syracuseStep 1060037 = 198757) (by norm_num)
theorem B1060061 : Blo 706319 1060061 := bbase (se 3 (by rfl) ⟨198761, by rfl⟩ : syracuseStep 1060061 = 397523) (by norm_num)
theorem B797917 : Blo 706319 797917 := bbase (se 3 (by rfl) ⟨149609, by rfl⟩ : syracuseStep 797917 = 299219) (by norm_num)
theorem B1060085 : Blo 706319 1060085 := bbase (se 5 (by rfl) ⟨49691, by rfl⟩ : syracuseStep 1060085 = 99383) (by norm_num)
theorem B797953 : Blo 706319 797953 := bbase (se 2 (by rfl) ⟨299232, by rfl⟩ : syracuseStep 797953 = 598465) (by norm_num)
theorem B1060109 : Blo 706319 1060109 := bbase (se 3 (by rfl) ⟨198770, by rfl⟩ : syracuseStep 1060109 = 397541) (by norm_num)
theorem B896285 : Blo 706319 896285 := bbase (se 3 (by rfl) ⟨168053, by rfl⟩ : syracuseStep 896285 = 336107) (by norm_num)
theorem B797989 : Blo 706319 797989 := bbase (se 4 (by rfl) ⟨74811, by rfl⟩ : syracuseStep 797989 = 149623) (by norm_num)
theorem B1060133 : Blo 706319 1060133 := bbase (se 4 (by rfl) ⟨99387, by rfl⟩ : syracuseStep 1060133 = 198775) (by norm_num)
theorem B1060157 : Blo 706319 1060157 := bbase (se 3 (by rfl) ⟨198779, by rfl⟩ : syracuseStep 1060157 = 397559) (by norm_num)
theorem B798025 : Blo 706319 798025 := bbase (se 2 (by rfl) ⟨299259, by rfl⟩ : syracuseStep 798025 = 598519) (by norm_num)
theorem B1060181 : Blo 706319 1060181 := bbase (se 11 (by rfl) ⟨776, by rfl⟩ : syracuseStep 1060181 = 1553) (by norm_num)
theorem B896341 : Blo 706319 896341 := bbase (se 11 (by rfl) ⟨656, by rfl⟩ : syracuseStep 896341 = 1313) (by norm_num)
theorem B3026261 : Blo 706319 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B1060205 : Blo 706319 1060205 := bbase (se 3 (by rfl) ⟨198788, by rfl⟩ : syracuseStep 1060205 = 397577) (by norm_num)
theorem B798061 : Blo 706319 798061 := bbase (se 3 (by rfl) ⟨149636, by rfl⟩ : syracuseStep 798061 = 299273) (by norm_num)
theorem B1060229 : Blo 706319 1060229 := bbase (se 4 (by rfl) ⟨99396, by rfl⟩ : syracuseStep 1060229 = 198793) (by norm_num)
theorem B798097 : Blo 706319 798097 := bbase (se 2 (by rfl) ⟨299286, by rfl⟩ : syracuseStep 798097 = 598573) (by norm_num)
theorem B1060253 : Blo 706319 1060253 := bbase (se 3 (by rfl) ⟨198797, by rfl⟩ : syracuseStep 1060253 = 397595) (by norm_num)
theorem B1060277 : Blo 706319 1060277 := bbase (se 5 (by rfl) ⟨49700, by rfl⟩ : syracuseStep 1060277 = 99401) (by norm_num)
theorem B896437 : Blo 706319 896437 := bbase (se 5 (by rfl) ⟨42020, by rfl⟩ : syracuseStep 896437 = 84041) (by norm_num)
theorem B798133 : Blo 706319 798133 := bbase (se 5 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 798133 = 74825) (by norm_num)
theorem B1060301 : Blo 706319 1060301 := bbase (se 3 (by rfl) ⟨198806, by rfl⟩ : syracuseStep 1060301 = 397613) (by norm_num)
theorem B798169 : Blo 706319 798169 := bbase (se 2 (by rfl) ⟨299313, by rfl⟩ : syracuseStep 798169 = 598627) (by norm_num)
theorem B1060325 : Blo 706319 1060325 := bbase (se 4 (by rfl) ⟨99405, by rfl⟩ : syracuseStep 1060325 = 198811) (by norm_num)
theorem B1060349 : Blo 706319 1060349 := bbase (se 3 (by rfl) ⟨198815, by rfl⟩ : syracuseStep 1060349 = 397631) (by norm_num)
theorem B798205 : Blo 706319 798205 := bbase (se 3 (by rfl) ⟨149663, by rfl⟩ : syracuseStep 798205 = 299327) (by norm_num)
theorem B1060373 : Blo 706319 1060373 := bbase (se 6 (by rfl) ⟨24852, by rfl⟩ : syracuseStep 1060373 = 49705) (by norm_num)
theorem B798241 : Blo 706319 798241 := bbase (se 2 (by rfl) ⟨299340, by rfl⟩ : syracuseStep 798241 = 598681) (by norm_num)
theorem B3059237 : Blo 706319 3059237 := bbase (se 4 (by rfl) ⟨286803, by rfl⟩ : syracuseStep 3059237 = 573607) (by norm_num)
theorem B1060397 : Blo 706319 1060397 := bbase (se 3 (by rfl) ⟨198824, by rfl⟩ : syracuseStep 1060397 = 397649) (by norm_num)
theorem B1060421 : Blo 706319 1060421 := bbase (se 4 (by rfl) ⟨99414, by rfl⟩ : syracuseStep 1060421 = 198829) (by norm_num)
theorem B798277 : Blo 706319 798277 := bbase (se 4 (by rfl) ⟨74838, by rfl⟩ : syracuseStep 798277 = 149677) (by norm_num)
theorem B1060445 : Blo 706319 1060445 := bbase (se 3 (by rfl) ⟨198833, by rfl⟩ : syracuseStep 1060445 = 397667) (by norm_num)
theorem B896609 : Blo 706319 896609 := bbase (se 2 (by rfl) ⟨336228, by rfl⟩ : syracuseStep 896609 = 672457) (by norm_num)
theorem B798313 : Blo 706319 798313 := bbase (se 2 (by rfl) ⟨299367, by rfl⟩ : syracuseStep 798313 = 598735) (by norm_num)
theorem B1060469 : Blo 706319 1060469 := bbase (se 5 (by rfl) ⟨49709, by rfl⟩ : syracuseStep 1060469 = 99419) (by norm_num)
theorem B1060493 : Blo 706319 1060493 := bbase (se 3 (by rfl) ⟨198842, by rfl⟩ : syracuseStep 1060493 = 397685) (by norm_num)
theorem B798349 : Blo 706319 798349 := bbase (se 3 (by rfl) ⟨149690, by rfl⟩ : syracuseStep 798349 = 299381) (by norm_num)
theorem B896665 : Blo 706319 896665 := bbase (se 2 (by rfl) ⟨336249, by rfl⟩ : syracuseStep 896665 = 672499) (by norm_num)
theorem B1060517 : Blo 706319 1060517 := bbase (se 4 (by rfl) ⟨99423, by rfl⟩ : syracuseStep 1060517 = 198847) (by norm_num)
theorem B798385 : Blo 706319 798385 := bbase (se 2 (by rfl) ⟨299394, by rfl⟩ : syracuseStep 798385 = 598789) (by norm_num)
theorem B1060541 : Blo 706319 1060541 := bbase (se 3 (by rfl) ⟨198851, by rfl⟩ : syracuseStep 1060541 = 397703) (by norm_num)
theorem B1060565 : Blo 706319 1060565 := bbase (se 7 (by rfl) ⟨12428, by rfl⟩ : syracuseStep 1060565 = 24857) (by norm_num)
theorem B798421 : Blo 706319 798421 := bbase (se 7 (by rfl) ⟨9356, by rfl⟩ : syracuseStep 798421 = 18713) (by norm_num)
theorem B1093349 : Blo 706319 1093349 := bbase (se 4 (by rfl) ⟨102501, by rfl⟩ : syracuseStep 1093349 = 205003) (by norm_num)
theorem B1060589 : Blo 706319 1060589 := bbase (se 3 (by rfl) ⟨198860, by rfl⟩ : syracuseStep 1060589 = 397721) (by norm_num)
theorem B896761 : Blo 706319 896761 := bbase (se 2 (by rfl) ⟨336285, by rfl⟩ : syracuseStep 896761 = 672571) (by norm_num)
theorem B798457 : Blo 706319 798457 := bbase (se 2 (by rfl) ⟨299421, by rfl⟩ : syracuseStep 798457 = 598843) (by norm_num)
theorem B1060613 : Blo 706319 1060613 := bbase (se 4 (by rfl) ⟨99432, by rfl⟩ : syracuseStep 1060613 = 198865) (by norm_num)
theorem B1060637 : Blo 706319 1060637 := bbase (se 3 (by rfl) ⟨198869, by rfl⟩ : syracuseStep 1060637 = 397739) (by norm_num)
theorem B798493 : Blo 706319 798493 := bbase (se 3 (by rfl) ⟨149717, by rfl⟩ : syracuseStep 798493 = 299435) (by norm_num)
theorem B1060661 : Blo 706319 1060661 := bbase (se 5 (by rfl) ⟨49718, by rfl⟩ : syracuseStep 1060661 = 99437) (by norm_num)
theorem B1945397 : Blo 706319 1945397 := bbase (se 5 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 1945397 = 182381) (by norm_num)
theorem B798529 : Blo 706319 798529 := bbase (se 2 (by rfl) ⟨299448, by rfl⟩ : syracuseStep 798529 = 598897) (by norm_num)
theorem B1060685 : Blo 706319 1060685 := bbase (se 3 (by rfl) ⟨198878, by rfl⟩ : syracuseStep 1060685 = 397757) (by norm_num)
theorem B1060709 : Blo 706319 1060709 := bbase (se 4 (by rfl) ⟨99441, by rfl⟩ : syracuseStep 1060709 = 198883) (by norm_num)
theorem B798565 : Blo 706319 798565 := bbase (se 4 (by rfl) ⟨74865, by rfl⟩ : syracuseStep 798565 = 149731) (by norm_num)
theorem B1060733 : Blo 706319 1060733 := bbase (se 3 (by rfl) ⟨198887, by rfl⟩ : syracuseStep 1060733 = 397775) (by norm_num)
theorem B798601 : Blo 706319 798601 := bbase (se 2 (by rfl) ⟨299475, by rfl⟩ : syracuseStep 798601 = 598951) (by norm_num)
theorem B1060757 : Blo 706319 1060757 := bbase (se 6 (by rfl) ⟨24861, by rfl⟩ : syracuseStep 1060757 = 49723) (by norm_num)
theorem B896933 : Blo 706319 896933 := bbase (se 4 (by rfl) ⟨84087, by rfl⟩ : syracuseStep 896933 = 168175) (by norm_num)
theorem B1060781 : Blo 706319 1060781 := bbase (se 3 (by rfl) ⟨198896, by rfl⟩ : syracuseStep 1060781 = 397793) (by norm_num)
theorem B798637 : Blo 706319 798637 := bbase (se 3 (by rfl) ⟨149744, by rfl⟩ : syracuseStep 798637 = 299489) (by norm_num)
theorem B3583925 : Blo 706319 3583925 := bbase (se 5 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 3583925 = 335993) (by norm_num)
theorem B1060805 : Blo 706319 1060805 := bbase (se 4 (by rfl) ⟨99450, by rfl⟩ : syracuseStep 1060805 = 198901) (by norm_num)
theorem B798673 : Blo 706319 798673 := bbase (se 2 (by rfl) ⟨299502, by rfl⟩ : syracuseStep 798673 = 599005) (by norm_num)
theorem B1060829 : Blo 706319 1060829 := bbase (se 3 (by rfl) ⟨198905, by rfl⟩ : syracuseStep 1060829 = 397811) (by norm_num)
theorem B896989 : Blo 706319 896989 := bbase (se 3 (by rfl) ⟨168185, by rfl⟩ : syracuseStep 896989 = 336371) (by norm_num)
theorem B1060853 : Blo 706319 1060853 := bbase (se 5 (by rfl) ⟨49727, by rfl⟩ : syracuseStep 1060853 = 99455) (by norm_num)
theorem B798709 : Blo 706319 798709 := bbase (se 5 (by rfl) ⟨37439, by rfl⟩ : syracuseStep 798709 = 74879) (by norm_num)
theorem B1814525 : Blo 706319 1814525 := bbase (se 3 (by rfl) ⟨340223, by rfl⟩ : syracuseStep 1814525 = 680447) (by norm_num)
theorem B2273285 : Blo 706319 2273285 := bbase (se 4 (by rfl) ⟨213120, by rfl⟩ : syracuseStep 2273285 = 426241) (by norm_num)
theorem B1060877 : Blo 706319 1060877 := bbase (se 3 (by rfl) ⟨198914, by rfl⟩ : syracuseStep 1060877 = 397829) (by norm_num)
theorem B798745 : Blo 706319 798745 := bbase (se 2 (by rfl) ⟨299529, by rfl⟩ : syracuseStep 798745 = 599059) (by norm_num)
theorem B1060901 : Blo 706319 1060901 := bbase (se 4 (by rfl) ⟨99459, by rfl⟩ : syracuseStep 1060901 = 198919) (by norm_num)
theorem B1191989 : Blo 706319 1191989 := bbase (se 5 (by rfl) ⟨55874, by rfl⟩ : syracuseStep 1191989 = 111749) (by norm_num)
theorem B1060925 : Blo 706319 1060925 := bbase (se 3 (by rfl) ⟨198923, by rfl⟩ : syracuseStep 1060925 = 397847) (by norm_num)
theorem B897085 : Blo 706319 897085 := bbase (se 3 (by rfl) ⟨168203, by rfl⟩ : syracuseStep 897085 = 336407) (by norm_num)
theorem B798781 : Blo 706319 798781 := bbase (se 3 (by rfl) ⟨149771, by rfl⟩ : syracuseStep 798781 = 299543) (by norm_num)
theorem B1060949 : Blo 706319 1060949 := bbase (se 8 (by rfl) ⟨6216, by rfl⟩ : syracuseStep 1060949 = 12433) (by norm_num)
theorem B798817 : Blo 706319 798817 := bbase (se 2 (by rfl) ⟨299556, by rfl⟩ : syracuseStep 798817 = 599113) (by norm_num)
theorem B1060973 : Blo 706319 1060973 := bbase (se 3 (by rfl) ⟨198932, by rfl⟩ : syracuseStep 1060973 = 397865) (by norm_num)
theorem B1060997 : Blo 706319 1060997 := bbase (se 4 (by rfl) ⟨99468, by rfl⟩ : syracuseStep 1060997 = 198937) (by norm_num)
theorem B798853 : Blo 706319 798853 := bbase (se 4 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 798853 = 149785) (by norm_num)
theorem B1061021 : Blo 706319 1061021 := bbase (se 3 (by rfl) ⟨198941, by rfl⟩ : syracuseStep 1061021 = 397883) (by norm_num)
theorem B798889 : Blo 706319 798889 := bbase (se 2 (by rfl) ⟨299583, by rfl⟩ : syracuseStep 798889 = 599167) (by norm_num)
theorem B1192117 : Blo 706319 1192117 := bbase (se 5 (by rfl) ⟨55880, by rfl⟩ : syracuseStep 1192117 = 111761) (by norm_num)
theorem B1061045 : Blo 706319 1061045 := bbase (se 5 (by rfl) ⟨49736, by rfl⟩ : syracuseStep 1061045 = 99473) (by norm_num)
theorem B1061069 : Blo 706319 1061069 := bbase (se 3 (by rfl) ⟨198950, by rfl⟩ : syracuseStep 1061069 = 397901) (by norm_num)
theorem B798925 : Blo 706319 798925 := bbase (se 3 (by rfl) ⟨149798, by rfl⟩ : syracuseStep 798925 = 299597) (by norm_num)
theorem B1061093 : Blo 706319 1061093 := bbase (se 4 (by rfl) ⟨99477, by rfl⟩ : syracuseStep 1061093 = 198955) (by norm_num)
theorem B897257 : Blo 706319 897257 := bbase (se 2 (by rfl) ⟨336471, by rfl⟩ : syracuseStep 897257 = 672943) (by norm_num)
theorem B798961 : Blo 706319 798961 := bbase (se 2 (by rfl) ⟨299610, by rfl⟩ : syracuseStep 798961 = 599221) (by norm_num)
theorem B1618165 : Blo 706319 1618165 := bbase (se 5 (by rfl) ⟨75851, by rfl⟩ : syracuseStep 1618165 = 151703) (by norm_num)
theorem B1061117 : Blo 706319 1061117 := bbase (se 3 (by rfl) ⟨198959, by rfl⟩ : syracuseStep 1061117 = 397919) (by norm_num)
theorem B1192205 : Blo 706319 1192205 := bbase (se 3 (by rfl) ⟨223538, by rfl⟩ : syracuseStep 1192205 = 447077) (by norm_num)
theorem B1061141 : Blo 706319 1061141 := bbase (se 6 (by rfl) ⟨24870, by rfl⟩ : syracuseStep 1061141 = 49741) (by norm_num)
theorem B798997 : Blo 706319 798997 := bbase (se 6 (by rfl) ⟨18726, by rfl⟩ : syracuseStep 798997 = 37453) (by norm_num)
theorem B897313 : Blo 706319 897313 := bbase (se 2 (by rfl) ⟨336492, by rfl⟩ : syracuseStep 897313 = 672985) (by norm_num)
theorem B1061165 : Blo 706319 1061165 := bbase (se 3 (by rfl) ⟨198968, by rfl⟩ : syracuseStep 1061165 = 397937) (by norm_num)
theorem B3027253 : Blo 706319 3027253 := bbase (se 5 (by rfl) ⟨141902, by rfl⟩ : syracuseStep 3027253 = 283805) (by norm_num)
theorem B799033 : Blo 706319 799033 := bbase (se 2 (by rfl) ⟨299637, by rfl⟩ : syracuseStep 799033 = 599275) (by norm_num)
theorem B1061189 : Blo 706319 1061189 := bbase (se 4 (by rfl) ⟨99486, by rfl⟩ : syracuseStep 1061189 = 198973) (by norm_num)
theorem B1061213 : Blo 706319 1061213 := bbase (se 3 (by rfl) ⟨198977, by rfl⟩ : syracuseStep 1061213 = 397955) (by norm_num)
theorem B799069 : Blo 706319 799069 := bbase (se 3 (by rfl) ⟨149825, by rfl⟩ : syracuseStep 799069 = 299651) (by norm_num)
theorem B2011493 : Blo 706319 2011493 := bbase (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) (by norm_num)
theorem B1061237 : Blo 706319 1061237 := bbase (se 5 (by rfl) ⟨49745, by rfl⟩ : syracuseStep 1061237 = 99491) (by norm_num)
theorem B897409 : Blo 706319 897409 := bbase (se 2 (by rfl) ⟨336528, by rfl⟩ : syracuseStep 897409 = 673057) (by norm_num)
theorem B799105 : Blo 706319 799105 := bbase (se 2 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 799105 = 599329) (by norm_num)
theorem B1192333 : Blo 706319 1192333 := bbase (se 3 (by rfl) ⟨223562, by rfl⟩ : syracuseStep 1192333 = 447125) (by norm_num)
theorem B1061261 : Blo 706319 1061261 := bbase (se 3 (by rfl) ⟨198986, by rfl⟩ : syracuseStep 1061261 = 397973) (by norm_num)
theorem B1061285 : Blo 706319 1061285 := bbase (se 4 (by rfl) ⟨99495, by rfl⟩ : syracuseStep 1061285 = 198991) (by norm_num)
theorem B1061309 : Blo 706319 1061309 := bbase (se 3 (by rfl) ⟨198995, by rfl⟩ : syracuseStep 1061309 = 397991) (by norm_num)
theorem B1061333 : Blo 706319 1061333 := bbase (se 7 (by rfl) ⟨12437, by rfl⟩ : syracuseStep 1061333 = 24875) (by norm_num)
theorem B1192421 : Blo 706319 1192421 := bbase (se 4 (by rfl) ⟨111789, by rfl⟩ : syracuseStep 1192421 = 223579) (by norm_num)
theorem B1061357 : Blo 706319 1061357 := bbase (se 3 (by rfl) ⟨199004, by rfl⟩ : syracuseStep 1061357 = 398009) (by norm_num)
theorem B1061381 : Blo 706319 1061381 := bbase (se 4 (by rfl) ⟨99504, by rfl⟩ : syracuseStep 1061381 = 199009) (by norm_num)
theorem B1061405 : Blo 706319 1061405 := bbase (se 3 (by rfl) ⟨199013, by rfl⟩ : syracuseStep 1061405 = 398027) (by norm_num)
theorem B897581 : Blo 706319 897581 := bbase (se 3 (by rfl) ⟨168296, by rfl⟩ : syracuseStep 897581 = 336593) (by norm_num)
theorem B1061429 : Blo 706319 1061429 := bbase (se 5 (by rfl) ⟨49754, by rfl⟩ : syracuseStep 1061429 = 99509) (by norm_num)
theorem B1061453 : Blo 706319 1061453 := bbase (se 3 (by rfl) ⟨199022, by rfl⟩ : syracuseStep 1061453 = 398045) (by norm_num)
theorem B1192549 : Blo 706319 1192549 := bbase (se 4 (by rfl) ⟨111801, by rfl⟩ : syracuseStep 1192549 = 223603) (by norm_num)
theorem B1061477 : Blo 706319 1061477 := bbase (se 4 (by rfl) ⟨99513, by rfl⟩ : syracuseStep 1061477 = 199027) (by norm_num)
theorem B897637 : Blo 706319 897637 := bbase (se 4 (by rfl) ⟨84153, by rfl⟩ : syracuseStep 897637 = 168307) (by norm_num)
theorem B1061501 : Blo 706319 1061501 := bbase (se 3 (by rfl) ⟨199031, by rfl⟩ : syracuseStep 1061501 = 398063) (by norm_num)
theorem B1061525 : Blo 706319 1061525 := bbase (se 6 (by rfl) ⟨24879, by rfl⟩ : syracuseStep 1061525 = 49759) (by norm_num)
theorem B1061549 : Blo 706319 1061549 := bbase (se 3 (by rfl) ⟨199040, by rfl⟩ : syracuseStep 1061549 = 398081) (by norm_num)
theorem B1192637 : Blo 706319 1192637 := bbase (se 3 (by rfl) ⟨223619, by rfl⟩ : syracuseStep 1192637 = 447239) (by norm_num)
theorem B1094333 : Blo 706319 1094333 := bbase (se 3 (by rfl) ⟨205187, by rfl⟩ : syracuseStep 1094333 = 410375) (by norm_num)
theorem B1061573 : Blo 706319 1061573 := bbase (se 4 (by rfl) ⟨99522, by rfl⟩ : syracuseStep 1061573 = 199045) (by norm_num)
theorem B897733 : Blo 706319 897733 := bbase (se 4 (by rfl) ⟨84162, by rfl⟩ : syracuseStep 897733 = 168325) (by norm_num)
theorem B1061597 : Blo 706319 1061597 := bbase (se 3 (by rfl) ⟨199049, by rfl⟩ : syracuseStep 1061597 = 398099) (by norm_num)
theorem B1061621 : Blo 706319 1061621 := bbase (se 5 (by rfl) ⟨49763, by rfl⟩ : syracuseStep 1061621 = 99527) (by norm_num)
theorem B1061645 : Blo 706319 1061645 := bbase (se 3 (by rfl) ⟨199058, by rfl⟩ : syracuseStep 1061645 = 398117) (by norm_num)
theorem B1061669 : Blo 706319 1061669 := bbase (se 4 (by rfl) ⟨99531, by rfl⟩ : syracuseStep 1061669 = 199063) (by norm_num)
theorem B1192765 : Blo 706319 1192765 := bbase (se 3 (by rfl) ⟨223643, by rfl⟩ : syracuseStep 1192765 = 447287) (by norm_num)
theorem B1061693 : Blo 706319 1061693 := bbase (se 3 (by rfl) ⟨199067, by rfl⟩ : syracuseStep 1061693 = 398135) (by norm_num)
theorem B3683141 : Blo 706319 3683141 := bbase (se 4 (by rfl) ⟨345294, by rfl⟩ : syracuseStep 3683141 = 690589) (by norm_num)
theorem B1061717 : Blo 706319 1061717 := bbase (se 9 (by rfl) ⟨3110, by rfl⟩ : syracuseStep 1061717 = 6221) (by norm_num)
theorem B1061741 : Blo 706319 1061741 := bbase (se 3 (by rfl) ⟨199076, by rfl⟩ : syracuseStep 1061741 = 398153) (by norm_num)
theorem B897905 : Blo 706319 897905 := bbase (se 2 (by rfl) ⟨336714, by rfl⟩ : syracuseStep 897905 = 673429) (by norm_num)
theorem B5747573 : Blo 706319 5747573 := bbase (se 5 (by rfl) ⟨269417, by rfl⟩ : syracuseStep 5747573 = 538835) (by norm_num)
theorem B1061765 : Blo 706319 1061765 := bbase (se 4 (by rfl) ⟨99540, by rfl⟩ : syracuseStep 1061765 = 199081) (by norm_num)
theorem B1192853 : Blo 706319 1192853 := bbase (se 6 (by rfl) ⟨27957, by rfl⟩ : syracuseStep 1192853 = 55915) (by norm_num)
theorem B1061789 : Blo 706319 1061789 := bbase (se 3 (by rfl) ⟨199085, by rfl⟩ : syracuseStep 1061789 = 398171) (by norm_num)
theorem B897961 : Blo 706319 897961 := bbase (se 2 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 897961 = 673471) (by norm_num)
theorem B1061813 : Blo 706319 1061813 := bbase (se 5 (by rfl) ⟨49772, by rfl⟩ : syracuseStep 1061813 = 99545) (by norm_num)
theorem B1061837 : Blo 706319 1061837 := bbase (se 3 (by rfl) ⟨199094, by rfl⟩ : syracuseStep 1061837 = 398189) (by norm_num)
theorem B1061861 : Blo 706319 1061861 := bbase (se 4 (by rfl) ⟨99549, by rfl⟩ : syracuseStep 1061861 = 199099) (by norm_num)
theorem B1061885 : Blo 706319 1061885 := bbase (se 3 (by rfl) ⟨199103, by rfl⟩ : syracuseStep 1061885 = 398207) (by norm_num)
theorem B898057 : Blo 706319 898057 := bbase (se 2 (by rfl) ⟨336771, by rfl⟩ : syracuseStep 898057 = 673543) (by norm_num)
theorem B1192981 : Blo 706319 1192981 := bbase (se 6 (by rfl) ⟨27960, by rfl⟩ : syracuseStep 1192981 = 55921) (by norm_num)
theorem B1061909 : Blo 706319 1061909 := bbase (se 6 (by rfl) ⟨24888, by rfl⟩ : syracuseStep 1061909 = 49777) (by norm_num)
theorem B1061933 : Blo 706319 1061933 := bbase (se 3 (by rfl) ⟨199112, by rfl⟩ : syracuseStep 1061933 = 398225) (by norm_num)
theorem B1061957 : Blo 706319 1061957 := bbase (se 4 (by rfl) ⟨99558, by rfl⟩ : syracuseStep 1061957 = 199117) (by norm_num)
theorem B1061981 : Blo 706319 1061981 := bbase (se 3 (by rfl) ⟨199121, by rfl⟩ : syracuseStep 1061981 = 398243) (by norm_num)
theorem B1193069 : Blo 706319 1193069 := bbase (se 3 (by rfl) ⟨223700, by rfl⟩ : syracuseStep 1193069 = 447401) (by norm_num)
theorem B1062005 : Blo 706319 1062005 := bbase (se 5 (by rfl) ⟨49781, by rfl⟩ : syracuseStep 1062005 = 99563) (by norm_num)
theorem B1062029 : Blo 706319 1062029 := bbase (se 3 (by rfl) ⟨199130, by rfl⟩ : syracuseStep 1062029 = 398261) (by norm_num)
theorem B1062053 : Blo 706319 1062053 := bbase (se 4 (by rfl) ⟨99567, by rfl⟩ : syracuseStep 1062053 = 199135) (by norm_num)
theorem B898229 : Blo 706319 898229 := bbase (se 5 (by rfl) ⟨42104, by rfl⟩ : syracuseStep 898229 = 84209) (by norm_num)
theorem B1062077 : Blo 706319 1062077 := bbase (se 3 (by rfl) ⟨199139, by rfl⟩ : syracuseStep 1062077 = 398279) (by norm_num)
theorem B3585221 : Blo 706319 3585221 := bbase (se 4 (by rfl) ⟨336114, by rfl⟩ : syracuseStep 3585221 = 672229) (by norm_num)
theorem B1062101 : Blo 706319 1062101 := bbase (se 7 (by rfl) ⟨12446, by rfl⟩ : syracuseStep 1062101 = 24893) (by norm_num)
theorem B1193197 : Blo 706319 1193197 := bbase (se 3 (by rfl) ⟨223724, by rfl⟩ : syracuseStep 1193197 = 447449) (by norm_num)
theorem B1062125 : Blo 706319 1062125 := bbase (se 3 (by rfl) ⟨199148, by rfl⟩ : syracuseStep 1062125 = 398297) (by norm_num)
theorem B898285 : Blo 706319 898285 := bbase (se 3 (by rfl) ⟨168428, by rfl⟩ : syracuseStep 898285 = 336857) (by norm_num)
theorem B1062149 : Blo 706319 1062149 := bbase (se 4 (by rfl) ⟨99576, by rfl⟩ : syracuseStep 1062149 = 199153) (by norm_num)
theorem B1062173 : Blo 706319 1062173 := bbase (se 3 (by rfl) ⟨199157, by rfl⟩ : syracuseStep 1062173 = 398315) (by norm_num)
theorem B1914149 : Blo 706319 1914149 := bbase (se 4 (by rfl) ⟨179451, by rfl⟩ : syracuseStep 1914149 = 358903) (by norm_num)
theorem B1062197 : Blo 706319 1062197 := bbase (se 5 (by rfl) ⟨49790, by rfl⟩ : syracuseStep 1062197 = 99581) (by norm_num)
theorem B2012485 : Blo 706319 2012485 := bbase (se 4 (by rfl) ⟨188670, by rfl⟩ : syracuseStep 2012485 = 377341) (by norm_num)
theorem B1193285 : Blo 706319 1193285 := bbase (se 4 (by rfl) ⟨111870, by rfl⟩ : syracuseStep 1193285 = 223741) (by norm_num)
theorem B1062221 : Blo 706319 1062221 := bbase (se 3 (by rfl) ⟨199166, by rfl⟩ : syracuseStep 1062221 = 398333) (by norm_num)
theorem B898381 : Blo 706319 898381 := bbase (se 3 (by rfl) ⟨168446, by rfl⟩ : syracuseStep 898381 = 336893) (by norm_num)
theorem B1062245 : Blo 706319 1062245 := bbase (se 4 (by rfl) ⟨99585, by rfl⟩ : syracuseStep 1062245 = 199171) (by norm_num)
theorem B1062269 : Blo 706319 1062269 := bbase (se 3 (by rfl) ⟨199175, by rfl⟩ : syracuseStep 1062269 = 398351) (by norm_num)
theorem B1062293 : Blo 706319 1062293 := bbase (se 6 (by rfl) ⟨24897, by rfl⟩ : syracuseStep 1062293 = 49795) (by norm_num)
theorem B1062317 : Blo 706319 1062317 := bbase (se 3 (by rfl) ⟨199184, by rfl⟩ : syracuseStep 1062317 = 398369) (by norm_num)
theorem B1193413 : Blo 706319 1193413 := bbase (se 4 (by rfl) ⟨111882, by rfl⟩ : syracuseStep 1193413 = 223765) (by norm_num)
theorem B1062341 : Blo 706319 1062341 := bbase (se 4 (by rfl) ⟨99594, by rfl⟩ : syracuseStep 1062341 = 199189) (by norm_num)
theorem B1062365 : Blo 706319 1062365 := bbase (se 3 (by rfl) ⟨199193, by rfl⟩ : syracuseStep 1062365 = 398387) (by norm_num)
theorem B1062389 : Blo 706319 1062389 := bbase (se 5 (by rfl) ⟨49799, by rfl⟩ : syracuseStep 1062389 = 99599) (by norm_num)
theorem B767477 : Blo 706319 767477 := bbase (se 5 (by rfl) ⟨35975, by rfl⟩ : syracuseStep 767477 = 71951) (by norm_num)
theorem B898553 : Blo 706319 898553 := bbase (se 2 (by rfl) ⟨336957, by rfl⟩ : syracuseStep 898553 = 673915) (by norm_num)
theorem B1062413 : Blo 706319 1062413 := bbase (se 3 (by rfl) ⟨199202, by rfl⟩ : syracuseStep 1062413 = 398405) (by norm_num)
theorem B1193501 : Blo 706319 1193501 := bbase (se 3 (by rfl) ⟨223781, by rfl⟩ : syracuseStep 1193501 = 447563) (by norm_num)
theorem B1062437 : Blo 706319 1062437 := bbase (se 4 (by rfl) ⟨99603, by rfl⟩ : syracuseStep 1062437 = 199207) (by norm_num)
theorem B898609 : Blo 706319 898609 := bbase (se 2 (by rfl) ⟨336978, by rfl⟩ : syracuseStep 898609 = 673957) (by norm_num)
theorem B1062461 : Blo 706319 1062461 := bbase (se 3 (by rfl) ⟨199211, by rfl⟩ : syracuseStep 1062461 = 398423) (by norm_num)
theorem B1062485 : Blo 706319 1062485 := bbase (se 8 (by rfl) ⟨6225, by rfl⟩ : syracuseStep 1062485 = 12451) (by norm_num)
theorem B1062509 : Blo 706319 1062509 := bbase (se 3 (by rfl) ⟨199220, by rfl⟩ : syracuseStep 1062509 = 398441) (by norm_num)
theorem B1062533 : Blo 706319 1062533 := bbase (se 4 (by rfl) ⟨99612, by rfl⟩ : syracuseStep 1062533 = 199225) (by norm_num)
theorem B898705 : Blo 706319 898705 := bbase (se 2 (by rfl) ⟨337014, by rfl⟩ : syracuseStep 898705 = 674029) (by norm_num)
theorem B1193629 : Blo 706319 1193629 := bbase (se 3 (by rfl) ⟨223805, by rfl⟩ : syracuseStep 1193629 = 447611) (by norm_num)
theorem B1062557 : Blo 706319 1062557 := bbase (se 3 (by rfl) ⟨199229, by rfl⟩ : syracuseStep 1062557 = 398459) (by norm_num)
theorem B1062581 : Blo 706319 1062581 := bbase (se 5 (by rfl) ⟨49808, by rfl⟩ : syracuseStep 1062581 = 99617) (by norm_num)
theorem B1062605 : Blo 706319 1062605 := bbase (se 3 (by rfl) ⟨199238, by rfl⟩ : syracuseStep 1062605 = 398477) (by norm_num)
theorem B1062629 : Blo 706319 1062629 := bbase (se 4 (by rfl) ⟨99621, by rfl⟩ : syracuseStep 1062629 = 199243) (by norm_num)
theorem B1193717 : Blo 706319 1193717 := bbase (se 5 (by rfl) ⟨55955, by rfl⟩ : syracuseStep 1193717 = 111911) (by norm_num)
theorem B1062653 : Blo 706319 1062653 := bbase (se 3 (by rfl) ⟨199247, by rfl⟩ : syracuseStep 1062653 = 398495) (by norm_num)
theorem B1062677 : Blo 706319 1062677 := bbase (se 6 (by rfl) ⟨24906, by rfl⟩ : syracuseStep 1062677 = 49813) (by norm_num)
theorem B1062701 : Blo 706319 1062701 := bbase (se 3 (by rfl) ⟨199256, by rfl⟩ : syracuseStep 1062701 = 398513) (by norm_num)
theorem B898877 : Blo 706319 898877 := bbase (se 3 (by rfl) ⟨168539, by rfl⟩ : syracuseStep 898877 = 337079) (by norm_num)
theorem B1062725 : Blo 706319 1062725 := bbase (se 4 (by rfl) ⟨99630, by rfl⟩ : syracuseStep 1062725 = 199261) (by norm_num)
theorem B1062749 : Blo 706319 1062749 := bbase (se 3 (by rfl) ⟨199265, by rfl⟩ : syracuseStep 1062749 = 398531) (by norm_num)
theorem B1193845 : Blo 706319 1193845 := bbase (se 5 (by rfl) ⟨55961, by rfl⟩ : syracuseStep 1193845 = 111923) (by norm_num)
theorem B1062773 : Blo 706319 1062773 := bbase (se 5 (by rfl) ⟨49817, by rfl⟩ : syracuseStep 1062773 = 99635) (by norm_num)
theorem B898933 : Blo 706319 898933 := bbase (se 5 (by rfl) ⟨42137, by rfl⟩ : syracuseStep 898933 = 84275) (by norm_num)
theorem B1062797 : Blo 706319 1062797 := bbase (se 3 (by rfl) ⟨199274, by rfl⟩ : syracuseStep 1062797 = 398549) (by norm_num)
theorem B2865061 : Blo 706319 2865061 := bbase (se 4 (by rfl) ⟨268599, by rfl⟩ : syracuseStep 2865061 = 537199) (by norm_num)
theorem B1062821 : Blo 706319 1062821 := bbase (se 4 (by rfl) ⟨99639, by rfl⟩ : syracuseStep 1062821 = 199279) (by norm_num)
theorem B1062845 : Blo 706319 1062845 := bbase (se 3 (by rfl) ⟨199283, by rfl⟩ : syracuseStep 1062845 = 398567) (by norm_num)
theorem B1193933 : Blo 706319 1193933 := bbase (se 3 (by rfl) ⟨223862, by rfl⟩ : syracuseStep 1193933 = 447725) (by norm_num)
theorem B1062869 : Blo 706319 1062869 := bbase (se 7 (by rfl) ⟨12455, by rfl⟩ : syracuseStep 1062869 = 24911) (by norm_num)
theorem B1062893 : Blo 706319 1062893 := bbase (se 3 (by rfl) ⟨199292, by rfl⟩ : syracuseStep 1062893 = 398585) (by norm_num)
theorem B1062917 : Blo 706319 1062917 := bbase (se 4 (by rfl) ⟨99648, by rfl⟩ : syracuseStep 1062917 = 199297) (by norm_num)
theorem B1619989 : Blo 706319 1619989 := bbase (se 6 (by rfl) ⟨37968, by rfl⟩ : syracuseStep 1619989 = 75937) (by norm_num)
theorem B1062941 : Blo 706319 1062941 := bbase (se 3 (by rfl) ⟨199301, by rfl⟩ : syracuseStep 1062941 = 398603) (by norm_num)
theorem B1062965 : Blo 706319 1062965 := bbase (se 5 (by rfl) ⟨49826, by rfl⟩ : syracuseStep 1062965 = 99653) (by norm_num)
theorem B1194061 : Blo 706319 1194061 := bbase (se 3 (by rfl) ⟨223886, by rfl⟩ : syracuseStep 1194061 = 447773) (by norm_num)
theorem B1062989 : Blo 706319 1062989 := bbase (se 3 (by rfl) ⟨199310, by rfl⟩ : syracuseStep 1062989 = 398621) (by norm_num)
theorem B1063013 : Blo 706319 1063013 := bbase (se 4 (by rfl) ⟨99657, by rfl⟩ : syracuseStep 1063013 = 199315) (by norm_num)
theorem B2046053 : Blo 706319 2046053 := bbase (se 4 (by rfl) ⟨191817, by rfl⟩ : syracuseStep 2046053 = 383635) (by norm_num)
theorem B1063037 : Blo 706319 1063037 := bbase (se 3 (by rfl) ⟨199319, by rfl⟩ : syracuseStep 1063037 = 398639) (by norm_num)
theorem B1063061 : Blo 706319 1063061 := bbase (se 6 (by rfl) ⟨24915, by rfl⟩ : syracuseStep 1063061 = 49831) (by norm_num)
theorem B1194149 : Blo 706319 1194149 := bbase (se 4 (by rfl) ⟨111951, by rfl⟩ : syracuseStep 1194149 = 223903) (by norm_num)
theorem B1063085 : Blo 706319 1063085 := bbase (se 3 (by rfl) ⟨199328, by rfl⟩ : syracuseStep 1063085 = 398657) (by norm_num)
theorem B1063109 : Blo 706319 1063109 := bbase (se 4 (by rfl) ⟨99666, by rfl⟩ : syracuseStep 1063109 = 199333) (by norm_num)
theorem B1063133 : Blo 706319 1063133 := bbase (se 3 (by rfl) ⟨199337, by rfl⟩ : syracuseStep 1063133 = 398675) (by norm_num)
theorem B1063157 : Blo 706319 1063157 := bbase (se 5 (by rfl) ⟨49835, by rfl⟩ : syracuseStep 1063157 = 99671) (by norm_num)
theorem B1063181 : Blo 706319 1063181 := bbase (se 3 (by rfl) ⟨199346, by rfl⟩ : syracuseStep 1063181 = 398693) (by norm_num)
theorem B1194277 : Blo 706319 1194277 := bbase (se 4 (by rfl) ⟨111963, by rfl⟩ : syracuseStep 1194277 = 223927) (by norm_num)
theorem B1063205 : Blo 706319 1063205 := bbase (se 4 (by rfl) ⟨99675, by rfl⟩ : syracuseStep 1063205 = 199351) (by norm_num)
theorem B1063229 : Blo 706319 1063229 := bbase (se 3 (by rfl) ⟨199355, by rfl⟩ : syracuseStep 1063229 = 398711) (by norm_num)
theorem B1063253 : Blo 706319 1063253 := bbase (se 10 (by rfl) ⟨1557, by rfl⟩ : syracuseStep 1063253 = 3115) (by norm_num)
theorem B1063277 : Blo 706319 1063277 := bbase (se 3 (by rfl) ⟨199364, by rfl⟩ : syracuseStep 1063277 = 398729) (by norm_num)
theorem B1227125 : Blo 706319 1227125 := bbase (se 5 (by rfl) ⟨57521, by rfl⟩ : syracuseStep 1227125 = 115043) (by norm_num)
theorem B1194365 : Blo 706319 1194365 := bbase (se 3 (by rfl) ⟨223943, by rfl⟩ : syracuseStep 1194365 = 447887) (by norm_num)
theorem B1063301 : Blo 706319 1063301 := bbase (se 4 (by rfl) ⟨99684, by rfl⟩ : syracuseStep 1063301 = 199369) (by norm_num)
theorem B2013589 : Blo 706319 2013589 := bbase (se 6 (by rfl) ⟨47193, by rfl⟩ : syracuseStep 2013589 = 94387) (by norm_num)
theorem B1063325 : Blo 706319 1063325 := bbase (se 3 (by rfl) ⟨199373, by rfl⟩ : syracuseStep 1063325 = 398747) (by norm_num)
theorem B768413 : Blo 706319 768413 := bbase (se 3 (by rfl) ⟨144077, by rfl⟩ : syracuseStep 768413 = 288155) (by norm_num)
theorem B1063349 : Blo 706319 1063349 := bbase (se 5 (by rfl) ⟨49844, by rfl⟩ : syracuseStep 1063349 = 99689) (by norm_num)
theorem B1063373 : Blo 706319 1063373 := bbase (se 3 (by rfl) ⟨199382, by rfl⟩ : syracuseStep 1063373 = 398765) (by norm_num)
theorem B3586517 : Blo 706319 3586517 := bbase (se 7 (by rfl) ⟨42029, by rfl⟩ : syracuseStep 3586517 = 84059) (by norm_num)
theorem B1063397 : Blo 706319 1063397 := bbase (se 4 (by rfl) ⟨99693, by rfl⟩ : syracuseStep 1063397 = 199387) (by norm_num)
theorem B1194493 : Blo 706319 1194493 := bbase (se 3 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 1194493 = 447935) (by norm_num)
theorem B1063421 : Blo 706319 1063421 := bbase (se 3 (by rfl) ⟨199391, by rfl⟩ : syracuseStep 1063421 = 398783) (by norm_num)
theorem B1063445 : Blo 706319 1063445 := bbase (se 6 (by rfl) ⟨24924, by rfl⟩ : syracuseStep 1063445 = 49849) (by norm_num)
theorem B1063469 : Blo 706319 1063469 := bbase (se 3 (by rfl) ⟨199400, by rfl⟩ : syracuseStep 1063469 = 398801) (by norm_num)
theorem B1063493 : Blo 706319 1063493 := bbase (se 4 (by rfl) ⟨99702, by rfl⟩ : syracuseStep 1063493 = 199405) (by norm_num)
theorem B1194581 : Blo 706319 1194581 := bbase (se 8 (by rfl) ⟨6999, by rfl⟩ : syracuseStep 1194581 = 13999) (by norm_num)
theorem B8075861 : Blo 706319 8075861 := bbase (se 8 (by rfl) ⟨47319, by rfl⟩ : syracuseStep 8075861 = 94639) (by norm_num)
theorem B1063517 : Blo 706319 1063517 := bbase (se 3 (by rfl) ⟨199409, by rfl⟩ : syracuseStep 1063517 = 398819) (by norm_num)
theorem B1063541 : Blo 706319 1063541 := bbase (se 5 (by rfl) ⟨49853, by rfl⟩ : syracuseStep 1063541 = 99707) (by norm_num)
theorem B1063565 : Blo 706319 1063565 := bbase (se 3 (by rfl) ⟨199418, by rfl⟩ : syracuseStep 1063565 = 398837) (by norm_num)
theorem B1063589 : Blo 706319 1063589 := bbase (se 4 (by rfl) ⟨99711, by rfl⟩ : syracuseStep 1063589 = 199423) (by norm_num)
theorem B1063613 : Blo 706319 1063613 := bbase (se 3 (by rfl) ⟨199427, by rfl⟩ : syracuseStep 1063613 = 398855) (by norm_num)
theorem B10205909 : Blo 706319 10205909 := bbase (se 7 (by rfl) ⟨119600, by rfl⟩ : syracuseStep 10205909 = 239201) (by norm_num)
theorem B1194709 : Blo 706319 1194709 := bbase (se 7 (by rfl) ⟨14000, by rfl⟩ : syracuseStep 1194709 = 28001) (by norm_num)
theorem B1063637 : Blo 706319 1063637 := bbase (se 7 (by rfl) ⟨12464, by rfl⟩ : syracuseStep 1063637 = 24929) (by norm_num)
theorem B1063661 : Blo 706319 1063661 := bbase (se 3 (by rfl) ⟨199436, by rfl⟩ : syracuseStep 1063661 = 398873) (by norm_num)
theorem B1063685 : Blo 706319 1063685 := bbase (se 4 (by rfl) ⟨99720, by rfl⟩ : syracuseStep 1063685 = 199441) (by norm_num)
theorem B1063709 : Blo 706319 1063709 := bbase (se 3 (by rfl) ⟨199445, by rfl⟩ : syracuseStep 1063709 = 398891) (by norm_num)
theorem B1194797 : Blo 706319 1194797 := bbase (se 3 (by rfl) ⟨224024, by rfl⟩ : syracuseStep 1194797 = 448049) (by norm_num)
theorem B1063733 : Blo 706319 1063733 := bbase (se 5 (by rfl) ⟨49862, by rfl⟩ : syracuseStep 1063733 = 99725) (by norm_num)
theorem B1063757 : Blo 706319 1063757 := bbase (se 3 (by rfl) ⟨199454, by rfl⟩ : syracuseStep 1063757 = 398909) (by norm_num)
theorem B1063781 : Blo 706319 1063781 := bbase (se 4 (by rfl) ⟨99729, by rfl⟩ : syracuseStep 1063781 = 199459) (by norm_num)
theorem B1063805 : Blo 706319 1063805 := bbase (se 3 (by rfl) ⟨199463, by rfl⟩ : syracuseStep 1063805 = 398927) (by norm_num)
theorem B1063829 : Blo 706319 1063829 := bbase (se 6 (by rfl) ⟨24933, by rfl⟩ : syracuseStep 1063829 = 49867) (by norm_num)
theorem B1194925 : Blo 706319 1194925 := bbase (se 3 (by rfl) ⟨224048, by rfl⟩ : syracuseStep 1194925 = 448097) (by norm_num)
theorem B1063853 : Blo 706319 1063853 := bbase (se 3 (by rfl) ⟨199472, by rfl⟩ : syracuseStep 1063853 = 398945) (by norm_num)
theorem B1063877 : Blo 706319 1063877 := bbase (se 4 (by rfl) ⟨99738, by rfl⟩ : syracuseStep 1063877 = 199477) (by norm_num)
theorem B1063901 : Blo 706319 1063901 := bbase (se 3 (by rfl) ⟨199481, by rfl⟩ : syracuseStep 1063901 = 398963) (by norm_num)
theorem B1063925 : Blo 706319 1063925 := bbase (se 5 (by rfl) ⟨49871, by rfl⟩ : syracuseStep 1063925 = 99743) (by norm_num)
theorem B1195013 : Blo 706319 1195013 := bbase (se 4 (by rfl) ⟨112032, by rfl⟩ : syracuseStep 1195013 = 224065) (by norm_num)
theorem B1063949 : Blo 706319 1063949 := bbase (se 3 (by rfl) ⟨199490, by rfl⟩ : syracuseStep 1063949 = 398981) (by norm_num)
theorem B1063973 : Blo 706319 1063973 := bbase (se 4 (by rfl) ⟨99747, by rfl⟩ : syracuseStep 1063973 = 199495) (by norm_num)
theorem B1063997 : Blo 706319 1063997 := bbase (se 3 (by rfl) ⟨199499, by rfl⟩ : syracuseStep 1063997 = 398999) (by norm_num)
theorem B2866261 : Blo 706319 2866261 := bbase (se 8 (by rfl) ⟨16794, by rfl⟩ : syracuseStep 2866261 = 33589) (by norm_num)
theorem B1064021 : Blo 706319 1064021 := bbase (se 8 (by rfl) ⟨6234, by rfl⟩ : syracuseStep 1064021 = 12469) (by norm_num)
theorem B1064045 : Blo 706319 1064045 := bbase (se 3 (by rfl) ⟨199508, by rfl⟩ : syracuseStep 1064045 = 399017) (by norm_num)
theorem B1195141 : Blo 706319 1195141 := bbase (se 4 (by rfl) ⟨112044, by rfl⟩ : syracuseStep 1195141 = 224089) (by norm_num)
theorem B1064069 : Blo 706319 1064069 := bbase (se 4 (by rfl) ⟨99756, by rfl⟩ : syracuseStep 1064069 = 199513) (by norm_num)
theorem B1064093 : Blo 706319 1064093 := bbase (se 3 (by rfl) ⟨199517, by rfl⟩ : syracuseStep 1064093 = 399035) (by norm_num)
theorem B1064117 : Blo 706319 1064117 := bbase (se 5 (by rfl) ⟨49880, by rfl⟩ : syracuseStep 1064117 = 99761) (by norm_num)
theorem B1064141 : Blo 706319 1064141 := bbase (se 3 (by rfl) ⟨199526, by rfl⟩ : syracuseStep 1064141 = 399053) (by norm_num)
theorem B1195229 : Blo 706319 1195229 := bbase (se 3 (by rfl) ⟨224105, by rfl⟩ : syracuseStep 1195229 = 448211) (by norm_num)
theorem B1064165 : Blo 706319 1064165 := bbase (se 4 (by rfl) ⟨99765, by rfl⟩ : syracuseStep 1064165 = 199531) (by norm_num)
theorem B1064189 : Blo 706319 1064189 := bbase (se 3 (by rfl) ⟨199535, by rfl⟩ : syracuseStep 1064189 = 399071) (by norm_num)
theorem B1064213 : Blo 706319 1064213 := bbase (se 6 (by rfl) ⟨24942, by rfl⟩ : syracuseStep 1064213 = 49885) (by norm_num)
theorem B1064237 : Blo 706319 1064237 := bbase (se 3 (by rfl) ⟨199544, by rfl⟩ : syracuseStep 1064237 = 399089) (by norm_num)
theorem B1064261 : Blo 706319 1064261 := bbase (se 4 (by rfl) ⟨99774, by rfl⟩ : syracuseStep 1064261 = 199549) (by norm_num)
theorem B1195357 : Blo 706319 1195357 := bbase (se 3 (by rfl) ⟨224129, by rfl⟩ : syracuseStep 1195357 = 448259) (by norm_num)
theorem B1064285 : Blo 706319 1064285 := bbase (se 3 (by rfl) ⟨199553, by rfl⟩ : syracuseStep 1064285 = 399107) (by norm_num)
theorem B1064309 : Blo 706319 1064309 := bbase (se 5 (by rfl) ⟨49889, by rfl⟩ : syracuseStep 1064309 = 99779) (by norm_num)
theorem B1064333 : Blo 706319 1064333 := bbase (se 3 (by rfl) ⟨199562, by rfl⟩ : syracuseStep 1064333 = 399125) (by norm_num)
theorem B1064357 : Blo 706319 1064357 := bbase (se 4 (by rfl) ⟨99783, by rfl⟩ : syracuseStep 1064357 = 199567) (by norm_num)
theorem B1195445 : Blo 706319 1195445 := bbase (se 5 (by rfl) ⟨56036, by rfl⟩ : syracuseStep 1195445 = 112073) (by norm_num)
theorem B1064381 : Blo 706319 1064381 := bbase (se 3 (by rfl) ⟨199571, by rfl⟩ : syracuseStep 1064381 = 399143) (by norm_num)
theorem B1064405 : Blo 706319 1064405 := bbase (se 7 (by rfl) ⟨12473, by rfl⟩ : syracuseStep 1064405 = 24947) (by norm_num)
theorem B1064429 : Blo 706319 1064429 := bbase (se 3 (by rfl) ⟨199580, by rfl⟩ : syracuseStep 1064429 = 399161) (by norm_num)
theorem B1064453 : Blo 706319 1064453 := bbase (se 4 (by rfl) ⟨99792, by rfl⟩ : syracuseStep 1064453 = 199585) (by norm_num)
theorem B1064477 : Blo 706319 1064477 := bbase (se 3 (by rfl) ⟨199589, by rfl⟩ : syracuseStep 1064477 = 399179) (by norm_num)
theorem B1195573 : Blo 706319 1195573 := bbase (se 5 (by rfl) ⟨56042, by rfl⟩ : syracuseStep 1195573 = 112085) (by norm_num)
theorem B1064501 : Blo 706319 1064501 := bbase (se 5 (by rfl) ⟨49898, by rfl⟩ : syracuseStep 1064501 = 99797) (by norm_num)
theorem B1064525 : Blo 706319 1064525 := bbase (se 3 (by rfl) ⟨199598, by rfl⟩ : syracuseStep 1064525 = 399197) (by norm_num)
theorem B1064549 : Blo 706319 1064549 := bbase (se 4 (by rfl) ⟨99801, by rfl⟩ : syracuseStep 1064549 = 199603) (by norm_num)
theorem B1064573 : Blo 706319 1064573 := bbase (se 3 (by rfl) ⟨199607, by rfl⟩ : syracuseStep 1064573 = 399215) (by norm_num)
theorem B1195661 : Blo 706319 1195661 := bbase (se 3 (by rfl) ⟨224186, by rfl⟩ : syracuseStep 1195661 = 448373) (by norm_num)
theorem B1064597 : Blo 706319 1064597 := bbase (se 6 (by rfl) ⟨24951, by rfl⟩ : syracuseStep 1064597 = 49903) (by norm_num)
theorem B1064621 : Blo 706319 1064621 := bbase (se 3 (by rfl) ⟨199616, by rfl⟩ : syracuseStep 1064621 = 399233) (by norm_num)
theorem B1064645 : Blo 706319 1064645 := bbase (se 4 (by rfl) ⟨99810, by rfl⟩ : syracuseStep 1064645 = 199621) (by norm_num)
theorem B1064669 : Blo 706319 1064669 := bbase (se 3 (by rfl) ⟨199625, by rfl⟩ : syracuseStep 1064669 = 399251) (by norm_num)
theorem B3587813 : Blo 706319 3587813 := bbase (se 4 (by rfl) ⟨336357, by rfl⟩ : syracuseStep 3587813 = 672715) (by norm_num)
theorem B1064693 : Blo 706319 1064693 := bbase (se 5 (by rfl) ⟨49907, by rfl⟩ : syracuseStep 1064693 = 99815) (by norm_num)
theorem B1195789 : Blo 706319 1195789 := bbase (se 3 (by rfl) ⟨224210, by rfl⟩ : syracuseStep 1195789 = 448421) (by norm_num)
theorem B1064717 : Blo 706319 1064717 := bbase (se 3 (by rfl) ⟨199634, by rfl⟩ : syracuseStep 1064717 = 399269) (by norm_num)
theorem B1064741 : Blo 706319 1064741 := bbase (se 4 (by rfl) ⟨99819, by rfl⟩ : syracuseStep 1064741 = 199639) (by norm_num)
theorem B1064765 : Blo 706319 1064765 := bbase (se 3 (by rfl) ⟨199643, by rfl⟩ : syracuseStep 1064765 = 399287) (by norm_num)
theorem B1064789 : Blo 706319 1064789 := bbase (se 9 (by rfl) ⟨3119, by rfl⟩ : syracuseStep 1064789 = 6239) (by norm_num)
theorem B1195877 : Blo 706319 1195877 := bbase (se 4 (by rfl) ⟨112113, by rfl⟩ : syracuseStep 1195877 = 224227) (by norm_num)
theorem B1064813 : Blo 706319 1064813 := bbase (se 3 (by rfl) ⟨199652, by rfl⟩ : syracuseStep 1064813 = 399305) (by norm_num)
theorem B2015093 : Blo 706319 2015093 := bbase (se 5 (by rfl) ⟨94457, by rfl⟩ : syracuseStep 2015093 = 188915) (by norm_num)
theorem B1064837 : Blo 706319 1064837 := bbase (se 4 (by rfl) ⟨99828, by rfl⟩ : syracuseStep 1064837 = 199657) (by norm_num)
theorem B1064861 : Blo 706319 1064861 := bbase (se 3 (by rfl) ⟨199661, by rfl⟩ : syracuseStep 1064861 = 399323) (by norm_num)
theorem B1064885 : Blo 706319 1064885 := bbase (se 5 (by rfl) ⟨49916, by rfl⟩ : syracuseStep 1064885 = 99833) (by norm_num)
theorem B1064909 : Blo 706319 1064909 := bbase (se 3 (by rfl) ⟨199670, by rfl⟩ : syracuseStep 1064909 = 399341) (by norm_num)
theorem B1196005 : Blo 706319 1196005 := bbase (se 4 (by rfl) ⟨112125, by rfl⟩ : syracuseStep 1196005 = 224251) (by norm_num)
theorem B1064933 : Blo 706319 1064933 := bbase (se 4 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 1064933 = 199675) (by norm_num)
theorem B1589237 : Blo 706319 1589237 := bbase (se 5 (by rfl) ⟨74495, by rfl⟩ : syracuseStep 1589237 = 148991) (by norm_num)
theorem B1064957 : Blo 706319 1064957 := bbase (se 3 (by rfl) ⟨199679, by rfl⟩ : syracuseStep 1064957 = 399359) (by norm_num)
theorem B1064981 : Blo 706319 1064981 := bbase (se 6 (by rfl) ⟨24960, by rfl⟩ : syracuseStep 1064981 = 49921) (by norm_num)
theorem B1065005 : Blo 706319 1065005 := bbase (se 3 (by rfl) ⟨199688, by rfl⟩ : syracuseStep 1065005 = 399377) (by norm_num)
theorem B3227701 : Blo 706319 3227701 := bbase (se 5 (by rfl) ⟨151298, by rfl⟩ : syracuseStep 3227701 = 302597) (by norm_num)
theorem B1589309 : Blo 706319 1589309 := bbase (se 3 (by rfl) ⟨297995, by rfl⟩ : syracuseStep 1589309 = 595991) (by norm_num)
theorem B1196093 : Blo 706319 1196093 := bbase (se 3 (by rfl) ⟨224267, by rfl⟩ : syracuseStep 1196093 = 448535) (by norm_num)
theorem B1065029 : Blo 706319 1065029 := bbase (se 4 (by rfl) ⟨99846, by rfl⟩ : syracuseStep 1065029 = 199693) (by norm_num)
theorem B1065053 : Blo 706319 1065053 := bbase (se 3 (by rfl) ⟨199697, by rfl⟩ : syracuseStep 1065053 = 399395) (by norm_num)
theorem B1065077 : Blo 706319 1065077 := bbase (se 5 (by rfl) ⟨49925, by rfl⟩ : syracuseStep 1065077 = 99851) (by norm_num)
theorem B1589381 : Blo 706319 1589381 := bbase (se 4 (by rfl) ⟨149004, by rfl⟩ : syracuseStep 1589381 = 298009) (by norm_num)
theorem B1065101 : Blo 706319 1065101 := bbase (se 3 (by rfl) ⟨199706, by rfl⟩ : syracuseStep 1065101 = 399413) (by norm_num)
theorem B1065125 : Blo 706319 1065125 := bbase (se 4 (by rfl) ⟨99855, by rfl⟩ : syracuseStep 1065125 = 199711) (by norm_num)
theorem B1196221 : Blo 706319 1196221 := bbase (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) (by norm_num)
theorem B1065149 : Blo 706319 1065149 := bbase (se 3 (by rfl) ⟨199715, by rfl⟩ : syracuseStep 1065149 = 399431) (by norm_num)
theorem B1589453 : Blo 706319 1589453 := bbase (se 3 (by rfl) ⟨298022, by rfl⟩ : syracuseStep 1589453 = 596045) (by norm_num)
theorem B8536277 : Blo 706319 8536277 := bbase (se 7 (by rfl) ⟨100034, by rfl⟩ : syracuseStep 8536277 = 200069) (by norm_num)
theorem B1065173 : Blo 706319 1065173 := bbase (se 7 (by rfl) ⟨12482, by rfl⟩ : syracuseStep 1065173 = 24965) (by norm_num)
theorem B1065197 : Blo 706319 1065197 := bbase (se 3 (by rfl) ⟨199724, by rfl⟩ : syracuseStep 1065197 = 399449) (by norm_num)
theorem B1065221 : Blo 706319 1065221 := bbase (se 4 (by rfl) ⟨99864, by rfl⟩ : syracuseStep 1065221 = 199729) (by norm_num)
theorem B1589525 : Blo 706319 1589525 := bbase (se 6 (by rfl) ⟨37254, by rfl⟩ : syracuseStep 1589525 = 74509) (by norm_num)
theorem B1196309 : Blo 706319 1196309 := bbase (se 6 (by rfl) ⟨28038, by rfl⟩ : syracuseStep 1196309 = 56077) (by norm_num)
theorem B1065245 : Blo 706319 1065245 := bbase (se 3 (by rfl) ⟨199733, by rfl⟩ : syracuseStep 1065245 = 399467) (by norm_num)
theorem B1065269 : Blo 706319 1065269 := bbase (se 5 (by rfl) ⟨49934, by rfl⟩ : syracuseStep 1065269 = 99869) (by norm_num)
theorem B1065293 : Blo 706319 1065293 := bbase (se 3 (by rfl) ⟨199742, by rfl⟩ : syracuseStep 1065293 = 399485) (by norm_num)
theorem B1589597 : Blo 706319 1589597 := bbase (se 3 (by rfl) ⟨298049, by rfl⟩ : syracuseStep 1589597 = 596099) (by norm_num)
theorem B1065317 : Blo 706319 1065317 := bbase (se 4 (by rfl) ⟨99873, by rfl⟩ : syracuseStep 1065317 = 199747) (by norm_num)
theorem B1065341 : Blo 706319 1065341 := bbase (se 3 (by rfl) ⟨199751, by rfl⟩ : syracuseStep 1065341 = 399503) (by norm_num)
theorem B7258517 : Blo 706319 7258517 := bbase (se 6 (by rfl) ⟨170121, by rfl⟩ : syracuseStep 7258517 = 340243) (by norm_num)
theorem B1196437 : Blo 706319 1196437 := bbase (se 6 (by rfl) ⟨28041, by rfl⟩ : syracuseStep 1196437 = 56083) (by norm_num)
theorem B1065365 : Blo 706319 1065365 := bbase (se 6 (by rfl) ⟨24969, by rfl⟩ : syracuseStep 1065365 = 49939) (by norm_num)
theorem B1589669 : Blo 706319 1589669 := bbase (se 4 (by rfl) ⟨149031, by rfl⟩ : syracuseStep 1589669 = 298063) (by norm_num)
theorem B1065389 : Blo 706319 1065389 := bbase (se 3 (by rfl) ⟨199760, by rfl⟩ : syracuseStep 1065389 = 399521) (by norm_num)
theorem B1065413 : Blo 706319 1065413 := bbase (se 4 (by rfl) ⟨99882, by rfl⟩ : syracuseStep 1065413 = 199765) (by norm_num)
theorem B1065437 : Blo 706319 1065437 := bbase (se 3 (by rfl) ⟨199769, by rfl⟩ : syracuseStep 1065437 = 399539) (by norm_num)
theorem B1589741 : Blo 706319 1589741 := bbase (se 3 (by rfl) ⟨298076, by rfl⟩ : syracuseStep 1589741 = 596153) (by norm_num)
theorem B1196525 : Blo 706319 1196525 := bbase (se 3 (by rfl) ⟨224348, by rfl⟩ : syracuseStep 1196525 = 448697) (by norm_num)
theorem B1065461 : Blo 706319 1065461 := bbase (se 5 (by rfl) ⟨49943, by rfl⟩ : syracuseStep 1065461 = 99887) (by norm_num)
theorem B3195413 : Blo 706319 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B1589813 : Blo 706319 1589813 := bbase (se 5 (by rfl) ⟨74522, by rfl⟩ : syracuseStep 1589813 = 149045) (by norm_num)
theorem B1196653 : Blo 706319 1196653 := bbase (se 3 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 1196653 = 448745) (by norm_num)
theorem B1589885 : Blo 706319 1589885 := bbase (se 3 (by rfl) ⟨298103, by rfl⟩ : syracuseStep 1589885 = 596207) (by norm_num)
theorem B1589957 : Blo 706319 1589957 := bbase (se 4 (by rfl) ⟨149058, by rfl⟩ : syracuseStep 1589957 = 298117) (by norm_num)
theorem B1196741 : Blo 706319 1196741 := bbase (se 4 (by rfl) ⟨112194, by rfl⟩ : syracuseStep 1196741 = 224389) (by norm_num)
theorem B1590029 : Blo 706319 1590029 := bbase (se 3 (by rfl) ⟨298130, by rfl⟩ : syracuseStep 1590029 = 596261) (by norm_num)
theorem B1196869 : Blo 706319 1196869 := bbase (se 4 (by rfl) ⟨112206, by rfl⟩ : syracuseStep 1196869 = 224413) (by norm_num)
theorem B1590101 : Blo 706319 1590101 := bbase (se 9 (by rfl) ⟨4658, by rfl⟩ : syracuseStep 1590101 = 9317) (by norm_num)
theorem B1819525 : Blo 706319 1819525 := bbase (se 4 (by rfl) ⟨170580, by rfl⟩ : syracuseStep 1819525 = 341161) (by norm_num)
theorem B1590173 : Blo 706319 1590173 := bbase (se 3 (by rfl) ⟨298157, by rfl⟩ : syracuseStep 1590173 = 596315) (by norm_num)
theorem B1196957 : Blo 706319 1196957 := bbase (se 3 (by rfl) ⟨224429, by rfl⟩ : syracuseStep 1196957 = 448859) (by norm_num)
theorem B1590245 : Blo 706319 1590245 := bbase (se 4 (by rfl) ⟨149085, by rfl⟩ : syracuseStep 1590245 = 298171) (by norm_num)
theorem B3589109 : Blo 706319 3589109 := bbase (se 5 (by rfl) ⟨168239, by rfl⟩ : syracuseStep 3589109 = 336479) (by norm_num)
theorem B1197085 : Blo 706319 1197085 := bbase (se 3 (by rfl) ⟨224453, by rfl⟩ : syracuseStep 1197085 = 448907) (by norm_num)
theorem B1590317 : Blo 706319 1590317 := bbase (se 3 (by rfl) ⟨298184, by rfl⟩ : syracuseStep 1590317 = 596369) (by norm_num)
theorem B1590389 : Blo 706319 1590389 := bbase (se 5 (by rfl) ⟨74549, by rfl⟩ : syracuseStep 1590389 = 149099) (by norm_num)
theorem B1197173 : Blo 706319 1197173 := bbase (se 5 (by rfl) ⟨56117, by rfl⟩ : syracuseStep 1197173 = 112235) (by norm_num)
theorem B3458213 : Blo 706319 3458213 := bbase (se 4 (by rfl) ⟨324207, by rfl⟩ : syracuseStep 3458213 = 648415) (by norm_num)
theorem B1590461 : Blo 706319 1590461 := bbase (se 3 (by rfl) ⟨298211, by rfl⟩ : syracuseStep 1590461 = 596423) (by norm_num)
theorem B3032261 : Blo 706319 3032261 := bbase (se 4 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 3032261 = 568549) (by norm_num)
theorem B7259381 : Blo 706319 7259381 := bbase (se 5 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 7259381 = 680567) (by norm_num)
theorem B1197301 : Blo 706319 1197301 := bbase (se 5 (by rfl) ⟨56123, by rfl⟩ : syracuseStep 1197301 = 112247) (by norm_num)
theorem B1590533 : Blo 706319 1590533 := bbase (se 4 (by rfl) ⟨149112, by rfl⟩ : syracuseStep 1590533 = 298225) (by norm_num)
theorem B1590605 : Blo 706319 1590605 := bbase (se 3 (by rfl) ⟨298238, by rfl⟩ : syracuseStep 1590605 = 596477) (by norm_num)
theorem B1197389 : Blo 706319 1197389 := bbase (se 3 (by rfl) ⟨224510, by rfl⟩ : syracuseStep 1197389 = 449021) (by norm_num)
theorem B1590677 : Blo 706319 1590677 := bbase (se 6 (by rfl) ⟨37281, by rfl⟩ : syracuseStep 1590677 = 74563) (by norm_num)
theorem B2016677 : Blo 706319 2016677 := bbase (se 4 (by rfl) ⟨189063, by rfl⟩ : syracuseStep 2016677 = 378127) (by norm_num)
theorem B1197517 : Blo 706319 1197517 := bbase (se 3 (by rfl) ⟨224534, by rfl⟩ : syracuseStep 1197517 = 449069) (by norm_num)
theorem B1918421 : Blo 706319 1918421 := bbase (se 7 (by rfl) ⟨22481, by rfl⟩ : syracuseStep 1918421 = 44963) (by norm_num)
theorem B1590749 : Blo 706319 1590749 := bbase (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) (by norm_num)
theorem B3032549 : Blo 706319 3032549 := bbase (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) (by norm_num)
theorem B1590821 : Blo 706319 1590821 := bbase (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) (by norm_num)
theorem B1197605 : Blo 706319 1197605 := bbase (se 4 (by rfl) ⟨112275, by rfl⟩ : syracuseStep 1197605 = 224551) (by norm_num)
theorem B1590893 : Blo 706319 1590893 := bbase (se 3 (by rfl) ⟨298292, by rfl⟩ : syracuseStep 1590893 = 596585) (by norm_num)
theorem B1197733 : Blo 706319 1197733 := bbase (se 4 (by rfl) ⟨112287, by rfl⟩ : syracuseStep 1197733 = 224575) (by norm_num)
theorem B1590965 : Blo 706319 1590965 := bbase (se 5 (by rfl) ⟨74576, by rfl⟩ : syracuseStep 1590965 = 149153) (by norm_num)
theorem B1591037 : Blo 706319 1591037 := bbase (se 3 (by rfl) ⟨298319, by rfl⟩ : syracuseStep 1591037 = 596639) (by norm_num)
theorem B1197821 : Blo 706319 1197821 := bbase (se 3 (by rfl) ⟨224591, by rfl⟩ : syracuseStep 1197821 = 449183) (by norm_num)
theorem B1591109 : Blo 706319 1591109 := bbase (se 4 (by rfl) ⟨149166, by rfl⟩ : syracuseStep 1591109 = 298333) (by norm_num)
theorem B1197949 : Blo 706319 1197949 := bbase (se 3 (by rfl) ⟨224615, by rfl⟩ : syracuseStep 1197949 = 449231) (by norm_num)
theorem B1591181 : Blo 706319 1591181 := bbase (se 3 (by rfl) ⟨298346, by rfl⟩ : syracuseStep 1591181 = 596693) (by norm_num)
theorem B1591253 : Blo 706319 1591253 := bbase (se 7 (by rfl) ⟨18647, by rfl⟩ : syracuseStep 1591253 = 37295) (by norm_num)
theorem B1198037 : Blo 706319 1198037 := bbase (se 7 (by rfl) ⟨14039, by rfl⟩ : syracuseStep 1198037 = 28079) (by norm_num)
theorem B1132517 : Blo 706319 1132517 := bbase (se 4 (by rfl) ⟨106173, by rfl⟩ : syracuseStep 1132517 = 212347) (by norm_num)
theorem B1787933 : Blo 706319 1787933 := bbase (se 3 (by rfl) ⟨335237, by rfl⟩ : syracuseStep 1787933 = 670475) (by norm_num)
theorem B1591325 : Blo 706319 1591325 := bbase (se 3 (by rfl) ⟨298373, by rfl⟩ : syracuseStep 1591325 = 596747) (by norm_num)
theorem B2017349 : Blo 706319 2017349 := bbase (se 4 (by rfl) ⟨189126, by rfl⟩ : syracuseStep 2017349 = 378253) (by norm_num)
theorem B1198165 : Blo 706319 1198165 := bbase (se 8 (by rfl) ⟨7020, by rfl⟩ : syracuseStep 1198165 = 14041) (by norm_num)
theorem B1591397 : Blo 706319 1591397 := bbase (se 4 (by rfl) ⟨149193, by rfl⟩ : syracuseStep 1591397 = 298387) (by norm_num)
theorem B1820837 : Blo 706319 1820837 := bbase (se 4 (by rfl) ⟨170703, by rfl⟩ : syracuseStep 1820837 = 341407) (by norm_num)
theorem B1591469 : Blo 706319 1591469 := bbase (se 3 (by rfl) ⟨298400, by rfl⟩ : syracuseStep 1591469 = 596801) (by norm_num)
theorem B1198253 : Blo 706319 1198253 := bbase (se 3 (by rfl) ⟨224672, by rfl⟩ : syracuseStep 1198253 = 449345) (by norm_num)
theorem B1132741 : Blo 706319 1132741 := bbase (se 4 (by rfl) ⟨106194, by rfl⟩ : syracuseStep 1132741 = 212389) (by norm_num)
theorem B1362125 : Blo 706319 1362125 := bbase (se 3 (by rfl) ⟨255398, by rfl⟩ : syracuseStep 1362125 = 510797) (by norm_num)
theorem B3033301 : Blo 706319 3033301 := bbase (se 7 (by rfl) ⟨35546, by rfl⟩ : syracuseStep 3033301 = 71093) (by norm_num)
theorem B1591541 : Blo 706319 1591541 := bbase (se 5 (by rfl) ⟨74603, by rfl⟩ : syracuseStep 1591541 = 149207) (by norm_num)
theorem B3590405 : Blo 706319 3590405 := bbase (se 4 (by rfl) ⟨336600, by rfl⟩ : syracuseStep 3590405 = 673201) (by norm_num)
theorem B1198381 : Blo 706319 1198381 := bbase (se 3 (by rfl) ⟨224696, by rfl⟩ : syracuseStep 1198381 = 449393) (by norm_num)
theorem B1591613 : Blo 706319 1591613 := bbase (se 3 (by rfl) ⟨298427, by rfl⟩ : syracuseStep 1591613 = 596855) (by norm_num)
theorem B1296749 : Blo 706319 1296749 := bbase (se 3 (by rfl) ⟨243140, by rfl⟩ : syracuseStep 1296749 = 486281) (by norm_num)
theorem B1788277 : Blo 706319 1788277 := bbase (se 5 (by rfl) ⟨83825, by rfl⟩ : syracuseStep 1788277 = 167651) (by norm_num)
theorem B1591685 : Blo 706319 1591685 := bbase (se 4 (by rfl) ⟨149220, by rfl⟩ : syracuseStep 1591685 = 298441) (by norm_num)
theorem B1198469 : Blo 706319 1198469 := bbase (se 4 (by rfl) ⟨112356, by rfl⟩ : syracuseStep 1198469 = 224713) (by norm_num)
theorem B1919381 : Blo 706319 1919381 := bbase (se 6 (by rfl) ⟨44985, by rfl⟩ : syracuseStep 1919381 = 89971) (by norm_num)
theorem B1591757 : Blo 706319 1591757 := bbase (se 3 (by rfl) ⟨298454, by rfl⟩ : syracuseStep 1591757 = 596909) (by norm_num)
theorem B1788389 : Blo 706319 1788389 := bbase (se 4 (by rfl) ⟨167661, by rfl⟩ : syracuseStep 1788389 = 335323) (by norm_num)
theorem B2017781 : Blo 706319 2017781 := bbase (se 5 (by rfl) ⟨94583, by rfl⟩ : syracuseStep 2017781 = 189167) (by norm_num)
theorem B1198597 : Blo 706319 1198597 := bbase (se 4 (by rfl) ⟨112368, by rfl⟩ : syracuseStep 1198597 = 224737) (by norm_num)
theorem B1591829 : Blo 706319 1591829 := bbase (se 6 (by rfl) ⟨37308, by rfl⟩ : syracuseStep 1591829 = 74617) (by norm_num)
theorem B1591901 : Blo 706319 1591901 := bbase (se 3 (by rfl) ⟨298481, by rfl⟩ : syracuseStep 1591901 = 596963) (by norm_num)
theorem B1788581 : Blo 706319 1788581 := bbase (se 4 (by rfl) ⟨167679, by rfl⟩ : syracuseStep 1788581 = 335359) (by norm_num)
theorem B1591973 : Blo 706319 1591973 := bbase (se 4 (by rfl) ⟨149247, by rfl⟩ : syracuseStep 1591973 = 298495) (by norm_num)
theorem B2869925 : Blo 706319 2869925 := bbase (se 4 (by rfl) ⟨269055, by rfl⟩ : syracuseStep 2869925 = 538111) (by norm_num)
theorem B1592045 : Blo 706319 1592045 := bbase (se 3 (by rfl) ⟨298508, by rfl⟩ : syracuseStep 1592045 = 597017) (by norm_num)
theorem B5393141 : Blo 706319 5393141 := bbase (se 5 (by rfl) ⟨252803, by rfl⟩ : syracuseStep 5393141 = 505607) (by norm_num)
theorem B1592117 : Blo 706319 1592117 := bbase (se 5 (by rfl) ⟨74630, by rfl⟩ : syracuseStep 1592117 = 149261) (by norm_num)
theorem B1592189 : Blo 706319 1592189 := bbase (se 3 (by rfl) ⟨298535, by rfl⟩ : syracuseStep 1592189 = 597071) (by norm_num)
theorem B3034037 : Blo 706319 3034037 := bbase (se 5 (by rfl) ⟨142220, by rfl⟩ : syracuseStep 3034037 = 284441) (by norm_num)
theorem B1592261 : Blo 706319 1592261 := bbase (se 4 (by rfl) ⟨149274, by rfl⟩ : syracuseStep 1592261 = 298549) (by norm_num)
theorem B8604629 : Blo 706319 8604629 := bbase (se 7 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 8604629 = 201671) (by norm_num)
theorem B1788925 : Blo 706319 1788925 := bbase (se 3 (by rfl) ⟨335423, by rfl⟩ : syracuseStep 1788925 = 670847) (by norm_num)
theorem B1592333 : Blo 706319 1592333 := bbase (se 3 (by rfl) ⟨298562, by rfl⟩ : syracuseStep 1592333 = 597125) (by norm_num)
theorem B1592405 : Blo 706319 1592405 := bbase (se 8 (by rfl) ⟨9330, by rfl⟩ : syracuseStep 1592405 = 18661) (by norm_num)
theorem B1789037 : Blo 706319 1789037 := bbase (se 3 (by rfl) ⟨335444, by rfl⟩ : syracuseStep 1789037 = 670889) (by norm_num)
theorem B1592477 : Blo 706319 1592477 := bbase (se 3 (by rfl) ⟨298589, by rfl⟩ : syracuseStep 1592477 = 597179) (by norm_num)
theorem B1592549 : Blo 706319 1592549 := bbase (se 4 (by rfl) ⟨149301, by rfl⟩ : syracuseStep 1592549 = 298603) (by norm_num)
theorem B2018533 : Blo 706319 2018533 := bbase (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) (by norm_num)
theorem B1789229 : Blo 706319 1789229 := bbase (se 3 (by rfl) ⟨335480, by rfl⟩ : syracuseStep 1789229 = 670961) (by norm_num)
theorem B1592621 : Blo 706319 1592621 := bbase (se 3 (by rfl) ⟨298616, by rfl⟩ : syracuseStep 1592621 = 597233) (by norm_num)
theorem B1592693 : Blo 706319 1592693 := bbase (se 5 (by rfl) ⟨74657, by rfl⟩ : syracuseStep 1592693 = 149315) (by norm_num)
theorem B1592765 : Blo 706319 1592765 := bbase (se 3 (by rfl) ⟨298643, by rfl⟩ : syracuseStep 1592765 = 597287) (by norm_num)
theorem B1592837 : Blo 706319 1592837 := bbase (se 4 (by rfl) ⟨149328, by rfl⟩ : syracuseStep 1592837 = 298657) (by norm_num)
theorem B3591701 : Blo 706319 3591701 := bbase (se 6 (by rfl) ⟨84180, by rfl⟩ : syracuseStep 3591701 = 168361) (by norm_num)
theorem B1592909 : Blo 706319 1592909 := bbase (se 3 (by rfl) ⟨298670, by rfl⟩ : syracuseStep 1592909 = 597341) (by norm_num)
theorem B1134157 : Blo 706319 1134157 := bbase (se 3 (by rfl) ⟨212654, by rfl⟩ : syracuseStep 1134157 = 425309) (by norm_num)
theorem B9064021 : Blo 706319 9064021 := bbase (se 8 (by rfl) ⟨53109, by rfl⟩ : syracuseStep 9064021 = 106219) (by norm_num)
theorem B1789573 : Blo 706319 1789573 := bbase (se 4 (by rfl) ⟨167772, by rfl⟩ : syracuseStep 1789573 = 335545) (by norm_num)
theorem B1592981 : Blo 706319 1592981 := bbase (se 6 (by rfl) ⟨37335, by rfl⟩ : syracuseStep 1592981 = 74671) (by norm_num)
theorem B1593053 : Blo 706319 1593053 := bbase (se 3 (by rfl) ⟨298697, by rfl⟩ : syracuseStep 1593053 = 597395) (by norm_num)
theorem B1789685 : Blo 706319 1789685 := bbase (se 5 (by rfl) ⟨83891, by rfl⟩ : syracuseStep 1789685 = 167783) (by norm_num)
theorem B1593125 : Blo 706319 1593125 := bbase (se 4 (by rfl) ⟨149355, by rfl⟩ : syracuseStep 1593125 = 298711) (by norm_num)
theorem B1134413 : Blo 706319 1134413 := bbase (se 3 (by rfl) ⟨212702, by rfl⟩ : syracuseStep 1134413 = 425405) (by norm_num)
theorem B1396565 : Blo 706319 1396565 := bbase (se 9 (by rfl) ⟨4091, by rfl⟩ : syracuseStep 1396565 = 8183) (by norm_num)
theorem B3231589 : Blo 706319 3231589 := bbase (se 4 (by rfl) ⟨302961, by rfl⟩ : syracuseStep 3231589 = 605923) (by norm_num)
theorem B1593197 : Blo 706319 1593197 := bbase (se 3 (by rfl) ⟨298724, by rfl⟩ : syracuseStep 1593197 = 597449) (by norm_num)
theorem B1789877 : Blo 706319 1789877 := bbase (se 5 (by rfl) ⟨83900, by rfl⟩ : syracuseStep 1789877 = 167801) (by norm_num)
theorem B1593269 : Blo 706319 1593269 := bbase (se 5 (by rfl) ⟨74684, by rfl⟩ : syracuseStep 1593269 = 149369) (by norm_num)
theorem B7655381 : Blo 706319 7655381 := bbase (se 7 (by rfl) ⟨89711, by rfl⟩ : syracuseStep 7655381 = 179423) (by norm_num)
theorem B1593341 : Blo 706319 1593341 := bbase (se 3 (by rfl) ⟨298751, by rfl⟩ : syracuseStep 1593341 = 597503) (by norm_num)
theorem B1134605 : Blo 706319 1134605 := bbase (se 3 (by rfl) ⟨212738, by rfl⟩ : syracuseStep 1134605 = 425477) (by norm_num)
theorem B1593413 : Blo 706319 1593413 := bbase (se 4 (by rfl) ⟨149382, by rfl⟩ : syracuseStep 1593413 = 298765) (by norm_num)
theorem B1593485 : Blo 706319 1593485 := bbase (se 3 (by rfl) ⟨298778, by rfl⟩ : syracuseStep 1593485 = 597557) (by norm_num)
theorem B1593557 : Blo 706319 1593557 := bbase (se 7 (by rfl) ⟨18674, by rfl⟩ : syracuseStep 1593557 = 37349) (by norm_num)
theorem B1790221 : Blo 706319 1790221 := bbase (se 3 (by rfl) ⟨335666, by rfl⟩ : syracuseStep 1790221 = 671333) (by norm_num)
theorem B1593629 : Blo 706319 1593629 := bbase (se 3 (by rfl) ⟨298805, by rfl⟩ : syracuseStep 1593629 = 597611) (by norm_num)
theorem B807241 : Blo 706319 807241 := bbase (se 2 (by rfl) ⟨302715, by rfl⟩ : syracuseStep 807241 = 605431) (by norm_num)
theorem B1593701 : Blo 706319 1593701 := bbase (se 4 (by rfl) ⟨149409, by rfl⟩ : syracuseStep 1593701 = 298819) (by norm_num)
theorem B1790333 : Blo 706319 1790333 := bbase (se 3 (by rfl) ⟨335687, by rfl⟩ : syracuseStep 1790333 = 671375) (by norm_num)
theorem B1593773 : Blo 706319 1593773 := bbase (se 3 (by rfl) ⟨298832, by rfl⟩ : syracuseStep 1593773 = 597665) (by norm_num)
theorem B1593845 : Blo 706319 1593845 := bbase (se 5 (by rfl) ⟨74711, by rfl⟩ : syracuseStep 1593845 = 149423) (by norm_num)
theorem B1790525 : Blo 706319 1790525 := bbase (se 3 (by rfl) ⟨335723, by rfl⟩ : syracuseStep 1790525 = 671447) (by norm_num)
theorem B1593917 : Blo 706319 1593917 := bbase (se 3 (by rfl) ⟨298859, by rfl⟩ : syracuseStep 1593917 = 597719) (by norm_num)
theorem B1364557 : Blo 706319 1364557 := bbase (se 3 (by rfl) ⟨255854, by rfl⟩ : syracuseStep 1364557 = 511709) (by norm_num)
theorem B1593989 : Blo 706319 1593989 := bbase (se 4 (by rfl) ⟨149436, by rfl⟩ : syracuseStep 1593989 = 298873) (by norm_num)
theorem B1594061 : Blo 706319 1594061 := bbase (se 3 (by rfl) ⟨298886, by rfl⟩ : syracuseStep 1594061 = 597773) (by norm_num)
theorem B5100245 : Blo 706319 5100245 := bbase (se 7 (by rfl) ⟨59768, by rfl⟩ : syracuseStep 5100245 = 119537) (by norm_num)
theorem B1594133 : Blo 706319 1594133 := bbase (se 6 (by rfl) ⟨37362, by rfl⟩ : syracuseStep 1594133 = 74725) (by norm_num)
theorem B3592997 : Blo 706319 3592997 := bbase (se 4 (by rfl) ⟨336843, by rfl⟩ : syracuseStep 3592997 = 673687) (by norm_num)
theorem B1037125 : Blo 706319 1037125 := bbase (se 4 (by rfl) ⟨97230, by rfl⟩ : syracuseStep 1037125 = 194461) (by norm_num)
theorem B807769 : Blo 706319 807769 := bbase (se 2 (by rfl) ⟨302913, by rfl⟩ : syracuseStep 807769 = 605827) (by norm_num)
theorem B1594205 : Blo 706319 1594205 := bbase (se 3 (by rfl) ⟨298913, by rfl⟩ : syracuseStep 1594205 = 597827) (by norm_num)
theorem B2872181 : Blo 706319 2872181 := bbase (se 5 (by rfl) ⟨134633, by rfl⟩ : syracuseStep 2872181 = 269267) (by norm_num)
theorem B1790869 : Blo 706319 1790869 := bbase (se 6 (by rfl) ⟨41973, by rfl⟩ : syracuseStep 1790869 = 83947) (by norm_num)
theorem B1594277 : Blo 706319 1594277 := bbase (se 4 (by rfl) ⟨149463, by rfl⟩ : syracuseStep 1594277 = 298927) (by norm_num)
theorem B1135541 : Blo 706319 1135541 := bbase (se 5 (by rfl) ⟨53228, by rfl⟩ : syracuseStep 1135541 = 106457) (by norm_num)
theorem B1594349 : Blo 706319 1594349 := bbase (se 3 (by rfl) ⟨298940, by rfl⟩ : syracuseStep 1594349 = 597881) (by norm_num)
theorem B1790981 : Blo 706319 1790981 := bbase (se 4 (by rfl) ⟨167904, by rfl⟩ : syracuseStep 1790981 = 335809) (by norm_num)
theorem B906277 : Blo 706319 906277 := bbase (se 4 (by rfl) ⟨84963, by rfl⟩ : syracuseStep 906277 = 169927) (by norm_num)
theorem B1594421 : Blo 706319 1594421 := bbase (se 5 (by rfl) ⟨74738, by rfl⟩ : syracuseStep 1594421 = 149477) (by norm_num)
theorem B1594493 : Blo 706319 1594493 := bbase (se 3 (by rfl) ⟨298967, by rfl⟩ : syracuseStep 1594493 = 597935) (by norm_num)
theorem B873613 : Blo 706319 873613 := bbase (se 3 (by rfl) ⟨163802, by rfl⟩ : syracuseStep 873613 = 327605) (by norm_num)
theorem B1791173 : Blo 706319 1791173 := bbase (se 4 (by rfl) ⟨167922, by rfl⟩ : syracuseStep 1791173 = 335845) (by norm_num)
theorem B1594565 : Blo 706319 1594565 := bbase (se 4 (by rfl) ⟨149490, by rfl⟩ : syracuseStep 1594565 = 298981) (by norm_num)
theorem B1594637 : Blo 706319 1594637 := bbase (se 3 (by rfl) ⟨298994, by rfl⟩ : syracuseStep 1594637 = 597989) (by norm_num)
theorem B1135925 : Blo 706319 1135925 := bbase (se 5 (by rfl) ⟨53246, by rfl⟩ : syracuseStep 1135925 = 106493) (by norm_num)
theorem B1594709 : Blo 706319 1594709 := bbase (se 16 (by rfl) ⟨36, by rfl⟩ : syracuseStep 1594709 = 73) (by norm_num)
theorem B1594781 : Blo 706319 1594781 := bbase (se 3 (by rfl) ⟨299021, by rfl⟩ : syracuseStep 1594781 = 598043) (by norm_num)
theorem B1136053 : Blo 706319 1136053 := bbase (se 5 (by rfl) ⟨53252, by rfl⟩ : syracuseStep 1136053 = 106505) (by norm_num)
theorem B808385 : Blo 706319 808385 := bbase (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) (by norm_num)
theorem B1594853 : Blo 706319 1594853 := bbase (se 4 (by rfl) ⟨149517, by rfl⟩ : syracuseStep 1594853 = 299035) (by norm_num)
theorem B1791517 : Blo 706319 1791517 := bbase (se 3 (by rfl) ⟨335909, by rfl⟩ : syracuseStep 1791517 = 671819) (by norm_num)
theorem B1594925 : Blo 706319 1594925 := bbase (se 3 (by rfl) ⟨299048, by rfl⟩ : syracuseStep 1594925 = 598097) (by norm_num)
theorem B1594997 : Blo 706319 1594997 := bbase (se 5 (by rfl) ⟨74765, by rfl⟩ : syracuseStep 1594997 = 149531) (by norm_num)
theorem B1791629 : Blo 706319 1791629 := bbase (se 3 (by rfl) ⟨335930, by rfl⟩ : syracuseStep 1791629 = 671861) (by norm_num)
theorem B3397301 : Blo 706319 3397301 := bbase (se 5 (by rfl) ⟨159248, by rfl⟩ : syracuseStep 3397301 = 318497) (by norm_num)
theorem B1595069 : Blo 706319 1595069 := bbase (se 3 (by rfl) ⟨299075, by rfl⟩ : syracuseStep 1595069 = 598151) (by norm_num)
theorem B808645 : Blo 706319 808645 := bbase (se 4 (by rfl) ⟨75810, by rfl⟩ : syracuseStep 808645 = 151621) (by norm_num)
theorem B1595141 : Blo 706319 1595141 := bbase (se 4 (by rfl) ⟨149544, by rfl⟩ : syracuseStep 1595141 = 299089) (by norm_num)
theorem B907057 : Blo 706319 907057 := bbase (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) (by norm_num)
theorem B1791821 : Blo 706319 1791821 := bbase (se 3 (by rfl) ⟨335966, by rfl⟩ : syracuseStep 1791821 = 671933) (by norm_num)
theorem B1595213 : Blo 706319 1595213 := bbase (se 3 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 1595213 = 598205) (by norm_num)
theorem B6805397 : Blo 706319 6805397 := bbase (se 6 (by rfl) ⟨159501, by rfl⟩ : syracuseStep 6805397 = 319003) (by norm_num)
theorem B1595285 : Blo 706319 1595285 := bbase (se 6 (by rfl) ⟨37389, by rfl⟩ : syracuseStep 1595285 = 74779) (by norm_num)
theorem B1595357 : Blo 706319 1595357 := bbase (se 3 (by rfl) ⟨299129, by rfl⟩ : syracuseStep 1595357 = 598259) (by norm_num)
theorem B2021381 : Blo 706319 2021381 := bbase (se 4 (by rfl) ⟨189504, by rfl⟩ : syracuseStep 2021381 = 379009) (by norm_num)
theorem B1366021 : Blo 706319 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B1595429 : Blo 706319 1595429 := bbase (se 4 (by rfl) ⟨149571, by rfl⟩ : syracuseStep 1595429 = 299143) (by norm_num)
theorem B3594293 : Blo 706319 3594293 := bbase (se 5 (by rfl) ⟨168482, by rfl⟩ : syracuseStep 3594293 = 336965) (by norm_num)
theorem B1595501 : Blo 706319 1595501 := bbase (se 3 (by rfl) ⟨299156, by rfl⟩ : syracuseStep 1595501 = 598313) (by norm_num)
theorem B1005701 : Blo 706319 1005701 := bbase (se 4 (by rfl) ⟨94284, by rfl⟩ : syracuseStep 1005701 = 188569) (by norm_num)
theorem B2545829 : Blo 706319 2545829 := bbase (se 4 (by rfl) ⟨238671, by rfl⟩ : syracuseStep 2545829 = 477343) (by norm_num)
theorem B1792165 : Blo 706319 1792165 := bbase (se 4 (by rfl) ⟨168015, by rfl⟩ : syracuseStep 1792165 = 336031) (by norm_num)
theorem B1595573 : Blo 706319 1595573 := bbase (se 5 (by rfl) ⟨74792, by rfl⟩ : syracuseStep 1595573 = 149585) (by norm_num)
theorem B1595645 : Blo 706319 1595645 := bbase (se 3 (by rfl) ⟨299183, by rfl⟩ : syracuseStep 1595645 = 598367) (by norm_num)
theorem B1792277 : Blo 706319 1792277 := bbase (se 6 (by rfl) ⟨42006, by rfl⟩ : syracuseStep 1792277 = 84013) (by norm_num)
theorem B1136941 : Blo 706319 1136941 := bbase (se 3 (by rfl) ⟨213176, by rfl⟩ : syracuseStep 1136941 = 426353) (by norm_num)
theorem B1595717 : Blo 706319 1595717 := bbase (se 4 (by rfl) ⟨149598, by rfl⟩ : syracuseStep 1595717 = 299197) (by norm_num)
theorem B1595789 : Blo 706319 1595789 := bbase (se 3 (by rfl) ⟨299210, by rfl⟩ : syracuseStep 1595789 = 598421) (by norm_num)
theorem B809357 : Blo 706319 809357 := bbase (se 3 (by rfl) ⟨151754, by rfl⟩ : syracuseStep 809357 = 303509) (by norm_num)
theorem B1137053 : Blo 706319 1137053 := bbase (se 3 (by rfl) ⟨213197, by rfl⟩ : syracuseStep 1137053 = 426395) (by norm_num)
theorem B1792469 : Blo 706319 1792469 := bbase (se 7 (by rfl) ⟨21005, by rfl⟩ : syracuseStep 1792469 = 42011) (by norm_num)
theorem B1595861 : Blo 706319 1595861 := bbase (se 7 (by rfl) ⟨18701, by rfl⟩ : syracuseStep 1595861 = 37403) (by norm_num)
theorem B4544981 : Blo 706319 4544981 := bbase (se 7 (by rfl) ⟨53261, by rfl⟩ : syracuseStep 4544981 = 106523) (by norm_num)
theorem B1595933 : Blo 706319 1595933 := bbase (se 3 (by rfl) ⟨299237, by rfl⟩ : syracuseStep 1595933 = 598475) (by norm_num)
theorem B1137181 : Blo 706319 1137181 := bbase (se 3 (by rfl) ⟨213221, by rfl⟩ : syracuseStep 1137181 = 426443) (by norm_num)
theorem B1596005 : Blo 706319 1596005 := bbase (se 4 (by rfl) ⟨149625, by rfl⟩ : syracuseStep 1596005 = 299251) (by norm_num)
theorem B1596077 : Blo 706319 1596077 := bbase (se 3 (by rfl) ⟨299264, by rfl⟩ : syracuseStep 1596077 = 598529) (by norm_num)
theorem B1596149 : Blo 706319 1596149 := bbase (se 5 (by rfl) ⟨74819, by rfl⟩ : syracuseStep 1596149 = 149639) (by norm_num)
theorem B1792813 : Blo 706319 1792813 := bbase (se 3 (by rfl) ⟨336152, by rfl⟩ : syracuseStep 1792813 = 672305) (by norm_num)
theorem B1596221 : Blo 706319 1596221 := bbase (se 3 (by rfl) ⟨299291, by rfl⟩ : syracuseStep 1596221 = 598583) (by norm_num)
theorem B1006453 : Blo 706319 1006453 := bbase (se 5 (by rfl) ⟨47177, by rfl⟩ : syracuseStep 1006453 = 94355) (by norm_num)
theorem B1596293 : Blo 706319 1596293 := bbase (se 4 (by rfl) ⟨149652, by rfl⟩ : syracuseStep 1596293 = 299305) (by norm_num)
theorem B1792925 : Blo 706319 1792925 := bbase (se 3 (by rfl) ⟨336173, by rfl⟩ : syracuseStep 1792925 = 672347) (by norm_num)
theorem B1137565 : Blo 706319 1137565 := bbase (se 3 (by rfl) ⟨213293, by rfl⟩ : syracuseStep 1137565 = 426587) (by norm_num)
theorem B1596365 : Blo 706319 1596365 := bbase (se 3 (by rfl) ⟨299318, by rfl⟩ : syracuseStep 1596365 = 598637) (by norm_num)
theorem B1596437 : Blo 706319 1596437 := bbase (se 6 (by rfl) ⟨37416, by rfl⟩ : syracuseStep 1596437 = 74833) (by norm_num)
theorem B1727525 : Blo 706319 1727525 := bbase (se 4 (by rfl) ⟨161955, by rfl⟩ : syracuseStep 1727525 = 323911) (by norm_num)
theorem B2874437 : Blo 706319 2874437 := bbase (se 4 (by rfl) ⟨269478, by rfl⟩ : syracuseStep 2874437 = 538957) (by norm_num)
theorem B1793117 : Blo 706319 1793117 := bbase (se 3 (by rfl) ⟨336209, by rfl⟩ : syracuseStep 1793117 = 672419) (by norm_num)
theorem B1596509 : Blo 706319 1596509 := bbase (se 3 (by rfl) ⟨299345, by rfl⟩ : syracuseStep 1596509 = 598691) (by norm_num)
theorem B1596581 : Blo 706319 1596581 := bbase (se 4 (by rfl) ⟨149679, by rfl⟩ : syracuseStep 1596581 = 299359) (by norm_num)
theorem B2022565 : Blo 706319 2022565 := bbase (se 4 (by rfl) ⟨189615, by rfl⟩ : syracuseStep 2022565 = 379231) (by norm_num)
theorem B1596653 : Blo 706319 1596653 := bbase (se 3 (by rfl) ⟨299372, by rfl⟩ : syracuseStep 1596653 = 598745) (by norm_num)
theorem B1596725 : Blo 706319 1596725 := bbase (se 5 (by rfl) ⟨74846, by rfl⟩ : syracuseStep 1596725 = 149693) (by norm_num)
theorem B3595589 : Blo 706319 3595589 := bbase (se 4 (by rfl) ⟨337086, by rfl⟩ : syracuseStep 3595589 = 674173) (by norm_num)
theorem B2022725 : Blo 706319 2022725 := bbase (se 4 (by rfl) ⟨189630, by rfl⟩ : syracuseStep 2022725 = 379261) (by norm_num)
theorem B1596797 : Blo 706319 1596797 := bbase (se 3 (by rfl) ⟨299399, by rfl⟩ : syracuseStep 1596797 = 598799) (by norm_num)
theorem B1793461 : Blo 706319 1793461 := bbase (se 5 (by rfl) ⟨84068, by rfl⟩ : syracuseStep 1793461 = 168137) (by norm_num)
theorem B1596869 : Blo 706319 1596869 := bbase (se 4 (by rfl) ⟨149706, by rfl⟩ : syracuseStep 1596869 = 299413) (by norm_num)
theorem B1596941 : Blo 706319 1596941 := bbase (se 3 (by rfl) ⟨299426, by rfl⟩ : syracuseStep 1596941 = 598853) (by norm_num)
theorem B1793573 : Blo 706319 1793573 := bbase (se 4 (by rfl) ⟨168147, by rfl⟩ : syracuseStep 1793573 = 336295) (by norm_num)
theorem B1597013 : Blo 706319 1597013 := bbase (se 8 (by rfl) ⟨9357, by rfl⟩ : syracuseStep 1597013 = 18715) (by norm_num)
theorem B1007245 : Blo 706319 1007245 := bbase (se 3 (by rfl) ⟨188858, by rfl⟩ : syracuseStep 1007245 = 377717) (by norm_num)
theorem B3399317 : Blo 706319 3399317 := bbase (se 6 (by rfl) ⟨79671, by rfl⟩ : syracuseStep 3399317 = 159343) (by norm_num)
theorem B1597085 : Blo 706319 1597085 := bbase (se 3 (by rfl) ⟨299453, by rfl⟩ : syracuseStep 1597085 = 598907) (by norm_num)
theorem B1793765 : Blo 706319 1793765 := bbase (se 4 (by rfl) ⟨168165, by rfl⟩ : syracuseStep 1793765 = 336331) (by norm_num)
theorem B1597157 : Blo 706319 1597157 := bbase (se 4 (by rfl) ⟨149733, by rfl⟩ : syracuseStep 1597157 = 299467) (by norm_num)
theorem B1597229 : Blo 706319 1597229 := bbase (se 3 (by rfl) ⟨299480, by rfl⟩ : syracuseStep 1597229 = 598961) (by norm_num)
theorem B3399509 : Blo 706319 3399509 := bbase (se 9 (by rfl) ⟨9959, by rfl⟩ : syracuseStep 3399509 = 19919) (by norm_num)
theorem B1597301 : Blo 706319 1597301 := bbase (se 5 (by rfl) ⟨74873, by rfl⟩ : syracuseStep 1597301 = 149747) (by norm_num)
theorem B1597373 : Blo 706319 1597373 := bbase (se 3 (by rfl) ⟨299507, by rfl⟩ : syracuseStep 1597373 = 599015) (by norm_num)
theorem B2383829 : Blo 706319 2383829 := bbase (se 7 (by rfl) ⟨27935, by rfl⟩ : syracuseStep 2383829 = 55871) (by norm_num)
theorem B6119381 : Blo 706319 6119381 := bbase (se 7 (by rfl) ⟨71711, by rfl⟩ : syracuseStep 6119381 = 143423) (by norm_num)
theorem B1007581 : Blo 706319 1007581 := bbase (se 3 (by rfl) ⟨188921, by rfl⟩ : syracuseStep 1007581 = 377843) (by norm_num)
theorem B1597445 : Blo 706319 1597445 := bbase (se 4 (by rfl) ⟨149760, by rfl⟩ : syracuseStep 1597445 = 299521) (by norm_num)
theorem B1794109 : Blo 706319 1794109 := bbase (se 3 (by rfl) ⟨336395, by rfl⟩ : syracuseStep 1794109 = 672791) (by norm_num)
theorem B1597517 : Blo 706319 1597517 := bbase (se 3 (by rfl) ⟨299534, by rfl⟩ : syracuseStep 1597517 = 599069) (by norm_num)
theorem B1597589 : Blo 706319 1597589 := bbase (se 6 (by rfl) ⟨37443, by rfl⟩ : syracuseStep 1597589 = 74887) (by norm_num)
theorem B1794221 : Blo 706319 1794221 := bbase (se 3 (by rfl) ⟨336416, by rfl⟩ : syracuseStep 1794221 = 672833) (by norm_num)
theorem B1007797 : Blo 706319 1007797 := bbase (se 5 (by rfl) ⟨47240, by rfl⟩ : syracuseStep 1007797 = 94481) (by norm_num)
theorem B1597661 : Blo 706319 1597661 := bbase (se 3 (by rfl) ⟨299561, by rfl⟩ : syracuseStep 1597661 = 599123) (by norm_num)
theorem B2547989 : Blo 706319 2547989 := bbase (se 6 (by rfl) ⟨59718, by rfl⟩ : syracuseStep 2547989 = 119437) (by norm_num)
theorem B1597733 : Blo 706319 1597733 := bbase (se 4 (by rfl) ⟨149787, by rfl⟩ : syracuseStep 1597733 = 299575) (by norm_num)
theorem B1433909 : Blo 706319 1433909 := bbase (se 5 (by rfl) ⟨67214, by rfl⟩ : syracuseStep 1433909 = 134429) (by norm_num)
theorem B1794413 : Blo 706319 1794413 := bbase (se 3 (by rfl) ⟨336452, by rfl⟩ : syracuseStep 1794413 = 672905) (by norm_num)
theorem B1597805 : Blo 706319 1597805 := bbase (se 3 (by rfl) ⟨299588, by rfl⟩ : syracuseStep 1597805 = 599177) (by norm_num)
theorem B2384261 : Blo 706319 2384261 := bbase (se 4 (by rfl) ⟨223524, by rfl⟩ : syracuseStep 2384261 = 447049) (by norm_num)
theorem B1597877 : Blo 706319 1597877 := bbase (se 5 (by rfl) ⟨74900, by rfl⟩ : syracuseStep 1597877 = 149801) (by norm_num)
theorem B1597949 : Blo 706319 1597949 := bbase (se 3 (by rfl) ⟨299615, by rfl⟩ : syracuseStep 1597949 = 599231) (by norm_num)
theorem B1008173 : Blo 706319 1008173 := bbase (se 3 (by rfl) ⟨189032, by rfl⟩ : syracuseStep 1008173 = 378065) (by norm_num)
theorem B2548277 : Blo 706319 2548277 := bbase (se 5 (by rfl) ⟨119450, by rfl⟩ : syracuseStep 2548277 = 238901) (by norm_num)
theorem B1598021 : Blo 706319 1598021 := bbase (se 4 (by rfl) ⟨149814, by rfl⟩ : syracuseStep 1598021 = 299629) (by norm_num)
theorem B1598093 : Blo 706319 1598093 := bbase (se 3 (by rfl) ⟨299642, by rfl⟩ : syracuseStep 1598093 = 599285) (by norm_num)
theorem B1794757 : Blo 706319 1794757 := bbase (se 4 (by rfl) ⟨168258, by rfl⟩ : syracuseStep 1794757 = 336517) (by norm_num)
theorem B1598165 : Blo 706319 1598165 := bbase (se 7 (by rfl) ⟨18728, by rfl⟩ : syracuseStep 1598165 = 37457) (by norm_num)
theorem B2384693 : Blo 706319 2384693 := bbase (se 5 (by rfl) ⟨111782, by rfl⟩ : syracuseStep 2384693 = 223565) (by norm_num)
theorem B6054709 : Blo 706319 6054709 := bbase (se 5 (by rfl) ⟨283814, by rfl⟩ : syracuseStep 6054709 = 567629) (by norm_num)
theorem B1794869 : Blo 706319 1794869 := bbase (se 5 (by rfl) ⟨84134, by rfl⟩ : syracuseStep 1794869 = 168269) (by norm_num)
theorem B1074053 : Blo 706319 1074053 := bbase (se 4 (by rfl) ⟨100692, by rfl⟩ : syracuseStep 1074053 = 201385) (by norm_num)
theorem B1795061 : Blo 706319 1795061 := bbase (se 5 (by rfl) ⟨84143, by rfl⟩ : syracuseStep 1795061 = 168287) (by norm_num)
theorem B10183765 : Blo 706319 10183765 := bbase (se 8 (by rfl) ⟨59670, by rfl⟩ : syracuseStep 10183765 = 119341) (by norm_num)
theorem B1729669 : Blo 706319 1729669 := bbase (se 4 (by rfl) ⟨162156, by rfl⟩ : syracuseStep 1729669 = 324313) (by norm_num)
theorem B2385125 : Blo 706319 2385125 := bbase (se 4 (by rfl) ⟨223605, by rfl⟩ : syracuseStep 2385125 = 447211) (by norm_num)
theorem B1795405 : Blo 706319 1795405 := bbase (se 3 (by rfl) ⟨336638, by rfl⟩ : syracuseStep 1795405 = 673277) (by norm_num)
theorem B1434989 : Blo 706319 1434989 := bbase (se 3 (by rfl) ⟨269060, by rfl⟩ : syracuseStep 1434989 = 538121) (by norm_num)
theorem B1795517 : Blo 706319 1795517 := bbase (se 3 (by rfl) ⟨336659, by rfl⟩ : syracuseStep 1795517 = 673319) (by norm_num)
theorem B1795709 : Blo 706319 1795709 := bbase (se 3 (by rfl) ⟨336695, by rfl⟩ : syracuseStep 1795709 = 673391) (by norm_num)
theorem B1697429 : Blo 706319 1697429 := bbase (se 6 (by rfl) ⟨39783, by rfl⟩ : syracuseStep 1697429 = 79567) (by norm_num)
theorem B2385557 : Blo 706319 2385557 := bbase (se 6 (by rfl) ⟨55911, by rfl⟩ : syracuseStep 2385557 = 111823) (by norm_num)
theorem B4023989 : Blo 706319 4023989 := bbase (se 5 (by rfl) ⟨188624, by rfl⟩ : syracuseStep 4023989 = 377249) (by norm_num)
theorem B3401605 : Blo 706319 3401605 := bbase (se 4 (by rfl) ⟨318900, by rfl⟩ : syracuseStep 3401605 = 637801) (by norm_num)
theorem B1009597 : Blo 706319 1009597 := bbase (se 3 (by rfl) ⟨189299, by rfl⟩ : syracuseStep 1009597 = 378599) (by norm_num)
theorem B1796053 : Blo 706319 1796053 := bbase (se 7 (by rfl) ⟨21047, by rfl⟩ : syracuseStep 1796053 = 42095) (by norm_num)
theorem B2385989 : Blo 706319 2385989 := bbase (se 4 (by rfl) ⟨223686, by rfl⟩ : syracuseStep 2385989 = 447373) (by norm_num)
theorem B1796165 : Blo 706319 1796165 := bbase (se 4 (by rfl) ⟨168390, by rfl⟩ : syracuseStep 1796165 = 336781) (by norm_num)
theorem B1796357 : Blo 706319 1796357 := bbase (se 4 (by rfl) ⟨168408, by rfl⟩ : syracuseStep 1796357 = 336817) (by norm_num)
theorem B2386421 : Blo 706319 2386421 := bbase (se 5 (by rfl) ⟨111863, by rfl⟩ : syracuseStep 2386421 = 223727) (by norm_num)
theorem B1010189 : Blo 706319 1010189 := bbase (se 3 (by rfl) ⟨189410, by rfl⟩ : syracuseStep 1010189 = 378821) (by norm_num)
theorem B1436221 : Blo 706319 1436221 := bbase (se 3 (by rfl) ⟨269291, by rfl⟩ : syracuseStep 1436221 = 538583) (by norm_num)
theorem B2878037 : Blo 706319 2878037 := bbase (se 8 (by rfl) ⟨16863, by rfl⟩ : syracuseStep 2878037 = 33727) (by norm_num)
theorem B1010269 : Blo 706319 1010269 := bbase (se 3 (by rfl) ⟨189425, by rfl⟩ : syracuseStep 1010269 = 378851) (by norm_num)
theorem B1796701 : Blo 706319 1796701 := bbase (se 3 (by rfl) ⟨336881, by rfl⟩ : syracuseStep 1796701 = 673763) (by norm_num)
theorem B1534573 : Blo 706319 1534573 := bbase (se 3 (by rfl) ⟨287732, by rfl⟩ : syracuseStep 1534573 = 575465) (by norm_num)
theorem B1796813 : Blo 706319 1796813 := bbase (se 3 (by rfl) ⟨336902, by rfl⟩ : syracuseStep 1796813 = 673805) (by norm_num)
theorem B1010389 : Blo 706319 1010389 := bbase (se 7 (by rfl) ⟨11840, by rfl⟩ : syracuseStep 1010389 = 23681) (by norm_num)
theorem B6056693 : Blo 706319 6056693 := bbase (se 5 (by rfl) ⟨283907, by rfl⟩ : syracuseStep 6056693 = 567815) (by norm_num)
theorem B1010485 : Blo 706319 1010485 := bbase (se 5 (by rfl) ⟨47366, by rfl⟩ : syracuseStep 1010485 = 94733) (by norm_num)
theorem B4025173 : Blo 706319 4025173 := bbase (se 9 (by rfl) ⟨11792, by rfl⟩ : syracuseStep 4025173 = 23585) (by norm_num)
theorem B1797005 : Blo 706319 1797005 := bbase (se 3 (by rfl) ⟨336938, by rfl⟩ : syracuseStep 1797005 = 673877) (by norm_num)
theorem B14740373 : Blo 706319 14740373 := bbase (se 6 (by rfl) ⟨345477, by rfl⟩ : syracuseStep 14740373 = 690955) (by norm_num)
theorem B2386853 : Blo 706319 2386853 := bbase (se 4 (by rfl) ⟨223767, by rfl⟩ : syracuseStep 2386853 = 447535) (by norm_num)
theorem B1797349 : Blo 706319 1797349 := bbase (se 4 (by rfl) ⟨168501, by rfl⟩ : syracuseStep 1797349 = 337003) (by norm_num)
theorem B1535269 : Blo 706319 1535269 := bbase (se 4 (by rfl) ⟨143931, by rfl⟩ : syracuseStep 1535269 = 287863) (by norm_num)
theorem B1010981 : Blo 706319 1010981 := bbase (se 4 (by rfl) ⟨94779, by rfl⟩ : syracuseStep 1010981 = 189559) (by norm_num)
theorem B2387285 : Blo 706319 2387285 := bbase (se 11 (by rfl) ⟨1748, by rfl⟩ : syracuseStep 2387285 = 3497) (by norm_num)
theorem B1797461 : Blo 706319 1797461 := bbase (se 11 (by rfl) ⟨1316, by rfl⟩ : syracuseStep 1797461 = 2633) (by norm_num)
theorem B1863109 : Blo 706319 1863109 := bbase (se 4 (by rfl) ⟨174666, by rfl⟩ : syracuseStep 1863109 = 349333) (by norm_num)
theorem B2682341 : Blo 706319 2682341 := bbase (se 4 (by rfl) ⟨251469, by rfl⟩ : syracuseStep 2682341 = 502939) (by norm_num)
theorem B1797653 : Blo 706319 1797653 := bbase (se 6 (by rfl) ⟨42132, by rfl⟩ : syracuseStep 1797653 = 84265) (by norm_num)
theorem B2551333 : Blo 706319 2551333 := bbase (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) (by norm_num)
theorem B25882325 : Blo 706319 25882325 := bbase (se 7 (by rfl) ⟨303308, by rfl⟩ : syracuseStep 25882325 = 606617) (by norm_num)
theorem B716533 : Blo 706319 716533 := bbase (se 5 (by rfl) ⟨33587, by rfl⟩ : syracuseStep 716533 = 67175) (by norm_num)
theorem B2682629 : Blo 706319 2682629 := bbase (se 4 (by rfl) ⟨251496, by rfl⟩ : syracuseStep 2682629 = 502993) (by norm_num)
theorem B2387717 : Blo 706319 2387717 := bbase (se 4 (by rfl) ⟨223848, by rfl⟩ : syracuseStep 2387717 = 447697) (by norm_num)
theorem B2879333 : Blo 706319 2879333 := bbase (se 4 (by rfl) ⟨269937, by rfl⟩ : syracuseStep 2879333 = 539875) (by norm_num)
theorem B1797997 : Blo 706319 1797997 := bbase (se 3 (by rfl) ⟨337124, by rfl⟩ : syracuseStep 1797997 = 674249) (by norm_num)
theorem B5369813 : Blo 706319 5369813 := bbase (se 7 (by rfl) ⟨62927, by rfl⟩ : syracuseStep 5369813 = 125855) (by norm_num)
theorem B716833 : Blo 706319 716833 := bbase (se 2 (by rfl) ⟨268812, by rfl⟩ : syracuseStep 716833 = 537625) (by norm_num)
theorem B2388149 : Blo 706319 2388149 := bbase (se 5 (by rfl) ⟨111944, by rfl⟩ : syracuseStep 2388149 = 223889) (by norm_num)
theorem B1274125 : Blo 706319 1274125 := bbase (se 3 (by rfl) ⟨238898, by rfl⟩ : syracuseStep 1274125 = 477797) (by norm_num)
theorem B1438013 : Blo 706319 1438013 := bbase (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) (by norm_num)
theorem B1438109 : Blo 706319 1438109 := bbase (se 3 (by rfl) ⟨269645, by rfl⟩ : syracuseStep 1438109 = 539291) (by norm_num)
theorem B1700389 : Blo 706319 1700389 := bbase (se 4 (by rfl) ⟨159411, by rfl⟩ : syracuseStep 1700389 = 318823) (by norm_num)
theorem B2388581 : Blo 706319 2388581 := bbase (se 4 (by rfl) ⟨223929, by rfl⟩ : syracuseStep 2388581 = 447859) (by norm_num)
theorem B7664341 : Blo 706319 7664341 := bbase (se 7 (by rfl) ⟨89816, by rfl⟩ : syracuseStep 7664341 = 179633) (by norm_num)
theorem B2585317 : Blo 706319 2585317 := bbase (se 4 (by rfl) ⟨242373, by rfl⟩ : syracuseStep 2585317 = 484747) (by norm_num)
theorem B1700581 : Blo 706319 1700581 := bbase (se 4 (by rfl) ⟨159429, by rfl⟩ : syracuseStep 1700581 = 318859) (by norm_num)
theorem B1700621 : Blo 706319 1700621 := bbase (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) (by norm_num)
theorem B848657 : Blo 706319 848657 := bbase (se 2 (by rfl) ⟨318246, by rfl⟩ : syracuseStep 848657 = 636493) (by norm_num)
theorem B4027157 : Blo 706319 4027157 := bbase (se 6 (by rfl) ⟨94386, by rfl⟩ : syracuseStep 4027157 = 188773) (by norm_num)
theorem B1078157 : Blo 706319 1078157 := bbase (se 3 (by rfl) ⟨202154, by rfl⟩ : syracuseStep 1078157 = 404309) (by norm_num)
theorem B2683813 : Blo 706319 2683813 := bbase (se 4 (by rfl) ⟨251607, by rfl⟩ : syracuseStep 2683813 = 503215) (by norm_num)
theorem B848917 : Blo 706319 848917 := bbase (se 6 (by rfl) ⟨19896, by rfl⟩ : syracuseStep 848917 = 39793) (by norm_num)
theorem B2389013 : Blo 706319 2389013 := bbase (se 6 (by rfl) ⟨55992, by rfl⟩ : syracuseStep 2389013 = 111985) (by norm_num)
theorem B1700909 : Blo 706319 1700909 := bbase (se 3 (by rfl) ⟨318920, by rfl⟩ : syracuseStep 1700909 = 637841) (by norm_num)
theorem B1274933 : Blo 706319 1274933 := bbase (se 5 (by rfl) ⟨59762, by rfl⟩ : syracuseStep 1274933 = 119525) (by norm_num)
theorem B1635509 : Blo 706319 1635509 := bbase (se 5 (by rfl) ⟨76664, by rfl⟩ : syracuseStep 1635509 = 153329) (by norm_num)
theorem B849109 : Blo 706319 849109 := bbase (se 7 (by rfl) ⟨9950, by rfl⟩ : syracuseStep 849109 = 19901) (by norm_num)
theorem B2684117 : Blo 706319 2684117 := bbase (se 7 (by rfl) ⟨31454, by rfl⟩ : syracuseStep 2684117 = 62909) (by norm_num)
theorem B849133 : Blo 706319 849133 := bbase (se 3 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 849133 = 318425) (by norm_num)
theorem B849137 : Blo 706319 849137 := bbase (se 2 (by rfl) ⟨318426, by rfl⟩ : syracuseStep 849137 = 636853) (by norm_num)
theorem B4846837 : Blo 706319 4846837 := bbase (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) (by norm_num)
theorem B2389445 : Blo 706319 2389445 := bbase (se 4 (by rfl) ⟨224010, by rfl⟩ : syracuseStep 2389445 = 448021) (by norm_num)
theorem B1209821 : Blo 706319 1209821 := bbase (se 3 (by rfl) ⟨226841, by rfl⟩ : syracuseStep 1209821 = 453683) (by norm_num)
theorem B718309 : Blo 706319 718309 := bbase (se 4 (by rfl) ⟨67341, by rfl⟩ : syracuseStep 718309 = 134683) (by norm_num)
theorem B1340965 : Blo 706319 1340965 := bbase (se 4 (by rfl) ⟨125715, by rfl⟩ : syracuseStep 1340965 = 251431) (by norm_num)
theorem B5174837 : Blo 706319 5174837 := bbase (se 5 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 5174837 = 485141) (by norm_num)
theorem B1275509 : Blo 706319 1275509 := bbase (se 5 (by rfl) ⟨59789, by rfl⟩ : syracuseStep 1275509 = 119579) (by norm_num)
theorem B3405509 : Blo 706319 3405509 := bbase (se 4 (by rfl) ⟨319266, by rfl⟩ : syracuseStep 3405509 = 638533) (by norm_num)
theorem B849637 : Blo 706319 849637 := bbase (se 4 (by rfl) ⟨79653, by rfl⟩ : syracuseStep 849637 = 159307) (by norm_num)
theorem B849733 : Blo 706319 849733 := bbase (se 4 (by rfl) ⟨79662, by rfl⟩ : syracuseStep 849733 = 159325) (by norm_num)
theorem B1341269 : Blo 706319 1341269 := bbase (se 9 (by rfl) ⟨3929, by rfl⟩ : syracuseStep 1341269 = 7859) (by norm_num)
theorem B2389877 : Blo 706319 2389877 := bbase (se 5 (by rfl) ⟨112025, by rfl⟩ : syracuseStep 2389877 = 224051) (by norm_num)
theorem B718889 : Blo 706319 718889 := bbase (se 2 (by rfl) ⟨269583, by rfl⟩ : syracuseStep 718889 = 539167) (by norm_num)
theorem B2390309 : Blo 706319 2390309 := bbase (se 4 (by rfl) ⟨224091, by rfl⟩ : syracuseStep 2390309 = 448183) (by norm_num)
theorem B1276301 : Blo 706319 1276301 := bbase (se 3 (by rfl) ⟨239306, by rfl⟩ : syracuseStep 1276301 = 478613) (by norm_num)
theorem B719249 : Blo 706319 719249 := bbase (se 2 (by rfl) ⟨269718, by rfl⟩ : syracuseStep 719249 = 539437) (by norm_num)
theorem B1276445 : Blo 706319 1276445 := bbase (se 3 (by rfl) ⟨239333, by rfl⟩ : syracuseStep 1276445 = 478667) (by norm_num)
theorem B1342021 : Blo 706319 1342021 := bbase (se 4 (by rfl) ⟨125814, by rfl⟩ : syracuseStep 1342021 = 251629) (by norm_num)
theorem B1079909 : Blo 706319 1079909 := bbase (se 4 (by rfl) ⟨101241, by rfl⟩ : syracuseStep 1079909 = 202483) (by norm_num)
theorem B1342165 : Blo 706319 1342165 := bbase (se 7 (by rfl) ⟨15728, by rfl⟩ : syracuseStep 1342165 = 31457) (by norm_num)
theorem B2390741 : Blo 706319 2390741 := bbase (se 7 (by rfl) ⟨28016, by rfl⟩ : syracuseStep 2390741 = 56033) (by norm_num)
theorem B850709 : Blo 706319 850709 := bbase (se 6 (by rfl) ⟨19938, by rfl⟩ : syracuseStep 850709 = 39877) (by norm_num)
theorem B1342325 : Blo 706319 1342325 := bbase (se 5 (by rfl) ⟨62921, by rfl⟩ : syracuseStep 1342325 = 125843) (by norm_num)
theorem B719785 : Blo 706319 719785 := bbase (se 2 (by rfl) ⟨269919, by rfl⟩ : syracuseStep 719785 = 539839) (by norm_num)
theorem B4029365 : Blo 706319 4029365 := bbase (se 5 (by rfl) ⟨188876, by rfl⟩ : syracuseStep 4029365 = 377753) (by norm_num)
theorem B1342469 : Blo 706319 1342469 := bbase (se 4 (by rfl) ⟨125856, by rfl⟩ : syracuseStep 1342469 = 251713) (by norm_num)
theorem B2391173 : Blo 706319 2391173 := bbase (se 4 (by rfl) ⟨224172, by rfl⟩ : syracuseStep 2391173 = 448345) (by norm_num)
theorem B851185 : Blo 706319 851185 := bbase (se 2 (by rfl) ⟨319194, by rfl⟩ : syracuseStep 851185 = 638389) (by norm_num)
theorem B851213 : Blo 706319 851213 := bbase (se 3 (by rfl) ⟨159602, by rfl⟩ : syracuseStep 851213 = 319205) (by norm_num)
theorem B2686229 : Blo 706319 2686229 := bbase (se 6 (by rfl) ⟨62958, by rfl⟩ : syracuseStep 2686229 = 125917) (by norm_num)
theorem B1342757 : Blo 706319 1342757 := bbase (se 4 (by rfl) ⟨125883, by rfl⟩ : syracuseStep 1342757 = 251767) (by norm_num)
theorem B14548373 : Blo 706319 14548373 := bbase (se 6 (by rfl) ⟨340977, by rfl⟩ : syracuseStep 14548373 = 681955) (by norm_num)
theorem B1342909 : Blo 706319 1342909 := bbase (se 3 (by rfl) ⟨251795, by rfl⟩ : syracuseStep 1342909 = 503591) (by norm_num)
theorem B851401 : Blo 706319 851401 := bbase (se 2 (by rfl) ⟨319275, by rfl⟩ : syracuseStep 851401 = 638551) (by norm_num)
theorem B2686517 : Blo 706319 2686517 := bbase (se 5 (by rfl) ⟨125930, by rfl⟩ : syracuseStep 2686517 = 251861) (by norm_num)
theorem B2391605 : Blo 706319 2391605 := bbase (se 5 (by rfl) ⟨112106, by rfl⟩ : syracuseStep 2391605 = 224213) (by norm_num)
theorem B851521 : Blo 706319 851521 := bbase (se 2 (by rfl) ⟨319320, by rfl⟩ : syracuseStep 851521 = 638641) (by norm_num)
theorem B1343213 : Blo 706319 1343213 := bbase (se 3 (by rfl) ⟨251852, by rfl⟩ : syracuseStep 1343213 = 503705) (by norm_num)
theorem B2392037 : Blo 706319 2392037 := bbase (se 4 (by rfl) ⟨224253, by rfl⟩ : syracuseStep 2392037 = 448507) (by norm_num)
theorem B2392145 : Blo 706319 2392145 := bstep (se 2 (by rfl) ⟨897054, by rfl⟩ : syracuseStep 2392145 = 1794109) B1794109
theorem B52396145 : Blo 706319 52396145 := bstep (se 2 (by rfl) ⟨19648554, by rfl⟩ : syracuseStep 52396145 = 39297109) B39297109
theorem B1147073 : Blo 706319 1147073 := bstep (se 2 (by rfl) ⟨430152, by rfl⟩ : syracuseStep 1147073 = 860305) B860305
theorem B1343729 : Blo 706319 1343729 := bstep (se 2 (by rfl) ⟨503898, by rfl⟩ : syracuseStep 1343729 = 1007797) B1007797
theorem B2130275 : Blo 706319 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B2556323 : Blo 706319 2556323 := bstep (se 1 (by rfl) ⟨1917242, by rfl⟩ : syracuseStep 2556323 = 3834485) B3834485
theorem B5439941 : Blo 706319 5439941 := bstep (se 4 (by rfl) ⟨509994, by rfl⟩ : syracuseStep 5439941 = 1019989) B1019989
theorem B2392685 : Blo 706319 2392685 := bstep (se 3 (by rfl) ⟨448628, by rfl⟩ : syracuseStep 2392685 = 897257) B897257
theorem B2392739 : Blo 706319 2392739 := bstep (se 1 (by rfl) ⟨1794554, by rfl⟩ : syracuseStep 2392739 = 3589109) B3589109
theorem B6128453 : Blo 706319 6128453 := bstep (se 4 (by rfl) ⟨574542, by rfl⟩ : syracuseStep 6128453 = 1149085) B1149085
theorem B3834701 : Blo 706319 3834701 := bstep (se 3 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 3834701 = 1438013) B1438013
theorem B2393009 : Blo 706319 2393009 := bstep (se 2 (by rfl) ⟨897378, by rfl⟩ : syracuseStep 2393009 = 1794757) B1794757
theorem B1344451 : Blo 706319 1344451 := bstep (se 1 (by rfl) ⟨1008338, by rfl⟩ : syracuseStep 1344451 = 2016677) B2016677
theorem B1278947 : Blo 706319 1278947 := bstep (se 1 (by rfl) ⟨959210, by rfl⟩ : syracuseStep 1278947 = 1918421) B1918421
theorem B2426033 : Blo 706319 2426033 := bstep (se 2 (by rfl) ⟨909762, by rfl⟩ : syracuseStep 2426033 = 1819525) B1819525
theorem B2458925 : Blo 706319 2458925 := bstep (se 3 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 2458925 = 922097) B922097
theorem B755011 : Blo 706319 755011 := bstep (se 1 (by rfl) ⟨566258, by rfl⟩ : syracuseStep 755011 = 1132517) B1132517
theorem B1344899 : Blo 706319 1344899 := bstep (se 1 (by rfl) ⟨1008674, by rfl⟩ : syracuseStep 1344899 = 2017349) B2017349
theorem B2688461 : Blo 706319 2688461 := bstep (se 3 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 2688461 = 1008173) B1008173
theorem B2393549 : Blo 706319 2393549 := bstep (se 3 (by rfl) ⟨448790, by rfl⟩ : syracuseStep 2393549 = 897581) B897581
theorem B2393603 : Blo 706319 2393603 := bstep (se 1 (by rfl) ⟨1795202, by rfl⟩ : syracuseStep 2393603 = 3590405) B3590405
theorem B2721293 : Blo 706319 2721293 := bstep (se 3 (by rfl) ⟨510242, by rfl⟩ : syracuseStep 2721293 = 1020485) B1020485
theorem B1345187 : Blo 706319 1345187 := bstep (se 1 (by rfl) ⟨1008890, by rfl⟩ : syracuseStep 1345187 = 2017781) B2017781
theorem B2393873 : Blo 706319 2393873 := bstep (se 2 (by rfl) ⟨897702, by rfl⟩ : syracuseStep 2393873 = 1795405) B1795405
theorem B2426755 : Blo 706319 2426755 := bstep (se 1 (by rfl) ⟨1820066, by rfl⟩ : syracuseStep 2426755 = 3640133) B3640133
theorem B5736419 : Blo 706319 5736419 := bstep (se 1 (by rfl) ⟨4302314, by rfl⟩ : syracuseStep 5736419 = 8604629) B8604629
theorem B2263085 : Blo 706319 2263085 := bstep (se 3 (by rfl) ⟨424328, by rfl⟩ : syracuseStep 2263085 = 848657) B848657
theorem B1509475 : Blo 706319 1509475 := bstep (se 1 (by rfl) ⟨1132106, by rfl⟩ : syracuseStep 1509475 = 2264213) B2264213
theorem B2394413 : Blo 706319 2394413 := bstep (se 3 (by rfl) ⟨448952, by rfl⟩ : syracuseStep 2394413 = 897905) B897905
theorem B2394467 : Blo 706319 2394467 := bstep (se 1 (by rfl) ⟨1795850, by rfl⟩ : syracuseStep 2394467 = 3591701) B3591701
theorem B1706339 : Blo 706319 1706339 := bstep (se 1 (by rfl) ⟨1279754, by rfl⟩ : syracuseStep 1706339 = 2559509) B2559509
theorem B1935917 : Blo 706319 1935917 := bstep (se 3 (by rfl) ⟨362984, by rfl⟩ : syracuseStep 1935917 = 725969) B725969
theorem B756275 : Blo 706319 756275 := bstep (se 1 (by rfl) ⟨567206, by rfl⟩ : syracuseStep 756275 = 1134413) B1134413
theorem B1346129 : Blo 706319 1346129 := bstep (se 2 (by rfl) ⟨504798, by rfl⟩ : syracuseStep 1346129 = 1009597) B1009597
theorem B1149553 : Blo 706319 1149553 := bstep (se 2 (by rfl) ⟨431082, by rfl⟩ : syracuseStep 1149553 = 862165) B862165
theorem B2394737 : Blo 706319 2394737 := bstep (se 2 (by rfl) ⟨898026, by rfl⟩ : syracuseStep 2394737 = 1796053) B1796053
theorem B4033421 : Blo 706319 4033421 := bstep (se 3 (by rfl) ⟨756266, by rfl⟩ : syracuseStep 4033421 = 1512533) B1512533
theorem B6818701 : Blo 706319 6818701 := bstep (se 3 (by rfl) ⟨1278506, by rfl⟩ : syracuseStep 6818701 = 2557013) B2557013
theorem B1510321 : Blo 706319 1510321 := bstep (se 2 (by rfl) ⟨566370, by rfl⟩ : syracuseStep 1510321 = 1132741) B1132741
theorem B4361357 : Blo 706319 4361357 := bstep (se 3 (by rfl) ⟨817754, by rfl⟩ : syracuseStep 4361357 = 1635509) B1635509
theorem B2395277 : Blo 706319 2395277 := bstep (se 3 (by rfl) ⟨449114, by rfl⟩ : syracuseStep 2395277 = 898229) B898229
theorem B2395331 : Blo 706319 2395331 := bstep (se 1 (by rfl) ⟨1796498, by rfl⟩ : syracuseStep 2395331 = 3592997) B3592997
theorem B8064197 : Blo 706319 8064197 := bstep (se 4 (by rfl) ⟨756018, by rfl⟩ : syracuseStep 8064197 = 1512037) B1512037
theorem B757027 : Blo 706319 757027 := bstep (se 1 (by rfl) ⟨567770, by rfl⟩ : syracuseStep 757027 = 1135541) B1135541
theorem B2264365 : Blo 706319 2264365 := bstep (se 3 (by rfl) ⟨424568, by rfl⟩ : syracuseStep 2264365 = 849137) B849137
theorem B1347025 : Blo 706319 1347025 := bstep (se 2 (by rfl) ⟨505134, by rfl⟩ : syracuseStep 1347025 = 1010269) B1010269
theorem B2395601 : Blo 706319 2395601 := bstep (se 2 (by rfl) ⟨898350, by rfl⟩ : syracuseStep 2395601 = 1796701) B1796701
theorem B757283 : Blo 706319 757283 := bstep (se 1 (by rfl) ⟨567962, by rfl⟩ : syracuseStep 757283 = 1135925) B1135925
theorem B1347185 : Blo 706319 1347185 := bstep (se 2 (by rfl) ⟨505194, by rfl⟩ : syracuseStep 1347185 = 1010389) B1010389
theorem B2264867 : Blo 706319 2264867 := bstep (se 1 (by rfl) ⟨1698650, by rfl⟩ : syracuseStep 2264867 = 3397301) B3397301
theorem B3411811 : Blo 706319 3411811 := bstep (se 1 (by rfl) ⟨2558858, by rfl⟩ : syracuseStep 3411811 = 5117717) B5117717
theorem B2396141 : Blo 706319 2396141 := bstep (se 3 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 2396141 = 898553) B898553
theorem B1347587 : Blo 706319 1347587 := bstep (se 1 (by rfl) ⟨1010690, by rfl⟩ : syracuseStep 1347587 = 2021381) B2021381
theorem B2396195 : Blo 706319 2396195 := bstep (se 1 (by rfl) ⟨1797146, by rfl⟩ : syracuseStep 2396195 = 3594293) B3594293
theorem B7671989 : Blo 706319 7671989 := bstep (se 5 (by rfl) ⟨359624, by rfl⟩ : syracuseStep 7671989 = 719249) B719249
theorem B758035 : Blo 706319 758035 := bstep (se 1 (by rfl) ⟨568526, by rfl⟩ : syracuseStep 758035 = 1137053) B1137053
theorem B2691377 : Blo 706319 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B2396465 : Blo 706319 2396465 := bstep (se 2 (by rfl) ⟨898674, by rfl⟩ : syracuseStep 2396465 = 1797349) B1797349
theorem B4854115 : Blo 706319 4854115 := bstep (se 1 (by rfl) ⟨3640586, by rfl⟩ : syracuseStep 4854115 = 7281173) B7281173
theorem B3019427 : Blo 706319 3019427 := bstep (se 1 (by rfl) ⟨2264570, by rfl⟩ : syracuseStep 3019427 = 4529141) B4529141
theorem B8622773 : Blo 706319 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B2757361 : Blo 706319 2757361 := bstep (se 2 (by rfl) ⟨1034010, by rfl⟩ : syracuseStep 2757361 = 2068021) B2068021
theorem B1512209 : Blo 706319 1512209 := bstep (se 2 (by rfl) ⟨567078, by rfl⟩ : syracuseStep 1512209 = 1134157) B1134157
theorem B2397005 : Blo 706319 2397005 := bstep (se 3 (by rfl) ⟨449438, by rfl⟩ : syracuseStep 2397005 = 898877) B898877
theorem B2397059 : Blo 706319 2397059 := bstep (se 1 (by rfl) ⟨1797794, by rfl⟩ : syracuseStep 2397059 = 3595589) B3595589
theorem B1348483 : Blo 706319 1348483 := bstep (se 1 (by rfl) ⟨1011362, by rfl⟩ : syracuseStep 1348483 = 2022725) B2022725
theorem B3838853 : Blo 706319 3838853 := bstep (se 4 (by rfl) ⟨359892, by rfl⟩ : syracuseStep 3838853 = 719785) B719785
theorem B4035653 : Blo 706319 4035653 := bstep (se 4 (by rfl) ⟨378342, by rfl⟩ : syracuseStep 4035653 = 756685) B756685
theorem B2266211 : Blo 706319 2266211 := bstep (se 1 (by rfl) ⟨1699658, by rfl⟩ : syracuseStep 2266211 = 3399317) B3399317
theorem B2397329 : Blo 706319 2397329 := bstep (se 2 (by rfl) ⟨898998, by rfl⟩ : syracuseStep 2397329 = 1797997) B1797997
theorem B2692835 : Blo 706319 2692835 := bstep (se 1 (by rfl) ⟨2019626, by rfl⟩ : syracuseStep 2692835 = 4039253) B4039253
theorem B4036337 : Blo 706319 4036337 := bstep (se 2 (by rfl) ⟨1513626, by rfl⟩ : syracuseStep 4036337 = 3027253) B3027253
theorem B4855565 : Blo 706319 4855565 := bstep (se 3 (by rfl) ⟨910418, by rfl⟩ : syracuseStep 4855565 = 1820837) B1820837
theorem B1513507 : Blo 706319 1513507 := bstep (se 1 (by rfl) ⟨1135130, by rfl⟩ : syracuseStep 1513507 = 2270261) B2270261
theorem B2267185 : Blo 706319 2267185 := bstep (se 2 (by rfl) ⟨850194, by rfl⟩ : syracuseStep 2267185 = 1700389) B1700389
theorem B956659 : Blo 706319 956659 := bstep (se 1 (by rfl) ⟨717494, by rfl⟩ : syracuseStep 956659 = 1434989) B1434989
theorem B4921613 : Blo 706319 4921613 := bstep (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) B1845605
theorem B24254741 : Blo 706319 24254741 := bstep (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) B1136941
theorem B3447089 : Blo 706319 3447089 := bstep (se 2 (by rfl) ⟨1292658, by rfl⟩ : syracuseStep 3447089 = 2585317) B2585317
theorem B2267441 : Blo 706319 2267441 := bstep (se 2 (by rfl) ⟨850290, by rfl⟩ : syracuseStep 2267441 = 1700581) B1700581
theorem B3578417 : Blo 706319 3578417 := bstep (se 2 (by rfl) ⟨1341906, by rfl⟩ : syracuseStep 3578417 = 2683813) B2683813
theorem B4528709 : Blo 706319 4528709 := bstep (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) B849133
theorem B2693837 : Blo 706319 2693837 := bstep (se 3 (by rfl) ⟨505094, by rfl⟩ : syracuseStep 2693837 = 1010189) B1010189
theorem B6462449 : Blo 706319 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B4037795 : Blo 706319 4037795 := bstep (se 1 (by rfl) ⟨3028346, by rfl⟩ : syracuseStep 4037795 = 6056693) B6056693
theorem B1514737 : Blo 706319 1514737 := bstep (se 2 (by rfl) ⟨568026, by rfl⟩ : syracuseStep 1514737 = 1136053) B1136053
theorem B957745 : Blo 706319 957745 := bstep (se 2 (by rfl) ⟨359154, by rfl⟩ : syracuseStep 957745 = 718309) B718309
theorem B11672885 : Blo 706319 11672885 := bstep (se 5 (by rfl) ⟨547166, by rfl⟩ : syracuseStep 11672885 = 1094333) B1094333
theorem B2268557 : Blo 706319 2268557 := bstep (se 3 (by rfl) ⟨425354, by rfl⟩ : syracuseStep 2268557 = 850709) B850709
theorem B2039491 : Blo 706319 2039491 := bstep (se 1 (by rfl) ⟨1529618, by rfl⟩ : syracuseStep 2039491 = 3059237) B3059237
theorem B728899 : Blo 706319 728899 := bstep (se 1 (by rfl) ⟨546674, by rfl⟩ : syracuseStep 728899 = 1093349) B1093349
theorem B3579875 : Blo 706319 3579875 := bstep (se 1 (by rfl) ⟨2684906, by rfl⟩ : syracuseStep 3579875 = 5369813) B5369813
theorem B1515523 : Blo 706319 1515523 := bstep (se 1 (by rfl) ⟨1136642, by rfl⟩ : syracuseStep 1515523 = 2273285) B2273285
theorem B794659 : Blo 706319 794659 := bstep (se 1 (by rfl) ⟨595994, by rfl⟩ : syracuseStep 794659 = 1191989) B1191989
theorem B794803 : Blo 706319 794803 := bstep (se 1 (by rfl) ⟨596102, by rfl⟩ : syracuseStep 794803 = 1192205) B1192205
theorem B958739 : Blo 706319 958739 := bstep (se 1 (by rfl) ⟨719054, by rfl⟩ : syracuseStep 958739 = 1438109) B1438109
theorem B3023153 : Blo 706319 3023153 := bstep (se 2 (by rfl) ⟨1133682, by rfl⟩ : syracuseStep 3023153 = 2267365) B2267365
theorem B794947 : Blo 706319 794947 := bstep (se 1 (by rfl) ⟨596210, by rfl⟩ : syracuseStep 794947 = 1192421) B1192421
theorem B795091 : Blo 706319 795091 := bstep (se 1 (by rfl) ⟨596318, by rfl⟩ : syracuseStep 795091 = 1192637) B1192637
theorem B795235 : Blo 706319 795235 := bstep (se 1 (by rfl) ⟨596426, by rfl⟩ : syracuseStep 795235 = 1192853) B1192853
theorem B2269901 : Blo 706319 2269901 := bstep (se 3 (by rfl) ⟨425606, by rfl⟩ : syracuseStep 2269901 = 851213) B851213
theorem B1516241 : Blo 706319 1516241 := bstep (se 2 (by rfl) ⟨568590, by rfl⟩ : syracuseStep 1516241 = 1137181) B1137181
theorem B795379 : Blo 706319 795379 := bstep (se 1 (by rfl) ⟨596534, by rfl⟩ : syracuseStep 795379 = 1193069) B1193069
theorem B3580685 : Blo 706319 3580685 := bstep (se 3 (by rfl) ⟨671378, by rfl⟩ : syracuseStep 3580685 = 1342757) B1342757
theorem B2695949 : Blo 706319 2695949 := bstep (se 3 (by rfl) ⟨505490, by rfl⟩ : syracuseStep 2695949 = 1010981) B1010981
theorem B795523 : Blo 706319 795523 := bstep (se 1 (by rfl) ⟨596642, by rfl⟩ : syracuseStep 795523 = 1193285) B1193285
theorem B8070029 : Blo 706319 8070029 := bstep (se 3 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 8070029 = 3026261) B3026261
theorem B795667 : Blo 706319 795667 := bstep (se 1 (by rfl) ⟨596750, by rfl⟩ : syracuseStep 795667 = 1193501) B1193501
theorem B3449891 : Blo 706319 3449891 := bstep (se 1 (by rfl) ⟨2587418, by rfl⟩ : syracuseStep 3449891 = 5174837) B5174837
theorem B2270339 : Blo 706319 2270339 := bstep (se 1 (by rfl) ⟨1702754, by rfl⟩ : syracuseStep 2270339 = 3405509) B3405509
theorem B795811 : Blo 706319 795811 := bstep (se 1 (by rfl) ⟨596858, by rfl⟩ : syracuseStep 795811 = 1193717) B1193717
theorem B1516753 : Blo 706319 1516753 := bstep (se 2 (by rfl) ⟨568782, by rfl⟩ : syracuseStep 1516753 = 1137565) B1137565
theorem B894179 : Blo 706319 894179 := bstep (se 1 (by rfl) ⟨670634, by rfl⟩ : syracuseStep 894179 = 1341269) B1341269
theorem B795955 : Blo 706319 795955 := bstep (se 1 (by rfl) ⟨596966, by rfl⟩ : syracuseStep 795955 = 1193933) B1193933
theorem B796099 : Blo 706319 796099 := bstep (se 1 (by rfl) ⟨597074, by rfl⟩ : syracuseStep 796099 = 1194149) B1194149
theorem B2696753 : Blo 706319 2696753 := bstep (se 2 (by rfl) ⟨1011282, by rfl⟩ : syracuseStep 2696753 = 2022565) B2022565
theorem B796243 : Blo 706319 796243 := bstep (se 1 (by rfl) ⟨597182, by rfl⟩ : syracuseStep 796243 = 1194365) B1194365
theorem B4531909 : Blo 706319 4531909 := bstep (se 4 (by rfl) ⟨424866, by rfl⟩ : syracuseStep 4531909 = 849733) B849733
theorem B796387 : Blo 706319 796387 := bstep (se 1 (by rfl) ⟨597290, by rfl⟩ : syracuseStep 796387 = 1194581) B1194581
theorem B5383907 : Blo 706319 5383907 := bstep (se 1 (by rfl) ⟨4037930, by rfl⟩ : syracuseStep 5383907 = 8075861) B8075861
theorem B796531 : Blo 706319 796531 := bstep (se 1 (by rfl) ⟨597398, by rfl⟩ : syracuseStep 796531 = 1194797) B1194797
theorem B894883 : Blo 706319 894883 := bstep (se 1 (by rfl) ⟨671162, by rfl⟩ : syracuseStep 894883 = 1342325) B1342325
theorem B894979 : Blo 706319 894979 := bstep (se 1 (by rfl) ⟨671234, by rfl⟩ : syracuseStep 894979 = 1342469) B1342469
theorem B796675 : Blo 706319 796675 := bstep (se 1 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 796675 = 1195013) B1195013
theorem B5187725 : Blo 706319 5187725 := bstep (se 3 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 5187725 = 1945397) B1945397
theorem B796819 : Blo 706319 796819 := bstep (se 1 (by rfl) ⟨597614, by rfl⟩ : syracuseStep 796819 = 1195229) B1195229
theorem B796963 : Blo 706319 796963 := bstep (se 1 (by rfl) ⟨597722, by rfl⟩ : syracuseStep 796963 = 1195445) B1195445
theorem B4041029 : Blo 706319 4041029 := bstep (se 4 (by rfl) ⟨378846, by rfl⟩ : syracuseStep 4041029 = 757693) B757693
theorem B797107 : Blo 706319 797107 := bstep (se 1 (by rfl) ⟨597830, by rfl⟩ : syracuseStep 797107 = 1195661) B1195661
theorem B895475 : Blo 706319 895475 := bstep (se 1 (by rfl) ⟨671606, by rfl⟩ : syracuseStep 895475 = 1343213) B1343213
theorem B797251 : Blo 706319 797251 := bstep (se 1 (by rfl) ⟨597938, by rfl⟩ : syracuseStep 797251 = 1195877) B1195877
theorem B1059491 : Blo 706319 1059491 := bstep (se 1 (by rfl) ⟨794618, by rfl⟩ : syracuseStep 1059491 = 1589237) B1589237
theorem B1059521 : Blo 706319 1059521 := bstep (se 2 (by rfl) ⟨397320, by rfl⟩ : syracuseStep 1059521 = 794641) B794641
theorem B3025613 : Blo 706319 3025613 := bstep (se 3 (by rfl) ⟨567302, by rfl⟩ : syracuseStep 3025613 = 1134605) B1134605
theorem B1059539 : Blo 706319 1059539 := bstep (se 1 (by rfl) ⟨794654, by rfl⟩ : syracuseStep 1059539 = 1589309) B1589309
theorem B797395 : Blo 706319 797395 := bstep (se 1 (by rfl) ⟨598046, by rfl⟩ : syracuseStep 797395 = 1196093) B1196093
theorem B1059569 : Blo 706319 1059569 := bstep (se 2 (by rfl) ⟨397338, by rfl⟩ : syracuseStep 1059569 = 794677) B794677
theorem B4303601 : Blo 706319 4303601 := bstep (se 2 (by rfl) ⟨1613850, by rfl⟩ : syracuseStep 4303601 = 3227701) B3227701
theorem B1059587 : Blo 706319 1059587 := bstep (se 1 (by rfl) ⟨794690, by rfl⟩ : syracuseStep 1059587 = 1589381) B1589381
theorem B4041485 : Blo 706319 4041485 := bstep (se 3 (by rfl) ⟨757778, by rfl⟩ : syracuseStep 4041485 = 1515557) B1515557
theorem B1059617 : Blo 706319 1059617 := bstep (se 2 (by rfl) ⟨397356, by rfl⟩ : syracuseStep 1059617 = 794713) B794713
theorem B1059635 : Blo 706319 1059635 := bstep (se 1 (by rfl) ⟨794726, by rfl⟩ : syracuseStep 1059635 = 1589453) B1589453
theorem B1059665 : Blo 706319 1059665 := bstep (se 2 (by rfl) ⟨397374, by rfl⟩ : syracuseStep 1059665 = 794749) B794749
theorem B1059683 : Blo 706319 1059683 := bstep (se 1 (by rfl) ⟨794762, by rfl⟩ : syracuseStep 1059683 = 1589525) B1589525
theorem B797539 : Blo 706319 797539 := bstep (se 1 (by rfl) ⟨598154, by rfl⟩ : syracuseStep 797539 = 1196309) B1196309
theorem B1059713 : Blo 706319 1059713 := bstep (se 2 (by rfl) ⟨397392, by rfl⟩ : syracuseStep 1059713 = 794785) B794785
theorem B1059731 : Blo 706319 1059731 := bstep (se 1 (by rfl) ⟨794798, by rfl⟩ : syracuseStep 1059731 = 1589597) B1589597
theorem B1059761 : Blo 706319 1059761 := bstep (se 2 (by rfl) ⟨397410, by rfl⟩ : syracuseStep 1059761 = 794821) B794821
theorem B1059779 : Blo 706319 1059779 := bstep (se 1 (by rfl) ⟨794834, by rfl⟩ : syracuseStep 1059779 = 1589669) B1589669
theorem B1059809 : Blo 706319 1059809 := bstep (se 2 (by rfl) ⟨397428, by rfl⟩ : syracuseStep 1059809 = 794857) B794857
theorem B1059827 : Blo 706319 1059827 := bstep (se 1 (by rfl) ⟨794870, by rfl⟩ : syracuseStep 1059827 = 1589741) B1589741
theorem B797683 : Blo 706319 797683 := bstep (se 1 (by rfl) ⟨598262, by rfl⟩ : syracuseStep 797683 = 1196525) B1196525
theorem B2272259 : Blo 706319 2272259 := bstep (se 1 (by rfl) ⟨1704194, by rfl⟩ : syracuseStep 2272259 = 3408389) B3408389
theorem B1059857 : Blo 706319 1059857 := bstep (se 2 (by rfl) ⟨397446, by rfl⟩ : syracuseStep 1059857 = 794893) B794893
theorem B1059875 : Blo 706319 1059875 := bstep (se 1 (by rfl) ⟨794906, by rfl⟩ : syracuseStep 1059875 = 1589813) B1589813
theorem B1059905 : Blo 706319 1059905 := bstep (se 2 (by rfl) ⟨397464, by rfl⟩ : syracuseStep 1059905 = 794929) B794929
theorem B1059923 : Blo 706319 1059923 := bstep (se 1 (by rfl) ⟨794942, by rfl⟩ : syracuseStep 1059923 = 1589885) B1589885
theorem B1059953 : Blo 706319 1059953 := bstep (se 2 (by rfl) ⟨397482, by rfl⟩ : syracuseStep 1059953 = 794965) B794965
theorem B1059971 : Blo 706319 1059971 := bstep (se 1 (by rfl) ⟨794978, by rfl⟩ : syracuseStep 1059971 = 1589957) B1589957
theorem B797827 : Blo 706319 797827 := bstep (se 1 (by rfl) ⟨598370, by rfl⟩ : syracuseStep 797827 = 1196741) B1196741
theorem B1060001 : Blo 706319 1060001 := bstep (se 2 (by rfl) ⟨397500, by rfl⟩ : syracuseStep 1060001 = 795001) B795001
theorem B1060019 : Blo 706319 1060019 := bstep (se 1 (by rfl) ⟨795014, by rfl⟩ : syracuseStep 1060019 = 1590029) B1590029
theorem B896179 : Blo 706319 896179 := bstep (se 1 (by rfl) ⟨672134, by rfl⟩ : syracuseStep 896179 = 1344269) B1344269
theorem B1060049 : Blo 706319 1060049 := bstep (se 2 (by rfl) ⟨397518, by rfl⟩ : syracuseStep 1060049 = 795037) B795037
theorem B1060067 : Blo 706319 1060067 := bstep (se 1 (by rfl) ⟨795050, by rfl⟩ : syracuseStep 1060067 = 1590101) B1590101
theorem B1060097 : Blo 706319 1060097 := bstep (se 2 (by rfl) ⟨397536, by rfl⟩ : syracuseStep 1060097 = 795073) B795073
theorem B1060115 : Blo 706319 1060115 := bstep (se 1 (by rfl) ⟨795086, by rfl⟩ : syracuseStep 1060115 = 1590173) B1590173
theorem B896275 : Blo 706319 896275 := bstep (se 1 (by rfl) ⟨672206, by rfl⟩ : syracuseStep 896275 = 1344413) B1344413
theorem B797971 : Blo 706319 797971 := bstep (se 1 (by rfl) ⟨598478, by rfl⟩ : syracuseStep 797971 = 1196957) B1196957
theorem B1060145 : Blo 706319 1060145 := bstep (se 2 (by rfl) ⟨397554, by rfl⟩ : syracuseStep 1060145 = 795109) B795109
theorem B1060163 : Blo 706319 1060163 := bstep (se 1 (by rfl) ⟨795122, by rfl⟩ : syracuseStep 1060163 = 1590245) B1590245
theorem B1060193 : Blo 706319 1060193 := bstep (se 2 (by rfl) ⟨397572, by rfl⟩ : syracuseStep 1060193 = 795145) B795145
theorem B1060211 : Blo 706319 1060211 := bstep (se 1 (by rfl) ⟨795158, by rfl⟩ : syracuseStep 1060211 = 1590317) B1590317
theorem B1060241 : Blo 706319 1060241 := bstep (se 2 (by rfl) ⟨397590, by rfl⟩ : syracuseStep 1060241 = 795181) B795181
theorem B1060259 : Blo 706319 1060259 := bstep (se 1 (by rfl) ⟨795194, by rfl⟩ : syracuseStep 1060259 = 1590389) B1590389
theorem B798115 : Blo 706319 798115 := bstep (se 1 (by rfl) ⟨598586, by rfl⟩ : syracuseStep 798115 = 1197173) B1197173
theorem B1060289 : Blo 706319 1060289 := bstep (se 2 (by rfl) ⟨397608, by rfl⟩ : syracuseStep 1060289 = 795217) B795217
theorem B2305475 : Blo 706319 2305475 := bstep (se 1 (by rfl) ⟨1729106, by rfl⟩ : syracuseStep 2305475 = 3458213) B3458213
theorem B1060307 : Blo 706319 1060307 := bstep (se 1 (by rfl) ⟨795230, by rfl⟩ : syracuseStep 1060307 = 1590461) B1590461
theorem B1060337 : Blo 706319 1060337 := bstep (se 2 (by rfl) ⟨397626, by rfl⟩ : syracuseStep 1060337 = 795253) B795253
theorem B8170993 : Blo 706319 8170993 := bstep (se 2 (by rfl) ⟨3064122, by rfl⟩ : syracuseStep 8170993 = 6128245) B6128245
theorem B1060355 : Blo 706319 1060355 := bstep (se 1 (by rfl) ⟨795266, by rfl⟩ : syracuseStep 1060355 = 1590533) B1590533
theorem B1060385 : Blo 706319 1060385 := bstep (se 2 (by rfl) ⟨397644, by rfl⟩ : syracuseStep 1060385 = 795289) B795289
theorem B798259 : Blo 706319 798259 := bstep (se 1 (by rfl) ⟨598694, by rfl⟩ : syracuseStep 798259 = 1197389) B1197389
theorem B1060403 : Blo 706319 1060403 := bstep (se 1 (by rfl) ⟨795302, by rfl⟩ : syracuseStep 1060403 = 1590605) B1590605
theorem B1060433 : Blo 706319 1060433 := bstep (se 2 (by rfl) ⟨397662, by rfl⟩ : syracuseStep 1060433 = 795325) B795325
theorem B1060451 : Blo 706319 1060451 := bstep (se 1 (by rfl) ⟨795338, by rfl⟩ : syracuseStep 1060451 = 1590677) B1590677
theorem B3583601 : Blo 706319 3583601 := bstep (se 2 (by rfl) ⟨1343850, by rfl⟩ : syracuseStep 3583601 = 2687701) B2687701
theorem B9088625 : Blo 706319 9088625 := bstep (se 2 (by rfl) ⟨3408234, by rfl⟩ : syracuseStep 9088625 = 6816469) B6816469
theorem B1060481 : Blo 706319 1060481 := bstep (se 2 (by rfl) ⟨397680, by rfl⟩ : syracuseStep 1060481 = 795361) B795361
theorem B1060499 : Blo 706319 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B1060529 : Blo 706319 1060529 := bstep (se 2 (by rfl) ⟨397698, by rfl⟩ : syracuseStep 1060529 = 795397) B795397
theorem B1060547 : Blo 706319 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B798403 : Blo 706319 798403 := bstep (se 1 (by rfl) ⟨598802, by rfl⟩ : syracuseStep 798403 = 1197605) B1197605
theorem B1060577 : Blo 706319 1060577 := bstep (se 2 (by rfl) ⟨397716, by rfl⟩ : syracuseStep 1060577 = 795433) B795433
theorem B8072945 : Blo 706319 8072945 := bstep (se 2 (by rfl) ⟨3027354, by rfl⟩ : syracuseStep 8072945 = 6054709) B6054709
theorem B1060595 : Blo 706319 1060595 := bstep (se 1 (by rfl) ⟨795446, by rfl⟩ : syracuseStep 1060595 = 1590893) B1590893
theorem B896771 : Blo 706319 896771 := bstep (se 1 (by rfl) ⟨672578, by rfl⟩ : syracuseStep 896771 = 1345157) B1345157
theorem B1060625 : Blo 706319 1060625 := bstep (se 2 (by rfl) ⟨397734, by rfl⟩ : syracuseStep 1060625 = 795469) B795469
theorem B1060643 : Blo 706319 1060643 := bstep (se 1 (by rfl) ⟨795482, by rfl⟩ : syracuseStep 1060643 = 1590965) B1590965
theorem B1060673 : Blo 706319 1060673 := bstep (se 2 (by rfl) ⟨397752, by rfl⟩ : syracuseStep 1060673 = 795505) B795505
theorem B765763 : Blo 706319 765763 := bstep (se 1 (by rfl) ⟨574322, by rfl⟩ : syracuseStep 765763 = 1148645) B1148645
theorem B1060691 : Blo 706319 1060691 := bstep (se 1 (by rfl) ⟨795518, by rfl⟩ : syracuseStep 1060691 = 1591037) B1591037
theorem B798547 : Blo 706319 798547 := bstep (se 1 (by rfl) ⟨598910, by rfl⟩ : syracuseStep 798547 = 1197821) B1197821
theorem B1060721 : Blo 706319 1060721 := bstep (se 2 (by rfl) ⟨397770, by rfl⟩ : syracuseStep 1060721 = 795541) B795541
theorem B4599665 : Blo 706319 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B1060739 : Blo 706319 1060739 := bstep (se 1 (by rfl) ⟨795554, by rfl⟩ : syracuseStep 1060739 = 1591109) B1591109
theorem B1060769 : Blo 706319 1060769 := bstep (se 2 (by rfl) ⟨397788, by rfl⟩ : syracuseStep 1060769 = 795577) B795577
theorem B1060787 : Blo 706319 1060787 := bstep (se 1 (by rfl) ⟨795590, by rfl⟩ : syracuseStep 1060787 = 1591181) B1591181
theorem B1060817 : Blo 706319 1060817 := bstep (se 2 (by rfl) ⟨397806, by rfl⟩ : syracuseStep 1060817 = 795613) B795613
theorem B1060835 : Blo 706319 1060835 := bstep (se 1 (by rfl) ⟨795626, by rfl⟩ : syracuseStep 1060835 = 1591253) B1591253
theorem B798691 : Blo 706319 798691 := bstep (se 1 (by rfl) ⟨599018, by rfl⟩ : syracuseStep 798691 = 1198037) B1198037
theorem B3026929 : Blo 706319 3026929 := bstep (se 2 (by rfl) ⟨1135098, by rfl⟩ : syracuseStep 3026929 = 2270197) B2270197
theorem B1060865 : Blo 706319 1060865 := bstep (se 2 (by rfl) ⟨397824, by rfl⟩ : syracuseStep 1060865 = 795649) B795649
theorem B1191955 : Blo 706319 1191955 := bstep (se 1 (by rfl) ⟨893966, by rfl⟩ : syracuseStep 1191955 = 1787933) B1787933
theorem B1060883 : Blo 706319 1060883 := bstep (se 1 (by rfl) ⟨795662, by rfl⟩ : syracuseStep 1060883 = 1591325) B1591325
theorem B1060913 : Blo 706319 1060913 := bstep (se 2 (by rfl) ⟨397842, by rfl⟩ : syracuseStep 1060913 = 795685) B795685
theorem B1060931 : Blo 706319 1060931 := bstep (se 1 (by rfl) ⟨795698, by rfl⟩ : syracuseStep 1060931 = 1591397) B1591397
theorem B1060961 : Blo 706319 1060961 := bstep (se 2 (by rfl) ⟨397860, by rfl⟩ : syracuseStep 1060961 = 795721) B795721
theorem B13578353 : Blo 706319 13578353 := bstep (se 2 (by rfl) ⟨5091882, by rfl⟩ : syracuseStep 13578353 = 10183765) B10183765
theorem B1060979 : Blo 706319 1060979 := bstep (se 1 (by rfl) ⟨795734, by rfl⟩ : syracuseStep 1060979 = 1591469) B1591469
theorem B798835 : Blo 706319 798835 := bstep (se 1 (by rfl) ⟨599126, by rfl⟩ : syracuseStep 798835 = 1198253) B1198253
theorem B1061009 : Blo 706319 1061009 := bstep (se 2 (by rfl) ⟨397878, by rfl⟩ : syracuseStep 1061009 = 795757) B795757
theorem B1192097 : Blo 706319 1192097 := bstep (se 2 (by rfl) ⟨447036, by rfl⟩ : syracuseStep 1192097 = 894073) B894073
theorem B1061027 : Blo 706319 1061027 := bstep (se 1 (by rfl) ⟨795770, by rfl⟩ : syracuseStep 1061027 = 1591541) B1591541
theorem B2306225 : Blo 706319 2306225 := bstep (se 2 (by rfl) ⟨864834, by rfl⟩ : syracuseStep 2306225 = 1729669) B1729669
theorem B1061057 : Blo 706319 1061057 := bstep (se 2 (by rfl) ⟨397896, by rfl⟩ : syracuseStep 1061057 = 795793) B795793
theorem B1061075 : Blo 706319 1061075 := bstep (se 1 (by rfl) ⟨795806, by rfl⟩ : syracuseStep 1061075 = 1591613) B1591613
theorem B1061105 : Blo 706319 1061105 := bstep (se 2 (by rfl) ⟨397914, by rfl⟩ : syracuseStep 1061105 = 795829) B795829
theorem B1061123 : Blo 706319 1061123 := bstep (se 1 (by rfl) ⟨795842, by rfl⟩ : syracuseStep 1061123 = 1591685) B1591685
theorem B798979 : Blo 706319 798979 := bstep (se 1 (by rfl) ⟨599234, by rfl⟩ : syracuseStep 798979 = 1198469) B1198469
theorem B1192225 : Blo 706319 1192225 := bstep (se 2 (by rfl) ⟨447084, by rfl⟩ : syracuseStep 1192225 = 894169) B894169
theorem B1061153 : Blo 706319 1061153 := bstep (se 2 (by rfl) ⟨397932, by rfl⟩ : syracuseStep 1061153 = 795865) B795865
theorem B1061171 : Blo 706319 1061171 := bstep (se 1 (by rfl) ⟨795878, by rfl⟩ : syracuseStep 1061171 = 1591757) B1591757
theorem B1192259 : Blo 706319 1192259 := bstep (se 1 (by rfl) ⟨894194, by rfl⟩ : syracuseStep 1192259 = 1788389) B1788389
theorem B1061201 : Blo 706319 1061201 := bstep (se 2 (by rfl) ⟨397950, by rfl⟩ : syracuseStep 1061201 = 795901) B795901
theorem B1061219 : Blo 706319 1061219 := bstep (se 1 (by rfl) ⟨795914, by rfl⟩ : syracuseStep 1061219 = 1591829) B1591829
theorem B1061249 : Blo 706319 1061249 := bstep (se 2 (by rfl) ⟨397968, by rfl⟩ : syracuseStep 1061249 = 795937) B795937
theorem B1061267 : Blo 706319 1061267 := bstep (se 1 (by rfl) ⟨795950, by rfl⟩ : syracuseStep 1061267 = 1591901) B1591901
theorem B1061297 : Blo 706319 1061297 := bstep (se 2 (by rfl) ⟨397986, by rfl⟩ : syracuseStep 1061297 = 795973) B795973
theorem B1192387 : Blo 706319 1192387 := bstep (se 1 (by rfl) ⟨894290, by rfl⟩ : syracuseStep 1192387 = 1788581) B1788581
theorem B1061315 : Blo 706319 1061315 := bstep (se 1 (by rfl) ⟨795986, by rfl⟩ : syracuseStep 1061315 = 1591973) B1591973
theorem B897475 : Blo 706319 897475 := bstep (se 1 (by rfl) ⟨673106, by rfl⟩ : syracuseStep 897475 = 1346213) B1346213
theorem B1061345 : Blo 706319 1061345 := bstep (se 2 (by rfl) ⟨398004, by rfl⟩ : syracuseStep 1061345 = 796009) B796009
theorem B1061363 : Blo 706319 1061363 := bstep (se 1 (by rfl) ⟨796022, by rfl⟩ : syracuseStep 1061363 = 1592045) B1592045
theorem B1061393 : Blo 706319 1061393 := bstep (se 2 (by rfl) ⟨398022, by rfl⟩ : syracuseStep 1061393 = 796045) B796045
theorem B1061411 : Blo 706319 1061411 := bstep (se 1 (by rfl) ⟨796058, by rfl⟩ : syracuseStep 1061411 = 1592117) B1592117
theorem B897571 : Blo 706319 897571 := bstep (se 1 (by rfl) ⟨673178, by rfl⟩ : syracuseStep 897571 = 1346357) B1346357
theorem B1061441 : Blo 706319 1061441 := bstep (se 2 (by rfl) ⟨398040, by rfl⟩ : syracuseStep 1061441 = 796081) B796081
theorem B1192529 : Blo 706319 1192529 := bstep (se 2 (by rfl) ⟨447198, by rfl⟩ : syracuseStep 1192529 = 894397) B894397
theorem B1061459 : Blo 706319 1061459 := bstep (se 1 (by rfl) ⟨796094, by rfl⟩ : syracuseStep 1061459 = 1592189) B1592189
theorem B1061489 : Blo 706319 1061489 := bstep (se 2 (by rfl) ⟨398058, by rfl⟩ : syracuseStep 1061489 = 796117) B796117
theorem B1061507 : Blo 706319 1061507 := bstep (se 1 (by rfl) ⟨796130, by rfl⟩ : syracuseStep 1061507 = 1592261) B1592261
theorem B1061537 : Blo 706319 1061537 := bstep (se 2 (by rfl) ⟨398076, by rfl⟩ : syracuseStep 1061537 = 796153) B796153
theorem B1061555 : Blo 706319 1061555 := bstep (se 1 (by rfl) ⟨796166, by rfl⟩ : syracuseStep 1061555 = 1592333) B1592333
theorem B1192657 : Blo 706319 1192657 := bstep (se 2 (by rfl) ⟨447246, by rfl⟩ : syracuseStep 1192657 = 894493) B894493
theorem B1061585 : Blo 706319 1061585 := bstep (se 2 (by rfl) ⟨398094, by rfl⟩ : syracuseStep 1061585 = 796189) B796189
theorem B1061603 : Blo 706319 1061603 := bstep (se 1 (by rfl) ⟨796202, by rfl⟩ : syracuseStep 1061603 = 1592405) B1592405
theorem B1192691 : Blo 706319 1192691 := bstep (se 1 (by rfl) ⟨894518, by rfl⟩ : syracuseStep 1192691 = 1789037) B1789037
theorem B1061633 : Blo 706319 1061633 := bstep (se 2 (by rfl) ⟨398112, by rfl⟩ : syracuseStep 1061633 = 796225) B796225
theorem B1061651 : Blo 706319 1061651 := bstep (se 1 (by rfl) ⟨796238, by rfl⟩ : syracuseStep 1061651 = 1592477) B1592477
theorem B2011949 : Blo 706319 2011949 := bstep (se 3 (by rfl) ⟨377240, by rfl⟩ : syracuseStep 2011949 = 754481) B754481
theorem B1061681 : Blo 706319 1061681 := bstep (se 2 (by rfl) ⟨398130, by rfl⟩ : syracuseStep 1061681 = 796261) B796261
theorem B1061699 : Blo 706319 1061699 := bstep (se 1 (by rfl) ⟨796274, by rfl⟩ : syracuseStep 1061699 = 1592549) B1592549
theorem B1061729 : Blo 706319 1061729 := bstep (se 2 (by rfl) ⟨398148, by rfl⟩ : syracuseStep 1061729 = 796297) B796297
theorem B1192819 : Blo 706319 1192819 := bstep (se 1 (by rfl) ⟨894614, by rfl⟩ : syracuseStep 1192819 = 1789229) B1789229
theorem B1061747 : Blo 706319 1061747 := bstep (se 1 (by rfl) ⟨796310, by rfl⟩ : syracuseStep 1061747 = 1592621) B1592621
theorem B1061777 : Blo 706319 1061777 := bstep (se 2 (by rfl) ⟨398166, by rfl⟩ : syracuseStep 1061777 = 796333) B796333
theorem B1061795 : Blo 706319 1061795 := bstep (se 1 (by rfl) ⟨796346, by rfl⟩ : syracuseStep 1061795 = 1592693) B1592693
theorem B1061825 : Blo 706319 1061825 := bstep (se 2 (by rfl) ⟨398184, by rfl⟩ : syracuseStep 1061825 = 796369) B796369
theorem B1061843 : Blo 706319 1061843 := bstep (se 1 (by rfl) ⟨796382, by rfl⟩ : syracuseStep 1061843 = 1592765) B1592765
theorem B2012131 : Blo 706319 2012131 := bstep (se 1 (by rfl) ⟨1509098, by rfl⟩ : syracuseStep 2012131 = 3018197) B3018197
theorem B1061873 : Blo 706319 1061873 := bstep (se 2 (by rfl) ⟨398202, by rfl⟩ : syracuseStep 1061873 = 796405) B796405
theorem B1192961 : Blo 706319 1192961 := bstep (se 2 (by rfl) ⟨447360, by rfl⟩ : syracuseStep 1192961 = 894721) B894721
theorem B1061891 : Blo 706319 1061891 := bstep (se 1 (by rfl) ⟨796418, by rfl⟩ : syracuseStep 1061891 = 1592837) B1592837
theorem B2012177 : Blo 706319 2012177 := bstep (se 2 (by rfl) ⟨754566, by rfl⟩ : syracuseStep 2012177 = 1509133) B1509133
theorem B898067 : Blo 706319 898067 := bstep (se 1 (by rfl) ⟨673550, by rfl⟩ : syracuseStep 898067 = 1347101) B1347101
theorem B1061921 : Blo 706319 1061921 := bstep (se 2 (by rfl) ⟨398220, by rfl⟩ : syracuseStep 1061921 = 796441) B796441
theorem B3585059 : Blo 706319 3585059 := bstep (se 1 (by rfl) ⟨2688794, by rfl⟩ : syracuseStep 3585059 = 5377589) B5377589
theorem B1061939 : Blo 706319 1061939 := bstep (se 1 (by rfl) ⟨796454, by rfl⟩ : syracuseStep 1061939 = 1592909) B1592909
theorem B1061969 : Blo 706319 1061969 := bstep (se 2 (by rfl) ⟨398238, by rfl⟩ : syracuseStep 1061969 = 796477) B796477
theorem B1061987 : Blo 706319 1061987 := bstep (se 1 (by rfl) ⟨796490, by rfl⟩ : syracuseStep 1061987 = 1592981) B1592981
theorem B1193089 : Blo 706319 1193089 := bstep (se 2 (by rfl) ⟨447408, by rfl⟩ : syracuseStep 1193089 = 894817) B894817
theorem B1062017 : Blo 706319 1062017 := bstep (se 2 (by rfl) ⟨398256, by rfl⟩ : syracuseStep 1062017 = 796513) B796513
theorem B1062035 : Blo 706319 1062035 := bstep (se 1 (by rfl) ⟨796526, by rfl⟩ : syracuseStep 1062035 = 1593053) B1593053
theorem B1193123 : Blo 706319 1193123 := bstep (se 1 (by rfl) ⟨894842, by rfl⟩ : syracuseStep 1193123 = 1789685) B1789685
theorem B4535473 : Blo 706319 4535473 := bstep (se 2 (by rfl) ⟨1700802, by rfl⟩ : syracuseStep 4535473 = 3401605) B3401605
theorem B1062065 : Blo 706319 1062065 := bstep (se 2 (by rfl) ⟨398274, by rfl⟩ : syracuseStep 1062065 = 796549) B796549
theorem B1062083 : Blo 706319 1062083 := bstep (se 1 (by rfl) ⟨796562, by rfl⟩ : syracuseStep 1062083 = 1593125) B1593125
theorem B1062113 : Blo 706319 1062113 := bstep (se 2 (by rfl) ⟨398292, by rfl⟩ : syracuseStep 1062113 = 796585) B796585
theorem B931043 : Blo 706319 931043 := bstep (se 1 (by rfl) ⟨698282, by rfl⟩ : syracuseStep 931043 = 1396565) B1396565
theorem B1062131 : Blo 706319 1062131 := bstep (se 1 (by rfl) ⟨796598, by rfl⟩ : syracuseStep 1062131 = 1593197) B1593197
theorem B1062161 : Blo 706319 1062161 := bstep (se 2 (by rfl) ⟨398310, by rfl⟩ : syracuseStep 1062161 = 796621) B796621
theorem B1193251 : Blo 706319 1193251 := bstep (se 1 (by rfl) ⟨894938, by rfl⟩ : syracuseStep 1193251 = 1789877) B1789877
theorem B1062179 : Blo 706319 1062179 := bstep (se 1 (by rfl) ⟨796634, by rfl⟩ : syracuseStep 1062179 = 1593269) B1593269
theorem B1062209 : Blo 706319 1062209 := bstep (se 2 (by rfl) ⟨398328, by rfl⟩ : syracuseStep 1062209 = 796657) B796657
theorem B1062227 : Blo 706319 1062227 := bstep (se 1 (by rfl) ⟨796670, by rfl⟩ : syracuseStep 1062227 = 1593341) B1593341
theorem B1062257 : Blo 706319 1062257 := bstep (se 2 (by rfl) ⟨398346, by rfl⟩ : syracuseStep 1062257 = 796693) B796693
theorem B1062275 : Blo 706319 1062275 := bstep (se 1 (by rfl) ⟨796706, by rfl⟩ : syracuseStep 1062275 = 1593413) B1593413
theorem B1062305 : Blo 706319 1062305 := bstep (se 2 (by rfl) ⟨398364, by rfl⟩ : syracuseStep 1062305 = 796729) B796729
theorem B1193393 : Blo 706319 1193393 := bstep (se 2 (by rfl) ⟨447522, by rfl⟩ : syracuseStep 1193393 = 895045) B895045
theorem B1062323 : Blo 706319 1062323 := bstep (se 1 (by rfl) ⟨796742, by rfl⟩ : syracuseStep 1062323 = 1593485) B1593485
theorem B1062353 : Blo 706319 1062353 := bstep (se 2 (by rfl) ⟨398382, by rfl⟩ : syracuseStep 1062353 = 796765) B796765
theorem B1062371 : Blo 706319 1062371 := bstep (se 1 (by rfl) ⟨796778, by rfl⟩ : syracuseStep 1062371 = 1593557) B1593557
theorem B1062401 : Blo 706319 1062401 := bstep (se 2 (by rfl) ⟨398400, by rfl⟩ : syracuseStep 1062401 = 796801) B796801
theorem B1062419 : Blo 706319 1062419 := bstep (se 1 (by rfl) ⟨796814, by rfl⟩ : syracuseStep 1062419 = 1593629) B1593629
theorem B1193521 : Blo 706319 1193521 := bstep (se 2 (by rfl) ⟨447570, by rfl⟩ : syracuseStep 1193521 = 895141) B895141
theorem B1062449 : Blo 706319 1062449 := bstep (se 2 (by rfl) ⟨398418, by rfl⟩ : syracuseStep 1062449 = 796837) B796837
theorem B1062467 : Blo 706319 1062467 := bstep (se 1 (by rfl) ⟨796850, by rfl⟩ : syracuseStep 1062467 = 1593701) B1593701
theorem B9090629 : Blo 706319 9090629 := bstep (se 4 (by rfl) ⟨852246, by rfl⟩ : syracuseStep 9090629 = 1704493) B1704493
theorem B1193555 : Blo 706319 1193555 := bstep (se 1 (by rfl) ⟨895166, by rfl⟩ : syracuseStep 1193555 = 1790333) B1790333
theorem B1062497 : Blo 706319 1062497 := bstep (se 2 (by rfl) ⟨398436, by rfl⟩ : syracuseStep 1062497 = 796873) B796873
theorem B2274925 : Blo 706319 2274925 := bstep (se 3 (by rfl) ⟨426548, by rfl⟩ : syracuseStep 2274925 = 853097) B853097
theorem B4044401 : Blo 706319 4044401 := bstep (se 2 (by rfl) ⟨1516650, by rfl⟩ : syracuseStep 4044401 = 3033301) B3033301
theorem B1062515 : Blo 706319 1062515 := bstep (se 1 (by rfl) ⟨796886, by rfl⟩ : syracuseStep 1062515 = 1593773) B1593773
theorem B1062545 : Blo 706319 1062545 := bstep (se 2 (by rfl) ⟨398454, by rfl⟩ : syracuseStep 1062545 = 796909) B796909
theorem B1062563 : Blo 706319 1062563 := bstep (se 1 (by rfl) ⟨796922, by rfl⟩ : syracuseStep 1062563 = 1593845) B1593845
theorem B1062593 : Blo 706319 1062593 := bstep (se 2 (by rfl) ⟨398472, by rfl⟩ : syracuseStep 1062593 = 796945) B796945
theorem B1193683 : Blo 706319 1193683 := bstep (se 1 (by rfl) ⟨895262, by rfl⟩ : syracuseStep 1193683 = 1790525) B1790525
theorem B1062611 : Blo 706319 1062611 := bstep (se 1 (by rfl) ⟨796958, by rfl⟩ : syracuseStep 1062611 = 1593917) B1593917
theorem B898771 : Blo 706319 898771 := bstep (se 1 (by rfl) ⟨674078, by rfl⟩ : syracuseStep 898771 = 1348157) B1348157
theorem B1062641 : Blo 706319 1062641 := bstep (se 2 (by rfl) ⟨398490, by rfl⟩ : syracuseStep 1062641 = 796981) B796981
theorem B1062659 : Blo 706319 1062659 := bstep (se 1 (by rfl) ⟨796994, by rfl⟩ : syracuseStep 1062659 = 1593989) B1593989
theorem B27997973 : Blo 706319 27997973 := bstep (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) B1312405
theorem B1062689 : Blo 706319 1062689 := bstep (se 2 (by rfl) ⟨398508, by rfl⟩ : syracuseStep 1062689 = 797017) B797017
theorem B1062707 : Blo 706319 1062707 := bstep (se 1 (by rfl) ⟨797030, by rfl⟩ : syracuseStep 1062707 = 1594061) B1594061
theorem B898867 : Blo 706319 898867 := bstep (se 1 (by rfl) ⟨674150, by rfl⟩ : syracuseStep 898867 = 1348301) B1348301
theorem B3585869 : Blo 706319 3585869 := bstep (se 3 (by rfl) ⟨672350, by rfl⟩ : syracuseStep 3585869 = 1344701) B1344701
theorem B1062737 : Blo 706319 1062737 := bstep (se 2 (by rfl) ⟨398526, by rfl⟩ : syracuseStep 1062737 = 797053) B797053
theorem B1193825 : Blo 706319 1193825 := bstep (se 2 (by rfl) ⟨447684, by rfl⟩ : syracuseStep 1193825 = 895369) B895369
theorem B1062755 : Blo 706319 1062755 := bstep (se 1 (by rfl) ⟨797066, by rfl⟩ : syracuseStep 1062755 = 1594133) B1594133
theorem B1062785 : Blo 706319 1062785 := bstep (se 2 (by rfl) ⟨398544, by rfl⟩ : syracuseStep 1062785 = 797089) B797089
theorem B1062803 : Blo 706319 1062803 := bstep (se 1 (by rfl) ⟨797102, by rfl⟩ : syracuseStep 1062803 = 1594205) B1594205
theorem B1914787 : Blo 706319 1914787 := bstep (se 1 (by rfl) ⟨1436090, by rfl⟩ : syracuseStep 1914787 = 2872181) B2872181
theorem B1062833 : Blo 706319 1062833 := bstep (se 2 (by rfl) ⟨398562, by rfl⟩ : syracuseStep 1062833 = 797125) B797125
theorem B1062851 : Blo 706319 1062851 := bstep (se 1 (by rfl) ⟨797138, by rfl⟩ : syracuseStep 1062851 = 1594277) B1594277
theorem B1193953 : Blo 706319 1193953 := bstep (se 2 (by rfl) ⟨447732, by rfl⟩ : syracuseStep 1193953 = 895465) B895465
theorem B1062881 : Blo 706319 1062881 := bstep (se 2 (by rfl) ⟨398580, by rfl⟩ : syracuseStep 1062881 = 797161) B797161
theorem B1062899 : Blo 706319 1062899 := bstep (se 1 (by rfl) ⟨797174, by rfl⟩ : syracuseStep 1062899 = 1594349) B1594349
theorem B1193987 : Blo 706319 1193987 := bstep (se 1 (by rfl) ⟨895490, by rfl⟩ : syracuseStep 1193987 = 1790981) B1790981
theorem B1062929 : Blo 706319 1062929 := bstep (se 2 (by rfl) ⟨398598, by rfl⟩ : syracuseStep 1062929 = 797197) B797197
theorem B1062947 : Blo 706319 1062947 := bstep (se 1 (by rfl) ⟨797210, by rfl⟩ : syracuseStep 1062947 = 1594421) B1594421
theorem B1062977 : Blo 706319 1062977 := bstep (se 2 (by rfl) ⟨398616, by rfl⟩ : syracuseStep 1062977 = 797233) B797233
theorem B1062995 : Blo 706319 1062995 := bstep (se 1 (by rfl) ⟨797246, by rfl⟩ : syracuseStep 1062995 = 1594493) B1594493
theorem B1063025 : Blo 706319 1063025 := bstep (se 2 (by rfl) ⟨398634, by rfl⟩ : syracuseStep 1063025 = 797269) B797269
theorem B1194115 : Blo 706319 1194115 := bstep (se 1 (by rfl) ⟨895586, by rfl⟩ : syracuseStep 1194115 = 1791173) B1791173
theorem B1063043 : Blo 706319 1063043 := bstep (se 1 (by rfl) ⟨797282, by rfl⟩ : syracuseStep 1063043 = 1594565) B1594565
theorem B2046097 : Blo 706319 2046097 := bstep (se 2 (by rfl) ⟨767286, by rfl⟩ : syracuseStep 2046097 = 1534573) B1534573
theorem B1063073 : Blo 706319 1063073 := bstep (se 2 (by rfl) ⟨398652, by rfl⟩ : syracuseStep 1063073 = 797305) B797305
theorem B1063091 : Blo 706319 1063091 := bstep (se 1 (by rfl) ⟨797318, by rfl⟩ : syracuseStep 1063091 = 1594637) B1594637
theorem B1063121 : Blo 706319 1063121 := bstep (se 2 (by rfl) ⟨398670, by rfl⟩ : syracuseStep 1063121 = 797341) B797341
theorem B1063139 : Blo 706319 1063139 := bstep (se 1 (by rfl) ⟨797354, by rfl⟩ : syracuseStep 1063139 = 1594709) B1594709
theorem B1063169 : Blo 706319 1063169 := bstep (se 2 (by rfl) ⟨398688, by rfl⟩ : syracuseStep 1063169 = 797377) B797377
theorem B1194257 : Blo 706319 1194257 := bstep (se 2 (by rfl) ⟨447846, by rfl⟩ : syracuseStep 1194257 = 895693) B895693
theorem B1063187 : Blo 706319 1063187 := bstep (se 1 (by rfl) ⟨797390, by rfl⟩ : syracuseStep 1063187 = 1594781) B1594781
theorem B1063217 : Blo 706319 1063217 := bstep (se 2 (by rfl) ⟨398706, by rfl⟩ : syracuseStep 1063217 = 797413) B797413
theorem B1063235 : Blo 706319 1063235 := bstep (se 1 (by rfl) ⟨797426, by rfl⟩ : syracuseStep 1063235 = 1594853) B1594853
theorem B1063265 : Blo 706319 1063265 := bstep (se 2 (by rfl) ⟨398724, by rfl⟩ : syracuseStep 1063265 = 797449) B797449
theorem B1063283 : Blo 706319 1063283 := bstep (se 1 (by rfl) ⟨797462, by rfl⟩ : syracuseStep 1063283 = 1594925) B1594925
theorem B1194385 : Blo 706319 1194385 := bstep (se 2 (by rfl) ⟨447894, by rfl⟩ : syracuseStep 1194385 = 895789) B895789
theorem B1063313 : Blo 706319 1063313 := bstep (se 2 (by rfl) ⟨398742, by rfl⟩ : syracuseStep 1063313 = 797485) B797485
theorem B1063331 : Blo 706319 1063331 := bstep (se 1 (by rfl) ⟨797498, by rfl⟩ : syracuseStep 1063331 = 1594997) B1594997
theorem B1194419 : Blo 706319 1194419 := bstep (se 1 (by rfl) ⟨895814, by rfl⟩ : syracuseStep 1194419 = 1791629) B1791629
theorem B1063361 : Blo 706319 1063361 := bstep (se 2 (by rfl) ⟨398760, by rfl⟩ : syracuseStep 1063361 = 797521) B797521
theorem B2013635 : Blo 706319 2013635 := bstep (se 1 (by rfl) ⟨1510226, by rfl⟩ : syracuseStep 2013635 = 3020453) B3020453
theorem B1063379 : Blo 706319 1063379 := bstep (se 1 (by rfl) ⟨797534, by rfl⟩ : syracuseStep 1063379 = 1595069) B1595069
theorem B1063409 : Blo 706319 1063409 := bstep (se 2 (by rfl) ⟨398778, by rfl⟩ : syracuseStep 1063409 = 797557) B797557
theorem B1063427 : Blo 706319 1063427 := bstep (se 1 (by rfl) ⟨797570, by rfl⟩ : syracuseStep 1063427 = 1595141) B1595141
theorem B1063457 : Blo 706319 1063457 := bstep (se 2 (by rfl) ⟨398796, by rfl⟩ : syracuseStep 1063457 = 797593) B797593
theorem B1194547 : Blo 706319 1194547 := bstep (se 1 (by rfl) ⟨895910, by rfl⟩ : syracuseStep 1194547 = 1791821) B1791821
theorem B1063475 : Blo 706319 1063475 := bstep (se 1 (by rfl) ⟨797606, by rfl⟩ : syracuseStep 1063475 = 1595213) B1595213
theorem B3226189 : Blo 706319 3226189 := bstep (se 3 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 3226189 = 1209821) B1209821
theorem B1063505 : Blo 706319 1063505 := bstep (se 2 (by rfl) ⟨398814, by rfl⟩ : syracuseStep 1063505 = 797629) B797629
theorem B1063523 : Blo 706319 1063523 := bstep (se 1 (by rfl) ⟨797642, by rfl⟩ : syracuseStep 1063523 = 1595285) B1595285
theorem B1063553 : Blo 706319 1063553 := bstep (se 2 (by rfl) ⟨398832, by rfl⟩ : syracuseStep 1063553 = 797665) B797665
theorem B2046605 : Blo 706319 2046605 := bstep (se 3 (by rfl) ⟨383738, by rfl⟩ : syracuseStep 2046605 = 767477) B767477
theorem B1063571 : Blo 706319 1063571 := bstep (se 1 (by rfl) ⟨797678, by rfl⟩ : syracuseStep 1063571 = 1595357) B1595357
theorem B1063601 : Blo 706319 1063601 := bstep (se 2 (by rfl) ⟨398850, by rfl⟩ : syracuseStep 1063601 = 797701) B797701
theorem B1194689 : Blo 706319 1194689 := bstep (se 2 (by rfl) ⟨448008, by rfl⟩ : syracuseStep 1194689 = 896017) B896017
theorem B1063619 : Blo 706319 1063619 := bstep (se 1 (by rfl) ⟨797714, by rfl⟩ : syracuseStep 1063619 = 1595429) B1595429
theorem B1063649 : Blo 706319 1063649 := bstep (se 2 (by rfl) ⟨398868, by rfl⟩ : syracuseStep 1063649 = 797737) B797737
theorem B1063667 : Blo 706319 1063667 := bstep (se 1 (by rfl) ⟨797750, by rfl⟩ : syracuseStep 1063667 = 1595501) B1595501
theorem B1063697 : Blo 706319 1063697 := bstep (se 2 (by rfl) ⟨398886, by rfl⟩ : syracuseStep 1063697 = 797773) B797773
theorem B1063715 : Blo 706319 1063715 := bstep (se 1 (by rfl) ⟨797786, by rfl⟩ : syracuseStep 1063715 = 1595573) B1595573
theorem B1194817 : Blo 706319 1194817 := bstep (se 2 (by rfl) ⟨448056, by rfl⟩ : syracuseStep 1194817 = 896113) B896113
theorem B1063745 : Blo 706319 1063745 := bstep (se 2 (by rfl) ⟨398904, by rfl⟩ : syracuseStep 1063745 = 797809) B797809
theorem B1063763 : Blo 706319 1063763 := bstep (se 1 (by rfl) ⟨797822, by rfl⟩ : syracuseStep 1063763 = 1595645) B1595645
theorem B1194851 : Blo 706319 1194851 := bstep (se 1 (by rfl) ⟨896138, by rfl⟩ : syracuseStep 1194851 = 1792277) B1792277
theorem B1063793 : Blo 706319 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B1063811 : Blo 706319 1063811 := bstep (se 1 (by rfl) ⟨797858, by rfl⟩ : syracuseStep 1063811 = 1595717) B1595717
theorem B1063841 : Blo 706319 1063841 := bstep (se 2 (by rfl) ⟨398940, by rfl⟩ : syracuseStep 1063841 = 797881) B797881
theorem B1063859 : Blo 706319 1063859 := bstep (se 1 (by rfl) ⟨797894, by rfl⟩ : syracuseStep 1063859 = 1595789) B1595789
theorem B5389253 : Blo 706319 5389253 := bstep (se 4 (by rfl) ⟨505242, by rfl⟩ : syracuseStep 5389253 = 1010485) B1010485
theorem B1063889 : Blo 706319 1063889 := bstep (se 2 (by rfl) ⟨398958, by rfl⟩ : syracuseStep 1063889 = 797917) B797917
theorem B1194979 : Blo 706319 1194979 := bstep (se 1 (by rfl) ⟨896234, by rfl⟩ : syracuseStep 1194979 = 1792469) B1792469
theorem B1063907 : Blo 706319 1063907 := bstep (se 1 (by rfl) ⟨797930, by rfl⟩ : syracuseStep 1063907 = 1595861) B1595861
theorem B3029987 : Blo 706319 3029987 := bstep (se 1 (by rfl) ⟨2272490, by rfl⟩ : syracuseStep 3029987 = 4544981) B4544981
theorem B1063937 : Blo 706319 1063937 := bstep (se 2 (by rfl) ⟨398976, by rfl⟩ : syracuseStep 1063937 = 797953) B797953
theorem B1063955 : Blo 706319 1063955 := bstep (se 1 (by rfl) ⟨797966, by rfl⟩ : syracuseStep 1063955 = 1595933) B1595933
theorem B2047025 : Blo 706319 2047025 := bstep (se 2 (by rfl) ⟨767634, by rfl⟩ : syracuseStep 2047025 = 1535269) B1535269
theorem B1063985 : Blo 706319 1063985 := bstep (se 2 (by rfl) ⟨398994, by rfl⟩ : syracuseStep 1063985 = 797989) B797989
theorem B1064003 : Blo 706319 1064003 := bstep (se 1 (by rfl) ⟨798002, by rfl⟩ : syracuseStep 1064003 = 1596005) B1596005
theorem B1064033 : Blo 706319 1064033 := bstep (se 2 (by rfl) ⟨399012, by rfl⟩ : syracuseStep 1064033 = 798025) B798025
theorem B1195121 : Blo 706319 1195121 := bstep (se 2 (by rfl) ⟨448170, by rfl⟩ : syracuseStep 1195121 = 896341) B896341
theorem B1064051 : Blo 706319 1064051 := bstep (se 1 (by rfl) ⟨798038, by rfl⟩ : syracuseStep 1064051 = 1596077) B1596077
theorem B1064081 : Blo 706319 1064081 := bstep (se 2 (by rfl) ⟨399030, by rfl⟩ : syracuseStep 1064081 = 798061) B798061
theorem B1064099 : Blo 706319 1064099 := bstep (se 1 (by rfl) ⟨798074, by rfl⟩ : syracuseStep 1064099 = 1596149) B1596149
theorem B1064129 : Blo 706319 1064129 := bstep (se 2 (by rfl) ⟨399048, by rfl⟩ : syracuseStep 1064129 = 798097) B798097
theorem B1064147 : Blo 706319 1064147 := bstep (se 1 (by rfl) ⟨798110, by rfl⟩ : syracuseStep 1064147 = 1596221) B1596221
theorem B1195249 : Blo 706319 1195249 := bstep (se 2 (by rfl) ⟨448218, by rfl⟩ : syracuseStep 1195249 = 896437) B896437
theorem B1064177 : Blo 706319 1064177 := bstep (se 2 (by rfl) ⟨399066, by rfl⟩ : syracuseStep 1064177 = 798133) B798133
theorem B1064195 : Blo 706319 1064195 := bstep (se 1 (by rfl) ⟨798146, by rfl⟩ : syracuseStep 1064195 = 1596293) B1596293
theorem B1195283 : Blo 706319 1195283 := bstep (se 1 (by rfl) ⟨896462, by rfl⟩ : syracuseStep 1195283 = 1792925) B1792925
theorem B1064225 : Blo 706319 1064225 := bstep (se 2 (by rfl) ⟨399084, by rfl⟩ : syracuseStep 1064225 = 798169) B798169
theorem B1817891 : Blo 706319 1817891 := bstep (se 1 (by rfl) ⟨1363418, by rfl⟩ : syracuseStep 1817891 = 2726837) B2726837
theorem B1064243 : Blo 706319 1064243 := bstep (se 1 (by rfl) ⟨798182, by rfl⟩ : syracuseStep 1064243 = 1596365) B1596365
theorem B1064273 : Blo 706319 1064273 := bstep (se 2 (by rfl) ⟨399102, by rfl⟩ : syracuseStep 1064273 = 798205) B798205
theorem B1064291 : Blo 706319 1064291 := bstep (se 1 (by rfl) ⟨798218, by rfl⟩ : syracuseStep 1064291 = 1596437) B1596437
theorem B1064321 : Blo 706319 1064321 := bstep (se 2 (by rfl) ⟨399120, by rfl⟩ : syracuseStep 1064321 = 798241) B798241
theorem B1916291 : Blo 706319 1916291 := bstep (se 1 (by rfl) ⟨1437218, by rfl⟩ : syracuseStep 1916291 = 2874437) B2874437
theorem B1195411 : Blo 706319 1195411 := bstep (se 1 (by rfl) ⟨896558, by rfl⟩ : syracuseStep 1195411 = 1793117) B1793117
theorem B1064339 : Blo 706319 1064339 := bstep (se 1 (by rfl) ⟨798254, by rfl⟩ : syracuseStep 1064339 = 1596509) B1596509
theorem B1064369 : Blo 706319 1064369 := bstep (se 2 (by rfl) ⟨399138, by rfl⟩ : syracuseStep 1064369 = 798277) B798277
theorem B1064387 : Blo 706319 1064387 := bstep (se 1 (by rfl) ⟨798290, by rfl⟩ : syracuseStep 1064387 = 1596581) B1596581
theorem B1064417 : Blo 706319 1064417 := bstep (se 2 (by rfl) ⟨399156, by rfl⟩ : syracuseStep 1064417 = 798313) B798313
theorem B1064435 : Blo 706319 1064435 := bstep (se 1 (by rfl) ⟨798326, by rfl⟩ : syracuseStep 1064435 = 1596653) B1596653
theorem B1064465 : Blo 706319 1064465 := bstep (se 2 (by rfl) ⟨399174, by rfl⟩ : syracuseStep 1064465 = 798349) B798349
theorem B1195553 : Blo 706319 1195553 := bstep (se 2 (by rfl) ⟨448332, by rfl⟩ : syracuseStep 1195553 = 896665) B896665
theorem B1064483 : Blo 706319 1064483 := bstep (se 1 (by rfl) ⟨798362, by rfl⟩ : syracuseStep 1064483 = 1596725) B1596725
theorem B1064513 : Blo 706319 1064513 := bstep (se 2 (by rfl) ⟨399192, by rfl⟩ : syracuseStep 1064513 = 798385) B798385
theorem B1064531 : Blo 706319 1064531 := bstep (se 1 (by rfl) ⟨798398, by rfl⟩ : syracuseStep 1064531 = 1596797) B1596797
theorem B1064561 : Blo 706319 1064561 := bstep (se 2 (by rfl) ⟨399210, by rfl⟩ : syracuseStep 1064561 = 798421) B798421
theorem B1064579 : Blo 706319 1064579 := bstep (se 1 (by rfl) ⟨798434, by rfl⟩ : syracuseStep 1064579 = 1596869) B1596869
theorem B2014865 : Blo 706319 2014865 := bstep (se 2 (by rfl) ⟨755574, by rfl⟩ : syracuseStep 2014865 = 1511149) B1511149
theorem B1195681 : Blo 706319 1195681 := bstep (se 2 (by rfl) ⟨448380, by rfl⟩ : syracuseStep 1195681 = 896761) B896761
theorem B1064609 : Blo 706319 1064609 := bstep (se 2 (by rfl) ⟨399228, by rfl⟩ : syracuseStep 1064609 = 798457) B798457
theorem B1064627 : Blo 706319 1064627 := bstep (se 1 (by rfl) ⟨798470, by rfl⟩ : syracuseStep 1064627 = 1596941) B1596941
theorem B1195715 : Blo 706319 1195715 := bstep (se 1 (by rfl) ⟨896786, by rfl⟩ : syracuseStep 1195715 = 1793573) B1793573
theorem B1064657 : Blo 706319 1064657 := bstep (se 2 (by rfl) ⟨399246, by rfl⟩ : syracuseStep 1064657 = 798493) B798493
theorem B1064675 : Blo 706319 1064675 := bstep (se 1 (by rfl) ⟨798506, by rfl⟩ : syracuseStep 1064675 = 1597013) B1597013
theorem B1064705 : Blo 706319 1064705 := bstep (se 2 (by rfl) ⟨399264, by rfl⟩ : syracuseStep 1064705 = 798529) B798529
theorem B1064723 : Blo 706319 1064723 := bstep (se 1 (by rfl) ⟨798542, by rfl⟩ : syracuseStep 1064723 = 1597085) B1597085
theorem B4308785 : Blo 706319 4308785 := bstep (se 2 (by rfl) ⟨1615794, by rfl⟩ : syracuseStep 4308785 = 3231589) B3231589
theorem B1064753 : Blo 706319 1064753 := bstep (se 2 (by rfl) ⟨399282, by rfl⟩ : syracuseStep 1064753 = 798565) B798565
theorem B1195843 : Blo 706319 1195843 := bstep (se 1 (by rfl) ⟨896882, by rfl⟩ : syracuseStep 1195843 = 1793765) B1793765
theorem B1064771 : Blo 706319 1064771 := bstep (se 1 (by rfl) ⟨798578, by rfl⟩ : syracuseStep 1064771 = 1597157) B1597157
theorem B1064801 : Blo 706319 1064801 := bstep (se 2 (by rfl) ⟨399300, by rfl⟩ : syracuseStep 1064801 = 798601) B798601
theorem B1064819 : Blo 706319 1064819 := bstep (se 1 (by rfl) ⟨798614, by rfl⟩ : syracuseStep 1064819 = 1597229) B1597229
theorem B1064849 : Blo 706319 1064849 := bstep (se 2 (by rfl) ⟨399318, by rfl⟩ : syracuseStep 1064849 = 798637) B798637
theorem B1064867 : Blo 706319 1064867 := bstep (se 1 (by rfl) ⟨798650, by rfl⟩ : syracuseStep 1064867 = 1597301) B1597301
theorem B1064897 : Blo 706319 1064897 := bstep (se 2 (by rfl) ⟨399336, by rfl⟩ : syracuseStep 1064897 = 798673) B798673
theorem B1195985 : Blo 706319 1195985 := bstep (se 2 (by rfl) ⟨448494, by rfl⟩ : syracuseStep 1195985 = 896989) B896989
theorem B1064915 : Blo 706319 1064915 := bstep (se 1 (by rfl) ⟨798686, by rfl⟩ : syracuseStep 1064915 = 1597373) B1597373
theorem B1589219 : Blo 706319 1589219 := bstep (se 1 (by rfl) ⟨1191914, by rfl⟩ : syracuseStep 1589219 = 2383829) B2383829
theorem B4079587 : Blo 706319 4079587 := bstep (se 1 (by rfl) ⟨3059690, by rfl⟩ : syracuseStep 4079587 = 6119381) B6119381
theorem B1064945 : Blo 706319 1064945 := bstep (se 2 (by rfl) ⟨399354, by rfl⟩ : syracuseStep 1064945 = 798709) B798709
theorem B1064963 : Blo 706319 1064963 := bstep (se 1 (by rfl) ⟨798722, by rfl⟩ : syracuseStep 1064963 = 1597445) B1597445
theorem B1064993 : Blo 706319 1064993 := bstep (se 2 (by rfl) ⟨399372, by rfl⟩ : syracuseStep 1064993 = 798745) B798745
theorem B1065011 : Blo 706319 1065011 := bstep (se 1 (by rfl) ⟨798758, by rfl⟩ : syracuseStep 1065011 = 1597517) B1597517
theorem B1196113 : Blo 706319 1196113 := bstep (se 2 (by rfl) ⟨448542, by rfl⟩ : syracuseStep 1196113 = 897085) B897085
theorem B1065041 : Blo 706319 1065041 := bstep (se 2 (by rfl) ⟨399390, by rfl⟩ : syracuseStep 1065041 = 798781) B798781
theorem B1065059 : Blo 706319 1065059 := bstep (se 1 (by rfl) ⟨798794, by rfl⟩ : syracuseStep 1065059 = 1597589) B1597589
theorem B1917037 : Blo 706319 1917037 := bstep (se 3 (by rfl) ⟨359444, by rfl⟩ : syracuseStep 1917037 = 718889) B718889
theorem B1196147 : Blo 706319 1196147 := bstep (se 1 (by rfl) ⟨897110, by rfl⟩ : syracuseStep 1196147 = 1794221) B1794221
theorem B1065089 : Blo 706319 1065089 := bstep (se 2 (by rfl) ⟨399408, by rfl⟩ : syracuseStep 1065089 = 798817) B798817
theorem B1065107 : Blo 706319 1065107 := bstep (se 1 (by rfl) ⟨798830, by rfl⟩ : syracuseStep 1065107 = 1597661) B1597661
theorem B1065137 : Blo 706319 1065137 := bstep (se 2 (by rfl) ⟨399426, by rfl⟩ : syracuseStep 1065137 = 798853) B798853
theorem B1065155 : Blo 706319 1065155 := bstep (se 1 (by rfl) ⟨798866, by rfl⟩ : syracuseStep 1065155 = 1597733) B1597733
theorem B1065185 : Blo 706319 1065185 := bstep (se 2 (by rfl) ⟨399444, by rfl⟩ : syracuseStep 1065185 = 798889) B798889
theorem B1589489 : Blo 706319 1589489 := bstep (se 2 (by rfl) ⟨596058, by rfl⟩ : syracuseStep 1589489 = 1192117) B1192117
theorem B1196275 : Blo 706319 1196275 := bstep (se 1 (by rfl) ⟨897206, by rfl⟩ : syracuseStep 1196275 = 1794413) B1794413
theorem B1065203 : Blo 706319 1065203 := bstep (se 1 (by rfl) ⟨798902, by rfl⟩ : syracuseStep 1065203 = 1597805) B1597805
theorem B1589507 : Blo 706319 1589507 := bstep (se 1 (by rfl) ⟨1192130, by rfl⟩ : syracuseStep 1589507 = 2384261) B2384261
theorem B1065233 : Blo 706319 1065233 := bstep (se 2 (by rfl) ⟨399462, by rfl⟩ : syracuseStep 1065233 = 798925) B798925
theorem B1065251 : Blo 706319 1065251 := bstep (se 1 (by rfl) ⟨798938, by rfl⟩ : syracuseStep 1065251 = 1597877) B1597877
theorem B1065281 : Blo 706319 1065281 := bstep (se 2 (by rfl) ⟨399480, by rfl⟩ : syracuseStep 1065281 = 798961) B798961
theorem B1065299 : Blo 706319 1065299 := bstep (se 1 (by rfl) ⟨798974, by rfl⟩ : syracuseStep 1065299 = 1597949) B1597949
theorem B1065329 : Blo 706319 1065329 := bstep (se 2 (by rfl) ⟨399498, by rfl⟩ : syracuseStep 1065329 = 798997) B798997
theorem B1196417 : Blo 706319 1196417 := bstep (se 2 (by rfl) ⟨448656, by rfl⟩ : syracuseStep 1196417 = 897313) B897313
theorem B1065347 : Blo 706319 1065347 := bstep (se 1 (by rfl) ⟨799010, by rfl⟩ : syracuseStep 1065347 = 1598021) B1598021
theorem B1065377 : Blo 706319 1065377 := bstep (se 2 (by rfl) ⟨399516, by rfl⟩ : syracuseStep 1065377 = 799033) B799033
theorem B1065395 : Blo 706319 1065395 := bstep (se 1 (by rfl) ⟨799046, by rfl⟩ : syracuseStep 1065395 = 1598093) B1598093
theorem B1065425 : Blo 706319 1065425 := bstep (se 2 (by rfl) ⟨399534, by rfl⟩ : syracuseStep 1065425 = 799069) B799069
theorem B1065443 : Blo 706319 1065443 := bstep (se 1 (by rfl) ⟨799082, by rfl⟩ : syracuseStep 1065443 = 1598165) B1598165
theorem B1196545 : Blo 706319 1196545 := bstep (se 2 (by rfl) ⟨448704, by rfl⟩ : syracuseStep 1196545 = 897409) B897409
theorem B1065473 : Blo 706319 1065473 := bstep (se 2 (by rfl) ⟨399552, by rfl⟩ : syracuseStep 1065473 = 799105) B799105
theorem B1589777 : Blo 706319 1589777 := bstep (se 2 (by rfl) ⟨596166, by rfl⟩ : syracuseStep 1589777 = 1192333) B1192333
theorem B1589795 : Blo 706319 1589795 := bstep (se 1 (by rfl) ⟨1192346, by rfl⟩ : syracuseStep 1589795 = 2384693) B2384693
theorem B1196579 : Blo 706319 1196579 := bstep (se 1 (by rfl) ⟨897434, by rfl⟩ : syracuseStep 1196579 = 1794869) B1794869
theorem B1196707 : Blo 706319 1196707 := bstep (se 1 (by rfl) ⟨897530, by rfl⟩ : syracuseStep 1196707 = 1795061) B1795061
theorem B3588785 : Blo 706319 3588785 := bstep (se 2 (by rfl) ⟨1345794, by rfl⟩ : syracuseStep 3588785 = 2691589) B2691589
theorem B1819409 : Blo 706319 1819409 := bstep (se 2 (by rfl) ⟨682278, by rfl⟩ : syracuseStep 1819409 = 1364557) B1364557
theorem B1590065 : Blo 706319 1590065 := bstep (se 2 (by rfl) ⟨596274, by rfl⟩ : syracuseStep 1590065 = 1192549) B1192549
theorem B1196849 : Blo 706319 1196849 := bstep (se 2 (by rfl) ⟨448818, by rfl⟩ : syracuseStep 1196849 = 897637) B897637
theorem B1590083 : Blo 706319 1590083 := bstep (se 1 (by rfl) ⟨1192562, by rfl⟩ : syracuseStep 1590083 = 2385125) B2385125
theorem B1196977 : Blo 706319 1196977 := bstep (se 2 (by rfl) ⟨448866, by rfl⟩ : syracuseStep 1196977 = 897733) B897733
theorem B3457997 : Blo 706319 3457997 := bstep (se 3 (by rfl) ⟨648374, by rfl⟩ : syracuseStep 3457997 = 1296749) B1296749
theorem B1197011 : Blo 706319 1197011 := bstep (se 1 (by rfl) ⟨897758, by rfl⟩ : syracuseStep 1197011 = 1795517) B1795517
theorem B2016323 : Blo 706319 2016323 := bstep (se 1 (by rfl) ⟨1512242, by rfl⟩ : syracuseStep 2016323 = 3024485) B3024485
theorem B2049101 : Blo 706319 2049101 := bstep (se 3 (by rfl) ⟨384206, by rfl⟩ : syracuseStep 2049101 = 768413) B768413
theorem B1590353 : Blo 706319 1590353 := bstep (se 2 (by rfl) ⟨596382, by rfl⟩ : syracuseStep 1590353 = 1192765) B1192765
theorem B1197139 : Blo 706319 1197139 := bstep (se 1 (by rfl) ⟨897854, by rfl⟩ : syracuseStep 1197139 = 1795709) B1795709
theorem B1131619 : Blo 706319 1131619 := bstep (se 1 (by rfl) ⟨848714, by rfl⟩ : syracuseStep 1131619 = 1697429) B1697429
theorem B1590371 : Blo 706319 1590371 := bstep (se 1 (by rfl) ⟨1192778, by rfl⟩ : syracuseStep 1590371 = 2385557) B2385557
theorem B46613717 : Blo 706319 46613717 := bstep (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) B1092509
theorem B1197281 : Blo 706319 1197281 := bstep (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) B897961
theorem B1197409 : Blo 706319 1197409 := bstep (se 2 (by rfl) ⟨449028, by rfl⟩ : syracuseStep 1197409 = 898057) B898057
theorem B1131889 : Blo 706319 1131889 := bstep (se 2 (by rfl) ⟨424458, by rfl⟩ : syracuseStep 1131889 = 848917) B848917
theorem B1590641 : Blo 706319 1590641 := bstep (se 2 (by rfl) ⟨596490, by rfl⟩ : syracuseStep 1590641 = 1192981) B1192981
theorem B1590659 : Blo 706319 1590659 := bstep (se 1 (by rfl) ⟨1192994, by rfl⟩ : syracuseStep 1590659 = 2385989) B2385989
theorem B1197443 : Blo 706319 1197443 := bstep (se 1 (by rfl) ⟨898082, by rfl⟩ : syracuseStep 1197443 = 1796165) B1796165
theorem B1197571 : Blo 706319 1197571 := bstep (se 1 (by rfl) ⟨898178, by rfl⟩ : syracuseStep 1197571 = 1796357) B1796357
theorem B1164817 : Blo 706319 1164817 := bstep (se 2 (by rfl) ⟨436806, by rfl⟩ : syracuseStep 1164817 = 873613) B873613
theorem B1132145 : Blo 706319 1132145 := bstep (se 2 (by rfl) ⟨424554, by rfl⟩ : syracuseStep 1132145 = 849109) B849109
theorem B1590929 : Blo 706319 1590929 := bstep (se 2 (by rfl) ⟨596598, by rfl⟩ : syracuseStep 1590929 = 1193197) B1193197
theorem B1197713 : Blo 706319 1197713 := bstep (se 2 (by rfl) ⟨449142, by rfl⟩ : syracuseStep 1197713 = 898285) B898285
theorem B1590947 : Blo 706319 1590947 := bstep (se 1 (by rfl) ⟨1193210, by rfl⟩ : syracuseStep 1590947 = 2386421) B2386421
theorem B1918691 : Blo 706319 1918691 := bstep (se 1 (by rfl) ⟨1439018, by rfl⟩ : syracuseStep 1918691 = 2878037) B2878037
theorem B7653133 : Blo 706319 7653133 := bstep (se 3 (by rfl) ⟨1434962, by rfl⟩ : syracuseStep 7653133 = 2869925) B2869925
theorem B1197841 : Blo 706319 1197841 := bstep (se 2 (by rfl) ⟨449190, by rfl⟩ : syracuseStep 1197841 = 898381) B898381
theorem B706323 : Blo 706319 706323 := bstep (se 1 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 706323 = 1059485) B1059485
theorem B706339 : Blo 706319 706339 := bstep (se 1 (by rfl) ⟨529754, by rfl⟩ : syracuseStep 706339 = 1059509) B1059509
theorem B706355 : Blo 706319 706355 := bstep (se 1 (by rfl) ⟨529766, by rfl⟩ : syracuseStep 706355 = 1059533) B1059533
theorem B1197875 : Blo 706319 1197875 := bstep (se 1 (by rfl) ⟨898406, by rfl⟩ : syracuseStep 1197875 = 1796813) B1796813
theorem B706371 : Blo 706319 706371 := bstep (se 1 (by rfl) ⟨529778, by rfl⟩ : syracuseStep 706371 = 1059557) B1059557
theorem B706387 : Blo 706319 706387 := bstep (se 1 (by rfl) ⟨529790, by rfl⟩ : syracuseStep 706387 = 1059581) B1059581
theorem B706403 : Blo 706319 706403 := bstep (se 1 (by rfl) ⟨529802, by rfl⟩ : syracuseStep 706403 = 1059605) B1059605
theorem B2017133 : Blo 706319 2017133 := bstep (se 3 (by rfl) ⟨378212, by rfl⟩ : syracuseStep 2017133 = 756425) B756425
theorem B706419 : Blo 706319 706419 := bstep (se 1 (by rfl) ⟨529814, by rfl⟩ : syracuseStep 706419 = 1059629) B1059629
theorem B706435 : Blo 706319 706435 := bstep (se 1 (by rfl) ⟨529826, by rfl⟩ : syracuseStep 706435 = 1059653) B1059653
theorem B706451 : Blo 706319 706451 := bstep (se 1 (by rfl) ⟨529838, by rfl⟩ : syracuseStep 706451 = 1059677) B1059677
theorem B706467 : Blo 706319 706467 := bstep (se 1 (by rfl) ⟨529850, by rfl⟩ : syracuseStep 706467 = 1059701) B1059701
theorem B1591217 : Blo 706319 1591217 := bstep (se 2 (by rfl) ⟨596706, by rfl⟩ : syracuseStep 1591217 = 1193413) B1193413
theorem B706483 : Blo 706319 706483 := bstep (se 1 (by rfl) ⟨529862, by rfl⟩ : syracuseStep 706483 = 1059725) B1059725
theorem B1198003 : Blo 706319 1198003 := bstep (se 1 (by rfl) ⟨898502, by rfl⟩ : syracuseStep 1198003 = 1797005) B1797005
theorem B706499 : Blo 706319 706499 := bstep (se 1 (by rfl) ⟨529874, by rfl⟩ : syracuseStep 706499 = 1059749) B1059749
theorem B1591235 : Blo 706319 1591235 := bstep (se 1 (by rfl) ⟨1193426, by rfl⟩ : syracuseStep 1591235 = 2386853) B2386853
theorem B706515 : Blo 706319 706515 := bstep (se 1 (by rfl) ⟨529886, by rfl⟩ : syracuseStep 706515 = 1059773) B1059773
theorem B706531 : Blo 706319 706531 := bstep (se 1 (by rfl) ⟨529898, by rfl⟩ : syracuseStep 706531 = 1059797) B1059797
theorem B706547 : Blo 706319 706547 := bstep (se 1 (by rfl) ⟨529910, by rfl⟩ : syracuseStep 706547 = 1059821) B1059821
theorem B706563 : Blo 706319 706563 := bstep (se 1 (by rfl) ⟨529922, by rfl⟩ : syracuseStep 706563 = 1059845) B1059845
theorem B706579 : Blo 706319 706579 := bstep (se 1 (by rfl) ⟨529934, by rfl⟩ : syracuseStep 706579 = 1059869) B1059869
theorem B706595 : Blo 706319 706595 := bstep (se 1 (by rfl) ⟨529946, by rfl⟩ : syracuseStep 706595 = 1059893) B1059893
theorem B2017325 : Blo 706319 2017325 := bstep (se 3 (by rfl) ⟨378248, by rfl⟩ : syracuseStep 2017325 = 756497) B756497
theorem B1787953 : Blo 706319 1787953 := bstep (se 2 (by rfl) ⟨670482, by rfl⟩ : syracuseStep 1787953 = 1340965) B1340965
theorem B706611 : Blo 706319 706611 := bstep (se 1 (by rfl) ⟨529958, by rfl⟩ : syracuseStep 706611 = 1059917) B1059917
theorem B1198145 : Blo 706319 1198145 := bstep (se 2 (by rfl) ⟨449304, by rfl⟩ : syracuseStep 1198145 = 898609) B898609
theorem B706627 : Blo 706319 706627 := bstep (se 1 (by rfl) ⟨529970, by rfl⟩ : syracuseStep 706627 = 1059941) B1059941
theorem B706643 : Blo 706319 706643 := bstep (se 1 (by rfl) ⟨529982, by rfl⟩ : syracuseStep 706643 = 1059965) B1059965
theorem B706659 : Blo 706319 706659 := bstep (se 1 (by rfl) ⟨529994, by rfl⟩ : syracuseStep 706659 = 1059989) B1059989
theorem B3590243 : Blo 706319 3590243 := bstep (se 1 (by rfl) ⟨2692682, by rfl⟩ : syracuseStep 3590243 = 5385365) B5385365
theorem B706675 : Blo 706319 706675 := bstep (se 1 (by rfl) ⟨530006, by rfl⟩ : syracuseStep 706675 = 1060013) B1060013
theorem B706691 : Blo 706319 706691 := bstep (se 1 (by rfl) ⟨530018, by rfl⟩ : syracuseStep 706691 = 1060037) B1060037
theorem B6146189 : Blo 706319 6146189 := bstep (se 3 (by rfl) ⟨1152410, by rfl⟩ : syracuseStep 6146189 = 2304821) B2304821
theorem B706707 : Blo 706319 706707 := bstep (se 1 (by rfl) ⟨530030, by rfl⟩ : syracuseStep 706707 = 1060061) B1060061
theorem B706723 : Blo 706319 706723 := bstep (se 1 (by rfl) ⟨530042, by rfl⟩ : syracuseStep 706723 = 1060085) B1060085
theorem B706739 : Blo 706319 706739 := bstep (se 1 (by rfl) ⟨530054, by rfl⟩ : syracuseStep 706739 = 1060109) B1060109
theorem B706755 : Blo 706319 706755 := bstep (se 1 (by rfl) ⟨530066, by rfl⟩ : syracuseStep 706755 = 1060133) B1060133
theorem B1198273 : Blo 706319 1198273 := bstep (se 2 (by rfl) ⟨449352, by rfl⟩ : syracuseStep 1198273 = 898705) B898705
theorem B1591505 : Blo 706319 1591505 := bstep (se 2 (by rfl) ⟨596814, by rfl⟩ : syracuseStep 1591505 = 1193629) B1193629
theorem B706771 : Blo 706319 706771 := bstep (se 1 (by rfl) ⟨530078, by rfl⟩ : syracuseStep 706771 = 1060157) B1060157
theorem B706787 : Blo 706319 706787 := bstep (se 1 (by rfl) ⟨530090, by rfl⟩ : syracuseStep 706787 = 1060181) B1060181
theorem B1591523 : Blo 706319 1591523 := bstep (se 1 (by rfl) ⟨1193642, by rfl⟩ : syracuseStep 1591523 = 2387285) B2387285
theorem B1198307 : Blo 706319 1198307 := bstep (se 1 (by rfl) ⟨898730, by rfl⟩ : syracuseStep 1198307 = 1797461) B1797461
theorem B706803 : Blo 706319 706803 := bstep (se 1 (by rfl) ⟨530102, by rfl⟩ : syracuseStep 706803 = 1060205) B1060205
theorem B706819 : Blo 706319 706819 := bstep (se 1 (by rfl) ⟨530114, by rfl⟩ : syracuseStep 706819 = 1060229) B1060229
theorem B706835 : Blo 706319 706835 := bstep (se 1 (by rfl) ⟨530126, by rfl⟩ : syracuseStep 706835 = 1060253) B1060253
theorem B706851 : Blo 706319 706851 := bstep (se 1 (by rfl) ⟨530138, by rfl⟩ : syracuseStep 706851 = 1060277) B1060277
theorem B1132849 : Blo 706319 1132849 := bstep (se 2 (by rfl) ⟨424818, by rfl⟩ : syracuseStep 1132849 = 849637) B849637
theorem B706867 : Blo 706319 706867 := bstep (se 1 (by rfl) ⟨530150, by rfl⟩ : syracuseStep 706867 = 1060301) B1060301
theorem B1788227 : Blo 706319 1788227 := bstep (se 1 (by rfl) ⟨1341170, by rfl⟩ : syracuseStep 1788227 = 2682341) B2682341
theorem B706883 : Blo 706319 706883 := bstep (se 1 (by rfl) ⟨530162, by rfl⟩ : syracuseStep 706883 = 1060325) B1060325
theorem B706899 : Blo 706319 706899 := bstep (se 1 (by rfl) ⟨530174, by rfl⟩ : syracuseStep 706899 = 1060349) B1060349
theorem B706915 : Blo 706319 706915 := bstep (se 1 (by rfl) ⟨530186, by rfl⟩ : syracuseStep 706915 = 1060373) B1060373
theorem B1198435 : Blo 706319 1198435 := bstep (se 1 (by rfl) ⟨898826, by rfl⟩ : syracuseStep 1198435 = 1797653) B1797653
theorem B706931 : Blo 706319 706931 := bstep (se 1 (by rfl) ⟨530198, by rfl⟩ : syracuseStep 706931 = 1060397) B1060397
theorem B706947 : Blo 706319 706947 := bstep (se 1 (by rfl) ⟨530210, by rfl⟩ : syracuseStep 706947 = 1060421) B1060421
theorem B4540805 : Blo 706319 4540805 := bstep (se 4 (by rfl) ⟨425700, by rfl⟩ : syracuseStep 4540805 = 851401) B851401
theorem B706963 : Blo 706319 706963 := bstep (se 1 (by rfl) ⟨530222, by rfl⟩ : syracuseStep 706963 = 1060445) B1060445
theorem B706979 : Blo 706319 706979 := bstep (se 1 (by rfl) ⟨530234, by rfl⟩ : syracuseStep 706979 = 1060469) B1060469
theorem B706995 : Blo 706319 706995 := bstep (se 1 (by rfl) ⟨530246, by rfl⟩ : syracuseStep 706995 = 1060493) B1060493
theorem B707011 : Blo 706319 707011 := bstep (se 1 (by rfl) ⟨530258, by rfl⟩ : syracuseStep 707011 = 1060517) B1060517
theorem B707027 : Blo 706319 707027 := bstep (se 1 (by rfl) ⟨530270, by rfl⟩ : syracuseStep 707027 = 1060541) B1060541
theorem B707043 : Blo 706319 707043 := bstep (se 1 (by rfl) ⟨530282, by rfl⟩ : syracuseStep 707043 = 1060565) B1060565
theorem B17254883 : Blo 706319 17254883 := bstep (se 1 (by rfl) ⟨12941162, by rfl⟩ : syracuseStep 17254883 = 25882325) B25882325
theorem B1591793 : Blo 706319 1591793 := bstep (se 2 (by rfl) ⟨596922, by rfl⟩ : syracuseStep 1591793 = 1193845) B1193845
theorem B1198577 : Blo 706319 1198577 := bstep (se 2 (by rfl) ⟨449466, by rfl⟩ : syracuseStep 1198577 = 898933) B898933
theorem B707059 : Blo 706319 707059 := bstep (se 1 (by rfl) ⟨530294, by rfl⟩ : syracuseStep 707059 = 1060589) B1060589
theorem B1788419 : Blo 706319 1788419 := bstep (se 1 (by rfl) ⟨1341314, by rfl⟩ : syracuseStep 1788419 = 2682629) B2682629
theorem B707075 : Blo 706319 707075 := bstep (se 1 (by rfl) ⟨530306, by rfl⟩ : syracuseStep 707075 = 1060613) B1060613
theorem B1591811 : Blo 706319 1591811 := bstep (se 1 (by rfl) ⟨1193858, by rfl⟩ : syracuseStep 1591811 = 2387717) B2387717
theorem B707091 : Blo 706319 707091 := bstep (se 1 (by rfl) ⟨530318, by rfl⟩ : syracuseStep 707091 = 1060637) B1060637
theorem B707107 : Blo 706319 707107 := bstep (se 1 (by rfl) ⟨530330, by rfl⟩ : syracuseStep 707107 = 1060661) B1060661
theorem B3820081 : Blo 706319 3820081 := bstep (se 2 (by rfl) ⟨1432530, by rfl⟩ : syracuseStep 3820081 = 2865061) B2865061
theorem B707123 : Blo 706319 707123 := bstep (se 1 (by rfl) ⟨530342, by rfl⟩ : syracuseStep 707123 = 1060685) B1060685
theorem B707139 : Blo 706319 707139 := bstep (se 1 (by rfl) ⟨530354, by rfl⟩ : syracuseStep 707139 = 1060709) B1060709
theorem B1919555 : Blo 706319 1919555 := bstep (se 1 (by rfl) ⟨1439666, by rfl⟩ : syracuseStep 1919555 = 2879333) B2879333
theorem B707155 : Blo 706319 707155 := bstep (se 1 (by rfl) ⟨530366, by rfl⟩ : syracuseStep 707155 = 1060733) B1060733
theorem B707171 : Blo 706319 707171 := bstep (se 1 (by rfl) ⟨530378, by rfl⟩ : syracuseStep 707171 = 1060757) B1060757
theorem B707187 : Blo 706319 707187 := bstep (se 1 (by rfl) ⟨530390, by rfl⟩ : syracuseStep 707187 = 1060781) B1060781
theorem B707203 : Blo 706319 707203 := bstep (se 1 (by rfl) ⟨530402, by rfl⟩ : syracuseStep 707203 = 1060805) B1060805
theorem B707219 : Blo 706319 707219 := bstep (se 1 (by rfl) ⟨530414, by rfl⟩ : syracuseStep 707219 = 1060829) B1060829
theorem B707235 : Blo 706319 707235 := bstep (se 1 (by rfl) ⟨530426, by rfl⟩ : syracuseStep 707235 = 1060853) B1060853
theorem B1821361 : Blo 706319 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B707251 : Blo 706319 707251 := bstep (se 1 (by rfl) ⟨530438, by rfl⟩ : syracuseStep 707251 = 1060877) B1060877
theorem B707267 : Blo 706319 707267 := bstep (se 1 (by rfl) ⟨530450, by rfl⟩ : syracuseStep 707267 = 1060901) B1060901
theorem B707283 : Blo 706319 707283 := bstep (se 1 (by rfl) ⟨530462, by rfl⟩ : syracuseStep 707283 = 1060925) B1060925
theorem B707299 : Blo 706319 707299 := bstep (se 1 (by rfl) ⟨530474, by rfl⟩ : syracuseStep 707299 = 1060949) B1060949
theorem B707315 : Blo 706319 707315 := bstep (se 1 (by rfl) ⟨530486, by rfl⟩ : syracuseStep 707315 = 1060973) B1060973
theorem B707331 : Blo 706319 707331 := bstep (se 1 (by rfl) ⟨530498, by rfl⟩ : syracuseStep 707331 = 1060997) B1060997
theorem B4606733 : Blo 706319 4606733 := bstep (se 3 (by rfl) ⟨863762, by rfl⟩ : syracuseStep 4606733 = 1727525) B1727525
theorem B1592081 : Blo 706319 1592081 := bstep (se 2 (by rfl) ⟨597030, by rfl⟩ : syracuseStep 1592081 = 1194061) B1194061
theorem B707347 : Blo 706319 707347 := bstep (se 1 (by rfl) ⟨530510, by rfl⟩ : syracuseStep 707347 = 1061021) B1061021
theorem B707363 : Blo 706319 707363 := bstep (se 1 (by rfl) ⟨530522, by rfl⟩ : syracuseStep 707363 = 1061045) B1061045
theorem B1592099 : Blo 706319 1592099 := bstep (se 1 (by rfl) ⟨1194074, by rfl⟩ : syracuseStep 1592099 = 2388149) B2388149
theorem B707379 : Blo 706319 707379 := bstep (se 1 (by rfl) ⟨530534, by rfl⟩ : syracuseStep 707379 = 1061069) B1061069
theorem B707395 : Blo 706319 707395 := bstep (se 1 (by rfl) ⟨530546, by rfl⟩ : syracuseStep 707395 = 1061093) B1061093
theorem B707411 : Blo 706319 707411 := bstep (se 1 (by rfl) ⟨530558, by rfl⟩ : syracuseStep 707411 = 1061117) B1061117
theorem B707427 : Blo 706319 707427 := bstep (se 1 (by rfl) ⟨530570, by rfl⟩ : syracuseStep 707427 = 1061141) B1061141
theorem B707443 : Blo 706319 707443 := bstep (se 1 (by rfl) ⟨530582, by rfl⟩ : syracuseStep 707443 = 1061165) B1061165
theorem B707459 : Blo 706319 707459 := bstep (se 1 (by rfl) ⟨530594, by rfl⟩ : syracuseStep 707459 = 1061189) B1061189
theorem B3591053 : Blo 706319 3591053 := bstep (se 3 (by rfl) ⟨673322, by rfl⟩ : syracuseStep 3591053 = 1346645) B1346645
theorem B707475 : Blo 706319 707475 := bstep (se 1 (by rfl) ⟨530606, by rfl⟩ : syracuseStep 707475 = 1061213) B1061213
theorem B707491 : Blo 706319 707491 := bstep (se 1 (by rfl) ⟨530618, by rfl⟩ : syracuseStep 707491 = 1061237) B1061237
theorem B707507 : Blo 706319 707507 := bstep (se 1 (by rfl) ⟨530630, by rfl⟩ : syracuseStep 707507 = 1061261) B1061261
theorem B707523 : Blo 706319 707523 := bstep (se 1 (by rfl) ⟨530642, by rfl⟩ : syracuseStep 707523 = 1061285) B1061285
theorem B707539 : Blo 706319 707539 := bstep (se 1 (by rfl) ⟨530654, by rfl⟩ : syracuseStep 707539 = 1061309) B1061309
theorem B707555 : Blo 706319 707555 := bstep (se 1 (by rfl) ⟨530666, by rfl⟩ : syracuseStep 707555 = 1061333) B1061333
theorem B707571 : Blo 706319 707571 := bstep (se 1 (by rfl) ⟨530678, by rfl⟩ : syracuseStep 707571 = 1061357) B1061357
theorem B707587 : Blo 706319 707587 := bstep (se 1 (by rfl) ⟨530690, by rfl⟩ : syracuseStep 707587 = 1061381) B1061381
theorem B2018317 : Blo 706319 2018317 := bstep (se 3 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 2018317 = 756869) B756869
theorem B707603 : Blo 706319 707603 := bstep (se 1 (by rfl) ⟨530702, by rfl⟩ : syracuseStep 707603 = 1061405) B1061405
theorem B707619 : Blo 706319 707619 := bstep (se 1 (by rfl) ⟨530714, by rfl⟩ : syracuseStep 707619 = 1061429) B1061429
theorem B1592369 : Blo 706319 1592369 := bstep (se 2 (by rfl) ⟨597138, by rfl⟩ : syracuseStep 1592369 = 1194277) B1194277
theorem B707635 : Blo 706319 707635 := bstep (se 1 (by rfl) ⟨530726, by rfl⟩ : syracuseStep 707635 = 1061453) B1061453
theorem B707651 : Blo 706319 707651 := bstep (se 1 (by rfl) ⟨530738, by rfl⟩ : syracuseStep 707651 = 1061477) B1061477
theorem B1592387 : Blo 706319 1592387 := bstep (se 1 (by rfl) ⟨1194290, by rfl⟩ : syracuseStep 1592387 = 2388581) B2388581
theorem B707667 : Blo 706319 707667 := bstep (se 1 (by rfl) ⟨530750, by rfl⟩ : syracuseStep 707667 = 1061501) B1061501
theorem B707683 : Blo 706319 707683 := bstep (se 1 (by rfl) ⟨530762, by rfl⟩ : syracuseStep 707683 = 1061525) B1061525
theorem B707699 : Blo 706319 707699 := bstep (se 1 (by rfl) ⟨530774, by rfl⟩ : syracuseStep 707699 = 1061549) B1061549
theorem B707715 : Blo 706319 707715 := bstep (se 1 (by rfl) ⟨530786, by rfl⟩ : syracuseStep 707715 = 1061573) B1061573
theorem B707731 : Blo 706319 707731 := bstep (se 1 (by rfl) ⟨530798, by rfl⟩ : syracuseStep 707731 = 1061597) B1061597
theorem B707747 : Blo 706319 707747 := bstep (se 1 (by rfl) ⟨530810, by rfl⟩ : syracuseStep 707747 = 1061621) B1061621
theorem B707763 : Blo 706319 707763 := bstep (se 1 (by rfl) ⟨530822, by rfl⟩ : syracuseStep 707763 = 1061645) B1061645
theorem B1133747 : Blo 706319 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B707779 : Blo 706319 707779 := bstep (se 1 (by rfl) ⟨530834, by rfl⟩ : syracuseStep 707779 = 1061669) B1061669
theorem B707795 : Blo 706319 707795 := bstep (se 1 (by rfl) ⟨530846, by rfl⟩ : syracuseStep 707795 = 1061693) B1061693
theorem B707811 : Blo 706319 707811 := bstep (se 1 (by rfl) ⟨530858, by rfl⟩ : syracuseStep 707811 = 1061717) B1061717
theorem B707827 : Blo 706319 707827 := bstep (se 1 (by rfl) ⟨530870, by rfl⟩ : syracuseStep 707827 = 1061741) B1061741
theorem B707843 : Blo 706319 707843 := bstep (se 1 (by rfl) ⟨530882, by rfl⟩ : syracuseStep 707843 = 1061765) B1061765
theorem B707859 : Blo 706319 707859 := bstep (se 1 (by rfl) ⟨530894, by rfl⟩ : syracuseStep 707859 = 1061789) B1061789
theorem B20401429 : Blo 706319 20401429 := bstep (se 6 (by rfl) ⟨478158, by rfl⟩ : syracuseStep 20401429 = 956317) B956317
theorem B707875 : Blo 706319 707875 := bstep (se 1 (by rfl) ⟨530906, by rfl⟩ : syracuseStep 707875 = 1061813) B1061813
theorem B707891 : Blo 706319 707891 := bstep (se 1 (by rfl) ⟨530918, by rfl⟩ : syracuseStep 707891 = 1061837) B1061837
theorem B707907 : Blo 706319 707907 := bstep (se 1 (by rfl) ⟨530930, by rfl⟩ : syracuseStep 707907 = 1061861) B1061861
theorem B1592657 : Blo 706319 1592657 := bstep (se 2 (by rfl) ⟨597246, by rfl⟩ : syracuseStep 1592657 = 1194493) B1194493
theorem B707923 : Blo 706319 707923 := bstep (se 1 (by rfl) ⟨530942, by rfl⟩ : syracuseStep 707923 = 1061885) B1061885
theorem B1592675 : Blo 706319 1592675 := bstep (se 1 (by rfl) ⟨1194506, by rfl⟩ : syracuseStep 1592675 = 2389013) B2389013
theorem B707939 : Blo 706319 707939 := bstep (se 1 (by rfl) ⟨530954, by rfl⟩ : syracuseStep 707939 = 1061909) B1061909
theorem B1133939 : Blo 706319 1133939 := bstep (se 1 (by rfl) ⟨850454, by rfl⟩ : syracuseStep 1133939 = 1700909) B1700909
theorem B707955 : Blo 706319 707955 := bstep (se 1 (by rfl) ⟨530966, by rfl⟩ : syracuseStep 707955 = 1061933) B1061933
theorem B707971 : Blo 706319 707971 := bstep (se 1 (by rfl) ⟨530978, by rfl⟩ : syracuseStep 707971 = 1061957) B1061957
theorem B707987 : Blo 706319 707987 := bstep (se 1 (by rfl) ⟨530990, by rfl⟩ : syracuseStep 707987 = 1061981) B1061981
theorem B708003 : Blo 706319 708003 := bstep (se 1 (by rfl) ⟨531002, by rfl⟩ : syracuseStep 708003 = 1062005) B1062005
theorem B1789361 : Blo 706319 1789361 := bstep (se 2 (by rfl) ⟨671010, by rfl⟩ : syracuseStep 1789361 = 1342021) B1342021
theorem B708019 : Blo 706319 708019 := bstep (se 1 (by rfl) ⟨531014, by rfl⟩ : syracuseStep 708019 = 1062029) B1062029
theorem B708035 : Blo 706319 708035 := bstep (se 1 (by rfl) ⟨531026, by rfl⟩ : syracuseStep 708035 = 1062053) B1062053
theorem B708051 : Blo 706319 708051 := bstep (se 1 (by rfl) ⟨531038, by rfl⟩ : syracuseStep 708051 = 1062077) B1062077
theorem B1789411 : Blo 706319 1789411 := bstep (se 1 (by rfl) ⟨1342058, by rfl⟩ : syracuseStep 1789411 = 2684117) B2684117
theorem B708067 : Blo 706319 708067 := bstep (se 1 (by rfl) ⟨531050, by rfl⟩ : syracuseStep 708067 = 1062101) B1062101
theorem B708083 : Blo 706319 708083 := bstep (se 1 (by rfl) ⟨531062, by rfl⟩ : syracuseStep 708083 = 1062125) B1062125
theorem B708099 : Blo 706319 708099 := bstep (se 1 (by rfl) ⟨531074, by rfl⟩ : syracuseStep 708099 = 1062149) B1062149
theorem B708115 : Blo 706319 708115 := bstep (se 1 (by rfl) ⟨531086, by rfl⟩ : syracuseStep 708115 = 1062173) B1062173
theorem B708131 : Blo 706319 708131 := bstep (se 1 (by rfl) ⟨531098, by rfl⟩ : syracuseStep 708131 = 1062197) B1062197
theorem B708147 : Blo 706319 708147 := bstep (se 1 (by rfl) ⟨531110, by rfl⟩ : syracuseStep 708147 = 1062221) B1062221
theorem B708163 : Blo 706319 708163 := bstep (se 1 (by rfl) ⟨531122, by rfl⟩ : syracuseStep 708163 = 1062245) B1062245
theorem B708179 : Blo 706319 708179 := bstep (se 1 (by rfl) ⟨531134, by rfl⟩ : syracuseStep 708179 = 1062269) B1062269
theorem B708195 : Blo 706319 708195 := bstep (se 1 (by rfl) ⟨531146, by rfl⟩ : syracuseStep 708195 = 1062293) B1062293
theorem B1789553 : Blo 706319 1789553 := bstep (se 2 (by rfl) ⟨671082, by rfl⟩ : syracuseStep 1789553 = 1342165) B1342165
theorem B1592945 : Blo 706319 1592945 := bstep (se 2 (by rfl) ⟨597354, by rfl⟩ : syracuseStep 1592945 = 1194709) B1194709
theorem B708211 : Blo 706319 708211 := bstep (se 1 (by rfl) ⟨531158, by rfl⟩ : syracuseStep 708211 = 1062317) B1062317
theorem B1592963 : Blo 706319 1592963 := bstep (se 1 (by rfl) ⟨1194722, by rfl⟩ : syracuseStep 1592963 = 2389445) B2389445
theorem B708227 : Blo 706319 708227 := bstep (se 1 (by rfl) ⟨531170, by rfl⟩ : syracuseStep 708227 = 1062341) B1062341
theorem B708243 : Blo 706319 708243 := bstep (se 1 (by rfl) ⟨531182, by rfl⟩ : syracuseStep 708243 = 1062365) B1062365
theorem B708259 : Blo 706319 708259 := bstep (se 1 (by rfl) ⟨531194, by rfl⟩ : syracuseStep 708259 = 1062389) B1062389
theorem B708275 : Blo 706319 708275 := bstep (se 1 (by rfl) ⟨531206, by rfl⟩ : syracuseStep 708275 = 1062413) B1062413
theorem B708291 : Blo 706319 708291 := bstep (se 1 (by rfl) ⟨531218, by rfl⟩ : syracuseStep 708291 = 1062437) B1062437
theorem B708307 : Blo 706319 708307 := bstep (se 1 (by rfl) ⟨531230, by rfl⟩ : syracuseStep 708307 = 1062461) B1062461
theorem B708323 : Blo 706319 708323 := bstep (se 1 (by rfl) ⟨531242, by rfl⟩ : syracuseStep 708323 = 1062485) B1062485
theorem B708339 : Blo 706319 708339 := bstep (se 1 (by rfl) ⟨531254, by rfl⟩ : syracuseStep 708339 = 1062509) B1062509
theorem B708355 : Blo 706319 708355 := bstep (se 1 (by rfl) ⟨531266, by rfl⟩ : syracuseStep 708355 = 1062533) B1062533
theorem B708371 : Blo 706319 708371 := bstep (se 1 (by rfl) ⟨531278, by rfl⟩ : syracuseStep 708371 = 1062557) B1062557
theorem B708387 : Blo 706319 708387 := bstep (se 1 (by rfl) ⟨531290, by rfl⟩ : syracuseStep 708387 = 1062581) B1062581
theorem B708403 : Blo 706319 708403 := bstep (se 1 (by rfl) ⟨531302, by rfl⟩ : syracuseStep 708403 = 1062605) B1062605
theorem B708419 : Blo 706319 708419 := bstep (se 1 (by rfl) ⟨531314, by rfl⟩ : syracuseStep 708419 = 1062629) B1062629
theorem B708435 : Blo 706319 708435 := bstep (se 1 (by rfl) ⟨531326, by rfl⟩ : syracuseStep 708435 = 1062653) B1062653
theorem B708451 : Blo 706319 708451 := bstep (se 1 (by rfl) ⟨531338, by rfl⟩ : syracuseStep 708451 = 1062677) B1062677
theorem B708467 : Blo 706319 708467 := bstep (se 1 (by rfl) ⟨531350, by rfl⟩ : syracuseStep 708467 = 1062701) B1062701
theorem B708483 : Blo 706319 708483 := bstep (se 1 (by rfl) ⟨531362, by rfl⟩ : syracuseStep 708483 = 1062725) B1062725
theorem B1593233 : Blo 706319 1593233 := bstep (se 2 (by rfl) ⟨597462, by rfl⟩ : syracuseStep 1593233 = 1194925) B1194925
theorem B708499 : Blo 706319 708499 := bstep (se 1 (by rfl) ⟨531374, by rfl⟩ : syracuseStep 708499 = 1062749) B1062749
theorem B1593251 : Blo 706319 1593251 := bstep (se 1 (by rfl) ⟨1194938, by rfl⟩ : syracuseStep 1593251 = 2389877) B2389877
theorem B708515 : Blo 706319 708515 := bstep (se 1 (by rfl) ⟨531386, by rfl⟩ : syracuseStep 708515 = 1062773) B1062773
theorem B708531 : Blo 706319 708531 := bstep (se 1 (by rfl) ⟨531398, by rfl⟩ : syracuseStep 708531 = 1062797) B1062797
theorem B708547 : Blo 706319 708547 := bstep (se 1 (by rfl) ⟨531410, by rfl⟩ : syracuseStep 708547 = 1062821) B1062821
theorem B3821509 : Blo 706319 3821509 := bstep (se 4 (by rfl) ⟨358266, by rfl⟩ : syracuseStep 3821509 = 716533) B716533
theorem B708563 : Blo 706319 708563 := bstep (se 1 (by rfl) ⟨531422, by rfl⟩ : syracuseStep 708563 = 1062845) B1062845
theorem B708579 : Blo 706319 708579 := bstep (se 1 (by rfl) ⟨531434, by rfl⟩ : syracuseStep 708579 = 1062869) B1062869
theorem B708595 : Blo 706319 708595 := bstep (se 1 (by rfl) ⟨531446, by rfl⟩ : syracuseStep 708595 = 1062893) B1062893
theorem B708611 : Blo 706319 708611 := bstep (se 1 (by rfl) ⟨531458, by rfl⟩ : syracuseStep 708611 = 1062917) B1062917
theorem B708627 : Blo 706319 708627 := bstep (se 1 (by rfl) ⟨531470, by rfl⟩ : syracuseStep 708627 = 1062941) B1062941
theorem B708643 : Blo 706319 708643 := bstep (se 1 (by rfl) ⟨531482, by rfl⟩ : syracuseStep 708643 = 1062965) B1062965
theorem B708659 : Blo 706319 708659 := bstep (se 1 (by rfl) ⟨531494, by rfl⟩ : syracuseStep 708659 = 1062989) B1062989
theorem B708675 : Blo 706319 708675 := bstep (se 1 (by rfl) ⟨531506, by rfl⟩ : syracuseStep 708675 = 1063013) B1063013
theorem B1364035 : Blo 706319 1364035 := bstep (se 1 (by rfl) ⟨1023026, by rfl⟩ : syracuseStep 1364035 = 2046053) B2046053
theorem B708691 : Blo 706319 708691 := bstep (se 1 (by rfl) ⟨531518, by rfl⟩ : syracuseStep 708691 = 1063037) B1063037
theorem B708707 : Blo 706319 708707 := bstep (se 1 (by rfl) ⟨531530, by rfl⟩ : syracuseStep 708707 = 1063061) B1063061
theorem B3821681 : Blo 706319 3821681 := bstep (se 2 (by rfl) ⟨1433130, by rfl⟩ : syracuseStep 3821681 = 2866261) B2866261
theorem B708723 : Blo 706319 708723 := bstep (se 1 (by rfl) ⟨531542, by rfl⟩ : syracuseStep 708723 = 1063085) B1063085
theorem B708739 : Blo 706319 708739 := bstep (se 1 (by rfl) ⟨531554, by rfl⟩ : syracuseStep 708739 = 1063109) B1063109
theorem B708755 : Blo 706319 708755 := bstep (se 1 (by rfl) ⟨531566, by rfl⟩ : syracuseStep 708755 = 1063133) B1063133
theorem B708771 : Blo 706319 708771 := bstep (se 1 (by rfl) ⟨531578, by rfl⟩ : syracuseStep 708771 = 1063157) B1063157
theorem B1593521 : Blo 706319 1593521 := bstep (se 2 (by rfl) ⟨597570, by rfl⟩ : syracuseStep 1593521 = 1195141) B1195141
theorem B708787 : Blo 706319 708787 := bstep (se 1 (by rfl) ⟨531590, by rfl⟩ : syracuseStep 708787 = 1063181) B1063181
theorem B1593539 : Blo 706319 1593539 := bstep (se 1 (by rfl) ⟨1195154, by rfl⟩ : syracuseStep 1593539 = 2390309) B2390309
theorem B708803 : Blo 706319 708803 := bstep (se 1 (by rfl) ⟨531602, by rfl⟩ : syracuseStep 708803 = 1063205) B1063205
theorem B708819 : Blo 706319 708819 := bstep (se 1 (by rfl) ⟨531614, by rfl⟩ : syracuseStep 708819 = 1063229) B1063229
theorem B708835 : Blo 706319 708835 := bstep (se 1 (by rfl) ⟨531626, by rfl⟩ : syracuseStep 708835 = 1063253) B1063253
theorem B708851 : Blo 706319 708851 := bstep (se 1 (by rfl) ⟨531638, by rfl⟩ : syracuseStep 708851 = 1063277) B1063277
theorem B708867 : Blo 706319 708867 := bstep (se 1 (by rfl) ⟨531650, by rfl⟩ : syracuseStep 708867 = 1063301) B1063301
theorem B4837637 : Blo 706319 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B708883 : Blo 706319 708883 := bstep (se 1 (by rfl) ⟨531662, by rfl⟩ : syracuseStep 708883 = 1063325) B1063325
theorem B708899 : Blo 706319 708899 := bstep (se 1 (by rfl) ⟨531674, by rfl⟩ : syracuseStep 708899 = 1063349) B1063349
theorem B708915 : Blo 706319 708915 := bstep (se 1 (by rfl) ⟨531686, by rfl⟩ : syracuseStep 708915 = 1063373) B1063373
theorem B1134913 : Blo 706319 1134913 := bstep (se 2 (by rfl) ⟨425592, by rfl⟩ : syracuseStep 1134913 = 851185) B851185
theorem B708931 : Blo 706319 708931 := bstep (se 1 (by rfl) ⟨531698, by rfl⟩ : syracuseStep 708931 = 1063397) B1063397
theorem B708947 : Blo 706319 708947 := bstep (se 1 (by rfl) ⟨531710, by rfl⟩ : syracuseStep 708947 = 1063421) B1063421
theorem B708963 : Blo 706319 708963 := bstep (se 1 (by rfl) ⟨531722, by rfl⟩ : syracuseStep 708963 = 1063445) B1063445
theorem B708979 : Blo 706319 708979 := bstep (se 1 (by rfl) ⟨531734, by rfl⟩ : syracuseStep 708979 = 1063469) B1063469
theorem B708995 : Blo 706319 708995 := bstep (se 1 (by rfl) ⟨531746, by rfl⟩ : syracuseStep 708995 = 1063493) B1063493
theorem B709011 : Blo 706319 709011 := bstep (se 1 (by rfl) ⟨531758, by rfl⟩ : syracuseStep 709011 = 1063517) B1063517
theorem B709027 : Blo 706319 709027 := bstep (se 1 (by rfl) ⟨531770, by rfl⟩ : syracuseStep 709027 = 1063541) B1063541
theorem B709043 : Blo 706319 709043 := bstep (se 1 (by rfl) ⟨531782, by rfl⟩ : syracuseStep 709043 = 1063565) B1063565
theorem B709059 : Blo 706319 709059 := bstep (se 1 (by rfl) ⟨531794, by rfl⟩ : syracuseStep 709059 = 1063589) B1063589
theorem B1593809 : Blo 706319 1593809 := bstep (se 2 (by rfl) ⟨597678, by rfl⟩ : syracuseStep 1593809 = 1195357) B1195357
theorem B709075 : Blo 706319 709075 := bstep (se 1 (by rfl) ⟨531806, by rfl⟩ : syracuseStep 709075 = 1063613) B1063613
theorem B6803939 : Blo 706319 6803939 := bstep (se 1 (by rfl) ⟨5102954, by rfl⟩ : syracuseStep 6803939 = 10205909) B10205909
theorem B1593827 : Blo 706319 1593827 := bstep (se 1 (by rfl) ⟨1195370, by rfl⟩ : syracuseStep 1593827 = 2390741) B2390741
theorem B709091 : Blo 706319 709091 := bstep (se 1 (by rfl) ⟨531818, by rfl⟩ : syracuseStep 709091 = 1063637) B1063637
theorem B709107 : Blo 706319 709107 := bstep (se 1 (by rfl) ⟨531830, by rfl⟩ : syracuseStep 709107 = 1063661) B1063661
theorem B709123 : Blo 706319 709123 := bstep (se 1 (by rfl) ⟨531842, by rfl⟩ : syracuseStep 709123 = 1063685) B1063685
theorem B709139 : Blo 706319 709139 := bstep (se 1 (by rfl) ⟨531854, by rfl⟩ : syracuseStep 709139 = 1063709) B1063709
theorem B709155 : Blo 706319 709155 := bstep (se 1 (by rfl) ⟨531866, by rfl⟩ : syracuseStep 709155 = 1063733) B1063733
theorem B709171 : Blo 706319 709171 := bstep (se 1 (by rfl) ⟨531878, by rfl⟩ : syracuseStep 709171 = 1063757) B1063757
theorem B709187 : Blo 706319 709187 := bstep (se 1 (by rfl) ⟨531890, by rfl⟩ : syracuseStep 709187 = 1063781) B1063781
theorem B1790545 : Blo 706319 1790545 := bstep (se 2 (by rfl) ⟨671454, by rfl⟩ : syracuseStep 1790545 = 1342909) B1342909
theorem B709203 : Blo 706319 709203 := bstep (se 1 (by rfl) ⟨531902, by rfl⟩ : syracuseStep 709203 = 1063805) B1063805
theorem B709219 : Blo 706319 709219 := bstep (se 1 (by rfl) ⟨531914, by rfl⟩ : syracuseStep 709219 = 1063829) B1063829
theorem B709235 : Blo 706319 709235 := bstep (se 1 (by rfl) ⟨531926, by rfl⟩ : syracuseStep 709235 = 1063853) B1063853
theorem B709251 : Blo 706319 709251 := bstep (se 1 (by rfl) ⟨531938, by rfl⟩ : syracuseStep 709251 = 1063877) B1063877
theorem B13652621 : Blo 706319 13652621 := bstep (se 3 (by rfl) ⟨2559866, by rfl⟩ : syracuseStep 13652621 = 5119733) B5119733
theorem B709267 : Blo 706319 709267 := bstep (se 1 (by rfl) ⟨531950, by rfl⟩ : syracuseStep 709267 = 1063901) B1063901
theorem B709283 : Blo 706319 709283 := bstep (se 1 (by rfl) ⟨531962, by rfl⟩ : syracuseStep 709283 = 1063925) B1063925
theorem B709299 : Blo 706319 709299 := bstep (se 1 (by rfl) ⟨531974, by rfl⟩ : syracuseStep 709299 = 1063949) B1063949
theorem B709315 : Blo 706319 709315 := bstep (se 1 (by rfl) ⟨531986, by rfl⟩ : syracuseStep 709315 = 1063973) B1063973
theorem B2020049 : Blo 706319 2020049 := bstep (se 2 (by rfl) ⟨757518, by rfl⟩ : syracuseStep 2020049 = 1515037) B1515037
theorem B709331 : Blo 706319 709331 := bstep (se 1 (by rfl) ⟨531998, by rfl⟩ : syracuseStep 709331 = 1063997) B1063997
theorem B709347 : Blo 706319 709347 := bstep (se 1 (by rfl) ⟨532010, by rfl⟩ : syracuseStep 709347 = 1064021) B1064021
theorem B1594097 : Blo 706319 1594097 := bstep (se 2 (by rfl) ⟨597786, by rfl⟩ : syracuseStep 1594097 = 1195573) B1195573
theorem B709363 : Blo 706319 709363 := bstep (se 1 (by rfl) ⟨532022, by rfl⟩ : syracuseStep 709363 = 1064045) B1064045
theorem B1135361 : Blo 706319 1135361 := bstep (se 2 (by rfl) ⟨425760, by rfl⟩ : syracuseStep 1135361 = 851521) B851521
theorem B1594115 : Blo 706319 1594115 := bstep (se 1 (by rfl) ⟨1195586, by rfl⟩ : syracuseStep 1594115 = 2391173) B2391173
theorem B709379 : Blo 706319 709379 := bstep (se 1 (by rfl) ⟨532034, by rfl⟩ : syracuseStep 709379 = 1064069) B1064069
theorem B709395 : Blo 706319 709395 := bstep (se 1 (by rfl) ⟨532046, by rfl⟩ : syracuseStep 709395 = 1064093) B1064093
theorem B709411 : Blo 706319 709411 := bstep (se 1 (by rfl) ⟨532058, by rfl⟩ : syracuseStep 709411 = 1064117) B1064117
theorem B709427 : Blo 706319 709427 := bstep (se 1 (by rfl) ⟨532070, by rfl⟩ : syracuseStep 709427 = 1064141) B1064141
theorem B709443 : Blo 706319 709443 := bstep (se 1 (by rfl) ⟨532082, by rfl⟩ : syracuseStep 709443 = 1064165) B1064165
theorem B709459 : Blo 706319 709459 := bstep (se 1 (by rfl) ⟨532094, by rfl⟩ : syracuseStep 709459 = 1064189) B1064189
theorem B1790819 : Blo 706319 1790819 := bstep (se 1 (by rfl) ⟨1343114, by rfl⟩ : syracuseStep 1790819 = 2686229) B2686229
theorem B709475 : Blo 706319 709475 := bstep (se 1 (by rfl) ⟨532106, by rfl⟩ : syracuseStep 709475 = 1064213) B1064213
theorem B709491 : Blo 706319 709491 := bstep (se 1 (by rfl) ⟨532118, by rfl⟩ : syracuseStep 709491 = 1064237) B1064237
theorem B709507 : Blo 706319 709507 := bstep (se 1 (by rfl) ⟨532130, by rfl⟩ : syracuseStep 709507 = 1064261) B1064261
theorem B9065357 : Blo 706319 9065357 := bstep (se 3 (by rfl) ⟨1699754, by rfl⟩ : syracuseStep 9065357 = 3399509) B3399509
theorem B2020241 : Blo 706319 2020241 := bstep (se 2 (by rfl) ⟨757590, by rfl⟩ : syracuseStep 2020241 = 1515181) B1515181
theorem B709523 : Blo 706319 709523 := bstep (se 1 (by rfl) ⟨532142, by rfl⟩ : syracuseStep 709523 = 1064285) B1064285
theorem B709539 : Blo 706319 709539 := bstep (se 1 (by rfl) ⟨532154, by rfl⟩ : syracuseStep 709539 = 1064309) B1064309
theorem B709555 : Blo 706319 709555 := bstep (se 1 (by rfl) ⟨532166, by rfl⟩ : syracuseStep 709555 = 1064333) B1064333
theorem B709571 : Blo 706319 709571 := bstep (se 1 (by rfl) ⟨532178, by rfl⟩ : syracuseStep 709571 = 1064357) B1064357
theorem B709587 : Blo 706319 709587 := bstep (se 1 (by rfl) ⟨532190, by rfl⟩ : syracuseStep 709587 = 1064381) B1064381
theorem B709603 : Blo 706319 709603 := bstep (se 1 (by rfl) ⟨532202, by rfl⟩ : syracuseStep 709603 = 1064405) B1064405
theorem B709619 : Blo 706319 709619 := bstep (se 1 (by rfl) ⟨532214, by rfl⟩ : syracuseStep 709619 = 1064429) B1064429
theorem B709635 : Blo 706319 709635 := bstep (se 1 (by rfl) ⟨532226, by rfl⟩ : syracuseStep 709635 = 1064453) B1064453
theorem B1594385 : Blo 706319 1594385 := bstep (se 2 (by rfl) ⟨597894, by rfl⟩ : syracuseStep 1594385 = 1195789) B1195789
theorem B709651 : Blo 706319 709651 := bstep (se 1 (by rfl) ⟨532238, by rfl⟩ : syracuseStep 709651 = 1064477) B1064477
theorem B1791011 : Blo 706319 1791011 := bstep (se 1 (by rfl) ⟨1343258, by rfl⟩ : syracuseStep 1791011 = 2686517) B2686517
theorem B1594403 : Blo 706319 1594403 := bstep (se 1 (by rfl) ⟨1195802, by rfl⟩ : syracuseStep 1594403 = 2391605) B2391605
theorem B709667 : Blo 706319 709667 := bstep (se 1 (by rfl) ⟨532250, by rfl⟩ : syracuseStep 709667 = 1064501) B1064501
theorem B709683 : Blo 706319 709683 := bstep (se 1 (by rfl) ⟨532262, by rfl⟩ : syracuseStep 709683 = 1064525) B1064525
theorem B709699 : Blo 706319 709699 := bstep (se 1 (by rfl) ⟨532274, by rfl⟩ : syracuseStep 709699 = 1064549) B1064549
theorem B709715 : Blo 706319 709715 := bstep (se 1 (by rfl) ⟨532286, by rfl⟩ : syracuseStep 709715 = 1064573) B1064573
theorem B709731 : Blo 706319 709731 := bstep (se 1 (by rfl) ⟨532298, by rfl⟩ : syracuseStep 709731 = 1064597) B1064597
theorem B709747 : Blo 706319 709747 := bstep (se 1 (by rfl) ⟨532310, by rfl⟩ : syracuseStep 709747 = 1064621) B1064621
theorem B709763 : Blo 706319 709763 := bstep (se 1 (by rfl) ⟨532322, by rfl⟩ : syracuseStep 709763 = 1064645) B1064645
theorem B709779 : Blo 706319 709779 := bstep (se 1 (by rfl) ⟨532334, by rfl⟩ : syracuseStep 709779 = 1064669) B1064669
theorem B709795 : Blo 706319 709795 := bstep (se 1 (by rfl) ⟨532346, by rfl⟩ : syracuseStep 709795 = 1064693) B1064693
theorem B709811 : Blo 706319 709811 := bstep (se 1 (by rfl) ⟨532358, by rfl⟩ : syracuseStep 709811 = 1064717) B1064717
theorem B709827 : Blo 706319 709827 := bstep (se 1 (by rfl) ⟨532370, by rfl⟩ : syracuseStep 709827 = 1064741) B1064741
theorem B709843 : Blo 706319 709843 := bstep (se 1 (by rfl) ⟨532382, by rfl⟩ : syracuseStep 709843 = 1064765) B1064765
theorem B709859 : Blo 706319 709859 := bstep (se 1 (by rfl) ⟨532394, by rfl⟩ : syracuseStep 709859 = 1064789) B1064789
theorem B709875 : Blo 706319 709875 := bstep (se 1 (by rfl) ⟨532406, by rfl⟩ : syracuseStep 709875 = 1064813) B1064813
theorem B709891 : Blo 706319 709891 := bstep (se 1 (by rfl) ⟨532418, by rfl⟩ : syracuseStep 709891 = 1064837) B1064837
theorem B709907 : Blo 706319 709907 := bstep (se 1 (by rfl) ⟨532430, by rfl⟩ : syracuseStep 709907 = 1064861) B1064861
theorem B709923 : Blo 706319 709923 := bstep (se 1 (by rfl) ⟨532442, by rfl⟩ : syracuseStep 709923 = 1064885) B1064885
theorem B1594673 : Blo 706319 1594673 := bstep (se 2 (by rfl) ⟨598002, by rfl⟩ : syracuseStep 1594673 = 1196005) B1196005
theorem B709939 : Blo 706319 709939 := bstep (se 1 (by rfl) ⟨532454, by rfl⟩ : syracuseStep 709939 = 1064909) B1064909
theorem B1594691 : Blo 706319 1594691 := bstep (se 1 (by rfl) ⟨1196018, by rfl⟩ : syracuseStep 1594691 = 2392037) B2392037
theorem B709955 : Blo 706319 709955 := bstep (se 1 (by rfl) ⟨532466, by rfl⟩ : syracuseStep 709955 = 1064933) B1064933
theorem B709971 : Blo 706319 709971 := bstep (se 1 (by rfl) ⟨532478, by rfl⟩ : syracuseStep 709971 = 1064957) B1064957
theorem B709987 : Blo 706319 709987 := bstep (se 1 (by rfl) ⟨532490, by rfl⟩ : syracuseStep 709987 = 1064981) B1064981
theorem B710003 : Blo 706319 710003 := bstep (se 1 (by rfl) ⟨532502, by rfl⟩ : syracuseStep 710003 = 1065005) B1065005
theorem B710019 : Blo 706319 710019 := bstep (se 1 (by rfl) ⟨532514, by rfl⟩ : syracuseStep 710019 = 1065029) B1065029
theorem B710035 : Blo 706319 710035 := bstep (se 1 (by rfl) ⟨532526, by rfl⟩ : syracuseStep 710035 = 1065053) B1065053
theorem B710051 : Blo 706319 710051 := bstep (se 1 (by rfl) ⟨532538, by rfl⟩ : syracuseStep 710051 = 1065077) B1065077
theorem B710067 : Blo 706319 710067 := bstep (se 1 (by rfl) ⟨532550, by rfl⟩ : syracuseStep 710067 = 1065101) B1065101
theorem B710083 : Blo 706319 710083 := bstep (se 1 (by rfl) ⟨532562, by rfl⟩ : syracuseStep 710083 = 1065125) B1065125
theorem B8639941 : Blo 706319 8639941 := bstep (se 4 (by rfl) ⟨809994, by rfl⟩ : syracuseStep 8639941 = 1619989) B1619989
theorem B710099 : Blo 706319 710099 := bstep (se 1 (by rfl) ⟨532574, by rfl⟩ : syracuseStep 710099 = 1065149) B1065149
theorem B710115 : Blo 706319 710115 := bstep (se 1 (by rfl) ⟨532586, by rfl⟩ : syracuseStep 710115 = 1065173) B1065173
theorem B710131 : Blo 706319 710131 := bstep (se 1 (by rfl) ⟨532598, by rfl⟩ : syracuseStep 710131 = 1065197) B1065197
theorem B710147 : Blo 706319 710147 := bstep (se 1 (by rfl) ⟨532610, by rfl⟩ : syracuseStep 710147 = 1065221) B1065221
theorem B3823109 : Blo 706319 3823109 := bstep (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) B716833
theorem B710163 : Blo 706319 710163 := bstep (se 1 (by rfl) ⟨532622, by rfl⟩ : syracuseStep 710163 = 1065245) B1065245
theorem B710179 : Blo 706319 710179 := bstep (se 1 (by rfl) ⟨532634, by rfl⟩ : syracuseStep 710179 = 1065269) B1065269
theorem B710195 : Blo 706319 710195 := bstep (se 1 (by rfl) ⟨532646, by rfl⟩ : syracuseStep 710195 = 1065293) B1065293
theorem B710211 : Blo 706319 710211 := bstep (se 1 (by rfl) ⟨532658, by rfl⟩ : syracuseStep 710211 = 1065317) B1065317
theorem B1594961 : Blo 706319 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B710227 : Blo 706319 710227 := bstep (se 1 (by rfl) ⟨532670, by rfl⟩ : syracuseStep 710227 = 1065341) B1065341
theorem B4839011 : Blo 706319 4839011 := bstep (se 1 (by rfl) ⟨3629258, by rfl⟩ : syracuseStep 4839011 = 7258517) B7258517
theorem B1594979 : Blo 706319 1594979 := bstep (se 1 (by rfl) ⟨1196234, by rfl⟩ : syracuseStep 1594979 = 2392469) B2392469
theorem B710243 : Blo 706319 710243 := bstep (se 1 (by rfl) ⟨532682, by rfl⟩ : syracuseStep 710243 = 1065365) B1065365
theorem B710259 : Blo 706319 710259 := bstep (se 1 (by rfl) ⟨532694, by rfl⟩ : syracuseStep 710259 = 1065389) B1065389
theorem B710275 : Blo 706319 710275 := bstep (se 1 (by rfl) ⟨532706, by rfl⟩ : syracuseStep 710275 = 1065413) B1065413
theorem B710291 : Blo 706319 710291 := bstep (se 1 (by rfl) ⟨532718, by rfl⟩ : syracuseStep 710291 = 1065437) B1065437
theorem B710307 : Blo 706319 710307 := bstep (se 1 (by rfl) ⟨532730, by rfl⟩ : syracuseStep 710307 = 1065461) B1065461
theorem B3593969 : Blo 706319 3593969 := bstep (se 2 (by rfl) ⟨1347738, by rfl⟩ : syracuseStep 3593969 = 2695477) B2695477
theorem B1595249 : Blo 706319 1595249 := bstep (se 2 (by rfl) ⟨598218, by rfl⟩ : syracuseStep 1595249 = 1196437) B1196437
theorem B2021233 : Blo 706319 2021233 := bstep (se 2 (by rfl) ⟨757962, by rfl⟩ : syracuseStep 2021233 = 1515925) B1515925
theorem B1595267 : Blo 706319 1595267 := bstep (se 1 (by rfl) ⟨1196450, by rfl⟩ : syracuseStep 1595267 = 2392901) B2392901
theorem B22763405 : Blo 706319 22763405 := bstep (se 3 (by rfl) ⟨4268138, by rfl⟩ : syracuseStep 22763405 = 8536277) B8536277
theorem B1791953 : Blo 706319 1791953 := bstep (se 2 (by rfl) ⟨671982, by rfl⟩ : syracuseStep 1791953 = 1343965) B1343965
theorem B1792003 : Blo 706319 1792003 := bstep (se 1 (by rfl) ⟨1344002, by rfl⟩ : syracuseStep 1792003 = 2688005) B2688005
theorem B1136771 : Blo 706319 1136771 := bstep (se 1 (by rfl) ⟨852578, by rfl⟩ : syracuseStep 1136771 = 1705157) B1705157
theorem B2021507 : Blo 706319 2021507 := bstep (se 1 (by rfl) ⟨1516130, by rfl⟩ : syracuseStep 2021507 = 3032261) B3032261
theorem B3823757 : Blo 706319 3823757 := bstep (se 3 (by rfl) ⟨716954, by rfl⟩ : syracuseStep 3823757 = 1433909) B1433909
theorem B1792145 : Blo 706319 1792145 := bstep (se 2 (by rfl) ⟨672054, by rfl⟩ : syracuseStep 1792145 = 1344109) B1344109
theorem B1595537 : Blo 706319 1595537 := bstep (se 2 (by rfl) ⟨598326, by rfl⟩ : syracuseStep 1595537 = 1196653) B1196653
theorem B4839587 : Blo 706319 4839587 := bstep (se 1 (by rfl) ⟨3629690, by rfl⟩ : syracuseStep 4839587 = 7259381) B7259381
theorem B1595555 : Blo 706319 1595555 := bstep (se 1 (by rfl) ⟨1196666, by rfl⟩ : syracuseStep 1595555 = 2393333) B2393333
theorem B5363981 : Blo 706319 5363981 := bstep (se 3 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 5363981 = 2011493) B2011493
theorem B1136963 : Blo 706319 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B2021699 : Blo 706319 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B1595825 : Blo 706319 1595825 := bstep (se 2 (by rfl) ⟨598434, by rfl⟩ : syracuseStep 1595825 = 1196869) B1196869
theorem B1595843 : Blo 706319 1595843 := bstep (se 1 (by rfl) ⟨1196882, by rfl⟩ : syracuseStep 1595843 = 2393765) B2393765
theorem B809411 : Blo 706319 809411 := bstep (se 1 (by rfl) ⟨607058, by rfl⟩ : syracuseStep 809411 = 1214117) B1214117
theorem B1596113 : Blo 706319 1596113 := bstep (se 2 (by rfl) ⟨598542, by rfl⟩ : syracuseStep 1596113 = 1197085) B1197085
theorem B1596131 : Blo 706319 1596131 := bstep (se 1 (by rfl) ⟨1197098, by rfl⟩ : syracuseStep 1596131 = 2394197) B2394197
theorem B1006339 : Blo 706319 1006339 := bstep (se 1 (by rfl) ⟨754754, by rfl⟩ : syracuseStep 1006339 = 1509509) B1509509
theorem B908083 : Blo 706319 908083 := bstep (se 1 (by rfl) ⟨681062, by rfl⟩ : syracuseStep 908083 = 1362125) B1362125
theorem B1596401 : Blo 706319 1596401 := bstep (se 2 (by rfl) ⟨598650, by rfl⟩ : syracuseStep 1596401 = 1197301) B1197301
theorem B1596419 : Blo 706319 1596419 := bstep (se 1 (by rfl) ⟨1197314, by rfl⟩ : syracuseStep 1596419 = 2394629) B2394629
theorem B2022509 : Blo 706319 2022509 := bstep (se 3 (by rfl) ⟨379220, by rfl⟩ : syracuseStep 2022509 = 758441) B758441
theorem B1793137 : Blo 706319 1793137 := bstep (se 2 (by rfl) ⟨672426, by rfl⟩ : syracuseStep 1793137 = 1344853) B1344853
theorem B3595427 : Blo 706319 3595427 := bstep (se 1 (by rfl) ⟨2696570, by rfl⟩ : syracuseStep 3595427 = 5393141) B5393141
theorem B2546893 : Blo 706319 2546893 := bstep (se 3 (by rfl) ⟨477542, by rfl⟩ : syracuseStep 2546893 = 955085) B955085
theorem B1596689 : Blo 706319 1596689 := bstep (se 2 (by rfl) ⟨598758, by rfl⟩ : syracuseStep 1596689 = 1197517) B1197517
theorem B1596707 : Blo 706319 1596707 := bstep (se 1 (by rfl) ⟨1197530, by rfl⟩ : syracuseStep 1596707 = 2395061) B2395061
theorem B2022691 : Blo 706319 2022691 := bstep (se 1 (by rfl) ⟨1517018, by rfl⟩ : syracuseStep 2022691 = 3034037) B3034037
theorem B1793411 : Blo 706319 1793411 := bstep (se 1 (by rfl) ⟨1345058, by rfl⟩ : syracuseStep 1793411 = 2690117) B2690117
theorem B1531345 : Blo 706319 1531345 := bstep (se 2 (by rfl) ⟨574254, by rfl⟩ : syracuseStep 1531345 = 1148509) B1148509
theorem B1596977 : Blo 706319 1596977 := bstep (se 2 (by rfl) ⟨598866, by rfl⟩ : syracuseStep 1596977 = 1197733) B1197733
theorem B1793603 : Blo 706319 1793603 := bstep (se 1 (by rfl) ⟨1345202, by rfl⟩ : syracuseStep 1793603 = 2690405) B2690405
theorem B1596995 : Blo 706319 1596995 := bstep (se 1 (by rfl) ⟨1197746, by rfl⟩ : syracuseStep 1596995 = 2395493) B2395493
theorem B2875085 : Blo 706319 2875085 := bstep (se 3 (by rfl) ⟨539078, by rfl⟩ : syracuseStep 2875085 = 1078157) B1078157
theorem B3825443 : Blo 706319 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B8052533 : Blo 706319 8052533 := bstep (se 5 (by rfl) ⟨377462, by rfl⟩ : syracuseStep 8052533 = 754925) B754925
theorem B1597265 : Blo 706319 1597265 := bstep (se 2 (by rfl) ⟨598974, by rfl⟩ : syracuseStep 1597265 = 1197949) B1197949
theorem B1597283 : Blo 706319 1597283 := bstep (se 1 (by rfl) ⟨1197962, by rfl⟩ : syracuseStep 1597283 = 2395925) B2395925
theorem B1007473 : Blo 706319 1007473 := bstep (se 2 (by rfl) ⟨377802, by rfl⟩ : syracuseStep 1007473 = 755605) B755605
theorem B1007569 : Blo 706319 1007569 := bstep (se 2 (by rfl) ⟨377838, by rfl⟩ : syracuseStep 1007569 = 755677) B755677
theorem B5103587 : Blo 706319 5103587 := bstep (se 1 (by rfl) ⟨3827690, by rfl⟩ : syracuseStep 5103587 = 7655381) B7655381
theorem B1597553 : Blo 706319 1597553 := bstep (se 2 (by rfl) ⟨599082, by rfl⟩ : syracuseStep 1597553 = 1198165) B1198165
theorem B1597571 : Blo 706319 1597571 := bstep (se 1 (by rfl) ⟨1198178, by rfl⟩ : syracuseStep 1597571 = 2396357) B2396357
theorem B2384045 : Blo 706319 2384045 := bstep (se 3 (by rfl) ⟨447008, by rfl⟩ : syracuseStep 2384045 = 894017) B894017
theorem B2384099 : Blo 706319 2384099 := bstep (se 1 (by rfl) ⟨1788074, by rfl⟩ : syracuseStep 2384099 = 3576149) B3576149
theorem B7659845 : Blo 706319 7659845 := bstep (se 4 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 7659845 = 1436221) B1436221
theorem B1597841 : Blo 706319 1597841 := bstep (se 2 (by rfl) ⟨599190, by rfl⟩ : syracuseStep 1597841 = 1198381) B1198381
theorem B4546979 : Blo 706319 4546979 := bstep (se 1 (by rfl) ⟨3410234, by rfl⟩ : syracuseStep 4546979 = 6820469) B6820469
theorem B1597859 : Blo 706319 1597859 := bstep (se 1 (by rfl) ⟨1198394, by rfl⟩ : syracuseStep 1597859 = 2396789) B2396789
theorem B1008065 : Blo 706319 1008065 := bstep (se 2 (by rfl) ⟨378024, by rfl⟩ : syracuseStep 1008065 = 756049) B756049
theorem B3400163 : Blo 706319 3400163 := bstep (se 1 (by rfl) ⟨2550122, by rfl⟩ : syracuseStep 3400163 = 5100245) B5100245
theorem B2384369 : Blo 706319 2384369 := bstep (se 2 (by rfl) ⟨894138, by rfl⟩ : syracuseStep 2384369 = 1788277) B1788277
theorem B1794545 : Blo 706319 1794545 := bstep (se 2 (by rfl) ⟨672954, by rfl⟩ : syracuseStep 1794545 = 1345909) B1345909
theorem B1794595 : Blo 706319 1794595 := bstep (se 1 (by rfl) ⟨1345946, by rfl⟩ : syracuseStep 1794595 = 2691893) B2691893
theorem B1794737 : Blo 706319 1794737 := bstep (se 2 (by rfl) ⟨673026, by rfl⟩ : syracuseStep 1794737 = 1346053) B1346053
theorem B1598129 : Blo 706319 1598129 := bstep (se 2 (by rfl) ⟨599298, by rfl⟩ : syracuseStep 1598129 = 1198597) B1198597
theorem B1598147 : Blo 706319 1598147 := bstep (se 1 (by rfl) ⟨1198610, by rfl⟩ : syracuseStep 1598147 = 2397221) B2397221
theorem B5104397 : Blo 706319 5104397 := bstep (se 3 (by rfl) ⟨957074, by rfl⟩ : syracuseStep 5104397 = 1914149) B1914149
theorem B3629873 : Blo 706319 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B4547441 : Blo 706319 4547441 := bstep (se 2 (by rfl) ⟨1705290, by rfl⟩ : syracuseStep 4547441 = 3410581) B3410581
theorem B2384909 : Blo 706319 2384909 := bstep (se 3 (by rfl) ⟨447170, by rfl⟩ : syracuseStep 2384909 = 894341) B894341
theorem B2384963 : Blo 706319 2384963 := bstep (se 1 (by rfl) ⟨1788722, by rfl⟩ : syracuseStep 2384963 = 3577445) B3577445
theorem B5366897 : Blo 706319 5366897 := bstep (se 2 (by rfl) ⟨2012586, by rfl⟩ : syracuseStep 5366897 = 4025173) B4025173
theorem B1008931 : Blo 706319 1008931 := bstep (se 1 (by rfl) ⟨756698, by rfl⟩ : syracuseStep 1008931 = 1513397) B1513397
theorem B2385233 : Blo 706319 2385233 := bstep (se 2 (by rfl) ⟨894462, by rfl⟩ : syracuseStep 2385233 = 1788925) B1788925
theorem B1009027 : Blo 706319 1009027 := bstep (se 1 (by rfl) ⟨756770, by rfl⟩ : syracuseStep 1009027 = 1513541) B1513541
theorem B4023715 : Blo 706319 4023715 := bstep (se 1 (by rfl) ⟨3017786, by rfl⟩ : syracuseStep 4023715 = 6035573) B6035573
theorem B1697219 : Blo 706319 1697219 := bstep (se 1 (by rfl) ⟨1272914, by rfl⟩ : syracuseStep 1697219 = 2545829) B2545829
theorem B20473397 : Blo 706319 20473397 := bstep (se 5 (by rfl) ⟨959690, by rfl⟩ : syracuseStep 20473397 = 1919381) B1919381
theorem B1795729 : Blo 706319 1795729 := bstep (se 2 (by rfl) ⟨673398, by rfl⟩ : syracuseStep 1795729 = 1346797) B1346797
theorem B5531333 : Blo 706319 5531333 := bstep (se 4 (by rfl) ⟨518562, by rfl⟩ : syracuseStep 5531333 = 1037125) B1037125
theorem B2385773 : Blo 706319 2385773 := bstep (se 3 (by rfl) ⟨447332, by rfl⟩ : syracuseStep 2385773 = 894665) B894665
theorem B1009523 : Blo 706319 1009523 := bstep (se 1 (by rfl) ⟨757142, by rfl⟩ : syracuseStep 1009523 = 1514285) B1514285
theorem B2385827 : Blo 706319 2385827 := bstep (se 1 (by rfl) ⟨1789370, by rfl⟩ : syracuseStep 2385827 = 3578741) B3578741
theorem B1796003 : Blo 706319 1796003 := bstep (se 1 (by rfl) ⟨1347002, by rfl⟩ : syracuseStep 1796003 = 2694005) B2694005
theorem B4024241 : Blo 706319 4024241 := bstep (se 2 (by rfl) ⟨1509090, by rfl⟩ : syracuseStep 4024241 = 3018181) B3018181
theorem B2484145 : Blo 706319 2484145 := bstep (se 2 (by rfl) ⟨931554, by rfl⟩ : syracuseStep 2484145 = 1863109) B1863109
theorem B3401777 : Blo 706319 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B1796195 : Blo 706319 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B12085361 : Blo 706319 12085361 := bstep (se 2 (by rfl) ⟨4532010, by rfl⟩ : syracuseStep 12085361 = 9064021) B9064021
theorem B2386097 : Blo 706319 2386097 := bstep (se 2 (by rfl) ⟨894786, by rfl⟩ : syracuseStep 2386097 = 1789573) B1789573
theorem B18147725 : Blo 706319 18147725 := bstep (se 3 (by rfl) ⟨3402698, by rfl⟩ : syracuseStep 18147725 = 6805397) B6805397
theorem B1010161 : Blo 706319 1010161 := bstep (se 2 (by rfl) ⟨378810, by rfl⟩ : syracuseStep 1010161 = 757621) B757621
theorem B2386637 : Blo 706319 2386637 := bstep (se 3 (by rfl) ⟨447494, by rfl⟩ : syracuseStep 2386637 = 894989) B894989
theorem B2386691 : Blo 706319 2386691 := bstep (se 1 (by rfl) ⟨1790018, by rfl⟩ : syracuseStep 2386691 = 3580037) B3580037
theorem B1010497 : Blo 706319 1010497 := bstep (se 2 (by rfl) ⟨378936, by rfl⟩ : syracuseStep 1010497 = 757873) B757873
theorem B1698659 : Blo 706319 1698659 := bstep (se 1 (by rfl) ⟨1273994, by rfl⟩ : syracuseStep 1698659 = 2547989) B2547989
theorem B2157553 : Blo 706319 2157553 := bstep (se 2 (by rfl) ⟨809082, by rfl⟩ : syracuseStep 2157553 = 1618165) B1618165
theorem B2681869 : Blo 706319 2681869 := bstep (se 3 (by rfl) ⟨502850, by rfl⟩ : syracuseStep 2681869 = 1005701) B1005701
theorem B1698833 : Blo 706319 1698833 := bstep (se 2 (by rfl) ⟨637062, by rfl⟩ : syracuseStep 1698833 = 1274125) B1274125
theorem B2386961 : Blo 706319 2386961 := bstep (se 2 (by rfl) ⟨895110, by rfl⟩ : syracuseStep 2386961 = 1790221) B1790221
theorem B1797137 : Blo 706319 1797137 := bstep (se 2 (by rfl) ⟨673926, by rfl⟩ : syracuseStep 1797137 = 1347853) B1347853
theorem B1698851 : Blo 706319 1698851 := bstep (se 1 (by rfl) ⟨1274138, by rfl⟩ : syracuseStep 1698851 = 2548277) B2548277
theorem B1797187 : Blo 706319 1797187 := bstep (se 1 (by rfl) ⟨1347890, by rfl⟩ : syracuseStep 1797187 = 2695781) B2695781
theorem B1076321 : Blo 706319 1076321 := bstep (se 2 (by rfl) ⟨403620, by rfl⟩ : syracuseStep 1076321 = 807241) B807241
theorem B1797329 : Blo 706319 1797329 := bstep (se 2 (by rfl) ⟨673998, by rfl⟩ : syracuseStep 1797329 = 1347997) B1347997
theorem B716035 : Blo 706319 716035 := bstep (se 1 (by rfl) ⟨537026, by rfl⟩ : syracuseStep 716035 = 1074053) B1074053
theorem B4025699 : Blo 706319 4025699 := bstep (se 1 (by rfl) ⟨3019274, by rfl⟩ : syracuseStep 4025699 = 6038549) B6038549
theorem B1011089 : Blo 706319 1011089 := bstep (se 2 (by rfl) ⟨379158, by rfl⟩ : syracuseStep 1011089 = 758317) B758317
theorem B6057443 : Blo 706319 6057443 := bstep (se 1 (by rfl) ⟨4543082, by rfl⟩ : syracuseStep 6057443 = 9086165) B9086165
theorem B2387501 : Blo 706319 2387501 := bstep (se 3 (by rfl) ⟨447656, by rfl⟩ : syracuseStep 2387501 = 895313) B895313
theorem B1273411 : Blo 706319 1273411 := bstep (se 1 (by rfl) ⟨955058, by rfl⟩ : syracuseStep 1273411 = 1910117) B1910117
theorem B2387555 : Blo 706319 2387555 := bstep (se 1 (by rfl) ⟨1790666, by rfl⟩ : syracuseStep 2387555 = 3581333) B3581333
theorem B10219121 : Blo 706319 10219121 := bstep (se 2 (by rfl) ⟨3832170, by rfl⟩ : syracuseStep 10219121 = 7664341) B7664341
theorem B1273475 : Blo 706319 1273475 := bstep (se 1 (by rfl) ⟨955106, by rfl⟩ : syracuseStep 1273475 = 1910213) B1910213
theorem B3272333 : Blo 706319 3272333 := bstep (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) B1227125
theorem B2158285 : Blo 706319 2158285 := bstep (se 3 (by rfl) ⟨404678, by rfl⟩ : syracuseStep 2158285 = 809357) B809357
theorem B1077025 : Blo 706319 1077025 := bstep (se 2 (by rfl) ⟨403884, by rfl⟩ : syracuseStep 1077025 = 807769) B807769
theorem B2682659 : Blo 706319 2682659 := bstep (se 1 (by rfl) ⟨2011994, by rfl⟩ : syracuseStep 2682659 = 4023989) B4023989
theorem B2387825 : Blo 706319 2387825 := bstep (se 2 (by rfl) ⟨895434, by rfl⟩ : syracuseStep 2387825 = 1790869) B1790869
theorem B1208369 : Blo 706319 1208369 := bstep (se 2 (by rfl) ⟨453138, by rfl⟩ : syracuseStep 1208369 = 906277) B906277
theorem B3403853 : Blo 706319 3403853 := bstep (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) B1276445
theorem B2552141 : Blo 706319 2552141 := bstep (se 3 (by rfl) ⟨478526, by rfl⟩ : syracuseStep 2552141 = 957053) B957053
theorem B2388365 : Blo 706319 2388365 := bstep (se 3 (by rfl) ⟨447818, by rfl⟩ : syracuseStep 2388365 = 895637) B895637
theorem B2683313 : Blo 706319 2683313 := bstep (se 2 (by rfl) ⟨1006242, by rfl⟩ : syracuseStep 2683313 = 2012485) B2012485
theorem B2388419 : Blo 706319 2388419 := bstep (se 1 (by rfl) ⟨1791314, by rfl⟩ : syracuseStep 2388419 = 3582629) B3582629
theorem B1274449 : Blo 706319 1274449 := bstep (se 2 (by rfl) ⟨477918, by rfl⟩ : syracuseStep 1274449 = 955837) B955837
theorem B9826915 : Blo 706319 9826915 := bstep (se 1 (by rfl) ⟨7370186, by rfl⟩ : syracuseStep 9826915 = 14740373) B14740373
theorem B1274513 : Blo 706319 1274513 := bstep (se 2 (by rfl) ⟨477942, by rfl⟩ : syracuseStep 1274513 = 955885) B955885
theorem B2388689 : Blo 706319 2388689 := bstep (se 2 (by rfl) ⟨895758, by rfl⟩ : syracuseStep 2388689 = 1791517) B1791517
theorem B24507157 : Blo 706319 24507157 := bstep (se 6 (by rfl) ⟨574386, by rfl⟩ : syracuseStep 24507157 = 1148773) B1148773
theorem B2552717 : Blo 706319 2552717 := bstep (se 3 (by rfl) ⟨478634, by rfl⟩ : syracuseStep 2552717 = 957269) B957269
theorem B1078193 : Blo 706319 1078193 := bstep (se 2 (by rfl) ⟨404322, by rfl⟩ : syracuseStep 1078193 = 808645) B808645
theorem B4027589 : Blo 706319 4027589 := bstep (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) B755173
theorem B2389229 : Blo 706319 2389229 := bstep (se 3 (by rfl) ⟨447980, by rfl⟩ : syracuseStep 2389229 = 895961) B895961
theorem B2389283 : Blo 706319 2389283 := bstep (se 1 (by rfl) ⟨1791962, by rfl⟩ : syracuseStep 2389283 = 3583925) B3583925
theorem B1209683 : Blo 706319 1209683 := bstep (se 1 (by rfl) ⟨907262, by rfl⟩ : syracuseStep 1209683 = 1814525) B1814525
theorem B2389553 : Blo 706319 2389553 := bstep (se 2 (by rfl) ⟨896082, by rfl⟩ : syracuseStep 2389553 = 1792165) B1792165
theorem B2684771 : Blo 706319 2684771 := bstep (se 1 (by rfl) ⟨2013578, by rfl⟩ : syracuseStep 2684771 = 4027157) B4027157
theorem B2684785 : Blo 706319 2684785 := bstep (se 2 (by rfl) ⟨1006794, by rfl⟩ : syracuseStep 2684785 = 2013589) B2013589
theorem B2455427 : Blo 706319 2455427 := bstep (se 1 (by rfl) ⟨1841570, by rfl⟩ : syracuseStep 2455427 = 3683141) B3683141
theorem B3831715 : Blo 706319 3831715 := bstep (se 1 (by rfl) ⟨2873786, by rfl⟩ : syracuseStep 3831715 = 5747573) B5747573
theorem B849955 : Blo 706319 849955 := bstep (se 1 (by rfl) ⟨637466, by rfl⟩ : syracuseStep 849955 = 1274933) B1274933
theorem B2390093 : Blo 706319 2390093 := bstep (se 3 (by rfl) ⟨448142, by rfl⟩ : syracuseStep 2390093 = 896285) B896285
theorem B2390147 : Blo 706319 2390147 := bstep (se 1 (by rfl) ⟨1792610, by rfl⟩ : syracuseStep 2390147 = 3585221) B3585221
theorem B2390417 : Blo 706319 2390417 := bstep (se 2 (by rfl) ⟨896406, by rfl⟩ : syracuseStep 2390417 = 1792813) B1792813
theorem B850339 : Blo 706319 850339 := bstep (se 1 (by rfl) ⟨637754, by rfl⟩ : syracuseStep 850339 = 1275509) B1275509
theorem B1341937 : Blo 706319 1341937 := bstep (se 2 (by rfl) ⟨503226, by rfl⟩ : syracuseStep 1341937 = 1006453) B1006453
theorem B5733233 : Blo 706319 5733233 := bstep (se 2 (by rfl) ⟨2149962, by rfl⟩ : syracuseStep 5733233 = 4299925) B4299925
theorem B2390957 : Blo 706319 2390957 := bstep (se 3 (by rfl) ⟨448304, by rfl⟩ : syracuseStep 2390957 = 896609) B896609
theorem B850867 : Blo 706319 850867 := bstep (se 1 (by rfl) ⟨638150, by rfl⟩ : syracuseStep 850867 = 1276301) B1276301
theorem B2391011 : Blo 706319 2391011 := bstep (se 1 (by rfl) ⟨1793258, by rfl⟩ : syracuseStep 2391011 = 3586517) B3586517
theorem B719939 : Blo 706319 719939 := bstep (se 1 (by rfl) ⟨539954, by rfl⟩ : syracuseStep 719939 = 1079909) B1079909
theorem B1277137 : Blo 706319 1277137 := bstep (se 2 (by rfl) ⟨478926, by rfl⟩ : syracuseStep 1277137 = 957853) B957853
theorem B2391281 : Blo 706319 2391281 := bstep (se 2 (by rfl) ⟨896730, by rfl⟩ : syracuseStep 2391281 = 1793461) B1793461
theorem B2686243 : Blo 706319 2686243 := bstep (se 1 (by rfl) ⟨2014682, by rfl⟩ : syracuseStep 2686243 = 4029365) B4029365
theorem B1342993 : Blo 706319 1342993 := bstep (se 2 (by rfl) ⟨503622, by rfl⟩ : syracuseStep 1342993 = 1007245) B1007245
theorem B9698915 : Blo 706319 9698915 := bstep (se 1 (by rfl) ⟨7274186, by rfl⟩ : syracuseStep 9698915 = 14548373) B14548373
theorem B2391821 : Blo 706319 2391821 := bstep (se 3 (by rfl) ⟨448466, by rfl⟩ : syracuseStep 2391821 = 896933) B896933
theorem B2391875 : Blo 706319 2391875 := bstep (se 1 (by rfl) ⟨1793906, by rfl⟩ : syracuseStep 2391875 = 3587813) B3587813
theorem B1343395 : Blo 706319 1343395 := bstep (se 1 (by rfl) ⟨1007546, by rfl⟩ : syracuseStep 1343395 = 2015093) B2015093
theorem B1343441 : Blo 706319 1343441 := bstep (se 2 (by rfl) ⟨503790, by rfl⟩ : syracuseStep 1343441 = 1007581) B1007581
theorem B34930763 : Blo 706319 34930763 := bstep (se 1 (by rfl) ⟨26198072, by rfl⟩ : syracuseStep 34930763 = 52396145) B52396145
theorem B2556049 : Blo 706319 2556049 := bstep (se 2 (by rfl) ⟨958518, by rfl⟩ : syracuseStep 2556049 = 1917037) B1917037
theorem B1704215 : Blo 706319 1704215 := bstep (se 1 (by rfl) ⟨1278161, by rfl⟩ : syracuseStep 1704215 = 2556323) B2556323
theorem B2392523 : Blo 706319 2392523 := bstep (se 1 (by rfl) ⟨1794392, by rfl⟩ : syracuseStep 2392523 = 3588785) B3588785
theorem B2556467 : Blo 706319 2556467 := bstep (se 1 (by rfl) ⟨1917350, by rfl⟩ : syracuseStep 2556467 = 3834701) B3834701
theorem B1344215 : Blo 706319 1344215 := bstep (se 1 (by rfl) ⟨1008161, by rfl⟩ : syracuseStep 1344215 = 2016323) B2016323
theorem B2392793 : Blo 706319 2392793 := bstep (se 2 (by rfl) ⟨897297, by rfl⟩ : syracuseStep 2392793 = 1794595) B1794595
theorem B1639283 : Blo 706319 1639283 := bstep (se 1 (by rfl) ⟨1229462, by rfl⟩ : syracuseStep 1639283 = 2458925) B2458925
theorem B754763 : Blo 706319 754763 := bstep (se 1 (by rfl) ⟨566072, by rfl⟩ : syracuseStep 754763 = 1132145) B1132145
theorem B1279127 : Blo 706319 1279127 := bstep (se 1 (by rfl) ⟨959345, by rfl⟩ : syracuseStep 1279127 = 1918691) B1918691
theorem B2688173 : Blo 706319 2688173 := bstep (se 3 (by rfl) ⟨504032, by rfl⟩ : syracuseStep 2688173 = 1008065) B1008065
theorem B1344755 : Blo 706319 1344755 := bstep (se 1 (by rfl) ⟨1008566, by rfl⟩ : syracuseStep 1344755 = 2017133) B2017133
theorem B1508723 : Blo 706319 1508723 := bstep (se 1 (by rfl) ⟨1131542, by rfl⟩ : syracuseStep 1508723 = 2263085) B2263085
theorem B2393495 : Blo 706319 2393495 := bstep (se 1 (by rfl) ⟨1795121, by rfl⟩ : syracuseStep 2393495 = 3590243) B3590243
theorem B4097459 : Blo 706319 4097459 := bstep (se 1 (by rfl) ⟨3073094, by rfl⟩ : syracuseStep 4097459 = 6146189) B6146189
theorem B1508825 : Blo 706319 1508825 := bstep (se 2 (by rfl) ⟨565809, by rfl⟩ : syracuseStep 1508825 = 1131619) B1131619
theorem B11503255 : Blo 706319 11503255 := bstep (se 1 (by rfl) ⟨8627441, by rfl⟩ : syracuseStep 11503255 = 17254883) B17254883
theorem B1279703 : Blo 706319 1279703 := bstep (se 1 (by rfl) ⟨959777, by rfl⟩ : syracuseStep 1279703 = 1919555) B1919555
theorem B1345241 : Blo 706319 1345241 := bstep (se 2 (by rfl) ⟨504465, by rfl⟩ : syracuseStep 1345241 = 1008931) B1008931
theorem B1509185 : Blo 706319 1509185 := bstep (se 2 (by rfl) ⟨565944, by rfl⟩ : syracuseStep 1509185 = 1131889) B1131889
theorem B2688947 : Blo 706319 2688947 := bstep (se 1 (by rfl) ⟨2016710, by rfl⟩ : syracuseStep 2688947 = 4033421) B4033421
theorem B2394035 : Blo 706319 2394035 := bstep (se 1 (by rfl) ⟨1795526, by rfl⟩ : syracuseStep 2394035 = 3591053) B3591053
theorem B4851757 : Blo 706319 4851757 := bstep (se 3 (by rfl) ⟨909704, by rfl⟩ : syracuseStep 4851757 = 1819409) B1819409
theorem B755831 : Blo 706319 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B5376131 : Blo 706319 5376131 := bstep (se 1 (by rfl) ⟨4032098, by rfl⟩ : syracuseStep 5376131 = 8064197) B8064197
theorem B2394305 : Blo 706319 2394305 := bstep (se 2 (by rfl) ⟨897864, by rfl⟩ : syracuseStep 2394305 = 1795729) B1795729
theorem B1509911 : Blo 706319 1509911 := bstep (se 1 (by rfl) ⟨1132433, by rfl⟩ : syracuseStep 1509911 = 2264867) B2264867
theorem B3312193 : Blo 706319 3312193 := bstep (se 2 (by rfl) ⟨1242072, by rfl⟩ : syracuseStep 3312193 = 2484145) B2484145
theorem B3410525 : Blo 706319 3410525 := bstep (se 3 (by rfl) ⟨639473, by rfl⟩ : syracuseStep 3410525 = 1278947) B1278947
theorem B2394845 : Blo 706319 2394845 := bstep (se 3 (by rfl) ⟨449033, by rfl⟩ : syracuseStep 2394845 = 898067) B898067
theorem B5114659 : Blo 706319 5114659 := bstep (se 1 (by rfl) ⟨3835994, by rfl⟩ : syracuseStep 5114659 = 7671989) B7671989
theorem B10226549 : Blo 706319 10226549 := bstep (se 5 (by rfl) ⟨479369, by rfl⟩ : syracuseStep 10226549 = 958739) B958739
theorem B1346699 : Blo 706319 1346699 := bstep (se 1 (by rfl) ⟨1010024, by rfl⟩ : syracuseStep 1346699 = 2020049) B2020049
theorem B756907 : Blo 706319 756907 := bstep (se 1 (by rfl) ⟨567680, by rfl⟩ : syracuseStep 756907 = 1135361) B1135361
theorem B2559235 : Blo 706319 2559235 := bstep (se 1 (by rfl) ⟨1919426, by rfl⟩ : syracuseStep 2559235 = 3838853) B3838853
theorem B1346881 : Blo 706319 1346881 := bstep (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) B1010161
theorem B2690435 : Blo 706319 2690435 := bstep (se 1 (by rfl) ⟨2017826, by rfl⟩ : syracuseStep 2690435 = 4035653) B4035653
theorem B1510807 : Blo 706319 1510807 := bstep (se 1 (by rfl) ⟨1133105, by rfl⟩ : syracuseStep 1510807 = 2266211) B2266211
theorem B2428481 : Blo 706319 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B1347329 : Blo 706319 1347329 := bstep (se 2 (by rfl) ⟨505248, by rfl⟩ : syracuseStep 1347329 = 1010497) B1010497
theorem B2690891 : Blo 706319 2690891 := bstep (se 1 (by rfl) ⟨2018168, by rfl⟩ : syracuseStep 2690891 = 4036337) B4036337
theorem B2395979 : Blo 706319 2395979 := bstep (se 1 (by rfl) ⟨1796984, by rfl⟩ : syracuseStep 2395979 = 3593969) B3593969
theorem B15175603 : Blo 706319 15175603 := bstep (se 1 (by rfl) ⟨11381702, by rfl⟩ : syracuseStep 15175603 = 22763405) B22763405
theorem B3575825 : Blo 706319 3575825 := bstep (se 2 (by rfl) ⟨1340934, by rfl⟩ : syracuseStep 3575825 = 2681869) B2681869
theorem B2691089 : Blo 706319 2691089 := bstep (se 2 (by rfl) ⟨1009158, by rfl⟩ : syracuseStep 2691089 = 2018317) B2018317
theorem B757847 : Blo 706319 757847 := bstep (se 1 (by rfl) ⟨568385, by rfl⟩ : syracuseStep 757847 = 1136771) B1136771
theorem B1347671 : Blo 706319 1347671 := bstep (se 1 (by rfl) ⟨1010753, by rfl⟩ : syracuseStep 1347671 = 2021507) B2021507
theorem B2396249 : Blo 706319 2396249 := bstep (se 2 (by rfl) ⟨898593, by rfl⟩ : syracuseStep 2396249 = 1797187) B1797187
theorem B3281075 : Blo 706319 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B3575987 : Blo 706319 3575987 := bstep (se 1 (by rfl) ⟨2681990, by rfl⟩ : syracuseStep 3575987 = 5363981) B5363981
theorem B2298059 : Blo 706319 2298059 := bstep (se 1 (by rfl) ⟨1723544, by rfl⟩ : syracuseStep 2298059 = 3447089) B3447089
theorem B1511627 : Blo 706319 1511627 := bstep (se 1 (by rfl) ⟨1133720, by rfl⟩ : syracuseStep 1511627 = 2267441) B2267441
theorem B954713 : Blo 706319 954713 := bstep (se 2 (by rfl) ⟨358017, by rfl⟩ : syracuseStep 954713 = 716035) B716035
theorem B27201905 : Blo 706319 27201905 := bstep (se 2 (by rfl) ⟨10200714, by rfl⟩ : syracuseStep 27201905 = 20401429) B20401429
theorem B3019139 : Blo 706319 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B14750221 : Blo 706319 14750221 := bstep (se 3 (by rfl) ⟨2765666, by rfl⟩ : syracuseStep 14750221 = 5531333) B5531333
theorem B1348339 : Blo 706319 1348339 := bstep (se 1 (by rfl) ⟨1011254, by rfl⟩ : syracuseStep 1348339 = 2022509) B2022509
theorem B2691863 : Blo 706319 2691863 := bstep (se 1 (by rfl) ⟨2018897, by rfl⟩ : syracuseStep 2691863 = 4037795) B4037795
theorem B2396951 : Blo 706319 2396951 := bstep (se 1 (by rfl) ⟨1797713, by rfl⟩ : syracuseStep 2396951 = 3595427) B3595427
theorem B1512371 : Blo 706319 1512371 := bstep (se 1 (by rfl) ⟨1134278, by rfl⟩ : syracuseStep 1512371 = 2268557) B2268557
theorem B2692061 : Blo 706319 2692061 := bstep (se 3 (by rfl) ⟨504761, by rfl⟩ : syracuseStep 2692061 = 1009523) B1009523
theorem B4035905 : Blo 706319 4035905 := bstep (se 2 (by rfl) ⟨1513464, by rfl⟩ : syracuseStep 4035905 = 3026929) B3026929
theorem B5379533 : Blo 706319 5379533 := bstep (se 3 (by rfl) ⟨1008662, by rfl⟩ : syracuseStep 5379533 = 2017325) B2017325
theorem B2266775 : Blo 706319 2266775 := bstep (se 1 (by rfl) ⟨1700081, by rfl⟩ : syracuseStep 2266775 = 3400163) B3400163
theorem B1513217 : Blo 706319 1513217 := bstep (se 2 (by rfl) ⟨567456, by rfl⟩ : syracuseStep 1513217 = 1134913) B1134913
theorem B5380019 : Blo 706319 5380019 := bstep (se 1 (by rfl) ⟨4035014, by rfl⟩ : syracuseStep 5380019 = 8070029) B8070029
theorem B2299927 : Blo 706319 2299927 := bstep (se 1 (by rfl) ⟨1724945, by rfl⟩ : syracuseStep 2299927 = 3449891) B3449891
theorem B3577931 : Blo 706319 3577931 := bstep (se 1 (by rfl) ⟨2683448, by rfl⟩ : syracuseStep 3577931 = 5366897) B5366897
theorem B1513559 : Blo 706319 1513559 := bstep (se 1 (by rfl) ⟨1135169, by rfl⟩ : syracuseStep 1513559 = 2270339) B2270339
theorem B3676481 : Blo 706319 3676481 := bstep (se 2 (by rfl) ⟨1378680, by rfl⟩ : syracuseStep 3676481 = 2757361) B2757361
theorem B32676209 : Blo 706319 32676209 := bstep (se 2 (by rfl) ⟨12253578, by rfl⟩ : syracuseStep 32676209 = 24507157) B24507157
theorem B2267851 : Blo 706319 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B2694019 : Blo 706319 2694019 := bstep (se 1 (by rfl) ⟨2020514, by rfl⟩ : syracuseStep 2694019 = 4041029) B4041029
theorem B12098483 : Blo 706319 12098483 := bstep (se 1 (by rfl) ⟨9073862, by rfl⟩ : syracuseStep 12098483 = 18147725) B18147725
theorem B2694323 : Blo 706319 2694323 := bstep (se 1 (by rfl) ⟨2020742, by rfl⟩ : syracuseStep 2694323 = 4041485) B4041485
theorem B5381477 : Blo 706319 5381477 := bstep (se 4 (by rfl) ⟨504513, by rfl⟩ : syracuseStep 5381477 = 1009027) B1009027
theorem B4038295 : Blo 706319 4038295 := bstep (se 1 (by rfl) ⟨3028721, by rfl⟩ : syracuseStep 4038295 = 6057443) B6057443
theorem B3579713 : Blo 706319 3579713 := bstep (se 2 (by rfl) ⟨1342392, by rfl⟩ : syracuseStep 3579713 = 2684785) B2684785
theorem B2694977 : Blo 706319 2694977 := bstep (se 2 (by rfl) ⟨1010616, by rfl⟩ : syracuseStep 2694977 = 2021233) B2021233
theorem B5381963 : Blo 706319 5381963 := bstep (se 1 (by rfl) ⟨4036472, by rfl⟩ : syracuseStep 5381963 = 8072945) B8072945
theorem B2269235 : Blo 706319 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B3022913 : Blo 706319 3022913 := bstep (se 2 (by rfl) ⟨1133592, by rfl⟩ : syracuseStep 3022913 = 2267185) B2267185
theorem B9052235 : Blo 706319 9052235 := bstep (se 1 (by rfl) ⟨6789176, by rfl⟩ : syracuseStep 9052235 = 13578353) B13578353
theorem B4530269 : Blo 706319 4530269 := bstep (se 3 (by rfl) ⟨849425, by rfl⟩ : syracuseStep 4530269 = 1698851) B1698851
theorem B794731 : Blo 706319 794731 := bstep (se 1 (by rfl) ⟨596048, by rfl⟩ : syracuseStep 794731 = 1192097) B1192097
theorem B2728129 : Blo 706319 2728129 := bstep (se 2 (by rfl) ⟨1023048, by rfl⟩ : syracuseStep 2728129 = 2046097) B2046097
theorem B794839 : Blo 706319 794839 := bstep (se 1 (by rfl) ⟨596129, by rfl⟩ : syracuseStep 794839 = 1192259) B1192259
theorem B6791525 : Blo 706319 6791525 := bstep (se 4 (by rfl) ⟨636705, by rfl⟩ : syracuseStep 6791525 = 1273411) B1273411
theorem B795019 : Blo 706319 795019 := bstep (se 1 (by rfl) ⟨596264, by rfl⟩ : syracuseStep 795019 = 1192529) B1192529
theorem B795127 : Blo 706319 795127 := bstep (se 1 (by rfl) ⟨596345, by rfl⟩ : syracuseStep 795127 = 1192691) B1192691
theorem B795307 : Blo 706319 795307 := bstep (se 1 (by rfl) ⟨596480, by rfl⟩ : syracuseStep 795307 = 1192961) B1192961
theorem B4301585 : Blo 706319 4301585 := bstep (se 2 (by rfl) ⟨1613094, by rfl⟩ : syracuseStep 4301585 = 3226189) B3226189
theorem B795415 : Blo 706319 795415 := bstep (se 1 (by rfl) ⟨596561, by rfl⟩ : syracuseStep 795415 = 1193123) B1193123
theorem B795595 : Blo 706319 795595 := bstep (se 1 (by rfl) ⟨596696, by rfl⟩ : syracuseStep 795595 = 1193393) B1193393
theorem B3023837 : Blo 706319 3023837 := bstep (se 3 (by rfl) ⟨566969, by rfl⟩ : syracuseStep 3023837 = 1133939) B1133939
theorem B2696237 : Blo 706319 2696237 := bstep (se 3 (by rfl) ⟨505544, by rfl⟩ : syracuseStep 2696237 = 1011089) B1011089
theorem B795703 : Blo 706319 795703 := bstep (se 1 (by rfl) ⟨596777, by rfl⟩ : syracuseStep 795703 = 1193555) B1193555
theorem B2696267 : Blo 706319 2696267 := bstep (se 1 (by rfl) ⟨2022200, by rfl⟩ : syracuseStep 2696267 = 4044401) B4044401
theorem B795883 : Blo 706319 795883 := bstep (se 1 (by rfl) ⟨596912, by rfl⟩ : syracuseStep 795883 = 1193825) B1193825
theorem B795991 : Blo 706319 795991 := bstep (se 1 (by rfl) ⟨596993, by rfl⟩ : syracuseStep 795991 = 1193987) B1193987
theorem B796171 : Blo 706319 796171 := bstep (se 1 (by rfl) ⟨597128, by rfl⟩ : syracuseStep 796171 = 1194257) B1194257
theorem B796279 : Blo 706319 796279 := bstep (se 1 (by rfl) ⟨597209, by rfl⟩ : syracuseStep 796279 = 1194419) B1194419
theorem B8726221 : Blo 706319 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B3581657 : Blo 706319 3581657 := bstep (se 2 (by rfl) ⟨1343121, by rfl⟩ : syracuseStep 3581657 = 2686243) B2686243
theorem B2696921 : Blo 706319 2696921 := bstep (se 2 (by rfl) ⟨1011345, by rfl⟩ : syracuseStep 2696921 = 2022691) B2022691
theorem B796459 : Blo 706319 796459 := bstep (se 1 (by rfl) ⟨597344, by rfl⟩ : syracuseStep 796459 = 1194689) B1194689
theorem B796567 : Blo 706319 796567 := bstep (se 1 (by rfl) ⟨597425, by rfl⟩ : syracuseStep 796567 = 1194851) B1194851
theorem B2041793 : Blo 706319 2041793 := bstep (se 2 (by rfl) ⟨765672, by rfl⟩ : syracuseStep 2041793 = 1531345) B1531345
theorem B796747 : Blo 706319 796747 := bstep (se 1 (by rfl) ⟨597560, by rfl⟩ : syracuseStep 796747 = 1195121) B1195121
theorem B796855 : Blo 706319 796855 := bstep (se 1 (by rfl) ⟨597641, by rfl⟩ : syracuseStep 796855 = 1195283) B1195283
theorem B797035 : Blo 706319 797035 := bstep (se 1 (by rfl) ⟨597776, by rfl⟩ : syracuseStep 797035 = 1195553) B1195553
theorem B6465943 : Blo 706319 6465943 := bstep (se 1 (by rfl) ⟨4849457, by rfl⟩ : syracuseStep 6465943 = 9698915) B9698915
theorem B797143 : Blo 706319 797143 := bstep (se 1 (by rfl) ⟨597857, by rfl⟩ : syracuseStep 797143 = 1195715) B1195715
theorem B13609565 : Blo 706319 13609565 := bstep (se 3 (by rfl) ⟨2551793, by rfl⟩ : syracuseStep 13609565 = 5103587) B5103587
theorem B895627 : Blo 706319 895627 := bstep (se 1 (by rfl) ⟨671720, by rfl⟩ : syracuseStep 895627 = 1343441) B1343441
theorem B797323 : Blo 706319 797323 := bstep (se 1 (by rfl) ⟨597992, by rfl⟩ : syracuseStep 797323 = 1195985) B1195985
theorem B1059479 : Blo 706319 1059479 := bstep (se 1 (by rfl) ⟨794609, by rfl⟩ : syracuseStep 1059479 = 1589219) B1589219
theorem B1059545 : Blo 706319 1059545 := bstep (se 2 (by rfl) ⟨397329, by rfl⟩ : syracuseStep 1059545 = 794659) B794659
theorem B797431 : Blo 706319 797431 := bstep (se 1 (by rfl) ⟨598073, by rfl⟩ : syracuseStep 797431 = 1196147) B1196147
theorem B3222317 : Blo 706319 3222317 := bstep (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) B1208369
theorem B1059659 : Blo 706319 1059659 := bstep (se 1 (by rfl) ⟨794744, by rfl⟩ : syracuseStep 1059659 = 1589489) B1589489
theorem B1059671 : Blo 706319 1059671 := bstep (se 1 (by rfl) ⟨794753, by rfl⟩ : syracuseStep 1059671 = 1589507) B1589507
theorem B1420183 : Blo 706319 1420183 := bstep (se 1 (by rfl) ⟨1065137, by rfl⟩ : syracuseStep 1420183 = 2130275) B2130275
theorem B1059737 : Blo 706319 1059737 := bstep (se 2 (by rfl) ⟨397401, by rfl⟩ : syracuseStep 1059737 = 794803) B794803
theorem B797611 : Blo 706319 797611 := bstep (se 1 (by rfl) ⟨598208, by rfl⟩ : syracuseStep 797611 = 1196417) B1196417
theorem B1059851 : Blo 706319 1059851 := bstep (se 1 (by rfl) ⟨794888, by rfl⟩ : syracuseStep 1059851 = 1589777) B1589777
theorem B1059863 : Blo 706319 1059863 := bstep (se 1 (by rfl) ⟨794897, by rfl⟩ : syracuseStep 1059863 = 1589795) B1589795
theorem B797719 : Blo 706319 797719 := bstep (se 1 (by rfl) ⟨598289, by rfl⟩ : syracuseStep 797719 = 1196579) B1196579
theorem B1059929 : Blo 706319 1059929 := bstep (se 2 (by rfl) ⟨397473, by rfl⟩ : syracuseStep 1059929 = 794947) B794947
theorem B1060043 : Blo 706319 1060043 := bstep (se 1 (by rfl) ⟨795032, by rfl⟩ : syracuseStep 1060043 = 1590065) B1590065
theorem B797899 : Blo 706319 797899 := bstep (se 1 (by rfl) ⟨598424, by rfl⟩ : syracuseStep 797899 = 1196849) B1196849
theorem B1060055 : Blo 706319 1060055 := bstep (se 1 (by rfl) ⟨795041, by rfl⟩ : syracuseStep 1060055 = 1590083) B1590083
theorem B1060121 : Blo 706319 1060121 := bstep (se 2 (by rfl) ⟨397545, by rfl⟩ : syracuseStep 1060121 = 795091) B795091
theorem B3583277 : Blo 706319 3583277 := bstep (se 3 (by rfl) ⟨671864, by rfl⟩ : syracuseStep 3583277 = 1343729) B1343729
theorem B2305331 : Blo 706319 2305331 := bstep (se 1 (by rfl) ⟨1728998, by rfl⟩ : syracuseStep 2305331 = 3457997) B3457997
theorem B798007 : Blo 706319 798007 := bstep (se 1 (by rfl) ⟨598505, by rfl⟩ : syracuseStep 798007 = 1197011) B1197011
theorem B1060235 : Blo 706319 1060235 := bstep (se 1 (by rfl) ⟨795176, by rfl⟩ : syracuseStep 1060235 = 1590353) B1590353
theorem B1060247 : Blo 706319 1060247 := bstep (se 1 (by rfl) ⟨795185, by rfl⟩ : syracuseStep 1060247 = 1590371) B1590371
theorem B1617355 : Blo 706319 1617355 := bstep (se 1 (by rfl) ⟨1213016, by rfl⟩ : syracuseStep 1617355 = 2426033) B2426033
theorem B1060313 : Blo 706319 1060313 := bstep (se 2 (by rfl) ⟨397617, by rfl⟩ : syracuseStep 1060313 = 795235) B795235
theorem B31075811 : Blo 706319 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B798187 : Blo 706319 798187 := bstep (se 1 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 798187 = 1197281) B1197281
theorem B1060427 : Blo 706319 1060427 := bstep (se 1 (by rfl) ⟨795320, by rfl⟩ : syracuseStep 1060427 = 1590641) B1590641
theorem B1060439 : Blo 706319 1060439 := bstep (se 1 (by rfl) ⟨795329, by rfl⟩ : syracuseStep 1060439 = 1590659) B1590659
theorem B896599 : Blo 706319 896599 := bstep (se 1 (by rfl) ⟨672449, by rfl⟩ : syracuseStep 896599 = 1344899) B1344899
theorem B798295 : Blo 706319 798295 := bstep (se 1 (by rfl) ⟨598721, by rfl⟩ : syracuseStep 798295 = 1197443) B1197443
theorem B1060505 : Blo 706319 1060505 := bstep (se 2 (by rfl) ⟨397689, by rfl⟩ : syracuseStep 1060505 = 795379) B795379
theorem B1814195 : Blo 706319 1814195 := bstep (se 1 (by rfl) ⟨1360646, by rfl⟩ : syracuseStep 1814195 = 2721293) B2721293
theorem B1060619 : Blo 706319 1060619 := bstep (se 1 (by rfl) ⟨795464, by rfl⟩ : syracuseStep 1060619 = 1590929) B1590929
theorem B798475 : Blo 706319 798475 := bstep (se 1 (by rfl) ⟨598856, by rfl⟩ : syracuseStep 798475 = 1197713) B1197713
theorem B1060631 : Blo 706319 1060631 := bstep (se 1 (by rfl) ⟨795473, by rfl⟩ : syracuseStep 1060631 = 1590947) B1590947
theorem B1060697 : Blo 706319 1060697 := bstep (se 2 (by rfl) ⟨397761, by rfl⟩ : syracuseStep 1060697 = 795523) B795523
theorem B798583 : Blo 706319 798583 := bstep (se 1 (by rfl) ⟨598937, by rfl⟩ : syracuseStep 798583 = 1197875) B1197875
theorem B1060811 : Blo 706319 1060811 := bstep (se 1 (by rfl) ⟨795608, by rfl⟩ : syracuseStep 1060811 = 1591217) B1591217
theorem B1060823 : Blo 706319 1060823 := bstep (se 1 (by rfl) ⟨795617, by rfl⟩ : syracuseStep 1060823 = 1591235) B1591235
theorem B1060889 : Blo 706319 1060889 := bstep (se 2 (by rfl) ⟨397833, by rfl⟩ : syracuseStep 1060889 = 795667) B795667
theorem B798763 : Blo 706319 798763 := bstep (se 1 (by rfl) ⟨599072, by rfl⟩ : syracuseStep 798763 = 1198145) B1198145
theorem B1061003 : Blo 706319 1061003 := bstep (se 1 (by rfl) ⟨795752, by rfl⟩ : syracuseStep 1061003 = 1591505) B1591505
theorem B1061015 : Blo 706319 1061015 := bstep (se 1 (by rfl) ⟨795761, by rfl⟩ : syracuseStep 1061015 = 1591523) B1591523
theorem B798871 : Blo 706319 798871 := bstep (se 1 (by rfl) ⟨599153, by rfl⟩ : syracuseStep 798871 = 1198307) B1198307
theorem B1192151 : Blo 706319 1192151 := bstep (se 1 (by rfl) ⟨894113, by rfl⟩ : syracuseStep 1192151 = 1788227) B1788227
theorem B1061081 : Blo 706319 1061081 := bstep (se 2 (by rfl) ⟨397905, by rfl⟩ : syracuseStep 1061081 = 795811) B795811
theorem B3027203 : Blo 706319 3027203 := bstep (se 1 (by rfl) ⟨2270402, by rfl⟩ : syracuseStep 3027203 = 4540805) B4540805
theorem B6041861 : Blo 706319 6041861 := bstep (se 4 (by rfl) ⟨566424, by rfl⟩ : syracuseStep 6041861 = 1132849) B1132849
theorem B1061195 : Blo 706319 1061195 := bstep (se 1 (by rfl) ⟨795896, by rfl⟩ : syracuseStep 1061195 = 1591793) B1591793
theorem B799051 : Blo 706319 799051 := bstep (se 1 (by rfl) ⟨599288, by rfl⟩ : syracuseStep 799051 = 1198577) B1198577
theorem B1192279 : Blo 706319 1192279 := bstep (se 1 (by rfl) ⟨894209, by rfl⟩ : syracuseStep 1192279 = 1788419) B1788419
theorem B1061207 : Blo 706319 1061207 := bstep (se 1 (by rfl) ⟨795905, by rfl⟩ : syracuseStep 1061207 = 1591811) B1591811
theorem B1290611 : Blo 706319 1290611 := bstep (se 1 (by rfl) ⟨967958, by rfl⟩ : syracuseStep 1290611 = 1935917) B1935917
theorem B897419 : Blo 706319 897419 := bstep (se 1 (by rfl) ⟨673064, by rfl⟩ : syracuseStep 897419 = 1346129) B1346129
theorem B1061273 : Blo 706319 1061273 := bstep (se 2 (by rfl) ⟨397977, by rfl⟩ : syracuseStep 1061273 = 795955) B795955
theorem B1061387 : Blo 706319 1061387 := bstep (se 1 (by rfl) ⟨796040, by rfl⟩ : syracuseStep 1061387 = 1592081) B1592081
theorem B1061399 : Blo 706319 1061399 := bstep (se 1 (by rfl) ⟨796049, by rfl⟩ : syracuseStep 1061399 = 1592099) B1592099
theorem B1061465 : Blo 706319 1061465 := bstep (se 2 (by rfl) ⟨398049, by rfl⟩ : syracuseStep 1061465 = 796099) B796099
theorem B12235445 : Blo 706319 12235445 := bstep (se 5 (by rfl) ⟨573536, by rfl⟩ : syracuseStep 12235445 = 1147073) B1147073
theorem B1553089 : Blo 706319 1553089 := bstep (se 2 (by rfl) ⟨582408, by rfl⟩ : syracuseStep 1553089 = 1164817) B1164817
theorem B1061579 : Blo 706319 1061579 := bstep (se 1 (by rfl) ⟨796184, by rfl⟩ : syracuseStep 1061579 = 1592369) B1592369
theorem B1061591 : Blo 706319 1061591 := bstep (se 1 (by rfl) ⟨796193, by rfl⟩ : syracuseStep 1061591 = 1592387) B1592387
theorem B1061657 : Blo 706319 1061657 := bstep (se 2 (by rfl) ⟨398121, by rfl⟩ : syracuseStep 1061657 = 796243) B796243
theorem B9679661 : Blo 706319 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B1061771 : Blo 706319 1061771 := bstep (se 1 (by rfl) ⟨796328, by rfl⟩ : syracuseStep 1061771 = 1592657) B1592657
theorem B1061783 : Blo 706319 1061783 := bstep (se 1 (by rfl) ⟨796337, by rfl⟩ : syracuseStep 1061783 = 1592675) B1592675
theorem B6042545 : Blo 706319 6042545 := bstep (se 2 (by rfl) ⟨2265954, by rfl⟩ : syracuseStep 6042545 = 4531909) B4531909
theorem B1192907 : Blo 706319 1192907 := bstep (se 1 (by rfl) ⟨894680, by rfl⟩ : syracuseStep 1192907 = 1789361) B1789361
theorem B1061849 : Blo 706319 1061849 := bstep (se 2 (by rfl) ⟨398193, by rfl⟩ : syracuseStep 1061849 = 796387) B796387
theorem B10204177 : Blo 706319 10204177 := bstep (se 2 (by rfl) ⟨3826566, by rfl⟩ : syracuseStep 10204177 = 7653133) B7653133
theorem B5387309 : Blo 706319 5387309 := bstep (se 3 (by rfl) ⟨1010120, by rfl⟩ : syracuseStep 5387309 = 2020241) B2020241
theorem B1193035 : Blo 706319 1193035 := bstep (se 1 (by rfl) ⟨894776, by rfl⟩ : syracuseStep 1193035 = 1789553) B1789553
theorem B1061963 : Blo 706319 1061963 := bstep (se 1 (by rfl) ⟨796472, by rfl⟩ : syracuseStep 1061963 = 1592945) B1592945
theorem B898123 : Blo 706319 898123 := bstep (se 1 (by rfl) ⟨673592, by rfl⟩ : syracuseStep 898123 = 1347185) B1347185
theorem B1061975 : Blo 706319 1061975 := bstep (se 1 (by rfl) ⟨796481, by rfl⟩ : syracuseStep 1061975 = 1592963) B1592963
theorem B1062041 : Blo 706319 1062041 := bstep (se 2 (by rfl) ⟨398265, by rfl⟩ : syracuseStep 1062041 = 796531) B796531
theorem B1193177 : Blo 706319 1193177 := bstep (se 2 (by rfl) ⟨447441, by rfl⟩ : syracuseStep 1193177 = 894883) B894883
theorem B1062155 : Blo 706319 1062155 := bstep (se 1 (by rfl) ⟨796616, by rfl⟩ : syracuseStep 1062155 = 1593233) B1593233
theorem B1062167 : Blo 706319 1062167 := bstep (se 1 (by rfl) ⟨796625, by rfl⟩ : syracuseStep 1062167 = 1593251) B1593251
theorem B898391 : Blo 706319 898391 := bstep (se 1 (by rfl) ⟨673793, by rfl⟩ : syracuseStep 898391 = 1347587) B1347587
theorem B1193305 : Blo 706319 1193305 := bstep (se 2 (by rfl) ⟨447489, by rfl⟩ : syracuseStep 1193305 = 894979) B894979
theorem B1062233 : Blo 706319 1062233 := bstep (se 2 (by rfl) ⟨398337, by rfl⟩ : syracuseStep 1062233 = 796675) B796675
theorem B1062347 : Blo 706319 1062347 := bstep (se 1 (by rfl) ⟨796760, by rfl⟩ : syracuseStep 1062347 = 1593521) B1593521
theorem B1062359 : Blo 706319 1062359 := bstep (se 1 (by rfl) ⟨796769, by rfl⟩ : syracuseStep 1062359 = 1593539) B1593539
theorem B2012633 : Blo 706319 2012633 := bstep (se 2 (by rfl) ⟨754737, by rfl⟩ : syracuseStep 2012633 = 1509475) B1509475
theorem B3225091 : Blo 706319 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B1062425 : Blo 706319 1062425 := bstep (se 2 (by rfl) ⟨398409, by rfl⟩ : syracuseStep 1062425 = 796819) B796819
theorem B1062539 : Blo 706319 1062539 := bstep (se 1 (by rfl) ⟨796904, by rfl⟩ : syracuseStep 1062539 = 1593809) B1593809
theorem B4535959 : Blo 706319 4535959 := bstep (se 1 (by rfl) ⟨3401969, by rfl⟩ : syracuseStep 4535959 = 6803939) B6803939
theorem B1062551 : Blo 706319 1062551 := bstep (se 1 (by rfl) ⟨796913, by rfl⟩ : syracuseStep 1062551 = 1593827) B1593827
theorem B1062617 : Blo 706319 1062617 := bstep (se 2 (by rfl) ⟨398481, by rfl⟩ : syracuseStep 1062617 = 796963) B796963
theorem B2012951 : Blo 706319 2012951 := bstep (se 1 (by rfl) ⟨1509713, by rfl⟩ : syracuseStep 2012951 = 3019427) B3019427
theorem B5748515 : Blo 706319 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B1062731 : Blo 706319 1062731 := bstep (se 1 (by rfl) ⟨797048, by rfl⟩ : syracuseStep 1062731 = 1594097) B1594097
theorem B1062743 : Blo 706319 1062743 := bstep (se 1 (by rfl) ⟨797057, by rfl⟩ : syracuseStep 1062743 = 1594115) B1594115
theorem B1193879 : Blo 706319 1193879 := bstep (se 1 (by rfl) ⟨895409, by rfl⟩ : syracuseStep 1193879 = 1790819) B1790819
theorem B1062809 : Blo 706319 1062809 := bstep (se 2 (by rfl) ⟨398553, by rfl⟩ : syracuseStep 1062809 = 797107) B797107
theorem B6043571 : Blo 706319 6043571 := bstep (se 1 (by rfl) ⟨4532678, by rfl⟩ : syracuseStep 6043571 = 9065357) B9065357
theorem B1062923 : Blo 706319 1062923 := bstep (se 1 (by rfl) ⟨797192, by rfl⟩ : syracuseStep 1062923 = 1594385) B1594385
theorem B1194007 : Blo 706319 1194007 := bstep (se 1 (by rfl) ⟨895505, by rfl⟩ : syracuseStep 1194007 = 1791011) B1791011
theorem B1062935 : Blo 706319 1062935 := bstep (se 1 (by rfl) ⟨797201, by rfl⟩ : syracuseStep 1062935 = 1594403) B1594403
theorem B5093441 : Blo 706319 5093441 := bstep (se 2 (by rfl) ⟨1910040, by rfl⟩ : syracuseStep 5093441 = 3820081) B3820081
theorem B1063001 : Blo 706319 1063001 := bstep (se 2 (by rfl) ⟨398625, by rfl⟩ : syracuseStep 1063001 = 797251) B797251
theorem B1063115 : Blo 706319 1063115 := bstep (se 1 (by rfl) ⟨797336, by rfl⟩ : syracuseStep 1063115 = 1594673) B1594673
theorem B1063127 : Blo 706319 1063127 := bstep (se 1 (by rfl) ⟨797345, by rfl⟩ : syracuseStep 1063127 = 1594691) B1594691
theorem B1063193 : Blo 706319 1063193 := bstep (se 2 (by rfl) ⟨398697, by rfl⟩ : syracuseStep 1063193 = 797395) B797395
theorem B1063307 : Blo 706319 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B3226007 : Blo 706319 3226007 := bstep (se 1 (by rfl) ⟨2419505, by rfl⟩ : syracuseStep 3226007 = 4839011) B4839011
theorem B1063319 : Blo 706319 1063319 := bstep (se 1 (by rfl) ⟨797489, by rfl⟩ : syracuseStep 1063319 = 1594979) B1594979
theorem B1063385 : Blo 706319 1063385 := bstep (se 2 (by rfl) ⟨398769, by rfl⟩ : syracuseStep 1063385 = 797539) B797539
theorem B9091601 : Blo 706319 9091601 := bstep (se 2 (by rfl) ⟨3409350, by rfl⟩ : syracuseStep 9091601 = 6818701) B6818701
theorem B2013761 : Blo 706319 2013761 := bstep (se 2 (by rfl) ⟨755160, by rfl⟩ : syracuseStep 2013761 = 1510321) B1510321
theorem B1063499 : Blo 706319 1063499 := bstep (se 1 (by rfl) ⟨797624, by rfl⟩ : syracuseStep 1063499 = 1595249) B1595249
theorem B1063511 : Blo 706319 1063511 := bstep (se 1 (by rfl) ⟨797633, by rfl⟩ : syracuseStep 1063511 = 1595267) B1595267
theorem B1194635 : Blo 706319 1194635 := bstep (se 1 (by rfl) ⟨895976, by rfl⟩ : syracuseStep 1194635 = 1791953) B1791953
theorem B1063577 : Blo 706319 1063577 := bstep (se 2 (by rfl) ⟨398841, by rfl⟩ : syracuseStep 1063577 = 797683) B797683
theorem B1194763 : Blo 706319 1194763 := bstep (se 1 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 1194763 = 1792145) B1792145
theorem B1063691 : Blo 706319 1063691 := bstep (se 1 (by rfl) ⟨797768, by rfl⟩ : syracuseStep 1063691 = 1595537) B1595537
theorem B3226391 : Blo 706319 3226391 := bstep (se 1 (by rfl) ⟨2419793, by rfl⟩ : syracuseStep 3226391 = 4839587) B4839587
theorem B1063703 : Blo 706319 1063703 := bstep (se 1 (by rfl) ⟨797777, by rfl⟩ : syracuseStep 1063703 = 1595555) B1595555
theorem B1063769 : Blo 706319 1063769 := bstep (se 2 (by rfl) ⟨398913, by rfl⟩ : syracuseStep 1063769 = 797827) B797827
theorem B16169827 : Blo 706319 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B1194905 : Blo 706319 1194905 := bstep (se 2 (by rfl) ⟨448089, by rfl⟩ : syracuseStep 1194905 = 896179) B896179
theorem B1063883 : Blo 706319 1063883 := bstep (se 1 (by rfl) ⟨797912, by rfl⟩ : syracuseStep 1063883 = 1595825) B1595825
theorem B1063895 : Blo 706319 1063895 := bstep (se 1 (by rfl) ⟨797921, by rfl⟩ : syracuseStep 1063895 = 1595843) B1595843
theorem B1195033 : Blo 706319 1195033 := bstep (se 2 (by rfl) ⟨448137, by rfl⟩ : syracuseStep 1195033 = 896275) B896275
theorem B1063961 : Blo 706319 1063961 := bstep (se 2 (by rfl) ⟨398985, by rfl⟩ : syracuseStep 1063961 = 797971) B797971
theorem B3587165 : Blo 706319 3587165 := bstep (se 3 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 3587165 = 1345187) B1345187
theorem B1064075 : Blo 706319 1064075 := bstep (se 1 (by rfl) ⟨798056, by rfl⟩ : syracuseStep 1064075 = 1596113) B1596113
theorem B1064087 : Blo 706319 1064087 := bstep (se 1 (by rfl) ⟨798065, by rfl⟩ : syracuseStep 1064087 = 1596131) B1596131
theorem B1064153 : Blo 706319 1064153 := bstep (se 2 (by rfl) ⟨399057, by rfl⟩ : syracuseStep 1064153 = 798115) B798115
theorem B10894657 : Blo 706319 10894657 := bstep (se 2 (by rfl) ⟨4085496, by rfl⟩ : syracuseStep 10894657 = 8170993) B8170993
theorem B4308299 : Blo 706319 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B1064267 : Blo 706319 1064267 := bstep (se 1 (by rfl) ⟨798200, by rfl⟩ : syracuseStep 1064267 = 1596401) B1596401
theorem B1064279 : Blo 706319 1064279 := bstep (se 1 (by rfl) ⟨798209, by rfl⟩ : syracuseStep 1064279 = 1596419) B1596419
theorem B1064345 : Blo 706319 1064345 := bstep (se 2 (by rfl) ⟨399129, by rfl⟩ : syracuseStep 1064345 = 798259) B798259
theorem B1064459 : Blo 706319 1064459 := bstep (se 1 (by rfl) ⟨798344, by rfl⟩ : syracuseStep 1064459 = 1596689) B1596689
theorem B1064471 : Blo 706319 1064471 := bstep (se 1 (by rfl) ⟨798353, by rfl⟩ : syracuseStep 1064471 = 1596707) B1596707
theorem B7781923 : Blo 706319 7781923 := bstep (se 1 (by rfl) ⟨5836442, by rfl⟩ : syracuseStep 7781923 = 11672885) B11672885
theorem B1195607 : Blo 706319 1195607 := bstep (se 1 (by rfl) ⟨896705, by rfl⟩ : syracuseStep 1195607 = 1793411) B1793411
theorem B1064537 : Blo 706319 1064537 := bstep (se 2 (by rfl) ⟨399201, by rfl⟩ : syracuseStep 1064537 = 798403) B798403
theorem B4537957 : Blo 706319 4537957 := bstep (se 4 (by rfl) ⟨425433, by rfl⟩ : syracuseStep 4537957 = 850867) B850867
theorem B1064651 : Blo 706319 1064651 := bstep (se 1 (by rfl) ⟨798488, by rfl⟩ : syracuseStep 1064651 = 1596977) B1596977
theorem B1195735 : Blo 706319 1195735 := bstep (se 1 (by rfl) ⟨896801, by rfl⟩ : syracuseStep 1195735 = 1793603) B1793603
theorem B1064663 : Blo 706319 1064663 := bstep (se 1 (by rfl) ⟨798497, by rfl⟩ : syracuseStep 1064663 = 1596995) B1596995
theorem B1064729 : Blo 706319 1064729 := bstep (se 2 (by rfl) ⟨399273, by rfl⟩ : syracuseStep 1064729 = 798547) B798547
theorem B1916723 : Blo 706319 1916723 := bstep (se 1 (by rfl) ⟨1437542, by rfl⟩ : syracuseStep 1916723 = 2875085) B2875085
theorem B1064843 : Blo 706319 1064843 := bstep (se 1 (by rfl) ⟨798632, by rfl⟩ : syracuseStep 1064843 = 1597265) B1597265
theorem B1064855 : Blo 706319 1064855 := bstep (se 1 (by rfl) ⟨798641, by rfl⟩ : syracuseStep 1064855 = 1597283) B1597283
theorem B5095345 : Blo 706319 5095345 := bstep (se 2 (by rfl) ⟨1910754, by rfl⟩ : syracuseStep 5095345 = 3821509) B3821509
theorem B1064921 : Blo 706319 1064921 := bstep (se 2 (by rfl) ⟨399345, by rfl⟩ : syracuseStep 1064921 = 798691) B798691
theorem B1589273 : Blo 706319 1589273 := bstep (se 2 (by rfl) ⟨595977, by rfl⟩ : syracuseStep 1589273 = 1191955) B1191955
theorem B1065035 : Blo 706319 1065035 := bstep (se 1 (by rfl) ⟨798776, by rfl⟩ : syracuseStep 1065035 = 1597553) B1597553
theorem B1065047 : Blo 706319 1065047 := bstep (se 1 (by rfl) ⟨798785, by rfl⟩ : syracuseStep 1065047 = 1597571) B1597571
theorem B1818713 : Blo 706319 1818713 := bstep (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) B1364035
theorem B1589363 : Blo 706319 1589363 := bstep (se 1 (by rfl) ⟨1192022, by rfl⟩ : syracuseStep 1589363 = 2384045) B2384045
theorem B1589399 : Blo 706319 1589399 := bstep (se 1 (by rfl) ⟨1192049, by rfl⟩ : syracuseStep 1589399 = 2384099) B2384099
theorem B1065113 : Blo 706319 1065113 := bstep (se 2 (by rfl) ⟨399417, by rfl⟩ : syracuseStep 1065113 = 798835) B798835
theorem B2015435 : Blo 706319 2015435 := bstep (se 1 (by rfl) ⟨1511576, by rfl⟩ : syracuseStep 2015435 = 3023153) B3023153
theorem B1065227 : Blo 706319 1065227 := bstep (se 1 (by rfl) ⟨798920, by rfl⟩ : syracuseStep 1065227 = 1597841) B1597841
theorem B3031319 : Blo 706319 3031319 := bstep (se 1 (by rfl) ⟨2273489, by rfl⟩ : syracuseStep 3031319 = 4546979) B4546979
theorem B1065239 : Blo 706319 1065239 := bstep (se 1 (by rfl) ⟨798929, by rfl⟩ : syracuseStep 1065239 = 1597859) B1597859
theorem B1589579 : Blo 706319 1589579 := bstep (se 1 (by rfl) ⟨1192184, by rfl⟩ : syracuseStep 1589579 = 2384369) B2384369
theorem B1196363 : Blo 706319 1196363 := bstep (se 1 (by rfl) ⟨897272, by rfl⟩ : syracuseStep 1196363 = 1794545) B1794545
theorem B1065305 : Blo 706319 1065305 := bstep (se 2 (by rfl) ⟨399489, by rfl⟩ : syracuseStep 1065305 = 798979) B798979
theorem B1589633 : Blo 706319 1589633 := bstep (se 2 (by rfl) ⟨596112, by rfl⟩ : syracuseStep 1589633 = 1192225) B1192225
theorem B1196491 : Blo 706319 1196491 := bstep (se 1 (by rfl) ⟨897368, by rfl⟩ : syracuseStep 1196491 = 1794737) B1794737
theorem B1065419 : Blo 706319 1065419 := bstep (se 1 (by rfl) ⟨799064, by rfl⟩ : syracuseStep 1065419 = 1598129) B1598129
theorem B1065431 : Blo 706319 1065431 := bstep (se 1 (by rfl) ⟨799073, by rfl⟩ : syracuseStep 1065431 = 1598147) B1598147
theorem B6472153 : Blo 706319 6472153 := bstep (se 2 (by rfl) ⟨2427057, by rfl⟩ : syracuseStep 6472153 = 4854115) B4854115
theorem B3031627 : Blo 706319 3031627 := bstep (se 1 (by rfl) ⟨2273720, by rfl⟩ : syracuseStep 3031627 = 4547441) B4547441
theorem B1589849 : Blo 706319 1589849 := bstep (se 2 (by rfl) ⟨596193, by rfl⟩ : syracuseStep 1589849 = 1192387) B1192387
theorem B1196633 : Blo 706319 1196633 := bstep (se 2 (by rfl) ⟨448737, by rfl⟩ : syracuseStep 1196633 = 897475) B897475
theorem B1589939 : Blo 706319 1589939 := bstep (se 1 (by rfl) ⟨1192454, by rfl⟩ : syracuseStep 1589939 = 2384909) B2384909
theorem B1589975 : Blo 706319 1589975 := bstep (se 1 (by rfl) ⟨1192481, by rfl⟩ : syracuseStep 1589975 = 2384963) B2384963
theorem B1196761 : Blo 706319 1196761 := bstep (se 2 (by rfl) ⟨448785, by rfl⟩ : syracuseStep 1196761 = 897571) B897571
theorem B3031901 : Blo 706319 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B5391197 : Blo 706319 5391197 := bstep (se 3 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 5391197 = 2021699) B2021699
theorem B1590155 : Blo 706319 1590155 := bstep (se 1 (by rfl) ⟨1192616, by rfl⟩ : syracuseStep 1590155 = 2385233) B2385233
theorem B1590209 : Blo 706319 1590209 := bstep (se 2 (by rfl) ⟨596328, by rfl⟩ : syracuseStep 1590209 = 1192657) B1192657
theorem B1131479 : Blo 706319 1131479 := bstep (se 1 (by rfl) ⟨848609, by rfl⟩ : syracuseStep 1131479 = 1697219) B1697219
theorem B13648931 : Blo 706319 13648931 := bstep (se 1 (by rfl) ⟨10236698, by rfl⟩ : syracuseStep 13648931 = 20473397) B20473397
theorem B3589271 : Blo 706319 3589271 := bstep (se 1 (by rfl) ⟨2691953, by rfl⟩ : syracuseStep 3589271 = 5383907) B5383907
theorem B1590425 : Blo 706319 1590425 := bstep (se 2 (by rfl) ⟨596409, by rfl⟩ : syracuseStep 1590425 = 1192819) B1192819
theorem B1590515 : Blo 706319 1590515 := bstep (se 1 (by rfl) ⟨1192886, by rfl⟩ : syracuseStep 1590515 = 2385773) B2385773
theorem B1590551 : Blo 706319 1590551 := bstep (se 1 (by rfl) ⟨1192913, by rfl⟩ : syracuseStep 1590551 = 2385827) B2385827
theorem B1197335 : Blo 706319 1197335 := bstep (se 1 (by rfl) ⟨898001, by rfl⟩ : syracuseStep 1197335 = 1796003) B1796003
theorem B1197463 : Blo 706319 1197463 := bstep (se 1 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 1197463 = 1796195) B1796195
theorem B3458483 : Blo 706319 3458483 := bstep (se 1 (by rfl) ⟨2593862, by rfl⟩ : syracuseStep 3458483 = 5187725) B5187725
theorem B1590731 : Blo 706319 1590731 := bstep (se 1 (by rfl) ⟨1193048, by rfl⟩ : syracuseStep 1590731 = 2386097) B2386097
theorem B2016733 : Blo 706319 2016733 := bstep (se 3 (by rfl) ⟨378137, by rfl⟩ : syracuseStep 2016733 = 756275) B756275
theorem B1590785 : Blo 706319 1590785 := bstep (se 2 (by rfl) ⟨596544, by rfl⟩ : syracuseStep 1590785 = 1193089) B1193089
theorem B6047297 : Blo 706319 6047297 := bstep (se 2 (by rfl) ⟨2267736, by rfl⟩ : syracuseStep 6047297 = 4535473) B4535473
theorem B12076613 : Blo 706319 12076613 := bstep (se 4 (by rfl) ⟨1132182, by rfl⟩ : syracuseStep 12076613 = 2264365) B2264365
theorem B5457613 : Blo 706319 5457613 := bstep (se 3 (by rfl) ⟨1023302, by rfl⟩ : syracuseStep 5457613 = 2046605) B2046605
theorem B1591001 : Blo 706319 1591001 := bstep (se 2 (by rfl) ⟨596625, by rfl⟩ : syracuseStep 1591001 = 1193251) B1193251
theorem B706327 : Blo 706319 706327 := bstep (se 1 (by rfl) ⟨529745, by rfl⟩ : syracuseStep 706327 = 1059491) B1059491
theorem B706347 : Blo 706319 706347 := bstep (se 1 (by rfl) ⟨529760, by rfl⟩ : syracuseStep 706347 = 1059521) B1059521
theorem B1591091 : Blo 706319 1591091 := bstep (se 1 (by rfl) ⟨1193318, by rfl⟩ : syracuseStep 1591091 = 2386637) B2386637
theorem B2017075 : Blo 706319 2017075 := bstep (se 1 (by rfl) ⟨1512806, by rfl⟩ : syracuseStep 2017075 = 3025613) B3025613
theorem B706359 : Blo 706319 706359 := bstep (se 1 (by rfl) ⟨529769, by rfl⟩ : syracuseStep 706359 = 1059539) B1059539
theorem B706379 : Blo 706319 706379 := bstep (se 1 (by rfl) ⟨529784, by rfl⟩ : syracuseStep 706379 = 1059569) B1059569
theorem B2869067 : Blo 706319 2869067 := bstep (se 1 (by rfl) ⟨2151800, by rfl⟩ : syracuseStep 2869067 = 4303601) B4303601
theorem B706391 : Blo 706319 706391 := bstep (se 1 (by rfl) ⟨529793, by rfl⟩ : syracuseStep 706391 = 1059587) B1059587
theorem B1591127 : Blo 706319 1591127 := bstep (se 1 (by rfl) ⟨1193345, by rfl⟩ : syracuseStep 1591127 = 2386691) B2386691
theorem B706411 : Blo 706319 706411 := bstep (se 1 (by rfl) ⟨529808, by rfl⟩ : syracuseStep 706411 = 1059617) B1059617
theorem B706423 : Blo 706319 706423 := bstep (se 1 (by rfl) ⟨529817, by rfl⟩ : syracuseStep 706423 = 1059635) B1059635
theorem B706443 : Blo 706319 706443 := bstep (se 1 (by rfl) ⟨529832, by rfl⟩ : syracuseStep 706443 = 1059665) B1059665
theorem B706455 : Blo 706319 706455 := bstep (se 1 (by rfl) ⟨529841, by rfl⟩ : syracuseStep 706455 = 1059683) B1059683
theorem B1132439 : Blo 706319 1132439 := bstep (se 1 (by rfl) ⟨849329, by rfl⟩ : syracuseStep 1132439 = 1698659) B1698659
theorem B706475 : Blo 706319 706475 := bstep (se 1 (by rfl) ⟨529856, by rfl⟩ : syracuseStep 706475 = 1059713) B1059713
theorem B11519921 : Blo 706319 11519921 := bstep (se 2 (by rfl) ⟨4319970, by rfl⟩ : syracuseStep 11519921 = 8639941) B8639941
theorem B706487 : Blo 706319 706487 := bstep (se 1 (by rfl) ⟨529865, by rfl⟩ : syracuseStep 706487 = 1059731) B1059731
theorem B706507 : Blo 706319 706507 := bstep (se 1 (by rfl) ⟨529880, by rfl⟩ : syracuseStep 706507 = 1059761) B1059761
theorem B706519 : Blo 706319 706519 := bstep (se 1 (by rfl) ⟨529889, by rfl⟩ : syracuseStep 706519 = 1059779) B1059779
theorem B706539 : Blo 706319 706539 := bstep (se 1 (by rfl) ⟨529904, by rfl⟩ : syracuseStep 706539 = 1059809) B1059809
theorem B706551 : Blo 706319 706551 := bstep (se 1 (by rfl) ⟨529913, by rfl⟩ : syracuseStep 706551 = 1059827) B1059827
theorem B706571 : Blo 706319 706571 := bstep (se 1 (by rfl) ⟨529928, by rfl⟩ : syracuseStep 706571 = 1059857) B1059857
theorem B1132555 : Blo 706319 1132555 := bstep (se 1 (by rfl) ⟨849416, by rfl⟩ : syracuseStep 1132555 = 1698833) B1698833
theorem B1591307 : Blo 706319 1591307 := bstep (se 1 (by rfl) ⟨1193480, by rfl⟩ : syracuseStep 1591307 = 2386961) B2386961
theorem B1198091 : Blo 706319 1198091 := bstep (se 1 (by rfl) ⟨898568, by rfl⟩ : syracuseStep 1198091 = 1797137) B1797137
theorem B706583 : Blo 706319 706583 := bstep (se 1 (by rfl) ⟨529937, by rfl⟩ : syracuseStep 706583 = 1059875) B1059875
theorem B706603 : Blo 706319 706603 := bstep (se 1 (by rfl) ⟨529952, by rfl⟩ : syracuseStep 706603 = 1059905) B1059905
theorem B706615 : Blo 706319 706615 := bstep (se 1 (by rfl) ⟨529961, by rfl⟩ : syracuseStep 706615 = 1059923) B1059923
theorem B1591361 : Blo 706319 1591361 := bstep (se 2 (by rfl) ⟨596760, by rfl⟩ : syracuseStep 1591361 = 1193521) B1193521
theorem B706635 : Blo 706319 706635 := bstep (se 1 (by rfl) ⟨529976, by rfl⟩ : syracuseStep 706635 = 1059953) B1059953
theorem B706647 : Blo 706319 706647 := bstep (se 1 (by rfl) ⟨529985, by rfl⟩ : syracuseStep 706647 = 1059971) B1059971
theorem B706667 : Blo 706319 706667 := bstep (se 1 (by rfl) ⟨530000, by rfl⟩ : syracuseStep 706667 = 1060001) B1060001
theorem B706679 : Blo 706319 706679 := bstep (se 1 (by rfl) ⟨530009, by rfl⟩ : syracuseStep 706679 = 1060019) B1060019
theorem B706699 : Blo 706319 706699 := bstep (se 1 (by rfl) ⟨530024, by rfl⟩ : syracuseStep 706699 = 1060049) B1060049
theorem B1198219 : Blo 706319 1198219 := bstep (se 1 (by rfl) ⟨898664, by rfl⟩ : syracuseStep 1198219 = 1797329) B1797329
theorem B3033233 : Blo 706319 3033233 := bstep (se 2 (by rfl) ⟨1137462, by rfl⟩ : syracuseStep 3033233 = 2274925) B2274925
theorem B706711 : Blo 706319 706711 := bstep (se 1 (by rfl) ⟨530033, by rfl⟩ : syracuseStep 706711 = 1060067) B1060067
theorem B706731 : Blo 706319 706731 := bstep (se 1 (by rfl) ⟨530048, by rfl⟩ : syracuseStep 706731 = 1060097) B1060097
theorem B706743 : Blo 706319 706743 := bstep (se 1 (by rfl) ⟨530057, by rfl⟩ : syracuseStep 706743 = 1060115) B1060115
theorem B706763 : Blo 706319 706763 := bstep (se 1 (by rfl) ⟨530072, by rfl⟩ : syracuseStep 706763 = 1060145) B1060145
theorem B706775 : Blo 706319 706775 := bstep (se 1 (by rfl) ⟨530081, by rfl⟩ : syracuseStep 706775 = 1060163) B1060163
theorem B706795 : Blo 706319 706795 := bstep (se 1 (by rfl) ⟨530096, by rfl⟩ : syracuseStep 706795 = 1060193) B1060193
theorem B706807 : Blo 706319 706807 := bstep (se 1 (by rfl) ⟨530105, by rfl⟩ : syracuseStep 706807 = 1060211) B1060211
theorem B706827 : Blo 706319 706827 := bstep (se 1 (by rfl) ⟨530120, by rfl⟩ : syracuseStep 706827 = 1060241) B1060241
theorem B706839 : Blo 706319 706839 := bstep (se 1 (by rfl) ⟨530129, by rfl⟩ : syracuseStep 706839 = 1060259) B1060259
theorem B1591577 : Blo 706319 1591577 := bstep (se 2 (by rfl) ⟨596841, by rfl⟩ : syracuseStep 1591577 = 1193683) B1193683
theorem B1198361 : Blo 706319 1198361 := bstep (se 2 (by rfl) ⟨449385, by rfl⟩ : syracuseStep 1198361 = 898771) B898771
theorem B706859 : Blo 706319 706859 := bstep (se 1 (by rfl) ⟨530144, by rfl⟩ : syracuseStep 706859 = 1060289) B1060289
theorem B706871 : Blo 706319 706871 := bstep (se 1 (by rfl) ⟨530153, by rfl⟩ : syracuseStep 706871 = 1060307) B1060307
theorem B706891 : Blo 706319 706891 := bstep (se 1 (by rfl) ⟨530168, by rfl⟩ : syracuseStep 706891 = 1060337) B1060337
theorem B706903 : Blo 706319 706903 := bstep (se 1 (by rfl) ⟨530177, by rfl⟩ : syracuseStep 706903 = 1060355) B1060355
theorem B706923 : Blo 706319 706923 := bstep (se 1 (by rfl) ⟨530192, by rfl⟩ : syracuseStep 706923 = 1060385) B1060385
theorem B1591667 : Blo 706319 1591667 := bstep (se 1 (by rfl) ⟨1193750, by rfl⟩ : syracuseStep 1591667 = 2387501) B2387501
theorem B706935 : Blo 706319 706935 := bstep (se 1 (by rfl) ⟨530201, by rfl⟩ : syracuseStep 706935 = 1060403) B1060403
theorem B706955 : Blo 706319 706955 := bstep (se 1 (by rfl) ⟨530216, by rfl⟩ : syracuseStep 706955 = 1060433) B1060433
theorem B706967 : Blo 706319 706967 := bstep (se 1 (by rfl) ⟨530225, by rfl⟩ : syracuseStep 706967 = 1060451) B1060451
theorem B1591703 : Blo 706319 1591703 := bstep (se 1 (by rfl) ⟨1193777, by rfl⟩ : syracuseStep 1591703 = 2387555) B2387555
theorem B1198489 : Blo 706319 1198489 := bstep (se 2 (by rfl) ⟨449433, by rfl⟩ : syracuseStep 1198489 = 898867) B898867
theorem B706987 : Blo 706319 706987 := bstep (se 1 (by rfl) ⟨530240, by rfl⟩ : syracuseStep 706987 = 1060481) B1060481
theorem B706999 : Blo 706319 706999 := bstep (se 1 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 706999 = 1060499) B1060499
theorem B707019 : Blo 706319 707019 := bstep (se 1 (by rfl) ⟨530264, by rfl⟩ : syracuseStep 707019 = 1060529) B1060529
theorem B707031 : Blo 706319 707031 := bstep (se 1 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 707031 = 1060547) B1060547
theorem B707051 : Blo 706319 707051 := bstep (se 1 (by rfl) ⟨530288, by rfl⟩ : syracuseStep 707051 = 1060577) B1060577
theorem B707063 : Blo 706319 707063 := bstep (se 1 (by rfl) ⟨530297, by rfl⟩ : syracuseStep 707063 = 1060595) B1060595
theorem B707083 : Blo 706319 707083 := bstep (se 1 (by rfl) ⟨530312, by rfl⟩ : syracuseStep 707083 = 1060625) B1060625
theorem B1788439 : Blo 706319 1788439 := bstep (se 1 (by rfl) ⟨1341329, by rfl⟩ : syracuseStep 1788439 = 2682659) B2682659
theorem B707095 : Blo 706319 707095 := bstep (se 1 (by rfl) ⟨530321, by rfl⟩ : syracuseStep 707095 = 1060643) B1060643
theorem B707115 : Blo 706319 707115 := bstep (se 1 (by rfl) ⟨530336, by rfl⟩ : syracuseStep 707115 = 1060673) B1060673
theorem B707127 : Blo 706319 707127 := bstep (se 1 (by rfl) ⟨530345, by rfl⟩ : syracuseStep 707127 = 1060691) B1060691
theorem B707147 : Blo 706319 707147 := bstep (se 1 (by rfl) ⟨530360, by rfl⟩ : syracuseStep 707147 = 1060721) B1060721
theorem B1591883 : Blo 706319 1591883 := bstep (se 1 (by rfl) ⟨1193912, by rfl⟩ : syracuseStep 1591883 = 2387825) B2387825
theorem B3066443 : Blo 706319 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B707159 : Blo 706319 707159 := bstep (se 1 (by rfl) ⟨530369, by rfl⟩ : syracuseStep 707159 = 1060739) B1060739
theorem B707179 : Blo 706319 707179 := bstep (se 1 (by rfl) ⟨530384, by rfl⟩ : syracuseStep 707179 = 1060769) B1060769
theorem B707191 : Blo 706319 707191 := bstep (se 1 (by rfl) ⟨530393, by rfl⟩ : syracuseStep 707191 = 1060787) B1060787
theorem B1591937 : Blo 706319 1591937 := bstep (se 2 (by rfl) ⟨596976, by rfl⟩ : syracuseStep 1591937 = 1193953) B1193953
theorem B707211 : Blo 706319 707211 := bstep (se 1 (by rfl) ⟨530408, by rfl⟩ : syracuseStep 707211 = 1060817) B1060817
theorem B707223 : Blo 706319 707223 := bstep (se 1 (by rfl) ⟨530417, by rfl⟩ : syracuseStep 707223 = 1060835) B1060835
theorem B707243 : Blo 706319 707243 := bstep (se 1 (by rfl) ⟨530432, by rfl⟩ : syracuseStep 707243 = 1060865) B1060865
theorem B707255 : Blo 706319 707255 := bstep (se 1 (by rfl) ⟨530441, by rfl⟩ : syracuseStep 707255 = 1060883) B1060883
theorem B707275 : Blo 706319 707275 := bstep (se 1 (by rfl) ⟨530456, by rfl⟩ : syracuseStep 707275 = 1060913) B1060913
theorem B707287 : Blo 706319 707287 := bstep (se 1 (by rfl) ⟨530465, by rfl⟩ : syracuseStep 707287 = 1060931) B1060931
theorem B1133273 : Blo 706319 1133273 := bstep (se 2 (by rfl) ⟨424977, by rfl⟩ : syracuseStep 1133273 = 849955) B849955
theorem B2018009 : Blo 706319 2018009 := bstep (se 2 (by rfl) ⟨756753, by rfl⟩ : syracuseStep 2018009 = 1513507) B1513507
theorem B707307 : Blo 706319 707307 := bstep (se 1 (by rfl) ⟨530480, by rfl⟩ : syracuseStep 707307 = 1060961) B1060961
theorem B707319 : Blo 706319 707319 := bstep (se 1 (by rfl) ⟨530489, by rfl⟩ : syracuseStep 707319 = 1060979) B1060979
theorem B707339 : Blo 706319 707339 := bstep (se 1 (by rfl) ⟨530504, by rfl⟩ : syracuseStep 707339 = 1061009) B1061009
theorem B707351 : Blo 706319 707351 := bstep (se 1 (by rfl) ⟨530513, by rfl⟩ : syracuseStep 707351 = 1061027) B1061027
theorem B707371 : Blo 706319 707371 := bstep (se 1 (by rfl) ⟨530528, by rfl⟩ : syracuseStep 707371 = 1061057) B1061057
theorem B707383 : Blo 706319 707383 := bstep (se 1 (by rfl) ⟨530537, by rfl⟩ : syracuseStep 707383 = 1061075) B1061075
theorem B707403 : Blo 706319 707403 := bstep (se 1 (by rfl) ⟨530552, by rfl⟩ : syracuseStep 707403 = 1061105) B1061105
theorem B707415 : Blo 706319 707415 := bstep (se 1 (by rfl) ⟨530561, by rfl⟩ : syracuseStep 707415 = 1061123) B1061123
theorem B1592153 : Blo 706319 1592153 := bstep (se 2 (by rfl) ⟨597057, by rfl⟩ : syracuseStep 1592153 = 1194115) B1194115
theorem B1919837 : Blo 706319 1919837 := bstep (se 3 (by rfl) ⟨359969, by rfl⟩ : syracuseStep 1919837 = 719939) B719939
theorem B707435 : Blo 706319 707435 := bstep (se 1 (by rfl) ⟨530576, by rfl⟩ : syracuseStep 707435 = 1061153) B1061153
theorem B707447 : Blo 706319 707447 := bstep (se 1 (by rfl) ⟨530585, by rfl⟩ : syracuseStep 707447 = 1061171) B1061171
theorem B707467 : Blo 706319 707467 := bstep (se 1 (by rfl) ⟨530600, by rfl⟩ : syracuseStep 707467 = 1061201) B1061201
theorem B707479 : Blo 706319 707479 := bstep (se 1 (by rfl) ⟨530609, by rfl⟩ : syracuseStep 707479 = 1061219) B1061219
theorem B707499 : Blo 706319 707499 := bstep (se 1 (by rfl) ⟨530624, by rfl⟩ : syracuseStep 707499 = 1061249) B1061249
theorem B1592243 : Blo 706319 1592243 := bstep (se 1 (by rfl) ⟨1194182, by rfl⟩ : syracuseStep 1592243 = 2388365) B2388365
theorem B707511 : Blo 706319 707511 := bstep (se 1 (by rfl) ⟨530633, by rfl⟩ : syracuseStep 707511 = 1061267) B1061267
theorem B1788875 : Blo 706319 1788875 := bstep (se 1 (by rfl) ⟨1341656, by rfl⟩ : syracuseStep 1788875 = 2683313) B2683313
theorem B707531 : Blo 706319 707531 := bstep (se 1 (by rfl) ⟨530648, by rfl⟩ : syracuseStep 707531 = 1061297) B1061297
theorem B707543 : Blo 706319 707543 := bstep (se 1 (by rfl) ⟨530657, by rfl⟩ : syracuseStep 707543 = 1061315) B1061315
theorem B1592279 : Blo 706319 1592279 := bstep (se 1 (by rfl) ⟨1194209, by rfl⟩ : syracuseStep 1592279 = 2388419) B2388419
theorem B707563 : Blo 706319 707563 := bstep (se 1 (by rfl) ⟨530672, by rfl⟩ : syracuseStep 707563 = 1061345) B1061345
theorem B707575 : Blo 706319 707575 := bstep (se 1 (by rfl) ⟨530681, by rfl⟩ : syracuseStep 707575 = 1061363) B1061363
theorem B707595 : Blo 706319 707595 := bstep (se 1 (by rfl) ⟨530696, by rfl⟩ : syracuseStep 707595 = 1061393) B1061393
theorem B707607 : Blo 706319 707607 := bstep (se 1 (by rfl) ⟨530705, by rfl⟩ : syracuseStep 707607 = 1061411) B1061411
theorem B707627 : Blo 706319 707627 := bstep (se 1 (by rfl) ⟨530720, by rfl⟩ : syracuseStep 707627 = 1061441) B1061441
theorem B707639 : Blo 706319 707639 := bstep (se 1 (by rfl) ⟨530729, by rfl⟩ : syracuseStep 707639 = 1061459) B1061459
theorem B707659 : Blo 706319 707659 := bstep (se 1 (by rfl) ⟨530744, by rfl⟩ : syracuseStep 707659 = 1061489) B1061489
theorem B707671 : Blo 706319 707671 := bstep (se 1 (by rfl) ⟨530753, by rfl⟩ : syracuseStep 707671 = 1061507) B1061507
theorem B707691 : Blo 706319 707691 := bstep (se 1 (by rfl) ⟨530768, by rfl⟩ : syracuseStep 707691 = 1061537) B1061537
theorem B707703 : Blo 706319 707703 := bstep (se 1 (by rfl) ⟨530777, by rfl⟩ : syracuseStep 707703 = 1061555) B1061555
theorem B707723 : Blo 706319 707723 := bstep (se 1 (by rfl) ⟨530792, by rfl⟩ : syracuseStep 707723 = 1061585) B1061585
theorem B1592459 : Blo 706319 1592459 := bstep (se 1 (by rfl) ⟨1194344, by rfl⟩ : syracuseStep 1592459 = 2388689) B2388689
theorem B707735 : Blo 706319 707735 := bstep (se 1 (by rfl) ⟨530801, by rfl⟩ : syracuseStep 707735 = 1061603) B1061603
theorem B707755 : Blo 706319 707755 := bstep (se 1 (by rfl) ⟨530816, by rfl⟩ : syracuseStep 707755 = 1061633) B1061633
theorem B707767 : Blo 706319 707767 := bstep (se 1 (by rfl) ⟨530825, by rfl⟩ : syracuseStep 707767 = 1061651) B1061651
theorem B1592513 : Blo 706319 1592513 := bstep (se 2 (by rfl) ⟨597192, by rfl⟩ : syracuseStep 1592513 = 1194385) B1194385
theorem B707787 : Blo 706319 707787 := bstep (se 1 (by rfl) ⟨530840, by rfl⟩ : syracuseStep 707787 = 1061681) B1061681
theorem B707799 : Blo 706319 707799 := bstep (se 1 (by rfl) ⟨530849, by rfl⟩ : syracuseStep 707799 = 1061699) B1061699
theorem B1133785 : Blo 706319 1133785 := bstep (se 2 (by rfl) ⟨425169, by rfl⟩ : syracuseStep 1133785 = 850339) B850339
theorem B707819 : Blo 706319 707819 := bstep (se 1 (by rfl) ⟨530864, by rfl⟩ : syracuseStep 707819 = 1061729) B1061729
theorem B707831 : Blo 706319 707831 := bstep (se 1 (by rfl) ⟨530873, by rfl⟩ : syracuseStep 707831 = 1061747) B1061747
theorem B707851 : Blo 706319 707851 := bstep (se 1 (by rfl) ⟨530888, by rfl⟩ : syracuseStep 707851 = 1061777) B1061777
theorem B707863 : Blo 706319 707863 := bstep (se 1 (by rfl) ⟨530897, by rfl⟩ : syracuseStep 707863 = 1061795) B1061795
theorem B707883 : Blo 706319 707883 := bstep (se 1 (by rfl) ⟨530912, by rfl⟩ : syracuseStep 707883 = 1061825) B1061825
theorem B707895 : Blo 706319 707895 := bstep (se 1 (by rfl) ⟨530921, by rfl⟩ : syracuseStep 707895 = 1061843) B1061843
theorem B1789249 : Blo 706319 1789249 := bstep (se 2 (by rfl) ⟨670968, by rfl⟩ : syracuseStep 1789249 = 1341937) B1341937
theorem B707915 : Blo 706319 707915 := bstep (se 1 (by rfl) ⟨530936, by rfl⟩ : syracuseStep 707915 = 1061873) B1061873
theorem B707927 : Blo 706319 707927 := bstep (se 1 (by rfl) ⟨530945, by rfl⟩ : syracuseStep 707927 = 1061891) B1061891
theorem B707947 : Blo 706319 707947 := bstep (se 1 (by rfl) ⟨530960, by rfl⟩ : syracuseStep 707947 = 1061921) B1061921
theorem B707959 : Blo 706319 707959 := bstep (se 1 (by rfl) ⟨530969, by rfl⟩ : syracuseStep 707959 = 1061939) B1061939
theorem B707979 : Blo 706319 707979 := bstep (se 1 (by rfl) ⟨530984, by rfl⟩ : syracuseStep 707979 = 1061969) B1061969
theorem B707991 : Blo 706319 707991 := bstep (se 1 (by rfl) ⟨530993, by rfl⟩ : syracuseStep 707991 = 1061987) B1061987
theorem B1592729 : Blo 706319 1592729 := bstep (se 2 (by rfl) ⟨597273, by rfl⟩ : syracuseStep 1592729 = 1194547) B1194547
theorem B708011 : Blo 706319 708011 := bstep (se 1 (by rfl) ⟨531008, by rfl⟩ : syracuseStep 708011 = 1062017) B1062017
theorem B708023 : Blo 706319 708023 := bstep (se 1 (by rfl) ⟨531017, by rfl⟩ : syracuseStep 708023 = 1062035) B1062035
theorem B708043 : Blo 706319 708043 := bstep (se 1 (by rfl) ⟨531032, by rfl⟩ : syracuseStep 708043 = 1062065) B1062065
theorem B708055 : Blo 706319 708055 := bstep (se 1 (by rfl) ⟨531041, by rfl⟩ : syracuseStep 708055 = 1062083) B1062083
theorem B708075 : Blo 706319 708075 := bstep (se 1 (by rfl) ⟨531056, by rfl⟩ : syracuseStep 708075 = 1062113) B1062113
theorem B1592819 : Blo 706319 1592819 := bstep (se 1 (by rfl) ⟨1194614, by rfl⟩ : syracuseStep 1592819 = 2389229) B2389229
theorem B708087 : Blo 706319 708087 := bstep (se 1 (by rfl) ⟨531065, by rfl⟩ : syracuseStep 708087 = 1062131) B1062131
theorem B708107 : Blo 706319 708107 := bstep (se 1 (by rfl) ⟨531080, by rfl⟩ : syracuseStep 708107 = 1062161) B1062161
theorem B1592855 : Blo 706319 1592855 := bstep (se 1 (by rfl) ⟨1194641, by rfl⟩ : syracuseStep 1592855 = 2389283) B2389283
theorem B708119 : Blo 706319 708119 := bstep (se 1 (by rfl) ⟨531089, by rfl⟩ : syracuseStep 708119 = 1062179) B1062179
theorem B708139 : Blo 706319 708139 := bstep (se 1 (by rfl) ⟨531104, by rfl⟩ : syracuseStep 708139 = 1062209) B1062209
theorem B806455 : Blo 706319 806455 := bstep (se 1 (by rfl) ⟨604841, by rfl⟩ : syracuseStep 806455 = 1209683) B1209683
theorem B708151 : Blo 706319 708151 := bstep (se 1 (by rfl) ⟨531113, by rfl⟩ : syracuseStep 708151 = 1062227) B1062227
theorem B708171 : Blo 706319 708171 := bstep (se 1 (by rfl) ⟨531128, by rfl⟩ : syracuseStep 708171 = 1062257) B1062257
theorem B708183 : Blo 706319 708183 := bstep (se 1 (by rfl) ⟨531137, by rfl⟩ : syracuseStep 708183 = 1062275) B1062275
theorem B708203 : Blo 706319 708203 := bstep (se 1 (by rfl) ⟨531152, by rfl⟩ : syracuseStep 708203 = 1062305) B1062305
theorem B708215 : Blo 706319 708215 := bstep (se 1 (by rfl) ⟨531161, by rfl⟩ : syracuseStep 708215 = 1062323) B1062323
theorem B708235 : Blo 706319 708235 := bstep (se 1 (by rfl) ⟨531176, by rfl⟩ : syracuseStep 708235 = 1062353) B1062353
theorem B708247 : Blo 706319 708247 := bstep (se 1 (by rfl) ⟨531185, by rfl⟩ : syracuseStep 708247 = 1062371) B1062371
theorem B708267 : Blo 706319 708267 := bstep (se 1 (by rfl) ⟨531200, by rfl⟩ : syracuseStep 708267 = 1062401) B1062401
theorem B708279 : Blo 706319 708279 := bstep (se 1 (by rfl) ⟨531209, by rfl⟩ : syracuseStep 708279 = 1062419) B1062419
theorem B1593035 : Blo 706319 1593035 := bstep (se 1 (by rfl) ⟨1194776, by rfl⟩ : syracuseStep 1593035 = 2389553) B2389553
theorem B708299 : Blo 706319 708299 := bstep (se 1 (by rfl) ⟨531224, by rfl⟩ : syracuseStep 708299 = 1062449) B1062449
theorem B708311 : Blo 706319 708311 := bstep (se 1 (by rfl) ⟨531233, by rfl⟩ : syracuseStep 708311 = 1062467) B1062467
theorem B708331 : Blo 706319 708331 := bstep (se 1 (by rfl) ⟨531248, by rfl⟩ : syracuseStep 708331 = 1062497) B1062497
theorem B708343 : Blo 706319 708343 := bstep (se 1 (by rfl) ⟨531257, by rfl⟩ : syracuseStep 708343 = 1062515) B1062515
theorem B1593089 : Blo 706319 1593089 := bstep (se 2 (by rfl) ⟨597408, by rfl⟩ : syracuseStep 1593089 = 1194817) B1194817
theorem B708363 : Blo 706319 708363 := bstep (se 1 (by rfl) ⟨531272, by rfl⟩ : syracuseStep 708363 = 1062545) B1062545
theorem B708375 : Blo 706319 708375 := bstep (se 1 (by rfl) ⟨531281, by rfl⟩ : syracuseStep 708375 = 1062563) B1062563
theorem B708395 : Blo 706319 708395 := bstep (se 1 (by rfl) ⟨531296, by rfl⟩ : syracuseStep 708395 = 1062593) B1062593
theorem B708407 : Blo 706319 708407 := bstep (se 1 (by rfl) ⟨531305, by rfl⟩ : syracuseStep 708407 = 1062611) B1062611
theorem B708427 : Blo 706319 708427 := bstep (se 1 (by rfl) ⟨531320, by rfl⟩ : syracuseStep 708427 = 1062641) B1062641
theorem B708439 : Blo 706319 708439 := bstep (se 1 (by rfl) ⟨531329, by rfl⟩ : syracuseStep 708439 = 1062659) B1062659
theorem B18665315 : Blo 706319 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B708459 : Blo 706319 708459 := bstep (se 1 (by rfl) ⟨531344, by rfl⟩ : syracuseStep 708459 = 1062689) B1062689
theorem B708471 : Blo 706319 708471 := bstep (se 1 (by rfl) ⟨531353, by rfl⟩ : syracuseStep 708471 = 1062707) B1062707
theorem B708491 : Blo 706319 708491 := bstep (se 1 (by rfl) ⟨531368, by rfl⟩ : syracuseStep 708491 = 1062737) B1062737
theorem B1789847 : Blo 706319 1789847 := bstep (se 1 (by rfl) ⟨1342385, by rfl⟩ : syracuseStep 1789847 = 2684771) B2684771
theorem B708503 : Blo 706319 708503 := bstep (se 1 (by rfl) ⟨531377, by rfl⟩ : syracuseStep 708503 = 1062755) B1062755
theorem B708523 : Blo 706319 708523 := bstep (se 1 (by rfl) ⟨531392, by rfl⟩ : syracuseStep 708523 = 1062785) B1062785
theorem B708535 : Blo 706319 708535 := bstep (se 1 (by rfl) ⟨531401, by rfl⟩ : syracuseStep 708535 = 1062803) B1062803
theorem B708555 : Blo 706319 708555 := bstep (se 1 (by rfl) ⟨531416, by rfl⟩ : syracuseStep 708555 = 1062833) B1062833
theorem B708567 : Blo 706319 708567 := bstep (se 1 (by rfl) ⟨531425, by rfl⟩ : syracuseStep 708567 = 1062851) B1062851
theorem B1593305 : Blo 706319 1593305 := bstep (se 2 (by rfl) ⟨597489, by rfl⟩ : syracuseStep 1593305 = 1194979) B1194979
theorem B708587 : Blo 706319 708587 := bstep (se 1 (by rfl) ⟨531440, by rfl⟩ : syracuseStep 708587 = 1062881) B1062881
theorem B708599 : Blo 706319 708599 := bstep (se 1 (by rfl) ⟨531449, by rfl⟩ : syracuseStep 708599 = 1062899) B1062899
theorem B708619 : Blo 706319 708619 := bstep (se 1 (by rfl) ⟨531464, by rfl⟩ : syracuseStep 708619 = 1062929) B1062929
theorem B708631 : Blo 706319 708631 := bstep (se 1 (by rfl) ⟨531473, by rfl⟩ : syracuseStep 708631 = 1062947) B1062947
theorem B708651 : Blo 706319 708651 := bstep (se 1 (by rfl) ⟨531488, by rfl⟩ : syracuseStep 708651 = 1062977) B1062977
theorem B1593395 : Blo 706319 1593395 := bstep (se 1 (by rfl) ⟨1195046, by rfl⟩ : syracuseStep 1593395 = 2390093) B2390093
theorem B708663 : Blo 706319 708663 := bstep (se 1 (by rfl) ⟨531497, by rfl⟩ : syracuseStep 708663 = 1062995) B1062995
theorem B708683 : Blo 706319 708683 := bstep (se 1 (by rfl) ⟨531512, by rfl⟩ : syracuseStep 708683 = 1063025) B1063025
theorem B1593431 : Blo 706319 1593431 := bstep (se 1 (by rfl) ⟨1195073, by rfl⟩ : syracuseStep 1593431 = 2390147) B2390147
theorem B708695 : Blo 706319 708695 := bstep (se 1 (by rfl) ⟨531521, by rfl⟩ : syracuseStep 708695 = 1063043) B1063043
theorem B2019421 : Blo 706319 2019421 := bstep (se 3 (by rfl) ⟨378641, by rfl⟩ : syracuseStep 2019421 = 757283) B757283
theorem B708715 : Blo 706319 708715 := bstep (se 1 (by rfl) ⟨531536, by rfl⟩ : syracuseStep 708715 = 1063073) B1063073
theorem B708727 : Blo 706319 708727 := bstep (se 1 (by rfl) ⟨531545, by rfl⟩ : syracuseStep 708727 = 1063091) B1063091
theorem B708747 : Blo 706319 708747 := bstep (se 1 (by rfl) ⟨531560, by rfl⟩ : syracuseStep 708747 = 1063121) B1063121
theorem B708759 : Blo 706319 708759 := bstep (se 1 (by rfl) ⟨531569, by rfl⟩ : syracuseStep 708759 = 1063139) B1063139
theorem B708779 : Blo 706319 708779 := bstep (se 1 (by rfl) ⟨531584, by rfl⟩ : syracuseStep 708779 = 1063169) B1063169
theorem B708791 : Blo 706319 708791 := bstep (se 1 (by rfl) ⟨531593, by rfl⟩ : syracuseStep 708791 = 1063187) B1063187
theorem B708811 : Blo 706319 708811 := bstep (se 1 (by rfl) ⟨531608, by rfl⟩ : syracuseStep 708811 = 1063217) B1063217
theorem B708823 : Blo 706319 708823 := bstep (se 1 (by rfl) ⟨531617, by rfl⟩ : syracuseStep 708823 = 1063235) B1063235
theorem B708843 : Blo 706319 708843 := bstep (se 1 (by rfl) ⟨531632, by rfl⟩ : syracuseStep 708843 = 1063265) B1063265
theorem B708855 : Blo 706319 708855 := bstep (se 1 (by rfl) ⟨531641, by rfl⟩ : syracuseStep 708855 = 1063283) B1063283
theorem B1593611 : Blo 706319 1593611 := bstep (se 1 (by rfl) ⟨1195208, by rfl⟩ : syracuseStep 1593611 = 2390417) B2390417
theorem B708875 : Blo 706319 708875 := bstep (se 1 (by rfl) ⟨531656, by rfl⟩ : syracuseStep 708875 = 1063313) B1063313
theorem B3395857 : Blo 706319 3395857 := bstep (se 2 (by rfl) ⟨1273446, by rfl⟩ : syracuseStep 3395857 = 2546893) B2546893
theorem B708887 : Blo 706319 708887 := bstep (se 1 (by rfl) ⟨531665, by rfl⟩ : syracuseStep 708887 = 1063331) B1063331
theorem B708907 : Blo 706319 708907 := bstep (se 1 (by rfl) ⟨531680, by rfl⟩ : syracuseStep 708907 = 1063361) B1063361
theorem B708919 : Blo 706319 708919 := bstep (se 1 (by rfl) ⟨531689, by rfl⟩ : syracuseStep 708919 = 1063379) B1063379
theorem B1593665 : Blo 706319 1593665 := bstep (se 2 (by rfl) ⟨597624, by rfl⟩ : syracuseStep 1593665 = 1195249) B1195249
theorem B2019649 : Blo 706319 2019649 := bstep (se 2 (by rfl) ⟨757368, by rfl⟩ : syracuseStep 2019649 = 1514737) B1514737
theorem B708939 : Blo 706319 708939 := bstep (se 1 (by rfl) ⟨531704, by rfl⟩ : syracuseStep 708939 = 1063409) B1063409
theorem B708951 : Blo 706319 708951 := bstep (se 1 (by rfl) ⟨531713, by rfl⟩ : syracuseStep 708951 = 1063427) B1063427
theorem B3395933 : Blo 706319 3395933 := bstep (se 3 (by rfl) ⟨636737, by rfl⟩ : syracuseStep 3395933 = 1273475) B1273475
theorem B4084069 : Blo 706319 4084069 := bstep (se 4 (by rfl) ⟨382881, by rfl⟩ : syracuseStep 4084069 = 765763) B765763
theorem B3887461 : Blo 706319 3887461 := bstep (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) B728899
theorem B708971 : Blo 706319 708971 := bstep (se 1 (by rfl) ⟨531728, by rfl⟩ : syracuseStep 708971 = 1063457) B1063457
theorem B708983 : Blo 706319 708983 := bstep (se 1 (by rfl) ⟨531737, by rfl⟩ : syracuseStep 708983 = 1063475) B1063475
theorem B709003 : Blo 706319 709003 := bstep (se 1 (by rfl) ⟨531752, by rfl⟩ : syracuseStep 709003 = 1063505) B1063505
theorem B709015 : Blo 706319 709015 := bstep (se 1 (by rfl) ⟨531761, by rfl⟩ : syracuseStep 709015 = 1063523) B1063523
theorem B709035 : Blo 706319 709035 := bstep (se 1 (by rfl) ⟨531776, by rfl⟩ : syracuseStep 709035 = 1063553) B1063553
theorem B709047 : Blo 706319 709047 := bstep (se 1 (by rfl) ⟨531785, by rfl⟩ : syracuseStep 709047 = 1063571) B1063571
theorem B709067 : Blo 706319 709067 := bstep (se 1 (by rfl) ⟨531800, by rfl⟩ : syracuseStep 709067 = 1063601) B1063601
theorem B709079 : Blo 706319 709079 := bstep (se 1 (by rfl) ⟨531809, by rfl⟩ : syracuseStep 709079 = 1063619) B1063619
theorem B709099 : Blo 706319 709099 := bstep (se 1 (by rfl) ⟨531824, by rfl⟩ : syracuseStep 709099 = 1063649) B1063649
theorem B709111 : Blo 706319 709111 := bstep (se 1 (by rfl) ⟨531833, by rfl⟩ : syracuseStep 709111 = 1063667) B1063667
theorem B709131 : Blo 706319 709131 := bstep (se 1 (by rfl) ⟨531848, by rfl⟩ : syracuseStep 709131 = 1063697) B1063697
theorem B709143 : Blo 706319 709143 := bstep (se 1 (by rfl) ⟨531857, by rfl⟩ : syracuseStep 709143 = 1063715) B1063715
theorem B1593881 : Blo 706319 1593881 := bstep (se 2 (by rfl) ⟨597705, by rfl⟩ : syracuseStep 1593881 = 1195411) B1195411
theorem B709163 : Blo 706319 709163 := bstep (se 1 (by rfl) ⟨531872, by rfl⟩ : syracuseStep 709163 = 1063745) B1063745
theorem B709175 : Blo 706319 709175 := bstep (se 1 (by rfl) ⟨531881, by rfl⟩ : syracuseStep 709175 = 1063763) B1063763
theorem B3822155 : Blo 706319 3822155 := bstep (se 1 (by rfl) ⟨2866616, by rfl⟩ : syracuseStep 3822155 = 5733233) B5733233
theorem B709195 : Blo 706319 709195 := bstep (se 1 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 709195 = 1063793) B1063793
theorem B709207 : Blo 706319 709207 := bstep (se 1 (by rfl) ⟨531905, by rfl⟩ : syracuseStep 709207 = 1063811) B1063811
theorem B709227 : Blo 706319 709227 := bstep (se 1 (by rfl) ⟨531920, by rfl⟩ : syracuseStep 709227 = 1063841) B1063841
theorem B1593971 : Blo 706319 1593971 := bstep (se 1 (by rfl) ⟨1195478, by rfl⟩ : syracuseStep 1593971 = 2390957) B2390957
theorem B709239 : Blo 706319 709239 := bstep (se 1 (by rfl) ⟨531929, by rfl⟩ : syracuseStep 709239 = 1063859) B1063859
theorem B3592835 : Blo 706319 3592835 := bstep (se 1 (by rfl) ⟨2694626, by rfl⟩ : syracuseStep 3592835 = 5389253) B5389253
theorem B709259 : Blo 706319 709259 := bstep (se 1 (by rfl) ⟨531944, by rfl⟩ : syracuseStep 709259 = 1063889) B1063889
theorem B1594007 : Blo 706319 1594007 := bstep (se 1 (by rfl) ⟨1195505, by rfl⟩ : syracuseStep 1594007 = 2391011) B2391011
theorem B709271 : Blo 706319 709271 := bstep (se 1 (by rfl) ⟨531953, by rfl⟩ : syracuseStep 709271 = 1063907) B1063907
theorem B2019991 : Blo 706319 2019991 := bstep (se 1 (by rfl) ⟨1514993, by rfl⟩ : syracuseStep 2019991 = 3029987) B3029987
theorem B709291 : Blo 706319 709291 := bstep (se 1 (by rfl) ⟨531968, by rfl⟩ : syracuseStep 709291 = 1063937) B1063937
theorem B709303 : Blo 706319 709303 := bstep (se 1 (by rfl) ⟨531977, by rfl⟩ : syracuseStep 709303 = 1063955) B1063955
theorem B1790657 : Blo 706319 1790657 := bstep (se 2 (by rfl) ⟨671496, by rfl⟩ : syracuseStep 1790657 = 1342993) B1342993
theorem B1364683 : Blo 706319 1364683 := bstep (se 1 (by rfl) ⟨1023512, by rfl⟩ : syracuseStep 1364683 = 2047025) B2047025
theorem B709323 : Blo 706319 709323 := bstep (se 1 (by rfl) ⟨531992, by rfl⟩ : syracuseStep 709323 = 1063985) B1063985
theorem B709335 : Blo 706319 709335 := bstep (se 1 (by rfl) ⟨532001, by rfl⟩ : syracuseStep 709335 = 1064003) B1064003
theorem B709355 : Blo 706319 709355 := bstep (se 1 (by rfl) ⟨532016, by rfl⟩ : syracuseStep 709355 = 1064033) B1064033
theorem B709367 : Blo 706319 709367 := bstep (se 1 (by rfl) ⟨532025, by rfl⟩ : syracuseStep 709367 = 1064051) B1064051
theorem B709387 : Blo 706319 709387 := bstep (se 1 (by rfl) ⟨532040, by rfl⟩ : syracuseStep 709387 = 1064081) B1064081
theorem B709399 : Blo 706319 709399 := bstep (se 1 (by rfl) ⟨532049, by rfl⟩ : syracuseStep 709399 = 1064099) B1064099
theorem B709419 : Blo 706319 709419 := bstep (se 1 (by rfl) ⟨532064, by rfl⟩ : syracuseStep 709419 = 1064129) B1064129
theorem B709431 : Blo 706319 709431 := bstep (se 1 (by rfl) ⟨532073, by rfl⟩ : syracuseStep 709431 = 1064147) B1064147
theorem B1594187 : Blo 706319 1594187 := bstep (se 1 (by rfl) ⟨1195640, by rfl⟩ : syracuseStep 1594187 = 2391281) B2391281
theorem B709451 : Blo 706319 709451 := bstep (se 1 (by rfl) ⟨532088, by rfl⟩ : syracuseStep 709451 = 1064177) B1064177
theorem B709463 : Blo 706319 709463 := bstep (se 1 (by rfl) ⟨532097, by rfl⟩ : syracuseStep 709463 = 1064195) B1064195
theorem B709483 : Blo 706319 709483 := bstep (se 1 (by rfl) ⟨532112, by rfl⟩ : syracuseStep 709483 = 1064225) B1064225
theorem B709495 : Blo 706319 709495 := bstep (se 1 (by rfl) ⟨532121, by rfl⟩ : syracuseStep 709495 = 1064243) B1064243
theorem B1594241 : Blo 706319 1594241 := bstep (se 2 (by rfl) ⟨597840, by rfl⟩ : syracuseStep 1594241 = 1195681) B1195681
theorem B709515 : Blo 706319 709515 := bstep (se 1 (by rfl) ⟨532136, by rfl⟩ : syracuseStep 709515 = 1064273) B1064273
theorem B709527 : Blo 706319 709527 := bstep (se 1 (by rfl) ⟨532145, by rfl⟩ : syracuseStep 709527 = 1064291) B1064291
theorem B709547 : Blo 706319 709547 := bstep (se 1 (by rfl) ⟨532160, by rfl⟩ : syracuseStep 709547 = 1064321) B1064321
theorem B709559 : Blo 706319 709559 := bstep (se 1 (by rfl) ⟨532169, by rfl⟩ : syracuseStep 709559 = 1064339) B1064339
theorem B709579 : Blo 706319 709579 := bstep (se 1 (by rfl) ⟨532184, by rfl⟩ : syracuseStep 709579 = 1064369) B1064369
theorem B709591 : Blo 706319 709591 := bstep (se 1 (by rfl) ⟨532193, by rfl⟩ : syracuseStep 709591 = 1064387) B1064387
theorem B709611 : Blo 706319 709611 := bstep (se 1 (by rfl) ⟨532208, by rfl⟩ : syracuseStep 709611 = 1064417) B1064417
theorem B709623 : Blo 706319 709623 := bstep (se 1 (by rfl) ⟨532217, by rfl⟩ : syracuseStep 709623 = 1064435) B1064435
theorem B709643 : Blo 706319 709643 := bstep (se 1 (by rfl) ⟨532232, by rfl⟩ : syracuseStep 709643 = 1064465) B1064465
theorem B709655 : Blo 706319 709655 := bstep (se 1 (by rfl) ⟨532241, by rfl⟩ : syracuseStep 709655 = 1064483) B1064483
theorem B709675 : Blo 706319 709675 := bstep (se 1 (by rfl) ⟨532256, by rfl⟩ : syracuseStep 709675 = 1064513) B1064513
theorem B709687 : Blo 706319 709687 := bstep (se 1 (by rfl) ⟨532265, by rfl⟩ : syracuseStep 709687 = 1064531) B1064531
theorem B709707 : Blo 706319 709707 := bstep (se 1 (by rfl) ⟨532280, by rfl⟩ : syracuseStep 709707 = 1064561) B1064561
theorem B709719 : Blo 706319 709719 := bstep (se 1 (by rfl) ⟨532289, by rfl⟩ : syracuseStep 709719 = 1064579) B1064579
theorem B1594457 : Blo 706319 1594457 := bstep (se 2 (by rfl) ⟨597921, by rfl⟩ : syracuseStep 1594457 = 1195843) B1195843
theorem B709739 : Blo 706319 709739 := bstep (se 1 (by rfl) ⟨532304, by rfl⟩ : syracuseStep 709739 = 1064609) B1064609
theorem B709751 : Blo 706319 709751 := bstep (se 1 (by rfl) ⟨532313, by rfl⟩ : syracuseStep 709751 = 1064627) B1064627
theorem B709771 : Blo 706319 709771 := bstep (se 1 (by rfl) ⟨532328, by rfl⟩ : syracuseStep 709771 = 1064657) B1064657
theorem B709783 : Blo 706319 709783 := bstep (se 1 (by rfl) ⟨532337, by rfl⟩ : syracuseStep 709783 = 1064675) B1064675
theorem B709803 : Blo 706319 709803 := bstep (se 1 (by rfl) ⟨532352, by rfl⟩ : syracuseStep 709803 = 1064705) B1064705
theorem B1594547 : Blo 706319 1594547 := bstep (se 1 (by rfl) ⟨1195910, by rfl⟩ : syracuseStep 1594547 = 2391821) B2391821
theorem B709815 : Blo 706319 709815 := bstep (se 1 (by rfl) ⟨532361, by rfl⟩ : syracuseStep 709815 = 1064723) B1064723
theorem B2872523 : Blo 706319 2872523 := bstep (se 1 (by rfl) ⟨2154392, by rfl⟩ : syracuseStep 2872523 = 4308785) B4308785
theorem B709835 : Blo 706319 709835 := bstep (se 1 (by rfl) ⟨532376, by rfl⟩ : syracuseStep 709835 = 1064753) B1064753
theorem B1594583 : Blo 706319 1594583 := bstep (se 1 (by rfl) ⟨1195937, by rfl⟩ : syracuseStep 1594583 = 2391875) B2391875
theorem B709847 : Blo 706319 709847 := bstep (se 1 (by rfl) ⟨532385, by rfl⟩ : syracuseStep 709847 = 1064771) B1064771
theorem B1791193 : Blo 706319 1791193 := bstep (se 2 (by rfl) ⟨671697, by rfl⟩ : syracuseStep 1791193 = 1343395) B1343395
theorem B709867 : Blo 706319 709867 := bstep (se 1 (by rfl) ⟨532400, by rfl⟩ : syracuseStep 709867 = 1064801) B1064801
theorem B709879 : Blo 706319 709879 := bstep (se 1 (by rfl) ⟨532409, by rfl⟩ : syracuseStep 709879 = 1064819) B1064819
theorem B709899 : Blo 706319 709899 := bstep (se 1 (by rfl) ⟨532424, by rfl⟩ : syracuseStep 709899 = 1064849) B1064849
theorem B709911 : Blo 706319 709911 := bstep (se 1 (by rfl) ⟨532433, by rfl⟩ : syracuseStep 709911 = 1064867) B1064867
theorem B709931 : Blo 706319 709931 := bstep (se 1 (by rfl) ⟨532448, by rfl⟩ : syracuseStep 709931 = 1064897) B1064897
theorem B709943 : Blo 706319 709943 := bstep (se 1 (by rfl) ⟨532457, by rfl⟩ : syracuseStep 709943 = 1064915) B1064915
theorem B709963 : Blo 706319 709963 := bstep (se 1 (by rfl) ⟨532472, by rfl⟩ : syracuseStep 709963 = 1064945) B1064945
theorem B709975 : Blo 706319 709975 := bstep (se 1 (by rfl) ⟨532481, by rfl⟩ : syracuseStep 709975 = 1064963) B1064963
theorem B2020697 : Blo 706319 2020697 := bstep (se 2 (by rfl) ⟨757761, by rfl⟩ : syracuseStep 2020697 = 1515523) B1515523
theorem B709995 : Blo 706319 709995 := bstep (se 1 (by rfl) ⟨532496, by rfl⟩ : syracuseStep 709995 = 1064993) B1064993
theorem B710007 : Blo 706319 710007 := bstep (se 1 (by rfl) ⟨532505, by rfl⟩ : syracuseStep 710007 = 1065011) B1065011
theorem B1594763 : Blo 706319 1594763 := bstep (se 1 (by rfl) ⟨1196072, by rfl⟩ : syracuseStep 1594763 = 2392145) B2392145
theorem B710027 : Blo 706319 710027 := bstep (se 1 (by rfl) ⟨532520, by rfl⟩ : syracuseStep 710027 = 1065041) B1065041
theorem B710039 : Blo 706319 710039 := bstep (se 1 (by rfl) ⟨532529, by rfl⟩ : syracuseStep 710039 = 1065059) B1065059
theorem B710059 : Blo 706319 710059 := bstep (se 1 (by rfl) ⟨532544, by rfl⟩ : syracuseStep 710059 = 1065089) B1065089
theorem B710071 : Blo 706319 710071 := bstep (se 1 (by rfl) ⟨532553, by rfl⟩ : syracuseStep 710071 = 1065107) B1065107
theorem B1594817 : Blo 706319 1594817 := bstep (se 2 (by rfl) ⟨598056, by rfl⟩ : syracuseStep 1594817 = 1196113) B1196113
theorem B710091 : Blo 706319 710091 := bstep (se 1 (by rfl) ⟨532568, by rfl⟩ : syracuseStep 710091 = 1065137) B1065137
theorem B710103 : Blo 706319 710103 := bstep (se 1 (by rfl) ⟨532577, by rfl⟩ : syracuseStep 710103 = 1065155) B1065155
theorem B710123 : Blo 706319 710123 := bstep (se 1 (by rfl) ⟨532592, by rfl⟩ : syracuseStep 710123 = 1065185) B1065185
theorem B710135 : Blo 706319 710135 := bstep (se 1 (by rfl) ⟨532601, by rfl⟩ : syracuseStep 710135 = 1065203) B1065203
theorem B710155 : Blo 706319 710155 := bstep (se 1 (by rfl) ⟨532616, by rfl⟩ : syracuseStep 710155 = 1065233) B1065233
theorem B710167 : Blo 706319 710167 := bstep (se 1 (by rfl) ⟨532625, by rfl⟩ : syracuseStep 710167 = 1065251) B1065251
theorem B710187 : Blo 706319 710187 := bstep (se 1 (by rfl) ⟨532640, by rfl⟩ : syracuseStep 710187 = 1065281) B1065281
theorem B710199 : Blo 706319 710199 := bstep (se 1 (by rfl) ⟨532649, by rfl⟩ : syracuseStep 710199 = 1065299) B1065299
theorem B710219 : Blo 706319 710219 := bstep (se 1 (by rfl) ⟨532664, by rfl⟩ : syracuseStep 710219 = 1065329) B1065329
theorem B710231 : Blo 706319 710231 := bstep (se 1 (by rfl) ⟨532673, by rfl⟩ : syracuseStep 710231 = 1065347) B1065347
theorem B710251 : Blo 706319 710251 := bstep (se 1 (by rfl) ⟨532688, by rfl⟩ : syracuseStep 710251 = 1065377) B1065377
theorem B710263 : Blo 706319 710263 := bstep (se 1 (by rfl) ⟨532697, by rfl⟩ : syracuseStep 710263 = 1065395) B1065395
theorem B3626627 : Blo 706319 3626627 := bstep (se 1 (by rfl) ⟨2719970, by rfl⟩ : syracuseStep 3626627 = 5439941) B5439941
theorem B710283 : Blo 706319 710283 := bstep (se 1 (by rfl) ⟨532712, by rfl⟩ : syracuseStep 710283 = 1065425) B1065425
theorem B710295 : Blo 706319 710295 := bstep (se 1 (by rfl) ⟨532721, by rfl⟩ : syracuseStep 710295 = 1065443) B1065443
theorem B1595033 : Blo 706319 1595033 := bstep (se 2 (by rfl) ⟨598137, by rfl⟩ : syracuseStep 1595033 = 1196275) B1196275
theorem B710315 : Blo 706319 710315 := bstep (se 1 (by rfl) ⟨532736, by rfl⟩ : syracuseStep 710315 = 1065473) B1065473
theorem B1595123 : Blo 706319 1595123 := bstep (se 1 (by rfl) ⟨1196342, by rfl⟩ : syracuseStep 1595123 = 2392685) B2392685
theorem B1595159 : Blo 706319 1595159 := bstep (se 1 (by rfl) ⟨1196369, by rfl⟩ : syracuseStep 1595159 = 2392739) B2392739
theorem B4085635 : Blo 706319 4085635 := bstep (se 1 (by rfl) ⟨3064226, by rfl⟩ : syracuseStep 4085635 = 6128453) B6128453
theorem B1595339 : Blo 706319 1595339 := bstep (se 1 (by rfl) ⟨1196504, by rfl⟩ : syracuseStep 1595339 = 2393009) B2393009
theorem B1595393 : Blo 706319 1595393 := bstep (se 2 (by rfl) ⟨598272, by rfl⟩ : syracuseStep 1595393 = 1196545) B1196545
theorem B1366067 : Blo 706319 1366067 := bstep (se 1 (by rfl) ⟨1024550, by rfl⟩ : syracuseStep 1366067 = 2049101) B2049101
theorem B1595609 : Blo 706319 1595609 := bstep (se 2 (by rfl) ⟨598353, by rfl⟩ : syracuseStep 1595609 = 1196707) B1196707
theorem B1792307 : Blo 706319 1792307 := bstep (se 1 (by rfl) ⟨1344230, by rfl⟩ : syracuseStep 1792307 = 2688461) B2688461
theorem B1595699 : Blo 706319 1595699 := bstep (se 1 (by rfl) ⟨1196774, by rfl⟩ : syracuseStep 1595699 = 2393549) B2393549
theorem B1595735 : Blo 706319 1595735 := bstep (se 1 (by rfl) ⟨1196801, by rfl⟩ : syracuseStep 1595735 = 2393603) B2393603
theorem B1595915 : Blo 706319 1595915 := bstep (se 1 (by rfl) ⟨1196936, by rfl⟩ : syracuseStep 1595915 = 2393873) B2393873
theorem B1595969 : Blo 706319 1595969 := bstep (se 2 (by rfl) ⟨598488, by rfl⟩ : syracuseStep 1595969 = 1196977) B1196977
theorem B1792601 : Blo 706319 1792601 := bstep (se 2 (by rfl) ⟨672225, by rfl⟩ : syracuseStep 1792601 = 1344451) B1344451
theorem B3824279 : Blo 706319 3824279 := bstep (se 1 (by rfl) ⟨2868209, by rfl⟩ : syracuseStep 3824279 = 5736419) B5736419
theorem B1596185 : Blo 706319 1596185 := bstep (se 2 (by rfl) ⟨598569, by rfl⟩ : syracuseStep 1596185 = 1197139) B1197139
theorem B1596275 : Blo 706319 1596275 := bstep (se 1 (by rfl) ⟨1197206, by rfl⟩ : syracuseStep 1596275 = 2394413) B2394413
theorem B1596311 : Blo 706319 1596311 := bstep (se 1 (by rfl) ⟨1197233, by rfl⟩ : syracuseStep 1596311 = 2394467) B2394467
theorem B1137559 : Blo 706319 1137559 := bstep (se 1 (by rfl) ⟨853169, by rfl⟩ : syracuseStep 1137559 = 1706339) B1706339
theorem B2022337 : Blo 706319 2022337 := bstep (se 2 (by rfl) ⟨758376, by rfl⟩ : syracuseStep 2022337 = 1516753) B1516753
theorem B3398701 : Blo 706319 3398701 := bstep (se 3 (by rfl) ⟨637256, by rfl⟩ : syracuseStep 3398701 = 1274513) B1274513
theorem B1596491 : Blo 706319 1596491 := bstep (se 1 (by rfl) ⟨1197368, by rfl⟩ : syracuseStep 1596491 = 2394737) B2394737
theorem B1006681 : Blo 706319 1006681 := bstep (se 2 (by rfl) ⟨377505, by rfl⟩ : syracuseStep 1006681 = 755011) B755011
theorem B1596545 : Blo 706319 1596545 := bstep (se 2 (by rfl) ⟨598704, by rfl⟩ : syracuseStep 1596545 = 1197409) B1197409
theorem B6053069 : Blo 706319 6053069 := bstep (se 3 (by rfl) ⟨1134950, by rfl⟩ : syracuseStep 6053069 = 2269901) B2269901
theorem B5364953 : Blo 706319 5364953 := bstep (se 2 (by rfl) ⟨2011857, by rfl⟩ : syracuseStep 5364953 = 4023715) B4023715
theorem B1596761 : Blo 706319 1596761 := bstep (se 2 (by rfl) ⟨598785, by rfl⟩ : syracuseStep 1596761 = 1197571) B1197571
theorem B2907571 : Blo 706319 2907571 := bstep (se 1 (by rfl) ⟨2180678, by rfl⟩ : syracuseStep 2907571 = 4361357) B4361357
theorem B1596851 : Blo 706319 1596851 := bstep (se 1 (by rfl) ⟨1197638, by rfl⟩ : syracuseStep 1596851 = 2395277) B2395277
theorem B1596887 : Blo 706319 1596887 := bstep (se 1 (by rfl) ⟨1197665, by rfl⟩ : syracuseStep 1596887 = 2395331) B2395331
theorem B1597067 : Blo 706319 1597067 := bstep (se 1 (by rfl) ⟨1197800, by rfl⟩ : syracuseStep 1597067 = 2395601) B2395601
theorem B1597121 : Blo 706319 1597121 := bstep (se 2 (by rfl) ⟨598920, by rfl⟩ : syracuseStep 1597121 = 1197841) B1197841
theorem B3235673 : Blo 706319 3235673 := bstep (se 2 (by rfl) ⟨1213377, by rfl⟩ : syracuseStep 3235673 = 2426755) B2426755
theorem B1597337 : Blo 706319 1597337 := bstep (se 2 (by rfl) ⟨599001, by rfl⟩ : syracuseStep 1597337 = 1198003) B1198003
theorem B1597427 : Blo 706319 1597427 := bstep (se 1 (by rfl) ⟨1198070, by rfl⟩ : syracuseStep 1597427 = 2396141) B2396141
theorem B1597463 : Blo 706319 1597463 := bstep (se 1 (by rfl) ⟨1198097, by rfl⟩ : syracuseStep 1597463 = 2396195) B2396195
theorem B2383937 : Blo 706319 2383937 := bstep (se 2 (by rfl) ⟨893976, by rfl⟩ : syracuseStep 2383937 = 1787953) B1787953
theorem B2547787 : Blo 706319 2547787 := bstep (se 1 (by rfl) ⟨1910840, by rfl⟩ : syracuseStep 2547787 = 3821681) B3821681
theorem B1794251 : Blo 706319 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B1597643 : Blo 706319 1597643 := bstep (se 1 (by rfl) ⟨1198232, by rfl⟩ : syracuseStep 1597643 = 2396465) B2396465
theorem B1597697 : Blo 706319 1597697 := bstep (se 2 (by rfl) ⟨599136, by rfl⟩ : syracuseStep 1597697 = 1198273) B1198273
theorem B9101747 : Blo 706319 9101747 := bstep (se 1 (by rfl) ⟨6826310, by rfl⟩ : syracuseStep 9101747 = 13652621) B13652621
theorem B1597913 : Blo 706319 1597913 := bstep (se 2 (by rfl) ⟨599217, by rfl⟩ : syracuseStep 1597913 = 1198435) B1198435
theorem B1008139 : Blo 706319 1008139 := bstep (se 1 (by rfl) ⟨756104, by rfl⟩ : syracuseStep 1008139 = 1512209) B1512209
theorem B1598003 : Blo 706319 1598003 := bstep (se 1 (by rfl) ⟨1198502, by rfl⟩ : syracuseStep 1598003 = 2397005) B2397005
theorem B1598039 : Blo 706319 1598039 := bstep (se 1 (by rfl) ⟨1198529, by rfl⟩ : syracuseStep 1598039 = 2397059) B2397059
theorem B2482781 : Blo 706319 2482781 := bstep (se 3 (by rfl) ⟨465521, by rfl⟩ : syracuseStep 2482781 = 931043) B931043
theorem B2384477 : Blo 706319 2384477 := bstep (se 3 (by rfl) ⟨447089, by rfl⟩ : syracuseStep 2384477 = 894179) B894179
theorem B1598219 : Blo 706319 1598219 := bstep (se 1 (by rfl) ⟨1198664, by rfl⟩ : syracuseStep 1598219 = 2397329) B2397329
theorem B1532737 : Blo 706319 1532737 := bstep (se 2 (by rfl) ⟨574776, by rfl⟩ : syracuseStep 1532737 = 1149553) B1149553
theorem B2548739 : Blo 706319 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B1795223 : Blo 706319 1795223 := bstep (se 1 (by rfl) ⟨1346417, by rfl⟩ : syracuseStep 1795223 = 2692835) B2692835
theorem B3237043 : Blo 706319 3237043 := bstep (se 1 (by rfl) ⟨2427782, by rfl⟩ : syracuseStep 3237043 = 4855565) B4855565
theorem B2876737 : Blo 706319 2876737 := bstep (se 2 (by rfl) ⟨1078776, by rfl⟩ : syracuseStep 2876737 = 2157553) B2157553
theorem B2549171 : Blo 706319 2549171 := bstep (se 1 (by rfl) ⟨1911878, by rfl⟩ : syracuseStep 2549171 = 3823757) B3823757
theorem B2385611 : Blo 706319 2385611 := bstep (se 1 (by rfl) ⟨1789208, by rfl⟩ : syracuseStep 2385611 = 3578417) B3578417
theorem B1009369 : Blo 706319 1009369 := bstep (se 2 (by rfl) ⟨378513, by rfl⟩ : syracuseStep 1009369 = 757027) B757027
theorem B1795891 : Blo 706319 1795891 := bstep (se 1 (by rfl) ⟨1346918, by rfl⟩ : syracuseStep 1795891 = 2693837) B2693837
theorem B1796033 : Blo 706319 1796033 := bstep (se 2 (by rfl) ⟨673512, by rfl⟩ : syracuseStep 1796033 = 1347025) B1347025
theorem B2385881 : Blo 706319 2385881 := bstep (se 2 (by rfl) ⟨894705, by rfl⟩ : syracuseStep 2385881 = 1789411) B1789411
theorem B2877713 : Blo 706319 2877713 := bstep (se 2 (by rfl) ⟨1079142, by rfl⟩ : syracuseStep 2877713 = 2158285) B2158285
theorem B1436033 : Blo 706319 1436033 := bstep (se 2 (by rfl) ⟨538512, by rfl⟩ : syracuseStep 1436033 = 1077025) B1077025
theorem B4549081 : Blo 706319 4549081 := bstep (se 2 (by rfl) ⟨1705905, by rfl⟩ : syracuseStep 4549081 = 3411811) B3411811
theorem B2550295 : Blo 706319 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B5368355 : Blo 706319 5368355 := bstep (se 1 (by rfl) ⟨4026266, by rfl⟩ : syracuseStep 5368355 = 8052533) B8052533
theorem B2386583 : Blo 706319 2386583 := bstep (se 1 (by rfl) ⟨1789937, by rfl⟩ : syracuseStep 2386583 = 3579875) B3579875
theorem B5106563 : Blo 706319 5106563 := bstep (se 1 (by rfl) ⟨3829922, by rfl⟩ : syracuseStep 5106563 = 7659845) B7659845
theorem B1010713 : Blo 706319 1010713 := bstep (se 2 (by rfl) ⟨379017, by rfl⟩ : syracuseStep 1010713 = 758035) B758035
theorem B1010827 : Blo 706319 1010827 := bstep (se 1 (by rfl) ⟨758120, by rfl⟩ : syracuseStep 1010827 = 1516241) B1516241
theorem B2387123 : Blo 706319 2387123 := bstep (se 1 (by rfl) ⟨1790342, by rfl⟩ : syracuseStep 2387123 = 3580685) B3580685
theorem B3402931 : Blo 706319 3402931 := bstep (se 1 (by rfl) ⟨2552198, by rfl⟩ : syracuseStep 3402931 = 5104397) B5104397
theorem B1797299 : Blo 706319 1797299 := bstep (se 1 (by rfl) ⟨1347974, by rfl⟩ : syracuseStep 1797299 = 2695949) B2695949
theorem B1699265 : Blo 706319 1699265 := bstep (se 2 (by rfl) ⟨637224, by rfl⟩ : syracuseStep 1699265 = 1274449) B1274449
theorem B2387393 : Blo 706319 2387393 := bstep (se 2 (by rfl) ⟨895272, by rfl⟩ : syracuseStep 2387393 = 1790545) B1790545
theorem B13102553 : Blo 706319 13102553 := bstep (se 2 (by rfl) ⟨4913457, by rfl⟩ : syracuseStep 13102553 = 9826915) B9826915
theorem B1797835 : Blo 706319 1797835 := bstep (se 1 (by rfl) ⟨1348376, by rfl⟩ : syracuseStep 1797835 = 2696753) B2696753
theorem B6811397 : Blo 706319 6811397 := bstep (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) B1277137
theorem B1797977 : Blo 706319 1797977 := bstep (se 2 (by rfl) ⟨674241, by rfl⟩ : syracuseStep 1797977 = 1348483) B1348483
theorem B2158429 : Blo 706319 2158429 := bstep (se 3 (by rfl) ⟨404705, by rfl⟩ : syracuseStep 2158429 = 809411) B809411
theorem B2682827 : Blo 706319 2682827 := bstep (se 1 (by rfl) ⟨2012120, by rfl⟩ : syracuseStep 2682827 = 4024241) B4024241
theorem B2682841 : Blo 706319 2682841 := bstep (se 2 (by rfl) ⟨1006065, by rfl⟩ : syracuseStep 2682841 = 2012131) B2012131
theorem B2387933 : Blo 706319 2387933 := bstep (se 3 (by rfl) ⟨447737, by rfl⟩ : syracuseStep 2387933 = 895475) B895475
theorem B8056907 : Blo 706319 8056907 := bstep (se 1 (by rfl) ⟨6042680, by rfl⟩ : syracuseStep 8056907 = 12085361) B12085361
theorem B12284621 : Blo 706319 12284621 := bstep (se 3 (by rfl) ⟨2303366, by rfl⟩ : syracuseStep 12284621 = 4606733) B4606733
theorem B717547 : Blo 706319 717547 := bstep (se 1 (by rfl) ⟨538160, by rfl⟩ : syracuseStep 717547 = 1076321) B1076321
theorem B2683799 : Blo 706319 2683799 := bstep (se 1 (by rfl) ⟨2012849, by rfl⟩ : syracuseStep 2683799 = 4025699) B4025699
theorem B1536983 : Blo 706319 1536983 := bstep (se 1 (by rfl) ⟨1152737, by rfl⟩ : syracuseStep 1536983 = 2305475) B2305475
theorem B2389067 : Blo 706319 2389067 := bstep (se 1 (by rfl) ⟨1791800, by rfl⟩ : syracuseStep 2389067 = 3583601) B3583601
theorem B6812747 : Blo 706319 6812747 := bstep (se 1 (by rfl) ⟨5109560, by rfl⟩ : syracuseStep 6812747 = 10219121) B10219121
theorem B6059083 : Blo 706319 6059083 := bstep (se 1 (by rfl) ⟨4544312, by rfl⟩ : syracuseStep 6059083 = 9088625) B9088625
theorem B2553049 : Blo 706319 2553049 := bstep (se 2 (by rfl) ⟨957393, by rfl⟩ : syracuseStep 2553049 = 1914787) B1914787
theorem B5108953 : Blo 706319 5108953 := bstep (se 2 (by rfl) ⟨1915857, by rfl⟩ : syracuseStep 5108953 = 3831715) B3831715
theorem B2389337 : Blo 706319 2389337 := bstep (se 2 (by rfl) ⟨896001, by rfl⟩ : syracuseStep 2389337 = 1792003) B1792003
theorem B6059357 : Blo 706319 6059357 := bstep (se 3 (by rfl) ⟨1136129, by rfl⟩ : syracuseStep 6059357 = 2272259) B2272259
theorem B1537483 : Blo 706319 1537483 := bstep (se 1 (by rfl) ⟨1153112, by rfl⟩ : syracuseStep 1537483 = 2306225) B2306225
theorem B1701427 : Blo 706319 1701427 := bstep (se 1 (by rfl) ⟨1276070, by rfl⟩ : syracuseStep 1701427 = 2552141) B2552141
theorem B1275545 : Blo 706319 1275545 := bstep (se 2 (by rfl) ⟨478329, by rfl⟩ : syracuseStep 1275545 = 956659) B956659
theorem B1341299 : Blo 706319 1341299 := bstep (se 1 (by rfl) ⟨1005974, by rfl⟩ : syracuseStep 1341299 = 2011949) B2011949
theorem B1701811 : Blo 706319 1701811 := bstep (se 1 (by rfl) ⟨1276358, by rfl⟩ : syracuseStep 1701811 = 2552717) B2552717
theorem B718795 : Blo 706319 718795 := bstep (se 1 (by rfl) ⟨539096, by rfl⟩ : syracuseStep 718795 = 1078193) B1078193
theorem B1341451 : Blo 706319 1341451 := bstep (se 1 (by rfl) ⟨1006088, by rfl⟩ : syracuseStep 1341451 = 2012177) B2012177
theorem B2390039 : Blo 706319 2390039 := bstep (se 1 (by rfl) ⟨1792529, by rfl⟩ : syracuseStep 2390039 = 3585059) B3585059
theorem B2685059 : Blo 706319 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B1341785 : Blo 706319 1341785 := bstep (se 2 (by rfl) ⟨503169, by rfl⟩ : syracuseStep 1341785 = 1006339) B1006339
theorem B10877285 : Blo 706319 10877285 := bstep (se 4 (by rfl) ⟨1019745, by rfl⟩ : syracuseStep 10877285 = 2039491) B2039491
theorem B6060419 : Blo 706319 6060419 := bstep (se 1 (by rfl) ⟨4545314, by rfl⟩ : syracuseStep 6060419 = 9090629) B9090629
theorem B1210777 : Blo 706319 1210777 := bstep (se 2 (by rfl) ⟨454041, by rfl⟩ : syracuseStep 1210777 = 908083) B908083
theorem B2390579 : Blo 706319 2390579 := bstep (se 1 (by rfl) ⟨1792934, by rfl⟩ : syracuseStep 2390579 = 3585869) B3585869
theorem B1636951 : Blo 706319 1636951 := bstep (se 1 (by rfl) ⟨1227713, by rfl⟩ : syracuseStep 1636951 = 2455427) B2455427
theorem B2390849 : Blo 706319 2390849 := bstep (se 2 (by rfl) ⟨896568, by rfl⟩ : syracuseStep 2390849 = 1793137) B1793137
theorem B1342423 : Blo 706319 1342423 := bstep (se 1 (by rfl) ⟨1006817, by rfl⟩ : syracuseStep 1342423 = 2013635) B2013635
theorem B1276993 : Blo 706319 1276993 := bstep (se 2 (by rfl) ⟨478872, by rfl⟩ : syracuseStep 1276993 = 957745) B957745
theorem B2391389 : Blo 706319 2391389 := bstep (se 3 (by rfl) ⟨448385, by rfl⟩ : syracuseStep 2391389 = 896771) B896771
theorem B1211927 : Blo 706319 1211927 := bstep (se 1 (by rfl) ⟨908945, by rfl⟩ : syracuseStep 1211927 = 1817891) B1817891
theorem B1277527 : Blo 706319 1277527 := bstep (se 1 (by rfl) ⟨958145, by rfl⟩ : syracuseStep 1277527 = 1916291) B1916291
theorem B5373701 : Blo 706319 5373701 := bstep (se 4 (by rfl) ⟨503784, by rfl⟩ : syracuseStep 5373701 = 1007569) B1007569
theorem B1343243 : Blo 706319 1343243 := bstep (se 1 (by rfl) ⟨1007432, by rfl⟩ : syracuseStep 1343243 = 2014865) B2014865
theorem B1343297 : Blo 706319 1343297 := bstep (se 2 (by rfl) ⟨503736, by rfl⟩ : syracuseStep 1343297 = 1007473) B1007473
theorem B5439449 : Blo 706319 5439449 := bstep (se 2 (by rfl) ⟨2039793, by rfl⟩ : syracuseStep 5439449 = 4079587) B4079587
theorem B1343623 : Blo 706319 1343623 := bstep (se 1 (by rfl) ⟨1007717, by rfl⟩ : syracuseStep 1343623 = 2015435) B2015435
theorem B3408065 : Blo 706319 3408065 := bstep (se 2 (by rfl) ⟨1278024, by rfl⟩ : syracuseStep 3408065 = 2556049) B2556049
theorem B4849901 : Blo 706319 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B3637505 : Blo 706319 3637505 := bstep (se 2 (by rfl) ⟨1364064, by rfl⟩ : syracuseStep 3637505 = 2728129) B2728129
theorem B1704311 : Blo 706319 1704311 := bstep (se 1 (by rfl) ⟨1278233, by rfl⟩ : syracuseStep 1704311 = 2556467) B2556467
theorem B4031005 : Blo 706319 4031005 := bstep (se 3 (by rfl) ⟨755813, by rfl⟩ : syracuseStep 4031005 = 1511627) B1511627
theorem B754319 : Blo 706319 754319 := bstep (se 1 (by rfl) ⟨565739, by rfl⟩ : syracuseStep 754319 = 1131479) B1131479
theorem B1344185 : Blo 706319 1344185 := bstep (se 2 (by rfl) ⟨504069, by rfl⟩ : syracuseStep 1344185 = 1008139) B1008139
theorem B2392847 : Blo 706319 2392847 := bstep (se 1 (by rfl) ⟨1794635, by rfl⟩ : syracuseStep 2392847 = 3589271) B3589271
theorem B852751 : Blo 706319 852751 := bstep (se 1 (by rfl) ⟨639563, by rfl⟩ : syracuseStep 852751 = 1279127) B1279127
theorem B3441629 : Blo 706319 3441629 := bstep (se 3 (by rfl) ⟨645305, by rfl⟩ : syracuseStep 3441629 = 1290611) B1290611
theorem B2393117 : Blo 706319 2393117 := bstep (se 3 (by rfl) ⟨448709, by rfl⟩ : syracuseStep 2393117 = 897419) B897419
theorem B4031531 : Blo 706319 4031531 := bstep (se 1 (by rfl) ⟨3023648, by rfl⟩ : syracuseStep 4031531 = 6047297) B6047297
theorem B853135 : Blo 706319 853135 := bstep (se 1 (by rfl) ⟨639851, by rfl⟩ : syracuseStep 853135 = 1279703) B1279703
theorem B3835649 : Blo 706319 3835649 := bstep (se 2 (by rfl) ⟨1438368, by rfl⟩ : syracuseStep 3835649 = 2876737) B2876737
theorem B755515 : Blo 706319 755515 := bstep (se 1 (by rfl) ⟨566636, by rfl⟩ : syracuseStep 755515 = 1133273) B1133273
theorem B1345339 : Blo 706319 1345339 := bstep (se 1 (by rfl) ⟨1009004, by rfl⟩ : syracuseStep 1345339 = 2018009) B2018009
theorem B1279891 : Blo 706319 1279891 := bstep (se 1 (by rfl) ⟨959918, by rfl⟩ : syracuseStep 1279891 = 1919837) B1919837
theorem B6817699 : Blo 706319 6817699 := bstep (se 1 (by rfl) ⟨5113274, by rfl⟩ : syracuseStep 6817699 = 10226549) B10226549
theorem B2688977 : Blo 706319 2688977 := bstep (se 2 (by rfl) ⟨1008366, by rfl⟩ : syracuseStep 2688977 = 2016733) B2016733
theorem B6457477 : Blo 706319 6457477 := bstep (se 4 (by rfl) ⟨605388, by rfl⟩ : syracuseStep 6457477 = 1210777) B1210777
theorem B15337673 : Blo 706319 15337673 := bstep (se 2 (by rfl) ⟨5751627, by rfl⟩ : syracuseStep 15337673 = 11503255) B11503255
theorem B11634961 : Blo 706319 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B7276817 : Blo 706319 7276817 := bstep (se 2 (by rfl) ⟨2728806, by rfl⟩ : syracuseStep 7276817 = 5457613) B5457613
theorem B1345825 : Blo 706319 1345825 := bstep (se 2 (by rfl) ⟨504684, by rfl⟩ : syracuseStep 1345825 = 1009369) B1009369
theorem B2689433 : Blo 706319 2689433 := bstep (se 2 (by rfl) ⟨1008537, by rfl⟩ : syracuseStep 2689433 = 2017075) B2017075
theorem B2394521 : Blo 706319 2394521 := bstep (se 2 (by rfl) ⟨897945, by rfl⟩ : syracuseStep 2394521 = 1795891) B1795891
theorem B4032989 : Blo 706319 4032989 := bstep (se 3 (by rfl) ⟨756185, by rfl⟩ : syracuseStep 4032989 = 1512371) B1512371
theorem B1510073 : Blo 706319 1510073 := bstep (se 2 (by rfl) ⟨566277, by rfl⟩ : syracuseStep 1510073 = 1132555) B1132555
theorem B2263955 : Blo 706319 2263955 := bstep (se 1 (by rfl) ⟨1697966, by rfl⟩ : syracuseStep 2263955 = 3395933) B3395933
theorem B2395223 : Blo 706319 2395223 := bstep (se 1 (by rfl) ⟨1796417, by rfl⟩ : syracuseStep 2395223 = 3592835) B3592835
theorem B8621257 : Blo 706319 8621257 := bstep (se 2 (by rfl) ⟨3232971, by rfl⟩ : syracuseStep 8621257 = 6465943) B6465943
theorem B6065441 : Blo 706319 6065441 := bstep (se 2 (by rfl) ⟨2274540, by rfl⟩ : syracuseStep 6065441 = 4549081) B4549081
theorem B2690603 : Blo 706319 2690603 := bstep (se 1 (by rfl) ⟨2017952, by rfl⟩ : syracuseStep 2690603 = 4035905) B4035905
theorem B1347131 : Blo 706319 1347131 := bstep (se 1 (by rfl) ⟨1010348, by rfl⟩ : syracuseStep 1347131 = 2020697) B2020697
theorem B2395709 : Blo 706319 2395709 := bstep (se 3 (by rfl) ⟨449195, by rfl⟩ : syracuseStep 2395709 = 898391) B898391
theorem B6819545 : Blo 706319 6819545 := bstep (se 2 (by rfl) ⟨2557329, by rfl⟩ : syracuseStep 6819545 = 5114659) B5114659
theorem B1511183 : Blo 706319 1511183 := bstep (se 1 (by rfl) ⟨1133387, by rfl⟩ : syracuseStep 1511183 = 2266775) B2266775
theorem B1347617 : Blo 706319 1347617 := bstep (se 2 (by rfl) ⟨505356, by rfl⟩ : syracuseStep 1347617 = 1010713) B1010713
theorem B1347769 : Blo 706319 1347769 := bstep (se 2 (by rfl) ⟨505413, by rfl⟩ : syracuseStep 1347769 = 1010827) B1010827
theorem B1511713 : Blo 706319 1511713 := bstep (se 2 (by rfl) ⟨566892, by rfl⟩ : syracuseStep 1511713 = 1133785) B1133785
theorem B3412313 : Blo 706319 3412313 := bstep (se 2 (by rfl) ⟨1279617, by rfl⟩ : syracuseStep 3412313 = 2559235) B2559235
theorem B9671005 : Blo 706319 9671005 := bstep (se 3 (by rfl) ⟨1813313, by rfl⟩ : syracuseStep 9671005 = 3626627) B3626627
theorem B8065655 : Blo 706319 8065655 := bstep (se 1 (by rfl) ⟨6049241, by rfl⟩ : syracuseStep 8065655 = 12098483) B12098483
theorem B7574309 : Blo 706319 7574309 := bstep (se 4 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 7574309 = 1420183) B1420183
theorem B4035379 : Blo 706319 4035379 := bstep (se 1 (by rfl) ⟨3026534, by rfl⟩ : syracuseStep 4035379 = 6053069) B6053069
theorem B3576635 : Blo 706319 3576635 := bstep (se 1 (by rfl) ⟨2682476, by rfl⟩ : syracuseStep 3576635 = 5364953) B5364953
theorem B2397113 : Blo 706319 2397113 := bstep (se 2 (by rfl) ⟨898917, by rfl⟩ : syracuseStep 2397113 = 1797835) B1797835
theorem B3576797 : Blo 706319 3576797 := bstep (se 3 (by rfl) ⟨670649, by rfl⟩ : syracuseStep 3576797 = 1341299) B1341299
theorem B3019837 : Blo 706319 3019837 := bstep (se 3 (by rfl) ⟨566219, by rfl⟩ : syracuseStep 3019837 = 1132439) B1132439
theorem B3577121 : Blo 706319 3577121 := bstep (se 2 (by rfl) ⟨1341420, by rfl⟩ : syracuseStep 3577121 = 2682841) B2682841
theorem B6034823 : Blo 706319 6034823 := bstep (se 1 (by rfl) ⟨4526117, by rfl⟩ : syracuseStep 6034823 = 9052235) B9052235
theorem B3020179 : Blo 706319 3020179 := bstep (se 1 (by rfl) ⟨2265134, by rfl⟩ : syracuseStep 3020179 = 4530269) B4530269
theorem B2692561 : Blo 706319 2692561 := bstep (se 2 (by rfl) ⟨1009710, by rfl⟩ : syracuseStep 2692561 = 2019421) B2019421
theorem B4527683 : Blo 706319 4527683 := bstep (se 1 (by rfl) ⟨3395762, by rfl⟩ : syracuseStep 4527683 = 6791525) B6791525
theorem B6067831 : Blo 706319 6067831 := bstep (se 1 (by rfl) ⟨4550873, by rfl⟩ : syracuseStep 6067831 = 9101747) B9101747
theorem B4527809 : Blo 706319 4527809 := bstep (se 2 (by rfl) ⟨1697928, by rfl⟩ : syracuseStep 4527809 = 3395857) B3395857
theorem B2692865 : Blo 706319 2692865 := bstep (se 2 (by rfl) ⟨1009824, by rfl⟩ : syracuseStep 2692865 = 2019649) B2019649
theorem B5445425 : Blo 706319 5445425 := bstep (se 2 (by rfl) ⟨2042034, by rfl⟩ : syracuseStep 5445425 = 4084069) B4084069
theorem B5183281 : Blo 706319 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B19666961 : Blo 706319 19666961 := bstep (se 2 (by rfl) ⟨7375110, by rfl⟩ : syracuseStep 19666961 = 14750221) B14750221
theorem B2693321 : Blo 706319 2693321 := bstep (se 2 (by rfl) ⟨1009995, by rfl⟩ : syracuseStep 2693321 = 2019991) B2019991
theorem B4036837 : Blo 706319 4036837 := bstep (se 4 (by rfl) ⟨378453, by rfl⟩ : syracuseStep 4036837 = 756907) B756907
theorem B3578093 : Blo 706319 3578093 := bstep (se 3 (by rfl) ⟨670892, by rfl⟩ : syracuseStep 3578093 = 1341785) B1341785
theorem B2070785 : Blo 706319 2070785 := bstep (se 2 (by rfl) ⟨776544, by rfl⟩ : syracuseStep 2070785 = 1553089) B1553089
theorem B29006093 : Blo 706319 29006093 := bstep (se 3 (by rfl) ⟨5438642, by rfl⟩ : syracuseStep 29006093 = 10877285) B10877285
theorem B26482997 : Blo 706319 26482997 := bstep (se 5 (by rfl) ⟨1241390, by rfl⟩ : syracuseStep 26482997 = 2482781) B2482781
theorem B956729 : Blo 706319 956729 := bstep (se 2 (by rfl) ⟨358773, by rfl⟩ : syracuseStep 956729 = 717547) B717547
theorem B13605569 : Blo 706319 13605569 := bstep (se 2 (by rfl) ⟨5102088, by rfl⟩ : syracuseStep 13605569 = 10204177) B10204177
theorem B957355 : Blo 706319 957355 := bstep (se 1 (by rfl) ⟨718016, by rfl⟩ : syracuseStep 957355 = 1436033) B1436033
theorem B3578903 : Blo 706319 3578903 := bstep (se 1 (by rfl) ⟨2684177, by rfl⟩ : syracuseStep 3578903 = 5368355) B5368355
theorem B4300121 : Blo 706319 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B2268569 : Blo 706319 2268569 := bstep (se 2 (by rfl) ⟨850713, by rfl⟩ : syracuseStep 2268569 = 1701427) B1701427
theorem B20717207 : Blo 706319 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B5447513 : Blo 706319 5447513 := bstep (se 2 (by rfl) ⟨2042817, by rfl⟩ : syracuseStep 5447513 = 4085635) B4085635
theorem B2269081 : Blo 706319 2269081 := bstep (se 2 (by rfl) ⟨850905, by rfl⟩ : syracuseStep 2269081 = 1701811) B1701811
theorem B958393 : Blo 706319 958393 := bstep (se 2 (by rfl) ⟨359397, by rfl⟩ : syracuseStep 958393 = 718795) B718795
theorem B794767 : Blo 706319 794767 := bstep (se 1 (by rfl) ⟨596075, by rfl⟩ : syracuseStep 794767 = 1192151) B1192151
theorem B4301093 : Blo 706319 4301093 := bstep (se 4 (by rfl) ⟨403227, by rfl⟩ : syracuseStep 4301093 = 806455) B806455
theorem B795271 : Blo 706319 795271 := bstep (se 1 (by rfl) ⟨596453, by rfl⟩ : syracuseStep 795271 = 1192907) B1192907
theorem B1024655 : Blo 706319 1024655 := bstep (se 1 (by rfl) ⟨768491, by rfl⟩ : syracuseStep 1024655 = 1536983) B1536983
theorem B795451 : Blo 706319 795451 := bstep (se 1 (by rfl) ⟨596588, by rfl⟩ : syracuseStep 795451 = 1193177) B1193177
theorem B4039571 : Blo 706319 4039571 := bstep (se 1 (by rfl) ⟨3029678, by rfl⟩ : syracuseStep 4039571 = 6059357) B6059357
theorem B3023801 : Blo 706319 3023801 := bstep (se 2 (by rfl) ⟨1133925, by rfl⟩ : syracuseStep 3023801 = 2267851) B2267851
theorem B4531373 : Blo 706319 4531373 := bstep (se 3 (by rfl) ⟨849632, by rfl⟩ : syracuseStep 4531373 = 1699265) B1699265
theorem B1516745 : Blo 706319 1516745 := bstep (se 2 (by rfl) ⟨568779, by rfl⟩ : syracuseStep 1516745 = 1137559) B1137559
theorem B2696449 : Blo 706319 2696449 := bstep (se 2 (by rfl) ⟨1011168, by rfl⟩ : syracuseStep 2696449 = 2022337) B2022337
theorem B795919 : Blo 706319 795919 := bstep (se 1 (by rfl) ⟨596939, by rfl⟩ : syracuseStep 795919 = 1193879) B1193879
theorem B4531601 : Blo 706319 4531601 := bstep (se 2 (by rfl) ⟨1699350, by rfl⟩ : syracuseStep 4531601 = 3398701) B3398701
theorem B4040279 : Blo 706319 4040279 := bstep (se 1 (by rfl) ⟨3030209, by rfl⟩ : syracuseStep 4040279 = 6060419) B6060419
theorem B14526209 : Blo 706319 14526209 := bstep (se 2 (by rfl) ⟨5447328, by rfl⟩ : syracuseStep 14526209 = 10894657) B10894657
theorem B796423 : Blo 706319 796423 := bstep (se 1 (by rfl) ⟨597317, by rfl⟩ : syracuseStep 796423 = 1194635) B1194635
theorem B3876761 : Blo 706319 3876761 := bstep (se 2 (by rfl) ⟨1453785, by rfl⟩ : syracuseStep 3876761 = 2907571) B2907571
theorem B796603 : Blo 706319 796603 := bstep (se 1 (by rfl) ⟨597452, by rfl⟩ : syracuseStep 796603 = 1194905) B1194905
theorem B3581981 : Blo 706319 3581981 := bstep (se 3 (by rfl) ⟨671621, by rfl⟩ : syracuseStep 3581981 = 1343243) B1343243
theorem B5384393 : Blo 706319 5384393 := bstep (se 2 (by rfl) ⟨2019147, by rfl⟩ : syracuseStep 5384393 = 4038295) B4038295
theorem B797071 : Blo 706319 797071 := bstep (se 1 (by rfl) ⟨597803, by rfl⟩ : syracuseStep 797071 = 1195607) B1195607
theorem B3582467 : Blo 706319 3582467 := bstep (se 1 (by rfl) ⟨2686850, by rfl⟩ : syracuseStep 3582467 = 5373701) B5373701
theorem B895531 : Blo 706319 895531 := bstep (se 1 (by rfl) ⟨671648, by rfl⟩ : syracuseStep 895531 = 1343297) B1343297
theorem B6793793 : Blo 706319 6793793 := bstep (se 2 (by rfl) ⟨2547672, by rfl⟩ : syracuseStep 6793793 = 5095345) B5095345
theorem B1059515 : Blo 706319 1059515 := bstep (se 1 (by rfl) ⟨794636, by rfl⟩ : syracuseStep 1059515 = 1589273) B1589273
theorem B1059575 : Blo 706319 1059575 := bstep (se 1 (by rfl) ⟨794681, by rfl⟩ : syracuseStep 1059575 = 1589363) B1589363
theorem B1059599 : Blo 706319 1059599 := bstep (se 1 (by rfl) ⟨794699, by rfl⟩ : syracuseStep 1059599 = 1589399) B1589399
theorem B1059641 : Blo 706319 1059641 := bstep (se 2 (by rfl) ⟨397365, by rfl⟩ : syracuseStep 1059641 = 794731) B794731
theorem B1059719 : Blo 706319 1059719 := bstep (se 1 (by rfl) ⟨794789, by rfl⟩ : syracuseStep 1059719 = 1589579) B1589579
theorem B797575 : Blo 706319 797575 := bstep (se 1 (by rfl) ⟨598181, by rfl⟩ : syracuseStep 797575 = 1196363) B1196363
theorem B1059755 : Blo 706319 1059755 := bstep (se 1 (by rfl) ⟨794816, by rfl⟩ : syracuseStep 1059755 = 1589633) B1589633
theorem B1059785 : Blo 706319 1059785 := bstep (se 2 (by rfl) ⟨397419, by rfl⟩ : syracuseStep 1059785 = 794839) B794839
theorem B1059899 : Blo 706319 1059899 := bstep (se 1 (by rfl) ⟨794924, by rfl⟩ : syracuseStep 1059899 = 1589849) B1589849
theorem B797755 : Blo 706319 797755 := bstep (se 1 (by rfl) ⟨598316, by rfl⟩ : syracuseStep 797755 = 1196633) B1196633
theorem B1059959 : Blo 706319 1059959 := bstep (se 1 (by rfl) ⟨794969, by rfl⟩ : syracuseStep 1059959 = 1589939) B1589939
theorem B1059983 : Blo 706319 1059983 := bstep (se 1 (by rfl) ⟨794987, by rfl⟩ : syracuseStep 1059983 = 1589975) B1589975
theorem B1060025 : Blo 706319 1060025 := bstep (se 2 (by rfl) ⟨397509, by rfl⟩ : syracuseStep 1060025 = 795019) B795019
theorem B1060103 : Blo 706319 1060103 := bstep (se 1 (by rfl) ⟨795077, by rfl⟩ : syracuseStep 1060103 = 1590155) B1590155
theorem B8629537 : Blo 706319 8629537 := bstep (se 2 (by rfl) ⟨3236076, by rfl⟩ : syracuseStep 8629537 = 6472153) B6472153
theorem B1060139 : Blo 706319 1060139 := bstep (se 1 (by rfl) ⟨795104, by rfl⟩ : syracuseStep 1060139 = 1590209) B1590209
theorem B1060169 : Blo 706319 1060169 := bstep (se 2 (by rfl) ⟨397563, by rfl⟩ : syracuseStep 1060169 = 795127) B795127
theorem B4042169 : Blo 706319 4042169 := bstep (se 2 (by rfl) ⟨1515813, by rfl⟩ : syracuseStep 4042169 = 3031627) B3031627
theorem B1060283 : Blo 706319 1060283 := bstep (se 1 (by rfl) ⟨795212, by rfl⟩ : syracuseStep 1060283 = 1590425) B1590425
theorem B1060343 : Blo 706319 1060343 := bstep (se 1 (by rfl) ⟨795257, by rfl⟩ : syracuseStep 1060343 = 1590515) B1590515
theorem B896503 : Blo 706319 896503 := bstep (se 1 (by rfl) ⟨672377, by rfl⟩ : syracuseStep 896503 = 1344755) B1344755
theorem B1060367 : Blo 706319 1060367 := bstep (se 1 (by rfl) ⟨795275, by rfl⟩ : syracuseStep 1060367 = 1590551) B1590551
theorem B798223 : Blo 706319 798223 := bstep (se 1 (by rfl) ⟨598667, by rfl⟩ : syracuseStep 798223 = 1197335) B1197335
theorem B1060409 : Blo 706319 1060409 := bstep (se 2 (by rfl) ⟨397653, by rfl⟩ : syracuseStep 1060409 = 795307) B795307
theorem B2731639 : Blo 706319 2731639 := bstep (se 1 (by rfl) ⟨2048729, by rfl⟩ : syracuseStep 2731639 = 4097459) B4097459
theorem B2305655 : Blo 706319 2305655 := bstep (se 1 (by rfl) ⟨1729241, by rfl⟩ : syracuseStep 2305655 = 3458483) B3458483
theorem B1060487 : Blo 706319 1060487 := bstep (se 1 (by rfl) ⟨795365, by rfl⟩ : syracuseStep 1060487 = 1590731) B1590731
theorem B1060523 : Blo 706319 1060523 := bstep (se 1 (by rfl) ⟨795392, by rfl⟩ : syracuseStep 1060523 = 1590785) B1590785
theorem B1060553 : Blo 706319 1060553 := bstep (se 2 (by rfl) ⟨397707, by rfl⟩ : syracuseStep 1060553 = 795415) B795415
theorem B2043649 : Blo 706319 2043649 := bstep (se 2 (by rfl) ⟨766368, by rfl⟩ : syracuseStep 2043649 = 1532737) B1532737
theorem B1060667 : Blo 706319 1060667 := bstep (se 1 (by rfl) ⟨795500, by rfl⟩ : syracuseStep 1060667 = 1591001) B1591001
theorem B896827 : Blo 706319 896827 := bstep (se 1 (by rfl) ⟨672620, by rfl⟩ : syracuseStep 896827 = 1345241) B1345241
theorem B1060727 : Blo 706319 1060727 := bstep (se 1 (by rfl) ⟨795545, by rfl⟩ : syracuseStep 1060727 = 1591091) B1591091
theorem B1060751 : Blo 706319 1060751 := bstep (se 1 (by rfl) ⟨795563, by rfl⟩ : syracuseStep 1060751 = 1591127) B1591127
theorem B1060793 : Blo 706319 1060793 := bstep (se 2 (by rfl) ⟨397797, by rfl⟩ : syracuseStep 1060793 = 795595) B795595
theorem B7679947 : Blo 706319 7679947 := bstep (se 1 (by rfl) ⟨5759960, by rfl⟩ : syracuseStep 7679947 = 11519921) B11519921
theorem B1060871 : Blo 706319 1060871 := bstep (se 1 (by rfl) ⟨795653, by rfl⟩ : syracuseStep 1060871 = 1591307) B1591307
theorem B798727 : Blo 706319 798727 := bstep (se 1 (by rfl) ⟨599045, by rfl⟩ : syracuseStep 798727 = 1198091) B1198091
theorem B70660117 : Blo 706319 70660117 := bstep (se 6 (by rfl) ⟨1656096, by rfl⟩ : syracuseStep 70660117 = 3312193) B3312193
theorem B1060907 : Blo 706319 1060907 := bstep (se 1 (by rfl) ⟨795680, by rfl⟩ : syracuseStep 1060907 = 1591361) B1591361
theorem B1060937 : Blo 706319 1060937 := bstep (se 2 (by rfl) ⟨397851, by rfl⟩ : syracuseStep 1060937 = 795703) B795703
theorem B3584087 : Blo 706319 3584087 := bstep (se 1 (by rfl) ⟨2688065, by rfl⟩ : syracuseStep 3584087 = 5376131) B5376131
theorem B1061051 : Blo 706319 1061051 := bstep (se 1 (by rfl) ⟨795788, by rfl⟩ : syracuseStep 1061051 = 1591577) B1591577
theorem B798907 : Blo 706319 798907 := bstep (se 1 (by rfl) ⟨599180, by rfl⟩ : syracuseStep 798907 = 1198361) B1198361
theorem B1061111 : Blo 706319 1061111 := bstep (se 1 (by rfl) ⟨795833, by rfl⟩ : syracuseStep 1061111 = 1591667) B1591667
theorem B1061135 : Blo 706319 1061135 := bstep (se 1 (by rfl) ⟨795851, by rfl⟩ : syracuseStep 1061135 = 1591703) B1591703
theorem B1061177 : Blo 706319 1061177 := bstep (se 2 (by rfl) ⟨397941, by rfl⟩ : syracuseStep 1061177 = 795883) B795883
theorem B1061255 : Blo 706319 1061255 := bstep (se 1 (by rfl) ⟨795941, by rfl⟩ : syracuseStep 1061255 = 1591883) B1591883
theorem B2044295 : Blo 706319 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B2273683 : Blo 706319 2273683 := bstep (se 1 (by rfl) ⟨1705262, by rfl⟩ : syracuseStep 2273683 = 3410525) B3410525
theorem B1061291 : Blo 706319 1061291 := bstep (se 1 (by rfl) ⟨795968, by rfl⟩ : syracuseStep 1061291 = 1591937) B1591937
theorem B1061321 : Blo 706319 1061321 := bstep (se 2 (by rfl) ⟨397995, by rfl⟩ : syracuseStep 1061321 = 795991) B795991
theorem B1061435 : Blo 706319 1061435 := bstep (se 1 (by rfl) ⟨796076, by rfl⟩ : syracuseStep 1061435 = 1592153) B1592153
theorem B3584573 : Blo 706319 3584573 := bstep (se 3 (by rfl) ⟨672107, by rfl⟩ : syracuseStep 3584573 = 1344215) B1344215
theorem B1061495 : Blo 706319 1061495 := bstep (se 1 (by rfl) ⟨796121, by rfl⟩ : syracuseStep 1061495 = 1592243) B1592243
theorem B1192583 : Blo 706319 1192583 := bstep (se 1 (by rfl) ⟨894437, by rfl⟩ : syracuseStep 1192583 = 1788875) B1788875
theorem B1061519 : Blo 706319 1061519 := bstep (se 1 (by rfl) ⟨796139, by rfl⟩ : syracuseStep 1061519 = 1592279) B1592279
theorem B1061561 : Blo 706319 1061561 := bstep (se 2 (by rfl) ⟨398085, by rfl⟩ : syracuseStep 1061561 = 796171) B796171
theorem B1061639 : Blo 706319 1061639 := bstep (se 1 (by rfl) ⟨796229, by rfl⟩ : syracuseStep 1061639 = 1592459) B1592459
theorem B897799 : Blo 706319 897799 := bstep (se 1 (by rfl) ⟨673349, by rfl⟩ : syracuseStep 897799 = 1346699) B1346699
theorem B1061675 : Blo 706319 1061675 := bstep (se 1 (by rfl) ⟨796256, by rfl⟩ : syracuseStep 1061675 = 1592513) B1592513
theorem B1061705 : Blo 706319 1061705 := bstep (se 2 (by rfl) ⟨398139, by rfl⟩ : syracuseStep 1061705 = 796279) B796279
theorem B1061819 : Blo 706319 1061819 := bstep (se 1 (by rfl) ⟨796364, by rfl⟩ : syracuseStep 1061819 = 1592729) B1592729
theorem B4371421 : Blo 706319 4371421 := bstep (se 3 (by rfl) ⟨819641, by rfl⟩ : syracuseStep 4371421 = 1639283) B1639283
theorem B1061879 : Blo 706319 1061879 := bstep (se 1 (by rfl) ⟨796409, by rfl⟩ : syracuseStep 1061879 = 1592819) B1592819
theorem B1061903 : Blo 706319 1061903 := bstep (se 1 (by rfl) ⟨796427, by rfl⟩ : syracuseStep 1061903 = 1592855) B1592855
theorem B1061945 : Blo 706319 1061945 := bstep (se 2 (by rfl) ⟨398229, by rfl⟩ : syracuseStep 1061945 = 796459) B796459
theorem B1062023 : Blo 706319 1062023 := bstep (se 1 (by rfl) ⟨796517, by rfl⟩ : syracuseStep 1062023 = 1593035) B1593035
theorem B1062059 : Blo 706319 1062059 := bstep (se 1 (by rfl) ⟨796544, by rfl⟩ : syracuseStep 1062059 = 1593089) B1593089
theorem B898219 : Blo 706319 898219 := bstep (se 1 (by rfl) ⟨673664, by rfl⟩ : syracuseStep 898219 = 1347329) B1347329
theorem B1062089 : Blo 706319 1062089 := bstep (se 2 (by rfl) ⟨398283, by rfl⟩ : syracuseStep 1062089 = 796567) B796567
theorem B1193231 : Blo 706319 1193231 := bstep (se 1 (by rfl) ⟨894923, by rfl⟩ : syracuseStep 1193231 = 1789847) B1789847
theorem B1062203 : Blo 706319 1062203 := bstep (se 1 (by rfl) ⟨796652, by rfl⟩ : syracuseStep 1062203 = 1593305) B1593305
theorem B1062263 : Blo 706319 1062263 := bstep (se 1 (by rfl) ⟨796697, by rfl⟩ : syracuseStep 1062263 = 1593395) B1593395
theorem B1062287 : Blo 706319 1062287 := bstep (se 1 (by rfl) ⟨796715, by rfl⟩ : syracuseStep 1062287 = 1593431) B1593431
theorem B898447 : Blo 706319 898447 := bstep (se 1 (by rfl) ⟨673835, by rfl⟩ : syracuseStep 898447 = 1347671) B1347671
theorem B1062329 : Blo 706319 1062329 := bstep (se 2 (by rfl) ⟨398373, by rfl⟩ : syracuseStep 1062329 = 796747) B796747
theorem B1062407 : Blo 706319 1062407 := bstep (se 1 (by rfl) ⟨796805, by rfl⟩ : syracuseStep 1062407 = 1593611) B1593611
theorem B2012701 : Blo 706319 2012701 := bstep (se 3 (by rfl) ⟨377381, by rfl⟩ : syracuseStep 2012701 = 754763) B754763
theorem B1062443 : Blo 706319 1062443 := bstep (se 1 (by rfl) ⟨796832, by rfl⟩ : syracuseStep 1062443 = 1593665) B1593665
theorem B1062473 : Blo 706319 1062473 := bstep (se 2 (by rfl) ⟨398427, by rfl⟩ : syracuseStep 1062473 = 796855) B796855
theorem B18134603 : Blo 706319 18134603 := bstep (se 1 (by rfl) ⟨13600952, by rfl⟩ : syracuseStep 18134603 = 27201905) B27201905
theorem B2012759 : Blo 706319 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B1062587 : Blo 706319 1062587 := bstep (se 1 (by rfl) ⟨796940, by rfl⟩ : syracuseStep 1062587 = 1593881) B1593881
theorem B1062647 : Blo 706319 1062647 := bstep (se 1 (by rfl) ⟨796985, by rfl⟩ : syracuseStep 1062647 = 1593971) B1593971
theorem B1062671 : Blo 706319 1062671 := bstep (se 1 (by rfl) ⟨797003, by rfl⟩ : syracuseStep 1062671 = 1594007) B1594007
theorem B1193771 : Blo 706319 1193771 := bstep (se 1 (by rfl) ⟨895328, by rfl⟩ : syracuseStep 1193771 = 1790657) B1790657
theorem B1062713 : Blo 706319 1062713 := bstep (se 2 (by rfl) ⟨398517, by rfl⟩ : syracuseStep 1062713 = 797035) B797035
theorem B1062791 : Blo 706319 1062791 := bstep (se 1 (by rfl) ⟨797093, by rfl⟩ : syracuseStep 1062791 = 1594187) B1594187
theorem B1062827 : Blo 706319 1062827 := bstep (se 1 (by rfl) ⟨797120, by rfl⟩ : syracuseStep 1062827 = 1594241) B1594241
theorem B1062857 : Blo 706319 1062857 := bstep (se 2 (by rfl) ⟨398571, by rfl⟩ : syracuseStep 1062857 = 797143) B797143
theorem B1062971 : Blo 706319 1062971 := bstep (se 1 (by rfl) ⟨797228, by rfl⟩ : syracuseStep 1062971 = 1594457) B1594457
theorem B1063031 : Blo 706319 1063031 := bstep (se 1 (by rfl) ⟨797273, by rfl⟩ : syracuseStep 1063031 = 1594547) B1594547
theorem B1915015 : Blo 706319 1915015 := bstep (se 1 (by rfl) ⟨1436261, by rfl⟩ : syracuseStep 1915015 = 2872523) B2872523
theorem B1063055 : Blo 706319 1063055 := bstep (se 1 (by rfl) ⟨797291, by rfl⟩ : syracuseStep 1063055 = 1594583) B1594583
theorem B1194169 : Blo 706319 1194169 := bstep (se 2 (by rfl) ⟨447813, by rfl⟩ : syracuseStep 1194169 = 895627) B895627
theorem B1063097 : Blo 706319 1063097 := bstep (se 2 (by rfl) ⟨398661, by rfl⟩ : syracuseStep 1063097 = 797323) B797323
theorem B1063175 : Blo 706319 1063175 := bstep (se 1 (by rfl) ⟨797381, by rfl⟩ : syracuseStep 1063175 = 1594763) B1594763
theorem B1063211 : Blo 706319 1063211 := bstep (se 1 (by rfl) ⟨797408, by rfl⟩ : syracuseStep 1063211 = 1594817) B1594817
theorem B3586355 : Blo 706319 3586355 := bstep (se 1 (by rfl) ⟨2689766, by rfl⟩ : syracuseStep 3586355 = 5379533) B5379533
theorem B1063241 : Blo 706319 1063241 := bstep (se 2 (by rfl) ⟨398715, by rfl⟩ : syracuseStep 1063241 = 797431) B797431
theorem B1063355 : Blo 706319 1063355 := bstep (se 1 (by rfl) ⟨797516, by rfl⟩ : syracuseStep 1063355 = 1595033) B1595033
theorem B6797789 : Blo 706319 6797789 := bstep (se 3 (by rfl) ⟨1274585, by rfl⟩ : syracuseStep 6797789 = 2549171) B2549171
theorem B1063415 : Blo 706319 1063415 := bstep (se 1 (by rfl) ⟨797561, by rfl⟩ : syracuseStep 1063415 = 1595123) B1595123
theorem B1063439 : Blo 706319 1063439 := bstep (se 1 (by rfl) ⟨797579, by rfl⟩ : syracuseStep 1063439 = 1595159) B1595159
theorem B1063481 : Blo 706319 1063481 := bstep (se 2 (by rfl) ⟨398805, by rfl⟩ : syracuseStep 1063481 = 797611) B797611
theorem B3586679 : Blo 706319 3586679 := bstep (se 1 (by rfl) ⟨2690009, by rfl⟩ : syracuseStep 3586679 = 5380019) B5380019
theorem B1063559 : Blo 706319 1063559 := bstep (se 1 (by rfl) ⟨797669, by rfl⟩ : syracuseStep 1063559 = 1595339) B1595339
theorem B1063595 : Blo 706319 1063595 := bstep (se 1 (by rfl) ⟨797696, by rfl⟩ : syracuseStep 1063595 = 1595393) B1595393
theorem B1063625 : Blo 706319 1063625 := bstep (se 2 (by rfl) ⟨398859, by rfl⟩ : syracuseStep 1063625 = 797719) B797719
theorem B1063739 : Blo 706319 1063739 := bstep (se 1 (by rfl) ⟨797804, by rfl⟩ : syracuseStep 1063739 = 1595609) B1595609
theorem B1194871 : Blo 706319 1194871 := bstep (se 1 (by rfl) ⟨896153, by rfl⟩ : syracuseStep 1194871 = 1792307) B1792307
theorem B1063799 : Blo 706319 1063799 := bstep (se 1 (by rfl) ⟨797849, by rfl⟩ : syracuseStep 1063799 = 1595699) B1595699
theorem B1063823 : Blo 706319 1063823 := bstep (se 1 (by rfl) ⟨797867, by rfl⟩ : syracuseStep 1063823 = 1595735) B1595735
theorem B4537241 : Blo 706319 4537241 := bstep (se 2 (by rfl) ⟨1701465, by rfl⟩ : syracuseStep 4537241 = 3402931) B3402931
theorem B1063865 : Blo 706319 1063865 := bstep (se 2 (by rfl) ⟨398949, by rfl⟩ : syracuseStep 1063865 = 797899) B797899
theorem B1063943 : Blo 706319 1063943 := bstep (se 1 (by rfl) ⟨797957, by rfl⟩ : syracuseStep 1063943 = 1595915) B1595915
theorem B1063979 : Blo 706319 1063979 := bstep (se 1 (by rfl) ⟨797984, by rfl⟩ : syracuseStep 1063979 = 1595969) B1595969
theorem B1195067 : Blo 706319 1195067 := bstep (se 1 (by rfl) ⟨896300, by rfl⟩ : syracuseStep 1195067 = 1792601) B1792601
theorem B1064009 : Blo 706319 1064009 := bstep (se 2 (by rfl) ⟨399003, by rfl⟩ : syracuseStep 1064009 = 798007) B798007
theorem B1064123 : Blo 706319 1064123 := bstep (se 1 (by rfl) ⟨798092, by rfl⟩ : syracuseStep 1064123 = 1596185) B1596185
theorem B2014409 : Blo 706319 2014409 := bstep (se 2 (by rfl) ⟨755403, by rfl⟩ : syracuseStep 2014409 = 1510807) B1510807
theorem B1064183 : Blo 706319 1064183 := bstep (se 1 (by rfl) ⟨798137, by rfl⟩ : syracuseStep 1064183 = 1596275) B1596275
theorem B1064207 : Blo 706319 1064207 := bstep (se 1 (by rfl) ⟨798155, by rfl⟩ : syracuseStep 1064207 = 1596311) B1596311
theorem B1064249 : Blo 706319 1064249 := bstep (se 2 (by rfl) ⟨399093, by rfl⟩ : syracuseStep 1064249 = 798187) B798187
theorem B1064327 : Blo 706319 1064327 := bstep (se 1 (by rfl) ⟨798245, by rfl⟩ : syracuseStep 1064327 = 1596491) B1596491
theorem B1064363 : Blo 706319 1064363 := bstep (se 1 (by rfl) ⟨798272, by rfl⟩ : syracuseStep 1064363 = 1596545) B1596545
theorem B1195465 : Blo 706319 1195465 := bstep (se 2 (by rfl) ⟨448299, by rfl⟩ : syracuseStep 1195465 = 896599) B896599
theorem B1064393 : Blo 706319 1064393 := bstep (se 2 (by rfl) ⟨399147, by rfl⟩ : syracuseStep 1064393 = 798295) B798295
theorem B7650845 : Blo 706319 7650845 := bstep (se 3 (by rfl) ⟨1434533, by rfl⟩ : syracuseStep 7650845 = 2869067) B2869067
theorem B1064507 : Blo 706319 1064507 := bstep (se 1 (by rfl) ⟨798380, by rfl⟩ : syracuseStep 1064507 = 1596761) B1596761
theorem B3587651 : Blo 706319 3587651 := bstep (se 1 (by rfl) ⟨2690738, by rfl⟩ : syracuseStep 3587651 = 5381477) B5381477
theorem B1064567 : Blo 706319 1064567 := bstep (se 1 (by rfl) ⟨798425, by rfl⟩ : syracuseStep 1064567 = 1596851) B1596851
theorem B1064591 : Blo 706319 1064591 := bstep (se 1 (by rfl) ⟨798443, by rfl⟩ : syracuseStep 1064591 = 1596887) B1596887
theorem B1064633 : Blo 706319 1064633 := bstep (se 2 (by rfl) ⟨399237, by rfl⟩ : syracuseStep 1064633 = 798475) B798475
theorem B1064711 : Blo 706319 1064711 := bstep (se 1 (by rfl) ⟨798533, by rfl⟩ : syracuseStep 1064711 = 1597067) B1597067
theorem B1064747 : Blo 706319 1064747 := bstep (se 1 (by rfl) ⟨798560, by rfl⟩ : syracuseStep 1064747 = 1597121) B1597121
theorem B1064777 : Blo 706319 1064777 := bstep (se 2 (by rfl) ⟨399291, by rfl⟩ : syracuseStep 1064777 = 798583) B798583
theorem B3587975 : Blo 706319 3587975 := bstep (se 1 (by rfl) ⟨2690981, by rfl⟩ : syracuseStep 3587975 = 5381963) B5381963
theorem B20234137 : Blo 706319 20234137 := bstep (se 2 (by rfl) ⟨7587801, by rfl⟩ : syracuseStep 20234137 = 15175603) B15175603
theorem B1064891 : Blo 706319 1064891 := bstep (se 1 (by rfl) ⟨798668, by rfl⟩ : syracuseStep 1064891 = 1597337) B1597337
theorem B1064951 : Blo 706319 1064951 := bstep (se 1 (by rfl) ⟨798713, by rfl⟩ : syracuseStep 1064951 = 1597427) B1597427
theorem B1064975 : Blo 706319 1064975 := bstep (se 1 (by rfl) ⟨798731, by rfl⟩ : syracuseStep 1064975 = 1597463) B1597463
theorem B1589291 : Blo 706319 1589291 := bstep (se 1 (by rfl) ⟨1191968, by rfl⟩ : syracuseStep 1589291 = 2383937) B2383937
theorem B2015275 : Blo 706319 2015275 := bstep (se 1 (by rfl) ⟨1511456, by rfl⟩ : syracuseStep 2015275 = 3022913) B3022913
theorem B1065017 : Blo 706319 1065017 := bstep (se 2 (by rfl) ⟨399381, by rfl⟩ : syracuseStep 1065017 = 798763) B798763
theorem B1196167 : Blo 706319 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B1065095 : Blo 706319 1065095 := bstep (se 1 (by rfl) ⟨798821, by rfl⟩ : syracuseStep 1065095 = 1597643) B1597643
theorem B1065131 : Blo 706319 1065131 := bstep (se 1 (by rfl) ⟨798848, by rfl⟩ : syracuseStep 1065131 = 1597697) B1597697
theorem B1065161 : Blo 706319 1065161 := bstep (se 2 (by rfl) ⟨399435, by rfl⟩ : syracuseStep 1065161 = 798871) B798871
theorem B12927221 : Blo 706319 12927221 := bstep (se 5 (by rfl) ⟨605963, by rfl⟩ : syracuseStep 12927221 = 1211927) B1211927
theorem B1065275 : Blo 706319 1065275 := bstep (se 1 (by rfl) ⟨798956, by rfl⟩ : syracuseStep 1065275 = 1597913) B1597913
theorem B2015549 : Blo 706319 2015549 := bstep (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) B755831
theorem B1065335 : Blo 706319 1065335 := bstep (se 1 (by rfl) ⟨799001, by rfl⟩ : syracuseStep 1065335 = 1598003) B1598003
theorem B1065359 : Blo 706319 1065359 := bstep (se 1 (by rfl) ⟨799019, by rfl⟩ : syracuseStep 1065359 = 1598039) B1598039
theorem B1589651 : Blo 706319 1589651 := bstep (se 1 (by rfl) ⟨1192238, by rfl⟩ : syracuseStep 1589651 = 2384477) B2384477
theorem B1065401 : Blo 706319 1065401 := bstep (se 2 (by rfl) ⟨399525, by rfl⟩ : syracuseStep 1065401 = 799051) B799051
theorem B1589705 : Blo 706319 1589705 := bstep (se 2 (by rfl) ⟨596139, by rfl⟩ : syracuseStep 1589705 = 1192279) B1192279
theorem B1065479 : Blo 706319 1065479 := bstep (se 1 (by rfl) ⟨799109, by rfl⟩ : syracuseStep 1065479 = 1598219) B1598219
theorem B2867723 : Blo 706319 2867723 := bstep (se 1 (by rfl) ⟨2150792, by rfl⟩ : syracuseStep 2867723 = 4301585) B4301585
theorem B2015891 : Blo 706319 2015891 := bstep (se 1 (by rfl) ⟨1511918, by rfl⟩ : syracuseStep 2015891 = 3023837) B3023837
theorem B1196815 : Blo 706319 1196815 := bstep (se 1 (by rfl) ⟨897611, by rfl⟩ : syracuseStep 1196815 = 1795223) B1795223
theorem B1819577 : Blo 706319 1819577 := bstep (se 2 (by rfl) ⟨682341, by rfl⟩ : syracuseStep 1819577 = 1364683) B1364683
theorem B13616261 : Blo 706319 13616261 := bstep (se 4 (by rfl) ⟨1276524, by rfl⟩ : syracuseStep 13616261 = 2553049) B2553049
theorem B1590407 : Blo 706319 1590407 := bstep (se 1 (by rfl) ⟨1192805, by rfl⟩ : syracuseStep 1590407 = 2385611) B2385611
theorem B1361195 : Blo 706319 1361195 := bstep (se 1 (by rfl) ⟨1020896, by rfl⟩ : syracuseStep 1361195 = 2041793) B2041793
theorem B1197355 : Blo 706319 1197355 := bstep (se 1 (by rfl) ⟨898016, by rfl⟩ : syracuseStep 1197355 = 1796033) B1796033
theorem B1590587 : Blo 706319 1590587 := bstep (se 1 (by rfl) ⟨1192940, by rfl⟩ : syracuseStep 1590587 = 2385881) B2385881
theorem B1590713 : Blo 706319 1590713 := bstep (se 2 (by rfl) ⟨596517, by rfl⟩ : syracuseStep 1590713 = 1193035) B1193035
theorem B8078777 : Blo 706319 8078777 := bstep (se 2 (by rfl) ⟨3029541, by rfl⟩ : syracuseStep 8078777 = 6059083) B6059083
theorem B1197497 : Blo 706319 1197497 := bstep (se 2 (by rfl) ⟨449061, by rfl⟩ : syracuseStep 1197497 = 898123) B898123
theorem B1918475 : Blo 706319 1918475 := bstep (se 1 (by rfl) ⟨1438856, by rfl⟩ : syracuseStep 1918475 = 2877713) B2877713
theorem B706319 : Blo 706319 706319 := bstep (se 1 (by rfl) ⟨529739, by rfl⟩ : syracuseStep 706319 = 1059479) B1059479
theorem B1591055 : Blo 706319 1591055 := bstep (se 1 (by rfl) ⟨1193291, by rfl⟩ : syracuseStep 1591055 = 2386583) B2386583
theorem B1591073 : Blo 706319 1591073 := bstep (se 2 (by rfl) ⟨596652, by rfl⟩ : syracuseStep 1591073 = 1193305) B1193305
theorem B706363 : Blo 706319 706363 := bstep (se 1 (by rfl) ⟨529772, by rfl⟩ : syracuseStep 706363 = 1059545) B1059545
theorem B2148211 : Blo 706319 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B706439 : Blo 706319 706439 := bstep (se 1 (by rfl) ⟨529829, by rfl⟩ : syracuseStep 706439 = 1059659) B1059659
theorem B706447 : Blo 706319 706447 := bstep (se 1 (by rfl) ⟨529835, by rfl⟩ : syracuseStep 706447 = 1059671) B1059671
theorem B2049977 : Blo 706319 2049977 := bstep (se 2 (by rfl) ⟨768741, by rfl⟩ : syracuseStep 2049977 = 1537483) B1537483
theorem B706491 : Blo 706319 706491 := bstep (se 1 (by rfl) ⟨529868, by rfl⟩ : syracuseStep 706491 = 1059737) B1059737
theorem B706567 : Blo 706319 706567 := bstep (se 1 (by rfl) ⟨529925, by rfl⟩ : syracuseStep 706567 = 1059851) B1059851
theorem B706575 : Blo 706319 706575 := bstep (se 1 (by rfl) ⟨529931, by rfl⟩ : syracuseStep 706575 = 1059863) B1059863
theorem B706619 : Blo 706319 706619 := bstep (se 1 (by rfl) ⟨529964, by rfl⟩ : syracuseStep 706619 = 1059929) B1059929
theorem B1591415 : Blo 706319 1591415 := bstep (se 1 (by rfl) ⟨1193561, by rfl⟩ : syracuseStep 1591415 = 2387123) B2387123
theorem B1198199 : Blo 706319 1198199 := bstep (se 1 (by rfl) ⟨898649, by rfl⟩ : syracuseStep 1198199 = 1797299) B1797299
theorem B706695 : Blo 706319 706695 := bstep (se 1 (by rfl) ⟨530021, by rfl⟩ : syracuseStep 706695 = 1060043) B1060043
theorem B706703 : Blo 706319 706703 := bstep (se 1 (by rfl) ⟨530027, by rfl⟩ : syracuseStep 706703 = 1060055) B1060055
theorem B706747 : Blo 706319 706747 := bstep (se 1 (by rfl) ⟨530060, by rfl⟩ : syracuseStep 706747 = 1060121) B1060121
theorem B6047945 : Blo 706319 6047945 := bstep (se 2 (by rfl) ⟨2267979, by rfl⟩ : syracuseStep 6047945 = 4535959) B4535959
theorem B706823 : Blo 706319 706823 := bstep (se 1 (by rfl) ⟨530117, by rfl⟩ : syracuseStep 706823 = 1060235) B1060235
theorem B706831 : Blo 706319 706831 := bstep (se 1 (by rfl) ⟨530123, by rfl⟩ : syracuseStep 706831 = 1060247) B1060247
theorem B1591595 : Blo 706319 1591595 := bstep (se 1 (by rfl) ⟨1193696, by rfl⟩ : syracuseStep 1591595 = 2387393) B2387393
theorem B706875 : Blo 706319 706875 := bstep (se 1 (by rfl) ⟨530156, by rfl⟩ : syracuseStep 706875 = 1060313) B1060313
theorem B8735035 : Blo 706319 8735035 := bstep (se 1 (by rfl) ⟨6551276, by rfl⟩ : syracuseStep 8735035 = 13102553) B13102553
theorem B706951 : Blo 706319 706951 := bstep (se 1 (by rfl) ⟨530213, by rfl⟩ : syracuseStep 706951 = 1060427) B1060427
theorem B706959 : Blo 706319 706959 := bstep (se 1 (by rfl) ⟨530219, by rfl⟩ : syracuseStep 706959 = 1060439) B1060439
theorem B707003 : Blo 706319 707003 := bstep (se 1 (by rfl) ⟨530252, by rfl⟩ : syracuseStep 707003 = 1060505) B1060505
theorem B4540931 : Blo 706319 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B707079 : Blo 706319 707079 := bstep (se 1 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 707079 = 1060619) B1060619
theorem B707087 : Blo 706319 707087 := bstep (se 1 (by rfl) ⟨530315, by rfl⟩ : syracuseStep 707087 = 1060631) B1060631
theorem B707131 : Blo 706319 707131 := bstep (se 1 (by rfl) ⟨530348, by rfl⟩ : syracuseStep 707131 = 1060697) B1060697
theorem B1198651 : Blo 706319 1198651 := bstep (se 1 (by rfl) ⟨898988, by rfl⟩ : syracuseStep 1198651 = 1797977) B1797977
theorem B1788551 : Blo 706319 1788551 := bstep (se 1 (by rfl) ⟨1341413, by rfl⟩ : syracuseStep 1788551 = 2682827) B2682827
theorem B707207 : Blo 706319 707207 := bstep (se 1 (by rfl) ⟨530405, by rfl⟩ : syracuseStep 707207 = 1060811) B1060811
theorem B707215 : Blo 706319 707215 := bstep (se 1 (by rfl) ⟨530411, by rfl⟩ : syracuseStep 707215 = 1060823) B1060823
theorem B1591955 : Blo 706319 1591955 := bstep (se 1 (by rfl) ⟨1193966, by rfl⟩ : syracuseStep 1591955 = 2387933) B2387933
theorem B1788601 : Blo 706319 1788601 := bstep (se 2 (by rfl) ⟨670725, by rfl⟩ : syracuseStep 1788601 = 1341451) B1341451
theorem B707259 : Blo 706319 707259 := bstep (se 1 (by rfl) ⟨530444, by rfl⟩ : syracuseStep 707259 = 1060889) B1060889
theorem B1592009 : Blo 706319 1592009 := bstep (se 2 (by rfl) ⟨597003, by rfl⟩ : syracuseStep 1592009 = 1194007) B1194007
theorem B3066569 : Blo 706319 3066569 := bstep (se 2 (by rfl) ⟨1149963, by rfl⟩ : syracuseStep 3066569 = 2299927) B2299927
theorem B707335 : Blo 706319 707335 := bstep (se 1 (by rfl) ⟨530501, by rfl⟩ : syracuseStep 707335 = 1061003) B1061003
theorem B707343 : Blo 706319 707343 := bstep (se 1 (by rfl) ⟨530507, by rfl⟩ : syracuseStep 707343 = 1061015) B1061015
theorem B707387 : Blo 706319 707387 := bstep (se 1 (by rfl) ⟨530540, by rfl⟩ : syracuseStep 707387 = 1061081) B1061081
theorem B2018135 : Blo 706319 2018135 := bstep (se 1 (by rfl) ⟨1513601, by rfl⟩ : syracuseStep 2018135 = 3027203) B3027203
theorem B41503589 : Blo 706319 41503589 := bstep (se 4 (by rfl) ⟨3890961, by rfl⟩ : syracuseStep 41503589 = 7781923) B7781923
theorem B707463 : Blo 706319 707463 := bstep (se 1 (by rfl) ⟨530597, by rfl⟩ : syracuseStep 707463 = 1061195) B1061195
theorem B707471 : Blo 706319 707471 := bstep (se 1 (by rfl) ⟨530603, by rfl⟩ : syracuseStep 707471 = 1061207) B1061207
theorem B707515 : Blo 706319 707515 := bstep (se 1 (by rfl) ⟨530636, by rfl⟩ : syracuseStep 707515 = 1061273) B1061273
theorem B707591 : Blo 706319 707591 := bstep (se 1 (by rfl) ⟨530693, by rfl⟩ : syracuseStep 707591 = 1061387) B1061387
theorem B707599 : Blo 706319 707599 := bstep (se 1 (by rfl) ⟨530699, by rfl⟩ : syracuseStep 707599 = 1061399) B1061399
theorem B707643 : Blo 706319 707643 := bstep (se 1 (by rfl) ⟨530732, by rfl⟩ : syracuseStep 707643 = 1061465) B1061465
theorem B707719 : Blo 706319 707719 := bstep (se 1 (by rfl) ⟨530789, by rfl⟩ : syracuseStep 707719 = 1061579) B1061579
theorem B707727 : Blo 706319 707727 := bstep (se 1 (by rfl) ⟨530795, by rfl⟩ : syracuseStep 707727 = 1061591) B1061591
theorem B707771 : Blo 706319 707771 := bstep (se 1 (by rfl) ⟨530828, by rfl⟩ : syracuseStep 707771 = 1061657) B1061657
theorem B707847 : Blo 706319 707847 := bstep (se 1 (by rfl) ⟨530885, by rfl⟩ : syracuseStep 707847 = 1061771) B1061771
theorem B1789199 : Blo 706319 1789199 := bstep (se 1 (by rfl) ⟨1341899, by rfl⟩ : syracuseStep 1789199 = 2683799) B2683799
theorem B707855 : Blo 706319 707855 := bstep (se 1 (by rfl) ⟨530891, by rfl⟩ : syracuseStep 707855 = 1061783) B1061783
theorem B707899 : Blo 706319 707899 := bstep (se 1 (by rfl) ⟨530924, by rfl⟩ : syracuseStep 707899 = 1061849) B1061849
theorem B3591539 : Blo 706319 3591539 := bstep (se 1 (by rfl) ⟨2693654, by rfl⟩ : syracuseStep 3591539 = 5387309) B5387309
theorem B1592711 : Blo 706319 1592711 := bstep (se 1 (by rfl) ⟨1194533, by rfl⟩ : syracuseStep 1592711 = 2389067) B2389067
theorem B707975 : Blo 706319 707975 := bstep (se 1 (by rfl) ⟨530981, by rfl⟩ : syracuseStep 707975 = 1061963) B1061963
theorem B4541831 : Blo 706319 4541831 := bstep (se 1 (by rfl) ⟨3406373, by rfl⟩ : syracuseStep 4541831 = 6812747) B6812747
theorem B707983 : Blo 706319 707983 := bstep (se 1 (by rfl) ⟨530987, by rfl⟩ : syracuseStep 707983 = 1061975) B1061975
theorem B708027 : Blo 706319 708027 := bstep (se 1 (by rfl) ⟨531020, by rfl⟩ : syracuseStep 708027 = 1062041) B1062041
theorem B2182601 : Blo 706319 2182601 := bstep (se 2 (by rfl) ⟨818475, by rfl⟩ : syracuseStep 2182601 = 1636951) B1636951
theorem B708103 : Blo 706319 708103 := bstep (se 1 (by rfl) ⟨531077, by rfl⟩ : syracuseStep 708103 = 1062155) B1062155
theorem B708111 : Blo 706319 708111 := bstep (se 1 (by rfl) ⟨531083, by rfl⟩ : syracuseStep 708111 = 1062167) B1062167
theorem B1592891 : Blo 706319 1592891 := bstep (se 1 (by rfl) ⟨1194668, by rfl⟩ : syracuseStep 1592891 = 2389337) B2389337
theorem B708155 : Blo 706319 708155 := bstep (se 1 (by rfl) ⟨531116, by rfl⟩ : syracuseStep 708155 = 1062233) B1062233
theorem B708231 : Blo 706319 708231 := bstep (se 1 (by rfl) ⟨531173, by rfl⟩ : syracuseStep 708231 = 1062347) B1062347
theorem B708239 : Blo 706319 708239 := bstep (se 1 (by rfl) ⟨531179, by rfl⟩ : syracuseStep 708239 = 1062359) B1062359
theorem B1593017 : Blo 706319 1593017 := bstep (se 2 (by rfl) ⟨597381, by rfl⟩ : syracuseStep 1593017 = 1194763) B1194763
theorem B708283 : Blo 706319 708283 := bstep (se 1 (by rfl) ⟨531212, by rfl⟩ : syracuseStep 708283 = 1062425) B1062425
theorem B708359 : Blo 706319 708359 := bstep (se 1 (by rfl) ⟨531269, by rfl⟩ : syracuseStep 708359 = 1062539) B1062539
theorem B708367 : Blo 706319 708367 := bstep (se 1 (by rfl) ⟨531275, by rfl⟩ : syracuseStep 708367 = 1062551) B1062551
theorem B708411 : Blo 706319 708411 := bstep (se 1 (by rfl) ⟨531308, by rfl⟩ : syracuseStep 708411 = 1062617) B1062617
theorem B3592025 : Blo 706319 3592025 := bstep (se 2 (by rfl) ⟨1347009, by rfl⟩ : syracuseStep 3592025 = 2694019) B2694019
theorem B708487 : Blo 706319 708487 := bstep (se 1 (by rfl) ⟨531365, by rfl⟩ : syracuseStep 708487 = 1062731) B1062731
theorem B708495 : Blo 706319 708495 := bstep (se 1 (by rfl) ⟨531371, by rfl⟩ : syracuseStep 708495 = 1062743) B1062743
theorem B708539 : Blo 706319 708539 := bstep (se 1 (by rfl) ⟨531404, by rfl⟩ : syracuseStep 708539 = 1062809) B1062809
theorem B1789897 : Blo 706319 1789897 := bstep (se 2 (by rfl) ⟨671211, by rfl⟩ : syracuseStep 1789897 = 1342423) B1342423
theorem B708615 : Blo 706319 708615 := bstep (se 1 (by rfl) ⟨531461, by rfl⟩ : syracuseStep 708615 = 1062923) B1062923
theorem B1593359 : Blo 706319 1593359 := bstep (se 1 (by rfl) ⟨1195019, by rfl⟩ : syracuseStep 1593359 = 2390039) B2390039
theorem B708623 : Blo 706319 708623 := bstep (se 1 (by rfl) ⟨531467, by rfl⟩ : syracuseStep 708623 = 1062935) B1062935
theorem B1593377 : Blo 706319 1593377 := bstep (se 2 (by rfl) ⟨597516, by rfl⟩ : syracuseStep 1593377 = 1195033) B1195033
theorem B3395627 : Blo 706319 3395627 := bstep (se 1 (by rfl) ⟨2546720, by rfl⟩ : syracuseStep 3395627 = 5093441) B5093441
theorem B708667 : Blo 706319 708667 := bstep (se 1 (by rfl) ⟨531500, by rfl⟩ : syracuseStep 708667 = 1063001) B1063001
theorem B1790039 : Blo 706319 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B708743 : Blo 706319 708743 := bstep (se 1 (by rfl) ⟨531557, by rfl⟩ : syracuseStep 708743 = 1063115) B1063115
theorem B708751 : Blo 706319 708751 := bstep (se 1 (by rfl) ⟨531563, by rfl⟩ : syracuseStep 708751 = 1063127) B1063127
theorem B6475949 : Blo 706319 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B708795 : Blo 706319 708795 := bstep (se 1 (by rfl) ⟨531596, by rfl⟩ : syracuseStep 708795 = 1063193) B1063193
theorem B708871 : Blo 706319 708871 := bstep (se 1 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 708871 = 1063307) B1063307
theorem B2150671 : Blo 706319 2150671 := bstep (se 1 (by rfl) ⟨1613003, by rfl⟩ : syracuseStep 2150671 = 3226007) B3226007
theorem B708879 : Blo 706319 708879 := bstep (se 1 (by rfl) ⟨531659, by rfl⟩ : syracuseStep 708879 = 1063319) B1063319
theorem B708923 : Blo 706319 708923 := bstep (se 1 (by rfl) ⟨531692, by rfl⟩ : syracuseStep 708923 = 1063385) B1063385
theorem B1593719 : Blo 706319 1593719 := bstep (se 1 (by rfl) ⟨1195289, by rfl⟩ : syracuseStep 1593719 = 2390579) B2390579
theorem B708999 : Blo 706319 708999 := bstep (se 1 (by rfl) ⟨531749, by rfl⟩ : syracuseStep 708999 = 1063499) B1063499
theorem B709007 : Blo 706319 709007 := bstep (se 1 (by rfl) ⟨531755, by rfl⟩ : syracuseStep 709007 = 1063511) B1063511
theorem B709051 : Blo 706319 709051 := bstep (se 1 (by rfl) ⟨531788, by rfl⟩ : syracuseStep 709051 = 1063577) B1063577
theorem B709127 : Blo 706319 709127 := bstep (se 1 (by rfl) ⟨531845, by rfl⟩ : syracuseStep 709127 = 1063691) B1063691
theorem B2150927 : Blo 706319 2150927 := bstep (se 1 (by rfl) ⟨1613195, by rfl⟩ : syracuseStep 2150927 = 3226391) B3226391
theorem B709135 : Blo 706319 709135 := bstep (se 1 (by rfl) ⟨531851, by rfl⟩ : syracuseStep 709135 = 1063703) B1063703
theorem B1593899 : Blo 706319 1593899 := bstep (se 1 (by rfl) ⟨1195424, by rfl⟩ : syracuseStep 1593899 = 2390849) B2390849
theorem B709179 : Blo 706319 709179 := bstep (se 1 (by rfl) ⟨531884, by rfl⟩ : syracuseStep 709179 = 1063769) B1063769
theorem B709255 : Blo 706319 709255 := bstep (se 1 (by rfl) ⟨531941, by rfl⟩ : syracuseStep 709255 = 1063883) B1063883
theorem B709263 : Blo 706319 709263 := bstep (se 1 (by rfl) ⟨531947, by rfl⟩ : syracuseStep 709263 = 1063895) B1063895
theorem B709307 : Blo 706319 709307 := bstep (se 1 (by rfl) ⟨531980, by rfl⟩ : syracuseStep 709307 = 1063961) B1063961
theorem B709383 : Blo 706319 709383 := bstep (se 1 (by rfl) ⟨532037, by rfl⟩ : syracuseStep 709383 = 1064075) B1064075
theorem B709391 : Blo 706319 709391 := bstep (se 1 (by rfl) ⟨532043, by rfl⟩ : syracuseStep 709391 = 1064087) B1064087
theorem B6050609 : Blo 706319 6050609 := bstep (se 2 (by rfl) ⟨2268978, by rfl⟩ : syracuseStep 6050609 = 4537957) B4537957
theorem B709435 : Blo 706319 709435 := bstep (se 1 (by rfl) ⟨532076, by rfl⟩ : syracuseStep 709435 = 1064153) B1064153
theorem B2872199 : Blo 706319 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B709511 : Blo 706319 709511 := bstep (se 1 (by rfl) ⟨532133, by rfl⟩ : syracuseStep 709511 = 1064267) B1064267
theorem B709519 : Blo 706319 709519 := bstep (se 1 (by rfl) ⟨532139, by rfl⟩ : syracuseStep 709519 = 1064279) B1064279
theorem B1594259 : Blo 706319 1594259 := bstep (se 1 (by rfl) ⟨1195694, by rfl⟩ : syracuseStep 1594259 = 2391389) B2391389
theorem B709563 : Blo 706319 709563 := bstep (se 1 (by rfl) ⟨532172, by rfl⟩ : syracuseStep 709563 = 1064345) B1064345
theorem B1594313 : Blo 706319 1594313 := bstep (se 2 (by rfl) ⟨597867, by rfl⟩ : syracuseStep 1594313 = 1195735) B1195735
theorem B709639 : Blo 706319 709639 := bstep (se 1 (by rfl) ⟨532229, by rfl⟩ : syracuseStep 709639 = 1064459) B1064459
theorem B709647 : Blo 706319 709647 := bstep (se 1 (by rfl) ⟨532235, by rfl⟩ : syracuseStep 709647 = 1064471) B1064471
theorem B709691 : Blo 706319 709691 := bstep (se 1 (by rfl) ⟨532268, by rfl⟩ : syracuseStep 709691 = 1064537) B1064537
theorem B709767 : Blo 706319 709767 := bstep (se 1 (by rfl) ⟨532325, by rfl⟩ : syracuseStep 709767 = 1064651) B1064651
theorem B709775 : Blo 706319 709775 := bstep (se 1 (by rfl) ⟨532331, by rfl⟩ : syracuseStep 709775 = 1064663) B1064663
theorem B709819 : Blo 706319 709819 := bstep (se 1 (by rfl) ⟨532364, by rfl⟩ : syracuseStep 709819 = 1064729) B1064729
theorem B709895 : Blo 706319 709895 := bstep (se 1 (by rfl) ⟨532421, by rfl⟩ : syracuseStep 709895 = 1064843) B1064843
theorem B709903 : Blo 706319 709903 := bstep (se 1 (by rfl) ⟨532427, by rfl⟩ : syracuseStep 709903 = 1064855) B1064855
theorem B3626299 : Blo 706319 3626299 := bstep (se 1 (by rfl) ⟨2719724, by rfl⟩ : syracuseStep 3626299 = 5439449) B5439449
theorem B709947 : Blo 706319 709947 := bstep (se 1 (by rfl) ⟨532460, by rfl⟩ : syracuseStep 709947 = 1064921) B1064921
theorem B23287175 : Blo 706319 23287175 := bstep (se 1 (by rfl) ⟨17465381, by rfl⟩ : syracuseStep 23287175 = 34930763) B34930763
theorem B710023 : Blo 706319 710023 := bstep (se 1 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 710023 = 1065035) B1065035
theorem B710031 : Blo 706319 710031 := bstep (se 1 (by rfl) ⟨532523, by rfl⟩ : syracuseStep 710031 = 1065047) B1065047
theorem B3397049 : Blo 706319 3397049 := bstep (se 2 (by rfl) ⟨1273893, by rfl⟩ : syracuseStep 3397049 = 2547787) B2547787
theorem B710075 : Blo 706319 710075 := bstep (se 1 (by rfl) ⟨532556, by rfl⟩ : syracuseStep 710075 = 1065113) B1065113
theorem B6051293 : Blo 706319 6051293 := bstep (se 3 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 6051293 = 2269235) B2269235
theorem B710151 : Blo 706319 710151 := bstep (se 1 (by rfl) ⟨532613, by rfl⟩ : syracuseStep 710151 = 1065227) B1065227
theorem B1136143 : Blo 706319 1136143 := bstep (se 1 (by rfl) ⟨852107, by rfl⟩ : syracuseStep 1136143 = 1704215) B1704215
theorem B2020879 : Blo 706319 2020879 := bstep (se 1 (by rfl) ⟨1515659, by rfl⟩ : syracuseStep 2020879 = 3031319) B3031319
theorem B710159 : Blo 706319 710159 := bstep (se 1 (by rfl) ⟨532619, by rfl⟩ : syracuseStep 710159 = 1065239) B1065239
theorem B710203 : Blo 706319 710203 := bstep (se 1 (by rfl) ⟨532652, by rfl⟩ : syracuseStep 710203 = 1065305) B1065305
theorem B2020925 : Blo 706319 2020925 := bstep (se 3 (by rfl) ⟨378923, by rfl⟩ : syracuseStep 2020925 = 757847) B757847
theorem B25876037 : Blo 706319 25876037 := bstep (se 4 (by rfl) ⟨2425878, by rfl⟩ : syracuseStep 25876037 = 4851757) B4851757
theorem B1595015 : Blo 706319 1595015 := bstep (se 1 (by rfl) ⟨1196261, by rfl⟩ : syracuseStep 1595015 = 2392523) B2392523
theorem B710279 : Blo 706319 710279 := bstep (se 1 (by rfl) ⟨532709, by rfl⟩ : syracuseStep 710279 = 1065419) B1065419
theorem B710287 : Blo 706319 710287 := bstep (se 1 (by rfl) ⟨532715, by rfl⟩ : syracuseStep 710287 = 1065431) B1065431
theorem B1595195 : Blo 706319 1595195 := bstep (se 1 (by rfl) ⟨1196396, by rfl⟩ : syracuseStep 1595195 = 2392793) B2392793
theorem B2021267 : Blo 706319 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B3594131 : Blo 706319 3594131 := bstep (se 1 (by rfl) ⟨2695598, by rfl⟩ : syracuseStep 3594131 = 5391197) B5391197
theorem B1595321 : Blo 706319 1595321 := bstep (se 2 (by rfl) ⟨598245, by rfl⟩ : syracuseStep 1595321 = 1196491) B1196491
theorem B9099287 : Blo 706319 9099287 := bstep (se 1 (by rfl) ⟨6824465, by rfl⟩ : syracuseStep 9099287 = 13648931) B13648931
theorem B1792115 : Blo 706319 1792115 := bstep (se 1 (by rfl) ⟨1344086, by rfl⟩ : syracuseStep 1792115 = 2688173) B2688173
theorem B2545901 : Blo 706319 2545901 := bstep (se 3 (by rfl) ⟨477356, by rfl⟩ : syracuseStep 2545901 = 954713) B954713
theorem B1005815 : Blo 706319 1005815 := bstep (se 1 (by rfl) ⟨754361, by rfl⟩ : syracuseStep 1005815 = 1508723) B1508723
theorem B1595663 : Blo 706319 1595663 := bstep (se 1 (by rfl) ⟨1196747, by rfl⟩ : syracuseStep 1595663 = 2393495) B2393495
theorem B1595681 : Blo 706319 1595681 := bstep (se 2 (by rfl) ⟨598380, by rfl⟩ : syracuseStep 1595681 = 1196761) B1196761
theorem B8051075 : Blo 706319 8051075 := bstep (se 1 (by rfl) ⟨6038306, by rfl⟩ : syracuseStep 8051075 = 12076613) B12076613
theorem B1006123 : Blo 706319 1006123 := bstep (se 1 (by rfl) ⟨754592, by rfl⟩ : syracuseStep 1006123 = 1509185) B1509185
theorem B1792631 : Blo 706319 1792631 := bstep (se 1 (by rfl) ⟨1344473, by rfl⟩ : syracuseStep 1792631 = 2688947) B2688947
theorem B1596023 : Blo 706319 1596023 := bstep (se 1 (by rfl) ⟨1197017, by rfl⟩ : syracuseStep 1596023 = 2394035) B2394035
theorem B2022155 : Blo 706319 2022155 := bstep (se 1 (by rfl) ⟨1516616, by rfl⟩ : syracuseStep 2022155 = 3033233) B3033233
theorem B1596203 : Blo 706319 1596203 := bstep (se 1 (by rfl) ⟨1197152, by rfl⟩ : syracuseStep 1596203 = 2394305) B2394305
theorem B4316057 : Blo 706319 4316057 := bstep (se 2 (by rfl) ⟨1618521, by rfl⟩ : syracuseStep 4316057 = 3237043) B3237043
theorem B1006607 : Blo 706319 1006607 := bstep (se 1 (by rfl) ⟨754955, by rfl⟩ : syracuseStep 1006607 = 1509911) B1509911
theorem B1596563 : Blo 706319 1596563 := bstep (se 1 (by rfl) ⟨1197422, by rfl⟩ : syracuseStep 1596563 = 2394845) B2394845
theorem B1596617 : Blo 706319 1596617 := bstep (se 2 (by rfl) ⟨598731, by rfl⟩ : syracuseStep 1596617 = 1197463) B1197463
theorem B1793623 : Blo 706319 1793623 := bstep (se 1 (by rfl) ⟨1345217, by rfl⟩ : syracuseStep 1793623 = 2690435) B2690435
theorem B1793927 : Blo 706319 1793927 := bstep (se 1 (by rfl) ⟨1345445, by rfl⟩ : syracuseStep 1793927 = 2690891) B2690891
theorem B1597319 : Blo 706319 1597319 := bstep (se 1 (by rfl) ⟨1197989, by rfl⟩ : syracuseStep 1597319 = 2395979) B2395979
theorem B12443543 : Blo 706319 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B2383883 : Blo 706319 2383883 := bstep (se 1 (by rfl) ⟨1787912, by rfl⟩ : syracuseStep 2383883 = 3575825) B3575825
theorem B1794059 : Blo 706319 1794059 := bstep (se 1 (by rfl) ⟨1345544, by rfl⟩ : syracuseStep 1794059 = 2691089) B2691089
theorem B1597499 : Blo 706319 1597499 := bstep (se 1 (by rfl) ⟨1198124, by rfl⟩ : syracuseStep 1597499 = 2396249) B2396249
theorem B2383991 : Blo 706319 2383991 := bstep (se 1 (by rfl) ⟨1787993, by rfl⟩ : syracuseStep 2383991 = 3575987) B3575987
theorem B2187383 : Blo 706319 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B1532039 : Blo 706319 1532039 := bstep (se 1 (by rfl) ⟨1149029, by rfl⟩ : syracuseStep 1532039 = 2298059) B2298059
theorem B1597625 : Blo 706319 1597625 := bstep (se 2 (by rfl) ⟨599109, by rfl⟩ : syracuseStep 1597625 = 1198219) B1198219
theorem B2548103 : Blo 706319 2548103 := bstep (se 1 (by rfl) ⟨1911077, by rfl⟩ : syracuseStep 2548103 = 3822155) B3822155
theorem B1794575 : Blo 706319 1794575 := bstep (se 1 (by rfl) ⟨1345931, by rfl⟩ : syracuseStep 1794575 = 2691863) B2691863
theorem B1597967 : Blo 706319 1597967 := bstep (se 1 (by rfl) ⟨1198475, by rfl⟩ : syracuseStep 1597967 = 2396951) B2396951
theorem B1597985 : Blo 706319 1597985 := bstep (se 2 (by rfl) ⟨599244, by rfl⟩ : syracuseStep 1597985 = 1198489) B1198489
theorem B1794707 : Blo 706319 1794707 := bstep (se 1 (by rfl) ⟨1346030, by rfl⟩ : syracuseStep 1794707 = 2692061) B2692061
theorem B2384585 : Blo 706319 2384585 := bstep (se 2 (by rfl) ⟨894219, by rfl⟩ : syracuseStep 2384585 = 1788439) B1788439
theorem B3400393 : Blo 706319 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B1008811 : Blo 706319 1008811 := bstep (se 1 (by rfl) ⟨756608, by rfl⟩ : syracuseStep 1008811 = 1513217) B1513217
theorem B4023533 : Blo 706319 4023533 := bstep (se 3 (by rfl) ⟨754412, by rfl⟩ : syracuseStep 4023533 = 1508825) B1508825
theorem B910711 : Blo 706319 910711 := bstep (se 1 (by rfl) ⟨683033, by rfl⟩ : syracuseStep 910711 = 1366067) B1366067
theorem B2385287 : Blo 706319 2385287 := bstep (se 1 (by rfl) ⟨1788965, by rfl⟩ : syracuseStep 2385287 = 3577931) B3577931
theorem B1009039 : Blo 706319 1009039 := bstep (se 1 (by rfl) ⟨756779, by rfl⟩ : syracuseStep 1009039 = 1513559) B1513559
theorem B2450987 : Blo 706319 2450987 := bstep (se 1 (by rfl) ⟨1838240, by rfl⟩ : syracuseStep 2450987 = 3676481) B3676481
theorem B21784139 : Blo 706319 21784139 := bstep (se 1 (by rfl) ⟨16338104, by rfl⟩ : syracuseStep 21784139 = 32676209) B32676209
theorem B3401453 : Blo 706319 3401453 := bstep (se 3 (by rfl) ⟨637772, by rfl⟩ : syracuseStep 3401453 = 1275545) B1275545
theorem B2385665 : Blo 706319 2385665 := bstep (se 2 (by rfl) ⟨894624, by rfl⟩ : syracuseStep 2385665 = 1789249) B1789249
theorem B1795841 : Blo 706319 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B2549519 : Blo 706319 2549519 := bstep (se 1 (by rfl) ⟨1912139, by rfl⟩ : syracuseStep 2549519 = 3824279) B3824279
theorem B2156473 : Blo 706319 2156473 := bstep (se 2 (by rfl) ⟨808677, by rfl⟩ : syracuseStep 2156473 = 1617355) B1617355
theorem B5367869 : Blo 706319 5367869 := bstep (se 3 (by rfl) ⟨1006475, by rfl⟩ : syracuseStep 5367869 = 2012951) B2012951
theorem B1796215 : Blo 706319 1796215 := bstep (se 1 (by rfl) ⟨1347161, by rfl⟩ : syracuseStep 1796215 = 2694323) B2694323
theorem B2877905 : Blo 706319 2877905 := bstep (se 2 (by rfl) ⟨1079214, by rfl⟩ : syracuseStep 2877905 = 2158429) B2158429
theorem B2386475 : Blo 706319 2386475 := bstep (se 1 (by rfl) ⟨1789856, by rfl⟩ : syracuseStep 2386475 = 3579713) B3579713
theorem B1796651 : Blo 706319 1796651 := bstep (se 1 (by rfl) ⟨1347488, by rfl⟩ : syracuseStep 1796651 = 2694977) B2694977
theorem B2157115 : Blo 706319 2157115 := bstep (se 1 (by rfl) ⟨1617836, by rfl⟩ : syracuseStep 2157115 = 3235673) B3235673
theorem B1699159 : Blo 706319 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B1797491 : Blo 706319 1797491 := bstep (se 1 (by rfl) ⟨1348118, by rfl⟩ : syracuseStep 1797491 = 2696237) B2696237
theorem B1797511 : Blo 706319 1797511 := bstep (se 1 (by rfl) ⟨1348133, by rfl⟩ : syracuseStep 1797511 = 2696267) B2696267
theorem B1797785 : Blo 706319 1797785 := bstep (se 2 (by rfl) ⟨674169, by rfl⟩ : syracuseStep 1797785 = 1348339) B1348339
theorem B2387771 : Blo 706319 2387771 := bstep (se 1 (by rfl) ⟨1790828, by rfl⟩ : syracuseStep 2387771 = 3581657) B3581657
theorem B1797947 : Blo 706319 1797947 := bstep (se 1 (by rfl) ⟨1348460, by rfl⟩ : syracuseStep 1797947 = 2696921) B2696921
theorem B2388257 : Blo 706319 2388257 := bstep (se 2 (by rfl) ⟨895596, by rfl⟩ : syracuseStep 2388257 = 1791193) B1791193
theorem B6811937 : Blo 706319 6811937 := bstep (se 2 (by rfl) ⟨2554476, by rfl⟩ : syracuseStep 6811937 = 5108953) B5108953
theorem B9073043 : Blo 706319 9073043 := bstep (se 1 (by rfl) ⟨6804782, by rfl⟩ : syracuseStep 9073043 = 13609565) B13609565
theorem B3404375 : Blo 706319 3404375 := bstep (se 1 (by rfl) ⟨2553281, by rfl⟩ : syracuseStep 3404375 = 5106563) B5106563
theorem B2388851 : Blo 706319 2388851 := bstep (se 1 (by rfl) ⟨1791638, by rfl⟩ : syracuseStep 2388851 = 3583277) B3583277
theorem B1536887 : Blo 706319 1536887 := bstep (se 1 (by rfl) ⟨1152665, by rfl⟩ : syracuseStep 1536887 = 2305331) B2305331
theorem B1209463 : Blo 706319 1209463 := bstep (se 1 (by rfl) ⟨907097, by rfl⟩ : syracuseStep 1209463 = 1814195) B1814195
theorem B5371271 : Blo 706319 5371271 := bstep (se 1 (by rfl) ⟨4028453, by rfl⟩ : syracuseStep 5371271 = 8056907) B8056907
theorem B4027907 : Blo 706319 4027907 := bstep (se 1 (by rfl) ⟨3020930, by rfl⟩ : syracuseStep 4027907 = 6041861) B6041861
theorem B8156963 : Blo 706319 8156963 := bstep (se 1 (by rfl) ⟨6117722, by rfl⟩ : syracuseStep 8156963 = 12235445) B12235445
theorem B8189747 : Blo 706319 8189747 := bstep (se 1 (by rfl) ⟨6142310, by rfl⟩ : syracuseStep 8189747 = 12284621) B12284621
theorem B6453107 : Blo 706319 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B4028363 : Blo 706319 4028363 := bstep (se 1 (by rfl) ⟨3021272, by rfl⟩ : syracuseStep 4028363 = 6042545) B6042545
theorem B1341755 : Blo 706319 1341755 := bstep (se 1 (by rfl) ⟨1006316, by rfl⟩ : syracuseStep 1341755 = 2012633) B2012633
theorem B21559769 : Blo 706319 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B3832343 : Blo 706319 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B4029047 : Blo 706319 4029047 := bstep (se 1 (by rfl) ⟨3021785, by rfl⟩ : syracuseStep 4029047 = 6043571) B6043571
theorem B1702657 : Blo 706319 1702657 := bstep (se 2 (by rfl) ⟨638496, by rfl⟩ : syracuseStep 1702657 = 1276993) B1276993
theorem B1342241 : Blo 706319 1342241 := bstep (se 2 (by rfl) ⟨503340, by rfl⟩ : syracuseStep 1342241 = 1006681) B1006681
theorem B6061067 : Blo 706319 6061067 := bstep (se 1 (by rfl) ⟨4545800, by rfl⟩ : syracuseStep 6061067 = 9091601) B9091601
theorem B1342507 : Blo 706319 1342507 := bstep (se 1 (by rfl) ⟨1006880, by rfl⟩ : syracuseStep 1342507 = 2013761) B2013761
theorem B2391443 : Blo 706319 2391443 := bstep (se 1 (by rfl) ⟨1793582, by rfl⟩ : syracuseStep 2391443 = 3587165) B3587165
theorem B1703369 : Blo 706319 1703369 := bstep (se 2 (by rfl) ⟨638763, by rfl⟩ : syracuseStep 1703369 = 1277527) B1277527
theorem B5111261 : Blo 706319 5111261 := bstep (se 3 (by rfl) ⟨958361, by rfl⟩ : syracuseStep 5111261 = 1916723) B1916723
theorem B2687033 : Blo 706319 2687033 := bstep (se 2 (by rfl) ⟨1007637, by rfl⟩ : syracuseStep 2687033 = 2015275) B2015275
theorem B8618147 : Blo 706319 8618147 := bstep (se 1 (by rfl) ⟨6463610, by rfl⟩ : syracuseStep 8618147 = 12927221) B12927221
theorem B1343699 : Blo 706319 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B5833021 : Blo 706319 5833021 := bstep (se 3 (by rfl) ⟨1093691, by rfl⟩ : syracuseStep 5833021 = 2187383) B2187383
theorem B1343927 : Blo 706319 1343927 := bstep (se 1 (by rfl) ⟨1007945, by rfl⟩ : syracuseStep 1343927 = 2015891) B2015891
theorem B1213051 : Blo 706319 1213051 := bstep (se 1 (by rfl) ⟨909788, by rfl⟩ : syracuseStep 1213051 = 1819577) B1819577
theorem B2294419 : Blo 706319 2294419 := bstep (se 1 (by rfl) ⟨1720814, by rfl⟩ : syracuseStep 2294419 = 3441629) B3441629
theorem B9700013 : Blo 706319 9700013 := bstep (se 3 (by rfl) ⟨1818752, by rfl⟩ : syracuseStep 9700013 = 3637505) B3637505
theorem B2687687 : Blo 706319 2687687 := bstep (se 1 (by rfl) ⟨2015765, by rfl⟩ : syracuseStep 2687687 = 4031531) B4031531
theorem B5374673 : Blo 706319 5374673 := bstep (se 2 (by rfl) ⟨2015502, by rfl⟩ : syracuseStep 5374673 = 4031005) B4031005
theorem B9077507 : Blo 706319 9077507 := bstep (se 1 (by rfl) ⟨6808130, by rfl⟩ : syracuseStep 9077507 = 13616261) B13616261
theorem B1278983 : Blo 706319 1278983 := bstep (se 1 (by rfl) ⟨959237, by rfl⟩ : syracuseStep 1278983 = 1918475) B1918475
theorem B2557099 : Blo 706319 2557099 := bstep (se 1 (by rfl) ⟨1917824, by rfl⟩ : syracuseStep 2557099 = 3835649) B3835649
theorem B4031963 : Blo 706319 4031963 := bstep (se 1 (by rfl) ⟨3023972, by rfl⟩ : syracuseStep 4031963 = 6047945) B6047945
theorem B10225115 : Blo 706319 10225115 := bstep (se 1 (by rfl) ⟨7668836, by rfl⟩ : syracuseStep 10225115 = 15337673) B15337673
theorem B4851211 : Blo 706319 4851211 := bstep (se 1 (by rfl) ⟨3638408, by rfl⟩ : syracuseStep 4851211 = 7276817) B7276817
theorem B1345081 : Blo 706319 1345081 := bstep (se 2 (by rfl) ⟨504405, by rfl⟩ : syracuseStep 1345081 = 1008811) B1008811
theorem B2688659 : Blo 706319 2688659 := bstep (se 1 (by rfl) ⟨2016494, by rfl⟩ : syracuseStep 2688659 = 4032989) B4032989
theorem B1214281 : Blo 706319 1214281 := bstep (se 2 (by rfl) ⟨455355, by rfl⟩ : syracuseStep 1214281 = 910711) B910711
theorem B1345385 : Blo 706319 1345385 := bstep (se 2 (by rfl) ⟨504519, by rfl⟩ : syracuseStep 1345385 = 1009039) B1009039
theorem B1345423 : Blo 706319 1345423 := bstep (se 1 (by rfl) ⟨1009067, by rfl⟩ : syracuseStep 1345423 = 2018135) B2018135
theorem B2394359 : Blo 706319 2394359 := bstep (se 1 (by rfl) ⟨1795769, by rfl⟩ : syracuseStep 2394359 = 3591539) B3591539
theorem B1706521 : Blo 706319 1706521 := bstep (se 2 (by rfl) ⟨639945, by rfl⟩ : syracuseStep 1706521 = 1279891) B1279891
theorem B2394683 : Blo 706319 2394683 := bstep (se 1 (by rfl) ⟨1796012, by rfl⟩ : syracuseStep 2394683 = 3592025) B3592025
theorem B2263751 : Blo 706319 2263751 := bstep (se 1 (by rfl) ⟨1697813, by rfl⟩ : syracuseStep 2263751 = 3395627) B3395627
theorem B2394953 : Blo 706319 2394953 := bstep (se 2 (by rfl) ⟨898107, by rfl⟩ : syracuseStep 2394953 = 1796215) B1796215
theorem B5377103 : Blo 706319 5377103 := bstep (se 1 (by rfl) ⟨4032827, by rfl⟩ : syracuseStep 5377103 = 8065655) B8065655
theorem B5049539 : Blo 706319 5049539 := bstep (se 1 (by rfl) ⟨3787154, by rfl⟩ : syracuseStep 5049539 = 7574309) B7574309
theorem B4033739 : Blo 706319 4033739 := bstep (se 1 (by rfl) ⟨3025304, by rfl⟩ : syracuseStep 4033739 = 6050609) B6050609
theorem B2264699 : Blo 706319 2264699 := bstep (se 1 (by rfl) ⟨1698524, by rfl⟩ : syracuseStep 2264699 = 3397049) B3397049
theorem B4034195 : Blo 706319 4034195 := bstep (se 1 (by rfl) ⟨3025646, by rfl⟩ : syracuseStep 4034195 = 6051293) B6051293
theorem B1347283 : Blo 706319 1347283 := bstep (se 1 (by rfl) ⟨1010462, by rfl⟩ : syracuseStep 1347283 = 2020925) B2020925
theorem B3018455 : Blo 706319 3018455 := bstep (se 1 (by rfl) ⟨2263841, by rfl⟩ : syracuseStep 3018455 = 4527683) B4527683
theorem B3018539 : Blo 706319 3018539 := bstep (se 1 (by rfl) ⟨2263904, by rfl⟩ : syracuseStep 3018539 = 4527809) B4527809
theorem B1347511 : Blo 706319 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B2396087 : Blo 706319 2396087 := bstep (se 1 (by rfl) ⟨1797065, by rfl⟩ : syracuseStep 2396087 = 3594131) B3594131
theorem B13111307 : Blo 706319 13111307 := bstep (se 1 (by rfl) ⟨9833480, by rfl⟩ : syracuseStep 13111307 = 19666961) B19666961
theorem B6066191 : Blo 706319 6066191 := bstep (se 1 (by rfl) ⟨4549643, by rfl⟩ : syracuseStep 6066191 = 9099287) B9099287
theorem B19337395 : Blo 706319 19337395 := bstep (se 1 (by rfl) ⟨14503046, by rfl⟩ : syracuseStep 19337395 = 29006093) B29006093
theorem B11506049 : Blo 706319 11506049 := bstep (se 2 (by rfl) ⟨4314768, by rfl⟩ : syracuseStep 11506049 = 8629537) B8629537
theorem B2265545 : Blo 706319 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B1348103 : Blo 706319 1348103 := bstep (se 1 (by rfl) ⟨1011077, by rfl⟩ : syracuseStep 1348103 = 2022155) B2022155
theorem B2396681 : Blo 706319 2396681 := bstep (se 2 (by rfl) ⟨898755, by rfl⟩ : syracuseStep 2396681 = 1797511) B1797511
theorem B14521133 : Blo 706319 14521133 := bstep (se 3 (by rfl) ⟨2722712, by rfl⟩ : syracuseStep 14521133 = 5445425) B5445425
theorem B3642185 : Blo 706319 3642185 := bstep (se 2 (by rfl) ⟨1365819, by rfl⟩ : syracuseStep 3642185 = 2731639) B2731639
theorem B1512379 : Blo 706319 1512379 := bstep (se 1 (by rfl) ⟨1134284, by rfl⟩ : syracuseStep 1512379 = 2268569) B2268569
theorem B8295695 : Blo 706319 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B94213489 : Blo 706319 94213489 := bstep (se 2 (by rfl) ⟨35330058, by rfl⟩ : syracuseStep 94213489 = 70660117) B70660117
theorem B2693047 : Blo 706319 2693047 := bstep (se 1 (by rfl) ⟨2019785, by rfl⟩ : syracuseStep 2693047 = 4039571) B4039571
theorem B3020915 : Blo 706319 3020915 := bstep (se 1 (by rfl) ⟨2265686, by rfl⟩ : syracuseStep 3020915 = 4531373) B4531373
theorem B3021067 : Blo 706319 3021067 := bstep (se 1 (by rfl) ⟨2265800, by rfl⟩ : syracuseStep 3021067 = 4531601) B4531601
theorem B14522759 : Blo 706319 14522759 := bstep (se 1 (by rfl) ⟨10892069, by rfl⟩ : syracuseStep 14522759 = 21784139) B21784139
theorem B2693519 : Blo 706319 2693519 := bstep (se 1 (by rfl) ⟨2020139, by rfl⟩ : syracuseStep 2693519 = 4040279) B4040279
theorem B5380505 : Blo 706319 5380505 := bstep (se 2 (by rfl) ⟨2017689, by rfl⟩ : syracuseStep 5380505 = 4035379) B4035379
theorem B2267635 : Blo 706319 2267635 := bstep (se 1 (by rfl) ⟨1700726, by rfl⟩ : syracuseStep 2267635 = 3401453) B3401453
theorem B3578579 : Blo 706319 3578579 := bstep (se 1 (by rfl) ⟨2683934, by rfl⟩ : syracuseStep 3578579 = 5367869) B5367869
theorem B4529195 : Blo 706319 4529195 := bstep (se 1 (by rfl) ⟨3396896, by rfl⟩ : syracuseStep 4529195 = 6793793) B6793793
theorem B1514857 : Blo 706319 1514857 := bstep (se 2 (by rfl) ⟨568071, by rfl⟩ : syracuseStep 1514857 = 1136143) B1136143
theorem B2694505 : Blo 706319 2694505 := bstep (se 2 (by rfl) ⟨1010439, by rfl⟩ : syracuseStep 2694505 = 2020879) B2020879
theorem B2694779 : Blo 706319 2694779 := bstep (se 1 (by rfl) ⟨2021084, by rfl⟩ : syracuseStep 2694779 = 4042169) B4042169
theorem B6037213 : Blo 706319 6037213 := bstep (se 3 (by rfl) ⟨1131977, by rfl⟩ : syracuseStep 6037213 = 2263955) B2263955
theorem B5382449 : Blo 706319 5382449 := bstep (se 2 (by rfl) ⟨2018418, by rfl⟩ : syracuseStep 5382449 = 4036837) B4036837
theorem B2269583 : Blo 706319 2269583 := bstep (se 1 (by rfl) ⟨1702187, by rfl⟩ : syracuseStep 2269583 = 3404375) B3404375
theorem B795055 : Blo 706319 795055 := bstep (se 1 (by rfl) ⟨596291, by rfl⟩ : syracuseStep 795055 = 1192583) B1192583
theorem B1024591 : Blo 706319 1024591 := bstep (se 1 (by rfl) ⟨768443, by rfl⟩ : syracuseStep 1024591 = 1536887) B1536887
theorem B795487 : Blo 706319 795487 := bstep (se 1 (by rfl) ⟨596615, by rfl⟩ : syracuseStep 795487 = 1193231) B1193231
theorem B20423573 : Blo 706319 20423573 := bstep (se 6 (by rfl) ⟨478677, by rfl⟩ : syracuseStep 20423573 = 957355) B957355
theorem B3580847 : Blo 706319 3580847 := bstep (se 1 (by rfl) ⟨2685635, by rfl⟩ : syracuseStep 3580847 = 5371271) B5371271
theorem B2270209 : Blo 706319 2270209 := bstep (se 2 (by rfl) ⟨851328, by rfl⟩ : syracuseStep 2270209 = 1702657) B1702657
theorem B795847 : Blo 706319 795847 := bstep (se 1 (by rfl) ⟨596885, by rfl⟩ : syracuseStep 795847 = 1193771) B1193771
theorem B4302071 : Blo 706319 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B894503 : Blo 706319 894503 := bstep (se 1 (by rfl) ⟨670877, by rfl⟩ : syracuseStep 894503 = 1341755) B1341755
theorem B4531859 : Blo 706319 4531859 := bstep (se 1 (by rfl) ⟨3398894, by rfl⟩ : syracuseStep 4531859 = 6797789) B6797789
theorem B894827 : Blo 706319 894827 := bstep (se 1 (by rfl) ⟨671120, by rfl⟩ : syracuseStep 894827 = 1342241) B1342241
theorem B3024827 : Blo 706319 3024827 := bstep (se 1 (by rfl) ⟨2268620, by rfl⟩ : syracuseStep 3024827 = 4537241) B4537241
theorem B4040711 : Blo 706319 4040711 := bstep (se 1 (by rfl) ⟨3030533, by rfl⟩ : syracuseStep 4040711 = 6061067) B6061067
theorem B796711 : Blo 706319 796711 := bstep (se 1 (by rfl) ⟨597533, by rfl⟩ : syracuseStep 796711 = 1195067) B1195067
theorem B3025441 : Blo 706319 3025441 := bstep (se 2 (by rfl) ⟨1134540, by rfl⟩ : syracuseStep 3025441 = 2269081) B2269081
theorem B26978849 : Blo 706319 26978849 := bstep (se 2 (by rfl) ⟨10117068, by rfl⟩ : syracuseStep 26978849 = 20234137) B20234137
theorem B1059527 : Blo 706319 1059527 := bstep (se 1 (by rfl) ⟨794645, by rfl⟩ : syracuseStep 1059527 = 1589291) B1589291
theorem B2272043 : Blo 706319 2272043 := bstep (se 1 (by rfl) ⟨1704032, by rfl⟩ : syracuseStep 2272043 = 3408065) B3408065
theorem B1059689 : Blo 706319 1059689 := bstep (se 2 (by rfl) ⟨397383, by rfl⟩ : syracuseStep 1059689 = 794767) B794767
theorem B1059767 : Blo 706319 1059767 := bstep (se 1 (by rfl) ⟨794825, by rfl⟩ : syracuseStep 1059767 = 1589651) B1589651
theorem B1059803 : Blo 706319 1059803 := bstep (se 1 (by rfl) ⟨794852, by rfl⟩ : syracuseStep 1059803 = 1589705) B1589705
theorem B1911815 : Blo 706319 1911815 := bstep (se 1 (by rfl) ⟨1433861, by rfl⟩ : syracuseStep 1911815 = 2867723) B2867723
theorem B896123 : Blo 706319 896123 := bstep (se 1 (by rfl) ⟨672092, by rfl⟩ : syracuseStep 896123 = 1344185) B1344185
theorem B1060271 : Blo 706319 1060271 := bstep (se 1 (by rfl) ⟨795203, by rfl⟩ : syracuseStep 1060271 = 1590407) B1590407
theorem B1060361 : Blo 706319 1060361 := bstep (se 2 (by rfl) ⟨397635, by rfl⟩ : syracuseStep 1060361 = 795271) B795271
theorem B1060391 : Blo 706319 1060391 := bstep (se 1 (by rfl) ⟨795293, by rfl⟩ : syracuseStep 1060391 = 1590587) B1590587
theorem B4533857 : Blo 706319 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B1060475 : Blo 706319 1060475 := bstep (se 1 (by rfl) ⟨795356, by rfl⟩ : syracuseStep 1060475 = 1590713) B1590713
theorem B5385851 : Blo 706319 5385851 := bstep (se 1 (by rfl) ⟨4039388, by rfl⟩ : syracuseStep 5385851 = 8078777) B8078777
theorem B798331 : Blo 706319 798331 := bstep (se 1 (by rfl) ⟨598748, by rfl⟩ : syracuseStep 798331 = 1197497) B1197497
theorem B6794941 : Blo 706319 6794941 := bstep (se 3 (by rfl) ⟨1274051, by rfl⟩ : syracuseStep 6794941 = 2548103) B2548103
theorem B1060601 : Blo 706319 1060601 := bstep (se 2 (by rfl) ⟨397725, by rfl⟩ : syracuseStep 1060601 = 795451) B795451
theorem B1060703 : Blo 706319 1060703 := bstep (se 1 (by rfl) ⟨795527, by rfl⟩ : syracuseStep 1060703 = 1591055) B1591055
theorem B1060715 : Blo 706319 1060715 := bstep (se 1 (by rfl) ⟨795536, by rfl⟩ : syracuseStep 1060715 = 1591073) B1591073
theorem B1060943 : Blo 706319 1060943 := bstep (se 1 (by rfl) ⟨795707, by rfl⟩ : syracuseStep 1060943 = 1591415) B1591415
theorem B798799 : Blo 706319 798799 := bstep (se 1 (by rfl) ⟨599099, by rfl⟩ : syracuseStep 798799 = 1198199) B1198199
theorem B1061063 : Blo 706319 1061063 := bstep (se 1 (by rfl) ⟨795797, by rfl⟩ : syracuseStep 1061063 = 1591595) B1591595
theorem B3027287 : Blo 706319 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B1061225 : Blo 706319 1061225 := bstep (se 2 (by rfl) ⟨397959, by rfl⟩ : syracuseStep 1061225 = 795919) B795919
theorem B2011517 : Blo 706319 2011517 := bstep (se 3 (by rfl) ⟨377159, by rfl⟩ : syracuseStep 2011517 = 754319) B754319
theorem B2732413 : Blo 706319 2732413 := bstep (se 3 (by rfl) ⟨512327, by rfl⟩ : syracuseStep 2732413 = 1024655) B1024655
theorem B1192367 : Blo 706319 1192367 := bstep (se 1 (by rfl) ⟨894275, by rfl⟩ : syracuseStep 1192367 = 1788551) B1788551
theorem B1061303 : Blo 706319 1061303 := bstep (se 1 (by rfl) ⟨795977, by rfl⟩ : syracuseStep 1061303 = 1591955) B1591955
theorem B1061339 : Blo 706319 1061339 := bstep (se 1 (by rfl) ⟨796004, by rfl⟩ : syracuseStep 1061339 = 1592009) B1592009
theorem B2044379 : Blo 706319 2044379 := bstep (se 1 (by rfl) ⟨1533284, by rfl⟩ : syracuseStep 2044379 = 3066569) B3066569
theorem B27669059 : Blo 706319 27669059 := bstep (se 1 (by rfl) ⟨20751794, by rfl⟩ : syracuseStep 27669059 = 41503589) B41503589
theorem B1192799 : Blo 706319 1192799 := bstep (se 1 (by rfl) ⟨894599, by rfl⟩ : syracuseStep 1192799 = 1789199) B1789199
theorem B4043627 : Blo 706319 4043627 := bstep (se 1 (by rfl) ⟨3032720, by rfl⟩ : syracuseStep 4043627 = 6065441) B6065441
theorem B1061807 : Blo 706319 1061807 := bstep (se 1 (by rfl) ⟨796355, by rfl⟩ : syracuseStep 1061807 = 1592711) B1592711
theorem B3027887 : Blo 706319 3027887 := bstep (se 1 (by rfl) ⟨2270915, by rfl⟩ : syracuseStep 3027887 = 4541831) B4541831
theorem B1455067 : Blo 706319 1455067 := bstep (se 1 (by rfl) ⟨1091300, by rfl⟩ : syracuseStep 1455067 = 2182601) B2182601
theorem B1061897 : Blo 706319 1061897 := bstep (se 2 (by rfl) ⟨398211, by rfl⟩ : syracuseStep 1061897 = 796423) B796423
theorem B1061927 : Blo 706319 1061927 := bstep (se 1 (by rfl) ⟨796445, by rfl⟩ : syracuseStep 1061927 = 1592891) B1592891
theorem B1062011 : Blo 706319 1062011 := bstep (se 1 (by rfl) ⟨796508, by rfl⟩ : syracuseStep 1062011 = 1593017) B1593017
theorem B25801877 : Blo 706319 25801877 := bstep (se 6 (by rfl) ⟨604731, by rfl⟩ : syracuseStep 25801877 = 1209463) B1209463
theorem B9090265 : Blo 706319 9090265 := bstep (se 2 (by rfl) ⟨3408849, by rfl⟩ : syracuseStep 9090265 = 6817699) B6817699
theorem B1062137 : Blo 706319 1062137 := bstep (se 2 (by rfl) ⟨398301, by rfl⟩ : syracuseStep 1062137 = 796603) B796603
theorem B1062239 : Blo 706319 1062239 := bstep (se 1 (by rfl) ⟨796679, by rfl⟩ : syracuseStep 1062239 = 1593359) B1593359
theorem B1062251 : Blo 706319 1062251 := bstep (se 1 (by rfl) ⟨796688, by rfl⟩ : syracuseStep 1062251 = 1593377) B1593377
theorem B1193359 : Blo 706319 1193359 := bstep (se 1 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 1193359 = 1790039) B1790039
theorem B2274875 : Blo 706319 2274875 := bstep (se 1 (by rfl) ⟨1706156, by rfl⟩ : syracuseStep 2274875 = 3412313) B3412313
theorem B1062479 : Blo 706319 1062479 := bstep (se 1 (by rfl) ⟨796859, by rfl⟩ : syracuseStep 1062479 = 1593719) B1593719
theorem B18200213 : Blo 706319 18200213 := bstep (se 6 (by rfl) ⟨426567, by rfl⟩ : syracuseStep 18200213 = 853135) B853135
theorem B15513281 : Blo 706319 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B1062599 : Blo 706319 1062599 := bstep (se 1 (by rfl) ⟨796949, by rfl⟩ : syracuseStep 1062599 = 1593899) B1593899
theorem B11646713 : Blo 706319 11646713 := bstep (se 2 (by rfl) ⟨4367517, by rfl⟩ : syracuseStep 11646713 = 8735035) B8735035
theorem B1062761 : Blo 706319 1062761 := bstep (se 2 (by rfl) ⟨398535, by rfl⟩ : syracuseStep 1062761 = 797071) B797071
theorem B4044653 : Blo 706319 4044653 := bstep (se 3 (by rfl) ⟨758372, by rfl⟩ : syracuseStep 4044653 = 1516745) B1516745
theorem B1914799 : Blo 706319 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B1062839 : Blo 706319 1062839 := bstep (se 1 (by rfl) ⟨797129, by rfl⟩ : syracuseStep 1062839 = 1594259) B1594259
theorem B1062875 : Blo 706319 1062875 := bstep (se 1 (by rfl) ⟨797156, by rfl⟩ : syracuseStep 1062875 = 1594313) B1594313
theorem B1194041 : Blo 706319 1194041 := bstep (se 2 (by rfl) ⟨447765, by rfl⟩ : syracuseStep 1194041 = 895531) B895531
theorem B17250691 : Blo 706319 17250691 := bstep (se 1 (by rfl) ⟨12938018, by rfl⟩ : syracuseStep 17250691 = 25876037) B25876037
theorem B1063343 : Blo 706319 1063343 := bstep (se 1 (by rfl) ⟨797507, by rfl⟩ : syracuseStep 1063343 = 1595015) B1595015
theorem B1063433 : Blo 706319 1063433 := bstep (se 2 (by rfl) ⟨398787, by rfl⟩ : syracuseStep 1063433 = 797575) B797575
theorem B1063463 : Blo 706319 1063463 := bstep (se 1 (by rfl) ⟨797597, by rfl⟩ : syracuseStep 1063463 = 1595195) B1595195
theorem B1063547 : Blo 706319 1063547 := bstep (se 1 (by rfl) ⟨797660, by rfl⟩ : syracuseStep 1063547 = 1595321) B1595321
theorem B1194743 : Blo 706319 1194743 := bstep (se 1 (by rfl) ⟨896057, by rfl⟩ : syracuseStep 1194743 = 1792115) B1792115
theorem B1063673 : Blo 706319 1063673 := bstep (se 2 (by rfl) ⟨398877, by rfl⟩ : syracuseStep 1063673 = 797755) B797755
theorem B1063775 : Blo 706319 1063775 := bstep (se 1 (by rfl) ⟨797831, by rfl⟩ : syracuseStep 1063775 = 1595663) B1595663
theorem B1063787 : Blo 706319 1063787 := bstep (se 1 (by rfl) ⟨797840, by rfl⟩ : syracuseStep 1063787 = 1595681) B1595681
theorem B1195087 : Blo 706319 1195087 := bstep (se 1 (by rfl) ⟨896315, by rfl⟩ : syracuseStep 1195087 = 1792631) B1792631
theorem B1064015 : Blo 706319 1064015 := bstep (se 1 (by rfl) ⟨798011, by rfl⟩ : syracuseStep 1064015 = 1596023) B1596023
theorem B1064135 : Blo 706319 1064135 := bstep (se 1 (by rfl) ⟨798101, by rfl⟩ : syracuseStep 1064135 = 1596203) B1596203
theorem B1195337 : Blo 706319 1195337 := bstep (se 2 (by rfl) ⟨448251, by rfl⟩ : syracuseStep 1195337 = 896503) B896503
theorem B1064297 : Blo 706319 1064297 := bstep (se 2 (by rfl) ⟨399111, by rfl⟩ : syracuseStep 1064297 = 798223) B798223
theorem B1064375 : Blo 706319 1064375 := bstep (se 1 (by rfl) ⟨798281, by rfl⟩ : syracuseStep 1064375 = 1596563) B1596563
theorem B1064411 : Blo 706319 1064411 := bstep (se 1 (by rfl) ⟨798308, by rfl⟩ : syracuseStep 1064411 = 1596617) B1596617
theorem B2866747 : Blo 706319 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B1195769 : Blo 706319 1195769 := bstep (se 2 (by rfl) ⟨448413, by rfl⟩ : syracuseStep 1195769 = 896827) B896827
theorem B13811471 : Blo 706319 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B1195951 : Blo 706319 1195951 := bstep (se 1 (by rfl) ⟨896963, by rfl⟩ : syracuseStep 1195951 = 1793927) B1793927
theorem B1064879 : Blo 706319 1064879 := bstep (se 1 (by rfl) ⟨798659, by rfl⟩ : syracuseStep 1064879 = 1597319) B1597319
theorem B10239929 : Blo 706319 10239929 := bstep (se 2 (by rfl) ⟨3839973, by rfl⟩ : syracuseStep 10239929 = 7679947) B7679947
theorem B1589255 : Blo 706319 1589255 := bstep (se 1 (by rfl) ⟨1191941, by rfl⟩ : syracuseStep 1589255 = 2383883) B2383883
theorem B1196039 : Blo 706319 1196039 := bstep (se 1 (by rfl) ⟨897029, by rfl⟩ : syracuseStep 1196039 = 1794059) B1794059
theorem B1064969 : Blo 706319 1064969 := bstep (se 2 (by rfl) ⟨399363, by rfl⟩ : syracuseStep 1064969 = 798727) B798727
theorem B1064999 : Blo 706319 1064999 := bstep (se 1 (by rfl) ⟨798749, by rfl⟩ : syracuseStep 1064999 = 1597499) B1597499
theorem B1589327 : Blo 706319 1589327 := bstep (se 1 (by rfl) ⟨1191995, by rfl⟩ : syracuseStep 1589327 = 2383991) B2383991
theorem B1065083 : Blo 706319 1065083 := bstep (se 1 (by rfl) ⟨798812, by rfl⟩ : syracuseStep 1065083 = 1597625) B1597625
theorem B2867395 : Blo 706319 2867395 := bstep (se 1 (by rfl) ⟨2150546, by rfl⟩ : syracuseStep 2867395 = 4301093) B4301093
theorem B1065209 : Blo 706319 1065209 := bstep (se 2 (by rfl) ⟨399453, by rfl⟩ : syracuseStep 1065209 = 798907) B798907
theorem B1196383 : Blo 706319 1196383 := bstep (se 1 (by rfl) ⟨897287, by rfl⟩ : syracuseStep 1196383 = 1794575) B1794575
theorem B1065311 : Blo 706319 1065311 := bstep (se 1 (by rfl) ⟨798983, by rfl⟩ : syracuseStep 1065311 = 1597967) B1597967
theorem B2867561 : Blo 706319 2867561 := bstep (se 2 (by rfl) ⟨1075335, by rfl⟩ : syracuseStep 2867561 = 2150671) B2150671
theorem B1065323 : Blo 706319 1065323 := bstep (se 1 (by rfl) ⟨798992, by rfl⟩ : syracuseStep 1065323 = 1597985) B1597985
theorem B2015617 : Blo 706319 2015617 := bstep (se 2 (by rfl) ⟨755856, by rfl⟩ : syracuseStep 2015617 = 1511713) B1511713
theorem B1196471 : Blo 706319 1196471 := bstep (se 1 (by rfl) ⟨897353, by rfl⟩ : syracuseStep 1196471 = 1794707) B1794707
theorem B12894673 : Blo 706319 12894673 := bstep (se 2 (by rfl) ⟨4835502, by rfl⟩ : syracuseStep 12894673 = 9671005) B9671005
theorem B1589723 : Blo 706319 1589723 := bstep (se 1 (by rfl) ⟨1192292, by rfl⟩ : syracuseStep 1589723 = 2384585) B2384585
theorem B3031577 : Blo 706319 3031577 := bstep (se 2 (by rfl) ⟨1136841, by rfl⟩ : syracuseStep 3031577 = 2273683) B2273683
theorem B2015867 : Blo 706319 2015867 := bstep (se 1 (by rfl) ⟨1511900, by rfl⟩ : syracuseStep 2015867 = 3023801) B3023801
theorem B5522093 : Blo 706319 5522093 := bstep (se 3 (by rfl) ⟨1035392, by rfl⟩ : syracuseStep 5522093 = 2070785) B2070785
theorem B1590191 : Blo 706319 1590191 := bstep (se 1 (by rfl) ⟨1192643, by rfl⟩ : syracuseStep 1590191 = 2385287) B2385287
theorem B1197065 : Blo 706319 1197065 := bstep (se 2 (by rfl) ⟨448899, by rfl⟩ : syracuseStep 1197065 = 897799) B897799
theorem B1590443 : Blo 706319 1590443 := bstep (se 1 (by rfl) ⟨1192832, by rfl⟩ : syracuseStep 1590443 = 2385665) B2385665
theorem B9684139 : Blo 706319 9684139 := bstep (se 1 (by rfl) ⟨7263104, by rfl⟩ : syracuseStep 9684139 = 14526209) B14526209
theorem B1197227 : Blo 706319 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B3589595 : Blo 706319 3589595 := bstep (se 1 (by rfl) ⟨2692196, by rfl⟩ : syracuseStep 3589595 = 5384393) B5384393
theorem B1197625 : Blo 706319 1197625 := bstep (se 2 (by rfl) ⟨449109, by rfl⟩ : syracuseStep 1197625 = 898219) B898219
theorem B1918603 : Blo 706319 1918603 := bstep (se 1 (by rfl) ⟨1438952, by rfl⟩ : syracuseStep 1918603 = 2877905) B2877905
theorem B1590983 : Blo 706319 1590983 := bstep (se 1 (by rfl) ⟨1193237, by rfl⟩ : syracuseStep 1590983 = 2386475) B2386475
theorem B1197767 : Blo 706319 1197767 := bstep (se 1 (by rfl) ⟨898325, by rfl⟩ : syracuseStep 1197767 = 1796651) B1796651
theorem B4835065 : Blo 706319 4835065 := bstep (se 2 (by rfl) ⟨1813149, by rfl⟩ : syracuseStep 4835065 = 3626299) B3626299
theorem B706343 : Blo 706319 706343 := bstep (se 1 (by rfl) ⟨529757, by rfl⟩ : syracuseStep 706343 = 1059515) B1059515
theorem B706383 : Blo 706319 706383 := bstep (se 1 (by rfl) ⟨529787, by rfl⟩ : syracuseStep 706383 = 1059575) B1059575
theorem B706399 : Blo 706319 706399 := bstep (se 1 (by rfl) ⟨529799, by rfl⟩ : syracuseStep 706399 = 1059599) B1059599
theorem B1197929 : Blo 706319 1197929 := bstep (se 2 (by rfl) ⟨449223, by rfl⟩ : syracuseStep 1197929 = 898447) B898447
theorem B706427 : Blo 706319 706427 := bstep (se 1 (by rfl) ⟨529820, by rfl⟩ : syracuseStep 706427 = 1059641) B1059641
theorem B706479 : Blo 706319 706479 := bstep (se 1 (by rfl) ⟨529859, by rfl⟩ : syracuseStep 706479 = 1059719) B1059719
theorem B3590081 : Blo 706319 3590081 := bstep (se 2 (by rfl) ⟨1346280, by rfl⟩ : syracuseStep 3590081 = 2692561) B2692561
theorem B706503 : Blo 706319 706503 := bstep (se 1 (by rfl) ⟨529877, by rfl⟩ : syracuseStep 706503 = 1059755) B1059755
theorem B706523 : Blo 706319 706523 := bstep (se 1 (by rfl) ⟨529892, by rfl⟩ : syracuseStep 706523 = 1059785) B1059785
theorem B706599 : Blo 706319 706599 := bstep (se 1 (by rfl) ⟨529949, by rfl⟩ : syracuseStep 706599 = 1059899) B1059899
theorem B706639 : Blo 706319 706639 := bstep (se 1 (by rfl) ⟨529979, by rfl⟩ : syracuseStep 706639 = 1059959) B1059959
theorem B706655 : Blo 706319 706655 := bstep (se 1 (by rfl) ⟨529991, by rfl⟩ : syracuseStep 706655 = 1059983) B1059983
theorem B706683 : Blo 706319 706683 := bstep (se 1 (by rfl) ⟨530012, by rfl⟩ : syracuseStep 706683 = 1060025) B1060025
theorem B706735 : Blo 706319 706735 := bstep (se 1 (by rfl) ⟨530051, by rfl⟩ : syracuseStep 706735 = 1060103) B1060103
theorem B706759 : Blo 706319 706759 := bstep (se 1 (by rfl) ⟨530069, by rfl⟩ : syracuseStep 706759 = 1060139) B1060139
theorem B706779 : Blo 706319 706779 := bstep (se 1 (by rfl) ⟨530084, by rfl⟩ : syracuseStep 706779 = 1060169) B1060169
theorem B1198327 : Blo 706319 1198327 := bstep (se 1 (by rfl) ⟨898745, by rfl⟩ : syracuseStep 1198327 = 1797491) B1797491
theorem B706855 : Blo 706319 706855 := bstep (se 1 (by rfl) ⟨530141, by rfl⟩ : syracuseStep 706855 = 1060283) B1060283
theorem B706895 : Blo 706319 706895 := bstep (se 1 (by rfl) ⟨530171, by rfl⟩ : syracuseStep 706895 = 1060343) B1060343
theorem B706911 : Blo 706319 706911 := bstep (se 1 (by rfl) ⟨530183, by rfl⟩ : syracuseStep 706911 = 1060367) B1060367
theorem B706939 : Blo 706319 706939 := bstep (se 1 (by rfl) ⟨530204, by rfl⟩ : syracuseStep 706939 = 1060409) B1060409
theorem B706991 : Blo 706319 706991 := bstep (se 1 (by rfl) ⟨530243, by rfl⟩ : syracuseStep 706991 = 1060487) B1060487
theorem B1198523 : Blo 706319 1198523 := bstep (se 1 (by rfl) ⟨898892, by rfl⟩ : syracuseStep 1198523 = 1797785) B1797785
theorem B707015 : Blo 706319 707015 := bstep (se 1 (by rfl) ⟨530261, by rfl⟩ : syracuseStep 707015 = 1060523) B1060523
theorem B707035 : Blo 706319 707035 := bstep (se 1 (by rfl) ⟨530276, by rfl⟩ : syracuseStep 707035 = 1060553) B1060553
theorem B707111 : Blo 706319 707111 := bstep (se 1 (by rfl) ⟨530333, by rfl⟩ : syracuseStep 707111 = 1060667) B1060667
theorem B1591847 : Blo 706319 1591847 := bstep (se 1 (by rfl) ⟨1193885, by rfl⟩ : syracuseStep 1591847 = 2387771) B2387771
theorem B1198631 : Blo 706319 1198631 := bstep (se 1 (by rfl) ⟨898973, by rfl⟩ : syracuseStep 1198631 = 1797947) B1797947
theorem B707151 : Blo 706319 707151 := bstep (se 1 (by rfl) ⟨530363, by rfl⟩ : syracuseStep 707151 = 1060727) B1060727
theorem B707167 : Blo 706319 707167 := bstep (se 1 (by rfl) ⟨530375, by rfl⟩ : syracuseStep 707167 = 1060751) B1060751
theorem B707195 : Blo 706319 707195 := bstep (se 1 (by rfl) ⟨530396, by rfl⟩ : syracuseStep 707195 = 1060793) B1060793
theorem B707247 : Blo 706319 707247 := bstep (se 1 (by rfl) ⟨530435, by rfl⟩ : syracuseStep 707247 = 1060871) B1060871
theorem B707271 : Blo 706319 707271 := bstep (se 1 (by rfl) ⟨530453, by rfl⟩ : syracuseStep 707271 = 1060907) B1060907
theorem B707291 : Blo 706319 707291 := bstep (se 1 (by rfl) ⟨530468, by rfl⟩ : syracuseStep 707291 = 1060937) B1060937
theorem B707367 : Blo 706319 707367 := bstep (se 1 (by rfl) ⟨530525, by rfl⟩ : syracuseStep 707367 = 1061051) B1061051
theorem B707407 : Blo 706319 707407 := bstep (se 1 (by rfl) ⟨530555, by rfl⟩ : syracuseStep 707407 = 1061111) B1061111
theorem B707423 : Blo 706319 707423 := bstep (se 1 (by rfl) ⟨530567, by rfl⟩ : syracuseStep 707423 = 1061135) B1061135
theorem B1592171 : Blo 706319 1592171 := bstep (se 1 (by rfl) ⟨1194128, by rfl⟩ : syracuseStep 1592171 = 2388257) B2388257
theorem B4541291 : Blo 706319 4541291 := bstep (se 1 (by rfl) ⟨3405968, by rfl⟩ : syracuseStep 4541291 = 6811937) B6811937
theorem B707451 : Blo 706319 707451 := bstep (se 1 (by rfl) ⟨530588, by rfl⟩ : syracuseStep 707451 = 1061177) B1061177
theorem B1592225 : Blo 706319 1592225 := bstep (se 2 (by rfl) ⟨597084, by rfl⟩ : syracuseStep 1592225 = 1194169) B1194169
theorem B707503 : Blo 706319 707503 := bstep (se 1 (by rfl) ⟨530627, by rfl⟩ : syracuseStep 707503 = 1061255) B1061255
theorem B1362863 : Blo 706319 1362863 := bstep (se 1 (by rfl) ⟨1022147, by rfl⟩ : syracuseStep 1362863 = 2044295) B2044295
theorem B6048695 : Blo 706319 6048695 := bstep (se 1 (by rfl) ⟨4536521, by rfl⟩ : syracuseStep 6048695 = 9073043) B9073043
theorem B707527 : Blo 706319 707527 := bstep (se 1 (by rfl) ⟨530645, by rfl⟩ : syracuseStep 707527 = 1061291) B1061291
theorem B707547 : Blo 706319 707547 := bstep (se 1 (by rfl) ⟨530660, by rfl⟩ : syracuseStep 707547 = 1061321) B1061321
theorem B707623 : Blo 706319 707623 := bstep (se 1 (by rfl) ⟨530717, by rfl⟩ : syracuseStep 707623 = 1061435) B1061435
theorem B707663 : Blo 706319 707663 := bstep (se 1 (by rfl) ⟨530747, by rfl⟩ : syracuseStep 707663 = 1061495) B1061495
theorem B707679 : Blo 706319 707679 := bstep (se 1 (by rfl) ⟨530759, by rfl⟩ : syracuseStep 707679 = 1061519) B1061519
theorem B707707 : Blo 706319 707707 := bstep (se 1 (by rfl) ⟨530780, by rfl⟩ : syracuseStep 707707 = 1061561) B1061561
theorem B707759 : Blo 706319 707759 := bstep (se 1 (by rfl) ⟨530819, by rfl⟩ : syracuseStep 707759 = 1061639) B1061639
theorem B707783 : Blo 706319 707783 := bstep (se 1 (by rfl) ⟨530837, by rfl⟩ : syracuseStep 707783 = 1061675) B1061675
theorem B707803 : Blo 706319 707803 := bstep (se 1 (by rfl) ⟨530852, by rfl⟩ : syracuseStep 707803 = 1061705) B1061705
theorem B1592567 : Blo 706319 1592567 := bstep (se 1 (by rfl) ⟨1194425, by rfl⟩ : syracuseStep 1592567 = 2388851) B2388851
theorem B707879 : Blo 706319 707879 := bstep (se 1 (by rfl) ⟨530909, by rfl⟩ : syracuseStep 707879 = 1061819) B1061819
theorem B707919 : Blo 706319 707919 := bstep (se 1 (by rfl) ⟨530939, by rfl⟩ : syracuseStep 707919 = 1061879) B1061879
theorem B707935 : Blo 706319 707935 := bstep (se 1 (by rfl) ⟨530951, by rfl⟩ : syracuseStep 707935 = 1061903) B1061903
theorem B707963 : Blo 706319 707963 := bstep (se 1 (by rfl) ⟨530972, by rfl⟩ : syracuseStep 707963 = 1061945) B1061945
theorem B708015 : Blo 706319 708015 := bstep (se 1 (by rfl) ⟨531011, by rfl⟩ : syracuseStep 708015 = 1062023) B1062023
theorem B708039 : Blo 706319 708039 := bstep (se 1 (by rfl) ⟨531029, by rfl⟩ : syracuseStep 708039 = 1062059) B1062059
theorem B708059 : Blo 706319 708059 := bstep (se 1 (by rfl) ⟨531044, by rfl⟩ : syracuseStep 708059 = 1062089) B1062089
theorem B708135 : Blo 706319 708135 := bstep (se 1 (by rfl) ⟨531101, by rfl⟩ : syracuseStep 708135 = 1062203) B1062203
theorem B708175 : Blo 706319 708175 := bstep (se 1 (by rfl) ⟨531131, by rfl⟩ : syracuseStep 708175 = 1062263) B1062263
theorem B708191 : Blo 706319 708191 := bstep (se 1 (by rfl) ⟨531143, by rfl⟩ : syracuseStep 708191 = 1062287) B1062287
theorem B708219 : Blo 706319 708219 := bstep (se 1 (by rfl) ⟨531164, by rfl⟩ : syracuseStep 708219 = 1062329) B1062329
theorem B708271 : Blo 706319 708271 := bstep (se 1 (by rfl) ⟨531203, by rfl⟩ : syracuseStep 708271 = 1062407) B1062407
theorem B708295 : Blo 706319 708295 := bstep (se 1 (by rfl) ⟨531221, by rfl⟩ : syracuseStep 708295 = 1062443) B1062443
theorem B708315 : Blo 706319 708315 := bstep (se 1 (by rfl) ⟨531236, by rfl⟩ : syracuseStep 708315 = 1062473) B1062473
theorem B708391 : Blo 706319 708391 := bstep (se 1 (by rfl) ⟨531293, by rfl⟩ : syracuseStep 708391 = 1062587) B1062587
theorem B1593161 : Blo 706319 1593161 := bstep (se 2 (by rfl) ⟨597435, by rfl⟩ : syracuseStep 1593161 = 1194871) B1194871
theorem B708431 : Blo 706319 708431 := bstep (se 1 (by rfl) ⟨531323, by rfl⟩ : syracuseStep 708431 = 1062647) B1062647
theorem B708447 : Blo 706319 708447 := bstep (se 1 (by rfl) ⟨531335, by rfl⟩ : syracuseStep 708447 = 1062671) B1062671
theorem B4542317 : Blo 706319 4542317 := bstep (se 3 (by rfl) ⟨851684, by rfl⟩ : syracuseStep 4542317 = 1703369) B1703369
theorem B5459831 : Blo 706319 5459831 := bstep (se 1 (by rfl) ⟨4094873, by rfl⟩ : syracuseStep 5459831 = 8189747) B8189747
theorem B708475 : Blo 706319 708475 := bstep (se 1 (by rfl) ⟨531356, by rfl⟩ : syracuseStep 708475 = 1062713) B1062713
theorem B708527 : Blo 706319 708527 := bstep (se 1 (by rfl) ⟨531395, by rfl⟩ : syracuseStep 708527 = 1062791) B1062791
theorem B708551 : Blo 706319 708551 := bstep (se 1 (by rfl) ⟨531413, by rfl⟩ : syracuseStep 708551 = 1062827) B1062827
theorem B708571 : Blo 706319 708571 := bstep (se 1 (by rfl) ⟨531428, by rfl⟩ : syracuseStep 708571 = 1062857) B1062857
theorem B10899461 : Blo 706319 10899461 := bstep (se 4 (by rfl) ⟨1021824, by rfl⟩ : syracuseStep 10899461 = 2043649) B2043649
theorem B708647 : Blo 706319 708647 := bstep (se 1 (by rfl) ⟨531485, by rfl⟩ : syracuseStep 708647 = 1062971) B1062971
theorem B1790009 : Blo 706319 1790009 := bstep (se 2 (by rfl) ⟨671253, by rfl⟩ : syracuseStep 1790009 = 1342507) B1342507
theorem B708687 : Blo 706319 708687 := bstep (se 1 (by rfl) ⟨531515, by rfl⟩ : syracuseStep 708687 = 1063031) B1063031
theorem B708703 : Blo 706319 708703 := bstep (se 1 (by rfl) ⟨531527, by rfl⟩ : syracuseStep 708703 = 1063055) B1063055
theorem B708731 : Blo 706319 708731 := bstep (se 1 (by rfl) ⟨531548, by rfl⟩ : syracuseStep 708731 = 1063097) B1063097
theorem B3592349 : Blo 706319 3592349 := bstep (se 3 (by rfl) ⟨673565, by rfl⟩ : syracuseStep 3592349 = 1347131) B1347131
theorem B708783 : Blo 706319 708783 := bstep (se 1 (by rfl) ⟨531587, by rfl⟩ : syracuseStep 708783 = 1063175) B1063175
theorem B708807 : Blo 706319 708807 := bstep (se 1 (by rfl) ⟨531605, by rfl⟩ : syracuseStep 708807 = 1063211) B1063211
theorem B708827 : Blo 706319 708827 := bstep (se 1 (by rfl) ⟨531620, by rfl⟩ : syracuseStep 708827 = 1063241) B1063241
theorem B708903 : Blo 706319 708903 := bstep (se 1 (by rfl) ⟨531677, by rfl⟩ : syracuseStep 708903 = 1063355) B1063355
theorem B14373179 : Blo 706319 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B708943 : Blo 706319 708943 := bstep (se 1 (by rfl) ⟨531707, by rfl⟩ : syracuseStep 708943 = 1063415) B1063415
theorem B708959 : Blo 706319 708959 := bstep (se 1 (by rfl) ⟨531719, by rfl⟩ : syracuseStep 708959 = 1063439) B1063439
theorem B708987 : Blo 706319 708987 := bstep (se 1 (by rfl) ⟨531740, by rfl⟩ : syracuseStep 708987 = 1063481) B1063481
theorem B709039 : Blo 706319 709039 := bstep (se 1 (by rfl) ⟨531779, by rfl⟩ : syracuseStep 709039 = 1063559) B1063559
theorem B709063 : Blo 706319 709063 := bstep (se 1 (by rfl) ⟨531797, by rfl⟩ : syracuseStep 709063 = 1063595) B1063595
theorem B709083 : Blo 706319 709083 := bstep (se 1 (by rfl) ⟨531812, by rfl⟩ : syracuseStep 709083 = 1063625) B1063625
theorem B709159 : Blo 706319 709159 := bstep (se 1 (by rfl) ⟨531869, by rfl⟩ : syracuseStep 709159 = 1063739) B1063739
theorem B709199 : Blo 706319 709199 := bstep (se 1 (by rfl) ⟨531899, by rfl⟩ : syracuseStep 709199 = 1063799) B1063799
theorem B709215 : Blo 706319 709215 := bstep (se 1 (by rfl) ⟨531911, by rfl⟩ : syracuseStep 709215 = 1063823) B1063823
theorem B1593953 : Blo 706319 1593953 := bstep (se 2 (by rfl) ⟨597732, by rfl⟩ : syracuseStep 1593953 = 1195465) B1195465
theorem B11457125 : Blo 706319 11457125 := bstep (se 4 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 11457125 = 2148211) B2148211
theorem B709243 : Blo 706319 709243 := bstep (se 1 (by rfl) ⟨531932, by rfl⟩ : syracuseStep 709243 = 1063865) B1063865
theorem B709295 : Blo 706319 709295 := bstep (se 1 (by rfl) ⟨531971, by rfl⟩ : syracuseStep 709295 = 1063943) B1063943
theorem B709319 : Blo 706319 709319 := bstep (se 1 (by rfl) ⟨531989, by rfl⟩ : syracuseStep 709319 = 1063979) B1063979
theorem B709339 : Blo 706319 709339 := bstep (se 1 (by rfl) ⟨532004, by rfl⟩ : syracuseStep 709339 = 1064009) B1064009
theorem B709415 : Blo 706319 709415 := bstep (se 1 (by rfl) ⟨532061, by rfl⟩ : syracuseStep 709415 = 1064123) B1064123
theorem B709455 : Blo 706319 709455 := bstep (se 1 (by rfl) ⟨532091, by rfl⟩ : syracuseStep 709455 = 1064183) B1064183
theorem B709471 : Blo 706319 709471 := bstep (se 1 (by rfl) ⟨532103, by rfl⟩ : syracuseStep 709471 = 1064207) B1064207
theorem B709499 : Blo 706319 709499 := bstep (se 1 (by rfl) ⟨532124, by rfl⟩ : syracuseStep 709499 = 1064249) B1064249
theorem B709551 : Blo 706319 709551 := bstep (se 1 (by rfl) ⟨532163, by rfl⟩ : syracuseStep 709551 = 1064327) B1064327
theorem B1594295 : Blo 706319 1594295 := bstep (se 1 (by rfl) ⟨1195721, by rfl⟩ : syracuseStep 1594295 = 2391443) B2391443
theorem B709575 : Blo 706319 709575 := bstep (se 1 (by rfl) ⟨532181, by rfl⟩ : syracuseStep 709575 = 1064363) B1064363
theorem B709595 : Blo 706319 709595 := bstep (se 1 (by rfl) ⟨532196, by rfl⟩ : syracuseStep 709595 = 1064393) B1064393
theorem B5100563 : Blo 706319 5100563 := bstep (se 1 (by rfl) ⟨3825422, by rfl⟩ : syracuseStep 5100563 = 7650845) B7650845
theorem B709671 : Blo 706319 709671 := bstep (se 1 (by rfl) ⟨532253, by rfl⟩ : syracuseStep 709671 = 1064507) B1064507
theorem B709711 : Blo 706319 709711 := bstep (se 1 (by rfl) ⟨532283, by rfl⟩ : syracuseStep 709711 = 1064567) B1064567
theorem B709727 : Blo 706319 709727 := bstep (se 1 (by rfl) ⟨532295, by rfl⟩ : syracuseStep 709727 = 1064591) B1064591
theorem B709755 : Blo 706319 709755 := bstep (se 1 (by rfl) ⟨532316, by rfl⟩ : syracuseStep 709755 = 1064633) B1064633
theorem B709807 : Blo 706319 709807 := bstep (se 1 (by rfl) ⟨532355, by rfl⟩ : syracuseStep 709807 = 1064711) B1064711
theorem B709831 : Blo 706319 709831 := bstep (se 1 (by rfl) ⟨532373, by rfl⟩ : syracuseStep 709831 = 1064747) B1064747
theorem B709851 : Blo 706319 709851 := bstep (se 1 (by rfl) ⟨532388, by rfl⟩ : syracuseStep 709851 = 1064777) B1064777
theorem B709927 : Blo 706319 709927 := bstep (se 1 (by rfl) ⟨532445, by rfl⟩ : syracuseStep 709927 = 1064891) B1064891
theorem B709967 : Blo 706319 709967 := bstep (se 1 (by rfl) ⟨532475, by rfl⟩ : syracuseStep 709967 = 1064951) B1064951
theorem B709983 : Blo 706319 709983 := bstep (se 1 (by rfl) ⟨532487, by rfl⟩ : syracuseStep 709983 = 1064975) B1064975
theorem B710011 : Blo 706319 710011 := bstep (se 1 (by rfl) ⟨532508, by rfl⟩ : syracuseStep 710011 = 1065017) B1065017
theorem B3593645 : Blo 706319 3593645 := bstep (se 3 (by rfl) ⟨673808, by rfl⟩ : syracuseStep 3593645 = 1347617) B1347617
theorem B710063 : Blo 706319 710063 := bstep (se 1 (by rfl) ⟨532547, by rfl⟩ : syracuseStep 710063 = 1065095) B1065095
theorem B710087 : Blo 706319 710087 := bstep (se 1 (by rfl) ⟨532565, by rfl⟩ : syracuseStep 710087 = 1065131) B1065131
theorem B710107 : Blo 706319 710107 := bstep (se 1 (by rfl) ⟨532580, by rfl⟩ : syracuseStep 710107 = 1065161) B1065161
theorem B3233267 : Blo 706319 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B1791497 : Blo 706319 1791497 := bstep (se 2 (by rfl) ⟨671811, by rfl⟩ : syracuseStep 1791497 = 1343623) B1343623
theorem B1594889 : Blo 706319 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B710183 : Blo 706319 710183 := bstep (se 1 (by rfl) ⟨532637, by rfl⟩ : syracuseStep 710183 = 1065275) B1065275
theorem B1136207 : Blo 706319 1136207 := bstep (se 1 (by rfl) ⟨852155, by rfl⟩ : syracuseStep 1136207 = 1704311) B1704311
theorem B710223 : Blo 706319 710223 := bstep (se 1 (by rfl) ⟨532667, by rfl⟩ : syracuseStep 710223 = 1065335) B1065335
theorem B710239 : Blo 706319 710239 := bstep (se 1 (by rfl) ⟨532679, by rfl⟩ : syracuseStep 710239 = 1065359) B1065359
theorem B710267 : Blo 706319 710267 := bstep (se 1 (by rfl) ⟨532700, by rfl⟩ : syracuseStep 710267 = 1065401) B1065401
theorem B710319 : Blo 706319 710319 := bstep (se 1 (by rfl) ⟨532739, by rfl⟩ : syracuseStep 710319 = 1065479) B1065479
theorem B4085437 : Blo 706319 4085437 := bstep (se 3 (by rfl) ⟨766019, by rfl⟩ : syracuseStep 4085437 = 1532039) B1532039
theorem B1595231 : Blo 706319 1595231 := bstep (se 1 (by rfl) ⟨1196423, by rfl⟩ : syracuseStep 1595231 = 2392847) B2392847
theorem B1595411 : Blo 706319 1595411 := bstep (se 1 (by rfl) ⟨1196558, by rfl⟩ : syracuseStep 1595411 = 2393117) B2393117
theorem B907463 : Blo 706319 907463 := bstep (se 1 (by rfl) ⟨680597, by rfl⟩ : syracuseStep 907463 = 1361195) B1361195
theorem B1595753 : Blo 706319 1595753 := bstep (se 2 (by rfl) ⟨598407, by rfl⟩ : syracuseStep 1595753 = 1196815) B1196815
theorem B1137001 : Blo 706319 1137001 := bstep (se 2 (by rfl) ⟨426375, by rfl⟩ : syracuseStep 1137001 = 852751) B852751
theorem B1366651 : Blo 706319 1366651 := bstep (se 1 (by rfl) ⟨1024988, by rfl⟩ : syracuseStep 1366651 = 2049977) B2049977
theorem B1792651 : Blo 706319 1792651 := bstep (se 1 (by rfl) ⟨1344488, by rfl⟩ : syracuseStep 1792651 = 2688977) B2688977
theorem B1792955 : Blo 706319 1792955 := bstep (se 1 (by rfl) ⟨1344716, by rfl⟩ : syracuseStep 1792955 = 2689433) B2689433
theorem B1596347 : Blo 706319 1596347 := bstep (se 1 (by rfl) ⟨1197260, by rfl⟩ : syracuseStep 1596347 = 2394521) B2394521
theorem B3595265 : Blo 706319 3595265 := bstep (se 2 (by rfl) ⟨1348224, by rfl⟩ : syracuseStep 3595265 = 2696449) B2696449
theorem B1596473 : Blo 706319 1596473 := bstep (se 2 (by rfl) ⟨598677, by rfl⟩ : syracuseStep 1596473 = 1197355) B1197355
theorem B1006715 : Blo 706319 1006715 := bstep (se 1 (by rfl) ⟨755036, by rfl⟩ : syracuseStep 1006715 = 1510073) B1510073
theorem B1596815 : Blo 706319 1596815 := bstep (se 1 (by rfl) ⟨1197611, by rfl⟩ : syracuseStep 1596815 = 2395223) B2395223
theorem B1793735 : Blo 706319 1793735 := bstep (se 1 (by rfl) ⟨1345301, by rfl⟩ : syracuseStep 1793735 = 2690603) B2690603
theorem B1597139 : Blo 706319 1597139 := bstep (se 1 (by rfl) ⟨1197854, by rfl⟩ : syracuseStep 1597139 = 2395709) B2395709
theorem B1007353 : Blo 706319 1007353 := bstep (se 2 (by rfl) ⟨377757, by rfl⟩ : syracuseStep 1007353 = 755515) B755515
theorem B1793785 : Blo 706319 1793785 := bstep (se 2 (by rfl) ⟨672669, by rfl⟩ : syracuseStep 1793785 = 1345339) B1345339
theorem B4546363 : Blo 706319 4546363 := bstep (se 1 (by rfl) ⟨3409772, by rfl⟩ : syracuseStep 4546363 = 6819545) B6819545
theorem B2875297 : Blo 706319 2875297 := bstep (se 2 (by rfl) ⟨1078236, by rfl⟩ : syracuseStep 2875297 = 2156473) B2156473
theorem B4317299 : Blo 706319 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B8609969 : Blo 706319 8609969 := bstep (se 2 (by rfl) ⟨3228738, by rfl⟩ : syracuseStep 8609969 = 6457477) B6457477
theorem B1433951 : Blo 706319 1433951 := bstep (se 1 (by rfl) ⟨1075463, by rfl⟩ : syracuseStep 1433951 = 2150927) B2150927
theorem B1794433 : Blo 706319 1794433 := bstep (se 2 (by rfl) ⟨672912, by rfl⟩ : syracuseStep 1794433 = 1345825) B1345825
theorem B2384423 : Blo 706319 2384423 := bstep (se 1 (by rfl) ⟨1788317, by rfl⟩ : syracuseStep 2384423 = 3576635) B3576635
theorem B1598075 : Blo 706319 1598075 := bstep (se 1 (by rfl) ⟨1198556, by rfl⟩ : syracuseStep 1598075 = 2397113) B2397113
theorem B2384531 : Blo 706319 2384531 := bstep (se 1 (by rfl) ⟨1788398, by rfl⟩ : syracuseStep 2384531 = 3576797) B3576797
theorem B2876153 : Blo 706319 2876153 := bstep (se 2 (by rfl) ⟨1078557, by rfl⟩ : syracuseStep 2876153 = 2157115) B2157115
theorem B1598201 : Blo 706319 1598201 := bstep (se 2 (by rfl) ⟨599325, by rfl⟩ : syracuseStep 1598201 = 1198651) B1198651
theorem B2384747 : Blo 706319 2384747 := bstep (se 1 (by rfl) ⟨1788560, by rfl⟩ : syracuseStep 2384747 = 3577121) B3577121
theorem B2384801 : Blo 706319 2384801 := bstep (se 2 (by rfl) ⟨894300, by rfl⟩ : syracuseStep 2384801 = 1788601) B1788601
theorem B4023215 : Blo 706319 4023215 := bstep (se 1 (by rfl) ⟨3017411, by rfl⟩ : syracuseStep 4023215 = 6034823) B6034823
theorem B15524783 : Blo 706319 15524783 := bstep (se 1 (by rfl) ⟨11643587, by rfl⟩ : syracuseStep 15524783 = 23287175) B23287175
theorem B1795243 : Blo 706319 1795243 := bstep (se 1 (by rfl) ⟨1346432, by rfl⟩ : syracuseStep 1795243 = 2692865) B2692865
theorem B1795547 : Blo 706319 1795547 := bstep (se 1 (by rfl) ⟨1346660, by rfl⟩ : syracuseStep 1795547 = 2693321) B2693321
theorem B1697267 : Blo 706319 1697267 := bstep (se 1 (by rfl) ⟨1272950, by rfl⟩ : syracuseStep 1697267 = 2545901) B2545901
theorem B2385395 : Blo 706319 2385395 := bstep (se 1 (by rfl) ⟨1789046, by rfl⟩ : syracuseStep 2385395 = 3578093) B3578093
theorem B17655331 : Blo 706319 17655331 := bstep (se 1 (by rfl) ⟨13241498, by rfl⟩ : syracuseStep 17655331 = 26482997) B26482997
theorem B5367383 : Blo 706319 5367383 := bstep (se 1 (by rfl) ⟨4025537, by rfl⟩ : syracuseStep 5367383 = 8051075) B8051075
theorem B11495009 : Blo 706319 11495009 := bstep (se 2 (by rfl) ⟨4310628, by rfl⟩ : syracuseStep 11495009 = 8621257) B8621257
theorem B9070379 : Blo 706319 9070379 := bstep (se 1 (by rfl) ⟨6802784, by rfl⟩ : syracuseStep 9070379 = 13605569) B13605569
theorem B2877371 : Blo 706319 2877371 := bstep (se 1 (by rfl) ⟨2158028, by rfl⟩ : syracuseStep 2877371 = 4316057) B4316057
theorem B2385935 : Blo 706319 2385935 := bstep (se 1 (by rfl) ⟨1789451, by rfl⟩ : syracuseStep 2385935 = 3578903) B3578903
theorem B21751901 : Blo 706319 21751901 := bstep (se 3 (by rfl) ⟨4078481, by rfl⟩ : syracuseStep 21751901 = 8156963) B8156963
theorem B3631675 : Blo 706319 3631675 := bstep (se 1 (by rfl) ⟨2723756, by rfl⟩ : syracuseStep 3631675 = 5447513) B5447513
theorem B2386529 : Blo 706319 2386529 := bstep (se 2 (by rfl) ⟨894948, by rfl⟩ : syracuseStep 2386529 = 1789897) B1789897
theorem B1797025 : Blo 706319 1797025 := bstep (se 2 (by rfl) ⟨673884, by rfl⟩ : syracuseStep 1797025 = 1347769) B1347769
theorem B2682173 : Blo 706319 2682173 := bstep (se 3 (by rfl) ⟨502907, by rfl⟩ : syracuseStep 2682173 = 1005815) B1005815
theorem B2551277 : Blo 706319 2551277 := bstep (se 3 (by rfl) ⟨478364, by rfl⟩ : syracuseStep 2551277 = 956729) B956729
theorem B2682355 : Blo 706319 2682355 := bstep (se 1 (by rfl) ⟨2011766, by rfl⟩ : syracuseStep 2682355 = 4023533) B4023533
theorem B1633991 : Blo 706319 1633991 := bstep (se 1 (by rfl) ⟨1225493, by rfl⟩ : syracuseStep 1633991 = 2450987) B2450987
theorem B1699679 : Blo 706319 1699679 := bstep (se 1 (by rfl) ⟨1274759, by rfl⟩ : syracuseStep 1699679 = 2549519) B2549519
theorem B2584507 : Blo 706319 2584507 := bstep (se 1 (by rfl) ⟨1938380, by rfl⟩ : syracuseStep 2584507 = 3876761) B3876761
theorem B5828561 : Blo 706319 5828561 := bstep (se 2 (by rfl) ⟨2185710, by rfl⟩ : syracuseStep 5828561 = 4371421) B4371421
theorem B2387987 : Blo 706319 2387987 := bstep (se 1 (by rfl) ⟨1790990, by rfl⟩ : syracuseStep 2387987 = 3581981) B3581981
theorem B4026449 : Blo 706319 4026449 := bstep (se 2 (by rfl) ⟨1509918, by rfl⟩ : syracuseStep 4026449 = 3019837) B3019837
theorem B2388311 : Blo 706319 2388311 := bstep (se 1 (by rfl) ⟨1791233, by rfl⟩ : syracuseStep 2388311 = 3582467) B3582467
theorem B4026905 : Blo 706319 4026905 := bstep (se 2 (by rfl) ⟨1510089, by rfl⟩ : syracuseStep 4026905 = 3020179) B3020179
theorem B2683601 : Blo 706319 2683601 := bstep (se 2 (by rfl) ⟨1006350, by rfl⟩ : syracuseStep 2683601 = 2012701) B2012701
theorem B8090441 : Blo 706319 8090441 := bstep (se 2 (by rfl) ⟨3033915, by rfl⟩ : syracuseStep 8090441 = 6067831) B6067831
theorem B6911041 : Blo 706319 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B1537103 : Blo 706319 1537103 := bstep (se 1 (by rfl) ⟨1152827, by rfl⟩ : syracuseStep 1537103 = 2305655) B2305655
theorem B2684285 : Blo 706319 2684285 := bstep (se 3 (by rfl) ⟨503303, by rfl⟩ : syracuseStep 2684285 = 1006607) B1006607
theorem B2389391 : Blo 706319 2389391 := bstep (se 1 (by rfl) ⟨1792043, by rfl⟩ : syracuseStep 2389391 = 3584087) B3584087
theorem B2553353 : Blo 706319 2553353 := bstep (se 2 (by rfl) ⟨957507, by rfl⟩ : syracuseStep 2553353 = 1915015) B1915015
theorem B2389715 : Blo 706319 2389715 := bstep (se 1 (by rfl) ⟨1792286, by rfl⟩ : syracuseStep 2389715 = 3584573) B3584573
theorem B5371757 : Blo 706319 5371757 := bstep (se 3 (by rfl) ⟨1007204, by rfl⟩ : syracuseStep 5371757 = 2014409) B2014409
theorem B1341497 : Blo 706319 1341497 := bstep (se 2 (by rfl) ⟨503061, by rfl⟩ : syracuseStep 1341497 = 1006123) B1006123
theorem B2685271 : Blo 706319 2685271 := bstep (se 1 (by rfl) ⟨2013953, by rfl⟩ : syracuseStep 2685271 = 4027907) B4027907
theorem B12089735 : Blo 706319 12089735 := bstep (se 1 (by rfl) ⟨9067301, by rfl⟩ : syracuseStep 12089735 = 18134603) B18134603
theorem B1341839 : Blo 706319 1341839 := bstep (se 1 (by rfl) ⟨1006379, by rfl⟩ : syracuseStep 1341839 = 2012759) B2012759
theorem B2685575 : Blo 706319 2685575 := bstep (se 1 (by rfl) ⟨2014181, by rfl⟩ : syracuseStep 2685575 = 4028363) B4028363
theorem B2390903 : Blo 706319 2390903 := bstep (se 1 (by rfl) ⟨1793177, by rfl⟩ : syracuseStep 2390903 = 3586355) B3586355
theorem B2554895 : Blo 706319 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B2686031 : Blo 706319 2686031 := bstep (se 1 (by rfl) ⟨2014523, by rfl⟩ : syracuseStep 2686031 = 4029047) B4029047
theorem B2391119 : Blo 706319 2391119 := bstep (se 1 (by rfl) ⟨1793339, by rfl⟩ : syracuseStep 2391119 = 3586679) B3586679
theorem B4029821 : Blo 706319 4029821 := bstep (se 3 (by rfl) ⟨755591, by rfl⟩ : syracuseStep 4029821 = 1511183) B1511183
theorem B2391497 : Blo 706319 2391497 := bstep (se 2 (by rfl) ⟨896811, by rfl⟩ : syracuseStep 2391497 = 1793623) B1793623
theorem B5111429 : Blo 706319 5111429 := bstep (se 4 (by rfl) ⟨479196, by rfl⟩ : syracuseStep 5111429 = 958393) B958393
theorem B3407507 : Blo 706319 3407507 := bstep (se 1 (by rfl) ⟨2555630, by rfl⟩ : syracuseStep 3407507 = 5111261) B5111261
theorem B2391767 : Blo 706319 2391767 := bstep (se 1 (by rfl) ⟨1793825, by rfl⟩ : syracuseStep 2391767 = 3587651) B3587651
theorem B2391983 : Blo 706319 2391983 := bstep (se 1 (by rfl) ⟨1793987, by rfl⟩ : syracuseStep 2391983 = 3587975) B3587975
theorem B29065229 : Blo 706319 29065229 := bstep (se 3 (by rfl) ⟨5449730, by rfl⟩ : syracuseStep 29065229 = 10899461) B10899461
theorem B2687489 : Blo 706319 2687489 := bstep (se 2 (by rfl) ⟨1007808, by rfl⟩ : syracuseStep 2687489 = 2015617) B2015617
theorem B2392577 : Blo 706319 2392577 := bstep (se 2 (by rfl) ⟨897216, by rfl⟩ : syracuseStep 2392577 = 1794433) B1794433
theorem B852655 : Blo 706319 852655 := bstep (se 1 (by rfl) ⟨639491, by rfl⟩ : syracuseStep 852655 = 1278983) B1278983
theorem B2687975 : Blo 706319 2687975 := bstep (se 1 (by rfl) ⟨2015981, by rfl⟩ : syracuseStep 2687975 = 4031963) B4031963
theorem B2393063 : Blo 706319 2393063 := bstep (se 1 (by rfl) ⟨1794797, by rfl⟩ : syracuseStep 2393063 = 3589595) B3589595
theorem B6816743 : Blo 706319 6816743 := bstep (se 1 (by rfl) ⟨5112557, by rfl⟩ : syracuseStep 6816743 = 10225115) B10225115
theorem B2393387 : Blo 706319 2393387 := bstep (se 1 (by rfl) ⟨1795040, by rfl⟩ : syracuseStep 2393387 = 3590081) B3590081
theorem B12912185 : Blo 706319 12912185 := bstep (se 2 (by rfl) ⟨4842069, by rfl⟩ : syracuseStep 12912185 = 9684139) B9684139
theorem B2393657 : Blo 706319 2393657 := bstep (se 2 (by rfl) ⟨897621, by rfl⟩ : syracuseStep 2393657 = 1795243) B1795243
theorem B3409465 : Blo 706319 3409465 := bstep (se 2 (by rfl) ⟨1278549, by rfl⟩ : syracuseStep 3409465 = 2557099) B2557099
theorem B5375645 : Blo 706319 5375645 := bstep (se 3 (by rfl) ⟨1007933, by rfl⟩ : syracuseStep 5375645 = 2015867) B2015867
theorem B1509167 : Blo 706319 1509167 := bstep (se 1 (by rfl) ⟨1131875, by rfl⟩ : syracuseStep 1509167 = 2263751) B2263751
theorem B4032463 : Blo 706319 4032463 := bstep (se 1 (by rfl) ⟨3024347, by rfl⟩ : syracuseStep 4032463 = 6048695) B6048695
theorem B7669741 : Blo 706319 7669741 := bstep (se 3 (by rfl) ⟨1438076, by rfl⟩ : syracuseStep 7669741 = 2876153) B2876153
theorem B2689159 : Blo 706319 2689159 := bstep (se 1 (by rfl) ⟨2016869, by rfl⟩ : syracuseStep 2689159 = 4033739) B4033739
theorem B2558137 : Blo 706319 2558137 := bstep (se 2 (by rfl) ⟨959301, by rfl⟩ : syracuseStep 2558137 = 1918603) B1918603
theorem B2689463 : Blo 706319 2689463 := bstep (se 1 (by rfl) ⟨2017097, by rfl⟩ : syracuseStep 2689463 = 4034195) B4034195
theorem B3639887 : Blo 706319 3639887 := bstep (se 1 (by rfl) ⟨2729915, by rfl⟩ : syracuseStep 3639887 = 5459831) B5459831
theorem B2394899 : Blo 706319 2394899 := bstep (se 1 (by rfl) ⟨1796174, by rfl⟩ : syracuseStep 2394899 = 3592349) B3592349
theorem B7670699 : Blo 706319 7670699 := bstep (se 1 (by rfl) ⟨5753024, by rfl⟩ : syracuseStep 7670699 = 11506049) B11506049
theorem B1510363 : Blo 706319 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B7638083 : Blo 706319 7638083 := bstep (se 1 (by rfl) ⟨5728562, by rfl⟩ : syracuseStep 7638083 = 11457125) B11457125
theorem B2428123 : Blo 706319 2428123 := bstep (se 1 (by rfl) ⟨1821092, by rfl⟩ : syracuseStep 2428123 = 3642185) B3642185
theorem B4033921 : Blo 706319 4033921 := bstep (se 2 (by rfl) ⟨1512720, by rfl⟩ : syracuseStep 4033921 = 3025441) B3025441
theorem B2395763 : Blo 706319 2395763 := bstep (se 1 (by rfl) ⟨1796822, by rfl⟩ : syracuseStep 2395763 = 3593645) B3593645
theorem B2396033 : Blo 706319 2396033 := bstep (se 2 (by rfl) ⟨898512, by rfl⟩ : syracuseStep 2396033 = 1797025) B1797025
theorem B3576473 : Blo 706319 3576473 := bstep (se 2 (by rfl) ⟨1341177, by rfl⟩ : syracuseStep 3576473 = 2682355) B2682355
theorem B2396843 : Blo 706319 2396843 := bstep (se 1 (by rfl) ⟨1797632, by rfl⟩ : syracuseStep 2396843 = 3595265) B3595265
theorem B3019463 : Blo 706319 3019463 := bstep (se 1 (by rfl) ⟨2264597, by rfl⟩ : syracuseStep 3019463 = 4529195) B4529195
theorem B3446009 : Blo 706319 3446009 := bstep (se 2 (by rfl) ⟨1292253, by rfl⟩ : syracuseStep 3446009 = 2584507) B2584507
theorem B5739979 : Blo 706319 5739979 := bstep (se 1 (by rfl) ⟨4304984, by rfl⟩ : syracuseStep 5739979 = 8609969) B8609969
theorem B955967 : Blo 706319 955967 := bstep (se 1 (by rfl) ⟨716975, by rfl⟩ : syracuseStep 955967 = 1433951) B1433951
theorem B1513055 : Blo 706319 1513055 := bstep (se 1 (by rfl) ⟨1134791, by rfl⟩ : syracuseStep 1513055 = 2269583) B2269583
theorem B3643217 : Blo 706319 3643217 := bstep (se 2 (by rfl) ⟨1366206, by rfl⟩ : syracuseStep 3643217 = 2732413) B2732413
theorem B3578255 : Blo 706319 3578255 := bstep (se 1 (by rfl) ⟨2683691, by rfl⟩ : syracuseStep 3578255 = 5367383) B5367383
theorem B3021239 : Blo 706319 3021239 := bstep (se 1 (by rfl) ⟨2265929, by rfl⟩ : syracuseStep 3021239 = 4531859) B4531859
theorem B1940089 : Blo 706319 1940089 := bstep (se 2 (by rfl) ⟨727533, by rfl⟩ : syracuseStep 1940089 = 1455067) B1455067
theorem B2693807 : Blo 706319 2693807 := bstep (se 1 (by rfl) ⟨2020355, by rfl⟩ : syracuseStep 2693807 = 4040711) B4040711
theorem B9214721 : Blo 706319 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B1514695 : Blo 706319 1514695 := bstep (se 1 (by rfl) ⟨1136021, by rfl⟩ : syracuseStep 1514695 = 2272043) B2272043
theorem B5447249 : Blo 706319 5447249 := bstep (se 2 (by rfl) ⟨2042718, by rfl⟩ : syracuseStep 5447249 = 4085437) B4085437
theorem B3022571 : Blo 706319 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B794911 : Blo 706319 794911 := bstep (se 1 (by rfl) ⟨596183, by rfl⟩ : syracuseStep 794911 = 1192367) B1192367
theorem B3580361 : Blo 706319 3580361 := bstep (se 2 (by rfl) ⟨1342635, by rfl⟩ : syracuseStep 3580361 = 2685271) B2685271
theorem B1516001 : Blo 706319 1516001 := bstep (se 2 (by rfl) ⟨568500, by rfl⟩ : syracuseStep 1516001 = 1137001) B1137001
theorem B795199 : Blo 706319 795199 := bstep (se 1 (by rfl) ⟨596399, by rfl⟩ : syracuseStep 795199 = 1192799) B1192799
theorem B2695751 : Blo 706319 2695751 := bstep (se 1 (by rfl) ⟨2021813, by rfl⟩ : syracuseStep 2695751 = 4043627) B4043627
theorem B3023513 : Blo 706319 3023513 := bstep (se 2 (by rfl) ⟨1133817, by rfl⟩ : syracuseStep 3023513 = 2267635) B2267635
theorem B1024735 : Blo 706319 1024735 := bstep (se 1 (by rfl) ⟨768551, by rfl⟩ : syracuseStep 1024735 = 1537103) B1537103
theorem B1516583 : Blo 706319 1516583 := bstep (se 1 (by rfl) ⟨1137437, by rfl⟩ : syracuseStep 1516583 = 2274875) B2274875
theorem B12133475 : Blo 706319 12133475 := bstep (se 1 (by rfl) ⟨9100106, by rfl⟩ : syracuseStep 12133475 = 18200213) B18200213
theorem B3581171 : Blo 706319 3581171 := bstep (se 1 (by rfl) ⟨2685878, by rfl⟩ : syracuseStep 3581171 = 5371757) B5371757
theorem B2696435 : Blo 706319 2696435 := bstep (se 1 (by rfl) ⟨2022326, by rfl⟩ : syracuseStep 2696435 = 4044653) B4044653
theorem B894331 : Blo 706319 894331 := bstep (se 1 (by rfl) ⟨670748, by rfl⟩ : syracuseStep 894331 = 1341497) B1341497
theorem B796027 : Blo 706319 796027 := bstep (se 1 (by rfl) ⟨597020, by rfl⟩ : syracuseStep 796027 = 1194041) B1194041
theorem B894559 : Blo 706319 894559 := bstep (se 1 (by rfl) ⟨670919, by rfl⟩ : syracuseStep 894559 = 1341839) B1341839
theorem B6039197 : Blo 706319 6039197 := bstep (se 3 (by rfl) ⟨1132349, by rfl⟩ : syracuseStep 6039197 = 2264699) B2264699
theorem B796495 : Blo 706319 796495 := bstep (se 1 (by rfl) ⟨597371, by rfl⟩ : syracuseStep 796495 = 1194743) B1194743
theorem B796891 : Blo 706319 796891 := bstep (se 1 (by rfl) ⟨597668, by rfl⟩ : syracuseStep 796891 = 1195337) B1195337
theorem B2271671 : Blo 706319 2271671 := bstep (se 1 (by rfl) ⟨1703753, by rfl⟩ : syracuseStep 2271671 = 3407507) B3407507
theorem B797179 : Blo 706319 797179 := bstep (se 1 (by rfl) ⟨597884, by rfl⟩ : syracuseStep 797179 = 1195769) B1195769
theorem B6826619 : Blo 706319 6826619 := bstep (se 1 (by rfl) ⟨5119964, by rfl⟩ : syracuseStep 6826619 = 10239929) B10239929
theorem B1059503 : Blo 706319 1059503 := bstep (se 1 (by rfl) ⟨794627, by rfl⟩ : syracuseStep 1059503 = 1589255) B1589255
theorem B797359 : Blo 706319 797359 := bstep (se 1 (by rfl) ⟨598019, by rfl⟩ : syracuseStep 797359 = 1196039) B1196039
theorem B1059551 : Blo 706319 1059551 := bstep (se 1 (by rfl) ⟨794663, by rfl⟩ : syracuseStep 1059551 = 1589327) B1589327
theorem B5745431 : Blo 706319 5745431 := bstep (se 1 (by rfl) ⟨4309073, by rfl⟩ : syracuseStep 5745431 = 8618147) B8618147
theorem B895799 : Blo 706319 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B1911707 : Blo 706319 1911707 := bstep (se 1 (by rfl) ⟨1433780, by rfl⟩ : syracuseStep 1911707 = 2867561) B2867561
theorem B895951 : Blo 706319 895951 := bstep (se 1 (by rfl) ⟨671963, by rfl⟩ : syracuseStep 895951 = 1343927) B1343927
theorem B797647 : Blo 706319 797647 := bstep (se 1 (by rfl) ⟨598235, by rfl⟩ : syracuseStep 797647 = 1196471) B1196471
theorem B1059815 : Blo 706319 1059815 := bstep (se 1 (by rfl) ⟨794861, by rfl⟩ : syracuseStep 1059815 = 1589723) B1589723
theorem B7777361 : Blo 706319 7777361 := bstep (se 2 (by rfl) ⟨2916510, by rfl⟩ : syracuseStep 7777361 = 5833021) B5833021
theorem B3681395 : Blo 706319 3681395 := bstep (se 1 (by rfl) ⟨2761046, by rfl⟩ : syracuseStep 3681395 = 5522093) B5522093
theorem B6466675 : Blo 706319 6466675 := bstep (se 1 (by rfl) ⟨4850006, by rfl⟩ : syracuseStep 6466675 = 9700013) B9700013
theorem B3583115 : Blo 706319 3583115 := bstep (se 1 (by rfl) ⟨2687336, by rfl⟩ : syracuseStep 3583115 = 5374673) B5374673
theorem B1060073 : Blo 706319 1060073 := bstep (se 2 (by rfl) ⟨397527, by rfl⟩ : syracuseStep 1060073 = 795055) B795055
theorem B1060127 : Blo 706319 1060127 := bstep (se 1 (by rfl) ⟨795095, by rfl⟩ : syracuseStep 1060127 = 1590191) B1590191
theorem B798043 : Blo 706319 798043 := bstep (se 1 (by rfl) ⟨598532, by rfl⟩ : syracuseStep 798043 = 1197065) B1197065
theorem B1060295 : Blo 706319 1060295 := bstep (se 1 (by rfl) ⟨795221, by rfl⟩ : syracuseStep 1060295 = 1590443) B1590443
theorem B798151 : Blo 706319 798151 := bstep (se 1 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 798151 = 1197227) B1197227
theorem B1617401 : Blo 706319 1617401 := bstep (se 2 (by rfl) ⟨606525, by rfl⟩ : syracuseStep 1617401 = 1213051) B1213051
theorem B3059225 : Blo 706319 3059225 := bstep (se 2 (by rfl) ⟨1147209, by rfl⟩ : syracuseStep 3059225 = 2294419) B2294419
theorem B1060649 : Blo 706319 1060649 := bstep (se 2 (by rfl) ⟨397743, by rfl⟩ : syracuseStep 1060649 = 795487) B795487
theorem B1060655 : Blo 706319 1060655 := bstep (se 1 (by rfl) ⟨795491, by rfl⟩ : syracuseStep 1060655 = 1590983) B1590983
theorem B798511 : Blo 706319 798511 := bstep (se 1 (by rfl) ⟨598883, by rfl⟩ : syracuseStep 798511 = 1197767) B1197767
theorem B896923 : Blo 706319 896923 := bstep (se 1 (by rfl) ⟨672692, by rfl⟩ : syracuseStep 896923 = 1345385) B1345385
theorem B798619 : Blo 706319 798619 := bstep (se 1 (by rfl) ⟨598964, by rfl⟩ : syracuseStep 798619 = 1197929) B1197929
theorem B3026945 : Blo 706319 3026945 := bstep (se 2 (by rfl) ⟨1135104, by rfl⟩ : syracuseStep 3026945 = 2270209) B2270209
theorem B1061129 : Blo 706319 1061129 := bstep (se 2 (by rfl) ⟨397923, by rfl⟩ : syracuseStep 1061129 = 795847) B795847
theorem B799015 : Blo 706319 799015 := bstep (se 1 (by rfl) ⟨599261, by rfl⟩ : syracuseStep 799015 = 1198523) B1198523
theorem B1061231 : Blo 706319 1061231 := bstep (se 1 (by rfl) ⟨795923, by rfl⟩ : syracuseStep 1061231 = 1591847) B1591847
theorem B799087 : Blo 706319 799087 := bstep (se 1 (by rfl) ⟨599315, by rfl⟩ : syracuseStep 799087 = 1198631) B1198631
theorem B1061447 : Blo 706319 1061447 := bstep (se 1 (by rfl) ⟨796085, by rfl⟩ : syracuseStep 1061447 = 1592171) B1592171
theorem B3027527 : Blo 706319 3027527 := bstep (se 1 (by rfl) ⟨2270645, by rfl⟩ : syracuseStep 3027527 = 4541291) B4541291
theorem B1061483 : Blo 706319 1061483 := bstep (se 1 (by rfl) ⟨796112, by rfl⟩ : syracuseStep 1061483 = 1592225) B1592225
theorem B6468281 : Blo 706319 6468281 := bstep (se 2 (by rfl) ⟨2425605, by rfl⟩ : syracuseStep 6468281 = 4851211) B4851211
theorem B23540441 : Blo 706319 23540441 := bstep (se 2 (by rfl) ⟨8827665, by rfl⟩ : syracuseStep 23540441 = 17655331) B17655331
theorem B3584735 : Blo 706319 3584735 := bstep (se 1 (by rfl) ⟨2688551, by rfl⟩ : syracuseStep 3584735 = 5377103) B5377103
theorem B1061711 : Blo 706319 1061711 := bstep (se 1 (by rfl) ⟨796283, by rfl⟩ : syracuseStep 1061711 = 1592567) B1592567
theorem B1619041 : Blo 706319 1619041 := bstep (se 2 (by rfl) ⟨607140, by rfl⟩ : syracuseStep 1619041 = 1214281) B1214281
theorem B2012303 : Blo 706319 2012303 := bstep (se 1 (by rfl) ⟨1509227, by rfl⟩ : syracuseStep 2012303 = 3018455) B3018455
theorem B2012359 : Blo 706319 2012359 := bstep (se 1 (by rfl) ⟨1509269, by rfl⟩ : syracuseStep 2012359 = 3018539) B3018539
theorem B1062107 : Blo 706319 1062107 := bstep (se 1 (by rfl) ⟨796580, by rfl⟩ : syracuseStep 1062107 = 1593161) B1593161
theorem B3028211 : Blo 706319 3028211 := bstep (se 1 (by rfl) ⟨2271158, by rfl⟩ : syracuseStep 3028211 = 4542317) B4542317
theorem B4044127 : Blo 706319 4044127 := bstep (se 1 (by rfl) ⟨3033095, by rfl⟩ : syracuseStep 4044127 = 6066191) B6066191
theorem B1193339 : Blo 706319 1193339 := bstep (se 1 (by rfl) ⟨895004, by rfl⟩ : syracuseStep 1193339 = 1790009) B1790009
theorem B1062281 : Blo 706319 1062281 := bstep (se 2 (by rfl) ⟨398355, by rfl⟩ : syracuseStep 1062281 = 796711) B796711
theorem B9582119 : Blo 706319 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B1062635 : Blo 706319 1062635 := bstep (se 1 (by rfl) ⟨796976, by rfl⟩ : syracuseStep 1062635 = 1593953) B1593953
theorem B9680755 : Blo 706319 9680755 := bstep (se 1 (by rfl) ⟨7260566, by rfl⟩ : syracuseStep 9680755 = 14521133) B14521133
theorem B1062863 : Blo 706319 1062863 := bstep (se 1 (by rfl) ⟨797147, by rfl⟩ : syracuseStep 1062863 = 1594295) B1594295
theorem B7288805 : Blo 706319 7288805 := bstep (se 4 (by rfl) ⟨683325, by rfl⟩ : syracuseStep 7288805 = 1366651) B1366651
theorem B2275361 : Blo 706319 2275361 := bstep (se 2 (by rfl) ⟨853260, by rfl⟩ : syracuseStep 2275361 = 1706521) B1706521
theorem B1194331 : Blo 706319 1194331 := bstep (se 1 (by rfl) ⟨895748, by rfl⟩ : syracuseStep 1194331 = 1791497) B1791497
theorem B1063259 : Blo 706319 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B1063487 : Blo 706319 1063487 := bstep (se 1 (by rfl) ⟨797615, by rfl⟩ : syracuseStep 1063487 = 1595231) B1595231
theorem B1063607 : Blo 706319 1063607 := bstep (se 1 (by rfl) ⟨797705, by rfl⟩ : syracuseStep 1063607 = 1595411) B1595411
theorem B2013943 : Blo 706319 2013943 := bstep (se 1 (by rfl) ⟨1510457, by rfl⟩ : syracuseStep 2013943 = 3020915) B3020915
theorem B3029885 : Blo 706319 3029885 := bstep (se 3 (by rfl) ⟨568103, by rfl⟩ : syracuseStep 3029885 = 1136207) B1136207
theorem B1063835 : Blo 706319 1063835 := bstep (se 1 (by rfl) ⟨797876, by rfl⟩ : syracuseStep 1063835 = 1595753) B1595753
theorem B9681839 : Blo 706319 9681839 := bstep (se 1 (by rfl) ⟨7261379, by rfl⟩ : syracuseStep 9681839 = 14522759) B14522759
theorem B3587003 : Blo 706319 3587003 := bstep (se 1 (by rfl) ⟨2690252, by rfl⟩ : syracuseStep 3587003 = 5380505) B5380505
theorem B1195303 : Blo 706319 1195303 := bstep (se 1 (by rfl) ⟨896477, by rfl⟩ : syracuseStep 1195303 = 1792955) B1792955
theorem B1064231 : Blo 706319 1064231 := bstep (se 1 (by rfl) ⟨798173, by rfl⟩ : syracuseStep 1064231 = 1596347) B1596347
theorem B1064315 : Blo 706319 1064315 := bstep (se 1 (by rfl) ⟨798236, by rfl⟩ : syracuseStep 1064315 = 1596473) B1596473
theorem B1064441 : Blo 706319 1064441 := bstep (se 2 (by rfl) ⟨399165, by rfl⟩ : syracuseStep 1064441 = 798331) B798331
theorem B9059921 : Blo 706319 9059921 := bstep (se 2 (by rfl) ⟨3397470, by rfl⟩ : syracuseStep 9059921 = 6794941) B6794941
theorem B1064543 : Blo 706319 1064543 := bstep (se 1 (by rfl) ⟨798407, by rfl⟩ : syracuseStep 1064543 = 1596815) B1596815
theorem B1195823 : Blo 706319 1195823 := bstep (se 1 (by rfl) ⟨896867, by rfl⟩ : syracuseStep 1195823 = 1793735) B1793735
theorem B1064759 : Blo 706319 1064759 := bstep (se 1 (by rfl) ⟨798569, by rfl⟩ : syracuseStep 1064759 = 1597139) B1597139
theorem B1065065 : Blo 706319 1065065 := bstep (se 2 (by rfl) ⟨399399, by rfl⟩ : syracuseStep 1065065 = 798799) B798799
theorem B3588299 : Blo 706319 3588299 := bstep (se 1 (by rfl) ⟨2691224, by rfl⟩ : syracuseStep 3588299 = 5382449) B5382449
theorem B1589615 : Blo 706319 1589615 := bstep (se 1 (by rfl) ⟨1192211, by rfl⟩ : syracuseStep 1589615 = 2384423) B2384423
theorem B1065383 : Blo 706319 1065383 := bstep (se 1 (by rfl) ⟨799037, by rfl⟩ : syracuseStep 1065383 = 1598075) B1598075
theorem B1589687 : Blo 706319 1589687 := bstep (se 1 (by rfl) ⟨1192265, by rfl⟩ : syracuseStep 1589687 = 2384531) B2384531
theorem B1065467 : Blo 706319 1065467 := bstep (se 1 (by rfl) ⟨799100, by rfl⟩ : syracuseStep 1065467 = 1598201) B1598201
theorem B1589831 : Blo 706319 1589831 := bstep (se 1 (by rfl) ⟨1192373, by rfl⟩ : syracuseStep 1589831 = 2384747) B2384747
theorem B13615715 : Blo 706319 13615715 := bstep (se 1 (by rfl) ⟨10211786, by rfl⟩ : syracuseStep 13615715 = 20423573) B20423573
theorem B1589867 : Blo 706319 1589867 := bstep (se 1 (by rfl) ⟨1192400, by rfl⟩ : syracuseStep 1589867 = 2384801) B2384801
theorem B2868047 : Blo 706319 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B1197031 : Blo 706319 1197031 := bstep (se 1 (by rfl) ⟨897773, by rfl⟩ : syracuseStep 1197031 = 1795547) B1795547
theorem B1131511 : Blo 706319 1131511 := bstep (se 1 (by rfl) ⟨848633, by rfl⟩ : syracuseStep 1131511 = 1697267) B1697267
theorem B1590263 : Blo 706319 1590263 := bstep (se 1 (by rfl) ⟨1192697, by rfl⟩ : syracuseStep 1590263 = 2385395) B2385395
theorem B6046919 : Blo 706319 6046919 := bstep (se 1 (by rfl) ⟨4535189, by rfl⟩ : syracuseStep 6046919 = 9070379) B9070379
theorem B2016505 : Blo 706319 2016505 := bstep (se 2 (by rfl) ⟨756189, by rfl⟩ : syracuseStep 2016505 = 1512379) B1512379
theorem B2016551 : Blo 706319 2016551 := bstep (se 1 (by rfl) ⟨1512413, by rfl⟩ : syracuseStep 2016551 = 3024827) B3024827
theorem B1918247 : Blo 706319 1918247 := bstep (se 1 (by rfl) ⟨1438685, by rfl⟩ : syracuseStep 1918247 = 2877371) B2877371
theorem B1590623 : Blo 706319 1590623 := bstep (se 1 (by rfl) ⟨1192967, by rfl⟩ : syracuseStep 1590623 = 2385935) B2385935
theorem B14501267 : Blo 706319 14501267 := bstep (se 1 (by rfl) ⟨10875950, by rfl⟩ : syracuseStep 14501267 = 21751901) B21751901
theorem B1591019 : Blo 706319 1591019 := bstep (se 1 (by rfl) ⟨1193264, by rfl⟩ : syracuseStep 1591019 = 2386529) B2386529
theorem B706351 : Blo 706319 706351 := bstep (se 1 (by rfl) ⟨529763, by rfl⟩ : syracuseStep 706351 = 1059527) B1059527
theorem B125617985 : Blo 706319 125617985 := bstep (se 2 (by rfl) ⟨47106744, by rfl⟩ : syracuseStep 125617985 = 94213489) B94213489
theorem B1591145 : Blo 706319 1591145 := bstep (se 2 (by rfl) ⟨596679, by rfl⟩ : syracuseStep 1591145 = 1193359) B1193359
theorem B706459 : Blo 706319 706459 := bstep (se 1 (by rfl) ⟨529844, by rfl⟩ : syracuseStep 706459 = 1059689) B1059689
theorem B706511 : Blo 706319 706511 := bstep (se 1 (by rfl) ⟨529883, by rfl⟩ : syracuseStep 706511 = 1059767) B1059767
theorem B706535 : Blo 706319 706535 := bstep (se 1 (by rfl) ⟨529901, by rfl⟩ : syracuseStep 706535 = 1059803) B1059803
theorem B1788115 : Blo 706319 1788115 := bstep (se 1 (by rfl) ⟨1341086, by rfl⟩ : syracuseStep 1788115 = 2682173) B2682173
theorem B706847 : Blo 706319 706847 := bstep (se 1 (by rfl) ⟨530135, by rfl⟩ : syracuseStep 706847 = 1060271) B1060271
theorem B706907 : Blo 706319 706907 := bstep (se 1 (by rfl) ⟨530180, by rfl⟩ : syracuseStep 706907 = 1060361) B1060361
theorem B706927 : Blo 706319 706927 := bstep (se 1 (by rfl) ⟨530195, by rfl⟩ : syracuseStep 706927 = 1060391) B1060391
theorem B706983 : Blo 706319 706983 := bstep (se 1 (by rfl) ⟨530237, by rfl⟩ : syracuseStep 706983 = 1060475) B1060475
theorem B3590567 : Blo 706319 3590567 := bstep (se 1 (by rfl) ⟨2692925, by rfl⟩ : syracuseStep 3590567 = 5385851) B5385851
theorem B707067 : Blo 706319 707067 := bstep (se 1 (by rfl) ⟨530300, by rfl⟩ : syracuseStep 707067 = 1060601) B1060601
theorem B707135 : Blo 706319 707135 := bstep (se 1 (by rfl) ⟨530351, by rfl⟩ : syracuseStep 707135 = 1060703) B1060703
theorem B1133119 : Blo 706319 1133119 := bstep (se 1 (by rfl) ⟨849839, by rfl⟩ : syracuseStep 1133119 = 1699679) B1699679
theorem B707143 : Blo 706319 707143 := bstep (se 1 (by rfl) ⟨530357, by rfl⟩ : syracuseStep 707143 = 1060715) B1060715
theorem B3590729 : Blo 706319 3590729 := bstep (se 2 (by rfl) ⟨1346523, by rfl⟩ : syracuseStep 3590729 = 2693047) B2693047
theorem B3885707 : Blo 706319 3885707 := bstep (se 1 (by rfl) ⟨2914280, by rfl⟩ : syracuseStep 3885707 = 5828561) B5828561
theorem B1591991 : Blo 706319 1591991 := bstep (se 1 (by rfl) ⟨1193993, by rfl⟩ : syracuseStep 1591991 = 2387987) B2387987
theorem B707295 : Blo 706319 707295 := bstep (se 1 (by rfl) ⟨530471, by rfl⟩ : syracuseStep 707295 = 1060943) B1060943
theorem B707375 : Blo 706319 707375 := bstep (se 1 (by rfl) ⟨530531, by rfl⟩ : syracuseStep 707375 = 1061063) B1061063
theorem B1592207 : Blo 706319 1592207 := bstep (se 1 (by rfl) ⟨1194155, by rfl⟩ : syracuseStep 1592207 = 2388311) B2388311
theorem B2018191 : Blo 706319 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B707483 : Blo 706319 707483 := bstep (se 1 (by rfl) ⟨530612, by rfl⟩ : syracuseStep 707483 = 1061225) B1061225
theorem B707535 : Blo 706319 707535 := bstep (se 1 (by rfl) ⟨530651, by rfl⟩ : syracuseStep 707535 = 1061303) B1061303
theorem B707559 : Blo 706319 707559 := bstep (se 1 (by rfl) ⟨530669, by rfl⟩ : syracuseStep 707559 = 1061339) B1061339
theorem B1362919 : Blo 706319 1362919 := bstep (se 1 (by rfl) ⟨1022189, by rfl⟩ : syracuseStep 1362919 = 2044379) B2044379
theorem B1789067 : Blo 706319 1789067 := bstep (se 1 (by rfl) ⟨1341800, by rfl⟩ : syracuseStep 1789067 = 2683601) B2683601
theorem B5393627 : Blo 706319 5393627 := bstep (se 1 (by rfl) ⟨4045220, by rfl⟩ : syracuseStep 5393627 = 8090441) B8090441
theorem B707871 : Blo 706319 707871 := bstep (se 1 (by rfl) ⟨530903, by rfl⟩ : syracuseStep 707871 = 1061807) B1061807
theorem B2018591 : Blo 706319 2018591 := bstep (se 1 (by rfl) ⟨1513943, by rfl⟩ : syracuseStep 2018591 = 3027887) B3027887
theorem B707931 : Blo 706319 707931 := bstep (se 1 (by rfl) ⟨530948, by rfl⟩ : syracuseStep 707931 = 1061897) B1061897
theorem B707951 : Blo 706319 707951 := bstep (se 1 (by rfl) ⟨530963, by rfl⟩ : syracuseStep 707951 = 1061927) B1061927
theorem B708007 : Blo 706319 708007 := bstep (se 1 (by rfl) ⟨531005, by rfl⟩ : syracuseStep 708007 = 1062011) B1062011
theorem B708091 : Blo 706319 708091 := bstep (se 1 (by rfl) ⟨531068, by rfl⟩ : syracuseStep 708091 = 1062137) B1062137
theorem B708159 : Blo 706319 708159 := bstep (se 1 (by rfl) ⟨531119, by rfl⟩ : syracuseStep 708159 = 1062239) B1062239
theorem B708167 : Blo 706319 708167 := bstep (se 1 (by rfl) ⟨531125, by rfl⟩ : syracuseStep 708167 = 1062251) B1062251
theorem B1789523 : Blo 706319 1789523 := bstep (se 1 (by rfl) ⟨1342142, by rfl⟩ : syracuseStep 1789523 = 2684285) B2684285
theorem B1592927 : Blo 706319 1592927 := bstep (se 1 (by rfl) ⟨1194695, by rfl⟩ : syracuseStep 1592927 = 2389391) B2389391
theorem B708319 : Blo 706319 708319 := bstep (se 1 (by rfl) ⟨531239, by rfl⟩ : syracuseStep 708319 = 1062479) B1062479
theorem B10342187 : Blo 706319 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B708399 : Blo 706319 708399 := bstep (se 1 (by rfl) ⟨531299, by rfl⟩ : syracuseStep 708399 = 1062599) B1062599
theorem B1593143 : Blo 706319 1593143 := bstep (se 1 (by rfl) ⟨1194857, by rfl⟩ : syracuseStep 1593143 = 2389715) B2389715
theorem B708507 : Blo 706319 708507 := bstep (se 1 (by rfl) ⟨531380, by rfl⟩ : syracuseStep 708507 = 1062761) B1062761
theorem B708559 : Blo 706319 708559 := bstep (se 1 (by rfl) ⟨531419, by rfl⟩ : syracuseStep 708559 = 1062839) B1062839
theorem B708583 : Blo 706319 708583 := bstep (se 1 (by rfl) ⟨531437, by rfl⟩ : syracuseStep 708583 = 1062875) B1062875
theorem B1593449 : Blo 706319 1593449 := bstep (se 2 (by rfl) ⟨597543, by rfl⟩ : syracuseStep 1593449 = 1195087) B1195087
theorem B708895 : Blo 706319 708895 := bstep (se 1 (by rfl) ⟨531671, by rfl⟩ : syracuseStep 708895 = 1063343) B1063343
theorem B708955 : Blo 706319 708955 := bstep (se 1 (by rfl) ⟨531716, by rfl⟩ : syracuseStep 708955 = 1063433) B1063433
theorem B708975 : Blo 706319 708975 := bstep (se 1 (by rfl) ⟨531731, by rfl⟩ : syracuseStep 708975 = 1063463) B1063463
theorem B709031 : Blo 706319 709031 := bstep (se 1 (by rfl) ⟨531773, by rfl⟩ : syracuseStep 709031 = 1063547) B1063547
theorem B1790383 : Blo 706319 1790383 := bstep (se 1 (by rfl) ⟨1342787, by rfl⟩ : syracuseStep 1790383 = 2685575) B2685575
theorem B2019809 : Blo 706319 2019809 := bstep (se 2 (by rfl) ⟨757428, by rfl⟩ : syracuseStep 2019809 = 1514857) B1514857
theorem B3592673 : Blo 706319 3592673 := bstep (se 2 (by rfl) ⟨1347252, by rfl⟩ : syracuseStep 3592673 = 2694505) B2694505
theorem B709115 : Blo 706319 709115 := bstep (se 1 (by rfl) ⟨531836, by rfl⟩ : syracuseStep 709115 = 1063673) B1063673
theorem B709183 : Blo 706319 709183 := bstep (se 1 (by rfl) ⟨531887, by rfl⟩ : syracuseStep 709183 = 1063775) B1063775
theorem B709191 : Blo 706319 709191 := bstep (se 1 (by rfl) ⟨531893, by rfl⟩ : syracuseStep 709191 = 1063787) B1063787
theorem B1593935 : Blo 706319 1593935 := bstep (se 1 (by rfl) ⟨1195451, by rfl⟩ : syracuseStep 1593935 = 2390903) B2390903
theorem B1790687 : Blo 706319 1790687 := bstep (se 1 (by rfl) ⟨1343015, by rfl⟩ : syracuseStep 1790687 = 2686031) B2686031
theorem B1594079 : Blo 706319 1594079 := bstep (se 1 (by rfl) ⟨1195559, by rfl⟩ : syracuseStep 1594079 = 2391119) B2391119
theorem B709343 : Blo 706319 709343 := bstep (se 1 (by rfl) ⟨532007, by rfl⟩ : syracuseStep 709343 = 1064015) B1064015
theorem B3822329 : Blo 706319 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B709423 : Blo 706319 709423 := bstep (se 1 (by rfl) ⟨532067, by rfl⟩ : syracuseStep 709423 = 1064135) B1064135
theorem B709531 : Blo 706319 709531 := bstep (se 1 (by rfl) ⟨532148, by rfl⟩ : syracuseStep 709531 = 1064297) B1064297
theorem B709583 : Blo 706319 709583 := bstep (se 1 (by rfl) ⟨532187, by rfl⟩ : syracuseStep 709583 = 1064375) B1064375
theorem B8049617 : Blo 706319 8049617 := bstep (se 2 (by rfl) ⟨3018606, by rfl⟩ : syracuseStep 8049617 = 6037213) B6037213
theorem B1594331 : Blo 706319 1594331 := bstep (se 1 (by rfl) ⟨1195748, by rfl⟩ : syracuseStep 1594331 = 2391497) B2391497
theorem B709607 : Blo 706319 709607 := bstep (se 1 (by rfl) ⟨532205, by rfl⟩ : syracuseStep 709607 = 1064411) B1064411
theorem B1594511 : Blo 706319 1594511 := bstep (se 1 (by rfl) ⟨1195883, by rfl⟩ : syracuseStep 1594511 = 2391767) B2391767
theorem B1594601 : Blo 706319 1594601 := bstep (se 2 (by rfl) ⟨597975, by rfl⟩ : syracuseStep 1594601 = 1195951) B1195951
theorem B1594655 : Blo 706319 1594655 := bstep (se 1 (by rfl) ⟨1195991, by rfl⟩ : syracuseStep 1594655 = 2391983) B2391983
theorem B709919 : Blo 706319 709919 := bstep (se 1 (by rfl) ⟨532439, by rfl⟩ : syracuseStep 709919 = 1064879) B1064879
theorem B709979 : Blo 706319 709979 := bstep (se 1 (by rfl) ⟨532484, by rfl⟩ : syracuseStep 709979 = 1064969) B1064969
theorem B709999 : Blo 706319 709999 := bstep (se 1 (by rfl) ⟨532499, by rfl⟩ : syracuseStep 709999 = 1064999) B1064999
theorem B1791355 : Blo 706319 1791355 := bstep (se 1 (by rfl) ⟨1343516, by rfl⟩ : syracuseStep 1791355 = 2687033) B2687033
theorem B710055 : Blo 706319 710055 := bstep (se 1 (by rfl) ⟨532541, by rfl⟩ : syracuseStep 710055 = 1065083) B1065083
theorem B710139 : Blo 706319 710139 := bstep (se 1 (by rfl) ⟨532604, by rfl⟩ : syracuseStep 710139 = 1065209) B1065209
theorem B710207 : Blo 706319 710207 := bstep (se 1 (by rfl) ⟨532655, by rfl⟩ : syracuseStep 710207 = 1065311) B1065311
theorem B710215 : Blo 706319 710215 := bstep (se 1 (by rfl) ⟨532661, by rfl⟩ : syracuseStep 710215 = 1065323) B1065323
theorem B3823193 : Blo 706319 3823193 := bstep (se 2 (by rfl) ⟨1433697, by rfl⟩ : syracuseStep 3823193 = 2867395) B2867395
theorem B2021051 : Blo 706319 2021051 := bstep (se 1 (by rfl) ⟨1515788, by rfl⟩ : syracuseStep 2021051 = 3031577) B3031577
theorem B1595177 : Blo 706319 1595177 := bstep (se 2 (by rfl) ⟨598191, by rfl⟩ : syracuseStep 1595177 = 1196383) B1196383
theorem B1791791 : Blo 706319 1791791 := bstep (se 1 (by rfl) ⟨1343843, by rfl⟩ : syracuseStep 1791791 = 2687687) B2687687
theorem B6051671 : Blo 706319 6051671 := bstep (se 1 (by rfl) ⟨4538753, by rfl⟩ : syracuseStep 6051671 = 9077507) B9077507
theorem B17192897 : Blo 706319 17192897 := bstep (se 2 (by rfl) ⟨6447336, by rfl⟩ : syracuseStep 17192897 = 12894673) B12894673
theorem B1366121 : Blo 706319 1366121 := bstep (se 2 (by rfl) ⟨512295, by rfl⟩ : syracuseStep 1366121 = 1024591) B1024591
theorem B1792439 : Blo 706319 1792439 := bstep (se 1 (by rfl) ⟨1344329, by rfl⟩ : syracuseStep 1792439 = 2688659) B2688659
theorem B3594941 : Blo 706319 3594941 := bstep (se 3 (by rfl) ⟨674051, by rfl⟩ : syracuseStep 3594941 = 1348103) B1348103
theorem B1596239 : Blo 706319 1596239 := bstep (se 1 (by rfl) ⟨1197179, by rfl⟩ : syracuseStep 1596239 = 2394359) B2394359
theorem B1596455 : Blo 706319 1596455 := bstep (se 1 (by rfl) ⟨1197341, by rfl⟩ : syracuseStep 1596455 = 2394683) B2394683
theorem B1596635 : Blo 706319 1596635 := bstep (se 1 (by rfl) ⟨1197476, by rfl⟩ : syracuseStep 1596635 = 2394953) B2394953
theorem B1793441 : Blo 706319 1793441 := bstep (se 2 (by rfl) ⟨672540, by rfl⟩ : syracuseStep 1793441 = 1345081) B1345081
theorem B1596833 : Blo 706319 1596833 := bstep (se 2 (by rfl) ⟨598812, by rfl⟩ : syracuseStep 1596833 = 1197625) B1197625
theorem B3366359 : Blo 706319 3366359 := bstep (se 1 (by rfl) ⟨2524769, by rfl⟩ : syracuseStep 3366359 = 5049539) B5049539
theorem B6446753 : Blo 706319 6446753 := bstep (se 2 (by rfl) ⟨2417532, by rfl⟩ : syracuseStep 6446753 = 4835065) B4835065
theorem B1793897 : Blo 706319 1793897 := bstep (se 2 (by rfl) ⟨672711, by rfl⟩ : syracuseStep 1793897 = 1345423) B1345423
theorem B1597391 : Blo 706319 1597391 := bstep (se 1 (by rfl) ⟨1198043, by rfl⟩ : syracuseStep 1597391 = 2396087) B2396087
theorem B8740871 : Blo 706319 8740871 := bstep (se 1 (by rfl) ⟨6555653, by rfl⟩ : syracuseStep 8740871 = 13111307) B13111307
theorem B1597769 : Blo 706319 1597769 := bstep (se 2 (by rfl) ⟨599163, by rfl⟩ : syracuseStep 1597769 = 1198327) B1198327
theorem B1597787 : Blo 706319 1597787 := bstep (se 1 (by rfl) ⟨1198340, by rfl⟩ : syracuseStep 1597787 = 2396681) B2396681
theorem B3400375 : Blo 706319 3400375 := bstep (se 1 (by rfl) ⟨2550281, by rfl⟩ : syracuseStep 3400375 = 5100563) B5100563
theorem B4842233 : Blo 706319 4842233 := bstep (se 2 (by rfl) ⟨1815837, by rfl⟩ : syracuseStep 4842233 = 3631675) B3631675
theorem B5530463 : Blo 706319 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B2155511 : Blo 706319 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B2385341 : Blo 706319 2385341 := bstep (se 3 (by rfl) ⟨447251, by rfl⟩ : syracuseStep 2385341 = 894503) B894503
theorem B1795679 : Blo 706319 1795679 := bstep (se 1 (by rfl) ⟨1346759, by rfl⟩ : syracuseStep 1795679 = 2693519) B2693519
theorem B2385719 : Blo 706319 2385719 := bstep (se 1 (by rfl) ⟨1789289, by rfl⟩ : syracuseStep 2385719 = 3578579) B3578579
theorem B31057901 : Blo 706319 31057901 := bstep (se 3 (by rfl) ⟨5823356, by rfl⟩ : syracuseStep 31057901 = 11646713) B11646713
theorem B1796377 : Blo 706319 1796377 := bstep (se 2 (by rfl) ⟨673641, by rfl⟩ : syracuseStep 1796377 = 1347283) B1347283
theorem B2386205 : Blo 706319 2386205 := bstep (se 3 (by rfl) ⟨447413, by rfl⟩ : syracuseStep 2386205 = 894827) B894827
theorem B1796519 : Blo 706319 1796519 := bstep (se 1 (by rfl) ⟨1347389, by rfl⟩ : syracuseStep 1796519 = 2694779) B2694779
theorem B1796681 : Blo 706319 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B2878199 : Blo 706319 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B25783193 : Blo 706319 25783193 := bstep (se 2 (by rfl) ⟨9668697, by rfl⟩ : syracuseStep 25783193 = 19337395) B19337395
theorem B2419901 : Blo 706319 2419901 := bstep (se 3 (by rfl) ⟨453731, by rfl⟩ : syracuseStep 2419901 = 907463) B907463
theorem B2682143 : Blo 706319 2682143 := bstep (se 1 (by rfl) ⟨2011607, by rfl⟩ : syracuseStep 2682143 = 4023215) B4023215
theorem B2387231 : Blo 706319 2387231 := bstep (se 1 (by rfl) ⟨1790423, by rfl⟩ : syracuseStep 2387231 = 3580847) B3580847
theorem B10349855 : Blo 706319 10349855 := bstep (se 1 (by rfl) ⟨7762391, by rfl⟩ : syracuseStep 10349855 = 15524783) B15524783
theorem B7663339 : Blo 706319 7663339 := bstep (se 1 (by rfl) ⟨5747504, by rfl⟩ : syracuseStep 7663339 = 11495009) B11495009
theorem B12120353 : Blo 706319 12120353 := bstep (se 2 (by rfl) ⟨4545132, by rfl⟩ : syracuseStep 12120353 = 9090265) B9090265
theorem B17985899 : Blo 706319 17985899 := bstep (se 1 (by rfl) ⟨13489424, by rfl⟩ : syracuseStep 17985899 = 26978849) B26978849
theorem B1274543 : Blo 706319 1274543 := bstep (se 1 (by rfl) ⟨955907, by rfl⟩ : syracuseStep 1274543 = 1911815) B1911815
theorem B1700851 : Blo 706319 1700851 := bstep (se 1 (by rfl) ⟨1275638, by rfl⟩ : syracuseStep 1700851 = 2551277) B2551277
theorem B3634301 : Blo 706319 3634301 := bstep (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) B1362863
theorem B2553065 : Blo 706319 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B2684299 : Blo 706319 2684299 := bstep (se 1 (by rfl) ⟨2013224, by rfl⟩ : syracuseStep 2684299 = 4026449) B4026449
theorem B1341011 : Blo 706319 1341011 := bstep (se 1 (by rfl) ⟨1005758, by rfl⟩ : syracuseStep 1341011 = 2011517) B2011517
theorem B2684573 : Blo 706319 2684573 := bstep (se 3 (by rfl) ⟨503357, by rfl⟩ : syracuseStep 2684573 = 1006715) B1006715
theorem B2389661 : Blo 706319 2389661 := bstep (se 3 (by rfl) ⟨448061, by rfl⟩ : syracuseStep 2389661 = 896123) B896123
theorem B4028089 : Blo 706319 4028089 := bstep (se 2 (by rfl) ⟨1510533, by rfl⟩ : syracuseStep 4028089 = 3021067) B3021067
theorem B2684603 : Blo 706319 2684603 := bstep (se 1 (by rfl) ⟨2013452, by rfl⟩ : syracuseStep 2684603 = 4026905) B4026905
theorem B18446039 : Blo 706319 18446039 := bstep (se 1 (by rfl) ⟨13834529, by rfl⟩ : syracuseStep 18446039 = 27669059) B27669059
theorem B23000921 : Blo 706319 23000921 := bstep (se 2 (by rfl) ⟨8625345, by rfl⟩ : syracuseStep 23000921 = 17250691) B17250691
theorem B17201251 : Blo 706319 17201251 := bstep (se 1 (by rfl) ⟨12900938, by rfl⟩ : syracuseStep 17201251 = 25801877) B25801877
theorem B2390201 : Blo 706319 2390201 := bstep (se 2 (by rfl) ⟨896325, by rfl⟩ : syracuseStep 2390201 = 1792651) B1792651
theorem B1702235 : Blo 706319 1702235 := bstep (se 1 (by rfl) ⟨1276676, by rfl⟩ : syracuseStep 1702235 = 2553353) B2553353
theorem B8059823 : Blo 706319 8059823 := bstep (se 1 (by rfl) ⟨6044867, by rfl⟩ : syracuseStep 8059823 = 12089735) B12089735
theorem B13630477 : Blo 706319 13630477 := bstep (se 3 (by rfl) ⟨2555714, by rfl⟩ : syracuseStep 13630477 = 5111429) B5111429
theorem B4357309 : Blo 706319 4357309 := bstep (se 3 (by rfl) ⟨816995, by rfl⟩ : syracuseStep 4357309 = 1633991) B1633991
theorem B1703263 : Blo 706319 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B2686547 : Blo 706319 2686547 := bstep (se 1 (by rfl) ⟨2014910, by rfl⟩ : syracuseStep 2686547 = 4029821) B4029821
theorem B1343137 : Blo 706319 1343137 := bstep (se 2 (by rfl) ⟨503676, by rfl⟩ : syracuseStep 1343137 = 1007353) B1007353
theorem B2391713 : Blo 706319 2391713 := bstep (se 2 (by rfl) ⟨896892, by rfl⟩ : syracuseStep 2391713 = 1793785) B1793785
theorem B6061817 : Blo 706319 6061817 := bstep (se 2 (by rfl) ⟨2273181, by rfl⟩ : syracuseStep 6061817 = 4546363) B4546363
theorem B9207647 : Blo 706319 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B3833729 : Blo 706319 3833729 := bstep (se 2 (by rfl) ⟨1437648, by rfl⟩ : syracuseStep 3833729 = 2875297) B2875297
theorem B2392199 : Blo 706319 2392199 := bstep (se 1 (by rfl) ⟨1794149, by rfl⟩ : syracuseStep 2392199 = 3588299) B3588299
theorem B9077143 : Blo 706319 9077143 := bstep (se 1 (by rfl) ⟨6807857, by rfl⟩ : syracuseStep 9077143 = 13615715) B13615715
theorem B4031279 : Blo 706319 4031279 := bstep (se 1 (by rfl) ⟨3023459, by rfl⟩ : syracuseStep 4031279 = 6046919) B6046919
theorem B1344367 : Blo 706319 1344367 := bstep (se 1 (by rfl) ⟨1008275, by rfl⟩ : syracuseStep 1344367 = 2016551) B2016551
theorem B9667511 : Blo 706319 9667511 := bstep (se 1 (by rfl) ⟨7250633, by rfl⟩ : syracuseStep 9667511 = 14501267) B14501267
theorem B1508681 : Blo 706319 1508681 := bstep (se 2 (by rfl) ⟨565755, by rfl⟩ : syracuseStep 1508681 = 1131511) B1131511
theorem B2393711 : Blo 706319 2393711 := bstep (se 1 (by rfl) ⟨1795283, by rfl⟩ : syracuseStep 2393711 = 3590567) B3590567
theorem B2688673 : Blo 706319 2688673 := bstep (se 2 (by rfl) ⟨1008252, by rfl⟩ : syracuseStep 2688673 = 2016505) B2016505
theorem B2393819 : Blo 706319 2393819 := bstep (se 1 (by rfl) ⟨1795364, by rfl⟩ : syracuseStep 2393819 = 3590729) B3590729
theorem B2426591 : Blo 706319 2426591 := bstep (se 1 (by rfl) ⟨1819943, by rfl⟩ : syracuseStep 2426591 = 3639887) B3639887
theorem B2590471 : Blo 706319 2590471 := bstep (se 1 (by rfl) ⟨1942853, by rfl⟩ : syracuseStep 2590471 = 3885707) B3885707
theorem B5113799 : Blo 706319 5113799 := bstep (se 1 (by rfl) ⟨3835349, by rfl⟩ : syracuseStep 5113799 = 7670699) B7670699
theorem B10192877 : Blo 706319 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B1345727 : Blo 706319 1345727 := bstep (se 1 (by rfl) ⟨1009295, by rfl⟩ : syracuseStep 1345727 = 2018591) B2018591
theorem B41388565 : Blo 706319 41388565 := bstep (se 6 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 41388565 = 1940089) B1940089
theorem B5376617 : Blo 706319 5376617 := bstep (se 2 (by rfl) ⟨2016231, by rfl⟩ : syracuseStep 5376617 = 4032463) B4032463
theorem B10226321 : Blo 706319 10226321 := bstep (se 2 (by rfl) ⟨3834870, by rfl⟩ : syracuseStep 10226321 = 7669741) B7669741
theorem B3410849 : Blo 706319 3410849 := bstep (se 2 (by rfl) ⟨1279068, by rfl⟩ : syracuseStep 3410849 = 2558137) B2558137
theorem B1346539 : Blo 706319 1346539 := bstep (se 1 (by rfl) ⟨1009904, by rfl⟩ : syracuseStep 1346539 = 2019809) B2019809
theorem B2395115 : Blo 706319 2395115 := bstep (se 1 (by rfl) ⟨1796336, by rfl⟩ : syracuseStep 2395115 = 3592673) B3592673
theorem B2395169 : Blo 706319 2395169 := bstep (se 2 (by rfl) ⟨898188, by rfl⟩ : syracuseStep 2395169 = 1796377) B1796377
theorem B1510825 : Blo 706319 1510825 := bstep (se 2 (by rfl) ⟨566559, by rfl⟩ : syracuseStep 1510825 = 1133119) B1133119
theorem B5115325 : Blo 706319 5115325 := bstep (se 3 (by rfl) ⟨959123, by rfl⟩ : syracuseStep 5115325 = 1918247) B1918247
theorem B2297339 : Blo 706319 2297339 := bstep (se 1 (by rfl) ⟨1723004, by rfl⟩ : syracuseStep 2297339 = 3446009) B3446009
theorem B1347367 : Blo 706319 1347367 := bstep (se 1 (by rfl) ⟨1010525, by rfl⟩ : syracuseStep 1347367 = 2021051) B2021051
theorem B2690921 : Blo 706319 2690921 := bstep (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) B2018191
theorem B2428811 : Blo 706319 2428811 := bstep (se 1 (by rfl) ⟨1821608, by rfl⟩ : syracuseStep 2428811 = 3643217) B3643217
theorem B4034447 : Blo 706319 4034447 := bstep (se 1 (by rfl) ⟨3025835, by rfl⟩ : syracuseStep 4034447 = 6051671) B6051671
theorem B8622233 : Blo 706319 8622233 := bstep (se 2 (by rfl) ⟨3233337, by rfl⟩ : syracuseStep 8622233 = 6466675) B6466675
theorem B2396627 : Blo 706319 2396627 := bstep (se 1 (by rfl) ⟨1797470, by rfl⟩ : syracuseStep 2396627 = 3594941) B3594941
theorem B5378561 : Blo 706319 5378561 := bstep (se 2 (by rfl) ⟨2016960, by rfl⟩ : syracuseStep 5378561 = 4033921) B4033921
theorem B4297835 : Blo 706319 4297835 := bstep (se 1 (by rfl) ⟨3223376, by rfl⟩ : syracuseStep 4297835 = 6446753) B6446753
theorem B2267801 : Blo 706319 2267801 := bstep (se 2 (by rfl) ⟨850425, by rfl⟩ : syracuseStep 2267801 = 1700851) B1700851
theorem B1514447 : Blo 706319 1514447 := bstep (se 1 (by rfl) ⟨1135835, by rfl⟩ : syracuseStep 1514447 = 2271671) B2271671
theorem B3579065 : Blo 706319 3579065 := bstep (se 2 (by rfl) ⟨1342149, by rfl⟩ : syracuseStep 3579065 = 2684299) B2684299
theorem B1613267 : Blo 706319 1613267 := bstep (se 1 (by rfl) ⟨1209950, by rfl⟩ : syracuseStep 1613267 = 2419901) B2419901
theorem B2039483 : Blo 706319 2039483 := bstep (se 1 (by rfl) ⟨1529612, by rfl⟩ : syracuseStep 2039483 = 3059225) B3059225
theorem B795559 : Blo 706319 795559 := bstep (se 1 (by rfl) ⟨596669, by rfl⟩ : syracuseStep 795559 = 1193339) B1193339
theorem B894007 : Blo 706319 894007 := bstep (se 1 (by rfl) ⟨670505, by rfl⟩ : syracuseStep 894007 = 1341011) B1341011
theorem B12297359 : Blo 706319 12297359 := bstep (se 1 (by rfl) ⟨9223019, by rfl⟩ : syracuseStep 12297359 = 18446039) B18446039
theorem B4859203 : Blo 706319 4859203 := bstep (se 1 (by rfl) ⟨3644402, by rfl⟩ : syracuseStep 4859203 = 7288805) B7288805
theorem B1516907 : Blo 706319 1516907 := bstep (se 1 (by rfl) ⟨1137680, by rfl⟩ : syracuseStep 1516907 = 2275361) B2275361
theorem B5809745 : Blo 706319 5809745 := bstep (se 2 (by rfl) ⟨2178654, by rfl⟩ : syracuseStep 5809745 = 4357309) B4357309
theorem B2271017 : Blo 706319 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B6039947 : Blo 706319 6039947 := bstep (se 1 (by rfl) ⟨4529960, by rfl⟩ : syracuseStep 6039947 = 9059921) B9059921
theorem B4041211 : Blo 706319 4041211 := bstep (se 1 (by rfl) ⟨3030908, by rfl⟩ : syracuseStep 4041211 = 6061817) B6061817
theorem B797215 : Blo 706319 797215 := bstep (se 1 (by rfl) ⟨597911, by rfl⟩ : syracuseStep 797215 = 1195823) B1195823
theorem B6138431 : Blo 706319 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B19376819 : Blo 706319 19376819 := bstep (se 1 (by rfl) ⟨14532614, by rfl⟩ : syracuseStep 19376819 = 29065229) B29065229
theorem B1059743 : Blo 706319 1059743 := bstep (se 1 (by rfl) ⟨794807, by rfl⟩ : syracuseStep 1059743 = 1589615) B1589615
theorem B1059791 : Blo 706319 1059791 := bstep (se 1 (by rfl) ⟨794843, by rfl⟩ : syracuseStep 1059791 = 1589687) B1589687
theorem B1059881 : Blo 706319 1059881 := bstep (se 2 (by rfl) ⟨397455, by rfl⟩ : syracuseStep 1059881 = 794911) B794911
theorem B1059887 : Blo 706319 1059887 := bstep (se 1 (by rfl) ⟨794915, by rfl⟩ : syracuseStep 1059887 = 1589831) B1589831
theorem B1059911 : Blo 706319 1059911 := bstep (se 1 (by rfl) ⟨794933, by rfl⟩ : syracuseStep 1059911 = 1589867) B1589867
theorem B1912031 : Blo 706319 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B1060175 : Blo 706319 1060175 := bstep (se 1 (by rfl) ⟨795131, by rfl⟩ : syracuseStep 1060175 = 1590263) B1590263
theorem B1060265 : Blo 706319 1060265 := bstep (se 2 (by rfl) ⟨397599, by rfl⟩ : syracuseStep 1060265 = 795199) B795199
theorem B1060415 : Blo 706319 1060415 := bstep (se 1 (by rfl) ⟨795311, by rfl⟩ : syracuseStep 1060415 = 1590623) B1590623
theorem B4533833 : Blo 706319 4533833 := bstep (se 2 (by rfl) ⟨1700187, by rfl⟩ : syracuseStep 4533833 = 3400375) B3400375
theorem B3583763 : Blo 706319 3583763 := bstep (se 1 (by rfl) ⟨2687822, by rfl⟩ : syracuseStep 3583763 = 5375645) B5375645
theorem B1060679 : Blo 706319 1060679 := bstep (se 1 (by rfl) ⟨795509, by rfl⟩ : syracuseStep 1060679 = 1591019) B1591019
theorem B1060763 : Blo 706319 1060763 := bstep (se 1 (by rfl) ⟨795572, by rfl⟩ : syracuseStep 1060763 = 1591145) B1591145
theorem B4042669 : Blo 706319 4042669 := bstep (se 3 (by rfl) ⟨758000, by rfl⟩ : syracuseStep 4042669 = 1516001) B1516001
theorem B1061327 : Blo 706319 1061327 := bstep (se 1 (by rfl) ⟨795995, by rfl⟩ : syracuseStep 1061327 = 1591991) B1591991
theorem B1192441 : Blo 706319 1192441 := bstep (se 2 (by rfl) ⟨447165, by rfl⟩ : syracuseStep 1192441 = 894331) B894331
theorem B1061369 : Blo 706319 1061369 := bstep (se 2 (by rfl) ⟨398013, by rfl⟩ : syracuseStep 1061369 = 796027) B796027
theorem B1061471 : Blo 706319 1061471 := bstep (se 1 (by rfl) ⟨796103, by rfl⟩ : syracuseStep 1061471 = 1592207) B1592207
theorem B5092055 : Blo 706319 5092055 := bstep (se 1 (by rfl) ⟨3819041, by rfl⟩ : syracuseStep 5092055 = 7638083) B7638083
theorem B1192711 : Blo 706319 1192711 := bstep (se 1 (by rfl) ⟨894533, by rfl⟩ : syracuseStep 1192711 = 1789067) B1789067
theorem B1192745 : Blo 706319 1192745 := bstep (se 2 (by rfl) ⟨447279, by rfl⟩ : syracuseStep 1192745 = 894559) B894559
theorem B1193015 : Blo 706319 1193015 := bstep (se 1 (by rfl) ⟨894761, by rfl⟩ : syracuseStep 1193015 = 1789523) B1789523
theorem B1061951 : Blo 706319 1061951 := bstep (se 1 (by rfl) ⟨796463, by rfl⟩ : syracuseStep 1061951 = 1592927) B1592927
theorem B1061993 : Blo 706319 1061993 := bstep (se 2 (by rfl) ⟨398247, by rfl⟩ : syracuseStep 1061993 = 796495) B796495
theorem B6894791 : Blo 706319 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B1062095 : Blo 706319 1062095 := bstep (se 1 (by rfl) ⟨796571, by rfl⟩ : syracuseStep 1062095 = 1593143) B1593143
theorem B5748029 : Blo 706319 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B1062299 : Blo 706319 1062299 := bstep (se 1 (by rfl) ⟨796724, by rfl⟩ : syracuseStep 1062299 = 1593449) B1593449
theorem B3585545 : Blo 706319 3585545 := bstep (se 2 (by rfl) ⟨1344579, by rfl⟩ : syracuseStep 3585545 = 2689159) B2689159
theorem B1062521 : Blo 706319 1062521 := bstep (se 2 (by rfl) ⟨398445, by rfl⟩ : syracuseStep 1062521 = 796891) B796891
theorem B1062623 : Blo 706319 1062623 := bstep (se 1 (by rfl) ⟨796967, by rfl⟩ : syracuseStep 1062623 = 1593935) B1593935
theorem B2012975 : Blo 706319 2012975 := bstep (se 1 (by rfl) ⟨1509731, by rfl⟩ : syracuseStep 2012975 = 3019463) B3019463
theorem B1193791 : Blo 706319 1193791 := bstep (se 1 (by rfl) ⟨895343, by rfl⟩ : syracuseStep 1193791 = 1790687) B1790687
theorem B1062719 : Blo 706319 1062719 := bstep (se 1 (by rfl) ⟨797039, by rfl⟩ : syracuseStep 1062719 = 1594079) B1594079
theorem B1062887 : Blo 706319 1062887 := bstep (se 1 (by rfl) ⟨797165, by rfl⟩ : syracuseStep 1062887 = 1594331) B1594331
theorem B1062905 : Blo 706319 1062905 := bstep (se 2 (by rfl) ⟨398589, by rfl⟩ : syracuseStep 1062905 = 797179) B797179
theorem B1063007 : Blo 706319 1063007 := bstep (se 1 (by rfl) ⟨797255, by rfl⟩ : syracuseStep 1063007 = 1594511) B1594511
theorem B1063067 : Blo 706319 1063067 := bstep (se 1 (by rfl) ⟨797300, by rfl⟩ : syracuseStep 1063067 = 1594601) B1594601
theorem B1063103 : Blo 706319 1063103 := bstep (se 1 (by rfl) ⟨797327, by rfl⟩ : syracuseStep 1063103 = 1594655) B1594655
theorem B1063145 : Blo 706319 1063145 := bstep (se 2 (by rfl) ⟨398679, by rfl⟩ : syracuseStep 1063145 = 797359) B797359
theorem B1063451 : Blo 706319 1063451 := bstep (se 1 (by rfl) ⟨797588, by rfl⟩ : syracuseStep 1063451 = 1595177) B1595177
theorem B1194527 : Blo 706319 1194527 := bstep (se 1 (by rfl) ⟨895895, by rfl⟩ : syracuseStep 1194527 = 1791791) B1791791
theorem B1194601 : Blo 706319 1194601 := bstep (se 2 (by rfl) ⟨447975, by rfl⟩ : syracuseStep 1194601 = 895951) B895951
theorem B1063529 : Blo 706319 1063529 := bstep (se 2 (by rfl) ⟨398823, by rfl⟩ : syracuseStep 1063529 = 797647) B797647
theorem B2013817 : Blo 706319 2013817 := bstep (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) B1510363
theorem B1817225 : Blo 706319 1817225 := bstep (se 2 (by rfl) ⟨681459, by rfl⟩ : syracuseStep 1817225 = 1362919) B1362919
theorem B2014159 : Blo 706319 2014159 := bstep (se 1 (by rfl) ⟨1510619, by rfl⟩ : syracuseStep 2014159 = 3021239) B3021239
theorem B1194959 : Blo 706319 1194959 := bstep (se 1 (by rfl) ⟨896219, by rfl⟩ : syracuseStep 1194959 = 1792439) B1792439
theorem B1064057 : Blo 706319 1064057 := bstep (se 2 (by rfl) ⟨399021, by rfl⟩ : syracuseStep 1064057 = 798043) B798043
theorem B6143147 : Blo 706319 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B1064159 : Blo 706319 1064159 := bstep (se 1 (by rfl) ⟨798119, by rfl⟩ : syracuseStep 1064159 = 1596239) B1596239
theorem B1064201 : Blo 706319 1064201 := bstep (se 2 (by rfl) ⟨399075, by rfl⟩ : syracuseStep 1064201 = 798151) B798151
theorem B1064303 : Blo 706319 1064303 := bstep (se 1 (by rfl) ⟨798227, by rfl⟩ : syracuseStep 1064303 = 1596455) B1596455
theorem B1064423 : Blo 706319 1064423 := bstep (se 1 (by rfl) ⟨798317, by rfl⟩ : syracuseStep 1064423 = 1596635) B1596635
theorem B1195627 : Blo 706319 1195627 := bstep (se 1 (by rfl) ⟨896720, by rfl⟩ : syracuseStep 1195627 = 1793441) B1793441
theorem B1064555 : Blo 706319 1064555 := bstep (se 1 (by rfl) ⟨798416, by rfl⟩ : syracuseStep 1064555 = 1596833) B1596833
theorem B2244239 : Blo 706319 2244239 := bstep (se 1 (by rfl) ⟨1683179, by rfl⟩ : syracuseStep 2244239 = 3366359) B3366359
theorem B1064681 : Blo 706319 1064681 := bstep (se 2 (by rfl) ⟨399255, by rfl⟩ : syracuseStep 1064681 = 798511) B798511
theorem B2015047 : Blo 706319 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B1195897 : Blo 706319 1195897 := bstep (se 2 (by rfl) ⟨448461, by rfl⟩ : syracuseStep 1195897 = 896923) B896923
theorem B1064825 : Blo 706319 1064825 := bstep (se 2 (by rfl) ⟨399309, by rfl⟩ : syracuseStep 1064825 = 798619) B798619
theorem B1195931 : Blo 706319 1195931 := bstep (se 1 (by rfl) ⟨896948, by rfl⟩ : syracuseStep 1195931 = 1793897) B1793897
theorem B1064927 : Blo 706319 1064927 := bstep (se 1 (by rfl) ⟨798695, by rfl⟩ : syracuseStep 1064927 = 1597391) B1597391
theorem B1065179 : Blo 706319 1065179 := bstep (se 1 (by rfl) ⟨798884, by rfl⟩ : syracuseStep 1065179 = 1597769) B1597769
theorem B1065191 : Blo 706319 1065191 := bstep (se 1 (by rfl) ⟨798893, by rfl⟩ : syracuseStep 1065191 = 1597787) B1597787
theorem B1065353 : Blo 706319 1065353 := bstep (se 2 (by rfl) ⟨399507, by rfl⟩ : syracuseStep 1065353 = 799015) B799015
theorem B2015675 : Blo 706319 2015675 := bstep (se 1 (by rfl) ⟨1511756, by rfl⟩ : syracuseStep 2015675 = 3023513) B3023513
theorem B1065449 : Blo 706319 1065449 := bstep (se 2 (by rfl) ⟨399543, by rfl⟩ : syracuseStep 1065449 = 799087) B799087
theorem B3228155 : Blo 706319 3228155 := bstep (se 1 (by rfl) ⟨2421116, by rfl⟩ : syracuseStep 3228155 = 4842233) B4842233
theorem B3686975 : Blo 706319 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B1590227 : Blo 706319 1590227 := bstep (se 1 (by rfl) ⟨1192670, by rfl⟩ : syracuseStep 1590227 = 2385341) B2385341
theorem B1197119 : Blo 706319 1197119 := bstep (se 1 (by rfl) ⟨897839, by rfl⟩ : syracuseStep 1197119 = 1795679) B1795679
theorem B1590479 : Blo 706319 1590479 := bstep (se 1 (by rfl) ⟨1192859, by rfl⟩ : syracuseStep 1590479 = 2385719) B2385719
theorem B1590803 : Blo 706319 1590803 := bstep (se 1 (by rfl) ⟨1193102, by rfl⟩ : syracuseStep 1590803 = 2386205) B2386205
theorem B1197679 : Blo 706319 1197679 := bstep (se 1 (by rfl) ⟨898259, by rfl⟩ : syracuseStep 1197679 = 1796519) B1796519
theorem B1197787 : Blo 706319 1197787 := bstep (se 1 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 1197787 = 1796681) B1796681
theorem B706335 : Blo 706319 706335 := bstep (se 1 (by rfl) ⟨529751, by rfl⟩ : syracuseStep 706335 = 1059503) B1059503
theorem B5392169 : Blo 706319 5392169 := bstep (se 2 (by rfl) ⟨2022063, by rfl⟩ : syracuseStep 5392169 = 4044127) B4044127
theorem B706367 : Blo 706319 706367 := bstep (se 1 (by rfl) ⟨529775, by rfl⟩ : syracuseStep 706367 = 1059551) B1059551
theorem B1918799 : Blo 706319 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B7653305 : Blo 706319 7653305 := bstep (se 2 (by rfl) ⟨2869989, by rfl⟩ : syracuseStep 7653305 = 5739979) B5739979
theorem B17188795 : Blo 706319 17188795 := bstep (se 1 (by rfl) ⟨12891596, by rfl⟩ : syracuseStep 17188795 = 25783193) B25783193
theorem B706543 : Blo 706319 706543 := bstep (se 1 (by rfl) ⟨529907, by rfl⟩ : syracuseStep 706543 = 1059815) B1059815
theorem B706715 : Blo 706319 706715 := bstep (se 1 (by rfl) ⟨530036, by rfl⟩ : syracuseStep 706715 = 1060073) B1060073
theorem B1788095 : Blo 706319 1788095 := bstep (se 1 (by rfl) ⟨1341071, by rfl⟩ : syracuseStep 1788095 = 2682143) B2682143
theorem B706751 : Blo 706319 706751 := bstep (se 1 (by rfl) ⟨530063, by rfl⟩ : syracuseStep 706751 = 1060127) B1060127
theorem B1591487 : Blo 706319 1591487 := bstep (se 1 (by rfl) ⟨1193615, by rfl⟩ : syracuseStep 1591487 = 2387231) B2387231
theorem B6899903 : Blo 706319 6899903 := bstep (se 1 (by rfl) ⟨5174927, by rfl⟩ : syracuseStep 6899903 = 10349855) B10349855
theorem B706863 : Blo 706319 706863 := bstep (se 1 (by rfl) ⟨530147, by rfl⟩ : syracuseStep 706863 = 1060295) B1060295
theorem B707099 : Blo 706319 707099 := bstep (se 1 (by rfl) ⟨530324, by rfl⟩ : syracuseStep 707099 = 1060649) B1060649
theorem B707103 : Blo 706319 707103 := bstep (se 1 (by rfl) ⟨530327, by rfl⟩ : syracuseStep 707103 = 1060655) B1060655
theorem B2017963 : Blo 706319 2017963 := bstep (se 1 (by rfl) ⟨1513472, by rfl⟩ : syracuseStep 2017963 = 3026945) B3026945
theorem B707419 : Blo 706319 707419 := bstep (se 1 (by rfl) ⟨530564, by rfl⟩ : syracuseStep 707419 = 1061129) B1061129
theorem B8080235 : Blo 706319 8080235 := bstep (se 1 (by rfl) ⟨6060176, by rfl⟩ : syracuseStep 8080235 = 12120353) B12120353
theorem B707487 : Blo 706319 707487 := bstep (se 1 (by rfl) ⟨530615, by rfl⟩ : syracuseStep 707487 = 1061231) B1061231
theorem B707631 : Blo 706319 707631 := bstep (se 1 (by rfl) ⟨530723, by rfl⟩ : syracuseStep 707631 = 1061447) B1061447
theorem B2018351 : Blo 706319 2018351 := bstep (se 1 (by rfl) ⟨1513763, by rfl⟩ : syracuseStep 2018351 = 3027527) B3027527
theorem B707655 : Blo 706319 707655 := bstep (se 1 (by rfl) ⟨530741, by rfl⟩ : syracuseStep 707655 = 1061483) B1061483
theorem B1592441 : Blo 706319 1592441 := bstep (se 2 (by rfl) ⟨597165, by rfl⟩ : syracuseStep 1592441 = 1194331) B1194331
theorem B4312187 : Blo 706319 4312187 := bstep (se 1 (by rfl) ⟨3234140, by rfl⟩ : syracuseStep 4312187 = 6468281) B6468281
theorem B707807 : Blo 706319 707807 := bstep (se 1 (by rfl) ⟨530855, by rfl⟩ : syracuseStep 707807 = 1061711) B1061711
theorem B708071 : Blo 706319 708071 := bstep (se 1 (by rfl) ⟨531053, by rfl⟩ : syracuseStep 708071 = 1062107) B1062107
theorem B2018807 : Blo 706319 2018807 := bstep (se 1 (by rfl) ⟨1514105, by rfl⟩ : syracuseStep 2018807 = 3028211) B3028211
theorem B708187 : Blo 706319 708187 := bstep (se 1 (by rfl) ⟨531140, by rfl⟩ : syracuseStep 708187 = 1062281) B1062281
theorem B1789715 : Blo 706319 1789715 := bstep (se 1 (by rfl) ⟨1342286, by rfl⟩ : syracuseStep 1789715 = 2684573) B2684573
theorem B1593107 : Blo 706319 1593107 := bstep (se 1 (by rfl) ⟨1194830, by rfl⟩ : syracuseStep 1593107 = 2389661) B2389661
theorem B1789735 : Blo 706319 1789735 := bstep (se 1 (by rfl) ⟨1342301, by rfl⟩ : syracuseStep 1789735 = 2684603) B2684603
theorem B708423 : Blo 706319 708423 := bstep (se 1 (by rfl) ⟨531317, by rfl⟩ : syracuseStep 708423 = 1062635) B1062635
theorem B708575 : Blo 706319 708575 := bstep (se 1 (by rfl) ⟨531431, by rfl⟩ : syracuseStep 708575 = 1062863) B1062863
theorem B18173969 : Blo 706319 18173969 := bstep (se 2 (by rfl) ⟨6815238, by rfl⟩ : syracuseStep 18173969 = 13630477) B13630477
theorem B1593467 : Blo 706319 1593467 := bstep (se 1 (by rfl) ⟨1195100, by rfl⟩ : syracuseStep 1593467 = 2390201) B2390201
theorem B1134823 : Blo 706319 1134823 := bstep (se 1 (by rfl) ⟨851117, by rfl⟩ : syracuseStep 1134823 = 1702235) B1702235
theorem B708839 : Blo 706319 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B2019593 : Blo 706319 2019593 := bstep (se 2 (by rfl) ⟨757347, by rfl⟩ : syracuseStep 2019593 = 1514695) B1514695
theorem B708991 : Blo 706319 708991 := bstep (se 1 (by rfl) ⟨531743, by rfl⟩ : syracuseStep 708991 = 1063487) B1063487
theorem B1593737 : Blo 706319 1593737 := bstep (se 2 (by rfl) ⟨597651, by rfl⟩ : syracuseStep 1593737 = 1195303) B1195303
theorem B709071 : Blo 706319 709071 := bstep (se 1 (by rfl) ⟨531803, by rfl⟩ : syracuseStep 709071 = 1063607) B1063607
theorem B2019923 : Blo 706319 2019923 := bstep (se 1 (by rfl) ⟨1514942, by rfl⟩ : syracuseStep 2019923 = 3029885) B3029885
theorem B709223 : Blo 706319 709223 := bstep (se 1 (by rfl) ⟨531917, by rfl⟩ : syracuseStep 709223 = 1063835) B1063835
theorem B709487 : Blo 706319 709487 := bstep (se 1 (by rfl) ⟨532115, by rfl⟩ : syracuseStep 709487 = 1064231) B1064231
theorem B1790849 : Blo 706319 1790849 := bstep (se 2 (by rfl) ⟨671568, by rfl⟩ : syracuseStep 1790849 = 1343137) B1343137
theorem B709543 : Blo 706319 709543 := bstep (se 1 (by rfl) ⟨532157, by rfl⟩ : syracuseStep 709543 = 1064315) B1064315
theorem B709627 : Blo 706319 709627 := bstep (se 1 (by rfl) ⟨532220, by rfl⟩ : syracuseStep 709627 = 1064441) B1064441
theorem B1791031 : Blo 706319 1791031 := bstep (se 1 (by rfl) ⟨1343273, by rfl⟩ : syracuseStep 1791031 = 2686547) B2686547
theorem B709695 : Blo 706319 709695 := bstep (se 1 (by rfl) ⟨532271, by rfl⟩ : syracuseStep 709695 = 1064543) B1064543
theorem B1594475 : Blo 706319 1594475 := bstep (se 1 (by rfl) ⟨1195856, by rfl⟩ : syracuseStep 1594475 = 2391713) B2391713
theorem B709839 : Blo 706319 709839 := bstep (se 1 (by rfl) ⟨532379, by rfl⟩ : syracuseStep 709839 = 1064759) B1064759
theorem B710043 : Blo 706319 710043 := bstep (se 1 (by rfl) ⟨532532, by rfl⟩ : syracuseStep 710043 = 1065065) B1065065
theorem B710255 : Blo 706319 710255 := bstep (se 1 (by rfl) ⟨532691, by rfl⟩ : syracuseStep 710255 = 1065383) B1065383
theorem B710311 : Blo 706319 710311 := bstep (se 1 (by rfl) ⟨532733, by rfl⟩ : syracuseStep 710311 = 1065467) B1065467
theorem B1791659 : Blo 706319 1791659 := bstep (se 1 (by rfl) ⟨1343744, by rfl⟩ : syracuseStep 1791659 = 2687489) B2687489
theorem B1595051 : Blo 706319 1595051 := bstep (se 1 (by rfl) ⟨1196288, by rfl⟩ : syracuseStep 1595051 = 2392577) B2392577
theorem B1791983 : Blo 706319 1791983 := bstep (se 1 (by rfl) ⟨1343987, by rfl⟩ : syracuseStep 1791983 = 2687975) B2687975
theorem B1595375 : Blo 706319 1595375 := bstep (se 1 (by rfl) ⟨1196531, by rfl⟩ : syracuseStep 1595375 = 2393063) B2393063
theorem B4544495 : Blo 706319 4544495 := bstep (se 1 (by rfl) ⟨3408371, by rfl⟩ : syracuseStep 4544495 = 6816743) B6816743
theorem B1595591 : Blo 706319 1595591 := bstep (se 1 (by rfl) ⟨1196693, by rfl⟩ : syracuseStep 1595591 = 2393387) B2393387
theorem B1136873 : Blo 706319 1136873 := bstep (se 2 (by rfl) ⟨426327, by rfl⟩ : syracuseStep 1136873 = 852655) B852655
theorem B47962397 : Blo 706319 47962397 := bstep (se 3 (by rfl) ⟨8992949, by rfl⟩ : syracuseStep 47962397 = 17985899) B17985899
theorem B1366313 : Blo 706319 1366313 := bstep (se 2 (by rfl) ⟨512367, by rfl⟩ : syracuseStep 1366313 = 1024735) B1024735
theorem B8608123 : Blo 706319 8608123 := bstep (se 1 (by rfl) ⟨6456092, by rfl⟩ : syracuseStep 8608123 = 12912185) B12912185
theorem B1595771 : Blo 706319 1595771 := bstep (se 1 (by rfl) ⟨1196828, by rfl⟩ : syracuseStep 1595771 = 2393657) B2393657
theorem B1006111 : Blo 706319 1006111 := bstep (se 1 (by rfl) ⟨754583, by rfl⟩ : syracuseStep 1006111 = 1509167) B1509167
theorem B83745323 : Blo 706319 83745323 := bstep (se 1 (by rfl) ⟨62808992, by rfl⟩ : syracuseStep 83745323 = 125617985) B125617985
theorem B1596041 : Blo 706319 1596041 := bstep (se 2 (by rfl) ⟨598515, by rfl⟩ : syracuseStep 1596041 = 1197031) B1197031
theorem B1792975 : Blo 706319 1792975 := bstep (se 1 (by rfl) ⟨1344731, by rfl⟩ : syracuseStep 1792975 = 2689463) B2689463
theorem B1596599 : Blo 706319 1596599 := bstep (se 1 (by rfl) ⟨1197449, by rfl⟩ : syracuseStep 1596599 = 2394899) B2394899
theorem B62774509 : Blo 706319 62774509 := bstep (se 3 (by rfl) ⟨11770220, by rfl⟩ : syracuseStep 62774509 = 23540441) B23540441
theorem B4545953 : Blo 706319 4545953 := bstep (se 2 (by rfl) ⟨1704732, by rfl⟩ : syracuseStep 4545953 = 3409465) B3409465
theorem B3595751 : Blo 706319 3595751 := bstep (se 1 (by rfl) ⟨2696813, by rfl⟩ : syracuseStep 3595751 = 5393627) B5393627
theorem B1597175 : Blo 706319 1597175 := bstep (se 1 (by rfl) ⟨1197881, by rfl⟩ : syracuseStep 1597175 = 2395763) B2395763
theorem B1597355 : Blo 706319 1597355 := bstep (se 1 (by rfl) ⟨1198016, by rfl⟩ : syracuseStep 1597355 = 2396033) B2396033
theorem B2384153 : Blo 706319 2384153 := bstep (se 2 (by rfl) ⟨894057, by rfl⟩ : syracuseStep 2384153 = 1788115) B1788115
theorem B9691469 : Blo 706319 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B2384315 : Blo 706319 2384315 := bstep (se 1 (by rfl) ⟨1788236, by rfl⟩ : syracuseStep 2384315 = 3576473) B3576473
theorem B1597895 : Blo 706319 1597895 := bstep (se 1 (by rfl) ⟨1198421, by rfl⟩ : syracuseStep 1597895 = 2396843) B2396843
theorem B5366411 : Blo 706319 5366411 := bstep (se 1 (by rfl) ⟨4024808, by rfl⟩ : syracuseStep 5366411 = 8049617) B8049617
theorem B2548795 : Blo 706319 2548795 := bstep (se 1 (by rfl) ⟨1911596, by rfl⟩ : syracuseStep 2548795 = 3823193) B3823193
theorem B1008703 : Blo 706319 1008703 := bstep (se 1 (by rfl) ⟨756527, by rfl⟩ : syracuseStep 1008703 = 1513055) B1513055
theorem B11461931 : Blo 706319 11461931 := bstep (se 1 (by rfl) ⟨8596448, by rfl⟩ : syracuseStep 11461931 = 17192897) B17192897
theorem B910747 : Blo 706319 910747 := bstep (se 1 (by rfl) ⟨683060, by rfl⟩ : syracuseStep 910747 = 1366121) B1366121
theorem B2549245 : Blo 706319 2549245 := bstep (se 3 (by rfl) ⟨477983, by rfl⟩ : syracuseStep 2549245 = 955967) B955967
theorem B2385503 : Blo 706319 2385503 := bstep (se 1 (by rfl) ⟨1789127, by rfl⟩ : syracuseStep 2385503 = 3578255) B3578255
theorem B3237497 : Blo 706319 3237497 := bstep (se 2 (by rfl) ⟨1214061, by rfl⟩ : syracuseStep 3237497 = 2428123) B2428123
theorem B1795871 : Blo 706319 1795871 := bstep (se 1 (by rfl) ⟨1346903, by rfl⟩ : syracuseStep 1795871 = 2693807) B2693807
theorem B10217785 : Blo 706319 10217785 := bstep (se 2 (by rfl) ⟨3831669, by rfl⟩ : syracuseStep 10217785 = 7663339) B7663339
theorem B3631499 : Blo 706319 3631499 := bstep (se 1 (by rfl) ⟨2723624, by rfl⟩ : syracuseStep 3631499 = 5447249) B5447249
theorem B5827247 : Blo 706319 5827247 := bstep (se 1 (by rfl) ⟨4370435, by rfl⟩ : syracuseStep 5827247 = 8740871) B8740871
theorem B2386907 : Blo 706319 2386907 := bstep (se 1 (by rfl) ⟨1790180, by rfl⟩ : syracuseStep 2386907 = 3580361) B3580361
theorem B1797167 : Blo 706319 1797167 := bstep (se 1 (by rfl) ⟨1347875, by rfl⟩ : syracuseStep 1797167 = 2695751) B2695751
theorem B2387177 : Blo 706319 2387177 := bstep (se 2 (by rfl) ⟨895191, by rfl⟩ : syracuseStep 2387177 = 1790383) B1790383
theorem B1011055 : Blo 706319 1011055 := bstep (se 1 (by rfl) ⟨758291, by rfl⟩ : syracuseStep 1011055 = 1516583) B1516583
theorem B8088983 : Blo 706319 8088983 := bstep (se 1 (by rfl) ⟨6066737, by rfl⟩ : syracuseStep 8088983 = 12133475) B12133475
theorem B2387447 : Blo 706319 2387447 := bstep (se 1 (by rfl) ⟨1790585, by rfl⟩ : syracuseStep 2387447 = 3581171) B3581171
theorem B1797623 : Blo 706319 1797623 := bstep (se 1 (by rfl) ⟨1348217, by rfl⟩ : syracuseStep 1797623 = 2696435) B2696435
theorem B4026131 : Blo 706319 4026131 := bstep (se 1 (by rfl) ⟨3019598, by rfl⟩ : syracuseStep 4026131 = 6039197) B6039197
theorem B20705267 : Blo 706319 20705267 := bstep (se 1 (by rfl) ⟨15528950, by rfl⟩ : syracuseStep 20705267 = 31057901) B31057901
theorem B2158721 : Blo 706319 2158721 := bstep (se 2 (by rfl) ⟨809520, by rfl⟩ : syracuseStep 2158721 = 1619041) B1619041
theorem B2683145 : Blo 706319 2683145 := bstep (se 2 (by rfl) ⟨1006179, by rfl⟩ : syracuseStep 2683145 = 2012359) B2012359
theorem B4551079 : Blo 706319 4551079 := bstep (se 1 (by rfl) ⟨3413309, by rfl⟩ : syracuseStep 4551079 = 6826619) B6826619
theorem B2388473 : Blo 706319 2388473 := bstep (se 2 (by rfl) ⟨895677, by rfl⟩ : syracuseStep 2388473 = 1791355) B1791355
theorem B3830287 : Blo 706319 3830287 := bstep (se 1 (by rfl) ⟨2872715, by rfl⟩ : syracuseStep 3830287 = 5745431) B5745431
theorem B1274471 : Blo 706319 1274471 := bstep (se 1 (by rfl) ⟨955853, by rfl⟩ : syracuseStep 1274471 = 1911707) B1911707
theorem B2454263 : Blo 706319 2454263 := bstep (se 1 (by rfl) ⟨1840697, by rfl⟩ : syracuseStep 2454263 = 3681395) B3681395
theorem B2388743 : Blo 706319 2388743 := bstep (se 1 (by rfl) ⟨1791557, by rfl⟩ : syracuseStep 2388743 = 3583115) B3583115
theorem B2388797 : Blo 706319 2388797 := bstep (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) B895799
theorem B5370785 : Blo 706319 5370785 := bstep (se 2 (by rfl) ⟨2014044, by rfl⟩ : syracuseStep 5370785 = 4028089) B4028089
theorem B1078267 : Blo 706319 1078267 := bstep (se 1 (by rfl) ⟨808700, by rfl⟩ : syracuseStep 1078267 = 1617401) B1617401
theorem B12907673 : Blo 706319 12907673 := bstep (se 2 (by rfl) ⟨4840377, by rfl⟩ : syracuseStep 12907673 = 9680755) B9680755
theorem B22935001 : Blo 706319 22935001 := bstep (se 2 (by rfl) ⟨8600625, by rfl⟩ : syracuseStep 22935001 = 17201251) B17201251
theorem B20739629 : Blo 706319 20739629 := bstep (se 3 (by rfl) ⟨3888680, by rfl⟩ : syracuseStep 20739629 = 7777361) B7777361
theorem B849695 : Blo 706319 849695 := bstep (se 1 (by rfl) ⟨637271, by rfl⟩ : syracuseStep 849695 = 1274543) B1274543
theorem B2389823 : Blo 706319 2389823 := bstep (se 1 (by rfl) ⟨1792367, by rfl⟩ : syracuseStep 2389823 = 3584735) B3584735
theorem B1341535 : Blo 706319 1341535 := bstep (se 1 (by rfl) ⟨1006151, by rfl⟩ : syracuseStep 1341535 = 2012303) B2012303
theorem B1702043 : Blo 706319 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B2685257 : Blo 706319 2685257 := bstep (se 2 (by rfl) ⟨1006971, by rfl⟩ : syracuseStep 2685257 = 2013943) B2013943
theorem B6388079 : Blo 706319 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B15333947 : Blo 706319 15333947 := bstep (se 1 (by rfl) ⟨11500460, by rfl⟩ : syracuseStep 15333947 = 23000921) B23000921
theorem B6454559 : Blo 706319 6454559 := bstep (se 1 (by rfl) ⟨4840919, by rfl⟩ : syracuseStep 6454559 = 9681839) B9681839
theorem B5373215 : Blo 706319 5373215 := bstep (se 1 (by rfl) ⟨4029911, by rfl⟩ : syracuseStep 5373215 = 8059823) B8059823
theorem B2391335 : Blo 706319 2391335 := bstep (se 1 (by rfl) ⟨1793501, by rfl⟩ : syracuseStep 2391335 = 3587003) B3587003
theorem B2555819 : Blo 706319 2555819 := bstep (se 1 (by rfl) ⟨1916864, by rfl⟩ : syracuseStep 2555819 = 3833729) B3833729
theorem B1343783 : Blo 706319 1343783 := bstep (se 1 (by rfl) ⟨1007837, by rfl⟩ : syracuseStep 1343783 = 2015675) B2015675
theorem B2457983 : Blo 706319 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B2687519 : Blo 706319 2687519 := bstep (se 1 (by rfl) ⟨2015639, by rfl⟩ : syracuseStep 2687519 = 4031279) B4031279
theorem B1279199 : Blo 706319 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B3409199 : Blo 706319 3409199 := bstep (se 1 (by rfl) ⟨2556899, by rfl⟩ : syracuseStep 3409199 = 5113799) B5113799
theorem B1344937 : Blo 706319 1344937 := bstep (se 2 (by rfl) ⟨504351, by rfl⟩ : syracuseStep 1344937 = 1008703) B1008703
theorem B6817547 : Blo 706319 6817547 := bstep (se 1 (by rfl) ⟨5113160, by rfl⟩ : syracuseStep 6817547 = 10226321) B10226321
theorem B1345567 : Blo 706319 1345567 := bstep (se 1 (by rfl) ⟨1009175, by rfl⟩ : syracuseStep 1345567 = 2018351) B2018351
theorem B1345871 : Blo 706319 1345871 := bstep (se 1 (by rfl) ⟨1009403, by rfl⟩ : syracuseStep 1345871 = 2018807) B2018807
theorem B2689631 : Blo 706319 2689631 := bstep (se 1 (by rfl) ⟨2017223, by rfl⟩ : syracuseStep 2689631 = 4034447) B4034447
theorem B1346395 : Blo 706319 1346395 := bstep (se 1 (by rfl) ⟨1009796, by rfl⟩ : syracuseStep 1346395 = 2019593) B2019593
theorem B1346615 : Blo 706319 1346615 := bstep (se 1 (by rfl) ⟨1009961, by rfl⟩ : syracuseStep 1346615 = 2019923) B2019923
theorem B55184753 : Blo 706319 55184753 := bstep (se 2 (by rfl) ⟨20694282, by rfl⟩ : syracuseStep 55184753 = 41388565) B41388565
theorem B2690617 : Blo 706319 2690617 := bstep (se 2 (by rfl) ⟨1008981, by rfl⟩ : syracuseStep 2690617 = 2017963) B2017963
theorem B1511867 : Blo 706319 1511867 := bstep (se 1 (by rfl) ⟨1133900, by rfl⟩ : syracuseStep 1511867 = 2267801) B2267801
theorem B1348073 : Blo 706319 1348073 := bstep (se 2 (by rfl) ⟨505527, by rfl⟩ : syracuseStep 1348073 = 1011055) B1011055
theorem B6820433 : Blo 706319 6820433 := bstep (se 2 (by rfl) ⟨2557662, by rfl⟩ : syracuseStep 6820433 = 5115325) B5115325
theorem B2265853 : Blo 706319 2265853 := bstep (se 3 (by rfl) ⟨424847, by rfl⟩ : syracuseStep 2265853 = 849695) B849695
theorem B2397167 : Blo 706319 2397167 := bstep (se 1 (by rfl) ⟨1797875, by rfl⟩ : syracuseStep 2397167 = 3595751) B3595751
theorem B6460979 : Blo 706319 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B1513097 : Blo 706319 1513097 := bstep (se 2 (by rfl) ⟨567411, by rfl⟩ : syracuseStep 1513097 = 1134823) B1134823
theorem B3577607 : Blo 706319 3577607 := bstep (se 1 (by rfl) ⟨2683205, by rfl⟩ : syracuseStep 3577607 = 5366411) B5366411
theorem B6068105 : Blo 706319 6068105 := bstep (se 2 (by rfl) ⟨2275539, by rfl⟩ : syracuseStep 6068105 = 4551079) B4551079
theorem B3643501 : Blo 706319 3643501 := bstep (se 3 (by rfl) ⟨683156, by rfl⟩ : syracuseStep 3643501 = 1366313) B1366313
theorem B7641287 : Blo 706319 7641287 := bstep (se 1 (by rfl) ⟨5730965, by rfl⟩ : syracuseStep 7641287 = 11461931) B11461931
theorem B12917879 : Blo 706319 12917879 := bstep (se 1 (by rfl) ⟨9688409, by rfl⟩ : syracuseStep 12917879 = 19376819) B19376819
theorem B30580001 : Blo 706319 30580001 := bstep (se 2 (by rfl) ⟨11467500, by rfl⟩ : syracuseStep 30580001 = 22935001) B22935001
theorem B4857317 : Blo 706319 4857317 := bstep (se 4 (by rfl) ⟨455373, by rfl⟩ : syracuseStep 4857317 = 910747) B910747
theorem B3022555 : Blo 706319 3022555 := bstep (se 1 (by rfl) ⟨2266916, by rfl⟩ : syracuseStep 3022555 = 4533833) B4533833
theorem B11477497 : Blo 706319 11477497 := bstep (se 2 (by rfl) ⟨4304061, by rfl⟩ : syracuseStep 11477497 = 8608123) B8608123
theorem B795163 : Blo 706319 795163 := bstep (se 1 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 795163 = 1192745) B1192745
theorem B3580523 : Blo 706319 3580523 := bstep (se 1 (by rfl) ⟨2685392, by rfl⟩ : syracuseStep 3580523 = 5370785) B5370785
theorem B795343 : Blo 706319 795343 := bstep (se 1 (by rfl) ⟨596507, by rfl⟩ : syracuseStep 795343 = 1193015) B1193015
theorem B4596527 : Blo 706319 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B83699345 : Blo 706319 83699345 := bstep (se 2 (by rfl) ⟨31387254, by rfl⟩ : syracuseStep 83699345 = 62774509) B62774509
theorem B796351 : Blo 706319 796351 := bstep (se 1 (by rfl) ⟨597263, by rfl⟩ : syracuseStep 796351 = 1194527) B1194527
theorem B796639 : Blo 706319 796639 := bstep (se 1 (by rfl) ⟨597479, by rfl⟩ : syracuseStep 796639 = 1194959) B1194959
theorem B4303039 : Blo 706319 4303039 := bstep (se 1 (by rfl) ⟨3227279, by rfl⟩ : syracuseStep 4303039 = 6454559) B6454559
theorem B3582143 : Blo 706319 3582143 := bstep (se 1 (by rfl) ⟨2686607, by rfl⟩ : syracuseStep 3582143 = 5373215) B5373215
theorem B797287 : Blo 706319 797287 := bstep (se 1 (by rfl) ⟨597965, by rfl⟩ : syracuseStep 797287 = 1195931) B1195931
theorem B12102857 : Blo 706319 12102857 := bstep (se 2 (by rfl) ⟨4538571, by rfl⟩ : syracuseStep 12102857 = 9077143) B9077143
theorem B1060151 : Blo 706319 1060151 := bstep (se 1 (by rfl) ⟨795113, by rfl⟩ : syracuseStep 1060151 = 1590227) B1590227
theorem B798079 : Blo 706319 798079 := bstep (se 1 (by rfl) ⟨598559, by rfl⟩ : syracuseStep 798079 = 1197119) B1197119
theorem B1060319 : Blo 706319 1060319 := bstep (se 1 (by rfl) ⟨795239, by rfl⟩ : syracuseStep 1060319 = 1590479) B1590479
theorem B1060535 : Blo 706319 1060535 := bstep (se 1 (by rfl) ⟨795401, by rfl⟩ : syracuseStep 1060535 = 1590803) B1590803
theorem B1617727 : Blo 706319 1617727 := bstep (se 1 (by rfl) ⟨1213295, by rfl⟩ : syracuseStep 1617727 = 2426591) B2426591
theorem B1060745 : Blo 706319 1060745 := bstep (se 2 (by rfl) ⟨397779, by rfl⟩ : syracuseStep 1060745 = 795559) B795559
theorem B6795251 : Blo 706319 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B1192009 : Blo 706319 1192009 := bstep (se 2 (by rfl) ⟨447003, by rfl⟩ : syracuseStep 1192009 = 894007) B894007
theorem B897151 : Blo 706319 897151 := bstep (se 1 (by rfl) ⟨672863, by rfl⟩ : syracuseStep 897151 = 1345727) B1345727
theorem B1192063 : Blo 706319 1192063 := bstep (se 1 (by rfl) ⟨894047, by rfl⟩ : syracuseStep 1192063 = 1788095) B1788095
theorem B1060991 : Blo 706319 1060991 := bstep (se 1 (by rfl) ⟨795743, by rfl⟩ : syracuseStep 1060991 = 1591487) B1591487
theorem B4599935 : Blo 706319 4599935 := bstep (se 1 (by rfl) ⟨3449951, by rfl⟩ : syracuseStep 4599935 = 6899903) B6899903
theorem B3584411 : Blo 706319 3584411 := bstep (se 1 (by rfl) ⟨2688308, by rfl⟩ : syracuseStep 3584411 = 5376617) B5376617
theorem B5386823 : Blo 706319 5386823 := bstep (se 1 (by rfl) ⟨4040117, by rfl⟩ : syracuseStep 5386823 = 8080235) B8080235
theorem B1061627 : Blo 706319 1061627 := bstep (se 1 (by rfl) ⟨796220, by rfl⟩ : syracuseStep 1061627 = 1592441) B1592441
theorem B3584897 : Blo 706319 3584897 := bstep (se 2 (by rfl) ⟨1344336, by rfl⟩ : syracuseStep 3584897 = 2688673) B2688673
theorem B3453961 : Blo 706319 3453961 := bstep (se 2 (by rfl) ⟨1295235, by rfl⟩ : syracuseStep 3453961 = 2590471) B2590471
theorem B1193143 : Blo 706319 1193143 := bstep (se 1 (by rfl) ⟨894857, by rfl⟩ : syracuseStep 1193143 = 1789715) B1789715
theorem B1062071 : Blo 706319 1062071 := bstep (se 1 (by rfl) ⟨796553, by rfl⟩ : syracuseStep 1062071 = 1593107) B1593107
theorem B22918393 : Blo 706319 22918393 := bstep (se 2 (by rfl) ⟨8594397, by rfl⟩ : syracuseStep 22918393 = 17188795) B17188795
theorem B1619207 : Blo 706319 1619207 := bstep (se 1 (by rfl) ⟨1214405, by rfl⟩ : syracuseStep 1619207 = 2428811) B2428811
theorem B1062311 : Blo 706319 1062311 := bstep (se 1 (by rfl) ⟨796733, by rfl⟩ : syracuseStep 1062311 = 1593467) B1593467
theorem B5748155 : Blo 706319 5748155 := bstep (se 1 (by rfl) ⟨4311116, by rfl⟩ : syracuseStep 5748155 = 8622233) B8622233
theorem B1062491 : Blo 706319 1062491 := bstep (se 1 (by rfl) ⟨796868, by rfl⟩ : syracuseStep 1062491 = 1593737) B1593737
theorem B3585707 : Blo 706319 3585707 := bstep (se 1 (by rfl) ⟨2689280, by rfl⟩ : syracuseStep 3585707 = 5378561) B5378561
theorem B1193899 : Blo 706319 1193899 := bstep (se 1 (by rfl) ⟨895424, by rfl⟩ : syracuseStep 1193899 = 1790849) B1790849
theorem B5388281 : Blo 706319 5388281 := bstep (se 2 (by rfl) ⟨2020605, by rfl⟩ : syracuseStep 5388281 = 4041211) B4041211
theorem B1062953 : Blo 706319 1062953 := bstep (se 2 (by rfl) ⟨398607, by rfl⟩ : syracuseStep 1062953 = 797215) B797215
theorem B2865223 : Blo 706319 2865223 := bstep (se 1 (by rfl) ⟨2148917, by rfl⟩ : syracuseStep 2865223 = 4297835) B4297835
theorem B1062983 : Blo 706319 1062983 := bstep (se 1 (by rfl) ⟨797237, by rfl⟩ : syracuseStep 1062983 = 1594475) B1594475
theorem B4045085 : Blo 706319 4045085 := bstep (se 3 (by rfl) ⟨758453, by rfl⟩ : syracuseStep 4045085 = 1516907) B1516907
theorem B1194439 : Blo 706319 1194439 := bstep (se 1 (by rfl) ⟨895829, by rfl⟩ : syracuseStep 1194439 = 1791659) B1791659
theorem B1063367 : Blo 706319 1063367 := bstep (se 1 (by rfl) ⟨797525, by rfl⟩ : syracuseStep 1063367 = 1595051) B1595051
theorem B1194655 : Blo 706319 1194655 := bstep (se 1 (by rfl) ⟨895991, by rfl⟩ : syracuseStep 1194655 = 1791983) B1791983
theorem B1063583 : Blo 706319 1063583 := bstep (se 1 (by rfl) ⟨797687, by rfl⟩ : syracuseStep 1063583 = 1595375) B1595375
theorem B3029663 : Blo 706319 3029663 := bstep (se 1 (by rfl) ⟨2272247, by rfl⟩ : syracuseStep 3029663 = 4544495) B4544495
theorem B1063727 : Blo 706319 1063727 := bstep (se 1 (by rfl) ⟨797795, by rfl⟩ : syracuseStep 1063727 = 1595591) B1595591
theorem B1063847 : Blo 706319 1063847 := bstep (se 1 (by rfl) ⟨797885, by rfl⟩ : syracuseStep 1063847 = 1595771) B1595771
theorem B1064027 : Blo 706319 1064027 := bstep (se 1 (by rfl) ⟨798020, by rfl⟩ : syracuseStep 1064027 = 1596041) B1596041
theorem B2014433 : Blo 706319 2014433 := bstep (se 2 (by rfl) ⟨755412, by rfl⟩ : syracuseStep 2014433 = 1510825) B1510825
theorem B1064399 : Blo 706319 1064399 := bstep (se 1 (by rfl) ⟨798299, by rfl⟩ : syracuseStep 1064399 = 1596599) B1596599
theorem B3030635 : Blo 706319 3030635 := bstep (se 1 (by rfl) ⟨2272976, by rfl⟩ : syracuseStep 3030635 = 4545953) B4545953
theorem B1064783 : Blo 706319 1064783 := bstep (se 1 (by rfl) ⟨798587, by rfl⟩ : syracuseStep 1064783 = 1597175) B1597175
theorem B5390225 : Blo 706319 5390225 := bstep (se 2 (by rfl) ⟨2021334, by rfl⟩ : syracuseStep 5390225 = 4042669) B4042669
theorem B1064903 : Blo 706319 1064903 := bstep (se 1 (by rfl) ⟨798677, by rfl⟩ : syracuseStep 1064903 = 1597355) B1597355
theorem B1589435 : Blo 706319 1589435 := bstep (se 1 (by rfl) ⟨1192076, by rfl⟩ : syracuseStep 1589435 = 2384153) B2384153
theorem B1589543 : Blo 706319 1589543 := bstep (se 1 (by rfl) ⟨1192157, by rfl⟩ : syracuseStep 1589543 = 2384315) B2384315
theorem B1065263 : Blo 706319 1065263 := bstep (se 1 (by rfl) ⟨798947, by rfl⟩ : syracuseStep 1065263 = 1597895) B1597895
theorem B3031661 : Blo 706319 3031661 := bstep (se 3 (by rfl) ⟨568436, by rfl⟩ : syracuseStep 3031661 = 1136873) B1136873
theorem B1589921 : Blo 706319 1589921 := bstep (se 2 (by rfl) ⟨596220, by rfl⟩ : syracuseStep 1589921 = 1192441) B1192441
theorem B1590281 : Blo 706319 1590281 := bstep (se 2 (by rfl) ⟨596355, by rfl⟩ : syracuseStep 1590281 = 1192711) B1192711
theorem B1590335 : Blo 706319 1590335 := bstep (se 1 (by rfl) ⟨1192751, by rfl⟩ : syracuseStep 1590335 = 2385503) B2385503
theorem B1197247 : Blo 706319 1197247 := bstep (se 1 (by rfl) ⟨897935, by rfl⟩ : syracuseStep 1197247 = 1795871) B1795871
theorem B3884831 : Blo 706319 3884831 := bstep (se 1 (by rfl) ⟨2913623, by rfl⟩ : syracuseStep 3884831 = 5827247) B5827247
theorem B706495 : Blo 706319 706495 := bstep (se 1 (by rfl) ⟨529871, by rfl⟩ : syracuseStep 706495 = 1059743) B1059743
theorem B706527 : Blo 706319 706527 := bstep (se 1 (by rfl) ⟨529895, by rfl⟩ : syracuseStep 706527 = 1059791) B1059791
theorem B1591271 : Blo 706319 1591271 := bstep (se 1 (by rfl) ⟨1193453, by rfl⟩ : syracuseStep 1591271 = 2386907) B2386907
theorem B706587 : Blo 706319 706587 := bstep (se 1 (by rfl) ⟨529940, by rfl⟩ : syracuseStep 706587 = 1059881) B1059881
theorem B706591 : Blo 706319 706591 := bstep (se 1 (by rfl) ⟨529943, by rfl⟩ : syracuseStep 706591 = 1059887) B1059887
theorem B1198111 : Blo 706319 1198111 := bstep (se 1 (by rfl) ⟨898583, by rfl⟩ : syracuseStep 1198111 = 1797167) B1797167
theorem B706607 : Blo 706319 706607 := bstep (se 1 (by rfl) ⟨529955, by rfl⟩ : syracuseStep 706607 = 1059911) B1059911
theorem B1591451 : Blo 706319 1591451 := bstep (se 1 (by rfl) ⟨1193588, by rfl⟩ : syracuseStep 1591451 = 2387177) B2387177
theorem B706783 : Blo 706319 706783 := bstep (se 1 (by rfl) ⟨530087, by rfl⟩ : syracuseStep 706783 = 1060175) B1060175
theorem B5392655 : Blo 706319 5392655 := bstep (se 1 (by rfl) ⟨4044491, by rfl⟩ : syracuseStep 5392655 = 8088983) B8088983
theorem B706843 : Blo 706319 706843 := bstep (se 1 (by rfl) ⟨530132, by rfl⟩ : syracuseStep 706843 = 1060265) B1060265
theorem B1591631 : Blo 706319 1591631 := bstep (se 1 (by rfl) ⟨1193723, by rfl⟩ : syracuseStep 1591631 = 2387447) B2387447
theorem B1198415 : Blo 706319 1198415 := bstep (se 1 (by rfl) ⟨898811, by rfl⟩ : syracuseStep 1198415 = 1797623) B1797623
theorem B706943 : Blo 706319 706943 := bstep (se 1 (by rfl) ⟨530207, by rfl⟩ : syracuseStep 706943 = 1060415) B1060415
theorem B1591721 : Blo 706319 1591721 := bstep (se 2 (by rfl) ⟨596895, by rfl⟩ : syracuseStep 1591721 = 1193791) B1193791
theorem B9095597 : Blo 706319 9095597 := bstep (se 3 (by rfl) ⟨1705424, by rfl⟩ : syracuseStep 9095597 = 3410849) B3410849
theorem B707119 : Blo 706319 707119 := bstep (se 1 (by rfl) ⟨530339, by rfl⟩ : syracuseStep 707119 = 1060679) B1060679
theorem B707175 : Blo 706319 707175 := bstep (se 1 (by rfl) ⟨530381, by rfl⟩ : syracuseStep 707175 = 1060763) B1060763
theorem B1788713 : Blo 706319 1788713 := bstep (se 2 (by rfl) ⟨670767, by rfl⟩ : syracuseStep 1788713 = 1341535) B1341535
theorem B1788763 : Blo 706319 1788763 := bstep (se 1 (by rfl) ⟨1341572, by rfl⟩ : syracuseStep 1788763 = 2683145) B2683145
theorem B707551 : Blo 706319 707551 := bstep (se 1 (by rfl) ⟨530663, by rfl⟩ : syracuseStep 707551 = 1061327) B1061327
theorem B707579 : Blo 706319 707579 := bstep (se 1 (by rfl) ⟨530684, by rfl⟩ : syracuseStep 707579 = 1061369) B1061369
theorem B1592315 : Blo 706319 1592315 := bstep (se 1 (by rfl) ⟨1194236, by rfl⟩ : syracuseStep 1592315 = 2388473) B2388473
theorem B707647 : Blo 706319 707647 := bstep (se 1 (by rfl) ⟨530735, by rfl⟩ : syracuseStep 707647 = 1061471) B1061471
theorem B3394703 : Blo 706319 3394703 := bstep (se 1 (by rfl) ⟨2546027, by rfl⟩ : syracuseStep 3394703 = 5092055) B5092055
theorem B1592495 : Blo 706319 1592495 := bstep (se 1 (by rfl) ⟨1194371, by rfl⟩ : syracuseStep 1592495 = 2388743) B2388743
theorem B1592531 : Blo 706319 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B707967 : Blo 706319 707967 := bstep (se 1 (by rfl) ⟨530975, by rfl⟩ : syracuseStep 707967 = 1061951) B1061951
theorem B707995 : Blo 706319 707995 := bstep (se 1 (by rfl) ⟨530996, by rfl⟩ : syracuseStep 707995 = 1061993) B1061993
theorem B8605115 : Blo 706319 8605115 := bstep (se 1 (by rfl) ⟨6453836, by rfl⟩ : syracuseStep 8605115 = 12907673) B12907673
theorem B708063 : Blo 706319 708063 := bstep (se 1 (by rfl) ⟨531047, by rfl⟩ : syracuseStep 708063 = 1062095) B1062095
theorem B1592801 : Blo 706319 1592801 := bstep (se 2 (by rfl) ⟨597300, by rfl⟩ : syracuseStep 1592801 = 1194601) B1194601
theorem B708199 : Blo 706319 708199 := bstep (se 1 (by rfl) ⟨531149, by rfl⟩ : syracuseStep 708199 = 1062299) B1062299
theorem B708347 : Blo 706319 708347 := bstep (se 1 (by rfl) ⟨531260, by rfl⟩ : syracuseStep 708347 = 1062521) B1062521
theorem B708415 : Blo 706319 708415 := bstep (se 1 (by rfl) ⟨531311, by rfl⟩ : syracuseStep 708415 = 1062623) B1062623
theorem B1593215 : Blo 706319 1593215 := bstep (se 1 (by rfl) ⟨1194911, by rfl⟩ : syracuseStep 1593215 = 2389823) B2389823
theorem B708479 : Blo 706319 708479 := bstep (se 1 (by rfl) ⟨531359, by rfl⟩ : syracuseStep 708479 = 1062719) B1062719
theorem B708591 : Blo 706319 708591 := bstep (se 1 (by rfl) ⟨531443, by rfl⟩ : syracuseStep 708591 = 1062887) B1062887
theorem B708603 : Blo 706319 708603 := bstep (se 1 (by rfl) ⟨531452, by rfl⟩ : syracuseStep 708603 = 1062905) B1062905
theorem B708671 : Blo 706319 708671 := bstep (se 1 (by rfl) ⟨531503, by rfl⟩ : syracuseStep 708671 = 1063007) B1063007
theorem B1134695 : Blo 706319 1134695 := bstep (se 1 (by rfl) ⟨851021, by rfl⟩ : syracuseStep 1134695 = 1702043) B1702043
theorem B708711 : Blo 706319 708711 := bstep (se 1 (by rfl) ⟨531533, by rfl⟩ : syracuseStep 708711 = 1063067) B1063067
theorem B708735 : Blo 706319 708735 := bstep (se 1 (by rfl) ⟨531551, by rfl⟩ : syracuseStep 708735 = 1063103) B1063103
theorem B708763 : Blo 706319 708763 := bstep (se 1 (by rfl) ⟨531572, by rfl⟩ : syracuseStep 708763 = 1063145) B1063145
theorem B1790171 : Blo 706319 1790171 := bstep (se 1 (by rfl) ⟨1342628, by rfl⟩ : syracuseStep 1790171 = 2685257) B2685257
theorem B708967 : Blo 706319 708967 := bstep (se 1 (by rfl) ⟨531725, by rfl⟩ : syracuseStep 708967 = 1063451) B1063451
theorem B709019 : Blo 706319 709019 := bstep (se 1 (by rfl) ⟨531764, by rfl⟩ : syracuseStep 709019 = 1063529) B1063529
theorem B709371 : Blo 706319 709371 := bstep (se 1 (by rfl) ⟨532028, by rfl⟩ : syracuseStep 709371 = 1064057) B1064057
theorem B1594169 : Blo 706319 1594169 := bstep (se 2 (by rfl) ⟨597813, by rfl⟩ : syracuseStep 1594169 = 1195627) B1195627
theorem B709439 : Blo 706319 709439 := bstep (se 1 (by rfl) ⟨532079, by rfl⟩ : syracuseStep 709439 = 1064159) B1064159
theorem B709467 : Blo 706319 709467 := bstep (se 1 (by rfl) ⟨532100, by rfl⟩ : syracuseStep 709467 = 1064201) B1064201
theorem B1594223 : Blo 706319 1594223 := bstep (se 1 (by rfl) ⟨1195667, by rfl⟩ : syracuseStep 1594223 = 2391335) B2391335
theorem B709535 : Blo 706319 709535 := bstep (se 1 (by rfl) ⟨532151, by rfl⟩ : syracuseStep 709535 = 1064303) B1064303
theorem B709615 : Blo 706319 709615 := bstep (se 1 (by rfl) ⟨532211, by rfl⟩ : syracuseStep 709615 = 1064423) B1064423
theorem B709703 : Blo 706319 709703 := bstep (se 1 (by rfl) ⟨532277, by rfl⟩ : syracuseStep 709703 = 1064555) B1064555
theorem B1496159 : Blo 706319 1496159 := bstep (se 1 (by rfl) ⟨1122119, by rfl⟩ : syracuseStep 1496159 = 2244239) B2244239
theorem B709787 : Blo 706319 709787 := bstep (se 1 (by rfl) ⟨532340, by rfl⟩ : syracuseStep 709787 = 1064681) B1064681
theorem B1594529 : Blo 706319 1594529 := bstep (se 2 (by rfl) ⟨597948, by rfl⟩ : syracuseStep 1594529 = 1195897) B1195897
theorem B709883 : Blo 706319 709883 := bstep (se 1 (by rfl) ⟨532412, by rfl⟩ : syracuseStep 709883 = 1064825) B1064825
theorem B709951 : Blo 706319 709951 := bstep (se 1 (by rfl) ⟨532463, by rfl⟩ : syracuseStep 709951 = 1064927) B1064927
theorem B1594799 : Blo 706319 1594799 := bstep (se 1 (by rfl) ⟨1196099, by rfl⟩ : syracuseStep 1594799 = 2392199) B2392199
theorem B710119 : Blo 706319 710119 := bstep (se 1 (by rfl) ⟨532589, by rfl⟩ : syracuseStep 710119 = 1065179) B1065179
theorem B710127 : Blo 706319 710127 := bstep (se 1 (by rfl) ⟨532595, by rfl⟩ : syracuseStep 710127 = 1065191) B1065191
theorem B710235 : Blo 706319 710235 := bstep (se 1 (by rfl) ⟨532676, by rfl⟩ : syracuseStep 710235 = 1065353) B1065353
theorem B710299 : Blo 706319 710299 := bstep (se 1 (by rfl) ⟨532724, by rfl⟩ : syracuseStep 710299 = 1065449) B1065449
theorem B2152103 : Blo 706319 2152103 := bstep (se 1 (by rfl) ⟨1614077, by rfl⟩ : syracuseStep 2152103 = 3228155) B3228155
theorem B6445007 : Blo 706319 6445007 := bstep (se 1 (by rfl) ⟨4833755, by rfl⟩ : syracuseStep 6445007 = 9667511) B9667511
theorem B1005787 : Blo 706319 1005787 := bstep (se 1 (by rfl) ⟨754340, by rfl⟩ : syracuseStep 1005787 = 1508681) B1508681
theorem B1595807 : Blo 706319 1595807 := bstep (se 1 (by rfl) ⟨1196855, by rfl⟩ : syracuseStep 1595807 = 2393711) B2393711
theorem B1595879 : Blo 706319 1595879 := bstep (se 1 (by rfl) ⟨1196909, by rfl⟩ : syracuseStep 1595879 = 2393819) B2393819
theorem B1792489 : Blo 706319 1792489 := bstep (se 2 (by rfl) ⟨672183, by rfl⟩ : syracuseStep 1792489 = 1344367) B1344367
theorem B3594779 : Blo 706319 3594779 := bstep (se 1 (by rfl) ⟨2696084, by rfl⟩ : syracuseStep 3594779 = 5392169) B5392169
theorem B5102203 : Blo 706319 5102203 := bstep (se 1 (by rfl) ⟨3826652, by rfl⟩ : syracuseStep 5102203 = 7653305) B7653305
theorem B3398393 : Blo 706319 3398393 := bstep (se 2 (by rfl) ⟨1274397, by rfl⟩ : syracuseStep 3398393 = 2548795) B2548795
theorem B6478937 : Blo 706319 6478937 := bstep (se 2 (by rfl) ⟨2429601, by rfl⟩ : syracuseStep 6478937 = 4859203) B4859203
theorem B1596743 : Blo 706319 1596743 := bstep (se 1 (by rfl) ⟨1197557, by rfl⟩ : syracuseStep 1596743 = 2395115) B2395115
theorem B3398993 : Blo 706319 3398993 := bstep (se 2 (by rfl) ⟨1274622, by rfl⟩ : syracuseStep 3398993 = 2549245) B2549245
theorem B1596779 : Blo 706319 1596779 := bstep (se 1 (by rfl) ⟨1197584, by rfl⟩ : syracuseStep 1596779 = 2395169) B2395169
theorem B2874791 : Blo 706319 2874791 := bstep (se 1 (by rfl) ⟨2156093, by rfl⟩ : syracuseStep 2874791 = 4312187) B4312187
theorem B1596905 : Blo 706319 1596905 := bstep (se 2 (by rfl) ⟨598839, by rfl⟩ : syracuseStep 1596905 = 1197679) B1197679
theorem B1597049 : Blo 706319 1597049 := bstep (se 2 (by rfl) ⟨598893, by rfl⟩ : syracuseStep 1597049 = 1197787) B1197787
theorem B1531559 : Blo 706319 1531559 := bstep (se 1 (by rfl) ⟨1148669, by rfl⟩ : syracuseStep 1531559 = 2297339) B2297339
theorem B1793947 : Blo 706319 1793947 := bstep (se 1 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 1793947 = 2690921) B2690921
theorem B12115979 : Blo 706319 12115979 := bstep (se 1 (by rfl) ⟨9086984, by rfl⟩ : syracuseStep 12115979 = 18173969) B18173969
theorem B5365925 : Blo 706319 5365925 := bstep (se 4 (by rfl) ⟨503055, by rfl⟩ : syracuseStep 5365925 = 1006111) B1006111
theorem B1597751 : Blo 706319 1597751 := bstep (se 1 (by rfl) ⟨1198313, by rfl⟩ : syracuseStep 1597751 = 2396627) B2396627
theorem B32792957 : Blo 706319 32792957 := bstep (se 3 (by rfl) ⟨6148679, by rfl⟩ : syracuseStep 32792957 = 12297359) B12297359
theorem B13623713 : Blo 706319 13623713 := bstep (se 2 (by rfl) ⟨5108892, by rfl⟩ : syracuseStep 13623713 = 10217785) B10217785
theorem B1795385 : Blo 706319 1795385 := bstep (se 2 (by rfl) ⟨673269, by rfl⟩ : syracuseStep 1795385 = 1346539) B1346539
theorem B31974931 : Blo 706319 31974931 := bstep (se 1 (by rfl) ⟨23981198, by rfl⟩ : syracuseStep 31974931 = 47962397) B47962397
theorem B15492653 : Blo 706319 15492653 := bstep (se 3 (by rfl) ⟨2904872, by rfl⟩ : syracuseStep 15492653 = 5809745) B5809745
theorem B55830215 : Blo 706319 55830215 := bstep (se 1 (by rfl) ⟨41872661, by rfl⟩ : syracuseStep 55830215 = 83745323) B83745323
theorem B1009631 : Blo 706319 1009631 := bstep (se 1 (by rfl) ⟨757223, by rfl⟩ : syracuseStep 1009631 = 1514447) B1514447
theorem B6056045 : Blo 706319 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B2386043 : Blo 706319 2386043 := bstep (se 1 (by rfl) ⟨1789532, by rfl⟩ : syracuseStep 2386043 = 3579065) B3579065
theorem B1075511 : Blo 706319 1075511 := bstep (se 1 (by rfl) ⟨806633, by rfl⟩ : syracuseStep 1075511 = 1613267) B1613267
theorem B2386313 : Blo 706319 2386313 := bstep (se 2 (by rfl) ⟨894867, by rfl⟩ : syracuseStep 2386313 = 1789735) B1789735
theorem B1796489 : Blo 706319 1796489 := bstep (se 2 (by rfl) ⟨673683, by rfl⟩ : syracuseStep 1796489 = 1347367) B1347367
theorem B5107049 : Blo 706319 5107049 := bstep (se 2 (by rfl) ⟨1915143, by rfl⟩ : syracuseStep 5107049 = 3830287) B3830287
theorem B17034877 : Blo 706319 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B2158331 : Blo 706319 2158331 := bstep (se 1 (by rfl) ⟨1618748, by rfl⟩ : syracuseStep 2158331 = 3237497) B3237497
theorem B1437689 : Blo 706319 1437689 := bstep (se 2 (by rfl) ⟨539133, by rfl⟩ : syracuseStep 1437689 = 1078267) B1078267
theorem B2388041 : Blo 706319 2388041 := bstep (se 2 (by rfl) ⟨895515, by rfl⟩ : syracuseStep 2388041 = 1791031) B1791031
theorem B4026631 : Blo 706319 4026631 := bstep (se 1 (by rfl) ⟨3019973, by rfl⟩ : syracuseStep 4026631 = 6039947) B6039947
theorem B2420999 : Blo 706319 2420999 := bstep (se 1 (by rfl) ⟨1815749, by rfl⟩ : syracuseStep 2420999 = 3631499) B3631499
theorem B4092287 : Blo 706319 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B1274687 : Blo 706319 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B2684087 : Blo 706319 2684087 := bstep (se 1 (by rfl) ⟨2013065, by rfl⟩ : syracuseStep 2684087 = 4026131) B4026131
theorem B2389175 : Blo 706319 2389175 := bstep (se 1 (by rfl) ⟨1791881, by rfl⟩ : syracuseStep 2389175 = 3583763) B3583763
theorem B1439147 : Blo 706319 1439147 := bstep (se 1 (by rfl) ⟨1079360, by rfl⟩ : syracuseStep 1439147 = 2158721) B2158721
theorem B849647 : Blo 706319 849647 := bstep (se 1 (by rfl) ⟨637235, by rfl⟩ : syracuseStep 849647 = 1274471) B1274471
theorem B1636175 : Blo 706319 1636175 := bstep (se 1 (by rfl) ⟨1227131, by rfl⟩ : syracuseStep 1636175 = 2454263) B2454263
theorem B2685089 : Blo 706319 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B3832019 : Blo 706319 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B2390363 : Blo 706319 2390363 := bstep (se 1 (by rfl) ⟨1792772, by rfl⟩ : syracuseStep 2390363 = 3585545) B3585545
theorem B13826419 : Blo 706319 13826419 := bstep (se 1 (by rfl) ⟨10369814, by rfl⟩ : syracuseStep 13826419 = 20739629) B20739629
theorem B1341983 : Blo 706319 1341983 := bstep (se 1 (by rfl) ⟨1006487, by rfl⟩ : syracuseStep 1341983 = 2012975) B2012975
theorem B2685545 : Blo 706319 2685545 := bstep (se 2 (by rfl) ⟨1007079, by rfl⟩ : syracuseStep 2685545 = 2014159) B2014159
theorem B2390633 : Blo 706319 2390633 := bstep (se 2 (by rfl) ⟨896487, by rfl⟩ : syracuseStep 2390633 = 1792975) B1792975
theorem B10222631 : Blo 706319 10222631 := bstep (se 1 (by rfl) ⟨7666973, by rfl⟩ : syracuseStep 10222631 = 15333947) B15333947
theorem B1211483 : Blo 706319 1211483 := bstep (se 1 (by rfl) ⟨908612, by rfl⟩ : syracuseStep 1211483 = 1817225) B1817225
theorem B5438621 : Blo 706319 5438621 := bstep (se 3 (by rfl) ⟨1019741, by rfl⟩ : syracuseStep 5438621 = 2039483) B2039483
theorem B4095431 : Blo 706319 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B2686729 : Blo 706319 2686729 := bstep (se 2 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 2686729 = 2015047) B2015047
theorem B1703879 : Blo 706319 1703879 := bstep (se 1 (by rfl) ⟨1277909, by rfl⟩ : syracuseStep 1703879 = 2555819) B2555819
theorem B55214045 : Blo 706319 55214045 := bstep (se 3 (by rfl) ⟨10352633, by rfl⟩ : syracuseStep 55214045 = 20705267) B20705267
theorem B15303329 : Blo 706319 15303329 := bstep (se 2 (by rfl) ⟨5738748, by rfl⟩ : syracuseStep 15303329 = 11477497) B11477497
theorem B6554621 : Blo 706319 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B10912765 : Blo 706319 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B2589887 : Blo 706319 2589887 := bstep (se 1 (by rfl) ⟨1942415, by rfl⟩ : syracuseStep 2589887 = 3884831) B3884831
theorem B6063731 : Blo 706319 6063731 := bstep (se 1 (by rfl) ⟨4547798, by rfl⟩ : syracuseStep 6063731 = 9095597) B9095597
theorem B2263135 : Blo 706319 2263135 := bstep (se 1 (by rfl) ⟨1697351, by rfl⟩ : syracuseStep 2263135 = 3394703) B3394703
theorem B5736743 : Blo 706319 5736743 := bstep (se 1 (by rfl) ⟨4302557, by rfl⟩ : syracuseStep 5736743 = 8605115) B8605115
theorem B756463 : Blo 706319 756463 := bstep (se 1 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 756463 = 1134695) B1134695
theorem B5737385 : Blo 706319 5737385 := bstep (se 2 (by rfl) ⟨2151519, by rfl⟩ : syracuseStep 5737385 = 4303039) B4303039
theorem B3411197 : Blo 706319 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B3837725 : Blo 706319 3837725 := bstep (se 3 (by rfl) ⟨719573, by rfl⟩ : syracuseStep 3837725 = 1439147) B1439147
theorem B4296671 : Blo 706319 4296671 := bstep (se 1 (by rfl) ⟨3222503, by rfl⟩ : syracuseStep 4296671 = 6445007) B6445007
theorem B2396519 : Blo 706319 2396519 := bstep (se 1 (by rfl) ⟨1797389, by rfl⟩ : syracuseStep 2396519 = 3594779) B3594779
theorem B5738941 : Blo 706319 5738941 := bstep (se 3 (by rfl) ⟨1076051, by rfl⟩ : syracuseStep 5738941 = 2152103) B2152103
theorem B2265725 : Blo 706319 2265725 := bstep (se 3 (by rfl) ⟨424823, by rfl⟩ : syracuseStep 2265725 = 849647) B849647
theorem B22713169 : Blo 706319 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B20386667 : Blo 706319 20386667 := bstep (se 1 (by rfl) ⟨15290000, by rfl⟩ : syracuseStep 20386667 = 30580001) B30580001
theorem B2265995 : Blo 706319 2265995 := bstep (se 1 (by rfl) ⟨1699496, by rfl⟩ : syracuseStep 2265995 = 3398993) B3398993
theorem B2692349 : Blo 706319 2692349 := bstep (se 3 (by rfl) ⟨504815, by rfl⟩ : syracuseStep 2692349 = 1009631) B1009631
theorem B3577283 : Blo 706319 3577283 := bstep (se 1 (by rfl) ⟨2682962, by rfl⟩ : syracuseStep 3577283 = 5365925) B5365925
theorem B21861971 : Blo 706319 21861971 := bstep (se 1 (by rfl) ⟨16396478, by rfl⟩ : syracuseStep 21861971 = 32792957) B32792957
theorem B9082475 : Blo 706319 9082475 := bstep (se 1 (by rfl) ⟨6811856, by rfl⟩ : syracuseStep 9082475 = 13623713) B13623713
theorem B3021137 : Blo 706319 3021137 := bstep (se 2 (by rfl) ⟨1132926, by rfl⟩ : syracuseStep 3021137 = 2265853) B2265853
theorem B10328435 : Blo 706319 10328435 := bstep (se 1 (by rfl) ⟨7746326, by rfl⟩ : syracuseStep 10328435 = 15492653) B15492653
theorem B4037363 : Blo 706319 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B8068571 : Blo 706319 8068571 := bstep (se 1 (by rfl) ⟨6051428, by rfl⟩ : syracuseStep 8068571 = 12102857) B12102857
theorem B4530167 : Blo 706319 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B958459 : Blo 706319 958459 := bstep (se 1 (by rfl) ⟨718844, by rfl⟩ : syracuseStep 958459 = 1437689) B1437689
theorem B170532965 : Blo 706319 170532965 := bstep (se 4 (by rfl) ⟨15987465, by rfl⟩ : syracuseStep 170532965 = 31974931) B31974931
theorem B4858001 : Blo 706319 4858001 := bstep (se 2 (by rfl) ⟨1821750, by rfl⟩ : syracuseStep 4858001 = 3643501) B3643501
theorem B1613999 : Blo 706319 1613999 := bstep (se 1 (by rfl) ⟨1210499, by rfl⟩ : syracuseStep 1613999 = 2420999) B2420999
theorem B1090783 : Blo 706319 1090783 := bstep (se 1 (by rfl) ⟨818087, by rfl⟩ : syracuseStep 1090783 = 1636175) B1636175
theorem B2696723 : Blo 706319 2696723 := bstep (se 1 (by rfl) ⟨2022542, by rfl⟩ : syracuseStep 2696723 = 4045085) B4045085
theorem B894655 : Blo 706319 894655 := bstep (se 1 (by rfl) ⟨670991, by rfl⟩ : syracuseStep 894655 = 1341983) B1341983
theorem B2730287 : Blo 706319 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B3582305 : Blo 706319 3582305 := bstep (se 2 (by rfl) ⟨1343364, by rfl⟩ : syracuseStep 3582305 = 2686729) B2686729
theorem B36809363 : Blo 706319 36809363 := bstep (se 1 (by rfl) ⟨27607022, by rfl⟩ : syracuseStep 36809363 = 55214045) B55214045
theorem B1059623 : Blo 706319 1059623 := bstep (se 1 (by rfl) ⟨794717, by rfl⟩ : syracuseStep 1059623 = 1589435) B1589435
theorem B1059695 : Blo 706319 1059695 := bstep (se 1 (by rfl) ⟨794771, by rfl⟩ : syracuseStep 1059695 = 1589543) B1589543
theorem B895855 : Blo 706319 895855 := bstep (se 1 (by rfl) ⟨671891, by rfl⟩ : syracuseStep 895855 = 1343783) B1343783
theorem B1059947 : Blo 706319 1059947 := bstep (se 1 (by rfl) ⟨794960, by rfl⟩ : syracuseStep 1059947 = 1589921) B1589921
theorem B1060187 : Blo 706319 1060187 := bstep (se 1 (by rfl) ⟨795140, by rfl⟩ : syracuseStep 1060187 = 1590281) B1590281
theorem B1060217 : Blo 706319 1060217 := bstep (se 2 (by rfl) ⟨397581, by rfl⟩ : syracuseStep 1060217 = 795163) B795163
theorem B1060223 : Blo 706319 1060223 := bstep (se 1 (by rfl) ⟨795167, by rfl⟩ : syracuseStep 1060223 = 1590335) B1590335
theorem B2272799 : Blo 706319 2272799 := bstep (se 1 (by rfl) ⟨1704599, by rfl⟩ : syracuseStep 2272799 = 3409199) B3409199
theorem B1060457 : Blo 706319 1060457 := bstep (se 2 (by rfl) ⟨397671, by rfl⟩ : syracuseStep 1060457 = 795343) B795343
theorem B1060847 : Blo 706319 1060847 := bstep (se 1 (by rfl) ⟨795635, by rfl⟩ : syracuseStep 1060847 = 1591271) B1591271
theorem B1060967 : Blo 706319 1060967 := bstep (se 1 (by rfl) ⟨795725, by rfl⟩ : syracuseStep 1060967 = 1591451) B1591451
theorem B1061087 : Blo 706319 1061087 := bstep (se 1 (by rfl) ⟨795815, by rfl⟩ : syracuseStep 1061087 = 1591631) B1591631
theorem B897247 : Blo 706319 897247 := bstep (se 1 (by rfl) ⟨672935, by rfl⟩ : syracuseStep 897247 = 1345871) B1345871
theorem B798943 : Blo 706319 798943 := bstep (se 1 (by rfl) ⟨599207, by rfl⟩ : syracuseStep 798943 = 1198415) B1198415
theorem B1061147 : Blo 706319 1061147 := bstep (se 1 (by rfl) ⟨795860, by rfl⟩ : syracuseStep 1061147 = 1591721) B1591721
theorem B1192475 : Blo 706319 1192475 := bstep (se 1 (by rfl) ⟨894356, by rfl⟩ : syracuseStep 1192475 = 1788713) B1788713
theorem B73740901 : Blo 706319 73740901 := bstep (se 4 (by rfl) ⟨6913209, by rfl⟩ : syracuseStep 73740901 = 13826419) B13826419
theorem B1061543 : Blo 706319 1061543 := bstep (se 1 (by rfl) ⟨796157, by rfl⟩ : syracuseStep 1061543 = 1592315) B1592315
theorem B897743 : Blo 706319 897743 := bstep (se 1 (by rfl) ⟨673307, by rfl⟩ : syracuseStep 897743 = 1346615) B1346615
theorem B1061663 : Blo 706319 1061663 := bstep (se 1 (by rfl) ⟨796247, by rfl⟩ : syracuseStep 1061663 = 1592495) B1592495
theorem B1061687 : Blo 706319 1061687 := bstep (se 1 (by rfl) ⟨796265, by rfl⟩ : syracuseStep 1061687 = 1592531) B1592531
theorem B1061801 : Blo 706319 1061801 := bstep (se 2 (by rfl) ⟨398175, by rfl⟩ : syracuseStep 1061801 = 796351) B796351
theorem B1061867 : Blo 706319 1061867 := bstep (se 1 (by rfl) ⟨796400, by rfl⟩ : syracuseStep 1061867 = 1592801) B1592801
theorem B1062143 : Blo 706319 1062143 := bstep (se 1 (by rfl) ⟨796607, by rfl⟩ : syracuseStep 1062143 = 1593215) B1593215
theorem B1062185 : Blo 706319 1062185 := bstep (se 2 (by rfl) ⟨398319, by rfl⟩ : syracuseStep 1062185 = 796639) B796639
theorem B1193447 : Blo 706319 1193447 := bstep (se 1 (by rfl) ⟨895085, by rfl⟩ : syracuseStep 1193447 = 1790171) B1790171
theorem B898715 : Blo 706319 898715 := bstep (se 1 (by rfl) ⟨674036, by rfl⟩ : syracuseStep 898715 = 1348073) B1348073
theorem B1062779 : Blo 706319 1062779 := bstep (se 1 (by rfl) ⟨797084, by rfl⟩ : syracuseStep 1062779 = 1594169) B1594169
theorem B1062815 : Blo 706319 1062815 := bstep (se 1 (by rfl) ⟨797111, by rfl⟩ : syracuseStep 1062815 = 1594223) B1594223
theorem B997439 : Blo 706319 997439 := bstep (se 1 (by rfl) ⟨748079, by rfl⟩ : syracuseStep 997439 = 1496159) B1496159
theorem B1063019 : Blo 706319 1063019 := bstep (se 1 (by rfl) ⟨797264, by rfl⟩ : syracuseStep 1063019 = 1594529) B1594529
theorem B1063049 : Blo 706319 1063049 := bstep (se 2 (by rfl) ⟨398643, by rfl⟩ : syracuseStep 1063049 = 797287) B797287
theorem B1063199 : Blo 706319 1063199 := bstep (se 1 (by rfl) ⟨797399, by rfl⟩ : syracuseStep 1063199 = 1594799) B1594799
theorem B4045403 : Blo 706319 4045403 := bstep (se 1 (by rfl) ⟨3034052, by rfl⟩ : syracuseStep 4045403 = 6068105) B6068105
theorem B5094191 : Blo 706319 5094191 := bstep (se 1 (by rfl) ⟨3820643, by rfl⟩ : syracuseStep 5094191 = 7641287) B7641287
theorem B1063871 : Blo 706319 1063871 := bstep (se 1 (by rfl) ⟨797903, by rfl⟩ : syracuseStep 1063871 = 1595807) B1595807
theorem B1063919 : Blo 706319 1063919 := bstep (se 1 (by rfl) ⟨797939, by rfl⟩ : syracuseStep 1063919 = 1595879) B1595879
theorem B1064105 : Blo 706319 1064105 := bstep (se 2 (by rfl) ⟨399039, by rfl⟩ : syracuseStep 1064105 = 798079) B798079
theorem B3587489 : Blo 706319 3587489 := bstep (se 2 (by rfl) ⟨1345308, by rfl⟩ : syracuseStep 3587489 = 2690617) B2690617
theorem B1064495 : Blo 706319 1064495 := bstep (se 1 (by rfl) ⟨798371, by rfl⟩ : syracuseStep 1064495 = 1596743) B1596743
theorem B1064519 : Blo 706319 1064519 := bstep (se 1 (by rfl) ⟨798389, by rfl⟩ : syracuseStep 1064519 = 1596779) B1596779
theorem B1064603 : Blo 706319 1064603 := bstep (se 1 (by rfl) ⟨798452, by rfl⟩ : syracuseStep 1064603 = 1596905) B1596905
theorem B1064699 : Blo 706319 1064699 := bstep (se 1 (by rfl) ⟨798524, by rfl⟩ : syracuseStep 1064699 = 1597049) B1597049
theorem B8077319 : Blo 706319 8077319 := bstep (se 1 (by rfl) ⟨6057989, by rfl⟩ : syracuseStep 8077319 = 12115979) B12115979
theorem B1589345 : Blo 706319 1589345 := bstep (se 2 (by rfl) ⟨596004, by rfl⟩ : syracuseStep 1589345 = 1192009) B1192009
theorem B1589417 : Blo 706319 1589417 := bstep (se 2 (by rfl) ⟨596031, by rfl⟩ : syracuseStep 1589417 = 1192063) B1192063
theorem B1196201 : Blo 706319 1196201 := bstep (se 2 (by rfl) ⟨448575, by rfl⟩ : syracuseStep 1196201 = 897151) B897151
theorem B1065167 : Blo 706319 1065167 := bstep (se 1 (by rfl) ⟨798875, by rfl⟩ : syracuseStep 1065167 = 1597751) B1597751
theorem B3064351 : Blo 706319 3064351 := bstep (se 1 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 3064351 = 4596527) B4596527
theorem B2868029 : Blo 706319 2868029 := bstep (se 3 (by rfl) ⟨537755, by rfl⟩ : syracuseStep 2868029 = 1075511) B1075511
theorem B1196923 : Blo 706319 1196923 := bstep (se 1 (by rfl) ⟨897692, by rfl⟩ : syracuseStep 1196923 = 1795385) B1795385
theorem B4605281 : Blo 706319 4605281 := bstep (se 2 (by rfl) ⟨1726980, by rfl⟩ : syracuseStep 4605281 = 3453961) B3453961
theorem B1590695 : Blo 706319 1590695 := bstep (se 1 (by rfl) ⟨1193021, by rfl⟩ : syracuseStep 1590695 = 2386043) B2386043
theorem B1590857 : Blo 706319 1590857 := bstep (se 2 (by rfl) ⟨596571, by rfl⟩ : syracuseStep 1590857 = 1193143) B1193143
theorem B1590875 : Blo 706319 1590875 := bstep (se 1 (by rfl) ⟨1193156, by rfl⟩ : syracuseStep 1590875 = 2386313) B2386313
theorem B1197659 : Blo 706319 1197659 := bstep (se 1 (by rfl) ⟨898244, by rfl⟩ : syracuseStep 1197659 = 1796489) B1796489
theorem B30557857 : Blo 706319 30557857 := bstep (se 2 (by rfl) ⟨11459196, by rfl⟩ : syracuseStep 30557857 = 22918393) B22918393
theorem B9062381 : Blo 706319 9062381 := bstep (se 3 (by rfl) ⟨1699196, by rfl⟩ : syracuseStep 9062381 = 3398393) B3398393
theorem B706767 : Blo 706319 706767 := bstep (se 1 (by rfl) ⟨530075, by rfl⟩ : syracuseStep 706767 = 1060151) B1060151
theorem B706879 : Blo 706319 706879 := bstep (se 1 (by rfl) ⟨530159, by rfl⟩ : syracuseStep 706879 = 1060319) B1060319
theorem B707023 : Blo 706319 707023 := bstep (se 1 (by rfl) ⟨530267, by rfl⟩ : syracuseStep 707023 = 1060535) B1060535
theorem B1591865 : Blo 706319 1591865 := bstep (se 2 (by rfl) ⟨596949, by rfl⟩ : syracuseStep 1591865 = 1193899) B1193899
theorem B707163 : Blo 706319 707163 := bstep (se 1 (by rfl) ⟨530372, by rfl⟩ : syracuseStep 707163 = 1060745) B1060745
theorem B1592027 : Blo 706319 1592027 := bstep (se 1 (by rfl) ⟨1194020, by rfl⟩ : syracuseStep 1592027 = 2388041) B2388041
theorem B707327 : Blo 706319 707327 := bstep (se 1 (by rfl) ⟨530495, by rfl⟩ : syracuseStep 707327 = 1060991) B1060991
theorem B3066623 : Blo 706319 3066623 := bstep (se 1 (by rfl) ⟨2299967, by rfl⟩ : syracuseStep 3066623 = 4599935) B4599935
theorem B3820297 : Blo 706319 3820297 := bstep (se 2 (by rfl) ⟨1432611, by rfl⟩ : syracuseStep 3820297 = 2865223) B2865223
theorem B3230621 : Blo 706319 3230621 := bstep (se 3 (by rfl) ⟨605741, by rfl⟩ : syracuseStep 3230621 = 1211483) B1211483
theorem B3591215 : Blo 706319 3591215 := bstep (se 1 (by rfl) ⟨2693411, by rfl⟩ : syracuseStep 3591215 = 5386823) B5386823
theorem B14502989 : Blo 706319 14502989 := bstep (se 3 (by rfl) ⟨2719310, by rfl⟩ : syracuseStep 14502989 = 5438621) B5438621
theorem B707751 : Blo 706319 707751 := bstep (se 1 (by rfl) ⟨530813, by rfl⟩ : syracuseStep 707751 = 1061627) B1061627
theorem B1592585 : Blo 706319 1592585 := bstep (se 2 (by rfl) ⟨597219, by rfl⟩ : syracuseStep 1592585 = 1194439) B1194439
theorem B1789391 : Blo 706319 1789391 := bstep (se 1 (by rfl) ⟨1342043, by rfl⟩ : syracuseStep 1789391 = 2684087) B2684087
theorem B1592783 : Blo 706319 1592783 := bstep (se 1 (by rfl) ⟨1194587, by rfl⟩ : syracuseStep 1592783 = 2389175) B2389175
theorem B708047 : Blo 706319 708047 := bstep (se 1 (by rfl) ⟨531035, by rfl⟩ : syracuseStep 708047 = 1062071) B1062071
theorem B6802937 : Blo 706319 6802937 := bstep (se 2 (by rfl) ⟨2551101, by rfl⟩ : syracuseStep 6802937 = 5102203) B5102203
theorem B1592873 : Blo 706319 1592873 := bstep (se 2 (by rfl) ⟨597327, by rfl⟩ : syracuseStep 1592873 = 1194655) B1194655
theorem B708207 : Blo 706319 708207 := bstep (se 1 (by rfl) ⟨531155, by rfl⟩ : syracuseStep 708207 = 1062311) B1062311
theorem B708327 : Blo 706319 708327 := bstep (se 1 (by rfl) ⟨531245, by rfl⟩ : syracuseStep 708327 = 1062491) B1062491
theorem B3592187 : Blo 706319 3592187 := bstep (se 1 (by rfl) ⟨2694140, by rfl⟩ : syracuseStep 3592187 = 5388281) B5388281
theorem B708635 : Blo 706319 708635 := bstep (se 1 (by rfl) ⟨531476, by rfl⟩ : syracuseStep 708635 = 1062953) B1062953
theorem B708655 : Blo 706319 708655 := bstep (se 1 (by rfl) ⟨531491, by rfl⟩ : syracuseStep 708655 = 1062983) B1062983
theorem B1790059 : Blo 706319 1790059 := bstep (se 1 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 1790059 = 2685089) B2685089
theorem B1593575 : Blo 706319 1593575 := bstep (se 1 (by rfl) ⟨1195181, by rfl⟩ : syracuseStep 1593575 = 2390363) B2390363
theorem B8081693 : Blo 706319 8081693 := bstep (se 3 (by rfl) ⟨1515317, by rfl⟩ : syracuseStep 8081693 = 3030635) B3030635
theorem B708911 : Blo 706319 708911 := bstep (se 1 (by rfl) ⟨531683, by rfl⟩ : syracuseStep 708911 = 1063367) B1063367
theorem B1790363 : Blo 706319 1790363 := bstep (se 1 (by rfl) ⟨1342772, by rfl⟩ : syracuseStep 1790363 = 2685545) B2685545
theorem B1593755 : Blo 706319 1593755 := bstep (se 1 (by rfl) ⟨1195316, by rfl⟩ : syracuseStep 1593755 = 2390633) B2390633
theorem B4084157 : Blo 706319 4084157 := bstep (se 3 (by rfl) ⟨765779, by rfl⟩ : syracuseStep 4084157 = 1531559) B1531559
theorem B2019775 : Blo 706319 2019775 := bstep (se 1 (by rfl) ⟨1514831, by rfl⟩ : syracuseStep 2019775 = 3029663) B3029663
theorem B709055 : Blo 706319 709055 := bstep (se 1 (by rfl) ⟨531791, by rfl⟩ : syracuseStep 709055 = 1063583) B1063583
theorem B709151 : Blo 706319 709151 := bstep (se 1 (by rfl) ⟨531863, by rfl⟩ : syracuseStep 709151 = 1063727) B1063727
theorem B709231 : Blo 706319 709231 := bstep (se 1 (by rfl) ⟨531923, by rfl⟩ : syracuseStep 709231 = 1063847) B1063847
theorem B5755549 : Blo 706319 5755549 := bstep (se 3 (by rfl) ⟨1079165, by rfl⟩ : syracuseStep 5755549 = 2158331) B2158331
theorem B709351 : Blo 706319 709351 := bstep (se 1 (by rfl) ⟨532013, by rfl⟩ : syracuseStep 709351 = 1064027) B1064027
theorem B709599 : Blo 706319 709599 := bstep (se 1 (by rfl) ⟨532199, by rfl⟩ : syracuseStep 709599 = 1064399) B1064399
theorem B709855 : Blo 706319 709855 := bstep (se 1 (by rfl) ⟨532391, by rfl⟩ : syracuseStep 709855 = 1064783) B1064783
theorem B3593483 : Blo 706319 3593483 := bstep (se 1 (by rfl) ⟨2695112, by rfl⟩ : syracuseStep 3593483 = 5390225) B5390225
theorem B1135919 : Blo 706319 1135919 := bstep (se 1 (by rfl) ⟨851939, by rfl⟩ : syracuseStep 1135919 = 1703879) B1703879
theorem B709935 : Blo 706319 709935 := bstep (se 1 (by rfl) ⟨532451, by rfl⟩ : syracuseStep 709935 = 1064903) B1064903
theorem B710175 : Blo 706319 710175 := bstep (se 1 (by rfl) ⟨532631, by rfl⟩ : syracuseStep 710175 = 1065263) B1065263
theorem B1791679 : Blo 706319 1791679 := bstep (se 1 (by rfl) ⟨1343759, by rfl⟩ : syracuseStep 1791679 = 2687519) B2687519
theorem B2021107 : Blo 706319 2021107 := bstep (se 1 (by rfl) ⟨1515830, by rfl⟩ : syracuseStep 2021107 = 3031661) B3031661
theorem B4545031 : Blo 706319 4545031 := bstep (se 1 (by rfl) ⟨3408773, by rfl⟩ : syracuseStep 4545031 = 6817547) B6817547
theorem B3595103 : Blo 706319 3595103 := bstep (se 1 (by rfl) ⟨2696327, by rfl⟩ : syracuseStep 3595103 = 5392655) B5392655
theorem B1596329 : Blo 706319 1596329 := bstep (se 2 (by rfl) ⟨598623, by rfl⟩ : syracuseStep 1596329 = 1197247) B1197247
theorem B1793087 : Blo 706319 1793087 := bstep (se 1 (by rfl) ⟨1344815, by rfl⟩ : syracuseStep 1793087 = 2689631) B2689631
theorem B1793249 : Blo 706319 1793249 := bstep (se 2 (by rfl) ⟨672468, by rfl⟩ : syracuseStep 1793249 = 1344937) B1344937
theorem B36789835 : Blo 706319 36789835 := bstep (se 1 (by rfl) ⟨27592376, by rfl⟩ : syracuseStep 36789835 = 55184753) B55184753
theorem B1794089 : Blo 706319 1794089 := bstep (se 2 (by rfl) ⟨672783, by rfl⟩ : syracuseStep 1794089 = 1345567) B1345567
theorem B1597481 : Blo 706319 1597481 := bstep (se 2 (by rfl) ⟨599055, by rfl⟩ : syracuseStep 1597481 = 1198111) B1198111
theorem B1007911 : Blo 706319 1007911 := bstep (se 1 (by rfl) ⟨755933, by rfl⟩ : syracuseStep 1007911 = 1511867) B1511867
theorem B4546955 : Blo 706319 4546955 := bstep (se 1 (by rfl) ⟨3410216, by rfl⟩ : syracuseStep 4546955 = 6820433) B6820433
theorem B1598111 : Blo 706319 1598111 := bstep (se 1 (by rfl) ⟨1198583, by rfl⟩ : syracuseStep 1598111 = 2397167) B2397167
theorem B1008731 : Blo 706319 1008731 := bstep (se 1 (by rfl) ⟨756548, by rfl⟩ : syracuseStep 1008731 = 1513097) B1513097
theorem B2385017 : Blo 706319 2385017 := bstep (se 2 (by rfl) ⟨894381, by rfl⟩ : syracuseStep 2385017 = 1788763) B1788763
theorem B1795193 : Blo 706319 1795193 := bstep (se 2 (by rfl) ⟨673197, by rfl⟩ : syracuseStep 1795193 = 1346395) B1346395
theorem B2385071 : Blo 706319 2385071 := bstep (se 1 (by rfl) ⟨1788803, by rfl⟩ : syracuseStep 2385071 = 3577607) B3577607
theorem B17229277 : Blo 706319 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B4319291 : Blo 706319 4319291 := bstep (se 1 (by rfl) ⟨3239468, by rfl⟩ : syracuseStep 4319291 = 6478937) B6478937
theorem B8611919 : Blo 706319 8611919 := bstep (se 1 (by rfl) ⟨6458939, by rfl⟩ : syracuseStep 8611919 = 12917879) B12917879
theorem B3238211 : Blo 706319 3238211 := bstep (se 1 (by rfl) ⟨2428658, by rfl⟩ : syracuseStep 3238211 = 4857317) B4857317
theorem B2156969 : Blo 706319 2156969 := bstep (se 2 (by rfl) ⟨808863, by rfl⟩ : syracuseStep 2156969 = 1617727) B1617727
theorem B5368841 : Blo 706319 5368841 := bstep (se 2 (by rfl) ⟨2013315, by rfl⟩ : syracuseStep 5368841 = 4026631) B4026631
theorem B2387015 : Blo 706319 2387015 := bstep (se 1 (by rfl) ⟨1790261, by rfl⟩ : syracuseStep 2387015 = 3580523) B3580523
theorem B55799563 : Blo 706319 55799563 := bstep (se 1 (by rfl) ⟨41849672, by rfl⟩ : syracuseStep 55799563 = 83699345) B83699345
theorem B37220143 : Blo 706319 37220143 := bstep (se 1 (by rfl) ⟨27915107, by rfl⟩ : syracuseStep 37220143 = 55830215) B55830215
theorem B2388095 : Blo 706319 2388095 := bstep (se 1 (by rfl) ⟨1791071, by rfl⟩ : syracuseStep 2388095 = 3582143) B3582143
theorem B3404699 : Blo 706319 3404699 := bstep (se 1 (by rfl) ⟨2553524, by rfl⟩ : syracuseStep 3404699 = 5107049) B5107049
theorem B2389607 : Blo 706319 2389607 := bstep (se 1 (by rfl) ⟨1792205, by rfl⟩ : syracuseStep 2389607 = 3584411) B3584411
theorem B1341049 : Blo 706319 1341049 := bstep (se 2 (by rfl) ⟨502893, by rfl⟩ : syracuseStep 1341049 = 1005787) B1005787
theorem B849791 : Blo 706319 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B2389931 : Blo 706319 2389931 := bstep (se 1 (by rfl) ⟨1792448, by rfl⟩ : syracuseStep 2389931 = 3584897) B3584897
theorem B2389985 : Blo 706319 2389985 := bstep (se 2 (by rfl) ⟨896244, by rfl⟩ : syracuseStep 2389985 = 1792489) B1792489
theorem B1079471 : Blo 706319 1079471 := bstep (se 1 (by rfl) ⟨809603, by rfl⟩ : syracuseStep 1079471 = 1619207) B1619207
theorem B3832103 : Blo 706319 3832103 := bstep (se 1 (by rfl) ⟨2874077, by rfl⟩ : syracuseStep 3832103 = 5748155) B5748155
theorem B7666109 : Blo 706319 7666109 := bstep (se 3 (by rfl) ⟨1437395, by rfl⟩ : syracuseStep 7666109 = 2874791) B2874791
theorem B2390471 : Blo 706319 2390471 := bstep (se 1 (by rfl) ⟨1792853, by rfl⟩ : syracuseStep 2390471 = 3585707) B3585707
theorem B2554679 : Blo 706319 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B6815087 : Blo 706319 6815087 := bstep (se 1 (by rfl) ⟨5111315, by rfl⟩ : syracuseStep 6815087 = 10222631) B10222631
theorem B1342955 : Blo 706319 1342955 := bstep (se 1 (by rfl) ⟨1007216, by rfl⟩ : syracuseStep 1342955 = 2014433) B2014433
theorem B4030073 : Blo 706319 4030073 := bstep (se 2 (by rfl) ⟨1511277, by rfl⟩ : syracuseStep 4030073 = 3022555) B3022555
theorem B2391929 : Blo 706319 2391929 := bstep (se 2 (by rfl) ⟨896973, by rfl⟩ : syracuseStep 2391929 = 1793947) B1793947
theorem B1343881 : Blo 706319 1343881 := bstep (se 2 (by rfl) ⟨503955, by rfl⟩ : syracuseStep 1343881 = 1007911) B1007911
theorem B14550353 : Blo 706319 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B2393981 : Blo 706319 2393981 := bstep (se 3 (by rfl) ⟨448871, by rfl⟩ : syracuseStep 2393981 = 897743) B897743
theorem B22972369 : Blo 706319 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B2394143 : Blo 706319 2394143 := bstep (se 1 (by rfl) ⟨1795607, by rfl⟩ : syracuseStep 2394143 = 3591215) B3591215
theorem B9668659 : Blo 706319 9668659 := bstep (se 1 (by rfl) ⟨7251494, by rfl⟩ : syracuseStep 9668659 = 14502989) B14502989
theorem B2558483 : Blo 706319 2558483 := bstep (se 1 (by rfl) ⟨1918862, by rfl⟩ : syracuseStep 2558483 = 3837725) B3837725
theorem B2394791 : Blo 706319 2394791 := bstep (se 1 (by rfl) ⟨1796093, by rfl⟩ : syracuseStep 2394791 = 3592187) B3592187
theorem B3017513 : Blo 706319 3017513 := bstep (se 2 (by rfl) ⟨1131567, by rfl⟩ : syracuseStep 3017513 = 2263135) B2263135
theorem B2689949 : Blo 706319 2689949 := bstep (se 3 (by rfl) ⟨504365, by rfl⟩ : syracuseStep 2689949 = 1008731) B1008731
theorem B2722771 : Blo 706319 2722771 := bstep (se 1 (by rfl) ⟨2042078, by rfl⟩ : syracuseStep 2722771 = 4084157) B4084157
theorem B1510483 : Blo 706319 1510483 := bstep (se 1 (by rfl) ⟨1132862, by rfl⟩ : syracuseStep 1510483 = 2265725) B2265725
theorem B1510663 : Blo 706319 1510663 := bstep (se 1 (by rfl) ⟨1132997, by rfl⟩ : syracuseStep 1510663 = 2265995) B2265995
theorem B2395655 : Blo 706319 2395655 := bstep (se 1 (by rfl) ⟨1796741, by rfl⟩ : syracuseStep 2395655 = 3593483) B3593483
theorem B757279 : Blo 706319 757279 := bstep (se 1 (by rfl) ⟨567959, by rfl⟩ : syracuseStep 757279 = 1135919) B1135919
theorem B6885623 : Blo 706319 6885623 := bstep (se 1 (by rfl) ⟨5164217, by rfl⟩ : syracuseStep 6885623 = 10328435) B10328435
theorem B2396573 : Blo 706319 2396573 := bstep (se 3 (by rfl) ⟨449357, by rfl⟩ : syracuseStep 2396573 = 898715) B898715
theorem B2691575 : Blo 706319 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B2396735 : Blo 706319 2396735 := bstep (se 1 (by rfl) ⟨1797551, by rfl⟩ : syracuseStep 2396735 = 3595103) B3595103
theorem B5379047 : Blo 706319 5379047 := bstep (se 1 (by rfl) ⟨4034285, by rfl⟩ : syracuseStep 5379047 = 8068571) B8068571
theorem B2266109 : Blo 706319 2266109 := bstep (se 3 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 2266109 = 849791) B849791
theorem B3020111 : Blo 706319 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B2659837 : Blo 706319 2659837 := bstep (se 3 (by rfl) ⟨498719, by rfl⟩ : syracuseStep 2659837 = 997439) B997439
theorem B2693033 : Blo 706319 2693033 := bstep (se 2 (by rfl) ⟨1009887, by rfl⟩ : syracuseStep 2693033 = 2019775) B2019775
theorem B7280765 : Blo 706319 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B7674065 : Blo 706319 7674065 := bstep (se 2 (by rfl) ⟨2877774, by rfl⟩ : syracuseStep 7674065 = 5755549) B5755549
theorem B30284225 : Blo 706319 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B5741279 : Blo 706319 5741279 := bstep (se 1 (by rfl) ⟨4305959, by rfl⟩ : syracuseStep 5741279 = 8611919) B8611919
theorem B3579227 : Blo 706319 3579227 := bstep (se 1 (by rfl) ⟨2684420, by rfl⟩ : syracuseStep 3579227 = 5368841) B5368841
theorem B2694809 : Blo 706319 2694809 := bstep (se 2 (by rfl) ⟨1010553, by rfl⟩ : syracuseStep 2694809 = 2021107) B2021107
theorem B1515199 : Blo 706319 1515199 := bstep (se 1 (by rfl) ⟨1136399, by rfl⟩ : syracuseStep 1515199 = 2272799) B2272799
theorem B794983 : Blo 706319 794983 := bstep (se 1 (by rfl) ⟨596237, by rfl⟩ : syracuseStep 794983 = 1192475) B1192475
theorem B2269799 : Blo 706319 2269799 := bstep (se 1 (by rfl) ⟨1702349, by rfl⟩ : syracuseStep 2269799 = 3404699) B3404699
theorem B795631 : Blo 706319 795631 := bstep (se 1 (by rfl) ⟨596723, by rfl⟩ : syracuseStep 795631 = 1193447) B1193447
theorem B2696935 : Blo 706319 2696935 := bstep (se 1 (by rfl) ⟨2022701, by rfl⟩ : syracuseStep 2696935 = 4045403) B4045403
theorem B895303 : Blo 706319 895303 := bstep (se 1 (by rfl) ⟨671477, by rfl⟩ : syracuseStep 895303 = 1342955) B1342955
theorem B5384879 : Blo 706319 5384879 := bstep (se 1 (by rfl) ⟨4038659, by rfl⟩ : syracuseStep 5384879 = 8077319) B8077319
theorem B1059563 : Blo 706319 1059563 := bstep (se 1 (by rfl) ⟨794672, by rfl⟩ : syracuseStep 1059563 = 1589345) B1589345
theorem B1059611 : Blo 706319 1059611 := bstep (se 1 (by rfl) ⟨794708, by rfl⟩ : syracuseStep 1059611 = 1589417) B1589417
theorem B797467 : Blo 706319 797467 := bstep (se 1 (by rfl) ⟨598100, by rfl⟩ : syracuseStep 797467 = 1196201) B1196201
theorem B10202219 : Blo 706319 10202219 := bstep (se 1 (by rfl) ⟨7651664, by rfl⟩ : syracuseStep 10202219 = 15303329) B15303329
theorem B1912019 : Blo 706319 1912019 := bstep (se 1 (by rfl) ⟨1434014, by rfl⟩ : syracuseStep 1912019 = 2868029) B2868029
theorem B4369747 : Blo 706319 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B1060463 : Blo 706319 1060463 := bstep (se 1 (by rfl) ⟨795347, by rfl⟩ : syracuseStep 1060463 = 1590695) B1590695
theorem B1060571 : Blo 706319 1060571 := bstep (se 1 (by rfl) ⟨795428, by rfl⟩ : syracuseStep 1060571 = 1590857) B1590857
theorem B1060583 : Blo 706319 1060583 := bstep (se 1 (by rfl) ⟨795437, by rfl⟩ : syracuseStep 1060583 = 1590875) B1590875
theorem B798439 : Blo 706319 798439 := bstep (se 1 (by rfl) ⟨598829, by rfl⟩ : syracuseStep 798439 = 1197659) B1197659
theorem B4042487 : Blo 706319 4042487 := bstep (se 1 (by rfl) ⟨3031865, by rfl⟩ : syracuseStep 4042487 = 6063731) B6063731
theorem B6041587 : Blo 706319 6041587 := bstep (se 1 (by rfl) ⟨4531190, by rfl⟩ : syracuseStep 6041587 = 9062381) B9062381
theorem B1454377 : Blo 706319 1454377 := bstep (se 2 (by rfl) ⟨545391, by rfl⟩ : syracuseStep 1454377 = 1090783) B1090783
theorem B1061243 : Blo 706319 1061243 := bstep (se 1 (by rfl) ⟨795932, by rfl⟩ : syracuseStep 1061243 = 1591865) B1591865
theorem B1061351 : Blo 706319 1061351 := bstep (se 1 (by rfl) ⟨796013, by rfl⟩ : syracuseStep 1061351 = 1592027) B1592027
theorem B2044415 : Blo 706319 2044415 := bstep (se 1 (by rfl) ⟨1533311, by rfl⟩ : syracuseStep 2044415 = 3066623) B3066623
theorem B2274131 : Blo 706319 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B1061723 : Blo 706319 1061723 := bstep (se 1 (by rfl) ⟨796292, by rfl⟩ : syracuseStep 1061723 = 1592585) B1592585
theorem B40743809 : Blo 706319 40743809 := bstep (se 2 (by rfl) ⟨15278928, by rfl⟩ : syracuseStep 40743809 = 30557857) B30557857
theorem B1192873 : Blo 706319 1192873 := bstep (se 2 (by rfl) ⟨447327, by rfl⟩ : syracuseStep 1192873 = 894655) B894655
theorem B1192927 : Blo 706319 1192927 := bstep (se 1 (by rfl) ⟨894695, by rfl⟩ : syracuseStep 1192927 = 1789391) B1789391
theorem B1061855 : Blo 706319 1061855 := bstep (se 1 (by rfl) ⟨796391, by rfl⟩ : syracuseStep 1061855 = 1592783) B1592783
theorem B4535291 : Blo 706319 4535291 := bstep (se 1 (by rfl) ⟨3401468, by rfl⟩ : syracuseStep 4535291 = 6802937) B6802937
theorem B1061915 : Blo 706319 1061915 := bstep (se 1 (by rfl) ⟨796436, by rfl⟩ : syracuseStep 1061915 = 1592873) B1592873
theorem B2864447 : Blo 706319 2864447 := bstep (se 1 (by rfl) ⟨2148335, by rfl⟩ : syracuseStep 2864447 = 4296671) B4296671
theorem B1062383 : Blo 706319 1062383 := bstep (se 1 (by rfl) ⟨796787, by rfl⟩ : syracuseStep 1062383 = 1593575) B1593575
theorem B5387795 : Blo 706319 5387795 := bstep (se 1 (by rfl) ⟨4040846, by rfl⟩ : syracuseStep 5387795 = 8081693) B8081693
theorem B1193575 : Blo 706319 1193575 := bstep (se 1 (by rfl) ⟨895181, by rfl⟩ : syracuseStep 1193575 = 1790363) B1790363
theorem B1062503 : Blo 706319 1062503 := bstep (se 1 (by rfl) ⟨796877, by rfl⟩ : syracuseStep 1062503 = 1593755) B1593755
theorem B5093729 : Blo 706319 5093729 := bstep (se 2 (by rfl) ⟨1910148, by rfl⟩ : syracuseStep 5093729 = 3820297) B3820297
theorem B1194473 : Blo 706319 1194473 := bstep (se 2 (by rfl) ⟨447927, by rfl⟩ : syracuseStep 1194473 = 895855) B895855
theorem B2014091 : Blo 706319 2014091 := bstep (se 1 (by rfl) ⟨1510568, by rfl⟩ : syracuseStep 2014091 = 3021137) B3021137
theorem B1064219 : Blo 706319 1064219 := bstep (se 1 (by rfl) ⟨798164, by rfl⟩ : syracuseStep 1064219 = 1596329) B1596329
theorem B1195391 : Blo 706319 1195391 := bstep (se 1 (by rfl) ⟨896543, by rfl⟩ : syracuseStep 1195391 = 1793087) B1793087
theorem B1195499 : Blo 706319 1195499 := bstep (se 1 (by rfl) ⟨896624, by rfl⟩ : syracuseStep 1195499 = 1793249) B1793249
theorem B74399417 : Blo 706319 74399417 := bstep (se 2 (by rfl) ⟨27899781, by rfl⟩ : syracuseStep 74399417 = 55799563) B55799563
theorem B49626857 : Blo 706319 49626857 := bstep (se 2 (by rfl) ⟨18610071, by rfl⟩ : syracuseStep 49626857 = 37220143) B37220143
theorem B1196059 : Blo 706319 1196059 := bstep (se 1 (by rfl) ⟨897044, by rfl⟩ : syracuseStep 1196059 = 1794089) B1794089
theorem B1064987 : Blo 706319 1064987 := bstep (se 1 (by rfl) ⟨798740, by rfl⟩ : syracuseStep 1064987 = 1597481) B1597481
theorem B113688643 : Blo 706319 113688643 := bstep (se 1 (by rfl) ⟨85266482, by rfl⟩ : syracuseStep 113688643 = 170532965) B170532965
theorem B11518109 : Blo 706319 11518109 := bstep (se 3 (by rfl) ⟨2159645, by rfl⟩ : syracuseStep 11518109 = 4319291) B4319291
theorem B3031303 : Blo 706319 3031303 := bstep (se 1 (by rfl) ⟨2273477, by rfl⟩ : syracuseStep 3031303 = 4546955) B4546955
theorem B1196329 : Blo 706319 1196329 := bstep (se 2 (by rfl) ⟨448623, by rfl⟩ : syracuseStep 1196329 = 897247) B897247
theorem B1065257 : Blo 706319 1065257 := bstep (se 2 (by rfl) ⟨399471, by rfl⟩ : syracuseStep 1065257 = 798943) B798943
theorem B1065407 : Blo 706319 1065407 := bstep (se 1 (by rfl) ⟨799055, by rfl⟩ : syracuseStep 1065407 = 1598111) B1598111
theorem B7651921 : Blo 706319 7651921 := bstep (se 2 (by rfl) ⟨2869470, by rfl⟩ : syracuseStep 7651921 = 5738941) B5738941
theorem B1590011 : Blo 706319 1590011 := bstep (se 1 (by rfl) ⟨1192508, by rfl⟩ : syracuseStep 1590011 = 2385017) B2385017
theorem B1196795 : Blo 706319 1196795 := bstep (se 1 (by rfl) ⟨897596, by rfl⟩ : syracuseStep 1196795 = 1795193) B1795193
theorem B1590047 : Blo 706319 1590047 := bstep (se 1 (by rfl) ⟨1192535, by rfl⟩ : syracuseStep 1590047 = 2385071) B2385071
theorem B98321201 : Blo 706319 98321201 := bstep (se 2 (by rfl) ⟨36870450, by rfl⟩ : syracuseStep 98321201 = 73740901) B73740901
theorem B5751917 : Blo 706319 5751917 := bstep (se 3 (by rfl) ⟨1078484, by rfl⟩ : syracuseStep 5751917 = 2156969) B2156969
theorem B98158301 : Blo 706319 98158301 := bstep (se 3 (by rfl) ⟨18404681, by rfl⟩ : syracuseStep 98158301 = 36809363) B36809363
theorem B706415 : Blo 706319 706415 := bstep (se 1 (by rfl) ⟨529811, by rfl⟩ : syracuseStep 706415 = 1059623) B1059623
theorem B706463 : Blo 706319 706463 := bstep (se 1 (by rfl) ⟨529847, by rfl⟩ : syracuseStep 706463 = 1059695) B1059695
theorem B1591343 : Blo 706319 1591343 := bstep (se 1 (by rfl) ⟨1193507, by rfl⟩ : syracuseStep 1591343 = 2387015) B2387015
theorem B706631 : Blo 706319 706631 := bstep (se 1 (by rfl) ⟨529973, by rfl⟩ : syracuseStep 706631 = 1059947) B1059947
theorem B1788065 : Blo 706319 1788065 := bstep (se 2 (by rfl) ⟨670524, by rfl⟩ : syracuseStep 1788065 = 1341049) B1341049
theorem B706791 : Blo 706319 706791 := bstep (se 1 (by rfl) ⟨530093, by rfl⟩ : syracuseStep 706791 = 1060187) B1060187
theorem B706811 : Blo 706319 706811 := bstep (se 1 (by rfl) ⟨530108, by rfl⟩ : syracuseStep 706811 = 1060217) B1060217
theorem B706815 : Blo 706319 706815 := bstep (se 1 (by rfl) ⟨530111, by rfl⟩ : syracuseStep 706815 = 1060223) B1060223
theorem B706971 : Blo 706319 706971 := bstep (se 1 (by rfl) ⟨530228, by rfl⟩ : syracuseStep 706971 = 1060457) B1060457
theorem B707231 : Blo 706319 707231 := bstep (se 1 (by rfl) ⟨530423, by rfl⟩ : syracuseStep 707231 = 1060847) B1060847
theorem B707311 : Blo 706319 707311 := bstep (se 1 (by rfl) ⟨530483, by rfl⟩ : syracuseStep 707311 = 1060967) B1060967
theorem B1592063 : Blo 706319 1592063 := bstep (se 1 (by rfl) ⟨1194047, by rfl⟩ : syracuseStep 1592063 = 2388095) B2388095
theorem B707391 : Blo 706319 707391 := bstep (se 1 (by rfl) ⟨530543, by rfl⟩ : syracuseStep 707391 = 1061087) B1061087
theorem B707431 : Blo 706319 707431 := bstep (se 1 (by rfl) ⟨530573, by rfl⟩ : syracuseStep 707431 = 1061147) B1061147
theorem B707695 : Blo 706319 707695 := bstep (se 1 (by rfl) ⟨530771, by rfl⟩ : syracuseStep 707695 = 1061543) B1061543
theorem B707775 : Blo 706319 707775 := bstep (se 1 (by rfl) ⟨530831, by rfl⟩ : syracuseStep 707775 = 1061663) B1061663
theorem B707791 : Blo 706319 707791 := bstep (se 1 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 707791 = 1061687) B1061687
theorem B707867 : Blo 706319 707867 := bstep (se 1 (by rfl) ⟨530900, by rfl⟩ : syracuseStep 707867 = 1061801) B1061801
theorem B707911 : Blo 706319 707911 := bstep (se 1 (by rfl) ⟨530933, by rfl⟩ : syracuseStep 707911 = 1061867) B1061867
theorem B708095 : Blo 706319 708095 := bstep (se 1 (by rfl) ⟨531071, by rfl⟩ : syracuseStep 708095 = 1062143) B1062143
theorem B708123 : Blo 706319 708123 := bstep (se 1 (by rfl) ⟨531092, by rfl⟩ : syracuseStep 708123 = 1062185) B1062185
theorem B1593071 : Blo 706319 1593071 := bstep (se 1 (by rfl) ⟨1194803, by rfl⟩ : syracuseStep 1593071 = 2389607) B2389607
theorem B708519 : Blo 706319 708519 := bstep (se 1 (by rfl) ⟨531389, by rfl⟩ : syracuseStep 708519 = 1062779) B1062779
theorem B708543 : Blo 706319 708543 := bstep (se 1 (by rfl) ⟨531407, by rfl⟩ : syracuseStep 708543 = 1062815) B1062815
theorem B1593287 : Blo 706319 1593287 := bstep (se 1 (by rfl) ⟨1194965, by rfl⟩ : syracuseStep 1593287 = 2389931) B2389931
theorem B1593323 : Blo 706319 1593323 := bstep (se 1 (by rfl) ⟨1194992, by rfl⟩ : syracuseStep 1593323 = 2389985) B2389985
theorem B708679 : Blo 706319 708679 := bstep (se 1 (by rfl) ⟨531509, by rfl⟩ : syracuseStep 708679 = 1063019) B1063019
theorem B708699 : Blo 706319 708699 := bstep (se 1 (by rfl) ⟨531524, by rfl⟩ : syracuseStep 708699 = 1063049) B1063049
theorem B708799 : Blo 706319 708799 := bstep (se 1 (by rfl) ⟨531599, by rfl⟩ : syracuseStep 708799 = 1063199) B1063199
theorem B1593647 : Blo 706319 1593647 := bstep (se 1 (by rfl) ⟨1195235, by rfl⟩ : syracuseStep 1593647 = 2390471) B2390471
theorem B3396127 : Blo 706319 3396127 := bstep (se 1 (by rfl) ⟨2547095, by rfl⟩ : syracuseStep 3396127 = 5094191) B5094191
theorem B709247 : Blo 706319 709247 := bstep (se 1 (by rfl) ⟨531935, by rfl⟩ : syracuseStep 709247 = 1063871) B1063871
theorem B709279 : Blo 706319 709279 := bstep (se 1 (by rfl) ⟨531959, by rfl⟩ : syracuseStep 709279 = 1063919) B1063919
theorem B709403 : Blo 706319 709403 := bstep (se 1 (by rfl) ⟨532052, by rfl⟩ : syracuseStep 709403 = 1064105) B1064105
theorem B4543391 : Blo 706319 4543391 := bstep (se 1 (by rfl) ⟨3407543, by rfl⟩ : syracuseStep 4543391 = 6815087) B6815087
theorem B709663 : Blo 706319 709663 := bstep (se 1 (by rfl) ⟨532247, by rfl⟩ : syracuseStep 709663 = 1064495) B1064495
theorem B709679 : Blo 706319 709679 := bstep (se 1 (by rfl) ⟨532259, by rfl⟩ : syracuseStep 709679 = 1064519) B1064519
theorem B709735 : Blo 706319 709735 := bstep (se 1 (by rfl) ⟨532301, by rfl⟩ : syracuseStep 709735 = 1064603) B1064603
theorem B709799 : Blo 706319 709799 := bstep (se 1 (by rfl) ⟨532349, by rfl⟩ : syracuseStep 709799 = 1064699) B1064699
theorem B1594619 : Blo 706319 1594619 := bstep (se 1 (by rfl) ⟨1195964, by rfl⟩ : syracuseStep 1594619 = 2391929) B2391929
theorem B710111 : Blo 706319 710111 := bstep (se 1 (by rfl) ⟨532583, by rfl⟩ : syracuseStep 710111 = 1065167) B1065167
theorem B4085801 : Blo 706319 4085801 := bstep (se 2 (by rfl) ⟨1532175, by rfl⟩ : syracuseStep 4085801 = 3064351) B3064351
theorem B1726591 : Blo 706319 1726591 := bstep (se 1 (by rfl) ⟨1294943, by rfl⟩ : syracuseStep 1726591 = 2589887) B2589887
theorem B3070187 : Blo 706319 3070187 := bstep (se 1 (by rfl) ⟨2302640, by rfl⟩ : syracuseStep 3070187 = 4605281) B4605281
theorem B1595897 : Blo 706319 1595897 := bstep (se 2 (by rfl) ⟨598461, by rfl⟩ : syracuseStep 1595897 = 1196923) B1196923
theorem B3824495 : Blo 706319 3824495 := bstep (se 1 (by rfl) ⟨2868371, by rfl⟩ : syracuseStep 3824495 = 5736743) B5736743
theorem B2153747 : Blo 706319 2153747 := bstep (se 1 (by rfl) ⟨1615310, by rfl⟩ : syracuseStep 2153747 = 3230621) B3230621
theorem B3824923 : Blo 706319 3824923 := bstep (se 1 (by rfl) ⟨2868692, by rfl⟩ : syracuseStep 3824923 = 5737385) B5737385
theorem B1597679 : Blo 706319 1597679 := bstep (se 1 (by rfl) ⟨1198259, by rfl⟩ : syracuseStep 1597679 = 2396519) B2396519
theorem B13591111 : Blo 706319 13591111 := bstep (se 1 (by rfl) ⟨10193333, by rfl⟩ : syracuseStep 13591111 = 20386667) B20386667
theorem B1794899 : Blo 706319 1794899 := bstep (se 1 (by rfl) ⟨1346174, by rfl⟩ : syracuseStep 1794899 = 2692349) B2692349
theorem B2384855 : Blo 706319 2384855 := bstep (se 1 (by rfl) ⟨1788641, by rfl⟩ : syracuseStep 2384855 = 3577283) B3577283
theorem B1008617 : Blo 706319 1008617 := bstep (se 2 (by rfl) ⟨378231, by rfl⟩ : syracuseStep 1008617 = 756463) B756463
theorem B14574647 : Blo 706319 14574647 := bstep (se 1 (by rfl) ⟨10930985, by rfl⟩ : syracuseStep 14574647 = 21861971) B21861971
theorem B6054983 : Blo 706319 6054983 := bstep (se 1 (by rfl) ⟨4541237, by rfl⟩ : syracuseStep 6054983 = 9082475) B9082475
theorem B3238667 : Blo 706319 3238667 := bstep (se 1 (by rfl) ⟨2429000, by rfl⟩ : syracuseStep 3238667 = 4858001) B4858001
theorem B1075999 : Blo 706319 1075999 := bstep (se 1 (by rfl) ⟨806999, by rfl⟩ : syracuseStep 1075999 = 1613999) B1613999
theorem B2386745 : Blo 706319 2386745 := bstep (se 2 (by rfl) ⟨895029, by rfl⟩ : syracuseStep 2386745 = 1790059) B1790059
theorem B1797815 : Blo 706319 1797815 := bstep (se 1 (by rfl) ⟨1348361, by rfl⟩ : syracuseStep 1797815 = 2696723) B2696723
theorem B2158807 : Blo 706319 2158807 := bstep (se 1 (by rfl) ⟨1619105, by rfl⟩ : syracuseStep 2158807 = 3238211) B3238211
theorem B2388203 : Blo 706319 2388203 := bstep (se 1 (by rfl) ⟨1791152, by rfl⟩ : syracuseStep 2388203 = 3582305) B3582305
theorem B2388905 : Blo 706319 2388905 := bstep (se 2 (by rfl) ⟨895839, by rfl⟩ : syracuseStep 2388905 = 1791679) B1791679
theorem B6060041 : Blo 706319 6060041 := bstep (se 2 (by rfl) ⟨2272515, by rfl⟩ : syracuseStep 6060041 = 4545031) B4545031
theorem B719647 : Blo 706319 719647 := bstep (se 1 (by rfl) ⟨539735, by rfl⟩ : syracuseStep 719647 = 1079471) B1079471
theorem B2554735 : Blo 706319 2554735 := bstep (se 1 (by rfl) ⟨1916051, by rfl⟩ : syracuseStep 2554735 = 3832103) B3832103
theorem B5110739 : Blo 706319 5110739 := bstep (se 1 (by rfl) ⟨3833054, by rfl⟩ : syracuseStep 5110739 = 7666109) B7666109
theorem B1703119 : Blo 706319 1703119 := bstep (se 1 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 1703119 = 2554679) B2554679
theorem B49053113 : Blo 706319 49053113 := bstep (se 2 (by rfl) ⟨18394917, by rfl⟩ : syracuseStep 49053113 = 36789835) B36789835
theorem B2391659 : Blo 706319 2391659 := bstep (se 1 (by rfl) ⟨1793744, by rfl⟩ : syracuseStep 2391659 = 3587489) B3587489
theorem B2686715 : Blo 706319 2686715 := bstep (se 1 (by rfl) ⟨2015036, by rfl⟩ : syracuseStep 2686715 = 4030073) B4030073
theorem B1277945 : Blo 706319 1277945 := bstep (se 2 (by rfl) ⟨479229, by rfl⟩ : syracuseStep 1277945 = 958459) B958459
theorem B151584857 : Blo 706319 151584857 := bstep (se 2 (by rfl) ⟨56844321, by rfl⟩ : syracuseStep 151584857 = 113688643) B113688643
theorem B3834611 : Blo 706319 3834611 := bstep (se 1 (by rfl) ⟨2875958, by rfl⟩ : syracuseStep 3834611 = 5751917) B5751917
theorem B18121481 : Blo 706319 18121481 := bstep (se 2 (by rfl) ⟨6795555, by rfl⟩ : syracuseStep 18121481 = 13591111) B13591111
theorem B9700235 : Blo 706319 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B65438867 : Blo 706319 65438867 := bstep (se 1 (by rfl) ⟨49079150, by rfl⟩ : syracuseStep 65438867 = 98158301) B98158301
theorem B1705655 : Blo 706319 1705655 := bstep (se 1 (by rfl) ⟨1279241, by rfl⟩ : syracuseStep 1705655 = 2558483) B2558483
theorem B2689645 : Blo 706319 2689645 := bstep (se 3 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 2689645 = 1008617) B1008617
theorem B12094109 : Blo 706319 12094109 := bstep (se 3 (by rfl) ⟨2267645, by rfl⟩ : syracuseStep 12094109 = 4535291) B4535291
theorem B4590415 : Blo 706319 4590415 := bstep (se 1 (by rfl) ⟨3442811, by rfl⟩ : syracuseStep 4590415 = 6885623) B6885623
theorem B1510739 : Blo 706319 1510739 := bstep (se 1 (by rfl) ⟨1133054, by rfl⟩ : syracuseStep 1510739 = 2266109) B2266109
theorem B2723867 : Blo 706319 2723867 := bstep (se 1 (by rfl) ⟨2042900, by rfl⟩ : syracuseStep 2723867 = 4085801) B4085801
theorem B4853843 : Blo 706319 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B5116043 : Blo 706319 5116043 := bstep (se 1 (by rfl) ⟨3837032, by rfl⟩ : syracuseStep 5116043 = 7674065) B7674065
theorem B3838117 : Blo 706319 3838117 := bstep (se 4 (by rfl) ⟨359823, by rfl⟩ : syracuseStep 3838117 = 719647) B719647
theorem B20189483 : Blo 706319 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B1939169 : Blo 706319 1939169 := bstep (se 2 (by rfl) ⟨727188, by rfl⟩ : syracuseStep 1939169 = 1454377) B1454377
theorem B1513199 : Blo 706319 1513199 := bstep (se 1 (by rfl) ⟨1134899, by rfl⟩ : syracuseStep 1513199 = 2269799) B2269799
theorem B4528169 : Blo 706319 4528169 := bstep (se 2 (by rfl) ⟨1698063, by rfl⟩ : syracuseStep 4528169 = 3396127) B3396127
theorem B4036655 : Blo 706319 4036655 := bstep (se 1 (by rfl) ⟨3027491, by rfl⟩ : syracuseStep 4036655 = 6054983) B6054983
theorem B3546449 : Blo 706319 3546449 := bstep (se 2 (by rfl) ⟨1329918, by rfl⟩ : syracuseStep 3546449 = 2659837) B2659837
theorem B2694991 : Blo 706319 2694991 := bstep (se 1 (by rfl) ⟨2021243, by rfl⟩ : syracuseStep 2694991 = 4042487) B4042487
theorem B4038821 : Blo 706319 4038821 := bstep (se 4 (by rfl) ⟨378639, by rfl⟩ : syracuseStep 4038821 = 757279) B757279
theorem B2302121 : Blo 706319 2302121 := bstep (se 2 (by rfl) ⟨863295, by rfl⟩ : syracuseStep 2302121 = 1726591) B1726591
theorem B1516087 : Blo 706319 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B5743325 : Blo 706319 5743325 := bstep (se 3 (by rfl) ⟨1076873, by rfl⟩ : syracuseStep 5743325 = 2153747) B2153747
theorem B1909631 : Blo 706319 1909631 := bstep (se 1 (by rfl) ⟨1432223, by rfl⟩ : syracuseStep 1909631 = 2864447) B2864447
theorem B4040027 : Blo 706319 4040027 := bstep (se 1 (by rfl) ⟨3030020, by rfl⟩ : syracuseStep 4040027 = 6060041) B6060041
theorem B2270825 : Blo 706319 2270825 := bstep (se 2 (by rfl) ⟨851559, by rfl⟩ : syracuseStep 2270825 = 1703119) B1703119
theorem B796315 : Blo 706319 796315 := bstep (se 1 (by rfl) ⟨597236, by rfl⟩ : syracuseStep 796315 = 1194473) B1194473
theorem B796927 : Blo 706319 796927 := bstep (se 1 (by rfl) ⟨597695, by rfl⟩ : syracuseStep 796927 = 1195391) B1195391
theorem B796999 : Blo 706319 796999 := bstep (se 1 (by rfl) ⟨597749, by rfl⟩ : syracuseStep 796999 = 1195499) B1195499
theorem B7678739 : Blo 706319 7678739 := bstep (se 1 (by rfl) ⟨5759054, by rfl⟩ : syracuseStep 7678739 = 11518109) B11518109
theorem B4041737 : Blo 706319 4041737 := bstep (se 2 (by rfl) ⟨1515651, by rfl⟩ : syracuseStep 4041737 = 3031303) B3031303
theorem B1059977 : Blo 706319 1059977 := bstep (se 2 (by rfl) ⟨397491, by rfl⟩ : syracuseStep 1059977 = 794983) B794983
theorem B1060007 : Blo 706319 1060007 := bstep (se 1 (by rfl) ⟨795005, by rfl⟩ : syracuseStep 1060007 = 1590011) B1590011
theorem B797863 : Blo 706319 797863 := bstep (se 1 (by rfl) ⟨598397, by rfl⟩ : syracuseStep 797863 = 1196795) B1196795
theorem B1060031 : Blo 706319 1060031 := bstep (se 1 (by rfl) ⟨795023, by rfl⟩ : syracuseStep 1060031 = 1590047) B1590047
theorem B65547467 : Blo 706319 65547467 := bstep (se 1 (by rfl) ⟨49160600, by rfl⟩ : syracuseStep 65547467 = 98321201) B98321201
theorem B10202561 : Blo 706319 10202561 := bstep (se 2 (by rfl) ⟨3825960, by rfl⟩ : syracuseStep 10202561 = 7651921) B7651921
theorem B1060841 : Blo 706319 1060841 := bstep (se 2 (by rfl) ⟨397815, by rfl⟩ : syracuseStep 1060841 = 795631) B795631
theorem B1060895 : Blo 706319 1060895 := bstep (se 1 (by rfl) ⟨795671, by rfl⟩ : syracuseStep 1060895 = 1591343) B1591343
theorem B1192043 : Blo 706319 1192043 := bstep (se 1 (by rfl) ⟨894032, by rfl⟩ : syracuseStep 1192043 = 1788065) B1788065
theorem B1061375 : Blo 706319 1061375 := bstep (se 1 (by rfl) ⟨796031, by rfl⟩ : syracuseStep 1061375 = 1592063) B1592063
theorem B1062047 : Blo 706319 1062047 := bstep (se 1 (by rfl) ⟨796535, by rfl⟩ : syracuseStep 1062047 = 1593071) B1593071
theorem B1062191 : Blo 706319 1062191 := bstep (se 1 (by rfl) ⟨796643, by rfl⟩ : syracuseStep 1062191 = 1593287) B1593287
theorem B1062215 : Blo 706319 1062215 := bstep (se 1 (by rfl) ⟨796661, by rfl⟩ : syracuseStep 1062215 = 1593323) B1593323
theorem B12891545 : Blo 706319 12891545 := bstep (se 2 (by rfl) ⟨4834329, by rfl⟩ : syracuseStep 12891545 = 9668659) B9668659
theorem B1062431 : Blo 706319 1062431 := bstep (se 1 (by rfl) ⟨796823, by rfl⟩ : syracuseStep 1062431 = 1593647) B1593647
theorem B1193737 : Blo 706319 1193737 := bstep (se 2 (by rfl) ⟨447651, by rfl⟩ : syracuseStep 1193737 = 895303) B895303
theorem B3028927 : Blo 706319 3028927 := bstep (se 1 (by rfl) ⟨2271695, by rfl⟩ : syracuseStep 3028927 = 4543391) B4543391
theorem B3586031 : Blo 706319 3586031 := bstep (se 1 (by rfl) ⟨2689523, by rfl⟩ : syracuseStep 3586031 = 5379047) B5379047
theorem B1063079 : Blo 706319 1063079 := bstep (se 1 (by rfl) ⟨797309, by rfl⟩ : syracuseStep 1063079 = 1594619) B1594619
theorem B2013407 : Blo 706319 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B1063289 : Blo 706319 1063289 := bstep (se 2 (by rfl) ⟨398733, by rfl⟩ : syracuseStep 1063289 = 797467) B797467
theorem B2013977 : Blo 706319 2013977 := bstep (se 2 (by rfl) ⟨755241, by rfl⟩ : syracuseStep 2013977 = 1510483) B1510483
theorem B2046791 : Blo 706319 2046791 := bstep (se 1 (by rfl) ⟨1535093, by rfl⟩ : syracuseStep 2046791 = 3070187) B3070187
theorem B1063931 : Blo 706319 1063931 := bstep (se 1 (by rfl) ⟨797948, by rfl⟩ : syracuseStep 1063931 = 1595897) B1595897
theorem B2014217 : Blo 706319 2014217 := bstep (se 2 (by rfl) ⟨755331, by rfl⟩ : syracuseStep 2014217 = 1510663) B1510663
theorem B1064585 : Blo 706319 1064585 := bstep (se 2 (by rfl) ⟨399219, by rfl⟩ : syracuseStep 1064585 = 798439) B798439
theorem B1065119 : Blo 706319 1065119 := bstep (se 1 (by rfl) ⟨798839, by rfl⟩ : syracuseStep 1065119 = 1597679) B1597679
theorem B1196599 : Blo 706319 1196599 := bstep (se 1 (by rfl) ⟨897449, by rfl⟩ : syracuseStep 1196599 = 1794899) B1794899
theorem B1589903 : Blo 706319 1589903 := bstep (se 1 (by rfl) ⟨1192427, by rfl⟩ : syracuseStep 1589903 = 2384855) B2384855
theorem B9716431 : Blo 706319 9716431 := bstep (se 1 (by rfl) ⟨7287323, by rfl⟩ : syracuseStep 9716431 = 14574647) B14574647
theorem B1590497 : Blo 706319 1590497 := bstep (se 2 (by rfl) ⟨596436, by rfl⟩ : syracuseStep 1590497 = 1192873) B1192873
theorem B1590569 : Blo 706319 1590569 := bstep (se 2 (by rfl) ⟨596463, by rfl⟩ : syracuseStep 1590569 = 1192927) B1192927
theorem B3589919 : Blo 706319 3589919 := bstep (se 1 (by rfl) ⟨2692439, by rfl⟩ : syracuseStep 3589919 = 5384879) B5384879
theorem B706375 : Blo 706319 706375 := bstep (se 1 (by rfl) ⟨529781, by rfl⟩ : syracuseStep 706375 = 1059563) B1059563
theorem B706407 : Blo 706319 706407 := bstep (se 1 (by rfl) ⟨529805, by rfl⟩ : syracuseStep 706407 = 1059611) B1059611
theorem B1591163 : Blo 706319 1591163 := bstep (se 1 (by rfl) ⟨1193372, by rfl⟩ : syracuseStep 1591163 = 2386745) B2386745
theorem B6801479 : Blo 706319 6801479 := bstep (se 1 (by rfl) ⟨5101109, by rfl⟩ : syracuseStep 6801479 = 10202219) B10202219
theorem B8046701 : Blo 706319 8046701 := bstep (se 3 (by rfl) ⟨1508756, by rfl⟩ : syracuseStep 8046701 = 3017513) B3017513
theorem B1591433 : Blo 706319 1591433 := bstep (se 2 (by rfl) ⟨596787, by rfl⟩ : syracuseStep 1591433 = 1193575) B1193575
theorem B706975 : Blo 706319 706975 := bstep (se 1 (by rfl) ⟨530231, by rfl⟩ : syracuseStep 706975 = 1060463) B1060463
theorem B1198543 : Blo 706319 1198543 := bstep (se 1 (by rfl) ⟨898907, by rfl⟩ : syracuseStep 1198543 = 1797815) B1797815
theorem B707047 : Blo 706319 707047 := bstep (se 1 (by rfl) ⟨530285, by rfl⟩ : syracuseStep 707047 = 1060571) B1060571
theorem B707055 : Blo 706319 707055 := bstep (se 1 (by rfl) ⟨530291, by rfl⟩ : syracuseStep 707055 = 1060583) B1060583
theorem B1592135 : Blo 706319 1592135 := bstep (se 1 (by rfl) ⟨1194101, by rfl⟩ : syracuseStep 1592135 = 2388203) B2388203
theorem B707495 : Blo 706319 707495 := bstep (se 1 (by rfl) ⟨530621, by rfl⟩ : syracuseStep 707495 = 1061243) B1061243
theorem B707567 : Blo 706319 707567 := bstep (se 1 (by rfl) ⟨530675, by rfl⟩ : syracuseStep 707567 = 1061351) B1061351
theorem B1362943 : Blo 706319 1362943 := bstep (se 1 (by rfl) ⟨1022207, by rfl⟩ : syracuseStep 1362943 = 2044415) B2044415
theorem B5098717 : Blo 706319 5098717 := bstep (se 3 (by rfl) ⟨956009, by rfl⟩ : syracuseStep 5098717 = 1912019) B1912019
theorem B707815 : Blo 706319 707815 := bstep (se 1 (by rfl) ⟨530861, by rfl⟩ : syracuseStep 707815 = 1061723) B1061723
theorem B1592603 : Blo 706319 1592603 := bstep (se 1 (by rfl) ⟨1194452, by rfl⟩ : syracuseStep 1592603 = 2388905) B2388905
theorem B707903 : Blo 706319 707903 := bstep (se 1 (by rfl) ⟨530927, by rfl⟩ : syracuseStep 707903 = 1061855) B1061855
theorem B707943 : Blo 706319 707943 := bstep (se 1 (by rfl) ⟨530957, by rfl⟩ : syracuseStep 707943 = 1061915) B1061915
theorem B708255 : Blo 706319 708255 := bstep (se 1 (by rfl) ⟨531191, by rfl⟩ : syracuseStep 708255 = 1062383) B1062383
theorem B3591863 : Blo 706319 3591863 := bstep (se 1 (by rfl) ⟨2693897, by rfl⟩ : syracuseStep 3591863 = 5387795) B5387795
theorem B708335 : Blo 706319 708335 := bstep (se 1 (by rfl) ⟨531251, by rfl⟩ : syracuseStep 708335 = 1062503) B1062503
theorem B3395819 : Blo 706319 3395819 := bstep (se 1 (by rfl) ⟨2546864, by rfl⟩ : syracuseStep 3395819 = 5093729) B5093729
theorem B5099897 : Blo 706319 5099897 := bstep (se 2 (by rfl) ⟨1912461, by rfl⟩ : syracuseStep 5099897 = 3824923) B3824923
theorem B709479 : Blo 706319 709479 := bstep (se 1 (by rfl) ⟨532109, by rfl⟩ : syracuseStep 709479 = 1064219) B1064219
theorem B2020265 : Blo 706319 2020265 := bstep (se 2 (by rfl) ⟨757599, by rfl⟩ : syracuseStep 2020265 = 1515199) B1515199
theorem B1594439 : Blo 706319 1594439 := bstep (se 1 (by rfl) ⟨1195829, by rfl⟩ : syracuseStep 1594439 = 2391659) B2391659
theorem B49599611 : Blo 706319 49599611 := bstep (se 1 (by rfl) ⟨37199708, by rfl⟩ : syracuseStep 49599611 = 74399417) B74399417
theorem B33084571 : Blo 706319 33084571 := bstep (se 1 (by rfl) ⟨24813428, by rfl⟩ : syracuseStep 33084571 = 49626857) B49626857
theorem B1791143 : Blo 706319 1791143 := bstep (se 1 (by rfl) ⟨1343357, by rfl⟩ : syracuseStep 1791143 = 2686715) B2686715
theorem B709991 : Blo 706319 709991 := bstep (se 1 (by rfl) ⟨532493, by rfl⟩ : syracuseStep 709991 = 1064987) B1064987
theorem B1594745 : Blo 706319 1594745 := bstep (se 2 (by rfl) ⟨598029, by rfl⟩ : syracuseStep 1594745 = 1196059) B1196059
theorem B710171 : Blo 706319 710171 := bstep (se 1 (by rfl) ⟨532628, by rfl⟩ : syracuseStep 710171 = 1065257) B1065257
theorem B710271 : Blo 706319 710271 := bstep (se 1 (by rfl) ⟨532703, by rfl⟩ : syracuseStep 710271 = 1065407) B1065407
theorem B1595105 : Blo 706319 1595105 := bstep (se 2 (by rfl) ⟨598164, by rfl⟩ : syracuseStep 1595105 = 1196329) B1196329
theorem B1791841 : Blo 706319 1791841 := bstep (se 2 (by rfl) ⟨671940, by rfl⟩ : syracuseStep 1791841 = 1343881) B1343881
theorem B1595987 : Blo 706319 1595987 := bstep (se 1 (by rfl) ⟨1196990, by rfl⟩ : syracuseStep 1595987 = 2393981) B2393981
theorem B1596095 : Blo 706319 1596095 := bstep (se 1 (by rfl) ⟨1197071, by rfl⟩ : syracuseStep 1596095 = 2394143) B2394143
theorem B1596527 : Blo 706319 1596527 := bstep (se 1 (by rfl) ⟨1197395, by rfl⟩ : syracuseStep 1596527 = 2394791) B2394791
theorem B1793299 : Blo 706319 1793299 := bstep (se 1 (by rfl) ⟨1344974, by rfl⟩ : syracuseStep 1793299 = 2689949) B2689949
theorem B3595913 : Blo 706319 3595913 := bstep (se 2 (by rfl) ⟨1348467, by rfl⟩ : syracuseStep 3595913 = 2696935) B2696935
theorem B1597103 : Blo 706319 1597103 := bstep (se 1 (by rfl) ⟨1197827, by rfl⟩ : syracuseStep 1597103 = 2395655) B2395655
theorem B30629825 : Blo 706319 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B1597715 : Blo 706319 1597715 := bstep (se 1 (by rfl) ⟨1198286, by rfl⟩ : syracuseStep 1597715 = 2396573) B2396573
theorem B1794383 : Blo 706319 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B1597823 : Blo 706319 1597823 := bstep (se 1 (by rfl) ⟨1198367, by rfl⟩ : syracuseStep 1597823 = 2396735) B2396735
theorem B1434665 : Blo 706319 1434665 := bstep (se 2 (by rfl) ⟨537999, by rfl⟩ : syracuseStep 1434665 = 1075999) B1075999
theorem B3630361 : Blo 706319 3630361 := bstep (se 2 (by rfl) ⟨1361385, by rfl⟩ : syracuseStep 3630361 = 2722771) B2722771
theorem B1795355 : Blo 706319 1795355 := bstep (se 1 (by rfl) ⟨1346516, by rfl⟩ : syracuseStep 1795355 = 2693033) B2693033
theorem B5826329 : Blo 706319 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B3827519 : Blo 706319 3827519 := bstep (se 1 (by rfl) ⟨2870639, by rfl⟩ : syracuseStep 3827519 = 5741279) B5741279
theorem B2549663 : Blo 706319 2549663 := bstep (se 1 (by rfl) ⟨1912247, by rfl⟩ : syracuseStep 2549663 = 3824495) B3824495
theorem B2386151 : Blo 706319 2386151 := bstep (se 1 (by rfl) ⟨1789613, by rfl⟩ : syracuseStep 2386151 = 3579227) B3579227
theorem B1796539 : Blo 706319 1796539 := bstep (se 1 (by rfl) ⟨1347404, by rfl⟩ : syracuseStep 1796539 = 2694809) B2694809
theorem B8055449 : Blo 706319 8055449 := bstep (se 2 (by rfl) ⟨3020793, by rfl⟩ : syracuseStep 8055449 = 6041587) B6041587
theorem B2878409 : Blo 706319 2878409 := bstep (se 2 (by rfl) ⟨1079403, by rfl⟩ : syracuseStep 2878409 = 2158807) B2158807
theorem B2159111 : Blo 706319 2159111 := bstep (se 1 (by rfl) ⟨1619333, by rfl⟩ : syracuseStep 2159111 = 3238667) B3238667
theorem B27162539 : Blo 706319 27162539 := bstep (se 1 (by rfl) ⟨20371904, by rfl⟩ : syracuseStep 27162539 = 40743809) B40743809
theorem B3406313 : Blo 706319 3406313 := bstep (se 2 (by rfl) ⟨1277367, by rfl⟩ : syracuseStep 3406313 = 2554735) B2554735
theorem B1342727 : Blo 706319 1342727 := bstep (se 1 (by rfl) ⟨1007045, by rfl⟩ : syracuseStep 1342727 = 2014091) B2014091
theorem B3407159 : Blo 706319 3407159 := bstep (se 1 (by rfl) ⟨2555369, by rfl⟩ : syracuseStep 3407159 = 5110739) B5110739
theorem B32702075 : Blo 706319 32702075 := bstep (se 1 (by rfl) ⟨24526556, by rfl⟩ : syracuseStep 32702075 = 49053113) B49053113
theorem B851963 : Blo 706319 851963 := bstep (se 1 (by rfl) ⟨638972, by rfl⟩ : syracuseStep 851963 = 1277945) B1277945
theorem B101056571 : Blo 706319 101056571 := bstep (se 1 (by rfl) ⟨75792428, by rfl⟩ : syracuseStep 101056571 = 151584857) B151584857
theorem B2556407 : Blo 706319 2556407 := bstep (se 1 (by rfl) ⟨1917305, by rfl⟩ : syracuseStep 2556407 = 3834611) B3834611
theorem B2393279 : Blo 706319 2393279 := bstep (se 1 (by rfl) ⟨1794959, by rfl⟩ : syracuseStep 2393279 = 3589919) B3589919
theorem B8062739 : Blo 706319 8062739 := bstep (se 1 (by rfl) ⟨6047054, by rfl⟩ : syracuseStep 8062739 = 12094109) B12094109
theorem B2394575 : Blo 706319 2394575 := bstep (se 1 (by rfl) ⟨1795931, by rfl⟩ : syracuseStep 2394575 = 3591863) B3591863
theorem B3410695 : Blo 706319 3410695 := bstep (se 1 (by rfl) ⟨2558021, by rfl⟩ : syracuseStep 3410695 = 5116043) B5116043
theorem B2263879 : Blo 706319 2263879 := bstep (se 1 (by rfl) ⟨1697909, by rfl⟩ : syracuseStep 2263879 = 3395819) B3395819
theorem B2395385 : Blo 706319 2395385 := bstep (se 2 (by rfl) ⟨898269, by rfl⟩ : syracuseStep 2395385 = 1796539) B1796539
theorem B1346843 : Blo 706319 1346843 := bstep (se 1 (by rfl) ⟨1010132, by rfl⟩ : syracuseStep 1346843 = 2020265) B2020265
theorem B33066407 : Blo 706319 33066407 := bstep (se 1 (by rfl) ⟨24799805, by rfl⟩ : syracuseStep 33066407 = 49599611) B49599611
theorem B3018779 : Blo 706319 3018779 := bstep (se 1 (by rfl) ⟨2264084, by rfl⟩ : syracuseStep 3018779 = 4528169) B4528169
theorem B2691103 : Blo 706319 2691103 := bstep (se 1 (by rfl) ⟨2018327, by rfl⟩ : syracuseStep 2691103 = 4036655) B4036655
theorem B24482213 : Blo 706319 24482213 := bstep (se 4 (by rfl) ⟨2295207, by rfl⟩ : syracuseStep 24482213 = 4590415) B4590415
theorem B4035197 : Blo 706319 4035197 := bstep (se 3 (by rfl) ⟨756599, by rfl⟩ : syracuseStep 4035197 = 1513199) B1513199
theorem B2364299 : Blo 706319 2364299 := bstep (se 1 (by rfl) ⟨1773224, by rfl⟩ : syracuseStep 2364299 = 3546449) B3546449
theorem B2397275 : Blo 706319 2397275 := bstep (se 1 (by rfl) ⟨1797956, by rfl⟩ : syracuseStep 2397275 = 3595913) B3595913
theorem B20419883 : Blo 706319 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B2692547 : Blo 706319 2692547 := bstep (se 1 (by rfl) ⟨2019410, by rfl⟩ : syracuseStep 2692547 = 4038821) B4038821
theorem B5117489 : Blo 706319 5117489 := bstep (se 2 (by rfl) ⟨1919058, by rfl⟩ : syracuseStep 5117489 = 3838117) B3838117
theorem B956443 : Blo 706319 956443 := bstep (se 1 (by rfl) ⟨717332, by rfl⟩ : syracuseStep 956443 = 1434665) B1434665
theorem B2693351 : Blo 706319 2693351 := bstep (se 1 (by rfl) ⟨2020013, by rfl⟩ : syracuseStep 2693351 = 4040027) B4040027
theorem B1513883 : Blo 706319 1513883 := bstep (se 1 (by rfl) ⟨1135412, by rfl⟩ : syracuseStep 1513883 = 2270825) B2270825
theorem B9083501 : Blo 706319 9083501 := bstep (se 3 (by rfl) ⟨1703156, by rfl⟩ : syracuseStep 9083501 = 3406313) B3406313
theorem B44112761 : Blo 706319 44112761 := bstep (se 2 (by rfl) ⟨16542285, by rfl⟩ : syracuseStep 44112761 = 33084571) B33084571
theorem B5119159 : Blo 706319 5119159 := bstep (se 1 (by rfl) ⟨3839369, by rfl⟩ : syracuseStep 5119159 = 7678739) B7678739
theorem B2694491 : Blo 706319 2694491 := bstep (se 1 (by rfl) ⟨2020868, by rfl⟩ : syracuseStep 2694491 = 4041737) B4041737
theorem B4038569 : Blo 706319 4038569 := bstep (se 2 (by rfl) ⟨1514463, by rfl⟩ : syracuseStep 4038569 = 3028927) B3028927
theorem B794695 : Blo 706319 794695 := bstep (se 1 (by rfl) ⟨596021, by rfl⟩ : syracuseStep 794695 = 1192043) B1192043
theorem B8594363 : Blo 706319 8594363 := bstep (se 1 (by rfl) ⟨6445772, by rfl⟩ : syracuseStep 8594363 = 12891545) B12891545
theorem B895151 : Blo 706319 895151 := bstep (se 1 (by rfl) ⟨671363, by rfl⟩ : syracuseStep 895151 = 1342727) B1342727
theorem B2271439 : Blo 706319 2271439 := bstep (se 1 (by rfl) ⟨1703579, by rfl⟩ : syracuseStep 2271439 = 3407159) B3407159
theorem B21801383 : Blo 706319 21801383 := bstep (se 1 (by rfl) ⟨16351037, by rfl⟩ : syracuseStep 21801383 = 32702075) B32702075
theorem B2271901 : Blo 706319 2271901 := bstep (se 3 (by rfl) ⟨425981, by rfl⟩ : syracuseStep 2271901 = 851963) B851963
theorem B1059935 : Blo 706319 1059935 := bstep (se 1 (by rfl) ⟨794951, by rfl⟩ : syracuseStep 1059935 = 1589903) B1589903
theorem B6466823 : Blo 706319 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B43625911 : Blo 706319 43625911 := bstep (se 1 (by rfl) ⟨32719433, by rfl⟩ : syracuseStep 43625911 = 65438867) B65438867
theorem B1060331 : Blo 706319 1060331 := bstep (se 1 (by rfl) ⟨795248, by rfl⟩ : syracuseStep 1060331 = 1590497) B1590497
theorem B1060379 : Blo 706319 1060379 := bstep (se 1 (by rfl) ⟨795284, by rfl⟩ : syracuseStep 1060379 = 1590569) B1590569
theorem B12955241 : Blo 706319 12955241 := bstep (se 2 (by rfl) ⟨4858215, by rfl⟩ : syracuseStep 12955241 = 9716431) B9716431
theorem B1060775 : Blo 706319 1060775 := bstep (se 1 (by rfl) ⟨795581, by rfl⟩ : syracuseStep 1060775 = 1591163) B1591163
theorem B4534319 : Blo 706319 4534319 := bstep (se 1 (by rfl) ⟨3400739, by rfl⟩ : syracuseStep 4534319 = 6801479) B6801479
theorem B1060955 : Blo 706319 1060955 := bstep (se 1 (by rfl) ⟨795716, by rfl⟩ : syracuseStep 1060955 = 1591433) B1591433
theorem B1061423 : Blo 706319 1061423 := bstep (se 1 (by rfl) ⟨796067, by rfl⟩ : syracuseStep 1061423 = 1592135) B1592135
theorem B1061735 : Blo 706319 1061735 := bstep (se 1 (by rfl) ⟨796301, by rfl⟩ : syracuseStep 1061735 = 1592603) B1592603
theorem B1061753 : Blo 706319 1061753 := bstep (se 2 (by rfl) ⟨398157, by rfl⟩ : syracuseStep 1061753 = 796315) B796315
theorem B1815911 : Blo 706319 1815911 := bstep (se 1 (by rfl) ⟨1361933, by rfl⟩ : syracuseStep 1815911 = 2723867) B2723867
theorem B1062569 : Blo 706319 1062569 := bstep (se 2 (by rfl) ⟨398463, by rfl⟩ : syracuseStep 1062569 = 796927) B796927
theorem B1062665 : Blo 706319 1062665 := bstep (se 2 (by rfl) ⟨398499, by rfl⟩ : syracuseStep 1062665 = 796999) B796999
theorem B1062959 : Blo 706319 1062959 := bstep (se 1 (by rfl) ⟨797219, by rfl⟩ : syracuseStep 1062959 = 1594439) B1594439
theorem B1194095 : Blo 706319 1194095 := bstep (se 1 (by rfl) ⟨895571, by rfl⟩ : syracuseStep 1194095 = 1791143) B1791143
theorem B3586193 : Blo 706319 3586193 := bstep (se 2 (by rfl) ⟨1344822, by rfl⟩ : syracuseStep 3586193 = 2689645) B2689645
theorem B1063163 : Blo 706319 1063163 := bstep (se 1 (by rfl) ⟨797372, by rfl⟩ : syracuseStep 1063163 = 1594745) B1594745
theorem B1292779 : Blo 706319 1292779 := bstep (se 1 (by rfl) ⟨969584, by rfl⟩ : syracuseStep 1292779 = 1939169) B1939169
theorem B1063403 : Blo 706319 1063403 := bstep (se 1 (by rfl) ⟨797552, by rfl⟩ : syracuseStep 1063403 = 1595105) B1595105
theorem B1817257 : Blo 706319 1817257 := bstep (se 2 (by rfl) ⟨681471, by rfl⟩ : syracuseStep 1817257 = 1362943) B1362943
theorem B1063817 : Blo 706319 1063817 := bstep (se 2 (by rfl) ⟨398931, by rfl⟩ : syracuseStep 1063817 = 797863) B797863
theorem B6798289 : Blo 706319 6798289 := bstep (se 2 (by rfl) ⟨2549358, by rfl⟩ : syracuseStep 6798289 = 5098717) B5098717
theorem B1063991 : Blo 706319 1063991 := bstep (se 1 (by rfl) ⟨797993, by rfl⟩ : syracuseStep 1063991 = 1595987) B1595987
theorem B1064063 : Blo 706319 1064063 := bstep (se 1 (by rfl) ⟨798047, by rfl⟩ : syracuseStep 1064063 = 1596095) B1596095
theorem B1064351 : Blo 706319 1064351 := bstep (se 1 (by rfl) ⟨798263, by rfl⟩ : syracuseStep 1064351 = 1596527) B1596527
theorem B1064735 : Blo 706319 1064735 := bstep (se 1 (by rfl) ⟨798551, by rfl⟩ : syracuseStep 1064735 = 1597103) B1597103
theorem B1065143 : Blo 706319 1065143 := bstep (se 1 (by rfl) ⟨798857, by rfl⟩ : syracuseStep 1065143 = 1597715) B1597715
theorem B1196255 : Blo 706319 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B1065215 : Blo 706319 1065215 := bstep (se 1 (by rfl) ⟨798911, by rfl⟩ : syracuseStep 1065215 = 1597823) B1597823
theorem B1196903 : Blo 706319 1196903 := bstep (se 1 (by rfl) ⟨897677, by rfl⟩ : syracuseStep 1196903 = 1795355) B1795355
theorem B3884219 : Blo 706319 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B1590767 : Blo 706319 1590767 := bstep (se 1 (by rfl) ⟨1193075, by rfl⟩ : syracuseStep 1590767 = 2386151) B2386151
theorem B1918939 : Blo 706319 1918939 := bstep (se 1 (by rfl) ⟨1439204, by rfl⟩ : syracuseStep 1918939 = 2878409) B2878409
theorem B706651 : Blo 706319 706651 := bstep (se 1 (by rfl) ⟨529988, by rfl⟩ : syracuseStep 706651 = 1059977) B1059977
theorem B706671 : Blo 706319 706671 := bstep (se 1 (by rfl) ⟨530003, by rfl⟩ : syracuseStep 706671 = 1060007) B1060007
theorem B706687 : Blo 706319 706687 := bstep (se 1 (by rfl) ⟨530015, by rfl⟩ : syracuseStep 706687 = 1060031) B1060031
theorem B43698311 : Blo 706319 43698311 := bstep (se 1 (by rfl) ⟨32773733, by rfl⟩ : syracuseStep 43698311 = 65547467) B65547467
theorem B6801707 : Blo 706319 6801707 := bstep (se 1 (by rfl) ⟨5101280, by rfl⟩ : syracuseStep 6801707 = 10202561) B10202561
theorem B1591649 : Blo 706319 1591649 := bstep (se 2 (by rfl) ⟨596868, by rfl⟩ : syracuseStep 1591649 = 1193737) B1193737
theorem B707227 : Blo 706319 707227 := bstep (se 1 (by rfl) ⟨530420, by rfl⟩ : syracuseStep 707227 = 1060841) B1060841
theorem B707263 : Blo 706319 707263 := bstep (se 1 (by rfl) ⟨530447, by rfl⟩ : syracuseStep 707263 = 1060895) B1060895
theorem B707583 : Blo 706319 707583 := bstep (se 1 (by rfl) ⟨530687, by rfl⟩ : syracuseStep 707583 = 1061375) B1061375
theorem B708031 : Blo 706319 708031 := bstep (se 1 (by rfl) ⟨531023, by rfl⟩ : syracuseStep 708031 = 1062047) B1062047
theorem B708127 : Blo 706319 708127 := bstep (se 1 (by rfl) ⟨531095, by rfl⟩ : syracuseStep 708127 = 1062191) B1062191
theorem B708143 : Blo 706319 708143 := bstep (se 1 (by rfl) ⟨531107, by rfl⟩ : syracuseStep 708143 = 1062215) B1062215
theorem B708287 : Blo 706319 708287 := bstep (se 1 (by rfl) ⟨531215, by rfl⟩ : syracuseStep 708287 = 1062431) B1062431
theorem B18108359 : Blo 706319 18108359 := bstep (se 1 (by rfl) ⟨13581269, by rfl⟩ : syracuseStep 18108359 = 27162539) B27162539
theorem B708719 : Blo 706319 708719 := bstep (se 1 (by rfl) ⟨531539, by rfl⟩ : syracuseStep 708719 = 1063079) B1063079
theorem B708859 : Blo 706319 708859 := bstep (se 1 (by rfl) ⟨531644, by rfl⟩ : syracuseStep 708859 = 1063289) B1063289
theorem B1364527 : Blo 706319 1364527 := bstep (se 1 (by rfl) ⟨1023395, by rfl⟩ : syracuseStep 1364527 = 2046791) B2046791
theorem B709287 : Blo 706319 709287 := bstep (se 1 (by rfl) ⟨531965, by rfl⟩ : syracuseStep 709287 = 1063931) B1063931
theorem B709723 : Blo 706319 709723 := bstep (se 1 (by rfl) ⟨532292, by rfl⟩ : syracuseStep 709723 = 1064585) B1064585
theorem B3593321 : Blo 706319 3593321 := bstep (se 2 (by rfl) ⟨1347495, by rfl⟩ : syracuseStep 3593321 = 2694991) B2694991
theorem B710079 : Blo 706319 710079 := bstep (se 1 (by rfl) ⟨532559, by rfl⟩ : syracuseStep 710079 = 1065119) B1065119
theorem B12080987 : Blo 706319 12080987 := bstep (se 1 (by rfl) ⟨9060740, by rfl⟩ : syracuseStep 12080987 = 18121481) B18121481
theorem B1595465 : Blo 706319 1595465 := bstep (se 2 (by rfl) ⟨598299, by rfl⟩ : syracuseStep 1595465 = 1196599) B1196599
theorem B2021449 : Blo 706319 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B5364467 : Blo 706319 5364467 := bstep (se 1 (by rfl) ⟨4023350, by rfl⟩ : syracuseStep 5364467 = 8046701) B8046701
theorem B4840481 : Blo 706319 4840481 := bstep (se 2 (by rfl) ⟨1815180, by rfl⟩ : syracuseStep 4840481 = 3630361) B3630361
theorem B1007159 : Blo 706319 1007159 := bstep (se 1 (by rfl) ⟨755369, by rfl⟩ : syracuseStep 1007159 = 1510739) B1510739
theorem B3235895 : Blo 706319 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B13459655 : Blo 706319 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B3399931 : Blo 706319 3399931 := bstep (se 1 (by rfl) ⟨2549948, by rfl⟩ : syracuseStep 3399931 = 5099897) B5099897
theorem B1598057 : Blo 706319 1598057 := bstep (se 2 (by rfl) ⟨599271, by rfl⟩ : syracuseStep 1598057 = 1198543) B1198543
theorem B4548413 : Blo 706319 4548413 := bstep (se 3 (by rfl) ⟨852827, by rfl⟩ : syracuseStep 4548413 = 1705655) B1705655
theorem B1534747 : Blo 706319 1534747 := bstep (se 1 (by rfl) ⟨1151060, by rfl⟩ : syracuseStep 1534747 = 2302121) B2302121
theorem B3828883 : Blo 706319 3828883 := bstep (se 1 (by rfl) ⟨2871662, by rfl⟩ : syracuseStep 3828883 = 5743325) B5743325
theorem B1273087 : Blo 706319 1273087 := bstep (se 1 (by rfl) ⟨954815, by rfl⟩ : syracuseStep 1273087 = 1909631) B1909631
theorem B2551679 : Blo 706319 2551679 := bstep (se 1 (by rfl) ⟨1913759, by rfl⟩ : syracuseStep 2551679 = 3827519) B3827519
theorem B1699775 : Blo 706319 1699775 := bstep (se 1 (by rfl) ⟨1274831, by rfl⟩ : syracuseStep 1699775 = 2549663) B2549663
theorem B5370299 : Blo 706319 5370299 := bstep (se 1 (by rfl) ⟨4027724, by rfl⟩ : syracuseStep 5370299 = 8055449) B8055449
theorem B2389121 : Blo 706319 2389121 := bstep (se 2 (by rfl) ⟨895920, by rfl⟩ : syracuseStep 2389121 = 1791841) B1791841
theorem B1439407 : Blo 706319 1439407 := bstep (se 1 (by rfl) ⟨1079555, by rfl⟩ : syracuseStep 1439407 = 2159111) B2159111
theorem B2390687 : Blo 706319 2390687 := bstep (se 1 (by rfl) ⟨1793015, by rfl⟩ : syracuseStep 2390687 = 3586031) B3586031
theorem B1342271 : Blo 706319 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B2391065 : Blo 706319 2391065 := bstep (se 2 (by rfl) ⟨896649, by rfl⟩ : syracuseStep 2391065 = 1793299) B1793299
theorem B1342651 : Blo 706319 1342651 := bstep (se 1 (by rfl) ⟨1006988, by rfl⟩ : syracuseStep 1342651 = 2013977) B2013977
theorem B1342811 : Blo 706319 1342811 := bstep (se 1 (by rfl) ⟨1007108, by rfl⟩ : syracuseStep 1342811 = 2014217) B2014217
theorem B67371047 : Blo 706319 67371047 := bstep (se 1 (by rfl) ⟨50528285, by rfl⟩ : syracuseStep 67371047 = 101056571) B101056571
theorem B2589479 : Blo 706319 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B5375159 : Blo 706319 5375159 := bstep (se 1 (by rfl) ⟨4031369, by rfl⟩ : syracuseStep 5375159 = 8062739) B8062739
theorem B6817085 : Blo 706319 6817085 := bstep (se 3 (by rfl) ⟨1278203, by rfl⟩ : syracuseStep 6817085 = 2556407) B2556407
theorem B29132207 : Blo 706319 29132207 := bstep (se 1 (by rfl) ⟨21849155, by rfl⟩ : syracuseStep 29132207 = 43698311) B43698311
theorem B2558585 : Blo 706319 2558585 := bstep (se 2 (by rfl) ⟨959469, by rfl⟩ : syracuseStep 2558585 = 1918939) B1918939
theorem B16321475 : Blo 706319 16321475 := bstep (se 1 (by rfl) ⟨12241106, by rfl⟩ : syracuseStep 16321475 = 24482213) B24482213
theorem B2690131 : Blo 706319 2690131 := bstep (se 1 (by rfl) ⟨2017598, by rfl⟩ : syracuseStep 2690131 = 4035197) B4035197
theorem B1576199 : Blo 706319 1576199 := bstep (se 1 (by rfl) ⟨1182149, by rfl⟩ : syracuseStep 1576199 = 2364299) B2364299
theorem B2395547 : Blo 706319 2395547 := bstep (se 1 (by rfl) ⟨1796660, by rfl⟩ : syracuseStep 2395547 = 3593321) B3593321
theorem B3411659 : Blo 706319 3411659 := bstep (se 1 (by rfl) ⟨2558744, by rfl⟩ : syracuseStep 3411659 = 5117489) B5117489
theorem B3018505 : Blo 706319 3018505 := bstep (se 2 (by rfl) ⟨1131939, by rfl⟩ : syracuseStep 3018505 = 2263879) B2263879
theorem B3576311 : Blo 706319 3576311 := bstep (se 1 (by rfl) ⟨2682233, by rfl⟩ : syracuseStep 3576311 = 5364467) B5364467
theorem B58167881 : Blo 706319 58167881 := bstep (se 2 (by rfl) ⟨21812955, by rfl⟩ : syracuseStep 58167881 = 43625911) B43625911
theorem B12129101 : Blo 706319 12129101 := bstep (se 3 (by rfl) ⟨2274206, by rfl⟩ : syracuseStep 12129101 = 4548413) B4548413
theorem B2692379 : Blo 706319 2692379 := bstep (se 1 (by rfl) ⟨2019284, by rfl⟩ : syracuseStep 2692379 = 4038569) B4038569
theorem B3579389 : Blo 706319 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B3022879 : Blo 706319 3022879 := bstep (se 1 (by rfl) ⟨2267159, by rfl⟩ : syracuseStep 3022879 = 4534319) B4534319
theorem B2695265 : Blo 706319 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B3580199 : Blo 706319 3580199 := bstep (se 1 (by rfl) ⟨2685149, by rfl⟩ : syracuseStep 3580199 = 5370299) B5370299
theorem B796063 : Blo 706319 796063 := bstep (se 1 (by rfl) ⟨597047, by rfl⟩ : syracuseStep 796063 = 1194095) B1194095
theorem B6825545 : Blo 706319 6825545 := bstep (se 2 (by rfl) ⟨2559579, by rfl⟩ : syracuseStep 6825545 = 5119159) B5119159
theorem B34547309 : Blo 706319 34547309 := bstep (se 3 (by rfl) ⟨6477620, by rfl⟩ : syracuseStep 34547309 = 12955241) B12955241
theorem B895207 : Blo 706319 895207 := bstep (se 1 (by rfl) ⟨671405, by rfl⟩ : syracuseStep 895207 = 1342811) B1342811
theorem B1059593 : Blo 706319 1059593 := bstep (se 2 (by rfl) ⟨397347, by rfl⟩ : syracuseStep 1059593 = 794695) B794695
theorem B797503 : Blo 706319 797503 := bstep (se 1 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 797503 = 1196255) B1196255
theorem B4533241 : Blo 706319 4533241 := bstep (se 2 (by rfl) ⟨1699965, by rfl⟩ : syracuseStep 4533241 = 3399931) B3399931
theorem B35892413 : Blo 706319 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B797935 : Blo 706319 797935 := bstep (se 1 (by rfl) ⟨598451, by rfl⟩ : syracuseStep 797935 = 1196903) B1196903
theorem B1060511 : Blo 706319 1060511 := bstep (se 1 (by rfl) ⟨795383, by rfl⟩ : syracuseStep 1060511 = 1590767) B1590767
theorem B4534471 : Blo 706319 4534471 := bstep (se 1 (by rfl) ⟨3400853, by rfl⟩ : syracuseStep 4534471 = 6801707) B6801707
theorem B1061099 : Blo 706319 1061099 := bstep (se 1 (by rfl) ⟨795824, by rfl⟩ : syracuseStep 1061099 = 1591649) B1591649
theorem B897895 : Blo 706319 897895 := bstep (se 1 (by rfl) ⟨673421, by rfl⟩ : syracuseStep 897895 = 1346843) B1346843
theorem B6894821 : Blo 706319 6894821 := bstep (se 4 (by rfl) ⟨646389, by rfl⟩ : syracuseStep 6894821 = 1292779) B1292779
theorem B12072239 : Blo 706319 12072239 := bstep (se 1 (by rfl) ⟨9054179, by rfl⟩ : syracuseStep 12072239 = 18108359) B18108359
theorem B2012519 : Blo 706319 2012519 := bstep (se 1 (by rfl) ⟨1509389, by rfl⟩ : syracuseStep 2012519 = 3018779) B3018779
theorem B3028585 : Blo 706319 3028585 := bstep (se 2 (by rfl) ⟨1135719, by rfl⟩ : syracuseStep 3028585 = 2271439) B2271439
theorem B13613255 : Blo 706319 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B3029201 : Blo 706319 3029201 := bstep (se 2 (by rfl) ⟨1135950, by rfl⟩ : syracuseStep 3029201 = 2271901) B2271901
theorem B2046329 : Blo 706319 2046329 := bstep (se 2 (by rfl) ⟨767373, by rfl⟩ : syracuseStep 2046329 = 1534747) B1534747
theorem B1063643 : Blo 706319 1063643 := bstep (se 1 (by rfl) ⟨797732, by rfl⟩ : syracuseStep 1063643 = 1595465) B1595465
theorem B29408507 : Blo 706319 29408507 := bstep (se 1 (by rfl) ⟨22056380, by rfl⟩ : syracuseStep 29408507 = 44112761) B44112761
theorem B3226987 : Blo 706319 3226987 := bstep (se 1 (by rfl) ⟨2420240, by rfl⟩ : syracuseStep 3226987 = 4840481) B4840481
theorem B3588137 : Blo 706319 3588137 := bstep (se 2 (by rfl) ⟨1345551, by rfl⟩ : syracuseStep 3588137 = 2691103) B2691103
theorem B1065371 : Blo 706319 1065371 := bstep (se 1 (by rfl) ⟨799028, by rfl⟩ : syracuseStep 1065371 = 1598057) B1598057
theorem B1819369 : Blo 706319 1819369 := bstep (se 2 (by rfl) ⟨682263, by rfl⟩ : syracuseStep 1819369 = 1364527) B1364527
theorem B14534255 : Blo 706319 14534255 := bstep (se 1 (by rfl) ⟨10900691, by rfl⟩ : syracuseStep 14534255 = 21801383) B21801383
theorem B706623 : Blo 706319 706623 := bstep (se 1 (by rfl) ⟨529967, by rfl⟩ : syracuseStep 706623 = 1059935) B1059935
theorem B4311215 : Blo 706319 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B1919209 : Blo 706319 1919209 := bstep (se 2 (by rfl) ⟨719703, by rfl⟩ : syracuseStep 1919209 = 1439407) B1439407
theorem B706887 : Blo 706319 706887 := bstep (se 1 (by rfl) ⟨530165, by rfl⟩ : syracuseStep 706887 = 1060331) B1060331
theorem B706919 : Blo 706319 706919 := bstep (se 1 (by rfl) ⟨530189, by rfl⟩ : syracuseStep 706919 = 1060379) B1060379
theorem B707183 : Blo 706319 707183 := bstep (se 1 (by rfl) ⟨530387, by rfl⟩ : syracuseStep 707183 = 1060775) B1060775
theorem B1133183 : Blo 706319 1133183 := bstep (se 1 (by rfl) ⟨849887, by rfl⟩ : syracuseStep 1133183 = 1699775) B1699775
theorem B707303 : Blo 706319 707303 := bstep (se 1 (by rfl) ⟨530477, by rfl⟩ : syracuseStep 707303 = 1060955) B1060955
theorem B707615 : Blo 706319 707615 := bstep (se 1 (by rfl) ⟨530711, by rfl⟩ : syracuseStep 707615 = 1061423) B1061423
theorem B707823 : Blo 706319 707823 := bstep (se 1 (by rfl) ⟨530867, by rfl⟩ : syracuseStep 707823 = 1061735) B1061735
theorem B707835 : Blo 706319 707835 := bstep (se 1 (by rfl) ⟨530876, by rfl⟩ : syracuseStep 707835 = 1061753) B1061753
theorem B1592747 : Blo 706319 1592747 := bstep (se 1 (by rfl) ⟨1194560, by rfl⟩ : syracuseStep 1592747 = 2389121) B2389121
theorem B708379 : Blo 706319 708379 := bstep (se 1 (by rfl) ⟨531284, by rfl⟩ : syracuseStep 708379 = 1062569) B1062569
theorem B708443 : Blo 706319 708443 := bstep (se 1 (by rfl) ⟨531332, by rfl⟩ : syracuseStep 708443 = 1062665) B1062665
theorem B9064385 : Blo 706319 9064385 := bstep (se 2 (by rfl) ⟨3399144, by rfl⟩ : syracuseStep 9064385 = 6798289) B6798289
theorem B708639 : Blo 706319 708639 := bstep (se 1 (by rfl) ⟨531479, by rfl⟩ : syracuseStep 708639 = 1062959) B1062959
theorem B708775 : Blo 706319 708775 := bstep (se 1 (by rfl) ⟨531581, by rfl⟩ : syracuseStep 708775 = 1063163) B1063163
theorem B1790201 : Blo 706319 1790201 := bstep (se 2 (by rfl) ⟨671325, by rfl⟩ : syracuseStep 1790201 = 1342651) B1342651
theorem B708935 : Blo 706319 708935 := bstep (se 1 (by rfl) ⟨531701, by rfl⟩ : syracuseStep 708935 = 1063403) B1063403
theorem B1593791 : Blo 706319 1593791 := bstep (se 1 (by rfl) ⟨1195343, by rfl⟩ : syracuseStep 1593791 = 2390687) B2390687
theorem B709211 : Blo 706319 709211 := bstep (se 1 (by rfl) ⟨531908, by rfl⟩ : syracuseStep 709211 = 1063817) B1063817
theorem B1594043 : Blo 706319 1594043 := bstep (se 1 (by rfl) ⟨1195532, by rfl⟩ : syracuseStep 1594043 = 2391065) B2391065
theorem B709327 : Blo 706319 709327 := bstep (se 1 (by rfl) ⟨531995, by rfl⟩ : syracuseStep 709327 = 1063991) B1063991
theorem B709375 : Blo 706319 709375 := bstep (se 1 (by rfl) ⟨532031, by rfl⟩ : syracuseStep 709375 = 1064063) B1064063
theorem B709567 : Blo 706319 709567 := bstep (se 1 (by rfl) ⟨532175, by rfl⟩ : syracuseStep 709567 = 1064351) B1064351
theorem B709823 : Blo 706319 709823 := bstep (se 1 (by rfl) ⟨532367, by rfl⟩ : syracuseStep 709823 = 1064735) B1064735
theorem B710095 : Blo 706319 710095 := bstep (se 1 (by rfl) ⟨532571, by rfl⟩ : syracuseStep 710095 = 1065143) B1065143
theorem B710143 : Blo 706319 710143 := bstep (se 1 (by rfl) ⟨532607, by rfl⟩ : syracuseStep 710143 = 1065215) B1065215
theorem B1595519 : Blo 706319 1595519 := bstep (se 1 (by rfl) ⟨1196639, by rfl⟩ : syracuseStep 1595519 = 2393279) B2393279
theorem B1596383 : Blo 706319 1596383 := bstep (se 1 (by rfl) ⟨1197287, by rfl⟩ : syracuseStep 1596383 = 2394575) B2394575
theorem B1596923 : Blo 706319 1596923 := bstep (se 1 (by rfl) ⟨1197692, by rfl⟩ : syracuseStep 1596923 = 2395385) B2395385
theorem B1598183 : Blo 706319 1598183 := bstep (se 1 (by rfl) ⟨1198637, by rfl⟩ : syracuseStep 1598183 = 2397275) B2397275
theorem B1795031 : Blo 706319 1795031 := bstep (se 1 (by rfl) ⟨1346273, by rfl⟩ : syracuseStep 1795031 = 2692547) B2692547
theorem B4547593 : Blo 706319 4547593 := bstep (se 2 (by rfl) ⟨1705347, by rfl⟩ : syracuseStep 4547593 = 3410695) B3410695
theorem B8053991 : Blo 706319 8053991 := bstep (se 1 (by rfl) ⟨6040493, by rfl⟩ : syracuseStep 8053991 = 12080987) B12080987
theorem B1795567 : Blo 706319 1795567 := bstep (se 1 (by rfl) ⟨1346675, by rfl⟩ : syracuseStep 1795567 = 2693351) B2693351
theorem B5105177 : Blo 706319 5105177 := bstep (se 2 (by rfl) ⟨1914441, by rfl⟩ : syracuseStep 5105177 = 3828883) B3828883
theorem B1009255 : Blo 706319 1009255 := bstep (se 1 (by rfl) ⟨756941, by rfl⟩ : syracuseStep 1009255 = 1513883) B1513883
theorem B1697449 : Blo 706319 1697449 := bstep (se 2 (by rfl) ⟨636543, by rfl⟩ : syracuseStep 1697449 = 1273087) B1273087
theorem B6055667 : Blo 706319 6055667 := bstep (se 1 (by rfl) ⟨4541750, by rfl⟩ : syracuseStep 6055667 = 9083501) B9083501
theorem B1796327 : Blo 706319 1796327 := bstep (se 1 (by rfl) ⟨1347245, by rfl⟩ : syracuseStep 1796327 = 2694491) B2694491
theorem B2157263 : Blo 706319 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B2387069 : Blo 706319 2387069 := bstep (se 3 (by rfl) ⟨447575, by rfl⟩ : syracuseStep 2387069 = 895151) B895151
theorem B5729575 : Blo 706319 5729575 := bstep (se 1 (by rfl) ⟨4297181, by rfl⟩ : syracuseStep 5729575 = 8594363) B8594363
theorem B1701119 : Blo 706319 1701119 := bstep (se 1 (by rfl) ⟨1275839, by rfl⟩ : syracuseStep 1701119 = 2551679) B2551679
theorem B1275257 : Blo 706319 1275257 := bstep (se 2 (by rfl) ⟨478221, by rfl⟩ : syracuseStep 1275257 = 956443) B956443
theorem B2423009 : Blo 706319 2423009 := bstep (se 2 (by rfl) ⟨908628, by rfl⟩ : syracuseStep 2423009 = 1817257) B1817257
theorem B1210607 : Blo 706319 1210607 := bstep (se 1 (by rfl) ⟨907955, by rfl⟩ : syracuseStep 1210607 = 1815911) B1815911
theorem B88177085 : Blo 706319 88177085 := bstep (se 3 (by rfl) ⟨16533203, by rfl⟩ : syracuseStep 88177085 = 33066407) B33066407
theorem B2390795 : Blo 706319 2390795 := bstep (se 1 (by rfl) ⟨1793096, by rfl⟩ : syracuseStep 2390795 = 3586193) B3586193
theorem B2685757 : Blo 706319 2685757 := bstep (se 3 (by rfl) ⟨503579, by rfl⟩ : syracuseStep 2685757 = 1007159) B1007159
theorem B2392091 : Blo 706319 2392091 := bstep (se 1 (by rfl) ⟨1794068, by rfl⟩ : syracuseStep 2392091 = 3588137) B3588137
theorem B4030505 : Blo 706319 4030505 := bstep (se 2 (by rfl) ⟨1511439, by rfl⟩ : syracuseStep 4030505 = 3022879) B3022879
theorem B2425825 : Blo 706319 2425825 := bstep (se 2 (by rfl) ⟨909684, by rfl⟩ : syracuseStep 2425825 = 1819369) B1819369
theorem B6063457 : Blo 706319 6063457 := bstep (se 2 (by rfl) ⟨2273796, by rfl⟩ : syracuseStep 6063457 = 4547593) B4547593
theorem B755455 : Blo 706319 755455 := bstep (se 1 (by rfl) ⟨566591, by rfl⟩ : syracuseStep 755455 = 1133183) B1133183
theorem B10880983 : Blo 706319 10880983 := bstep (se 1 (by rfl) ⟨8160737, by rfl⟩ : syracuseStep 10880983 = 16321475) B16321475
theorem B2394089 : Blo 706319 2394089 := bstep (se 2 (by rfl) ⟨897783, by rfl⟩ : syracuseStep 2394089 = 1795567) B1795567
theorem B1345673 : Blo 706319 1345673 := bstep (se 2 (by rfl) ⟨504627, by rfl⟩ : syracuseStep 1345673 = 1009255) B1009255
theorem B2263265 : Blo 706319 2263265 := bstep (se 2 (by rfl) ⟨848724, by rfl⟩ : syracuseStep 2263265 = 1697449) B1697449
theorem B12913141 : Blo 706319 12913141 := bstep (se 5 (by rfl) ⟨605303, by rfl⟩ : syracuseStep 12913141 = 1210607) B1210607
theorem B2558945 : Blo 706319 2558945 := bstep (se 2 (by rfl) ⟨959604, by rfl⟩ : syracuseStep 2558945 = 1919209) B1919209
theorem B7639433 : Blo 706319 7639433 := bstep (se 2 (by rfl) ⟨2864787, by rfl⟩ : syracuseStep 7639433 = 5729575) B5729575
theorem B4037111 : Blo 706319 4037111 := bstep (se 1 (by rfl) ⟨3027833, by rfl⟩ : syracuseStep 4037111 = 6055667) B6055667
theorem B6822893 : Blo 706319 6822893 := bstep (se 3 (by rfl) ⟨1279292, by rfl⟩ : syracuseStep 6822893 = 2558585) B2558585
theorem B23928275 : Blo 706319 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B4038113 : Blo 706319 4038113 := bstep (se 2 (by rfl) ⟨1514292, by rfl⟩ : syracuseStep 4038113 = 3028585) B3028585
theorem B4203197 : Blo 706319 4203197 := bstep (se 3 (by rfl) ⟨788099, by rfl⟩ : syracuseStep 4203197 = 1576199) B1576199
theorem B4596547 : Blo 706319 4596547 := bstep (se 1 (by rfl) ⟨3447410, by rfl⟩ : syracuseStep 4596547 = 6894821) B6894821
theorem B3581009 : Blo 706319 3581009 := bstep (se 2 (by rfl) ⟨1342878, by rfl⟩ : syracuseStep 3581009 = 2685757) B2685757
theorem B1615339 : Blo 706319 1615339 := bstep (se 1 (by rfl) ⟨1211504, by rfl⟩ : syracuseStep 1615339 = 2423009) B2423009
theorem B4302649 : Blo 706319 4302649 := bstep (se 2 (by rfl) ⟨1613493, by rfl⟩ : syracuseStep 4302649 = 3226987) B3226987
theorem B19605671 : Blo 706319 19605671 := bstep (se 1 (by rfl) ⟨14704253, by rfl⟩ : syracuseStep 19605671 = 29408507) B29408507
theorem B3583439 : Blo 706319 3583439 := bstep (se 1 (by rfl) ⟨2687579, by rfl⟩ : syracuseStep 3583439 = 5375159) B5375159
theorem B1061417 : Blo 706319 1061417 := bstep (se 2 (by rfl) ⟨398031, by rfl⟩ : syracuseStep 1061417 = 796063) B796063
theorem B1061831 : Blo 706319 1061831 := bstep (se 1 (by rfl) ⟨796373, by rfl⟩ : syracuseStep 1061831 = 1592747) B1592747
theorem B2274439 : Blo 706319 2274439 := bstep (se 1 (by rfl) ⟨1705829, by rfl⟩ : syracuseStep 2274439 = 3411659) B3411659
theorem B6042923 : Blo 706319 6042923 := bstep (se 1 (by rfl) ⟨4532192, by rfl⟩ : syracuseStep 6042923 = 9064385) B9064385
theorem B1193467 : Blo 706319 1193467 := bstep (se 1 (by rfl) ⟨895100, by rfl⟩ : syracuseStep 1193467 = 1790201) B1790201
theorem B1062527 : Blo 706319 1062527 := bstep (se 1 (by rfl) ⟨796895, by rfl⟩ : syracuseStep 1062527 = 1593791) B1593791
theorem B1193609 : Blo 706319 1193609 := bstep (se 2 (by rfl) ⟨447603, by rfl⟩ : syracuseStep 1193609 = 895207) B895207
theorem B38778587 : Blo 706319 38778587 := bstep (se 1 (by rfl) ⟨29083940, by rfl⟩ : syracuseStep 38778587 = 58167881) B58167881
theorem B1062695 : Blo 706319 1062695 := bstep (se 1 (by rfl) ⟨797021, by rfl⟩ : syracuseStep 1062695 = 1594043) B1594043
theorem B4536317 : Blo 706319 4536317 := bstep (se 3 (by rfl) ⟨850559, by rfl⟩ : syracuseStep 4536317 = 1701119) B1701119
theorem B1063337 : Blo 706319 1063337 := bstep (se 2 (by rfl) ⟨398751, by rfl⟩ : syracuseStep 1063337 = 797503) B797503
theorem B6044321 : Blo 706319 6044321 := bstep (se 2 (by rfl) ⟨2266620, by rfl⟩ : syracuseStep 6044321 = 4533241) B4533241
theorem B1063679 : Blo 706319 1063679 := bstep (se 1 (by rfl) ⟨797759, by rfl⟩ : syracuseStep 1063679 = 1595519) B1595519
theorem B3586841 : Blo 706319 3586841 := bstep (se 2 (by rfl) ⟨1345065, by rfl⟩ : syracuseStep 3586841 = 2690131) B2690131
theorem B1063913 : Blo 706319 1063913 := bstep (se 2 (by rfl) ⟨398967, by rfl⟩ : syracuseStep 1063913 = 797935) B797935
theorem B1064255 : Blo 706319 1064255 := bstep (se 1 (by rfl) ⟨798191, by rfl⟩ : syracuseStep 1064255 = 1596383) B1596383
theorem B1064615 : Blo 706319 1064615 := bstep (se 1 (by rfl) ⟨798461, by rfl⟩ : syracuseStep 1064615 = 1596923) B1596923
theorem B6045961 : Blo 706319 6045961 := bstep (se 2 (by rfl) ⟨2267235, by rfl⟩ : syracuseStep 6045961 = 4534471) B4534471
theorem B1065455 : Blo 706319 1065455 := bstep (se 1 (by rfl) ⟨799091, by rfl⟩ : syracuseStep 1065455 = 1598183) B1598183
theorem B1196687 : Blo 706319 1196687 := bstep (se 1 (by rfl) ⟨897515, by rfl⟩ : syracuseStep 1196687 = 1795031) B1795031
theorem B1197193 : Blo 706319 1197193 := bstep (se 2 (by rfl) ⟨448947, by rfl⟩ : syracuseStep 1197193 = 897895) B897895
theorem B1197551 : Blo 706319 1197551 := bstep (se 1 (by rfl) ⟨898163, by rfl⟩ : syracuseStep 1197551 = 1796327) B1796327
theorem B706395 : Blo 706319 706395 := bstep (se 1 (by rfl) ⟨529796, by rfl⟩ : syracuseStep 706395 = 1059593) B1059593
theorem B1591379 : Blo 706319 1591379 := bstep (se 1 (by rfl) ⟨1193534, by rfl⟩ : syracuseStep 1591379 = 2387069) B2387069
theorem B707007 : Blo 706319 707007 := bstep (se 1 (by rfl) ⟨530255, by rfl⟩ : syracuseStep 707007 = 1060511) B1060511
theorem B707399 : Blo 706319 707399 := bstep (se 1 (by rfl) ⟨530549, by rfl⟩ : syracuseStep 707399 = 1061099) B1061099
theorem B8048159 : Blo 706319 8048159 := bstep (se 1 (by rfl) ⟨6036119, by rfl⟩ : syracuseStep 8048159 = 12072239) B12072239
theorem B2019467 : Blo 706319 2019467 := bstep (se 1 (by rfl) ⟨1514600, by rfl⟩ : syracuseStep 2019467 = 3029201) B3029201
theorem B1364219 : Blo 706319 1364219 := bstep (se 1 (by rfl) ⟨1023164, by rfl⟩ : syracuseStep 1364219 = 2046329) B2046329
theorem B709095 : Blo 706319 709095 := bstep (se 1 (by rfl) ⟨531821, by rfl⟩ : syracuseStep 709095 = 1063643) B1063643
theorem B1593863 : Blo 706319 1593863 := bstep (se 1 (by rfl) ⟨1195397, by rfl⟩ : syracuseStep 1593863 = 2390795) B2390795
theorem B44914031 : Blo 706319 44914031 := bstep (se 1 (by rfl) ⟨33685523, by rfl⟩ : syracuseStep 44914031 = 67371047) B67371047
theorem B710247 : Blo 706319 710247 := bstep (se 1 (by rfl) ⟨532685, by rfl⟩ : syracuseStep 710247 = 1065371) B1065371
theorem B1726319 : Blo 706319 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B4544723 : Blo 706319 4544723 := bstep (se 1 (by rfl) ⟨3408542, by rfl⟩ : syracuseStep 4544723 = 6817085) B6817085
theorem B19421471 : Blo 706319 19421471 := bstep (se 1 (by rfl) ⟨14566103, by rfl⟩ : syracuseStep 19421471 = 29132207) B29132207
theorem B2874143 : Blo 706319 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B1597031 : Blo 706319 1597031 := bstep (se 1 (by rfl) ⟨1197773, by rfl⟩ : syracuseStep 1597031 = 2395547) B2395547
theorem B2384207 : Blo 706319 2384207 := bstep (se 1 (by rfl) ⟨1788155, by rfl⟩ : syracuseStep 2384207 = 3576311) B3576311
theorem B8086067 : Blo 706319 8086067 := bstep (se 1 (by rfl) ⟨6064550, by rfl⟩ : syracuseStep 8086067 = 12129101) B12129101
theorem B1794919 : Blo 706319 1794919 := bstep (se 1 (by rfl) ⟨1346189, by rfl⟩ : syracuseStep 1794919 = 2692379) B2692379
theorem B38758013 : Blo 706319 38758013 := bstep (se 3 (by rfl) ⟨7267127, by rfl⟩ : syracuseStep 38758013 = 14534255) B14534255
theorem B2386259 : Blo 706319 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B4024673 : Blo 706319 4024673 := bstep (se 2 (by rfl) ⟨1509252, by rfl⟩ : syracuseStep 4024673 = 3018505) B3018505
theorem B1796843 : Blo 706319 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B2386799 : Blo 706319 2386799 := bstep (se 1 (by rfl) ⟨1790099, by rfl⟩ : syracuseStep 2386799 = 3580199) B3580199
theorem B5369327 : Blo 706319 5369327 := bstep (se 1 (by rfl) ⟨4026995, by rfl⟩ : syracuseStep 5369327 = 8053991) B8053991
theorem B3403451 : Blo 706319 3403451 := bstep (se 1 (by rfl) ⟨2552588, by rfl⟩ : syracuseStep 3403451 = 5105177) B5105177
theorem B4550363 : Blo 706319 4550363 := bstep (se 1 (by rfl) ⟨3412772, by rfl⟩ : syracuseStep 4550363 = 6825545) B6825545
theorem B23031539 : Blo 706319 23031539 := bstep (se 1 (by rfl) ⟨17273654, by rfl⟩ : syracuseStep 23031539 = 34547309) B34547309
theorem B1438175 : Blo 706319 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B1341679 : Blo 706319 1341679 := bstep (se 1 (by rfl) ⟨1006259, by rfl⟩ : syracuseStep 1341679 = 2012519) B2012519
theorem B850171 : Blo 706319 850171 := bstep (se 1 (by rfl) ⟨637628, by rfl⟩ : syracuseStep 850171 = 1275257) B1275257
theorem B9075503 : Blo 706319 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B58784723 : Blo 706319 58784723 := bstep (se 1 (by rfl) ⟨44088542, by rfl⟩ : syracuseStep 58784723 = 88177085) B88177085
theorem B2687003 : Blo 706319 2687003 := bstep (se 1 (by rfl) ⟨2015252, by rfl⟩ : syracuseStep 2687003 = 4030505) B4030505
theorem B8061281 : Blo 706319 8061281 := bstep (se 2 (by rfl) ⟨3022980, by rfl⟩ : syracuseStep 8061281 = 6045961) B6045961
theorem B6128729 : Blo 706319 6128729 := bstep (se 2 (by rfl) ⟨2298273, by rfl⟩ : syracuseStep 6128729 = 4596547) B4596547
theorem B2393225 : Blo 706319 2393225 := bstep (se 2 (by rfl) ⟨897459, by rfl⟩ : syracuseStep 2393225 = 1794919) B1794919
theorem B3835133 : Blo 706319 3835133 := bstep (se 3 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 3835133 = 1438175) B1438175
theorem B1508843 : Blo 706319 1508843 := bstep (se 1 (by rfl) ⟨1131632, by rfl⟩ : syracuseStep 1508843 = 2263265) B2263265
theorem B1705963 : Blo 706319 1705963 := bstep (se 1 (by rfl) ⟨1279472, by rfl⟩ : syracuseStep 1705963 = 2558945) B2558945
theorem B1346311 : Blo 706319 1346311 := bstep (se 1 (by rfl) ⟨1009733, by rfl⟩ : syracuseStep 1346311 = 2019467) B2019467
theorem B2691407 : Blo 706319 2691407 := bstep (se 1 (by rfl) ⟨2018555, by rfl⟩ : syracuseStep 2691407 = 4037111) B4037111
theorem B2692075 : Blo 706319 2692075 := bstep (se 1 (by rfl) ⟨2019056, by rfl⟩ : syracuseStep 2692075 = 4038113) B4038113
theorem B3579551 : Blo 706319 3579551 := bstep (se 1 (by rfl) ⟨2684663, by rfl⟩ : syracuseStep 3579551 = 5369327) B5369327
theorem B2268967 : Blo 706319 2268967 := bstep (se 1 (by rfl) ⟨1701725, by rfl⟩ : syracuseStep 2268967 = 3403451) B3403451
theorem B795739 : Blo 706319 795739 := bstep (se 1 (by rfl) ⟨596804, by rfl⟩ : syracuseStep 795739 = 1193609) B1193609
theorem B3024211 : Blo 706319 3024211 := bstep (se 1 (by rfl) ⟨2268158, by rfl⟩ : syracuseStep 3024211 = 4536317) B4536317
theorem B22947461 : Blo 706319 22947461 := bstep (se 4 (by rfl) ⟨2151324, by rfl⟩ : syracuseStep 22947461 = 4302649) B4302649
theorem B797791 : Blo 706319 797791 := bstep (se 1 (by rfl) ⟨598343, by rfl⟩ : syracuseStep 797791 = 1196687) B1196687
theorem B798367 : Blo 706319 798367 := bstep (se 1 (by rfl) ⟨598775, by rfl⟩ : syracuseStep 798367 = 1197551) B1197551
theorem B1060919 : Blo 706319 1060919 := bstep (se 1 (by rfl) ⟨795689, by rfl⟩ : syracuseStep 1060919 = 1591379) B1591379
theorem B5092955 : Blo 706319 5092955 := bstep (se 1 (by rfl) ⟨3819716, by rfl⟩ : syracuseStep 5092955 = 7639433) B7639433
theorem B1062575 : Blo 706319 1062575 := bstep (se 1 (by rfl) ⟨796931, by rfl⟩ : syracuseStep 1062575 = 1593863) B1593863
theorem B17217521 : Blo 706319 17217521 := bstep (se 2 (by rfl) ⟨6456570, by rfl⟩ : syracuseStep 17217521 = 12913141) B12913141
theorem B3029815 : Blo 706319 3029815 := bstep (se 1 (by rfl) ⟨2272361, by rfl⟩ : syracuseStep 3029815 = 4544723) B4544723
theorem B1916095 : Blo 706319 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B4603517 : Blo 706319 4603517 := bstep (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) B1726319
theorem B1064687 : Blo 706319 1064687 := bstep (se 1 (by rfl) ⟨798515, by rfl⟩ : syracuseStep 1064687 = 1597031) B1597031
theorem B1589471 : Blo 706319 1589471 := bstep (se 1 (by rfl) ⟨1192103, by rfl⟩ : syracuseStep 1589471 = 2384207) B2384207
theorem B3588461 : Blo 706319 3588461 := bstep (se 3 (by rfl) ⟨672836, by rfl⟩ : syracuseStep 3588461 = 1345673) B1345673
theorem B5390711 : Blo 706319 5390711 := bstep (se 1 (by rfl) ⟨4043033, by rfl⟩ : syracuseStep 5390711 = 8086067) B8086067
theorem B2802131 : Blo 706319 2802131 := bstep (se 1 (by rfl) ⟨2101598, by rfl⟩ : syracuseStep 2802131 = 4203197) B4203197
theorem B51790589 : Blo 706319 51790589 := bstep (se 3 (by rfl) ⟨9710735, by rfl⟩ : syracuseStep 51790589 = 19421471) B19421471
theorem B25838675 : Blo 706319 25838675 := bstep (se 1 (by rfl) ⟨19379006, by rfl⟩ : syracuseStep 25838675 = 38758013) B38758013
theorem B3032585 : Blo 706319 3032585 := bstep (se 2 (by rfl) ⟨1137219, by rfl⟩ : syracuseStep 3032585 = 2274439) B2274439
theorem B1590839 : Blo 706319 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B1197895 : Blo 706319 1197895 := bstep (se 1 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 1197895 = 1796843) B1796843
theorem B1591199 : Blo 706319 1591199 := bstep (se 1 (by rfl) ⟨1193399, by rfl⟩ : syracuseStep 1591199 = 2386799) B2386799
theorem B1591289 : Blo 706319 1591289 := bstep (se 2 (by rfl) ⟨596733, by rfl⟩ : syracuseStep 1591289 = 1193467) B1193467
theorem B3033575 : Blo 706319 3033575 := bstep (se 1 (by rfl) ⟨2275181, by rfl⟩ : syracuseStep 3033575 = 4550363) B4550363
theorem B15354359 : Blo 706319 15354359 := bstep (se 1 (by rfl) ⟨11515769, by rfl⟩ : syracuseStep 15354359 = 23031539) B23031539
theorem B1788905 : Blo 706319 1788905 := bstep (se 2 (by rfl) ⟨670839, by rfl⟩ : syracuseStep 1788905 = 1341679) B1341679
theorem B1133561 : Blo 706319 1133561 := bstep (se 2 (by rfl) ⟨425085, by rfl⟩ : syracuseStep 1133561 = 850171) B850171
theorem B707611 : Blo 706319 707611 := bstep (se 1 (by rfl) ⟨530708, by rfl⟩ : syracuseStep 707611 = 1061417) B1061417
theorem B707887 : Blo 706319 707887 := bstep (se 1 (by rfl) ⟨530915, by rfl⟩ : syracuseStep 707887 = 1061831) B1061831
theorem B708351 : Blo 706319 708351 := bstep (se 1 (by rfl) ⟨531263, by rfl⟩ : syracuseStep 708351 = 1062527) B1062527
theorem B708463 : Blo 706319 708463 := bstep (se 1 (by rfl) ⟨531347, by rfl⟩ : syracuseStep 708463 = 1062695) B1062695
theorem B708891 : Blo 706319 708891 := bstep (se 1 (by rfl) ⟨531668, by rfl⟩ : syracuseStep 708891 = 1063337) B1063337
theorem B709119 : Blo 706319 709119 := bstep (se 1 (by rfl) ⟨531839, by rfl⟩ : syracuseStep 709119 = 1063679) B1063679
theorem B6050335 : Blo 706319 6050335 := bstep (se 1 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 6050335 = 9075503) B9075503
theorem B709275 : Blo 706319 709275 := bstep (se 1 (by rfl) ⟨531956, by rfl⟩ : syracuseStep 709275 = 1063913) B1063913
theorem B709503 : Blo 706319 709503 := bstep (se 1 (by rfl) ⟨532127, by rfl⟩ : syracuseStep 709503 = 1064255) B1064255
theorem B709743 : Blo 706319 709743 := bstep (se 1 (by rfl) ⟨532307, by rfl⟩ : syracuseStep 709743 = 1064615) B1064615
theorem B1594727 : Blo 706319 1594727 := bstep (se 1 (by rfl) ⟨1196045, by rfl⟩ : syracuseStep 1594727 = 2392091) B2392091
theorem B710303 : Blo 706319 710303 := bstep (se 1 (by rfl) ⟨532727, by rfl⟩ : syracuseStep 710303 = 1065455) B1065455
theorem B3234433 : Blo 706319 3234433 := bstep (se 2 (by rfl) ⟨1212912, by rfl⟩ : syracuseStep 3234433 = 2425825) B2425825
theorem B1596059 : Blo 706319 1596059 := bstep (se 1 (by rfl) ⟨1197044, by rfl⟩ : syracuseStep 1596059 = 2394089) B2394089
theorem B1596257 : Blo 706319 1596257 := bstep (se 2 (by rfl) ⟨598596, by rfl⟩ : syracuseStep 1596257 = 1197193) B1197193
theorem B8084609 : Blo 706319 8084609 := bstep (se 2 (by rfl) ⟨3031728, by rfl⟩ : syracuseStep 8084609 = 6063457) B6063457
theorem B2153785 : Blo 706319 2153785 := bstep (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) B1615339
theorem B1007273 : Blo 706319 1007273 := bstep (se 2 (by rfl) ⟨377727, by rfl⟩ : syracuseStep 1007273 = 755455) B755455
theorem B5365439 : Blo 706319 5365439 := bstep (se 1 (by rfl) ⟨4024079, by rfl⟩ : syracuseStep 5365439 = 8048159) B8048159
theorem B909479 : Blo 706319 909479 := bstep (se 1 (by rfl) ⟨682109, by rfl⟩ : syracuseStep 909479 = 1364219) B1364219
theorem B29942687 : Blo 706319 29942687 := bstep (se 1 (by rfl) ⟨22457015, by rfl⟩ : syracuseStep 29942687 = 44914031) B44914031
theorem B4548595 : Blo 706319 4548595 := bstep (se 1 (by rfl) ⟨3411446, by rfl⟩ : syracuseStep 4548595 = 6822893) B6822893
theorem B15952183 : Blo 706319 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B2387339 : Blo 706319 2387339 := bstep (se 1 (by rfl) ⟨1790504, by rfl⟩ : syracuseStep 2387339 = 3581009) B3581009
theorem B13070447 : Blo 706319 13070447 := bstep (se 1 (by rfl) ⟨9802835, by rfl⟩ : syracuseStep 13070447 = 19605671) B19605671
theorem B2683115 : Blo 706319 2683115 := bstep (se 1 (by rfl) ⟨2012336, by rfl⟩ : syracuseStep 2683115 = 4024673) B4024673
theorem B2388959 : Blo 706319 2388959 := bstep (se 1 (by rfl) ⟨1791719, by rfl⟩ : syracuseStep 2388959 = 3583439) B3583439
theorem B4028615 : Blo 706319 4028615 := bstep (se 1 (by rfl) ⟨3021461, by rfl⟩ : syracuseStep 4028615 = 6042923) B6042923
theorem B25852391 : Blo 706319 25852391 := bstep (se 1 (by rfl) ⟨19389293, by rfl⟩ : syracuseStep 25852391 = 38778587) B38778587
theorem B4029547 : Blo 706319 4029547 := bstep (se 1 (by rfl) ⟨3022160, by rfl⟩ : syracuseStep 4029547 = 6044321) B6044321
theorem B2391227 : Blo 706319 2391227 := bstep (se 1 (by rfl) ⟨1793420, by rfl⟩ : syracuseStep 2391227 = 3586841) B3586841
theorem B39189815 : Blo 706319 39189815 := bstep (se 1 (by rfl) ⟨29392361, by rfl⟩ : syracuseStep 39189815 = 58784723) B58784723
theorem B58031909 : Blo 706319 58031909 := bstep (se 4 (by rfl) ⟨5440491, by rfl⟩ : syracuseStep 58031909 = 10880983) B10880983
theorem B5374187 : Blo 706319 5374187 := bstep (se 1 (by rfl) ⟨4030640, by rfl⟩ : syracuseStep 5374187 = 8061281) B8061281
theorem B2392307 : Blo 706319 2392307 := bstep (se 1 (by rfl) ⟨1794230, by rfl⟩ : syracuseStep 2392307 = 3588461) B3588461
theorem B1868087 : Blo 706319 1868087 := bstep (se 1 (by rfl) ⟨1401065, by rfl⟩ : syracuseStep 1868087 = 2802131) B2802131
theorem B2425277 : Blo 706319 2425277 := bstep (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) B909479
theorem B2556755 : Blo 706319 2556755 := bstep (se 1 (by rfl) ⟨1917566, by rfl⟩ : syracuseStep 2556755 = 3835133) B3835133
theorem B4032281 : Blo 706319 4032281 := bstep (se 2 (by rfl) ⟨1512105, by rfl⟩ : syracuseStep 4032281 = 3024211) B3024211
theorem B6064793 : Blo 706319 6064793 := bstep (se 2 (by rfl) ⟨2274297, by rfl⟩ : syracuseStep 6064793 = 4548595) B4548595
theorem B3576959 : Blo 706319 3576959 := bstep (se 1 (by rfl) ⟨2682719, by rfl⟩ : syracuseStep 3576959 = 5365439) B5365439
theorem B8067113 : Blo 706319 8067113 := bstep (se 2 (by rfl) ⟨3025167, by rfl⟩ : syracuseStep 8067113 = 6050335) B6050335
theorem B3022829 : Blo 706319 3022829 := bstep (se 3 (by rfl) ⟨566780, by rfl⟩ : syracuseStep 3022829 = 1133561) B1133561
theorem B4039753 : Blo 706319 4039753 := bstep (se 2 (by rfl) ⟨1514907, by rfl⟩ : syracuseStep 4039753 = 3029815) B3029815
theorem B11478347 : Blo 706319 11478347 := bstep (se 1 (by rfl) ⟨8608760, by rfl⟩ : syracuseStep 11478347 = 17217521) B17217521
theorem B26126543 : Blo 706319 26126543 := bstep (se 1 (by rfl) ⟨19594907, by rfl⟩ : syracuseStep 26126543 = 39189815) B39189815
theorem B3025289 : Blo 706319 3025289 := bstep (se 2 (by rfl) ⟨1134483, by rfl⟩ : syracuseStep 3025289 = 2268967) B2268967
theorem B1059647 : Blo 706319 1059647 := bstep (se 1 (by rfl) ⟨794735, by rfl⟩ : syracuseStep 1059647 = 1589471) B1589471
theorem B1060559 : Blo 706319 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B1060799 : Blo 706319 1060799 := bstep (se 1 (by rfl) ⟨795599, by rfl⟩ : syracuseStep 1060799 = 1591199) B1591199
theorem B1060859 : Blo 706319 1060859 := bstep (se 1 (by rfl) ⟨795644, by rfl⟩ : syracuseStep 1060859 = 1591289) B1591289
theorem B1060985 : Blo 706319 1060985 := bstep (se 2 (by rfl) ⟨397869, by rfl⟩ : syracuseStep 1060985 = 795739) B795739
theorem B85078309 : Blo 706319 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B10236239 : Blo 706319 10236239 := bstep (se 1 (by rfl) ⟨7677179, by rfl⟩ : syracuseStep 10236239 = 15354359) B15354359
theorem B1192603 : Blo 706319 1192603 := bstep (se 1 (by rfl) ⟨894452, by rfl⟩ : syracuseStep 1192603 = 1788905) B1788905
theorem B2274617 : Blo 706319 2274617 := bstep (se 2 (by rfl) ⟨852981, by rfl⟩ : syracuseStep 2274617 = 1705963) B1705963
theorem B1063151 : Blo 706319 1063151 := bstep (se 1 (by rfl) ⟨797363, by rfl⟩ : syracuseStep 1063151 = 1594727) B1594727
theorem B1063721 : Blo 706319 1063721 := bstep (se 2 (by rfl) ⟨398895, by rfl⟩ : syracuseStep 1063721 = 797791) B797791
theorem B1064039 : Blo 706319 1064039 := bstep (se 1 (by rfl) ⟨798029, by rfl⟩ : syracuseStep 1064039 = 1596059) B1596059
theorem B1064171 : Blo 706319 1064171 := bstep (se 1 (by rfl) ⟨798128, by rfl⟩ : syracuseStep 1064171 = 1596257) B1596257
theorem B5389739 : Blo 706319 5389739 := bstep (se 1 (by rfl) ⟨4042304, by rfl⟩ : syracuseStep 5389739 = 8084609) B8084609
theorem B1064489 : Blo 706319 1064489 := bstep (se 2 (by rfl) ⟨399183, by rfl⟩ : syracuseStep 1064489 = 798367) B798367
theorem B3589433 : Blo 706319 3589433 := bstep (se 2 (by rfl) ⟨1346037, by rfl⟩ : syracuseStep 3589433 = 2692075) B2692075
theorem B1591559 : Blo 706319 1591559 := bstep (se 1 (by rfl) ⟨1193669, by rfl⟩ : syracuseStep 1591559 = 2387339) B2387339
theorem B707279 : Blo 706319 707279 := bstep (se 1 (by rfl) ⟨530459, by rfl⟩ : syracuseStep 707279 = 1060919) B1060919
theorem B1788743 : Blo 706319 1788743 := bstep (se 1 (by rfl) ⟨1341557, by rfl⟩ : syracuseStep 1788743 = 2683115) B2683115
theorem B1592639 : Blo 706319 1592639 := bstep (se 1 (by rfl) ⟨1194479, by rfl⟩ : syracuseStep 1592639 = 2388959) B2388959
theorem B4312577 : Blo 706319 4312577 := bstep (se 2 (by rfl) ⟨1617216, by rfl⟩ : syracuseStep 4312577 = 3234433) B3234433
theorem B3395303 : Blo 706319 3395303 := bstep (se 1 (by rfl) ⟨2546477, by rfl⟩ : syracuseStep 3395303 = 5092955) B5092955
theorem B708383 : Blo 706319 708383 := bstep (se 1 (by rfl) ⟨531287, by rfl⟩ : syracuseStep 708383 = 1062575) B1062575
theorem B2871713 : Blo 706319 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B1594151 : Blo 706319 1594151 := bstep (se 1 (by rfl) ⟨1195613, by rfl⟩ : syracuseStep 1594151 = 2391227) B2391227
theorem B3069011 : Blo 706319 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B709791 : Blo 706319 709791 := bstep (se 1 (by rfl) ⟨532343, by rfl⟩ : syracuseStep 709791 = 1064687) B1064687
theorem B38687939 : Blo 706319 38687939 := bstep (se 1 (by rfl) ⟨29015954, by rfl⟩ : syracuseStep 38687939 = 58031909) B58031909
theorem B1791335 : Blo 706319 1791335 := bstep (se 1 (by rfl) ⟨1343501, by rfl⟩ : syracuseStep 1791335 = 2687003) B2687003
theorem B3593807 : Blo 706319 3593807 := bstep (se 1 (by rfl) ⟨2695355, by rfl⟩ : syracuseStep 3593807 = 5390711) B5390711
theorem B34527059 : Blo 706319 34527059 := bstep (se 1 (by rfl) ⟨25895294, by rfl⟩ : syracuseStep 34527059 = 51790589) B51790589
theorem B17225783 : Blo 706319 17225783 := bstep (se 1 (by rfl) ⟨12919337, by rfl⟩ : syracuseStep 17225783 = 25838675) B25838675
theorem B4085819 : Blo 706319 4085819 := bstep (se 1 (by rfl) ⟨3064364, by rfl⟩ : syracuseStep 4085819 = 6128729) B6128729
theorem B1595483 : Blo 706319 1595483 := bstep (se 1 (by rfl) ⟨1196612, by rfl⟩ : syracuseStep 1595483 = 2393225) B2393225
theorem B1005895 : Blo 706319 1005895 := bstep (se 1 (by rfl) ⟨754421, by rfl⟩ : syracuseStep 1005895 = 1508843) B1508843
theorem B2021723 : Blo 706319 2021723 := bstep (se 1 (by rfl) ⟨1516292, by rfl⟩ : syracuseStep 2021723 = 3032585) B3032585
theorem B2022383 : Blo 706319 2022383 := bstep (se 1 (by rfl) ⟨1516787, by rfl⟩ : syracuseStep 2022383 = 3033575) B3033575
theorem B79847165 : Blo 706319 79847165 := bstep (se 3 (by rfl) ⟨14971343, by rfl⟩ : syracuseStep 79847165 = 29942687) B29942687
theorem B1597193 : Blo 706319 1597193 := bstep (se 2 (by rfl) ⟨598947, by rfl⟩ : syracuseStep 1597193 = 1197895) B1197895
theorem B1794271 : Blo 706319 1794271 := bstep (se 1 (by rfl) ⟨1345703, by rfl⟩ : syracuseStep 1794271 = 2691407) B2691407
theorem B1795081 : Blo 706319 1795081 := bstep (se 2 (by rfl) ⟨673155, by rfl⟩ : syracuseStep 1795081 = 1346311) B1346311
theorem B2386367 : Blo 706319 2386367 := bstep (se 1 (by rfl) ⟨1789775, by rfl⟩ : syracuseStep 2386367 = 3579551) B3579551
theorem B15298307 : Blo 706319 15298307 := bstep (se 1 (by rfl) ⟨11473730, by rfl⟩ : syracuseStep 15298307 = 22947461) B22947461
theorem B8713631 : Blo 706319 8713631 := bstep (se 1 (by rfl) ⟨6535223, by rfl⟩ : syracuseStep 8713631 = 13070447) B13070447
theorem B2685743 : Blo 706319 2685743 := bstep (se 1 (by rfl) ⟨2014307, by rfl⟩ : syracuseStep 2685743 = 4028615) B4028615
theorem B5372729 : Blo 706319 5372729 := bstep (se 2 (by rfl) ⟨2014773, by rfl⟩ : syracuseStep 5372729 = 4029547) B4029547
theorem B2554793 : Blo 706319 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B17234927 : Blo 706319 17234927 := bstep (se 1 (by rfl) ⟨12926195, by rfl⟩ : syracuseStep 17234927 = 25852391) B25852391
theorem B2686061 : Blo 706319 2686061 := bstep (se 3 (by rfl) ⟨503636, by rfl⟩ : syracuseStep 2686061 = 1007273) B1007273
theorem B2392361 : Blo 706319 2392361 := bstep (se 2 (by rfl) ⟨897135, by rfl⟩ : syracuseStep 2392361 = 1794271) B1794271
theorem B1704503 : Blo 706319 1704503 := bstep (se 1 (by rfl) ⟨1278377, by rfl⟩ : syracuseStep 1704503 = 2556755) B2556755
theorem B4981565 : Blo 706319 4981565 := bstep (se 3 (by rfl) ⟨934043, by rfl⟩ : syracuseStep 4981565 = 1868087) B1868087
theorem B2392955 : Blo 706319 2392955 := bstep (se 1 (by rfl) ⟨1794716, by rfl⟩ : syracuseStep 2392955 = 3589433) B3589433
theorem B2688187 : Blo 706319 2688187 := bstep (se 1 (by rfl) ⟨2016140, by rfl⟩ : syracuseStep 2688187 = 4032281) B4032281
theorem B2393441 : Blo 706319 2393441 := bstep (se 2 (by rfl) ⟨897540, by rfl⟩ : syracuseStep 2393441 = 1795081) B1795081
theorem B2263535 : Blo 706319 2263535 := bstep (se 1 (by rfl) ⟨1697651, by rfl⟩ : syracuseStep 2263535 = 3395303) B3395303
theorem B25791959 : Blo 706319 25791959 := bstep (se 1 (by rfl) ⟨19343969, by rfl⟩ : syracuseStep 25791959 = 38687939) B38687939
theorem B2395871 : Blo 706319 2395871 := bstep (se 1 (by rfl) ⟨1796903, by rfl⟩ : syracuseStep 2395871 = 3593807) B3593807
theorem B5378075 : Blo 706319 5378075 := bstep (se 1 (by rfl) ⟨4033556, by rfl⟩ : syracuseStep 5378075 = 8067113) B8067113
theorem B2723879 : Blo 706319 2723879 := bstep (se 1 (by rfl) ⟨2042909, by rfl⟩ : syracuseStep 2723879 = 4085819) B4085819
theorem B1347815 : Blo 706319 1347815 := bstep (se 1 (by rfl) ⟨1010861, by rfl⟩ : syracuseStep 1347815 = 2021723) B2021723
theorem B1348255 : Blo 706319 1348255 := bstep (se 1 (by rfl) ⟨1011191, by rfl⟩ : syracuseStep 1348255 = 2022383) B2022383
theorem B69670781 : Blo 706319 69670781 := bstep (se 3 (by rfl) ⟨13063271, by rfl⟩ : syracuseStep 69670781 = 26126543) B26126543
theorem B10198871 : Blo 706319 10198871 := bstep (se 1 (by rfl) ⟨7649153, by rfl⟩ : syracuseStep 10198871 = 15298307) B15298307
theorem B6824159 : Blo 706319 6824159 := bstep (se 1 (by rfl) ⟨5118119, by rfl⟩ : syracuseStep 6824159 = 10236239) B10236239
theorem B1516411 : Blo 706319 1516411 := bstep (se 1 (by rfl) ⟨1137308, by rfl⟩ : syracuseStep 1516411 = 2274617) B2274617
theorem B5809087 : Blo 706319 5809087 := bstep (se 1 (by rfl) ⟨4356815, by rfl⟩ : syracuseStep 5809087 = 8713631) B8713631
theorem B3581819 : Blo 706319 3581819 := bstep (se 1 (by rfl) ⟨2686364, by rfl⟩ : syracuseStep 3581819 = 5372729) B5372729
theorem B3582791 : Blo 706319 3582791 := bstep (se 1 (by rfl) ⟨2687093, by rfl⟩ : syracuseStep 3582791 = 5374187) B5374187
theorem B1616851 : Blo 706319 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B5386337 : Blo 706319 5386337 := bstep (se 2 (by rfl) ⟨2019876, by rfl⟩ : syracuseStep 5386337 = 4039753) B4039753
theorem B1061039 : Blo 706319 1061039 := bstep (se 1 (by rfl) ⟨795779, by rfl⟩ : syracuseStep 1061039 = 1591559) B1591559
theorem B4043195 : Blo 706319 4043195 := bstep (se 1 (by rfl) ⟨3032396, by rfl⟩ : syracuseStep 4043195 = 6064793) B6064793
theorem B1192495 : Blo 706319 1192495 := bstep (se 1 (by rfl) ⟨894371, by rfl⟩ : syracuseStep 1192495 = 1788743) B1788743
theorem B1061759 : Blo 706319 1061759 := bstep (se 1 (by rfl) ⟨796319, by rfl⟩ : syracuseStep 1061759 = 1592639) B1592639
theorem B1914475 : Blo 706319 1914475 := bstep (se 1 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 1914475 = 2871713) B2871713
theorem B1062767 : Blo 706319 1062767 := bstep (se 1 (by rfl) ⟨797075, by rfl⟩ : syracuseStep 1062767 = 1594151) B1594151
theorem B2046007 : Blo 706319 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B1194223 : Blo 706319 1194223 := bstep (se 1 (by rfl) ⟨895667, by rfl⟩ : syracuseStep 1194223 = 1791335) B1791335
theorem B23018039 : Blo 706319 23018039 := bstep (se 1 (by rfl) ⟨17263529, by rfl⟩ : syracuseStep 23018039 = 34527059) B34527059
theorem B11483855 : Blo 706319 11483855 := bstep (se 1 (by rfl) ⟨8612891, by rfl⟩ : syracuseStep 11483855 = 17225783) B17225783
theorem B1063655 : Blo 706319 1063655 := bstep (se 1 (by rfl) ⟨797741, by rfl⟩ : syracuseStep 1063655 = 1595483) B1595483
theorem B1064795 : Blo 706319 1064795 := bstep (se 1 (by rfl) ⟨798596, by rfl⟩ : syracuseStep 1064795 = 1597193) B1597193
theorem B2015219 : Blo 706319 2015219 := bstep (se 1 (by rfl) ⟨1511414, by rfl⟩ : syracuseStep 2015219 = 3022829) B3022829
theorem B1590137 : Blo 706319 1590137 := bstep (se 2 (by rfl) ⟨596301, by rfl⟩ : syracuseStep 1590137 = 1192603) B1192603
theorem B7652231 : Blo 706319 7652231 := bstep (se 1 (by rfl) ⟨5739173, by rfl⟩ : syracuseStep 7652231 = 11478347) B11478347
theorem B2016859 : Blo 706319 2016859 := bstep (se 1 (by rfl) ⟨1512644, by rfl⟩ : syracuseStep 2016859 = 3025289) B3025289
theorem B1590911 : Blo 706319 1590911 := bstep (se 1 (by rfl) ⟨1193183, by rfl⟩ : syracuseStep 1590911 = 2386367) B2386367
theorem B706431 : Blo 706319 706431 := bstep (se 1 (by rfl) ⟨529823, by rfl⟩ : syracuseStep 706431 = 1059647) B1059647
theorem B707039 : Blo 706319 707039 := bstep (se 1 (by rfl) ⟨530279, by rfl⟩ : syracuseStep 707039 = 1060559) B1060559
theorem B707199 : Blo 706319 707199 := bstep (se 1 (by rfl) ⟨530399, by rfl⟩ : syracuseStep 707199 = 1060799) B1060799
theorem B707239 : Blo 706319 707239 := bstep (se 1 (by rfl) ⟨530429, by rfl⟩ : syracuseStep 707239 = 1060859) B1060859
theorem B707323 : Blo 706319 707323 := bstep (se 1 (by rfl) ⟨530492, by rfl⟩ : syracuseStep 707323 = 1060985) B1060985
theorem B708767 : Blo 706319 708767 := bstep (se 1 (by rfl) ⟨531575, by rfl⟩ : syracuseStep 708767 = 1063151) B1063151
theorem B709147 : Blo 706319 709147 := bstep (se 1 (by rfl) ⟨531860, by rfl⟩ : syracuseStep 709147 = 1063721) B1063721
theorem B1790495 : Blo 706319 1790495 := bstep (se 1 (by rfl) ⟨1342871, by rfl⟩ : syracuseStep 1790495 = 2685743) B2685743
theorem B11489951 : Blo 706319 11489951 := bstep (se 1 (by rfl) ⟨8617463, by rfl⟩ : syracuseStep 11489951 = 17234927) B17234927
theorem B709359 : Blo 706319 709359 := bstep (se 1 (by rfl) ⟨532019, by rfl⟩ : syracuseStep 709359 = 1064039) B1064039
theorem B1790707 : Blo 706319 1790707 := bstep (se 1 (by rfl) ⟨1343030, by rfl⟩ : syracuseStep 1790707 = 2686061) B2686061
theorem B709447 : Blo 706319 709447 := bstep (se 1 (by rfl) ⟨532085, by rfl⟩ : syracuseStep 709447 = 1064171) B1064171
theorem B3593159 : Blo 706319 3593159 := bstep (se 1 (by rfl) ⟨2694869, by rfl⟩ : syracuseStep 3593159 = 5389739) B5389739
theorem B709659 : Blo 706319 709659 := bstep (se 1 (by rfl) ⟨532244, by rfl⟩ : syracuseStep 709659 = 1064489) B1064489
theorem B1594871 : Blo 706319 1594871 := bstep (se 1 (by rfl) ⟨1196153, by rfl⟩ : syracuseStep 1594871 = 2392307) B2392307
theorem B2875051 : Blo 706319 2875051 := bstep (se 1 (by rfl) ⟨2156288, by rfl⟩ : syracuseStep 2875051 = 4312577) B4312577
theorem B2384639 : Blo 706319 2384639 := bstep (se 1 (by rfl) ⟨1788479, by rfl⟩ : syracuseStep 2384639 = 3576959) B3576959
theorem B113437745 : Blo 706319 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B1341193 : Blo 706319 1341193 := bstep (se 2 (by rfl) ⟨502947, by rfl⟩ : syracuseStep 1341193 = 1005895) B1005895
theorem B1703195 : Blo 706319 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B212925773 : Blo 706319 212925773 := bstep (se 3 (by rfl) ⟨39923582, by rfl⟩ : syracuseStep 212925773 = 79847165) B79847165
theorem B1509023 : Blo 706319 1509023 := bstep (se 1 (by rfl) ⟨1131767, by rfl⟩ : syracuseStep 1509023 = 2263535) B2263535
theorem B30639869 : Blo 706319 30639869 := bstep (se 3 (by rfl) ⟨5744975, by rfl⟩ : syracuseStep 30639869 = 11489951) B11489951
theorem B2689145 : Blo 706319 2689145 := bstep (se 2 (by rfl) ⟨1008429, by rfl⟩ : syracuseStep 2689145 = 2016859) B2016859
theorem B2395439 : Blo 706319 2395439 := bstep (se 1 (by rfl) ⟨1796579, by rfl⟩ : syracuseStep 2395439 = 3593159) B3593159
theorem B8623205 : Blo 706319 8623205 := bstep (se 4 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 8623205 = 1616851) B1616851
theorem B2728009 : Blo 706319 2728009 := bstep (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) B2046007
theorem B2695463 : Blo 706319 2695463 := bstep (se 1 (by rfl) ⟨2021597, by rfl⟩ : syracuseStep 2695463 = 4043195) B4043195
theorem B15345359 : Blo 706319 15345359 := bstep (se 1 (by rfl) ⟨11509019, by rfl⟩ : syracuseStep 15345359 = 23018039) B23018039
theorem B3321043 : Blo 706319 3321043 := bstep (se 1 (by rfl) ⟨2490782, by rfl⟩ : syracuseStep 3321043 = 4981565) B4981565
theorem B1060091 : Blo 706319 1060091 := bstep (se 1 (by rfl) ⟨795068, by rfl⟩ : syracuseStep 1060091 = 1590137) B1590137
theorem B1060607 : Blo 706319 1060607 := bstep (se 1 (by rfl) ⟨795455, by rfl⟩ : syracuseStep 1060607 = 1590911) B1590911
theorem B7745449 : Blo 706319 7745449 := bstep (se 2 (by rfl) ⟨2904543, by rfl⟩ : syracuseStep 7745449 = 5809087) B5809087
theorem B3584249 : Blo 706319 3584249 := bstep (se 2 (by rfl) ⟨1344093, by rfl⟩ : syracuseStep 3584249 = 2688187) B2688187
theorem B3585383 : Blo 706319 3585383 := bstep (se 1 (by rfl) ⟨2689037, by rfl⟩ : syracuseStep 3585383 = 5378075) B5378075
theorem B898543 : Blo 706319 898543 := bstep (se 1 (by rfl) ⟨673907, by rfl⟩ : syracuseStep 898543 = 1347815) B1347815
theorem B1193663 : Blo 706319 1193663 := bstep (se 1 (by rfl) ⟨895247, by rfl⟩ : syracuseStep 1193663 = 1790495) B1790495
theorem B1063247 : Blo 706319 1063247 := bstep (se 1 (by rfl) ⟨797435, by rfl⟩ : syracuseStep 1063247 = 1594871) B1594871
theorem B46447187 : Blo 706319 46447187 := bstep (se 1 (by rfl) ⟨34835390, by rfl⟩ : syracuseStep 46447187 = 69670781) B69670781
theorem B6799247 : Blo 706319 6799247 := bstep (se 1 (by rfl) ⟨5099435, by rfl⟩ : syracuseStep 6799247 = 10198871) B10198871
theorem B1589759 : Blo 706319 1589759 := bstep (se 1 (by rfl) ⟨1192319, by rfl⟩ : syracuseStep 1589759 = 2384639) B2384639
theorem B1589993 : Blo 706319 1589993 := bstep (se 2 (by rfl) ⟨596247, by rfl⟩ : syracuseStep 1589993 = 1192495) B1192495
theorem B1788257 : Blo 706319 1788257 := bstep (se 2 (by rfl) ⟨670596, by rfl⟩ : syracuseStep 1788257 = 1341193) B1341193
theorem B3590891 : Blo 706319 3590891 := bstep (se 1 (by rfl) ⟨2693168, by rfl⟩ : syracuseStep 3590891 = 5386337) B5386337
theorem B707359 : Blo 706319 707359 := bstep (se 1 (by rfl) ⟨530519, by rfl⟩ : syracuseStep 707359 = 1061039) B1061039
theorem B1592297 : Blo 706319 1592297 := bstep (se 2 (by rfl) ⟨597111, by rfl⟩ : syracuseStep 1592297 = 1194223) B1194223
theorem B707839 : Blo 706319 707839 := bstep (se 1 (by rfl) ⟨530879, by rfl⟩ : syracuseStep 707839 = 1061759) B1061759
theorem B708511 : Blo 706319 708511 := bstep (se 1 (by rfl) ⟨531383, by rfl⟩ : syracuseStep 708511 = 1062767) B1062767
theorem B7655903 : Blo 706319 7655903 := bstep (se 1 (by rfl) ⟨5741927, by rfl⟩ : syracuseStep 7655903 = 11483855) B11483855
theorem B709103 : Blo 706319 709103 := bstep (se 1 (by rfl) ⟨531827, by rfl⟩ : syracuseStep 709103 = 1063655) B1063655
theorem B1135463 : Blo 706319 1135463 := bstep (se 1 (by rfl) ⟨851597, by rfl⟩ : syracuseStep 1135463 = 1703195) B1703195
theorem B709863 : Blo 706319 709863 := bstep (se 1 (by rfl) ⟨532397, by rfl⟩ : syracuseStep 709863 = 1064795) B1064795
theorem B7263677 : Blo 706319 7263677 := bstep (se 3 (by rfl) ⟨1361939, by rfl⟩ : syracuseStep 7263677 = 2723879) B2723879
theorem B1594907 : Blo 706319 1594907 := bstep (se 1 (by rfl) ⟨1196180, by rfl⟩ : syracuseStep 1594907 = 2392361) B2392361
theorem B1136335 : Blo 706319 1136335 := bstep (se 1 (by rfl) ⟨852251, by rfl⟩ : syracuseStep 1136335 = 1704503) B1704503
theorem B1595303 : Blo 706319 1595303 := bstep (se 1 (by rfl) ⟨1196477, by rfl⟩ : syracuseStep 1595303 = 2392955) B2392955
theorem B5101487 : Blo 706319 5101487 := bstep (se 1 (by rfl) ⟨3826115, by rfl⟩ : syracuseStep 5101487 = 7652231) B7652231
theorem B1595627 : Blo 706319 1595627 := bstep (se 1 (by rfl) ⟨1196720, by rfl⟩ : syracuseStep 1595627 = 2393441) B2393441
theorem B17194639 : Blo 706319 17194639 := bstep (se 1 (by rfl) ⟨12895979, by rfl⟩ : syracuseStep 17194639 = 25791959) B25791959
theorem B1597247 : Blo 706319 1597247 := bstep (se 1 (by rfl) ⟨1197935, by rfl⟩ : syracuseStep 1597247 = 2395871) B2395871
theorem B8087525 : Blo 706319 8087525 := bstep (se 4 (by rfl) ⟨758205, by rfl⟩ : syracuseStep 8087525 = 1516411) B1516411
theorem B4549439 : Blo 706319 4549439 := bstep (se 1 (by rfl) ⟨3412079, by rfl⟩ : syracuseStep 4549439 = 6824159) B6824159
theorem B1797673 : Blo 706319 1797673 := bstep (se 2 (by rfl) ⟨674127, by rfl⟩ : syracuseStep 1797673 = 1348255) B1348255
theorem B2387609 : Blo 706319 2387609 := bstep (se 2 (by rfl) ⟨895353, by rfl⟩ : syracuseStep 2387609 = 1790707) B1790707
theorem B2387879 : Blo 706319 2387879 := bstep (se 1 (by rfl) ⟨1790909, by rfl⟩ : syracuseStep 2387879 = 3581819) B3581819
theorem B2388527 : Blo 706319 2388527 := bstep (se 1 (by rfl) ⟨1791395, by rfl⟩ : syracuseStep 2388527 = 3582791) B3582791
theorem B75625163 : Blo 706319 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B2552633 : Blo 706319 2552633 := bstep (se 2 (by rfl) ⟨957237, by rfl⟩ : syracuseStep 2552633 = 1914475) B1914475
theorem B141950515 : Blo 706319 141950515 := bstep (se 1 (by rfl) ⟨106462886, by rfl⟩ : syracuseStep 141950515 = 212925773) B212925773
theorem B3833401 : Blo 706319 3833401 := bstep (se 2 (by rfl) ⟨1437525, by rfl⟩ : syracuseStep 3833401 = 2875051) B2875051
theorem B1343479 : Blo 706319 1343479 := bstep (se 1 (by rfl) ⟨1007609, by rfl⟩ : syracuseStep 1343479 = 2015219) B2015219
theorem B14549381 : Blo 706319 14549381 := bstep (se 4 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 14549381 = 2728009) B2728009
theorem B2393927 : Blo 706319 2393927 := bstep (se 1 (by rfl) ⟨1795445, by rfl⟩ : syracuseStep 2393927 = 3590891) B3590891
theorem B2396897 : Blo 706319 2396897 := bstep (se 2 (by rfl) ⟨898836, by rfl⟩ : syracuseStep 2396897 = 1797673) B1797673
theorem B10327265 : Blo 706319 10327265 := bstep (se 2 (by rfl) ⟨3872724, by rfl⟩ : syracuseStep 10327265 = 7745449) B7745449
theorem B10230239 : Blo 706319 10230239 := bstep (se 1 (by rfl) ⟨7672679, by rfl⟩ : syracuseStep 10230239 = 15345359) B15345359
theorem B1515113 : Blo 706319 1515113 := bstep (se 2 (by rfl) ⟨568167, by rfl⟩ : syracuseStep 1515113 = 1136335) B1136335
theorem B795775 : Blo 706319 795775 := bstep (se 1 (by rfl) ⟨596831, by rfl⟩ : syracuseStep 795775 = 1193663) B1193663
theorem B4532831 : Blo 706319 4532831 := bstep (se 1 (by rfl) ⟨3399623, by rfl⟩ : syracuseStep 4532831 = 6799247) B6799247
theorem B1059839 : Blo 706319 1059839 := bstep (se 1 (by rfl) ⟨794879, by rfl⟩ : syracuseStep 1059839 = 1589759) B1589759
theorem B1059995 : Blo 706319 1059995 := bstep (se 1 (by rfl) ⟨794996, by rfl⟩ : syracuseStep 1059995 = 1589993) B1589993
theorem B20426579 : Blo 706319 20426579 := bstep (se 1 (by rfl) ⟨15319934, by rfl⟩ : syracuseStep 20426579 = 30639869) B30639869
theorem B1192171 : Blo 706319 1192171 := bstep (se 1 (by rfl) ⟨894128, by rfl⟩ : syracuseStep 1192171 = 1788257) B1788257
theorem B1061531 : Blo 706319 1061531 := bstep (se 1 (by rfl) ⟨796148, by rfl⟩ : syracuseStep 1061531 = 1592297) B1592297
theorem B5748803 : Blo 706319 5748803 := bstep (se 1 (by rfl) ⟨4311602, by rfl⟩ : syracuseStep 5748803 = 8623205) B8623205
theorem B1063271 : Blo 706319 1063271 := bstep (se 1 (by rfl) ⟨797453, by rfl⟩ : syracuseStep 1063271 = 1594907) B1594907
theorem B1063535 : Blo 706319 1063535 := bstep (se 1 (by rfl) ⟨797651, by rfl⟩ : syracuseStep 1063535 = 1595303) B1595303
theorem B1063751 : Blo 706319 1063751 := bstep (se 1 (by rfl) ⟨797813, by rfl⟩ : syracuseStep 1063751 = 1595627) B1595627
theorem B1064831 : Blo 706319 1064831 := bstep (se 1 (by rfl) ⟨798623, by rfl⟩ : syracuseStep 1064831 = 1597247) B1597247
theorem B495436661 : Blo 706319 495436661 := bstep (se 5 (by rfl) ⟨23223593, by rfl⟩ : syracuseStep 495436661 = 46447187) B46447187
theorem B17712229 : Blo 706319 17712229 := bstep (se 4 (by rfl) ⟨1660521, by rfl⟩ : syracuseStep 17712229 = 3321043) B3321043
theorem B5391683 : Blo 706319 5391683 := bstep (se 1 (by rfl) ⟨4043762, by rfl⟩ : syracuseStep 5391683 = 8087525) B8087525
theorem B3032959 : Blo 706319 3032959 := bstep (se 1 (by rfl) ⟨2274719, by rfl⟩ : syracuseStep 3032959 = 4549439) B4549439
theorem B1198057 : Blo 706319 1198057 := bstep (se 2 (by rfl) ⟨449271, by rfl⟩ : syracuseStep 1198057 = 898543) B898543
theorem B706727 : Blo 706319 706727 := bstep (se 1 (by rfl) ⟨530045, by rfl⟩ : syracuseStep 706727 = 1060091) B1060091
theorem B1591739 : Blo 706319 1591739 := bstep (se 1 (by rfl) ⟨1193804, by rfl⟩ : syracuseStep 1591739 = 2387609) B2387609
theorem B707071 : Blo 706319 707071 := bstep (se 1 (by rfl) ⟨530303, by rfl⟩ : syracuseStep 707071 = 1060607) B1060607
theorem B1591919 : Blo 706319 1591919 := bstep (se 1 (by rfl) ⟨1193939, by rfl⟩ : syracuseStep 1591919 = 2387879) B2387879
theorem B1592351 : Blo 706319 1592351 := bstep (se 1 (by rfl) ⟨1194263, by rfl⟩ : syracuseStep 1592351 = 2388527) B2388527
theorem B50416775 : Blo 706319 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B12111605 : Blo 706319 12111605 := bstep (se 5 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 12111605 = 1135463) B1135463
theorem B708831 : Blo 706319 708831 := bstep (se 1 (by rfl) ⟨531623, by rfl⟩ : syracuseStep 708831 = 1063247) B1063247
theorem B22926185 : Blo 706319 22926185 := bstep (se 2 (by rfl) ⟨8597319, by rfl⟩ : syracuseStep 22926185 = 17194639) B17194639
theorem B1791305 : Blo 706319 1791305 := bstep (se 2 (by rfl) ⟨671739, by rfl⟩ : syracuseStep 1791305 = 1343479) B1343479
theorem B1006015 : Blo 706319 1006015 := bstep (se 1 (by rfl) ⟨754511, by rfl⟩ : syracuseStep 1006015 = 1509023) B1509023
theorem B1792763 : Blo 706319 1792763 := bstep (se 1 (by rfl) ⟨1344572, by rfl⟩ : syracuseStep 1792763 = 2689145) B2689145
theorem B1596959 : Blo 706319 1596959 := bstep (se 1 (by rfl) ⟨1197719, by rfl⟩ : syracuseStep 1596959 = 2395439) B2395439
theorem B5103935 : Blo 706319 5103935 := bstep (se 1 (by rfl) ⟨3827951, by rfl⟩ : syracuseStep 5103935 = 7655903) B7655903
theorem B4842451 : Blo 706319 4842451 := bstep (se 1 (by rfl) ⟨3631838, by rfl⟩ : syracuseStep 4842451 = 7263677) B7263677
theorem B3400991 : Blo 706319 3400991 := bstep (se 1 (by rfl) ⟨2550743, by rfl⟩ : syracuseStep 3400991 = 5101487) B5101487
theorem B1796975 : Blo 706319 1796975 := bstep (se 1 (by rfl) ⟨1347731, by rfl⟩ : syracuseStep 1796975 = 2695463) B2695463
theorem B2389499 : Blo 706319 2389499 := bstep (se 1 (by rfl) ⟨1792124, by rfl⟩ : syracuseStep 2389499 = 3584249) B3584249
theorem B1701755 : Blo 706319 1701755 := bstep (se 1 (by rfl) ⟨1276316, by rfl⟩ : syracuseStep 1701755 = 2552633) B2552633
theorem B2390255 : Blo 706319 2390255 := bstep (se 1 (by rfl) ⟨1792691, by rfl⟩ : syracuseStep 2390255 = 3585383) B3585383
theorem B189267353 : Blo 706319 189267353 := bstep (se 2 (by rfl) ⟨70975257, by rfl⟩ : syracuseStep 189267353 = 141950515) B141950515
theorem B5111201 : Blo 706319 5111201 := bstep (se 2 (by rfl) ⟨1916700, by rfl⟩ : syracuseStep 5111201 = 3833401) B3833401
theorem B9699587 : Blo 706319 9699587 := bstep (se 1 (by rfl) ⟨7274690, by rfl⟩ : syracuseStep 9699587 = 14549381) B14549381
theorem B6456601 : Blo 706319 6456601 := bstep (se 2 (by rfl) ⟨2421225, by rfl⟩ : syracuseStep 6456601 = 4842451) B4842451
theorem B6884843 : Blo 706319 6884843 := bstep (se 1 (by rfl) ⟨5163632, by rfl⟩ : syracuseStep 6884843 = 10327265) B10327265
theorem B2267327 : Blo 706319 2267327 := bstep (se 1 (by rfl) ⟨1700495, by rfl⟩ : syracuseStep 2267327 = 3400991) B3400991
theorem B3021887 : Blo 706319 3021887 := bstep (se 1 (by rfl) ⟨2266415, by rfl⟩ : syracuseStep 3021887 = 4532831) B4532831
theorem B1061033 : Blo 706319 1061033 := bstep (se 2 (by rfl) ⟨397887, by rfl⟩ : syracuseStep 1061033 = 795775) B795775
theorem B1061159 : Blo 706319 1061159 := bstep (se 1 (by rfl) ⟨795869, by rfl⟩ : syracuseStep 1061159 = 1591739) B1591739
theorem B1061279 : Blo 706319 1061279 := bstep (se 1 (by rfl) ⟨795959, by rfl⟩ : syracuseStep 1061279 = 1591919) B1591919
theorem B1061567 : Blo 706319 1061567 := bstep (se 1 (by rfl) ⟨796175, by rfl⟩ : syracuseStep 1061567 = 1592351) B1592351
theorem B8074403 : Blo 706319 8074403 := bstep (se 1 (by rfl) ⟨6055802, by rfl⟩ : syracuseStep 8074403 = 12111605) B12111605
theorem B4043945 : Blo 706319 4043945 := bstep (se 2 (by rfl) ⟨1516479, by rfl⟩ : syracuseStep 4043945 = 3032959) B3032959
theorem B15284123 : Blo 706319 15284123 := bstep (se 1 (by rfl) ⟨11463092, by rfl⟩ : syracuseStep 15284123 = 22926185) B22926185
theorem B1194203 : Blo 706319 1194203 := bstep (se 1 (by rfl) ⟨895652, by rfl⟩ : syracuseStep 1194203 = 1791305) B1791305
theorem B1195175 : Blo 706319 1195175 := bstep (se 1 (by rfl) ⟨896381, by rfl⟩ : syracuseStep 1195175 = 1792763) B1792763
theorem B1064639 : Blo 706319 1064639 := bstep (se 1 (by rfl) ⟨798479, by rfl⟩ : syracuseStep 1064639 = 1596959) B1596959
theorem B1589561 : Blo 706319 1589561 := bstep (se 2 (by rfl) ⟨596085, by rfl⟩ : syracuseStep 1589561 = 1192171) B1192171
theorem B27280637 : Blo 706319 27280637 := bstep (se 3 (by rfl) ⟨5115119, by rfl⟩ : syracuseStep 27280637 = 10230239) B10230239
theorem B1197983 : Blo 706319 1197983 := bstep (se 1 (by rfl) ⟨898487, by rfl⟩ : syracuseStep 1197983 = 1796975) B1796975
theorem B706559 : Blo 706319 706559 := bstep (se 1 (by rfl) ⟨529919, by rfl⟩ : syracuseStep 706559 = 1059839) B1059839
theorem B706663 : Blo 706319 706663 := bstep (se 1 (by rfl) ⟨529997, by rfl⟩ : syracuseStep 706663 = 1059995) B1059995
theorem B13617719 : Blo 706319 13617719 := bstep (se 1 (by rfl) ⟨10213289, by rfl⟩ : syracuseStep 13617719 = 20426579) B20426579
theorem B707687 : Blo 706319 707687 := bstep (se 1 (by rfl) ⟨530765, by rfl⟩ : syracuseStep 707687 = 1061531) B1061531
theorem B1592999 : Blo 706319 1592999 := bstep (se 1 (by rfl) ⟨1194749, by rfl⟩ : syracuseStep 1592999 = 2389499) B2389499
theorem B1134503 : Blo 706319 1134503 := bstep (se 1 (by rfl) ⟨850877, by rfl⟩ : syracuseStep 1134503 = 1701755) B1701755
theorem B1593503 : Blo 706319 1593503 := bstep (se 1 (by rfl) ⟨1195127, by rfl⟩ : syracuseStep 1593503 = 2390255) B2390255
theorem B708847 : Blo 706319 708847 := bstep (se 1 (by rfl) ⟨531635, by rfl⟩ : syracuseStep 708847 = 1063271) B1063271
theorem B709023 : Blo 706319 709023 := bstep (se 1 (by rfl) ⟨531767, by rfl⟩ : syracuseStep 709023 = 1063535) B1063535
theorem B709167 : Blo 706319 709167 := bstep (se 1 (by rfl) ⟨531875, by rfl⟩ : syracuseStep 709167 = 1063751) B1063751
theorem B126178235 : Blo 706319 126178235 := bstep (se 1 (by rfl) ⟨94633676, by rfl⟩ : syracuseStep 126178235 = 189267353) B189267353
theorem B709887 : Blo 706319 709887 := bstep (se 1 (by rfl) ⟨532415, by rfl⟩ : syracuseStep 709887 = 1064831) B1064831
theorem B330291107 : Blo 706319 330291107 := bstep (se 1 (by rfl) ⟨247718330, by rfl⟩ : syracuseStep 330291107 = 495436661) B495436661
theorem B3594455 : Blo 706319 3594455 := bstep (se 1 (by rfl) ⟨2695841, by rfl⟩ : syracuseStep 3594455 = 5391683) B5391683
theorem B1595951 : Blo 706319 1595951 := bstep (se 1 (by rfl) ⟨1196963, by rfl⟩ : syracuseStep 1595951 = 2393927) B2393927
theorem B23616305 : Blo 706319 23616305 := bstep (se 2 (by rfl) ⟨8856114, by rfl⟩ : syracuseStep 23616305 = 17712229) B17712229
theorem B33611183 : Blo 706319 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B1597409 : Blo 706319 1597409 := bstep (se 2 (by rfl) ⟨599028, by rfl⟩ : syracuseStep 1597409 = 1198057) B1198057
theorem B1597931 : Blo 706319 1597931 := bstep (se 1 (by rfl) ⟨1198448, by rfl⟩ : syracuseStep 1597931 = 2396897) B2396897
theorem B1010075 : Blo 706319 1010075 := bstep (se 1 (by rfl) ⟨757556, by rfl⟩ : syracuseStep 1010075 = 1515113) B1515113
theorem B3402623 : Blo 706319 3402623 := bstep (se 1 (by rfl) ⟨2551967, by rfl⟩ : syracuseStep 3402623 = 5103935) B5103935
theorem B1341353 : Blo 706319 1341353 := bstep (se 2 (by rfl) ⟨503007, by rfl⟩ : syracuseStep 1341353 = 1006015) B1006015
theorem B3832535 : Blo 706319 3832535 := bstep (se 1 (by rfl) ⟨2874401, by rfl⟩ : syracuseStep 3832535 = 5748803) B5748803
theorem B3407467 : Blo 706319 3407467 := bstep (se 1 (by rfl) ⟨2555600, by rfl⟩ : syracuseStep 3407467 = 5111201) B5111201
theorem B18187091 : Blo 706319 18187091 := bstep (se 1 (by rfl) ⟨13640318, by rfl⟩ : syracuseStep 18187091 = 27280637) B27280637
theorem B9078479 : Blo 706319 9078479 := bstep (se 1 (by rfl) ⟨6808859, by rfl⟩ : syracuseStep 9078479 = 13617719) B13617719
theorem B756335 : Blo 706319 756335 := bstep (se 1 (by rfl) ⟨567251, by rfl⟩ : syracuseStep 756335 = 1134503) B1134503
theorem B84118823 : Blo 706319 84118823 := bstep (se 1 (by rfl) ⟨63089117, by rfl⟩ : syracuseStep 84118823 = 126178235) B126178235
theorem B1511551 : Blo 706319 1511551 := bstep (se 1 (by rfl) ⟨1133663, by rfl⟩ : syracuseStep 1511551 = 2267327) B2267327
theorem B2396303 : Blo 706319 2396303 := bstep (se 1 (by rfl) ⟨1797227, by rfl⟩ : syracuseStep 2396303 = 3594455) B3594455
theorem B2693533 : Blo 706319 2693533 := bstep (se 3 (by rfl) ⟨505037, by rfl⟩ : syracuseStep 2693533 = 1010075) B1010075
theorem B2268415 : Blo 706319 2268415 := bstep (se 1 (by rfl) ⟨1701311, by rfl⟩ : syracuseStep 2268415 = 3402623) B3402623
theorem B5382935 : Blo 706319 5382935 := bstep (se 1 (by rfl) ⟨4037201, by rfl⟩ : syracuseStep 5382935 = 8074403) B8074403
theorem B2695963 : Blo 706319 2695963 := bstep (se 1 (by rfl) ⟨2021972, by rfl⟩ : syracuseStep 2695963 = 4043945) B4043945
theorem B894235 : Blo 706319 894235 := bstep (se 1 (by rfl) ⟨670676, by rfl⟩ : syracuseStep 894235 = 1341353) B1341353
theorem B18359581 : Blo 706319 18359581 := bstep (se 3 (by rfl) ⟨3442421, by rfl⟩ : syracuseStep 18359581 = 6884843) B6884843
theorem B796135 : Blo 706319 796135 := bstep (se 1 (by rfl) ⟨597101, by rfl⟩ : syracuseStep 796135 = 1194203) B1194203
theorem B796783 : Blo 706319 796783 := bstep (se 1 (by rfl) ⟨597587, by rfl⟩ : syracuseStep 796783 = 1195175) B1195175
theorem B6466391 : Blo 706319 6466391 := bstep (se 1 (by rfl) ⟨4849793, by rfl⟩ : syracuseStep 6466391 = 9699587) B9699587
theorem B1059707 : Blo 706319 1059707 := bstep (se 1 (by rfl) ⟨794780, by rfl⟩ : syracuseStep 1059707 = 1589561) B1589561
theorem B798655 : Blo 706319 798655 := bstep (se 1 (by rfl) ⟨598991, by rfl⟩ : syracuseStep 798655 = 1197983) B1197983
theorem B1061999 : Blo 706319 1061999 := bstep (se 1 (by rfl) ⟨796499, by rfl⟩ : syracuseStep 1061999 = 1592999) B1592999
theorem B1062335 : Blo 706319 1062335 := bstep (se 1 (by rfl) ⟨796751, by rfl⟩ : syracuseStep 1062335 = 1593503) B1593503
theorem B1063967 : Blo 706319 1063967 := bstep (se 1 (by rfl) ⟨797975, by rfl⟩ : syracuseStep 1063967 = 1595951) B1595951
theorem B15744203 : Blo 706319 15744203 := bstep (se 1 (by rfl) ⟨11808152, by rfl⟩ : syracuseStep 15744203 = 23616305) B23616305
theorem B1064939 : Blo 706319 1064939 := bstep (se 1 (by rfl) ⟨798704, by rfl⟩ : syracuseStep 1064939 = 1597409) B1597409
theorem B1065287 : Blo 706319 1065287 := bstep (se 1 (by rfl) ⟨798965, by rfl⟩ : syracuseStep 1065287 = 1597931) B1597931
theorem B707355 : Blo 706319 707355 := bstep (se 1 (by rfl) ⟨530516, by rfl⟩ : syracuseStep 707355 = 1061033) B1061033
theorem B707439 : Blo 706319 707439 := bstep (se 1 (by rfl) ⟨530579, by rfl⟩ : syracuseStep 707439 = 1061159) B1061159
theorem B707519 : Blo 706319 707519 := bstep (se 1 (by rfl) ⟨530639, by rfl⟩ : syracuseStep 707519 = 1061279) B1061279
theorem B707711 : Blo 706319 707711 := bstep (se 1 (by rfl) ⟨530783, by rfl⟩ : syracuseStep 707711 = 1061567) B1061567
theorem B4543289 : Blo 706319 4543289 := bstep (se 2 (by rfl) ⟨1703733, by rfl⟩ : syracuseStep 4543289 = 3407467) B3407467
theorem B709759 : Blo 706319 709759 := bstep (se 1 (by rfl) ⟨532319, by rfl⟩ : syracuseStep 709759 = 1064639) B1064639
theorem B220194071 : Blo 706319 220194071 := bstep (se 1 (by rfl) ⟨165145553, by rfl⟩ : syracuseStep 220194071 = 330291107) B330291107
theorem B22407455 : Blo 706319 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B34435205 : Blo 706319 34435205 := bstep (se 4 (by rfl) ⟨3228300, by rfl⟩ : syracuseStep 34435205 = 6456601) B6456601
theorem B10220093 : Blo 706319 10220093 := bstep (se 3 (by rfl) ⟨1916267, by rfl⟩ : syracuseStep 10220093 = 3832535) B3832535
theorem B8058365 : Blo 706319 8058365 := bstep (se 3 (by rfl) ⟨1510943, by rfl⟩ : syracuseStep 8058365 = 3021887) B3021887
theorem B10189415 : Blo 706319 10189415 := bstep (se 1 (by rfl) ⟨7642061, by rfl⟩ : syracuseStep 10189415 = 15284123) B15284123
theorem B12124727 : Blo 706319 12124727 := bstep (se 1 (by rfl) ⟨9093545, by rfl⟩ : syracuseStep 12124727 = 18187091) B18187091
theorem B24479441 : Blo 706319 24479441 := bstep (se 2 (by rfl) ⟨9179790, by rfl⟩ : syracuseStep 24479441 = 18359581) B18359581
theorem B3024553 : Blo 706319 3024553 := bstep (se 2 (by rfl) ⟨1134207, by rfl⟩ : syracuseStep 3024553 = 2268415) B2268415
theorem B6792943 : Blo 706319 6792943 := bstep (se 1 (by rfl) ⟨5094707, by rfl⟩ : syracuseStep 6792943 = 10189415) B10189415
theorem B10496135 : Blo 706319 10496135 := bstep (se 1 (by rfl) ⟨7872101, by rfl⟩ : syracuseStep 10496135 = 15744203) B15744203
theorem B1192313 : Blo 706319 1192313 := bstep (se 2 (by rfl) ⟨447117, by rfl⟩ : syracuseStep 1192313 = 894235) B894235
theorem B1061513 : Blo 706319 1061513 := bstep (se 2 (by rfl) ⟨398067, by rfl⟩ : syracuseStep 1061513 = 796135) B796135
theorem B56079215 : Blo 706319 56079215 := bstep (se 1 (by rfl) ⟨42059411, by rfl⟩ : syracuseStep 56079215 = 84118823) B84118823
theorem B1062377 : Blo 706319 1062377 := bstep (se 2 (by rfl) ⟨398391, by rfl⟩ : syracuseStep 1062377 = 796783) B796783
theorem B3028859 : Blo 706319 3028859 := bstep (se 1 (by rfl) ⟨2271644, by rfl⟩ : syracuseStep 3028859 = 4543289) B4543289
theorem B1064873 : Blo 706319 1064873 := bstep (se 2 (by rfl) ⟨399327, by rfl⟩ : syracuseStep 1064873 = 798655) B798655
theorem B2015401 : Blo 706319 2015401 := bstep (se 2 (by rfl) ⟨755775, by rfl⟩ : syracuseStep 2015401 = 1511551) B1511551
theorem B3588623 : Blo 706319 3588623 := bstep (se 1 (by rfl) ⟨2691467, by rfl⟩ : syracuseStep 3588623 = 5382935) B5382935
theorem B59753213 : Blo 706319 59753213 := bstep (se 3 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 59753213 = 22407455) B22407455
theorem B2016893 : Blo 706319 2016893 := bstep (se 3 (by rfl) ⟨378167, by rfl⟩ : syracuseStep 2016893 = 756335) B756335
theorem B4310927 : Blo 706319 4310927 := bstep (se 1 (by rfl) ⟨3233195, by rfl⟩ : syracuseStep 4310927 = 6466391) B6466391
theorem B706471 : Blo 706319 706471 := bstep (se 1 (by rfl) ⟨529853, by rfl⟩ : syracuseStep 706471 = 1059707) B1059707
theorem B22956803 : Blo 706319 22956803 := bstep (se 1 (by rfl) ⟨17217602, by rfl⟩ : syracuseStep 22956803 = 34435205) B34435205
theorem B3591377 : Blo 706319 3591377 := bstep (se 2 (by rfl) ⟨1346766, by rfl⟩ : syracuseStep 3591377 = 2693533) B2693533
theorem B707999 : Blo 706319 707999 := bstep (se 1 (by rfl) ⟨530999, by rfl⟩ : syracuseStep 707999 = 1061999) B1061999
theorem B708223 : Blo 706319 708223 := bstep (se 1 (by rfl) ⟨531167, by rfl⟩ : syracuseStep 708223 = 1062335) B1062335
theorem B709311 : Blo 706319 709311 := bstep (se 1 (by rfl) ⟨531983, by rfl⟩ : syracuseStep 709311 = 1063967) B1063967
theorem B709959 : Blo 706319 709959 := bstep (se 1 (by rfl) ⟨532469, by rfl⟩ : syracuseStep 709959 = 1064939) B1064939
theorem B710191 : Blo 706319 710191 := bstep (se 1 (by rfl) ⟨532643, by rfl⟩ : syracuseStep 710191 = 1065287) B1065287
theorem B3594617 : Blo 706319 3594617 := bstep (se 2 (by rfl) ⟨1347981, by rfl⟩ : syracuseStep 3594617 = 2695963) B2695963
theorem B6052319 : Blo 706319 6052319 := bstep (se 1 (by rfl) ⟨4539239, by rfl⟩ : syracuseStep 6052319 = 9078479) B9078479
theorem B1597535 : Blo 706319 1597535 := bstep (se 1 (by rfl) ⟨1198151, by rfl⟩ : syracuseStep 1597535 = 2396303) B2396303
theorem B146796047 : Blo 706319 146796047 := bstep (se 1 (by rfl) ⟨110097035, by rfl⟩ : syracuseStep 146796047 = 220194071) B220194071
theorem B6813395 : Blo 706319 6813395 := bstep (se 1 (by rfl) ⟨5110046, by rfl⟩ : syracuseStep 6813395 = 10220093) B10220093
theorem B5372243 : Blo 706319 5372243 := bstep (se 1 (by rfl) ⟨4029182, by rfl⟩ : syracuseStep 5372243 = 8058365) B8058365
theorem B2687201 : Blo 706319 2687201 := bstep (se 2 (by rfl) ⟨1007700, by rfl⟩ : syracuseStep 2687201 = 2015401) B2015401
theorem B2392415 : Blo 706319 2392415 := bstep (se 1 (by rfl) ⟨1794311, by rfl⟩ : syracuseStep 2392415 = 3588623) B3588623
theorem B1344595 : Blo 706319 1344595 := bstep (se 1 (by rfl) ⟨1008446, by rfl⟩ : syracuseStep 1344595 = 2016893) B2016893
theorem B16319627 : Blo 706319 16319627 := bstep (se 1 (by rfl) ⟨12239720, by rfl⟩ : syracuseStep 16319627 = 24479441) B24479441
theorem B15304535 : Blo 706319 15304535 := bstep (se 1 (by rfl) ⟨11478401, by rfl⟩ : syracuseStep 15304535 = 22956803) B22956803
theorem B2394251 : Blo 706319 2394251 := bstep (se 1 (by rfl) ⟨1795688, by rfl⟩ : syracuseStep 2394251 = 3591377) B3591377
theorem B4032737 : Blo 706319 4032737 := bstep (se 2 (by rfl) ⟨1512276, by rfl⟩ : syracuseStep 4032737 = 3024553) B3024553
theorem B2396411 : Blo 706319 2396411 := bstep (se 1 (by rfl) ⟨1797308, by rfl⟩ : syracuseStep 2396411 = 3594617) B3594617
theorem B4034879 : Blo 706319 4034879 := bstep (se 1 (by rfl) ⟨3026159, by rfl⟩ : syracuseStep 4034879 = 6052319) B6052319
theorem B794875 : Blo 706319 794875 := bstep (se 1 (by rfl) ⟨596156, by rfl⟩ : syracuseStep 794875 = 1192313) B1192313
theorem B3581495 : Blo 706319 3581495 := bstep (se 1 (by rfl) ⟨2686121, by rfl⟩ : syracuseStep 3581495 = 5372243) B5372243
theorem B9057257 : Blo 706319 9057257 := bstep (se 2 (by rfl) ⟨3396471, by rfl⟩ : syracuseStep 9057257 = 6792943) B6792943
theorem B1065023 : Blo 706319 1065023 := bstep (se 1 (by rfl) ⟨798767, by rfl⟩ : syracuseStep 1065023 = 1597535) B1597535
theorem B6997423 : Blo 706319 6997423 := bstep (se 1 (by rfl) ⟨5248067, by rfl⟩ : syracuseStep 6997423 = 10496135) B10496135
theorem B97864031 : Blo 706319 97864031 := bstep (se 1 (by rfl) ⟨73398023, by rfl⟩ : syracuseStep 97864031 = 146796047) B146796047
theorem B707675 : Blo 706319 707675 := bstep (se 1 (by rfl) ⟨530756, by rfl⟩ : syracuseStep 707675 = 1061513) B1061513
theorem B708251 : Blo 706319 708251 := bstep (se 1 (by rfl) ⟨531188, by rfl⟩ : syracuseStep 708251 = 1062377) B1062377
theorem B4542263 : Blo 706319 4542263 := bstep (se 1 (by rfl) ⟨3406697, by rfl⟩ : syracuseStep 4542263 = 6813395) B6813395
theorem B2019239 : Blo 706319 2019239 := bstep (se 1 (by rfl) ⟨1514429, by rfl⟩ : syracuseStep 2019239 = 3028859) B3028859
theorem B709915 : Blo 706319 709915 := bstep (se 1 (by rfl) ⟨532436, by rfl⟩ : syracuseStep 709915 = 1064873) B1064873
theorem B8083151 : Blo 706319 8083151 := bstep (se 1 (by rfl) ⟨6062363, by rfl⟩ : syracuseStep 8083151 = 12124727) B12124727
theorem B39835475 : Blo 706319 39835475 := bstep (se 1 (by rfl) ⟨29876606, by rfl⟩ : syracuseStep 39835475 = 59753213) B59753213
theorem B2873951 : Blo 706319 2873951 := bstep (se 1 (by rfl) ⟨2155463, by rfl⟩ : syracuseStep 2873951 = 4310927) B4310927
theorem B37386143 : Blo 706319 37386143 := bstep (se 1 (by rfl) ⟨28039607, by rfl⟩ : syracuseStep 37386143 = 56079215) B56079215
theorem B10879751 : Blo 706319 10879751 := bstep (se 1 (by rfl) ⟨8159813, by rfl⟩ : syracuseStep 10879751 = 16319627) B16319627
theorem B2688491 : Blo 706319 2688491 := bstep (se 1 (by rfl) ⟨2016368, by rfl⟩ : syracuseStep 2688491 = 4032737) B4032737
theorem B65242687 : Blo 706319 65242687 := bstep (se 1 (by rfl) ⟨48932015, by rfl⟩ : syracuseStep 65242687 = 97864031) B97864031
theorem B1346159 : Blo 706319 1346159 := bstep (se 1 (by rfl) ⟨1009619, by rfl⟩ : syracuseStep 1346159 = 2019239) B2019239
theorem B2689919 : Blo 706319 2689919 := bstep (se 1 (by rfl) ⟨2017439, by rfl⟩ : syracuseStep 2689919 = 4034879) B4034879
theorem B6038171 : Blo 706319 6038171 := bstep (se 1 (by rfl) ⟨4528628, by rfl⟩ : syracuseStep 6038171 = 9057257) B9057257
theorem B1059833 : Blo 706319 1059833 := bstep (se 2 (by rfl) ⟨397437, by rfl⟩ : syracuseStep 1059833 = 794875) B794875
theorem B10203023 : Blo 706319 10203023 := bstep (se 1 (by rfl) ⟨7652267, by rfl⟩ : syracuseStep 10203023 = 15304535) B15304535
theorem B3028175 : Blo 706319 3028175 := bstep (se 1 (by rfl) ⟨2271131, by rfl⟩ : syracuseStep 3028175 = 4542263) B4542263
theorem B5388767 : Blo 706319 5388767 := bstep (se 1 (by rfl) ⟨4041575, by rfl⟩ : syracuseStep 5388767 = 8083151) B8083151
theorem B26556983 : Blo 706319 26556983 := bstep (se 1 (by rfl) ⟨19917737, by rfl⟩ : syracuseStep 26556983 = 39835475) B39835475
theorem B1915967 : Blo 706319 1915967 := bstep (se 1 (by rfl) ⟨1436975, by rfl⟩ : syracuseStep 1915967 = 2873951) B2873951
theorem B24924095 : Blo 706319 24924095 := bstep (se 1 (by rfl) ⟨18693071, by rfl⟩ : syracuseStep 24924095 = 37386143) B37386143
theorem B710015 : Blo 706319 710015 := bstep (se 1 (by rfl) ⟨532511, by rfl⟩ : syracuseStep 710015 = 1065023) B1065023
theorem B1791467 : Blo 706319 1791467 := bstep (se 1 (by rfl) ⟨1343600, by rfl⟩ : syracuseStep 1791467 = 2687201) B2687201
theorem B1594943 : Blo 706319 1594943 := bstep (se 1 (by rfl) ⟨1196207, by rfl⟩ : syracuseStep 1594943 = 2392415) B2392415
theorem B1596167 : Blo 706319 1596167 := bstep (se 1 (by rfl) ⟨1197125, by rfl⟩ : syracuseStep 1596167 = 2394251) B2394251
theorem B1792793 : Blo 706319 1792793 := bstep (se 2 (by rfl) ⟨672297, by rfl⟩ : syracuseStep 1792793 = 1344595) B1344595
theorem B9329897 : Blo 706319 9329897 := bstep (se 2 (by rfl) ⟨3498711, by rfl⟩ : syracuseStep 9329897 = 6997423) B6997423
theorem B1597607 : Blo 706319 1597607 := bstep (se 1 (by rfl) ⟨1198205, by rfl⟩ : syracuseStep 1597607 = 2396411) B2396411
theorem B2387663 : Blo 706319 2387663 := bstep (se 1 (by rfl) ⟨1790747, by rfl⟩ : syracuseStep 2387663 = 3581495) B3581495
theorem B16616063 : Blo 706319 16616063 := bstep (se 1 (by rfl) ⟨12462047, by rfl⟩ : syracuseStep 16616063 = 24924095) B24924095
theorem B17704655 : Blo 706319 17704655 := bstep (se 1 (by rfl) ⟨13278491, by rfl⟩ : syracuseStep 17704655 = 26556983) B26556983
theorem B7253167 : Blo 706319 7253167 := bstep (se 1 (by rfl) ⟨5439875, by rfl⟩ : syracuseStep 7253167 = 10879751) B10879751
theorem B1194311 : Blo 706319 1194311 := bstep (se 1 (by rfl) ⟨895733, by rfl⟩ : syracuseStep 1194311 = 1791467) B1791467
theorem B1063295 : Blo 706319 1063295 := bstep (se 1 (by rfl) ⟨797471, by rfl⟩ : syracuseStep 1063295 = 1594943) B1594943
theorem B1064111 : Blo 706319 1064111 := bstep (se 1 (by rfl) ⟨798083, by rfl⟩ : syracuseStep 1064111 = 1596167) B1596167
theorem B1195195 : Blo 706319 1195195 := bstep (se 1 (by rfl) ⟨896396, by rfl⟩ : syracuseStep 1195195 = 1792793) B1792793
theorem B1065071 : Blo 706319 1065071 := bstep (se 1 (by rfl) ⟨798803, by rfl⟩ : syracuseStep 1065071 = 1597607) B1597607
theorem B3589757 : Blo 706319 3589757 := bstep (se 3 (by rfl) ⟨673079, by rfl⟩ : syracuseStep 3589757 = 1346159) B1346159
theorem B706555 : Blo 706319 706555 := bstep (se 1 (by rfl) ⟨529916, by rfl⟩ : syracuseStep 706555 = 1059833) B1059833
theorem B1591775 : Blo 706319 1591775 := bstep (se 1 (by rfl) ⟨1193831, by rfl⟩ : syracuseStep 1591775 = 2387663) B2387663
theorem B6802015 : Blo 706319 6802015 := bstep (se 1 (by rfl) ⟨5101511, by rfl⟩ : syracuseStep 6802015 = 10203023) B10203023
theorem B2018783 : Blo 706319 2018783 := bstep (se 1 (by rfl) ⟨1514087, by rfl⟩ : syracuseStep 2018783 = 3028175) B3028175
theorem B3592511 : Blo 706319 3592511 := bstep (se 1 (by rfl) ⟨2694383, by rfl⟩ : syracuseStep 3592511 = 5388767) B5388767
theorem B1792327 : Blo 706319 1792327 := bstep (se 1 (by rfl) ⟨1344245, by rfl⟩ : syracuseStep 1792327 = 2688491) B2688491
theorem B1793279 : Blo 706319 1793279 := bstep (se 1 (by rfl) ⟨1344959, by rfl⟩ : syracuseStep 1793279 = 2689919) B2689919
theorem B86990249 : Blo 706319 86990249 := bstep (se 2 (by rfl) ⟨32621343, by rfl⟩ : syracuseStep 86990249 = 65242687) B65242687
theorem B6219931 : Blo 706319 6219931 := bstep (se 1 (by rfl) ⟨4664948, by rfl⟩ : syracuseStep 6219931 = 9329897) B9329897
theorem B4025447 : Blo 706319 4025447 := bstep (se 1 (by rfl) ⟨3019085, by rfl⟩ : syracuseStep 4025447 = 6038171) B6038171
theorem B1277311 : Blo 706319 1277311 := bstep (se 1 (by rfl) ⟨957983, by rfl⟩ : syracuseStep 1277311 = 1915967) B1915967
theorem B2393171 : Blo 706319 2393171 := bstep (se 1 (by rfl) ⟨1794878, by rfl⟩ : syracuseStep 2393171 = 3589757) B3589757
theorem B8293241 : Blo 706319 8293241 := bstep (se 2 (by rfl) ⟨3109965, by rfl⟩ : syracuseStep 8293241 = 6219931) B6219931
theorem B2395007 : Blo 706319 2395007 := bstep (se 1 (by rfl) ⟨1796255, by rfl⟩ : syracuseStep 2395007 = 3592511) B3592511
theorem B9670889 : Blo 706319 9670889 := bstep (se 2 (by rfl) ⟨3626583, by rfl⟩ : syracuseStep 9670889 = 7253167) B7253167
theorem B11803103 : Blo 706319 11803103 := bstep (se 1 (by rfl) ⟨8852327, by rfl⟩ : syracuseStep 11803103 = 17704655) B17704655
theorem B44309501 : Blo 706319 44309501 := bstep (se 3 (by rfl) ⟨8308031, by rfl⟩ : syracuseStep 44309501 = 16616063) B16616063
theorem B5383421 : Blo 706319 5383421 := bstep (se 3 (by rfl) ⟨1009391, by rfl⟩ : syracuseStep 5383421 = 2018783) B2018783
theorem B796207 : Blo 706319 796207 := bstep (se 1 (by rfl) ⟨597155, by rfl⟩ : syracuseStep 796207 = 1194311) B1194311
theorem B1061183 : Blo 706319 1061183 := bstep (se 1 (by rfl) ⟨795887, by rfl⟩ : syracuseStep 1061183 = 1591775) B1591775
theorem B1195519 : Blo 706319 1195519 := bstep (se 1 (by rfl) ⟨896639, by rfl⟩ : syracuseStep 1195519 = 1793279) B1793279
theorem B1593593 : Blo 706319 1593593 := bstep (se 2 (by rfl) ⟨597597, by rfl⟩ : syracuseStep 1593593 = 1195195) B1195195
theorem B708863 : Blo 706319 708863 := bstep (se 1 (by rfl) ⟨531647, by rfl⟩ : syracuseStep 708863 = 1063295) B1063295
theorem B709407 : Blo 706319 709407 := bstep (se 1 (by rfl) ⟨532055, by rfl⟩ : syracuseStep 709407 = 1064111) B1064111
theorem B710047 : Blo 706319 710047 := bstep (se 1 (by rfl) ⟨532535, by rfl⟩ : syracuseStep 710047 = 1065071) B1065071
theorem B9069353 : Blo 706319 9069353 := bstep (se 2 (by rfl) ⟨3401007, by rfl⟩ : syracuseStep 9069353 = 6802015) B6802015
theorem B57993499 : Blo 706319 57993499 := bstep (se 1 (by rfl) ⟨43495124, by rfl⟩ : syracuseStep 57993499 = 86990249) B86990249
theorem B2683631 : Blo 706319 2683631 := bstep (se 1 (by rfl) ⟨2012723, by rfl⟩ : syracuseStep 2683631 = 4025447) B4025447
theorem B2389769 : Blo 706319 2389769 := bstep (se 2 (by rfl) ⟨896163, by rfl⟩ : syracuseStep 2389769 = 1792327) B1792327
theorem B1703081 : Blo 706319 1703081 := bstep (se 2 (by rfl) ⟨638655, by rfl⟩ : syracuseStep 1703081 = 1277311) B1277311
theorem B7868735 : Blo 706319 7868735 := bstep (se 1 (by rfl) ⟨5901551, by rfl⟩ : syracuseStep 7868735 = 11803103) B11803103
theorem B1061609 : Blo 706319 1061609 := bstep (se 2 (by rfl) ⟨398103, by rfl⟩ : syracuseStep 1061609 = 796207) B796207
theorem B1062395 : Blo 706319 1062395 := bstep (se 1 (by rfl) ⟨796796, by rfl⟩ : syracuseStep 1062395 = 1593593) B1593593
theorem B29539667 : Blo 706319 29539667 := bstep (se 1 (by rfl) ⟨22154750, by rfl⟩ : syracuseStep 29539667 = 44309501) B44309501
theorem B6046235 : Blo 706319 6046235 := bstep (se 1 (by rfl) ⟨4534676, by rfl⟩ : syracuseStep 6046235 = 9069353) B9069353
theorem B3588947 : Blo 706319 3588947 := bstep (se 1 (by rfl) ⟨2691710, by rfl⟩ : syracuseStep 3588947 = 5383421) B5383421
theorem B707455 : Blo 706319 707455 := bstep (se 1 (by rfl) ⟨530591, by rfl⟩ : syracuseStep 707455 = 1061183) B1061183
theorem B1789087 : Blo 706319 1789087 := bstep (se 1 (by rfl) ⟨1341815, by rfl⟩ : syracuseStep 1789087 = 2683631) B2683631
theorem B1593179 : Blo 706319 1593179 := bstep (se 1 (by rfl) ⟨1194884, by rfl⟩ : syracuseStep 1593179 = 2389769) B2389769
theorem B1594025 : Blo 706319 1594025 := bstep (se 2 (by rfl) ⟨597759, by rfl⟩ : syracuseStep 1594025 = 1195519) B1195519
theorem B1135387 : Blo 706319 1135387 := bstep (se 1 (by rfl) ⟨851540, by rfl⟩ : syracuseStep 1135387 = 1703081) B1703081
theorem B1595447 : Blo 706319 1595447 := bstep (se 1 (by rfl) ⟨1196585, by rfl⟩ : syracuseStep 1595447 = 2393171) B2393171
theorem B5528827 : Blo 706319 5528827 := bstep (se 1 (by rfl) ⟨4146620, by rfl⟩ : syracuseStep 5528827 = 8293241) B8293241
theorem B1596671 : Blo 706319 1596671 := bstep (se 1 (by rfl) ⟨1197503, by rfl⟩ : syracuseStep 1596671 = 2395007) B2395007
theorem B6447259 : Blo 706319 6447259 := bstep (se 1 (by rfl) ⟨4835444, by rfl⟩ : syracuseStep 6447259 = 9670889) B9670889
theorem B77324665 : Blo 706319 77324665 := bstep (se 2 (by rfl) ⟨28996749, by rfl⟩ : syracuseStep 77324665 = 57993499) B57993499
theorem B4030823 : Blo 706319 4030823 := bstep (se 1 (by rfl) ⟨3023117, by rfl⟩ : syracuseStep 4030823 = 6046235) B6046235
theorem B2392631 : Blo 706319 2392631 := bstep (se 1 (by rfl) ⟨1794473, by rfl⟩ : syracuseStep 2392631 = 3588947) B3588947
theorem B5245823 : Blo 706319 5245823 := bstep (se 1 (by rfl) ⟨3934367, by rfl⟩ : syracuseStep 5245823 = 7868735) B7868735
theorem B1513849 : Blo 706319 1513849 := bstep (se 2 (by rfl) ⟨567693, by rfl⟩ : syracuseStep 1513849 = 1135387) B1135387
theorem B103099553 : Blo 706319 103099553 := bstep (se 2 (by rfl) ⟨38662332, by rfl⟩ : syracuseStep 103099553 = 77324665) B77324665
theorem B34385381 : Blo 706319 34385381 := bstep (se 4 (by rfl) ⟨3223629, by rfl⟩ : syracuseStep 34385381 = 6447259) B6447259
theorem B1062119 : Blo 706319 1062119 := bstep (se 1 (by rfl) ⟨796589, by rfl⟩ : syracuseStep 1062119 = 1593179) B1593179
theorem B1062683 : Blo 706319 1062683 := bstep (se 1 (by rfl) ⟨797012, by rfl⟩ : syracuseStep 1062683 = 1594025) B1594025
theorem B1063631 : Blo 706319 1063631 := bstep (se 1 (by rfl) ⟨797723, by rfl⟩ : syracuseStep 1063631 = 1595447) B1595447
theorem B1064447 : Blo 706319 1064447 := bstep (se 1 (by rfl) ⟨798335, by rfl⟩ : syracuseStep 1064447 = 1596671) B1596671
theorem B707739 : Blo 706319 707739 := bstep (se 1 (by rfl) ⟨530804, by rfl⟩ : syracuseStep 707739 = 1061609) B1061609
theorem B708263 : Blo 706319 708263 := bstep (se 1 (by rfl) ⟨531197, by rfl⟩ : syracuseStep 708263 = 1062395) B1062395
theorem B2385449 : Blo 706319 2385449 := bstep (se 2 (by rfl) ⟨894543, by rfl⟩ : syracuseStep 2385449 = 1789087) B1789087
theorem B78772445 : Blo 706319 78772445 := bstep (se 3 (by rfl) ⟨14769833, by rfl⟩ : syracuseStep 78772445 = 29539667) B29539667
theorem B7371769 : Blo 706319 7371769 := bstep (se 2 (by rfl) ⟨2764413, by rfl⟩ : syracuseStep 7371769 = 5528827) B5528827
theorem B2687215 : Blo 706319 2687215 := bstep (se 1 (by rfl) ⟨2015411, by rfl⟩ : syracuseStep 2687215 = 4030823) B4030823
theorem B1590299 : Blo 706319 1590299 := bstep (se 1 (by rfl) ⟨1192724, by rfl⟩ : syracuseStep 1590299 = 2385449) B2385449
theorem B68733035 : Blo 706319 68733035 := bstep (se 1 (by rfl) ⟨51549776, by rfl⟩ : syracuseStep 68733035 = 103099553) B103099553
theorem B22923587 : Blo 706319 22923587 := bstep (se 1 (by rfl) ⟨17192690, by rfl⟩ : syracuseStep 22923587 = 34385381) B34385381
theorem B2018465 : Blo 706319 2018465 := bstep (se 2 (by rfl) ⟨756924, by rfl⟩ : syracuseStep 2018465 = 1513849) B1513849
theorem B708079 : Blo 706319 708079 := bstep (se 1 (by rfl) ⟨531059, by rfl⟩ : syracuseStep 708079 = 1062119) B1062119
theorem B708455 : Blo 706319 708455 := bstep (se 1 (by rfl) ⟨531341, by rfl⟩ : syracuseStep 708455 = 1062683) B1062683
theorem B52514963 : Blo 706319 52514963 := bstep (se 1 (by rfl) ⟨39386222, by rfl⟩ : syracuseStep 52514963 = 78772445) B78772445
theorem B709087 : Blo 706319 709087 := bstep (se 1 (by rfl) ⟨531815, by rfl⟩ : syracuseStep 709087 = 1063631) B1063631
theorem B709631 : Blo 706319 709631 := bstep (se 1 (by rfl) ⟨532223, by rfl⟩ : syracuseStep 709631 = 1064447) B1064447
theorem B1595087 : Blo 706319 1595087 := bstep (se 1 (by rfl) ⟨1196315, by rfl⟩ : syracuseStep 1595087 = 2392631) B2392631
theorem B3497215 : Blo 706319 3497215 := bstep (se 1 (by rfl) ⟨2622911, by rfl⟩ : syracuseStep 3497215 = 5245823) B5245823
theorem B9829025 : Blo 706319 9829025 := bstep (se 2 (by rfl) ⟨3685884, by rfl⟩ : syracuseStep 9829025 = 7371769) B7371769
theorem B1345643 : Blo 706319 1345643 := bstep (se 1 (by rfl) ⟨1009232, by rfl⟩ : syracuseStep 1345643 = 2018465) B2018465
theorem B4662953 : Blo 706319 4662953 := bstep (se 2 (by rfl) ⟨1748607, by rfl⟩ : syracuseStep 4662953 = 3497215) B3497215
theorem B3582953 : Blo 706319 3582953 := bstep (se 2 (by rfl) ⟨1343607, by rfl⟩ : syracuseStep 3582953 = 2687215) B2687215
theorem B1060199 : Blo 706319 1060199 := bstep (se 1 (by rfl) ⟨795149, by rfl⟩ : syracuseStep 1060199 = 1590299) B1590299
theorem B45822023 : Blo 706319 45822023 := bstep (se 1 (by rfl) ⟨34366517, by rfl⟩ : syracuseStep 45822023 = 68733035) B68733035
theorem B15282391 : Blo 706319 15282391 := bstep (se 1 (by rfl) ⟨11461793, by rfl⟩ : syracuseStep 15282391 = 22923587) B22923587
theorem B35009975 : Blo 706319 35009975 := bstep (se 1 (by rfl) ⟨26257481, by rfl⟩ : syracuseStep 35009975 = 52514963) B52514963
theorem B1063391 : Blo 706319 1063391 := bstep (se 1 (by rfl) ⟨797543, by rfl⟩ : syracuseStep 1063391 = 1595087) B1595087
theorem B6552683 : Blo 706319 6552683 := bstep (se 1 (by rfl) ⟨4914512, by rfl⟩ : syracuseStep 6552683 = 9829025) B9829025
theorem B30548015 : Blo 706319 30548015 := bstep (se 1 (by rfl) ⟨22911011, by rfl⟩ : syracuseStep 30548015 = 45822023) B45822023
theorem B23339983 : Blo 706319 23339983 := bstep (se 1 (by rfl) ⟨17504987, by rfl⟩ : syracuseStep 23339983 = 35009975) B35009975
theorem B4368455 : Blo 706319 4368455 := bstep (se 1 (by rfl) ⟨3276341, by rfl⟩ : syracuseStep 4368455 = 6552683) B6552683
theorem B897095 : Blo 706319 897095 := bstep (se 1 (by rfl) ⟨672821, by rfl⟩ : syracuseStep 897095 = 1345643) B1345643
theorem B706799 : Blo 706319 706799 := bstep (se 1 (by rfl) ⟨530099, by rfl⟩ : syracuseStep 706799 = 1060199) B1060199
theorem B708927 : Blo 706319 708927 := bstep (se 1 (by rfl) ⟨531695, by rfl⟩ : syracuseStep 708927 = 1063391) B1063391
theorem B20376521 : Blo 706319 20376521 := bstep (se 2 (by rfl) ⟨7641195, by rfl⟩ : syracuseStep 20376521 = 15282391) B15282391
theorem B3108635 : Blo 706319 3108635 := bstep (se 1 (by rfl) ⟨2331476, by rfl⟩ : syracuseStep 3108635 = 4662953) B4662953
theorem B2388635 : Blo 706319 2388635 := bstep (se 1 (by rfl) ⟨1791476, by rfl⟩ : syracuseStep 2388635 = 3582953) B3582953
theorem B2392253 : Blo 706319 2392253 := bstep (se 3 (by rfl) ⟨448547, by rfl⟩ : syracuseStep 2392253 = 897095) B897095
theorem B2072423 : Blo 706319 2072423 := bstep (se 1 (by rfl) ⟨1554317, by rfl⟩ : syracuseStep 2072423 = 3108635) B3108635
theorem B20365343 : Blo 706319 20365343 := bstep (se 1 (by rfl) ⟨15274007, by rfl⟩ : syracuseStep 20365343 = 30548015) B30548015
theorem B13584347 : Blo 706319 13584347 := bstep (se 1 (by rfl) ⟨10188260, by rfl⟩ : syracuseStep 13584347 = 20376521) B20376521
theorem B1592423 : Blo 706319 1592423 := bstep (se 1 (by rfl) ⟨1194317, by rfl⟩ : syracuseStep 1592423 = 2388635) B2388635
theorem B31119977 : Blo 706319 31119977 := bstep (se 2 (by rfl) ⟨11669991, by rfl⟩ : syracuseStep 31119977 = 23339983) B23339983
theorem B2912303 : Blo 706319 2912303 := bstep (se 1 (by rfl) ⟨2184227, by rfl⟩ : syracuseStep 2912303 = 4368455) B4368455
theorem B1941535 : Blo 706319 1941535 := bstep (se 1 (by rfl) ⟨1456151, by rfl⟩ : syracuseStep 1941535 = 2912303) B2912303
theorem B13576895 : Blo 706319 13576895 := bstep (se 1 (by rfl) ⟨10182671, by rfl⟩ : syracuseStep 13576895 = 20365343) B20365343
theorem B9056231 : Blo 706319 9056231 := bstep (se 1 (by rfl) ⟨6792173, by rfl⟩ : syracuseStep 9056231 = 13584347) B13584347
theorem B1061615 : Blo 706319 1061615 := bstep (se 1 (by rfl) ⟨796211, by rfl⟩ : syracuseStep 1061615 = 1592423) B1592423
theorem B82986605 : Blo 706319 82986605 := bstep (se 3 (by rfl) ⟨15559988, by rfl⟩ : syracuseStep 82986605 = 31119977) B31119977
theorem B5526461 : Blo 706319 5526461 := bstep (se 3 (by rfl) ⟨1036211, by rfl⟩ : syracuseStep 5526461 = 2072423) B2072423
theorem B1594835 : Blo 706319 1594835 := bstep (se 1 (by rfl) ⟨1196126, by rfl⟩ : syracuseStep 1594835 = 2392253) B2392253
theorem B10354853 : Blo 706319 10354853 := bstep (se 4 (by rfl) ⟨970767, by rfl⟩ : syracuseStep 10354853 = 1941535) B1941535
theorem B9051263 : Blo 706319 9051263 := bstep (se 1 (by rfl) ⟨6788447, by rfl⟩ : syracuseStep 9051263 = 13576895) B13576895
theorem B6037487 : Blo 706319 6037487 := bstep (se 1 (by rfl) ⟨4528115, by rfl⟩ : syracuseStep 6037487 = 9056231) B9056231
theorem B55324403 : Blo 706319 55324403 := bstep (se 1 (by rfl) ⟨41493302, by rfl⟩ : syracuseStep 55324403 = 82986605) B82986605
theorem B3684307 : Blo 706319 3684307 := bstep (se 1 (by rfl) ⟨2763230, by rfl⟩ : syracuseStep 3684307 = 5526461) B5526461
theorem B1063223 : Blo 706319 1063223 := bstep (se 1 (by rfl) ⟨797417, by rfl⟩ : syracuseStep 1063223 = 1594835) B1594835
theorem B707743 : Blo 706319 707743 := bstep (se 1 (by rfl) ⟨530807, by rfl⟩ : syracuseStep 707743 = 1061615) B1061615
theorem B6034175 : Blo 706319 6034175 := bstep (se 1 (by rfl) ⟨4525631, by rfl⟩ : syracuseStep 6034175 = 9051263) B9051263
theorem B36882935 : Blo 706319 36882935 := bstep (se 1 (by rfl) ⟨27662201, by rfl⟩ : syracuseStep 36882935 = 55324403) B55324403
theorem B708815 : Blo 706319 708815 := bstep (se 1 (by rfl) ⟨531611, by rfl⟩ : syracuseStep 708815 = 1063223) B1063223
theorem B6903235 : Blo 706319 6903235 := bstep (se 1 (by rfl) ⟨5177426, by rfl⟩ : syracuseStep 6903235 = 10354853) B10354853
theorem B4024991 : Blo 706319 4024991 := bstep (se 1 (by rfl) ⟨3018743, by rfl⟩ : syracuseStep 4024991 = 6037487) B6037487
theorem B4912409 : Blo 706319 4912409 := bstep (se 2 (by rfl) ⟨1842153, by rfl⟩ : syracuseStep 4912409 = 3684307) B3684307
theorem B24588623 : Blo 706319 24588623 := bstep (se 1 (by rfl) ⟨18441467, by rfl⟩ : syracuseStep 24588623 = 36882935) B36882935
theorem B4022783 : Blo 706319 4022783 := bstep (se 1 (by rfl) ⟨3017087, by rfl⟩ : syracuseStep 4022783 = 6034175) B6034175
theorem B2683327 : Blo 706319 2683327 := bstep (se 1 (by rfl) ⟨2012495, by rfl⟩ : syracuseStep 2683327 = 4024991) B4024991
theorem B9204313 : Blo 706319 9204313 := bstep (se 2 (by rfl) ⟨3451617, by rfl⟩ : syracuseStep 9204313 = 6903235) B6903235
theorem B3274939 : Blo 706319 3274939 := bstep (se 1 (by rfl) ⟨2456204, by rfl⟩ : syracuseStep 3274939 = 4912409) B4912409
theorem B3577769 : Blo 706319 3577769 := bstep (se 2 (by rfl) ⟨1341663, by rfl⟩ : syracuseStep 3577769 = 2683327) B2683327
theorem B16392415 : Blo 706319 16392415 := bstep (se 1 (by rfl) ⟨12294311, by rfl⟩ : syracuseStep 16392415 = 24588623) B24588623
theorem B4366585 : Blo 706319 4366585 := bstep (se 2 (by rfl) ⟨1637469, by rfl⟩ : syracuseStep 4366585 = 3274939) B3274939
theorem B12272417 : Blo 706319 12272417 := bstep (se 2 (by rfl) ⟨4602156, by rfl⟩ : syracuseStep 12272417 = 9204313) B9204313
theorem B2681855 : Blo 706319 2681855 := bstep (se 1 (by rfl) ⟨2011391, by rfl⟩ : syracuseStep 2681855 = 4022783) B4022783
theorem B21856553 : Blo 706319 21856553 := bstep (se 2 (by rfl) ⟨8196207, by rfl⟩ : syracuseStep 21856553 = 16392415) B16392415
theorem B1787903 : Blo 706319 1787903 := bstep (se 1 (by rfl) ⟨1340927, by rfl⟩ : syracuseStep 1787903 = 2681855) B2681855
theorem B5822113 : Blo 706319 5822113 := bstep (se 2 (by rfl) ⟨2183292, by rfl⟩ : syracuseStep 5822113 = 4366585) B4366585
theorem B8181611 : Blo 706319 8181611 := bstep (se 1 (by rfl) ⟨6136208, by rfl⟩ : syracuseStep 8181611 = 12272417) B12272417
theorem B2385179 : Blo 706319 2385179 := bstep (se 1 (by rfl) ⟨1788884, by rfl⟩ : syracuseStep 2385179 = 3577769) B3577769
theorem B1191935 : Blo 706319 1191935 := bstep (se 1 (by rfl) ⟨893951, by rfl⟩ : syracuseStep 1191935 = 1787903) B1787903
theorem B5454407 : Blo 706319 5454407 := bstep (se 1 (by rfl) ⟨4090805, by rfl⟩ : syracuseStep 5454407 = 8181611) B8181611
theorem B1590119 : Blo 706319 1590119 := bstep (se 1 (by rfl) ⟨1192589, by rfl⟩ : syracuseStep 1590119 = 2385179) B2385179
theorem B14571035 : Blo 706319 14571035 := bstep (se 1 (by rfl) ⟨10928276, by rfl⟩ : syracuseStep 14571035 = 21856553) B21856553
theorem B7762817 : Blo 706319 7762817 := bstep (se 2 (by rfl) ⟨2911056, by rfl⟩ : syracuseStep 7762817 = 5822113) B5822113
theorem B794623 : Blo 706319 794623 := bstep (se 1 (by rfl) ⟨595967, by rfl⟩ : syracuseStep 794623 = 1191935) B1191935
theorem B1060079 : Blo 706319 1060079 := bstep (se 1 (by rfl) ⟨795059, by rfl⟩ : syracuseStep 1060079 = 1590119) B1590119
theorem B9714023 : Blo 706319 9714023 := bstep (se 1 (by rfl) ⟨7285517, by rfl⟩ : syracuseStep 9714023 = 14571035) B14571035
theorem B20700845 : Blo 706319 20700845 := bstep (se 3 (by rfl) ⟨3881408, by rfl⟩ : syracuseStep 20700845 = 7762817) B7762817
theorem B3636271 : Blo 706319 3636271 := bstep (se 1 (by rfl) ⟨2727203, by rfl⟩ : syracuseStep 3636271 = 5454407) B5454407
theorem B13800563 : Blo 706319 13800563 := bstep (se 1 (by rfl) ⟨10350422, by rfl⟩ : syracuseStep 13800563 = 20700845) B20700845
theorem B1059497 : Blo 706319 1059497 := bstep (se 2 (by rfl) ⟨397311, by rfl⟩ : syracuseStep 1059497 = 794623) B794623
theorem B706719 : Blo 706319 706719 := bstep (se 1 (by rfl) ⟨530039, by rfl⟩ : syracuseStep 706719 = 1060079) B1060079
theorem B6476015 : Blo 706319 6476015 := bstep (se 1 (by rfl) ⟨4857011, by rfl⟩ : syracuseStep 6476015 = 9714023) B9714023
theorem B19393445 : Blo 706319 19393445 := bstep (se 4 (by rfl) ⟨1818135, by rfl⟩ : syracuseStep 19393445 = 3636271) B3636271
theorem B51715853 : Blo 706319 51715853 := bstep (se 3 (by rfl) ⟨9696722, by rfl⟩ : syracuseStep 51715853 = 19393445) B19393445
theorem B706331 : Blo 706319 706331 := bstep (se 1 (by rfl) ⟨529748, by rfl⟩ : syracuseStep 706331 = 1059497) B1059497
theorem B4317343 : Blo 706319 4317343 := bstep (se 1 (by rfl) ⟨3238007, by rfl⟩ : syracuseStep 4317343 = 6476015) B6476015
theorem B9200375 : Blo 706319 9200375 := bstep (se 1 (by rfl) ⟨6900281, by rfl⟩ : syracuseStep 9200375 = 13800563) B13800563
theorem B34477235 : Blo 706319 34477235 := bstep (se 1 (by rfl) ⟨25857926, by rfl⟩ : syracuseStep 34477235 = 51715853) B51715853
theorem B6133583 : Blo 706319 6133583 := bstep (se 1 (by rfl) ⟨4600187, by rfl⟩ : syracuseStep 6133583 = 9200375) B9200375
theorem B23025829 : Blo 706319 23025829 := bstep (se 4 (by rfl) ⟨2158671, by rfl⟩ : syracuseStep 23025829 = 4317343) B4317343
theorem B22984823 : Blo 706319 22984823 := bstep (se 1 (by rfl) ⟨17238617, by rfl⟩ : syracuseStep 22984823 = 34477235) B34477235
theorem B4089055 : Blo 706319 4089055 := bstep (se 1 (by rfl) ⟨3066791, by rfl⟩ : syracuseStep 4089055 = 6133583) B6133583
theorem B30701105 : Blo 706319 30701105 := bstep (se 2 (by rfl) ⟨11512914, by rfl⟩ : syracuseStep 30701105 = 23025829) B23025829
theorem B5452073 : Blo 706319 5452073 := bstep (se 2 (by rfl) ⟨2044527, by rfl⟩ : syracuseStep 5452073 = 4089055) B4089055
theorem B61292861 : Blo 706319 61292861 := bstep (se 3 (by rfl) ⟨11492411, by rfl⟩ : syracuseStep 61292861 = 22984823) B22984823
theorem B20467403 : Blo 706319 20467403 := bstep (se 1 (by rfl) ⟨15350552, by rfl⟩ : syracuseStep 20467403 = 30701105) B30701105
theorem B40861907 : Blo 706319 40861907 := bstep (se 1 (by rfl) ⟨30646430, by rfl⟩ : syracuseStep 40861907 = 61292861) B61292861
theorem B13644935 : Blo 706319 13644935 := bstep (se 1 (by rfl) ⟨10233701, by rfl⟩ : syracuseStep 13644935 = 20467403) B20467403
theorem B3634715 : Blo 706319 3634715 := bstep (se 1 (by rfl) ⟨2726036, by rfl⟩ : syracuseStep 3634715 = 5452073) B5452073
theorem B27241271 : Blo 706319 27241271 := bstep (se 1 (by rfl) ⟨20430953, by rfl⟩ : syracuseStep 27241271 = 40861907) B40861907
theorem B9096623 : Blo 706319 9096623 := bstep (se 1 (by rfl) ⟨6822467, by rfl⟩ : syracuseStep 9096623 = 13644935) B13644935
theorem B2423143 : Blo 706319 2423143 := bstep (se 1 (by rfl) ⟨1817357, by rfl⟩ : syracuseStep 2423143 = 3634715) B3634715
theorem B6064415 : Blo 706319 6064415 := bstep (se 1 (by rfl) ⟨4548311, by rfl⟩ : syracuseStep 6064415 = 9096623) B9096623
theorem B18160847 : Blo 706319 18160847 := bstep (se 1 (by rfl) ⟨13620635, by rfl⟩ : syracuseStep 18160847 = 27241271) B27241271
theorem B3230857 : Blo 706319 3230857 := bstep (se 2 (by rfl) ⟨1211571, by rfl⟩ : syracuseStep 3230857 = 2423143) B2423143
theorem B4042943 : Blo 706319 4042943 := bstep (se 1 (by rfl) ⟨3032207, by rfl⟩ : syracuseStep 4042943 = 6064415) B6064415
theorem B12107231 : Blo 706319 12107231 := bstep (se 1 (by rfl) ⟨9080423, by rfl⟩ : syracuseStep 12107231 = 18160847) B18160847
theorem B17231237 : Blo 706319 17231237 := bstep (se 4 (by rfl) ⟨1615428, by rfl⟩ : syracuseStep 17231237 = 3230857) B3230857
theorem B2695295 : Blo 706319 2695295 := bstep (se 1 (by rfl) ⟨2021471, by rfl⟩ : syracuseStep 2695295 = 4042943) B4042943
theorem B8071487 : Blo 706319 8071487 := bstep (se 1 (by rfl) ⟨6053615, by rfl⟩ : syracuseStep 8071487 = 12107231) B12107231
theorem B11487491 : Blo 706319 11487491 := bstep (se 1 (by rfl) ⟨8615618, by rfl⟩ : syracuseStep 11487491 = 17231237) B17231237
theorem B5380991 : Blo 706319 5380991 := bstep (se 1 (by rfl) ⟨4035743, by rfl⟩ : syracuseStep 5380991 = 8071487) B8071487
theorem B7658327 : Blo 706319 7658327 := bstep (se 1 (by rfl) ⟨5743745, by rfl⟩ : syracuseStep 7658327 = 11487491) B11487491
theorem B1796863 : Blo 706319 1796863 := bstep (se 1 (by rfl) ⟨1347647, by rfl⟩ : syracuseStep 1796863 = 2695295) B2695295
theorem B2395817 : Blo 706319 2395817 := bstep (se 2 (by rfl) ⟨898431, by rfl⟩ : syracuseStep 2395817 = 1796863) B1796863
theorem B3587327 : Blo 706319 3587327 := bstep (se 1 (by rfl) ⟨2690495, by rfl⟩ : syracuseStep 3587327 = 5380991) B5380991
theorem B5105551 : Blo 706319 5105551 := bstep (se 1 (by rfl) ⟨3829163, by rfl⟩ : syracuseStep 5105551 = 7658327) B7658327
theorem B1597211 : Blo 706319 1597211 := bstep (se 1 (by rfl) ⟨1197908, by rfl⟩ : syracuseStep 1597211 = 2395817) B2395817
theorem B6807401 : Blo 706319 6807401 := bstep (se 2 (by rfl) ⟨2552775, by rfl⟩ : syracuseStep 6807401 = 5105551) B5105551
theorem B2391551 : Blo 706319 2391551 := bstep (se 1 (by rfl) ⟨1793663, by rfl⟩ : syracuseStep 2391551 = 3587327) B3587327
theorem B1064807 : Blo 706319 1064807 := bstep (se 1 (by rfl) ⟨798605, by rfl⟩ : syracuseStep 1064807 = 1597211) B1597211
theorem B4538267 : Blo 706319 4538267 := bstep (se 1 (by rfl) ⟨3403700, by rfl⟩ : syracuseStep 4538267 = 6807401) B6807401
theorem B1594367 : Blo 706319 1594367 := bstep (se 1 (by rfl) ⟨1195775, by rfl⟩ : syracuseStep 1594367 = 2391551) B2391551
theorem B3025511 : Blo 706319 3025511 := bstep (se 1 (by rfl) ⟨2269133, by rfl⟩ : syracuseStep 3025511 = 4538267) B4538267
theorem B1062911 : Blo 706319 1062911 := bstep (se 1 (by rfl) ⟨797183, by rfl⟩ : syracuseStep 1062911 = 1594367) B1594367
theorem B709871 : Blo 706319 709871 := bstep (se 1 (by rfl) ⟨532403, by rfl⟩ : syracuseStep 709871 = 1064807) B1064807
theorem B2017007 : Blo 706319 2017007 := bstep (se 1 (by rfl) ⟨1512755, by rfl⟩ : syracuseStep 2017007 = 3025511) B3025511
theorem B708607 : Blo 706319 708607 := bstep (se 1 (by rfl) ⟨531455, by rfl⟩ : syracuseStep 708607 = 1062911) B1062911
theorem B1344671 : Blo 706319 1344671 := bstep (se 1 (by rfl) ⟨1008503, by rfl⟩ : syracuseStep 1344671 = 2017007) B2017007
theorem B896447 : Blo 706319 896447 := bstep (se 1 (by rfl) ⟨672335, by rfl⟩ : syracuseStep 896447 = 1344671) B1344671
theorem B2390525 : Blo 706319 2390525 := bstep (se 3 (by rfl) ⟨448223, by rfl⟩ : syracuseStep 2390525 = 896447) B896447
theorem B1593683 : Blo 706319 1593683 := bstep (se 1 (by rfl) ⟨1195262, by rfl⟩ : syracuseStep 1593683 = 2390525) B2390525
theorem B1062455 : Blo 706319 1062455 := bstep (se 1 (by rfl) ⟨796841, by rfl⟩ : syracuseStep 1062455 = 1593683) B1593683
theorem B708303 : Blo 706319 708303 := bstep (se 1 (by rfl) ⟨531227, by rfl⟩ : syracuseStep 708303 = 1062455) B1062455

theorem C0 (j : ℕ) (h1 : 176579 ≤ j) (h2 : j ≤ 177278) : Blo 706319 (4 * j + 3) := by
  interval_cases j
  · exact B706319
  · exact B706323
  · exact B706327
  · exact B706331
  · exact B706335
  · exact B706339
  · exact B706343
  · exact B706347
  · exact B706351
  · exact B706355
  · exact B706359
  · exact B706363
  · exact B706367
  · exact B706371
  · exact B706375
  · exact B706379
  · exact B706383
  · exact B706387
  · exact B706391
  · exact B706395
  · exact B706399
  · exact B706403
  · exact B706407
  · exact B706411
  · exact B706415
  · exact B706419
  · exact B706423
  · exact B706427
  · exact B706431
  · exact B706435
  · exact B706439
  · exact B706443
  · exact B706447
  · exact B706451
  · exact B706455
  · exact B706459
  · exact B706463
  · exact B706467
  · exact B706471
  · exact B706475
  · exact B706479
  · exact B706483
  · exact B706487
  · exact B706491
  · exact B706495
  · exact B706499
  · exact B706503
  · exact B706507
  · exact B706511
  · exact B706515
  · exact B706519
  · exact B706523
  · exact B706527
  · exact B706531
  · exact B706535
  · exact B706539
  · exact B706543
  · exact B706547
  · exact B706551
  · exact B706555
  · exact B706559
  · exact B706563
  · exact B706567
  · exact B706571
  · exact B706575
  · exact B706579
  · exact B706583
  · exact B706587
  · exact B706591
  · exact B706595
  · exact B706599
  · exact B706603
  · exact B706607
  · exact B706611
  · exact B706615
  · exact B706619
  · exact B706623
  · exact B706627
  · exact B706631
  · exact B706635
  · exact B706639
  · exact B706643
  · exact B706647
  · exact B706651
  · exact B706655
  · exact B706659
  · exact B706663
  · exact B706667
  · exact B706671
  · exact B706675
  · exact B706679
  · exact B706683
  · exact B706687
  · exact B706691
  · exact B706695
  · exact B706699
  · exact B706703
  · exact B706707
  · exact B706711
  · exact B706715
  · exact B706719
  · exact B706723
  · exact B706727
  · exact B706731
  · exact B706735
  · exact B706739
  · exact B706743
  · exact B706747
  · exact B706751
  · exact B706755
  · exact B706759
  · exact B706763
  · exact B706767
  · exact B706771
  · exact B706775
  · exact B706779
  · exact B706783
  · exact B706787
  · exact B706791
  · exact B706795
  · exact B706799
  · exact B706803
  · exact B706807
  · exact B706811
  · exact B706815
  · exact B706819
  · exact B706823
  · exact B706827
  · exact B706831
  · exact B706835
  · exact B706839
  · exact B706843
  · exact B706847
  · exact B706851
  · exact B706855
  · exact B706859
  · exact B706863
  · exact B706867
  · exact B706871
  · exact B706875
  · exact B706879
  · exact B706883
  · exact B706887
  · exact B706891
  · exact B706895
  · exact B706899
  · exact B706903
  · exact B706907
  · exact B706911
  · exact B706915
  · exact B706919
  · exact B706923
  · exact B706927
  · exact B706931
  · exact B706935
  · exact B706939
  · exact B706943
  · exact B706947
  · exact B706951
  · exact B706955
  · exact B706959
  · exact B706963
  · exact B706967
  · exact B706971
  · exact B706975
  · exact B706979
  · exact B706983
  · exact B706987
  · exact B706991
  · exact B706995
  · exact B706999
  · exact B707003
  · exact B707007
  · exact B707011
  · exact B707015
  · exact B707019
  · exact B707023
  · exact B707027
  · exact B707031
  · exact B707035
  · exact B707039
  · exact B707043
  · exact B707047
  · exact B707051
  · exact B707055
  · exact B707059
  · exact B707063
  · exact B707067
  · exact B707071
  · exact B707075
  · exact B707079
  · exact B707083
  · exact B707087
  · exact B707091
  · exact B707095
  · exact B707099
  · exact B707103
  · exact B707107
  · exact B707111
  · exact B707115
  · exact B707119
  · exact B707123
  · exact B707127
  · exact B707131
  · exact B707135
  · exact B707139
  · exact B707143
  · exact B707147
  · exact B707151
  · exact B707155
  · exact B707159
  · exact B707163
  · exact B707167
  · exact B707171
  · exact B707175
  · exact B707179
  · exact B707183
  · exact B707187
  · exact B707191
  · exact B707195
  · exact B707199
  · exact B707203
  · exact B707207
  · exact B707211
  · exact B707215
  · exact B707219
  · exact B707223
  · exact B707227
  · exact B707231
  · exact B707235
  · exact B707239
  · exact B707243
  · exact B707247
  · exact B707251
  · exact B707255
  · exact B707259
  · exact B707263
  · exact B707267
  · exact B707271
  · exact B707275
  · exact B707279
  · exact B707283
  · exact B707287
  · exact B707291
  · exact B707295
  · exact B707299
  · exact B707303
  · exact B707307
  · exact B707311
  · exact B707315
  · exact B707319
  · exact B707323
  · exact B707327
  · exact B707331
  · exact B707335
  · exact B707339
  · exact B707343
  · exact B707347
  · exact B707351
  · exact B707355
  · exact B707359
  · exact B707363
  · exact B707367
  · exact B707371
  · exact B707375
  · exact B707379
  · exact B707383
  · exact B707387
  · exact B707391
  · exact B707395
  · exact B707399
  · exact B707403
  · exact B707407
  · exact B707411
  · exact B707415
  · exact B707419
  · exact B707423
  · exact B707427
  · exact B707431
  · exact B707435
  · exact B707439
  · exact B707443
  · exact B707447
  · exact B707451
  · exact B707455
  · exact B707459
  · exact B707463
  · exact B707467
  · exact B707471
  · exact B707475
  · exact B707479
  · exact B707483
  · exact B707487
  · exact B707491
  · exact B707495
  · exact B707499
  · exact B707503
  · exact B707507
  · exact B707511
  · exact B707515
  · exact B707519
  · exact B707523
  · exact B707527
  · exact B707531
  · exact B707535
  · exact B707539
  · exact B707543
  · exact B707547
  · exact B707551
  · exact B707555
  · exact B707559
  · exact B707563
  · exact B707567
  · exact B707571
  · exact B707575
  · exact B707579
  · exact B707583
  · exact B707587
  · exact B707591
  · exact B707595
  · exact B707599
  · exact B707603
  · exact B707607
  · exact B707611
  · exact B707615
  · exact B707619
  · exact B707623
  · exact B707627
  · exact B707631
  · exact B707635
  · exact B707639
  · exact B707643
  · exact B707647
  · exact B707651
  · exact B707655
  · exact B707659
  · exact B707663
  · exact B707667
  · exact B707671
  · exact B707675
  · exact B707679
  · exact B707683
  · exact B707687
  · exact B707691
  · exact B707695
  · exact B707699
  · exact B707703
  · exact B707707
  · exact B707711
  · exact B707715
  · exact B707719
  · exact B707723
  · exact B707727
  · exact B707731
  · exact B707735
  · exact B707739
  · exact B707743
  · exact B707747
  · exact B707751
  · exact B707755
  · exact B707759
  · exact B707763
  · exact B707767
  · exact B707771
  · exact B707775
  · exact B707779
  · exact B707783
  · exact B707787
  · exact B707791
  · exact B707795
  · exact B707799
  · exact B707803
  · exact B707807
  · exact B707811
  · exact B707815
  · exact B707819
  · exact B707823
  · exact B707827
  · exact B707831
  · exact B707835
  · exact B707839
  · exact B707843
  · exact B707847
  · exact B707851
  · exact B707855
  · exact B707859
  · exact B707863
  · exact B707867
  · exact B707871
  · exact B707875
  · exact B707879
  · exact B707883
  · exact B707887
  · exact B707891
  · exact B707895
  · exact B707899
  · exact B707903
  · exact B707907
  · exact B707911
  · exact B707915
  · exact B707919
  · exact B707923
  · exact B707927
  · exact B707931
  · exact B707935
  · exact B707939
  · exact B707943
  · exact B707947
  · exact B707951
  · exact B707955
  · exact B707959
  · exact B707963
  · exact B707967
  · exact B707971
  · exact B707975
  · exact B707979
  · exact B707983
  · exact B707987
  · exact B707991
  · exact B707995
  · exact B707999
  · exact B708003
  · exact B708007
  · exact B708011
  · exact B708015
  · exact B708019
  · exact B708023
  · exact B708027
  · exact B708031
  · exact B708035
  · exact B708039
  · exact B708043
  · exact B708047
  · exact B708051
  · exact B708055
  · exact B708059
  · exact B708063
  · exact B708067
  · exact B708071
  · exact B708075
  · exact B708079
  · exact B708083
  · exact B708087
  · exact B708091
  · exact B708095
  · exact B708099
  · exact B708103
  · exact B708107
  · exact B708111
  · exact B708115
  · exact B708119
  · exact B708123
  · exact B708127
  · exact B708131
  · exact B708135
  · exact B708139
  · exact B708143
  · exact B708147
  · exact B708151
  · exact B708155
  · exact B708159
  · exact B708163
  · exact B708167
  · exact B708171
  · exact B708175
  · exact B708179
  · exact B708183
  · exact B708187
  · exact B708191
  · exact B708195
  · exact B708199
  · exact B708203
  · exact B708207
  · exact B708211
  · exact B708215
  · exact B708219
  · exact B708223
  · exact B708227
  · exact B708231
  · exact B708235
  · exact B708239
  · exact B708243
  · exact B708247
  · exact B708251
  · exact B708255
  · exact B708259
  · exact B708263
  · exact B708267
  · exact B708271
  · exact B708275
  · exact B708279
  · exact B708283
  · exact B708287
  · exact B708291
  · exact B708295
  · exact B708299
  · exact B708303
  · exact B708307
  · exact B708311
  · exact B708315
  · exact B708319
  · exact B708323
  · exact B708327
  · exact B708331
  · exact B708335
  · exact B708339
  · exact B708343
  · exact B708347
  · exact B708351
  · exact B708355
  · exact B708359
  · exact B708363
  · exact B708367
  · exact B708371
  · exact B708375
  · exact B708379
  · exact B708383
  · exact B708387
  · exact B708391
  · exact B708395
  · exact B708399
  · exact B708403
  · exact B708407
  · exact B708411
  · exact B708415
  · exact B708419
  · exact B708423
  · exact B708427
  · exact B708431
  · exact B708435
  · exact B708439
  · exact B708443
  · exact B708447
  · exact B708451
  · exact B708455
  · exact B708459
  · exact B708463
  · exact B708467
  · exact B708471
  · exact B708475
  · exact B708479
  · exact B708483
  · exact B708487
  · exact B708491
  · exact B708495
  · exact B708499
  · exact B708503
  · exact B708507
  · exact B708511
  · exact B708515
  · exact B708519
  · exact B708523
  · exact B708527
  · exact B708531
  · exact B708535
  · exact B708539
  · exact B708543
  · exact B708547
  · exact B708551
  · exact B708555
  · exact B708559
  · exact B708563
  · exact B708567
  · exact B708571
  · exact B708575
  · exact B708579
  · exact B708583
  · exact B708587
  · exact B708591
  · exact B708595
  · exact B708599
  · exact B708603
  · exact B708607
  · exact B708611
  · exact B708615
  · exact B708619
  · exact B708623
  · exact B708627
  · exact B708631
  · exact B708635
  · exact B708639
  · exact B708643
  · exact B708647
  · exact B708651
  · exact B708655
  · exact B708659
  · exact B708663
  · exact B708667
  · exact B708671
  · exact B708675
  · exact B708679
  · exact B708683
  · exact B708687
  · exact B708691
  · exact B708695
  · exact B708699
  · exact B708703
  · exact B708707
  · exact B708711
  · exact B708715
  · exact B708719
  · exact B708723
  · exact B708727
  · exact B708731
  · exact B708735
  · exact B708739
  · exact B708743
  · exact B708747
  · exact B708751
  · exact B708755
  · exact B708759
  · exact B708763
  · exact B708767
  · exact B708771
  · exact B708775
  · exact B708779
  · exact B708783
  · exact B708787
  · exact B708791
  · exact B708795
  · exact B708799
  · exact B708803
  · exact B708807
  · exact B708811
  · exact B708815
  · exact B708819
  · exact B708823
  · exact B708827
  · exact B708831
  · exact B708835
  · exact B708839
  · exact B708843
  · exact B708847
  · exact B708851
  · exact B708855
  · exact B708859
  · exact B708863
  · exact B708867
  · exact B708871
  · exact B708875
  · exact B708879
  · exact B708883
  · exact B708887
  · exact B708891
  · exact B708895
  · exact B708899
  · exact B708903
  · exact B708907
  · exact B708911
  · exact B708915
  · exact B708919
  · exact B708923
  · exact B708927
  · exact B708931
  · exact B708935
  · exact B708939
  · exact B708943
  · exact B708947
  · exact B708951
  · exact B708955
  · exact B708959
  · exact B708963
  · exact B708967
  · exact B708971
  · exact B708975
  · exact B708979
  · exact B708983
  · exact B708987
  · exact B708991
  · exact B708995
  · exact B708999
  · exact B709003
  · exact B709007
  · exact B709011
  · exact B709015
  · exact B709019
  · exact B709023
  · exact B709027
  · exact B709031
  · exact B709035
  · exact B709039
  · exact B709043
  · exact B709047
  · exact B709051
  · exact B709055
  · exact B709059
  · exact B709063
  · exact B709067
  · exact B709071
  · exact B709075
  · exact B709079
  · exact B709083
  · exact B709087
  · exact B709091
  · exact B709095
  · exact B709099
  · exact B709103
  · exact B709107
  · exact B709111
  · exact B709115

theorem C1 (j : ℕ) (h1 : 177279 ≤ j) (h2 : j ≤ 177579) : Blo 706319 (4 * j + 3) := by
  interval_cases j
  · exact B709119
  · exact B709123
  · exact B709127
  · exact B709131
  · exact B709135
  · exact B709139
  · exact B709143
  · exact B709147
  · exact B709151
  · exact B709155
  · exact B709159
  · exact B709163
  · exact B709167
  · exact B709171
  · exact B709175
  · exact B709179
  · exact B709183
  · exact B709187
  · exact B709191
  · exact B709195
  · exact B709199
  · exact B709203
  · exact B709207
  · exact B709211
  · exact B709215
  · exact B709219
  · exact B709223
  · exact B709227
  · exact B709231
  · exact B709235
  · exact B709239
  · exact B709243
  · exact B709247
  · exact B709251
  · exact B709255
  · exact B709259
  · exact B709263
  · exact B709267
  · exact B709271
  · exact B709275
  · exact B709279
  · exact B709283
  · exact B709287
  · exact B709291
  · exact B709295
  · exact B709299
  · exact B709303
  · exact B709307
  · exact B709311
  · exact B709315
  · exact B709319
  · exact B709323
  · exact B709327
  · exact B709331
  · exact B709335
  · exact B709339
  · exact B709343
  · exact B709347
  · exact B709351
  · exact B709355
  · exact B709359
  · exact B709363
  · exact B709367
  · exact B709371
  · exact B709375
  · exact B709379
  · exact B709383
  · exact B709387
  · exact B709391
  · exact B709395
  · exact B709399
  · exact B709403
  · exact B709407
  · exact B709411
  · exact B709415
  · exact B709419
  · exact B709423
  · exact B709427
  · exact B709431
  · exact B709435
  · exact B709439
  · exact B709443
  · exact B709447
  · exact B709451
  · exact B709455
  · exact B709459
  · exact B709463
  · exact B709467
  · exact B709471
  · exact B709475
  · exact B709479
  · exact B709483
  · exact B709487
  · exact B709491
  · exact B709495
  · exact B709499
  · exact B709503
  · exact B709507
  · exact B709511
  · exact B709515
  · exact B709519
  · exact B709523
  · exact B709527
  · exact B709531
  · exact B709535
  · exact B709539
  · exact B709543
  · exact B709547
  · exact B709551
  · exact B709555
  · exact B709559
  · exact B709563
  · exact B709567
  · exact B709571
  · exact B709575
  · exact B709579
  · exact B709583
  · exact B709587
  · exact B709591
  · exact B709595
  · exact B709599
  · exact B709603
  · exact B709607
  · exact B709611
  · exact B709615
  · exact B709619
  · exact B709623
  · exact B709627
  · exact B709631
  · exact B709635
  · exact B709639
  · exact B709643
  · exact B709647
  · exact B709651
  · exact B709655
  · exact B709659
  · exact B709663
  · exact B709667
  · exact B709671
  · exact B709675
  · exact B709679
  · exact B709683
  · exact B709687
  · exact B709691
  · exact B709695
  · exact B709699
  · exact B709703
  · exact B709707
  · exact B709711
  · exact B709715
  · exact B709719
  · exact B709723
  · exact B709727
  · exact B709731
  · exact B709735
  · exact B709739
  · exact B709743
  · exact B709747
  · exact B709751
  · exact B709755
  · exact B709759
  · exact B709763
  · exact B709767
  · exact B709771
  · exact B709775
  · exact B709779
  · exact B709783
  · exact B709787
  · exact B709791
  · exact B709795
  · exact B709799
  · exact B709803
  · exact B709807
  · exact B709811
  · exact B709815
  · exact B709819
  · exact B709823
  · exact B709827
  · exact B709831
  · exact B709835
  · exact B709839
  · exact B709843
  · exact B709847
  · exact B709851
  · exact B709855
  · exact B709859
  · exact B709863
  · exact B709867
  · exact B709871
  · exact B709875
  · exact B709879
  · exact B709883
  · exact B709887
  · exact B709891
  · exact B709895
  · exact B709899
  · exact B709903
  · exact B709907
  · exact B709911
  · exact B709915
  · exact B709919
  · exact B709923
  · exact B709927
  · exact B709931
  · exact B709935
  · exact B709939
  · exact B709943
  · exact B709947
  · exact B709951
  · exact B709955
  · exact B709959
  · exact B709963
  · exact B709967
  · exact B709971
  · exact B709975
  · exact B709979
  · exact B709983
  · exact B709987
  · exact B709991
  · exact B709995
  · exact B709999
  · exact B710003
  · exact B710007
  · exact B710011
  · exact B710015
  · exact B710019
  · exact B710023
  · exact B710027
  · exact B710031
  · exact B710035
  · exact B710039
  · exact B710043
  · exact B710047
  · exact B710051
  · exact B710055
  · exact B710059
  · exact B710063
  · exact B710067
  · exact B710071
  · exact B710075
  · exact B710079
  · exact B710083
  · exact B710087
  · exact B710091
  · exact B710095
  · exact B710099
  · exact B710103
  · exact B710107
  · exact B710111
  · exact B710115
  · exact B710119
  · exact B710123
  · exact B710127
  · exact B710131
  · exact B710135
  · exact B710139
  · exact B710143
  · exact B710147
  · exact B710151
  · exact B710155
  · exact B710159
  · exact B710163
  · exact B710167
  · exact B710171
  · exact B710175
  · exact B710179
  · exact B710183
  · exact B710187
  · exact B710191
  · exact B710195
  · exact B710199
  · exact B710203
  · exact B710207
  · exact B710211
  · exact B710215
  · exact B710219
  · exact B710223
  · exact B710227
  · exact B710231
  · exact B710235
  · exact B710239
  · exact B710243
  · exact B710247
  · exact B710251
  · exact B710255
  · exact B710259
  · exact B710263
  · exact B710267
  · exact B710271
  · exact B710275
  · exact B710279
  · exact B710283
  · exact B710287
  · exact B710291
  · exact B710295
  · exact B710299
  · exact B710303
  · exact B710307
  · exact B710311
  · exact B710315
  · exact B710319

theorem solution (m : ℕ) (hlo : 706319 ≤ m) (hhi : m ≤ 710319) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 176579 ≤ j := by omega
    have hj2 : j ≤ 177579 := by omega
    have hb : Blo 706319 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 177279 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
