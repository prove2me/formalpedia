-- Prove2me | solution 1 for syracuse_descends_range_662308_666308
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:50.493921+00:00
-- url     : https://prove2.me/submissions/588572cf-fc61-47d9-b1b0-cee4baa35093

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


theorem B2523221 : Blo 662308 2523221 := bbase (se 8 (by rfl) ⟨14784, by rfl⟩ : syracuseStep 2523221 = 29569) (by norm_num)
theorem B2162933 : Blo 662308 2162933 := bbase (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) (by norm_num)
theorem B819677 : Blo 662308 819677 := bbase (se 3 (by rfl) ⟨153689, by rfl⟩ : syracuseStep 819677 = 307379) (by norm_num)
theorem B2130533 : Blo 662308 2130533 := bbase (se 4 (by rfl) ⟨199737, by rfl⟩ : syracuseStep 2130533 = 399475) (by norm_num)
theorem B1344109 : Blo 662308 1344109 := bbase (se 3 (by rfl) ⟨252020, by rfl⟩ : syracuseStep 1344109 = 504041) (by norm_num)
theorem B5374613 : Blo 662308 5374613 := bbase (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) (by norm_num)
theorem B2687957 : Blo 662308 2687957 := bbase (se 7 (by rfl) ⟨31499, by rfl⟩ : syracuseStep 2687957 = 62999) (by norm_num)
theorem B2688085 : Blo 662308 2688085 := bbase (se 8 (by rfl) ⟨15750, by rfl⟩ : syracuseStep 2688085 = 31501) (by norm_num)
theorem B2884805 : Blo 662308 2884805 := bbase (se 4 (by rfl) ⟨270450, by rfl⟩ : syracuseStep 2884805 = 540901) (by norm_num)
theorem B2524405 : Blo 662308 2524405 := bbase (se 5 (by rfl) ⟨118331, by rfl⟩ : syracuseStep 2524405 = 236663) (by norm_num)
theorem B853237 : Blo 662308 853237 := bbase (se 5 (by rfl) ⟨39995, by rfl⟩ : syracuseStep 853237 = 79991) (by norm_num)
theorem B10225045 : Blo 662308 10225045 := bbase (se 6 (by rfl) ⟨239649, by rfl⟩ : syracuseStep 10225045 = 479299) (by norm_num)
theorem B2131429 : Blo 662308 2131429 := bbase (se 4 (by rfl) ⟨199821, by rfl⟩ : syracuseStep 2131429 = 399643) (by norm_num)
theorem B2524709 : Blo 662308 2524709 := bbase (se 4 (by rfl) ⟨236691, by rfl⟩ : syracuseStep 2524709 = 473383) (by norm_num)
theorem B788077 : Blo 662308 788077 := bbase (se 3 (by rfl) ⟨147764, by rfl⟩ : syracuseStep 788077 = 295529) (by norm_num)
theorem B7669525 : Blo 662308 7669525 := bbase (se 6 (by rfl) ⟨179754, by rfl⟩ : syracuseStep 7669525 = 359509) (by norm_num)
theorem B7767893 : Blo 662308 7767893 := bbase (se 9 (by rfl) ⟨22757, by rfl⟩ : syracuseStep 7767893 = 45515) (by norm_num)
theorem B2427029 : Blo 662308 2427029 := bbase (se 6 (by rfl) ⟨56883, by rfl⟩ : syracuseStep 2427029 = 113767) (by norm_num)
theorem B8063189 : Blo 662308 8063189 := bbase (se 7 (by rfl) ⟨94490, by rfl⟩ : syracuseStep 8063189 = 188981) (by norm_num)
theorem B1149149 : Blo 662308 1149149 := bbase (se 3 (by rfl) ⟨215465, by rfl⟩ : syracuseStep 1149149 = 430931) (by norm_num)
theorem B1706309 : Blo 662308 1706309 := bbase (se 4 (by rfl) ⟨159966, by rfl⟩ : syracuseStep 1706309 = 319933) (by norm_num)
theorem B1345877 : Blo 662308 1345877 := bbase (se 10 (by rfl) ⟨1971, by rfl⟩ : syracuseStep 1345877 = 3943) (by norm_num)
theorem B2394485 : Blo 662308 2394485 := bbase (se 5 (by rfl) ⟨112241, by rfl⟩ : syracuseStep 2394485 = 224483) (by norm_num)
theorem B756097 : Blo 662308 756097 := bbase (se 2 (by rfl) ⟨283536, by rfl⟩ : syracuseStep 756097 = 567073) (by norm_num)
theorem B854797 : Blo 662308 854797 := bbase (se 3 (by rfl) ⟨160274, by rfl⟩ : syracuseStep 854797 = 320549) (by norm_num)
theorem B1706885 : Blo 662308 1706885 := bbase (se 4 (by rfl) ⟨160020, by rfl⟩ : syracuseStep 1706885 = 320041) (by norm_num)
theorem B1117685 : Blo 662308 1117685 := bbase (se 5 (by rfl) ⟨52391, by rfl⟩ : syracuseStep 1117685 = 104783) (by norm_num)
theorem B2395637 : Blo 662308 2395637 := bbase (se 5 (by rfl) ⟨112295, by rfl⟩ : syracuseStep 2395637 = 224591) (by norm_num)
theorem B2526821 : Blo 662308 2526821 := bbase (se 4 (by rfl) ⟨236889, by rfl⟩ : syracuseStep 2526821 = 473779) (by norm_num)
theorem B1117813 : Blo 662308 1117813 := bbase (se 5 (by rfl) ⟨52397, by rfl⟩ : syracuseStep 1117813 = 104795) (by norm_num)
theorem B1117901 : Blo 662308 1117901 := bbase (se 3 (by rfl) ⟨209606, by rfl⟩ : syracuseStep 1117901 = 419213) (by norm_num)
theorem B1118029 : Blo 662308 1118029 := bbase (se 3 (by rfl) ⟨209630, by rfl⟩ : syracuseStep 1118029 = 419261) (by norm_num)
theorem B2527109 : Blo 662308 2527109 := bbase (se 4 (by rfl) ⟨236916, by rfl⟩ : syracuseStep 2527109 = 473833) (by norm_num)
theorem B1118117 : Blo 662308 1118117 := bbase (se 4 (by rfl) ⟨104823, by rfl⟩ : syracuseStep 1118117 = 209647) (by norm_num)
theorem B11341781 : Blo 662308 11341781 := bbase (se 7 (by rfl) ⟨132911, by rfl⟩ : syracuseStep 11341781 = 265823) (by norm_num)
theorem B1118245 : Blo 662308 1118245 := bbase (se 4 (by rfl) ⟨104835, by rfl⟩ : syracuseStep 1118245 = 209671) (by norm_num)
theorem B1118333 : Blo 662308 1118333 := bbase (se 3 (by rfl) ⟨209687, by rfl⟩ : syracuseStep 1118333 = 419375) (by norm_num)
theorem B1347773 : Blo 662308 1347773 := bbase (se 3 (by rfl) ⟨252707, by rfl⟩ : syracuseStep 1347773 = 505415) (by norm_num)
theorem B1118461 : Blo 662308 1118461 := bbase (se 3 (by rfl) ⟨209711, by rfl⟩ : syracuseStep 1118461 = 419423) (by norm_num)
theorem B2298133 : Blo 662308 2298133 := bbase (se 6 (by rfl) ⟨53862, by rfl⟩ : syracuseStep 2298133 = 107725) (by norm_num)
theorem B2134325 : Blo 662308 2134325 := bbase (se 5 (by rfl) ⟨100046, by rfl⟩ : syracuseStep 2134325 = 200093) (by norm_num)
theorem B3772757 : Blo 662308 3772757 := bbase (se 10 (by rfl) ⟨5526, by rfl⟩ : syracuseStep 3772757 = 11053) (by norm_num)
theorem B1118549 : Blo 662308 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B5476693 : Blo 662308 5476693 := bbase (se 10 (by rfl) ⟨8022, by rfl⟩ : syracuseStep 5476693 = 16045) (by norm_num)
theorem B1118677 : Blo 662308 1118677 := bbase (se 7 (by rfl) ⟨13109, by rfl⟩ : syracuseStep 1118677 = 26219) (by norm_num)
theorem B1118765 : Blo 662308 1118765 := bbase (se 3 (by rfl) ⟨209768, by rfl⟩ : syracuseStep 1118765 = 419537) (by norm_num)
theorem B5050997 : Blo 662308 5050997 := bbase (se 5 (by rfl) ⟨236765, by rfl⟩ : syracuseStep 5050997 = 473531) (by norm_num)
theorem B987781 : Blo 662308 987781 := bbase (se 4 (by rfl) ⟨92604, by rfl⟩ : syracuseStep 987781 = 185209) (by norm_num)
theorem B1118893 : Blo 662308 1118893 := bbase (se 3 (by rfl) ⟨209792, by rfl⟩ : syracuseStep 1118893 = 419585) (by norm_num)
theorem B1118981 : Blo 662308 1118981 := bbase (se 4 (by rfl) ⟨104904, by rfl⟩ : syracuseStep 1118981 = 209809) (by norm_num)
theorem B1119109 : Blo 662308 1119109 := bbase (se 4 (by rfl) ⟨104916, by rfl⟩ : syracuseStep 1119109 = 209833) (by norm_num)
theorem B1119197 : Blo 662308 1119197 := bbase (se 3 (by rfl) ⟨209849, by rfl⟩ : syracuseStep 1119197 = 419699) (by norm_num)
theorem B2528293 : Blo 662308 2528293 := bbase (se 4 (by rfl) ⟨237027, by rfl⟩ : syracuseStep 2528293 = 474055) (by norm_num)
theorem B1119325 : Blo 662308 1119325 := bbase (se 3 (by rfl) ⟨209873, by rfl⟩ : syracuseStep 1119325 = 419747) (by norm_num)
theorem B1152173 : Blo 662308 1152173 := bbase (se 3 (by rfl) ⟨216032, by rfl⟩ : syracuseStep 1152173 = 432065) (by norm_num)
theorem B1119413 : Blo 662308 1119413 := bbase (se 5 (by rfl) ⟨52472, by rfl⟩ : syracuseStep 1119413 = 104945) (by norm_num)
theorem B1676477 : Blo 662308 1676477 := bbase (se 3 (by rfl) ⟨314339, by rfl⟩ : syracuseStep 1676477 = 628679) (by norm_num)
theorem B2397397 : Blo 662308 2397397 := bbase (se 7 (by rfl) ⟨28094, by rfl⟩ : syracuseStep 2397397 = 56189) (by norm_num)
theorem B759013 : Blo 662308 759013 := bbase (se 4 (by rfl) ⟨71157, by rfl⟩ : syracuseStep 759013 = 142315) (by norm_num)
theorem B922909 : Blo 662308 922909 := bbase (se 3 (by rfl) ⟨173045, by rfl⟩ : syracuseStep 922909 = 346091) (by norm_num)
theorem B1119541 : Blo 662308 1119541 := bbase (se 5 (by rfl) ⟨52478, by rfl⟩ : syracuseStep 1119541 = 104957) (by norm_num)
theorem B2528597 : Blo 662308 2528597 := bbase (se 14 (by rfl) ⟨231, by rfl⟩ : syracuseStep 2528597 = 463) (by norm_num)
theorem B759145 : Blo 662308 759145 := bbase (se 2 (by rfl) ⟨284679, by rfl⟩ : syracuseStep 759145 = 569359) (by norm_num)
theorem B1709429 : Blo 662308 1709429 := bbase (se 5 (by rfl) ⟨80129, by rfl⟩ : syracuseStep 1709429 = 160259) (by norm_num)
theorem B1119629 : Blo 662308 1119629 := bbase (se 3 (by rfl) ⟨209930, by rfl⟩ : syracuseStep 1119629 = 419861) (by norm_num)
theorem B1414597 : Blo 662308 1414597 := bbase (se 4 (by rfl) ⟨132618, by rfl⟩ : syracuseStep 1414597 = 265237) (by norm_num)
theorem B759305 : Blo 662308 759305 := bbase (se 2 (by rfl) ⟨284739, by rfl⟩ : syracuseStep 759305 = 569479) (by norm_num)
theorem B1119757 : Blo 662308 1119757 := bbase (se 3 (by rfl) ⟨209954, by rfl⟩ : syracuseStep 1119757 = 419909) (by norm_num)
theorem B1676821 : Blo 662308 1676821 := bbase (se 6 (by rfl) ⟨39300, by rfl⟩ : syracuseStep 1676821 = 78601) (by norm_num)
theorem B2692693 : Blo 662308 2692693 := bbase (se 8 (by rfl) ⟨15777, by rfl⟩ : syracuseStep 2692693 = 31555) (by norm_num)
theorem B1119845 : Blo 662308 1119845 := bbase (se 4 (by rfl) ⟨104985, by rfl⟩ : syracuseStep 1119845 = 209971) (by norm_num)
theorem B1676933 : Blo 662308 1676933 := bbase (se 4 (by rfl) ⟨157212, by rfl⟩ : syracuseStep 1676933 = 314425) (by norm_num)
theorem B1119973 : Blo 662308 1119973 := bbase (se 4 (by rfl) ⟨104997, by rfl⟩ : syracuseStep 1119973 = 209995) (by norm_num)
theorem B1120061 : Blo 662308 1120061 := bbase (se 3 (by rfl) ⟨210011, by rfl⟩ : syracuseStep 1120061 = 420023) (by norm_num)
theorem B1677125 : Blo 662308 1677125 := bbase (se 4 (by rfl) ⟨157230, by rfl⟩ : syracuseStep 1677125 = 314461) (by norm_num)
theorem B1120189 : Blo 662308 1120189 := bbase (se 3 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 1120189 = 420071) (by norm_num)
theorem B1120277 : Blo 662308 1120277 := bbase (se 6 (by rfl) ⟨26256, by rfl⟩ : syracuseStep 1120277 = 52513) (by norm_num)
theorem B1120405 : Blo 662308 1120405 := bbase (se 6 (by rfl) ⟨26259, by rfl⟩ : syracuseStep 1120405 = 52519) (by norm_num)
theorem B1677469 : Blo 662308 1677469 := bbase (se 3 (by rfl) ⟨314525, by rfl⟩ : syracuseStep 1677469 = 629051) (by norm_num)
theorem B2398405 : Blo 662308 2398405 := bbase (se 4 (by rfl) ⟨224850, by rfl⟩ : syracuseStep 2398405 = 449701) (by norm_num)
theorem B1120493 : Blo 662308 1120493 := bbase (se 3 (by rfl) ⟨210092, by rfl⟩ : syracuseStep 1120493 = 420185) (by norm_num)
theorem B1677581 : Blo 662308 1677581 := bbase (se 3 (by rfl) ⟨314546, by rfl⟩ : syracuseStep 1677581 = 629093) (by norm_num)
theorem B1415485 : Blo 662308 1415485 := bbase (se 3 (by rfl) ⟨265403, by rfl⟩ : syracuseStep 1415485 = 530807) (by norm_num)
theorem B1120621 : Blo 662308 1120621 := bbase (se 3 (by rfl) ⟨210116, by rfl⟩ : syracuseStep 1120621 = 420233) (by norm_num)
theorem B1350029 : Blo 662308 1350029 := bbase (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) (by norm_num)
theorem B1120709 : Blo 662308 1120709 := bbase (se 4 (by rfl) ⟨105066, by rfl⟩ : syracuseStep 1120709 = 210133) (by norm_num)
theorem B1677773 : Blo 662308 1677773 := bbase (se 3 (by rfl) ⟨314582, by rfl⟩ : syracuseStep 1677773 = 629165) (by norm_num)
theorem B3185189 : Blo 662308 3185189 := bbase (se 4 (by rfl) ⟨298611, by rfl⟩ : syracuseStep 3185189 = 597223) (by norm_num)
theorem B1120837 : Blo 662308 1120837 := bbase (se 4 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 1120837 = 210157) (by norm_num)
theorem B1120925 : Blo 662308 1120925 := bbase (se 3 (by rfl) ⟨210173, by rfl⟩ : syracuseStep 1120925 = 420347) (by norm_num)
theorem B1121053 : Blo 662308 1121053 := bbase (se 3 (by rfl) ⟨210197, by rfl⟩ : syracuseStep 1121053 = 420395) (by norm_num)
theorem B1678117 : Blo 662308 1678117 := bbase (se 4 (by rfl) ⟨157323, by rfl⟩ : syracuseStep 1678117 = 314647) (by norm_num)
theorem B1415981 : Blo 662308 1415981 := bbase (se 3 (by rfl) ⟨265496, by rfl⟩ : syracuseStep 1415981 = 530993) (by norm_num)
theorem B2693957 : Blo 662308 2693957 := bbase (se 4 (by rfl) ⟨252558, by rfl⟩ : syracuseStep 2693957 = 505117) (by norm_num)
theorem B1121141 : Blo 662308 1121141 := bbase (se 5 (by rfl) ⟨52553, by rfl⟩ : syracuseStep 1121141 = 105107) (by norm_num)
theorem B1678229 : Blo 662308 1678229 := bbase (se 6 (by rfl) ⟨39333, by rfl⟩ : syracuseStep 1678229 = 78667) (by norm_num)
theorem B1350589 : Blo 662308 1350589 := bbase (se 3 (by rfl) ⟨253235, by rfl⟩ : syracuseStep 1350589 = 506471) (by norm_num)
theorem B1514477 : Blo 662308 1514477 := bbase (se 3 (by rfl) ⟨283964, by rfl⟩ : syracuseStep 1514477 = 567929) (by norm_num)
theorem B1121269 : Blo 662308 1121269 := bbase (se 5 (by rfl) ⟨52559, by rfl⟩ : syracuseStep 1121269 = 105119) (by norm_num)
theorem B1121357 : Blo 662308 1121357 := bbase (se 3 (by rfl) ⟨210254, by rfl⟩ : syracuseStep 1121357 = 420509) (by norm_num)
theorem B1678421 : Blo 662308 1678421 := bbase (se 8 (by rfl) ⟨9834, by rfl⟩ : syracuseStep 1678421 = 19669) (by norm_num)
theorem B1121485 : Blo 662308 1121485 := bbase (se 3 (by rfl) ⟨210278, by rfl⟩ : syracuseStep 1121485 = 420557) (by norm_num)
theorem B2235653 : Blo 662308 2235653 := bbase (se 4 (by rfl) ⟨209592, by rfl⟩ : syracuseStep 2235653 = 419185) (by norm_num)
theorem B1121573 : Blo 662308 1121573 := bbase (se 4 (by rfl) ⟨105147, by rfl⟩ : syracuseStep 1121573 = 210295) (by norm_num)
theorem B1121701 : Blo 662308 1121701 := bbase (se 4 (by rfl) ⟨105159, by rfl⟩ : syracuseStep 1121701 = 210319) (by norm_num)
theorem B1678765 : Blo 662308 1678765 := bbase (se 3 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 1678765 = 629537) (by norm_num)
theorem B1121789 : Blo 662308 1121789 := bbase (se 3 (by rfl) ⟨210335, by rfl⟩ : syracuseStep 1121789 = 420671) (by norm_num)
theorem B1678877 : Blo 662308 1678877 := bbase (se 3 (by rfl) ⟨314789, by rfl⟩ : syracuseStep 1678877 = 629579) (by norm_num)
theorem B728617 : Blo 662308 728617 := bbase (se 2 (by rfl) ⟨273231, by rfl⟩ : syracuseStep 728617 = 546463) (by norm_num)
theorem B1121917 : Blo 662308 1121917 := bbase (se 3 (by rfl) ⟨210359, by rfl⟩ : syracuseStep 1121917 = 420719) (by norm_num)
theorem B3186341 : Blo 662308 3186341 := bbase (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) (by norm_num)
theorem B1416869 : Blo 662308 1416869 := bbase (se 4 (by rfl) ⟨132831, by rfl⟩ : syracuseStep 1416869 = 265663) (by norm_num)
theorem B2236085 : Blo 662308 2236085 := bbase (se 5 (by rfl) ⟨104816, by rfl⟩ : syracuseStep 2236085 = 209633) (by norm_num)
theorem B1122005 : Blo 662308 1122005 := bbase (se 7 (by rfl) ⟨13148, by rfl⟩ : syracuseStep 1122005 = 26297) (by norm_num)
theorem B1679069 : Blo 662308 1679069 := bbase (se 3 (by rfl) ⟨314825, by rfl⟩ : syracuseStep 1679069 = 629651) (by norm_num)
theorem B1154837 : Blo 662308 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B1416989 : Blo 662308 1416989 := bbase (se 3 (by rfl) ⟨265685, by rfl⟩ : syracuseStep 1416989 = 531371) (by norm_num)
theorem B4267829 : Blo 662308 4267829 := bbase (se 5 (by rfl) ⟨200054, by rfl⟩ : syracuseStep 4267829 = 400109) (by norm_num)
theorem B1122133 : Blo 662308 1122133 := bbase (se 9 (by rfl) ⟨3287, by rfl⟩ : syracuseStep 1122133 = 6575) (by norm_num)
theorem B1122221 : Blo 662308 1122221 := bbase (se 3 (by rfl) ⟨210416, by rfl⟩ : syracuseStep 1122221 = 420833) (by norm_num)
theorem B1122349 : Blo 662308 1122349 := bbase (se 3 (by rfl) ⟨210440, by rfl⟩ : syracuseStep 1122349 = 420881) (by norm_num)
theorem B1679413 : Blo 662308 1679413 := bbase (se 5 (by rfl) ⟨78722, by rfl⟩ : syracuseStep 1679413 = 157445) (by norm_num)
theorem B2236517 : Blo 662308 2236517 := bbase (se 4 (by rfl) ⟨209673, by rfl⟩ : syracuseStep 2236517 = 419347) (by norm_num)
theorem B1122437 : Blo 662308 1122437 := bbase (se 4 (by rfl) ⟨105228, by rfl⟩ : syracuseStep 1122437 = 210457) (by norm_num)
theorem B1679525 : Blo 662308 1679525 := bbase (se 4 (by rfl) ⟨157455, by rfl⟩ : syracuseStep 1679525 = 314911) (by norm_num)
theorem B1122565 : Blo 662308 1122565 := bbase (se 4 (by rfl) ⟨105240, by rfl⟩ : syracuseStep 1122565 = 210481) (by norm_num)
theorem B1122653 : Blo 662308 1122653 := bbase (se 3 (by rfl) ⟨210497, by rfl⟩ : syracuseStep 1122653 = 420995) (by norm_num)
theorem B1679717 : Blo 662308 1679717 := bbase (se 4 (by rfl) ⟨157473, by rfl⟩ : syracuseStep 1679717 = 314947) (by norm_num)
theorem B1417621 : Blo 662308 1417621 := bbase (se 6 (by rfl) ⟨33225, by rfl⟩ : syracuseStep 1417621 = 66451) (by norm_num)
theorem B3187109 : Blo 662308 3187109 := bbase (se 4 (by rfl) ⟨298791, by rfl⟩ : syracuseStep 3187109 = 597583) (by norm_num)
theorem B1122781 : Blo 662308 1122781 := bbase (se 3 (by rfl) ⟨210521, by rfl⟩ : syracuseStep 1122781 = 421043) (by norm_num)
theorem B2236949 : Blo 662308 2236949 := bbase (se 6 (by rfl) ⟨52428, by rfl⟩ : syracuseStep 2236949 = 104857) (by norm_num)
theorem B1122869 : Blo 662308 1122869 := bbase (se 5 (by rfl) ⟨52634, by rfl⟩ : syracuseStep 1122869 = 105269) (by norm_num)
theorem B1122997 : Blo 662308 1122997 := bbase (se 5 (by rfl) ⟨52640, by rfl⟩ : syracuseStep 1122997 = 105281) (by norm_num)
theorem B1680061 : Blo 662308 1680061 := bbase (se 3 (by rfl) ⟨315011, by rfl⟩ : syracuseStep 1680061 = 630023) (by norm_num)
theorem B1516229 : Blo 662308 1516229 := bbase (se 4 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 1516229 = 284293) (by norm_num)
theorem B1123085 : Blo 662308 1123085 := bbase (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) (by norm_num)
theorem B1680173 : Blo 662308 1680173 := bbase (se 3 (by rfl) ⟨315032, by rfl⟩ : syracuseStep 1680173 = 630065) (by norm_num)
theorem B1123213 : Blo 662308 1123213 := bbase (se 3 (by rfl) ⟨210602, by rfl⟩ : syracuseStep 1123213 = 421205) (by norm_num)
theorem B2237381 : Blo 662308 2237381 := bbase (se 4 (by rfl) ⟨209754, by rfl⟩ : syracuseStep 2237381 = 419509) (by norm_num)
theorem B1123301 : Blo 662308 1123301 := bbase (se 4 (by rfl) ⟨105309, by rfl⟩ : syracuseStep 1123301 = 210619) (by norm_num)
theorem B1680365 : Blo 662308 1680365 := bbase (se 3 (by rfl) ⟨315068, by rfl⟩ : syracuseStep 1680365 = 630137) (by norm_num)
theorem B795701 : Blo 662308 795701 := bbase (se 5 (by rfl) ⟨37298, by rfl⟩ : syracuseStep 795701 = 74597) (by norm_num)
theorem B795749 : Blo 662308 795749 := bbase (se 4 (by rfl) ⟨74601, by rfl⟩ : syracuseStep 795749 = 149203) (by norm_num)
theorem B1123429 : Blo 662308 1123429 := bbase (se 4 (by rfl) ⟨105321, by rfl⟩ : syracuseStep 1123429 = 210643) (by norm_num)
theorem B1123517 : Blo 662308 1123517 := bbase (se 3 (by rfl) ⟨210659, by rfl⟩ : syracuseStep 1123517 = 421319) (by norm_num)
theorem B1418509 : Blo 662308 1418509 := bbase (se 3 (by rfl) ⟨265970, by rfl⟩ : syracuseStep 1418509 = 531941) (by norm_num)
theorem B730405 : Blo 662308 730405 := bbase (se 4 (by rfl) ⟨68475, by rfl⟩ : syracuseStep 730405 = 136951) (by norm_num)
theorem B1123645 : Blo 662308 1123645 := bbase (se 3 (by rfl) ⟨210683, by rfl⟩ : syracuseStep 1123645 = 421367) (by norm_num)
theorem B1680709 : Blo 662308 1680709 := bbase (se 4 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 1680709 = 315133) (by norm_num)
theorem B796009 : Blo 662308 796009 := bbase (se 2 (by rfl) ⟨298503, by rfl⟩ : syracuseStep 796009 = 597007) (by norm_num)
theorem B2237813 : Blo 662308 2237813 := bbase (se 5 (by rfl) ⟨104897, by rfl⟩ : syracuseStep 2237813 = 209795) (by norm_num)
theorem B1418629 : Blo 662308 1418629 := bbase (se 4 (by rfl) ⟨132996, by rfl⟩ : syracuseStep 1418629 = 265993) (by norm_num)
theorem B1123733 : Blo 662308 1123733 := bbase (se 6 (by rfl) ⟨26337, by rfl⟩ : syracuseStep 1123733 = 52675) (by norm_num)
theorem B1680821 : Blo 662308 1680821 := bbase (se 5 (by rfl) ⟨78788, by rfl⟩ : syracuseStep 1680821 = 157577) (by norm_num)
theorem B4793813 : Blo 662308 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B1123861 : Blo 662308 1123861 := bbase (se 6 (by rfl) ⟨26340, by rfl⟩ : syracuseStep 1123861 = 52681) (by norm_num)
theorem B1123949 : Blo 662308 1123949 := bbase (se 3 (by rfl) ⟨210740, by rfl⟩ : syracuseStep 1123949 = 421481) (by norm_num)
theorem B796273 : Blo 662308 796273 := bbase (se 2 (by rfl) ⟨298602, by rfl⟩ : syracuseStep 796273 = 597205) (by norm_num)
theorem B1681013 : Blo 662308 1681013 := bbase (se 5 (by rfl) ⟨78797, by rfl⟩ : syracuseStep 1681013 = 157595) (by norm_num)
theorem B1418885 : Blo 662308 1418885 := bbase (se 4 (by rfl) ⟨133020, by rfl⟩ : syracuseStep 1418885 = 266041) (by norm_num)
theorem B796393 : Blo 662308 796393 := bbase (se 2 (by rfl) ⟨298647, by rfl⟩ : syracuseStep 796393 = 597295) (by norm_num)
theorem B1124077 : Blo 662308 1124077 := bbase (se 3 (by rfl) ⟨210764, by rfl⟩ : syracuseStep 1124077 = 421529) (by norm_num)
theorem B2238245 : Blo 662308 2238245 := bbase (se 4 (by rfl) ⟨209835, by rfl⟩ : syracuseStep 2238245 = 419671) (by norm_num)
theorem B1124165 : Blo 662308 1124165 := bbase (se 4 (by rfl) ⟨105390, by rfl⟩ : syracuseStep 1124165 = 210781) (by norm_num)
theorem B1124293 : Blo 662308 1124293 := bbase (se 4 (by rfl) ⟨105402, by rfl⟩ : syracuseStep 1124293 = 210805) (by norm_num)
theorem B1681357 : Blo 662308 1681357 := bbase (se 3 (by rfl) ⟨315254, by rfl⟩ : syracuseStep 1681357 = 630509) (by norm_num)
theorem B1124381 : Blo 662308 1124381 := bbase (se 3 (by rfl) ⟨210821, by rfl⟩ : syracuseStep 1124381 = 421643) (by norm_num)
theorem B1681469 : Blo 662308 1681469 := bbase (se 3 (by rfl) ⟨315275, by rfl⟩ : syracuseStep 1681469 = 630551) (by norm_num)
theorem B993485 : Blo 662308 993485 := bbase (se 3 (by rfl) ⟨186278, by rfl⟩ : syracuseStep 993485 = 372557) (by norm_num)
theorem B2238677 : Blo 662308 2238677 := bbase (se 7 (by rfl) ⟨26234, by rfl⟩ : syracuseStep 2238677 = 52469) (by norm_num)
theorem B993509 : Blo 662308 993509 := bbase (se 4 (by rfl) ⟨93141, by rfl⟩ : syracuseStep 993509 = 186283) (by norm_num)
theorem B993533 : Blo 662308 993533 := bbase (se 3 (by rfl) ⟨186287, by rfl⟩ : syracuseStep 993533 = 372575) (by norm_num)
theorem B1681661 : Blo 662308 1681661 := bbase (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) (by norm_num)
theorem B993557 : Blo 662308 993557 := bbase (se 6 (by rfl) ⟨23286, by rfl⟩ : syracuseStep 993557 = 46573) (by norm_num)
theorem B993581 : Blo 662308 993581 := bbase (se 3 (by rfl) ⟨186296, by rfl⟩ : syracuseStep 993581 = 372593) (by norm_num)
theorem B993605 : Blo 662308 993605 := bbase (se 4 (by rfl) ⟨93150, by rfl⟩ : syracuseStep 993605 = 186301) (by norm_num)
theorem B993629 : Blo 662308 993629 := bbase (se 3 (by rfl) ⟨186305, by rfl⟩ : syracuseStep 993629 = 372611) (by norm_num)
theorem B1616237 : Blo 662308 1616237 := bbase (se 3 (by rfl) ⟨303044, by rfl⟩ : syracuseStep 1616237 = 606089) (by norm_num)
theorem B993653 : Blo 662308 993653 := bbase (se 5 (by rfl) ⟨46577, by rfl⟩ : syracuseStep 993653 = 93155) (by norm_num)
theorem B993677 : Blo 662308 993677 := bbase (se 3 (by rfl) ⟨186314, by rfl⟩ : syracuseStep 993677 = 372629) (by norm_num)
theorem B993701 : Blo 662308 993701 := bbase (se 4 (by rfl) ⟨93159, by rfl⟩ : syracuseStep 993701 = 186319) (by norm_num)
theorem B993725 : Blo 662308 993725 := bbase (se 3 (by rfl) ⟨186323, by rfl⟩ : syracuseStep 993725 = 372647) (by norm_num)
theorem B993749 : Blo 662308 993749 := bbase (se 7 (by rfl) ⟨11645, by rfl⟩ : syracuseStep 993749 = 23291) (by norm_num)
theorem B993773 : Blo 662308 993773 := bbase (se 3 (by rfl) ⟨186332, by rfl⟩ : syracuseStep 993773 = 372665) (by norm_num)
theorem B1419773 : Blo 662308 1419773 := bbase (se 3 (by rfl) ⟨266207, by rfl⟩ : syracuseStep 1419773 = 532415) (by norm_num)
theorem B993797 : Blo 662308 993797 := bbase (se 4 (by rfl) ⟨93168, by rfl⟩ : syracuseStep 993797 = 186337) (by norm_num)
theorem B993821 : Blo 662308 993821 := bbase (se 3 (by rfl) ⟨186341, by rfl⟩ : syracuseStep 993821 = 372683) (by norm_num)
theorem B993845 : Blo 662308 993845 := bbase (se 5 (by rfl) ⟨46586, by rfl⟩ : syracuseStep 993845 = 93173) (by norm_num)
theorem B797249 : Blo 662308 797249 := bbase (se 2 (by rfl) ⟨298968, by rfl⟩ : syracuseStep 797249 = 597937) (by norm_num)
theorem B993869 : Blo 662308 993869 := bbase (se 3 (by rfl) ⟨186350, by rfl⟩ : syracuseStep 993869 = 372701) (by norm_num)
theorem B1682005 : Blo 662308 1682005 := bbase (se 8 (by rfl) ⟨9855, by rfl⟩ : syracuseStep 1682005 = 19711) (by norm_num)
theorem B993893 : Blo 662308 993893 := bbase (se 4 (by rfl) ⟨93177, by rfl⟩ : syracuseStep 993893 = 186355) (by norm_num)
theorem B993917 : Blo 662308 993917 := bbase (se 3 (by rfl) ⟨186359, by rfl⟩ : syracuseStep 993917 = 372719) (by norm_num)
theorem B2239109 : Blo 662308 2239109 := bbase (se 4 (by rfl) ⟨209916, by rfl⟩ : syracuseStep 2239109 = 419833) (by norm_num)
theorem B3353237 : Blo 662308 3353237 := bbase (se 6 (by rfl) ⟨78591, by rfl⟩ : syracuseStep 3353237 = 157183) (by norm_num)
theorem B993941 : Blo 662308 993941 := bbase (se 6 (by rfl) ⟨23295, by rfl⟩ : syracuseStep 993941 = 46591) (by norm_num)
theorem B2468501 : Blo 662308 2468501 := bbase (se 6 (by rfl) ⟨57855, by rfl⟩ : syracuseStep 2468501 = 115711) (by norm_num)
theorem B993965 : Blo 662308 993965 := bbase (se 3 (by rfl) ⟨186368, by rfl⟩ : syracuseStep 993965 = 372737) (by norm_num)
theorem B993989 : Blo 662308 993989 := bbase (se 4 (by rfl) ⟨93186, by rfl⟩ : syracuseStep 993989 = 186373) (by norm_num)
theorem B1682117 : Blo 662308 1682117 := bbase (se 4 (by rfl) ⟨157698, by rfl⟩ : syracuseStep 1682117 = 315397) (by norm_num)
theorem B994013 : Blo 662308 994013 := bbase (se 3 (by rfl) ⟨186377, by rfl⟩ : syracuseStep 994013 = 372755) (by norm_num)
theorem B1420013 : Blo 662308 1420013 := bbase (se 3 (by rfl) ⟨266252, by rfl⟩ : syracuseStep 1420013 = 532505) (by norm_num)
theorem B994037 : Blo 662308 994037 := bbase (se 5 (by rfl) ⟨46595, by rfl⟩ : syracuseStep 994037 = 93191) (by norm_num)
theorem B994061 : Blo 662308 994061 := bbase (se 3 (by rfl) ⟨186386, by rfl⟩ : syracuseStep 994061 = 372773) (by norm_num)
theorem B895765 : Blo 662308 895765 := bbase (se 6 (by rfl) ⟨20994, by rfl⟩ : syracuseStep 895765 = 41989) (by norm_num)
theorem B3025685 : Blo 662308 3025685 := bbase (se 6 (by rfl) ⟨70914, by rfl⟩ : syracuseStep 3025685 = 141829) (by norm_num)
theorem B994085 : Blo 662308 994085 := bbase (se 4 (by rfl) ⟨93195, by rfl⟩ : syracuseStep 994085 = 186391) (by norm_num)
theorem B2304821 : Blo 662308 2304821 := bbase (se 5 (by rfl) ⟨108038, by rfl⟩ : syracuseStep 2304821 = 216077) (by norm_num)
theorem B994109 : Blo 662308 994109 := bbase (se 3 (by rfl) ⟨186395, by rfl⟩ : syracuseStep 994109 = 372791) (by norm_num)
theorem B994133 : Blo 662308 994133 := bbase (se 9 (by rfl) ⟨2912, by rfl⟩ : syracuseStep 994133 = 5825) (by norm_num)
theorem B994157 : Blo 662308 994157 := bbase (se 3 (by rfl) ⟨186404, by rfl⟩ : syracuseStep 994157 = 372809) (by norm_num)
theorem B994181 : Blo 662308 994181 := bbase (se 4 (by rfl) ⟨93204, by rfl⟩ : syracuseStep 994181 = 186409) (by norm_num)
theorem B1682309 : Blo 662308 1682309 := bbase (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) (by norm_num)
theorem B994205 : Blo 662308 994205 := bbase (se 3 (by rfl) ⟨186413, by rfl⟩ : syracuseStep 994205 = 372827) (by norm_num)
theorem B994229 : Blo 662308 994229 := bbase (se 5 (by rfl) ⟨46604, by rfl⟩ : syracuseStep 994229 = 93209) (by norm_num)
theorem B994253 : Blo 662308 994253 := bbase (se 3 (by rfl) ⟨186422, by rfl⟩ : syracuseStep 994253 = 372845) (by norm_num)
theorem B994277 : Blo 662308 994277 := bbase (se 4 (by rfl) ⟨93213, by rfl⟩ : syracuseStep 994277 = 186427) (by norm_num)
theorem B1518581 : Blo 662308 1518581 := bbase (se 5 (by rfl) ⟨71183, by rfl⟩ : syracuseStep 1518581 = 142367) (by norm_num)
theorem B994301 : Blo 662308 994301 := bbase (se 3 (by rfl) ⟨186431, by rfl⟩ : syracuseStep 994301 = 372863) (by norm_num)
theorem B994325 : Blo 662308 994325 := bbase (se 6 (by rfl) ⟨23304, by rfl⟩ : syracuseStep 994325 = 46609) (by norm_num)
theorem B994349 : Blo 662308 994349 := bbase (se 3 (by rfl) ⟨186440, by rfl⟩ : syracuseStep 994349 = 372881) (by norm_num)
theorem B2239541 : Blo 662308 2239541 := bbase (se 5 (by rfl) ⟨104978, by rfl⟩ : syracuseStep 2239541 = 209957) (by norm_num)
theorem B994373 : Blo 662308 994373 := bbase (se 4 (by rfl) ⟨93222, by rfl⟩ : syracuseStep 994373 = 186445) (by norm_num)
theorem B994397 : Blo 662308 994397 := bbase (se 3 (by rfl) ⟨186449, by rfl⟩ : syracuseStep 994397 = 372899) (by norm_num)
theorem B994421 : Blo 662308 994421 := bbase (se 5 (by rfl) ⟨46613, by rfl⟩ : syracuseStep 994421 = 93227) (by norm_num)
theorem B994445 : Blo 662308 994445 := bbase (se 3 (by rfl) ⟨186458, by rfl⟩ : syracuseStep 994445 = 372917) (by norm_num)
theorem B994469 : Blo 662308 994469 := bbase (se 4 (by rfl) ⟨93231, by rfl⟩ : syracuseStep 994469 = 186463) (by norm_num)
theorem B994493 : Blo 662308 994493 := bbase (se 3 (by rfl) ⟨186467, by rfl⟩ : syracuseStep 994493 = 372935) (by norm_num)
theorem B994517 : Blo 662308 994517 := bbase (se 7 (by rfl) ⟨11654, by rfl⟩ : syracuseStep 994517 = 23309) (by norm_num)
theorem B1682653 : Blo 662308 1682653 := bbase (se 3 (by rfl) ⟨315497, by rfl⟩ : syracuseStep 1682653 = 630995) (by norm_num)
theorem B1420517 : Blo 662308 1420517 := bbase (se 4 (by rfl) ⟨133173, by rfl⟩ : syracuseStep 1420517 = 266347) (by norm_num)
theorem B994541 : Blo 662308 994541 := bbase (se 3 (by rfl) ⟨186476, by rfl⟩ : syracuseStep 994541 = 372953) (by norm_num)
theorem B1420525 : Blo 662308 1420525 := bbase (se 3 (by rfl) ⟨266348, by rfl⟩ : syracuseStep 1420525 = 532697) (by norm_num)
theorem B994565 : Blo 662308 994565 := bbase (se 4 (by rfl) ⟨93240, by rfl⟩ : syracuseStep 994565 = 186481) (by norm_num)
theorem B797969 : Blo 662308 797969 := bbase (se 2 (by rfl) ⟨299238, by rfl⟩ : syracuseStep 797969 = 598477) (by norm_num)
theorem B994589 : Blo 662308 994589 := bbase (se 3 (by rfl) ⟨186485, by rfl⟩ : syracuseStep 994589 = 372971) (by norm_num)
theorem B994613 : Blo 662308 994613 := bbase (se 5 (by rfl) ⟨46622, by rfl⟩ : syracuseStep 994613 = 93245) (by norm_num)
theorem B994637 : Blo 662308 994637 := bbase (se 3 (by rfl) ⟨186494, by rfl⟩ : syracuseStep 994637 = 372989) (by norm_num)
theorem B1682765 : Blo 662308 1682765 := bbase (se 3 (by rfl) ⟨315518, by rfl⟩ : syracuseStep 1682765 = 631037) (by norm_num)
theorem B994661 : Blo 662308 994661 := bbase (se 4 (by rfl) ⟨93249, by rfl⟩ : syracuseStep 994661 = 186499) (by norm_num)
theorem B994685 : Blo 662308 994685 := bbase (se 3 (by rfl) ⟨186503, by rfl⟩ : syracuseStep 994685 = 373007) (by norm_num)
theorem B994709 : Blo 662308 994709 := bbase (se 6 (by rfl) ⟨23313, by rfl⟩ : syracuseStep 994709 = 46627) (by norm_num)
theorem B994733 : Blo 662308 994733 := bbase (se 3 (by rfl) ⟨186512, by rfl⟩ : syracuseStep 994733 = 373025) (by norm_num)
theorem B994757 : Blo 662308 994757 := bbase (se 4 (by rfl) ⟨93258, by rfl⟩ : syracuseStep 994757 = 186517) (by norm_num)
theorem B994781 : Blo 662308 994781 := bbase (se 3 (by rfl) ⟨186521, by rfl⟩ : syracuseStep 994781 = 373043) (by norm_num)
theorem B2239973 : Blo 662308 2239973 := bbase (se 4 (by rfl) ⟨209997, by rfl⟩ : syracuseStep 2239973 = 419995) (by norm_num)
theorem B994805 : Blo 662308 994805 := bbase (se 5 (by rfl) ⟨46631, by rfl⟩ : syracuseStep 994805 = 93263) (by norm_num)
theorem B994829 : Blo 662308 994829 := bbase (se 3 (by rfl) ⟨186530, by rfl⟩ : syracuseStep 994829 = 373061) (by norm_num)
theorem B1682957 : Blo 662308 1682957 := bbase (se 3 (by rfl) ⟨315554, by rfl⟩ : syracuseStep 1682957 = 631109) (by norm_num)
theorem B994853 : Blo 662308 994853 := bbase (se 4 (by rfl) ⟨93267, by rfl⟩ : syracuseStep 994853 = 186535) (by norm_num)
theorem B994877 : Blo 662308 994877 := bbase (se 3 (by rfl) ⟨186539, by rfl⟩ : syracuseStep 994877 = 373079) (by norm_num)
theorem B798277 : Blo 662308 798277 := bbase (se 4 (by rfl) ⟨74838, by rfl⟩ : syracuseStep 798277 = 149677) (by norm_num)
theorem B994901 : Blo 662308 994901 := bbase (se 8 (by rfl) ⟨5829, by rfl⟩ : syracuseStep 994901 = 11659) (by norm_num)
theorem B994925 : Blo 662308 994925 := bbase (se 3 (by rfl) ⟨186548, by rfl⟩ : syracuseStep 994925 = 373097) (by norm_num)
theorem B994949 : Blo 662308 994949 := bbase (se 4 (by rfl) ⟨93276, by rfl⟩ : syracuseStep 994949 = 186553) (by norm_num)
theorem B994973 : Blo 662308 994973 := bbase (se 3 (by rfl) ⟨186557, by rfl⟩ : syracuseStep 994973 = 373115) (by norm_num)
theorem B798373 : Blo 662308 798373 := bbase (se 4 (by rfl) ⟨74847, by rfl⟩ : syracuseStep 798373 = 149695) (by norm_num)
theorem B994997 : Blo 662308 994997 := bbase (se 5 (by rfl) ⟨46640, by rfl⟩ : syracuseStep 994997 = 93281) (by norm_num)
theorem B995021 : Blo 662308 995021 := bbase (se 3 (by rfl) ⟨186566, by rfl⟩ : syracuseStep 995021 = 373133) (by norm_num)
theorem B995045 : Blo 662308 995045 := bbase (se 4 (by rfl) ⟨93285, by rfl⟩ : syracuseStep 995045 = 186571) (by norm_num)
theorem B1093349 : Blo 662308 1093349 := bbase (se 4 (by rfl) ⟨102501, by rfl⟩ : syracuseStep 1093349 = 205003) (by norm_num)
theorem B995069 : Blo 662308 995069 := bbase (se 3 (by rfl) ⟨186575, by rfl⟩ : syracuseStep 995069 = 373151) (by norm_num)
theorem B995093 : Blo 662308 995093 := bbase (se 6 (by rfl) ⟨23322, by rfl⟩ : syracuseStep 995093 = 46645) (by norm_num)
theorem B995117 : Blo 662308 995117 := bbase (se 3 (by rfl) ⟨186584, by rfl⟩ : syracuseStep 995117 = 373169) (by norm_num)
theorem B798517 : Blo 662308 798517 := bbase (se 5 (by rfl) ⟨37430, by rfl⟩ : syracuseStep 798517 = 74861) (by norm_num)
theorem B995141 : Blo 662308 995141 := bbase (se 4 (by rfl) ⟨93294, by rfl⟩ : syracuseStep 995141 = 186589) (by norm_num)
theorem B995165 : Blo 662308 995165 := bbase (se 3 (by rfl) ⟨186593, by rfl⟩ : syracuseStep 995165 = 373187) (by norm_num)
theorem B1683301 : Blo 662308 1683301 := bbase (se 4 (by rfl) ⟨157809, by rfl⟩ : syracuseStep 1683301 = 315619) (by norm_num)
theorem B995189 : Blo 662308 995189 := bbase (se 5 (by rfl) ⟨46649, by rfl⟩ : syracuseStep 995189 = 93299) (by norm_num)
theorem B995213 : Blo 662308 995213 := bbase (se 3 (by rfl) ⟨186602, by rfl⟩ : syracuseStep 995213 = 373205) (by norm_num)
theorem B2240405 : Blo 662308 2240405 := bbase (se 6 (by rfl) ⟨52509, by rfl⟩ : syracuseStep 2240405 = 105019) (by norm_num)
theorem B1257373 : Blo 662308 1257373 := bbase (se 3 (by rfl) ⟨235757, by rfl⟩ : syracuseStep 1257373 = 471515) (by norm_num)
theorem B3354533 : Blo 662308 3354533 := bbase (se 4 (by rfl) ⟨314487, by rfl⟩ : syracuseStep 3354533 = 628975) (by norm_num)
theorem B995237 : Blo 662308 995237 := bbase (se 4 (by rfl) ⟨93303, by rfl⟩ : syracuseStep 995237 = 186607) (by norm_num)
theorem B3583925 : Blo 662308 3583925 := bbase (se 5 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 3583925 = 335993) (by norm_num)
theorem B995261 : Blo 662308 995261 := bbase (se 3 (by rfl) ⟨186611, by rfl⟩ : syracuseStep 995261 = 373223) (by norm_num)
theorem B995285 : Blo 662308 995285 := bbase (se 7 (by rfl) ⟨11663, by rfl⟩ : syracuseStep 995285 = 23327) (by norm_num)
theorem B1683413 : Blo 662308 1683413 := bbase (se 7 (by rfl) ⟨19727, by rfl⟩ : syracuseStep 1683413 = 39455) (by norm_num)
theorem B995309 : Blo 662308 995309 := bbase (se 3 (by rfl) ⟨186620, by rfl⟩ : syracuseStep 995309 = 373241) (by norm_num)
theorem B995333 : Blo 662308 995333 := bbase (se 4 (by rfl) ⟨93312, by rfl⟩ : syracuseStep 995333 = 186625) (by norm_num)
theorem B995357 : Blo 662308 995357 := bbase (se 3 (by rfl) ⟨186629, by rfl⟩ : syracuseStep 995357 = 373259) (by norm_num)
theorem B2830373 : Blo 662308 2830373 := bbase (se 4 (by rfl) ⟨265347, by rfl⟩ : syracuseStep 2830373 = 530695) (by norm_num)
theorem B995381 : Blo 662308 995381 := bbase (se 5 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 995381 = 93317) (by norm_num)
theorem B995405 : Blo 662308 995405 := bbase (se 3 (by rfl) ⟨186638, by rfl⟩ : syracuseStep 995405 = 373277) (by norm_num)
theorem B995429 : Blo 662308 995429 := bbase (se 4 (by rfl) ⟨93321, by rfl⟩ : syracuseStep 995429 = 186643) (by norm_num)
theorem B995453 : Blo 662308 995453 := bbase (se 3 (by rfl) ⟨186647, by rfl⟩ : syracuseStep 995453 = 373295) (by norm_num)
theorem B995477 : Blo 662308 995477 := bbase (se 6 (by rfl) ⟨23331, by rfl⟩ : syracuseStep 995477 = 46663) (by norm_num)
theorem B1683605 : Blo 662308 1683605 := bbase (se 6 (by rfl) ⟨39459, by rfl⟩ : syracuseStep 1683605 = 78919) (by norm_num)
theorem B995501 : Blo 662308 995501 := bbase (se 3 (by rfl) ⟨186656, by rfl⟩ : syracuseStep 995501 = 373313) (by norm_num)
theorem B995525 : Blo 662308 995525 := bbase (se 4 (by rfl) ⟨93330, by rfl⟩ : syracuseStep 995525 = 186661) (by norm_num)
theorem B1257677 : Blo 662308 1257677 := bbase (se 3 (by rfl) ⟨235814, by rfl⟩ : syracuseStep 1257677 = 471629) (by norm_num)
theorem B5058773 : Blo 662308 5058773 := bbase (se 7 (by rfl) ⟨59282, by rfl⟩ : syracuseStep 5058773 = 118565) (by norm_num)
theorem B995549 : Blo 662308 995549 := bbase (se 3 (by rfl) ⟨186665, by rfl⟩ : syracuseStep 995549 = 373331) (by norm_num)
theorem B995573 : Blo 662308 995573 := bbase (se 5 (by rfl) ⟨46667, by rfl⟩ : syracuseStep 995573 = 93335) (by norm_num)
theorem B995597 : Blo 662308 995597 := bbase (se 3 (by rfl) ⟨186674, by rfl⟩ : syracuseStep 995597 = 373349) (by norm_num)
theorem B995621 : Blo 662308 995621 := bbase (se 4 (by rfl) ⟨93339, by rfl⟩ : syracuseStep 995621 = 186679) (by norm_num)
theorem B995645 : Blo 662308 995645 := bbase (se 3 (by rfl) ⟨186683, by rfl⟩ : syracuseStep 995645 = 373367) (by norm_num)
theorem B2240837 : Blo 662308 2240837 := bbase (se 4 (by rfl) ⟨210078, by rfl⟩ : syracuseStep 2240837 = 420157) (by norm_num)
theorem B995669 : Blo 662308 995669 := bbase (se 10 (by rfl) ⟨1458, by rfl⟩ : syracuseStep 995669 = 2917) (by norm_num)
theorem B897365 : Blo 662308 897365 := bbase (se 10 (by rfl) ⟨1314, by rfl⟩ : syracuseStep 897365 = 2629) (by norm_num)
theorem B1421653 : Blo 662308 1421653 := bbase (se 10 (by rfl) ⟨2082, by rfl⟩ : syracuseStep 1421653 = 4165) (by norm_num)
theorem B995693 : Blo 662308 995693 := bbase (se 3 (by rfl) ⟨186692, by rfl⟩ : syracuseStep 995693 = 373385) (by norm_num)
theorem B1061237 : Blo 662308 1061237 := bbase (se 5 (by rfl) ⟨49745, by rfl⟩ : syracuseStep 1061237 = 99491) (by norm_num)
theorem B995717 : Blo 662308 995717 := bbase (se 4 (by rfl) ⟨93348, by rfl⟩ : syracuseStep 995717 = 186697) (by norm_num)
theorem B2699669 : Blo 662308 2699669 := bbase (se 6 (by rfl) ⟨63273, by rfl⟩ : syracuseStep 2699669 = 126547) (by norm_num)
theorem B995741 : Blo 662308 995741 := bbase (se 3 (by rfl) ⟨186701, by rfl⟩ : syracuseStep 995741 = 373403) (by norm_num)
theorem B995765 : Blo 662308 995765 := bbase (se 5 (by rfl) ⟨46676, by rfl⟩ : syracuseStep 995765 = 93353) (by norm_num)
theorem B995789 : Blo 662308 995789 := bbase (se 3 (by rfl) ⟨186710, by rfl⟩ : syracuseStep 995789 = 373421) (by norm_num)
theorem B995813 : Blo 662308 995813 := bbase (se 4 (by rfl) ⟨93357, by rfl⟩ : syracuseStep 995813 = 186715) (by norm_num)
theorem B1683949 : Blo 662308 1683949 := bbase (se 3 (by rfl) ⟨315740, by rfl⟩ : syracuseStep 1683949 = 631481) (by norm_num)
theorem B995837 : Blo 662308 995837 := bbase (se 3 (by rfl) ⟨186719, by rfl⟩ : syracuseStep 995837 = 373439) (by norm_num)
theorem B995861 : Blo 662308 995861 := bbase (se 6 (by rfl) ⟨23340, by rfl⟩ : syracuseStep 995861 = 46681) (by norm_num)
theorem B995885 : Blo 662308 995885 := bbase (se 3 (by rfl) ⟨186728, by rfl⟩ : syracuseStep 995885 = 373457) (by norm_num)
theorem B995909 : Blo 662308 995909 := bbase (se 4 (by rfl) ⟨93366, by rfl⟩ : syracuseStep 995909 = 186733) (by norm_num)
theorem B995933 : Blo 662308 995933 := bbase (se 3 (by rfl) ⟨186737, by rfl⟩ : syracuseStep 995933 = 373475) (by norm_num)
theorem B1684061 : Blo 662308 1684061 := bbase (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) (by norm_num)
theorem B766561 : Blo 662308 766561 := bbase (se 2 (by rfl) ⟨287460, by rfl⟩ : syracuseStep 766561 = 574921) (by norm_num)
theorem B995957 : Blo 662308 995957 := bbase (se 5 (by rfl) ⟨46685, by rfl⟩ : syracuseStep 995957 = 93371) (by norm_num)
theorem B995981 : Blo 662308 995981 := bbase (se 3 (by rfl) ⟨186746, by rfl⟩ : syracuseStep 995981 = 373493) (by norm_num)
theorem B996005 : Blo 662308 996005 := bbase (se 4 (by rfl) ⟨93375, by rfl⟩ : syracuseStep 996005 = 186751) (by norm_num)
theorem B996029 : Blo 662308 996029 := bbase (se 3 (by rfl) ⟨186755, by rfl⟩ : syracuseStep 996029 = 373511) (by norm_num)
theorem B1422029 : Blo 662308 1422029 := bbase (se 3 (by rfl) ⟨266630, by rfl⟩ : syracuseStep 1422029 = 533261) (by norm_num)
theorem B996053 : Blo 662308 996053 := bbase (se 7 (by rfl) ⟨11672, by rfl⟩ : syracuseStep 996053 = 23345) (by norm_num)
theorem B996077 : Blo 662308 996077 := bbase (se 3 (by rfl) ⟨186764, by rfl⟩ : syracuseStep 996077 = 373529) (by norm_num)
theorem B2241269 : Blo 662308 2241269 := bbase (se 5 (by rfl) ⟨105059, by rfl⟩ : syracuseStep 2241269 = 210119) (by norm_num)
theorem B996101 : Blo 662308 996101 := bbase (se 4 (by rfl) ⟨93384, by rfl⟩ : syracuseStep 996101 = 186769) (by norm_num)
theorem B996125 : Blo 662308 996125 := bbase (se 3 (by rfl) ⟨186773, by rfl⟩ : syracuseStep 996125 = 373547) (by norm_num)
theorem B1684253 : Blo 662308 1684253 := bbase (se 3 (by rfl) ⟨315797, by rfl⟩ : syracuseStep 1684253 = 631595) (by norm_num)
theorem B799517 : Blo 662308 799517 := bbase (se 3 (by rfl) ⟨149909, by rfl⟩ : syracuseStep 799517 = 299819) (by norm_num)
theorem B996149 : Blo 662308 996149 := bbase (se 5 (by rfl) ⟨46694, by rfl⟩ : syracuseStep 996149 = 93389) (by norm_num)
theorem B996173 : Blo 662308 996173 := bbase (se 3 (by rfl) ⟨186782, by rfl⟩ : syracuseStep 996173 = 373565) (by norm_num)
theorem B996197 : Blo 662308 996197 := bbase (se 4 (by rfl) ⟨93393, by rfl⟩ : syracuseStep 996197 = 186787) (by norm_num)
theorem B996221 : Blo 662308 996221 := bbase (se 3 (by rfl) ⟨186791, by rfl⟩ : syracuseStep 996221 = 373583) (by norm_num)
theorem B996245 : Blo 662308 996245 := bbase (se 6 (by rfl) ⟨23349, by rfl⟩ : syracuseStep 996245 = 46699) (by norm_num)
theorem B996269 : Blo 662308 996269 := bbase (se 3 (by rfl) ⟨186800, by rfl⟩ : syracuseStep 996269 = 373601) (by norm_num)
theorem B1258429 : Blo 662308 1258429 := bbase (se 3 (by rfl) ⟨235955, by rfl⟩ : syracuseStep 1258429 = 471911) (by norm_num)
theorem B996293 : Blo 662308 996293 := bbase (se 4 (by rfl) ⟨93402, by rfl⟩ : syracuseStep 996293 = 186805) (by norm_num)
theorem B996317 : Blo 662308 996317 := bbase (se 3 (by rfl) ⟨186809, by rfl⟩ : syracuseStep 996317 = 373619) (by norm_num)
theorem B996341 : Blo 662308 996341 := bbase (se 5 (by rfl) ⟨46703, by rfl⟩ : syracuseStep 996341 = 93407) (by norm_num)
theorem B996365 : Blo 662308 996365 := bbase (se 3 (by rfl) ⟨186818, by rfl⟩ : syracuseStep 996365 = 373637) (by norm_num)
theorem B2831381 : Blo 662308 2831381 := bbase (se 6 (by rfl) ⟨66360, by rfl⟩ : syracuseStep 2831381 = 132721) (by norm_num)
theorem B996389 : Blo 662308 996389 := bbase (se 4 (by rfl) ⟨93411, by rfl⟩ : syracuseStep 996389 = 186823) (by norm_num)
theorem B996413 : Blo 662308 996413 := bbase (se 3 (by rfl) ⟨186827, by rfl⟩ : syracuseStep 996413 = 373655) (by norm_num)
theorem B1258573 : Blo 662308 1258573 := bbase (se 3 (by rfl) ⟨235982, by rfl⟩ : syracuseStep 1258573 = 471965) (by norm_num)
theorem B996437 : Blo 662308 996437 := bbase (se 8 (by rfl) ⟨5838, by rfl⟩ : syracuseStep 996437 = 11677) (by norm_num)
theorem B996461 : Blo 662308 996461 := bbase (se 3 (by rfl) ⟨186836, by rfl⟩ : syracuseStep 996461 = 373673) (by norm_num)
theorem B1684597 : Blo 662308 1684597 := bbase (se 5 (by rfl) ⟨78965, by rfl⟩ : syracuseStep 1684597 = 157931) (by norm_num)
theorem B996485 : Blo 662308 996485 := bbase (se 4 (by rfl) ⟨93420, by rfl⟩ : syracuseStep 996485 = 186841) (by norm_num)
theorem B996509 : Blo 662308 996509 := bbase (se 3 (by rfl) ⟨186845, by rfl⟩ : syracuseStep 996509 = 373691) (by norm_num)
theorem B2241701 : Blo 662308 2241701 := bbase (se 4 (by rfl) ⟨210159, by rfl⟩ : syracuseStep 2241701 = 420319) (by norm_num)
theorem B3355829 : Blo 662308 3355829 := bbase (se 5 (by rfl) ⟨157304, by rfl⟩ : syracuseStep 3355829 = 314609) (by norm_num)
theorem B996533 : Blo 662308 996533 := bbase (se 5 (by rfl) ⟨46712, by rfl⟩ : syracuseStep 996533 = 93425) (by norm_num)
theorem B996557 : Blo 662308 996557 := bbase (se 3 (by rfl) ⟨186854, by rfl⟩ : syracuseStep 996557 = 373709) (by norm_num)
theorem B996581 : Blo 662308 996581 := bbase (se 4 (by rfl) ⟨93429, by rfl⟩ : syracuseStep 996581 = 186859) (by norm_num)
theorem B1684709 : Blo 662308 1684709 := bbase (se 4 (by rfl) ⟨157941, by rfl⟩ : syracuseStep 1684709 = 315883) (by norm_num)
theorem B1258733 : Blo 662308 1258733 := bbase (se 3 (by rfl) ⟨236012, by rfl⟩ : syracuseStep 1258733 = 472025) (by norm_num)
theorem B996605 : Blo 662308 996605 := bbase (se 3 (by rfl) ⟨186863, by rfl⟩ : syracuseStep 996605 = 373727) (by norm_num)
theorem B996629 : Blo 662308 996629 := bbase (se 6 (by rfl) ⟨23358, by rfl⟩ : syracuseStep 996629 = 46717) (by norm_num)
theorem B996653 : Blo 662308 996653 := bbase (se 3 (by rfl) ⟨186872, by rfl⟩ : syracuseStep 996653 = 373745) (by norm_num)
theorem B996677 : Blo 662308 996677 := bbase (se 4 (by rfl) ⟨93438, by rfl⟩ : syracuseStep 996677 = 186877) (by norm_num)
theorem B1062229 : Blo 662308 1062229 := bbase (se 13 (by rfl) ⟨194, by rfl⟩ : syracuseStep 1062229 = 389) (by norm_num)
theorem B996701 : Blo 662308 996701 := bbase (se 3 (by rfl) ⟨186881, by rfl⟩ : syracuseStep 996701 = 373763) (by norm_num)
theorem B996725 : Blo 662308 996725 := bbase (se 5 (by rfl) ⟨46721, by rfl⟩ : syracuseStep 996725 = 93443) (by norm_num)
theorem B1258877 : Blo 662308 1258877 := bbase (se 3 (by rfl) ⟨236039, by rfl⟩ : syracuseStep 1258877 = 472079) (by norm_num)
theorem B996749 : Blo 662308 996749 := bbase (se 3 (by rfl) ⟨186890, by rfl⟩ : syracuseStep 996749 = 373781) (by norm_num)
theorem B996773 : Blo 662308 996773 := bbase (se 4 (by rfl) ⟨93447, by rfl⟩ : syracuseStep 996773 = 186895) (by norm_num)
theorem B1684901 : Blo 662308 1684901 := bbase (se 4 (by rfl) ⟨157959, by rfl⟩ : syracuseStep 1684901 = 315919) (by norm_num)
theorem B996797 : Blo 662308 996797 := bbase (se 3 (by rfl) ⟨186899, by rfl⟩ : syracuseStep 996797 = 373799) (by norm_num)
theorem B800209 : Blo 662308 800209 := bbase (se 2 (by rfl) ⟨300078, by rfl⟩ : syracuseStep 800209 = 600157) (by norm_num)
theorem B996821 : Blo 662308 996821 := bbase (se 7 (by rfl) ⟨11681, by rfl⟩ : syracuseStep 996821 = 23363) (by norm_num)
theorem B865753 : Blo 662308 865753 := bbase (se 2 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 865753 = 649315) (by norm_num)
theorem B996845 : Blo 662308 996845 := bbase (se 3 (by rfl) ⟨186908, by rfl⟩ : syracuseStep 996845 = 373817) (by norm_num)
theorem B996869 : Blo 662308 996869 := bbase (se 4 (by rfl) ⟨93456, by rfl⟩ : syracuseStep 996869 = 186913) (by norm_num)
theorem B6829589 : Blo 662308 6829589 := bbase (se 6 (by rfl) ⟨160068, by rfl⟩ : syracuseStep 6829589 = 320137) (by norm_num)
theorem B996893 : Blo 662308 996893 := bbase (se 3 (by rfl) ⟨186917, by rfl⟩ : syracuseStep 996893 = 373835) (by norm_num)
theorem B996917 : Blo 662308 996917 := bbase (se 5 (by rfl) ⟨46730, by rfl⟩ : syracuseStep 996917 = 93461) (by norm_num)
theorem B996941 : Blo 662308 996941 := bbase (se 3 (by rfl) ⟨186926, by rfl⟩ : syracuseStep 996941 = 373853) (by norm_num)
theorem B2242133 : Blo 662308 2242133 := bbase (se 8 (by rfl) ⟨13137, by rfl⟩ : syracuseStep 2242133 = 26275) (by norm_num)
theorem B996965 : Blo 662308 996965 := bbase (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) (by norm_num)
theorem B996989 : Blo 662308 996989 := bbase (se 3 (by rfl) ⟨186935, by rfl⟩ : syracuseStep 996989 = 373871) (by norm_num)
theorem B997013 : Blo 662308 997013 := bbase (se 6 (by rfl) ⟨23367, by rfl⟩ : syracuseStep 997013 = 46735) (by norm_num)
theorem B1259165 : Blo 662308 1259165 := bbase (se 3 (by rfl) ⟨236093, by rfl⟩ : syracuseStep 1259165 = 472187) (by norm_num)
theorem B800425 : Blo 662308 800425 := bbase (se 2 (by rfl) ⟨300159, by rfl⟩ : syracuseStep 800425 = 600319) (by norm_num)
theorem B997037 : Blo 662308 997037 := bbase (se 3 (by rfl) ⟨186944, by rfl⟩ : syracuseStep 997037 = 373889) (by norm_num)
theorem B997061 : Blo 662308 997061 := bbase (se 4 (by rfl) ⟨93474, by rfl⟩ : syracuseStep 997061 = 186949) (by norm_num)
theorem B997085 : Blo 662308 997085 := bbase (se 3 (by rfl) ⟨186953, by rfl⟩ : syracuseStep 997085 = 373907) (by norm_num)
theorem B997109 : Blo 662308 997109 := bbase (se 5 (by rfl) ⟨46739, by rfl⟩ : syracuseStep 997109 = 93479) (by norm_num)
theorem B1685245 : Blo 662308 1685245 := bbase (se 3 (by rfl) ⟨315983, by rfl⟩ : syracuseStep 1685245 = 631967) (by norm_num)
theorem B997133 : Blo 662308 997133 := bbase (se 3 (by rfl) ⟨186962, by rfl⟩ : syracuseStep 997133 = 373925) (by norm_num)
theorem B1062677 : Blo 662308 1062677 := bbase (se 6 (by rfl) ⟨24906, by rfl⟩ : syracuseStep 1062677 = 49813) (by norm_num)
theorem B997157 : Blo 662308 997157 := bbase (se 4 (by rfl) ⟨93483, by rfl⟩ : syracuseStep 997157 = 186967) (by norm_num)
theorem B1259317 : Blo 662308 1259317 := bbase (se 5 (by rfl) ⟨59030, by rfl⟩ : syracuseStep 1259317 = 118061) (by norm_num)
theorem B997181 : Blo 662308 997181 := bbase (se 3 (by rfl) ⟨186971, by rfl⟩ : syracuseStep 997181 = 373943) (by norm_num)
theorem B997205 : Blo 662308 997205 := bbase (se 9 (by rfl) ⟨2921, by rfl⟩ : syracuseStep 997205 = 5843) (by norm_num)
theorem B997229 : Blo 662308 997229 := bbase (se 3 (by rfl) ⟨186980, by rfl⟩ : syracuseStep 997229 = 373961) (by norm_num)
theorem B1685357 : Blo 662308 1685357 := bbase (se 3 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 1685357 = 632009) (by norm_num)
theorem B997253 : Blo 662308 997253 := bbase (se 4 (by rfl) ⟨93492, by rfl⟩ : syracuseStep 997253 = 186985) (by norm_num)
theorem B1193869 : Blo 662308 1193869 := bbase (se 3 (by rfl) ⟨223850, by rfl⟩ : syracuseStep 1193869 = 447701) (by norm_num)
theorem B997277 : Blo 662308 997277 := bbase (se 3 (by rfl) ⟨186989, by rfl⟩ : syracuseStep 997277 = 373979) (by norm_num)
theorem B997301 : Blo 662308 997301 := bbase (se 5 (by rfl) ⟨46748, by rfl⟩ : syracuseStep 997301 = 93497) (by norm_num)
theorem B997325 : Blo 662308 997325 := bbase (se 3 (by rfl) ⟨186998, by rfl⟩ : syracuseStep 997325 = 373997) (by norm_num)
theorem B1062877 : Blo 662308 1062877 := bbase (se 3 (by rfl) ⟨199289, by rfl⟩ : syracuseStep 1062877 = 398579) (by norm_num)
theorem B997349 : Blo 662308 997349 := bbase (se 4 (by rfl) ⟨93501, by rfl⟩ : syracuseStep 997349 = 187003) (by norm_num)
theorem B3782645 : Blo 662308 3782645 := bbase (se 5 (by rfl) ⟨177311, by rfl⟩ : syracuseStep 3782645 = 354623) (by norm_num)
theorem B997373 : Blo 662308 997373 := bbase (se 3 (by rfl) ⟨187007, by rfl⟩ : syracuseStep 997373 = 374015) (by norm_num)
theorem B2242565 : Blo 662308 2242565 := bbase (se 4 (by rfl) ⟨210240, by rfl⟩ : syracuseStep 2242565 = 420481) (by norm_num)
theorem B997397 : Blo 662308 997397 := bbase (se 6 (by rfl) ⟨23376, by rfl⟩ : syracuseStep 997397 = 46753) (by norm_num)
theorem B997421 : Blo 662308 997421 := bbase (se 3 (by rfl) ⟨187016, by rfl⟩ : syracuseStep 997421 = 374033) (by norm_num)
theorem B1685549 : Blo 662308 1685549 := bbase (se 3 (by rfl) ⟨316040, by rfl⟩ : syracuseStep 1685549 = 632081) (by norm_num)
theorem B997445 : Blo 662308 997445 := bbase (se 4 (by rfl) ⟨93510, by rfl⟩ : syracuseStep 997445 = 187021) (by norm_num)
theorem B997469 : Blo 662308 997469 := bbase (se 3 (by rfl) ⟨187025, by rfl⟩ : syracuseStep 997469 = 374051) (by norm_num)
theorem B1194085 : Blo 662308 1194085 := bbase (se 4 (by rfl) ⟨111945, by rfl⟩ : syracuseStep 1194085 = 223891) (by norm_num)
theorem B1259621 : Blo 662308 1259621 := bbase (se 4 (by rfl) ⟨118089, by rfl⟩ : syracuseStep 1259621 = 236179) (by norm_num)
theorem B997493 : Blo 662308 997493 := bbase (se 5 (by rfl) ⟨46757, by rfl⟩ : syracuseStep 997493 = 93515) (by norm_num)
theorem B997517 : Blo 662308 997517 := bbase (se 3 (by rfl) ⟨187034, by rfl⟩ : syracuseStep 997517 = 374069) (by norm_num)
theorem B997541 : Blo 662308 997541 := bbase (se 4 (by rfl) ⟨93519, by rfl⟩ : syracuseStep 997541 = 187039) (by norm_num)
theorem B997565 : Blo 662308 997565 := bbase (se 3 (by rfl) ⟨187043, by rfl⟩ : syracuseStep 997565 = 374087) (by norm_num)
theorem B997589 : Blo 662308 997589 := bbase (se 7 (by rfl) ⟨11690, by rfl⟩ : syracuseStep 997589 = 23381) (by norm_num)
theorem B1063133 : Blo 662308 1063133 := bbase (se 3 (by rfl) ⟨199337, by rfl⟩ : syracuseStep 1063133 = 398675) (by norm_num)
theorem B997613 : Blo 662308 997613 := bbase (se 3 (by rfl) ⟨187052, by rfl⟩ : syracuseStep 997613 = 374105) (by norm_num)
theorem B997637 : Blo 662308 997637 := bbase (se 4 (by rfl) ⟨93528, by rfl⟩ : syracuseStep 997637 = 187057) (by norm_num)
theorem B997661 : Blo 662308 997661 := bbase (se 3 (by rfl) ⟨187061, by rfl⟩ : syracuseStep 997661 = 374123) (by norm_num)
theorem B997685 : Blo 662308 997685 := bbase (se 5 (by rfl) ⟨46766, by rfl⟩ : syracuseStep 997685 = 93533) (by norm_num)
theorem B899381 : Blo 662308 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B997709 : Blo 662308 997709 := bbase (se 3 (by rfl) ⟨187070, by rfl⟩ : syracuseStep 997709 = 374141) (by norm_num)
theorem B997733 : Blo 662308 997733 := bbase (se 4 (by rfl) ⟨93537, by rfl⟩ : syracuseStep 997733 = 187075) (by norm_num)
theorem B997757 : Blo 662308 997757 := bbase (se 3 (by rfl) ⟨187079, by rfl⟩ : syracuseStep 997757 = 374159) (by norm_num)
theorem B1685893 : Blo 662308 1685893 := bbase (se 4 (by rfl) ⟨158052, by rfl⟩ : syracuseStep 1685893 = 316105) (by norm_num)
theorem B997781 : Blo 662308 997781 := bbase (se 6 (by rfl) ⟨23385, by rfl⟩ : syracuseStep 997781 = 46771) (by norm_num)
theorem B997805 : Blo 662308 997805 := bbase (se 3 (by rfl) ⟨187088, by rfl⟩ : syracuseStep 997805 = 374177) (by norm_num)
theorem B2242997 : Blo 662308 2242997 := bbase (se 5 (by rfl) ⟨105140, by rfl⟩ : syracuseStep 2242997 = 210281) (by norm_num)
theorem B3357125 : Blo 662308 3357125 := bbase (se 4 (by rfl) ⟨314730, by rfl⟩ : syracuseStep 3357125 = 629461) (by norm_num)
theorem B997829 : Blo 662308 997829 := bbase (se 4 (by rfl) ⟨93546, by rfl⟩ : syracuseStep 997829 = 187093) (by norm_num)
theorem B997853 : Blo 662308 997853 := bbase (se 3 (by rfl) ⟨187097, by rfl⟩ : syracuseStep 997853 = 374195) (by norm_num)
theorem B997877 : Blo 662308 997877 := bbase (se 5 (by rfl) ⟨46775, by rfl⟩ : syracuseStep 997877 = 93551) (by norm_num)
theorem B1686005 : Blo 662308 1686005 := bbase (se 5 (by rfl) ⟨79031, by rfl⟩ : syracuseStep 1686005 = 158063) (by norm_num)
theorem B997901 : Blo 662308 997901 := bbase (se 3 (by rfl) ⟨187106, by rfl⟩ : syracuseStep 997901 = 374213) (by norm_num)
theorem B997925 : Blo 662308 997925 := bbase (se 4 (by rfl) ⟨93555, by rfl⟩ : syracuseStep 997925 = 187111) (by norm_num)
theorem B997949 : Blo 662308 997949 := bbase (se 3 (by rfl) ⟨187115, by rfl⟩ : syracuseStep 997949 = 374231) (by norm_num)
theorem B4536917 : Blo 662308 4536917 := bbase (se 8 (by rfl) ⟨26583, by rfl⟩ : syracuseStep 4536917 = 53167) (by norm_num)
theorem B997973 : Blo 662308 997973 := bbase (se 8 (by rfl) ⟨5847, by rfl⟩ : syracuseStep 997973 = 11695) (by norm_num)
theorem B997997 : Blo 662308 997997 := bbase (se 3 (by rfl) ⟨187124, by rfl⟩ : syracuseStep 997997 = 374249) (by norm_num)
theorem B998021 : Blo 662308 998021 := bbase (se 4 (by rfl) ⟨93564, by rfl⟩ : syracuseStep 998021 = 187129) (by norm_num)
theorem B998045 : Blo 662308 998045 := bbase (se 3 (by rfl) ⟨187133, by rfl⟩ : syracuseStep 998045 = 374267) (by norm_num)
theorem B998069 : Blo 662308 998069 := bbase (se 5 (by rfl) ⟨46784, by rfl⟩ : syracuseStep 998069 = 93569) (by norm_num)
theorem B1686197 : Blo 662308 1686197 := bbase (se 5 (by rfl) ⟨79040, by rfl⟩ : syracuseStep 1686197 = 158081) (by norm_num)
theorem B998093 : Blo 662308 998093 := bbase (se 3 (by rfl) ⟨187142, by rfl⟩ : syracuseStep 998093 = 374285) (by norm_num)
theorem B998117 : Blo 662308 998117 := bbase (se 4 (by rfl) ⟨93573, by rfl⟩ : syracuseStep 998117 = 187147) (by norm_num)
theorem B998141 : Blo 662308 998141 := bbase (se 3 (by rfl) ⟨187151, by rfl⟩ : syracuseStep 998141 = 374303) (by norm_num)
theorem B2833157 : Blo 662308 2833157 := bbase (se 4 (by rfl) ⟨265608, by rfl⟩ : syracuseStep 2833157 = 531217) (by norm_num)
theorem B998165 : Blo 662308 998165 := bbase (se 6 (by rfl) ⟨23394, by rfl⟩ : syracuseStep 998165 = 46789) (by norm_num)
theorem B998189 : Blo 662308 998189 := bbase (se 3 (by rfl) ⟨187160, by rfl⟩ : syracuseStep 998189 = 374321) (by norm_num)
theorem B998213 : Blo 662308 998213 := bbase (se 4 (by rfl) ⟨93582, by rfl⟩ : syracuseStep 998213 = 187165) (by norm_num)
theorem B1260373 : Blo 662308 1260373 := bbase (se 9 (by rfl) ⟨3692, by rfl⟩ : syracuseStep 1260373 = 7385) (by norm_num)
theorem B998237 : Blo 662308 998237 := bbase (se 3 (by rfl) ⟨187169, by rfl⟩ : syracuseStep 998237 = 374339) (by norm_num)
theorem B2243429 : Blo 662308 2243429 := bbase (se 4 (by rfl) ⟨210321, by rfl⟩ : syracuseStep 2243429 = 420643) (by norm_num)
theorem B998261 : Blo 662308 998261 := bbase (se 5 (by rfl) ⟨46793, by rfl⟩ : syracuseStep 998261 = 93587) (by norm_num)
theorem B998285 : Blo 662308 998285 := bbase (se 3 (by rfl) ⟨187178, by rfl⟩ : syracuseStep 998285 = 374357) (by norm_num)
theorem B998309 : Blo 662308 998309 := bbase (se 4 (by rfl) ⟨93591, by rfl⟩ : syracuseStep 998309 = 187183) (by norm_num)
theorem B998333 : Blo 662308 998333 := bbase (se 3 (by rfl) ⟨187187, by rfl⟩ : syracuseStep 998333 = 374375) (by norm_num)
theorem B998357 : Blo 662308 998357 := bbase (se 7 (by rfl) ⟨11699, by rfl⟩ : syracuseStep 998357 = 23399) (by norm_num)
theorem B1260517 : Blo 662308 1260517 := bbase (se 4 (by rfl) ⟨118173, by rfl⟩ : syracuseStep 1260517 = 236347) (by norm_num)
theorem B998381 : Blo 662308 998381 := bbase (se 3 (by rfl) ⟨187196, by rfl⟩ : syracuseStep 998381 = 374393) (by norm_num)
theorem B998405 : Blo 662308 998405 := bbase (se 4 (by rfl) ⟨93600, by rfl⟩ : syracuseStep 998405 = 187201) (by norm_num)
theorem B1686541 : Blo 662308 1686541 := bbase (se 3 (by rfl) ⟨316226, by rfl⟩ : syracuseStep 1686541 = 632453) (by norm_num)
theorem B998429 : Blo 662308 998429 := bbase (se 3 (by rfl) ⟨187205, by rfl⟩ : syracuseStep 998429 = 374411) (by norm_num)
theorem B998453 : Blo 662308 998453 := bbase (se 5 (by rfl) ⟨46802, by rfl⟩ : syracuseStep 998453 = 93605) (by norm_num)
theorem B998477 : Blo 662308 998477 := bbase (se 3 (by rfl) ⟨187214, by rfl⟩ : syracuseStep 998477 = 374429) (by norm_num)
theorem B769109 : Blo 662308 769109 := bbase (se 8 (by rfl) ⟨4506, by rfl⟩ : syracuseStep 769109 = 9013) (by norm_num)
theorem B998501 : Blo 662308 998501 := bbase (se 4 (by rfl) ⟨93609, by rfl⟩ : syracuseStep 998501 = 187219) (by norm_num)
theorem B998525 : Blo 662308 998525 := bbase (se 3 (by rfl) ⟨187223, by rfl⟩ : syracuseStep 998525 = 374447) (by norm_num)
theorem B1260677 : Blo 662308 1260677 := bbase (se 4 (by rfl) ⟨118188, by rfl⟩ : syracuseStep 1260677 = 236377) (by norm_num)
theorem B998549 : Blo 662308 998549 := bbase (se 6 (by rfl) ⟨23403, by rfl⟩ : syracuseStep 998549 = 46807) (by norm_num)
theorem B998573 : Blo 662308 998573 := bbase (se 3 (by rfl) ⟨187232, by rfl⟩ : syracuseStep 998573 = 374465) (by norm_num)
theorem B998597 : Blo 662308 998597 := bbase (se 4 (by rfl) ⟨93618, by rfl⟩ : syracuseStep 998597 = 187237) (by norm_num)
theorem B998621 : Blo 662308 998621 := bbase (se 3 (by rfl) ⟨187241, by rfl⟩ : syracuseStep 998621 = 374483) (by norm_num)
theorem B1195253 : Blo 662308 1195253 := bbase (se 5 (by rfl) ⟨56027, by rfl⟩ : syracuseStep 1195253 = 112055) (by norm_num)
theorem B998645 : Blo 662308 998645 := bbase (se 5 (by rfl) ⟨46811, by rfl⟩ : syracuseStep 998645 = 93623) (by norm_num)
theorem B998669 : Blo 662308 998669 := bbase (se 3 (by rfl) ⟨187250, by rfl⟩ : syracuseStep 998669 = 374501) (by norm_num)
theorem B1260821 : Blo 662308 1260821 := bbase (se 6 (by rfl) ⟨29550, by rfl⟩ : syracuseStep 1260821 = 59101) (by norm_num)
theorem B2243861 : Blo 662308 2243861 := bbase (se 6 (by rfl) ⟨52590, by rfl⟩ : syracuseStep 2243861 = 105181) (by norm_num)
theorem B998693 : Blo 662308 998693 := bbase (se 4 (by rfl) ⟨93627, by rfl⟩ : syracuseStep 998693 = 187255) (by norm_num)
theorem B1490237 : Blo 662308 1490237 := bbase (se 3 (by rfl) ⟨279419, by rfl⟩ : syracuseStep 1490237 = 558839) (by norm_num)
theorem B998717 : Blo 662308 998717 := bbase (se 3 (by rfl) ⟨187259, by rfl⟩ : syracuseStep 998717 = 374519) (by norm_num)
theorem B1064261 : Blo 662308 1064261 := bbase (se 4 (by rfl) ⟨99774, by rfl⟩ : syracuseStep 1064261 = 199549) (by norm_num)
theorem B998741 : Blo 662308 998741 := bbase (se 11 (by rfl) ⟨731, by rfl⟩ : syracuseStep 998741 = 1463) (by norm_num)
theorem B998765 : Blo 662308 998765 := bbase (se 3 (by rfl) ⟨187268, by rfl⟩ : syracuseStep 998765 = 374537) (by norm_num)
theorem B1490309 : Blo 662308 1490309 := bbase (se 4 (by rfl) ⟨139716, by rfl⟩ : syracuseStep 1490309 = 279433) (by norm_num)
theorem B998789 : Blo 662308 998789 := bbase (se 4 (by rfl) ⟨93636, by rfl⟩ : syracuseStep 998789 = 187273) (by norm_num)
theorem B998813 : Blo 662308 998813 := bbase (se 3 (by rfl) ⟨187277, by rfl⟩ : syracuseStep 998813 = 374555) (by norm_num)
theorem B998837 : Blo 662308 998837 := bbase (se 5 (by rfl) ⟨46820, by rfl⟩ : syracuseStep 998837 = 93641) (by norm_num)
theorem B1490381 : Blo 662308 1490381 := bbase (se 3 (by rfl) ⟨279446, by rfl⟩ : syracuseStep 1490381 = 558893) (by norm_num)
theorem B998861 : Blo 662308 998861 := bbase (se 3 (by rfl) ⟨187286, by rfl⟩ : syracuseStep 998861 = 374573) (by norm_num)
theorem B998885 : Blo 662308 998885 := bbase (se 4 (by rfl) ⟨93645, by rfl⟩ : syracuseStep 998885 = 187291) (by norm_num)
theorem B998909 : Blo 662308 998909 := bbase (se 3 (by rfl) ⟨187295, by rfl⟩ : syracuseStep 998909 = 374591) (by norm_num)
theorem B1490453 : Blo 662308 1490453 := bbase (se 6 (by rfl) ⟨34932, by rfl⟩ : syracuseStep 1490453 = 69865) (by norm_num)
theorem B998933 : Blo 662308 998933 := bbase (se 6 (by rfl) ⟨23412, by rfl⟩ : syracuseStep 998933 = 46825) (by norm_num)
theorem B998957 : Blo 662308 998957 := bbase (se 3 (by rfl) ⟨187304, by rfl⟩ : syracuseStep 998957 = 374609) (by norm_num)
theorem B1261109 : Blo 662308 1261109 := bbase (se 5 (by rfl) ⟨59114, by rfl⟩ : syracuseStep 1261109 = 118229) (by norm_num)
theorem B2014789 : Blo 662308 2014789 := bbase (se 4 (by rfl) ⟨188886, by rfl⟩ : syracuseStep 2014789 = 377773) (by norm_num)
theorem B998981 : Blo 662308 998981 := bbase (se 4 (by rfl) ⟨93654, by rfl⟩ : syracuseStep 998981 = 187309) (by norm_num)
theorem B1490525 : Blo 662308 1490525 := bbase (se 3 (by rfl) ⟨279473, by rfl⟩ : syracuseStep 1490525 = 558947) (by norm_num)
theorem B999005 : Blo 662308 999005 := bbase (se 3 (by rfl) ⟨187313, by rfl⟩ : syracuseStep 999005 = 374627) (by norm_num)
theorem B999029 : Blo 662308 999029 := bbase (se 5 (by rfl) ⟨46829, by rfl⟩ : syracuseStep 999029 = 93659) (by norm_num)
theorem B999053 : Blo 662308 999053 := bbase (se 3 (by rfl) ⟨187322, by rfl⟩ : syracuseStep 999053 = 374645) (by norm_num)
theorem B1490597 : Blo 662308 1490597 := bbase (se 4 (by rfl) ⟨139743, by rfl⟩ : syracuseStep 1490597 = 279487) (by norm_num)
theorem B999077 : Blo 662308 999077 := bbase (se 4 (by rfl) ⟨93663, by rfl⟩ : syracuseStep 999077 = 187327) (by norm_num)
theorem B999101 : Blo 662308 999101 := bbase (se 3 (by rfl) ⟨187331, by rfl⟩ : syracuseStep 999101 = 374663) (by norm_num)
theorem B2244293 : Blo 662308 2244293 := bbase (se 4 (by rfl) ⟨210402, by rfl⟩ : syracuseStep 2244293 = 420805) (by norm_num)
theorem B1261261 : Blo 662308 1261261 := bbase (se 3 (by rfl) ⟨236486, by rfl⟩ : syracuseStep 1261261 = 472973) (by norm_num)
theorem B3358421 : Blo 662308 3358421 := bbase (se 7 (by rfl) ⟨39356, by rfl⟩ : syracuseStep 3358421 = 78713) (by norm_num)
theorem B999125 : Blo 662308 999125 := bbase (se 7 (by rfl) ⟨11708, by rfl⟩ : syracuseStep 999125 = 23417) (by norm_num)
theorem B1490669 : Blo 662308 1490669 := bbase (se 3 (by rfl) ⟨279500, by rfl⟩ : syracuseStep 1490669 = 559001) (by norm_num)
theorem B999149 : Blo 662308 999149 := bbase (se 3 (by rfl) ⟨187340, by rfl⟩ : syracuseStep 999149 = 374681) (by norm_num)
theorem B999173 : Blo 662308 999173 := bbase (se 4 (by rfl) ⟨93672, by rfl⟩ : syracuseStep 999173 = 187345) (by norm_num)
theorem B999197 : Blo 662308 999197 := bbase (se 3 (by rfl) ⟨187349, by rfl⟩ : syracuseStep 999197 = 374699) (by norm_num)
theorem B1490741 : Blo 662308 1490741 := bbase (se 5 (by rfl) ⟨69878, by rfl⟩ : syracuseStep 1490741 = 139757) (by norm_num)
theorem B999221 : Blo 662308 999221 := bbase (se 5 (by rfl) ⟨46838, by rfl⟩ : syracuseStep 999221 = 93677) (by norm_num)
theorem B1064773 : Blo 662308 1064773 := bbase (se 4 (by rfl) ⟨99822, by rfl⟩ : syracuseStep 1064773 = 199645) (by norm_num)
theorem B999245 : Blo 662308 999245 := bbase (se 3 (by rfl) ⟨187358, by rfl⟩ : syracuseStep 999245 = 374717) (by norm_num)
theorem B999269 : Blo 662308 999269 := bbase (se 4 (by rfl) ⟨93681, by rfl⟩ : syracuseStep 999269 = 187363) (by norm_num)
theorem B1490813 : Blo 662308 1490813 := bbase (se 3 (by rfl) ⟨279527, by rfl⟩ : syracuseStep 1490813 = 559055) (by norm_num)
theorem B999293 : Blo 662308 999293 := bbase (se 3 (by rfl) ⟨187367, by rfl⟩ : syracuseStep 999293 = 374735) (by norm_num)
theorem B999317 : Blo 662308 999317 := bbase (se 6 (by rfl) ⟨23421, by rfl⟩ : syracuseStep 999317 = 46843) (by norm_num)
theorem B999341 : Blo 662308 999341 := bbase (se 3 (by rfl) ⟨187376, by rfl⟩ : syracuseStep 999341 = 374753) (by norm_num)
theorem B1490885 : Blo 662308 1490885 := bbase (se 4 (by rfl) ⟨139770, by rfl⟩ : syracuseStep 1490885 = 279541) (by norm_num)
theorem B999365 : Blo 662308 999365 := bbase (se 4 (by rfl) ⟨93690, by rfl⟩ : syracuseStep 999365 = 187381) (by norm_num)
theorem B2015189 : Blo 662308 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B999389 : Blo 662308 999389 := bbase (se 3 (by rfl) ⟨187385, by rfl⟩ : syracuseStep 999389 = 374771) (by norm_num)
theorem B999413 : Blo 662308 999413 := bbase (se 5 (by rfl) ⟨46847, by rfl⟩ : syracuseStep 999413 = 93695) (by norm_num)
theorem B1261565 : Blo 662308 1261565 := bbase (se 3 (by rfl) ⟨236543, by rfl⟩ : syracuseStep 1261565 = 473087) (by norm_num)
theorem B1490957 : Blo 662308 1490957 := bbase (se 3 (by rfl) ⟨279554, by rfl⟩ : syracuseStep 1490957 = 559109) (by norm_num)
theorem B999437 : Blo 662308 999437 := bbase (se 3 (by rfl) ⟨187394, by rfl⟩ : syracuseStep 999437 = 374789) (by norm_num)
theorem B999461 : Blo 662308 999461 := bbase (se 4 (by rfl) ⟨93699, by rfl⟩ : syracuseStep 999461 = 187399) (by norm_num)
theorem B1491029 : Blo 662308 1491029 := bbase (se 8 (by rfl) ⟨8736, by rfl⟩ : syracuseStep 1491029 = 17473) (by norm_num)
theorem B2244725 : Blo 662308 2244725 := bbase (se 5 (by rfl) ⟨105221, by rfl⟩ : syracuseStep 2244725 = 210443) (by norm_num)
theorem B1491101 : Blo 662308 1491101 := bbase (se 3 (by rfl) ⟨279581, by rfl⟩ : syracuseStep 1491101 = 559163) (by norm_num)
theorem B1491173 : Blo 662308 1491173 := bbase (se 4 (by rfl) ⟨139797, by rfl⟩ : syracuseStep 1491173 = 279595) (by norm_num)
theorem B1491245 : Blo 662308 1491245 := bbase (se 3 (by rfl) ⟨279608, by rfl⟩ : syracuseStep 1491245 = 559217) (by norm_num)
theorem B1065317 : Blo 662308 1065317 := bbase (se 4 (by rfl) ⟨99873, by rfl⟩ : syracuseStep 1065317 = 199747) (by norm_num)
theorem B1491317 : Blo 662308 1491317 := bbase (se 5 (by rfl) ⟨69905, by rfl⟩ : syracuseStep 1491317 = 139811) (by norm_num)
theorem B5685653 : Blo 662308 5685653 := bbase (se 6 (by rfl) ⟨133257, by rfl⟩ : syracuseStep 5685653 = 266515) (by norm_num)
theorem B1491389 : Blo 662308 1491389 := bbase (se 3 (by rfl) ⟨279635, by rfl⟩ : syracuseStep 1491389 = 559271) (by norm_num)
theorem B1491461 : Blo 662308 1491461 := bbase (se 4 (by rfl) ⟨139824, by rfl⟩ : syracuseStep 1491461 = 279649) (by norm_num)
theorem B3195413 : Blo 662308 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B6242837 : Blo 662308 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B2245157 : Blo 662308 2245157 := bbase (se 4 (by rfl) ⟨210483, by rfl⟩ : syracuseStep 2245157 = 420967) (by norm_num)
theorem B1491533 : Blo 662308 1491533 := bbase (se 3 (by rfl) ⟨279662, by rfl⟩ : syracuseStep 1491533 = 559325) (by norm_num)
theorem B1491605 : Blo 662308 1491605 := bbase (se 6 (by rfl) ⟨34959, by rfl⟩ : syracuseStep 1491605 = 69919) (by norm_num)
theorem B1491677 : Blo 662308 1491677 := bbase (se 3 (by rfl) ⟨279689, by rfl⟩ : syracuseStep 1491677 = 559379) (by norm_num)
theorem B1262317 : Blo 662308 1262317 := bbase (se 3 (by rfl) ⟨236684, by rfl⟩ : syracuseStep 1262317 = 473369) (by norm_num)
theorem B1491749 : Blo 662308 1491749 := bbase (se 4 (by rfl) ⟨139851, by rfl⟩ : syracuseStep 1491749 = 279703) (by norm_num)
theorem B1491821 : Blo 662308 1491821 := bbase (se 3 (by rfl) ⟨279716, by rfl⟩ : syracuseStep 1491821 = 559433) (by norm_num)
theorem B1262461 : Blo 662308 1262461 := bbase (se 3 (by rfl) ⟨236711, by rfl⟩ : syracuseStep 1262461 = 473423) (by norm_num)
theorem B1065869 : Blo 662308 1065869 := bbase (se 3 (by rfl) ⟨199850, by rfl⟩ : syracuseStep 1065869 = 399701) (by norm_num)
theorem B1065901 : Blo 662308 1065901 := bbase (se 3 (by rfl) ⟨199856, by rfl⟩ : syracuseStep 1065901 = 399713) (by norm_num)
theorem B1491893 : Blo 662308 1491893 := bbase (se 5 (by rfl) ⟨69932, by rfl⟩ : syracuseStep 1491893 = 139865) (by norm_num)
theorem B2245589 : Blo 662308 2245589 := bbase (se 7 (by rfl) ⟨26315, by rfl⟩ : syracuseStep 2245589 = 52631) (by norm_num)
theorem B3359717 : Blo 662308 3359717 := bbase (se 4 (by rfl) ⟨314973, by rfl⟩ : syracuseStep 3359717 = 629947) (by norm_num)
theorem B1491965 : Blo 662308 1491965 := bbase (se 3 (by rfl) ⟨279743, by rfl⟩ : syracuseStep 1491965 = 559487) (by norm_num)
theorem B1262621 : Blo 662308 1262621 := bbase (se 3 (by rfl) ⟨236741, by rfl⟩ : syracuseStep 1262621 = 473483) (by norm_num)
theorem B672833 : Blo 662308 672833 := bbase (se 2 (by rfl) ⟨252312, by rfl⟩ : syracuseStep 672833 = 504625) (by norm_num)
theorem B1492037 : Blo 662308 1492037 := bbase (se 4 (by rfl) ⟨139878, by rfl⟩ : syracuseStep 1492037 = 279757) (by norm_num)
theorem B1492109 : Blo 662308 1492109 := bbase (se 3 (by rfl) ⟨279770, by rfl⟩ : syracuseStep 1492109 = 559541) (by norm_num)
theorem B1262765 : Blo 662308 1262765 := bbase (se 3 (by rfl) ⟨236768, by rfl⟩ : syracuseStep 1262765 = 473537) (by norm_num)
theorem B1492181 : Blo 662308 1492181 := bbase (se 7 (by rfl) ⟨17486, by rfl⟩ : syracuseStep 1492181 = 34973) (by norm_num)
theorem B1492253 : Blo 662308 1492253 := bbase (se 3 (by rfl) ⟨279797, by rfl⟩ : syracuseStep 1492253 = 559595) (by norm_num)
theorem B1492325 : Blo 662308 1492325 := bbase (se 4 (by rfl) ⟨139905, by rfl⟩ : syracuseStep 1492325 = 279811) (by norm_num)
theorem B2246021 : Blo 662308 2246021 := bbase (se 4 (by rfl) ⟨210564, by rfl⟩ : syracuseStep 2246021 = 421129) (by norm_num)
theorem B1492397 : Blo 662308 1492397 := bbase (se 3 (by rfl) ⟨279824, by rfl⟩ : syracuseStep 1492397 = 559649) (by norm_num)
theorem B1263053 : Blo 662308 1263053 := bbase (se 3 (by rfl) ⟨236822, by rfl⟩ : syracuseStep 1263053 = 473645) (by norm_num)
theorem B10765781 : Blo 662308 10765781 := bbase (se 7 (by rfl) ⟨126161, by rfl⟩ : syracuseStep 10765781 = 252323) (by norm_num)
theorem B3032549 : Blo 662308 3032549 := bbase (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) (by norm_num)
theorem B1492469 : Blo 662308 1492469 := bbase (se 5 (by rfl) ⟨69959, by rfl⟩ : syracuseStep 1492469 = 139919) (by norm_num)
theorem B1492541 : Blo 662308 1492541 := bbase (se 3 (by rfl) ⟨279851, by rfl⟩ : syracuseStep 1492541 = 559703) (by norm_num)
theorem B673381 : Blo 662308 673381 := bbase (se 4 (by rfl) ⟨63129, by rfl⟩ : syracuseStep 673381 = 126259) (by norm_num)
theorem B1263205 : Blo 662308 1263205 := bbase (se 4 (by rfl) ⟨118425, by rfl⟩ : syracuseStep 1263205 = 236851) (by norm_num)
theorem B1492613 : Blo 662308 1492613 := bbase (se 4 (by rfl) ⟨139932, by rfl⟩ : syracuseStep 1492613 = 279865) (by norm_num)
theorem B4245173 : Blo 662308 4245173 := bbase (se 5 (by rfl) ⟨198992, by rfl⟩ : syracuseStep 4245173 = 397985) (by norm_num)
theorem B1492685 : Blo 662308 1492685 := bbase (se 3 (by rfl) ⟨279878, by rfl⟩ : syracuseStep 1492685 = 559757) (by norm_num)
theorem B1492757 : Blo 662308 1492757 := bbase (se 6 (by rfl) ⟨34986, by rfl⟩ : syracuseStep 1492757 = 69973) (by norm_num)
theorem B1361693 : Blo 662308 1361693 := bbase (se 3 (by rfl) ⟨255317, by rfl⟩ : syracuseStep 1361693 = 510635) (by norm_num)
theorem B2246453 : Blo 662308 2246453 := bbase (se 5 (by rfl) ⟨105302, by rfl⟩ : syracuseStep 2246453 = 210605) (by norm_num)
theorem B1066829 : Blo 662308 1066829 := bbase (se 3 (by rfl) ⟨200030, by rfl⟩ : syracuseStep 1066829 = 400061) (by norm_num)
theorem B1492829 : Blo 662308 1492829 := bbase (se 3 (by rfl) ⟨279905, by rfl⟩ : syracuseStep 1492829 = 559811) (by norm_num)
theorem B1263509 : Blo 662308 1263509 := bbase (se 6 (by rfl) ⟨29613, by rfl⟩ : syracuseStep 1263509 = 59227) (by norm_num)
theorem B1492901 : Blo 662308 1492901 := bbase (se 4 (by rfl) ⟨139959, by rfl⟩ : syracuseStep 1492901 = 279919) (by norm_num)
theorem B1492973 : Blo 662308 1492973 := bbase (se 3 (by rfl) ⟨279932, by rfl⟩ : syracuseStep 1492973 = 559865) (by norm_num)
theorem B1493045 : Blo 662308 1493045 := bbase (se 5 (by rfl) ⟨69986, by rfl⟩ : syracuseStep 1493045 = 139973) (by norm_num)
theorem B1198165 : Blo 662308 1198165 := bbase (se 8 (by rfl) ⟨7020, by rfl⟩ : syracuseStep 1198165 = 14041) (by norm_num)
theorem B3197029 : Blo 662308 3197029 := bbase (se 4 (by rfl) ⟨299721, by rfl⟩ : syracuseStep 3197029 = 599443) (by norm_num)
theorem B1493117 : Blo 662308 1493117 := bbase (se 3 (by rfl) ⟨279959, by rfl⟩ : syracuseStep 1493117 = 559919) (by norm_num)
theorem B1198237 : Blo 662308 1198237 := bbase (se 3 (by rfl) ⟨224669, by rfl⟩ : syracuseStep 1198237 = 449339) (by norm_num)
theorem B1493189 : Blo 662308 1493189 := bbase (se 4 (by rfl) ⟨139986, by rfl⟩ : syracuseStep 1493189 = 279973) (by norm_num)
theorem B2246885 : Blo 662308 2246885 := bbase (se 4 (by rfl) ⟨210645, by rfl⟩ : syracuseStep 2246885 = 421291) (by norm_num)
theorem B3361013 : Blo 662308 3361013 := bbase (se 5 (by rfl) ⟨157547, by rfl⟩ : syracuseStep 3361013 = 315095) (by norm_num)
theorem B1493261 : Blo 662308 1493261 := bbase (se 3 (by rfl) ⟨279986, by rfl⟩ : syracuseStep 1493261 = 559973) (by norm_num)
theorem B674065 : Blo 662308 674065 := bbase (se 2 (by rfl) ⟨252774, by rfl⟩ : syracuseStep 674065 = 505549) (by norm_num)
theorem B1493333 : Blo 662308 1493333 := bbase (se 10 (by rfl) ⟨2187, by rfl⟩ : syracuseStep 1493333 = 4375) (by norm_num)
theorem B1198469 : Blo 662308 1198469 := bbase (se 4 (by rfl) ⟨112356, by rfl⟩ : syracuseStep 1198469 = 224713) (by norm_num)
theorem B1591709 : Blo 662308 1591709 := bbase (se 3 (by rfl) ⟨298445, by rfl⟩ : syracuseStep 1591709 = 596891) (by norm_num)
theorem B1493405 : Blo 662308 1493405 := bbase (se 3 (by rfl) ⟨280013, by rfl⟩ : syracuseStep 1493405 = 560027) (by norm_num)
theorem B1296821 : Blo 662308 1296821 := bbase (se 5 (by rfl) ⟨60788, by rfl⟩ : syracuseStep 1296821 = 121577) (by norm_num)
theorem B1493477 : Blo 662308 1493477 := bbase (se 4 (by rfl) ⟨140013, by rfl⟩ : syracuseStep 1493477 = 280027) (by norm_num)
theorem B1493549 : Blo 662308 1493549 := bbase (se 3 (by rfl) ⟨280040, by rfl⟩ : syracuseStep 1493549 = 560081) (by norm_num)
theorem B1886789 : Blo 662308 1886789 := bbase (se 4 (by rfl) ⟨176886, by rfl⟩ : syracuseStep 1886789 = 353773) (by norm_num)
theorem B1493621 : Blo 662308 1493621 := bbase (se 5 (by rfl) ⟨70013, by rfl⟩ : syracuseStep 1493621 = 140027) (by norm_num)
theorem B1264261 : Blo 662308 1264261 := bbase (se 4 (by rfl) ⟨118524, by rfl⟩ : syracuseStep 1264261 = 237049) (by norm_num)
theorem B838289 : Blo 662308 838289 := bbase (se 2 (by rfl) ⟨314358, by rfl⟩ : syracuseStep 838289 = 628717) (by norm_num)
theorem B2247317 : Blo 662308 2247317 := bbase (se 6 (by rfl) ⟨52671, by rfl⟩ : syracuseStep 2247317 = 105343) (by norm_num)
theorem B1493693 : Blo 662308 1493693 := bbase (se 3 (by rfl) ⟨280067, by rfl⟩ : syracuseStep 1493693 = 560135) (by norm_num)
theorem B838345 : Blo 662308 838345 := bbase (se 2 (by rfl) ⟨314379, by rfl⟩ : syracuseStep 838345 = 628759) (by norm_num)
theorem B1493765 : Blo 662308 1493765 := bbase (se 4 (by rfl) ⟨140040, by rfl⟩ : syracuseStep 1493765 = 280081) (by norm_num)
theorem B707341 : Blo 662308 707341 := bbase (se 3 (by rfl) ⟨132626, by rfl⟩ : syracuseStep 707341 = 265253) (by norm_num)
theorem B8506133 : Blo 662308 8506133 := bbase (se 6 (by rfl) ⟨199362, by rfl⟩ : syracuseStep 8506133 = 398725) (by norm_num)
theorem B1264405 : Blo 662308 1264405 := bbase (se 6 (by rfl) ⟨29634, by rfl⟩ : syracuseStep 1264405 = 59269) (by norm_num)
theorem B838441 : Blo 662308 838441 := bbase (se 2 (by rfl) ⟨314415, by rfl⟩ : syracuseStep 838441 = 628831) (by norm_num)
theorem B707401 : Blo 662308 707401 := bbase (se 2 (by rfl) ⟨265275, by rfl⟩ : syracuseStep 707401 = 530551) (by norm_num)
theorem B1493837 : Blo 662308 1493837 := bbase (se 3 (by rfl) ⟨280094, by rfl⟩ : syracuseStep 1493837 = 560189) (by norm_num)
theorem B1493909 : Blo 662308 1493909 := bbase (se 6 (by rfl) ⟨35013, by rfl⟩ : syracuseStep 1493909 = 70027) (by norm_num)
theorem B2837429 : Blo 662308 2837429 := bbase (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) (by norm_num)
theorem B1264565 : Blo 662308 1264565 := bbase (se 5 (by rfl) ⟨59276, by rfl⟩ : syracuseStep 1264565 = 118553) (by norm_num)
theorem B838613 : Blo 662308 838613 := bbase (se 7 (by rfl) ⟨9827, by rfl⟩ : syracuseStep 838613 = 19655) (by norm_num)
theorem B674777 : Blo 662308 674777 := bbase (se 2 (by rfl) ⟨253041, by rfl⟩ : syracuseStep 674777 = 506083) (by norm_num)
theorem B1493981 : Blo 662308 1493981 := bbase (se 3 (by rfl) ⟨280121, by rfl⟩ : syracuseStep 1493981 = 560243) (by norm_num)
theorem B838669 : Blo 662308 838669 := bbase (se 3 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 838669 = 314501) (by norm_num)
theorem B1494053 : Blo 662308 1494053 := bbase (se 4 (by rfl) ⟨140067, by rfl⟩ : syracuseStep 1494053 = 280135) (by norm_num)
theorem B2247749 : Blo 662308 2247749 := bbase (se 4 (by rfl) ⟨210726, by rfl⟩ : syracuseStep 2247749 = 421453) (by norm_num)
theorem B1264709 : Blo 662308 1264709 := bbase (se 4 (by rfl) ⟨118566, by rfl⟩ : syracuseStep 1264709 = 237133) (by norm_num)
theorem B674893 : Blo 662308 674893 := bbase (se 3 (by rfl) ⟨126542, by rfl⟩ : syracuseStep 674893 = 253085) (by norm_num)
theorem B838765 : Blo 662308 838765 := bbase (se 3 (by rfl) ⟨157268, by rfl⟩ : syracuseStep 838765 = 314537) (by norm_num)
theorem B1494125 : Blo 662308 1494125 := bbase (se 3 (by rfl) ⟨280148, by rfl⟩ : syracuseStep 1494125 = 560297) (by norm_num)
theorem B674941 : Blo 662308 674941 := bbase (se 3 (by rfl) ⟨126551, by rfl⟩ : syracuseStep 674941 = 253103) (by norm_num)
theorem B707717 : Blo 662308 707717 := bbase (se 4 (by rfl) ⟨66348, by rfl⟩ : syracuseStep 707717 = 132697) (by norm_num)
theorem B1199261 : Blo 662308 1199261 := bbase (se 3 (by rfl) ⟨224861, by rfl⟩ : syracuseStep 1199261 = 449723) (by norm_num)
theorem B1494197 : Blo 662308 1494197 := bbase (se 5 (by rfl) ⟨70040, by rfl⟩ : syracuseStep 1494197 = 140081) (by norm_num)
theorem B1494269 : Blo 662308 1494269 := bbase (se 3 (by rfl) ⟨280175, by rfl⟩ : syracuseStep 1494269 = 560351) (by norm_num)
theorem B838937 : Blo 662308 838937 := bbase (se 2 (by rfl) ⟨314601, by rfl⟩ : syracuseStep 838937 = 629203) (by norm_num)
theorem B5688629 : Blo 662308 5688629 := bbase (se 5 (by rfl) ⟨266654, by rfl⟩ : syracuseStep 5688629 = 533309) (by norm_num)
theorem B1494341 : Blo 662308 1494341 := bbase (se 4 (by rfl) ⟨140094, by rfl⟩ : syracuseStep 1494341 = 280189) (by norm_num)
theorem B838993 : Blo 662308 838993 := bbase (se 2 (by rfl) ⟨314622, by rfl⟩ : syracuseStep 838993 = 629245) (by norm_num)
theorem B1494413 : Blo 662308 1494413 := bbase (se 3 (by rfl) ⟨280202, by rfl⟩ : syracuseStep 1494413 = 560405) (by norm_num)
theorem B839089 : Blo 662308 839089 := bbase (se 2 (by rfl) ⟨314658, by rfl⟩ : syracuseStep 839089 = 629317) (by norm_num)
theorem B1199549 : Blo 662308 1199549 := bbase (se 3 (by rfl) ⟨224915, by rfl⟩ : syracuseStep 1199549 = 449831) (by norm_num)
theorem B2870741 : Blo 662308 2870741 := bbase (se 7 (by rfl) ⟨33641, by rfl⟩ : syracuseStep 2870741 = 67283) (by norm_num)
theorem B24202709 : Blo 662308 24202709 := bbase (se 7 (by rfl) ⟨283625, by rfl⟩ : syracuseStep 24202709 = 567251) (by norm_num)
theorem B1494485 : Blo 662308 1494485 := bbase (se 7 (by rfl) ⟨17513, by rfl⟩ : syracuseStep 1494485 = 35027) (by norm_num)
theorem B2248181 : Blo 662308 2248181 := bbase (se 5 (by rfl) ⟨105383, by rfl⟩ : syracuseStep 2248181 = 210767) (by norm_num)
theorem B3362309 : Blo 662308 3362309 := bbase (se 4 (by rfl) ⟨315216, by rfl⟩ : syracuseStep 3362309 = 630433) (by norm_num)
theorem B1199621 : Blo 662308 1199621 := bbase (se 4 (by rfl) ⟨112464, by rfl⟩ : syracuseStep 1199621 = 224929) (by norm_num)
theorem B1494557 : Blo 662308 1494557 := bbase (se 3 (by rfl) ⟨280229, by rfl⟩ : syracuseStep 1494557 = 560459) (by norm_num)
theorem B708161 : Blo 662308 708161 := bbase (se 2 (by rfl) ⟨265560, by rfl⟩ : syracuseStep 708161 = 531121) (by norm_num)
theorem B839261 : Blo 662308 839261 := bbase (se 3 (by rfl) ⟨157361, by rfl⟩ : syracuseStep 839261 = 314723) (by norm_num)
theorem B1494629 : Blo 662308 1494629 := bbase (se 4 (by rfl) ⟨140121, by rfl⟩ : syracuseStep 1494629 = 280243) (by norm_num)
theorem B708221 : Blo 662308 708221 := bbase (se 3 (by rfl) ⟨132791, by rfl⟩ : syracuseStep 708221 = 265583) (by norm_num)
theorem B839317 : Blo 662308 839317 := bbase (se 6 (by rfl) ⟨19671, by rfl⟩ : syracuseStep 839317 = 39343) (by norm_num)
theorem B1494701 : Blo 662308 1494701 := bbase (se 3 (by rfl) ⟨280256, by rfl⟩ : syracuseStep 1494701 = 560513) (by norm_num)
theorem B839413 : Blo 662308 839413 := bbase (se 5 (by rfl) ⟨39347, by rfl⟩ : syracuseStep 839413 = 78695) (by norm_num)
theorem B1494773 : Blo 662308 1494773 := bbase (se 5 (by rfl) ⟨70067, by rfl⟩ : syracuseStep 1494773 = 140135) (by norm_num)
theorem B708349 : Blo 662308 708349 := bbase (se 3 (by rfl) ⟨132815, by rfl⟩ : syracuseStep 708349 = 265631) (by norm_num)
theorem B1494845 : Blo 662308 1494845 := bbase (se 3 (by rfl) ⟨280283, by rfl⟩ : syracuseStep 1494845 = 560567) (by norm_num)
theorem B1494917 : Blo 662308 1494917 := bbase (se 4 (by rfl) ⟨140148, by rfl⟩ : syracuseStep 1494917 = 280297) (by norm_num)
theorem B839585 : Blo 662308 839585 := bbase (se 2 (by rfl) ⟨314844, by rfl⟩ : syracuseStep 839585 = 629689) (by norm_num)
theorem B2248613 : Blo 662308 2248613 := bbase (se 4 (by rfl) ⟨210807, by rfl⟩ : syracuseStep 2248613 = 421615) (by norm_num)
theorem B1494989 : Blo 662308 1494989 := bbase (se 3 (by rfl) ⟨280310, by rfl⟩ : syracuseStep 1494989 = 560621) (by norm_num)
theorem B839641 : Blo 662308 839641 := bbase (se 2 (by rfl) ⟨314865, by rfl⟩ : syracuseStep 839641 = 629731) (by norm_num)
theorem B1495061 : Blo 662308 1495061 := bbase (se 6 (by rfl) ⟨35040, by rfl⟩ : syracuseStep 1495061 = 70081) (by norm_num)
theorem B839737 : Blo 662308 839737 := bbase (se 2 (by rfl) ⟨314901, by rfl⟩ : syracuseStep 839737 = 629803) (by norm_num)
theorem B1495133 : Blo 662308 1495133 := bbase (se 3 (by rfl) ⟨280337, by rfl⟩ : syracuseStep 1495133 = 560675) (by norm_num)
theorem B1888373 : Blo 662308 1888373 := bbase (se 5 (by rfl) ⟨88517, by rfl⟩ : syracuseStep 1888373 = 177035) (by norm_num)
theorem B1593469 : Blo 662308 1593469 := bbase (se 3 (by rfl) ⟨298775, by rfl⟩ : syracuseStep 1593469 = 597551) (by norm_num)
theorem B1495205 : Blo 662308 1495205 := bbase (se 4 (by rfl) ⟨140175, by rfl⟩ : syracuseStep 1495205 = 280351) (by norm_num)
theorem B708793 : Blo 662308 708793 := bbase (se 2 (by rfl) ⟨265797, by rfl⟩ : syracuseStep 708793 = 531595) (by norm_num)
theorem B839909 : Blo 662308 839909 := bbase (se 4 (by rfl) ⟨78741, by rfl⟩ : syracuseStep 839909 = 157483) (by norm_num)
theorem B1495277 : Blo 662308 1495277 := bbase (se 3 (by rfl) ⟨280364, by rfl⟩ : syracuseStep 1495277 = 560729) (by norm_num)
theorem B839965 : Blo 662308 839965 := bbase (se 3 (by rfl) ⟨157493, by rfl⟩ : syracuseStep 839965 = 314987) (by norm_num)
theorem B708913 : Blo 662308 708913 := bbase (se 2 (by rfl) ⟨265842, by rfl⟩ : syracuseStep 708913 = 531685) (by norm_num)
theorem B1495349 : Blo 662308 1495349 := bbase (se 5 (by rfl) ⟨70094, by rfl⟩ : syracuseStep 1495349 = 140189) (by norm_num)
theorem B1593701 : Blo 662308 1593701 := bbase (se 4 (by rfl) ⟨149409, by rfl⟩ : syracuseStep 1593701 = 298819) (by norm_num)
theorem B840061 : Blo 662308 840061 := bbase (se 3 (by rfl) ⟨157511, by rfl⟩ : syracuseStep 840061 = 315023) (by norm_num)
theorem B1495421 : Blo 662308 1495421 := bbase (se 3 (by rfl) ⟨280391, by rfl⟩ : syracuseStep 1495421 = 560783) (by norm_num)
theorem B1495493 : Blo 662308 1495493 := bbase (se 4 (by rfl) ⟨140202, by rfl⟩ : syracuseStep 1495493 = 280405) (by norm_num)
theorem B1495565 : Blo 662308 1495565 := bbase (se 3 (by rfl) ⟨280418, by rfl⟩ : syracuseStep 1495565 = 560837) (by norm_num)
theorem B840233 : Blo 662308 840233 := bbase (se 2 (by rfl) ⟨315087, by rfl⟩ : syracuseStep 840233 = 630175) (by norm_num)
theorem B709165 : Blo 662308 709165 := bbase (se 3 (by rfl) ⟨132968, by rfl⟩ : syracuseStep 709165 = 265937) (by norm_num)
theorem B709169 : Blo 662308 709169 := bbase (se 2 (by rfl) ⟨265938, by rfl⟩ : syracuseStep 709169 = 531877) (by norm_num)
theorem B1495637 : Blo 662308 1495637 := bbase (se 8 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 1495637 = 17527) (by norm_num)
theorem B840289 : Blo 662308 840289 := bbase (se 2 (by rfl) ⟨315108, by rfl⟩ : syracuseStep 840289 = 630217) (by norm_num)
theorem B1495709 : Blo 662308 1495709 := bbase (se 3 (by rfl) ⟨280445, by rfl⟩ : syracuseStep 1495709 = 560891) (by norm_num)
theorem B2839205 : Blo 662308 2839205 := bbase (se 4 (by rfl) ⟨266175, by rfl⟩ : syracuseStep 2839205 = 532351) (by norm_num)
theorem B840385 : Blo 662308 840385 := bbase (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) (by norm_num)
theorem B1495781 : Blo 662308 1495781 := bbase (se 4 (by rfl) ⟨140229, by rfl⟩ : syracuseStep 1495781 = 280459) (by norm_num)
theorem B1594093 : Blo 662308 1594093 := bbase (se 3 (by rfl) ⟨298892, by rfl⟩ : syracuseStep 1594093 = 597785) (by norm_num)
theorem B1889045 : Blo 662308 1889045 := bbase (se 6 (by rfl) ⟨44274, by rfl⟩ : syracuseStep 1889045 = 88549) (by norm_num)
theorem B3363605 : Blo 662308 3363605 := bbase (se 6 (by rfl) ⟨78834, by rfl⟩ : syracuseStep 3363605 = 157669) (by norm_num)
theorem B1495853 : Blo 662308 1495853 := bbase (se 3 (by rfl) ⟨280472, by rfl⟩ : syracuseStep 1495853 = 560945) (by norm_num)
theorem B1299253 : Blo 662308 1299253 := bbase (se 5 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 1299253 = 121805) (by norm_num)
theorem B19452757 : Blo 662308 19452757 := bbase (se 9 (by rfl) ⟨56990, by rfl⟩ : syracuseStep 19452757 = 113981) (by norm_num)
theorem B840557 : Blo 662308 840557 := bbase (se 3 (by rfl) ⟨157604, by rfl⟩ : syracuseStep 840557 = 315209) (by norm_num)
theorem B1495925 : Blo 662308 1495925 := bbase (se 5 (by rfl) ⟨70121, by rfl⟩ : syracuseStep 1495925 = 140243) (by norm_num)
theorem B2839445 : Blo 662308 2839445 := bbase (se 6 (by rfl) ⟨66549, by rfl⟩ : syracuseStep 2839445 = 133099) (by norm_num)
theorem B840613 : Blo 662308 840613 := bbase (se 4 (by rfl) ⟨78807, by rfl⟩ : syracuseStep 840613 = 157615) (by norm_num)
theorem B1495997 : Blo 662308 1495997 := bbase (se 3 (by rfl) ⟨280499, by rfl⟩ : syracuseStep 1495997 = 560999) (by norm_num)
theorem B840709 : Blo 662308 840709 := bbase (se 4 (by rfl) ⟨78816, by rfl⟩ : syracuseStep 840709 = 157633) (by norm_num)
theorem B1496069 : Blo 662308 1496069 := bbase (se 4 (by rfl) ⟨140256, by rfl⟩ : syracuseStep 1496069 = 280513) (by norm_num)
theorem B2020373 : Blo 662308 2020373 := bbase (se 6 (by rfl) ⟨47352, by rfl⟩ : syracuseStep 2020373 = 94705) (by norm_num)
theorem B1496141 : Blo 662308 1496141 := bbase (se 3 (by rfl) ⟨280526, by rfl⟩ : syracuseStep 1496141 = 561053) (by norm_num)
theorem B709733 : Blo 662308 709733 := bbase (se 4 (by rfl) ⟨66537, by rfl⟩ : syracuseStep 709733 = 133075) (by norm_num)
theorem B1496213 : Blo 662308 1496213 := bbase (se 6 (by rfl) ⟨35067, by rfl⟩ : syracuseStep 1496213 = 70135) (by norm_num)
theorem B840881 : Blo 662308 840881 := bbase (se 2 (by rfl) ⟨315330, by rfl⟩ : syracuseStep 840881 = 630661) (by norm_num)
theorem B1889477 : Blo 662308 1889477 := bbase (se 4 (by rfl) ⟨177138, by rfl⟩ : syracuseStep 1889477 = 354277) (by norm_num)
theorem B1496285 : Blo 662308 1496285 := bbase (se 3 (by rfl) ⟨280553, by rfl⟩ : syracuseStep 1496285 = 561107) (by norm_num)
theorem B840937 : Blo 662308 840937 := bbase (se 2 (by rfl) ⟨315351, by rfl⟩ : syracuseStep 840937 = 630703) (by norm_num)
theorem B7165205 : Blo 662308 7165205 := bbase (se 6 (by rfl) ⟨167934, by rfl⟩ : syracuseStep 7165205 = 335869) (by norm_num)
theorem B709921 : Blo 662308 709921 := bbase (se 2 (by rfl) ⟨266220, by rfl⟩ : syracuseStep 709921 = 532441) (by norm_num)
theorem B1496357 : Blo 662308 1496357 := bbase (se 4 (by rfl) ⟨140283, by rfl⟩ : syracuseStep 1496357 = 280567) (by norm_num)
theorem B841033 : Blo 662308 841033 := bbase (se 2 (by rfl) ⟨315387, by rfl⟩ : syracuseStep 841033 = 630775) (by norm_num)
theorem B1496429 : Blo 662308 1496429 := bbase (se 3 (by rfl) ⟨280580, by rfl⟩ : syracuseStep 1496429 = 561161) (by norm_num)
theorem B5035445 : Blo 662308 5035445 := bbase (se 5 (by rfl) ⟨236036, by rfl⟩ : syracuseStep 5035445 = 472073) (by norm_num)
theorem B1496501 : Blo 662308 1496501 := bbase (se 5 (by rfl) ⟨70148, by rfl⟩ : syracuseStep 1496501 = 140297) (by norm_num)
theorem B808385 : Blo 662308 808385 := bbase (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) (by norm_num)
theorem B841205 : Blo 662308 841205 := bbase (se 5 (by rfl) ⟨39431, by rfl⟩ : syracuseStep 841205 = 78863) (by norm_num)
theorem B1496573 : Blo 662308 1496573 := bbase (se 3 (by rfl) ⟨280607, by rfl⟩ : syracuseStep 1496573 = 561215) (by norm_num)
theorem B841261 : Blo 662308 841261 := bbase (se 3 (by rfl) ⟨157736, by rfl⟩ : syracuseStep 841261 = 315473) (by norm_num)
theorem B1496645 : Blo 662308 1496645 := bbase (se 4 (by rfl) ⟨140310, by rfl⟩ : syracuseStep 1496645 = 280621) (by norm_num)
theorem B841357 : Blo 662308 841357 := bbase (se 3 (by rfl) ⟨157754, by rfl⟩ : syracuseStep 841357 = 315509) (by norm_num)
theorem B1496717 : Blo 662308 1496717 := bbase (se 3 (by rfl) ⟨280634, by rfl⟩ : syracuseStep 1496717 = 561269) (by norm_num)
theorem B1496789 : Blo 662308 1496789 := bbase (se 7 (by rfl) ⟨17540, by rfl⟩ : syracuseStep 1496789 = 35081) (by norm_num)
theorem B1496861 : Blo 662308 1496861 := bbase (se 3 (by rfl) ⟨280661, by rfl⟩ : syracuseStep 1496861 = 561323) (by norm_num)
theorem B1595189 : Blo 662308 1595189 := bbase (se 5 (by rfl) ⟨74774, by rfl⟩ : syracuseStep 1595189 = 149549) (by norm_num)
theorem B841529 : Blo 662308 841529 := bbase (se 2 (by rfl) ⟨315573, by rfl⟩ : syracuseStep 841529 = 631147) (by norm_num)
theorem B1496933 : Blo 662308 1496933 := bbase (se 4 (by rfl) ⟨140337, by rfl⟩ : syracuseStep 1496933 = 280675) (by norm_num)
theorem B841585 : Blo 662308 841585 := bbase (se 2 (by rfl) ⟨315594, by rfl⟩ : syracuseStep 841585 = 631189) (by norm_num)
theorem B3790709 : Blo 662308 3790709 := bbase (se 5 (by rfl) ⟨177689, by rfl⟩ : syracuseStep 3790709 = 355379) (by norm_num)
theorem B1497005 : Blo 662308 1497005 := bbase (se 3 (by rfl) ⟨280688, by rfl⟩ : syracuseStep 1497005 = 561377) (by norm_num)
theorem B1890229 : Blo 662308 1890229 := bbase (se 5 (by rfl) ⟨88604, by rfl⟩ : syracuseStep 1890229 = 177209) (by norm_num)
theorem B841681 : Blo 662308 841681 := bbase (se 2 (by rfl) ⟨315630, by rfl⟩ : syracuseStep 841681 = 631261) (by norm_num)
theorem B1497077 : Blo 662308 1497077 := bbase (se 5 (by rfl) ⟨70175, by rfl⟩ : syracuseStep 1497077 = 140351) (by norm_num)
theorem B3364901 : Blo 662308 3364901 := bbase (se 4 (by rfl) ⟨315459, by rfl⟩ : syracuseStep 3364901 = 630919) (by norm_num)
theorem B1497149 : Blo 662308 1497149 := bbase (se 3 (by rfl) ⟨280715, by rfl⟩ : syracuseStep 1497149 = 561431) (by norm_num)
theorem B1595477 : Blo 662308 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B710741 : Blo 662308 710741 := bbase (se 8 (by rfl) ⟨4164, by rfl⟩ : syracuseStep 710741 = 8329) (by norm_num)
theorem B841853 : Blo 662308 841853 := bbase (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) (by norm_num)
theorem B1497221 : Blo 662308 1497221 := bbase (se 4 (by rfl) ⟨140364, by rfl⟩ : syracuseStep 1497221 = 280729) (by norm_num)
theorem B1136773 : Blo 662308 1136773 := bbase (se 4 (by rfl) ⟨106572, by rfl⟩ : syracuseStep 1136773 = 213145) (by norm_num)
theorem B841909 : Blo 662308 841909 := bbase (se 5 (by rfl) ⟨39464, by rfl⟩ : syracuseStep 841909 = 78929) (by norm_num)
theorem B1497293 : Blo 662308 1497293 := bbase (se 3 (by rfl) ⟨280742, by rfl⟩ : syracuseStep 1497293 = 561485) (by norm_num)
theorem B1366253 : Blo 662308 1366253 := bbase (se 3 (by rfl) ⟨256172, by rfl⟩ : syracuseStep 1366253 = 512345) (by norm_num)
theorem B842005 : Blo 662308 842005 := bbase (se 6 (by rfl) ⟨19734, by rfl⟩ : syracuseStep 842005 = 39469) (by norm_num)
theorem B1497365 : Blo 662308 1497365 := bbase (se 6 (by rfl) ⟨35094, by rfl⟩ : syracuseStep 1497365 = 70189) (by norm_num)
theorem B1136933 : Blo 662308 1136933 := bbase (se 4 (by rfl) ⟨106587, by rfl⟩ : syracuseStep 1136933 = 213175) (by norm_num)
theorem B1497437 : Blo 662308 1497437 := bbase (se 3 (by rfl) ⟨280769, by rfl⟩ : syracuseStep 1497437 = 561539) (by norm_num)
theorem B1497509 : Blo 662308 1497509 := bbase (se 4 (by rfl) ⟨140391, by rfl⟩ : syracuseStep 1497509 = 280783) (by norm_num)
theorem B842177 : Blo 662308 842177 := bbase (se 2 (by rfl) ⟨315816, by rfl⟩ : syracuseStep 842177 = 631633) (by norm_num)
theorem B1497581 : Blo 662308 1497581 := bbase (se 3 (by rfl) ⟨280796, by rfl⟩ : syracuseStep 1497581 = 561593) (by norm_num)
theorem B842233 : Blo 662308 842233 := bbase (se 2 (by rfl) ⟨315837, by rfl⟩ : syracuseStep 842233 = 631675) (by norm_num)
theorem B711185 : Blo 662308 711185 := bbase (se 2 (by rfl) ⟨266694, by rfl⟩ : syracuseStep 711185 = 533389) (by norm_num)
theorem B1497653 : Blo 662308 1497653 := bbase (se 5 (by rfl) ⟨70202, by rfl⟩ : syracuseStep 1497653 = 140405) (by norm_num)
theorem B842329 : Blo 662308 842329 := bbase (se 2 (by rfl) ⟨315873, by rfl⟩ : syracuseStep 842329 = 631747) (by norm_num)
theorem B1497725 : Blo 662308 1497725 := bbase (se 3 (by rfl) ⟨280823, by rfl⟩ : syracuseStep 1497725 = 561647) (by norm_num)
theorem B1497797 : Blo 662308 1497797 := bbase (se 4 (by rfl) ⟨140418, by rfl⟩ : syracuseStep 1497797 = 280837) (by norm_num)
theorem B842501 : Blo 662308 842501 := bbase (se 4 (by rfl) ⟨78984, by rfl⟩ : syracuseStep 842501 = 157969) (by norm_num)
theorem B711433 : Blo 662308 711433 := bbase (se 2 (by rfl) ⟨266787, by rfl⟩ : syracuseStep 711433 = 533575) (by norm_num)
theorem B1497869 : Blo 662308 1497869 := bbase (se 3 (by rfl) ⟨280850, by rfl⟩ : syracuseStep 1497869 = 561701) (by norm_num)
theorem B842557 : Blo 662308 842557 := bbase (se 3 (by rfl) ⟨157979, by rfl⟩ : syracuseStep 842557 = 315959) (by norm_num)
theorem B1497941 : Blo 662308 1497941 := bbase (se 9 (by rfl) ⟨4388, by rfl⟩ : syracuseStep 1497941 = 8777) (by norm_num)
theorem B1498013 : Blo 662308 1498013 := bbase (se 3 (by rfl) ⟨280877, by rfl⟩ : syracuseStep 1498013 = 561755) (by norm_num)
theorem B842653 : Blo 662308 842653 := bbase (se 3 (by rfl) ⟨157997, by rfl⟩ : syracuseStep 842653 = 315995) (by norm_num)
theorem B1498085 : Blo 662308 1498085 := bbase (se 4 (by rfl) ⟨140445, by rfl⟩ : syracuseStep 1498085 = 280891) (by norm_num)
theorem B3791893 : Blo 662308 3791893 := bbase (se 6 (by rfl) ⟨88872, by rfl⟩ : syracuseStep 3791893 = 177745) (by norm_num)
theorem B1498157 : Blo 662308 1498157 := bbase (se 3 (by rfl) ⟨280904, by rfl⟩ : syracuseStep 1498157 = 561809) (by norm_num)
theorem B842825 : Blo 662308 842825 := bbase (se 2 (by rfl) ⟨316059, by rfl⟩ : syracuseStep 842825 = 632119) (by norm_num)
theorem B1498229 : Blo 662308 1498229 := bbase (se 5 (by rfl) ⟨70229, by rfl⟩ : syracuseStep 1498229 = 140459) (by norm_num)
theorem B842881 : Blo 662308 842881 := bbase (se 2 (by rfl) ⟨316080, by rfl⟩ : syracuseStep 842881 = 632161) (by norm_num)
theorem B2841733 : Blo 662308 2841733 := bbase (se 4 (by rfl) ⟨266412, by rfl⟩ : syracuseStep 2841733 = 532825) (by norm_num)
theorem B1793173 : Blo 662308 1793173 := bbase (se 6 (by rfl) ⟨42027, by rfl⟩ : syracuseStep 1793173 = 84055) (by norm_num)
theorem B1498301 : Blo 662308 1498301 := bbase (se 3 (by rfl) ⟨280931, by rfl⟩ : syracuseStep 1498301 = 561863) (by norm_num)
theorem B842977 : Blo 662308 842977 := bbase (se 2 (by rfl) ⟨316116, by rfl⟩ : syracuseStep 842977 = 632233) (by norm_num)
theorem B810221 : Blo 662308 810221 := bbase (se 3 (by rfl) ⟨151916, by rfl⟩ : syracuseStep 810221 = 303833) (by norm_num)
theorem B1498373 : Blo 662308 1498373 := bbase (se 4 (by rfl) ⟨140472, by rfl⟩ : syracuseStep 1498373 = 280945) (by norm_num)
theorem B3366197 : Blo 662308 3366197 := bbase (se 5 (by rfl) ⟨157790, by rfl⟩ : syracuseStep 3366197 = 315581) (by norm_num)
theorem B1498445 : Blo 662308 1498445 := bbase (se 3 (by rfl) ⟨280958, by rfl⟩ : syracuseStep 1498445 = 561917) (by norm_num)
theorem B843149 : Blo 662308 843149 := bbase (se 3 (by rfl) ⟨158090, by rfl⟩ : syracuseStep 843149 = 316181) (by norm_num)
theorem B1498517 : Blo 662308 1498517 := bbase (se 6 (by rfl) ⟨35121, by rfl⟩ : syracuseStep 1498517 = 70243) (by norm_num)
theorem B843205 : Blo 662308 843205 := bbase (se 4 (by rfl) ⟨79050, by rfl⟩ : syracuseStep 843205 = 158101) (by norm_num)
theorem B1498589 : Blo 662308 1498589 := bbase (se 3 (by rfl) ⟨280985, by rfl⟩ : syracuseStep 1498589 = 561971) (by norm_num)
theorem B3071461 : Blo 662308 3071461 := bbase (se 4 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 3071461 = 575899) (by norm_num)
theorem B1793573 : Blo 662308 1793573 := bbase (se 4 (by rfl) ⟨168147, by rfl⟩ : syracuseStep 1793573 = 336295) (by norm_num)
theorem B1498661 : Blo 662308 1498661 := bbase (se 4 (by rfl) ⟨140499, by rfl⟩ : syracuseStep 1498661 = 280999) (by norm_num)
theorem B2022965 : Blo 662308 2022965 := bbase (se 5 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 2022965 = 189653) (by norm_num)
theorem B1498733 : Blo 662308 1498733 := bbase (se 3 (by rfl) ⟨281012, by rfl⟩ : syracuseStep 1498733 = 562025) (by norm_num)
theorem B745105 : Blo 662308 745105 := bbase (se 2 (by rfl) ⟨279414, by rfl⟩ : syracuseStep 745105 = 558829) (by norm_num)
theorem B1793701 : Blo 662308 1793701 := bbase (se 4 (by rfl) ⟨168159, by rfl⟩ : syracuseStep 1793701 = 336319) (by norm_num)
theorem B745141 : Blo 662308 745141 := bbase (se 5 (by rfl) ⟨34928, by rfl⟩ : syracuseStep 745141 = 69857) (by norm_num)
theorem B1498805 : Blo 662308 1498805 := bbase (se 5 (by rfl) ⟨70256, by rfl⟩ : syracuseStep 1498805 = 140513) (by norm_num)
theorem B745177 : Blo 662308 745177 := bbase (se 2 (by rfl) ⟨279441, by rfl⟩ : syracuseStep 745177 = 558883) (by norm_num)
theorem B745213 : Blo 662308 745213 := bbase (se 3 (by rfl) ⟨139727, by rfl⟩ : syracuseStep 745213 = 279455) (by norm_num)
theorem B1498877 : Blo 662308 1498877 := bbase (se 3 (by rfl) ⟨281039, by rfl⟩ : syracuseStep 1498877 = 562079) (by norm_num)
theorem B745249 : Blo 662308 745249 := bbase (se 2 (by rfl) ⟨279468, by rfl⟩ : syracuseStep 745249 = 558937) (by norm_num)
theorem B745285 : Blo 662308 745285 := bbase (se 4 (by rfl) ⟨69870, by rfl⟩ : syracuseStep 745285 = 139741) (by norm_num)
theorem B1498949 : Blo 662308 1498949 := bbase (se 4 (by rfl) ⟨140526, by rfl⟩ : syracuseStep 1498949 = 281053) (by norm_num)
theorem B745321 : Blo 662308 745321 := bbase (se 2 (by rfl) ⟨279495, by rfl⟩ : syracuseStep 745321 = 558991) (by norm_num)
theorem B745357 : Blo 662308 745357 := bbase (se 3 (by rfl) ⟨139754, by rfl⟩ : syracuseStep 745357 = 279509) (by norm_num)
theorem B1499021 : Blo 662308 1499021 := bbase (se 3 (by rfl) ⟨281066, by rfl⟩ : syracuseStep 1499021 = 562133) (by norm_num)
theorem B745393 : Blo 662308 745393 := bbase (se 2 (by rfl) ⟨279522, by rfl⟩ : syracuseStep 745393 = 559045) (by norm_num)
theorem B745429 : Blo 662308 745429 := bbase (se 7 (by rfl) ⟨8735, by rfl⟩ : syracuseStep 745429 = 17471) (by norm_num)
theorem B1499093 : Blo 662308 1499093 := bbase (se 7 (by rfl) ⟨17567, by rfl⟩ : syracuseStep 1499093 = 35135) (by norm_num)
theorem B1368037 : Blo 662308 1368037 := bbase (se 4 (by rfl) ⟨128253, by rfl⟩ : syracuseStep 1368037 = 256507) (by norm_num)
theorem B745465 : Blo 662308 745465 := bbase (se 2 (by rfl) ⟨279549, by rfl⟩ : syracuseStep 745465 = 559099) (by norm_num)
theorem B745501 : Blo 662308 745501 := bbase (se 3 (by rfl) ⟨139781, by rfl⟩ : syracuseStep 745501 = 279563) (by norm_num)
theorem B1499165 : Blo 662308 1499165 := bbase (se 3 (by rfl) ⟨281093, by rfl⟩ : syracuseStep 1499165 = 562187) (by norm_num)
theorem B745537 : Blo 662308 745537 := bbase (se 2 (by rfl) ⟨279576, by rfl⟩ : syracuseStep 745537 = 559153) (by norm_num)
theorem B745573 : Blo 662308 745573 := bbase (se 4 (by rfl) ⟨69897, by rfl⟩ : syracuseStep 745573 = 139795) (by norm_num)
theorem B1597573 : Blo 662308 1597573 := bbase (se 4 (by rfl) ⟨149772, by rfl⟩ : syracuseStep 1597573 = 299545) (by norm_num)
theorem B745609 : Blo 662308 745609 := bbase (se 2 (by rfl) ⟨279603, by rfl⟩ : syracuseStep 745609 = 559207) (by norm_num)
theorem B745645 : Blo 662308 745645 := bbase (se 3 (by rfl) ⟨139808, by rfl⟩ : syracuseStep 745645 = 279617) (by norm_num)
theorem B745681 : Blo 662308 745681 := bbase (se 2 (by rfl) ⟨279630, by rfl⟩ : syracuseStep 745681 = 559261) (by norm_num)
theorem B2515157 : Blo 662308 2515157 := bbase (se 7 (by rfl) ⟨29474, by rfl⟩ : syracuseStep 2515157 = 58949) (by norm_num)
theorem B745717 : Blo 662308 745717 := bbase (se 5 (by rfl) ⟨34955, by rfl⟩ : syracuseStep 745717 = 69911) (by norm_num)
theorem B745753 : Blo 662308 745753 := bbase (se 2 (by rfl) ⟨279657, by rfl⟩ : syracuseStep 745753 = 559315) (by norm_num)
theorem B745789 : Blo 662308 745789 := bbase (se 3 (by rfl) ⟨139835, by rfl⟩ : syracuseStep 745789 = 279671) (by norm_num)
theorem B745825 : Blo 662308 745825 := bbase (se 2 (by rfl) ⟨279684, by rfl⟩ : syracuseStep 745825 = 559369) (by norm_num)
theorem B745861 : Blo 662308 745861 := bbase (se 4 (by rfl) ⟨69924, by rfl⟩ : syracuseStep 745861 = 139849) (by norm_num)
theorem B745897 : Blo 662308 745897 := bbase (se 2 (by rfl) ⟨279711, by rfl⟩ : syracuseStep 745897 = 559423) (by norm_num)
theorem B1139141 : Blo 662308 1139141 := bbase (se 4 (by rfl) ⟨106794, by rfl⟩ : syracuseStep 1139141 = 213589) (by norm_num)
theorem B745933 : Blo 662308 745933 := bbase (se 3 (by rfl) ⟨139862, by rfl⟩ : syracuseStep 745933 = 279725) (by norm_num)
theorem B745969 : Blo 662308 745969 := bbase (se 2 (by rfl) ⟨279738, by rfl⟩ : syracuseStep 745969 = 559477) (by norm_num)
theorem B2515445 : Blo 662308 2515445 := bbase (se 5 (by rfl) ⟨117911, by rfl⟩ : syracuseStep 2515445 = 235823) (by norm_num)
theorem B746005 : Blo 662308 746005 := bbase (se 6 (by rfl) ⟨17484, by rfl⟩ : syracuseStep 746005 = 34969) (by norm_num)
theorem B1008173 : Blo 662308 1008173 := bbase (se 3 (by rfl) ⟨189032, by rfl⟩ : syracuseStep 1008173 = 378065) (by norm_num)
theorem B746041 : Blo 662308 746041 := bbase (se 2 (by rfl) ⟨279765, by rfl⟩ : syracuseStep 746041 = 559531) (by norm_num)
theorem B3367493 : Blo 662308 3367493 := bbase (se 4 (by rfl) ⟨315702, by rfl⟩ : syracuseStep 3367493 = 631405) (by norm_num)
theorem B2843221 : Blo 662308 2843221 := bbase (se 8 (by rfl) ⟨16659, by rfl⟩ : syracuseStep 2843221 = 33319) (by norm_num)
theorem B746077 : Blo 662308 746077 := bbase (se 3 (by rfl) ⟨139889, by rfl⟩ : syracuseStep 746077 = 279779) (by norm_num)
theorem B2843237 : Blo 662308 2843237 := bbase (se 4 (by rfl) ⟨266553, by rfl⟩ : syracuseStep 2843237 = 533107) (by norm_num)
theorem B746113 : Blo 662308 746113 := bbase (se 2 (by rfl) ⟨279792, by rfl⟩ : syracuseStep 746113 = 559585) (by norm_num)
theorem B746149 : Blo 662308 746149 := bbase (se 4 (by rfl) ⟨69951, by rfl⟩ : syracuseStep 746149 = 139903) (by norm_num)
theorem B746185 : Blo 662308 746185 := bbase (se 2 (by rfl) ⟨279819, by rfl⟩ : syracuseStep 746185 = 559639) (by norm_num)
theorem B1893077 : Blo 662308 1893077 := bbase (se 7 (by rfl) ⟨22184, by rfl⟩ : syracuseStep 1893077 = 44369) (by norm_num)
theorem B746221 : Blo 662308 746221 := bbase (se 3 (by rfl) ⟨139916, by rfl⟩ : syracuseStep 746221 = 279833) (by norm_num)
theorem B1008373 : Blo 662308 1008373 := bbase (se 5 (by rfl) ⟨47267, by rfl⟩ : syracuseStep 1008373 = 94535) (by norm_num)
theorem B746257 : Blo 662308 746257 := bbase (se 2 (by rfl) ⟨279846, by rfl⟩ : syracuseStep 746257 = 559693) (by norm_num)
theorem B1598237 : Blo 662308 1598237 := bbase (se 3 (by rfl) ⟨299669, by rfl⟩ : syracuseStep 1598237 = 599339) (by norm_num)
theorem B746293 : Blo 662308 746293 := bbase (se 5 (by rfl) ⟨34982, by rfl⟩ : syracuseStep 746293 = 69965) (by norm_num)
theorem B746329 : Blo 662308 746329 := bbase (se 2 (by rfl) ⟨279873, by rfl⟩ : syracuseStep 746329 = 559747) (by norm_num)
theorem B746365 : Blo 662308 746365 := bbase (se 3 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 746365 = 279887) (by norm_num)
theorem B746401 : Blo 662308 746401 := bbase (se 2 (by rfl) ⟨279900, by rfl⟩ : syracuseStep 746401 = 559801) (by norm_num)
theorem B746437 : Blo 662308 746437 := bbase (se 4 (by rfl) ⟨69978, by rfl⟩ : syracuseStep 746437 = 139957) (by norm_num)
theorem B3793877 : Blo 662308 3793877 := bbase (se 7 (by rfl) ⟨44459, by rfl⟩ : syracuseStep 3793877 = 88919) (by norm_num)
theorem B746473 : Blo 662308 746473 := bbase (se 2 (by rfl) ⟨279927, by rfl⟩ : syracuseStep 746473 = 559855) (by norm_num)
theorem B943093 : Blo 662308 943093 := bbase (se 5 (by rfl) ⟨44207, by rfl⟩ : syracuseStep 943093 = 88415) (by norm_num)
theorem B746509 : Blo 662308 746509 := bbase (se 3 (by rfl) ⟨139970, by rfl⟩ : syracuseStep 746509 = 279941) (by norm_num)
theorem B1008677 : Blo 662308 1008677 := bbase (se 4 (by rfl) ⟨94563, by rfl⟩ : syracuseStep 1008677 = 189127) (by norm_num)
theorem B746545 : Blo 662308 746545 := bbase (se 2 (by rfl) ⟨279954, by rfl⟩ : syracuseStep 746545 = 559909) (by norm_num)
theorem B746581 : Blo 662308 746581 := bbase (se 8 (by rfl) ⟨4374, by rfl⟩ : syracuseStep 746581 = 8749) (by norm_num)
theorem B746617 : Blo 662308 746617 := bbase (se 2 (by rfl) ⟨279981, by rfl⟩ : syracuseStep 746617 = 559963) (by norm_num)
theorem B746653 : Blo 662308 746653 := bbase (se 3 (by rfl) ⟨139997, by rfl⟩ : syracuseStep 746653 = 279995) (by norm_num)
theorem B746689 : Blo 662308 746689 := bbase (se 2 (by rfl) ⟨280008, by rfl⟩ : syracuseStep 746689 = 560017) (by norm_num)
theorem B746725 : Blo 662308 746725 := bbase (se 4 (by rfl) ⟨70005, by rfl⟩ : syracuseStep 746725 = 140011) (by norm_num)
theorem B746761 : Blo 662308 746761 := bbase (se 2 (by rfl) ⟨280035, by rfl⟩ : syracuseStep 746761 = 560071) (by norm_num)
theorem B746797 : Blo 662308 746797 := bbase (se 3 (by rfl) ⟨140024, by rfl⟩ : syracuseStep 746797 = 280049) (by norm_num)
theorem B943429 : Blo 662308 943429 := bbase (se 4 (by rfl) ⟨88446, by rfl⟩ : syracuseStep 943429 = 176893) (by norm_num)
theorem B746833 : Blo 662308 746833 := bbase (se 2 (by rfl) ⟨280062, by rfl⟩ : syracuseStep 746833 = 560125) (by norm_num)
theorem B746869 : Blo 662308 746869 := bbase (se 5 (by rfl) ⟨35009, by rfl⟩ : syracuseStep 746869 = 70019) (by norm_num)
theorem B7562645 : Blo 662308 7562645 := bbase (se 6 (by rfl) ⟨177249, by rfl⟩ : syracuseStep 7562645 = 354499) (by norm_num)
theorem B746905 : Blo 662308 746905 := bbase (se 2 (by rfl) ⟨280089, by rfl⟩ : syracuseStep 746905 = 560179) (by norm_num)
theorem B746941 : Blo 662308 746941 := bbase (se 3 (by rfl) ⟨140051, by rfl⟩ : syracuseStep 746941 = 280103) (by norm_num)
theorem B746977 : Blo 662308 746977 := bbase (se 2 (by rfl) ⟨280116, by rfl⟩ : syracuseStep 746977 = 560233) (by norm_num)
theorem B1533421 : Blo 662308 1533421 := bbase (se 3 (by rfl) ⟨287516, by rfl⟩ : syracuseStep 1533421 = 575033) (by norm_num)
theorem B747013 : Blo 662308 747013 := bbase (se 4 (by rfl) ⟨70032, by rfl⟩ : syracuseStep 747013 = 140065) (by norm_num)
theorem B943645 : Blo 662308 943645 := bbase (se 3 (by rfl) ⟨176933, by rfl⟩ : syracuseStep 943645 = 353867) (by norm_num)
theorem B747049 : Blo 662308 747049 := bbase (se 2 (by rfl) ⟨280143, by rfl⟩ : syracuseStep 747049 = 560287) (by norm_num)
theorem B747085 : Blo 662308 747085 := bbase (se 3 (by rfl) ⟨140078, by rfl⟩ : syracuseStep 747085 = 280157) (by norm_num)
theorem B747121 : Blo 662308 747121 := bbase (se 2 (by rfl) ⟨280170, by rfl⟩ : syracuseStep 747121 = 560341) (by norm_num)
theorem B2516629 : Blo 662308 2516629 := bbase (se 6 (by rfl) ⟨58983, by rfl⟩ : syracuseStep 2516629 = 117967) (by norm_num)
theorem B747157 : Blo 662308 747157 := bbase (se 6 (by rfl) ⟨17511, by rfl⟩ : syracuseStep 747157 = 35023) (by norm_num)
theorem B747193 : Blo 662308 747193 := bbase (se 2 (by rfl) ⟨280197, by rfl⟩ : syracuseStep 747193 = 560395) (by norm_num)
theorem B747229 : Blo 662308 747229 := bbase (se 3 (by rfl) ⟨140105, by rfl⟩ : syracuseStep 747229 = 280211) (by norm_num)
theorem B2123509 : Blo 662308 2123509 := bbase (se 5 (by rfl) ⟨99539, by rfl⟩ : syracuseStep 2123509 = 199079) (by norm_num)
theorem B747265 : Blo 662308 747265 := bbase (se 2 (by rfl) ⟨280224, by rfl⟩ : syracuseStep 747265 = 560449) (by norm_num)
theorem B747301 : Blo 662308 747301 := bbase (se 4 (by rfl) ⟨70059, by rfl⟩ : syracuseStep 747301 = 140119) (by norm_num)
theorem B747337 : Blo 662308 747337 := bbase (se 2 (by rfl) ⟨280251, by rfl⟩ : syracuseStep 747337 = 560503) (by norm_num)
theorem B3368789 : Blo 662308 3368789 := bbase (se 9 (by rfl) ⟨9869, by rfl⟩ : syracuseStep 3368789 = 19739) (by norm_num)
theorem B747373 : Blo 662308 747373 := bbase (se 3 (by rfl) ⟨140132, by rfl⟩ : syracuseStep 747373 = 280265) (by norm_num)
theorem B1894261 : Blo 662308 1894261 := bbase (se 5 (by rfl) ⟨88793, by rfl⟩ : syracuseStep 1894261 = 177587) (by norm_num)
theorem B1009541 : Blo 662308 1009541 := bbase (se 4 (by rfl) ⟨94644, by rfl⟩ : syracuseStep 1009541 = 189289) (by norm_num)
theorem B747409 : Blo 662308 747409 := bbase (se 2 (by rfl) ⟨280278, by rfl⟩ : syracuseStep 747409 = 560557) (by norm_num)
theorem B944021 : Blo 662308 944021 := bbase (se 6 (by rfl) ⟨22125, by rfl⟩ : syracuseStep 944021 = 44251) (by norm_num)
theorem B1009589 : Blo 662308 1009589 := bbase (se 5 (by rfl) ⟨47324, by rfl⟩ : syracuseStep 1009589 = 94649) (by norm_num)
theorem B747445 : Blo 662308 747445 := bbase (se 5 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 747445 = 70073) (by norm_num)
theorem B2516933 : Blo 662308 2516933 := bbase (se 4 (by rfl) ⟨235962, by rfl⟩ : syracuseStep 2516933 = 471925) (by norm_num)
theorem B747481 : Blo 662308 747481 := bbase (se 2 (by rfl) ⟨280305, by rfl⟩ : syracuseStep 747481 = 560611) (by norm_num)
theorem B747517 : Blo 662308 747517 := bbase (se 3 (by rfl) ⟨140159, by rfl⟩ : syracuseStep 747517 = 280319) (by norm_num)
theorem B1894421 : Blo 662308 1894421 := bbase (se 6 (by rfl) ⟨44400, by rfl⟩ : syracuseStep 1894421 = 88801) (by norm_num)
theorem B747553 : Blo 662308 747553 := bbase (se 2 (by rfl) ⟨280332, by rfl⟩ : syracuseStep 747553 = 560665) (by norm_num)
theorem B747589 : Blo 662308 747589 := bbase (se 4 (by rfl) ⟨70086, by rfl⟩ : syracuseStep 747589 = 140173) (by norm_num)
theorem B747625 : Blo 662308 747625 := bbase (se 2 (by rfl) ⟨280359, by rfl⟩ : syracuseStep 747625 = 560719) (by norm_num)
theorem B747661 : Blo 662308 747661 := bbase (se 3 (by rfl) ⟨140186, by rfl⟩ : syracuseStep 747661 = 280373) (by norm_num)
theorem B747697 : Blo 662308 747697 := bbase (se 2 (by rfl) ⟨280386, by rfl⟩ : syracuseStep 747697 = 560773) (by norm_num)
theorem B747733 : Blo 662308 747733 := bbase (se 7 (by rfl) ⟨8762, by rfl⟩ : syracuseStep 747733 = 17525) (by norm_num)
theorem B747769 : Blo 662308 747769 := bbase (se 2 (by rfl) ⟨280413, by rfl⟩ : syracuseStep 747769 = 560827) (by norm_num)
theorem B1009925 : Blo 662308 1009925 := bbase (se 4 (by rfl) ⟨94680, by rfl⟩ : syracuseStep 1009925 = 189361) (by norm_num)
theorem B1894661 : Blo 662308 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B747805 : Blo 662308 747805 := bbase (se 3 (by rfl) ⟨140213, by rfl⟩ : syracuseStep 747805 = 280427) (by norm_num)
theorem B747841 : Blo 662308 747841 := bbase (se 2 (by rfl) ⟨280440, by rfl⟩ : syracuseStep 747841 = 560881) (by norm_num)
theorem B747877 : Blo 662308 747877 := bbase (se 4 (by rfl) ⟨70113, by rfl⟩ : syracuseStep 747877 = 140227) (by norm_num)
theorem B747913 : Blo 662308 747913 := bbase (se 2 (by rfl) ⟨280467, by rfl⟩ : syracuseStep 747913 = 560935) (by norm_num)
theorem B747949 : Blo 662308 747949 := bbase (se 3 (by rfl) ⟨140240, by rfl⟩ : syracuseStep 747949 = 280481) (by norm_num)
theorem B1894853 : Blo 662308 1894853 := bbase (se 4 (by rfl) ⟨177642, by rfl⟩ : syracuseStep 1894853 = 355285) (by norm_num)
theorem B747985 : Blo 662308 747985 := bbase (se 2 (by rfl) ⟨280494, by rfl⟩ : syracuseStep 747985 = 560989) (by norm_num)
theorem B748021 : Blo 662308 748021 := bbase (se 5 (by rfl) ⟨35063, by rfl⟩ : syracuseStep 748021 = 70127) (by norm_num)
theorem B1600013 : Blo 662308 1600013 := bbase (se 3 (by rfl) ⟨300002, by rfl⟩ : syracuseStep 1600013 = 600005) (by norm_num)
theorem B748057 : Blo 662308 748057 := bbase (se 2 (by rfl) ⟨280521, by rfl⟩ : syracuseStep 748057 = 561043) (by norm_num)
theorem B748093 : Blo 662308 748093 := bbase (se 3 (by rfl) ⟨140267, by rfl⟩ : syracuseStep 748093 = 280535) (by norm_num)
theorem B748129 : Blo 662308 748129 := bbase (se 2 (by rfl) ⟨280548, by rfl⟩ : syracuseStep 748129 = 561097) (by norm_num)
theorem B748165 : Blo 662308 748165 := bbase (se 4 (by rfl) ⟨70140, by rfl⟩ : syracuseStep 748165 = 140281) (by norm_num)
theorem B748201 : Blo 662308 748201 := bbase (se 2 (by rfl) ⟨280575, by rfl⟩ : syracuseStep 748201 = 561151) (by norm_num)
theorem B748237 : Blo 662308 748237 := bbase (se 3 (by rfl) ⟨140294, by rfl⟩ : syracuseStep 748237 = 280589) (by norm_num)
theorem B748273 : Blo 662308 748273 := bbase (se 2 (by rfl) ⟨280602, by rfl⟩ : syracuseStep 748273 = 561205) (by norm_num)
theorem B748309 : Blo 662308 748309 := bbase (se 6 (by rfl) ⟨17538, by rfl⟩ : syracuseStep 748309 = 35077) (by norm_num)
theorem B6810421 : Blo 662308 6810421 := bbase (se 5 (by rfl) ⟨319238, by rfl⟩ : syracuseStep 6810421 = 638477) (by norm_num)
theorem B2845493 : Blo 662308 2845493 := bbase (se 5 (by rfl) ⟨133382, by rfl⟩ : syracuseStep 2845493 = 266765) (by norm_num)
theorem B748345 : Blo 662308 748345 := bbase (se 2 (by rfl) ⟨280629, by rfl⟩ : syracuseStep 748345 = 561259) (by norm_num)
theorem B748381 : Blo 662308 748381 := bbase (se 3 (by rfl) ⟨140321, by rfl⟩ : syracuseStep 748381 = 280643) (by norm_num)
theorem B748417 : Blo 662308 748417 := bbase (se 2 (by rfl) ⟨280656, by rfl⟩ : syracuseStep 748417 = 561313) (by norm_num)
theorem B748453 : Blo 662308 748453 := bbase (se 4 (by rfl) ⟨70167, by rfl⟩ : syracuseStep 748453 = 140335) (by norm_num)
theorem B748489 : Blo 662308 748489 := bbase (se 2 (by rfl) ⟨280683, by rfl⟩ : syracuseStep 748489 = 561367) (by norm_num)
theorem B748525 : Blo 662308 748525 := bbase (se 3 (by rfl) ⟨140348, by rfl⟩ : syracuseStep 748525 = 280697) (by norm_num)
theorem B748561 : Blo 662308 748561 := bbase (se 2 (by rfl) ⟨280710, by rfl⟩ : syracuseStep 748561 = 561421) (by norm_num)
theorem B748597 : Blo 662308 748597 := bbase (se 5 (by rfl) ⟨35090, by rfl⟩ : syracuseStep 748597 = 70181) (by norm_num)
theorem B748633 : Blo 662308 748633 := bbase (se 2 (by rfl) ⟨280737, by rfl⟩ : syracuseStep 748633 = 561475) (by norm_num)
theorem B3370085 : Blo 662308 3370085 := bbase (se 4 (by rfl) ⟨315945, by rfl⟩ : syracuseStep 3370085 = 631891) (by norm_num)
theorem B748669 : Blo 662308 748669 := bbase (se 3 (by rfl) ⟨140375, by rfl⟩ : syracuseStep 748669 = 280751) (by norm_num)
theorem B748705 : Blo 662308 748705 := bbase (se 2 (by rfl) ⟨280764, by rfl⟩ : syracuseStep 748705 = 561529) (by norm_num)
theorem B748741 : Blo 662308 748741 := bbase (se 4 (by rfl) ⟨70194, by rfl⟩ : syracuseStep 748741 = 140389) (by norm_num)
theorem B748777 : Blo 662308 748777 := bbase (se 2 (by rfl) ⟨280791, by rfl⟩ : syracuseStep 748777 = 561583) (by norm_num)
theorem B748813 : Blo 662308 748813 := bbase (se 3 (by rfl) ⟨140402, by rfl⟩ : syracuseStep 748813 = 280805) (by norm_num)
theorem B945445 : Blo 662308 945445 := bbase (se 4 (by rfl) ⟨88635, by rfl⟩ : syracuseStep 945445 = 177271) (by norm_num)
theorem B748849 : Blo 662308 748849 := bbase (se 2 (by rfl) ⟨280818, by rfl⟩ : syracuseStep 748849 = 561637) (by norm_num)
theorem B748885 : Blo 662308 748885 := bbase (se 11 (by rfl) ⟨548, by rfl⟩ : syracuseStep 748885 = 1097) (by norm_num)
theorem B748921 : Blo 662308 748921 := bbase (se 2 (by rfl) ⟨280845, by rfl⟩ : syracuseStep 748921 = 561691) (by norm_num)
theorem B2387333 : Blo 662308 2387333 := bbase (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) (by norm_num)
theorem B748957 : Blo 662308 748957 := bbase (se 3 (by rfl) ⟨140429, by rfl⟩ : syracuseStep 748957 = 280859) (by norm_num)
theorem B1895845 : Blo 662308 1895845 := bbase (se 4 (by rfl) ⟨177735, by rfl⟩ : syracuseStep 1895845 = 355471) (by norm_num)
theorem B748993 : Blo 662308 748993 := bbase (se 2 (by rfl) ⟨280872, by rfl⟩ : syracuseStep 748993 = 561745) (by norm_num)
theorem B749029 : Blo 662308 749029 := bbase (se 4 (by rfl) ⟨70221, by rfl⟩ : syracuseStep 749029 = 140443) (by norm_num)
theorem B749065 : Blo 662308 749065 := bbase (se 2 (by rfl) ⟨280899, by rfl⟩ : syracuseStep 749065 = 561799) (by norm_num)
theorem B749101 : Blo 662308 749101 := bbase (se 3 (by rfl) ⟨140456, by rfl⟩ : syracuseStep 749101 = 280913) (by norm_num)
theorem B749137 : Blo 662308 749137 := bbase (se 2 (by rfl) ⟨280926, by rfl⟩ : syracuseStep 749137 = 561853) (by norm_num)
theorem B749173 : Blo 662308 749173 := bbase (se 5 (by rfl) ⟨35117, by rfl⟩ : syracuseStep 749173 = 70235) (by norm_num)
theorem B749209 : Blo 662308 749209 := bbase (se 2 (by rfl) ⟨280953, by rfl⟩ : syracuseStep 749209 = 561907) (by norm_num)
theorem B749245 : Blo 662308 749245 := bbase (se 3 (by rfl) ⟨140483, by rfl⟩ : syracuseStep 749245 = 280967) (by norm_num)
theorem B749281 : Blo 662308 749281 := bbase (se 2 (by rfl) ⟨280980, by rfl⟩ : syracuseStep 749281 = 561961) (by norm_num)
theorem B749317 : Blo 662308 749317 := bbase (se 4 (by rfl) ⟨70248, by rfl⟩ : syracuseStep 749317 = 140497) (by norm_num)
theorem B749353 : Blo 662308 749353 := bbase (se 2 (by rfl) ⟨281007, by rfl⟩ : syracuseStep 749353 = 562015) (by norm_num)
theorem B749389 : Blo 662308 749389 := bbase (se 3 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 749389 = 281021) (by norm_num)
theorem B749425 : Blo 662308 749425 := bbase (se 2 (by rfl) ⟨281034, by rfl⟩ : syracuseStep 749425 = 562069) (by norm_num)
theorem B946037 : Blo 662308 946037 := bbase (se 5 (by rfl) ⟨44345, by rfl⟩ : syracuseStep 946037 = 88691) (by norm_num)
theorem B749461 : Blo 662308 749461 := bbase (se 6 (by rfl) ⟨17565, by rfl⟩ : syracuseStep 749461 = 35131) (by norm_num)
theorem B749497 : Blo 662308 749497 := bbase (se 2 (by rfl) ⟨281061, by rfl⟩ : syracuseStep 749497 = 562123) (by norm_num)
theorem B946117 : Blo 662308 946117 := bbase (se 4 (by rfl) ⟨88698, by rfl⟩ : syracuseStep 946117 = 177397) (by norm_num)
theorem B749533 : Blo 662308 749533 := bbase (se 3 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 749533 = 281075) (by norm_num)
theorem B749569 : Blo 662308 749569 := bbase (se 2 (by rfl) ⟨281088, by rfl⟩ : syracuseStep 749569 = 562177) (by norm_num)
theorem B2519045 : Blo 662308 2519045 := bbase (se 4 (by rfl) ⟨236160, by rfl⟩ : syracuseStep 2519045 = 472321) (by norm_num)
theorem B946237 : Blo 662308 946237 := bbase (se 3 (by rfl) ⟨177419, by rfl⟩ : syracuseStep 946237 = 354839) (by norm_num)
theorem B946333 : Blo 662308 946333 := bbase (se 3 (by rfl) ⟨177437, by rfl⟩ : syracuseStep 946333 = 354875) (by norm_num)
theorem B2519333 : Blo 662308 2519333 := bbase (se 4 (by rfl) ⟨236187, by rfl⟩ : syracuseStep 2519333 = 472375) (by norm_num)
theorem B3371381 : Blo 662308 3371381 := bbase (se 5 (by rfl) ⟨158033, by rfl⟩ : syracuseStep 3371381 = 316067) (by norm_num)
theorem B1012133 : Blo 662308 1012133 := bbase (se 4 (by rfl) ⟨94887, by rfl⟩ : syracuseStep 1012133 = 189775) (by norm_num)
theorem B1896949 : Blo 662308 1896949 := bbase (se 5 (by rfl) ⟨88919, by rfl⟩ : syracuseStep 1896949 = 177839) (by norm_num)
theorem B946829 : Blo 662308 946829 := bbase (se 3 (by rfl) ⟨177530, by rfl⟩ : syracuseStep 946829 = 355061) (by norm_num)
theorem B3240805 : Blo 662308 3240805 := bbase (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) (by norm_num)
theorem B1438661 : Blo 662308 1438661 := bbase (se 4 (by rfl) ⟨134874, by rfl⟩ : syracuseStep 1438661 = 269749) (by norm_num)
theorem B1274869 : Blo 662308 1274869 := bbase (se 5 (by rfl) ⟨59759, by rfl⟩ : syracuseStep 1274869 = 119519) (by norm_num)
theorem B5043221 : Blo 662308 5043221 := bbase (se 6 (by rfl) ⟨118200, by rfl⟩ : syracuseStep 5043221 = 236401) (by norm_num)
theorem B947381 : Blo 662308 947381 := bbase (se 5 (by rfl) ⟨44408, by rfl⟩ : syracuseStep 947381 = 88817) (by norm_num)
theorem B4846837 : Blo 662308 4846837 := bbase (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) (by norm_num)
theorem B1799605 : Blo 662308 1799605 := bbase (se 5 (by rfl) ⟨84356, by rfl⟩ : syracuseStep 1799605 = 168713) (by norm_num)
theorem B2520517 : Blo 662308 2520517 := bbase (se 4 (by rfl) ⟨236298, by rfl⟩ : syracuseStep 2520517 = 472597) (by norm_num)
theorem B718309 : Blo 662308 718309 := bbase (se 4 (by rfl) ⟨67341, by rfl⟩ : syracuseStep 718309 = 134683) (by norm_num)
theorem B4257269 : Blo 662308 4257269 := bbase (se 5 (by rfl) ⟨199559, by rfl⟩ : syracuseStep 4257269 = 399119) (by norm_num)
theorem B3372677 : Blo 662308 3372677 := bbase (se 4 (by rfl) ⟨316188, by rfl⟩ : syracuseStep 3372677 = 632377) (by norm_num)
theorem B2520821 : Blo 662308 2520821 := bbase (se 5 (by rfl) ⟨118163, by rfl⟩ : syracuseStep 2520821 = 236327) (by norm_num)
theorem B2127701 : Blo 662308 2127701 := bbase (se 9 (by rfl) ⟨6233, by rfl⟩ : syracuseStep 2127701 = 12467) (by norm_num)
theorem B948133 : Blo 662308 948133 := bbase (se 4 (by rfl) ⟨88887, by rfl⟩ : syracuseStep 948133 = 177775) (by norm_num)
theorem B1210421 : Blo 662308 1210421 := bbase (se 5 (by rfl) ⟨56738, by rfl⟩ : syracuseStep 1210421 = 113477) (by norm_num)
theorem B8518229 : Blo 662308 8518229 := bbase (se 8 (by rfl) ⟨49911, by rfl⟩ : syracuseStep 8518229 = 99823) (by norm_num)
theorem B1079957 : Blo 662308 1079957 := bbase (se 6 (by rfl) ⟨25311, by rfl⟩ : syracuseStep 1079957 = 50623) (by norm_num)
theorem B6454325 : Blo 662308 6454325 := bbase (se 5 (by rfl) ⟨302546, by rfl⟩ : syracuseStep 6454325 = 605093) (by norm_num)
theorem B1277117 : Blo 662308 1277117 := bbase (se 3 (by rfl) ⟨239459, by rfl⟩ : syracuseStep 1277117 = 478919) (by norm_num)
theorem B851185 : Blo 662308 851185 := bbase (se 2 (by rfl) ⟨319194, by rfl⟩ : syracuseStep 851185 = 638389) (by norm_num)
theorem B851401 : Blo 662308 851401 := bbase (se 2 (by rfl) ⟨319275, by rfl⟩ : syracuseStep 851401 = 638551) (by norm_num)
theorem B4783637 : Blo 662308 4783637 := bbase (se 6 (by rfl) ⟨112116, by rfl⟩ : syracuseStep 4783637 = 224233) (by norm_num)
theorem B851677 : Blo 662308 851677 := bbase (se 3 (by rfl) ⟨159689, by rfl⟩ : syracuseStep 851677 = 319379) (by norm_num)
theorem B4849397 : Blo 662308 4849397 := bbase (se 5 (by rfl) ⟨227315, by rfl⟩ : syracuseStep 4849397 = 454631) (by norm_num)
theorem B2522933 : Blo 662308 2522933 := bbase (se 5 (by rfl) ⟨118262, by rfl⟩ : syracuseStep 2522933 = 236525) (by norm_num)
theorem B1212293 : Blo 662308 1212293 := bbase (se 4 (by rfl) ⟨113652, by rfl⟩ : syracuseStep 1212293 = 227305) (by norm_num)
theorem B4030357 : Blo 662308 4030357 := bbase (se 6 (by rfl) ⟨94461, by rfl⟩ : syracuseStep 4030357 = 188923) (by norm_num)
theorem B20742101 : Blo 662308 20742101 := bbase (se 7 (by rfl) ⟨243071, by rfl⟩ : syracuseStep 20742101 = 486143) (by norm_num)
theorem B1441955 : Blo 662308 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B2130097 : Blo 662308 2130097 := bstep (se 2 (by rfl) ⟨798786, by rfl⟩ : syracuseStep 2130097 = 1597573) B1597573
theorem B2130275 : Blo 662308 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B6062789 : Blo 662308 6062789 := bstep (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) B1136773
theorem B5047109 : Blo 662308 5047109 := bstep (se 4 (by rfl) ⟨473166, by rfl⟩ : syracuseStep 5047109 = 946333) B946333
theorem B2392973 : Blo 662308 2392973 := bstep (se 3 (by rfl) ⟨448682, by rfl⟩ : syracuseStep 2392973 = 897365) B897365
theorem B7177187 : Blo 662308 7177187 := bstep (se 1 (by rfl) ⟨5382890, by rfl⟩ : syracuseStep 7177187 = 10765781) B10765781
theorem B1344497 : Blo 662308 1344497 := bstep (se 2 (by rfl) ⟨504186, by rfl⟩ : syracuseStep 1344497 = 1008373) B1008373
theorem B8487989 : Blo 662308 8487989 := bstep (se 5 (by rfl) ⟨397874, by rfl⟩ : syracuseStep 8487989 = 795749) B795749
theorem B5178595 : Blo 662308 5178595 := bstep (se 1 (by rfl) ⟨3883946, by rfl⟩ : syracuseStep 5178595 = 7767893) B7767893
theorem B16647565 : Blo 662308 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B2688461 : Blo 662308 2688461 := bstep (se 3 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 2688461 = 1008173) B1008173
theorem B5375459 : Blo 662308 5375459 := bstep (se 1 (by rfl) ⟨4031594, by rfl⟩ : syracuseStep 5375459 = 8063189) B8063189
theorem B2524877 : Blo 662308 2524877 := bstep (se 3 (by rfl) ⟨473414, by rfl⟩ : syracuseStep 2524877 = 946829) B946829
theorem B5670755 : Blo 662308 5670755 := bstep (se 1 (by rfl) ⟨4253066, by rfl⟩ : syracuseStep 5670755 = 8506133) B8506133
theorem B13633393 : Blo 662308 13633393 := bstep (se 2 (by rfl) ⟨5112522, by rfl⟩ : syracuseStep 13633393 = 10225045) B10225045
theorem B4032517 : Blo 662308 4032517 := bstep (se 4 (by rfl) ⟨378048, by rfl⟩ : syracuseStep 4032517 = 756097) B756097
theorem B2132045 : Blo 662308 2132045 := bstep (se 3 (by rfl) ⟨399758, by rfl⟩ : syracuseStep 2132045 = 799517) B799517
theorem B1050769 : Blo 662308 1050769 := bstep (se 2 (by rfl) ⟨394038, by rfl⟩ : syracuseStep 1050769 = 788077) B788077
theorem B10226033 : Blo 662308 10226033 := bstep (se 2 (by rfl) ⟨3834762, by rfl⟩ : syracuseStep 10226033 = 7669525) B7669525
theorem B2525681 : Blo 662308 2525681 := bstep (se 2 (by rfl) ⟨947130, by rfl⟩ : syracuseStep 2525681 = 1894261) B1894261
theorem B3836429 : Blo 662308 3836429 := bstep (se 3 (by rfl) ⟨719330, by rfl⟩ : syracuseStep 3836429 = 1438661) B1438661
theorem B2689805 : Blo 662308 2689805 := bstep (se 3 (by rfl) ⟨504338, by rfl⟩ : syracuseStep 2689805 = 1008677) B1008677
theorem B4262705 : Blo 662308 4262705 := bstep (se 2 (by rfl) ⟨1598514, by rfl⟩ : syracuseStep 4262705 = 3197029) B3197029
theorem B2526349 : Blo 662308 2526349 := bstep (se 3 (by rfl) ⟨473690, by rfl⟩ : syracuseStep 2526349 = 947381) B947381
theorem B1346915 : Blo 662308 1346915 := bstep (se 1 (by rfl) ⟨1010186, by rfl⟩ : syracuseStep 1346915 = 2020373) B2020373
theorem B1117651 : Blo 662308 1117651 := bstep (se 1 (by rfl) ⟨838238, by rfl⟩ : syracuseStep 1117651 = 1676477) B1676477
theorem B1117793 : Blo 662308 1117793 := bstep (se 2 (by rfl) ⟨419172, by rfl⟩ : syracuseStep 1117793 = 838345) B838345
theorem B1117921 : Blo 662308 1117921 := bstep (se 2 (by rfl) ⟨419220, by rfl⟩ : syracuseStep 1117921 = 838441) B838441
theorem B9080561 : Blo 662308 9080561 := bstep (se 2 (by rfl) ⟨3405210, by rfl⟩ : syracuseStep 9080561 = 6810421) B6810421
theorem B1117955 : Blo 662308 1117955 := bstep (se 1 (by rfl) ⟨838466, by rfl⟩ : syracuseStep 1117955 = 1676933) B1676933
theorem B1118083 : Blo 662308 1118083 := bstep (se 1 (by rfl) ⟨838562, by rfl⟩ : syracuseStep 1118083 = 1677125) B1677125
theorem B2527139 : Blo 662308 2527139 := bstep (se 1 (by rfl) ⟨1895354, by rfl⟩ : syracuseStep 2527139 = 3790709) B3790709
theorem B1118225 : Blo 662308 1118225 := bstep (se 2 (by rfl) ⟨419334, by rfl⟩ : syracuseStep 1118225 = 838669) B838669
theorem B1118353 : Blo 662308 1118353 := bstep (se 2 (by rfl) ⟨419382, by rfl⟩ : syracuseStep 1118353 = 838765) B838765
theorem B1118387 : Blo 662308 1118387 := bstep (se 1 (by rfl) ⟨838790, by rfl⟩ : syracuseStep 1118387 = 1677581) B1677581
theorem B757955 : Blo 662308 757955 := bstep (se 1 (by rfl) ⟨568466, by rfl⟩ : syracuseStep 757955 = 1136933) B1136933
theorem B1118515 : Blo 662308 1118515 := bstep (se 1 (by rfl) ⟨838886, by rfl⟩ : syracuseStep 1118515 = 1677773) B1677773
theorem B1118657 : Blo 662308 1118657 := bstep (se 2 (by rfl) ⟨419496, by rfl⟩ : syracuseStep 1118657 = 838993) B838993
theorem B2527793 : Blo 662308 2527793 := bstep (se 2 (by rfl) ⟨947922, by rfl⟩ : syracuseStep 2527793 = 1895845) B1895845
theorem B1118785 : Blo 662308 1118785 := bstep (se 2 (by rfl) ⟨419544, by rfl⟩ : syracuseStep 1118785 = 839089) B839089
theorem B1118819 : Blo 662308 1118819 := bstep (se 1 (by rfl) ⟨839114, by rfl⟩ : syracuseStep 1118819 = 1678229) B1678229
theorem B8622773 : Blo 662308 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B1118947 : Blo 662308 1118947 := bstep (se 1 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 1118947 = 1678421) B1678421
theorem B1119089 : Blo 662308 1119089 := bstep (se 2 (by rfl) ⟨419658, by rfl⟩ : syracuseStep 1119089 = 839317) B839317
theorem B1119217 : Blo 662308 1119217 := bstep (se 2 (by rfl) ⟨419706, by rfl⟩ : syracuseStep 1119217 = 839413) B839413
theorem B2692109 : Blo 662308 2692109 := bstep (se 3 (by rfl) ⟨504770, by rfl⟩ : syracuseStep 2692109 = 1009541) B1009541
theorem B1119251 : Blo 662308 1119251 := bstep (se 1 (by rfl) ⟨839438, by rfl⟩ : syracuseStep 1119251 = 1678877) B1678877
theorem B1348643 : Blo 662308 1348643 := bstep (se 1 (by rfl) ⟨1011482, by rfl⟩ : syracuseStep 1348643 = 2022965) B2022965
theorem B1119379 : Blo 662308 1119379 := bstep (se 1 (by rfl) ⟨839534, by rfl⟩ : syracuseStep 1119379 = 1679069) B1679069
theorem B1676497 : Blo 662308 1676497 := bstep (se 2 (by rfl) ⟨628686, by rfl⟩ : syracuseStep 1676497 = 1257373) B1257373
theorem B1119521 : Blo 662308 1119521 := bstep (se 2 (by rfl) ⟨419820, by rfl⟩ : syracuseStep 1119521 = 839641) B839641
theorem B1119649 : Blo 662308 1119649 := bstep (se 2 (by rfl) ⟨419868, by rfl⟩ : syracuseStep 1119649 = 839737) B839737
theorem B1119683 : Blo 662308 1119683 := bstep (se 1 (by rfl) ⟨839762, by rfl⟩ : syracuseStep 1119683 = 1679525) B1679525
theorem B1676771 : Blo 662308 1676771 := bstep (se 1 (by rfl) ⟨1257578, by rfl⟩ : syracuseStep 1676771 = 2515157) B2515157
theorem B1119811 : Blo 662308 1119811 := bstep (se 1 (by rfl) ⟨839858, by rfl⟩ : syracuseStep 1119811 = 1679717) B1679717
theorem B1676963 : Blo 662308 1676963 := bstep (se 1 (by rfl) ⟨1257722, by rfl⟩ : syracuseStep 1676963 = 2515445) B2515445
theorem B1119953 : Blo 662308 1119953 := bstep (se 2 (by rfl) ⟨419982, by rfl⟩ : syracuseStep 1119953 = 839965) B839965
theorem B1120081 : Blo 662308 1120081 := bstep (se 2 (by rfl) ⟨420030, by rfl⟩ : syracuseStep 1120081 = 840061) B840061
theorem B1120115 : Blo 662308 1120115 := bstep (se 1 (by rfl) ⟨840086, by rfl⟩ : syracuseStep 1120115 = 1680173) B1680173
theorem B2529251 : Blo 662308 2529251 := bstep (se 1 (by rfl) ⟨1896938, by rfl⟩ : syracuseStep 2529251 = 3793877) B3793877
theorem B2529265 : Blo 662308 2529265 := bstep (se 2 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 2529265 = 1896949) B1896949
theorem B1120243 : Blo 662308 1120243 := bstep (se 1 (by rfl) ⟨840182, by rfl⟩ : syracuseStep 1120243 = 1680365) B1680365
theorem B1022081 : Blo 662308 1022081 := bstep (se 2 (by rfl) ⟨383280, by rfl⟩ : syracuseStep 1022081 = 766561) B766561
theorem B1120385 : Blo 662308 1120385 := bstep (se 2 (by rfl) ⟨420144, by rfl⟩ : syracuseStep 1120385 = 840289) B840289
theorem B2398349 : Blo 662308 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B1317041 : Blo 662308 1317041 := bstep (se 2 (by rfl) ⟨493890, by rfl⟩ : syracuseStep 1317041 = 987781) B987781
theorem B1120513 : Blo 662308 1120513 := bstep (se 2 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 1120513 = 840385) B840385
theorem B1120547 : Blo 662308 1120547 := bstep (se 1 (by rfl) ⟨840410, by rfl⟩ : syracuseStep 1120547 = 1680821) B1680821
theorem B1120675 : Blo 662308 1120675 := bstep (se 1 (by rfl) ⟨840506, by rfl⟩ : syracuseStep 1120675 = 1681013) B1681013
theorem B5052941 : Blo 662308 5052941 := bstep (se 3 (by rfl) ⟨947426, by rfl⟩ : syracuseStep 5052941 = 1894853) B1894853
theorem B1120817 : Blo 662308 1120817 := bstep (se 2 (by rfl) ⟨420306, by rfl⟩ : syracuseStep 1120817 = 840613) B840613
theorem B1677905 : Blo 662308 1677905 := bstep (se 2 (by rfl) ⟨629214, by rfl⟩ : syracuseStep 1677905 = 1258429) B1258429
theorem B1677955 : Blo 662308 1677955 := bstep (se 1 (by rfl) ⟨1258466, by rfl⟩ : syracuseStep 1677955 = 2516933) B2516933
theorem B1120945 : Blo 662308 1120945 := bstep (se 2 (by rfl) ⟨420354, by rfl⟩ : syracuseStep 1120945 = 840709) B840709
theorem B4266701 : Blo 662308 4266701 := bstep (se 3 (by rfl) ⟨800006, by rfl⟩ : syracuseStep 4266701 = 1600013) B1600013
theorem B1120979 : Blo 662308 1120979 := bstep (se 1 (by rfl) ⟨840734, by rfl⟩ : syracuseStep 1120979 = 1681469) B1681469
theorem B1678097 : Blo 662308 1678097 := bstep (se 2 (by rfl) ⟨629286, by rfl⟩ : syracuseStep 1678097 = 1258573) B1258573
theorem B662323 : Blo 662308 662323 := bstep (se 1 (by rfl) ⟨496742, by rfl⟩ : syracuseStep 662323 = 993485) B993485
theorem B662339 : Blo 662308 662339 := bstep (se 1 (by rfl) ⟨496754, by rfl⟩ : syracuseStep 662339 = 993509) B993509
theorem B662355 : Blo 662308 662355 := bstep (se 1 (by rfl) ⟨496766, by rfl⟩ : syracuseStep 662355 = 993533) B993533
theorem B1121107 : Blo 662308 1121107 := bstep (se 1 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 1121107 = 1681661) B1681661
theorem B662371 : Blo 662308 662371 := bstep (se 1 (by rfl) ⟨496778, by rfl⟩ : syracuseStep 662371 = 993557) B993557
theorem B662387 : Blo 662308 662387 := bstep (se 1 (by rfl) ⟨496790, by rfl⟩ : syracuseStep 662387 = 993581) B993581
theorem B662403 : Blo 662308 662403 := bstep (se 1 (by rfl) ⟨496802, by rfl⟩ : syracuseStep 662403 = 993605) B993605
theorem B662419 : Blo 662308 662419 := bstep (se 1 (by rfl) ⟨496814, by rfl⟩ : syracuseStep 662419 = 993629) B993629
theorem B662435 : Blo 662308 662435 := bstep (se 1 (by rfl) ⟨496826, by rfl⟩ : syracuseStep 662435 = 993653) B993653
theorem B662451 : Blo 662308 662451 := bstep (se 1 (by rfl) ⟨496838, by rfl⟩ : syracuseStep 662451 = 993677) B993677
theorem B662467 : Blo 662308 662467 := bstep (se 1 (by rfl) ⟨496850, by rfl⟩ : syracuseStep 662467 = 993701) B993701
theorem B662483 : Blo 662308 662483 := bstep (se 1 (by rfl) ⟨496862, by rfl⟩ : syracuseStep 662483 = 993725) B993725
theorem B1121249 : Blo 662308 1121249 := bstep (se 2 (by rfl) ⟨420468, by rfl⟩ : syracuseStep 1121249 = 840937) B840937
theorem B662499 : Blo 662308 662499 := bstep (se 1 (by rfl) ⟨496874, by rfl⟩ : syracuseStep 662499 = 993749) B993749
theorem B6462449 : Blo 662308 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B662515 : Blo 662308 662515 := bstep (se 1 (by rfl) ⟨496886, by rfl⟩ : syracuseStep 662515 = 993773) B993773
theorem B662531 : Blo 662308 662531 := bstep (se 1 (by rfl) ⟨496898, by rfl⟩ : syracuseStep 662531 = 993797) B993797
theorem B662547 : Blo 662308 662547 := bstep (se 1 (by rfl) ⟨496910, by rfl⟩ : syracuseStep 662547 = 993821) B993821
theorem B662563 : Blo 662308 662563 := bstep (se 1 (by rfl) ⟨496922, by rfl⟩ : syracuseStep 662563 = 993845) B993845
theorem B2235437 : Blo 662308 2235437 := bstep (se 3 (by rfl) ⟨419144, by rfl⟩ : syracuseStep 2235437 = 838289) B838289
theorem B662579 : Blo 662308 662579 := bstep (se 1 (by rfl) ⟨496934, by rfl⟩ : syracuseStep 662579 = 993869) B993869
theorem B662595 : Blo 662308 662595 := bstep (se 1 (by rfl) ⟨496946, by rfl⟩ : syracuseStep 662595 = 993893) B993893
theorem B662611 : Blo 662308 662611 := bstep (se 1 (by rfl) ⟨496958, by rfl⟩ : syracuseStep 662611 = 993917) B993917
theorem B1121377 : Blo 662308 1121377 := bstep (se 2 (by rfl) ⟨420516, by rfl⟩ : syracuseStep 1121377 = 841033) B841033
theorem B2235491 : Blo 662308 2235491 := bstep (se 1 (by rfl) ⟨1676618, by rfl⟩ : syracuseStep 2235491 = 3353237) B3353237
theorem B662627 : Blo 662308 662627 := bstep (se 1 (by rfl) ⟨496970, by rfl⟩ : syracuseStep 662627 = 993941) B993941
theorem B1645667 : Blo 662308 1645667 := bstep (se 1 (by rfl) ⟨1234250, by rfl⟩ : syracuseStep 1645667 = 2468501) B2468501
theorem B1416305 : Blo 662308 1416305 := bstep (se 2 (by rfl) ⟨531114, by rfl⟩ : syracuseStep 1416305 = 1062229) B1062229
theorem B662643 : Blo 662308 662643 := bstep (se 1 (by rfl) ⟨496982, by rfl⟩ : syracuseStep 662643 = 993965) B993965
theorem B662659 : Blo 662308 662659 := bstep (se 1 (by rfl) ⟨496994, by rfl⟩ : syracuseStep 662659 = 993989) B993989
theorem B1121411 : Blo 662308 1121411 := bstep (se 1 (by rfl) ⟨841058, by rfl⟩ : syracuseStep 1121411 = 1682117) B1682117
theorem B662675 : Blo 662308 662675 := bstep (se 1 (by rfl) ⟨497006, by rfl⟩ : syracuseStep 662675 = 994013) B994013
theorem B662691 : Blo 662308 662691 := bstep (se 1 (by rfl) ⟨497018, by rfl⟩ : syracuseStep 662691 = 994037) B994037
theorem B662707 : Blo 662308 662707 := bstep (se 1 (by rfl) ⟨497030, by rfl⟩ : syracuseStep 662707 = 994061) B994061
theorem B662723 : Blo 662308 662723 := bstep (se 1 (by rfl) ⟨497042, by rfl⟩ : syracuseStep 662723 = 994085) B994085
theorem B662739 : Blo 662308 662739 := bstep (se 1 (by rfl) ⟨497054, by rfl⟩ : syracuseStep 662739 = 994109) B994109
theorem B662755 : Blo 662308 662755 := bstep (se 1 (by rfl) ⟨497066, by rfl⟩ : syracuseStep 662755 = 994133) B994133
theorem B2399473 : Blo 662308 2399473 := bstep (se 2 (by rfl) ⟨899802, by rfl⟩ : syracuseStep 2399473 = 1799605) B1799605
theorem B662771 : Blo 662308 662771 := bstep (se 1 (by rfl) ⟨497078, by rfl⟩ : syracuseStep 662771 = 994157) B994157
theorem B662787 : Blo 662308 662787 := bstep (se 1 (by rfl) ⟨497090, by rfl⟩ : syracuseStep 662787 = 994181) B994181
theorem B1121539 : Blo 662308 1121539 := bstep (se 1 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 1121539 = 1682309) B1682309
theorem B662803 : Blo 662308 662803 := bstep (se 1 (by rfl) ⟨497102, by rfl⟩ : syracuseStep 662803 = 994205) B994205
theorem B662819 : Blo 662308 662819 := bstep (se 1 (by rfl) ⟨497114, by rfl⟩ : syracuseStep 662819 = 994229) B994229
theorem B957745 : Blo 662308 957745 := bstep (se 2 (by rfl) ⟨359154, by rfl⟩ : syracuseStep 957745 = 718309) B718309
theorem B662835 : Blo 662308 662835 := bstep (se 1 (by rfl) ⟨497126, by rfl⟩ : syracuseStep 662835 = 994253) B994253
theorem B662851 : Blo 662308 662851 := bstep (se 1 (by rfl) ⟨497138, by rfl⟩ : syracuseStep 662851 = 994277) B994277
theorem B662867 : Blo 662308 662867 := bstep (se 1 (by rfl) ⟨497150, by rfl⟩ : syracuseStep 662867 = 994301) B994301
theorem B662883 : Blo 662308 662883 := bstep (se 1 (by rfl) ⟨497162, by rfl⟩ : syracuseStep 662883 = 994325) B994325
theorem B2235761 : Blo 662308 2235761 := bstep (se 2 (by rfl) ⟨838410, by rfl⟩ : syracuseStep 2235761 = 1676821) B1676821
theorem B662899 : Blo 662308 662899 := bstep (se 1 (by rfl) ⟨497174, by rfl⟩ : syracuseStep 662899 = 994349) B994349
theorem B662915 : Blo 662308 662915 := bstep (se 1 (by rfl) ⟨497186, by rfl⟩ : syracuseStep 662915 = 994373) B994373
theorem B8068493 : Blo 662308 8068493 := bstep (se 3 (by rfl) ⟨1512842, by rfl⟩ : syracuseStep 8068493 = 3025685) B3025685
theorem B1121681 : Blo 662308 1121681 := bstep (se 2 (by rfl) ⟨420630, by rfl⟩ : syracuseStep 1121681 = 841261) B841261
theorem B662931 : Blo 662308 662931 := bstep (se 1 (by rfl) ⟨497198, by rfl⟩ : syracuseStep 662931 = 994397) B994397
theorem B662947 : Blo 662308 662947 := bstep (se 1 (by rfl) ⟨497210, by rfl⟩ : syracuseStep 662947 = 994421) B994421
theorem B662963 : Blo 662308 662963 := bstep (se 1 (by rfl) ⟨497222, by rfl⟩ : syracuseStep 662963 = 994445) B994445
theorem B662979 : Blo 662308 662979 := bstep (se 1 (by rfl) ⟨497234, by rfl⟩ : syracuseStep 662979 = 994469) B994469
theorem B662995 : Blo 662308 662995 := bstep (se 1 (by rfl) ⟨497246, by rfl⟩ : syracuseStep 662995 = 994493) B994493
theorem B663011 : Blo 662308 663011 := bstep (se 1 (by rfl) ⟨497258, by rfl⟩ : syracuseStep 663011 = 994517) B994517
theorem B663027 : Blo 662308 663027 := bstep (se 1 (by rfl) ⟨497270, by rfl⟩ : syracuseStep 663027 = 994541) B994541
theorem B663043 : Blo 662308 663043 := bstep (se 1 (by rfl) ⟨497282, by rfl⟩ : syracuseStep 663043 = 994565) B994565
theorem B7183885 : Blo 662308 7183885 := bstep (se 3 (by rfl) ⟨1346978, by rfl⟩ : syracuseStep 7183885 = 2693957) B2693957
theorem B1121809 : Blo 662308 1121809 := bstep (se 2 (by rfl) ⟨420678, by rfl⟩ : syracuseStep 1121809 = 841357) B841357
theorem B663059 : Blo 662308 663059 := bstep (se 1 (by rfl) ⟨497294, by rfl⟩ : syracuseStep 663059 = 994589) B994589
theorem B663075 : Blo 662308 663075 := bstep (se 1 (by rfl) ⟨497306, by rfl⟩ : syracuseStep 663075 = 994613) B994613
theorem B663091 : Blo 662308 663091 := bstep (se 1 (by rfl) ⟨497318, by rfl⟩ : syracuseStep 663091 = 994637) B994637
theorem B1121843 : Blo 662308 1121843 := bstep (se 1 (by rfl) ⟨841382, by rfl⟩ : syracuseStep 1121843 = 1682765) B1682765
theorem B663107 : Blo 662308 663107 := bstep (se 1 (by rfl) ⟨497330, by rfl⟩ : syracuseStep 663107 = 994661) B994661
theorem B663123 : Blo 662308 663123 := bstep (se 1 (by rfl) ⟨497342, by rfl⟩ : syracuseStep 663123 = 994685) B994685
theorem B663139 : Blo 662308 663139 := bstep (se 1 (by rfl) ⟨497354, by rfl⟩ : syracuseStep 663139 = 994709) B994709
theorem B663155 : Blo 662308 663155 := bstep (se 1 (by rfl) ⟨497366, by rfl⟩ : syracuseStep 663155 = 994733) B994733
theorem B663171 : Blo 662308 663171 := bstep (se 1 (by rfl) ⟨497378, by rfl⟩ : syracuseStep 663171 = 994757) B994757
theorem B663187 : Blo 662308 663187 := bstep (se 1 (by rfl) ⟨497390, by rfl⟩ : syracuseStep 663187 = 994781) B994781
theorem B663203 : Blo 662308 663203 := bstep (se 1 (by rfl) ⟨497402, by rfl⟩ : syracuseStep 663203 = 994805) B994805
theorem B663219 : Blo 662308 663219 := bstep (se 1 (by rfl) ⟨497414, by rfl⟩ : syracuseStep 663219 = 994829) B994829
theorem B1121971 : Blo 662308 1121971 := bstep (se 1 (by rfl) ⟨841478, by rfl⟩ : syracuseStep 1121971 = 1682957) B1682957
theorem B663235 : Blo 662308 663235 := bstep (se 1 (by rfl) ⟨497426, by rfl⟩ : syracuseStep 663235 = 994853) B994853
theorem B663251 : Blo 662308 663251 := bstep (se 1 (by rfl) ⟨497438, by rfl⟩ : syracuseStep 663251 = 994877) B994877
theorem B663267 : Blo 662308 663267 := bstep (se 1 (by rfl) ⟨497450, by rfl⟩ : syracuseStep 663267 = 994901) B994901
theorem B1679089 : Blo 662308 1679089 := bstep (se 2 (by rfl) ⟨629658, by rfl⟩ : syracuseStep 1679089 = 1259317) B1259317
theorem B663283 : Blo 662308 663283 := bstep (se 1 (by rfl) ⟨497462, by rfl⟩ : syracuseStep 663283 = 994925) B994925
theorem B663299 : Blo 662308 663299 := bstep (se 1 (by rfl) ⟨497474, by rfl⟩ : syracuseStep 663299 = 994949) B994949
theorem B663315 : Blo 662308 663315 := bstep (se 1 (by rfl) ⟨497486, by rfl⟩ : syracuseStep 663315 = 994973) B994973
theorem B663331 : Blo 662308 663331 := bstep (se 1 (by rfl) ⟨497498, by rfl⟩ : syracuseStep 663331 = 994997) B994997
theorem B663347 : Blo 662308 663347 := bstep (se 1 (by rfl) ⟨497510, by rfl⟩ : syracuseStep 663347 = 995021) B995021
theorem B1122113 : Blo 662308 1122113 := bstep (se 2 (by rfl) ⟨420792, by rfl⟩ : syracuseStep 1122113 = 841585) B841585
theorem B663363 : Blo 662308 663363 := bstep (se 1 (by rfl) ⟨497522, by rfl⟩ : syracuseStep 663363 = 995045) B995045
theorem B728899 : Blo 662308 728899 := bstep (se 1 (by rfl) ⟨546674, by rfl⟩ : syracuseStep 728899 = 1093349) B1093349
theorem B663379 : Blo 662308 663379 := bstep (se 1 (by rfl) ⟨497534, by rfl⟩ : syracuseStep 663379 = 995069) B995069
theorem B663395 : Blo 662308 663395 := bstep (se 1 (by rfl) ⟨497546, by rfl⟩ : syracuseStep 663395 = 995093) B995093
theorem B663411 : Blo 662308 663411 := bstep (se 1 (by rfl) ⟨497558, by rfl⟩ : syracuseStep 663411 = 995117) B995117
theorem B663427 : Blo 662308 663427 := bstep (se 1 (by rfl) ⟨497570, by rfl⟩ : syracuseStep 663427 = 995141) B995141
theorem B2236301 : Blo 662308 2236301 := bstep (se 3 (by rfl) ⟨419306, by rfl⟩ : syracuseStep 2236301 = 838613) B838613
theorem B663443 : Blo 662308 663443 := bstep (se 1 (by rfl) ⟨497582, by rfl⟩ : syracuseStep 663443 = 995165) B995165
theorem B663459 : Blo 662308 663459 := bstep (se 1 (by rfl) ⟨497594, by rfl⟩ : syracuseStep 663459 = 995189) B995189
theorem B663475 : Blo 662308 663475 := bstep (se 1 (by rfl) ⟨497606, by rfl⟩ : syracuseStep 663475 = 995213) B995213
theorem B1122241 : Blo 662308 1122241 := bstep (se 2 (by rfl) ⟨420840, by rfl⟩ : syracuseStep 1122241 = 841681) B841681
theorem B2236355 : Blo 662308 2236355 := bstep (se 1 (by rfl) ⟨1677266, by rfl⟩ : syracuseStep 2236355 = 3354533) B3354533
theorem B663491 : Blo 662308 663491 := bstep (se 1 (by rfl) ⟨497618, by rfl⟩ : syracuseStep 663491 = 995237) B995237
theorem B4038605 : Blo 662308 4038605 := bstep (se 3 (by rfl) ⟨757238, by rfl⟩ : syracuseStep 4038605 = 1514477) B1514477
theorem B1417169 : Blo 662308 1417169 := bstep (se 2 (by rfl) ⟨531438, by rfl⟩ : syracuseStep 1417169 = 1062877) B1062877
theorem B663507 : Blo 662308 663507 := bstep (se 1 (by rfl) ⟨497630, by rfl⟩ : syracuseStep 663507 = 995261) B995261
theorem B663523 : Blo 662308 663523 := bstep (se 1 (by rfl) ⟨497642, by rfl⟩ : syracuseStep 663523 = 995285) B995285
theorem B1122275 : Blo 662308 1122275 := bstep (se 1 (by rfl) ⟨841706, by rfl⟩ : syracuseStep 1122275 = 1683413) B1683413
theorem B663539 : Blo 662308 663539 := bstep (se 1 (by rfl) ⟨497654, by rfl⟩ : syracuseStep 663539 = 995309) B995309
theorem B1679363 : Blo 662308 1679363 := bstep (se 1 (by rfl) ⟨1259522, by rfl⟩ : syracuseStep 1679363 = 2519045) B2519045
theorem B663555 : Blo 662308 663555 := bstep (se 1 (by rfl) ⟨497666, by rfl⟩ : syracuseStep 663555 = 995333) B995333
theorem B663571 : Blo 662308 663571 := bstep (se 1 (by rfl) ⟨497678, by rfl⟩ : syracuseStep 663571 = 995357) B995357
theorem B663587 : Blo 662308 663587 := bstep (se 1 (by rfl) ⟨497690, by rfl⟩ : syracuseStep 663587 = 995381) B995381
theorem B663603 : Blo 662308 663603 := bstep (se 1 (by rfl) ⟨497702, by rfl⟩ : syracuseStep 663603 = 995405) B995405
theorem B663619 : Blo 662308 663619 := bstep (se 1 (by rfl) ⟨497714, by rfl⟩ : syracuseStep 663619 = 995429) B995429
theorem B663635 : Blo 662308 663635 := bstep (se 1 (by rfl) ⟨497726, by rfl⟩ : syracuseStep 663635 = 995453) B995453
theorem B663651 : Blo 662308 663651 := bstep (se 1 (by rfl) ⟨497738, by rfl⟩ : syracuseStep 663651 = 995477) B995477
theorem B1122403 : Blo 662308 1122403 := bstep (se 1 (by rfl) ⟨841802, by rfl⟩ : syracuseStep 1122403 = 1683605) B1683605
theorem B663667 : Blo 662308 663667 := bstep (se 1 (by rfl) ⟨497750, by rfl⟩ : syracuseStep 663667 = 995501) B995501
theorem B663683 : Blo 662308 663683 := bstep (se 1 (by rfl) ⟨497762, by rfl⟩ : syracuseStep 663683 = 995525) B995525
theorem B663699 : Blo 662308 663699 := bstep (se 1 (by rfl) ⟨497774, by rfl⟩ : syracuseStep 663699 = 995549) B995549
theorem B663715 : Blo 662308 663715 := bstep (se 1 (by rfl) ⟨497786, by rfl⟩ : syracuseStep 663715 = 995573) B995573
theorem B663731 : Blo 662308 663731 := bstep (se 1 (by rfl) ⟨497798, by rfl⟩ : syracuseStep 663731 = 995597) B995597
theorem B1679555 : Blo 662308 1679555 := bstep (se 1 (by rfl) ⟨1259666, by rfl⟩ : syracuseStep 1679555 = 2519333) B2519333
theorem B663747 : Blo 662308 663747 := bstep (se 1 (by rfl) ⟨497810, by rfl⟩ : syracuseStep 663747 = 995621) B995621
theorem B2236625 : Blo 662308 2236625 := bstep (se 2 (by rfl) ⟨838734, by rfl⟩ : syracuseStep 2236625 = 1677469) B1677469
theorem B663763 : Blo 662308 663763 := bstep (se 1 (by rfl) ⟨497822, by rfl⟩ : syracuseStep 663763 = 995645) B995645
theorem B663779 : Blo 662308 663779 := bstep (se 1 (by rfl) ⟨497834, by rfl⟩ : syracuseStep 663779 = 995669) B995669
theorem B1122545 : Blo 662308 1122545 := bstep (se 2 (by rfl) ⟨420954, by rfl⟩ : syracuseStep 1122545 = 841909) B841909
theorem B663795 : Blo 662308 663795 := bstep (se 1 (by rfl) ⟨497846, by rfl⟩ : syracuseStep 663795 = 995693) B995693
theorem B663811 : Blo 662308 663811 := bstep (se 1 (by rfl) ⟨497858, by rfl⟩ : syracuseStep 663811 = 995717) B995717
theorem B663827 : Blo 662308 663827 := bstep (se 1 (by rfl) ⟨497870, by rfl⟩ : syracuseStep 663827 = 995741) B995741
theorem B663843 : Blo 662308 663843 := bstep (se 1 (by rfl) ⟨497882, by rfl⟩ : syracuseStep 663843 = 995765) B995765
theorem B663859 : Blo 662308 663859 := bstep (se 1 (by rfl) ⟨497894, by rfl⟩ : syracuseStep 663859 = 995789) B995789
theorem B663875 : Blo 662308 663875 := bstep (se 1 (by rfl) ⟨497906, by rfl⟩ : syracuseStep 663875 = 995813) B995813
theorem B663891 : Blo 662308 663891 := bstep (se 1 (by rfl) ⟨497918, by rfl⟩ : syracuseStep 663891 = 995837) B995837
theorem B663907 : Blo 662308 663907 := bstep (se 1 (by rfl) ⟨497930, by rfl⟩ : syracuseStep 663907 = 995861) B995861
theorem B1122673 : Blo 662308 1122673 := bstep (se 2 (by rfl) ⟨421002, by rfl⟩ : syracuseStep 1122673 = 842005) B842005
theorem B663923 : Blo 662308 663923 := bstep (se 1 (by rfl) ⟨497942, by rfl⟩ : syracuseStep 663923 = 995885) B995885
theorem B663939 : Blo 662308 663939 := bstep (se 1 (by rfl) ⟨497954, by rfl⟩ : syracuseStep 663939 = 995909) B995909
theorem B663955 : Blo 662308 663955 := bstep (se 1 (by rfl) ⟨497966, by rfl⟩ : syracuseStep 663955 = 995933) B995933
theorem B1122707 : Blo 662308 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B663971 : Blo 662308 663971 := bstep (se 1 (by rfl) ⟨497978, by rfl⟩ : syracuseStep 663971 = 995957) B995957
theorem B663987 : Blo 662308 663987 := bstep (se 1 (by rfl) ⟨497990, by rfl⟩ : syracuseStep 663987 = 995981) B995981
theorem B664003 : Blo 662308 664003 := bstep (se 1 (by rfl) ⟨498002, by rfl⟩ : syracuseStep 664003 = 996005) B996005
theorem B664019 : Blo 662308 664019 := bstep (se 1 (by rfl) ⟨498014, by rfl⟩ : syracuseStep 664019 = 996029) B996029
theorem B664035 : Blo 662308 664035 := bstep (se 1 (by rfl) ⟨498026, by rfl⟩ : syracuseStep 664035 = 996053) B996053
theorem B664051 : Blo 662308 664051 := bstep (se 1 (by rfl) ⟨498038, by rfl⟩ : syracuseStep 664051 = 996077) B996077
theorem B664067 : Blo 662308 664067 := bstep (se 1 (by rfl) ⟨498050, by rfl⟩ : syracuseStep 664067 = 996101) B996101
theorem B664083 : Blo 662308 664083 := bstep (se 1 (by rfl) ⟨498062, by rfl⟩ : syracuseStep 664083 = 996125) B996125
theorem B1122835 : Blo 662308 1122835 := bstep (se 1 (by rfl) ⟨842126, by rfl⟩ : syracuseStep 1122835 = 1684253) B1684253
theorem B664099 : Blo 662308 664099 := bstep (se 1 (by rfl) ⟨498074, by rfl⟩ : syracuseStep 664099 = 996149) B996149
theorem B664115 : Blo 662308 664115 := bstep (se 1 (by rfl) ⟨498086, by rfl⟩ : syracuseStep 664115 = 996173) B996173
theorem B664131 : Blo 662308 664131 := bstep (se 1 (by rfl) ⟨498098, by rfl⟩ : syracuseStep 664131 = 996197) B996197
theorem B664147 : Blo 662308 664147 := bstep (se 1 (by rfl) ⟨498110, by rfl⟩ : syracuseStep 664147 = 996221) B996221
theorem B664163 : Blo 662308 664163 := bstep (se 1 (by rfl) ⟨498122, by rfl⟩ : syracuseStep 664163 = 996245) B996245
theorem B664179 : Blo 662308 664179 := bstep (se 1 (by rfl) ⟨498134, by rfl⟩ : syracuseStep 664179 = 996269) B996269
theorem B664195 : Blo 662308 664195 := bstep (se 1 (by rfl) ⟨498146, by rfl⟩ : syracuseStep 664195 = 996293) B996293
theorem B664211 : Blo 662308 664211 := bstep (se 1 (by rfl) ⟨498158, by rfl⟩ : syracuseStep 664211 = 996317) B996317
theorem B1122977 : Blo 662308 1122977 := bstep (se 2 (by rfl) ⟨421116, by rfl⟩ : syracuseStep 1122977 = 842233) B842233
theorem B664227 : Blo 662308 664227 := bstep (se 1 (by rfl) ⟨498170, by rfl⟩ : syracuseStep 664227 = 996341) B996341
theorem B664243 : Blo 662308 664243 := bstep (se 1 (by rfl) ⟨498182, by rfl⟩ : syracuseStep 664243 = 996365) B996365
theorem B664259 : Blo 662308 664259 := bstep (se 1 (by rfl) ⟨498194, by rfl⟩ : syracuseStep 664259 = 996389) B996389
theorem B664275 : Blo 662308 664275 := bstep (se 1 (by rfl) ⟨498206, by rfl⟩ : syracuseStep 664275 = 996413) B996413
theorem B664291 : Blo 662308 664291 := bstep (se 1 (by rfl) ⟨498218, by rfl⟩ : syracuseStep 664291 = 996437) B996437
theorem B2237165 : Blo 662308 2237165 := bstep (se 3 (by rfl) ⟨419468, by rfl⟩ : syracuseStep 2237165 = 838937) B838937
theorem B664307 : Blo 662308 664307 := bstep (se 1 (by rfl) ⟨498230, by rfl⟩ : syracuseStep 664307 = 996461) B996461
theorem B664323 : Blo 662308 664323 := bstep (se 1 (by rfl) ⟨498242, by rfl⟩ : syracuseStep 664323 = 996485) B996485
theorem B664339 : Blo 662308 664339 := bstep (se 1 (by rfl) ⟨498254, by rfl⟩ : syracuseStep 664339 = 996509) B996509
theorem B2237219 : Blo 662308 2237219 := bstep (se 1 (by rfl) ⟨1677914, by rfl⟩ : syracuseStep 2237219 = 3355829) B3355829
theorem B664355 : Blo 662308 664355 := bstep (se 1 (by rfl) ⟨498266, by rfl⟩ : syracuseStep 664355 = 996533) B996533
theorem B1123105 : Blo 662308 1123105 := bstep (se 2 (by rfl) ⟨421164, by rfl⟩ : syracuseStep 1123105 = 842329) B842329
theorem B664371 : Blo 662308 664371 := bstep (se 1 (by rfl) ⟨498278, by rfl⟩ : syracuseStep 664371 = 996557) B996557
theorem B664387 : Blo 662308 664387 := bstep (se 1 (by rfl) ⟨498290, by rfl⟩ : syracuseStep 664387 = 996581) B996581
theorem B1123139 : Blo 662308 1123139 := bstep (se 1 (by rfl) ⟨842354, by rfl⟩ : syracuseStep 1123139 = 1684709) B1684709
theorem B664403 : Blo 662308 664403 := bstep (se 1 (by rfl) ⟨498302, by rfl⟩ : syracuseStep 664403 = 996605) B996605
theorem B664419 : Blo 662308 664419 := bstep (se 1 (by rfl) ⟨498314, by rfl⟩ : syracuseStep 664419 = 996629) B996629
theorem B664435 : Blo 662308 664435 := bstep (se 1 (by rfl) ⟨498326, by rfl⟩ : syracuseStep 664435 = 996653) B996653
theorem B664451 : Blo 662308 664451 := bstep (se 1 (by rfl) ⟨498338, by rfl⟩ : syracuseStep 664451 = 996677) B996677
theorem B4268933 : Blo 662308 4268933 := bstep (se 4 (by rfl) ⟨400212, by rfl⟩ : syracuseStep 4268933 = 800425) B800425
theorem B664467 : Blo 662308 664467 := bstep (se 1 (by rfl) ⟨498350, by rfl⟩ : syracuseStep 664467 = 996701) B996701
theorem B664483 : Blo 662308 664483 := bstep (se 1 (by rfl) ⟨498362, by rfl⟩ : syracuseStep 664483 = 996725) B996725
theorem B664499 : Blo 662308 664499 := bstep (se 1 (by rfl) ⟨498374, by rfl⟩ : syracuseStep 664499 = 996749) B996749
theorem B664515 : Blo 662308 664515 := bstep (se 1 (by rfl) ⟨498386, by rfl⟩ : syracuseStep 664515 = 996773) B996773
theorem B1123267 : Blo 662308 1123267 := bstep (se 1 (by rfl) ⟨842450, by rfl⟩ : syracuseStep 1123267 = 1684901) B1684901
theorem B664531 : Blo 662308 664531 := bstep (se 1 (by rfl) ⟨498398, by rfl⟩ : syracuseStep 664531 = 996797) B996797
theorem B664547 : Blo 662308 664547 := bstep (se 1 (by rfl) ⟨498410, by rfl⟩ : syracuseStep 664547 = 996821) B996821
theorem B664563 : Blo 662308 664563 := bstep (se 1 (by rfl) ⟨498422, by rfl⟩ : syracuseStep 664563 = 996845) B996845
theorem B664579 : Blo 662308 664579 := bstep (se 1 (by rfl) ⟨498434, by rfl⟩ : syracuseStep 664579 = 996869) B996869
theorem B6366221 : Blo 662308 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B664595 : Blo 662308 664595 := bstep (se 1 (by rfl) ⟨498446, by rfl⟩ : syracuseStep 664595 = 996893) B996893
theorem B664611 : Blo 662308 664611 := bstep (se 1 (by rfl) ⟨498458, by rfl⟩ : syracuseStep 664611 = 996917) B996917
theorem B2237489 : Blo 662308 2237489 := bstep (se 2 (by rfl) ⟨839058, by rfl⟩ : syracuseStep 2237489 = 1678117) B1678117
theorem B664627 : Blo 662308 664627 := bstep (se 1 (by rfl) ⟨498470, by rfl⟩ : syracuseStep 664627 = 996941) B996941
theorem B664643 : Blo 662308 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B1123409 : Blo 662308 1123409 := bstep (se 2 (by rfl) ⟨421278, by rfl⟩ : syracuseStep 1123409 = 842557) B842557
theorem B664659 : Blo 662308 664659 := bstep (se 1 (by rfl) ⟨498494, by rfl⟩ : syracuseStep 664659 = 996989) B996989
theorem B664675 : Blo 662308 664675 := bstep (se 1 (by rfl) ⟨498506, by rfl⟩ : syracuseStep 664675 = 997013) B997013
theorem B1680497 : Blo 662308 1680497 := bstep (se 2 (by rfl) ⟨630186, by rfl⟩ : syracuseStep 1680497 = 1260373) B1260373
theorem B664691 : Blo 662308 664691 := bstep (se 1 (by rfl) ⟨498518, by rfl⟩ : syracuseStep 664691 = 997037) B997037
theorem B664707 : Blo 662308 664707 := bstep (se 1 (by rfl) ⟨498530, by rfl⟩ : syracuseStep 664707 = 997061) B997061
theorem B664723 : Blo 662308 664723 := bstep (se 1 (by rfl) ⟨498542, by rfl⟩ : syracuseStep 664723 = 997085) B997085
theorem B1680547 : Blo 662308 1680547 := bstep (se 1 (by rfl) ⟨1260410, by rfl⟩ : syracuseStep 1680547 = 2520821) B2520821
theorem B664739 : Blo 662308 664739 := bstep (se 1 (by rfl) ⟨498554, by rfl⟩ : syracuseStep 664739 = 997109) B997109
theorem B664755 : Blo 662308 664755 := bstep (se 1 (by rfl) ⟨498566, by rfl⟩ : syracuseStep 664755 = 997133) B997133
theorem B664771 : Blo 662308 664771 := bstep (se 1 (by rfl) ⟨498578, by rfl⟩ : syracuseStep 664771 = 997157) B997157
theorem B1123537 : Blo 662308 1123537 := bstep (se 2 (by rfl) ⟨421326, by rfl⟩ : syracuseStep 1123537 = 842653) B842653
theorem B664787 : Blo 662308 664787 := bstep (se 1 (by rfl) ⟨498590, by rfl⟩ : syracuseStep 664787 = 997181) B997181
theorem B1418467 : Blo 662308 1418467 := bstep (se 1 (by rfl) ⟨1063850, by rfl⟩ : syracuseStep 1418467 = 2127701) B2127701
theorem B664803 : Blo 662308 664803 := bstep (se 1 (by rfl) ⟨498602, by rfl⟩ : syracuseStep 664803 = 997205) B997205
theorem B664819 : Blo 662308 664819 := bstep (se 1 (by rfl) ⟨498614, by rfl⟩ : syracuseStep 664819 = 997229) B997229
theorem B1123571 : Blo 662308 1123571 := bstep (se 1 (by rfl) ⟨842678, by rfl⟩ : syracuseStep 1123571 = 1685357) B1685357
theorem B664835 : Blo 662308 664835 := bstep (se 1 (by rfl) ⟨498626, by rfl⟩ : syracuseStep 664835 = 997253) B997253
theorem B664851 : Blo 662308 664851 := bstep (se 1 (by rfl) ⟨498638, by rfl⟩ : syracuseStep 664851 = 997277) B997277
theorem B664867 : Blo 662308 664867 := bstep (se 1 (by rfl) ⟨498650, by rfl⟩ : syracuseStep 664867 = 997301) B997301
theorem B1680689 : Blo 662308 1680689 := bstep (se 2 (by rfl) ⟨630258, by rfl⟩ : syracuseStep 1680689 = 1260517) B1260517
theorem B664883 : Blo 662308 664883 := bstep (se 1 (by rfl) ⟨498662, by rfl⟩ : syracuseStep 664883 = 997325) B997325
theorem B664899 : Blo 662308 664899 := bstep (se 1 (by rfl) ⟨498674, by rfl⟩ : syracuseStep 664899 = 997349) B997349
theorem B664915 : Blo 662308 664915 := bstep (se 1 (by rfl) ⟨498686, by rfl⟩ : syracuseStep 664915 = 997373) B997373
theorem B664931 : Blo 662308 664931 := bstep (se 1 (by rfl) ⟨498698, by rfl⟩ : syracuseStep 664931 = 997397) B997397
theorem B5055857 : Blo 662308 5055857 := bstep (se 2 (by rfl) ⟨1895946, by rfl⟩ : syracuseStep 5055857 = 3791893) B3791893
theorem B664947 : Blo 662308 664947 := bstep (se 1 (by rfl) ⟨498710, by rfl⟩ : syracuseStep 664947 = 997421) B997421
theorem B1123699 : Blo 662308 1123699 := bstep (se 1 (by rfl) ⟨842774, by rfl⟩ : syracuseStep 1123699 = 1685549) B1685549
theorem B664963 : Blo 662308 664963 := bstep (se 1 (by rfl) ⟨498722, by rfl⟩ : syracuseStep 664963 = 997445) B997445
theorem B664979 : Blo 662308 664979 := bstep (se 1 (by rfl) ⟨498734, by rfl⟩ : syracuseStep 664979 = 997469) B997469
theorem B664995 : Blo 662308 664995 := bstep (se 1 (by rfl) ⟨498746, by rfl⟩ : syracuseStep 664995 = 997493) B997493
theorem B665011 : Blo 662308 665011 := bstep (se 1 (by rfl) ⟨498758, by rfl⟩ : syracuseStep 665011 = 997517) B997517
theorem B665027 : Blo 662308 665027 := bstep (se 1 (by rfl) ⟨498770, by rfl⟩ : syracuseStep 665027 = 997541) B997541
theorem B665043 : Blo 662308 665043 := bstep (se 1 (by rfl) ⟨498782, by rfl⟩ : syracuseStep 665043 = 997565) B997565
theorem B665059 : Blo 662308 665059 := bstep (se 1 (by rfl) ⟨498794, by rfl⟩ : syracuseStep 665059 = 997589) B997589
theorem B665075 : Blo 662308 665075 := bstep (se 1 (by rfl) ⟨498806, by rfl⟩ : syracuseStep 665075 = 997613) B997613
theorem B1123841 : Blo 662308 1123841 := bstep (se 2 (by rfl) ⟨421440, by rfl⟩ : syracuseStep 1123841 = 842881) B842881
theorem B665091 : Blo 662308 665091 := bstep (se 1 (by rfl) ⟨498818, by rfl⟩ : syracuseStep 665091 = 997637) B997637
theorem B665107 : Blo 662308 665107 := bstep (se 1 (by rfl) ⟨498830, by rfl⟩ : syracuseStep 665107 = 997661) B997661
theorem B665123 : Blo 662308 665123 := bstep (se 1 (by rfl) ⟨498842, by rfl⟩ : syracuseStep 665123 = 997685) B997685
theorem B665139 : Blo 662308 665139 := bstep (se 1 (by rfl) ⟨498854, by rfl⟩ : syracuseStep 665139 = 997709) B997709
theorem B665155 : Blo 662308 665155 := bstep (se 1 (by rfl) ⟨498866, by rfl⟩ : syracuseStep 665155 = 997733) B997733
theorem B2238029 : Blo 662308 2238029 := bstep (se 3 (by rfl) ⟨419630, by rfl⟩ : syracuseStep 2238029 = 839261) B839261
theorem B665171 : Blo 662308 665171 := bstep (se 1 (by rfl) ⟨498878, by rfl⟩ : syracuseStep 665171 = 997757) B997757
theorem B665187 : Blo 662308 665187 := bstep (se 1 (by rfl) ⟨498890, by rfl⟩ : syracuseStep 665187 = 997781) B997781
theorem B665203 : Blo 662308 665203 := bstep (se 1 (by rfl) ⟨498902, by rfl⟩ : syracuseStep 665203 = 997805) B997805
theorem B1123969 : Blo 662308 1123969 := bstep (se 2 (by rfl) ⟨421488, by rfl⟩ : syracuseStep 1123969 = 842977) B842977
theorem B2238083 : Blo 662308 2238083 := bstep (se 1 (by rfl) ⟨1678562, by rfl⟩ : syracuseStep 2238083 = 3357125) B3357125
theorem B665219 : Blo 662308 665219 := bstep (se 1 (by rfl) ⟨498914, by rfl⟩ : syracuseStep 665219 = 997829) B997829
theorem B665235 : Blo 662308 665235 := bstep (se 1 (by rfl) ⟨498926, by rfl⟩ : syracuseStep 665235 = 997853) B997853
theorem B665251 : Blo 662308 665251 := bstep (se 1 (by rfl) ⟨498938, by rfl⟩ : syracuseStep 665251 = 997877) B997877
theorem B1124003 : Blo 662308 1124003 := bstep (se 1 (by rfl) ⟨843002, by rfl⟩ : syracuseStep 1124003 = 1686005) B1686005
theorem B665267 : Blo 662308 665267 := bstep (se 1 (by rfl) ⟨498950, by rfl⟩ : syracuseStep 665267 = 997901) B997901
theorem B665283 : Blo 662308 665283 := bstep (se 1 (by rfl) ⟨498962, by rfl⟩ : syracuseStep 665283 = 997925) B997925
theorem B665299 : Blo 662308 665299 := bstep (se 1 (by rfl) ⟨498974, by rfl⟩ : syracuseStep 665299 = 997949) B997949
theorem B3024611 : Blo 662308 3024611 := bstep (se 1 (by rfl) ⟨2268458, by rfl⟩ : syracuseStep 3024611 = 4536917) B4536917
theorem B5678819 : Blo 662308 5678819 := bstep (se 1 (by rfl) ⟨4259114, by rfl⟩ : syracuseStep 5678819 = 8518229) B8518229
theorem B665315 : Blo 662308 665315 := bstep (se 1 (by rfl) ⟨498986, by rfl⟩ : syracuseStep 665315 = 997973) B997973
theorem B665331 : Blo 662308 665331 := bstep (se 1 (by rfl) ⟨498998, by rfl⟩ : syracuseStep 665331 = 997997) B997997
theorem B665347 : Blo 662308 665347 := bstep (se 1 (by rfl) ⟨499010, by rfl⟩ : syracuseStep 665347 = 998021) B998021
theorem B665363 : Blo 662308 665363 := bstep (se 1 (by rfl) ⟨499022, by rfl⟩ : syracuseStep 665363 = 998045) B998045
theorem B665379 : Blo 662308 665379 := bstep (se 1 (by rfl) ⟨499034, by rfl⟩ : syracuseStep 665379 = 998069) B998069
theorem B1124131 : Blo 662308 1124131 := bstep (se 1 (by rfl) ⟨843098, by rfl⟩ : syracuseStep 1124131 = 1686197) B1686197
theorem B665395 : Blo 662308 665395 := bstep (se 1 (by rfl) ⟨499046, by rfl⟩ : syracuseStep 665395 = 998093) B998093
theorem B665411 : Blo 662308 665411 := bstep (se 1 (by rfl) ⟨499058, by rfl⟩ : syracuseStep 665411 = 998117) B998117
theorem B665427 : Blo 662308 665427 := bstep (se 1 (by rfl) ⟨499070, by rfl⟩ : syracuseStep 665427 = 998141) B998141
theorem B665443 : Blo 662308 665443 := bstep (se 1 (by rfl) ⟨499082, by rfl⟩ : syracuseStep 665443 = 998165) B998165
theorem B665459 : Blo 662308 665459 := bstep (se 1 (by rfl) ⟨499094, by rfl⟩ : syracuseStep 665459 = 998189) B998189
theorem B665475 : Blo 662308 665475 := bstep (se 1 (by rfl) ⟨499106, by rfl⟩ : syracuseStep 665475 = 998213) B998213
theorem B2238353 : Blo 662308 2238353 := bstep (se 2 (by rfl) ⟨839382, by rfl⟩ : syracuseStep 2238353 = 1678765) B1678765
theorem B665491 : Blo 662308 665491 := bstep (se 1 (by rfl) ⟨499118, by rfl⟩ : syracuseStep 665491 = 998237) B998237
theorem B665507 : Blo 662308 665507 := bstep (se 1 (by rfl) ⟨499130, by rfl⟩ : syracuseStep 665507 = 998261) B998261
theorem B1124273 : Blo 662308 1124273 := bstep (se 2 (by rfl) ⟨421602, by rfl⟩ : syracuseStep 1124273 = 843205) B843205
theorem B665523 : Blo 662308 665523 := bstep (se 1 (by rfl) ⟨499142, by rfl⟩ : syracuseStep 665523 = 998285) B998285
theorem B665539 : Blo 662308 665539 := bstep (se 1 (by rfl) ⟨499154, by rfl⟩ : syracuseStep 665539 = 998309) B998309
theorem B665555 : Blo 662308 665555 := bstep (se 1 (by rfl) ⟨499166, by rfl⟩ : syracuseStep 665555 = 998333) B998333
theorem B665571 : Blo 662308 665571 := bstep (se 1 (by rfl) ⟨499178, by rfl⟩ : syracuseStep 665571 = 998357) B998357
theorem B665587 : Blo 662308 665587 := bstep (se 1 (by rfl) ⟨499190, by rfl⟩ : syracuseStep 665587 = 998381) B998381
theorem B665603 : Blo 662308 665603 := bstep (se 1 (by rfl) ⟨499202, by rfl⟩ : syracuseStep 665603 = 998405) B998405
theorem B665619 : Blo 662308 665619 := bstep (se 1 (by rfl) ⟨499214, by rfl⟩ : syracuseStep 665619 = 998429) B998429
theorem B4302883 : Blo 662308 4302883 := bstep (se 1 (by rfl) ⟨3227162, by rfl⟩ : syracuseStep 4302883 = 6454325) B6454325
theorem B665635 : Blo 662308 665635 := bstep (se 1 (by rfl) ⟨499226, by rfl⟩ : syracuseStep 665635 = 998453) B998453
theorem B665651 : Blo 662308 665651 := bstep (se 1 (by rfl) ⟨499238, by rfl⟩ : syracuseStep 665651 = 998477) B998477
theorem B665667 : Blo 662308 665667 := bstep (se 1 (by rfl) ⟨499250, by rfl⟩ : syracuseStep 665667 = 998501) B998501
theorem B665683 : Blo 662308 665683 := bstep (se 1 (by rfl) ⟨499262, by rfl⟩ : syracuseStep 665683 = 998525) B998525
theorem B665699 : Blo 662308 665699 := bstep (se 1 (by rfl) ⟨499274, by rfl⟩ : syracuseStep 665699 = 998549) B998549
theorem B665715 : Blo 662308 665715 := bstep (se 1 (by rfl) ⟨499286, by rfl⟩ : syracuseStep 665715 = 998573) B998573
theorem B665731 : Blo 662308 665731 := bstep (se 1 (by rfl) ⟨499298, by rfl⟩ : syracuseStep 665731 = 998597) B998597
theorem B665747 : Blo 662308 665747 := bstep (se 1 (by rfl) ⟨499310, by rfl⟩ : syracuseStep 665747 = 998621) B998621
theorem B796835 : Blo 662308 796835 := bstep (se 1 (by rfl) ⟨597626, by rfl⟩ : syracuseStep 796835 = 1195253) B1195253
theorem B665763 : Blo 662308 665763 := bstep (se 1 (by rfl) ⟨499322, by rfl⟩ : syracuseStep 665763 = 998645) B998645
theorem B665779 : Blo 662308 665779 := bstep (se 1 (by rfl) ⟨499334, by rfl⟩ : syracuseStep 665779 = 998669) B998669
theorem B993473 : Blo 662308 993473 := bstep (se 2 (by rfl) ⟨372552, by rfl⟩ : syracuseStep 993473 = 745105) B745105
theorem B665795 : Blo 662308 665795 := bstep (se 1 (by rfl) ⟨499346, by rfl⟩ : syracuseStep 665795 = 998693) B998693
theorem B993491 : Blo 662308 993491 := bstep (se 1 (by rfl) ⟨745118, by rfl⟩ : syracuseStep 993491 = 1490237) B1490237
theorem B665811 : Blo 662308 665811 := bstep (se 1 (by rfl) ⟨499358, by rfl⟩ : syracuseStep 665811 = 998717) B998717
theorem B665827 : Blo 662308 665827 := bstep (se 1 (by rfl) ⟨499370, by rfl⟩ : syracuseStep 665827 = 998741) B998741
theorem B993521 : Blo 662308 993521 := bstep (se 2 (by rfl) ⟨372570, by rfl⟩ : syracuseStep 993521 = 745141) B745141
theorem B665843 : Blo 662308 665843 := bstep (se 1 (by rfl) ⟨499382, by rfl⟩ : syracuseStep 665843 = 998765) B998765
theorem B993539 : Blo 662308 993539 := bstep (se 1 (by rfl) ⟨745154, by rfl⟩ : syracuseStep 993539 = 1490309) B1490309
theorem B665859 : Blo 662308 665859 := bstep (se 1 (by rfl) ⟨499394, by rfl⟩ : syracuseStep 665859 = 998789) B998789
theorem B1681681 : Blo 662308 1681681 := bstep (se 2 (by rfl) ⟨630630, by rfl⟩ : syracuseStep 1681681 = 1261261) B1261261
theorem B665875 : Blo 662308 665875 := bstep (se 1 (by rfl) ⟨499406, by rfl⟩ : syracuseStep 665875 = 998813) B998813
theorem B993569 : Blo 662308 993569 := bstep (se 2 (by rfl) ⟨372588, by rfl⟩ : syracuseStep 993569 = 745177) B745177
theorem B665891 : Blo 662308 665891 := bstep (se 1 (by rfl) ⟨499418, by rfl⟩ : syracuseStep 665891 = 998837) B998837
theorem B993587 : Blo 662308 993587 := bstep (se 1 (by rfl) ⟨745190, by rfl⟩ : syracuseStep 993587 = 1490381) B1490381
theorem B665907 : Blo 662308 665907 := bstep (se 1 (by rfl) ⟨499430, by rfl⟩ : syracuseStep 665907 = 998861) B998861
theorem B665923 : Blo 662308 665923 := bstep (se 1 (by rfl) ⟨499442, by rfl⟩ : syracuseStep 665923 = 998885) B998885
theorem B993617 : Blo 662308 993617 := bstep (se 2 (by rfl) ⟨372606, by rfl⟩ : syracuseStep 993617 = 745213) B745213
theorem B665939 : Blo 662308 665939 := bstep (se 1 (by rfl) ⟨499454, by rfl⟩ : syracuseStep 665939 = 998909) B998909
theorem B993635 : Blo 662308 993635 := bstep (se 1 (by rfl) ⟨745226, by rfl⟩ : syracuseStep 993635 = 1490453) B1490453
theorem B3189091 : Blo 662308 3189091 := bstep (se 1 (by rfl) ⟨2391818, by rfl⟩ : syracuseStep 3189091 = 4783637) B4783637
theorem B665955 : Blo 662308 665955 := bstep (se 1 (by rfl) ⟨499466, by rfl⟩ : syracuseStep 665955 = 998933) B998933
theorem B665971 : Blo 662308 665971 := bstep (se 1 (by rfl) ⟨499478, by rfl⟩ : syracuseStep 665971 = 998957) B998957
theorem B993665 : Blo 662308 993665 := bstep (se 2 (by rfl) ⟨372624, by rfl⟩ : syracuseStep 993665 = 745249) B745249
theorem B665987 : Blo 662308 665987 := bstep (se 1 (by rfl) ⟨499490, by rfl⟩ : syracuseStep 665987 = 998981) B998981
theorem B993683 : Blo 662308 993683 := bstep (se 1 (by rfl) ⟨745262, by rfl⟩ : syracuseStep 993683 = 1490525) B1490525
theorem B666003 : Blo 662308 666003 := bstep (se 1 (by rfl) ⟨499502, by rfl⟩ : syracuseStep 666003 = 999005) B999005
theorem B666019 : Blo 662308 666019 := bstep (se 1 (by rfl) ⟨499514, by rfl⟩ : syracuseStep 666019 = 999029) B999029
theorem B2238893 : Blo 662308 2238893 := bstep (se 3 (by rfl) ⟨419792, by rfl⟩ : syracuseStep 2238893 = 839585) B839585
theorem B993713 : Blo 662308 993713 := bstep (se 2 (by rfl) ⟨372642, by rfl⟩ : syracuseStep 993713 = 745285) B745285
theorem B1419697 : Blo 662308 1419697 := bstep (se 2 (by rfl) ⟨532386, by rfl⟩ : syracuseStep 1419697 = 1064773) B1064773
theorem B666035 : Blo 662308 666035 := bstep (se 1 (by rfl) ⟨499526, by rfl⟩ : syracuseStep 666035 = 999053) B999053
theorem B993731 : Blo 662308 993731 := bstep (se 1 (by rfl) ⟨745298, by rfl⟩ : syracuseStep 993731 = 1490597) B1490597
theorem B666051 : Blo 662308 666051 := bstep (se 1 (by rfl) ⟨499538, by rfl⟩ : syracuseStep 666051 = 999077) B999077
theorem B666067 : Blo 662308 666067 := bstep (se 1 (by rfl) ⟨499550, by rfl⟩ : syracuseStep 666067 = 999101) B999101
theorem B993761 : Blo 662308 993761 := bstep (se 2 (by rfl) ⟨372660, by rfl⟩ : syracuseStep 993761 = 745321) B745321
theorem B2238947 : Blo 662308 2238947 := bstep (se 1 (by rfl) ⟨1679210, by rfl⟩ : syracuseStep 2238947 = 3358421) B3358421
theorem B666083 : Blo 662308 666083 := bstep (se 1 (by rfl) ⟨499562, by rfl⟩ : syracuseStep 666083 = 999125) B999125
theorem B993779 : Blo 662308 993779 := bstep (se 1 (by rfl) ⟨745334, by rfl⟩ : syracuseStep 993779 = 1490669) B1490669
theorem B666099 : Blo 662308 666099 := bstep (se 1 (by rfl) ⟨499574, by rfl⟩ : syracuseStep 666099 = 999149) B999149
theorem B666115 : Blo 662308 666115 := bstep (se 1 (by rfl) ⟨499586, by rfl⟩ : syracuseStep 666115 = 999173) B999173
theorem B993809 : Blo 662308 993809 := bstep (se 2 (by rfl) ⟨372678, by rfl⟩ : syracuseStep 993809 = 745357) B745357
theorem B666131 : Blo 662308 666131 := bstep (se 1 (by rfl) ⟨499598, by rfl⟩ : syracuseStep 666131 = 999197) B999197
theorem B993827 : Blo 662308 993827 := bstep (se 1 (by rfl) ⟨745370, by rfl⟩ : syracuseStep 993827 = 1490741) B1490741
theorem B1681955 : Blo 662308 1681955 := bstep (se 1 (by rfl) ⟨1261466, by rfl⟩ : syracuseStep 1681955 = 2522933) B2522933
theorem B666147 : Blo 662308 666147 := bstep (se 1 (by rfl) ⟨499610, by rfl⟩ : syracuseStep 666147 = 999221) B999221
theorem B666163 : Blo 662308 666163 := bstep (se 1 (by rfl) ⟨499622, by rfl⟩ : syracuseStep 666163 = 999245) B999245
theorem B993857 : Blo 662308 993857 := bstep (se 2 (by rfl) ⟨372696, by rfl⟩ : syracuseStep 993857 = 745393) B745393
theorem B666179 : Blo 662308 666179 := bstep (se 1 (by rfl) ⟨499634, by rfl⟩ : syracuseStep 666179 = 999269) B999269
theorem B993875 : Blo 662308 993875 := bstep (se 1 (by rfl) ⟨745406, by rfl⟩ : syracuseStep 993875 = 1490813) B1490813
theorem B666195 : Blo 662308 666195 := bstep (se 1 (by rfl) ⟨499646, by rfl⟩ : syracuseStep 666195 = 999293) B999293
theorem B666211 : Blo 662308 666211 := bstep (se 1 (by rfl) ⟨499658, by rfl⟩ : syracuseStep 666211 = 999317) B999317
theorem B993905 : Blo 662308 993905 := bstep (se 2 (by rfl) ⟨372714, by rfl⟩ : syracuseStep 993905 = 745429) B745429
theorem B666227 : Blo 662308 666227 := bstep (se 1 (by rfl) ⟨499670, by rfl⟩ : syracuseStep 666227 = 999341) B999341
theorem B993923 : Blo 662308 993923 := bstep (se 1 (by rfl) ⟨745442, by rfl⟩ : syracuseStep 993923 = 1490885) B1490885
theorem B666243 : Blo 662308 666243 := bstep (se 1 (by rfl) ⟨499682, by rfl⟩ : syracuseStep 666243 = 999365) B999365
theorem B666259 : Blo 662308 666259 := bstep (se 1 (by rfl) ⟨499694, by rfl⟩ : syracuseStep 666259 = 999389) B999389
theorem B993953 : Blo 662308 993953 := bstep (se 2 (by rfl) ⟨372732, by rfl⟩ : syracuseStep 993953 = 745465) B745465
theorem B666275 : Blo 662308 666275 := bstep (se 1 (by rfl) ⟨499706, by rfl⟩ : syracuseStep 666275 = 999413) B999413
theorem B993971 : Blo 662308 993971 := bstep (se 1 (by rfl) ⟨745478, by rfl⟩ : syracuseStep 993971 = 1490957) B1490957
theorem B666291 : Blo 662308 666291 := bstep (se 1 (by rfl) ⟨499718, by rfl⟩ : syracuseStep 666291 = 999437) B999437
theorem B666307 : Blo 662308 666307 := bstep (se 1 (by rfl) ⟨499730, by rfl⟩ : syracuseStep 666307 = 999461) B999461
theorem B994001 : Blo 662308 994001 := bstep (se 2 (by rfl) ⟨372750, by rfl⟩ : syracuseStep 994001 = 745501) B745501
theorem B994019 : Blo 662308 994019 := bstep (se 1 (by rfl) ⟨745514, by rfl⟩ : syracuseStep 994019 = 1491029) B1491029
theorem B1682147 : Blo 662308 1682147 := bstep (se 1 (by rfl) ⟨1261610, by rfl⟩ : syracuseStep 1682147 = 2523221) B2523221
theorem B2239217 : Blo 662308 2239217 := bstep (se 2 (by rfl) ⟨839706, by rfl⟩ : syracuseStep 2239217 = 1679413) B1679413
theorem B994049 : Blo 662308 994049 := bstep (se 2 (by rfl) ⟨372768, by rfl⟩ : syracuseStep 994049 = 745537) B745537
theorem B994067 : Blo 662308 994067 := bstep (se 1 (by rfl) ⟨745550, by rfl⟩ : syracuseStep 994067 = 1491101) B1491101
theorem B994097 : Blo 662308 994097 := bstep (se 2 (by rfl) ⟨372786, by rfl⟩ : syracuseStep 994097 = 745573) B745573
theorem B994115 : Blo 662308 994115 := bstep (se 1 (by rfl) ⟨745586, by rfl⟩ : syracuseStep 994115 = 1491173) B1491173
theorem B994145 : Blo 662308 994145 := bstep (se 2 (by rfl) ⟨372804, by rfl⟩ : syracuseStep 994145 = 745609) B745609
theorem B994163 : Blo 662308 994163 := bstep (se 1 (by rfl) ⟨745622, by rfl⟩ : syracuseStep 994163 = 1491245) B1491245
theorem B994193 : Blo 662308 994193 := bstep (se 2 (by rfl) ⟨372822, by rfl⟩ : syracuseStep 994193 = 745645) B745645
theorem B994211 : Blo 662308 994211 := bstep (se 1 (by rfl) ⟨745658, by rfl⟩ : syracuseStep 994211 = 1491317) B1491317
theorem B994241 : Blo 662308 994241 := bstep (se 2 (by rfl) ⟨372840, by rfl⟩ : syracuseStep 994241 = 745681) B745681
theorem B994259 : Blo 662308 994259 := bstep (se 1 (by rfl) ⟨745694, by rfl⟩ : syracuseStep 994259 = 1491389) B1491389
theorem B994289 : Blo 662308 994289 := bstep (se 2 (by rfl) ⟨372858, by rfl⟩ : syracuseStep 994289 = 745717) B745717
theorem B994307 : Blo 662308 994307 := bstep (se 1 (by rfl) ⟨745730, by rfl⟩ : syracuseStep 994307 = 1491461) B1491461
theorem B994337 : Blo 662308 994337 := bstep (se 2 (by rfl) ⟨372876, by rfl⟩ : syracuseStep 994337 = 745753) B745753
theorem B994355 : Blo 662308 994355 := bstep (se 1 (by rfl) ⟨745766, by rfl⟩ : syracuseStep 994355 = 1491533) B1491533
theorem B1420355 : Blo 662308 1420355 := bstep (se 1 (by rfl) ⟨1065266, by rfl⟩ : syracuseStep 1420355 = 2130533) B2130533
theorem B994385 : Blo 662308 994385 := bstep (se 2 (by rfl) ⟨372894, by rfl⟩ : syracuseStep 994385 = 745789) B745789
theorem B994403 : Blo 662308 994403 := bstep (se 1 (by rfl) ⟨745802, by rfl⟩ : syracuseStep 994403 = 1491605) B1491605
theorem B994433 : Blo 662308 994433 := bstep (se 2 (by rfl) ⟨372912, by rfl⟩ : syracuseStep 994433 = 745825) B745825
theorem B994451 : Blo 662308 994451 := bstep (se 1 (by rfl) ⟨745838, by rfl⟩ : syracuseStep 994451 = 1491677) B1491677
theorem B994481 : Blo 662308 994481 := bstep (se 2 (by rfl) ⟨372930, by rfl⟩ : syracuseStep 994481 = 745861) B745861
theorem B994499 : Blo 662308 994499 := bstep (se 1 (by rfl) ⟨745874, by rfl⟩ : syracuseStep 994499 = 1491749) B1491749
theorem B6368453 : Blo 662308 6368453 := bstep (se 4 (by rfl) ⟨597042, by rfl⟩ : syracuseStep 6368453 = 1194085) B1194085
theorem B994529 : Blo 662308 994529 := bstep (se 2 (by rfl) ⟨372948, by rfl⟩ : syracuseStep 994529 = 745897) B745897
theorem B994547 : Blo 662308 994547 := bstep (se 1 (by rfl) ⟨745910, by rfl⟩ : syracuseStep 994547 = 1491821) B1491821
theorem B2239757 : Blo 662308 2239757 := bstep (se 3 (by rfl) ⟨419954, by rfl⟩ : syracuseStep 2239757 = 839909) B839909
theorem B994577 : Blo 662308 994577 := bstep (se 2 (by rfl) ⟨372966, by rfl⟩ : syracuseStep 994577 = 745933) B745933
theorem B994595 : Blo 662308 994595 := bstep (se 1 (by rfl) ⟨745946, by rfl⟩ : syracuseStep 994595 = 1491893) B1491893
theorem B994625 : Blo 662308 994625 := bstep (se 2 (by rfl) ⟨372984, by rfl⟩ : syracuseStep 994625 = 745969) B745969
theorem B2239811 : Blo 662308 2239811 := bstep (se 1 (by rfl) ⟨1679858, by rfl⟩ : syracuseStep 2239811 = 3359717) B3359717
theorem B994643 : Blo 662308 994643 := bstep (se 1 (by rfl) ⟨745982, by rfl⟩ : syracuseStep 994643 = 1491965) B1491965
theorem B994673 : Blo 662308 994673 := bstep (se 2 (by rfl) ⟨373002, by rfl⟩ : syracuseStep 994673 = 746005) B746005
theorem B994691 : Blo 662308 994691 := bstep (se 1 (by rfl) ⟨746018, by rfl⟩ : syracuseStep 994691 = 1492037) B1492037
theorem B994721 : Blo 662308 994721 := bstep (se 2 (by rfl) ⟨373020, by rfl⟩ : syracuseStep 994721 = 746041) B746041
theorem B994739 : Blo 662308 994739 := bstep (se 1 (by rfl) ⟨746054, by rfl⟩ : syracuseStep 994739 = 1492109) B1492109
theorem B994769 : Blo 662308 994769 := bstep (se 2 (by rfl) ⟨373038, by rfl⟩ : syracuseStep 994769 = 746077) B746077
theorem B994787 : Blo 662308 994787 := bstep (se 1 (by rfl) ⟨746090, by rfl⟩ : syracuseStep 994787 = 1492181) B1492181
theorem B994817 : Blo 662308 994817 := bstep (se 2 (by rfl) ⟨373056, by rfl⟩ : syracuseStep 994817 = 746113) B746113
theorem B994835 : Blo 662308 994835 := bstep (se 1 (by rfl) ⟨746126, by rfl⟩ : syracuseStep 994835 = 1492253) B1492253
theorem B15543829 : Blo 662308 15543829 := bstep (se 6 (by rfl) ⟨364308, by rfl⟩ : syracuseStep 15543829 = 728617) B728617
theorem B994865 : Blo 662308 994865 := bstep (se 2 (by rfl) ⟨373074, by rfl⟩ : syracuseStep 994865 = 746149) B746149
theorem B994883 : Blo 662308 994883 := bstep (se 1 (by rfl) ⟨746162, by rfl⟩ : syracuseStep 994883 = 1492325) B1492325
theorem B2240081 : Blo 662308 2240081 := bstep (se 2 (by rfl) ⟨840030, by rfl⟩ : syracuseStep 2240081 = 1680061) B1680061
theorem B994913 : Blo 662308 994913 := bstep (se 2 (by rfl) ⟨373092, by rfl⟩ : syracuseStep 994913 = 746185) B746185
theorem B994931 : Blo 662308 994931 := bstep (se 1 (by rfl) ⟨746198, by rfl⟩ : syracuseStep 994931 = 1492397) B1492397
theorem B3780229 : Blo 662308 3780229 := bstep (se 4 (by rfl) ⟨354396, by rfl⟩ : syracuseStep 3780229 = 708793) B708793
theorem B994961 : Blo 662308 994961 := bstep (se 2 (by rfl) ⟨373110, by rfl⟩ : syracuseStep 994961 = 746221) B746221
theorem B1683089 : Blo 662308 1683089 := bstep (se 2 (by rfl) ⟨631158, by rfl⟩ : syracuseStep 1683089 = 1262317) B1262317
theorem B994979 : Blo 662308 994979 := bstep (se 1 (by rfl) ⟨746234, by rfl⟩ : syracuseStep 994979 = 1492469) B1492469
theorem B995009 : Blo 662308 995009 := bstep (se 2 (by rfl) ⟨373128, by rfl⟩ : syracuseStep 995009 = 746257) B746257
theorem B1683139 : Blo 662308 1683139 := bstep (se 1 (by rfl) ⟨1262354, by rfl⟩ : syracuseStep 1683139 = 2524709) B2524709
theorem B995027 : Blo 662308 995027 := bstep (se 1 (by rfl) ⟨746270, by rfl⟩ : syracuseStep 995027 = 1492541) B1492541
theorem B995057 : Blo 662308 995057 := bstep (se 2 (by rfl) ⟨373146, by rfl⟩ : syracuseStep 995057 = 746293) B746293
theorem B995075 : Blo 662308 995075 := bstep (se 1 (by rfl) ⟨746306, by rfl⟩ : syracuseStep 995075 = 1492613) B1492613
theorem B2699021 : Blo 662308 2699021 := bstep (se 3 (by rfl) ⟨506066, by rfl⟩ : syracuseStep 2699021 = 1012133) B1012133
theorem B995105 : Blo 662308 995105 := bstep (se 2 (by rfl) ⟨373164, by rfl⟩ : syracuseStep 995105 = 746329) B746329
theorem B2830115 : Blo 662308 2830115 := bstep (se 1 (by rfl) ⟨2122586, by rfl⟩ : syracuseStep 2830115 = 4245173) B4245173
theorem B995123 : Blo 662308 995123 := bstep (se 1 (by rfl) ⟨746342, by rfl⟩ : syracuseStep 995123 = 1492685) B1492685
theorem B995153 : Blo 662308 995153 := bstep (se 2 (by rfl) ⟨373182, by rfl⟩ : syracuseStep 995153 = 746365) B746365
theorem B1683281 : Blo 662308 1683281 := bstep (se 2 (by rfl) ⟨631230, by rfl⟩ : syracuseStep 1683281 = 1262461) B1262461
theorem B995171 : Blo 662308 995171 := bstep (se 1 (by rfl) ⟨746378, by rfl⟩ : syracuseStep 995171 = 1492757) B1492757
theorem B995201 : Blo 662308 995201 := bstep (se 2 (by rfl) ⟨373200, by rfl⟩ : syracuseStep 995201 = 746401) B746401
theorem B1421201 : Blo 662308 1421201 := bstep (se 2 (by rfl) ⟨532950, by rfl⟩ : syracuseStep 1421201 = 1065901) B1065901
theorem B995219 : Blo 662308 995219 := bstep (se 1 (by rfl) ⟨746414, by rfl⟩ : syracuseStep 995219 = 1492829) B1492829
theorem B995249 : Blo 662308 995249 := bstep (se 2 (by rfl) ⟨373218, by rfl⟩ : syracuseStep 995249 = 746437) B746437
theorem B995267 : Blo 662308 995267 := bstep (se 1 (by rfl) ⟨746450, by rfl⟩ : syracuseStep 995267 = 1492901) B1492901
theorem B995297 : Blo 662308 995297 := bstep (se 2 (by rfl) ⟨373236, by rfl⟩ : syracuseStep 995297 = 746473) B746473
theorem B1257457 : Blo 662308 1257457 := bstep (se 2 (by rfl) ⟨471546, by rfl⟩ : syracuseStep 1257457 = 943093) B943093
theorem B995315 : Blo 662308 995315 := bstep (se 1 (by rfl) ⟨746486, by rfl⟩ : syracuseStep 995315 = 1492973) B1492973
theorem B995345 : Blo 662308 995345 := bstep (se 2 (by rfl) ⟨373254, by rfl⟩ : syracuseStep 995345 = 746509) B746509
theorem B995363 : Blo 662308 995363 := bstep (se 1 (by rfl) ⟨746522, by rfl⟩ : syracuseStep 995363 = 1493045) B1493045
theorem B995393 : Blo 662308 995393 := bstep (se 2 (by rfl) ⟨373272, by rfl⟩ : syracuseStep 995393 = 746545) B746545
theorem B995411 : Blo 662308 995411 := bstep (se 1 (by rfl) ⟨746558, by rfl⟩ : syracuseStep 995411 = 1493117) B1493117
theorem B1618019 : Blo 662308 1618019 := bstep (se 1 (by rfl) ⟨1213514, by rfl⟩ : syracuseStep 1618019 = 2427029) B2427029
theorem B2240621 : Blo 662308 2240621 := bstep (se 3 (by rfl) ⟨420116, by rfl⟩ : syracuseStep 2240621 = 840233) B840233
theorem B995441 : Blo 662308 995441 := bstep (se 2 (by rfl) ⟨373290, by rfl⟩ : syracuseStep 995441 = 746581) B746581
theorem B995459 : Blo 662308 995459 := bstep (se 1 (by rfl) ⟨746594, by rfl⟩ : syracuseStep 995459 = 1493189) B1493189
theorem B766099 : Blo 662308 766099 := bstep (se 1 (by rfl) ⟨574574, by rfl⟩ : syracuseStep 766099 = 1149149) B1149149
theorem B995489 : Blo 662308 995489 := bstep (se 2 (by rfl) ⟨373308, by rfl⟩ : syracuseStep 995489 = 746617) B746617
theorem B2240675 : Blo 662308 2240675 := bstep (se 1 (by rfl) ⟨1680506, by rfl⟩ : syracuseStep 2240675 = 3361013) B3361013
theorem B995507 : Blo 662308 995507 := bstep (se 1 (by rfl) ⟨746630, by rfl⟩ : syracuseStep 995507 = 1493261) B1493261
theorem B995537 : Blo 662308 995537 := bstep (se 2 (by rfl) ⟨373326, by rfl⟩ : syracuseStep 995537 = 746653) B746653
theorem B995555 : Blo 662308 995555 := bstep (se 1 (by rfl) ⟨746666, by rfl⟩ : syracuseStep 995555 = 1493333) B1493333
theorem B897251 : Blo 662308 897251 := bstep (se 1 (by rfl) ⟨672938, by rfl⟩ : syracuseStep 897251 = 1345877) B1345877
theorem B995585 : Blo 662308 995585 := bstep (se 2 (by rfl) ⟨373344, by rfl⟩ : syracuseStep 995585 = 746689) B746689
theorem B798979 : Blo 662308 798979 := bstep (se 1 (by rfl) ⟨599234, by rfl⟩ : syracuseStep 798979 = 1198469) B1198469
theorem B995603 : Blo 662308 995603 := bstep (se 1 (by rfl) ⟨746702, by rfl⟩ : syracuseStep 995603 = 1493405) B1493405
theorem B995633 : Blo 662308 995633 := bstep (se 2 (by rfl) ⟨373362, by rfl⟩ : syracuseStep 995633 = 746725) B746725
theorem B995651 : Blo 662308 995651 := bstep (se 1 (by rfl) ⟨746738, by rfl⟩ : syracuseStep 995651 = 1493477) B1493477
theorem B995681 : Blo 662308 995681 := bstep (se 2 (by rfl) ⟨373380, by rfl⟩ : syracuseStep 995681 = 746761) B746761
theorem B995699 : Blo 662308 995699 := bstep (se 1 (by rfl) ⟨746774, by rfl⟩ : syracuseStep 995699 = 1493549) B1493549
theorem B1257859 : Blo 662308 1257859 := bstep (se 1 (by rfl) ⟨943394, by rfl⟩ : syracuseStep 1257859 = 1886789) B1886789
theorem B14332301 : Blo 662308 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B995729 : Blo 662308 995729 := bstep (se 2 (by rfl) ⟨373398, by rfl⟩ : syracuseStep 995729 = 746797) B746797
theorem B995747 : Blo 662308 995747 := bstep (se 1 (by rfl) ⟨746810, by rfl⟩ : syracuseStep 995747 = 1493621) B1493621
theorem B1257905 : Blo 662308 1257905 := bstep (se 2 (by rfl) ⟨471714, by rfl⟩ : syracuseStep 1257905 = 943429) B943429
theorem B2240945 : Blo 662308 2240945 := bstep (se 2 (by rfl) ⟨840354, by rfl⟩ : syracuseStep 2240945 = 1680709) B1680709
theorem B995777 : Blo 662308 995777 := bstep (se 2 (by rfl) ⟨373416, by rfl⟩ : syracuseStep 995777 = 746833) B746833
theorem B995795 : Blo 662308 995795 := bstep (se 1 (by rfl) ⟨746846, by rfl⟩ : syracuseStep 995795 = 1493693) B1493693
theorem B1061345 : Blo 662308 1061345 := bstep (se 2 (by rfl) ⟨398004, by rfl⟩ : syracuseStep 1061345 = 796009) B796009
theorem B995825 : Blo 662308 995825 := bstep (se 2 (by rfl) ⟨373434, by rfl⟩ : syracuseStep 995825 = 746869) B746869
theorem B995843 : Blo 662308 995843 := bstep (se 1 (by rfl) ⟨746882, by rfl⟩ : syracuseStep 995843 = 1493765) B1493765
theorem B995873 : Blo 662308 995873 := bstep (se 2 (by rfl) ⟨373452, by rfl⟩ : syracuseStep 995873 = 746905) B746905
theorem B995891 : Blo 662308 995891 := bstep (se 1 (by rfl) ⟨746918, by rfl⟩ : syracuseStep 995891 = 1493837) B1493837
theorem B995921 : Blo 662308 995921 := bstep (se 2 (by rfl) ⟨373470, by rfl⟩ : syracuseStep 995921 = 746941) B746941
theorem B995939 : Blo 662308 995939 := bstep (se 1 (by rfl) ⟨746954, by rfl⟩ : syracuseStep 995939 = 1493909) B1493909
theorem B995969 : Blo 662308 995969 := bstep (se 2 (by rfl) ⟨373488, by rfl⟩ : syracuseStep 995969 = 746977) B746977
theorem B2044561 : Blo 662308 2044561 := bstep (se 2 (by rfl) ⟨766710, by rfl⟩ : syracuseStep 2044561 = 1533421) B1533421
theorem B995987 : Blo 662308 995987 := bstep (se 1 (by rfl) ⟨746990, by rfl⟩ : syracuseStep 995987 = 1493981) B1493981
theorem B996017 : Blo 662308 996017 := bstep (se 2 (by rfl) ⟨373506, by rfl⟩ : syracuseStep 996017 = 747013) B747013
theorem B996035 : Blo 662308 996035 := bstep (se 1 (by rfl) ⟨747026, by rfl⟩ : syracuseStep 996035 = 1494053) B1494053
theorem B1258193 : Blo 662308 1258193 := bstep (se 2 (by rfl) ⟨471822, by rfl⟩ : syracuseStep 1258193 = 943645) B943645
theorem B996065 : Blo 662308 996065 := bstep (se 2 (by rfl) ⟨373524, by rfl⟩ : syracuseStep 996065 = 747049) B747049
theorem B996083 : Blo 662308 996083 := bstep (se 1 (by rfl) ⟨747062, by rfl⟩ : syracuseStep 996083 = 1494125) B1494125
theorem B996113 : Blo 662308 996113 := bstep (se 2 (by rfl) ⟨373542, by rfl⟩ : syracuseStep 996113 = 747085) B747085
theorem B799507 : Blo 662308 799507 := bstep (se 1 (by rfl) ⟨599630, by rfl⟩ : syracuseStep 799507 = 1199261) B1199261
theorem B996131 : Blo 662308 996131 := bstep (se 1 (by rfl) ⟨747098, by rfl⟩ : syracuseStep 996131 = 1494197) B1494197
theorem B897841 : Blo 662308 897841 := bstep (se 2 (by rfl) ⟨336690, by rfl⟩ : syracuseStep 897841 = 673381) B673381
theorem B1684273 : Blo 662308 1684273 := bstep (se 2 (by rfl) ⟨631602, by rfl⟩ : syracuseStep 1684273 = 1263205) B1263205
theorem B996161 : Blo 662308 996161 := bstep (se 2 (by rfl) ⟨373560, by rfl⟩ : syracuseStep 996161 = 747121) B747121
theorem B996179 : Blo 662308 996179 := bstep (se 1 (by rfl) ⟨747134, by rfl⟩ : syracuseStep 996179 = 1494269) B1494269
theorem B3355505 : Blo 662308 3355505 := bstep (se 2 (by rfl) ⟨1258314, by rfl⟩ : syracuseStep 3355505 = 2516629) B2516629
theorem B996209 : Blo 662308 996209 := bstep (se 2 (by rfl) ⟨373578, by rfl⟩ : syracuseStep 996209 = 747157) B747157
theorem B996227 : Blo 662308 996227 := bstep (se 1 (by rfl) ⟨747170, by rfl⟩ : syracuseStep 996227 = 1494341) B1494341
theorem B996257 : Blo 662308 996257 := bstep (se 2 (by rfl) ⟨373596, by rfl⟩ : syracuseStep 996257 = 747193) B747193
theorem B996275 : Blo 662308 996275 := bstep (se 1 (by rfl) ⟨747206, by rfl⟩ : syracuseStep 996275 = 1494413) B1494413
theorem B2241485 : Blo 662308 2241485 := bstep (se 3 (by rfl) ⟨420278, by rfl⟩ : syracuseStep 2241485 = 840557) B840557
theorem B996305 : Blo 662308 996305 := bstep (se 2 (by rfl) ⟨373614, by rfl⟩ : syracuseStep 996305 = 747229) B747229
theorem B1061857 : Blo 662308 1061857 := bstep (se 2 (by rfl) ⟨398196, by rfl⟩ : syracuseStep 1061857 = 796393) B796393
theorem B1913827 : Blo 662308 1913827 := bstep (se 1 (by rfl) ⟨1435370, by rfl⟩ : syracuseStep 1913827 = 2870741) B2870741
theorem B16135139 : Blo 662308 16135139 := bstep (se 1 (by rfl) ⟨12101354, by rfl⟩ : syracuseStep 16135139 = 24202709) B24202709
theorem B996323 : Blo 662308 996323 := bstep (se 1 (by rfl) ⟨747242, by rfl⟩ : syracuseStep 996323 = 1494485) B1494485
theorem B2831345 : Blo 662308 2831345 := bstep (se 2 (by rfl) ⟨1061754, by rfl⟩ : syracuseStep 2831345 = 2123509) B2123509
theorem B996353 : Blo 662308 996353 := bstep (se 2 (by rfl) ⟨373632, by rfl⟩ : syracuseStep 996353 = 747265) B747265
theorem B2241539 : Blo 662308 2241539 := bstep (se 1 (by rfl) ⟨1681154, by rfl⟩ : syracuseStep 2241539 = 3362309) B3362309
theorem B996371 : Blo 662308 996371 := bstep (se 1 (by rfl) ⟨747278, by rfl⟩ : syracuseStep 996371 = 1494557) B1494557
theorem B996401 : Blo 662308 996401 := bstep (se 2 (by rfl) ⟨373650, by rfl⟩ : syracuseStep 996401 = 747301) B747301
theorem B996419 : Blo 662308 996419 := bstep (se 1 (by rfl) ⟨747314, by rfl⟩ : syracuseStep 996419 = 1494629) B1494629
theorem B1684547 : Blo 662308 1684547 := bstep (se 1 (by rfl) ⟨1263410, by rfl⟩ : syracuseStep 1684547 = 2526821) B2526821
theorem B996449 : Blo 662308 996449 := bstep (se 2 (by rfl) ⟨373668, by rfl⟩ : syracuseStep 996449 = 747337) B747337
theorem B996467 : Blo 662308 996467 := bstep (se 1 (by rfl) ⟨747350, by rfl⟩ : syracuseStep 996467 = 1494701) B1494701
theorem B996497 : Blo 662308 996497 := bstep (se 2 (by rfl) ⟨373686, by rfl⟩ : syracuseStep 996497 = 747373) B747373
theorem B996515 : Blo 662308 996515 := bstep (se 1 (by rfl) ⟨747386, by rfl⟩ : syracuseStep 996515 = 1494773) B1494773
theorem B996545 : Blo 662308 996545 := bstep (se 2 (by rfl) ⟨373704, by rfl⟩ : syracuseStep 996545 = 747409) B747409
theorem B996563 : Blo 662308 996563 := bstep (se 1 (by rfl) ⟨747422, by rfl⟩ : syracuseStep 996563 = 1494845) B1494845
theorem B996593 : Blo 662308 996593 := bstep (se 2 (by rfl) ⟨373722, by rfl⟩ : syracuseStep 996593 = 747445) B747445
theorem B996611 : Blo 662308 996611 := bstep (se 1 (by rfl) ⟨747458, by rfl⟩ : syracuseStep 996611 = 1494917) B1494917
theorem B1684739 : Blo 662308 1684739 := bstep (se 1 (by rfl) ⟨1263554, by rfl⟩ : syracuseStep 1684739 = 2527109) B2527109
theorem B2241809 : Blo 662308 2241809 := bstep (se 2 (by rfl) ⟨840678, by rfl⟩ : syracuseStep 2241809 = 1681357) B1681357
theorem B996641 : Blo 662308 996641 := bstep (se 2 (by rfl) ⟨373740, by rfl⟩ : syracuseStep 996641 = 747481) B747481
theorem B996659 : Blo 662308 996659 := bstep (se 1 (by rfl) ⟨747494, by rfl⟩ : syracuseStep 996659 = 1494989) B1494989
theorem B996689 : Blo 662308 996689 := bstep (se 2 (by rfl) ⟨373758, by rfl⟩ : syracuseStep 996689 = 747517) B747517
theorem B996707 : Blo 662308 996707 := bstep (se 1 (by rfl) ⟨747530, by rfl⟩ : syracuseStep 996707 = 1495061) B1495061
theorem B996737 : Blo 662308 996737 := bstep (se 2 (by rfl) ⟨373776, by rfl⟩ : syracuseStep 996737 = 747553) B747553
theorem B996755 : Blo 662308 996755 := bstep (se 1 (by rfl) ⟨747566, by rfl⟩ : syracuseStep 996755 = 1495133) B1495133
theorem B1258915 : Blo 662308 1258915 := bstep (se 1 (by rfl) ⟨944186, by rfl⟩ : syracuseStep 1258915 = 1888373) B1888373
theorem B996785 : Blo 662308 996785 := bstep (se 2 (by rfl) ⟨373794, by rfl⟩ : syracuseStep 996785 = 747589) B747589
theorem B996803 : Blo 662308 996803 := bstep (se 1 (by rfl) ⟨747602, by rfl⟩ : syracuseStep 996803 = 1495205) B1495205
theorem B996833 : Blo 662308 996833 := bstep (se 2 (by rfl) ⟨373812, by rfl⟩ : syracuseStep 996833 = 747625) B747625
theorem B996851 : Blo 662308 996851 := bstep (se 1 (by rfl) ⟨747638, by rfl⟩ : syracuseStep 996851 = 1495277) B1495277
theorem B996881 : Blo 662308 996881 := bstep (se 2 (by rfl) ⟨373830, by rfl⟩ : syracuseStep 996881 = 747661) B747661
theorem B996899 : Blo 662308 996899 := bstep (se 1 (by rfl) ⟨747674, by rfl⟩ : syracuseStep 996899 = 1495349) B1495349
theorem B1422883 : Blo 662308 1422883 := bstep (se 1 (by rfl) ⟨1067162, by rfl⟩ : syracuseStep 1422883 = 2134325) B2134325
theorem B996929 : Blo 662308 996929 := bstep (se 2 (by rfl) ⟨373848, by rfl⟩ : syracuseStep 996929 = 747697) B747697
theorem B1062467 : Blo 662308 1062467 := bstep (se 1 (by rfl) ⟨796850, by rfl⟩ : syracuseStep 1062467 = 1593701) B1593701
theorem B3782213 : Blo 662308 3782213 := bstep (se 4 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 3782213 = 709165) B709165
theorem B996947 : Blo 662308 996947 := bstep (se 1 (by rfl) ⟨747710, by rfl⟩ : syracuseStep 996947 = 1495421) B1495421
theorem B996977 : Blo 662308 996977 := bstep (se 2 (by rfl) ⟨373866, by rfl⟩ : syracuseStep 996977 = 747733) B747733
theorem B996995 : Blo 662308 996995 := bstep (se 1 (by rfl) ⟨747746, by rfl⟩ : syracuseStep 996995 = 1495493) B1495493
theorem B997025 : Blo 662308 997025 := bstep (se 2 (by rfl) ⟨373884, by rfl⟩ : syracuseStep 997025 = 747769) B747769
theorem B997043 : Blo 662308 997043 := bstep (se 1 (by rfl) ⟨747782, by rfl⟩ : syracuseStep 997043 = 1495565) B1495565
theorem B997073 : Blo 662308 997073 := bstep (se 2 (by rfl) ⟨373902, by rfl⟩ : syracuseStep 997073 = 747805) B747805
theorem B997091 : Blo 662308 997091 := bstep (se 1 (by rfl) ⟨747818, by rfl⟩ : syracuseStep 997091 = 1495637) B1495637
theorem B997121 : Blo 662308 997121 := bstep (se 2 (by rfl) ⟨373920, by rfl⟩ : syracuseStep 997121 = 747841) B747841
theorem B997139 : Blo 662308 997139 := bstep (se 1 (by rfl) ⟨747854, by rfl⟩ : syracuseStep 997139 = 1495709) B1495709
theorem B2242349 : Blo 662308 2242349 := bstep (se 3 (by rfl) ⟨420440, by rfl⟩ : syracuseStep 2242349 = 840881) B840881
theorem B997169 : Blo 662308 997169 := bstep (se 2 (by rfl) ⟨373938, by rfl⟩ : syracuseStep 997169 = 747877) B747877
theorem B997187 : Blo 662308 997187 := bstep (se 1 (by rfl) ⟨747890, by rfl⟩ : syracuseStep 997187 = 1495781) B1495781
theorem B997217 : Blo 662308 997217 := bstep (se 2 (by rfl) ⟨373956, by rfl⟩ : syracuseStep 997217 = 747913) B747913
theorem B1259363 : Blo 662308 1259363 := bstep (se 1 (by rfl) ⟨944522, by rfl⟩ : syracuseStep 1259363 = 1889045) B1889045
theorem B2242403 : Blo 662308 2242403 := bstep (se 1 (by rfl) ⟨1681802, by rfl⟩ : syracuseStep 2242403 = 3363605) B3363605
theorem B997235 : Blo 662308 997235 := bstep (se 1 (by rfl) ⟨747926, by rfl⟩ : syracuseStep 997235 = 1495853) B1495853
theorem B997265 : Blo 662308 997265 := bstep (se 2 (by rfl) ⟨373974, by rfl⟩ : syracuseStep 997265 = 747949) B747949
theorem B997283 : Blo 662308 997283 := bstep (se 1 (by rfl) ⟨747962, by rfl⟩ : syracuseStep 997283 = 1495925) B1495925
theorem B997313 : Blo 662308 997313 := bstep (se 2 (by rfl) ⟨373992, by rfl⟩ : syracuseStep 997313 = 747985) B747985
theorem B997331 : Blo 662308 997331 := bstep (se 1 (by rfl) ⟨747998, by rfl⟩ : syracuseStep 997331 = 1495997) B1495997
theorem B997361 : Blo 662308 997361 := bstep (se 2 (by rfl) ⟨374010, by rfl⟩ : syracuseStep 997361 = 748021) B748021
theorem B997379 : Blo 662308 997379 := bstep (se 1 (by rfl) ⟨748034, by rfl⟩ : syracuseStep 997379 = 1496069) B1496069
theorem B997409 : Blo 662308 997409 := bstep (se 2 (by rfl) ⟨374028, by rfl⟩ : syracuseStep 997409 = 748057) B748057
theorem B997427 : Blo 662308 997427 := bstep (se 1 (by rfl) ⟨748070, by rfl⟩ : syracuseStep 997427 = 1496141) B1496141
theorem B997457 : Blo 662308 997457 := bstep (se 2 (by rfl) ⟨374046, by rfl⟩ : syracuseStep 997457 = 748093) B748093
theorem B997475 : Blo 662308 997475 := bstep (se 1 (by rfl) ⟨748106, by rfl⟩ : syracuseStep 997475 = 1496213) B1496213
theorem B2242673 : Blo 662308 2242673 := bstep (se 2 (by rfl) ⟨841002, by rfl⟩ : syracuseStep 2242673 = 1682005) B1682005
theorem B768115 : Blo 662308 768115 := bstep (se 1 (by rfl) ⟨576086, by rfl⟩ : syracuseStep 768115 = 1152173) B1152173
theorem B997505 : Blo 662308 997505 := bstep (se 2 (by rfl) ⟨374064, by rfl⟩ : syracuseStep 997505 = 748129) B748129
theorem B1259651 : Blo 662308 1259651 := bstep (se 1 (by rfl) ⟨944738, by rfl⟩ : syracuseStep 1259651 = 1889477) B1889477
theorem B997523 : Blo 662308 997523 := bstep (se 1 (by rfl) ⟨748142, by rfl⟩ : syracuseStep 997523 = 1496285) B1496285
theorem B997553 : Blo 662308 997553 := bstep (se 2 (by rfl) ⟨374082, by rfl⟩ : syracuseStep 997553 = 748165) B748165
theorem B1685681 : Blo 662308 1685681 := bstep (se 2 (by rfl) ⟨632130, by rfl⟩ : syracuseStep 1685681 = 1264261) B1264261
theorem B997571 : Blo 662308 997571 := bstep (se 1 (by rfl) ⟨748178, by rfl⟩ : syracuseStep 997571 = 1496357) B1496357
theorem B997601 : Blo 662308 997601 := bstep (se 2 (by rfl) ⟨374100, by rfl⟩ : syracuseStep 997601 = 748201) B748201
theorem B1685731 : Blo 662308 1685731 := bstep (se 1 (by rfl) ⟨1264298, by rfl⟩ : syracuseStep 1685731 = 2528597) B2528597
theorem B997619 : Blo 662308 997619 := bstep (se 1 (by rfl) ⟨748214, by rfl⟩ : syracuseStep 997619 = 1496429) B1496429
theorem B997649 : Blo 662308 997649 := bstep (se 2 (by rfl) ⟨374118, by rfl⟩ : syracuseStep 997649 = 748237) B748237
theorem B3356963 : Blo 662308 3356963 := bstep (se 1 (by rfl) ⟨2517722, by rfl⟩ : syracuseStep 3356963 = 5035445) B5035445
theorem B997667 : Blo 662308 997667 := bstep (se 1 (by rfl) ⟨748250, by rfl⟩ : syracuseStep 997667 = 1496501) B1496501
theorem B997697 : Blo 662308 997697 := bstep (se 2 (by rfl) ⟨374136, by rfl⟩ : syracuseStep 997697 = 748273) B748273
theorem B997715 : Blo 662308 997715 := bstep (se 1 (by rfl) ⟨748286, by rfl⟩ : syracuseStep 997715 = 1496573) B1496573
theorem B1194353 : Blo 662308 1194353 := bstep (se 2 (by rfl) ⟨447882, by rfl⟩ : syracuseStep 1194353 = 895765) B895765
theorem B997745 : Blo 662308 997745 := bstep (se 2 (by rfl) ⟨374154, by rfl⟩ : syracuseStep 997745 = 748309) B748309
theorem B1685873 : Blo 662308 1685873 := bstep (se 2 (by rfl) ⟨632202, by rfl⟩ : syracuseStep 1685873 = 1264405) B1264405
theorem B997763 : Blo 662308 997763 := bstep (se 1 (by rfl) ⟨748322, by rfl⟩ : syracuseStep 997763 = 1496645) B1496645
theorem B997793 : Blo 662308 997793 := bstep (se 2 (by rfl) ⟨374172, by rfl⟩ : syracuseStep 997793 = 748345) B748345
theorem B997811 : Blo 662308 997811 := bstep (se 1 (by rfl) ⟨748358, by rfl⟩ : syracuseStep 997811 = 1496717) B1496717
theorem B997841 : Blo 662308 997841 := bstep (se 2 (by rfl) ⟨374190, by rfl⟩ : syracuseStep 997841 = 748381) B748381
theorem B997859 : Blo 662308 997859 := bstep (se 1 (by rfl) ⟨748394, by rfl⟩ : syracuseStep 997859 = 1496789) B1496789
theorem B997889 : Blo 662308 997889 := bstep (se 2 (by rfl) ⟨374208, by rfl⟩ : syracuseStep 997889 = 748417) B748417
theorem B997907 : Blo 662308 997907 := bstep (se 1 (by rfl) ⟨748430, by rfl⟩ : syracuseStep 997907 = 1496861) B1496861
theorem B1063459 : Blo 662308 1063459 := bstep (se 1 (by rfl) ⟨797594, by rfl⟩ : syracuseStep 1063459 = 1595189) B1595189
theorem B997937 : Blo 662308 997937 := bstep (se 2 (by rfl) ⟨374226, by rfl⟩ : syracuseStep 997937 = 748453) B748453
theorem B18233909 : Blo 662308 18233909 := bstep (se 5 (by rfl) ⟨854714, by rfl⟩ : syracuseStep 18233909 = 1709429) B1709429
theorem B997955 : Blo 662308 997955 := bstep (se 1 (by rfl) ⟨748466, by rfl⟩ : syracuseStep 997955 = 1496933) B1496933
theorem B997985 : Blo 662308 997985 := bstep (se 2 (by rfl) ⟨374244, by rfl⟩ : syracuseStep 997985 = 748489) B748489
theorem B998003 : Blo 662308 998003 := bstep (se 1 (by rfl) ⟨748502, by rfl⟩ : syracuseStep 998003 = 1497005) B1497005
theorem B2243213 : Blo 662308 2243213 := bstep (se 3 (by rfl) ⟨420602, by rfl⟩ : syracuseStep 2243213 = 841205) B841205
theorem B998033 : Blo 662308 998033 := bstep (se 2 (by rfl) ⟨374262, by rfl⟩ : syracuseStep 998033 = 748525) B748525
theorem B998051 : Blo 662308 998051 := bstep (se 1 (by rfl) ⟨748538, by rfl⟩ : syracuseStep 998051 = 1497077) B1497077
theorem B998081 : Blo 662308 998081 := bstep (se 2 (by rfl) ⟨374280, by rfl⟩ : syracuseStep 998081 = 748561) B748561
theorem B2243267 : Blo 662308 2243267 := bstep (se 1 (by rfl) ⟨1682450, by rfl⟩ : syracuseStep 2243267 = 3364901) B3364901
theorem B998099 : Blo 662308 998099 := bstep (se 1 (by rfl) ⟨748574, by rfl⟩ : syracuseStep 998099 = 1497149) B1497149
theorem B998129 : Blo 662308 998129 := bstep (se 2 (by rfl) ⟨374298, by rfl⟩ : syracuseStep 998129 = 748597) B748597
theorem B998147 : Blo 662308 998147 := bstep (se 1 (by rfl) ⟨748610, by rfl⟩ : syracuseStep 998147 = 1497221) B1497221
theorem B899857 : Blo 662308 899857 := bstep (se 2 (by rfl) ⟨337446, by rfl⟩ : syracuseStep 899857 = 674893) B674893
theorem B998177 : Blo 662308 998177 := bstep (se 2 (by rfl) ⟨374316, by rfl⟩ : syracuseStep 998177 = 748633) B748633
theorem B998195 : Blo 662308 998195 := bstep (se 1 (by rfl) ⟨748646, by rfl⟩ : syracuseStep 998195 = 1497293) B1497293
theorem B998225 : Blo 662308 998225 := bstep (se 2 (by rfl) ⟨374334, by rfl⟩ : syracuseStep 998225 = 748669) B748669
theorem B899921 : Blo 662308 899921 := bstep (se 2 (by rfl) ⟨337470, by rfl⟩ : syracuseStep 899921 = 674941) B674941
theorem B998243 : Blo 662308 998243 := bstep (se 1 (by rfl) ⟨748682, by rfl⟩ : syracuseStep 998243 = 1497365) B1497365
theorem B998273 : Blo 662308 998273 := bstep (se 2 (by rfl) ⟨374352, by rfl⟩ : syracuseStep 998273 = 748705) B748705
theorem B998291 : Blo 662308 998291 := bstep (se 1 (by rfl) ⟨748718, by rfl⟩ : syracuseStep 998291 = 1497437) B1497437
theorem B998321 : Blo 662308 998321 := bstep (se 2 (by rfl) ⟨374370, by rfl⟩ : syracuseStep 998321 = 748741) B748741
theorem B900019 : Blo 662308 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B998339 : Blo 662308 998339 := bstep (se 1 (by rfl) ⟨748754, by rfl⟩ : syracuseStep 998339 = 1497509) B1497509
theorem B2243537 : Blo 662308 2243537 := bstep (se 2 (by rfl) ⟨841326, by rfl⟩ : syracuseStep 2243537 = 1682653) B1682653
theorem B998369 : Blo 662308 998369 := bstep (se 2 (by rfl) ⟨374388, by rfl⟩ : syracuseStep 998369 = 748777) B748777
theorem B998387 : Blo 662308 998387 := bstep (se 1 (by rfl) ⟨748790, by rfl⟩ : syracuseStep 998387 = 1497581) B1497581
theorem B998417 : Blo 662308 998417 := bstep (se 2 (by rfl) ⟨374406, by rfl⟩ : syracuseStep 998417 = 748813) B748813
theorem B998435 : Blo 662308 998435 := bstep (se 1 (by rfl) ⟨748826, by rfl⟩ : syracuseStep 998435 = 1497653) B1497653
theorem B1260593 : Blo 662308 1260593 := bstep (se 2 (by rfl) ⟨472722, by rfl⟩ : syracuseStep 1260593 = 945445) B945445
theorem B998465 : Blo 662308 998465 := bstep (se 2 (by rfl) ⟨374424, by rfl⟩ : syracuseStep 998465 = 748849) B748849
theorem B3357773 : Blo 662308 3357773 := bstep (se 3 (by rfl) ⟨629582, by rfl⟩ : syracuseStep 3357773 = 1259165) B1259165
theorem B998483 : Blo 662308 998483 := bstep (se 1 (by rfl) ⟨748862, by rfl⟩ : syracuseStep 998483 = 1497725) B1497725
theorem B998513 : Blo 662308 998513 := bstep (se 2 (by rfl) ⟨374442, by rfl⟩ : syracuseStep 998513 = 748885) B748885
theorem B998531 : Blo 662308 998531 := bstep (se 1 (by rfl) ⟨748898, by rfl⟩ : syracuseStep 998531 = 1497797) B1497797
theorem B998561 : Blo 662308 998561 := bstep (se 2 (by rfl) ⟨374460, by rfl⟩ : syracuseStep 998561 = 748921) B748921
theorem B998579 : Blo 662308 998579 := bstep (se 1 (by rfl) ⟨748934, by rfl⟩ : syracuseStep 998579 = 1497869) B1497869
theorem B998609 : Blo 662308 998609 := bstep (se 2 (by rfl) ⟨374478, by rfl⟩ : syracuseStep 998609 = 748957) B748957
theorem B998627 : Blo 662308 998627 := bstep (se 1 (by rfl) ⟨748970, by rfl⟩ : syracuseStep 998627 = 1497941) B1497941
theorem B998657 : Blo 662308 998657 := bstep (se 2 (by rfl) ⟨374496, by rfl⟩ : syracuseStep 998657 = 748993) B748993
theorem B998675 : Blo 662308 998675 := bstep (se 1 (by rfl) ⟨749006, by rfl⟩ : syracuseStep 998675 = 1498013) B1498013
theorem B998705 : Blo 662308 998705 := bstep (se 2 (by rfl) ⟨374514, by rfl⟩ : syracuseStep 998705 = 749029) B749029
theorem B998723 : Blo 662308 998723 := bstep (se 1 (by rfl) ⟨749042, by rfl⟩ : syracuseStep 998723 = 1498085) B1498085
theorem B998753 : Blo 662308 998753 := bstep (se 2 (by rfl) ⟨374532, by rfl⟩ : syracuseStep 998753 = 749065) B749065
theorem B998771 : Blo 662308 998771 := bstep (se 1 (by rfl) ⟨749078, by rfl⟩ : syracuseStep 998771 = 1498157) B1498157
theorem B2833805 : Blo 662308 2833805 := bstep (se 3 (by rfl) ⟨531338, by rfl⟩ : syracuseStep 2833805 = 1062677) B1062677
theorem B998801 : Blo 662308 998801 := bstep (se 2 (by rfl) ⟨374550, by rfl⟩ : syracuseStep 998801 = 749101) B749101
theorem B998819 : Blo 662308 998819 := bstep (se 1 (by rfl) ⟨749114, by rfl⟩ : syracuseStep 998819 = 1498229) B1498229
theorem B1064369 : Blo 662308 1064369 := bstep (se 2 (by rfl) ⟨399138, by rfl⟩ : syracuseStep 1064369 = 798277) B798277
theorem B998849 : Blo 662308 998849 := bstep (se 2 (by rfl) ⟨374568, by rfl⟩ : syracuseStep 998849 = 749137) B749137
theorem B998867 : Blo 662308 998867 := bstep (se 1 (by rfl) ⟨749150, by rfl⟩ : syracuseStep 998867 = 1498301) B1498301
theorem B2244077 : Blo 662308 2244077 := bstep (se 3 (by rfl) ⟨420764, by rfl⟩ : syracuseStep 2244077 = 841529) B841529
theorem B1490417 : Blo 662308 1490417 := bstep (se 2 (by rfl) ⟨558906, by rfl⟩ : syracuseStep 1490417 = 1117813) B1117813
theorem B998897 : Blo 662308 998897 := bstep (se 2 (by rfl) ⟨374586, by rfl⟩ : syracuseStep 998897 = 749173) B749173
theorem B1490435 : Blo 662308 1490435 := bstep (se 1 (by rfl) ⟨1117826, by rfl⟩ : syracuseStep 1490435 = 2235653) B2235653
theorem B998915 : Blo 662308 998915 := bstep (se 1 (by rfl) ⟨749186, by rfl⟩ : syracuseStep 998915 = 1498373) B1498373
theorem B998945 : Blo 662308 998945 := bstep (se 2 (by rfl) ⟨374604, by rfl⟩ : syracuseStep 998945 = 749209) B749209
theorem B2244131 : Blo 662308 2244131 := bstep (se 1 (by rfl) ⟨1683098, by rfl⟩ : syracuseStep 2244131 = 3366197) B3366197
theorem B1064497 : Blo 662308 1064497 := bstep (se 2 (by rfl) ⟨399186, by rfl⟩ : syracuseStep 1064497 = 798373) B798373
theorem B998963 : Blo 662308 998963 := bstep (se 1 (by rfl) ⟨749222, by rfl⟩ : syracuseStep 998963 = 1498445) B1498445
theorem B998993 : Blo 662308 998993 := bstep (se 2 (by rfl) ⟨374622, by rfl⟩ : syracuseStep 998993 = 749245) B749245
theorem B999011 : Blo 662308 999011 := bstep (se 1 (by rfl) ⟨749258, by rfl⟩ : syracuseStep 999011 = 1498517) B1498517
theorem B999041 : Blo 662308 999041 := bstep (se 2 (by rfl) ⟨374640, by rfl⟩ : syracuseStep 999041 = 749281) B749281
theorem B999059 : Blo 662308 999059 := bstep (se 1 (by rfl) ⟨749294, by rfl⟩ : syracuseStep 999059 = 1498589) B1498589
theorem B999089 : Blo 662308 999089 := bstep (se 2 (by rfl) ⟨374658, by rfl⟩ : syracuseStep 999089 = 749317) B749317
theorem B1195715 : Blo 662308 1195715 := bstep (se 1 (by rfl) ⟨896786, by rfl⟩ : syracuseStep 1195715 = 1793573) B1793573
theorem B999107 : Blo 662308 999107 := bstep (se 1 (by rfl) ⟨749330, by rfl⟩ : syracuseStep 999107 = 1498661) B1498661
theorem B999137 : Blo 662308 999137 := bstep (se 2 (by rfl) ⟨374676, by rfl⟩ : syracuseStep 999137 = 749353) B749353
theorem B999155 : Blo 662308 999155 := bstep (se 1 (by rfl) ⟨749366, by rfl⟩ : syracuseStep 999155 = 1498733) B1498733
theorem B1490705 : Blo 662308 1490705 := bstep (se 2 (by rfl) ⟨559014, by rfl⟩ : syracuseStep 1490705 = 1118029) B1118029
theorem B999185 : Blo 662308 999185 := bstep (se 2 (by rfl) ⟨374694, by rfl⟩ : syracuseStep 999185 = 749389) B749389
theorem B1490723 : Blo 662308 1490723 := bstep (se 1 (by rfl) ⟨1118042, by rfl⟩ : syracuseStep 1490723 = 2236085) B2236085
theorem B999203 : Blo 662308 999203 := bstep (se 1 (by rfl) ⟨749402, by rfl⟩ : syracuseStep 999203 = 1498805) B1498805
theorem B2244401 : Blo 662308 2244401 := bstep (se 2 (by rfl) ⟨841650, by rfl⟩ : syracuseStep 2244401 = 1683301) B1683301
theorem B999233 : Blo 662308 999233 := bstep (se 2 (by rfl) ⟨374712, by rfl⟩ : syracuseStep 999233 = 749425) B749425
theorem B999251 : Blo 662308 999251 := bstep (se 1 (by rfl) ⟨749438, by rfl⟩ : syracuseStep 999251 = 1498877) B1498877
theorem B999281 : Blo 662308 999281 := bstep (se 2 (by rfl) ⟨374730, by rfl⟩ : syracuseStep 999281 = 749461) B749461
theorem B999299 : Blo 662308 999299 := bstep (se 1 (by rfl) ⟨749474, by rfl⟩ : syracuseStep 999299 = 1498949) B1498949
theorem B999329 : Blo 662308 999329 := bstep (se 2 (by rfl) ⟨374748, by rfl⟩ : syracuseStep 999329 = 749497) B749497
theorem B1261489 : Blo 662308 1261489 := bstep (se 2 (by rfl) ⟨473058, by rfl⟩ : syracuseStep 1261489 = 946117) B946117
theorem B999347 : Blo 662308 999347 := bstep (se 1 (by rfl) ⟨749510, by rfl⟩ : syracuseStep 999347 = 1499021) B1499021
theorem B6799301 : Blo 662308 6799301 := bstep (se 4 (by rfl) ⟨637434, by rfl⟩ : syracuseStep 6799301 = 1274869) B1274869
theorem B999377 : Blo 662308 999377 := bstep (se 2 (by rfl) ⟨374766, by rfl⟩ : syracuseStep 999377 = 749533) B749533
theorem B999395 : Blo 662308 999395 := bstep (se 1 (by rfl) ⟨749546, by rfl⟩ : syracuseStep 999395 = 1499093) B1499093
theorem B999425 : Blo 662308 999425 := bstep (se 2 (by rfl) ⟨374784, by rfl⟩ : syracuseStep 999425 = 749569) B749569
theorem B999443 : Blo 662308 999443 := bstep (se 1 (by rfl) ⟨749582, by rfl⟩ : syracuseStep 999443 = 1499165) B1499165
theorem B1490993 : Blo 662308 1490993 := bstep (se 2 (by rfl) ⟨559122, by rfl⟩ : syracuseStep 1490993 = 1118245) B1118245
theorem B1491011 : Blo 662308 1491011 := bstep (se 1 (by rfl) ⟨1118258, by rfl⟩ : syracuseStep 1491011 = 2236517) B2236517
theorem B1261649 : Blo 662308 1261649 := bstep (se 2 (by rfl) ⟨473118, by rfl⟩ : syracuseStep 1261649 = 946237) B946237
theorem B3227789 : Blo 662308 3227789 := bstep (se 3 (by rfl) ⟨605210, by rfl⟩ : syracuseStep 3227789 = 1210421) B1210421
theorem B7585973 : Blo 662308 7585973 := bstep (se 5 (by rfl) ⟨355592, by rfl⟩ : syracuseStep 7585973 = 711185) B711185
theorem B2244941 : Blo 662308 2244941 := bstep (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) B841853
theorem B1491281 : Blo 662308 1491281 := bstep (se 2 (by rfl) ⟨559230, by rfl⟩ : syracuseStep 1491281 = 1118461) B1118461
theorem B1491299 : Blo 662308 1491299 := bstep (se 1 (by rfl) ⟨1118474, by rfl⟩ : syracuseStep 1491299 = 2236949) B2236949
theorem B3064177 : Blo 662308 3064177 := bstep (se 2 (by rfl) ⟨1149066, by rfl⟩ : syracuseStep 3064177 = 2298133) B2298133
theorem B2244995 : Blo 662308 2244995 := bstep (se 1 (by rfl) ⟨1683746, by rfl⟩ : syracuseStep 2244995 = 3367493) B3367493
theorem B14336453 : Blo 662308 14336453 := bstep (se 4 (by rfl) ⟨1344042, by rfl⟩ : syracuseStep 14336453 = 2688085) B2688085
theorem B1262051 : Blo 662308 1262051 := bstep (se 1 (by rfl) ⟨946538, by rfl⟩ : syracuseStep 1262051 = 1893077) B1893077
theorem B1065491 : Blo 662308 1065491 := bstep (se 1 (by rfl) ⟨799118, by rfl⟩ : syracuseStep 1065491 = 1598237) B1598237
theorem B1491569 : Blo 662308 1491569 := bstep (se 2 (by rfl) ⟨559338, by rfl⟩ : syracuseStep 1491569 = 1118677) B1118677
theorem B1491587 : Blo 662308 1491587 := bstep (se 1 (by rfl) ⟨1118690, by rfl⟩ : syracuseStep 1491587 = 2237381) B2237381
theorem B2245265 : Blo 662308 2245265 := bstep (se 2 (by rfl) ⟨841974, by rfl⟩ : syracuseStep 2245265 = 1683949) B1683949
theorem B1491857 : Blo 662308 1491857 := bstep (se 2 (by rfl) ⟨559446, by rfl⟩ : syracuseStep 1491857 = 1118893) B1118893
theorem B1491875 : Blo 662308 1491875 := bstep (se 1 (by rfl) ⟨1118906, by rfl⟩ : syracuseStep 1491875 = 2237813) B2237813
theorem B3195875 : Blo 662308 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B4244557 : Blo 662308 4244557 := bstep (se 3 (by rfl) ⟨795854, by rfl⟩ : syracuseStep 4244557 = 1591709) B1591709
theorem B25937009 : Blo 662308 25937009 := bstep (se 2 (by rfl) ⟨9726378, by rfl⟩ : syracuseStep 25937009 = 19452757) B19452757
theorem B3458189 : Blo 662308 3458189 := bstep (se 3 (by rfl) ⟨648410, by rfl⟩ : syracuseStep 3458189 = 1296821) B1296821
theorem B2245805 : Blo 662308 2245805 := bstep (se 3 (by rfl) ⟨421088, by rfl⟩ : syracuseStep 2245805 = 842177) B842177
theorem B1492145 : Blo 662308 1492145 := bstep (se 2 (by rfl) ⟨559554, by rfl⟩ : syracuseStep 1492145 = 1119109) B1119109
theorem B1492163 : Blo 662308 1492163 := bstep (se 1 (by rfl) ⟨1119122, by rfl⟩ : syracuseStep 1492163 = 2238245) B2238245
theorem B4048069 : Blo 662308 4048069 := bstep (se 4 (by rfl) ⟨379506, by rfl⟩ : syracuseStep 4048069 = 759013) B759013
theorem B2245859 : Blo 662308 2245859 := bstep (se 1 (by rfl) ⟨1684394, by rfl⟩ : syracuseStep 2245859 = 3368789) B3368789
theorem B3786061 : Blo 662308 3786061 := bstep (se 3 (by rfl) ⟨709886, by rfl⟩ : syracuseStep 3786061 = 1419773) B1419773
theorem B1262947 : Blo 662308 1262947 := bstep (se 1 (by rfl) ⟨947210, by rfl⟩ : syracuseStep 1262947 = 1894421) B1894421
theorem B1492433 : Blo 662308 1492433 := bstep (se 2 (by rfl) ⟨559662, by rfl⟩ : syracuseStep 1492433 = 1119325) B1119325
theorem B1492451 : Blo 662308 1492451 := bstep (se 1 (by rfl) ⟨1119338, by rfl⟩ : syracuseStep 1492451 = 2238677) B2238677
theorem B2246129 : Blo 662308 2246129 := bstep (se 2 (by rfl) ⟨842298, by rfl⟩ : syracuseStep 2246129 = 1684597) B1684597
theorem B673283 : Blo 662308 673283 := bstep (se 1 (by rfl) ⟨504962, by rfl⟩ : syracuseStep 673283 = 1009925) B1009925
theorem B1263107 : Blo 662308 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B3196529 : Blo 662308 3196529 := bstep (se 2 (by rfl) ⟨1198698, by rfl⟩ : syracuseStep 3196529 = 2397397) B2397397
theorem B1230545 : Blo 662308 1230545 := bstep (se 2 (by rfl) ⟨461454, by rfl⟩ : syracuseStep 1230545 = 922909) B922909
theorem B1492721 : Blo 662308 1492721 := bstep (se 2 (by rfl) ⟨559770, by rfl⟩ : syracuseStep 1492721 = 1119541) B1119541
theorem B1492739 : Blo 662308 1492739 := bstep (se 1 (by rfl) ⟨1119554, by rfl⟩ : syracuseStep 1492739 = 2239109) B2239109
theorem B1886129 : Blo 662308 1886129 := bstep (se 2 (by rfl) ⟨707298, by rfl⟩ : syracuseStep 1886129 = 1414597) B1414597
theorem B3360689 : Blo 662308 3360689 := bstep (se 2 (by rfl) ⟨1260258, by rfl⟩ : syracuseStep 3360689 = 2520517) B2520517
theorem B1066945 : Blo 662308 1066945 := bstep (se 2 (by rfl) ⟨400104, by rfl⟩ : syracuseStep 1066945 = 800209) B800209
theorem B2246669 : Blo 662308 2246669 := bstep (se 3 (by rfl) ⟨421250, by rfl⟩ : syracuseStep 2246669 = 842501) B842501
theorem B1493009 : Blo 662308 1493009 := bstep (se 2 (by rfl) ⟨559878, by rfl⟩ : syracuseStep 1493009 = 1119757) B1119757
theorem B1493027 : Blo 662308 1493027 := bstep (se 1 (by rfl) ⟨1119770, by rfl⟩ : syracuseStep 1493027 = 2239541) B2239541
theorem B2246723 : Blo 662308 2246723 := bstep (se 1 (by rfl) ⟨1685042, by rfl⟩ : syracuseStep 2246723 = 3370085) B3370085
theorem B3590257 : Blo 662308 3590257 := bstep (se 2 (by rfl) ⟨1346346, by rfl⟩ : syracuseStep 3590257 = 2692693) B2692693
theorem B6146189 : Blo 662308 6146189 := bstep (se 3 (by rfl) ⟨1152410, by rfl⟩ : syracuseStep 6146189 = 2304821) B2304821
theorem B1493297 : Blo 662308 1493297 := bstep (se 2 (by rfl) ⟨559986, by rfl⟩ : syracuseStep 1493297 = 1119973) B1119973
theorem B1493315 : Blo 662308 1493315 := bstep (se 1 (by rfl) ⟨1119986, by rfl⟩ : syracuseStep 1493315 = 2239973) B2239973
theorem B2246993 : Blo 662308 2246993 := bstep (se 2 (by rfl) ⟨842622, by rfl⟩ : syracuseStep 2246993 = 1685245) B1685245
theorem B4540805 : Blo 662308 4540805 := bstep (se 4 (by rfl) ⟨425700, by rfl⟩ : syracuseStep 4540805 = 851401) B851401
theorem B1591825 : Blo 662308 1591825 := bstep (se 2 (by rfl) ⟨596934, by rfl⟩ : syracuseStep 1591825 = 1193869) B1193869
theorem B1264177 : Blo 662308 1264177 := bstep (se 2 (by rfl) ⟨474066, by rfl⟩ : syracuseStep 1264177 = 948133) B948133
theorem B1493585 : Blo 662308 1493585 := bstep (se 2 (by rfl) ⟨560094, by rfl⟩ : syracuseStep 1493585 = 1120189) B1120189
theorem B1493603 : Blo 662308 1493603 := bstep (se 1 (by rfl) ⟨1120202, by rfl⟩ : syracuseStep 1493603 = 2240405) B2240405
theorem B1886915 : Blo 662308 1886915 := bstep (se 1 (by rfl) ⟨1415186, by rfl⟩ : syracuseStep 1886915 = 2830373) B2830373
theorem B838451 : Blo 662308 838451 := bstep (se 1 (by rfl) ⟨628838, by rfl⟩ : syracuseStep 838451 = 1257677) B1257677
theorem B2247533 : Blo 662308 2247533 := bstep (se 3 (by rfl) ⟨421412, by rfl⟩ : syracuseStep 2247533 = 842825) B842825
theorem B1493873 : Blo 662308 1493873 := bstep (se 2 (by rfl) ⟨560202, by rfl⟩ : syracuseStep 1493873 = 1120405) B1120405
theorem B1493891 : Blo 662308 1493891 := bstep (se 1 (by rfl) ⟨1120418, by rfl⟩ : syracuseStep 1493891 = 2240837) B2240837
theorem B2050957 : Blo 662308 2050957 := bstep (se 3 (by rfl) ⟨384554, by rfl⟩ : syracuseStep 2050957 = 769109) B769109
theorem B707491 : Blo 662308 707491 := bstep (se 1 (by rfl) ⟨530618, by rfl⟩ : syracuseStep 707491 = 1061237) B1061237
theorem B2247587 : Blo 662308 2247587 := bstep (se 1 (by rfl) ⟨1685690, by rfl⟩ : syracuseStep 2247587 = 3371381) B3371381
theorem B3197873 : Blo 662308 3197873 := bstep (se 2 (by rfl) ⟨1199202, by rfl⟩ : syracuseStep 3197873 = 2398405) B2398405
theorem B1887245 : Blo 662308 1887245 := bstep (se 3 (by rfl) ⟨353858, by rfl⟩ : syracuseStep 1887245 = 707717) B707717
theorem B1887313 : Blo 662308 1887313 := bstep (se 2 (by rfl) ⟨707742, by rfl⟩ : syracuseStep 1887313 = 1415485) B1415485
theorem B1494161 : Blo 662308 1494161 := bstep (se 2 (by rfl) ⟨560310, by rfl⟩ : syracuseStep 1494161 = 1120621) B1120621
theorem B1494179 : Blo 662308 1494179 := bstep (se 1 (by rfl) ⟨1120634, by rfl⟩ : syracuseStep 1494179 = 2241269) B2241269
theorem B2247857 : Blo 662308 2247857 := bstep (se 2 (by rfl) ⟨842946, by rfl⟩ : syracuseStep 2247857 = 1685893) B1685893
theorem B4246789 : Blo 662308 4246789 := bstep (se 4 (by rfl) ⟨398136, by rfl⟩ : syracuseStep 4246789 = 796273) B796273
theorem B3788045 : Blo 662308 3788045 := bstep (se 3 (by rfl) ⟨710258, by rfl⟩ : syracuseStep 3788045 = 1420517) B1420517
theorem B1887587 : Blo 662308 1887587 := bstep (se 1 (by rfl) ⟨1415690, by rfl⟩ : syracuseStep 1887587 = 2831381) B2831381
theorem B3362147 : Blo 662308 3362147 := bstep (se 1 (by rfl) ⟨2521610, by rfl⟩ : syracuseStep 3362147 = 5043221) B5043221
theorem B1494449 : Blo 662308 1494449 := bstep (se 2 (by rfl) ⟨560418, by rfl⟩ : syracuseStep 1494449 = 1120837) B1120837
theorem B1494467 : Blo 662308 1494467 := bstep (se 1 (by rfl) ⟨1120850, by rfl⟩ : syracuseStep 1494467 = 2241701) B2241701
theorem B839155 : Blo 662308 839155 := bstep (se 1 (by rfl) ⟨629366, by rfl⟩ : syracuseStep 839155 = 1258733) B1258733
theorem B839251 : Blo 662308 839251 := bstep (se 1 (by rfl) ⟨629438, by rfl⟩ : syracuseStep 839251 = 1258877) B1258877
theorem B2838179 : Blo 662308 2838179 := bstep (se 1 (by rfl) ⟨2128634, by rfl⟩ : syracuseStep 2838179 = 4257269) B4257269
theorem B2248397 : Blo 662308 2248397 := bstep (se 3 (by rfl) ⟨421574, by rfl⟩ : syracuseStep 2248397 = 843149) B843149
theorem B1494737 : Blo 662308 1494737 := bstep (se 2 (by rfl) ⟨560526, by rfl⟩ : syracuseStep 1494737 = 1121053) B1121053
theorem B1494755 : Blo 662308 1494755 := bstep (se 1 (by rfl) ⟨1121066, by rfl⟩ : syracuseStep 1494755 = 2242133) B2242133
theorem B2248451 : Blo 662308 2248451 := bstep (se 1 (by rfl) ⟨1686338, by rfl⟩ : syracuseStep 2248451 = 3372677) B3372677
theorem B4542277 : Blo 662308 4542277 := bstep (se 4 (by rfl) ⟨425838, by rfl⟩ : syracuseStep 4542277 = 851677) B851677
theorem B3198797 : Blo 662308 3198797 := bstep (se 3 (by rfl) ⟨599774, by rfl⟩ : syracuseStep 3198797 = 1199549) B1199549
theorem B1495025 : Blo 662308 1495025 := bstep (se 2 (by rfl) ⟨560634, by rfl⟩ : syracuseStep 1495025 = 1121269) B1121269
theorem B1495043 : Blo 662308 1495043 := bstep (se 1 (by rfl) ⟨1121282, by rfl⟩ : syracuseStep 1495043 = 2242565) B2242565
theorem B3198989 : Blo 662308 3198989 := bstep (se 3 (by rfl) ⟨599810, by rfl⟩ : syracuseStep 3198989 = 1199621) B1199621
theorem B2248721 : Blo 662308 2248721 := bstep (se 2 (by rfl) ⟨843270, by rfl⟩ : syracuseStep 2248721 = 1686541) B1686541
theorem B839747 : Blo 662308 839747 := bstep (se 1 (by rfl) ⟨629810, by rfl⟩ : syracuseStep 839747 = 1259621) B1259621
theorem B3362957 : Blo 662308 3362957 := bstep (se 3 (by rfl) ⟨630554, by rfl⟩ : syracuseStep 3362957 = 1261109) B1261109
theorem B708755 : Blo 662308 708755 := bstep (se 1 (by rfl) ⟨531566, by rfl⟩ : syracuseStep 708755 = 1063133) B1063133
theorem B1888429 : Blo 662308 1888429 := bstep (se 3 (by rfl) ⟨354080, by rfl⟩ : syracuseStep 1888429 = 708161) B708161
theorem B3788977 : Blo 662308 3788977 := bstep (se 2 (by rfl) ⟨1420866, by rfl⟩ : syracuseStep 3788977 = 2841733) B2841733
theorem B1495313 : Blo 662308 1495313 := bstep (se 2 (by rfl) ⟨560742, by rfl⟩ : syracuseStep 1495313 = 1121485) B1121485
theorem B1495331 : Blo 662308 1495331 := bstep (se 1 (by rfl) ⟨1121498, by rfl⟩ : syracuseStep 1495331 = 2242997) B2242997
theorem B1134913 : Blo 662308 1134913 := bstep (se 2 (by rfl) ⟨425592, by rfl⟩ : syracuseStep 1134913 = 851185) B851185
theorem B1888589 : Blo 662308 1888589 := bstep (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) B708221
theorem B1888771 : Blo 662308 1888771 := bstep (se 1 (by rfl) ⟨1416578, by rfl⟩ : syracuseStep 1888771 = 2833157) B2833157
theorem B18469397 : Blo 662308 18469397 := bstep (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) B865753
theorem B1495601 : Blo 662308 1495601 := bstep (se 2 (by rfl) ⟨560850, by rfl⟩ : syracuseStep 1495601 = 1121701) B1121701
theorem B10768949 : Blo 662308 10768949 := bstep (se 5 (by rfl) ⟨504794, by rfl⟩ : syracuseStep 10768949 = 1009589) B1009589
theorem B1495619 : Blo 662308 1495619 := bstep (se 1 (by rfl) ⟨1121714, by rfl⟩ : syracuseStep 1495619 = 2243429) B2243429
theorem B840451 : Blo 662308 840451 := bstep (se 1 (by rfl) ⟨630338, by rfl⟩ : syracuseStep 840451 = 1260677) B1260677
theorem B1495889 : Blo 662308 1495889 := bstep (se 2 (by rfl) ⟨560958, by rfl⟩ : syracuseStep 1495889 = 1121917) B1121917
theorem B840547 : Blo 662308 840547 := bstep (se 1 (by rfl) ⟨630410, by rfl⟩ : syracuseStep 840547 = 1260821) B1260821
theorem B1495907 : Blo 662308 1495907 := bstep (se 1 (by rfl) ⟨1121930, by rfl⟩ : syracuseStep 1495907 = 2243861) B2243861
theorem B709507 : Blo 662308 709507 := bstep (se 1 (by rfl) ⟨532130, by rfl⟩ : syracuseStep 709507 = 1064261) B1064261
theorem B3232781 : Blo 662308 3232781 := bstep (se 3 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 3232781 = 1212293) B1212293
theorem B1496177 : Blo 662308 1496177 := bstep (se 2 (by rfl) ⟨561066, by rfl⟩ : syracuseStep 1496177 = 1122133) B1122133
theorem B1496195 : Blo 662308 1496195 := bstep (se 1 (by rfl) ⟨1122146, by rfl⟩ : syracuseStep 1496195 = 2244293) B2244293
theorem B3232931 : Blo 662308 3232931 := bstep (se 1 (by rfl) ⟨2424698, by rfl⟩ : syracuseStep 3232931 = 4849397) B4849397
theorem B1824049 : Blo 662308 1824049 := bstep (se 2 (by rfl) ⟨684018, by rfl⟩ : syracuseStep 1824049 = 1368037) B1368037
theorem B841043 : Blo 662308 841043 := bstep (se 1 (by rfl) ⟨630782, by rfl⟩ : syracuseStep 841043 = 1261565) B1261565
theorem B1496465 : Blo 662308 1496465 := bstep (se 2 (by rfl) ⟨561174, by rfl⟩ : syracuseStep 1496465 = 1122349) B1122349
theorem B1496483 : Blo 662308 1496483 := bstep (se 1 (by rfl) ⟨1122362, by rfl⟩ : syracuseStep 1496483 = 2244725) B2244725
theorem B3790435 : Blo 662308 3790435 := bstep (se 1 (by rfl) ⟨2842826, by rfl⟩ : syracuseStep 3790435 = 5685653) B5685653
theorem B1496753 : Blo 662308 1496753 := bstep (se 2 (by rfl) ⟨561282, by rfl⟩ : syracuseStep 1496753 = 1122565) B1122565
theorem B1496771 : Blo 662308 1496771 := bstep (se 1 (by rfl) ⟨1122578, by rfl⟩ : syracuseStep 1496771 = 2245157) B2245157
theorem B3594061 : Blo 662308 3594061 := bstep (se 3 (by rfl) ⟨673886, by rfl⟩ : syracuseStep 3594061 = 1347773) B1347773
theorem B1890161 : Blo 662308 1890161 := bstep (se 2 (by rfl) ⟨708810, by rfl⟩ : syracuseStep 1890161 = 1417621) B1417621
theorem B710579 : Blo 662308 710579 := bstep (se 1 (by rfl) ⟨532934, by rfl⟩ : syracuseStep 710579 = 1065869) B1065869
theorem B1497041 : Blo 662308 1497041 := bstep (se 2 (by rfl) ⟨561390, by rfl⟩ : syracuseStep 1497041 = 1122781) B1122781
theorem B1791971 : Blo 662308 1791971 := bstep (se 1 (by rfl) ⟨1343978, by rfl⟩ : syracuseStep 1791971 = 2687957) B2687957
theorem B1497059 : Blo 662308 1497059 := bstep (se 1 (by rfl) ⟨1122794, by rfl⟩ : syracuseStep 1497059 = 2245589) B2245589
theorem B841747 : Blo 662308 841747 := bstep (se 1 (by rfl) ⟨631310, by rfl⟩ : syracuseStep 841747 = 1262621) B1262621
theorem B3790961 : Blo 662308 3790961 := bstep (se 2 (by rfl) ⟨1421610, by rfl⟩ : syracuseStep 3790961 = 2843221) B2843221
theorem B841843 : Blo 662308 841843 := bstep (se 1 (by rfl) ⟨631382, by rfl⟩ : syracuseStep 841843 = 1262765) B1262765
theorem B1923203 : Blo 662308 1923203 := bstep (se 1 (by rfl) ⟨1442402, by rfl⟩ : syracuseStep 1923203 = 2884805) B2884805
theorem B1792145 : Blo 662308 1792145 := bstep (se 2 (by rfl) ⟨672054, by rfl⟩ : syracuseStep 1792145 = 1344109) B1344109
theorem B1497329 : Blo 662308 1497329 := bstep (se 2 (by rfl) ⟨561498, by rfl⟩ : syracuseStep 1497329 = 1122997) B1122997
theorem B1497347 : Blo 662308 1497347 := bstep (se 1 (by rfl) ⟨1123010, by rfl⟩ : syracuseStep 1497347 = 2246021) B2246021
theorem B2840845 : Blo 662308 2840845 := bstep (se 3 (by rfl) ⟨532658, by rfl⟩ : syracuseStep 2840845 = 1065317) B1065317
theorem B2021699 : Blo 662308 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B3037709 : Blo 662308 3037709 := bstep (se 3 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 3037709 = 1139141) B1139141
theorem B1497617 : Blo 662308 1497617 := bstep (se 2 (by rfl) ⟨561606, by rfl⟩ : syracuseStep 1497617 = 1123213) B1123213
theorem B907795 : Blo 662308 907795 := bstep (se 1 (by rfl) ⟨680846, by rfl⟩ : syracuseStep 907795 = 1361693) B1361693
theorem B1497635 : Blo 662308 1497635 := bstep (se 1 (by rfl) ⟨1123226, by rfl⟩ : syracuseStep 1497635 = 2246453) B2246453
theorem B2185805 : Blo 662308 2185805 := bstep (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) B819677
theorem B842339 : Blo 662308 842339 := bstep (se 1 (by rfl) ⟨631754, by rfl⟩ : syracuseStep 842339 = 1263509) B1263509
theorem B3595013 : Blo 662308 3595013 := bstep (se 4 (by rfl) ⟨337032, by rfl⟩ : syracuseStep 3595013 = 674065) B674065
theorem B1891117 : Blo 662308 1891117 := bstep (se 3 (by rfl) ⟨354584, by rfl⟩ : syracuseStep 1891117 = 709169) B709169
theorem B1497905 : Blo 662308 1497905 := bstep (se 2 (by rfl) ⟨561714, by rfl⟩ : syracuseStep 1497905 = 1123429) B1123429
theorem B1497923 : Blo 662308 1497923 := bstep (se 1 (by rfl) ⟨1123442, by rfl⟩ : syracuseStep 1497923 = 2246885) B2246885
theorem B1137539 : Blo 662308 1137539 := bstep (se 1 (by rfl) ⟨853154, by rfl⟩ : syracuseStep 1137539 = 1706309) B1706309
theorem B1596323 : Blo 662308 1596323 := bstep (se 1 (by rfl) ⟨1197242, by rfl⟩ : syracuseStep 1596323 = 2394485) B2394485
theorem B3365873 : Blo 662308 3365873 := bstep (se 2 (by rfl) ⟨1262202, by rfl⟩ : syracuseStep 3365873 = 2524405) B2524405
theorem B1137649 : Blo 662308 1137649 := bstep (se 2 (by rfl) ⟨426618, by rfl⟩ : syracuseStep 1137649 = 853237) B853237
theorem B1891345 : Blo 662308 1891345 := bstep (se 2 (by rfl) ⟨709254, by rfl⟩ : syracuseStep 1891345 = 1418509) B1418509
theorem B973873 : Blo 662308 973873 := bstep (se 2 (by rfl) ⟨365202, by rfl⟩ : syracuseStep 973873 = 730405) B730405
theorem B1498193 : Blo 662308 1498193 := bstep (se 2 (by rfl) ⟨561822, by rfl⟩ : syracuseStep 1498193 = 1123645) B1123645
theorem B1498211 : Blo 662308 1498211 := bstep (se 1 (by rfl) ⟨1123658, by rfl⟩ : syracuseStep 1498211 = 2247317) B2247317
theorem B1891505 : Blo 662308 1891505 := bstep (se 2 (by rfl) ⟨709314, by rfl⟩ : syracuseStep 1891505 = 1418629) B1418629
theorem B1137923 : Blo 662308 1137923 := bstep (se 1 (by rfl) ⟨853442, by rfl⟩ : syracuseStep 1137923 = 1706885) B1706885
theorem B1891619 : Blo 662308 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B843043 : Blo 662308 843043 := bstep (se 1 (by rfl) ⟨632282, by rfl⟩ : syracuseStep 843043 = 1264565) B1264565
theorem B2841905 : Blo 662308 2841905 := bstep (se 2 (by rfl) ⟨1065714, by rfl⟩ : syracuseStep 2841905 = 2131429) B2131429
theorem B1498481 : Blo 662308 1498481 := bstep (se 2 (by rfl) ⟨561930, by rfl⟩ : syracuseStep 1498481 = 1123861) B1123861
theorem B1498499 : Blo 662308 1498499 := bstep (se 1 (by rfl) ⟨1123874, by rfl⟩ : syracuseStep 1498499 = 2247749) B2247749
theorem B843139 : Blo 662308 843139 := bstep (se 1 (by rfl) ⟨632354, by rfl⟩ : syracuseStep 843139 = 1264709) B1264709
theorem B3792419 : Blo 662308 3792419 := bstep (se 1 (by rfl) ⟨2844314, by rfl⟩ : syracuseStep 3792419 = 5688629) B5688629
theorem B1498769 : Blo 662308 1498769 := bstep (se 2 (by rfl) ⟨562038, by rfl⟩ : syracuseStep 1498769 = 1124077) B1124077
theorem B745123 : Blo 662308 745123 := bstep (se 1 (by rfl) ⟨558842, by rfl⟩ : syracuseStep 745123 = 1117685) B1117685
theorem B1597091 : Blo 662308 1597091 := bstep (se 1 (by rfl) ⟨1197818, by rfl⟩ : syracuseStep 1597091 = 2395637) B2395637
theorem B1498787 : Blo 662308 1498787 := bstep (se 1 (by rfl) ⟨1124090, by rfl⟩ : syracuseStep 1498787 = 2248181) B2248181
theorem B745267 : Blo 662308 745267 := bstep (se 1 (by rfl) ⟨558950, by rfl⟩ : syracuseStep 745267 = 1117901) B1117901
theorem B1499057 : Blo 662308 1499057 := bstep (se 2 (by rfl) ⟨562146, by rfl⟩ : syracuseStep 1499057 = 1124293) B1124293
theorem B745411 : Blo 662308 745411 := bstep (se 1 (by rfl) ⟨559058, by rfl⟩ : syracuseStep 745411 = 1118117) B1118117
theorem B1499075 : Blo 662308 1499075 := bstep (se 1 (by rfl) ⟨1124306, by rfl⟩ : syracuseStep 1499075 = 2248613) B2248613
theorem B7561187 : Blo 662308 7561187 := bstep (se 1 (by rfl) ⟨5670890, by rfl⟩ : syracuseStep 7561187 = 11341781) B11341781
theorem B745555 : Blo 662308 745555 := bstep (se 1 (by rfl) ⟨559166, by rfl⟩ : syracuseStep 745555 = 1118333) B1118333
theorem B1597553 : Blo 662308 1597553 := bstep (se 2 (by rfl) ⟨599082, by rfl⟩ : syracuseStep 1597553 = 1198165) B1198165
theorem B2121869 : Blo 662308 2121869 := bstep (se 3 (by rfl) ⟨397850, by rfl⟩ : syracuseStep 2121869 = 795701) B795701
theorem B1794221 : Blo 662308 1794221 := bstep (se 3 (by rfl) ⟨336416, by rfl⟩ : syracuseStep 1794221 = 672833) B672833
theorem B1597649 : Blo 662308 1597649 := bstep (se 2 (by rfl) ⟨599118, by rfl⟩ : syracuseStep 1597649 = 1198237) B1198237
theorem B2515171 : Blo 662308 2515171 := bstep (se 1 (by rfl) ⟨1886378, by rfl⟩ : syracuseStep 2515171 = 3772757) B3772757
theorem B745699 : Blo 662308 745699 := bstep (se 1 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 745699 = 1118549) B1118549
theorem B1892621 : Blo 662308 1892621 := bstep (se 3 (by rfl) ⟨354866, by rfl⟩ : syracuseStep 1892621 = 709733) B709733
theorem B745843 : Blo 662308 745843 := bstep (se 1 (by rfl) ⟨559382, by rfl⟩ : syracuseStep 745843 = 1118765) B1118765
theorem B3367331 : Blo 662308 3367331 := bstep (se 1 (by rfl) ⟨2525498, by rfl⟩ : syracuseStep 3367331 = 5050997) B5050997
theorem B1892803 : Blo 662308 1892803 := bstep (se 1 (by rfl) ⟨1419602, by rfl⟩ : syracuseStep 1892803 = 2839205) B2839205
theorem B745987 : Blo 662308 745987 := bstep (se 1 (by rfl) ⟨559490, by rfl⟩ : syracuseStep 745987 = 1118981) B1118981
theorem B1892963 : Blo 662308 1892963 := bstep (se 1 (by rfl) ⟨1419722, by rfl⟩ : syracuseStep 1892963 = 2839445) B2839445
theorem B746131 : Blo 662308 746131 := bstep (se 1 (by rfl) ⟨559598, by rfl⟩ : syracuseStep 746131 = 1119197) B1119197
theorem B746275 : Blo 662308 746275 := bstep (se 1 (by rfl) ⟨559706, by rfl⟩ : syracuseStep 746275 = 1119413) B1119413
theorem B4776803 : Blo 662308 4776803 := bstep (se 1 (by rfl) ⟨3582602, by rfl⟩ : syracuseStep 4776803 = 7165205) B7165205
theorem B746419 : Blo 662308 746419 := bstep (se 1 (by rfl) ⟨559814, by rfl⟩ : syracuseStep 746419 = 1119629) B1119629
theorem B943121 : Blo 662308 943121 := bstep (se 2 (by rfl) ⟨353670, by rfl⟩ : syracuseStep 943121 = 707341) B707341
theorem B1139729 : Blo 662308 1139729 := bstep (se 2 (by rfl) ⟨427398, by rfl⟩ : syracuseStep 1139729 = 854797) B854797
theorem B746563 : Blo 662308 746563 := bstep (se 1 (by rfl) ⟨559922, by rfl⟩ : syracuseStep 746563 = 1119845) B1119845
theorem B943201 : Blo 662308 943201 := bstep (se 2 (by rfl) ⟨353700, by rfl⟩ : syracuseStep 943201 = 707401) B707401
theorem B3368141 : Blo 662308 3368141 := bstep (se 3 (by rfl) ⟨631526, by rfl⟩ : syracuseStep 3368141 = 1263053) B1263053
theorem B746707 : Blo 662308 746707 := bstep (se 1 (by rfl) ⟨560030, by rfl⟩ : syracuseStep 746707 = 1120061) B1120061
theorem B746851 : Blo 662308 746851 := bstep (se 1 (by rfl) ⟨560138, by rfl⟩ : syracuseStep 746851 = 1120277) B1120277
theorem B2024813 : Blo 662308 2024813 := bstep (se 3 (by rfl) ⟨379652, by rfl⟩ : syracuseStep 2024813 = 759305) B759305
theorem B3794309 : Blo 662308 3794309 := bstep (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) B711433
theorem B746995 : Blo 662308 746995 := bstep (se 1 (by rfl) ⟨560246, by rfl⟩ : syracuseStep 746995 = 1120493) B1120493
theorem B910835 : Blo 662308 910835 := bstep (se 1 (by rfl) ⟨683126, by rfl⟩ : syracuseStep 910835 = 1366253) B1366253
theorem B747139 : Blo 662308 747139 := bstep (se 1 (by rfl) ⟨560354, by rfl⟩ : syracuseStep 747139 = 1120709) B1120709
theorem B1894033 : Blo 662308 1894033 := bstep (se 2 (by rfl) ⟨710262, by rfl⟩ : syracuseStep 1894033 = 1420525) B1420525
theorem B2123459 : Blo 662308 2123459 := bstep (se 1 (by rfl) ⟨1592594, by rfl⟩ : syracuseStep 2123459 = 3185189) B3185189
theorem B747283 : Blo 662308 747283 := bstep (se 1 (by rfl) ⟨560462, by rfl⟩ : syracuseStep 747283 = 1120925) B1120925
theorem B943987 : Blo 662308 943987 := bstep (se 1 (by rfl) ⟨707990, by rfl⟩ : syracuseStep 943987 = 1415981) B1415981
theorem B747427 : Blo 662308 747427 := bstep (se 1 (by rfl) ⟨560570, by rfl⟩ : syracuseStep 747427 = 1121141) B1121141
theorem B747571 : Blo 662308 747571 := bstep (se 1 (by rfl) ⟨560678, by rfl⟩ : syracuseStep 747571 = 1121357) B1121357
theorem B747715 : Blo 662308 747715 := bstep (se 1 (by rfl) ⟨560786, by rfl⟩ : syracuseStep 747715 = 1121573) B1121573
theorem B2844877 : Blo 662308 2844877 := bstep (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) B1066829
theorem B944465 : Blo 662308 944465 := bstep (se 2 (by rfl) ⟨354174, by rfl⟩ : syracuseStep 944465 = 708349) B708349
theorem B747859 : Blo 662308 747859 := bstep (se 1 (by rfl) ⟨560894, by rfl⟩ : syracuseStep 747859 = 1121789) B1121789
theorem B2517389 : Blo 662308 2517389 := bstep (se 3 (by rfl) ⟨472010, by rfl⟩ : syracuseStep 2517389 = 944021) B944021
theorem B2124227 : Blo 662308 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B944579 : Blo 662308 944579 := bstep (se 1 (by rfl) ⟨708434, by rfl⟩ : syracuseStep 944579 = 1416869) B1416869
theorem B748003 : Blo 662308 748003 := bstep (se 1 (by rfl) ⟨561002, by rfl⟩ : syracuseStep 748003 = 1122005) B1122005
theorem B944659 : Blo 662308 944659 := bstep (se 1 (by rfl) ⟨708494, by rfl⟩ : syracuseStep 944659 = 1416989) B1416989
theorem B2845219 : Blo 662308 2845219 := bstep (se 1 (by rfl) ⟨2133914, by rfl⟩ : syracuseStep 2845219 = 4267829) B4267829
theorem B748147 : Blo 662308 748147 := bstep (se 1 (by rfl) ⟨561110, by rfl⟩ : syracuseStep 748147 = 1122221) B1122221
theorem B748291 : Blo 662308 748291 := bstep (se 1 (by rfl) ⟨561218, by rfl⟩ : syracuseStep 748291 = 1122437) B1122437
theorem B2124625 : Blo 662308 2124625 := bstep (se 2 (by rfl) ⟨796734, by rfl⟩ : syracuseStep 2124625 = 1593469) B1593469
theorem B4254605 : Blo 662308 4254605 := bstep (se 3 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 4254605 = 1595477) B1595477
theorem B1895309 : Blo 662308 1895309 := bstep (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) B710741
theorem B748435 : Blo 662308 748435 := bstep (se 1 (by rfl) ⟨561326, by rfl⟩ : syracuseStep 748435 = 1122653) B1122653
theorem B2124739 : Blo 662308 2124739 := bstep (se 1 (by rfl) ⟨1593554, by rfl⟩ : syracuseStep 2124739 = 3187109) B3187109
theorem B748579 : Blo 662308 748579 := bstep (se 1 (by rfl) ⟨561434, by rfl⟩ : syracuseStep 748579 = 1122869) B1122869
theorem B945217 : Blo 662308 945217 := bstep (se 2 (by rfl) ⟨354456, by rfl⟩ : syracuseStep 945217 = 708913) B708913
theorem B1895491 : Blo 662308 1895491 := bstep (se 1 (by rfl) ⟨1421618, by rfl⟩ : syracuseStep 1895491 = 2843237) B2843237
theorem B1895537 : Blo 662308 1895537 := bstep (se 2 (by rfl) ⟨710826, by rfl⟩ : syracuseStep 1895537 = 1421653) B1421653
theorem B7302257 : Blo 662308 7302257 := bstep (se 2 (by rfl) ⟨2738346, by rfl⟩ : syracuseStep 7302257 = 5476693) B5476693
theorem B1010819 : Blo 662308 1010819 := bstep (se 1 (by rfl) ⟨758114, by rfl⟩ : syracuseStep 1010819 = 1516229) B1516229
theorem B748723 : Blo 662308 748723 := bstep (se 1 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 748723 = 1123085) B1123085
theorem B748867 : Blo 662308 748867 := bstep (se 1 (by rfl) ⟨561650, by rfl⟩ : syracuseStep 748867 = 1123301) B1123301
theorem B749011 : Blo 662308 749011 := bstep (se 1 (by rfl) ⟨561758, by rfl⟩ : syracuseStep 749011 = 1123517) B1123517
theorem B5041763 : Blo 662308 5041763 := bstep (se 1 (by rfl) ⟨3781322, by rfl⟩ : syracuseStep 5041763 = 7562645) B7562645
theorem B749155 : Blo 662308 749155 := bstep (se 1 (by rfl) ⟨561866, by rfl⟩ : syracuseStep 749155 = 1123733) B1123733
theorem B2125457 : Blo 662308 2125457 := bstep (se 2 (by rfl) ⟨797046, by rfl⟩ : syracuseStep 2125457 = 1594093) B1594093
theorem B1732337 : Blo 662308 1732337 := bstep (se 2 (by rfl) ⟨649626, by rfl⟩ : syracuseStep 1732337 = 1299253) B1299253
theorem B749299 : Blo 662308 749299 := bstep (se 1 (by rfl) ⟨561974, by rfl⟩ : syracuseStep 749299 = 1123949) B1123949
theorem B945923 : Blo 662308 945923 := bstep (se 1 (by rfl) ⟨709442, by rfl⟩ : syracuseStep 945923 = 1418885) B1418885
theorem B4321073 : Blo 662308 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B749443 : Blo 662308 749443 := bstep (se 1 (by rfl) ⟨562082, by rfl⟩ : syracuseStep 749443 = 1124165) B1124165
theorem B749587 : Blo 662308 749587 := bstep (se 1 (by rfl) ⟨562190, by rfl⟩ : syracuseStep 749587 = 1124381) B1124381
theorem B3371057 : Blo 662308 3371057 := bstep (se 2 (by rfl) ⟨1264146, by rfl⟩ : syracuseStep 3371057 = 2528293) B2528293
theorem B2125997 : Blo 662308 2125997 := bstep (se 3 (by rfl) ⟨398624, by rfl⟩ : syracuseStep 2125997 = 797249) B797249
theorem B1077491 : Blo 662308 1077491 := bstep (se 1 (by rfl) ⟨808118, by rfl⟩ : syracuseStep 1077491 = 1616237) B1616237
theorem B946561 : Blo 662308 946561 := bstep (se 2 (by rfl) ⟨354960, by rfl⟩ : syracuseStep 946561 = 709921) B709921
theorem B1012193 : Blo 662308 1012193 := bstep (se 2 (by rfl) ⟨379572, by rfl⟩ : syracuseStep 1012193 = 759145) B759145
theorem B946675 : Blo 662308 946675 := bstep (se 1 (by rfl) ⟨710006, by rfl⟩ : syracuseStep 946675 = 1420013) B1420013
theorem B1896995 : Blo 662308 1896995 := bstep (se 1 (by rfl) ⟨1422746, by rfl⟩ : syracuseStep 1896995 = 2845493) B2845493
theorem B1012387 : Blo 662308 1012387 := bstep (se 1 (by rfl) ⟨759290, by rfl⟩ : syracuseStep 1012387 = 1518581) B1518581
theorem B1799405 : Blo 662308 1799405 := bstep (se 3 (by rfl) ⟨337388, by rfl⟩ : syracuseStep 1799405 = 674777) B674777
theorem B2520305 : Blo 662308 2520305 := bstep (se 2 (by rfl) ⟨945114, by rfl⟩ : syracuseStep 2520305 = 1890229) B1890229
theorem B2389283 : Blo 662308 2389283 := bstep (se 1 (by rfl) ⟨1791962, by rfl⟩ : syracuseStep 2389283 = 3583925) B3583925
theorem B3372515 : Blo 662308 3372515 := bstep (se 1 (by rfl) ⟨2529386, by rfl⟩ : syracuseStep 3372515 = 5058773) B5058773
theorem B1799779 : Blo 662308 1799779 := bstep (se 1 (by rfl) ⟨1349834, by rfl⟩ : syracuseStep 1799779 = 2699669) B2699669
theorem B948019 : Blo 662308 948019 := bstep (se 1 (by rfl) ⟨711014, by rfl⟩ : syracuseStep 948019 = 1422029) B1422029
theorem B2160589 : Blo 662308 2160589 := bstep (se 3 (by rfl) ⟨405110, by rfl⟩ : syracuseStep 2160589 = 810221) B810221
theorem B2127917 : Blo 662308 2127917 := bstep (se 3 (by rfl) ⟨398984, by rfl⟩ : syracuseStep 2127917 = 797969) B797969
theorem B4553059 : Blo 662308 4553059 := bstep (se 1 (by rfl) ⟨3414794, by rfl⟩ : syracuseStep 4553059 = 6829589) B6829589
theorem B1800785 : Blo 662308 1800785 := bstep (se 2 (by rfl) ⟨675294, by rfl⟩ : syracuseStep 1800785 = 1350589) B1350589
theorem B2521763 : Blo 662308 2521763 := bstep (se 1 (by rfl) ⟨1891322, by rfl⟩ : syracuseStep 2521763 = 3782645) B3782645
theorem B2390897 : Blo 662308 2390897 := bstep (se 2 (by rfl) ⟨896586, by rfl⟩ : syracuseStep 2390897 = 1793173) B1793173
theorem B4258757 : Blo 662308 4258757 := bstep (se 4 (by rfl) ⟨399258, by rfl⟩ : syracuseStep 4258757 = 798517) B798517
theorem B719971 : Blo 662308 719971 := bstep (se 1 (by rfl) ⟨539978, by rfl⟩ : syracuseStep 719971 = 1079957) B1079957
theorem B4095281 : Blo 662308 4095281 := bstep (se 2 (by rfl) ⟨1535730, by rfl⟩ : syracuseStep 4095281 = 3071461) B3071461
theorem B3079565 : Blo 662308 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B2686385 : Blo 662308 2686385 := bstep (se 2 (by rfl) ⟨1007394, by rfl⟩ : syracuseStep 2686385 = 2014789) B2014789
theorem B851411 : Blo 662308 851411 := bstep (se 1 (by rfl) ⟨638558, by rfl⟩ : syracuseStep 851411 = 1277117) B1277117
theorem B2391601 : Blo 662308 2391601 := bstep (se 2 (by rfl) ⟨896850, by rfl⟩ : syracuseStep 2391601 = 1793701) B1793701
theorem B2522765 : Blo 662308 2522765 := bstep (se 3 (by rfl) ⟨473018, by rfl⟩ : syracuseStep 2522765 = 946037) B946037
theorem B5373809 : Blo 662308 5373809 := bstep (se 2 (by rfl) ⟨2015178, by rfl⟩ : syracuseStep 5373809 = 4030357) B4030357
theorem B1343459 : Blo 662308 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B13828067 : Blo 662308 13828067 := bstep (se 1 (by rfl) ⟨10371050, by rfl⟩ : syracuseStep 13828067 = 20742101) B20742101
theorem B4260397 : Blo 662308 4260397 := bstep (se 3 (by rfl) ⟨798824, by rfl⟩ : syracuseStep 4260397 = 1597649) B1597649
theorem B2523737 : Blo 662308 2523737 := bstep (se 2 (by rfl) ⟨946401, by rfl⟩ : syracuseStep 2523737 = 1892803) B1892803
theorem B2392669 : Blo 662308 2392669 := bstep (se 3 (by rfl) ⟨448625, by rfl⟩ : syracuseStep 2392669 = 897251) B897251
theorem B4784791 : Blo 662308 4784791 := bstep (se 1 (by rfl) ⟨3588593, by rfl⟩ : syracuseStep 4784791 = 7177187) B7177187
theorem B2130583 : Blo 662308 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B2131019 : Blo 662308 2131019 := bstep (se 1 (by rfl) ⟨1598264, by rfl⟩ : syracuseStep 2131019 = 3196529) B3196529
theorem B820363 : Blo 662308 820363 := bstep (se 1 (by rfl) ⟨615272, by rfl⟩ : syracuseStep 820363 = 1230545) B1230545
theorem B4097459 : Blo 662308 4097459 := bstep (se 1 (by rfl) ⟨3073094, by rfl⟩ : syracuseStep 4097459 = 6146189) B6146189
theorem B6817355 : Blo 662308 6817355 := bstep (se 1 (by rfl) ⟨5113016, by rfl⟩ : syracuseStep 6817355 = 10226033) B10226033
theorem B2557619 : Blo 662308 2557619 := bstep (se 1 (by rfl) ⟨1918214, by rfl⟩ : syracuseStep 2557619 = 3836429) B3836429
theorem B5048081 : Blo 662308 5048081 := bstep (se 2 (by rfl) ⟨1893030, by rfl⟩ : syracuseStep 5048081 = 3786061) B3786061
theorem B2131915 : Blo 662308 2131915 := bstep (se 1 (by rfl) ⟨1598936, by rfl⟩ : syracuseStep 2131915 = 3197873) B3197873
theorem B2525363 : Blo 662308 2525363 := bstep (se 1 (by rfl) ⟨1894022, by rfl⟩ : syracuseStep 2525363 = 3788045) B3788045
theorem B2525377 : Blo 662308 2525377 := bstep (se 2 (by rfl) ⟨947016, by rfl⟩ : syracuseStep 2525377 = 1894033) B1894033
theorem B2132531 : Blo 662308 2132531 := bstep (se 1 (by rfl) ⟨1599398, by rfl⟩ : syracuseStep 2132531 = 3198797) B3198797
theorem B5376689 : Blo 662308 5376689 := bstep (se 2 (by rfl) ⟨2016258, by rfl⟩ : syracuseStep 5376689 = 4032517) B4032517
theorem B2132659 : Blo 662308 2132659 := bstep (se 1 (by rfl) ⟨1599494, by rfl⟩ : syracuseStep 2132659 = 3198989) B3198989
theorem B5737177 : Blo 662308 5737177 := bstep (se 2 (by rfl) ⟨2151441, by rfl⟩ : syracuseStep 5737177 = 4302883) B4302883
theorem B4787009 : Blo 662308 4787009 := bstep (se 2 (by rfl) ⟨1795128, by rfl⟩ : syracuseStep 4787009 = 3590257) B3590257
theorem B5671781 : Blo 662308 5671781 := bstep (se 4 (by rfl) ⟨531729, by rfl⟩ : syracuseStep 5671781 = 1063459) B1063459
theorem B7179299 : Blo 662308 7179299 := bstep (se 1 (by rfl) ⟨5384474, by rfl⟩ : syracuseStep 7179299 = 10768949) B10768949
theorem B8621149 : Blo 662308 8621149 := bstep (se 3 (by rfl) ⟨1616465, by rfl⟩ : syracuseStep 8621149 = 3232931) B3232931
theorem B1117847 : Blo 662308 1117847 := bstep (se 1 (by rfl) ⟨838385, by rfl⟩ : syracuseStep 1117847 = 1676771) B1676771
theorem B1117975 : Blo 662308 1117975 := bstep (se 1 (by rfl) ⟨838481, by rfl⟩ : syracuseStep 1117975 = 1676963) B1676963
theorem B2527307 : Blo 662308 2527307 := bstep (se 1 (by rfl) ⟨1895480, by rfl⟩ : syracuseStep 2527307 = 3790961) B3790961
theorem B1282135 : Blo 662308 1282135 := bstep (se 1 (by rfl) ⟨961601, by rfl⟩ : syracuseStep 1282135 = 1923203) B1923203
theorem B2527321 : Blo 662308 2527321 := bstep (se 2 (by rfl) ⟨947745, by rfl⟩ : syracuseStep 2527321 = 1895491) B1895491
theorem B1118603 : Blo 662308 1118603 := bstep (se 1 (by rfl) ⟨838952, by rfl⟩ : syracuseStep 1118603 = 1677905) B1677905
theorem B2396675 : Blo 662308 2396675 := bstep (se 1 (by rfl) ⟨1797506, by rfl⟩ : syracuseStep 2396675 = 3595013) B3595013
theorem B1118731 : Blo 662308 1118731 := bstep (se 1 (by rfl) ⟨839048, by rfl⟩ : syracuseStep 1118731 = 1678097) B1678097
theorem B1118873 : Blo 662308 1118873 := bstep (se 2 (by rfl) ⟨419577, by rfl⟩ : syracuseStep 1118873 = 839155) B839155
theorem B1119001 : Blo 662308 1119001 := bstep (se 2 (by rfl) ⟨419625, by rfl⟩ : syracuseStep 1119001 = 839251) B839251
theorem B758615 : Blo 662308 758615 := bstep (se 1 (by rfl) ⟨568961, by rfl⟩ : syracuseStep 758615 = 1137923) B1137923
theorem B5378995 : Blo 662308 5378995 := bstep (se 1 (by rfl) ⟨4034246, by rfl⟩ : syracuseStep 5378995 = 8068493) B8068493
theorem B2528279 : Blo 662308 2528279 := bstep (se 1 (by rfl) ⟨1896209, by rfl⟩ : syracuseStep 2528279 = 3792419) B3792419
theorem B2692403 : Blo 662308 2692403 := bstep (se 1 (by rfl) ⟨2019302, by rfl⟩ : syracuseStep 2692403 = 4038605) B4038605
theorem B1676609 : Blo 662308 1676609 := bstep (se 2 (by rfl) ⟨628728, by rfl⟩ : syracuseStep 1676609 = 1257457) B1257457
theorem B1119575 : Blo 662308 1119575 := bstep (se 1 (by rfl) ⟨839681, by rfl⟩ : syracuseStep 1119575 = 1679363) B1679363
theorem B1414579 : Blo 662308 1414579 := bstep (se 1 (by rfl) ⟨1060934, by rfl⟩ : syracuseStep 1414579 = 2121869) B2121869
theorem B5674445 : Blo 662308 5674445 := bstep (se 3 (by rfl) ⟨1063958, by rfl⟩ : syracuseStep 5674445 = 2127917) B2127917
theorem B48534997 : Blo 662308 48534997 := bstep (se 7 (by rfl) ⟨568769, by rfl⟩ : syracuseStep 48534997 = 1137539) B1137539
theorem B1119703 : Blo 662308 1119703 := bstep (se 1 (by rfl) ⟨839777, by rfl⟩ : syracuseStep 1119703 = 1679555) B1679555
theorem B1021465 : Blo 662308 1021465 := bstep (se 2 (by rfl) ⟨383049, by rfl⟩ : syracuseStep 1021465 = 766099) B766099
theorem B5051969 : Blo 662308 5051969 := bstep (se 2 (by rfl) ⟨1894488, by rfl⟩ : syracuseStep 5051969 = 3788977) B3788977
theorem B1513217 : Blo 662308 1513217 := bstep (se 2 (by rfl) ⟨567456, by rfl⟩ : syracuseStep 1513217 = 1134913) B1134913
theorem B1677145 : Blo 662308 1677145 := bstep (se 2 (by rfl) ⟨628929, by rfl⟩ : syracuseStep 1677145 = 1257859) B1257859
theorem B3839845 : Blo 662308 3839845 := bstep (se 4 (by rfl) ⟨359985, by rfl⟩ : syracuseStep 3839845 = 719971) B719971
theorem B3184535 : Blo 662308 3184535 := bstep (se 1 (by rfl) ⟨2388401, by rfl⟩ : syracuseStep 3184535 = 4776803) B4776803
theorem B1120331 : Blo 662308 1120331 := bstep (se 1 (by rfl) ⟨840248, by rfl⟩ : syracuseStep 1120331 = 1680497) B1680497
theorem B2726081 : Blo 662308 2726081 := bstep (se 2 (by rfl) ⟨1022280, by rfl⟩ : syracuseStep 2726081 = 2044561) B2044561
theorem B1120459 : Blo 662308 1120459 := bstep (se 1 (by rfl) ⟨840344, by rfl⟩ : syracuseStep 1120459 = 1680689) B1680689
theorem B1349849 : Blo 662308 1349849 := bstep (se 2 (by rfl) ⟨506193, by rfl⟩ : syracuseStep 1349849 = 1012387) B1012387
theorem B1349875 : Blo 662308 1349875 := bstep (se 1 (by rfl) ⟨1012406, by rfl⟩ : syracuseStep 1349875 = 2024813) B2024813
theorem B2529539 : Blo 662308 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B1120601 : Blo 662308 1120601 := bstep (se 2 (by rfl) ⟨420225, by rfl⟩ : syracuseStep 1120601 = 840451) B840451
theorem B1415639 : Blo 662308 1415639 := bstep (se 1 (by rfl) ⟨1061729, by rfl⟩ : syracuseStep 1415639 = 2123459) B2123459
theorem B1120729 : Blo 662308 1120729 := bstep (se 2 (by rfl) ⟨420273, by rfl⟩ : syracuseStep 1120729 = 840547) B840547
theorem B1415809 : Blo 662308 1415809 := bstep (se 2 (by rfl) ⟨530928, by rfl⟩ : syracuseStep 1415809 = 1061857) B1061857
theorem B8100557 : Blo 662308 8100557 := bstep (se 3 (by rfl) ⟨1518854, by rfl⟩ : syracuseStep 8100557 = 3037709) B3037709
theorem B662315 : Blo 662308 662315 := bstep (se 1 (by rfl) ⟨496736, by rfl⟩ : syracuseStep 662315 = 993473) B993473
theorem B662327 : Blo 662308 662327 := bstep (se 1 (by rfl) ⟨496745, by rfl⟩ : syracuseStep 662327 = 993491) B993491
theorem B662347 : Blo 662308 662347 := bstep (se 1 (by rfl) ⟨496760, by rfl⟩ : syracuseStep 662347 = 993521) B993521
theorem B662359 : Blo 662308 662359 := bstep (se 1 (by rfl) ⟨496769, by rfl⟩ : syracuseStep 662359 = 993539) B993539
theorem B662379 : Blo 662308 662379 := bstep (se 1 (by rfl) ⟨496784, by rfl⟩ : syracuseStep 662379 = 993569) B993569
theorem B662391 : Blo 662308 662391 := bstep (se 1 (by rfl) ⟨496793, by rfl⟩ : syracuseStep 662391 = 993587) B993587
theorem B662411 : Blo 662308 662411 := bstep (se 1 (by rfl) ⟨496808, by rfl⟩ : syracuseStep 662411 = 993617) B993617
theorem B662423 : Blo 662308 662423 := bstep (se 1 (by rfl) ⟨496817, by rfl⟩ : syracuseStep 662423 = 993635) B993635
theorem B662443 : Blo 662308 662443 := bstep (se 1 (by rfl) ⟨496832, by rfl⟩ : syracuseStep 662443 = 993665) B993665
theorem B1678259 : Blo 662308 1678259 := bstep (se 1 (by rfl) ⟨1258694, by rfl⟩ : syracuseStep 1678259 = 2517389) B2517389
theorem B662455 : Blo 662308 662455 := bstep (se 1 (by rfl) ⟨496841, by rfl⟩ : syracuseStep 662455 = 993683) B993683
theorem B2235329 : Blo 662308 2235329 := bstep (se 2 (by rfl) ⟨838248, by rfl⟩ : syracuseStep 2235329 = 1676497) B1676497
theorem B662475 : Blo 662308 662475 := bstep (se 1 (by rfl) ⟨496856, by rfl⟩ : syracuseStep 662475 = 993713) B993713
theorem B662487 : Blo 662308 662487 := bstep (se 1 (by rfl) ⟨496865, by rfl⟩ : syracuseStep 662487 = 993731) B993731
theorem B1416151 : Blo 662308 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B662507 : Blo 662308 662507 := bstep (se 1 (by rfl) ⟨496880, by rfl⟩ : syracuseStep 662507 = 993761) B993761
theorem B662519 : Blo 662308 662519 := bstep (se 1 (by rfl) ⟨496889, by rfl⟩ : syracuseStep 662519 = 993779) B993779
theorem B662539 : Blo 662308 662539 := bstep (se 1 (by rfl) ⟨496904, by rfl⟩ : syracuseStep 662539 = 993809) B993809
theorem B662551 : Blo 662308 662551 := bstep (se 1 (by rfl) ⟨496913, by rfl⟩ : syracuseStep 662551 = 993827) B993827
theorem B1121303 : Blo 662308 1121303 := bstep (se 1 (by rfl) ⟨840977, by rfl⟩ : syracuseStep 1121303 = 1681955) B1681955
theorem B662571 : Blo 662308 662571 := bstep (se 1 (by rfl) ⟨496928, by rfl⟩ : syracuseStep 662571 = 993857) B993857
theorem B662583 : Blo 662308 662583 := bstep (se 1 (by rfl) ⟨496937, by rfl⟩ : syracuseStep 662583 = 993875) B993875
theorem B2432065 : Blo 662308 2432065 := bstep (se 2 (by rfl) ⟨912024, by rfl⟩ : syracuseStep 2432065 = 1824049) B1824049
theorem B662603 : Blo 662308 662603 := bstep (se 1 (by rfl) ⟨496952, by rfl⟩ : syracuseStep 662603 = 993905) B993905
theorem B662615 : Blo 662308 662615 := bstep (se 1 (by rfl) ⟨496961, by rfl⟩ : syracuseStep 662615 = 993923) B993923
theorem B662635 : Blo 662308 662635 := bstep (se 1 (by rfl) ⟨496976, by rfl⟩ : syracuseStep 662635 = 993953) B993953
theorem B662647 : Blo 662308 662647 := bstep (se 1 (by rfl) ⟨496985, by rfl⟩ : syracuseStep 662647 = 993971) B993971
theorem B662667 : Blo 662308 662667 := bstep (se 1 (by rfl) ⟨497000, by rfl⟩ : syracuseStep 662667 = 994001) B994001
theorem B662679 : Blo 662308 662679 := bstep (se 1 (by rfl) ⟨497009, by rfl⟩ : syracuseStep 662679 = 994019) B994019
theorem B1121431 : Blo 662308 1121431 := bstep (se 1 (by rfl) ⟨841073, by rfl⟩ : syracuseStep 1121431 = 1682147) B1682147
theorem B662699 : Blo 662308 662699 := bstep (se 1 (by rfl) ⟨497024, by rfl⟩ : syracuseStep 662699 = 994049) B994049
theorem B662711 : Blo 662308 662711 := bstep (se 1 (by rfl) ⟨497033, by rfl⟩ : syracuseStep 662711 = 994067) B994067
theorem B662731 : Blo 662308 662731 := bstep (se 1 (by rfl) ⟨497048, by rfl⟩ : syracuseStep 662731 = 994097) B994097
theorem B662743 : Blo 662308 662743 := bstep (se 1 (by rfl) ⟨497057, by rfl⟩ : syracuseStep 662743 = 994115) B994115
theorem B1678553 : Blo 662308 1678553 := bstep (se 2 (by rfl) ⟨629457, by rfl⟩ : syracuseStep 1678553 = 1258915) B1258915
theorem B662763 : Blo 662308 662763 := bstep (se 1 (by rfl) ⟨497072, by rfl⟩ : syracuseStep 662763 = 994145) B994145
theorem B662775 : Blo 662308 662775 := bstep (se 1 (by rfl) ⟨497081, by rfl⟩ : syracuseStep 662775 = 994163) B994163
theorem B662795 : Blo 662308 662795 := bstep (se 1 (by rfl) ⟨497096, by rfl⟩ : syracuseStep 662795 = 994193) B994193
theorem B662807 : Blo 662308 662807 := bstep (se 1 (by rfl) ⟨497105, by rfl⟩ : syracuseStep 662807 = 994211) B994211
theorem B662827 : Blo 662308 662827 := bstep (se 1 (by rfl) ⟨497120, by rfl⟩ : syracuseStep 662827 = 994241) B994241
theorem B662839 : Blo 662308 662839 := bstep (se 1 (by rfl) ⟨497129, by rfl⟩ : syracuseStep 662839 = 994259) B994259
theorem B662859 : Blo 662308 662859 := bstep (se 1 (by rfl) ⟨497144, by rfl⟩ : syracuseStep 662859 = 994289) B994289
theorem B662871 : Blo 662308 662871 := bstep (se 1 (by rfl) ⟨497153, by rfl⟩ : syracuseStep 662871 = 994307) B994307
theorem B662891 : Blo 662308 662891 := bstep (se 1 (by rfl) ⟨497168, by rfl⟩ : syracuseStep 662891 = 994337) B994337
theorem B662903 : Blo 662308 662903 := bstep (se 1 (by rfl) ⟨497177, by rfl⟩ : syracuseStep 662903 = 994355) B994355
theorem B662923 : Blo 662308 662923 := bstep (se 1 (by rfl) ⟨497192, by rfl⟩ : syracuseStep 662923 = 994385) B994385
theorem B662935 : Blo 662308 662935 := bstep (se 1 (by rfl) ⟨497201, by rfl⟩ : syracuseStep 662935 = 994403) B994403
theorem B662955 : Blo 662308 662955 := bstep (se 1 (by rfl) ⟨497216, by rfl⟩ : syracuseStep 662955 = 994433) B994433
theorem B662967 : Blo 662308 662967 := bstep (se 1 (by rfl) ⟨497225, by rfl⟩ : syracuseStep 662967 = 994451) B994451
theorem B662987 : Blo 662308 662987 := bstep (se 1 (by rfl) ⟨497240, by rfl⟩ : syracuseStep 662987 = 994481) B994481
theorem B662999 : Blo 662308 662999 := bstep (se 1 (by rfl) ⟨497249, by rfl⟩ : syracuseStep 662999 = 994499) B994499
theorem B5053913 : Blo 662308 5053913 := bstep (se 2 (by rfl) ⟨1895217, by rfl⟩ : syracuseStep 5053913 = 3790435) B3790435
theorem B2399705 : Blo 662308 2399705 := bstep (se 2 (by rfl) ⟨899889, by rfl⟩ : syracuseStep 2399705 = 1799779) B1799779
theorem B2235869 : Blo 662308 2235869 := bstep (se 3 (by rfl) ⟨419225, by rfl⟩ : syracuseStep 2235869 = 838451) B838451
theorem B663019 : Blo 662308 663019 := bstep (se 1 (by rfl) ⟨497264, by rfl⟩ : syracuseStep 663019 = 994529) B994529
theorem B663031 : Blo 662308 663031 := bstep (se 1 (by rfl) ⟨497273, by rfl⟩ : syracuseStep 663031 = 994547) B994547
theorem B663051 : Blo 662308 663051 := bstep (se 1 (by rfl) ⟨497288, by rfl⟩ : syracuseStep 663051 = 994577) B994577
theorem B663063 : Blo 662308 663063 := bstep (se 1 (by rfl) ⟨497297, by rfl⟩ : syracuseStep 663063 = 994595) B994595
theorem B663083 : Blo 662308 663083 := bstep (se 1 (by rfl) ⟨497312, by rfl⟩ : syracuseStep 663083 = 994625) B994625
theorem B2399789 : Blo 662308 2399789 := bstep (se 3 (by rfl) ⟨449960, by rfl⟩ : syracuseStep 2399789 = 899921) B899921
theorem B663095 : Blo 662308 663095 := bstep (se 1 (by rfl) ⟨497321, by rfl⟩ : syracuseStep 663095 = 994643) B994643
theorem B663115 : Blo 662308 663115 := bstep (se 1 (by rfl) ⟨497336, by rfl⟩ : syracuseStep 663115 = 994673) B994673
theorem B663127 : Blo 662308 663127 := bstep (se 1 (by rfl) ⟨497345, by rfl⟩ : syracuseStep 663127 = 994691) B994691
theorem B663147 : Blo 662308 663147 := bstep (se 1 (by rfl) ⟨497360, by rfl⟩ : syracuseStep 663147 = 994721) B994721
theorem B663159 : Blo 662308 663159 := bstep (se 1 (by rfl) ⟨497369, by rfl⟩ : syracuseStep 663159 = 994739) B994739
theorem B663179 : Blo 662308 663179 := bstep (se 1 (by rfl) ⟨497384, by rfl⟩ : syracuseStep 663179 = 994769) B994769
theorem B663191 : Blo 662308 663191 := bstep (se 1 (by rfl) ⟨497393, by rfl⟩ : syracuseStep 663191 = 994787) B994787
theorem B663211 : Blo 662308 663211 := bstep (se 1 (by rfl) ⟨497408, by rfl⟩ : syracuseStep 663211 = 994817) B994817
theorem B663223 : Blo 662308 663223 := bstep (se 1 (by rfl) ⟨497417, by rfl⟩ : syracuseStep 663223 = 994835) B994835
theorem B663243 : Blo 662308 663243 := bstep (se 1 (by rfl) ⟨497432, by rfl⟩ : syracuseStep 663243 = 994865) B994865
theorem B663255 : Blo 662308 663255 := bstep (se 1 (by rfl) ⟨497441, by rfl⟩ : syracuseStep 663255 = 994883) B994883
theorem B663275 : Blo 662308 663275 := bstep (se 1 (by rfl) ⟨497456, by rfl⟩ : syracuseStep 663275 = 994913) B994913
theorem B663287 : Blo 662308 663287 := bstep (se 1 (by rfl) ⟨497465, by rfl⟩ : syracuseStep 663287 = 994931) B994931
theorem B663307 : Blo 662308 663307 := bstep (se 1 (by rfl) ⟨497480, by rfl⟩ : syracuseStep 663307 = 994961) B994961
theorem B1416971 : Blo 662308 1416971 := bstep (se 1 (by rfl) ⟨1062728, by rfl⟩ : syracuseStep 1416971 = 2125457) B2125457
theorem B1122059 : Blo 662308 1122059 := bstep (se 1 (by rfl) ⟨841544, by rfl⟩ : syracuseStep 1122059 = 1683089) B1683089
theorem B663319 : Blo 662308 663319 := bstep (se 1 (by rfl) ⟨497489, by rfl⟩ : syracuseStep 663319 = 994979) B994979
theorem B663339 : Blo 662308 663339 := bstep (se 1 (by rfl) ⟨497504, by rfl⟩ : syracuseStep 663339 = 995009) B995009
theorem B663351 : Blo 662308 663351 := bstep (se 1 (by rfl) ⟨497513, by rfl⟩ : syracuseStep 663351 = 995027) B995027
theorem B663371 : Blo 662308 663371 := bstep (se 1 (by rfl) ⟨497528, by rfl⟩ : syracuseStep 663371 = 995057) B995057
theorem B1154891 : Blo 662308 1154891 := bstep (se 1 (by rfl) ⟨866168, by rfl⟩ : syracuseStep 1154891 = 1732337) B1732337
theorem B663383 : Blo 662308 663383 := bstep (se 1 (by rfl) ⟨497537, by rfl⟩ : syracuseStep 663383 = 995075) B995075
theorem B663403 : Blo 662308 663403 := bstep (se 1 (by rfl) ⟨497552, by rfl⟩ : syracuseStep 663403 = 995105) B995105
theorem B663415 : Blo 662308 663415 := bstep (se 1 (by rfl) ⟨497561, by rfl⟩ : syracuseStep 663415 = 995123) B995123
theorem B663435 : Blo 662308 663435 := bstep (se 1 (by rfl) ⟨497576, by rfl⟩ : syracuseStep 663435 = 995153) B995153
theorem B1122187 : Blo 662308 1122187 := bstep (se 1 (by rfl) ⟨841640, by rfl⟩ : syracuseStep 1122187 = 1683281) B1683281
theorem B663447 : Blo 662308 663447 := bstep (se 1 (by rfl) ⟨497585, by rfl⟩ : syracuseStep 663447 = 995171) B995171
theorem B663467 : Blo 662308 663467 := bstep (se 1 (by rfl) ⟨497600, by rfl⟩ : syracuseStep 663467 = 995201) B995201
theorem B663479 : Blo 662308 663479 := bstep (se 1 (by rfl) ⟨497609, by rfl⟩ : syracuseStep 663479 = 995219) B995219
theorem B663499 : Blo 662308 663499 := bstep (se 1 (by rfl) ⟨497624, by rfl⟩ : syracuseStep 663499 = 995249) B995249
theorem B663511 : Blo 662308 663511 := bstep (se 1 (by rfl) ⟨497633, by rfl⟩ : syracuseStep 663511 = 995267) B995267
theorem B663531 : Blo 662308 663531 := bstep (se 1 (by rfl) ⟨497648, by rfl⟩ : syracuseStep 663531 = 995297) B995297
theorem B663543 : Blo 662308 663543 := bstep (se 1 (by rfl) ⟨497657, by rfl⟩ : syracuseStep 663543 = 995315) B995315
theorem B663563 : Blo 662308 663563 := bstep (se 1 (by rfl) ⟨497672, by rfl⟩ : syracuseStep 663563 = 995345) B995345
theorem B663575 : Blo 662308 663575 := bstep (se 1 (by rfl) ⟨497681, by rfl⟩ : syracuseStep 663575 = 995363) B995363
theorem B1122329 : Blo 662308 1122329 := bstep (se 2 (by rfl) ⟨420873, by rfl⟩ : syracuseStep 1122329 = 841747) B841747
theorem B663595 : Blo 662308 663595 := bstep (se 1 (by rfl) ⟨497696, by rfl⟩ : syracuseStep 663595 = 995393) B995393
theorem B663607 : Blo 662308 663607 := bstep (se 1 (by rfl) ⟨497705, by rfl⟩ : syracuseStep 663607 = 995411) B995411
theorem B663627 : Blo 662308 663627 := bstep (se 1 (by rfl) ⟨497720, by rfl⟩ : syracuseStep 663627 = 995441) B995441
theorem B663639 : Blo 662308 663639 := bstep (se 1 (by rfl) ⟨497729, by rfl⟩ : syracuseStep 663639 = 995459) B995459
theorem B663659 : Blo 662308 663659 := bstep (se 1 (by rfl) ⟨497744, by rfl⟩ : syracuseStep 663659 = 995489) B995489
theorem B1417331 : Blo 662308 1417331 := bstep (se 1 (by rfl) ⟨1062998, by rfl⟩ : syracuseStep 1417331 = 2125997) B2125997
theorem B663671 : Blo 662308 663671 := bstep (se 1 (by rfl) ⟨497753, by rfl⟩ : syracuseStep 663671 = 995507) B995507
theorem B663691 : Blo 662308 663691 := bstep (se 1 (by rfl) ⟨497768, by rfl⟩ : syracuseStep 663691 = 995537) B995537
theorem B663703 : Blo 662308 663703 := bstep (se 1 (by rfl) ⟨497777, by rfl⟩ : syracuseStep 663703 = 995555) B995555
theorem B1024153 : Blo 662308 1024153 := bstep (se 2 (by rfl) ⟨384057, by rfl⟩ : syracuseStep 1024153 = 768115) B768115
theorem B1122457 : Blo 662308 1122457 := bstep (se 2 (by rfl) ⟨420921, by rfl⟩ : syracuseStep 1122457 = 841843) B841843
theorem B663723 : Blo 662308 663723 := bstep (se 1 (by rfl) ⟨497792, by rfl⟩ : syracuseStep 663723 = 995585) B995585
theorem B663735 : Blo 662308 663735 := bstep (se 1 (by rfl) ⟨497801, by rfl⟩ : syracuseStep 663735 = 995603) B995603
theorem B663755 : Blo 662308 663755 := bstep (se 1 (by rfl) ⟨497816, by rfl⟩ : syracuseStep 663755 = 995633) B995633
theorem B663767 : Blo 662308 663767 := bstep (se 1 (by rfl) ⟨497825, by rfl⟩ : syracuseStep 663767 = 995651) B995651
theorem B663787 : Blo 662308 663787 := bstep (se 1 (by rfl) ⟨497840, by rfl⟩ : syracuseStep 663787 = 995681) B995681
theorem B663799 : Blo 662308 663799 := bstep (se 1 (by rfl) ⟨497849, by rfl⟩ : syracuseStep 663799 = 995699) B995699
theorem B663819 : Blo 662308 663819 := bstep (se 1 (by rfl) ⟨497864, by rfl⟩ : syracuseStep 663819 = 995729) B995729
theorem B663831 : Blo 662308 663831 := bstep (se 1 (by rfl) ⟨497873, by rfl⟩ : syracuseStep 663831 = 995747) B995747
theorem B663851 : Blo 662308 663851 := bstep (se 1 (by rfl) ⟨497888, by rfl⟩ : syracuseStep 663851 = 995777) B995777
theorem B3776813 : Blo 662308 3776813 := bstep (se 3 (by rfl) ⟨708152, by rfl⟩ : syracuseStep 3776813 = 1416305) B1416305
theorem B663863 : Blo 662308 663863 := bstep (se 1 (by rfl) ⟨497897, by rfl⟩ : syracuseStep 663863 = 995795) B995795
theorem B663883 : Blo 662308 663883 := bstep (se 1 (by rfl) ⟨497912, by rfl⟩ : syracuseStep 663883 = 995825) B995825
theorem B663895 : Blo 662308 663895 := bstep (se 1 (by rfl) ⟨497921, by rfl⟩ : syracuseStep 663895 = 995843) B995843
theorem B2695517 : Blo 662308 2695517 := bstep (se 3 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 2695517 = 1010819) B1010819
theorem B663915 : Blo 662308 663915 := bstep (se 1 (by rfl) ⟨497936, by rfl⟩ : syracuseStep 663915 = 995873) B995873
theorem B663927 : Blo 662308 663927 := bstep (se 1 (by rfl) ⟨497945, by rfl⟩ : syracuseStep 663927 = 995891) B995891
theorem B663947 : Blo 662308 663947 := bstep (se 1 (by rfl) ⟨497960, by rfl⟩ : syracuseStep 663947 = 995921) B995921
theorem B663959 : Blo 662308 663959 := bstep (se 1 (by rfl) ⟨497969, by rfl⟩ : syracuseStep 663959 = 995939) B995939
theorem B663979 : Blo 662308 663979 := bstep (se 1 (by rfl) ⟨497984, by rfl⟩ : syracuseStep 663979 = 995969) B995969
theorem B663991 : Blo 662308 663991 := bstep (se 1 (by rfl) ⟨497993, by rfl⟩ : syracuseStep 663991 = 995987) B995987
theorem B664011 : Blo 662308 664011 := bstep (se 1 (by rfl) ⟨498008, by rfl⟩ : syracuseStep 664011 = 996017) B996017
theorem B664023 : Blo 662308 664023 := bstep (se 1 (by rfl) ⟨498017, by rfl⟩ : syracuseStep 664023 = 996035) B996035
theorem B6070745 : Blo 662308 6070745 := bstep (se 2 (by rfl) ⟨2276529, by rfl⟩ : syracuseStep 6070745 = 4553059) B4553059
theorem B664043 : Blo 662308 664043 := bstep (se 1 (by rfl) ⟨498032, by rfl⟩ : syracuseStep 664043 = 996065) B996065
theorem B664055 : Blo 662308 664055 := bstep (se 1 (by rfl) ⟨498041, by rfl⟩ : syracuseStep 664055 = 996083) B996083
theorem B664075 : Blo 662308 664075 := bstep (se 1 (by rfl) ⟨498056, by rfl⟩ : syracuseStep 664075 = 996113) B996113
theorem B664087 : Blo 662308 664087 := bstep (se 1 (by rfl) ⟨498065, by rfl⟩ : syracuseStep 664087 = 996131) B996131
theorem B664107 : Blo 662308 664107 := bstep (se 1 (by rfl) ⟨498080, by rfl⟩ : syracuseStep 664107 = 996161) B996161
theorem B664119 : Blo 662308 664119 := bstep (se 1 (by rfl) ⟨498089, by rfl⟩ : syracuseStep 664119 = 996179) B996179
theorem B2237003 : Blo 662308 2237003 := bstep (se 1 (by rfl) ⟨1677752, by rfl⟩ : syracuseStep 2237003 = 3355505) B3355505
theorem B664139 : Blo 662308 664139 := bstep (se 1 (by rfl) ⟨498104, by rfl⟩ : syracuseStep 664139 = 996209) B996209
theorem B664151 : Blo 662308 664151 := bstep (se 1 (by rfl) ⟨498113, by rfl⟩ : syracuseStep 664151 = 996227) B996227
theorem B664171 : Blo 662308 664171 := bstep (se 1 (by rfl) ⟨498128, by rfl⟩ : syracuseStep 664171 = 996257) B996257
theorem B664183 : Blo 662308 664183 := bstep (se 1 (by rfl) ⟨498137, by rfl⟩ : syracuseStep 664183 = 996275) B996275
theorem B664203 : Blo 662308 664203 := bstep (se 1 (by rfl) ⟨498152, by rfl⟩ : syracuseStep 664203 = 996305) B996305
theorem B10756759 : Blo 662308 10756759 := bstep (se 1 (by rfl) ⟨8067569, by rfl⟩ : syracuseStep 10756759 = 16135139) B16135139
theorem B664215 : Blo 662308 664215 := bstep (se 1 (by rfl) ⟨498161, by rfl⟩ : syracuseStep 664215 = 996323) B996323
theorem B664235 : Blo 662308 664235 := bstep (se 1 (by rfl) ⟨498176, by rfl⟩ : syracuseStep 664235 = 996353) B996353
theorem B664247 : Blo 662308 664247 := bstep (se 1 (by rfl) ⟨498185, by rfl⟩ : syracuseStep 664247 = 996371) B996371
theorem B664267 : Blo 662308 664267 := bstep (se 1 (by rfl) ⟨498200, by rfl⟩ : syracuseStep 664267 = 996401) B996401
theorem B664279 : Blo 662308 664279 := bstep (se 1 (by rfl) ⟨498209, by rfl⟩ : syracuseStep 664279 = 996419) B996419
theorem B1123031 : Blo 662308 1123031 := bstep (se 1 (by rfl) ⟨842273, by rfl⟩ : syracuseStep 1123031 = 1684547) B1684547
theorem B664299 : Blo 662308 664299 := bstep (se 1 (by rfl) ⟨498224, by rfl⟩ : syracuseStep 664299 = 996449) B996449
theorem B664311 : Blo 662308 664311 := bstep (se 1 (by rfl) ⟨498233, by rfl⟩ : syracuseStep 664311 = 996467) B996467
theorem B664331 : Blo 662308 664331 := bstep (se 1 (by rfl) ⟨498248, by rfl⟩ : syracuseStep 664331 = 996497) B996497
theorem B664343 : Blo 662308 664343 := bstep (se 1 (by rfl) ⟨498257, by rfl⟩ : syracuseStep 664343 = 996515) B996515
theorem B664363 : Blo 662308 664363 := bstep (se 1 (by rfl) ⟨498272, by rfl⟩ : syracuseStep 664363 = 996545) B996545
theorem B664375 : Blo 662308 664375 := bstep (se 1 (by rfl) ⟨498281, by rfl⟩ : syracuseStep 664375 = 996563) B996563
theorem B1680203 : Blo 662308 1680203 := bstep (se 1 (by rfl) ⟨1260152, by rfl⟩ : syracuseStep 1680203 = 2520305) B2520305
theorem B664395 : Blo 662308 664395 := bstep (se 1 (by rfl) ⟨498296, by rfl⟩ : syracuseStep 664395 = 996593) B996593
theorem B664407 : Blo 662308 664407 := bstep (se 1 (by rfl) ⟨498305, by rfl⟩ : syracuseStep 664407 = 996611) B996611
theorem B1123159 : Blo 662308 1123159 := bstep (se 1 (by rfl) ⟨842369, by rfl⟩ : syracuseStep 1123159 = 1684739) B1684739
theorem B2237273 : Blo 662308 2237273 := bstep (se 2 (by rfl) ⟨838977, by rfl⟩ : syracuseStep 2237273 = 1677955) B1677955
theorem B664427 : Blo 662308 664427 := bstep (se 1 (by rfl) ⟨498320, by rfl⟩ : syracuseStep 664427 = 996641) B996641
theorem B664439 : Blo 662308 664439 := bstep (se 1 (by rfl) ⟨498329, by rfl⟩ : syracuseStep 664439 = 996659) B996659
theorem B664459 : Blo 662308 664459 := bstep (se 1 (by rfl) ⟨498344, by rfl⟩ : syracuseStep 664459 = 996689) B996689
theorem B664471 : Blo 662308 664471 := bstep (se 1 (by rfl) ⟨498353, by rfl⟩ : syracuseStep 664471 = 996707) B996707
theorem B664491 : Blo 662308 664491 := bstep (se 1 (by rfl) ⟨498368, by rfl⟩ : syracuseStep 664491 = 996737) B996737
theorem B664503 : Blo 662308 664503 := bstep (se 1 (by rfl) ⟨498377, by rfl⟩ : syracuseStep 664503 = 996755) B996755
theorem B664523 : Blo 662308 664523 := bstep (se 1 (by rfl) ⟨498392, by rfl⟩ : syracuseStep 664523 = 996785) B996785
theorem B664535 : Blo 662308 664535 := bstep (se 1 (by rfl) ⟨498401, by rfl⟩ : syracuseStep 664535 = 996803) B996803
theorem B664555 : Blo 662308 664555 := bstep (se 1 (by rfl) ⟨498416, by rfl⟩ : syracuseStep 664555 = 996833) B996833
theorem B664567 : Blo 662308 664567 := bstep (se 1 (by rfl) ⟨498425, by rfl⟩ : syracuseStep 664567 = 996851) B996851
theorem B664587 : Blo 662308 664587 := bstep (se 1 (by rfl) ⟨498440, by rfl⟩ : syracuseStep 664587 = 996881) B996881
theorem B664599 : Blo 662308 664599 := bstep (se 1 (by rfl) ⟨498449, by rfl⟩ : syracuseStep 664599 = 996899) B996899
theorem B664619 : Blo 662308 664619 := bstep (se 1 (by rfl) ⟨498464, by rfl⟩ : syracuseStep 664619 = 996929) B996929
theorem B664631 : Blo 662308 664631 := bstep (se 1 (by rfl) ⟨498473, by rfl⟩ : syracuseStep 664631 = 996947) B996947
theorem B664651 : Blo 662308 664651 := bstep (se 1 (by rfl) ⟨498488, by rfl⟩ : syracuseStep 664651 = 996977) B996977
theorem B664663 : Blo 662308 664663 := bstep (se 1 (by rfl) ⟨498497, by rfl⟩ : syracuseStep 664663 = 996995) B996995
theorem B664683 : Blo 662308 664683 := bstep (se 1 (by rfl) ⟨498512, by rfl⟩ : syracuseStep 664683 = 997025) B997025
theorem B664695 : Blo 662308 664695 := bstep (se 1 (by rfl) ⟨498521, by rfl⟩ : syracuseStep 664695 = 997043) B997043
theorem B664715 : Blo 662308 664715 := bstep (se 1 (by rfl) ⟨498536, by rfl⟩ : syracuseStep 664715 = 997073) B997073
theorem B664727 : Blo 662308 664727 := bstep (se 1 (by rfl) ⟨498545, by rfl⟩ : syracuseStep 664727 = 997091) B997091
theorem B664747 : Blo 662308 664747 := bstep (se 1 (by rfl) ⟨498560, by rfl⟩ : syracuseStep 664747 = 997121) B997121
theorem B664759 : Blo 662308 664759 := bstep (se 1 (by rfl) ⟨498569, by rfl⟩ : syracuseStep 664759 = 997139) B997139
theorem B664779 : Blo 662308 664779 := bstep (se 1 (by rfl) ⟨498584, by rfl⟩ : syracuseStep 664779 = 997169) B997169
theorem B664791 : Blo 662308 664791 := bstep (se 1 (by rfl) ⟨498593, by rfl⟩ : syracuseStep 664791 = 997187) B997187
theorem B2270429 : Blo 662308 2270429 := bstep (se 3 (by rfl) ⟨425705, by rfl⟩ : syracuseStep 2270429 = 851411) B851411
theorem B664811 : Blo 662308 664811 := bstep (se 1 (by rfl) ⟨498608, by rfl⟩ : syracuseStep 664811 = 997217) B997217
theorem B664823 : Blo 662308 664823 := bstep (se 1 (by rfl) ⟨498617, by rfl⟩ : syracuseStep 664823 = 997235) B997235
theorem B664843 : Blo 662308 664843 := bstep (se 1 (by rfl) ⟨498632, by rfl⟩ : syracuseStep 664843 = 997265) B997265
theorem B664855 : Blo 662308 664855 := bstep (se 1 (by rfl) ⟨498641, by rfl⟩ : syracuseStep 664855 = 997283) B997283
theorem B664875 : Blo 662308 664875 := bstep (se 1 (by rfl) ⟨498656, by rfl⟩ : syracuseStep 664875 = 997313) B997313
theorem B664887 : Blo 662308 664887 := bstep (se 1 (by rfl) ⟨498665, by rfl⟩ : syracuseStep 664887 = 997331) B997331
theorem B1516865 : Blo 662308 1516865 := bstep (se 2 (by rfl) ⟨568824, by rfl⟩ : syracuseStep 1516865 = 1137649) B1137649
theorem B664907 : Blo 662308 664907 := bstep (se 1 (by rfl) ⟨498680, by rfl⟩ : syracuseStep 664907 = 997361) B997361
theorem B664919 : Blo 662308 664919 := bstep (se 1 (by rfl) ⟨498689, by rfl⟩ : syracuseStep 664919 = 997379) B997379
theorem B664939 : Blo 662308 664939 := bstep (se 1 (by rfl) ⟨498704, by rfl⟩ : syracuseStep 664939 = 997409) B997409
theorem B664951 : Blo 662308 664951 := bstep (se 1 (by rfl) ⟨498713, by rfl⟩ : syracuseStep 664951 = 997427) B997427
theorem B664971 : Blo 662308 664971 := bstep (se 1 (by rfl) ⟨498728, by rfl⟩ : syracuseStep 664971 = 997457) B997457
theorem B664983 : Blo 662308 664983 := bstep (se 1 (by rfl) ⟨498737, by rfl⟩ : syracuseStep 664983 = 997475) B997475
theorem B665003 : Blo 662308 665003 := bstep (se 1 (by rfl) ⟨498752, by rfl⟩ : syracuseStep 665003 = 997505) B997505
theorem B665015 : Blo 662308 665015 := bstep (se 1 (by rfl) ⟨498761, by rfl⟩ : syracuseStep 665015 = 997523) B997523
theorem B665035 : Blo 662308 665035 := bstep (se 1 (by rfl) ⟨498776, by rfl⟩ : syracuseStep 665035 = 997553) B997553
theorem B1123787 : Blo 662308 1123787 := bstep (se 1 (by rfl) ⟨842840, by rfl⟩ : syracuseStep 1123787 = 1685681) B1685681
theorem B665047 : Blo 662308 665047 := bstep (se 1 (by rfl) ⟨498785, by rfl⟩ : syracuseStep 665047 = 997571) B997571
theorem B665067 : Blo 662308 665067 := bstep (se 1 (by rfl) ⟨498800, by rfl⟩ : syracuseStep 665067 = 997601) B997601
theorem B665079 : Blo 662308 665079 := bstep (se 1 (by rfl) ⟨498809, by rfl⟩ : syracuseStep 665079 = 997619) B997619
theorem B665099 : Blo 662308 665099 := bstep (se 1 (by rfl) ⟨498824, by rfl⟩ : syracuseStep 665099 = 997649) B997649
theorem B2237975 : Blo 662308 2237975 := bstep (se 1 (by rfl) ⟨1678481, by rfl⟩ : syracuseStep 2237975 = 3356963) B3356963
theorem B665111 : Blo 662308 665111 := bstep (se 1 (by rfl) ⟨498833, by rfl⟩ : syracuseStep 665111 = 997667) B997667
theorem B665131 : Blo 662308 665131 := bstep (se 1 (by rfl) ⟨498848, by rfl⟩ : syracuseStep 665131 = 997697) B997697
theorem B665143 : Blo 662308 665143 := bstep (se 1 (by rfl) ⟨498857, by rfl⟩ : syracuseStep 665143 = 997715) B997715
theorem B796235 : Blo 662308 796235 := bstep (se 1 (by rfl) ⟨597176, by rfl⟩ : syracuseStep 796235 = 1194353) B1194353
theorem B665163 : Blo 662308 665163 := bstep (se 1 (by rfl) ⟨498872, by rfl⟩ : syracuseStep 665163 = 997745) B997745
theorem B1123915 : Blo 662308 1123915 := bstep (se 1 (by rfl) ⟨842936, by rfl⟩ : syracuseStep 1123915 = 1685873) B1685873
theorem B665175 : Blo 662308 665175 := bstep (se 1 (by rfl) ⟨498881, by rfl⟩ : syracuseStep 665175 = 997763) B997763
theorem B665195 : Blo 662308 665195 := bstep (se 1 (by rfl) ⟨498896, by rfl⟩ : syracuseStep 665195 = 997793) B997793
theorem B665207 : Blo 662308 665207 := bstep (se 1 (by rfl) ⟨498905, by rfl⟩ : syracuseStep 665207 = 997811) B997811
theorem B665227 : Blo 662308 665227 := bstep (se 1 (by rfl) ⟨498920, by rfl⟩ : syracuseStep 665227 = 997841) B997841
theorem B665239 : Blo 662308 665239 := bstep (se 1 (by rfl) ⟨498929, by rfl⟩ : syracuseStep 665239 = 997859) B997859
theorem B665259 : Blo 662308 665259 := bstep (se 1 (by rfl) ⟨498944, by rfl⟩ : syracuseStep 665259 = 997889) B997889
theorem B665271 : Blo 662308 665271 := bstep (se 1 (by rfl) ⟨498953, by rfl⟩ : syracuseStep 665271 = 997907) B997907
theorem B665291 : Blo 662308 665291 := bstep (se 1 (by rfl) ⟨498968, by rfl⟩ : syracuseStep 665291 = 997937) B997937
theorem B665303 : Blo 662308 665303 := bstep (se 1 (by rfl) ⟨498977, by rfl⟩ : syracuseStep 665303 = 997955) B997955
theorem B1124057 : Blo 662308 1124057 := bstep (se 2 (by rfl) ⟨421521, by rfl⟩ : syracuseStep 1124057 = 843043) B843043
theorem B665323 : Blo 662308 665323 := bstep (se 1 (by rfl) ⟨498992, by rfl⟩ : syracuseStep 665323 = 997985) B997985
theorem B665335 : Blo 662308 665335 := bstep (se 1 (by rfl) ⟨499001, by rfl⟩ : syracuseStep 665335 = 998003) B998003
theorem B665355 : Blo 662308 665355 := bstep (se 1 (by rfl) ⟨499016, by rfl⟩ : syracuseStep 665355 = 998033) B998033
theorem B1681175 : Blo 662308 1681175 := bstep (se 1 (by rfl) ⟨1260881, by rfl⟩ : syracuseStep 1681175 = 2521763) B2521763
theorem B665367 : Blo 662308 665367 := bstep (se 1 (by rfl) ⟨499025, by rfl⟩ : syracuseStep 665367 = 998051) B998051
theorem B665387 : Blo 662308 665387 := bstep (se 1 (by rfl) ⟨499040, by rfl⟩ : syracuseStep 665387 = 998081) B998081
theorem B665399 : Blo 662308 665399 := bstep (se 1 (by rfl) ⟨499049, by rfl⟩ : syracuseStep 665399 = 998099) B998099
theorem B665419 : Blo 662308 665419 := bstep (se 1 (by rfl) ⟨499064, by rfl⟩ : syracuseStep 665419 = 998129) B998129
theorem B665431 : Blo 662308 665431 := bstep (se 1 (by rfl) ⟨499073, by rfl⟩ : syracuseStep 665431 = 998147) B998147
theorem B1124185 : Blo 662308 1124185 := bstep (se 2 (by rfl) ⟨421569, by rfl⟩ : syracuseStep 1124185 = 843139) B843139
theorem B665451 : Blo 662308 665451 := bstep (se 1 (by rfl) ⟨499088, by rfl⟩ : syracuseStep 665451 = 998177) B998177
theorem B665463 : Blo 662308 665463 := bstep (se 1 (by rfl) ⟨499097, by rfl⟩ : syracuseStep 665463 = 998195) B998195
theorem B665483 : Blo 662308 665483 := bstep (se 1 (by rfl) ⟨499112, by rfl⟩ : syracuseStep 665483 = 998225) B998225
theorem B665495 : Blo 662308 665495 := bstep (se 1 (by rfl) ⟨499121, by rfl⟩ : syracuseStep 665495 = 998243) B998243
theorem B665515 : Blo 662308 665515 := bstep (se 1 (by rfl) ⟨499136, by rfl⟩ : syracuseStep 665515 = 998273) B998273
theorem B665527 : Blo 662308 665527 := bstep (se 1 (by rfl) ⟨499145, by rfl⟩ : syracuseStep 665527 = 998291) B998291
theorem B665547 : Blo 662308 665547 := bstep (se 1 (by rfl) ⟨499160, by rfl⟩ : syracuseStep 665547 = 998321) B998321
theorem B665559 : Blo 662308 665559 := bstep (se 1 (by rfl) ⟨499169, by rfl⟩ : syracuseStep 665559 = 998339) B998339
theorem B665579 : Blo 662308 665579 := bstep (se 1 (by rfl) ⟨499184, by rfl⟩ : syracuseStep 665579 = 998369) B998369
theorem B665591 : Blo 662308 665591 := bstep (se 1 (by rfl) ⟨499193, by rfl⟩ : syracuseStep 665591 = 998387) B998387
theorem B665611 : Blo 662308 665611 := bstep (se 1 (by rfl) ⟨499208, by rfl⟩ : syracuseStep 665611 = 998417) B998417
theorem B9578513 : Blo 662308 9578513 := bstep (se 2 (by rfl) ⟨3591942, by rfl⟩ : syracuseStep 9578513 = 7183885) B7183885
theorem B665623 : Blo 662308 665623 := bstep (se 1 (by rfl) ⟨499217, by rfl⟩ : syracuseStep 665623 = 998435) B998435
theorem B665643 : Blo 662308 665643 := bstep (se 1 (by rfl) ⟨499232, by rfl⟩ : syracuseStep 665643 = 998465) B998465
theorem B2238515 : Blo 662308 2238515 := bstep (se 1 (by rfl) ⟨1678886, by rfl⟩ : syracuseStep 2238515 = 3357773) B3357773
theorem B665655 : Blo 662308 665655 := bstep (se 1 (by rfl) ⟨499241, by rfl⟩ : syracuseStep 665655 = 998483) B998483
theorem B3188801 : Blo 662308 3188801 := bstep (se 2 (by rfl) ⟨1195800, by rfl⟩ : syracuseStep 3188801 = 2391601) B2391601
theorem B1419329 : Blo 662308 1419329 := bstep (se 2 (by rfl) ⟨532248, by rfl⟩ : syracuseStep 1419329 = 1064497) B1064497
theorem B665675 : Blo 662308 665675 := bstep (se 1 (by rfl) ⟨499256, by rfl⟩ : syracuseStep 665675 = 998513) B998513
theorem B665687 : Blo 662308 665687 := bstep (se 1 (by rfl) ⟨499265, by rfl⟩ : syracuseStep 665687 = 998531) B998531
theorem B665707 : Blo 662308 665707 := bstep (se 1 (by rfl) ⟨499280, by rfl⟩ : syracuseStep 665707 = 998561) B998561
theorem B665719 : Blo 662308 665719 := bstep (se 1 (by rfl) ⟨499289, by rfl⟩ : syracuseStep 665719 = 998579) B998579
theorem B665739 : Blo 662308 665739 := bstep (se 1 (by rfl) ⟨499304, by rfl⟩ : syracuseStep 665739 = 998609) B998609
theorem B665751 : Blo 662308 665751 := bstep (se 1 (by rfl) ⟨499313, by rfl⟩ : syracuseStep 665751 = 998627) B998627
theorem B665771 : Blo 662308 665771 := bstep (se 1 (by rfl) ⟨499328, by rfl⟩ : syracuseStep 665771 = 998657) B998657
theorem B665783 : Blo 662308 665783 := bstep (se 1 (by rfl) ⟨499337, by rfl⟩ : syracuseStep 665783 = 998675) B998675
theorem B2730187 : Blo 662308 2730187 := bstep (se 1 (by rfl) ⟨2047640, by rfl⟩ : syracuseStep 2730187 = 4095281) B4095281
theorem B665803 : Blo 662308 665803 := bstep (se 1 (by rfl) ⟨499352, by rfl⟩ : syracuseStep 665803 = 998705) B998705
theorem B665815 : Blo 662308 665815 := bstep (se 1 (by rfl) ⟨499361, by rfl⟩ : syracuseStep 665815 = 998723) B998723
theorem B993497 : Blo 662308 993497 := bstep (se 2 (by rfl) ⟨372561, by rfl⟩ : syracuseStep 993497 = 745123) B745123
theorem B665835 : Blo 662308 665835 := bstep (se 1 (by rfl) ⟨499376, by rfl⟩ : syracuseStep 665835 = 998753) B998753
theorem B665847 : Blo 662308 665847 := bstep (se 1 (by rfl) ⟨499385, by rfl⟩ : syracuseStep 665847 = 998771) B998771
theorem B665867 : Blo 662308 665867 := bstep (se 1 (by rfl) ⟨499400, by rfl⟩ : syracuseStep 665867 = 998801) B998801
theorem B665879 : Blo 662308 665879 := bstep (se 1 (by rfl) ⟨499409, by rfl⟩ : syracuseStep 665879 = 998819) B998819
theorem B665899 : Blo 662308 665899 := bstep (se 1 (by rfl) ⟨499424, by rfl⟩ : syracuseStep 665899 = 998849) B998849
theorem B665911 : Blo 662308 665911 := bstep (se 1 (by rfl) ⟨499433, by rfl⟩ : syracuseStep 665911 = 998867) B998867
theorem B2238785 : Blo 662308 2238785 := bstep (se 2 (by rfl) ⟨839544, by rfl⟩ : syracuseStep 2238785 = 1679089) B1679089
theorem B993611 : Blo 662308 993611 := bstep (se 1 (by rfl) ⟨745208, by rfl⟩ : syracuseStep 993611 = 1490417) B1490417
theorem B665931 : Blo 662308 665931 := bstep (se 1 (by rfl) ⟨499448, by rfl⟩ : syracuseStep 665931 = 998897) B998897
theorem B993623 : Blo 662308 993623 := bstep (se 1 (by rfl) ⟨745217, by rfl⟩ : syracuseStep 993623 = 1490435) B1490435
theorem B665943 : Blo 662308 665943 := bstep (se 1 (by rfl) ⟨499457, by rfl⟩ : syracuseStep 665943 = 998915) B998915
theorem B665963 : Blo 662308 665963 := bstep (se 1 (by rfl) ⟨499472, by rfl⟩ : syracuseStep 665963 = 998945) B998945
theorem B665975 : Blo 662308 665975 := bstep (se 1 (by rfl) ⟨499481, by rfl⟩ : syracuseStep 665975 = 998963) B998963
theorem B665995 : Blo 662308 665995 := bstep (se 1 (by rfl) ⟨499496, by rfl⟩ : syracuseStep 665995 = 998993) B998993
theorem B666007 : Blo 662308 666007 := bstep (se 1 (by rfl) ⟨499505, by rfl⟩ : syracuseStep 666007 = 999011) B999011
theorem B993689 : Blo 662308 993689 := bstep (se 2 (by rfl) ⟨372633, by rfl⟩ : syracuseStep 993689 = 745267) B745267
theorem B666027 : Blo 662308 666027 := bstep (se 1 (by rfl) ⟨499520, by rfl⟩ : syracuseStep 666027 = 999041) B999041
theorem B1681843 : Blo 662308 1681843 := bstep (se 1 (by rfl) ⟨1261382, by rfl⟩ : syracuseStep 1681843 = 2522765) B2522765
theorem B666039 : Blo 662308 666039 := bstep (se 1 (by rfl) ⟨499529, by rfl⟩ : syracuseStep 666039 = 999059) B999059
theorem B666059 : Blo 662308 666059 := bstep (se 1 (by rfl) ⟨499544, by rfl⟩ : syracuseStep 666059 = 999089) B999089
theorem B797143 : Blo 662308 797143 := bstep (se 1 (by rfl) ⟨597857, by rfl⟩ : syracuseStep 797143 = 1195715) B1195715
theorem B666071 : Blo 662308 666071 := bstep (se 1 (by rfl) ⟨499553, by rfl⟩ : syracuseStep 666071 = 999107) B999107
theorem B666091 : Blo 662308 666091 := bstep (se 1 (by rfl) ⟨499568, by rfl⟩ : syracuseStep 666091 = 999137) B999137
theorem B666103 : Blo 662308 666103 := bstep (se 1 (by rfl) ⟨499577, by rfl⟩ : syracuseStep 666103 = 999155) B999155
theorem B993803 : Blo 662308 993803 := bstep (se 1 (by rfl) ⟨745352, by rfl⟩ : syracuseStep 993803 = 1490705) B1490705
theorem B666123 : Blo 662308 666123 := bstep (se 1 (by rfl) ⟨499592, by rfl⟩ : syracuseStep 666123 = 999185) B999185
theorem B993815 : Blo 662308 993815 := bstep (se 1 (by rfl) ⟨745361, by rfl⟩ : syracuseStep 993815 = 1490723) B1490723
theorem B666135 : Blo 662308 666135 := bstep (se 1 (by rfl) ⟨499601, by rfl⟩ : syracuseStep 666135 = 999203) B999203
theorem B666155 : Blo 662308 666155 := bstep (se 1 (by rfl) ⟨499616, by rfl⟩ : syracuseStep 666155 = 999233) B999233
theorem B666167 : Blo 662308 666167 := bstep (se 1 (by rfl) ⟨499625, by rfl⟩ : syracuseStep 666167 = 999251) B999251
theorem B1681985 : Blo 662308 1681985 := bstep (se 2 (by rfl) ⟨630744, by rfl⟩ : syracuseStep 1681985 = 1261489) B1261489
theorem B3582539 : Blo 662308 3582539 := bstep (se 1 (by rfl) ⟨2686904, by rfl⟩ : syracuseStep 3582539 = 5373809) B5373809
theorem B666187 : Blo 662308 666187 := bstep (se 1 (by rfl) ⟨499640, by rfl⟩ : syracuseStep 666187 = 999281) B999281
theorem B666199 : Blo 662308 666199 := bstep (se 1 (by rfl) ⟨499649, by rfl⟩ : syracuseStep 666199 = 999299) B999299
theorem B993881 : Blo 662308 993881 := bstep (se 2 (by rfl) ⟨372705, by rfl⟩ : syracuseStep 993881 = 745411) B745411
theorem B3582557 : Blo 662308 3582557 := bstep (se 3 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 3582557 = 1343459) B1343459
theorem B666219 : Blo 662308 666219 := bstep (se 1 (by rfl) ⟨499664, by rfl⟩ : syracuseStep 666219 = 999329) B999329
theorem B666231 : Blo 662308 666231 := bstep (se 1 (by rfl) ⟨499673, by rfl⟩ : syracuseStep 666231 = 999347) B999347
theorem B4532867 : Blo 662308 4532867 := bstep (se 1 (by rfl) ⟨3399650, by rfl⟩ : syracuseStep 4532867 = 6799301) B6799301
theorem B666251 : Blo 662308 666251 := bstep (se 1 (by rfl) ⟨499688, by rfl⟩ : syracuseStep 666251 = 999377) B999377
theorem B9218711 : Blo 662308 9218711 := bstep (se 1 (by rfl) ⟨6914033, by rfl⟩ : syracuseStep 9218711 = 13828067) B13828067
theorem B666263 : Blo 662308 666263 := bstep (se 1 (by rfl) ⟨499697, by rfl⟩ : syracuseStep 666263 = 999395) B999395
theorem B666283 : Blo 662308 666283 := bstep (se 1 (by rfl) ⟨499712, by rfl⟩ : syracuseStep 666283 = 999425) B999425
theorem B666295 : Blo 662308 666295 := bstep (se 1 (by rfl) ⟨499721, by rfl⟩ : syracuseStep 666295 = 999443) B999443
theorem B993995 : Blo 662308 993995 := bstep (se 1 (by rfl) ⟨745496, by rfl⟩ : syracuseStep 993995 = 1490993) B1490993
theorem B994007 : Blo 662308 994007 := bstep (se 1 (by rfl) ⟨745505, by rfl⟩ : syracuseStep 994007 = 1491011) B1491011
theorem B961303 : Blo 662308 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B994073 : Blo 662308 994073 := bstep (se 2 (by rfl) ⟨372777, by rfl⟩ : syracuseStep 994073 = 745555) B745555
theorem B5057315 : Blo 662308 5057315 := bstep (se 1 (by rfl) ⟨3792986, by rfl⟩ : syracuseStep 5057315 = 7585973) B7585973
theorem B2239325 : Blo 662308 2239325 := bstep (se 3 (by rfl) ⟨419873, by rfl⟩ : syracuseStep 2239325 = 839747) B839747
theorem B994187 : Blo 662308 994187 := bstep (se 1 (by rfl) ⟨745640, by rfl⟩ : syracuseStep 994187 = 1491281) B1491281
theorem B994199 : Blo 662308 994199 := bstep (se 1 (by rfl) ⟨745649, by rfl⟩ : syracuseStep 994199 = 1491299) B1491299
theorem B1420183 : Blo 662308 1420183 := bstep (se 1 (by rfl) ⟨1065137, by rfl⟩ : syracuseStep 1420183 = 2130275) B2130275
theorem B3353561 : Blo 662308 3353561 := bstep (se 2 (by rfl) ⟨1257585, by rfl⟩ : syracuseStep 3353561 = 2515171) B2515171
theorem B994265 : Blo 662308 994265 := bstep (se 2 (by rfl) ⟨372849, by rfl⟩ : syracuseStep 994265 = 745699) B745699
theorem B994379 : Blo 662308 994379 := bstep (se 1 (by rfl) ⟨745784, by rfl⟩ : syracuseStep 994379 = 1491569) B1491569
theorem B994391 : Blo 662308 994391 := bstep (se 1 (by rfl) ⟨745793, by rfl⟩ : syracuseStep 994391 = 1491587) B1491587
theorem B4041859 : Blo 662308 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B994457 : Blo 662308 994457 := bstep (se 2 (by rfl) ⟨372921, by rfl⟩ : syracuseStep 994457 = 745843) B745843
theorem B994571 : Blo 662308 994571 := bstep (se 1 (by rfl) ⟨745928, by rfl⟩ : syracuseStep 994571 = 1491857) B1491857
theorem B994583 : Blo 662308 994583 := bstep (se 1 (by rfl) ⟨745937, by rfl⟩ : syracuseStep 994583 = 1491875) B1491875
theorem B994649 : Blo 662308 994649 := bstep (se 2 (by rfl) ⟨372993, by rfl⟩ : syracuseStep 994649 = 745987) B745987
theorem B2305459 : Blo 662308 2305459 := bstep (se 1 (by rfl) ⟨1729094, by rfl⟩ : syracuseStep 2305459 = 3458189) B3458189
theorem B994763 : Blo 662308 994763 := bstep (se 1 (by rfl) ⟨746072, by rfl⟩ : syracuseStep 994763 = 1492145) B1492145
theorem B994775 : Blo 662308 994775 := bstep (se 1 (by rfl) ⟨746081, by rfl⟩ : syracuseStep 994775 = 1492163) B1492163
theorem B994841 : Blo 662308 994841 := bstep (se 2 (by rfl) ⟨373065, by rfl⟩ : syracuseStep 994841 = 746131) B746131
theorem B994955 : Blo 662308 994955 := bstep (se 1 (by rfl) ⟨746216, by rfl⟩ : syracuseStep 994955 = 1492433) B1492433
theorem B3583639 : Blo 662308 3583639 := bstep (se 1 (by rfl) ⟨2687729, by rfl⟩ : syracuseStep 3583639 = 5375459) B5375459
theorem B994967 : Blo 662308 994967 := bstep (se 1 (by rfl) ⟨746225, by rfl⟩ : syracuseStep 994967 = 1492451) B1492451
theorem B995033 : Blo 662308 995033 := bstep (se 2 (by rfl) ⟨373137, by rfl⟩ : syracuseStep 995033 = 746275) B746275
theorem B1683251 : Blo 662308 1683251 := bstep (se 1 (by rfl) ⟨1262438, by rfl⟩ : syracuseStep 1683251 = 2524877) B2524877
theorem B995147 : Blo 662308 995147 := bstep (se 1 (by rfl) ⟨746360, by rfl⟩ : syracuseStep 995147 = 1492721) B1492721
theorem B995159 : Blo 662308 995159 := bstep (se 1 (by rfl) ⟨746369, by rfl⟩ : syracuseStep 995159 = 1492739) B1492739
theorem B3780503 : Blo 662308 3780503 := bstep (se 1 (by rfl) ⟨2835377, by rfl⟩ : syracuseStep 3780503 = 5670755) B5670755
theorem B995225 : Blo 662308 995225 := bstep (se 2 (by rfl) ⟨373209, by rfl⟩ : syracuseStep 995225 = 746419) B746419
theorem B1257419 : Blo 662308 1257419 := bstep (se 1 (by rfl) ⟨943064, by rfl⟩ : syracuseStep 1257419 = 1886129) B1886129
theorem B2240459 : Blo 662308 2240459 := bstep (se 1 (by rfl) ⟨1680344, by rfl⟩ : syracuseStep 2240459 = 3360689) B3360689
theorem B995339 : Blo 662308 995339 := bstep (se 1 (by rfl) ⟨746504, by rfl⟩ : syracuseStep 995339 = 1493009) B1493009
theorem B995351 : Blo 662308 995351 := bstep (se 1 (by rfl) ⟨746513, by rfl⟩ : syracuseStep 995351 = 1493027) B1493027
theorem B1421363 : Blo 662308 1421363 := bstep (se 1 (by rfl) ⟨1066022, by rfl⟩ : syracuseStep 1421363 = 2132045) B2132045
theorem B995417 : Blo 662308 995417 := bstep (se 2 (by rfl) ⟨373281, by rfl⟩ : syracuseStep 995417 = 746563) B746563
theorem B1257601 : Blo 662308 1257601 := bstep (se 2 (by rfl) ⟨471600, by rfl⟩ : syracuseStep 1257601 = 943201) B943201
theorem B995531 : Blo 662308 995531 := bstep (se 1 (by rfl) ⟨746648, by rfl⟩ : syracuseStep 995531 = 1493297) B1493297
theorem B995543 : Blo 662308 995543 := bstep (se 1 (by rfl) ⟨746657, by rfl⟩ : syracuseStep 995543 = 1493315) B1493315
theorem B2240729 : Blo 662308 2240729 := bstep (se 2 (by rfl) ⟨840273, by rfl⟩ : syracuseStep 2240729 = 1680547) B1680547
theorem B3027203 : Blo 662308 3027203 := bstep (se 1 (by rfl) ⟨2270402, by rfl⟩ : syracuseStep 3027203 = 4540805) B4540805
theorem B995609 : Blo 662308 995609 := bstep (se 2 (by rfl) ⟨373353, by rfl⟩ : syracuseStep 995609 = 746707) B746707
theorem B1683787 : Blo 662308 1683787 := bstep (se 1 (by rfl) ⟨1262840, by rfl⟩ : syracuseStep 1683787 = 2525681) B2525681
theorem B995723 : Blo 662308 995723 := bstep (se 1 (by rfl) ⟨746792, by rfl⟩ : syracuseStep 995723 = 1493585) B1493585
theorem B995735 : Blo 662308 995735 := bstep (se 1 (by rfl) ⟨746801, by rfl⟩ : syracuseStep 995735 = 1493603) B1493603
theorem B1257943 : Blo 662308 1257943 := bstep (se 1 (by rfl) ⟨943457, by rfl⟩ : syracuseStep 1257943 = 1886915) B1886915
theorem B995801 : Blo 662308 995801 := bstep (se 2 (by rfl) ⟨373425, by rfl⟩ : syracuseStep 995801 = 746851) B746851
theorem B1683929 : Blo 662308 1683929 := bstep (se 2 (by rfl) ⟨631473, by rfl⟩ : syracuseStep 1683929 = 1262947) B1262947
theorem B22196753 : Blo 662308 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B3355181 : Blo 662308 3355181 := bstep (se 3 (by rfl) ⟨629096, by rfl⟩ : syracuseStep 3355181 = 1258193) B1258193
theorem B995915 : Blo 662308 995915 := bstep (se 1 (by rfl) ⟨746936, by rfl⟩ : syracuseStep 995915 = 1493873) B1493873
theorem B995927 : Blo 662308 995927 := bstep (se 1 (by rfl) ⟨746945, by rfl⟩ : syracuseStep 995927 = 1493891) B1493891
theorem B995993 : Blo 662308 995993 := bstep (se 2 (by rfl) ⟨373497, by rfl⟩ : syracuseStep 995993 = 746995) B746995
theorem B1258163 : Blo 662308 1258163 := bstep (se 1 (by rfl) ⟨943622, by rfl⟩ : syracuseStep 1258163 = 1887245) B1887245
theorem B996107 : Blo 662308 996107 := bstep (se 1 (by rfl) ⟨747080, by rfl⟩ : syracuseStep 996107 = 1494161) B1494161
theorem B996119 : Blo 662308 996119 := bstep (se 1 (by rfl) ⟨747089, by rfl⟩ : syracuseStep 996119 = 1494179) B1494179
theorem B996185 : Blo 662308 996185 := bstep (se 2 (by rfl) ⟨373569, by rfl⟩ : syracuseStep 996185 = 747139) B747139
theorem B1258391 : Blo 662308 1258391 := bstep (se 1 (by rfl) ⟨943793, by rfl⟩ : syracuseStep 1258391 = 1887587) B1887587
theorem B2241431 : Blo 662308 2241431 := bstep (se 1 (by rfl) ⟨1681073, by rfl⟩ : syracuseStep 2241431 = 3362147) B3362147
theorem B996299 : Blo 662308 996299 := bstep (se 1 (by rfl) ⟨747224, by rfl⟩ : syracuseStep 996299 = 1494449) B1494449
theorem B996311 : Blo 662308 996311 := bstep (se 1 (by rfl) ⟨747233, by rfl⟩ : syracuseStep 996311 = 1494467) B1494467
theorem B996377 : Blo 662308 996377 := bstep (se 2 (by rfl) ⟨373641, by rfl⟩ : syracuseStep 996377 = 747283) B747283
theorem B996491 : Blo 662308 996491 := bstep (se 1 (by rfl) ⟨747368, by rfl⟩ : syracuseStep 996491 = 1494737) B1494737
theorem B996503 : Blo 662308 996503 := bstep (se 1 (by rfl) ⟨747377, by rfl⟩ : syracuseStep 996503 = 1494755) B1494755
theorem B1258649 : Blo 662308 1258649 := bstep (se 2 (by rfl) ⟨471993, by rfl⟩ : syracuseStep 1258649 = 943987) B943987
theorem B996569 : Blo 662308 996569 := bstep (se 2 (by rfl) ⟨373713, by rfl⟩ : syracuseStep 996569 = 747427) B747427
theorem B1422593 : Blo 662308 1422593 := bstep (se 2 (by rfl) ⟨533472, by rfl⟩ : syracuseStep 1422593 = 1066945) B1066945
theorem B1684759 : Blo 662308 1684759 := bstep (se 1 (by rfl) ⟨1263569, by rfl⟩ : syracuseStep 1684759 = 2527139) B2527139
theorem B3585325 : Blo 662308 3585325 := bstep (se 3 (by rfl) ⟨672248, by rfl⟩ : syracuseStep 3585325 = 1344497) B1344497
theorem B996683 : Blo 662308 996683 := bstep (se 1 (by rfl) ⟨747512, by rfl⟩ : syracuseStep 996683 = 1495025) B1495025
theorem B996695 : Blo 662308 996695 := bstep (se 1 (by rfl) ⟨747521, by rfl⟩ : syracuseStep 996695 = 1495043) B1495043
theorem B996761 : Blo 662308 996761 := bstep (se 2 (by rfl) ⟨373785, by rfl⟩ : syracuseStep 996761 = 747571) B747571
theorem B2241971 : Blo 662308 2241971 := bstep (se 1 (by rfl) ⟨1681478, by rfl⟩ : syracuseStep 2241971 = 3362957) B3362957
theorem B996875 : Blo 662308 996875 := bstep (se 1 (by rfl) ⟨747656, by rfl⟩ : syracuseStep 996875 = 1495313) B1495313
theorem B996887 : Blo 662308 996887 := bstep (se 1 (by rfl) ⟨747665, by rfl⟩ : syracuseStep 996887 = 1495331) B1495331
theorem B1259059 : Blo 662308 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B996953 : Blo 662308 996953 := bstep (se 2 (by rfl) ⟨373857, by rfl⟩ : syracuseStep 996953 = 747715) B747715
theorem B2242241 : Blo 662308 2242241 := bstep (se 2 (by rfl) ⟨840840, by rfl⟩ : syracuseStep 2242241 = 1681681) B1681681
theorem B997067 : Blo 662308 997067 := bstep (se 1 (by rfl) ⟨747800, by rfl⟩ : syracuseStep 997067 = 1495601) B1495601
theorem B1685195 : Blo 662308 1685195 := bstep (se 1 (by rfl) ⟨1263896, by rfl⟩ : syracuseStep 1685195 = 2527793) B2527793
theorem B997079 : Blo 662308 997079 := bstep (se 1 (by rfl) ⟨747809, by rfl⟩ : syracuseStep 997079 = 1495619) B1495619
theorem B997145 : Blo 662308 997145 := bstep (se 2 (by rfl) ⟨373929, by rfl⟩ : syracuseStep 997145 = 747859) B747859
theorem B5748515 : Blo 662308 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B997259 : Blo 662308 997259 := bstep (se 1 (by rfl) ⟨747944, by rfl⟩ : syracuseStep 997259 = 1495889) B1495889
theorem B997271 : Blo 662308 997271 := bstep (se 1 (by rfl) ⟨747953, by rfl⟩ : syracuseStep 997271 = 1495907) B1495907
theorem B997337 : Blo 662308 997337 := bstep (se 2 (by rfl) ⟨374001, by rfl⟩ : syracuseStep 997337 = 748003) B748003
theorem B899095 : Blo 662308 899095 := bstep (se 1 (by rfl) ⟨674321, by rfl⟩ : syracuseStep 899095 = 1348643) B1348643
theorem B1259545 : Blo 662308 1259545 := bstep (se 2 (by rfl) ⟨472329, by rfl⟩ : syracuseStep 1259545 = 944659) B944659
theorem B1685569 : Blo 662308 1685569 := bstep (se 2 (by rfl) ⟨632088, by rfl⟩ : syracuseStep 1685569 = 1264177) B1264177
theorem B997451 : Blo 662308 997451 := bstep (se 1 (by rfl) ⟨748088, by rfl⟩ : syracuseStep 997451 = 1496177) B1496177
theorem B997463 : Blo 662308 997463 := bstep (se 1 (by rfl) ⟨748097, by rfl⟩ : syracuseStep 997463 = 1496195) B1496195
theorem B997529 : Blo 662308 997529 := bstep (se 2 (by rfl) ⟨374073, by rfl⟩ : syracuseStep 997529 = 748147) B748147
theorem B2242781 : Blo 662308 2242781 := bstep (se 3 (by rfl) ⟨420521, by rfl⟩ : syracuseStep 2242781 = 841043) B841043
theorem B997643 : Blo 662308 997643 := bstep (se 1 (by rfl) ⟨748232, by rfl⟩ : syracuseStep 997643 = 1496465) B1496465
theorem B997655 : Blo 662308 997655 := bstep (se 1 (by rfl) ⟨748241, by rfl⟩ : syracuseStep 997655 = 1496483) B1496483
theorem B997721 : Blo 662308 997721 := bstep (se 2 (by rfl) ⟨374145, by rfl⟩ : syracuseStep 997721 = 748291) B748291
theorem B2832833 : Blo 662308 2832833 := bstep (se 2 (by rfl) ⟨1062312, by rfl⟩ : syracuseStep 2832833 = 2124625) B2124625
theorem B997835 : Blo 662308 997835 := bstep (se 1 (by rfl) ⟨748376, by rfl⟩ : syracuseStep 997835 = 1496753) B1496753
theorem B997847 : Blo 662308 997847 := bstep (se 1 (by rfl) ⟨748385, by rfl⟩ : syracuseStep 997847 = 1496771) B1496771
theorem B2734609 : Blo 662308 2734609 := bstep (se 2 (by rfl) ⟨1025478, by rfl⟩ : syracuseStep 2734609 = 2050957) B2050957
theorem B997913 : Blo 662308 997913 := bstep (se 2 (by rfl) ⟨374217, by rfl⟩ : syracuseStep 997913 = 748435) B748435
theorem B1260107 : Blo 662308 1260107 := bstep (se 1 (by rfl) ⟨945080, by rfl⟩ : syracuseStep 1260107 = 1890161) B1890161
theorem B2832985 : Blo 662308 2832985 := bstep (se 2 (by rfl) ⟨1062369, by rfl⟩ : syracuseStep 2832985 = 2124739) B2124739
theorem B998027 : Blo 662308 998027 := bstep (se 1 (by rfl) ⟨748520, by rfl⟩ : syracuseStep 998027 = 1497041) B1497041
theorem B1194647 : Blo 662308 1194647 := bstep (se 1 (by rfl) ⟨895985, by rfl⟩ : syracuseStep 1194647 = 1791971) B1791971
theorem B998039 : Blo 662308 998039 := bstep (se 1 (by rfl) ⟨748529, by rfl⟩ : syracuseStep 998039 = 1497059) B1497059
theorem B1686167 : Blo 662308 1686167 := bstep (se 1 (by rfl) ⟨1264625, by rfl⟩ : syracuseStep 1686167 = 2529251) B2529251
theorem B998105 : Blo 662308 998105 := bstep (se 2 (by rfl) ⟨374289, by rfl⟩ : syracuseStep 998105 = 748579) B748579
theorem B1260289 : Blo 662308 1260289 := bstep (se 2 (by rfl) ⟨472608, by rfl⟩ : syracuseStep 1260289 = 945217) B945217
theorem B1194763 : Blo 662308 1194763 := bstep (se 1 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 1194763 = 1792145) B1792145
theorem B998219 : Blo 662308 998219 := bstep (se 1 (by rfl) ⟨748664, by rfl⟩ : syracuseStep 998219 = 1497329) B1497329
theorem B998231 : Blo 662308 998231 := bstep (se 1 (by rfl) ⟨748673, by rfl⟩ : syracuseStep 998231 = 1497347) B1497347
theorem B998297 : Blo 662308 998297 := bstep (se 2 (by rfl) ⟨374361, by rfl⟩ : syracuseStep 998297 = 748723) B748723
theorem B998411 : Blo 662308 998411 := bstep (se 1 (by rfl) ⟨748808, by rfl⟩ : syracuseStep 998411 = 1497617) B1497617
theorem B998423 : Blo 662308 998423 := bstep (se 1 (by rfl) ⟨748817, by rfl⟩ : syracuseStep 998423 = 1497635) B1497635
theorem B1457203 : Blo 662308 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B998489 : Blo 662308 998489 := bstep (se 2 (by rfl) ⟨374433, by rfl⟩ : syracuseStep 998489 = 748867) B748867
theorem B998603 : Blo 662308 998603 := bstep (se 1 (by rfl) ⟨748952, by rfl⟩ : syracuseStep 998603 = 1497905) B1497905
theorem B998615 : Blo 662308 998615 := bstep (se 1 (by rfl) ⟨748961, by rfl⟩ : syracuseStep 998615 = 1497923) B1497923
theorem B1064215 : Blo 662308 1064215 := bstep (se 1 (by rfl) ⟨798161, by rfl⟩ : syracuseStep 1064215 = 1596323) B1596323
theorem B1490201 : Blo 662308 1490201 := bstep (se 2 (by rfl) ⟨558825, by rfl⟩ : syracuseStep 1490201 = 1117651) B1117651
theorem B998681 : Blo 662308 998681 := bstep (se 2 (by rfl) ⟨374505, by rfl⟩ : syracuseStep 998681 = 749011) B749011
theorem B4308299 : Blo 662308 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B2243915 : Blo 662308 2243915 := bstep (se 1 (by rfl) ⟨1682936, by rfl⟩ : syracuseStep 2243915 = 3365873) B3365873
theorem B1490291 : Blo 662308 1490291 := bstep (se 1 (by rfl) ⟨1117718, by rfl⟩ : syracuseStep 1490291 = 2235437) B2235437
theorem B998795 : Blo 662308 998795 := bstep (se 1 (by rfl) ⟨749096, by rfl⟩ : syracuseStep 998795 = 1498193) B1498193
theorem B1490327 : Blo 662308 1490327 := bstep (se 1 (by rfl) ⟨1117745, by rfl⟩ : syracuseStep 1490327 = 2235491) B2235491
theorem B1097111 : Blo 662308 1097111 := bstep (se 1 (by rfl) ⟨822833, by rfl⟩ : syracuseStep 1097111 = 1645667) B1645667
theorem B998807 : Blo 662308 998807 := bstep (se 1 (by rfl) ⟨749105, by rfl⟩ : syracuseStep 998807 = 1498211) B1498211
theorem B1261003 : Blo 662308 1261003 := bstep (se 1 (by rfl) ⟨945752, by rfl⟩ : syracuseStep 1261003 = 1891505) B1891505
theorem B998873 : Blo 662308 998873 := bstep (se 2 (by rfl) ⟨374577, by rfl⟩ : syracuseStep 998873 = 749155) B749155
theorem B1261079 : Blo 662308 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B1490507 : Blo 662308 1490507 := bstep (se 1 (by rfl) ⟨1117880, by rfl⟩ : syracuseStep 1490507 = 2235761) B2235761
theorem B998987 : Blo 662308 998987 := bstep (se 1 (by rfl) ⟨749240, by rfl⟩ : syracuseStep 998987 = 1498481) B1498481
theorem B998999 : Blo 662308 998999 := bstep (se 1 (by rfl) ⟨749249, by rfl⟩ : syracuseStep 998999 = 1498499) B1498499
theorem B2244185 : Blo 662308 2244185 := bstep (se 2 (by rfl) ⟨841569, by rfl⟩ : syracuseStep 2244185 = 1683139) B1683139
theorem B1490561 : Blo 662308 1490561 := bstep (se 2 (by rfl) ⟨558960, by rfl⟩ : syracuseStep 1490561 = 1117921) B1117921
theorem B999065 : Blo 662308 999065 := bstep (se 2 (by rfl) ⟨374649, by rfl⟩ : syracuseStep 999065 = 749299) B749299
theorem B999179 : Blo 662308 999179 := bstep (se 1 (by rfl) ⟨749384, by rfl⟩ : syracuseStep 999179 = 1498769) B1498769
theorem B999191 : Blo 662308 999191 := bstep (se 1 (by rfl) ⟨749393, by rfl⟩ : syracuseStep 999191 = 1498787) B1498787
theorem B1490777 : Blo 662308 1490777 := bstep (se 2 (by rfl) ⟨559041, by rfl⟩ : syracuseStep 1490777 = 1118083) B1118083
theorem B999257 : Blo 662308 999257 := bstep (se 2 (by rfl) ⟨374721, by rfl⟩ : syracuseStep 999257 = 749443) B749443
theorem B9715573 : Blo 662308 9715573 := bstep (se 5 (by rfl) ⟨455417, by rfl⟩ : syracuseStep 9715573 = 910835) B910835
theorem B1490867 : Blo 662308 1490867 := bstep (se 1 (by rfl) ⟨1118150, by rfl⟩ : syracuseStep 1490867 = 2236301) B2236301
theorem B999371 : Blo 662308 999371 := bstep (se 1 (by rfl) ⟨749528, by rfl⟩ : syracuseStep 999371 = 1499057) B1499057
theorem B1490903 : Blo 662308 1490903 := bstep (se 1 (by rfl) ⟨1118177, by rfl⟩ : syracuseStep 1490903 = 2236355) B2236355
theorem B999383 : Blo 662308 999383 := bstep (se 1 (by rfl) ⟨749537, by rfl⟩ : syracuseStep 999383 = 1499075) B1499075
theorem B999449 : Blo 662308 999449 := bstep (se 2 (by rfl) ⟨374793, by rfl⟩ : syracuseStep 999449 = 749587) B749587
theorem B1065035 : Blo 662308 1065035 := bstep (se 1 (by rfl) ⟨798776, by rfl⟩ : syracuseStep 1065035 = 1597553) B1597553
theorem B1196147 : Blo 662308 1196147 := bstep (se 1 (by rfl) ⟨897110, by rfl⟩ : syracuseStep 1196147 = 1794221) B1794221
theorem B1491083 : Blo 662308 1491083 := bstep (se 1 (by rfl) ⟨1118312, by rfl⟩ : syracuseStep 1491083 = 2236625) B2236625
theorem B1261747 : Blo 662308 1261747 := bstep (se 1 (by rfl) ⟨946310, by rfl⟩ : syracuseStep 1261747 = 1892621) B1892621
theorem B1491137 : Blo 662308 1491137 := bstep (se 2 (by rfl) ⟨559176, by rfl⟩ : syracuseStep 1491137 = 1118353) B1118353
theorem B5193989 : Blo 662308 5193989 := bstep (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) B973873
theorem B2244887 : Blo 662308 2244887 := bstep (se 1 (by rfl) ⟨1683665, by rfl⟩ : syracuseStep 2244887 = 3367331) B3367331
theorem B1065305 : Blo 662308 1065305 := bstep (se 2 (by rfl) ⟨399489, by rfl⟩ : syracuseStep 1065305 = 798979) B798979
theorem B3359069 : Blo 662308 3359069 := bstep (se 3 (by rfl) ⟨629825, by rfl⟩ : syracuseStep 3359069 = 1259651) B1259651
theorem B1261975 : Blo 662308 1261975 := bstep (se 1 (by rfl) ⟨946481, by rfl⟩ : syracuseStep 1261975 = 1892963) B1892963
theorem B1491353 : Blo 662308 1491353 := bstep (se 2 (by rfl) ⟨559257, by rfl⟩ : syracuseStep 1491353 = 1118515) B1118515
theorem B1491443 : Blo 662308 1491443 := bstep (se 1 (by rfl) ⟨1118582, by rfl⟩ : syracuseStep 1491443 = 2237165) B2237165
theorem B1262081 : Blo 662308 1262081 := bstep (se 2 (by rfl) ⟨473280, by rfl⟩ : syracuseStep 1262081 = 946561) B946561
theorem B1491479 : Blo 662308 1491479 := bstep (se 1 (by rfl) ⟨1118609, by rfl⟩ : syracuseStep 1491479 = 2237219) B2237219
theorem B1262233 : Blo 662308 1262233 := bstep (se 2 (by rfl) ⟨473337, by rfl⟩ : syracuseStep 1262233 = 946675) B946675
theorem B4244147 : Blo 662308 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B1491659 : Blo 662308 1491659 := bstep (se 1 (by rfl) ⟨1118744, by rfl⟩ : syracuseStep 1491659 = 2237489) B2237489
theorem B1491713 : Blo 662308 1491713 := bstep (se 2 (by rfl) ⟨559392, by rfl⟩ : syracuseStep 1491713 = 1118785) B1118785
theorem B2245427 : Blo 662308 2245427 := bstep (se 1 (by rfl) ⟨1684070, by rfl⟩ : syracuseStep 2245427 = 3368141) B3368141
theorem B5391197 : Blo 662308 5391197 := bstep (se 3 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 5391197 = 2021699) B2021699
theorem B1491929 : Blo 662308 1491929 := bstep (se 2 (by rfl) ⟨559473, by rfl⟩ : syracuseStep 1491929 = 1118947) B1118947
theorem B1066009 : Blo 662308 1066009 := bstep (se 2 (by rfl) ⟨399753, by rfl⟩ : syracuseStep 1066009 = 799507) B799507
theorem B1492019 : Blo 662308 1492019 := bstep (se 1 (by rfl) ⟨1119014, by rfl⟩ : syracuseStep 1492019 = 2238029) B2238029
theorem B1197121 : Blo 662308 1197121 := bstep (se 2 (by rfl) ⟨448920, by rfl⟩ : syracuseStep 1197121 = 897841) B897841
theorem B2245697 : Blo 662308 2245697 := bstep (se 2 (by rfl) ⟨842136, by rfl⟩ : syracuseStep 2245697 = 1684273) B1684273
theorem B1492055 : Blo 662308 1492055 := bstep (se 1 (by rfl) ⟨1119041, by rfl⟩ : syracuseStep 1492055 = 2238083) B2238083
theorem B2016407 : Blo 662308 2016407 := bstep (se 1 (by rfl) ⟨1512305, by rfl⟩ : syracuseStep 2016407 = 3024611) B3024611
theorem B3785879 : Blo 662308 3785879 := bstep (se 1 (by rfl) ⟨2839409, by rfl⟩ : syracuseStep 3785879 = 5678819) B5678819
theorem B1492235 : Blo 662308 1492235 := bstep (se 1 (by rfl) ⟨1119176, by rfl⟩ : syracuseStep 1492235 = 2238353) B2238353
theorem B1492289 : Blo 662308 1492289 := bstep (se 2 (by rfl) ⟨559608, by rfl⟩ : syracuseStep 1492289 = 1119217) B1119217
theorem B1492505 : Blo 662308 1492505 := bstep (se 2 (by rfl) ⟨559689, by rfl⟩ : syracuseStep 1492505 = 1119379) B1119379
theorem B2246237 : Blo 662308 2246237 := bstep (se 3 (by rfl) ⟨421169, by rfl⟩ : syracuseStep 2246237 = 842339) B842339
theorem B1492595 : Blo 662308 1492595 := bstep (se 1 (by rfl) ⟨1119446, by rfl⟩ : syracuseStep 1492595 = 2238893) B2238893
theorem B1492631 : Blo 662308 1492631 := bstep (se 1 (by rfl) ⟨1119473, by rfl⟩ : syracuseStep 1492631 = 2238947) B2238947
theorem B1492811 : Blo 662308 1492811 := bstep (se 1 (by rfl) ⟨1119608, by rfl⟩ : syracuseStep 1492811 = 2239217) B2239217
theorem B1492865 : Blo 662308 1492865 := bstep (se 2 (by rfl) ⟨559824, by rfl⟩ : syracuseStep 1492865 = 1119649) B1119649
theorem B1263539 : Blo 662308 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B2836403 : Blo 662308 2836403 := bstep (se 1 (by rfl) ⟨2127302, by rfl⟩ : syracuseStep 2836403 = 4254605) B4254605
theorem B1263691 : Blo 662308 1263691 := bstep (se 1 (by rfl) ⟨947768, by rfl⟩ : syracuseStep 1263691 = 1895537) B1895537
theorem B4868171 : Blo 662308 4868171 := bstep (se 1 (by rfl) ⟨3651128, by rfl⟩ : syracuseStep 4868171 = 7302257) B7302257
theorem B1493081 : Blo 662308 1493081 := bstep (se 2 (by rfl) ⟨559905, by rfl⟩ : syracuseStep 1493081 = 1119811) B1119811
theorem B4245635 : Blo 662308 4245635 := bstep (se 1 (by rfl) ⟨3184226, by rfl⟩ : syracuseStep 4245635 = 6368453) B6368453
theorem B1493171 : Blo 662308 1493171 := bstep (se 1 (by rfl) ⟨1119878, by rfl⟩ : syracuseStep 1493171 = 2239757) B2239757
theorem B1493207 : Blo 662308 1493207 := bstep (se 1 (by rfl) ⟨1119905, by rfl⟩ : syracuseStep 1493207 = 2239811) B2239811
theorem B1493387 : Blo 662308 1493387 := bstep (se 1 (by rfl) ⟨1120040, by rfl⟩ : syracuseStep 1493387 = 2240081) B2240081
theorem B3361175 : Blo 662308 3361175 := bstep (se 1 (by rfl) ⟨2520881, by rfl⟩ : syracuseStep 3361175 = 5041763) B5041763
theorem B1264025 : Blo 662308 1264025 := bstep (se 2 (by rfl) ⟨474009, by rfl⟩ : syracuseStep 1264025 = 948019) B948019
theorem B1493441 : Blo 662308 1493441 := bstep (se 2 (by rfl) ⟨560040, by rfl⟩ : syracuseStep 1493441 = 1120081) B1120081
theorem B1886743 : Blo 662308 1886743 := bstep (se 1 (by rfl) ⟨1415057, by rfl⟩ : syracuseStep 1886743 = 2830115) B2830115
theorem B1493657 : Blo 662308 1493657 := bstep (se 2 (by rfl) ⟨560121, by rfl⟩ : syracuseStep 1493657 = 1120243) B1120243
theorem B2247371 : Blo 662308 2247371 := bstep (se 1 (by rfl) ⟨1685528, by rfl⟩ : syracuseStep 2247371 = 3371057) B3371057
theorem B1493747 : Blo 662308 1493747 := bstep (se 1 (by rfl) ⟨1120310, by rfl⟩ : syracuseStep 1493747 = 2240621) B2240621
theorem B1493783 : Blo 662308 1493783 := bstep (se 1 (by rfl) ⟨1120337, by rfl⟩ : syracuseStep 1493783 = 2240675) B2240675
theorem B9554867 : Blo 662308 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B838603 : Blo 662308 838603 := bstep (se 1 (by rfl) ⟨628952, by rfl⟩ : syracuseStep 838603 = 1257905) B1257905
theorem B1493963 : Blo 662308 1493963 := bstep (se 1 (by rfl) ⟨1120472, by rfl⟩ : syracuseStep 1493963 = 2240945) B2240945
theorem B2247641 : Blo 662308 2247641 := bstep (se 2 (by rfl) ⟨842865, by rfl⟩ : syracuseStep 2247641 = 1685731) B1685731
theorem B707563 : Blo 662308 707563 := bstep (se 1 (by rfl) ⟨530672, by rfl⟩ : syracuseStep 707563 = 1061345) B1061345
theorem B674795 : Blo 662308 674795 := bstep (se 1 (by rfl) ⟨506096, by rfl⟩ : syracuseStep 674795 = 1012193) B1012193
theorem B1494017 : Blo 662308 1494017 := bstep (se 2 (by rfl) ⟨560256, by rfl⟩ : syracuseStep 1494017 = 1120513) B1120513
theorem B3787793 : Blo 662308 3787793 := bstep (se 2 (by rfl) ⟨1420422, by rfl⟩ : syracuseStep 3787793 = 2840845) B2840845
theorem B1264663 : Blo 662308 1264663 := bstep (se 1 (by rfl) ⟨948497, by rfl⟩ : syracuseStep 1264663 = 1896995) B1896995
theorem B1494233 : Blo 662308 1494233 := bstep (se 2 (by rfl) ⟨560337, by rfl⟩ : syracuseStep 1494233 = 1120675) B1120675
theorem B1494323 : Blo 662308 1494323 := bstep (se 1 (by rfl) ⟨1120742, by rfl⟩ : syracuseStep 1494323 = 2241485) B2241485
theorem B1887563 : Blo 662308 1887563 := bstep (se 1 (by rfl) ⟨1415672, by rfl⟩ : syracuseStep 1887563 = 2831345) B2831345
theorem B1494359 : Blo 662308 1494359 := bstep (se 1 (by rfl) ⟨1120769, by rfl⟩ : syracuseStep 1494359 = 2241539) B2241539
theorem B1199603 : Blo 662308 1199603 := bstep (se 1 (by rfl) ⟨899702, by rfl⟩ : syracuseStep 1199603 = 1799405) B1799405
theorem B1494539 : Blo 662308 1494539 := bstep (se 1 (by rfl) ⟨1120904, by rfl⟩ : syracuseStep 1494539 = 2241809) B2241809
theorem B1592855 : Blo 662308 1592855 := bstep (se 1 (by rfl) ⟨1194641, by rfl⟩ : syracuseStep 1592855 = 2389283) B2389283
theorem B1494593 : Blo 662308 1494593 := bstep (se 2 (by rfl) ⟨560472, by rfl⟩ : syracuseStep 1494593 = 1120945) B1120945
theorem B3591773 : Blo 662308 3591773 := bstep (se 3 (by rfl) ⟨673457, by rfl⟩ : syracuseStep 3591773 = 1346915) B1346915
theorem B2248343 : Blo 662308 2248343 := bstep (se 1 (by rfl) ⟨1686257, by rfl⟩ : syracuseStep 2248343 = 3372515) B3372515
theorem B1199809 : Blo 662308 1199809 := bstep (se 2 (by rfl) ⟨449928, by rfl⟩ : syracuseStep 1199809 = 899857) B899857
theorem B7556813 : Blo 662308 7556813 := bstep (se 3 (by rfl) ⟨1416902, by rfl⟩ : syracuseStep 7556813 = 2833805) B2833805
theorem B708311 : Blo 662308 708311 := bstep (se 1 (by rfl) ⟨531233, by rfl⟩ : syracuseStep 708311 = 1062467) B1062467
theorem B1494809 : Blo 662308 1494809 := bstep (se 2 (by rfl) ⟨560553, by rfl⟩ : syracuseStep 1494809 = 1121107) B1121107
theorem B1494899 : Blo 662308 1494899 := bstep (se 1 (by rfl) ⟨1121174, by rfl⟩ : syracuseStep 1494899 = 2242349) B2242349
theorem B839575 : Blo 662308 839575 := bstep (se 1 (by rfl) ⟨629681, by rfl⟩ : syracuseStep 839575 = 1259363) B1259363
theorem B1494935 : Blo 662308 1494935 := bstep (se 1 (by rfl) ⟨1121201, by rfl⟩ : syracuseStep 1494935 = 2242403) B2242403
theorem B1200025 : Blo 662308 1200025 := bstep (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) B900019
theorem B1495115 : Blo 662308 1495115 := bstep (se 1 (by rfl) ⟨1121336, by rfl⟩ : syracuseStep 1495115 = 2242673) B2242673
theorem B1495169 : Blo 662308 1495169 := bstep (se 2 (by rfl) ⟨560688, by rfl⟩ : syracuseStep 1495169 = 1121377) B1121377
theorem B3199297 : Blo 662308 3199297 := bstep (se 2 (by rfl) ⟨1199736, by rfl⟩ : syracuseStep 3199297 = 2399473) B2399473
theorem B1495385 : Blo 662308 1495385 := bstep (se 2 (by rfl) ⟨560769, by rfl⟩ : syracuseStep 1495385 = 1121539) B1121539
theorem B3887461 : Blo 662308 3887461 := bstep (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) B728899
theorem B1200523 : Blo 662308 1200523 := bstep (se 1 (by rfl) ⟨900392, by rfl⟩ : syracuseStep 1200523 = 1800785) B1800785
theorem B1495475 : Blo 662308 1495475 := bstep (se 1 (by rfl) ⟨1121606, by rfl⟩ : syracuseStep 1495475 = 2243213) B2243213
theorem B1495511 : Blo 662308 1495511 := bstep (se 1 (by rfl) ⟨1121633, by rfl⟩ : syracuseStep 1495511 = 2243267) B2243267
theorem B1593931 : Blo 662308 1593931 := bstep (se 1 (by rfl) ⟨1195448, by rfl⟩ : syracuseStep 1593931 = 2390897) B2390897
theorem B2839171 : Blo 662308 2839171 := bstep (se 1 (by rfl) ⟨2129378, by rfl⟩ : syracuseStep 2839171 = 4258757) B4258757
theorem B1495691 : Blo 662308 1495691 := bstep (se 1 (by rfl) ⟨1121768, by rfl⟩ : syracuseStep 1495691 = 2243537) B2243537
theorem B1495745 : Blo 662308 1495745 := bstep (se 2 (by rfl) ⟨560904, by rfl⟩ : syracuseStep 1495745 = 1121809) B1121809
theorem B840395 : Blo 662308 840395 := bstep (se 1 (by rfl) ⟨630296, by rfl⟩ : syracuseStep 840395 = 1260593) B1260593
theorem B1495961 : Blo 662308 1495961 := bstep (se 2 (by rfl) ⟨560985, by rfl⟩ : syracuseStep 1495961 = 1121971) B1121971
theorem B2053043 : Blo 662308 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B1790923 : Blo 662308 1790923 := bstep (se 1 (by rfl) ⟨1343192, by rfl⟩ : syracuseStep 1790923 = 2686385) B2686385
theorem B709579 : Blo 662308 709579 := bstep (se 1 (by rfl) ⟨532184, by rfl⟩ : syracuseStep 709579 = 1064369) B1064369
theorem B1496051 : Blo 662308 1496051 := bstep (se 1 (by rfl) ⟨1122038, by rfl⟩ : syracuseStep 1496051 = 2244077) B2244077
theorem B1496087 : Blo 662308 1496087 := bstep (se 1 (by rfl) ⟨1122065, by rfl⟩ : syracuseStep 1496087 = 2244131) B2244131
theorem B1496267 : Blo 662308 1496267 := bstep (se 1 (by rfl) ⟨1122200, by rfl⟩ : syracuseStep 1496267 = 2244401) B2244401
theorem B1496321 : Blo 662308 1496321 := bstep (se 2 (by rfl) ⟨561120, by rfl⟩ : syracuseStep 1496321 = 1122241) B1122241
theorem B841099 : Blo 662308 841099 := bstep (se 1 (by rfl) ⟨630824, by rfl⟩ : syracuseStep 841099 = 1261649) B1261649
theorem B2151859 : Blo 662308 2151859 := bstep (se 1 (by rfl) ⟨1613894, by rfl⟩ : syracuseStep 2151859 = 3227789) B3227789
theorem B1496537 : Blo 662308 1496537 := bstep (se 2 (by rfl) ⟨561201, by rfl⟩ : syracuseStep 1496537 = 1122403) B1122403
theorem B1496627 : Blo 662308 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B2840129 : Blo 662308 2840129 := bstep (se 2 (by rfl) ⟨1065048, by rfl⟩ : syracuseStep 2840129 = 2130097) B2130097
theorem B1496663 : Blo 662308 1496663 := bstep (se 1 (by rfl) ⟨1122497, by rfl⟩ : syracuseStep 1496663 = 2244995) B2244995
theorem B9557635 : Blo 662308 9557635 := bstep (se 1 (by rfl) ⟨7168226, by rfl⟩ : syracuseStep 9557635 = 14336453) B14336453
theorem B841367 : Blo 662308 841367 := bstep (se 1 (by rfl) ⟨631025, by rfl⟩ : syracuseStep 841367 = 1262051) B1262051
theorem B710327 : Blo 662308 710327 := bstep (se 1 (by rfl) ⟨532745, by rfl⟩ : syracuseStep 710327 = 1065491) B1065491
theorem B1890013 : Blo 662308 1890013 := bstep (se 3 (by rfl) ⟨354377, by rfl⟩ : syracuseStep 1890013 = 708755) B708755
theorem B1496843 : Blo 662308 1496843 := bstep (se 1 (by rfl) ⟨1122632, by rfl⟩ : syracuseStep 1496843 = 2245265) B2245265
theorem B4085569 : Blo 662308 4085569 := bstep (se 2 (by rfl) ⟨1532088, by rfl⟩ : syracuseStep 4085569 = 3064177) B3064177
theorem B1496897 : Blo 662308 1496897 := bstep (se 2 (by rfl) ⟨561336, by rfl⟩ : syracuseStep 1496897 = 1122673) B1122673
theorem B2021213 : Blo 662308 2021213 := bstep (se 3 (by rfl) ⟨378977, by rfl⟩ : syracuseStep 2021213 = 757955) B757955
theorem B3364739 : Blo 662308 3364739 := bstep (se 1 (by rfl) ⟨2523554, by rfl⟩ : syracuseStep 3364739 = 5047109) B5047109
theorem B1595315 : Blo 662308 1595315 := bstep (se 1 (by rfl) ⟨1196486, by rfl⟩ : syracuseStep 1595315 = 2392973) B2392973
theorem B1497113 : Blo 662308 1497113 := bstep (se 2 (by rfl) ⟨561417, by rfl⟩ : syracuseStep 1497113 = 1122835) B1122835
theorem B5658659 : Blo 662308 5658659 := bstep (se 1 (by rfl) ⟨4243994, by rfl⟩ : syracuseStep 5658659 = 8487989) B8487989
theorem B17291339 : Blo 662308 17291339 := bstep (se 1 (by rfl) ⟨12968504, by rfl⟩ : syracuseStep 17291339 = 25937009) B25937009
theorem B1497203 : Blo 662308 1497203 := bstep (se 1 (by rfl) ⟨1122902, by rfl⟩ : syracuseStep 1497203 = 2245805) B2245805
theorem B1497239 : Blo 662308 1497239 := bstep (se 1 (by rfl) ⟨1122929, by rfl⟩ : syracuseStep 1497239 = 2245859) B2245859
theorem B1792307 : Blo 662308 1792307 := bstep (se 1 (by rfl) ⟨1344230, by rfl⟩ : syracuseStep 1792307 = 2688461) B2688461
theorem B1497419 : Blo 662308 1497419 := bstep (se 1 (by rfl) ⟨1123064, by rfl⟩ : syracuseStep 1497419 = 2246129) B2246129
theorem B842071 : Blo 662308 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B1497473 : Blo 662308 1497473 := bstep (se 2 (by rfl) ⟨561552, by rfl⟩ : syracuseStep 1497473 = 1123105) B1123105
theorem B1497689 : Blo 662308 1497689 := bstep (se 2 (by rfl) ⟨561633, by rfl⟩ : syracuseStep 1497689 = 1123267) B1123267
theorem B1497779 : Blo 662308 1497779 := bstep (se 1 (by rfl) ⟨1123334, by rfl⟩ : syracuseStep 1497779 = 2246669) B2246669
theorem B10902197 : Blo 662308 10902197 := bstep (se 5 (by rfl) ⟨511040, by rfl⟩ : syracuseStep 10902197 = 1022081) B1022081
theorem B1497815 : Blo 662308 1497815 := bstep (se 1 (by rfl) ⟨1123361, by rfl⟩ : syracuseStep 1497815 = 2246723) B2246723
theorem B5659409 : Blo 662308 5659409 := bstep (se 2 (by rfl) ⟨2122278, by rfl⟩ : syracuseStep 5659409 = 4244557) B4244557
theorem B1497995 : Blo 662308 1497995 := bstep (se 1 (by rfl) ⟨1123496, by rfl⟩ : syracuseStep 1497995 = 2246993) B2246993
theorem B5397425 : Blo 662308 5397425 := bstep (se 2 (by rfl) ⟨2024034, by rfl⟩ : syracuseStep 5397425 = 4048069) B4048069
theorem B1498049 : Blo 662308 1498049 := bstep (se 2 (by rfl) ⟨561768, by rfl⟩ : syracuseStep 1498049 = 1123537) B1123537
theorem B6904793 : Blo 662308 6904793 := bstep (se 2 (by rfl) ⟨2589297, by rfl⟩ : syracuseStep 6904793 = 5178595) B5178595
theorem B1891289 : Blo 662308 1891289 := bstep (se 2 (by rfl) ⟨709233, by rfl⟩ : syracuseStep 1891289 = 1418467) B1418467
theorem B1498265 : Blo 662308 1498265 := bstep (se 2 (by rfl) ⟨561849, by rfl⟩ : syracuseStep 1498265 = 1123699) B1123699
theorem B2841803 : Blo 662308 2841803 := bstep (se 1 (by rfl) ⟨2131352, by rfl⟩ : syracuseStep 2841803 = 4262705) B4262705
theorem B1498355 : Blo 662308 1498355 := bstep (se 1 (by rfl) ⟨1123766, by rfl⟩ : syracuseStep 1498355 = 2247533) B2247533
theorem B1498391 : Blo 662308 1498391 := bstep (se 1 (by rfl) ⟨1123793, by rfl⟩ : syracuseStep 1498391 = 2247587) B2247587
theorem B1498571 : Blo 662308 1498571 := bstep (se 1 (by rfl) ⟨1123928, by rfl⟩ : syracuseStep 1498571 = 2247857) B2247857
theorem B1498625 : Blo 662308 1498625 := bstep (se 2 (by rfl) ⟨561984, by rfl⟩ : syracuseStep 1498625 = 1123969) B1123969
theorem B1498841 : Blo 662308 1498841 := bstep (se 2 (by rfl) ⟨562065, by rfl⟩ : syracuseStep 1498841 = 1124131) B1124131
theorem B745195 : Blo 662308 745195 := bstep (se 1 (by rfl) ⟨558896, by rfl⟩ : syracuseStep 745195 = 1117793) B1117793
theorem B1498931 : Blo 662308 1498931 := bstep (se 1 (by rfl) ⟨1124198, by rfl⟩ : syracuseStep 1498931 = 2248397) B2248397
theorem B18177857 : Blo 662308 18177857 := bstep (se 2 (by rfl) ⟨6816696, by rfl⟩ : syracuseStep 18177857 = 13633393) B13633393
theorem B6053707 : Blo 662308 6053707 := bstep (se 1 (by rfl) ⟨4540280, by rfl⟩ : syracuseStep 6053707 = 9080561) B9080561
theorem B745303 : Blo 662308 745303 := bstep (se 1 (by rfl) ⟨558977, by rfl⟩ : syracuseStep 745303 = 1117955) B1117955
theorem B1498967 : Blo 662308 1498967 := bstep (se 1 (by rfl) ⟨1124225, by rfl⟩ : syracuseStep 1498967 = 2248451) B2248451
theorem B745483 : Blo 662308 745483 := bstep (se 1 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 745483 = 1118225) B1118225
theorem B1499147 : Blo 662308 1499147 := bstep (se 1 (by rfl) ⟨1124360, by rfl⟩ : syracuseStep 1499147 = 2248721) B2248721
theorem B2514989 : Blo 662308 2514989 := bstep (se 3 (by rfl) ⟨471560, by rfl⟩ : syracuseStep 2514989 = 943121) B943121
theorem B3039277 : Blo 662308 3039277 := bstep (se 3 (by rfl) ⟨569864, by rfl⟩ : syracuseStep 3039277 = 1139729) B1139729
theorem B745591 : Blo 662308 745591 := bstep (se 1 (by rfl) ⟨559193, by rfl⟩ : syracuseStep 745591 = 1118387) B1118387
theorem B1401025 : Blo 662308 1401025 := bstep (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) B1050769
theorem B3793169 : Blo 662308 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B745771 : Blo 662308 745771 := bstep (se 1 (by rfl) ⟨559328, by rfl⟩ : syracuseStep 745771 = 1118657) B1118657
theorem B12312931 : Blo 662308 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B745879 : Blo 662308 745879 := bstep (se 1 (by rfl) ⟨559409, by rfl⟩ : syracuseStep 745879 = 1118819) B1118819
theorem B4252121 : Blo 662308 4252121 := bstep (se 2 (by rfl) ⟨1594545, by rfl⟩ : syracuseStep 4252121 = 3189091) B3189091
theorem B1892929 : Blo 662308 1892929 := bstep (se 2 (by rfl) ⟨709848, by rfl⟩ : syracuseStep 1892929 = 1419697) B1419697
theorem B746059 : Blo 662308 746059 := bstep (se 1 (by rfl) ⟨559544, by rfl⟩ : syracuseStep 746059 = 1119089) B1119089
theorem B2155187 : Blo 662308 2155187 := bstep (se 1 (by rfl) ⟨1616390, by rfl⟩ : syracuseStep 2155187 = 3232781) B3232781
theorem B1794739 : Blo 662308 1794739 := bstep (se 1 (by rfl) ⟨1346054, by rfl⟩ : syracuseStep 1794739 = 2692109) B2692109
theorem B746167 : Blo 662308 746167 := bstep (se 1 (by rfl) ⟨559625, by rfl⟩ : syracuseStep 746167 = 1119251) B1119251
theorem B2122433 : Blo 662308 2122433 := bstep (se 2 (by rfl) ⟨795912, by rfl⟩ : syracuseStep 2122433 = 1591825) B1591825
theorem B3793625 : Blo 662308 3793625 := bstep (se 2 (by rfl) ⟨1422609, by rfl⟩ : syracuseStep 3793625 = 2845219) B2845219
theorem B746347 : Blo 662308 746347 := bstep (se 1 (by rfl) ⟨559760, by rfl⟩ : syracuseStep 746347 = 1119521) B1119521
theorem B746455 : Blo 662308 746455 := bstep (se 1 (by rfl) ⟨559841, by rfl⟩ : syracuseStep 746455 = 1119683) B1119683
theorem B746635 : Blo 662308 746635 := bstep (se 1 (by rfl) ⟨559976, by rfl⟩ : syracuseStep 746635 = 1119953) B1119953
theorem B943321 : Blo 662308 943321 := bstep (se 2 (by rfl) ⟨353745, by rfl⟩ : syracuseStep 943321 = 707491) B707491
theorem B746743 : Blo 662308 746743 := bstep (se 1 (by rfl) ⟨560057, by rfl⟩ : syracuseStep 746743 = 1120115) B1120115
theorem B1795421 : Blo 662308 1795421 := bstep (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) B673283
theorem B746923 : Blo 662308 746923 := bstep (se 1 (by rfl) ⟨560192, by rfl⟩ : syracuseStep 746923 = 1120385) B1120385
theorem B1598899 : Blo 662308 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B2516417 : Blo 662308 2516417 := bstep (se 2 (by rfl) ⟨943656, by rfl⟩ : syracuseStep 2516417 = 1887313) B1887313
theorem B878027 : Blo 662308 878027 := bstep (se 1 (by rfl) ⟨658520, by rfl⟩ : syracuseStep 878027 = 1317041) B1317041
theorem B3368465 : Blo 662308 3368465 := bstep (se 2 (by rfl) ⟨1263174, by rfl⟩ : syracuseStep 3368465 = 2526349) B2526349
theorem B747031 : Blo 662308 747031 := bstep (se 1 (by rfl) ⟨560273, by rfl⟩ : syracuseStep 747031 = 1120547) B1120547
theorem B5662385 : Blo 662308 5662385 := bstep (se 2 (by rfl) ⟨2123394, by rfl⟩ : syracuseStep 5662385 = 4246789) B4246789
theorem B3368627 : Blo 662308 3368627 := bstep (se 1 (by rfl) ⟨2526470, by rfl⟩ : syracuseStep 3368627 = 5052941) B5052941
theorem B747211 : Blo 662308 747211 := bstep (se 1 (by rfl) ⟨560408, by rfl⟩ : syracuseStep 747211 = 1120817) B1120817
theorem B2844467 : Blo 662308 2844467 := bstep (se 1 (by rfl) ⟨2133350, by rfl⟩ : syracuseStep 2844467 = 4266701) B4266701
theorem B747319 : Blo 662308 747319 := bstep (se 1 (by rfl) ⟨560489, by rfl⟩ : syracuseStep 747319 = 1120979) B1120979
theorem B747499 : Blo 662308 747499 := bstep (se 1 (by rfl) ⟨560624, by rfl⟩ : syracuseStep 747499 = 1121249) B1121249
theorem B747607 : Blo 662308 747607 := bstep (se 1 (by rfl) ⟨560705, by rfl⟩ : syracuseStep 747607 = 1121411) B1121411
theorem B5040305 : Blo 662308 5040305 := bstep (se 2 (by rfl) ⟨1890114, by rfl⟩ : syracuseStep 5040305 = 3780229) B3780229
theorem B1894603 : Blo 662308 1894603 := bstep (se 1 (by rfl) ⟨1420952, by rfl⟩ : syracuseStep 1894603 = 2841905) B2841905
theorem B747787 : Blo 662308 747787 := bstep (se 1 (by rfl) ⟨560840, by rfl⟩ : syracuseStep 747787 = 1121681) B1121681
theorem B747895 : Blo 662308 747895 := bstep (se 1 (by rfl) ⟨560921, by rfl⟩ : syracuseStep 747895 = 1121843) B1121843
theorem B6056369 : Blo 662308 6056369 := bstep (se 2 (by rfl) ⟨2271138, by rfl⟩ : syracuseStep 6056369 = 4542277) B4542277
theorem B1894877 : Blo 662308 1894877 := bstep (se 3 (by rfl) ⟨355289, by rfl⟩ : syracuseStep 1894877 = 710579) B710579
theorem B748075 : Blo 662308 748075 := bstep (se 1 (by rfl) ⟨561056, by rfl⟩ : syracuseStep 748075 = 1122113) B1122113
theorem B944779 : Blo 662308 944779 := bstep (se 1 (by rfl) ⟨708584, by rfl⟩ : syracuseStep 944779 = 1417169) B1417169
theorem B5040791 : Blo 662308 5040791 := bstep (se 1 (by rfl) ⟨3780593, by rfl⟩ : syracuseStep 5040791 = 7561187) B7561187
theorem B748183 : Blo 662308 748183 := bstep (se 1 (by rfl) ⟨561137, by rfl⟩ : syracuseStep 748183 = 1122275) B1122275
theorem B748363 : Blo 662308 748363 := bstep (se 1 (by rfl) ⟨561272, by rfl⟩ : syracuseStep 748363 = 1122545) B1122545
theorem B2517905 : Blo 662308 2517905 := bstep (se 2 (by rfl) ⟨944214, by rfl⟩ : syracuseStep 2517905 = 1888429) B1888429
theorem B748471 : Blo 662308 748471 := bstep (se 1 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 748471 = 1122707) B1122707
theorem B2124893 : Blo 662308 2124893 := bstep (se 3 (by rfl) ⟨398417, by rfl⟩ : syracuseStep 2124893 = 796835) B796835
theorem B748651 : Blo 662308 748651 := bstep (se 1 (by rfl) ⟨561488, by rfl⟩ : syracuseStep 748651 = 1122977) B1122977
theorem B748759 : Blo 662308 748759 := bstep (se 1 (by rfl) ⟨561569, by rfl⟩ : syracuseStep 748759 = 1123139) B1123139
theorem B2845955 : Blo 662308 2845955 := bstep (se 1 (by rfl) ⟨2134466, by rfl⟩ : syracuseStep 2845955 = 4268933) B4268933
theorem B2518361 : Blo 662308 2518361 := bstep (se 2 (by rfl) ⟨944385, by rfl⟩ : syracuseStep 2518361 = 1888771) B1888771
theorem B748939 : Blo 662308 748939 := bstep (se 1 (by rfl) ⟨561704, by rfl⟩ : syracuseStep 748939 = 1123409) B1123409
theorem B749047 : Blo 662308 749047 := bstep (se 1 (by rfl) ⟨561785, by rfl⟩ : syracuseStep 749047 = 1123571) B1123571
theorem B2518573 : Blo 662308 2518573 := bstep (se 3 (by rfl) ⟨472232, by rfl⟩ : syracuseStep 2518573 = 944465) B944465
theorem B3370571 : Blo 662308 3370571 := bstep (se 1 (by rfl) ⟨2527928, by rfl⟩ : syracuseStep 3370571 = 5055857) B5055857
theorem B749227 : Blo 662308 749227 := bstep (se 1 (by rfl) ⟨561920, by rfl⟩ : syracuseStep 749227 = 1123841) B1123841
theorem B749335 : Blo 662308 749335 := bstep (se 1 (by rfl) ⟨562001, by rfl⟩ : syracuseStep 749335 = 1124003) B1124003
theorem B946009 : Blo 662308 946009 := bstep (se 2 (by rfl) ⟨354753, by rfl⟩ : syracuseStep 946009 = 709507) B709507
theorem B2518877 : Blo 662308 2518877 := bstep (se 3 (by rfl) ⟨472289, by rfl⟩ : syracuseStep 2518877 = 944579) B944579
theorem B749515 : Blo 662308 749515 := bstep (se 1 (by rfl) ⟨562136, by rfl⟩ : syracuseStep 749515 = 1124273) B1124273
theorem B2551769 : Blo 662308 2551769 := bstep (se 2 (by rfl) ⟨956913, by rfl⟩ : syracuseStep 2551769 = 1913827) B1913827
theorem B7172813 : Blo 662308 7172813 := bstep (se 3 (by rfl) ⟨1344902, by rfl⟩ : syracuseStep 7172813 = 2689805) B2689805
theorem B946903 : Blo 662308 946903 := bstep (se 1 (by rfl) ⟨710177, by rfl⟩ : syracuseStep 946903 = 1420355) B1420355
theorem B1897177 : Blo 662308 1897177 := bstep (se 2 (by rfl) ⟨711441, by rfl⟩ : syracuseStep 1897177 = 1422883) B1422883
theorem B1799347 : Blo 662308 1799347 := bstep (se 1 (by rfl) ⟨1349510, by rfl⟩ : syracuseStep 1799347 = 2699021) B2699021
theorem B2880715 : Blo 662308 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B947467 : Blo 662308 947467 := bstep (se 1 (by rfl) ⟨710600, by rfl⟩ : syracuseStep 947467 = 1421201) B1421201
theorem B2880785 : Blo 662308 2880785 := bstep (se 2 (by rfl) ⟨1080294, by rfl⟩ : syracuseStep 2880785 = 2160589) B2160589
theorem B3372353 : Blo 662308 3372353 := bstep (se 2 (by rfl) ⟨1264632, by rfl⟩ : syracuseStep 3372353 = 2529265) B2529265
theorem B1078679 : Blo 662308 1078679 := bstep (se 1 (by rfl) ⟨809009, by rfl⟩ : syracuseStep 1078679 = 1618019) B1618019
theorem B82900421 : Blo 662308 82900421 := bstep (se 4 (by rfl) ⟨7771914, by rfl⟩ : syracuseStep 82900421 = 15543829) B15543829
theorem B718327 : Blo 662308 718327 := bstep (se 1 (by rfl) ⟨538745, by rfl⟩ : syracuseStep 718327 = 1077491) B1077491
theorem B1210393 : Blo 662308 1210393 := bstep (se 2 (by rfl) ⟨453897, by rfl⟩ : syracuseStep 1210393 = 907795) B907795
theorem B2521475 : Blo 662308 2521475 := bstep (se 1 (by rfl) ⟨1891106, by rfl⟩ : syracuseStep 2521475 = 3782213) B3782213
theorem B2521489 : Blo 662308 2521489 := bstep (se 2 (by rfl) ⟨945558, by rfl⟩ : syracuseStep 2521489 = 1891117) B1891117
theorem B2521793 : Blo 662308 2521793 := bstep (se 2 (by rfl) ⟨945672, by rfl⟩ : syracuseStep 2521793 = 1891345) B1891345
theorem B12155939 : Blo 662308 12155939 := bstep (se 1 (by rfl) ⟨9116954, by rfl⟩ : syracuseStep 12155939 = 18233909) B18233909
theorem B1276993 : Blo 662308 1276993 := bstep (se 2 (by rfl) ⟨478872, by rfl⟩ : syracuseStep 1276993 = 957745) B957745
theorem B19168325 : Blo 662308 19168325 := bstep (se 4 (by rfl) ⟨1797030, by rfl⟩ : syracuseStep 19168325 = 3594061) B3594061
theorem B7568477 : Blo 662308 7568477 := bstep (se 3 (by rfl) ⟨1419089, by rfl⟩ : syracuseStep 7568477 = 2838179) B2838179
theorem B4258909 : Blo 662308 4258909 := bstep (se 3 (by rfl) ⟨798545, by rfl⟩ : syracuseStep 4258909 = 1597091) B1597091
theorem B2522461 : Blo 662308 2522461 := bstep (se 3 (by rfl) ⟨472961, by rfl⟩ : syracuseStep 2522461 = 945923) B945923
theorem B1868033 : Blo 662308 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B16417241 : Blo 662308 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B2523905 : Blo 662308 2523905 := bstep (se 2 (by rfl) ⟨946464, by rfl⟩ : syracuseStep 2523905 = 1892929) B1892929
theorem B1344271 : Blo 662308 1344271 := bstep (se 1 (by rfl) ⟨1008203, by rfl⟩ : syracuseStep 1344271 = 2016407) B2016407
theorem B2523919 : Blo 662308 2523919 := bstep (se 1 (by rfl) ⟨1892939, by rfl⟩ : syracuseStep 2523919 = 3785879) B3785879
theorem B2392985 : Blo 662308 2392985 := bstep (se 2 (by rfl) ⟨897369, by rfl⟩ : syracuseStep 2392985 = 1794739) B1794739
theorem B1705079 : Blo 662308 1705079 := bstep (se 1 (by rfl) ⟨1278809, by rfl⟩ : syracuseStep 1705079 = 2557619) B2557619
theorem B16188653 : Blo 662308 16188653 := bstep (se 3 (by rfl) ⟨3035372, by rfl⟩ : syracuseStep 16188653 = 6070745) B6070745
theorem B6391133 : Blo 662308 6391133 := bstep (se 3 (by rfl) ⟨1198337, by rfl⟩ : syracuseStep 6391133 = 2396675) B2396675
theorem B3245447 : Blo 662308 3245447 := bstep (se 1 (by rfl) ⟨2434085, by rfl⟩ : syracuseStep 3245447 = 4868171) B4868171
theorem B2131865 : Blo 662308 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B2525195 : Blo 662308 2525195 := bstep (se 1 (by rfl) ⟨1893896, by rfl⟩ : syracuseStep 2525195 = 3787793) B3787793
theorem B4786199 : Blo 662308 4786199 := bstep (se 1 (by rfl) ⟨3589649, by rfl⟩ : syracuseStep 4786199 = 7179299) B7179299
theorem B2394515 : Blo 662308 2394515 := bstep (se 1 (by rfl) ⟨1795886, by rfl⟩ : syracuseStep 2394515 = 3591773) B3591773
theorem B3640249 : Blo 662308 3640249 := bstep (se 2 (by rfl) ⟨1365093, by rfl⟩ : syracuseStep 3640249 = 2730187) B2730187
theorem B2526137 : Blo 662308 2526137 := bstep (se 2 (by rfl) ⟨947301, by rfl⟩ : syracuseStep 2526137 = 1894603) B1894603
theorem B1117739 : Blo 662308 1117739 := bstep (se 1 (by rfl) ⟨838304, by rfl⟩ : syracuseStep 1117739 = 1676609) B1676609
theorem B1281737 : Blo 662308 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B1347475 : Blo 662308 1347475 := bstep (se 1 (by rfl) ⟨1010606, by rfl⟩ : syracuseStep 1347475 = 2021213) B2021213
theorem B1118137 : Blo 662308 1118137 := bstep (se 2 (by rfl) ⟨419301, by rfl⟩ : syracuseStep 1118137 = 838603) B838603
theorem B3772439 : Blo 662308 3772439 := bstep (se 1 (by rfl) ⟨2829329, by rfl⟩ : syracuseStep 3772439 = 5658659) B5658659
theorem B3772939 : Blo 662308 3772939 := bstep (se 1 (by rfl) ⟨2829704, by rfl⟩ : syracuseStep 3772939 = 5659409) B5659409
theorem B1118839 : Blo 662308 1118839 := bstep (se 1 (by rfl) ⟨839129, by rfl⟩ : syracuseStep 1118839 = 1678259) B1678259
theorem B7574309 : Blo 662308 7574309 := bstep (se 4 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 7574309 = 1420183) B1420183
theorem B1119035 : Blo 662308 1119035 := bstep (se 1 (by rfl) ⟨839276, by rfl⟩ : syracuseStep 1119035 = 1678553) B1678553
theorem B1119433 : Blo 662308 1119433 := bstep (se 2 (by rfl) ⟨419787, by rfl⟩ : syracuseStep 1119433 = 839575) B839575
theorem B1676659 : Blo 662308 1676659 := bstep (se 1 (by rfl) ⟨1257494, by rfl⟩ : syracuseStep 1676659 = 2514989) B2514989
theorem B1709513 : Blo 662308 1709513 := bstep (se 2 (by rfl) ⟨641067, by rfl⟩ : syracuseStep 1709513 = 1282135) B1282135
theorem B1676801 : Blo 662308 1676801 := bstep (se 2 (by rfl) ⟨628800, by rfl⟩ : syracuseStep 1676801 = 1257601) B1257601
theorem B2528779 : Blo 662308 2528779 := bstep (se 1 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 2528779 = 3793169) B3793169
theorem B4265729 : Blo 662308 4265729 := bstep (se 2 (by rfl) ⟨1599648, by rfl⟩ : syracuseStep 4265729 = 3199297) B3199297
theorem B1414955 : Blo 662308 1414955 := bstep (se 1 (by rfl) ⟨1061216, by rfl⟩ : syracuseStep 1414955 = 2122433) B2122433
theorem B5183281 : Blo 662308 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B2529083 : Blo 662308 2529083 := bstep (se 1 (by rfl) ⟨1896812, by rfl⟩ : syracuseStep 2529083 = 3793625) B3793625
theorem B1120135 : Blo 662308 1120135 := bstep (se 1 (by rfl) ⟨840101, by rfl⟩ : syracuseStep 1120135 = 1680203) B1680203
theorem B1677257 : Blo 662308 1677257 := bstep (se 2 (by rfl) ⟨628971, by rfl⟩ : syracuseStep 1677257 = 1257943) B1257943
theorem B1513619 : Blo 662308 1513619 := bstep (se 1 (by rfl) ⟨1135214, by rfl⟩ : syracuseStep 1513619 = 2270429) B2270429
theorem B2529569 : Blo 662308 2529569 := bstep (se 2 (by rfl) ⟨948588, by rfl⟩ : syracuseStep 2529569 = 1897177) B1897177
theorem B1677611 : Blo 662308 1677611 := bstep (se 1 (by rfl) ⟨1258208, by rfl⟩ : syracuseStep 1677611 = 2516417) B2516417
theorem B3774923 : Blo 662308 3774923 := bstep (se 1 (by rfl) ⟨2831192, by rfl⟩ : syracuseStep 3774923 = 5662385) B5662385
theorem B1120783 : Blo 662308 1120783 := bstep (se 1 (by rfl) ⟨840587, by rfl⟩ : syracuseStep 1120783 = 1681175) B1681175
theorem B662331 : Blo 662308 662331 := bstep (se 1 (by rfl) ⟨496748, by rfl⟩ : syracuseStep 662331 = 993497) B993497
theorem B662407 : Blo 662308 662407 := bstep (se 1 (by rfl) ⟨496805, by rfl⟩ : syracuseStep 662407 = 993611) B993611
theorem B662415 : Blo 662308 662415 := bstep (se 1 (by rfl) ⟨496811, by rfl⟩ : syracuseStep 662415 = 993623) B993623
theorem B2399129 : Blo 662308 2399129 := bstep (se 2 (by rfl) ⟨899673, by rfl⟩ : syracuseStep 2399129 = 1799347) B1799347
theorem B3840953 : Blo 662308 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B662459 : Blo 662308 662459 := bstep (se 1 (by rfl) ⟨496844, by rfl⟩ : syracuseStep 662459 = 993689) B993689
theorem B4037579 : Blo 662308 4037579 := bstep (se 1 (by rfl) ⟨3028184, by rfl⟩ : syracuseStep 4037579 = 6056369) B6056369
theorem B662535 : Blo 662308 662535 := bstep (se 1 (by rfl) ⟨496901, by rfl⟩ : syracuseStep 662535 = 993803) B993803
theorem B662543 : Blo 662308 662543 := bstep (se 1 (by rfl) ⟨496907, by rfl⟩ : syracuseStep 662543 = 993815) B993815
theorem B1121323 : Blo 662308 1121323 := bstep (se 1 (by rfl) ⟨840992, by rfl⟩ : syracuseStep 1121323 = 1681985) B1681985
theorem B662587 : Blo 662308 662587 := bstep (se 1 (by rfl) ⟨496940, by rfl⟩ : syracuseStep 662587 = 993881) B993881
theorem B3185725 : Blo 662308 3185725 := bstep (se 3 (by rfl) ⟨597323, by rfl⟩ : syracuseStep 3185725 = 1194647) B1194647
theorem B3021911 : Blo 662308 3021911 := bstep (se 1 (by rfl) ⟨2266433, by rfl⟩ : syracuseStep 3021911 = 4532867) B4532867
theorem B662663 : Blo 662308 662663 := bstep (se 1 (by rfl) ⟨496997, by rfl⟩ : syracuseStep 662663 = 993995) B993995
theorem B662671 : Blo 662308 662671 := bstep (se 1 (by rfl) ⟨497003, by rfl⟩ : syracuseStep 662671 = 994007) B994007
theorem B1121465 : Blo 662308 1121465 := bstep (se 2 (by rfl) ⟨420549, by rfl⟩ : syracuseStep 1121465 = 841099) B841099
theorem B662715 : Blo 662308 662715 := bstep (se 1 (by rfl) ⟨497036, by rfl⟩ : syracuseStep 662715 = 994073) B994073
theorem B662791 : Blo 662308 662791 := bstep (se 1 (by rfl) ⟨497093, by rfl⟩ : syracuseStep 662791 = 994187) B994187
theorem B1678603 : Blo 662308 1678603 := bstep (se 1 (by rfl) ⟨1258952, by rfl⟩ : syracuseStep 1678603 = 2517905) B2517905
theorem B662799 : Blo 662308 662799 := bstep (se 1 (by rfl) ⟨497099, by rfl⟩ : syracuseStep 662799 = 994199) B994199
theorem B2235707 : Blo 662308 2235707 := bstep (se 1 (by rfl) ⟨1676780, by rfl⟩ : syracuseStep 2235707 = 3353561) B3353561
theorem B662843 : Blo 662308 662843 := bstep (se 1 (by rfl) ⟨497132, by rfl⟩ : syracuseStep 662843 = 994265) B994265
theorem B662919 : Blo 662308 662919 := bstep (se 1 (by rfl) ⟨497189, by rfl⟩ : syracuseStep 662919 = 994379) B994379
theorem B662927 : Blo 662308 662927 := bstep (se 1 (by rfl) ⟨497195, by rfl⟩ : syracuseStep 662927 = 994391) B994391
theorem B1678745 : Blo 662308 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B662971 : Blo 662308 662971 := bstep (se 1 (by rfl) ⟨497228, by rfl⟩ : syracuseStep 662971 = 994457) B994457
theorem B663047 : Blo 662308 663047 := bstep (se 1 (by rfl) ⟨497285, by rfl⟩ : syracuseStep 663047 = 994571) B994571
theorem B663055 : Blo 662308 663055 := bstep (se 1 (by rfl) ⟨497291, by rfl⟩ : syracuseStep 663055 = 994583) B994583
theorem B663099 : Blo 662308 663099 := bstep (se 1 (by rfl) ⟨497324, by rfl⟩ : syracuseStep 663099 = 994649) B994649
theorem B1678907 : Blo 662308 1678907 := bstep (se 1 (by rfl) ⟨1259180, by rfl⟩ : syracuseStep 1678907 = 2518361) B2518361
theorem B663175 : Blo 662308 663175 := bstep (se 1 (by rfl) ⟨497381, by rfl⟩ : syracuseStep 663175 = 994763) B994763
theorem B663183 : Blo 662308 663183 := bstep (se 1 (by rfl) ⟨497387, by rfl⟩ : syracuseStep 663183 = 994775) B994775
theorem B663227 : Blo 662308 663227 := bstep (se 1 (by rfl) ⟨497420, by rfl⟩ : syracuseStep 663227 = 994841) B994841
theorem B5447425 : Blo 662308 5447425 := bstep (se 2 (by rfl) ⟨2042784, by rfl⟩ : syracuseStep 5447425 = 4085569) B4085569
theorem B663303 : Blo 662308 663303 := bstep (se 1 (by rfl) ⟨497477, by rfl⟩ : syracuseStep 663303 = 994955) B994955
theorem B663311 : Blo 662308 663311 := bstep (se 1 (by rfl) ⟨497483, by rfl⟩ : syracuseStep 663311 = 994967) B994967
theorem B2236193 : Blo 662308 2236193 := bstep (se 2 (by rfl) ⟨838572, by rfl⟩ : syracuseStep 2236193 = 1677145) B1677145
theorem B5119793 : Blo 662308 5119793 := bstep (se 2 (by rfl) ⟨1919922, by rfl⟩ : syracuseStep 5119793 = 3839845) B3839845
theorem B663355 : Blo 662308 663355 := bstep (se 1 (by rfl) ⟨497516, by rfl⟩ : syracuseStep 663355 = 995033) B995033
theorem B1122167 : Blo 662308 1122167 := bstep (se 1 (by rfl) ⟨841625, by rfl⟩ : syracuseStep 1122167 = 1683251) B1683251
theorem B663431 : Blo 662308 663431 := bstep (se 1 (by rfl) ⟨497573, by rfl⟩ : syracuseStep 663431 = 995147) B995147
theorem B663439 : Blo 662308 663439 := bstep (se 1 (by rfl) ⟨497579, by rfl⟩ : syracuseStep 663439 = 995159) B995159
theorem B1679251 : Blo 662308 1679251 := bstep (se 1 (by rfl) ⟨1259438, by rfl⟩ : syracuseStep 1679251 = 2518877) B2518877
theorem B663483 : Blo 662308 663483 := bstep (se 1 (by rfl) ⟨497612, by rfl⟩ : syracuseStep 663483 = 995225) B995225
theorem B663559 : Blo 662308 663559 := bstep (se 1 (by rfl) ⟨497669, by rfl⟩ : syracuseStep 663559 = 995339) B995339
theorem B663567 : Blo 662308 663567 := bstep (se 1 (by rfl) ⟨497675, by rfl⟩ : syracuseStep 663567 = 995351) B995351
theorem B1613857 : Blo 662308 1613857 := bstep (se 2 (by rfl) ⟨605196, by rfl⟩ : syracuseStep 1613857 = 1210393) B1210393
theorem B1679393 : Blo 662308 1679393 := bstep (se 2 (by rfl) ⟨629772, by rfl⟩ : syracuseStep 1679393 = 1259545) B1259545
theorem B663611 : Blo 662308 663611 := bstep (se 1 (by rfl) ⟨497708, by rfl⟩ : syracuseStep 663611 = 995417) B995417
theorem B663687 : Blo 662308 663687 := bstep (se 1 (by rfl) ⟨497765, by rfl⟩ : syracuseStep 663687 = 995531) B995531
theorem B663695 : Blo 662308 663695 := bstep (se 1 (by rfl) ⟨497771, by rfl⟩ : syracuseStep 663695 = 995543) B995543
theorem B663739 : Blo 662308 663739 := bstep (se 1 (by rfl) ⟨497804, by rfl⟩ : syracuseStep 663739 = 995609) B995609
theorem B663815 : Blo 662308 663815 := bstep (se 1 (by rfl) ⟨497861, by rfl⟩ : syracuseStep 663815 = 995723) B995723
theorem B663823 : Blo 662308 663823 := bstep (se 1 (by rfl) ⟨497867, by rfl⟩ : syracuseStep 663823 = 995735) B995735
theorem B663867 : Blo 662308 663867 := bstep (se 1 (by rfl) ⟨497900, by rfl⟩ : syracuseStep 663867 = 995801) B995801
theorem B1122619 : Blo 662308 1122619 := bstep (se 1 (by rfl) ⟨841964, by rfl⟩ : syracuseStep 1122619 = 1683929) B1683929
theorem B2236787 : Blo 662308 2236787 := bstep (se 1 (by rfl) ⟨1677590, by rfl⟩ : syracuseStep 2236787 = 3355181) B3355181
theorem B663943 : Blo 662308 663943 := bstep (se 1 (by rfl) ⟨497957, by rfl⟩ : syracuseStep 663943 = 995915) B995915
theorem B663951 : Blo 662308 663951 := bstep (se 1 (by rfl) ⟨497963, by rfl⟩ : syracuseStep 663951 = 995927) B995927
theorem B663995 : Blo 662308 663995 := bstep (se 1 (by rfl) ⟨497996, by rfl⟩ : syracuseStep 663995 = 995993) B995993
theorem B1122761 : Blo 662308 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B664071 : Blo 662308 664071 := bstep (se 1 (by rfl) ⟨498053, by rfl⟩ : syracuseStep 664071 = 996107) B996107
theorem B664079 : Blo 662308 664079 := bstep (se 1 (by rfl) ⟨498059, by rfl⟩ : syracuseStep 664079 = 996119) B996119
theorem B664123 : Blo 662308 664123 := bstep (se 1 (by rfl) ⟨498092, by rfl⟩ : syracuseStep 664123 = 996185) B996185
theorem B664199 : Blo 662308 664199 := bstep (se 1 (by rfl) ⟨498149, by rfl⟩ : syracuseStep 664199 = 996299) B996299
theorem B664207 : Blo 662308 664207 := bstep (se 1 (by rfl) ⟨498155, by rfl⟩ : syracuseStep 664207 = 996311) B996311
theorem B664251 : Blo 662308 664251 := bstep (se 1 (by rfl) ⟨498188, by rfl⟩ : syracuseStep 664251 = 996377) B996377
theorem B3646145 : Blo 662308 3646145 := bstep (se 2 (by rfl) ⟨1367304, by rfl⟩ : syracuseStep 3646145 = 2734609) B2734609
theorem B664327 : Blo 662308 664327 := bstep (se 1 (by rfl) ⟨498245, by rfl⟩ : syracuseStep 664327 = 996491) B996491
theorem B664335 : Blo 662308 664335 := bstep (se 1 (by rfl) ⟨498251, by rfl⟩ : syracuseStep 664335 = 996503) B996503
theorem B3777313 : Blo 662308 3777313 := bstep (se 2 (by rfl) ⟨1416492, by rfl⟩ : syracuseStep 3777313 = 2832985) B2832985
theorem B664379 : Blo 662308 664379 := bstep (se 1 (by rfl) ⟨498284, by rfl⟩ : syracuseStep 664379 = 996569) B996569
theorem B664455 : Blo 662308 664455 := bstep (se 1 (by rfl) ⟨498341, by rfl⟩ : syracuseStep 664455 = 996683) B996683
theorem B664463 : Blo 662308 664463 := bstep (se 1 (by rfl) ⟨498347, by rfl⟩ : syracuseStep 664463 = 996695) B996695
theorem B664507 : Blo 662308 664507 := bstep (se 1 (by rfl) ⟨498380, by rfl⟩ : syracuseStep 664507 = 996761) B996761
theorem B1680385 : Blo 662308 1680385 := bstep (se 2 (by rfl) ⟨630144, by rfl⟩ : syracuseStep 1680385 = 1260289) B1260289
theorem B664583 : Blo 662308 664583 := bstep (se 1 (by rfl) ⟨498437, by rfl⟩ : syracuseStep 664583 = 996875) B996875
theorem B664591 : Blo 662308 664591 := bstep (se 1 (by rfl) ⟨498443, by rfl⟩ : syracuseStep 664591 = 996887) B996887
theorem B664635 : Blo 662308 664635 := bstep (se 1 (by rfl) ⟨498476, by rfl⟩ : syracuseStep 664635 = 996953) B996953
theorem B2925629 : Blo 662308 2925629 := bstep (se 3 (by rfl) ⟨548555, by rfl⟩ : syracuseStep 2925629 = 1097111) B1097111
theorem B664711 : Blo 662308 664711 := bstep (se 1 (by rfl) ⟨498533, by rfl⟩ : syracuseStep 664711 = 997067) B997067
theorem B1123463 : Blo 662308 1123463 := bstep (se 1 (by rfl) ⟨842597, by rfl⟩ : syracuseStep 1123463 = 1685195) B1685195
theorem B664719 : Blo 662308 664719 := bstep (se 1 (by rfl) ⟨498539, by rfl⟩ : syracuseStep 664719 = 997079) B997079
theorem B664763 : Blo 662308 664763 := bstep (se 1 (by rfl) ⟨498572, by rfl⟩ : syracuseStep 664763 = 997145) B997145
theorem B664839 : Blo 662308 664839 := bstep (se 1 (by rfl) ⟨498629, by rfl⟩ : syracuseStep 664839 = 997259) B997259
theorem B664847 : Blo 662308 664847 := bstep (se 1 (by rfl) ⟨498635, by rfl⟩ : syracuseStep 664847 = 997271) B997271
theorem B664891 : Blo 662308 664891 := bstep (se 1 (by rfl) ⟨498668, by rfl⟩ : syracuseStep 664891 = 997337) B997337
theorem B664967 : Blo 662308 664967 := bstep (se 1 (by rfl) ⟨498725, by rfl⟩ : syracuseStep 664967 = 997451) B997451
theorem B664975 : Blo 662308 664975 := bstep (se 1 (by rfl) ⟨498731, by rfl⟩ : syracuseStep 664975 = 997463) B997463
theorem B1942937 : Blo 662308 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B665019 : Blo 662308 665019 := bstep (se 1 (by rfl) ⟨498764, by rfl⟩ : syracuseStep 665019 = 997529) B997529
theorem B5678545 : Blo 662308 5678545 := bstep (se 2 (by rfl) ⟨2129454, by rfl⟩ : syracuseStep 5678545 = 4258909) B4258909
theorem B665095 : Blo 662308 665095 := bstep (se 1 (by rfl) ⟨498821, by rfl⟩ : syracuseStep 665095 = 997643) B997643
theorem B665103 : Blo 662308 665103 := bstep (se 1 (by rfl) ⟨498827, by rfl⟩ : syracuseStep 665103 = 997655) B997655
theorem B665147 : Blo 662308 665147 := bstep (se 1 (by rfl) ⟨498860, by rfl⟩ : syracuseStep 665147 = 997721) B997721
theorem B1680983 : Blo 662308 1680983 := bstep (se 1 (by rfl) ⟨1260737, by rfl⟩ : syracuseStep 1680983 = 2521475) B2521475
theorem B665223 : Blo 662308 665223 := bstep (se 1 (by rfl) ⟨498917, by rfl⟩ : syracuseStep 665223 = 997835) B997835
theorem B665231 : Blo 662308 665231 := bstep (se 1 (by rfl) ⟨498923, by rfl⟩ : syracuseStep 665231 = 997847) B997847
theorem B665275 : Blo 662308 665275 := bstep (se 1 (by rfl) ⟨498956, by rfl⟩ : syracuseStep 665275 = 997913) B997913
theorem B1418953 : Blo 662308 1418953 := bstep (se 2 (by rfl) ⟨532107, by rfl⟩ : syracuseStep 1418953 = 1064215) B1064215
theorem B665351 : Blo 662308 665351 := bstep (se 1 (by rfl) ⟨499013, by rfl⟩ : syracuseStep 665351 = 998027) B998027
theorem B665359 : Blo 662308 665359 := bstep (se 1 (by rfl) ⟨499019, by rfl⟩ : syracuseStep 665359 = 998039) B998039
theorem B1124111 : Blo 662308 1124111 := bstep (se 1 (by rfl) ⟨843083, by rfl⟩ : syracuseStep 1124111 = 1686167) B1686167
theorem B1681195 : Blo 662308 1681195 := bstep (se 1 (by rfl) ⟨1260896, by rfl⟩ : syracuseStep 1681195 = 2521793) B2521793
theorem B665403 : Blo 662308 665403 := bstep (se 1 (by rfl) ⟨499052, by rfl⟩ : syracuseStep 665403 = 998105) B998105
theorem B665479 : Blo 662308 665479 := bstep (se 1 (by rfl) ⟨499109, by rfl⟩ : syracuseStep 665479 = 998219) B998219
theorem B665487 : Blo 662308 665487 := bstep (se 1 (by rfl) ⟨499115, by rfl⟩ : syracuseStep 665487 = 998231) B998231
theorem B1681337 : Blo 662308 1681337 := bstep (se 2 (by rfl) ⟨630501, by rfl⟩ : syracuseStep 1681337 = 1261003) B1261003
theorem B665531 : Blo 662308 665531 := bstep (se 1 (by rfl) ⟨499148, by rfl⟩ : syracuseStep 665531 = 998297) B998297
theorem B665607 : Blo 662308 665607 := bstep (se 1 (by rfl) ⟨499205, by rfl⟩ : syracuseStep 665607 = 998411) B998411
theorem B665615 : Blo 662308 665615 := bstep (se 1 (by rfl) ⟨499211, by rfl⟩ : syracuseStep 665615 = 998423) B998423
theorem B8103959 : Blo 662308 8103959 := bstep (se 1 (by rfl) ⟨6077969, by rfl⟩ : syracuseStep 8103959 = 12155939) B12155939
theorem B3778589 : Blo 662308 3778589 := bstep (se 3 (by rfl) ⟨708485, by rfl⟩ : syracuseStep 3778589 = 1416971) B1416971
theorem B665659 : Blo 662308 665659 := bstep (se 1 (by rfl) ⟨499244, by rfl⟩ : syracuseStep 665659 = 998489) B998489
theorem B6400133 : Blo 662308 6400133 := bstep (se 4 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 6400133 = 1200025) B1200025
theorem B665735 : Blo 662308 665735 := bstep (se 1 (by rfl) ⟨499301, by rfl⟩ : syracuseStep 665735 = 998603) B998603
theorem B665743 : Blo 662308 665743 := bstep (se 1 (by rfl) ⟨499307, by rfl⟩ : syracuseStep 665743 = 998615) B998615
theorem B993467 : Blo 662308 993467 := bstep (se 1 (by rfl) ⟨745100, by rfl⟩ : syracuseStep 993467 = 1490201) B1490201
theorem B665787 : Blo 662308 665787 := bstep (se 1 (by rfl) ⟨499340, by rfl⟩ : syracuseStep 665787 = 998681) B998681
theorem B993527 : Blo 662308 993527 := bstep (se 1 (by rfl) ⟨745145, by rfl⟩ : syracuseStep 993527 = 1490291) B1490291
theorem B665863 : Blo 662308 665863 := bstep (se 1 (by rfl) ⟨499397, by rfl⟩ : syracuseStep 665863 = 998795) B998795
theorem B993551 : Blo 662308 993551 := bstep (se 1 (by rfl) ⟨745163, by rfl⟩ : syracuseStep 993551 = 1490327) B1490327
theorem B665871 : Blo 662308 665871 := bstep (se 1 (by rfl) ⟨499403, by rfl⟩ : syracuseStep 665871 = 998807) B998807
theorem B993593 : Blo 662308 993593 := bstep (se 2 (by rfl) ⟨372597, by rfl⟩ : syracuseStep 993593 = 745195) B745195
theorem B665915 : Blo 662308 665915 := bstep (se 1 (by rfl) ⟨499436, by rfl⟩ : syracuseStep 665915 = 998873) B998873
theorem B993671 : Blo 662308 993671 := bstep (se 1 (by rfl) ⟨745253, by rfl⟩ : syracuseStep 993671 = 1490507) B1490507
theorem B665991 : Blo 662308 665991 := bstep (se 1 (by rfl) ⟨499493, by rfl⟩ : syracuseStep 665991 = 998987) B998987
theorem B665999 : Blo 662308 665999 := bstep (se 1 (by rfl) ⟨499499, by rfl⟩ : syracuseStep 665999 = 998999) B998999
theorem B993707 : Blo 662308 993707 := bstep (se 1 (by rfl) ⟨745280, by rfl⟩ : syracuseStep 993707 = 1490561) B1490561
theorem B8071609 : Blo 662308 8071609 := bstep (se 2 (by rfl) ⟨3026853, by rfl⟩ : syracuseStep 8071609 = 6053707) B6053707
theorem B666043 : Blo 662308 666043 := bstep (se 1 (by rfl) ⟨499532, by rfl⟩ : syracuseStep 666043 = 999065) B999065
theorem B993737 : Blo 662308 993737 := bstep (se 2 (by rfl) ⟨372651, by rfl⟩ : syracuseStep 993737 = 745303) B745303
theorem B12954097 : Blo 662308 12954097 := bstep (se 2 (by rfl) ⟨4857786, by rfl⟩ : syracuseStep 12954097 = 9715573) B9715573
theorem B666119 : Blo 662308 666119 := bstep (se 1 (by rfl) ⟨499589, by rfl⟩ : syracuseStep 666119 = 999179) B999179
theorem B666127 : Blo 662308 666127 := bstep (se 1 (by rfl) ⟨499595, by rfl⟩ : syracuseStep 666127 = 999191) B999191
theorem B993851 : Blo 662308 993851 := bstep (se 1 (by rfl) ⟨745388, by rfl⟩ : syracuseStep 993851 = 1490777) B1490777
theorem B666171 : Blo 662308 666171 := bstep (se 1 (by rfl) ⟨499628, by rfl⟩ : syracuseStep 666171 = 999257) B999257
theorem B993911 : Blo 662308 993911 := bstep (se 1 (by rfl) ⟨745433, by rfl⟩ : syracuseStep 993911 = 1490867) B1490867
theorem B666247 : Blo 662308 666247 := bstep (se 1 (by rfl) ⟨499685, by rfl⟩ : syracuseStep 666247 = 999371) B999371
theorem B993935 : Blo 662308 993935 := bstep (se 1 (by rfl) ⟨745451, by rfl⟩ : syracuseStep 993935 = 1490903) B1490903
theorem B666255 : Blo 662308 666255 := bstep (se 1 (by rfl) ⟨499691, by rfl⟩ : syracuseStep 666255 = 999383) B999383
theorem B993977 : Blo 662308 993977 := bstep (se 2 (by rfl) ⟨372741, by rfl⟩ : syracuseStep 993977 = 745483) B745483
theorem B666299 : Blo 662308 666299 := bstep (se 1 (by rfl) ⟨499724, by rfl⟩ : syracuseStep 666299 = 999449) B999449
theorem B994055 : Blo 662308 994055 := bstep (se 1 (by rfl) ⟨745541, by rfl⟩ : syracuseStep 994055 = 1491083) B1491083
theorem B994091 : Blo 662308 994091 := bstep (se 1 (by rfl) ⟨745568, by rfl⟩ : syracuseStep 994091 = 1491137) B1491137
theorem B994121 : Blo 662308 994121 := bstep (se 2 (by rfl) ⟨372795, by rfl⟩ : syracuseStep 994121 = 745591) B745591
theorem B2239379 : Blo 662308 2239379 := bstep (se 1 (by rfl) ⟨1679534, by rfl⟩ : syracuseStep 2239379 = 3359069) B3359069
theorem B1682329 : Blo 662308 1682329 := bstep (se 2 (by rfl) ⟨630873, by rfl⟩ : syracuseStep 1682329 = 1261747) B1261747
theorem B994235 : Blo 662308 994235 := bstep (se 1 (by rfl) ⟨745676, by rfl⟩ : syracuseStep 994235 = 1491353) B1491353
theorem B3189725 : Blo 662308 3189725 := bstep (se 3 (by rfl) ⟨598073, by rfl⟩ : syracuseStep 3189725 = 1196147) B1196147
theorem B994295 : Blo 662308 994295 := bstep (se 1 (by rfl) ⟨745721, by rfl⟩ : syracuseStep 994295 = 1491443) B1491443
theorem B994319 : Blo 662308 994319 := bstep (se 1 (by rfl) ⟨745739, by rfl⟩ : syracuseStep 994319 = 1491479) B1491479
theorem B994361 : Blo 662308 994361 := bstep (se 2 (by rfl) ⟨372885, by rfl⟩ : syracuseStep 994361 = 745771) B745771
theorem B1682491 : Blo 662308 1682491 := bstep (se 1 (by rfl) ⟨1261868, by rfl⟩ : syracuseStep 1682491 = 2523737) B2523737
theorem B2829431 : Blo 662308 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B994439 : Blo 662308 994439 := bstep (se 1 (by rfl) ⟨745829, by rfl⟩ : syracuseStep 994439 = 1491659) B1491659
theorem B994475 : Blo 662308 994475 := bstep (se 1 (by rfl) ⟨745856, by rfl⟩ : syracuseStep 994475 = 1491713) B1491713
theorem B994505 : Blo 662308 994505 := bstep (se 2 (by rfl) ⟨372939, by rfl⟩ : syracuseStep 994505 = 745879) B745879
theorem B1682633 : Blo 662308 1682633 := bstep (se 2 (by rfl) ⟨630987, by rfl⟩ : syracuseStep 1682633 = 1261975) B1261975
theorem B994619 : Blo 662308 994619 := bstep (se 1 (by rfl) ⟨745964, by rfl⟩ : syracuseStep 994619 = 1491929) B1491929
theorem B994679 : Blo 662308 994679 := bstep (se 1 (by rfl) ⟨746009, by rfl⟩ : syracuseStep 994679 = 1492019) B1492019
theorem B1420679 : Blo 662308 1420679 := bstep (se 1 (by rfl) ⟨1065509, by rfl⟩ : syracuseStep 1420679 = 2131019) B2131019
theorem B994703 : Blo 662308 994703 := bstep (se 1 (by rfl) ⟨746027, by rfl⟩ : syracuseStep 994703 = 1492055) B1492055
theorem B5680529 : Blo 662308 5680529 := bstep (se 2 (by rfl) ⟨2130198, by rfl⟩ : syracuseStep 5680529 = 4260397) B4260397
theorem B994745 : Blo 662308 994745 := bstep (se 2 (by rfl) ⟨373029, by rfl⟩ : syracuseStep 994745 = 746059) B746059
theorem B3190225 : Blo 662308 3190225 := bstep (se 2 (by rfl) ⟨1196334, by rfl⟩ : syracuseStep 3190225 = 2392669) B2392669
theorem B994823 : Blo 662308 994823 := bstep (se 1 (by rfl) ⟨746117, by rfl⟩ : syracuseStep 994823 = 1492235) B1492235
theorem B1682977 : Blo 662308 1682977 := bstep (se 2 (by rfl) ⟨631116, by rfl⟩ : syracuseStep 1682977 = 1262233) B1262233
theorem B994859 : Blo 662308 994859 := bstep (se 1 (by rfl) ⟨746144, by rfl⟩ : syracuseStep 994859 = 1492289) B1492289
theorem B994889 : Blo 662308 994889 := bstep (se 2 (by rfl) ⟨373083, by rfl⟩ : syracuseStep 994889 = 746167) B746167
theorem B2731639 : Blo 662308 2731639 := bstep (se 1 (by rfl) ⟨2048729, by rfl⟩ : syracuseStep 2731639 = 4097459) B4097459
theorem B995003 : Blo 662308 995003 := bstep (se 1 (by rfl) ⟨746252, by rfl⟩ : syracuseStep 995003 = 1492505) B1492505
theorem B995063 : Blo 662308 995063 := bstep (se 1 (by rfl) ⟨746297, by rfl⟩ : syracuseStep 995063 = 1492595) B1492595
theorem B995087 : Blo 662308 995087 := bstep (se 1 (by rfl) ⟨746315, by rfl⟩ : syracuseStep 995087 = 1492631) B1492631
theorem B995129 : Blo 662308 995129 := bstep (se 2 (by rfl) ⟨373173, by rfl⟩ : syracuseStep 995129 = 746347) B746347
theorem B995207 : Blo 662308 995207 := bstep (se 1 (by rfl) ⟨746405, by rfl⟩ : syracuseStep 995207 = 1492811) B1492811
theorem B995243 : Blo 662308 995243 := bstep (se 1 (by rfl) ⟨746432, by rfl⟩ : syracuseStep 995243 = 1492865) B1492865
theorem B995273 : Blo 662308 995273 := bstep (se 2 (by rfl) ⟨373227, by rfl⟩ : syracuseStep 995273 = 746455) B746455
theorem B1421345 : Blo 662308 1421345 := bstep (se 2 (by rfl) ⟨533004, by rfl⟩ : syracuseStep 1421345 = 1066009) B1066009
theorem B995387 : Blo 662308 995387 := bstep (se 1 (by rfl) ⟨746540, by rfl⟩ : syracuseStep 995387 = 1493081) B1493081
theorem B2830423 : Blo 662308 2830423 := bstep (se 1 (by rfl) ⟨2122817, by rfl⟩ : syracuseStep 2830423 = 4245635) B4245635
theorem B995447 : Blo 662308 995447 := bstep (se 1 (by rfl) ⟨746585, by rfl⟩ : syracuseStep 995447 = 1493171) B1493171
theorem B1683575 : Blo 662308 1683575 := bstep (se 1 (by rfl) ⟨1262681, by rfl⟩ : syracuseStep 1683575 = 2525363) B2525363
theorem B995471 : Blo 662308 995471 := bstep (se 1 (by rfl) ⟨746603, by rfl⟩ : syracuseStep 995471 = 1493207) B1493207
theorem B995513 : Blo 662308 995513 := bstep (se 2 (by rfl) ⟨373317, by rfl⟩ : syracuseStep 995513 = 746635) B746635
theorem B1093817 : Blo 662308 1093817 := bstep (se 2 (by rfl) ⟨410181, by rfl⟩ : syracuseStep 1093817 = 820363) B820363
theorem B995591 : Blo 662308 995591 := bstep (se 1 (by rfl) ⟨746693, by rfl⟩ : syracuseStep 995591 = 1493387) B1493387
theorem B2240783 : Blo 662308 2240783 := bstep (se 1 (by rfl) ⟨1680587, by rfl⟩ : syracuseStep 2240783 = 3361175) B3361175
theorem B1257761 : Blo 662308 1257761 := bstep (se 2 (by rfl) ⟨471660, by rfl⟩ : syracuseStep 1257761 = 943321) B943321
theorem B995627 : Blo 662308 995627 := bstep (se 1 (by rfl) ⟨746720, by rfl⟩ : syracuseStep 995627 = 1493441) B1493441
theorem B995657 : Blo 662308 995657 := bstep (se 2 (by rfl) ⟨373371, by rfl⟩ : syracuseStep 995657 = 746743) B746743
theorem B1421687 : Blo 662308 1421687 := bstep (se 1 (by rfl) ⟨1066265, by rfl⟩ : syracuseStep 1421687 = 2132531) B2132531
theorem B995771 : Blo 662308 995771 := bstep (se 1 (by rfl) ⟨746828, by rfl⟩ : syracuseStep 995771 = 1493657) B1493657
theorem B3584459 : Blo 662308 3584459 := bstep (se 1 (by rfl) ⟨2688344, by rfl⟩ : syracuseStep 3584459 = 5376689) B5376689
theorem B995831 : Blo 662308 995831 := bstep (se 1 (by rfl) ⟨746873, by rfl⟩ : syracuseStep 995831 = 1493747) B1493747
theorem B995855 : Blo 662308 995855 := bstep (se 1 (by rfl) ⟨746891, by rfl⟩ : syracuseStep 995855 = 1493783) B1493783
theorem B2241053 : Blo 662308 2241053 := bstep (se 3 (by rfl) ⟨420197, by rfl⟩ : syracuseStep 2241053 = 840395) B840395
theorem B3191339 : Blo 662308 3191339 := bstep (se 1 (by rfl) ⟨2393504, by rfl⟩ : syracuseStep 3191339 = 4787009) B4787009
theorem B995897 : Blo 662308 995897 := bstep (se 2 (by rfl) ⟨373461, by rfl⟩ : syracuseStep 995897 = 746923) B746923
theorem B3781187 : Blo 662308 3781187 := bstep (se 1 (by rfl) ⟨2835890, by rfl⟩ : syracuseStep 3781187 = 5671781) B5671781
theorem B6369911 : Blo 662308 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B995975 : Blo 662308 995975 := bstep (se 1 (by rfl) ⟨746981, by rfl⟩ : syracuseStep 995975 = 1493963) B1493963
theorem B996011 : Blo 662308 996011 := bstep (se 1 (by rfl) ⟨747008, by rfl⟩ : syracuseStep 996011 = 1494017) B1494017
theorem B996041 : Blo 662308 996041 := bstep (se 2 (by rfl) ⟨373515, by rfl⟩ : syracuseStep 996041 = 747031) B747031
theorem B996155 : Blo 662308 996155 := bstep (se 1 (by rfl) ⟨747116, by rfl⟩ : syracuseStep 996155 = 1494233) B1494233
theorem B996215 : Blo 662308 996215 := bstep (se 1 (by rfl) ⟨747161, by rfl⟩ : syracuseStep 996215 = 1494323) B1494323
theorem B996239 : Blo 662308 996239 := bstep (se 1 (by rfl) ⟨747179, by rfl⟩ : syracuseStep 996239 = 1494359) B1494359
theorem B996281 : Blo 662308 996281 := bstep (se 2 (by rfl) ⟨373605, by rfl⟩ : syracuseStep 996281 = 747211) B747211
theorem B799735 : Blo 662308 799735 := bstep (se 1 (by rfl) ⟨599801, by rfl⟩ : syracuseStep 799735 = 1199603) B1199603
theorem B996359 : Blo 662308 996359 := bstep (se 1 (by rfl) ⟨747269, by rfl⟩ : syracuseStep 996359 = 1494539) B1494539
theorem B1061903 : Blo 662308 1061903 := bstep (se 1 (by rfl) ⟨796427, by rfl⟩ : syracuseStep 1061903 = 1592855) B1592855
theorem B996395 : Blo 662308 996395 := bstep (se 1 (by rfl) ⟨747296, by rfl⟩ : syracuseStep 996395 = 1494593) B1494593
theorem B996425 : Blo 662308 996425 := bstep (se 2 (by rfl) ⟨373659, by rfl⟩ : syracuseStep 996425 = 747319) B747319
theorem B996539 : Blo 662308 996539 := bstep (se 1 (by rfl) ⟨747404, by rfl⟩ : syracuseStep 996539 = 1494809) B1494809
theorem B996599 : Blo 662308 996599 := bstep (se 1 (by rfl) ⟨747449, by rfl⟩ : syracuseStep 996599 = 1494899) B1494899
theorem B996623 : Blo 662308 996623 := bstep (se 1 (by rfl) ⟨747467, by rfl⟩ : syracuseStep 996623 = 1494935) B1494935
theorem B996665 : Blo 662308 996665 := bstep (se 2 (by rfl) ⟨373749, by rfl⟩ : syracuseStep 996665 = 747499) B747499
theorem B996743 : Blo 662308 996743 := bstep (se 1 (by rfl) ⟨747557, by rfl⟩ : syracuseStep 996743 = 1495115) B1495115
theorem B1684871 : Blo 662308 1684871 := bstep (se 1 (by rfl) ⟨1263653, by rfl⟩ : syracuseStep 1684871 = 2527307) B2527307
theorem B996779 : Blo 662308 996779 := bstep (se 1 (by rfl) ⟨747584, by rfl⟩ : syracuseStep 996779 = 1495169) B1495169
theorem B1684921 : Blo 662308 1684921 := bstep (se 2 (by rfl) ⟨631845, by rfl⟩ : syracuseStep 1684921 = 1263691) B1263691
theorem B996809 : Blo 662308 996809 := bstep (se 2 (by rfl) ⟨373803, by rfl⟩ : syracuseStep 996809 = 747607) B747607
theorem B996923 : Blo 662308 996923 := bstep (se 1 (by rfl) ⟨747692, by rfl⟩ : syracuseStep 996923 = 1495385) B1495385
theorem B996983 : Blo 662308 996983 := bstep (se 1 (by rfl) ⟨747737, by rfl⟩ : syracuseStep 996983 = 1495475) B1495475
theorem B997007 : Blo 662308 997007 := bstep (se 1 (by rfl) ⟨747755, by rfl⟩ : syracuseStep 997007 = 1495511) B1495511
theorem B997049 : Blo 662308 997049 := bstep (se 2 (by rfl) ⟨373893, by rfl⟩ : syracuseStep 997049 = 747787) B747787
theorem B997127 : Blo 662308 997127 := bstep (se 1 (by rfl) ⟨747845, by rfl⟩ : syracuseStep 997127 = 1495691) B1495691
theorem B997163 : Blo 662308 997163 := bstep (se 1 (by rfl) ⟨747872, by rfl⟩ : syracuseStep 997163 = 1495745) B1495745
theorem B997193 : Blo 662308 997193 := bstep (se 2 (by rfl) ⟨373947, by rfl⟩ : syracuseStep 997193 = 747895) B747895
theorem B2242457 : Blo 662308 2242457 := bstep (se 2 (by rfl) ⟨840921, by rfl⟩ : syracuseStep 2242457 = 1681843) B1681843
theorem B997307 : Blo 662308 997307 := bstep (se 1 (by rfl) ⟨747980, by rfl⟩ : syracuseStep 997307 = 1495961) B1495961
theorem B1062857 : Blo 662308 1062857 := bstep (se 2 (by rfl) ⟨398571, by rfl⟩ : syracuseStep 1062857 = 797143) B797143
theorem B997367 : Blo 662308 997367 := bstep (se 1 (by rfl) ⟨748025, by rfl⟩ : syracuseStep 997367 = 1496051) B1496051
theorem B7550981 : Blo 662308 7550981 := bstep (se 4 (by rfl) ⟨707904, by rfl⟩ : syracuseStep 7550981 = 1415809) B1415809
theorem B997391 : Blo 662308 997391 := bstep (se 1 (by rfl) ⟨748043, by rfl⟩ : syracuseStep 997391 = 1496087) B1496087
theorem B1685519 : Blo 662308 1685519 := bstep (se 1 (by rfl) ⟨1264139, by rfl⟩ : syracuseStep 1685519 = 2528279) B2528279
theorem B997433 : Blo 662308 997433 := bstep (se 2 (by rfl) ⟨374037, by rfl⟩ : syracuseStep 997433 = 748075) B748075
theorem B997511 : Blo 662308 997511 := bstep (se 1 (by rfl) ⟨748133, by rfl⟩ : syracuseStep 997511 = 1496267) B1496267
theorem B997547 : Blo 662308 997547 := bstep (se 1 (by rfl) ⟨748160, by rfl⟩ : syracuseStep 997547 = 1496321) B1496321
theorem B4044973 : Blo 662308 4044973 := bstep (se 3 (by rfl) ⟨758432, by rfl⟩ : syracuseStep 4044973 = 1516865) B1516865
theorem B1259705 : Blo 662308 1259705 := bstep (se 2 (by rfl) ⟨472389, by rfl⟩ : syracuseStep 1259705 = 944779) B944779
theorem B997577 : Blo 662308 997577 := bstep (se 2 (by rfl) ⟨374091, by rfl⟩ : syracuseStep 997577 = 748183) B748183
theorem B7649569 : Blo 662308 7649569 := bstep (se 2 (by rfl) ⟨2868588, by rfl⟩ : syracuseStep 7649569 = 5737177) B5737177
theorem B3782963 : Blo 662308 3782963 := bstep (se 1 (by rfl) ⟨2837222, by rfl⟩ : syracuseStep 3782963 = 5674445) B5674445
theorem B997691 : Blo 662308 997691 := bstep (se 1 (by rfl) ⟨748268, by rfl⟩ : syracuseStep 997691 = 1496537) B1496537
theorem B997751 : Blo 662308 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B997775 : Blo 662308 997775 := bstep (se 1 (by rfl) ⟨748331, by rfl⟩ : syracuseStep 997775 = 1496663) B1496663
theorem B997817 : Blo 662308 997817 := bstep (se 2 (by rfl) ⟨374181, by rfl⟩ : syracuseStep 997817 = 748363) B748363
theorem B997895 : Blo 662308 997895 := bstep (se 1 (by rfl) ⟨748421, by rfl⟩ : syracuseStep 997895 = 1496843) B1496843
theorem B2341405 : Blo 662308 2341405 := bstep (se 3 (by rfl) ⟨439013, by rfl⟩ : syracuseStep 2341405 = 878027) B878027
theorem B997931 : Blo 662308 997931 := bstep (se 1 (by rfl) ⟨748448, by rfl⟩ : syracuseStep 997931 = 1496897) B1496897
theorem B997961 : Blo 662308 997961 := bstep (se 2 (by rfl) ⟨374235, by rfl⟩ : syracuseStep 997961 = 748471) B748471
theorem B2243159 : Blo 662308 2243159 := bstep (se 1 (by rfl) ⟨1682369, by rfl⟩ : syracuseStep 2243159 = 3364739) B3364739
theorem B1063543 : Blo 662308 1063543 := bstep (se 1 (by rfl) ⟨797657, by rfl⟩ : syracuseStep 1063543 = 1595315) B1595315
theorem B998075 : Blo 662308 998075 := bstep (se 1 (by rfl) ⟨748556, by rfl⟩ : syracuseStep 998075 = 1497113) B1497113
theorem B1686217 : Blo 662308 1686217 := bstep (se 2 (by rfl) ⟨632331, by rfl⟩ : syracuseStep 1686217 = 1264663) B1264663
theorem B998135 : Blo 662308 998135 := bstep (se 1 (by rfl) ⟨748601, by rfl⟩ : syracuseStep 998135 = 1497203) B1497203
theorem B998159 : Blo 662308 998159 := bstep (se 1 (by rfl) ⟨748619, by rfl⟩ : syracuseStep 998159 = 1497239) B1497239
theorem B1817387 : Blo 662308 1817387 := bstep (se 1 (by rfl) ⟨1363040, by rfl⟩ : syracuseStep 1817387 = 2726081) B2726081
theorem B998201 : Blo 662308 998201 := bstep (se 2 (by rfl) ⟨374325, by rfl⟩ : syracuseStep 998201 = 748651) B748651
theorem B1686359 : Blo 662308 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B5389145 : Blo 662308 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B998279 : Blo 662308 998279 := bstep (se 1 (by rfl) ⟨748709, by rfl⟩ : syracuseStep 998279 = 1497419) B1497419
theorem B998315 : Blo 662308 998315 := bstep (se 1 (by rfl) ⟨748736, by rfl⟩ : syracuseStep 998315 = 1497473) B1497473
theorem B998345 : Blo 662308 998345 := bstep (se 2 (by rfl) ⟨374379, by rfl⟩ : syracuseStep 998345 = 748759) B748759
theorem B998459 : Blo 662308 998459 := bstep (se 1 (by rfl) ⟨748844, by rfl⟩ : syracuseStep 998459 = 1497689) B1497689
theorem B2243645 : Blo 662308 2243645 := bstep (se 3 (by rfl) ⟨420683, by rfl⟩ : syracuseStep 2243645 = 841367) B841367
theorem B998519 : Blo 662308 998519 := bstep (se 1 (by rfl) ⟨748889, by rfl⟩ : syracuseStep 998519 = 1497779) B1497779
theorem B998543 : Blo 662308 998543 := bstep (se 1 (by rfl) ⟨748907, by rfl⟩ : syracuseStep 998543 = 1497815) B1497815
theorem B998585 : Blo 662308 998585 := bstep (se 2 (by rfl) ⟨374469, by rfl⟩ : syracuseStep 998585 = 748939) B748939
theorem B998663 : Blo 662308 998663 := bstep (se 1 (by rfl) ⟨748997, by rfl⟩ : syracuseStep 998663 = 1497995) B1497995
theorem B1490219 : Blo 662308 1490219 := bstep (se 1 (by rfl) ⟨1117664, by rfl⟩ : syracuseStep 1490219 = 2235329) B2235329
theorem B998699 : Blo 662308 998699 := bstep (se 1 (by rfl) ⟨749024, by rfl⟩ : syracuseStep 998699 = 1498049) B1498049
theorem B4603195 : Blo 662308 4603195 := bstep (se 1 (by rfl) ⟨3452396, by rfl⟩ : syracuseStep 4603195 = 6904793) B6904793
theorem B1260859 : Blo 662308 1260859 := bstep (se 1 (by rfl) ⟨945644, by rfl⟩ : syracuseStep 1260859 = 1891289) B1891289
theorem B998729 : Blo 662308 998729 := bstep (se 2 (by rfl) ⟨374523, by rfl⟩ : syracuseStep 998729 = 749047) B749047
theorem B3358097 : Blo 662308 3358097 := bstep (se 2 (by rfl) ⟨1259286, by rfl⟩ : syracuseStep 3358097 = 2518573) B2518573
theorem B998843 : Blo 662308 998843 := bstep (se 1 (by rfl) ⟨749132, by rfl⟩ : syracuseStep 998843 = 1498265) B1498265
theorem B998903 : Blo 662308 998903 := bstep (se 1 (by rfl) ⟨749177, by rfl⟩ : syracuseStep 998903 = 1498355) B1498355
theorem B998927 : Blo 662308 998927 := bstep (se 1 (by rfl) ⟨749195, by rfl⟩ : syracuseStep 998927 = 1498391) B1498391
theorem B998969 : Blo 662308 998969 := bstep (se 2 (by rfl) ⟨374613, by rfl⟩ : syracuseStep 998969 = 749227) B749227
theorem B999047 : Blo 662308 999047 := bstep (se 1 (by rfl) ⟨749285, by rfl⟩ : syracuseStep 999047 = 1498571) B1498571
theorem B1490579 : Blo 662308 1490579 := bstep (se 1 (by rfl) ⟨1117934, by rfl⟩ : syracuseStep 1490579 = 2235869) B2235869
theorem B999083 : Blo 662308 999083 := bstep (se 1 (by rfl) ⟨749312, by rfl⟩ : syracuseStep 999083 = 1498625) B1498625
theorem B1490633 : Blo 662308 1490633 := bstep (se 2 (by rfl) ⟨558987, by rfl⟩ : syracuseStep 1490633 = 1117975) B1117975
theorem B999113 : Blo 662308 999113 := bstep (se 2 (by rfl) ⟨374667, by rfl⟩ : syracuseStep 999113 = 749335) B749335
theorem B3784421 : Blo 662308 3784421 := bstep (se 4 (by rfl) ⟨354789, by rfl⟩ : syracuseStep 3784421 = 709579) B709579
theorem B1261345 : Blo 662308 1261345 := bstep (se 2 (by rfl) ⟨473004, by rfl⟩ : syracuseStep 1261345 = 946009) B946009
theorem B999227 : Blo 662308 999227 := bstep (se 1 (by rfl) ⟨749420, by rfl⟩ : syracuseStep 999227 = 1498841) B1498841
theorem B999287 : Blo 662308 999287 := bstep (se 1 (by rfl) ⟨749465, by rfl⟩ : syracuseStep 999287 = 1498931) B1498931
theorem B769927 : Blo 662308 769927 := bstep (se 1 (by rfl) ⟨577445, by rfl⟩ : syracuseStep 769927 = 1154891) B1154891
theorem B999311 : Blo 662308 999311 := bstep (se 1 (by rfl) ⟨749483, by rfl⟩ : syracuseStep 999311 = 1498967) B1498967
theorem B999353 : Blo 662308 999353 := bstep (se 2 (by rfl) ⟨374757, by rfl⟩ : syracuseStep 999353 = 749515) B749515
theorem B999431 : Blo 662308 999431 := bstep (se 1 (by rfl) ⟨749573, by rfl⟩ : syracuseStep 999431 = 1499147) B1499147
theorem B3784877 : Blo 662308 3784877 := bstep (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) B1419329
theorem B2834747 : Blo 662308 2834747 := bstep (se 1 (by rfl) ⟨2126060, by rfl⟩ : syracuseStep 2834747 = 4252121) B4252121
theorem B1491335 : Blo 662308 1491335 := bstep (se 1 (by rfl) ⟨1118501, by rfl⟩ : syracuseStep 1491335 = 2237003) B2237003
theorem B2245049 : Blo 662308 2245049 := bstep (se 2 (by rfl) ⟨841893, by rfl⟩ : syracuseStep 2245049 = 1683787) B1683787
theorem B1491515 : Blo 662308 1491515 := bstep (se 1 (by rfl) ⟨1118636, by rfl⟩ : syracuseStep 1491515 = 2237273) B2237273
theorem B1491641 : Blo 662308 1491641 := bstep (se 2 (by rfl) ⟨559365, by rfl⟩ : syracuseStep 1491641 = 1118731) B1118731
theorem B3785561 : Blo 662308 3785561 := bstep (se 2 (by rfl) ⟨1419585, by rfl⟩ : syracuseStep 3785561 = 2839171) B2839171
theorem B1196947 : Blo 662308 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B1262537 : Blo 662308 1262537 := bstep (se 2 (by rfl) ⟨473451, by rfl⟩ : syracuseStep 1262537 = 946903) B946903
theorem B2245643 : Blo 662308 2245643 := bstep (se 1 (by rfl) ⟨1684232, by rfl⟩ : syracuseStep 2245643 = 3368465) B3368465
theorem B1491983 : Blo 662308 1491983 := bstep (se 1 (by rfl) ⟨1118987, by rfl⟩ : syracuseStep 1491983 = 2237975) B2237975
theorem B1492001 : Blo 662308 1492001 := bstep (se 2 (by rfl) ⟨559500, by rfl⟩ : syracuseStep 1492001 = 1119001) B1119001
theorem B2245751 : Blo 662308 2245751 := bstep (se 1 (by rfl) ⟨1684313, by rfl⟩ : syracuseStep 2245751 = 3368627) B3368627
theorem B1492343 : Blo 662308 1492343 := bstep (se 1 (by rfl) ⟨1119257, by rfl⟩ : syracuseStep 1492343 = 2238515) B2238515
theorem B3360203 : Blo 662308 3360203 := bstep (se 1 (by rfl) ⟨2520152, by rfl⟩ : syracuseStep 3360203 = 5040305) B5040305
theorem B1492523 : Blo 662308 1492523 := bstep (se 1 (by rfl) ⟨1119392, by rfl⟩ : syracuseStep 1492523 = 2238785) B2238785
theorem B1263251 : Blo 662308 1263251 := bstep (se 1 (by rfl) ⟨947438, by rfl⟩ : syracuseStep 1263251 = 1894877) B1894877
theorem B1263289 : Blo 662308 1263289 := bstep (se 2 (by rfl) ⟨473733, by rfl⟩ : syracuseStep 1263289 = 947467) B947467
theorem B2246345 : Blo 662308 2246345 := bstep (se 2 (by rfl) ⟨842379, by rfl⟩ : syracuseStep 2246345 = 1684759) B1684759
theorem B3360527 : Blo 662308 3360527 := bstep (se 1 (by rfl) ⟨2520395, by rfl⟩ : syracuseStep 3360527 = 5040791) B5040791
theorem B6145807 : Blo 662308 6145807 := bstep (se 1 (by rfl) ⟨4609355, by rfl⟩ : syracuseStep 6145807 = 9218711) B9218711
theorem B1492883 : Blo 662308 1492883 := bstep (se 1 (by rfl) ⟨1119662, by rfl⟩ : syracuseStep 1492883 = 2239325) B2239325
theorem B1886105 : Blo 662308 1886105 := bstep (se 2 (by rfl) ⟨707289, by rfl⟩ : syracuseStep 1886105 = 1414579) B1414579
theorem B2869145 : Blo 662308 2869145 := bstep (se 2 (by rfl) ⟨1075929, by rfl⟩ : syracuseStep 2869145 = 2151859) B2151859
theorem B1492937 : Blo 662308 1492937 := bstep (se 2 (by rfl) ⟨559851, by rfl⟩ : syracuseStep 1492937 = 1119703) B1119703
theorem B1361953 : Blo 662308 1361953 := bstep (se 2 (by rfl) ⟨510732, by rfl⟩ : syracuseStep 1361953 = 1021465) B1021465
theorem B2247047 : Blo 662308 2247047 := bstep (se 1 (by rfl) ⟨1685285, by rfl⟩ : syracuseStep 2247047 = 3370571) B3370571
theorem B838279 : Blo 662308 838279 := bstep (se 1 (by rfl) ⟨628709, by rfl⟩ : syracuseStep 838279 = 1257419) B1257419
theorem B1493639 : Blo 662308 1493639 := bstep (se 1 (by rfl) ⟨1120229, by rfl⟩ : syracuseStep 1493639 = 2240459) B2240459
theorem B1198793 : Blo 662308 1198793 := bstep (se 2 (by rfl) ⟨449547, by rfl⟩ : syracuseStep 1198793 = 899095) B899095
theorem B2247425 : Blo 662308 2247425 := bstep (se 2 (by rfl) ⟨842784, by rfl⟩ : syracuseStep 2247425 = 1685569) B1685569
theorem B1493819 : Blo 662308 1493819 := bstep (se 1 (by rfl) ⟨1120364, by rfl⟩ : syracuseStep 1493819 = 2240729) B2240729
theorem B2018135 : Blo 662308 2018135 := bstep (se 1 (by rfl) ⟨1513601, by rfl⟩ : syracuseStep 2018135 = 3027203) B3027203
theorem B1493945 : Blo 662308 1493945 := bstep (se 2 (by rfl) ⟨560229, by rfl⟩ : syracuseStep 1493945 = 1120459) B1120459
theorem B14797835 : Blo 662308 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B838775 : Blo 662308 838775 := bstep (se 1 (by rfl) ⟨629081, by rfl⟩ : syracuseStep 838775 = 1258163) B1258163
theorem B3361985 : Blo 662308 3361985 := bstep (se 2 (by rfl) ⟨1260744, by rfl⟩ : syracuseStep 3361985 = 2521489) B2521489
theorem B838927 : Blo 662308 838927 := bstep (se 1 (by rfl) ⟨629195, by rfl⟩ : syracuseStep 838927 = 1258391) B1258391
theorem B1494287 : Blo 662308 1494287 := bstep (se 1 (by rfl) ⟨1120715, by rfl⟩ : syracuseStep 1494287 = 2241431) B2241431
theorem B1494305 : Blo 662308 1494305 := bstep (se 2 (by rfl) ⟨560364, by rfl⟩ : syracuseStep 1494305 = 1120729) B1120729
theorem B839099 : Blo 662308 839099 := bstep (se 1 (by rfl) ⟨629324, by rfl⟩ : syracuseStep 839099 = 1258649) B1258649
theorem B1920523 : Blo 662308 1920523 := bstep (se 1 (by rfl) ⟨1440392, by rfl⟩ : syracuseStep 1920523 = 2880785) B2880785
theorem B5033501 : Blo 662308 5033501 := bstep (se 3 (by rfl) ⟨943781, by rfl⟩ : syracuseStep 5033501 = 1887563) B1887563
theorem B2248235 : Blo 662308 2248235 := bstep (se 1 (by rfl) ⟨1686176, by rfl⟩ : syracuseStep 2248235 = 3372353) B3372353
theorem B1494647 : Blo 662308 1494647 := bstep (se 1 (by rfl) ⟨1120985, by rfl⟩ : syracuseStep 1494647 = 2241971) B2241971
theorem B55266947 : Blo 662308 55266947 := bstep (se 1 (by rfl) ⟨41450210, by rfl⟩ : syracuseStep 55266947 = 82900421) B82900421
theorem B1593017 : Blo 662308 1593017 := bstep (se 2 (by rfl) ⟨597381, by rfl⟩ : syracuseStep 1593017 = 1194763) B1194763
theorem B1494827 : Blo 662308 1494827 := bstep (se 1 (by rfl) ⟨1121120, by rfl⟩ : syracuseStep 1494827 = 2242241) B2242241
theorem B1888201 : Blo 662308 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B1495187 : Blo 662308 1495187 := bstep (se 1 (by rfl) ⟨1121390, by rfl⟩ : syracuseStep 1495187 = 2242781) B2242781
theorem B1495241 : Blo 662308 1495241 := bstep (se 2 (by rfl) ⟨560715, by rfl⟩ : syracuseStep 1495241 = 1121431) B1121431
theorem B1888555 : Blo 662308 1888555 := bstep (se 1 (by rfl) ⟨1416416, by rfl⟩ : syracuseStep 1888555 = 2832833) B2832833
theorem B840071 : Blo 662308 840071 := bstep (se 1 (by rfl) ⟨630053, by rfl⟩ : syracuseStep 840071 = 1260107) B1260107
theorem B3363281 : Blo 662308 3363281 := bstep (se 2 (by rfl) ⟨1261230, by rfl⟩ : syracuseStep 3363281 = 2522461) B2522461
theorem B1888829 : Blo 662308 1888829 := bstep (se 3 (by rfl) ⟨354155, by rfl⟩ : syracuseStep 1888829 = 708311) B708311
theorem B2872199 : Blo 662308 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B1495943 : Blo 662308 1495943 := bstep (se 1 (by rfl) ⟨1121957, by rfl⟩ : syracuseStep 1495943 = 2243915) B2243915
theorem B840719 : Blo 662308 840719 := bstep (se 1 (by rfl) ⟨630539, by rfl⟩ : syracuseStep 840719 = 1261079) B1261079
theorem B1496123 : Blo 662308 1496123 := bstep (se 1 (by rfl) ⟨1122092, by rfl⟩ : syracuseStep 1496123 = 2244185) B2244185
theorem B1496249 : Blo 662308 1496249 := bstep (se 2 (by rfl) ⟨561093, by rfl⟩ : syracuseStep 1496249 = 1122187) B1122187
theorem B4052369 : Blo 662308 4052369 := bstep (se 2 (by rfl) ⟨1519638, by rfl⟩ : syracuseStep 4052369 = 3039277) B3039277
theorem B3462659 : Blo 662308 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B1496591 : Blo 662308 1496591 := bstep (se 1 (by rfl) ⟨1122443, by rfl⟩ : syracuseStep 1496591 = 2244887) B2244887
theorem B2840093 : Blo 662308 2840093 := bstep (se 3 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 2840093 = 1065035) B1065035
theorem B1496609 : Blo 662308 1496609 := bstep (se 2 (by rfl) ⟨561228, by rfl⟩ : syracuseStep 1496609 = 1122457) B1122457
theorem B710203 : Blo 662308 710203 := bstep (se 1 (by rfl) ⟨532652, by rfl⟩ : syracuseStep 710203 = 1065305) B1065305
theorem B1496951 : Blo 662308 1496951 := bstep (se 1 (by rfl) ⟨1122713, by rfl⟩ : syracuseStep 1496951 = 2245427) B2245427
theorem B3594131 : Blo 662308 3594131 := bstep (se 1 (by rfl) ⟨2695598, by rfl⟩ : syracuseStep 3594131 = 5391197) B5391197
theorem B1497131 : Blo 662308 1497131 := bstep (se 1 (by rfl) ⟨1122848, by rfl⟩ : syracuseStep 1497131 = 2245697) B2245697
theorem B5462149 : Blo 662308 5462149 := bstep (se 4 (by rfl) ⟨512076, by rfl⟩ : syracuseStep 5462149 = 1024153) B1024153
theorem B14342345 : Blo 662308 14342345 := bstep (se 2 (by rfl) ⟨5378379, by rfl⟩ : syracuseStep 14342345 = 10756759) B10756759
theorem B6379721 : Blo 662308 6379721 := bstep (se 2 (by rfl) ⟨2392395, by rfl⟩ : syracuseStep 6379721 = 4784791) B4784791
theorem B2840777 : Blo 662308 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B4544903 : Blo 662308 4544903 := bstep (se 1 (by rfl) ⟨3408677, by rfl⟩ : syracuseStep 4544903 = 6817355) B6817355
theorem B1497491 : Blo 662308 1497491 := bstep (se 1 (by rfl) ⟨1123118, by rfl⟩ : syracuseStep 1497491 = 2246237) B2246237
theorem B1497545 : Blo 662308 1497545 := bstep (se 2 (by rfl) ⟨561579, by rfl⟩ : syracuseStep 1497545 = 1123159) B1123159
theorem B3365387 : Blo 662308 3365387 := bstep (se 1 (by rfl) ⟨2524040, by rfl⟩ : syracuseStep 3365387 = 5048081) B5048081
theorem B1890935 : Blo 662308 1890935 := bstep (se 1 (by rfl) ⟨1418201, by rfl⟩ : syracuseStep 1890935 = 2836403) B2836403
theorem B3365549 : Blo 662308 3365549 := bstep (se 3 (by rfl) ⟨631040, by rfl⟩ : syracuseStep 3365549 = 1262081) B1262081
theorem B1596161 : Blo 662308 1596161 := bstep (se 2 (by rfl) ⟨598560, by rfl⟩ : syracuseStep 1596161 = 1197121) B1197121
theorem B1498247 : Blo 662308 1498247 := bstep (se 1 (by rfl) ⟨1123685, by rfl⟩ : syracuseStep 1498247 = 2247371) B2247371
theorem B19127501 : Blo 662308 19127501 := bstep (se 3 (by rfl) ⟨3586406, by rfl⟩ : syracuseStep 19127501 = 7172813) B7172813
theorem B1498427 : Blo 662308 1498427 := bstep (se 1 (by rfl) ⟨1123820, by rfl⟩ : syracuseStep 1498427 = 2247641) B2247641
theorem B1498553 : Blo 662308 1498553 := bstep (se 2 (by rfl) ⟨561957, by rfl⟩ : syracuseStep 1498553 = 1123915) B1123915
theorem B745231 : Blo 662308 745231 := bstep (se 1 (by rfl) ⟨558923, by rfl⟩ : syracuseStep 745231 = 1117847) B1117847
theorem B1498895 : Blo 662308 1498895 := bstep (se 1 (by rfl) ⟨1124171, by rfl⟩ : syracuseStep 1498895 = 2248343) B2248343
theorem B1498913 : Blo 662308 1498913 := bstep (se 2 (by rfl) ⟨562092, by rfl⟩ : syracuseStep 1498913 = 1124185) B1124185
theorem B5037875 : Blo 662308 5037875 := bstep (se 1 (by rfl) ⟨3778406, by rfl⟩ : syracuseStep 5037875 = 7556813) B7556813
theorem B2842553 : Blo 662308 2842553 := bstep (se 2 (by rfl) ⟨1065957, by rfl⟩ : syracuseStep 2842553 = 2131915) B2131915
theorem B3367169 : Blo 662308 3367169 := bstep (se 2 (by rfl) ⟨1262688, by rfl⟩ : syracuseStep 3367169 = 2525377) B2525377
theorem B745735 : Blo 662308 745735 := bstep (se 1 (by rfl) ⟨559301, by rfl⟩ : syracuseStep 745735 = 1118603) B1118603
theorem B745915 : Blo 662308 745915 := bstep (se 1 (by rfl) ⟨559436, by rfl⟩ : syracuseStep 745915 = 1118873) B1118873
theorem B1368695 : Blo 662308 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B2515657 : Blo 662308 2515657 := bstep (se 2 (by rfl) ⟨943371, by rfl⟩ : syracuseStep 2515657 = 1886743) B1886743
theorem B1794935 : Blo 662308 1794935 := bstep (se 1 (by rfl) ⟨1346201, by rfl⟩ : syracuseStep 1794935 = 2692403) B2692403
theorem B746383 : Blo 662308 746383 := bstep (se 1 (by rfl) ⟨559787, by rfl⟩ : syracuseStep 746383 = 1119575) B1119575
theorem B2843545 : Blo 662308 2843545 := bstep (se 2 (by rfl) ⟨1066329, by rfl⟩ : syracuseStep 2843545 = 2132659) B2132659
theorem B1893419 : Blo 662308 1893419 := bstep (se 1 (by rfl) ⟨1420064, by rfl⟩ : syracuseStep 1893419 = 2840129) B2840129
theorem B3367979 : Blo 662308 3367979 := bstep (se 1 (by rfl) ⟨2525984, by rfl⟩ : syracuseStep 3367979 = 5051969) B5051969
theorem B1008811 : Blo 662308 1008811 := bstep (se 1 (by rfl) ⟨756608, by rfl⟩ : syracuseStep 1008811 = 1513217) B1513217
theorem B2123023 : Blo 662308 2123023 := bstep (se 1 (by rfl) ⟨1592267, by rfl⟩ : syracuseStep 2123023 = 3184535) B3184535
theorem B943417 : Blo 662308 943417 := bstep (se 2 (by rfl) ⟨353781, by rfl⟩ : syracuseStep 943417 = 707563) B707563
theorem B746887 : Blo 662308 746887 := bstep (se 1 (by rfl) ⟨560165, by rfl⟩ : syracuseStep 746887 = 1120331) B1120331
theorem B11527559 : Blo 662308 11527559 := bstep (se 1 (by rfl) ⟨8645669, by rfl⟩ : syracuseStep 11527559 = 17291339) B17291339
theorem B11494865 : Blo 662308 11494865 := bstep (se 2 (by rfl) ⟨4310574, by rfl⟩ : syracuseStep 11494865 = 8621149) B8621149
theorem B2123293 : Blo 662308 2123293 := bstep (se 3 (by rfl) ⟨398117, by rfl⟩ : syracuseStep 2123293 = 796235) B796235
theorem B747067 : Blo 662308 747067 := bstep (se 1 (by rfl) ⟨560300, by rfl⟩ : syracuseStep 747067 = 1120601) B1120601
theorem B943759 : Blo 662308 943759 := bstep (se 1 (by rfl) ⟨707819, by rfl⟩ : syracuseStep 943759 = 1415639) B1415639
theorem B7268131 : Blo 662308 7268131 := bstep (se 1 (by rfl) ⟨5451098, by rfl⟩ : syracuseStep 7268131 = 10902197) B10902197
theorem B5400371 : Blo 662308 5400371 := bstep (se 1 (by rfl) ⟨4050278, by rfl⟩ : syracuseStep 5400371 = 8100557) B8100557
theorem B1894205 : Blo 662308 1894205 := bstep (se 3 (by rfl) ⟨355163, by rfl⟩ : syracuseStep 1894205 = 710327) B710327
theorem B3073945 : Blo 662308 3073945 := bstep (se 2 (by rfl) ⟨1152729, by rfl⟩ : syracuseStep 3073945 = 2305459) B2305459
theorem B3598283 : Blo 662308 3598283 := bstep (se 1 (by rfl) ⟨2698712, by rfl⟩ : syracuseStep 3598283 = 5397425) B5397425
theorem B747535 : Blo 662308 747535 := bstep (se 1 (by rfl) ⟨560651, by rfl⟩ : syracuseStep 747535 = 1121303) B1121303
theorem B1894535 : Blo 662308 1894535 := bstep (se 1 (by rfl) ⟨1420901, by rfl⟩ : syracuseStep 1894535 = 2841803) B2841803
theorem B4778185 : Blo 662308 4778185 := bstep (se 2 (by rfl) ⟨1791819, by rfl⟩ : syracuseStep 4778185 = 3583639) B3583639
theorem B1599745 : Blo 662308 1599745 := bstep (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) B1199809
theorem B3369275 : Blo 662308 3369275 := bstep (se 1 (by rfl) ⟨2526956, by rfl⟩ : syracuseStep 3369275 = 5053913) B5053913
theorem B1599803 : Blo 662308 1599803 := bstep (se 1 (by rfl) ⟨1199852, by rfl⟩ : syracuseStep 1599803 = 2399705) B2399705
theorem B1599859 : Blo 662308 1599859 := bstep (se 1 (by rfl) ⟨1199894, by rfl⟩ : syracuseStep 1599859 = 2399789) B2399789
theorem B3369437 : Blo 662308 3369437 := bstep (se 3 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 3369437 = 1263539) B1263539
theorem B748039 : Blo 662308 748039 := bstep (se 1 (by rfl) ⟨561029, by rfl⟩ : syracuseStep 748039 = 1122059) B1122059
theorem B12118571 : Blo 662308 12118571 := bstep (se 1 (by rfl) ⟨9088928, by rfl⟩ : syracuseStep 12118571 = 18177857) B18177857
theorem B748219 : Blo 662308 748219 := bstep (se 1 (by rfl) ⟨561164, by rfl⟩ : syracuseStep 748219 = 1122329) B1122329
theorem B944887 : Blo 662308 944887 := bstep (se 1 (by rfl) ⟨708665, by rfl⟩ : syracuseStep 944887 = 1417331) B1417331
theorem B3369761 : Blo 662308 3369761 := bstep (se 2 (by rfl) ⟨1263660, by rfl⟩ : syracuseStep 3369761 = 2527321) B2527321
theorem B2517875 : Blo 662308 2517875 := bstep (se 1 (by rfl) ⟨1888406, by rfl⟩ : syracuseStep 2517875 = 3776813) B3776813
theorem B1797011 : Blo 662308 1797011 := bstep (se 1 (by rfl) ⟨1347758, by rfl⟩ : syracuseStep 1797011 = 2695517) B2695517
theorem B1436791 : Blo 662308 1436791 := bstep (se 1 (by rfl) ⟨1077593, by rfl⟩ : syracuseStep 1436791 = 2155187) B2155187
theorem B748687 : Blo 662308 748687 := bstep (se 1 (by rfl) ⟨561515, by rfl⟩ : syracuseStep 748687 = 1123031) B1123031
theorem B1600697 : Blo 662308 1600697 := bstep (se 2 (by rfl) ⟨600261, by rfl⟩ : syracuseStep 1600697 = 1200523) B1200523
theorem B3599597 : Blo 662308 3599597 := bstep (se 3 (by rfl) ⟨674924, by rfl⟩ : syracuseStep 3599597 = 1349849) B1349849
theorem B2125241 : Blo 662308 2125241 := bstep (se 2 (by rfl) ⟨796965, by rfl⟩ : syracuseStep 2125241 = 1593931) B1593931
theorem B4779485 : Blo 662308 4779485 := bstep (se 3 (by rfl) ⟨896153, by rfl⟩ : syracuseStep 4779485 = 1792307) B1792307
theorem B749191 : Blo 662308 749191 := bstep (se 1 (by rfl) ⟨561893, by rfl⟩ : syracuseStep 749191 = 1123787) B1123787
theorem B3370733 : Blo 662308 3370733 := bstep (se 3 (by rfl) ⟨632012, by rfl⟩ : syracuseStep 3370733 = 1264025) B1264025
theorem B749371 : Blo 662308 749371 := bstep (se 1 (by rfl) ⟨562028, by rfl⟩ : syracuseStep 749371 = 1124057) B1124057
theorem B1896311 : Blo 662308 1896311 := bstep (se 1 (by rfl) ⟨1422233, by rfl⟩ : syracuseStep 1896311 = 2844467) B2844467
theorem B7171993 : Blo 662308 7171993 := bstep (se 2 (by rfl) ⟨2689497, by rfl⟩ : syracuseStep 7171993 = 5378995) B5378995
theorem B2387897 : Blo 662308 2387897 := bstep (se 2 (by rfl) ⟨895461, by rfl⟩ : syracuseStep 2387897 = 1790923) B1790923
theorem B6385675 : Blo 662308 6385675 := bstep (se 1 (by rfl) ⟨4789256, by rfl⟩ : syracuseStep 6385675 = 9578513) B9578513
theorem B2125867 : Blo 662308 2125867 := bstep (se 1 (by rfl) ⟨1594400, by rfl⟩ : syracuseStep 2125867 = 3188801) B3188801
theorem B2388359 : Blo 662308 2388359 := bstep (se 1 (by rfl) ⟨1791269, by rfl⟩ : syracuseStep 2388359 = 3582539) B3582539
theorem B4780433 : Blo 662308 4780433 := bstep (se 2 (by rfl) ⟨1792662, by rfl⟩ : syracuseStep 4780433 = 3585325) B3585325
theorem B2388371 : Blo 662308 2388371 := bstep (se 1 (by rfl) ⟨1791278, by rfl⟩ : syracuseStep 2388371 = 3582557) B3582557
theorem B3371543 : Blo 662308 3371543 := bstep (se 1 (by rfl) ⟨2528657, by rfl⟩ : syracuseStep 3371543 = 5057315) B5057315
theorem B64713329 : Blo 662308 64713329 := bstep (se 2 (by rfl) ⟨24267498, by rfl⟩ : syracuseStep 64713329 = 48534997) B48534997
theorem B1897303 : Blo 662308 1897303 := bstep (se 1 (by rfl) ⟨1422977, by rfl⟩ : syracuseStep 1897303 = 2845955) B2845955
theorem B12743513 : Blo 662308 12743513 := bstep (se 2 (by rfl) ⟨4778817, by rfl⟩ : syracuseStep 12743513 = 9557635) B9557635
theorem B2520017 : Blo 662308 2520017 := bstep (se 2 (by rfl) ⟨945006, by rfl⟩ : syracuseStep 2520017 = 1890013) B1890013
theorem B2520335 : Blo 662308 2520335 := bstep (se 1 (by rfl) ⟨1890251, by rfl⟩ : syracuseStep 2520335 = 3780503) B3780503
theorem B1799453 : Blo 662308 1799453 := bstep (se 3 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 1799453 = 674795) B674795
theorem B3831077 : Blo 662308 3831077 := bstep (se 4 (by rfl) ⟨359163, by rfl⟩ : syracuseStep 3831077 = 718327) B718327
theorem B1701179 : Blo 662308 1701179 := bstep (se 1 (by rfl) ⟨1275884, by rfl⟩ : syracuseStep 1701179 = 2551769) B2551769
theorem B947575 : Blo 662308 947575 := bstep (se 1 (by rfl) ⟨710681, by rfl⟩ : syracuseStep 947575 = 1421363) B1421363
theorem B5666381 : Blo 662308 5666381 := bstep (se 3 (by rfl) ⟨1062446, by rfl⟩ : syracuseStep 5666381 = 2124893) B2124893
theorem B1799833 : Blo 662308 1799833 := bstep (se 2 (by rfl) ⟨674937, by rfl⟩ : syracuseStep 1799833 = 1349875) B1349875
theorem B948395 : Blo 662308 948395 := bstep (se 1 (by rfl) ⟨711296, by rfl⟩ : syracuseStep 948395 = 1422593) B1422593
theorem B8091893 : Blo 662308 8091893 := bstep (se 5 (by rfl) ⟨379307, by rfl⟩ : syracuseStep 8091893 = 758615) B758615
theorem B719119 : Blo 662308 719119 := bstep (se 1 (by rfl) ⟨539339, by rfl⟩ : syracuseStep 719119 = 1078679) B1078679
theorem B3832343 : Blo 662308 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B1702657 : Blo 662308 1702657 := bstep (se 2 (by rfl) ⟨638496, by rfl⟩ : syracuseStep 1702657 = 1276993) B1276993
theorem B3242753 : Blo 662308 3242753 := bstep (se 2 (by rfl) ⟨1216032, by rfl⟩ : syracuseStep 3242753 = 2432065) B2432065
theorem B12778883 : Blo 662308 12778883 := bstep (se 1 (by rfl) ⟨9584162, by rfl⟩ : syracuseStep 12778883 = 19168325) B19168325
theorem B5045651 : Blo 662308 5045651 := bstep (se 1 (by rfl) ⟨3784238, by rfl⟩ : syracuseStep 5045651 = 7568477) B7568477
theorem B2523251 : Blo 662308 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B10944827 : Blo 662308 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B2523707 : Blo 662308 2523707 := bstep (se 1 (by rfl) ⟨1892780, by rfl⟩ : syracuseStep 2523707 = 3785561) B3785561
theorem B4981421 : Blo 662308 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B4260755 : Blo 662308 4260755 := bstep (se 1 (by rfl) ⟨3195566, by rfl⟩ : syracuseStep 4260755 = 6391133) B6391133
theorem B2163631 : Blo 662308 2163631 := bstep (se 1 (by rfl) ⟨1622723, by rfl⟩ : syracuseStep 2163631 = 3245447) B3245447
theorem B40797701 : Blo 662308 40797701 := bstep (se 4 (by rfl) ⟨3824784, by rfl⟩ : syracuseStep 40797701 = 7649569) B7649569
theorem B1345081 : Blo 662308 1345081 := bstep (se 2 (by rfl) ⟨504405, by rfl⟩ : syracuseStep 1345081 = 1008811) B1008811
theorem B1345423 : Blo 662308 1345423 := bstep (se 1 (by rfl) ⟨1009067, by rfl⟩ : syracuseStep 1345423 = 2018135) B2018135
theorem B7571393 : Blo 662308 7571393 := bstep (se 2 (by rfl) ⟨2839272, by rfl⟩ : syracuseStep 7571393 = 5678545) B5678545
theorem B9865223 : Blo 662308 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B8194409 : Blo 662308 8194409 := bstep (se 2 (by rfl) ⟨3072903, by rfl⟩ : syracuseStep 8194409 = 6145807) B6145807
theorem B854491 : Blo 662308 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B4098593 : Blo 662308 4098593 := bstep (se 2 (by rfl) ⟨1536972, by rfl⟩ : syracuseStep 4098593 = 3073945) B3073945
theorem B12487493 : Blo 662308 12487493 := bstep (se 4 (by rfl) ⟨1170702, by rfl⟩ : syracuseStep 12487493 = 2341405) B2341405
theorem B2132993 : Blo 662308 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B2133145 : Blo 662308 2133145 := bstep (se 2 (by rfl) ⟨799929, by rfl⟩ : syracuseStep 2133145 = 1599859) B1599859
theorem B5049539 : Blo 662308 5049539 := bstep (se 1 (by rfl) ⟨3787154, by rfl⟩ : syracuseStep 5049539 = 7574309) B7574309
theorem B17272129 : Blo 662308 17272129 := bstep (se 2 (by rfl) ⟨6477048, by rfl⟩ : syracuseStep 17272129 = 12954097) B12954097
theorem B1117705 : Blo 662308 1117705 := bstep (se 2 (by rfl) ⟨419139, by rfl⟩ : syracuseStep 1117705 = 838279) B838279
theorem B1117867 : Blo 662308 1117867 := bstep (se 1 (by rfl) ⟨838400, by rfl⟩ : syracuseStep 1117867 = 1676801) B1676801
theorem B4853665 : Blo 662308 4853665 := bstep (se 2 (by rfl) ⟨1820124, by rfl⟩ : syracuseStep 4853665 = 3640249) B3640249
theorem B2396087 : Blo 662308 2396087 := bstep (se 1 (by rfl) ⟨1797065, by rfl⟩ : syracuseStep 2396087 = 3594131) B3594131
theorem B1118171 : Blo 662308 1118171 := bstep (se 1 (by rfl) ⟨838628, by rfl⟩ : syracuseStep 1118171 = 1677257) B1677257
theorem B1118407 : Blo 662308 1118407 := bstep (se 1 (by rfl) ⟨838805, by rfl⟩ : syracuseStep 1118407 = 1677611) B1677611
theorem B1118569 : Blo 662308 1118569 := bstep (se 2 (by rfl) ⟨419463, by rfl⟩ : syracuseStep 1118569 = 838927) B838927
theorem B2691719 : Blo 662308 2691719 := bstep (se 1 (by rfl) ⟨2018789, by rfl⟩ : syracuseStep 2691719 = 4037579) B4037579
theorem B2560697 : Blo 662308 2560697 := bstep (se 2 (by rfl) ⟨960261, by rfl⟩ : syracuseStep 2560697 = 1920523) B1920523
theorem B3773213 : Blo 662308 3773213 := bstep (se 3 (by rfl) ⟨707477, by rfl⟩ : syracuseStep 3773213 = 1414955) B1414955
theorem B12751667 : Blo 662308 12751667 := bstep (se 1 (by rfl) ⟨9563750, by rfl⟩ : syracuseStep 12751667 = 19127501) B19127501
theorem B3642185 : Blo 662308 3642185 := bstep (se 2 (by rfl) ⟨1365819, by rfl⟩ : syracuseStep 3642185 = 2731639) B2731639
theorem B1119163 : Blo 662308 1119163 := bstep (se 1 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 1119163 = 1678745) B1678745
theorem B1119271 : Blo 662308 1119271 := bstep (se 1 (by rfl) ⟨839453, by rfl⟩ : syracuseStep 1119271 = 1678907) B1678907
theorem B3413195 : Blo 662308 3413195 := bstep (se 1 (by rfl) ⟨2559896, by rfl⟩ : syracuseStep 3413195 = 5119793) B5119793
theorem B1119595 : Blo 662308 1119595 := bstep (se 1 (by rfl) ⟨839696, by rfl⟩ : syracuseStep 1119595 = 1679393) B1679393
theorem B3773897 : Blo 662308 3773897 := bstep (se 2 (by rfl) ⟨1415211, by rfl⟩ : syracuseStep 3773897 = 2830423) B2830423
theorem B2529053 : Blo 662308 2529053 := bstep (se 3 (by rfl) ⟨474197, by rfl⟩ : syracuseStep 2529053 = 948395) B948395
theorem B1120655 : Blo 662308 1120655 := bstep (se 1 (by rfl) ⟨840491, by rfl⟩ : syracuseStep 1120655 = 1680983) B1680983
theorem B2529737 : Blo 662308 2529737 := bstep (se 2 (by rfl) ⟨948651, by rfl⟩ : syracuseStep 2529737 = 1897303) B1897303
theorem B1120891 : Blo 662308 1120891 := bstep (se 1 (by rfl) ⟨840668, by rfl⟩ : syracuseStep 1120891 = 1681337) B1681337
theorem B2398855 : Blo 662308 2398855 := bstep (se 1 (by rfl) ⟨1799141, by rfl⟩ : syracuseStep 2398855 = 3598283) B3598283
theorem B4266755 : Blo 662308 4266755 := bstep (se 1 (by rfl) ⟨3200066, by rfl⟩ : syracuseStep 4266755 = 6400133) B6400133
theorem B662311 : Blo 662308 662311 := bstep (se 1 (by rfl) ⟨496733, by rfl⟩ : syracuseStep 662311 = 993467) B993467
theorem B662351 : Blo 662308 662351 := bstep (se 1 (by rfl) ⟨496763, by rfl⟩ : syracuseStep 662351 = 993527) B993527
theorem B662367 : Blo 662308 662367 := bstep (se 1 (by rfl) ⟨496775, by rfl⟩ : syracuseStep 662367 = 993551) B993551
theorem B662395 : Blo 662308 662395 := bstep (se 1 (by rfl) ⟨496796, by rfl⟩ : syracuseStep 662395 = 993593) B993593
theorem B662447 : Blo 662308 662447 := bstep (se 1 (by rfl) ⟨496835, by rfl⟩ : syracuseStep 662447 = 993671) B993671
theorem B662471 : Blo 662308 662471 := bstep (se 1 (by rfl) ⟨496853, by rfl⟩ : syracuseStep 662471 = 993707) B993707
theorem B662491 : Blo 662308 662491 := bstep (se 1 (by rfl) ⟨496868, by rfl⟩ : syracuseStep 662491 = 993737) B993737
theorem B662567 : Blo 662308 662567 := bstep (se 1 (by rfl) ⟨496925, by rfl⟩ : syracuseStep 662567 = 993851) B993851
theorem B662607 : Blo 662308 662607 := bstep (se 1 (by rfl) ⟨496955, by rfl⟩ : syracuseStep 662607 = 993911) B993911
theorem B662623 : Blo 662308 662623 := bstep (se 1 (by rfl) ⟨496967, by rfl⟩ : syracuseStep 662623 = 993935) B993935
theorem B662651 : Blo 662308 662651 := bstep (se 1 (by rfl) ⟨496988, by rfl⟩ : syracuseStep 662651 = 993977) B993977
theorem B2235545 : Blo 662308 2235545 := bstep (se 2 (by rfl) ⟨838329, by rfl⟩ : syracuseStep 2235545 = 1676659) B1676659
theorem B662703 : Blo 662308 662703 := bstep (se 1 (by rfl) ⟨497027, by rfl⟩ : syracuseStep 662703 = 994055) B994055
theorem B662727 : Blo 662308 662727 := bstep (se 1 (by rfl) ⟨497045, by rfl⟩ : syracuseStep 662727 = 994091) B994091
theorem B662747 : Blo 662308 662747 := bstep (se 1 (by rfl) ⟨497060, by rfl⟩ : syracuseStep 662747 = 994121) B994121
theorem B1678583 : Blo 662308 1678583 := bstep (se 1 (by rfl) ⟨1258937, by rfl⟩ : syracuseStep 1678583 = 2517875) B2517875
theorem B662823 : Blo 662308 662823 := bstep (se 1 (by rfl) ⟨497117, by rfl⟩ : syracuseStep 662823 = 994235) B994235
theorem B662863 : Blo 662308 662863 := bstep (se 1 (by rfl) ⟨497147, by rfl⟩ : syracuseStep 662863 = 994295) B994295
theorem B662879 : Blo 662308 662879 := bstep (se 1 (by rfl) ⟨497159, by rfl⟩ : syracuseStep 662879 = 994319) B994319
theorem B662907 : Blo 662308 662907 := bstep (se 1 (by rfl) ⟨497180, by rfl⟩ : syracuseStep 662907 = 994361) B994361
theorem B662959 : Blo 662308 662959 := bstep (se 1 (by rfl) ⟨497219, by rfl⟩ : syracuseStep 662959 = 994439) B994439
theorem B662983 : Blo 662308 662983 := bstep (se 1 (by rfl) ⟨497237, by rfl⟩ : syracuseStep 662983 = 994475) B994475
theorem B663003 : Blo 662308 663003 := bstep (se 1 (by rfl) ⟨497252, by rfl⟩ : syracuseStep 663003 = 994505) B994505
theorem B1121755 : Blo 662308 1121755 := bstep (se 1 (by rfl) ⟨841316, by rfl⟩ : syracuseStep 1121755 = 1682633) B1682633
theorem B2399777 : Blo 662308 2399777 := bstep (se 2 (by rfl) ⟨899916, by rfl⟩ : syracuseStep 2399777 = 1799833) B1799833
theorem B663079 : Blo 662308 663079 := bstep (se 1 (by rfl) ⟨497309, by rfl⟩ : syracuseStep 663079 = 994619) B994619
theorem B663119 : Blo 662308 663119 := bstep (se 1 (by rfl) ⟨497339, by rfl⟩ : syracuseStep 663119 = 994679) B994679
theorem B663135 : Blo 662308 663135 := bstep (se 1 (by rfl) ⟨497351, by rfl⟩ : syracuseStep 663135 = 994703) B994703
theorem B663163 : Blo 662308 663163 := bstep (se 1 (by rfl) ⟨497372, by rfl⟩ : syracuseStep 663163 = 994745) B994745
theorem B1416827 : Blo 662308 1416827 := bstep (se 1 (by rfl) ⟨1062620, by rfl⟩ : syracuseStep 1416827 = 2125241) B2125241
theorem B3186323 : Blo 662308 3186323 := bstep (se 1 (by rfl) ⟨2389742, by rfl⟩ : syracuseStep 3186323 = 4779485) B4779485
theorem B663215 : Blo 662308 663215 := bstep (se 1 (by rfl) ⟨497411, by rfl⟩ : syracuseStep 663215 = 994823) B994823
theorem B663239 : Blo 662308 663239 := bstep (se 1 (by rfl) ⟨497429, by rfl⟩ : syracuseStep 663239 = 994859) B994859
theorem B663259 : Blo 662308 663259 := bstep (se 1 (by rfl) ⟨497444, by rfl⟩ : syracuseStep 663259 = 994889) B994889
theorem B663335 : Blo 662308 663335 := bstep (se 1 (by rfl) ⟨497501, by rfl⟩ : syracuseStep 663335 = 995003) B995003
theorem B663375 : Blo 662308 663375 := bstep (se 1 (by rfl) ⟨497531, by rfl⟩ : syracuseStep 663375 = 995063) B995063
theorem B663391 : Blo 662308 663391 := bstep (se 1 (by rfl) ⟨497543, by rfl⟩ : syracuseStep 663391 = 995087) B995087
theorem B663419 : Blo 662308 663419 := bstep (se 1 (by rfl) ⟨497564, by rfl⟩ : syracuseStep 663419 = 995129) B995129
theorem B663471 : Blo 662308 663471 := bstep (se 1 (by rfl) ⟨497603, by rfl⟩ : syracuseStep 663471 = 995207) B995207
theorem B663495 : Blo 662308 663495 := bstep (se 1 (by rfl) ⟨497621, by rfl⟩ : syracuseStep 663495 = 995243) B995243
theorem B663515 : Blo 662308 663515 := bstep (se 1 (by rfl) ⟨497636, by rfl⟩ : syracuseStep 663515 = 995273) B995273
theorem B663591 : Blo 662308 663591 := bstep (se 1 (by rfl) ⟨497693, by rfl⟩ : syracuseStep 663591 = 995387) B995387
theorem B663631 : Blo 662308 663631 := bstep (se 1 (by rfl) ⟨497723, by rfl⟩ : syracuseStep 663631 = 995447) B995447
theorem B1122383 : Blo 662308 1122383 := bstep (se 1 (by rfl) ⟨841787, by rfl⟩ : syracuseStep 1122383 = 1683575) B1683575
theorem B663647 : Blo 662308 663647 := bstep (se 1 (by rfl) ⟨497735, by rfl⟩ : syracuseStep 663647 = 995471) B995471
theorem B663675 : Blo 662308 663675 := bstep (se 1 (by rfl) ⟨497756, by rfl⟩ : syracuseStep 663675 = 995513) B995513
theorem B729211 : Blo 662308 729211 := bstep (se 1 (by rfl) ⟨546908, by rfl⟩ : syracuseStep 729211 = 1093817) B1093817
theorem B16425109 : Blo 662308 16425109 := bstep (se 6 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 16425109 = 769927) B769927
theorem B663727 : Blo 662308 663727 := bstep (se 1 (by rfl) ⟨497795, by rfl⟩ : syracuseStep 663727 = 995591) B995591
theorem B7282865 : Blo 662308 7282865 := bstep (se 2 (by rfl) ⟨2731074, by rfl⟩ : syracuseStep 7282865 = 5462149) B5462149
theorem B663751 : Blo 662308 663751 := bstep (se 1 (by rfl) ⟨497813, by rfl⟩ : syracuseStep 663751 = 995627) B995627
theorem B663771 : Blo 662308 663771 := bstep (se 1 (by rfl) ⟨497828, by rfl⟩ : syracuseStep 663771 = 995657) B995657
theorem B3186955 : Blo 662308 3186955 := bstep (se 1 (by rfl) ⟨2390216, by rfl⟩ : syracuseStep 3186955 = 4780433) B4780433
theorem B663847 : Blo 662308 663847 := bstep (se 1 (by rfl) ⟨497885, by rfl⟩ : syracuseStep 663847 = 995771) B995771
theorem B7545149 : Blo 662308 7545149 := bstep (se 3 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 7545149 = 2829431) B2829431
theorem B2236733 : Blo 662308 2236733 := bstep (se 3 (by rfl) ⟨419387, by rfl⟩ : syracuseStep 2236733 = 838775) B838775
theorem B663887 : Blo 662308 663887 := bstep (se 1 (by rfl) ⟨497915, by rfl⟩ : syracuseStep 663887 = 995831) B995831
theorem B663903 : Blo 662308 663903 := bstep (se 1 (by rfl) ⟨497927, by rfl⟩ : syracuseStep 663903 = 995855) B995855
theorem B958825 : Blo 662308 958825 := bstep (se 2 (by rfl) ⟨359559, by rfl⟩ : syracuseStep 958825 = 719119) B719119
theorem B663931 : Blo 662308 663931 := bstep (se 1 (by rfl) ⟨497948, by rfl⟩ : syracuseStep 663931 = 995897) B995897
theorem B663983 : Blo 662308 663983 := bstep (se 1 (by rfl) ⟨497987, by rfl⟩ : syracuseStep 663983 = 995975) B995975
theorem B664007 : Blo 662308 664007 := bstep (se 1 (by rfl) ⟨498005, by rfl⟩ : syracuseStep 664007 = 996011) B996011
theorem B664027 : Blo 662308 664027 := bstep (se 1 (by rfl) ⟨498020, by rfl⟩ : syracuseStep 664027 = 996041) B996041
theorem B664103 : Blo 662308 664103 := bstep (se 1 (by rfl) ⟨498077, by rfl⟩ : syracuseStep 664103 = 996155) B996155
theorem B8495675 : Blo 662308 8495675 := bstep (se 1 (by rfl) ⟨6371756, by rfl⟩ : syracuseStep 8495675 = 12743513) B12743513
theorem B664143 : Blo 662308 664143 := bstep (se 1 (by rfl) ⟨498107, by rfl⟩ : syracuseStep 664143 = 996215) B996215
theorem B664159 : Blo 662308 664159 := bstep (se 1 (by rfl) ⟨498119, by rfl⟩ : syracuseStep 664159 = 996239) B996239
theorem B664187 : Blo 662308 664187 := bstep (se 1 (by rfl) ⟨498140, by rfl⟩ : syracuseStep 664187 = 996281) B996281
theorem B1680011 : Blo 662308 1680011 := bstep (se 1 (by rfl) ⟨1260008, by rfl⟩ : syracuseStep 1680011 = 2520017) B2520017
theorem B664239 : Blo 662308 664239 := bstep (se 1 (by rfl) ⟨498179, by rfl⟩ : syracuseStep 664239 = 996359) B996359
theorem B664263 : Blo 662308 664263 := bstep (se 1 (by rfl) ⟨498197, by rfl⟩ : syracuseStep 664263 = 996395) B996395
theorem B664283 : Blo 662308 664283 := bstep (se 1 (by rfl) ⟨498212, by rfl⟩ : syracuseStep 664283 = 996425) B996425
theorem B664359 : Blo 662308 664359 := bstep (se 1 (by rfl) ⟨498269, by rfl⟩ : syracuseStep 664359 = 996539) B996539
theorem B1418057 : Blo 662308 1418057 := bstep (se 2 (by rfl) ⟨531771, by rfl⟩ : syracuseStep 1418057 = 1063543) B1063543
theorem B664399 : Blo 662308 664399 := bstep (se 1 (by rfl) ⟨498299, by rfl⟩ : syracuseStep 664399 = 996599) B996599
theorem B1680223 : Blo 662308 1680223 := bstep (se 1 (by rfl) ⟨1260167, by rfl⟩ : syracuseStep 1680223 = 2520335) B2520335
theorem B664415 : Blo 662308 664415 := bstep (se 1 (by rfl) ⟨498311, by rfl⟩ : syracuseStep 664415 = 996623) B996623
theorem B664443 : Blo 662308 664443 := bstep (se 1 (by rfl) ⟨498332, by rfl⟩ : syracuseStep 664443 = 996665) B996665
theorem B664495 : Blo 662308 664495 := bstep (se 1 (by rfl) ⟨498371, by rfl⟩ : syracuseStep 664495 = 996743) B996743
theorem B1123247 : Blo 662308 1123247 := bstep (se 1 (by rfl) ⟨842435, by rfl⟩ : syracuseStep 1123247 = 1684871) B1684871
theorem B664519 : Blo 662308 664519 := bstep (se 1 (by rfl) ⟨498389, by rfl⟩ : syracuseStep 664519 = 996779) B996779
theorem B664539 : Blo 662308 664539 := bstep (se 1 (by rfl) ⟨498404, by rfl⟩ : syracuseStep 664539 = 996809) B996809
theorem B2270209 : Blo 662308 2270209 := bstep (se 2 (by rfl) ⟨851328, by rfl⟩ : syracuseStep 2270209 = 1702657) B1702657
theorem B664615 : Blo 662308 664615 := bstep (se 1 (by rfl) ⟨498461, by rfl⟩ : syracuseStep 664615 = 996923) B996923
theorem B3777587 : Blo 662308 3777587 := bstep (se 1 (by rfl) ⟨2833190, by rfl⟩ : syracuseStep 3777587 = 5666381) B5666381
theorem B664655 : Blo 662308 664655 := bstep (se 1 (by rfl) ⟨498491, by rfl⟩ : syracuseStep 664655 = 996983) B996983
theorem B664671 : Blo 662308 664671 := bstep (se 1 (by rfl) ⟨498503, by rfl⟩ : syracuseStep 664671 = 997007) B997007
theorem B664699 : Blo 662308 664699 := bstep (se 1 (by rfl) ⟨498524, by rfl⟩ : syracuseStep 664699 = 997049) B997049
theorem B2237597 : Blo 662308 2237597 := bstep (se 3 (by rfl) ⟨419549, by rfl⟩ : syracuseStep 2237597 = 839099) B839099
theorem B664751 : Blo 662308 664751 := bstep (se 1 (by rfl) ⟨498563, by rfl⟩ : syracuseStep 664751 = 997127) B997127
theorem B664775 : Blo 662308 664775 := bstep (se 1 (by rfl) ⟨498581, by rfl⟩ : syracuseStep 664775 = 997163) B997163
theorem B664795 : Blo 662308 664795 := bstep (se 1 (by rfl) ⟨498596, by rfl⟩ : syracuseStep 664795 = 997193) B997193
theorem B664871 : Blo 662308 664871 := bstep (se 1 (by rfl) ⟨498653, by rfl⟩ : syracuseStep 664871 = 997307) B997307
theorem B664911 : Blo 662308 664911 := bstep (se 1 (by rfl) ⟨498683, by rfl⟩ : syracuseStep 664911 = 997367) B997367
theorem B664927 : Blo 662308 664927 := bstep (se 1 (by rfl) ⟨498695, by rfl⟩ : syracuseStep 664927 = 997391) B997391
theorem B1123679 : Blo 662308 1123679 := bstep (se 1 (by rfl) ⟨842759, by rfl⟩ : syracuseStep 1123679 = 1685519) B1685519
theorem B664955 : Blo 662308 664955 := bstep (se 1 (by rfl) ⟨498716, by rfl⟩ : syracuseStep 664955 = 997433) B997433
theorem B665007 : Blo 662308 665007 := bstep (se 1 (by rfl) ⟨498755, by rfl⟩ : syracuseStep 665007 = 997511) B997511
theorem B665031 : Blo 662308 665031 := bstep (se 1 (by rfl) ⟨498773, by rfl⟩ : syracuseStep 665031 = 997547) B997547
theorem B665051 : Blo 662308 665051 := bstep (se 1 (by rfl) ⟨498788, by rfl⟩ : syracuseStep 665051 = 997577) B997577
theorem B665127 : Blo 662308 665127 := bstep (se 1 (by rfl) ⟨498845, by rfl⟩ : syracuseStep 665127 = 997691) B997691
theorem B665167 : Blo 662308 665167 := bstep (se 1 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 665167 = 997751) B997751
theorem B665183 : Blo 662308 665183 := bstep (se 1 (by rfl) ⟨498887, by rfl⟩ : syracuseStep 665183 = 997775) B997775
theorem B665211 : Blo 662308 665211 := bstep (se 1 (by rfl) ⟨498908, by rfl⟩ : syracuseStep 665211 = 997817) B997817
theorem B665263 : Blo 662308 665263 := bstep (se 1 (by rfl) ⟨498947, by rfl⟩ : syracuseStep 665263 = 997895) B997895
theorem B2238137 : Blo 662308 2238137 := bstep (se 2 (by rfl) ⟨839301, by rfl⟩ : syracuseStep 2238137 = 1678603) B1678603
theorem B665287 : Blo 662308 665287 := bstep (se 1 (by rfl) ⟨498965, by rfl⟩ : syracuseStep 665287 = 997931) B997931
theorem B665307 : Blo 662308 665307 := bstep (se 1 (by rfl) ⟨498980, by rfl⟩ : syracuseStep 665307 = 997961) B997961
theorem B6137593 : Blo 662308 6137593 := bstep (se 2 (by rfl) ⟨2301597, by rfl⟩ : syracuseStep 6137593 = 4603195) B4603195
theorem B1681145 : Blo 662308 1681145 := bstep (se 2 (by rfl) ⟨630429, by rfl⟩ : syracuseStep 1681145 = 1260859) B1260859
theorem B665383 : Blo 662308 665383 := bstep (se 1 (by rfl) ⟨499037, by rfl⟩ : syracuseStep 665383 = 998075) B998075
theorem B665423 : Blo 662308 665423 := bstep (se 1 (by rfl) ⟨499067, by rfl⟩ : syracuseStep 665423 = 998135) B998135
theorem B665439 : Blo 662308 665439 := bstep (se 1 (by rfl) ⟨499079, by rfl⟩ : syracuseStep 665439 = 998159) B998159
theorem B665467 : Blo 662308 665467 := bstep (se 1 (by rfl) ⟨499100, by rfl⟩ : syracuseStep 665467 = 998201) B998201
theorem B1124239 : Blo 662308 1124239 := bstep (se 1 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 1124239 = 1686359) B1686359
theorem B665519 : Blo 662308 665519 := bstep (se 1 (by rfl) ⟨499139, by rfl⟩ : syracuseStep 665519 = 998279) B998279
theorem B665543 : Blo 662308 665543 := bstep (se 1 (by rfl) ⟨499157, by rfl⟩ : syracuseStep 665543 = 998315) B998315
theorem B665563 : Blo 662308 665563 := bstep (se 1 (by rfl) ⟨499172, by rfl⟩ : syracuseStep 665563 = 998345) B998345
theorem B665639 : Blo 662308 665639 := bstep (se 1 (by rfl) ⟨499229, by rfl⟩ : syracuseStep 665639 = 998459) B998459
theorem B665679 : Blo 662308 665679 := bstep (se 1 (by rfl) ⟨499259, by rfl⟩ : syracuseStep 665679 = 998519) B998519
theorem B665695 : Blo 662308 665695 := bstep (se 1 (by rfl) ⟨499271, by rfl⟩ : syracuseStep 665695 = 998543) B998543
theorem B665723 : Blo 662308 665723 := bstep (se 1 (by rfl) ⟨499292, by rfl⟩ : syracuseStep 665723 = 998585) B998585
theorem B665775 : Blo 662308 665775 := bstep (se 1 (by rfl) ⟨499331, by rfl⟩ : syracuseStep 665775 = 998663) B998663
theorem B993479 : Blo 662308 993479 := bstep (se 1 (by rfl) ⟨745109, by rfl⟩ : syracuseStep 993479 = 1490219) B1490219
theorem B665799 : Blo 662308 665799 := bstep (se 1 (by rfl) ⟨499349, by rfl⟩ : syracuseStep 665799 = 998699) B998699
theorem B665819 : Blo 662308 665819 := bstep (se 1 (by rfl) ⟨499364, by rfl⟩ : syracuseStep 665819 = 998729) B998729
theorem B2238731 : Blo 662308 2238731 := bstep (se 1 (by rfl) ⟨1679048, by rfl⟩ : syracuseStep 2238731 = 3358097) B3358097
theorem B665895 : Blo 662308 665895 := bstep (se 1 (by rfl) ⟨499421, by rfl⟩ : syracuseStep 665895 = 998843) B998843
theorem B5056829 : Blo 662308 5056829 := bstep (se 3 (by rfl) ⟨948155, by rfl⟩ : syracuseStep 5056829 = 1896311) B1896311
theorem B665935 : Blo 662308 665935 := bstep (se 1 (by rfl) ⟨499451, by rfl⟩ : syracuseStep 665935 = 998903) B998903
theorem B665951 : Blo 662308 665951 := bstep (se 1 (by rfl) ⟨499463, by rfl⟩ : syracuseStep 665951 = 998927) B998927
theorem B993641 : Blo 662308 993641 := bstep (se 2 (by rfl) ⟨372615, by rfl⟩ : syracuseStep 993641 = 745231) B745231
theorem B665979 : Blo 662308 665979 := bstep (se 1 (by rfl) ⟨499484, by rfl⟩ : syracuseStep 665979 = 998969) B998969
theorem B1681793 : Blo 662308 1681793 := bstep (se 2 (by rfl) ⟨630672, by rfl⟩ : syracuseStep 1681793 = 1261345) B1261345
theorem B666031 : Blo 662308 666031 := bstep (se 1 (by rfl) ⟨499523, by rfl⟩ : syracuseStep 666031 = 999047) B999047
theorem B993719 : Blo 662308 993719 := bstep (se 1 (by rfl) ⟨745289, by rfl⟩ : syracuseStep 993719 = 1490579) B1490579
theorem B666055 : Blo 662308 666055 := bstep (se 1 (by rfl) ⟨499541, by rfl⟩ : syracuseStep 666055 = 999083) B999083
theorem B993755 : Blo 662308 993755 := bstep (se 1 (by rfl) ⟨745316, by rfl⟩ : syracuseStep 993755 = 1490633) B1490633
theorem B666075 : Blo 662308 666075 := bstep (se 1 (by rfl) ⟨499556, by rfl⟩ : syracuseStep 666075 = 999113) B999113
theorem B7580141 : Blo 662308 7580141 := bstep (se 3 (by rfl) ⟨1421276, by rfl⟩ : syracuseStep 7580141 = 2842553) B2842553
theorem B2239001 : Blo 662308 2239001 := bstep (se 2 (by rfl) ⟨839625, by rfl⟩ : syracuseStep 2239001 = 1679251) B1679251
theorem B666151 : Blo 662308 666151 := bstep (se 1 (by rfl) ⟨499613, by rfl⟩ : syracuseStep 666151 = 999227) B999227
theorem B666191 : Blo 662308 666191 := bstep (se 1 (by rfl) ⟨499643, by rfl⟩ : syracuseStep 666191 = 999287) B999287
theorem B666207 : Blo 662308 666207 := bstep (se 1 (by rfl) ⟨499655, by rfl⟩ : syracuseStep 666207 = 999311) B999311
theorem B666235 : Blo 662308 666235 := bstep (se 1 (by rfl) ⟨499676, by rfl⟩ : syracuseStep 666235 = 999353) B999353
theorem B666287 : Blo 662308 666287 := bstep (se 1 (by rfl) ⟨499715, by rfl⟩ : syracuseStep 666287 = 999431) B999431
theorem B994223 : Blo 662308 994223 := bstep (se 1 (by rfl) ⟨745667, by rfl⟩ : syracuseStep 994223 = 1491335) B1491335
theorem B994313 : Blo 662308 994313 := bstep (se 2 (by rfl) ⟨372867, by rfl⟩ : syracuseStep 994313 = 745735) B745735
theorem B994343 : Blo 662308 994343 := bstep (se 1 (by rfl) ⟨745757, by rfl⟩ : syracuseStep 994343 = 1491515) B1491515
theorem B994427 : Blo 662308 994427 := bstep (se 1 (by rfl) ⟨745820, by rfl⟩ : syracuseStep 994427 = 1491641) B1491641
theorem B1682603 : Blo 662308 1682603 := bstep (se 1 (by rfl) ⟨1261952, by rfl⟩ : syracuseStep 1682603 = 2523905) B2523905
theorem B994553 : Blo 662308 994553 := bstep (se 2 (by rfl) ⟨372957, by rfl⟩ : syracuseStep 994553 = 745915) B745915
theorem B994655 : Blo 662308 994655 := bstep (se 1 (by rfl) ⟨745991, by rfl⟩ : syracuseStep 994655 = 1491983) B1491983
theorem B994667 : Blo 662308 994667 := bstep (se 1 (by rfl) ⟨746000, by rfl⟩ : syracuseStep 994667 = 1492001) B1492001
theorem B10792435 : Blo 662308 10792435 := bstep (se 1 (by rfl) ⟨8094326, by rfl⟩ : syracuseStep 10792435 = 16188653) B16188653
theorem B994895 : Blo 662308 994895 := bstep (se 1 (by rfl) ⟨746171, by rfl⟩ : syracuseStep 994895 = 1492343) B1492343
theorem B3354209 : Blo 662308 3354209 := bstep (se 2 (by rfl) ⟨1257828, by rfl⟩ : syracuseStep 3354209 = 2515657) B2515657
theorem B2240135 : Blo 662308 2240135 := bstep (se 1 (by rfl) ⟨1680101, by rfl⟩ : syracuseStep 2240135 = 3360203) B3360203
theorem B2240189 : Blo 662308 2240189 := bstep (se 3 (by rfl) ⟨420035, by rfl⟩ : syracuseStep 2240189 = 840071) B840071
theorem B995015 : Blo 662308 995015 := bstep (se 1 (by rfl) ⟨746261, by rfl⟩ : syracuseStep 995015 = 1492523) B1492523
theorem B6368989 : Blo 662308 6368989 := bstep (se 3 (by rfl) ⟨1194185, by rfl⟩ : syracuseStep 6368989 = 2388371) B2388371
theorem B2240351 : Blo 662308 2240351 := bstep (se 1 (by rfl) ⟨1680263, by rfl⟩ : syracuseStep 2240351 = 3360527) B3360527
theorem B995177 : Blo 662308 995177 := bstep (se 2 (by rfl) ⟨373191, by rfl⟩ : syracuseStep 995177 = 746383) B746383
theorem B995255 : Blo 662308 995255 := bstep (se 1 (by rfl) ⟨746441, by rfl⟩ : syracuseStep 995255 = 1492883) B1492883
theorem B1912763 : Blo 662308 1912763 := bstep (se 1 (by rfl) ⟨1434572, by rfl⟩ : syracuseStep 1912763 = 2869145) B2869145
theorem B1421243 : Blo 662308 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B995291 : Blo 662308 995291 := bstep (se 1 (by rfl) ⟨746468, by rfl⟩ : syracuseStep 995291 = 1492937) B1492937
theorem B2240513 : Blo 662308 2240513 := bstep (se 2 (by rfl) ⟨840192, by rfl⟩ : syracuseStep 2240513 = 1680385) B1680385
theorem B1683463 : Blo 662308 1683463 := bstep (se 1 (by rfl) ⟨1262597, by rfl⟩ : syracuseStep 1683463 = 2525195) B2525195
theorem B3190799 : Blo 662308 3190799 := bstep (se 1 (by rfl) ⟨2393099, by rfl⟩ : syracuseStep 3190799 = 4786199) B4786199
theorem B3649853 : Blo 662308 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B2830697 : Blo 662308 2830697 := bstep (se 2 (by rfl) ⟨1061511, by rfl⟩ : syracuseStep 2830697 = 2123023) B2123023
theorem B995759 : Blo 662308 995759 := bstep (se 1 (by rfl) ⟨746819, by rfl⟩ : syracuseStep 995759 = 1493639) B1493639
theorem B799195 : Blo 662308 799195 := bstep (se 1 (by rfl) ⟨599396, by rfl⟩ : syracuseStep 799195 = 1198793) B1198793
theorem B995849 : Blo 662308 995849 := bstep (se 2 (by rfl) ⟨373443, by rfl⟩ : syracuseStep 995849 = 746887) B746887
theorem B995879 : Blo 662308 995879 := bstep (se 1 (by rfl) ⟨746909, by rfl⟩ : syracuseStep 995879 = 1493819) B1493819
theorem B995963 : Blo 662308 995963 := bstep (se 1 (by rfl) ⟨746972, by rfl⟩ : syracuseStep 995963 = 1493945) B1493945
theorem B1684091 : Blo 662308 1684091 := bstep (se 1 (by rfl) ⟨1263068, by rfl⟩ : syracuseStep 1684091 = 2526137) B2526137
theorem B2831057 : Blo 662308 2831057 := bstep (se 2 (by rfl) ⟨1061646, by rfl⟩ : syracuseStep 2831057 = 2123293) B2123293
theorem B996089 : Blo 662308 996089 := bstep (se 2 (by rfl) ⟨373533, by rfl⟩ : syracuseStep 996089 = 747067) B747067
theorem B2241323 : Blo 662308 2241323 := bstep (se 1 (by rfl) ⟨1680992, by rfl⟩ : syracuseStep 2241323 = 3361985) B3361985
theorem B996191 : Blo 662308 996191 := bstep (se 1 (by rfl) ⟨747143, by rfl⟩ : syracuseStep 996191 = 1494287) B1494287
theorem B1258345 : Blo 662308 1258345 := bstep (se 2 (by rfl) ⟨471879, by rfl⟩ : syracuseStep 1258345 = 943759) B943759
theorem B996203 : Blo 662308 996203 := bstep (se 1 (by rfl) ⟨747152, by rfl⟩ : syracuseStep 996203 = 1494305) B1494305
theorem B1684385 : Blo 662308 1684385 := bstep (se 2 (by rfl) ⟨631644, by rfl⟩ : syracuseStep 1684385 = 1263289) B1263289
theorem B3355667 : Blo 662308 3355667 := bstep (se 1 (by rfl) ⟨2516750, by rfl⟩ : syracuseStep 3355667 = 5033501) B5033501
theorem B2241593 : Blo 662308 2241593 := bstep (se 2 (by rfl) ⟨840597, by rfl⟩ : syracuseStep 2241593 = 1681195) B1681195
theorem B996431 : Blo 662308 996431 := bstep (se 1 (by rfl) ⟨747323, by rfl⟩ : syracuseStep 996431 = 1494647) B1494647
theorem B36844631 : Blo 662308 36844631 := bstep (se 1 (by rfl) ⟨27633473, by rfl⟩ : syracuseStep 36844631 = 55266947) B55266947
theorem B1062011 : Blo 662308 1062011 := bstep (se 1 (by rfl) ⟨796508, by rfl⟩ : syracuseStep 1062011 = 1593017) B1593017
theorem B996551 : Blo 662308 996551 := bstep (se 1 (by rfl) ⟨747413, by rfl⟩ : syracuseStep 996551 = 1494827) B1494827
theorem B996713 : Blo 662308 996713 := bstep (se 2 (by rfl) ⟨373767, by rfl⟩ : syracuseStep 996713 = 747535) B747535
theorem B2241917 : Blo 662308 2241917 := bstep (se 3 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 2241917 = 840719) B840719
theorem B996791 : Blo 662308 996791 := bstep (se 1 (by rfl) ⟨747593, by rfl⟩ : syracuseStep 996791 = 1495187) B1495187
theorem B996827 : Blo 662308 996827 := bstep (se 1 (by rfl) ⟨747620, by rfl⟩ : syracuseStep 996827 = 1495241) B1495241
theorem B6370913 : Blo 662308 6370913 := bstep (se 2 (by rfl) ⟨2389092, by rfl⟩ : syracuseStep 6370913 = 4778185) B4778185
theorem B2242187 : Blo 662308 2242187 := bstep (se 1 (by rfl) ⟨1681640, by rfl⟩ : syracuseStep 2242187 = 3363281) B3363281
theorem B1259219 : Blo 662308 1259219 := bstep (se 1 (by rfl) ⟨944414, by rfl⟩ : syracuseStep 1259219 = 1888829) B1888829
theorem B10762145 : Blo 662308 10762145 := bstep (se 2 (by rfl) ⟨4035804, by rfl⟩ : syracuseStep 10762145 = 8071609) B8071609
theorem B1914799 : Blo 662308 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B997295 : Blo 662308 997295 := bstep (se 1 (by rfl) ⟨747971, by rfl⟩ : syracuseStep 997295 = 1495943) B1495943
theorem B997385 : Blo 662308 997385 := bstep (se 2 (by rfl) ⟨374019, by rfl⟩ : syracuseStep 997385 = 748039) B748039
theorem B997415 : Blo 662308 997415 := bstep (se 1 (by rfl) ⟨748061, by rfl⟩ : syracuseStep 997415 = 1496123) B1496123
theorem B4798541 : Blo 662308 4798541 := bstep (se 3 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 4798541 = 1799453) B1799453
theorem B997499 : Blo 662308 997499 := bstep (se 1 (by rfl) ⟨748124, by rfl⟩ : syracuseStep 997499 = 1496249) B1496249
theorem B997625 : Blo 662308 997625 := bstep (se 2 (by rfl) ⟨374109, by rfl⟩ : syracuseStep 997625 = 748219) B748219
theorem B1259849 : Blo 662308 1259849 := bstep (se 2 (by rfl) ⟨472443, by rfl⟩ : syracuseStep 1259849 = 944887) B944887
theorem B2308439 : Blo 662308 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B997727 : Blo 662308 997727 := bstep (se 1 (by rfl) ⟨748295, by rfl⟩ : syracuseStep 997727 = 1496591) B1496591
theorem B997739 : Blo 662308 997739 := bstep (se 1 (by rfl) ⟨748304, by rfl⟩ : syracuseStep 997739 = 1496609) B1496609
theorem B2243105 : Blo 662308 2243105 := bstep (se 2 (by rfl) ⟨841164, by rfl⟩ : syracuseStep 2243105 = 1682329) B1682329
theorem B1686055 : Blo 662308 1686055 := bstep (se 1 (by rfl) ⟨1264541, by rfl⟩ : syracuseStep 1686055 = 2529083) B2529083
theorem B997967 : Blo 662308 997967 := bstep (se 1 (by rfl) ⟨748475, by rfl⟩ : syracuseStep 997967 = 1496951) B1496951
theorem B998087 : Blo 662308 998087 := bstep (se 1 (by rfl) ⟨748565, by rfl⟩ : syracuseStep 998087 = 1497131) B1497131
theorem B2243321 : Blo 662308 2243321 := bstep (se 2 (by rfl) ⟨841245, by rfl⟩ : syracuseStep 2243321 = 1682491) B1682491
theorem B1915721 : Blo 662308 1915721 := bstep (se 2 (by rfl) ⟨718395, by rfl⟩ : syracuseStep 1915721 = 1436791) B1436791
theorem B998249 : Blo 662308 998249 := bstep (se 2 (by rfl) ⟨374343, by rfl⟩ : syracuseStep 998249 = 748687) B748687
theorem B1686379 : Blo 662308 1686379 := bstep (se 1 (by rfl) ⟨1264784, by rfl⟩ : syracuseStep 1686379 = 2529569) B2529569
theorem B3029935 : Blo 662308 3029935 := bstep (se 1 (by rfl) ⟨2272451, by rfl⟩ : syracuseStep 3029935 = 4544903) B4544903
theorem B998327 : Blo 662308 998327 := bstep (se 1 (by rfl) ⟨748745, by rfl⟩ : syracuseStep 998327 = 1497491) B1497491
theorem B998363 : Blo 662308 998363 := bstep (se 1 (by rfl) ⟨748772, by rfl⟩ : syracuseStep 998363 = 1497545) B1497545
theorem B2243591 : Blo 662308 2243591 := bstep (se 1 (by rfl) ⟨1682693, by rfl⟩ : syracuseStep 2243591 = 3365387) B3365387
theorem B1260623 : Blo 662308 1260623 := bstep (se 1 (by rfl) ⟨945467, by rfl⟩ : syracuseStep 1260623 = 1890935) B1890935
theorem B2243699 : Blo 662308 2243699 := bstep (se 1 (by rfl) ⟨1682774, by rfl⟩ : syracuseStep 2243699 = 3365549) B3365549
theorem B1064107 : Blo 662308 1064107 := bstep (se 1 (by rfl) ⟨798080, by rfl⟩ : syracuseStep 1064107 = 1596161) B1596161
theorem B2243969 : Blo 662308 2243969 := bstep (se 2 (by rfl) ⟨841488, by rfl⟩ : syracuseStep 2243969 = 1682977) B1682977
theorem B2014607 : Blo 662308 2014607 := bstep (se 1 (by rfl) ⟨1510955, by rfl⟩ : syracuseStep 2014607 = 3021911) B3021911
theorem B998831 : Blo 662308 998831 := bstep (se 1 (by rfl) ⟨749123, by rfl⟩ : syracuseStep 998831 = 1498247) B1498247
theorem B998921 : Blo 662308 998921 := bstep (se 2 (by rfl) ⟨374595, by rfl⟩ : syracuseStep 998921 = 749191) B749191
theorem B1490471 : Blo 662308 1490471 := bstep (se 1 (by rfl) ⟨1117853, by rfl⟩ : syracuseStep 1490471 = 2235707) B2235707
theorem B998951 : Blo 662308 998951 := bstep (se 1 (by rfl) ⟨749213, by rfl⟩ : syracuseStep 998951 = 1498427) B1498427
theorem B999035 : Blo 662308 999035 := bstep (se 1 (by rfl) ⟨749276, by rfl⟩ : syracuseStep 999035 = 1498553) B1498553
theorem B5029613 : Blo 662308 5029613 := bstep (se 3 (by rfl) ⟨943052, by rfl⟩ : syracuseStep 5029613 = 1886105) B1886105
theorem B999161 : Blo 662308 999161 := bstep (se 2 (by rfl) ⟨374685, by rfl⟩ : syracuseStep 999161 = 749371) B749371
theorem B999263 : Blo 662308 999263 := bstep (se 1 (by rfl) ⟨749447, by rfl⟩ : syracuseStep 999263 = 1498895) B1498895
theorem B1490795 : Blo 662308 1490795 := bstep (se 1 (by rfl) ⟨1118096, by rfl⟩ : syracuseStep 1490795 = 2236193) B2236193
theorem B999275 : Blo 662308 999275 := bstep (se 1 (by rfl) ⟨749456, by rfl⟩ : syracuseStep 999275 = 1498913) B1498913
theorem B3358583 : Blo 662308 3358583 := bstep (se 1 (by rfl) ⟨2518937, by rfl⟩ : syracuseStep 3358583 = 5037875) B5037875
theorem B1490849 : Blo 662308 1490849 := bstep (se 2 (by rfl) ⟨559068, by rfl⟩ : syracuseStep 1490849 = 1118137) B1118137
theorem B2834489 : Blo 662308 2834489 := bstep (se 2 (by rfl) ⟨1062933, by rfl⟩ : syracuseStep 2834489 = 2125867) B2125867
theorem B2244779 : Blo 662308 2244779 := bstep (se 1 (by rfl) ⟨1683584, by rfl⟩ : syracuseStep 2244779 = 3367169) B3367169
theorem B1491191 : Blo 662308 1491191 := bstep (se 1 (by rfl) ⟨1118393, by rfl⟩ : syracuseStep 1491191 = 2236787) B2236787
theorem B1196623 : Blo 662308 1196623 := bstep (se 1 (by rfl) ⟨897467, by rfl⟩ : syracuseStep 1196623 = 1794935) B1794935
theorem B5030585 : Blo 662308 5030585 := bstep (se 2 (by rfl) ⟨1886469, by rfl⟩ : syracuseStep 5030585 = 3772939) B3772939
theorem B1262279 : Blo 662308 1262279 := bstep (se 1 (by rfl) ⟨946709, by rfl⟩ : syracuseStep 1262279 = 1893419) B1893419
theorem B2245319 : Blo 662308 2245319 := bstep (se 1 (by rfl) ⟨1683989, by rfl⟩ : syracuseStep 2245319 = 3367979) B3367979
theorem B1950419 : Blo 662308 1950419 := bstep (se 1 (by rfl) ⟨1462814, by rfl⟩ : syracuseStep 1950419 = 2925629) B2925629
theorem B1491785 : Blo 662308 1491785 := bstep (se 2 (by rfl) ⟨559419, by rfl⟩ : syracuseStep 1491785 = 1118839) B1118839
theorem B7685039 : Blo 662308 7685039 := bstep (se 1 (by rfl) ⟨5763779, by rfl⟩ : syracuseStep 7685039 = 11527559) B11527559
theorem B1295291 : Blo 662308 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B1262803 : Blo 662308 1262803 := bstep (se 1 (by rfl) ⟨947102, by rfl⟩ : syracuseStep 1262803 = 1894205) B1894205
theorem B1066313 : Blo 662308 1066313 := bstep (se 2 (by rfl) ⟨399867, by rfl⟩ : syracuseStep 1066313 = 799735) B799735
theorem B1263023 : Blo 662308 1263023 := bstep (se 1 (by rfl) ⟨947267, by rfl⟩ : syracuseStep 1263023 = 1894535) B1894535
theorem B2246183 : Blo 662308 2246183 := bstep (se 1 (by rfl) ⟨1684637, by rfl⟩ : syracuseStep 2246183 = 3369275) B3369275
theorem B1066535 : Blo 662308 1066535 := bstep (se 1 (by rfl) ⟨799901, by rfl⟩ : syracuseStep 1066535 = 1599803) B1599803
theorem B1492577 : Blo 662308 1492577 := bstep (se 2 (by rfl) ⟨559716, by rfl⟩ : syracuseStep 1492577 = 1119433) B1119433
theorem B5031557 : Blo 662308 5031557 := bstep (se 4 (by rfl) ⟨471708, by rfl⟩ : syracuseStep 5031557 = 943417) B943417
theorem B2246291 : Blo 662308 2246291 := bstep (se 1 (by rfl) ⟨1684718, by rfl⟩ : syracuseStep 2246291 = 3369437) B3369437
theorem B8079047 : Blo 662308 8079047 := bstep (se 1 (by rfl) ⟨6059285, by rfl⟩ : syracuseStep 8079047 = 12118571) B12118571
theorem B1263433 : Blo 662308 1263433 := bstep (se 2 (by rfl) ⟨473787, by rfl⟩ : syracuseStep 1263433 = 947575) B947575
theorem B2246507 : Blo 662308 2246507 := bstep (se 1 (by rfl) ⟨1684880, by rfl⟩ : syracuseStep 2246507 = 3369761) B3369761
theorem B2246561 : Blo 662308 2246561 := bstep (se 2 (by rfl) ⟨842460, by rfl⟩ : syracuseStep 2246561 = 1684921) B1684921
theorem B1492919 : Blo 662308 1492919 := bstep (se 1 (by rfl) ⟨1119689, by rfl⟩ : syracuseStep 1492919 = 2239379) B2239379
theorem B1198007 : Blo 662308 1198007 := bstep (se 1 (by rfl) ⟨898505, by rfl⟩ : syracuseStep 1198007 = 1797011) B1797011
theorem B1067131 : Blo 662308 1067131 := bstep (se 1 (by rfl) ⟨800348, by rfl⟩ : syracuseStep 1067131 = 1600697) B1600697
theorem B3787019 : Blo 662308 3787019 := bstep (se 1 (by rfl) ⟨2840264, by rfl⟩ : syracuseStep 3787019 = 5680529) B5680529
theorem B10242541 : Blo 662308 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B2247155 : Blo 662308 2247155 := bstep (se 1 (by rfl) ⟨1685366, by rfl⟩ : syracuseStep 2247155 = 3370733) B3370733
theorem B1493513 : Blo 662308 1493513 := bstep (se 2 (by rfl) ⟨560067, by rfl⟩ : syracuseStep 1493513 = 1120135) B1120135
theorem B1591931 : Blo 662308 1591931 := bstep (se 1 (by rfl) ⟨1193948, by rfl⟩ : syracuseStep 1591931 = 2387897) B2387897
theorem B1493855 : Blo 662308 1493855 := bstep (se 1 (by rfl) ⟨1120391, by rfl⟩ : syracuseStep 1493855 = 2240783) B2240783
theorem B838507 : Blo 662308 838507 := bstep (se 1 (by rfl) ⟨628880, by rfl⟩ : syracuseStep 838507 = 1257761) B1257761
theorem B5393297 : Blo 662308 5393297 := bstep (se 2 (by rfl) ⟨2022486, by rfl⟩ : syracuseStep 5393297 = 4044973) B4044973
theorem B1592239 : Blo 662308 1592239 := bstep (se 1 (by rfl) ⟨1194179, by rfl⟩ : syracuseStep 1592239 = 2388359) B2388359
theorem B2247695 : Blo 662308 2247695 := bstep (se 1 (by rfl) ⟨1685771, by rfl⟩ : syracuseStep 2247695 = 3371543) B3371543
theorem B1494035 : Blo 662308 1494035 := bstep (se 1 (by rfl) ⟨1120526, by rfl⟩ : syracuseStep 1494035 = 2241053) B2241053
theorem B43142219 : Blo 662308 43142219 := bstep (se 1 (by rfl) ⟨32356664, by rfl⟩ : syracuseStep 43142219 = 64713329) B64713329
theorem B4246607 : Blo 662308 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B707935 : Blo 662308 707935 := bstep (se 1 (by rfl) ⟨530951, by rfl⟩ : syracuseStep 707935 = 1061903) B1061903
theorem B1494377 : Blo 662308 1494377 := bstep (se 2 (by rfl) ⟨560391, by rfl⟩ : syracuseStep 1494377 = 1120783) B1120783
theorem B1134119 : Blo 662308 1134119 := bstep (se 1 (by rfl) ⟨850589, by rfl⟩ : syracuseStep 1134119 = 1701179) B1701179
theorem B2248289 : Blo 662308 2248289 := bstep (se 2 (by rfl) ⟨843108, by rfl⟩ : syracuseStep 2248289 = 1686217) B1686217
theorem B3788477 : Blo 662308 3788477 := bstep (se 3 (by rfl) ⟨710339, by rfl⟩ : syracuseStep 3788477 = 1420679) B1420679
theorem B1494971 : Blo 662308 1494971 := bstep (se 1 (by rfl) ⟨1121228, by rfl⟩ : syracuseStep 1494971 = 2242457) B2242457
theorem B708571 : Blo 662308 708571 := bstep (se 1 (by rfl) ⟨531428, by rfl⟩ : syracuseStep 708571 = 1062857) B1062857
theorem B5033987 : Blo 662308 5033987 := bstep (se 1 (by rfl) ⟨3775490, by rfl⟩ : syracuseStep 5033987 = 7550981) B7550981
theorem B1495097 : Blo 662308 1495097 := bstep (se 2 (by rfl) ⟨560661, by rfl⟩ : syracuseStep 1495097 = 1121323) B1121323
theorem B4247633 : Blo 662308 4247633 := bstep (se 2 (by rfl) ⟨1592862, by rfl⟩ : syracuseStep 4247633 = 3185725) B3185725
theorem B839803 : Blo 662308 839803 := bstep (se 1 (by rfl) ⟨629852, by rfl⟩ : syracuseStep 839803 = 1259705) B1259705
theorem B5394595 : Blo 662308 5394595 := bstep (se 1 (by rfl) ⟨4045946, by rfl⟩ : syracuseStep 5394595 = 8091893) B8091893
theorem B1495439 : Blo 662308 1495439 := bstep (se 1 (by rfl) ⟨1121579, by rfl⟩ : syracuseStep 1495439 = 2243159) B2243159
theorem B3592763 : Blo 662308 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B1495763 : Blo 662308 1495763 := bstep (se 1 (by rfl) ⟨1121822, by rfl⟩ : syracuseStep 1495763 = 2243645) B2243645
theorem B3363767 : Blo 662308 3363767 := bstep (se 1 (by rfl) ⟨2522825, by rfl⟩ : syracuseStep 3363767 = 5045651) B5045651
theorem B7263233 : Blo 662308 7263233 := bstep (se 2 (by rfl) ⟨2723712, by rfl⟩ : syracuseStep 7263233 = 5447425) B5447425
theorem B2151809 : Blo 662308 2151809 := bstep (se 2 (by rfl) ⟨806928, by rfl⟩ : syracuseStep 2151809 = 1613857) B1613857
theorem B3790253 : Blo 662308 3790253 := bstep (se 3 (by rfl) ⟨710672, by rfl⟩ : syracuseStep 3790253 = 1421345) B1421345
theorem B7263749 : Blo 662308 7263749 := bstep (se 4 (by rfl) ⟨680976, by rfl⟩ : syracuseStep 7263749 = 1361953) B1361953
theorem B1889831 : Blo 662308 1889831 := bstep (se 1 (by rfl) ⟨1417373, by rfl⟩ : syracuseStep 1889831 = 2834747) B2834747
theorem B1496699 : Blo 662308 1496699 := bstep (se 1 (by rfl) ⟨1122524, by rfl⟩ : syracuseStep 1496699 = 2245049) B2245049
theorem B1496825 : Blo 662308 1496825 := bstep (se 2 (by rfl) ⟨561309, by rfl⟩ : syracuseStep 1496825 = 1122619) B1122619
theorem B1595323 : Blo 662308 1595323 := bstep (se 1 (by rfl) ⟨1196492, by rfl⟩ : syracuseStep 1595323 = 2392985) B2392985
theorem B841691 : Blo 662308 841691 := bstep (se 1 (by rfl) ⟨631268, by rfl⟩ : syracuseStep 841691 = 1262537) B1262537
theorem B1497095 : Blo 662308 1497095 := bstep (se 1 (by rfl) ⟨1122821, by rfl⟩ : syracuseStep 1497095 = 2245643) B2245643
theorem B1136719 : Blo 662308 1136719 := bstep (se 1 (by rfl) ⟨852539, by rfl⟩ : syracuseStep 1136719 = 1705079) B1705079
theorem B1497167 : Blo 662308 1497167 := bstep (se 1 (by rfl) ⟨1122875, by rfl⟩ : syracuseStep 1497167 = 2245751) B2245751
theorem B1792361 : Blo 662308 1792361 := bstep (se 2 (by rfl) ⟨672135, by rfl⟩ : syracuseStep 1792361 = 1344271) B1344271
theorem B3365225 : Blo 662308 3365225 := bstep (se 2 (by rfl) ⟨1261959, by rfl⟩ : syracuseStep 3365225 = 2523919) B2523919
theorem B5036417 : Blo 662308 5036417 := bstep (se 2 (by rfl) ⟨1888656, by rfl⟩ : syracuseStep 5036417 = 3777313) B3777313
theorem B842167 : Blo 662308 842167 := bstep (se 1 (by rfl) ⟨631625, by rfl⟩ : syracuseStep 842167 = 1263251) B1263251
theorem B1497563 : Blo 662308 1497563 := bstep (se 1 (by rfl) ⟨1123172, by rfl⟩ : syracuseStep 1497563 = 2246345) B2246345
theorem B9558557 : Blo 662308 9558557 := bstep (se 3 (by rfl) ⟨1792229, by rfl⟩ : syracuseStep 9558557 = 3584459) B3584459
theorem B3791393 : Blo 662308 3791393 := bstep (se 2 (by rfl) ⟨1421772, by rfl⟩ : syracuseStep 3791393 = 2843545) B2843545
theorem B1498031 : Blo 662308 1498031 := bstep (se 1 (by rfl) ⟨1123523, by rfl⟩ : syracuseStep 1498031 = 2247047) B2247047
theorem B1596343 : Blo 662308 1596343 := bstep (se 1 (by rfl) ⟨1197257, by rfl⟩ : syracuseStep 1596343 = 2394515) B2394515
theorem B1498283 : Blo 662308 1498283 := bstep (se 1 (by rfl) ⟨1123712, by rfl⟩ : syracuseStep 1498283 = 2247425) B2247425
theorem B9723053 : Blo 662308 9723053 := bstep (se 3 (by rfl) ⟨1823072, by rfl⟩ : syracuseStep 9723053 = 3646145) B3646145
theorem B1891937 : Blo 662308 1891937 := bstep (se 2 (by rfl) ⟨709476, by rfl⟩ : syracuseStep 1891937 = 1418953) B1418953
theorem B745159 : Blo 662308 745159 := bstep (se 1 (by rfl) ⟨558869, by rfl⟩ : syracuseStep 745159 = 1117739) B1117739
theorem B1498823 : Blo 662308 1498823 := bstep (se 1 (by rfl) ⟨1124117, by rfl⟩ : syracuseStep 1498823 = 2248235) B2248235
theorem B9690841 : Blo 662308 9690841 := bstep (se 2 (by rfl) ⟨3634065, by rfl⟩ : syracuseStep 9690841 = 7268131) B7268131
theorem B2514959 : Blo 662308 2514959 := bstep (se 1 (by rfl) ⟨1886219, by rfl⟩ : syracuseStep 2514959 = 3772439) B3772439
theorem B746023 : Blo 662308 746023 := bstep (se 1 (by rfl) ⟨559517, by rfl⟩ : syracuseStep 746023 = 1119035) B1119035
theorem B1139675 : Blo 662308 1139675 := bstep (se 1 (by rfl) ⟨854756, by rfl⟩ : syracuseStep 1139675 = 1709513) B1709513
theorem B1893395 : Blo 662308 1893395 := bstep (se 1 (by rfl) ⟨1420046, by rfl⟩ : syracuseStep 1893395 = 2840093) B2840093
theorem B10806317 : Blo 662308 10806317 := bstep (se 3 (by rfl) ⟨2026184, by rfl⟩ : syracuseStep 10806317 = 4052369) B4052369
theorem B2843819 : Blo 662308 2843819 := bstep (se 1 (by rfl) ⟨2132864, by rfl⟩ : syracuseStep 2843819 = 4265729) B4265729
theorem B1009079 : Blo 662308 1009079 := bstep (se 1 (by rfl) ⟨756809, by rfl⟩ : syracuseStep 1009079 = 1513619) B1513619
theorem B9561563 : Blo 662308 9561563 := bstep (se 1 (by rfl) ⟨7171172, by rfl⟩ : syracuseStep 9561563 = 14342345) B14342345
theorem B4253147 : Blo 662308 4253147 := bstep (se 1 (by rfl) ⟨3189860, by rfl⟩ : syracuseStep 4253147 = 6379721) B6379721
theorem B1893851 : Blo 662308 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B2516615 : Blo 662308 2516615 := bstep (se 1 (by rfl) ⟨1887461, by rfl⟩ : syracuseStep 2516615 = 3774923) B3774923
theorem B1599419 : Blo 662308 1599419 := bstep (se 1 (by rfl) ⟨1199564, by rfl⟩ : syracuseStep 1599419 = 2399129) B2399129
theorem B4253633 : Blo 662308 4253633 := bstep (se 2 (by rfl) ⟨1595112, by rfl⟩ : syracuseStep 4253633 = 3190225) B3190225
theorem B6383717 : Blo 662308 6383717 := bstep (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) B1196947
theorem B747643 : Blo 662308 747643 := bstep (se 1 (by rfl) ⟨560732, by rfl⟩ : syracuseStep 747643 = 1121465) B1121465
theorem B1796633 : Blo 662308 1796633 := bstep (se 2 (by rfl) ⟨673737, by rfl⟩ : syracuseStep 1796633 = 1347475) B1347475
theorem B9562657 : Blo 662308 9562657 := bstep (se 2 (by rfl) ⟨3585996, by rfl⟩ : syracuseStep 9562657 = 7171993) B7171993
theorem B748111 : Blo 662308 748111 := bstep (se 1 (by rfl) ⟨561083, by rfl⟩ : syracuseStep 748111 = 1122167) B1122167
theorem B2517601 : Blo 662308 2517601 := bstep (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) B1888201
theorem B8514233 : Blo 662308 8514233 := bstep (se 2 (by rfl) ⟨3192837, by rfl⟩ : syracuseStep 8514233 = 6385675) B6385675
theorem B748507 : Blo 662308 748507 := bstep (se 1 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 748507 = 1122761) B1122761
theorem B2518073 : Blo 662308 2518073 := bstep (se 2 (by rfl) ⟨944277, by rfl⟩ : syracuseStep 2518073 = 1888555) B1888555
theorem B748975 : Blo 662308 748975 := bstep (se 1 (by rfl) ⟨561731, by rfl⟩ : syracuseStep 748975 = 1123463) B1123463
theorem B7663243 : Blo 662308 7663243 := bstep (se 1 (by rfl) ⟨5747432, by rfl⟩ : syracuseStep 7663243 = 11494865) B11494865
theorem B749407 : Blo 662308 749407 := bstep (se 1 (by rfl) ⟨562055, by rfl⟩ : syracuseStep 749407 = 1124111) B1124111
theorem B3600247 : Blo 662308 3600247 := bstep (se 1 (by rfl) ⟨2700185, by rfl⟩ : syracuseStep 3600247 = 5400371) B5400371
theorem B5402639 : Blo 662308 5402639 := bstep (se 1 (by rfl) ⟨4051979, by rfl⟩ : syracuseStep 5402639 = 8103959) B8103959
theorem B2519059 : Blo 662308 2519059 := bstep (se 1 (by rfl) ⟨1889294, by rfl⟩ : syracuseStep 2519059 = 3778589) B3778589
theorem B2126483 : Blo 662308 2126483 := bstep (se 1 (by rfl) ⟨1594862, by rfl⟩ : syracuseStep 2126483 = 3189725) B3189725
theorem B3371705 : Blo 662308 3371705 := bstep (se 2 (by rfl) ⟨1264389, by rfl⟩ : syracuseStep 3371705 = 2528779) B2528779
theorem B946937 : Blo 662308 946937 := bstep (se 2 (by rfl) ⟨355101, by rfl⟩ : syracuseStep 946937 = 710203) B710203
theorem B6911041 : Blo 662308 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B947791 : Blo 662308 947791 := bstep (se 1 (by rfl) ⟨710843, by rfl⟩ : syracuseStep 947791 = 1421687) B1421687
theorem B2127559 : Blo 662308 2127559 := bstep (se 1 (by rfl) ⟨1595669, by rfl⟩ : syracuseStep 2127559 = 3191339) B3191339
theorem B2520791 : Blo 662308 2520791 := bstep (se 1 (by rfl) ⟨1890593, by rfl⟩ : syracuseStep 2520791 = 3781187) B3781187
theorem B9598925 : Blo 662308 9598925 := bstep (se 3 (by rfl) ⟨1799798, by rfl⟩ : syracuseStep 9598925 = 3599597) B3599597
theorem B2554051 : Blo 662308 2554051 := bstep (se 1 (by rfl) ⟨1915538, by rfl⟩ : syracuseStep 2554051 = 3831077) B3831077
theorem B2521975 : Blo 662308 2521975 := bstep (se 1 (by rfl) ⟨1891481, by rfl⟩ : syracuseStep 2521975 = 3782963) B3782963
theorem B2554895 : Blo 662308 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B2161835 : Blo 662308 2161835 := bstep (se 1 (by rfl) ⟨1621376, by rfl⟩ : syracuseStep 2161835 = 3242753) B3242753
theorem B1211591 : Blo 662308 1211591 := bstep (se 1 (by rfl) ⟨908693, by rfl⟩ : syracuseStep 1211591 = 1817387) B1817387
theorem B8519255 : Blo 662308 8519255 := bstep (se 1 (by rfl) ⟨6389441, by rfl⟩ : syracuseStep 8519255 = 12778883) B12778883
theorem B2522947 : Blo 662308 2522947 := bstep (se 1 (by rfl) ⟨1892210, by rfl⟩ : syracuseStep 2522947 = 3784421) B3784421
theorem B6062501 : Blo 662308 6062501 := bstep (se 4 (by rfl) ⟨568359, by rfl⟩ : syracuseStep 6062501 = 1136719) B1136719
theorem B1278433 : Blo 662308 1278433 := bstep (se 2 (by rfl) ⟨479412, by rfl⟩ : syracuseStep 1278433 = 958825) B958825
theorem B27198467 : Blo 662308 27198467 := bstep (se 1 (by rfl) ⟨20398850, by rfl⟩ : syracuseStep 27198467 = 40797701) B40797701
theorem B2884841 : Blo 662308 2884841 := bstep (se 2 (by rfl) ⟨1081815, by rfl⟩ : syracuseStep 2884841 = 2163631) B2163631
theorem B5047595 : Blo 662308 5047595 := bstep (se 1 (by rfl) ⟨3785696, by rfl⟩ : syracuseStep 5047595 = 7571393) B7571393
theorem B2524679 : Blo 662308 2524679 := bstep (se 1 (by rfl) ⟨1893509, by rfl⟩ : syracuseStep 2524679 = 3787019) B3787019
theorem B8324995 : Blo 662308 8324995 := bstep (se 1 (by rfl) ⟨6243746, by rfl⟩ : syracuseStep 8324995 = 12487493) B12487493
theorem B2525165 : Blo 662308 2525165 := bstep (se 3 (by rfl) ⟨473468, by rfl⟩ : syracuseStep 2525165 = 946937) B946937
theorem B2525651 : Blo 662308 2525651 := bstep (se 1 (by rfl) ⟨1894238, by rfl⟩ : syracuseStep 2525651 = 3788477) B3788477
theorem B5049053 : Blo 662308 5049053 := bstep (se 3 (by rfl) ⟨946697, by rfl⟩ : syracuseStep 5049053 = 1893395) B1893395
theorem B2395175 : Blo 662308 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B1707131 : Blo 662308 1707131 := bstep (se 1 (by rfl) ⟨1280348, by rfl⟩ : syracuseStep 1707131 = 2560697) B2560697
theorem B2428123 : Blo 662308 2428123 := bstep (se 1 (by rfl) ⟨1821092, by rfl⟩ : syracuseStep 2428123 = 3642185) B3642185
theorem B12750209 : Blo 662308 12750209 := bstep (se 2 (by rfl) ⟨4781328, by rfl⟩ : syracuseStep 12750209 = 9562657) B9562657
theorem B2526835 : Blo 662308 2526835 := bstep (se 1 (by rfl) ⟨1895126, by rfl⟩ : syracuseStep 2526835 = 3790253) B3790253
theorem B1118009 : Blo 662308 1118009 := bstep (se 2 (by rfl) ⟨419253, by rfl⟩ : syracuseStep 1118009 = 838507) B838507
theorem B2527595 : Blo 662308 2527595 := bstep (se 1 (by rfl) ⟨1895696, by rfl⟩ : syracuseStep 2527595 = 3791393) B3791393
theorem B14389913 : Blo 662308 14389913 := bstep (se 2 (by rfl) ⟨5396217, by rfl⟩ : syracuseStep 14389913 = 10792435) B10792435
theorem B1119055 : Blo 662308 1119055 := bstep (se 1 (by rfl) ⟨839291, by rfl⟩ : syracuseStep 1119055 = 1678583) B1678583
theorem B8491985 : Blo 662308 8491985 := bstep (se 2 (by rfl) ⟨3184494, by rfl⟩ : syracuseStep 8491985 = 6368989) B6368989
theorem B1676639 : Blo 662308 1676639 := bstep (se 1 (by rfl) ⟨1257479, by rfl⟩ : syracuseStep 1676639 = 2514959) B2514959
theorem B4855243 : Blo 662308 4855243 := bstep (se 1 (by rfl) ⟨3641432, by rfl⟩ : syracuseStep 4855243 = 7282865) B7282865
theorem B1119737 : Blo 662308 1119737 := bstep (se 2 (by rfl) ⟨419901, by rfl⟩ : syracuseStep 1119737 = 839803) B839803
theorem B1120007 : Blo 662308 1120007 := bstep (se 1 (by rfl) ⟨840005, by rfl⟩ : syracuseStep 1120007 = 1680011) B1680011
theorem B11376773 : Blo 662308 11376773 := bstep (se 4 (by rfl) ⟨1066572, by rfl⟩ : syracuseStep 11376773 = 2133145) B2133145
theorem B1677743 : Blo 662308 1677743 := bstep (se 1 (by rfl) ⟨1258307, by rfl⟩ : syracuseStep 1677743 = 2516615) B2516615
theorem B1677793 : Blo 662308 1677793 := bstep (se 2 (by rfl) ⟨629172, by rfl⟩ : syracuseStep 1677793 = 1258345) B1258345
theorem B1120763 : Blo 662308 1120763 := bstep (se 1 (by rfl) ⟨840572, by rfl⟩ : syracuseStep 1120763 = 1681145) B1681145
theorem B9214721 : Blo 662308 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B662319 : Blo 662308 662319 := bstep (se 1 (by rfl) ⟨496739, by rfl⟩ : syracuseStep 662319 = 993479) B993479
theorem B662427 : Blo 662308 662427 := bstep (se 1 (by rfl) ⟨496820, by rfl⟩ : syracuseStep 662427 = 993641) B993641
theorem B1121195 : Blo 662308 1121195 := bstep (se 1 (by rfl) ⟨840896, by rfl⟩ : syracuseStep 1121195 = 1681793) B1681793
theorem B662479 : Blo 662308 662479 := bstep (se 1 (by rfl) ⟨496859, by rfl⟩ : syracuseStep 662479 = 993719) B993719
theorem B662503 : Blo 662308 662503 := bstep (se 1 (by rfl) ⟨496877, by rfl⟩ : syracuseStep 662503 = 993755) B993755
theorem B5053427 : Blo 662308 5053427 := bstep (se 1 (by rfl) ⟨3790070, by rfl⟩ : syracuseStep 5053427 = 7580141) B7580141
theorem B5676155 : Blo 662308 5676155 := bstep (se 1 (by rfl) ⟨4257116, by rfl⟩ : syracuseStep 5676155 = 8514233) B8514233
theorem B662815 : Blo 662308 662815 := bstep (se 1 (by rfl) ⟨497111, by rfl⟩ : syracuseStep 662815 = 994223) B994223
theorem B662875 : Blo 662308 662875 := bstep (se 1 (by rfl) ⟨497156, by rfl⟩ : syracuseStep 662875 = 994313) B994313
theorem B662895 : Blo 662308 662895 := bstep (se 1 (by rfl) ⟨497171, by rfl⟩ : syracuseStep 662895 = 994343) B994343
theorem B1678715 : Blo 662308 1678715 := bstep (se 1 (by rfl) ⟨1259036, by rfl⟩ : syracuseStep 1678715 = 2518073) B2518073
theorem B662951 : Blo 662308 662951 := bstep (se 1 (by rfl) ⟨497213, by rfl⟩ : syracuseStep 662951 = 994427) B994427
theorem B1121735 : Blo 662308 1121735 := bstep (se 1 (by rfl) ⟨841301, by rfl⟩ : syracuseStep 1121735 = 1682603) B1682603
theorem B663035 : Blo 662308 663035 := bstep (se 1 (by rfl) ⟨497276, by rfl⟩ : syracuseStep 663035 = 994553) B994553
theorem B663103 : Blo 662308 663103 := bstep (se 1 (by rfl) ⟨497327, by rfl⟩ : syracuseStep 663103 = 994655) B994655
theorem B663111 : Blo 662308 663111 := bstep (se 1 (by rfl) ⟨497333, by rfl⟩ : syracuseStep 663111 = 994667) B994667
theorem B663263 : Blo 662308 663263 := bstep (se 1 (by rfl) ⟨497447, by rfl⟩ : syracuseStep 663263 = 994895) B994895
theorem B2236139 : Blo 662308 2236139 := bstep (se 1 (by rfl) ⟨1677104, by rfl⟩ : syracuseStep 2236139 = 3354209) B3354209
theorem B663343 : Blo 662308 663343 := bstep (se 1 (by rfl) ⟨497507, by rfl⟩ : syracuseStep 663343 = 995015) B995015
theorem B663451 : Blo 662308 663451 := bstep (se 1 (by rfl) ⟨497588, by rfl⟩ : syracuseStep 663451 = 995177) B995177
theorem B663503 : Blo 662308 663503 := bstep (se 1 (by rfl) ⟨497627, by rfl⟩ : syracuseStep 663503 = 995255) B995255
theorem B663527 : Blo 662308 663527 := bstep (se 1 (by rfl) ⟨497645, by rfl⟩ : syracuseStep 663527 = 995291) B995291
theorem B2433235 : Blo 662308 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B663839 : Blo 662308 663839 := bstep (se 1 (by rfl) ⟨497879, by rfl⟩ : syracuseStep 663839 = 995759) B995759
theorem B663899 : Blo 662308 663899 := bstep (se 1 (by rfl) ⟨497924, by rfl⟩ : syracuseStep 663899 = 995849) B995849
theorem B663919 : Blo 662308 663919 := bstep (se 1 (by rfl) ⟨497939, by rfl⟩ : syracuseStep 663919 = 995879) B995879
theorem B5054885 : Blo 662308 5054885 := bstep (se 4 (by rfl) ⟨473895, by rfl⟩ : syracuseStep 5054885 = 947791) B947791
theorem B663975 : Blo 662308 663975 := bstep (se 1 (by rfl) ⟨497981, by rfl⟩ : syracuseStep 663975 = 995963) B995963
theorem B1122727 : Blo 662308 1122727 := bstep (se 1 (by rfl) ⟨842045, by rfl⟩ : syracuseStep 1122727 = 1684091) B1684091
theorem B1417655 : Blo 662308 1417655 := bstep (se 1 (by rfl) ⟨1063241, by rfl⟩ : syracuseStep 1417655 = 2126483) B2126483
theorem B664059 : Blo 662308 664059 := bstep (se 1 (by rfl) ⟨498044, by rfl⟩ : syracuseStep 664059 = 996089) B996089
theorem B664127 : Blo 662308 664127 := bstep (se 1 (by rfl) ⟨498095, by rfl⟩ : syracuseStep 664127 = 996191) B996191
theorem B664135 : Blo 662308 664135 := bstep (se 1 (by rfl) ⟨498101, by rfl⟩ : syracuseStep 664135 = 996203) B996203
theorem B1122889 : Blo 662308 1122889 := bstep (se 2 (by rfl) ⟨421083, by rfl⟩ : syracuseStep 1122889 = 842167) B842167
theorem B1122923 : Blo 662308 1122923 := bstep (se 1 (by rfl) ⟨842192, by rfl⟩ : syracuseStep 1122923 = 1684385) B1684385
theorem B2237111 : Blo 662308 2237111 := bstep (se 1 (by rfl) ⟨1677833, by rfl⟩ : syracuseStep 2237111 = 3355667) B3355667
theorem B664287 : Blo 662308 664287 := bstep (se 1 (by rfl) ⟨498215, by rfl⟩ : syracuseStep 664287 = 996431) B996431
theorem B664367 : Blo 662308 664367 := bstep (se 1 (by rfl) ⟨498275, by rfl⟩ : syracuseStep 664367 = 996551) B996551
theorem B664475 : Blo 662308 664475 := bstep (se 1 (by rfl) ⟨498356, by rfl⟩ : syracuseStep 664475 = 996713) B996713
theorem B664527 : Blo 662308 664527 := bstep (se 1 (by rfl) ⟨498395, by rfl⟩ : syracuseStep 664527 = 996791) B996791
theorem B664551 : Blo 662308 664551 := bstep (se 1 (by rfl) ⟨498413, by rfl⟩ : syracuseStep 664551 = 996827) B996827
theorem B1680527 : Blo 662308 1680527 := bstep (se 1 (by rfl) ⟨1260395, by rfl⟩ : syracuseStep 1680527 = 2520791) B2520791
theorem B4039913 : Blo 662308 4039913 := bstep (se 2 (by rfl) ⟨1514967, by rfl⟩ : syracuseStep 4039913 = 3029935) B3029935
theorem B664863 : Blo 662308 664863 := bstep (se 1 (by rfl) ⟨498647, by rfl⟩ : syracuseStep 664863 = 997295) B997295
theorem B6399283 : Blo 662308 6399283 := bstep (se 1 (by rfl) ⟨4799462, by rfl⟩ : syracuseStep 6399283 = 9598925) B9598925
theorem B664923 : Blo 662308 664923 := bstep (se 1 (by rfl) ⟨498692, by rfl⟩ : syracuseStep 664923 = 997385) B997385
theorem B664943 : Blo 662308 664943 := bstep (se 1 (by rfl) ⟨498707, by rfl⟩ : syracuseStep 664943 = 997415) B997415
theorem B664999 : Blo 662308 664999 := bstep (se 1 (by rfl) ⟨498749, by rfl⟩ : syracuseStep 664999 = 997499) B997499
theorem B3024317 : Blo 662308 3024317 := bstep (se 3 (by rfl) ⟨567059, by rfl⟩ : syracuseStep 3024317 = 1134119) B1134119
theorem B665083 : Blo 662308 665083 := bstep (se 1 (by rfl) ⟨498812, by rfl⟩ : syracuseStep 665083 = 997625) B997625
theorem B1418809 : Blo 662308 1418809 := bstep (se 2 (by rfl) ⟨532053, by rfl⟩ : syracuseStep 1418809 = 1064107) B1064107
theorem B665151 : Blo 662308 665151 := bstep (se 1 (by rfl) ⟨498863, by rfl⟩ : syracuseStep 665151 = 997727) B997727
theorem B665159 : Blo 662308 665159 := bstep (se 1 (by rfl) ⟨498869, by rfl⟩ : syracuseStep 665159 = 997739) B997739
theorem B665311 : Blo 662308 665311 := bstep (se 1 (by rfl) ⟨498983, by rfl⟩ : syracuseStep 665311 = 997967) B997967
theorem B665391 : Blo 662308 665391 := bstep (se 1 (by rfl) ⟨499043, by rfl⟩ : syracuseStep 665391 = 998087) B998087
theorem B665499 : Blo 662308 665499 := bstep (se 1 (by rfl) ⟨499124, by rfl⟩ : syracuseStep 665499 = 998249) B998249
theorem B665551 : Blo 662308 665551 := bstep (se 1 (by rfl) ⟨499163, by rfl⟩ : syracuseStep 665551 = 998327) B998327
theorem B665575 : Blo 662308 665575 := bstep (se 1 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 665575 = 998363) B998363
theorem B993545 : Blo 662308 993545 := bstep (se 2 (by rfl) ⟨372579, by rfl⟩ : syracuseStep 993545 = 745159) B745159
theorem B665887 : Blo 662308 665887 := bstep (se 1 (by rfl) ⟨499415, by rfl⟩ : syracuseStep 665887 = 998831) B998831
theorem B12921121 : Blo 662308 12921121 := bstep (se 2 (by rfl) ⟨4845420, by rfl⟩ : syracuseStep 12921121 = 9690841) B9690841
theorem B665947 : Blo 662308 665947 := bstep (se 1 (by rfl) ⟨499460, by rfl⟩ : syracuseStep 665947 = 998921) B998921
theorem B993647 : Blo 662308 993647 := bstep (se 1 (by rfl) ⟨745235, by rfl⟩ : syracuseStep 993647 = 1490471) B1490471
theorem B665967 : Blo 662308 665967 := bstep (se 1 (by rfl) ⟨499475, by rfl⟩ : syracuseStep 665967 = 998951) B998951
theorem B5679503 : Blo 662308 5679503 := bstep (se 1 (by rfl) ⟨4259627, by rfl⟩ : syracuseStep 5679503 = 8519255) B8519255
theorem B666023 : Blo 662308 666023 := bstep (se 1 (by rfl) ⟨499517, by rfl⟩ : syracuseStep 666023 = 999035) B999035
theorem B3779045 : Blo 662308 3779045 := bstep (se 4 (by rfl) ⟨354285, by rfl⟩ : syracuseStep 3779045 = 708571) B708571
theorem B3353075 : Blo 662308 3353075 := bstep (se 1 (by rfl) ⟨2514806, by rfl⟩ : syracuseStep 3353075 = 5029613) B5029613
theorem B666107 : Blo 662308 666107 := bstep (se 1 (by rfl) ⟨499580, by rfl⟩ : syracuseStep 666107 = 999161) B999161
theorem B666175 : Blo 662308 666175 := bstep (se 1 (by rfl) ⟨499631, by rfl⟩ : syracuseStep 666175 = 999263) B999263
theorem B993863 : Blo 662308 993863 := bstep (se 1 (by rfl) ⟨745397, by rfl⟩ : syracuseStep 993863 = 1490795) B1490795
theorem B666183 : Blo 662308 666183 := bstep (se 1 (by rfl) ⟨499637, by rfl⟩ : syracuseStep 666183 = 999275) B999275
theorem B2239055 : Blo 662308 2239055 := bstep (se 1 (by rfl) ⟨1679291, by rfl⟩ : syracuseStep 2239055 = 3358583) B3358583
theorem B993899 : Blo 662308 993899 := bstep (se 1 (by rfl) ⟨745424, by rfl⟩ : syracuseStep 993899 = 1490849) B1490849
theorem B1682167 : Blo 662308 1682167 := bstep (se 1 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 1682167 = 2523251) B2523251
theorem B994127 : Blo 662308 994127 := bstep (se 1 (by rfl) ⟨745595, by rfl⟩ : syracuseStep 994127 = 1491191) B1491191
theorem B21900145 : Blo 662308 21900145 := bstep (se 2 (by rfl) ⟨8212554, by rfl⟩ : syracuseStep 21900145 = 16425109) B16425109
theorem B1682471 : Blo 662308 1682471 := bstep (se 1 (by rfl) ⟨1261853, by rfl⟩ : syracuseStep 1682471 = 2523707) B2523707
theorem B3320947 : Blo 662308 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B3353723 : Blo 662308 3353723 := bstep (se 1 (by rfl) ⟨2515292, by rfl⟩ : syracuseStep 3353723 = 5030585) B5030585
theorem B994523 : Blo 662308 994523 := bstep (se 1 (by rfl) ⟨745892, by rfl⟩ : syracuseStep 994523 = 1491785) B1491785
theorem B5123359 : Blo 662308 5123359 := bstep (se 1 (by rfl) ⟨3842519, by rfl⟩ : syracuseStep 5123359 = 7685039) B7685039
theorem B994697 : Blo 662308 994697 := bstep (se 2 (by rfl) ⟨373011, by rfl⟩ : syracuseStep 994697 = 746023) B746023
theorem B995051 : Blo 662308 995051 := bstep (se 1 (by rfl) ⟨746288, by rfl⟩ : syracuseStep 995051 = 1492577) B1492577
theorem B3354371 : Blo 662308 3354371 := bstep (se 1 (by rfl) ⟨2515778, by rfl⟩ : syracuseStep 3354371 = 5031557) B5031557
theorem B2240297 : Blo 662308 2240297 := bstep (se 2 (by rfl) ⟨840111, by rfl⟩ : syracuseStep 2240297 = 1680223) B1680223
theorem B5386031 : Blo 662308 5386031 := bstep (se 1 (by rfl) ⟨4039523, by rfl⟩ : syracuseStep 5386031 = 8079047) B8079047
theorem B995279 : Blo 662308 995279 := bstep (se 1 (by rfl) ⟨746459, by rfl⟩ : syracuseStep 995279 = 1492919) B1492919
theorem B798671 : Blo 662308 798671 := bstep (se 1 (by rfl) ⟨599003, by rfl⟩ : syracuseStep 798671 = 1198007) B1198007
theorem B3026945 : Blo 662308 3026945 := bstep (se 2 (by rfl) ⟨1135104, by rfl⟩ : syracuseStep 3026945 = 2270209) B2270209
theorem B1683737 : Blo 662308 1683737 := bstep (se 2 (by rfl) ⟨631401, by rfl⟩ : syracuseStep 1683737 = 1262803) B1262803
theorem B995675 : Blo 662308 995675 := bstep (se 1 (by rfl) ⟨746756, by rfl⟩ : syracuseStep 995675 = 1493513) B1493513
theorem B2732395 : Blo 662308 2732395 := bstep (se 1 (by rfl) ⟨2049296, by rfl⟩ : syracuseStep 2732395 = 4098593) B4098593
theorem B995903 : Blo 662308 995903 := bstep (se 1 (by rfl) ⟨746927, by rfl⟩ : syracuseStep 995903 = 1493855) B1493855
theorem B1421995 : Blo 662308 1421995 := bstep (se 1 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 1421995 = 2132993) B2132993
theorem B996023 : Blo 662308 996023 := bstep (se 1 (by rfl) ⟨747017, by rfl⟩ : syracuseStep 996023 = 1494035) B1494035
theorem B996251 : Blo 662308 996251 := bstep (se 1 (by rfl) ⟨747188, by rfl⟩ : syracuseStep 996251 = 1494377) B1494377
theorem B1684577 : Blo 662308 1684577 := bstep (se 2 (by rfl) ⟨631716, by rfl⟩ : syracuseStep 1684577 = 1263433) B1263433
theorem B3454109 : Blo 662308 3454109 := bstep (se 3 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 3454109 = 1295291) B1295291
theorem B996647 : Blo 662308 996647 := bstep (se 1 (by rfl) ⟨747485, by rfl⟩ : syracuseStep 996647 = 1494971) B1494971
theorem B3355991 : Blo 662308 3355991 := bstep (se 1 (by rfl) ⟨2516993, by rfl⟩ : syracuseStep 3355991 = 5033987) B5033987
theorem B996731 : Blo 662308 996731 := bstep (se 1 (by rfl) ⟨747548, by rfl⟩ : syracuseStep 996731 = 1495097) B1495097
theorem B2831755 : Blo 662308 2831755 := bstep (se 1 (by rfl) ⟨2123816, by rfl⟩ : syracuseStep 2831755 = 4247633) B4247633
theorem B996857 : Blo 662308 996857 := bstep (se 2 (by rfl) ⟨373821, by rfl⟩ : syracuseStep 996857 = 747643) B747643
theorem B1422841 : Blo 662308 1422841 := bstep (se 2 (by rfl) ⟨533565, by rfl⟩ : syracuseStep 1422841 = 1067131) B1067131
theorem B996959 : Blo 662308 996959 := bstep (se 1 (by rfl) ⟨747719, by rfl⟩ : syracuseStep 996959 = 1495439) B1495439
theorem B2832029 : Blo 662308 2832029 := bstep (se 3 (by rfl) ⟨531005, by rfl⟩ : syracuseStep 2832029 = 1062011) B1062011
theorem B997175 : Blo 662308 997175 := bstep (se 1 (by rfl) ⟨747881, by rfl⟩ : syracuseStep 997175 = 1495763) B1495763
theorem B8501111 : Blo 662308 8501111 := bstep (se 1 (by rfl) ⟨6375833, by rfl⟩ : syracuseStep 8501111 = 12751667) B12751667
theorem B2242511 : Blo 662308 2242511 := bstep (se 1 (by rfl) ⟨1681883, by rfl⟩ : syracuseStep 2242511 = 3363767) B3363767
theorem B997481 : Blo 662308 997481 := bstep (se 2 (by rfl) ⟨374055, by rfl⟩ : syracuseStep 997481 = 748111) B748111
theorem B3356801 : Blo 662308 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B2275463 : Blo 662308 2275463 := bstep (se 1 (by rfl) ⟨1706597, by rfl⟩ : syracuseStep 2275463 = 3413195) B3413195
theorem B1259887 : Blo 662308 1259887 := bstep (se 1 (by rfl) ⟨944915, by rfl⟩ : syracuseStep 1259887 = 1889831) B1889831
theorem B997799 : Blo 662308 997799 := bstep (se 1 (by rfl) ⟨748349, by rfl⟩ : syracuseStep 997799 = 1496699) B1496699
theorem B997883 : Blo 662308 997883 := bstep (se 1 (by rfl) ⟨748412, by rfl⟩ : syracuseStep 997883 = 1496825) B1496825
theorem B1686035 : Blo 662308 1686035 := bstep (se 1 (by rfl) ⟨1264526, by rfl⟩ : syracuseStep 1686035 = 2529053) B2529053
theorem B998009 : Blo 662308 998009 := bstep (se 2 (by rfl) ⟨374253, by rfl⟩ : syracuseStep 998009 = 748507) B748507
theorem B998063 : Blo 662308 998063 := bstep (se 1 (by rfl) ⟨748547, by rfl⟩ : syracuseStep 998063 = 1497095) B1497095
theorem B998111 : Blo 662308 998111 := bstep (se 1 (by rfl) ⟨748583, by rfl⟩ : syracuseStep 998111 = 1497167) B1497167
theorem B1194907 : Blo 662308 1194907 := bstep (se 1 (by rfl) ⟨896180, by rfl⟩ : syracuseStep 1194907 = 1792361) B1792361
theorem B2243483 : Blo 662308 2243483 := bstep (se 1 (by rfl) ⟨1682612, by rfl⟩ : syracuseStep 2243483 = 3365225) B3365225
theorem B3357611 : Blo 662308 3357611 := bstep (se 1 (by rfl) ⟨2518208, by rfl⟩ : syracuseStep 3357611 = 5036417) B5036417
theorem B1686491 : Blo 662308 1686491 := bstep (se 1 (by rfl) ⟨1264868, by rfl⟩ : syracuseStep 1686491 = 2529737) B2529737
theorem B998375 : Blo 662308 998375 := bstep (se 1 (by rfl) ⟨748781, by rfl⟩ : syracuseStep 998375 = 1497563) B1497563
theorem B6372371 : Blo 662308 6372371 := bstep (se 1 (by rfl) ⟨4779278, by rfl⟩ : syracuseStep 6372371 = 9558557) B9558557
theorem B998633 : Blo 662308 998633 := bstep (se 2 (by rfl) ⟨374487, by rfl⟩ : syracuseStep 998633 = 748975) B748975
theorem B998687 : Blo 662308 998687 := bstep (se 1 (by rfl) ⟨749015, by rfl⟩ : syracuseStep 998687 = 1498031) B1498031
theorem B1490273 : Blo 662308 1490273 := bstep (se 2 (by rfl) ⟨558852, by rfl⟩ : syracuseStep 1490273 = 1117705) B1117705
theorem B1490363 : Blo 662308 1490363 := bstep (se 1 (by rfl) ⟨1117772, by rfl⟩ : syracuseStep 1490363 = 2235545) B2235545
theorem B998855 : Blo 662308 998855 := bstep (se 1 (by rfl) ⟨749141, by rfl⟩ : syracuseStep 998855 = 1498283) B1498283
theorem B1490489 : Blo 662308 1490489 := bstep (se 2 (by rfl) ⟨558933, by rfl⟩ : syracuseStep 1490489 = 1117867) B1117867
theorem B999209 : Blo 662308 999209 := bstep (se 2 (by rfl) ⟨374703, by rfl⟩ : syracuseStep 999209 = 749407) B749407
theorem B999215 : Blo 662308 999215 := bstep (se 1 (by rfl) ⟨749411, by rfl⟩ : syracuseStep 999215 = 1498823) B1498823
theorem B4800329 : Blo 662308 4800329 := bstep (se 2 (by rfl) ⟨1800123, by rfl⟩ : syracuseStep 4800329 = 3600247) B3600247
theorem B2244509 : Blo 662308 2244509 := bstep (se 3 (by rfl) ⟨420845, by rfl⟩ : syracuseStep 2244509 = 841691) B841691
theorem B2244617 : Blo 662308 2244617 := bstep (se 2 (by rfl) ⟨841731, by rfl⟩ : syracuseStep 2244617 = 1683463) B1683463
theorem B3358745 : Blo 662308 3358745 := bstep (se 2 (by rfl) ⟨1259529, by rfl⟩ : syracuseStep 3358745 = 2519059) B2519059
theorem B5030099 : Blo 662308 5030099 := bstep (se 1 (by rfl) ⟨3772574, by rfl⟩ : syracuseStep 5030099 = 7545149) B7545149
theorem B1491155 : Blo 662308 1491155 := bstep (se 1 (by rfl) ⟨1118366, by rfl⟩ : syracuseStep 1491155 = 2236733) B2236733
theorem B7192793 : Blo 662308 7192793 := bstep (se 2 (by rfl) ⟨2697297, by rfl⟩ : syracuseStep 7192793 = 5394595) B5394595
theorem B1491209 : Blo 662308 1491209 := bstep (se 2 (by rfl) ⟨559203, by rfl⟩ : syracuseStep 1491209 = 1118407) B1118407
theorem B1491425 : Blo 662308 1491425 := bstep (se 2 (by rfl) ⟨559284, by rfl⟩ : syracuseStep 1491425 = 1118569) B1118569
theorem B1065593 : Blo 662308 1065593 := bstep (se 2 (by rfl) ⟨399597, by rfl⟩ : syracuseStep 1065593 = 799195) B799195
theorem B1491731 : Blo 662308 1491731 := bstep (se 1 (by rfl) ⟨1118798, by rfl⟩ : syracuseStep 1491731 = 2237597) B2237597
theorem B672719 : Blo 662308 672719 := bstep (se 1 (by rfl) ⟨504539, by rfl⟩ : syracuseStep 672719 = 1009079) B1009079
theorem B6374375 : Blo 662308 6374375 := bstep (se 1 (by rfl) ⟨4780781, by rfl⟩ : syracuseStep 6374375 = 9561563) B9561563
theorem B2835431 : Blo 662308 2835431 := bstep (se 1 (by rfl) ⟨2126573, by rfl⟩ : syracuseStep 2835431 = 4253147) B4253147
theorem B1262567 : Blo 662308 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B1492091 : Blo 662308 1492091 := bstep (se 1 (by rfl) ⟨1119068, by rfl⟩ : syracuseStep 1492091 = 2238137) B2238137
theorem B1492217 : Blo 662308 1492217 := bstep (se 2 (by rfl) ⟨559581, by rfl⟩ : syracuseStep 1492217 = 1119163) B1119163
theorem B1066279 : Blo 662308 1066279 := bstep (se 1 (by rfl) ⟨799709, by rfl⟩ : syracuseStep 1066279 = 1599419) B1599419
theorem B2835755 : Blo 662308 2835755 := bstep (se 1 (by rfl) ⟨2126816, by rfl⟩ : syracuseStep 2835755 = 4253633) B4253633
theorem B1492361 : Blo 662308 1492361 := bstep (se 2 (by rfl) ⟨559635, by rfl⟩ : syracuseStep 1492361 = 1119271) B1119271
theorem B1492487 : Blo 662308 1492487 := bstep (se 1 (by rfl) ⟨1119365, by rfl⟩ : syracuseStep 1492487 = 2238731) B2238731
theorem B4245149 : Blo 662308 4245149 := bstep (se 3 (by rfl) ⟨795965, by rfl⟩ : syracuseStep 4245149 = 1591931) B1591931
theorem B1492667 : Blo 662308 1492667 := bstep (se 1 (by rfl) ⟨1119500, by rfl⟩ : syracuseStep 1492667 = 2239001) B2239001
theorem B1197755 : Blo 662308 1197755 := bstep (se 1 (by rfl) ⟨898316, by rfl⟩ : syracuseStep 1197755 = 1796633) B1796633
theorem B1492793 : Blo 662308 1492793 := bstep (se 2 (by rfl) ⟨559797, by rfl⟩ : syracuseStep 1492793 = 1119595) B1119595
theorem B2836745 : Blo 662308 2836745 := bstep (se 2 (by rfl) ⟨1063779, by rfl⟩ : syracuseStep 2836745 = 2127559) B2127559
theorem B1493423 : Blo 662308 1493423 := bstep (se 1 (by rfl) ⟨1120067, by rfl⟩ : syracuseStep 1493423 = 2240135) B2240135
theorem B1493459 : Blo 662308 1493459 := bstep (se 1 (by rfl) ⟨1120094, by rfl⟩ : syracuseStep 1493459 = 2240189) B2240189
theorem B1493567 : Blo 662308 1493567 := bstep (se 1 (by rfl) ⟨1120175, by rfl⟩ : syracuseStep 1493567 = 2240351) B2240351
theorem B1493675 : Blo 662308 1493675 := bstep (se 1 (by rfl) ⟨1120256, by rfl⟩ : syracuseStep 1493675 = 2240513) B2240513
theorem B11324285 : Blo 662308 11324285 := bstep (se 3 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 11324285 = 4246607) B4246607
theorem B3361661 : Blo 662308 3361661 := bstep (se 3 (by rfl) ⟨630311, by rfl⟩ : syracuseStep 3361661 = 1260623) B1260623
theorem B1887131 : Blo 662308 1887131 := bstep (se 1 (by rfl) ⟨1415348, by rfl⟩ : syracuseStep 1887131 = 2830697) B2830697
theorem B2247803 : Blo 662308 2247803 := bstep (se 1 (by rfl) ⟨1685852, by rfl⟩ : syracuseStep 2247803 = 3371705) B3371705
theorem B1887371 : Blo 662308 1887371 := bstep (se 1 (by rfl) ⟨1415528, by rfl⟩ : syracuseStep 1887371 = 2831057) B2831057
theorem B1494215 : Blo 662308 1494215 := bstep (se 1 (by rfl) ⟨1120661, by rfl⟩ : syracuseStep 1494215 = 2241323) B2241323
theorem B1494395 : Blo 662308 1494395 := bstep (se 1 (by rfl) ⟨1120796, by rfl⟩ : syracuseStep 1494395 = 2241593) B2241593
theorem B2248073 : Blo 662308 2248073 := bstep (se 2 (by rfl) ⟨843027, by rfl⟩ : syracuseStep 2248073 = 1686055) B1686055
theorem B24563087 : Blo 662308 24563087 := bstep (se 1 (by rfl) ⟨18422315, by rfl⟩ : syracuseStep 24563087 = 36844631) B36844631
theorem B1494521 : Blo 662308 1494521 := bstep (se 2 (by rfl) ⟨560445, by rfl⟩ : syracuseStep 1494521 = 1120891) B1120891
theorem B3198473 : Blo 662308 3198473 := bstep (se 2 (by rfl) ⟨1199427, by rfl⟩ : syracuseStep 3198473 = 2398855) B2398855
theorem B1494611 : Blo 662308 1494611 := bstep (se 1 (by rfl) ⟨1120958, by rfl⟩ : syracuseStep 1494611 = 2241917) B2241917
theorem B4247275 : Blo 662308 4247275 := bstep (se 1 (by rfl) ⟨3185456, by rfl⟩ : syracuseStep 4247275 = 6370913) B6370913
theorem B1494791 : Blo 662308 1494791 := bstep (se 1 (by rfl) ⟨1121093, by rfl⟩ : syracuseStep 1494791 = 2242187) B2242187
theorem B839479 : Blo 662308 839479 := bstep (se 1 (by rfl) ⟨629609, by rfl⟩ : syracuseStep 839479 = 1259219) B1259219
theorem B2248505 : Blo 662308 2248505 := bstep (se 2 (by rfl) ⟨843189, by rfl⟩ : syracuseStep 2248505 = 1686379) B1686379
theorem B3362633 : Blo 662308 3362633 := bstep (se 2 (by rfl) ⟨1260987, by rfl⟩ : syracuseStep 3362633 = 2521975) B2521975
theorem B3199027 : Blo 662308 3199027 := bstep (se 1 (by rfl) ⟨2399270, by rfl⟩ : syracuseStep 3199027 = 4798541) B4798541
theorem B839899 : Blo 662308 839899 := bstep (se 1 (by rfl) ⟨629924, by rfl⟩ : syracuseStep 839899 = 1259849) B1259849
theorem B1495403 : Blo 662308 1495403 := bstep (se 1 (by rfl) ⟨1121552, by rfl⟩ : syracuseStep 1495403 = 2243105) B2243105
theorem B1495547 : Blo 662308 1495547 := bstep (se 1 (by rfl) ⟨1121660, by rfl⟩ : syracuseStep 1495547 = 2243321) B2243321
theorem B1495673 : Blo 662308 1495673 := bstep (se 2 (by rfl) ⟨560877, by rfl⟩ : syracuseStep 1495673 = 1121755) B1121755
theorem B1495727 : Blo 662308 1495727 := bstep (se 1 (by rfl) ⟨1121795, by rfl⟩ : syracuseStep 1495727 = 2243591) B2243591
theorem B1495799 : Blo 662308 1495799 := bstep (se 1 (by rfl) ⟨1121849, by rfl⟩ : syracuseStep 1495799 = 2243699) B2243699
theorem B807727 : Blo 662308 807727 := bstep (se 1 (by rfl) ⟨605795, by rfl⟩ : syracuseStep 807727 = 1211591) B1211591
theorem B1495979 : Blo 662308 1495979 := bstep (se 1 (by rfl) ⟨1121984, by rfl⟩ : syracuseStep 1495979 = 2243969) B2243969
theorem B3363929 : Blo 662308 3363929 := bstep (se 2 (by rfl) ⟨1261473, by rfl⟩ : syracuseStep 3363929 = 2522947) B2522947
theorem B1889659 : Blo 662308 1889659 := bstep (se 1 (by rfl) ⟨1417244, by rfl⟩ : syracuseStep 1889659 = 2834489) B2834489
theorem B8508797 : Blo 662308 8508797 := bstep (se 3 (by rfl) ⟨1595399, by rfl⟩ : syracuseStep 8508797 = 3190799) B3190799
theorem B1496519 : Blo 662308 1496519 := bstep (se 1 (by rfl) ⟨1122389, by rfl⟩ : syracuseStep 1496519 = 2244779) B2244779
theorem B972281 : Blo 662308 972281 := bstep (se 2 (by rfl) ⟨364605, by rfl⟩ : syracuseStep 972281 = 729211) B729211
theorem B7296551 : Blo 662308 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B4249273 : Blo 662308 4249273 := bstep (se 2 (by rfl) ⟨1593477, by rfl⟩ : syracuseStep 4249273 = 3186955) B3186955
theorem B841519 : Blo 662308 841519 := bstep (se 1 (by rfl) ⟨631139, by rfl⟩ : syracuseStep 841519 = 1262279) B1262279
theorem B1496879 : Blo 662308 1496879 := bstep (se 1 (by rfl) ⟨1122659, by rfl⟩ : syracuseStep 1496879 = 2245319) B2245319
theorem B2840503 : Blo 662308 2840503 := bstep (se 1 (by rfl) ⟨2130377, by rfl⟩ : syracuseStep 2840503 = 4260755) B4260755
theorem B1595497 : Blo 662308 1595497 := bstep (se 2 (by rfl) ⟨598311, by rfl⟩ : syracuseStep 1595497 = 1196623) B1196623
theorem B710875 : Blo 662308 710875 := bstep (se 1 (by rfl) ⟨533156, by rfl⟩ : syracuseStep 710875 = 1066313) B1066313
theorem B842015 : Blo 662308 842015 := bstep (se 1 (by rfl) ⟨631511, by rfl⟩ : syracuseStep 842015 = 1263023) B1263023
theorem B1497455 : Blo 662308 1497455 := bstep (se 1 (by rfl) ⟨1123091, by rfl⟩ : syracuseStep 1497455 = 2246183) B2246183
theorem B711023 : Blo 662308 711023 := bstep (se 1 (by rfl) ⟨533267, by rfl⟩ : syracuseStep 711023 = 1066535) B1066535
theorem B1497527 : Blo 662308 1497527 := bstep (se 1 (by rfl) ⟨1123145, by rfl⟩ : syracuseStep 1497527 = 2246291) B2246291
theorem B1497671 : Blo 662308 1497671 := bstep (se 1 (by rfl) ⟨1123253, by rfl⟩ : syracuseStep 1497671 = 2246507) B2246507
theorem B1497707 : Blo 662308 1497707 := bstep (se 1 (by rfl) ⟨1123280, by rfl⟩ : syracuseStep 1497707 = 2246561) B2246561
theorem B6576815 : Blo 662308 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B5462939 : Blo 662308 5462939 := bstep (se 1 (by rfl) ⟨4097204, by rfl⟩ : syracuseStep 5462939 = 8194409) B8194409
theorem B1498103 : Blo 662308 1498103 := bstep (se 1 (by rfl) ⟨1123577, by rfl⟩ : syracuseStep 1498103 = 2247155) B2247155
theorem B5201117 : Blo 662308 5201117 := bstep (se 3 (by rfl) ⟨975209, by rfl⟩ : syracuseStep 5201117 = 1950419) B1950419
theorem B3595531 : Blo 662308 3595531 := bstep (se 1 (by rfl) ⟨2696648, by rfl⟩ : syracuseStep 3595531 = 5393297) B5393297
theorem B1498463 : Blo 662308 1498463 := bstep (se 1 (by rfl) ⟨1123847, by rfl⟩ : syracuseStep 1498463 = 2247695) B2247695
theorem B28761479 : Blo 662308 28761479 := bstep (se 1 (by rfl) ⟨21571109, by rfl⟩ : syracuseStep 28761479 = 43142219) B43142219
theorem B1793441 : Blo 662308 1793441 := bstep (se 2 (by rfl) ⟨672540, by rfl⟩ : syracuseStep 1793441 = 1345081) B1345081
theorem B3366359 : Blo 662308 3366359 := bstep (se 1 (by rfl) ⟨2524769, by rfl⟩ : syracuseStep 3366359 = 5049539) B5049539
theorem B1498859 : Blo 662308 1498859 := bstep (se 1 (by rfl) ⟨1124144, by rfl⟩ : syracuseStep 1498859 = 2248289) B2248289
theorem B1793897 : Blo 662308 1793897 := bstep (se 2 (by rfl) ⟨672711, by rfl⟩ : syracuseStep 1793897 = 1345423) B1345423
theorem B1498985 : Blo 662308 1498985 := bstep (se 2 (by rfl) ⟨562119, by rfl⟩ : syracuseStep 1498985 = 1124239) B1124239
theorem B3039133 : Blo 662308 3039133 := bstep (se 3 (by rfl) ⟨569837, by rfl⟩ : syracuseStep 3039133 = 1139675) B1139675
theorem B1597391 : Blo 662308 1597391 := bstep (se 1 (by rfl) ⟨1198043, by rfl⟩ : syracuseStep 1597391 = 2396087) B2396087
theorem B745447 : Blo 662308 745447 := bstep (se 1 (by rfl) ⟨559085, by rfl⟩ : syracuseStep 745447 = 1118171) B1118171
theorem B1794479 : Blo 662308 1794479 := bstep (se 1 (by rfl) ⟨1345859, by rfl⟩ : syracuseStep 1794479 = 2691719) B2691719
theorem B2515475 : Blo 662308 2515475 := bstep (se 1 (by rfl) ⟨1886606, by rfl⟩ : syracuseStep 2515475 = 3773213) B3773213
theorem B1139321 : Blo 662308 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B13656721 : Blo 662308 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B4842155 : Blo 662308 4842155 := bstep (se 1 (by rfl) ⟨3631616, by rfl⟩ : syracuseStep 4842155 = 7263233) B7263233
theorem B1434539 : Blo 662308 1434539 := bstep (se 1 (by rfl) ⟨1075904, by rfl⟩ : syracuseStep 1434539 = 2151809) B2151809
theorem B2515931 : Blo 662308 2515931 := bstep (se 1 (by rfl) ⟨1886948, by rfl⟩ : syracuseStep 2515931 = 3773897) B3773897
theorem B4842499 : Blo 662308 4842499 := bstep (se 1 (by rfl) ⟨3631874, by rfl⟩ : syracuseStep 4842499 = 7263749) B7263749
theorem B2122985 : Blo 662308 2122985 := bstep (se 2 (by rfl) ⟨796119, by rfl⟩ : syracuseStep 2122985 = 1592239) B1592239
theorem B747103 : Blo 662308 747103 := bstep (se 1 (by rfl) ⟨560327, by rfl⟩ : syracuseStep 747103 = 1120655) B1120655
theorem B23029505 : Blo 662308 23029505 := bstep (se 2 (by rfl) ⟨8636064, by rfl⟩ : syracuseStep 23029505 = 17272129) B17272129
theorem B943913 : Blo 662308 943913 := bstep (se 2 (by rfl) ⟨353967, by rfl⟩ : syracuseStep 943913 = 707935) B707935
theorem B2844503 : Blo 662308 2844503 := bstep (se 1 (by rfl) ⟨2133377, by rfl⟩ : syracuseStep 2844503 = 4266755) B4266755
theorem B6482035 : Blo 662308 6482035 := bstep (se 1 (by rfl) ⟨4861526, by rfl⟩ : syracuseStep 6482035 = 9723053) B9723053
theorem B10217657 : Blo 662308 10217657 := bstep (se 2 (by rfl) ⟨3831621, by rfl⟩ : syracuseStep 10217657 = 7663243) B7663243
theorem B1599851 : Blo 662308 1599851 := bstep (se 1 (by rfl) ⟨1199888, by rfl⟩ : syracuseStep 1599851 = 2399777) B2399777
theorem B944551 : Blo 662308 944551 := bstep (se 1 (by rfl) ⟨708413, by rfl⟩ : syracuseStep 944551 = 1416827) B1416827
theorem B2124215 : Blo 662308 2124215 := bstep (se 1 (by rfl) ⟨1593161, by rfl⟩ : syracuseStep 2124215 = 3186323) B3186323
theorem B748255 : Blo 662308 748255 := bstep (se 1 (by rfl) ⟨561191, by rfl⟩ : syracuseStep 748255 = 1122383) B1122383
theorem B5663783 : Blo 662308 5663783 := bstep (se 1 (by rfl) ⟨4247837, by rfl⟩ : syracuseStep 5663783 = 8495675) B8495675
theorem B945371 : Blo 662308 945371 := bstep (se 1 (by rfl) ⟨709028, by rfl⟩ : syracuseStep 945371 = 1418057) B1418057
theorem B748831 : Blo 662308 748831 := bstep (se 1 (by rfl) ⟨561623, by rfl⟩ : syracuseStep 748831 = 1123247) B1123247
theorem B7204211 : Blo 662308 7204211 := bstep (se 1 (by rfl) ⟨5403158, by rfl⟩ : syracuseStep 7204211 = 10806317) B10806317
theorem B2518391 : Blo 662308 2518391 := bstep (se 1 (by rfl) ⟨1888793, by rfl⟩ : syracuseStep 2518391 = 3777587) B3777587
theorem B1895879 : Blo 662308 1895879 := bstep (se 1 (by rfl) ⟨1421909, by rfl⟩ : syracuseStep 1895879 = 2843819) B2843819
theorem B6155837 : Blo 662308 6155837 := bstep (se 3 (by rfl) ⟨1154219, by rfl⟩ : syracuseStep 6155837 = 2308439) B2308439
theorem B749119 : Blo 662308 749119 := bstep (se 1 (by rfl) ⟨561839, by rfl⟩ : syracuseStep 749119 = 1123679) B1123679
theorem B4255811 : Blo 662308 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B3371219 : Blo 662308 3371219 := bstep (se 1 (by rfl) ⟨2528414, by rfl⟩ : syracuseStep 3371219 = 5056829) B5056829
theorem B2553065 : Blo 662308 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B2127097 : Blo 662308 2127097 := bstep (se 2 (by rfl) ⟨797661, by rfl⟩ : syracuseStep 2127097 = 1595323) B1595323
theorem B1275175 : Blo 662308 1275175 := bstep (se 1 (by rfl) ⟨956381, by rfl⟩ : syracuseStep 1275175 = 1912763) B1912763
theorem B947495 : Blo 662308 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B3601759 : Blo 662308 3601759 := bstep (se 1 (by rfl) ⟨2701319, by rfl⟩ : syracuseStep 3601759 = 5402639) B5402639
theorem B3405401 : Blo 662308 3405401 := bstep (se 2 (by rfl) ⟨1277025, by rfl⟩ : syracuseStep 3405401 = 2554051) B2554051
theorem B2128457 : Blo 662308 2128457 := bstep (se 2 (by rfl) ⟨798171, by rfl⟩ : syracuseStep 2128457 = 1596343) B1596343
theorem B7174763 : Blo 662308 7174763 := bstep (se 1 (by rfl) ⟨5381072, by rfl⟩ : syracuseStep 7174763 = 10762145) B10762145
theorem B32733829 : Blo 662308 32733829 := bstep (se 4 (by rfl) ⟨3068796, by rfl⟩ : syracuseStep 32733829 = 6137593) B6137593
theorem B5045165 : Blo 662308 5045165 := bstep (se 3 (by rfl) ⟨945968, by rfl⟩ : syracuseStep 5045165 = 1891937) B1891937
theorem B1277147 : Blo 662308 1277147 := bstep (se 1 (by rfl) ⟨957860, by rfl⟩ : syracuseStep 1277147 = 1915721) B1915721
theorem B1703263 : Blo 662308 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B1441223 : Blo 662308 1441223 := bstep (se 1 (by rfl) ⟨1080917, by rfl⟩ : syracuseStep 1441223 = 2161835) B2161835
theorem B25886213 : Blo 662308 25886213 := bstep (se 4 (by rfl) ⟨2426832, by rfl⟩ : syracuseStep 25886213 = 4853665) B4853665
theorem B1343071 : Blo 662308 1343071 := bstep (se 1 (by rfl) ⟨1007303, by rfl⟩ : syracuseStep 1343071 = 2014607) B2014607
theorem B3244313 : Blo 662308 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B1704577 : Blo 662308 1704577 := bstep (se 2 (by rfl) ⟨639216, by rfl⟩ : syracuseStep 1704577 = 1278433) B1278433
theorem B4785277 : Blo 662308 4785277 := bstep (se 3 (by rfl) ⟨897239, by rfl⟩ : syracuseStep 4785277 = 1794479) B1794479
theorem B6456665 : Blo 662308 6456665 := bstep (se 2 (by rfl) ⟨2421249, by rfl⟩ : syracuseStep 6456665 = 4842499) B4842499
theorem B2132315 : Blo 662308 2132315 := bstep (se 1 (by rfl) ⟨1599236, by rfl⟩ : syracuseStep 2132315 = 3198473) B3198473
theorem B2526653 : Blo 662308 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B1117759 : Blo 662308 1117759 := bstep (se 1 (by rfl) ⟨838319, by rfl⟩ : syracuseStep 1117759 = 1676639) B1676639
theorem B5672531 : Blo 662308 5672531 := bstep (se 1 (by rfl) ⟨4254398, by rfl⟩ : syracuseStep 5672531 = 8508797) B8508797
theorem B29200193 : Blo 662308 29200193 := bstep (se 2 (by rfl) ⟨10950072, by rfl⟩ : syracuseStep 29200193 = 21900145) B21900145
theorem B8064845 : Blo 662308 8064845 := bstep (se 3 (by rfl) ⟨1512158, by rfl⟩ : syracuseStep 8064845 = 3024317) B3024317
theorem B2592749 : Blo 662308 2592749 := bstep (se 3 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 2592749 = 972281) B972281
theorem B4427929 : Blo 662308 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B1118495 : Blo 662308 1118495 := bstep (se 1 (by rfl) ⟨838871, by rfl⟩ : syracuseStep 1118495 = 1677743) B1677743
theorem B3641959 : Blo 662308 3641959 := bstep (se 1 (by rfl) ⟨2731469, by rfl⟩ : syracuseStep 3641959 = 5462939) B5462939
theorem B1119143 : Blo 662308 1119143 := bstep (se 1 (by rfl) ⟨839357, by rfl⟩ : syracuseStep 1119143 = 1678715) B1678715
theorem B19174319 : Blo 662308 19174319 := bstep (se 1 (by rfl) ⟨14380739, by rfl⟩ : syracuseStep 19174319 = 28761479) B28761479
theorem B1119305 : Blo 662308 1119305 := bstep (se 2 (by rfl) ⟨419739, by rfl⟩ : syracuseStep 1119305 = 839479) B839479
theorem B4265369 : Blo 662308 4265369 := bstep (se 2 (by rfl) ⟨1599513, by rfl⟩ : syracuseStep 4265369 = 3199027) B3199027
theorem B1119865 : Blo 662308 1119865 := bstep (se 2 (by rfl) ⟨419949, by rfl⟩ : syracuseStep 1119865 = 839899) B839899
theorem B1676983 : Blo 662308 1676983 := bstep (se 1 (by rfl) ⟨1257737, by rfl⟩ : syracuseStep 1676983 = 2515475) B2515475
theorem B759547 : Blo 662308 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B3643193 : Blo 662308 3643193 := bstep (se 2 (by rfl) ⟨1366197, by rfl⟩ : syracuseStep 3643193 = 2732395) B2732395
theorem B956359 : Blo 662308 956359 := bstep (se 1 (by rfl) ⟨717269, by rfl⟩ : syracuseStep 956359 = 1434539) B1434539
theorem B1677287 : Blo 662308 1677287 := bstep (se 1 (by rfl) ⟨1257965, by rfl⟩ : syracuseStep 1677287 = 2515931) B2515931
theorem B1120351 : Blo 662308 1120351 := bstep (se 1 (by rfl) ⟨840263, by rfl⟩ : syracuseStep 1120351 = 1680527) B1680527
theorem B1415323 : Blo 662308 1415323 := bstep (se 1 (by rfl) ⟨1061492, by rfl⟩ : syracuseStep 1415323 = 2122985) B2122985
theorem B4266269 : Blo 662308 4266269 := bstep (se 3 (by rfl) ⟨799925, by rfl⟩ : syracuseStep 4266269 = 1599851) B1599851
theorem B662363 : Blo 662308 662363 := bstep (se 1 (by rfl) ⟨496772, by rfl⟩ : syracuseStep 662363 = 993545) B993545
theorem B662431 : Blo 662308 662431 := bstep (se 1 (by rfl) ⟨496823, by rfl⟩ : syracuseStep 662431 = 993647) B993647
theorem B1416143 : Blo 662308 1416143 := bstep (se 1 (by rfl) ⟨1062107, by rfl⟩ : syracuseStep 1416143 = 2124215) B2124215
theorem B2235383 : Blo 662308 2235383 := bstep (se 1 (by rfl) ⟨1676537, by rfl⟩ : syracuseStep 2235383 = 3353075) B3353075
theorem B662575 : Blo 662308 662575 := bstep (se 1 (by rfl) ⟨496931, by rfl⟩ : syracuseStep 662575 = 993863) B993863
theorem B662599 : Blo 662308 662599 := bstep (se 1 (by rfl) ⟨496949, by rfl⟩ : syracuseStep 662599 = 993899) B993899
theorem B3775673 : Blo 662308 3775673 := bstep (se 2 (by rfl) ⟨1415877, by rfl⟩ : syracuseStep 3775673 = 2831755) B2831755
theorem B662751 : Blo 662308 662751 := bstep (se 1 (by rfl) ⟨497063, by rfl⟩ : syracuseStep 662751 = 994127) B994127
theorem B3775855 : Blo 662308 3775855 := bstep (se 1 (by rfl) ⟨2831891, by rfl⟩ : syracuseStep 3775855 = 5663783) B5663783
theorem B1121647 : Blo 662308 1121647 := bstep (se 1 (by rfl) ⟨841235, by rfl⟩ : syracuseStep 1121647 = 1682471) B1682471
theorem B2235815 : Blo 662308 2235815 := bstep (se 1 (by rfl) ⟨1676861, by rfl⟩ : syracuseStep 2235815 = 3353723) B3353723
theorem B663015 : Blo 662308 663015 := bstep (se 1 (by rfl) ⟨497261, by rfl⟩ : syracuseStep 663015 = 994523) B994523
theorem B1678927 : Blo 662308 1678927 := bstep (se 1 (by rfl) ⟨1259195, by rfl⟩ : syracuseStep 1678927 = 2518391) B2518391
theorem B663131 : Blo 662308 663131 := bstep (se 1 (by rfl) ⟨497348, by rfl⟩ : syracuseStep 663131 = 994697) B994697
theorem B4103891 : Blo 662308 4103891 := bstep (se 1 (by rfl) ⟨3077918, by rfl⟩ : syracuseStep 4103891 = 6155837) B6155837
theorem B1122025 : Blo 662308 1122025 := bstep (se 2 (by rfl) ⟨420759, by rfl⟩ : syracuseStep 1122025 = 841519) B841519
theorem B663367 : Blo 662308 663367 := bstep (se 1 (by rfl) ⟨497525, by rfl⟩ : syracuseStep 663367 = 995051) B995051
theorem B2236247 : Blo 662308 2236247 := bstep (se 1 (by rfl) ⟨1677185, by rfl⟩ : syracuseStep 2236247 = 3354371) B3354371
theorem B663519 : Blo 662308 663519 := bstep (se 1 (by rfl) ⟨497639, by rfl⟩ : syracuseStep 663519 = 995279) B995279
theorem B1122491 : Blo 662308 1122491 := bstep (se 1 (by rfl) ⟨841868, by rfl⟩ : syracuseStep 1122491 = 1683737) B1683737
theorem B663783 : Blo 662308 663783 := bstep (se 1 (by rfl) ⟨497837, by rfl⟩ : syracuseStep 663783 = 995675) B995675
theorem B663935 : Blo 662308 663935 := bstep (se 1 (by rfl) ⟨497951, by rfl⟩ : syracuseStep 663935 = 995903) B995903
theorem B664015 : Blo 662308 664015 := bstep (se 1 (by rfl) ⟨498011, by rfl⟩ : syracuseStep 664015 = 996023) B996023
theorem B1679849 : Blo 662308 1679849 := bstep (se 2 (by rfl) ⟨629943, by rfl⟩ : syracuseStep 1679849 = 1259887) B1259887
theorem B664167 : Blo 662308 664167 := bstep (se 1 (by rfl) ⟨498125, by rfl⟩ : syracuseStep 664167 = 996251) B996251
theorem B2237057 : Blo 662308 2237057 := bstep (se 2 (by rfl) ⟨838896, by rfl⟩ : syracuseStep 2237057 = 1677793) B1677793
theorem B1123051 : Blo 662308 1123051 := bstep (se 1 (by rfl) ⟨842288, by rfl⟩ : syracuseStep 1123051 = 1684577) B1684577
theorem B2302739 : Blo 662308 2302739 := bstep (se 1 (by rfl) ⟨1727054, by rfl⟩ : syracuseStep 2302739 = 3454109) B3454109
theorem B664431 : Blo 662308 664431 := bstep (se 1 (by rfl) ⟨498323, by rfl⟩ : syracuseStep 664431 = 996647) B996647
theorem B2237327 : Blo 662308 2237327 := bstep (se 1 (by rfl) ⟨1677995, by rfl⟩ : syracuseStep 2237327 = 3355991) B3355991
theorem B664487 : Blo 662308 664487 := bstep (se 1 (by rfl) ⟨498365, by rfl⟩ : syracuseStep 664487 = 996731) B996731
theorem B664571 : Blo 662308 664571 := bstep (se 1 (by rfl) ⟨498428, by rfl⟩ : syracuseStep 664571 = 996857) B996857
theorem B2270267 : Blo 662308 2270267 := bstep (se 1 (by rfl) ⟨1702700, by rfl⟩ : syracuseStep 2270267 = 3405401) B3405401
theorem B664639 : Blo 662308 664639 := bstep (se 1 (by rfl) ⟨498479, by rfl⟩ : syracuseStep 664639 = 996959) B996959
theorem B664783 : Blo 662308 664783 := bstep (se 1 (by rfl) ⟨498587, by rfl⟩ : syracuseStep 664783 = 997175) B997175
theorem B664987 : Blo 662308 664987 := bstep (se 1 (by rfl) ⟨498740, by rfl⟩ : syracuseStep 664987 = 997481) B997481
theorem B2237867 : Blo 662308 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B1516975 : Blo 662308 1516975 := bstep (se 1 (by rfl) ⟨1137731, by rfl⟩ : syracuseStep 1516975 = 2275463) B2275463
theorem B665199 : Blo 662308 665199 := bstep (se 1 (by rfl) ⟨498899, by rfl⟩ : syracuseStep 665199 = 997799) B997799
theorem B665255 : Blo 662308 665255 := bstep (se 1 (by rfl) ⟨498941, by rfl⟩ : syracuseStep 665255 = 997883) B997883
theorem B1124023 : Blo 662308 1124023 := bstep (se 1 (by rfl) ⟨843017, by rfl⟩ : syracuseStep 1124023 = 1686035) B1686035
theorem B4794041 : Blo 662308 4794041 := bstep (se 2 (by rfl) ⟨1797765, by rfl⟩ : syracuseStep 4794041 = 3595531) B3595531
theorem B1418971 : Blo 662308 1418971 := bstep (se 1 (by rfl) ⟨1064228, by rfl⟩ : syracuseStep 1418971 = 2128457) B2128457
theorem B665339 : Blo 662308 665339 := bstep (se 1 (by rfl) ⟨499004, by rfl⟩ : syracuseStep 665339 = 998009) B998009
theorem B665375 : Blo 662308 665375 := bstep (se 1 (by rfl) ⟨499031, by rfl⟩ : syracuseStep 665375 = 998063) B998063
theorem B2271017 : Blo 662308 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B665407 : Blo 662308 665407 := bstep (se 1 (by rfl) ⟨499055, by rfl⟩ : syracuseStep 665407 = 998111) B998111
theorem B2238407 : Blo 662308 2238407 := bstep (se 1 (by rfl) ⟨1678805, by rfl⟩ : syracuseStep 2238407 = 3357611) B3357611
theorem B1124327 : Blo 662308 1124327 := bstep (se 1 (by rfl) ⟨843245, by rfl⟩ : syracuseStep 1124327 = 1686491) B1686491
theorem B665583 : Blo 662308 665583 := bstep (se 1 (by rfl) ⟨499187, by rfl⟩ : syracuseStep 665583 = 998375) B998375
theorem B665755 : Blo 662308 665755 := bstep (se 1 (by rfl) ⟨499316, by rfl⟩ : syracuseStep 665755 = 998633) B998633
theorem B665791 : Blo 662308 665791 := bstep (se 1 (by rfl) ⟨499343, by rfl⟩ : syracuseStep 665791 = 998687) B998687
theorem B993515 : Blo 662308 993515 := bstep (se 1 (by rfl) ⟨745136, by rfl⟩ : syracuseStep 993515 = 1490273) B1490273
theorem B993575 : Blo 662308 993575 := bstep (se 1 (by rfl) ⟨745181, by rfl⟩ : syracuseStep 993575 = 1490363) B1490363
theorem B960815 : Blo 662308 960815 := bstep (se 1 (by rfl) ⟨720611, by rfl⟩ : syracuseStep 960815 = 1441223) B1441223
theorem B665903 : Blo 662308 665903 := bstep (se 1 (by rfl) ⟨499427, by rfl⟩ : syracuseStep 665903 = 998855) B998855
theorem B993659 : Blo 662308 993659 := bstep (se 1 (by rfl) ⟨745244, by rfl⟩ : syracuseStep 993659 = 1490489) B1490489
theorem B666139 : Blo 662308 666139 := bstep (se 1 (by rfl) ⟨499604, by rfl⟩ : syracuseStep 666139 = 999209) B999209
theorem B666143 : Blo 662308 666143 := bstep (se 1 (by rfl) ⟨499607, by rfl⟩ : syracuseStep 666143 = 999215) B999215
theorem B993929 : Blo 662308 993929 := bstep (se 2 (by rfl) ⟨372723, by rfl⟩ : syracuseStep 993929 = 745447) B745447
theorem B2239163 : Blo 662308 2239163 := bstep (se 1 (by rfl) ⟨1679372, by rfl⟩ : syracuseStep 2239163 = 3358745) B3358745
theorem B3353399 : Blo 662308 3353399 := bstep (se 1 (by rfl) ⟨2515049, by rfl⟩ : syracuseStep 3353399 = 5030099) B5030099
theorem B994103 : Blo 662308 994103 := bstep (se 1 (by rfl) ⟨745577, by rfl⟩ : syracuseStep 994103 = 1491155) B1491155
theorem B4795195 : Blo 662308 4795195 := bstep (se 1 (by rfl) ⟨3596396, by rfl⟩ : syracuseStep 4795195 = 7192793) B7192793
theorem B994139 : Blo 662308 994139 := bstep (se 1 (by rfl) ⟨745604, by rfl⟩ : syracuseStep 994139 = 1491209) B1491209
theorem B4041667 : Blo 662308 4041667 := bstep (se 1 (by rfl) ⟨3031250, by rfl⟩ : syracuseStep 4041667 = 6062501) B6062501
theorem B994283 : Blo 662308 994283 := bstep (se 1 (by rfl) ⟨745712, by rfl⟩ : syracuseStep 994283 = 1491425) B1491425
theorem B994487 : Blo 662308 994487 := bstep (se 1 (by rfl) ⟨745865, by rfl⟩ : syracuseStep 994487 = 1491731) B1491731
theorem B18132311 : Blo 662308 18132311 := bstep (se 1 (by rfl) ⟨13599233, by rfl⟩ : syracuseStep 18132311 = 27198467) B27198467
theorem B994727 : Blo 662308 994727 := bstep (se 1 (by rfl) ⟨746045, by rfl⟩ : syracuseStep 994727 = 1492091) B1492091
theorem B994811 : Blo 662308 994811 := bstep (se 1 (by rfl) ⟨746108, by rfl⟩ : syracuseStep 994811 = 1492217) B1492217
theorem B994907 : Blo 662308 994907 := bstep (se 1 (by rfl) ⟨746180, by rfl⟩ : syracuseStep 994907 = 1492361) B1492361
theorem B994991 : Blo 662308 994991 := bstep (se 1 (by rfl) ⟨746243, by rfl⟩ : syracuseStep 994991 = 1492487) B1492487
theorem B1683119 : Blo 662308 1683119 := bstep (se 1 (by rfl) ⟨1262339, by rfl⟩ : syracuseStep 1683119 = 2524679) B2524679
theorem B2830099 : Blo 662308 2830099 := bstep (se 1 (by rfl) ⟨2122574, by rfl⟩ : syracuseStep 2830099 = 4245149) B4245149
theorem B995111 : Blo 662308 995111 := bstep (se 1 (by rfl) ⟨746333, by rfl⟩ : syracuseStep 995111 = 1492667) B1492667
theorem B798503 : Blo 662308 798503 := bstep (se 1 (by rfl) ⟨598877, by rfl⟩ : syracuseStep 798503 = 1197755) B1197755
theorem B995195 : Blo 662308 995195 := bstep (se 1 (by rfl) ⟨746396, by rfl⟩ : syracuseStep 995195 = 1492793) B1492793
theorem B1683443 : Blo 662308 1683443 := bstep (se 1 (by rfl) ⟨1262582, by rfl⟩ : syracuseStep 1683443 = 2525165) B2525165
theorem B995615 : Blo 662308 995615 := bstep (se 1 (by rfl) ⟨746711, by rfl⟩ : syracuseStep 995615 = 1493423) B1493423
theorem B995639 : Blo 662308 995639 := bstep (se 1 (by rfl) ⟨746729, by rfl⟩ : syracuseStep 995639 = 1493459) B1493459
theorem B1683767 : Blo 662308 1683767 := bstep (se 1 (by rfl) ⟨1262825, by rfl⟩ : syracuseStep 1683767 = 2525651) B2525651
theorem B995711 : Blo 662308 995711 := bstep (se 1 (by rfl) ⟨746783, by rfl⟩ : syracuseStep 995711 = 1493567) B1493567
theorem B1421705 : Blo 662308 1421705 := bstep (se 2 (by rfl) ⟨533139, by rfl⟩ : syracuseStep 1421705 = 1066279) B1066279
theorem B8532377 : Blo 662308 8532377 := bstep (se 2 (by rfl) ⟨3199641, by rfl⟩ : syracuseStep 8532377 = 6399283) B6399283
theorem B995783 : Blo 662308 995783 := bstep (se 1 (by rfl) ⟨746837, by rfl⟩ : syracuseStep 995783 = 1493675) B1493675
theorem B7549523 : Blo 662308 7549523 := bstep (se 1 (by rfl) ⟨5662142, by rfl⟩ : syracuseStep 7549523 = 11324285) B11324285
theorem B2241107 : Blo 662308 2241107 := bstep (se 1 (by rfl) ⟨1680830, by rfl⟩ : syracuseStep 2241107 = 3361661) B3361661
theorem B1258087 : Blo 662308 1258087 := bstep (se 1 (by rfl) ⟨943565, by rfl⟩ : syracuseStep 1258087 = 1887131) B1887131
theorem B1258247 : Blo 662308 1258247 := bstep (se 1 (by rfl) ⟨943685, by rfl⟩ : syracuseStep 1258247 = 1887371) B1887371
theorem B996137 : Blo 662308 996137 := bstep (se 2 (by rfl) ⟨373551, by rfl⟩ : syracuseStep 996137 = 747103) B747103
theorem B996143 : Blo 662308 996143 := bstep (se 1 (by rfl) ⟨747107, by rfl⟩ : syracuseStep 996143 = 1494215) B1494215
theorem B996263 : Blo 662308 996263 := bstep (se 1 (by rfl) ⟨747197, by rfl⟩ : syracuseStep 996263 = 1494395) B1494395
theorem B8500139 : Blo 662308 8500139 := bstep (se 1 (by rfl) ⟨6375104, by rfl⟩ : syracuseStep 8500139 = 12750209) B12750209
theorem B996347 : Blo 662308 996347 := bstep (se 1 (by rfl) ⟨747260, by rfl⟩ : syracuseStep 996347 = 1494521) B1494521
theorem B996407 : Blo 662308 996407 := bstep (se 1 (by rfl) ⟨747305, by rfl⟩ : syracuseStep 996407 = 1494611) B1494611
theorem B996527 : Blo 662308 996527 := bstep (se 1 (by rfl) ⟨747395, by rfl⟩ : syracuseStep 996527 = 1494791) B1494791
theorem B2241755 : Blo 662308 2241755 := bstep (se 1 (by rfl) ⟨1681316, by rfl⟩ : syracuseStep 2241755 = 3362633) B3362633
theorem B996935 : Blo 662308 996935 := bstep (se 1 (by rfl) ⟨747701, by rfl⟩ : syracuseStep 996935 = 1495403) B1495403
theorem B1685063 : Blo 662308 1685063 := bstep (se 1 (by rfl) ⟨1263797, by rfl⟩ : syracuseStep 1685063 = 2527595) B2527595
theorem B997031 : Blo 662308 997031 := bstep (se 1 (by rfl) ⟨747773, by rfl⟩ : syracuseStep 997031 = 1495547) B1495547
theorem B997115 : Blo 662308 997115 := bstep (se 1 (by rfl) ⟨747836, by rfl⟩ : syracuseStep 997115 = 1495673) B1495673
theorem B997151 : Blo 662308 997151 := bstep (se 1 (by rfl) ⟨747863, by rfl⟩ : syracuseStep 997151 = 1495727) B1495727
theorem B997199 : Blo 662308 997199 := bstep (se 1 (by rfl) ⟨747899, by rfl⟩ : syracuseStep 997199 = 1495799) B1495799
theorem B1259401 : Blo 662308 1259401 := bstep (se 2 (by rfl) ⟨472275, by rfl⟩ : syracuseStep 1259401 = 944551) B944551
theorem B997319 : Blo 662308 997319 := bstep (se 1 (by rfl) ⟨747989, by rfl⟩ : syracuseStep 997319 = 1495979) B1495979
theorem B2242619 : Blo 662308 2242619 := bstep (se 1 (by rfl) ⟨1681964, by rfl⟩ : syracuseStep 2242619 = 3363929) B3363929
theorem B997673 : Blo 662308 997673 := bstep (se 2 (by rfl) ⟨374127, by rfl⟩ : syracuseStep 997673 = 748255) B748255
theorem B997679 : Blo 662308 997679 := bstep (se 1 (by rfl) ⟨748259, by rfl⟩ : syracuseStep 997679 = 1496519) B1496519
theorem B2242889 : Blo 662308 2242889 := bstep (se 2 (by rfl) ⟨841083, by rfl⟩ : syracuseStep 2242889 = 1682167) B1682167
theorem B4864367 : Blo 662308 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B997919 : Blo 662308 997919 := bstep (se 1 (by rfl) ⟨748439, by rfl⟩ : syracuseStep 997919 = 1496879) B1496879
theorem B7584515 : Blo 662308 7584515 := bstep (se 1 (by rfl) ⟨5688386, by rfl⟩ : syracuseStep 7584515 = 11376773) B11376773
theorem B998303 : Blo 662308 998303 := bstep (se 1 (by rfl) ⟨748727, by rfl⟩ : syracuseStep 998303 = 1497455) B1497455
theorem B998351 : Blo 662308 998351 := bstep (se 1 (by rfl) ⟨748763, by rfl⟩ : syracuseStep 998351 = 1497527) B1497527
theorem B6831145 : Blo 662308 6831145 := bstep (se 2 (by rfl) ⟨2561679, by rfl⟩ : syracuseStep 6831145 = 5123359) B5123359
theorem B998441 : Blo 662308 998441 := bstep (se 2 (by rfl) ⟨374415, by rfl⟩ : syracuseStep 998441 = 748831) B748831
theorem B998447 : Blo 662308 998447 := bstep (se 1 (by rfl) ⟨748835, by rfl⟩ : syracuseStep 998447 = 1497671) B1497671
theorem B998471 : Blo 662308 998471 := bstep (se 1 (by rfl) ⟨748853, by rfl⟩ : syracuseStep 998471 = 1497707) B1497707
theorem B6143147 : Blo 662308 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B998735 : Blo 662308 998735 := bstep (se 1 (by rfl) ⟨749051, by rfl⟩ : syracuseStep 998735 = 1498103) B1498103
theorem B3784103 : Blo 662308 3784103 := bstep (se 1 (by rfl) ⟨2838077, by rfl⟩ : syracuseStep 3784103 = 5676155) B5676155
theorem B998825 : Blo 662308 998825 := bstep (se 2 (by rfl) ⟨374559, by rfl⟩ : syracuseStep 998825 = 749119) B749119
theorem B998975 : Blo 662308 998975 := bstep (se 1 (by rfl) ⟨749231, by rfl⟩ : syracuseStep 998975 = 1498463) B1498463
theorem B2244239 : Blo 662308 2244239 := bstep (se 1 (by rfl) ⟨1683179, by rfl⟩ : syracuseStep 2244239 = 3366359) B3366359
theorem B1490759 : Blo 662308 1490759 := bstep (se 1 (by rfl) ⟨1118069, by rfl⟩ : syracuseStep 1490759 = 2236139) B2236139
theorem B999239 : Blo 662308 999239 := bstep (se 1 (by rfl) ⟨749429, by rfl⟩ : syracuseStep 999239 = 1498859) B1498859
theorem B1195931 : Blo 662308 1195931 := bstep (se 1 (by rfl) ⟨896948, by rfl⟩ : syracuseStep 1195931 = 1793897) B1793897
theorem B999323 : Blo 662308 999323 := bstep (se 1 (by rfl) ⟨749492, by rfl⟩ : syracuseStep 999323 = 1498985) B1498985
theorem B1064927 : Blo 662308 1064927 := bstep (se 1 (by rfl) ⟨798695, by rfl⟩ : syracuseStep 1064927 = 1597391) B1597391
theorem B3228103 : Blo 662308 3228103 := bstep (se 1 (by rfl) ⟨2421077, by rfl⟩ : syracuseStep 3228103 = 4842155) B4842155
theorem B1491407 : Blo 662308 1491407 := bstep (se 1 (by rfl) ⟨1118555, by rfl⟩ : syracuseStep 1491407 = 2237111) B2237111
theorem B2245373 : Blo 662308 2245373 := bstep (se 3 (by rfl) ⟨421007, by rfl⟩ : syracuseStep 2245373 = 842015) B842015
theorem B1492073 : Blo 662308 1492073 := bstep (se 2 (by rfl) ⟨559527, by rfl⟩ : syracuseStep 1492073 = 1119055) B1119055
theorem B15353003 : Blo 662308 15353003 := bstep (se 1 (by rfl) ⟨11514752, by rfl⟩ : syracuseStep 15353003 = 23029505) B23029505
theorem B3786335 : Blo 662308 3786335 := bstep (se 1 (by rfl) ⟨2839751, by rfl⟩ : syracuseStep 3786335 = 5679503) B5679503
theorem B2836129 : Blo 662308 2836129 := bstep (se 2 (by rfl) ⟨1063548, by rfl⟩ : syracuseStep 2836129 = 2127097) B2127097
theorem B1492703 : Blo 662308 1492703 := bstep (se 1 (by rfl) ⟨1119527, by rfl⟩ : syracuseStep 1492703 = 2239055) B2239055
theorem B4802345 : Blo 662308 4802345 := bstep (se 2 (by rfl) ⟨1800879, by rfl⟩ : syracuseStep 4802345 = 3601759) B3601759
theorem B6473657 : Blo 662308 6473657 := bstep (se 2 (by rfl) ⟨2427621, by rfl⟩ : syracuseStep 6473657 = 4855243) B4855243
theorem B4802807 : Blo 662308 4802807 := bstep (se 1 (by rfl) ⟨3602105, by rfl⟩ : syracuseStep 4802807 = 7204211) B7204211
theorem B1263919 : Blo 662308 1263919 := bstep (se 1 (by rfl) ⟨947939, by rfl⟩ : syracuseStep 1263919 = 1895879) B1895879
theorem B1493531 : Blo 662308 1493531 := bstep (se 1 (by rfl) ⟨1120148, by rfl⟩ : syracuseStep 1493531 = 2240297) B2240297
theorem B3590687 : Blo 662308 3590687 := bstep (se 1 (by rfl) ⟨2693015, by rfl⟩ : syracuseStep 3590687 = 5386031) B5386031
theorem B3787337 : Blo 662308 3787337 := bstep (se 2 (by rfl) ⟨1420251, by rfl⟩ : syracuseStep 3787337 = 2840503) B2840503
theorem B2017963 : Blo 662308 2017963 := bstep (se 1 (by rfl) ⟨1513472, by rfl⟩ : syracuseStep 2017963 = 3026945) B3026945
theorem B2837207 : Blo 662308 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B16992989 : Blo 662308 16992989 := bstep (se 3 (by rfl) ⟨3186185, by rfl⟩ : syracuseStep 16992989 = 6372371) B6372371
theorem B2247479 : Blo 662308 2247479 := bstep (se 1 (by rfl) ⟨1685609, by rfl⟩ : syracuseStep 2247479 = 3371219) B3371219
theorem B1888019 : Blo 662308 1888019 := bstep (se 1 (by rfl) ⟨1416014, by rfl⟩ : syracuseStep 1888019 = 2832029) B2832029
theorem B1593209 : Blo 662308 1593209 := bstep (se 2 (by rfl) ⟨597453, by rfl⟩ : syracuseStep 1593209 = 1194907) B1194907
theorem B1495007 : Blo 662308 1495007 := bstep (se 1 (by rfl) ⟨1121255, by rfl⟩ : syracuseStep 1495007 = 2242511) B2242511
theorem B1495655 : Blo 662308 1495655 := bstep (se 1 (by rfl) ⟨1121741, by rfl⟩ : syracuseStep 1495655 = 2243483) B2243483
theorem B3363443 : Blo 662308 3363443 := bstep (se 1 (by rfl) ⟨2522582, by rfl⟩ : syracuseStep 3363443 = 5045165) B5045165
theorem B1790761 : Blo 662308 1790761 := bstep (se 2 (by rfl) ⟨671535, by rfl⟩ : syracuseStep 1790761 = 1343071) B1343071
theorem B17257475 : Blo 662308 17257475 := bstep (se 1 (by rfl) ⟨12943106, by rfl⟩ : syracuseStep 17257475 = 25886213) B25886213
theorem B4052177 : Blo 662308 4052177 := bstep (se 2 (by rfl) ⟨1519566, by rfl⟩ : syracuseStep 4052177 = 3039133) B3039133
theorem B3200219 : Blo 662308 3200219 := bstep (se 1 (by rfl) ⟨2400164, by rfl⟩ : syracuseStep 3200219 = 4800329) B4800329
theorem B1496339 : Blo 662308 1496339 := bstep (se 1 (by rfl) ⟨1122254, by rfl⟩ : syracuseStep 1496339 = 2244509) B2244509
theorem B1496411 : Blo 662308 1496411 := bstep (se 1 (by rfl) ⟨1122308, by rfl⟩ : syracuseStep 1496411 = 2244617) B2244617
theorem B25548533 : Blo 662308 25548533 := bstep (se 5 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 25548533 = 2395175) B2395175
theorem B1496969 : Blo 662308 1496969 := bstep (se 2 (by rfl) ⟨561363, by rfl⟩ : syracuseStep 1496969 = 1122727) B1122727
theorem B4249583 : Blo 662308 4249583 := bstep (se 1 (by rfl) ⟨3187187, by rfl⟩ : syracuseStep 4249583 = 6374375) B6374375
theorem B1890287 : Blo 662308 1890287 := bstep (se 1 (by rfl) ⟨1417715, by rfl⟩ : syracuseStep 1890287 = 2835431) B2835431
theorem B1497185 : Blo 662308 1497185 := bstep (se 2 (by rfl) ⟨561444, by rfl⟩ : syracuseStep 1497185 = 1122889) B1122889
theorem B1923227 : Blo 662308 1923227 := bstep (se 1 (by rfl) ⟨1442420, by rfl⟩ : syracuseStep 1923227 = 2884841) B2884841
theorem B18208961 : Blo 662308 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B1890503 : Blo 662308 1890503 := bstep (se 1 (by rfl) ⟨1417877, by rfl⟩ : syracuseStep 1890503 = 2835755) B2835755
theorem B3365063 : Blo 662308 3365063 := bstep (se 1 (by rfl) ⟨2523797, by rfl⟩ : syracuseStep 3365063 = 5047595) B5047595
theorem B3791333 : Blo 662308 3791333 := bstep (se 4 (by rfl) ⟨355437, by rfl⟩ : syracuseStep 3791333 = 710875) B710875
theorem B1891163 : Blo 662308 1891163 := bstep (se 1 (by rfl) ⟨1418372, by rfl⟩ : syracuseStep 1891163 = 2836745) B2836745
theorem B2841581 : Blo 662308 2841581 := bstep (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) B1065593
theorem B3366035 : Blo 662308 3366035 := bstep (se 1 (by rfl) ⟨2524526, by rfl⟩ : syracuseStep 3366035 = 5049053) B5049053
theorem B1891745 : Blo 662308 1891745 := bstep (se 2 (by rfl) ⟨709404, by rfl⟩ : syracuseStep 1891745 = 1418809) B1418809
theorem B1138087 : Blo 662308 1138087 := bstep (se 1 (by rfl) ⟨853565, by rfl⟩ : syracuseStep 1138087 = 1707131) B1707131
theorem B1498535 : Blo 662308 1498535 := bstep (se 1 (by rfl) ⟨1123901, by rfl⟩ : syracuseStep 1498535 = 2247803) B2247803
theorem B1498715 : Blo 662308 1498715 := bstep (se 1 (by rfl) ⟨1124036, by rfl⟩ : syracuseStep 1498715 = 2248073) B2248073
theorem B16375391 : Blo 662308 16375391 := bstep (se 1 (by rfl) ⟨12281543, by rfl⟩ : syracuseStep 16375391 = 24563087) B24563087
theorem B11099993 : Blo 662308 11099993 := bstep (se 2 (by rfl) ⟨4162497, by rfl⟩ : syracuseStep 11099993 = 8324995) B8324995
theorem B745339 : Blo 662308 745339 := bstep (se 1 (by rfl) ⟨559004, by rfl⟩ : syracuseStep 745339 = 1118009) B1118009
theorem B1499003 : Blo 662308 1499003 := bstep (se 1 (by rfl) ⟨1124252, by rfl⟩ : syracuseStep 1499003 = 2248505) B2248505
theorem B1793917 : Blo 662308 1793917 := bstep (se 3 (by rfl) ⟨336359, by rfl⟩ : syracuseStep 1793917 = 672719) B672719
theorem B3366845 : Blo 662308 3366845 := bstep (se 3 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 3366845 = 1262567) B1262567
theorem B8642713 : Blo 662308 8642713 := bstep (se 2 (by rfl) ⟨3241017, by rfl⟩ : syracuseStep 8642713 = 6482035) B6482035
theorem B17228161 : Blo 662308 17228161 := bstep (se 2 (by rfl) ⟨6460560, by rfl⟩ : syracuseStep 17228161 = 12921121) B12921121
theorem B9593275 : Blo 662308 9593275 := bstep (se 1 (by rfl) ⟨7194956, by rfl⟩ : syracuseStep 9593275 = 14389913) B14389913
theorem B10773101 : Blo 662308 10773101 := bstep (se 3 (by rfl) ⟨2019956, by rfl⟩ : syracuseStep 10773101 = 4039913) B4039913
theorem B5661323 : Blo 662308 5661323 := bstep (se 1 (by rfl) ⟨4245992, by rfl⟩ : syracuseStep 5661323 = 8491985) B8491985
theorem B746491 : Blo 662308 746491 := bstep (se 1 (by rfl) ⟨559868, by rfl⟩ : syracuseStep 746491 = 1119737) B1119737
theorem B746671 : Blo 662308 746671 := bstep (se 1 (by rfl) ⟨560003, by rfl⟩ : syracuseStep 746671 = 1120007) B1120007
theorem B3237497 : Blo 662308 3237497 := bstep (se 2 (by rfl) ⟨1214061, by rfl⟩ : syracuseStep 3237497 = 2428123) B2428123
theorem B747175 : Blo 662308 747175 := bstep (se 1 (by rfl) ⟨560381, by rfl⟩ : syracuseStep 747175 = 1120763) B1120763
theorem B4384543 : Blo 662308 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B747463 : Blo 662308 747463 := bstep (se 1 (by rfl) ⟨560597, by rfl⟩ : syracuseStep 747463 = 1121195) B1121195
theorem B3368951 : Blo 662308 3368951 := bstep (se 1 (by rfl) ⟨2526713, by rfl⟩ : syracuseStep 3368951 = 5053427) B5053427
theorem B2517101 : Blo 662308 2517101 := bstep (se 3 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 2517101 = 943913) B943913
theorem B3467411 : Blo 662308 3467411 := bstep (se 1 (by rfl) ⟨2600558, by rfl⟩ : syracuseStep 3467411 = 5201117) B5201117
theorem B3369113 : Blo 662308 3369113 := bstep (se 2 (by rfl) ⟨1263417, by rfl⟩ : syracuseStep 3369113 = 2526835) B2526835
theorem B747823 : Blo 662308 747823 := bstep (se 1 (by rfl) ⟨560867, by rfl⟩ : syracuseStep 747823 = 1121735) B1121735
theorem B5663033 : Blo 662308 5663033 := bstep (se 2 (by rfl) ⟨2123637, by rfl⟩ : syracuseStep 5663033 = 4247275) B4247275
theorem B3369923 : Blo 662308 3369923 := bstep (se 1 (by rfl) ⟨2527442, by rfl⟩ : syracuseStep 3369923 = 5054885) B5054885
theorem B945103 : Blo 662308 945103 := bstep (se 1 (by rfl) ⟨708827, by rfl⟩ : syracuseStep 945103 = 1417655) B1417655
theorem B748615 : Blo 662308 748615 := bstep (se 1 (by rfl) ⟨561461, by rfl⟩ : syracuseStep 748615 = 1122923) B1122923
theorem B1895993 : Blo 662308 1895993 := bstep (se 2 (by rfl) ⟨710997, by rfl⟩ : syracuseStep 1895993 = 1421995) B1421995
theorem B1896061 : Blo 662308 1896061 := bstep (se 3 (by rfl) ⟨355511, by rfl⟩ : syracuseStep 1896061 = 711023) B711023
theorem B1076969 : Blo 662308 1076969 := bstep (se 2 (by rfl) ⟨403863, by rfl⟩ : syracuseStep 1076969 = 807727) B807727
theorem B1896335 : Blo 662308 1896335 := bstep (se 1 (by rfl) ⟨1422251, by rfl⟩ : syracuseStep 1896335 = 2844503) B2844503
theorem B6811771 : Blo 662308 6811771 := bstep (se 1 (by rfl) ⟨5108828, by rfl⟩ : syracuseStep 6811771 = 10217657) B10217657
theorem B2519363 : Blo 662308 2519363 := bstep (se 1 (by rfl) ⟨1889522, by rfl⟩ : syracuseStep 2519363 = 3779045) B3779045
theorem B1700233 : Blo 662308 1700233 := bstep (se 2 (by rfl) ⟨637587, by rfl⟩ : syracuseStep 1700233 = 1275175) B1275175
theorem B2519545 : Blo 662308 2519545 := bstep (se 2 (by rfl) ⟨944829, by rfl⟩ : syracuseStep 2519545 = 1889659) B1889659
theorem B1897121 : Blo 662308 1897121 := bstep (se 2 (by rfl) ⟨711420, by rfl⟩ : syracuseStep 1897121 = 1422841) B1422841
theorem B5665697 : Blo 662308 5665697 := bstep (se 2 (by rfl) ⟨2124636, by rfl⟩ : syracuseStep 5665697 = 4249273) B4249273
theorem B2127329 : Blo 662308 2127329 := bstep (se 2 (by rfl) ⟨797748, by rfl⟩ : syracuseStep 2127329 = 1595497) B1595497
theorem B3405725 : Blo 662308 3405725 := bstep (se 3 (by rfl) ⟨638573, by rfl⟩ : syracuseStep 3405725 = 1277147) B1277147
theorem B2520989 : Blo 662308 2520989 := bstep (se 3 (by rfl) ⟨472685, by rfl⟩ : syracuseStep 2520989 = 945371) B945371
theorem B1702043 : Blo 662308 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B43645105 : Blo 662308 43645105 := bstep (se 2 (by rfl) ⟨16366914, by rfl⟩ : syracuseStep 43645105 = 32733829) B32733829
theorem B4782509 : Blo 662308 4782509 := bstep (se 3 (by rfl) ⟨896720, by rfl⟩ : syracuseStep 4782509 = 1793441) B1793441
theorem B5667407 : Blo 662308 5667407 := bstep (se 1 (by rfl) ⟨4250555, by rfl⟩ : syracuseStep 5667407 = 8501111) B8501111
theorem B4783175 : Blo 662308 4783175 := bstep (se 1 (by rfl) ⟨3587381, by rfl⟩ : syracuseStep 4783175 = 7174763) B7174763
theorem B2129789 : Blo 662308 2129789 := bstep (se 3 (by rfl) ⟨399335, by rfl⟩ : syracuseStep 2129789 = 798671) B798671
theorem B2162875 : Blo 662308 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B22970881 : Blo 662308 22970881 := bstep (se 2 (by rfl) ⟨8614080, by rfl⟩ : syracuseStep 22970881 = 17228161) B17228161
theorem B2524223 : Blo 662308 2524223 := bstep (se 1 (by rfl) ⟨1893167, by rfl⟩ : syracuseStep 2524223 = 3786335) B3786335
theorem B2524891 : Blo 662308 2524891 := bstep (se 1 (by rfl) ⟨1893668, by rfl⟩ : syracuseStep 2524891 = 3787337) B3787337
theorem B19466795 : Blo 662308 19466795 := bstep (se 1 (by rfl) ⟨14600096, by rfl⟩ : syracuseStep 19466795 = 29200193) B29200193
theorem B5376563 : Blo 662308 5376563 := bstep (se 1 (by rfl) ⟨4032422, by rfl⟩ : syracuseStep 5376563 = 8064845) B8064845
theorem B12782879 : Blo 662308 12782879 := bstep (se 1 (by rfl) ⟨9587159, by rfl⟩ : syracuseStep 12782879 = 19174319) B19174319
theorem B2133479 : Blo 662308 2133479 := bstep (se 1 (by rfl) ⟨1600109, by rfl⟩ : syracuseStep 2133479 = 3200219) B3200219
theorem B6393593 : Blo 662308 6393593 := bstep (se 2 (by rfl) ⟨2397597, by rfl⟩ : syracuseStep 6393593 = 4795195) B4795195
theorem B2428795 : Blo 662308 2428795 := bstep (se 1 (by rfl) ⟨1821596, by rfl⟩ : syracuseStep 2428795 = 3643193) B3643193
theorem B1118191 : Blo 662308 1118191 := bstep (se 1 (by rfl) ⟨838643, by rfl⟩ : syracuseStep 1118191 = 1677287) B1677287
theorem B1282151 : Blo 662308 1282151 := bstep (se 1 (by rfl) ⟨961613, by rfl⟩ : syracuseStep 1282151 = 1923227) B1923227
theorem B2528081 : Blo 662308 2528081 := bstep (se 2 (by rfl) ⟨948030, by rfl⟩ : syracuseStep 2528081 = 1896061) B1896061
theorem B3773465 : Blo 662308 3773465 := bstep (se 2 (by rfl) ⟨1415049, by rfl⟩ : syracuseStep 3773465 = 2830099) B2830099
theorem B10916927 : Blo 662308 10916927 := bstep (se 1 (by rfl) ⟨8187695, by rfl⟩ : syracuseStep 10916927 = 16375391) B16375391
theorem B9082361 : Blo 662308 9082361 := bstep (se 2 (by rfl) ⟨3405885, by rfl⟩ : syracuseStep 9082361 = 6811771) B6811771
theorem B1119899 : Blo 662308 1119899 := bstep (se 1 (by rfl) ⟨839924, by rfl⟩ : syracuseStep 1119899 = 1679849) B1679849
theorem B7182067 : Blo 662308 7182067 := bstep (se 1 (by rfl) ⟨5386550, by rfl⟩ : syracuseStep 7182067 = 10773101) B10773101
theorem B3774215 : Blo 662308 3774215 := bstep (se 1 (by rfl) ⟨2830661, by rfl⟩ : syracuseStep 3774215 = 5661323) B5661323
theorem B1513511 : Blo 662308 1513511 := bstep (se 1 (by rfl) ⟨1135133, by rfl⟩ : syracuseStep 1513511 = 2270267) B2270267
theorem B2562173 : Blo 662308 2562173 := bstep (se 3 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 2562173 = 960815) B960815
theorem B1677449 : Blo 662308 1677449 := bstep (se 2 (by rfl) ⟨629043, by rfl⟩ : syracuseStep 1677449 = 1258087) B1258087
theorem B4855945 : Blo 662308 4855945 := bstep (se 2 (by rfl) ⟨1820979, by rfl⟩ : syracuseStep 4855945 = 3641959) B3641959
theorem B1678067 : Blo 662308 1678067 := bstep (se 1 (by rfl) ⟨1258550, by rfl⟩ : syracuseStep 1678067 = 2517101) B2517101
theorem B9575165 : Blo 662308 9575165 := bstep (se 3 (by rfl) ⟨1795343, by rfl⟩ : syracuseStep 9575165 = 3590687) B3590687
theorem B662343 : Blo 662308 662343 := bstep (se 1 (by rfl) ⟨496757, by rfl⟩ : syracuseStep 662343 = 993515) B993515
theorem B662383 : Blo 662308 662383 := bstep (se 1 (by rfl) ⟨496787, by rfl⟩ : syracuseStep 662383 = 993575) B993575
theorem B3775355 : Blo 662308 3775355 := bstep (se 1 (by rfl) ⟨2831516, by rfl⟩ : syracuseStep 3775355 = 5663033) B5663033
theorem B662439 : Blo 662308 662439 := bstep (se 1 (by rfl) ⟨496829, by rfl⟩ : syracuseStep 662439 = 993659) B993659
theorem B662619 : Blo 662308 662619 := bstep (se 1 (by rfl) ⟨496964, by rfl⟩ : syracuseStep 662619 = 993929) B993929
theorem B2235599 : Blo 662308 2235599 := bstep (se 1 (by rfl) ⟨1676699, by rfl⟩ : syracuseStep 2235599 = 3353399) B3353399
theorem B662735 : Blo 662308 662735 := bstep (se 1 (by rfl) ⟨497051, by rfl⟩ : syracuseStep 662735 = 994103) B994103
theorem B662759 : Blo 662308 662759 := bstep (se 1 (by rfl) ⟨497069, by rfl⟩ : syracuseStep 662759 = 994139) B994139
theorem B662855 : Blo 662308 662855 := bstep (se 1 (by rfl) ⟨497141, by rfl⟩ : syracuseStep 662855 = 994283) B994283
theorem B662991 : Blo 662308 662991 := bstep (se 1 (by rfl) ⟨497243, by rfl⟩ : syracuseStep 662991 = 994487) B994487
theorem B2235977 : Blo 662308 2235977 := bstep (se 2 (by rfl) ⟨838491, by rfl⟩ : syracuseStep 2235977 = 1676983) B1676983
theorem B663151 : Blo 662308 663151 := bstep (se 1 (by rfl) ⟨497363, by rfl⟩ : syracuseStep 663151 = 994727) B994727
theorem B663207 : Blo 662308 663207 := bstep (se 1 (by rfl) ⟨497405, by rfl⟩ : syracuseStep 663207 = 994811) B994811
theorem B663271 : Blo 662308 663271 := bstep (se 1 (by rfl) ⟨497453, by rfl⟩ : syracuseStep 663271 = 994907) B994907
theorem B663327 : Blo 662308 663327 := bstep (se 1 (by rfl) ⟨497495, by rfl⟩ : syracuseStep 663327 = 994991) B994991
theorem B1122079 : Blo 662308 1122079 := bstep (se 1 (by rfl) ⟨841559, by rfl⟩ : syracuseStep 1122079 = 1683119) B1683119
theorem B1679201 : Blo 662308 1679201 := bstep (se 2 (by rfl) ⟨629700, by rfl⟩ : syracuseStep 1679201 = 1259401) B1259401
theorem B663407 : Blo 662308 663407 := bstep (se 1 (by rfl) ⟨497555, by rfl⟩ : syracuseStep 663407 = 995111) B995111
theorem B3776381 : Blo 662308 3776381 := bstep (se 3 (by rfl) ⟨708071, by rfl⟩ : syracuseStep 3776381 = 1416143) B1416143
theorem B663463 : Blo 662308 663463 := bstep (se 1 (by rfl) ⟨497597, by rfl⟩ : syracuseStep 663463 = 995195) B995195
theorem B1122295 : Blo 662308 1122295 := bstep (se 1 (by rfl) ⟨841721, by rfl⟩ : syracuseStep 1122295 = 1683443) B1683443
theorem B663743 : Blo 662308 663743 := bstep (se 1 (by rfl) ⟨497807, by rfl⟩ : syracuseStep 663743 = 995615) B995615
theorem B663759 : Blo 662308 663759 := bstep (se 1 (by rfl) ⟨497819, by rfl⟩ : syracuseStep 663759 = 995639) B995639
theorem B1122511 : Blo 662308 1122511 := bstep (se 1 (by rfl) ⟨841883, by rfl⟩ : syracuseStep 1122511 = 1683767) B1683767
theorem B1679575 : Blo 662308 1679575 := bstep (se 1 (by rfl) ⟨1259681, by rfl⟩ : syracuseStep 1679575 = 2519363) B2519363
theorem B663807 : Blo 662308 663807 := bstep (se 1 (by rfl) ⟨497855, by rfl⟩ : syracuseStep 663807 = 995711) B995711
theorem B663855 : Blo 662308 663855 := bstep (se 1 (by rfl) ⟨497891, by rfl⟩ : syracuseStep 663855 = 995783) B995783
theorem B664091 : Blo 662308 664091 := bstep (se 1 (by rfl) ⟨498068, by rfl⟩ : syracuseStep 664091 = 996137) B996137
theorem B664095 : Blo 662308 664095 := bstep (se 1 (by rfl) ⟨498071, by rfl⟩ : syracuseStep 664095 = 996143) B996143
theorem B3777131 : Blo 662308 3777131 := bstep (se 1 (by rfl) ⟨2832848, by rfl⟩ : syracuseStep 3777131 = 5665697) B5665697
theorem B664175 : Blo 662308 664175 := bstep (se 1 (by rfl) ⟨498131, by rfl⟩ : syracuseStep 664175 = 996263) B996263
theorem B664231 : Blo 662308 664231 := bstep (se 1 (by rfl) ⟨498173, by rfl⟩ : syracuseStep 664231 = 996347) B996347
theorem B664271 : Blo 662308 664271 := bstep (se 1 (by rfl) ⟨498203, by rfl⟩ : syracuseStep 664271 = 996407) B996407
theorem B664351 : Blo 662308 664351 := bstep (se 1 (by rfl) ⟨498263, by rfl⟩ : syracuseStep 664351 = 996527) B996527
theorem B1418219 : Blo 662308 1418219 := bstep (se 1 (by rfl) ⟨1063664, by rfl⟩ : syracuseStep 1418219 = 2127329) B2127329
theorem B664623 : Blo 662308 664623 := bstep (se 1 (by rfl) ⟨498467, by rfl⟩ : syracuseStep 664623 = 996935) B996935
theorem B1123375 : Blo 662308 1123375 := bstep (se 1 (by rfl) ⟨842531, by rfl⟩ : syracuseStep 1123375 = 1685063) B1685063
theorem B664687 : Blo 662308 664687 := bstep (se 1 (by rfl) ⟨498515, by rfl⟩ : syracuseStep 664687 = 997031) B997031
theorem B664743 : Blo 662308 664743 := bstep (se 1 (by rfl) ⟨498557, by rfl⟩ : syracuseStep 664743 = 997115) B997115
theorem B664767 : Blo 662308 664767 := bstep (se 1 (by rfl) ⟨498575, by rfl⟩ : syracuseStep 664767 = 997151) B997151
theorem B664799 : Blo 662308 664799 := bstep (se 1 (by rfl) ⟨498599, by rfl⟩ : syracuseStep 664799 = 997199) B997199
theorem B2270483 : Blo 662308 2270483 := bstep (se 1 (by rfl) ⟨1702862, by rfl⟩ : syracuseStep 2270483 = 3405725) B3405725
theorem B1680659 : Blo 662308 1680659 := bstep (se 1 (by rfl) ⟨1260494, by rfl⟩ : syracuseStep 1680659 = 2520989) B2520989
theorem B664879 : Blo 662308 664879 := bstep (se 1 (by rfl) ⟨498659, by rfl⟩ : syracuseStep 664879 = 997319) B997319
theorem B665115 : Blo 662308 665115 := bstep (se 1 (by rfl) ⟨498836, by rfl⟩ : syracuseStep 665115 = 997673) B997673
theorem B665119 : Blo 662308 665119 := bstep (se 1 (by rfl) ⟨498839, by rfl⟩ : syracuseStep 665119 = 997679) B997679
theorem B3188339 : Blo 662308 3188339 := bstep (se 1 (by rfl) ⟨2391254, by rfl⟩ : syracuseStep 3188339 = 4782509) B4782509
theorem B665279 : Blo 662308 665279 := bstep (se 1 (by rfl) ⟨498959, by rfl⟩ : syracuseStep 665279 = 997919) B997919
theorem B3778271 : Blo 662308 3778271 := bstep (se 1 (by rfl) ⟨2833703, by rfl⟩ : syracuseStep 3778271 = 5667407) B5667407
theorem B5056343 : Blo 662308 5056343 := bstep (se 1 (by rfl) ⟨3792257, by rfl⟩ : syracuseStep 5056343 = 7584515) B7584515
theorem B1517449 : Blo 662308 1517449 := bstep (se 2 (by rfl) ⟨569043, by rfl⟩ : syracuseStep 1517449 = 1138087) B1138087
theorem B665535 : Blo 662308 665535 := bstep (se 1 (by rfl) ⟨499151, by rfl⟩ : syracuseStep 665535 = 998303) B998303
theorem B665567 : Blo 662308 665567 := bstep (se 1 (by rfl) ⟨499175, by rfl⟩ : syracuseStep 665567 = 998351) B998351
theorem B665627 : Blo 662308 665627 := bstep (se 1 (by rfl) ⟨499220, by rfl⟩ : syracuseStep 665627 = 998441) B998441
theorem B665631 : Blo 662308 665631 := bstep (se 1 (by rfl) ⟨499223, by rfl⟩ : syracuseStep 665631 = 998447) B998447
theorem B3188783 : Blo 662308 3188783 := bstep (se 1 (by rfl) ⟨2391587, by rfl⟩ : syracuseStep 3188783 = 4783175) B4783175
theorem B665647 : Blo 662308 665647 := bstep (se 1 (by rfl) ⟨499235, by rfl⟩ : syracuseStep 665647 = 998471) B998471
theorem B2238569 : Blo 662308 2238569 := bstep (se 2 (by rfl) ⟨839463, by rfl⟩ : syracuseStep 2238569 = 1678927) B1678927
theorem B665823 : Blo 662308 665823 := bstep (se 1 (by rfl) ⟨499367, by rfl⟩ : syracuseStep 665823 = 998735) B998735
theorem B29599981 : Blo 662308 29599981 := bstep (se 3 (by rfl) ⟨5549996, by rfl⟩ : syracuseStep 29599981 = 11099993) B11099993
theorem B665883 : Blo 662308 665883 := bstep (se 1 (by rfl) ⟨499412, by rfl⟩ : syracuseStep 665883 = 998825) B998825
theorem B665983 : Blo 662308 665983 := bstep (se 1 (by rfl) ⟨499487, by rfl⟩ : syracuseStep 665983 = 998975) B998975
theorem B993785 : Blo 662308 993785 := bstep (se 2 (by rfl) ⟨372669, by rfl⟩ : syracuseStep 993785 = 745339) B745339
theorem B993839 : Blo 662308 993839 := bstep (se 1 (by rfl) ⟨745379, by rfl⟩ : syracuseStep 993839 = 1490759) B1490759
theorem B666159 : Blo 662308 666159 := bstep (se 1 (by rfl) ⟨499619, by rfl⟩ : syracuseStep 666159 = 999239) B999239
theorem B1419859 : Blo 662308 1419859 := bstep (se 1 (by rfl) ⟨1064894, by rfl⟩ : syracuseStep 1419859 = 2129789) B2129789
theorem B797287 : Blo 662308 797287 := bstep (se 1 (by rfl) ⟨597965, by rfl⟩ : syracuseStep 797287 = 1195931) B1195931
theorem B666215 : Blo 662308 666215 := bstep (se 1 (by rfl) ⟨499661, by rfl⟩ : syracuseStep 666215 = 999323) B999323
theorem B994271 : Blo 662308 994271 := bstep (se 1 (by rfl) ⟨745703, by rfl⟩ : syracuseStep 994271 = 1491407) B1491407
theorem B12791033 : Blo 662308 12791033 := bstep (se 2 (by rfl) ⟨4796637, by rfl⟩ : syracuseStep 12791033 = 9593275) B9593275
theorem B4304137 : Blo 662308 4304137 := bstep (se 2 (by rfl) ⟨1614051, by rfl⟩ : syracuseStep 4304137 = 3228103) B3228103
theorem B994715 : Blo 662308 994715 := bstep (se 1 (by rfl) ⟨746036, by rfl⟩ : syracuseStep 994715 = 1492073) B1492073
theorem B10235335 : Blo 662308 10235335 := bstep (se 1 (by rfl) ⟨7676501, by rfl⟩ : syracuseStep 10235335 = 15353003) B15353003
theorem B2272769 : Blo 662308 2272769 := bstep (se 2 (by rfl) ⟨852288, by rfl⟩ : syracuseStep 2272769 = 1704577) B1704577
theorem B995135 : Blo 662308 995135 := bstep (se 1 (by rfl) ⟨746351, by rfl⟩ : syracuseStep 995135 = 1492703) B1492703
theorem B995321 : Blo 662308 995321 := bstep (se 2 (by rfl) ⟨373245, by rfl⟩ : syracuseStep 995321 = 746491) B746491
theorem B1421543 : Blo 662308 1421543 := bstep (se 1 (by rfl) ⟨1066157, by rfl⟩ : syracuseStep 1421543 = 2132315) B2132315
theorem B995561 : Blo 662308 995561 := bstep (se 2 (by rfl) ⟨373335, by rfl⟩ : syracuseStep 995561 = 746671) B746671
theorem B995687 : Blo 662308 995687 := bstep (se 1 (by rfl) ⟨746765, by rfl⟩ : syracuseStep 995687 = 1493531) B1493531
theorem B3781505 : Blo 662308 3781505 := bstep (se 2 (by rfl) ⟨1418064, by rfl⟩ : syracuseStep 3781505 = 2836129) B2836129
theorem B996233 : Blo 662308 996233 := bstep (se 2 (by rfl) ⟨373587, by rfl⟩ : syracuseStep 996233 = 747175) B747175
theorem B1684435 : Blo 662308 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B5846057 : Blo 662308 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B3781687 : Blo 662308 3781687 := bstep (se 1 (by rfl) ⟨2836265, by rfl⟩ : syracuseStep 3781687 = 5672531) B5672531
theorem B1258679 : Blo 662308 1258679 := bstep (se 1 (by rfl) ⟨944009, by rfl⟩ : syracuseStep 1258679 = 1888019) B1888019
theorem B996617 : Blo 662308 996617 := bstep (se 2 (by rfl) ⟨373731, by rfl⟩ : syracuseStep 996617 = 747463) B747463
theorem B996671 : Blo 662308 996671 := bstep (se 1 (by rfl) ⟨747503, by rfl⟩ : syracuseStep 996671 = 1495007) B1495007
theorem B46019933 : Blo 662308 46019933 := bstep (se 3 (by rfl) ⟨8628737, by rfl⟩ : syracuseStep 46019933 = 17257475) B17257475
theorem B997097 : Blo 662308 997097 := bstep (se 2 (by rfl) ⟨373911, by rfl⟩ : syracuseStep 997097 = 747823) B747823
theorem B1685225 : Blo 662308 1685225 := bstep (se 2 (by rfl) ⟨631959, by rfl⟩ : syracuseStep 1685225 = 1263919) B1263919
theorem B997103 : Blo 662308 997103 := bstep (se 1 (by rfl) ⟨747827, by rfl⟩ : syracuseStep 997103 = 1495655) B1495655
theorem B2242295 : Blo 662308 2242295 := bstep (se 1 (by rfl) ⟨1681721, by rfl⟩ : syracuseStep 2242295 = 3363443) B3363443
theorem B2701451 : Blo 662308 2701451 := bstep (se 1 (by rfl) ⟨2026088, by rfl⟩ : syracuseStep 2701451 = 4052177) B4052177
theorem B997559 : Blo 662308 997559 := bstep (se 1 (by rfl) ⟨748169, by rfl⟩ : syracuseStep 997559 = 1496339) B1496339
theorem B10762469 : Blo 662308 10762469 := bstep (se 4 (by rfl) ⟨1008981, by rfl⟩ : syracuseStep 10762469 = 2017963) B2017963
theorem B997607 : Blo 662308 997607 := bstep (se 1 (by rfl) ⟨748205, by rfl⟩ : syracuseStep 997607 = 1496411) B1496411
theorem B17217773 : Blo 662308 17217773 := bstep (se 3 (by rfl) ⟨3228332, by rfl⟩ : syracuseStep 17217773 = 6456665) B6456665
theorem B5388889 : Blo 662308 5388889 := bstep (se 2 (by rfl) ⟨2020833, by rfl⟩ : syracuseStep 5388889 = 4041667) B4041667
theorem B997979 : Blo 662308 997979 := bstep (se 1 (by rfl) ⟨748484, by rfl⟩ : syracuseStep 997979 = 1496969) B1496969
theorem B1260137 : Blo 662308 1260137 := bstep (se 2 (by rfl) ⟨472551, by rfl⟩ : syracuseStep 1260137 = 945103) B945103
theorem B2833055 : Blo 662308 2833055 := bstep (se 1 (by rfl) ⟨2124791, by rfl⟩ : syracuseStep 2833055 = 4249583) B4249583
theorem B1260191 : Blo 662308 1260191 := bstep (se 1 (by rfl) ⟨945143, by rfl⟩ : syracuseStep 1260191 = 1890287) B1890287
theorem B998123 : Blo 662308 998123 := bstep (se 1 (by rfl) ⟨748592, by rfl⟩ : syracuseStep 998123 = 1497185) B1497185
theorem B998153 : Blo 662308 998153 := bstep (se 2 (by rfl) ⟨374307, by rfl⟩ : syracuseStep 998153 = 748615) B748615
theorem B12139307 : Blo 662308 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B1260335 : Blo 662308 1260335 := bstep (se 1 (by rfl) ⟨945251, by rfl⟩ : syracuseStep 1260335 = 1890503) B1890503
theorem B2243375 : Blo 662308 2243375 := bstep (se 1 (by rfl) ⟨1682531, by rfl⟩ : syracuseStep 2243375 = 3365063) B3365063
theorem B1260775 : Blo 662308 1260775 := bstep (se 1 (by rfl) ⟨945581, by rfl⟩ : syracuseStep 1260775 = 1891163) B1891163
theorem B1490255 : Blo 662308 1490255 := bstep (se 1 (by rfl) ⟨1117691, by rfl⟩ : syracuseStep 1490255 = 2235383) B2235383
theorem B1490345 : Blo 662308 1490345 := bstep (se 2 (by rfl) ⟨558879, by rfl⟩ : syracuseStep 1490345 = 1117759) B1117759
theorem B2244023 : Blo 662308 2244023 := bstep (se 1 (by rfl) ⟨1683017, by rfl⟩ : syracuseStep 2244023 = 3366035) B3366035
theorem B1261163 : Blo 662308 1261163 := bstep (se 1 (by rfl) ⟨945872, by rfl⟩ : syracuseStep 1261163 = 1891745) B1891745
theorem B1490543 : Blo 662308 1490543 := bstep (se 1 (by rfl) ⟨1117907, by rfl⟩ : syracuseStep 1490543 = 2235815) B2235815
theorem B999023 : Blo 662308 999023 := bstep (se 1 (by rfl) ⟨749267, by rfl⟩ : syracuseStep 999023 = 1498535) B1498535
theorem B999143 : Blo 662308 999143 := bstep (se 1 (by rfl) ⟨749357, by rfl⟩ : syracuseStep 999143 = 1498715) B1498715
theorem B2735927 : Blo 662308 2735927 := bstep (se 1 (by rfl) ⟨2051945, by rfl⟩ : syracuseStep 2735927 = 4103891) B4103891
theorem B1490831 : Blo 662308 1490831 := bstep (se 1 (by rfl) ⟨1118123, by rfl⟩ : syracuseStep 1490831 = 2236247) B2236247
theorem B999335 : Blo 662308 999335 := bstep (se 1 (by rfl) ⟨749501, by rfl⟩ : syracuseStep 999335 = 1499003) B1499003
theorem B2244563 : Blo 662308 2244563 := bstep (se 1 (by rfl) ⟨1683422, by rfl⟩ : syracuseStep 2244563 = 3366845) B3366845
theorem B1491371 : Blo 662308 1491371 := bstep (se 1 (by rfl) ⟨1118528, by rfl⟩ : syracuseStep 1491371 = 2237057) B2237057
theorem B1491551 : Blo 662308 1491551 := bstep (se 1 (by rfl) ⟨1118663, by rfl⟩ : syracuseStep 1491551 = 2237327) B2237327
theorem B3359393 : Blo 662308 3359393 := bstep (se 2 (by rfl) ⟨1259772, by rfl⟩ : syracuseStep 3359393 = 2519545) B2519545
theorem B1491911 : Blo 662308 1491911 := bstep (se 1 (by rfl) ⟨1118933, by rfl⟩ : syracuseStep 1491911 = 2237867) B2237867
theorem B3196027 : Blo 662308 3196027 := bstep (se 1 (by rfl) ⟨2397020, by rfl⟩ : syracuseStep 3196027 = 4794041) B4794041
theorem B10110221 : Blo 662308 10110221 := bstep (se 3 (by rfl) ⟨1895666, by rfl⟩ : syracuseStep 10110221 = 3791333) B3791333
theorem B1492271 : Blo 662308 1492271 := bstep (se 1 (by rfl) ⟨1119203, by rfl⟩ : syracuseStep 1492271 = 2238407) B2238407
theorem B2245967 : Blo 662308 2245967 := bstep (se 1 (by rfl) ⟨1684475, by rfl⟩ : syracuseStep 2245967 = 3368951) B3368951
theorem B2311607 : Blo 662308 2311607 := bstep (se 1 (by rfl) ⟨1733705, by rfl⟩ : syracuseStep 2311607 = 3467411) B3467411
theorem B2246075 : Blo 662308 2246075 := bstep (se 1 (by rfl) ⟨1684556, by rfl⟩ : syracuseStep 2246075 = 3369113) B3369113
theorem B1492775 : Blo 662308 1492775 := bstep (se 1 (by rfl) ⟨1119581, by rfl⟩ : syracuseStep 1492775 = 2239163) B2239163
theorem B2246615 : Blo 662308 2246615 := bstep (se 1 (by rfl) ⟨1684961, by rfl⟩ : syracuseStep 2246615 = 3369923) B3369923
theorem B1493153 : Blo 662308 1493153 := bstep (se 2 (by rfl) ⟨559932, by rfl⟩ : syracuseStep 1493153 = 1119865) B1119865
theorem B1263995 : Blo 662308 1263995 := bstep (se 1 (by rfl) ⟨947996, by rfl⟩ : syracuseStep 1263995 = 1895993) B1895993
theorem B1264223 : Blo 662308 1264223 := bstep (se 1 (by rfl) ⟨948167, by rfl⟩ : syracuseStep 1264223 = 1896335) B1896335
theorem B1493801 : Blo 662308 1493801 := bstep (se 2 (by rfl) ⟨560175, by rfl⟩ : syracuseStep 1493801 = 1120351) B1120351
theorem B1887097 : Blo 662308 1887097 := bstep (se 2 (by rfl) ⟨707661, by rfl⟩ : syracuseStep 1887097 = 1415323) B1415323
theorem B5688251 : Blo 662308 5688251 := bstep (se 1 (by rfl) ⟨4266188, by rfl⟩ : syracuseStep 5688251 = 8532377) B8532377
theorem B5033015 : Blo 662308 5033015 := bstep (se 1 (by rfl) ⟨3774761, by rfl⟩ : syracuseStep 5033015 = 7549523) B7549523
theorem B1494071 : Blo 662308 1494071 := bstep (se 1 (by rfl) ⟨1120553, by rfl⟩ : syracuseStep 1494071 = 2241107) B2241107
theorem B1264747 : Blo 662308 1264747 := bstep (se 1 (by rfl) ⟨948560, by rfl⟩ : syracuseStep 1264747 = 1897121) B1897121
theorem B838831 : Blo 662308 838831 := bstep (se 1 (by rfl) ⟨629123, by rfl⟩ : syracuseStep 838831 = 1258247) B1258247
theorem B1494503 : Blo 662308 1494503 := bstep (se 1 (by rfl) ⟨1120877, by rfl⟩ : syracuseStep 1494503 = 2241755) B2241755
theorem B4050917 : Blo 662308 4050917 := bstep (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) B759547
theorem B1495079 : Blo 662308 1495079 := bstep (se 1 (by rfl) ⟨1121309, by rfl⟩ : syracuseStep 1495079 = 2242619) B2242619
theorem B1134695 : Blo 662308 1134695 := bstep (se 1 (by rfl) ⟨851021, by rfl⟩ : syracuseStep 1134695 = 1702043) B1702043
theorem B1495259 : Blo 662308 1495259 := bstep (se 1 (by rfl) ⟨1121444, by rfl⟩ : syracuseStep 1495259 = 2242889) B2242889
theorem B5034473 : Blo 662308 5034473 := bstep (se 2 (by rfl) ⟨1887927, by rfl⟩ : syracuseStep 5034473 = 3775855) B3775855
theorem B1495529 : Blo 662308 1495529 := bstep (se 2 (by rfl) ⟨560823, by rfl⟩ : syracuseStep 1495529 = 1121647) B1121647
theorem B1496033 : Blo 662308 1496033 := bstep (se 2 (by rfl) ⟨561012, by rfl⟩ : syracuseStep 1496033 = 1122025) B1122025
theorem B4248557 : Blo 662308 4248557 := bstep (se 3 (by rfl) ⟨796604, by rfl⟩ : syracuseStep 4248557 = 1593209) B1593209
theorem B1496159 : Blo 662308 1496159 := bstep (se 1 (by rfl) ⟨1122119, by rfl⟩ : syracuseStep 1496159 = 2244239) B2244239
theorem B2839805 : Blo 662308 2839805 := bstep (se 3 (by rfl) ⟨532463, by rfl⟩ : syracuseStep 2839805 = 1064927) B1064927
theorem B11523617 : Blo 662308 11523617 := bstep (se 2 (by rfl) ⟨4321356, by rfl⟩ : syracuseStep 11523617 = 8642713) B8642713
theorem B1496915 : Blo 662308 1496915 := bstep (se 1 (by rfl) ⟨1122686, by rfl⟩ : syracuseStep 1496915 = 2245373) B2245373
theorem B23615621 : Blo 662308 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B1497401 : Blo 662308 1497401 := bstep (se 2 (by rfl) ⟨561525, by rfl⟩ : syracuseStep 1497401 = 1123051) B1123051
theorem B3201563 : Blo 662308 3201563 := bstep (se 1 (by rfl) ⟨2401172, by rfl⟩ : syracuseStep 3201563 = 4802345) B4802345
theorem B4315771 : Blo 662308 4315771 := bstep (se 1 (by rfl) ⟨3236828, by rfl⟩ : syracuseStep 4315771 = 6473657) B6473657
theorem B3201871 : Blo 662308 3201871 := bstep (se 1 (by rfl) ⟨2401403, by rfl⟩ : syracuseStep 3201871 = 4802807) B4802807
theorem B6380369 : Blo 662308 6380369 := bstep (se 2 (by rfl) ⟨2392638, by rfl⟩ : syracuseStep 6380369 = 4785277) B4785277
theorem B1891471 : Blo 662308 1891471 := bstep (se 1 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 1891471 = 2837207) B2837207
theorem B11328659 : Blo 662308 11328659 := bstep (se 1 (by rfl) ⟨8496494, by rfl⟩ : syracuseStep 11328659 = 16992989) B16992989
theorem B1498319 : Blo 662308 1498319 := bstep (se 1 (by rfl) ⟨1123739, by rfl⟩ : syracuseStep 1498319 = 2247479) B2247479
theorem B1498697 : Blo 662308 1498697 := bstep (se 2 (by rfl) ⟨562011, by rfl⟩ : syracuseStep 1498697 = 1124023) B1124023
theorem B1891961 : Blo 662308 1891961 := bstep (se 2 (by rfl) ⟨709485, by rfl⟩ : syracuseStep 1891961 = 1418971) B1418971
theorem B745663 : Blo 662308 745663 := bstep (se 1 (by rfl) ⟨559247, by rfl⟩ : syracuseStep 745663 = 1118495) B1118495
theorem B746095 : Blo 662308 746095 := bstep (se 1 (by rfl) ⟨559571, by rfl⟩ : syracuseStep 746095 = 1119143) B1119143
theorem B746203 : Blo 662308 746203 := bstep (se 1 (by rfl) ⟨559652, by rfl⟩ : syracuseStep 746203 = 1119305) B1119305
theorem B2843579 : Blo 662308 2843579 := bstep (se 1 (by rfl) ⟨2132684, by rfl⟩ : syracuseStep 2843579 = 4265369) B4265369
theorem B17032355 : Blo 662308 17032355 := bstep (se 1 (by rfl) ⟨12774266, by rfl⟩ : syracuseStep 17032355 = 25548533) B25548533
theorem B2844179 : Blo 662308 2844179 := bstep (se 1 (by rfl) ⟨2133134, by rfl⟩ : syracuseStep 2844179 = 4266269) B4266269
theorem B1894387 : Blo 662308 1894387 := bstep (se 1 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 1894387 = 2841581) B2841581
theorem B6056045 : Blo 662308 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B2517115 : Blo 662308 2517115 := bstep (se 1 (by rfl) ⟨1887836, by rfl⟩ : syracuseStep 2517115 = 3775673) B3775673
theorem B748327 : Blo 662308 748327 := bstep (se 1 (by rfl) ⟨561245, by rfl⟩ : syracuseStep 748327 = 1122491) B1122491
theorem B36432773 : Blo 662308 36432773 := bstep (se 4 (by rfl) ⟨3415572, by rfl⟩ : syracuseStep 36432773 = 6831145) B6831145
theorem B1535159 : Blo 662308 1535159 := bstep (se 1 (by rfl) ⟨1151369, by rfl⟩ : syracuseStep 1535159 = 2302739) B2302739
theorem B2387681 : Blo 662308 2387681 := bstep (se 2 (by rfl) ⟨895380, by rfl⟩ : syracuseStep 2387681 = 1790761) B1790761
theorem B2158331 : Blo 662308 2158331 := bstep (se 1 (by rfl) ⟨1618748, by rfl⟩ : syracuseStep 2158331 = 3237497) B3237497
theorem B749551 : Blo 662308 749551 := bstep (se 1 (by rfl) ⟨562163, by rfl⟩ : syracuseStep 749551 = 1124327) B1124327
theorem B12088207 : Blo 662308 12088207 := bstep (se 1 (by rfl) ⟨9066155, by rfl⟩ : syracuseStep 12088207 = 18132311) B18132311
theorem B8090533 : Blo 662308 8090533 := bstep (se 4 (by rfl) ⟨758487, by rfl⟩ : syracuseStep 8090533 = 1516975) B1516975
theorem B717979 : Blo 662308 717979 := bstep (se 1 (by rfl) ⟨538484, by rfl⟩ : syracuseStep 717979 = 1076969) B1076969
theorem B1275145 : Blo 662308 1275145 := bstep (se 2 (by rfl) ⟨478179, by rfl⟩ : syracuseStep 1275145 = 956359) B956359
theorem B36271637 : Blo 662308 36271637 := bstep (se 6 (by rfl) ⟨850116, by rfl⟩ : syracuseStep 36271637 = 1700233) B1700233
theorem B58193473 : Blo 662308 58193473 := bstep (se 2 (by rfl) ⟨21822552, by rfl⟩ : syracuseStep 58193473 = 43645105) B43645105
theorem B947803 : Blo 662308 947803 := bstep (se 1 (by rfl) ⟨710852, by rfl⟩ : syracuseStep 947803 = 1421705) B1421705
theorem B5666759 : Blo 662308 5666759 := bstep (se 1 (by rfl) ⟨4250069, by rfl⟩ : syracuseStep 5666759 = 8500139) B8500139
theorem B3242911 : Blo 662308 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B9567557 : Blo 662308 9567557 := bstep (se 4 (by rfl) ⟨896958, by rfl⟩ : syracuseStep 9567557 = 1793917) B1793917
theorem B2129341 : Blo 662308 2129341 := bstep (se 3 (by rfl) ⟨399251, by rfl⟩ : syracuseStep 2129341 = 798503) B798503
theorem B4095431 : Blo 662308 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B2522735 : Blo 662308 2522735 := bstep (se 1 (by rfl) ⟨1892051, by rfl⟩ : syracuseStep 2522735 = 3784103) B3784103
theorem B6913997 : Blo 662308 6913997 := bstep (se 3 (by rfl) ⟨1296374, by rfl⟩ : syracuseStep 6913997 = 2592749) B2592749
theorem B2883833 : Blo 662308 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B1541071 : Blo 662308 1541071 := bstep (se 1 (by rfl) ⟨1155803, by rfl⟩ : syracuseStep 1541071 = 2311607) B2311607
theorem B27329845 : Blo 662308 27329845 := bstep (se 5 (by rfl) ⟨1281086, by rfl⟩ : syracuseStep 27329845 = 2562173) B2562173
theorem B12977863 : Blo 662308 12977863 := bstep (se 1 (by rfl) ⟨9733397, by rfl⟩ : syracuseStep 12977863 = 19466795) B19466795
theorem B8521919 : Blo 662308 8521919 := bstep (se 1 (by rfl) ⟨6391439, by rfl⟩ : syracuseStep 8521919 = 12782879) B12782879
theorem B4262395 : Blo 662308 4262395 := bstep (se 1 (by rfl) ⟨3196796, by rfl⟩ : syracuseStep 4262395 = 6393593) B6393593
theorem B2525849 : Blo 662308 2525849 := bstep (se 2 (by rfl) ⟨947193, by rfl⟩ : syracuseStep 2525849 = 1894387) B1894387
theorem B756463 : Blo 662308 756463 := bstep (se 1 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 756463 = 1134695) B1134695
theorem B854767 : Blo 662308 854767 := bstep (se 1 (by rfl) ⟨641075, by rfl⟩ : syracuseStep 854767 = 1282151) B1282151
theorem B7277951 : Blo 662308 7277951 := bstep (se 1 (by rfl) ⟨5458463, by rfl⟩ : syracuseStep 7277951 = 10916927) B10916927
theorem B1118299 : Blo 662308 1118299 := bstep (se 1 (by rfl) ⟨838724, by rfl⟩ : syracuseStep 1118299 = 1677449) B1677449
theorem B1118441 : Blo 662308 1118441 := bstep (se 2 (by rfl) ⟨419415, by rfl⟩ : syracuseStep 1118441 = 838831) B838831
theorem B5738849 : Blo 662308 5738849 := bstep (se 2 (by rfl) ⟨2152068, by rfl⟩ : syracuseStep 5738849 = 4304137) B4304137
theorem B1118711 : Blo 662308 1118711 := bstep (se 1 (by rfl) ⟨839033, by rfl⟩ : syracuseStep 1118711 = 1678067) B1678067
theorem B1119467 : Blo 662308 1119467 := bstep (se 1 (by rfl) ⟨839600, by rfl⟩ : syracuseStep 1119467 = 1679201) B1679201
theorem B17045477 : Blo 662308 17045477 := bstep (se 4 (by rfl) ⟨1598013, by rfl⟩ : syracuseStep 17045477 = 3196027) B3196027
theorem B1513655 : Blo 662308 1513655 := bstep (se 1 (by rfl) ⟨1135241, by rfl⟩ : syracuseStep 1513655 = 2270483) B2270483
theorem B1120439 : Blo 662308 1120439 := bstep (se 1 (by rfl) ⟨840329, by rfl⟩ : syracuseStep 1120439 = 1680659) B1680659
theorem B10787377 : Blo 662308 10787377 := bstep (se 2 (by rfl) ⟨4045266, by rfl⟩ : syracuseStep 10787377 = 8090533) B8090533
theorem B4037363 : Blo 662308 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B957305 : Blo 662308 957305 := bstep (se 2 (by rfl) ⟨358989, by rfl⟩ : syracuseStep 957305 = 717979) B717979
theorem B662523 : Blo 662308 662523 := bstep (se 1 (by rfl) ⟨496892, by rfl⟩ : syracuseStep 662523 = 993785) B993785
theorem B662559 : Blo 662308 662559 := bstep (se 1 (by rfl) ⟨496919, by rfl⟩ : syracuseStep 662559 = 993839) B993839
theorem B24288515 : Blo 662308 24288515 := bstep (se 1 (by rfl) ⟨18216386, by rfl⟩ : syracuseStep 24288515 = 36432773) B36432773
theorem B662847 : Blo 662308 662847 := bstep (se 1 (by rfl) ⟨497135, by rfl⟩ : syracuseStep 662847 = 994271) B994271
theorem B8527355 : Blo 662308 8527355 := bstep (se 1 (by rfl) ⟨6395516, by rfl⟩ : syracuseStep 8527355 = 12791033) B12791033
theorem B663143 : Blo 662308 663143 := bstep (se 1 (by rfl) ⟨497357, by rfl⟩ : syracuseStep 663143 = 994715) B994715
theorem B9576089 : Blo 662308 9576089 := bstep (se 2 (by rfl) ⟨3591033, by rfl⟩ : syracuseStep 9576089 = 7182067) B7182067
theorem B1515179 : Blo 662308 1515179 := bstep (se 1 (by rfl) ⟨1136384, by rfl⟩ : syracuseStep 1515179 = 2272769) B2272769
theorem B663423 : Blo 662308 663423 := bstep (se 1 (by rfl) ⟨497567, by rfl⟩ : syracuseStep 663423 = 995135) B995135
theorem B663547 : Blo 662308 663547 := bstep (se 1 (by rfl) ⟨497660, by rfl⟩ : syracuseStep 663547 = 995321) B995321
theorem B663707 : Blo 662308 663707 := bstep (se 1 (by rfl) ⟨497780, by rfl⟩ : syracuseStep 663707 = 995561) B995561
theorem B663791 : Blo 662308 663791 := bstep (se 1 (by rfl) ⟨497843, by rfl⟩ : syracuseStep 663791 = 995687) B995687
theorem B664155 : Blo 662308 664155 := bstep (se 1 (by rfl) ⟨498116, by rfl⟩ : syracuseStep 664155 = 996233) B996233
theorem B7185185 : Blo 662308 7185185 := bstep (se 2 (by rfl) ⟨2694444, by rfl⟩ : syracuseStep 7185185 = 5388889) B5388889
theorem B664411 : Blo 662308 664411 := bstep (se 1 (by rfl) ⟨498308, by rfl⟩ : syracuseStep 664411 = 996617) B996617
theorem B664447 : Blo 662308 664447 := bstep (se 1 (by rfl) ⟨498335, by rfl⟩ : syracuseStep 664447 = 996671) B996671
theorem B30679955 : Blo 662308 30679955 := bstep (se 1 (by rfl) ⟨23009966, by rfl⟩ : syracuseStep 30679955 = 46019933) B46019933
theorem B4269161 : Blo 662308 4269161 := bstep (se 2 (by rfl) ⟨1600935, by rfl⟩ : syracuseStep 4269161 = 3201871) B3201871
theorem B664731 : Blo 662308 664731 := bstep (se 1 (by rfl) ⟨498548, by rfl⟩ : syracuseStep 664731 = 997097) B997097
theorem B1123483 : Blo 662308 1123483 := bstep (se 1 (by rfl) ⟨842612, by rfl⟩ : syracuseStep 1123483 = 1685225) B1685225
theorem B664735 : Blo 662308 664735 := bstep (se 1 (by rfl) ⟨498551, by rfl⟩ : syracuseStep 664735 = 997103) B997103
theorem B3777839 : Blo 662308 3777839 := bstep (se 1 (by rfl) ⟨2833379, by rfl⟩ : syracuseStep 3777839 = 5666759) B5666759
theorem B665039 : Blo 662308 665039 := bstep (se 1 (by rfl) ⟨498779, by rfl⟩ : syracuseStep 665039 = 997559) B997559
theorem B665071 : Blo 662308 665071 := bstep (se 1 (by rfl) ⟨498803, by rfl⟩ : syracuseStep 665071 = 997607) B997607
theorem B11478515 : Blo 662308 11478515 := bstep (se 1 (by rfl) ⟨8608886, by rfl⟩ : syracuseStep 11478515 = 17217773) B17217773
theorem B1681033 : Blo 662308 1681033 := bstep (se 2 (by rfl) ⟨630387, by rfl⟩ : syracuseStep 1681033 = 1260775) B1260775
theorem B665319 : Blo 662308 665319 := bstep (se 1 (by rfl) ⟨498989, by rfl⟩ : syracuseStep 665319 = 997979) B997979
theorem B665415 : Blo 662308 665415 := bstep (se 1 (by rfl) ⟨499061, by rfl⟩ : syracuseStep 665415 = 998123) B998123
theorem B665435 : Blo 662308 665435 := bstep (se 1 (by rfl) ⟨499076, by rfl⟩ : syracuseStep 665435 = 998153) B998153
theorem B993503 : Blo 662308 993503 := bstep (se 1 (by rfl) ⟨745127, by rfl⟩ : syracuseStep 993503 = 1490255) B1490255
theorem B993563 : Blo 662308 993563 := bstep (se 1 (by rfl) ⟨745172, by rfl⟩ : syracuseStep 993563 = 1490345) B1490345
theorem B2730287 : Blo 662308 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B993695 : Blo 662308 993695 := bstep (se 1 (by rfl) ⟨745271, by rfl⟩ : syracuseStep 993695 = 1490543) B1490543
theorem B1681823 : Blo 662308 1681823 := bstep (se 1 (by rfl) ⟨1261367, by rfl⟩ : syracuseStep 1681823 = 2522735) B2522735
theorem B666015 : Blo 662308 666015 := bstep (se 1 (by rfl) ⟨499511, by rfl⟩ : syracuseStep 666015 = 999023) B999023
theorem B666095 : Blo 662308 666095 := bstep (se 1 (by rfl) ⟨499571, by rfl⟩ : syracuseStep 666095 = 999143) B999143
theorem B993887 : Blo 662308 993887 := bstep (se 1 (by rfl) ⟨745415, by rfl⟩ : syracuseStep 993887 = 1490831) B1490831
theorem B666223 : Blo 662308 666223 := bstep (se 1 (by rfl) ⟨499667, by rfl⟩ : syracuseStep 666223 = 999335) B999335
theorem B994217 : Blo 662308 994217 := bstep (se 2 (by rfl) ⟨372831, by rfl⟩ : syracuseStep 994217 = 745663) B745663
theorem B994247 : Blo 662308 994247 := bstep (se 1 (by rfl) ⟨745685, by rfl⟩ : syracuseStep 994247 = 1491371) B1491371
theorem B2239433 : Blo 662308 2239433 := bstep (se 2 (by rfl) ⟨839787, by rfl⟩ : syracuseStep 2239433 = 1679575) B1679575
theorem B994367 : Blo 662308 994367 := bstep (se 1 (by rfl) ⟨745775, by rfl⟩ : syracuseStep 994367 = 1491551) B1491551
theorem B2239595 : Blo 662308 2239595 := bstep (se 1 (by rfl) ⟨1679696, by rfl⟩ : syracuseStep 2239595 = 3359393) B3359393
theorem B994607 : Blo 662308 994607 := bstep (se 1 (by rfl) ⟨745955, by rfl⟩ : syracuseStep 994607 = 1491911) B1491911
theorem B1682815 : Blo 662308 1682815 := bstep (se 1 (by rfl) ⟨1262111, by rfl⟩ : syracuseStep 1682815 = 2524223) B2524223
theorem B994793 : Blo 662308 994793 := bstep (se 2 (by rfl) ⟨373047, by rfl⟩ : syracuseStep 994793 = 746095) B746095
theorem B994847 : Blo 662308 994847 := bstep (se 1 (by rfl) ⟨746135, by rfl⟩ : syracuseStep 994847 = 1492271) B1492271
theorem B994937 : Blo 662308 994937 := bstep (se 2 (by rfl) ⟨373101, by rfl⟩ : syracuseStep 994937 = 746203) B746203
theorem B995183 : Blo 662308 995183 := bstep (se 1 (by rfl) ⟨746387, by rfl⟩ : syracuseStep 995183 = 1492775) B1492775
theorem B995435 : Blo 662308 995435 := bstep (se 1 (by rfl) ⟨746576, by rfl⟩ : syracuseStep 995435 = 1493153) B1493153
theorem B3584375 : Blo 662308 3584375 := bstep (se 1 (by rfl) ⟨2688281, by rfl⟩ : syracuseStep 3584375 = 5376563) B5376563
theorem B995867 : Blo 662308 995867 := bstep (se 1 (by rfl) ⟨746900, by rfl⟩ : syracuseStep 995867 = 1493801) B1493801
theorem B3355343 : Blo 662308 3355343 := bstep (se 1 (by rfl) ⟨2516507, by rfl⟩ : syracuseStep 3355343 = 5033015) B5033015
theorem B996047 : Blo 662308 996047 := bstep (se 1 (by rfl) ⟨747035, by rfl⟩ : syracuseStep 996047 = 1494071) B1494071
theorem B996335 : Blo 662308 996335 := bstep (se 1 (by rfl) ⟨747251, by rfl⟩ : syracuseStep 996335 = 1494503) B1494503
theorem B2700611 : Blo 662308 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B996719 : Blo 662308 996719 := bstep (se 1 (by rfl) ⟨747539, by rfl⟩ : syracuseStep 996719 = 1495079) B1495079
theorem B996839 : Blo 662308 996839 := bstep (se 1 (by rfl) ⟨747629, by rfl⟩ : syracuseStep 996839 = 1495259) B1495259
theorem B3356153 : Blo 662308 3356153 := bstep (se 2 (by rfl) ⟨1258557, by rfl⟩ : syracuseStep 3356153 = 2517115) B2517115
theorem B3356315 : Blo 662308 3356315 := bstep (se 1 (by rfl) ⟨2517236, by rfl⟩ : syracuseStep 3356315 = 5034473) B5034473
theorem B997019 : Blo 662308 997019 := bstep (se 1 (by rfl) ⟨747764, by rfl⟩ : syracuseStep 997019 = 1495529) B1495529
theorem B3356477 : Blo 662308 3356477 := bstep (se 3 (by rfl) ⟨629339, by rfl⟩ : syracuseStep 3356477 = 1258679) B1258679
theorem B1685387 : Blo 662308 1685387 := bstep (se 1 (by rfl) ⟨1264040, by rfl⟩ : syracuseStep 1685387 = 2528081) B2528081
theorem B23017445 : Blo 662308 23017445 := bstep (se 4 (by rfl) ⟨2157885, by rfl⟩ : syracuseStep 23017445 = 4315771) B4315771
theorem B997355 : Blo 662308 997355 := bstep (se 1 (by rfl) ⟨748016, by rfl⟩ : syracuseStep 997355 = 1496033) B1496033
theorem B2832371 : Blo 662308 2832371 := bstep (se 1 (by rfl) ⟨2124278, by rfl⟩ : syracuseStep 2832371 = 4248557) B4248557
theorem B997439 : Blo 662308 997439 := bstep (se 1 (by rfl) ⟨748079, by rfl⟩ : syracuseStep 997439 = 1496159) B1496159
theorem B1063049 : Blo 662308 1063049 := bstep (se 2 (by rfl) ⟨398643, by rfl⟩ : syracuseStep 1063049 = 797287) B797287
theorem B7682411 : Blo 662308 7682411 := bstep (se 1 (by rfl) ⟨5761808, by rfl⟩ : syracuseStep 7682411 = 11523617) B11523617
theorem B997769 : Blo 662308 997769 := bstep (se 2 (by rfl) ⟨374163, by rfl⟩ : syracuseStep 997769 = 748327) B748327
theorem B997943 : Blo 662308 997943 := bstep (se 1 (by rfl) ⟨748457, by rfl⟩ : syracuseStep 997943 = 1496915) B1496915
theorem B15743747 : Blo 662308 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B1686329 : Blo 662308 1686329 := bstep (se 2 (by rfl) ⟨632373, by rfl⟩ : syracuseStep 1686329 = 1264747) B1264747
theorem B998267 : Blo 662308 998267 := bstep (se 1 (by rfl) ⟨748700, by rfl⟩ : syracuseStep 998267 = 1497401) B1497401
theorem B13647113 : Blo 662308 13647113 := bstep (se 2 (by rfl) ⟨5117667, by rfl⟩ : syracuseStep 13647113 = 10235335) B10235335
theorem B64470437 : Blo 662308 64470437 := bstep (se 4 (by rfl) ⟨6044103, by rfl⟩ : syracuseStep 64470437 = 12088207) B12088207
theorem B7552439 : Blo 662308 7552439 := bstep (se 1 (by rfl) ⟨5664329, by rfl⟩ : syracuseStep 7552439 = 11328659) B11328659
theorem B1490399 : Blo 662308 1490399 := bstep (se 1 (by rfl) ⟨1117799, by rfl⟩ : syracuseStep 1490399 = 2235599) B2235599
theorem B998879 : Blo 662308 998879 := bstep (se 1 (by rfl) ⟨749159, by rfl⟩ : syracuseStep 998879 = 1498319) B1498319
theorem B1490651 : Blo 662308 1490651 := bstep (se 1 (by rfl) ⟨1117988, by rfl⟩ : syracuseStep 1490651 = 2235977) B2235977
theorem B999131 : Blo 662308 999131 := bstep (se 1 (by rfl) ⟨749348, by rfl⟩ : syracuseStep 999131 = 1498697) B1498697
theorem B1261307 : Blo 662308 1261307 := bstep (se 1 (by rfl) ⟨945980, by rfl⟩ : syracuseStep 1261307 = 1891961) B1891961
theorem B1490921 : Blo 662308 1490921 := bstep (se 2 (by rfl) ⟨559095, by rfl⟩ : syracuseStep 1490921 = 1118191) B1118191
theorem B999401 : Blo 662308 999401 := bstep (se 2 (by rfl) ⟨374775, by rfl⟩ : syracuseStep 999401 = 749551) B749551
theorem B11354903 : Blo 662308 11354903 := bstep (se 1 (by rfl) ⟨8516177, by rfl⟩ : syracuseStep 11354903 = 17032355) B17032355
theorem B2245913 : Blo 662308 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B6800773 : Blo 662308 6800773 := bstep (se 4 (by rfl) ⟨637572, by rfl⟩ : syracuseStep 6800773 = 1275145) B1275145
theorem B1492379 : Blo 662308 1492379 := bstep (se 1 (by rfl) ⟨1119284, by rfl⟩ : syracuseStep 1492379 = 2238569) B2238569
theorem B8537501 : Blo 662308 8537501 := bstep (se 3 (by rfl) ⟨1600781, by rfl⟩ : syracuseStep 8537501 = 3201563) B3201563
theorem B3360365 : Blo 662308 3360365 := bstep (se 3 (by rfl) ⟨630068, by rfl⟩ : syracuseStep 3360365 = 1260137) B1260137
theorem B1263737 : Blo 662308 1263737 := bstep (se 2 (by rfl) ⟨473901, by rfl⟩ : syracuseStep 1263737 = 947803) B947803
theorem B1591787 : Blo 662308 1591787 := bstep (se 1 (by rfl) ⟨1193840, by rfl⟩ : syracuseStep 1591787 = 2387681) B2387681
theorem B6474593 : Blo 662308 6474593 := bstep (se 2 (by rfl) ⟨2427972, by rfl⟩ : syracuseStep 6474593 = 4855945) B4855945
theorem B1494863 : Blo 662308 1494863 := bstep (se 1 (by rfl) ⟨1121147, by rfl⟩ : syracuseStep 1494863 = 2242295) B2242295
theorem B5689277 : Blo 662308 5689277 := bstep (se 3 (by rfl) ⟨1066739, by rfl⟩ : syracuseStep 5689277 = 2133479) B2133479
theorem B1888703 : Blo 662308 1888703 := bstep (se 1 (by rfl) ⟨1416527, by rfl⟩ : syracuseStep 1888703 = 2833055) B2833055
theorem B840127 : Blo 662308 840127 := bstep (se 1 (by rfl) ⟨630095, by rfl⟩ : syracuseStep 840127 = 1260191) B1260191
theorem B840223 : Blo 662308 840223 := bstep (se 1 (by rfl) ⟨630167, by rfl⟩ : syracuseStep 840223 = 1260335) B1260335
theorem B1495583 : Blo 662308 1495583 := bstep (se 1 (by rfl) ⟨1121687, by rfl⟩ : syracuseStep 1495583 = 2243375) B2243375
theorem B2839121 : Blo 662308 2839121 := bstep (se 2 (by rfl) ⟨1064670, by rfl⟩ : syracuseStep 2839121 = 2129341) B2129341
theorem B5755549 : Blo 662308 5755549 := bstep (se 3 (by rfl) ⟨1079165, by rfl⟩ : syracuseStep 5755549 = 2158331) B2158331
theorem B6378371 : Blo 662308 6378371 := bstep (se 1 (by rfl) ⟨4783778, by rfl⟩ : syracuseStep 6378371 = 9567557) B9567557
theorem B1496015 : Blo 662308 1496015 := bstep (se 1 (by rfl) ⟨1122011, by rfl⟩ : syracuseStep 1496015 = 2244023) B2244023
theorem B1496105 : Blo 662308 1496105 := bstep (se 2 (by rfl) ⟨561039, by rfl⟩ : syracuseStep 1496105 = 1122079) B1122079
theorem B840775 : Blo 662308 840775 := bstep (se 1 (by rfl) ⟨630581, by rfl⟩ : syracuseStep 840775 = 1261163) B1261163
theorem B1823951 : Blo 662308 1823951 := bstep (se 1 (by rfl) ⟨1367963, by rfl⟩ : syracuseStep 1823951 = 2735927) B2735927
theorem B4609331 : Blo 662308 4609331 := bstep (se 1 (by rfl) ⟨3456998, by rfl⟩ : syracuseStep 4609331 = 6913997) B6913997
theorem B1496375 : Blo 662308 1496375 := bstep (se 1 (by rfl) ⟨1122281, by rfl⟩ : syracuseStep 1496375 = 2244563) B2244563
theorem B1496393 : Blo 662308 1496393 := bstep (se 2 (by rfl) ⟨561147, by rfl⟩ : syracuseStep 1496393 = 1122295) B1122295
theorem B1496681 : Blo 662308 1496681 := bstep (se 2 (by rfl) ⟨561255, by rfl⟩ : syracuseStep 1496681 = 1122511) B1122511
theorem B30627841 : Blo 662308 30627841 := bstep (se 2 (by rfl) ⟨11485440, by rfl⟩ : syracuseStep 30627841 = 22970881) B22970881
theorem B6740147 : Blo 662308 6740147 := bstep (se 1 (by rfl) ⟨5055110, by rfl⟩ : syracuseStep 6740147 = 10110221) B10110221
theorem B1497311 : Blo 662308 1497311 := bstep (se 1 (by rfl) ⟨1122983, by rfl⟩ : syracuseStep 1497311 = 2245967) B2245967
theorem B1497383 : Blo 662308 1497383 := bstep (se 1 (by rfl) ⟨1123037, by rfl⟩ : syracuseStep 1497383 = 2246075) B2246075
theorem B157866565 : Blo 662308 157866565 := bstep (se 4 (by rfl) ⟨14799990, by rfl⟩ : syracuseStep 157866565 = 29599981) B29599981
theorem B1497743 : Blo 662308 1497743 := bstep (se 1 (by rfl) ⟨1123307, by rfl⟩ : syracuseStep 1497743 = 2246615) B2246615
theorem B1497833 : Blo 662308 1497833 := bstep (se 2 (by rfl) ⟨561687, by rfl⟩ : syracuseStep 1497833 = 1123375) B1123375
theorem B842663 : Blo 662308 842663 := bstep (se 1 (by rfl) ⟨631997, by rfl⟩ : syracuseStep 842663 = 1263995) B1263995
theorem B842815 : Blo 662308 842815 := bstep (se 1 (by rfl) ⟨632111, by rfl⟩ : syracuseStep 842815 = 1264223) B1264223
theorem B3792167 : Blo 662308 3792167 := bstep (se 1 (by rfl) ⟨2844125, by rfl⟩ : syracuseStep 3792167 = 5688251) B5688251
theorem B3366521 : Blo 662308 3366521 := bstep (se 2 (by rfl) ⟨1262445, by rfl⟩ : syracuseStep 3366521 = 2524891) B2524891
theorem B2023265 : Blo 662308 2023265 := bstep (se 2 (by rfl) ⟨758724, by rfl⟩ : syracuseStep 2023265 = 1517449) B1517449
theorem B2515643 : Blo 662308 2515643 := bstep (se 1 (by rfl) ⟨1886732, by rfl⟩ : syracuseStep 2515643 = 3773465) B3773465
theorem B1893145 : Blo 662308 1893145 := bstep (se 2 (by rfl) ⟨709929, by rfl⟩ : syracuseStep 1893145 = 1419859) B1419859
theorem B1893203 : Blo 662308 1893203 := bstep (se 1 (by rfl) ⟨1419902, by rfl⟩ : syracuseStep 1893203 = 2839805) B2839805
theorem B6054907 : Blo 662308 6054907 := bstep (se 1 (by rfl) ⟨4541180, by rfl⟩ : syracuseStep 6054907 = 9082361) B9082361
theorem B746599 : Blo 662308 746599 := bstep (se 1 (by rfl) ⟨559949, by rfl⟩ : syracuseStep 746599 = 1119899) B1119899
theorem B2516129 : Blo 662308 2516129 := bstep (se 2 (by rfl) ⟨943548, by rfl⟩ : syracuseStep 2516129 = 1887097) B1887097
theorem B2516143 : Blo 662308 2516143 := bstep (se 1 (by rfl) ⟨1887107, by rfl⟩ : syracuseStep 2516143 = 3774215) B3774215
theorem B1009007 : Blo 662308 1009007 := bstep (se 1 (by rfl) ⟨756755, by rfl⟩ : syracuseStep 1009007 = 1513511) B1513511
theorem B6383443 : Blo 662308 6383443 := bstep (se 1 (by rfl) ⟨4787582, by rfl⟩ : syracuseStep 6383443 = 9575165) B9575165
theorem B4253579 : Blo 662308 4253579 := bstep (se 1 (by rfl) ⟨3190184, by rfl⟩ : syracuseStep 4253579 = 6380369) B6380369
theorem B2516903 : Blo 662308 2516903 := bstep (se 1 (by rfl) ⟨1887677, by rfl⟩ : syracuseStep 2516903 = 3775355) B3775355
theorem B3238393 : Blo 662308 3238393 := bstep (se 2 (by rfl) ⟨1214397, by rfl⟩ : syracuseStep 3238393 = 2428795) B2428795
theorem B2517587 : Blo 662308 2517587 := bstep (se 1 (by rfl) ⟨1888190, by rfl⟩ : syracuseStep 2517587 = 3776381) B3776381
theorem B2518087 : Blo 662308 2518087 := bstep (se 1 (by rfl) ⟨1888565, by rfl⟩ : syracuseStep 2518087 = 3777131) B3777131
theorem B1895719 : Blo 662308 1895719 := bstep (se 1 (by rfl) ⟨1421789, by rfl⟩ : syracuseStep 1895719 = 2843579) B2843579
theorem B945479 : Blo 662308 945479 := bstep (se 1 (by rfl) ⟨709109, by rfl⟩ : syracuseStep 945479 = 1418219) B1418219
theorem B1896119 : Blo 662308 1896119 := bstep (se 1 (by rfl) ⟨1422089, by rfl⟩ : syracuseStep 1896119 = 2844179) B2844179
theorem B2125559 : Blo 662308 2125559 := bstep (se 1 (by rfl) ⟨1594169, by rfl⟩ : syracuseStep 2125559 = 3188339) B3188339
theorem B2518847 : Blo 662308 2518847 := bstep (se 1 (by rfl) ⟨1889135, by rfl⟩ : syracuseStep 2518847 = 3778271) B3778271
theorem B3370895 : Blo 662308 3370895 := bstep (se 1 (by rfl) ⟨2528171, by rfl⟩ : syracuseStep 3370895 = 5056343) B5056343
theorem B2125855 : Blo 662308 2125855 := bstep (se 1 (by rfl) ⟨1594391, by rfl⟩ : syracuseStep 2125855 = 3188783) B3188783
theorem B5042249 : Blo 662308 5042249 := bstep (se 2 (by rfl) ⟨1890843, by rfl⟩ : syracuseStep 5042249 = 3781687) B3781687
theorem B77591297 : Blo 662308 77591297 := bstep (se 2 (by rfl) ⟨29096736, by rfl⟩ : syracuseStep 77591297 = 58193473) B58193473
theorem B947695 : Blo 662308 947695 := bstep (se 1 (by rfl) ⟨710771, by rfl⟩ : syracuseStep 947695 = 1421543) B1421543
theorem B4093757 : Blo 662308 4093757 := bstep (se 3 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 4093757 = 1535159) B1535159
theorem B2521003 : Blo 662308 2521003 := bstep (se 1 (by rfl) ⟨1890752, by rfl⟩ : syracuseStep 2521003 = 3781505) B3781505
theorem B3897371 : Blo 662308 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B24181091 : Blo 662308 24181091 := bstep (se 1 (by rfl) ⟨18135818, by rfl⟩ : syracuseStep 24181091 = 36271637) B36271637
theorem B4323881 : Blo 662308 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B1800967 : Blo 662308 1800967 := bstep (se 1 (by rfl) ⟨1350725, by rfl⟩ : syracuseStep 1800967 = 2701451) B2701451
theorem B7174979 : Blo 662308 7174979 := bstep (se 1 (by rfl) ⟨5381234, by rfl⟩ : syracuseStep 7174979 = 10762469) B10762469
theorem B2521961 : Blo 662308 2521961 := bstep (se 2 (by rfl) ⟨945735, by rfl⟩ : syracuseStep 2521961 = 1891471) B1891471
theorem B8092871 : Blo 662308 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B7569935 : Blo 662308 7569935 := bstep (se 1 (by rfl) ⟨5677451, by rfl⟩ : syracuseStep 7569935 = 11354903) B11354903
theorem B2524193 : Blo 662308 2524193 := bstep (se 2 (by rfl) ⟨946572, by rfl⟩ : syracuseStep 2524193 = 1893145) B1893145
theorem B36439793 : Blo 662308 36439793 := bstep (se 2 (by rfl) ⟨13664922, by rfl⟩ : syracuseStep 36439793 = 27329845) B27329845
theorem B4851967 : Blo 662308 4851967 := bstep (se 1 (by rfl) ⟨3638975, by rfl⟩ : syracuseStep 4851967 = 7277951) B7277951
theorem B1215967 : Blo 662308 1215967 := bstep (se 1 (by rfl) ⟨911975, by rfl⟩ : syracuseStep 1215967 = 1823951) B1823951
theorem B30609373 : Blo 662308 30609373 := bstep (se 3 (by rfl) ⟨5739257, by rfl⟩ : syracuseStep 30609373 = 11478515) B11478515
theorem B4493431 : Blo 662308 4493431 := bstep (se 1 (by rfl) ⟨3370073, by rfl⟩ : syracuseStep 4493431 = 6740147) B6740147
theorem B2527625 : Blo 662308 2527625 := bstep (se 2 (by rfl) ⟨947859, by rfl⟩ : syracuseStep 2527625 = 1895719) B1895719
theorem B2691575 : Blo 662308 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B16192343 : Blo 662308 16192343 := bstep (se 1 (by rfl) ⟨12144257, by rfl⟩ : syracuseStep 16192343 = 24288515) B24288515
theorem B2528111 : Blo 662308 2528111 := bstep (se 1 (by rfl) ⟨1896083, by rfl⟩ : syracuseStep 2528111 = 3792167) B3792167
theorem B1677095 : Blo 662308 1677095 := bstep (se 1 (by rfl) ⟨1257821, by rfl⟩ : syracuseStep 1677095 = 2515643) B2515643
theorem B4790123 : Blo 662308 4790123 := bstep (se 1 (by rfl) ⟨3592592, by rfl⟩ : syracuseStep 4790123 = 7185185) B7185185
theorem B1120169 : Blo 662308 1120169 := bstep (se 2 (by rfl) ⟨420063, by rfl⟩ : syracuseStep 1120169 = 840127) B840127
theorem B20453303 : Blo 662308 20453303 := bstep (se 1 (by rfl) ⟨15339977, by rfl⟩ : syracuseStep 20453303 = 30679955) B30679955
theorem B1120297 : Blo 662308 1120297 := bstep (se 2 (by rfl) ⟨420111, by rfl⟩ : syracuseStep 1120297 = 840223) B840223
theorem B1677419 : Blo 662308 1677419 := bstep (se 1 (by rfl) ⟨1258064, by rfl⟩ : syracuseStep 1677419 = 2516129) B2516129
theorem B7280765 : Blo 662308 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B7674065 : Blo 662308 7674065 := bstep (se 2 (by rfl) ⟨2877774, by rfl⟩ : syracuseStep 7674065 = 5755549) B5755549
theorem B20486429 : Blo 662308 20486429 := bstep (se 3 (by rfl) ⟨3841205, by rfl⟩ : syracuseStep 20486429 = 7682411) B7682411
theorem B1677935 : Blo 662308 1677935 := bstep (se 1 (by rfl) ⟨1258451, by rfl⟩ : syracuseStep 1677935 = 2516903) B2516903
theorem B1121033 : Blo 662308 1121033 := bstep (se 2 (by rfl) ⟨420387, by rfl⟩ : syracuseStep 1121033 = 840775) B840775
theorem B662335 : Blo 662308 662335 := bstep (se 1 (by rfl) ⟨496751, by rfl⟩ : syracuseStep 662335 = 993503) B993503
theorem B662375 : Blo 662308 662375 := bstep (se 1 (by rfl) ⟨496781, by rfl⟩ : syracuseStep 662375 = 993563) B993563
theorem B662463 : Blo 662308 662463 := bstep (se 1 (by rfl) ⟨496847, by rfl⟩ : syracuseStep 662463 = 993695) B993695
theorem B1121215 : Blo 662308 1121215 := bstep (se 1 (by rfl) ⟨840911, by rfl⟩ : syracuseStep 1121215 = 1681823) B1681823
theorem B1678391 : Blo 662308 1678391 := bstep (se 1 (by rfl) ⟨1258793, by rfl⟩ : syracuseStep 1678391 = 2517587) B2517587
theorem B662591 : Blo 662308 662591 := bstep (se 1 (by rfl) ⟨496943, by rfl⟩ : syracuseStep 662591 = 993887) B993887
theorem B662811 : Blo 662308 662811 := bstep (se 1 (by rfl) ⟨497108, by rfl⟩ : syracuseStep 662811 = 994217) B994217
theorem B662831 : Blo 662308 662831 := bstep (se 1 (by rfl) ⟨497123, by rfl⟩ : syracuseStep 662831 = 994247) B994247
theorem B662911 : Blo 662308 662911 := bstep (se 1 (by rfl) ⟨497183, by rfl⟩ : syracuseStep 662911 = 994367) B994367
theorem B663071 : Blo 662308 663071 := bstep (se 1 (by rfl) ⟨497303, by rfl⟩ : syracuseStep 663071 = 994607) B994607
theorem B663195 : Blo 662308 663195 := bstep (se 1 (by rfl) ⟨497396, by rfl⟩ : syracuseStep 663195 = 994793) B994793
theorem B663231 : Blo 662308 663231 := bstep (se 1 (by rfl) ⟨497423, by rfl⟩ : syracuseStep 663231 = 994847) B994847
theorem B663291 : Blo 662308 663291 := bstep (se 1 (by rfl) ⟨497468, by rfl⟩ : syracuseStep 663291 = 994937) B994937
theorem B1679231 : Blo 662308 1679231 := bstep (se 1 (by rfl) ⟨1259423, by rfl⟩ : syracuseStep 1679231 = 2518847) B2518847
theorem B663455 : Blo 662308 663455 := bstep (se 1 (by rfl) ⟨497591, by rfl⟩ : syracuseStep 663455 = 995183) B995183
theorem B40837121 : Blo 662308 40837121 := bstep (se 2 (by rfl) ⟨15313920, by rfl⟩ : syracuseStep 40837121 = 30627841) B30627841
theorem B663623 : Blo 662308 663623 := bstep (se 1 (by rfl) ⟨497717, by rfl⟩ : syracuseStep 663623 = 995435) B995435
theorem B663911 : Blo 662308 663911 := bstep (se 1 (by rfl) ⟨497933, by rfl⟩ : syracuseStep 663911 = 995867) B995867
theorem B2236895 : Blo 662308 2236895 := bstep (se 1 (by rfl) ⟨1677671, by rfl⟩ : syracuseStep 2236895 = 3355343) B3355343
theorem B664031 : Blo 662308 664031 := bstep (se 1 (by rfl) ⟨498023, by rfl⟩ : syracuseStep 664031 = 996047) B996047
theorem B664223 : Blo 662308 664223 := bstep (se 1 (by rfl) ⟨498167, by rfl⟩ : syracuseStep 664223 = 996335) B996335
theorem B664479 : Blo 662308 664479 := bstep (se 1 (by rfl) ⟨498359, by rfl⟩ : syracuseStep 664479 = 996719) B996719
theorem B664559 : Blo 662308 664559 := bstep (se 1 (by rfl) ⟨498419, by rfl⟩ : syracuseStep 664559 = 996839) B996839
theorem B2237435 : Blo 662308 2237435 := bstep (se 1 (by rfl) ⟨1678076, by rfl⟩ : syracuseStep 2237435 = 3356153) B3356153
theorem B2401289 : Blo 662308 2401289 := bstep (se 2 (by rfl) ⟨900483, by rfl⟩ : syracuseStep 2401289 = 1800967) B1800967
theorem B69215269 : Blo 662308 69215269 := bstep (se 4 (by rfl) ⟨6488931, by rfl⟩ : syracuseStep 69215269 = 12977863) B12977863
theorem B2237543 : Blo 662308 2237543 := bstep (se 1 (by rfl) ⟨1678157, by rfl⟩ : syracuseStep 2237543 = 3356315) B3356315
theorem B664679 : Blo 662308 664679 := bstep (se 1 (by rfl) ⟨498509, by rfl⟩ : syracuseStep 664679 = 997019) B997019
theorem B2237651 : Blo 662308 2237651 := bstep (se 1 (by rfl) ⟨1678238, by rfl⟩ : syracuseStep 2237651 = 3356477) B3356477
theorem B2729171 : Blo 662308 2729171 := bstep (se 1 (by rfl) ⟨2046878, by rfl⟩ : syracuseStep 2729171 = 4093757) B4093757
theorem B1123591 : Blo 662308 1123591 := bstep (se 1 (by rfl) ⟨842693, by rfl⟩ : syracuseStep 1123591 = 1685387) B1685387
theorem B15344963 : Blo 662308 15344963 := bstep (se 1 (by rfl) ⟨11508722, by rfl⟩ : syracuseStep 15344963 = 23017445) B23017445
theorem B664903 : Blo 662308 664903 := bstep (se 1 (by rfl) ⟨498677, by rfl⟩ : syracuseStep 664903 = 997355) B997355
theorem B2598247 : Blo 662308 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B664959 : Blo 662308 664959 := bstep (se 1 (by rfl) ⟨498719, by rfl⟩ : syracuseStep 664959 = 997439) B997439
theorem B1123753 : Blo 662308 1123753 := bstep (se 2 (by rfl) ⟨421407, by rfl⟩ : syracuseStep 1123753 = 842815) B842815
theorem B665179 : Blo 662308 665179 := bstep (se 1 (by rfl) ⟨498884, by rfl⟩ : syracuseStep 665179 = 997769) B997769
theorem B665295 : Blo 662308 665295 := bstep (se 1 (by rfl) ⟨498971, by rfl⟩ : syracuseStep 665295 = 997943) B997943
theorem B10495831 : Blo 662308 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B1124219 : Blo 662308 1124219 := bstep (se 1 (by rfl) ⟨843164, by rfl⟩ : syracuseStep 1124219 = 1686329) B1686329
theorem B1681307 : Blo 662308 1681307 := bstep (se 1 (by rfl) ⟨1260980, by rfl⟩ : syracuseStep 1681307 = 2521961) B2521961
theorem B665511 : Blo 662308 665511 := bstep (se 1 (by rfl) ⟨499133, by rfl⟩ : syracuseStep 665511 = 998267) B998267
theorem B993599 : Blo 662308 993599 := bstep (se 1 (by rfl) ⟨745199, by rfl⟩ : syracuseStep 993599 = 1490399) B1490399
theorem B665919 : Blo 662308 665919 := bstep (se 1 (by rfl) ⟨499439, by rfl⟩ : syracuseStep 665919 = 998879) B998879
theorem B993767 : Blo 662308 993767 := bstep (se 1 (by rfl) ⟨745325, by rfl⟩ : syracuseStep 993767 = 1490651) B1490651
theorem B666087 : Blo 662308 666087 := bstep (se 1 (by rfl) ⟨499565, by rfl⟩ : syracuseStep 666087 = 999131) B999131
theorem B993947 : Blo 662308 993947 := bstep (se 1 (by rfl) ⟨745460, by rfl⟩ : syracuseStep 993947 = 1490921) B1490921
theorem B666267 : Blo 662308 666267 := bstep (se 1 (by rfl) ⟨499700, by rfl⟩ : syracuseStep 666267 = 999401) B999401
theorem B994919 : Blo 662308 994919 := bstep (se 1 (by rfl) ⟨746189, by rfl⟩ : syracuseStep 994919 = 1492379) B1492379
theorem B2240243 : Blo 662308 2240243 := bstep (se 1 (by rfl) ⟨1680182, by rfl⟩ : syracuseStep 2240243 = 3360365) B3360365
theorem B8073209 : Blo 662308 8073209 := bstep (se 2 (by rfl) ⟨3027453, by rfl⟩ : syracuseStep 8073209 = 6054907) B6054907
theorem B5681279 : Blo 662308 5681279 := bstep (se 1 (by rfl) ⟨4260959, by rfl⟩ : syracuseStep 5681279 = 8521919) B8521919
theorem B995465 : Blo 662308 995465 := bstep (se 2 (by rfl) ⟨373299, by rfl⟩ : syracuseStep 995465 = 746599) B746599
theorem B3354857 : Blo 662308 3354857 := bstep (se 2 (by rfl) ⟨1258071, by rfl⟩ : syracuseStep 3354857 = 2516143) B2516143
theorem B1061191 : Blo 662308 1061191 := bstep (se 1 (by rfl) ⟨795893, by rfl⟩ : syracuseStep 1061191 = 1591787) B1591787
theorem B1683899 : Blo 662308 1683899 := bstep (se 1 (by rfl) ⟨1262924, by rfl⟩ : syracuseStep 1683899 = 2525849) B2525849
theorem B206910125 : Blo 662308 206910125 := bstep (se 3 (by rfl) ⟨38795648, by rfl⟩ : syracuseStep 206910125 = 77591297) B77591297
theorem B2241377 : Blo 662308 2241377 := bstep (se 2 (by rfl) ⟨840516, by rfl⟩ : syracuseStep 2241377 = 1681033) B1681033
theorem B996575 : Blo 662308 996575 := bstep (se 1 (by rfl) ⟨747431, by rfl⟩ : syracuseStep 996575 = 1494863) B1494863
theorem B1259135 : Blo 662308 1259135 := bstep (se 1 (by rfl) ⟨944351, by rfl⟩ : syracuseStep 1259135 = 1888703) B1888703
theorem B997055 : Blo 662308 997055 := bstep (se 1 (by rfl) ⟨747791, by rfl⟩ : syracuseStep 997055 = 1495583) B1495583
theorem B997343 : Blo 662308 997343 := bstep (se 1 (by rfl) ⟨748007, by rfl⟩ : syracuseStep 997343 = 1496015) B1496015
theorem B5683193 : Blo 662308 5683193 := bstep (se 2 (by rfl) ⟨2131197, by rfl⟩ : syracuseStep 5683193 = 4262395) B4262395
theorem B997403 : Blo 662308 997403 := bstep (se 1 (by rfl) ⟨748052, by rfl⟩ : syracuseStep 997403 = 1496105) B1496105
theorem B997583 : Blo 662308 997583 := bstep (se 1 (by rfl) ⟨748187, by rfl⟩ : syracuseStep 997583 = 1496375) B1496375
theorem B997595 : Blo 662308 997595 := bstep (se 1 (by rfl) ⟨748196, by rfl⟩ : syracuseStep 997595 = 1496393) B1496393
theorem B997787 : Blo 662308 997787 := bstep (se 1 (by rfl) ⟨748340, by rfl⟩ : syracuseStep 997787 = 1496681) B1496681
theorem B3357449 : Blo 662308 3357449 := bstep (se 2 (by rfl) ⟨1259043, by rfl⟩ : syracuseStep 3357449 = 2518087) B2518087
theorem B998207 : Blo 662308 998207 := bstep (se 1 (by rfl) ⟨748655, by rfl⟩ : syracuseStep 998207 = 1497311) B1497311
theorem B998255 : Blo 662308 998255 := bstep (se 1 (by rfl) ⟨748691, by rfl⟩ : syracuseStep 998255 = 1497383) B1497383
theorem B998495 : Blo 662308 998495 := bstep (se 1 (by rfl) ⟨748871, by rfl⟩ : syracuseStep 998495 = 1497743) B1497743
theorem B998555 : Blo 662308 998555 := bstep (se 1 (by rfl) ⟨748916, by rfl⟩ : syracuseStep 998555 = 1497833) B1497833
theorem B2243753 : Blo 662308 2243753 := bstep (se 2 (by rfl) ⟨841407, by rfl⟩ : syracuseStep 2243753 = 1682815) B1682815
theorem B5684903 : Blo 662308 5684903 := bstep (se 1 (by rfl) ⟨4263677, by rfl⟩ : syracuseStep 5684903 = 8527355) B8527355
theorem B2244347 : Blo 662308 2244347 := bstep (se 1 (by rfl) ⟨1683260, by rfl⟩ : syracuseStep 2244347 = 3366521) B3366521
theorem B2834473 : Blo 662308 2834473 := bstep (se 2 (by rfl) ⟨1062927, by rfl⟩ : syracuseStep 2834473 = 2125855) B2125855
theorem B1491065 : Blo 662308 1491065 := bstep (se 2 (by rfl) ⟨559149, by rfl⟩ : syracuseStep 1491065 = 1118299) B1118299
theorem B2834797 : Blo 662308 2834797 := bstep (se 3 (by rfl) ⟨531524, by rfl⟩ : syracuseStep 2834797 = 1063049) B1063049
theorem B1262135 : Blo 662308 1262135 := bstep (se 1 (by rfl) ⟨946601, by rfl⟩ : syracuseStep 1262135 = 1893203) B1893203
theorem B672671 : Blo 662308 672671 := bstep (se 1 (by rfl) ⟨504503, by rfl⟩ : syracuseStep 672671 = 1009007) B1009007
theorem B2835719 : Blo 662308 2835719 := bstep (se 1 (by rfl) ⟨2126789, by rfl⟩ : syracuseStep 2835719 = 4253579) B4253579
theorem B1492955 : Blo 662308 1492955 := bstep (se 1 (by rfl) ⟨1119716, by rfl⟩ : syracuseStep 1492955 = 2239433) B2239433
theorem B1263593 : Blo 662308 1263593 := bstep (se 2 (by rfl) ⟨473847, by rfl⟩ : syracuseStep 1263593 = 947695) B947695
theorem B1493063 : Blo 662308 1493063 := bstep (se 1 (by rfl) ⟨1119797, by rfl⟩ : syracuseStep 1493063 = 2239595) B2239595
theorem B2247101 : Blo 662308 2247101 := bstep (se 3 (by rfl) ⟨421331, by rfl⟩ : syracuseStep 2247101 = 842663) B842663
theorem B1264079 : Blo 662308 1264079 := bstep (se 1 (by rfl) ⟨948059, by rfl⟩ : syracuseStep 1264079 = 1896119) B1896119
theorem B3361337 : Blo 662308 3361337 := bstep (se 2 (by rfl) ⟨1260501, by rfl⟩ : syracuseStep 3361337 = 2521003) B2521003
theorem B2247263 : Blo 662308 2247263 := bstep (se 1 (by rfl) ⟨1685447, by rfl⟩ : syracuseStep 2247263 = 3370895) B3370895
theorem B3361499 : Blo 662308 3361499 := bstep (se 1 (by rfl) ⟨2521124, by rfl⟩ : syracuseStep 3361499 = 5042249) B5042249
theorem B210488753 : Blo 662308 210488753 := bstep (se 2 (by rfl) ⟨78933282, by rfl⟩ : syracuseStep 210488753 = 157866565) B157866565
theorem B1888247 : Blo 662308 1888247 := bstep (se 1 (by rfl) ⟨1416185, by rfl⟩ : syracuseStep 1888247 = 2832371) B2832371
theorem B5395247 : Blo 662308 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B9098075 : Blo 662308 9098075 := bstep (se 1 (by rfl) ⟨6823556, by rfl⟩ : syracuseStep 9098075 = 13647113) B13647113
theorem B5395373 : Blo 662308 5395373 := bstep (se 3 (by rfl) ⟨1011632, by rfl⟩ : syracuseStep 5395373 = 2023265) B2023265
theorem B42980291 : Blo 662308 42980291 := bstep (se 1 (by rfl) ⟨32235218, by rfl⟩ : syracuseStep 42980291 = 64470437) B64470437
theorem B5034959 : Blo 662308 5034959 := bstep (se 1 (by rfl) ⟨3776219, by rfl⟩ : syracuseStep 5034959 = 7552439) B7552439
theorem B840871 : Blo 662308 840871 := bstep (se 1 (by rfl) ⟨630653, by rfl⟩ : syracuseStep 840871 = 1261307) B1261307
theorem B1922555 : Blo 662308 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B1497275 : Blo 662308 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B5691667 : Blo 662308 5691667 := bstep (se 1 (by rfl) ⟨4268750, by rfl⟩ : syracuseStep 5691667 = 8537501) B8537501
theorem B842491 : Blo 662308 842491 := bstep (se 1 (by rfl) ⟨631868, by rfl⟩ : syracuseStep 842491 = 1263737) B1263737
theorem B1497977 : Blo 662308 1497977 := bstep (se 2 (by rfl) ⟨561741, by rfl⟩ : syracuseStep 1497977 = 1123483) B1123483
theorem B9067697 : Blo 662308 9067697 := bstep (se 2 (by rfl) ⟨3400386, by rfl⟩ : syracuseStep 9067697 = 6800773) B6800773
theorem B8511257 : Blo 662308 8511257 := bstep (se 2 (by rfl) ⟨3191721, by rfl⟩ : syracuseStep 8511257 = 6383443) B6383443
theorem B3792851 : Blo 662308 3792851 := bstep (se 1 (by rfl) ⟨2844638, by rfl⟩ : syracuseStep 3792851 = 5689277) B5689277
theorem B745627 : Blo 662308 745627 := bstep (se 1 (by rfl) ⟨559220, by rfl⟩ : syracuseStep 745627 = 1118441) B1118441
theorem B3825899 : Blo 662308 3825899 := bstep (se 1 (by rfl) ⟨2869424, by rfl⟩ : syracuseStep 3825899 = 5738849) B5738849
theorem B745807 : Blo 662308 745807 := bstep (se 1 (by rfl) ⟨559355, by rfl⟩ : syracuseStep 745807 = 1118711) B1118711
theorem B1892747 : Blo 662308 1892747 := bstep (se 1 (by rfl) ⟨1419560, by rfl⟩ : syracuseStep 1892747 = 2839121) B2839121
theorem B4252247 : Blo 662308 4252247 := bstep (se 1 (by rfl) ⟨3189185, by rfl⟩ : syracuseStep 4252247 = 6378371) B6378371
theorem B4317857 : Blo 662308 4317857 := bstep (se 2 (by rfl) ⟨1619196, by rfl⟩ : syracuseStep 4317857 = 3238393) B3238393
theorem B746311 : Blo 662308 746311 := bstep (se 1 (by rfl) ⟨559733, by rfl⟩ : syracuseStep 746311 = 1119467) B1119467
theorem B3072887 : Blo 662308 3072887 := bstep (se 1 (by rfl) ⟨2304665, by rfl⟩ : syracuseStep 3072887 = 4609331) B4609331
theorem B1008617 : Blo 662308 1008617 := bstep (se 2 (by rfl) ⟨378231, by rfl⟩ : syracuseStep 1008617 = 756463) B756463
theorem B1139689 : Blo 662308 1139689 := bstep (se 2 (by rfl) ⟨427383, by rfl⟩ : syracuseStep 1139689 = 854767) B854767
theorem B11363651 : Blo 662308 11363651 := bstep (se 1 (by rfl) ⟨8522738, by rfl⟩ : syracuseStep 11363651 = 17045477) B17045477
theorem B1009103 : Blo 662308 1009103 := bstep (se 1 (by rfl) ⟨756827, by rfl⟩ : syracuseStep 1009103 = 1513655) B1513655
theorem B746959 : Blo 662308 746959 := bstep (se 1 (by rfl) ⟨560219, by rfl⟩ : syracuseStep 746959 = 1120439) B1120439
theorem B8219045 : Blo 662308 8219045 := bstep (se 4 (by rfl) ⟨770535, by rfl⟩ : syracuseStep 8219045 = 1541071) B1541071
theorem B6384059 : Blo 662308 6384059 := bstep (se 1 (by rfl) ⟨4788044, by rfl⟩ : syracuseStep 6384059 = 9576089) B9576089
theorem B1010119 : Blo 662308 1010119 := bstep (se 1 (by rfl) ⟨757589, by rfl⟩ : syracuseStep 1010119 = 1515179) B1515179
theorem B2846107 : Blo 662308 2846107 := bstep (se 1 (by rfl) ⟨2134580, by rfl⟩ : syracuseStep 2846107 = 4269161) B4269161
theorem B2518559 : Blo 662308 2518559 := bstep (se 1 (by rfl) ⟨1888919, by rfl⟩ : syracuseStep 2518559 = 3777839) B3777839
theorem B17265581 : Blo 662308 17265581 := bstep (se 3 (by rfl) ⟨3237296, by rfl⟩ : syracuseStep 17265581 = 6474593) B6474593
theorem B2552813 : Blo 662308 2552813 := bstep (se 3 (by rfl) ⟨478652, by rfl⟩ : syracuseStep 2552813 = 957305) B957305
theorem B2389583 : Blo 662308 2389583 := bstep (se 1 (by rfl) ⟨1792187, by rfl⟩ : syracuseStep 2389583 = 3584375) B3584375
theorem B14383169 : Blo 662308 14383169 := bstep (se 2 (by rfl) ⟨5393688, by rfl⟩ : syracuseStep 14383169 = 10787377) B10787377
theorem B2521277 : Blo 662308 2521277 := bstep (se 3 (by rfl) ⟨472739, by rfl⟩ : syracuseStep 2521277 = 945479) B945479
theorem B1800407 : Blo 662308 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B16120727 : Blo 662308 16120727 := bstep (se 1 (by rfl) ⟨12090545, by rfl⟩ : syracuseStep 16120727 = 24181091) B24181091
theorem B2882587 : Blo 662308 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B4783319 : Blo 662308 4783319 := bstep (se 1 (by rfl) ⟨3587489, by rfl⟩ : syracuseStep 4783319 = 7174979) B7174979
theorem B5668157 : Blo 662308 5668157 := bstep (se 3 (by rfl) ⟨1062779, by rfl⟩ : syracuseStep 5668157 = 2125559) B2125559
theorem B5046623 : Blo 662308 5046623 := bstep (se 1 (by rfl) ⟨3784967, by rfl⟩ : syracuseStep 5046623 = 7569935) B7569935
theorem B13994441 : Blo 662308 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B2689645 : Blo 662308 2689645 := bstep (se 3 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 2689645 = 1008617) B1008617
theorem B7277789 : Blo 662308 7277789 := bstep (se 3 (by rfl) ⟨1364585, by rfl⟩ : syracuseStep 7277789 = 2729171) B2729171
theorem B6065383 : Blo 662308 6065383 := bstep (se 1 (by rfl) ⟨4549037, by rfl⟩ : syracuseStep 6065383 = 9098075) B9098075
theorem B1346825 : Blo 662308 1346825 := bstep (se 2 (by rfl) ⟨505059, by rfl⟩ : syracuseStep 1346825 = 1010119) B1010119
theorem B1118063 : Blo 662308 1118063 := bstep (se 1 (by rfl) ⟨838547, by rfl⟩ : syracuseStep 1118063 = 1677095) B1677095
theorem B2690941 : Blo 662308 2690941 := bstep (se 3 (by rfl) ⟨504551, by rfl⟩ : syracuseStep 2690941 = 1009103) B1009103
theorem B13635535 : Blo 662308 13635535 := bstep (se 1 (by rfl) ⟨10226651, by rfl⟩ : syracuseStep 13635535 = 20453303) B20453303
theorem B1118279 : Blo 662308 1118279 := bstep (se 1 (by rfl) ⟨838709, by rfl⟩ : syracuseStep 1118279 = 1677419) B1677419
theorem B4853843 : Blo 662308 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B5116043 : Blo 662308 5116043 := bstep (se 1 (by rfl) ⟨3837032, by rfl⟩ : syracuseStep 5116043 = 7674065) B7674065
theorem B1118623 : Blo 662308 1118623 := bstep (se 1 (by rfl) ⟨838967, by rfl⟩ : syracuseStep 1118623 = 1677935) B1677935
theorem B1118927 : Blo 662308 1118927 := bstep (se 1 (by rfl) ⟨839195, by rfl⟩ : syracuseStep 1118927 = 1678391) B1678391
theorem B5674171 : Blo 662308 5674171 := bstep (se 1 (by rfl) ⟨4255628, by rfl⟩ : syracuseStep 5674171 = 8511257) B8511257
theorem B1119487 : Blo 662308 1119487 := bstep (se 1 (by rfl) ⟨839615, by rfl⟩ : syracuseStep 1119487 = 1679231) B1679231
theorem B2528567 : Blo 662308 2528567 := bstep (se 1 (by rfl) ⟨1896425, by rfl⟩ : syracuseStep 2528567 = 3792851) B3792851
theorem B1414921 : Blo 662308 1414921 := bstep (se 2 (by rfl) ⟨530595, by rfl⟩ : syracuseStep 1414921 = 1061191) B1061191
theorem B10229975 : Blo 662308 10229975 := bstep (se 1 (by rfl) ⟨7672481, by rfl⟩ : syracuseStep 10229975 = 15344963) B15344963
theorem B7575767 : Blo 662308 7575767 := bstep (se 1 (by rfl) ⟨5681825, by rfl⟩ : syracuseStep 7575767 = 11363651) B11363651
theorem B1120871 : Blo 662308 1120871 := bstep (se 1 (by rfl) ⟨840653, by rfl⟩ : syracuseStep 1120871 = 1681307) B1681307
theorem B662399 : Blo 662308 662399 := bstep (se 1 (by rfl) ⟨496799, by rfl⟩ : syracuseStep 662399 = 993599) B993599
theorem B1121161 : Blo 662308 1121161 := bstep (se 2 (by rfl) ⟨420435, by rfl⟩ : syracuseStep 1121161 = 840871) B840871
theorem B5479363 : Blo 662308 5479363 := bstep (se 1 (by rfl) ⟨4109522, by rfl⟩ : syracuseStep 5479363 = 8219045) B8219045
theorem B662511 : Blo 662308 662511 := bstep (se 1 (by rfl) ⟨496883, by rfl⟩ : syracuseStep 662511 = 993767) B993767
theorem B662631 : Blo 662308 662631 := bstep (se 1 (by rfl) ⟨496973, by rfl⟩ : syracuseStep 662631 = 993947) B993947
theorem B1679039 : Blo 662308 1679039 := bstep (se 1 (by rfl) ⟨1259279, by rfl⟩ : syracuseStep 1679039 = 2518559) B2518559
theorem B663279 : Blo 662308 663279 := bstep (se 1 (by rfl) ⟨497459, by rfl⟩ : syracuseStep 663279 = 994919) B994919
theorem B5382139 : Blo 662308 5382139 := bstep (se 1 (by rfl) ⟨4036604, by rfl⟩ : syracuseStep 5382139 = 8073209) B8073209
theorem B663643 : Blo 662308 663643 := bstep (se 1 (by rfl) ⟨497732, by rfl⟩ : syracuseStep 663643 = 995465) B995465
theorem B2236571 : Blo 662308 2236571 := bstep (se 1 (by rfl) ⟨1677428, by rfl⟩ : syracuseStep 2236571 = 3354857) B3354857
theorem B1122599 : Blo 662308 1122599 := bstep (se 1 (by rfl) ⟨841949, by rfl⟩ : syracuseStep 1122599 = 1683899) B1683899
theorem B11510387 : Blo 662308 11510387 := bstep (se 1 (by rfl) ⟨8632790, by rfl⟩ : syracuseStep 11510387 = 17265581) B17265581
theorem B664383 : Blo 662308 664383 := bstep (se 1 (by rfl) ⟨498287, by rfl⟩ : syracuseStep 664383 = 996575) B996575
theorem B1123321 : Blo 662308 1123321 := bstep (se 2 (by rfl) ⟨421245, by rfl⟩ : syracuseStep 1123321 = 842491) B842491
theorem B664703 : Blo 662308 664703 := bstep (se 1 (by rfl) ⟨498527, by rfl⟩ : syracuseStep 664703 = 997055) B997055
theorem B664895 : Blo 662308 664895 := bstep (se 1 (by rfl) ⟨498671, by rfl⟩ : syracuseStep 664895 = 997343) B997343
theorem B664935 : Blo 662308 664935 := bstep (se 1 (by rfl) ⟨498701, by rfl⟩ : syracuseStep 664935 = 997403) B997403
theorem B3843449 : Blo 662308 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B1680851 : Blo 662308 1680851 := bstep (se 1 (by rfl) ⟨1260638, by rfl⟩ : syracuseStep 1680851 = 2521277) B2521277
theorem B665055 : Blo 662308 665055 := bstep (se 1 (by rfl) ⟨498791, by rfl⟩ : syracuseStep 665055 = 997583) B997583
theorem B665063 : Blo 662308 665063 := bstep (se 1 (by rfl) ⟨498797, by rfl⟩ : syracuseStep 665063 = 997595) B997595
theorem B665191 : Blo 662308 665191 := bstep (se 1 (by rfl) ⟨498893, by rfl⟩ : syracuseStep 665191 = 997787) B997787
theorem B2238299 : Blo 662308 2238299 := bstep (se 1 (by rfl) ⟨1678724, by rfl⟩ : syracuseStep 2238299 = 3357449) B3357449
theorem B665471 : Blo 662308 665471 := bstep (se 1 (by rfl) ⟨499103, by rfl⟩ : syracuseStep 665471 = 998207) B998207
theorem B665503 : Blo 662308 665503 := bstep (se 1 (by rfl) ⟨499127, by rfl⟩ : syracuseStep 665503 = 998255) B998255
theorem B665663 : Blo 662308 665663 := bstep (se 1 (by rfl) ⟨499247, by rfl⟩ : syracuseStep 665663 = 998495) B998495
theorem B665703 : Blo 662308 665703 := bstep (se 1 (by rfl) ⟨499277, by rfl⟩ : syracuseStep 665703 = 998555) B998555
theorem B3188879 : Blo 662308 3188879 := bstep (se 1 (by rfl) ⟨2391659, by rfl⟩ : syracuseStep 3188879 = 4783319) B4783319
theorem B3778771 : Blo 662308 3778771 := bstep (se 1 (by rfl) ⟨2834078, by rfl⟩ : syracuseStep 3778771 = 5668157) B5668157
theorem B3779297 : Blo 662308 3779297 := bstep (se 2 (by rfl) ⟨1417236, by rfl⟩ : syracuseStep 3779297 = 2834473) B2834473
theorem B994043 : Blo 662308 994043 := bstep (se 1 (by rfl) ⟨745532, by rfl⟩ : syracuseStep 994043 = 1491065) B1491065
theorem B994169 : Blo 662308 994169 := bstep (se 2 (by rfl) ⟨372813, by rfl⟩ : syracuseStep 994169 = 745627) B745627
theorem B994409 : Blo 662308 994409 := bstep (se 2 (by rfl) ⟨372903, by rfl⟩ : syracuseStep 994409 = 745807) B745807
theorem B3779729 : Blo 662308 3779729 := bstep (se 2 (by rfl) ⟨1417398, by rfl⟩ : syracuseStep 3779729 = 2834797) B2834797
theorem B1682795 : Blo 662308 1682795 := bstep (se 1 (by rfl) ⟨1262096, by rfl⟩ : syracuseStep 1682795 = 2524193) B2524193
theorem B995081 : Blo 662308 995081 := bstep (se 2 (by rfl) ⟨373155, by rfl⟩ : syracuseStep 995081 = 746311) B746311
theorem B24293195 : Blo 662308 24293195 := bstep (se 1 (by rfl) ⟨18219896, by rfl⟩ : syracuseStep 24293195 = 36439793) B36439793
theorem B995303 : Blo 662308 995303 := bstep (se 1 (by rfl) ⟨746477, by rfl⟩ : syracuseStep 995303 = 1492955) B1492955
theorem B995375 : Blo 662308 995375 := bstep (se 1 (by rfl) ⟨746531, by rfl⟩ : syracuseStep 995375 = 1493063) B1493063
theorem B92287025 : Blo 662308 92287025 := bstep (se 2 (by rfl) ⟨34607634, by rfl⟩ : syracuseStep 92287025 = 69215269) B69215269
theorem B2240891 : Blo 662308 2240891 := bstep (se 1 (by rfl) ⟨1680668, by rfl⟩ : syracuseStep 2240891 = 3361337) B3361337
theorem B2240999 : Blo 662308 2240999 := bstep (se 1 (by rfl) ⟨1680749, by rfl⟩ : syracuseStep 2240999 = 3361499) B3361499
theorem B995945 : Blo 662308 995945 := bstep (se 2 (by rfl) ⟨373479, by rfl⟩ : syracuseStep 995945 = 746959) B746959
theorem B1258831 : Blo 662308 1258831 := bstep (se 1 (by rfl) ⟨944123, by rfl⟩ : syracuseStep 1258831 = 1888247) B1888247
theorem B1685083 : Blo 662308 1685083 := bstep (se 1 (by rfl) ⟨1263812, by rfl⟩ : syracuseStep 1685083 = 2527625) B2527625
theorem B6469289 : Blo 662308 6469289 := bstep (se 2 (by rfl) ⟨2425983, by rfl⟩ : syracuseStep 6469289 = 4851967) B4851967
theorem B1685407 : Blo 662308 1685407 := bstep (se 1 (by rfl) ⟨1264055, by rfl⟩ : syracuseStep 1685407 = 2528111) B2528111
theorem B28653527 : Blo 662308 28653527 := bstep (se 1 (by rfl) ⟨21490145, by rfl⟩ : syracuseStep 28653527 = 42980291) B42980291
theorem B3356639 : Blo 662308 3356639 := bstep (se 1 (by rfl) ⟨2517479, by rfl⟩ : syracuseStep 3356639 = 5034959) B5034959
theorem B3193415 : Blo 662308 3193415 := bstep (se 1 (by rfl) ⟨2395061, by rfl⟩ : syracuseStep 3193415 = 4790123) B4790123
theorem B5126813 : Blo 662308 5126813 := bstep (se 3 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 5126813 = 1922555) B1922555
theorem B998183 : Blo 662308 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B998651 : Blo 662308 998651 := bstep (se 1 (by rfl) ⟨748988, by rfl⟩ : syracuseStep 998651 = 1497977) B1497977
theorem B1621289 : Blo 662308 1621289 := bstep (se 2 (by rfl) ⟨607983, by rfl⟩ : syracuseStep 1621289 = 1215967) B1215967
theorem B6045131 : Blo 662308 6045131 := bstep (se 1 (by rfl) ⟨4533848, by rfl⟩ : syracuseStep 6045131 = 9067697) B9067697
theorem B6078341 : Blo 662308 6078341 := bstep (se 4 (by rfl) ⟨569844, by rfl⟩ : syracuseStep 6078341 = 1139689) B1139689
theorem B40812497 : Blo 662308 40812497 := bstep (se 2 (by rfl) ⟨15304686, by rfl⟩ : syracuseStep 40812497 = 30609373) B30609373
theorem B1261831 : Blo 662308 1261831 := bstep (se 1 (by rfl) ⟨946373, by rfl⟩ : syracuseStep 1261831 = 1892747) B1892747
theorem B1491263 : Blo 662308 1491263 := bstep (se 1 (by rfl) ⟨1118447, by rfl⟩ : syracuseStep 1491263 = 2236895) B2236895
theorem B2834831 : Blo 662308 2834831 := bstep (se 1 (by rfl) ⟨2126123, by rfl⟩ : syracuseStep 2834831 = 4252247) B4252247
theorem B2048591 : Blo 662308 2048591 := bstep (se 1 (by rfl) ⟨1536443, by rfl⟩ : syracuseStep 2048591 = 3072887) B3072887
theorem B1491623 : Blo 662308 1491623 := bstep (se 1 (by rfl) ⟨1118717, by rfl⟩ : syracuseStep 1491623 = 2237435) B2237435
theorem B1491695 : Blo 662308 1491695 := bstep (se 1 (by rfl) ⟨1118771, by rfl⟩ : syracuseStep 1491695 = 2237543) B2237543
theorem B1491767 : Blo 662308 1491767 := bstep (se 1 (by rfl) ⟨1118825, by rfl⟩ : syracuseStep 1491767 = 2237651) B2237651
theorem B1493495 : Blo 662308 1493495 := bstep (se 1 (by rfl) ⟨1120121, by rfl⟩ : syracuseStep 1493495 = 2240243) B2240243
theorem B1493729 : Blo 662308 1493729 := bstep (se 2 (by rfl) ⟨560148, by rfl⟩ : syracuseStep 1493729 = 1120297) B1120297
theorem B3787519 : Blo 662308 3787519 := bstep (se 1 (by rfl) ⟨2840639, by rfl⟩ : syracuseStep 3787519 = 5681279) B5681279
theorem B7588889 : Blo 662308 7588889 := bstep (se 2 (by rfl) ⟨2845833, by rfl⟩ : syracuseStep 7588889 = 5691667) B5691667
theorem B137940083 : Blo 662308 137940083 := bstep (se 1 (by rfl) ⟨103455062, by rfl⟩ : syracuseStep 137940083 = 206910125) B206910125
theorem B1494251 : Blo 662308 1494251 := bstep (se 1 (by rfl) ⟨1120688, by rfl⟩ : syracuseStep 1494251 = 2241377) B2241377
theorem B1593055 : Blo 662308 1593055 := bstep (se 1 (by rfl) ⟨1194791, by rfl⟩ : syracuseStep 1593055 = 2389583) B2389583
theorem B839423 : Blo 662308 839423 := bstep (se 1 (by rfl) ⟨629567, by rfl⟩ : syracuseStep 839423 = 1259135) B1259135
theorem B561303341 : Blo 662308 561303341 := bstep (se 3 (by rfl) ⟨105244376, by rfl⟩ : syracuseStep 561303341 = 210488753) B210488753
theorem B1494953 : Blo 662308 1494953 := bstep (se 2 (by rfl) ⟨560607, by rfl⟩ : syracuseStep 1494953 = 1121215) B1121215
theorem B3788795 : Blo 662308 3788795 := bstep (se 1 (by rfl) ⟨2841596, by rfl⟩ : syracuseStep 3788795 = 5683193) B5683193
theorem B9588779 : Blo 662308 9588779 := bstep (se 1 (by rfl) ⟨7191584, by rfl⟩ : syracuseStep 9588779 = 14383169) B14383169
theorem B1200271 : Blo 662308 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B1495835 : Blo 662308 1495835 := bstep (se 1 (by rfl) ⟨1121876, by rfl⟩ : syracuseStep 1495835 = 2243753) B2243753
theorem B3789935 : Blo 662308 3789935 := bstep (se 1 (by rfl) ⟨2842451, by rfl⟩ : syracuseStep 3789935 = 5684903) B5684903
theorem B1496231 : Blo 662308 1496231 := bstep (se 1 (by rfl) ⟨1122173, by rfl⟩ : syracuseStep 1496231 = 2244347) B2244347
theorem B841423 : Blo 662308 841423 := bstep (se 1 (by rfl) ⟨631067, by rfl⟩ : syracuseStep 841423 = 1262135) B1262135
theorem B1890479 : Blo 662308 1890479 := bstep (se 1 (by rfl) ⟨1417859, by rfl⟩ : syracuseStep 1890479 = 2835719) B2835719
theorem B842395 : Blo 662308 842395 := bstep (se 1 (by rfl) ⟨631796, by rfl⟩ : syracuseStep 842395 = 1263593) B1263593
theorem B1498067 : Blo 662308 1498067 := bstep (se 1 (by rfl) ⟨1123550, by rfl⟩ : syracuseStep 1498067 = 2247101) B2247101
theorem B842719 : Blo 662308 842719 := bstep (se 1 (by rfl) ⟨632039, by rfl⟩ : syracuseStep 842719 = 1264079) B1264079
theorem B1498121 : Blo 662308 1498121 := bstep (se 2 (by rfl) ⟨561795, by rfl⟩ : syracuseStep 1498121 = 1123591) B1123591
theorem B1498175 : Blo 662308 1498175 := bstep (se 1 (by rfl) ⟨1123631, by rfl⟩ : syracuseStep 1498175 = 2247263) B2247263
theorem B3464329 : Blo 662308 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B1498337 : Blo 662308 1498337 := bstep (se 2 (by rfl) ⟨561876, by rfl⟩ : syracuseStep 1498337 = 1123753) B1123753
theorem B43179581 : Blo 662308 43179581 := bstep (se 3 (by rfl) ⟨8096171, by rfl⟩ : syracuseStep 43179581 = 16192343) B16192343
theorem B1793789 : Blo 662308 1793789 := bstep (se 3 (by rfl) ⟨336335, by rfl⟩ : syracuseStep 1793789 = 672671) B672671
theorem B1794383 : Blo 662308 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B3596831 : Blo 662308 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B3596915 : Blo 662308 3596915 := bstep (se 1 (by rfl) ⟨2697686, by rfl⟩ : syracuseStep 3596915 = 5395373) B5395373
theorem B746779 : Blo 662308 746779 := bstep (se 1 (by rfl) ⟨560084, by rfl⟩ : syracuseStep 746779 = 1120169) B1120169
theorem B13657619 : Blo 662308 13657619 := bstep (se 1 (by rfl) ⟨10243214, by rfl⟩ : syracuseStep 13657619 = 20486429) B20486429
theorem B747355 : Blo 662308 747355 := bstep (se 1 (by rfl) ⟨560516, by rfl⟩ : syracuseStep 747355 = 1121033) B1121033
theorem B3794809 : Blo 662308 3794809 := bstep (se 2 (by rfl) ⟨1423053, by rfl⟩ : syracuseStep 3794809 = 2846107) B2846107
theorem B27224747 : Blo 662308 27224747 := bstep (se 1 (by rfl) ⟨20418560, by rfl⟩ : syracuseStep 27224747 = 40837121) B40837121
theorem B2550599 : Blo 662308 2550599 := bstep (se 1 (by rfl) ⟨1912949, by rfl⟩ : syracuseStep 2550599 = 3825899) B3825899
theorem B5991241 : Blo 662308 5991241 := bstep (se 2 (by rfl) ⟨2246715, by rfl⟩ : syracuseStep 5991241 = 4493431) B4493431
theorem B2878571 : Blo 662308 2878571 := bstep (se 1 (by rfl) ⟨2158928, by rfl⟩ : syracuseStep 2878571 = 4317857) B4317857
theorem B1600859 : Blo 662308 1600859 := bstep (se 1 (by rfl) ⟨1200644, by rfl⟩ : syracuseStep 1600859 = 2401289) B2401289
theorem B749479 : Blo 662308 749479 := bstep (se 1 (by rfl) ⟨562109, by rfl⟩ : syracuseStep 749479 = 1124219) B1124219
theorem B4256039 : Blo 662308 4256039 := bstep (se 1 (by rfl) ⟨3192029, by rfl⟩ : syracuseStep 4256039 = 6384059) B6384059
theorem B1701875 : Blo 662308 1701875 := bstep (se 1 (by rfl) ⟨1276406, by rfl⟩ : syracuseStep 1701875 = 2552813) B2552813
theorem B10747151 : Blo 662308 10747151 := bstep (se 1 (by rfl) ⟨8060363, by rfl⟩ : syracuseStep 10747151 = 16120727) B16120727
theorem B2525863 : Blo 662308 2525863 := bstep (se 1 (by rfl) ⟨1894397, by rfl⟩ : syracuseStep 2525863 = 3788795) B3788795
theorem B6392519 : Blo 662308 6392519 := bstep (se 1 (by rfl) ⟨4794389, by rfl⟩ : syracuseStep 6392519 = 9588779) B9588779
theorem B3410695 : Blo 662308 3410695 := bstep (se 1 (by rfl) ⟨2558021, by rfl⟩ : syracuseStep 3410695 = 5116043) B5116043
theorem B2526623 : Blo 662308 2526623 := bstep (se 1 (by rfl) ⟨1894967, by rfl⟩ : syracuseStep 2526623 = 3789935) B3789935
theorem B5050025 : Blo 662308 5050025 := bstep (se 2 (by rfl) ⟨1893759, by rfl⟩ : syracuseStep 5050025 = 3787519) B3787519
theorem B6819983 : Blo 662308 6819983 := bstep (se 1 (by rfl) ⟨5114987, by rfl⟩ : syracuseStep 6819983 = 10229975) B10229975
theorem B5050511 : Blo 662308 5050511 := bstep (se 1 (by rfl) ⟨3787883, by rfl⟩ : syracuseStep 5050511 = 7575767) B7575767
theorem B1119359 : Blo 662308 1119359 := bstep (se 1 (by rfl) ⟨839519, by rfl⟩ : syracuseStep 1119359 = 1679039) B1679039
theorem B2397887 : Blo 662308 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B7673591 : Blo 662308 7673591 := bstep (se 1 (by rfl) ⟨5755193, by rfl⟩ : syracuseStep 7673591 = 11510387) B11510387
theorem B2397943 : Blo 662308 2397943 := bstep (se 1 (by rfl) ⟨1798457, by rfl⟩ : syracuseStep 2397943 = 3596915) B3596915
theorem B2562299 : Blo 662308 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B1120567 : Blo 662308 1120567 := bstep (se 1 (by rfl) ⟨840425, by rfl⟩ : syracuseStep 1120567 = 1680851) B1680851
theorem B1678441 : Blo 662308 1678441 := bstep (se 2 (by rfl) ⟨629415, by rfl⟩ : syracuseStep 1678441 = 1258831) B1258831
theorem B662695 : Blo 662308 662695 := bstep (se 1 (by rfl) ⟨497021, by rfl⟩ : syracuseStep 662695 = 994043) B994043
theorem B662779 : Blo 662308 662779 := bstep (se 1 (by rfl) ⟨497084, by rfl⟩ : syracuseStep 662779 = 994169) B994169
theorem B662939 : Blo 662308 662939 := bstep (se 1 (by rfl) ⟨497204, by rfl⟩ : syracuseStep 662939 = 994409) B994409
theorem B1121863 : Blo 662308 1121863 := bstep (se 1 (by rfl) ⟨841397, by rfl⟩ : syracuseStep 1121863 = 1682795) B1682795
theorem B1121897 : Blo 662308 1121897 := bstep (se 2 (by rfl) ⟨420711, by rfl⟩ : syracuseStep 1121897 = 841423) B841423
theorem B663387 : Blo 662308 663387 := bstep (se 1 (by rfl) ⟨497540, by rfl⟩ : syracuseStep 663387 = 995081) B995081
theorem B16195463 : Blo 662308 16195463 := bstep (se 1 (by rfl) ⟨12146597, by rfl⟩ : syracuseStep 16195463 = 24293195) B24293195
theorem B663535 : Blo 662308 663535 := bstep (se 1 (by rfl) ⟨497651, by rfl⟩ : syracuseStep 663535 = 995303) B995303
theorem B663583 : Blo 662308 663583 := bstep (se 1 (by rfl) ⟨497687, by rfl⟩ : syracuseStep 663583 = 995375) B995375
theorem B663963 : Blo 662308 663963 := bstep (se 1 (by rfl) ⟨497972, by rfl⟩ : syracuseStep 663963 = 995945) B995945
theorem B19407437 : Blo 662308 19407437 := bstep (se 3 (by rfl) ⟨3638894, by rfl⟩ : syracuseStep 19407437 = 7277789) B7277789
theorem B1123193 : Blo 662308 1123193 := bstep (se 2 (by rfl) ⟨421197, by rfl⟩ : syracuseStep 1123193 = 842395) B842395
theorem B1123625 : Blo 662308 1123625 := bstep (se 2 (by rfl) ⟨421359, by rfl⟩ : syracuseStep 1123625 = 842719) B842719
theorem B2237759 : Blo 662308 2237759 := bstep (se 1 (by rfl) ⟨1678319, by rfl⟩ : syracuseStep 2237759 = 3356639) B3356639
theorem B3417875 : Blo 662308 3417875 := bstep (se 1 (by rfl) ⟨2563406, by rfl⟩ : syracuseStep 3417875 = 5126813) B5126813
theorem B665455 : Blo 662308 665455 := bstep (se 1 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 665455 = 998183) B998183
theorem B2238461 : Blo 662308 2238461 := bstep (se 3 (by rfl) ⟨419711, by rfl⟩ : syracuseStep 2238461 = 839423) B839423
theorem B665767 : Blo 662308 665767 := bstep (se 1 (by rfl) ⟨499325, by rfl⟩ : syracuseStep 665767 = 998651) B998651
theorem B27208331 : Blo 662308 27208331 := bstep (se 1 (by rfl) ⟨20406248, by rfl⟩ : syracuseStep 27208331 = 40812497) B40812497
theorem B994175 : Blo 662308 994175 := bstep (se 1 (by rfl) ⟨745631, by rfl⟩ : syracuseStep 994175 = 1491263) B1491263
theorem B1682441 : Blo 662308 1682441 := bstep (se 2 (by rfl) ⟨630915, by rfl⟩ : syracuseStep 1682441 = 1261831) B1261831
theorem B994415 : Blo 662308 994415 := bstep (se 1 (by rfl) ⟨745811, by rfl⟩ : syracuseStep 994415 = 1491623) B1491623
theorem B994463 : Blo 662308 994463 := bstep (se 1 (by rfl) ⟨745847, by rfl⟩ : syracuseStep 994463 = 1491695) B1491695
theorem B994511 : Blo 662308 994511 := bstep (se 1 (by rfl) ⟨745883, by rfl⟩ : syracuseStep 994511 = 1491767) B1491767
theorem B995663 : Blo 662308 995663 := bstep (se 1 (by rfl) ⟨746747, by rfl⟩ : syracuseStep 995663 = 1493495) B1493495
theorem B995705 : Blo 662308 995705 := bstep (se 2 (by rfl) ⟨373389, by rfl⟩ : syracuseStep 995705 = 746779) B746779
theorem B995819 : Blo 662308 995819 := bstep (se 1 (by rfl) ⟨746864, by rfl⟩ : syracuseStep 995819 = 1493729) B1493729
theorem B5059259 : Blo 662308 5059259 := bstep (se 1 (by rfl) ⟨3794444, by rfl⟩ : syracuseStep 5059259 = 7588889) B7588889
theorem B91960055 : Blo 662308 91960055 := bstep (se 1 (by rfl) ⟨68970041, by rfl⟩ : syracuseStep 91960055 = 137940083) B137940083
theorem B996167 : Blo 662308 996167 := bstep (se 1 (by rfl) ⟨747125, by rfl⟩ : syracuseStep 996167 = 1494251) B1494251
theorem B996473 : Blo 662308 996473 := bstep (se 2 (by rfl) ⟨373677, by rfl⟩ : syracuseStep 996473 = 747355) B747355
theorem B5059745 : Blo 662308 5059745 := bstep (se 2 (by rfl) ⟨1897404, by rfl⟩ : syracuseStep 5059745 = 3794809) B3794809
theorem B996635 : Blo 662308 996635 := bstep (se 1 (by rfl) ⟨747476, by rfl⟩ : syracuseStep 996635 = 1494953) B1494953
theorem B997223 : Blo 662308 997223 := bstep (se 1 (by rfl) ⟨747917, by rfl⟩ : syracuseStep 997223 = 1495835) B1495835
theorem B997487 : Blo 662308 997487 := bstep (se 1 (by rfl) ⟨748115, by rfl⟩ : syracuseStep 997487 = 1496231) B1496231
theorem B3586193 : Blo 662308 3586193 := bstep (se 2 (by rfl) ⟨1344822, by rfl⟩ : syracuseStep 3586193 = 2689645) B2689645
theorem B1685711 : Blo 662308 1685711 := bstep (se 1 (by rfl) ⟨1264283, by rfl⟩ : syracuseStep 1685711 = 2528567) B2528567
theorem B36420317 : Blo 662308 36420317 := bstep (se 3 (by rfl) ⟨6828809, by rfl⟩ : syracuseStep 36420317 = 13657619) B13657619
theorem B998711 : Blo 662308 998711 := bstep (se 1 (by rfl) ⟨749033, by rfl⟩ : syracuseStep 998711 = 1498067) B1498067
theorem B998747 : Blo 662308 998747 := bstep (se 1 (by rfl) ⟨749060, by rfl⟩ : syracuseStep 998747 = 1498121) B1498121
theorem B998783 : Blo 662308 998783 := bstep (se 1 (by rfl) ⟨749087, by rfl⟩ : syracuseStep 998783 = 1498175) B1498175
theorem B998891 : Blo 662308 998891 := bstep (se 1 (by rfl) ⟨749168, by rfl⟩ : syracuseStep 998891 = 1498337) B1498337
theorem B28786387 : Blo 662308 28786387 := bstep (se 1 (by rfl) ⟨21589790, by rfl⟩ : syracuseStep 28786387 = 43179581) B43179581
theorem B3587921 : Blo 662308 3587921 := bstep (se 2 (by rfl) ⟨1345470, by rfl⟩ : syracuseStep 3587921 = 2690941) B2690941
theorem B1195859 : Blo 662308 1195859 := bstep (se 1 (by rfl) ⟨896894, by rfl⟩ : syracuseStep 1195859 = 1793789) B1793789
theorem B999305 : Blo 662308 999305 := bstep (se 2 (by rfl) ⟨374739, by rfl⟩ : syracuseStep 999305 = 749479) B749479
theorem B4538333 : Blo 662308 4538333 := bstep (se 3 (by rfl) ⟨850937, by rfl⟩ : syracuseStep 4538333 = 1701875) B1701875
theorem B1491047 : Blo 662308 1491047 := bstep (se 1 (by rfl) ⟨1118285, by rfl⟩ : syracuseStep 1491047 = 2236571) B2236571
theorem B1196255 : Blo 662308 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B1491497 : Blo 662308 1491497 := bstep (se 2 (by rfl) ⟨559311, by rfl⟩ : syracuseStep 1491497 = 1118623) B1118623
theorem B1492199 : Blo 662308 1492199 := bstep (se 1 (by rfl) ⟨1119149, by rfl⟩ : syracuseStep 1492199 = 2238299) B2238299
theorem B1492649 : Blo 662308 1492649 := bstep (se 2 (by rfl) ⟨559743, by rfl⟩ : syracuseStep 1492649 = 1119487) B1119487
theorem B1919047 : Blo 662308 1919047 := bstep (se 1 (by rfl) ⟨1439285, by rfl⟩ : syracuseStep 1919047 = 2878571) B2878571
theorem B2246777 : Blo 662308 2246777 := bstep (se 2 (by rfl) ⟨842541, by rfl⟩ : syracuseStep 2246777 = 1685083) B1685083
theorem B1067239 : Blo 662308 1067239 := bstep (se 1 (by rfl) ⟨800429, by rfl⟩ : syracuseStep 1067239 = 1600859) B1600859
theorem B1886561 : Blo 662308 1886561 := bstep (se 2 (by rfl) ⟨707460, by rfl⟩ : syracuseStep 1886561 = 1414921) B1414921
theorem B2247209 : Blo 662308 2247209 := bstep (se 2 (by rfl) ⟨842703, by rfl⟩ : syracuseStep 2247209 = 1685407) B1685407
theorem B61524683 : Blo 662308 61524683 := bstep (se 1 (by rfl) ⟨46143512, by rfl⟩ : syracuseStep 61524683 = 92287025) B92287025
theorem B2837359 : Blo 662308 2837359 := bstep (se 1 (by rfl) ⟨2128019, by rfl⟩ : syracuseStep 2837359 = 4256039) B4256039
theorem B1493927 : Blo 662308 1493927 := bstep (se 1 (by rfl) ⟨1120445, by rfl⟩ : syracuseStep 1493927 = 2240891) B2240891
theorem B1493999 : Blo 662308 1493999 := bstep (se 1 (by rfl) ⟨1120499, by rfl⟩ : syracuseStep 1493999 = 2240999) B2240999
theorem B3591533 : Blo 662308 3591533 := bstep (se 3 (by rfl) ⟨673412, by rfl⟩ : syracuseStep 3591533 = 1346825) B1346825
theorem B4312859 : Blo 662308 4312859 := bstep (se 1 (by rfl) ⟨3234644, by rfl⟩ : syracuseStep 4312859 = 6469289) B6469289
theorem B1494881 : Blo 662308 1494881 := bstep (se 2 (by rfl) ⟨560580, by rfl⟩ : syracuseStep 1494881 = 1121161) B1121161
theorem B7164767 : Blo 662308 7164767 := bstep (se 1 (by rfl) ⟨5373575, by rfl⟩ : syracuseStep 7164767 = 10747151) B10747151
theorem B4052227 : Blo 662308 4052227 := bstep (se 1 (by rfl) ⟨3039170, by rfl⟩ : syracuseStep 4052227 = 6078341) B6078341
theorem B3364415 : Blo 662308 3364415 := bstep (se 1 (by rfl) ⟨2523311, by rfl⟩ : syracuseStep 3364415 = 5046623) B5046623
theorem B1889887 : Blo 662308 1889887 := bstep (se 1 (by rfl) ⟨1417415, by rfl⟩ : syracuseStep 1889887 = 2834831) B2834831
theorem B1365727 : Blo 662308 1365727 := bstep (se 1 (by rfl) ⟨1024295, by rfl⟩ : syracuseStep 1365727 = 2048591) B2048591
theorem B1497761 : Blo 662308 1497761 := bstep (se 2 (by rfl) ⟨561660, by rfl⟩ : syracuseStep 1497761 = 1123321) B1123321
theorem B9329627 : Blo 662308 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B374202227 : Blo 662308 374202227 := bstep (se 1 (by rfl) ⟨280651670, by rfl⟩ : syracuseStep 374202227 = 561303341) B561303341
theorem B745375 : Blo 662308 745375 := bstep (se 1 (by rfl) ⟨559031, by rfl⟩ : syracuseStep 745375 = 1118063) B1118063
theorem B745519 : Blo 662308 745519 := bstep (se 1 (by rfl) ⟨559139, by rfl⟩ : syracuseStep 745519 = 1118279) B1118279
theorem B3235895 : Blo 662308 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B5038361 : Blo 662308 5038361 := bstep (se 2 (by rfl) ⟨1889385, by rfl⟩ : syracuseStep 5038361 = 3778771) B3778771
theorem B745951 : Blo 662308 745951 := bstep (se 1 (by rfl) ⟨559463, by rfl⟩ : syracuseStep 745951 = 1118927) B1118927
theorem B7988321 : Blo 662308 7988321 := bstep (se 2 (by rfl) ⟨2995620, by rfl⟩ : syracuseStep 7988321 = 5991241) B5991241
theorem B8087177 : Blo 662308 8087177 := bstep (se 2 (by rfl) ⟨3032691, by rfl⟩ : syracuseStep 8087177 = 6065383) B6065383
theorem B747247 : Blo 662308 747247 := bstep (se 1 (by rfl) ⟨560435, by rfl⟩ : syracuseStep 747247 = 1120871) B1120871
theorem B2124073 : Blo 662308 2124073 := bstep (se 2 (by rfl) ⟨796527, by rfl⟩ : syracuseStep 2124073 = 1593055) B1593055
theorem B18180713 : Blo 662308 18180713 := bstep (se 2 (by rfl) ⟨6817767, by rfl⟩ : syracuseStep 18180713 = 13635535) B13635535
theorem B1600361 : Blo 662308 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B748399 : Blo 662308 748399 := bstep (se 1 (by rfl) ⟨561299, by rfl⟩ : syracuseStep 748399 = 1122599) B1122599
theorem B5041277 : Blo 662308 5041277 := bstep (se 3 (by rfl) ⟨945239, by rfl⟩ : syracuseStep 5041277 = 1890479) B1890479
theorem B2125919 : Blo 662308 2125919 := bstep (se 1 (by rfl) ⟨1594439, by rfl⟩ : syracuseStep 2125919 = 3188879) B3188879
theorem B7565561 : Blo 662308 7565561 := bstep (se 2 (by rfl) ⟨2837085, by rfl⟩ : syracuseStep 7565561 = 5674171) B5674171
theorem B18149831 : Blo 662308 18149831 := bstep (se 1 (by rfl) ⟨13612373, by rfl⟩ : syracuseStep 18149831 = 27224747) B27224747
theorem B2519531 : Blo 662308 2519531 := bstep (se 1 (by rfl) ⟨1889648, by rfl⟩ : syracuseStep 2519531 = 3779297) B3779297
theorem B1700399 : Blo 662308 1700399 := bstep (se 1 (by rfl) ⟨1275299, by rfl⟩ : syracuseStep 1700399 = 2550599) B2550599
theorem B2519819 : Blo 662308 2519819 := bstep (se 1 (by rfl) ⟨1889864, by rfl⟩ : syracuseStep 2519819 = 3779729) B3779729
theorem B4323437 : Blo 662308 4323437 := bstep (se 3 (by rfl) ⟨810644, by rfl⟩ : syracuseStep 4323437 = 1621289) B1621289
theorem B7305817 : Blo 662308 7305817 := bstep (se 2 (by rfl) ⟨2739681, by rfl⟩ : syracuseStep 7305817 = 5479363) B5479363
theorem B19102351 : Blo 662308 19102351 := bstep (se 1 (by rfl) ⟨14326763, by rfl⟩ : syracuseStep 19102351 = 28653527) B28653527
theorem B4619105 : Blo 662308 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B2128943 : Blo 662308 2128943 := bstep (se 1 (by rfl) ⟨1596707, by rfl⟩ : syracuseStep 2128943 = 3193415) B3193415
theorem B4030087 : Blo 662308 4030087 := bstep (se 1 (by rfl) ⟨3022565, by rfl⟩ : syracuseStep 4030087 = 6045131) B6045131
theorem B7176185 : Blo 662308 7176185 := bstep (se 2 (by rfl) ⟨2691069, by rfl⟩ : syracuseStep 7176185 = 5382139) B5382139
theorem B4261679 : Blo 662308 4261679 := bstep (se 1 (by rfl) ⟨3196259, by rfl⟩ : syracuseStep 4261679 = 6392519) B6392519
theorem B2394355 : Blo 662308 2394355 := bstep (se 1 (by rfl) ⟨1795766, by rfl⟩ : syracuseStep 2394355 = 3591533) B3591533
theorem B2558729 : Blo 662308 2558729 := bstep (se 2 (by rfl) ⟨959523, by rfl⟩ : syracuseStep 2558729 = 1919047) B1919047
theorem B5115727 : Blo 662308 5115727 := bstep (se 1 (by rfl) ⟨3836795, by rfl⟩ : syracuseStep 5115727 = 7673591) B7673591
theorem B1708199 : Blo 662308 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B662783 : Blo 662308 662783 := bstep (se 1 (by rfl) ⟨497087, by rfl⟩ : syracuseStep 662783 = 994175) B994175
theorem B1121627 : Blo 662308 1121627 := bstep (se 1 (by rfl) ⟨841220, by rfl⟩ : syracuseStep 1121627 = 1682441) B1682441
theorem B662943 : Blo 662308 662943 := bstep (se 1 (by rfl) ⟨497207, by rfl⟩ : syracuseStep 662943 = 994415) B994415
theorem B662975 : Blo 662308 662975 := bstep (se 1 (by rfl) ⟨497231, by rfl⟩ : syracuseStep 662975 = 994463) B994463
theorem B663007 : Blo 662308 663007 := bstep (se 1 (by rfl) ⟨497255, by rfl⟩ : syracuseStep 663007 = 994511) B994511
theorem B24879005 : Blo 662308 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B1417279 : Blo 662308 1417279 := bstep (se 1 (by rfl) ⟨1062959, by rfl⟩ : syracuseStep 1417279 = 2125919) B2125919
theorem B663775 : Blo 662308 663775 := bstep (se 1 (by rfl) ⟨497831, by rfl⟩ : syracuseStep 663775 = 995663) B995663
theorem B663803 : Blo 662308 663803 := bstep (se 1 (by rfl) ⟨497852, by rfl⟩ : syracuseStep 663803 = 995705) B995705
theorem B12099887 : Blo 662308 12099887 := bstep (se 1 (by rfl) ⟨9074915, by rfl⟩ : syracuseStep 12099887 = 18149831) B18149831
theorem B1679687 : Blo 662308 1679687 := bstep (se 1 (by rfl) ⟨1259765, by rfl⟩ : syracuseStep 1679687 = 2519531) B2519531
theorem B663879 : Blo 662308 663879 := bstep (se 1 (by rfl) ⟨497909, by rfl⟩ : syracuseStep 663879 = 995819) B995819
theorem B1679879 : Blo 662308 1679879 := bstep (se 1 (by rfl) ⟨1259909, by rfl⟩ : syracuseStep 1679879 = 2519819) B2519819
theorem B664111 : Blo 662308 664111 := bstep (se 1 (by rfl) ⟨498083, by rfl⟩ : syracuseStep 664111 = 996167) B996167
theorem B664315 : Blo 662308 664315 := bstep (se 1 (by rfl) ⟨498236, by rfl⟩ : syracuseStep 664315 = 996473) B996473
theorem B9741089 : Blo 662308 9741089 := bstep (se 2 (by rfl) ⟨3652908, by rfl⟩ : syracuseStep 9741089 = 7305817) B7305817
theorem B664423 : Blo 662308 664423 := bstep (se 1 (by rfl) ⟨498317, by rfl⟩ : syracuseStep 664423 = 996635) B996635
theorem B25469801 : Blo 662308 25469801 := bstep (se 2 (by rfl) ⟨9551175, by rfl⟩ : syracuseStep 25469801 = 19102351) B19102351
theorem B664815 : Blo 662308 664815 := bstep (se 1 (by rfl) ⟨498611, by rfl⟩ : syracuseStep 664815 = 997223) B997223
theorem B12789029 : Blo 662308 12789029 := bstep (se 4 (by rfl) ⟨1198971, by rfl⟩ : syracuseStep 12789029 = 2397943) B2397943
theorem B664991 : Blo 662308 664991 := bstep (se 1 (by rfl) ⟨498743, by rfl⟩ : syracuseStep 664991 = 997487) B997487
theorem B1123807 : Blo 662308 1123807 := bstep (se 1 (by rfl) ⟨842855, by rfl⟩ : syracuseStep 1123807 = 1685711) B1685711
theorem B2237921 : Blo 662308 2237921 := bstep (se 2 (by rfl) ⟨839220, by rfl⟩ : syracuseStep 2237921 = 1678441) B1678441
theorem B1419295 : Blo 662308 1419295 := bstep (se 1 (by rfl) ⟨1064471, by rfl⟩ : syracuseStep 1419295 = 2128943) B2128943
theorem B665807 : Blo 662308 665807 := bstep (se 1 (by rfl) ⟨499355, by rfl⟩ : syracuseStep 665807 = 998711) B998711
theorem B665831 : Blo 662308 665831 := bstep (se 1 (by rfl) ⟨499373, by rfl⟩ : syracuseStep 665831 = 998747) B998747
theorem B665855 : Blo 662308 665855 := bstep (se 1 (by rfl) ⟨499391, by rfl⟩ : syracuseStep 665855 = 998783) B998783
theorem B38381849 : Blo 662308 38381849 := bstep (se 2 (by rfl) ⟨14393193, by rfl⟩ : syracuseStep 38381849 = 28786387) B28786387
theorem B665927 : Blo 662308 665927 := bstep (se 1 (by rfl) ⟨499445, by rfl⟩ : syracuseStep 665927 = 998891) B998891
theorem B993833 : Blo 662308 993833 := bstep (se 2 (by rfl) ⟨372687, by rfl⟩ : syracuseStep 993833 = 745375) B745375
theorem B797239 : Blo 662308 797239 := bstep (se 1 (by rfl) ⟨597929, by rfl⟩ : syracuseStep 797239 = 1195859) B1195859
theorem B666203 : Blo 662308 666203 := bstep (se 1 (by rfl) ⟨499652, by rfl⟩ : syracuseStep 666203 = 999305) B999305
theorem B3025555 : Blo 662308 3025555 := bstep (se 1 (by rfl) ⟨2269166, by rfl⟩ : syracuseStep 3025555 = 4538333) B4538333
theorem B994025 : Blo 662308 994025 := bstep (se 2 (by rfl) ⟨372759, by rfl⟩ : syracuseStep 994025 = 745519) B745519
theorem B994031 : Blo 662308 994031 := bstep (se 1 (by rfl) ⟨745523, by rfl⟩ : syracuseStep 994031 = 1491047) B1491047
theorem B994331 : Blo 662308 994331 := bstep (se 1 (by rfl) ⟨745748, by rfl⟩ : syracuseStep 994331 = 1491497) B1491497
theorem B3190013 : Blo 662308 3190013 := bstep (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) B1196255
theorem B994601 : Blo 662308 994601 := bstep (se 2 (by rfl) ⟨372975, by rfl⟩ : syracuseStep 994601 = 745951) B745951
theorem B994799 : Blo 662308 994799 := bstep (se 1 (by rfl) ⟨746099, by rfl⟩ : syracuseStep 994799 = 1492199) B1492199
theorem B995099 : Blo 662308 995099 := bstep (se 1 (by rfl) ⟨746324, by rfl⟩ : syracuseStep 995099 = 1492649) B1492649
theorem B1257707 : Blo 662308 1257707 := bstep (se 1 (by rfl) ⟨943280, by rfl⟩ : syracuseStep 1257707 = 1886561) B1886561
theorem B995951 : Blo 662308 995951 := bstep (se 1 (by rfl) ⟨746963, by rfl⟩ : syracuseStep 995951 = 1493927) B1493927
theorem B995999 : Blo 662308 995999 := bstep (se 1 (by rfl) ⟨746999, by rfl⟩ : syracuseStep 995999 = 1493999) B1493999
theorem B1684415 : Blo 662308 1684415 := bstep (se 1 (by rfl) ⟨1263311, by rfl⟩ : syracuseStep 1684415 = 2526623) B2526623
theorem B996329 : Blo 662308 996329 := bstep (se 2 (by rfl) ⟨373623, by rfl⟩ : syracuseStep 996329 = 747247) B747247
theorem B996587 : Blo 662308 996587 := bstep (se 1 (by rfl) ⟨747440, by rfl⟩ : syracuseStep 996587 = 1494881) B1494881
theorem B2832097 : Blo 662308 2832097 := bstep (se 2 (by rfl) ⟨1062036, by rfl⟩ : syracuseStep 2832097 = 2124073) B2124073
theorem B2242943 : Blo 662308 2242943 := bstep (se 1 (by rfl) ⟨1682207, by rfl⟩ : syracuseStep 2242943 = 3364415) B3364415
theorem B3783145 : Blo 662308 3783145 := bstep (se 2 (by rfl) ⟨1418679, by rfl⟩ : syracuseStep 3783145 = 2837359) B2837359
theorem B997865 : Blo 662308 997865 := bstep (se 2 (by rfl) ⟨374199, by rfl⟩ : syracuseStep 997865 = 748399) B748399
theorem B998507 : Blo 662308 998507 := bstep (se 1 (by rfl) ⟨748880, by rfl⟩ : syracuseStep 998507 = 1497761) B1497761
theorem B10796975 : Blo 662308 10796975 := bstep (se 1 (by rfl) ⟨8097731, by rfl⟩ : syracuseStep 10796975 = 16195463) B16195463
theorem B3358907 : Blo 662308 3358907 := bstep (se 1 (by rfl) ⟨2519180, by rfl⟩ : syracuseStep 3358907 = 5038361) B5038361
theorem B5325547 : Blo 662308 5325547 := bstep (se 1 (by rfl) ⟨3994160, by rfl⟩ : syracuseStep 5325547 = 7988321) B7988321
theorem B1491839 : Blo 662308 1491839 := bstep (se 1 (by rfl) ⟨1118879, by rfl⟩ : syracuseStep 1491839 = 2237759) B2237759
theorem B5391451 : Blo 662308 5391451 := bstep (se 1 (by rfl) ⟨4043588, by rfl⟩ : syracuseStep 5391451 = 8087177) B8087177
theorem B2278583 : Blo 662308 2278583 := bstep (se 1 (by rfl) ⟨1708937, by rfl⟩ : syracuseStep 2278583 = 3417875) B3417875
theorem B1492307 : Blo 662308 1492307 := bstep (se 1 (by rfl) ⟨1119230, by rfl⟩ : syracuseStep 1492307 = 2238461) B2238461
theorem B18138887 : Blo 662308 18138887 := bstep (se 1 (by rfl) ⟨13604165, by rfl⟩ : syracuseStep 18138887 = 27208331) B27208331
theorem B1066907 : Blo 662308 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B3360851 : Blo 662308 3360851 := bstep (se 1 (by rfl) ⟨2520638, by rfl⟩ : syracuseStep 3360851 = 5041277) B5041277
theorem B1820969 : Blo 662308 1820969 := bstep (se 2 (by rfl) ⟨682863, by rfl⟩ : syracuseStep 1820969 = 1365727) B1365727
theorem B1133599 : Blo 662308 1133599 := bstep (se 1 (by rfl) ⟨850199, by rfl⟩ : syracuseStep 1133599 = 1700399) B1700399
theorem B1494089 : Blo 662308 1494089 := bstep (se 2 (by rfl) ⟨560283, by rfl⟩ : syracuseStep 1494089 = 1120567) B1120567
theorem B1495817 : Blo 662308 1495817 := bstep (se 2 (by rfl) ⟨560931, by rfl⟩ : syracuseStep 1495817 = 1121863) B1121863
theorem B997872605 : Blo 662308 997872605 := bstep (se 3 (by rfl) ⟨187101113, by rfl⟩ : syracuseStep 997872605 = 374202227) B374202227
theorem B5691941 : Blo 662308 5691941 := bstep (se 4 (by rfl) ⟨533619, by rfl⟩ : syracuseStep 5691941 = 1067239) B1067239
theorem B1497851 : Blo 662308 1497851 := bstep (se 1 (by rfl) ⟨1123388, by rfl⟩ : syracuseStep 1497851 = 2246777) B2246777
theorem B1498139 : Blo 662308 1498139 := bstep (se 1 (by rfl) ⟨1123604, by rfl⟩ : syracuseStep 1498139 = 2247209) B2247209
theorem B41016455 : Blo 662308 41016455 := bstep (se 1 (by rfl) ⟨30762341, by rfl⟩ : syracuseStep 41016455 = 61524683) B61524683
theorem B3366683 : Blo 662308 3366683 := bstep (se 1 (by rfl) ⟨2525012, by rfl⟩ : syracuseStep 3366683 = 5050025) B5050025
theorem B4546655 : Blo 662308 4546655 := bstep (se 1 (by rfl) ⟨3409991, by rfl⟩ : syracuseStep 4546655 = 6819983) B6819983
theorem B3367007 : Blo 662308 3367007 := bstep (se 1 (by rfl) ⟨2525255, by rfl⟩ : syracuseStep 3367007 = 5050511) B5050511
theorem B4776511 : Blo 662308 4776511 := bstep (se 1 (by rfl) ⟨3582383, by rfl⟩ : syracuseStep 4776511 = 7164767) B7164767
theorem B746239 : Blo 662308 746239 := bstep (se 1 (by rfl) ⟨559679, by rfl⟩ : syracuseStep 746239 = 1119359) B1119359
theorem B3367817 : Blo 662308 3367817 := bstep (se 2 (by rfl) ⟨1262931, by rfl⟩ : syracuseStep 3367817 = 2525863) B2525863
theorem B4547593 : Blo 662308 4547593 := bstep (se 2 (by rfl) ⟨1705347, by rfl⟩ : syracuseStep 4547593 = 3410695) B3410695
theorem B1598591 : Blo 662308 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B747931 : Blo 662308 747931 := bstep (se 1 (by rfl) ⟨560948, by rfl⟩ : syracuseStep 747931 = 1121897) B1121897
theorem B2157263 : Blo 662308 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B12938291 : Blo 662308 12938291 := bstep (se 1 (by rfl) ⟨9703718, by rfl⟩ : syracuseStep 12938291 = 19407437) B19407437
theorem B748795 : Blo 662308 748795 := bstep (se 1 (by rfl) ⟨561596, by rfl⟩ : syracuseStep 748795 = 1123193) B1123193
theorem B749083 : Blo 662308 749083 := bstep (se 1 (by rfl) ⟨561812, by rfl⟩ : syracuseStep 749083 = 1123625) B1123625
theorem B5402969 : Blo 662308 5402969 := bstep (se 2 (by rfl) ⟨2026113, by rfl⟩ : syracuseStep 5402969 = 4052227) B4052227
theorem B12120475 : Blo 662308 12120475 := bstep (se 1 (by rfl) ⟨9090356, by rfl⟩ : syracuseStep 12120475 = 18180713) B18180713
theorem B2519849 : Blo 662308 2519849 := bstep (se 2 (by rfl) ⟨944943, by rfl⟩ : syracuseStep 2519849 = 1889887) B1889887
theorem B5043707 : Blo 662308 5043707 := bstep (se 1 (by rfl) ⟨3782780, by rfl⟩ : syracuseStep 5043707 = 7565561) B7565561
theorem B3372839 : Blo 662308 3372839 := bstep (se 1 (by rfl) ⟨2529629, by rfl⟩ : syracuseStep 3372839 = 5059259) B5059259
theorem B61306703 : Blo 662308 61306703 := bstep (se 1 (by rfl) ⟨45980027, by rfl⟩ : syracuseStep 61306703 = 91960055) B91960055
theorem B3373163 : Blo 662308 3373163 := bstep (se 1 (by rfl) ⟨2529872, by rfl⟩ : syracuseStep 3373163 = 5059745) B5059745
theorem B2882291 : Blo 662308 2882291 := bstep (se 1 (by rfl) ⟨2161718, by rfl⟩ : syracuseStep 2882291 = 4323437) B4323437
theorem B2390795 : Blo 662308 2390795 := bstep (se 1 (by rfl) ⟨1793096, by rfl⟩ : syracuseStep 2390795 = 3586193) B3586193
theorem B24280211 : Blo 662308 24280211 := bstep (se 1 (by rfl) ⟨18210158, by rfl⟩ : syracuseStep 24280211 = 36420317) B36420317
theorem B3079403 : Blo 662308 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B11500957 : Blo 662308 11500957 := bstep (se 3 (by rfl) ⟨2156429, by rfl⟩ : syracuseStep 11500957 = 4312859) B4312859
theorem B5373449 : Blo 662308 5373449 := bstep (se 2 (by rfl) ⟨2015043, by rfl⟩ : syracuseStep 5373449 = 4030087) B4030087
theorem B2391947 : Blo 662308 2391947 := bstep (se 1 (by rfl) ⟨1793960, by rfl⟩ : syracuseStep 2391947 = 3587921) B3587921
theorem B4784123 : Blo 662308 4784123 := bstep (se 1 (by rfl) ⟨3588092, by rfl⟩ : syracuseStep 4784123 = 7176185) B7176185
theorem B12092591 : Blo 662308 12092591 := bstep (se 1 (by rfl) ⟨9069443, by rfl⟩ : syracuseStep 12092591 = 18138887) B18138887
theorem B6063457 : Blo 662308 6063457 := bstep (se 2 (by rfl) ⟨2273796, by rfl⟩ : syracuseStep 6063457 = 4547593) B4547593
theorem B1213979 : Blo 662308 1213979 := bstep (se 1 (by rfl) ⟨910484, by rfl⟩ : syracuseStep 1213979 = 1820969) B1820969
theorem B1705819 : Blo 662308 1705819 := bstep (se 1 (by rfl) ⟨1279364, by rfl⟩ : syracuseStep 1705819 = 2558729) B2558729
theorem B1511465 : Blo 662308 1511465 := bstep (se 2 (by rfl) ⟨566799, by rfl⟩ : syracuseStep 1511465 = 1133599) B1133599
theorem B6820969 : Blo 662308 6820969 := bstep (se 2 (by rfl) ⟨2557863, by rfl⟩ : syracuseStep 6820969 = 5115727) B5115727
theorem B16586003 : Blo 662308 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B8066591 : Blo 662308 8066591 := bstep (se 1 (by rfl) ⟨6049943, by rfl⟩ : syracuseStep 8066591 = 12099887) B12099887
theorem B1119791 : Blo 662308 1119791 := bstep (se 1 (by rfl) ⟨839843, by rfl⟩ : syracuseStep 1119791 = 1679687) B1679687
theorem B1119919 : Blo 662308 1119919 := bstep (se 1 (by rfl) ⟨839939, by rfl⟩ : syracuseStep 1119919 = 1679879) B1679879
theorem B6494059 : Blo 662308 6494059 := bstep (se 1 (by rfl) ⟨4870544, by rfl⟩ : syracuseStep 6494059 = 9741089) B9741089
theorem B16160633 : Blo 662308 16160633 := bstep (se 2 (by rfl) ⟨6060237, by rfl⟩ : syracuseStep 16160633 = 12120475) B12120475
theorem B16979867 : Blo 662308 16979867 := bstep (se 1 (by rfl) ⟨12734900, by rfl⟩ : syracuseStep 16979867 = 25469801) B25469801
theorem B8526019 : Blo 662308 8526019 := bstep (se 1 (by rfl) ⟨6394514, by rfl⟩ : syracuseStep 8526019 = 12789029) B12789029
theorem B662555 : Blo 662308 662555 := bstep (se 1 (by rfl) ⟨496916, by rfl⟩ : syracuseStep 662555 = 993833) B993833
theorem B662683 : Blo 662308 662683 := bstep (se 1 (by rfl) ⟨497012, by rfl⟩ : syracuseStep 662683 = 994025) B994025
theorem B662687 : Blo 662308 662687 := bstep (se 1 (by rfl) ⟨497015, by rfl⟩ : syracuseStep 662687 = 994031) B994031
theorem B662887 : Blo 662308 662887 := bstep (se 1 (by rfl) ⟨497165, by rfl⟩ : syracuseStep 662887 = 994331) B994331
theorem B8625527 : Blo 662308 8625527 := bstep (se 1 (by rfl) ⟨6469145, by rfl⟩ : syracuseStep 8625527 = 12938291) B12938291
theorem B663067 : Blo 662308 663067 := bstep (se 1 (by rfl) ⟨497300, by rfl⟩ : syracuseStep 663067 = 994601) B994601
theorem B3776129 : Blo 662308 3776129 := bstep (se 2 (by rfl) ⟨1416048, by rfl⟩ : syracuseStep 3776129 = 2832097) B2832097
theorem B663199 : Blo 662308 663199 := bstep (se 1 (by rfl) ⟨497399, by rfl⟩ : syracuseStep 663199 = 994799) B994799
theorem B663399 : Blo 662308 663399 := bstep (se 1 (by rfl) ⟨497549, by rfl⟩ : syracuseStep 663399 = 995099) B995099
theorem B663967 : Blo 662308 663967 := bstep (se 1 (by rfl) ⟨497975, by rfl⟩ : syracuseStep 663967 = 995951) B995951
theorem B663999 : Blo 662308 663999 := bstep (se 1 (by rfl) ⟨497999, by rfl⟩ : syracuseStep 663999 = 995999) B995999
theorem B1679899 : Blo 662308 1679899 := bstep (se 1 (by rfl) ⟨1259924, by rfl⟩ : syracuseStep 1679899 = 2519849) B2519849
theorem B1122943 : Blo 662308 1122943 := bstep (se 1 (by rfl) ⟨842207, by rfl⟩ : syracuseStep 1122943 = 1684415) B1684415
theorem B664219 : Blo 662308 664219 := bstep (se 1 (by rfl) ⟨498164, by rfl⟩ : syracuseStep 664219 = 996329) B996329
theorem B664391 : Blo 662308 664391 := bstep (se 1 (by rfl) ⟨498293, by rfl⟩ : syracuseStep 664391 = 996587) B996587
theorem B40871135 : Blo 662308 40871135 := bstep (se 1 (by rfl) ⟨30653351, by rfl⟩ : syracuseStep 40871135 = 61306703) B61306703
theorem B665243 : Blo 662308 665243 := bstep (se 1 (by rfl) ⟨498932, by rfl⟩ : syracuseStep 665243 = 997865) B997865
theorem B665671 : Blo 662308 665671 := bstep (se 1 (by rfl) ⟨499253, by rfl⟩ : syracuseStep 665671 = 998507) B998507
theorem B3582299 : Blo 662308 3582299 := bstep (se 1 (by rfl) ⟨2686724, by rfl⟩ : syracuseStep 3582299 = 5373449) B5373449
theorem B12757661 : Blo 662308 12757661 := bstep (se 3 (by rfl) ⟨2392061, by rfl⟩ : syracuseStep 12757661 = 4784123) B4784123
theorem B2239271 : Blo 662308 2239271 := bstep (se 1 (by rfl) ⟨1679453, by rfl⟩ : syracuseStep 2239271 = 3358907) B3358907
theorem B994559 : Blo 662308 994559 := bstep (se 1 (by rfl) ⟨745919, by rfl⟩ : syracuseStep 994559 = 1491839) B1491839
theorem B3353885 : Blo 662308 3353885 := bstep (se 3 (by rfl) ⟨628853, by rfl⟩ : syracuseStep 3353885 = 1257707) B1257707
theorem B6368681 : Blo 662308 6368681 := bstep (se 2 (by rfl) ⟨2388255, by rfl⟩ : syracuseStep 6368681 = 4776511) B4776511
theorem B1519055 : Blo 662308 1519055 := bstep (se 1 (by rfl) ⟨1139291, by rfl⟩ : syracuseStep 1519055 = 2278583) B2278583
theorem B994871 : Blo 662308 994871 := bstep (se 1 (by rfl) ⟨746153, by rfl⟩ : syracuseStep 994871 = 1492307) B1492307
theorem B994985 : Blo 662308 994985 := bstep (se 2 (by rfl) ⟨373119, by rfl⟩ : syracuseStep 994985 = 746239) B746239
theorem B2240567 : Blo 662308 2240567 := bstep (se 1 (by rfl) ⟨1680425, by rfl⟩ : syracuseStep 2240567 = 3360851) B3360851
theorem B7188601 : Blo 662308 7188601 := bstep (se 2 (by rfl) ⟨2695725, by rfl⟩ : syracuseStep 7188601 = 5391451) B5391451
theorem B996059 : Blo 662308 996059 := bstep (se 1 (by rfl) ⟨747044, by rfl⟩ : syracuseStep 996059 = 1494089) B1494089
theorem B3192473 : Blo 662308 3192473 := bstep (se 2 (by rfl) ⟨1197177, by rfl⟩ : syracuseStep 3192473 = 2394355) B2394355
theorem B997211 : Blo 662308 997211 := bstep (se 1 (by rfl) ⟨747908, by rfl⟩ : syracuseStep 997211 = 1495817) B1495817
theorem B997241 : Blo 662308 997241 := bstep (se 2 (by rfl) ⟨373965, by rfl⟩ : syracuseStep 997241 = 747931) B747931
theorem B1062985 : Blo 662308 1062985 := bstep (se 2 (by rfl) ⟨398619, by rfl⟩ : syracuseStep 1062985 = 797239) B797239
theorem B998393 : Blo 662308 998393 := bstep (se 2 (by rfl) ⟨374397, by rfl⟩ : syracuseStep 998393 = 748795) B748795
theorem B998567 : Blo 662308 998567 := bstep (se 1 (by rfl) ⟨748925, by rfl⟩ : syracuseStep 998567 = 1497851) B1497851
theorem B998759 : Blo 662308 998759 := bstep (se 1 (by rfl) ⟨749069, by rfl⟩ : syracuseStep 998759 = 1498139) B1498139
theorem B998777 : Blo 662308 998777 := bstep (se 2 (by rfl) ⟨374541, by rfl⟩ : syracuseStep 998777 = 749083) B749083
theorem B27344303 : Blo 662308 27344303 := bstep (se 1 (by rfl) ⟨20508227, by rfl⟩ : syracuseStep 27344303 = 41016455) B41016455
theorem B2244455 : Blo 662308 2244455 := bstep (se 1 (by rfl) ⟨1683341, by rfl⟩ : syracuseStep 2244455 = 3366683) B3366683
theorem B3031103 : Blo 662308 3031103 := bstep (se 1 (by rfl) ⟨2273327, by rfl⟩ : syracuseStep 3031103 = 4546655) B4546655
theorem B2244671 : Blo 662308 2244671 := bstep (se 1 (by rfl) ⟨1683503, by rfl⟩ : syracuseStep 2244671 = 3367007) B3367007
theorem B2245211 : Blo 662308 2245211 := bstep (se 1 (by rfl) ⟨1683908, by rfl⟩ : syracuseStep 2245211 = 3367817) B3367817
theorem B1065727 : Blo 662308 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B1491947 : Blo 662308 1491947 := bstep (se 1 (by rfl) ⟨1118960, by rfl⟩ : syracuseStep 1491947 = 2237921) B2237921
theorem B7686109 : Blo 662308 7686109 := bstep (se 3 (by rfl) ⟨1441145, by rfl⟩ : syracuseStep 7686109 = 2882291) B2882291
theorem B3362471 : Blo 662308 3362471 := bstep (se 1 (by rfl) ⟨2521853, by rfl⟩ : syracuseStep 3362471 = 5043707) B5043707
theorem B2248559 : Blo 662308 2248559 := bstep (se 1 (by rfl) ⟨1686419, by rfl⟩ : syracuseStep 2248559 = 3372839) B3372839
theorem B2248775 : Blo 662308 2248775 := bstep (se 1 (by rfl) ⟨1686581, by rfl⟩ : syracuseStep 2248775 = 3373163) B3373163
theorem B1495295 : Blo 662308 1495295 := bstep (se 1 (by rfl) ⟨1121471, by rfl⟩ : syracuseStep 1495295 = 2242943) B2242943
theorem B1593863 : Blo 662308 1593863 := bstep (se 1 (by rfl) ⟨1195397, by rfl⟩ : syracuseStep 1593863 = 2390795) B2390795
theorem B2052935 : Blo 662308 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B1594631 : Blo 662308 1594631 := bstep (se 1 (by rfl) ⟨1195973, by rfl⟩ : syracuseStep 1594631 = 2391947) B2391947
theorem B7197983 : Blo 662308 7197983 := bstep (se 1 (by rfl) ⟨5398487, by rfl⟩ : syracuseStep 7197983 = 10796975) B10796975
theorem B1889705 : Blo 662308 1889705 := bstep (se 2 (by rfl) ⟨708639, by rfl⟩ : syracuseStep 1889705 = 1417279) B1417279
theorem B7100729 : Blo 662308 7100729 := bstep (se 2 (by rfl) ⟨2662773, by rfl⟩ : syracuseStep 7100729 = 5325547) B5325547
theorem B2841119 : Blo 662308 2841119 := bstep (se 1 (by rfl) ⟨2130839, by rfl⟩ : syracuseStep 2841119 = 4261679) B4261679
theorem B711271 : Blo 662308 711271 := bstep (se 1 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 711271 = 1066907) B1066907
theorem B1498409 : Blo 662308 1498409 := bstep (se 2 (by rfl) ⟨561903, by rfl⟩ : syracuseStep 1498409 = 1123807) B1123807
theorem B1892393 : Blo 662308 1892393 := bstep (se 2 (by rfl) ⟨709647, by rfl⟩ : syracuseStep 1892393 = 1419295) B1419295
theorem B1138799 : Blo 662308 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B64545173 : Blo 662308 64545173 := bstep (se 6 (by rfl) ⟨1512777, by rfl⟩ : syracuseStep 64545173 = 3025555) B3025555
theorem B665248403 : Blo 662308 665248403 := bstep (se 1 (by rfl) ⟨498936302, by rfl⟩ : syracuseStep 665248403 = 997872605) B997872605
theorem B3794627 : Blo 662308 3794627 := bstep (se 1 (by rfl) ⟨2845970, by rfl⟩ : syracuseStep 3794627 = 5691941) B5691941
theorem B747751 : Blo 662308 747751 := bstep (se 1 (by rfl) ⟨560813, by rfl⟩ : syracuseStep 747751 = 1121627) B1121627
theorem B25587899 : Blo 662308 25587899 := bstep (se 1 (by rfl) ⟨19190924, by rfl⟩ : syracuseStep 25587899 = 38381849) B38381849
theorem B1438175 : Blo 662308 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B2126675 : Blo 662308 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B3601979 : Blo 662308 3601979 := bstep (se 1 (by rfl) ⟨2701484, by rfl⟩ : syracuseStep 3601979 = 5402969) B5402969
theorem B5044193 : Blo 662308 5044193 := bstep (se 2 (by rfl) ⟨1891572, by rfl⟩ : syracuseStep 5044193 = 3783145) B3783145
theorem B15334609 : Blo 662308 15334609 := bstep (se 2 (by rfl) ⟨5750478, by rfl⟩ : syracuseStep 15334609 = 11500957) B11500957
theorem B16186807 : Blo 662308 16186807 := bstep (se 1 (by rfl) ⟨12140105, by rfl⟩ : syracuseStep 16186807 = 24280211) B24280211
theorem B4030573 : Blo 662308 4030573 := bstep (se 3 (by rfl) ⟨755732, by rfl⟩ : syracuseStep 4030573 = 1511465) B1511465
theorem B8061727 : Blo 662308 8061727 := bstep (se 1 (by rfl) ⟨6046295, by rfl⟩ : syracuseStep 8061727 = 12092591) B12092591
theorem B3835133 : Blo 662308 3835133 := bstep (se 3 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 3835133 = 1438175) B1438175
theorem B5671133 : Blo 662308 5671133 := bstep (se 3 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 5671133 = 2126675) B2126675
theorem B5377727 : Blo 662308 5377727 := bstep (se 1 (by rfl) ⟨4033295, by rfl⟩ : syracuseStep 5377727 = 8066591) B8066591
theorem B43030115 : Blo 662308 43030115 := bstep (se 1 (by rfl) ⟨32272586, by rfl⟩ : syracuseStep 43030115 = 64545173) B64545173
theorem B12949109 : Blo 662308 12949109 := bstep (se 5 (by rfl) ⟨606989, by rfl⟩ : syracuseStep 12949109 = 1213979) B1213979
theorem B2529751 : Blo 662308 2529751 := bstep (se 1 (by rfl) ⟨1897313, by rfl⟩ : syracuseStep 2529751 = 3794627) B3794627
theorem B663039 : Blo 662308 663039 := bstep (se 1 (by rfl) ⟨497279, by rfl⟩ : syracuseStep 663039 = 994559) B994559
theorem B2235923 : Blo 662308 2235923 := bstep (se 1 (by rfl) ⟨1676942, by rfl⟩ : syracuseStep 2235923 = 3353885) B3353885
theorem B663247 : Blo 662308 663247 := bstep (se 1 (by rfl) ⟨497435, by rfl⟩ : syracuseStep 663247 = 994871) B994871
theorem B663323 : Blo 662308 663323 := bstep (se 1 (by rfl) ⟨497492, by rfl⟩ : syracuseStep 663323 = 994985) B994985
theorem B1417313 : Blo 662308 1417313 := bstep (se 2 (by rfl) ⟨531492, by rfl⟩ : syracuseStep 1417313 = 1062985) B1062985
theorem B664039 : Blo 662308 664039 := bstep (se 1 (by rfl) ⟨498029, by rfl⟩ : syracuseStep 664039 = 996059) B996059
theorem B2401319 : Blo 662308 2401319 := bstep (se 1 (by rfl) ⟨1800989, by rfl⟩ : syracuseStep 2401319 = 3601979) B3601979
theorem B664807 : Blo 662308 664807 := bstep (se 1 (by rfl) ⟨498605, by rfl⟩ : syracuseStep 664807 = 997211) B997211
theorem B664827 : Blo 662308 664827 := bstep (se 1 (by rfl) ⟨498620, by rfl⟩ : syracuseStep 664827 = 997241) B997241
theorem B665595 : Blo 662308 665595 := bstep (se 1 (by rfl) ⟨499196, by rfl⟩ : syracuseStep 665595 = 998393) B998393
theorem B665711 : Blo 662308 665711 := bstep (se 1 (by rfl) ⟨499283, by rfl⟩ : syracuseStep 665711 = 998567) B998567
theorem B665839 : Blo 662308 665839 := bstep (se 1 (by rfl) ⟨499379, by rfl⟩ : syracuseStep 665839 = 998759) B998759
theorem B665851 : Blo 662308 665851 := bstep (se 1 (by rfl) ⟨499388, by rfl⟩ : syracuseStep 665851 = 998777) B998777
theorem B18229535 : Blo 662308 18229535 := bstep (se 1 (by rfl) ⟨13672151, by rfl⟩ : syracuseStep 18229535 = 27344303) B27344303
theorem B994631 : Blo 662308 994631 := bstep (se 1 (by rfl) ⟨745973, by rfl⟩ : syracuseStep 994631 = 1491947) B1491947
theorem B2239865 : Blo 662308 2239865 := bstep (se 2 (by rfl) ⟨839949, by rfl⟩ : syracuseStep 2239865 = 1679899) B1679899
theorem B2241647 : Blo 662308 2241647 := bstep (se 1 (by rfl) ⟨1681235, by rfl⟩ : syracuseStep 2241647 = 3362471) B3362471
theorem B2274425 : Blo 662308 2274425 := bstep (se 2 (by rfl) ⟨852909, by rfl⟩ : syracuseStep 2274425 = 1705819) B1705819
theorem B996863 : Blo 662308 996863 := bstep (se 1 (by rfl) ⟨747647, by rfl⟩ : syracuseStep 996863 = 1495295) B1495295
theorem B997001 : Blo 662308 997001 := bstep (se 2 (by rfl) ⟨373875, by rfl⟩ : syracuseStep 997001 = 747751) B747751
theorem B1062575 : Blo 662308 1062575 := bstep (se 1 (by rfl) ⟨796931, by rfl⟩ : syracuseStep 1062575 = 1593863) B1593863
theorem B1063087 : Blo 662308 1063087 := bstep (se 1 (by rfl) ⟨797315, by rfl⟩ : syracuseStep 1063087 = 1594631) B1594631
theorem B4798655 : Blo 662308 4798655 := bstep (se 1 (by rfl) ⟨3598991, by rfl⟩ : syracuseStep 4798655 = 7197983) B7197983
theorem B1259803 : Blo 662308 1259803 := bstep (se 1 (by rfl) ⟨944852, by rfl⟩ : syracuseStep 1259803 = 1889705) B1889705
theorem B11319911 : Blo 662308 11319911 := bstep (se 1 (by rfl) ⟨8489933, by rfl⟩ : syracuseStep 11319911 = 16979867) B16979867
theorem B5683877 : Blo 662308 5683877 := bstep (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) B1065727
theorem B4733819 : Blo 662308 4733819 := bstep (se 1 (by rfl) ⟨3550364, by rfl⟩ : syracuseStep 4733819 = 7100729) B7100729
theorem B998939 : Blo 662308 998939 := bstep (se 1 (by rfl) ⟨749204, by rfl⟩ : syracuseStep 998939 = 1498409) B1498409
theorem B5750351 : Blo 662308 5750351 := bstep (se 1 (by rfl) ⟨4312763, by rfl⟩ : syracuseStep 5750351 = 8625527) B8625527
theorem B1261595 : Blo 662308 1261595 := bstep (se 1 (by rfl) ⟨946196, by rfl⟩ : syracuseStep 1261595 = 1892393) B1892393
theorem B9584801 : Blo 662308 9584801 := bstep (se 2 (by rfl) ⟨3594300, by rfl⟩ : syracuseStep 9584801 = 7188601) B7188601
theorem B443498935 : Blo 662308 443498935 := bstep (se 1 (by rfl) ⟨332624201, by rfl⟩ : syracuseStep 443498935 = 665248403) B665248403
theorem B27247423 : Blo 662308 27247423 := bstep (se 1 (by rfl) ⟨20435567, by rfl⟩ : syracuseStep 27247423 = 40871135) B40871135
theorem B9094625 : Blo 662308 9094625 := bstep (se 2 (by rfl) ⟨3410484, by rfl⟩ : syracuseStep 9094625 = 6820969) B6820969
theorem B8505107 : Blo 662308 8505107 := bstep (se 1 (by rfl) ⟨6378830, by rfl⟩ : syracuseStep 8505107 = 12757661) B12757661
theorem B1492847 : Blo 662308 1492847 := bstep (se 1 (by rfl) ⟨1119635, by rfl⟩ : syracuseStep 1492847 = 2239271) B2239271
theorem B1493225 : Blo 662308 1493225 := bstep (se 2 (by rfl) ⟨559959, by rfl⟩ : syracuseStep 1493225 = 1119919) B1119919
theorem B4245787 : Blo 662308 4245787 := bstep (se 1 (by rfl) ⟨3184340, by rfl⟩ : syracuseStep 4245787 = 6368681) B6368681
theorem B1493711 : Blo 662308 1493711 := bstep (se 1 (by rfl) ⟨1120283, by rfl⟩ : syracuseStep 1493711 = 2240567) B2240567
theorem B17058599 : Blo 662308 17058599 := bstep (se 1 (by rfl) ⟨12793949, by rfl⟩ : syracuseStep 17058599 = 25587899) B25587899
theorem B3362795 : Blo 662308 3362795 := bstep (se 1 (by rfl) ⟨2522096, by rfl⟩ : syracuseStep 3362795 = 5044193) B5044193
theorem B21582409 : Blo 662308 21582409 := bstep (se 2 (by rfl) ⟨8093403, by rfl⟩ : syracuseStep 21582409 = 16186807) B16186807
theorem B1496303 : Blo 662308 1496303 := bstep (se 1 (by rfl) ⟨1122227, by rfl⟩ : syracuseStep 1496303 = 2244455) B2244455
theorem B2020735 : Blo 662308 2020735 := bstep (se 1 (by rfl) ⟨1515551, by rfl⟩ : syracuseStep 2020735 = 3031103) B3031103
theorem B1496447 : Blo 662308 1496447 := bstep (se 1 (by rfl) ⟨1122335, by rfl⟩ : syracuseStep 1496447 = 2244671) B2244671
theorem B3036797 : Blo 662308 3036797 := bstep (se 3 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 3036797 = 1138799) B1138799
theorem B1496807 : Blo 662308 1496807 := bstep (se 1 (by rfl) ⟨1122605, by rfl⟩ : syracuseStep 1496807 = 2245211) B2245211
theorem B1497257 : Blo 662308 1497257 := bstep (se 2 (by rfl) ⟨561471, by rfl⟩ : syracuseStep 1497257 = 1122943) B1122943
theorem B8084609 : Blo 662308 8084609 := bstep (se 2 (by rfl) ⟨3031728, by rfl⟩ : syracuseStep 8084609 = 6063457) B6063457
theorem B1499039 : Blo 662308 1499039 := bstep (se 1 (by rfl) ⟨1124279, by rfl⟩ : syracuseStep 1499039 = 2248559) B2248559
theorem B1499183 : Blo 662308 1499183 := bstep (se 1 (by rfl) ⟨1124387, by rfl⟩ : syracuseStep 1499183 = 2248775) B2248775
theorem B1368623 : Blo 662308 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B44229341 : Blo 662308 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B746527 : Blo 662308 746527 := bstep (se 1 (by rfl) ⟨559895, by rfl⟩ : syracuseStep 746527 = 1119791) B1119791
theorem B10773755 : Blo 662308 10773755 := bstep (se 1 (by rfl) ⟨8080316, by rfl⟩ : syracuseStep 10773755 = 16160633) B16160633
theorem B1894079 : Blo 662308 1894079 := bstep (se 1 (by rfl) ⟨1420559, by rfl⟩ : syracuseStep 1894079 = 2841119) B2841119
theorem B8513261 : Blo 662308 8513261 := bstep (se 3 (by rfl) ⟨1596236, by rfl⟩ : syracuseStep 8513261 = 3192473) B3192473
theorem B2517419 : Blo 662308 2517419 := bstep (se 1 (by rfl) ⟨1888064, by rfl⟩ : syracuseStep 2517419 = 3776129) B3776129
theorem B2388199 : Blo 662308 2388199 := bstep (se 1 (by rfl) ⟨1791149, by rfl⟩ : syracuseStep 2388199 = 3582299) B3582299
theorem B1012703 : Blo 662308 1012703 := bstep (se 1 (by rfl) ⟨759527, by rfl⟩ : syracuseStep 1012703 = 1519055) B1519055
theorem B11368025 : Blo 662308 11368025 := bstep (se 2 (by rfl) ⟨4263009, by rfl⟩ : syracuseStep 11368025 = 8526019) B8526019
theorem B948361 : Blo 662308 948361 := bstep (se 2 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 948361 = 711271) B711271
theorem B20446145 : Blo 662308 20446145 := bstep (se 2 (by rfl) ⟨7667304, by rfl⟩ : syracuseStep 20446145 = 15334609) B15334609
theorem B34634981 : Blo 662308 34634981 := bstep (se 4 (by rfl) ⟨3247029, by rfl⟩ : syracuseStep 34634981 = 6494059) B6494059
theorem B40992581 : Blo 662308 40992581 := bstep (se 4 (by rfl) ⟨3843054, by rfl⟩ : syracuseStep 40992581 = 7686109) B7686109
theorem B6389867 : Blo 662308 6389867 := bstep (se 1 (by rfl) ⟨4792400, by rfl⟩ : syracuseStep 6389867 = 9584801) B9584801
theorem B5374097 : Blo 662308 5374097 := bstep (se 2 (by rfl) ⟨2015286, by rfl⟩ : syracuseStep 5374097 = 4030573) B4030573
theorem B591331913 : Blo 662308 591331913 := bstep (se 2 (by rfl) ⟨221749467, by rfl⟩ : syracuseStep 591331913 = 443498935) B443498935
theorem B2556755 : Blo 662308 2556755 := bstep (se 1 (by rfl) ⟨1917566, by rfl⟩ : syracuseStep 2556755 = 3835133) B3835133
theorem B5669797 : Blo 662308 5669797 := bstep (se 4 (by rfl) ⟨531543, by rfl⟩ : syracuseStep 5669797 = 1063087) B1063087
theorem B6063083 : Blo 662308 6063083 := bstep (se 1 (by rfl) ⟨4547312, by rfl⟩ : syracuseStep 6063083 = 9094625) B9094625
theorem B10748969 : Blo 662308 10748969 := bstep (se 2 (by rfl) ⟨4030863, by rfl⟩ : syracuseStep 10748969 = 8061727) B8061727
theorem B5670071 : Blo 662308 5670071 := bstep (se 1 (by rfl) ⟨4252553, by rfl⟩ : syracuseStep 5670071 = 8505107) B8505107
theorem B11372399 : Blo 662308 11372399 := bstep (se 1 (by rfl) ⟨8529299, by rfl⟩ : syracuseStep 11372399 = 17058599) B17058599
theorem B3184265 : Blo 662308 3184265 := bstep (se 2 (by rfl) ⟨1194099, by rfl⟩ : syracuseStep 3184265 = 2388199) B2388199
theorem B28776545 : Blo 662308 28776545 := bstep (se 2 (by rfl) ⟨10791204, by rfl⟩ : syracuseStep 28776545 = 21582409) B21582409
theorem B7182503 : Blo 662308 7182503 := bstep (se 1 (by rfl) ⟨5386877, by rfl⟩ : syracuseStep 7182503 = 10773755) B10773755
theorem B5675507 : Blo 662308 5675507 := bstep (se 1 (by rfl) ⟨4256630, by rfl⟩ : syracuseStep 5675507 = 8513261) B8513261
theorem B1678279 : Blo 662308 1678279 := bstep (se 1 (by rfl) ⟨1258709, by rfl⟩ : syracuseStep 1678279 = 2517419) B2517419
theorem B2694313 : Blo 662308 2694313 := bstep (se 2 (by rfl) ⟨1010367, by rfl⟩ : syracuseStep 2694313 = 2020735) B2020735
theorem B663087 : Blo 662308 663087 := bstep (se 1 (by rfl) ⟨497315, by rfl⟩ : syracuseStep 663087 = 994631) B994631
theorem B1679737 : Blo 662308 1679737 := bstep (se 2 (by rfl) ⟨629901, by rfl⟩ : syracuseStep 1679737 = 1259803) B1259803
theorem B1516283 : Blo 662308 1516283 := bstep (se 1 (by rfl) ⟨1137212, by rfl⟩ : syracuseStep 1516283 = 2274425) B2274425
theorem B664575 : Blo 662308 664575 := bstep (se 1 (by rfl) ⟨498431, by rfl⟩ : syracuseStep 664575 = 996863) B996863
theorem B7578683 : Blo 662308 7578683 := bstep (se 1 (by rfl) ⟨5684012, by rfl⟩ : syracuseStep 7578683 = 11368025) B11368025
theorem B664667 : Blo 662308 664667 := bstep (se 1 (by rfl) ⟨498500, by rfl⟩ : syracuseStep 664667 = 997001) B997001
theorem B7546607 : Blo 662308 7546607 := bstep (se 1 (by rfl) ⟨5659955, by rfl⟩ : syracuseStep 7546607 = 11319911) B11319911
theorem B3155879 : Blo 662308 3155879 := bstep (se 1 (by rfl) ⟨2366909, by rfl⟩ : syracuseStep 3155879 = 4733819) B4733819
theorem B665959 : Blo 662308 665959 := bstep (se 1 (by rfl) ⟨499469, by rfl⟩ : syracuseStep 665959 = 998939) B998939
theorem B995231 : Blo 662308 995231 := bstep (se 1 (by rfl) ⟨746423, by rfl⟩ : syracuseStep 995231 = 1492847) B1492847
theorem B995369 : Blo 662308 995369 := bstep (se 2 (by rfl) ⟨373263, by rfl⟩ : syracuseStep 995369 = 746527) B746527
theorem B3780755 : Blo 662308 3780755 := bstep (se 1 (by rfl) ⟨2835566, by rfl⟩ : syracuseStep 3780755 = 5671133) B5671133
theorem B995483 : Blo 662308 995483 := bstep (se 1 (by rfl) ⟨746612, by rfl⟩ : syracuseStep 995483 = 1493225) B1493225
theorem B995807 : Blo 662308 995807 := bstep (se 1 (by rfl) ⟨746855, by rfl⟩ : syracuseStep 995807 = 1493711) B1493711
theorem B3585151 : Blo 662308 3585151 := bstep (se 1 (by rfl) ⟨2688863, by rfl⟩ : syracuseStep 3585151 = 5377727) B5377727
theorem B2700541 : Blo 662308 2700541 := bstep (se 3 (by rfl) ⟨506351, by rfl⟩ : syracuseStep 2700541 = 1012703) B1012703
theorem B2241863 : Blo 662308 2241863 := bstep (se 1 (by rfl) ⟨1681397, by rfl⟩ : syracuseStep 2241863 = 3362795) B3362795
theorem B997535 : Blo 662308 997535 := bstep (se 1 (by rfl) ⟨748151, by rfl⟩ : syracuseStep 997535 = 1496303) B1496303
theorem B997631 : Blo 662308 997631 := bstep (se 1 (by rfl) ⟨748223, by rfl⟩ : syracuseStep 997631 = 1496447) B1496447
theorem B28686743 : Blo 662308 28686743 := bstep (se 1 (by rfl) ⟨21515057, by rfl⟩ : syracuseStep 28686743 = 43030115) B43030115
theorem B8632739 : Blo 662308 8632739 := bstep (se 1 (by rfl) ⟨6474554, by rfl⟩ : syracuseStep 8632739 = 12949109) B12949109
theorem B997871 : Blo 662308 997871 := bstep (se 1 (by rfl) ⟨748403, by rfl⟩ : syracuseStep 997871 = 1496807) B1496807
theorem B998171 : Blo 662308 998171 := bstep (se 1 (by rfl) ⟨748628, by rfl⟩ : syracuseStep 998171 = 1497257) B1497257
theorem B5389739 : Blo 662308 5389739 := bstep (se 1 (by rfl) ⟨4042304, by rfl⟩ : syracuseStep 5389739 = 8084609) B8084609
theorem B1490615 : Blo 662308 1490615 := bstep (se 1 (by rfl) ⟨1117961, by rfl⟩ : syracuseStep 1490615 = 2235923) B2235923
theorem B999359 : Blo 662308 999359 := bstep (se 1 (by rfl) ⟨749519, by rfl⟩ : syracuseStep 999359 = 1499039) B1499039
theorem B999455 : Blo 662308 999455 := bstep (se 1 (by rfl) ⟨749591, by rfl⟩ : syracuseStep 999455 = 1499183) B1499183
theorem B1262719 : Blo 662308 1262719 := bstep (se 1 (by rfl) ⟨947039, by rfl⟩ : syracuseStep 1262719 = 1894079) B1894079
theorem B1493243 : Blo 662308 1493243 := bstep (se 1 (by rfl) ⟨1119932, by rfl⟩ : syracuseStep 1493243 = 2239865) B2239865
theorem B1264481 : Blo 662308 1264481 := bstep (se 2 (by rfl) ⟨474180, by rfl⟩ : syracuseStep 1264481 = 948361) B948361
theorem B1494431 : Blo 662308 1494431 := bstep (se 1 (by rfl) ⟨1120823, by rfl⟩ : syracuseStep 1494431 = 2241647) B2241647
theorem B708383 : Blo 662308 708383 := bstep (se 1 (by rfl) ⟨531287, by rfl⟩ : syracuseStep 708383 = 1062575) B1062575
theorem B3199103 : Blo 662308 3199103 := bstep (se 1 (by rfl) ⟨2399327, by rfl⟩ : syracuseStep 3199103 = 4798655) B4798655
theorem B3789251 : Blo 662308 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B23089987 : Blo 662308 23089987 := bstep (se 1 (by rfl) ⟨17317490, by rfl⟩ : syracuseStep 23089987 = 34634981) B34634981
theorem B3364253 : Blo 662308 3364253 := bstep (se 3 (by rfl) ⟨630797, by rfl⟩ : syracuseStep 3364253 = 1261595) B1261595
theorem B36329897 : Blo 662308 36329897 := bstep (se 2 (by rfl) ⟨13623711, by rfl⟩ : syracuseStep 36329897 = 27247423) B27247423
theorem B5661049 : Blo 662308 5661049 := bstep (se 2 (by rfl) ⟨2122893, by rfl⟩ : syracuseStep 5661049 = 4245787) B4245787
theorem B2024531 : Blo 662308 2024531 := bstep (se 1 (by rfl) ⟨1518398, by rfl⟩ : syracuseStep 2024531 = 3036797) B3036797
theorem B944875 : Blo 662308 944875 := bstep (se 1 (by rfl) ⟨708656, by rfl⟩ : syracuseStep 944875 = 1417313) B1417313
theorem B912415 : Blo 662308 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B29486227 : Blo 662308 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B1600879 : Blo 662308 1600879 := bstep (se 1 (by rfl) ⟨1200659, by rfl⟩ : syracuseStep 1600879 = 2401319) B2401319
theorem B12153023 : Blo 662308 12153023 := bstep (se 1 (by rfl) ⟨9114767, by rfl⟩ : syracuseStep 12153023 = 18229535) B18229535
theorem B3373001 : Blo 662308 3373001 := bstep (se 2 (by rfl) ⟨1264875, by rfl⟩ : syracuseStep 3373001 = 2529751) B2529751
theorem B13630763 : Blo 662308 13630763 := bstep (se 1 (by rfl) ⟨10223072, by rfl⟩ : syracuseStep 13630763 = 20446145) B20446145
theorem B3833567 : Blo 662308 3833567 := bstep (se 1 (by rfl) ⟨2875175, by rfl⟩ : syracuseStep 3833567 = 5750351) B5750351
theorem B27328387 : Blo 662308 27328387 := bstep (se 1 (by rfl) ⟨20496290, by rfl⟩ : syracuseStep 27328387 = 40992581) B40992581
theorem B4259911 : Blo 662308 4259911 := bstep (se 1 (by rfl) ⟨3194933, by rfl⟩ : syracuseStep 4259911 = 6389867) B6389867
theorem B1704503 : Blo 662308 1704503 := bstep (se 1 (by rfl) ⟨1278377, by rfl⟩ : syracuseStep 1704503 = 2556755) B2556755
theorem B2132735 : Blo 662308 2132735 := bstep (se 1 (by rfl) ⟨1599551, by rfl⟩ : syracuseStep 2132735 = 3199103) B3199103
theorem B2526167 : Blo 662308 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B1216553 : Blo 662308 1216553 := bstep (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) B912415
theorem B4788335 : Blo 662308 4788335 := bstep (se 1 (by rfl) ⟨3591251, by rfl⟩ : syracuseStep 4788335 = 7182503) B7182503
theorem B24219931 : Blo 662308 24219931 := bstep (se 1 (by rfl) ⟨18164948, by rfl⟩ : syracuseStep 24219931 = 36329897) B36329897
theorem B2134505 : Blo 662308 2134505 := bstep (se 2 (by rfl) ⟨800439, by rfl⟩ : syracuseStep 2134505 = 1600879) B1600879
theorem B5052455 : Blo 662308 5052455 := bstep (se 1 (by rfl) ⟨3789341, by rfl⟩ : syracuseStep 5052455 = 7578683) B7578683
theorem B1349687 : Blo 662308 1349687 := bstep (se 1 (by rfl) ⟨1012265, by rfl⟩ : syracuseStep 1349687 = 2024531) B2024531
theorem B663487 : Blo 662308 663487 := bstep (se 1 (by rfl) ⟨497615, by rfl⟩ : syracuseStep 663487 = 995231) B995231
theorem B663579 : Blo 662308 663579 := bstep (se 1 (by rfl) ⟨497684, by rfl⟩ : syracuseStep 663579 = 995369) B995369
theorem B663655 : Blo 662308 663655 := bstep (se 1 (by rfl) ⟨497741, by rfl⟩ : syracuseStep 663655 = 995483) B995483
theorem B8102015 : Blo 662308 8102015 := bstep (se 1 (by rfl) ⟨6076511, by rfl⟩ : syracuseStep 8102015 = 12153023) B12153023
theorem B663871 : Blo 662308 663871 := bstep (se 1 (by rfl) ⟨497903, by rfl⟩ : syracuseStep 663871 = 995807) B995807
theorem B2237705 : Blo 662308 2237705 := bstep (se 2 (by rfl) ⟨839139, by rfl⟩ : syracuseStep 2237705 = 1678279) B1678279
theorem B665023 : Blo 662308 665023 := bstep (se 1 (by rfl) ⟨498767, by rfl⟩ : syracuseStep 665023 = 997535) B997535
theorem B665087 : Blo 662308 665087 := bstep (se 1 (by rfl) ⟨498815, by rfl⟩ : syracuseStep 665087 = 997631) B997631
theorem B665247 : Blo 662308 665247 := bstep (se 1 (by rfl) ⟨498935, by rfl⟩ : syracuseStep 665247 = 997871) B997871
theorem B665447 : Blo 662308 665447 := bstep (se 1 (by rfl) ⟨499085, by rfl⟩ : syracuseStep 665447 = 998171) B998171
theorem B9087175 : Blo 662308 9087175 := bstep (se 1 (by rfl) ⟨6815381, by rfl⟩ : syracuseStep 9087175 = 13630763) B13630763
theorem B993743 : Blo 662308 993743 := bstep (se 1 (by rfl) ⟨745307, by rfl⟩ : syracuseStep 993743 = 1490615) B1490615
theorem B666239 : Blo 662308 666239 := bstep (se 1 (by rfl) ⟨499679, by rfl⟩ : syracuseStep 666239 = 999359) B999359
theorem B666303 : Blo 662308 666303 := bstep (se 1 (by rfl) ⟨499727, by rfl⟩ : syracuseStep 666303 = 999455) B999455
theorem B3582731 : Blo 662308 3582731 := bstep (se 1 (by rfl) ⟨2687048, by rfl⟩ : syracuseStep 3582731 = 5374097) B5374097
theorem B7548065 : Blo 662308 7548065 := bstep (se 2 (by rfl) ⟨2830524, by rfl⟩ : syracuseStep 7548065 = 5661049) B5661049
theorem B2239649 : Blo 662308 2239649 := bstep (se 2 (by rfl) ⟨839868, by rfl⟩ : syracuseStep 2239649 = 1679737) B1679737
theorem B4042055 : Blo 662308 4042055 := bstep (se 1 (by rfl) ⟨3031541, by rfl⟩ : syracuseStep 4042055 = 6063083) B6063083
theorem B3780047 : Blo 662308 3780047 := bstep (se 1 (by rfl) ⟨2835035, by rfl⟩ : syracuseStep 3780047 = 5670071) B5670071
theorem B7581599 : Blo 662308 7581599 := bstep (se 1 (by rfl) ⟨5686199, by rfl⟩ : syracuseStep 7581599 = 11372399) B11372399
theorem B995495 : Blo 662308 995495 := bstep (se 1 (by rfl) ⟨746621, by rfl⟩ : syracuseStep 995495 = 1493243) B1493243
theorem B1683625 : Blo 662308 1683625 := bstep (se 2 (by rfl) ⟨631359, by rfl⟩ : syracuseStep 1683625 = 1262719) B1262719
theorem B996287 : Blo 662308 996287 := bstep (se 1 (by rfl) ⟨747215, by rfl⟩ : syracuseStep 996287 = 1494431) B1494431
theorem B2242835 : Blo 662308 2242835 := bstep (se 1 (by rfl) ⟨1682126, by rfl⟩ : syracuseStep 2242835 = 3364253) B3364253
theorem B19184363 : Blo 662308 19184363 := bstep (se 1 (by rfl) ⟨14388272, by rfl⟩ : syracuseStep 19184363 = 28776545) B28776545
theorem B3783671 : Blo 662308 3783671 := bstep (se 1 (by rfl) ⟨2837753, by rfl⟩ : syracuseStep 3783671 = 5675507) B5675507
theorem B19120805 : Blo 662308 19120805 := bstep (se 4 (by rfl) ⟨1792575, by rfl⟩ : syracuseStep 19120805 = 3585151) B3585151
theorem B14369669 : Blo 662308 14369669 := bstep (se 4 (by rfl) ⟨1347156, by rfl⟩ : syracuseStep 14369669 = 2694313) B2694313
theorem B30786649 : Blo 662308 30786649 := bstep (se 2 (by rfl) ⟨11544993, by rfl⟩ : syracuseStep 30786649 = 23089987) B23089987
theorem B5031071 : Blo 662308 5031071 := bstep (se 1 (by rfl) ⟨3773303, by rfl⟩ : syracuseStep 5031071 = 7546607) B7546607
theorem B1494575 : Blo 662308 1494575 := bstep (se 1 (by rfl) ⟨1120931, by rfl⟩ : syracuseStep 1494575 = 2241863) B2241863
theorem B2248667 : Blo 662308 2248667 := bstep (se 1 (by rfl) ⟨1686500, by rfl⟩ : syracuseStep 2248667 = 3373001) B3373001
theorem B19124495 : Blo 662308 19124495 := bstep (se 1 (by rfl) ⟨14343371, by rfl⟩ : syracuseStep 19124495 = 28686743) B28686743
theorem B5755159 : Blo 662308 5755159 := bstep (se 1 (by rfl) ⟨4316369, by rfl⟩ : syracuseStep 5755159 = 8632739) B8632739
theorem B1889021 : Blo 662308 1889021 := bstep (se 3 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 1889021 = 708383) B708383
theorem B3593159 : Blo 662308 3593159 := bstep (se 1 (by rfl) ⟨2694869, by rfl⟩ : syracuseStep 3593159 = 5389739) B5389739
theorem B394221275 : Blo 662308 394221275 := bstep (se 1 (by rfl) ⟨295665956, by rfl⟩ : syracuseStep 394221275 = 591331913) B591331913
theorem B7165979 : Blo 662308 7165979 := bstep (se 1 (by rfl) ⟨5374484, by rfl⟩ : syracuseStep 7165979 = 10748969) B10748969
theorem B7559729 : Blo 662308 7559729 := bstep (se 2 (by rfl) ⟨2834898, by rfl⟩ : syracuseStep 7559729 = 5669797) B5669797
theorem B842987 : Blo 662308 842987 := bstep (se 1 (by rfl) ⟨632240, by rfl⟩ : syracuseStep 842987 = 1264481) B1264481
theorem B2122843 : Blo 662308 2122843 := bstep (se 1 (by rfl) ⟨1592132, by rfl⟩ : syracuseStep 2122843 = 3184265) B3184265
theorem B5039333 : Blo 662308 5039333 := bstep (se 4 (by rfl) ⟨472437, by rfl⟩ : syracuseStep 5039333 = 944875) B944875
theorem B39314969 : Blo 662308 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B8415677 : Blo 662308 8415677 := bstep (se 3 (by rfl) ⟨1577939, by rfl⟩ : syracuseStep 8415677 = 3155879) B3155879
theorem B1010855 : Blo 662308 1010855 := bstep (se 1 (by rfl) ⟨758141, by rfl⟩ : syracuseStep 1010855 = 1516283) B1516283
theorem B3600721 : Blo 662308 3600721 := bstep (se 2 (by rfl) ⟨1350270, by rfl⟩ : syracuseStep 3600721 = 2700541) B2700541
theorem B2520503 : Blo 662308 2520503 := bstep (se 1 (by rfl) ⟨1890377, by rfl⟩ : syracuseStep 2520503 = 3780755) B3780755
theorem B2555711 : Blo 662308 2555711 := bstep (se 1 (by rfl) ⟨1916783, by rfl⟩ : syracuseStep 2555711 = 3833567) B3833567
theorem B36437849 : Blo 662308 36437849 := bstep (se 2 (by rfl) ⟨13664193, by rfl⟩ : syracuseStep 36437849 = 27328387) B27328387
theorem B3244141 : Blo 662308 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B12747203 : Blo 662308 12747203 := bstep (se 1 (by rfl) ⟨9560402, by rfl⟩ : syracuseStep 12747203 = 19120805) B19120805
theorem B12749663 : Blo 662308 12749663 := bstep (se 1 (by rfl) ⟨9562247, by rfl⟩ : syracuseStep 12749663 = 19124495) B19124495
theorem B2395439 : Blo 662308 2395439 := bstep (se 1 (by rfl) ⟨1796579, by rfl⟩ : syracuseStep 2395439 = 3593159) B3593159
theorem B7673545 : Blo 662308 7673545 := bstep (se 2 (by rfl) ⟨2877579, by rfl⟩ : syracuseStep 7673545 = 5755159) B5755159
theorem B5610451 : Blo 662308 5610451 := bstep (se 1 (by rfl) ⟨4207838, by rfl⟩ : syracuseStep 5610451 = 8415677) B8415677
theorem B662495 : Blo 662308 662495 := bstep (se 1 (by rfl) ⟨496871, by rfl⟩ : syracuseStep 662495 = 993743) B993743
theorem B2694703 : Blo 662308 2694703 := bstep (se 1 (by rfl) ⟨2021027, by rfl⟩ : syracuseStep 2694703 = 4042055) B4042055
theorem B5054399 : Blo 662308 5054399 := bstep (se 1 (by rfl) ⟨3790799, by rfl⟩ : syracuseStep 5054399 = 7581599) B7581599
theorem B663663 : Blo 662308 663663 := bstep (se 1 (by rfl) ⟨497747, by rfl⟩ : syracuseStep 663663 = 995495) B995495
theorem B664191 : Blo 662308 664191 := bstep (se 1 (by rfl) ⟨498143, by rfl⟩ : syracuseStep 664191 = 996287) B996287
theorem B1680335 : Blo 662308 1680335 := bstep (se 1 (by rfl) ⟨1260251, by rfl⟩ : syracuseStep 1680335 = 2520503) B2520503
theorem B12789575 : Blo 662308 12789575 := bstep (se 1 (by rfl) ⟨9592181, by rfl⟩ : syracuseStep 12789575 = 19184363) B19184363
theorem B24291899 : Blo 662308 24291899 := bstep (se 1 (by rfl) ⟨18218924, by rfl⟩ : syracuseStep 24291899 = 36437849) B36437849
theorem B5679881 : Blo 662308 5679881 := bstep (se 2 (by rfl) ⟨2129955, by rfl⟩ : syracuseStep 5679881 = 4259911) B4259911
theorem B9579779 : Blo 662308 9579779 := bstep (se 1 (by rfl) ⟨7184834, by rfl⟩ : syracuseStep 9579779 = 14369669) B14369669
theorem B3354047 : Blo 662308 3354047 := bstep (se 1 (by rfl) ⟨2515535, by rfl⟩ : syracuseStep 3354047 = 5031071) B5031071
theorem B2830457 : Blo 662308 2830457 := bstep (se 2 (by rfl) ⟨1061421, by rfl⟩ : syracuseStep 2830457 = 2122843) B2122843
theorem B1684111 : Blo 662308 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B996383 : Blo 662308 996383 := bstep (se 1 (by rfl) ⟨747287, by rfl⟩ : syracuseStep 996383 = 1494575) B1494575
theorem B3192223 : Blo 662308 3192223 := bstep (se 1 (by rfl) ⟨2394167, by rfl⟩ : syracuseStep 3192223 = 4788335) B4788335
theorem B1423003 : Blo 662308 1423003 := bstep (se 1 (by rfl) ⟨1067252, by rfl⟩ : syracuseStep 1423003 = 2134505) B2134505
theorem B262814183 : Blo 662308 262814183 := bstep (se 1 (by rfl) ⟨197110637, by rfl⟩ : syracuseStep 262814183 = 394221275) B394221275
theorem B899791 : Blo 662308 899791 := bstep (se 1 (by rfl) ⟨674843, by rfl⟩ : syracuseStep 899791 = 1349687) B1349687
theorem B2244833 : Blo 662308 2244833 := bstep (se 2 (by rfl) ⟨841812, by rfl⟩ : syracuseStep 2244833 = 1683625) B1683625
theorem B32293241 : Blo 662308 32293241 := bstep (se 2 (by rfl) ⟨12109965, by rfl⟩ : syracuseStep 32293241 = 24219931) B24219931
theorem B4800961 : Blo 662308 4800961 := bstep (se 2 (by rfl) ⟨1800360, by rfl⟩ : syracuseStep 4800961 = 3600721) B3600721
theorem B3359555 : Blo 662308 3359555 := bstep (se 1 (by rfl) ⟨2519666, by rfl⟩ : syracuseStep 3359555 = 5039333) B5039333
theorem B1491803 : Blo 662308 1491803 := bstep (se 1 (by rfl) ⟨1118852, by rfl⟩ : syracuseStep 1491803 = 2237705) B2237705
theorem B5687293 : Blo 662308 5687293 := bstep (se 3 (by rfl) ⟨1066367, by rfl⟩ : syracuseStep 5687293 = 2132735) B2132735
theorem B5032043 : Blo 662308 5032043 := bstep (se 1 (by rfl) ⟨3774032, by rfl⟩ : syracuseStep 5032043 = 7548065) B7548065
theorem B1493099 : Blo 662308 1493099 := bstep (se 1 (by rfl) ⟨1119824, by rfl⟩ : syracuseStep 1493099 = 2239649) B2239649
theorem B673903 : Blo 662308 673903 := bstep (se 1 (by rfl) ⟨505427, by rfl⟩ : syracuseStep 673903 = 1010855) B1010855
theorem B2247965 : Blo 662308 2247965 := bstep (se 3 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 2247965 = 842987) B842987
theorem B1495223 : Blo 662308 1495223 := bstep (se 1 (by rfl) ⟨1121417, by rfl⟩ : syracuseStep 1495223 = 2242835) B2242835
theorem B4545341 : Blo 662308 4545341 := bstep (se 3 (by rfl) ⟨852251, by rfl⟩ : syracuseStep 4545341 = 1704503) B1704503
theorem B5037389 : Blo 662308 5037389 := bstep (se 3 (by rfl) ⟨944510, by rfl⟩ : syracuseStep 5037389 = 1889021) B1889021
theorem B1499111 : Blo 662308 1499111 := bstep (se 1 (by rfl) ⟨1124333, by rfl⟩ : syracuseStep 1499111 = 2248667) B2248667
theorem B12116233 : Blo 662308 12116233 := bstep (se 2 (by rfl) ⟨4543587, by rfl⟩ : syracuseStep 12116233 = 9087175) B9087175
theorem B4777319 : Blo 662308 4777319 := bstep (se 1 (by rfl) ⟨3582989, by rfl⟩ : syracuseStep 4777319 = 7165979) B7165979
theorem B3368303 : Blo 662308 3368303 := bstep (se 1 (by rfl) ⟨2526227, by rfl⟩ : syracuseStep 3368303 = 5052455) B5052455
theorem B5039819 : Blo 662308 5039819 := bstep (se 1 (by rfl) ⟨3779864, by rfl⟩ : syracuseStep 5039819 = 7559729) B7559729
theorem B5401343 : Blo 662308 5401343 := bstep (se 1 (by rfl) ⟨4051007, by rfl⟩ : syracuseStep 5401343 = 8102015) B8102015
theorem B164195461 : Blo 662308 164195461 := bstep (se 4 (by rfl) ⟨15393324, by rfl⟩ : syracuseStep 164195461 = 30786649) B30786649
theorem B26209979 : Blo 662308 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B2388487 : Blo 662308 2388487 := bstep (se 1 (by rfl) ⟨1791365, by rfl⟩ : syracuseStep 2388487 = 3582731) B3582731
theorem B2520031 : Blo 662308 2520031 := bstep (se 1 (by rfl) ⟨1890023, by rfl⟩ : syracuseStep 2520031 = 3780047) B3780047
theorem B2522447 : Blo 662308 2522447 := bstep (se 1 (by rfl) ⟨1891835, by rfl⟩ : syracuseStep 2522447 = 3783671) B3783671
theorem B1703807 : Blo 662308 1703807 := bstep (se 1 (by rfl) ⟨1277855, by rfl⟩ : syracuseStep 1703807 = 2555711) B2555711
theorem B4325521 : Blo 662308 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B21528827 : Blo 662308 21528827 := bstep (se 1 (by rfl) ⟨16146620, by rfl⟩ : syracuseStep 21528827 = 32293241) B32293241
theorem B16154977 : Blo 662308 16154977 := bstep (se 2 (by rfl) ⟨6058116, by rfl⟩ : syracuseStep 16154977 = 12116233) B12116233
theorem B218927281 : Blo 662308 218927281 := bstep (se 2 (by rfl) ⟨82097730, by rfl⟩ : syracuseStep 218927281 = 164195461) B164195461
theorem B1120223 : Blo 662308 1120223 := bstep (se 1 (by rfl) ⟨840167, by rfl⟩ : syracuseStep 1120223 = 1680335) B1680335
theorem B3184649 : Blo 662308 3184649 := bstep (se 2 (by rfl) ⟨1194243, by rfl⟩ : syracuseStep 3184649 = 2388487) B2388487
theorem B8526383 : Blo 662308 8526383 := bstep (se 1 (by rfl) ⟨6394787, by rfl⟩ : syracuseStep 8526383 = 12789575) B12789575
theorem B16194599 : Blo 662308 16194599 := bstep (se 1 (by rfl) ⟨12145949, by rfl⟩ : syracuseStep 16194599 = 24291899) B24291899
theorem B2236031 : Blo 662308 2236031 := bstep (se 1 (by rfl) ⟨1677023, by rfl⟩ : syracuseStep 2236031 = 3354047) B3354047
theorem B17473319 : Blo 662308 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B664255 : Blo 662308 664255 := bstep (se 1 (by rfl) ⟨498191, by rfl⟩ : syracuseStep 664255 = 996383) B996383
theorem B7480601 : Blo 662308 7480601 := bstep (se 2 (by rfl) ⟨2805225, by rfl⟩ : syracuseStep 7480601 = 5610451) B5610451
theorem B1681631 : Blo 662308 1681631 := bstep (se 1 (by rfl) ⟨1261223, by rfl⟩ : syracuseStep 1681631 = 2522447) B2522447
theorem B8498135 : Blo 662308 8498135 := bstep (se 1 (by rfl) ⟨6373601, by rfl⟩ : syracuseStep 8498135 = 12747203) B12747203
theorem B2239703 : Blo 662308 2239703 := bstep (se 1 (by rfl) ⟨1679777, by rfl⟩ : syracuseStep 2239703 = 3359555) B3359555
theorem B994535 : Blo 662308 994535 := bstep (se 1 (by rfl) ⟨745901, by rfl⟩ : syracuseStep 994535 = 1491803) B1491803
theorem B6401281 : Blo 662308 6401281 := bstep (se 2 (by rfl) ⟨2400480, by rfl⟩ : syracuseStep 6401281 = 4800961) B4800961
theorem B3354695 : Blo 662308 3354695 := bstep (se 1 (by rfl) ⟨2516021, by rfl⟩ : syracuseStep 3354695 = 5032043) B5032043
theorem B995399 : Blo 662308 995399 := bstep (se 1 (by rfl) ⟨746549, by rfl⟩ : syracuseStep 995399 = 1493099) B1493099
theorem B8499775 : Blo 662308 8499775 := bstep (se 1 (by rfl) ⟨6374831, by rfl⟩ : syracuseStep 8499775 = 12749663) B12749663
theorem B7583057 : Blo 662308 7583057 := bstep (se 2 (by rfl) ⟨2843646, by rfl⟩ : syracuseStep 7583057 = 5687293) B5687293
theorem B996815 : Blo 662308 996815 := bstep (se 1 (by rfl) ⟨747611, by rfl⟩ : syracuseStep 996815 = 1495223) B1495223
theorem B898537 : Blo 662308 898537 := bstep (se 2 (by rfl) ⟨336951, by rfl⟩ : syracuseStep 898537 = 673903) B673903
theorem B3030227 : Blo 662308 3030227 := bstep (se 1 (by rfl) ⟨2272670, by rfl⟩ : syracuseStep 3030227 = 4545341) B4545341
theorem B3358259 : Blo 662308 3358259 := bstep (se 1 (by rfl) ⟨2518694, by rfl⟩ : syracuseStep 3358259 = 5037389) B5037389
theorem B999407 : Blo 662308 999407 := bstep (se 1 (by rfl) ⟨749555, by rfl⟩ : syracuseStep 999407 = 1499111) B1499111
theorem B2245481 : Blo 662308 2245481 := bstep (se 2 (by rfl) ⟨842055, by rfl⟩ : syracuseStep 2245481 = 1684111) B1684111
theorem B2245535 : Blo 662308 2245535 := bstep (se 1 (by rfl) ⟨1684151, by rfl⟩ : syracuseStep 2245535 = 3368303) B3368303
theorem B3359879 : Blo 662308 3359879 := bstep (se 1 (by rfl) ⟨2519909, by rfl⟩ : syracuseStep 3359879 = 5039819) B5039819
theorem B3360041 : Blo 662308 3360041 := bstep (se 2 (by rfl) ⟨1260015, by rfl⟩ : syracuseStep 3360041 = 2520031) B2520031
theorem B3786587 : Blo 662308 3786587 := bstep (se 1 (by rfl) ⟨2839940, by rfl⟩ : syracuseStep 3786587 = 5679881) B5679881
theorem B14403581 : Blo 662308 14403581 := bstep (se 3 (by rfl) ⟨2700671, by rfl⟩ : syracuseStep 14403581 = 5401343) B5401343
theorem B1886971 : Blo 662308 1886971 := bstep (se 1 (by rfl) ⟨1415228, by rfl⟩ : syracuseStep 1886971 = 2830457) B2830457
theorem B3592937 : Blo 662308 3592937 := bstep (se 2 (by rfl) ⟨1347351, by rfl⟩ : syracuseStep 3592937 = 2694703) B2694703
theorem B1135871 : Blo 662308 1135871 := bstep (se 1 (by rfl) ⟨851903, by rfl⟩ : syracuseStep 1135871 = 1703807) B1703807
theorem B1496555 : Blo 662308 1496555 := bstep (se 1 (by rfl) ⟨1122416, by rfl⟩ : syracuseStep 1496555 = 2244833) B2244833
theorem B1498643 : Blo 662308 1498643 := bstep (se 1 (by rfl) ⟨1123982, by rfl⟩ : syracuseStep 1498643 = 2247965) B2247965
theorem B1596959 : Blo 662308 1596959 := bstep (se 1 (by rfl) ⟨1197719, by rfl⟩ : syracuseStep 1596959 = 2395439) B2395439
theorem B12739517 : Blo 662308 12739517 := bstep (se 3 (by rfl) ⟨2388659, by rfl⟩ : syracuseStep 12739517 = 4777319) B4777319
theorem B19195541 : Blo 662308 19195541 := bstep (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) B899791
theorem B3369599 : Blo 662308 3369599 := bstep (se 1 (by rfl) ⟨2527199, by rfl⟩ : syracuseStep 3369599 = 5054399) B5054399
theorem B4256297 : Blo 662308 4256297 := bstep (se 2 (by rfl) ⟨1596111, by rfl⟩ : syracuseStep 4256297 = 3192223) B3192223
theorem B6386519 : Blo 662308 6386519 := bstep (se 1 (by rfl) ⟨4789889, by rfl⟩ : syracuseStep 6386519 = 9579779) B9579779
theorem B1897337 : Blo 662308 1897337 := bstep (se 2 (by rfl) ⟨711501, by rfl⟩ : syracuseStep 1897337 = 1423003) B1423003
theorem B40925573 : Blo 662308 40925573 := bstep (se 4 (by rfl) ⟨3836772, by rfl⟩ : syracuseStep 40925573 = 7673545) B7673545
theorem B175209455 : Blo 662308 175209455 := bstep (se 1 (by rfl) ⟨131407091, by rfl⟩ : syracuseStep 175209455 = 262814183) B262814183
theorem B14352551 : Blo 662308 14352551 := bstep (se 1 (by rfl) ⟨10764413, by rfl⟩ : syracuseStep 14352551 = 21528827) B21528827
theorem B5767361 : Blo 662308 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B2524391 : Blo 662308 2524391 := bstep (se 1 (by rfl) ⟨1893293, by rfl⟩ : syracuseStep 2524391 = 3786587) B3786587
theorem B9602387 : Blo 662308 9602387 := bstep (se 1 (by rfl) ⟨7201790, by rfl⟩ : syracuseStep 9602387 = 14403581) B14403581
theorem B757247 : Blo 662308 757247 := bstep (se 1 (by rfl) ⟨567935, by rfl⟩ : syracuseStep 757247 = 1135871) B1135871
theorem B291903041 : Blo 662308 291903041 := bstep (se 2 (by rfl) ⟨109463640, by rfl⟩ : syracuseStep 291903041 = 218927281) B218927281
theorem B8493011 : Blo 662308 8493011 := bstep (se 1 (by rfl) ⟨6369758, by rfl⟩ : syracuseStep 8493011 = 12739517) B12739517
theorem B4987067 : Blo 662308 4987067 := bstep (se 1 (by rfl) ⟨3740300, by rfl⟩ : syracuseStep 4987067 = 7480601) B7480601
theorem B1121087 : Blo 662308 1121087 := bstep (se 1 (by rfl) ⟨840815, by rfl⟩ : syracuseStep 1121087 = 1681631) B1681631
theorem B663023 : Blo 662308 663023 := bstep (se 1 (by rfl) ⟨497267, by rfl⟩ : syracuseStep 663023 = 994535) B994535
theorem B2236463 : Blo 662308 2236463 := bstep (se 1 (by rfl) ⟨1677347, by rfl⟩ : syracuseStep 2236463 = 3354695) B3354695
theorem B663599 : Blo 662308 663599 := bstep (se 1 (by rfl) ⟨497699, by rfl⟩ : syracuseStep 663599 = 995399) B995399
theorem B5055371 : Blo 662308 5055371 := bstep (se 1 (by rfl) ⟨3791528, by rfl⟩ : syracuseStep 5055371 = 7583057) B7583057
theorem B664543 : Blo 662308 664543 := bstep (se 1 (by rfl) ⟨498407, by rfl⟩ : syracuseStep 664543 = 996815) B996815
theorem B2238839 : Blo 662308 2238839 := bstep (se 1 (by rfl) ⟨1679129, by rfl⟩ : syracuseStep 2238839 = 3358259) B3358259
theorem B666271 : Blo 662308 666271 := bstep (se 1 (by rfl) ⟨499703, by rfl⟩ : syracuseStep 666271 = 999407) B999407
theorem B21539969 : Blo 662308 21539969 := bstep (se 2 (by rfl) ⟨8077488, by rfl⟩ : syracuseStep 21539969 = 16154977) B16154977
theorem B2239919 : Blo 662308 2239919 := bstep (se 1 (by rfl) ⟨1679939, by rfl⟩ : syracuseStep 2239919 = 3359879) B3359879
theorem B2240027 : Blo 662308 2240027 := bstep (se 1 (by rfl) ⟨1680020, by rfl⟩ : syracuseStep 2240027 = 3360041) B3360041
theorem B9581165 : Blo 662308 9581165 := bstep (se 3 (by rfl) ⟨1796468, by rfl⟩ : syracuseStep 9581165 = 3592937) B3592937
theorem B997703 : Blo 662308 997703 := bstep (se 1 (by rfl) ⟨748277, by rfl⟩ : syracuseStep 997703 = 1496555) B1496555
theorem B8535041 : Blo 662308 8535041 := bstep (se 2 (by rfl) ⟨3200640, by rfl⟩ : syracuseStep 8535041 = 6401281) B6401281
theorem B5684255 : Blo 662308 5684255 := bstep (se 1 (by rfl) ⟨4263191, by rfl⟩ : syracuseStep 5684255 = 8526383) B8526383
theorem B10796399 : Blo 662308 10796399 := bstep (se 1 (by rfl) ⟨8097299, by rfl⟩ : syracuseStep 10796399 = 16194599) B16194599
theorem B999095 : Blo 662308 999095 := bstep (se 1 (by rfl) ⟨749321, by rfl⟩ : syracuseStep 999095 = 1498643) B1498643
theorem B1064639 : Blo 662308 1064639 := bstep (se 1 (by rfl) ⟨798479, by rfl⟩ : syracuseStep 1064639 = 1596959) B1596959
theorem B1490687 : Blo 662308 1490687 := bstep (se 1 (by rfl) ⟨1118015, by rfl⟩ : syracuseStep 1490687 = 2236031) B2236031
theorem B11648879 : Blo 662308 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B12797027 : Blo 662308 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B2246399 : Blo 662308 2246399 := bstep (se 1 (by rfl) ⟨1684799, by rfl⟩ : syracuseStep 2246399 = 3369599) B3369599
theorem B1198049 : Blo 662308 1198049 := bstep (se 2 (by rfl) ⟨449268, by rfl⟩ : syracuseStep 1198049 = 898537) B898537
theorem B1493135 : Blo 662308 1493135 := bstep (se 1 (by rfl) ⟨1119851, by rfl⟩ : syracuseStep 1493135 = 2239703) B2239703
theorem B2837531 : Blo 662308 2837531 := bstep (se 1 (by rfl) ⟨2128148, by rfl⟩ : syracuseStep 2837531 = 4256297) B4256297
theorem B1264891 : Blo 662308 1264891 := bstep (se 1 (by rfl) ⟨948668, by rfl⟩ : syracuseStep 1264891 = 1897337) B1897337
theorem B27283715 : Blo 662308 27283715 := bstep (se 1 (by rfl) ⟨20462786, by rfl⟩ : syracuseStep 27283715 = 40925573) B40925573
theorem B116806303 : Blo 662308 116806303 := bstep (se 1 (by rfl) ⟨87604727, by rfl⟩ : syracuseStep 116806303 = 175209455) B175209455
theorem B2020151 : Blo 662308 2020151 := bstep (se 1 (by rfl) ⟨1515113, by rfl⟩ : syracuseStep 2020151 = 3030227) B3030227
theorem B1496987 : Blo 662308 1496987 := bstep (se 1 (by rfl) ⟨1122740, by rfl⟩ : syracuseStep 1496987 = 2245481) B2245481
theorem B1497023 : Blo 662308 1497023 := bstep (se 1 (by rfl) ⟨1122767, by rfl⟩ : syracuseStep 1497023 = 2245535) B2245535
theorem B2515961 : Blo 662308 2515961 := bstep (se 2 (by rfl) ⟨943485, by rfl⟩ : syracuseStep 2515961 = 1886971) B1886971
theorem B746815 : Blo 662308 746815 := bstep (se 1 (by rfl) ⟨560111, by rfl⟩ : syracuseStep 746815 = 1120223) B1120223
theorem B2123099 : Blo 662308 2123099 := bstep (se 1 (by rfl) ⟨1592324, by rfl⟩ : syracuseStep 2123099 = 3184649) B3184649
theorem B11333033 : Blo 662308 11333033 := bstep (se 2 (by rfl) ⟨4249887, by rfl⟩ : syracuseStep 11333033 = 8499775) B8499775
theorem B5665423 : Blo 662308 5665423 := bstep (se 1 (by rfl) ⟨4249067, by rfl⟩ : syracuseStep 5665423 = 8498135) B8498135
theorem B4257679 : Blo 662308 4257679 := bstep (se 1 (by rfl) ⟨3193259, by rfl⟩ : syracuseStep 4257679 = 6386519) B6386519
theorem B9568367 : Blo 662308 9568367 := bstep (se 1 (by rfl) ⟨7176275, by rfl⟩ : syracuseStep 9568367 = 14352551) B14352551
theorem B18189143 : Blo 662308 18189143 := bstep (se 1 (by rfl) ⟨13641857, by rfl⟩ : syracuseStep 18189143 = 27283715) B27283715
theorem B1677307 : Blo 662308 1677307 := bstep (se 1 (by rfl) ⟨1257980, by rfl⟩ : syracuseStep 1677307 = 2515961) B2515961
theorem B1415399 : Blo 662308 1415399 := bstep (se 1 (by rfl) ⟨1061549, by rfl⟩ : syracuseStep 1415399 = 2123099) B2123099
theorem B14359979 : Blo 662308 14359979 := bstep (se 1 (by rfl) ⟨10769984, by rfl⟩ : syracuseStep 14359979 = 21539969) B21539969
theorem B5676905 : Blo 662308 5676905 := bstep (se 2 (by rfl) ⟨2128839, by rfl⟩ : syracuseStep 5676905 = 4257679) B4257679
theorem B665135 : Blo 662308 665135 := bstep (se 1 (by rfl) ⟨498851, by rfl⟩ : syracuseStep 665135 = 997703) B997703
theorem B666063 : Blo 662308 666063 := bstep (se 1 (by rfl) ⟨499547, by rfl⟩ : syracuseStep 666063 = 999095) B999095
theorem B993791 : Blo 662308 993791 := bstep (se 1 (by rfl) ⟨745343, by rfl⟩ : syracuseStep 993791 = 1490687) B1490687
theorem B3844907 : Blo 662308 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B8531351 : Blo 662308 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B1682927 : Blo 662308 1682927 := bstep (se 1 (by rfl) ⟨1262195, by rfl⟩ : syracuseStep 1682927 = 2524391) B2524391
theorem B6401591 : Blo 662308 6401591 := bstep (se 1 (by rfl) ⟨4801193, by rfl⟩ : syracuseStep 6401591 = 9602387) B9602387
theorem B995423 : Blo 662308 995423 := bstep (se 1 (by rfl) ⟨746567, by rfl⟩ : syracuseStep 995423 = 1493135) B1493135
theorem B995753 : Blo 662308 995753 := bstep (se 2 (by rfl) ⟨373407, by rfl⟩ : syracuseStep 995753 = 746815) B746815
theorem B53195381 : Blo 662308 53195381 := bstep (se 5 (by rfl) ⟨2493533, by rfl⟩ : syracuseStep 53195381 = 4987067) B4987067
theorem B5387069 : Blo 662308 5387069 := bstep (se 3 (by rfl) ⟨1010075, by rfl⟩ : syracuseStep 5387069 = 2020151) B2020151
theorem B622966949 : Blo 662308 622966949 := bstep (se 4 (by rfl) ⟨58403151, by rfl⟩ : syracuseStep 622966949 = 116806303) B116806303
theorem B997991 : Blo 662308 997991 := bstep (se 1 (by rfl) ⟨748493, by rfl⟩ : syracuseStep 997991 = 1496987) B1496987
theorem B998015 : Blo 662308 998015 := bstep (se 1 (by rfl) ⟨748511, by rfl⟩ : syracuseStep 998015 = 1497023) B1497023
theorem B1686521 : Blo 662308 1686521 := bstep (se 2 (by rfl) ⟨632445, by rfl⟩ : syracuseStep 1686521 = 1264891) B1264891
theorem B3194797 : Blo 662308 3194797 := bstep (se 3 (by rfl) ⟨599024, by rfl⟩ : syracuseStep 3194797 = 1198049) B1198049
theorem B1490975 : Blo 662308 1490975 := bstep (se 1 (by rfl) ⟨1118231, by rfl⟩ : syracuseStep 1490975 = 2236463) B2236463
theorem B7553897 : Blo 662308 7553897 := bstep (se 2 (by rfl) ⟨2832711, by rfl⟩ : syracuseStep 7553897 = 5665423) B5665423
theorem B1492559 : Blo 662308 1492559 := bstep (se 1 (by rfl) ⟨1119419, by rfl⟩ : syracuseStep 1492559 = 2238839) B2238839
theorem B7555355 : Blo 662308 7555355 := bstep (se 1 (by rfl) ⟨5666516, by rfl⟩ : syracuseStep 7555355 = 11333033) B11333033
theorem B1493279 : Blo 662308 1493279 := bstep (se 1 (by rfl) ⟨1119959, by rfl⟩ : syracuseStep 1493279 = 2239919) B2239919
theorem B1493351 : Blo 662308 1493351 := bstep (se 1 (by rfl) ⟨1120013, by rfl⟩ : syracuseStep 1493351 = 2240027) B2240027
theorem B2019325 : Blo 662308 2019325 := bstep (se 3 (by rfl) ⟨378623, by rfl⟩ : syracuseStep 2019325 = 757247) B757247
theorem B5690027 : Blo 662308 5690027 := bstep (se 1 (by rfl) ⟨4267520, by rfl⟩ : syracuseStep 5690027 = 8535041) B8535041
theorem B3789503 : Blo 662308 3789503 := bstep (se 1 (by rfl) ⟨2842127, by rfl⟩ : syracuseStep 3789503 = 5684255) B5684255
theorem B7197599 : Blo 662308 7197599 := bstep (se 1 (by rfl) ⟨5398199, by rfl⟩ : syracuseStep 7197599 = 10796399) B10796399
theorem B709759 : Blo 662308 709759 := bstep (se 1 (by rfl) ⟨532319, by rfl⟩ : syracuseStep 709759 = 1064639) B1064639
theorem B1497599 : Blo 662308 1497599 := bstep (se 1 (by rfl) ⟨1123199, by rfl⟩ : syracuseStep 1497599 = 2246399) B2246399
theorem B1891687 : Blo 662308 1891687 := bstep (se 1 (by rfl) ⟨1418765, by rfl⟩ : syracuseStep 1891687 = 2837531) B2837531
theorem B194602027 : Blo 662308 194602027 := bstep (se 1 (by rfl) ⟨145951520, by rfl⟩ : syracuseStep 194602027 = 291903041) B291903041
theorem B5662007 : Blo 662308 5662007 := bstep (se 1 (by rfl) ⟨4246505, by rfl⟩ : syracuseStep 5662007 = 8493011) B8493011
theorem B747391 : Blo 662308 747391 := bstep (se 1 (by rfl) ⟨560543, by rfl⟩ : syracuseStep 747391 = 1121087) B1121087
theorem B3370247 : Blo 662308 3370247 := bstep (se 1 (by rfl) ⟨2527685, by rfl⟩ : syracuseStep 3370247 = 5055371) B5055371
theorem B6387443 : Blo 662308 6387443 := bstep (se 1 (by rfl) ⟨4790582, by rfl⟩ : syracuseStep 6387443 = 9581165) B9581165
theorem B7765919 : Blo 662308 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B12126095 : Blo 662308 12126095 := bstep (se 1 (by rfl) ⟨9094571, by rfl⟩ : syracuseStep 12126095 = 18189143) B18189143
theorem B2526335 : Blo 662308 2526335 := bstep (se 1 (by rfl) ⟨1894751, by rfl⟩ : syracuseStep 2526335 = 3789503) B3789503
theorem B9573319 : Blo 662308 9573319 := bstep (se 1 (by rfl) ⟨7179989, by rfl⟩ : syracuseStep 9573319 = 14359979) B14359979
theorem B2692433 : Blo 662308 2692433 := bstep (se 2 (by rfl) ⟨1009662, by rfl⟩ : syracuseStep 2692433 = 2019325) B2019325
theorem B3774397 : Blo 662308 3774397 := bstep (se 3 (by rfl) ⟨707699, by rfl⟩ : syracuseStep 3774397 = 1415399) B1415399
theorem B3774671 : Blo 662308 3774671 := bstep (se 1 (by rfl) ⟨2831003, by rfl⟩ : syracuseStep 3774671 = 5662007) B5662007
theorem B662527 : Blo 662308 662527 := bstep (se 1 (by rfl) ⟨496895, by rfl⟩ : syracuseStep 662527 = 993791) B993791
theorem B2563271 : Blo 662308 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B1121951 : Blo 662308 1121951 := bstep (se 1 (by rfl) ⟨841463, by rfl⟩ : syracuseStep 1121951 = 1682927) B1682927
theorem B4267727 : Blo 662308 4267727 := bstep (se 1 (by rfl) ⟨3200795, by rfl⟩ : syracuseStep 4267727 = 6401591) B6401591
theorem B2236409 : Blo 662308 2236409 := bstep (se 2 (by rfl) ⟨838653, by rfl⟩ : syracuseStep 2236409 = 1677307) B1677307
theorem B663615 : Blo 662308 663615 := bstep (se 1 (by rfl) ⟨497711, by rfl⟩ : syracuseStep 663615 = 995423) B995423
theorem B663835 : Blo 662308 663835 := bstep (se 1 (by rfl) ⟨497876, by rfl⟩ : syracuseStep 663835 = 995753) B995753
theorem B35463587 : Blo 662308 35463587 := bstep (se 1 (by rfl) ⟨26597690, by rfl⟩ : syracuseStep 35463587 = 53195381) B53195381
theorem B415311299 : Blo 662308 415311299 := bstep (se 1 (by rfl) ⟨311483474, by rfl⟩ : syracuseStep 415311299 = 622966949) B622966949
theorem B665327 : Blo 662308 665327 := bstep (se 1 (by rfl) ⟨498995, by rfl⟩ : syracuseStep 665327 = 997991) B997991
theorem B665343 : Blo 662308 665343 := bstep (se 1 (by rfl) ⟨499007, by rfl⟩ : syracuseStep 665343 = 998015) B998015
theorem B1124347 : Blo 662308 1124347 := bstep (se 1 (by rfl) ⟨843260, by rfl⟩ : syracuseStep 1124347 = 1686521) B1686521
theorem B993983 : Blo 662308 993983 := bstep (se 1 (by rfl) ⟨745487, by rfl⟩ : syracuseStep 993983 = 1490975) B1490975
theorem B995039 : Blo 662308 995039 := bstep (se 1 (by rfl) ⟨746279, by rfl⟩ : syracuseStep 995039 = 1492559) B1492559
theorem B259469369 : Blo 662308 259469369 := bstep (se 2 (by rfl) ⟨97301013, by rfl⟩ : syracuseStep 259469369 = 194602027) B194602027
theorem B995519 : Blo 662308 995519 := bstep (se 1 (by rfl) ⟨746639, by rfl⟩ : syracuseStep 995519 = 1493279) B1493279
theorem B995567 : Blo 662308 995567 := bstep (se 1 (by rfl) ⟨746675, by rfl⟩ : syracuseStep 995567 = 1493351) B1493351
theorem B996521 : Blo 662308 996521 := bstep (se 2 (by rfl) ⟨373695, by rfl⟩ : syracuseStep 996521 = 747391) B747391
theorem B4798399 : Blo 662308 4798399 := bstep (se 1 (by rfl) ⟨3598799, by rfl⟩ : syracuseStep 4798399 = 7197599) B7197599
theorem B998399 : Blo 662308 998399 := bstep (se 1 (by rfl) ⟨748799, by rfl⟩ : syracuseStep 998399 = 1497599) B1497599
theorem B3784603 : Blo 662308 3784603 := bstep (se 1 (by rfl) ⟨2838452, by rfl⟩ : syracuseStep 3784603 = 5676905) B5676905
theorem B2246831 : Blo 662308 2246831 := bstep (se 1 (by rfl) ⟨1685123, by rfl⟩ : syracuseStep 2246831 = 3370247) B3370247
theorem B5687567 : Blo 662308 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B3591379 : Blo 662308 3591379 := bstep (se 1 (by rfl) ⟨2693534, by rfl⟩ : syracuseStep 3591379 = 5387069) B5387069
theorem B6378911 : Blo 662308 6378911 := bstep (se 1 (by rfl) ⟨4784183, by rfl⟩ : syracuseStep 6378911 = 9568367) B9568367
theorem B5035931 : Blo 662308 5035931 := bstep (se 1 (by rfl) ⟨3776948, by rfl⟩ : syracuseStep 5035931 = 7553897) B7553897
theorem B5036903 : Blo 662308 5036903 := bstep (se 1 (by rfl) ⟨3777677, by rfl⟩ : syracuseStep 5036903 = 7555355) B7555355
theorem B3793351 : Blo 662308 3793351 := bstep (se 1 (by rfl) ⟨2845013, by rfl⟩ : syracuseStep 3793351 = 5690027) B5690027
theorem B946345 : Blo 662308 946345 := bstep (se 2 (by rfl) ⟨354879, by rfl⟩ : syracuseStep 946345 = 709759) B709759
theorem B4258295 : Blo 662308 4258295 := bstep (se 1 (by rfl) ⟨3193721, by rfl⟩ : syracuseStep 4258295 = 6387443) B6387443
theorem B2522249 : Blo 662308 2522249 := bstep (se 2 (by rfl) ⟨945843, by rfl⟩ : syracuseStep 2522249 = 1891687) B1891687
theorem B4259729 : Blo 662308 4259729 := bstep (se 2 (by rfl) ⟨1597398, by rfl⟩ : syracuseStep 4259729 = 3194797) B3194797
theorem B5177279 : Blo 662308 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B4788505 : Blo 662308 4788505 := bstep (se 2 (by rfl) ⟨1795689, by rfl⟩ : syracuseStep 4788505 = 3591379) B3591379
theorem B378278261 : Blo 662308 378278261 := bstep (se 5 (by rfl) ⟨17731793, by rfl⟩ : syracuseStep 378278261 = 35463587) B35463587
theorem B1708847 : Blo 662308 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B662655 : Blo 662308 662655 := bstep (se 1 (by rfl) ⟨496991, by rfl⟩ : syracuseStep 662655 = 993983) B993983
theorem B663359 : Blo 662308 663359 := bstep (se 1 (by rfl) ⟨497519, by rfl⟩ : syracuseStep 663359 = 995039) B995039
theorem B6397865 : Blo 662308 6397865 := bstep (se 2 (by rfl) ⟨2399199, by rfl⟩ : syracuseStep 6397865 = 4798399) B4798399
theorem B663679 : Blo 662308 663679 := bstep (se 1 (by rfl) ⟨497759, by rfl⟩ : syracuseStep 663679 = 995519) B995519
theorem B663711 : Blo 662308 663711 := bstep (se 1 (by rfl) ⟨497783, by rfl⟩ : syracuseStep 663711 = 995567) B995567
theorem B664347 : Blo 662308 664347 := bstep (se 1 (by rfl) ⟨498260, by rfl⟩ : syracuseStep 664347 = 996521) B996521
theorem B665599 : Blo 662308 665599 := bstep (se 1 (by rfl) ⟨499199, by rfl⟩ : syracuseStep 665599 = 998399) B998399
theorem B1681499 : Blo 662308 1681499 := bstep (se 1 (by rfl) ⟨1261124, by rfl⟩ : syracuseStep 1681499 = 2522249) B2522249
theorem B13806077 : Blo 662308 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B5057801 : Blo 662308 5057801 := bstep (se 2 (by rfl) ⟨1896675, by rfl⟩ : syracuseStep 5057801 = 3793351) B3793351
theorem B1684223 : Blo 662308 1684223 := bstep (se 1 (by rfl) ⟨1263167, by rfl⟩ : syracuseStep 1684223 = 2526335) B2526335
theorem B3357287 : Blo 662308 3357287 := bstep (se 1 (by rfl) ⟨2517965, by rfl⟩ : syracuseStep 3357287 = 5035931) B5035931
theorem B3357935 : Blo 662308 3357935 := bstep (se 1 (by rfl) ⟨2518451, by rfl⟩ : syracuseStep 3357935 = 5036903) B5036903
theorem B1490939 : Blo 662308 1490939 := bstep (se 1 (by rfl) ⟨1118204, by rfl⟩ : syracuseStep 1490939 = 2236409) B2236409
theorem B1261793 : Blo 662308 1261793 := bstep (se 2 (by rfl) ⟨473172, by rfl⟩ : syracuseStep 1261793 = 946345) B946345
theorem B276874199 : Blo 662308 276874199 := bstep (se 1 (by rfl) ⟨207655649, by rfl⟩ : syracuseStep 276874199 = 415311299) B415311299
theorem B12764425 : Blo 662308 12764425 := bstep (se 2 (by rfl) ⟨4786659, by rfl⟩ : syracuseStep 12764425 = 9573319) B9573319
theorem B5032529 : Blo 662308 5032529 := bstep (se 2 (by rfl) ⟨1887198, by rfl⟩ : syracuseStep 5032529 = 3774397) B3774397
theorem B2838863 : Blo 662308 2838863 := bstep (se 1 (by rfl) ⟨2129147, by rfl⟩ : syracuseStep 2838863 = 4258295) B4258295
theorem B11359277 : Blo 662308 11359277 := bstep (se 3 (by rfl) ⟨2129864, by rfl⟩ : syracuseStep 11359277 = 4259729) B4259729
theorem B8084063 : Blo 662308 8084063 := bstep (se 1 (by rfl) ⟨6063047, by rfl⟩ : syracuseStep 8084063 = 12126095) B12126095
theorem B1497887 : Blo 662308 1497887 := bstep (se 1 (by rfl) ⟨1123415, by rfl⟩ : syracuseStep 1497887 = 2246831) B2246831
theorem B3791711 : Blo 662308 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B1499129 : Blo 662308 1499129 := bstep (se 2 (by rfl) ⟨562173, by rfl⟩ : syracuseStep 1499129 = 1124347) B1124347
theorem B1794955 : Blo 662308 1794955 := bstep (se 1 (by rfl) ⟨1346216, by rfl⟩ : syracuseStep 1794955 = 2692433) B2692433
theorem B4252607 : Blo 662308 4252607 := bstep (se 1 (by rfl) ⟨3189455, by rfl⟩ : syracuseStep 4252607 = 6378911) B6378911
theorem B2516447 : Blo 662308 2516447 := bstep (se 1 (by rfl) ⟨1887335, by rfl⟩ : syracuseStep 2516447 = 3774671) B3774671
theorem B747967 : Blo 662308 747967 := bstep (se 1 (by rfl) ⟨560975, by rfl⟩ : syracuseStep 747967 = 1121951) B1121951
theorem B2845151 : Blo 662308 2845151 := bstep (se 1 (by rfl) ⟨2133863, by rfl⟩ : syracuseStep 2845151 = 4267727) B4267727
theorem B172979579 : Blo 662308 172979579 := bstep (se 1 (by rfl) ⟨129734684, by rfl⟩ : syracuseStep 172979579 = 259469369) B259469369
theorem B5046137 : Blo 662308 5046137 := bstep (se 2 (by rfl) ⟨1892301, by rfl⟩ : syracuseStep 5046137 = 3784603) B3784603
theorem B184582799 : Blo 662308 184582799 := bstep (se 1 (by rfl) ⟨138437099, by rfl⟩ : syracuseStep 184582799 = 276874199) B276874199
theorem B2393273 : Blo 662308 2393273 := bstep (se 2 (by rfl) ⟨897477, by rfl⟩ : syracuseStep 2393273 = 1794955) B1794955
theorem B252185507 : Blo 662308 252185507 := bstep (se 1 (by rfl) ⟨189139130, by rfl⟩ : syracuseStep 252185507 = 378278261) B378278261
theorem B7572851 : Blo 662308 7572851 := bstep (se 1 (by rfl) ⟨5679638, by rfl⟩ : syracuseStep 7572851 = 11359277) B11359277
theorem B2527807 : Blo 662308 2527807 := bstep (se 1 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 2527807 = 3791711) B3791711
theorem B4265243 : Blo 662308 4265243 := bstep (se 1 (by rfl) ⟨3198932, by rfl⟩ : syracuseStep 4265243 = 6397865) B6397865
theorem B1677631 : Blo 662308 1677631 := bstep (se 1 (by rfl) ⟨1258223, by rfl⟩ : syracuseStep 1677631 = 2516447) B2516447
theorem B1120999 : Blo 662308 1120999 := bstep (se 1 (by rfl) ⟨840749, by rfl⟩ : syracuseStep 1120999 = 1681499) B1681499
theorem B1122815 : Blo 662308 1122815 := bstep (se 1 (by rfl) ⟨842111, by rfl⟩ : syracuseStep 1122815 = 1684223) B1684223
theorem B115319719 : Blo 662308 115319719 := bstep (se 1 (by rfl) ⟨86489789, by rfl⟩ : syracuseStep 115319719 = 172979579) B172979579
theorem B2238191 : Blo 662308 2238191 := bstep (se 1 (by rfl) ⟨1678643, by rfl⟩ : syracuseStep 2238191 = 3357287) B3357287
theorem B2238623 : Blo 662308 2238623 := bstep (se 1 (by rfl) ⟨1678967, by rfl⟩ : syracuseStep 2238623 = 3357935) B3357935
theorem B993959 : Blo 662308 993959 := bstep (se 1 (by rfl) ⟨745469, by rfl⟩ : syracuseStep 993959 = 1490939) B1490939
theorem B17019233 : Blo 662308 17019233 := bstep (se 2 (by rfl) ⟨6382212, by rfl⟩ : syracuseStep 17019233 = 12764425) B12764425
theorem B3355019 : Blo 662308 3355019 := bstep (se 1 (by rfl) ⟨2516264, by rfl⟩ : syracuseStep 3355019 = 5032529) B5032529
theorem B997289 : Blo 662308 997289 := bstep (se 2 (by rfl) ⟨373983, by rfl⟩ : syracuseStep 997289 = 747967) B747967
theorem B998591 : Blo 662308 998591 := bstep (se 1 (by rfl) ⟨748943, by rfl⟩ : syracuseStep 998591 = 1497887) B1497887
theorem B999419 : Blo 662308 999419 := bstep (se 1 (by rfl) ⟨749564, by rfl⟩ : syracuseStep 999419 = 1499129) B1499129
theorem B2835071 : Blo 662308 2835071 := bstep (se 1 (by rfl) ⟨2126303, by rfl⟩ : syracuseStep 2835071 = 4252607) B4252607
theorem B36816205 : Blo 662308 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B3364091 : Blo 662308 3364091 := bstep (se 1 (by rfl) ⟨2523068, by rfl⟩ : syracuseStep 3364091 = 5046137) B5046137
theorem B841195 : Blo 662308 841195 := bstep (se 1 (by rfl) ⟨630896, by rfl⟩ : syracuseStep 841195 = 1261793) B1261793
theorem B1892575 : Blo 662308 1892575 := bstep (se 1 (by rfl) ⟨1419431, by rfl⟩ : syracuseStep 1892575 = 2838863) B2838863
theorem B1139231 : Blo 662308 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B6384673 : Blo 662308 6384673 := bstep (se 2 (by rfl) ⟨2394252, by rfl⟩ : syracuseStep 6384673 = 4788505) B4788505
theorem B21557501 : Blo 662308 21557501 := bstep (se 3 (by rfl) ⟨4042031, by rfl⟩ : syracuseStep 21557501 = 8084063) B8084063
theorem B1896767 : Blo 662308 1896767 := bstep (se 1 (by rfl) ⟨1422575, by rfl⟩ : syracuseStep 1896767 = 2845151) B2845151
theorem B3371867 : Blo 662308 3371867 := bstep (se 1 (by rfl) ⟨2528900, by rfl⟩ : syracuseStep 3371867 = 5057801) B5057801
theorem B2523433 : Blo 662308 2523433 := bstep (se 2 (by rfl) ⟨946287, by rfl⟩ : syracuseStep 2523433 = 1892575) B1892575
theorem B49088273 : Blo 662308 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B5048567 : Blo 662308 5048567 := bstep (se 1 (by rfl) ⟨3786425, by rfl⟩ : syracuseStep 5048567 = 7572851) B7572851
theorem B662639 : Blo 662308 662639 := bstep (se 1 (by rfl) ⟨496979, by rfl⟩ : syracuseStep 662639 = 993959) B993959
theorem B1121593 : Blo 662308 1121593 := bstep (se 2 (by rfl) ⟨420597, by rfl⟩ : syracuseStep 1121593 = 841195) B841195
theorem B11346155 : Blo 662308 11346155 := bstep (se 1 (by rfl) ⟨8509616, by rfl⟩ : syracuseStep 11346155 = 17019233) B17019233
theorem B2236679 : Blo 662308 2236679 := bstep (se 1 (by rfl) ⟨1677509, by rfl⟩ : syracuseStep 2236679 = 3355019) B3355019
theorem B2236841 : Blo 662308 2236841 := bstep (se 2 (by rfl) ⟨838815, by rfl⟩ : syracuseStep 2236841 = 1677631) B1677631
theorem B664859 : Blo 662308 664859 := bstep (se 1 (by rfl) ⟨498644, by rfl⟩ : syracuseStep 664859 = 997289) B997289
theorem B665727 : Blo 662308 665727 := bstep (se 1 (by rfl) ⟨499295, by rfl⟩ : syracuseStep 665727 = 998591) B998591
theorem B666279 : Blo 662308 666279 := bstep (se 1 (by rfl) ⟨499709, by rfl⟩ : syracuseStep 666279 = 999419) B999419
theorem B123055199 : Blo 662308 123055199 := bstep (se 1 (by rfl) ⟨92291399, by rfl⟩ : syracuseStep 123055199 = 184582799) B184582799
theorem B153759625 : Blo 662308 153759625 := bstep (se 2 (by rfl) ⟨57659859, by rfl⟩ : syracuseStep 153759625 = 115319719) B115319719
theorem B2242727 : Blo 662308 2242727 := bstep (se 1 (by rfl) ⟨1682045, by rfl⟩ : syracuseStep 2242727 = 3364091) B3364091
theorem B1492127 : Blo 662308 1492127 := bstep (se 1 (by rfl) ⟨1119095, by rfl⟩ : syracuseStep 1492127 = 2238191) B2238191
theorem B1492415 : Blo 662308 1492415 := bstep (se 1 (by rfl) ⟨1119311, by rfl⟩ : syracuseStep 1492415 = 2238623) B2238623
theorem B14371667 : Blo 662308 14371667 := bstep (se 1 (by rfl) ⟨10778750, by rfl⟩ : syracuseStep 14371667 = 21557501) B21557501
theorem B1264511 : Blo 662308 1264511 := bstep (se 1 (by rfl) ⟨948383, by rfl⟩ : syracuseStep 1264511 = 1896767) B1896767
theorem B2247911 : Blo 662308 2247911 := bstep (se 1 (by rfl) ⟨1685933, by rfl⟩ : syracuseStep 2247911 = 3371867) B3371867
theorem B1494665 : Blo 662308 1494665 := bstep (se 2 (by rfl) ⟨560499, by rfl⟩ : syracuseStep 1494665 = 1120999) B1120999
theorem B1890047 : Blo 662308 1890047 := bstep (se 1 (by rfl) ⟨1417535, by rfl⟩ : syracuseStep 1890047 = 2835071) B2835071
theorem B3037949 : Blo 662308 3037949 := bstep (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) B1139231
theorem B168123671 : Blo 662308 168123671 := bstep (se 1 (by rfl) ⟨126092753, by rfl⟩ : syracuseStep 168123671 = 252185507) B252185507
theorem B6382061 : Blo 662308 6382061 := bstep (se 3 (by rfl) ⟨1196636, by rfl⟩ : syracuseStep 6382061 = 2393273) B2393273
theorem B2843495 : Blo 662308 2843495 := bstep (se 1 (by rfl) ⟨2132621, by rfl⟩ : syracuseStep 2843495 = 4265243) B4265243
theorem B8512897 : Blo 662308 8512897 := bstep (se 2 (by rfl) ⟨3192336, by rfl⟩ : syracuseStep 8512897 = 6384673) B6384673
theorem B748543 : Blo 662308 748543 := bstep (se 1 (by rfl) ⟨561407, by rfl⟩ : syracuseStep 748543 = 1122815) B1122815
theorem B3370409 : Blo 662308 3370409 := bstep (se 2 (by rfl) ⟨1263903, by rfl⟩ : syracuseStep 3370409 = 2527807) B2527807
theorem B523608245 : Blo 662308 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B994751 : Blo 662308 994751 := bstep (se 1 (by rfl) ⟨746063, by rfl⟩ : syracuseStep 994751 = 1492127) B1492127
theorem B994943 : Blo 662308 994943 := bstep (se 1 (by rfl) ⟨746207, by rfl⟩ : syracuseStep 994943 = 1492415) B1492415
theorem B11350529 : Blo 662308 11350529 := bstep (se 2 (by rfl) ⟨4256448, by rfl⟩ : syracuseStep 11350529 = 8512897) B8512897
theorem B9581111 : Blo 662308 9581111 := bstep (se 1 (by rfl) ⟨7185833, by rfl⟩ : syracuseStep 9581111 = 14371667) B14371667
theorem B996443 : Blo 662308 996443 := bstep (se 1 (by rfl) ⟨747332, by rfl⟩ : syracuseStep 996443 = 1494665) B1494665
theorem B1260031 : Blo 662308 1260031 := bstep (se 1 (by rfl) ⟨945023, by rfl⟩ : syracuseStep 1260031 = 1890047) B1890047
theorem B998057 : Blo 662308 998057 := bstep (se 2 (by rfl) ⟨374271, by rfl⟩ : syracuseStep 998057 = 748543) B748543
theorem B112082447 : Blo 662308 112082447 := bstep (se 1 (by rfl) ⟨84061835, by rfl⟩ : syracuseStep 112082447 = 168123671) B168123671
theorem B1491119 : Blo 662308 1491119 := bstep (se 1 (by rfl) ⟨1118339, by rfl⟩ : syracuseStep 1491119 = 2236679) B2236679
theorem B1491227 : Blo 662308 1491227 := bstep (se 1 (by rfl) ⟨1118420, by rfl⟩ : syracuseStep 1491227 = 2236841) B2236841
theorem B82036799 : Blo 662308 82036799 := bstep (se 1 (by rfl) ⟨61527599, by rfl⟩ : syracuseStep 82036799 = 123055199) B123055199
theorem B2246939 : Blo 662308 2246939 := bstep (se 1 (by rfl) ⟨1685204, by rfl⟩ : syracuseStep 2246939 = 3370409) B3370409
theorem B1495151 : Blo 662308 1495151 := bstep (se 1 (by rfl) ⟨1121363, by rfl⟩ : syracuseStep 1495151 = 2242727) B2242727
theorem B1495457 : Blo 662308 1495457 := bstep (se 2 (by rfl) ⟨560796, by rfl⟩ : syracuseStep 1495457 = 1121593) B1121593
theorem B3364577 : Blo 662308 3364577 := bstep (se 2 (by rfl) ⟨1261716, by rfl⟩ : syracuseStep 3364577 = 2523433) B2523433
theorem B3365711 : Blo 662308 3365711 := bstep (se 1 (by rfl) ⟨2524283, by rfl⟩ : syracuseStep 3365711 = 5048567) B5048567
theorem B1498607 : Blo 662308 1498607 := bstep (se 1 (by rfl) ⟨1123955, by rfl⟩ : syracuseStep 1498607 = 2247911) B2247911
theorem B2025299 : Blo 662308 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B7564103 : Blo 662308 7564103 := bstep (se 1 (by rfl) ⟨5673077, by rfl⟩ : syracuseStep 7564103 = 11346155) B11346155
theorem B4254707 : Blo 662308 4254707 := bstep (se 1 (by rfl) ⟨3191030, by rfl⟩ : syracuseStep 4254707 = 6382061) B6382061
theorem B1895663 : Blo 662308 1895663 := bstep (se 1 (by rfl) ⟨1421747, by rfl⟩ : syracuseStep 1895663 = 2843495) B2843495
theorem B3372029 : Blo 662308 3372029 := bstep (se 3 (by rfl) ⟨632255, by rfl⟩ : syracuseStep 3372029 = 1264511) B1264511
theorem B820051333 : Blo 662308 820051333 := bstep (se 4 (by rfl) ⟨76879812, by rfl⟩ : syracuseStep 820051333 = 153759625) B153759625
theorem B54691199 : Blo 662308 54691199 := bstep (se 1 (by rfl) ⟨41018399, by rfl⟩ : syracuseStep 54691199 = 82036799) B82036799
theorem B1350199 : Blo 662308 1350199 := bstep (se 1 (by rfl) ⟨1012649, by rfl⟩ : syracuseStep 1350199 = 2025299) B2025299
theorem B663167 : Blo 662308 663167 := bstep (se 1 (by rfl) ⟨497375, by rfl⟩ : syracuseStep 663167 = 994751) B994751
theorem B663295 : Blo 662308 663295 := bstep (se 1 (by rfl) ⟨497471, by rfl⟩ : syracuseStep 663295 = 994943) B994943
theorem B1680041 : Blo 662308 1680041 := bstep (se 2 (by rfl) ⟨630015, by rfl⟩ : syracuseStep 1680041 = 1260031) B1260031
theorem B664295 : Blo 662308 664295 := bstep (se 1 (by rfl) ⟨498221, by rfl⟩ : syracuseStep 664295 = 996443) B996443
theorem B665371 : Blo 662308 665371 := bstep (se 1 (by rfl) ⟨499028, by rfl⟩ : syracuseStep 665371 = 998057) B998057
theorem B74721631 : Blo 662308 74721631 := bstep (se 1 (by rfl) ⟨56041223, by rfl⟩ : syracuseStep 74721631 = 112082447) B112082447
theorem B994079 : Blo 662308 994079 := bstep (se 1 (by rfl) ⟨745559, by rfl⟩ : syracuseStep 994079 = 1491119) B1491119
theorem B994151 : Blo 662308 994151 := bstep (se 1 (by rfl) ⟨745613, by rfl⟩ : syracuseStep 994151 = 1491227) B1491227
theorem B996767 : Blo 662308 996767 := bstep (se 1 (by rfl) ⟨747575, by rfl⟩ : syracuseStep 996767 = 1495151) B1495151
theorem B996971 : Blo 662308 996971 := bstep (se 1 (by rfl) ⟨747728, by rfl⟩ : syracuseStep 996971 = 1495457) B1495457
theorem B2243051 : Blo 662308 2243051 := bstep (se 1 (by rfl) ⟨1682288, by rfl⟩ : syracuseStep 2243051 = 3364577) B3364577
theorem B2243807 : Blo 662308 2243807 := bstep (se 1 (by rfl) ⟨1682855, by rfl⟩ : syracuseStep 2243807 = 3365711) B3365711
theorem B999071 : Blo 662308 999071 := bstep (se 1 (by rfl) ⟨749303, by rfl⟩ : syracuseStep 999071 = 1498607) B1498607
theorem B2836471 : Blo 662308 2836471 := bstep (se 1 (by rfl) ⟨2127353, by rfl⟩ : syracuseStep 2836471 = 4254707) B4254707
theorem B1263775 : Blo 662308 1263775 := bstep (se 1 (by rfl) ⟨947831, by rfl⟩ : syracuseStep 1263775 = 1895663) B1895663
theorem B17494428437 : Blo 662308 17494428437 := bstep (se 6 (by rfl) ⟨410025666, by rfl⟩ : syracuseStep 17494428437 = 820051333) B820051333
theorem B2248019 : Blo 662308 2248019 := bstep (se 1 (by rfl) ⟨1686014, by rfl⟩ : syracuseStep 2248019 = 3372029) B3372029
theorem B1497959 : Blo 662308 1497959 := bstep (se 1 (by rfl) ⟨1123469, by rfl⟩ : syracuseStep 1497959 = 2246939) B2246939
theorem B349072163 : Blo 662308 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B5042735 : Blo 662308 5042735 := bstep (se 1 (by rfl) ⟨3782051, by rfl⟩ : syracuseStep 5042735 = 7564103) B7564103
theorem B7567019 : Blo 662308 7567019 := bstep (se 1 (by rfl) ⟨5675264, by rfl⟩ : syracuseStep 7567019 = 11350529) B11350529
theorem B6387407 : Blo 662308 6387407 := bstep (se 1 (by rfl) ⟨4790555, by rfl⟩ : syracuseStep 6387407 = 9581111) B9581111
theorem B11662952291 : Blo 662308 11662952291 := bstep (se 1 (by rfl) ⟨8747214218, by rfl⟩ : syracuseStep 11662952291 = 17494428437) B17494428437
theorem B1120027 : Blo 662308 1120027 := bstep (se 1 (by rfl) ⟨840020, by rfl⟩ : syracuseStep 1120027 = 1680041) B1680041
theorem B662719 : Blo 662308 662719 := bstep (se 1 (by rfl) ⟨497039, by rfl⟩ : syracuseStep 662719 = 994079) B994079
theorem B662767 : Blo 662308 662767 := bstep (se 1 (by rfl) ⟨497075, by rfl⟩ : syracuseStep 662767 = 994151) B994151
theorem B664511 : Blo 662308 664511 := bstep (se 1 (by rfl) ⟨498383, by rfl⟩ : syracuseStep 664511 = 996767) B996767
theorem B664647 : Blo 662308 664647 := bstep (se 1 (by rfl) ⟨498485, by rfl⟩ : syracuseStep 664647 = 996971) B996971
theorem B666047 : Blo 662308 666047 := bstep (se 1 (by rfl) ⟨499535, by rfl⟩ : syracuseStep 666047 = 999071) B999071
theorem B3781961 : Blo 662308 3781961 := bstep (se 2 (by rfl) ⟨1418235, by rfl⟩ : syracuseStep 3781961 = 2836471) B2836471
theorem B1685033 : Blo 662308 1685033 := bstep (se 2 (by rfl) ⟨631887, by rfl⟩ : syracuseStep 1685033 = 1263775) B1263775
theorem B99628841 : Blo 662308 99628841 := bstep (se 2 (by rfl) ⟨37360815, by rfl⟩ : syracuseStep 99628841 = 74721631) B74721631
theorem B998639 : Blo 662308 998639 := bstep (se 1 (by rfl) ⟨748979, by rfl⟩ : syracuseStep 998639 = 1497959) B1497959
theorem B3361823 : Blo 662308 3361823 := bstep (se 1 (by rfl) ⟨2521367, by rfl⟩ : syracuseStep 3361823 = 5042735) B5042735
theorem B1495367 : Blo 662308 1495367 := bstep (se 1 (by rfl) ⟨1121525, by rfl⟩ : syracuseStep 1495367 = 2243051) B2243051
theorem B1495871 : Blo 662308 1495871 := bstep (se 1 (by rfl) ⟨1121903, by rfl⟩ : syracuseStep 1495871 = 2243807) B2243807
theorem B36460799 : Blo 662308 36460799 := bstep (se 1 (by rfl) ⟨27345599, by rfl⟩ : syracuseStep 36460799 = 54691199) B54691199
theorem B1498679 : Blo 662308 1498679 := bstep (se 1 (by rfl) ⟨1124009, by rfl⟩ : syracuseStep 1498679 = 2248019) B2248019
theorem B7201061 : Blo 662308 7201061 := bstep (se 4 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 7201061 = 1350199) B1350199
theorem B232714775 : Blo 662308 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B5044679 : Blo 662308 5044679 := bstep (se 1 (by rfl) ⟨3783509, by rfl⟩ : syracuseStep 5044679 = 7567019) B7567019
theorem B4258271 : Blo 662308 4258271 := bstep (se 1 (by rfl) ⟨3193703, by rfl⟩ : syracuseStep 4258271 = 6387407) B6387407
theorem B1123355 : Blo 662308 1123355 := bstep (se 1 (by rfl) ⟨842516, by rfl⟩ : syracuseStep 1123355 = 1685033) B1685033
theorem B665759 : Blo 662308 665759 := bstep (se 1 (by rfl) ⟨499319, by rfl⟩ : syracuseStep 665759 = 998639) B998639
theorem B7775301527 : Blo 662308 7775301527 := bstep (se 1 (by rfl) ⟨5831476145, by rfl⟩ : syracuseStep 7775301527 = 11662952291) B11662952291
theorem B2241215 : Blo 662308 2241215 := bstep (se 1 (by rfl) ⟨1680911, by rfl⟩ : syracuseStep 2241215 = 3361823) B3361823
theorem B996911 : Blo 662308 996911 := bstep (se 1 (by rfl) ⟨747683, by rfl⟩ : syracuseStep 996911 = 1495367) B1495367
theorem B997247 : Blo 662308 997247 := bstep (se 1 (by rfl) ⟨747935, by rfl⟩ : syracuseStep 997247 = 1495871) B1495871
theorem B999119 : Blo 662308 999119 := bstep (se 1 (by rfl) ⟨749339, by rfl⟩ : syracuseStep 999119 = 1498679) B1498679
theorem B4800707 : Blo 662308 4800707 := bstep (se 1 (by rfl) ⟨3600530, by rfl⟩ : syracuseStep 4800707 = 7201061) B7201061
theorem B1493369 : Blo 662308 1493369 := bstep (se 2 (by rfl) ⟨560013, by rfl⟩ : syracuseStep 1493369 = 1120027) B1120027
theorem B155143183 : Blo 662308 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B3363119 : Blo 662308 3363119 := bstep (se 1 (by rfl) ⟨2522339, by rfl⟩ : syracuseStep 3363119 = 5044679) B5044679
theorem B2838847 : Blo 662308 2838847 := bstep (se 1 (by rfl) ⟨2129135, by rfl⟩ : syracuseStep 2838847 = 4258271) B4258271
theorem B24307199 : Blo 662308 24307199 := bstep (se 1 (by rfl) ⟨18230399, by rfl⟩ : syracuseStep 24307199 = 36460799) B36460799
theorem B2521307 : Blo 662308 2521307 := bstep (se 1 (by rfl) ⟨1890980, by rfl⟩ : syracuseStep 2521307 = 3781961) B3781961
theorem B66419227 : Blo 662308 66419227 := bstep (se 1 (by rfl) ⟨49814420, by rfl⟩ : syracuseStep 66419227 = 99628841) B99628841
theorem B664607 : Blo 662308 664607 := bstep (se 1 (by rfl) ⟨498455, by rfl⟩ : syracuseStep 664607 = 996911) B996911
theorem B664831 : Blo 662308 664831 := bstep (se 1 (by rfl) ⟨498623, by rfl⟩ : syracuseStep 664831 = 997247) B997247
theorem B1680871 : Blo 662308 1680871 := bstep (se 1 (by rfl) ⟨1260653, by rfl⟩ : syracuseStep 1680871 = 2521307) B2521307
theorem B666079 : Blo 662308 666079 := bstep (se 1 (by rfl) ⟨499559, by rfl⟩ : syracuseStep 666079 = 999119) B999119
theorem B995579 : Blo 662308 995579 := bstep (se 1 (by rfl) ⟨746684, by rfl⟩ : syracuseStep 995579 = 1493369) B1493369
theorem B2242079 : Blo 662308 2242079 := bstep (se 1 (by rfl) ⟨1681559, by rfl⟩ : syracuseStep 2242079 = 3363119) B3363119
theorem B3785129 : Blo 662308 3785129 := bstep (se 2 (by rfl) ⟨1419423, by rfl⟩ : syracuseStep 3785129 = 2838847) B2838847
theorem B16204799 : Blo 662308 16204799 := bstep (se 1 (by rfl) ⟨12153599, by rfl⟩ : syracuseStep 16204799 = 24307199) B24307199
theorem B1494143 : Blo 662308 1494143 := bstep (se 1 (by rfl) ⟨1120607, by rfl⟩ : syracuseStep 1494143 = 2241215) B2241215
theorem B88558969 : Blo 662308 88558969 := bstep (se 2 (by rfl) ⟨33209613, by rfl⟩ : syracuseStep 88558969 = 66419227) B66419227
theorem B3200471 : Blo 662308 3200471 := bstep (se 1 (by rfl) ⟨2400353, by rfl⟩ : syracuseStep 3200471 = 4800707) B4800707
theorem B206857577 : Blo 662308 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B748903 : Blo 662308 748903 := bstep (se 1 (by rfl) ⟨561677, by rfl⟩ : syracuseStep 748903 = 1123355) B1123355
theorem B5183534351 : Blo 662308 5183534351 := bstep (se 1 (by rfl) ⟨3887650763, by rfl⟩ : syracuseStep 5183534351 = 7775301527) B7775301527
theorem B2523419 : Blo 662308 2523419 := bstep (se 1 (by rfl) ⟨1892564, by rfl⟩ : syracuseStep 2523419 = 3785129) B3785129
theorem B2133647 : Blo 662308 2133647 := bstep (se 1 (by rfl) ⟨1600235, by rfl⟩ : syracuseStep 2133647 = 3200471) B3200471
theorem B663719 : Blo 662308 663719 := bstep (se 1 (by rfl) ⟨497789, by rfl⟩ : syracuseStep 663719 = 995579) B995579
theorem B3455689567 : Blo 662308 3455689567 := bstep (se 1 (by rfl) ⟨2591767175, by rfl⟩ : syracuseStep 3455689567 = 5183534351) B5183534351
theorem B2241161 : Blo 662308 2241161 := bstep (se 2 (by rfl) ⟨840435, by rfl⟩ : syracuseStep 2241161 = 1680871) B1680871
theorem B996095 : Blo 662308 996095 := bstep (se 1 (by rfl) ⟨747071, by rfl⟩ : syracuseStep 996095 = 1494143) B1494143
theorem B998537 : Blo 662308 998537 := bstep (se 2 (by rfl) ⟨374451, by rfl⟩ : syracuseStep 998537 = 748903) B748903
theorem B118078625 : Blo 662308 118078625 := bstep (se 2 (by rfl) ⟨44279484, by rfl⟩ : syracuseStep 118078625 = 88558969) B88558969
theorem B137905051 : Blo 662308 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B1494719 : Blo 662308 1494719 := bstep (se 1 (by rfl) ⟨1121039, by rfl⟩ : syracuseStep 1494719 = 2242079) B2242079
theorem B43212797 : Blo 662308 43212797 := bstep (se 3 (by rfl) ⟨8102399, by rfl⟩ : syracuseStep 43212797 = 16204799) B16204799
theorem B28808531 : Blo 662308 28808531 := bstep (se 1 (by rfl) ⟨21606398, by rfl⟩ : syracuseStep 28808531 = 43212797) B43212797
theorem B664063 : Blo 662308 664063 := bstep (se 1 (by rfl) ⟨498047, by rfl⟩ : syracuseStep 664063 = 996095) B996095
theorem B665691 : Blo 662308 665691 := bstep (se 1 (by rfl) ⟨499268, by rfl⟩ : syracuseStep 665691 = 998537) B998537
theorem B78719083 : Blo 662308 78719083 := bstep (se 1 (by rfl) ⟨59039312, by rfl⟩ : syracuseStep 78719083 = 118078625) B118078625
theorem B1682279 : Blo 662308 1682279 := bstep (se 1 (by rfl) ⟨1261709, by rfl⟩ : syracuseStep 1682279 = 2523419) B2523419
theorem B4607586089 : Blo 662308 4607586089 := bstep (se 2 (by rfl) ⟨1727844783, by rfl⟩ : syracuseStep 4607586089 = 3455689567) B3455689567
theorem B183873401 : Blo 662308 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B1422431 : Blo 662308 1422431 := bstep (se 1 (by rfl) ⟨1066823, by rfl⟩ : syracuseStep 1422431 = 2133647) B2133647
theorem B996479 : Blo 662308 996479 := bstep (se 1 (by rfl) ⟨747359, by rfl⟩ : syracuseStep 996479 = 1494719) B1494719
theorem B1494107 : Blo 662308 1494107 := bstep (se 1 (by rfl) ⟨1120580, by rfl⟩ : syracuseStep 1494107 = 2241161) B2241161
theorem B19205687 : Blo 662308 19205687 := bstep (se 1 (by rfl) ⟨14404265, by rfl⟩ : syracuseStep 19205687 = 28808531) B28808531
theorem B1121519 : Blo 662308 1121519 := bstep (se 1 (by rfl) ⟨841139, by rfl⟩ : syracuseStep 1121519 = 1682279) B1682279
theorem B664319 : Blo 662308 664319 := bstep (se 1 (by rfl) ⟨498239, by rfl⟩ : syracuseStep 664319 = 996479) B996479
theorem B419835109 : Blo 662308 419835109 := bstep (se 4 (by rfl) ⟨39359541, by rfl⟩ : syracuseStep 419835109 = 78719083) B78719083
theorem B996071 : Blo 662308 996071 := bstep (se 1 (by rfl) ⟨747053, by rfl⟩ : syracuseStep 996071 = 1494107) B1494107
theorem B3071724059 : Blo 662308 3071724059 := bstep (se 1 (by rfl) ⟨2303793044, by rfl⟩ : syracuseStep 3071724059 = 4607586089) B4607586089
theorem B122582267 : Blo 662308 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B948287 : Blo 662308 948287 := bstep (se 1 (by rfl) ⟨711215, by rfl⟩ : syracuseStep 948287 = 1422431) B1422431
theorem B559780145 : Blo 662308 559780145 := bstep (se 2 (by rfl) ⟨209917554, by rfl⟩ : syracuseStep 559780145 = 419835109) B419835109
theorem B2528765 : Blo 662308 2528765 := bstep (se 3 (by rfl) ⟨474143, by rfl⟩ : syracuseStep 2528765 = 948287) B948287
theorem B664047 : Blo 662308 664047 := bstep (se 1 (by rfl) ⟨498035, by rfl⟩ : syracuseStep 664047 = 996071) B996071
theorem B2047816039 : Blo 662308 2047816039 := bstep (se 1 (by rfl) ⟨1535862029, by rfl⟩ : syracuseStep 2047816039 = 3071724059) B3071724059
theorem B12803791 : Blo 662308 12803791 := bstep (se 1 (by rfl) ⟨9602843, by rfl⟩ : syracuseStep 12803791 = 19205687) B19205687
theorem B747679 : Blo 662308 747679 := bstep (se 1 (by rfl) ⟨560759, by rfl⟩ : syracuseStep 747679 = 1121519) B1121519
theorem B81721511 : Blo 662308 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B996905 : Blo 662308 996905 := bstep (se 2 (by rfl) ⟨373839, by rfl⟩ : syracuseStep 996905 = 747679) B747679
theorem B1685843 : Blo 662308 1685843 := bstep (se 1 (by rfl) ⟨1264382, by rfl⟩ : syracuseStep 1685843 = 2528765) B2528765
theorem B54481007 : Blo 662308 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B373186763 : Blo 662308 373186763 := bstep (se 1 (by rfl) ⟨279890072, by rfl⟩ : syracuseStep 373186763 = 559780145) B559780145
theorem B2730421385 : Blo 662308 2730421385 := bstep (se 2 (by rfl) ⟨1023908019, by rfl⟩ : syracuseStep 2730421385 = 2047816039) B2047816039
theorem B17071721 : Blo 662308 17071721 := bstep (se 2 (by rfl) ⟨6401895, by rfl⟩ : syracuseStep 17071721 = 12803791) B12803791
theorem B664603 : Blo 662308 664603 := bstep (se 1 (by rfl) ⟨498452, by rfl⟩ : syracuseStep 664603 = 996905) B996905
theorem B1123895 : Blo 662308 1123895 := bstep (se 1 (by rfl) ⟨842921, by rfl⟩ : syracuseStep 1123895 = 1685843) B1685843
theorem B11381147 : Blo 662308 11381147 := bstep (se 1 (by rfl) ⟨8535860, by rfl⟩ : syracuseStep 11381147 = 17071721) B17071721
theorem B36320671 : Blo 662308 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B248791175 : Blo 662308 248791175 := bstep (se 1 (by rfl) ⟨186593381, by rfl⟩ : syracuseStep 248791175 = 373186763) B373186763
theorem B1820280923 : Blo 662308 1820280923 := bstep (se 1 (by rfl) ⟨1365210692, by rfl⟩ : syracuseStep 1820280923 = 2730421385) B2730421385
theorem B7587431 : Blo 662308 7587431 := bstep (se 1 (by rfl) ⟨5690573, by rfl⟩ : syracuseStep 7587431 = 11381147) B11381147
theorem B165860783 : Blo 662308 165860783 := bstep (se 1 (by rfl) ⟨124395587, by rfl⟩ : syracuseStep 165860783 = 248791175) B248791175
theorem B1213520615 : Blo 662308 1213520615 := bstep (se 1 (by rfl) ⟨910140461, by rfl⟩ : syracuseStep 1213520615 = 1820280923) B1820280923
theorem B749263 : Blo 662308 749263 := bstep (se 1 (by rfl) ⟨561947, by rfl⟩ : syracuseStep 749263 = 1123895) B1123895
theorem B48427561 : Blo 662308 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B809013743 : Blo 662308 809013743 := bstep (se 1 (by rfl) ⟨606760307, by rfl⟩ : syracuseStep 809013743 = 1213520615) B1213520615
theorem B5058287 : Blo 662308 5058287 := bstep (se 1 (by rfl) ⟨3793715, by rfl⟩ : syracuseStep 5058287 = 7587431) B7587431
theorem B110573855 : Blo 662308 110573855 := bstep (se 1 (by rfl) ⟨82930391, by rfl⟩ : syracuseStep 110573855 = 165860783) B165860783
theorem B999017 : Blo 662308 999017 := bstep (se 2 (by rfl) ⟨374631, by rfl⟩ : syracuseStep 999017 = 749263) B749263
theorem B64570081 : Blo 662308 64570081 := bstep (se 2 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 64570081 = 48427561) B48427561
theorem B666011 : Blo 662308 666011 := bstep (se 1 (by rfl) ⟨499508, by rfl⟩ : syracuseStep 666011 = 999017) B999017
theorem B86093441 : Blo 662308 86093441 := bstep (se 2 (by rfl) ⟨32285040, by rfl⟩ : syracuseStep 86093441 = 64570081) B64570081
theorem B539342495 : Blo 662308 539342495 := bstep (se 1 (by rfl) ⟨404506871, by rfl⟩ : syracuseStep 539342495 = 809013743) B809013743
theorem B73715903 : Blo 662308 73715903 := bstep (se 1 (by rfl) ⟨55286927, by rfl⟩ : syracuseStep 73715903 = 110573855) B110573855
theorem B3372191 : Blo 662308 3372191 := bstep (se 1 (by rfl) ⟨2529143, by rfl⟩ : syracuseStep 3372191 = 5058287) B5058287
theorem B57395627 : Blo 662308 57395627 := bstep (se 1 (by rfl) ⟨43046720, by rfl⟩ : syracuseStep 57395627 = 86093441) B86093441
theorem B2248127 : Blo 662308 2248127 := bstep (se 1 (by rfl) ⟨1686095, by rfl⟩ : syracuseStep 2248127 = 3372191) B3372191
theorem B49143935 : Blo 662308 49143935 := bstep (se 1 (by rfl) ⟨36857951, by rfl⟩ : syracuseStep 49143935 = 73715903) B73715903
theorem B359561663 : Blo 662308 359561663 := bstep (se 1 (by rfl) ⟨269671247, by rfl⟩ : syracuseStep 359561663 = 539342495) B539342495
theorem B239707775 : Blo 662308 239707775 := bstep (se 1 (by rfl) ⟨179780831, by rfl⟩ : syracuseStep 239707775 = 359561663) B359561663
theorem B131050493 : Blo 662308 131050493 := bstep (se 3 (by rfl) ⟨24571967, by rfl⟩ : syracuseStep 131050493 = 49143935) B49143935
theorem B38263751 : Blo 662308 38263751 := bstep (se 1 (by rfl) ⟨28697813, by rfl⟩ : syracuseStep 38263751 = 57395627) B57395627
theorem B1498751 : Blo 662308 1498751 := bstep (se 1 (by rfl) ⟨1124063, by rfl⟩ : syracuseStep 1498751 = 2248127) B2248127
theorem B87366995 : Blo 662308 87366995 := bstep (se 1 (by rfl) ⟨65525246, by rfl⟩ : syracuseStep 87366995 = 131050493) B131050493
theorem B639220733 : Blo 662308 639220733 := bstep (se 3 (by rfl) ⟨119853887, by rfl⟩ : syracuseStep 639220733 = 239707775) B239707775
theorem B25509167 : Blo 662308 25509167 := bstep (se 1 (by rfl) ⟨19131875, by rfl⟩ : syracuseStep 25509167 = 38263751) B38263751
theorem B999167 : Blo 662308 999167 := bstep (se 1 (by rfl) ⟨749375, by rfl⟩ : syracuseStep 999167 = 1498751) B1498751
theorem B666111 : Blo 662308 666111 := bstep (se 1 (by rfl) ⟨499583, by rfl⟩ : syracuseStep 666111 = 999167) B999167
theorem B58244663 : Blo 662308 58244663 := bstep (se 1 (by rfl) ⟨43683497, by rfl⟩ : syracuseStep 58244663 = 87366995) B87366995
theorem B426147155 : Blo 662308 426147155 := bstep (se 1 (by rfl) ⟨319610366, by rfl⟩ : syracuseStep 426147155 = 639220733) B639220733
theorem B17006111 : Blo 662308 17006111 := bstep (se 1 (by rfl) ⟨12754583, by rfl⟩ : syracuseStep 17006111 = 25509167) B25509167
theorem B284098103 : Blo 662308 284098103 := bstep (se 1 (by rfl) ⟨213073577, by rfl⟩ : syracuseStep 284098103 = 426147155) B426147155
theorem B11337407 : Blo 662308 11337407 := bstep (se 1 (by rfl) ⟨8503055, by rfl⟩ : syracuseStep 11337407 = 17006111) B17006111
theorem B38829775 : Blo 662308 38829775 := bstep (se 1 (by rfl) ⟨29122331, by rfl⟩ : syracuseStep 38829775 = 58244663) B58244663
theorem B7558271 : Blo 662308 7558271 := bstep (se 1 (by rfl) ⟨5668703, by rfl⟩ : syracuseStep 7558271 = 11337407) B11337407
theorem B51773033 : Blo 662308 51773033 := bstep (se 2 (by rfl) ⟨19414887, by rfl⟩ : syracuseStep 51773033 = 38829775) B38829775
theorem B189398735 : Blo 662308 189398735 := bstep (se 1 (by rfl) ⟨142049051, by rfl⟩ : syracuseStep 189398735 = 284098103) B284098103
theorem B34515355 : Blo 662308 34515355 := bstep (se 1 (by rfl) ⟨25886516, by rfl⟩ : syracuseStep 34515355 = 51773033) B51773033
theorem B126265823 : Blo 662308 126265823 := bstep (se 1 (by rfl) ⟨94699367, by rfl⟩ : syracuseStep 126265823 = 189398735) B189398735
theorem B5038847 : Blo 662308 5038847 := bstep (se 1 (by rfl) ⟨3779135, by rfl⟩ : syracuseStep 5038847 = 7558271) B7558271
theorem B46020473 : Blo 662308 46020473 := bstep (se 2 (by rfl) ⟨17257677, by rfl⟩ : syracuseStep 46020473 = 34515355) B34515355
theorem B3359231 : Blo 662308 3359231 := bstep (se 1 (by rfl) ⟨2519423, by rfl⟩ : syracuseStep 3359231 = 5038847) B5038847
theorem B84177215 : Blo 662308 84177215 := bstep (se 1 (by rfl) ⟨63132911, by rfl⟩ : syracuseStep 84177215 = 126265823) B126265823
theorem B30680315 : Blo 662308 30680315 := bstep (se 1 (by rfl) ⟨23010236, by rfl⟩ : syracuseStep 30680315 = 46020473) B46020473
theorem B2239487 : Blo 662308 2239487 := bstep (se 1 (by rfl) ⟨1679615, by rfl⟩ : syracuseStep 2239487 = 3359231) B3359231
theorem B56118143 : Blo 662308 56118143 := bstep (se 1 (by rfl) ⟨42088607, by rfl⟩ : syracuseStep 56118143 = 84177215) B84177215
theorem B20453543 : Blo 662308 20453543 := bstep (se 1 (by rfl) ⟨15340157, by rfl⟩ : syracuseStep 20453543 = 30680315) B30680315
theorem B1492991 : Blo 662308 1492991 := bstep (se 1 (by rfl) ⟨1119743, by rfl⟩ : syracuseStep 1492991 = 2239487) B2239487
theorem B149648381 : Blo 662308 149648381 := bstep (se 3 (by rfl) ⟨28059071, by rfl⟩ : syracuseStep 149648381 = 56118143) B56118143
theorem B13635695 : Blo 662308 13635695 := bstep (se 1 (by rfl) ⟨10226771, by rfl⟩ : syracuseStep 13635695 = 20453543) B20453543
theorem B995327 : Blo 662308 995327 := bstep (se 1 (by rfl) ⟨746495, by rfl⟩ : syracuseStep 995327 = 1492991) B1492991
theorem B99765587 : Blo 662308 99765587 := bstep (se 1 (by rfl) ⟨74824190, by rfl⟩ : syracuseStep 99765587 = 149648381) B149648381
theorem B663551 : Blo 662308 663551 := bstep (se 1 (by rfl) ⟨497663, by rfl⟩ : syracuseStep 663551 = 995327) B995327
theorem B9090463 : Blo 662308 9090463 := bstep (se 1 (by rfl) ⟨6817847, by rfl⟩ : syracuseStep 9090463 = 13635695) B13635695
theorem B66510391 : Blo 662308 66510391 := bstep (se 1 (by rfl) ⟨49882793, by rfl⟩ : syracuseStep 66510391 = 99765587) B99765587
theorem B88680521 : Blo 662308 88680521 := bstep (se 2 (by rfl) ⟨33255195, by rfl⟩ : syracuseStep 88680521 = 66510391) B66510391
theorem B12120617 : Blo 662308 12120617 := bstep (se 2 (by rfl) ⟨4545231, by rfl⟩ : syracuseStep 12120617 = 9090463) B9090463
theorem B8080411 : Blo 662308 8080411 := bstep (se 1 (by rfl) ⟨6060308, by rfl⟩ : syracuseStep 8080411 = 12120617) B12120617
theorem B236481389 : Blo 662308 236481389 := bstep (se 3 (by rfl) ⟨44340260, by rfl⟩ : syracuseStep 236481389 = 88680521) B88680521
theorem B157654259 : Blo 662308 157654259 := bstep (se 1 (by rfl) ⟨118240694, by rfl⟩ : syracuseStep 157654259 = 236481389) B236481389
theorem B10773881 : Blo 662308 10773881 := bstep (se 2 (by rfl) ⟨4040205, by rfl⟩ : syracuseStep 10773881 = 8080411) B8080411
theorem B7182587 : Blo 662308 7182587 := bstep (se 1 (by rfl) ⟨5386940, by rfl⟩ : syracuseStep 7182587 = 10773881) B10773881
theorem B105102839 : Blo 662308 105102839 := bstep (se 1 (by rfl) ⟨78827129, by rfl⟩ : syracuseStep 105102839 = 157654259) B157654259
theorem B4788391 : Blo 662308 4788391 := bstep (se 1 (by rfl) ⟨3591293, by rfl⟩ : syracuseStep 4788391 = 7182587) B7182587
theorem B70068559 : Blo 662308 70068559 := bstep (se 1 (by rfl) ⟨52551419, by rfl⟩ : syracuseStep 70068559 = 105102839) B105102839
theorem B93424745 : Blo 662308 93424745 := bstep (se 2 (by rfl) ⟨35034279, by rfl⟩ : syracuseStep 93424745 = 70068559) B70068559
theorem B6384521 : Blo 662308 6384521 := bstep (se 2 (by rfl) ⟨2394195, by rfl⟩ : syracuseStep 6384521 = 4788391) B4788391
theorem B62283163 : Blo 662308 62283163 := bstep (se 1 (by rfl) ⟨46712372, by rfl⟩ : syracuseStep 62283163 = 93424745) B93424745
theorem B4256347 : Blo 662308 4256347 := bstep (se 1 (by rfl) ⟨3192260, by rfl⟩ : syracuseStep 4256347 = 6384521) B6384521
theorem B5675129 : Blo 662308 5675129 := bstep (se 2 (by rfl) ⟨2128173, by rfl⟩ : syracuseStep 5675129 = 4256347) B4256347
theorem B83044217 : Blo 662308 83044217 := bstep (se 2 (by rfl) ⟨31141581, by rfl⟩ : syracuseStep 83044217 = 62283163) B62283163
theorem B3783419 : Blo 662308 3783419 := bstep (se 1 (by rfl) ⟨2837564, by rfl⟩ : syracuseStep 3783419 = 5675129) B5675129
theorem B55362811 : Blo 662308 55362811 := bstep (se 1 (by rfl) ⟨41522108, by rfl⟩ : syracuseStep 55362811 = 83044217) B83044217
theorem B73817081 : Blo 662308 73817081 := bstep (se 2 (by rfl) ⟨27681405, by rfl⟩ : syracuseStep 73817081 = 55362811) B55362811
theorem B2522279 : Blo 662308 2522279 := bstep (se 1 (by rfl) ⟨1891709, by rfl⟩ : syracuseStep 2522279 = 3783419) B3783419
theorem B1681519 : Blo 662308 1681519 := bstep (se 1 (by rfl) ⟨1261139, by rfl⟩ : syracuseStep 1681519 = 2522279) B2522279
theorem B49211387 : Blo 662308 49211387 := bstep (se 1 (by rfl) ⟨36908540, by rfl⟩ : syracuseStep 49211387 = 73817081) B73817081
theorem B32807591 : Blo 662308 32807591 := bstep (se 1 (by rfl) ⟨24605693, by rfl⟩ : syracuseStep 32807591 = 49211387) B49211387
theorem B2242025 : Blo 662308 2242025 := bstep (se 2 (by rfl) ⟨840759, by rfl⟩ : syracuseStep 2242025 = 1681519) B1681519
theorem B21871727 : Blo 662308 21871727 := bstep (se 1 (by rfl) ⟨16403795, by rfl⟩ : syracuseStep 21871727 = 32807591) B32807591
theorem B1494683 : Blo 662308 1494683 := bstep (se 1 (by rfl) ⟨1121012, by rfl⟩ : syracuseStep 1494683 = 2242025) B2242025
theorem B996455 : Blo 662308 996455 := bstep (se 1 (by rfl) ⟨747341, by rfl⟩ : syracuseStep 996455 = 1494683) B1494683
theorem B14581151 : Blo 662308 14581151 := bstep (se 1 (by rfl) ⟨10935863, by rfl⟩ : syracuseStep 14581151 = 21871727) B21871727
theorem B664303 : Blo 662308 664303 := bstep (se 1 (by rfl) ⟨498227, by rfl⟩ : syracuseStep 664303 = 996455) B996455
theorem B9720767 : Blo 662308 9720767 := bstep (se 1 (by rfl) ⟨7290575, by rfl⟩ : syracuseStep 9720767 = 14581151) B14581151
theorem B25922045 : Blo 662308 25922045 := bstep (se 3 (by rfl) ⟨4860383, by rfl⟩ : syracuseStep 25922045 = 9720767) B9720767
theorem B17281363 : Blo 662308 17281363 := bstep (se 1 (by rfl) ⟨12961022, by rfl⟩ : syracuseStep 17281363 = 25922045) B25922045
theorem B23041817 : Blo 662308 23041817 := bstep (se 2 (by rfl) ⟨8640681, by rfl⟩ : syracuseStep 23041817 = 17281363) B17281363
theorem B15361211 : Blo 662308 15361211 := bstep (se 1 (by rfl) ⟨11520908, by rfl⟩ : syracuseStep 15361211 = 23041817) B23041817
theorem B40963229 : Blo 662308 40963229 := bstep (se 3 (by rfl) ⟨7680605, by rfl⟩ : syracuseStep 40963229 = 15361211) B15361211
theorem B27308819 : Blo 662308 27308819 := bstep (se 1 (by rfl) ⟨20481614, by rfl⟩ : syracuseStep 27308819 = 40963229) B40963229
theorem B18205879 : Blo 662308 18205879 := bstep (se 1 (by rfl) ⟨13654409, by rfl⟩ : syracuseStep 18205879 = 27308819) B27308819
theorem B24274505 : Blo 662308 24274505 := bstep (se 2 (by rfl) ⟨9102939, by rfl⟩ : syracuseStep 24274505 = 18205879) B18205879
theorem B16183003 : Blo 662308 16183003 := bstep (se 1 (by rfl) ⟨12137252, by rfl⟩ : syracuseStep 16183003 = 24274505) B24274505
theorem B21577337 : Blo 662308 21577337 := bstep (se 2 (by rfl) ⟨8091501, by rfl⟩ : syracuseStep 21577337 = 16183003) B16183003
theorem B14384891 : Blo 662308 14384891 := bstep (se 1 (by rfl) ⟨10788668, by rfl⟩ : syracuseStep 14384891 = 21577337) B21577337
theorem B9589927 : Blo 662308 9589927 := bstep (se 1 (by rfl) ⟨7192445, by rfl⟩ : syracuseStep 9589927 = 14384891) B14384891
theorem B12786569 : Blo 662308 12786569 := bstep (se 2 (by rfl) ⟨4794963, by rfl⟩ : syracuseStep 12786569 = 9589927) B9589927
theorem B8524379 : Blo 662308 8524379 := bstep (se 1 (by rfl) ⟨6393284, by rfl⟩ : syracuseStep 8524379 = 12786569) B12786569
theorem B5682919 : Blo 662308 5682919 := bstep (se 1 (by rfl) ⟨4262189, by rfl⟩ : syracuseStep 5682919 = 8524379) B8524379
theorem B7577225 : Blo 662308 7577225 := bstep (se 2 (by rfl) ⟨2841459, by rfl⟩ : syracuseStep 7577225 = 5682919) B5682919
theorem B5051483 : Blo 662308 5051483 := bstep (se 1 (by rfl) ⟨3788612, by rfl⟩ : syracuseStep 5051483 = 7577225) B7577225
theorem B3367655 : Blo 662308 3367655 := bstep (se 1 (by rfl) ⟨2525741, by rfl⟩ : syracuseStep 3367655 = 5051483) B5051483
theorem B2245103 : Blo 662308 2245103 := bstep (se 1 (by rfl) ⟨1683827, by rfl⟩ : syracuseStep 2245103 = 3367655) B3367655
theorem B1496735 : Blo 662308 1496735 := bstep (se 1 (by rfl) ⟨1122551, by rfl⟩ : syracuseStep 1496735 = 2245103) B2245103
theorem B997823 : Blo 662308 997823 := bstep (se 1 (by rfl) ⟨748367, by rfl⟩ : syracuseStep 997823 = 1496735) B1496735
theorem B665215 : Blo 662308 665215 := bstep (se 1 (by rfl) ⟨498911, by rfl⟩ : syracuseStep 665215 = 997823) B997823

theorem C0 (j : ℕ) (h1 : 165577 ≤ j) (h2 : j ≤ 166276) : Blo 662308 (4 * j + 3) := by
  interval_cases j
  · exact B662311
  · exact B662315
  · exact B662319
  · exact B662323
  · exact B662327
  · exact B662331
  · exact B662335
  · exact B662339
  · exact B662343
  · exact B662347
  · exact B662351
  · exact B662355
  · exact B662359
  · exact B662363
  · exact B662367
  · exact B662371
  · exact B662375
  · exact B662379
  · exact B662383
  · exact B662387
  · exact B662391
  · exact B662395
  · exact B662399
  · exact B662403
  · exact B662407
  · exact B662411
  · exact B662415
  · exact B662419
  · exact B662423
  · exact B662427
  · exact B662431
  · exact B662435
  · exact B662439
  · exact B662443
  · exact B662447
  · exact B662451
  · exact B662455
  · exact B662459
  · exact B662463
  · exact B662467
  · exact B662471
  · exact B662475
  · exact B662479
  · exact B662483
  · exact B662487
  · exact B662491
  · exact B662495
  · exact B662499
  · exact B662503
  · exact B662507
  · exact B662511
  · exact B662515
  · exact B662519
  · exact B662523
  · exact B662527
  · exact B662531
  · exact B662535
  · exact B662539
  · exact B662543
  · exact B662547
  · exact B662551
  · exact B662555
  · exact B662559
  · exact B662563
  · exact B662567
  · exact B662571
  · exact B662575
  · exact B662579
  · exact B662583
  · exact B662587
  · exact B662591
  · exact B662595
  · exact B662599
  · exact B662603
  · exact B662607
  · exact B662611
  · exact B662615
  · exact B662619
  · exact B662623
  · exact B662627
  · exact B662631
  · exact B662635
  · exact B662639
  · exact B662643
  · exact B662647
  · exact B662651
  · exact B662655
  · exact B662659
  · exact B662663
  · exact B662667
  · exact B662671
  · exact B662675
  · exact B662679
  · exact B662683
  · exact B662687
  · exact B662691
  · exact B662695
  · exact B662699
  · exact B662703
  · exact B662707
  · exact B662711
  · exact B662715
  · exact B662719
  · exact B662723
  · exact B662727
  · exact B662731
  · exact B662735
  · exact B662739
  · exact B662743
  · exact B662747
  · exact B662751
  · exact B662755
  · exact B662759
  · exact B662763
  · exact B662767
  · exact B662771
  · exact B662775
  · exact B662779
  · exact B662783
  · exact B662787
  · exact B662791
  · exact B662795
  · exact B662799
  · exact B662803
  · exact B662807
  · exact B662811
  · exact B662815
  · exact B662819
  · exact B662823
  · exact B662827
  · exact B662831
  · exact B662835
  · exact B662839
  · exact B662843
  · exact B662847
  · exact B662851
  · exact B662855
  · exact B662859
  · exact B662863
  · exact B662867
  · exact B662871
  · exact B662875
  · exact B662879
  · exact B662883
  · exact B662887
  · exact B662891
  · exact B662895
  · exact B662899
  · exact B662903
  · exact B662907
  · exact B662911
  · exact B662915
  · exact B662919
  · exact B662923
  · exact B662927
  · exact B662931
  · exact B662935
  · exact B662939
  · exact B662943
  · exact B662947
  · exact B662951
  · exact B662955
  · exact B662959
  · exact B662963
  · exact B662967
  · exact B662971
  · exact B662975
  · exact B662979
  · exact B662983
  · exact B662987
  · exact B662991
  · exact B662995
  · exact B662999
  · exact B663003
  · exact B663007
  · exact B663011
  · exact B663015
  · exact B663019
  · exact B663023
  · exact B663027
  · exact B663031
  · exact B663035
  · exact B663039
  · exact B663043
  · exact B663047
  · exact B663051
  · exact B663055
  · exact B663059
  · exact B663063
  · exact B663067
  · exact B663071
  · exact B663075
  · exact B663079
  · exact B663083
  · exact B663087
  · exact B663091
  · exact B663095
  · exact B663099
  · exact B663103
  · exact B663107
  · exact B663111
  · exact B663115
  · exact B663119
  · exact B663123
  · exact B663127
  · exact B663131
  · exact B663135
  · exact B663139
  · exact B663143
  · exact B663147
  · exact B663151
  · exact B663155
  · exact B663159
  · exact B663163
  · exact B663167
  · exact B663171
  · exact B663175
  · exact B663179
  · exact B663183
  · exact B663187
  · exact B663191
  · exact B663195
  · exact B663199
  · exact B663203
  · exact B663207
  · exact B663211
  · exact B663215
  · exact B663219
  · exact B663223
  · exact B663227
  · exact B663231
  · exact B663235
  · exact B663239
  · exact B663243
  · exact B663247
  · exact B663251
  · exact B663255
  · exact B663259
  · exact B663263
  · exact B663267
  · exact B663271
  · exact B663275
  · exact B663279
  · exact B663283
  · exact B663287
  · exact B663291
  · exact B663295
  · exact B663299
  · exact B663303
  · exact B663307
  · exact B663311
  · exact B663315
  · exact B663319
  · exact B663323
  · exact B663327
  · exact B663331
  · exact B663335
  · exact B663339
  · exact B663343
  · exact B663347
  · exact B663351
  · exact B663355
  · exact B663359
  · exact B663363
  · exact B663367
  · exact B663371
  · exact B663375
  · exact B663379
  · exact B663383
  · exact B663387
  · exact B663391
  · exact B663395
  · exact B663399
  · exact B663403
  · exact B663407
  · exact B663411
  · exact B663415
  · exact B663419
  · exact B663423
  · exact B663427
  · exact B663431
  · exact B663435
  · exact B663439
  · exact B663443
  · exact B663447
  · exact B663451
  · exact B663455
  · exact B663459
  · exact B663463
  · exact B663467
  · exact B663471
  · exact B663475
  · exact B663479
  · exact B663483
  · exact B663487
  · exact B663491
  · exact B663495
  · exact B663499
  · exact B663503
  · exact B663507
  · exact B663511
  · exact B663515
  · exact B663519
  · exact B663523
  · exact B663527
  · exact B663531
  · exact B663535
  · exact B663539
  · exact B663543
  · exact B663547
  · exact B663551
  · exact B663555
  · exact B663559
  · exact B663563
  · exact B663567
  · exact B663571
  · exact B663575
  · exact B663579
  · exact B663583
  · exact B663587
  · exact B663591
  · exact B663595
  · exact B663599
  · exact B663603
  · exact B663607
  · exact B663611
  · exact B663615
  · exact B663619
  · exact B663623
  · exact B663627
  · exact B663631
  · exact B663635
  · exact B663639
  · exact B663643
  · exact B663647
  · exact B663651
  · exact B663655
  · exact B663659
  · exact B663663
  · exact B663667
  · exact B663671
  · exact B663675
  · exact B663679
  · exact B663683
  · exact B663687
  · exact B663691
  · exact B663695
  · exact B663699
  · exact B663703
  · exact B663707
  · exact B663711
  · exact B663715
  · exact B663719
  · exact B663723
  · exact B663727
  · exact B663731
  · exact B663735
  · exact B663739
  · exact B663743
  · exact B663747
  · exact B663751
  · exact B663755
  · exact B663759
  · exact B663763
  · exact B663767
  · exact B663771
  · exact B663775
  · exact B663779
  · exact B663783
  · exact B663787
  · exact B663791
  · exact B663795
  · exact B663799
  · exact B663803
  · exact B663807
  · exact B663811
  · exact B663815
  · exact B663819
  · exact B663823
  · exact B663827
  · exact B663831
  · exact B663835
  · exact B663839
  · exact B663843
  · exact B663847
  · exact B663851
  · exact B663855
  · exact B663859
  · exact B663863
  · exact B663867
  · exact B663871
  · exact B663875
  · exact B663879
  · exact B663883
  · exact B663887
  · exact B663891
  · exact B663895
  · exact B663899
  · exact B663903
  · exact B663907
  · exact B663911
  · exact B663915
  · exact B663919
  · exact B663923
  · exact B663927
  · exact B663931
  · exact B663935
  · exact B663939
  · exact B663943
  · exact B663947
  · exact B663951
  · exact B663955
  · exact B663959
  · exact B663963
  · exact B663967
  · exact B663971
  · exact B663975
  · exact B663979
  · exact B663983
  · exact B663987
  · exact B663991
  · exact B663995
  · exact B663999
  · exact B664003
  · exact B664007
  · exact B664011
  · exact B664015
  · exact B664019
  · exact B664023
  · exact B664027
  · exact B664031
  · exact B664035
  · exact B664039
  · exact B664043
  · exact B664047
  · exact B664051
  · exact B664055
  · exact B664059
  · exact B664063
  · exact B664067
  · exact B664071
  · exact B664075
  · exact B664079
  · exact B664083
  · exact B664087
  · exact B664091
  · exact B664095
  · exact B664099
  · exact B664103
  · exact B664107
  · exact B664111
  · exact B664115
  · exact B664119
  · exact B664123
  · exact B664127
  · exact B664131
  · exact B664135
  · exact B664139
  · exact B664143
  · exact B664147
  · exact B664151
  · exact B664155
  · exact B664159
  · exact B664163
  · exact B664167
  · exact B664171
  · exact B664175
  · exact B664179
  · exact B664183
  · exact B664187
  · exact B664191
  · exact B664195
  · exact B664199
  · exact B664203
  · exact B664207
  · exact B664211
  · exact B664215
  · exact B664219
  · exact B664223
  · exact B664227
  · exact B664231
  · exact B664235
  · exact B664239
  · exact B664243
  · exact B664247
  · exact B664251
  · exact B664255
  · exact B664259
  · exact B664263
  · exact B664267
  · exact B664271
  · exact B664275
  · exact B664279
  · exact B664283
  · exact B664287
  · exact B664291
  · exact B664295
  · exact B664299
  · exact B664303
  · exact B664307
  · exact B664311
  · exact B664315
  · exact B664319
  · exact B664323
  · exact B664327
  · exact B664331
  · exact B664335
  · exact B664339
  · exact B664343
  · exact B664347
  · exact B664351
  · exact B664355
  · exact B664359
  · exact B664363
  · exact B664367
  · exact B664371
  · exact B664375
  · exact B664379
  · exact B664383
  · exact B664387
  · exact B664391
  · exact B664395
  · exact B664399
  · exact B664403
  · exact B664407
  · exact B664411
  · exact B664415
  · exact B664419
  · exact B664423
  · exact B664427
  · exact B664431
  · exact B664435
  · exact B664439
  · exact B664443
  · exact B664447
  · exact B664451
  · exact B664455
  · exact B664459
  · exact B664463
  · exact B664467
  · exact B664471
  · exact B664475
  · exact B664479
  · exact B664483
  · exact B664487
  · exact B664491
  · exact B664495
  · exact B664499
  · exact B664503
  · exact B664507
  · exact B664511
  · exact B664515
  · exact B664519
  · exact B664523
  · exact B664527
  · exact B664531
  · exact B664535
  · exact B664539
  · exact B664543
  · exact B664547
  · exact B664551
  · exact B664555
  · exact B664559
  · exact B664563
  · exact B664567
  · exact B664571
  · exact B664575
  · exact B664579
  · exact B664583
  · exact B664587
  · exact B664591
  · exact B664595
  · exact B664599
  · exact B664603
  · exact B664607
  · exact B664611
  · exact B664615
  · exact B664619
  · exact B664623
  · exact B664627
  · exact B664631
  · exact B664635
  · exact B664639
  · exact B664643
  · exact B664647
  · exact B664651
  · exact B664655
  · exact B664659
  · exact B664663
  · exact B664667
  · exact B664671
  · exact B664675
  · exact B664679
  · exact B664683
  · exact B664687
  · exact B664691
  · exact B664695
  · exact B664699
  · exact B664703
  · exact B664707
  · exact B664711
  · exact B664715
  · exact B664719
  · exact B664723
  · exact B664727
  · exact B664731
  · exact B664735
  · exact B664739
  · exact B664743
  · exact B664747
  · exact B664751
  · exact B664755
  · exact B664759
  · exact B664763
  · exact B664767
  · exact B664771
  · exact B664775
  · exact B664779
  · exact B664783
  · exact B664787
  · exact B664791
  · exact B664795
  · exact B664799
  · exact B664803
  · exact B664807
  · exact B664811
  · exact B664815
  · exact B664819
  · exact B664823
  · exact B664827
  · exact B664831
  · exact B664835
  · exact B664839
  · exact B664843
  · exact B664847
  · exact B664851
  · exact B664855
  · exact B664859
  · exact B664863
  · exact B664867
  · exact B664871
  · exact B664875
  · exact B664879
  · exact B664883
  · exact B664887
  · exact B664891
  · exact B664895
  · exact B664899
  · exact B664903
  · exact B664907
  · exact B664911
  · exact B664915
  · exact B664919
  · exact B664923
  · exact B664927
  · exact B664931
  · exact B664935
  · exact B664939
  · exact B664943
  · exact B664947
  · exact B664951
  · exact B664955
  · exact B664959
  · exact B664963
  · exact B664967
  · exact B664971
  · exact B664975
  · exact B664979
  · exact B664983
  · exact B664987
  · exact B664991
  · exact B664995
  · exact B664999
  · exact B665003
  · exact B665007
  · exact B665011
  · exact B665015
  · exact B665019
  · exact B665023
  · exact B665027
  · exact B665031
  · exact B665035
  · exact B665039
  · exact B665043
  · exact B665047
  · exact B665051
  · exact B665055
  · exact B665059
  · exact B665063
  · exact B665067
  · exact B665071
  · exact B665075
  · exact B665079
  · exact B665083
  · exact B665087
  · exact B665091
  · exact B665095
  · exact B665099
  · exact B665103
  · exact B665107

theorem C1 (j : ℕ) (h1 : 166277 ≤ j) (h2 : j ≤ 166576) : Blo 662308 (4 * j + 3) := by
  interval_cases j
  · exact B665111
  · exact B665115
  · exact B665119
  · exact B665123
  · exact B665127
  · exact B665131
  · exact B665135
  · exact B665139
  · exact B665143
  · exact B665147
  · exact B665151
  · exact B665155
  · exact B665159
  · exact B665163
  · exact B665167
  · exact B665171
  · exact B665175
  · exact B665179
  · exact B665183
  · exact B665187
  · exact B665191
  · exact B665195
  · exact B665199
  · exact B665203
  · exact B665207
  · exact B665211
  · exact B665215
  · exact B665219
  · exact B665223
  · exact B665227
  · exact B665231
  · exact B665235
  · exact B665239
  · exact B665243
  · exact B665247
  · exact B665251
  · exact B665255
  · exact B665259
  · exact B665263
  · exact B665267
  · exact B665271
  · exact B665275
  · exact B665279
  · exact B665283
  · exact B665287
  · exact B665291
  · exact B665295
  · exact B665299
  · exact B665303
  · exact B665307
  · exact B665311
  · exact B665315
  · exact B665319
  · exact B665323
  · exact B665327
  · exact B665331
  · exact B665335
  · exact B665339
  · exact B665343
  · exact B665347
  · exact B665351
  · exact B665355
  · exact B665359
  · exact B665363
  · exact B665367
  · exact B665371
  · exact B665375
  · exact B665379
  · exact B665383
  · exact B665387
  · exact B665391
  · exact B665395
  · exact B665399
  · exact B665403
  · exact B665407
  · exact B665411
  · exact B665415
  · exact B665419
  · exact B665423
  · exact B665427
  · exact B665431
  · exact B665435
  · exact B665439
  · exact B665443
  · exact B665447
  · exact B665451
  · exact B665455
  · exact B665459
  · exact B665463
  · exact B665467
  · exact B665471
  · exact B665475
  · exact B665479
  · exact B665483
  · exact B665487
  · exact B665491
  · exact B665495
  · exact B665499
  · exact B665503
  · exact B665507
  · exact B665511
  · exact B665515
  · exact B665519
  · exact B665523
  · exact B665527
  · exact B665531
  · exact B665535
  · exact B665539
  · exact B665543
  · exact B665547
  · exact B665551
  · exact B665555
  · exact B665559
  · exact B665563
  · exact B665567
  · exact B665571
  · exact B665575
  · exact B665579
  · exact B665583
  · exact B665587
  · exact B665591
  · exact B665595
  · exact B665599
  · exact B665603
  · exact B665607
  · exact B665611
  · exact B665615
  · exact B665619
  · exact B665623
  · exact B665627
  · exact B665631
  · exact B665635
  · exact B665639
  · exact B665643
  · exact B665647
  · exact B665651
  · exact B665655
  · exact B665659
  · exact B665663
  · exact B665667
  · exact B665671
  · exact B665675
  · exact B665679
  · exact B665683
  · exact B665687
  · exact B665691
  · exact B665695
  · exact B665699
  · exact B665703
  · exact B665707
  · exact B665711
  · exact B665715
  · exact B665719
  · exact B665723
  · exact B665727
  · exact B665731
  · exact B665735
  · exact B665739
  · exact B665743
  · exact B665747
  · exact B665751
  · exact B665755
  · exact B665759
  · exact B665763
  · exact B665767
  · exact B665771
  · exact B665775
  · exact B665779
  · exact B665783
  · exact B665787
  · exact B665791
  · exact B665795
  · exact B665799
  · exact B665803
  · exact B665807
  · exact B665811
  · exact B665815
  · exact B665819
  · exact B665823
  · exact B665827
  · exact B665831
  · exact B665835
  · exact B665839
  · exact B665843
  · exact B665847
  · exact B665851
  · exact B665855
  · exact B665859
  · exact B665863
  · exact B665867
  · exact B665871
  · exact B665875
  · exact B665879
  · exact B665883
  · exact B665887
  · exact B665891
  · exact B665895
  · exact B665899
  · exact B665903
  · exact B665907
  · exact B665911
  · exact B665915
  · exact B665919
  · exact B665923
  · exact B665927
  · exact B665931
  · exact B665935
  · exact B665939
  · exact B665943
  · exact B665947
  · exact B665951
  · exact B665955
  · exact B665959
  · exact B665963
  · exact B665967
  · exact B665971
  · exact B665975
  · exact B665979
  · exact B665983
  · exact B665987
  · exact B665991
  · exact B665995
  · exact B665999
  · exact B666003
  · exact B666007
  · exact B666011
  · exact B666015
  · exact B666019
  · exact B666023
  · exact B666027
  · exact B666031
  · exact B666035
  · exact B666039
  · exact B666043
  · exact B666047
  · exact B666051
  · exact B666055
  · exact B666059
  · exact B666063
  · exact B666067
  · exact B666071
  · exact B666075
  · exact B666079
  · exact B666083
  · exact B666087
  · exact B666091
  · exact B666095
  · exact B666099
  · exact B666103
  · exact B666107
  · exact B666111
  · exact B666115
  · exact B666119
  · exact B666123
  · exact B666127
  · exact B666131
  · exact B666135
  · exact B666139
  · exact B666143
  · exact B666147
  · exact B666151
  · exact B666155
  · exact B666159
  · exact B666163
  · exact B666167
  · exact B666171
  · exact B666175
  · exact B666179
  · exact B666183
  · exact B666187
  · exact B666191
  · exact B666195
  · exact B666199
  · exact B666203
  · exact B666207
  · exact B666211
  · exact B666215
  · exact B666219
  · exact B666223
  · exact B666227
  · exact B666231
  · exact B666235
  · exact B666239
  · exact B666243
  · exact B666247
  · exact B666251
  · exact B666255
  · exact B666259
  · exact B666263
  · exact B666267
  · exact B666271
  · exact B666275
  · exact B666279
  · exact B666283
  · exact B666287
  · exact B666291
  · exact B666295
  · exact B666299
  · exact B666303
  · exact B666307

theorem solution (m : ℕ) (hlo : 662308 ≤ m) (hhi : m ≤ 666308) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 165577 ≤ j := by omega
    have hj2 : j ≤ 166576 := by omega
    have hb : Blo 662308 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 166277 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
