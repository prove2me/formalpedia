-- Prove2me | solution 1 for syracuse_descends_range_972592_976592
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:05.420986+00:00
-- url     : https://prove2.me/submissions/530a5d23-3bae-4c7e-b96f-d30e23db1115

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


theorem B2195477 : Blo 972592 2195477 := bbase (se 6 (by rfl) ⟨51456, by rfl⟩ : syracuseStep 2195477 = 102913) (by norm_num)
theorem B2195549 : Blo 972592 2195549 := bbase (se 3 (by rfl) ⟨411665, by rfl⟩ : syracuseStep 2195549 = 823331) (by norm_num)
theorem B1409125 : Blo 972592 1409125 := bbase (se 4 (by rfl) ⟨132105, by rfl⟩ : syracuseStep 1409125 = 264211) (by norm_num)
theorem B11108501 : Blo 972592 11108501 := bbase (se 6 (by rfl) ⟨260355, by rfl⟩ : syracuseStep 11108501 = 520711) (by norm_num)
theorem B2195621 : Blo 972592 2195621 := bbase (se 4 (by rfl) ⟨205839, by rfl⟩ : syracuseStep 2195621 = 411679) (by norm_num)
theorem B2195693 : Blo 972592 2195693 := bbase (se 3 (by rfl) ⟨411692, by rfl⟩ : syracuseStep 2195693 = 823385) (by norm_num)
theorem B4686133 : Blo 972592 4686133 := bbase (se 5 (by rfl) ⟨219662, by rfl⟩ : syracuseStep 4686133 = 439325) (by norm_num)
theorem B2195765 : Blo 972592 2195765 := bbase (se 5 (by rfl) ⟨102926, by rfl⟩ : syracuseStep 2195765 = 205853) (by norm_num)
theorem B2195837 : Blo 972592 2195837 := bbase (se 3 (by rfl) ⟨411719, by rfl⟩ : syracuseStep 2195837 = 823439) (by norm_num)
theorem B2195909 : Blo 972592 2195909 := bbase (se 4 (by rfl) ⟨205866, by rfl⟩ : syracuseStep 2195909 = 411733) (by norm_num)
theorem B2195981 : Blo 972592 2195981 := bbase (se 3 (by rfl) ⟨411746, by rfl⟩ : syracuseStep 2195981 = 823493) (by norm_num)
theorem B2196053 : Blo 972592 2196053 := bbase (se 8 (by rfl) ⟨12867, by rfl⟩ : syracuseStep 2196053 = 25735) (by norm_num)
theorem B2196125 : Blo 972592 2196125 := bbase (se 3 (by rfl) ⟨411773, by rfl⟩ : syracuseStep 2196125 = 823547) (by norm_num)
theorem B4752101 : Blo 972592 4752101 := bbase (se 4 (by rfl) ⟨445509, by rfl⟩ : syracuseStep 4752101 = 891019) (by norm_num)
theorem B2196197 : Blo 972592 2196197 := bbase (se 4 (by rfl) ⟨205893, by rfl⟩ : syracuseStep 2196197 = 411787) (by norm_num)
theorem B2196269 : Blo 972592 2196269 := bbase (se 3 (by rfl) ⟨411800, by rfl⟩ : syracuseStep 2196269 = 823601) (by norm_num)
theorem B2196341 : Blo 972592 2196341 := bbase (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) (by norm_num)
theorem B2196413 : Blo 972592 2196413 := bbase (se 3 (by rfl) ⟨411827, by rfl⟩ : syracuseStep 2196413 = 823655) (by norm_num)
theorem B2196485 : Blo 972592 2196485 := bbase (se 4 (by rfl) ⟨205920, by rfl⟩ : syracuseStep 2196485 = 411841) (by norm_num)
theorem B2196557 : Blo 972592 2196557 := bbase (se 3 (by rfl) ⟨411854, by rfl⟩ : syracuseStep 2196557 = 823709) (by norm_num)
theorem B2196629 : Blo 972592 2196629 := bbase (se 6 (by rfl) ⟨51483, by rfl⟩ : syracuseStep 2196629 = 102967) (by norm_num)
theorem B2196701 : Blo 972592 2196701 := bbase (se 3 (by rfl) ⟨411881, by rfl⟩ : syracuseStep 2196701 = 823763) (by norm_num)
theorem B4162853 : Blo 972592 4162853 := bbase (se 4 (by rfl) ⟨390267, by rfl⟩ : syracuseStep 4162853 = 780535) (by norm_num)
theorem B2196773 : Blo 972592 2196773 := bbase (se 4 (by rfl) ⟨205947, by rfl⟩ : syracuseStep 2196773 = 411895) (by norm_num)
theorem B2196845 : Blo 972592 2196845 := bbase (se 3 (by rfl) ⟨411908, by rfl⟩ : syracuseStep 2196845 = 823817) (by norm_num)
theorem B2196917 : Blo 972592 2196917 := bbase (se 5 (by rfl) ⟨102980, by rfl⟩ : syracuseStep 2196917 = 205961) (by norm_num)
theorem B2196989 : Blo 972592 2196989 := bbase (se 3 (by rfl) ⟨411935, by rfl⟩ : syracuseStep 2196989 = 823871) (by norm_num)
theorem B7407125 : Blo 972592 7407125 := bbase (se 6 (by rfl) ⟨173604, by rfl⟩ : syracuseStep 7407125 = 347209) (by norm_num)
theorem B2197061 : Blo 972592 2197061 := bbase (se 4 (by rfl) ⟨205974, by rfl⟩ : syracuseStep 2197061 = 411949) (by norm_num)
theorem B2197133 : Blo 972592 2197133 := bbase (se 3 (by rfl) ⟨411962, by rfl⟩ : syracuseStep 2197133 = 823925) (by norm_num)
theorem B2000533 : Blo 972592 2000533 := bbase (se 6 (by rfl) ⟨46887, by rfl⟩ : syracuseStep 2000533 = 93775) (by norm_num)
theorem B2164429 : Blo 972592 2164429 := bbase (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) (by norm_num)
theorem B2197205 : Blo 972592 2197205 := bbase (se 7 (by rfl) ⟨25748, by rfl⟩ : syracuseStep 2197205 = 51497) (by norm_num)
theorem B2197277 : Blo 972592 2197277 := bbase (se 3 (by rfl) ⟨411989, by rfl⟩ : syracuseStep 2197277 = 823979) (by norm_num)
theorem B3704885 : Blo 972592 3704885 := bbase (se 5 (by rfl) ⟨173666, by rfl⟩ : syracuseStep 3704885 = 347333) (by norm_num)
theorem B9373877 : Blo 972592 9373877 := bbase (se 5 (by rfl) ⟨439400, by rfl⟩ : syracuseStep 9373877 = 878801) (by norm_num)
theorem B3705173 : Blo 972592 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B5540309 : Blo 972592 5540309 := bbase (se 7 (by rfl) ⟨64925, by rfl⟩ : syracuseStep 5540309 = 129851) (by norm_num)
theorem B1804853 : Blo 972592 1804853 := bbase (se 5 (by rfl) ⟨84602, by rfl⟩ : syracuseStep 1804853 = 169205) (by norm_num)
theorem B1641269 : Blo 972592 1641269 := bbase (se 5 (by rfl) ⟨76934, by rfl⟩ : syracuseStep 1641269 = 153869) (by norm_num)
theorem B1641397 : Blo 972592 1641397 := bbase (se 5 (by rfl) ⟨76940, by rfl⟩ : syracuseStep 1641397 = 153881) (by norm_num)
theorem B5934005 : Blo 972592 5934005 := bbase (se 5 (by rfl) ⟨278156, by rfl⟩ : syracuseStep 5934005 = 556313) (by norm_num)
theorem B986041 : Blo 972592 986041 := bbase (se 2 (by rfl) ⟨369765, by rfl⟩ : syracuseStep 986041 = 739531) (by norm_num)
theorem B1641485 : Blo 972592 1641485 := bbase (se 3 (by rfl) ⟨307778, by rfl⟩ : syracuseStep 1641485 = 615557) (by norm_num)
theorem B1641613 : Blo 972592 1641613 := bbase (se 3 (by rfl) ⟨307802, by rfl⟩ : syracuseStep 1641613 = 615605) (by norm_num)
theorem B1641701 : Blo 972592 1641701 := bbase (se 4 (by rfl) ⟨153909, by rfl⟩ : syracuseStep 1641701 = 307819) (by norm_num)
theorem B1641829 : Blo 972592 1641829 := bbase (se 4 (by rfl) ⟨153921, by rfl⟩ : syracuseStep 1641829 = 307843) (by norm_num)
theorem B3509669 : Blo 972592 3509669 := bbase (se 4 (by rfl) ⟨329031, by rfl⟩ : syracuseStep 3509669 = 658063) (by norm_num)
theorem B1641917 : Blo 972592 1641917 := bbase (se 3 (by rfl) ⟨307859, by rfl⟩ : syracuseStep 1641917 = 615719) (by norm_num)
theorem B3706357 : Blo 972592 3706357 := bbase (se 5 (by rfl) ⟨173735, by rfl⟩ : syracuseStep 3706357 = 347471) (by norm_num)
theorem B1642045 : Blo 972592 1642045 := bbase (se 3 (by rfl) ⟨307883, by rfl⟩ : syracuseStep 1642045 = 615767) (by norm_num)
theorem B5541493 : Blo 972592 5541493 := bbase (se 5 (by rfl) ⟨259757, by rfl⟩ : syracuseStep 5541493 = 519515) (by norm_num)
theorem B1642133 : Blo 972592 1642133 := bbase (se 6 (by rfl) ⟨38487, by rfl⟩ : syracuseStep 1642133 = 76975) (by norm_num)
theorem B1642261 : Blo 972592 1642261 := bbase (se 6 (by rfl) ⟨38490, by rfl⟩ : syracuseStep 1642261 = 76981) (by norm_num)
theorem B3706661 : Blo 972592 3706661 := bbase (se 4 (by rfl) ⟨347499, by rfl⟩ : syracuseStep 3706661 = 694999) (by norm_num)
theorem B3116885 : Blo 972592 3116885 := bbase (se 9 (by rfl) ⟨9131, by rfl⟩ : syracuseStep 3116885 = 18263) (by norm_num)
theorem B3510101 : Blo 972592 3510101 := bbase (se 9 (by rfl) ⟨10283, by rfl⟩ : syracuseStep 3510101 = 20567) (by norm_num)
theorem B1642349 : Blo 972592 1642349 := bbase (se 3 (by rfl) ⟨307940, by rfl⟩ : syracuseStep 1642349 = 615881) (by norm_num)
theorem B1314677 : Blo 972592 1314677 := bbase (se 5 (by rfl) ⟨61625, by rfl⟩ : syracuseStep 1314677 = 123251) (by norm_num)
theorem B1642477 : Blo 972592 1642477 := bbase (se 3 (by rfl) ⟨307964, by rfl⟩ : syracuseStep 1642477 = 615929) (by norm_num)
theorem B1314829 : Blo 972592 1314829 := bbase (se 3 (by rfl) ⟨246530, by rfl⟩ : syracuseStep 1314829 = 493061) (by norm_num)
theorem B1642565 : Blo 972592 1642565 := bbase (se 4 (by rfl) ⟨153990, by rfl⟩ : syracuseStep 1642565 = 307981) (by norm_num)
theorem B1642693 : Blo 972592 1642693 := bbase (se 4 (by rfl) ⟨154002, by rfl⟩ : syracuseStep 1642693 = 308005) (by norm_num)
theorem B1315045 : Blo 972592 1315045 := bbase (se 4 (by rfl) ⟨123285, by rfl⟩ : syracuseStep 1315045 = 246571) (by norm_num)
theorem B1642781 : Blo 972592 1642781 := bbase (se 3 (by rfl) ⟨308021, by rfl⟩ : syracuseStep 1642781 = 616043) (by norm_num)
theorem B1642909 : Blo 972592 1642909 := bbase (se 3 (by rfl) ⟨308045, by rfl⟩ : syracuseStep 1642909 = 616091) (by norm_num)
theorem B2462197 : Blo 972592 2462197 := bbase (se 5 (by rfl) ⟨115415, by rfl⟩ : syracuseStep 2462197 = 230831) (by norm_num)
theorem B1642997 : Blo 972592 1642997 := bbase (se 5 (by rfl) ⟨77015, by rfl⟩ : syracuseStep 1642997 = 154031) (by norm_num)
theorem B2462309 : Blo 972592 2462309 := bbase (se 4 (by rfl) ⟨230841, by rfl⟩ : syracuseStep 2462309 = 461683) (by norm_num)
theorem B1643125 : Blo 972592 1643125 := bbase (se 5 (by rfl) ⟨77021, by rfl⟩ : syracuseStep 1643125 = 154043) (by norm_num)
theorem B1643213 : Blo 972592 1643213 := bbase (se 3 (by rfl) ⟨308102, by rfl⟩ : syracuseStep 1643213 = 616205) (by norm_num)
theorem B3117797 : Blo 972592 3117797 := bbase (se 4 (by rfl) ⟨292293, by rfl⟩ : syracuseStep 3117797 = 584587) (by norm_num)
theorem B1315597 : Blo 972592 1315597 := bbase (se 3 (by rfl) ⟨246674, by rfl⟩ : syracuseStep 1315597 = 493349) (by norm_num)
theorem B2462501 : Blo 972592 2462501 := bbase (se 4 (by rfl) ⟨230859, by rfl⟩ : syracuseStep 2462501 = 461719) (by norm_num)
theorem B1479493 : Blo 972592 1479493 := bbase (se 4 (by rfl) ⟨138702, by rfl⟩ : syracuseStep 1479493 = 277405) (by norm_num)
theorem B1643341 : Blo 972592 1643341 := bbase (se 3 (by rfl) ⟨308126, by rfl⟩ : syracuseStep 1643341 = 616253) (by norm_num)
theorem B1643429 : Blo 972592 1643429 := bbase (se 4 (by rfl) ⟨154071, by rfl⟩ : syracuseStep 1643429 = 308143) (by norm_num)
theorem B2888677 : Blo 972592 2888677 := bbase (se 4 (by rfl) ⟨270813, by rfl⟩ : syracuseStep 2888677 = 541627) (by norm_num)
theorem B1643557 : Blo 972592 1643557 := bbase (se 4 (by rfl) ⟨154083, by rfl⟩ : syracuseStep 1643557 = 308167) (by norm_num)
theorem B2462845 : Blo 972592 2462845 := bbase (se 3 (by rfl) ⟨461783, by rfl⟩ : syracuseStep 2462845 = 923567) (by norm_num)
theorem B1643645 : Blo 972592 1643645 := bbase (se 3 (by rfl) ⟨308183, by rfl⟩ : syracuseStep 1643645 = 616367) (by norm_num)
theorem B1053865 : Blo 972592 1053865 := bbase (se 2 (by rfl) ⟨395199, by rfl⟩ : syracuseStep 1053865 = 790399) (by norm_num)
theorem B2462957 : Blo 972592 2462957 := bbase (se 3 (by rfl) ⟨461804, by rfl⟩ : syracuseStep 2462957 = 923609) (by norm_num)
theorem B1643773 : Blo 972592 1643773 := bbase (se 3 (by rfl) ⟨308207, by rfl⟩ : syracuseStep 1643773 = 616415) (by norm_num)
theorem B1643861 : Blo 972592 1643861 := bbase (se 14 (by rfl) ⟨150, by rfl⟩ : syracuseStep 1643861 = 301) (by norm_num)
theorem B2463149 : Blo 972592 2463149 := bbase (se 3 (by rfl) ⟨461840, by rfl⟩ : syracuseStep 2463149 = 923681) (by norm_num)
theorem B1643989 : Blo 972592 1643989 := bbase (se 7 (by rfl) ⟨19265, by rfl⟩ : syracuseStep 1643989 = 38531) (by norm_num)
theorem B4167125 : Blo 972592 4167125 := bbase (se 7 (by rfl) ⟨48833, by rfl⟩ : syracuseStep 4167125 = 97667) (by norm_num)
theorem B1644077 : Blo 972592 1644077 := bbase (se 3 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 1644077 = 616529) (by norm_num)
theorem B5543477 : Blo 972592 5543477 := bbase (se 5 (by rfl) ⟨259850, by rfl⟩ : syracuseStep 5543477 = 519701) (by norm_num)
theorem B1480277 : Blo 972592 1480277 := bbase (se 8 (by rfl) ⟨8673, by rfl⟩ : syracuseStep 1480277 = 17347) (by norm_num)
theorem B1644205 : Blo 972592 1644205 := bbase (se 3 (by rfl) ⟨308288, by rfl⟩ : syracuseStep 1644205 = 616577) (by norm_num)
theorem B2463493 : Blo 972592 2463493 := bbase (se 4 (by rfl) ⟨230952, by rfl⟩ : syracuseStep 2463493 = 461905) (by norm_num)
theorem B1644293 : Blo 972592 1644293 := bbase (se 4 (by rfl) ⟨154152, by rfl⟩ : syracuseStep 1644293 = 308305) (by norm_num)
theorem B2463605 : Blo 972592 2463605 := bbase (se 5 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 2463605 = 230963) (by norm_num)
theorem B989057 : Blo 972592 989057 := bbase (se 2 (by rfl) ⟨370896, by rfl⟩ : syracuseStep 989057 = 741793) (by norm_num)
theorem B3282821 : Blo 972592 3282821 := bbase (se 4 (by rfl) ⟨307764, by rfl⟩ : syracuseStep 3282821 = 615529) (by norm_num)
theorem B1644421 : Blo 972592 1644421 := bbase (se 4 (by rfl) ⟨154164, by rfl⟩ : syracuseStep 1644421 = 308329) (by norm_num)
theorem B1054661 : Blo 972592 1054661 := bbase (se 4 (by rfl) ⟨98874, by rfl⟩ : syracuseStep 1054661 = 197749) (by norm_num)
theorem B1644509 : Blo 972592 1644509 := bbase (se 3 (by rfl) ⟨308345, by rfl⟩ : syracuseStep 1644509 = 616691) (by norm_num)
theorem B3119141 : Blo 972592 3119141 := bbase (se 4 (by rfl) ⟨292419, by rfl⟩ : syracuseStep 3119141 = 584839) (by norm_num)
theorem B2463797 : Blo 972592 2463797 := bbase (se 5 (by rfl) ⟨115490, by rfl⟩ : syracuseStep 2463797 = 230981) (by norm_num)
theorem B1644637 : Blo 972592 1644637 := bbase (se 3 (by rfl) ⟨308369, by rfl⟩ : syracuseStep 1644637 = 616739) (by norm_num)
theorem B1480837 : Blo 972592 1480837 := bbase (se 4 (by rfl) ⟨138828, by rfl⟩ : syracuseStep 1480837 = 277657) (by norm_num)
theorem B1644725 : Blo 972592 1644725 := bbase (se 5 (by rfl) ⟨77096, by rfl⟩ : syracuseStep 1644725 = 154193) (by norm_num)
theorem B3283253 : Blo 972592 3283253 := bbase (se 5 (by rfl) ⟨153902, by rfl⟩ : syracuseStep 3283253 = 307805) (by norm_num)
theorem B1644853 : Blo 972592 1644853 := bbase (se 5 (by rfl) ⟨77102, by rfl⟩ : syracuseStep 1644853 = 154205) (by norm_num)
theorem B2005301 : Blo 972592 2005301 := bbase (se 5 (by rfl) ⟨93998, by rfl⟩ : syracuseStep 2005301 = 187997) (by norm_num)
theorem B2529677 : Blo 972592 2529677 := bbase (se 3 (by rfl) ⟨474314, by rfl⟩ : syracuseStep 2529677 = 948629) (by norm_num)
theorem B2464141 : Blo 972592 2464141 := bbase (se 3 (by rfl) ⟨462026, by rfl⟩ : syracuseStep 2464141 = 924053) (by norm_num)
theorem B1644941 : Blo 972592 1644941 := bbase (se 3 (by rfl) ⟨308426, by rfl⟩ : syracuseStep 1644941 = 616853) (by norm_num)
theorem B4692437 : Blo 972592 4692437 := bbase (se 7 (by rfl) ⟨54989, by rfl⟩ : syracuseStep 4692437 = 109979) (by norm_num)
theorem B8886773 : Blo 972592 8886773 := bbase (se 5 (by rfl) ⟨416567, by rfl⟩ : syracuseStep 8886773 = 833135) (by norm_num)
theorem B2464253 : Blo 972592 2464253 := bbase (se 3 (by rfl) ⟨462047, by rfl⟩ : syracuseStep 2464253 = 924095) (by norm_num)
theorem B1645069 : Blo 972592 1645069 := bbase (se 3 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 1645069 = 616901) (by norm_num)
theorem B1645157 : Blo 972592 1645157 := bbase (se 4 (by rfl) ⟨154233, by rfl⟩ : syracuseStep 1645157 = 308467) (by norm_num)
theorem B2464445 : Blo 972592 2464445 := bbase (se 3 (by rfl) ⟨462083, by rfl⟩ : syracuseStep 2464445 = 924167) (by norm_num)
theorem B3283685 : Blo 972592 3283685 := bbase (se 4 (by rfl) ⟨307845, by rfl⟩ : syracuseStep 3283685 = 615691) (by norm_num)
theorem B1645285 : Blo 972592 1645285 := bbase (se 4 (by rfl) ⟨154245, by rfl⟩ : syracuseStep 1645285 = 308491) (by norm_num)
theorem B1973053 : Blo 972592 1973053 := bbase (se 3 (by rfl) ⟨369947, by rfl⟩ : syracuseStep 1973053 = 739895) (by norm_num)
theorem B1645373 : Blo 972592 1645373 := bbase (se 3 (by rfl) ⟨308507, by rfl⟩ : syracuseStep 1645373 = 617015) (by norm_num)
theorem B1645501 : Blo 972592 1645501 := bbase (se 3 (by rfl) ⟨308531, by rfl⟩ : syracuseStep 1645501 = 617063) (by norm_num)
theorem B2464789 : Blo 972592 2464789 := bbase (se 6 (by rfl) ⟨57768, by rfl⟩ : syracuseStep 2464789 = 115537) (by norm_num)
theorem B1645589 : Blo 972592 1645589 := bbase (se 6 (by rfl) ⟨38568, by rfl⟩ : syracuseStep 1645589 = 77137) (by norm_num)
theorem B2464901 : Blo 972592 2464901 := bbase (se 4 (by rfl) ⟨231084, by rfl⟩ : syracuseStep 2464901 = 462169) (by norm_num)
theorem B3284117 : Blo 972592 3284117 := bbase (se 6 (by rfl) ⟨76971, by rfl⟩ : syracuseStep 3284117 = 153943) (by norm_num)
theorem B1645717 : Blo 972592 1645717 := bbase (se 6 (by rfl) ⟨38571, by rfl⟩ : syracuseStep 1645717 = 77143) (by norm_num)
theorem B4168901 : Blo 972592 4168901 := bbase (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) (by norm_num)
theorem B1645805 : Blo 972592 1645805 := bbase (se 3 (by rfl) ⟨308588, by rfl⟩ : syracuseStep 1645805 = 617177) (by norm_num)
theorem B2465093 : Blo 972592 2465093 := bbase (se 4 (by rfl) ⟨231102, by rfl⟩ : syracuseStep 2465093 = 462205) (by norm_num)
theorem B1645933 : Blo 972592 1645933 := bbase (se 3 (by rfl) ⟨308612, by rfl⟩ : syracuseStep 1645933 = 617225) (by norm_num)
theorem B3120565 : Blo 972592 3120565 := bbase (se 5 (by rfl) ⟨146276, by rfl⟩ : syracuseStep 3120565 = 292553) (by norm_num)
theorem B4169141 : Blo 972592 4169141 := bbase (se 5 (by rfl) ⟨195428, by rfl⟩ : syracuseStep 4169141 = 390857) (by norm_num)
theorem B1646021 : Blo 972592 1646021 := bbase (se 4 (by rfl) ⟨154314, by rfl⟩ : syracuseStep 1646021 = 308629) (by norm_num)
theorem B3284549 : Blo 972592 3284549 := bbase (se 4 (by rfl) ⟨307926, by rfl⟩ : syracuseStep 3284549 = 615853) (by norm_num)
theorem B1646149 : Blo 972592 1646149 := bbase (se 4 (by rfl) ⟨154326, by rfl⟩ : syracuseStep 1646149 = 308653) (by norm_num)
theorem B2465437 : Blo 972592 2465437 := bbase (se 3 (by rfl) ⟨462269, by rfl⟩ : syracuseStep 2465437 = 924539) (by norm_num)
theorem B1646237 : Blo 972592 1646237 := bbase (se 3 (by rfl) ⟨308669, by rfl⟩ : syracuseStep 1646237 = 617339) (by norm_num)
theorem B1318565 : Blo 972592 1318565 := bbase (se 4 (by rfl) ⟨123615, by rfl⟩ : syracuseStep 1318565 = 247231) (by norm_num)
theorem B5545685 : Blo 972592 5545685 := bbase (se 7 (by rfl) ⟨64988, by rfl⟩ : syracuseStep 5545685 = 129977) (by norm_num)
theorem B2465549 : Blo 972592 2465549 := bbase (se 3 (by rfl) ⟨462290, by rfl⟩ : syracuseStep 2465549 = 924581) (by norm_num)
theorem B1646365 : Blo 972592 1646365 := bbase (se 3 (by rfl) ⟨308693, by rfl⟩ : syracuseStep 1646365 = 617387) (by norm_num)
theorem B7020373 : Blo 972592 7020373 := bbase (se 9 (by rfl) ⟨20567, by rfl⟩ : syracuseStep 7020373 = 41135) (by norm_num)
theorem B1646453 : Blo 972592 1646453 := bbase (se 5 (by rfl) ⟨77177, by rfl⟩ : syracuseStep 1646453 = 154355) (by norm_num)
theorem B1187713 : Blo 972592 1187713 := bbase (se 2 (by rfl) ⟨445392, by rfl⟩ : syracuseStep 1187713 = 890785) (by norm_num)
theorem B2465741 : Blo 972592 2465741 := bbase (se 3 (by rfl) ⟨462326, by rfl⟩ : syracuseStep 2465741 = 924653) (by norm_num)
theorem B3284981 : Blo 972592 3284981 := bbase (se 5 (by rfl) ⟨153983, by rfl⟩ : syracuseStep 3284981 = 307967) (by norm_num)
theorem B1646581 : Blo 972592 1646581 := bbase (se 5 (by rfl) ⟨77183, by rfl⟩ : syracuseStep 1646581 = 154367) (by norm_num)
theorem B1646669 : Blo 972592 1646669 := bbase (se 3 (by rfl) ⟨308750, by rfl⟩ : syracuseStep 1646669 = 617501) (by norm_num)
theorem B6758549 : Blo 972592 6758549 := bbase (se 6 (by rfl) ⟨158403, by rfl⟩ : syracuseStep 6758549 = 316807) (by norm_num)
theorem B1876117 : Blo 972592 1876117 := bbase (se 6 (by rfl) ⟨43971, by rfl⟩ : syracuseStep 1876117 = 87943) (by norm_num)
theorem B1646797 : Blo 972592 1646797 := bbase (se 3 (by rfl) ⟨308774, by rfl⟩ : syracuseStep 1646797 = 617549) (by norm_num)
theorem B6004949 : Blo 972592 6004949 := bbase (se 7 (by rfl) ⟨70370, by rfl⟩ : syracuseStep 6004949 = 140741) (by norm_num)
theorem B2466085 : Blo 972592 2466085 := bbase (se 4 (by rfl) ⟨231195, by rfl⟩ : syracuseStep 2466085 = 462391) (by norm_num)
theorem B1646885 : Blo 972592 1646885 := bbase (se 4 (by rfl) ⟨154395, by rfl⟩ : syracuseStep 1646885 = 308791) (by norm_num)
theorem B1319261 : Blo 972592 1319261 := bbase (se 3 (by rfl) ⟨247361, by rfl⟩ : syracuseStep 1319261 = 494723) (by norm_num)
theorem B2466197 : Blo 972592 2466197 := bbase (se 6 (by rfl) ⟨57801, by rfl⟩ : syracuseStep 2466197 = 115603) (by norm_num)
theorem B3285413 : Blo 972592 3285413 := bbase (se 4 (by rfl) ⟨308007, by rfl⟩ : syracuseStep 3285413 = 616015) (by norm_num)
theorem B1647013 : Blo 972592 1647013 := bbase (se 4 (by rfl) ⟨154407, by rfl⟩ : syracuseStep 1647013 = 308815) (by norm_num)
theorem B1647101 : Blo 972592 1647101 := bbase (se 3 (by rfl) ⟨308831, by rfl⟩ : syracuseStep 1647101 = 617663) (by norm_num)
theorem B4923989 : Blo 972592 4923989 := bbase (se 8 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 4923989 = 57703) (by norm_num)
theorem B2466389 : Blo 972592 2466389 := bbase (se 8 (by rfl) ⟨14451, by rfl⟩ : syracuseStep 2466389 = 28903) (by norm_num)
theorem B1647229 : Blo 972592 1647229 := bbase (se 3 (by rfl) ⟨308855, by rfl⟩ : syracuseStep 1647229 = 617711) (by norm_num)
theorem B1647317 : Blo 972592 1647317 := bbase (se 7 (by rfl) ⟨19304, by rfl⟩ : syracuseStep 1647317 = 38609) (by norm_num)
theorem B3285845 : Blo 972592 3285845 := bbase (se 9 (by rfl) ⟨9626, by rfl⟩ : syracuseStep 3285845 = 19253) (by norm_num)
theorem B1647445 : Blo 972592 1647445 := bbase (se 9 (by rfl) ⟨4826, by rfl⟩ : syracuseStep 1647445 = 9653) (by norm_num)
theorem B2630501 : Blo 972592 2630501 := bbase (se 4 (by rfl) ⟨246609, by rfl⟩ : syracuseStep 2630501 = 493219) (by norm_num)
theorem B2466733 : Blo 972592 2466733 := bbase (se 3 (by rfl) ⟨462512, by rfl⟩ : syracuseStep 2466733 = 925025) (by norm_num)
theorem B1647533 : Blo 972592 1647533 := bbase (se 3 (by rfl) ⟨308912, by rfl⟩ : syracuseStep 1647533 = 617825) (by norm_num)
theorem B3122165 : Blo 972592 3122165 := bbase (se 5 (by rfl) ⟨146351, by rfl⟩ : syracuseStep 3122165 = 292703) (by norm_num)
theorem B10003445 : Blo 972592 10003445 := bbase (se 5 (by rfl) ⟨468911, by rfl⟩ : syracuseStep 10003445 = 937823) (by norm_num)
theorem B2466845 : Blo 972592 2466845 := bbase (se 3 (by rfl) ⟨462533, by rfl⟩ : syracuseStep 2466845 = 925067) (by norm_num)
theorem B1647661 : Blo 972592 1647661 := bbase (se 3 (by rfl) ⟨308936, by rfl⟩ : syracuseStep 1647661 = 617873) (by norm_num)
theorem B1385533 : Blo 972592 1385533 := bbase (se 3 (by rfl) ⟨259787, by rfl⟩ : syracuseStep 1385533 = 519575) (by norm_num)
theorem B1975357 : Blo 972592 1975357 := bbase (se 3 (by rfl) ⟨370379, by rfl⟩ : syracuseStep 1975357 = 740759) (by norm_num)
theorem B7414901 : Blo 972592 7414901 := bbase (se 5 (by rfl) ⟨347573, by rfl⟩ : syracuseStep 7414901 = 695147) (by norm_num)
theorem B1647749 : Blo 972592 1647749 := bbase (se 4 (by rfl) ⟨154476, by rfl⟩ : syracuseStep 1647749 = 308953) (by norm_num)
theorem B2467037 : Blo 972592 2467037 := bbase (se 3 (by rfl) ⟨462569, by rfl⟩ : syracuseStep 2467037 = 925139) (by norm_num)
theorem B3286277 : Blo 972592 3286277 := bbase (se 4 (by rfl) ⟨308088, by rfl⟩ : syracuseStep 3286277 = 616177) (by norm_num)
theorem B1647877 : Blo 972592 1647877 := bbase (se 4 (by rfl) ⟨154488, by rfl⟩ : syracuseStep 1647877 = 308977) (by norm_num)
theorem B1647965 : Blo 972592 1647965 := bbase (se 3 (by rfl) ⟨308993, by rfl⟩ : syracuseStep 1647965 = 617987) (by norm_num)
theorem B1484165 : Blo 972592 1484165 := bbase (se 4 (by rfl) ⟨139140, by rfl⟩ : syracuseStep 1484165 = 278281) (by norm_num)
theorem B2467381 : Blo 972592 2467381 := bbase (se 5 (by rfl) ⟨115658, by rfl⟩ : syracuseStep 2467381 = 231317) (by norm_num)
theorem B1975909 : Blo 972592 1975909 := bbase (se 4 (by rfl) ⟨185241, by rfl⟩ : syracuseStep 1975909 = 370483) (by norm_num)
theorem B2107037 : Blo 972592 2107037 := bbase (se 3 (by rfl) ⟨395069, by rfl⟩ : syracuseStep 2107037 = 790139) (by norm_num)
theorem B2467493 : Blo 972592 2467493 := bbase (se 4 (by rfl) ⟨231327, by rfl⟩ : syracuseStep 2467493 = 462655) (by norm_num)
theorem B4171429 : Blo 972592 4171429 := bbase (se 4 (by rfl) ⟨391071, by rfl⟩ : syracuseStep 4171429 = 782143) (by norm_num)
theorem B3286709 : Blo 972592 3286709 := bbase (se 5 (by rfl) ⟨154064, by rfl⟩ : syracuseStep 3286709 = 308129) (by norm_num)
theorem B1386325 : Blo 972592 1386325 := bbase (se 9 (by rfl) ⟨4061, by rfl⟩ : syracuseStep 1386325 = 8123) (by norm_num)
theorem B4925285 : Blo 972592 4925285 := bbase (se 4 (by rfl) ⟨461745, by rfl⟩ : syracuseStep 4925285 = 923491) (by norm_num)
theorem B2467685 : Blo 972592 2467685 := bbase (se 4 (by rfl) ⟨231345, by rfl⟩ : syracuseStep 2467685 = 462691) (by norm_num)
theorem B3123269 : Blo 972592 3123269 := bbase (se 4 (by rfl) ⟨292806, by rfl⟩ : syracuseStep 3123269 = 585613) (by norm_num)
theorem B3287141 : Blo 972592 3287141 := bbase (se 4 (by rfl) ⟨308169, by rfl⟩ : syracuseStep 3287141 = 616339) (by norm_num)
theorem B1386661 : Blo 972592 1386661 := bbase (se 4 (by rfl) ⟨129999, by rfl⟩ : syracuseStep 1386661 = 259999) (by norm_num)
theorem B2468029 : Blo 972592 2468029 := bbase (se 3 (by rfl) ⟨462755, by rfl⟩ : syracuseStep 2468029 = 925511) (by norm_num)
theorem B1976557 : Blo 972592 1976557 := bbase (se 3 (by rfl) ⟨370604, by rfl⟩ : syracuseStep 1976557 = 741209) (by norm_num)
theorem B1976621 : Blo 972592 1976621 := bbase (se 3 (by rfl) ⟨370616, by rfl⟩ : syracuseStep 1976621 = 741233) (by norm_num)
theorem B2468141 : Blo 972592 2468141 := bbase (se 3 (by rfl) ⟨462776, by rfl⟩ : syracuseStep 2468141 = 925553) (by norm_num)
theorem B1386877 : Blo 972592 1386877 := bbase (se 3 (by rfl) ⟨260039, by rfl⟩ : syracuseStep 1386877 = 520079) (by norm_num)
theorem B1780093 : Blo 972592 1780093 := bbase (se 3 (by rfl) ⟨333767, by rfl⟩ : syracuseStep 1780093 = 667535) (by norm_num)
theorem B2468333 : Blo 972592 2468333 := bbase (se 3 (by rfl) ⟨462812, by rfl⟩ : syracuseStep 2468333 = 925625) (by norm_num)
theorem B3287573 : Blo 972592 3287573 := bbase (se 6 (by rfl) ⟨77052, by rfl⟩ : syracuseStep 3287573 = 154105) (by norm_num)
theorem B2337349 : Blo 972592 2337349 := bbase (se 4 (by rfl) ⟨219126, by rfl⟩ : syracuseStep 2337349 = 438253) (by norm_num)
theorem B2960117 : Blo 972592 2960117 := bbase (se 5 (by rfl) ⟨138755, by rfl⟩ : syracuseStep 2960117 = 277511) (by norm_num)
theorem B1387253 : Blo 972592 1387253 := bbase (se 5 (by rfl) ⟨65027, by rfl⟩ : syracuseStep 1387253 = 130055) (by norm_num)
theorem B2960165 : Blo 972592 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B2468677 : Blo 972592 2468677 := bbase (se 4 (by rfl) ⟨231438, by rfl⟩ : syracuseStep 2468677 = 462877) (by norm_num)
theorem B1977205 : Blo 972592 1977205 := bbase (se 5 (by rfl) ⟨92681, by rfl⟩ : syracuseStep 1977205 = 185363) (by norm_num)
theorem B2468789 : Blo 972592 2468789 := bbase (se 5 (by rfl) ⟨115724, by rfl⟩ : syracuseStep 2468789 = 231449) (by norm_num)
theorem B3288005 : Blo 972592 3288005 := bbase (se 4 (by rfl) ⟨308250, by rfl⟩ : syracuseStep 3288005 = 616501) (by norm_num)
theorem B6663221 : Blo 972592 6663221 := bbase (se 5 (by rfl) ⟨312338, by rfl⟩ : syracuseStep 6663221 = 624677) (by norm_num)
theorem B4926581 : Blo 972592 4926581 := bbase (se 5 (by rfl) ⟨230933, by rfl⟩ : syracuseStep 4926581 = 461867) (by norm_num)
theorem B2468981 : Blo 972592 2468981 := bbase (se 5 (by rfl) ⟨115733, by rfl⟩ : syracuseStep 2468981 = 231467) (by norm_num)
theorem B6237461 : Blo 972592 6237461 := bbase (se 6 (by rfl) ⟨146190, by rfl⟩ : syracuseStep 6237461 = 292381) (by norm_num)
theorem B3288437 : Blo 972592 3288437 := bbase (se 5 (by rfl) ⟨154145, by rfl⟩ : syracuseStep 3288437 = 308291) (by norm_num)
theorem B1584533 : Blo 972592 1584533 := bbase (se 6 (by rfl) ⟨37137, by rfl⟩ : syracuseStep 1584533 = 74275) (by norm_num)
theorem B1846709 : Blo 972592 1846709 := bbase (se 5 (by rfl) ⟨86564, by rfl⟩ : syracuseStep 1846709 = 173129) (by norm_num)
theorem B2469325 : Blo 972592 2469325 := bbase (se 3 (by rfl) ⟨462998, by rfl⟩ : syracuseStep 2469325 = 925997) (by norm_num)
theorem B2469437 : Blo 972592 2469437 := bbase (se 3 (by rfl) ⟨463019, by rfl⟩ : syracuseStep 2469437 = 926039) (by norm_num)
theorem B2469629 : Blo 972592 2469629 := bbase (se 3 (by rfl) ⟨463055, by rfl⟩ : syracuseStep 2469629 = 926111) (by norm_num)
theorem B3288869 : Blo 972592 3288869 := bbase (se 4 (by rfl) ⟨308331, by rfl⟩ : syracuseStep 3288869 = 616663) (by norm_num)
theorem B3518261 : Blo 972592 3518261 := bbase (se 5 (by rfl) ⟨164918, by rfl⟩ : syracuseStep 3518261 = 329837) (by norm_num)
theorem B2502485 : Blo 972592 2502485 := bbase (se 9 (by rfl) ⟨7331, by rfl⟩ : syracuseStep 2502485 = 14663) (by norm_num)
theorem B3125189 : Blo 972592 3125189 := bbase (se 4 (by rfl) ⟨292986, by rfl⟩ : syracuseStep 3125189 = 585973) (by norm_num)
theorem B3518405 : Blo 972592 3518405 := bbase (se 4 (by rfl) ⟨329850, by rfl⟩ : syracuseStep 3518405 = 659701) (by norm_num)
theorem B1978373 : Blo 972592 1978373 := bbase (se 4 (by rfl) ⟨185472, by rfl⟩ : syracuseStep 1978373 = 370945) (by norm_num)
theorem B2469973 : Blo 972592 2469973 := bbase (se 8 (by rfl) ⟨14472, by rfl⟩ : syracuseStep 2469973 = 28945) (by norm_num)
theorem B1388677 : Blo 972592 1388677 := bbase (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) (by norm_num)
theorem B1847461 : Blo 972592 1847461 := bbase (se 4 (by rfl) ⟨173199, by rfl⟩ : syracuseStep 1847461 = 346399) (by norm_num)
theorem B2470085 : Blo 972592 2470085 := bbase (se 4 (by rfl) ⟨231570, by rfl⟩ : syracuseStep 2470085 = 463141) (by norm_num)
theorem B3289301 : Blo 972592 3289301 := bbase (se 7 (by rfl) ⟨38546, by rfl⟩ : syracuseStep 3289301 = 77093) (by norm_num)
theorem B1847605 : Blo 972592 1847605 := bbase (se 5 (by rfl) ⟨86606, by rfl⟩ : syracuseStep 1847605 = 173213) (by norm_num)
theorem B1585469 : Blo 972592 1585469 := bbase (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) (by norm_num)
theorem B4927877 : Blo 972592 4927877 := bbase (se 4 (by rfl) ⟨461988, by rfl⟩ : syracuseStep 4927877 = 923977) (by norm_num)
theorem B2470277 : Blo 972592 2470277 := bbase (se 4 (by rfl) ⟨231588, by rfl⟩ : syracuseStep 2470277 = 463177) (by norm_num)
theorem B1847765 : Blo 972592 1847765 := bbase (se 7 (by rfl) ⟨21653, by rfl⟩ : syracuseStep 1847765 = 43307) (by norm_num)
theorem B2503181 : Blo 972592 2503181 := bbase (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) (by norm_num)
theorem B1094197 : Blo 972592 1094197 := bbase (se 5 (by rfl) ⟨51290, by rfl⟩ : syracuseStep 1094197 = 102581) (by norm_num)
theorem B9351733 : Blo 972592 9351733 := bbase (se 5 (by rfl) ⟨438362, by rfl⟩ : syracuseStep 9351733 = 876725) (by norm_num)
theorem B1978949 : Blo 972592 1978949 := bbase (se 4 (by rfl) ⟨185526, by rfl⟩ : syracuseStep 1978949 = 371053) (by norm_num)
theorem B1094233 : Blo 972592 1094233 := bbase (se 2 (by rfl) ⟨410337, by rfl⟩ : syracuseStep 1094233 = 820675) (by norm_num)
theorem B1847909 : Blo 972592 1847909 := bbase (se 4 (by rfl) ⟨173241, by rfl⟩ : syracuseStep 1847909 = 346483) (by norm_num)
theorem B2077301 : Blo 972592 2077301 := bbase (se 5 (by rfl) ⟨97373, by rfl⟩ : syracuseStep 2077301 = 194747) (by norm_num)
theorem B1094269 : Blo 972592 1094269 := bbase (se 3 (by rfl) ⟨205175, by rfl⟩ : syracuseStep 1094269 = 410351) (by norm_num)
theorem B3289733 : Blo 972592 3289733 := bbase (se 4 (by rfl) ⟨308412, by rfl⟩ : syracuseStep 3289733 = 616825) (by norm_num)
theorem B1094305 : Blo 972592 1094305 := bbase (se 2 (by rfl) ⟨410364, by rfl⟩ : syracuseStep 1094305 = 820729) (by norm_num)
theorem B1094341 : Blo 972592 1094341 := bbase (se 4 (by rfl) ⟨102594, by rfl⟩ : syracuseStep 1094341 = 205189) (by norm_num)
theorem B1389269 : Blo 972592 1389269 := bbase (se 7 (by rfl) ⟨16280, by rfl⟩ : syracuseStep 1389269 = 32561) (by norm_num)
theorem B2470621 : Blo 972592 2470621 := bbase (se 3 (by rfl) ⟨463241, by rfl⟩ : syracuseStep 2470621 = 926483) (by norm_num)
theorem B1094377 : Blo 972592 1094377 := bbase (se 2 (by rfl) ⟨410391, by rfl⟩ : syracuseStep 1094377 = 820783) (by norm_num)
theorem B2077445 : Blo 972592 2077445 := bbase (se 4 (by rfl) ⟨194760, by rfl⟩ : syracuseStep 2077445 = 389521) (by norm_num)
theorem B2667269 : Blo 972592 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B1094413 : Blo 972592 1094413 := bbase (se 3 (by rfl) ⟨205202, by rfl⟩ : syracuseStep 1094413 = 410405) (by norm_num)
theorem B1389349 : Blo 972592 1389349 := bbase (se 4 (by rfl) ⟨130251, by rfl⟩ : syracuseStep 1389349 = 260503) (by norm_num)
theorem B1094449 : Blo 972592 1094449 := bbase (se 2 (by rfl) ⟨410418, by rfl⟩ : syracuseStep 1094449 = 820837) (by norm_num)
theorem B2470733 : Blo 972592 2470733 := bbase (se 3 (by rfl) ⟨463262, by rfl⟩ : syracuseStep 2470733 = 926525) (by norm_num)
theorem B1094485 : Blo 972592 1094485 := bbase (se 9 (by rfl) ⟨3206, by rfl⟩ : syracuseStep 1094485 = 6413) (by norm_num)
theorem B1094521 : Blo 972592 1094521 := bbase (se 2 (by rfl) ⟨410445, by rfl⟩ : syracuseStep 1094521 = 820891) (by norm_num)
theorem B1848197 : Blo 972592 1848197 := bbase (se 4 (by rfl) ⟨173268, by rfl⟩ : syracuseStep 1848197 = 346537) (by norm_num)
theorem B8893333 : Blo 972592 8893333 := bbase (se 6 (by rfl) ⟨208437, by rfl⟩ : syracuseStep 8893333 = 416875) (by norm_num)
theorem B1094557 : Blo 972592 1094557 := bbase (se 3 (by rfl) ⟨205229, by rfl⟩ : syracuseStep 1094557 = 410459) (by norm_num)
theorem B2339741 : Blo 972592 2339741 := bbase (se 3 (by rfl) ⟨438701, by rfl⟩ : syracuseStep 2339741 = 877403) (by norm_num)
theorem B1389469 : Blo 972592 1389469 := bbase (se 3 (by rfl) ⟨260525, by rfl⟩ : syracuseStep 1389469 = 521051) (by norm_num)
theorem B1094593 : Blo 972592 1094593 := bbase (se 2 (by rfl) ⟨410472, by rfl⟩ : syracuseStep 1094593 = 820945) (by norm_num)
theorem B1094629 : Blo 972592 1094629 := bbase (se 4 (by rfl) ⟨102621, by rfl⟩ : syracuseStep 1094629 = 205243) (by norm_num)
theorem B1389565 : Blo 972592 1389565 := bbase (se 3 (by rfl) ⟨260543, by rfl⟩ : syracuseStep 1389565 = 521087) (by norm_num)
theorem B1094665 : Blo 972592 1094665 := bbase (se 2 (by rfl) ⟨410499, by rfl⟩ : syracuseStep 1094665 = 820999) (by norm_num)
theorem B2470925 : Blo 972592 2470925 := bbase (se 3 (by rfl) ⟨463298, by rfl⟩ : syracuseStep 2470925 = 926597) (by norm_num)
theorem B1848349 : Blo 972592 1848349 := bbase (se 3 (by rfl) ⟨346565, by rfl⟩ : syracuseStep 1848349 = 693131) (by norm_num)
theorem B1094701 : Blo 972592 1094701 := bbase (se 3 (by rfl) ⟨205256, by rfl⟩ : syracuseStep 1094701 = 410513) (by norm_num)
theorem B2339885 : Blo 972592 2339885 := bbase (se 3 (by rfl) ⟨438728, by rfl⟩ : syracuseStep 2339885 = 877457) (by norm_num)
theorem B3290165 : Blo 972592 3290165 := bbase (se 5 (by rfl) ⟨154226, by rfl⟩ : syracuseStep 3290165 = 308453) (by norm_num)
theorem B1094737 : Blo 972592 1094737 := bbase (se 2 (by rfl) ⟨410526, by rfl⟩ : syracuseStep 1094737 = 821053) (by norm_num)
theorem B2077805 : Blo 972592 2077805 := bbase (se 3 (by rfl) ⟨389588, by rfl⟩ : syracuseStep 2077805 = 779177) (by norm_num)
theorem B1094773 : Blo 972592 1094773 := bbase (se 5 (by rfl) ⟨51317, by rfl⟩ : syracuseStep 1094773 = 102635) (by norm_num)
theorem B1094809 : Blo 972592 1094809 := bbase (se 2 (by rfl) ⟨410553, by rfl⟩ : syracuseStep 1094809 = 821107) (by norm_num)
theorem B3159205 : Blo 972592 3159205 := bbase (se 4 (by rfl) ⟨296175, by rfl⟩ : syracuseStep 3159205 = 592351) (by norm_num)
theorem B2962597 : Blo 972592 2962597 := bbase (se 4 (by rfl) ⟨277743, by rfl⟩ : syracuseStep 2962597 = 555487) (by norm_num)
theorem B1094845 : Blo 972592 1094845 := bbase (se 3 (by rfl) ⟨205283, by rfl⟩ : syracuseStep 1094845 = 410567) (by norm_num)
theorem B1094881 : Blo 972592 1094881 := bbase (se 2 (by rfl) ⟨410580, by rfl⟩ : syracuseStep 1094881 = 821161) (by norm_num)
theorem B1094917 : Blo 972592 1094917 := bbase (se 4 (by rfl) ⟨102648, by rfl⟩ : syracuseStep 1094917 = 205297) (by norm_num)
theorem B1094953 : Blo 972592 1094953 := bbase (se 2 (by rfl) ⟨410607, by rfl⟩ : syracuseStep 1094953 = 821215) (by norm_num)
theorem B1094989 : Blo 972592 1094989 := bbase (se 3 (by rfl) ⟨205310, by rfl⟩ : syracuseStep 1094989 = 410621) (by norm_num)
theorem B1848653 : Blo 972592 1848653 := bbase (se 3 (by rfl) ⟨346622, by rfl⟩ : syracuseStep 1848653 = 693245) (by norm_num)
theorem B3126613 : Blo 972592 3126613 := bbase (se 13 (by rfl) ⟨572, by rfl⟩ : syracuseStep 3126613 = 1145) (by norm_num)
theorem B2471269 : Blo 972592 2471269 := bbase (se 4 (by rfl) ⟨231681, by rfl⟩ : syracuseStep 2471269 = 463363) (by norm_num)
theorem B1095025 : Blo 972592 1095025 := bbase (se 2 (by rfl) ⟨410634, by rfl⟩ : syracuseStep 1095025 = 821269) (by norm_num)
theorem B1095061 : Blo 972592 1095061 := bbase (se 6 (by rfl) ⟨25665, by rfl⟩ : syracuseStep 1095061 = 51331) (by norm_num)
theorem B1095097 : Blo 972592 1095097 := bbase (se 2 (by rfl) ⟨410661, by rfl⟩ : syracuseStep 1095097 = 821323) (by norm_num)
theorem B2471381 : Blo 972592 2471381 := bbase (se 7 (by rfl) ⟨28961, by rfl⟩ : syracuseStep 2471381 = 57923) (by norm_num)
theorem B1095133 : Blo 972592 1095133 := bbase (se 3 (by rfl) ⟨205337, by rfl⟩ : syracuseStep 1095133 = 410675) (by norm_num)
theorem B3290597 : Blo 972592 3290597 := bbase (se 4 (by rfl) ⟨308493, by rfl⟩ : syracuseStep 3290597 = 616987) (by norm_num)
theorem B1390061 : Blo 972592 1390061 := bbase (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) (by norm_num)
theorem B1095169 : Blo 972592 1095169 := bbase (se 2 (by rfl) ⟨410688, by rfl⟩ : syracuseStep 1095169 = 821377) (by norm_num)
theorem B1783309 : Blo 972592 1783309 := bbase (se 3 (by rfl) ⟨334370, by rfl⟩ : syracuseStep 1783309 = 668741) (by norm_num)
theorem B1095205 : Blo 972592 1095205 := bbase (se 4 (by rfl) ⟨102675, by rfl⟩ : syracuseStep 1095205 = 205351) (by norm_num)
theorem B1095241 : Blo 972592 1095241 := bbase (se 2 (by rfl) ⟨410715, by rfl⟩ : syracuseStep 1095241 = 821431) (by norm_num)
theorem B1095277 : Blo 972592 1095277 := bbase (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) (by norm_num)
theorem B1095313 : Blo 972592 1095313 := bbase (se 2 (by rfl) ⟨410742, by rfl⟩ : syracuseStep 1095313 = 821485) (by norm_num)
theorem B4929173 : Blo 972592 4929173 := bbase (se 6 (by rfl) ⟨115527, by rfl⟩ : syracuseStep 4929173 = 231055) (by norm_num)
theorem B2471573 : Blo 972592 2471573 := bbase (se 6 (by rfl) ⟨57927, by rfl⟩ : syracuseStep 2471573 = 115855) (by norm_num)
theorem B1095349 : Blo 972592 1095349 := bbase (se 5 (by rfl) ⟨51344, by rfl⟩ : syracuseStep 1095349 = 102689) (by norm_num)
theorem B1095385 : Blo 972592 1095385 := bbase (se 2 (by rfl) ⟨410769, by rfl⟩ : syracuseStep 1095385 = 821539) (by norm_num)
theorem B1095421 : Blo 972592 1095421 := bbase (se 3 (by rfl) ⟨205391, by rfl⟩ : syracuseStep 1095421 = 410783) (by norm_num)
theorem B3127061 : Blo 972592 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B1095457 : Blo 972592 1095457 := bbase (se 2 (by rfl) ⟨410796, by rfl⟩ : syracuseStep 1095457 = 821593) (by norm_num)
theorem B1095493 : Blo 972592 1095493 := bbase (se 4 (by rfl) ⟨102702, by rfl⟩ : syracuseStep 1095493 = 205405) (by norm_num)
theorem B1095529 : Blo 972592 1095529 := bbase (se 2 (by rfl) ⟨410823, by rfl⟩ : syracuseStep 1095529 = 821647) (by norm_num)
theorem B1095565 : Blo 972592 1095565 := bbase (se 3 (by rfl) ⟨205418, by rfl⟩ : syracuseStep 1095565 = 410837) (by norm_num)
theorem B2635669 : Blo 972592 2635669 := bbase (se 6 (by rfl) ⟨61773, by rfl⟩ : syracuseStep 2635669 = 123547) (by norm_num)
theorem B3291029 : Blo 972592 3291029 := bbase (se 6 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 3291029 = 154267) (by norm_num)
theorem B1095601 : Blo 972592 1095601 := bbase (se 2 (by rfl) ⟨410850, by rfl⟩ : syracuseStep 1095601 = 821701) (by norm_num)
theorem B1095637 : Blo 972592 1095637 := bbase (se 7 (by rfl) ⟨12839, by rfl⟩ : syracuseStep 1095637 = 25679) (by norm_num)
theorem B2078693 : Blo 972592 2078693 := bbase (se 4 (by rfl) ⟨194877, by rfl⟩ : syracuseStep 2078693 = 389755) (by norm_num)
theorem B2471917 : Blo 972592 2471917 := bbase (se 3 (by rfl) ⟨463484, by rfl⟩ : syracuseStep 2471917 = 926969) (by norm_num)
theorem B1095673 : Blo 972592 1095673 := bbase (se 2 (by rfl) ⟨410877, by rfl⟩ : syracuseStep 1095673 = 821755) (by norm_num)
theorem B1095709 : Blo 972592 1095709 := bbase (se 3 (by rfl) ⟨205445, by rfl⟩ : syracuseStep 1095709 = 410891) (by norm_num)
theorem B1849405 : Blo 972592 1849405 := bbase (se 3 (by rfl) ⟨346763, by rfl⟩ : syracuseStep 1849405 = 693527) (by norm_num)
theorem B1095745 : Blo 972592 1095745 := bbase (se 2 (by rfl) ⟨410904, by rfl⟩ : syracuseStep 1095745 = 821809) (by norm_num)
theorem B16660565 : Blo 972592 16660565 := bbase (se 8 (by rfl) ⟨97620, by rfl⟩ : syracuseStep 16660565 = 195241) (by norm_num)
theorem B1095781 : Blo 972592 1095781 := bbase (se 4 (by rfl) ⟨102729, by rfl⟩ : syracuseStep 1095781 = 205459) (by norm_num)
theorem B1095817 : Blo 972592 1095817 := bbase (se 2 (by rfl) ⟨410931, by rfl⟩ : syracuseStep 1095817 = 821863) (by norm_num)
theorem B1095853 : Blo 972592 1095853 := bbase (se 3 (by rfl) ⟨205472, by rfl⟩ : syracuseStep 1095853 = 410945) (by norm_num)
theorem B1849549 : Blo 972592 1849549 := bbase (se 3 (by rfl) ⟨346790, by rfl⟩ : syracuseStep 1849549 = 693581) (by norm_num)
theorem B1095889 : Blo 972592 1095889 := bbase (se 2 (by rfl) ⟨410958, by rfl⟩ : syracuseStep 1095889 = 821917) (by norm_num)
theorem B29997269 : Blo 972592 29997269 := bbase (se 7 (by rfl) ⟨351530, by rfl⟩ : syracuseStep 29997269 = 703061) (by norm_num)
theorem B2078941 : Blo 972592 2078941 := bbase (se 3 (by rfl) ⟨389801, by rfl⟩ : syracuseStep 2078941 = 779603) (by norm_num)
theorem B1095925 : Blo 972592 1095925 := bbase (se 5 (by rfl) ⟨51371, by rfl⟩ : syracuseStep 1095925 = 102743) (by norm_num)
theorem B1095961 : Blo 972592 1095961 := bbase (se 2 (by rfl) ⟨410985, by rfl⟩ : syracuseStep 1095961 = 821971) (by norm_num)
theorem B1095997 : Blo 972592 1095997 := bbase (se 3 (by rfl) ⟨205499, by rfl⟩ : syracuseStep 1095997 = 410999) (by norm_num)
theorem B3291461 : Blo 972592 3291461 := bbase (se 4 (by rfl) ⟨308574, by rfl⟩ : syracuseStep 3291461 = 617149) (by norm_num)
theorem B1096033 : Blo 972592 1096033 := bbase (se 2 (by rfl) ⟨411012, by rfl⟩ : syracuseStep 1096033 = 822025) (by norm_num)
theorem B1849709 : Blo 972592 1849709 := bbase (se 3 (by rfl) ⟨346820, by rfl⟩ : syracuseStep 1849709 = 693641) (by norm_num)
theorem B1096069 : Blo 972592 1096069 := bbase (se 4 (by rfl) ⟨102756, by rfl⟩ : syracuseStep 1096069 = 205513) (by norm_num)
theorem B1096105 : Blo 972592 1096105 := bbase (se 2 (by rfl) ⟨411039, by rfl⟩ : syracuseStep 1096105 = 822079) (by norm_num)
theorem B1030577 : Blo 972592 1030577 := bbase (se 2 (by rfl) ⟨386466, by rfl⟩ : syracuseStep 1030577 = 772933) (by norm_num)
theorem B1096141 : Blo 972592 1096141 := bbase (se 3 (by rfl) ⟨205526, by rfl⟩ : syracuseStep 1096141 = 411053) (by norm_num)
theorem B1096177 : Blo 972592 1096177 := bbase (se 2 (by rfl) ⟨411066, by rfl⟩ : syracuseStep 1096177 = 822133) (by norm_num)
theorem B1849853 : Blo 972592 1849853 := bbase (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) (by norm_num)
theorem B1096213 : Blo 972592 1096213 := bbase (se 6 (by rfl) ⟨25692, by rfl⟩ : syracuseStep 1096213 = 51385) (by norm_num)
theorem B1096249 : Blo 972592 1096249 := bbase (se 2 (by rfl) ⟨411093, by rfl⟩ : syracuseStep 1096249 = 822187) (by norm_num)
theorem B2374229 : Blo 972592 2374229 := bbase (se 8 (by rfl) ⟨13911, by rfl⟩ : syracuseStep 2374229 = 27823) (by norm_num)
theorem B1096285 : Blo 972592 1096285 := bbase (se 3 (by rfl) ⟨205553, by rfl⟩ : syracuseStep 1096285 = 411107) (by norm_num)
theorem B1096321 : Blo 972592 1096321 := bbase (se 2 (by rfl) ⟨411120, by rfl⟩ : syracuseStep 1096321 = 822241) (by norm_num)
theorem B1096357 : Blo 972592 1096357 := bbase (se 4 (by rfl) ⟨102783, by rfl⟩ : syracuseStep 1096357 = 205567) (by norm_num)
theorem B1096393 : Blo 972592 1096393 := bbase (se 2 (by rfl) ⟨411147, by rfl⟩ : syracuseStep 1096393 = 822295) (by norm_num)
theorem B2079445 : Blo 972592 2079445 := bbase (se 7 (by rfl) ⟨24368, by rfl⟩ : syracuseStep 2079445 = 48737) (by norm_num)
theorem B1096429 : Blo 972592 1096429 := bbase (se 3 (by rfl) ⟨205580, by rfl⟩ : syracuseStep 1096429 = 411161) (by norm_num)
theorem B3291893 : Blo 972592 3291893 := bbase (se 5 (by rfl) ⟨154307, by rfl⟩ : syracuseStep 3291893 = 308615) (by norm_num)
theorem B1096465 : Blo 972592 1096465 := bbase (se 2 (by rfl) ⟨411174, by rfl⟩ : syracuseStep 1096465 = 822349) (by norm_num)
theorem B1850141 : Blo 972592 1850141 := bbase (se 3 (by rfl) ⟨346901, by rfl⟩ : syracuseStep 1850141 = 693803) (by norm_num)
theorem B1096501 : Blo 972592 1096501 := bbase (se 5 (by rfl) ⟨51398, by rfl⟩ : syracuseStep 1096501 = 102797) (by norm_num)
theorem B1096537 : Blo 972592 1096537 := bbase (se 2 (by rfl) ⟨411201, by rfl⟩ : syracuseStep 1096537 = 822403) (by norm_num)
theorem B1096573 : Blo 972592 1096573 := bbase (se 3 (by rfl) ⟨205607, by rfl⟩ : syracuseStep 1096573 = 411215) (by norm_num)
theorem B1096609 : Blo 972592 1096609 := bbase (se 2 (by rfl) ⟨411228, by rfl⟩ : syracuseStep 1096609 = 822457) (by norm_num)
theorem B4930469 : Blo 972592 4930469 := bbase (se 4 (by rfl) ⟨462231, by rfl⟩ : syracuseStep 4930469 = 924463) (by norm_num)
theorem B1850293 : Blo 972592 1850293 := bbase (se 5 (by rfl) ⟨86732, by rfl⟩ : syracuseStep 1850293 = 173465) (by norm_num)
theorem B1096645 : Blo 972592 1096645 := bbase (se 4 (by rfl) ⟨102810, by rfl⟩ : syracuseStep 1096645 = 205621) (by norm_num)
theorem B1096681 : Blo 972592 1096681 := bbase (se 2 (by rfl) ⟨411255, by rfl⟩ : syracuseStep 1096681 = 822511) (by norm_num)
theorem B2341885 : Blo 972592 2341885 := bbase (se 3 (by rfl) ⟨439103, by rfl⟩ : syracuseStep 2341885 = 878207) (by norm_num)
theorem B2112509 : Blo 972592 2112509 := bbase (se 3 (by rfl) ⟨396095, by rfl⟩ : syracuseStep 2112509 = 792191) (by norm_num)
theorem B1096717 : Blo 972592 1096717 := bbase (se 3 (by rfl) ⟨205634, by rfl⟩ : syracuseStep 1096717 = 411269) (by norm_num)
theorem B1096753 : Blo 972592 1096753 := bbase (se 2 (by rfl) ⟨411282, by rfl⟩ : syracuseStep 1096753 = 822565) (by norm_num)
theorem B6241333 : Blo 972592 6241333 := bbase (se 5 (by rfl) ⟨292562, by rfl⟩ : syracuseStep 6241333 = 585125) (by norm_num)
theorem B2636869 : Blo 972592 2636869 := bbase (se 4 (by rfl) ⟨247206, by rfl⟩ : syracuseStep 2636869 = 494413) (by norm_num)
theorem B1096789 : Blo 972592 1096789 := bbase (se 8 (by rfl) ⟨6426, by rfl⟩ : syracuseStep 1096789 = 12853) (by norm_num)
theorem B1096825 : Blo 972592 1096825 := bbase (se 2 (by rfl) ⟨411309, by rfl⟩ : syracuseStep 1096825 = 822619) (by norm_num)
theorem B1096861 : Blo 972592 1096861 := bbase (se 3 (by rfl) ⟨205661, by rfl⟩ : syracuseStep 1096861 = 411323) (by norm_num)
theorem B3292325 : Blo 972592 3292325 := bbase (se 4 (by rfl) ⟨308655, by rfl⟩ : syracuseStep 3292325 = 617311) (by norm_num)
theorem B2636965 : Blo 972592 2636965 := bbase (se 4 (by rfl) ⟨247215, by rfl⟩ : syracuseStep 2636965 = 494431) (by norm_num)
theorem B1096897 : Blo 972592 1096897 := bbase (se 2 (by rfl) ⟨411336, by rfl⟩ : syracuseStep 1096897 = 822673) (by norm_num)
theorem B1850597 : Blo 972592 1850597 := bbase (se 4 (by rfl) ⟨173493, by rfl⟩ : syracuseStep 1850597 = 346987) (by norm_num)
theorem B1096933 : Blo 972592 1096933 := bbase (se 4 (by rfl) ⟨102837, by rfl⟩ : syracuseStep 1096933 = 205675) (by norm_num)
theorem B1096969 : Blo 972592 1096969 := bbase (se 2 (by rfl) ⟨411363, by rfl⟩ : syracuseStep 1096969 = 822727) (by norm_num)
theorem B1097005 : Blo 972592 1097005 := bbase (se 3 (by rfl) ⟨205688, by rfl⟩ : syracuseStep 1097005 = 411377) (by norm_num)
theorem B1097041 : Blo 972592 1097041 := bbase (se 2 (by rfl) ⟨411390, by rfl⟩ : syracuseStep 1097041 = 822781) (by norm_num)
theorem B1097077 : Blo 972592 1097077 := bbase (se 5 (by rfl) ⟨51425, by rfl⟩ : syracuseStep 1097077 = 102851) (by norm_num)
theorem B1097113 : Blo 972592 1097113 := bbase (se 2 (by rfl) ⟨411417, by rfl⟩ : syracuseStep 1097113 = 822835) (by norm_num)
theorem B1097149 : Blo 972592 1097149 := bbase (se 3 (by rfl) ⟨205715, by rfl⟩ : syracuseStep 1097149 = 411431) (by norm_num)
theorem B1097185 : Blo 972592 1097185 := bbase (se 2 (by rfl) ⟨411444, by rfl⟩ : syracuseStep 1097185 = 822889) (by norm_num)
theorem B1097221 : Blo 972592 1097221 := bbase (se 4 (by rfl) ⟨102864, by rfl⟩ : syracuseStep 1097221 = 205729) (by norm_num)
theorem B1097257 : Blo 972592 1097257 := bbase (se 2 (by rfl) ⟨411471, by rfl⟩ : syracuseStep 1097257 = 822943) (by norm_num)
theorem B2080333 : Blo 972592 2080333 := bbase (se 3 (by rfl) ⟨390062, by rfl⟩ : syracuseStep 2080333 = 780125) (by norm_num)
theorem B1097293 : Blo 972592 1097293 := bbase (se 3 (by rfl) ⟨205742, by rfl⟩ : syracuseStep 1097293 = 411485) (by norm_num)
theorem B3292757 : Blo 972592 3292757 := bbase (se 8 (by rfl) ⟨19293, by rfl⟩ : syracuseStep 3292757 = 38587) (by norm_num)
theorem B1097329 : Blo 972592 1097329 := bbase (se 2 (by rfl) ⟨411498, by rfl⟩ : syracuseStep 1097329 = 822997) (by norm_num)
theorem B1097365 : Blo 972592 1097365 := bbase (se 6 (by rfl) ⟨25719, by rfl⟩ : syracuseStep 1097365 = 51439) (by norm_num)
theorem B1097401 : Blo 972592 1097401 := bbase (se 2 (by rfl) ⟨411525, by rfl⟩ : syracuseStep 1097401 = 823051) (by norm_num)
theorem B1097437 : Blo 972592 1097437 := bbase (se 3 (by rfl) ⟨205769, by rfl⟩ : syracuseStep 1097437 = 411539) (by norm_num)
theorem B1097473 : Blo 972592 1097473 := bbase (se 2 (by rfl) ⟨411552, by rfl⟩ : syracuseStep 1097473 = 823105) (by norm_num)
theorem B1097509 : Blo 972592 1097509 := bbase (se 4 (by rfl) ⟨102891, by rfl⟩ : syracuseStep 1097509 = 205783) (by norm_num)
theorem B1097545 : Blo 972592 1097545 := bbase (se 2 (by rfl) ⟨411579, by rfl⟩ : syracuseStep 1097545 = 823159) (by norm_num)
theorem B1097581 : Blo 972592 1097581 := bbase (se 3 (by rfl) ⟨205796, by rfl⟩ : syracuseStep 1097581 = 411593) (by norm_num)
theorem B1097617 : Blo 972592 1097617 := bbase (se 2 (by rfl) ⟨411606, by rfl⟩ : syracuseStep 1097617 = 823213) (by norm_num)
theorem B1097653 : Blo 972592 1097653 := bbase (se 5 (by rfl) ⟨51452, by rfl⟩ : syracuseStep 1097653 = 102905) (by norm_num)
theorem B1851349 : Blo 972592 1851349 := bbase (se 7 (by rfl) ⟨21695, by rfl⟩ : syracuseStep 1851349 = 43391) (by norm_num)
theorem B1097689 : Blo 972592 1097689 := bbase (se 2 (by rfl) ⟨411633, by rfl⟩ : syracuseStep 1097689 = 823267) (by norm_num)
theorem B1753069 : Blo 972592 1753069 := bbase (se 3 (by rfl) ⟨328700, by rfl⟩ : syracuseStep 1753069 = 657401) (by norm_num)
theorem B1097725 : Blo 972592 1097725 := bbase (se 3 (by rfl) ⟨205823, by rfl⟩ : syracuseStep 1097725 = 411647) (by norm_num)
theorem B3293189 : Blo 972592 3293189 := bbase (se 4 (by rfl) ⟨308736, by rfl⟩ : syracuseStep 3293189 = 617473) (by norm_num)
theorem B1097761 : Blo 972592 1097761 := bbase (se 2 (by rfl) ⟨411660, by rfl⟩ : syracuseStep 1097761 = 823321) (by norm_num)
theorem B2080829 : Blo 972592 2080829 := bbase (se 3 (by rfl) ⟨390155, by rfl⟩ : syracuseStep 2080829 = 780311) (by norm_num)
theorem B1097797 : Blo 972592 1097797 := bbase (se 4 (by rfl) ⟨102918, by rfl⟩ : syracuseStep 1097797 = 205837) (by norm_num)
theorem B2408525 : Blo 972592 2408525 := bbase (se 3 (by rfl) ⟨451598, by rfl⟩ : syracuseStep 2408525 = 903197) (by norm_num)
theorem B1851493 : Blo 972592 1851493 := bbase (se 4 (by rfl) ⟨173577, by rfl⟩ : syracuseStep 1851493 = 347155) (by norm_num)
theorem B1097833 : Blo 972592 1097833 := bbase (se 2 (by rfl) ⟨411687, by rfl⟩ : syracuseStep 1097833 = 823375) (by norm_num)
theorem B1097869 : Blo 972592 1097869 := bbase (se 3 (by rfl) ⟨205850, by rfl⟩ : syracuseStep 1097869 = 411701) (by norm_num)
theorem B1097905 : Blo 972592 1097905 := bbase (se 2 (by rfl) ⟨411714, by rfl⟩ : syracuseStep 1097905 = 823429) (by norm_num)
theorem B4931765 : Blo 972592 4931765 := bbase (se 5 (by rfl) ⟨231176, by rfl⟩ : syracuseStep 4931765 = 462353) (by norm_num)
theorem B1097941 : Blo 972592 1097941 := bbase (se 7 (by rfl) ⟨12866, by rfl⟩ : syracuseStep 1097941 = 25733) (by norm_num)
theorem B1097977 : Blo 972592 1097977 := bbase (se 2 (by rfl) ⟨411741, by rfl⟩ : syracuseStep 1097977 = 823483) (by norm_num)
theorem B1851653 : Blo 972592 1851653 := bbase (se 4 (by rfl) ⟨173592, by rfl⟩ : syracuseStep 1851653 = 347185) (by norm_num)
theorem B1098013 : Blo 972592 1098013 := bbase (se 3 (by rfl) ⟨205877, by rfl⟩ : syracuseStep 1098013 = 411755) (by norm_num)
theorem B1098049 : Blo 972592 1098049 := bbase (se 2 (by rfl) ⟨411768, by rfl⟩ : syracuseStep 1098049 = 823537) (by norm_num)
theorem B2343269 : Blo 972592 2343269 := bbase (se 4 (by rfl) ⟨219681, by rfl⟩ : syracuseStep 2343269 = 439363) (by norm_num)
theorem B1098085 : Blo 972592 1098085 := bbase (se 4 (by rfl) ⟨102945, by rfl⟩ : syracuseStep 1098085 = 205891) (by norm_num)
theorem B2343277 : Blo 972592 2343277 := bbase (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) (by norm_num)
theorem B1098121 : Blo 972592 1098121 := bbase (se 2 (by rfl) ⟨411795, by rfl⟩ : syracuseStep 1098121 = 823591) (by norm_num)
theorem B1851797 : Blo 972592 1851797 := bbase (se 6 (by rfl) ⟨43401, by rfl⟩ : syracuseStep 1851797 = 86803) (by norm_num)
theorem B1130917 : Blo 972592 1130917 := bbase (se 4 (by rfl) ⟨106023, by rfl⟩ : syracuseStep 1130917 = 212047) (by norm_num)
theorem B1098157 : Blo 972592 1098157 := bbase (se 3 (by rfl) ⟨205904, by rfl⟩ : syracuseStep 1098157 = 411809) (by norm_num)
theorem B3293621 : Blo 972592 3293621 := bbase (se 5 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 3293621 = 308777) (by norm_num)
theorem B1098193 : Blo 972592 1098193 := bbase (se 2 (by rfl) ⟨411822, by rfl⟩ : syracuseStep 1098193 = 823645) (by norm_num)
theorem B1098229 : Blo 972592 1098229 := bbase (se 5 (by rfl) ⟨51479, by rfl⟩ : syracuseStep 1098229 = 102959) (by norm_num)
theorem B1098265 : Blo 972592 1098265 := bbase (se 2 (by rfl) ⟨411849, by rfl⟩ : syracuseStep 1098265 = 823699) (by norm_num)
theorem B1098301 : Blo 972592 1098301 := bbase (se 3 (by rfl) ⟨205931, by rfl⟩ : syracuseStep 1098301 = 411863) (by norm_num)
theorem B1098337 : Blo 972592 1098337 := bbase (se 2 (by rfl) ⟨411876, by rfl⟩ : syracuseStep 1098337 = 823753) (by norm_num)
theorem B2966149 : Blo 972592 2966149 := bbase (se 4 (by rfl) ⟨278076, by rfl⟩ : syracuseStep 2966149 = 556153) (by norm_num)
theorem B1098373 : Blo 972592 1098373 := bbase (se 4 (by rfl) ⟨102972, by rfl⟩ : syracuseStep 1098373 = 205945) (by norm_num)
theorem B1098409 : Blo 972592 1098409 := bbase (se 2 (by rfl) ⟨411903, by rfl⟩ : syracuseStep 1098409 = 823807) (by norm_num)
theorem B4440757 : Blo 972592 4440757 := bbase (se 5 (by rfl) ⟨208160, by rfl⟩ : syracuseStep 4440757 = 416321) (by norm_num)
theorem B1852085 : Blo 972592 1852085 := bbase (se 5 (by rfl) ⟨86816, by rfl⟩ : syracuseStep 1852085 = 173633) (by norm_num)
theorem B1458893 : Blo 972592 1458893 := bbase (se 3 (by rfl) ⟨273542, by rfl⟩ : syracuseStep 1458893 = 547085) (by norm_num)
theorem B1098445 : Blo 972592 1098445 := bbase (se 3 (by rfl) ⟨205958, by rfl⟩ : syracuseStep 1098445 = 411917) (by norm_num)
theorem B1458917 : Blo 972592 1458917 := bbase (se 4 (by rfl) ⟨136773, by rfl⟩ : syracuseStep 1458917 = 273547) (by norm_num)
theorem B1098481 : Blo 972592 1098481 := bbase (se 2 (by rfl) ⟨411930, by rfl⟩ : syracuseStep 1098481 = 823861) (by norm_num)
theorem B2769653 : Blo 972592 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B1458941 : Blo 972592 1458941 := bbase (se 3 (by rfl) ⟨273551, by rfl⟩ : syracuseStep 1458941 = 547103) (by norm_num)
theorem B1458965 : Blo 972592 1458965 := bbase (se 6 (by rfl) ⟨34194, by rfl⟩ : syracuseStep 1458965 = 68389) (by norm_num)
theorem B1098517 : Blo 972592 1098517 := bbase (se 6 (by rfl) ⟨25746, by rfl⟩ : syracuseStep 1098517 = 51493) (by norm_num)
theorem B1458989 : Blo 972592 1458989 := bbase (se 3 (by rfl) ⟨273560, by rfl⟩ : syracuseStep 1458989 = 547121) (by norm_num)
theorem B1098553 : Blo 972592 1098553 := bbase (se 2 (by rfl) ⟨411957, by rfl⟩ : syracuseStep 1098553 = 823915) (by norm_num)
theorem B1459013 : Blo 972592 1459013 := bbase (se 4 (by rfl) ⟨136782, by rfl⟩ : syracuseStep 1459013 = 273565) (by norm_num)
theorem B1852237 : Blo 972592 1852237 := bbase (se 3 (by rfl) ⟨347294, by rfl⟩ : syracuseStep 1852237 = 694589) (by norm_num)
theorem B1459037 : Blo 972592 1459037 := bbase (se 3 (by rfl) ⟨273569, by rfl⟩ : syracuseStep 1459037 = 547139) (by norm_num)
theorem B1098589 : Blo 972592 1098589 := bbase (se 3 (by rfl) ⟨205985, by rfl⟩ : syracuseStep 1098589 = 411971) (by norm_num)
theorem B3294053 : Blo 972592 3294053 := bbase (se 4 (by rfl) ⟨308817, by rfl⟩ : syracuseStep 3294053 = 617635) (by norm_num)
theorem B1459061 : Blo 972592 1459061 := bbase (se 5 (by rfl) ⟨68393, by rfl⟩ : syracuseStep 1459061 = 136787) (by norm_num)
theorem B1098625 : Blo 972592 1098625 := bbase (se 2 (by rfl) ⟨411984, by rfl⟩ : syracuseStep 1098625 = 823969) (by norm_num)
theorem B1459085 : Blo 972592 1459085 := bbase (se 3 (by rfl) ⟨273578, by rfl⟩ : syracuseStep 1459085 = 547157) (by norm_num)
theorem B1459109 : Blo 972592 1459109 := bbase (se 4 (by rfl) ⟨136791, by rfl⟩ : syracuseStep 1459109 = 273583) (by norm_num)
theorem B1098661 : Blo 972592 1098661 := bbase (se 4 (by rfl) ⟨102999, by rfl⟩ : syracuseStep 1098661 = 205999) (by norm_num)
theorem B2081717 : Blo 972592 2081717 := bbase (se 5 (by rfl) ⟨97580, by rfl⟩ : syracuseStep 2081717 = 195161) (by norm_num)
theorem B1459133 : Blo 972592 1459133 := bbase (se 3 (by rfl) ⟨273587, by rfl⟩ : syracuseStep 1459133 = 547175) (by norm_num)
theorem B1459157 : Blo 972592 1459157 := bbase (se 7 (by rfl) ⟨17099, by rfl⟩ : syracuseStep 1459157 = 34199) (by norm_num)
theorem B1459181 : Blo 972592 1459181 := bbase (se 3 (by rfl) ⟨273596, by rfl⟩ : syracuseStep 1459181 = 547193) (by norm_num)
theorem B1459205 : Blo 972592 1459205 := bbase (se 4 (by rfl) ⟨136800, by rfl⟩ : syracuseStep 1459205 = 273601) (by norm_num)
theorem B1459229 : Blo 972592 1459229 := bbase (se 3 (by rfl) ⟨273605, by rfl⟩ : syracuseStep 1459229 = 547211) (by norm_num)
theorem B2081837 : Blo 972592 2081837 := bbase (se 3 (by rfl) ⟨390344, by rfl⟩ : syracuseStep 2081837 = 780689) (by norm_num)
theorem B1459253 : Blo 972592 1459253 := bbase (se 5 (by rfl) ⟨68402, by rfl⟩ : syracuseStep 1459253 = 136805) (by norm_num)
theorem B1459277 : Blo 972592 1459277 := bbase (se 3 (by rfl) ⟨273614, by rfl⟩ : syracuseStep 1459277 = 547229) (by norm_num)
theorem B1459301 : Blo 972592 1459301 := bbase (se 4 (by rfl) ⟨136809, by rfl⟩ : syracuseStep 1459301 = 273619) (by norm_num)
theorem B1459325 : Blo 972592 1459325 := bbase (se 3 (by rfl) ⟨273623, by rfl⟩ : syracuseStep 1459325 = 547247) (by norm_num)
theorem B1852541 : Blo 972592 1852541 := bbase (se 3 (by rfl) ⟨347351, by rfl⟩ : syracuseStep 1852541 = 694703) (by norm_num)
theorem B1459349 : Blo 972592 1459349 := bbase (se 6 (by rfl) ⟨34203, by rfl⟩ : syracuseStep 1459349 = 68407) (by norm_num)
theorem B1459373 : Blo 972592 1459373 := bbase (se 3 (by rfl) ⟨273632, by rfl⟩ : syracuseStep 1459373 = 547265) (by norm_num)
theorem B1459397 : Blo 972592 1459397 := bbase (se 4 (by rfl) ⟨136818, by rfl⟩ : syracuseStep 1459397 = 273637) (by norm_num)
theorem B1459421 : Blo 972592 1459421 := bbase (se 3 (by rfl) ⟨273641, by rfl⟩ : syracuseStep 1459421 = 547283) (by norm_num)
theorem B1459445 : Blo 972592 1459445 := bbase (se 5 (by rfl) ⟨68411, by rfl⟩ : syracuseStep 1459445 = 136823) (by norm_num)
theorem B1459469 : Blo 972592 1459469 := bbase (se 3 (by rfl) ⟨273650, by rfl⟩ : syracuseStep 1459469 = 547301) (by norm_num)
theorem B3294485 : Blo 972592 3294485 := bbase (se 6 (by rfl) ⟨77214, by rfl⟩ : syracuseStep 3294485 = 154429) (by norm_num)
theorem B1459493 : Blo 972592 1459493 := bbase (se 4 (by rfl) ⟨136827, by rfl⟩ : syracuseStep 1459493 = 273655) (by norm_num)
theorem B1459517 : Blo 972592 1459517 := bbase (se 3 (by rfl) ⟨273659, by rfl⟩ : syracuseStep 1459517 = 547319) (by norm_num)
theorem B1459541 : Blo 972592 1459541 := bbase (se 12 (by rfl) ⟨534, by rfl⟩ : syracuseStep 1459541 = 1069) (by norm_num)
theorem B2344277 : Blo 972592 2344277 := bbase (se 12 (by rfl) ⟨858, by rfl⟩ : syracuseStep 2344277 = 1717) (by norm_num)
theorem B1459565 : Blo 972592 1459565 := bbase (se 3 (by rfl) ⟨273668, by rfl⟩ : syracuseStep 1459565 = 547337) (by norm_num)
theorem B5555573 : Blo 972592 5555573 := bbase (se 5 (by rfl) ⟨260417, by rfl⟩ : syracuseStep 5555573 = 520835) (by norm_num)
theorem B1459589 : Blo 972592 1459589 := bbase (se 4 (by rfl) ⟨136836, by rfl⟩ : syracuseStep 1459589 = 273673) (by norm_num)
theorem B1459613 : Blo 972592 1459613 := bbase (se 3 (by rfl) ⟨273677, by rfl⟩ : syracuseStep 1459613 = 547355) (by norm_num)
theorem B1459637 : Blo 972592 1459637 := bbase (se 5 (by rfl) ⟨68420, by rfl⟩ : syracuseStep 1459637 = 136841) (by norm_num)
theorem B4933061 : Blo 972592 4933061 := bbase (se 4 (by rfl) ⟨462474, by rfl⟩ : syracuseStep 4933061 = 924949) (by norm_num)
theorem B1459661 : Blo 972592 1459661 := bbase (se 3 (by rfl) ⟨273686, by rfl⟩ : syracuseStep 1459661 = 547373) (by norm_num)
theorem B8898005 : Blo 972592 8898005 := bbase (se 7 (by rfl) ⟨104273, by rfl⟩ : syracuseStep 8898005 = 208547) (by norm_num)
theorem B1459685 : Blo 972592 1459685 := bbase (se 4 (by rfl) ⟨136845, by rfl⟩ : syracuseStep 1459685 = 273691) (by norm_num)
theorem B1459709 : Blo 972592 1459709 := bbase (se 3 (by rfl) ⟨273695, by rfl⟩ : syracuseStep 1459709 = 547391) (by norm_num)
theorem B1459733 : Blo 972592 1459733 := bbase (se 6 (by rfl) ⟨34212, by rfl⟩ : syracuseStep 1459733 = 68425) (by norm_num)
theorem B3950117 : Blo 972592 3950117 := bbase (se 4 (by rfl) ⟨370323, by rfl⟩ : syracuseStep 3950117 = 740647) (by norm_num)
theorem B1459757 : Blo 972592 1459757 := bbase (se 3 (by rfl) ⟨273704, by rfl⟩ : syracuseStep 1459757 = 547409) (by norm_num)
theorem B5064245 : Blo 972592 5064245 := bbase (se 5 (by rfl) ⟨237386, by rfl⟩ : syracuseStep 5064245 = 474773) (by norm_num)
theorem B1459781 : Blo 972592 1459781 := bbase (se 4 (by rfl) ⟨136854, by rfl⟩ : syracuseStep 1459781 = 273709) (by norm_num)
theorem B1459805 : Blo 972592 1459805 := bbase (se 3 (by rfl) ⟨273713, by rfl⟩ : syracuseStep 1459805 = 547427) (by norm_num)
theorem B1459829 : Blo 972592 1459829 := bbase (se 5 (by rfl) ⟨68429, by rfl⟩ : syracuseStep 1459829 = 136859) (by norm_num)
theorem B1459853 : Blo 972592 1459853 := bbase (se 3 (by rfl) ⟨273722, by rfl⟩ : syracuseStep 1459853 = 547445) (by norm_num)
theorem B1459877 : Blo 972592 1459877 := bbase (se 4 (by rfl) ⟨136863, by rfl⟩ : syracuseStep 1459877 = 273727) (by norm_num)
theorem B2082469 : Blo 972592 2082469 := bbase (se 4 (by rfl) ⟨195231, by rfl⟩ : syracuseStep 2082469 = 390463) (by norm_num)
theorem B1459901 : Blo 972592 1459901 := bbase (se 3 (by rfl) ⟨273731, by rfl⟩ : syracuseStep 1459901 = 547463) (by norm_num)
theorem B3294917 : Blo 972592 3294917 := bbase (se 4 (by rfl) ⟨308898, by rfl⟩ : syracuseStep 3294917 = 617797) (by norm_num)
theorem B2770645 : Blo 972592 2770645 := bbase (se 7 (by rfl) ⟨32468, by rfl⟩ : syracuseStep 2770645 = 64937) (by norm_num)
theorem B1459925 : Blo 972592 1459925 := bbase (se 7 (by rfl) ⟨17108, by rfl⟩ : syracuseStep 1459925 = 34217) (by norm_num)
theorem B1459949 : Blo 972592 1459949 := bbase (se 3 (by rfl) ⟨273740, by rfl⟩ : syracuseStep 1459949 = 547481) (by norm_num)
theorem B1459973 : Blo 972592 1459973 := bbase (se 4 (by rfl) ⟨136872, by rfl⟩ : syracuseStep 1459973 = 273745) (by norm_num)
theorem B1459997 : Blo 972592 1459997 := bbase (se 3 (by rfl) ⟨273749, by rfl⟩ : syracuseStep 1459997 = 547499) (by norm_num)
theorem B1460021 : Blo 972592 1460021 := bbase (se 5 (by rfl) ⟨68438, by rfl⟩ : syracuseStep 1460021 = 136877) (by norm_num)
theorem B1001269 : Blo 972592 1001269 := bbase (se 5 (by rfl) ⟨46934, by rfl⟩ : syracuseStep 1001269 = 93869) (by norm_num)
theorem B1460045 : Blo 972592 1460045 := bbase (se 3 (by rfl) ⟨273758, by rfl⟩ : syracuseStep 1460045 = 547517) (by norm_num)
theorem B1460069 : Blo 972592 1460069 := bbase (se 4 (by rfl) ⟨136881, by rfl⟩ : syracuseStep 1460069 = 273763) (by norm_num)
theorem B1853293 : Blo 972592 1853293 := bbase (se 3 (by rfl) ⟨347492, by rfl⟩ : syracuseStep 1853293 = 694985) (by norm_num)
theorem B1460093 : Blo 972592 1460093 := bbase (se 3 (by rfl) ⟨273767, by rfl⟩ : syracuseStep 1460093 = 547535) (by norm_num)
theorem B1460117 : Blo 972592 1460117 := bbase (se 6 (by rfl) ⟨34221, by rfl⟩ : syracuseStep 1460117 = 68443) (by norm_num)
theorem B1460141 : Blo 972592 1460141 := bbase (se 3 (by rfl) ⟨273776, by rfl⟩ : syracuseStep 1460141 = 547553) (by norm_num)
theorem B1460165 : Blo 972592 1460165 := bbase (se 4 (by rfl) ⟨136890, by rfl⟩ : syracuseStep 1460165 = 273781) (by norm_num)
theorem B1460189 : Blo 972592 1460189 := bbase (se 3 (by rfl) ⟨273785, by rfl⟩ : syracuseStep 1460189 = 547571) (by norm_num)
theorem B1460213 : Blo 972592 1460213 := bbase (se 5 (by rfl) ⟨68447, by rfl⟩ : syracuseStep 1460213 = 136895) (by norm_num)
theorem B1853437 : Blo 972592 1853437 := bbase (se 3 (by rfl) ⟨347519, by rfl⟩ : syracuseStep 1853437 = 695039) (by norm_num)
theorem B1460237 : Blo 972592 1460237 := bbase (se 3 (by rfl) ⟨273794, by rfl⟩ : syracuseStep 1460237 = 547589) (by norm_num)
theorem B1460261 : Blo 972592 1460261 := bbase (se 4 (by rfl) ⟨136899, by rfl⟩ : syracuseStep 1460261 = 273799) (by norm_num)
theorem B1460285 : Blo 972592 1460285 := bbase (se 3 (by rfl) ⟨273803, by rfl⟩ : syracuseStep 1460285 = 547607) (by norm_num)
theorem B1558597 : Blo 972592 1558597 := bbase (se 4 (by rfl) ⟨146118, by rfl⟩ : syracuseStep 1558597 = 292237) (by norm_num)
theorem B1460309 : Blo 972592 1460309 := bbase (se 8 (by rfl) ⟨8556, by rfl⟩ : syracuseStep 1460309 = 17113) (by norm_num)
theorem B2345045 : Blo 972592 2345045 := bbase (se 8 (by rfl) ⟨13740, by rfl⟩ : syracuseStep 2345045 = 27481) (by norm_num)
theorem B1460333 : Blo 972592 1460333 := bbase (se 3 (by rfl) ⟨273812, by rfl⟩ : syracuseStep 1460333 = 547625) (by norm_num)
theorem B3295349 : Blo 972592 3295349 := bbase (se 5 (by rfl) ⟨154469, by rfl⟩ : syracuseStep 3295349 = 308939) (by norm_num)
theorem B1230977 : Blo 972592 1230977 := bbase (se 2 (by rfl) ⟨461616, by rfl⟩ : syracuseStep 1230977 = 923233) (by norm_num)
theorem B1460357 : Blo 972592 1460357 := bbase (se 4 (by rfl) ⟨136908, by rfl⟩ : syracuseStep 1460357 = 273817) (by norm_num)
theorem B1460381 : Blo 972592 1460381 := bbase (se 3 (by rfl) ⟨273821, by rfl⟩ : syracuseStep 1460381 = 547643) (by norm_num)
theorem B1853597 : Blo 972592 1853597 := bbase (se 3 (by rfl) ⟨347549, by rfl⟩ : syracuseStep 1853597 = 695099) (by norm_num)
theorem B1558693 : Blo 972592 1558693 := bbase (se 4 (by rfl) ⟨146127, by rfl⟩ : syracuseStep 1558693 = 292255) (by norm_num)
theorem B1460405 : Blo 972592 1460405 := bbase (se 5 (by rfl) ⟨68456, by rfl⟩ : syracuseStep 1460405 = 136913) (by norm_num)
theorem B1231033 : Blo 972592 1231033 := bbase (se 2 (by rfl) ⟨461637, by rfl⟩ : syracuseStep 1231033 = 923275) (by norm_num)
theorem B1460429 : Blo 972592 1460429 := bbase (se 3 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 1460429 = 547661) (by norm_num)
theorem B1460453 : Blo 972592 1460453 := bbase (se 4 (by rfl) ⟨136917, by rfl⟩ : syracuseStep 1460453 = 273835) (by norm_num)
theorem B1460477 : Blo 972592 1460477 := bbase (se 3 (by rfl) ⟨273839, by rfl⟩ : syracuseStep 1460477 = 547679) (by norm_num)
theorem B1460501 : Blo 972592 1460501 := bbase (se 6 (by rfl) ⟨34230, by rfl⟩ : syracuseStep 1460501 = 68461) (by norm_num)
theorem B1231129 : Blo 972592 1231129 := bbase (se 2 (by rfl) ⟨461673, by rfl⟩ : syracuseStep 1231129 = 923347) (by norm_num)
theorem B1460525 : Blo 972592 1460525 := bbase (se 3 (by rfl) ⟨273848, by rfl⟩ : syracuseStep 1460525 = 547697) (by norm_num)
theorem B1853741 : Blo 972592 1853741 := bbase (se 3 (by rfl) ⟨347576, by rfl⟩ : syracuseStep 1853741 = 695153) (by norm_num)
theorem B1558853 : Blo 972592 1558853 := bbase (se 4 (by rfl) ⟨146142, by rfl⟩ : syracuseStep 1558853 = 292285) (by norm_num)
theorem B1460549 : Blo 972592 1460549 := bbase (se 4 (by rfl) ⟨136926, by rfl⟩ : syracuseStep 1460549 = 273853) (by norm_num)
theorem B7391573 : Blo 972592 7391573 := bbase (se 10 (by rfl) ⟨10827, by rfl⟩ : syracuseStep 7391573 = 21655) (by norm_num)
theorem B1460573 : Blo 972592 1460573 := bbase (se 3 (by rfl) ⟨273857, by rfl⟩ : syracuseStep 1460573 = 547715) (by norm_num)
theorem B1460597 : Blo 972592 1460597 := bbase (se 5 (by rfl) ⟨68465, by rfl⟩ : syracuseStep 1460597 = 136931) (by norm_num)
theorem B1460621 : Blo 972592 1460621 := bbase (se 3 (by rfl) ⟨273866, by rfl⟩ : syracuseStep 1460621 = 547733) (by norm_num)
theorem B1460645 : Blo 972592 1460645 := bbase (se 4 (by rfl) ⟨136935, by rfl⟩ : syracuseStep 1460645 = 273871) (by norm_num)
theorem B1460669 : Blo 972592 1460669 := bbase (se 3 (by rfl) ⟨273875, by rfl⟩ : syracuseStep 1460669 = 547751) (by norm_num)
theorem B1231301 : Blo 972592 1231301 := bbase (se 4 (by rfl) ⟨115434, by rfl⟩ : syracuseStep 1231301 = 230869) (by norm_num)
theorem B1460693 : Blo 972592 1460693 := bbase (se 7 (by rfl) ⟨17117, by rfl⟩ : syracuseStep 1460693 = 34235) (by norm_num)
theorem B1460717 : Blo 972592 1460717 := bbase (se 3 (by rfl) ⟨273884, by rfl⟩ : syracuseStep 1460717 = 547769) (by norm_num)
theorem B1231357 : Blo 972592 1231357 := bbase (se 3 (by rfl) ⟨230879, by rfl⟩ : syracuseStep 1231357 = 461759) (by norm_num)
theorem B1460741 : Blo 972592 1460741 := bbase (se 4 (by rfl) ⟨136944, by rfl⟩ : syracuseStep 1460741 = 273889) (by norm_num)
theorem B1460765 : Blo 972592 1460765 := bbase (se 3 (by rfl) ⟨273893, by rfl⟩ : syracuseStep 1460765 = 547787) (by norm_num)
theorem B2083357 : Blo 972592 2083357 := bbase (se 3 (by rfl) ⟨390629, by rfl⟩ : syracuseStep 2083357 = 781259) (by norm_num)
theorem B3295781 : Blo 972592 3295781 := bbase (se 4 (by rfl) ⟨308979, by rfl⟩ : syracuseStep 3295781 = 617959) (by norm_num)
theorem B1460789 : Blo 972592 1460789 := bbase (se 5 (by rfl) ⟨68474, by rfl⟩ : syracuseStep 1460789 = 136949) (by norm_num)
theorem B1460813 : Blo 972592 1460813 := bbase (se 3 (by rfl) ⟨273902, by rfl⟩ : syracuseStep 1460813 = 547805) (by norm_num)
theorem B1231453 : Blo 972592 1231453 := bbase (se 3 (by rfl) ⟨230897, by rfl⟩ : syracuseStep 1231453 = 461795) (by norm_num)
theorem B1460837 : Blo 972592 1460837 := bbase (se 4 (by rfl) ⟨136953, by rfl⟩ : syracuseStep 1460837 = 273907) (by norm_num)
theorem B1755757 : Blo 972592 1755757 := bbase (se 3 (by rfl) ⟨329204, by rfl⟩ : syracuseStep 1755757 = 658409) (by norm_num)
theorem B1460861 : Blo 972592 1460861 := bbase (se 3 (by rfl) ⟨273911, by rfl⟩ : syracuseStep 1460861 = 547823) (by norm_num)
theorem B1460885 : Blo 972592 1460885 := bbase (se 6 (by rfl) ⟨34239, by rfl⟩ : syracuseStep 1460885 = 68479) (by norm_num)
theorem B2083477 : Blo 972592 2083477 := bbase (se 6 (by rfl) ⟨48831, by rfl⟩ : syracuseStep 2083477 = 97663) (by norm_num)
theorem B1460909 : Blo 972592 1460909 := bbase (se 3 (by rfl) ⟨273920, by rfl⟩ : syracuseStep 1460909 = 547841) (by norm_num)
theorem B1460933 : Blo 972592 1460933 := bbase (se 4 (by rfl) ⟨136962, by rfl⟩ : syracuseStep 1460933 = 273925) (by norm_num)
theorem B9358037 : Blo 972592 9358037 := bbase (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) (by norm_num)
theorem B4934357 : Blo 972592 4934357 := bbase (se 7 (by rfl) ⟨57824, by rfl⟩ : syracuseStep 4934357 = 115649) (by norm_num)
theorem B1460957 : Blo 972592 1460957 := bbase (se 3 (by rfl) ⟨273929, by rfl⟩ : syracuseStep 1460957 = 547859) (by norm_num)
theorem B1460981 : Blo 972592 1460981 := bbase (se 5 (by rfl) ⟨68483, by rfl⟩ : syracuseStep 1460981 = 136967) (by norm_num)
theorem B1231625 : Blo 972592 1231625 := bbase (se 2 (by rfl) ⟨461859, by rfl⟩ : syracuseStep 1231625 = 923719) (by norm_num)
theorem B1461005 : Blo 972592 1461005 := bbase (se 3 (by rfl) ⟨273938, by rfl⟩ : syracuseStep 1461005 = 547877) (by norm_num)
theorem B2771749 : Blo 972592 2771749 := bbase (se 4 (by rfl) ⟨259851, by rfl⟩ : syracuseStep 2771749 = 519703) (by norm_num)
theorem B1461029 : Blo 972592 1461029 := bbase (se 4 (by rfl) ⟨136971, by rfl⟩ : syracuseStep 1461029 = 273943) (by norm_num)
theorem B1461053 : Blo 972592 1461053 := bbase (se 3 (by rfl) ⟨273947, by rfl⟩ : syracuseStep 1461053 = 547895) (by norm_num)
theorem B1231681 : Blo 972592 1231681 := bbase (se 2 (by rfl) ⟨461880, by rfl⟩ : syracuseStep 1231681 = 923761) (by norm_num)
theorem B1461077 : Blo 972592 1461077 := bbase (se 9 (by rfl) ⟨4280, by rfl⟩ : syracuseStep 1461077 = 8561) (by norm_num)
theorem B1461101 : Blo 972592 1461101 := bbase (se 3 (by rfl) ⟨273956, by rfl⟩ : syracuseStep 1461101 = 547913) (by norm_num)
theorem B1461125 : Blo 972592 1461125 := bbase (se 4 (by rfl) ⟨136980, by rfl⟩ : syracuseStep 1461125 = 273961) (by norm_num)
theorem B2083733 : Blo 972592 2083733 := bbase (se 6 (by rfl) ⟨48837, by rfl⟩ : syracuseStep 2083733 = 97675) (by norm_num)
theorem B1461149 : Blo 972592 1461149 := bbase (se 3 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 1461149 = 547931) (by norm_num)
theorem B1231777 : Blo 972592 1231777 := bbase (se 2 (by rfl) ⟨461916, by rfl⟩ : syracuseStep 1231777 = 923833) (by norm_num)
theorem B1461173 : Blo 972592 1461173 := bbase (se 5 (by rfl) ⟨68492, by rfl⟩ : syracuseStep 1461173 = 136985) (by norm_num)
theorem B1461197 : Blo 972592 1461197 := bbase (se 3 (by rfl) ⟨273974, by rfl⟩ : syracuseStep 1461197 = 547949) (by norm_num)
theorem B1002449 : Blo 972592 1002449 := bbase (se 2 (by rfl) ⟨375918, by rfl⟩ : syracuseStep 1002449 = 751837) (by norm_num)
theorem B1461221 : Blo 972592 1461221 := bbase (se 4 (by rfl) ⟨136989, by rfl⟩ : syracuseStep 1461221 = 273979) (by norm_num)
theorem B1461245 : Blo 972592 1461245 := bbase (se 3 (by rfl) ⟨273983, by rfl⟩ : syracuseStep 1461245 = 547967) (by norm_num)
theorem B1461269 : Blo 972592 1461269 := bbase (se 6 (by rfl) ⟨34248, by rfl⟩ : syracuseStep 1461269 = 68497) (by norm_num)
theorem B1461293 : Blo 972592 1461293 := bbase (se 3 (by rfl) ⟨273992, by rfl⟩ : syracuseStep 1461293 = 547985) (by norm_num)
theorem B1461317 : Blo 972592 1461317 := bbase (se 4 (by rfl) ⟨136998, by rfl⟩ : syracuseStep 1461317 = 273997) (by norm_num)
theorem B1231949 : Blo 972592 1231949 := bbase (se 3 (by rfl) ⟨230990, by rfl⟩ : syracuseStep 1231949 = 461981) (by norm_num)
theorem B1461341 : Blo 972592 1461341 := bbase (se 3 (by rfl) ⟨274001, by rfl⟩ : syracuseStep 1461341 = 548003) (by norm_num)
theorem B1461365 : Blo 972592 1461365 := bbase (se 5 (by rfl) ⟨68501, by rfl⟩ : syracuseStep 1461365 = 137003) (by norm_num)
theorem B1232005 : Blo 972592 1232005 := bbase (se 4 (by rfl) ⟨115500, by rfl⟩ : syracuseStep 1232005 = 231001) (by norm_num)
theorem B1461389 : Blo 972592 1461389 := bbase (se 3 (by rfl) ⟨274010, by rfl⟩ : syracuseStep 1461389 = 548021) (by norm_num)
theorem B1461413 : Blo 972592 1461413 := bbase (se 4 (by rfl) ⟨137007, by rfl⟩ : syracuseStep 1461413 = 274015) (by norm_num)
theorem B1461437 : Blo 972592 1461437 := bbase (se 3 (by rfl) ⟨274019, by rfl⟩ : syracuseStep 1461437 = 548039) (by norm_num)
theorem B1461461 : Blo 972592 1461461 := bbase (se 7 (by rfl) ⟨17126, by rfl⟩ : syracuseStep 1461461 = 34253) (by norm_num)
theorem B1232101 : Blo 972592 1232101 := bbase (se 4 (by rfl) ⟨115509, by rfl⟩ : syracuseStep 1232101 = 231019) (by norm_num)
theorem B1461485 : Blo 972592 1461485 := bbase (se 3 (by rfl) ⟨274028, by rfl⟩ : syracuseStep 1461485 = 548057) (by norm_num)
theorem B1461509 : Blo 972592 1461509 := bbase (se 4 (by rfl) ⟨137016, by rfl⟩ : syracuseStep 1461509 = 274033) (by norm_num)
theorem B1461533 : Blo 972592 1461533 := bbase (se 3 (by rfl) ⟨274037, by rfl⟩ : syracuseStep 1461533 = 548075) (by norm_num)
theorem B1461557 : Blo 972592 1461557 := bbase (se 5 (by rfl) ⟨68510, by rfl⟩ : syracuseStep 1461557 = 137021) (by norm_num)
theorem B1461581 : Blo 972592 1461581 := bbase (se 3 (by rfl) ⟨274046, by rfl⟩ : syracuseStep 1461581 = 548093) (by norm_num)
theorem B1461605 : Blo 972592 1461605 := bbase (se 4 (by rfl) ⟨137025, by rfl⟩ : syracuseStep 1461605 = 274051) (by norm_num)
theorem B1461629 : Blo 972592 1461629 := bbase (se 3 (by rfl) ⟨274055, by rfl⟩ : syracuseStep 1461629 = 548111) (by norm_num)
theorem B1232273 : Blo 972592 1232273 := bbase (se 2 (by rfl) ⟨462102, by rfl⟩ : syracuseStep 1232273 = 924205) (by norm_num)
theorem B1461653 : Blo 972592 1461653 := bbase (se 6 (by rfl) ⟨34257, by rfl⟩ : syracuseStep 1461653 = 68515) (by norm_num)
theorem B1559981 : Blo 972592 1559981 := bbase (se 3 (by rfl) ⟨292496, by rfl⟩ : syracuseStep 1559981 = 584993) (by norm_num)
theorem B1461677 : Blo 972592 1461677 := bbase (se 3 (by rfl) ⟨274064, by rfl⟩ : syracuseStep 1461677 = 548129) (by norm_num)
theorem B1461701 : Blo 972592 1461701 := bbase (se 4 (by rfl) ⟨137034, by rfl⟩ : syracuseStep 1461701 = 274069) (by norm_num)
theorem B1232329 : Blo 972592 1232329 := bbase (se 2 (by rfl) ⟨462123, by rfl⟩ : syracuseStep 1232329 = 924247) (by norm_num)
theorem B1461725 : Blo 972592 1461725 := bbase (se 3 (by rfl) ⟨274073, by rfl⟩ : syracuseStep 1461725 = 548147) (by norm_num)
theorem B1461749 : Blo 972592 1461749 := bbase (se 5 (by rfl) ⟨68519, by rfl⟩ : syracuseStep 1461749 = 137039) (by norm_num)
theorem B1461773 : Blo 972592 1461773 := bbase (se 3 (by rfl) ⟨274082, by rfl⟩ : syracuseStep 1461773 = 548165) (by norm_num)
theorem B1461797 : Blo 972592 1461797 := bbase (se 4 (by rfl) ⟨137043, by rfl⟩ : syracuseStep 1461797 = 274087) (by norm_num)
theorem B1232425 : Blo 972592 1232425 := bbase (se 2 (by rfl) ⟨462159, by rfl⟩ : syracuseStep 1232425 = 924319) (by norm_num)
theorem B4574773 : Blo 972592 4574773 := bbase (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) (by norm_num)
theorem B1461821 : Blo 972592 1461821 := bbase (se 3 (by rfl) ⟨274091, by rfl⟩ : syracuseStep 1461821 = 548183) (by norm_num)
theorem B1265233 : Blo 972592 1265233 := bbase (se 2 (by rfl) ⟨474462, by rfl⟩ : syracuseStep 1265233 = 948925) (by norm_num)
theorem B1461845 : Blo 972592 1461845 := bbase (se 8 (by rfl) ⟨8565, by rfl⟩ : syracuseStep 1461845 = 17131) (by norm_num)
theorem B1461869 : Blo 972592 1461869 := bbase (se 3 (by rfl) ⟨274100, by rfl⟩ : syracuseStep 1461869 = 548201) (by norm_num)
theorem B1461893 : Blo 972592 1461893 := bbase (se 4 (by rfl) ⟨137052, by rfl⟩ : syracuseStep 1461893 = 274105) (by norm_num)
theorem B1068701 : Blo 972592 1068701 := bbase (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) (by norm_num)
theorem B1461917 : Blo 972592 1461917 := bbase (se 3 (by rfl) ⟨274109, by rfl⟩ : syracuseStep 1461917 = 548219) (by norm_num)
theorem B1461941 : Blo 972592 1461941 := bbase (se 5 (by rfl) ⟨68528, by rfl⟩ : syracuseStep 1461941 = 137057) (by norm_num)
theorem B1461965 : Blo 972592 1461965 := bbase (se 3 (by rfl) ⟨274118, by rfl⟩ : syracuseStep 1461965 = 548237) (by norm_num)
theorem B1232597 : Blo 972592 1232597 := bbase (se 7 (by rfl) ⟨14444, by rfl⟩ : syracuseStep 1232597 = 28889) (by norm_num)
theorem B1461989 : Blo 972592 1461989 := bbase (se 4 (by rfl) ⟨137061, by rfl⟩ : syracuseStep 1461989 = 274123) (by norm_num)
theorem B4116197 : Blo 972592 4116197 := bbase (se 4 (by rfl) ⟨385893, by rfl⟩ : syracuseStep 4116197 = 771787) (by norm_num)
theorem B1462013 : Blo 972592 1462013 := bbase (se 3 (by rfl) ⟨274127, by rfl⟩ : syracuseStep 1462013 = 548255) (by norm_num)
theorem B1232653 : Blo 972592 1232653 := bbase (se 3 (by rfl) ⟨231122, by rfl⟩ : syracuseStep 1232653 = 462245) (by norm_num)
theorem B2084621 : Blo 972592 2084621 := bbase (se 3 (by rfl) ⟨390866, by rfl⟩ : syracuseStep 2084621 = 781733) (by norm_num)
theorem B1462037 : Blo 972592 1462037 := bbase (se 6 (by rfl) ⟨34266, by rfl⟩ : syracuseStep 1462037 = 68533) (by norm_num)
theorem B1462061 : Blo 972592 1462061 := bbase (se 3 (by rfl) ⟨274136, by rfl⟩ : syracuseStep 1462061 = 548273) (by norm_num)
theorem B1462085 : Blo 972592 1462085 := bbase (se 4 (by rfl) ⟨137070, by rfl⟩ : syracuseStep 1462085 = 274141) (by norm_num)
theorem B1462109 : Blo 972592 1462109 := bbase (se 3 (by rfl) ⟨274145, by rfl⟩ : syracuseStep 1462109 = 548291) (by norm_num)
theorem B1232749 : Blo 972592 1232749 := bbase (se 3 (by rfl) ⟨231140, by rfl⟩ : syracuseStep 1232749 = 462281) (by norm_num)
theorem B1462133 : Blo 972592 1462133 := bbase (se 5 (by rfl) ⟨68537, by rfl⟩ : syracuseStep 1462133 = 137075) (by norm_num)
theorem B1462157 : Blo 972592 1462157 := bbase (se 3 (by rfl) ⟨274154, by rfl⟩ : syracuseStep 1462157 = 548309) (by norm_num)
theorem B1462181 : Blo 972592 1462181 := bbase (se 4 (by rfl) ⟨137079, by rfl⟩ : syracuseStep 1462181 = 274159) (by norm_num)
theorem B1560493 : Blo 972592 1560493 := bbase (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) (by norm_num)
theorem B1462205 : Blo 972592 1462205 := bbase (se 3 (by rfl) ⟨274163, by rfl⟩ : syracuseStep 1462205 = 548327) (by norm_num)
theorem B1462229 : Blo 972592 1462229 := bbase (se 7 (by rfl) ⟨17135, by rfl⟩ : syracuseStep 1462229 = 34271) (by norm_num)
theorem B1757141 : Blo 972592 1757141 := bbase (se 7 (by rfl) ⟨20591, by rfl⟩ : syracuseStep 1757141 = 41183) (by norm_num)
theorem B4935653 : Blo 972592 4935653 := bbase (se 4 (by rfl) ⟨462717, by rfl⟩ : syracuseStep 4935653 = 925435) (by norm_num)
theorem B1462253 : Blo 972592 1462253 := bbase (se 3 (by rfl) ⟨274172, by rfl⟩ : syracuseStep 1462253 = 548345) (by norm_num)
theorem B2084861 : Blo 972592 2084861 := bbase (se 3 (by rfl) ⟨390911, by rfl⟩ : syracuseStep 2084861 = 781823) (by norm_num)
theorem B1462277 : Blo 972592 1462277 := bbase (se 4 (by rfl) ⟨137088, by rfl⟩ : syracuseStep 1462277 = 274177) (by norm_num)
theorem B17813525 : Blo 972592 17813525 := bbase (se 6 (by rfl) ⟨417504, by rfl⟩ : syracuseStep 17813525 = 835009) (by norm_num)
theorem B1232921 : Blo 972592 1232921 := bbase (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) (by norm_num)
theorem B1462301 : Blo 972592 1462301 := bbase (se 3 (by rfl) ⟨274181, by rfl⟩ : syracuseStep 1462301 = 548363) (by norm_num)
theorem B1462325 : Blo 972592 1462325 := bbase (se 5 (by rfl) ⟨68546, by rfl⟩ : syracuseStep 1462325 = 137093) (by norm_num)
theorem B3952709 : Blo 972592 3952709 := bbase (se 4 (by rfl) ⟨370566, by rfl⟩ : syracuseStep 3952709 = 741133) (by norm_num)
theorem B1462349 : Blo 972592 1462349 := bbase (se 3 (by rfl) ⟨274190, by rfl⟩ : syracuseStep 1462349 = 548381) (by norm_num)
theorem B1232977 : Blo 972592 1232977 := bbase (se 2 (by rfl) ⟨462366, by rfl⟩ : syracuseStep 1232977 = 924733) (by norm_num)
theorem B6672469 : Blo 972592 6672469 := bbase (se 8 (by rfl) ⟨39096, by rfl⟩ : syracuseStep 6672469 = 78193) (by norm_num)
theorem B1462373 : Blo 972592 1462373 := bbase (se 4 (by rfl) ⟨137097, by rfl⟩ : syracuseStep 1462373 = 274195) (by norm_num)
theorem B1462397 : Blo 972592 1462397 := bbase (se 3 (by rfl) ⟨274199, by rfl⟩ : syracuseStep 1462397 = 548399) (by norm_num)
theorem B1462421 : Blo 972592 1462421 := bbase (se 6 (by rfl) ⟨34275, by rfl⟩ : syracuseStep 1462421 = 68551) (by norm_num)
theorem B1462445 : Blo 972592 1462445 := bbase (se 3 (by rfl) ⟨274208, by rfl⟩ : syracuseStep 1462445 = 548417) (by norm_num)
theorem B1233073 : Blo 972592 1233073 := bbase (se 2 (by rfl) ⟨462402, by rfl⟩ : syracuseStep 1233073 = 924805) (by norm_num)
theorem B1462469 : Blo 972592 1462469 := bbase (se 4 (by rfl) ⟨137106, by rfl⟩ : syracuseStep 1462469 = 274213) (by norm_num)
theorem B1462493 : Blo 972592 1462493 := bbase (se 3 (by rfl) ⟨274217, by rfl⟩ : syracuseStep 1462493 = 548435) (by norm_num)
theorem B1462517 : Blo 972592 1462517 := bbase (se 5 (by rfl) ⟨68555, by rfl⟩ : syracuseStep 1462517 = 137111) (by norm_num)
theorem B2773253 : Blo 972592 2773253 := bbase (se 4 (by rfl) ⟨259992, by rfl⟩ : syracuseStep 2773253 = 519985) (by norm_num)
theorem B3166469 : Blo 972592 3166469 := bbase (se 4 (by rfl) ⟨296856, by rfl⟩ : syracuseStep 3166469 = 593713) (by norm_num)
theorem B1462541 : Blo 972592 1462541 := bbase (se 3 (by rfl) ⟨274226, by rfl⟩ : syracuseStep 1462541 = 548453) (by norm_num)
theorem B1462565 : Blo 972592 1462565 := bbase (se 4 (by rfl) ⟨137115, by rfl⟩ : syracuseStep 1462565 = 274231) (by norm_num)
theorem B1462589 : Blo 972592 1462589 := bbase (se 3 (by rfl) ⟨274235, by rfl⟩ : syracuseStep 1462589 = 548471) (by norm_num)
theorem B1462613 : Blo 972592 1462613 := bbase (se 10 (by rfl) ⟨2142, by rfl⟩ : syracuseStep 1462613 = 4285) (by norm_num)
theorem B1233245 : Blo 972592 1233245 := bbase (se 3 (by rfl) ⟨231233, by rfl⟩ : syracuseStep 1233245 = 462467) (by norm_num)
theorem B1462637 : Blo 972592 1462637 := bbase (se 3 (by rfl) ⟨274244, by rfl⟩ : syracuseStep 1462637 = 548489) (by norm_num)
theorem B1462661 : Blo 972592 1462661 := bbase (se 4 (by rfl) ⟨137124, by rfl⟩ : syracuseStep 1462661 = 274249) (by norm_num)
theorem B1233301 : Blo 972592 1233301 := bbase (se 6 (by rfl) ⟨28905, by rfl⟩ : syracuseStep 1233301 = 57811) (by norm_num)
theorem B1462685 : Blo 972592 1462685 := bbase (se 3 (by rfl) ⟨274253, by rfl⟩ : syracuseStep 1462685 = 548507) (by norm_num)
theorem B1462709 : Blo 972592 1462709 := bbase (se 5 (by rfl) ⟨68564, by rfl⟩ : syracuseStep 1462709 = 137129) (by norm_num)
theorem B1692085 : Blo 972592 1692085 := bbase (se 5 (by rfl) ⟨79316, by rfl⟩ : syracuseStep 1692085 = 158633) (by norm_num)
theorem B1462733 : Blo 972592 1462733 := bbase (se 3 (by rfl) ⟨274262, by rfl⟩ : syracuseStep 1462733 = 548525) (by norm_num)
theorem B1462757 : Blo 972592 1462757 := bbase (se 4 (by rfl) ⟨137133, by rfl⟩ : syracuseStep 1462757 = 274267) (by norm_num)
theorem B1233397 : Blo 972592 1233397 := bbase (se 5 (by rfl) ⟨57815, by rfl⟩ : syracuseStep 1233397 = 115631) (by norm_num)
theorem B2085365 : Blo 972592 2085365 := bbase (se 5 (by rfl) ⟨97751, by rfl⟩ : syracuseStep 2085365 = 195503) (by norm_num)
theorem B1462781 : Blo 972592 1462781 := bbase (se 3 (by rfl) ⟨274271, by rfl⟩ : syracuseStep 1462781 = 548543) (by norm_num)
theorem B2085373 : Blo 972592 2085373 := bbase (se 3 (by rfl) ⟨391007, by rfl⟩ : syracuseStep 2085373 = 782015) (by norm_num)
theorem B1462805 : Blo 972592 1462805 := bbase (se 6 (by rfl) ⟨34284, by rfl⟩ : syracuseStep 1462805 = 68569) (by norm_num)
theorem B1462829 : Blo 972592 1462829 := bbase (se 3 (by rfl) ⟨274280, by rfl⟩ : syracuseStep 1462829 = 548561) (by norm_num)
theorem B1462853 : Blo 972592 1462853 := bbase (se 4 (by rfl) ⟨137142, by rfl⟩ : syracuseStep 1462853 = 274285) (by norm_num)
theorem B15782485 : Blo 972592 15782485 := bbase (se 8 (by rfl) ⟨92475, by rfl⟩ : syracuseStep 15782485 = 184951) (by norm_num)
theorem B1462877 : Blo 972592 1462877 := bbase (se 3 (by rfl) ⟨274289, by rfl⟩ : syracuseStep 1462877 = 548579) (by norm_num)
theorem B1462901 : Blo 972592 1462901 := bbase (se 5 (by rfl) ⟨68573, by rfl⟩ : syracuseStep 1462901 = 137147) (by norm_num)
theorem B1462925 : Blo 972592 1462925 := bbase (se 3 (by rfl) ⟨274298, by rfl⟩ : syracuseStep 1462925 = 548597) (by norm_num)
theorem B1233569 : Blo 972592 1233569 := bbase (se 2 (by rfl) ⟨462588, by rfl⟩ : syracuseStep 1233569 = 925177) (by norm_num)
theorem B1462949 : Blo 972592 1462949 := bbase (se 4 (by rfl) ⟨137151, by rfl⟩ : syracuseStep 1462949 = 274303) (by norm_num)
theorem B1462973 : Blo 972592 1462973 := bbase (se 3 (by rfl) ⟨274307, by rfl⟩ : syracuseStep 1462973 = 548615) (by norm_num)
theorem B1462997 : Blo 972592 1462997 := bbase (se 7 (by rfl) ⟨17144, by rfl⟩ : syracuseStep 1462997 = 34289) (by norm_num)
theorem B1233625 : Blo 972592 1233625 := bbase (se 2 (by rfl) ⟨462609, by rfl⟩ : syracuseStep 1233625 = 925219) (by norm_num)
theorem B1463021 : Blo 972592 1463021 := bbase (se 3 (by rfl) ⟨274316, by rfl⟩ : syracuseStep 1463021 = 548633) (by norm_num)
theorem B4674293 : Blo 972592 4674293 := bbase (se 5 (by rfl) ⟨219107, by rfl⟩ : syracuseStep 4674293 = 438215) (by norm_num)
theorem B1463045 : Blo 972592 1463045 := bbase (se 4 (by rfl) ⟨137160, by rfl⟩ : syracuseStep 1463045 = 274321) (by norm_num)
theorem B1463069 : Blo 972592 1463069 := bbase (se 3 (by rfl) ⟨274325, by rfl⟩ : syracuseStep 1463069 = 548651) (by norm_num)
theorem B1463093 : Blo 972592 1463093 := bbase (se 5 (by rfl) ⟨68582, by rfl⟩ : syracuseStep 1463093 = 137165) (by norm_num)
theorem B1233721 : Blo 972592 1233721 := bbase (se 2 (by rfl) ⟨462645, by rfl⟩ : syracuseStep 1233721 = 925291) (by norm_num)
theorem B1463117 : Blo 972592 1463117 := bbase (se 3 (by rfl) ⟨274334, by rfl⟩ : syracuseStep 1463117 = 548669) (by norm_num)
theorem B1463141 : Blo 972592 1463141 := bbase (se 4 (by rfl) ⟨137169, by rfl⟩ : syracuseStep 1463141 = 274339) (by norm_num)
theorem B1463165 : Blo 972592 1463165 := bbase (se 3 (by rfl) ⟨274343, by rfl⟩ : syracuseStep 1463165 = 548687) (by norm_num)
theorem B1561493 : Blo 972592 1561493 := bbase (se 6 (by rfl) ⟨36597, by rfl⟩ : syracuseStep 1561493 = 73195) (by norm_num)
theorem B1463189 : Blo 972592 1463189 := bbase (se 6 (by rfl) ⟨34293, by rfl⟩ : syracuseStep 1463189 = 68587) (by norm_num)
theorem B1463213 : Blo 972592 1463213 := bbase (se 3 (by rfl) ⟨274352, by rfl⟩ : syracuseStep 1463213 = 548705) (by norm_num)
theorem B1463237 : Blo 972592 1463237 := bbase (se 4 (by rfl) ⟨137178, by rfl⟩ : syracuseStep 1463237 = 274357) (by norm_num)
theorem B1463261 : Blo 972592 1463261 := bbase (se 3 (by rfl) ⟨274361, by rfl⟩ : syracuseStep 1463261 = 548723) (by norm_num)
theorem B1233893 : Blo 972592 1233893 := bbase (se 4 (by rfl) ⟨115677, by rfl⟩ : syracuseStep 1233893 = 231355) (by norm_num)
theorem B1463285 : Blo 972592 1463285 := bbase (se 5 (by rfl) ⟨68591, by rfl⟩ : syracuseStep 1463285 = 137183) (by norm_num)
theorem B1463309 : Blo 972592 1463309 := bbase (se 3 (by rfl) ⟨274370, by rfl⟩ : syracuseStep 1463309 = 548741) (by norm_num)
theorem B1561621 : Blo 972592 1561621 := bbase (se 6 (by rfl) ⟨36600, by rfl⟩ : syracuseStep 1561621 = 73201) (by norm_num)
theorem B1233949 : Blo 972592 1233949 := bbase (se 3 (by rfl) ⟨231365, by rfl⟩ : syracuseStep 1233949 = 462731) (by norm_num)
theorem B1463333 : Blo 972592 1463333 := bbase (se 4 (by rfl) ⟨137187, by rfl⟩ : syracuseStep 1463333 = 274375) (by norm_num)
theorem B1463357 : Blo 972592 1463357 := bbase (se 3 (by rfl) ⟨274379, by rfl⟩ : syracuseStep 1463357 = 548759) (by norm_num)
theorem B21353557 : Blo 972592 21353557 := bbase (se 8 (by rfl) ⟨125118, by rfl⟩ : syracuseStep 21353557 = 250237) (by norm_num)
theorem B1561685 : Blo 972592 1561685 := bbase (se 8 (by rfl) ⟨9150, by rfl⟩ : syracuseStep 1561685 = 18301) (by norm_num)
theorem B1463381 : Blo 972592 1463381 := bbase (se 8 (by rfl) ⟨8574, by rfl⟩ : syracuseStep 1463381 = 17149) (by norm_num)
theorem B1463405 : Blo 972592 1463405 := bbase (se 3 (by rfl) ⟨274388, by rfl⟩ : syracuseStep 1463405 = 548777) (by norm_num)
theorem B1234045 : Blo 972592 1234045 := bbase (se 3 (by rfl) ⟨231383, by rfl⟩ : syracuseStep 1234045 = 462767) (by norm_num)
theorem B1463429 : Blo 972592 1463429 := bbase (se 4 (by rfl) ⟨137196, by rfl⟩ : syracuseStep 1463429 = 274393) (by norm_num)
theorem B1463453 : Blo 972592 1463453 := bbase (se 3 (by rfl) ⟨274397, by rfl⟩ : syracuseStep 1463453 = 548795) (by norm_num)
theorem B1463477 : Blo 972592 1463477 := bbase (se 5 (by rfl) ⟨68600, by rfl⟩ : syracuseStep 1463477 = 137201) (by norm_num)
theorem B1463501 : Blo 972592 1463501 := bbase (se 3 (by rfl) ⟨274406, by rfl⟩ : syracuseStep 1463501 = 548813) (by norm_num)
theorem B1463525 : Blo 972592 1463525 := bbase (se 4 (by rfl) ⟨137205, by rfl⟩ : syracuseStep 1463525 = 274411) (by norm_num)
theorem B4936949 : Blo 972592 4936949 := bbase (se 5 (by rfl) ⟨231419, by rfl⟩ : syracuseStep 4936949 = 462839) (by norm_num)
theorem B1463549 : Blo 972592 1463549 := bbase (se 3 (by rfl) ⟨274415, by rfl⟩ : syracuseStep 1463549 = 548831) (by norm_num)
theorem B1463573 : Blo 972592 1463573 := bbase (se 6 (by rfl) ⟨34302, by rfl⟩ : syracuseStep 1463573 = 68605) (by norm_num)
theorem B1234217 : Blo 972592 1234217 := bbase (se 2 (by rfl) ⟨462831, by rfl⟩ : syracuseStep 1234217 = 925663) (by norm_num)
theorem B1463597 : Blo 972592 1463597 := bbase (se 3 (by rfl) ⟨274424, by rfl⟩ : syracuseStep 1463597 = 548849) (by norm_num)
theorem B1463621 : Blo 972592 1463621 := bbase (se 4 (by rfl) ⟨137214, by rfl⟩ : syracuseStep 1463621 = 274429) (by norm_num)
theorem B1168717 : Blo 972592 1168717 := bbase (se 3 (by rfl) ⟨219134, by rfl⟩ : syracuseStep 1168717 = 438269) (by norm_num)
theorem B1463645 : Blo 972592 1463645 := bbase (se 3 (by rfl) ⟨274433, by rfl⟩ : syracuseStep 1463645 = 548867) (by norm_num)
theorem B1234273 : Blo 972592 1234273 := bbase (se 2 (by rfl) ⟨462852, by rfl⟩ : syracuseStep 1234273 = 925705) (by norm_num)
theorem B1463669 : Blo 972592 1463669 := bbase (se 5 (by rfl) ⟨68609, by rfl⟩ : syracuseStep 1463669 = 137219) (by norm_num)
theorem B1463693 : Blo 972592 1463693 := bbase (se 3 (by rfl) ⟨274442, by rfl⟩ : syracuseStep 1463693 = 548885) (by norm_num)
theorem B1463717 : Blo 972592 1463717 := bbase (se 4 (by rfl) ⟨137223, by rfl⟩ : syracuseStep 1463717 = 274447) (by norm_num)
theorem B1168813 : Blo 972592 1168813 := bbase (se 3 (by rfl) ⟨219152, by rfl⟩ : syracuseStep 1168813 = 438305) (by norm_num)
theorem B1463741 : Blo 972592 1463741 := bbase (se 3 (by rfl) ⟨274451, by rfl⟩ : syracuseStep 1463741 = 548903) (by norm_num)
theorem B1234369 : Blo 972592 1234369 := bbase (se 2 (by rfl) ⟨462888, by rfl⟩ : syracuseStep 1234369 = 925777) (by norm_num)
theorem B1463765 : Blo 972592 1463765 := bbase (se 7 (by rfl) ⟨17153, by rfl⟩ : syracuseStep 1463765 = 34307) (by norm_num)
theorem B1758685 : Blo 972592 1758685 := bbase (se 3 (by rfl) ⟨329753, by rfl⟩ : syracuseStep 1758685 = 659507) (by norm_num)
theorem B1463789 : Blo 972592 1463789 := bbase (se 3 (by rfl) ⟨274460, by rfl⟩ : syracuseStep 1463789 = 548921) (by norm_num)
theorem B1463813 : Blo 972592 1463813 := bbase (se 4 (by rfl) ⟨137232, by rfl⟩ : syracuseStep 1463813 = 274465) (by norm_num)
theorem B1463837 : Blo 972592 1463837 := bbase (se 3 (by rfl) ⟨274469, by rfl⟩ : syracuseStep 1463837 = 548939) (by norm_num)
theorem B1463861 : Blo 972592 1463861 := bbase (se 5 (by rfl) ⟨68618, by rfl⟩ : syracuseStep 1463861 = 137237) (by norm_num)
theorem B1463885 : Blo 972592 1463885 := bbase (se 3 (by rfl) ⟨274478, by rfl⟩ : syracuseStep 1463885 = 548957) (by norm_num)
theorem B1463909 : Blo 972592 1463909 := bbase (se 4 (by rfl) ⟨137241, by rfl⟩ : syracuseStep 1463909 = 274483) (by norm_num)
theorem B1234541 : Blo 972592 1234541 := bbase (se 3 (by rfl) ⟨231476, by rfl⟩ : syracuseStep 1234541 = 462953) (by norm_num)
theorem B1463933 : Blo 972592 1463933 := bbase (se 3 (by rfl) ⟨274487, by rfl⟩ : syracuseStep 1463933 = 548975) (by norm_num)
theorem B1463957 : Blo 972592 1463957 := bbase (se 6 (by rfl) ⟨34311, by rfl⟩ : syracuseStep 1463957 = 68623) (by norm_num)
theorem B1234597 : Blo 972592 1234597 := bbase (se 4 (by rfl) ⟨115743, by rfl⟩ : syracuseStep 1234597 = 231487) (by norm_num)
theorem B1463981 : Blo 972592 1463981 := bbase (se 3 (by rfl) ⟨274496, by rfl⟩ : syracuseStep 1463981 = 548993) (by norm_num)
theorem B1464005 : Blo 972592 1464005 := bbase (se 4 (by rfl) ⟨137250, by rfl⟩ : syracuseStep 1464005 = 274501) (by norm_num)
theorem B1464029 : Blo 972592 1464029 := bbase (se 3 (by rfl) ⟨274505, by rfl⟩ : syracuseStep 1464029 = 549011) (by norm_num)
theorem B1464053 : Blo 972592 1464053 := bbase (se 5 (by rfl) ⟨68627, by rfl⟩ : syracuseStep 1464053 = 137255) (by norm_num)
theorem B2807557 : Blo 972592 2807557 := bbase (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) (by norm_num)
theorem B1234693 : Blo 972592 1234693 := bbase (se 4 (by rfl) ⟨115752, by rfl⟩ : syracuseStep 1234693 = 231505) (by norm_num)
theorem B1464077 : Blo 972592 1464077 := bbase (se 3 (by rfl) ⟨274514, by rfl⟩ : syracuseStep 1464077 = 549029) (by norm_num)
theorem B1464101 : Blo 972592 1464101 := bbase (se 4 (by rfl) ⟨137259, by rfl⟩ : syracuseStep 1464101 = 274519) (by norm_num)
theorem B2774837 : Blo 972592 2774837 := bbase (se 5 (by rfl) ⟨130070, by rfl⟩ : syracuseStep 2774837 = 260141) (by norm_num)
theorem B1464125 : Blo 972592 1464125 := bbase (se 3 (by rfl) ⟨274523, by rfl⟩ : syracuseStep 1464125 = 549047) (by norm_num)
theorem B1464149 : Blo 972592 1464149 := bbase (se 9 (by rfl) ⟨4289, by rfl⟩ : syracuseStep 1464149 = 8579) (by norm_num)
theorem B1464173 : Blo 972592 1464173 := bbase (se 3 (by rfl) ⟨274532, by rfl⟩ : syracuseStep 1464173 = 549065) (by norm_num)
theorem B1464197 : Blo 972592 1464197 := bbase (se 4 (by rfl) ⟨137268, by rfl⟩ : syracuseStep 1464197 = 274537) (by norm_num)
theorem B1464221 : Blo 972592 1464221 := bbase (se 3 (by rfl) ⟨274541, by rfl⟩ : syracuseStep 1464221 = 549083) (by norm_num)
theorem B1234865 : Blo 972592 1234865 := bbase (se 2 (by rfl) ⟨463074, by rfl⟩ : syracuseStep 1234865 = 926149) (by norm_num)
theorem B1464245 : Blo 972592 1464245 := bbase (se 5 (by rfl) ⟨68636, by rfl⟩ : syracuseStep 1464245 = 137273) (by norm_num)
theorem B1464269 : Blo 972592 1464269 := bbase (se 3 (by rfl) ⟨274550, by rfl⟩ : syracuseStep 1464269 = 549101) (by norm_num)
theorem B1464293 : Blo 972592 1464293 := bbase (se 4 (by rfl) ⟨137277, by rfl⟩ : syracuseStep 1464293 = 274555) (by norm_num)
theorem B1234921 : Blo 972592 1234921 := bbase (se 2 (by rfl) ⟨463095, by rfl⟩ : syracuseStep 1234921 = 926191) (by norm_num)
theorem B1464317 : Blo 972592 1464317 := bbase (se 3 (by rfl) ⟨274559, by rfl⟩ : syracuseStep 1464317 = 549119) (by norm_num)
theorem B1464341 : Blo 972592 1464341 := bbase (se 6 (by rfl) ⟨34320, by rfl⟩ : syracuseStep 1464341 = 68641) (by norm_num)
theorem B1464365 : Blo 972592 1464365 := bbase (se 3 (by rfl) ⟨274568, by rfl⟩ : syracuseStep 1464365 = 549137) (by norm_num)
theorem B1464389 : Blo 972592 1464389 := bbase (se 4 (by rfl) ⟨137286, by rfl⟩ : syracuseStep 1464389 = 274573) (by norm_num)
theorem B1235017 : Blo 972592 1235017 := bbase (se 2 (by rfl) ⟨463131, by rfl⟩ : syracuseStep 1235017 = 926263) (by norm_num)
theorem B1464413 : Blo 972592 1464413 := bbase (se 3 (by rfl) ⟨274577, by rfl⟩ : syracuseStep 1464413 = 549155) (by norm_num)
theorem B1464437 : Blo 972592 1464437 := bbase (se 5 (by rfl) ⟨68645, by rfl⟩ : syracuseStep 1464437 = 137291) (by norm_num)
theorem B1464461 : Blo 972592 1464461 := bbase (se 3 (by rfl) ⟨274586, by rfl⟩ : syracuseStep 1464461 = 549173) (by norm_num)
theorem B1464485 : Blo 972592 1464485 := bbase (se 4 (by rfl) ⟨137295, by rfl⟩ : syracuseStep 1464485 = 274591) (by norm_num)
theorem B1169597 : Blo 972592 1169597 := bbase (se 3 (by rfl) ⟨219299, by rfl⟩ : syracuseStep 1169597 = 438599) (by norm_num)
theorem B1464509 : Blo 972592 1464509 := bbase (se 3 (by rfl) ⟨274595, by rfl⟩ : syracuseStep 1464509 = 549191) (by norm_num)
theorem B1464533 : Blo 972592 1464533 := bbase (se 7 (by rfl) ⟨17162, by rfl⟩ : syracuseStep 1464533 = 34325) (by norm_num)
theorem B1464557 : Blo 972592 1464557 := bbase (se 3 (by rfl) ⟨274604, by rfl⟩ : syracuseStep 1464557 = 549209) (by norm_num)
theorem B1235189 : Blo 972592 1235189 := bbase (se 5 (by rfl) ⟨57899, by rfl⟩ : syracuseStep 1235189 = 115799) (by norm_num)
theorem B1464581 : Blo 972592 1464581 := bbase (se 4 (by rfl) ⟨137304, by rfl⟩ : syracuseStep 1464581 = 274609) (by norm_num)
theorem B1464605 : Blo 972592 1464605 := bbase (se 3 (by rfl) ⟨274613, by rfl⟩ : syracuseStep 1464605 = 549227) (by norm_num)
theorem B1038629 : Blo 972592 1038629 := bbase (se 4 (by rfl) ⟨97371, by rfl⟩ : syracuseStep 1038629 = 194743) (by norm_num)
theorem B1235245 : Blo 972592 1235245 := bbase (se 3 (by rfl) ⟨231608, by rfl⟩ : syracuseStep 1235245 = 463217) (by norm_num)
theorem B1464629 : Blo 972592 1464629 := bbase (se 5 (by rfl) ⟨68654, by rfl⟩ : syracuseStep 1464629 = 137309) (by norm_num)
theorem B1464653 : Blo 972592 1464653 := bbase (se 3 (by rfl) ⟨274622, by rfl⟩ : syracuseStep 1464653 = 549245) (by norm_num)
theorem B1464677 : Blo 972592 1464677 := bbase (se 4 (by rfl) ⟨137313, by rfl⟩ : syracuseStep 1464677 = 274627) (by norm_num)
theorem B1563005 : Blo 972592 1563005 := bbase (se 3 (by rfl) ⟨293063, by rfl⟩ : syracuseStep 1563005 = 586127) (by norm_num)
theorem B1464701 : Blo 972592 1464701 := bbase (se 3 (by rfl) ⟨274631, by rfl⟩ : syracuseStep 1464701 = 549263) (by norm_num)
theorem B2218373 : Blo 972592 2218373 := bbase (se 4 (by rfl) ⟨207972, by rfl⟩ : syracuseStep 2218373 = 415945) (by norm_num)
theorem B1235341 : Blo 972592 1235341 := bbase (se 3 (by rfl) ⟨231626, by rfl⟩ : syracuseStep 1235341 = 463253) (by norm_num)
theorem B10541461 : Blo 972592 10541461 := bbase (se 6 (by rfl) ⟨247065, by rfl⟩ : syracuseStep 10541461 = 494131) (by norm_num)
theorem B1464725 : Blo 972592 1464725 := bbase (se 6 (by rfl) ⟨34329, by rfl⟩ : syracuseStep 1464725 = 68659) (by norm_num)
theorem B1464749 : Blo 972592 1464749 := bbase (se 3 (by rfl) ⟨274640, by rfl⟩ : syracuseStep 1464749 = 549281) (by norm_num)
theorem B1464773 : Blo 972592 1464773 := bbase (se 4 (by rfl) ⟨137322, by rfl⟩ : syracuseStep 1464773 = 274645) (by norm_num)
theorem B2775509 : Blo 972592 2775509 := bbase (se 7 (by rfl) ⟨32525, by rfl⟩ : syracuseStep 2775509 = 65051) (by norm_num)
theorem B1464797 : Blo 972592 1464797 := bbase (se 3 (by rfl) ⟨274649, by rfl⟩ : syracuseStep 1464797 = 549299) (by norm_num)
theorem B1169905 : Blo 972592 1169905 := bbase (se 2 (by rfl) ⟨438714, by rfl⟩ : syracuseStep 1169905 = 877429) (by norm_num)
theorem B1464821 : Blo 972592 1464821 := bbase (se 5 (by rfl) ⟨68663, by rfl⟩ : syracuseStep 1464821 = 137327) (by norm_num)
theorem B1563133 : Blo 972592 1563133 := bbase (se 3 (by rfl) ⟨293087, by rfl⟩ : syracuseStep 1563133 = 586175) (by norm_num)
theorem B4938245 : Blo 972592 4938245 := bbase (se 4 (by rfl) ⟨462960, by rfl⟩ : syracuseStep 4938245 = 925921) (by norm_num)
theorem B1464845 : Blo 972592 1464845 := bbase (se 3 (by rfl) ⟨274658, by rfl⟩ : syracuseStep 1464845 = 549317) (by norm_num)
theorem B1464869 : Blo 972592 1464869 := bbase (se 4 (by rfl) ⟨137331, by rfl⟩ : syracuseStep 1464869 = 274663) (by norm_num)
theorem B1235513 : Blo 972592 1235513 := bbase (se 2 (by rfl) ⟨463317, by rfl⟩ : syracuseStep 1235513 = 926635) (by norm_num)
theorem B1235569 : Blo 972592 1235569 := bbase (se 2 (by rfl) ⟨463338, by rfl⟩ : syracuseStep 1235569 = 926677) (by norm_num)
theorem B3693221 : Blo 972592 3693221 := bbase (se 4 (by rfl) ⟨346239, by rfl⟩ : syracuseStep 3693221 = 692479) (by norm_num)
theorem B2808485 : Blo 972592 2808485 := bbase (se 4 (by rfl) ⟨263295, by rfl⟩ : syracuseStep 2808485 = 526591) (by norm_num)
theorem B1235665 : Blo 972592 1235665 := bbase (se 2 (by rfl) ⟨463374, by rfl⟩ : syracuseStep 1235665 = 926749) (by norm_num)
theorem B1039073 : Blo 972592 1039073 := bbase (se 2 (by rfl) ⟨389652, by rfl⟩ : syracuseStep 1039073 = 779305) (by norm_num)
theorem B1170293 : Blo 972592 1170293 := bbase (se 5 (by rfl) ⟨54857, by rfl⟩ : syracuseStep 1170293 = 109715) (by norm_num)
theorem B1235837 : Blo 972592 1235837 := bbase (se 3 (by rfl) ⟨231719, by rfl⟩ : syracuseStep 1235837 = 463439) (by norm_num)
theorem B2775941 : Blo 972592 2775941 := bbase (se 4 (by rfl) ⟨260244, by rfl⟩ : syracuseStep 2775941 = 520489) (by norm_num)
theorem B1235893 : Blo 972592 1235893 := bbase (se 5 (by rfl) ⟨57932, by rfl⟩ : syracuseStep 1235893 = 115865) (by norm_num)
theorem B3693509 : Blo 972592 3693509 := bbase (se 4 (by rfl) ⟨346266, by rfl⟩ : syracuseStep 3693509 = 692533) (by norm_num)
theorem B1039321 : Blo 972592 1039321 := bbase (se 2 (by rfl) ⟨389745, by rfl⟩ : syracuseStep 1039321 = 779491) (by norm_num)
theorem B1235989 : Blo 972592 1235989 := bbase (se 6 (by rfl) ⟨28968, by rfl⟩ : syracuseStep 1235989 = 57937) (by norm_num)
theorem B1170649 : Blo 972592 1170649 := bbase (se 2 (by rfl) ⟨438993, by rfl⟩ : syracuseStep 1170649 = 877987) (by norm_num)
theorem B1563941 : Blo 972592 1563941 := bbase (se 4 (by rfl) ⟨146619, by rfl⟩ : syracuseStep 1563941 = 293239) (by norm_num)
theorem B1039765 : Blo 972592 1039765 := bbase (se 6 (by rfl) ⟨24369, by rfl⟩ : syracuseStep 1039765 = 48739) (by norm_num)
theorem B1039825 : Blo 972592 1039825 := bbase (se 2 (by rfl) ⟨389934, by rfl⟩ : syracuseStep 1039825 = 779869) (by norm_num)
theorem B1170985 : Blo 972592 1170985 := bbase (se 2 (by rfl) ⟨439119, by rfl⟩ : syracuseStep 1170985 = 878239) (by norm_num)
theorem B1334845 : Blo 972592 1334845 := bbase (se 3 (by rfl) ⟨250283, by rfl⟩ : syracuseStep 1334845 = 500567) (by norm_num)
theorem B1564229 : Blo 972592 1564229 := bbase (se 4 (by rfl) ⟨146646, by rfl⟩ : syracuseStep 1564229 = 293293) (by norm_num)
theorem B2776693 : Blo 972592 2776693 := bbase (se 5 (by rfl) ⟨130157, by rfl⟩ : syracuseStep 2776693 = 260315) (by norm_num)
theorem B1040141 : Blo 972592 1040141 := bbase (se 3 (by rfl) ⟨195026, by rfl⟩ : syracuseStep 1040141 = 390053) (by norm_num)
theorem B4939541 : Blo 972592 4939541 := bbase (se 6 (by rfl) ⟨115770, by rfl⟩ : syracuseStep 4939541 = 231541) (by norm_num)
theorem B3694693 : Blo 972592 3694693 := bbase (se 4 (by rfl) ⟨346377, by rfl⟩ : syracuseStep 3694693 = 692755) (by norm_num)
theorem B1040585 : Blo 972592 1040585 := bbase (se 2 (by rfl) ⟨390219, by rfl⟩ : syracuseStep 1040585 = 780439) (by norm_num)
theorem B1040645 : Blo 972592 1040645 := bbase (se 4 (by rfl) ⟨97560, by rfl⟩ : syracuseStep 1040645 = 195121) (by norm_num)
theorem B4677925 : Blo 972592 4677925 := bbase (se 4 (by rfl) ⟨438555, by rfl⟩ : syracuseStep 4677925 = 877111) (by norm_num)
theorem B1040773 : Blo 972592 1040773 := bbase (se 4 (by rfl) ⟨97572, by rfl⟩ : syracuseStep 1040773 = 195145) (by norm_num)
theorem B3694997 : Blo 972592 3694997 := bbase (se 6 (by rfl) ⟨86601, by rfl⟩ : syracuseStep 3694997 = 173203) (by norm_num)
theorem B1171865 : Blo 972592 1171865 := bbase (se 2 (by rfl) ⟨439449, by rfl⟩ : syracuseStep 1171865 = 878899) (by norm_num)
theorem B4940293 : Blo 972592 4940293 := bbase (se 4 (by rfl) ⟨463152, by rfl⟩ : syracuseStep 4940293 = 926305) (by norm_num)
theorem B12477077 : Blo 972592 12477077 := bbase (se 6 (by rfl) ⟨292431, by rfl⟩ : syracuseStep 12477077 = 584863) (by norm_num)
theorem B1172173 : Blo 972592 1172173 := bbase (se 3 (by rfl) ⟨219782, by rfl⟩ : syracuseStep 1172173 = 439565) (by norm_num)
theorem B2220853 : Blo 972592 2220853 := bbase (se 5 (by rfl) ⟨104102, by rfl⟩ : syracuseStep 2220853 = 208205) (by norm_num)
theorem B5923637 : Blo 972592 5923637 := bbase (se 5 (by rfl) ⟨277670, by rfl⟩ : syracuseStep 5923637 = 555341) (by norm_num)
theorem B1041217 : Blo 972592 1041217 := bbase (se 2 (by rfl) ⟨390456, by rfl⟩ : syracuseStep 1041217 = 780913) (by norm_num)
theorem B1041337 : Blo 972592 1041337 := bbase (se 2 (by rfl) ⟨390501, by rfl⟩ : syracuseStep 1041337 = 781003) (by norm_num)
theorem B4219877 : Blo 972592 4219877 := bbase (se 4 (by rfl) ⟨395613, by rfl⟩ : syracuseStep 4219877 = 791227) (by norm_num)
theorem B1663997 : Blo 972592 1663997 := bbase (se 3 (by rfl) ⟨311999, by rfl⟩ : syracuseStep 1663997 = 623999) (by norm_num)
theorem B4940837 : Blo 972592 4940837 := bbase (se 4 (by rfl) ⟨463203, by rfl⟩ : syracuseStep 4940837 = 926407) (by norm_num)
theorem B2188349 : Blo 972592 2188349 := bbase (se 3 (by rfl) ⟨410315, by rfl⟩ : syracuseStep 2188349 = 820631) (by norm_num)
theorem B1172557 : Blo 972592 1172557 := bbase (se 3 (by rfl) ⟨219854, by rfl⟩ : syracuseStep 1172557 = 439709) (by norm_num)
theorem B1172561 : Blo 972592 1172561 := bbase (se 2 (by rfl) ⟨439710, by rfl⟩ : syracuseStep 1172561 = 879421) (by norm_num)
theorem B2188421 : Blo 972592 2188421 := bbase (se 4 (by rfl) ⟨205164, by rfl⟩ : syracuseStep 2188421 = 410329) (by norm_num)
theorem B1041589 : Blo 972592 1041589 := bbase (se 5 (by rfl) ⟨48824, by rfl⟩ : syracuseStep 1041589 = 97649) (by norm_num)
theorem B1041593 : Blo 972592 1041593 := bbase (se 2 (by rfl) ⟨390597, by rfl⟩ : syracuseStep 1041593 = 781195) (by norm_num)
theorem B2188493 : Blo 972592 2188493 := bbase (se 3 (by rfl) ⟨410342, by rfl⟩ : syracuseStep 2188493 = 820685) (by norm_num)
theorem B5268725 : Blo 972592 5268725 := bbase (se 5 (by rfl) ⟨246971, by rfl⟩ : syracuseStep 5268725 = 493943) (by norm_num)
theorem B2188565 : Blo 972592 2188565 := bbase (se 6 (by rfl) ⟨51294, by rfl⟩ : syracuseStep 2188565 = 102589) (by norm_num)
theorem B2221357 : Blo 972592 2221357 := bbase (se 3 (by rfl) ⟨416504, by rfl⟩ : syracuseStep 2221357 = 833009) (by norm_num)
theorem B2188637 : Blo 972592 2188637 := bbase (se 3 (by rfl) ⟨410369, by rfl⟩ : syracuseStep 2188637 = 820739) (by norm_num)
theorem B2188709 : Blo 972592 2188709 := bbase (se 4 (by rfl) ⟨205191, by rfl⟩ : syracuseStep 2188709 = 410383) (by norm_num)
theorem B8316341 : Blo 972592 8316341 := bbase (se 5 (by rfl) ⟨389828, by rfl⟩ : syracuseStep 8316341 = 779657) (by norm_num)
theorem B1172965 : Blo 972592 1172965 := bbase (se 4 (by rfl) ⟨109965, by rfl⟩ : syracuseStep 1172965 = 219931) (by norm_num)
theorem B2188781 : Blo 972592 2188781 := bbase (se 3 (by rfl) ⟨410396, by rfl⟩ : syracuseStep 2188781 = 820793) (by norm_num)
theorem B2188853 : Blo 972592 2188853 := bbase (se 5 (by rfl) ⟨102602, by rfl⟩ : syracuseStep 2188853 = 205205) (by norm_num)
theorem B2188925 : Blo 972592 2188925 := bbase (se 3 (by rfl) ⟨410423, by rfl⟩ : syracuseStep 2188925 = 820847) (by norm_num)
theorem B2188997 : Blo 972592 2188997 := bbase (se 4 (by rfl) ⟨205218, by rfl⟩ : syracuseStep 2188997 = 410437) (by norm_num)
theorem B1042157 : Blo 972592 1042157 := bbase (se 3 (by rfl) ⟨195404, by rfl⟩ : syracuseStep 1042157 = 390809) (by norm_num)
theorem B2189069 : Blo 972592 2189069 := bbase (se 3 (by rfl) ⟨410450, by rfl⟩ : syracuseStep 2189069 = 820901) (by norm_num)
theorem B2189141 : Blo 972592 2189141 := bbase (se 9 (by rfl) ⟨6413, by rfl⟩ : syracuseStep 2189141 = 12827) (by norm_num)
theorem B2189213 : Blo 972592 2189213 := bbase (se 3 (by rfl) ⟨410477, by rfl⟩ : syracuseStep 2189213 = 820955) (by norm_num)
theorem B1042345 : Blo 972592 1042345 := bbase (se 2 (by rfl) ⟨390879, by rfl⟩ : syracuseStep 1042345 = 781759) (by norm_num)
theorem B7399349 : Blo 972592 7399349 := bbase (se 5 (by rfl) ⟨346844, by rfl⟩ : syracuseStep 7399349 = 693689) (by norm_num)
theorem B1664957 : Blo 972592 1664957 := bbase (se 3 (by rfl) ⟨312179, by rfl⟩ : syracuseStep 1664957 = 624359) (by norm_num)
theorem B2189285 : Blo 972592 2189285 := bbase (se 4 (by rfl) ⟨205245, by rfl⟩ : syracuseStep 2189285 = 410491) (by norm_num)
theorem B2189357 : Blo 972592 2189357 := bbase (se 3 (by rfl) ⟨410504, by rfl⟩ : syracuseStep 2189357 = 821009) (by norm_num)
theorem B2189429 : Blo 972592 2189429 := bbase (se 5 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 2189429 = 205259) (by norm_num)
theorem B2189501 : Blo 972592 2189501 := bbase (se 3 (by rfl) ⟨410531, by rfl⟩ : syracuseStep 2189501 = 821063) (by norm_num)
theorem B2189573 : Blo 972592 2189573 := bbase (se 4 (by rfl) ⟨205272, by rfl⟩ : syracuseStep 2189573 = 410545) (by norm_num)
theorem B4942133 : Blo 972592 4942133 := bbase (se 5 (by rfl) ⟨231662, by rfl⟩ : syracuseStep 4942133 = 463325) (by norm_num)
theorem B2189645 : Blo 972592 2189645 := bbase (se 3 (by rfl) ⟨410558, by rfl⟩ : syracuseStep 2189645 = 821117) (by norm_num)
theorem B2189717 : Blo 972592 2189717 := bbase (se 6 (by rfl) ⟨51321, by rfl⟩ : syracuseStep 2189717 = 102643) (by norm_num)
theorem B2779541 : Blo 972592 2779541 := bbase (se 6 (by rfl) ⟨65145, by rfl⟩ : syracuseStep 2779541 = 130291) (by norm_num)
theorem B3697109 : Blo 972592 3697109 := bbase (se 7 (by rfl) ⟨43325, by rfl⟩ : syracuseStep 3697109 = 86651) (by norm_num)
theorem B2189789 : Blo 972592 2189789 := bbase (se 3 (by rfl) ⟨410585, by rfl⟩ : syracuseStep 2189789 = 821171) (by norm_num)
theorem B2189861 : Blo 972592 2189861 := bbase (se 4 (by rfl) ⟨205299, by rfl⟩ : syracuseStep 2189861 = 410599) (by norm_num)
theorem B2189933 : Blo 972592 2189933 := bbase (se 3 (by rfl) ⟨410612, by rfl⟩ : syracuseStep 2189933 = 821225) (by norm_num)
theorem B2190005 : Blo 972592 2190005 := bbase (se 5 (by rfl) ⟨102656, by rfl⟩ : syracuseStep 2190005 = 205313) (by norm_num)
theorem B3697397 : Blo 972592 3697397 := bbase (se 5 (by rfl) ⟨173315, by rfl⟩ : syracuseStep 3697397 = 346631) (by norm_num)
theorem B6253301 : Blo 972592 6253301 := bbase (se 5 (by rfl) ⟨293123, by rfl⟩ : syracuseStep 6253301 = 586247) (by norm_num)
theorem B2190077 : Blo 972592 2190077 := bbase (se 3 (by rfl) ⟨410639, by rfl⟩ : syracuseStep 2190077 = 821279) (by norm_num)
theorem B2190149 : Blo 972592 2190149 := bbase (se 4 (by rfl) ⟨205326, by rfl⟩ : syracuseStep 2190149 = 410653) (by norm_num)
theorem B2190221 : Blo 972592 2190221 := bbase (se 3 (by rfl) ⟨410666, by rfl⟩ : syracuseStep 2190221 = 821333) (by norm_num)
theorem B9989077 : Blo 972592 9989077 := bbase (se 7 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 9989077 = 234119) (by norm_num)
theorem B2190293 : Blo 972592 2190293 := bbase (se 7 (by rfl) ⟨25667, by rfl⟩ : syracuseStep 2190293 = 51335) (by norm_num)
theorem B2190365 : Blo 972592 2190365 := bbase (se 3 (by rfl) ⟨410693, by rfl⟩ : syracuseStep 2190365 = 821387) (by norm_num)
theorem B5925973 : Blo 972592 5925973 := bbase (se 8 (by rfl) ⟨34722, by rfl⟩ : syracuseStep 5925973 = 69445) (by norm_num)
theorem B2190437 : Blo 972592 2190437 := bbase (se 4 (by rfl) ⟨205353, by rfl⟩ : syracuseStep 2190437 = 410707) (by norm_num)
theorem B9989237 : Blo 972592 9989237 := bbase (se 5 (by rfl) ⟨468245, by rfl⟩ : syracuseStep 9989237 = 936491) (by norm_num)
theorem B2190509 : Blo 972592 2190509 := bbase (se 3 (by rfl) ⟨410720, by rfl⟩ : syracuseStep 2190509 = 821441) (by norm_num)
theorem B1404149 : Blo 972592 1404149 := bbase (se 5 (by rfl) ⟨65819, by rfl⟩ : syracuseStep 1404149 = 131639) (by norm_num)
theorem B2190581 : Blo 972592 2190581 := bbase (se 5 (by rfl) ⟨102683, by rfl⟩ : syracuseStep 2190581 = 205367) (by norm_num)
theorem B2190653 : Blo 972592 2190653 := bbase (se 3 (by rfl) ⟨410747, by rfl⟩ : syracuseStep 2190653 = 821495) (by norm_num)
theorem B2223445 : Blo 972592 2223445 := bbase (se 11 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2223445 = 3257) (by norm_num)
theorem B3796325 : Blo 972592 3796325 := bbase (se 4 (by rfl) ⟨355905, by rfl⟩ : syracuseStep 3796325 = 711811) (by norm_num)
theorem B2190725 : Blo 972592 2190725 := bbase (se 4 (by rfl) ⟨205380, by rfl⟩ : syracuseStep 2190725 = 410761) (by norm_num)
theorem B1109437 : Blo 972592 1109437 := bbase (se 3 (by rfl) ⟨208019, by rfl⟩ : syracuseStep 1109437 = 416039) (by norm_num)
theorem B2190797 : Blo 972592 2190797 := bbase (se 3 (by rfl) ⟨410774, by rfl⟩ : syracuseStep 2190797 = 821549) (by norm_num)
theorem B2190869 : Blo 972592 2190869 := bbase (se 6 (by rfl) ⟨51348, by rfl⟩ : syracuseStep 2190869 = 102697) (by norm_num)
theorem B2780725 : Blo 972592 2780725 := bbase (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) (by norm_num)
theorem B4943429 : Blo 972592 4943429 := bbase (se 4 (by rfl) ⟨463446, by rfl⟩ : syracuseStep 4943429 = 926893) (by norm_num)
theorem B2190941 : Blo 972592 2190941 := bbase (se 3 (by rfl) ⟨410801, by rfl⟩ : syracuseStep 2190941 = 821603) (by norm_num)
theorem B4157077 : Blo 972592 4157077 := bbase (se 6 (by rfl) ⟨97431, by rfl⟩ : syracuseStep 4157077 = 194863) (by norm_num)
theorem B2191013 : Blo 972592 2191013 := bbase (se 4 (by rfl) ⟨205407, by rfl⟩ : syracuseStep 2191013 = 410815) (by norm_num)
theorem B1502885 : Blo 972592 1502885 := bbase (se 4 (by rfl) ⟨140895, by rfl⟩ : syracuseStep 1502885 = 281791) (by norm_num)
theorem B2780885 : Blo 972592 2780885 := bbase (se 7 (by rfl) ⟨32588, by rfl⟩ : syracuseStep 2780885 = 65177) (by norm_num)
theorem B2191085 : Blo 972592 2191085 := bbase (se 3 (by rfl) ⟨410828, by rfl⟩ : syracuseStep 2191085 = 821657) (by norm_num)
theorem B2191157 : Blo 972592 2191157 := bbase (se 5 (by rfl) ⟨102710, by rfl⟩ : syracuseStep 2191157 = 205421) (by norm_num)
theorem B7499573 : Blo 972592 7499573 := bbase (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) (by norm_num)
theorem B2191229 : Blo 972592 2191229 := bbase (se 3 (by rfl) ⟨410855, by rfl⟩ : syracuseStep 2191229 = 821711) (by norm_num)
theorem B3698581 : Blo 972592 3698581 := bbase (se 6 (by rfl) ⟨86685, by rfl⟩ : syracuseStep 3698581 = 173371) (by norm_num)
theorem B1666981 : Blo 972592 1666981 := bbase (se 4 (by rfl) ⟨156279, by rfl⟩ : syracuseStep 1666981 = 312559) (by norm_num)
theorem B2191301 : Blo 972592 2191301 := bbase (se 4 (by rfl) ⟨205434, by rfl⟩ : syracuseStep 2191301 = 410869) (by norm_num)
theorem B2191373 : Blo 972592 2191373 := bbase (se 3 (by rfl) ⟨410882, by rfl⟩ : syracuseStep 2191373 = 821765) (by norm_num)
theorem B2256925 : Blo 972592 2256925 := bbase (se 3 (by rfl) ⟨423173, by rfl⟩ : syracuseStep 2256925 = 846347) (by norm_num)
theorem B2191445 : Blo 972592 2191445 := bbase (se 8 (by rfl) ⟨12840, by rfl⟩ : syracuseStep 2191445 = 25681) (by norm_num)
theorem B2191517 : Blo 972592 2191517 := bbase (se 3 (by rfl) ⟨410909, by rfl⟩ : syracuseStep 2191517 = 821819) (by norm_num)
theorem B1110181 : Blo 972592 1110181 := bbase (se 4 (by rfl) ⟨104079, by rfl⟩ : syracuseStep 1110181 = 208159) (by norm_num)
theorem B3698885 : Blo 972592 3698885 := bbase (se 4 (by rfl) ⟨346770, by rfl⟩ : syracuseStep 3698885 = 693541) (by norm_num)
theorem B2191589 : Blo 972592 2191589 := bbase (se 4 (by rfl) ⟨205461, by rfl⟩ : syracuseStep 2191589 = 410923) (by norm_num)
theorem B2191661 : Blo 972592 2191661 := bbase (se 3 (by rfl) ⟨410936, by rfl⟩ : syracuseStep 2191661 = 821873) (by norm_num)
theorem B2191733 : Blo 972592 2191733 := bbase (se 5 (by rfl) ⟨102737, by rfl⟩ : syracuseStep 2191733 = 205475) (by norm_num)
theorem B2191805 : Blo 972592 2191805 := bbase (se 3 (by rfl) ⟨410963, by rfl⟩ : syracuseStep 2191805 = 821927) (by norm_num)
theorem B2191877 : Blo 972592 2191877 := bbase (se 4 (by rfl) ⟨205488, by rfl⟩ : syracuseStep 2191877 = 410977) (by norm_num)
theorem B2191949 : Blo 972592 2191949 := bbase (se 3 (by rfl) ⟨410990, by rfl⟩ : syracuseStep 2191949 = 821981) (by norm_num)
theorem B2192021 : Blo 972592 2192021 := bbase (se 6 (by rfl) ⟨51375, by rfl⟩ : syracuseStep 2192021 = 102751) (by norm_num)
theorem B3961541 : Blo 972592 3961541 := bbase (se 4 (by rfl) ⟨371394, by rfl⟩ : syracuseStep 3961541 = 742789) (by norm_num)
theorem B2192093 : Blo 972592 2192093 := bbase (se 3 (by rfl) ⟨411017, by rfl⟩ : syracuseStep 2192093 = 822035) (by norm_num)
theorem B2192165 : Blo 972592 2192165 := bbase (se 4 (by rfl) ⟨205515, by rfl⟩ : syracuseStep 2192165 = 411031) (by norm_num)
theorem B2192237 : Blo 972592 2192237 := bbase (se 3 (by rfl) ⟨411044, by rfl⟩ : syracuseStep 2192237 = 822089) (by norm_num)
theorem B2192309 : Blo 972592 2192309 := bbase (se 5 (by rfl) ⟨102764, by rfl⟩ : syracuseStep 2192309 = 205529) (by norm_num)
theorem B2192381 : Blo 972592 2192381 := bbase (se 3 (by rfl) ⟨411071, by rfl⟩ : syracuseStep 2192381 = 822143) (by norm_num)
theorem B2192453 : Blo 972592 2192453 := bbase (se 4 (by rfl) ⟨205542, by rfl⟩ : syracuseStep 2192453 = 411085) (by norm_num)
theorem B2192525 : Blo 972592 2192525 := bbase (se 3 (by rfl) ⟨411098, by rfl⟩ : syracuseStep 2192525 = 822197) (by norm_num)
theorem B2192597 : Blo 972592 2192597 := bbase (se 7 (by rfl) ⟨25694, by rfl⟩ : syracuseStep 2192597 = 51389) (by norm_num)
theorem B2192669 : Blo 972592 2192669 := bbase (se 3 (by rfl) ⟨411125, by rfl⟩ : syracuseStep 2192669 = 822251) (by norm_num)
theorem B2192741 : Blo 972592 2192741 := bbase (se 4 (by rfl) ⟨205569, by rfl⟩ : syracuseStep 2192741 = 411139) (by norm_num)
theorem B2192813 : Blo 972592 2192813 := bbase (se 3 (by rfl) ⟨411152, by rfl⟩ : syracuseStep 2192813 = 822305) (by norm_num)
theorem B2192885 : Blo 972592 2192885 := bbase (se 5 (by rfl) ⟨102791, by rfl⟩ : syracuseStep 2192885 = 205583) (by norm_num)
theorem B1504813 : Blo 972592 1504813 := bbase (se 3 (by rfl) ⟨282152, by rfl⟩ : syracuseStep 1504813 = 564305) (by norm_num)
theorem B2192957 : Blo 972592 2192957 := bbase (se 3 (by rfl) ⟨411179, by rfl⟩ : syracuseStep 2192957 = 822359) (by norm_num)
theorem B2193029 : Blo 972592 2193029 := bbase (se 4 (by rfl) ⟨205596, by rfl⟩ : syracuseStep 2193029 = 411193) (by norm_num)
theorem B2193101 : Blo 972592 2193101 := bbase (se 3 (by rfl) ⟨411206, by rfl⟩ : syracuseStep 2193101 = 822413) (by norm_num)
theorem B2193173 : Blo 972592 2193173 := bbase (se 6 (by rfl) ⟨51402, by rfl⟩ : syracuseStep 2193173 = 102805) (by norm_num)
theorem B2193245 : Blo 972592 2193245 := bbase (se 3 (by rfl) ⟨411233, by rfl⟩ : syracuseStep 2193245 = 822467) (by norm_num)
theorem B2193317 : Blo 972592 2193317 := bbase (se 4 (by rfl) ⟨205623, by rfl⟩ : syracuseStep 2193317 = 411247) (by norm_num)
theorem B2193389 : Blo 972592 2193389 := bbase (se 3 (by rfl) ⟨411260, by rfl⟩ : syracuseStep 2193389 = 822521) (by norm_num)
theorem B4454405 : Blo 972592 4454405 := bbase (se 4 (by rfl) ⟨417600, by rfl⟩ : syracuseStep 4454405 = 835201) (by norm_num)
theorem B2193461 : Blo 972592 2193461 := bbase (se 5 (by rfl) ⟨102818, by rfl⟩ : syracuseStep 2193461 = 205637) (by norm_num)
theorem B2193533 : Blo 972592 2193533 := bbase (se 3 (by rfl) ⟨411287, by rfl⟩ : syracuseStep 2193533 = 822575) (by norm_num)
theorem B3340421 : Blo 972592 3340421 := bbase (se 4 (by rfl) ⟨313164, by rfl⟩ : syracuseStep 3340421 = 626329) (by norm_num)
theorem B2193605 : Blo 972592 2193605 := bbase (se 4 (by rfl) ⟨205650, by rfl⟩ : syracuseStep 2193605 = 411301) (by norm_num)
theorem B1407181 : Blo 972592 1407181 := bbase (se 3 (by rfl) ⟨263846, by rfl⟩ : syracuseStep 1407181 = 527693) (by norm_num)
theorem B3700997 : Blo 972592 3700997 := bbase (se 4 (by rfl) ⟨346968, by rfl⟩ : syracuseStep 3700997 = 693937) (by norm_num)
theorem B2193677 : Blo 972592 2193677 := bbase (se 3 (by rfl) ⟨411314, by rfl⟩ : syracuseStep 2193677 = 822629) (by norm_num)
theorem B2193749 : Blo 972592 2193749 := bbase (se 10 (by rfl) ⟨3213, by rfl⟩ : syracuseStep 2193749 = 6427) (by norm_num)
theorem B3340693 : Blo 972592 3340693 := bbase (se 6 (by rfl) ⟨78297, by rfl⟩ : syracuseStep 3340693 = 156595) (by norm_num)
theorem B1603997 : Blo 972592 1603997 := bbase (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) (by norm_num)
theorem B2193821 : Blo 972592 2193821 := bbase (se 3 (by rfl) ⟨411341, by rfl⟩ : syracuseStep 2193821 = 822683) (by norm_num)
theorem B2193893 : Blo 972592 2193893 := bbase (se 4 (by rfl) ⟨205677, by rfl⟩ : syracuseStep 2193893 = 411355) (by norm_num)
theorem B3701285 : Blo 972592 3701285 := bbase (se 4 (by rfl) ⟨346995, by rfl⟩ : syracuseStep 3701285 = 693991) (by norm_num)
theorem B2193965 : Blo 972592 2193965 := bbase (se 3 (by rfl) ⟨411368, by rfl⟩ : syracuseStep 2193965 = 822737) (by norm_num)
theorem B4160069 : Blo 972592 4160069 := bbase (se 4 (by rfl) ⟨390006, by rfl⟩ : syracuseStep 4160069 = 780013) (by norm_num)
theorem B2194037 : Blo 972592 2194037 := bbase (se 5 (by rfl) ⟨102845, by rfl⟩ : syracuseStep 2194037 = 205691) (by norm_num)
theorem B2194109 : Blo 972592 2194109 := bbase (se 3 (by rfl) ⟨411395, by rfl⟩ : syracuseStep 2194109 = 822791) (by norm_num)
theorem B2194181 : Blo 972592 2194181 := bbase (se 4 (by rfl) ⟨205704, by rfl⟩ : syracuseStep 2194181 = 411409) (by norm_num)
theorem B2194253 : Blo 972592 2194253 := bbase (se 3 (by rfl) ⟨411422, by rfl⟩ : syracuseStep 2194253 = 822845) (by norm_num)
theorem B1407877 : Blo 972592 1407877 := bbase (se 4 (by rfl) ⟨131988, by rfl⟩ : syracuseStep 1407877 = 263977) (by norm_num)
theorem B2194325 : Blo 972592 2194325 := bbase (se 6 (by rfl) ⟨51429, by rfl⟩ : syracuseStep 2194325 = 102859) (by norm_num)
theorem B4684709 : Blo 972592 4684709 := bbase (se 4 (by rfl) ⟨439191, by rfl⟩ : syracuseStep 4684709 = 878383) (by norm_num)
theorem B2194397 : Blo 972592 2194397 := bbase (se 3 (by rfl) ⟨411449, by rfl⟩ : syracuseStep 2194397 = 822899) (by norm_num)
theorem B2194469 : Blo 972592 2194469 := bbase (se 4 (by rfl) ⟨205731, by rfl⟩ : syracuseStep 2194469 = 411463) (by norm_num)
theorem B57736277 : Blo 972592 57736277 := bbase (se 8 (by rfl) ⟨338298, by rfl⟩ : syracuseStep 57736277 = 676597) (by norm_num)
theorem B2194541 : Blo 972592 2194541 := bbase (se 3 (by rfl) ⟨411476, by rfl⟩ : syracuseStep 2194541 = 822953) (by norm_num)
theorem B2194613 : Blo 972592 2194613 := bbase (se 5 (by rfl) ⟨102872, by rfl⟩ : syracuseStep 2194613 = 205745) (by norm_num)
theorem B1408213 : Blo 972592 1408213 := bbase (se 7 (by rfl) ⟨16502, by rfl⟩ : syracuseStep 1408213 = 33005) (by norm_num)
theorem B2194685 : Blo 972592 2194685 := bbase (se 3 (by rfl) ⟨411503, by rfl⟩ : syracuseStep 2194685 = 823007) (by norm_num)
theorem B2194757 : Blo 972592 2194757 := bbase (se 4 (by rfl) ⟨205758, by rfl⟩ : syracuseStep 2194757 = 411517) (by norm_num)
theorem B1670485 : Blo 972592 1670485 := bbase (se 11 (by rfl) ⟨1223, by rfl⟩ : syracuseStep 1670485 = 2447) (by norm_num)
theorem B2194829 : Blo 972592 2194829 := bbase (se 3 (by rfl) ⟨411530, by rfl⟩ : syracuseStep 2194829 = 823061) (by norm_num)
theorem B2194901 : Blo 972592 2194901 := bbase (se 7 (by rfl) ⟨25721, by rfl⟩ : syracuseStep 2194901 = 51443) (by norm_num)
theorem B2817557 : Blo 972592 2817557 := bbase (se 6 (by rfl) ⟨66036, by rfl⟩ : syracuseStep 2817557 = 132073) (by norm_num)
theorem B2194973 : Blo 972592 2194973 := bbase (se 3 (by rfl) ⟨411557, by rfl⟩ : syracuseStep 2194973 = 823115) (by norm_num)
theorem B4161077 : Blo 972592 4161077 := bbase (se 5 (by rfl) ⟨195050, by rfl⟩ : syracuseStep 4161077 = 390101) (by norm_num)
theorem B2195045 : Blo 972592 2195045 := bbase (se 4 (by rfl) ⟨205785, by rfl⟩ : syracuseStep 2195045 = 411571) (by norm_num)
theorem B2195117 : Blo 972592 2195117 := bbase (se 3 (by rfl) ⟨411584, by rfl⟩ : syracuseStep 2195117 = 823169) (by norm_num)
theorem B3702469 : Blo 972592 3702469 := bbase (se 4 (by rfl) ⟨347106, by rfl⟩ : syracuseStep 3702469 = 694213) (by norm_num)
theorem B2195189 : Blo 972592 2195189 := bbase (se 5 (by rfl) ⟨102899, by rfl⟩ : syracuseStep 2195189 = 205799) (by norm_num)
theorem B2195261 : Blo 972592 2195261 := bbase (se 3 (by rfl) ⟨411611, by rfl⟩ : syracuseStep 2195261 = 823223) (by norm_num)
theorem B5930837 : Blo 972592 5930837 := bbase (se 9 (by rfl) ⟨17375, by rfl⟩ : syracuseStep 5930837 = 34751) (by norm_num)
theorem B2195333 : Blo 972592 2195333 := bbase (se 4 (by rfl) ⟨205812, by rfl⟩ : syracuseStep 2195333 = 411625) (by norm_num)
theorem B2195405 : Blo 972592 2195405 := bbase (se 3 (by rfl) ⟨411638, by rfl⟩ : syracuseStep 2195405 = 823277) (by norm_num)
theorem B3702773 : Blo 972592 3702773 := bbase (se 5 (by rfl) ⟨173567, by rfl⟩ : syracuseStep 3702773 = 347135) (by norm_num)
theorem B2195459 : Blo 972592 2195459 := bstep (se 1 (by rfl) ⟨1646594, by rfl⟩ : syracuseStep 2195459 = 3293189) B3293189
theorem B1605683 : Blo 972592 1605683 := bstep (se 1 (by rfl) ⟨1204262, by rfl⟩ : syracuseStep 1605683 = 2408525) B2408525
theorem B7405667 : Blo 972592 7405667 := bstep (se 1 (by rfl) ⟨5554250, by rfl⟩ : syracuseStep 7405667 = 11108501) B11108501
theorem B2195729 : Blo 972592 2195729 := bstep (se 2 (by rfl) ⟨823398, by rfl⟩ : syracuseStep 2195729 = 1646797) B1646797
theorem B2195747 : Blo 972592 2195747 := bstep (se 1 (by rfl) ⟨1646810, by rfl⟩ : syracuseStep 2195747 = 3293621) B3293621
theorem B2196017 : Blo 972592 2196017 := bstep (se 2 (by rfl) ⟨823506, by rfl⟩ : syracuseStep 2196017 = 1647013) B1647013
theorem B1507889 : Blo 972592 1507889 := bstep (se 2 (by rfl) ⟨565458, by rfl⟩ : syracuseStep 1507889 = 1130917) B1130917
theorem B2196035 : Blo 972592 2196035 := bstep (se 1 (by rfl) ⟨1647026, by rfl⟩ : syracuseStep 2196035 = 3294053) B3294053
theorem B6587057 : Blo 972592 6587057 := bstep (se 2 (by rfl) ⟨2470146, by rfl⟩ : syracuseStep 6587057 = 4940293) B4940293
theorem B2196305 : Blo 972592 2196305 := bstep (se 2 (by rfl) ⟨823614, by rfl⟩ : syracuseStep 2196305 = 1647229) B1647229
theorem B2196323 : Blo 972592 2196323 := bstep (se 1 (by rfl) ⟨1647242, by rfl⟩ : syracuseStep 2196323 = 3294485) B3294485
theorem B3703715 : Blo 972592 3703715 := bstep (se 1 (by rfl) ⟨2777786, by rfl⟩ : syracuseStep 3703715 = 5555573) B5555573
theorem B5932003 : Blo 972592 5932003 := bstep (se 1 (by rfl) ⟨4449002, by rfl⟩ : syracuseStep 5932003 = 8898005) B8898005
theorem B3376163 : Blo 972592 3376163 := bstep (se 1 (by rfl) ⟨2532122, by rfl⟩ : syracuseStep 3376163 = 5064245) B5064245
theorem B2196593 : Blo 972592 2196593 := bstep (se 2 (by rfl) ⟨823722, by rfl⟩ : syracuseStep 2196593 = 1647445) B1647445
theorem B2196611 : Blo 972592 2196611 := bstep (se 1 (by rfl) ⟨1647458, by rfl⟩ : syracuseStep 2196611 = 3294917) B3294917
theorem B7013573 : Blo 972592 7013573 := bstep (se 4 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 7013573 = 1315045) B1315045
theorem B2196881 : Blo 972592 2196881 := bstep (se 2 (by rfl) ⟨823830, by rfl⟩ : syracuseStep 2196881 = 1647661) B1647661
theorem B2196899 : Blo 972592 2196899 := bstep (se 1 (by rfl) ⟨1647674, by rfl⟩ : syracuseStep 2196899 = 3295349) B3295349
theorem B5277197 : Blo 972592 5277197 := bstep (se 3 (by rfl) ⟨989474, by rfl⟩ : syracuseStep 5277197 = 1978949) B1978949
theorem B2197169 : Blo 972592 2197169 := bstep (se 2 (by rfl) ⟨823938, by rfl⟩ : syracuseStep 2197169 = 1647877) B1647877
theorem B2197187 : Blo 972592 2197187 := bstep (se 1 (by rfl) ⟨1647890, by rfl⟩ : syracuseStep 2197187 = 3295781) B3295781
theorem B3704717 : Blo 972592 3704717 := bstep (se 3 (by rfl) ⟨694634, by rfl⟩ : syracuseStep 3704717 = 1389269) B1389269
theorem B5539853 : Blo 972592 5539853 := bstep (se 3 (by rfl) ⟨1038722, by rfl⟩ : syracuseStep 5539853 = 2077445) B2077445
theorem B7112717 : Blo 972592 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B2885905 : Blo 972592 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B8325773 : Blo 972592 8325773 := bstep (se 3 (by rfl) ⟨1561082, by rfl⟩ : syracuseStep 8325773 = 3122165) B3122165
theorem B4164493 : Blo 972592 4164493 := bstep (se 3 (by rfl) ⟨780842, by rfl⟩ : syracuseStep 4164493 = 1561685) B1561685
theorem B1641377 : Blo 972592 1641377 := bstep (se 2 (by rfl) ⟨615516, by rfl⟩ : syracuseStep 1641377 = 1231033) B1231033
theorem B1641505 : Blo 972592 1641505 := bstep (se 2 (by rfl) ⟨615564, by rfl⟩ : syracuseStep 1641505 = 1231129) B1231129
theorem B1641539 : Blo 972592 1641539 := bstep (se 1 (by rfl) ⟨1231154, by rfl⟩ : syracuseStep 1641539 = 2462309) B2462309
theorem B3116195 : Blo 972592 3116195 := bstep (se 1 (by rfl) ⟨2337146, by rfl⟩ : syracuseStep 3116195 = 4674293) B4674293
theorem B1641667 : Blo 972592 1641667 := bstep (se 1 (by rfl) ⟨1231250, by rfl⟩ : syracuseStep 1641667 = 2462501) B2462501
theorem B1641809 : Blo 972592 1641809 := bstep (se 2 (by rfl) ⟨615678, by rfl⟩ : syracuseStep 1641809 = 1231357) B1231357
theorem B3116465 : Blo 972592 3116465 := bstep (se 2 (by rfl) ⟨1168674, by rfl⟩ : syracuseStep 3116465 = 2337349) B2337349
theorem B1641937 : Blo 972592 1641937 := bstep (se 2 (by rfl) ⟨615726, by rfl⟩ : syracuseStep 1641937 = 1231453) B1231453
theorem B1641971 : Blo 972592 1641971 := bstep (se 1 (by rfl) ⟨1231478, by rfl⟩ : syracuseStep 1641971 = 2462957) B2462957
theorem B1642099 : Blo 972592 1642099 := bstep (se 1 (by rfl) ⟨1231574, by rfl⟩ : syracuseStep 1642099 = 2463149) B2463149
theorem B986851 : Blo 972592 986851 := bstep (se 1 (by rfl) ⟨740138, by rfl⟩ : syracuseStep 986851 = 1480277) B1480277
theorem B1642241 : Blo 972592 1642241 := bstep (se 2 (by rfl) ⟨615840, by rfl⟩ : syracuseStep 1642241 = 1231681) B1231681
theorem B1642369 : Blo 972592 1642369 := bstep (se 2 (by rfl) ⟨615888, by rfl⟩ : syracuseStep 1642369 = 1231777) B1231777
theorem B1314721 : Blo 972592 1314721 := bstep (se 2 (by rfl) ⟨493020, by rfl⟩ : syracuseStep 1314721 = 986041) B986041
theorem B1642403 : Blo 972592 1642403 := bstep (se 1 (by rfl) ⟨1231802, by rfl⟩ : syracuseStep 1642403 = 2463605) B2463605
theorem B3706829 : Blo 972592 3706829 := bstep (se 3 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 3706829 = 1390061) B1390061
theorem B1642531 : Blo 972592 1642531 := bstep (se 1 (by rfl) ⟨1231898, by rfl⟩ : syracuseStep 1642531 = 2463797) B2463797
theorem B7901297 : Blo 972592 7901297 := bstep (se 2 (by rfl) ⟨2962986, by rfl⟩ : syracuseStep 7901297 = 5925973) B5925973
theorem B1642673 : Blo 972592 1642673 := bstep (se 2 (by rfl) ⟨616002, by rfl⟩ : syracuseStep 1642673 = 1232005) B1232005
theorem B1478915 : Blo 972592 1478915 := bstep (se 1 (by rfl) ⟨1109186, by rfl⟩ : syracuseStep 1478915 = 2218373) B2218373
theorem B1642801 : Blo 972592 1642801 := bstep (se 2 (by rfl) ⟨616050, by rfl⟩ : syracuseStep 1642801 = 1232101) B1232101
theorem B1642835 : Blo 972592 1642835 := bstep (se 1 (by rfl) ⟨1232126, by rfl⟩ : syracuseStep 1642835 = 2464253) B2464253
theorem B2462147 : Blo 972592 2462147 := bstep (se 1 (by rfl) ⟨1846610, by rfl⟩ : syracuseStep 2462147 = 3693221) B3693221
theorem B1872323 : Blo 972592 1872323 := bstep (se 1 (by rfl) ⟨1404242, by rfl⟩ : syracuseStep 1872323 = 2808485) B2808485
theorem B1642963 : Blo 972592 1642963 := bstep (se 1 (by rfl) ⟨1232222, by rfl⟩ : syracuseStep 1642963 = 2464445) B2464445
theorem B1643105 : Blo 972592 1643105 := bstep (se 2 (by rfl) ⟨616164, by rfl⟩ : syracuseStep 1643105 = 1232329) B1232329
theorem B2462339 : Blo 972592 2462339 := bstep (se 1 (by rfl) ⟨1846754, by rfl⟩ : syracuseStep 2462339 = 3693509) B3693509
theorem B1643233 : Blo 972592 1643233 := bstep (se 2 (by rfl) ⟨616212, by rfl⟩ : syracuseStep 1643233 = 1232425) B1232425
theorem B6099697 : Blo 972592 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B3707633 : Blo 972592 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B1643267 : Blo 972592 1643267 := bstep (se 1 (by rfl) ⟨1232450, by rfl⟩ : syracuseStep 1643267 = 2464901) B2464901
theorem B5542769 : Blo 972592 5542769 := bstep (se 2 (by rfl) ⟨2078538, by rfl⟩ : syracuseStep 5542769 = 4157077) B4157077
theorem B1643395 : Blo 972592 1643395 := bstep (se 1 (by rfl) ⟨1232546, by rfl⟩ : syracuseStep 1643395 = 2465093) B2465093
theorem B1643537 : Blo 972592 1643537 := bstep (se 2 (by rfl) ⟨616326, by rfl⟩ : syracuseStep 1643537 = 1232653) B1232653
theorem B1643665 : Blo 972592 1643665 := bstep (se 2 (by rfl) ⟨616374, by rfl⟩ : syracuseStep 1643665 = 1232749) B1232749
theorem B1643699 : Blo 972592 1643699 := bstep (se 1 (by rfl) ⟨1232774, by rfl⟩ : syracuseStep 1643699 = 2465549) B2465549
theorem B1643827 : Blo 972592 1643827 := bstep (se 1 (by rfl) ⟨1232870, by rfl⟩ : syracuseStep 1643827 = 2465741) B2465741
theorem B7411013 : Blo 972592 7411013 := bstep (se 4 (by rfl) ⟨694782, by rfl⟩ : syracuseStep 7411013 = 1389565) B1389565
theorem B1643969 : Blo 972592 1643969 := bstep (se 2 (by rfl) ⟨616488, by rfl⟩ : syracuseStep 1643969 = 1232977) B1232977
theorem B2463281 : Blo 972592 2463281 := bstep (se 2 (by rfl) ⟨923730, by rfl⟩ : syracuseStep 2463281 = 1847461) B1847461
theorem B1480241 : Blo 972592 1480241 := bstep (se 2 (by rfl) ⟨555090, by rfl⟩ : syracuseStep 1480241 = 1110181) B1110181
theorem B1644097 : Blo 972592 1644097 := bstep (se 2 (by rfl) ⟨616536, by rfl⟩ : syracuseStep 1644097 = 1233073) B1233073
theorem B2463331 : Blo 972592 2463331 := bstep (se 1 (by rfl) ⟨1847498, by rfl⟩ : syracuseStep 2463331 = 3694997) B3694997
theorem B1644131 : Blo 972592 1644131 := bstep (se 1 (by rfl) ⟨1233098, by rfl⟩ : syracuseStep 1644131 = 2466197) B2466197
theorem B3282605 : Blo 972592 3282605 := bstep (se 3 (by rfl) ⟨615488, by rfl⟩ : syracuseStep 3282605 = 1230977) B1230977
theorem B3282659 : Blo 972592 3282659 := bstep (se 1 (by rfl) ⟨2461994, by rfl⟩ : syracuseStep 3282659 = 4923989) B4923989
theorem B1644259 : Blo 972592 1644259 := bstep (se 1 (by rfl) ⟨1233194, by rfl⟩ : syracuseStep 1644259 = 2466389) B2466389
theorem B2463473 : Blo 972592 2463473 := bstep (se 2 (by rfl) ⟨923802, by rfl⟩ : syracuseStep 2463473 = 1847605) B1847605
theorem B3118925 : Blo 972592 3118925 := bstep (se 3 (by rfl) ⟨584798, by rfl⟩ : syracuseStep 3118925 = 1169597) B1169597
theorem B1644401 : Blo 972592 1644401 := bstep (se 2 (by rfl) ⟨616650, by rfl⟩ : syracuseStep 1644401 = 1233301) B1233301
theorem B3282929 : Blo 972592 3282929 := bstep (se 2 (by rfl) ⟨1231098, by rfl⟩ : syracuseStep 3282929 = 2462197) B2462197
theorem B1644529 : Blo 972592 1644529 := bstep (se 2 (by rfl) ⟨616698, by rfl⟩ : syracuseStep 1644529 = 1233397) B1233397
theorem B1644563 : Blo 972592 1644563 := bstep (se 1 (by rfl) ⟨1233422, by rfl⟩ : syracuseStep 1644563 = 2466845) B2466845
theorem B21043313 : Blo 972592 21043313 := bstep (se 2 (by rfl) ⟨7891242, by rfl⟩ : syracuseStep 21043313 = 15782485) B15782485
theorem B1644691 : Blo 972592 1644691 := bstep (se 1 (by rfl) ⟨1233518, by rfl⟩ : syracuseStep 1644691 = 2467037) B2467037
theorem B3512483 : Blo 972592 3512483 := bstep (se 1 (by rfl) ⟨2634362, by rfl⟩ : syracuseStep 3512483 = 5268725) B5268725
theorem B14063813 : Blo 972592 14063813 := bstep (se 4 (by rfl) ⟨1318482, by rfl⟩ : syracuseStep 14063813 = 2636965) B2636965
theorem B16849093 : Blo 972592 16849093 := bstep (se 4 (by rfl) ⟨1579602, by rfl⟩ : syracuseStep 16849093 = 3159205) B3159205
theorem B989443 : Blo 972592 989443 := bstep (se 1 (by rfl) ⟨742082, by rfl⟩ : syracuseStep 989443 = 1484165) B1484165
theorem B1644833 : Blo 972592 1644833 := bstep (se 2 (by rfl) ⟨616812, by rfl⟩ : syracuseStep 1644833 = 1233625) B1233625
theorem B5544227 : Blo 972592 5544227 := bstep (se 1 (by rfl) ⟨4158170, by rfl⟩ : syracuseStep 5544227 = 8316341) B8316341
theorem B1644961 : Blo 972592 1644961 := bstep (se 2 (by rfl) ⟨616860, by rfl⟩ : syracuseStep 1644961 = 1233721) B1233721
theorem B1972657 : Blo 972592 1972657 := bstep (se 2 (by rfl) ⟨739746, by rfl⟩ : syracuseStep 1972657 = 1479493) B1479493
theorem B1644995 : Blo 972592 1644995 := bstep (se 1 (by rfl) ⟨1233746, by rfl⟩ : syracuseStep 1644995 = 2467493) B2467493
theorem B3283469 : Blo 972592 3283469 := bstep (se 3 (by rfl) ⟨615650, by rfl⟩ : syracuseStep 3283469 = 1231301) B1231301
theorem B3283523 : Blo 972592 3283523 := bstep (se 1 (by rfl) ⟨2462642, by rfl⟩ : syracuseStep 3283523 = 4925285) B4925285
theorem B1645123 : Blo 972592 1645123 := bstep (se 1 (by rfl) ⟨1233842, by rfl⟩ : syracuseStep 1645123 = 2467685) B2467685
theorem B2464465 : Blo 972592 2464465 := bstep (se 2 (by rfl) ⟨924174, by rfl⟩ : syracuseStep 2464465 = 1848349) B1848349
theorem B1645265 : Blo 972592 1645265 := bstep (se 2 (by rfl) ⟨616974, by rfl⟩ : syracuseStep 1645265 = 1233949) B1233949
theorem B3283793 : Blo 972592 3283793 := bstep (se 2 (by rfl) ⟨1231422, by rfl⟩ : syracuseStep 3283793 = 2462845) B2462845
theorem B1645393 : Blo 972592 1645393 := bstep (se 2 (by rfl) ⟨617022, by rfl⟩ : syracuseStep 1645393 = 1234045) B1234045
theorem B1645427 : Blo 972592 1645427 := bstep (se 1 (by rfl) ⟨1234070, by rfl⟩ : syracuseStep 1645427 = 2468141) B2468141
theorem B6331277 : Blo 972592 6331277 := bstep (se 3 (by rfl) ⟨1187114, by rfl⟩ : syracuseStep 6331277 = 2374229) B2374229
theorem B2464739 : Blo 972592 2464739 := bstep (se 1 (by rfl) ⟨1848554, by rfl⟩ : syracuseStep 2464739 = 3697109) B3697109
theorem B1645555 : Blo 972592 1645555 := bstep (se 1 (by rfl) ⟨1234166, by rfl⟩ : syracuseStep 1645555 = 2468333) B2468333
theorem B4168817 : Blo 972592 4168817 := bstep (se 2 (by rfl) ⟨1563306, by rfl⟩ : syracuseStep 4168817 = 3126613) B3126613
theorem B1645697 : Blo 972592 1645697 := bstep (se 2 (by rfl) ⟨617136, by rfl⟩ : syracuseStep 1645697 = 1234273) B1234273
theorem B1973411 : Blo 972592 1973411 := bstep (se 1 (by rfl) ⟨1480058, by rfl⟩ : syracuseStep 1973411 = 2960117) B2960117
theorem B2464931 : Blo 972592 2464931 := bstep (se 1 (by rfl) ⟨1848698, by rfl⟩ : syracuseStep 2464931 = 3697397) B3697397
theorem B4168867 : Blo 972592 4168867 := bstep (se 1 (by rfl) ⟨3126650, by rfl⟩ : syracuseStep 4168867 = 6253301) B6253301
theorem B1973443 : Blo 972592 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B1645825 : Blo 972592 1645825 := bstep (se 2 (by rfl) ⟨617184, by rfl⟩ : syracuseStep 1645825 = 1234369) B1234369
theorem B1645859 : Blo 972592 1645859 := bstep (se 1 (by rfl) ⟨1234394, by rfl⟩ : syracuseStep 1645859 = 2468789) B2468789
theorem B3284333 : Blo 972592 3284333 := bstep (se 3 (by rfl) ⟨615812, by rfl⟩ : syracuseStep 3284333 = 1231625) B1231625
theorem B2006417 : Blo 972592 2006417 := bstep (se 2 (by rfl) ⟨752406, by rfl⟩ : syracuseStep 2006417 = 1504813) B1504813
theorem B3284387 : Blo 972592 3284387 := bstep (se 1 (by rfl) ⟨2463290, by rfl⟩ : syracuseStep 3284387 = 4926581) B4926581
theorem B6659491 : Blo 972592 6659491 := bstep (se 1 (by rfl) ⟨4994618, by rfl⟩ : syracuseStep 6659491 = 9989237) B9989237
theorem B1645987 : Blo 972592 1645987 := bstep (se 1 (by rfl) ⟨1234490, by rfl⟩ : syracuseStep 1645987 = 2468981) B2468981
theorem B1646129 : Blo 972592 1646129 := bstep (se 2 (by rfl) ⟨617298, by rfl⟩ : syracuseStep 1646129 = 1234597) B1234597
theorem B2530883 : Blo 972592 2530883 := bstep (se 1 (by rfl) ⟨1898162, by rfl⟩ : syracuseStep 2530883 = 3796325) B3796325
theorem B6233669 : Blo 972592 6233669 := bstep (se 4 (by rfl) ⟨584406, by rfl⟩ : syracuseStep 6233669 = 1168813) B1168813
theorem B3120781 : Blo 972592 3120781 := bstep (se 3 (by rfl) ⟨585146, by rfl⟩ : syracuseStep 3120781 = 1170293) B1170293
theorem B3284657 : Blo 972592 3284657 := bstep (se 2 (by rfl) ⟨1231746, by rfl⟩ : syracuseStep 3284657 = 2463493) B2463493
theorem B1646257 : Blo 972592 1646257 := bstep (se 2 (by rfl) ⟨617346, by rfl⟩ : syracuseStep 1646257 = 1234693) B1234693
theorem B1646291 : Blo 972592 1646291 := bstep (se 1 (by rfl) ⟨1234718, by rfl⟩ : syracuseStep 1646291 = 2469437) B2469437
theorem B1646419 : Blo 972592 1646419 := bstep (se 1 (by rfl) ⟨1234814, by rfl⟩ : syracuseStep 1646419 = 2469629) B2469629
theorem B3514225 : Blo 972592 3514225 := bstep (se 2 (by rfl) ⟨1317834, by rfl⟩ : syracuseStep 3514225 = 2635669) B2635669
theorem B1646561 : Blo 972592 1646561 := bstep (se 2 (by rfl) ⟨617460, by rfl⟩ : syracuseStep 1646561 = 1234921) B1234921
theorem B1318915 : Blo 972592 1318915 := bstep (se 1 (by rfl) ⟨989186, by rfl⟩ : syracuseStep 1318915 = 1978373) B1978373
theorem B2465873 : Blo 972592 2465873 := bstep (se 2 (by rfl) ⟨924702, by rfl⟩ : syracuseStep 2465873 = 1849405) B1849405
theorem B1646689 : Blo 972592 1646689 := bstep (se 2 (by rfl) ⟨617508, by rfl⟩ : syracuseStep 1646689 = 1235017) B1235017
theorem B2465923 : Blo 972592 2465923 := bstep (se 1 (by rfl) ⟨1849442, by rfl⟩ : syracuseStep 2465923 = 3698885) B3698885
theorem B1646723 : Blo 972592 1646723 := bstep (se 1 (by rfl) ⟨1235042, by rfl⟩ : syracuseStep 1646723 = 2470085) B2470085
theorem B1974449 : Blo 972592 1974449 := bstep (se 2 (by rfl) ⟨740418, by rfl⟩ : syracuseStep 1974449 = 1480837) B1480837
theorem B3285197 : Blo 972592 3285197 := bstep (se 3 (by rfl) ⟨615974, by rfl⟩ : syracuseStep 3285197 = 1231949) B1231949
theorem B1056979 : Blo 972592 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B3285251 : Blo 972592 3285251 := bstep (se 1 (by rfl) ⟨2463938, by rfl⟩ : syracuseStep 3285251 = 4927877) B4927877
theorem B1646851 : Blo 972592 1646851 := bstep (se 1 (by rfl) ⟨1235138, by rfl⟩ : syracuseStep 1646851 = 2470277) B2470277
theorem B2466065 : Blo 972592 2466065 := bstep (se 2 (by rfl) ⟨924774, by rfl⟩ : syracuseStep 2466065 = 1849549) B1849549
theorem B1876241 : Blo 972592 1876241 := bstep (se 2 (by rfl) ⟨703590, by rfl⟩ : syracuseStep 1876241 = 1407181) B1407181
theorem B7119173 : Blo 972592 7119173 := bstep (se 4 (by rfl) ⟨667422, by rfl⟩ : syracuseStep 7119173 = 1334845) B1334845
theorem B1646993 : Blo 972592 1646993 := bstep (se 2 (by rfl) ⟨617622, by rfl⟩ : syracuseStep 1646993 = 1235245) B1235245
theorem B1384867 : Blo 972592 1384867 := bstep (se 1 (by rfl) ⟨1038650, by rfl⟩ : syracuseStep 1384867 = 2077301) B2077301
theorem B3285521 : Blo 972592 3285521 := bstep (se 2 (by rfl) ⟨1232070, by rfl⟩ : syracuseStep 3285521 = 2464141) B2464141
theorem B1647121 : Blo 972592 1647121 := bstep (se 2 (by rfl) ⟨617670, by rfl⟩ : syracuseStep 1647121 = 1235341) B1235341
theorem B1647155 : Blo 972592 1647155 := bstep (se 1 (by rfl) ⟨1235366, by rfl⟩ : syracuseStep 1647155 = 2470733) B2470733
theorem B3744397 : Blo 972592 3744397 := bstep (se 3 (by rfl) ⟨702074, by rfl⟩ : syracuseStep 3744397 = 1404149) B1404149
theorem B1647283 : Blo 972592 1647283 := bstep (se 1 (by rfl) ⟨1235462, by rfl⟩ : syracuseStep 1647283 = 2470925) B2470925
theorem B1385203 : Blo 972592 1385203 := bstep (se 1 (by rfl) ⟨1038902, by rfl⟩ : syracuseStep 1385203 = 2077805) B2077805
theorem B1647425 : Blo 972592 1647425 := bstep (se 2 (by rfl) ⟨617784, by rfl⟩ : syracuseStep 1647425 = 1235569) B1235569
theorem B1647553 : Blo 972592 1647553 := bstep (se 2 (by rfl) ⟨617832, by rfl⟩ : syracuseStep 1647553 = 1235665) B1235665
theorem B1647587 : Blo 972592 1647587 := bstep (se 1 (by rfl) ⟨1235690, by rfl⟩ : syracuseStep 1647587 = 2471381) B2471381
theorem B3286061 : Blo 972592 3286061 := bstep (se 3 (by rfl) ⟨616136, by rfl⟩ : syracuseStep 3286061 = 1232273) B1232273
theorem B2630737 : Blo 972592 2630737 := bstep (se 2 (by rfl) ⟨986526, by rfl⟩ : syracuseStep 2630737 = 1973053) B1973053
theorem B3286115 : Blo 972592 3286115 := bstep (se 1 (by rfl) ⟨2464586, by rfl⟩ : syracuseStep 3286115 = 4929173) B4929173
theorem B1647715 : Blo 972592 1647715 := bstep (se 1 (by rfl) ⟨1235786, by rfl⟩ : syracuseStep 1647715 = 2471573) B2471573
theorem B2467057 : Blo 972592 2467057 := bstep (se 2 (by rfl) ⟨925146, by rfl⟩ : syracuseStep 2467057 = 1850293) B1850293
theorem B1647857 : Blo 972592 1647857 := bstep (se 2 (by rfl) ⟨617946, by rfl⟩ : syracuseStep 1647857 = 1235893) B1235893
theorem B1385761 : Blo 972592 1385761 := bstep (se 2 (by rfl) ⟨519660, by rfl⟩ : syracuseStep 1385761 = 1039321) B1039321
theorem B1385795 : Blo 972592 1385795 := bstep (se 1 (by rfl) ⟨1039346, by rfl⟩ : syracuseStep 1385795 = 2078693) B2078693
theorem B3122513 : Blo 972592 3122513 := bstep (se 2 (by rfl) ⟨1170942, by rfl⟩ : syracuseStep 3122513 = 2341885) B2341885
theorem B3286385 : Blo 972592 3286385 := bstep (se 2 (by rfl) ⟨1232394, by rfl⟩ : syracuseStep 3286385 = 2464789) B2464789
theorem B1647985 : Blo 972592 1647985 := bstep (se 2 (by rfl) ⟨617994, by rfl⟩ : syracuseStep 1647985 = 1235989) B1235989
theorem B3515825 : Blo 972592 3515825 := bstep (se 2 (by rfl) ⟨1318434, by rfl⟩ : syracuseStep 3515825 = 2636869) B2636869
theorem B19998179 : Blo 972592 19998179 := bstep (se 1 (by rfl) ⟨14998634, by rfl⟩ : syracuseStep 19998179 = 29997269) B29997269
theorem B2467331 : Blo 972592 2467331 := bstep (se 1 (by rfl) ⟨1850498, by rfl⟩ : syracuseStep 2467331 = 3700997) B3700997
theorem B4171277 : Blo 972592 4171277 := bstep (se 3 (by rfl) ⟨782114, by rfl⟩ : syracuseStep 4171277 = 1564229) B1564229
theorem B1877617 : Blo 972592 1877617 := bstep (se 2 (by rfl) ⟨704106, by rfl⟩ : syracuseStep 1877617 = 1408213) B1408213
theorem B2467523 : Blo 972592 2467523 := bstep (se 1 (by rfl) ⟨1850642, by rfl⟩ : syracuseStep 2467523 = 3701285) B3701285
theorem B4007693 : Blo 972592 4007693 := bstep (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) B1502885
theorem B3516173 : Blo 972592 3516173 := bstep (se 3 (by rfl) ⟨659282, by rfl⟩ : syracuseStep 3516173 = 1318565) B1318565
theorem B1386353 : Blo 972592 1386353 := bstep (se 2 (by rfl) ⟨519882, by rfl⟩ : syracuseStep 1386353 = 1039765) B1039765
theorem B3286925 : Blo 972592 3286925 := bstep (se 3 (by rfl) ⟨616298, by rfl⟩ : syracuseStep 3286925 = 1232597) B1232597
theorem B1386433 : Blo 972592 1386433 := bstep (se 2 (by rfl) ⟨519912, by rfl⟩ : syracuseStep 1386433 = 1039825) B1039825
theorem B3286979 : Blo 972592 3286979 := bstep (se 1 (by rfl) ⟨2465234, by rfl⟩ : syracuseStep 3286979 = 4930469) B4930469
theorem B3123139 : Blo 972592 3123139 := bstep (se 1 (by rfl) ⟨2342354, by rfl⟩ : syracuseStep 3123139 = 4684709) B4684709
theorem B6334469 : Blo 972592 6334469 := bstep (se 4 (by rfl) ⟨593856, by rfl⟩ : syracuseStep 6334469 = 1187713) B1187713
theorem B8890565 : Blo 972592 8890565 := bstep (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) B1666981
theorem B3287249 : Blo 972592 3287249 := bstep (se 2 (by rfl) ⟨1232718, by rfl⟩ : syracuseStep 3287249 = 2465437) B2465437
theorem B1878371 : Blo 972592 1878371 := bstep (se 1 (by rfl) ⟨1408778, by rfl⟩ : syracuseStep 1878371 = 2817557) B2817557
theorem B8333837 : Blo 972592 8333837 := bstep (se 3 (by rfl) ⟨1562594, by rfl⟩ : syracuseStep 8333837 = 3125189) B3125189
theorem B2468465 : Blo 972592 2468465 := bstep (se 2 (by rfl) ⟨925674, by rfl⟩ : syracuseStep 2468465 = 1851349) B1851349
theorem B2337425 : Blo 972592 2337425 := bstep (se 2 (by rfl) ⟨876534, by rfl⟩ : syracuseStep 2337425 = 1753069) B1753069
theorem B2468515 : Blo 972592 2468515 := bstep (se 1 (by rfl) ⟨1851386, by rfl⟩ : syracuseStep 2468515 = 3702773) B3702773
theorem B1387219 : Blo 972592 1387219 := bstep (se 1 (by rfl) ⟨1040414, by rfl⟩ : syracuseStep 1387219 = 2080829) B2080829
theorem B3287789 : Blo 972592 3287789 := bstep (se 3 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 3287789 = 1232921) B1232921
theorem B3287843 : Blo 972592 3287843 := bstep (se 1 (by rfl) ⟨2465882, by rfl⟩ : syracuseStep 3287843 = 4931765) B4931765
theorem B4926257 : Blo 972592 4926257 := bstep (se 2 (by rfl) ⟨1847346, by rfl⟩ : syracuseStep 4926257 = 3694693) B3694693
theorem B2468657 : Blo 972592 2468657 := bstep (se 2 (by rfl) ⟨925746, by rfl⟩ : syracuseStep 2468657 = 1851493) B1851493
theorem B1878833 : Blo 972592 1878833 := bstep (se 2 (by rfl) ⟨704562, by rfl⟩ : syracuseStep 1878833 = 1409125) B1409125
theorem B2501489 : Blo 972592 2501489 := bstep (se 2 (by rfl) ⟨938058, by rfl⟩ : syracuseStep 2501489 = 1876117) B1876117
theorem B6237233 : Blo 972592 6237233 := bstep (se 2 (by rfl) ⟨2338962, by rfl⟩ : syracuseStep 6237233 = 4677925) B4677925
theorem B3288113 : Blo 972592 3288113 := bstep (se 2 (by rfl) ⟨1233042, by rfl⟩ : syracuseStep 3288113 = 2466085) B2466085
theorem B3124369 : Blo 972592 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B1387697 : Blo 972592 1387697 := bstep (se 2 (by rfl) ⟨520386, by rfl⟩ : syracuseStep 1387697 = 1040773) B1040773
theorem B1387811 : Blo 972592 1387811 := bstep (se 1 (by rfl) ⟨1040858, by rfl⟩ : syracuseStep 1387811 = 2081717) B2081717
theorem B1387891 : Blo 972592 1387891 := bstep (se 1 (by rfl) ⟨1040918, by rfl⟩ : syracuseStep 1387891 = 2081837) B2081837
theorem B3288653 : Blo 972592 3288653 := bstep (se 3 (by rfl) ⟨616622, by rfl⟩ : syracuseStep 3288653 = 1233245) B1233245
theorem B3518029 : Blo 972592 3518029 := bstep (se 3 (by rfl) ⟨659630, by rfl⟩ : syracuseStep 3518029 = 1319261) B1319261
theorem B3288707 : Blo 972592 3288707 := bstep (se 1 (by rfl) ⟨2466530, by rfl⟩ : syracuseStep 3288707 = 4933061) B4933061
theorem B2633411 : Blo 972592 2633411 := bstep (se 1 (by rfl) ⟨1975058, by rfl⟩ : syracuseStep 2633411 = 3950117) B3950117
theorem B3124973 : Blo 972592 3124973 := bstep (se 3 (by rfl) ⟨585932, by rfl⟩ : syracuseStep 3124973 = 1171865) B1171865
theorem B2961137 : Blo 972592 2961137 := bstep (se 2 (by rfl) ⟨1110426, by rfl⟩ : syracuseStep 2961137 = 2220853) B2220853
theorem B2469649 : Blo 972592 2469649 := bstep (se 2 (by rfl) ⟨926118, by rfl⟩ : syracuseStep 2469649 = 1852237) B1852237
theorem B3288977 : Blo 972592 3288977 := bstep (se 2 (by rfl) ⟨1233366, by rfl⟩ : syracuseStep 3288977 = 2466733) B2466733
theorem B1388449 : Blo 972592 1388449 := bstep (se 2 (by rfl) ⟨520668, by rfl⟩ : syracuseStep 1388449 = 1041337) B1041337
theorem B2469923 : Blo 972592 2469923 := bstep (se 1 (by rfl) ⟨1852442, by rfl⟩ : syracuseStep 2469923 = 3704885) B3704885
theorem B1847377 : Blo 972592 1847377 := bstep (se 2 (by rfl) ⟨692766, by rfl⟩ : syracuseStep 1847377 = 1385533) B1385533
theorem B2633809 : Blo 972592 2633809 := bstep (se 2 (by rfl) ⟨987678, by rfl⟩ : syracuseStep 2633809 = 1975357) B1975357
theorem B4927715 : Blo 972592 4927715 := bstep (se 1 (by rfl) ⟨3695786, by rfl⟩ : syracuseStep 4927715 = 7391573) B7391573
theorem B2470115 : Blo 972592 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B2961809 : Blo 972592 2961809 := bstep (se 2 (by rfl) ⟨1110678, by rfl⟩ : syracuseStep 2961809 = 2221357) B2221357
theorem B3289517 : Blo 972592 3289517 := bstep (se 3 (by rfl) ⟨616784, by rfl⟩ : syracuseStep 3289517 = 1233569) B1233569
theorem B6238691 : Blo 972592 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B3289571 : Blo 972592 3289571 := bstep (se 1 (by rfl) ⟨2467178, by rfl⟩ : syracuseStep 3289571 = 4934357) B4934357
theorem B1094179 : Blo 972592 1094179 := bstep (se 1 (by rfl) ⟨820634, by rfl⟩ : syracuseStep 1094179 = 1641269) B1641269
theorem B1389155 : Blo 972592 1389155 := bstep (se 1 (by rfl) ⟨1041866, by rfl⟩ : syracuseStep 1389155 = 2083733) B2083733
theorem B7385741 : Blo 972592 7385741 := bstep (se 3 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 7385741 = 2769653) B2769653
theorem B1094323 : Blo 972592 1094323 := bstep (se 1 (by rfl) ⟨820742, by rfl⟩ : syracuseStep 1094323 = 1641485) B1641485
theorem B3289841 : Blo 972592 3289841 := bstep (se 2 (by rfl) ⟨1233690, by rfl⟩ : syracuseStep 3289841 = 2467381) B2467381
theorem B2634545 : Blo 972592 2634545 := bstep (se 2 (by rfl) ⟨987954, by rfl⟩ : syracuseStep 2634545 = 1975909) B1975909
theorem B1094467 : Blo 972592 1094467 := bstep (se 1 (by rfl) ⟨820850, by rfl⟩ : syracuseStep 1094467 = 1641701) B1641701
theorem B2667377 : Blo 972592 2667377 := bstep (se 2 (by rfl) ⟨1000266, by rfl⟩ : syracuseStep 2667377 = 2000533) B2000533
theorem B2339779 : Blo 972592 2339779 := bstep (se 1 (by rfl) ⟨1754834, by rfl⟩ : syracuseStep 2339779 = 3509669) B3509669
theorem B1094611 : Blo 972592 1094611 := bstep (se 1 (by rfl) ⟨820958, by rfl⟩ : syracuseStep 1094611 = 1641917) B1641917
theorem B4928525 : Blo 972592 4928525 := bstep (se 3 (by rfl) ⟨924098, by rfl⟩ : syracuseStep 4928525 = 1848197) B1848197
theorem B1094755 : Blo 972592 1094755 := bstep (se 1 (by rfl) ⟨821066, by rfl⟩ : syracuseStep 1094755 = 1642133) B1642133
theorem B1848433 : Blo 972592 1848433 := bstep (se 2 (by rfl) ⟨693162, by rfl⟩ : syracuseStep 1848433 = 1386325) B1386325
theorem B2471057 : Blo 972592 2471057 := bstep (se 2 (by rfl) ⟨926646, by rfl⟩ : syracuseStep 2471057 = 1853293) B1853293
theorem B2471107 : Blo 972592 2471107 := bstep (se 1 (by rfl) ⟨1853330, by rfl⟩ : syracuseStep 2471107 = 3706661) B3706661
theorem B1389793 : Blo 972592 1389793 := bstep (se 2 (by rfl) ⟨521172, by rfl⟩ : syracuseStep 1389793 = 1042345) B1042345
theorem B1094899 : Blo 972592 1094899 := bstep (se 1 (by rfl) ⟨821174, by rfl⟩ : syracuseStep 1094899 = 1642349) B1642349
theorem B11253005 : Blo 972592 11253005 := bstep (se 3 (by rfl) ⟨2109938, by rfl⟩ : syracuseStep 11253005 = 4219877) B4219877
theorem B3290381 : Blo 972592 3290381 := bstep (se 3 (by rfl) ⟨616946, by rfl⟩ : syracuseStep 3290381 = 1233893) B1233893
theorem B3290435 : Blo 972592 3290435 := bstep (se 1 (by rfl) ⟨2467826, by rfl⟩ : syracuseStep 3290435 = 4935653) B4935653
theorem B4437325 : Blo 972592 4437325 := bstep (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) B1663997
theorem B2471249 : Blo 972592 2471249 := bstep (se 2 (by rfl) ⟨926718, by rfl⟩ : syracuseStep 2471249 = 1853437) B1853437
theorem B1389907 : Blo 972592 1389907 := bstep (se 1 (by rfl) ⟨1042430, by rfl⟩ : syracuseStep 1389907 = 2084861) B2084861
theorem B1095043 : Blo 972592 1095043 := bstep (se 1 (by rfl) ⟨821282, by rfl⟩ : syracuseStep 1095043 = 1642565) B1642565
theorem B2635139 : Blo 972592 2635139 := bstep (se 1 (by rfl) ⟨1976354, by rfl⟩ : syracuseStep 2635139 = 3952709) B3952709
theorem B2078129 : Blo 972592 2078129 := bstep (se 2 (by rfl) ⟨779298, by rfl⟩ : syracuseStep 2078129 = 1558597) B1558597
theorem B6239693 : Blo 972592 6239693 := bstep (se 3 (by rfl) ⟨1169942, by rfl⟩ : syracuseStep 6239693 = 2339885) B2339885
theorem B1848835 : Blo 972592 1848835 := bstep (se 1 (by rfl) ⟨1386626, by rfl⟩ : syracuseStep 1848835 = 2773253) B2773253
theorem B2110979 : Blo 972592 2110979 := bstep (se 1 (by rfl) ⟨1583234, by rfl⟩ : syracuseStep 2110979 = 3166469) B3166469
theorem B1095187 : Blo 972592 1095187 := bstep (se 1 (by rfl) ⟨821390, by rfl⟩ : syracuseStep 1095187 = 1642781) B1642781
theorem B1848881 : Blo 972592 1848881 := bstep (se 2 (by rfl) ⟨693330, by rfl⟩ : syracuseStep 1848881 = 1386661) B1386661
theorem B3290705 : Blo 972592 3290705 := bstep (se 2 (by rfl) ⟨1234014, by rfl⟩ : syracuseStep 3290705 = 2468029) B2468029
theorem B2635409 : Blo 972592 2635409 := bstep (se 2 (by rfl) ⟨988278, by rfl⟩ : syracuseStep 2635409 = 1976557) B1976557
theorem B1095331 : Blo 972592 1095331 := bstep (se 1 (by rfl) ⟨821498, by rfl⟩ : syracuseStep 1095331 = 1642997) B1642997
theorem B1095475 : Blo 972592 1095475 := bstep (se 1 (by rfl) ⟨821606, by rfl⟩ : syracuseStep 1095475 = 1643213) B1643213
theorem B2078531 : Blo 972592 2078531 := bstep (se 1 (by rfl) ⟨1558898, by rfl⟩ : syracuseStep 2078531 = 3117797) B3117797
theorem B1849169 : Blo 972592 1849169 := bstep (se 2 (by rfl) ⟨693438, by rfl⟩ : syracuseStep 1849169 = 1386877) B1386877
theorem B2373457 : Blo 972592 2373457 := bstep (se 2 (by rfl) ⟨890046, by rfl⟩ : syracuseStep 2373457 = 1780093) B1780093
theorem B1095619 : Blo 972592 1095619 := bstep (se 1 (by rfl) ⟨821714, by rfl⟩ : syracuseStep 1095619 = 1643429) B1643429
theorem B1095763 : Blo 972592 1095763 := bstep (se 1 (by rfl) ⟨821822, by rfl⟩ : syracuseStep 1095763 = 1643645) B1643645
theorem B3291245 : Blo 972592 3291245 := bstep (se 3 (by rfl) ⟨617108, by rfl⟩ : syracuseStep 3291245 = 1234217) B1234217
theorem B2341009 : Blo 972592 2341009 := bstep (se 2 (by rfl) ⟨877878, by rfl⟩ : syracuseStep 2341009 = 1755757) B1755757
theorem B3291299 : Blo 972592 3291299 := bstep (se 1 (by rfl) ⟨2468474, by rfl⟩ : syracuseStep 3291299 = 4936949) B4936949
theorem B1095907 : Blo 972592 1095907 := bstep (se 1 (by rfl) ⟨821930, by rfl⟩ : syracuseStep 1095907 = 1643861) B1643861
theorem B1096051 : Blo 972592 1096051 := bstep (se 1 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 1096051 = 1644077) B1644077
theorem B3291569 : Blo 972592 3291569 := bstep (se 2 (by rfl) ⟨1234338, by rfl⟩ : syracuseStep 3291569 = 2468677) B2468677
theorem B2636273 : Blo 972592 2636273 := bstep (se 2 (by rfl) ⟨988602, by rfl⟩ : syracuseStep 2636273 = 1977205) B1977205
theorem B1096195 : Blo 972592 1096195 := bstep (se 1 (by rfl) ⟨822146, by rfl⟩ : syracuseStep 1096195 = 1644293) B1644293
theorem B1849891 : Blo 972592 1849891 := bstep (se 1 (by rfl) ⟨1387418, by rfl⟩ : syracuseStep 1849891 = 2774837) B2774837
theorem B13318769 : Blo 972592 13318769 := bstep (se 2 (by rfl) ⟨4994538, by rfl⟩ : syracuseStep 13318769 = 9989077) B9989077
theorem B1096339 : Blo 972592 1096339 := bstep (se 1 (by rfl) ⟨822254, by rfl⟩ : syracuseStep 1096339 = 1644509) B1644509
theorem B2079427 : Blo 972592 2079427 := bstep (se 1 (by rfl) ⟨1559570, by rfl⟩ : syracuseStep 2079427 = 3119141) B3119141
theorem B1096483 : Blo 972592 1096483 := bstep (se 1 (by rfl) ⟨822362, by rfl⟩ : syracuseStep 1096483 = 1644725) B1644725
theorem B1096627 : Blo 972592 1096627 := bstep (se 1 (by rfl) ⟨822470, by rfl⟩ : syracuseStep 1096627 = 1644941) B1644941
theorem B3292109 : Blo 972592 3292109 := bstep (se 3 (by rfl) ⟨617270, by rfl⟩ : syracuseStep 3292109 = 1234541) B1234541
theorem B1850339 : Blo 972592 1850339 := bstep (se 1 (by rfl) ⟨1387754, by rfl⟩ : syracuseStep 1850339 = 2775509) B2775509
theorem B3128291 : Blo 972592 3128291 := bstep (se 1 (by rfl) ⟨2346218, by rfl⟩ : syracuseStep 3128291 = 4692437) B4692437
theorem B3292163 : Blo 972592 3292163 := bstep (se 1 (by rfl) ⟨2469122, by rfl⟩ : syracuseStep 3292163 = 4938245) B4938245
theorem B5553157 : Blo 972592 5553157 := bstep (se 4 (by rfl) ⟨520608, by rfl⟩ : syracuseStep 5553157 = 1041217) B1041217
theorem B1096771 : Blo 972592 1096771 := bstep (se 1 (by rfl) ⟨822578, by rfl⟩ : syracuseStep 1096771 = 1645157) B1645157
theorem B2964593 : Blo 972592 2964593 := bstep (se 2 (by rfl) ⟨1111722, by rfl⟩ : syracuseStep 2964593 = 2223445) B2223445
theorem B1096915 : Blo 972592 1096915 := bstep (se 1 (by rfl) ⟨822686, by rfl⟩ : syracuseStep 1096915 = 1645373) B1645373
theorem B1850627 : Blo 972592 1850627 := bstep (se 1 (by rfl) ⟨1387970, by rfl⟩ : syracuseStep 1850627 = 2775941) B2775941
theorem B3292433 : Blo 972592 3292433 := bstep (se 2 (by rfl) ⟨1234662, by rfl⟩ : syracuseStep 3292433 = 2469325) B2469325
theorem B1097059 : Blo 972592 1097059 := bstep (se 1 (by rfl) ⟨822794, by rfl⟩ : syracuseStep 1097059 = 1645589) B1645589
theorem B1686977 : Blo 972592 1686977 := bstep (se 2 (by rfl) ⟨632616, by rfl⟩ : syracuseStep 1686977 = 1265233) B1265233
theorem B47431109 : Blo 972592 47431109 := bstep (se 4 (by rfl) ⟨4446666, by rfl⟩ : syracuseStep 47431109 = 8893333) B8893333
theorem B7388657 : Blo 972592 7388657 := bstep (se 2 (by rfl) ⟨2770746, by rfl⟩ : syracuseStep 7388657 = 5541493) B5541493
theorem B1097203 : Blo 972592 1097203 := bstep (se 1 (by rfl) ⟨822902, by rfl⟩ : syracuseStep 1097203 = 1645805) B1645805
theorem B1097347 : Blo 972592 1097347 := bstep (se 1 (by rfl) ⟨823010, by rfl⟩ : syracuseStep 1097347 = 1646021) B1646021
theorem B2637485 : Blo 972592 2637485 := bstep (se 3 (by rfl) ⟨494528, by rfl⟩ : syracuseStep 2637485 = 989057) B989057
theorem B1097491 : Blo 972592 1097491 := bstep (se 1 (by rfl) ⟨823118, by rfl⟩ : syracuseStep 1097491 = 1646237) B1646237
theorem B3292973 : Blo 972592 3292973 := bstep (se 3 (by rfl) ⟨617432, by rfl⟩ : syracuseStep 3292973 = 1234865) B1234865
theorem B3293027 : Blo 972592 3293027 := bstep (se 1 (by rfl) ⟨2469770, by rfl⟩ : syracuseStep 3293027 = 4939541) B4939541
theorem B4931441 : Blo 972592 4931441 := bstep (se 2 (by rfl) ⟨1849290, by rfl⟩ : syracuseStep 4931441 = 3698581) B3698581
theorem B2080657 : Blo 972592 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B1097635 : Blo 972592 1097635 := bstep (se 1 (by rfl) ⟨823226, by rfl⟩ : syracuseStep 1097635 = 1646453) B1646453
theorem B1753105 : Blo 972592 1753105 := bstep (se 2 (by rfl) ⟨657414, by rfl⟩ : syracuseStep 1753105 = 1314829) B1314829
theorem B1097779 : Blo 972592 1097779 := bstep (se 1 (by rfl) ⟨823334, by rfl⟩ : syracuseStep 1097779 = 1646669) B1646669
theorem B4505699 : Blo 972592 4505699 := bstep (se 1 (by rfl) ⟨3379274, by rfl⟩ : syracuseStep 4505699 = 6758549) B6758549
theorem B8896625 : Blo 972592 8896625 := bstep (se 2 (by rfl) ⟨3336234, by rfl⟩ : syracuseStep 8896625 = 6672469) B6672469
theorem B3293297 : Blo 972592 3293297 := bstep (se 2 (by rfl) ⟨1234986, by rfl⟩ : syracuseStep 3293297 = 2469973) B2469973
theorem B1851569 : Blo 972592 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B1097923 : Blo 972592 1097923 := bstep (se 1 (by rfl) ⟨823442, by rfl⟩ : syracuseStep 1097923 = 1646885) B1646885
theorem B1098067 : Blo 972592 1098067 := bstep (se 1 (by rfl) ⟨823550, by rfl⟩ : syracuseStep 1098067 = 1647101) B1647101
theorem B1098211 : Blo 972592 1098211 := bstep (se 1 (by rfl) ⟨823658, by rfl⟩ : syracuseStep 1098211 = 1647317) B1647317
theorem B3949091 : Blo 972592 3949091 := bstep (se 1 (by rfl) ⟨2961818, by rfl⟩ : syracuseStep 3949091 = 5923637) B5923637
theorem B1753667 : Blo 972592 1753667 := bstep (se 1 (by rfl) ⟨1315250, by rfl⟩ : syracuseStep 1753667 = 2630501) B2630501
theorem B1098355 : Blo 972592 1098355 := bstep (se 1 (by rfl) ⟨823766, by rfl⟩ : syracuseStep 1098355 = 1647533) B1647533
theorem B3293837 : Blo 972592 3293837 := bstep (se 3 (by rfl) ⟨617594, by rfl⟩ : syracuseStep 3293837 = 1235189) B1235189
theorem B6668963 : Blo 972592 6668963 := bstep (se 1 (by rfl) ⟨5001722, by rfl⟩ : syracuseStep 6668963 = 10003445) B10003445
theorem B3293891 : Blo 972592 3293891 := bstep (se 1 (by rfl) ⟨2470418, by rfl⟩ : syracuseStep 3293891 = 4940837) B4940837
theorem B1458899 : Blo 972592 1458899 := bstep (se 1 (by rfl) ⟨1094174, by rfl⟩ : syracuseStep 1458899 = 2188349) B2188349
theorem B1458929 : Blo 972592 1458929 := bstep (se 2 (by rfl) ⟨547098, by rfl⟩ : syracuseStep 1458929 = 1094197) B1094197
theorem B12468977 : Blo 972592 12468977 := bstep (se 2 (by rfl) ⟨4675866, by rfl⟩ : syracuseStep 12468977 = 9351733) B9351733
theorem B1458947 : Blo 972592 1458947 := bstep (se 1 (by rfl) ⟨1094210, by rfl⟩ : syracuseStep 1458947 = 2188421) B2188421
theorem B1098499 : Blo 972592 1098499 := bstep (se 1 (by rfl) ⟨823874, by rfl⟩ : syracuseStep 1098499 = 1647749) B1647749
theorem B2769677 : Blo 972592 2769677 := bstep (se 3 (by rfl) ⟨519314, by rfl⟩ : syracuseStep 2769677 = 1038629) B1038629
theorem B1458977 : Blo 972592 1458977 := bstep (se 2 (by rfl) ⟨547116, by rfl⟩ : syracuseStep 1458977 = 1094233) B1094233
theorem B1458995 : Blo 972592 1458995 := bstep (se 1 (by rfl) ⟨1094246, by rfl⟩ : syracuseStep 1458995 = 2188493) B2188493
theorem B1459025 : Blo 972592 1459025 := bstep (se 2 (by rfl) ⟨547134, by rfl⟩ : syracuseStep 1459025 = 1094269) B1094269
theorem B1459043 : Blo 972592 1459043 := bstep (se 1 (by rfl) ⟨1094282, by rfl⟩ : syracuseStep 1459043 = 2188565) B2188565
theorem B1459073 : Blo 972592 1459073 := bstep (se 2 (by rfl) ⟨547152, by rfl⟩ : syracuseStep 1459073 = 1094305) B1094305
theorem B1459091 : Blo 972592 1459091 := bstep (se 1 (by rfl) ⟨1094318, by rfl⟩ : syracuseStep 1459091 = 2188637) B2188637
theorem B1098643 : Blo 972592 1098643 := bstep (se 1 (by rfl) ⟨823982, by rfl⟩ : syracuseStep 1098643 = 1647965) B1647965
theorem B1459121 : Blo 972592 1459121 := bstep (se 2 (by rfl) ⟨547170, by rfl⟩ : syracuseStep 1459121 = 1094341) B1094341
theorem B1459139 : Blo 972592 1459139 := bstep (se 1 (by rfl) ⟨1094354, by rfl⟩ : syracuseStep 1459139 = 2188709) B2188709
theorem B5555141 : Blo 972592 5555141 := bstep (se 4 (by rfl) ⟨520794, by rfl⟩ : syracuseStep 5555141 = 1041589) B1041589
theorem B3294161 : Blo 972592 3294161 := bstep (se 2 (by rfl) ⟨1235310, by rfl⟩ : syracuseStep 3294161 = 2470621) B2470621
theorem B1459169 : Blo 972592 1459169 := bstep (se 2 (by rfl) ⟨547188, by rfl⟩ : syracuseStep 1459169 = 1094377) B1094377
theorem B1459187 : Blo 972592 1459187 := bstep (se 1 (by rfl) ⟨1094390, by rfl⟩ : syracuseStep 1459187 = 2188781) B2188781
theorem B1459217 : Blo 972592 1459217 := bstep (se 2 (by rfl) ⟨547206, by rfl⟩ : syracuseStep 1459217 = 1094413) B1094413
theorem B1754129 : Blo 972592 1754129 := bstep (se 2 (by rfl) ⟨657798, by rfl⟩ : syracuseStep 1754129 = 1315597) B1315597
theorem B1459235 : Blo 972592 1459235 := bstep (se 1 (by rfl) ⟨1094426, by rfl⟩ : syracuseStep 1459235 = 2188853) B2188853
theorem B1852465 : Blo 972592 1852465 := bstep (se 2 (by rfl) ⟨694674, by rfl⟩ : syracuseStep 1852465 = 1389349) B1389349
theorem B1459265 : Blo 972592 1459265 := bstep (se 2 (by rfl) ⟨547224, by rfl⟩ : syracuseStep 1459265 = 1094449) B1094449
theorem B1459283 : Blo 972592 1459283 := bstep (se 1 (by rfl) ⟨1094462, by rfl⟩ : syracuseStep 1459283 = 2188925) B2188925
theorem B1459313 : Blo 972592 1459313 := bstep (se 2 (by rfl) ⟨547242, by rfl⟩ : syracuseStep 1459313 = 1094485) B1094485
theorem B1459331 : Blo 972592 1459331 := bstep (se 1 (by rfl) ⟨1094498, by rfl⟩ : syracuseStep 1459331 = 2188997) B2188997
theorem B1459361 : Blo 972592 1459361 := bstep (se 2 (by rfl) ⟨547260, by rfl⟩ : syracuseStep 1459361 = 1094521) B1094521
theorem B1459379 : Blo 972592 1459379 := bstep (se 1 (by rfl) ⟨1094534, by rfl⟩ : syracuseStep 1459379 = 2189069) B2189069
theorem B1459409 : Blo 972592 1459409 := bstep (se 2 (by rfl) ⟨547278, by rfl⟩ : syracuseStep 1459409 = 1094557) B1094557
theorem B1852625 : Blo 972592 1852625 := bstep (se 2 (by rfl) ⟨694734, by rfl⟩ : syracuseStep 1852625 = 1389469) B1389469
theorem B1459427 : Blo 972592 1459427 := bstep (se 1 (by rfl) ⟨1094570, by rfl⟩ : syracuseStep 1459427 = 2189141) B2189141
theorem B1459457 : Blo 972592 1459457 := bstep (se 2 (by rfl) ⟨547296, by rfl⟩ : syracuseStep 1459457 = 1094593) B1094593
theorem B1459475 : Blo 972592 1459475 := bstep (se 1 (by rfl) ⟨1094606, by rfl⟩ : syracuseStep 1459475 = 2189213) B2189213
theorem B4932899 : Blo 972592 4932899 := bstep (se 1 (by rfl) ⟨3699674, by rfl⟩ : syracuseStep 4932899 = 7399349) B7399349
theorem B1459505 : Blo 972592 1459505 := bstep (se 2 (by rfl) ⟨547314, by rfl⟩ : syracuseStep 1459505 = 1094629) B1094629
theorem B3851569 : Blo 972592 3851569 := bstep (se 2 (by rfl) ⟨1444338, by rfl⟩ : syracuseStep 3851569 = 2888677) B2888677
theorem B1459523 : Blo 972592 1459523 := bstep (se 1 (by rfl) ⟨1094642, by rfl⟩ : syracuseStep 1459523 = 2189285) B2189285
theorem B1459553 : Blo 972592 1459553 := bstep (se 2 (by rfl) ⟨547332, by rfl⟩ : syracuseStep 1459553 = 1094665) B1094665
theorem B2082161 : Blo 972592 2082161 := bstep (se 2 (by rfl) ⟨780810, by rfl⟩ : syracuseStep 2082161 = 1561621) B1561621
theorem B1459571 : Blo 972592 1459571 := bstep (se 1 (by rfl) ⟨1094678, by rfl⟩ : syracuseStep 1459571 = 2189357) B2189357
theorem B2082179 : Blo 972592 2082179 := bstep (se 1 (by rfl) ⟨1561634, by rfl⟩ : syracuseStep 2082179 = 3123269) B3123269
theorem B1459601 : Blo 972592 1459601 := bstep (se 2 (by rfl) ⟨547350, by rfl⟩ : syracuseStep 1459601 = 1094701) B1094701
theorem B1459619 : Blo 972592 1459619 := bstep (se 1 (by rfl) ⟨1094714, by rfl⟩ : syracuseStep 1459619 = 2189429) B2189429
theorem B1459649 : Blo 972592 1459649 := bstep (se 2 (by rfl) ⟨547368, by rfl⟩ : syracuseStep 1459649 = 1094737) B1094737
theorem B1459667 : Blo 972592 1459667 := bstep (se 1 (by rfl) ⟨1094750, by rfl⟩ : syracuseStep 1459667 = 2189501) B2189501
theorem B3294701 : Blo 972592 3294701 := bstep (se 3 (by rfl) ⟨617756, by rfl⟩ : syracuseStep 3294701 = 1235513) B1235513
theorem B1459697 : Blo 972592 1459697 := bstep (se 2 (by rfl) ⟨547386, by rfl⟩ : syracuseStep 1459697 = 1094773) B1094773
theorem B1459715 : Blo 972592 1459715 := bstep (se 1 (by rfl) ⟨1094786, by rfl⟩ : syracuseStep 1459715 = 2189573) B2189573
theorem B1459745 : Blo 972592 1459745 := bstep (se 2 (by rfl) ⟨547404, by rfl⟩ : syracuseStep 1459745 = 1094809) B1094809
theorem B3294755 : Blo 972592 3294755 := bstep (se 1 (by rfl) ⟨2471066, by rfl⟩ : syracuseStep 3294755 = 4942133) B4942133
theorem B3950129 : Blo 972592 3950129 := bstep (se 2 (by rfl) ⟨1481298, by rfl⟩ : syracuseStep 3950129 = 2962597) B2962597
theorem B1459763 : Blo 972592 1459763 := bstep (se 1 (by rfl) ⟨1094822, by rfl⟩ : syracuseStep 1459763 = 2189645) B2189645
theorem B1459793 : Blo 972592 1459793 := bstep (se 2 (by rfl) ⟨547422, by rfl⟩ : syracuseStep 1459793 = 1094845) B1094845
theorem B1459811 : Blo 972592 1459811 := bstep (se 1 (by rfl) ⟨1094858, by rfl⟩ : syracuseStep 1459811 = 2189717) B2189717
theorem B1853027 : Blo 972592 1853027 := bstep (se 1 (by rfl) ⟨1389770, by rfl⟩ : syracuseStep 1853027 = 2779541) B2779541
theorem B1459841 : Blo 972592 1459841 := bstep (se 2 (by rfl) ⟨547440, by rfl⟩ : syracuseStep 1459841 = 1094881) B1094881
theorem B1459859 : Blo 972592 1459859 := bstep (se 1 (by rfl) ⟨1094894, by rfl⟩ : syracuseStep 1459859 = 2189789) B2189789
theorem B1459889 : Blo 972592 1459889 := bstep (se 2 (by rfl) ⟨547458, by rfl⟩ : syracuseStep 1459889 = 1094917) B1094917
theorem B1459907 : Blo 972592 1459907 := bstep (se 1 (by rfl) ⟨1094930, by rfl⟩ : syracuseStep 1459907 = 2189861) B2189861
theorem B1459937 : Blo 972592 1459937 := bstep (se 2 (by rfl) ⟨547476, by rfl⟩ : syracuseStep 1459937 = 1094953) B1094953
theorem B1459955 : Blo 972592 1459955 := bstep (se 1 (by rfl) ⟨1094966, by rfl⟩ : syracuseStep 1459955 = 2189933) B2189933
theorem B1558289 : Blo 972592 1558289 := bstep (se 2 (by rfl) ⟨584358, by rfl⟩ : syracuseStep 1558289 = 1168717) B1168717
theorem B1459985 : Blo 972592 1459985 := bstep (se 2 (by rfl) ⟨547494, by rfl⟩ : syracuseStep 1459985 = 1094989) B1094989
theorem B1460003 : Blo 972592 1460003 := bstep (se 1 (by rfl) ⟨1095002, by rfl⟩ : syracuseStep 1460003 = 2190005) B2190005
theorem B3295025 : Blo 972592 3295025 := bstep (se 2 (by rfl) ⟨1235634, by rfl⟩ : syracuseStep 3295025 = 2471269) B2471269
theorem B1460033 : Blo 972592 1460033 := bstep (se 2 (by rfl) ⟨547512, by rfl⟩ : syracuseStep 1460033 = 1095025) B1095025
theorem B1460051 : Blo 972592 1460051 := bstep (se 1 (by rfl) ⟨1095038, by rfl⟩ : syracuseStep 1460051 = 2190077) B2190077
theorem B1460081 : Blo 972592 1460081 := bstep (se 2 (by rfl) ⟨547530, by rfl⟩ : syracuseStep 1460081 = 1095061) B1095061
theorem B1460099 : Blo 972592 1460099 := bstep (se 1 (by rfl) ⟨1095074, by rfl⟩ : syracuseStep 1460099 = 2190149) B2190149
theorem B1460129 : Blo 972592 1460129 := bstep (se 2 (by rfl) ⟨547548, by rfl⟩ : syracuseStep 1460129 = 1095097) B1095097
theorem B2770861 : Blo 972592 2770861 := bstep (se 3 (by rfl) ⟨519536, by rfl⟩ : syracuseStep 2770861 = 1039073) B1039073
theorem B1460147 : Blo 972592 1460147 := bstep (se 1 (by rfl) ⟨1095110, by rfl⟩ : syracuseStep 1460147 = 2190221) B2190221
theorem B1460177 : Blo 972592 1460177 := bstep (se 2 (by rfl) ⟨547566, by rfl⟩ : syracuseStep 1460177 = 1095133) B1095133
theorem B2344913 : Blo 972592 2344913 := bstep (se 2 (by rfl) ⟨879342, by rfl⟩ : syracuseStep 2344913 = 1758685) B1758685
theorem B1460195 : Blo 972592 1460195 := bstep (se 1 (by rfl) ⟨1095146, by rfl⟩ : syracuseStep 1460195 = 2190293) B2190293
theorem B1460225 : Blo 972592 1460225 := bstep (se 2 (by rfl) ⟨547584, by rfl⟩ : syracuseStep 1460225 = 1095169) B1095169
theorem B2377745 : Blo 972592 2377745 := bstep (se 2 (by rfl) ⟨891654, by rfl⟩ : syracuseStep 2377745 = 1783309) B1783309
theorem B1460243 : Blo 972592 1460243 := bstep (se 1 (by rfl) ⟨1095182, by rfl⟩ : syracuseStep 1460243 = 2190365) B2190365
theorem B4442147 : Blo 972592 4442147 := bstep (se 1 (by rfl) ⟨3331610, by rfl⟩ : syracuseStep 4442147 = 6663221) B6663221
theorem B1460273 : Blo 972592 1460273 := bstep (se 2 (by rfl) ⟨547602, by rfl⟩ : syracuseStep 1460273 = 1095205) B1095205
theorem B1460291 : Blo 972592 1460291 := bstep (se 1 (by rfl) ⟨1095218, by rfl⟩ : syracuseStep 1460291 = 2190437) B2190437
theorem B4933709 : Blo 972592 4933709 := bstep (se 3 (by rfl) ⟨925070, by rfl⟩ : syracuseStep 4933709 = 1850141) B1850141
theorem B1460321 : Blo 972592 1460321 := bstep (se 2 (by rfl) ⟨547620, by rfl⟩ : syracuseStep 1460321 = 1095241) B1095241
theorem B1460339 : Blo 972592 1460339 := bstep (se 1 (by rfl) ⟨1095254, by rfl⟩ : syracuseStep 1460339 = 2190509) B2190509
theorem B1460369 : Blo 972592 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B1460387 : Blo 972592 1460387 := bstep (se 1 (by rfl) ⟨1095290, by rfl⟩ : syracuseStep 1460387 = 2190581) B2190581
theorem B1460417 : Blo 972592 1460417 := bstep (se 2 (by rfl) ⟨547656, by rfl⟩ : syracuseStep 1460417 = 1095313) B1095313
theorem B1460435 : Blo 972592 1460435 := bstep (se 1 (by rfl) ⟨1095326, by rfl⟩ : syracuseStep 1460435 = 2190653) B2190653
theorem B1460465 : Blo 972592 1460465 := bstep (se 2 (by rfl) ⟨547674, by rfl⟩ : syracuseStep 1460465 = 1095349) B1095349
theorem B1460483 : Blo 972592 1460483 := bstep (se 1 (by rfl) ⟨1095362, by rfl⟩ : syracuseStep 1460483 = 2190725) B2190725
theorem B1460513 : Blo 972592 1460513 := bstep (se 2 (by rfl) ⟨547692, by rfl⟩ : syracuseStep 1460513 = 1095385) B1095385
theorem B1231139 : Blo 972592 1231139 := bstep (se 1 (by rfl) ⟨923354, by rfl⟩ : syracuseStep 1231139 = 1846709) B1846709
theorem B1460531 : Blo 972592 1460531 := bstep (se 1 (by rfl) ⟨1095398, by rfl⟩ : syracuseStep 1460531 = 2190797) B2190797
theorem B5916997 : Blo 972592 5916997 := bstep (se 4 (by rfl) ⟨554718, by rfl⟩ : syracuseStep 5916997 = 1109437) B1109437
theorem B3295565 : Blo 972592 3295565 := bstep (se 3 (by rfl) ⟨617918, by rfl⟩ : syracuseStep 3295565 = 1235837) B1235837
theorem B1460561 : Blo 972592 1460561 := bstep (se 2 (by rfl) ⟨547710, by rfl⟩ : syracuseStep 1460561 = 1095421) B1095421
theorem B1460579 : Blo 972592 1460579 := bstep (se 1 (by rfl) ⟨1095434, by rfl⟩ : syracuseStep 1460579 = 2190869) B2190869
theorem B1460609 : Blo 972592 1460609 := bstep (se 2 (by rfl) ⟨547728, by rfl⟩ : syracuseStep 1460609 = 1095457) B1095457
theorem B3295619 : Blo 972592 3295619 := bstep (se 1 (by rfl) ⟨2471714, by rfl⟩ : syracuseStep 3295619 = 4943429) B4943429
theorem B1460627 : Blo 972592 1460627 := bstep (se 1 (by rfl) ⟨1095470, by rfl⟩ : syracuseStep 1460627 = 2190941) B2190941
theorem B1460657 : Blo 972592 1460657 := bstep (se 2 (by rfl) ⟨547746, by rfl⟩ : syracuseStep 1460657 = 1095493) B1095493
theorem B1460675 : Blo 972592 1460675 := bstep (se 1 (by rfl) ⟨1095506, by rfl⟩ : syracuseStep 1460675 = 2191013) B2191013
theorem B1460705 : Blo 972592 1460705 := bstep (se 2 (by rfl) ⟨547764, by rfl⟩ : syracuseStep 1460705 = 1095529) B1095529
theorem B1853923 : Blo 972592 1853923 := bstep (se 1 (by rfl) ⟨1390442, by rfl⟩ : syracuseStep 1853923 = 2780885) B2780885
theorem B1460723 : Blo 972592 1460723 := bstep (se 1 (by rfl) ⟨1095542, by rfl⟩ : syracuseStep 1460723 = 2191085) B2191085
theorem B1460753 : Blo 972592 1460753 := bstep (se 2 (by rfl) ⟨547782, by rfl⟩ : syracuseStep 1460753 = 1095565) B1095565
theorem B1460771 : Blo 972592 1460771 := bstep (se 1 (by rfl) ⟨1095578, by rfl⟩ : syracuseStep 1460771 = 2191157) B2191157
theorem B4999715 : Blo 972592 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B2345507 : Blo 972592 2345507 := bstep (se 1 (by rfl) ⟨1759130, by rfl⟩ : syracuseStep 2345507 = 3518261) B3518261
theorem B2673197 : Blo 972592 2673197 := bstep (se 3 (by rfl) ⟨501224, by rfl⟩ : syracuseStep 2673197 = 1002449) B1002449
theorem B1460801 : Blo 972592 1460801 := bstep (se 2 (by rfl) ⟨547800, by rfl⟩ : syracuseStep 1460801 = 1095601) B1095601
theorem B1460819 : Blo 972592 1460819 := bstep (se 1 (by rfl) ⟨1095614, by rfl⟩ : syracuseStep 1460819 = 2191229) B2191229
theorem B1460849 : Blo 972592 1460849 := bstep (se 2 (by rfl) ⟨547818, by rfl⟩ : syracuseStep 1460849 = 1095637) B1095637
theorem B1460867 : Blo 972592 1460867 := bstep (se 1 (by rfl) ⟨1095650, by rfl⟩ : syracuseStep 1460867 = 2191301) B2191301
theorem B2345603 : Blo 972592 2345603 := bstep (se 1 (by rfl) ⟨1759202, by rfl⟩ : syracuseStep 2345603 = 3518405) B3518405
theorem B3295889 : Blo 972592 3295889 := bstep (se 2 (by rfl) ⟨1235958, by rfl⟩ : syracuseStep 3295889 = 2471917) B2471917
theorem B1460897 : Blo 972592 1460897 := bstep (se 2 (by rfl) ⟨547836, by rfl⟩ : syracuseStep 1460897 = 1095673) B1095673
theorem B1460915 : Blo 972592 1460915 := bstep (se 1 (by rfl) ⟨1095686, by rfl⟩ : syracuseStep 1460915 = 2191373) B2191373
theorem B1460945 : Blo 972592 1460945 := bstep (se 2 (by rfl) ⟨547854, by rfl⟩ : syracuseStep 1460945 = 1095709) B1095709
theorem B1460963 : Blo 972592 1460963 := bstep (se 1 (by rfl) ⟨1095722, by rfl⟩ : syracuseStep 1460963 = 2191445) B2191445
theorem B1460993 : Blo 972592 1460993 := bstep (se 2 (by rfl) ⟨547872, by rfl⟩ : syracuseStep 1460993 = 1095745) B1095745
theorem B1461011 : Blo 972592 1461011 := bstep (se 1 (by rfl) ⟨1095758, by rfl⟩ : syracuseStep 1461011 = 2191517) B2191517
theorem B30034709 : Blo 972592 30034709 := bstep (se 6 (by rfl) ⟨703938, by rfl⟩ : syracuseStep 30034709 = 1407877) B1407877
theorem B1461041 : Blo 972592 1461041 := bstep (se 2 (by rfl) ⟨547890, by rfl⟩ : syracuseStep 1461041 = 1095781) B1095781
theorem B1461059 : Blo 972592 1461059 := bstep (se 1 (by rfl) ⟨1095794, by rfl⟩ : syracuseStep 1461059 = 2191589) B2191589
theorem B1461089 : Blo 972592 1461089 := bstep (se 2 (by rfl) ⟨547908, by rfl⟩ : syracuseStep 1461089 = 1095817) B1095817
theorem B1461107 : Blo 972592 1461107 := bstep (se 1 (by rfl) ⟨1095830, by rfl⟩ : syracuseStep 1461107 = 2191661) B2191661
theorem B1461137 : Blo 972592 1461137 := bstep (se 2 (by rfl) ⟨547926, by rfl⟩ : syracuseStep 1461137 = 1095853) B1095853
theorem B1461155 : Blo 972592 1461155 := bstep (se 1 (by rfl) ⟨1095866, by rfl⟩ : syracuseStep 1461155 = 2191733) B2191733
theorem B1461185 : Blo 972592 1461185 := bstep (se 2 (by rfl) ⟨547944, by rfl⟩ : syracuseStep 1461185 = 1095889) B1095889
theorem B2771921 : Blo 972592 2771921 := bstep (se 2 (by rfl) ⟨1039470, by rfl⟩ : syracuseStep 2771921 = 2078941) B2078941
theorem B1461203 : Blo 972592 1461203 := bstep (se 1 (by rfl) ⟨1095902, by rfl⟩ : syracuseStep 1461203 = 2191805) B2191805
theorem B1231843 : Blo 972592 1231843 := bstep (se 1 (by rfl) ⟨923882, by rfl⟩ : syracuseStep 1231843 = 1847765) B1847765
theorem B1461233 : Blo 972592 1461233 := bstep (se 2 (by rfl) ⟨547962, by rfl⟩ : syracuseStep 1461233 = 1095925) B1095925
theorem B1461251 : Blo 972592 1461251 := bstep (se 1 (by rfl) ⟨1095938, by rfl⟩ : syracuseStep 1461251 = 2191877) B2191877
theorem B1461281 : Blo 972592 1461281 := bstep (se 2 (by rfl) ⟨547980, by rfl⟩ : syracuseStep 1461281 = 1095961) B1095961
theorem B1461299 : Blo 972592 1461299 := bstep (se 1 (by rfl) ⟨1095974, by rfl⟩ : syracuseStep 1461299 = 2191949) B2191949
theorem B1231939 : Blo 972592 1231939 := bstep (se 1 (by rfl) ⟨923954, by rfl⟩ : syracuseStep 1231939 = 1847909) B1847909
theorem B1461329 : Blo 972592 1461329 := bstep (se 2 (by rfl) ⟨547998, by rfl⟩ : syracuseStep 1461329 = 1095997) B1095997
theorem B1461347 : Blo 972592 1461347 := bstep (se 1 (by rfl) ⟨1096010, by rfl⟩ : syracuseStep 1461347 = 2192021) B2192021
theorem B1461377 : Blo 972592 1461377 := bstep (se 2 (by rfl) ⟨548016, by rfl⟩ : syracuseStep 1461377 = 1096033) B1096033
theorem B2641027 : Blo 972592 2641027 := bstep (se 1 (by rfl) ⟨1980770, by rfl⟩ : syracuseStep 2641027 = 3961541) B3961541
theorem B1461395 : Blo 972592 1461395 := bstep (se 1 (by rfl) ⟨1096046, by rfl⟩ : syracuseStep 1461395 = 2192093) B2192093
theorem B1461425 : Blo 972592 1461425 := bstep (se 2 (by rfl) ⟨548034, by rfl⟩ : syracuseStep 1461425 = 1096069) B1096069
theorem B1461443 : Blo 972592 1461443 := bstep (se 1 (by rfl) ⟨1096082, by rfl⟩ : syracuseStep 1461443 = 2192165) B2192165
theorem B1461473 : Blo 972592 1461473 := bstep (se 2 (by rfl) ⟨548052, by rfl⟩ : syracuseStep 1461473 = 1096105) B1096105
theorem B1461491 : Blo 972592 1461491 := bstep (se 1 (by rfl) ⟨1096118, by rfl⟩ : syracuseStep 1461491 = 2192237) B2192237
theorem B1461521 : Blo 972592 1461521 := bstep (se 2 (by rfl) ⟨548070, by rfl⟩ : syracuseStep 1461521 = 1096141) B1096141
theorem B1559827 : Blo 972592 1559827 := bstep (se 1 (by rfl) ⟨1169870, by rfl⟩ : syracuseStep 1559827 = 2339741) B2339741
theorem B1461539 : Blo 972592 1461539 := bstep (se 1 (by rfl) ⟨1096154, by rfl⟩ : syracuseStep 1461539 = 2192309) B2192309
theorem B1559873 : Blo 972592 1559873 := bstep (se 2 (by rfl) ⟨584952, by rfl⟩ : syracuseStep 1559873 = 1169905) B1169905
theorem B1461569 : Blo 972592 1461569 := bstep (se 2 (by rfl) ⟨548088, by rfl⟩ : syracuseStep 1461569 = 1096177) B1096177
theorem B2084177 : Blo 972592 2084177 := bstep (se 2 (by rfl) ⟨781566, by rfl⟩ : syracuseStep 2084177 = 1563133) B1563133
theorem B1461587 : Blo 972592 1461587 := bstep (se 1 (by rfl) ⟨1096190, by rfl⟩ : syracuseStep 1461587 = 2192381) B2192381
theorem B1461617 : Blo 972592 1461617 := bstep (se 2 (by rfl) ⟨548106, by rfl⟩ : syracuseStep 1461617 = 1096213) B1096213
theorem B1461635 : Blo 972592 1461635 := bstep (se 1 (by rfl) ⟨1096226, by rfl⟩ : syracuseStep 1461635 = 2192453) B2192453
theorem B1461665 : Blo 972592 1461665 := bstep (se 2 (by rfl) ⟨548124, by rfl⟩ : syracuseStep 1461665 = 1096249) B1096249
theorem B1461683 : Blo 972592 1461683 := bstep (se 1 (by rfl) ⟨1096262, by rfl⟩ : syracuseStep 1461683 = 2192525) B2192525
theorem B1461713 : Blo 972592 1461713 := bstep (se 2 (by rfl) ⟨548142, by rfl⟩ : syracuseStep 1461713 = 1096285) B1096285
theorem B1461731 : Blo 972592 1461731 := bstep (se 1 (by rfl) ⟨1096298, by rfl⟩ : syracuseStep 1461731 = 2192597) B2192597
theorem B1461761 : Blo 972592 1461761 := bstep (se 2 (by rfl) ⟨548160, by rfl⟩ : syracuseStep 1461761 = 1096321) B1096321
theorem B1461779 : Blo 972592 1461779 := bstep (se 1 (by rfl) ⟨1096334, by rfl⟩ : syracuseStep 1461779 = 2192669) B2192669
theorem B1461809 : Blo 972592 1461809 := bstep (se 2 (by rfl) ⟨548178, by rfl⟩ : syracuseStep 1461809 = 1096357) B1096357
theorem B1232435 : Blo 972592 1232435 := bstep (se 1 (by rfl) ⟨924326, by rfl⟩ : syracuseStep 1232435 = 1848653) B1848653
theorem B1461827 : Blo 972592 1461827 := bstep (se 1 (by rfl) ⟨1096370, by rfl⟩ : syracuseStep 1461827 = 2192741) B2192741
theorem B1461857 : Blo 972592 1461857 := bstep (se 2 (by rfl) ⟨548196, by rfl⟩ : syracuseStep 1461857 = 1096393) B1096393
theorem B2772593 : Blo 972592 2772593 := bstep (se 2 (by rfl) ⟨1039722, by rfl⟩ : syracuseStep 2772593 = 2079445) B2079445
theorem B1461875 : Blo 972592 1461875 := bstep (se 1 (by rfl) ⟨1096406, by rfl⟩ : syracuseStep 1461875 = 2192813) B2192813
theorem B1461905 : Blo 972592 1461905 := bstep (se 2 (by rfl) ⟨548214, by rfl⟩ : syracuseStep 1461905 = 1096429) B1096429
theorem B1461923 : Blo 972592 1461923 := bstep (se 1 (by rfl) ⟨1096442, by rfl⟩ : syracuseStep 1461923 = 2192885) B2192885
theorem B1461953 : Blo 972592 1461953 := bstep (se 2 (by rfl) ⟨548232, by rfl⟩ : syracuseStep 1461953 = 1096465) B1096465
theorem B1461971 : Blo 972592 1461971 := bstep (se 1 (by rfl) ⟨1096478, by rfl⟩ : syracuseStep 1461971 = 2192957) B2192957
theorem B1462001 : Blo 972592 1462001 := bstep (se 2 (by rfl) ⟨548250, by rfl⟩ : syracuseStep 1462001 = 1096501) B1096501
theorem B1462019 : Blo 972592 1462019 := bstep (se 1 (by rfl) ⟨1096514, by rfl⟩ : syracuseStep 1462019 = 2193029) B2193029
theorem B1462049 : Blo 972592 1462049 := bstep (se 2 (by rfl) ⟨548268, by rfl⟩ : syracuseStep 1462049 = 1096537) B1096537
theorem B1462067 : Blo 972592 1462067 := bstep (se 1 (by rfl) ⟨1096550, by rfl⟩ : syracuseStep 1462067 = 2193101) B2193101
theorem B1462097 : Blo 972592 1462097 := bstep (se 2 (by rfl) ⟨548286, by rfl⟩ : syracuseStep 1462097 = 1096573) B1096573
theorem B1462115 : Blo 972592 1462115 := bstep (se 1 (by rfl) ⟨1096586, by rfl⟩ : syracuseStep 1462115 = 2193173) B2193173
theorem B2084707 : Blo 972592 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B1462145 : Blo 972592 1462145 := bstep (se 2 (by rfl) ⟨548304, by rfl⟩ : syracuseStep 1462145 = 1096609) B1096609
theorem B1462163 : Blo 972592 1462163 := bstep (se 1 (by rfl) ⟨1096622, by rfl⟩ : syracuseStep 1462163 = 2193245) B2193245
theorem B1462193 : Blo 972592 1462193 := bstep (se 2 (by rfl) ⟨548322, by rfl⟩ : syracuseStep 1462193 = 1096645) B1096645
theorem B1462211 : Blo 972592 1462211 := bstep (se 1 (by rfl) ⟨1096658, by rfl⟩ : syracuseStep 1462211 = 2193317) B2193317
theorem B1462241 : Blo 972592 1462241 := bstep (se 2 (by rfl) ⟨548340, by rfl⟩ : syracuseStep 1462241 = 1096681) B1096681
theorem B1462259 : Blo 972592 1462259 := bstep (se 1 (by rfl) ⟨1096694, by rfl⟩ : syracuseStep 1462259 = 2193389) B2193389
theorem B2969603 : Blo 972592 2969603 := bstep (se 1 (by rfl) ⟨2227202, by rfl⟩ : syracuseStep 2969603 = 4454405) B4454405
theorem B1462289 : Blo 972592 1462289 := bstep (se 2 (by rfl) ⟨548358, by rfl⟩ : syracuseStep 1462289 = 1096717) B1096717
theorem B1462307 : Blo 972592 1462307 := bstep (se 1 (by rfl) ⟨1096730, by rfl⟩ : syracuseStep 1462307 = 2193461) B2193461
theorem B1462337 : Blo 972592 1462337 := bstep (se 2 (by rfl) ⟨548376, by rfl⟩ : syracuseStep 1462337 = 1096753) B1096753
theorem B1462355 : Blo 972592 1462355 := bstep (se 1 (by rfl) ⟨1096766, by rfl⟩ : syracuseStep 1462355 = 2193533) B2193533
theorem B1462385 : Blo 972592 1462385 := bstep (se 2 (by rfl) ⟨548394, by rfl⟩ : syracuseStep 1462385 = 1096789) B1096789
theorem B1462403 : Blo 972592 1462403 := bstep (se 1 (by rfl) ⟨1096802, by rfl⟩ : syracuseStep 1462403 = 2193605) B2193605
theorem B1462433 : Blo 972592 1462433 := bstep (se 2 (by rfl) ⟨548412, by rfl⟩ : syracuseStep 1462433 = 1096825) B1096825
theorem B1462451 : Blo 972592 1462451 := bstep (se 1 (by rfl) ⟨1096838, by rfl⟩ : syracuseStep 1462451 = 2193677) B2193677
theorem B1462481 : Blo 972592 1462481 := bstep (se 2 (by rfl) ⟨548430, by rfl⟩ : syracuseStep 1462481 = 1096861) B1096861
theorem B1462499 : Blo 972592 1462499 := bstep (se 1 (by rfl) ⟨1096874, by rfl⟩ : syracuseStep 1462499 = 2193749) B2193749
theorem B1233139 : Blo 972592 1233139 := bstep (se 1 (by rfl) ⟨924854, by rfl⟩ : syracuseStep 1233139 = 1849709) B1849709
theorem B1462529 : Blo 972592 1462529 := bstep (se 2 (by rfl) ⟨548448, by rfl⟩ : syracuseStep 1462529 = 1096897) B1096897
theorem B1069331 : Blo 972592 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B1462547 : Blo 972592 1462547 := bstep (se 1 (by rfl) ⟨1096910, by rfl⟩ : syracuseStep 1462547 = 2193821) B2193821
theorem B1560865 : Blo 972592 1560865 := bstep (se 2 (by rfl) ⟨585324, by rfl⟩ : syracuseStep 1560865 = 1170649) B1170649
theorem B1462577 : Blo 972592 1462577 := bstep (se 2 (by rfl) ⟨548466, by rfl⟩ : syracuseStep 1462577 = 1096933) B1096933
theorem B1462595 : Blo 972592 1462595 := bstep (se 1 (by rfl) ⟨1096946, by rfl⟩ : syracuseStep 1462595 = 2193893) B2193893
theorem B1233235 : Blo 972592 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B1462625 : Blo 972592 1462625 := bstep (se 2 (by rfl) ⟨548484, by rfl⟩ : syracuseStep 1462625 = 1096969) B1096969
theorem B1462643 : Blo 972592 1462643 := bstep (se 1 (by rfl) ⟨1096982, by rfl⟩ : syracuseStep 1462643 = 2193965) B2193965
theorem B2773379 : Blo 972592 2773379 := bstep (se 1 (by rfl) ⟨2080034, by rfl⟩ : syracuseStep 2773379 = 4160069) B4160069
theorem B1462673 : Blo 972592 1462673 := bstep (se 2 (by rfl) ⟨548502, by rfl⟩ : syracuseStep 1462673 = 1097005) B1097005
theorem B1462691 : Blo 972592 1462691 := bstep (se 1 (by rfl) ⟨1097018, by rfl⟩ : syracuseStep 1462691 = 2194037) B2194037
theorem B1462721 : Blo 972592 1462721 := bstep (se 2 (by rfl) ⟨548520, by rfl⟩ : syracuseStep 1462721 = 1097041) B1097041
theorem B1462739 : Blo 972592 1462739 := bstep (se 1 (by rfl) ⟨1097054, by rfl⟩ : syracuseStep 1462739 = 2194109) B2194109
theorem B1462769 : Blo 972592 1462769 := bstep (se 2 (by rfl) ⟨548538, by rfl⟩ : syracuseStep 1462769 = 1097077) B1097077
theorem B1462787 : Blo 972592 1462787 := bstep (se 1 (by rfl) ⟨1097090, by rfl⟩ : syracuseStep 1462787 = 2194181) B2194181
theorem B1462817 : Blo 972592 1462817 := bstep (se 2 (by rfl) ⟨548556, by rfl⟩ : syracuseStep 1462817 = 1097113) B1097113
theorem B1462835 : Blo 972592 1462835 := bstep (se 1 (by rfl) ⟨1097126, by rfl⟩ : syracuseStep 1462835 = 2194253) B2194253
theorem B1462865 : Blo 972592 1462865 := bstep (se 2 (by rfl) ⟨548574, by rfl⟩ : syracuseStep 1462865 = 1097149) B1097149
theorem B1462883 : Blo 972592 1462883 := bstep (se 1 (by rfl) ⟨1097162, by rfl⟩ : syracuseStep 1462883 = 2194325) B2194325
theorem B1462913 : Blo 972592 1462913 := bstep (se 2 (by rfl) ⟨548592, by rfl⟩ : syracuseStep 1462913 = 1097185) B1097185
theorem B1462931 : Blo 972592 1462931 := bstep (se 1 (by rfl) ⟨1097198, by rfl⟩ : syracuseStep 1462931 = 2194397) B2194397
theorem B1462961 : Blo 972592 1462961 := bstep (se 2 (by rfl) ⟨548610, by rfl⟩ : syracuseStep 1462961 = 1097221) B1097221
theorem B1462979 : Blo 972592 1462979 := bstep (se 1 (by rfl) ⟨1097234, by rfl⟩ : syracuseStep 1462979 = 2194469) B2194469
theorem B2773709 : Blo 972592 2773709 := bstep (se 3 (by rfl) ⟨520070, by rfl⟩ : syracuseStep 2773709 = 1040141) B1040141
theorem B5558989 : Blo 972592 5558989 := bstep (se 3 (by rfl) ⟨1042310, by rfl⟩ : syracuseStep 5558989 = 2084621) B2084621
theorem B1561313 : Blo 972592 1561313 := bstep (se 2 (by rfl) ⟨585492, by rfl⟩ : syracuseStep 1561313 = 1170985) B1170985
theorem B1463009 : Blo 972592 1463009 := bstep (se 2 (by rfl) ⟨548628, by rfl⟩ : syracuseStep 1463009 = 1097257) B1097257
theorem B38490851 : Blo 972592 38490851 := bstep (se 1 (by rfl) ⟨28868138, by rfl⟩ : syracuseStep 38490851 = 57736277) B57736277
theorem B1463027 : Blo 972592 1463027 := bstep (se 1 (by rfl) ⟨1097270, by rfl⟩ : syracuseStep 1463027 = 2194541) B2194541
theorem B2773777 : Blo 972592 2773777 := bstep (se 2 (by rfl) ⟨1040166, by rfl⟩ : syracuseStep 2773777 = 2080333) B2080333
theorem B1463057 : Blo 972592 1463057 := bstep (se 2 (by rfl) ⟨548646, by rfl⟩ : syracuseStep 1463057 = 1097293) B1097293
theorem B1463075 : Blo 972592 1463075 := bstep (se 1 (by rfl) ⟨1097306, by rfl⟩ : syracuseStep 1463075 = 2194613) B2194613
theorem B1463105 : Blo 972592 1463105 := bstep (se 2 (by rfl) ⟨548664, by rfl⟩ : syracuseStep 1463105 = 1097329) B1097329
theorem B1233731 : Blo 972592 1233731 := bstep (se 1 (by rfl) ⟨925298, by rfl⟩ : syracuseStep 1233731 = 1850597) B1850597
theorem B1463123 : Blo 972592 1463123 := bstep (se 1 (by rfl) ⟨1097342, by rfl⟩ : syracuseStep 1463123 = 2194685) B2194685
theorem B1463153 : Blo 972592 1463153 := bstep (se 2 (by rfl) ⟨548682, by rfl⟩ : syracuseStep 1463153 = 1097365) B1097365
theorem B1463171 : Blo 972592 1463171 := bstep (se 1 (by rfl) ⟨1097378, by rfl⟩ : syracuseStep 1463171 = 2194757) B2194757
theorem B8311693 : Blo 972592 8311693 := bstep (se 3 (by rfl) ⟨1558442, by rfl⟩ : syracuseStep 8311693 = 3116885) B3116885
theorem B9360269 : Blo 972592 9360269 := bstep (se 3 (by rfl) ⟨1755050, by rfl⟩ : syracuseStep 9360269 = 3510101) B3510101
theorem B1463201 : Blo 972592 1463201 := bstep (se 2 (by rfl) ⟨548700, by rfl⟩ : syracuseStep 1463201 = 1097401) B1097401
theorem B4936625 : Blo 972592 4936625 := bstep (se 2 (by rfl) ⟨1851234, by rfl⟩ : syracuseStep 4936625 = 3702469) B3702469
theorem B1463219 : Blo 972592 1463219 := bstep (se 1 (by rfl) ⟨1097414, by rfl⟩ : syracuseStep 1463219 = 2194829) B2194829
theorem B1463249 : Blo 972592 1463249 := bstep (se 2 (by rfl) ⟨548718, by rfl⟩ : syracuseStep 1463249 = 1097437) B1097437
theorem B1463267 : Blo 972592 1463267 := bstep (se 1 (by rfl) ⟨1097450, by rfl⟩ : syracuseStep 1463267 = 2194901) B2194901
theorem B1463297 : Blo 972592 1463297 := bstep (se 2 (by rfl) ⟨548736, by rfl⟩ : syracuseStep 1463297 = 1097473) B1097473
theorem B1463315 : Blo 972592 1463315 := bstep (se 1 (by rfl) ⟨1097486, by rfl⟩ : syracuseStep 1463315 = 2194973) B2194973
theorem B2774051 : Blo 972592 2774051 := bstep (se 1 (by rfl) ⟨2080538, by rfl⟩ : syracuseStep 2774051 = 4161077) B4161077
theorem B1463345 : Blo 972592 1463345 := bstep (se 2 (by rfl) ⟨548754, by rfl⟩ : syracuseStep 1463345 = 1097509) B1097509
theorem B1463363 : Blo 972592 1463363 := bstep (se 1 (by rfl) ⟨1097522, by rfl⟩ : syracuseStep 1463363 = 2195045) B2195045
theorem B1463393 : Blo 972592 1463393 := bstep (se 2 (by rfl) ⟨548772, by rfl⟩ : syracuseStep 1463393 = 1097545) B1097545
theorem B9360497 : Blo 972592 9360497 := bstep (se 2 (by rfl) ⟨3510186, by rfl⟩ : syracuseStep 9360497 = 7020373) B7020373
theorem B1463411 : Blo 972592 1463411 := bstep (se 1 (by rfl) ⟨1097558, by rfl⟩ : syracuseStep 1463411 = 2195117) B2195117
theorem B1463441 : Blo 972592 1463441 := bstep (se 2 (by rfl) ⟨548790, by rfl⟩ : syracuseStep 1463441 = 1097581) B1097581
theorem B1463459 : Blo 972592 1463459 := bstep (se 1 (by rfl) ⟨1097594, by rfl⟩ : syracuseStep 1463459 = 2195189) B2195189
theorem B1463489 : Blo 972592 1463489 := bstep (se 2 (by rfl) ⟨548808, by rfl⟩ : syracuseStep 1463489 = 1097617) B1097617
theorem B1463507 : Blo 972592 1463507 := bstep (se 1 (by rfl) ⟨1097630, by rfl⟩ : syracuseStep 1463507 = 2195261) B2195261
theorem B3953891 : Blo 972592 3953891 := bstep (se 1 (by rfl) ⟨2965418, by rfl⟩ : syracuseStep 3953891 = 5930837) B5930837
theorem B1463537 : Blo 972592 1463537 := bstep (se 2 (by rfl) ⟨548826, by rfl⟩ : syracuseStep 1463537 = 1097653) B1097653
theorem B1463555 : Blo 972592 1463555 := bstep (se 1 (by rfl) ⟨1097666, by rfl⟩ : syracuseStep 1463555 = 2195333) B2195333
theorem B1463585 : Blo 972592 1463585 := bstep (se 2 (by rfl) ⟨548844, by rfl⟩ : syracuseStep 1463585 = 1097689) B1097689
theorem B1463603 : Blo 972592 1463603 := bstep (se 1 (by rfl) ⟨1097702, by rfl⟩ : syracuseStep 1463603 = 2195405) B2195405
theorem B1463633 : Blo 972592 1463633 := bstep (se 2 (by rfl) ⟨548862, by rfl⟩ : syracuseStep 1463633 = 1097725) B1097725
theorem B1463651 : Blo 972592 1463651 := bstep (se 1 (by rfl) ⟨1097738, by rfl⟩ : syracuseStep 1463651 = 2195477) B2195477
theorem B1463681 : Blo 972592 1463681 := bstep (se 2 (by rfl) ⟨548880, by rfl⟩ : syracuseStep 1463681 = 1097761) B1097761
theorem B47502733 : Blo 972592 47502733 := bstep (se 3 (by rfl) ⟨8906762, by rfl⟩ : syracuseStep 47502733 = 17813525) B17813525
theorem B1463699 : Blo 972592 1463699 := bstep (se 1 (by rfl) ⟨1097774, by rfl⟩ : syracuseStep 1463699 = 2195549) B2195549
theorem B1463729 : Blo 972592 1463729 := bstep (se 2 (by rfl) ⟨548898, by rfl⟩ : syracuseStep 1463729 = 1097797) B1097797
theorem B1463747 : Blo 972592 1463747 := bstep (se 1 (by rfl) ⟨1097810, by rfl⟩ : syracuseStep 1463747 = 2195621) B2195621
theorem B1463777 : Blo 972592 1463777 := bstep (se 2 (by rfl) ⟨548916, by rfl⟩ : syracuseStep 1463777 = 1097833) B1097833
theorem B1463795 : Blo 972592 1463795 := bstep (se 1 (by rfl) ⟨1097846, by rfl⟩ : syracuseStep 1463795 = 2195693) B2195693
theorem B1234435 : Blo 972592 1234435 := bstep (se 1 (by rfl) ⟨925826, by rfl⟩ : syracuseStep 1234435 = 1851653) B1851653
theorem B1463825 : Blo 972592 1463825 := bstep (se 2 (by rfl) ⟨548934, by rfl⟩ : syracuseStep 1463825 = 1097869) B1097869
theorem B1463843 : Blo 972592 1463843 := bstep (se 1 (by rfl) ⟨1097882, by rfl⟩ : syracuseStep 1463843 = 2195765) B2195765
theorem B1463873 : Blo 972592 1463873 := bstep (se 2 (by rfl) ⟨548952, by rfl⟩ : syracuseStep 1463873 = 1097905) B1097905
theorem B1562179 : Blo 972592 1562179 := bstep (se 1 (by rfl) ⟨1171634, by rfl⟩ : syracuseStep 1562179 = 2343269) B2343269
theorem B1463891 : Blo 972592 1463891 := bstep (se 1 (by rfl) ⟨1097918, by rfl⟩ : syracuseStep 1463891 = 2195837) B2195837
theorem B1234531 : Blo 972592 1234531 := bstep (se 1 (by rfl) ⟨925898, by rfl⟩ : syracuseStep 1234531 = 1851797) B1851797
theorem B1463921 : Blo 972592 1463921 := bstep (se 2 (by rfl) ⟨548970, by rfl⟩ : syracuseStep 1463921 = 1097941) B1097941
theorem B1463939 : Blo 972592 1463939 := bstep (se 1 (by rfl) ⟨1097954, by rfl⟩ : syracuseStep 1463939 = 2195909) B2195909
theorem B1463969 : Blo 972592 1463969 := bstep (se 2 (by rfl) ⟨548988, by rfl⟩ : syracuseStep 1463969 = 1097977) B1097977
theorem B1463987 : Blo 972592 1463987 := bstep (se 1 (by rfl) ⟨1097990, by rfl⟩ : syracuseStep 1463987 = 2195981) B2195981
theorem B1464017 : Blo 972592 1464017 := bstep (se 2 (by rfl) ⟨549006, by rfl⟩ : syracuseStep 1464017 = 1098013) B1098013
theorem B1464035 : Blo 972592 1464035 := bstep (se 1 (by rfl) ⟨1098026, by rfl⟩ : syracuseStep 1464035 = 2196053) B2196053
theorem B6248177 : Blo 972592 6248177 := bstep (se 2 (by rfl) ⟨2343066, by rfl⟩ : syracuseStep 6248177 = 4686133) B4686133
theorem B1464065 : Blo 972592 1464065 := bstep (se 2 (by rfl) ⟨549024, by rfl⟩ : syracuseStep 1464065 = 1098049) B1098049
theorem B1464083 : Blo 972592 1464083 := bstep (se 1 (by rfl) ⟨1098062, by rfl⟩ : syracuseStep 1464083 = 2196125) B2196125
theorem B1464113 : Blo 972592 1464113 := bstep (se 2 (by rfl) ⟨549042, by rfl⟩ : syracuseStep 1464113 = 1098085) B1098085
theorem B972595 : Blo 972592 972595 := bstep (se 1 (by rfl) ⟨729446, by rfl⟩ : syracuseStep 972595 = 1458893) B1458893
theorem B972611 : Blo 972592 972611 := bstep (se 1 (by rfl) ⟨729458, by rfl⟩ : syracuseStep 972611 = 1458917) B1458917
theorem B3168067 : Blo 972592 3168067 := bstep (se 1 (by rfl) ⟨2376050, by rfl⟩ : syracuseStep 3168067 = 4752101) B4752101
theorem B1464131 : Blo 972592 1464131 := bstep (se 1 (by rfl) ⟨1098098, by rfl⟩ : syracuseStep 1464131 = 2196197) B2196197
theorem B972627 : Blo 972592 972627 := bstep (se 1 (by rfl) ⟨729470, by rfl⟩ : syracuseStep 972627 = 1458941) B1458941
theorem B1464161 : Blo 972592 1464161 := bstep (se 2 (by rfl) ⟨549060, by rfl⟩ : syracuseStep 1464161 = 1098121) B1098121
theorem B972643 : Blo 972592 972643 := bstep (se 1 (by rfl) ⟨729482, by rfl⟩ : syracuseStep 972643 = 1458965) B1458965
theorem B2774893 : Blo 972592 2774893 := bstep (se 3 (by rfl) ⟨520292, by rfl⟩ : syracuseStep 2774893 = 1040585) B1040585
theorem B972659 : Blo 972592 972659 := bstep (se 1 (by rfl) ⟨729494, by rfl⟩ : syracuseStep 972659 = 1458989) B1458989
theorem B1464179 : Blo 972592 1464179 := bstep (se 1 (by rfl) ⟨1098134, by rfl⟩ : syracuseStep 1464179 = 2196269) B2196269
theorem B972675 : Blo 972592 972675 := bstep (se 1 (by rfl) ⟨729506, by rfl⟩ : syracuseStep 972675 = 1459013) B1459013
theorem B16013197 : Blo 972592 16013197 := bstep (se 3 (by rfl) ⟨3002474, by rfl⟩ : syracuseStep 16013197 = 6004949) B6004949
theorem B1464209 : Blo 972592 1464209 := bstep (se 2 (by rfl) ⟨549078, by rfl⟩ : syracuseStep 1464209 = 1098157) B1098157
theorem B972691 : Blo 972592 972691 := bstep (se 1 (by rfl) ⟨729518, by rfl⟩ : syracuseStep 972691 = 1459037) B1459037
theorem B972707 : Blo 972592 972707 := bstep (se 1 (by rfl) ⟨729530, by rfl⟩ : syracuseStep 972707 = 1459061) B1459061
theorem B1464227 : Blo 972592 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B972723 : Blo 972592 972723 := bstep (se 1 (by rfl) ⟨729542, by rfl⟩ : syracuseStep 972723 = 1459085) B1459085
theorem B1464257 : Blo 972592 1464257 := bstep (se 2 (by rfl) ⟨549096, by rfl⟩ : syracuseStep 1464257 = 1098193) B1098193
theorem B972739 : Blo 972592 972739 := bstep (se 1 (by rfl) ⟨729554, by rfl⟩ : syracuseStep 972739 = 1459109) B1459109
theorem B972755 : Blo 972592 972755 := bstep (se 1 (by rfl) ⟨729566, by rfl⟩ : syracuseStep 972755 = 1459133) B1459133
theorem B1464275 : Blo 972592 1464275 := bstep (se 1 (by rfl) ⟨1098206, by rfl⟩ : syracuseStep 1464275 = 2196413) B2196413
theorem B972771 : Blo 972592 972771 := bstep (se 1 (by rfl) ⟨729578, by rfl⟩ : syracuseStep 972771 = 1459157) B1459157
theorem B1464305 : Blo 972592 1464305 := bstep (se 2 (by rfl) ⟨549114, by rfl⟩ : syracuseStep 1464305 = 1098229) B1098229
theorem B972787 : Blo 972592 972787 := bstep (se 1 (by rfl) ⟨729590, by rfl⟩ : syracuseStep 972787 = 1459181) B1459181
theorem B972803 : Blo 972592 972803 := bstep (se 1 (by rfl) ⟨729602, by rfl⟩ : syracuseStep 972803 = 1459205) B1459205
theorem B1464323 : Blo 972592 1464323 := bstep (se 1 (by rfl) ⟨1098242, by rfl⟩ : syracuseStep 1464323 = 2196485) B2196485
theorem B2775053 : Blo 972592 2775053 := bstep (se 3 (by rfl) ⟨520322, by rfl⟩ : syracuseStep 2775053 = 1040645) B1040645
theorem B972819 : Blo 972592 972819 := bstep (se 1 (by rfl) ⟨729614, by rfl⟩ : syracuseStep 972819 = 1459229) B1459229
theorem B1464353 : Blo 972592 1464353 := bstep (se 2 (by rfl) ⟨549132, by rfl⟩ : syracuseStep 1464353 = 1098265) B1098265
theorem B972835 : Blo 972592 972835 := bstep (se 1 (by rfl) ⟨729626, by rfl⟩ : syracuseStep 972835 = 1459253) B1459253
theorem B972851 : Blo 972592 972851 := bstep (se 1 (by rfl) ⟨729638, by rfl⟩ : syracuseStep 972851 = 1459277) B1459277
theorem B1464371 : Blo 972592 1464371 := bstep (se 1 (by rfl) ⟨1098278, by rfl⟩ : syracuseStep 1464371 = 2196557) B2196557
theorem B972867 : Blo 972592 972867 := bstep (se 1 (by rfl) ⟨729650, by rfl⟩ : syracuseStep 972867 = 1459301) B1459301
theorem B1464401 : Blo 972592 1464401 := bstep (se 2 (by rfl) ⟨549150, by rfl⟩ : syracuseStep 1464401 = 1098301) B1098301
theorem B972883 : Blo 972592 972883 := bstep (se 1 (by rfl) ⟨729662, by rfl⟩ : syracuseStep 972883 = 1459325) B1459325
theorem B1235027 : Blo 972592 1235027 := bstep (se 1 (by rfl) ⟨926270, by rfl⟩ : syracuseStep 1235027 = 1852541) B1852541
theorem B972899 : Blo 972592 972899 := bstep (se 1 (by rfl) ⟨729674, by rfl⟩ : syracuseStep 972899 = 1459349) B1459349
theorem B1464419 : Blo 972592 1464419 := bstep (se 1 (by rfl) ⟨1098314, by rfl⟩ : syracuseStep 1464419 = 2196629) B2196629
theorem B972915 : Blo 972592 972915 := bstep (se 1 (by rfl) ⟨729686, by rfl⟩ : syracuseStep 972915 = 1459373) B1459373
theorem B1464449 : Blo 972592 1464449 := bstep (se 2 (by rfl) ⟨549168, by rfl⟩ : syracuseStep 1464449 = 1098337) B1098337
theorem B972931 : Blo 972592 972931 := bstep (se 1 (by rfl) ⟨729698, by rfl⟩ : syracuseStep 972931 = 1459397) B1459397
theorem B972947 : Blo 972592 972947 := bstep (se 1 (by rfl) ⟨729710, by rfl⟩ : syracuseStep 972947 = 1459421) B1459421
theorem B1464467 : Blo 972592 1464467 := bstep (se 1 (by rfl) ⟨1098350, by rfl⟩ : syracuseStep 1464467 = 2196701) B2196701
theorem B972963 : Blo 972592 972963 := bstep (se 1 (by rfl) ⟨729722, by rfl⟩ : syracuseStep 972963 = 1459445) B1459445
theorem B1464497 : Blo 972592 1464497 := bstep (se 2 (by rfl) ⟨549186, by rfl⟩ : syracuseStep 1464497 = 1098373) B1098373
theorem B972979 : Blo 972592 972979 := bstep (se 1 (by rfl) ⟨729734, by rfl⟩ : syracuseStep 972979 = 1459469) B1459469
theorem B12507317 : Blo 972592 12507317 := bstep (se 5 (by rfl) ⟨586280, by rfl⟩ : syracuseStep 12507317 = 1172561) B1172561
theorem B972995 : Blo 972592 972995 := bstep (se 1 (by rfl) ⟨729746, by rfl⟩ : syracuseStep 972995 = 1459493) B1459493
theorem B2775235 : Blo 972592 2775235 := bstep (se 1 (by rfl) ⟨2081426, by rfl⟩ : syracuseStep 2775235 = 4162853) B4162853
theorem B8313029 : Blo 972592 8313029 := bstep (se 4 (by rfl) ⟨779346, by rfl⟩ : syracuseStep 8313029 = 1558693) B1558693
theorem B1464515 : Blo 972592 1464515 := bstep (se 1 (by rfl) ⟨1098386, by rfl⟩ : syracuseStep 1464515 = 2196773) B2196773
theorem B973011 : Blo 972592 973011 := bstep (se 1 (by rfl) ⟨729758, by rfl⟩ : syracuseStep 973011 = 1459517) B1459517
theorem B1464545 : Blo 972592 1464545 := bstep (se 2 (by rfl) ⟨549204, by rfl⟩ : syracuseStep 1464545 = 1098409) B1098409
theorem B973027 : Blo 972592 973027 := bstep (se 1 (by rfl) ⟨729770, by rfl⟩ : syracuseStep 973027 = 1459541) B1459541
theorem B1562851 : Blo 972592 1562851 := bstep (se 1 (by rfl) ⟨1172138, by rfl⟩ : syracuseStep 1562851 = 2344277) B2344277
theorem B5921009 : Blo 972592 5921009 := bstep (se 2 (by rfl) ⟨2220378, by rfl⟩ : syracuseStep 5921009 = 4440757) B4440757
theorem B973043 : Blo 972592 973043 := bstep (se 1 (by rfl) ⟨729782, by rfl⟩ : syracuseStep 973043 = 1459565) B1459565
theorem B1464563 : Blo 972592 1464563 := bstep (se 1 (by rfl) ⟨1098422, by rfl⟩ : syracuseStep 1464563 = 2196845) B2196845
theorem B973059 : Blo 972592 973059 := bstep (se 1 (by rfl) ⟨729794, by rfl⟩ : syracuseStep 973059 = 1459589) B1459589
theorem B1562897 : Blo 972592 1562897 := bstep (se 2 (by rfl) ⟨586086, by rfl⟩ : syracuseStep 1562897 = 1172173) B1172173
theorem B1464593 : Blo 972592 1464593 := bstep (se 2 (by rfl) ⟨549222, by rfl⟩ : syracuseStep 1464593 = 1098445) B1098445
theorem B973075 : Blo 972592 973075 := bstep (se 1 (by rfl) ⟨729806, by rfl⟩ : syracuseStep 973075 = 1459613) B1459613
theorem B973091 : Blo 972592 973091 := bstep (se 1 (by rfl) ⟨729818, by rfl⟩ : syracuseStep 973091 = 1459637) B1459637
theorem B1464611 : Blo 972592 1464611 := bstep (se 1 (by rfl) ⟨1098458, by rfl⟩ : syracuseStep 1464611 = 2196917) B2196917
theorem B973107 : Blo 972592 973107 := bstep (se 1 (by rfl) ⟨729830, by rfl⟩ : syracuseStep 973107 = 1459661) B1459661
theorem B1464641 : Blo 972592 1464641 := bstep (se 2 (by rfl) ⟨549240, by rfl⟩ : syracuseStep 1464641 = 1098481) B1098481
theorem B973123 : Blo 972592 973123 := bstep (se 1 (by rfl) ⟨729842, by rfl⟩ : syracuseStep 973123 = 1459685) B1459685
theorem B973139 : Blo 972592 973139 := bstep (se 1 (by rfl) ⟨729854, by rfl⟩ : syracuseStep 973139 = 1459709) B1459709
theorem B1464659 : Blo 972592 1464659 := bstep (se 1 (by rfl) ⟨1098494, by rfl⟩ : syracuseStep 1464659 = 2196989) B2196989
theorem B973155 : Blo 972592 973155 := bstep (se 1 (by rfl) ⟨729866, by rfl⟩ : syracuseStep 973155 = 1459733) B1459733
theorem B4938083 : Blo 972592 4938083 := bstep (se 1 (by rfl) ⟨3703562, by rfl⟩ : syracuseStep 4938083 = 7407125) B7407125
theorem B1464689 : Blo 972592 1464689 := bstep (se 2 (by rfl) ⟨549258, by rfl⟩ : syracuseStep 1464689 = 1098517) B1098517
theorem B973171 : Blo 972592 973171 := bstep (se 1 (by rfl) ⟨729878, by rfl⟩ : syracuseStep 973171 = 1459757) B1459757
theorem B973187 : Blo 972592 973187 := bstep (se 1 (by rfl) ⟨729890, by rfl⟩ : syracuseStep 973187 = 1459781) B1459781
theorem B1464707 : Blo 972592 1464707 := bstep (se 1 (by rfl) ⟨1098530, by rfl⟩ : syracuseStep 1464707 = 2197061) B2197061
theorem B973203 : Blo 972592 973203 := bstep (se 1 (by rfl) ⟨729902, by rfl⟩ : syracuseStep 973203 = 1459805) B1459805
theorem B1464737 : Blo 972592 1464737 := bstep (se 2 (by rfl) ⟨549276, by rfl⟩ : syracuseStep 1464737 = 1098553) B1098553
theorem B973219 : Blo 972592 973219 := bstep (se 1 (by rfl) ⟨729914, by rfl⟩ : syracuseStep 973219 = 1459829) B1459829
theorem B973235 : Blo 972592 973235 := bstep (se 1 (by rfl) ⟨729926, by rfl⟩ : syracuseStep 973235 = 1459853) B1459853
theorem B1464755 : Blo 972592 1464755 := bstep (se 1 (by rfl) ⟨1098566, by rfl⟩ : syracuseStep 1464755 = 2197133) B2197133
theorem B973251 : Blo 972592 973251 := bstep (se 1 (by rfl) ⟨729938, by rfl⟩ : syracuseStep 973251 = 1459877) B1459877
theorem B1464785 : Blo 972592 1464785 := bstep (se 2 (by rfl) ⟨549294, by rfl⟩ : syracuseStep 1464785 = 1098589) B1098589
theorem B973267 : Blo 972592 973267 := bstep (se 1 (by rfl) ⟨729950, by rfl⟩ : syracuseStep 973267 = 1459901) B1459901
theorem B973283 : Blo 972592 973283 := bstep (se 1 (by rfl) ⟨729962, by rfl⟩ : syracuseStep 973283 = 1459925) B1459925
theorem B1464803 : Blo 972592 1464803 := bstep (se 1 (by rfl) ⟨1098602, by rfl⟩ : syracuseStep 1464803 = 2197205) B2197205
theorem B973299 : Blo 972592 973299 := bstep (se 1 (by rfl) ⟨729974, by rfl⟩ : syracuseStep 973299 = 1459949) B1459949
theorem B1464833 : Blo 972592 1464833 := bstep (se 2 (by rfl) ⟨549312, by rfl⟩ : syracuseStep 1464833 = 1098625) B1098625
theorem B973315 : Blo 972592 973315 := bstep (se 1 (by rfl) ⟨729986, by rfl⟩ : syracuseStep 973315 = 1459973) B1459973
theorem B973331 : Blo 972592 973331 := bstep (se 1 (by rfl) ⟨729998, by rfl⟩ : syracuseStep 973331 = 1459997) B1459997
theorem B1464851 : Blo 972592 1464851 := bstep (se 1 (by rfl) ⟨1098638, by rfl⟩ : syracuseStep 1464851 = 2197277) B2197277
theorem B973347 : Blo 972592 973347 := bstep (se 1 (by rfl) ⟨730010, by rfl⟩ : syracuseStep 973347 = 1460021) B1460021
theorem B1464881 : Blo 972592 1464881 := bstep (se 2 (by rfl) ⟨549330, by rfl⟩ : syracuseStep 1464881 = 1098661) B1098661
theorem B973363 : Blo 972592 973363 := bstep (se 1 (by rfl) ⟨730022, by rfl⟩ : syracuseStep 973363 = 1460045) B1460045
theorem B973379 : Blo 972592 973379 := bstep (se 1 (by rfl) ⟨730034, by rfl⟩ : syracuseStep 973379 = 1460069) B1460069
theorem B973395 : Blo 972592 973395 := bstep (se 1 (by rfl) ⟨730046, by rfl⟩ : syracuseStep 973395 = 1460093) B1460093
theorem B973411 : Blo 972592 973411 := bstep (se 1 (by rfl) ⟨730058, by rfl⟩ : syracuseStep 973411 = 1460117) B1460117
theorem B973427 : Blo 972592 973427 := bstep (se 1 (by rfl) ⟨730070, by rfl⟩ : syracuseStep 973427 = 1460141) B1460141
theorem B973443 : Blo 972592 973443 := bstep (se 1 (by rfl) ⟨730082, by rfl⟩ : syracuseStep 973443 = 1460165) B1460165
theorem B5560973 : Blo 972592 5560973 := bstep (se 3 (by rfl) ⟨1042682, by rfl⟩ : syracuseStep 5560973 = 2085365) B2085365
theorem B973459 : Blo 972592 973459 := bstep (se 1 (by rfl) ⟨730094, by rfl⟩ : syracuseStep 973459 = 1460189) B1460189
theorem B973475 : Blo 972592 973475 := bstep (se 1 (by rfl) ⟨730106, by rfl⟩ : syracuseStep 973475 = 1460213) B1460213
theorem B973491 : Blo 972592 973491 := bstep (se 1 (by rfl) ⟨730118, by rfl⟩ : syracuseStep 973491 = 1460237) B1460237
theorem B973507 : Blo 972592 973507 := bstep (se 1 (by rfl) ⟨730130, by rfl⟩ : syracuseStep 973507 = 1460261) B1460261
theorem B6675149 : Blo 972592 6675149 := bstep (se 3 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 6675149 = 2503181) B2503181
theorem B973523 : Blo 972592 973523 := bstep (se 1 (by rfl) ⟨730142, by rfl⟩ : syracuseStep 973523 = 1460285) B1460285
theorem B973539 : Blo 972592 973539 := bstep (se 1 (by rfl) ⟨730154, by rfl⟩ : syracuseStep 973539 = 1460309) B1460309
theorem B973555 : Blo 972592 973555 := bstep (se 1 (by rfl) ⟨730166, by rfl⟩ : syracuseStep 973555 = 1460333) B1460333
theorem B973571 : Blo 972592 973571 := bstep (se 1 (by rfl) ⟨730178, by rfl⟩ : syracuseStep 973571 = 1460357) B1460357
theorem B1563409 : Blo 972592 1563409 := bstep (se 2 (by rfl) ⟨586278, by rfl⟩ : syracuseStep 1563409 = 1172557) B1172557
theorem B973587 : Blo 972592 973587 := bstep (se 1 (by rfl) ⟨730190, by rfl⟩ : syracuseStep 973587 = 1460381) B1460381
theorem B1235731 : Blo 972592 1235731 := bstep (se 1 (by rfl) ⟨926798, by rfl⟩ : syracuseStep 1235731 = 1853597) B1853597
theorem B973603 : Blo 972592 973603 := bstep (se 1 (by rfl) ⟨730202, by rfl⟩ : syracuseStep 973603 = 1460405) B1460405
theorem B6249251 : Blo 972592 6249251 := bstep (se 1 (by rfl) ⟨4686938, by rfl⟩ : syracuseStep 6249251 = 9373877) B9373877
theorem B973619 : Blo 972592 973619 := bstep (se 1 (by rfl) ⟨730214, by rfl⟩ : syracuseStep 973619 = 1460429) B1460429
theorem B973635 : Blo 972592 973635 := bstep (se 1 (by rfl) ⟨730226, by rfl⟩ : syracuseStep 973635 = 1460453) B1460453
theorem B973651 : Blo 972592 973651 := bstep (se 1 (by rfl) ⟨730238, by rfl⟩ : syracuseStep 973651 = 1460477) B1460477
theorem B973667 : Blo 972592 973667 := bstep (se 1 (by rfl) ⟨730250, by rfl⟩ : syracuseStep 973667 = 1460501) B1460501
theorem B973683 : Blo 972592 973683 := bstep (se 1 (by rfl) ⟨730262, by rfl⟩ : syracuseStep 973683 = 1460525) B1460525
theorem B1235827 : Blo 972592 1235827 := bstep (se 1 (by rfl) ⟨926870, by rfl⟩ : syracuseStep 1235827 = 1853741) B1853741
theorem B1039235 : Blo 972592 1039235 := bstep (se 1 (by rfl) ⟨779426, by rfl⟩ : syracuseStep 1039235 = 1558853) B1558853
theorem B973699 : Blo 972592 973699 := bstep (se 1 (by rfl) ⟨730274, by rfl⟩ : syracuseStep 973699 = 1460549) B1460549
theorem B973715 : Blo 972592 973715 := bstep (se 1 (by rfl) ⟨730286, by rfl⟩ : syracuseStep 973715 = 1460573) B1460573
theorem B973731 : Blo 972592 973731 := bstep (se 1 (by rfl) ⟨730298, by rfl⟩ : syracuseStep 973731 = 1460597) B1460597
theorem B973747 : Blo 972592 973747 := bstep (se 1 (by rfl) ⟨730310, by rfl⟩ : syracuseStep 973747 = 1460621) B1460621
theorem B973763 : Blo 972592 973763 := bstep (se 1 (by rfl) ⟨730322, by rfl⟩ : syracuseStep 973763 = 1460645) B1460645
theorem B973779 : Blo 972592 973779 := bstep (se 1 (by rfl) ⟨730334, by rfl⟩ : syracuseStep 973779 = 1460669) B1460669
theorem B3693539 : Blo 972592 3693539 := bstep (se 1 (by rfl) ⟨2770154, by rfl⟩ : syracuseStep 3693539 = 5540309) B5540309
theorem B973795 : Blo 972592 973795 := bstep (se 1 (by rfl) ⟨730346, by rfl⟩ : syracuseStep 973795 = 1460693) B1460693
theorem B973811 : Blo 972592 973811 := bstep (se 1 (by rfl) ⟨730358, by rfl⟩ : syracuseStep 973811 = 1460717) B1460717
theorem B973827 : Blo 972592 973827 := bstep (se 1 (by rfl) ⟨730370, by rfl⟩ : syracuseStep 973827 = 1460741) B1460741
theorem B973843 : Blo 972592 973843 := bstep (se 1 (by rfl) ⟨730382, by rfl⟩ : syracuseStep 973843 = 1460765) B1460765
theorem B973859 : Blo 972592 973859 := bstep (se 1 (by rfl) ⟨730394, by rfl⟩ : syracuseStep 973859 = 1460789) B1460789
theorem B973875 : Blo 972592 973875 := bstep (se 1 (by rfl) ⟨730406, by rfl⟩ : syracuseStep 973875 = 1460813) B1460813
theorem B973891 : Blo 972592 973891 := bstep (se 1 (by rfl) ⟨730418, by rfl⟩ : syracuseStep 973891 = 1460837) B1460837
theorem B973907 : Blo 972592 973907 := bstep (se 1 (by rfl) ⟨730430, by rfl⟩ : syracuseStep 973907 = 1460861) B1460861
theorem B973923 : Blo 972592 973923 := bstep (se 1 (by rfl) ⟨730442, by rfl⟩ : syracuseStep 973923 = 1460885) B1460885
theorem B973939 : Blo 972592 973939 := bstep (se 1 (by rfl) ⟨730454, by rfl⟩ : syracuseStep 973939 = 1460909) B1460909
theorem B973955 : Blo 972592 973955 := bstep (se 1 (by rfl) ⟨730466, by rfl⟩ : syracuseStep 973955 = 1460933) B1460933
theorem B4938893 : Blo 972592 4938893 := bstep (se 3 (by rfl) ⟨926042, by rfl⟩ : syracuseStep 4938893 = 1852085) B1852085
theorem B973971 : Blo 972592 973971 := bstep (se 1 (by rfl) ⟨730478, by rfl⟩ : syracuseStep 973971 = 1460957) B1460957
theorem B973987 : Blo 972592 973987 := bstep (se 1 (by rfl) ⟨730490, by rfl⟩ : syracuseStep 973987 = 1460981) B1460981
theorem B974003 : Blo 972592 974003 := bstep (se 1 (by rfl) ⟨730502, by rfl⟩ : syracuseStep 974003 = 1461005) B1461005
theorem B974019 : Blo 972592 974019 := bstep (se 1 (by rfl) ⟨730514, by rfl⟩ : syracuseStep 974019 = 1461029) B1461029
theorem B974035 : Blo 972592 974035 := bstep (se 1 (by rfl) ⟨730526, by rfl⟩ : syracuseStep 974035 = 1461053) B1461053
theorem B974051 : Blo 972592 974051 := bstep (se 1 (by rfl) ⟨730538, by rfl⟩ : syracuseStep 974051 = 1461077) B1461077
theorem B974067 : Blo 972592 974067 := bstep (se 1 (by rfl) ⟨730550, by rfl⟩ : syracuseStep 974067 = 1461101) B1461101
theorem B974083 : Blo 972592 974083 := bstep (se 1 (by rfl) ⟨730562, by rfl⟩ : syracuseStep 974083 = 1461125) B1461125
theorem B974099 : Blo 972592 974099 := bstep (se 1 (by rfl) ⟨730574, by rfl⟩ : syracuseStep 974099 = 1461149) B1461149
theorem B974115 : Blo 972592 974115 := bstep (se 1 (by rfl) ⟨730586, by rfl⟩ : syracuseStep 974115 = 1461173) B1461173
theorem B3956003 : Blo 972592 3956003 := bstep (se 1 (by rfl) ⟨2967002, by rfl⟩ : syracuseStep 3956003 = 5934005) B5934005
theorem B1563953 : Blo 972592 1563953 := bstep (se 2 (by rfl) ⟨586482, by rfl⟩ : syracuseStep 1563953 = 1172965) B1172965
theorem B974131 : Blo 972592 974131 := bstep (se 1 (by rfl) ⟨730598, by rfl⟩ : syracuseStep 974131 = 1461197) B1461197
theorem B974147 : Blo 972592 974147 := bstep (se 1 (by rfl) ⟨730610, by rfl⟩ : syracuseStep 974147 = 1461221) B1461221
theorem B974163 : Blo 972592 974163 := bstep (se 1 (by rfl) ⟨730622, by rfl⟩ : syracuseStep 974163 = 1461245) B1461245
theorem B974179 : Blo 972592 974179 := bstep (se 1 (by rfl) ⟨730634, by rfl⟩ : syracuseStep 974179 = 1461269) B1461269
theorem B974195 : Blo 972592 974195 := bstep (se 1 (by rfl) ⟨730646, by rfl⟩ : syracuseStep 974195 = 1461293) B1461293
theorem B974211 : Blo 972592 974211 := bstep (se 1 (by rfl) ⟨730658, by rfl⟩ : syracuseStep 974211 = 1461317) B1461317
theorem B974227 : Blo 972592 974227 := bstep (se 1 (by rfl) ⟨730670, by rfl⟩ : syracuseStep 974227 = 1461341) B1461341
theorem B974243 : Blo 972592 974243 := bstep (se 1 (by rfl) ⟨730682, by rfl⟩ : syracuseStep 974243 = 1461365) B1461365
theorem B974259 : Blo 972592 974259 := bstep (se 1 (by rfl) ⟨730694, by rfl⟩ : syracuseStep 974259 = 1461389) B1461389
theorem B974275 : Blo 972592 974275 := bstep (se 1 (by rfl) ⟨730706, by rfl⟩ : syracuseStep 974275 = 1461413) B1461413
theorem B17817029 : Blo 972592 17817029 := bstep (se 4 (by rfl) ⟨1670346, by rfl⟩ : syracuseStep 17817029 = 3340693) B3340693
theorem B974291 : Blo 972592 974291 := bstep (se 1 (by rfl) ⟨730718, by rfl⟩ : syracuseStep 974291 = 1461437) B1461437
theorem B974307 : Blo 972592 974307 := bstep (se 1 (by rfl) ⟨730730, by rfl⟩ : syracuseStep 974307 = 1461461) B1461461
theorem B974323 : Blo 972592 974323 := bstep (se 1 (by rfl) ⟨730742, by rfl⟩ : syracuseStep 974323 = 1461485) B1461485
theorem B974339 : Blo 972592 974339 := bstep (se 1 (by rfl) ⟨730754, by rfl⟩ : syracuseStep 974339 = 1461509) B1461509
theorem B974355 : Blo 972592 974355 := bstep (se 1 (by rfl) ⟨730766, by rfl⟩ : syracuseStep 974355 = 1461533) B1461533
theorem B974371 : Blo 972592 974371 := bstep (se 1 (by rfl) ⟨730778, by rfl⟩ : syracuseStep 974371 = 1461557) B1461557
theorem B2776625 : Blo 972592 2776625 := bstep (se 2 (by rfl) ⟨1041234, by rfl⟩ : syracuseStep 2776625 = 2082469) B2082469
theorem B5561905 : Blo 972592 5561905 := bstep (se 2 (by rfl) ⟨2085714, by rfl⟩ : syracuseStep 5561905 = 4171429) B4171429
theorem B974387 : Blo 972592 974387 := bstep (se 1 (by rfl) ⟨730790, by rfl⟩ : syracuseStep 974387 = 1461581) B1461581
theorem B974403 : Blo 972592 974403 := bstep (se 1 (by rfl) ⟨730802, by rfl⟩ : syracuseStep 974403 = 1461605) B1461605
theorem B974419 : Blo 972592 974419 := bstep (se 1 (by rfl) ⟨730814, by rfl⟩ : syracuseStep 974419 = 1461629) B1461629
theorem B974435 : Blo 972592 974435 := bstep (se 1 (by rfl) ⟨730826, by rfl⟩ : syracuseStep 974435 = 1461653) B1461653
theorem B3694193 : Blo 972592 3694193 := bstep (se 2 (by rfl) ⟨1385322, by rfl⟩ : syracuseStep 3694193 = 2770645) B2770645
theorem B1039987 : Blo 972592 1039987 := bstep (se 1 (by rfl) ⟨779990, by rfl⟩ : syracuseStep 1039987 = 1559981) B1559981
theorem B974451 : Blo 972592 974451 := bstep (se 1 (by rfl) ⟨730838, by rfl⟩ : syracuseStep 974451 = 1461677) B1461677
theorem B974467 : Blo 972592 974467 := bstep (se 1 (by rfl) ⟨730850, by rfl⟩ : syracuseStep 974467 = 1461701) B1461701
theorem B974483 : Blo 972592 974483 := bstep (se 1 (by rfl) ⟨730862, by rfl⟩ : syracuseStep 974483 = 1461725) B1461725
theorem B974499 : Blo 972592 974499 := bstep (se 1 (by rfl) ⟨730874, by rfl⟩ : syracuseStep 974499 = 1461749) B1461749
theorem B974515 : Blo 972592 974515 := bstep (se 1 (by rfl) ⟨730886, by rfl⟩ : syracuseStep 974515 = 1461773) B1461773
theorem B974531 : Blo 972592 974531 := bstep (se 1 (by rfl) ⟨730898, by rfl⟩ : syracuseStep 974531 = 1461797) B1461797
theorem B974547 : Blo 972592 974547 := bstep (se 1 (by rfl) ⟨730910, by rfl⟩ : syracuseStep 974547 = 1461821) B1461821
theorem B974563 : Blo 972592 974563 := bstep (se 1 (by rfl) ⟨730922, by rfl⟩ : syracuseStep 974563 = 1461845) B1461845
theorem B1335025 : Blo 972592 1335025 := bstep (se 2 (by rfl) ⟨500634, by rfl⟩ : syracuseStep 1335025 = 1001269) B1001269
theorem B974579 : Blo 972592 974579 := bstep (se 1 (by rfl) ⟨730934, by rfl⟩ : syracuseStep 974579 = 1461869) B1461869
theorem B974595 : Blo 972592 974595 := bstep (se 1 (by rfl) ⟨730946, by rfl⟩ : syracuseStep 974595 = 1461893) B1461893
theorem B974611 : Blo 972592 974611 := bstep (se 1 (by rfl) ⟨730958, by rfl⟩ : syracuseStep 974611 = 1461917) B1461917
theorem B974627 : Blo 972592 974627 := bstep (se 1 (by rfl) ⟨730970, by rfl⟩ : syracuseStep 974627 = 1461941) B1461941
theorem B974643 : Blo 972592 974643 := bstep (se 1 (by rfl) ⟨730982, by rfl⟩ : syracuseStep 974643 = 1461965) B1461965
theorem B974659 : Blo 972592 974659 := bstep (se 1 (by rfl) ⟨730994, by rfl⟩ : syracuseStep 974659 = 1461989) B1461989
theorem B2744131 : Blo 972592 2744131 := bstep (se 1 (by rfl) ⟨2058098, by rfl⟩ : syracuseStep 2744131 = 4116197) B4116197
theorem B974675 : Blo 972592 974675 := bstep (se 1 (by rfl) ⟨731006, by rfl⟩ : syracuseStep 974675 = 1462013) B1462013
theorem B974691 : Blo 972592 974691 := bstep (se 1 (by rfl) ⟨731018, by rfl⟩ : syracuseStep 974691 = 1462037) B1462037
theorem B974707 : Blo 972592 974707 := bstep (se 1 (by rfl) ⟨731030, by rfl⟩ : syracuseStep 974707 = 1462061) B1462061
theorem B974723 : Blo 972592 974723 := bstep (se 1 (by rfl) ⟨731042, by rfl⟩ : syracuseStep 974723 = 1462085) B1462085
theorem B974739 : Blo 972592 974739 := bstep (se 1 (by rfl) ⟨731054, by rfl⟩ : syracuseStep 974739 = 1462109) B1462109
theorem B974755 : Blo 972592 974755 := bstep (se 1 (by rfl) ⟨731066, by rfl⟩ : syracuseStep 974755 = 1462133) B1462133
theorem B974771 : Blo 972592 974771 := bstep (se 1 (by rfl) ⟨731078, by rfl⟩ : syracuseStep 974771 = 1462157) B1462157
theorem B974787 : Blo 972592 974787 := bstep (se 1 (by rfl) ⟨731090, by rfl⟩ : syracuseStep 974787 = 1462181) B1462181
theorem B974803 : Blo 972592 974803 := bstep (se 1 (by rfl) ⟨731102, by rfl⟩ : syracuseStep 974803 = 1462205) B1462205
theorem B974819 : Blo 972592 974819 := bstep (se 1 (by rfl) ⟨731114, by rfl⟩ : syracuseStep 974819 = 1462229) B1462229
theorem B1171427 : Blo 972592 1171427 := bstep (se 1 (by rfl) ⟨878570, by rfl⟩ : syracuseStep 1171427 = 1757141) B1757141
theorem B974835 : Blo 972592 974835 := bstep (se 1 (by rfl) ⟨731126, by rfl⟩ : syracuseStep 974835 = 1462253) B1462253
theorem B974851 : Blo 972592 974851 := bstep (se 1 (by rfl) ⟨731138, by rfl⟩ : syracuseStep 974851 = 1462277) B1462277
theorem B974867 : Blo 972592 974867 := bstep (se 1 (by rfl) ⟨731150, by rfl⟩ : syracuseStep 974867 = 1462301) B1462301
theorem B974883 : Blo 972592 974883 := bstep (se 1 (by rfl) ⟨731162, by rfl⟩ : syracuseStep 974883 = 1462325) B1462325
theorem B974899 : Blo 972592 974899 := bstep (se 1 (by rfl) ⟨731174, by rfl⟩ : syracuseStep 974899 = 1462349) B1462349
theorem B974915 : Blo 972592 974915 := bstep (se 1 (by rfl) ⟨731186, by rfl⟩ : syracuseStep 974915 = 1462373) B1462373
theorem B974931 : Blo 972592 974931 := bstep (se 1 (by rfl) ⟨731198, by rfl⟩ : syracuseStep 974931 = 1462397) B1462397
theorem B974947 : Blo 972592 974947 := bstep (se 1 (by rfl) ⟨731210, by rfl⟩ : syracuseStep 974947 = 1462421) B1462421
theorem B974963 : Blo 972592 974963 := bstep (se 1 (by rfl) ⟨731222, by rfl⟩ : syracuseStep 974963 = 1462445) B1462445
theorem B974979 : Blo 972592 974979 := bstep (se 1 (by rfl) ⟨731234, by rfl⟩ : syracuseStep 974979 = 1462469) B1462469
theorem B974995 : Blo 972592 974995 := bstep (se 1 (by rfl) ⟨731246, by rfl⟩ : syracuseStep 974995 = 1462493) B1462493
theorem B975011 : Blo 972592 975011 := bstep (se 1 (by rfl) ⟨731258, by rfl⟩ : syracuseStep 975011 = 1462517) B1462517
theorem B975027 : Blo 972592 975027 := bstep (se 1 (by rfl) ⟨731270, by rfl⟩ : syracuseStep 975027 = 1462541) B1462541
theorem B975043 : Blo 972592 975043 := bstep (se 1 (by rfl) ⟨731282, by rfl⟩ : syracuseStep 975043 = 1462565) B1462565
theorem B975059 : Blo 972592 975059 := bstep (se 1 (by rfl) ⟨731294, by rfl⟩ : syracuseStep 975059 = 1462589) B1462589
theorem B975075 : Blo 972592 975075 := bstep (se 1 (by rfl) ⟨731306, by rfl⟩ : syracuseStep 975075 = 1462613) B1462613
theorem B975091 : Blo 972592 975091 := bstep (se 1 (by rfl) ⟨731318, by rfl⟩ : syracuseStep 975091 = 1462637) B1462637
theorem B975107 : Blo 972592 975107 := bstep (se 1 (by rfl) ⟨731330, by rfl⟩ : syracuseStep 975107 = 1462661) B1462661
theorem B975123 : Blo 972592 975123 := bstep (se 1 (by rfl) ⟨731342, by rfl⟩ : syracuseStep 975123 = 1462685) B1462685
theorem B975139 : Blo 972592 975139 := bstep (se 1 (by rfl) ⟨731354, by rfl⟩ : syracuseStep 975139 = 1462709) B1462709
theorem B975155 : Blo 972592 975155 := bstep (se 1 (by rfl) ⟨731366, by rfl⟩ : syracuseStep 975155 = 1462733) B1462733
theorem B975171 : Blo 972592 975171 := bstep (se 1 (by rfl) ⟨731378, by rfl⟩ : syracuseStep 975171 = 1462757) B1462757
theorem B975187 : Blo 972592 975187 := bstep (se 1 (by rfl) ⟨731390, by rfl⟩ : syracuseStep 975187 = 1462781) B1462781
theorem B975203 : Blo 972592 975203 := bstep (se 1 (by rfl) ⟨731402, by rfl⟩ : syracuseStep 975203 = 1462805) B1462805
theorem B975219 : Blo 972592 975219 := bstep (se 1 (by rfl) ⟨731414, by rfl⟩ : syracuseStep 975219 = 1462829) B1462829
theorem B975235 : Blo 972592 975235 := bstep (se 1 (by rfl) ⟨731426, by rfl⟩ : syracuseStep 975235 = 1462853) B1462853
theorem B975251 : Blo 972592 975251 := bstep (se 1 (by rfl) ⟨731438, by rfl⟩ : syracuseStep 975251 = 1462877) B1462877
theorem B975267 : Blo 972592 975267 := bstep (se 1 (by rfl) ⟨731450, by rfl⟩ : syracuseStep 975267 = 1462901) B1462901
theorem B975283 : Blo 972592 975283 := bstep (se 1 (by rfl) ⟨731462, by rfl⟩ : syracuseStep 975283 = 1462925) B1462925
theorem B975299 : Blo 972592 975299 := bstep (se 1 (by rfl) ⟨731474, by rfl⟩ : syracuseStep 975299 = 1462949) B1462949
theorem B975315 : Blo 972592 975315 := bstep (se 1 (by rfl) ⟨731486, by rfl⟩ : syracuseStep 975315 = 1462973) B1462973
theorem B975331 : Blo 972592 975331 := bstep (se 1 (by rfl) ⟨731498, by rfl⟩ : syracuseStep 975331 = 1462997) B1462997
theorem B2777581 : Blo 972592 2777581 := bstep (se 3 (by rfl) ⟨520796, by rfl⟩ : syracuseStep 2777581 = 1041593) B1041593
theorem B975347 : Blo 972592 975347 := bstep (se 1 (by rfl) ⟨731510, by rfl⟩ : syracuseStep 975347 = 1463021) B1463021
theorem B975363 : Blo 972592 975363 := bstep (se 1 (by rfl) ⟨731522, by rfl⟩ : syracuseStep 975363 = 1463045) B1463045
theorem B975379 : Blo 972592 975379 := bstep (se 1 (by rfl) ⟨731534, by rfl⟩ : syracuseStep 975379 = 1463069) B1463069
theorem B975395 : Blo 972592 975395 := bstep (se 1 (by rfl) ⟨731546, by rfl⟩ : syracuseStep 975395 = 1463093) B1463093
theorem B975411 : Blo 972592 975411 := bstep (se 1 (by rfl) ⟨731558, by rfl⟩ : syracuseStep 975411 = 1463117) B1463117
theorem B975427 : Blo 972592 975427 := bstep (se 1 (by rfl) ⟨731570, by rfl⟩ : syracuseStep 975427 = 1463141) B1463141
theorem B975443 : Blo 972592 975443 := bstep (se 1 (by rfl) ⟨731582, by rfl⟩ : syracuseStep 975443 = 1463165) B1463165
theorem B1040995 : Blo 972592 1040995 := bstep (se 1 (by rfl) ⟨780746, by rfl⟩ : syracuseStep 1040995 = 1561493) B1561493
theorem B975459 : Blo 972592 975459 := bstep (se 1 (by rfl) ⟨731594, by rfl⟩ : syracuseStep 975459 = 1463189) B1463189
theorem B975475 : Blo 972592 975475 := bstep (se 1 (by rfl) ⟨731606, by rfl⟩ : syracuseStep 975475 = 1463213) B1463213
theorem B975491 : Blo 972592 975491 := bstep (se 1 (by rfl) ⟨731618, by rfl⟩ : syracuseStep 975491 = 1463237) B1463237
theorem B975507 : Blo 972592 975507 := bstep (se 1 (by rfl) ⟨731630, by rfl⟩ : syracuseStep 975507 = 1463261) B1463261
theorem B975523 : Blo 972592 975523 := bstep (se 1 (by rfl) ⟨731642, by rfl⟩ : syracuseStep 975523 = 1463285) B1463285
theorem B975539 : Blo 972592 975539 := bstep (se 1 (by rfl) ⟨731654, by rfl⟩ : syracuseStep 975539 = 1463309) B1463309
theorem B975555 : Blo 972592 975555 := bstep (se 1 (by rfl) ⟨731666, by rfl⟩ : syracuseStep 975555 = 1463333) B1463333
theorem B15819461 : Blo 972592 15819461 := bstep (se 4 (by rfl) ⟨1483074, by rfl⟩ : syracuseStep 15819461 = 2966149) B2966149
theorem B2777809 : Blo 972592 2777809 := bstep (se 2 (by rfl) ⟨1041678, by rfl⟩ : syracuseStep 2777809 = 2083357) B2083357
theorem B975571 : Blo 972592 975571 := bstep (se 1 (by rfl) ⟨731678, by rfl⟩ : syracuseStep 975571 = 1463357) B1463357
theorem B975587 : Blo 972592 975587 := bstep (se 1 (by rfl) ⟨731690, by rfl⟩ : syracuseStep 975587 = 1463381) B1463381
theorem B975603 : Blo 972592 975603 := bstep (se 1 (by rfl) ⟨731702, by rfl⟩ : syracuseStep 975603 = 1463405) B1463405
theorem B975619 : Blo 972592 975619 := bstep (se 1 (by rfl) ⟨731714, by rfl⟩ : syracuseStep 975619 = 1463429) B1463429
theorem B975635 : Blo 972592 975635 := bstep (se 1 (by rfl) ⟨731726, by rfl⟩ : syracuseStep 975635 = 1463453) B1463453
theorem B975651 : Blo 972592 975651 := bstep (se 1 (by rfl) ⟨731738, by rfl⟩ : syracuseStep 975651 = 1463477) B1463477
theorem B975667 : Blo 972592 975667 := bstep (se 1 (by rfl) ⟨731750, by rfl⟩ : syracuseStep 975667 = 1463501) B1463501
theorem B975683 : Blo 972592 975683 := bstep (se 1 (by rfl) ⟨731762, by rfl⟩ : syracuseStep 975683 = 1463525) B1463525
theorem B975699 : Blo 972592 975699 := bstep (se 1 (by rfl) ⟨731774, by rfl⟩ : syracuseStep 975699 = 1463549) B1463549
theorem B975715 : Blo 972592 975715 := bstep (se 1 (by rfl) ⟨731786, by rfl⟩ : syracuseStep 975715 = 1463573) B1463573
theorem B2777969 : Blo 972592 2777969 := bstep (se 2 (by rfl) ⟨1041738, by rfl⟩ : syracuseStep 2777969 = 2083477) B2083477
theorem B975731 : Blo 972592 975731 := bstep (se 1 (by rfl) ⟨731798, by rfl⟩ : syracuseStep 975731 = 1463597) B1463597
theorem B975747 : Blo 972592 975747 := bstep (se 1 (by rfl) ⟨731810, by rfl⟩ : syracuseStep 975747 = 1463621) B1463621
theorem B975763 : Blo 972592 975763 := bstep (se 1 (by rfl) ⟨731822, by rfl⟩ : syracuseStep 975763 = 1463645) B1463645
theorem B975779 : Blo 972592 975779 := bstep (se 1 (by rfl) ⟨731834, by rfl⟩ : syracuseStep 975779 = 1463669) B1463669
theorem B975795 : Blo 972592 975795 := bstep (se 1 (by rfl) ⟨731846, by rfl⟩ : syracuseStep 975795 = 1463693) B1463693
theorem B975811 : Blo 972592 975811 := bstep (se 1 (by rfl) ⟨731858, by rfl⟩ : syracuseStep 975811 = 1463717) B1463717
theorem B975827 : Blo 972592 975827 := bstep (se 1 (by rfl) ⟨731870, by rfl⟩ : syracuseStep 975827 = 1463741) B1463741
theorem B2778083 : Blo 972592 2778083 := bstep (se 1 (by rfl) ⟨2083562, by rfl⟩ : syracuseStep 2778083 = 4167125) B4167125
theorem B975843 : Blo 972592 975843 := bstep (se 1 (by rfl) ⟨731882, by rfl⟩ : syracuseStep 975843 = 1463765) B1463765
theorem B975859 : Blo 972592 975859 := bstep (se 1 (by rfl) ⟨731894, by rfl⟩ : syracuseStep 975859 = 1463789) B1463789
theorem B975875 : Blo 972592 975875 := bstep (se 1 (by rfl) ⟨731906, by rfl⟩ : syracuseStep 975875 = 1463813) B1463813
theorem B975891 : Blo 972592 975891 := bstep (se 1 (by rfl) ⟨731918, by rfl⟩ : syracuseStep 975891 = 1463837) B1463837
theorem B3695651 : Blo 972592 3695651 := bstep (se 1 (by rfl) ⟨2771738, by rfl⟩ : syracuseStep 3695651 = 5543477) B5543477
theorem B975907 : Blo 972592 975907 := bstep (se 1 (by rfl) ⟨731930, by rfl⟩ : syracuseStep 975907 = 1463861) B1463861
theorem B3695665 : Blo 972592 3695665 := bstep (se 2 (by rfl) ⟨1385874, by rfl⟩ : syracuseStep 3695665 = 2771749) B2771749
theorem B975923 : Blo 972592 975923 := bstep (se 1 (by rfl) ⟨731942, by rfl⟩ : syracuseStep 975923 = 1463885) B1463885
theorem B975939 : Blo 972592 975939 := bstep (se 1 (by rfl) ⟨731954, by rfl⟩ : syracuseStep 975939 = 1463909) B1463909
theorem B975955 : Blo 972592 975955 := bstep (se 1 (by rfl) ⟨731966, by rfl⟩ : syracuseStep 975955 = 1463933) B1463933
theorem B975971 : Blo 972592 975971 := bstep (se 1 (by rfl) ⟨731978, by rfl⟩ : syracuseStep 975971 = 1463957) B1463957
theorem B975987 : Blo 972592 975987 := bstep (se 1 (by rfl) ⟨731990, by rfl⟩ : syracuseStep 975987 = 1463981) B1463981
theorem B976003 : Blo 972592 976003 := bstep (se 1 (by rfl) ⟨732002, by rfl⟩ : syracuseStep 976003 = 1464005) B1464005
theorem B976019 : Blo 972592 976019 := bstep (se 1 (by rfl) ⟨732014, by rfl⟩ : syracuseStep 976019 = 1464029) B1464029
theorem B976035 : Blo 972592 976035 := bstep (se 1 (by rfl) ⟨732026, by rfl⟩ : syracuseStep 976035 = 1464053) B1464053
theorem B976051 : Blo 972592 976051 := bstep (se 1 (by rfl) ⟨732038, by rfl⟩ : syracuseStep 976051 = 1464077) B1464077
theorem B976067 : Blo 972592 976067 := bstep (se 1 (by rfl) ⟨732050, by rfl⟩ : syracuseStep 976067 = 1464101) B1464101
theorem B976083 : Blo 972592 976083 := bstep (se 1 (by rfl) ⟨732062, by rfl⟩ : syracuseStep 976083 = 1464125) B1464125
theorem B976099 : Blo 972592 976099 := bstep (se 1 (by rfl) ⟨732074, by rfl⟩ : syracuseStep 976099 = 1464149) B1464149
theorem B2188529 : Blo 972592 2188529 := bstep (se 2 (by rfl) ⟨820698, by rfl⟩ : syracuseStep 2188529 = 1641397) B1641397
theorem B976115 : Blo 972592 976115 := bstep (se 1 (by rfl) ⟨732086, by rfl⟩ : syracuseStep 976115 = 1464173) B1464173
theorem B2188547 : Blo 972592 2188547 := bstep (se 1 (by rfl) ⟨1641410, by rfl⟩ : syracuseStep 2188547 = 3282821) B3282821
theorem B976131 : Blo 972592 976131 := bstep (se 1 (by rfl) ⟨732098, by rfl⟩ : syracuseStep 976131 = 1464197) B1464197
theorem B976147 : Blo 972592 976147 := bstep (se 1 (by rfl) ⟨732110, by rfl⟩ : syracuseStep 976147 = 1464221) B1464221
theorem B976163 : Blo 972592 976163 := bstep (se 1 (by rfl) ⟨732122, by rfl⟩ : syracuseStep 976163 = 1464245) B1464245
theorem B976179 : Blo 972592 976179 := bstep (se 1 (by rfl) ⟨732134, by rfl⟩ : syracuseStep 976179 = 1464269) B1464269
theorem B976195 : Blo 972592 976195 := bstep (se 1 (by rfl) ⟨732146, by rfl⟩ : syracuseStep 976195 = 1464293) B1464293
theorem B976211 : Blo 972592 976211 := bstep (se 1 (by rfl) ⟨732158, by rfl⟩ : syracuseStep 976211 = 1464317) B1464317
theorem B976227 : Blo 972592 976227 := bstep (se 1 (by rfl) ⟨732170, by rfl⟩ : syracuseStep 976227 = 1464341) B1464341
theorem B976243 : Blo 972592 976243 := bstep (se 1 (by rfl) ⟨732182, by rfl⟩ : syracuseStep 976243 = 1464365) B1464365
theorem B976259 : Blo 972592 976259 := bstep (se 1 (by rfl) ⟨732194, by rfl⟩ : syracuseStep 976259 = 1464389) B1464389
theorem B976275 : Blo 972592 976275 := bstep (se 1 (by rfl) ⟨732206, by rfl⟩ : syracuseStep 976275 = 1464413) B1464413
theorem B976291 : Blo 972592 976291 := bstep (se 1 (by rfl) ⟨732218, by rfl⟩ : syracuseStep 976291 = 1464437) B1464437
theorem B976307 : Blo 972592 976307 := bstep (se 1 (by rfl) ⟨732230, by rfl⟩ : syracuseStep 976307 = 1464461) B1464461
theorem B976323 : Blo 972592 976323 := bstep (se 1 (by rfl) ⟨732242, by rfl⟩ : syracuseStep 976323 = 1464485) B1464485
theorem B976339 : Blo 972592 976339 := bstep (se 1 (by rfl) ⟨732254, by rfl⟩ : syracuseStep 976339 = 1464509) B1464509
theorem B976355 : Blo 972592 976355 := bstep (se 1 (by rfl) ⟨732266, by rfl⟩ : syracuseStep 976355 = 1464533) B1464533
theorem B976371 : Blo 972592 976371 := bstep (se 1 (by rfl) ⟨732278, by rfl⟩ : syracuseStep 976371 = 1464557) B1464557
theorem B976387 : Blo 972592 976387 := bstep (se 1 (by rfl) ⟨732290, by rfl⟩ : syracuseStep 976387 = 1464581) B1464581
theorem B2188817 : Blo 972592 2188817 := bstep (se 2 (by rfl) ⟨820806, by rfl⟩ : syracuseStep 2188817 = 1641613) B1641613
theorem B976403 : Blo 972592 976403 := bstep (se 1 (by rfl) ⟨732302, by rfl⟩ : syracuseStep 976403 = 1464605) B1464605
theorem B2188835 : Blo 972592 2188835 := bstep (se 1 (by rfl) ⟨1641626, by rfl⟩ : syracuseStep 2188835 = 3283253) B3283253
theorem B1336867 : Blo 972592 1336867 := bstep (se 1 (by rfl) ⟨1002650, by rfl⟩ : syracuseStep 1336867 = 2005301) B2005301
theorem B976419 : Blo 972592 976419 := bstep (se 1 (by rfl) ⟨732314, by rfl⟩ : syracuseStep 976419 = 1464629) B1464629
theorem B976435 : Blo 972592 976435 := bstep (se 1 (by rfl) ⟨732326, by rfl⟩ : syracuseStep 976435 = 1464653) B1464653
theorem B976451 : Blo 972592 976451 := bstep (se 1 (by rfl) ⟨732338, by rfl⟩ : syracuseStep 976451 = 1464677) B1464677
theorem B1042003 : Blo 972592 1042003 := bstep (se 1 (by rfl) ⟨781502, by rfl⟩ : syracuseStep 1042003 = 1563005) B1563005
theorem B976467 : Blo 972592 976467 := bstep (se 1 (by rfl) ⟨732350, by rfl⟩ : syracuseStep 976467 = 1464701) B1464701
theorem B976483 : Blo 972592 976483 := bstep (se 1 (by rfl) ⟨732362, by rfl⟩ : syracuseStep 976483 = 1464725) B1464725
theorem B976499 : Blo 972592 976499 := bstep (se 1 (by rfl) ⟨732374, by rfl⟩ : syracuseStep 976499 = 1464749) B1464749
theorem B976515 : Blo 972592 976515 := bstep (se 1 (by rfl) ⟨732386, by rfl⟩ : syracuseStep 976515 = 1464773) B1464773
theorem B976531 : Blo 972592 976531 := bstep (se 1 (by rfl) ⟨732398, by rfl⟩ : syracuseStep 976531 = 1464797) B1464797
theorem B5924515 : Blo 972592 5924515 := bstep (se 1 (by rfl) ⟨4443386, by rfl⟩ : syracuseStep 5924515 = 8886773) B8886773
theorem B976547 : Blo 972592 976547 := bstep (se 1 (by rfl) ⟨732410, by rfl⟩ : syracuseStep 976547 = 1464821) B1464821
theorem B976563 : Blo 972592 976563 := bstep (se 1 (by rfl) ⟨732422, by rfl⟩ : syracuseStep 976563 = 1464845) B1464845
theorem B976579 : Blo 972592 976579 := bstep (se 1 (by rfl) ⟨732434, by rfl⟩ : syracuseStep 976579 = 1464869) B1464869
theorem B2189105 : Blo 972592 2189105 := bstep (se 2 (by rfl) ⟨820914, by rfl⟩ : syracuseStep 2189105 = 1641829) B1641829
theorem B2189123 : Blo 972592 2189123 := bstep (se 1 (by rfl) ⟨1641842, by rfl⟩ : syracuseStep 2189123 = 3283685) B3283685
theorem B2779085 : Blo 972592 2779085 := bstep (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) B1042157
theorem B4941809 : Blo 972592 4941809 := bstep (se 2 (by rfl) ⟨1853178, by rfl⟩ : syracuseStep 4941809 = 3706357) B3706357
theorem B2189393 : Blo 972592 2189393 := bstep (se 2 (by rfl) ⟨821022, by rfl⟩ : syracuseStep 2189393 = 1642045) B1642045
theorem B2189411 : Blo 972592 2189411 := bstep (se 1 (by rfl) ⟨1642058, by rfl⟩ : syracuseStep 2189411 = 3284117) B3284117
theorem B2779267 : Blo 972592 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B1042627 : Blo 972592 1042627 := bstep (se 1 (by rfl) ⟨781970, by rfl⟩ : syracuseStep 1042627 = 1563941) B1563941
theorem B2779427 : Blo 972592 2779427 := bstep (se 1 (by rfl) ⟨2084570, by rfl⟩ : syracuseStep 2779427 = 4169141) B4169141
theorem B2189681 : Blo 972592 2189681 := bstep (se 2 (by rfl) ⟨821130, by rfl⟩ : syracuseStep 2189681 = 1642261) B1642261
theorem B2189699 : Blo 972592 2189699 := bstep (se 1 (by rfl) ⟨1642274, by rfl⟩ : syracuseStep 2189699 = 3284549) B3284549
theorem B3697123 : Blo 972592 3697123 := bstep (se 1 (by rfl) ⟨2772842, by rfl⟩ : syracuseStep 3697123 = 5545685) B5545685
theorem B2812429 : Blo 972592 2812429 := bstep (se 3 (by rfl) ⟨527330, by rfl⟩ : syracuseStep 2812429 = 1054661) B1054661
theorem B2189969 : Blo 972592 2189969 := bstep (se 2 (by rfl) ⟨821238, by rfl⟩ : syracuseStep 2189969 = 1642477) B1642477
theorem B2189987 : Blo 972592 2189987 := bstep (se 1 (by rfl) ⟨1642490, by rfl⟩ : syracuseStep 2189987 = 3284981) B3284981
theorem B3009233 : Blo 972592 3009233 := bstep (se 2 (by rfl) ⟨1128462, by rfl⟩ : syracuseStep 3009233 = 2256925) B2256925
theorem B59894549 : Blo 972592 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B6253453 : Blo 972592 6253453 := bstep (se 3 (by rfl) ⟨1172522, by rfl⟩ : syracuseStep 6253453 = 2345045) B2345045
theorem B2190257 : Blo 972592 2190257 := bstep (se 2 (by rfl) ⟨821346, by rfl⟩ : syracuseStep 2190257 = 1642693) B1642693
theorem B2190275 : Blo 972592 2190275 := bstep (se 1 (by rfl) ⟨1642706, by rfl⟩ : syracuseStep 2190275 = 3285413) B3285413
theorem B8318051 : Blo 972592 8318051 := bstep (se 1 (by rfl) ⟨6238538, by rfl⟩ : syracuseStep 8318051 = 12477077) B12477077
theorem B2190545 : Blo 972592 2190545 := bstep (se 2 (by rfl) ⟨821454, by rfl⟩ : syracuseStep 2190545 = 1642909) B1642909
theorem B2190563 : Blo 972592 2190563 := bstep (se 1 (by rfl) ⟨1642922, by rfl⟩ : syracuseStep 2190563 = 3285845) B3285845
theorem B2256113 : Blo 972592 2256113 := bstep (se 2 (by rfl) ⟨846042, by rfl⟩ : syracuseStep 2256113 = 1692085) B1692085
theorem B2780497 : Blo 972592 2780497 := bstep (se 2 (by rfl) ⟨1042686, by rfl⟩ : syracuseStep 2780497 = 2085373) B2085373
theorem B4943267 : Blo 972592 4943267 := bstep (se 1 (by rfl) ⟨3707450, by rfl⟩ : syracuseStep 4943267 = 7414901) B7414901
theorem B5270989 : Blo 972592 5270989 := bstep (se 3 (by rfl) ⟨988310, by rfl⟩ : syracuseStep 5270989 = 1976621) B1976621
theorem B2190833 : Blo 972592 2190833 := bstep (se 2 (by rfl) ⟨821562, by rfl⟩ : syracuseStep 2190833 = 1643125) B1643125
theorem B2190851 : Blo 972592 2190851 := bstep (se 1 (by rfl) ⟨1643138, by rfl⟩ : syracuseStep 2190851 = 3286277) B3286277
theorem B6745805 : Blo 972592 6745805 := bstep (se 3 (by rfl) ⟨1264838, by rfl⟩ : syracuseStep 6745805 = 2529677) B2529677
theorem B2191121 : Blo 972592 2191121 := bstep (se 2 (by rfl) ⟨821670, by rfl⟩ : syracuseStep 2191121 = 1643341) B1643341
theorem B1404691 : Blo 972592 1404691 := bstep (se 1 (by rfl) ⟨1053518, by rfl⟩ : syracuseStep 1404691 = 2107037) B2107037
theorem B2191139 : Blo 972592 2191139 := bstep (se 1 (by rfl) ⟨1643354, by rfl⟩ : syracuseStep 2191139 = 3286709) B3286709
theorem B2748205 : Blo 972592 2748205 := bstep (se 3 (by rfl) ⟨515288, by rfl⟩ : syracuseStep 2748205 = 1030577) B1030577
theorem B1109971 : Blo 972592 1109971 := bstep (se 1 (by rfl) ⟨832478, by rfl⟩ : syracuseStep 1109971 = 1664957) B1664957
theorem B2191409 : Blo 972592 2191409 := bstep (se 2 (by rfl) ⟨821778, by rfl⟩ : syracuseStep 2191409 = 1643557) B1643557
theorem B2191427 : Blo 972592 2191427 := bstep (se 1 (by rfl) ⟨1643570, by rfl⟩ : syracuseStep 2191427 = 3287141) B3287141
theorem B28471409 : Blo 972592 28471409 := bstep (se 2 (by rfl) ⟨10676778, by rfl⟩ : syracuseStep 28471409 = 21353557) B21353557
theorem B4812941 : Blo 972592 4812941 := bstep (se 3 (by rfl) ⟨902426, by rfl⟩ : syracuseStep 4812941 = 1804853) B1804853
theorem B1405153 : Blo 972592 1405153 := bstep (se 2 (by rfl) ⟨526932, by rfl⟩ : syracuseStep 1405153 = 1053865) B1053865
theorem B2191697 : Blo 972592 2191697 := bstep (se 2 (by rfl) ⟨821886, by rfl⟩ : syracuseStep 2191697 = 1643773) B1643773
theorem B2191715 : Blo 972592 2191715 := bstep (se 1 (by rfl) ⟨1643786, by rfl⟩ : syracuseStep 2191715 = 3287573) B3287573
theorem B2191985 : Blo 972592 2191985 := bstep (se 2 (by rfl) ⟨821994, by rfl⟩ : syracuseStep 2191985 = 1643989) B1643989
theorem B2192003 : Blo 972592 2192003 := bstep (se 1 (by rfl) ⟨1644002, by rfl⟩ : syracuseStep 2192003 = 3288005) B3288005
theorem B3699341 : Blo 972592 3699341 := bstep (se 3 (by rfl) ⟨693626, by rfl⟩ : syracuseStep 3699341 = 1387253) B1387253
theorem B4158307 : Blo 972592 4158307 := bstep (se 1 (by rfl) ⟨3118730, by rfl⟩ : syracuseStep 4158307 = 6237461) B6237461
theorem B2192273 : Blo 972592 2192273 := bstep (se 2 (by rfl) ⟨822102, by rfl⟩ : syracuseStep 2192273 = 1644205) B1644205
theorem B2192291 : Blo 972592 2192291 := bstep (se 1 (by rfl) ⟨1644218, by rfl⟩ : syracuseStep 2192291 = 3288437) B3288437
theorem B2192561 : Blo 972592 2192561 := bstep (se 2 (by rfl) ⟨822210, by rfl⟩ : syracuseStep 2192561 = 1644421) B1644421
theorem B2192579 : Blo 972592 2192579 := bstep (se 1 (by rfl) ⟨1644434, by rfl⟩ : syracuseStep 2192579 = 3288869) B3288869
theorem B1668323 : Blo 972592 1668323 := bstep (se 1 (by rfl) ⟨1251242, by rfl⟩ : syracuseStep 1668323 = 2502485) B2502485
theorem B2192849 : Blo 972592 2192849 := bstep (se 2 (by rfl) ⟨822318, by rfl⟩ : syracuseStep 2192849 = 1644637) B1644637
theorem B2192867 : Blo 972592 2192867 := bstep (se 1 (by rfl) ⟨1644650, by rfl⟩ : syracuseStep 2192867 = 3289301) B3289301
theorem B2193137 : Blo 972592 2193137 := bstep (se 2 (by rfl) ⟨822426, by rfl⟩ : syracuseStep 2193137 = 1644853) B1644853
theorem B2193155 : Blo 972592 2193155 := bstep (se 1 (by rfl) ⟨1644866, by rfl⟩ : syracuseStep 2193155 = 3289733) B3289733
theorem B14055281 : Blo 972592 14055281 := bstep (se 2 (by rfl) ⟨5270730, by rfl⟩ : syracuseStep 14055281 = 10541461) B10541461
theorem B2193425 : Blo 972592 2193425 := bstep (se 2 (by rfl) ⟨822534, by rfl⟩ : syracuseStep 2193425 = 1645069) B1645069
theorem B2193443 : Blo 972592 2193443 := bstep (se 1 (by rfl) ⟨1645082, by rfl⟩ : syracuseStep 2193443 = 3290165) B3290165
theorem B2193713 : Blo 972592 2193713 := bstep (se 2 (by rfl) ⟨822642, by rfl⟩ : syracuseStep 2193713 = 1645285) B1645285
theorem B2193731 : Blo 972592 2193731 := bstep (se 1 (by rfl) ⟨1645298, by rfl⟩ : syracuseStep 2193731 = 3290597) B3290597
theorem B4225421 : Blo 972592 4225421 := bstep (se 3 (by rfl) ⟨792266, by rfl⟩ : syracuseStep 4225421 = 1584533) B1584533
theorem B2194001 : Blo 972592 2194001 := bstep (se 2 (by rfl) ⟨822750, by rfl⟩ : syracuseStep 2194001 = 1645501) B1645501
theorem B2194019 : Blo 972592 2194019 := bstep (se 1 (by rfl) ⟨1645514, by rfl⟩ : syracuseStep 2194019 = 3291029) B3291029
theorem B11107043 : Blo 972592 11107043 := bstep (se 1 (by rfl) ⟨8330282, by rfl⟩ : syracuseStep 11107043 = 16660565) B16660565
theorem B8321777 : Blo 972592 8321777 := bstep (se 2 (by rfl) ⟨3120666, by rfl⟩ : syracuseStep 8321777 = 6241333) B6241333
theorem B2226947 : Blo 972592 2226947 := bstep (se 1 (by rfl) ⟨1670210, by rfl⟩ : syracuseStep 2226947 = 3340421) B3340421
theorem B2194289 : Blo 972592 2194289 := bstep (se 2 (by rfl) ⟨822858, by rfl⟩ : syracuseStep 2194289 = 1645717) B1645717
theorem B2194307 : Blo 972592 2194307 := bstep (se 1 (by rfl) ⟨1645730, by rfl⟩ : syracuseStep 2194307 = 3291461) B3291461
theorem B2849869 : Blo 972592 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B2227313 : Blo 972592 2227313 := bstep (se 2 (by rfl) ⟨835242, by rfl⟩ : syracuseStep 2227313 = 1670485) B1670485
theorem B2194577 : Blo 972592 2194577 := bstep (se 2 (by rfl) ⟨822966, by rfl⟩ : syracuseStep 2194577 = 1645933) B1645933
theorem B2194595 : Blo 972592 2194595 := bstep (se 1 (by rfl) ⟨1645946, by rfl⟩ : syracuseStep 2194595 = 3291893) B3291893
theorem B4160753 : Blo 972592 4160753 := bstep (se 2 (by rfl) ⟨1560282, by rfl⟩ : syracuseStep 4160753 = 3120565) B3120565
theorem B1408339 : Blo 972592 1408339 := bstep (se 1 (by rfl) ⟨1056254, by rfl⟩ : syracuseStep 1408339 = 2112509) B2112509
theorem B2194865 : Blo 972592 2194865 := bstep (se 2 (by rfl) ⟨823074, by rfl⟩ : syracuseStep 2194865 = 1646149) B1646149
theorem B2194883 : Blo 972592 2194883 := bstep (se 1 (by rfl) ⟨1646162, by rfl⟩ : syracuseStep 2194883 = 3292325) B3292325
theorem B3702257 : Blo 972592 3702257 := bstep (se 2 (by rfl) ⟨1388346, by rfl⟩ : syracuseStep 3702257 = 2776693) B2776693
theorem B3505805 : Blo 972592 3505805 := bstep (se 3 (by rfl) ⟨657338, by rfl⟩ : syracuseStep 3505805 = 1314677) B1314677
theorem B2195153 : Blo 972592 2195153 := bstep (se 2 (by rfl) ⟨823182, by rfl⟩ : syracuseStep 2195153 = 1646365) B1646365
theorem B2195171 : Blo 972592 2195171 := bstep (se 1 (by rfl) ⟨1646378, by rfl⟩ : syracuseStep 2195171 = 3292757) B3292757
theorem B2195441 : Blo 972592 2195441 := bstep (se 2 (by rfl) ⟨823290, by rfl⟩ : syracuseStep 2195441 = 1646581) B1646581
theorem B5931083 : Blo 972592 5931083 := bstep (se 1 (by rfl) ⟨4448312, by rfl⟩ : syracuseStep 5931083 = 8896625) B8896625
theorem B2195531 : Blo 972592 2195531 := bstep (se 1 (by rfl) ⟨1646648, by rfl⟩ : syracuseStep 2195531 = 3293297) B3293297
theorem B2195585 : Blo 972592 2195585 := bstep (se 2 (by rfl) ⟨823344, by rfl⟩ : syracuseStep 2195585 = 1646689) B1646689
theorem B2195801 : Blo 972592 2195801 := bstep (se 2 (by rfl) ⟨823425, by rfl⟩ : syracuseStep 2195801 = 1646851) B1646851
theorem B2195891 : Blo 972592 2195891 := bstep (se 1 (by rfl) ⟨1646918, by rfl⟩ : syracuseStep 2195891 = 3293837) B3293837
theorem B4391371 : Blo 972592 4391371 := bstep (se 1 (by rfl) ⟨3293528, by rfl⟩ : syracuseStep 4391371 = 6587057) B6587057
theorem B2195927 : Blo 972592 2195927 := bstep (se 1 (by rfl) ⟨1646945, by rfl⟩ : syracuseStep 2195927 = 3293891) B3293891
theorem B3703427 : Blo 972592 3703427 := bstep (se 1 (by rfl) ⟨2777570, by rfl⟩ : syracuseStep 3703427 = 5555141) B5555141
theorem B2196107 : Blo 972592 2196107 := bstep (se 1 (by rfl) ⟨1647080, by rfl⟩ : syracuseStep 2196107 = 3294161) B3294161
theorem B3703441 : Blo 972592 3703441 := bstep (se 2 (by rfl) ⟨1388790, by rfl⟩ : syracuseStep 3703441 = 2777581) B2777581
theorem B2196161 : Blo 972592 2196161 := bstep (se 2 (by rfl) ⟨823560, by rfl⟩ : syracuseStep 2196161 = 1647121) B1647121
theorem B2851549 : Blo 972592 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B2196377 : Blo 972592 2196377 := bstep (se 2 (by rfl) ⟨823641, by rfl⟩ : syracuseStep 2196377 = 1647283) B1647283
theorem B3703745 : Blo 972592 3703745 := bstep (se 2 (by rfl) ⟨1388904, by rfl⟩ : syracuseStep 3703745 = 2777809) B2777809
theorem B2196467 : Blo 972592 2196467 := bstep (se 1 (by rfl) ⟨1647350, by rfl⟩ : syracuseStep 2196467 = 3294701) B3294701
theorem B2196503 : Blo 972592 2196503 := bstep (se 1 (by rfl) ⟨1647377, by rfl⟩ : syracuseStep 2196503 = 3294755) B3294755
theorem B5637221 : Blo 972592 5637221 := bstep (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) B1056979
theorem B2196683 : Blo 972592 2196683 := bstep (se 1 (by rfl) ⟨1647512, by rfl⟩ : syracuseStep 2196683 = 3295025) B3295025
theorem B2196737 : Blo 972592 2196737 := bstep (se 2 (by rfl) ⟨823776, by rfl⟩ : syracuseStep 2196737 = 1647553) B1647553
theorem B2196953 : Blo 972592 2196953 := bstep (se 2 (by rfl) ⟨823857, by rfl⟩ : syracuseStep 2196953 = 1647715) B1647715
theorem B2197043 : Blo 972592 2197043 := bstep (se 1 (by rfl) ⟨1647782, by rfl⟩ : syracuseStep 2197043 = 3295565) B3295565
theorem B2197079 : Blo 972592 2197079 := bstep (se 1 (by rfl) ⟨1647809, by rfl⟩ : syracuseStep 2197079 = 3295619) B3295619
theorem B3704413 : Blo 972592 3704413 := bstep (se 3 (by rfl) ⟨694577, by rfl⟩ : syracuseStep 3704413 = 1389155) B1389155
theorem B2197259 : Blo 972592 2197259 := bstep (se 1 (by rfl) ⟨1647944, by rfl⟩ : syracuseStep 2197259 = 3295889) B3295889
theorem B2197313 : Blo 972592 2197313 := bstep (se 2 (by rfl) ⟨823992, by rfl⟩ : syracuseStep 2197313 = 1647985) B1647985
theorem B20023139 : Blo 972592 20023139 := bstep (se 1 (by rfl) ⟨15017354, by rfl⟩ : syracuseStep 20023139 = 30034709) B30034709
theorem B4163501 : Blo 972592 4163501 := bstep (se 3 (by rfl) ⟨780656, by rfl⟩ : syracuseStep 4163501 = 1561313) B1561313
theorem B7899353 : Blo 972592 7899353 := bstep (se 2 (by rfl) ⟨2962257, by rfl⟩ : syracuseStep 7899353 = 5924515) B5924515
theorem B10520837 : Blo 972592 10520837 := bstep (se 4 (by rfl) ⟨986328, by rfl⟩ : syracuseStep 10520837 = 1972657) B1972657
theorem B7113005 : Blo 972592 7113005 := bstep (se 3 (by rfl) ⟨1333688, by rfl⟩ : syracuseStep 7113005 = 2667377) B2667377
theorem B4164185 : Blo 972592 4164185 := bstep (se 2 (by rfl) ⟨1561569, by rfl⟩ : syracuseStep 4164185 = 3123139) B3123139
theorem B985943 : Blo 972592 985943 := bstep (se 1 (by rfl) ⟨739457, by rfl⟩ : syracuseStep 985943 = 1478915) B1478915
theorem B3705689 : Blo 972592 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B1641431 : Blo 972592 1641431 := bstep (se 1 (by rfl) ⟨1231073, by rfl⟩ : syracuseStep 1641431 = 2462147) B2462147
theorem B1248215 : Blo 972592 1248215 := bstep (se 1 (by rfl) ⟨936161, by rfl⟩ : syracuseStep 1248215 = 1872323) B1872323
theorem B1641559 : Blo 972592 1641559 := bstep (se 1 (by rfl) ⟨1231169, by rfl⟩ : syracuseStep 1641559 = 2462339) B2462339
theorem B25660567 : Blo 972592 25660567 := bstep (se 1 (by rfl) ⟨19245425, by rfl⟩ : syracuseStep 25660567 = 38490851) B38490851
theorem B1642187 : Blo 972592 1642187 := bstep (se 1 (by rfl) ⟨1231640, by rfl⟩ : syracuseStep 1642187 = 2463281) B2463281
theorem B986827 : Blo 972592 986827 := bstep (se 1 (by rfl) ⟨740120, by rfl⟩ : syracuseStep 986827 = 1480241) B1480241
theorem B9375533 : Blo 972592 9375533 := bstep (se 3 (by rfl) ⟨1757912, by rfl⟩ : syracuseStep 9375533 = 3515825) B3515825
theorem B1642315 : Blo 972592 1642315 := bstep (se 1 (by rfl) ⟨1231736, by rfl⟩ : syracuseStep 1642315 = 2463473) B2463473
theorem B4165451 : Blo 972592 4165451 := bstep (se 1 (by rfl) ⟨3124088, by rfl⟩ : syracuseStep 4165451 = 6248177) B6248177
theorem B1642457 : Blo 972592 1642457 := bstep (se 2 (by rfl) ⟨615921, by rfl⟩ : syracuseStep 1642457 = 1231843) B1231843
theorem B14028875 : Blo 972592 14028875 := bstep (se 1 (by rfl) ⟨10521656, by rfl⟩ : syracuseStep 14028875 = 21043313) B21043313
theorem B1642585 : Blo 972592 1642585 := bstep (se 2 (by rfl) ⟨615969, by rfl⟩ : syracuseStep 1642585 = 1231939) B1231939
theorem B5542019 : Blo 972592 5542019 := bstep (se 1 (by rfl) ⟨4156514, by rfl⟩ : syracuseStep 5542019 = 8313029) B8313029
theorem B9375875 : Blo 972592 9375875 := bstep (se 1 (by rfl) ⟨7031906, by rfl⟩ : syracuseStep 9375875 = 14063813) B14063813
theorem B4165825 : Blo 972592 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B3707315 : Blo 972592 3707315 := bstep (se 1 (by rfl) ⟨2780486, by rfl⟩ : syracuseStep 3707315 = 5560973) B5560973
theorem B3707329 : Blo 972592 3707329 := bstep (se 2 (by rfl) ⟨1390248, by rfl⟩ : syracuseStep 3707329 = 2780497) B2780497
theorem B4166167 : Blo 972592 4166167 := bstep (se 1 (by rfl) ⟨3124625, by rfl⟩ : syracuseStep 4166167 = 6249251) B6249251
theorem B2462359 : Blo 972592 2462359 := bstep (se 1 (by rfl) ⟨1846769, by rfl⟩ : syracuseStep 2462359 = 3693539) B3693539
theorem B1643159 : Blo 972592 1643159 := bstep (se 1 (by rfl) ⟨1232369, by rfl⟩ : syracuseStep 1643159 = 2464739) B2464739
theorem B17994421 : Blo 972592 17994421 := bstep (se 5 (by rfl) ⟨843488, by rfl⟩ : syracuseStep 17994421 = 1686977) B1686977
theorem B4690705 : Blo 972592 4690705 := bstep (se 2 (by rfl) ⟨1759014, by rfl⟩ : syracuseStep 4690705 = 3518029) B3518029
theorem B1315607 : Blo 972592 1315607 := bstep (se 1 (by rfl) ⟨986705, by rfl⟩ : syracuseStep 1315607 = 1973411) B1973411
theorem B1643287 : Blo 972592 1643287 := bstep (se 1 (by rfl) ⟨1232465, by rfl⟩ : syracuseStep 1643287 = 2464931) B2464931
theorem B1315801 : Blo 972592 1315801 := bstep (se 2 (by rfl) ⟨493425, by rfl⟩ : syracuseStep 1315801 = 986851) B986851
theorem B2462795 : Blo 972592 2462795 := bstep (se 1 (by rfl) ⟨1847096, by rfl⟩ : syracuseStep 2462795 = 3694193) B3694193
theorem B1479961 : Blo 972592 1479961 := bstep (se 2 (by rfl) ⟨554985, by rfl⟩ : syracuseStep 1479961 = 1109971) B1109971
theorem B1643915 : Blo 972592 1643915 := bstep (se 1 (by rfl) ⟨1232936, by rfl⟩ : syracuseStep 1643915 = 2465873) B2465873
theorem B2463169 : Blo 972592 2463169 := bstep (se 2 (by rfl) ⟨923688, by rfl⟩ : syracuseStep 2463169 = 1847377) B1847377
theorem B3511745 : Blo 972592 3511745 := bstep (se 2 (by rfl) ⟨1316904, by rfl⟩ : syracuseStep 3511745 = 2633809) B2633809
theorem B1316299 : Blo 972592 1316299 := bstep (se 1 (by rfl) ⟨987224, by rfl⟩ : syracuseStep 1316299 = 1974449) B1974449
theorem B1644043 : Blo 972592 1644043 := bstep (se 1 (by rfl) ⟨1233032, by rfl⟩ : syracuseStep 1644043 = 2466065) B2466065
theorem B1644185 : Blo 972592 1644185 := bstep (se 2 (by rfl) ⟨616569, by rfl⟩ : syracuseStep 1644185 = 1233139) B1233139
theorem B14030597 : Blo 972592 14030597 := bstep (se 4 (by rfl) ⟨1315368, by rfl⟩ : syracuseStep 14030597 = 2630737) B2630737
theorem B1644313 : Blo 972592 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B2463767 : Blo 972592 2463767 := bstep (se 1 (by rfl) ⟨1847825, by rfl⟩ : syracuseStep 2463767 = 3695651) B3695651
theorem B3283037 : Blo 972592 3283037 := bstep (se 3 (by rfl) ⟨615569, by rfl⟩ : syracuseStep 3283037 = 1231139) B1231139
theorem B7411985 : Blo 972592 7411985 := bstep (se 2 (by rfl) ⟨2779494, by rfl⟩ : syracuseStep 7411985 = 5558989) B5558989
theorem B1644887 : Blo 972592 1644887 := bstep (se 1 (by rfl) ⟨1233665, by rfl⟩ : syracuseStep 1644887 = 2467331) B2467331
theorem B1645015 : Blo 972592 1645015 := bstep (se 1 (by rfl) ⟨1233761, by rfl⟩ : syracuseStep 1645015 = 2467523) B2467523
theorem B5544409 : Blo 972592 5544409 := bstep (se 2 (by rfl) ⟨2079153, by rfl⟩ : syracuseStep 5544409 = 4158307) B4158307
theorem B11082257 : Blo 972592 11082257 := bstep (se 2 (by rfl) ⟨4155846, by rfl⟩ : syracuseStep 11082257 = 8311693) B8311693
theorem B3119705 : Blo 972592 3119705 := bstep (se 2 (by rfl) ⟨1169889, by rfl⟩ : syracuseStep 3119705 = 2339779) B2339779
theorem B2464577 : Blo 972592 2464577 := bstep (se 2 (by rfl) ⟨924216, by rfl⟩ : syracuseStep 2464577 = 1848433) B1848433
theorem B1252247 : Blo 972592 1252247 := bstep (se 1 (by rfl) ⟨939185, by rfl⟩ : syracuseStep 1252247 = 1878371) B1878371
theorem B23665733 : Blo 972592 23665733 := bstep (se 4 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 23665733 = 4437325) B4437325
theorem B1645643 : Blo 972592 1645643 := bstep (se 1 (by rfl) ⟨1234232, by rfl⟩ : syracuseStep 1645643 = 2468465) B2468465
theorem B7511141 : Blo 972592 7511141 := bstep (se 4 (by rfl) ⟨704169, by rfl⟩ : syracuseStep 7511141 = 1408339) B1408339
theorem B2006155 : Blo 972592 2006155 := bstep (se 1 (by rfl) ⟨1504616, by rfl⟩ : syracuseStep 2006155 = 3009233) B3009233
theorem B3284171 : Blo 972592 3284171 := bstep (se 1 (by rfl) ⟨2463128, by rfl⟩ : syracuseStep 3284171 = 4926257) B4926257
theorem B1645771 : Blo 972592 1645771 := bstep (se 1 (by rfl) ⟨1234328, by rfl⟩ : syracuseStep 1645771 = 2468657) B2468657
theorem B2465113 : Blo 972592 2465113 := bstep (se 2 (by rfl) ⟨924417, by rfl⟩ : syracuseStep 2465113 = 1848835) B1848835
theorem B1645913 : Blo 972592 1645913 := bstep (se 2 (by rfl) ⟨617217, by rfl⟩ : syracuseStep 1645913 = 1234435) B1234435
theorem B5938525 : Blo 972592 5938525 := bstep (se 3 (by rfl) ⟨1113473, by rfl⟩ : syracuseStep 5938525 = 2226947) B2226947
theorem B5545367 : Blo 972592 5545367 := bstep (se 1 (by rfl) ⟨4159025, by rfl⟩ : syracuseStep 5545367 = 8318051) B8318051
theorem B3284441 : Blo 972592 3284441 := bstep (se 2 (by rfl) ⟨1231665, by rfl⟩ : syracuseStep 3284441 = 2463331) B2463331
theorem B1646041 : Blo 972592 1646041 := bstep (se 2 (by rfl) ⟨617265, by rfl⟩ : syracuseStep 1646041 = 1234531) B1234531
theorem B4497203 : Blo 972592 4497203 := bstep (se 1 (by rfl) ⟨3372902, by rfl⟩ : syracuseStep 4497203 = 6745805) B6745805
theorem B1646615 : Blo 972592 1646615 := bstep (se 1 (by rfl) ⟨1234961, by rfl⟩ : syracuseStep 1646615 = 2469923) B2469923
theorem B18980939 : Blo 972592 18980939 := bstep (se 1 (by rfl) ⟨14235704, by rfl⟩ : syracuseStep 18980939 = 28471409) B28471409
theorem B3285143 : Blo 972592 3285143 := bstep (se 1 (by rfl) ⟨2463857, by rfl⟩ : syracuseStep 3285143 = 4927715) B4927715
theorem B1646743 : Blo 972592 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B3121345 : Blo 972592 3121345 := bstep (se 2 (by rfl) ⟨1170504, by rfl⟩ : syracuseStep 3121345 = 2341009) B2341009
theorem B1974539 : Blo 972592 1974539 := bstep (se 1 (by rfl) ⟨1480904, by rfl⟩ : syracuseStep 1974539 = 2961809) B2961809
theorem B1319257 : Blo 972592 1319257 := bstep (se 2 (by rfl) ⟨494721, by rfl⟩ : syracuseStep 1319257 = 989443) B989443
theorem B4923827 : Blo 972592 4923827 := bstep (se 1 (by rfl) ⟨3692870, by rfl⟩ : syracuseStep 4923827 = 7385741) B7385741
theorem B2466227 : Blo 972592 2466227 := bstep (se 1 (by rfl) ⟨1849670, by rfl⟩ : syracuseStep 2466227 = 3699341) B3699341
theorem B3285683 : Blo 972592 3285683 := bstep (se 1 (by rfl) ⟨2464262, by rfl⟩ : syracuseStep 3285683 = 4928525) B4928525
theorem B2466521 : Blo 972592 2466521 := bstep (se 2 (by rfl) ⟨924945, by rfl⟩ : syracuseStep 2466521 = 1849891) B1849891
theorem B1647371 : Blo 972592 1647371 := bstep (se 1 (by rfl) ⟨1235528, by rfl⟩ : syracuseStep 1647371 = 2471057) B2471057
theorem B4170541 : Blo 972592 4170541 := bstep (se 3 (by rfl) ⟨781976, by rfl⟩ : syracuseStep 4170541 = 1563953) B1563953
theorem B1647499 : Blo 972592 1647499 := bstep (se 1 (by rfl) ⟨1235624, by rfl⟩ : syracuseStep 1647499 = 2471249) B2471249
theorem B3285953 : Blo 972592 3285953 := bstep (se 2 (by rfl) ⟨1232232, by rfl⟩ : syracuseStep 3285953 = 2464465) B2464465
theorem B1385419 : Blo 972592 1385419 := bstep (se 1 (by rfl) ⟨1039064, by rfl⟩ : syracuseStep 1385419 = 2078129) B2078129
theorem B1647641 : Blo 972592 1647641 := bstep (se 2 (by rfl) ⟨617865, by rfl⟩ : syracuseStep 1647641 = 1235731) B1235731
theorem B5350445 : Blo 972592 5350445 := bstep (se 3 (by rfl) ⟨1003208, by rfl⟩ : syracuseStep 5350445 = 2006417) B2006417
theorem B1647769 : Blo 972592 1647769 := bstep (se 2 (by rfl) ⟨617913, by rfl⟩ : syracuseStep 1647769 = 1235827) B1235827
theorem B1385687 : Blo 972592 1385687 := bstep (se 1 (by rfl) ⟨1039265, by rfl⟩ : syracuseStep 1385687 = 2078531) B2078531
theorem B7120133 : Blo 972592 7120133 := bstep (se 4 (by rfl) ⟨667512, by rfl⟩ : syracuseStep 7120133 = 1335025) B1335025
theorem B11085173 : Blo 972592 11085173 := bstep (se 5 (by rfl) ⟨519617, by rfl⟩ : syracuseStep 11085173 = 1039235) B1039235
theorem B3286493 : Blo 972592 3286493 := bstep (se 3 (by rfl) ⟨616217, by rfl⟩ : syracuseStep 3286493 = 1232435) B1232435
theorem B2631257 : Blo 972592 2631257 := bstep (se 2 (by rfl) ⟨986721, by rfl⟩ : syracuseStep 2631257 = 1973443) B1973443
theorem B5547851 : Blo 972592 5547851 := bstep (se 1 (by rfl) ⟨4160888, by rfl⟩ : syracuseStep 5547851 = 8321777) B8321777
theorem B7415873 : Blo 972592 7415873 := bstep (se 2 (by rfl) ⟨2780952, by rfl⟩ : syracuseStep 7415873 = 5561905) B5561905
theorem B85403717 : Blo 972592 85403717 := bstep (se 4 (by rfl) ⟨8006598, by rfl⟩ : syracuseStep 85403717 = 16013197) B16013197
theorem B1976395 : Blo 972592 1976395 := bstep (se 1 (by rfl) ⟨1482296, by rfl⟩ : syracuseStep 1976395 = 2964593) B2964593
theorem B1484875 : Blo 972592 1484875 := bstep (se 1 (by rfl) ⟨1113656, by rfl⟩ : syracuseStep 1484875 = 2227313) B2227313
theorem B1386649 : Blo 972592 1386649 := bstep (se 2 (by rfl) ⟨519993, by rfl⟩ : syracuseStep 1386649 = 1039987) B1039987
theorem B4925771 : Blo 972592 4925771 := bstep (se 1 (by rfl) ⟨3694328, by rfl⟩ : syracuseStep 4925771 = 7388657) B7388657
theorem B2468171 : Blo 972592 2468171 := bstep (se 1 (by rfl) ⟨1851128, by rfl⟩ : syracuseStep 2468171 = 3702257) B3702257
theorem B12495221 : Blo 972592 12495221 := bstep (se 5 (by rfl) ⟨585713, by rfl⟩ : syracuseStep 12495221 = 1171427) B1171427
theorem B2337203 : Blo 972592 2337203 := bstep (se 1 (by rfl) ⟨1752902, by rfl⟩ : syracuseStep 2337203 = 3505805) B3505805
theorem B3287627 : Blo 972592 3287627 := bstep (se 1 (by rfl) ⟨2465720, by rfl⟩ : syracuseStep 3287627 = 4931441) B4931441
theorem B2337473 : Blo 972592 2337473 := bstep (se 2 (by rfl) ⟨876552, by rfl⟩ : syracuseStep 2337473 = 1753105) B1753105
theorem B3287897 : Blo 972592 3287897 := bstep (se 2 (by rfl) ⟨1232961, by rfl⟩ : syracuseStep 3287897 = 2465923) B2465923
theorem B2632727 : Blo 972592 2632727 := bstep (se 1 (by rfl) ⟨1974545, by rfl⟩ : syracuseStep 2632727 = 3949091) B3949091
theorem B1846451 : Blo 972592 1846451 := bstep (se 1 (by rfl) ⟨1384838, by rfl⟩ : syracuseStep 1846451 = 2769677) B2769677
theorem B1846489 : Blo 972592 1846489 := bstep (se 2 (by rfl) ⟨692433, by rfl⟩ : syracuseStep 1846489 = 1384867) B1384867
theorem B2469143 : Blo 972592 2469143 := bstep (se 1 (by rfl) ⟨1851857, by rfl⟩ : syracuseStep 2469143 = 3703715) B3703715
theorem B4992529 : Blo 972592 4992529 := bstep (se 2 (by rfl) ⟨1872198, by rfl⟩ : syracuseStep 4992529 = 3744397) B3744397
theorem B3288599 : Blo 972592 3288599 := bstep (se 1 (by rfl) ⟨2466449, by rfl⟩ : syracuseStep 3288599 = 4932899) B4932899
theorem B1388107 : Blo 972592 1388107 := bstep (se 1 (by rfl) ⟨1041080, by rfl⟩ : syracuseStep 1388107 = 2082161) B2082161
theorem B1388119 : Blo 972592 1388119 := bstep (se 1 (by rfl) ⟨1041089, by rfl⟩ : syracuseStep 1388119 = 2082179) B2082179
theorem B1846937 : Blo 972592 1846937 := bstep (se 2 (by rfl) ⟨692601, by rfl⟩ : syracuseStep 1846937 = 1385203) B1385203
theorem B2633419 : Blo 972592 2633419 := bstep (se 1 (by rfl) ⟨1975064, by rfl⟩ : syracuseStep 2633419 = 3950129) B3950129
theorem B2469811 : Blo 972592 2469811 := bstep (se 1 (by rfl) ⟨1852358, by rfl⟩ : syracuseStep 2469811 = 3704717) B3704717
theorem B7909337 : Blo 972592 7909337 := bstep (se 2 (by rfl) ⟨2966001, by rfl⟩ : syracuseStep 7909337 = 5932003) B5932003
theorem B1585163 : Blo 972592 1585163 := bstep (se 1 (by rfl) ⟨1188872, by rfl⟩ : syracuseStep 1585163 = 2377745) B2377745
theorem B2961431 : Blo 972592 2961431 := bstep (se 1 (by rfl) ⟨2221073, by rfl⟩ : syracuseStep 2961431 = 4442147) B4442147
theorem B3289139 : Blo 972592 3289139 := bstep (se 1 (by rfl) ⟨2466854, by rfl⟩ : syracuseStep 3289139 = 4933709) B4933709
theorem B4927553 : Blo 972592 4927553 := bstep (se 2 (by rfl) ⟨1847832, by rfl⟩ : syracuseStep 4927553 = 3695665) B3695665
theorem B2469953 : Blo 972592 2469953 := bstep (se 2 (by rfl) ⟨926232, by rfl⟩ : syracuseStep 2469953 = 1852465) B1852465
theorem B3289409 : Blo 972592 3289409 := bstep (se 2 (by rfl) ⟨1233528, by rfl⟩ : syracuseStep 3289409 = 2467057) B2467057
theorem B1782131 : Blo 972592 1782131 := bstep (se 1 (by rfl) ⟨1336598, by rfl⟩ : syracuseStep 1782131 = 2673197) B2673197
theorem B1847681 : Blo 972592 1847681 := bstep (se 2 (by rfl) ⟨692880, by rfl⟩ : syracuseStep 1847681 = 1385761) B1385761
theorem B5550515 : Blo 972592 5550515 := bstep (se 1 (by rfl) ⟨4162886, by rfl⟩ : syracuseStep 5550515 = 8325773) B8325773
theorem B1094251 : Blo 972592 1094251 := bstep (se 1 (by rfl) ⟨820688, by rfl⟩ : syracuseStep 1094251 = 1641377) B1641377
theorem B1847947 : Blo 972592 1847947 := bstep (se 1 (by rfl) ⟨1385960, by rfl⟩ : syracuseStep 1847947 = 2771921) B2771921
theorem B1094359 : Blo 972592 1094359 := bstep (se 1 (by rfl) ⟨820769, by rfl⟩ : syracuseStep 1094359 = 1641539) B1641539
theorem B2077463 : Blo 972592 2077463 := bstep (se 1 (by rfl) ⟨1558097, by rfl⟩ : syracuseStep 2077463 = 3116195) B3116195
theorem B2503489 : Blo 972592 2503489 := bstep (se 2 (by rfl) ⟨938808, by rfl⟩ : syracuseStep 2503489 = 1877617) B1877617
theorem B3289949 : Blo 972592 3289949 := bstep (se 3 (by rfl) ⟨616865, by rfl⟩ : syracuseStep 3289949 = 1233731) B1233731
theorem B1094539 : Blo 972592 1094539 := bstep (se 1 (by rfl) ⟨820904, by rfl⟩ : syracuseStep 1094539 = 1641809) B1641809
theorem B2077643 : Blo 972592 2077643 := bstep (se 1 (by rfl) ⟨1558232, by rfl⟩ : syracuseStep 2077643 = 3116465) B3116465
theorem B1094647 : Blo 972592 1094647 := bstep (se 1 (by rfl) ⟨820985, by rfl⟩ : syracuseStep 1094647 = 1641971) B1641971
theorem B1848395 : Blo 972592 1848395 := bstep (se 1 (by rfl) ⟨1386296, by rfl⟩ : syracuseStep 1848395 = 2772593) B2772593
theorem B1094827 : Blo 972592 1094827 := bstep (se 1 (by rfl) ⟨821120, by rfl⟩ : syracuseStep 1094827 = 1642241) B1642241
theorem B1848577 : Blo 972592 1848577 := bstep (se 2 (by rfl) ⟨693216, by rfl⟩ : syracuseStep 1848577 = 1386433) B1386433
theorem B1094935 : Blo 972592 1094935 := bstep (se 1 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 1094935 = 1642403) B1642403
theorem B2471219 : Blo 972592 2471219 := bstep (se 1 (by rfl) ⟨1853414, by rfl⟩ : syracuseStep 2471219 = 3706829) B3706829
theorem B1979735 : Blo 972592 1979735 := bstep (se 1 (by rfl) ⟨1484801, by rfl⟩ : syracuseStep 1979735 = 2969603) B2969603
theorem B1095115 : Blo 972592 1095115 := bstep (se 1 (by rfl) ⟨821336, by rfl⟩ : syracuseStep 1095115 = 1642673) B1642673
theorem B1095223 : Blo 972592 1095223 := bstep (se 1 (by rfl) ⟨821417, by rfl⟩ : syracuseStep 1095223 = 1642835) B1642835
theorem B1848919 : Blo 972592 1848919 := bstep (se 1 (by rfl) ⟨1386689, by rfl⟩ : syracuseStep 1848919 = 2773379) B2773379
theorem B1390169 : Blo 972592 1390169 := bstep (se 2 (by rfl) ⟨521313, by rfl⟩ : syracuseStep 1390169 = 1042627) B1042627
theorem B3847873 : Blo 972592 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B1095403 : Blo 972592 1095403 := bstep (se 1 (by rfl) ⟨821552, by rfl⟩ : syracuseStep 1095403 = 1643105) B1643105
theorem B1849139 : Blo 972592 1849139 := bstep (se 1 (by rfl) ⟨1386854, by rfl⟩ : syracuseStep 1849139 = 2773709) B2773709
theorem B2471755 : Blo 972592 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B1095511 : Blo 972592 1095511 := bstep (se 1 (by rfl) ⟨821633, by rfl⟩ : syracuseStep 1095511 = 1643267) B1643267
theorem B5551973 : Blo 972592 5551973 := bstep (se 4 (by rfl) ⟨520497, by rfl⟩ : syracuseStep 5551973 = 1040995) B1040995
theorem B6240179 : Blo 972592 6240179 := bstep (se 1 (by rfl) ⟨4680134, by rfl⟩ : syracuseStep 6240179 = 9360269) B9360269
theorem B3291083 : Blo 972592 3291083 := bstep (se 1 (by rfl) ⟨2468312, by rfl⟩ : syracuseStep 3291083 = 4936625) B4936625
theorem B4929497 : Blo 972592 4929497 := bstep (se 2 (by rfl) ⟨1848561, by rfl⟩ : syracuseStep 4929497 = 3697123) B3697123
theorem B2471897 : Blo 972592 2471897 := bstep (se 2 (by rfl) ⟨926961, by rfl⟩ : syracuseStep 2471897 = 1853923) B1853923
theorem B1095691 : Blo 972592 1095691 := bstep (se 1 (by rfl) ⟨821768, by rfl⟩ : syracuseStep 1095691 = 1643537) B1643537
theorem B3749905 : Blo 972592 3749905 := bstep (se 2 (by rfl) ⟨1406214, by rfl⟩ : syracuseStep 3749905 = 2812429) B2812429
theorem B1849367 : Blo 972592 1849367 := bstep (se 1 (by rfl) ⟨1387025, by rfl⟩ : syracuseStep 1849367 = 2774051) B2774051
theorem B6240331 : Blo 972592 6240331 := bstep (se 1 (by rfl) ⟨4680248, by rfl⟩ : syracuseStep 6240331 = 9360497) B9360497
theorem B1095799 : Blo 972592 1095799 := bstep (se 1 (by rfl) ⟨821849, by rfl⟩ : syracuseStep 1095799 = 1643699) B1643699
theorem B3291353 : Blo 972592 3291353 := bstep (se 2 (by rfl) ⟨1234257, by rfl⟩ : syracuseStep 3291353 = 2468515) B2468515
theorem B1849625 : Blo 972592 1849625 := bstep (se 2 (by rfl) ⟨693609, by rfl⟩ : syracuseStep 1849625 = 1387219) B1387219
theorem B1095979 : Blo 972592 1095979 := bstep (se 1 (by rfl) ⟨821984, by rfl⟩ : syracuseStep 1095979 = 1643969) B1643969
theorem B7027037 : Blo 972592 7027037 := bstep (se 3 (by rfl) ⟨1317569, by rfl⟩ : syracuseStep 7027037 = 2635139) B2635139
theorem B1096087 : Blo 972592 1096087 := bstep (se 1 (by rfl) ⟨822065, by rfl⟩ : syracuseStep 1096087 = 1644131) B1644131
theorem B5552657 : Blo 972592 5552657 := bstep (se 2 (by rfl) ⟨2082246, by rfl⟩ : syracuseStep 5552657 = 4164493) B4164493
theorem B8337937 : Blo 972592 8337937 := bstep (se 2 (by rfl) ⟨3126726, by rfl⟩ : syracuseStep 8337937 = 6253453) B6253453
theorem B2079283 : Blo 972592 2079283 := bstep (se 1 (by rfl) ⟨1559462, by rfl⟩ : syracuseStep 2079283 = 3118925) B3118925
theorem B1096267 : Blo 972592 1096267 := bstep (se 1 (by rfl) ⟨822200, by rfl⟩ : syracuseStep 1096267 = 1644401) B1644401
theorem B1850035 : Blo 972592 1850035 := bstep (se 1 (by rfl) ⟨1387526, by rfl⟩ : syracuseStep 1850035 = 2775053) B2775053
theorem B1096375 : Blo 972592 1096375 := bstep (se 1 (by rfl) ⟨822281, by rfl⟩ : syracuseStep 1096375 = 1644563) B1644563
theorem B14072525 : Blo 972592 14072525 := bstep (se 3 (by rfl) ⟨2638598, by rfl⟩ : syracuseStep 14072525 = 5277197) B5277197
theorem B2341655 : Blo 972592 2341655 := bstep (se 1 (by rfl) ⟨1756241, by rfl⟩ : syracuseStep 2341655 = 3512483) B3512483
theorem B8338211 : Blo 972592 8338211 := bstep (se 1 (by rfl) ⟨6253658, by rfl⟩ : syracuseStep 8338211 = 12507317) B12507317
theorem B3947339 : Blo 972592 3947339 := bstep (se 1 (by rfl) ⟨2960504, by rfl⟩ : syracuseStep 3947339 = 5921009) B5921009
theorem B3521369 : Blo 972592 3521369 := bstep (se 2 (by rfl) ⟨1320513, by rfl⟩ : syracuseStep 3521369 = 2641027) B2641027
theorem B1096555 : Blo 972592 1096555 := bstep (se 1 (by rfl) ⟨822416, by rfl⟩ : syracuseStep 1096555 = 1644833) B1644833
theorem B3292055 : Blo 972592 3292055 := bstep (se 1 (by rfl) ⟨2469041, by rfl⟩ : syracuseStep 3292055 = 4938083) B4938083
theorem B1096663 : Blo 972592 1096663 := bstep (se 1 (by rfl) ⟨822497, by rfl⟩ : syracuseStep 1096663 = 1644995) B1644995
theorem B2079769 : Blo 972592 2079769 := bstep (se 2 (by rfl) ⟨779913, by rfl⟩ : syracuseStep 2079769 = 1559827) B1559827
theorem B1096843 : Blo 972592 1096843 := bstep (se 1 (by rfl) ⟨822632, by rfl⟩ : syracuseStep 1096843 = 1645265) B1645265
theorem B1850521 : Blo 972592 1850521 := bstep (se 2 (by rfl) ⟨693945, by rfl⟩ : syracuseStep 1850521 = 1387891) B1387891
theorem B1096951 : Blo 972592 1096951 := bstep (se 1 (by rfl) ⟨822713, by rfl⟩ : syracuseStep 1096951 = 1645427) B1645427
theorem B7027985 : Blo 972592 7027985 := bstep (se 2 (by rfl) ⟨2635494, by rfl⟩ : syracuseStep 7027985 = 5270989) B5270989
theorem B1097131 : Blo 972592 1097131 := bstep (se 1 (by rfl) ⟨822848, by rfl⟩ : syracuseStep 1097131 = 1645697) B1645697
theorem B3292595 : Blo 972592 3292595 := bstep (se 1 (by rfl) ⟨2469446, by rfl⟩ : syracuseStep 3292595 = 4938893) B4938893
theorem B1097239 : Blo 972592 1097239 := bstep (se 1 (by rfl) ⟨822929, by rfl⟩ : syracuseStep 1097239 = 1645859) B1645859
theorem B2637335 : Blo 972592 2637335 := bstep (se 1 (by rfl) ⟨1978001, by rfl⟩ : syracuseStep 2637335 = 3956003) B3956003
theorem B4931117 : Blo 972592 4931117 := bstep (se 3 (by rfl) ⟨924584, by rfl⟩ : syracuseStep 4931117 = 1849169) B1849169
theorem B11878019 : Blo 972592 11878019 := bstep (se 1 (by rfl) ⟨8908514, by rfl⟩ : syracuseStep 11878019 = 17817029) B17817029
theorem B3292865 : Blo 972592 3292865 := bstep (se 2 (by rfl) ⟨1234824, by rfl⟩ : syracuseStep 3292865 = 2469649) B2469649
theorem B1851083 : Blo 972592 1851083 := bstep (se 1 (by rfl) ⟨1388312, by rfl⟩ : syracuseStep 1851083 = 2776625) B2776625
theorem B1097419 : Blo 972592 1097419 := bstep (se 1 (by rfl) ⟨823064, by rfl⟩ : syracuseStep 1097419 = 1646129) B1646129
theorem B1097527 : Blo 972592 1097527 := bstep (se 1 (by rfl) ⟨823145, by rfl⟩ : syracuseStep 1097527 = 1646291) B1646291
theorem B1752961 : Blo 972592 1752961 := bstep (se 2 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 1752961 = 1314721) B1314721
theorem B1851265 : Blo 972592 1851265 := bstep (se 2 (by rfl) ⟨694224, by rfl⟩ : syracuseStep 1851265 = 1388449) B1388449
theorem B1097707 : Blo 972592 1097707 := bstep (se 1 (by rfl) ⟨823280, by rfl⟩ : syracuseStep 1097707 = 1646561) B1646561
theorem B1097815 : Blo 972592 1097815 := bstep (se 1 (by rfl) ⟨823361, by rfl⟩ : syracuseStep 1097815 = 1646723) B1646723
theorem B3293405 : Blo 972592 3293405 := bstep (se 3 (by rfl) ⟨617513, by rfl⟩ : syracuseStep 3293405 = 1235027) B1235027
theorem B1097995 : Blo 972592 1097995 := bstep (se 1 (by rfl) ⟨823496, by rfl⟩ : syracuseStep 1097995 = 1646993) B1646993
theorem B1098103 : Blo 972592 1098103 := bstep (se 1 (by rfl) ⟨823577, by rfl⟩ : syracuseStep 1098103 = 1647155) B1647155
theorem B2081153 : Blo 972592 2081153 := bstep (se 2 (by rfl) ⟨780432, by rfl⟩ : syracuseStep 2081153 = 1560865) B1560865
theorem B23708173 : Blo 972592 23708173 := bstep (se 3 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 23708173 = 8890565) B8890565
theorem B1098283 : Blo 972592 1098283 := bstep (se 1 (by rfl) ⟨823712, by rfl⟩ : syracuseStep 1098283 = 1647425) B1647425
theorem B1851979 : Blo 972592 1851979 := bstep (se 1 (by rfl) ⟨1388984, by rfl⟩ : syracuseStep 1851979 = 2777969) B2777969
theorem B1852055 : Blo 972592 1852055 := bstep (se 1 (by rfl) ⟨1389041, by rfl⟩ : syracuseStep 1852055 = 2778083) B2778083
theorem B1098391 : Blo 972592 1098391 := bstep (se 1 (by rfl) ⟨823793, by rfl⟩ : syracuseStep 1098391 = 1647587) B1647587
theorem B1458905 : Blo 972592 1458905 := bstep (se 2 (by rfl) ⟨547089, by rfl⟩ : syracuseStep 1458905 = 1094179) B1094179
theorem B1459019 : Blo 972592 1459019 := bstep (se 1 (by rfl) ⟨1094264, by rfl⟩ : syracuseStep 1459019 = 2188529) B2188529
theorem B1098571 : Blo 972592 1098571 := bstep (se 1 (by rfl) ⟨823928, by rfl⟩ : syracuseStep 1098571 = 1647857) B1647857
theorem B1459031 : Blo 972592 1459031 := bstep (se 1 (by rfl) ⟨1094273, by rfl⟩ : syracuseStep 1459031 = 2188547) B2188547
theorem B2081675 : Blo 972592 2081675 := bstep (se 1 (by rfl) ⟨1561256, by rfl⟩ : syracuseStep 2081675 = 3122513) B3122513
theorem B1459097 : Blo 972592 1459097 := bstep (se 2 (by rfl) ⟨547161, by rfl⟩ : syracuseStep 1459097 = 1094323) B1094323
theorem B1459211 : Blo 972592 1459211 := bstep (se 1 (by rfl) ⟨1094408, by rfl⟩ : syracuseStep 1459211 = 2188817) B2188817
theorem B1459223 : Blo 972592 1459223 := bstep (se 1 (by rfl) ⟨1094417, by rfl⟩ : syracuseStep 1459223 = 2188835) B2188835
theorem B1459289 : Blo 972592 1459289 := bstep (se 2 (by rfl) ⟨547233, by rfl⟩ : syracuseStep 1459289 = 1094467) B1094467
theorem B2671795 : Blo 972592 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B2344115 : Blo 972592 2344115 := bstep (se 1 (by rfl) ⟨1758086, by rfl⟩ : syracuseStep 2344115 = 3516173) B3516173
theorem B1459403 : Blo 972592 1459403 := bstep (se 1 (by rfl) ⟨1094552, by rfl⟩ : syracuseStep 1459403 = 2189105) B2189105
theorem B1459415 : Blo 972592 1459415 := bstep (se 1 (by rfl) ⟨1094561, by rfl⟩ : syracuseStep 1459415 = 2189123) B2189123
theorem B1459481 : Blo 972592 1459481 := bstep (se 2 (by rfl) ⟨547305, by rfl⟩ : syracuseStep 1459481 = 1094611) B1094611
theorem B7030061 : Blo 972592 7030061 := bstep (se 3 (by rfl) ⟨1318136, by rfl⟩ : syracuseStep 7030061 = 2636273) B2636273
theorem B1852723 : Blo 972592 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B3294539 : Blo 972592 3294539 := bstep (se 1 (by rfl) ⟨2470904, by rfl⟩ : syracuseStep 3294539 = 4941809) B4941809
theorem B1459595 : Blo 972592 1459595 := bstep (se 1 (by rfl) ⟨1094696, by rfl⟩ : syracuseStep 1459595 = 2189393) B2189393
theorem B1459607 : Blo 972592 1459607 := bstep (se 1 (by rfl) ⟨1094705, by rfl⟩ : syracuseStep 1459607 = 2189411) B2189411
theorem B1459673 : Blo 972592 1459673 := bstep (se 2 (by rfl) ⟨547377, by rfl⟩ : syracuseStep 1459673 = 1094755) B1094755
theorem B1852951 : Blo 972592 1852951 := bstep (se 1 (by rfl) ⟨1389713, by rfl⟩ : syracuseStep 1852951 = 2779427) B2779427
theorem B1459787 : Blo 972592 1459787 := bstep (se 1 (by rfl) ⟨1094840, by rfl⟩ : syracuseStep 1459787 = 2189681) B2189681
theorem B1459799 : Blo 972592 1459799 := bstep (se 1 (by rfl) ⟨1094849, by rfl⟩ : syracuseStep 1459799 = 2189699) B2189699
theorem B3294809 : Blo 972592 3294809 := bstep (se 2 (by rfl) ⟨1235553, by rfl⟩ : syracuseStep 3294809 = 2471107) B2471107
theorem B1853057 : Blo 972592 1853057 := bstep (se 2 (by rfl) ⟨694896, by rfl⟩ : syracuseStep 1853057 = 1389793) B1389793
theorem B1459865 : Blo 972592 1459865 := bstep (se 2 (by rfl) ⟨547449, by rfl⟩ : syracuseStep 1459865 = 1094899) B1094899
theorem B5555891 : Blo 972592 5555891 := bstep (se 1 (by rfl) ⟨4166918, by rfl⟩ : syracuseStep 5555891 = 8333837) B8333837
theorem B1558283 : Blo 972592 1558283 := bstep (se 1 (by rfl) ⟨1168712, by rfl⟩ : syracuseStep 1558283 = 2337425) B2337425
theorem B1459979 : Blo 972592 1459979 := bstep (se 1 (by rfl) ⟨1094984, by rfl⟩ : syracuseStep 1459979 = 2189969) B2189969
theorem B1459991 : Blo 972592 1459991 := bstep (se 1 (by rfl) ⟨1094993, by rfl⟩ : syracuseStep 1459991 = 2189987) B2189987
theorem B1853209 : Blo 972592 1853209 := bstep (se 2 (by rfl) ⟨694953, by rfl⟩ : syracuseStep 1853209 = 1389907) B1389907
theorem B1460057 : Blo 972592 1460057 := bstep (se 2 (by rfl) ⟨547521, by rfl⟩ : syracuseStep 1460057 = 1095043) B1095043
theorem B39929699 : Blo 972592 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B1460171 : Blo 972592 1460171 := bstep (se 1 (by rfl) ⟨1095128, by rfl⟩ : syracuseStep 1460171 = 2190257) B2190257
theorem B1460183 : Blo 972592 1460183 := bstep (se 1 (by rfl) ⟨1095137, by rfl⟩ : syracuseStep 1460183 = 2190275) B2190275
theorem B1460249 : Blo 972592 1460249 := bstep (se 2 (by rfl) ⟨547593, by rfl⟩ : syracuseStep 1460249 = 1095187) B1095187
theorem B2082905 : Blo 972592 2082905 := bstep (se 2 (by rfl) ⟨781089, by rfl⟩ : syracuseStep 2082905 = 1562179) B1562179
theorem B1460363 : Blo 972592 1460363 := bstep (se 1 (by rfl) ⟨1095272, by rfl⟩ : syracuseStep 1460363 = 2190545) B2190545
theorem B1460375 : Blo 972592 1460375 := bstep (se 1 (by rfl) ⟨1095281, by rfl⟩ : syracuseStep 1460375 = 2190563) B2190563
theorem B1460441 : Blo 972592 1460441 := bstep (se 2 (by rfl) ⟨547665, by rfl⟩ : syracuseStep 1460441 = 1095331) B1095331
theorem B3295511 : Blo 972592 3295511 := bstep (se 1 (by rfl) ⟨2471633, by rfl⟩ : syracuseStep 3295511 = 4943267) B4943267
theorem B1460555 : Blo 972592 1460555 := bstep (se 1 (by rfl) ⟨1095416, by rfl⟩ : syracuseStep 1460555 = 2190833) B2190833
theorem B1460567 : Blo 972592 1460567 := bstep (se 1 (by rfl) ⟨1095425, by rfl⟩ : syracuseStep 1460567 = 2190851) B2190851
theorem B1460633 : Blo 972592 1460633 := bstep (se 2 (by rfl) ⟨547737, by rfl⟩ : syracuseStep 1460633 = 1095475) B1095475
theorem B3164609 : Blo 972592 3164609 := bstep (se 2 (by rfl) ⟨1186728, by rfl⟩ : syracuseStep 3164609 = 2373457) B2373457
theorem B1755607 : Blo 972592 1755607 := bstep (se 1 (by rfl) ⟨1316705, by rfl⟩ : syracuseStep 1755607 = 2633411) B2633411
theorem B2083315 : Blo 972592 2083315 := bstep (se 1 (by rfl) ⟨1562486, by rfl⟩ : syracuseStep 2083315 = 3124973) B3124973
theorem B1460747 : Blo 972592 1460747 := bstep (se 1 (by rfl) ⟨1095560, by rfl⟩ : syracuseStep 1460747 = 2191121) B2191121
theorem B1460759 : Blo 972592 1460759 := bstep (se 1 (by rfl) ⟨1095569, by rfl⟩ : syracuseStep 1460759 = 2191139) B2191139
theorem B1460825 : Blo 972592 1460825 := bstep (se 2 (by rfl) ⟨547809, by rfl⟩ : syracuseStep 1460825 = 1095619) B1095619
theorem B1460939 : Blo 972592 1460939 := bstep (se 1 (by rfl) ⟨1095704, by rfl⟩ : syracuseStep 1460939 = 2191409) B2191409
theorem B1460951 : Blo 972592 1460951 := bstep (se 1 (by rfl) ⟨1095713, by rfl⟩ : syracuseStep 1460951 = 2191427) B2191427
theorem B1461017 : Blo 972592 1461017 := bstep (se 2 (by rfl) ⟨547881, by rfl⟩ : syracuseStep 1461017 = 1095763) B1095763
theorem B7129957 : Blo 972592 7129957 := bstep (se 4 (by rfl) ⟨668433, by rfl⟩ : syracuseStep 7129957 = 1336867) B1336867
theorem B1461131 : Blo 972592 1461131 := bstep (se 1 (by rfl) ⟨1095848, by rfl⟩ : syracuseStep 1461131 = 2191697) B2191697
theorem B1461143 : Blo 972592 1461143 := bstep (se 1 (by rfl) ⟨1095857, by rfl⟩ : syracuseStep 1461143 = 2191715) B2191715
theorem B22465457 : Blo 972592 22465457 := bstep (se 2 (by rfl) ⟨8424546, by rfl⟩ : syracuseStep 22465457 = 16849093) B16849093
theorem B1461209 : Blo 972592 1461209 := bstep (se 2 (by rfl) ⟨547953, by rfl⟩ : syracuseStep 1461209 = 1095907) B1095907
theorem B2083801 : Blo 972592 2083801 := bstep (se 2 (by rfl) ⟨781425, by rfl⟩ : syracuseStep 2083801 = 1562851) B1562851
theorem B1461323 : Blo 972592 1461323 := bstep (se 1 (by rfl) ⟨1095992, by rfl⟩ : syracuseStep 1461323 = 2191985) B2191985
theorem B1461335 : Blo 972592 1461335 := bstep (se 1 (by rfl) ⟨1096001, by rfl⟩ : syracuseStep 1461335 = 2192003) B2192003
theorem B5557349 : Blo 972592 5557349 := bstep (se 4 (by rfl) ⟨521001, by rfl⟩ : syracuseStep 5557349 = 1042003) B1042003
theorem B1461401 : Blo 972592 1461401 := bstep (se 2 (by rfl) ⟨548025, by rfl⟩ : syracuseStep 1461401 = 1096051) B1096051
theorem B1756363 : Blo 972592 1756363 := bstep (se 1 (by rfl) ⟨1317272, by rfl⟩ : syracuseStep 1756363 = 2634545) B2634545
theorem B1461515 : Blo 972592 1461515 := bstep (se 1 (by rfl) ⟨1096136, by rfl⟩ : syracuseStep 1461515 = 2192273) B2192273
theorem B1461527 : Blo 972592 1461527 := bstep (se 1 (by rfl) ⟨1096145, by rfl⟩ : syracuseStep 1461527 = 2192291) B2192291
theorem B6016301 : Blo 972592 6016301 := bstep (se 3 (by rfl) ⟨1128056, by rfl⟩ : syracuseStep 6016301 = 2256113) B2256113
theorem B1461593 : Blo 972592 1461593 := bstep (se 2 (by rfl) ⟨548097, by rfl⟩ : syracuseStep 1461593 = 1096195) B1096195
theorem B4935005 : Blo 972592 4935005 := bstep (se 3 (by rfl) ⟨925313, by rfl⟩ : syracuseStep 4935005 = 1850627) B1850627
theorem B1461707 : Blo 972592 1461707 := bstep (se 1 (by rfl) ⟨1096280, by rfl⟩ : syracuseStep 1461707 = 2192561) B2192561
theorem B1461719 : Blo 972592 1461719 := bstep (se 1 (by rfl) ⟨1096289, by rfl⟩ : syracuseStep 1461719 = 2192579) B2192579
theorem B1461785 : Blo 972592 1461785 := bstep (se 2 (by rfl) ⟨548169, by rfl⟩ : syracuseStep 1461785 = 1096339) B1096339
theorem B5557805 : Blo 972592 5557805 := bstep (se 3 (by rfl) ⟨1042088, by rfl⟩ : syracuseStep 5557805 = 2084177) B2084177
theorem B2772569 : Blo 972592 2772569 := bstep (se 2 (by rfl) ⟨1039713, by rfl⟩ : syracuseStep 2772569 = 2079427) B2079427
theorem B1461899 : Blo 972592 1461899 := bstep (se 1 (by rfl) ⟨1096424, by rfl⟩ : syracuseStep 1461899 = 2192849) B2192849
theorem B1461911 : Blo 972592 1461911 := bstep (se 1 (by rfl) ⟨1096433, by rfl⟩ : syracuseStep 1461911 = 2192867) B2192867
theorem B2084545 : Blo 972592 2084545 := bstep (se 2 (by rfl) ⟨781704, by rfl⟩ : syracuseStep 2084545 = 1563409) B1563409
theorem B1232587 : Blo 972592 1232587 := bstep (se 1 (by rfl) ⟨924440, by rfl⟩ : syracuseStep 1232587 = 1848881) B1848881
theorem B1461977 : Blo 972592 1461977 := bstep (se 2 (by rfl) ⟨548241, by rfl⟩ : syracuseStep 1461977 = 1096483) B1096483
theorem B1756939 : Blo 972592 1756939 := bstep (se 1 (by rfl) ⟨1317704, by rfl⟩ : syracuseStep 1756939 = 2635409) B2635409
theorem B1462091 : Blo 972592 1462091 := bstep (se 1 (by rfl) ⟨1096568, by rfl⟩ : syracuseStep 1462091 = 2193137) B2193137
theorem B1462103 : Blo 972592 1462103 := bstep (se 1 (by rfl) ⟨1096577, by rfl⟩ : syracuseStep 1462103 = 2193155) B2193155
theorem B1462169 : Blo 972592 1462169 := bstep (se 2 (by rfl) ⟨548313, by rfl⟩ : syracuseStep 1462169 = 1096627) B1096627
theorem B1462283 : Blo 972592 1462283 := bstep (se 1 (by rfl) ⟨1096712, by rfl⟩ : syracuseStep 1462283 = 2193425) B2193425
theorem B1462295 : Blo 972592 1462295 := bstep (se 1 (by rfl) ⟨1096721, by rfl⟩ : syracuseStep 1462295 = 2193443) B2193443
theorem B1462361 : Blo 972592 1462361 := bstep (se 2 (by rfl) ⟨548385, by rfl⟩ : syracuseStep 1462361 = 1096771) B1096771
theorem B7491685 : Blo 972592 7491685 := bstep (se 4 (by rfl) ⟨702345, by rfl⟩ : syracuseStep 7491685 = 1404691) B1404691
theorem B1462475 : Blo 972592 1462475 := bstep (se 1 (by rfl) ⟨1096856, by rfl⟩ : syracuseStep 1462475 = 2193713) B2193713
theorem B1462487 : Blo 972592 1462487 := bstep (se 1 (by rfl) ⟨1096865, by rfl⟩ : syracuseStep 1462487 = 2193731) B2193731
theorem B5558489 : Blo 972592 5558489 := bstep (se 2 (by rfl) ⟨2084433, by rfl⟩ : syracuseStep 5558489 = 4168867) B4168867
theorem B1462553 : Blo 972592 1462553 := bstep (se 2 (by rfl) ⟨548457, by rfl⟩ : syracuseStep 1462553 = 1096915) B1096915
theorem B1462667 : Blo 972592 1462667 := bstep (se 1 (by rfl) ⟨1097000, by rfl⟩ : syracuseStep 1462667 = 2194001) B2194001
theorem B1462679 : Blo 972592 1462679 := bstep (se 1 (by rfl) ⟨1097009, by rfl⟩ : syracuseStep 1462679 = 2194019) B2194019
theorem B1462745 : Blo 972592 1462745 := bstep (se 2 (by rfl) ⟨548529, by rfl⟩ : syracuseStep 1462745 = 1097059) B1097059
theorem B1462859 : Blo 972592 1462859 := bstep (se 1 (by rfl) ⟨1097144, by rfl⟩ : syracuseStep 1462859 = 2194289) B2194289
theorem B1462871 : Blo 972592 1462871 := bstep (se 1 (by rfl) ⟨1097153, by rfl⟩ : syracuseStep 1462871 = 2194307) B2194307
theorem B1233559 : Blo 972592 1233559 := bstep (se 1 (by rfl) ⟨925169, by rfl⟩ : syracuseStep 1233559 = 1850339) B1850339
theorem B2085527 : Blo 972592 2085527 := bstep (se 1 (by rfl) ⟨1564145, by rfl⟩ : syracuseStep 2085527 = 3128291) B3128291
theorem B1462937 : Blo 972592 1462937 := bstep (se 2 (by rfl) ⟨548601, by rfl⟩ : syracuseStep 1462937 = 1097203) B1097203
theorem B11096837 : Blo 972592 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B1463051 : Blo 972592 1463051 := bstep (se 1 (by rfl) ⟨1097288, by rfl⟩ : syracuseStep 1463051 = 2194577) B2194577
theorem B1463063 : Blo 972592 1463063 := bstep (se 1 (by rfl) ⟨1097297, by rfl⟩ : syracuseStep 1463063 = 2194595) B2194595
theorem B2773835 : Blo 972592 2773835 := bstep (se 1 (by rfl) ⟨2080376, by rfl⟩ : syracuseStep 2773835 = 4160753) B4160753
theorem B1463129 : Blo 972592 1463129 := bstep (se 2 (by rfl) ⟨548673, by rfl⟩ : syracuseStep 1463129 = 1097347) B1097347
theorem B1463243 : Blo 972592 1463243 := bstep (se 1 (by rfl) ⟨1097432, by rfl⟩ : syracuseStep 1463243 = 2194865) B2194865
theorem B1463255 : Blo 972592 1463255 := bstep (se 1 (by rfl) ⟨1097441, by rfl⟩ : syracuseStep 1463255 = 2194883) B2194883
theorem B1463321 : Blo 972592 1463321 := bstep (se 2 (by rfl) ⟨548745, by rfl⟩ : syracuseStep 1463321 = 1097491) B1097491
theorem B3658841 : Blo 972592 3658841 := bstep (se 2 (by rfl) ⟨1372065, by rfl⟩ : syracuseStep 3658841 = 2744131) B2744131
theorem B1758323 : Blo 972592 1758323 := bstep (se 1 (by rfl) ⟨1318742, by rfl⟩ : syracuseStep 1758323 = 2637485) B2637485
theorem B1463435 : Blo 972592 1463435 := bstep (se 1 (by rfl) ⟨1097576, by rfl⟩ : syracuseStep 1463435 = 2195153) B2195153
theorem B1463447 : Blo 972592 1463447 := bstep (se 1 (by rfl) ⟨1097585, by rfl⟩ : syracuseStep 1463447 = 2195171) B2195171
theorem B1463513 : Blo 972592 1463513 := bstep (se 2 (by rfl) ⟨548817, by rfl⟩ : syracuseStep 1463513 = 1097635) B1097635
theorem B1463627 : Blo 972592 1463627 := bstep (se 1 (by rfl) ⟨1097720, by rfl⟩ : syracuseStep 1463627 = 2195441) B2195441
theorem B1463639 : Blo 972592 1463639 := bstep (se 1 (by rfl) ⟨1097729, by rfl⟩ : syracuseStep 1463639 = 2195459) B2195459
theorem B1758553 : Blo 972592 1758553 := bstep (se 2 (by rfl) ⟨659457, by rfl⟩ : syracuseStep 1758553 = 1318915) B1318915
theorem B3003799 : Blo 972592 3003799 := bstep (se 1 (by rfl) ⟨2252849, by rfl⟩ : syracuseStep 3003799 = 4505699) B4505699
theorem B4937111 : Blo 972592 4937111 := bstep (se 1 (by rfl) ⟨3702833, by rfl⟩ : syracuseStep 4937111 = 7405667) B7405667
theorem B1463705 : Blo 972592 1463705 := bstep (se 2 (by rfl) ⟨548889, by rfl⟩ : syracuseStep 1463705 = 1097779) B1097779
theorem B1234379 : Blo 972592 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B4281821 : Blo 972592 4281821 := bstep (se 3 (by rfl) ⟨802841, by rfl⟩ : syracuseStep 4281821 = 1605683) B1605683
theorem B1463819 : Blo 972592 1463819 := bstep (se 1 (by rfl) ⟨1097864, by rfl⟩ : syracuseStep 1463819 = 2195729) B2195729
theorem B1463831 : Blo 972592 1463831 := bstep (se 1 (by rfl) ⟨1097873, by rfl⟩ : syracuseStep 1463831 = 2195747) B2195747
theorem B1463897 : Blo 972592 1463897 := bstep (se 2 (by rfl) ⟨548961, by rfl⟩ : syracuseStep 1463897 = 1097923) B1097923
theorem B1464011 : Blo 972592 1464011 := bstep (se 1 (by rfl) ⟨1098008, by rfl⟩ : syracuseStep 1464011 = 2196017) B2196017
theorem B1005259 : Blo 972592 1005259 := bstep (se 1 (by rfl) ⟨753944, by rfl⟩ : syracuseStep 1005259 = 1507889) B1507889
theorem B1169111 : Blo 972592 1169111 := bstep (se 1 (by rfl) ⟨876833, by rfl⟩ : syracuseStep 1169111 = 1753667) B1753667
theorem B1464023 : Blo 972592 1464023 := bstep (se 1 (by rfl) ⟨1098017, by rfl⟩ : syracuseStep 1464023 = 2196035) B2196035
theorem B4445975 : Blo 972592 4445975 := bstep (se 1 (by rfl) ⟨3334481, by rfl⟩ : syracuseStep 4445975 = 6668963) B6668963
theorem B1464089 : Blo 972592 1464089 := bstep (se 2 (by rfl) ⟨549033, by rfl⟩ : syracuseStep 1464089 = 1098067) B1098067
theorem B972599 : Blo 972592 972599 := bstep (se 1 (by rfl) ⟨729449, by rfl⟩ : syracuseStep 972599 = 1458899) B1458899
theorem B972619 : Blo 972592 972619 := bstep (se 1 (by rfl) ⟨729464, by rfl⟩ : syracuseStep 972619 = 1458929) B1458929
theorem B8312651 : Blo 972592 8312651 := bstep (se 1 (by rfl) ⟨6234488, by rfl⟩ : syracuseStep 8312651 = 12468977) B12468977
theorem B972631 : Blo 972592 972631 := bstep (se 1 (by rfl) ⟨729473, by rfl⟩ : syracuseStep 972631 = 1458947) B1458947
theorem B972651 : Blo 972592 972651 := bstep (se 1 (by rfl) ⟨729488, by rfl⟩ : syracuseStep 972651 = 1458977) B1458977
theorem B972663 : Blo 972592 972663 := bstep (se 1 (by rfl) ⟨729497, by rfl⟩ : syracuseStep 972663 = 1458995) B1458995
theorem B972683 : Blo 972592 972683 := bstep (se 1 (by rfl) ⟨729512, by rfl⟩ : syracuseStep 972683 = 1459025) B1459025
theorem B1464203 : Blo 972592 1464203 := bstep (se 1 (by rfl) ⟨1098152, by rfl⟩ : syracuseStep 1464203 = 2196305) B2196305
theorem B972695 : Blo 972592 972695 := bstep (se 1 (by rfl) ⟨729521, by rfl⟩ : syracuseStep 972695 = 1459043) B1459043
theorem B1464215 : Blo 972592 1464215 := bstep (se 1 (by rfl) ⟨1098161, by rfl⟩ : syracuseStep 1464215 = 2196323) B2196323
theorem B972715 : Blo 972592 972715 := bstep (se 1 (by rfl) ⟨729536, by rfl⟩ : syracuseStep 972715 = 1459073) B1459073
theorem B972727 : Blo 972592 972727 := bstep (se 1 (by rfl) ⟨729545, by rfl⟩ : syracuseStep 972727 = 1459091) B1459091
theorem B972747 : Blo 972592 972747 := bstep (se 1 (by rfl) ⟨729560, by rfl⟩ : syracuseStep 972747 = 1459121) B1459121
theorem B972759 : Blo 972592 972759 := bstep (se 1 (by rfl) ⟨729569, by rfl⟩ : syracuseStep 972759 = 1459139) B1459139
theorem B1464281 : Blo 972592 1464281 := bstep (se 2 (by rfl) ⟨549105, by rfl⟩ : syracuseStep 1464281 = 1098211) B1098211
theorem B972779 : Blo 972592 972779 := bstep (se 1 (by rfl) ⟨729584, by rfl⟩ : syracuseStep 972779 = 1459169) B1459169
theorem B972791 : Blo 972592 972791 := bstep (se 1 (by rfl) ⟨729593, by rfl⟩ : syracuseStep 972791 = 1459187) B1459187
theorem B972811 : Blo 972592 972811 := bstep (se 1 (by rfl) ⟨729608, by rfl⟩ : syracuseStep 972811 = 1459217) B1459217
theorem B1169419 : Blo 972592 1169419 := bstep (se 1 (by rfl) ⟨877064, by rfl⟩ : syracuseStep 1169419 = 1754129) B1754129
theorem B972823 : Blo 972592 972823 := bstep (se 1 (by rfl) ⟨729617, by rfl⟩ : syracuseStep 972823 = 1459235) B1459235
theorem B2250775 : Blo 972592 2250775 := bstep (se 1 (by rfl) ⟨1688081, by rfl⟩ : syracuseStep 2250775 = 3376163) B3376163
theorem B972843 : Blo 972592 972843 := bstep (se 1 (by rfl) ⟨729632, by rfl⟩ : syracuseStep 972843 = 1459265) B1459265
theorem B5003309 : Blo 972592 5003309 := bstep (se 3 (by rfl) ⟨938120, by rfl⟩ : syracuseStep 5003309 = 1876241) B1876241
theorem B972855 : Blo 972592 972855 := bstep (se 1 (by rfl) ⟨729641, by rfl⟩ : syracuseStep 972855 = 1459283) B1459283
theorem B972875 : Blo 972592 972875 := bstep (se 1 (by rfl) ⟨729656, by rfl⟩ : syracuseStep 972875 = 1459313) B1459313
theorem B1464395 : Blo 972592 1464395 := bstep (se 1 (by rfl) ⟨1098296, by rfl⟩ : syracuseStep 1464395 = 2196593) B2196593
theorem B972887 : Blo 972592 972887 := bstep (se 1 (by rfl) ⟨729665, by rfl⟩ : syracuseStep 972887 = 1459331) B1459331
theorem B1464407 : Blo 972592 1464407 := bstep (se 1 (by rfl) ⟨1098305, by rfl⟩ : syracuseStep 1464407 = 2196611) B2196611
theorem B972907 : Blo 972592 972907 := bstep (se 1 (by rfl) ⟨729680, by rfl⟩ : syracuseStep 972907 = 1459361) B1459361
theorem B972919 : Blo 972592 972919 := bstep (se 1 (by rfl) ⟨729689, by rfl⟩ : syracuseStep 972919 = 1459379) B1459379
theorem B4675715 : Blo 972592 4675715 := bstep (se 1 (by rfl) ⟨3506786, by rfl⟩ : syracuseStep 4675715 = 7013573) B7013573
theorem B972939 : Blo 972592 972939 := bstep (se 1 (by rfl) ⟨729704, by rfl⟩ : syracuseStep 972939 = 1459409) B1459409
theorem B1235083 : Blo 972592 1235083 := bstep (se 1 (by rfl) ⟨926312, by rfl⟩ : syracuseStep 1235083 = 1852625) B1852625
theorem B972951 : Blo 972592 972951 := bstep (se 1 (by rfl) ⟨729713, by rfl⟩ : syracuseStep 972951 = 1459427) B1459427
theorem B1464473 : Blo 972592 1464473 := bstep (se 2 (by rfl) ⟨549177, by rfl⟩ : syracuseStep 1464473 = 1098355) B1098355
theorem B972971 : Blo 972592 972971 := bstep (se 1 (by rfl) ⟨729728, by rfl⟩ : syracuseStep 972971 = 1459457) B1459457
theorem B972983 : Blo 972592 972983 := bstep (se 1 (by rfl) ⟨729737, by rfl⟩ : syracuseStep 972983 = 1459475) B1459475
theorem B973003 : Blo 972592 973003 := bstep (se 1 (by rfl) ⟨729752, by rfl⟩ : syracuseStep 973003 = 1459505) B1459505
theorem B973015 : Blo 972592 973015 := bstep (se 1 (by rfl) ⟨729761, by rfl⟩ : syracuseStep 973015 = 1459523) B1459523
theorem B973035 : Blo 972592 973035 := bstep (se 1 (by rfl) ⟨729776, by rfl⟩ : syracuseStep 973035 = 1459553) B1459553
theorem B973047 : Blo 972592 973047 := bstep (se 1 (by rfl) ⟨729785, by rfl⟩ : syracuseStep 973047 = 1459571) B1459571
theorem B973067 : Blo 972592 973067 := bstep (se 1 (by rfl) ⟨729800, by rfl⟩ : syracuseStep 973067 = 1459601) B1459601
theorem B1464587 : Blo 972592 1464587 := bstep (se 1 (by rfl) ⟨1098440, by rfl⟩ : syracuseStep 1464587 = 2196881) B2196881
theorem B973079 : Blo 972592 973079 := bstep (se 1 (by rfl) ⟨729809, by rfl⟩ : syracuseStep 973079 = 1459619) B1459619
theorem B1464599 : Blo 972592 1464599 := bstep (se 1 (by rfl) ⟨1098449, by rfl⟩ : syracuseStep 1464599 = 2196899) B2196899
theorem B973099 : Blo 972592 973099 := bstep (se 1 (by rfl) ⟨729824, by rfl⟩ : syracuseStep 973099 = 1459649) B1459649
theorem B973111 : Blo 972592 973111 := bstep (se 1 (by rfl) ⟨729833, by rfl⟩ : syracuseStep 973111 = 1459667) B1459667
theorem B973131 : Blo 972592 973131 := bstep (se 1 (by rfl) ⟨729848, by rfl⟩ : syracuseStep 973131 = 1459697) B1459697
theorem B973143 : Blo 972592 973143 := bstep (se 1 (by rfl) ⟨729857, by rfl⟩ : syracuseStep 973143 = 1459715) B1459715
theorem B1464665 : Blo 972592 1464665 := bstep (se 2 (by rfl) ⟨549249, by rfl⟩ : syracuseStep 1464665 = 1098499) B1098499
theorem B973163 : Blo 972592 973163 := bstep (se 1 (by rfl) ⟨729872, by rfl⟩ : syracuseStep 973163 = 1459745) B1459745
theorem B973175 : Blo 972592 973175 := bstep (se 1 (by rfl) ⟨729881, by rfl⟩ : syracuseStep 973175 = 1459763) B1459763
theorem B973195 : Blo 972592 973195 := bstep (se 1 (by rfl) ⟨729896, by rfl⟩ : syracuseStep 973195 = 1459793) B1459793
theorem B973207 : Blo 972592 973207 := bstep (se 1 (by rfl) ⟨729905, by rfl⟩ : syracuseStep 973207 = 1459811) B1459811
theorem B1235351 : Blo 972592 1235351 := bstep (se 1 (by rfl) ⟨926513, by rfl⟩ : syracuseStep 1235351 = 1853027) B1853027
theorem B973227 : Blo 972592 973227 := bstep (se 1 (by rfl) ⟨729920, by rfl⟩ : syracuseStep 973227 = 1459841) B1459841
theorem B973239 : Blo 972592 973239 := bstep (se 1 (by rfl) ⟨729929, by rfl⟩ : syracuseStep 973239 = 1459859) B1459859
theorem B973259 : Blo 972592 973259 := bstep (se 1 (by rfl) ⟨729944, by rfl⟩ : syracuseStep 973259 = 1459889) B1459889
theorem B1464779 : Blo 972592 1464779 := bstep (se 1 (by rfl) ⟨1098584, by rfl⟩ : syracuseStep 1464779 = 2197169) B2197169
theorem B973271 : Blo 972592 973271 := bstep (se 1 (by rfl) ⟨729953, by rfl⟩ : syracuseStep 973271 = 1459907) B1459907
theorem B1464791 : Blo 972592 1464791 := bstep (se 1 (by rfl) ⟨1098593, by rfl⟩ : syracuseStep 1464791 = 2197187) B2197187
theorem B973291 : Blo 972592 973291 := bstep (se 1 (by rfl) ⟨729968, by rfl⟩ : syracuseStep 973291 = 1459937) B1459937
theorem B973303 : Blo 972592 973303 := bstep (se 1 (by rfl) ⟨729977, by rfl⟩ : syracuseStep 973303 = 1459955) B1459955
theorem B7494149 : Blo 972592 7494149 := bstep (se 4 (by rfl) ⟨702576, by rfl⟩ : syracuseStep 7494149 = 1405153) B1405153
theorem B973323 : Blo 972592 973323 := bstep (se 1 (by rfl) ⟨729992, by rfl⟩ : syracuseStep 973323 = 1459985) B1459985
theorem B973335 : Blo 972592 973335 := bstep (se 1 (by rfl) ⟨730001, by rfl⟩ : syracuseStep 973335 = 1460003) B1460003
theorem B1464857 : Blo 972592 1464857 := bstep (se 2 (by rfl) ⟨549321, by rfl⟩ : syracuseStep 1464857 = 1098643) B1098643
theorem B973355 : Blo 972592 973355 := bstep (se 1 (by rfl) ⟨730016, by rfl⟩ : syracuseStep 973355 = 1460033) B1460033
theorem B973367 : Blo 972592 973367 := bstep (se 1 (by rfl) ⟨730025, by rfl⟩ : syracuseStep 973367 = 1460051) B1460051
theorem B973387 : Blo 972592 973387 := bstep (se 1 (by rfl) ⟨730040, by rfl⟩ : syracuseStep 973387 = 1460081) B1460081
theorem B973399 : Blo 972592 973399 := bstep (se 1 (by rfl) ⟨730049, by rfl⟩ : syracuseStep 973399 = 1460099) B1460099
theorem B973419 : Blo 972592 973419 := bstep (se 1 (by rfl) ⟨730064, by rfl⟩ : syracuseStep 973419 = 1460129) B1460129
theorem B973431 : Blo 972592 973431 := bstep (se 1 (by rfl) ⟨730073, by rfl⟩ : syracuseStep 973431 = 1460147) B1460147
theorem B973451 : Blo 972592 973451 := bstep (se 1 (by rfl) ⟨730088, by rfl⟩ : syracuseStep 973451 = 1460177) B1460177
theorem B1563275 : Blo 972592 1563275 := bstep (se 1 (by rfl) ⟨1172456, by rfl⟩ : syracuseStep 1563275 = 2344913) B2344913
theorem B973463 : Blo 972592 973463 := bstep (se 1 (by rfl) ⟨730097, by rfl⟩ : syracuseStep 973463 = 1460195) B1460195
theorem B973483 : Blo 972592 973483 := bstep (se 1 (by rfl) ⟨730112, by rfl⟩ : syracuseStep 973483 = 1460225) B1460225
theorem B3693235 : Blo 972592 3693235 := bstep (se 1 (by rfl) ⟨2769926, by rfl⟩ : syracuseStep 3693235 = 5539853) B5539853
theorem B4741811 : Blo 972592 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B973495 : Blo 972592 973495 := bstep (se 1 (by rfl) ⟨730121, by rfl⟩ : syracuseStep 973495 = 1460243) B1460243
theorem B973515 : Blo 972592 973515 := bstep (se 1 (by rfl) ⟨730136, by rfl⟩ : syracuseStep 973515 = 1460273) B1460273
theorem B973527 : Blo 972592 973527 := bstep (se 1 (by rfl) ⟨730145, by rfl⟩ : syracuseStep 973527 = 1460291) B1460291
theorem B973547 : Blo 972592 973547 := bstep (se 1 (by rfl) ⟨730160, by rfl⟩ : syracuseStep 973547 = 1460321) B1460321
theorem B973559 : Blo 972592 973559 := bstep (se 1 (by rfl) ⟨730169, by rfl⟩ : syracuseStep 973559 = 1460339) B1460339
theorem B973579 : Blo 972592 973579 := bstep (se 1 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 973579 = 1460369) B1460369
theorem B973591 : Blo 972592 973591 := bstep (se 1 (by rfl) ⟨730193, by rfl⟩ : syracuseStep 973591 = 1460387) B1460387
theorem B973611 : Blo 972592 973611 := bstep (se 1 (by rfl) ⟨730208, by rfl⟩ : syracuseStep 973611 = 1460417) B1460417
theorem B973623 : Blo 972592 973623 := bstep (se 1 (by rfl) ⟨730217, by rfl⟩ : syracuseStep 973623 = 1460435) B1460435
theorem B973643 : Blo 972592 973643 := bstep (se 1 (by rfl) ⟨730232, by rfl⟩ : syracuseStep 973643 = 1460465) B1460465
theorem B973655 : Blo 972592 973655 := bstep (se 1 (by rfl) ⟨730241, by rfl⟩ : syracuseStep 973655 = 1460483) B1460483
theorem B973675 : Blo 972592 973675 := bstep (se 1 (by rfl) ⟨730256, by rfl⟩ : syracuseStep 973675 = 1460513) B1460513
theorem B973687 : Blo 972592 973687 := bstep (se 1 (by rfl) ⟨730265, by rfl⟩ : syracuseStep 973687 = 1460531) B1460531
theorem B973707 : Blo 972592 973707 := bstep (se 1 (by rfl) ⟨730280, by rfl⟩ : syracuseStep 973707 = 1460561) B1460561
theorem B973719 : Blo 972592 973719 := bstep (se 1 (by rfl) ⟨730289, by rfl⟩ : syracuseStep 973719 = 1460579) B1460579
theorem B973739 : Blo 972592 973739 := bstep (se 1 (by rfl) ⟨730304, by rfl⟩ : syracuseStep 973739 = 1460609) B1460609
theorem B973751 : Blo 972592 973751 := bstep (se 1 (by rfl) ⟨730313, by rfl⟩ : syracuseStep 973751 = 1460627) B1460627
theorem B973771 : Blo 972592 973771 := bstep (se 1 (by rfl) ⟨730328, by rfl⟩ : syracuseStep 973771 = 1460657) B1460657
theorem B973783 : Blo 972592 973783 := bstep (se 1 (by rfl) ⟨730337, by rfl⟩ : syracuseStep 973783 = 1460675) B1460675
theorem B973803 : Blo 972592 973803 := bstep (se 1 (by rfl) ⟨730352, by rfl⟩ : syracuseStep 973803 = 1460705) B1460705
theorem B973815 : Blo 972592 973815 := bstep (se 1 (by rfl) ⟨730361, by rfl⟩ : syracuseStep 973815 = 1460723) B1460723
theorem B973835 : Blo 972592 973835 := bstep (se 1 (by rfl) ⟨730376, by rfl⟩ : syracuseStep 973835 = 1460753) B1460753
theorem B973847 : Blo 972592 973847 := bstep (se 1 (by rfl) ⟨730385, by rfl⟩ : syracuseStep 973847 = 1460771) B1460771
theorem B3333143 : Blo 972592 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B1563671 : Blo 972592 1563671 := bstep (se 1 (by rfl) ⟨1172753, by rfl⟩ : syracuseStep 1563671 = 2345507) B2345507
theorem B973867 : Blo 972592 973867 := bstep (se 1 (by rfl) ⟨730400, by rfl⟩ : syracuseStep 973867 = 1460801) B1460801
theorem B973879 : Blo 972592 973879 := bstep (se 1 (by rfl) ⟨730409, by rfl⟩ : syracuseStep 973879 = 1460819) B1460819
theorem B5135425 : Blo 972592 5135425 := bstep (se 2 (by rfl) ⟨1925784, by rfl⟩ : syracuseStep 5135425 = 3851569) B3851569
theorem B973899 : Blo 972592 973899 := bstep (se 1 (by rfl) ⟨730424, by rfl⟩ : syracuseStep 973899 = 1460849) B1460849
theorem B973911 : Blo 972592 973911 := bstep (se 1 (by rfl) ⟨730433, by rfl⟩ : syracuseStep 973911 = 1460867) B1460867
theorem B973931 : Blo 972592 973931 := bstep (se 1 (by rfl) ⟨730448, by rfl⟩ : syracuseStep 973931 = 1460897) B1460897
theorem B973943 : Blo 972592 973943 := bstep (se 1 (by rfl) ⟨730457, by rfl⟩ : syracuseStep 973943 = 1460915) B1460915
theorem B973963 : Blo 972592 973963 := bstep (se 1 (by rfl) ⟨730472, by rfl⟩ : syracuseStep 973963 = 1460945) B1460945
theorem B973975 : Blo 972592 973975 := bstep (se 1 (by rfl) ⟨730481, by rfl⟩ : syracuseStep 973975 = 1460963) B1460963
theorem B973995 : Blo 972592 973995 := bstep (se 1 (by rfl) ⟨730496, by rfl⟩ : syracuseStep 973995 = 1460993) B1460993
theorem B974007 : Blo 972592 974007 := bstep (se 1 (by rfl) ⟨730505, by rfl⟩ : syracuseStep 974007 = 1461011) B1461011
theorem B974027 : Blo 972592 974027 := bstep (se 1 (by rfl) ⟨730520, by rfl⟩ : syracuseStep 974027 = 1461041) B1461041
theorem B974039 : Blo 972592 974039 := bstep (se 1 (by rfl) ⟨730529, by rfl⟩ : syracuseStep 974039 = 1461059) B1461059
theorem B974059 : Blo 972592 974059 := bstep (se 1 (by rfl) ⟨730544, by rfl⟩ : syracuseStep 974059 = 1461089) B1461089
theorem B974071 : Blo 972592 974071 := bstep (se 1 (by rfl) ⟨730553, by rfl⟩ : syracuseStep 974071 = 1461107) B1461107
theorem B974091 : Blo 972592 974091 := bstep (se 1 (by rfl) ⟨730568, by rfl⟩ : syracuseStep 974091 = 1461137) B1461137
theorem B974103 : Blo 972592 974103 := bstep (se 1 (by rfl) ⟨730577, by rfl⟩ : syracuseStep 974103 = 1461155) B1461155
theorem B974123 : Blo 972592 974123 := bstep (se 1 (by rfl) ⟨730592, by rfl⟩ : syracuseStep 974123 = 1461185) B1461185
theorem B974135 : Blo 972592 974135 := bstep (se 1 (by rfl) ⟨730601, by rfl⟩ : syracuseStep 974135 = 1461203) B1461203
theorem B974155 : Blo 972592 974155 := bstep (se 1 (by rfl) ⟨730616, by rfl⟩ : syracuseStep 974155 = 1461233) B1461233
theorem B974167 : Blo 972592 974167 := bstep (se 1 (by rfl) ⟨730625, by rfl⟩ : syracuseStep 974167 = 1461251) B1461251
theorem B974187 : Blo 972592 974187 := bstep (se 1 (by rfl) ⟨730640, by rfl⟩ : syracuseStep 974187 = 1461281) B1461281
theorem B974199 : Blo 972592 974199 := bstep (se 1 (by rfl) ⟨730649, by rfl⟩ : syracuseStep 974199 = 1461299) B1461299
theorem B974219 : Blo 972592 974219 := bstep (se 1 (by rfl) ⟨730664, by rfl⟩ : syracuseStep 974219 = 1461329) B1461329
theorem B974231 : Blo 972592 974231 := bstep (se 1 (by rfl) ⟨730673, by rfl⟩ : syracuseStep 974231 = 1461347) B1461347
theorem B974251 : Blo 972592 974251 := bstep (se 1 (by rfl) ⟨730688, by rfl⟩ : syracuseStep 974251 = 1461377) B1461377
theorem B974263 : Blo 972592 974263 := bstep (se 1 (by rfl) ⟨730697, by rfl⟩ : syracuseStep 974263 = 1461395) B1461395
theorem B974283 : Blo 972592 974283 := bstep (se 1 (by rfl) ⟨730712, by rfl⟩ : syracuseStep 974283 = 1461425) B1461425
theorem B974295 : Blo 972592 974295 := bstep (se 1 (by rfl) ⟨730721, by rfl⟩ : syracuseStep 974295 = 1461443) B1461443
theorem B974315 : Blo 972592 974315 := bstep (se 1 (by rfl) ⟨730736, by rfl⟩ : syracuseStep 974315 = 1461473) B1461473
theorem B974327 : Blo 972592 974327 := bstep (se 1 (by rfl) ⟨730745, by rfl⟩ : syracuseStep 974327 = 1461491) B1461491
theorem B974347 : Blo 972592 974347 := bstep (se 1 (by rfl) ⟨730760, by rfl⟩ : syracuseStep 974347 = 1461521) B1461521
theorem B974359 : Blo 972592 974359 := bstep (se 1 (by rfl) ⟨730769, by rfl⟩ : syracuseStep 974359 = 1461539) B1461539
theorem B1039915 : Blo 972592 1039915 := bstep (se 1 (by rfl) ⟨779936, by rfl⟩ : syracuseStep 1039915 = 1559873) B1559873
theorem B974379 : Blo 972592 974379 := bstep (se 1 (by rfl) ⟨730784, by rfl⟩ : syracuseStep 974379 = 1461569) B1461569
theorem B974391 : Blo 972592 974391 := bstep (se 1 (by rfl) ⟨730793, by rfl⟩ : syracuseStep 974391 = 1461587) B1461587
theorem B974411 : Blo 972592 974411 := bstep (se 1 (by rfl) ⟨730808, by rfl⟩ : syracuseStep 974411 = 1461617) B1461617
theorem B974423 : Blo 972592 974423 := bstep (se 1 (by rfl) ⟨730817, by rfl⟩ : syracuseStep 974423 = 1461635) B1461635
theorem B974443 : Blo 972592 974443 := bstep (se 1 (by rfl) ⟨730832, by rfl⟩ : syracuseStep 974443 = 1461665) B1461665
theorem B974455 : Blo 972592 974455 := bstep (se 1 (by rfl) ⟨730841, by rfl⟩ : syracuseStep 974455 = 1461683) B1461683
theorem B974475 : Blo 972592 974475 := bstep (se 1 (by rfl) ⟨730856, by rfl⟩ : syracuseStep 974475 = 1461713) B1461713
theorem B974487 : Blo 972592 974487 := bstep (se 1 (by rfl) ⟨730865, by rfl⟩ : syracuseStep 974487 = 1461731) B1461731
theorem B974507 : Blo 972592 974507 := bstep (se 1 (by rfl) ⟨730880, by rfl⟩ : syracuseStep 974507 = 1461761) B1461761
theorem B974519 : Blo 972592 974519 := bstep (se 1 (by rfl) ⟨730889, by rfl⟩ : syracuseStep 974519 = 1461779) B1461779
theorem B974539 : Blo 972592 974539 := bstep (se 1 (by rfl) ⟨730904, by rfl⟩ : syracuseStep 974539 = 1461809) B1461809
theorem B974551 : Blo 972592 974551 := bstep (se 1 (by rfl) ⟨730913, by rfl⟩ : syracuseStep 974551 = 1461827) B1461827
theorem B974571 : Blo 972592 974571 := bstep (se 1 (by rfl) ⟨730928, by rfl⟩ : syracuseStep 974571 = 1461857) B1461857
theorem B974583 : Blo 972592 974583 := bstep (se 1 (by rfl) ⟨730937, by rfl⟩ : syracuseStep 974583 = 1461875) B1461875
theorem B974603 : Blo 972592 974603 := bstep (se 1 (by rfl) ⟨730952, by rfl⟩ : syracuseStep 974603 = 1461905) B1461905
theorem B974615 : Blo 972592 974615 := bstep (se 1 (by rfl) ⟨730961, by rfl⟩ : syracuseStep 974615 = 1461923) B1461923
theorem B974635 : Blo 972592 974635 := bstep (se 1 (by rfl) ⟨730976, by rfl⟩ : syracuseStep 974635 = 1461953) B1461953
theorem B974647 : Blo 972592 974647 := bstep (se 1 (by rfl) ⟨730985, by rfl⟩ : syracuseStep 974647 = 1461971) B1461971
theorem B974667 : Blo 972592 974667 := bstep (se 1 (by rfl) ⟨731000, by rfl⟩ : syracuseStep 974667 = 1462001) B1462001
theorem B974679 : Blo 972592 974679 := bstep (se 1 (by rfl) ⟨731009, by rfl⟩ : syracuseStep 974679 = 1462019) B1462019
theorem B974699 : Blo 972592 974699 := bstep (se 1 (by rfl) ⟨731024, by rfl⟩ : syracuseStep 974699 = 1462049) B1462049
theorem B974711 : Blo 972592 974711 := bstep (se 1 (by rfl) ⟨731033, by rfl⟩ : syracuseStep 974711 = 1462067) B1462067
theorem B974731 : Blo 972592 974731 := bstep (se 1 (by rfl) ⟨731048, by rfl⟩ : syracuseStep 974731 = 1462097) B1462097
theorem B3694481 : Blo 972592 3694481 := bstep (se 2 (by rfl) ⟨1385430, by rfl⟩ : syracuseStep 3694481 = 2770861) B2770861
theorem B974743 : Blo 972592 974743 := bstep (se 1 (by rfl) ⟨731057, by rfl⟩ : syracuseStep 974743 = 1462115) B1462115
theorem B974763 : Blo 972592 974763 := bstep (se 1 (by rfl) ⟨731072, by rfl⟩ : syracuseStep 974763 = 1462145) B1462145
theorem B974775 : Blo 972592 974775 := bstep (se 1 (by rfl) ⟨731081, by rfl⟩ : syracuseStep 974775 = 1462163) B1462163
theorem B974795 : Blo 972592 974795 := bstep (se 1 (by rfl) ⟨731096, by rfl⟩ : syracuseStep 974795 = 1462193) B1462193
theorem B974807 : Blo 972592 974807 := bstep (se 1 (by rfl) ⟨731105, by rfl⟩ : syracuseStep 974807 = 1462211) B1462211
theorem B974827 : Blo 972592 974827 := bstep (se 1 (by rfl) ⟨731120, by rfl⟩ : syracuseStep 974827 = 1462241) B1462241
theorem B974839 : Blo 972592 974839 := bstep (se 1 (by rfl) ⟨731129, by rfl⟩ : syracuseStep 974839 = 1462259) B1462259
theorem B974859 : Blo 972592 974859 := bstep (se 1 (by rfl) ⟨731144, by rfl⟩ : syracuseStep 974859 = 1462289) B1462289
theorem B974871 : Blo 972592 974871 := bstep (se 1 (by rfl) ⟨731153, by rfl⟩ : syracuseStep 974871 = 1462307) B1462307
theorem B974891 : Blo 972592 974891 := bstep (se 1 (by rfl) ⟨731168, by rfl⟩ : syracuseStep 974891 = 1462337) B1462337
theorem B974903 : Blo 972592 974903 := bstep (se 1 (by rfl) ⟨731177, by rfl⟩ : syracuseStep 974903 = 1462355) B1462355
theorem B5267531 : Blo 972592 5267531 := bstep (se 1 (by rfl) ⟨3950648, by rfl⟩ : syracuseStep 5267531 = 7901297) B7901297
theorem B974923 : Blo 972592 974923 := bstep (se 1 (by rfl) ⟨731192, by rfl⟩ : syracuseStep 974923 = 1462385) B1462385
theorem B974935 : Blo 972592 974935 := bstep (se 1 (by rfl) ⟨731201, by rfl⟩ : syracuseStep 974935 = 1462403) B1462403
theorem B974955 : Blo 972592 974955 := bstep (se 1 (by rfl) ⟨731216, by rfl⟩ : syracuseStep 974955 = 1462433) B1462433
theorem B974967 : Blo 972592 974967 := bstep (se 1 (by rfl) ⟨731225, by rfl⟩ : syracuseStep 974967 = 1462451) B1462451
theorem B974987 : Blo 972592 974987 := bstep (se 1 (by rfl) ⟨731240, by rfl⟩ : syracuseStep 974987 = 1462481) B1462481
theorem B974999 : Blo 972592 974999 := bstep (se 1 (by rfl) ⟨731249, by rfl⟩ : syracuseStep 974999 = 1462499) B1462499
theorem B975019 : Blo 972592 975019 := bstep (se 1 (by rfl) ⟨731264, by rfl⟩ : syracuseStep 975019 = 1462529) B1462529
theorem B975031 : Blo 972592 975031 := bstep (se 1 (by rfl) ⟨731273, by rfl⟩ : syracuseStep 975031 = 1462547) B1462547
theorem B975051 : Blo 972592 975051 := bstep (se 1 (by rfl) ⟨731288, by rfl⟩ : syracuseStep 975051 = 1462577) B1462577
theorem B975063 : Blo 972592 975063 := bstep (se 1 (by rfl) ⟨731297, by rfl⟩ : syracuseStep 975063 = 1462595) B1462595
theorem B975083 : Blo 972592 975083 := bstep (se 1 (by rfl) ⟨731312, by rfl⟩ : syracuseStep 975083 = 1462625) B1462625
theorem B975095 : Blo 972592 975095 := bstep (se 1 (by rfl) ⟨731321, by rfl⟩ : syracuseStep 975095 = 1462643) B1462643
theorem B975115 : Blo 972592 975115 := bstep (se 1 (by rfl) ⟨731336, by rfl⟩ : syracuseStep 975115 = 1462673) B1462673
theorem B975127 : Blo 972592 975127 := bstep (se 1 (by rfl) ⟨731345, by rfl⟩ : syracuseStep 975127 = 1462691) B1462691
theorem B975147 : Blo 972592 975147 := bstep (se 1 (by rfl) ⟨731360, by rfl⟩ : syracuseStep 975147 = 1462721) B1462721
theorem B975159 : Blo 972592 975159 := bstep (se 1 (by rfl) ⟨731369, by rfl⟩ : syracuseStep 975159 = 1462739) B1462739
theorem B975179 : Blo 972592 975179 := bstep (se 1 (by rfl) ⟨731384, by rfl⟩ : syracuseStep 975179 = 1462769) B1462769
theorem B975191 : Blo 972592 975191 := bstep (se 1 (by rfl) ⟨731393, by rfl⟩ : syracuseStep 975191 = 1462787) B1462787
theorem B975211 : Blo 972592 975211 := bstep (se 1 (by rfl) ⟨731408, by rfl⟩ : syracuseStep 975211 = 1462817) B1462817
theorem B975223 : Blo 972592 975223 := bstep (se 1 (by rfl) ⟨731417, by rfl⟩ : syracuseStep 975223 = 1462835) B1462835
theorem B975243 : Blo 972592 975243 := bstep (se 1 (by rfl) ⟨731432, by rfl⟩ : syracuseStep 975243 = 1462865) B1462865
theorem B975255 : Blo 972592 975255 := bstep (se 1 (by rfl) ⟨731441, by rfl⟩ : syracuseStep 975255 = 1462883) B1462883
theorem B975275 : Blo 972592 975275 := bstep (se 1 (by rfl) ⟨731456, by rfl⟩ : syracuseStep 975275 = 1462913) B1462913
theorem B7889329 : Blo 972592 7889329 := bstep (se 2 (by rfl) ⟨2958498, by rfl⟩ : syracuseStep 7889329 = 5916997) B5916997
theorem B975287 : Blo 972592 975287 := bstep (se 1 (by rfl) ⟨731465, by rfl⟩ : syracuseStep 975287 = 1462931) B1462931
theorem B975307 : Blo 972592 975307 := bstep (se 1 (by rfl) ⟨731480, by rfl⟩ : syracuseStep 975307 = 1462961) B1462961
theorem B975319 : Blo 972592 975319 := bstep (se 1 (by rfl) ⟨731489, by rfl⟩ : syracuseStep 975319 = 1462979) B1462979
theorem B975339 : Blo 972592 975339 := bstep (se 1 (by rfl) ⟨731504, by rfl⟩ : syracuseStep 975339 = 1463009) B1463009
theorem B975351 : Blo 972592 975351 := bstep (se 1 (by rfl) ⟨731513, by rfl⟩ : syracuseStep 975351 = 1463027) B1463027
theorem B975371 : Blo 972592 975371 := bstep (se 1 (by rfl) ⟨731528, by rfl⟩ : syracuseStep 975371 = 1463057) B1463057
theorem B975383 : Blo 972592 975383 := bstep (se 1 (by rfl) ⟨731537, by rfl⟩ : syracuseStep 975383 = 1463075) B1463075
theorem B975403 : Blo 972592 975403 := bstep (se 1 (by rfl) ⟨731552, by rfl⟩ : syracuseStep 975403 = 1463105) B1463105
theorem B975415 : Blo 972592 975415 := bstep (se 1 (by rfl) ⟨731561, by rfl⟩ : syracuseStep 975415 = 1463123) B1463123
theorem B3695179 : Blo 972592 3695179 := bstep (se 1 (by rfl) ⟨2771384, by rfl⟩ : syracuseStep 3695179 = 5542769) B5542769
theorem B975435 : Blo 972592 975435 := bstep (se 1 (by rfl) ⟨731576, by rfl⟩ : syracuseStep 975435 = 1463153) B1463153
theorem B975447 : Blo 972592 975447 := bstep (se 1 (by rfl) ⟨731585, by rfl⟩ : syracuseStep 975447 = 1463171) B1463171
theorem B10543709 : Blo 972592 10543709 := bstep (se 3 (by rfl) ⟨1976945, by rfl⟩ : syracuseStep 10543709 = 3953891) B3953891
theorem B975467 : Blo 972592 975467 := bstep (se 1 (by rfl) ⟨731600, by rfl⟩ : syracuseStep 975467 = 1463201) B1463201
theorem B975479 : Blo 972592 975479 := bstep (se 1 (by rfl) ⟨731609, by rfl⟩ : syracuseStep 975479 = 1463219) B1463219
theorem B975499 : Blo 972592 975499 := bstep (se 1 (by rfl) ⟨731624, by rfl⟩ : syracuseStep 975499 = 1463249) B1463249
theorem B975511 : Blo 972592 975511 := bstep (se 1 (by rfl) ⟨731633, by rfl⟩ : syracuseStep 975511 = 1463267) B1463267
theorem B975531 : Blo 972592 975531 := bstep (se 1 (by rfl) ⟨731648, by rfl⟩ : syracuseStep 975531 = 1463297) B1463297
theorem B975543 : Blo 972592 975543 := bstep (se 1 (by rfl) ⟨731657, by rfl⟩ : syracuseStep 975543 = 1463315) B1463315
theorem B975563 : Blo 972592 975563 := bstep (se 1 (by rfl) ⟨731672, by rfl⟩ : syracuseStep 975563 = 1463345) B1463345
theorem B975575 : Blo 972592 975575 := bstep (se 1 (by rfl) ⟨731681, by rfl⟩ : syracuseStep 975575 = 1463363) B1463363
theorem B975595 : Blo 972592 975595 := bstep (se 1 (by rfl) ⟨731696, by rfl⟩ : syracuseStep 975595 = 1463393) B1463393
theorem B975607 : Blo 972592 975607 := bstep (se 1 (by rfl) ⟨731705, by rfl⟩ : syracuseStep 975607 = 1463411) B1463411
theorem B975627 : Blo 972592 975627 := bstep (se 1 (by rfl) ⟨731720, by rfl⟩ : syracuseStep 975627 = 1463441) B1463441
theorem B975639 : Blo 972592 975639 := bstep (se 1 (by rfl) ⟨731729, by rfl⟩ : syracuseStep 975639 = 1463459) B1463459
theorem B975659 : Blo 972592 975659 := bstep (se 1 (by rfl) ⟨731744, by rfl⟩ : syracuseStep 975659 = 1463489) B1463489
theorem B975671 : Blo 972592 975671 := bstep (se 1 (by rfl) ⟨731753, by rfl⟩ : syracuseStep 975671 = 1463507) B1463507
theorem B975691 : Blo 972592 975691 := bstep (se 1 (by rfl) ⟨731768, by rfl⟩ : syracuseStep 975691 = 1463537) B1463537
theorem B975703 : Blo 972592 975703 := bstep (se 1 (by rfl) ⟨731777, by rfl⟩ : syracuseStep 975703 = 1463555) B1463555
theorem B3695453 : Blo 972592 3695453 := bstep (se 3 (by rfl) ⟨692897, by rfl⟩ : syracuseStep 3695453 = 1385795) B1385795
theorem B975723 : Blo 972592 975723 := bstep (se 1 (by rfl) ⟨731792, by rfl⟩ : syracuseStep 975723 = 1463585) B1463585
theorem B975735 : Blo 972592 975735 := bstep (se 1 (by rfl) ⟨731801, by rfl⟩ : syracuseStep 975735 = 1463603) B1463603
theorem B4940675 : Blo 972592 4940675 := bstep (se 1 (by rfl) ⟨3705506, by rfl⟩ : syracuseStep 4940675 = 7411013) B7411013
theorem B975755 : Blo 972592 975755 := bstep (se 1 (by rfl) ⟨731816, by rfl⟩ : syracuseStep 975755 = 1463633) B1463633
theorem B975767 : Blo 972592 975767 := bstep (se 1 (by rfl) ⟨731825, by rfl⟩ : syracuseStep 975767 = 1463651) B1463651
theorem B975787 : Blo 972592 975787 := bstep (se 1 (by rfl) ⟨731840, by rfl⟩ : syracuseStep 975787 = 1463681) B1463681
theorem B975799 : Blo 972592 975799 := bstep (se 1 (by rfl) ⟨731849, by rfl⟩ : syracuseStep 975799 = 1463699) B1463699
theorem B975819 : Blo 972592 975819 := bstep (se 1 (by rfl) ⟨731864, by rfl⟩ : syracuseStep 975819 = 1463729) B1463729
theorem B975831 : Blo 972592 975831 := bstep (se 1 (by rfl) ⟨731873, by rfl⟩ : syracuseStep 975831 = 1463747) B1463747
theorem B975851 : Blo 972592 975851 := bstep (se 1 (by rfl) ⟨731888, by rfl⟩ : syracuseStep 975851 = 1463777) B1463777
theorem B975863 : Blo 972592 975863 := bstep (se 1 (by rfl) ⟨731897, by rfl⟩ : syracuseStep 975863 = 1463795) B1463795
theorem B975883 : Blo 972592 975883 := bstep (se 1 (by rfl) ⟨731912, by rfl⟩ : syracuseStep 975883 = 1463825) B1463825
theorem B975895 : Blo 972592 975895 := bstep (se 1 (by rfl) ⟨731921, by rfl⟩ : syracuseStep 975895 = 1463843) B1463843
theorem B975915 : Blo 972592 975915 := bstep (se 1 (by rfl) ⟨731936, by rfl⟩ : syracuseStep 975915 = 1463873) B1463873
theorem B975927 : Blo 972592 975927 := bstep (se 1 (by rfl) ⟨731945, by rfl⟩ : syracuseStep 975927 = 1463891) B1463891
theorem B975947 : Blo 972592 975947 := bstep (se 1 (by rfl) ⟨731960, by rfl⟩ : syracuseStep 975947 = 1463921) B1463921
theorem B975959 : Blo 972592 975959 := bstep (se 1 (by rfl) ⟨731969, by rfl⟩ : syracuseStep 975959 = 1463939) B1463939
theorem B975979 : Blo 972592 975979 := bstep (se 1 (by rfl) ⟨731984, by rfl⟩ : syracuseStep 975979 = 1463969) B1463969
theorem B2188403 : Blo 972592 2188403 := bstep (se 1 (by rfl) ⟨1641302, by rfl⟩ : syracuseStep 2188403 = 3282605) B3282605
theorem B975991 : Blo 972592 975991 := bstep (se 1 (by rfl) ⟨731993, by rfl⟩ : syracuseStep 975991 = 1463987) B1463987
theorem B976011 : Blo 972592 976011 := bstep (se 1 (by rfl) ⟨732008, by rfl⟩ : syracuseStep 976011 = 1464017) B1464017
theorem B2188439 : Blo 972592 2188439 := bstep (se 1 (by rfl) ⟨1641329, by rfl⟩ : syracuseStep 2188439 = 3282659) B3282659
theorem B976023 : Blo 972592 976023 := bstep (se 1 (by rfl) ⟨732017, by rfl⟩ : syracuseStep 976023 = 1464035) B1464035
theorem B976043 : Blo 972592 976043 := bstep (se 1 (by rfl) ⟨732032, by rfl⟩ : syracuseStep 976043 = 1464065) B1464065
theorem B976055 : Blo 972592 976055 := bstep (se 1 (by rfl) ⟨732041, by rfl⟩ : syracuseStep 976055 = 1464083) B1464083
theorem B976075 : Blo 972592 976075 := bstep (se 1 (by rfl) ⟨732056, by rfl⟩ : syracuseStep 976075 = 1464113) B1464113
theorem B976087 : Blo 972592 976087 := bstep (se 1 (by rfl) ⟨732065, by rfl⟩ : syracuseStep 976087 = 1464131) B1464131
theorem B976107 : Blo 972592 976107 := bstep (se 1 (by rfl) ⟨732080, by rfl⟩ : syracuseStep 976107 = 1464161) B1464161
theorem B976119 : Blo 972592 976119 := bstep (se 1 (by rfl) ⟨732089, by rfl⟩ : syracuseStep 976119 = 1464179) B1464179
theorem B32531717 : Blo 972592 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B976139 : Blo 972592 976139 := bstep (se 1 (by rfl) ⟨732104, by rfl⟩ : syracuseStep 976139 = 1464209) B1464209
theorem B976151 : Blo 972592 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B976171 : Blo 972592 976171 := bstep (se 1 (by rfl) ⟨732128, by rfl⟩ : syracuseStep 976171 = 1464257) B1464257
theorem B976183 : Blo 972592 976183 := bstep (se 1 (by rfl) ⟨732137, by rfl⟩ : syracuseStep 976183 = 1464275) B1464275
theorem B2188619 : Blo 972592 2188619 := bstep (se 1 (by rfl) ⟨1641464, by rfl⟩ : syracuseStep 2188619 = 3282929) B3282929
theorem B976203 : Blo 972592 976203 := bstep (se 1 (by rfl) ⟨732152, by rfl⟩ : syracuseStep 976203 = 1464305) B1464305
theorem B976215 : Blo 972592 976215 := bstep (se 1 (by rfl) ⟨732161, by rfl⟩ : syracuseStep 976215 = 1464323) B1464323
theorem B5629277 : Blo 972592 5629277 := bstep (se 3 (by rfl) ⟨1055489, by rfl⟩ : syracuseStep 5629277 = 2110979) B2110979
theorem B976235 : Blo 972592 976235 := bstep (se 1 (by rfl) ⟨732176, by rfl⟩ : syracuseStep 976235 = 1464353) B1464353
theorem B976247 : Blo 972592 976247 := bstep (se 1 (by rfl) ⟨732185, by rfl⟩ : syracuseStep 976247 = 1464371) B1464371
theorem B2188673 : Blo 972592 2188673 := bstep (se 2 (by rfl) ⟨820752, by rfl⟩ : syracuseStep 2188673 = 1641505) B1641505
theorem B976267 : Blo 972592 976267 := bstep (se 1 (by rfl) ⟨732200, by rfl⟩ : syracuseStep 976267 = 1464401) B1464401
theorem B976279 : Blo 972592 976279 := bstep (se 1 (by rfl) ⟨732209, by rfl⟩ : syracuseStep 976279 = 1464419) B1464419
theorem B976299 : Blo 972592 976299 := bstep (se 1 (by rfl) ⟨732224, by rfl⟩ : syracuseStep 976299 = 1464449) B1464449
theorem B976311 : Blo 972592 976311 := bstep (se 1 (by rfl) ⟨732233, by rfl⟩ : syracuseStep 976311 = 1464467) B1464467
theorem B976331 : Blo 972592 976331 := bstep (se 1 (by rfl) ⟨732248, by rfl⟩ : syracuseStep 976331 = 1464497) B1464497
theorem B976343 : Blo 972592 976343 := bstep (se 1 (by rfl) ⟨732257, by rfl⟩ : syracuseStep 976343 = 1464515) B1464515
theorem B976363 : Blo 972592 976363 := bstep (se 1 (by rfl) ⟨732272, by rfl⟩ : syracuseStep 976363 = 1464545) B1464545
theorem B976375 : Blo 972592 976375 := bstep (se 1 (by rfl) ⟨732281, by rfl⟩ : syracuseStep 976375 = 1464563) B1464563
theorem B1041931 : Blo 972592 1041931 := bstep (se 1 (by rfl) ⟨781448, by rfl⟩ : syracuseStep 1041931 = 1562897) B1562897
theorem B976395 : Blo 972592 976395 := bstep (se 1 (by rfl) ⟨732296, by rfl⟩ : syracuseStep 976395 = 1464593) B1464593
theorem B3696151 : Blo 972592 3696151 := bstep (se 1 (by rfl) ⟨2772113, by rfl⟩ : syracuseStep 3696151 = 5544227) B5544227
theorem B976407 : Blo 972592 976407 := bstep (se 1 (by rfl) ⟨732305, by rfl⟩ : syracuseStep 976407 = 1464611) B1464611
theorem B976427 : Blo 972592 976427 := bstep (se 1 (by rfl) ⟨732320, by rfl⟩ : syracuseStep 976427 = 1464641) B1464641
theorem B976439 : Blo 972592 976439 := bstep (se 1 (by rfl) ⟨732329, by rfl⟩ : syracuseStep 976439 = 1464659) B1464659
theorem B976459 : Blo 972592 976459 := bstep (se 1 (by rfl) ⟨732344, by rfl⟩ : syracuseStep 976459 = 1464689) B1464689
theorem B976471 : Blo 972592 976471 := bstep (se 1 (by rfl) ⟨732353, by rfl⟩ : syracuseStep 976471 = 1464707) B1464707
theorem B2188889 : Blo 972592 2188889 := bstep (se 2 (by rfl) ⟨820833, by rfl⟩ : syracuseStep 2188889 = 1641667) B1641667
theorem B976491 : Blo 972592 976491 := bstep (se 1 (by rfl) ⟨732368, by rfl⟩ : syracuseStep 976491 = 1464737) B1464737
theorem B976503 : Blo 972592 976503 := bstep (se 1 (by rfl) ⟨732377, by rfl⟩ : syracuseStep 976503 = 1464755) B1464755
theorem B976523 : Blo 972592 976523 := bstep (se 1 (by rfl) ⟨732392, by rfl⟩ : syracuseStep 976523 = 1464785) B1464785
theorem B976535 : Blo 972592 976535 := bstep (se 1 (by rfl) ⟨732401, by rfl⟩ : syracuseStep 976535 = 1464803) B1464803
theorem B976555 : Blo 972592 976555 := bstep (se 1 (by rfl) ⟨732416, by rfl⟩ : syracuseStep 976555 = 1464833) B1464833
theorem B2188979 : Blo 972592 2188979 := bstep (se 1 (by rfl) ⟨1641734, by rfl⟩ : syracuseStep 2188979 = 3283469) B3283469
theorem B976567 : Blo 972592 976567 := bstep (se 1 (by rfl) ⟨732425, by rfl⟩ : syracuseStep 976567 = 1464851) B1464851
theorem B976587 : Blo 972592 976587 := bstep (se 1 (by rfl) ⟨732440, by rfl⟩ : syracuseStep 976587 = 1464881) B1464881
theorem B2189015 : Blo 972592 2189015 := bstep (se 1 (by rfl) ⟨1641761, by rfl⟩ : syracuseStep 2189015 = 3283523) B3283523
theorem B4450099 : Blo 972592 4450099 := bstep (se 1 (by rfl) ⟨3337574, by rfl⟩ : syracuseStep 4450099 = 6675149) B6675149
theorem B2189195 : Blo 972592 2189195 := bstep (se 1 (by rfl) ⟨1641896, by rfl⟩ : syracuseStep 2189195 = 3283793) B3283793
theorem B4220851 : Blo 972592 4220851 := bstep (se 1 (by rfl) ⟨3165638, by rfl⟩ : syracuseStep 4220851 = 6331277) B6331277
theorem B2189249 : Blo 972592 2189249 := bstep (se 2 (by rfl) ⟨820968, by rfl⟩ : syracuseStep 2189249 = 1641937) B1641937
theorem B4155437 : Blo 972592 4155437 := bstep (se 3 (by rfl) ⟨779144, by rfl⟩ : syracuseStep 4155437 = 1558289) B1558289
theorem B2779211 : Blo 972592 2779211 := bstep (se 1 (by rfl) ⟨2084408, by rfl⟩ : syracuseStep 2779211 = 4168817) B4168817
theorem B2189465 : Blo 972592 2189465 := bstep (se 2 (by rfl) ⟨821049, by rfl⟩ : syracuseStep 2189465 = 1642099) B1642099
theorem B2189555 : Blo 972592 2189555 := bstep (se 1 (by rfl) ⟨1642166, by rfl⟩ : syracuseStep 2189555 = 3284333) B3284333
theorem B2189591 : Blo 972592 2189591 := bstep (se 1 (by rfl) ⟨1642193, by rfl⟩ : syracuseStep 2189591 = 3284387) B3284387
theorem B3696941 : Blo 972592 3696941 := bstep (se 3 (by rfl) ⟨693176, by rfl⟩ : syracuseStep 3696941 = 1386353) B1386353
theorem B4155779 : Blo 972592 4155779 := bstep (se 1 (by rfl) ⟨3116834, by rfl⟩ : syracuseStep 4155779 = 6233669) B6233669
theorem B3664273 : Blo 972592 3664273 := bstep (se 2 (by rfl) ⟨1374102, by rfl⟩ : syracuseStep 3664273 = 2748205) B2748205
theorem B2189771 : Blo 972592 2189771 := bstep (se 1 (by rfl) ⟨1642328, by rfl⟩ : syracuseStep 2189771 = 3284657) B3284657
theorem B2779609 : Blo 972592 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B2189825 : Blo 972592 2189825 := bstep (se 2 (by rfl) ⟨821184, by rfl⟩ : syracuseStep 2189825 = 1642369) B1642369
theorem B2190041 : Blo 972592 2190041 := bstep (se 2 (by rfl) ⟨821265, by rfl⟩ : syracuseStep 2190041 = 1642531) B1642531
theorem B2190131 : Blo 972592 2190131 := bstep (se 1 (by rfl) ⟨1642598, by rfl⟩ : syracuseStep 2190131 = 3285197) B3285197
theorem B2190167 : Blo 972592 2190167 := bstep (se 1 (by rfl) ⟨1642625, by rfl⟩ : syracuseStep 2190167 = 3285251) B3285251
theorem B4746115 : Blo 972592 4746115 := bstep (se 1 (by rfl) ⟨3559586, by rfl⟩ : syracuseStep 4746115 = 7119173) B7119173
theorem B2190347 : Blo 972592 2190347 := bstep (se 1 (by rfl) ⟨1642760, by rfl⟩ : syracuseStep 2190347 = 3285521) B3285521
theorem B2190401 : Blo 972592 2190401 := bstep (se 2 (by rfl) ⟨821400, by rfl⟩ : syracuseStep 2190401 = 1642801) B1642801
theorem B15199301 : Blo 972592 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B10546307 : Blo 972592 10546307 := bstep (se 1 (by rfl) ⟨7909730, by rfl⟩ : syracuseStep 10546307 = 15819461) B15819461
theorem B2190617 : Blo 972592 2190617 := bstep (se 2 (by rfl) ⟨821481, by rfl⟩ : syracuseStep 2190617 = 1642963) B1642963
theorem B2190707 : Blo 972592 2190707 := bstep (se 1 (by rfl) ⟨1643030, by rfl⟩ : syracuseStep 2190707 = 3286061) B3286061
theorem B2190743 : Blo 972592 2190743 := bstep (se 1 (by rfl) ⟨1643057, by rfl⟩ : syracuseStep 2190743 = 3286115) B3286115
theorem B2190923 : Blo 972592 2190923 := bstep (se 1 (by rfl) ⟨1643192, by rfl⟩ : syracuseStep 2190923 = 3286385) B3286385
theorem B2190977 : Blo 972592 2190977 := bstep (se 2 (by rfl) ⟨821616, by rfl⟩ : syracuseStep 2190977 = 1643233) B1643233
theorem B13332119 : Blo 972592 13332119 := bstep (se 1 (by rfl) ⟨9999089, by rfl⟩ : syracuseStep 13332119 = 19998179) B19998179
theorem B2780851 : Blo 972592 2780851 := bstep (se 1 (by rfl) ⟨2085638, by rfl⟩ : syracuseStep 2780851 = 4171277) B4171277
theorem B3698369 : Blo 972592 3698369 := bstep (se 2 (by rfl) ⟨1386888, by rfl⟩ : syracuseStep 3698369 = 2773777) B2773777
theorem B2191193 : Blo 972592 2191193 := bstep (se 2 (by rfl) ⟨821697, by rfl⟩ : syracuseStep 2191193 = 1643395) B1643395
theorem B2191283 : Blo 972592 2191283 := bstep (se 1 (by rfl) ⟨1643462, by rfl⟩ : syracuseStep 2191283 = 3286925) B3286925
theorem B2191319 : Blo 972592 2191319 := bstep (se 1 (by rfl) ⟨1643489, by rfl⟩ : syracuseStep 2191319 = 3286979) B3286979
theorem B4222979 : Blo 972592 4222979 := bstep (se 1 (by rfl) ⟨3167234, by rfl⟩ : syracuseStep 4222979 = 6334469) B6334469
theorem B2191499 : Blo 972592 2191499 := bstep (se 1 (by rfl) ⟨1643624, by rfl⟩ : syracuseStep 2191499 = 3287249) B3287249
theorem B2191553 : Blo 972592 2191553 := bstep (se 2 (by rfl) ⟨821832, by rfl⟩ : syracuseStep 2191553 = 1643665) B1643665
theorem B6254941 : Blo 972592 6254941 := bstep (se 3 (by rfl) ⟨1172801, by rfl⟩ : syracuseStep 6254941 = 2345603) B2345603
theorem B2191769 : Blo 972592 2191769 := bstep (se 2 (by rfl) ⟨821913, by rfl⟩ : syracuseStep 2191769 = 1643827) B1643827
theorem B2191859 : Blo 972592 2191859 := bstep (se 1 (by rfl) ⟨1643894, by rfl⟩ : syracuseStep 2191859 = 3287789) B3287789
theorem B63336977 : Blo 972592 63336977 := bstep (se 2 (by rfl) ⟨23751366, by rfl⟩ : syracuseStep 63336977 = 47502733) B47502733
theorem B2191895 : Blo 972592 2191895 := bstep (se 1 (by rfl) ⟨1643921, by rfl⟩ : syracuseStep 2191895 = 3287843) B3287843
theorem B1667659 : Blo 972592 1667659 := bstep (se 1 (by rfl) ⟨1250744, by rfl⟩ : syracuseStep 1667659 = 2501489) B2501489
theorem B4158155 : Blo 972592 4158155 := bstep (se 1 (by rfl) ⟨3118616, by rfl⟩ : syracuseStep 4158155 = 6237233) B6237233
theorem B2192075 : Blo 972592 2192075 := bstep (se 1 (by rfl) ⟨1644056, by rfl⟩ : syracuseStep 2192075 = 3288113) B3288113
theorem B2192129 : Blo 972592 2192129 := bstep (se 2 (by rfl) ⟨822048, by rfl⟩ : syracuseStep 2192129 = 1644097) B1644097
theorem B5010221 : Blo 972592 5010221 := bstep (se 3 (by rfl) ⟨939416, by rfl⟩ : syracuseStep 5010221 = 1878833) B1878833
theorem B2192345 : Blo 972592 2192345 := bstep (se 2 (by rfl) ⟨822129, by rfl⟩ : syracuseStep 2192345 = 1644259) B1644259
theorem B2192435 : Blo 972592 2192435 := bstep (se 1 (by rfl) ⟨1644326, by rfl⟩ : syracuseStep 2192435 = 3288653) B3288653
theorem B2192471 : Blo 972592 2192471 := bstep (se 1 (by rfl) ⟨1644353, by rfl⟩ : syracuseStep 2192471 = 3288707) B3288707
theorem B4224089 : Blo 972592 4224089 := bstep (se 2 (by rfl) ⟨1584033, by rfl⟩ : syracuseStep 4224089 = 3168067) B3168067
theorem B3699857 : Blo 972592 3699857 := bstep (se 2 (by rfl) ⟨1387446, by rfl⟩ : syracuseStep 3699857 = 2774893) B2774893
theorem B2192651 : Blo 972592 2192651 := bstep (se 1 (by rfl) ⟨1644488, by rfl⟩ : syracuseStep 2192651 = 3288977) B3288977
theorem B2192705 : Blo 972592 2192705 := bstep (se 2 (by rfl) ⟨822264, by rfl⟩ : syracuseStep 2192705 = 1644529) B1644529
theorem B3208627 : Blo 972592 3208627 := bstep (se 1 (by rfl) ⟨2406470, by rfl⟩ : syracuseStep 3208627 = 4812941) B4812941
theorem B2192921 : Blo 972592 2192921 := bstep (se 2 (by rfl) ⟨822345, by rfl⟩ : syracuseStep 2192921 = 1644691) B1644691
theorem B3700313 : Blo 972592 3700313 := bstep (se 2 (by rfl) ⟨1387617, by rfl⟩ : syracuseStep 3700313 = 2775235) B2775235
theorem B2193011 : Blo 972592 2193011 := bstep (se 1 (by rfl) ⟨1644758, by rfl⟩ : syracuseStep 2193011 = 3289517) B3289517
theorem B4159127 : Blo 972592 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B2193047 : Blo 972592 2193047 := bstep (se 1 (by rfl) ⟨1644785, by rfl⟩ : syracuseStep 2193047 = 3289571) B3289571
theorem B3700525 : Blo 972592 3700525 := bstep (se 3 (by rfl) ⟨693848, by rfl⟩ : syracuseStep 3700525 = 1387697) B1387697
theorem B2193227 : Blo 972592 2193227 := bstep (se 1 (by rfl) ⟨1644920, by rfl⟩ : syracuseStep 2193227 = 3289841) B3289841
theorem B2193281 : Blo 972592 2193281 := bstep (se 2 (by rfl) ⟨822480, by rfl⟩ : syracuseStep 2193281 = 1644961) B1644961
theorem B2193497 : Blo 972592 2193497 := bstep (se 2 (by rfl) ⟨822561, by rfl⟩ : syracuseStep 2193497 = 1645123) B1645123
theorem B3700829 : Blo 972592 3700829 := bstep (se 3 (by rfl) ⟨693905, by rfl⟩ : syracuseStep 3700829 = 1387811) B1387811
theorem B1112215 : Blo 972592 1112215 := bstep (se 1 (by rfl) ⟨834161, by rfl⟩ : syracuseStep 1112215 = 1668323) B1668323
theorem B7502003 : Blo 972592 7502003 := bstep (se 1 (by rfl) ⟨5626502, by rfl⟩ : syracuseStep 7502003 = 11253005) B11253005
theorem B2193587 : Blo 972592 2193587 := bstep (se 1 (by rfl) ⟨1645190, by rfl⟩ : syracuseStep 2193587 = 3290381) B3290381
theorem B2193623 : Blo 972592 2193623 := bstep (se 1 (by rfl) ⟨1645217, by rfl⟩ : syracuseStep 2193623 = 3290435) B3290435
theorem B4159795 : Blo 972592 4159795 := bstep (se 1 (by rfl) ⟨3119846, by rfl⟩ : syracuseStep 4159795 = 6239693) B6239693
theorem B2193803 : Blo 972592 2193803 := bstep (se 1 (by rfl) ⟨1645352, by rfl⟩ : syracuseStep 2193803 = 3290705) B3290705
theorem B2193857 : Blo 972592 2193857 := bstep (se 2 (by rfl) ⟨822696, by rfl⟩ : syracuseStep 2193857 = 1645393) B1645393
theorem B126482957 : Blo 972592 126482957 := bstep (se 3 (by rfl) ⟨23715554, by rfl⟩ : syracuseStep 126482957 = 47431109) B47431109
theorem B9370187 : Blo 972592 9370187 := bstep (se 1 (by rfl) ⟨7027640, by rfl⟩ : syracuseStep 9370187 = 14055281) B14055281
theorem B2194073 : Blo 972592 2194073 := bstep (se 2 (by rfl) ⟨822777, by rfl⟩ : syracuseStep 2194073 = 1645555) B1645555
theorem B7404209 : Blo 972592 7404209 := bstep (se 2 (by rfl) ⟨2776578, by rfl⟩ : syracuseStep 7404209 = 5553157) B5553157
theorem B2194163 : Blo 972592 2194163 := bstep (se 1 (by rfl) ⟨1645622, by rfl⟩ : syracuseStep 2194163 = 3291245) B3291245
theorem B2194199 : Blo 972592 2194199 := bstep (se 1 (by rfl) ⟨1645649, by rfl⟩ : syracuseStep 2194199 = 3291299) B3291299
theorem B6749021 : Blo 972592 6749021 := bstep (se 3 (by rfl) ⟨1265441, by rfl⟩ : syracuseStep 6749021 = 2530883) B2530883
theorem B2816947 : Blo 972592 2816947 := bstep (se 1 (by rfl) ⟨2112710, by rfl⟩ : syracuseStep 2816947 = 4225421) B4225421
theorem B2194379 : Blo 972592 2194379 := bstep (se 1 (by rfl) ⟨1645784, by rfl⟩ : syracuseStep 2194379 = 3291569) B3291569
theorem B2194433 : Blo 972592 2194433 := bstep (se 2 (by rfl) ⟨822912, by rfl⟩ : syracuseStep 2194433 = 1645825) B1645825
theorem B8879179 : Blo 972592 8879179 := bstep (se 1 (by rfl) ⟨6659384, by rfl⟩ : syracuseStep 8879179 = 13318769) B13318769
theorem B7404695 : Blo 972592 7404695 := bstep (se 1 (by rfl) ⟨5553521, by rfl⟩ : syracuseStep 7404695 = 11107043) B11107043
theorem B8879321 : Blo 972592 8879321 := bstep (se 2 (by rfl) ⟨3329745, by rfl⟩ : syracuseStep 8879321 = 6659491) B6659491
theorem B2194649 : Blo 972592 2194649 := bstep (se 2 (by rfl) ⟨822993, by rfl⟩ : syracuseStep 2194649 = 1645987) B1645987
theorem B7896365 : Blo 972592 7896365 := bstep (se 3 (by rfl) ⟨1480568, by rfl⟩ : syracuseStep 7896365 = 2961137) B2961137
theorem B2194739 : Blo 972592 2194739 := bstep (se 1 (by rfl) ⟨1646054, by rfl⟩ : syracuseStep 2194739 = 3292109) B3292109
theorem B2194775 : Blo 972592 2194775 := bstep (se 1 (by rfl) ⟨1646081, by rfl⟩ : syracuseStep 2194775 = 3292163) B3292163
theorem B2194955 : Blo 972592 2194955 := bstep (se 1 (by rfl) ⟨1646216, by rfl⟩ : syracuseStep 2194955 = 3292433) B3292433
theorem B4161041 : Blo 972592 4161041 := bstep (se 2 (by rfl) ⟨1560390, by rfl⟩ : syracuseStep 4161041 = 3120781) B3120781
theorem B2195009 : Blo 972592 2195009 := bstep (se 2 (by rfl) ⟨823128, by rfl⟩ : syracuseStep 2195009 = 1646257) B1646257
theorem B2195225 : Blo 972592 2195225 := bstep (se 2 (by rfl) ⟨823209, by rfl⟩ : syracuseStep 2195225 = 1646419) B1646419
theorem B4685633 : Blo 972592 4685633 := bstep (se 2 (by rfl) ⟨1757112, by rfl⟩ : syracuseStep 4685633 = 3514225) B3514225
theorem B2195315 : Blo 972592 2195315 := bstep (se 1 (by rfl) ⟨1646486, by rfl⟩ : syracuseStep 2195315 = 3292973) B3292973
theorem B2195351 : Blo 972592 2195351 := bstep (se 1 (by rfl) ⟨1646513, by rfl⟩ : syracuseStep 2195351 = 3293027) B3293027
theorem B2195603 : Blo 972592 2195603 := bstep (se 1 (by rfl) ⟨1646702, by rfl⟩ : syracuseStep 2195603 = 3293405) B3293405
theorem B2195657 : Blo 972592 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B4161793 : Blo 972592 4161793 := bstep (se 2 (by rfl) ⟨1560672, by rfl⟩ : syracuseStep 4161793 = 3121345) B3121345
theorem B10519105 : Blo 972592 10519105 := bstep (se 2 (by rfl) ⟨3944664, by rfl⟩ : syracuseStep 10519105 = 7889329) B7889329
theorem B4686707 : Blo 972592 4686707 := bstep (se 1 (by rfl) ⟨3515030, by rfl⟩ : syracuseStep 4686707 = 7030061) B7030061
theorem B2196359 : Blo 972592 2196359 := bstep (se 1 (by rfl) ⟨1647269, by rfl⟩ : syracuseStep 2196359 = 3294539) B3294539
theorem B2196539 : Blo 972592 2196539 := bstep (se 1 (by rfl) ⟨1647404, by rfl⟩ : syracuseStep 2196539 = 3294809) B3294809
theorem B3703927 : Blo 972592 3703927 := bstep (se 1 (by rfl) ⟨2777945, by rfl⟩ : syracuseStep 3703927 = 5555891) B5555891
theorem B2196665 : Blo 972592 2196665 := bstep (se 2 (by rfl) ⟨823749, by rfl⟩ : syracuseStep 2196665 = 1647499) B1647499
theorem B7013891 : Blo 972592 7013891 := bstep (se 1 (by rfl) ⟨5260418, by rfl⟩ : syracuseStep 7013891 = 10520837) B10520837
theorem B2197007 : Blo 972592 2197007 := bstep (se 1 (by rfl) ⟨1647755, by rfl⟩ : syracuseStep 2197007 = 3295511) B3295511
theorem B2197025 : Blo 972592 2197025 := bstep (se 2 (by rfl) ⟨823884, by rfl⟩ : syracuseStep 2197025 = 1647769) B1647769
theorem B14976971 : Blo 972592 14976971 := bstep (se 1 (by rfl) ⟨11232728, by rfl⟩ : syracuseStep 14976971 = 22465457) B22465457
theorem B3508285 : Blo 972592 3508285 := bstep (se 3 (by rfl) ⟨657803, by rfl⟩ : syracuseStep 3508285 = 1315607) B1315607
theorem B3704899 : Blo 972592 3704899 := bstep (se 1 (by rfl) ⟨2778674, by rfl⟩ : syracuseStep 3704899 = 5557349) B5557349
theorem B3705203 : Blo 972592 3705203 := bstep (se 1 (by rfl) ⟨2778902, by rfl⟩ : syracuseStep 3705203 = 5557805) B5557805
theorem B5933465 : Blo 972592 5933465 := bstep (se 2 (by rfl) ⟨2225049, by rfl⟩ : syracuseStep 5933465 = 4450099) B4450099
theorem B3705659 : Blo 972592 3705659 := bstep (se 1 (by rfl) ⟨2779244, by rfl⟩ : syracuseStep 3705659 = 5558489) B5558489
theorem B4885697 : Blo 972592 4885697 := bstep (se 2 (by rfl) ⟨1832136, by rfl⟩ : syracuseStep 4885697 = 3664273) B3664273
theorem B3706145 : Blo 972592 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B1641863 : Blo 972592 1641863 := bstep (se 1 (by rfl) ⟨1231397, by rfl⟩ : syracuseStep 1641863 = 2462795) B2462795
theorem B5279293 : Blo 972592 5279293 := bstep (se 3 (by rfl) ⟨989867, by rfl⟩ : syracuseStep 5279293 = 1979735) B1979735
theorem B2854547 : Blo 972592 2854547 := bstep (se 1 (by rfl) ⟨2140910, by rfl⟩ : syracuseStep 2854547 = 4281821) B4281821
theorem B150245077 : Blo 972592 150245077 := bstep (se 7 (by rfl) ⟨1760684, by rfl⟩ : syracuseStep 150245077 = 3521369) B3521369
theorem B9506609 : Blo 972592 9506609 := bstep (se 2 (by rfl) ⟨3564978, by rfl⟩ : syracuseStep 9506609 = 7129957) B7129957
theorem B6328153 : Blo 972592 6328153 := bstep (se 2 (by rfl) ⟨2373057, by rfl⟩ : syracuseStep 6328153 = 4746115) B4746115
theorem B19009397 : Blo 972592 19009397 := bstep (se 5 (by rfl) ⟨891065, by rfl⟩ : syracuseStep 19009397 = 1782131) B1782131
theorem B5541767 : Blo 972592 5541767 := bstep (se 1 (by rfl) ⟨4156325, by rfl⟩ : syracuseStep 5541767 = 8312651) B8312651
theorem B1642511 : Blo 972592 1642511 := bstep (se 1 (by rfl) ⟨1231883, by rfl⟩ : syracuseStep 1642511 = 2463767) B2463767
theorem B3117143 : Blo 972592 3117143 := bstep (se 1 (by rfl) ⟨2337857, by rfl⟩ : syracuseStep 3117143 = 4675715) B4675715
theorem B34214089 : Blo 972592 34214089 := bstep (se 2 (by rfl) ⟨12830283, by rfl⟩ : syracuseStep 34214089 = 25660567) B25660567
theorem B3707117 : Blo 972592 3707117 := bstep (se 3 (by rfl) ⟨695084, by rfl⟩ : syracuseStep 3707117 = 1390169) B1390169
theorem B2461985 : Blo 972592 2461985 := bstep (se 2 (by rfl) ⟨923244, by rfl⟩ : syracuseStep 2461985 = 1846489) B1846489
theorem B1643051 : Blo 972592 1643051 := bstep (se 1 (by rfl) ⟨1232288, by rfl⟩ : syracuseStep 1643051 = 2464577) B2464577
theorem B3117629 : Blo 972592 3117629 := bstep (se 3 (by rfl) ⟨584555, by rfl⟩ : syracuseStep 3117629 = 1169111) B1169111
theorem B6656705 : Blo 972592 6656705 := bstep (se 2 (by rfl) ⟨2496264, by rfl⟩ : syracuseStep 6656705 = 4992529) B4992529
theorem B3707801 : Blo 972592 3707801 := bstep (se 2 (by rfl) ⟨1390425, by rfl⟩ : syracuseStep 3707801 = 2780851) B2780851
theorem B1315769 : Blo 972592 1315769 := bstep (se 2 (by rfl) ⟨493413, by rfl⟩ : syracuseStep 1315769 = 986827) B986827
theorem B1643449 : Blo 972592 1643449 := bstep (se 2 (by rfl) ⟨616293, by rfl⟩ : syracuseStep 1643449 = 1232587) B1232587
theorem B3511225 : Blo 972592 3511225 := bstep (se 2 (by rfl) ⟨1316709, by rfl⟩ : syracuseStep 3511225 = 2633419) B2633419
theorem B7017605 : Blo 972592 7017605 := bstep (se 4 (by rfl) ⟨657900, by rfl⟩ : syracuseStep 7017605 = 1315801) B1315801
theorem B2462987 : Blo 972592 2462987 := bstep (se 1 (by rfl) ⟨1847240, by rfl⟩ : syracuseStep 2462987 = 3694481) B3694481
theorem B3511687 : Blo 972592 3511687 := bstep (se 1 (by rfl) ⟨2633765, by rfl⟩ : syracuseStep 3511687 = 5267531) B5267531
theorem B13342157 : Blo 972592 13342157 := bstep (se 3 (by rfl) ⟨2501654, by rfl⟩ : syracuseStep 13342157 = 5003309) B5003309
theorem B1316359 : Blo 972592 1316359 := bstep (se 1 (by rfl) ⟨987269, by rfl⟩ : syracuseStep 1316359 = 1974539) B1974539
theorem B3282551 : Blo 972592 3282551 := bstep (se 1 (by rfl) ⟨2461913, by rfl⟩ : syracuseStep 3282551 = 4923827) B4923827
theorem B1644151 : Blo 972592 1644151 := bstep (se 1 (by rfl) ⟨1233113, by rfl⟩ : syracuseStep 1644151 = 2466227) B2466227
theorem B1644347 : Blo 972592 1644347 := bstep (se 1 (by rfl) ⟨1233260, by rfl⟩ : syracuseStep 1644347 = 2466521) B2466521
theorem B2463635 : Blo 972592 2463635 := bstep (se 1 (by rfl) ⟨1847726, by rfl⟩ : syracuseStep 2463635 = 3695453) B3695453
theorem B2463929 : Blo 972592 2463929 := bstep (se 2 (by rfl) ⟨923973, by rfl⟩ : syracuseStep 2463929 = 1847947) B1847947
theorem B3283145 : Blo 972592 3283145 := bstep (se 2 (by rfl) ⟨1231179, by rfl⟩ : syracuseStep 3283145 = 2462359) B2462359
theorem B1644745 : Blo 972592 1644745 := bstep (se 2 (by rfl) ⟨616779, by rfl⟩ : syracuseStep 1644745 = 1233559) B1233559
theorem B23992561 : Blo 972592 23992561 := bstep (se 2 (by rfl) ⟨8997210, by rfl⟩ : syracuseStep 23992561 = 17994421) B17994421
theorem B2464627 : Blo 972592 2464627 := bstep (se 1 (by rfl) ⟨1848470, by rfl⟩ : syracuseStep 2464627 = 3696941) B3696941
theorem B3283847 : Blo 972592 3283847 := bstep (se 1 (by rfl) ⟨2462885, by rfl⟩ : syracuseStep 3283847 = 4925771) B4925771
theorem B1645447 : Blo 972592 1645447 := bstep (se 1 (by rfl) ⟨1234085, by rfl⟩ : syracuseStep 1645447 = 2468171) B2468171
theorem B8330147 : Blo 972592 8330147 := bstep (se 1 (by rfl) ⟨6247610, by rfl⟩ : syracuseStep 8330147 = 12495221) B12495221
theorem B2464769 : Blo 972592 2464769 := bstep (se 2 (by rfl) ⟨924288, by rfl⟩ : syracuseStep 2464769 = 1848577) B1848577
theorem B4005065 : Blo 972592 4005065 := bstep (se 2 (by rfl) ⟨1501899, by rfl⟩ : syracuseStep 4005065 = 3003799) B3003799
theorem B3284225 : Blo 972592 3284225 := bstep (se 2 (by rfl) ⟨1231584, by rfl⟩ : syracuseStep 3284225 = 2463169) B2463169
theorem B10132867 : Blo 972592 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B2465225 : Blo 972592 2465225 := bstep (se 2 (by rfl) ⟨924459, by rfl⟩ : syracuseStep 2465225 = 1848919) B1848919
theorem B1646095 : Blo 972592 1646095 := bstep (se 1 (by rfl) ⟨1234571, by rfl⟩ : syracuseStep 1646095 = 2469143) B2469143
theorem B10526237 : Blo 972592 10526237 := bstep (se 3 (by rfl) ⟨1973669, by rfl⟩ : syracuseStep 10526237 = 3947339) B3947339
theorem B2629181 : Blo 972592 2629181 := bstep (se 3 (by rfl) ⟨492971, by rfl⟩ : syracuseStep 2629181 = 985943) B985943
theorem B17997389 : Blo 972592 17997389 := bstep (se 3 (by rfl) ⟨3374510, by rfl⟩ : syracuseStep 17997389 = 6749021) B6749021
theorem B2465579 : Blo 972592 2465579 := bstep (se 1 (by rfl) ⟨1849184, by rfl⟩ : syracuseStep 2465579 = 3698369) B3698369
theorem B1056775 : Blo 972592 1056775 := bstep (se 1 (by rfl) ⟨792581, by rfl⟩ : syracuseStep 1056775 = 1585163) B1585163
theorem B1974287 : Blo 972592 1974287 := bstep (se 1 (by rfl) ⟨1480715, by rfl⟩ : syracuseStep 1974287 = 2961431) B2961431
theorem B3285035 : Blo 972592 3285035 := bstep (se 1 (by rfl) ⟨2463776, by rfl⟩ : syracuseStep 3285035 = 4927553) B4927553
theorem B1646635 : Blo 972592 1646635 := bstep (se 1 (by rfl) ⟨1234976, by rfl⟩ : syracuseStep 1646635 = 2469953) B2469953
theorem B4169789 : Blo 972592 4169789 := bstep (se 3 (by rfl) ⟨781835, by rfl⟩ : syracuseStep 4169789 = 1563671) B1563671
theorem B1646777 : Blo 972592 1646777 := bstep (se 2 (by rfl) ⟨617541, by rfl⟩ : syracuseStep 1646777 = 1235083) B1235083
theorem B1482953 : Blo 972592 1482953 := bstep (se 2 (by rfl) ⟨556107, by rfl⟩ : syracuseStep 1482953 = 1112215) B1112215
theorem B5546393 : Blo 972592 5546393 := bstep (se 2 (by rfl) ⟨2079897, by rfl⟩ : syracuseStep 5546393 = 4159795) B4159795
theorem B1384975 : Blo 972592 1384975 := bstep (se 1 (by rfl) ⟨1038731, by rfl⟩ : syracuseStep 1384975 = 2077463) B2077463
theorem B1385095 : Blo 972592 1385095 := bstep (se 1 (by rfl) ⟨1038821, by rfl⟩ : syracuseStep 1385095 = 2077643) B2077643
theorem B11117249 : Blo 972592 11117249 := bstep (se 2 (by rfl) ⟨4168968, by rfl⟩ : syracuseStep 11117249 = 8337937) B8337937
theorem B2466571 : Blo 972592 2466571 := bstep (se 1 (by rfl) ⟨1849928, by rfl⟩ : syracuseStep 2466571 = 3699857) B3699857
theorem B1647479 : Blo 972592 1647479 := bstep (se 1 (by rfl) ⟨1235609, by rfl⟩ : syracuseStep 1647479 = 2471219) B2471219
theorem B4924313 : Blo 972592 4924313 := bstep (se 2 (by rfl) ⟨1846617, by rfl⟩ : syracuseStep 4924313 = 3693235) B3693235
theorem B2466713 : Blo 972592 2466713 := bstep (se 2 (by rfl) ⟨925017, by rfl⟩ : syracuseStep 2466713 = 1850035) B1850035
theorem B2466875 : Blo 972592 2466875 := bstep (se 1 (by rfl) ⟨1850156, by rfl⟩ : syracuseStep 2466875 = 3700313) B3700313
theorem B3286331 : Blo 972592 3286331 := bstep (se 1 (by rfl) ⟨2464748, by rfl⟩ : syracuseStep 3286331 = 4929497) B4929497
theorem B1647931 : Blo 972592 1647931 := bstep (se 1 (by rfl) ⟨1235948, by rfl⟩ : syracuseStep 1647931 = 2471897) B2471897
theorem B2467219 : Blo 972592 2467219 := bstep (se 1 (by rfl) ⟨1850414, by rfl⟩ : syracuseStep 2467219 = 3700829) B3700829
theorem B11838905 : Blo 972592 11838905 := bstep (se 2 (by rfl) ⟨4439589, by rfl⟩ : syracuseStep 11838905 = 8879179) B8879179
theorem B2467361 : Blo 972592 2467361 := bstep (se 2 (by rfl) ⟨925260, by rfl⟩ : syracuseStep 2467361 = 1850521) B1850521
theorem B84321971 : Blo 972592 84321971 := bstep (se 1 (by rfl) ⟨63241478, by rfl⟩ : syracuseStep 84321971 = 126482957) B126482957
theorem B3286817 : Blo 972592 3286817 := bstep (se 2 (by rfl) ⟨1232556, by rfl⟩ : syracuseStep 3286817 = 2465113) B2465113
theorem B9381683 : Blo 972592 9381683 := bstep (se 1 (by rfl) ⟨7036262, by rfl⟩ : syracuseStep 9381683 = 14072525) B14072525
theorem B1386553 : Blo 972592 1386553 := bstep (se 2 (by rfl) ⟨519957, by rfl⟩ : syracuseStep 1386553 = 1039915) B1039915
theorem B3287411 : Blo 972592 3287411 := bstep (se 1 (by rfl) ⟨2465558, by rfl⟩ : syracuseStep 3287411 = 4931117) B4931117
theorem B2337281 : Blo 972592 2337281 := bstep (se 2 (by rfl) ⟨876480, by rfl⟩ : syracuseStep 2337281 = 1752961) B1752961
theorem B2468353 : Blo 972592 2468353 := bstep (se 2 (by rfl) ⟨925632, by rfl⟩ : syracuseStep 2468353 = 1851265) B1851265
theorem B3123755 : Blo 972592 3123755 := bstep (se 1 (by rfl) ⟨2342816, by rfl⟩ : syracuseStep 3123755 = 4685633) B4685633
theorem B19999493 : Blo 972592 19999493 := bstep (se 4 (by rfl) ⟨1874952, by rfl⟩ : syracuseStep 19999493 = 3749905) B3749905
theorem B2468951 : Blo 972592 2468951 := bstep (se 1 (by rfl) ⟨1851713, by rfl⟩ : syracuseStep 2468951 = 3703427) B3703427
theorem B1387783 : Blo 972592 1387783 := bstep (se 1 (by rfl) ⟨1040837, by rfl⟩ : syracuseStep 1387783 = 2081675) B2081675
theorem B2469163 : Blo 972592 2469163 := bstep (se 1 (by rfl) ⟨1851872, by rfl⟩ : syracuseStep 2469163 = 3703745) B3703745
theorem B4926905 : Blo 972592 4926905 := bstep (se 2 (by rfl) ⟨1847589, by rfl⟩ : syracuseStep 4926905 = 3695179) B3695179
theorem B2469305 : Blo 972592 2469305 := bstep (se 2 (by rfl) ⟨925989, by rfl⟩ : syracuseStep 2469305 = 1851979) B1851979
theorem B5549741 : Blo 972592 5549741 := bstep (se 3 (by rfl) ⟨1040576, by rfl⟩ : syracuseStep 5549741 = 2081153) B2081153
theorem B26619799 : Blo 972592 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B1847225 : Blo 972592 1847225 := bstep (se 2 (by rfl) ⟨692709, by rfl⟩ : syracuseStep 1847225 = 1385419) B1385419
theorem B109555733 : Blo 972592 109555733 := bstep (se 6 (by rfl) ⟨2567712, by rfl⟩ : syracuseStep 109555733 = 5135425) B5135425
theorem B1388603 : Blo 972592 1388603 := bstep (se 1 (by rfl) ⟨1041452, by rfl⟩ : syracuseStep 1388603 = 2082905) B2082905
theorem B2109739 : Blo 972592 2109739 := bstep (se 1 (by rfl) ⟨1582304, by rfl⟩ : syracuseStep 2109739 = 3164609) B3164609
theorem B2470297 : Blo 972592 2470297 := bstep (se 2 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 2470297 = 1852723) B1852723
theorem B2470459 : Blo 972592 2470459 := bstep (se 1 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 2470459 = 3705689) B3705689
theorem B1094287 : Blo 972592 1094287 := bstep (se 1 (by rfl) ⟨820715, by rfl⟩ : syracuseStep 1094287 = 1641431) B1641431
theorem B1389241 : Blo 972592 1389241 := bstep (se 2 (by rfl) ⟨520965, by rfl⟩ : syracuseStep 1389241 = 1041931) B1041931
theorem B4928201 : Blo 972592 4928201 := bstep (se 2 (by rfl) ⟨1848075, by rfl⟩ : syracuseStep 4928201 = 3696151) B3696151
theorem B2470601 : Blo 972592 2470601 := bstep (se 2 (by rfl) ⟨926475, by rfl⟩ : syracuseStep 2470601 = 1852951) B1852951
theorem B4010867 : Blo 972592 4010867 := bstep (se 1 (by rfl) ⟨3008150, by rfl⟩ : syracuseStep 4010867 = 6016301) B6016301
theorem B3290003 : Blo 972592 3290003 := bstep (se 1 (by rfl) ⟨2467502, by rfl⟩ : syracuseStep 3290003 = 4935005) B4935005
theorem B2470945 : Blo 972592 2470945 := bstep (se 2 (by rfl) ⟨926604, by rfl⟩ : syracuseStep 2470945 = 1853209) B1853209
theorem B1094791 : Blo 972592 1094791 := bstep (se 1 (by rfl) ⟨821093, by rfl⟩ : syracuseStep 1094791 = 1642187) B1642187
theorem B1094971 : Blo 972592 1094971 := bstep (se 1 (by rfl) ⟨821228, by rfl⟩ : syracuseStep 1094971 = 1642457) B1642457
theorem B9352583 : Blo 972592 9352583 := bstep (se 1 (by rfl) ⟨7014437, by rfl⟩ : syracuseStep 9352583 = 14028875) B14028875
theorem B2635193 : Blo 972592 2635193 := bstep (se 2 (by rfl) ⟨988197, by rfl⟩ : syracuseStep 2635193 = 1976395) B1976395
theorem B2471543 : Blo 972592 2471543 := bstep (se 1 (by rfl) ⟨1853657, by rfl⟩ : syracuseStep 2471543 = 3707315) B3707315
theorem B1095439 : Blo 972592 1095439 := bstep (se 1 (by rfl) ⟨821579, by rfl⟩ : syracuseStep 1095439 = 1643159) B1643159
theorem B1849223 : Blo 972592 1849223 := bstep (se 1 (by rfl) ⟨1386917, by rfl⟩ : syracuseStep 1849223 = 2773835) B2773835
theorem B2340809 : Blo 972592 2340809 := bstep (se 2 (by rfl) ⟨877803, by rfl⟩ : syracuseStep 2340809 = 1755607) B1755607
theorem B86751245 : Blo 972592 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B2439227 : Blo 972592 2439227 := bstep (se 1 (by rfl) ⟨1829420, by rfl⟩ : syracuseStep 2439227 = 3658841) B3658841
theorem B1095943 : Blo 972592 1095943 := bstep (se 1 (by rfl) ⟨821957, by rfl⟩ : syracuseStep 1095943 = 1643915) B1643915
theorem B3291407 : Blo 972592 3291407 := bstep (se 1 (by rfl) ⟨2468555, by rfl⟩ : syracuseStep 3291407 = 4937111) B4937111
theorem B2341163 : Blo 972592 2341163 := bstep (se 1 (by rfl) ⟨1755872, by rfl⟩ : syracuseStep 2341163 = 3511745) B3511745
theorem B1096123 : Blo 972592 1096123 := bstep (se 1 (by rfl) ⟨822092, by rfl⟩ : syracuseStep 1096123 = 1644185) B1644185
theorem B9353731 : Blo 972592 9353731 := bstep (se 1 (by rfl) ⟨7015298, by rfl⟩ : syracuseStep 9353731 = 14030597) B14030597
theorem B3291677 : Blo 972592 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B1096591 : Blo 972592 1096591 := bstep (se 1 (by rfl) ⟨822443, by rfl⟩ : syracuseStep 1096591 = 1644887) B1644887
theorem B2341817 : Blo 972592 2341817 := bstep (se 2 (by rfl) ⟨878181, by rfl⟩ : syracuseStep 2341817 = 1756363) B1756363
theorem B4996099 : Blo 972592 4996099 := bstep (se 1 (by rfl) ⟨3747074, by rfl⟩ : syracuseStep 4996099 = 7494149) B7494149
theorem B7388171 : Blo 972592 7388171 := bstep (se 1 (by rfl) ⟨5541128, by rfl⟩ : syracuseStep 7388171 = 11082257) B11082257
theorem B2079803 : Blo 972592 2079803 := bstep (se 1 (by rfl) ⟨1559852, by rfl⟩ : syracuseStep 2079803 = 3119705) B3119705
theorem B11091005 : Blo 972592 11091005 := bstep (se 3 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 11091005 = 4159127) B4159127
theorem B3161207 : Blo 972592 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B60833045 : Blo 972592 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B15777155 : Blo 972592 15777155 := bstep (se 1 (by rfl) ⟨11832866, by rfl⟩ : syracuseStep 15777155 = 23665733) B23665733
theorem B1097095 : Blo 972592 1097095 := bstep (se 1 (by rfl) ⟨822821, by rfl⟩ : syracuseStep 1097095 = 1645643) B1645643
theorem B1850825 : Blo 972592 1850825 := bstep (se 2 (by rfl) ⟨694059, by rfl⟩ : syracuseStep 1850825 = 1388119) B1388119
theorem B1097275 : Blo 972592 1097275 := bstep (se 1 (by rfl) ⟨822956, by rfl⟩ : syracuseStep 1097275 = 1645913) B1645913
theorem B53395037 : Blo 972592 53395037 := bstep (se 3 (by rfl) ⟨10011569, by rfl⟩ : syracuseStep 53395037 = 20023139) B20023139
theorem B2342585 : Blo 972592 2342585 := bstep (se 2 (by rfl) ⟨878469, by rfl⟩ : syracuseStep 2342585 = 1756939) B1756939
theorem B3293081 : Blo 972592 3293081 := bstep (se 2 (by rfl) ⟨1234905, by rfl⟩ : syracuseStep 3293081 = 2469811) B2469811
theorem B1097743 : Blo 972592 1097743 := bstep (se 1 (by rfl) ⟨823307, by rfl⟩ : syracuseStep 1097743 = 1646615) B1646615
theorem B5554433 : Blo 972592 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B7029139 : Blo 972592 7029139 := bstep (se 1 (by rfl) ⟨5271854, by rfl⟩ : syracuseStep 7029139 = 10543709) B10543709
theorem B8339921 : Blo 972592 8339921 := bstep (se 2 (by rfl) ⟨3127470, by rfl⟩ : syracuseStep 8339921 = 6254941) B6254941
theorem B1098247 : Blo 972592 1098247 := bstep (se 1 (by rfl) ⟨823685, by rfl⟩ : syracuseStep 1098247 = 1647371) B1647371
theorem B3293783 : Blo 972592 3293783 := bstep (se 1 (by rfl) ⟨2470337, by rfl⟩ : syracuseStep 3293783 = 4940675) B4940675
theorem B1098427 : Blo 972592 1098427 := bstep (se 1 (by rfl) ⟨823820, by rfl⟩ : syracuseStep 1098427 = 1647641) B1647641
theorem B5554889 : Blo 972592 5554889 := bstep (se 2 (by rfl) ⟨2083083, by rfl⟩ : syracuseStep 5554889 = 4166167) B4166167
theorem B1458935 : Blo 972592 1458935 := bstep (se 1 (by rfl) ⟨1094201, by rfl⟩ : syracuseStep 1458935 = 2188403) B2188403
theorem B1458959 : Blo 972592 1458959 := bstep (se 1 (by rfl) ⟨1094219, by rfl⟩ : syracuseStep 1458959 = 2188439) B2188439
theorem B1459001 : Blo 972592 1459001 := bstep (se 2 (by rfl) ⟨547125, by rfl⟩ : syracuseStep 1459001 = 1094251) B1094251
theorem B1459079 : Blo 972592 1459079 := bstep (se 1 (by rfl) ⟨1094309, by rfl⟩ : syracuseStep 1459079 = 2188619) B2188619
theorem B3752851 : Blo 972592 3752851 := bstep (se 1 (by rfl) ⟨2814638, by rfl⟩ : syracuseStep 3752851 = 5629277) B5629277
theorem B7390115 : Blo 972592 7390115 := bstep (se 1 (by rfl) ⟨5542586, by rfl⟩ : syracuseStep 7390115 = 11085173) B11085173
theorem B1459115 : Blo 972592 1459115 := bstep (se 1 (by rfl) ⟨1094336, by rfl⟩ : syracuseStep 1459115 = 2188673) B2188673
theorem B1459145 : Blo 972592 1459145 := bstep (se 2 (by rfl) ⟨547179, by rfl⟩ : syracuseStep 1459145 = 1094359) B1094359
theorem B1459259 : Blo 972592 1459259 := bstep (se 1 (by rfl) ⟨1094444, by rfl⟩ : syracuseStep 1459259 = 2188889) B2188889
theorem B1754171 : Blo 972592 1754171 := bstep (se 1 (by rfl) ⟨1315628, by rfl⟩ : syracuseStep 1754171 = 2631257) B2631257
theorem B3294269 : Blo 972592 3294269 := bstep (se 3 (by rfl) ⟨617675, by rfl⟩ : syracuseStep 3294269 = 1235351) B1235351
theorem B1459319 : Blo 972592 1459319 := bstep (se 1 (by rfl) ⟨1094489, by rfl⟩ : syracuseStep 1459319 = 2188979) B2188979
theorem B1459343 : Blo 972592 1459343 := bstep (se 1 (by rfl) ⟨1094507, by rfl⟩ : syracuseStep 1459343 = 2189015) B2189015
theorem B1459385 : Blo 972592 1459385 := bstep (se 2 (by rfl) ⟨547269, by rfl⟩ : syracuseStep 1459385 = 1094539) B1094539
theorem B1459463 : Blo 972592 1459463 := bstep (se 1 (by rfl) ⟨1094597, by rfl⟩ : syracuseStep 1459463 = 2189195) B2189195
theorem B1459499 : Blo 972592 1459499 := bstep (se 1 (by rfl) ⟨1094624, by rfl⟩ : syracuseStep 1459499 = 2189249) B2189249
theorem B1459529 : Blo 972592 1459529 := bstep (se 2 (by rfl) ⟨547323, by rfl⟩ : syracuseStep 1459529 = 1094647) B1094647
theorem B2770291 : Blo 972592 2770291 := bstep (se 1 (by rfl) ⟨2077718, by rfl⟩ : syracuseStep 2770291 = 4155437) B4155437
theorem B56935811 : Blo 972592 56935811 := bstep (se 1 (by rfl) ⟨42701858, by rfl⟩ : syracuseStep 56935811 = 85403717) B85403717
theorem B1852807 : Blo 972592 1852807 := bstep (se 1 (by rfl) ⟨1389605, by rfl⟩ : syracuseStep 1852807 = 2779211) B2779211
theorem B1459643 : Blo 972592 1459643 := bstep (se 1 (by rfl) ⟨1094732, by rfl⟩ : syracuseStep 1459643 = 2189465) B2189465
theorem B1459703 : Blo 972592 1459703 := bstep (se 1 (by rfl) ⟨1094777, by rfl⟩ : syracuseStep 1459703 = 2189555) B2189555
theorem B1459727 : Blo 972592 1459727 := bstep (se 1 (by rfl) ⟨1094795, by rfl⟩ : syracuseStep 1459727 = 2189591) B2189591
theorem B1459769 : Blo 972592 1459769 := bstep (se 2 (by rfl) ⟨547413, by rfl⟩ : syracuseStep 1459769 = 1094827) B1094827
theorem B2770519 : Blo 972592 2770519 := bstep (se 1 (by rfl) ⟨2077889, by rfl⟩ : syracuseStep 2770519 = 4155779) B4155779
theorem B1558135 : Blo 972592 1558135 := bstep (se 1 (by rfl) ⟨1168601, by rfl⟩ : syracuseStep 1558135 = 2337203) B2337203
theorem B1459847 : Blo 972592 1459847 := bstep (se 1 (by rfl) ⟨1094885, by rfl⟩ : syracuseStep 1459847 = 2189771) B2189771
theorem B1459883 : Blo 972592 1459883 := bstep (se 1 (by rfl) ⟨1094912, by rfl⟩ : syracuseStep 1459883 = 2189825) B2189825
theorem B1459913 : Blo 972592 1459913 := bstep (se 2 (by rfl) ⟨547467, by rfl⟩ : syracuseStep 1459913 = 1094935) B1094935
theorem B1558315 : Blo 972592 1558315 := bstep (se 1 (by rfl) ⟨1168736, by rfl⟩ : syracuseStep 1558315 = 2337473) B2337473
theorem B1460027 : Blo 972592 1460027 := bstep (se 1 (by rfl) ⟨1095020, by rfl⟩ : syracuseStep 1460027 = 2190041) B2190041
theorem B31672133 : Blo 972592 31672133 := bstep (se 4 (by rfl) ⟨2969262, by rfl⟩ : syracuseStep 31672133 = 5938525) B5938525
theorem B1460087 : Blo 972592 1460087 := bstep (se 1 (by rfl) ⟨1095065, by rfl⟩ : syracuseStep 1460087 = 2190131) B2190131
theorem B1460111 : Blo 972592 1460111 := bstep (se 1 (by rfl) ⟨1095083, by rfl⟩ : syracuseStep 1460111 = 2190167) B2190167
theorem B4278169 : Blo 972592 4278169 := bstep (se 2 (by rfl) ⟨1604313, by rfl⟩ : syracuseStep 4278169 = 3208627) B3208627
theorem B1460153 : Blo 972592 1460153 := bstep (se 2 (by rfl) ⟨547557, by rfl⟩ : syracuseStep 1460153 = 1095115) B1095115
theorem B1755065 : Blo 972592 1755065 := bstep (se 2 (by rfl) ⟨658149, by rfl⟩ : syracuseStep 1755065 = 1316299) B1316299
theorem B1460231 : Blo 972592 1460231 := bstep (se 1 (by rfl) ⟨1095173, by rfl⟩ : syracuseStep 1460231 = 2190347) B2190347
theorem B1755151 : Blo 972592 1755151 := bstep (se 1 (by rfl) ⟨1316363, by rfl⟩ : syracuseStep 1755151 = 2632727) B2632727
theorem B1460267 : Blo 972592 1460267 := bstep (se 1 (by rfl) ⟨1095200, by rfl⟩ : syracuseStep 1460267 = 2190401) B2190401
theorem B1460297 : Blo 972592 1460297 := bstep (se 2 (by rfl) ⟨547611, by rfl⟩ : syracuseStep 1460297 = 1095223) B1095223
theorem B7030871 : Blo 972592 7030871 := bstep (se 1 (by rfl) ⟨5273153, by rfl⟩ : syracuseStep 7030871 = 10546307) B10546307
theorem B1230967 : Blo 972592 1230967 := bstep (se 1 (by rfl) ⟨923225, by rfl⟩ : syracuseStep 1230967 = 1846451) B1846451
theorem B1460411 : Blo 972592 1460411 := bstep (se 1 (by rfl) ⟨1095308, by rfl⟩ : syracuseStep 1460411 = 2190617) B2190617
theorem B1460471 : Blo 972592 1460471 := bstep (se 1 (by rfl) ⟨1095353, by rfl⟩ : syracuseStep 1460471 = 2190707) B2190707
theorem B5130497 : Blo 972592 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B1460495 : Blo 972592 1460495 := bstep (se 1 (by rfl) ⟨1095371, by rfl⟩ : syracuseStep 1460495 = 2190743) B2190743
theorem B1460537 : Blo 972592 1460537 := bstep (se 2 (by rfl) ⟨547701, by rfl⟩ : syracuseStep 1460537 = 1095403) B1095403
theorem B1460615 : Blo 972592 1460615 := bstep (se 1 (by rfl) ⟨1095461, by rfl⟩ : syracuseStep 1460615 = 2190923) B2190923
theorem B4934033 : Blo 972592 4934033 := bstep (se 2 (by rfl) ⟨1850262, by rfl⟩ : syracuseStep 4934033 = 3700525) B3700525
theorem B1460651 : Blo 972592 1460651 := bstep (se 1 (by rfl) ⟨1095488, by rfl⟩ : syracuseStep 1460651 = 2190977) B2190977
theorem B3295673 : Blo 972592 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B1231291 : Blo 972592 1231291 := bstep (se 1 (by rfl) ⟨923468, by rfl⟩ : syracuseStep 1231291 = 1846937) B1846937
theorem B1460681 : Blo 972592 1460681 := bstep (se 2 (by rfl) ⟨547755, by rfl⟩ : syracuseStep 1460681 = 1095511) B1095511
theorem B1460795 : Blo 972592 1460795 := bstep (se 1 (by rfl) ⟨1095596, by rfl⟩ : syracuseStep 1460795 = 2191193) B2191193
theorem B3328573 : Blo 972592 3328573 := bstep (se 3 (by rfl) ⟨624107, by rfl⟩ : syracuseStep 3328573 = 1248215) B1248215
theorem B1460855 : Blo 972592 1460855 := bstep (se 1 (by rfl) ⟨1095641, by rfl⟩ : syracuseStep 1460855 = 2191283) B2191283
theorem B1460879 : Blo 972592 1460879 := bstep (se 1 (by rfl) ⟨1095659, by rfl⟩ : syracuseStep 1460879 = 2191319) B2191319
theorem B1559225 : Blo 972592 1559225 := bstep (se 2 (by rfl) ⟨584709, by rfl⟩ : syracuseStep 1559225 = 1169419) B1169419
theorem B1460921 : Blo 972592 1460921 := bstep (se 2 (by rfl) ⟨547845, by rfl⟩ : syracuseStep 1460921 = 1095691) B1095691
theorem B3001033 : Blo 972592 3001033 := bstep (se 2 (by rfl) ⟨1125387, by rfl⟩ : syracuseStep 3001033 = 2250775) B2250775
theorem B1460999 : Blo 972592 1460999 := bstep (se 1 (by rfl) ⟨1095749, by rfl⟩ : syracuseStep 1460999 = 2191499) B2191499
theorem B1461035 : Blo 972592 1461035 := bstep (se 1 (by rfl) ⟨1095776, by rfl⟩ : syracuseStep 1461035 = 2191553) B2191553
theorem B1461065 : Blo 972592 1461065 := bstep (se 2 (by rfl) ⟨547899, by rfl⟩ : syracuseStep 1461065 = 1095799) B1095799
theorem B1231787 : Blo 972592 1231787 := bstep (se 1 (by rfl) ⟨923840, by rfl⟩ : syracuseStep 1231787 = 1847681) B1847681
theorem B1461179 : Blo 972592 1461179 := bstep (se 1 (by rfl) ⟨1095884, by rfl⟩ : syracuseStep 1461179 = 2191769) B2191769
theorem B1461239 : Blo 972592 1461239 := bstep (se 1 (by rfl) ⟨1095929, by rfl⟩ : syracuseStep 1461239 = 2191859) B2191859
theorem B42224651 : Blo 972592 42224651 := bstep (se 1 (by rfl) ⟨31668488, by rfl⟩ : syracuseStep 42224651 = 63336977) B63336977
theorem B1461263 : Blo 972592 1461263 := bstep (se 1 (by rfl) ⟨1095947, by rfl⟩ : syracuseStep 1461263 = 2191895) B2191895
theorem B1461305 : Blo 972592 1461305 := bstep (se 2 (by rfl) ⟨547989, by rfl⟩ : syracuseStep 1461305 = 1095979) B1095979
theorem B2772103 : Blo 972592 2772103 := bstep (se 1 (by rfl) ⟨2079077, by rfl⟩ : syracuseStep 2772103 = 4158155) B4158155
theorem B1461383 : Blo 972592 1461383 := bstep (se 1 (by rfl) ⟨1096037, by rfl⟩ : syracuseStep 1461383 = 2192075) B2192075
theorem B1461419 : Blo 972592 1461419 := bstep (se 1 (by rfl) ⟨1096064, by rfl⟩ : syracuseStep 1461419 = 2192129) B2192129
theorem B1461449 : Blo 972592 1461449 := bstep (se 2 (by rfl) ⟨548043, by rfl⟩ : syracuseStep 1461449 = 1096087) B1096087
theorem B23678189 : Blo 972592 23678189 := bstep (se 3 (by rfl) ⟨4439660, by rfl⟩ : syracuseStep 23678189 = 8879321) B8879321
theorem B7392545 : Blo 972592 7392545 := bstep (se 2 (by rfl) ⟨2772204, by rfl⟩ : syracuseStep 7392545 = 5544409) B5544409
theorem B1461563 : Blo 972592 1461563 := bstep (se 1 (by rfl) ⟨1096172, by rfl⟩ : syracuseStep 1461563 = 2192345) B2192345
theorem B1461623 : Blo 972592 1461623 := bstep (se 1 (by rfl) ⟨1096217, by rfl⟩ : syracuseStep 1461623 = 2192435) B2192435
theorem B1232263 : Blo 972592 1232263 := bstep (se 1 (by rfl) ⟨924197, by rfl⟩ : syracuseStep 1232263 = 1848395) B1848395
theorem B1461647 : Blo 972592 1461647 := bstep (se 1 (by rfl) ⟨1096235, by rfl⟩ : syracuseStep 1461647 = 2192471) B2192471
theorem B2772377 : Blo 972592 2772377 := bstep (se 2 (by rfl) ⟨1039641, by rfl⟩ : syracuseStep 2772377 = 2079283) B2079283
theorem B1461689 : Blo 972592 1461689 := bstep (se 2 (by rfl) ⟨548133, by rfl⟩ : syracuseStep 1461689 = 1096267) B1096267
theorem B1461767 : Blo 972592 1461767 := bstep (se 1 (by rfl) ⟨1096325, by rfl⟩ : syracuseStep 1461767 = 2192651) B2192651
theorem B1461803 : Blo 972592 1461803 := bstep (se 1 (by rfl) ⟨1096352, by rfl⟩ : syracuseStep 1461803 = 2192705) B2192705
theorem B1461833 : Blo 972592 1461833 := bstep (se 2 (by rfl) ⟨548187, by rfl⟩ : syracuseStep 1461833 = 1096375) B1096375
theorem B1461947 : Blo 972592 1461947 := bstep (se 1 (by rfl) ⟨1096460, by rfl⟩ : syracuseStep 1461947 = 2192921) B2192921
theorem B1462007 : Blo 972592 1462007 := bstep (se 1 (by rfl) ⟨1096505, by rfl⟩ : syracuseStep 1462007 = 2193011) B2193011
theorem B1462031 : Blo 972592 1462031 := bstep (se 1 (by rfl) ⟨1096523, by rfl⟩ : syracuseStep 1462031 = 2193047) B2193047
theorem B1462073 : Blo 972592 1462073 := bstep (se 2 (by rfl) ⟨548277, by rfl⟩ : syracuseStep 1462073 = 1096555) B1096555
theorem B1232759 : Blo 972592 1232759 := bstep (se 1 (by rfl) ⟨924569, by rfl⟩ : syracuseStep 1232759 = 1849139) B1849139
theorem B1462151 : Blo 972592 1462151 := bstep (se 1 (by rfl) ⟨1096613, by rfl⟩ : syracuseStep 1462151 = 2193227) B2193227
theorem B3755929 : Blo 972592 3755929 := bstep (se 2 (by rfl) ⟨1408473, by rfl⟩ : syracuseStep 3755929 = 2816947) B2816947
theorem B1462187 : Blo 972592 1462187 := bstep (se 1 (by rfl) ⟨1096640, by rfl⟩ : syracuseStep 1462187 = 2193281) B2193281
theorem B1462217 : Blo 972592 1462217 := bstep (se 2 (by rfl) ⟨548331, by rfl⟩ : syracuseStep 1462217 = 1096663) B1096663
theorem B1232911 : Blo 972592 1232911 := bstep (se 1 (by rfl) ⟨924683, by rfl⟩ : syracuseStep 1232911 = 1849367) B1849367
theorem B2773025 : Blo 972592 2773025 := bstep (se 2 (by rfl) ⟨1039884, by rfl⟩ : syracuseStep 2773025 = 2079769) B2079769
theorem B1462331 : Blo 972592 1462331 := bstep (se 1 (by rfl) ⟨1096748, by rfl⟩ : syracuseStep 1462331 = 2193497) B2193497
theorem B5001335 : Blo 972592 5001335 := bstep (se 1 (by rfl) ⟨3751001, by rfl⟩ : syracuseStep 5001335 = 7502003) B7502003
theorem B1462391 : Blo 972592 1462391 := bstep (se 1 (by rfl) ⟨1096793, by rfl⟩ : syracuseStep 1462391 = 2193587) B2193587
theorem B1462415 : Blo 972592 1462415 := bstep (se 1 (by rfl) ⟨1096811, by rfl⟩ : syracuseStep 1462415 = 2193623) B2193623
theorem B1462457 : Blo 972592 1462457 := bstep (se 2 (by rfl) ⟨548421, by rfl⟩ : syracuseStep 1462457 = 1096843) B1096843
theorem B2674873 : Blo 972592 2674873 := bstep (se 2 (by rfl) ⟨1003077, by rfl⟩ : syracuseStep 2674873 = 2006155) B2006155
theorem B1233083 : Blo 972592 1233083 := bstep (se 1 (by rfl) ⟨924812, by rfl⟩ : syracuseStep 1233083 = 1849625) B1849625
theorem B7393517 : Blo 972592 7393517 := bstep (se 3 (by rfl) ⟨1386284, by rfl⟩ : syracuseStep 7393517 = 2772569) B2772569
theorem B1462535 : Blo 972592 1462535 := bstep (se 1 (by rfl) ⟨1096901, by rfl⟩ : syracuseStep 1462535 = 2193803) B2193803
theorem B1462571 : Blo 972592 1462571 := bstep (se 1 (by rfl) ⟨1096928, by rfl⟩ : syracuseStep 1462571 = 2193857) B2193857
theorem B1462601 : Blo 972592 1462601 := bstep (se 2 (by rfl) ⟨548475, by rfl⟩ : syracuseStep 1462601 = 1096951) B1096951
theorem B6246791 : Blo 972592 6246791 := bstep (se 1 (by rfl) ⟨4685093, by rfl⟩ : syracuseStep 6246791 = 9370187) B9370187
theorem B1462715 : Blo 972592 1462715 := bstep (se 1 (by rfl) ⟨1097036, by rfl⟩ : syracuseStep 1462715 = 2194073) B2194073
theorem B4936139 : Blo 972592 4936139 := bstep (se 1 (by rfl) ⟨3702104, by rfl⟩ : syracuseStep 4936139 = 7404209) B7404209
theorem B1462775 : Blo 972592 1462775 := bstep (se 1 (by rfl) ⟨1097081, by rfl⟩ : syracuseStep 1462775 = 2194163) B2194163
theorem B1561103 : Blo 972592 1561103 := bstep (se 1 (by rfl) ⟨1170827, by rfl⟩ : syracuseStep 1561103 = 2341655) B2341655
theorem B1462799 : Blo 972592 1462799 := bstep (se 1 (by rfl) ⟨1097099, by rfl⟩ : syracuseStep 1462799 = 2194199) B2194199
theorem B5558807 : Blo 972592 5558807 := bstep (se 1 (by rfl) ⟨4169105, by rfl⟩ : syracuseStep 5558807 = 8338211) B8338211
theorem B1462841 : Blo 972592 1462841 := bstep (se 2 (by rfl) ⟨548565, by rfl⟩ : syracuseStep 1462841 = 1097131) B1097131
theorem B1462919 : Blo 972592 1462919 := bstep (se 1 (by rfl) ⟨1097189, by rfl⟩ : syracuseStep 1462919 = 2194379) B2194379
theorem B1462955 : Blo 972592 1462955 := bstep (se 1 (by rfl) ⟨1097216, by rfl⟩ : syracuseStep 1462955 = 2194433) B2194433
theorem B1462985 : Blo 972592 1462985 := bstep (se 2 (by rfl) ⟨548619, by rfl⟩ : syracuseStep 1462985 = 1097239) B1097239
theorem B4936463 : Blo 972592 4936463 := bstep (se 1 (by rfl) ⟨3702347, by rfl⟩ : syracuseStep 4936463 = 7404695) B7404695
theorem B1463099 : Blo 972592 1463099 := bstep (se 1 (by rfl) ⟨1097324, by rfl⟩ : syracuseStep 1463099 = 2194649) B2194649
theorem B5264243 : Blo 972592 5264243 := bstep (se 1 (by rfl) ⟨3948182, by rfl⟩ : syracuseStep 5264243 = 7896365) B7896365
theorem B1463159 : Blo 972592 1463159 := bstep (se 1 (by rfl) ⟨1097369, by rfl⟩ : syracuseStep 1463159 = 2194739) B2194739
theorem B1463183 : Blo 972592 1463183 := bstep (se 1 (by rfl) ⟨1097387, by rfl⟩ : syracuseStep 1463183 = 2194775) B2194775
theorem B1463225 : Blo 972592 1463225 := bstep (se 2 (by rfl) ⟨548709, by rfl⟩ : syracuseStep 1463225 = 1097419) B1097419
theorem B1463303 : Blo 972592 1463303 := bstep (se 1 (by rfl) ⟨1097477, by rfl⟩ : syracuseStep 1463303 = 2194955) B2194955
theorem B2774027 : Blo 972592 2774027 := bstep (se 1 (by rfl) ⟨2080520, by rfl⟩ : syracuseStep 2774027 = 4161041) B4161041
theorem B1758223 : Blo 972592 1758223 := bstep (se 1 (by rfl) ⟨1318667, by rfl⟩ : syracuseStep 1758223 = 2637335) B2637335
theorem B1463339 : Blo 972592 1463339 := bstep (se 1 (by rfl) ⟨1097504, by rfl⟩ : syracuseStep 1463339 = 2195009) B2195009
theorem B1463369 : Blo 972592 1463369 := bstep (se 2 (by rfl) ⟨548763, by rfl⟩ : syracuseStep 1463369 = 1097527) B1097527
theorem B7918679 : Blo 972592 7918679 := bstep (se 1 (by rfl) ⟨5939009, by rfl⟩ : syracuseStep 7918679 = 11878019) B11878019
theorem B1234055 : Blo 972592 1234055 := bstep (se 1 (by rfl) ⟨925541, by rfl⟩ : syracuseStep 1234055 = 1851083) B1851083
theorem B1463483 : Blo 972592 1463483 := bstep (se 1 (by rfl) ⟨1097612, by rfl⟩ : syracuseStep 1463483 = 2195225) B2195225
theorem B21091565 : Blo 972592 21091565 := bstep (se 3 (by rfl) ⟨3954668, by rfl⟩ : syracuseStep 21091565 = 7909337) B7909337
theorem B1463543 : Blo 972592 1463543 := bstep (se 1 (by rfl) ⟨1097657, by rfl⟩ : syracuseStep 1463543 = 2195315) B2195315
theorem B1463567 : Blo 972592 1463567 := bstep (se 1 (by rfl) ⟨1097675, by rfl⟩ : syracuseStep 1463567 = 2195351) B2195351
theorem B1463609 : Blo 972592 1463609 := bstep (se 2 (by rfl) ⟨548853, by rfl⟩ : syracuseStep 1463609 = 1097707) B1097707
theorem B3954055 : Blo 972592 3954055 := bstep (se 1 (by rfl) ⟨2965541, by rfl⟩ : syracuseStep 3954055 = 5931083) B5931083
theorem B1463687 : Blo 972592 1463687 := bstep (se 1 (by rfl) ⟨1097765, by rfl⟩ : syracuseStep 1463687 = 2195531) B2195531
theorem B1463723 : Blo 972592 1463723 := bstep (se 1 (by rfl) ⟨1097792, by rfl⟩ : syracuseStep 1463723 = 2195585) B2195585
theorem B1463753 : Blo 972592 1463753 := bstep (se 2 (by rfl) ⟨548907, by rfl⟩ : syracuseStep 1463753 = 1097815) B1097815
theorem B50615837 : Blo 972592 50615837 := bstep (se 3 (by rfl) ⟨9490469, by rfl⟩ : syracuseStep 50615837 = 18980939) B18980939
theorem B1463867 : Blo 972592 1463867 := bstep (se 1 (by rfl) ⟨1097900, by rfl⟩ : syracuseStep 1463867 = 2195801) B2195801
theorem B1463927 : Blo 972592 1463927 := bstep (se 1 (by rfl) ⟨1097945, by rfl⟩ : syracuseStep 1463927 = 2195891) B2195891
theorem B1463951 : Blo 972592 1463951 := bstep (se 1 (by rfl) ⟨1097963, by rfl⟩ : syracuseStep 1463951 = 2195927) B2195927
theorem B1463993 : Blo 972592 1463993 := bstep (se 2 (by rfl) ⟨548997, by rfl⟩ : syracuseStep 1463993 = 1097995) B1097995
theorem B7919333 : Blo 972592 7919333 := bstep (se 4 (by rfl) ⟨742437, by rfl⟩ : syracuseStep 7919333 = 1484875) B1484875
theorem B1464071 : Blo 972592 1464071 := bstep (se 1 (by rfl) ⟨1098053, by rfl⟩ : syracuseStep 1464071 = 2196107) B2196107
theorem B1234703 : Blo 972592 1234703 := bstep (se 1 (by rfl) ⟨926027, by rfl⟩ : syracuseStep 1234703 = 1852055) B1852055
theorem B1759009 : Blo 972592 1759009 := bstep (se 2 (by rfl) ⟨659628, by rfl⟩ : syracuseStep 1759009 = 1319257) B1319257
theorem B1464107 : Blo 972592 1464107 := bstep (se 1 (by rfl) ⟨1098080, by rfl⟩ : syracuseStep 1464107 = 2196161) B2196161
theorem B972603 : Blo 972592 972603 := bstep (se 1 (by rfl) ⟨729452, by rfl⟩ : syracuseStep 972603 = 1458905) B1458905
theorem B1464137 : Blo 972592 1464137 := bstep (se 2 (by rfl) ⟨549051, by rfl⟩ : syracuseStep 1464137 = 1098103) B1098103
theorem B972679 : Blo 972592 972679 := bstep (se 1 (by rfl) ⟨729509, by rfl⟩ : syracuseStep 972679 = 1459019) B1459019
theorem B972687 : Blo 972592 972687 := bstep (se 1 (by rfl) ⟨729515, by rfl⟩ : syracuseStep 972687 = 1459031) B1459031
theorem B5855161 : Blo 972592 5855161 := bstep (se 2 (by rfl) ⟨2195685, by rfl⟩ : syracuseStep 5855161 = 4391371) B4391371
theorem B972731 : Blo 972592 972731 := bstep (se 1 (by rfl) ⟨729548, by rfl⟩ : syracuseStep 972731 = 1459097) B1459097
theorem B1464251 : Blo 972592 1464251 := bstep (se 1 (by rfl) ⟨1098188, by rfl⟩ : syracuseStep 1464251 = 2196377) B2196377
theorem B1464311 : Blo 972592 1464311 := bstep (se 1 (by rfl) ⟨1098233, by rfl⟩ : syracuseStep 1464311 = 2196467) B2196467
theorem B972807 : Blo 972592 972807 := bstep (se 1 (by rfl) ⟨729605, by rfl⟩ : syracuseStep 972807 = 1459211) B1459211
theorem B972815 : Blo 972592 972815 := bstep (se 1 (by rfl) ⟨729611, by rfl⟩ : syracuseStep 972815 = 1459223) B1459223
theorem B1464335 : Blo 972592 1464335 := bstep (se 1 (by rfl) ⟨1098251, by rfl⟩ : syracuseStep 1464335 = 2196503) B2196503
theorem B31610897 : Blo 972592 31610897 := bstep (se 2 (by rfl) ⟨11854086, by rfl⟩ : syracuseStep 31610897 = 23708173) B23708173
theorem B1464377 : Blo 972592 1464377 := bstep (se 2 (by rfl) ⟨549141, by rfl⟩ : syracuseStep 1464377 = 1098283) B1098283
theorem B972859 : Blo 972592 972859 := bstep (se 1 (by rfl) ⟨729644, by rfl⟩ : syracuseStep 972859 = 1459289) B1459289
theorem B3758147 : Blo 972592 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B1562743 : Blo 972592 1562743 := bstep (se 1 (by rfl) ⟨1172057, by rfl⟩ : syracuseStep 1562743 = 2344115) B2344115
theorem B7395461 : Blo 972592 7395461 := bstep (se 4 (by rfl) ⟨693324, by rfl⟩ : syracuseStep 7395461 = 1386649) B1386649
theorem B972935 : Blo 972592 972935 := bstep (se 1 (by rfl) ⟨729701, by rfl⟩ : syracuseStep 972935 = 1459403) B1459403
theorem B1464455 : Blo 972592 1464455 := bstep (se 1 (by rfl) ⟨1098341, by rfl⟩ : syracuseStep 1464455 = 2196683) B2196683
theorem B972943 : Blo 972592 972943 := bstep (se 1 (by rfl) ⟨729707, by rfl⟩ : syracuseStep 972943 = 1459415) B1459415
theorem B1464491 : Blo 972592 1464491 := bstep (se 1 (by rfl) ⟨1098368, by rfl⟩ : syracuseStep 1464491 = 2196737) B2196737
theorem B972987 : Blo 972592 972987 := bstep (se 1 (by rfl) ⟨729740, by rfl⟩ : syracuseStep 972987 = 1459481) B1459481
theorem B4937921 : Blo 972592 4937921 := bstep (se 2 (by rfl) ⟨1851720, by rfl⟩ : syracuseStep 4937921 = 3703441) B3703441
theorem B1464521 : Blo 972592 1464521 := bstep (se 2 (by rfl) ⟨549195, by rfl⟩ : syracuseStep 1464521 = 1098391) B1098391
theorem B973063 : Blo 972592 973063 := bstep (se 1 (by rfl) ⟨729797, by rfl⟩ : syracuseStep 973063 = 1459595) B1459595
theorem B973071 : Blo 972592 973071 := bstep (se 1 (by rfl) ⟨729803, by rfl⟩ : syracuseStep 973071 = 1459607) B1459607
theorem B973115 : Blo 972592 973115 := bstep (se 1 (by rfl) ⟨729836, by rfl⟩ : syracuseStep 973115 = 1459673) B1459673
theorem B1464635 : Blo 972592 1464635 := bstep (se 1 (by rfl) ⟨1098476, by rfl⟩ : syracuseStep 1464635 = 2196953) B2196953
theorem B1464695 : Blo 972592 1464695 := bstep (se 1 (by rfl) ⟨1098521, by rfl⟩ : syracuseStep 1464695 = 2197043) B2197043
theorem B973191 : Blo 972592 973191 := bstep (se 1 (by rfl) ⟨729893, by rfl⟩ : syracuseStep 973191 = 1459787) B1459787
theorem B973199 : Blo 972592 973199 := bstep (se 1 (by rfl) ⟨729899, by rfl⟩ : syracuseStep 973199 = 1459799) B1459799
theorem B1464719 : Blo 972592 1464719 := bstep (se 1 (by rfl) ⟨1098539, by rfl⟩ : syracuseStep 1464719 = 2197079) B2197079
theorem B5560721 : Blo 972592 5560721 := bstep (se 2 (by rfl) ⟨2085270, by rfl⟩ : syracuseStep 5560721 = 4170541) B4170541
theorem B1464761 : Blo 972592 1464761 := bstep (se 2 (by rfl) ⟨549285, by rfl⟩ : syracuseStep 1464761 = 1098571) B1098571
theorem B973243 : Blo 972592 973243 := bstep (se 1 (by rfl) ⟨729932, by rfl⟩ : syracuseStep 973243 = 1459865) B1459865
theorem B973319 : Blo 972592 973319 := bstep (se 1 (by rfl) ⟨729989, by rfl⟩ : syracuseStep 973319 = 1459979) B1459979
theorem B1464839 : Blo 972592 1464839 := bstep (se 1 (by rfl) ⟨1098629, by rfl⟩ : syracuseStep 1464839 = 2197259) B2197259
theorem B973327 : Blo 972592 973327 := bstep (se 1 (by rfl) ⟨729995, by rfl⟩ : syracuseStep 973327 = 1459991) B1459991
theorem B1464875 : Blo 972592 1464875 := bstep (se 1 (by rfl) ⟨1098656, by rfl⟩ : syracuseStep 1464875 = 2197313) B2197313
theorem B973371 : Blo 972592 973371 := bstep (se 1 (by rfl) ⟨730028, by rfl⟩ : syracuseStep 973371 = 1460057) B1460057
theorem B973447 : Blo 972592 973447 := bstep (se 1 (by rfl) ⟨730085, by rfl⟩ : syracuseStep 973447 = 1460171) B1460171
theorem B973455 : Blo 972592 973455 := bstep (se 1 (by rfl) ⟨730091, by rfl⟩ : syracuseStep 973455 = 1460183) B1460183
theorem B973499 : Blo 972592 973499 := bstep (se 1 (by rfl) ⟨730124, by rfl⟩ : syracuseStep 973499 = 1460249) B1460249
theorem B973575 : Blo 972592 973575 := bstep (se 1 (by rfl) ⟨730181, by rfl⟩ : syracuseStep 973575 = 1460363) B1460363
theorem B973583 : Blo 972592 973583 := bstep (se 1 (by rfl) ⟨730187, by rfl⟩ : syracuseStep 973583 = 1460375) B1460375
theorem B973627 : Blo 972592 973627 := bstep (se 1 (by rfl) ⟨730220, by rfl⟩ : syracuseStep 973627 = 1460441) B1460441
theorem B5266235 : Blo 972592 5266235 := bstep (se 1 (by rfl) ⟨3949676, by rfl⟩ : syracuseStep 5266235 = 7899353) B7899353
theorem B4742003 : Blo 972592 4742003 := bstep (se 1 (by rfl) ⟨3556502, by rfl⟩ : syracuseStep 4742003 = 7113005) B7113005
theorem B973703 : Blo 972592 973703 := bstep (se 1 (by rfl) ⟨730277, by rfl⟩ : syracuseStep 973703 = 1460555) B1460555
theorem B973711 : Blo 972592 973711 := bstep (se 1 (by rfl) ⟨730283, by rfl⟩ : syracuseStep 973711 = 1460567) B1460567
theorem B3562393 : Blo 972592 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B973755 : Blo 972592 973755 := bstep (se 1 (by rfl) ⟨730316, by rfl⟩ : syracuseStep 973755 = 1460633) B1460633
theorem B973831 : Blo 972592 973831 := bstep (se 1 (by rfl) ⟨730373, by rfl⟩ : syracuseStep 973831 = 1460747) B1460747
theorem B973839 : Blo 972592 973839 := bstep (se 1 (by rfl) ⟨730379, by rfl⟩ : syracuseStep 973839 = 1460759) B1460759
theorem B973883 : Blo 972592 973883 := bstep (se 1 (by rfl) ⟨730412, by rfl⟩ : syracuseStep 973883 = 1460825) B1460825
theorem B2776123 : Blo 972592 2776123 := bstep (se 1 (by rfl) ⟨2082092, by rfl⟩ : syracuseStep 2776123 = 4164185) B4164185
theorem B5561405 : Blo 972592 5561405 := bstep (se 3 (by rfl) ⟨1042763, by rfl⟩ : syracuseStep 5561405 = 2085527) B2085527
theorem B973959 : Blo 972592 973959 := bstep (se 1 (by rfl) ⟨730469, by rfl⟩ : syracuseStep 973959 = 1460939) B1460939
theorem B973967 : Blo 972592 973967 := bstep (se 1 (by rfl) ⟨730475, by rfl⟩ : syracuseStep 973967 = 1460951) B1460951
theorem B974011 : Blo 972592 974011 := bstep (se 1 (by rfl) ⟨730508, by rfl⟩ : syracuseStep 974011 = 1461017) B1461017
theorem B974087 : Blo 972592 974087 := bstep (se 1 (by rfl) ⟨730565, by rfl⟩ : syracuseStep 974087 = 1461131) B1461131
theorem B974095 : Blo 972592 974095 := bstep (se 1 (by rfl) ⟨730571, by rfl⟩ : syracuseStep 974095 = 1461143) B1461143
theorem B974139 : Blo 972592 974139 := bstep (se 1 (by rfl) ⟨730604, by rfl⟩ : syracuseStep 974139 = 1461209) B1461209
theorem B974215 : Blo 972592 974215 := bstep (se 1 (by rfl) ⟨730661, by rfl⟩ : syracuseStep 974215 = 1461323) B1461323
theorem B974223 : Blo 972592 974223 := bstep (se 1 (by rfl) ⟨730667, by rfl⟩ : syracuseStep 974223 = 1461335) B1461335
theorem B974267 : Blo 972592 974267 := bstep (se 1 (by rfl) ⟨730700, by rfl⟩ : syracuseStep 974267 = 1461401) B1461401
theorem B13360589 : Blo 972592 13360589 := bstep (se 3 (by rfl) ⟨2505110, by rfl⟩ : syracuseStep 13360589 = 5010221) B5010221
theorem B4939217 : Blo 972592 4939217 := bstep (se 2 (by rfl) ⟨1852206, by rfl⟩ : syracuseStep 4939217 = 3704413) B3704413
theorem B974343 : Blo 972592 974343 := bstep (se 1 (by rfl) ⟨730757, by rfl⟩ : syracuseStep 974343 = 1461515) B1461515
theorem B974351 : Blo 972592 974351 := bstep (se 1 (by rfl) ⟨730763, by rfl⟩ : syracuseStep 974351 = 1461527) B1461527
theorem B974395 : Blo 972592 974395 := bstep (se 1 (by rfl) ⟨730796, by rfl⟩ : syracuseStep 974395 = 1461593) B1461593
theorem B974471 : Blo 972592 974471 := bstep (se 1 (by rfl) ⟨730853, by rfl⟩ : syracuseStep 974471 = 1461707) B1461707
theorem B974479 : Blo 972592 974479 := bstep (se 1 (by rfl) ⟨730859, by rfl⟩ : syracuseStep 974479 = 1461719) B1461719
theorem B974523 : Blo 972592 974523 := bstep (se 1 (by rfl) ⟨730892, by rfl⟩ : syracuseStep 974523 = 1461785) B1461785
theorem B974599 : Blo 972592 974599 := bstep (se 1 (by rfl) ⟨730949, by rfl⟩ : syracuseStep 974599 = 1461899) B1461899
theorem B974607 : Blo 972592 974607 := bstep (se 1 (by rfl) ⟨730955, by rfl⟩ : syracuseStep 974607 = 1461911) B1461911
theorem B974651 : Blo 972592 974651 := bstep (se 1 (by rfl) ⟨730988, by rfl⟩ : syracuseStep 974651 = 1461977) B1461977
theorem B6250355 : Blo 972592 6250355 := bstep (se 1 (by rfl) ⟨4687766, by rfl⟩ : syracuseStep 6250355 = 9375533) B9375533
theorem B974727 : Blo 972592 974727 := bstep (se 1 (by rfl) ⟨731045, by rfl⟩ : syracuseStep 974727 = 1462091) B1462091
theorem B2776967 : Blo 972592 2776967 := bstep (se 1 (by rfl) ⟨2082725, by rfl⟩ : syracuseStep 2776967 = 4165451) B4165451
theorem B974735 : Blo 972592 974735 := bstep (se 1 (by rfl) ⟨731051, by rfl⟩ : syracuseStep 974735 = 1462103) B1462103
theorem B5627801 : Blo 972592 5627801 := bstep (se 2 (by rfl) ⟨2110425, by rfl⟩ : syracuseStep 5627801 = 4220851) B4220851
theorem B974779 : Blo 972592 974779 := bstep (se 1 (by rfl) ⟨731084, by rfl⟩ : syracuseStep 974779 = 1462169) B1462169
theorem B974855 : Blo 972592 974855 := bstep (se 1 (by rfl) ⟨731141, by rfl⟩ : syracuseStep 974855 = 1462283) B1462283
theorem B974863 : Blo 972592 974863 := bstep (se 1 (by rfl) ⟨731147, by rfl⟩ : syracuseStep 974863 = 1462295) B1462295
theorem B974907 : Blo 972592 974907 := bstep (se 1 (by rfl) ⟨731180, by rfl⟩ : syracuseStep 974907 = 1462361) B1462361
theorem B3694679 : Blo 972592 3694679 := bstep (se 1 (by rfl) ⟨2771009, by rfl⟩ : syracuseStep 3694679 = 5542019) B5542019
theorem B6250583 : Blo 972592 6250583 := bstep (se 1 (by rfl) ⟨4687937, by rfl⟩ : syracuseStep 6250583 = 9375875) B9375875
theorem B974983 : Blo 972592 974983 := bstep (se 1 (by rfl) ⟨731237, by rfl⟩ : syracuseStep 974983 = 1462475) B1462475
theorem B974991 : Blo 972592 974991 := bstep (se 1 (by rfl) ⟨731243, by rfl⟩ : syracuseStep 974991 = 1462487) B1462487
theorem B975035 : Blo 972592 975035 := bstep (se 1 (by rfl) ⟨731276, by rfl⟩ : syracuseStep 975035 = 1462553) B1462553
theorem B975111 : Blo 972592 975111 := bstep (se 1 (by rfl) ⟨731333, by rfl⟩ : syracuseStep 975111 = 1462667) B1462667
theorem B975119 : Blo 972592 975119 := bstep (se 1 (by rfl) ⟨731339, by rfl⟩ : syracuseStep 975119 = 1462679) B1462679
theorem B975163 : Blo 972592 975163 := bstep (se 1 (by rfl) ⟨731372, by rfl⟩ : syracuseStep 975163 = 1462745) B1462745
theorem B975239 : Blo 972592 975239 := bstep (se 1 (by rfl) ⟨731429, by rfl⟩ : syracuseStep 975239 = 1462859) B1462859
theorem B975247 : Blo 972592 975247 := bstep (se 1 (by rfl) ⟨731435, by rfl⟩ : syracuseStep 975247 = 1462871) B1462871
theorem B975291 : Blo 972592 975291 := bstep (se 1 (by rfl) ⟨731468, by rfl⟩ : syracuseStep 975291 = 1462937) B1462937
theorem B7397891 : Blo 972592 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B975367 : Blo 972592 975367 := bstep (se 1 (by rfl) ⟨731525, by rfl⟩ : syracuseStep 975367 = 1463051) B1463051
theorem B975375 : Blo 972592 975375 := bstep (se 1 (by rfl) ⟨731531, by rfl⟩ : syracuseStep 975375 = 1463063) B1463063
theorem B975419 : Blo 972592 975419 := bstep (se 1 (by rfl) ⟨731564, by rfl⟩ : syracuseStep 975419 = 1463129) B1463129
theorem B3695165 : Blo 972592 3695165 := bstep (se 3 (by rfl) ⟨692843, by rfl⟩ : syracuseStep 3695165 = 1385687) B1385687
theorem B975495 : Blo 972592 975495 := bstep (se 1 (by rfl) ⟨731621, by rfl⟩ : syracuseStep 975495 = 1463243) B1463243
theorem B975503 : Blo 972592 975503 := bstep (se 1 (by rfl) ⟨731627, by rfl⟩ : syracuseStep 975503 = 1463255) B1463255
theorem B2777753 : Blo 972592 2777753 := bstep (se 2 (by rfl) ⟨1041657, by rfl⟩ : syracuseStep 2777753 = 2083315) B2083315
theorem B975547 : Blo 972592 975547 := bstep (se 1 (by rfl) ⟨731660, by rfl⟩ : syracuseStep 975547 = 1463321) B1463321
theorem B1172215 : Blo 972592 1172215 := bstep (se 1 (by rfl) ⟨879161, by rfl⟩ : syracuseStep 1172215 = 1758323) B1758323
theorem B975623 : Blo 972592 975623 := bstep (se 1 (by rfl) ⟨731717, by rfl⟩ : syracuseStep 975623 = 1463435) B1463435
theorem B975631 : Blo 972592 975631 := bstep (se 1 (by rfl) ⟨731723, by rfl⟩ : syracuseStep 975631 = 1463447) B1463447
theorem B975675 : Blo 972592 975675 := bstep (se 1 (by rfl) ⟨731756, by rfl⟩ : syracuseStep 975675 = 1463513) B1463513
theorem B975751 : Blo 972592 975751 := bstep (se 1 (by rfl) ⟨731813, by rfl⟩ : syracuseStep 975751 = 1463627) B1463627
theorem B975759 : Blo 972592 975759 := bstep (se 1 (by rfl) ⟨731819, by rfl⟩ : syracuseStep 975759 = 1463639) B1463639
theorem B975803 : Blo 972592 975803 := bstep (se 1 (by rfl) ⟨731852, by rfl⟩ : syracuseStep 975803 = 1463705) B1463705
theorem B975879 : Blo 972592 975879 := bstep (se 1 (by rfl) ⟨731909, by rfl⟩ : syracuseStep 975879 = 1463819) B1463819
theorem B975887 : Blo 972592 975887 := bstep (se 1 (by rfl) ⟨731915, by rfl⟩ : syracuseStep 975887 = 1463831) B1463831
theorem B975931 : Blo 972592 975931 := bstep (se 1 (by rfl) ⟨731948, by rfl⟩ : syracuseStep 975931 = 1463897) B1463897
theorem B976007 : Blo 972592 976007 := bstep (se 1 (by rfl) ⟨732005, by rfl⟩ : syracuseStep 976007 = 1464011) B1464011
theorem B976015 : Blo 972592 976015 := bstep (se 1 (by rfl) ⟨732011, by rfl⟩ : syracuseStep 976015 = 1464023) B1464023
theorem B976059 : Blo 972592 976059 := bstep (se 1 (by rfl) ⟨732044, by rfl⟩ : syracuseStep 976059 = 1464089) B1464089
theorem B976135 : Blo 972592 976135 := bstep (se 1 (by rfl) ⟨732101, by rfl⟩ : syracuseStep 976135 = 1464203) B1464203
theorem B976143 : Blo 972592 976143 := bstep (se 1 (by rfl) ⟨732107, by rfl⟩ : syracuseStep 976143 = 1464215) B1464215
theorem B2778401 : Blo 972592 2778401 := bstep (se 2 (by rfl) ⟨1041900, by rfl⟩ : syracuseStep 2778401 = 2083801) B2083801
theorem B976187 : Blo 972592 976187 := bstep (se 1 (by rfl) ⟨732140, by rfl⟩ : syracuseStep 976187 = 1464281) B1464281
theorem B976263 : Blo 972592 976263 := bstep (se 1 (by rfl) ⟨732197, by rfl⟩ : syracuseStep 976263 = 1464395) B1464395
theorem B976271 : Blo 972592 976271 := bstep (se 1 (by rfl) ⟨732203, by rfl⟩ : syracuseStep 976271 = 1464407) B1464407
theorem B2188691 : Blo 972592 2188691 := bstep (se 1 (by rfl) ⟨1641518, by rfl⟩ : syracuseStep 2188691 = 3283037) B3283037
theorem B976315 : Blo 972592 976315 := bstep (se 1 (by rfl) ⟨732236, by rfl⟩ : syracuseStep 976315 = 1464473) B1464473
theorem B2188745 : Blo 972592 2188745 := bstep (se 2 (by rfl) ⟨820779, by rfl⟩ : syracuseStep 2188745 = 1641559) B1641559
theorem B976391 : Blo 972592 976391 := bstep (se 1 (by rfl) ⟨732293, by rfl⟩ : syracuseStep 976391 = 1464587) B1464587
theorem B4941323 : Blo 972592 4941323 := bstep (se 1 (by rfl) ⟨3705992, by rfl⟩ : syracuseStep 4941323 = 7411985) B7411985
theorem B976399 : Blo 972592 976399 := bstep (se 1 (by rfl) ⟨732299, by rfl⟩ : syracuseStep 976399 = 1464599) B1464599
theorem B976443 : Blo 972592 976443 := bstep (se 1 (by rfl) ⟨732332, by rfl⟩ : syracuseStep 976443 = 1464665) B1464665
theorem B976519 : Blo 972592 976519 := bstep (se 1 (by rfl) ⟨732389, by rfl⟩ : syracuseStep 976519 = 1464779) B1464779
theorem B976527 : Blo 972592 976527 := bstep (se 1 (by rfl) ⟨732395, by rfl⟩ : syracuseStep 976527 = 1464791) B1464791
theorem B4941485 : Blo 972592 4941485 := bstep (se 3 (by rfl) ⟨926528, by rfl⟩ : syracuseStep 4941485 = 1853057) B1853057
theorem B976571 : Blo 972592 976571 := bstep (se 1 (by rfl) ⟨732428, by rfl⟩ : syracuseStep 976571 = 1464857) B1464857
theorem B1042183 : Blo 972592 1042183 := bstep (se 1 (by rfl) ⟨781637, by rfl⟩ : syracuseStep 1042183 = 1563275) B1563275
theorem B2222095 : Blo 972592 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B4155421 : Blo 972592 4155421 := bstep (se 3 (by rfl) ⟨779141, by rfl⟩ : syracuseStep 4155421 = 1558283) B1558283
theorem B11855933 : Blo 972592 11855933 := bstep (se 3 (by rfl) ⟨2222987, by rfl⟩ : syracuseStep 11855933 = 4445975) B4445975
theorem B5007427 : Blo 972592 5007427 := bstep (se 1 (by rfl) ⟨3755570, by rfl⟩ : syracuseStep 5007427 = 7511141) B7511141
theorem B2189447 : Blo 972592 2189447 := bstep (se 1 (by rfl) ⟨1642085, by rfl⟩ : syracuseStep 2189447 = 3284171) B3284171
theorem B2779393 : Blo 972592 2779393 := bstep (se 2 (by rfl) ⟨1042272, by rfl⟩ : syracuseStep 2779393 = 2084545) B2084545
theorem B3696911 : Blo 972592 3696911 := bstep (se 1 (by rfl) ⟨2772683, by rfl⟩ : syracuseStep 3696911 = 5545367) B5545367
theorem B2189627 : Blo 972592 2189627 := bstep (se 1 (by rfl) ⟨1642220, by rfl⟩ : syracuseStep 2189627 = 3284441) B3284441
theorem B2189753 : Blo 972592 2189753 := bstep (se 2 (by rfl) ⟨821157, by rfl⟩ : syracuseStep 2189753 = 1642315) B1642315
theorem B11102669 : Blo 972592 11102669 := bstep (se 3 (by rfl) ⟨2081750, by rfl⟩ : syracuseStep 11102669 = 4163501) B4163501
theorem B2190095 : Blo 972592 2190095 := bstep (se 1 (by rfl) ⟨1642571, by rfl⟩ : syracuseStep 2190095 = 3285143) B3285143
theorem B2190113 : Blo 972592 2190113 := bstep (se 2 (by rfl) ⟨821292, by rfl⟩ : syracuseStep 2190113 = 1642585) B1642585
theorem B9988913 : Blo 972592 9988913 := bstep (se 2 (by rfl) ⟨3745842, by rfl⟩ : syracuseStep 9988913 = 7491685) B7491685
theorem B2190455 : Blo 972592 2190455 := bstep (se 1 (by rfl) ⟨1642841, by rfl⟩ : syracuseStep 2190455 = 3285683) B3285683
theorem B4943105 : Blo 972592 4943105 := bstep (se 2 (by rfl) ⟨1853664, by rfl⟩ : syracuseStep 4943105 = 3707329) B3707329
theorem B2190635 : Blo 972592 2190635 := bstep (se 1 (by rfl) ⟨1642976, by rfl⟩ : syracuseStep 2190635 = 3285953) B3285953
theorem B3566963 : Blo 972592 3566963 := bstep (se 1 (by rfl) ⟨2675222, by rfl⟩ : syracuseStep 3566963 = 5350445) B5350445
theorem B2223545 : Blo 972592 2223545 := bstep (se 2 (by rfl) ⟨833829, by rfl⟩ : syracuseStep 2223545 = 1667659) B1667659
theorem B4746755 : Blo 972592 4746755 := bstep (se 1 (by rfl) ⟨3560066, by rfl⟩ : syracuseStep 4746755 = 7120133) B7120133
theorem B2190995 : Blo 972592 2190995 := bstep (se 1 (by rfl) ⟨1643246, by rfl⟩ : syracuseStep 2190995 = 3286493) B3286493
theorem B6254273 : Blo 972592 6254273 := bstep (se 2 (by rfl) ⟨2345352, by rfl⟩ : syracuseStep 6254273 = 4690705) B4690705
theorem B2191049 : Blo 972592 2191049 := bstep (se 2 (by rfl) ⟨821643, by rfl⟩ : syracuseStep 2191049 = 1643287) B1643287
theorem B3337985 : Blo 972592 3337985 := bstep (se 2 (by rfl) ⟨1251744, by rfl⟩ : syracuseStep 3337985 = 2503489) B2503489
theorem B3698567 : Blo 972592 3698567 := bstep (se 1 (by rfl) ⟨2773925, by rfl⟩ : syracuseStep 3698567 = 5547851) B5547851
theorem B4943915 : Blo 972592 4943915 := bstep (se 1 (by rfl) ⟨3707936, by rfl⟩ : syracuseStep 4943915 = 7415873) B7415873
theorem B7893125 : Blo 972592 7893125 := bstep (se 4 (by rfl) ⟨739980, by rfl⟩ : syracuseStep 7893125 = 1479961) B1479961
theorem B2191751 : Blo 972592 2191751 := bstep (se 1 (by rfl) ⟨1643813, by rfl⟩ : syracuseStep 2191751 = 3287627) B3287627
theorem B37515797 : Blo 972592 37515797 := bstep (se 6 (by rfl) ⟨879276, by rfl⟩ : syracuseStep 37515797 = 1758553) B1758553
theorem B2191931 : Blo 972592 2191931 := bstep (se 1 (by rfl) ⟨1643948, by rfl⟩ : syracuseStep 2191931 = 3287897) B3287897
theorem B2192057 : Blo 972592 2192057 := bstep (se 2 (by rfl) ⟨822021, by rfl⟩ : syracuseStep 2192057 = 1644043) B1644043
theorem B1340345 : Blo 972592 1340345 := bstep (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) B1005259
theorem B2192399 : Blo 972592 2192399 := bstep (se 1 (by rfl) ⟨1644299, by rfl⟩ : syracuseStep 2192399 = 3288599) B3288599
theorem B2192417 : Blo 972592 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B3339325 : Blo 972592 3339325 := bstep (se 3 (by rfl) ⟨626123, by rfl⟩ : syracuseStep 3339325 = 1252247) B1252247
theorem B2815319 : Blo 972592 2815319 := bstep (se 1 (by rfl) ⟨2111489, by rfl⟩ : syracuseStep 2815319 = 4222979) B4222979
theorem B2192759 : Blo 972592 2192759 := bstep (se 1 (by rfl) ⟨1644569, by rfl⟩ : syracuseStep 2192759 = 3289139) B3289139
theorem B8320441 : Blo 972592 8320441 := bstep (se 2 (by rfl) ⟨3120165, by rfl⟩ : syracuseStep 8320441 = 6240331) B6240331
theorem B2192939 : Blo 972592 2192939 := bstep (se 1 (by rfl) ⟨1644704, by rfl⟩ : syracuseStep 2192939 = 3289409) B3289409
theorem B3700343 : Blo 972592 3700343 := bstep (se 1 (by rfl) ⟨2775257, by rfl⟩ : syracuseStep 3700343 = 5550515) B5550515
theorem B7403237 : Blo 972592 7403237 := bstep (se 4 (by rfl) ⟨694053, by rfl⟩ : syracuseStep 7403237 = 1388107) B1388107
theorem B2193299 : Blo 972592 2193299 := bstep (se 1 (by rfl) ⟨1644974, by rfl⟩ : syracuseStep 2193299 = 3289949) B3289949
theorem B2193353 : Blo 972592 2193353 := bstep (se 2 (by rfl) ⟨822507, by rfl⟩ : syracuseStep 2193353 = 1645015) B1645015
theorem B18741293 : Blo 972592 18741293 := bstep (se 3 (by rfl) ⟨3513992, by rfl⟩ : syracuseStep 18741293 = 7027985) B7027985
theorem B2816059 : Blo 972592 2816059 := bstep (se 1 (by rfl) ⟨2112044, by rfl⟩ : syracuseStep 2816059 = 4224089) B4224089
theorem B3701315 : Blo 972592 3701315 := bstep (se 1 (by rfl) ⟨2775986, by rfl⟩ : syracuseStep 3701315 = 5551973) B5551973
theorem B4160119 : Blo 972592 4160119 := bstep (se 1 (by rfl) ⟨3120089, by rfl⟩ : syracuseStep 4160119 = 6240179) B6240179
theorem B2194055 : Blo 972592 2194055 := bstep (se 1 (by rfl) ⟨1645541, by rfl⟩ : syracuseStep 2194055 = 3291083) B3291083
theorem B2194235 : Blo 972592 2194235 := bstep (se 1 (by rfl) ⟨1645676, by rfl⟩ : syracuseStep 2194235 = 3291353) B3291353
theorem B4684691 : Blo 972592 4684691 := bstep (se 1 (by rfl) ⟨3513518, by rfl⟩ : syracuseStep 4684691 = 7027037) B7027037
theorem B2194361 : Blo 972592 2194361 := bstep (se 2 (by rfl) ⟨822885, by rfl⟩ : syracuseStep 2194361 = 1645771) B1645771
theorem B3701771 : Blo 972592 3701771 := bstep (se 1 (by rfl) ⟨2776328, by rfl⟩ : syracuseStep 3701771 = 5552657) B5552657
theorem B35552317 : Blo 972592 35552317 := bstep (se 3 (by rfl) ⟨6666059, by rfl⟩ : syracuseStep 35552317 = 13332119) B13332119
theorem B2194703 : Blo 972592 2194703 := bstep (se 1 (by rfl) ⟨1646027, by rfl⟩ : syracuseStep 2194703 = 3292055) B3292055
theorem B2194721 : Blo 972592 2194721 := bstep (se 2 (by rfl) ⟨823020, by rfl⟩ : syracuseStep 2194721 = 1646041) B1646041
theorem B11992541 : Blo 972592 11992541 := bstep (se 3 (by rfl) ⟨2248601, by rfl⟩ : syracuseStep 11992541 = 4497203) B4497203
theorem B2195063 : Blo 972592 2195063 := bstep (se 1 (by rfl) ⟨1646297, by rfl⟩ : syracuseStep 2195063 = 3292595) B3292595
theorem B2195243 : Blo 972592 2195243 := bstep (se 1 (by rfl) ⟨1646432, by rfl⟩ : syracuseStep 2195243 = 3292865) B3292865
theorem B1409033 : Blo 972592 1409033 := bstep (se 2 (by rfl) ⟨528387, by rfl⟩ : syracuseStep 1409033 = 1056775) B1056775
theorem B2195513 : Blo 972592 2195513 := bstep (se 2 (by rfl) ⟨823317, by rfl⟩ : syracuseStep 2195513 = 1646635) B1646635
theorem B3702941 : Blo 972592 3702941 := bstep (se 3 (by rfl) ⟨694301, by rfl⟩ : syracuseStep 3702941 = 1388603) B1388603
theorem B3702955 : Blo 972592 3702955 := bstep (se 1 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 3702955 = 5554433) B5554433
theorem B26706277 : Blo 972592 26706277 := bstep (se 4 (by rfl) ⟨2503713, by rfl⟩ : syracuseStep 26706277 = 5007427) B5007427
theorem B2195855 : Blo 972592 2195855 := bstep (se 1 (by rfl) ⟨1646891, by rfl⟩ : syracuseStep 2195855 = 3293783) B3293783
theorem B3703259 : Blo 972592 3703259 := bstep (se 1 (by rfl) ⟨2777444, by rfl⟩ : syracuseStep 3703259 = 5554889) B5554889
theorem B9372185 : Blo 972592 9372185 := bstep (se 2 (by rfl) ⟨3514569, by rfl⟩ : syracuseStep 9372185 = 7029139) B7029139
theorem B2196179 : Blo 972592 2196179 := bstep (se 1 (by rfl) ⟨1647134, by rfl⟩ : syracuseStep 2196179 = 3294269) B3294269
theorem B14025473 : Blo 972592 14025473 := bstep (se 2 (by rfl) ⟨5259552, by rfl⟩ : syracuseStep 14025473 = 10519105) B10519105
theorem B4687247 : Blo 972592 4687247 := bstep (se 1 (by rfl) ⟨3515435, by rfl⟩ : syracuseStep 4687247 = 7030871) B7030871
theorem B2197115 : Blo 972592 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B2197241 : Blo 972592 2197241 := bstep (se 2 (by rfl) ⟨823965, by rfl⟩ : syracuseStep 2197241 = 1647931) B1647931
theorem B28149767 : Blo 972592 28149767 := bstep (se 1 (by rfl) ⟨21112325, by rfl⟩ : syracuseStep 28149767 = 42224651) B42224651
theorem B1903031 : Blo 972592 1903031 := bstep (se 1 (by rfl) ⟨1427273, by rfl⟩ : syracuseStep 1903031 = 2854547) B2854547
theorem B3574253 : Blo 972592 3574253 := bstep (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) B1340345
theorem B5704225 : Blo 972592 5704225 := bstep (se 2 (by rfl) ⟨2139084, by rfl⟩ : syracuseStep 5704225 = 4278169) B4278169
theorem B5540561 : Blo 972592 5540561 := bstep (se 2 (by rfl) ⟨2077710, by rfl⟩ : syracuseStep 5540561 = 4155421) B4155421
theorem B1641289 : Blo 972592 1641289 := bstep (se 2 (by rfl) ⟨615483, by rfl⟩ : syracuseStep 1641289 = 1230967) B1230967
theorem B1641323 : Blo 972592 1641323 := bstep (se 1 (by rfl) ⟨1230992, by rfl⟩ : syracuseStep 1641323 = 2461985) B2461985
theorem B4164527 : Blo 972592 4164527 := bstep (se 1 (by rfl) ⟨3123395, by rfl⟩ : syracuseStep 4164527 = 6246791) B6246791
theorem B3705857 : Blo 972592 3705857 := bstep (se 2 (by rfl) ⟨1389696, by rfl⟩ : syracuseStep 3705857 = 2779393) B2779393
theorem B3705871 : Blo 972592 3705871 := bstep (se 1 (by rfl) ⟨2779403, by rfl⟩ : syracuseStep 3705871 = 5558807) B5558807
theorem B3509495 : Blo 972592 3509495 := bstep (se 1 (by rfl) ⟨2632121, by rfl⟩ : syracuseStep 3509495 = 5264243) B5264243
theorem B1641721 : Blo 972592 1641721 := bstep (se 2 (by rfl) ⟨615645, by rfl⟩ : syracuseStep 1641721 = 1231291) B1231291
theorem B7409069 : Blo 972592 7409069 := bstep (se 3 (by rfl) ⟨1389200, by rfl⟩ : syracuseStep 7409069 = 2778401) B2778401
theorem B14061043 : Blo 972592 14061043 := bstep (se 1 (by rfl) ⟨10545782, by rfl⟩ : syracuseStep 14061043 = 21091565) B21091565
theorem B1641991 : Blo 972592 1641991 := bstep (se 1 (by rfl) ⟨1231493, by rfl⟩ : syracuseStep 1641991 = 2462987) B2462987
theorem B5279555 : Blo 972592 5279555 := bstep (se 1 (by rfl) ⟨3959666, by rfl⟩ : syracuseStep 5279555 = 7919333) B7919333
theorem B1642423 : Blo 972592 1642423 := bstep (se 1 (by rfl) ⟨1231817, by rfl⟩ : syracuseStep 1642423 = 2463635) B2463635
theorem B21073931 : Blo 972592 21073931 := bstep (se 1 (by rfl) ⟨15805448, by rfl⟩ : syracuseStep 21073931 = 31610897) B31610897
theorem B1642619 : Blo 972592 1642619 := bstep (se 1 (by rfl) ⟨1231964, by rfl⟩ : syracuseStep 1642619 = 2463929) B2463929
theorem B3707147 : Blo 972592 3707147 := bstep (se 1 (by rfl) ⟨2780360, by rfl⟩ : syracuseStep 3707147 = 5560721) B5560721
theorem B1643017 : Blo 972592 1643017 := bstep (se 2 (by rfl) ⟨616131, by rfl⟩ : syracuseStep 1643017 = 1232263) B1232263
theorem B3510823 : Blo 972592 3510823 := bstep (se 1 (by rfl) ⟨2633117, by rfl⟩ : syracuseStep 3510823 = 5266235) B5266235
theorem B1643179 : Blo 972592 1643179 := bstep (se 1 (by rfl) ⟨1232384, by rfl⟩ : syracuseStep 1643179 = 2464769) B2464769
theorem B3707603 : Blo 972592 3707603 := bstep (se 1 (by rfl) ⟨2780702, by rfl⟩ : syracuseStep 3707603 = 5561405) B5561405
theorem B1643483 : Blo 972592 1643483 := bstep (se 1 (by rfl) ⟨1232612, by rfl⟩ : syracuseStep 1643483 = 2465225) B2465225
theorem B7017491 : Blo 972592 7017491 := bstep (se 1 (by rfl) ⟨5263118, by rfl⟩ : syracuseStep 7017491 = 10526237) B10526237
theorem B11998259 : Blo 972592 11998259 := bstep (se 1 (by rfl) ⟨8998694, by rfl⟩ : syracuseStep 11998259 = 17997389) B17997389
theorem B1643719 : Blo 972592 1643719 := bstep (se 1 (by rfl) ⟨1232789, by rfl⟩ : syracuseStep 1643719 = 2465579) B2465579
theorem B35493065 : Blo 972592 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B4166903 : Blo 972592 4166903 := bstep (se 1 (by rfl) ⟨3125177, by rfl⟩ : syracuseStep 4166903 = 6250355) B6250355
theorem B1316191 : Blo 972592 1316191 := bstep (se 1 (by rfl) ⟨987143, by rfl⟩ : syracuseStep 1316191 = 1974287) B1974287
theorem B26645861 : Blo 972592 26645861 := bstep (se 4 (by rfl) ⟨2498049, by rfl⟩ : syracuseStep 26645861 = 4996099) B4996099
theorem B1643881 : Blo 972592 1643881 := bstep (se 2 (by rfl) ⟨616455, by rfl⟩ : syracuseStep 1643881 = 1232911) B1232911
theorem B2463119 : Blo 972592 2463119 := bstep (se 1 (by rfl) ⟨1847339, by rfl⟩ : syracuseStep 2463119 = 3694679) B3694679
theorem B4167055 : Blo 972592 4167055 := bstep (se 1 (by rfl) ⟨3125291, by rfl⟩ : syracuseStep 4167055 = 6250583) B6250583
theorem B45618785 : Blo 972592 45618785 := bstep (se 2 (by rfl) ⟨17107044, by rfl⟩ : syracuseStep 45618785 = 34214089) B34214089
theorem B2463443 : Blo 972592 2463443 := bstep (se 1 (by rfl) ⟨1847582, by rfl⟩ : syracuseStep 2463443 = 3695165) B3695165
theorem B7411499 : Blo 972592 7411499 := bstep (se 1 (by rfl) ⟨5558624, by rfl⟩ : syracuseStep 7411499 = 11117249) B11117249
theorem B3282875 : Blo 972592 3282875 := bstep (se 1 (by rfl) ⟨2462156, by rfl⟩ : syracuseStep 3282875 = 4924313) B4924313
theorem B1644475 : Blo 972592 1644475 := bstep (se 1 (by rfl) ⟨1233356, by rfl⟩ : syracuseStep 1644475 = 2466713) B2466713
theorem B1644583 : Blo 972592 1644583 := bstep (se 1 (by rfl) ⟨1233437, by rfl⟩ : syracuseStep 1644583 = 2466875) B2466875
theorem B1644907 : Blo 972592 1644907 := bstep (se 1 (by rfl) ⟨1233680, by rfl⟩ : syracuseStep 1644907 = 2467361) B2467361
theorem B7903955 : Blo 972592 7903955 := bstep (se 1 (by rfl) ⟨5927966, by rfl⟩ : syracuseStep 7903955 = 11855933) B11855933
theorem B2464607 : Blo 972592 2464607 := bstep (se 1 (by rfl) ⟨1848455, by rfl⟩ : syracuseStep 2464607 = 3696911) B3696911
theorem B6659275 : Blo 972592 6659275 := bstep (se 1 (by rfl) ⟨4994456, by rfl⟩ : syracuseStep 6659275 = 9988913) B9988913
theorem B1645967 : Blo 972592 1645967 := bstep (se 1 (by rfl) ⟨1234475, by rfl⟩ : syracuseStep 1645967 = 2468951) B2468951
theorem B3284603 : Blo 972592 3284603 := bstep (se 1 (by rfl) ⟨2463452, by rfl⟩ : syracuseStep 3284603 = 4926905) B4926905
theorem B1646203 : Blo 972592 1646203 := bstep (se 1 (by rfl) ⟨1234652, by rfl⟩ : syracuseStep 1646203 = 2469305) B2469305
theorem B3284765 : Blo 972592 3284765 := bstep (se 3 (by rfl) ⟨615893, by rfl⟩ : syracuseStep 3284765 = 1231787) B1231787
theorem B7806881 : Blo 972592 7806881 := bstep (se 2 (by rfl) ⟨2927580, by rfl⟩ : syracuseStep 7806881 = 5855161) B5855161
theorem B2465711 : Blo 972592 2465711 := bstep (se 1 (by rfl) ⟨1849283, by rfl⟩ : syracuseStep 2465711 = 3698567) B3698567
theorem B5546141 : Blo 972592 5546141 := bstep (se 3 (by rfl) ⟨1039901, by rfl⟩ : syracuseStep 5546141 = 2079803) B2079803
theorem B31990081 : Blo 972592 31990081 := bstep (se 2 (by rfl) ⟨11996280, by rfl⟩ : syracuseStep 31990081 = 23992561) B23992561
theorem B25010531 : Blo 972592 25010531 := bstep (se 1 (by rfl) ⟨18757898, by rfl⟩ : syracuseStep 25010531 = 37515797) B37515797
theorem B3285467 : Blo 972592 3285467 := bstep (se 1 (by rfl) ⟨2464100, by rfl⟩ : syracuseStep 3285467 = 4928201) B4928201
theorem B1647067 : Blo 972592 1647067 := bstep (se 1 (by rfl) ⟨1235300, by rfl⟩ : syracuseStep 1647067 = 2470601) B2470601
theorem B5546825 : Blo 972592 5546825 := bstep (se 2 (by rfl) ⟨2080059, by rfl⟩ : syracuseStep 5546825 = 4160119) B4160119
theorem B1876879 : Blo 972592 1876879 := bstep (se 1 (by rfl) ⟨1407659, by rfl⟩ : syracuseStep 1876879 = 2815319) B2815319
theorem B6235055 : Blo 972592 6235055 := bstep (se 1 (by rfl) ⟨4676291, by rfl⟩ : syracuseStep 6235055 = 9352583) B9352583
theorem B9511901 : Blo 972592 9511901 := bstep (se 3 (by rfl) ⟨1783481, by rfl⟩ : syracuseStep 9511901 = 3566963) B3566963
theorem B2466895 : Blo 972592 2466895 := bstep (se 1 (by rfl) ⟨1850171, by rfl⟩ : syracuseStep 2466895 = 3700343) B3700343
theorem B1647695 : Blo 972592 1647695 := bstep (se 1 (by rfl) ⟨1235771, by rfl⟩ : syracuseStep 1647695 = 2471543) B2471543
theorem B3286169 : Blo 972592 3286169 := bstep (se 2 (by rfl) ⟨1232313, by rfl⟩ : syracuseStep 3286169 = 2464627) B2464627
theorem B12494195 : Blo 972592 12494195 := bstep (se 1 (by rfl) ⟨9370646, by rfl⟩ : syracuseStep 12494195 = 18741293) B18741293
theorem B2467543 : Blo 972592 2467543 := bstep (se 1 (by rfl) ⟨1850657, by rfl⟩ : syracuseStep 2467543 = 3701315) B3701315
theorem B13510489 : Blo 972592 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B14034869 : Blo 972592 14034869 := bstep (se 5 (by rfl) ⟨657884, by rfl⟩ : syracuseStep 14034869 = 1315769) B1315769
theorem B3123127 : Blo 972592 3123127 := bstep (se 1 (by rfl) ⟨2342345, by rfl⟩ : syracuseStep 3123127 = 4684691) B4684691
theorem B4925447 : Blo 972592 4925447 := bstep (se 1 (by rfl) ⟨3694085, by rfl⟩ : syracuseStep 4925447 = 7388171) B7388171
theorem B2467847 : Blo 972592 2467847 := bstep (se 1 (by rfl) ⟨1850885, by rfl⟩ : syracuseStep 2467847 = 3701771) B3701771
theorem B2107471 : Blo 972592 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B3287357 : Blo 972592 3287357 := bstep (se 3 (by rfl) ⟨616379, by rfl⟩ : syracuseStep 3287357 = 1232759) B1232759
theorem B35596691 : Blo 972592 35596691 := bstep (se 1 (by rfl) ⟨26697518, by rfl⟩ : syracuseStep 35596691 = 53395037) B53395037
theorem B4925933 : Blo 972592 4925933 := bstep (se 3 (by rfl) ⟨923612, by rfl⟩ : syracuseStep 4925933 = 1847225) B1847225
theorem B5549057 : Blo 972592 5549057 := bstep (se 2 (by rfl) ⟨2080896, by rfl⟩ : syracuseStep 5549057 = 4161793) B4161793
theorem B3288221 : Blo 972592 3288221 := bstep (se 3 (by rfl) ⟨616541, by rfl⟩ : syracuseStep 3288221 = 1233083) B1233083
theorem B4926743 : Blo 972592 4926743 := bstep (se 1 (by rfl) ⟨3695057, by rfl⟩ : syracuseStep 4926743 = 7390115) B7390115
theorem B1846633 : Blo 972592 1846633 := bstep (se 2 (by rfl) ⟨692487, by rfl⟩ : syracuseStep 1846633 = 1384975) B1384975
theorem B1846793 : Blo 972592 1846793 := bstep (se 2 (by rfl) ⟨692547, by rfl⟩ : syracuseStep 1846793 = 1385095) B1385095
theorem B37957207 : Blo 972592 37957207 := bstep (se 1 (by rfl) ⟨28467905, by rfl⟩ : syracuseStep 37957207 = 56935811) B56935811
theorem B3288761 : Blo 972592 3288761 := bstep (se 2 (by rfl) ⟨1233285, by rfl⟩ : syracuseStep 3288761 = 2466571) B2466571
theorem B21114755 : Blo 972592 21114755 := bstep (se 1 (by rfl) ⟨15836066, by rfl⟩ : syracuseStep 21114755 = 31672133) B31672133
theorem B2470135 : Blo 972592 2470135 := bstep (se 1 (by rfl) ⟨1852601, by rfl⟩ : syracuseStep 2470135 = 3705203) B3705203
theorem B3289355 : Blo 972592 3289355 := bstep (se 1 (by rfl) ⟨2467016, by rfl⟩ : syracuseStep 3289355 = 4934033) B4934033
theorem B2470409 : Blo 972592 2470409 := bstep (se 2 (by rfl) ⟨926403, by rfl⟩ : syracuseStep 2470409 = 1852807) B1852807
theorem B3289625 : Blo 972592 3289625 := bstep (se 2 (by rfl) ⟨1233609, by rfl⟩ : syracuseStep 3289625 = 2467219) B2467219
theorem B2470439 : Blo 972592 2470439 := bstep (se 1 (by rfl) ⟨1852829, by rfl⟩ : syracuseStep 2470439 = 3705659) B3705659
theorem B4928363 : Blo 972592 4928363 := bstep (se 1 (by rfl) ⟨3696272, by rfl⟩ : syracuseStep 4928363 = 7392545) B7392545
theorem B2470763 : Blo 972592 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B1094575 : Blo 972592 1094575 := bstep (se 1 (by rfl) ⟨820931, by rfl⟩ : syracuseStep 1094575 = 1641863) B1641863
theorem B1848251 : Blo 972592 1848251 := bstep (se 1 (by rfl) ⟨1386188, by rfl⟩ : syracuseStep 1848251 = 2772377) B2772377
theorem B12497885 : Blo 972592 12497885 := bstep (se 3 (by rfl) ⟨2343353, by rfl⟩ : syracuseStep 12497885 = 4686707) B4686707
theorem B1389577 : Blo 972592 1389577 := bstep (se 2 (by rfl) ⟨521091, by rfl⟩ : syracuseStep 1389577 = 1042183) B1042183
theorem B2077753 : Blo 972592 2077753 := bstep (se 2 (by rfl) ⟨779157, by rfl⟩ : syracuseStep 2077753 = 1558315) B1558315
theorem B6337739 : Blo 972592 6337739 := bstep (se 1 (by rfl) ⟨4753304, by rfl⟩ : syracuseStep 6337739 = 9506609) B9506609
theorem B1095007 : Blo 972592 1095007 := bstep (se 1 (by rfl) ⟨821255, by rfl⟩ : syracuseStep 1095007 = 1642511) B1642511
theorem B2962793 : Blo 972592 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B1848683 : Blo 972592 1848683 := bstep (se 1 (by rfl) ⟨1386512, by rfl⟩ : syracuseStep 1848683 = 2773025) B2773025
theorem B2078095 : Blo 972592 2078095 := bstep (se 1 (by rfl) ⟨1558571, by rfl⟩ : syracuseStep 2078095 = 3117143) B3117143
theorem B1848737 : Blo 972592 1848737 := bstep (se 2 (by rfl) ⟨693276, by rfl⟩ : syracuseStep 1848737 = 1386553) B1386553
theorem B4929011 : Blo 972592 4929011 := bstep (se 1 (by rfl) ⟨3696758, by rfl⟩ : syracuseStep 4929011 = 7393517) B7393517
theorem B2471411 : Blo 972592 2471411 := bstep (se 1 (by rfl) ⟨1853558, by rfl⟩ : syracuseStep 2471411 = 3707117) B3707117
theorem B21116477 : Blo 972592 21116477 := bstep (se 3 (by rfl) ⟨3959339, by rfl⟩ : syracuseStep 21116477 = 7918679) B7918679
theorem B3290759 : Blo 972592 3290759 := bstep (se 1 (by rfl) ⟨2468069, by rfl⟩ : syracuseStep 3290759 = 4936139) B4936139
theorem B3290813 : Blo 972592 3290813 := bstep (se 3 (by rfl) ⟨617027, by rfl⟩ : syracuseStep 3290813 = 1234055) B1234055
theorem B1095367 : Blo 972592 1095367 := bstep (se 1 (by rfl) ⟨821525, by rfl⟩ : syracuseStep 1095367 = 1643051) B1643051
theorem B4437803 : Blo 972592 4437803 := bstep (se 1 (by rfl) ⟨3328352, by rfl⟩ : syracuseStep 4437803 = 6656705) B6656705
theorem B3290975 : Blo 972592 3290975 := bstep (se 1 (by rfl) ⟨2468231, by rfl⟩ : syracuseStep 3290975 = 4936463) B4936463
theorem B2471867 : Blo 972592 2471867 := bstep (se 1 (by rfl) ⟨1853900, by rfl⟩ : syracuseStep 2471867 = 3707801) B3707801
theorem B3291137 : Blo 972592 3291137 := bstep (se 2 (by rfl) ⟨1234176, by rfl⟩ : syracuseStep 3291137 = 2468353) B2468353
theorem B4438097 : Blo 972592 4438097 := bstep (se 2 (by rfl) ⟨1664286, by rfl⟩ : syracuseStep 4438097 = 3328573) B3328573
theorem B8894771 : Blo 972592 8894771 := bstep (se 1 (by rfl) ⟨6671078, by rfl⟩ : syracuseStep 8894771 = 13342157) B13342157
theorem B16005509 : Blo 972592 16005509 := bstep (se 4 (by rfl) ⟨1500516, by rfl⟩ : syracuseStep 16005509 = 3001033) B3001033
theorem B7027181 : Blo 972592 7027181 := bstep (se 3 (by rfl) ⟨1317596, by rfl⟩ : syracuseStep 7027181 = 2635193) B2635193
theorem B1096231 : Blo 972592 1096231 := bstep (se 1 (by rfl) ⟨822173, by rfl⟩ : syracuseStep 1096231 = 1644347) B1644347
theorem B2505431 : Blo 972592 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B4930307 : Blo 972592 4930307 := bstep (se 1 (by rfl) ⟨3697730, by rfl⟩ : syracuseStep 4930307 = 7395461) B7395461
theorem B3291947 : Blo 972592 3291947 := bstep (se 1 (by rfl) ⟨2468960, by rfl⟩ : syracuseStep 3291947 = 4937921) B4937921
theorem B1850377 : Blo 972592 1850377 := bstep (se 2 (by rfl) ⟨693891, by rfl⟩ : syracuseStep 1850377 = 1387783) B1387783
theorem B3292217 : Blo 972592 3292217 := bstep (se 2 (by rfl) ⟨1234581, by rfl⟩ : syracuseStep 3292217 = 2469163) B2469163
theorem B5553431 : Blo 972592 5553431 := bstep (se 1 (by rfl) ⟨4165073, by rfl⟩ : syracuseStep 5553431 = 8330147) B8330147
theorem B3292541 : Blo 972592 3292541 := bstep (se 3 (by rfl) ⟨617351, by rfl⟩ : syracuseStep 3292541 = 1234703) B1234703
theorem B2670043 : Blo 972592 2670043 := bstep (se 1 (by rfl) ⟨2002532, by rfl⟩ : syracuseStep 2670043 = 4005065) B4005065
theorem B200326769 : Blo 972592 200326769 := bstep (se 2 (by rfl) ⟨75122538, by rfl⟩ : syracuseStep 200326769 = 150245077) B150245077
theorem B3292811 : Blo 972592 3292811 := bstep (se 1 (by rfl) ⟨2469608, by rfl⟩ : syracuseStep 3292811 = 4939217) B4939217
theorem B1752787 : Blo 972592 1752787 := bstep (se 1 (by rfl) ⟨1314590, by rfl⟩ : syracuseStep 1752787 = 2629181) B2629181
theorem B8437537 : Blo 972592 8437537 := bstep (se 2 (by rfl) ⟨3164076, by rfl⟩ : syracuseStep 8437537 = 6328153) B6328153
theorem B1851311 : Blo 972592 1851311 := bstep (se 1 (by rfl) ⟨1388483, by rfl⟩ : syracuseStep 1851311 = 2776967) B2776967
theorem B3751867 : Blo 972592 3751867 := bstep (se 1 (by rfl) ⟨2813900, by rfl⟩ : syracuseStep 3751867 = 5627801) B5627801
theorem B1097851 : Blo 972592 1097851 := bstep (se 1 (by rfl) ⟨823388, by rfl⟩ : syracuseStep 1097851 = 1646777) B1646777
theorem B17809733 : Blo 972592 17809733 := bstep (se 4 (by rfl) ⟨1669662, by rfl⟩ : syracuseStep 17809733 = 3339325) B3339325
theorem B4931927 : Blo 972592 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B1851835 : Blo 972592 1851835 := bstep (se 1 (by rfl) ⟨1388876, by rfl⟩ : syracuseStep 1851835 = 2777753) B2777753
theorem B3293729 : Blo 972592 3293729 := bstep (se 2 (by rfl) ⟨1235148, by rfl⟩ : syracuseStep 3293729 = 2470297) B2470297
theorem B1098319 : Blo 972592 1098319 := bstep (se 1 (by rfl) ⟨823739, by rfl⟩ : syracuseStep 1098319 = 1647479) B1647479
theorem B13681325 : Blo 972592 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B3293945 : Blo 972592 3293945 := bstep (se 2 (by rfl) ⟨1235229, by rfl⟩ : syracuseStep 3293945 = 2470459) B2470459
theorem B6243101 : Blo 972592 6243101 := bstep (se 3 (by rfl) ⟨1170581, by rfl⟩ : syracuseStep 6243101 = 2341163) B2341163
theorem B1459049 : Blo 972592 1459049 := bstep (se 2 (by rfl) ⟨547143, by rfl⟩ : syracuseStep 1459049 = 1094287) B1094287
theorem B1852321 : Blo 972592 1852321 := bstep (se 2 (by rfl) ⟨694620, by rfl⟩ : syracuseStep 1852321 = 1389241) B1389241
theorem B1459127 : Blo 972592 1459127 := bstep (se 1 (by rfl) ⟨1094345, by rfl⟩ : syracuseStep 1459127 = 2188691) B2188691
theorem B1459163 : Blo 972592 1459163 := bstep (se 1 (by rfl) ⟨1094372, by rfl⟩ : syracuseStep 1459163 = 2188745) B2188745
theorem B3294215 : Blo 972592 3294215 := bstep (se 1 (by rfl) ⟨2470661, by rfl⟩ : syracuseStep 3294215 = 4941323) B4941323
theorem B3294323 : Blo 972592 3294323 := bstep (se 1 (by rfl) ⟨2470742, by rfl⟩ : syracuseStep 3294323 = 4941485) B4941485
theorem B56214647 : Blo 972592 56214647 := bstep (se 1 (by rfl) ⟨42160985, by rfl⟩ : syracuseStep 56214647 = 84321971) B84321971
theorem B2344297 : Blo 972592 2344297 := bstep (se 2 (by rfl) ⟨879111, by rfl⟩ : syracuseStep 2344297 = 1758223) B1758223
theorem B3294593 : Blo 972592 3294593 := bstep (se 2 (by rfl) ⟨1235472, by rfl⟩ : syracuseStep 3294593 = 2470945) B2470945
theorem B1459631 : Blo 972592 1459631 := bstep (se 1 (by rfl) ⟨1094723, by rfl⟩ : syracuseStep 1459631 = 2189447) B2189447
theorem B1459721 : Blo 972592 1459721 := bstep (se 2 (by rfl) ⟨547395, by rfl⟩ : syracuseStep 1459721 = 1094791) B1094791
theorem B1459751 : Blo 972592 1459751 := bstep (se 1 (by rfl) ⟨1094813, by rfl⟩ : syracuseStep 1459751 = 2189627) B2189627
theorem B1459835 : Blo 972592 1459835 := bstep (se 1 (by rfl) ⟨1094876, by rfl⟩ : syracuseStep 1459835 = 2189753) B2189753
theorem B1558187 : Blo 972592 1558187 := bstep (se 1 (by rfl) ⟨1168640, by rfl⟩ : syracuseStep 1558187 = 2337281) B2337281
theorem B2082503 : Blo 972592 2082503 := bstep (se 1 (by rfl) ⟨1561877, by rfl⟩ : syracuseStep 2082503 = 3123755) B3123755
theorem B1459961 : Blo 972592 1459961 := bstep (se 2 (by rfl) ⟨547485, by rfl⟩ : syracuseStep 1459961 = 1094971) B1094971
theorem B1460063 : Blo 972592 1460063 := bstep (se 1 (by rfl) ⟨1095047, by rfl⟩ : syracuseStep 1460063 = 2190095) B2190095
theorem B1460075 : Blo 972592 1460075 := bstep (se 1 (by rfl) ⟨1095056, by rfl⟩ : syracuseStep 1460075 = 2190113) B2190113
theorem B11093921 : Blo 972592 11093921 := bstep (se 2 (by rfl) ⟨4160220, by rfl⟩ : syracuseStep 11093921 = 8320441) B8320441
theorem B1755145 : Blo 972592 1755145 := bstep (se 2 (by rfl) ⟨658179, by rfl⟩ : syracuseStep 1755145 = 1316359) B1316359
theorem B1460303 : Blo 972592 1460303 := bstep (se 1 (by rfl) ⟨1095227, by rfl⟩ : syracuseStep 1460303 = 2190455) B2190455
theorem B3295403 : Blo 972592 3295403 := bstep (se 1 (by rfl) ⟨2471552, by rfl⟩ : syracuseStep 3295403 = 4943105) B4943105
theorem B1460423 : Blo 972592 1460423 := bstep (se 1 (by rfl) ⟨1095317, by rfl⟩ : syracuseStep 1460423 = 2190635) B2190635
theorem B3164503 : Blo 972592 3164503 := bstep (se 1 (by rfl) ⟨2373377, by rfl⟩ : syracuseStep 3164503 = 4746755) B4746755
theorem B1460585 : Blo 972592 1460585 := bstep (se 2 (by rfl) ⟨547719, by rfl⟩ : syracuseStep 1460585 = 1095439) B1095439
theorem B2345345 : Blo 972592 2345345 := bstep (se 2 (by rfl) ⟨879504, by rfl⟩ : syracuseStep 2345345 = 1759009) B1759009
theorem B1460663 : Blo 972592 1460663 := bstep (se 1 (by rfl) ⟨1095497, by rfl⟩ : syracuseStep 1460663 = 2190995) B2190995
theorem B1460699 : Blo 972592 1460699 := bstep (se 1 (by rfl) ⟨1095524, by rfl⟩ : syracuseStep 1460699 = 2191049) B2191049
theorem B3295943 : Blo 972592 3295943 := bstep (se 1 (by rfl) ⟨2471957, by rfl⟩ : syracuseStep 3295943 = 4943915) B4943915
theorem B3754745 : Blo 972592 3754745 := bstep (se 2 (by rfl) ⟨1408029, by rfl⟩ : syracuseStep 3754745 = 2816059) B2816059
theorem B5262083 : Blo 972592 5262083 := bstep (se 1 (by rfl) ⟨3946562, by rfl⟩ : syracuseStep 5262083 = 7893125) B7893125
theorem B2083657 : Blo 972592 2083657 := bstep (se 2 (by rfl) ⟨781371, by rfl⟩ : syracuseStep 2083657 = 1562743) B1562743
theorem B1461167 : Blo 972592 1461167 := bstep (se 1 (by rfl) ⟨1095875, by rfl⟩ : syracuseStep 1461167 = 2191751) B2191751
theorem B1461257 : Blo 972592 1461257 := bstep (se 2 (by rfl) ⟨547971, by rfl⟩ : syracuseStep 1461257 = 1095943) B1095943
theorem B1461287 : Blo 972592 1461287 := bstep (se 1 (by rfl) ⟨1095965, by rfl⟩ : syracuseStep 1461287 = 2191931) B2191931
theorem B1461371 : Blo 972592 1461371 := bstep (se 1 (by rfl) ⟨1096028, by rfl⟩ : syracuseStep 1461371 = 2192057) B2192057
theorem B13028525 : Blo 972592 13028525 := bstep (se 3 (by rfl) ⟨2442848, by rfl⟩ : syracuseStep 13028525 = 4885697) B4885697
theorem B2673911 : Blo 972592 2673911 := bstep (se 1 (by rfl) ⟨2005433, by rfl⟩ : syracuseStep 2673911 = 4010867) B4010867
theorem B1461497 : Blo 972592 1461497 := bstep (se 2 (by rfl) ⟨548061, by rfl⟩ : syracuseStep 1461497 = 1096123) B1096123
theorem B8310053 : Blo 972592 8310053 := bstep (se 4 (by rfl) ⟨779067, by rfl⟩ : syracuseStep 8310053 = 1558135) B1558135
theorem B12471641 : Blo 972592 12471641 := bstep (se 2 (by rfl) ⟨4676865, by rfl⟩ : syracuseStep 12471641 = 9353731) B9353731
theorem B1461599 : Blo 972592 1461599 := bstep (se 1 (by rfl) ⟨1096199, by rfl⟩ : syracuseStep 1461599 = 2192399) B2192399
theorem B1461611 : Blo 972592 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B1461839 : Blo 972592 1461839 := bstep (se 1 (by rfl) ⟨1096379, by rfl⟩ : syracuseStep 1461839 = 2192759) B2192759
theorem B1461959 : Blo 972592 1461959 := bstep (se 1 (by rfl) ⟨1096469, by rfl⟩ : syracuseStep 1461959 = 2192939) B2192939
theorem B4935491 : Blo 972592 4935491 := bstep (se 1 (by rfl) ⟨3701618, by rfl⟩ : syracuseStep 4935491 = 7403237) B7403237
theorem B1462121 : Blo 972592 1462121 := bstep (se 2 (by rfl) ⟨548295, by rfl⟩ : syracuseStep 1462121 = 1096591) B1096591
theorem B1232815 : Blo 972592 1232815 := bstep (se 1 (by rfl) ⟨924611, by rfl⟩ : syracuseStep 1232815 = 1849223) B1849223
theorem B1462199 : Blo 972592 1462199 := bstep (se 1 (by rfl) ⟨1096649, by rfl⟩ : syracuseStep 1462199 = 2193299) B2193299
theorem B1560539 : Blo 972592 1560539 := bstep (se 1 (by rfl) ⟨1170404, by rfl⟩ : syracuseStep 1560539 = 2340809) B2340809
theorem B1462235 : Blo 972592 1462235 := bstep (se 1 (by rfl) ⟨1096676, by rfl⟩ : syracuseStep 1462235 = 2193353) B2193353
theorem B1626151 : Blo 972592 1626151 := bstep (se 1 (by rfl) ⟨1219613, by rfl⟩ : syracuseStep 1626151 = 2439227) B2439227
theorem B47403089 : Blo 972592 47403089 := bstep (se 2 (by rfl) ⟨17776158, by rfl⟩ : syracuseStep 47403089 = 35552317) B35552317
theorem B1462703 : Blo 972592 1462703 := bstep (se 1 (by rfl) ⟨1097027, by rfl⟩ : syracuseStep 1462703 = 2194055) B2194055
theorem B1462793 : Blo 972592 1462793 := bstep (se 2 (by rfl) ⟨548547, by rfl⟩ : syracuseStep 1462793 = 1097095) B1097095
theorem B1462823 : Blo 972592 1462823 := bstep (se 1 (by rfl) ⟨1097117, by rfl⟩ : syracuseStep 1462823 = 2194235) B2194235
theorem B1561211 : Blo 972592 1561211 := bstep (se 1 (by rfl) ⟨1170908, by rfl⟩ : syracuseStep 1561211 = 2341817) B2341817
theorem B1462907 : Blo 972592 1462907 := bstep (se 1 (by rfl) ⟨1097180, by rfl⟩ : syracuseStep 1462907 = 2194361) B2194361
theorem B7394003 : Blo 972592 7394003 := bstep (se 1 (by rfl) ⟨5545502, by rfl⟩ : syracuseStep 7394003 = 11091005) B11091005
theorem B1463033 : Blo 972592 1463033 := bstep (se 2 (by rfl) ⟨548637, by rfl⟩ : syracuseStep 1463033 = 1097275) B1097275
theorem B1463135 : Blo 972592 1463135 := bstep (se 1 (by rfl) ⟨1097351, by rfl⟩ : syracuseStep 1463135 = 2194703) B2194703
theorem B40555363 : Blo 972592 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B1463147 : Blo 972592 1463147 := bstep (se 1 (by rfl) ⟨1097360, by rfl⟩ : syracuseStep 1463147 = 2194721) B2194721
theorem B1233883 : Blo 972592 1233883 := bstep (se 1 (by rfl) ⟨925412, by rfl⟩ : syracuseStep 1233883 = 1850825) B1850825
theorem B1463375 : Blo 972592 1463375 := bstep (se 1 (by rfl) ⟨1097531, by rfl⟩ : syracuseStep 1463375 = 2195063) B2195063
theorem B1561723 : Blo 972592 1561723 := bstep (se 1 (by rfl) ⟨1171292, by rfl⟩ : syracuseStep 1561723 = 2342585) B2342585
theorem B1463495 : Blo 972592 1463495 := bstep (se 1 (by rfl) ⟨1097621, by rfl⟩ : syracuseStep 1463495 = 2195243) B2195243
theorem B1463657 : Blo 972592 1463657 := bstep (se 2 (by rfl) ⟨548871, by rfl⟩ : syracuseStep 1463657 = 1097743) B1097743
theorem B9360805 : Blo 972592 9360805 := bstep (se 4 (by rfl) ⟨877575, by rfl⟩ : syracuseStep 9360805 = 1755151) B1755151
theorem B1463735 : Blo 972592 1463735 := bstep (se 1 (by rfl) ⟨1097801, by rfl⟩ : syracuseStep 1463735 = 2195603) B2195603
theorem B1463771 : Blo 972592 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B5559947 : Blo 972592 5559947 := bstep (se 1 (by rfl) ⟨4169960, by rfl⟩ : syracuseStep 5559947 = 8339921) B8339921
theorem B972623 : Blo 972592 972623 := bstep (se 1 (by rfl) ⟨729467, by rfl⟩ : syracuseStep 972623 = 1458935) B1458935
theorem B972639 : Blo 972592 972639 := bstep (se 1 (by rfl) ⟨729479, by rfl⟩ : syracuseStep 972639 = 1458959) B1458959
theorem B3954541 : Blo 972592 3954541 := bstep (se 3 (by rfl) ⟨741476, by rfl⟩ : syracuseStep 3954541 = 1482953) B1482953
theorem B972667 : Blo 972592 972667 := bstep (se 1 (by rfl) ⟨729500, by rfl⟩ : syracuseStep 972667 = 1459001) B1459001
theorem B972719 : Blo 972592 972719 := bstep (se 1 (by rfl) ⟨729539, by rfl⟩ : syracuseStep 972719 = 1459079) B1459079
theorem B1464239 : Blo 972592 1464239 := bstep (se 1 (by rfl) ⟨1098179, by rfl⟩ : syracuseStep 1464239 = 2196359) B2196359
theorem B972743 : Blo 972592 972743 := bstep (se 1 (by rfl) ⟨729557, by rfl⟩ : syracuseStep 972743 = 1459115) B1459115
theorem B972763 : Blo 972592 972763 := bstep (se 1 (by rfl) ⟨729572, by rfl⟩ : syracuseStep 972763 = 1459145) B1459145
theorem B1464329 : Blo 972592 1464329 := bstep (se 2 (by rfl) ⟨549123, by rfl⟩ : syracuseStep 1464329 = 1098247) B1098247
theorem B972839 : Blo 972592 972839 := bstep (se 1 (by rfl) ⟨729629, by rfl⟩ : syracuseStep 972839 = 1459259) B1459259
theorem B1169447 : Blo 972592 1169447 := bstep (se 1 (by rfl) ⟨877085, by rfl⟩ : syracuseStep 1169447 = 1754171) B1754171
theorem B1464359 : Blo 972592 1464359 := bstep (se 1 (by rfl) ⟨1098269, by rfl⟩ : syracuseStep 1464359 = 2196539) B2196539
theorem B972879 : Blo 972592 972879 := bstep (se 1 (by rfl) ⟨729659, by rfl⟩ : syracuseStep 972879 = 1459319) B1459319
theorem B972895 : Blo 972592 972895 := bstep (se 1 (by rfl) ⟨729671, by rfl⟩ : syracuseStep 972895 = 1459343) B1459343
theorem B972923 : Blo 972592 972923 := bstep (se 1 (by rfl) ⟨729692, by rfl⟩ : syracuseStep 972923 = 1459385) B1459385
theorem B1464443 : Blo 972592 1464443 := bstep (se 1 (by rfl) ⟨1098332, by rfl⟩ : syracuseStep 1464443 = 2196665) B2196665
theorem B972975 : Blo 972592 972975 := bstep (se 1 (by rfl) ⟨729731, by rfl⟩ : syracuseStep 972975 = 1459463) B1459463
theorem B972999 : Blo 972592 972999 := bstep (se 1 (by rfl) ⟨729749, by rfl⟩ : syracuseStep 972999 = 1459499) B1459499
theorem B973019 : Blo 972592 973019 := bstep (se 1 (by rfl) ⟨729764, by rfl⟩ : syracuseStep 973019 = 1459529) B1459529
theorem B1464569 : Blo 972592 1464569 := bstep (se 2 (by rfl) ⟨549213, by rfl⟩ : syracuseStep 1464569 = 1098427) B1098427
theorem B973095 : Blo 972592 973095 := bstep (se 1 (by rfl) ⟨729821, by rfl⟩ : syracuseStep 973095 = 1459643) B1459643
theorem B973135 : Blo 972592 973135 := bstep (se 1 (by rfl) ⟨729851, by rfl⟩ : syracuseStep 973135 = 1459703) B1459703
theorem B4675927 : Blo 972592 4675927 := bstep (se 1 (by rfl) ⟨3506945, by rfl⟩ : syracuseStep 4675927 = 7013891) B7013891
theorem B973151 : Blo 972592 973151 := bstep (se 1 (by rfl) ⟨729863, by rfl⟩ : syracuseStep 973151 = 1459727) B1459727
theorem B1464671 : Blo 972592 1464671 := bstep (se 1 (by rfl) ⟨1098503, by rfl⟩ : syracuseStep 1464671 = 2197007) B2197007
theorem B1464683 : Blo 972592 1464683 := bstep (se 1 (by rfl) ⟨1098512, by rfl⟩ : syracuseStep 1464683 = 2197025) B2197025
theorem B973179 : Blo 972592 973179 := bstep (se 1 (by rfl) ⟨729884, by rfl⟩ : syracuseStep 973179 = 1459769) B1459769
theorem B973231 : Blo 972592 973231 := bstep (se 1 (by rfl) ⟨729923, by rfl⟩ : syracuseStep 973231 = 1459847) B1459847
theorem B973255 : Blo 972592 973255 := bstep (se 1 (by rfl) ⟨729941, by rfl⟩ : syracuseStep 973255 = 1459883) B1459883
theorem B973275 : Blo 972592 973275 := bstep (se 1 (by rfl) ⟨729956, by rfl⟩ : syracuseStep 973275 = 1459913) B1459913
theorem B5003801 : Blo 972592 5003801 := bstep (se 2 (by rfl) ⟨1876425, by rfl⟩ : syracuseStep 5003801 = 3752851) B3752851
theorem B973351 : Blo 972592 973351 := bstep (se 1 (by rfl) ⟨730013, by rfl⟩ : syracuseStep 973351 = 1460027) B1460027
theorem B973391 : Blo 972592 973391 := bstep (se 1 (by rfl) ⟨730043, by rfl⟩ : syracuseStep 973391 = 1460087) B1460087
theorem B973407 : Blo 972592 973407 := bstep (se 1 (by rfl) ⟨730055, by rfl⟩ : syracuseStep 973407 = 1460111) B1460111
theorem B973435 : Blo 972592 973435 := bstep (se 1 (by rfl) ⟨730076, by rfl⟩ : syracuseStep 973435 = 1460153) B1460153
theorem B9984647 : Blo 972592 9984647 := bstep (se 1 (by rfl) ⟨7488485, by rfl⟩ : syracuseStep 9984647 = 14976971) B14976971
theorem B973487 : Blo 972592 973487 := bstep (se 1 (by rfl) ⟨730115, by rfl⟩ : syracuseStep 973487 = 1460231) B1460231
theorem B973511 : Blo 972592 973511 := bstep (se 1 (by rfl) ⟨730133, by rfl⟩ : syracuseStep 973511 = 1460267) B1460267
theorem B973531 : Blo 972592 973531 := bstep (se 1 (by rfl) ⟨730148, by rfl⟩ : syracuseStep 973531 = 1460297) B1460297
theorem B973607 : Blo 972592 973607 := bstep (se 1 (by rfl) ⟨730205, by rfl⟩ : syracuseStep 973607 = 1460411) B1460411
theorem B4938569 : Blo 972592 4938569 := bstep (se 2 (by rfl) ⟨1851963, by rfl⟩ : syracuseStep 4938569 = 3703927) B3703927
theorem B8313677 : Blo 972592 8313677 := bstep (se 3 (by rfl) ⟨1558814, by rfl⟩ : syracuseStep 8313677 = 3117629) B3117629
theorem B973647 : Blo 972592 973647 := bstep (se 1 (by rfl) ⟨730235, by rfl⟩ : syracuseStep 973647 = 1460471) B1460471
theorem B973663 : Blo 972592 973663 := bstep (se 1 (by rfl) ⟨730247, by rfl⟩ : syracuseStep 973663 = 1460495) B1460495
theorem B973691 : Blo 972592 973691 := bstep (se 1 (by rfl) ⟨730268, by rfl⟩ : syracuseStep 973691 = 1460537) B1460537
theorem B973743 : Blo 972592 973743 := bstep (se 1 (by rfl) ⟨730307, by rfl⟩ : syracuseStep 973743 = 1460615) B1460615
theorem B3955643 : Blo 972592 3955643 := bstep (se 1 (by rfl) ⟨2966732, by rfl⟩ : syracuseStep 3955643 = 5933465) B5933465
theorem B973767 : Blo 972592 973767 := bstep (se 1 (by rfl) ⟨730325, by rfl⟩ : syracuseStep 973767 = 1460651) B1460651
theorem B973787 : Blo 972592 973787 := bstep (se 1 (by rfl) ⟨730340, by rfl⟩ : syracuseStep 973787 = 1460681) B1460681
theorem B973863 : Blo 972592 973863 := bstep (se 1 (by rfl) ⟨730397, by rfl⟩ : syracuseStep 973863 = 1460795) B1460795
theorem B973903 : Blo 972592 973903 := bstep (se 1 (by rfl) ⟨730427, by rfl⟩ : syracuseStep 973903 = 1460855) B1460855
theorem B973919 : Blo 972592 973919 := bstep (se 1 (by rfl) ⟨730439, by rfl⟩ : syracuseStep 973919 = 1460879) B1460879
theorem B1039483 : Blo 972592 1039483 := bstep (se 1 (by rfl) ⟨779612, by rfl⟩ : syracuseStep 1039483 = 1559225) B1559225
theorem B973947 : Blo 972592 973947 := bstep (se 1 (by rfl) ⟨730460, by rfl⟩ : syracuseStep 973947 = 1460921) B1460921
theorem B3693721 : Blo 972592 3693721 := bstep (se 2 (by rfl) ⟨1385145, by rfl⟩ : syracuseStep 3693721 = 2770291) B2770291
theorem B973999 : Blo 972592 973999 := bstep (se 1 (by rfl) ⟨730499, by rfl⟩ : syracuseStep 973999 = 1460999) B1460999
theorem B974023 : Blo 972592 974023 := bstep (se 1 (by rfl) ⟨730517, by rfl⟩ : syracuseStep 974023 = 1461035) B1461035
theorem B974043 : Blo 972592 974043 := bstep (se 1 (by rfl) ⟨730532, by rfl⟩ : syracuseStep 974043 = 1461065) B1461065
theorem B974119 : Blo 972592 974119 := bstep (se 1 (by rfl) ⟨730589, by rfl⟩ : syracuseStep 974119 = 1461179) B1461179
theorem B974159 : Blo 972592 974159 := bstep (se 1 (by rfl) ⟨730619, by rfl⟩ : syracuseStep 974159 = 1461239) B1461239
theorem B974175 : Blo 972592 974175 := bstep (se 1 (by rfl) ⟨730631, by rfl⟩ : syracuseStep 974175 = 1461263) B1461263
theorem B974203 : Blo 972592 974203 := bstep (se 1 (by rfl) ⟨730652, by rfl⟩ : syracuseStep 974203 = 1461305) B1461305
theorem B974255 : Blo 972592 974255 := bstep (se 1 (by rfl) ⟨730691, by rfl⟩ : syracuseStep 974255 = 1461383) B1461383
theorem B974279 : Blo 972592 974279 := bstep (se 1 (by rfl) ⟨730709, by rfl⟩ : syracuseStep 974279 = 1461419) B1461419
theorem B3694025 : Blo 972592 3694025 := bstep (se 2 (by rfl) ⟨1385259, by rfl⟩ : syracuseStep 3694025 = 2770519) B2770519
theorem B974299 : Blo 972592 974299 := bstep (se 1 (by rfl) ⟨730724, by rfl⟩ : syracuseStep 974299 = 1461449) B1461449
theorem B15785459 : Blo 972592 15785459 := bstep (se 1 (by rfl) ⟨11839094, by rfl⟩ : syracuseStep 15785459 = 23678189) B23678189
theorem B974375 : Blo 972592 974375 := bstep (se 1 (by rfl) ⟨730781, by rfl⟩ : syracuseStep 974375 = 1461563) B1461563
theorem B974415 : Blo 972592 974415 := bstep (se 1 (by rfl) ⟨730811, by rfl⟩ : syracuseStep 974415 = 1461623) B1461623
theorem B974431 : Blo 972592 974431 := bstep (se 1 (by rfl) ⟨730823, by rfl⟩ : syracuseStep 974431 = 1461647) B1461647
theorem B974459 : Blo 972592 974459 := bstep (se 1 (by rfl) ⟨730844, by rfl⟩ : syracuseStep 974459 = 1461689) B1461689
theorem B974511 : Blo 972592 974511 := bstep (se 1 (by rfl) ⟨730883, by rfl⟩ : syracuseStep 974511 = 1461767) B1461767
theorem B974535 : Blo 972592 974535 := bstep (se 1 (by rfl) ⟨730901, by rfl⟩ : syracuseStep 974535 = 1461803) B1461803
theorem B974555 : Blo 972592 974555 := bstep (se 1 (by rfl) ⟨730916, by rfl⟩ : syracuseStep 974555 = 1461833) B1461833
theorem B974631 : Blo 972592 974631 := bstep (se 1 (by rfl) ⟨730973, by rfl⟩ : syracuseStep 974631 = 1461947) B1461947
theorem B974671 : Blo 972592 974671 := bstep (se 1 (by rfl) ⟨731003, by rfl⟩ : syracuseStep 974671 = 1462007) B1462007
theorem B974687 : Blo 972592 974687 := bstep (se 1 (by rfl) ⟨731015, by rfl⟩ : syracuseStep 974687 = 1462031) B1462031
theorem B974715 : Blo 972592 974715 := bstep (se 1 (by rfl) ⟨731036, by rfl⟩ : syracuseStep 974715 = 1462073) B1462073
theorem B12672931 : Blo 972592 12672931 := bstep (se 1 (by rfl) ⟨9504698, by rfl⟩ : syracuseStep 12672931 = 19009397) B19009397
theorem B3694511 : Blo 972592 3694511 := bstep (se 1 (by rfl) ⟨2770883, by rfl⟩ : syracuseStep 3694511 = 5541767) B5541767
theorem B974767 : Blo 972592 974767 := bstep (se 1 (by rfl) ⟨731075, by rfl⟩ : syracuseStep 974767 = 1462151) B1462151
theorem B974791 : Blo 972592 974791 := bstep (se 1 (by rfl) ⟨731093, by rfl⟩ : syracuseStep 974791 = 1462187) B1462187
theorem B974811 : Blo 972592 974811 := bstep (se 1 (by rfl) ⟨731108, by rfl⟩ : syracuseStep 974811 = 1462217) B1462217
theorem B7397405 : Blo 972592 7397405 := bstep (se 3 (by rfl) ⟨1387013, by rfl⟩ : syracuseStep 7397405 = 2774027) B2774027
theorem B974887 : Blo 972592 974887 := bstep (se 1 (by rfl) ⟨731165, by rfl⟩ : syracuseStep 974887 = 1462331) B1462331
theorem B3334223 : Blo 972592 3334223 := bstep (se 1 (by rfl) ⟨2500667, by rfl⟩ : syracuseStep 3334223 = 5001335) B5001335
theorem B974927 : Blo 972592 974927 := bstep (se 1 (by rfl) ⟨731195, by rfl⟩ : syracuseStep 974927 = 1462391) B1462391
theorem B4677713 : Blo 972592 4677713 := bstep (se 2 (by rfl) ⟨1754142, by rfl⟩ : syracuseStep 4677713 = 3508285) B3508285
theorem B4939865 : Blo 972592 4939865 := bstep (se 2 (by rfl) ⟨1852449, by rfl⟩ : syracuseStep 4939865 = 3704899) B3704899
theorem B974943 : Blo 972592 974943 := bstep (se 1 (by rfl) ⟨731207, by rfl⟩ : syracuseStep 974943 = 1462415) B1462415
theorem B974971 : Blo 972592 974971 := bstep (se 1 (by rfl) ⟨731228, by rfl⟩ : syracuseStep 974971 = 1462457) B1462457
theorem B975023 : Blo 972592 975023 := bstep (se 1 (by rfl) ⟨731267, by rfl⟩ : syracuseStep 975023 = 1462535) B1462535
theorem B975047 : Blo 972592 975047 := bstep (se 1 (by rfl) ⟨731285, by rfl⟩ : syracuseStep 975047 = 1462571) B1462571
theorem B975067 : Blo 972592 975067 := bstep (se 1 (by rfl) ⟨731300, by rfl⟩ : syracuseStep 975067 = 1462601) B1462601
theorem B975143 : Blo 972592 975143 := bstep (se 1 (by rfl) ⟨731357, by rfl⟩ : syracuseStep 975143 = 1462715) B1462715
theorem B975183 : Blo 972592 975183 := bstep (se 1 (by rfl) ⟨731387, by rfl⟩ : syracuseStep 975183 = 1462775) B1462775
theorem B1040735 : Blo 972592 1040735 := bstep (se 1 (by rfl) ⟨780551, by rfl⟩ : syracuseStep 1040735 = 1561103) B1561103
theorem B975199 : Blo 972592 975199 := bstep (se 1 (by rfl) ⟨731399, by rfl⟩ : syracuseStep 975199 = 1462799) B1462799
theorem B975227 : Blo 972592 975227 := bstep (se 1 (by rfl) ⟨731420, by rfl⟩ : syracuseStep 975227 = 1462841) B1462841
theorem B975279 : Blo 972592 975279 := bstep (se 1 (by rfl) ⟨731459, by rfl⟩ : syracuseStep 975279 = 1462919) B1462919
theorem B975303 : Blo 972592 975303 := bstep (se 1 (by rfl) ⟨731477, by rfl⟩ : syracuseStep 975303 = 1462955) B1462955
theorem B975323 : Blo 972592 975323 := bstep (se 1 (by rfl) ⟨731492, by rfl⟩ : syracuseStep 975323 = 1462985) B1462985
theorem B975399 : Blo 972592 975399 := bstep (se 1 (by rfl) ⟨731549, by rfl⟩ : syracuseStep 975399 = 1463099) B1463099
theorem B975439 : Blo 972592 975439 := bstep (se 1 (by rfl) ⟨731579, by rfl⟩ : syracuseStep 975439 = 1463159) B1463159
theorem B975455 : Blo 972592 975455 := bstep (se 1 (by rfl) ⟨731591, by rfl⟩ : syracuseStep 975455 = 1463183) B1463183
theorem B975483 : Blo 972592 975483 := bstep (se 1 (by rfl) ⟨731612, by rfl⟩ : syracuseStep 975483 = 1463225) B1463225
theorem B975535 : Blo 972592 975535 := bstep (se 1 (by rfl) ⟨731651, by rfl⟩ : syracuseStep 975535 = 1463303) B1463303
theorem B975559 : Blo 972592 975559 := bstep (se 1 (by rfl) ⟨731669, by rfl⟩ : syracuseStep 975559 = 1463339) B1463339
theorem B975579 : Blo 972592 975579 := bstep (se 1 (by rfl) ⟨731684, by rfl⟩ : syracuseStep 975579 = 1463369) B1463369
theorem B4678403 : Blo 972592 4678403 := bstep (se 1 (by rfl) ⟨3508802, by rfl⟩ : syracuseStep 4678403 = 7017605) B7017605
theorem B975655 : Blo 972592 975655 := bstep (se 1 (by rfl) ⟨731741, by rfl⟩ : syracuseStep 975655 = 1463483) B1463483
theorem B975695 : Blo 972592 975695 := bstep (se 1 (by rfl) ⟨731771, by rfl⟩ : syracuseStep 975695 = 1463543) B1463543
theorem B975711 : Blo 972592 975711 := bstep (se 1 (by rfl) ⟨731783, by rfl⟩ : syracuseStep 975711 = 1463567) B1463567
theorem B975739 : Blo 972592 975739 := bstep (se 1 (by rfl) ⟨731804, by rfl⟩ : syracuseStep 975739 = 1463609) B1463609
theorem B975791 : Blo 972592 975791 := bstep (se 1 (by rfl) ⟨731843, by rfl⟩ : syracuseStep 975791 = 1463687) B1463687
theorem B975815 : Blo 972592 975815 := bstep (se 1 (by rfl) ⟨731861, by rfl⟩ : syracuseStep 975815 = 1463723) B1463723
theorem B975835 : Blo 972592 975835 := bstep (se 1 (by rfl) ⟨731876, by rfl⟩ : syracuseStep 975835 = 1463753) B1463753
theorem B33743891 : Blo 972592 33743891 := bstep (se 1 (by rfl) ⟨25307918, by rfl⟩ : syracuseStep 33743891 = 50615837) B50615837
theorem B975911 : Blo 972592 975911 := bstep (se 1 (by rfl) ⟨731933, by rfl⟩ : syracuseStep 975911 = 1463867) B1463867
theorem B2188367 : Blo 972592 2188367 := bstep (se 1 (by rfl) ⟨1641275, by rfl⟩ : syracuseStep 2188367 = 3282551) B3282551
theorem B975951 : Blo 972592 975951 := bstep (se 1 (by rfl) ⟨731963, by rfl⟩ : syracuseStep 975951 = 1463927) B1463927
theorem B975967 : Blo 972592 975967 := bstep (se 1 (by rfl) ⟨731975, by rfl⟩ : syracuseStep 975967 = 1463951) B1463951
theorem B975995 : Blo 972592 975995 := bstep (se 1 (by rfl) ⟨731996, by rfl⟩ : syracuseStep 975995 = 1463993) B1463993
theorem B976047 : Blo 972592 976047 := bstep (se 1 (by rfl) ⟨732035, by rfl⟩ : syracuseStep 976047 = 1464071) B1464071
theorem B976071 : Blo 972592 976071 := bstep (se 1 (by rfl) ⟨732053, by rfl⟩ : syracuseStep 976071 = 1464107) B1464107
theorem B976091 : Blo 972592 976091 := bstep (se 1 (by rfl) ⟨732068, by rfl⟩ : syracuseStep 976091 = 1464137) B1464137
theorem B6251813 : Blo 972592 6251813 := bstep (se 4 (by rfl) ⟨586107, by rfl⟩ : syracuseStep 6251813 = 1172215) B1172215
theorem B976167 : Blo 972592 976167 := bstep (se 1 (by rfl) ⟨732125, by rfl⟩ : syracuseStep 976167 = 1464251) B1464251
theorem B976207 : Blo 972592 976207 := bstep (se 1 (by rfl) ⟨732155, by rfl⟩ : syracuseStep 976207 = 1464311) B1464311
theorem B976223 : Blo 972592 976223 := bstep (se 1 (by rfl) ⟨732167, by rfl⟩ : syracuseStep 976223 = 1464335) B1464335
theorem B976251 : Blo 972592 976251 := bstep (se 1 (by rfl) ⟨732188, by rfl⟩ : syracuseStep 976251 = 1464377) B1464377
theorem B976303 : Blo 972592 976303 := bstep (se 1 (by rfl) ⟨732227, by rfl⟩ : syracuseStep 976303 = 1464455) B1464455
theorem B976327 : Blo 972592 976327 := bstep (se 1 (by rfl) ⟨732245, by rfl⟩ : syracuseStep 976327 = 1464491) B1464491
theorem B2188763 : Blo 972592 2188763 := bstep (se 1 (by rfl) ⟨1641572, by rfl⟩ : syracuseStep 2188763 = 3283145) B3283145
theorem B976347 : Blo 972592 976347 := bstep (se 1 (by rfl) ⟨732260, by rfl⟩ : syracuseStep 976347 = 1464521) B1464521
theorem B3696137 : Blo 972592 3696137 := bstep (se 2 (by rfl) ⟨1386051, by rfl⟩ : syracuseStep 3696137 = 2772103) B2772103
theorem B976423 : Blo 972592 976423 := bstep (se 1 (by rfl) ⟨732317, by rfl⟩ : syracuseStep 976423 = 1464635) B1464635
theorem B976463 : Blo 972592 976463 := bstep (se 1 (by rfl) ⟨732347, by rfl⟩ : syracuseStep 976463 = 1464695) B1464695
theorem B976479 : Blo 972592 976479 := bstep (se 1 (by rfl) ⟨732359, by rfl⟩ : syracuseStep 976479 = 1464719) B1464719
theorem B976507 : Blo 972592 976507 := bstep (se 1 (by rfl) ⟨732380, by rfl⟩ : syracuseStep 976507 = 1464761) B1464761
theorem B976559 : Blo 972592 976559 := bstep (se 1 (by rfl) ⟨732419, by rfl⟩ : syracuseStep 976559 = 1464839) B1464839
theorem B976583 : Blo 972592 976583 := bstep (se 1 (by rfl) ⟨732437, by rfl⟩ : syracuseStep 976583 = 1464875) B1464875
theorem B2189231 : Blo 972592 2189231 := bstep (se 1 (by rfl) ⟨1641923, by rfl⟩ : syracuseStep 2189231 = 3283847) B3283847
theorem B7039057 : Blo 972592 7039057 := bstep (se 2 (by rfl) ⟨2639646, by rfl⟩ : syracuseStep 7039057 = 5279293) B5279293
theorem B2189483 : Blo 972592 2189483 := bstep (se 1 (by rfl) ⟨1642112, by rfl⟩ : syracuseStep 2189483 = 3284225) B3284225
theorem B8907059 : Blo 972592 8907059 := bstep (se 1 (by rfl) ⟨6680294, by rfl⟩ : syracuseStep 8907059 = 13360589) B13360589
theorem B4680173 : Blo 972592 4680173 := bstep (se 3 (by rfl) ⟨877532, by rfl⟩ : syracuseStep 4680173 = 1755065) B1755065
theorem B5007905 : Blo 972592 5007905 := bstep (se 2 (by rfl) ⟨1877964, by rfl⟩ : syracuseStep 5007905 = 3755929) B3755929
theorem B2190023 : Blo 972592 2190023 := bstep (se 1 (by rfl) ⟨1642517, by rfl⟩ : syracuseStep 2190023 = 3285035) B3285035
theorem B2779859 : Blo 972592 2779859 := bstep (se 1 (by rfl) ⟨2084894, by rfl⟩ : syracuseStep 2779859 = 4169789) B4169789
theorem B3566497 : Blo 972592 3566497 := bstep (se 2 (by rfl) ⟨1337436, by rfl⟩ : syracuseStep 3566497 = 2674873) B2674873
theorem B3697595 : Blo 972592 3697595 := bstep (se 1 (by rfl) ⟨2773196, by rfl⟩ : syracuseStep 3697595 = 5546393) B5546393
theorem B2812985 : Blo 972592 2812985 := bstep (se 2 (by rfl) ⟨1054869, by rfl⟩ : syracuseStep 2812985 = 2109739) B2109739
theorem B2190887 : Blo 972592 2190887 := bstep (se 1 (by rfl) ⟨1643165, by rfl⟩ : syracuseStep 2190887 = 3286331) B3286331
theorem B7892603 : Blo 972592 7892603 := bstep (se 1 (by rfl) ⟨5919452, by rfl⟩ : syracuseStep 7892603 = 11838905) B11838905
theorem B2191211 : Blo 972592 2191211 := bstep (se 1 (by rfl) ⟨1643408, by rfl⟩ : syracuseStep 2191211 = 3286817) B3286817
theorem B6254455 : Blo 972592 6254455 := bstep (se 1 (by rfl) ⟨4690841, by rfl⟩ : syracuseStep 6254455 = 9381683) B9381683
theorem B2191265 : Blo 972592 2191265 := bstep (se 2 (by rfl) ⟨821724, by rfl⟩ : syracuseStep 2191265 = 1643449) B1643449
theorem B4681633 : Blo 972592 4681633 := bstep (se 2 (by rfl) ⟨1755612, by rfl⟩ : syracuseStep 4681633 = 3511225) B3511225
theorem B2191607 : Blo 972592 2191607 := bstep (se 1 (by rfl) ⟨1643705, by rfl⟩ : syracuseStep 2191607 = 3287411) B3287411
theorem B7401779 : Blo 972592 7401779 := bstep (se 1 (by rfl) ⟨5551334, by rfl⟩ : syracuseStep 7401779 = 11102669) B11102669
theorem B13332995 : Blo 972592 13332995 := bstep (se 1 (by rfl) ⟨9999746, by rfl⟩ : syracuseStep 13332995 = 19999493) B19999493
theorem B4682249 : Blo 972592 4682249 := bstep (se 2 (by rfl) ⟨1755843, by rfl⟩ : syracuseStep 4682249 = 3511687) B3511687
theorem B5272073 : Blo 972592 5272073 := bstep (se 2 (by rfl) ⟨1977027, by rfl⟩ : syracuseStep 5272073 = 3954055) B3954055
theorem B2192201 : Blo 972592 2192201 := bstep (se 2 (by rfl) ⟨822075, by rfl⟩ : syracuseStep 2192201 = 1644151) B1644151
theorem B12645341 : Blo 972592 12645341 := bstep (se 3 (by rfl) ⟨2371001, by rfl⟩ : syracuseStep 12645341 = 4742003) B4742003
theorem B3699827 : Blo 972592 3699827 := bstep (se 1 (by rfl) ⟨2774870, by rfl⟩ : syracuseStep 3699827 = 5549741) B5549741
theorem B2225323 : Blo 972592 2225323 := bstep (se 1 (by rfl) ⟨1668992, by rfl⟩ : syracuseStep 2225323 = 3337985) B3337985
theorem B73037155 : Blo 972592 73037155 := bstep (se 1 (by rfl) ⟨54777866, by rfl⟩ : syracuseStep 73037155 = 109555733) B109555733
theorem B2192993 : Blo 972592 2192993 := bstep (se 2 (by rfl) ⟨822372, by rfl⟩ : syracuseStep 2192993 = 1644745) B1644745
theorem B2193335 : Blo 972592 2193335 := bstep (se 1 (by rfl) ⟨1645001, by rfl⟩ : syracuseStep 2193335 = 3290003) B3290003
theorem B5929453 : Blo 972592 5929453 := bstep (se 3 (by rfl) ⟨1111772, by rfl⟩ : syracuseStep 5929453 = 2223545) B2223545
theorem B2193929 : Blo 972592 2193929 := bstep (se 2 (by rfl) ⟨822723, by rfl⟩ : syracuseStep 2193929 = 1645447) B1645447
theorem B4749857 : Blo 972592 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B31980109 : Blo 972592 31980109 := bstep (se 3 (by rfl) ⟨5996270, by rfl⟩ : syracuseStep 31980109 = 11992541) B11992541
theorem B57834163 : Blo 972592 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B3701497 : Blo 972592 3701497 := bstep (se 2 (by rfl) ⟨1388061, by rfl⟩ : syracuseStep 3701497 = 2776123) B2776123
theorem B2194271 : Blo 972592 2194271 := bstep (se 1 (by rfl) ⟨1645703, by rfl⟩ : syracuseStep 2194271 = 3291407) B3291407
theorem B2194451 : Blo 972592 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B16678061 : Blo 972592 16678061 := bstep (se 3 (by rfl) ⟨3127136, by rfl⟩ : syracuseStep 16678061 = 6254273) B6254273
theorem B2194793 : Blo 972592 2194793 := bstep (se 2 (by rfl) ⟨823047, by rfl⟩ : syracuseStep 2194793 = 1646095) B1646095
theorem B10518103 : Blo 972592 10518103 := bstep (se 1 (by rfl) ⟨7888577, by rfl⟩ : syracuseStep 10518103 = 15777155) B15777155
theorem B2195387 : Blo 972592 2195387 := bstep (se 1 (by rfl) ⟨1646540, by rfl⟩ : syracuseStep 2195387 = 3293081) B3293081
theorem B2195819 : Blo 972592 2195819 := bstep (se 1 (by rfl) ⟨1646864, by rfl⟩ : syracuseStep 2195819 = 3293729) B3293729
theorem B2195963 : Blo 972592 2195963 := bstep (se 1 (by rfl) ⟨1646972, by rfl⟩ : syracuseStep 2195963 = 3293945) B3293945
theorem B4162067 : Blo 972592 4162067 := bstep (se 1 (by rfl) ⟨3121550, by rfl⟩ : syracuseStep 4162067 = 6243101) B6243101
theorem B2196089 : Blo 972592 2196089 := bstep (se 2 (by rfl) ⟨823533, by rfl⟩ : syracuseStep 2196089 = 1647067) B1647067
theorem B2196143 : Blo 972592 2196143 := bstep (se 1 (by rfl) ⟨1647107, by rfl⟩ : syracuseStep 2196143 = 3294215) B3294215
theorem B2196215 : Blo 972592 2196215 := bstep (se 1 (by rfl) ⟨1647161, by rfl⟩ : syracuseStep 2196215 = 3294323) B3294323
theorem B2196395 : Blo 972592 2196395 := bstep (se 1 (by rfl) ⟨1647296, by rfl⟩ : syracuseStep 2196395 = 3294593) B3294593
theorem B2196935 : Blo 972592 2196935 := bstep (se 1 (by rfl) ⟨1647701, by rfl⟩ : syracuseStep 2196935 = 3295403) B3295403
theorem B2197295 : Blo 972592 2197295 := bstep (se 1 (by rfl) ⟨1647971, by rfl⟩ : syracuseStep 2197295 = 3295943) B3295943
theorem B3508055 : Blo 972592 3508055 := bstep (se 1 (by rfl) ⟨2631041, by rfl⟩ : syracuseStep 3508055 = 5262083) B5262083
theorem B8685683 : Blo 972592 8685683 := bstep (se 1 (by rfl) ⟨6514262, by rfl⟩ : syracuseStep 8685683 = 13028525) B13028525
theorem B5540035 : Blo 972592 5540035 := bstep (se 1 (by rfl) ⟨4155026, by rfl⟩ : syracuseStep 5540035 = 8310053) B8310053
theorem B4164169 : Blo 972592 4164169 := bstep (se 2 (by rfl) ⟨1561563, by rfl⟩ : syracuseStep 4164169 = 3123127) B3123127
theorem B7998839 : Blo 972592 7998839 := bstep (se 1 (by rfl) ⟨5999129, by rfl⟩ : syracuseStep 7998839 = 11998259) B11998259
theorem B23662043 : Blo 972592 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B17763907 : Blo 972592 17763907 := bstep (se 1 (by rfl) ⟨13322930, by rfl⟩ : syracuseStep 17763907 = 26645861) B26645861
theorem B1642079 : Blo 972592 1642079 := bstep (se 1 (by rfl) ⟨1231559, by rfl⟩ : syracuseStep 1642079 = 2463119) B2463119
theorem B30412523 : Blo 972592 30412523 := bstep (se 1 (by rfl) ⟨22809392, by rfl⟩ : syracuseStep 30412523 = 45618785) B45618785
theorem B3706631 : Blo 972592 3706631 := bstep (se 1 (by rfl) ⟨2779973, by rfl⟩ : syracuseStep 3706631 = 5559947) B5559947
theorem B1642295 : Blo 972592 1642295 := bstep (se 1 (by rfl) ⟨1231721, by rfl⟩ : syracuseStep 1642295 = 2463443) B2463443
theorem B4755329 : Blo 972592 4755329 := bstep (se 2 (by rfl) ⟨1783248, by rfl⟩ : syracuseStep 4755329 = 3566497) B3566497
theorem B6656431 : Blo 972592 6656431 := bstep (se 1 (by rfl) ⟨4992323, by rfl⟩ : syracuseStep 6656431 = 9984647) B9984647
theorem B2462177 : Blo 972592 2462177 := bstep (se 2 (by rfl) ⟨923316, by rfl⟩ : syracuseStep 2462177 = 1846633) B1846633
theorem B5542451 : Blo 972592 5542451 := bstep (se 1 (by rfl) ⟨4156838, by rfl⟩ : syracuseStep 5542451 = 8313677) B8313677
theorem B1643071 : Blo 972592 1643071 := bstep (se 1 (by rfl) ⟨1232303, by rfl⟩ : syracuseStep 1643071 = 2464607) B2464607
theorem B18748057 : Blo 972592 18748057 := bstep (se 2 (by rfl) ⟨7030521, by rfl⟩ : syracuseStep 18748057 = 14061043) B14061043
theorem B2462683 : Blo 972592 2462683 := bstep (se 1 (by rfl) ⟨1847012, by rfl⟩ : syracuseStep 2462683 = 3694025) B3694025
theorem B10523639 : Blo 972592 10523639 := bstep (se 1 (by rfl) ⟨7892729, by rfl⟩ : syracuseStep 10523639 = 15785459) B15785459
theorem B1643753 : Blo 972592 1643753 := bstep (se 2 (by rfl) ⟨616407, by rfl⟩ : syracuseStep 1643753 = 1232815) B1232815
theorem B2463007 : Blo 972592 2463007 := bstep (se 1 (by rfl) ⟨1847255, by rfl⟩ : syracuseStep 2463007 = 3694511) B3694511
theorem B1643807 : Blo 972592 1643807 := bstep (se 1 (by rfl) ⟨1232855, by rfl⟩ : syracuseStep 1643807 = 2465711) B2465711
theorem B2168201 : Blo 972592 2168201 := bstep (se 2 (by rfl) ⟨813075, by rfl⟩ : syracuseStep 2168201 = 1626151) B1626151
theorem B3118475 : Blo 972592 3118475 := bstep (se 1 (by rfl) ⟨2338856, by rfl⟩ : syracuseStep 3118475 = 4677713) B4677713
theorem B5543909 : Blo 972592 5543909 := bstep (se 4 (by rfl) ⟨519741, by rfl⟩ : syracuseStep 5543909 = 1039483) B1039483
theorem B8329189 : Blo 972592 8329189 := bstep (se 4 (by rfl) ⟨780861, by rfl⟩ : syracuseStep 8329189 = 1561723) B1561723
theorem B4167875 : Blo 972592 4167875 := bstep (se 1 (by rfl) ⟨3125906, by rfl⟩ : syracuseStep 4167875 = 6251813) B6251813
theorem B11868389 : Blo 972592 11868389 := bstep (se 4 (by rfl) ⟨1112661, by rfl⟩ : syracuseStep 11868389 = 2225323) B2225323
theorem B8329463 : Blo 972592 8329463 := bstep (se 1 (by rfl) ⟨6247097, by rfl⟩ : syracuseStep 8329463 = 12494195) B12494195
theorem B2464091 : Blo 972592 2464091 := bstep (se 1 (by rfl) ⟨1848068, by rfl⟩ : syracuseStep 2464091 = 3696137) B3696137
theorem B54073817 : Blo 972592 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B1645177 : Blo 972592 1645177 := bstep (se 2 (by rfl) ⟨616941, by rfl⟩ : syracuseStep 1645177 = 1233883) B1233883
theorem B3283631 : Blo 972592 3283631 := bstep (se 1 (by rfl) ⟨2462723, by rfl⟩ : syracuseStep 3283631 = 4925447) B4925447
theorem B1645231 : Blo 972592 1645231 := bstep (se 1 (by rfl) ⟨1233923, by rfl⟩ : syracuseStep 1645231 = 2467847) B2467847
theorem B5938039 : Blo 972592 5938039 := bstep (se 1 (by rfl) ⟨4453529, by rfl⟩ : syracuseStep 5938039 = 8907059) B8907059
theorem B23731127 : Blo 972592 23731127 := bstep (se 1 (by rfl) ⟨17798345, by rfl⟩ : syracuseStep 23731127 = 35596691) B35596691
theorem B3283955 : Blo 972592 3283955 := bstep (se 1 (by rfl) ⟨2462966, by rfl⟩ : syracuseStep 3283955 = 4925933) B4925933
theorem B3120115 : Blo 972592 3120115 := bstep (se 1 (by rfl) ⟨2340086, by rfl⟩ : syracuseStep 3120115 = 4680173) B4680173
theorem B7412957 : Blo 972592 7412957 := bstep (se 3 (by rfl) ⟨1389929, by rfl⟩ : syracuseStep 7412957 = 2779859) B2779859
theorem B2465063 : Blo 972592 2465063 := bstep (se 1 (by rfl) ⟨1848797, by rfl⟩ : syracuseStep 2465063 = 3697595) B3697595
theorem B1875323 : Blo 972592 1875323 := bstep (se 1 (by rfl) ⟨1406492, by rfl⟩ : syracuseStep 1875323 = 2812985) B2812985
theorem B3284495 : Blo 972592 3284495 := bstep (se 1 (by rfl) ⟨2463371, by rfl⟩ : syracuseStep 3284495 = 4926743) B4926743
theorem B8888663 : Blo 972592 8888663 := bstep (se 1 (by rfl) ⟨6666497, by rfl⟩ : syracuseStep 8888663 = 13332995) B13332995
theorem B3121499 : Blo 972592 3121499 := bstep (se 1 (by rfl) ⟨2341124, by rfl⟩ : syracuseStep 3121499 = 4682249) B4682249
theorem B3514715 : Blo 972592 3514715 := bstep (se 1 (by rfl) ⟨2636036, by rfl⟩ : syracuseStep 3514715 = 5272073) B5272073
theorem B1646939 : Blo 972592 1646939 := bstep (se 1 (by rfl) ⟨1235204, by rfl⟩ : syracuseStep 1646939 = 2470409) B2470409
theorem B1646959 : Blo 972592 1646959 := bstep (se 1 (by rfl) ⟨1235219, by rfl⟩ : syracuseStep 1646959 = 2470439) B2470439
theorem B6234569 : Blo 972592 6234569 := bstep (se 2 (by rfl) ⟨2337963, by rfl⟩ : syracuseStep 6234569 = 4675927) B4675927
theorem B3285575 : Blo 972592 3285575 := bstep (se 1 (by rfl) ⟨2464181, by rfl⟩ : syracuseStep 3285575 = 4928363) B4928363
theorem B1647175 : Blo 972592 1647175 := bstep (se 1 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 1647175 = 2470763) B2470763
theorem B7905937 : Blo 972592 7905937 := bstep (se 2 (by rfl) ⟨2964726, by rfl⟩ : syracuseStep 7905937 = 5929453) B5929453
theorem B8430227 : Blo 972592 8430227 := bstep (se 1 (by rfl) ⟨6322670, by rfl⟩ : syracuseStep 8430227 = 12645341) B12645341
theorem B8331923 : Blo 972592 8331923 := bstep (se 1 (by rfl) ⟨6248942, by rfl⟩ : syracuseStep 8331923 = 12497885) B12497885
theorem B2466551 : Blo 972592 2466551 := bstep (se 1 (by rfl) ⟨1849913, by rfl⟩ : syracuseStep 2466551 = 3699827) B3699827
theorem B42640145 : Blo 972592 42640145 := bstep (se 2 (by rfl) ⟨15990054, by rfl⟩ : syracuseStep 42640145 = 31980109) B31980109
theorem B77112217 : Blo 972592 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B1975195 : Blo 972592 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B3286007 : Blo 972592 3286007 := bstep (se 1 (by rfl) ⟨2464505, by rfl⟩ : syracuseStep 3286007 = 4929011) B4929011
theorem B1647607 : Blo 972592 1647607 := bstep (se 1 (by rfl) ⟨1235705, by rfl⟩ : syracuseStep 1647607 = 2471411) B2471411
theorem B2958535 : Blo 972592 2958535 := bstep (se 1 (by rfl) ⟨2218901, by rfl⟩ : syracuseStep 2958535 = 4437803) B4437803
theorem B1647911 : Blo 972592 1647911 := bstep (se 1 (by rfl) ⟨1235933, by rfl⟩ : syracuseStep 1647911 = 2471867) B2471867
theorem B2467169 : Blo 972592 2467169 := bstep (se 2 (by rfl) ⟨925188, by rfl⟩ : syracuseStep 2467169 = 1850377) B1850377
theorem B2958731 : Blo 972592 2958731 := bstep (se 1 (by rfl) ⟨2219048, by rfl⟩ : syracuseStep 2958731 = 4438097) B4438097
theorem B4924961 : Blo 972592 4924961 := bstep (se 2 (by rfl) ⟨1846860, by rfl⟩ : syracuseStep 4924961 = 3693721) B3693721
theorem B3286871 : Blo 972592 3286871 := bstep (se 1 (by rfl) ⟨2465153, by rfl⟩ : syracuseStep 3286871 = 4930307) B4930307
theorem B11118707 : Blo 972592 11118707 := bstep (se 1 (by rfl) ⟨8339030, by rfl⟩ : syracuseStep 11118707 = 16678061) B16678061
theorem B2337049 : Blo 972592 2337049 := bstep (se 2 (by rfl) ⟨876393, by rfl⟩ : syracuseStep 2337049 = 1752787) B1752787
theorem B11250049 : Blo 972592 11250049 := bstep (se 2 (by rfl) ⟨4218768, by rfl⟩ : syracuseStep 11250049 = 8437537) B8437537
theorem B2468627 : Blo 972592 2468627 := bstep (se 1 (by rfl) ⟨1851470, by rfl⟩ : syracuseStep 2468627 = 3702941) B3702941
theorem B11873155 : Blo 972592 11873155 := bstep (se 1 (by rfl) ⟨8904866, by rfl⟩ : syracuseStep 11873155 = 17809733) B17809733
theorem B3287951 : Blo 972592 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B2468839 : Blo 972592 2468839 := bstep (se 1 (by rfl) ⟨1851629, by rfl⟩ : syracuseStep 2468839 = 3703259) B3703259
theorem B9120883 : Blo 972592 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B9350315 : Blo 972592 9350315 := bstep (se 1 (by rfl) ⟨7012736, by rfl⟩ : syracuseStep 9350315 = 14025473) B14025473
theorem B2469113 : Blo 972592 2469113 := bstep (se 2 (by rfl) ⟨925917, by rfl⟩ : syracuseStep 2469113 = 1851835) B1851835
theorem B3124831 : Blo 972592 3124831 := bstep (se 1 (by rfl) ⟨2343623, by rfl⟩ : syracuseStep 3124831 = 4687247) B4687247
theorem B1388335 : Blo 972592 1388335 := bstep (se 1 (by rfl) ⟨1041251, by rfl⟩ : syracuseStep 1388335 = 2082503) B2082503
theorem B2502505 : Blo 972592 2502505 := bstep (se 2 (by rfl) ⟨938439, by rfl⟩ : syracuseStep 2502505 = 1876879) B1876879
theorem B2469761 : Blo 972592 2469761 := bstep (se 2 (by rfl) ⟨926160, by rfl⟩ : syracuseStep 2469761 = 1852321) B1852321
theorem B3289193 : Blo 972592 3289193 := bstep (se 2 (by rfl) ⟨1233447, by rfl⟩ : syracuseStep 3289193 = 2466895) B2466895
theorem B3125729 : Blo 972592 3125729 := bstep (se 2 (by rfl) ⟨1172148, by rfl⟩ : syracuseStep 3125729 = 2344297) B2344297
theorem B2503163 : Blo 972592 2503163 := bstep (se 1 (by rfl) ⟨1877372, by rfl⟩ : syracuseStep 2503163 = 3754745) B3754745
theorem B1094215 : Blo 972592 1094215 := bstep (se 1 (by rfl) ⟨820661, by rfl⟩ : syracuseStep 1094215 = 1641323) B1641323
theorem B2470571 : Blo 972592 2470571 := bstep (se 1 (by rfl) ⟨1852928, by rfl⟩ : syracuseStep 2470571 = 3705857) B3705857
theorem B2339663 : Blo 972592 2339663 := bstep (se 1 (by rfl) ⟨1754747, by rfl⟩ : syracuseStep 2339663 = 3509495) B3509495
theorem B1782607 : Blo 972592 1782607 := bstep (se 1 (by rfl) ⟨1336955, by rfl⟩ : syracuseStep 1782607 = 2673911) B2673911
theorem B3290057 : Blo 972592 3290057 := bstep (se 2 (by rfl) ⟨1233771, by rfl⟩ : syracuseStep 3290057 = 2467543) B2467543
theorem B3290327 : Blo 972592 3290327 := bstep (se 1 (by rfl) ⟨2467745, by rfl⟩ : syracuseStep 3290327 = 4935491) B4935491
theorem B3519703 : Blo 972592 3519703 := bstep (se 1 (by rfl) ⟨2639777, by rfl⟩ : syracuseStep 3519703 = 5279555) B5279555
theorem B2340193 : Blo 972592 2340193 := bstep (se 2 (by rfl) ⟨877572, by rfl⟩ : syracuseStep 2340193 = 1755145) B1755145
theorem B31602059 : Blo 972592 31602059 := bstep (se 1 (by rfl) ⟨23701544, by rfl⟩ : syracuseStep 31602059 = 47403089) B47403089
theorem B1095079 : Blo 972592 1095079 := bstep (se 1 (by rfl) ⟨821309, by rfl⟩ : syracuseStep 1095079 = 1642619) B1642619
theorem B9385409 : Blo 972592 9385409 := bstep (se 2 (by rfl) ⟨3519528, by rfl⟩ : syracuseStep 9385409 = 7039057) B7039057
theorem B2471431 : Blo 972592 2471431 := bstep (se 1 (by rfl) ⟨1853573, by rfl⟩ : syracuseStep 2471431 = 3707147) B3707147
theorem B4929335 : Blo 972592 4929335 := bstep (se 1 (by rfl) ⟨3697001, by rfl⟩ : syracuseStep 4929335 = 7394003) B7394003
theorem B2471735 : Blo 972592 2471735 := bstep (se 1 (by rfl) ⟨1853801, by rfl⟩ : syracuseStep 2471735 = 3707603) B3707603
theorem B1095655 : Blo 972592 1095655 := bstep (se 1 (by rfl) ⟨821741, by rfl⟩ : syracuseStep 1095655 = 1643483) B1643483
theorem B4929821 : Blo 972592 4929821 := bstep (se 3 (by rfl) ⟨924341, by rfl⟩ : syracuseStep 4929821 = 1848683) B1848683
theorem B3292379 : Blo 972592 3292379 := bstep (se 1 (by rfl) ⟨2469284, by rfl⟩ : syracuseStep 3292379 = 4938569) B4938569
theorem B2637095 : Blo 972592 2637095 := bstep (se 1 (by rfl) ⟨1977821, by rfl⟩ : syracuseStep 2637095 = 3955643) B3955643
theorem B50609609 : Blo 972592 50609609 := bstep (se 2 (by rfl) ⟨18978603, by rfl⟩ : syracuseStep 50609609 = 37957207) B37957207
theorem B1097311 : Blo 972592 1097311 := bstep (se 1 (by rfl) ⟨822983, by rfl⟩ : syracuseStep 1097311 = 1645967) B1645967
theorem B8339273 : Blo 972592 8339273 := bstep (se 2 (by rfl) ⟨3127227, by rfl⟩ : syracuseStep 8339273 = 6254455) B6254455
theorem B6242177 : Blo 972592 6242177 := bstep (se 2 (by rfl) ⟨2340816, by rfl⟩ : syracuseStep 6242177 = 4681633) B4681633
theorem B4931603 : Blo 972592 4931603 := bstep (se 1 (by rfl) ⟨3698702, by rfl⟩ : syracuseStep 4931603 = 7397405) B7397405
theorem B3293243 : Blo 972592 3293243 := bstep (se 1 (by rfl) ⟨2469932, by rfl⟩ : syracuseStep 3293243 = 4939865) B4939865
theorem B3293513 : Blo 972592 3293513 := bstep (se 2 (by rfl) ⟨1235067, by rfl⟩ : syracuseStep 3293513 = 2470135) B2470135
theorem B6341267 : Blo 972592 6341267 := bstep (se 1 (by rfl) ⟨4755950, by rfl⟩ : syracuseStep 6341267 = 9511901) B9511901
theorem B22495927 : Blo 972592 22495927 := bstep (se 1 (by rfl) ⟨16871945, by rfl⟩ : syracuseStep 22495927 = 33743891) B33743891
theorem B1458911 : Blo 972592 1458911 := bstep (se 1 (by rfl) ⟨1094183, by rfl⟩ : syracuseStep 1458911 = 2188367) B2188367
theorem B1098463 : Blo 972592 1098463 := bstep (se 1 (by rfl) ⟨823847, by rfl⟩ : syracuseStep 1098463 = 1647695) B1647695
theorem B1459175 : Blo 972592 1459175 := bstep (se 1 (by rfl) ⟨1094381, by rfl⟩ : syracuseStep 1459175 = 2188763) B2188763
theorem B1459433 : Blo 972592 1459433 := bstep (se 2 (by rfl) ⟨547287, by rfl⟩ : syracuseStep 1459433 = 1094575) B1094575
theorem B1459487 : Blo 972592 1459487 := bstep (se 1 (by rfl) ⟨1094615, by rfl⟩ : syracuseStep 1459487 = 2189231) B2189231
theorem B9356579 : Blo 972592 9356579 := bstep (se 1 (by rfl) ⟨7017434, by rfl⟩ : syracuseStep 9356579 = 14034869) B14034869
theorem B1852769 : Blo 972592 1852769 := bstep (se 2 (by rfl) ⟨694788, by rfl⟩ : syracuseStep 1852769 = 1389577) B1389577
theorem B2770337 : Blo 972592 2770337 := bstep (se 2 (by rfl) ⟨1038876, by rfl⟩ : syracuseStep 2770337 = 2077753) B2077753
theorem B1459655 : Blo 972592 1459655 := bstep (se 1 (by rfl) ⟨1094741, by rfl⟩ : syracuseStep 1459655 = 2189483) B2189483
theorem B1460009 : Blo 972592 1460009 := bstep (se 2 (by rfl) ⟨547503, by rfl⟩ : syracuseStep 1460009 = 1095007) B1095007
theorem B1754921 : Blo 972592 1754921 := bstep (se 2 (by rfl) ⟨658095, by rfl⟩ : syracuseStep 1754921 = 1316191) B1316191
theorem B1460015 : Blo 972592 1460015 := bstep (se 1 (by rfl) ⟨1095011, by rfl⟩ : syracuseStep 1460015 = 2190023) B2190023
theorem B2770793 : Blo 972592 2770793 := bstep (se 2 (by rfl) ⟨1039047, by rfl⟩ : syracuseStep 2770793 = 2078095) B2078095
theorem B5556073 : Blo 972592 5556073 := bstep (se 2 (by rfl) ⟨2083527, by rfl⟩ : syracuseStep 5556073 = 4167055) B4167055
theorem B1460489 : Blo 972592 1460489 := bstep (se 2 (by rfl) ⟨547683, by rfl⟩ : syracuseStep 1460489 = 1095367) B1095367
theorem B1231195 : Blo 972592 1231195 := bstep (se 1 (by rfl) ⟨923396, by rfl⟩ : syracuseStep 1231195 = 1846793) B1846793
theorem B1460591 : Blo 972592 1460591 := bstep (se 1 (by rfl) ⟨1095443, by rfl⟩ : syracuseStep 1460591 = 2190887) B2190887
theorem B5261735 : Blo 972592 5261735 := bstep (se 1 (by rfl) ⟨3946301, by rfl⟩ : syracuseStep 5261735 = 7892603) B7892603
theorem B1460807 : Blo 972592 1460807 := bstep (se 1 (by rfl) ⟨1095605, by rfl⟩ : syracuseStep 1460807 = 2191211) B2191211
theorem B14076503 : Blo 972592 14076503 := bstep (se 1 (by rfl) ⟨10557377, by rfl⟩ : syracuseStep 14076503 = 21114755) B21114755
theorem B1460843 : Blo 972592 1460843 := bstep (se 1 (by rfl) ⟨1095632, by rfl⟩ : syracuseStep 1460843 = 2191265) B2191265
theorem B1461071 : Blo 972592 1461071 := bstep (se 1 (by rfl) ⟨1095803, by rfl⟩ : syracuseStep 1461071 = 2191607) B2191607
theorem B4934519 : Blo 972592 4934519 := bstep (se 1 (by rfl) ⟨3700889, by rfl⟩ : syracuseStep 4934519 = 7401779) B7401779
theorem B1461467 : Blo 972592 1461467 := bstep (se 1 (by rfl) ⟨1096100, by rfl⟩ : syracuseStep 1461467 = 2192201) B2192201
theorem B1232167 : Blo 972592 1232167 := bstep (se 1 (by rfl) ⟨924125, by rfl⟩ : syracuseStep 1232167 = 1848251) B1848251
theorem B1461641 : Blo 972592 1461641 := bstep (se 2 (by rfl) ⟨548115, by rfl⟩ : syracuseStep 1461641 = 1096231) B1096231
theorem B1232491 : Blo 972592 1232491 := bstep (se 1 (by rfl) ⟨924368, by rfl⟩ : syracuseStep 1232491 = 1848737) B1848737
theorem B4935329 : Blo 972592 4935329 := bstep (se 2 (by rfl) ⟨1850748, by rfl⟩ : syracuseStep 4935329 = 3701497) B3701497
theorem B14077651 : Blo 972592 14077651 := bstep (se 1 (by rfl) ⟨10558238, by rfl⟩ : syracuseStep 14077651 = 21116477) B21116477
theorem B1461995 : Blo 972592 1461995 := bstep (se 1 (by rfl) ⟨1096496, by rfl⟩ : syracuseStep 1461995 = 2192993) B2192993
theorem B1462223 : Blo 972592 1462223 := bstep (se 1 (by rfl) ⟨1096667, by rfl⟩ : syracuseStep 1462223 = 2193335) B2193335
theorem B10670339 : Blo 972592 10670339 := bstep (se 1 (by rfl) ⟨8002754, by rfl⟩ : syracuseStep 10670339 = 16005509) B16005509
theorem B1462619 : Blo 972592 1462619 := bstep (se 1 (by rfl) ⟨1096964, by rfl⟩ : syracuseStep 1462619 = 2193929) B2193929
theorem B3166571 : Blo 972592 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B1462847 : Blo 972592 1462847 := bstep (se 1 (by rfl) ⟨1097135, by rfl⟩ : syracuseStep 1462847 = 2194271) B2194271
theorem B3560057 : Blo 972592 3560057 := bstep (se 2 (by rfl) ⟨1335021, by rfl⟩ : syracuseStep 3560057 = 2670043) B2670043
theorem B1462967 : Blo 972592 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B1463195 : Blo 972592 1463195 := bstep (se 1 (by rfl) ⟨1097396, by rfl⟩ : syracuseStep 1463195 = 2194793) B2194793
theorem B133551179 : Blo 972592 133551179 := bstep (se 1 (by rfl) ⟨100163384, by rfl⟩ : syracuseStep 133551179 = 200326769) B200326769
theorem B16897241 : Blo 972592 16897241 := bstep (se 2 (by rfl) ⟨6336465, by rfl⟩ : syracuseStep 16897241 = 12672931) B12672931
theorem B5002489 : Blo 972592 5002489 := bstep (se 2 (by rfl) ⟨1875933, by rfl⟩ : syracuseStep 5002489 = 3751867) B3751867
theorem B1234207 : Blo 972592 1234207 := bstep (se 1 (by rfl) ⟨925655, by rfl⟩ : syracuseStep 1234207 = 1851311) B1851311
theorem B1463591 : Blo 972592 1463591 := bstep (se 1 (by rfl) ⟨1097693, by rfl⟩ : syracuseStep 1463591 = 2195387) B2195387
theorem B3757421 : Blo 972592 3757421 := bstep (se 3 (by rfl) ⟨704516, by rfl⟩ : syracuseStep 3757421 = 1409033) B1409033
theorem B1463675 : Blo 972592 1463675 := bstep (se 1 (by rfl) ⟨1097756, by rfl⟩ : syracuseStep 1463675 = 2195513) B2195513
theorem B1463801 : Blo 972592 1463801 := bstep (se 2 (by rfl) ⟨548925, by rfl⟩ : syracuseStep 1463801 = 1097851) B1097851
theorem B4937273 : Blo 972592 4937273 := bstep (se 2 (by rfl) ⟨1851477, by rfl⟩ : syracuseStep 4937273 = 3702955) B3702955
theorem B1463903 : Blo 972592 1463903 := bstep (se 1 (by rfl) ⟨1097927, by rfl⟩ : syracuseStep 1463903 = 2195855) B2195855
theorem B6248123 : Blo 972592 6248123 := bstep (se 1 (by rfl) ⟨4686092, by rfl⟩ : syracuseStep 6248123 = 9372185) B9372185
theorem B12474101 : Blo 972592 12474101 := bstep (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) B1169447
theorem B42653441 : Blo 972592 42653441 := bstep (se 2 (by rfl) ⟨15995040, by rfl⟩ : syracuseStep 42653441 = 31990081) B31990081
theorem B35608369 : Blo 972592 35608369 := bstep (se 2 (by rfl) ⟨13353138, by rfl⟩ : syracuseStep 35608369 = 26706277) B26706277
theorem B1464119 : Blo 972592 1464119 := bstep (se 1 (by rfl) ⟨1098089, by rfl⟩ : syracuseStep 1464119 = 2196179) B2196179
theorem B972699 : Blo 972592 972699 := bstep (se 1 (by rfl) ⟨729524, by rfl⟩ : syracuseStep 972699 = 1459049) B1459049
theorem B972751 : Blo 972592 972751 := bstep (se 1 (by rfl) ⟨729563, by rfl⟩ : syracuseStep 972751 = 1459127) B1459127
theorem B972775 : Blo 972592 972775 := bstep (se 1 (by rfl) ⟨729581, by rfl⟩ : syracuseStep 972775 = 1459163) B1459163
theorem B121690133 : Blo 972592 121690133 := bstep (se 6 (by rfl) ⟨2852112, by rfl⟩ : syracuseStep 121690133 = 5704225) B5704225
theorem B37476431 : Blo 972592 37476431 := bstep (se 1 (by rfl) ⟨28107323, by rfl⟩ : syracuseStep 37476431 = 56214647) B56214647
theorem B1464425 : Blo 972592 1464425 := bstep (se 2 (by rfl) ⟨549159, by rfl⟩ : syracuseStep 1464425 = 1098319) B1098319
theorem B2775293 : Blo 972592 2775293 := bstep (se 3 (by rfl) ⟨520367, by rfl⟩ : syracuseStep 2775293 = 1040735) B1040735
theorem B973087 : Blo 972592 973087 := bstep (se 1 (by rfl) ⟨729815, by rfl⟩ : syracuseStep 973087 = 1459631) B1459631
theorem B973147 : Blo 972592 973147 := bstep (se 1 (by rfl) ⟨729860, by rfl⟩ : syracuseStep 973147 = 1459721) B1459721
theorem B973167 : Blo 972592 973167 := bstep (se 1 (by rfl) ⟨729875, by rfl⟩ : syracuseStep 973167 = 1459751) B1459751
theorem B973223 : Blo 972592 973223 := bstep (se 1 (by rfl) ⟨729917, by rfl⟩ : syracuseStep 973223 = 1459835) B1459835
theorem B1464743 : Blo 972592 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B1038791 : Blo 972592 1038791 := bstep (se 1 (by rfl) ⟨779093, by rfl⟩ : syracuseStep 1038791 = 1558187) B1558187
theorem B973307 : Blo 972592 973307 := bstep (se 1 (by rfl) ⟨729980, by rfl⟩ : syracuseStep 973307 = 1459961) B1459961
theorem B1464827 : Blo 972592 1464827 := bstep (se 1 (by rfl) ⟨1098620, by rfl⟩ : syracuseStep 1464827 = 2197241) B2197241
theorem B973375 : Blo 972592 973375 := bstep (se 1 (by rfl) ⟨730031, by rfl⟩ : syracuseStep 973375 = 1460063) B1460063
theorem B973383 : Blo 972592 973383 := bstep (se 1 (by rfl) ⟨730037, by rfl⟩ : syracuseStep 973383 = 1460075) B1460075
theorem B7395947 : Blo 972592 7395947 := bstep (se 1 (by rfl) ⟨5546960, by rfl⟩ : syracuseStep 7395947 = 11093921) B11093921
theorem B18766511 : Blo 972592 18766511 := bstep (se 1 (by rfl) ⟨14074883, by rfl⟩ : syracuseStep 18766511 = 28149767) B28149767
theorem B973535 : Blo 972592 973535 := bstep (se 1 (by rfl) ⟨730151, by rfl⟩ : syracuseStep 973535 = 1460303) B1460303
theorem B973615 : Blo 972592 973615 := bstep (se 1 (by rfl) ⟨730211, by rfl⟩ : syracuseStep 973615 = 1460423) B1460423
theorem B973723 : Blo 972592 973723 := bstep (se 1 (by rfl) ⟨730292, by rfl⟩ : syracuseStep 973723 = 1460585) B1460585
theorem B1563563 : Blo 972592 1563563 := bstep (se 1 (by rfl) ⟨1172672, by rfl⟩ : syracuseStep 1563563 = 2345345) B2345345
theorem B973775 : Blo 972592 973775 := bstep (se 1 (by rfl) ⟨730331, by rfl⟩ : syracuseStep 973775 = 1460663) B1460663
theorem B1268687 : Blo 972592 1268687 := bstep (se 1 (by rfl) ⟨951515, by rfl⟩ : syracuseStep 1268687 = 1903031) B1903031
theorem B973799 : Blo 972592 973799 := bstep (se 1 (by rfl) ⟨730349, by rfl⟩ : syracuseStep 973799 = 1460699) B1460699
theorem B3693707 : Blo 972592 3693707 := bstep (se 1 (by rfl) ⟨2770280, by rfl⟩ : syracuseStep 3693707 = 5540561) B5540561
theorem B974111 : Blo 972592 974111 := bstep (se 1 (by rfl) ⟨730583, by rfl⟩ : syracuseStep 974111 = 1461167) B1461167
theorem B2776351 : Blo 972592 2776351 := bstep (se 1 (by rfl) ⟨2082263, by rfl⟩ : syracuseStep 2776351 = 4164527) B4164527
theorem B974171 : Blo 972592 974171 := bstep (se 1 (by rfl) ⟨730628, by rfl⟩ : syracuseStep 974171 = 1461257) B1461257
theorem B12475741 : Blo 972592 12475741 := bstep (se 3 (by rfl) ⟨2339201, by rfl⟩ : syracuseStep 12475741 = 4678403) B4678403
theorem B974191 : Blo 972592 974191 := bstep (se 1 (by rfl) ⟨730643, by rfl⟩ : syracuseStep 974191 = 1461287) B1461287
theorem B974247 : Blo 972592 974247 := bstep (se 1 (by rfl) ⟨730685, by rfl⟩ : syracuseStep 974247 = 1461371) B1461371
theorem B974331 : Blo 972592 974331 := bstep (se 1 (by rfl) ⟨730748, by rfl⟩ : syracuseStep 974331 = 1461497) B1461497
theorem B8314427 : Blo 972592 8314427 := bstep (se 1 (by rfl) ⟨6235820, by rfl⟩ : syracuseStep 8314427 = 12471641) B12471641
theorem B974399 : Blo 972592 974399 := bstep (se 1 (by rfl) ⟨730799, by rfl⟩ : syracuseStep 974399 = 1461599) B1461599
theorem B974407 : Blo 972592 974407 := bstep (se 1 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 974407 = 1461611) B1461611
theorem B4939379 : Blo 972592 4939379 := bstep (se 1 (by rfl) ⟨3704534, by rfl⟩ : syracuseStep 4939379 = 7409069) B7409069
theorem B974559 : Blo 972592 974559 := bstep (se 1 (by rfl) ⟨730919, by rfl⟩ : syracuseStep 974559 = 1461839) B1461839
theorem B18013985 : Blo 972592 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B974639 : Blo 972592 974639 := bstep (se 1 (by rfl) ⟨730979, by rfl⟩ : syracuseStep 974639 = 1461959) B1461959
theorem B974747 : Blo 972592 974747 := bstep (se 1 (by rfl) ⟨731060, by rfl⟩ : syracuseStep 974747 = 1462121) B1462121
theorem B974799 : Blo 972592 974799 := bstep (se 1 (by rfl) ⟨731099, by rfl⟩ : syracuseStep 974799 = 1462199) B1462199
theorem B1040359 : Blo 972592 1040359 := bstep (se 1 (by rfl) ⟨780269, by rfl⟩ : syracuseStep 1040359 = 1560539) B1560539
theorem B974823 : Blo 972592 974823 := bstep (se 1 (by rfl) ⟨731117, by rfl⟩ : syracuseStep 974823 = 1462235) B1462235
theorem B14049287 : Blo 972592 14049287 := bstep (se 1 (by rfl) ⟨10536965, by rfl⟩ : syracuseStep 14049287 = 21073931) B21073931
theorem B2809961 : Blo 972592 2809961 := bstep (se 2 (by rfl) ⟨1053735, by rfl⟩ : syracuseStep 2809961 = 2107471) B2107471
theorem B975135 : Blo 972592 975135 := bstep (se 1 (by rfl) ⟨731351, by rfl⟩ : syracuseStep 975135 = 1462703) B1462703
theorem B975195 : Blo 972592 975195 := bstep (se 1 (by rfl) ⟨731396, by rfl⟩ : syracuseStep 975195 = 1462793) B1462793
theorem B975215 : Blo 972592 975215 := bstep (se 1 (by rfl) ⟨731411, by rfl⟩ : syracuseStep 975215 = 1462823) B1462823
theorem B1040807 : Blo 972592 1040807 := bstep (se 1 (by rfl) ⟨780605, by rfl⟩ : syracuseStep 1040807 = 1561211) B1561211
theorem B975271 : Blo 972592 975271 := bstep (se 1 (by rfl) ⟨731453, by rfl⟩ : syracuseStep 975271 = 1462907) B1462907
theorem B4219337 : Blo 972592 4219337 := bstep (se 2 (by rfl) ⟨1582251, by rfl⟩ : syracuseStep 4219337 = 3164503) B3164503
theorem B975355 : Blo 972592 975355 := bstep (se 1 (by rfl) ⟨731516, by rfl⟩ : syracuseStep 975355 = 1463033) B1463033
theorem B975423 : Blo 972592 975423 := bstep (se 1 (by rfl) ⟨731567, by rfl⟩ : syracuseStep 975423 = 1463135) B1463135
theorem B975431 : Blo 972592 975431 := bstep (se 1 (by rfl) ⟨731573, by rfl⟩ : syracuseStep 975431 = 1463147) B1463147
theorem B4678327 : Blo 972592 4678327 := bstep (se 1 (by rfl) ⟨3508745, by rfl⟩ : syracuseStep 4678327 = 7017491) B7017491
theorem B975583 : Blo 972592 975583 := bstep (se 1 (by rfl) ⟨731687, by rfl⟩ : syracuseStep 975583 = 1463375) B1463375
theorem B975663 : Blo 972592 975663 := bstep (se 1 (by rfl) ⟨731747, by rfl⟩ : syracuseStep 975663 = 1463495) B1463495
theorem B2777935 : Blo 972592 2777935 := bstep (se 1 (by rfl) ⟨2083451, by rfl⟩ : syracuseStep 2777935 = 4166903) B4166903
theorem B975771 : Blo 972592 975771 := bstep (se 1 (by rfl) ⟨731828, by rfl⟩ : syracuseStep 975771 = 1463657) B1463657
theorem B975823 : Blo 972592 975823 := bstep (se 1 (by rfl) ⟨731867, by rfl⟩ : syracuseStep 975823 = 1463735) B1463735
theorem B975847 : Blo 972592 975847 := bstep (se 1 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 975847 = 1463771) B1463771
theorem B2188385 : Blo 972592 2188385 := bstep (se 2 (by rfl) ⟨820644, by rfl⟩ : syracuseStep 2188385 = 1641289) B1641289
theorem B2778209 : Blo 972592 2778209 := bstep (se 2 (by rfl) ⟨1041828, by rfl⟩ : syracuseStep 2778209 = 2083657) B2083657
theorem B4940999 : Blo 972592 4940999 := bstep (se 1 (by rfl) ⟨3705749, by rfl⟩ : syracuseStep 4940999 = 7411499) B7411499
theorem B976159 : Blo 972592 976159 := bstep (se 1 (by rfl) ⟨732119, by rfl⟩ : syracuseStep 976159 = 1464239) B1464239
theorem B2188583 : Blo 972592 2188583 := bstep (se 1 (by rfl) ⟨1641437, by rfl⟩ : syracuseStep 2188583 = 3282875) B3282875
theorem B976219 : Blo 972592 976219 := bstep (se 1 (by rfl) ⟨732164, by rfl⟩ : syracuseStep 976219 = 1464329) B1464329
theorem B4941161 : Blo 972592 4941161 := bstep (se 2 (by rfl) ⟨1852935, by rfl⟩ : syracuseStep 4941161 = 3705871) B3705871
theorem B976239 : Blo 972592 976239 := bstep (se 1 (by rfl) ⟨732179, by rfl⟩ : syracuseStep 976239 = 1464359) B1464359
theorem B976295 : Blo 972592 976295 := bstep (se 1 (by rfl) ⟨732221, by rfl⟩ : syracuseStep 976295 = 1464443) B1464443
theorem B976379 : Blo 972592 976379 := bstep (se 1 (by rfl) ⟨732284, by rfl⟩ : syracuseStep 976379 = 1464569) B1464569
theorem B976447 : Blo 972592 976447 := bstep (se 1 (by rfl) ⟨732335, by rfl⟩ : syracuseStep 976447 = 1464671) B1464671
theorem B976455 : Blo 972592 976455 := bstep (se 1 (by rfl) ⟨732341, by rfl⟩ : syracuseStep 976455 = 1464683) B1464683
theorem B2188961 : Blo 972592 2188961 := bstep (se 2 (by rfl) ⟨820860, by rfl⟩ : syracuseStep 2188961 = 1641721) B1641721
theorem B3335867 : Blo 972592 3335867 := bstep (se 1 (by rfl) ⟨2501900, by rfl⟩ : syracuseStep 3335867 = 5003801) B5003801
theorem B5269303 : Blo 972592 5269303 := bstep (se 1 (by rfl) ⟨3951977, by rfl⟩ : syracuseStep 5269303 = 7903955) B7903955
theorem B2189321 : Blo 972592 2189321 := bstep (se 2 (by rfl) ⟨820995, by rfl⟩ : syracuseStep 2189321 = 1641991) B1641991
theorem B2189735 : Blo 972592 2189735 := bstep (se 1 (by rfl) ⟨1642301, by rfl⟩ : syracuseStep 2189735 = 3284603) B3284603
theorem B2189843 : Blo 972592 2189843 := bstep (se 1 (by rfl) ⟨1642382, by rfl⟩ : syracuseStep 2189843 = 3284765) B3284765
theorem B2189897 : Blo 972592 2189897 := bstep (se 2 (by rfl) ⟨821211, by rfl⟩ : syracuseStep 2189897 = 1642423) B1642423
theorem B5204587 : Blo 972592 5204587 := bstep (se 1 (by rfl) ⟨3903440, by rfl⟩ : syracuseStep 5204587 = 7806881) B7806881
theorem B2222815 : Blo 972592 2222815 := bstep (se 1 (by rfl) ⟨1667111, by rfl⟩ : syracuseStep 2222815 = 3334223) B3334223
theorem B3697427 : Blo 972592 3697427 := bstep (se 1 (by rfl) ⟨2773070, by rfl⟩ : syracuseStep 3697427 = 5546141) B5546141
theorem B16673687 : Blo 972592 16673687 := bstep (se 1 (by rfl) ⟨12505265, by rfl⟩ : syracuseStep 16673687 = 25010531) B25010531
theorem B2190311 : Blo 972592 2190311 := bstep (se 1 (by rfl) ⟨1642733, by rfl⟩ : syracuseStep 2190311 = 3285467) B3285467
theorem B3697883 : Blo 972592 3697883 := bstep (se 1 (by rfl) ⟨2773412, by rfl⟩ : syracuseStep 3697883 = 5546825) B5546825
theorem B4156703 : Blo 972592 4156703 := bstep (se 1 (by rfl) ⟨3117527, by rfl⟩ : syracuseStep 4156703 = 6235055) B6235055
theorem B2190689 : Blo 972592 2190689 := bstep (se 2 (by rfl) ⟨821508, by rfl⟩ : syracuseStep 2190689 = 1643017) B1643017
theorem B4681097 : Blo 972592 4681097 := bstep (se 2 (by rfl) ⟨1755411, by rfl⟩ : syracuseStep 4681097 = 3510823) B3510823
theorem B2190779 : Blo 972592 2190779 := bstep (se 1 (by rfl) ⟨1643084, by rfl⟩ : syracuseStep 2190779 = 3286169) B3286169
theorem B2190905 : Blo 972592 2190905 := bstep (se 2 (by rfl) ⟨821589, by rfl⟩ : syracuseStep 2190905 = 1643179) B1643179
theorem B9531341 : Blo 972592 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B2191571 : Blo 972592 2191571 := bstep (se 1 (by rfl) ⟨1643678, by rfl⟩ : syracuseStep 2191571 = 3287357) B3287357
theorem B2191625 : Blo 972592 2191625 := bstep (se 2 (by rfl) ⟨821859, by rfl⟩ : syracuseStep 2191625 = 1643719) B1643719
theorem B3338603 : Blo 972592 3338603 := bstep (se 1 (by rfl) ⟨2503952, by rfl⟩ : syracuseStep 3338603 = 5007905) B5007905
theorem B97382873 : Blo 972592 97382873 := bstep (se 2 (by rfl) ⟨36518577, by rfl⟩ : syracuseStep 97382873 = 73037155) B73037155
theorem B2191841 : Blo 972592 2191841 := bstep (se 2 (by rfl) ⟨821940, by rfl⟩ : syracuseStep 2191841 = 1643881) B1643881
theorem B12481073 : Blo 972592 12481073 := bstep (se 2 (by rfl) ⟨4680402, by rfl⟩ : syracuseStep 12481073 = 9360805) B9360805
theorem B6681149 : Blo 972592 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B3699371 : Blo 972592 3699371 := bstep (se 1 (by rfl) ⟨2774528, by rfl⟩ : syracuseStep 3699371 = 5549057) B5549057
theorem B2192147 : Blo 972592 2192147 := bstep (se 1 (by rfl) ⟨1644110, by rfl⟩ : syracuseStep 2192147 = 3288221) B3288221
theorem B2192507 : Blo 972592 2192507 := bstep (se 1 (by rfl) ⟨1644380, by rfl⟩ : syracuseStep 2192507 = 3288761) B3288761
theorem B5272721 : Blo 972592 5272721 := bstep (se 2 (by rfl) ⟨1977270, by rfl⟩ : syracuseStep 5272721 = 3954541) B3954541
theorem B2192633 : Blo 972592 2192633 := bstep (se 2 (by rfl) ⟨822237, by rfl⟩ : syracuseStep 2192633 = 1644475) B1644475
theorem B2192777 : Blo 972592 2192777 := bstep (se 2 (by rfl) ⟨822291, by rfl⟩ : syracuseStep 2192777 = 1644583) B1644583
theorem B2192903 : Blo 972592 2192903 := bstep (se 1 (by rfl) ⟨1644677, by rfl⟩ : syracuseStep 2192903 = 3289355) B3289355
theorem B2193083 : Blo 972592 2193083 := bstep (se 1 (by rfl) ⟨1644812, by rfl⟩ : syracuseStep 2193083 = 3289625) B3289625
theorem B56096549 : Blo 972592 56096549 := bstep (se 4 (by rfl) ⟨5259051, by rfl⟩ : syracuseStep 56096549 = 10518103) B10518103
theorem B2193209 : Blo 972592 2193209 := bstep (se 2 (by rfl) ⟨822453, by rfl⟩ : syracuseStep 2193209 = 1644907) B1644907
theorem B4225159 : Blo 972592 4225159 := bstep (se 1 (by rfl) ⟨3168869, by rfl⟩ : syracuseStep 4225159 = 6337739) B6337739
theorem B2193839 : Blo 972592 2193839 := bstep (se 1 (by rfl) ⟨1645379, by rfl⟩ : syracuseStep 2193839 = 3290759) B3290759
theorem B2193875 : Blo 972592 2193875 := bstep (se 1 (by rfl) ⟨1645406, by rfl⟩ : syracuseStep 2193875 = 3290813) B3290813
theorem B2193983 : Blo 972592 2193983 := bstep (se 1 (by rfl) ⟨1645487, by rfl⟩ : syracuseStep 2193983 = 3290975) B3290975
theorem B2194091 : Blo 972592 2194091 := bstep (se 1 (by rfl) ⟨1645568, by rfl⟩ : syracuseStep 2194091 = 3291137) B3291137
theorem B5929847 : Blo 972592 5929847 := bstep (se 1 (by rfl) ⟨4447385, by rfl⟩ : syracuseStep 5929847 = 8894771) B8894771
theorem B8879033 : Blo 972592 8879033 := bstep (se 2 (by rfl) ⟨3329637, by rfl⟩ : syracuseStep 8879033 = 6659275) B6659275
theorem B4684787 : Blo 972592 4684787 := bstep (se 1 (by rfl) ⟨3513590, by rfl⟩ : syracuseStep 4684787 = 7027181) B7027181
theorem B2194631 : Blo 972592 2194631 := bstep (se 1 (by rfl) ⟨1645973, by rfl⟩ : syracuseStep 2194631 = 3291947) B3291947
theorem B2194811 : Blo 972592 2194811 := bstep (se 1 (by rfl) ⟨1646108, by rfl⟩ : syracuseStep 2194811 = 3292217) B3292217
theorem B2194937 : Blo 972592 2194937 := bstep (se 2 (by rfl) ⟨823101, by rfl⟩ : syracuseStep 2194937 = 1646203) B1646203
theorem B3702287 : Blo 972592 3702287 := bstep (se 1 (by rfl) ⟨2776715, by rfl⟩ : syracuseStep 3702287 = 5553431) B5553431
theorem B2195027 : Blo 972592 2195027 := bstep (se 1 (by rfl) ⟨1646270, by rfl⟩ : syracuseStep 2195027 = 3292541) B3292541
theorem B2195207 : Blo 972592 2195207 := bstep (se 1 (by rfl) ⟨1646405, by rfl⟩ : syracuseStep 2195207 = 3292811) B3292811
theorem B2195495 : Blo 972592 2195495 := bstep (se 1 (by rfl) ⟨1646621, by rfl⟩ : syracuseStep 2195495 = 3293243) B3293243
theorem B2195675 : Blo 972592 2195675 := bstep (se 1 (by rfl) ⟨1646756, by rfl⟩ : syracuseStep 2195675 = 3293513) B3293513
theorem B2195945 : Blo 972592 2195945 := bstep (se 2 (by rfl) ⟨823479, by rfl⟩ : syracuseStep 2195945 = 1646959) B1646959
theorem B2196233 : Blo 972592 2196233 := bstep (se 2 (by rfl) ⟨823587, by rfl⟩ : syracuseStep 2196233 = 1647175) B1647175
theorem B3703913 : Blo 972592 3703913 := bstep (se 2 (by rfl) ⟨1388967, by rfl⟩ : syracuseStep 3703913 = 2777935) B2777935
theorem B2196809 : Blo 972592 2196809 := bstep (se 2 (by rfl) ⟨823803, by rfl⟩ : syracuseStep 2196809 = 1647607) B1647607
theorem B3507823 : Blo 972592 3507823 := bstep (se 1 (by rfl) ⟨2630867, by rfl⟩ : syracuseStep 3507823 = 5261735) B5261735
theorem B16910045 : Blo 972592 16910045 := bstep (se 3 (by rfl) ⟨3170633, by rfl⟩ : syracuseStep 16910045 = 6341267) B6341267
theorem B7408097 : Blo 972592 7408097 := bstep (se 2 (by rfl) ⟨2778036, by rfl⟩ : syracuseStep 7408097 = 5556073) B5556073
theorem B1641451 : Blo 972592 1641451 := bstep (se 1 (by rfl) ⟨1231088, by rfl⟩ : syracuseStep 1641451 = 2462177) B2462177
theorem B3116065 : Blo 972592 3116065 := bstep (se 2 (by rfl) ⟨1168524, by rfl⟩ : syracuseStep 3116065 = 2337049) B2337049
theorem B1641593 : Blo 972592 1641593 := bstep (se 2 (by rfl) ⟨615597, by rfl⟩ : syracuseStep 1641593 = 1231195) B1231195
theorem B89034119 : Blo 972592 89034119 := bstep (se 1 (by rfl) ⟨66775589, by rfl⟩ : syracuseStep 89034119 = 133551179) B133551179
theorem B1445467 : Blo 972592 1445467 := bstep (se 1 (by rfl) ⟨1084100, by rfl⟩ : syracuseStep 1445467 = 2168201) B2168201
theorem B4165415 : Blo 972592 4165415 := bstep (se 1 (by rfl) ⟨3124061, by rfl⟩ : syracuseStep 4165415 = 6248123) B6248123
theorem B15830873 : Blo 972592 15830873 := bstep (se 2 (by rfl) ⟨5936577, by rfl⟩ : syracuseStep 15830873 = 11873155) B11873155
theorem B12161177 : Blo 972592 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B1642727 : Blo 972592 1642727 := bstep (se 1 (by rfl) ⟨1232045, by rfl⟩ : syracuseStep 1642727 = 2464091) B2464091
theorem B36049211 : Blo 972592 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B1642889 : Blo 972592 1642889 := bstep (se 2 (by rfl) ⟨616083, by rfl⟩ : syracuseStep 1642889 = 1232167) B1232167
theorem B2462471 : Blo 972592 2462471 := bstep (se 1 (by rfl) ⟨1846853, by rfl⟩ : syracuseStep 2462471 = 3693707) B3693707
theorem B4166441 : Blo 972592 4166441 := bstep (se 2 (by rfl) ⟨1562415, by rfl⟩ : syracuseStep 4166441 = 3124831) B3124831
theorem B1643321 : Blo 972592 1643321 := bstep (se 2 (by rfl) ⟨616245, by rfl⟩ : syracuseStep 1643321 = 1232491) B1232491
theorem B1643375 : Blo 972592 1643375 := bstep (se 1 (by rfl) ⟨1232531, by rfl⟩ : syracuseStep 1643375 = 2465063) B2465063
theorem B5542951 : Blo 972592 5542951 := bstep (se 1 (by rfl) ⟨4157213, by rfl⟩ : syracuseStep 5542951 = 8314427) B8314427
theorem B1873307 : Blo 972592 1873307 := bstep (se 1 (by rfl) ⟨1404980, by rfl⟩ : syracuseStep 1873307 = 2809961) B2809961
theorem B1644367 : Blo 972592 1644367 := bstep (se 1 (by rfl) ⟨1233275, by rfl⟩ : syracuseStep 1644367 = 2466551) B2466551
theorem B11114333 : Blo 972592 11114333 := bstep (se 3 (by rfl) ⟨2083937, by rfl⟩ : syracuseStep 11114333 = 4167875) B4167875
theorem B1644779 : Blo 972592 1644779 := bstep (se 1 (by rfl) ⟨1233584, by rfl⟩ : syracuseStep 1644779 = 2467169) B2467169
theorem B1972487 : Blo 972592 1972487 := bstep (se 1 (by rfl) ⟨1479365, by rfl⟩ : syracuseStep 1972487 = 2958731) B2958731
theorem B3283307 : Blo 972592 3283307 := bstep (se 1 (by rfl) ⟨2462480, by rfl⟩ : syracuseStep 3283307 = 4924961) B4924961
theorem B3283577 : Blo 972592 3283577 := bstep (se 2 (by rfl) ⟨1231341, by rfl⟩ : syracuseStep 3283577 = 2462683) B2462683
theorem B7412471 : Blo 972592 7412471 := bstep (se 1 (by rfl) ⟨5559353, by rfl⟩ : syracuseStep 7412471 = 11118707) B11118707
theorem B4692937 : Blo 972592 4692937 := bstep (se 2 (by rfl) ⟨1759851, by rfl⟩ : syracuseStep 4692937 = 3519703) B3519703
theorem B3284009 : Blo 972592 3284009 := bstep (se 2 (by rfl) ⟨1231503, by rfl⟩ : syracuseStep 3284009 = 2463007) B2463007
theorem B1645609 : Blo 972592 1645609 := bstep (se 2 (by rfl) ⟨617103, by rfl⟩ : syracuseStep 1645609 = 1234207) B1234207
theorem B3120257 : Blo 972592 3120257 := bstep (se 2 (by rfl) ⟨1170096, by rfl⟩ : syracuseStep 3120257 = 2340193) B2340193
theorem B2464951 : Blo 972592 2464951 := bstep (se 1 (by rfl) ⟨1848713, by rfl⟩ : syracuseStep 2464951 = 3697427) B3697427
theorem B1645751 : Blo 972592 1645751 := bstep (se 1 (by rfl) ⟨1234313, by rfl⟩ : syracuseStep 1645751 = 2468627) B2468627
theorem B11115791 : Blo 972592 11115791 := bstep (se 1 (by rfl) ⟨8336843, by rfl⟩ : syracuseStep 11115791 = 16673687) B16673687
theorem B6233543 : Blo 972592 6233543 := bstep (se 1 (by rfl) ⟨4675157, by rfl⟩ : syracuseStep 6233543 = 9350315) B9350315
theorem B2465255 : Blo 972592 2465255 := bstep (se 1 (by rfl) ⟨1848941, by rfl⟩ : syracuseStep 2465255 = 3697883) B3697883
theorem B1646075 : Blo 972592 1646075 := bstep (se 1 (by rfl) ⟨1234556, by rfl⟩ : syracuseStep 1646075 = 2469113) B2469113
theorem B3120731 : Blo 972592 3120731 := bstep (se 1 (by rfl) ⟨2340548, by rfl⟩ : syracuseStep 3120731 = 4681097) B4681097
theorem B4169501 : Blo 972592 4169501 := bstep (se 3 (by rfl) ⟨781781, by rfl⟩ : syracuseStep 4169501 = 1563563) B1563563
theorem B3383165 : Blo 972592 3383165 := bstep (se 3 (by rfl) ⟨634343, by rfl⟩ : syracuseStep 3383165 = 1268687) B1268687
theorem B1646507 : Blo 972592 1646507 := bstep (se 1 (by rfl) ⟨1234880, by rfl⟩ : syracuseStep 1646507 = 2469761) B2469761
theorem B64921915 : Blo 972592 64921915 := bstep (se 1 (by rfl) ⟨48691436, by rfl⟩ : syracuseStep 64921915 = 97382873) B97382873
theorem B2466247 : Blo 972592 2466247 := bstep (se 1 (by rfl) ⟨1849685, by rfl⟩ : syracuseStep 2466247 = 3699371) B3699371
theorem B1647047 : Blo 972592 1647047 := bstep (se 1 (by rfl) ⟨1235285, by rfl⟩ : syracuseStep 1647047 = 2470571) B2470571
theorem B3515147 : Blo 972592 3515147 := bstep (se 1 (by rfl) ⟨2636360, by rfl⟩ : syracuseStep 3515147 = 5272721) B5272721
theorem B37397699 : Blo 972592 37397699 := bstep (se 1 (by rfl) ⟨28048274, by rfl⟩ : syracuseStep 37397699 = 56096549) B56096549
theorem B3286223 : Blo 972592 3286223 := bstep (se 1 (by rfl) ⟨2464667, by rfl⟩ : syracuseStep 3286223 = 4929335) B4929335
theorem B1647823 : Blo 972592 1647823 := bstep (se 1 (by rfl) ⟨1235867, by rfl⟩ : syracuseStep 1647823 = 2471735) B2471735
theorem B3286547 : Blo 972592 3286547 := bstep (se 1 (by rfl) ⟨2464910, by rfl⟩ : syracuseStep 3286547 = 4929821) B4929821
theorem B13346693 : Blo 972592 13346693 := bstep (se 4 (by rfl) ⟨1251252, by rfl⟩ : syracuseStep 13346693 = 2502505) B2502505
theorem B3123191 : Blo 972592 3123191 := bstep (se 1 (by rfl) ⟨2342393, by rfl⟩ : syracuseStep 3123191 = 4684787) B4684787
theorem B2468191 : Blo 972592 2468191 := bstep (se 1 (by rfl) ⟨1851143, by rfl⟩ : syracuseStep 2468191 = 3702287) B3702287
theorem B1387145 : Blo 972592 1387145 := bstep (se 2 (by rfl) ⟨520179, by rfl⟩ : syracuseStep 1387145 = 1040359) B1040359
theorem B3287735 : Blo 972592 3287735 := bstep (se 1 (by rfl) ⟨2465801, by rfl⟩ : syracuseStep 3287735 = 4931603) B4931603
theorem B28454237 : Blo 972592 28454237 := bstep (se 3 (by rfl) ⟨5335169, by rfl⟩ : syracuseStep 28454237 = 10670339) B10670339
theorem B6237719 : Blo 972592 6237719 := bstep (se 1 (by rfl) ⟨4678289, by rfl⟩ : syracuseStep 6237719 = 9356579) B9356579
theorem B23703101 : Blo 972592 23703101 := bstep (se 3 (by rfl) ⟨4444331, by rfl⟩ : syracuseStep 23703101 = 8888663) B8888663
theorem B6237769 : Blo 972592 6237769 := bstep (se 2 (by rfl) ⟨2339163, by rfl⟩ : syracuseStep 6237769 = 4678327) B4678327
theorem B29994569 : Blo 972592 29994569 := bstep (se 2 (by rfl) ⟨11247963, by rfl⟩ : syracuseStep 29994569 = 22495927) B22495927
theorem B1846891 : Blo 972592 1846891 := bstep (se 1 (by rfl) ⟨1385168, by rfl⟩ : syracuseStep 1846891 = 2770337) B2770337
theorem B11251565 : Blo 972592 11251565 := bstep (se 3 (by rfl) ⟨2109668, by rfl⟩ : syracuseStep 11251565 = 4219337) B4219337
theorem B2633593 : Blo 972592 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B2338703 : Blo 972592 2338703 := bstep (se 1 (by rfl) ⟨1754027, by rfl⟩ : syracuseStep 2338703 = 3508055) B3508055
theorem B1847195 : Blo 972592 1847195 := bstep (se 1 (by rfl) ⟨1385396, by rfl⟩ : syracuseStep 1847195 = 2770793) B2770793
theorem B3944713 : Blo 972592 3944713 := bstep (se 2 (by rfl) ⟨1479267, by rfl⟩ : syracuseStep 3944713 = 2958535) B2958535
theorem B9384335 : Blo 972592 9384335 := bstep (se 1 (by rfl) ⟨7038251, by rfl⟩ : syracuseStep 9384335 = 14076503) B14076503
theorem B3289679 : Blo 972592 3289679 := bstep (se 1 (by rfl) ⟨2467259, by rfl⟩ : syracuseStep 3289679 = 4934519) B4934519
theorem B6239101 : Blo 972592 6239101 := bstep (se 3 (by rfl) ⟨1169831, by rfl⟩ : syracuseStep 6239101 = 2339663) B2339663
theorem B15774695 : Blo 972592 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B1094719 : Blo 972592 1094719 := bstep (se 1 (by rfl) ⟨821039, by rfl⟩ : syracuseStep 1094719 = 1642079) B1642079
theorem B3290219 : Blo 972592 3290219 := bstep (se 1 (by rfl) ⟨2467664, by rfl⟩ : syracuseStep 3290219 = 4935329) B4935329
theorem B2471087 : Blo 972592 2471087 := bstep (se 1 (by rfl) ⟨1853315, by rfl⟩ : syracuseStep 2471087 = 3706631) B3706631
theorem B1094863 : Blo 972592 1094863 := bstep (se 1 (by rfl) ⟨821147, by rfl⟩ : syracuseStep 1094863 = 1642295) B1642295
theorem B28063037 : Blo 972592 28063037 := bstep (se 3 (by rfl) ⟨5261819, by rfl⟩ : syracuseStep 28063037 = 10523639) B10523639
theorem B7386713 : Blo 972592 7386713 := bstep (se 2 (by rfl) ⟨2770017, by rfl⟩ : syracuseStep 7386713 = 5540035) B5540035
theorem B2373371 : Blo 972592 2373371 := bstep (se 1 (by rfl) ⟨1780028, by rfl⟩ : syracuseStep 2373371 = 3560057) B3560057
theorem B5552225 : Blo 972592 5552225 := bstep (se 2 (by rfl) ⟨2082084, by rfl⟩ : syracuseStep 5552225 = 4164169) B4164169
theorem B1095835 : Blo 972592 1095835 := bstep (se 1 (by rfl) ⟨821876, by rfl⟩ : syracuseStep 1095835 = 1643753) B1643753
theorem B1095871 : Blo 972592 1095871 := bstep (se 1 (by rfl) ⟨821903, by rfl⟩ : syracuseStep 1095871 = 1643807) B1643807
theorem B2504947 : Blo 972592 2504947 := bstep (se 1 (by rfl) ⟨1878710, by rfl⟩ : syracuseStep 2504947 = 3757421) B3757421
theorem B2078983 : Blo 972592 2078983 := bstep (se 1 (by rfl) ⟨1559237, by rfl⟩ : syracuseStep 2078983 = 3118475) B3118475
theorem B2963753 : Blo 972592 2963753 := bstep (se 2 (by rfl) ⟨1111407, by rfl⟩ : syracuseStep 2963753 = 2222815) B2222815
theorem B3291515 : Blo 972592 3291515 := bstep (se 1 (by rfl) ⟨2468636, by rfl⟩ : syracuseStep 3291515 = 4937273) B4937273
theorem B3291785 : Blo 972592 3291785 := bstep (se 2 (by rfl) ⟨1234419, by rfl⟩ : syracuseStep 3291785 = 2468839) B2468839
theorem B24984287 : Blo 972592 24984287 := bstep (se 1 (by rfl) ⟨18738215, by rfl⟩ : syracuseStep 24984287 = 37476431) B37476431
theorem B7912259 : Blo 972592 7912259 := bstep (se 1 (by rfl) ⟨5934194, by rfl⟩ : syracuseStep 7912259 = 11868389) B11868389
theorem B5552975 : Blo 972592 5552975 := bstep (se 1 (by rfl) ⟨4164731, by rfl⟩ : syracuseStep 5552975 = 8329463) B8329463
theorem B1850195 : Blo 972592 1850195 := bstep (se 1 (by rfl) ⟨1387646, by rfl⟩ : syracuseStep 1850195 = 2775293) B2775293
theorem B4930631 : Blo 972592 4930631 := bstep (se 1 (by rfl) ⟨3697973, by rfl⟩ : syracuseStep 4930631 = 7395947) B7395947
theorem B1851113 : Blo 972592 1851113 := bstep (se 2 (by rfl) ⟨694167, by rfl⟩ : syracuseStep 1851113 = 1388335) B1388335
theorem B3292919 : Blo 972592 3292919 := bstep (se 1 (by rfl) ⟨2469689, by rfl⟩ : syracuseStep 3292919 = 4939379) B4939379
theorem B12009323 : Blo 972592 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B2080999 : Blo 972592 2080999 := bstep (se 1 (by rfl) ⟨1560749, by rfl⟩ : syracuseStep 2080999 = 3121499) B3121499
theorem B2343143 : Blo 972592 2343143 := bstep (se 1 (by rfl) ⟨1757357, by rfl⟩ : syracuseStep 2343143 = 3514715) B3514715
theorem B1097959 : Blo 972592 1097959 := bstep (se 1 (by rfl) ⟨823469, by rfl⟩ : syracuseStep 1097959 = 1646939) B1646939
theorem B5620151 : Blo 972592 5620151 := bstep (se 1 (by rfl) ⟨4215113, by rfl⟩ : syracuseStep 5620151 = 8430227) B8430227
theorem B5554615 : Blo 972592 5554615 := bstep (se 1 (by rfl) ⟨4165961, by rfl⟩ : syracuseStep 5554615 = 8331923) B8331923
theorem B28426763 : Blo 972592 28426763 := bstep (se 1 (by rfl) ⟨21320072, by rfl⟩ : syracuseStep 28426763 = 42640145) B42640145
theorem B1458923 : Blo 972592 1458923 := bstep (se 1 (by rfl) ⟨1094192, by rfl⟩ : syracuseStep 1458923 = 2188385) B2188385
theorem B1852139 : Blo 972592 1852139 := bstep (se 1 (by rfl) ⟨1389104, by rfl⟩ : syracuseStep 1852139 = 2778209) B2778209
theorem B1458953 : Blo 972592 1458953 := bstep (se 2 (by rfl) ⟨547107, by rfl⟩ : syracuseStep 1458953 = 1094215) B1094215
theorem B3293999 : Blo 972592 3293999 := bstep (se 1 (by rfl) ⟨2470499, by rfl⟩ : syracuseStep 3293999 = 4940999) B4940999
theorem B1459055 : Blo 972592 1459055 := bstep (se 1 (by rfl) ⟨1094291, by rfl⟩ : syracuseStep 1459055 = 2188583) B2188583
theorem B1098607 : Blo 972592 1098607 := bstep (se 1 (by rfl) ⟨823955, by rfl⟩ : syracuseStep 1098607 = 1647911) B1647911
theorem B3294107 : Blo 972592 3294107 := bstep (se 1 (by rfl) ⟨2470580, by rfl⟩ : syracuseStep 3294107 = 4941161) B4941161
theorem B2376809 : Blo 972592 2376809 := bstep (se 2 (by rfl) ⟨891303, by rfl⟩ : syracuseStep 2376809 = 1782607) B1782607
theorem B1459307 : Blo 972592 1459307 := bstep (se 1 (by rfl) ⟨1094480, by rfl⟩ : syracuseStep 1459307 = 2188961) B2188961
theorem B2770109 : Blo 972592 2770109 := bstep (se 3 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 2770109 = 1038791) B1038791
theorem B1459547 : Blo 972592 1459547 := bstep (se 1 (by rfl) ⟨1094660, by rfl⟩ : syracuseStep 1459547 = 2189321) B2189321
theorem B1459823 : Blo 972592 1459823 := bstep (se 1 (by rfl) ⟨1094867, by rfl⟩ : syracuseStep 1459823 = 2189735) B2189735
theorem B6669985 : Blo 972592 6669985 := bstep (se 2 (by rfl) ⟨2501244, by rfl⟩ : syracuseStep 6669985 = 5002489) B5002489
theorem B1459895 : Blo 972592 1459895 := bstep (se 1 (by rfl) ⟨1094921, by rfl⟩ : syracuseStep 1459895 = 2189843) B2189843
theorem B1459931 : Blo 972592 1459931 := bstep (se 1 (by rfl) ⟨1094948, by rfl⟩ : syracuseStep 1459931 = 2189897) B2189897
theorem B1460105 : Blo 972592 1460105 := bstep (se 2 (by rfl) ⟨547539, by rfl⟩ : syracuseStep 1460105 = 1095079) B1095079
theorem B1460207 : Blo 972592 1460207 := bstep (se 1 (by rfl) ⟨1095155, by rfl⟩ : syracuseStep 1460207 = 2190311) B2190311
theorem B3295241 : Blo 972592 3295241 := bstep (se 2 (by rfl) ⟨1235715, by rfl⟩ : syracuseStep 3295241 = 2471431) B2471431
theorem B2771135 : Blo 972592 2771135 := bstep (se 1 (by rfl) ⟨2078351, by rfl⟩ : syracuseStep 2771135 = 4156703) B4156703
theorem B1460459 : Blo 972592 1460459 := bstep (se 1 (by rfl) ⟨1095344, by rfl⟩ : syracuseStep 1460459 = 2190689) B2190689
theorem B1460519 : Blo 972592 1460519 := bstep (se 1 (by rfl) ⟨1095389, by rfl⟩ : syracuseStep 1460519 = 2190779) B2190779
theorem B1460603 : Blo 972592 1460603 := bstep (se 1 (by rfl) ⟨1095452, by rfl⟩ : syracuseStep 1460603 = 2190905) B2190905
theorem B1460873 : Blo 972592 1460873 := bstep (se 2 (by rfl) ⟨547827, by rfl⟩ : syracuseStep 1460873 = 1095655) B1095655
theorem B1461047 : Blo 972592 1461047 := bstep (se 1 (by rfl) ⟨1095785, by rfl⟩ : syracuseStep 1461047 = 2191571) B2191571
theorem B1461083 : Blo 972592 1461083 := bstep (se 1 (by rfl) ⟨1095812, by rfl⟩ : syracuseStep 1461083 = 2191625) B2191625
theorem B1461227 : Blo 972592 1461227 := bstep (se 1 (by rfl) ⟨1095920, by rfl⟩ : syracuseStep 1461227 = 2191841) B2191841
theorem B2083819 : Blo 972592 2083819 := bstep (se 1 (by rfl) ⟨1562864, by rfl⟩ : syracuseStep 2083819 = 3125729) B3125729
theorem B1461431 : Blo 972592 1461431 := bstep (se 1 (by rfl) ⟨1096073, by rfl⟩ : syracuseStep 1461431 = 2192147) B2192147
theorem B1461671 : Blo 972592 1461671 := bstep (se 1 (by rfl) ⟨1096253, by rfl⟩ : syracuseStep 1461671 = 2192507) B2192507
theorem B7032253 : Blo 972592 7032253 := bstep (se 3 (by rfl) ⟨1318547, by rfl⟩ : syracuseStep 7032253 = 2637095) B2637095
theorem B1461755 : Blo 972592 1461755 := bstep (se 1 (by rfl) ⟨1096316, by rfl⟩ : syracuseStep 1461755 = 2192633) B2192633
theorem B1461851 : Blo 972592 1461851 := bstep (se 1 (by rfl) ⟨1096388, by rfl⟩ : syracuseStep 1461851 = 2192777) B2192777
theorem B5000861 : Blo 972592 5000861 := bstep (se 3 (by rfl) ⟨937661, by rfl⟩ : syracuseStep 5000861 = 1875323) B1875323
theorem B1461935 : Blo 972592 1461935 := bstep (se 1 (by rfl) ⟨1096451, by rfl⟩ : syracuseStep 1461935 = 2192903) B2192903
theorem B1462055 : Blo 972592 1462055 := bstep (se 1 (by rfl) ⟨1096541, by rfl⟩ : syracuseStep 1462055 = 2193083) B2193083
theorem B7917385 : Blo 972592 7917385 := bstep (se 2 (by rfl) ⟨2969019, by rfl⟩ : syracuseStep 7917385 = 5938039) B5938039
theorem B1462139 : Blo 972592 1462139 := bstep (se 1 (by rfl) ⟨1096604, by rfl⟩ : syracuseStep 1462139 = 2193209) B2193209
theorem B1462559 : Blo 972592 1462559 := bstep (se 1 (by rfl) ⟨1096919, by rfl⟩ : syracuseStep 1462559 = 2193839) B2193839
theorem B28102949 : Blo 972592 28102949 := bstep (se 4 (by rfl) ⟨2634651, by rfl⟩ : syracuseStep 28102949 = 5269303) B5269303
theorem B1462583 : Blo 972592 1462583 := bstep (se 1 (by rfl) ⟨1096937, by rfl⟩ : syracuseStep 1462583 = 2193875) B2193875
theorem B1462655 : Blo 972592 1462655 := bstep (se 1 (by rfl) ⟨1096991, by rfl⟩ : syracuseStep 1462655 = 2193983) B2193983
theorem B1462727 : Blo 972592 1462727 := bstep (se 1 (by rfl) ⟨1097045, by rfl⟩ : syracuseStep 1462727 = 2194091) B2194091
theorem B16634321 : Blo 972592 16634321 := bstep (se 2 (by rfl) ⟨6237870, by rfl⟩ : syracuseStep 16634321 = 12475741) B12475741
theorem B3953231 : Blo 972592 3953231 := bstep (se 1 (by rfl) ⟨2964923, by rfl⟩ : syracuseStep 3953231 = 5929847) B5929847
theorem B5919355 : Blo 972592 5919355 := bstep (se 1 (by rfl) ⟨4439516, by rfl⟩ : syracuseStep 5919355 = 8879033) B8879033
theorem B1463081 : Blo 972592 1463081 := bstep (se 2 (by rfl) ⟨548655, by rfl⟩ : syracuseStep 1463081 = 1097311) B1097311
theorem B1463087 : Blo 972592 1463087 := bstep (se 1 (by rfl) ⟨1097315, by rfl⟩ : syracuseStep 1463087 = 2194631) B2194631
theorem B1463207 : Blo 972592 1463207 := bstep (se 1 (by rfl) ⟨1097405, by rfl⟩ : syracuseStep 1463207 = 2194811) B2194811
theorem B33739739 : Blo 972592 33739739 := bstep (se 1 (by rfl) ⟨25304804, by rfl⟩ : syracuseStep 33739739 = 50609609) B50609609
theorem B1463291 : Blo 972592 1463291 := bstep (se 1 (by rfl) ⟨1097468, by rfl⟩ : syracuseStep 1463291 = 2194937) B2194937
theorem B1463351 : Blo 972592 1463351 := bstep (se 1 (by rfl) ⟨1097513, by rfl⟩ : syracuseStep 1463351 = 2195027) B2195027
theorem B1463471 : Blo 972592 1463471 := bstep (se 1 (by rfl) ⟨1097603, by rfl⟩ : syracuseStep 1463471 = 2195207) B2195207
theorem B5559515 : Blo 972592 5559515 := bstep (se 1 (by rfl) ⟨4169636, by rfl⟩ : syracuseStep 5559515 = 8339273) B8339273
theorem B1463879 : Blo 972592 1463879 := bstep (se 1 (by rfl) ⟨1097909, by rfl⟩ : syracuseStep 1463879 = 2195819) B2195819
theorem B1463975 : Blo 972592 1463975 := bstep (se 1 (by rfl) ⟨1097981, by rfl⟩ : syracuseStep 1463975 = 2195963) B2195963
theorem B2774711 : Blo 972592 2774711 := bstep (se 1 (by rfl) ⟨2081033, by rfl⟩ : syracuseStep 2774711 = 4162067) B4162067
theorem B1464059 : Blo 972592 1464059 := bstep (se 1 (by rfl) ⟨1098044, by rfl⟩ : syracuseStep 1464059 = 2196089) B2196089
theorem B1464095 : Blo 972592 1464095 := bstep (se 1 (by rfl) ⟨1098071, by rfl⟩ : syracuseStep 1464095 = 2196143) B2196143
theorem B972607 : Blo 972592 972607 := bstep (se 1 (by rfl) ⟨729455, by rfl⟩ : syracuseStep 972607 = 1458911) B1458911
theorem B1464143 : Blo 972592 1464143 := bstep (se 1 (by rfl) ⟨1098107, by rfl⟩ : syracuseStep 1464143 = 2196215) B2196215
theorem B1464263 : Blo 972592 1464263 := bstep (se 1 (by rfl) ⟨1098197, by rfl⟩ : syracuseStep 1464263 = 2196395) B2196395
theorem B972783 : Blo 972592 972783 := bstep (se 1 (by rfl) ⟨729587, by rfl⟩ : syracuseStep 972783 = 1459175) B1459175
theorem B972955 : Blo 972592 972955 := bstep (se 1 (by rfl) ⟨729716, by rfl⟩ : syracuseStep 972955 = 1459433) B1459433
theorem B972991 : Blo 972592 972991 := bstep (se 1 (by rfl) ⟨729743, by rfl⟩ : syracuseStep 972991 = 1459487) B1459487
theorem B10541249 : Blo 972592 10541249 := bstep (se 2 (by rfl) ⟨3952968, by rfl⟩ : syracuseStep 10541249 = 7905937) B7905937
theorem B1235179 : Blo 972592 1235179 := bstep (se 1 (by rfl) ⟨926384, by rfl⟩ : syracuseStep 1235179 = 1852769) B1852769
theorem B8444189 : Blo 972592 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B1464617 : Blo 972592 1464617 := bstep (se 2 (by rfl) ⟨549231, by rfl⟩ : syracuseStep 1464617 = 1098463) B1098463
theorem B973103 : Blo 972592 973103 := bstep (se 1 (by rfl) ⟨729827, by rfl⟩ : syracuseStep 973103 = 1459655) B1459655
theorem B1464623 : Blo 972592 1464623 := bstep (se 1 (by rfl) ⟨1098467, by rfl⟩ : syracuseStep 1464623 = 2196935) B2196935
theorem B2775485 : Blo 972592 2775485 := bstep (se 3 (by rfl) ⟨520403, by rfl⟩ : syracuseStep 2775485 = 1040807) B1040807
theorem B973339 : Blo 972592 973339 := bstep (se 1 (by rfl) ⟨730004, by rfl⟩ : syracuseStep 973339 = 1460009) B1460009
theorem B1169947 : Blo 972592 1169947 := bstep (se 1 (by rfl) ⟨877460, by rfl⟩ : syracuseStep 1169947 = 1754921) B1754921
theorem B973343 : Blo 972592 973343 := bstep (se 1 (by rfl) ⟨730007, by rfl⟩ : syracuseStep 973343 = 1460015) B1460015
theorem B1464863 : Blo 972592 1464863 := bstep (se 1 (by rfl) ⟨1098647, by rfl⟩ : syracuseStep 1464863 = 2197295) B2197295
theorem B102816289 : Blo 972592 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B5790455 : Blo 972592 5790455 := bstep (se 1 (by rfl) ⟨4342841, by rfl⟩ : syracuseStep 5790455 = 8685683) B8685683
theorem B973659 : Blo 972592 973659 := bstep (se 1 (by rfl) ⟨730244, by rfl⟩ : syracuseStep 973659 = 1460489) B1460489
theorem B973727 : Blo 972592 973727 := bstep (se 1 (by rfl) ⟨730295, by rfl⟩ : syracuseStep 973727 = 1460591) B1460591
theorem B973871 : Blo 972592 973871 := bstep (se 1 (by rfl) ⟨730403, by rfl⟩ : syracuseStep 973871 = 1460807) B1460807
theorem B973895 : Blo 972592 973895 := bstep (se 1 (by rfl) ⟨730421, by rfl⟩ : syracuseStep 973895 = 1460843) B1460843
theorem B974047 : Blo 972592 974047 := bstep (se 1 (by rfl) ⟨730535, by rfl⟩ : syracuseStep 974047 = 1461071) B1461071
theorem B974311 : Blo 972592 974311 := bstep (se 1 (by rfl) ⟨730733, by rfl⟩ : syracuseStep 974311 = 1461467) B1461467
theorem B5332559 : Blo 972592 5332559 := bstep (se 1 (by rfl) ⟨3999419, by rfl⟩ : syracuseStep 5332559 = 7998839) B7998839
theorem B974427 : Blo 972592 974427 := bstep (se 1 (by rfl) ⟨730820, by rfl⟩ : syracuseStep 974427 = 1461641) B1461641
theorem B974663 : Blo 972592 974663 := bstep (se 1 (by rfl) ⟨730997, by rfl⟩ : syracuseStep 974663 = 1461995) B1461995
theorem B3170219 : Blo 972592 3170219 := bstep (se 1 (by rfl) ⟨2377664, by rfl⟩ : syracuseStep 3170219 = 4755329) B4755329
theorem B974815 : Blo 972592 974815 := bstep (se 1 (by rfl) ⟨731111, by rfl⟩ : syracuseStep 974815 = 1462223) B1462223
theorem B975079 : Blo 972592 975079 := bstep (se 1 (by rfl) ⟨731309, by rfl⟩ : syracuseStep 975079 = 1462619) B1462619
theorem B3694967 : Blo 972592 3694967 := bstep (se 1 (by rfl) ⟨2771225, by rfl⟩ : syracuseStep 3694967 = 5542451) B5542451
theorem B975231 : Blo 972592 975231 := bstep (se 1 (by rfl) ⟨731423, by rfl⟩ : syracuseStep 975231 = 1462847) B1462847
theorem B975311 : Blo 972592 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B15000065 : Blo 972592 15000065 := bstep (se 2 (by rfl) ⟨5625024, by rfl⟩ : syracuseStep 15000065 = 11250049) B11250049
theorem B975463 : Blo 972592 975463 := bstep (se 1 (by rfl) ⟨731597, by rfl⟩ : syracuseStep 975463 = 1463195) B1463195
theorem B6939449 : Blo 972592 6939449 := bstep (se 2 (by rfl) ⟨2602293, by rfl⟩ : syracuseStep 6939449 = 5204587) B5204587
theorem B11264827 : Blo 972592 11264827 := bstep (se 1 (by rfl) ⟨8448620, by rfl⟩ : syracuseStep 11264827 = 16897241) B16897241
theorem B975727 : Blo 972592 975727 := bstep (se 1 (by rfl) ⟨731795, by rfl⟩ : syracuseStep 975727 = 1463591) B1463591
theorem B975783 : Blo 972592 975783 := bstep (se 1 (by rfl) ⟨731837, by rfl⟩ : syracuseStep 975783 = 1463675) B1463675
theorem B975867 : Blo 972592 975867 := bstep (se 1 (by rfl) ⟨731900, by rfl⟩ : syracuseStep 975867 = 1463801) B1463801
theorem B975935 : Blo 972592 975935 := bstep (se 1 (by rfl) ⟨731951, by rfl⟩ : syracuseStep 975935 = 1463903) B1463903
theorem B8316067 : Blo 972592 8316067 := bstep (se 1 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 8316067 = 12474101) B12474101
theorem B28435627 : Blo 972592 28435627 := bstep (se 1 (by rfl) ⟨21326720, by rfl⟩ : syracuseStep 28435627 = 42653441) B42653441
theorem B976079 : Blo 972592 976079 := bstep (se 1 (by rfl) ⟨732059, by rfl⟩ : syracuseStep 976079 = 1464119) B1464119
theorem B3695939 : Blo 972592 3695939 := bstep (se 1 (by rfl) ⟨2771954, by rfl⟩ : syracuseStep 3695939 = 5543909) B5543909
theorem B81126755 : Blo 972592 81126755 := bstep (se 1 (by rfl) ⟨60845066, by rfl⟩ : syracuseStep 81126755 = 121690133) B121690133
theorem B976283 : Blo 972592 976283 := bstep (se 1 (by rfl) ⟨732212, by rfl⟩ : syracuseStep 976283 = 1464425) B1464425
theorem B976495 : Blo 972592 976495 := bstep (se 1 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 976495 = 1464743) B1464743
theorem B976551 : Blo 972592 976551 := bstep (se 1 (by rfl) ⟨732413, by rfl⟩ : syracuseStep 976551 = 1464827) B1464827
theorem B2189087 : Blo 972592 2189087 := bstep (se 1 (by rfl) ⟨1641815, by rfl⟩ : syracuseStep 2189087 = 3283631) B3283631
theorem B12511007 : Blo 972592 12511007 := bstep (se 1 (by rfl) ⟨9383255, by rfl⟩ : syracuseStep 12511007 = 18766511) B18766511
theorem B15820751 : Blo 972592 15820751 := bstep (se 1 (by rfl) ⟨11865563, by rfl⟩ : syracuseStep 15820751 = 23731127) B23731127
theorem B2189303 : Blo 972592 2189303 := bstep (se 1 (by rfl) ⟨1641977, by rfl⟩ : syracuseStep 2189303 = 3283955) B3283955
theorem B23685209 : Blo 972592 23685209 := bstep (se 2 (by rfl) ⟨8881953, by rfl⟩ : syracuseStep 23685209 = 17763907) B17763907
theorem B4941971 : Blo 972592 4941971 := bstep (se 1 (by rfl) ⟨3706478, by rfl⟩ : syracuseStep 4941971 = 7412957) B7412957
theorem B18770201 : Blo 972592 18770201 := bstep (se 2 (by rfl) ⟨7038825, by rfl⟩ : syracuseStep 18770201 = 14077651) B14077651
theorem B2189663 : Blo 972592 2189663 := bstep (se 1 (by rfl) ⟨1642247, by rfl⟩ : syracuseStep 2189663 = 3284495) B3284495
theorem B9366191 : Blo 972592 9366191 := bstep (se 1 (by rfl) ⟨7024643, by rfl⟩ : syracuseStep 9366191 = 14049287) B14049287
theorem B4156379 : Blo 972592 4156379 := bstep (se 1 (by rfl) ⟨3117284, by rfl⟩ : syracuseStep 4156379 = 6234569) B6234569
theorem B2190383 : Blo 972592 2190383 := bstep (se 1 (by rfl) ⟨1642787, by rfl⟩ : syracuseStep 2190383 = 3285575) B3285575
theorem B8875241 : Blo 972592 8875241 := bstep (se 2 (by rfl) ⟨3328215, by rfl⟩ : syracuseStep 8875241 = 6656431) B6656431
theorem B2190671 : Blo 972592 2190671 := bstep (se 1 (by rfl) ⟨1643003, by rfl⟩ : syracuseStep 2190671 = 3286007) B3286007
theorem B2190761 : Blo 972592 2190761 := bstep (se 2 (by rfl) ⟨821535, by rfl⟩ : syracuseStep 2190761 = 1643071) B1643071
theorem B24997409 : Blo 972592 24997409 := bstep (se 2 (by rfl) ⟨9374028, by rfl⟩ : syracuseStep 24997409 = 18748057) B18748057
theorem B2223911 : Blo 972592 2223911 := bstep (se 1 (by rfl) ⟨1667933, by rfl⟩ : syracuseStep 2223911 = 3335867) B3335867
theorem B2191247 : Blo 972592 2191247 := bstep (se 1 (by rfl) ⟨1643435, by rfl⟩ : syracuseStep 2191247 = 3286871) B3286871
theorem B2191967 : Blo 972592 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B47477825 : Blo 972592 47477825 := bstep (se 2 (by rfl) ⟨17804184, by rfl⟩ : syracuseStep 47477825 = 35608369) B35608369
theorem B11105585 : Blo 972592 11105585 := bstep (se 2 (by rfl) ⟨4164594, by rfl⟩ : syracuseStep 11105585 = 8329189) B8329189
theorem B6354227 : Blo 972592 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B2192795 : Blo 972592 2192795 := bstep (se 1 (by rfl) ⟨1644596, by rfl⟩ : syracuseStep 2192795 = 3289193) B3289193
theorem B5633545 : Blo 972592 5633545 := bstep (se 2 (by rfl) ⟨2112579, by rfl⟩ : syracuseStep 5633545 = 4225159) B4225159
theorem B2225735 : Blo 972592 2225735 := bstep (se 1 (by rfl) ⟨1669301, by rfl⟩ : syracuseStep 2225735 = 3338603) B3338603
theorem B1668775 : Blo 972592 1668775 := bstep (se 1 (by rfl) ⟨1251581, by rfl⟩ : syracuseStep 1668775 = 2503163) B2503163
theorem B8320715 : Blo 972592 8320715 := bstep (se 1 (by rfl) ⟨6240536, by rfl⟩ : syracuseStep 8320715 = 12481073) B12481073
theorem B4454099 : Blo 972592 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B2193371 : Blo 972592 2193371 := bstep (se 1 (by rfl) ⟨1645028, by rfl⟩ : syracuseStep 2193371 = 3290057) B3290057
theorem B2193551 : Blo 972592 2193551 := bstep (se 1 (by rfl) ⟨1645163, by rfl⟩ : syracuseStep 2193551 = 3290327) B3290327
theorem B2193569 : Blo 972592 2193569 := bstep (se 2 (by rfl) ⟨822588, by rfl⟩ : syracuseStep 2193569 = 1645177) B1645177
theorem B2193641 : Blo 972592 2193641 := bstep (se 2 (by rfl) ⟨822615, by rfl⟩ : syracuseStep 2193641 = 1645231) B1645231
theorem B21068039 : Blo 972592 21068039 := bstep (se 1 (by rfl) ⟨15801029, by rfl⟩ : syracuseStep 21068039 = 31602059) B31602059
theorem B6256939 : Blo 972592 6256939 := bstep (se 1 (by rfl) ⟨4692704, by rfl⟩ : syracuseStep 6256939 = 9385409) B9385409
theorem B4160153 : Blo 972592 4160153 := bstep (se 2 (by rfl) ⟨1560057, by rfl⟩ : syracuseStep 4160153 = 3120115) B3120115
theorem B3701801 : Blo 972592 3701801 := bstep (se 2 (by rfl) ⟨1388175, by rfl⟩ : syracuseStep 3701801 = 2776351) B2776351
theorem B81100061 : Blo 972592 81100061 := bstep (se 3 (by rfl) ⟨15206261, by rfl⟩ : syracuseStep 81100061 = 30412523) B30412523
theorem B2194919 : Blo 972592 2194919 := bstep (se 1 (by rfl) ⟨1646189, by rfl⟩ : syracuseStep 2194919 = 3292379) B3292379
theorem B4161451 : Blo 972592 4161451 := bstep (se 1 (by rfl) ⟨3121088, by rfl⟩ : syracuseStep 4161451 = 6242177) B6242177
theorem B2195999 : Blo 972592 2195999 := bstep (se 1 (by rfl) ⟨1646999, by rfl⟩ : syracuseStep 2195999 = 3293999) B3293999
theorem B7406153 : Blo 972592 7406153 := bstep (se 2 (by rfl) ⟨2777307, by rfl⟩ : syracuseStep 7406153 = 5554615) B5554615
theorem B2196071 : Blo 972592 2196071 := bstep (se 1 (by rfl) ⟨1647053, by rfl⟩ : syracuseStep 2196071 = 3294107) B3294107
theorem B11273363 : Blo 972592 11273363 := bstep (se 1 (by rfl) ⟨8455022, by rfl⟩ : syracuseStep 11273363 = 16910045) B16910045
theorem B2196827 : Blo 972592 2196827 := bstep (se 1 (by rfl) ⟨1647620, by rfl⟩ : syracuseStep 2196827 = 3295241) B3295241
theorem B37914169 : Blo 972592 37914169 := bstep (se 2 (by rfl) ⟨14217813, by rfl⟩ : syracuseStep 37914169 = 28435627) B28435627
theorem B2197097 : Blo 972592 2197097 := bstep (se 2 (by rfl) ⟨823911, by rfl⟩ : syracuseStep 2197097 = 1647823) B1647823
theorem B10553915 : Blo 972592 10553915 := bstep (se 1 (by rfl) ⟨7915436, by rfl⟩ : syracuseStep 10553915 = 15830873) B15830873
theorem B1641647 : Blo 972592 1641647 := bstep (se 1 (by rfl) ⟨1231235, by rfl⟩ : syracuseStep 1641647 = 2462471) B2462471
theorem B3706343 : Blo 972592 3706343 := bstep (se 1 (by rfl) ⟨2779757, by rfl⟩ : syracuseStep 3706343 = 5559515) B5559515
theorem B7409555 : Blo 972592 7409555 := bstep (se 1 (by rfl) ⟨5557166, by rfl⟩ : syracuseStep 7409555 = 11114333) B11114333
theorem B1314991 : Blo 972592 1314991 := bstep (se 1 (by rfl) ⟨986243, by rfl⟩ : syracuseStep 1314991 = 1972487) B1972487
theorem B9376337 : Blo 972592 9376337 := bstep (se 2 (by rfl) ⟨3516126, by rfl⟩ : syracuseStep 9376337 = 7032253) B7032253
theorem B2462521 : Blo 972592 2462521 := bstep (se 2 (by rfl) ⟨923445, by rfl⟩ : syracuseStep 2462521 = 1846891) B1846891
theorem B7410527 : Blo 972592 7410527 := bstep (se 1 (by rfl) ⟨5557895, by rfl⟩ : syracuseStep 7410527 = 11115791) B11115791
theorem B1643503 : Blo 972592 1643503 := bstep (se 1 (by rfl) ⟨1232627, by rfl⟩ : syracuseStep 1643503 = 2465255) B2465255
theorem B10556513 : Blo 972592 10556513 := bstep (se 2 (by rfl) ⟨3958692, by rfl⟩ : syracuseStep 10556513 = 7917385) B7917385
theorem B3511457 : Blo 972592 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B2463311 : Blo 972592 2463311 := bstep (se 1 (by rfl) ⟨1847483, by rfl⟩ : syracuseStep 2463311 = 3694967) B3694967
theorem B10000043 : Blo 972592 10000043 := bstep (se 1 (by rfl) ⟨7500032, by rfl⟩ : syracuseStep 10000043 = 15000065) B15000065
theorem B4626299 : Blo 972592 4626299 := bstep (se 1 (by rfl) ⟨3469724, by rfl⟩ : syracuseStep 4626299 = 6939449) B6939449
theorem B2463959 : Blo 972592 2463959 := bstep (se 1 (by rfl) ⟨1847969, by rfl⟩ : syracuseStep 2463959 = 3695939) B3695939
theorem B7511393 : Blo 972592 7511393 := bstep (se 2 (by rfl) ⟨2816772, by rfl⟩ : syracuseStep 7511393 = 5633545) B5633545
theorem B15802067 : Blo 972592 15802067 := bstep (se 1 (by rfl) ⟨11851550, by rfl⟩ : syracuseStep 15802067 = 23703101) B23703101
theorem B19996379 : Blo 972592 19996379 := bstep (se 1 (by rfl) ⟨14997284, by rfl⟩ : syracuseStep 19996379 = 29994569) B29994569
theorem B1482607 : Blo 972592 1482607 := bstep (se 1 (by rfl) ⟨1111955, by rfl⟩ : syracuseStep 1482607 = 2223911) B2223911
theorem B1646905 : Blo 972592 1646905 := bstep (se 2 (by rfl) ⟨617589, by rfl⟩ : syracuseStep 1646905 = 1235179) B1235179
theorem B1647391 : Blo 972592 1647391 := bstep (se 1 (by rfl) ⟨1235543, by rfl⟩ : syracuseStep 1647391 = 2471087) B2471087
theorem B4236151 : Blo 972592 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B1483823 : Blo 972592 1483823 := bstep (se 1 (by rfl) ⟨1112867, by rfl⟩ : syracuseStep 1483823 = 2225735) B2225735
theorem B4924475 : Blo 972592 4924475 := bstep (se 1 (by rfl) ⟨3693356, by rfl⟩ : syracuseStep 4924475 = 7386713) B7386713
theorem B5547143 : Blo 972592 5547143 := bstep (se 1 (by rfl) ⟨4160357, by rfl⟩ : syracuseStep 5547143 = 8320715) B8320715
theorem B1582247 : Blo 972592 1582247 := bstep (se 1 (by rfl) ⟨1186685, by rfl⟩ : syracuseStep 1582247 = 2373371) B2373371
theorem B1975835 : Blo 972592 1975835 := bstep (se 1 (by rfl) ⟨1481876, by rfl⟩ : syracuseStep 1975835 = 2963753) B2963753
theorem B3286601 : Blo 972592 3286601 := bstep (se 2 (by rfl) ⟨1232475, by rfl⟩ : syracuseStep 3286601 = 2464951) B2464951
theorem B16656191 : Blo 972592 16656191 := bstep (se 1 (by rfl) ⟨12492143, by rfl⟩ : syracuseStep 16656191 = 24984287) B24984287
theorem B2467867 : Blo 972592 2467867 := bstep (se 1 (by rfl) ⟨1850900, by rfl⟩ : syracuseStep 2467867 = 3701801) B3701801
theorem B3287087 : Blo 972592 3287087 := bstep (se 1 (by rfl) ⟨2465315, by rfl⟩ : syracuseStep 3287087 = 4930631) B4930631
theorem B9021773 : Blo 972592 9021773 := bstep (se 3 (by rfl) ⟨1691582, by rfl⟩ : syracuseStep 9021773 = 3383165) B3383165
theorem B5548601 : Blo 972592 5548601 := bstep (se 2 (by rfl) ⟨2080725, by rfl⟩ : syracuseStep 5548601 = 4161451) B4161451
theorem B8006215 : Blo 972592 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B3746767 : Blo 972592 3746767 := bstep (se 1 (by rfl) ⟨2810075, by rfl⟩ : syracuseStep 3746767 = 5620151) B5620151
theorem B18951175 : Blo 972592 18951175 := bstep (se 1 (by rfl) ⟨14213381, by rfl⟩ : syracuseStep 18951175 = 28426763) B28426763
theorem B3288329 : Blo 972592 3288329 := bstep (se 2 (by rfl) ⟨1233123, by rfl⟩ : syracuseStep 3288329 = 2466247) B2466247
theorem B2469275 : Blo 972592 2469275 := bstep (se 1 (by rfl) ⟨1851956, by rfl⟩ : syracuseStep 2469275 = 3703913) B3703913
theorem B1584539 : Blo 972592 1584539 := bstep (se 1 (by rfl) ⟨1188404, by rfl⟩ : syracuseStep 1584539 = 2376809) B2376809
theorem B1846739 : Blo 972592 1846739 := bstep (se 1 (by rfl) ⟨1385054, by rfl⟩ : syracuseStep 1846739 = 2770109) B2770109
theorem B15019769 : Blo 972592 15019769 := bstep (se 2 (by rfl) ⟨5632413, by rfl⟩ : syracuseStep 15019769 = 11264827) B11264827
theorem B1847423 : Blo 972592 1847423 := bstep (se 1 (by rfl) ⟨1385567, by rfl⟩ : syracuseStep 1847423 = 2771135) B2771135
theorem B11088089 : Blo 972592 11088089 := bstep (se 2 (by rfl) ⟨4158033, by rfl⟩ : syracuseStep 11088089 = 8316067) B8316067
theorem B1094395 : Blo 972592 1094395 := bstep (se 1 (by rfl) ⟨820796, by rfl⟩ : syracuseStep 1094395 = 1641593) B1641593
theorem B8893313 : Blo 972592 8893313 := bstep (se 2 (by rfl) ⟨3334992, by rfl⟩ : syracuseStep 8893313 = 6669985) B6669985
theorem B59356079 : Blo 972592 59356079 := bstep (se 1 (by rfl) ⟨44517059, by rfl⟩ : syracuseStep 59356079 = 89034119) B89034119
theorem B8107451 : Blo 972592 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B6239717 : Blo 972592 6239717 := bstep (se 4 (by rfl) ⟨584973, by rfl⟩ : syracuseStep 6239717 = 1169947) B1169947
theorem B1095151 : Blo 972592 1095151 := bstep (se 1 (by rfl) ⟨821363, by rfl⟩ : syracuseStep 1095151 = 1642727) B1642727
theorem B24032807 : Blo 972592 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B1095259 : Blo 972592 1095259 := bstep (se 1 (by rfl) ⟨821444, by rfl⟩ : syracuseStep 1095259 = 1642889) B1642889
theorem B11089547 : Blo 972592 11089547 := bstep (se 1 (by rfl) ⟨8317160, by rfl⟩ : syracuseStep 11089547 = 16634321) B16634321
theorem B2635487 : Blo 972592 2635487 := bstep (se 1 (by rfl) ⟨1976615, by rfl⟩ : syracuseStep 2635487 = 3953231) B3953231
theorem B3290921 : Blo 972592 3290921 := bstep (se 2 (by rfl) ⟨1234095, by rfl⟩ : syracuseStep 3290921 = 2468191) B2468191
theorem B1095547 : Blo 972592 1095547 := bstep (se 1 (by rfl) ⟨821660, by rfl⟩ : syracuseStep 1095547 = 1643321) B1643321
theorem B1095583 : Blo 972592 1095583 := bstep (se 1 (by rfl) ⟨821687, by rfl⟩ : syracuseStep 1095583 = 1643375) B1643375
theorem B22493159 : Blo 972592 22493159 := bstep (se 1 (by rfl) ⟨16869869, by rfl⟩ : syracuseStep 22493159 = 33739739) B33739739
theorem B4995485 : Blo 972592 4995485 := bstep (se 3 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 4995485 = 1873307) B1873307
theorem B1849807 : Blo 972592 1849807 := bstep (se 1 (by rfl) ⟨1387355, by rfl⟩ : syracuseStep 1849807 = 2774711) B2774711
theorem B7027499 : Blo 972592 7027499 := bstep (se 1 (by rfl) ⟨5270624, by rfl⟩ : syracuseStep 7027499 = 10541249) B10541249
theorem B1096519 : Blo 972592 1096519 := bstep (se 1 (by rfl) ⟨822389, by rfl⟩ : syracuseStep 1096519 = 1644779) B1644779
theorem B2080171 : Blo 972592 2080171 := bstep (se 1 (by rfl) ⟨1560128, by rfl⟩ : syracuseStep 2080171 = 3120257) B3120257
theorem B1097167 : Blo 972592 1097167 := bstep (se 1 (by rfl) ⟨822875, by rfl⟩ : syracuseStep 1097167 = 1645751) B1645751
theorem B1097383 : Blo 972592 1097383 := bstep (se 1 (by rfl) ⟨823037, by rfl⟩ : syracuseStep 1097383 = 1646075) B1646075
theorem B2080487 : Blo 972592 2080487 := bstep (se 1 (by rfl) ⟨1560365, by rfl⟩ : syracuseStep 2080487 = 3120731) B3120731
theorem B1097671 : Blo 972592 1097671 := bstep (se 1 (by rfl) ⟨823253, by rfl⟩ : syracuseStep 1097671 = 1646507) B1646507
theorem B1098031 : Blo 972592 1098031 := bstep (se 1 (by rfl) ⟨823523, by rfl⟩ : syracuseStep 1098031 = 1647047) B1647047
theorem B5259617 : Blo 972592 5259617 := bstep (se 2 (by rfl) ⟨1972356, by rfl⟩ : syracuseStep 5259617 = 3944713) B3944713
theorem B2343431 : Blo 972592 2343431 := bstep (se 1 (by rfl) ⟨1757573, by rfl⟩ : syracuseStep 2343431 = 3515147) B3515147
theorem B54084503 : Blo 972592 54084503 := bstep (se 1 (by rfl) ⟨40563377, by rfl⟩ : syracuseStep 54084503 = 81126755) B81126755
theorem B1459391 : Blo 972592 1459391 := bstep (se 1 (by rfl) ⟨1094543, by rfl⟩ : syracuseStep 1459391 = 2189087) B2189087
theorem B8340671 : Blo 972592 8340671 := bstep (se 1 (by rfl) ⟨6255503, by rfl⟩ : syracuseStep 8340671 = 12511007) B12511007
theorem B8897795 : Blo 972592 8897795 := bstep (se 1 (by rfl) ⟨6673346, by rfl⟩ : syracuseStep 8897795 = 13346693) B13346693
theorem B1459535 : Blo 972592 1459535 := bstep (se 1 (by rfl) ⟨1094651, by rfl⟩ : syracuseStep 1459535 = 2189303) B2189303
theorem B2082127 : Blo 972592 2082127 := bstep (se 1 (by rfl) ⟨1561595, by rfl⟩ : syracuseStep 2082127 = 3123191) B3123191
theorem B7390601 : Blo 972592 7390601 := bstep (se 2 (by rfl) ⟨2771475, by rfl⟩ : syracuseStep 7390601 = 5542951) B5542951
theorem B1459625 : Blo 972592 1459625 := bstep (se 2 (by rfl) ⟨547359, by rfl⟩ : syracuseStep 1459625 = 1094719) B1094719
theorem B3294647 : Blo 972592 3294647 := bstep (se 1 (by rfl) ⟨2470985, by rfl⟩ : syracuseStep 3294647 = 4941971) B4941971
theorem B1459775 : Blo 972592 1459775 := bstep (se 1 (by rfl) ⟨1094831, by rfl⟩ : syracuseStep 1459775 = 2189663) B2189663
theorem B1459817 : Blo 972592 1459817 := bstep (se 2 (by rfl) ⟨547431, by rfl⟩ : syracuseStep 1459817 = 1094863) B1094863
theorem B6244127 : Blo 972592 6244127 := bstep (se 1 (by rfl) ⟨4683095, by rfl⟩ : syracuseStep 6244127 = 9366191) B9366191
theorem B2770919 : Blo 972592 2770919 := bstep (se 1 (by rfl) ⟨2078189, by rfl⟩ : syracuseStep 2770919 = 4156379) B4156379
theorem B1460255 : Blo 972592 1460255 := bstep (se 1 (by rfl) ⟨1095191, by rfl⟩ : syracuseStep 1460255 = 2190383) B2190383
theorem B5916827 : Blo 972592 5916827 := bstep (se 1 (by rfl) ⟨4437620, by rfl⟩ : syracuseStep 5916827 = 8875241) B8875241
theorem B1460447 : Blo 972592 1460447 := bstep (se 1 (by rfl) ⟨1095335, by rfl⟩ : syracuseStep 1460447 = 2190671) B2190671
theorem B1460507 : Blo 972592 1460507 := bstep (se 1 (by rfl) ⟨1095380, by rfl⟩ : syracuseStep 1460507 = 2190761) B2190761
theorem B16664939 : Blo 972592 16664939 := bstep (se 1 (by rfl) ⟨12498704, by rfl⟩ : syracuseStep 16664939 = 24997409) B24997409
theorem B1559135 : Blo 972592 1559135 := bstep (se 1 (by rfl) ⟨1169351, by rfl⟩ : syracuseStep 1559135 = 2338703) B2338703
theorem B1460831 : Blo 972592 1460831 := bstep (se 1 (by rfl) ⟨1095623, by rfl⟩ : syracuseStep 1460831 = 2191247) B2191247
theorem B1231463 : Blo 972592 1231463 := bstep (se 1 (by rfl) ⟨923597, by rfl⟩ : syracuseStep 1231463 = 1847195) B1847195
theorem B1461113 : Blo 972592 1461113 := bstep (se 2 (by rfl) ⟨547917, by rfl⟩ : syracuseStep 1461113 = 1095835) B1095835
theorem B1461161 : Blo 972592 1461161 := bstep (se 2 (by rfl) ⟨547935, by rfl⟩ : syracuseStep 1461161 = 1095871) B1095871
theorem B2771977 : Blo 972592 2771977 := bstep (se 2 (by rfl) ⟨1039491, by rfl⟩ : syracuseStep 2771977 = 2078983) B2078983
theorem B8342585 : Blo 972592 8342585 := bstep (se 2 (by rfl) ⟨3128469, by rfl⟩ : syracuseStep 8342585 = 6256939) B6256939
theorem B1461311 : Blo 972592 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B137088385 : Blo 972592 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B1461863 : Blo 972592 1461863 := bstep (se 1 (by rfl) ⟨1096397, by rfl⟩ : syracuseStep 1461863 = 2192795) B2192795
theorem B2969399 : Blo 972592 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B1462247 : Blo 972592 1462247 := bstep (se 1 (by rfl) ⟨1096685, by rfl⟩ : syracuseStep 1462247 = 2193371) B2193371
theorem B1462367 : Blo 972592 1462367 := bstep (se 1 (by rfl) ⟨1096775, by rfl⟩ : syracuseStep 1462367 = 2193551) B2193551
theorem B1462379 : Blo 972592 1462379 := bstep (se 1 (by rfl) ⟨1096784, by rfl⟩ : syracuseStep 1462379 = 2193569) B2193569
theorem B1462427 : Blo 972592 1462427 := bstep (se 1 (by rfl) ⟨1096820, by rfl⟩ : syracuseStep 1462427 = 2193641) B2193641
theorem B14045359 : Blo 972592 14045359 := bstep (se 1 (by rfl) ⟨10534019, by rfl⟩ : syracuseStep 14045359 = 21068039) B21068039
theorem B2773435 : Blo 972592 2773435 := bstep (se 1 (by rfl) ⟨2080076, by rfl⟩ : syracuseStep 2773435 = 4160153) B4160153
theorem B1233463 : Blo 972592 1233463 := bstep (se 1 (by rfl) ⟨925097, by rfl⟩ : syracuseStep 1233463 = 1850195) B1850195
theorem B4936301 : Blo 972592 4936301 := bstep (se 3 (by rfl) ⟨925556, by rfl⟩ : syracuseStep 4936301 = 1851113) B1851113
theorem B1463279 : Blo 972592 1463279 := bstep (se 1 (by rfl) ⟨1097459, by rfl⟩ : syracuseStep 1463279 = 2194919) B2194919
theorem B1463663 : Blo 972592 1463663 := bstep (se 1 (by rfl) ⟨1097747, by rfl⟩ : syracuseStep 1463663 = 2195495) B2195495
theorem B1463783 : Blo 972592 1463783 := bstep (se 1 (by rfl) ⟨1097837, by rfl⟩ : syracuseStep 1463783 = 2195675) B2195675
theorem B1562095 : Blo 972592 1562095 := bstep (se 1 (by rfl) ⟨1171571, by rfl⟩ : syracuseStep 1562095 = 2343143) B2343143
theorem B2774665 : Blo 972592 2774665 := bstep (se 2 (by rfl) ⟨1040499, by rfl⟩ : syracuseStep 2774665 = 2080999) B2080999
theorem B1463945 : Blo 972592 1463945 := bstep (se 2 (by rfl) ⟨548979, by rfl⟩ : syracuseStep 1463945 = 1097959) B1097959
theorem B1463963 : Blo 972592 1463963 := bstep (se 1 (by rfl) ⟨1097972, by rfl⟩ : syracuseStep 1463963 = 2195945) B2195945
theorem B86562553 : Blo 972592 86562553 := bstep (se 2 (by rfl) ⟨32460957, by rfl⟩ : syracuseStep 86562553 = 64921915) B64921915
theorem B972615 : Blo 972592 972615 := bstep (se 1 (by rfl) ⟨729461, by rfl⟩ : syracuseStep 972615 = 1458923) B1458923
theorem B1234759 : Blo 972592 1234759 := bstep (se 1 (by rfl) ⟨926069, by rfl⟩ : syracuseStep 1234759 = 1852139) B1852139
theorem B972635 : Blo 972592 972635 := bstep (se 1 (by rfl) ⟨729476, by rfl⟩ : syracuseStep 972635 = 1458953) B1458953
theorem B1464155 : Blo 972592 1464155 := bstep (se 1 (by rfl) ⟨1098116, by rfl⟩ : syracuseStep 1464155 = 2196233) B2196233
theorem B972703 : Blo 972592 972703 := bstep (se 1 (by rfl) ⟨729527, by rfl⟩ : syracuseStep 972703 = 1459055) B1459055
theorem B972871 : Blo 972592 972871 := bstep (se 1 (by rfl) ⟨729653, by rfl⟩ : syracuseStep 972871 = 1459307) B1459307
theorem B1464539 : Blo 972592 1464539 := bstep (se 1 (by rfl) ⟨1098404, by rfl⟩ : syracuseStep 1464539 = 2196809) B2196809
theorem B973031 : Blo 972592 973031 := bstep (se 1 (by rfl) ⟨729773, by rfl⟩ : syracuseStep 973031 = 1459547) B1459547
theorem B973215 : Blo 972592 973215 := bstep (se 1 (by rfl) ⟨729911, by rfl⟩ : syracuseStep 973215 = 1459823) B1459823
theorem B973263 : Blo 972592 973263 := bstep (se 1 (by rfl) ⟨729947, by rfl⟩ : syracuseStep 973263 = 1459895) B1459895
theorem B973287 : Blo 972592 973287 := bstep (se 1 (by rfl) ⟨729965, by rfl⟩ : syracuseStep 973287 = 1459931) B1459931
theorem B1464809 : Blo 972592 1464809 := bstep (se 2 (by rfl) ⟨549303, by rfl⟩ : syracuseStep 1464809 = 1098607) B1098607
theorem B973403 : Blo 972592 973403 := bstep (se 1 (by rfl) ⟨730052, by rfl⟩ : syracuseStep 973403 = 1460105) B1460105
theorem B973471 : Blo 972592 973471 := bstep (se 1 (by rfl) ⟨730103, by rfl⟩ : syracuseStep 973471 = 1460207) B1460207
theorem B973639 : Blo 972592 973639 := bstep (se 1 (by rfl) ⟨730229, by rfl⟩ : syracuseStep 973639 = 1460459) B1460459
theorem B973679 : Blo 972592 973679 := bstep (se 1 (by rfl) ⟨730259, by rfl⟩ : syracuseStep 973679 = 1460519) B1460519
theorem B973735 : Blo 972592 973735 := bstep (se 1 (by rfl) ⟨730301, by rfl⟩ : syracuseStep 973735 = 1460603) B1460603
theorem B4938731 : Blo 972592 4938731 := bstep (se 1 (by rfl) ⟨3704048, by rfl⟩ : syracuseStep 4938731 = 7408097) B7408097
theorem B973915 : Blo 972592 973915 := bstep (se 1 (by rfl) ⟨730436, by rfl⟩ : syracuseStep 973915 = 1460873) B1460873
theorem B974031 : Blo 972592 974031 := bstep (se 1 (by rfl) ⟨730523, by rfl⟩ : syracuseStep 974031 = 1461047) B1461047
theorem B974055 : Blo 972592 974055 := bstep (se 1 (by rfl) ⟨730541, by rfl⟩ : syracuseStep 974055 = 1461083) B1461083
theorem B974151 : Blo 972592 974151 := bstep (se 1 (by rfl) ⟨730613, by rfl⟩ : syracuseStep 974151 = 1461227) B1461227
theorem B974287 : Blo 972592 974287 := bstep (se 1 (by rfl) ⟨730715, by rfl⟩ : syracuseStep 974287 = 1461431) B1461431
theorem B4677097 : Blo 972592 4677097 := bstep (se 2 (by rfl) ⟨1753911, by rfl⟩ : syracuseStep 4677097 = 3507823) B3507823
theorem B974447 : Blo 972592 974447 := bstep (se 1 (by rfl) ⟨730835, by rfl⟩ : syracuseStep 974447 = 1461671) B1461671
theorem B974503 : Blo 972592 974503 := bstep (se 1 (by rfl) ⟨730877, by rfl⟩ : syracuseStep 974503 = 1461755) B1461755
theorem B974567 : Blo 972592 974567 := bstep (se 1 (by rfl) ⟨730925, by rfl⟩ : syracuseStep 974567 = 1461851) B1461851
theorem B3333907 : Blo 972592 3333907 := bstep (se 1 (by rfl) ⟨2500430, by rfl⟩ : syracuseStep 3333907 = 5000861) B5000861
theorem B974623 : Blo 972592 974623 := bstep (se 1 (by rfl) ⟨730967, by rfl⟩ : syracuseStep 974623 = 1461935) B1461935
theorem B974703 : Blo 972592 974703 := bstep (se 1 (by rfl) ⟨731027, by rfl⟩ : syracuseStep 974703 = 1462055) B1462055
theorem B2776943 : Blo 972592 2776943 := bstep (se 1 (by rfl) ⟨2082707, by rfl⟩ : syracuseStep 2776943 = 4165415) B4165415
theorem B974759 : Blo 972592 974759 := bstep (se 1 (by rfl) ⟨731069, by rfl⟩ : syracuseStep 974759 = 1462139) B1462139
theorem B975039 : Blo 972592 975039 := bstep (se 1 (by rfl) ⟨731279, by rfl⟩ : syracuseStep 975039 = 1462559) B1462559
theorem B18735299 : Blo 972592 18735299 := bstep (se 1 (by rfl) ⟨14051474, by rfl⟩ : syracuseStep 18735299 = 28102949) B28102949
theorem B975055 : Blo 972592 975055 := bstep (se 1 (by rfl) ⟨731291, by rfl⟩ : syracuseStep 975055 = 1462583) B1462583
theorem B975103 : Blo 972592 975103 := bstep (se 1 (by rfl) ⟨731327, by rfl⟩ : syracuseStep 975103 = 1462655) B1462655
theorem B975151 : Blo 972592 975151 := bstep (se 1 (by rfl) ⟨731363, by rfl⟩ : syracuseStep 975151 = 1462727) B1462727
theorem B975387 : Blo 972592 975387 := bstep (se 1 (by rfl) ⟨731540, by rfl⟩ : syracuseStep 975387 = 1463081) B1463081
theorem B2777627 : Blo 972592 2777627 := bstep (se 1 (by rfl) ⟨2083220, by rfl⟩ : syracuseStep 2777627 = 4166441) B4166441
theorem B975391 : Blo 972592 975391 := bstep (se 1 (by rfl) ⟨731543, by rfl⟩ : syracuseStep 975391 = 1463087) B1463087
theorem B975471 : Blo 972592 975471 := bstep (se 1 (by rfl) ⟨731603, by rfl⟩ : syracuseStep 975471 = 1463207) B1463207
theorem B975527 : Blo 972592 975527 := bstep (se 1 (by rfl) ⟨731645, by rfl⟩ : syracuseStep 975527 = 1463291) B1463291
theorem B975567 : Blo 972592 975567 := bstep (se 1 (by rfl) ⟨731675, by rfl⟩ : syracuseStep 975567 = 1463351) B1463351
theorem B975647 : Blo 972592 975647 := bstep (se 1 (by rfl) ⟨731735, by rfl⟩ : syracuseStep 975647 = 1463471) B1463471
theorem B975919 : Blo 972592 975919 := bstep (se 1 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 975919 = 1463879) B1463879
theorem B975983 : Blo 972592 975983 := bstep (se 1 (by rfl) ⟨731987, by rfl⟩ : syracuseStep 975983 = 1463975) B1463975
theorem B976039 : Blo 972592 976039 := bstep (se 1 (by rfl) ⟨732029, by rfl⟩ : syracuseStep 976039 = 1464059) B1464059
theorem B976063 : Blo 972592 976063 := bstep (se 1 (by rfl) ⟨732047, by rfl⟩ : syracuseStep 976063 = 1464095) B1464095
theorem B976095 : Blo 972592 976095 := bstep (se 1 (by rfl) ⟨732071, by rfl⟩ : syracuseStep 976095 = 1464143) B1464143
theorem B976175 : Blo 972592 976175 := bstep (se 1 (by rfl) ⟨732131, by rfl⟩ : syracuseStep 976175 = 1464263) B1464263
theorem B2188601 : Blo 972592 2188601 := bstep (se 2 (by rfl) ⟨820725, by rfl⟩ : syracuseStep 2188601 = 1641451) B1641451
theorem B2778425 : Blo 972592 2778425 := bstep (se 2 (by rfl) ⟨1041909, by rfl⟩ : syracuseStep 2778425 = 2083819) B2083819
theorem B4154753 : Blo 972592 4154753 := bstep (se 2 (by rfl) ⟨1558032, by rfl⟩ : syracuseStep 4154753 = 3116065) B3116065
theorem B5629459 : Blo 972592 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B976411 : Blo 972592 976411 := bstep (se 1 (by rfl) ⟨732308, by rfl⟩ : syracuseStep 976411 = 1464617) B1464617
theorem B976415 : Blo 972592 976415 := bstep (se 1 (by rfl) ⟨732311, by rfl⟩ : syracuseStep 976415 = 1464623) B1464623
theorem B2188871 : Blo 972592 2188871 := bstep (se 1 (by rfl) ⟨1641653, by rfl⟩ : syracuseStep 2188871 = 3283307) B3283307
theorem B976575 : Blo 972592 976575 := bstep (se 1 (by rfl) ⟨732431, by rfl⟩ : syracuseStep 976575 = 1464863) B1464863
theorem B2189051 : Blo 972592 2189051 := bstep (se 1 (by rfl) ⟨1641788, by rfl⟩ : syracuseStep 2189051 = 3283577) B3283577
theorem B4941647 : Blo 972592 4941647 := bstep (se 1 (by rfl) ⟨3706235, by rfl⟩ : syracuseStep 4941647 = 7412471) B7412471
theorem B3860303 : Blo 972592 3860303 := bstep (se 1 (by rfl) ⟨2895227, by rfl⟩ : syracuseStep 3860303 = 5790455) B5790455
theorem B2189339 : Blo 972592 2189339 := bstep (se 1 (by rfl) ⟨1642004, by rfl⟩ : syracuseStep 2189339 = 3284009) B3284009
theorem B8317025 : Blo 972592 8317025 := bstep (se 2 (by rfl) ⟨3118884, by rfl⟩ : syracuseStep 8317025 = 6237769) B6237769
theorem B1927289 : Blo 972592 1927289 := bstep (se 2 (by rfl) ⟨722733, by rfl⟩ : syracuseStep 1927289 = 1445467) B1445467
theorem B4155695 : Blo 972592 4155695 := bstep (se 1 (by rfl) ⟨3116771, by rfl⟩ : syracuseStep 4155695 = 6233543) B6233543
theorem B2779667 : Blo 972592 2779667 := bstep (se 1 (by rfl) ⟨2084750, by rfl⟩ : syracuseStep 2779667 = 4169501) B4169501
theorem B24931799 : Blo 972592 24931799 := bstep (se 1 (by rfl) ⟨18698849, by rfl⟩ : syracuseStep 24931799 = 37397699) B37397699
theorem B2190815 : Blo 972592 2190815 := bstep (se 1 (by rfl) ⟨1643111, by rfl⟩ : syracuseStep 2190815 = 3286223) B3286223
theorem B7892473 : Blo 972592 7892473 := bstep (se 2 (by rfl) ⟨2959677, by rfl⟩ : syracuseStep 7892473 = 5919355) B5919355
theorem B2191031 : Blo 972592 2191031 := bstep (se 1 (by rfl) ⟨1643273, by rfl⟩ : syracuseStep 2191031 = 3286547) B3286547
theorem B7401293 : Blo 972592 7401293 := bstep (se 3 (by rfl) ⟨1387742, by rfl⟩ : syracuseStep 7401293 = 2775485) B2775485
theorem B8318801 : Blo 972592 8318801 := bstep (se 2 (by rfl) ⟨3119550, by rfl⟩ : syracuseStep 8318801 = 6239101) B6239101
theorem B10547167 : Blo 972592 10547167 := bstep (se 1 (by rfl) ⟨7910375, by rfl⟩ : syracuseStep 10547167 = 15820751) B15820751
theorem B15790139 : Blo 972592 15790139 := bstep (se 1 (by rfl) ⟨11842604, by rfl⟩ : syracuseStep 15790139 = 23685209) B23685209
theorem B12513467 : Blo 972592 12513467 := bstep (se 1 (by rfl) ⟨9385100, by rfl⟩ : syracuseStep 12513467 = 18770201) B18770201
theorem B3699053 : Blo 972592 3699053 := bstep (se 3 (by rfl) ⟨693572, by rfl⟩ : syracuseStep 3699053 = 1387145) B1387145
theorem B2191823 : Blo 972592 2191823 := bstep (se 1 (by rfl) ⟨1643867, by rfl⟩ : syracuseStep 2191823 = 3287735) B3287735
theorem B2225033 : Blo 972592 2225033 := bstep (se 2 (by rfl) ⟨834387, by rfl⟩ : syracuseStep 2225033 = 1668775) B1668775
theorem B18969491 : Blo 972592 18969491 := bstep (se 1 (by rfl) ⟨14227118, by rfl⟩ : syracuseStep 18969491 = 28454237) B28454237
theorem B4158479 : Blo 972592 4158479 := bstep (se 1 (by rfl) ⟨3118859, by rfl⟩ : syracuseStep 4158479 = 6237719) B6237719
theorem B2192489 : Blo 972592 2192489 := bstep (se 2 (by rfl) ⟨822183, by rfl⟩ : syracuseStep 2192489 = 1644367) B1644367
theorem B7501043 : Blo 972592 7501043 := bstep (se 1 (by rfl) ⟨5625782, by rfl⟩ : syracuseStep 7501043 = 11251565) B11251565
theorem B6256223 : Blo 972592 6256223 := bstep (se 1 (by rfl) ⟨4692167, by rfl⟩ : syracuseStep 6256223 = 9384335) B9384335
theorem B3339929 : Blo 972592 3339929 := bstep (se 2 (by rfl) ⟨1252473, by rfl⟩ : syracuseStep 3339929 = 2504947) B2504947
theorem B2193119 : Blo 972592 2193119 := bstep (se 1 (by rfl) ⟨1644839, by rfl⟩ : syracuseStep 2193119 = 3289679) B3289679
theorem B10516463 : Blo 972592 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B31651883 : Blo 972592 31651883 := bstep (se 1 (by rfl) ⟨23738912, by rfl⟩ : syracuseStep 31651883 = 47477825) B47477825
theorem B2193479 : Blo 972592 2193479 := bstep (se 1 (by rfl) ⟨1645109, by rfl⟩ : syracuseStep 2193479 = 3290219) B3290219
theorem B7403723 : Blo 972592 7403723 := bstep (se 1 (by rfl) ⟨5552792, by rfl⟩ : syracuseStep 7403723 = 11105585) B11105585
theorem B18708691 : Blo 972592 18708691 := bstep (se 1 (by rfl) ⟨14031518, by rfl⟩ : syracuseStep 18708691 = 28063037) B28063037
theorem B6257249 : Blo 972592 6257249 := bstep (se 2 (by rfl) ⟨2346468, by rfl⟩ : syracuseStep 6257249 = 4692937) B4692937
theorem B2194145 : Blo 972592 2194145 := bstep (se 2 (by rfl) ⟨822804, by rfl⟩ : syracuseStep 2194145 = 1645609) B1645609
theorem B3701483 : Blo 972592 3701483 := bstep (se 1 (by rfl) ⟨2776112, by rfl⟩ : syracuseStep 3701483 = 5552225) B5552225
theorem B14220157 : Blo 972592 14220157 := bstep (se 3 (by rfl) ⟨2666279, by rfl⟩ : syracuseStep 14220157 = 5332559) B5332559
theorem B2194343 : Blo 972592 2194343 := bstep (se 1 (by rfl) ⟨1645757, by rfl⟩ : syracuseStep 2194343 = 3291515) B3291515
theorem B2194523 : Blo 972592 2194523 := bstep (se 1 (by rfl) ⟨1645892, by rfl⟩ : syracuseStep 2194523 = 3291785) B3291785
theorem B5274839 : Blo 972592 5274839 := bstep (se 1 (by rfl) ⟨3956129, by rfl⟩ : syracuseStep 5274839 = 7912259) B7912259
theorem B3701983 : Blo 972592 3701983 := bstep (se 1 (by rfl) ⟨2776487, by rfl⟩ : syracuseStep 3701983 = 5552975) B5552975
theorem B54066707 : Blo 972592 54066707 := bstep (se 1 (by rfl) ⟨40550030, by rfl⟩ : syracuseStep 54066707 = 81100061) B81100061
theorem B8453917 : Blo 972592 8453917 := bstep (se 3 (by rfl) ⟨1585109, by rfl⟩ : syracuseStep 8453917 = 3170219) B3170219
theorem B2195279 : Blo 972592 2195279 := bstep (se 1 (by rfl) ⟨1646459, by rfl⟩ : syracuseStep 2195279 = 3292919) B3292919
theorem B3506411 : Blo 972592 3506411 := bstep (se 1 (by rfl) ⟨2629808, by rfl⟩ : syracuseStep 3506411 = 5259617) B5259617
theorem B2195873 : Blo 972592 2195873 := bstep (se 2 (by rfl) ⟨823452, by rfl⟩ : syracuseStep 2195873 = 1646905) B1646905
theorem B5931863 : Blo 972592 5931863 := bstep (se 1 (by rfl) ⟨4448897, by rfl⟩ : syracuseStep 5931863 = 8897795) B8897795
theorem B2196431 : Blo 972592 2196431 := bstep (se 1 (by rfl) ⟨1647323, by rfl⟩ : syracuseStep 2196431 = 3294647) B3294647
theorem B2196521 : Blo 972592 2196521 := bstep (se 2 (by rfl) ⟨823695, by rfl⟩ : syracuseStep 2196521 = 1647391) B1647391
theorem B4162751 : Blo 972592 4162751 := bstep (se 1 (by rfl) ⟨3122063, by rfl⟩ : syracuseStep 4162751 = 6244127) B6244127
theorem B11109959 : Blo 972592 11109959 := bstep (se 1 (by rfl) ⟨8332469, by rfl⟩ : syracuseStep 11109959 = 16664939) B16664939
theorem B7505945 : Blo 972592 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B11079341 : Blo 972592 11079341 := bstep (se 3 (by rfl) ⟨2077376, by rfl⟩ : syracuseStep 11079341 = 4154753) B4154753
theorem B1642207 : Blo 972592 1642207 := bstep (se 1 (by rfl) ⟨1231655, by rfl⟩ : syracuseStep 1642207 = 2463311) B2463311
theorem B3084199 : Blo 972592 3084199 := bstep (se 1 (by rfl) ⟨2313149, by rfl⟩ : syracuseStep 3084199 = 4626299) B4626299
theorem B25268233 : Blo 972592 25268233 := bstep (se 2 (by rfl) ⟨9475587, by rfl⟩ : syracuseStep 25268233 = 18951175) B18951175
theorem B1642639 : Blo 972592 1642639 := bstep (se 1 (by rfl) ⟨1231979, by rfl⟩ : syracuseStep 1642639 = 2463959) B2463959
theorem B10523297 : Blo 972592 10523297 := bstep (se 2 (by rfl) ⟨3946236, by rfl⟩ : syracuseStep 10523297 = 7892473) B7892473
theorem B10294141 : Blo 972592 10294141 := bstep (se 3 (by rfl) ⟨1930151, by rfl⟩ : syracuseStep 10294141 = 3860303) B3860303
theorem B14062889 : Blo 972592 14062889 := bstep (se 2 (by rfl) ⟨5273583, by rfl⟩ : syracuseStep 14062889 = 10547167) B10547167
theorem B12490199 : Blo 972592 12490199 := bstep (se 1 (by rfl) ⟨9367649, by rfl⟩ : syracuseStep 12490199 = 18735299) B18735299
theorem B989215 : Blo 972592 989215 := bstep (se 1 (by rfl) ⟨741911, by rfl⟩ : syracuseStep 989215 = 1483823) B1483823
theorem B3282983 : Blo 972592 3282983 := bstep (se 1 (by rfl) ⟨2462237, by rfl⟩ : syracuseStep 3282983 = 4924475) B4924475
theorem B1644617 : Blo 972592 1644617 := bstep (se 2 (by rfl) ⟨616731, by rfl⟩ : syracuseStep 1644617 = 1233463) B1233463
theorem B1054831 : Blo 972592 1054831 := bstep (se 1 (by rfl) ⟨791123, by rfl⟩ : syracuseStep 1054831 = 1582247) B1582247
theorem B3283361 : Blo 972592 3283361 := bstep (se 2 (by rfl) ⟨1231260, by rfl⟩ : syracuseStep 3283361 = 2462521) B2462521
theorem B5544683 : Blo 972592 5544683 := bstep (se 1 (by rfl) ⟨4158512, by rfl⟩ : syracuseStep 5544683 = 8317025) B8317025
theorem B1284859 : Blo 972592 1284859 := bstep (se 1 (by rfl) ⟨963644, by rfl⟩ : syracuseStep 1284859 = 1927289) B1927289
theorem B3283901 : Blo 972592 3283901 := bstep (se 3 (by rfl) ⟨615731, by rfl⟩ : syracuseStep 3283901 = 1231463) B1231463
theorem B1646183 : Blo 972592 1646183 := bstep (se 1 (by rfl) ⟨1234637, by rfl⟩ : syracuseStep 1646183 = 2469275) B2469275
theorem B1056359 : Blo 972592 1056359 := bstep (se 1 (by rfl) ⟨792269, by rfl⟩ : syracuseStep 1056359 = 1584539) B1584539
theorem B16621199 : Blo 972592 16621199 := bstep (se 1 (by rfl) ⟨12465899, by rfl⟩ : syracuseStep 16621199 = 24931799) B24931799
theorem B115416737 : Blo 972592 115416737 := bstep (se 2 (by rfl) ⟨43281276, by rfl⟩ : syracuseStep 115416737 = 86562553) B86562553
theorem B1646345 : Blo 972592 1646345 := bstep (se 2 (by rfl) ⟨617379, by rfl⟩ : syracuseStep 1646345 = 1234759) B1234759
theorem B5545867 : Blo 972592 5545867 := bstep (se 1 (by rfl) ⟨4159400, by rfl⟩ : syracuseStep 5545867 = 8318801) B8318801
theorem B8331173 : Blo 972592 8331173 := bstep (se 4 (by rfl) ⟨781047, by rfl⟩ : syracuseStep 8331173 = 1562095) B1562095
theorem B2924552213 : Blo 972592 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B10526759 : Blo 972592 10526759 := bstep (se 1 (by rfl) ⟨7895069, by rfl⟩ : syracuseStep 10526759 = 15790139) B15790139
theorem B2466035 : Blo 972592 2466035 := bstep (se 1 (by rfl) ⟨1849526, by rfl⟩ : syracuseStep 2466035 = 3699053) B3699053
theorem B24944921 : Blo 972592 24944921 := bstep (se 2 (by rfl) ⟨9354345, by rfl⟩ : syracuseStep 24944921 = 18708691) B18708691
theorem B14066237 : Blo 972592 14066237 := bstep (se 3 (by rfl) ⟨2637419, by rfl⟩ : syracuseStep 14066237 = 5274839) B5274839
theorem B1483355 : Blo 972592 1483355 := bstep (se 1 (by rfl) ⟨1112516, by rfl⟩ : syracuseStep 1483355 = 2225033) B2225033
theorem B2466409 : Blo 972592 2466409 := bstep (se 2 (by rfl) ⟨924903, by rfl⟩ : syracuseStep 2466409 = 1849807) B1849807
theorem B4170815 : Blo 972592 4170815 := bstep (se 1 (by rfl) ⟨3128111, by rfl⟩ : syracuseStep 4170815 = 6256223) B6256223
theorem B4924637 : Blo 972592 4924637 := bstep (se 3 (by rfl) ⟨923369, by rfl⟩ : syracuseStep 4924637 = 1846739) B1846739
theorem B4171499 : Blo 972592 4171499 := bstep (se 1 (by rfl) ⟨3128624, by rfl⟩ : syracuseStep 4171499 = 6257249) B6257249
theorem B2467655 : Blo 972592 2467655 := bstep (se 1 (by rfl) ⟨1850741, by rfl⟩ : syracuseStep 2467655 = 3701483) B3701483
theorem B6236129 : Blo 972592 6236129 := bstep (se 2 (by rfl) ⟨2338548, by rfl⟩ : syracuseStep 6236129 = 4677097) B4677097
theorem B1976809 : Blo 972592 1976809 := bstep (se 2 (by rfl) ⟨741303, by rfl⟩ : syracuseStep 1976809 = 1482607) B1482607
theorem B1386991 : Blo 972592 1386991 := bstep (se 1 (by rfl) ⟨1040243, by rfl⟩ : syracuseStep 1386991 = 2080487) B2080487
theorem B36056335 : Blo 972592 36056335 := bstep (se 1 (by rfl) ⟨27042251, by rfl⟩ : syracuseStep 36056335 = 54084503) B54084503
theorem B7515575 : Blo 972592 7515575 := bstep (se 1 (by rfl) ⟨5636681, by rfl⟩ : syracuseStep 7515575 = 11273363) B11273363
theorem B4927067 : Blo 972592 4927067 := bstep (se 1 (by rfl) ⟨3695300, by rfl⟩ : syracuseStep 4927067 = 7390601) B7390601
theorem B5648201 : Blo 972592 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B1847279 : Blo 972592 1847279 := bstep (se 1 (by rfl) ⟨1385459, by rfl⟩ : syracuseStep 1847279 = 2770919) B2770919
theorem B3944551 : Blo 972592 3944551 := bstep (se 1 (by rfl) ⟨2958413, by rfl⟩ : syracuseStep 3944551 = 5916827) B5916827
theorem B1094431 : Blo 972592 1094431 := bstep (se 1 (by rfl) ⟨820823, by rfl⟩ : syracuseStep 1094431 = 1641647) B1641647
theorem B2470895 : Blo 972592 2470895 := bstep (se 1 (by rfl) ⟨1853171, by rfl⟩ : syracuseStep 2470895 = 3706343) B3706343
theorem B3290489 : Blo 972592 3290489 := bstep (se 2 (by rfl) ⟨1233933, by rfl⟩ : syracuseStep 3290489 = 2467867) B2467867
theorem B3290867 : Blo 972592 3290867 := bstep (se 1 (by rfl) ⟨2468150, by rfl⟩ : syracuseStep 3290867 = 4936301) B4936301
theorem B20002781 : Blo 972592 20002781 := bstep (se 3 (by rfl) ⟨3750521, by rfl⟩ : syracuseStep 20002781 = 7501043) B7501043
theorem B2340971 : Blo 972592 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B6666695 : Blo 972592 6666695 := bstep (se 1 (by rfl) ⟨5000021, by rfl⟩ : syracuseStep 6666695 = 10000043) B10000043
theorem B4995689 : Blo 972592 4995689 := bstep (se 2 (by rfl) ⟨1873383, by rfl⟩ : syracuseStep 4995689 = 3746767) B3746767
theorem B3292487 : Blo 972592 3292487 := bstep (se 1 (by rfl) ⟨2469365, by rfl⟩ : syracuseStep 3292487 = 4938731) B4938731
theorem B10534711 : Blo 972592 10534711 := bstep (se 1 (by rfl) ⟨7901033, by rfl⟩ : syracuseStep 10534711 = 15802067) B15802067
theorem B1753321 : Blo 972592 1753321 := bstep (se 2 (by rfl) ⟨657495, by rfl⟩ : syracuseStep 1753321 = 1314991) B1314991
theorem B18727145 : Blo 972592 18727145 := bstep (se 2 (by rfl) ⟨7022679, by rfl⟩ : syracuseStep 18727145 = 14045359) B14045359
theorem B1851751 : Blo 972592 1851751 := bstep (se 1 (by rfl) ⟨1388813, by rfl⟩ : syracuseStep 1851751 = 2777627) B2777627
theorem B1459067 : Blo 972592 1459067 := bstep (se 1 (by rfl) ⟨1094300, by rfl⟩ : syracuseStep 1459067 = 2188601) B2188601
theorem B1852283 : Blo 972592 1852283 := bstep (se 1 (by rfl) ⟨1389212, by rfl⟩ : syracuseStep 1852283 = 2778425) B2778425
theorem B1459193 : Blo 972592 1459193 := bstep (se 2 (by rfl) ⟨547197, by rfl⟩ : syracuseStep 1459193 = 1094395) B1094395
theorem B1459247 : Blo 972592 1459247 := bstep (se 1 (by rfl) ⟨1094435, by rfl⟩ : syracuseStep 1459247 = 2188871) B2188871
theorem B1459367 : Blo 972592 1459367 := bstep (se 1 (by rfl) ⟨1094525, by rfl⟩ : syracuseStep 1459367 = 2189051) B2189051
theorem B3294431 : Blo 972592 3294431 := bstep (se 1 (by rfl) ⟨2470823, by rfl⟩ : syracuseStep 3294431 = 4941647) B4941647
theorem B1459559 : Blo 972592 1459559 := bstep (se 1 (by rfl) ⟨1094669, by rfl⟩ : syracuseStep 1459559 = 2189339) B2189339
theorem B2770463 : Blo 972592 2770463 := bstep (se 1 (by rfl) ⟨2077847, by rfl⟩ : syracuseStep 2770463 = 4155695) B4155695
theorem B6014515 : Blo 972592 6014515 := bstep (se 1 (by rfl) ⟨4510886, by rfl⟩ : syracuseStep 6014515 = 9021773) B9021773
theorem B1853111 : Blo 972592 1853111 := bstep (se 1 (by rfl) ⟨1389833, by rfl⟩ : syracuseStep 1853111 = 2779667) B2779667
theorem B2532526037 : Blo 972592 2532526037 := bstep (se 7 (by rfl) ⟨29678039, by rfl⟩ : syracuseStep 2532526037 = 59356079) B59356079
theorem B1460201 : Blo 972592 1460201 := bstep (se 2 (by rfl) ⟨547575, by rfl⟩ : syracuseStep 1460201 = 1095151) B1095151
theorem B1460345 : Blo 972592 1460345 := bstep (se 2 (by rfl) ⟨547629, by rfl⟩ : syracuseStep 1460345 = 1095259) B1095259
theorem B1460543 : Blo 972592 1460543 := bstep (se 1 (by rfl) ⟨1095407, by rfl⟩ : syracuseStep 1460543 = 2190815) B2190815
theorem B1460687 : Blo 972592 1460687 := bstep (se 1 (by rfl) ⟨1095515, by rfl⟩ : syracuseStep 1460687 = 2191031) B2191031
theorem B1460729 : Blo 972592 1460729 := bstep (se 2 (by rfl) ⟨547773, by rfl⟩ : syracuseStep 1460729 = 1095547) B1095547
theorem B10013179 : Blo 972592 10013179 := bstep (se 1 (by rfl) ⟨7509884, by rfl⟩ : syracuseStep 10013179 = 15019769) B15019769
theorem B1460777 : Blo 972592 1460777 := bstep (se 2 (by rfl) ⟨547791, by rfl⟩ : syracuseStep 1460777 = 1095583) B1095583
theorem B4934195 : Blo 972592 4934195 := bstep (se 1 (by rfl) ⟨3700646, by rfl⟩ : syracuseStep 4934195 = 7401293) B7401293
theorem B1231615 : Blo 972592 1231615 := bstep (se 1 (by rfl) ⟨923711, by rfl⟩ : syracuseStep 1231615 = 1847423) B1847423
theorem B8342311 : Blo 972592 8342311 := bstep (se 1 (by rfl) ⟨6256733, by rfl⟩ : syracuseStep 8342311 = 12513467) B12513467
theorem B7392059 : Blo 972592 7392059 := bstep (se 1 (by rfl) ⟨5544044, by rfl⟩ : syracuseStep 7392059 = 11088089) B11088089
theorem B1461215 : Blo 972592 1461215 := bstep (se 1 (by rfl) ⟨1095911, by rfl⟩ : syracuseStep 1461215 = 2191823) B2191823
theorem B2772319 : Blo 972592 2772319 := bstep (se 1 (by rfl) ⟨2079239, by rfl⟩ : syracuseStep 2772319 = 4158479) B4158479
theorem B1461659 : Blo 972592 1461659 := bstep (se 1 (by rfl) ⟨1096244, by rfl⟩ : syracuseStep 1461659 = 2192489) B2192489
theorem B7393031 : Blo 972592 7393031 := bstep (se 1 (by rfl) ⟨5544773, by rfl⟩ : syracuseStep 7393031 = 11089547) B11089547
theorem B1462025 : Blo 972592 1462025 := bstep (se 2 (by rfl) ⟨548259, by rfl⟩ : syracuseStep 1462025 = 1096519) B1096519
theorem B1462079 : Blo 972592 1462079 := bstep (se 1 (by rfl) ⟨1096559, by rfl⟩ : syracuseStep 1462079 = 2193119) B2193119
theorem B1756991 : Blo 972592 1756991 := bstep (se 1 (by rfl) ⟨1317743, by rfl⟩ : syracuseStep 1756991 = 2635487) B2635487
theorem B18960209 : Blo 972592 18960209 := bstep (se 2 (by rfl) ⟨7110078, by rfl⟩ : syracuseStep 18960209 = 14220157) B14220157
theorem B14995439 : Blo 972592 14995439 := bstep (se 1 (by rfl) ⟨11246579, by rfl⟩ : syracuseStep 14995439 = 22493159) B22493159
theorem B1462319 : Blo 972592 1462319 := bstep (se 1 (by rfl) ⟨1096739, by rfl⟩ : syracuseStep 1462319 = 2193479) B2193479
theorem B4935815 : Blo 972592 4935815 := bstep (se 1 (by rfl) ⟨3701861, by rfl⟩ : syracuseStep 4935815 = 7403723) B7403723
theorem B3330323 : Blo 972592 3330323 := bstep (se 1 (by rfl) ⟨2497742, by rfl⟩ : syracuseStep 3330323 = 4995485) B4995485
theorem B4935977 : Blo 972592 4935977 := bstep (se 2 (by rfl) ⟨1850991, by rfl⟩ : syracuseStep 4935977 = 3701983) B3701983
theorem B1462763 : Blo 972592 1462763 := bstep (se 1 (by rfl) ⟨1097072, by rfl⟩ : syracuseStep 1462763 = 2194145) B2194145
theorem B2773561 : Blo 972592 2773561 := bstep (se 2 (by rfl) ⟨1040085, by rfl⟩ : syracuseStep 2773561 = 2080171) B2080171
theorem B1462889 : Blo 972592 1462889 := bstep (se 2 (by rfl) ⟨548583, by rfl⟩ : syracuseStep 1462889 = 1097167) B1097167
theorem B1462895 : Blo 972592 1462895 := bstep (se 1 (by rfl) ⟨1097171, by rfl⟩ : syracuseStep 1462895 = 2194343) B2194343
theorem B1463015 : Blo 972592 1463015 := bstep (se 1 (by rfl) ⟨1097261, by rfl⟩ : syracuseStep 1463015 = 2194523) B2194523
theorem B7918397 : Blo 972592 7918397 := bstep (se 3 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 7918397 = 2969399) B2969399
theorem B1463177 : Blo 972592 1463177 := bstep (se 2 (by rfl) ⟨548691, by rfl⟩ : syracuseStep 1463177 = 1097383) B1097383
theorem B4445209 : Blo 972592 4445209 := bstep (se 2 (by rfl) ⟨1666953, by rfl⟩ : syracuseStep 4445209 = 3333907) B3333907
theorem B1463519 : Blo 972592 1463519 := bstep (se 1 (by rfl) ⟨1097639, by rfl⟩ : syracuseStep 1463519 = 2195279) B2195279
theorem B1463561 : Blo 972592 1463561 := bstep (se 2 (by rfl) ⟨548835, by rfl⟩ : syracuseStep 1463561 = 1097671) B1097671
theorem B1463999 : Blo 972592 1463999 := bstep (se 1 (by rfl) ⟨1097999, by rfl⟩ : syracuseStep 1463999 = 2195999) B2195999
theorem B4937435 : Blo 972592 4937435 := bstep (se 1 (by rfl) ⟨3703076, by rfl⟩ : syracuseStep 4937435 = 7406153) B7406153
theorem B1464041 : Blo 972592 1464041 := bstep (se 2 (by rfl) ⟨549015, by rfl⟩ : syracuseStep 1464041 = 1098031) B1098031
theorem B1464047 : Blo 972592 1464047 := bstep (se 1 (by rfl) ⟨1098035, by rfl⟩ : syracuseStep 1464047 = 2196071) B2196071
theorem B972927 : Blo 972592 972927 := bstep (se 1 (by rfl) ⟨729695, by rfl⟩ : syracuseStep 972927 = 1459391) B1459391
theorem B5560447 : Blo 972592 5560447 := bstep (se 1 (by rfl) ⟨4170335, by rfl⟩ : syracuseStep 5560447 = 8340671) B8340671
theorem B973023 : Blo 972592 973023 := bstep (se 1 (by rfl) ⟨729767, by rfl⟩ : syracuseStep 973023 = 1459535) B1459535
theorem B1464551 : Blo 972592 1464551 := bstep (se 1 (by rfl) ⟨1098413, by rfl⟩ : syracuseStep 1464551 = 2196827) B2196827
theorem B973083 : Blo 972592 973083 := bstep (se 1 (by rfl) ⟨729812, by rfl⟩ : syracuseStep 973083 = 1459625) B1459625
theorem B973183 : Blo 972592 973183 := bstep (se 1 (by rfl) ⟨729887, by rfl⟩ : syracuseStep 973183 = 1459775) B1459775
theorem B973211 : Blo 972592 973211 := bstep (se 1 (by rfl) ⟨729908, by rfl⟩ : syracuseStep 973211 = 1459817) B1459817
theorem B1464731 : Blo 972592 1464731 := bstep (se 1 (by rfl) ⟨1098548, by rfl⟩ : syracuseStep 1464731 = 2197097) B2197097
theorem B6249149 : Blo 972592 6249149 := bstep (se 3 (by rfl) ⟨1171715, by rfl⟩ : syracuseStep 6249149 = 2343431) B2343431
theorem B973503 : Blo 972592 973503 := bstep (se 1 (by rfl) ⟨730127, by rfl⟩ : syracuseStep 973503 = 1460255) B1460255
theorem B973631 : Blo 972592 973631 := bstep (se 1 (by rfl) ⟨730223, by rfl⟩ : syracuseStep 973631 = 1460447) B1460447
theorem B973671 : Blo 972592 973671 := bstep (se 1 (by rfl) ⟨730253, by rfl⟩ : syracuseStep 973671 = 1460507) B1460507
theorem B973887 : Blo 972592 973887 := bstep (se 1 (by rfl) ⟨730415, by rfl⟩ : syracuseStep 973887 = 1460831) B1460831
theorem B2776169 : Blo 972592 2776169 := bstep (se 2 (by rfl) ⟨1041063, by rfl⟩ : syracuseStep 2776169 = 2082127) B2082127
theorem B974075 : Blo 972592 974075 := bstep (se 1 (by rfl) ⟨730556, by rfl⟩ : syracuseStep 974075 = 1461113) B1461113
theorem B974107 : Blo 972592 974107 := bstep (se 1 (by rfl) ⟨730580, by rfl⟩ : syracuseStep 974107 = 1461161) B1461161
theorem B5561723 : Blo 972592 5561723 := bstep (se 1 (by rfl) ⟨4171292, by rfl⟩ : syracuseStep 5561723 = 8342585) B8342585
theorem B974207 : Blo 972592 974207 := bstep (se 1 (by rfl) ⟨730655, by rfl⟩ : syracuseStep 974207 = 1461311) B1461311
theorem B50552225 : Blo 972592 50552225 := bstep (se 2 (by rfl) ⟨18957084, by rfl⟩ : syracuseStep 50552225 = 37914169) B37914169
theorem B50585309 : Blo 972592 50585309 := bstep (se 3 (by rfl) ⟨9484745, by rfl⟩ : syracuseStep 50585309 = 18969491) B18969491
theorem B974575 : Blo 972592 974575 := bstep (se 1 (by rfl) ⟨730931, by rfl⟩ : syracuseStep 974575 = 1461863) B1461863
theorem B4939703 : Blo 972592 4939703 := bstep (se 1 (by rfl) ⟨3704777, by rfl⟩ : syracuseStep 4939703 = 7409555) B7409555
theorem B974831 : Blo 972592 974831 := bstep (se 1 (by rfl) ⟨731123, by rfl⟩ : syracuseStep 974831 = 1462247) B1462247
theorem B974911 : Blo 972592 974911 := bstep (se 1 (by rfl) ⟨731183, by rfl⟩ : syracuseStep 974911 = 1462367) B1462367
theorem B974919 : Blo 972592 974919 := bstep (se 1 (by rfl) ⟨731189, by rfl⟩ : syracuseStep 974919 = 1462379) B1462379
theorem B974951 : Blo 972592 974951 := bstep (se 1 (by rfl) ⟨731213, by rfl⟩ : syracuseStep 974951 = 1462427) B1462427
theorem B6250891 : Blo 972592 6250891 := bstep (se 1 (by rfl) ⟨4688168, by rfl⟩ : syracuseStep 6250891 = 9376337) B9376337
theorem B4940351 : Blo 972592 4940351 := bstep (se 1 (by rfl) ⟨3705263, by rfl⟩ : syracuseStep 4940351 = 7410527) B7410527
theorem B975519 : Blo 972592 975519 := bstep (se 1 (by rfl) ⟨731639, by rfl⟩ : syracuseStep 975519 = 1463279) B1463279
theorem B7037675 : Blo 972592 7037675 := bstep (se 1 (by rfl) ⟨5278256, by rfl⟩ : syracuseStep 7037675 = 10556513) B10556513
theorem B10674953 : Blo 972592 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B975775 : Blo 972592 975775 := bstep (se 1 (by rfl) ⟨731831, by rfl⟩ : syracuseStep 975775 = 1463663) B1463663
theorem B975855 : Blo 972592 975855 := bstep (se 1 (by rfl) ⟨731891, by rfl⟩ : syracuseStep 975855 = 1463783) B1463783
theorem B975963 : Blo 972592 975963 := bstep (se 1 (by rfl) ⟨731972, by rfl⟩ : syracuseStep 975963 = 1463945) B1463945
theorem B975975 : Blo 972592 975975 := bstep (se 1 (by rfl) ⟨731981, by rfl⟩ : syracuseStep 975975 = 1463963) B1463963
theorem B976103 : Blo 972592 976103 := bstep (se 1 (by rfl) ⟨732077, by rfl⟩ : syracuseStep 976103 = 1464155) B1464155
theorem B3695969 : Blo 972592 3695969 := bstep (se 2 (by rfl) ⟨1385988, by rfl⟩ : syracuseStep 3695969 = 2771977) B2771977
theorem B5268893 : Blo 972592 5268893 := bstep (se 3 (by rfl) ⟨987917, by rfl⟩ : syracuseStep 5268893 = 1975835) B1975835
theorem B976359 : Blo 972592 976359 := bstep (se 1 (by rfl) ⟨732269, by rfl⟩ : syracuseStep 976359 = 1464539) B1464539
theorem B976539 : Blo 972592 976539 := bstep (se 1 (by rfl) ⟨732404, by rfl⟩ : syracuseStep 976539 = 1464809) B1464809
theorem B5007595 : Blo 972592 5007595 := bstep (se 1 (by rfl) ⟨3755696, by rfl⟩ : syracuseStep 5007595 = 7511393) B7511393
theorem B13330919 : Blo 972592 13330919 := bstep (se 1 (by rfl) ⟨9998189, by rfl⟩ : syracuseStep 13330919 = 19996379) B19996379
theorem B3697913 : Blo 972592 3697913 := bstep (se 2 (by rfl) ⟨1386717, by rfl⟩ : syracuseStep 3697913 = 2773435) B2773435
theorem B3698095 : Blo 972592 3698095 := bstep (se 1 (by rfl) ⟨2773571, by rfl⟩ : syracuseStep 3698095 = 5547143) B5547143
theorem B2191067 : Blo 972592 2191067 := bstep (se 1 (by rfl) ⟨1643300, by rfl⟩ : syracuseStep 2191067 = 3286601) B3286601
theorem B11104127 : Blo 972592 11104127 := bstep (se 1 (by rfl) ⟨8328095, by rfl⟩ : syracuseStep 11104127 = 16656191) B16656191
theorem B2191337 : Blo 972592 2191337 := bstep (se 2 (by rfl) ⟨821751, by rfl⟩ : syracuseStep 2191337 = 1643503) B1643503
theorem B2191391 : Blo 972592 2191391 := bstep (se 1 (by rfl) ⟨1643543, by rfl⟩ : syracuseStep 2191391 = 3287087) B3287087
theorem B28143773 : Blo 972592 28143773 := bstep (se 3 (by rfl) ⟨5276957, by rfl⟩ : syracuseStep 28143773 = 10553915) B10553915
theorem B4157693 : Blo 972592 4157693 := bstep (se 3 (by rfl) ⟨779567, by rfl⟩ : syracuseStep 4157693 = 1559135) B1559135
theorem B3699067 : Blo 972592 3699067 := bstep (se 1 (by rfl) ⟨2774300, by rfl⟩ : syracuseStep 3699067 = 5548601) B5548601
theorem B2192219 : Blo 972592 2192219 := bstep (se 1 (by rfl) ⟨1644164, by rfl⟩ : syracuseStep 2192219 = 3288329) B3288329
theorem B3699553 : Blo 972592 3699553 := bstep (se 2 (by rfl) ⟨1387332, by rfl⟩ : syracuseStep 3699553 = 2774665) B2774665
theorem B5928875 : Blo 972592 5928875 := bstep (se 1 (by rfl) ⟨4446656, by rfl⟩ : syracuseStep 5928875 = 8893313) B8893313
theorem B5404967 : Blo 972592 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B4159811 : Blo 972592 4159811 := bstep (se 1 (by rfl) ⟨3119858, by rfl⟩ : syracuseStep 4159811 = 6239717) B6239717
theorem B16021871 : Blo 972592 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B2226619 : Blo 972592 2226619 := bstep (se 1 (by rfl) ⟨1669964, by rfl⟩ : syracuseStep 2226619 = 3339929) B3339929
theorem B2193947 : Blo 972592 2193947 := bstep (se 1 (by rfl) ⟨1645460, by rfl⟩ : syracuseStep 2193947 = 3290921) B3290921
theorem B7010975 : Blo 972592 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B21101255 : Blo 972592 21101255 := bstep (se 1 (by rfl) ⟨15825941, by rfl⟩ : syracuseStep 21101255 = 31651883) B31651883
theorem B4684999 : Blo 972592 4684999 := bstep (se 1 (by rfl) ⟨3513749, by rfl⟩ : syracuseStep 4684999 = 7027499) B7027499
theorem B7405181 : Blo 972592 7405181 := bstep (se 3 (by rfl) ⟨1388471, by rfl⟩ : syracuseStep 7405181 = 2776943) B2776943
theorem B36044471 : Blo 972592 36044471 := bstep (se 1 (by rfl) ⟨27033353, by rfl⟩ : syracuseStep 36044471 = 54066707) B54066707
theorem B11271889 : Blo 972592 11271889 := bstep (se 2 (by rfl) ⟨4226958, by rfl⟩ : syracuseStep 11271889 = 8453917) B8453917
theorem B12484763 : Blo 972592 12484763 := bstep (se 1 (by rfl) ⟨9363572, by rfl⟩ : syracuseStep 12484763 = 18727145) B18727145
theorem B21103253 : Blo 972592 21103253 := bstep (se 6 (by rfl) ⟨494607, by rfl⟩ : syracuseStep 21103253 = 989215) B989215
theorem B2196287 : Blo 972592 2196287 := bstep (se 1 (by rfl) ⟨1647215, by rfl⟩ : syracuseStep 2196287 = 3294431) B3294431
theorem B7406639 : Blo 972592 7406639 := bstep (se 1 (by rfl) ⟨5554979, by rfl⟩ : syracuseStep 7406639 = 11109959) B11109959
theorem B9996959 : Blo 972592 9996959 := bstep (se 1 (by rfl) ⟨7497719, by rfl⟩ : syracuseStep 9996959 = 14995439) B14995439
theorem B7015531 : Blo 972592 7015531 := bstep (se 1 (by rfl) ⟨5261648, by rfl⟩ : syracuseStep 7015531 = 10523297) B10523297
theorem B5278931 : Blo 972592 5278931 := bstep (se 1 (by rfl) ⟨3959198, by rfl⟩ : syracuseStep 5278931 = 7918397) B7918397
theorem B9375259 : Blo 972592 9375259 := bstep (se 1 (by rfl) ⟨7031444, by rfl⟩ : syracuseStep 9375259 = 14062889) B14062889
theorem B8326799 : Blo 972592 8326799 := bstep (se 1 (by rfl) ⟨6245099, by rfl⟩ : syracuseStep 8326799 = 12490199) B12490199
theorem B1642153 : Blo 972592 1642153 := bstep (se 2 (by rfl) ⟨615807, by rfl⟩ : syracuseStep 1642153 = 1231615) B1231615
theorem B48075113 : Blo 972592 48075113 := bstep (se 2 (by rfl) ⟨18028167, by rfl⟩ : syracuseStep 48075113 = 36056335) B36056335
theorem B4166099 : Blo 972592 4166099 := bstep (se 1 (by rfl) ⟨3124574, by rfl⟩ : syracuseStep 4166099 = 6249149) B6249149
theorem B3707815 : Blo 972592 3707815 := bstep (se 1 (by rfl) ⟨2780861, by rfl⟩ : syracuseStep 3707815 = 5561723) B5561723
theorem B11080799 : Blo 972592 11080799 := bstep (se 1 (by rfl) ⟨8310599, by rfl⟩ : syracuseStep 11080799 = 16621199) B16621199
theorem B76944491 : Blo 972592 76944491 := bstep (se 1 (by rfl) ⟨57708368, by rfl⟩ : syracuseStep 76944491 = 115416737) B115416737
theorem B33723539 : Blo 972592 33723539 := bstep (se 1 (by rfl) ⟨25292654, by rfl⟩ : syracuseStep 33723539 = 50585309) B50585309
theorem B33690977 : Blo 972592 33690977 := bstep (se 2 (by rfl) ⟨12634116, by rfl⟩ : syracuseStep 33690977 = 25268233) B25268233
theorem B1949701475 : Blo 972592 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B7017839 : Blo 972592 7017839 := bstep (se 1 (by rfl) ⟨5263379, by rfl⟩ : syracuseStep 7017839 = 10526759) B10526759
theorem B1644023 : Blo 972592 1644023 := bstep (se 1 (by rfl) ⟨1233017, by rfl⟩ : syracuseStep 1644023 = 2466035) B2466035
theorem B9377491 : Blo 972592 9377491 := bstep (se 1 (by rfl) ⟨7033118, by rfl⟩ : syracuseStep 9377491 = 14066237) B14066237
theorem B988903 : Blo 972592 988903 := bstep (se 1 (by rfl) ⟨741677, by rfl⟩ : syracuseStep 988903 = 1483355) B1483355
theorem B4691783 : Blo 972592 4691783 := bstep (se 1 (by rfl) ⟨3518837, by rfl⟩ : syracuseStep 4691783 = 7037675) B7037675
theorem B7116635 : Blo 972592 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B3283091 : Blo 972592 3283091 := bstep (se 1 (by rfl) ⟨2462318, by rfl⟩ : syracuseStep 3283091 = 4924637) B4924637
theorem B2463979 : Blo 972592 2463979 := bstep (se 1 (by rfl) ⟨1847984, by rfl⟩ : syracuseStep 2463979 = 3695969) B3695969
theorem B1645103 : Blo 972592 1645103 := bstep (se 1 (by rfl) ⟨1233827, by rfl⟩ : syracuseStep 1645103 = 2467655) B2467655
theorem B2465275 : Blo 972592 2465275 := bstep (se 1 (by rfl) ⟨1848956, by rfl⟩ : syracuseStep 2465275 = 3697913) B3697913
theorem B3284711 : Blo 972592 3284711 := bstep (se 1 (by rfl) ⟨2463533, by rfl⟩ : syracuseStep 3284711 = 4927067) B4927067
theorem B7413929 : Blo 972592 7413929 := bstep (se 2 (by rfl) ⟨2780223, by rfl⟩ : syracuseStep 7413929 = 5560447) B5560447
theorem B1647263 : Blo 972592 1647263 := bstep (se 1 (by rfl) ⟨1235447, by rfl⟩ : syracuseStep 1647263 = 2470895) B2470895
theorem B1713145 : Blo 972592 1713145 := bstep (se 2 (by rfl) ⟨642429, by rfl⟩ : syracuseStep 1713145 = 1284859) B1284859
theorem B14067503 : Blo 972592 14067503 := bstep (se 1 (by rfl) ⟨10550627, by rfl⟩ : syracuseStep 14067503 = 21101255) B21101255
theorem B96118589 : Blo 972592 96118589 := bstep (se 3 (by rfl) ⟨18022235, by rfl⟩ : syracuseStep 96118589 = 36044471) B36044471
theorem B2337607 : Blo 972592 2337607 := bstep (se 1 (by rfl) ⟨1753205, by rfl⟩ : syracuseStep 2337607 = 3506411) B3506411
theorem B2337761 : Blo 972592 2337761 := bstep (se 2 (by rfl) ⟨876660, by rfl⟩ : syracuseStep 2337761 = 1753321) B1753321
theorem B2469001 : Blo 972592 2469001 := bstep (se 2 (by rfl) ⟨925875, by rfl⟩ : syracuseStep 2469001 = 1851751) B1851751
theorem B8334521 : Blo 972592 8334521 := bstep (se 2 (by rfl) ⟨3125445, by rfl⟩ : syracuseStep 8334521 = 6250891) B6250891
theorem B3288545 : Blo 972592 3288545 := bstep (se 2 (by rfl) ⟨1233204, by rfl⟩ : syracuseStep 3288545 = 2466409) B2466409
theorem B1846975 : Blo 972592 1846975 := bstep (se 1 (by rfl) ⟨1385231, by rfl⟩ : syracuseStep 1846975 = 2770463) B2770463
theorem B1688350691 : Blo 972592 1688350691 := bstep (se 1 (by rfl) ⟨1266263018, by rfl⟩ : syracuseStep 1688350691 = 2532526037) B2532526037
theorem B3289463 : Blo 972592 3289463 := bstep (se 1 (by rfl) ⟨2467097, by rfl⟩ : syracuseStep 3289463 = 4934195) B4934195
theorem B4928039 : Blo 972592 4928039 := bstep (se 1 (by rfl) ⟨3696029, by rfl⟩ : syracuseStep 4928039 = 7392059) B7392059
theorem B7386227 : Blo 972592 7386227 := bstep (se 1 (by rfl) ⟨5539670, by rfl⟩ : syracuseStep 7386227 = 11079341) B11079341
theorem B4928687 : Blo 972592 4928687 := bstep (se 1 (by rfl) ⟨3696515, by rfl⟩ : syracuseStep 4928687 = 7393031) B7393031
theorem B3290543 : Blo 972592 3290543 := bstep (se 1 (by rfl) ⟨2467907, by rfl⟩ : syracuseStep 3290543 = 4935815) B4935815
theorem B3290651 : Blo 972592 3290651 := bstep (se 1 (by rfl) ⟨2467988, by rfl⟩ : syracuseStep 3290651 = 4935977) B4935977
theorem B2635745 : Blo 972592 2635745 := bstep (se 2 (by rfl) ⟨988404, by rfl⟩ : syracuseStep 2635745 = 1976809) B1976809
theorem B1849321 : Blo 972592 1849321 := bstep (se 2 (by rfl) ⟨693495, by rfl⟩ : syracuseStep 1849321 = 1386991) B1386991
theorem B13350905 : Blo 972592 13350905 := bstep (se 2 (by rfl) ⟨5006589, by rfl⟩ : syracuseStep 13350905 = 10013179) B10013179
theorem B11123081 : Blo 972592 11123081 := bstep (se 2 (by rfl) ⟨4171155, by rfl⟩ : syracuseStep 11123081 = 8342311) B8342311
theorem B3291623 : Blo 972592 3291623 := bstep (se 1 (by rfl) ⟨2468717, by rfl⟩ : syracuseStep 3291623 = 4937435) B4937435
theorem B1096411 : Blo 972592 1096411 := bstep (se 1 (by rfl) ⟨822308, by rfl⟩ : syracuseStep 1096411 = 1644617) B1644617
theorem B4930793 : Blo 972592 4930793 := bstep (se 2 (by rfl) ⟨1849047, by rfl⟩ : syracuseStep 4930793 = 3698095) B3698095
theorem B1850779 : Blo 972592 1850779 := bstep (se 1 (by rfl) ⟨1388084, by rfl⟩ : syracuseStep 1850779 = 2776169) B2776169
theorem B33701483 : Blo 972592 33701483 := bstep (se 1 (by rfl) ⟨25276112, by rfl⟩ : syracuseStep 33701483 = 50552225) B50552225
theorem B1097455 : Blo 972592 1097455 := bstep (se 1 (by rfl) ⟨823091, by rfl⟩ : syracuseStep 1097455 = 1646183) B1646183
theorem B1097563 : Blo 972592 1097563 := bstep (se 1 (by rfl) ⟨823172, by rfl⟩ : syracuseStep 1097563 = 1646345) B1646345
theorem B5554115 : Blo 972592 5554115 := bstep (se 1 (by rfl) ⟨4165586, by rfl⟩ : syracuseStep 5554115 = 8331173) B8331173
theorem B3293135 : Blo 972592 3293135 := bstep (se 1 (by rfl) ⟨2469851, by rfl⟩ : syracuseStep 3293135 = 4939703) B4939703
theorem B5259401 : Blo 972592 5259401 := bstep (se 2 (by rfl) ⟨1972275, by rfl⟩ : syracuseStep 5259401 = 3944551) B3944551
theorem B16629947 : Blo 972592 16629947 := bstep (se 1 (by rfl) ⟨12472460, by rfl⟩ : syracuseStep 16629947 = 24944921) B24944921
theorem B3293567 : Blo 972592 3293567 := bstep (se 1 (by rfl) ⟨2470175, by rfl⟩ : syracuseStep 3293567 = 4940351) B4940351
theorem B4932089 : Blo 972592 4932089 := bstep (se 2 (by rfl) ⟨1849533, by rfl⟩ : syracuseStep 4932089 = 3699067) B3699067
theorem B1459241 : Blo 972592 1459241 := bstep (se 2 (by rfl) ⟨547215, by rfl⟩ : syracuseStep 1459241 = 1094431) B1094431
theorem B4932737 : Blo 972592 4932737 := bstep (se 2 (by rfl) ⟨1849776, by rfl⟩ : syracuseStep 4932737 = 3699553) B3699553
theorem B13321837 : Blo 972592 13321837 := bstep (se 3 (by rfl) ⟨2497844, by rfl⟩ : syracuseStep 13321837 = 4995689) B4995689
theorem B18695933 : Blo 972592 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B1460711 : Blo 972592 1460711 := bstep (se 1 (by rfl) ⟨1095533, by rfl⟩ : syracuseStep 1460711 = 2191067) B2191067
theorem B1460891 : Blo 972592 1460891 := bstep (se 1 (by rfl) ⟨1095668, by rfl⟩ : syracuseStep 1460891 = 2191337) B2191337
theorem B1231519 : Blo 972592 1231519 := bstep (se 1 (by rfl) ⟨923639, by rfl⟩ : syracuseStep 1231519 = 1847279) B1847279
theorem B1460927 : Blo 972592 1460927 := bstep (se 1 (by rfl) ⟨1095695, by rfl⟩ : syracuseStep 1460927 = 2191391) B2191391
theorem B18762515 : Blo 972592 18762515 := bstep (se 1 (by rfl) ⟨14071886, by rfl⟩ : syracuseStep 18762515 = 28143773) B28143773
theorem B2771795 : Blo 972592 2771795 := bstep (se 1 (by rfl) ⟨2078846, by rfl⟩ : syracuseStep 2771795 = 4157693) B4157693
theorem B1461479 : Blo 972592 1461479 := bstep (se 1 (by rfl) ⟨1096109, by rfl⟩ : syracuseStep 1461479 = 2192219) B2192219
theorem B2968825 : Blo 972592 2968825 := bstep (se 2 (by rfl) ⟨1113309, by rfl⟩ : syracuseStep 2968825 = 2226619) B2226619
theorem B3952583 : Blo 972592 3952583 := bstep (se 1 (by rfl) ⟨2964437, by rfl⟩ : syracuseStep 3952583 = 5928875) B5928875
theorem B1560647 : Blo 972592 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B2773207 : Blo 972592 2773207 := bstep (se 1 (by rfl) ⟨2079905, by rfl⟩ : syracuseStep 2773207 = 4159811) B4159811
theorem B6246665 : Blo 972592 6246665 := bstep (se 2 (by rfl) ⟨2342499, by rfl⟩ : syracuseStep 6246665 = 4684999) B4684999
theorem B4444463 : Blo 972592 4444463 := bstep (se 1 (by rfl) ⟨3333347, by rfl⟩ : syracuseStep 4444463 = 6666695) B6666695
theorem B1462631 : Blo 972592 1462631 := bstep (se 1 (by rfl) ⟨1096973, by rfl⟩ : syracuseStep 1462631 = 2193947) B2193947
theorem B15029185 : Blo 972592 15029185 := bstep (se 2 (by rfl) ⟨5635944, by rfl⟩ : syracuseStep 15029185 = 11271889) B11271889
theorem B14046281 : Blo 972592 14046281 := bstep (se 2 (by rfl) ⟨5267355, by rfl⟩ : syracuseStep 14046281 = 10534711) B10534711
theorem B4936787 : Blo 972592 4936787 := bstep (se 1 (by rfl) ⟨3702590, by rfl⟩ : syracuseStep 4936787 = 7405181) B7405181
theorem B7394489 : Blo 972592 7394489 := bstep (se 2 (by rfl) ⟨2772933, by rfl⟩ : syracuseStep 7394489 = 5545867) B5545867
theorem B1463915 : Blo 972592 1463915 := bstep (se 1 (by rfl) ⟨1097936, by rfl⟩ : syracuseStep 1463915 = 2195873) B2195873
theorem B3954575 : Blo 972592 3954575 := bstep (se 1 (by rfl) ⟨2965931, by rfl⟩ : syracuseStep 3954575 = 5931863) B5931863
theorem B972711 : Blo 972592 972711 := bstep (se 1 (by rfl) ⟨729533, by rfl⟩ : syracuseStep 972711 = 1459067) B1459067
theorem B1234855 : Blo 972592 1234855 := bstep (se 1 (by rfl) ⟨926141, by rfl⟩ : syracuseStep 1234855 = 1852283) B1852283
theorem B1464287 : Blo 972592 1464287 := bstep (se 1 (by rfl) ⟨1098215, by rfl⟩ : syracuseStep 1464287 = 2196431) B2196431
theorem B972795 : Blo 972592 972795 := bstep (se 1 (by rfl) ⟨729596, by rfl⟩ : syracuseStep 972795 = 1459193) B1459193
theorem B1464347 : Blo 972592 1464347 := bstep (se 1 (by rfl) ⟨1098260, by rfl⟩ : syracuseStep 1464347 = 2196521) B2196521
theorem B972831 : Blo 972592 972831 := bstep (se 1 (by rfl) ⟨729623, by rfl⟩ : syracuseStep 972831 = 1459247) B1459247
theorem B972911 : Blo 972592 972911 := bstep (se 1 (by rfl) ⟨729683, by rfl⟩ : syracuseStep 972911 = 1459367) B1459367
theorem B2775167 : Blo 972592 2775167 := bstep (se 1 (by rfl) ⟨2081375, by rfl⟩ : syracuseStep 2775167 = 4162751) B4162751
theorem B973039 : Blo 972592 973039 := bstep (se 1 (by rfl) ⟨729779, by rfl⟩ : syracuseStep 973039 = 1459559) B1459559
theorem B1235407 : Blo 972592 1235407 := bstep (se 1 (by rfl) ⟨926555, by rfl⟩ : syracuseStep 1235407 = 1853111) B1853111
theorem B973467 : Blo 972592 973467 := bstep (se 1 (by rfl) ⟨730100, by rfl⟩ : syracuseStep 973467 = 1460201) B1460201
theorem B5003963 : Blo 972592 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B973563 : Blo 972592 973563 := bstep (se 1 (by rfl) ⟨730172, by rfl⟩ : syracuseStep 973563 = 1460345) B1460345
theorem B973695 : Blo 972592 973695 := bstep (se 1 (by rfl) ⟨730271, by rfl⟩ : syracuseStep 973695 = 1460543) B1460543
theorem B973791 : Blo 972592 973791 := bstep (se 1 (by rfl) ⟨730343, by rfl⟩ : syracuseStep 973791 = 1460687) B1460687
theorem B973819 : Blo 972592 973819 := bstep (se 1 (by rfl) ⟨730364, by rfl⟩ : syracuseStep 973819 = 1460729) B1460729
theorem B973851 : Blo 972592 973851 := bstep (se 1 (by rfl) ⟨730388, by rfl⟩ : syracuseStep 973851 = 1460777) B1460777
theorem B974143 : Blo 972592 974143 := bstep (se 1 (by rfl) ⟨730607, by rfl⟩ : syracuseStep 974143 = 1461215) B1461215
theorem B8019353 : Blo 972592 8019353 := bstep (se 2 (by rfl) ⟨3007257, by rfl⟩ : syracuseStep 8019353 = 6014515) B6014515
theorem B974439 : Blo 972592 974439 := bstep (se 1 (by rfl) ⟨730829, by rfl⟩ : syracuseStep 974439 = 1461659) B1461659
theorem B974683 : Blo 972592 974683 := bstep (se 1 (by rfl) ⟨731012, by rfl⟩ : syracuseStep 974683 = 1462025) B1462025
theorem B974719 : Blo 972592 974719 := bstep (se 1 (by rfl) ⟨731039, by rfl⟩ : syracuseStep 974719 = 1462079) B1462079
theorem B1171327 : Blo 972592 1171327 := bstep (se 1 (by rfl) ⟨878495, by rfl⟩ : syracuseStep 1171327 = 1756991) B1756991
theorem B12640139 : Blo 972592 12640139 := bstep (se 1 (by rfl) ⟨9480104, by rfl⟩ : syracuseStep 12640139 = 18960209) B18960209
theorem B974879 : Blo 972592 974879 := bstep (se 1 (by rfl) ⟨731159, by rfl⟩ : syracuseStep 974879 = 1462319) B1462319
theorem B2220215 : Blo 972592 2220215 := bstep (se 1 (by rfl) ⟨1665161, by rfl⟩ : syracuseStep 2220215 = 3330323) B3330323
theorem B6676793 : Blo 972592 6676793 := bstep (se 2 (by rfl) ⟨2503797, by rfl⟩ : syracuseStep 6676793 = 5007595) B5007595
theorem B975175 : Blo 972592 975175 := bstep (se 1 (by rfl) ⟨731381, by rfl⟩ : syracuseStep 975175 = 1462763) B1462763
theorem B975259 : Blo 972592 975259 := bstep (se 1 (by rfl) ⟨731444, by rfl⟩ : syracuseStep 975259 = 1462889) B1462889
theorem B975263 : Blo 972592 975263 := bstep (se 1 (by rfl) ⟨731447, by rfl⟩ : syracuseStep 975263 = 1462895) B1462895
theorem B975343 : Blo 972592 975343 := bstep (se 1 (by rfl) ⟨731507, by rfl⟩ : syracuseStep 975343 = 1463015) B1463015
theorem B975451 : Blo 972592 975451 := bstep (se 1 (by rfl) ⟨731588, by rfl⟩ : syracuseStep 975451 = 1463177) B1463177
theorem B975679 : Blo 972592 975679 := bstep (se 1 (by rfl) ⟨731759, by rfl⟩ : syracuseStep 975679 = 1463519) B1463519
theorem B975707 : Blo 972592 975707 := bstep (se 1 (by rfl) ⟨731780, by rfl⟩ : syracuseStep 975707 = 1463561) B1463561
theorem B14050381 : Blo 972592 14050381 := bstep (se 3 (by rfl) ⟨2634446, by rfl⟩ : syracuseStep 14050381 = 5268893) B5268893
theorem B975999 : Blo 972592 975999 := bstep (se 1 (by rfl) ⟨731999, by rfl⟩ : syracuseStep 975999 = 1463999) B1463999
theorem B976027 : Blo 972592 976027 := bstep (se 1 (by rfl) ⟨732020, by rfl⟩ : syracuseStep 976027 = 1464041) B1464041
theorem B976031 : Blo 972592 976031 := bstep (se 1 (by rfl) ⟨732023, by rfl⟩ : syracuseStep 976031 = 1464047) B1464047
theorem B2188655 : Blo 972592 2188655 := bstep (se 1 (by rfl) ⟨1641491, by rfl⟩ : syracuseStep 2188655 = 3282983) B3282983
theorem B976367 : Blo 972592 976367 := bstep (se 1 (by rfl) ⟨732275, by rfl⟩ : syracuseStep 976367 = 1464551) B1464551
theorem B976487 : Blo 972592 976487 := bstep (se 1 (by rfl) ⟨732365, by rfl⟩ : syracuseStep 976487 = 1464731) B1464731
theorem B2188907 : Blo 972592 2188907 := bstep (se 1 (by rfl) ⟨1641680, by rfl⟩ : syracuseStep 2188907 = 3283361) B3283361
theorem B3696425 : Blo 972592 3696425 := bstep (se 2 (by rfl) ⟨1386159, by rfl⟩ : syracuseStep 3696425 = 2772319) B2772319
theorem B3696455 : Blo 972592 3696455 := bstep (se 1 (by rfl) ⟨2772341, by rfl⟩ : syracuseStep 3696455 = 5544683) B5544683
theorem B2189267 : Blo 972592 2189267 := bstep (se 1 (by rfl) ⟨1641950, by rfl⟩ : syracuseStep 2189267 = 3283901) B3283901
theorem B2189609 : Blo 972592 2189609 := bstep (se 2 (by rfl) ⟨821103, by rfl⟩ : syracuseStep 2189609 = 1642207) B1642207
theorem B2190185 : Blo 972592 2190185 := bstep (se 2 (by rfl) ⟨821319, by rfl⟩ : syracuseStep 2190185 = 1642639) B1642639
theorem B2780543 : Blo 972592 2780543 := bstep (se 1 (by rfl) ⟨2085407, by rfl⟩ : syracuseStep 2780543 = 4170815) B4170815
theorem B3698081 : Blo 972592 3698081 := bstep (se 2 (by rfl) ⟨1386780, by rfl⟩ : syracuseStep 3698081 = 2773561) B2773561
theorem B2780999 : Blo 972592 2780999 := bstep (se 1 (by rfl) ⟨2085749, by rfl⟩ : syracuseStep 2780999 = 4171499) B4171499
theorem B13725521 : Blo 972592 13725521 := bstep (se 2 (by rfl) ⟨5147070, by rfl⟩ : syracuseStep 13725521 = 10294141) B10294141
theorem B35549117 : Blo 972592 35549117 := bstep (se 3 (by rfl) ⟨6665459, by rfl⟩ : syracuseStep 35549117 = 13330919) B13330919
theorem B4157419 : Blo 972592 4157419 := bstep (se 1 (by rfl) ⟨3118064, by rfl⟩ : syracuseStep 4157419 = 6236129) B6236129
theorem B5926945 : Blo 972592 5926945 := bstep (se 2 (by rfl) ⟨2222604, by rfl⟩ : syracuseStep 5926945 = 4445209) B4445209
theorem B5010383 : Blo 972592 5010383 := bstep (se 1 (by rfl) ⟨3757787, by rfl⟩ : syracuseStep 5010383 = 7515575) B7515575
theorem B3765467 : Blo 972592 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B7402751 : Blo 972592 7402751 := bstep (se 1 (by rfl) ⟨5552063, by rfl⟩ : syracuseStep 7402751 = 11104127) B11104127
theorem B1406441 : Blo 972592 1406441 := bstep (se 2 (by rfl) ⟨527415, by rfl⟩ : syracuseStep 1406441 = 1054831) B1054831
theorem B65796245 : Blo 972592 65796245 := bstep (se 6 (by rfl) ⟨1542099, by rfl⟩ : syracuseStep 65796245 = 3084199) B3084199
theorem B2193659 : Blo 972592 2193659 := bstep (se 1 (by rfl) ⟨1645244, by rfl⟩ : syracuseStep 2193659 = 3290489) B3290489
theorem B2193911 : Blo 972592 2193911 := bstep (se 1 (by rfl) ⟨1645433, by rfl⟩ : syracuseStep 2193911 = 3290867) B3290867
theorem B13335187 : Blo 972592 13335187 := bstep (se 1 (by rfl) ⟨10001390, by rfl⟩ : syracuseStep 13335187 = 20002781) B20002781
theorem B3603311 : Blo 972592 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B10681247 : Blo 972592 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B2816957 : Blo 972592 2816957 := bstep (se 3 (by rfl) ⟨528179, by rfl⟩ : syracuseStep 2816957 = 1056359) B1056359
theorem B2194991 : Blo 972592 2194991 := bstep (se 1 (by rfl) ⟨1646243, by rfl⟩ : syracuseStep 2194991 = 3292487) B3292487
theorem B3506267 : Blo 972592 3506267 := bstep (se 1 (by rfl) ⟨2629700, by rfl⟩ : syracuseStep 3506267 = 5259401) B5259401
theorem B8323175 : Blo 972592 8323175 := bstep (se 1 (by rfl) ⟨6242381, by rfl⟩ : syracuseStep 8323175 = 12484763) B12484763
theorem B4161725 : Blo 972592 4161725 := bstep (se 3 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 4161725 = 1560647) B1560647
theorem B2195711 : Blo 972592 2195711 := bstep (se 1 (by rfl) ⟨1646783, by rfl⟩ : syracuseStep 2195711 = 3293567) B3293567
theorem B17762449 : Blo 972592 17762449 := bstep (se 2 (by rfl) ⟨6660918, by rfl⟩ : syracuseStep 17762449 = 13321837) B13321837
theorem B4164443 : Blo 972592 4164443 := bstep (se 1 (by rfl) ⟨3123332, by rfl⟩ : syracuseStep 4164443 = 6246665) B6246665
theorem B32050075 : Blo 972592 32050075 := bstep (se 1 (by rfl) ⟨24037556, by rfl⟩ : syracuseStep 32050075 = 48075113) B48075113
theorem B22482359 : Blo 972592 22482359 := bstep (se 1 (by rfl) ⟨16861769, by rfl⟩ : syracuseStep 22482359 = 33723539) B33723539
theorem B1642025 : Blo 972592 1642025 := bstep (se 2 (by rfl) ⟨615759, by rfl⟩ : syracuseStep 1642025 = 1231519) B1231519
theorem B5199203933 : Blo 972592 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B3116809 : Blo 972592 3116809 := bstep (se 2 (by rfl) ⟨1168803, by rfl⟩ : syracuseStep 3116809 = 2337607) B2337607
theorem B2462633 : Blo 972592 2462633 := bstep (se 2 (by rfl) ⟨923487, by rfl⟩ : syracuseStep 2462633 = 1846975) B1846975
theorem B5346235 : Blo 972592 5346235 := bstep (se 1 (by rfl) ⟨4009676, by rfl⟩ : syracuseStep 5346235 = 8019353) B8019353
theorem B8426759 : Blo 972592 8426759 := bstep (se 1 (by rfl) ⟨6320069, by rfl⟩ : syracuseStep 8426759 = 12640139) B12640139
theorem B5543225 : Blo 972592 5543225 := bstep (se 2 (by rfl) ⟨2078709, by rfl⟩ : syracuseStep 5543225 = 4157419) B4157419
theorem B7902593 : Blo 972592 7902593 := bstep (se 2 (by rfl) ⟨2963472, by rfl⟩ : syracuseStep 7902593 = 5926945) B5926945
theorem B2464283 : Blo 972592 2464283 := bstep (se 1 (by rfl) ⟨1848212, by rfl⟩ : syracuseStep 2464283 = 3696425) B3696425
theorem B9378335 : Blo 972592 9378335 := bstep (se 1 (by rfl) ⟨7033751, by rfl⟩ : syracuseStep 9378335 = 14067503) B14067503
theorem B2464303 : Blo 972592 2464303 := bstep (se 1 (by rfl) ⟨1848227, by rfl⟩ : syracuseStep 2464303 = 3696455) B3696455
theorem B2465387 : Blo 972592 2465387 := bstep (se 1 (by rfl) ⟨1849040, by rfl⟩ : syracuseStep 2465387 = 3698081) B3698081
theorem B1318537 : Blo 972592 1318537 := bstep (se 2 (by rfl) ⟨494451, by rfl⟩ : syracuseStep 1318537 = 988903) B988903
theorem B1646473 : Blo 972592 1646473 := bstep (se 2 (by rfl) ⟨617427, by rfl⟩ : syracuseStep 1646473 = 1234855) B1234855
theorem B9150347 : Blo 972592 9150347 := bstep (se 1 (by rfl) ⟨6862760, by rfl⟩ : syracuseStep 9150347 = 13725521) B13725521
theorem B6234029 : Blo 972592 6234029 := bstep (se 3 (by rfl) ⟨1168880, by rfl⟩ : syracuseStep 6234029 = 2337761) B2337761
theorem B23699411 : Blo 972592 23699411 := bstep (se 1 (by rfl) ⟨17774558, by rfl⟩ : syracuseStep 23699411 = 35549117) B35549117
theorem B2465761 : Blo 972592 2465761 := bstep (se 2 (by rfl) ⟨924660, by rfl⟩ : syracuseStep 2465761 = 1849321) B1849321
theorem B3285305 : Blo 972592 3285305 := bstep (se 2 (by rfl) ⟨1231989, by rfl⟩ : syracuseStep 3285305 = 2463979) B2463979
theorem B3285359 : Blo 972592 3285359 := bstep (se 1 (by rfl) ⟨2464019, by rfl⟩ : syracuseStep 3285359 = 4928039) B4928039
theorem B1647209 : Blo 972592 1647209 := bstep (se 2 (by rfl) ⟨617703, by rfl⟩ : syracuseStep 1647209 = 1235407) B1235407
theorem B4924151 : Blo 972592 4924151 := bstep (se 1 (by rfl) ⟨3693113, by rfl⟩ : syracuseStep 4924151 = 7386227) B7386227
theorem B3285791 : Blo 972592 3285791 := bstep (se 1 (by rfl) ⟨2464343, by rfl⟩ : syracuseStep 3285791 = 4928687) B4928687
theorem B7415387 : Blo 972592 7415387 := bstep (se 1 (by rfl) ⟨5561540, by rfl⟩ : syracuseStep 7415387 = 11123081) B11123081
theorem B2467705 : Blo 972592 2467705 := bstep (se 2 (by rfl) ⟨925389, by rfl⟩ : syracuseStep 2467705 = 1850779) B1850779
theorem B2402207 : Blo 972592 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B7120831 : Blo 972592 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B1877971 : Blo 972592 1877971 := bstep (se 1 (by rfl) ⟨1408478, by rfl⟩ : syracuseStep 1877971 = 2816957) B2816957
theorem B3287033 : Blo 972592 3287033 := bstep (se 2 (by rfl) ⟨1232637, by rfl⟩ : syracuseStep 3287033 = 2465275) B2465275
theorem B3287195 : Blo 972592 3287195 := bstep (se 1 (by rfl) ⟨2465396, by rfl⟩ : syracuseStep 3287195 = 4930793) B4930793
theorem B11086631 : Blo 972592 11086631 := bstep (se 1 (by rfl) ⟨8314973, by rfl⟩ : syracuseStep 11086631 = 16629947) B16629947
theorem B3288059 : Blo 972592 3288059 := bstep (se 1 (by rfl) ⟨2466044, by rfl⟩ : syracuseStep 3288059 = 4932089) B4932089
theorem B14068835 : Blo 972592 14068835 := bstep (se 1 (by rfl) ⟨10551626, by rfl⟩ : syracuseStep 14068835 = 21103253) B21103253
theorem B3288491 : Blo 972592 3288491 := bstep (se 1 (by rfl) ⟨2466368, by rfl⟩ : syracuseStep 3288491 = 4932737) B4932737
theorem B12463955 : Blo 972592 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B6664639 : Blo 972592 6664639 := bstep (se 1 (by rfl) ⟨4998479, by rfl⟩ : syracuseStep 6664639 = 9996959) B9996959
theorem B1847863 : Blo 972592 1847863 := bstep (se 1 (by rfl) ⟨1385897, by rfl⟩ : syracuseStep 1847863 = 2771795) B2771795
theorem B3519287 : Blo 972592 3519287 := bstep (se 1 (by rfl) ⟨2639465, by rfl⟩ : syracuseStep 3519287 = 5278931) B5278931
theorem B5551199 : Blo 972592 5551199 := bstep (se 1 (by rfl) ⟨4163399, by rfl⟩ : syracuseStep 5551199 = 8326799) B8326799
theorem B2635055 : Blo 972592 2635055 := bstep (se 1 (by rfl) ⟨1976291, by rfl⟩ : syracuseStep 2635055 = 3952583) B3952583
theorem B2962975 : Blo 972592 2962975 := bstep (se 1 (by rfl) ⟨2222231, by rfl⟩ : syracuseStep 2962975 = 4444463) B4444463
theorem B10041245 : Blo 972592 10041245 := bstep (se 3 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 10041245 = 3765467) B3765467
theorem B3291191 : Blo 972592 3291191 := bstep (se 1 (by rfl) ⟨2468393, by rfl⟩ : syracuseStep 3291191 = 4936787) B4936787
theorem B7387199 : Blo 972592 7387199 := bstep (se 1 (by rfl) ⟨5540399, by rfl⟩ : syracuseStep 7387199 = 11080799) B11080799
theorem B51296327 : Blo 972592 51296327 := bstep (se 1 (by rfl) ⟨38472245, by rfl⟩ : syracuseStep 51296327 = 76944491) B76944491
theorem B4929659 : Blo 972592 4929659 := bstep (se 1 (by rfl) ⟨3697244, by rfl⟩ : syracuseStep 4929659 = 7394489) B7394489
theorem B22460651 : Blo 972592 22460651 := bstep (se 1 (by rfl) ⟨16845488, by rfl⟩ : syracuseStep 22460651 = 33690977) B33690977
theorem B1096015 : Blo 972592 1096015 := bstep (se 1 (by rfl) ⟨822011, by rfl⟩ : syracuseStep 1096015 = 1644023) B1644023
theorem B3127855 : Blo 972592 3127855 := bstep (se 1 (by rfl) ⟨2345891, by rfl⟩ : syracuseStep 3127855 = 4691783) B4691783
theorem B2636383 : Blo 972592 2636383 := bstep (se 1 (by rfl) ⟨1977287, by rfl⟩ : syracuseStep 2636383 = 3954575) B3954575
theorem B3750509 : Blo 972592 3750509 := bstep (se 3 (by rfl) ⟨703220, by rfl⟩ : syracuseStep 3750509 = 1406441) B1406441
theorem B1850111 : Blo 972592 1850111 := bstep (se 1 (by rfl) ⟨1387583, by rfl⟩ : syracuseStep 1850111 = 2775167) B2775167
theorem B9354041 : Blo 972592 9354041 := bstep (se 2 (by rfl) ⟨3507765, by rfl⟩ : syracuseStep 9354041 = 7015531) B7015531
theorem B3292001 : Blo 972592 3292001 := bstep (se 2 (by rfl) ⟨1234500, by rfl⟩ : syracuseStep 3292001 = 2469001) B2469001
theorem B1096735 : Blo 972592 1096735 := bstep (se 1 (by rfl) ⟨822551, by rfl⟩ : syracuseStep 1096735 = 1645103) B1645103
theorem B12500345 : Blo 972592 12500345 := bstep (se 2 (by rfl) ⟨4687629, by rfl⟩ : syracuseStep 12500345 = 9375259) B9375259
theorem B7028653 : Blo 972592 7028653 := bstep (se 3 (by rfl) ⟨1317872, by rfl⟩ : syracuseStep 7028653 = 2635745) B2635745
theorem B1098175 : Blo 972592 1098175 := bstep (se 1 (by rfl) ⟨823631, by rfl⟩ : syracuseStep 1098175 = 1647263) B1647263
theorem B1459103 : Blo 972592 1459103 := bstep (se 1 (by rfl) ⟨1094327, by rfl⟩ : syracuseStep 1459103 = 2188655) B2188655
theorem B1459271 : Blo 972592 1459271 := bstep (se 1 (by rfl) ⟨1094453, by rfl⟩ : syracuseStep 1459271 = 2188907) B2188907
theorem B64079059 : Blo 972592 64079059 := bstep (se 1 (by rfl) ⟨48059294, by rfl⟩ : syracuseStep 64079059 = 96118589) B96118589
theorem B20038913 : Blo 972592 20038913 := bstep (se 2 (by rfl) ⟨7514592, by rfl⟩ : syracuseStep 20038913 = 15029185) B15029185
theorem B1459511 : Blo 972592 1459511 := bstep (se 1 (by rfl) ⟨1094633, by rfl⟩ : syracuseStep 1459511 = 2189267) B2189267
theorem B1459739 : Blo 972592 1459739 := bstep (se 1 (by rfl) ⟨1094804, by rfl⟩ : syracuseStep 1459739 = 2189609) B2189609
theorem B1460123 : Blo 972592 1460123 := bstep (se 1 (by rfl) ⟨1095092, by rfl⟩ : syracuseStep 1460123 = 2190185) B2190185
theorem B5556347 : Blo 972592 5556347 := bstep (se 1 (by rfl) ⟨4167260, by rfl⟩ : syracuseStep 5556347 = 8334521) B8334521
theorem B1853695 : Blo 972592 1853695 := bstep (se 1 (by rfl) ⟨1390271, by rfl⟩ : syracuseStep 1853695 = 2780543) B2780543
theorem B12503321 : Blo 972592 12503321 := bstep (se 2 (by rfl) ⟨4688745, by rfl⟩ : syracuseStep 12503321 = 9377491) B9377491
theorem B1853999 : Blo 972592 1853999 := bstep (se 1 (by rfl) ⟨1390499, by rfl⟩ : syracuseStep 1853999 = 2780999) B2780999
theorem B1125567127 : Blo 972592 1125567127 := bstep (se 1 (by rfl) ⟨844175345, by rfl⟩ : syracuseStep 1125567127 = 1688350691) B1688350691
theorem B4935167 : Blo 972592 4935167 := bstep (se 1 (by rfl) ⟨3701375, by rfl⟩ : syracuseStep 4935167 = 7402751) B7402751
theorem B17780249 : Blo 972592 17780249 := bstep (se 2 (by rfl) ⟨6667593, by rfl⟩ : syracuseStep 17780249 = 13335187) B13335187
theorem B1461881 : Blo 972592 1461881 := bstep (se 2 (by rfl) ⟨548205, by rfl⟩ : syracuseStep 1461881 = 1096411) B1096411
theorem B8900603 : Blo 972592 8900603 := bstep (se 1 (by rfl) ⟨6675452, by rfl⟩ : syracuseStep 8900603 = 13350905) B13350905
theorem B43864163 : Blo 972592 43864163 := bstep (se 1 (by rfl) ⟨32898122, by rfl⟩ : syracuseStep 43864163 = 65796245) B65796245
theorem B1462439 : Blo 972592 1462439 := bstep (se 1 (by rfl) ⟨1096829, by rfl⟩ : syracuseStep 1462439 = 2193659) B2193659
theorem B1462607 : Blo 972592 1462607 := bstep (se 1 (by rfl) ⟨1096955, by rfl⟩ : syracuseStep 1462607 = 2193911) B2193911
theorem B1463273 : Blo 972592 1463273 := bstep (se 2 (by rfl) ⟨548727, by rfl⟩ : syracuseStep 1463273 = 1097455) B1097455
theorem B1463327 : Blo 972592 1463327 := bstep (se 1 (by rfl) ⟨1097495, by rfl⟩ : syracuseStep 1463327 = 2194991) B2194991
theorem B22467655 : Blo 972592 22467655 := bstep (se 1 (by rfl) ⟨16850741, by rfl⟩ : syracuseStep 22467655 = 33701483) B33701483
theorem B1463417 : Blo 972592 1463417 := bstep (se 2 (by rfl) ⟨548781, by rfl⟩ : syracuseStep 1463417 = 1097563) B1097563
theorem B1561769 : Blo 972592 1561769 := bstep (se 2 (by rfl) ⟨585663, by rfl⟩ : syracuseStep 1561769 = 1171327) B1171327
theorem B1464191 : Blo 972592 1464191 := bstep (se 1 (by rfl) ⟨1098143, by rfl⟩ : syracuseStep 1464191 = 2196287) B2196287
theorem B972827 : Blo 972592 972827 := bstep (se 1 (by rfl) ⟨729620, by rfl⟩ : syracuseStep 972827 = 1459241) B1459241
theorem B4937759 : Blo 972592 4937759 := bstep (se 1 (by rfl) ⟨3703319, by rfl⟩ : syracuseStep 4937759 = 7406639) B7406639
theorem B2284193 : Blo 972592 2284193 := bstep (se 2 (by rfl) ⟨856572, by rfl⟩ : syracuseStep 2284193 = 1713145) B1713145
theorem B18733841 : Blo 972592 18733841 := bstep (se 2 (by rfl) ⟨7025190, by rfl⟩ : syracuseStep 18733841 = 14050381) B14050381
theorem B973807 : Blo 972592 973807 := bstep (se 1 (by rfl) ⟨730355, by rfl⟩ : syracuseStep 973807 = 1460711) B1460711
theorem B973927 : Blo 972592 973927 := bstep (se 1 (by rfl) ⟨730445, by rfl⟩ : syracuseStep 973927 = 1460891) B1460891
theorem B973951 : Blo 972592 973951 := bstep (se 1 (by rfl) ⟨730463, by rfl⟩ : syracuseStep 973951 = 1460927) B1460927
theorem B12508343 : Blo 972592 12508343 := bstep (se 1 (by rfl) ⟨9381257, by rfl⟩ : syracuseStep 12508343 = 18762515) B18762515
theorem B23682293 : Blo 972592 23682293 := bstep (se 5 (by rfl) ⟨1110107, by rfl⟩ : syracuseStep 23682293 = 2220215) B2220215
theorem B974319 : Blo 972592 974319 := bstep (se 1 (by rfl) ⟨730739, by rfl⟩ : syracuseStep 974319 = 1461479) B1461479
theorem B13361021 : Blo 972592 13361021 := bstep (se 3 (by rfl) ⟨2505191, by rfl⟩ : syracuseStep 13361021 = 5010383) B5010383
theorem B975087 : Blo 972592 975087 := bstep (se 1 (by rfl) ⟨731315, by rfl⟩ : syracuseStep 975087 = 1462631) B1462631
theorem B2777399 : Blo 972592 2777399 := bstep (se 1 (by rfl) ⟨2083049, by rfl⟩ : syracuseStep 2777399 = 4166099) B4166099
theorem B9364187 : Blo 972592 9364187 := bstep (se 1 (by rfl) ⟨7023140, by rfl⟩ : syracuseStep 9364187 = 14046281) B14046281
theorem B4678559 : Blo 972592 4678559 := bstep (se 1 (by rfl) ⟨3508919, by rfl⟩ : syracuseStep 4678559 = 7017839) B7017839
theorem B975943 : Blo 972592 975943 := bstep (se 1 (by rfl) ⟨731957, by rfl⟩ : syracuseStep 975943 = 1463915) B1463915
theorem B4744423 : Blo 972592 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B976191 : Blo 972592 976191 := bstep (se 1 (by rfl) ⟨732143, by rfl⟩ : syracuseStep 976191 = 1464287) B1464287
theorem B976231 : Blo 972592 976231 := bstep (se 1 (by rfl) ⟨732173, by rfl⟩ : syracuseStep 976231 = 1464347) B1464347
theorem B2188727 : Blo 972592 2188727 := bstep (se 1 (by rfl) ⟨1641545, by rfl⟩ : syracuseStep 2188727 = 3283091) B3283091
theorem B3958433 : Blo 972592 3958433 := bstep (se 2 (by rfl) ⟨1484412, by rfl⟩ : syracuseStep 3958433 = 2968825) B2968825
theorem B3335975 : Blo 972592 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B2189537 : Blo 972592 2189537 := bstep (se 2 (by rfl) ⟨821076, by rfl⟩ : syracuseStep 2189537 = 1642153) B1642153
theorem B2189807 : Blo 972592 2189807 := bstep (se 1 (by rfl) ⟨1642355, by rfl⟩ : syracuseStep 2189807 = 3284711) B3284711
theorem B4942619 : Blo 972592 4942619 := bstep (se 1 (by rfl) ⟨3706964, by rfl⟩ : syracuseStep 4942619 = 7413929) B7413929
theorem B4451195 : Blo 972592 4451195 := bstep (se 1 (by rfl) ⟨3338396, by rfl⟩ : syracuseStep 4451195 = 6676793) B6676793
theorem B3697609 : Blo 972592 3697609 := bstep (se 2 (by rfl) ⟨1386603, by rfl⟩ : syracuseStep 3697609 = 2773207) B2773207
theorem B4943753 : Blo 972592 4943753 := bstep (se 2 (by rfl) ⟨1853907, by rfl⟩ : syracuseStep 4943753 = 3707815) B3707815
theorem B2192363 : Blo 972592 2192363 := bstep (se 1 (by rfl) ⟨1644272, by rfl⟩ : syracuseStep 2192363 = 3288545) B3288545
theorem B2192975 : Blo 972592 2192975 := bstep (se 1 (by rfl) ⟨1644731, by rfl⟩ : syracuseStep 2192975 = 3289463) B3289463
theorem B2193695 : Blo 972592 2193695 := bstep (se 1 (by rfl) ⟨1645271, by rfl⟩ : syracuseStep 2193695 = 3290543) B3290543
theorem B2193767 : Blo 972592 2193767 := bstep (se 1 (by rfl) ⟨1645325, by rfl⟩ : syracuseStep 2193767 = 3290651) B3290651
theorem B2194415 : Blo 972592 2194415 := bstep (se 1 (by rfl) ⟨1645811, by rfl⟩ : syracuseStep 2194415 = 3291623) B3291623
theorem B3702743 : Blo 972592 3702743 := bstep (se 1 (by rfl) ⟨2777057, by rfl⟩ : syracuseStep 3702743 = 5554115) B5554115
theorem B2195423 : Blo 972592 2195423 := bstep (se 1 (by rfl) ⟨1646567, by rfl⟩ : syracuseStep 2195423 = 3293135) B3293135
theorem B3704231 : Blo 972592 3704231 := bstep (se 1 (by rfl) ⟨2778173, by rfl⟩ : syracuseStep 3704231 = 5556347) B5556347
theorem B6325897 : Blo 972592 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B24971165 : Blo 972592 24971165 := bstep (se 3 (by rfl) ⟨4682093, by rfl⟩ : syracuseStep 24971165 = 9364187) B9364187
theorem B3466135955 : Blo 972592 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B5933735 : Blo 972592 5933735 := bstep (se 1 (by rfl) ⟨4450301, by rfl⟩ : syracuseStep 5933735 = 8900603) B8900603
theorem B1641755 : Blo 972592 1641755 := bstep (se 1 (by rfl) ⟨1231316, by rfl⟩ : syracuseStep 1641755 = 2462633) B2462633
theorem B42733433 : Blo 972592 42733433 := bstep (se 2 (by rfl) ⟨16025037, by rfl⟩ : syracuseStep 42733433 = 32050075) B32050075
theorem B1642855 : Blo 972592 1642855 := bstep (se 1 (by rfl) ⟨1232141, by rfl⟩ : syracuseStep 1642855 = 2464283) B2464283
theorem B12489227 : Blo 972592 12489227 := bstep (se 1 (by rfl) ⟨9366920, by rfl⟩ : syracuseStep 12489227 = 18733841) B18733841
theorem B1643591 : Blo 972592 1643591 := bstep (se 1 (by rfl) ⟨1232693, by rfl⟩ : syracuseStep 1643591 = 2465387) B2465387
theorem B15799607 : Blo 972592 15799607 := bstep (se 1 (by rfl) ⟨11849705, by rfl⟩ : syracuseStep 15799607 = 23699411) B23699411
theorem B3282767 : Blo 972592 3282767 := bstep (se 1 (by rfl) ⟨2462075, by rfl⟩ : syracuseStep 3282767 = 4924151) B4924151
theorem B8886185 : Blo 972592 8886185 := bstep (se 2 (by rfl) ⟨3332319, by rfl⟩ : syracuseStep 8886185 = 6664639) B6664639
theorem B3119039 : Blo 972592 3119039 := bstep (se 1 (by rfl) ⟨2339279, by rfl⟩ : syracuseStep 3119039 = 4678559) B4678559
theorem B2463817 : Blo 972592 2463817 := bstep (se 2 (by rfl) ⟨923931, by rfl⟩ : syracuseStep 2463817 = 1847863) B1847863
theorem B29956873 : Blo 972592 29956873 := bstep (se 2 (by rfl) ⟨11233827, by rfl⟩ : syracuseStep 29956873 = 22467655) B22467655
theorem B10001357 : Blo 972592 10001357 := bstep (se 3 (by rfl) ⟨1875254, by rfl⟩ : syracuseStep 10001357 = 3750509) B3750509
theorem B9379223 : Blo 972592 9379223 := bstep (se 1 (by rfl) ⟨7034417, by rfl⟩ : syracuseStep 9379223 = 14068835) B14068835
theorem B3285737 : Blo 972592 3285737 := bstep (se 2 (by rfl) ⟨1232151, by rfl⟩ : syracuseStep 3285737 = 2464303) B2464303
theorem B4170473 : Blo 972592 4170473 := bstep (se 2 (by rfl) ⟨1563927, by rfl⟩ : syracuseStep 4170473 = 3127855) B3127855
theorem B3515177 : Blo 972592 3515177 := bstep (se 2 (by rfl) ⟨1318191, by rfl⟩ : syracuseStep 3515177 = 2636383) B2636383
theorem B6694163 : Blo 972592 6694163 := bstep (se 1 (by rfl) ⟨5020622, by rfl⟩ : syracuseStep 6694163 = 10041245) B10041245
theorem B4924799 : Blo 972592 4924799 := bstep (se 1 (by rfl) ⟨3693599, by rfl⟩ : syracuseStep 4924799 = 7387199) B7387199
theorem B3286439 : Blo 972592 3286439 := bstep (se 1 (by rfl) ⟨2464829, by rfl⟩ : syracuseStep 3286439 = 4929659) B4929659
theorem B6236027 : Blo 972592 6236027 := bstep (se 1 (by rfl) ⟨4677020, by rfl⟩ : syracuseStep 6236027 = 9354041) B9354041
theorem B8333563 : Blo 972592 8333563 := bstep (se 1 (by rfl) ⟨6250172, by rfl⟩ : syracuseStep 8333563 = 12500345) B12500345
theorem B3287681 : Blo 972592 3287681 := bstep (se 2 (by rfl) ⟨1232880, by rfl⟩ : syracuseStep 3287681 = 2465761) B2465761
theorem B2468495 : Blo 972592 2468495 := bstep (se 1 (by rfl) ⟨1851371, by rfl⟩ : syracuseStep 2468495 = 3702743) B3702743
theorem B2337511 : Blo 972592 2337511 := bstep (se 1 (by rfl) ⟨1753133, by rfl⟩ : syracuseStep 2337511 = 3506267) B3506267
theorem B5548783 : Blo 972592 5548783 := bstep (se 1 (by rfl) ⟨4161587, by rfl⟩ : syracuseStep 5548783 = 8323175) B8323175
theorem B8335547 : Blo 972592 8335547 := bstep (se 1 (by rfl) ⟨6251660, by rfl⟩ : syracuseStep 8335547 = 12503321) B12503321
theorem B85438745 : Blo 972592 85438745 := bstep (se 2 (by rfl) ⟨32039529, by rfl⟩ : syracuseStep 85438745 = 64079059) B64079059
theorem B14988239 : Blo 972592 14988239 := bstep (se 1 (by rfl) ⟨11241179, by rfl⟩ : syracuseStep 14988239 = 22482359) B22482359
theorem B3290111 : Blo 972592 3290111 := bstep (se 1 (by rfl) ⟨2467583, by rfl⟩ : syracuseStep 3290111 = 4935167) B4935167
theorem B1094683 : Blo 972592 1094683 := bstep (se 1 (by rfl) ⟨821012, by rfl⟩ : syracuseStep 1094683 = 1642025) B1642025
theorem B3290273 : Blo 972592 3290273 := bstep (se 2 (by rfl) ⟨1233852, by rfl⟩ : syracuseStep 3290273 = 2467705) B2467705
theorem B2503961 : Blo 972592 2503961 := bstep (se 2 (by rfl) ⟨938985, by rfl⟩ : syracuseStep 2503961 = 1877971) B1877971
theorem B29242775 : Blo 972592 29242775 := bstep (se 1 (by rfl) ⟨21932081, by rfl⟩ : syracuseStep 29242775 = 43864163) B43864163
theorem B2471593 : Blo 972592 2471593 := bstep (se 2 (by rfl) ⟨926847, by rfl⟩ : syracuseStep 2471593 = 1853695) B1853695
theorem B1500756169 : Blo 972592 1500756169 := bstep (se 2 (by rfl) ⟨562783563, by rfl⟩ : syracuseStep 1500756169 = 1125567127) B1125567127
theorem B4930145 : Blo 972592 4930145 := bstep (se 2 (by rfl) ⟨1848804, by rfl⟩ : syracuseStep 4930145 = 3697609) B3697609
theorem B3291839 : Blo 972592 3291839 := bstep (se 1 (by rfl) ⟨2468879, by rfl⟩ : syracuseStep 3291839 = 4937759) B4937759
theorem B1522795 : Blo 972592 1522795 := bstep (se 1 (by rfl) ⟨1142096, by rfl⟩ : syracuseStep 1522795 = 2284193) B2284193
theorem B8338895 : Blo 972592 8338895 := bstep (se 1 (by rfl) ⟨6254171, by rfl⟩ : syracuseStep 8338895 = 12508343) B12508343
theorem B1851599 : Blo 972592 1851599 := bstep (se 1 (by rfl) ⟨1388699, by rfl⟩ : syracuseStep 1851599 = 2777399) B2777399
theorem B1098139 : Blo 972592 1098139 := bstep (se 1 (by rfl) ⟨823604, by rfl⟩ : syracuseStep 1098139 = 1647209) B1647209
theorem B1459151 : Blo 972592 1459151 := bstep (se 1 (by rfl) ⟨1094363, by rfl⟩ : syracuseStep 1459151 = 2188727) B2188727
theorem B2638955 : Blo 972592 2638955 := bstep (se 1 (by rfl) ⟨1979216, by rfl⟩ : syracuseStep 2638955 = 3958433) B3958433
theorem B7128313 : Blo 972592 7128313 := bstep (se 2 (by rfl) ⟨2673117, by rfl⟩ : syracuseStep 7128313 = 5346235) B5346235
theorem B1459691 : Blo 972592 1459691 := bstep (se 1 (by rfl) ⟨1094768, by rfl⟩ : syracuseStep 1459691 = 2189537) B2189537
theorem B1459871 : Blo 972592 1459871 := bstep (se 1 (by rfl) ⟨1094903, by rfl⟩ : syracuseStep 1459871 = 2189807) B2189807
theorem B3295079 : Blo 972592 3295079 := bstep (se 1 (by rfl) ⟨2471309, by rfl⟩ : syracuseStep 3295079 = 4942619) B4942619
theorem B7391087 : Blo 972592 7391087 := bstep (se 1 (by rfl) ⟨5543315, by rfl⟩ : syracuseStep 7391087 = 11086631) B11086631
theorem B2967463 : Blo 972592 2967463 := bstep (se 1 (by rfl) ⟨2225597, by rfl⟩ : syracuseStep 2967463 = 4451195) B4451195
theorem B3950633 : Blo 972592 3950633 := bstep (se 2 (by rfl) ⟨1481487, by rfl⟩ : syracuseStep 3950633 = 2962975) B2962975
theorem B8309303 : Blo 972592 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B3295835 : Blo 972592 3295835 := bstep (se 1 (by rfl) ⟨2471876, by rfl⟩ : syracuseStep 3295835 = 4943753) B4943753
theorem B1461353 : Blo 972592 1461353 := bstep (se 2 (by rfl) ⟨548007, by rfl⟩ : syracuseStep 1461353 = 1096015) B1096015
theorem B2346191 : Blo 972592 2346191 := bstep (se 1 (by rfl) ⟨1759643, by rfl⟩ : syracuseStep 2346191 = 3519287) B3519287
theorem B1461575 : Blo 972592 1461575 := bstep (se 1 (by rfl) ⟨1096181, by rfl⟩ : syracuseStep 1461575 = 2192363) B2192363
theorem B7032197 : Blo 972592 7032197 := bstep (se 4 (by rfl) ⟨659268, by rfl⟩ : syracuseStep 7032197 = 1318537) B1318537
theorem B1756703 : Blo 972592 1756703 := bstep (se 1 (by rfl) ⟨1317527, by rfl⟩ : syracuseStep 1756703 = 2635055) B2635055
theorem B1461983 : Blo 972592 1461983 := bstep (se 1 (by rfl) ⟨1096487, by rfl⟩ : syracuseStep 1461983 = 2192975) B2192975
theorem B1462313 : Blo 972592 1462313 := bstep (se 2 (by rfl) ⟨548367, by rfl⟩ : syracuseStep 1462313 = 1096735) B1096735
theorem B34197551 : Blo 972592 34197551 := bstep (se 1 (by rfl) ⟨25648163, by rfl⟩ : syracuseStep 34197551 = 51296327) B51296327
theorem B1462463 : Blo 972592 1462463 := bstep (se 1 (by rfl) ⟨1096847, by rfl⟩ : syracuseStep 1462463 = 2193695) B2193695
theorem B1462511 : Blo 972592 1462511 := bstep (se 1 (by rfl) ⟨1096883, by rfl⟩ : syracuseStep 1462511 = 2193767) B2193767
theorem B1233407 : Blo 972592 1233407 := bstep (se 1 (by rfl) ⟨925055, by rfl⟩ : syracuseStep 1233407 = 1850111) B1850111
theorem B1462943 : Blo 972592 1462943 := bstep (se 1 (by rfl) ⟨1097207, by rfl⟩ : syracuseStep 1462943 = 2194415) B2194415
theorem B24400925 : Blo 972592 24400925 := bstep (se 3 (by rfl) ⟨4575173, by rfl⟩ : syracuseStep 24400925 = 9150347) B9150347
theorem B1463615 : Blo 972592 1463615 := bstep (se 1 (by rfl) ⟨1097711, by rfl⟩ : syracuseStep 1463615 = 2195423) B2195423
theorem B2774483 : Blo 972592 2774483 := bstep (se 1 (by rfl) ⟨2080862, by rfl⟩ : syracuseStep 2774483 = 4161725) B4161725
theorem B1463807 : Blo 972592 1463807 := bstep (se 1 (by rfl) ⟨1097855, by rfl⟩ : syracuseStep 1463807 = 2195711) B2195711
theorem B1464233 : Blo 972592 1464233 := bstep (se 2 (by rfl) ⟨549087, by rfl⟩ : syracuseStep 1464233 = 1098175) B1098175
theorem B972735 : Blo 972592 972735 := bstep (se 1 (by rfl) ⟨729551, by rfl⟩ : syracuseStep 972735 = 1459103) B1459103
theorem B972847 : Blo 972592 972847 := bstep (se 1 (by rfl) ⟨729635, by rfl⟩ : syracuseStep 972847 = 1459271) B1459271
theorem B13359275 : Blo 972592 13359275 := bstep (se 1 (by rfl) ⟨10019456, by rfl⟩ : syracuseStep 13359275 = 20038913) B20038913
theorem B973007 : Blo 972592 973007 := bstep (se 1 (by rfl) ⟨729755, by rfl⟩ : syracuseStep 973007 = 1459511) B1459511
theorem B973159 : Blo 972592 973159 := bstep (se 1 (by rfl) ⟨729869, by rfl⟩ : syracuseStep 973159 = 1459739) B1459739
theorem B973415 : Blo 972592 973415 := bstep (se 1 (by rfl) ⟨730061, by rfl⟩ : syracuseStep 973415 = 1460123) B1460123
theorem B1235999 : Blo 972592 1235999 := bstep (se 1 (by rfl) ⟨926999, by rfl⟩ : syracuseStep 1235999 = 1853999) B1853999
theorem B2776295 : Blo 972592 2776295 := bstep (se 1 (by rfl) ⟨2082221, by rfl⟩ : syracuseStep 2776295 = 4164443) B4164443
theorem B11853499 : Blo 972592 11853499 := bstep (se 1 (by rfl) ⟨8890124, by rfl⟩ : syracuseStep 11853499 = 17780249) B17780249
theorem B974587 : Blo 972592 974587 := bstep (se 1 (by rfl) ⟨730940, by rfl⟩ : syracuseStep 974587 = 1461881) B1461881
theorem B9494441 : Blo 972592 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B974959 : Blo 972592 974959 := bstep (se 1 (by rfl) ⟨731219, by rfl⟩ : syracuseStep 974959 = 1462439) B1462439
theorem B23683265 : Blo 972592 23683265 := bstep (se 2 (by rfl) ⟨8881224, by rfl⟩ : syracuseStep 23683265 = 17762449) B17762449
theorem B975071 : Blo 972592 975071 := bstep (se 1 (by rfl) ⟨731303, by rfl⟩ : syracuseStep 975071 = 1462607) B1462607
theorem B975515 : Blo 972592 975515 := bstep (se 1 (by rfl) ⟨731636, by rfl⟩ : syracuseStep 975515 = 1463273) B1463273
theorem B22471357 : Blo 972592 22471357 := bstep (se 3 (by rfl) ⟨4213379, by rfl⟩ : syracuseStep 22471357 = 8426759) B8426759
theorem B975551 : Blo 972592 975551 := bstep (se 1 (by rfl) ⟨731663, by rfl⟩ : syracuseStep 975551 = 1463327) B1463327
theorem B975611 : Blo 972592 975611 := bstep (se 1 (by rfl) ⟨731708, by rfl⟩ : syracuseStep 975611 = 1463417) B1463417
theorem B1041179 : Blo 972592 1041179 := bstep (se 1 (by rfl) ⟨780884, by rfl⟩ : syracuseStep 1041179 = 1561769) B1561769
theorem B3695483 : Blo 972592 3695483 := bstep (se 1 (by rfl) ⟨2771612, by rfl⟩ : syracuseStep 3695483 = 5543225) B5543225
theorem B5268395 : Blo 972592 5268395 := bstep (se 1 (by rfl) ⟨3951296, by rfl⟩ : syracuseStep 5268395 = 7902593) B7902593
theorem B976127 : Blo 972592 976127 := bstep (se 1 (by rfl) ⟨732095, by rfl⟩ : syracuseStep 976127 = 1464191) B1464191
theorem B6252223 : Blo 972592 6252223 := bstep (se 1 (by rfl) ⟨4689167, by rfl⟩ : syracuseStep 6252223 = 9378335) B9378335
theorem B15788195 : Blo 972592 15788195 := bstep (se 1 (by rfl) ⟨11841146, by rfl⟩ : syracuseStep 15788195 = 23682293) B23682293
theorem B4155745 : Blo 972592 4155745 := bstep (se 2 (by rfl) ⟨1558404, by rfl⟩ : syracuseStep 4155745 = 3116809) B3116809
theorem B8907347 : Blo 972592 8907347 := bstep (se 1 (by rfl) ⟨6680510, by rfl⟩ : syracuseStep 8907347 = 13361021) B13361021
theorem B4156019 : Blo 972592 4156019 := bstep (se 1 (by rfl) ⟨3117014, by rfl⟩ : syracuseStep 4156019 = 6234029) B6234029
theorem B2190203 : Blo 972592 2190203 := bstep (se 1 (by rfl) ⟨1642652, by rfl⟩ : syracuseStep 2190203 = 3285305) B3285305
theorem B2190239 : Blo 972592 2190239 := bstep (se 1 (by rfl) ⟨1642679, by rfl⟩ : syracuseStep 2190239 = 3285359) B3285359
theorem B2190527 : Blo 972592 2190527 := bstep (se 1 (by rfl) ⟨1642895, by rfl⟩ : syracuseStep 2190527 = 3285791) B3285791
theorem B4943591 : Blo 972592 4943591 := bstep (se 1 (by rfl) ⟨3707693, by rfl⟩ : syracuseStep 4943591 = 7415387) B7415387
theorem B2223983 : Blo 972592 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B1601471 : Blo 972592 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B2191355 : Blo 972592 2191355 := bstep (se 1 (by rfl) ⟨1643516, by rfl⟩ : syracuseStep 2191355 = 3287033) B3287033
theorem B2191463 : Blo 972592 2191463 := bstep (se 1 (by rfl) ⟨1643597, by rfl⟩ : syracuseStep 2191463 = 3287195) B3287195
theorem B2192039 : Blo 972592 2192039 := bstep (se 1 (by rfl) ⟨1644029, by rfl⟩ : syracuseStep 2192039 = 3288059) B3288059
theorem B2192327 : Blo 972592 2192327 := bstep (se 1 (by rfl) ⟨1644245, by rfl⟩ : syracuseStep 2192327 = 3288491) B3288491
theorem B3700799 : Blo 972592 3700799 := bstep (se 1 (by rfl) ⟨2775599, by rfl⟩ : syracuseStep 3700799 = 5551199) B5551199
theorem B2194127 : Blo 972592 2194127 := bstep (se 1 (by rfl) ⟨1645595, by rfl⟩ : syracuseStep 2194127 = 3291191) B3291191
theorem B14973767 : Blo 972592 14973767 := bstep (se 1 (by rfl) ⟨11230325, by rfl⟩ : syracuseStep 14973767 = 22460651) B22460651
theorem B2194667 : Blo 972592 2194667 := bstep (se 1 (by rfl) ⟨1646000, by rfl⟩ : syracuseStep 2194667 = 3292001) B3292001
theorem B2195297 : Blo 972592 2195297 := bstep (se 2 (by rfl) ⟨823236, by rfl⟩ : syracuseStep 2195297 = 1646473) B1646473
theorem B9371537 : Blo 972592 9371537 := bstep (se 2 (by rfl) ⟨3514326, by rfl⟩ : syracuseStep 9371537 = 7028653) B7028653
theorem B2196719 : Blo 972592 2196719 := bstep (se 1 (by rfl) ⟨1647539, by rfl⟩ : syracuseStep 2196719 = 3295079) B3295079
theorem B16647443 : Blo 972592 16647443 := bstep (se 1 (by rfl) ⟨12485582, by rfl⟩ : syracuseStep 16647443 = 24971165) B24971165
theorem B5539535 : Blo 972592 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B2197223 : Blo 972592 2197223 := bstep (se 1 (by rfl) ⟨1647917, by rfl⟩ : syracuseStep 2197223 = 3295835) B3295835
theorem B4688131 : Blo 972592 4688131 := bstep (se 1 (by rfl) ⟨3516098, by rfl⟩ : syracuseStep 4688131 = 7032197) B7032197
theorem B11111417 : Blo 972592 11111417 := bstep (se 2 (by rfl) ⟨4166781, by rfl⟩ : syracuseStep 11111417 = 8333563) B8333563
theorem B8326151 : Blo 972592 8326151 := bstep (se 1 (by rfl) ⟨6244613, by rfl⟩ : syracuseStep 8326151 = 12489227) B12489227
theorem B5540993 : Blo 972592 5540993 := bstep (se 2 (by rfl) ⟨2077872, by rfl⟩ : syracuseStep 5540993 = 4155745) B4155745
theorem B3116681 : Blo 972592 3116681 := bstep (se 2 (by rfl) ⟨1168755, by rfl⟩ : syracuseStep 3116681 = 2337511) B2337511
theorem B6329627 : Blo 972592 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B2463655 : Blo 972592 2463655 := bstep (se 1 (by rfl) ⟨1847741, by rfl⟩ : syracuseStep 2463655 = 3695483) B3695483
theorem B3512263 : Blo 972592 3512263 := bstep (se 1 (by rfl) ⟨2634197, by rfl⟩ : syracuseStep 3512263 = 5268395) B5268395
theorem B4462775 : Blo 972592 4462775 := bstep (se 1 (by rfl) ⟨3347081, by rfl⟩ : syracuseStep 4462775 = 6694163) B6694163
theorem B3283199 : Blo 972592 3283199 := bstep (se 1 (by rfl) ⟨2462399, by rfl⟩ : syracuseStep 3283199 = 4924799) B4924799
theorem B38017669 : Blo 972592 38017669 := bstep (se 4 (by rfl) ⟨3564156, by rfl⟩ : syracuseStep 38017669 = 7128313) B7128313
theorem B10525463 : Blo 972592 10525463 := bstep (se 1 (by rfl) ⟨7894097, by rfl⟩ : syracuseStep 10525463 = 15788195) B15788195
theorem B1645663 : Blo 972592 1645663 := bstep (se 1 (by rfl) ⟨1234247, by rfl⟩ : syracuseStep 1645663 = 2468495) B2468495
theorem B3285089 : Blo 972592 3285089 := bstep (se 2 (by rfl) ⟨1231908, by rfl⟩ : syracuseStep 3285089 = 2463817) B2463817
theorem B56959163 : Blo 972592 56959163 := bstep (se 1 (by rfl) ⟨42719372, by rfl⟩ : syracuseStep 56959163 = 85438745) B85438745
theorem B2467199 : Blo 972592 2467199 := bstep (se 1 (by rfl) ⟨1850399, by rfl⟩ : syracuseStep 2467199 = 3700799) B3700799
theorem B3286763 : Blo 972592 3286763 := bstep (se 1 (by rfl) ⟨2465072, by rfl⟩ : syracuseStep 3286763 = 4930145) B4930145
theorem B15804665 : Blo 972592 15804665 := bstep (se 2 (by rfl) ⟨5926749, by rfl⟩ : syracuseStep 15804665 = 11853499) B11853499
theorem B4270589 : Blo 972592 4270589 := bstep (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) B1601471
theorem B29961809 : Blo 972592 29961809 := bstep (se 2 (by rfl) ⟨11235678, by rfl⟩ : syracuseStep 29961809 = 22471357) B22471357
theorem B2469487 : Blo 972592 2469487 := bstep (se 1 (by rfl) ⟨1852115, by rfl⟩ : syracuseStep 2469487 = 3704231) B3704231
theorem B4927391 : Blo 972592 4927391 := bstep (se 1 (by rfl) ⟨3695543, by rfl⟩ : syracuseStep 4927391 = 7391087) B7391087
theorem B3289085 : Blo 972592 3289085 := bstep (se 3 (by rfl) ⟨616703, by rfl⟩ : syracuseStep 3289085 = 1233407) B1233407
theorem B8434529 : Blo 972592 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B1094503 : Blo 972592 1094503 := bstep (se 1 (by rfl) ⟨820877, by rfl⟩ : syracuseStep 1094503 = 1641755) B1641755
theorem B8336297 : Blo 972592 8336297 := bstep (se 2 (by rfl) ⟨3126111, by rfl⟩ : syracuseStep 8336297 = 6252223) B6252223
theorem B28488955 : Blo 972592 28488955 := bstep (se 1 (by rfl) ⟨21366716, by rfl⟩ : syracuseStep 28488955 = 42733433) B42733433
theorem B16267283 : Blo 972592 16267283 := bstep (se 1 (by rfl) ⟨12200462, by rfl⟩ : syracuseStep 16267283 = 24400925) B24400925
theorem B1095727 : Blo 972592 1095727 := bstep (se 1 (by rfl) ⟨821795, by rfl⟩ : syracuseStep 1095727 = 1643591) B1643591
theorem B10533071 : Blo 972592 10533071 := bstep (se 1 (by rfl) ⟨7899803, by rfl⟩ : syracuseStep 10533071 = 15799607) B15799607
theorem B1849655 : Blo 972592 1849655 := bstep (se 1 (by rfl) ⟨1387241, by rfl⟩ : syracuseStep 1849655 = 2774483) B2774483
theorem B2079359 : Blo 972592 2079359 := bstep (se 1 (by rfl) ⟨1559519, by rfl⟩ : syracuseStep 2079359 = 3119039) B3119039
theorem B6667571 : Blo 972592 6667571 := bstep (se 1 (by rfl) ⟨5000678, by rfl⟩ : syracuseStep 6667571 = 10001357) B10001357
theorem B1850863 : Blo 972592 1850863 := bstep (se 1 (by rfl) ⟨1388147, by rfl⟩ : syracuseStep 1850863 = 2776295) B2776295
theorem B10535021 : Blo 972592 10535021 := bstep (se 3 (by rfl) ⟨1975316, by rfl⟩ : syracuseStep 10535021 = 3950633) B3950633
theorem B2343451 : Blo 972592 2343451 := bstep (se 1 (by rfl) ⟨1757588, by rfl⟩ : syracuseStep 2343451 = 3515177) B3515177
theorem B1459577 : Blo 972592 1459577 := bstep (se 2 (by rfl) ⟨547341, by rfl⟩ : syracuseStep 1459577 = 1094683) B1094683
theorem B2770679 : Blo 972592 2770679 := bstep (se 1 (by rfl) ⟨2078009, by rfl⟩ : syracuseStep 2770679 = 4156019) B4156019
theorem B1460135 : Blo 972592 1460135 := bstep (se 1 (by rfl) ⟨1095101, by rfl⟩ : syracuseStep 1460135 = 2190203) B2190203
theorem B1460159 : Blo 972592 1460159 := bstep (se 1 (by rfl) ⟨1095119, by rfl⟩ : syracuseStep 1460159 = 2190239) B2190239
theorem B1460351 : Blo 972592 1460351 := bstep (se 1 (by rfl) ⟨1095263, by rfl⟩ : syracuseStep 1460351 = 2190527) B2190527
theorem B3295457 : Blo 972592 3295457 := bstep (se 2 (by rfl) ⟨1235796, by rfl⟩ : syracuseStep 3295457 = 2471593) B2471593
theorem B3295727 : Blo 972592 3295727 := bstep (se 1 (by rfl) ⟨2471795, by rfl⟩ : syracuseStep 3295727 = 4943591) B4943591
theorem B1460903 : Blo 972592 1460903 := bstep (se 1 (by rfl) ⟨1095677, by rfl⟩ : syracuseStep 1460903 = 2191355) B2191355
theorem B1460975 : Blo 972592 1460975 := bstep (se 1 (by rfl) ⟨1095731, by rfl⟩ : syracuseStep 1460975 = 2191463) B2191463
theorem B3295997 : Blo 972592 3295997 := bstep (se 3 (by rfl) ⟨617999, by rfl⟩ : syracuseStep 3295997 = 1235999) B1235999
theorem B5557031 : Blo 972592 5557031 := bstep (se 1 (by rfl) ⟨4167773, by rfl⟩ : syracuseStep 5557031 = 8335547) B8335547
theorem B1461359 : Blo 972592 1461359 := bstep (se 1 (by rfl) ⟨1096019, by rfl⟩ : syracuseStep 1461359 = 2192039) B2192039
theorem B1461551 : Blo 972592 1461551 := bstep (se 1 (by rfl) ⟨1096163, by rfl⟩ : syracuseStep 1461551 = 2192327) B2192327
theorem B1462751 : Blo 972592 1462751 := bstep (se 1 (by rfl) ⟨1097063, by rfl⟩ : syracuseStep 1462751 = 2194127) B2194127
theorem B9982511 : Blo 972592 9982511 := bstep (se 1 (by rfl) ⟨7486883, by rfl⟩ : syracuseStep 9982511 = 14973767) B14973767
theorem B1463111 : Blo 972592 1463111 := bstep (se 1 (by rfl) ⟨1097333, by rfl⟩ : syracuseStep 1463111 = 2194667) B2194667
theorem B5559263 : Blo 972592 5559263 := bstep (se 1 (by rfl) ⟨4169447, by rfl⟩ : syracuseStep 5559263 = 8338895) B8338895
theorem B1463531 : Blo 972592 1463531 := bstep (se 1 (by rfl) ⟨1097648, by rfl⟩ : syracuseStep 1463531 = 2195297) B2195297
theorem B6247691 : Blo 972592 6247691 := bstep (se 1 (by rfl) ⟨4685768, by rfl⟩ : syracuseStep 6247691 = 9371537) B9371537
theorem B1464185 : Blo 972592 1464185 := bstep (se 2 (by rfl) ⟨549069, by rfl⟩ : syracuseStep 1464185 = 1098139) B1098139
theorem B4937597 : Blo 972592 4937597 := bstep (se 3 (by rfl) ⟨925799, by rfl⟩ : syracuseStep 4937597 = 1851599) B1851599
theorem B972767 : Blo 972592 972767 := bstep (se 1 (by rfl) ⟨729575, by rfl⟩ : syracuseStep 972767 = 1459151) B1459151
theorem B1759303 : Blo 972592 1759303 := bstep (se 1 (by rfl) ⟨1319477, by rfl⟩ : syracuseStep 1759303 = 2638955) B2638955
theorem B973127 : Blo 972592 973127 := bstep (se 1 (by rfl) ⟨729845, by rfl⟩ : syracuseStep 973127 = 1459691) B1459691
theorem B973247 : Blo 972592 973247 := bstep (se 1 (by rfl) ⟨729935, by rfl⟩ : syracuseStep 973247 = 1459871) B1459871
theorem B2310757303 : Blo 972592 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B3955823 : Blo 972592 3955823 := bstep (se 1 (by rfl) ⟨2966867, by rfl⟩ : syracuseStep 3955823 = 5933735) B5933735
theorem B974235 : Blo 972592 974235 := bstep (se 1 (by rfl) ⟨730676, by rfl⟩ : syracuseStep 974235 = 1461353) B1461353
theorem B2776477 : Blo 972592 2776477 := bstep (se 3 (by rfl) ⟨520589, by rfl⟩ : syracuseStep 2776477 = 1041179) B1041179
theorem B1564127 : Blo 972592 1564127 := bstep (se 1 (by rfl) ⟨1173095, by rfl⟩ : syracuseStep 1564127 = 2346191) B2346191
theorem B974383 : Blo 972592 974383 := bstep (se 1 (by rfl) ⟨730787, by rfl⟩ : syracuseStep 974383 = 1461575) B1461575
theorem B1171135 : Blo 972592 1171135 := bstep (se 1 (by rfl) ⟨878351, by rfl⟩ : syracuseStep 1171135 = 1756703) B1756703
theorem B974655 : Blo 972592 974655 := bstep (se 1 (by rfl) ⟨730991, by rfl⟩ : syracuseStep 974655 = 1461983) B1461983
theorem B3956617 : Blo 972592 3956617 := bstep (se 2 (by rfl) ⟨1483731, by rfl⟩ : syracuseStep 3956617 = 2967463) B2967463
theorem B974875 : Blo 972592 974875 := bstep (se 1 (by rfl) ⟨731156, by rfl⟩ : syracuseStep 974875 = 1462313) B1462313
theorem B22798367 : Blo 972592 22798367 := bstep (se 1 (by rfl) ⟨17098775, by rfl⟩ : syracuseStep 22798367 = 34197551) B34197551
theorem B974975 : Blo 972592 974975 := bstep (se 1 (by rfl) ⟨731231, by rfl⟩ : syracuseStep 974975 = 1462463) B1462463
theorem B975007 : Blo 972592 975007 := bstep (se 1 (by rfl) ⟨731255, by rfl⟩ : syracuseStep 975007 = 1462511) B1462511
theorem B975295 : Blo 972592 975295 := bstep (se 1 (by rfl) ⟨731471, by rfl⟩ : syracuseStep 975295 = 1462943) B1462943
theorem B975743 : Blo 972592 975743 := bstep (se 1 (by rfl) ⟨731807, by rfl⟩ : syracuseStep 975743 = 1463615) B1463615
theorem B7398377 : Blo 972592 7398377 := bstep (se 2 (by rfl) ⟨2774391, by rfl⟩ : syracuseStep 7398377 = 5548783) B5548783
theorem B975871 : Blo 972592 975871 := bstep (se 1 (by rfl) ⟨731903, by rfl⟩ : syracuseStep 975871 = 1463807) B1463807
theorem B2188511 : Blo 972592 2188511 := bstep (se 1 (by rfl) ⟨1641383, by rfl⟩ : syracuseStep 2188511 = 3282767) B3282767
theorem B5924123 : Blo 972592 5924123 := bstep (se 1 (by rfl) ⟨4443092, by rfl⟩ : syracuseStep 5924123 = 8886185) B8886185
theorem B976155 : Blo 972592 976155 := bstep (se 1 (by rfl) ⟨732116, by rfl⟩ : syracuseStep 976155 = 1464233) B1464233
theorem B8906183 : Blo 972592 8906183 := bstep (se 1 (by rfl) ⟨6679637, by rfl⟩ : syracuseStep 8906183 = 13359275) B13359275
theorem B6252815 : Blo 972592 6252815 := bstep (se 1 (by rfl) ⟨4689611, by rfl⟩ : syracuseStep 6252815 = 9379223) B9379223
theorem B15788843 : Blo 972592 15788843 := bstep (se 1 (by rfl) ⟨11841632, by rfl⟩ : syracuseStep 15788843 = 23683265) B23683265
theorem B2190473 : Blo 972592 2190473 := bstep (se 2 (by rfl) ⟨821427, by rfl⟩ : syracuseStep 2190473 = 1642855) B1642855
theorem B2190491 : Blo 972592 2190491 := bstep (se 1 (by rfl) ⟨1642868, by rfl⟩ : syracuseStep 2190491 = 3285737) B3285737
theorem B2780315 : Blo 972592 2780315 := bstep (se 1 (by rfl) ⟨2085236, by rfl⟩ : syracuseStep 2780315 = 4170473) B4170473
theorem B2190959 : Blo 972592 2190959 := bstep (se 1 (by rfl) ⟨1643219, by rfl⟩ : syracuseStep 2190959 = 3286439) B3286439
theorem B4157351 : Blo 972592 4157351 := bstep (se 1 (by rfl) ⟨3118013, by rfl⟩ : syracuseStep 4157351 = 6236027) B6236027
theorem B23752925 : Blo 972592 23752925 := bstep (se 3 (by rfl) ⟨4453673, by rfl⟩ : syracuseStep 23752925 = 8907347) B8907347
theorem B2191787 : Blo 972592 2191787 := bstep (se 1 (by rfl) ⟨1643840, by rfl⟩ : syracuseStep 2191787 = 3287681) B3287681
theorem B2001008225 : Blo 972592 2001008225 := bstep (se 2 (by rfl) ⟨750378084, by rfl⟩ : syracuseStep 2001008225 = 1500756169) B1500756169
theorem B9992159 : Blo 972592 9992159 := bstep (se 1 (by rfl) ⟨7494119, by rfl⟩ : syracuseStep 9992159 = 14988239) B14988239
theorem B2193407 : Blo 972592 2193407 := bstep (se 1 (by rfl) ⟨1645055, by rfl⟩ : syracuseStep 2193407 = 3290111) B3290111
theorem B2193515 : Blo 972592 2193515 := bstep (se 1 (by rfl) ⟨1645136, by rfl⟩ : syracuseStep 2193515 = 3290273) B3290273
theorem B1669307 : Blo 972592 1669307 := bstep (se 1 (by rfl) ⟨1251980, by rfl⟩ : syracuseStep 1669307 = 2503961) B2503961
theorem B19495183 : Blo 972592 19495183 := bstep (se 1 (by rfl) ⟨14621387, by rfl⟩ : syracuseStep 19495183 = 29242775) B29242775
theorem B39942497 : Blo 972592 39942497 := bstep (se 2 (by rfl) ⟨14978436, by rfl⟩ : syracuseStep 39942497 = 29956873) B29956873
theorem B2030393 : Blo 972592 2030393 := bstep (se 2 (by rfl) ⟨761397, by rfl⟩ : syracuseStep 2030393 = 1522795) B1522795
theorem B2194559 : Blo 972592 2194559 := bstep (se 1 (by rfl) ⟨1645919, by rfl⟩ : syracuseStep 2194559 = 3291839) B3291839
theorem B5930621 : Blo 972592 5930621 := bstep (se 3 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 5930621 = 2223983) B2223983
theorem B2196971 : Blo 972592 2196971 := bstep (se 1 (by rfl) ⟨1647728, by rfl⟩ : syracuseStep 2196971 = 3295457) B3295457
theorem B2197151 : Blo 972592 2197151 := bstep (se 1 (by rfl) ⟨1647863, by rfl⟩ : syracuseStep 2197151 = 3295727) B3295727
theorem B2197331 : Blo 972592 2197331 := bstep (se 1 (by rfl) ⟨1647998, by rfl⟩ : syracuseStep 2197331 = 3295997) B3295997
theorem B3704687 : Blo 972592 3704687 := bstep (se 1 (by rfl) ⟨2778515, by rfl⟩ : syracuseStep 3704687 = 5557031) B5557031
theorem B7407611 : Blo 972592 7407611 := bstep (se 1 (by rfl) ⟨5555708, by rfl⟩ : syracuseStep 7407611 = 11111417) B11111417
theorem B6655007 : Blo 972592 6655007 := bstep (se 1 (by rfl) ⟨4991255, by rfl⟩ : syracuseStep 6655007 = 9982511) B9982511
theorem B3706175 : Blo 972592 3706175 := bstep (se 1 (by rfl) ⟨2779631, by rfl⟩ : syracuseStep 3706175 = 5559263) B5559263
theorem B4165127 : Blo 972592 4165127 := bstep (se 1 (by rfl) ⟨3123845, by rfl⟩ : syracuseStep 4165127 = 6247691) B6247691
theorem B7016975 : Blo 972592 7016975 := bstep (se 1 (by rfl) ⟨5262731, by rfl⟩ : syracuseStep 7016975 = 10525463) B10525463
theorem B1644799 : Blo 972592 1644799 := bstep (se 1 (by rfl) ⟨1233599, by rfl⟩ : syracuseStep 1644799 = 2467199) B2467199
theorem B5937455 : Blo 972592 5937455 := bstep (se 1 (by rfl) ⟨4453091, by rfl⟩ : syracuseStep 5937455 = 8906183) B8906183
theorem B4168543 : Blo 972592 4168543 := bstep (se 1 (by rfl) ⟨3126407, by rfl⟩ : syracuseStep 4168543 = 6252815) B6252815
theorem B37985273 : Blo 972592 37985273 := bstep (se 2 (by rfl) ⟨14244477, by rfl⟩ : syracuseStep 37985273 = 28488955) B28488955
theorem B10525895 : Blo 972592 10525895 := bstep (se 1 (by rfl) ⟨7894421, by rfl⟩ : syracuseStep 10525895 = 15788843) B15788843
theorem B5414381 : Blo 972592 5414381 := bstep (se 3 (by rfl) ⟨1015196, by rfl⟩ : syracuseStep 5414381 = 2030393) B2030393
theorem B3284873 : Blo 972592 3284873 := bstep (se 2 (by rfl) ⟨1231827, by rfl⟩ : syracuseStep 3284873 = 2463655) B2463655
theorem B3284927 : Blo 972592 3284927 := bstep (se 1 (by rfl) ⟨2463695, by rfl⟩ : syracuseStep 3284927 = 4927391) B4927391
theorem B15835283 : Blo 972592 15835283 := bstep (se 1 (by rfl) ⟨11876462, by rfl⟩ : syracuseStep 15835283 = 23752925) B23752925
theorem B25993577 : Blo 972592 25993577 := bstep (se 2 (by rfl) ⟨9747591, by rfl⟩ : syracuseStep 25993577 = 19495183) B19495183
theorem B6661439 : Blo 972592 6661439 := bstep (se 1 (by rfl) ⟨4996079, by rfl⟩ : syracuseStep 6661439 = 9992159) B9992159
theorem B7022047 : Blo 972592 7022047 := bstep (se 1 (by rfl) ⟨5266535, by rfl⟩ : syracuseStep 7022047 = 10533071) B10533071
theorem B1386239 : Blo 972592 1386239 := bstep (se 1 (by rfl) ⟨1039679, by rfl⟩ : syracuseStep 1386239 = 2079359) B2079359
theorem B2467817 : Blo 972592 2467817 := bstep (se 2 (by rfl) ⟨925431, by rfl⟩ : syracuseStep 2467817 = 1850863) B1850863
theorem B7023347 : Blo 972592 7023347 := bstep (se 1 (by rfl) ⟨5267510, by rfl⟩ : syracuseStep 7023347 = 10535021) B10535021
theorem B9382949 : Blo 972592 9382949 := bstep (se 4 (by rfl) ⟨879651, by rfl⟩ : syracuseStep 9382949 = 1759303) B1759303
theorem B3124601 : Blo 972592 3124601 := bstep (se 2 (by rfl) ⟨1171725, by rfl⟩ : syracuseStep 3124601 = 2343451) B2343451
theorem B1847119 : Blo 972592 1847119 := bstep (se 1 (by rfl) ⟨1385339, by rfl⟩ : syracuseStep 1847119 = 2770679) B2770679
theorem B5550767 : Blo 972592 5550767 := bstep (se 1 (by rfl) ⟨4163075, by rfl⟩ : syracuseStep 5550767 = 8326151) B8326151
theorem B2077787 : Blo 972592 2077787 := bstep (se 1 (by rfl) ⟨1558340, by rfl⟩ : syracuseStep 2077787 = 3116681) B3116681
theorem B3291731 : Blo 972592 3291731 := bstep (se 1 (by rfl) ⟨2468798, by rfl⟩ : syracuseStep 3291731 = 4937597) B4937597
theorem B2637215 : Blo 972592 2637215 := bstep (se 1 (by rfl) ⟨1977911, by rfl⟩ : syracuseStep 2637215 = 3955823) B3955823
theorem B3292649 : Blo 972592 3292649 := bstep (se 2 (by rfl) ⟨1234743, by rfl⟩ : syracuseStep 3292649 = 2469487) B2469487
theorem B4932251 : Blo 972592 4932251 := bstep (se 1 (by rfl) ⟨3699188, by rfl⟩ : syracuseStep 4932251 = 7398377) B7398377
theorem B4932413 : Blo 972592 4932413 := bstep (se 3 (by rfl) ⟨924827, by rfl⟩ : syracuseStep 4932413 = 1849655) B1849655
theorem B1459007 : Blo 972592 1459007 := bstep (se 1 (by rfl) ⟨1094255, by rfl⟩ : syracuseStep 1459007 = 2188511) B2188511
theorem B3949415 : Blo 972592 3949415 := bstep (se 1 (by rfl) ⟨2962061, by rfl⟩ : syracuseStep 3949415 = 5924123) B5924123
theorem B106513325 : Blo 972592 106513325 := bstep (se 3 (by rfl) ⟨19971248, by rfl⟩ : syracuseStep 106513325 = 39942497) B39942497
theorem B1459337 : Blo 972592 1459337 := bstep (se 2 (by rfl) ⟨547251, by rfl⟩ : syracuseStep 1459337 = 1094503) B1094503
theorem B10536443 : Blo 972592 10536443 := bstep (se 1 (by rfl) ⟨7902332, by rfl⟩ : syracuseStep 10536443 = 15804665) B15804665
theorem B1460315 : Blo 972592 1460315 := bstep (se 1 (by rfl) ⟨1095236, by rfl⟩ : syracuseStep 1460315 = 2190473) B2190473
theorem B1460327 : Blo 972592 1460327 := bstep (se 1 (by rfl) ⟨1095245, by rfl⟩ : syracuseStep 1460327 = 2190491) B2190491
theorem B1853543 : Blo 972592 1853543 := bstep (se 1 (by rfl) ⟨1390157, by rfl⟩ : syracuseStep 1853543 = 2780315) B2780315
theorem B19974539 : Blo 972592 19974539 := bstep (se 1 (by rfl) ⟨14980904, by rfl⟩ : syracuseStep 19974539 = 29961809) B29961809
theorem B1460639 : Blo 972592 1460639 := bstep (se 1 (by rfl) ⟨1095479, by rfl⟩ : syracuseStep 1460639 = 2190959) B2190959
theorem B2771567 : Blo 972592 2771567 := bstep (se 1 (by rfl) ⟨2078675, by rfl⟩ : syracuseStep 2771567 = 4157351) B4157351
theorem B1460969 : Blo 972592 1460969 := bstep (se 2 (by rfl) ⟨547863, by rfl⟩ : syracuseStep 1460969 = 1095727) B1095727
theorem B1461191 : Blo 972592 1461191 := bstep (se 1 (by rfl) ⟨1095893, by rfl⟩ : syracuseStep 1461191 = 2191787) B2191787
theorem B5623019 : Blo 972592 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B5557531 : Blo 972592 5557531 := bstep (se 1 (by rfl) ⟨4168148, by rfl⟩ : syracuseStep 5557531 = 8336297) B8336297
theorem B1334005483 : Blo 972592 1334005483 := bstep (se 1 (by rfl) ⟨1000504112, by rfl⟩ : syracuseStep 1334005483 = 2001008225) B2001008225
theorem B1462271 : Blo 972592 1462271 := bstep (se 1 (by rfl) ⟨1096703, by rfl⟩ : syracuseStep 1462271 = 2193407) B2193407
theorem B1462343 : Blo 972592 1462343 := bstep (se 1 (by rfl) ⟨1096757, by rfl⟩ : syracuseStep 1462343 = 2193515) B2193515
theorem B1463039 : Blo 972592 1463039 := bstep (se 1 (by rfl) ⟨1097279, by rfl⟩ : syracuseStep 1463039 = 2194559) B2194559
theorem B4445047 : Blo 972592 4445047 := bstep (se 1 (by rfl) ⟨3333785, by rfl⟩ : syracuseStep 4445047 = 6667571) B6667571
theorem B1561513 : Blo 972592 1561513 := bstep (se 2 (by rfl) ⟨585567, by rfl⟩ : syracuseStep 1561513 = 1171135) B1171135
theorem B3953747 : Blo 972592 3953747 := bstep (se 1 (by rfl) ⟨2965310, by rfl⟩ : syracuseStep 3953747 = 5930621) B5930621
theorem B1464479 : Blo 972592 1464479 := bstep (se 1 (by rfl) ⟨1098359, by rfl⟩ : syracuseStep 1464479 = 2196719) B2196719
theorem B11098295 : Blo 972592 11098295 := bstep (se 1 (by rfl) ⟨8323721, by rfl⟩ : syracuseStep 11098295 = 16647443) B16647443
theorem B973051 : Blo 972592 973051 := bstep (se 1 (by rfl) ⟨729788, by rfl⟩ : syracuseStep 973051 = 1459577) B1459577
theorem B3693023 : Blo 972592 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B1464815 : Blo 972592 1464815 := bstep (se 1 (by rfl) ⟨1098611, by rfl⟩ : syracuseStep 1464815 = 2197223) B2197223
theorem B973423 : Blo 972592 973423 := bstep (se 1 (by rfl) ⟨730067, by rfl⟩ : syracuseStep 973423 = 1460135) B1460135
theorem B973439 : Blo 972592 973439 := bstep (se 1 (by rfl) ⟨730079, by rfl⟩ : syracuseStep 973439 = 1460159) B1460159
theorem B973567 : Blo 972592 973567 := bstep (se 1 (by rfl) ⟨730175, by rfl⟩ : syracuseStep 973567 = 1460351) B1460351
theorem B973935 : Blo 972592 973935 := bstep (se 1 (by rfl) ⟨730451, by rfl⟩ : syracuseStep 973935 = 1460903) B1460903
theorem B973983 : Blo 972592 973983 := bstep (se 1 (by rfl) ⟨730487, by rfl⟩ : syracuseStep 973983 = 1460975) B1460975
theorem B974239 : Blo 972592 974239 := bstep (se 1 (by rfl) ⟨730679, by rfl⟩ : syracuseStep 974239 = 1461359) B1461359
theorem B3693995 : Blo 972592 3693995 := bstep (se 1 (by rfl) ⟨2770496, by rfl⟩ : syracuseStep 3693995 = 5540993) B5540993
theorem B974367 : Blo 972592 974367 := bstep (se 1 (by rfl) ⟨730775, by rfl⟩ : syracuseStep 974367 = 1461551) B1461551
theorem B975167 : Blo 972592 975167 := bstep (se 1 (by rfl) ⟨731375, by rfl⟩ : syracuseStep 975167 = 1462751) B1462751
theorem B6250841 : Blo 972592 6250841 := bstep (se 2 (by rfl) ⟨2344065, by rfl⟩ : syracuseStep 6250841 = 4688131) B4688131
theorem B975407 : Blo 972592 975407 := bstep (se 1 (by rfl) ⟨731555, by rfl⟩ : syracuseStep 975407 = 1463111) B1463111
theorem B975687 : Blo 972592 975687 := bstep (se 1 (by rfl) ⟨731765, by rfl⟩ : syracuseStep 975687 = 1463531) B1463531
theorem B4219751 : Blo 972592 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B976123 : Blo 972592 976123 := bstep (se 1 (by rfl) ⟨732092, by rfl⟩ : syracuseStep 976123 = 1464185) B1464185
theorem B2975183 : Blo 972592 2975183 := bstep (se 1 (by rfl) ⟨2231387, by rfl⟩ : syracuseStep 2975183 = 4462775) B4462775
theorem B2188799 : Blo 972592 2188799 := bstep (se 1 (by rfl) ⟨1641599, by rfl⟩ : syracuseStep 2188799 = 3283199) B3283199
theorem B1042751 : Blo 972592 1042751 := bstep (se 1 (by rfl) ⟨782063, by rfl⟩ : syracuseStep 1042751 = 1564127) B1564127
theorem B15198911 : Blo 972592 15198911 := bstep (se 1 (by rfl) ⟨11399183, by rfl⟩ : syracuseStep 15198911 = 22798367) B22798367
theorem B2190059 : Blo 972592 2190059 := bstep (se 1 (by rfl) ⟨1642544, by rfl⟩ : syracuseStep 2190059 = 3285089) B3285089
theorem B37972775 : Blo 972592 37972775 := bstep (se 1 (by rfl) ⟨28479581, by rfl⟩ : syracuseStep 37972775 = 56959163) B56959163
theorem B4451485 : Blo 972592 4451485 := bstep (se 3 (by rfl) ⟨834653, by rfl⟩ : syracuseStep 4451485 = 1669307) B1669307
theorem B2191175 : Blo 972592 2191175 := bstep (se 1 (by rfl) ⟨1643381, by rfl⟩ : syracuseStep 2191175 = 3286763) B3286763
theorem B2847059 : Blo 972592 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B4683017 : Blo 972592 4683017 := bstep (se 2 (by rfl) ⟨1756131, by rfl⟩ : syracuseStep 4683017 = 3512263) B3512263
theorem B2192723 : Blo 972592 2192723 := bstep (se 1 (by rfl) ⟨1644542, by rfl⟩ : syracuseStep 2192723 = 3289085) B3289085
theorem B50690225 : Blo 972592 50690225 := bstep (se 2 (by rfl) ⟨19008834, by rfl⟩ : syracuseStep 50690225 = 38017669) B38017669
theorem B3081009737 : Blo 972592 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B10844855 : Blo 972592 10844855 := bstep (se 1 (by rfl) ⟨8133641, by rfl⟩ : syracuseStep 10844855 = 16267283) B16267283
theorem B2194217 : Blo 972592 2194217 := bstep (se 2 (by rfl) ⟨822831, by rfl⟩ : syracuseStep 2194217 = 1645663) B1645663
theorem B3701969 : Blo 972592 3701969 := bstep (se 2 (by rfl) ⟨1388238, by rfl⟩ : syracuseStep 3701969 = 2776477) B2776477
theorem B5275489 : Blo 972592 5275489 := bstep (se 2 (by rfl) ⟨1978308, by rfl⟩ : syracuseStep 5275489 = 3956617) B3956617
theorem B71008883 : Blo 972592 71008883 := bstep (se 1 (by rfl) ⟨53256662, by rfl⟩ : syracuseStep 71008883 = 106513325) B106513325
theorem B5935313 : Blo 972592 5935313 := bstep (se 2 (by rfl) ⟨2225742, by rfl⟩ : syracuseStep 5935313 = 4451485) B4451485
theorem B2462015 : Blo 972592 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B7410041 : Blo 972592 7410041 := bstep (se 2 (by rfl) ⟨2778765, by rfl⟩ : syracuseStep 7410041 = 5557531) B5557531
theorem B7017263 : Blo 972592 7017263 := bstep (se 1 (by rfl) ⟨5262947, by rfl⟩ : syracuseStep 7017263 = 10525895) B10525895
theorem B2462663 : Blo 972592 2462663 := bstep (se 1 (by rfl) ⟨1846997, by rfl⟩ : syracuseStep 2462663 = 3693995) B3693995
theorem B3609587 : Blo 972592 3609587 := bstep (se 1 (by rfl) ⟨2707190, by rfl⟩ : syracuseStep 3609587 = 5414381) B5414381
theorem B2462825 : Blo 972592 2462825 := bstep (se 2 (by rfl) ⟨923559, by rfl⟩ : syracuseStep 2462825 = 1847119) B1847119
theorem B10556855 : Blo 972592 10556855 := bstep (se 1 (by rfl) ⟨7917641, by rfl⟩ : syracuseStep 10556855 = 15835283) B15835283
theorem B4167227 : Blo 972592 4167227 := bstep (se 1 (by rfl) ⟨3125420, by rfl⟩ : syracuseStep 4167227 = 6250841) B6250841
theorem B1645211 : Blo 972592 1645211 := bstep (se 1 (by rfl) ⟨1233908, by rfl⟩ : syracuseStep 1645211 = 2467817) B2467817
theorem B8216025965 : Blo 972592 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B10132607 : Blo 972592 10132607 := bstep (se 1 (by rfl) ⟨7599455, by rfl⟩ : syracuseStep 10132607 = 15198911) B15198911
theorem B1385191 : Blo 972592 1385191 := bstep (se 1 (by rfl) ⟨1038893, by rfl⟩ : syracuseStep 1385191 = 2077787) B2077787
theorem B3122011 : Blo 972592 3122011 := bstep (se 1 (by rfl) ⟨2341508, by rfl⟩ : syracuseStep 3122011 = 4683017) B4683017
theorem B33793483 : Blo 972592 33793483 := bstep (se 1 (by rfl) ⟨25345112, by rfl⟩ : syracuseStep 33793483 = 50690225) B50690225
theorem B2467979 : Blo 972592 2467979 := bstep (se 1 (by rfl) ⟨1850984, by rfl⟩ : syracuseStep 2467979 = 3701969) B3701969
theorem B3288167 : Blo 972592 3288167 := bstep (se 1 (by rfl) ⟨2466125, by rfl⟩ : syracuseStep 3288167 = 4932251) B4932251
theorem B3288275 : Blo 972592 3288275 := bstep (se 1 (by rfl) ⟨2466206, by rfl⟩ : syracuseStep 3288275 = 4932413) B4932413
theorem B2632943 : Blo 972592 2632943 := bstep (se 1 (by rfl) ⟨1974707, by rfl⟩ : syracuseStep 2632943 = 3949415) B3949415
theorem B7024295 : Blo 972592 7024295 := bstep (se 1 (by rfl) ⟨5268221, by rfl⟩ : syracuseStep 7024295 = 10536443) B10536443
theorem B2469791 : Blo 972592 2469791 := bstep (se 1 (by rfl) ⟨1852343, by rfl⟩ : syracuseStep 2469791 = 3704687) B3704687
theorem B13316359 : Blo 972592 13316359 := bstep (se 1 (by rfl) ⟨9987269, by rfl⟩ : syracuseStep 13316359 = 19974539) B19974539
theorem B1847711 : Blo 972592 1847711 := bstep (se 1 (by rfl) ⟨1385783, by rfl⟩ : syracuseStep 1847711 = 2771567) B2771567
theorem B3748679 : Blo 972592 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B2470783 : Blo 972592 2470783 := bstep (se 1 (by rfl) ⟨1853087, by rfl⟩ : syracuseStep 2470783 = 3706175) B3706175
theorem B2635831 : Blo 972592 2635831 := bstep (se 1 (by rfl) ⟨1976873, by rfl⟩ : syracuseStep 2635831 = 3953747) B3953747
theorem B180042709 : Blo 972592 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B4440959 : Blo 972592 4440959 := bstep (se 1 (by rfl) ⟨3330719, by rfl⟩ : syracuseStep 4440959 = 6661439) B6661439
theorem B1983455 : Blo 972592 1983455 := bstep (se 1 (by rfl) ⟨1487591, by rfl⟩ : syracuseStep 1983455 = 2975183) B2975183
theorem B1459199 : Blo 972592 1459199 := bstep (se 1 (by rfl) ⟨1094399, by rfl⟩ : syracuseStep 1459199 = 2188799) B2188799
theorem B2082017 : Blo 972592 2082017 := bstep (se 2 (by rfl) ⟨780756, by rfl⟩ : syracuseStep 2082017 = 1561513) B1561513
theorem B1460039 : Blo 972592 1460039 := bstep (se 1 (by rfl) ⟨1095029, by rfl⟩ : syracuseStep 1460039 = 2190059) B2190059
theorem B25315183 : Blo 972592 25315183 := bstep (se 1 (by rfl) ⟨18986387, by rfl⟩ : syracuseStep 25315183 = 37972775) B37972775
theorem B2083067 : Blo 972592 2083067 := bstep (se 1 (by rfl) ⟨1562300, by rfl⟩ : syracuseStep 2083067 = 3124601) B3124601
theorem B1460783 : Blo 972592 1460783 := bstep (se 1 (by rfl) ⟨1095587, by rfl⟩ : syracuseStep 1460783 = 2191175) B2191175
theorem B17746685 : Blo 972592 17746685 := bstep (se 3 (by rfl) ⟨3327503, by rfl⟩ : syracuseStep 17746685 = 6655007) B6655007
theorem B1461815 : Blo 972592 1461815 := bstep (se 1 (by rfl) ⟨1096361, by rfl⟩ : syracuseStep 1461815 = 2192723) B2192723
theorem B5558057 : Blo 972592 5558057 := bstep (se 2 (by rfl) ⟨2084271, by rfl⟩ : syracuseStep 5558057 = 4168543) B4168543
theorem B7229903 : Blo 972592 7229903 := bstep (se 1 (by rfl) ⟨5422427, by rfl⟩ : syracuseStep 7229903 = 10844855) B10844855
theorem B1462811 : Blo 972592 1462811 := bstep (se 1 (by rfl) ⟨1097108, by rfl⟩ : syracuseStep 1462811 = 2194217) B2194217
theorem B1758143 : Blo 972592 1758143 := bstep (se 1 (by rfl) ⟨1318607, by rfl⟩ : syracuseStep 1758143 = 2637215) B2637215
theorem B7033985 : Blo 972592 7033985 := bstep (se 2 (by rfl) ⟨2637744, by rfl⟩ : syracuseStep 7033985 = 5275489) B5275489
theorem B972671 : Blo 972592 972671 := bstep (se 1 (by rfl) ⟨729503, by rfl⟩ : syracuseStep 972671 = 1459007) B1459007
theorem B972891 : Blo 972592 972891 := bstep (se 1 (by rfl) ⟨729668, by rfl⟩ : syracuseStep 972891 = 1459337) B1459337
theorem B1464647 : Blo 972592 1464647 := bstep (se 1 (by rfl) ⟨1098485, by rfl⟩ : syracuseStep 1464647 = 2196971) B2196971
theorem B1464767 : Blo 972592 1464767 := bstep (se 1 (by rfl) ⟨1098575, by rfl⟩ : syracuseStep 1464767 = 2197151) B2197151
theorem B1464887 : Blo 972592 1464887 := bstep (se 1 (by rfl) ⟨1098665, by rfl⟩ : syracuseStep 1464887 = 2197331) B2197331
theorem B4938407 : Blo 972592 4938407 := bstep (se 1 (by rfl) ⟨3703805, by rfl⟩ : syracuseStep 4938407 = 7407611) B7407611
theorem B973543 : Blo 972592 973543 := bstep (se 1 (by rfl) ⟨730157, by rfl⟩ : syracuseStep 973543 = 1460315) B1460315
theorem B973551 : Blo 972592 973551 := bstep (se 1 (by rfl) ⟨730163, by rfl⟩ : syracuseStep 973551 = 1460327) B1460327
theorem B973759 : Blo 972592 973759 := bstep (se 1 (by rfl) ⟨730319, by rfl⟩ : syracuseStep 973759 = 1460639) B1460639
theorem B973979 : Blo 972592 973979 := bstep (se 1 (by rfl) ⟨730484, by rfl⟩ : syracuseStep 973979 = 1460969) B1460969
theorem B9362729 : Blo 972592 9362729 := bstep (se 2 (by rfl) ⟨3511023, by rfl⟩ : syracuseStep 9362729 = 7022047) B7022047
theorem B974127 : Blo 972592 974127 := bstep (se 1 (by rfl) ⟨730595, by rfl⟩ : syracuseStep 974127 = 1461191) B1461191
theorem B2776751 : Blo 972592 2776751 := bstep (se 1 (by rfl) ⟨2082563, by rfl⟩ : syracuseStep 2776751 = 4165127) B4165127
theorem B974847 : Blo 972592 974847 := bstep (se 1 (by rfl) ⟨731135, by rfl⟩ : syracuseStep 974847 = 1462271) B1462271
theorem B974895 : Blo 972592 974895 := bstep (se 1 (by rfl) ⟨731171, by rfl⟩ : syracuseStep 974895 = 1462343) B1462343
theorem B4677983 : Blo 972592 4677983 := bstep (se 1 (by rfl) ⟨3508487, by rfl⟩ : syracuseStep 4677983 = 7016975) B7016975
theorem B975359 : Blo 972592 975359 := bstep (se 1 (by rfl) ⟨731519, by rfl⟩ : syracuseStep 975359 = 1463039) B1463039
theorem B976319 : Blo 972592 976319 := bstep (se 1 (by rfl) ⟨732239, by rfl⟩ : syracuseStep 976319 = 1464479) B1464479
theorem B7398863 : Blo 972592 7398863 := bstep (se 1 (by rfl) ⟨5549147, by rfl⟩ : syracuseStep 7398863 = 11098295) B11098295
theorem B3958303 : Blo 972592 3958303 := bstep (se 1 (by rfl) ⟨2968727, by rfl⟩ : syracuseStep 3958303 = 5937455) B5937455
theorem B976543 : Blo 972592 976543 := bstep (se 1 (by rfl) ⟨732407, by rfl⟩ : syracuseStep 976543 = 1464815) B1464815
theorem B25323515 : Blo 972592 25323515 := bstep (se 1 (by rfl) ⟨18992636, by rfl⟩ : syracuseStep 25323515 = 37985273) B37985273
theorem B3696637 : Blo 972592 3696637 := bstep (se 3 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 3696637 = 1386239) B1386239
theorem B1778673977 : Blo 972592 1778673977 := bstep (se 2 (by rfl) ⟨667002741, by rfl⟩ : syracuseStep 1778673977 = 1334005483) B1334005483
theorem B2189915 : Blo 972592 2189915 := bstep (se 1 (by rfl) ⟨1642436, by rfl⟩ : syracuseStep 2189915 = 3284873) B3284873
theorem B2189951 : Blo 972592 2189951 := bstep (se 1 (by rfl) ⟨1642463, by rfl⟩ : syracuseStep 2189951 = 3284927) B3284927
theorem B17329051 : Blo 972592 17329051 := bstep (se 1 (by rfl) ⟨12996788, by rfl⟩ : syracuseStep 17329051 = 25993577) B25993577
theorem B4942781 : Blo 972592 4942781 := bstep (se 3 (by rfl) ⟨926771, by rfl⟩ : syracuseStep 4942781 = 1853543) B1853543
theorem B2780669 : Blo 972592 2780669 := bstep (se 3 (by rfl) ⟨521375, by rfl⟩ : syracuseStep 2780669 = 1042751) B1042751
theorem B5926729 : Blo 972592 5926729 := bstep (se 2 (by rfl) ⟨2222523, by rfl⟩ : syracuseStep 5926729 = 4445047) B4445047
theorem B4682231 : Blo 972592 4682231 := bstep (se 1 (by rfl) ⟨3511673, by rfl⟩ : syracuseStep 4682231 = 7023347) B7023347
theorem B6255299 : Blo 972592 6255299 := bstep (se 1 (by rfl) ⟨4691474, by rfl⟩ : syracuseStep 6255299 = 9382949) B9382949
theorem B1898039 : Blo 972592 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B2193065 : Blo 972592 2193065 := bstep (se 2 (by rfl) ⟨822399, by rfl⟩ : syracuseStep 2193065 = 1644799) B1644799
theorem B3700511 : Blo 972592 3700511 := bstep (se 1 (by rfl) ⟨2775383, by rfl⟩ : syracuseStep 3700511 = 5550767) B5550767
theorem B2194487 : Blo 972592 2194487 := bstep (se 1 (by rfl) ⟨1645865, by rfl⟩ : syracuseStep 2194487 = 3291731) B3291731
theorem B2195099 : Blo 972592 2195099 := bstep (se 1 (by rfl) ⟨1646324, by rfl⟩ : syracuseStep 2195099 = 3292649) B3292649
theorem B15827501 : Blo 972592 15827501 := bstep (se 3 (by rfl) ⟨2967656, by rfl⟩ : syracuseStep 15827501 = 5935313) B5935313
theorem B4162681 : Blo 972592 4162681 := bstep (se 2 (by rfl) ⟨1561005, by rfl⟩ : syracuseStep 4162681 = 3122011) B3122011
theorem B11831123 : Blo 972592 11831123 := bstep (se 1 (by rfl) ⟨8873342, by rfl⟩ : syracuseStep 11831123 = 17746685) B17746685
theorem B45057977 : Blo 972592 45057977 := bstep (se 2 (by rfl) ⟨16896741, by rfl⟩ : syracuseStep 45057977 = 33793483) B33793483
theorem B5277737 : Blo 972592 5277737 := bstep (se 2 (by rfl) ⟨1979151, by rfl⟩ : syracuseStep 5277737 = 3958303) B3958303
theorem B4688381 : Blo 972592 4688381 := bstep (se 3 (by rfl) ⟨879071, by rfl⟩ : syracuseStep 4688381 = 1758143) B1758143
theorem B3705371 : Blo 972592 3705371 := bstep (se 1 (by rfl) ⟨2779028, by rfl⟩ : syracuseStep 3705371 = 5558057) B5558057
theorem B1641343 : Blo 972592 1641343 := bstep (se 1 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 1641343 = 2462015) B2462015
theorem B1641775 : Blo 972592 1641775 := bstep (se 1 (by rfl) ⟨1231331, by rfl⟩ : syracuseStep 1641775 = 2462663) B2462663
theorem B1641883 : Blo 972592 1641883 := bstep (se 1 (by rfl) ⟨1231412, by rfl⟩ : syracuseStep 1641883 = 2462825) B2462825
theorem B4689323 : Blo 972592 4689323 := bstep (se 1 (by rfl) ⟨3516992, by rfl⟩ : syracuseStep 4689323 = 7033985) B7033985
theorem B23105401 : Blo 972592 23105401 := bstep (se 2 (by rfl) ⟨8664525, by rfl⟩ : syracuseStep 23105401 = 17329051) B17329051
theorem B6755071 : Blo 972592 6755071 := bstep (se 1 (by rfl) ⟨5066303, by rfl⟩ : syracuseStep 6755071 = 10132607) B10132607
theorem B7902305 : Blo 972592 7902305 := bstep (se 2 (by rfl) ⟨2963364, by rfl⟩ : syracuseStep 7902305 = 5926729) B5926729
theorem B3118655 : Blo 972592 3118655 := bstep (se 1 (by rfl) ⟨2338991, by rfl⟩ : syracuseStep 3118655 = 4677983) B4677983
theorem B16882343 : Blo 972592 16882343 := bstep (se 1 (by rfl) ⟨12661757, by rfl⟩ : syracuseStep 16882343 = 25323515) B25323515
theorem B1645319 : Blo 972592 1645319 := bstep (se 1 (by rfl) ⟨1233989, by rfl⟩ : syracuseStep 1645319 = 2467979) B2467979
theorem B1185782651 : Blo 972592 1185782651 := bstep (se 1 (by rfl) ⟨889336988, by rfl⟩ : syracuseStep 1185782651 = 1778673977) B1778673977
theorem B1646527 : Blo 972592 1646527 := bstep (se 1 (by rfl) ⟨1234895, by rfl⟩ : syracuseStep 1646527 = 2469791) B2469791
theorem B3514441 : Blo 972592 3514441 := bstep (se 2 (by rfl) ⟨1317915, by rfl⟩ : syracuseStep 3514441 = 2635831) B2635831
theorem B3121487 : Blo 972592 3121487 := bstep (se 1 (by rfl) ⟨2341115, by rfl⟩ : syracuseStep 3121487 = 4682231) B4682231
theorem B4170199 : Blo 972592 4170199 := bstep (se 1 (by rfl) ⟨3127649, by rfl⟩ : syracuseStep 4170199 = 6255299) B6255299
theorem B2499119 : Blo 972592 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B7021181 : Blo 972592 7021181 := bstep (se 3 (by rfl) ⟨1316471, by rfl⟩ : syracuseStep 7021181 = 2632943) B2632943
theorem B2467007 : Blo 972592 2467007 := bstep (se 1 (by rfl) ⟨1850255, by rfl⟩ : syracuseStep 2467007 = 3700511) B3700511
theorem B135014309 : Blo 972592 135014309 := bstep (se 4 (by rfl) ⟨12657591, by rfl⟩ : syracuseStep 135014309 = 25315183) B25315183
theorem B2960639 : Blo 972592 2960639 := bstep (se 1 (by rfl) ⟨2220479, by rfl⟩ : syracuseStep 2960639 = 4440959) B4440959
theorem B1322303 : Blo 972592 1322303 := bstep (se 1 (by rfl) ⟨991727, by rfl⟩ : syracuseStep 1322303 = 1983455) B1983455
theorem B1388011 : Blo 972592 1388011 := bstep (se 1 (by rfl) ⟨1041008, by rfl⟩ : syracuseStep 1388011 = 2082017) B2082017
theorem B4927229 : Blo 972592 4927229 := bstep (se 3 (by rfl) ⟨923855, by rfl⟩ : syracuseStep 4927229 = 1847711) B1847711
theorem B19279741 : Blo 972592 19279741 := bstep (se 3 (by rfl) ⟨3614951, by rfl⟩ : syracuseStep 19279741 = 7229903) B7229903
theorem B1388711 : Blo 972592 1388711 := bstep (se 1 (by rfl) ⟨1041533, by rfl⟩ : syracuseStep 1388711 = 2083067) B2083067
theorem B4928849 : Blo 972592 4928849 := bstep (se 2 (by rfl) ⟨1848318, by rfl⟩ : syracuseStep 4928849 = 3696637) B3696637
theorem B2406391 : Blo 972592 2406391 := bstep (se 1 (by rfl) ⟨1804793, by rfl⟩ : syracuseStep 2406391 = 3609587) B3609587
theorem B7387685 : Blo 972592 7387685 := bstep (se 4 (by rfl) ⟨692595, by rfl⟩ : syracuseStep 7387685 = 1385191) B1385191
theorem B5061437 : Blo 972592 5061437 := bstep (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) B1898039
theorem B1096807 : Blo 972592 1096807 := bstep (se 1 (by rfl) ⟨822605, by rfl⟩ : syracuseStep 1096807 = 1645211) B1645211
theorem B3292271 : Blo 972592 3292271 := bstep (se 1 (by rfl) ⟨2469203, by rfl⟩ : syracuseStep 3292271 = 4938407) B4938407
theorem B5477350643 : Blo 972592 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B6241819 : Blo 972592 6241819 := bstep (se 1 (by rfl) ⟨4681364, by rfl⟩ : syracuseStep 6241819 = 9362729) B9362729
theorem B1851167 : Blo 972592 1851167 := bstep (se 1 (by rfl) ⟨1388375, by rfl⟩ : syracuseStep 1851167 = 2776751) B2776751
theorem B4932575 : Blo 972592 4932575 := bstep (se 1 (by rfl) ⟨3699431, by rfl⟩ : syracuseStep 4932575 = 7398863) B7398863
theorem B3294377 : Blo 972592 3294377 := bstep (se 2 (by rfl) ⟨1235391, by rfl⟩ : syracuseStep 3294377 = 2470783) B2470783
theorem B1459943 : Blo 972592 1459943 := bstep (se 1 (by rfl) ⟨1094957, by rfl⟩ : syracuseStep 1459943 = 2189915) B2189915
theorem B1459967 : Blo 972592 1459967 := bstep (se 1 (by rfl) ⟨1094975, by rfl⟩ : syracuseStep 1459967 = 2189951) B2189951
theorem B3295187 : Blo 972592 3295187 := bstep (se 1 (by rfl) ⟨2471390, by rfl⟩ : syracuseStep 3295187 = 4942781) B4942781
theorem B1853779 : Blo 972592 1853779 := bstep (se 1 (by rfl) ⟨1390334, by rfl⟩ : syracuseStep 1853779 = 2780669) B2780669
theorem B1462043 : Blo 972592 1462043 := bstep (se 1 (by rfl) ⟨1096532, by rfl⟩ : syracuseStep 1462043 = 2193065) B2193065
theorem B1462991 : Blo 972592 1462991 := bstep (se 1 (by rfl) ⟨1097243, by rfl⟩ : syracuseStep 1462991 = 2194487) B2194487
theorem B1463399 : Blo 972592 1463399 := bstep (se 1 (by rfl) ⟨1097549, by rfl⟩ : syracuseStep 1463399 = 2195099) B2195099
theorem B47339255 : Blo 972592 47339255 := bstep (se 1 (by rfl) ⟨35504441, by rfl⟩ : syracuseStep 47339255 = 71008883) B71008883
theorem B972799 : Blo 972592 972799 := bstep (se 1 (by rfl) ⟨729599, by rfl⟩ : syracuseStep 972799 = 1459199) B1459199
theorem B973359 : Blo 972592 973359 := bstep (se 1 (by rfl) ⟨730019, by rfl⟩ : syracuseStep 973359 = 1460039) B1460039
theorem B973855 : Blo 972592 973855 := bstep (se 1 (by rfl) ⟨730391, by rfl⟩ : syracuseStep 973855 = 1460783) B1460783
theorem B974543 : Blo 972592 974543 := bstep (se 1 (by rfl) ⟨730907, by rfl⟩ : syracuseStep 974543 = 1461815) B1461815
theorem B4940027 : Blo 972592 4940027 := bstep (se 1 (by rfl) ⟨3705020, by rfl⟩ : syracuseStep 4940027 = 7410041) B7410041
theorem B975207 : Blo 972592 975207 := bstep (se 1 (by rfl) ⟨731405, by rfl⟩ : syracuseStep 975207 = 1462811) B1462811
theorem B4678175 : Blo 972592 4678175 := bstep (se 1 (by rfl) ⟨3508631, by rfl⟩ : syracuseStep 4678175 = 7017263) B7017263
theorem B7037903 : Blo 972592 7037903 := bstep (se 1 (by rfl) ⟨5278427, by rfl⟩ : syracuseStep 7037903 = 10556855) B10556855
theorem B2778151 : Blo 972592 2778151 := bstep (se 1 (by rfl) ⟨2083613, by rfl⟩ : syracuseStep 2778151 = 4167227) B4167227
theorem B976431 : Blo 972592 976431 := bstep (se 1 (by rfl) ⟨732323, by rfl⟩ : syracuseStep 976431 = 1464647) B1464647
theorem B976511 : Blo 972592 976511 := bstep (se 1 (by rfl) ⟨732383, by rfl⟩ : syracuseStep 976511 = 1464767) B1464767
theorem B976591 : Blo 972592 976591 := bstep (se 1 (by rfl) ⟨732443, by rfl⟩ : syracuseStep 976591 = 1464887) B1464887
theorem B17755145 : Blo 972592 17755145 := bstep (se 2 (by rfl) ⟨6658179, by rfl⟩ : syracuseStep 17755145 = 13316359) B13316359
theorem B2192111 : Blo 972592 2192111 := bstep (se 1 (by rfl) ⟨1644083, by rfl⟩ : syracuseStep 2192111 = 3288167) B3288167
theorem B2192183 : Blo 972592 2192183 := bstep (se 1 (by rfl) ⟨1644137, by rfl⟩ : syracuseStep 2192183 = 3288275) B3288275
theorem B4682863 : Blo 972592 4682863 := bstep (se 1 (by rfl) ⟨3512147, by rfl⟩ : syracuseStep 4682863 = 7024295) B7024295
theorem B240056945 : Blo 972592 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B4685921 : Blo 972592 4685921 := bstep (se 2 (by rfl) ⟨1757220, by rfl⟩ : syracuseStep 4685921 = 3514441) B3514441
theorem B10551667 : Blo 972592 10551667 := bstep (se 1 (by rfl) ⟨7913750, by rfl⟩ : syracuseStep 10551667 = 15827501) B15827501
theorem B3703229 : Blo 972592 3703229 := bstep (se 3 (by rfl) ⟨694355, by rfl⟩ : syracuseStep 3703229 = 1388711) B1388711
theorem B2196251 : Blo 972592 2196251 := bstep (se 1 (by rfl) ⟨1647188, by rfl⟩ : syracuseStep 2196251 = 3294377) B3294377
theorem B2196791 : Blo 972592 2196791 := bstep (se 1 (by rfl) ⟨1647593, by rfl⟩ : syracuseStep 2196791 = 3295187) B3295187
theorem B3704201 : Blo 972592 3704201 := bstep (se 2 (by rfl) ⟨1389075, by rfl⟩ : syracuseStep 3704201 = 2778151) B2778151
theorem B31559503 : Blo 972592 31559503 := bstep (se 1 (by rfl) ⟨23669627, by rfl⟩ : syracuseStep 31559503 = 47339255) B47339255
theorem B3118783 : Blo 972592 3118783 := bstep (se 1 (by rfl) ⟨2339087, by rfl⟩ : syracuseStep 3118783 = 4678175) B4678175
theorem B4691935 : Blo 972592 4691935 := bstep (se 1 (by rfl) ⟨3518951, by rfl⟩ : syracuseStep 4691935 = 7037903) B7037903
theorem B1644671 : Blo 972592 1644671 := bstep (se 1 (by rfl) ⟨1233503, by rfl⟩ : syracuseStep 1644671 = 2467007) B2467007
theorem B11836763 : Blo 972592 11836763 := bstep (se 1 (by rfl) ⟨8877572, by rfl⟩ : syracuseStep 11836763 = 17755145) B17755145
theorem B1973759 : Blo 972592 1973759 := bstep (se 1 (by rfl) ⟨1480319, by rfl⟩ : syracuseStep 1973759 = 2960639) B2960639
theorem B3284819 : Blo 972592 3284819 := bstep (se 1 (by rfl) ⟨2463614, by rfl⟩ : syracuseStep 3284819 = 4927229) B4927229
theorem B3285899 : Blo 972592 3285899 := bstep (se 1 (by rfl) ⟨2464424, by rfl⟩ : syracuseStep 3285899 = 4928849) B4928849
theorem B4925123 : Blo 972592 4925123 := bstep (se 1 (by rfl) ⟨3693842, by rfl⟩ : syracuseStep 4925123 = 7387685) B7387685
theorem B3288383 : Blo 972592 3288383 := bstep (se 1 (by rfl) ⟨2466287, by rfl⟩ : syracuseStep 3288383 = 4932575) B4932575
theorem B3518491 : Blo 972592 3518491 := bstep (se 1 (by rfl) ⟨2638868, by rfl⟩ : syracuseStep 3518491 = 5277737) B5277737
theorem B5550241 : Blo 972592 5550241 := bstep (se 2 (by rfl) ⟨2081340, by rfl⟩ : syracuseStep 5550241 = 4162681) B4162681
theorem B18723149 : Blo 972592 18723149 := bstep (se 3 (by rfl) ⟨3510590, by rfl⟩ : syracuseStep 18723149 = 7021181) B7021181
theorem B2470247 : Blo 972592 2470247 := bstep (se 1 (by rfl) ⟨1852685, by rfl⟩ : syracuseStep 2470247 = 3705371) B3705371
theorem B3126215 : Blo 972592 3126215 := bstep (se 1 (by rfl) ⟨2344661, by rfl⟩ : syracuseStep 3126215 = 4689323) B4689323
theorem B2471705 : Blo 972592 2471705 := bstep (se 2 (by rfl) ⟨926889, by rfl⟩ : syracuseStep 2471705 = 1853779) B1853779
theorem B2079103 : Blo 972592 2079103 := bstep (se 1 (by rfl) ⟨1559327, by rfl⟩ : syracuseStep 2079103 = 3118655) B3118655
theorem B11254895 : Blo 972592 11254895 := bstep (se 1 (by rfl) ⟨8441171, by rfl⟩ : syracuseStep 11254895 = 16882343) B16882343
theorem B1096879 : Blo 972592 1096879 := bstep (se 1 (by rfl) ⟨822659, by rfl⟩ : syracuseStep 1096879 = 1645319) B1645319
theorem B1850681 : Blo 972592 1850681 := bstep (se 2 (by rfl) ⟨694005, by rfl⟩ : syracuseStep 1850681 = 1388011) B1388011
theorem B25706321 : Blo 972592 25706321 := bstep (se 2 (by rfl) ⟨9639870, by rfl⟩ : syracuseStep 25706321 = 19279741) B19279741
theorem B3293351 : Blo 972592 3293351 := bstep (se 1 (by rfl) ⟨2470013, by rfl⟩ : syracuseStep 3293351 = 4940027) B4940027
theorem B2080991 : Blo 972592 2080991 := bstep (se 1 (by rfl) ⟨1560743, by rfl⟩ : syracuseStep 2080991 = 3121487) B3121487
theorem B12502349 : Blo 972592 12502349 := bstep (se 3 (by rfl) ⟨2344190, by rfl⟩ : syracuseStep 12502349 = 4688381) B4688381
theorem B6243817 : Blo 972592 6243817 := bstep (se 2 (by rfl) ⟨2341431, by rfl⟩ : syracuseStep 6243817 = 4682863) B4682863
theorem B1461407 : Blo 972592 1461407 := bstep (se 1 (by rfl) ⟨1096055, by rfl⟩ : syracuseStep 1461407 = 2192111) B2192111
theorem B1461455 : Blo 972592 1461455 := bstep (se 1 (by rfl) ⟨1096091, by rfl⟩ : syracuseStep 1461455 = 2192183) B2192183
theorem B3526141 : Blo 972592 3526141 := bstep (se 3 (by rfl) ⟨661151, by rfl⟩ : syracuseStep 3526141 = 1322303) B1322303
theorem B1462409 : Blo 972592 1462409 := bstep (se 2 (by rfl) ⟨548403, by rfl⟩ : syracuseStep 1462409 = 1096807) B1096807
theorem B123228805 : Blo 972592 123228805 := bstep (se 4 (by rfl) ⟨11552700, by rfl⟩ : syracuseStep 123228805 = 23105401) B23105401
theorem B51336341 : Blo 972592 51336341 := bstep (se 6 (by rfl) ⟨1203195, by rfl⟩ : syracuseStep 51336341 = 2406391) B2406391
theorem B1234111 : Blo 972592 1234111 := bstep (se 1 (by rfl) ⟨925583, by rfl⟩ : syracuseStep 1234111 = 1851167) B1851167
theorem B5560265 : Blo 972592 5560265 := bstep (se 2 (by rfl) ⟨2085099, by rfl⟩ : syracuseStep 5560265 = 4170199) B4170199
theorem B973295 : Blo 972592 973295 := bstep (se 1 (by rfl) ⟨729971, by rfl⟩ : syracuseStep 973295 = 1459943) B1459943
theorem B973311 : Blo 972592 973311 := bstep (se 1 (by rfl) ⟨729983, by rfl⟩ : syracuseStep 973311 = 1459967) B1459967
theorem B7887415 : Blo 972592 7887415 := bstep (se 1 (by rfl) ⟨5915561, by rfl⟩ : syracuseStep 7887415 = 11831123) B11831123
theorem B30038651 : Blo 972592 30038651 := bstep (se 1 (by rfl) ⟨22528988, by rfl⟩ : syracuseStep 30038651 = 45057977) B45057977
theorem B974695 : Blo 972592 974695 := bstep (se 1 (by rfl) ⟨731021, by rfl⟩ : syracuseStep 974695 = 1462043) B1462043
theorem B975327 : Blo 972592 975327 := bstep (se 1 (by rfl) ⟨731495, by rfl⟩ : syracuseStep 975327 = 1462991) B1462991
theorem B5268203 : Blo 972592 5268203 := bstep (se 1 (by rfl) ⟨3951152, by rfl⟩ : syracuseStep 5268203 = 7902305) B7902305
theorem B975599 : Blo 972592 975599 := bstep (se 1 (by rfl) ⟨731699, by rfl⟩ : syracuseStep 975599 = 1463399) B1463399
theorem B2188457 : Blo 972592 2188457 := bstep (se 2 (by rfl) ⟨820671, by rfl⟩ : syracuseStep 2188457 = 1641343) B1641343
theorem B2189033 : Blo 972592 2189033 := bstep (se 2 (by rfl) ⟨820887, by rfl⟩ : syracuseStep 2189033 = 1641775) B1641775
theorem B2189177 : Blo 972592 2189177 := bstep (se 2 (by rfl) ⟨820941, by rfl⟩ : syracuseStep 2189177 = 1641883) B1641883
theorem B790521767 : Blo 972592 790521767 := bstep (se 1 (by rfl) ⟨592891325, by rfl⟩ : syracuseStep 790521767 = 1185782651) B1185782651
theorem B1666079 : Blo 972592 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B9006761 : Blo 972592 9006761 := bstep (se 2 (by rfl) ⟨3377535, by rfl⟩ : syracuseStep 9006761 = 6755071) B6755071
theorem B90009539 : Blo 972592 90009539 := bstep (se 1 (by rfl) ⟨67507154, by rfl⟩ : syracuseStep 90009539 = 135014309) B135014309
theorem B160037963 : Blo 972592 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B3374291 : Blo 972592 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B8322425 : Blo 972592 8322425 := bstep (se 2 (by rfl) ⟨3120909, by rfl⟩ : syracuseStep 8322425 = 6241819) B6241819
theorem B2194847 : Blo 972592 2194847 := bstep (se 1 (by rfl) ⟨1646135, by rfl⟩ : syracuseStep 2194847 = 3292271) B3292271
theorem B3651567095 : Blo 972592 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B2195369 : Blo 972592 2195369 := bstep (se 2 (by rfl) ⟨823263, by rfl⟩ : syracuseStep 2195369 = 1646527) B1646527
theorem B2195567 : Blo 972592 2195567 := bstep (se 1 (by rfl) ⟨1646675, by rfl⟩ : syracuseStep 2195567 = 3293351) B3293351
theorem B8325089 : Blo 972592 8325089 := bstep (se 2 (by rfl) ⟨3121908, by rfl⟩ : syracuseStep 8325089 = 6243817) B6243817
theorem B3706843 : Blo 972592 3706843 := bstep (se 1 (by rfl) ⟨2780132, by rfl⟩ : syracuseStep 3706843 = 5560265) B5560265
theorem B20025767 : Blo 972592 20025767 := bstep (se 1 (by rfl) ⟨15019325, by rfl⟩ : syracuseStep 20025767 = 30038651) B30038651
theorem B42079337 : Blo 972592 42079337 := bstep (se 2 (by rfl) ⟨15779751, by rfl⟩ : syracuseStep 42079337 = 31559503) B31559503
theorem B4691321 : Blo 972592 4691321 := bstep (se 2 (by rfl) ⟨1759245, by rfl⟩ : syracuseStep 4691321 = 3518491) B3518491
theorem B3512135 : Blo 972592 3512135 := bstep (se 1 (by rfl) ⟨2634101, by rfl⟩ : syracuseStep 3512135 = 5268203) B5268203
theorem B164305073 : Blo 972592 164305073 := bstep (se 2 (by rfl) ⟨61614402, by rfl⟩ : syracuseStep 164305073 = 123228805) B123228805
theorem B3283415 : Blo 972592 3283415 := bstep (se 1 (by rfl) ⟨2462561, by rfl⟩ : syracuseStep 3283415 = 4925123) B4925123
theorem B527014511 : Blo 972592 527014511 := bstep (se 1 (by rfl) ⟨395260883, by rfl⟩ : syracuseStep 527014511 = 790521767) B790521767
theorem B1645481 : Blo 972592 1645481 := bstep (se 2 (by rfl) ⟨617055, by rfl⟩ : syracuseStep 1645481 = 1234111) B1234111
theorem B6004507 : Blo 972592 6004507 := bstep (se 1 (by rfl) ⟨4503380, by rfl⟩ : syracuseStep 6004507 = 9006761) B9006761
theorem B60006359 : Blo 972592 60006359 := bstep (se 1 (by rfl) ⟨45004769, by rfl⟩ : syracuseStep 60006359 = 90009539) B90009539
theorem B1646831 : Blo 972592 1646831 := bstep (se 1 (by rfl) ⟨1235123, by rfl⟩ : syracuseStep 1646831 = 2470247) B2470247
theorem B1647803 : Blo 972592 1647803 := bstep (se 1 (by rfl) ⟨1235852, by rfl⟩ : syracuseStep 1647803 = 2471705) B2471705
theorem B5548283 : Blo 972592 5548283 := bstep (se 1 (by rfl) ⟨4161212, by rfl⟩ : syracuseStep 5548283 = 8322425) B8322425
theorem B2434378063 : Blo 972592 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B3123947 : Blo 972592 3123947 := bstep (se 1 (by rfl) ⟨2342960, by rfl⟩ : syracuseStep 3123947 = 4685921) B4685921
theorem B2468819 : Blo 972592 2468819 := bstep (se 1 (by rfl) ⟨1851614, by rfl⟩ : syracuseStep 2468819 = 3703229) B3703229
theorem B14068889 : Blo 972592 14068889 := bstep (se 2 (by rfl) ⟨5275833, by rfl⟩ : syracuseStep 14068889 = 10551667) B10551667
theorem B5549309 : Blo 972592 5549309 := bstep (se 3 (by rfl) ⟨1040495, by rfl⟩ : syracuseStep 5549309 = 2080991) B2080991
theorem B8334899 : Blo 972592 8334899 := bstep (se 1 (by rfl) ⟨6251174, by rfl⟩ : syracuseStep 8334899 = 12502349) B12502349
theorem B2469467 : Blo 972592 2469467 := bstep (se 1 (by rfl) ⟨1852100, by rfl⟩ : syracuseStep 2469467 = 3704201) B3704201
theorem B34224227 : Blo 972592 34224227 := bstep (se 1 (by rfl) ⟨25668170, by rfl⟩ : syracuseStep 34224227 = 51336341) B51336341
theorem B1096447 : Blo 972592 1096447 := bstep (se 1 (by rfl) ⟨822335, by rfl⟩ : syracuseStep 1096447 = 1644671) B1644671
theorem B4701521 : Blo 972592 4701521 := bstep (se 2 (by rfl) ⟨1763070, by rfl⟩ : syracuseStep 4701521 = 3526141) B3526141
theorem B21053429 : Blo 972592 21053429 := bstep (se 5 (by rfl) ⟨986879, by rfl⟩ : syracuseStep 21053429 = 1973759) B1973759
theorem B1458971 : Blo 972592 1458971 := bstep (se 1 (by rfl) ⟨1094228, by rfl⟩ : syracuseStep 1458971 = 2188457) B2188457
theorem B1459355 : Blo 972592 1459355 := bstep (se 1 (by rfl) ⟨1094516, by rfl⟩ : syracuseStep 1459355 = 2189033) B2189033
theorem B1459451 : Blo 972592 1459451 := bstep (se 1 (by rfl) ⟨1094588, by rfl⟩ : syracuseStep 1459451 = 2189177) B2189177
theorem B2772137 : Blo 972592 2772137 := bstep (se 2 (by rfl) ⟨1039551, by rfl⟩ : syracuseStep 2772137 = 2079103) B2079103
theorem B2084143 : Blo 972592 2084143 := bstep (se 1 (by rfl) ⟨1563107, by rfl⟩ : syracuseStep 2084143 = 3126215) B3126215
theorem B1462505 : Blo 972592 1462505 := bstep (se 2 (by rfl) ⟨548439, by rfl⟩ : syracuseStep 1462505 = 1096879) B1096879
theorem B2249527 : Blo 972592 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B1233787 : Blo 972592 1233787 := bstep (se 1 (by rfl) ⟨925340, by rfl⟩ : syracuseStep 1233787 = 1850681) B1850681
theorem B1463231 : Blo 972592 1463231 := bstep (se 1 (by rfl) ⟨1097423, by rfl⟩ : syracuseStep 1463231 = 2194847) B2194847
theorem B25023653 : Blo 972592 25023653 := bstep (se 4 (by rfl) ⟨2345967, by rfl⟩ : syracuseStep 25023653 = 4691935) B4691935
theorem B1463579 : Blo 972592 1463579 := bstep (se 1 (by rfl) ⟨1097684, by rfl⟩ : syracuseStep 1463579 = 2195369) B2195369
theorem B1464167 : Blo 972592 1464167 := bstep (se 1 (by rfl) ⟨1098125, by rfl⟩ : syracuseStep 1464167 = 2196251) B2196251
theorem B1464527 : Blo 972592 1464527 := bstep (se 1 (by rfl) ⟨1098395, by rfl⟩ : syracuseStep 1464527 = 2196791) B2196791
theorem B974271 : Blo 972592 974271 := bstep (se 1 (by rfl) ⟨730703, by rfl⟩ : syracuseStep 974271 = 1461407) B1461407
theorem B974303 : Blo 972592 974303 := bstep (se 1 (by rfl) ⟨730727, by rfl⟩ : syracuseStep 974303 = 1461455) B1461455
theorem B974939 : Blo 972592 974939 := bstep (se 1 (by rfl) ⟨731204, by rfl⟩ : syracuseStep 974939 = 1462409) B1462409
theorem B7891175 : Blo 972592 7891175 := bstep (se 1 (by rfl) ⟨5918381, by rfl⟩ : syracuseStep 7891175 = 11836763) B11836763
theorem B2189879 : Blo 972592 2189879 := bstep (se 1 (by rfl) ⟨1642409, by rfl⟩ : syracuseStep 2189879 = 3284819) B3284819
theorem B7400321 : Blo 972592 7400321 := bstep (se 2 (by rfl) ⟨2775120, by rfl⟩ : syracuseStep 7400321 = 5550241) B5550241
theorem B2190599 : Blo 972592 2190599 := bstep (se 1 (by rfl) ⟨1642949, by rfl⟩ : syracuseStep 2190599 = 3285899) B3285899
theorem B1110719 : Blo 972592 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B2192255 : Blo 972592 2192255 := bstep (se 1 (by rfl) ⟨1644191, by rfl⟩ : syracuseStep 2192255 = 3288383) B3288383
theorem B4158377 : Blo 972592 4158377 := bstep (se 2 (by rfl) ⟨1559391, by rfl⟩ : syracuseStep 4158377 = 3118783) B3118783
theorem B12482099 : Blo 972592 12482099 := bstep (se 1 (by rfl) ⟨9361574, by rfl⟩ : syracuseStep 12482099 = 18723149) B18723149
theorem B10516553 : Blo 972592 10516553 := bstep (se 2 (by rfl) ⟨3943707, by rfl⟩ : syracuseStep 10516553 = 7887415) B7887415
theorem B106691975 : Blo 972592 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B7503263 : Blo 972592 7503263 := bstep (se 1 (by rfl) ⟨5627447, by rfl⟩ : syracuseStep 7503263 = 11254895) B11254895
theorem B17137547 : Blo 972592 17137547 := bstep (se 1 (by rfl) ⟨12853160, by rfl⟩ : syracuseStep 17137547 = 25706321) B25706321
theorem B3245837417 : Blo 972592 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B28052891 : Blo 972592 28052891 := bstep (se 1 (by rfl) ⟨21039668, by rfl⟩ : syracuseStep 28052891 = 42079337) B42079337
theorem B16682435 : Blo 972592 16682435 := bstep (se 1 (by rfl) ⟨12511826, by rfl⟩ : syracuseStep 16682435 = 25023653) B25023653
theorem B351343007 : Blo 972592 351343007 := bstep (se 1 (by rfl) ⟨263507255, by rfl⟩ : syracuseStep 351343007 = 527014511) B527014511
theorem B1645049 : Blo 972592 1645049 := bstep (se 2 (by rfl) ⟨616893, by rfl⟩ : syracuseStep 1645049 = 1233787) B1233787
theorem B8330525 : Blo 972592 8330525 := bstep (se 3 (by rfl) ⟨1561973, by rfl⟩ : syracuseStep 8330525 = 3123947) B3123947
theorem B1645879 : Blo 972592 1645879 := bstep (se 1 (by rfl) ⟨1234409, by rfl⟩ : syracuseStep 1645879 = 2468819) B2468819
theorem B9379259 : Blo 972592 9379259 := bstep (se 1 (by rfl) ⟨7034444, by rfl⟩ : syracuseStep 9379259 = 14068889) B14068889
theorem B1646311 : Blo 972592 1646311 := bstep (se 1 (by rfl) ⟨1234733, by rfl⟩ : syracuseStep 1646311 = 2469467) B2469467
theorem B22816151 : Blo 972592 22816151 := bstep (se 1 (by rfl) ⟨17112113, by rfl⟩ : syracuseStep 22816151 = 34224227) B34224227
theorem B8006009 : Blo 972592 8006009 := bstep (se 2 (by rfl) ⟨3002253, by rfl⟩ : syracuseStep 8006009 = 6004507) B6004507
theorem B14035619 : Blo 972592 14035619 := bstep (se 1 (by rfl) ⟨10526714, by rfl⟩ : syracuseStep 14035619 = 21053429) B21053429
theorem B5550059 : Blo 972592 5550059 := bstep (se 1 (by rfl) ⟨4162544, by rfl⟩ : syracuseStep 5550059 = 8325089) B8325089
theorem B2961917 : Blo 972592 2961917 := bstep (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) B1110719
theorem B1848091 : Blo 972592 1848091 := bstep (se 1 (by rfl) ⟨1386068, by rfl⟩ : syracuseStep 1848091 = 2772137) B2772137
theorem B13350511 : Blo 972592 13350511 := bstep (se 1 (by rfl) ⟨10012883, by rfl⟩ : syracuseStep 13350511 = 20025767) B20025767
theorem B3127547 : Blo 972592 3127547 := bstep (se 1 (by rfl) ⟨2345660, by rfl⟩ : syracuseStep 3127547 = 4691321) B4691321
theorem B2341423 : Blo 972592 2341423 := bstep (se 1 (by rfl) ⟨1756067, by rfl⟩ : syracuseStep 2341423 = 3512135) B3512135
theorem B1096987 : Blo 972592 1096987 := bstep (se 1 (by rfl) ⟨822740, by rfl⟩ : syracuseStep 1096987 = 1645481) B1645481
theorem B1097887 : Blo 972592 1097887 := bstep (se 1 (by rfl) ⟨823415, by rfl⟩ : syracuseStep 1097887 = 1646831) B1646831
theorem B1098535 : Blo 972592 1098535 := bstep (se 1 (by rfl) ⟨823901, by rfl⟩ : syracuseStep 1098535 = 1647803) B1647803
theorem B2999369 : Blo 972592 2999369 := bstep (se 2 (by rfl) ⟨1124763, by rfl⟩ : syracuseStep 2999369 = 2249527) B2249527
theorem B5260783 : Blo 972592 5260783 := bstep (se 1 (by rfl) ⟨3945587, by rfl⟩ : syracuseStep 5260783 = 7891175) B7891175
theorem B1459919 : Blo 972592 1459919 := bstep (se 1 (by rfl) ⟨1094939, by rfl⟩ : syracuseStep 1459919 = 2189879) B2189879
theorem B4933547 : Blo 972592 4933547 := bstep (se 1 (by rfl) ⟨3700160, by rfl⟩ : syracuseStep 4933547 = 7400321) B7400321
theorem B1460399 : Blo 972592 1460399 := bstep (se 1 (by rfl) ⟨1095299, by rfl⟩ : syracuseStep 1460399 = 2190599) B2190599
theorem B5556599 : Blo 972592 5556599 := bstep (se 1 (by rfl) ⟨4167449, by rfl⟩ : syracuseStep 5556599 = 8334899) B8334899
theorem B1461503 : Blo 972592 1461503 := bstep (se 1 (by rfl) ⟨1096127, by rfl⟩ : syracuseStep 1461503 = 2192255) B2192255
theorem B2772251 : Blo 972592 2772251 := bstep (se 1 (by rfl) ⟨2079188, by rfl⟩ : syracuseStep 2772251 = 4158377) B4158377
theorem B12537389 : Blo 972592 12537389 := bstep (se 3 (by rfl) ⟨2350760, by rfl⟩ : syracuseStep 12537389 = 4701521) B4701521
theorem B1461929 : Blo 972592 1461929 := bstep (se 2 (by rfl) ⟨548223, by rfl⟩ : syracuseStep 1461929 = 1096447) B1096447
theorem B71127983 : Blo 972592 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B5002175 : Blo 972592 5002175 := bstep (se 1 (by rfl) ⟨3751631, by rfl⟩ : syracuseStep 5002175 = 7503263) B7503263
theorem B11425031 : Blo 972592 11425031 := bstep (se 1 (by rfl) ⟨8568773, by rfl⟩ : syracuseStep 11425031 = 17137547) B17137547
theorem B1463711 : Blo 972592 1463711 := bstep (se 1 (by rfl) ⟨1097783, by rfl⟩ : syracuseStep 1463711 = 2195567) B2195567
theorem B972647 : Blo 972592 972647 := bstep (se 1 (by rfl) ⟨729485, by rfl⟩ : syracuseStep 972647 = 1458971) B1458971
theorem B972903 : Blo 972592 972903 := bstep (se 1 (by rfl) ⟨729677, by rfl⟩ : syracuseStep 972903 = 1459355) B1459355
theorem B972967 : Blo 972592 972967 := bstep (se 1 (by rfl) ⟨729725, by rfl⟩ : syracuseStep 972967 = 1459451) B1459451
theorem B975003 : Blo 972592 975003 := bstep (se 1 (by rfl) ⟨731252, by rfl⟩ : syracuseStep 975003 = 1462505) B1462505
theorem B975487 : Blo 972592 975487 := bstep (se 1 (by rfl) ⟨731615, by rfl⟩ : syracuseStep 975487 = 1463231) B1463231
theorem B975719 : Blo 972592 975719 := bstep (se 1 (by rfl) ⟨731789, by rfl⟩ : syracuseStep 975719 = 1463579) B1463579
theorem B976111 : Blo 972592 976111 := bstep (se 1 (by rfl) ⟨732083, by rfl⟩ : syracuseStep 976111 = 1464167) B1464167
theorem B109536715 : Blo 972592 109536715 := bstep (se 1 (by rfl) ⟨82152536, by rfl⟩ : syracuseStep 109536715 = 164305073) B164305073
theorem B976351 : Blo 972592 976351 := bstep (se 1 (by rfl) ⟨732263, by rfl⟩ : syracuseStep 976351 = 1464527) B1464527
theorem B2188943 : Blo 972592 2188943 := bstep (se 1 (by rfl) ⟨1641707, by rfl⟩ : syracuseStep 2188943 = 3283415) B3283415
theorem B2778857 : Blo 972592 2778857 := bstep (se 2 (by rfl) ⟨1042071, by rfl⟩ : syracuseStep 2778857 = 2084143) B2084143
theorem B4942457 : Blo 972592 4942457 := bstep (se 2 (by rfl) ⟨1853421, by rfl⟩ : syracuseStep 4942457 = 3706843) B3706843
theorem B40004239 : Blo 972592 40004239 := bstep (se 1 (by rfl) ⟨30003179, by rfl⟩ : syracuseStep 40004239 = 60006359) B60006359
theorem B3698855 : Blo 972592 3698855 := bstep (se 1 (by rfl) ⟨2774141, by rfl⟩ : syracuseStep 3698855 = 5548283) B5548283
theorem B3699539 : Blo 972592 3699539 := bstep (se 1 (by rfl) ⟨2774654, by rfl⟩ : syracuseStep 3699539 = 5549309) B5549309
theorem B8321399 : Blo 972592 8321399 := bstep (se 1 (by rfl) ⟨6241049, by rfl⟩ : syracuseStep 8321399 = 12482099) B12482099
theorem B7011035 : Blo 972592 7011035 := bstep (se 1 (by rfl) ⟨5258276, by rfl⟩ : syracuseStep 7011035 = 10516553) B10516553
theorem B1999579 : Blo 972592 1999579 := bstep (se 1 (by rfl) ⟨1499684, by rfl⟩ : syracuseStep 1999579 = 2999369) B2999369
theorem B3704399 : Blo 972592 3704399 := bstep (se 1 (by rfl) ⟨2778299, by rfl⟩ : syracuseStep 3704399 = 5556599) B5556599
theorem B146048953 : Blo 972592 146048953 := bstep (se 2 (by rfl) ⟨54768357, by rfl⟩ : syracuseStep 146048953 = 109536715) B109536715
theorem B7014377 : Blo 972592 7014377 := bstep (se 2 (by rfl) ⟨2630391, by rfl⟩ : syracuseStep 7014377 = 5260783) B5260783
theorem B234228671 : Blo 972592 234228671 := bstep (se 1 (by rfl) ⟨175671503, by rfl⟩ : syracuseStep 234228671 = 351343007) B351343007
theorem B47418655 : Blo 972592 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B85397429 : Blo 972592 85397429 := bstep (se 5 (by rfl) ⟨4003004, by rfl⟩ : syracuseStep 85397429 = 8006009) B8006009
theorem B15210767 : Blo 972592 15210767 := bstep (se 1 (by rfl) ⟨11408075, by rfl⟩ : syracuseStep 15210767 = 22816151) B22816151
theorem B2464121 : Blo 972592 2464121 := bstep (se 2 (by rfl) ⟨924045, by rfl⟩ : syracuseStep 2464121 = 1848091) B1848091
theorem B17800681 : Blo 972592 17800681 := bstep (se 2 (by rfl) ⟨6675255, by rfl⟩ : syracuseStep 17800681 = 13350511) B13350511
theorem B2465903 : Blo 972592 2465903 := bstep (se 1 (by rfl) ⟨1849427, by rfl⟩ : syracuseStep 2465903 = 3698855) B3698855
theorem B1974611 : Blo 972592 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B2466359 : Blo 972592 2466359 := bstep (se 1 (by rfl) ⟨1849769, by rfl⟩ : syracuseStep 2466359 = 3699539) B3699539
theorem B3121897 : Blo 972592 3121897 := bstep (se 2 (by rfl) ⟨1170711, by rfl⟩ : syracuseStep 3121897 = 2341423) B2341423
theorem B33433037 : Blo 972592 33433037 := bstep (se 3 (by rfl) ⟨6268694, by rfl⟩ : syracuseStep 33433037 = 12537389) B12537389
theorem B5547599 : Blo 972592 5547599 := bstep (se 1 (by rfl) ⟨4160699, by rfl⟩ : syracuseStep 5547599 = 8321399) B8321399
theorem B3289031 : Blo 972592 3289031 := bstep (se 1 (by rfl) ⟨2466773, by rfl⟩ : syracuseStep 3289031 = 4933547) B4933547
theorem B1848167 : Blo 972592 1848167 := bstep (se 1 (by rfl) ⟨1386125, by rfl⟩ : syracuseStep 1848167 = 2772251) B2772251
theorem B11121623 : Blo 972592 11121623 := bstep (se 1 (by rfl) ⟨8341217, by rfl⟩ : syracuseStep 11121623 = 16682435) B16682435
theorem B7616687 : Blo 972592 7616687 := bstep (se 1 (by rfl) ⟨5712515, by rfl⟩ : syracuseStep 7616687 = 11425031) B11425031
theorem B1096699 : Blo 972592 1096699 := bstep (se 1 (by rfl) ⟨822524, by rfl⟩ : syracuseStep 1096699 = 1645049) B1645049
theorem B5553683 : Blo 972592 5553683 := bstep (se 1 (by rfl) ⟨4165262, by rfl⟩ : syracuseStep 5553683 = 8330525) B8330525
theorem B1459295 : Blo 972592 1459295 := bstep (se 1 (by rfl) ⟨1094471, by rfl⟩ : syracuseStep 1459295 = 2188943) B2188943
theorem B1852571 : Blo 972592 1852571 := bstep (se 1 (by rfl) ⟨1389428, by rfl⟩ : syracuseStep 1852571 = 2778857) B2778857
theorem B3294971 : Blo 972592 3294971 := bstep (se 1 (by rfl) ⟨2471228, by rfl⟩ : syracuseStep 3294971 = 4942457) B4942457
theorem B9357079 : Blo 972592 9357079 := bstep (se 1 (by rfl) ⟨7017809, by rfl⟩ : syracuseStep 9357079 = 14035619) B14035619
theorem B2085031 : Blo 972592 2085031 := bstep (se 1 (by rfl) ⟨1563773, by rfl⟩ : syracuseStep 2085031 = 3127547) B3127547
theorem B1462649 : Blo 972592 1462649 := bstep (se 2 (by rfl) ⟨548493, by rfl⟩ : syracuseStep 1462649 = 1096987) B1096987
theorem B4674023 : Blo 972592 4674023 := bstep (se 1 (by rfl) ⟨3505517, by rfl⟩ : syracuseStep 4674023 = 7011035) B7011035
theorem B1463849 : Blo 972592 1463849 := bstep (se 2 (by rfl) ⟨548943, by rfl⟩ : syracuseStep 1463849 = 1097887) B1097887
theorem B1464713 : Blo 972592 1464713 := bstep (se 2 (by rfl) ⟨549267, by rfl⟩ : syracuseStep 1464713 = 1098535) B1098535
theorem B973279 : Blo 972592 973279 := bstep (se 1 (by rfl) ⟨729959, by rfl⟩ : syracuseStep 973279 = 1459919) B1459919
theorem B973599 : Blo 972592 973599 := bstep (se 1 (by rfl) ⟨730199, by rfl⟩ : syracuseStep 973599 = 1460399) B1460399
theorem B2163891611 : Blo 972592 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B974335 : Blo 972592 974335 := bstep (se 1 (by rfl) ⟨730751, by rfl⟩ : syracuseStep 974335 = 1461503) B1461503
theorem B18701927 : Blo 972592 18701927 := bstep (se 1 (by rfl) ⟨14026445, by rfl⟩ : syracuseStep 18701927 = 28052891) B28052891
theorem B974619 : Blo 972592 974619 := bstep (se 1 (by rfl) ⟨730964, by rfl⟩ : syracuseStep 974619 = 1461929) B1461929
theorem B3334783 : Blo 972592 3334783 := bstep (se 1 (by rfl) ⟨2501087, by rfl⟩ : syracuseStep 3334783 = 5002175) B5002175
theorem B53338985 : Blo 972592 53338985 := bstep (se 2 (by rfl) ⟨20002119, by rfl⟩ : syracuseStep 53338985 = 40004239) B40004239
theorem B975807 : Blo 972592 975807 := bstep (se 1 (by rfl) ⟨731855, by rfl⟩ : syracuseStep 975807 = 1463711) B1463711
theorem B6252839 : Blo 972592 6252839 := bstep (se 1 (by rfl) ⟨4689629, by rfl⟩ : syracuseStep 6252839 = 9379259) B9379259
theorem B3700039 : Blo 972592 3700039 := bstep (se 1 (by rfl) ⟨2775029, by rfl⟩ : syracuseStep 3700039 = 5550059) B5550059
theorem B2194505 : Blo 972592 2194505 := bstep (se 2 (by rfl) ⟨822939, by rfl⟩ : syracuseStep 2194505 = 1645879) B1645879
theorem B2195081 : Blo 972592 2195081 := bstep (se 2 (by rfl) ⟨823155, by rfl⟩ : syracuseStep 2195081 = 1646311) B1646311
theorem B4162529 : Blo 972592 4162529 := bstep (se 2 (by rfl) ⟨1560948, by rfl⟩ : syracuseStep 4162529 = 3121897) B3121897
theorem B2196647 : Blo 972592 2196647 := bstep (se 1 (by rfl) ⟨1647485, by rfl⟩ : syracuseStep 2196647 = 3294971) B3294971
theorem B3116015 : Blo 972592 3116015 := bstep (se 1 (by rfl) ⟨2337011, by rfl⟩ : syracuseStep 3116015 = 4674023) B4674023
theorem B1642747 : Blo 972592 1642747 := bstep (se 1 (by rfl) ⟨1232060, by rfl⟩ : syracuseStep 1642747 = 2464121) B2464121
theorem B1643935 : Blo 972592 1643935 := bstep (se 1 (by rfl) ⟨1232951, by rfl⟩ : syracuseStep 1643935 = 2465903) B2465903
theorem B1316407 : Blo 972592 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B1644239 : Blo 972592 1644239 := bstep (se 1 (by rfl) ⟨1233179, by rfl⟩ : syracuseStep 1644239 = 2466359) B2466359
theorem B35559323 : Blo 972592 35559323 := bstep (se 1 (by rfl) ⟨26669492, by rfl⟩ : syracuseStep 35559323 = 53338985) B53338985
theorem B22288691 : Blo 972592 22288691 := bstep (se 1 (by rfl) ⟨16716518, by rfl⟩ : syracuseStep 22288691 = 33433037) B33433037
theorem B4168559 : Blo 972592 4168559 := bstep (se 1 (by rfl) ⟨3126419, by rfl⟩ : syracuseStep 4168559 = 6252839) B6252839
theorem B7414415 : Blo 972592 7414415 := bstep (se 1 (by rfl) ⟨5560811, by rfl⟩ : syracuseStep 7414415 = 11121623) B11121623
theorem B23734241 : Blo 972592 23734241 := bstep (se 2 (by rfl) ⟨8900340, by rfl⟩ : syracuseStep 23734241 = 17800681) B17800681
theorem B11120165 : Blo 972592 11120165 := bstep (se 4 (by rfl) ⟨1042515, by rfl⟩ : syracuseStep 11120165 = 2085031) B2085031
theorem B2666105 : Blo 972592 2666105 := bstep (se 2 (by rfl) ⟨999789, by rfl⟩ : syracuseStep 2666105 = 1999579) B1999579
theorem B2469599 : Blo 972592 2469599 := bstep (se 1 (by rfl) ⟨1852199, by rfl⟩ : syracuseStep 2469599 = 3704399) B3704399
theorem B156152447 : Blo 972592 156152447 := bstep (se 1 (by rfl) ⟨117114335, by rfl⟩ : syracuseStep 156152447 = 234228671) B234228671
theorem B56931619 : Blo 972592 56931619 := bstep (se 1 (by rfl) ⟨42698714, by rfl⟩ : syracuseStep 56931619 = 85397429) B85397429
theorem B63224873 : Blo 972592 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B1442594407 : Blo 972592 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B12467951 : Blo 972592 12467951 := bstep (se 1 (by rfl) ⟨9350963, by rfl⟩ : syracuseStep 12467951 = 18701927) B18701927
theorem B4933385 : Blo 972592 4933385 := bstep (se 2 (by rfl) ⟨1850019, by rfl⟩ : syracuseStep 4933385 = 3700039) B3700039
theorem B1232111 : Blo 972592 1232111 := bstep (se 1 (by rfl) ⟨924083, by rfl⟩ : syracuseStep 1232111 = 1848167) B1848167
theorem B1462265 : Blo 972592 1462265 := bstep (se 2 (by rfl) ⟨548349, by rfl⟩ : syracuseStep 1462265 = 1096699) B1096699
theorem B1463003 : Blo 972592 1463003 := bstep (se 1 (by rfl) ⟨1097252, by rfl⟩ : syracuseStep 1463003 = 2194505) B2194505
theorem B1463387 : Blo 972592 1463387 := bstep (se 1 (by rfl) ⟨1097540, by rfl⟩ : syracuseStep 1463387 = 2195081) B2195081
theorem B972863 : Blo 972592 972863 := bstep (se 1 (by rfl) ⟨729647, by rfl⟩ : syracuseStep 972863 = 1459295) B1459295
theorem B4446377 : Blo 972592 4446377 := bstep (se 2 (by rfl) ⟨1667391, by rfl⟩ : syracuseStep 4446377 = 3334783) B3334783
theorem B4676251 : Blo 972592 4676251 := bstep (se 1 (by rfl) ⟨3507188, by rfl⟩ : syracuseStep 4676251 = 7014377) B7014377
theorem B12476105 : Blo 972592 12476105 := bstep (se 2 (by rfl) ⟨4678539, by rfl⟩ : syracuseStep 12476105 = 9357079) B9357079
theorem B194731937 : Blo 972592 194731937 := bstep (se 2 (by rfl) ⟨73024476, by rfl⟩ : syracuseStep 194731937 = 146048953) B146048953
theorem B975099 : Blo 972592 975099 := bstep (se 1 (by rfl) ⟨731324, by rfl⟩ : syracuseStep 975099 = 1462649) B1462649
theorem B4940189 : Blo 972592 4940189 := bstep (se 3 (by rfl) ⟨926285, by rfl⟩ : syracuseStep 4940189 = 1852571) B1852571
theorem B975899 : Blo 972592 975899 := bstep (se 1 (by rfl) ⟨731924, by rfl⟩ : syracuseStep 975899 = 1463849) B1463849
theorem B976475 : Blo 972592 976475 := bstep (se 1 (by rfl) ⟨732356, by rfl⟩ : syracuseStep 976475 = 1464713) B1464713
theorem B20311165 : Blo 972592 20311165 := bstep (se 3 (by rfl) ⟨3808343, by rfl⟩ : syracuseStep 20311165 = 7616687) B7616687
theorem B40562045 : Blo 972592 40562045 := bstep (se 3 (by rfl) ⟨7605383, by rfl⟩ : syracuseStep 40562045 = 15210767) B15210767
theorem B3698399 : Blo 972592 3698399 := bstep (se 1 (by rfl) ⟨2773799, by rfl⟩ : syracuseStep 3698399 = 5547599) B5547599
theorem B2192687 : Blo 972592 2192687 := bstep (se 1 (by rfl) ⟨1644515, by rfl⟩ : syracuseStep 2192687 = 3289031) B3289031
theorem B3702455 : Blo 972592 3702455 := bstep (se 1 (by rfl) ⟨2776841, by rfl⟩ : syracuseStep 3702455 = 5553683) B5553683
theorem B27041363 : Blo 972592 27041363 := bstep (se 1 (by rfl) ⟨20281022, by rfl⟩ : syracuseStep 27041363 = 40562045) B40562045
theorem B7413443 : Blo 972592 7413443 := bstep (se 1 (by rfl) ⟨5560082, by rfl⟩ : syracuseStep 7413443 = 11120165) B11120165
theorem B1777403 : Blo 972592 1777403 := bstep (se 1 (by rfl) ⟨1333052, by rfl⟩ : syracuseStep 1777403 = 2666105) B2666105
theorem B2465599 : Blo 972592 2465599 := bstep (se 1 (by rfl) ⟨1849199, by rfl⟩ : syracuseStep 2465599 = 3698399) B3698399
theorem B1646399 : Blo 972592 1646399 := bstep (se 1 (by rfl) ⟨1234799, by rfl⟩ : syracuseStep 1646399 = 2469599) B2469599
theorem B3285629 : Blo 972592 3285629 := bstep (se 3 (by rfl) ⟨616055, by rfl⟩ : syracuseStep 3285629 = 1232111) B1232111
theorem B6235001 : Blo 972592 6235001 := bstep (se 2 (by rfl) ⟨2338125, by rfl⟩ : syracuseStep 6235001 = 4676251) B4676251
theorem B42149915 : Blo 972592 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B1923459209 : Blo 972592 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B2468303 : Blo 972592 2468303 := bstep (se 1 (by rfl) ⟨1851227, by rfl⟩ : syracuseStep 2468303 = 3702455) B3702455
theorem B3288923 : Blo 972592 3288923 := bstep (se 1 (by rfl) ⟨2466692, by rfl⟩ : syracuseStep 3288923 = 4933385) B4933385
theorem B2077343 : Blo 972592 2077343 := bstep (se 1 (by rfl) ⟨1558007, by rfl⟩ : syracuseStep 2077343 = 3116015) B3116015
theorem B1096159 : Blo 972592 1096159 := bstep (se 1 (by rfl) ⟨822119, by rfl⟩ : syracuseStep 1096159 = 1644239) B1644239
theorem B23706215 : Blo 972592 23706215 := bstep (se 1 (by rfl) ⟨17779661, by rfl⟩ : syracuseStep 23706215 = 35559323) B35559323
theorem B2964251 : Blo 972592 2964251 := bstep (se 1 (by rfl) ⟨2223188, by rfl⟩ : syracuseStep 2964251 = 4446377) B4446377
theorem B27081553 : Blo 972592 27081553 := bstep (se 2 (by rfl) ⟨10155582, by rfl⟩ : syracuseStep 27081553 = 20311165) B20311165
theorem B3293459 : Blo 972592 3293459 := bstep (se 1 (by rfl) ⟨2470094, by rfl⟩ : syracuseStep 3293459 = 4940189) B4940189
theorem B75908825 : Blo 972592 75908825 := bstep (se 2 (by rfl) ⟨28465809, by rfl⟩ : syracuseStep 75908825 = 56931619) B56931619
theorem B1755209 : Blo 972592 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B1461791 : Blo 972592 1461791 := bstep (se 1 (by rfl) ⟨1096343, by rfl⟩ : syracuseStep 1461791 = 2192687) B2192687
theorem B8311967 : Blo 972592 8311967 := bstep (se 1 (by rfl) ⟨6233975, by rfl⟩ : syracuseStep 8311967 = 12467951) B12467951
theorem B2775019 : Blo 972592 2775019 := bstep (se 1 (by rfl) ⟨2081264, by rfl⟩ : syracuseStep 2775019 = 4162529) B4162529
theorem B1464431 : Blo 972592 1464431 := bstep (se 1 (by rfl) ⟨1098323, by rfl⟩ : syracuseStep 1464431 = 2196647) B2196647
theorem B974843 : Blo 972592 974843 := bstep (se 1 (by rfl) ⟨731132, by rfl⟩ : syracuseStep 974843 = 1462265) B1462265
theorem B975335 : Blo 972592 975335 := bstep (se 1 (by rfl) ⟨731501, by rfl⟩ : syracuseStep 975335 = 1463003) B1463003
theorem B975591 : Blo 972592 975591 := bstep (se 1 (by rfl) ⟨731693, by rfl⟩ : syracuseStep 975591 = 1463387) B1463387
theorem B2779039 : Blo 972592 2779039 := bstep (se 1 (by rfl) ⟨2084279, by rfl⟩ : syracuseStep 2779039 = 4168559) B4168559
theorem B8317403 : Blo 972592 8317403 := bstep (se 1 (by rfl) ⟨6238052, by rfl⟩ : syracuseStep 8317403 = 12476105) B12476105
theorem B129821291 : Blo 972592 129821291 := bstep (se 1 (by rfl) ⟨97365968, by rfl⟩ : syracuseStep 129821291 = 194731937) B194731937
theorem B2190329 : Blo 972592 2190329 := bstep (se 2 (by rfl) ⟨821373, by rfl⟩ : syracuseStep 2190329 = 1642747) B1642747
theorem B4942943 : Blo 972592 4942943 := bstep (se 1 (by rfl) ⟨3707207, by rfl⟩ : syracuseStep 4942943 = 7414415) B7414415
theorem B59436509 : Blo 972592 59436509 := bstep (se 3 (by rfl) ⟨11144345, by rfl⟩ : syracuseStep 59436509 = 22288691) B22288691
theorem B15822827 : Blo 972592 15822827 := bstep (se 1 (by rfl) ⟨11867120, by rfl⟩ : syracuseStep 15822827 = 23734241) B23734241
theorem B2191913 : Blo 972592 2191913 := bstep (se 2 (by rfl) ⟨821967, by rfl⟩ : syracuseStep 2191913 = 1643935) B1643935
theorem B104101631 : Blo 972592 104101631 := bstep (se 1 (by rfl) ⟨78076223, by rfl⟩ : syracuseStep 104101631 = 156152447) B156152447
theorem B2195639 : Blo 972592 2195639 := bstep (se 1 (by rfl) ⟨1646729, by rfl⟩ : syracuseStep 2195639 = 3293459) B3293459
theorem B3705385 : Blo 972592 3705385 := bstep (se 2 (by rfl) ⟨1389519, by rfl⟩ : syracuseStep 3705385 = 2779039) B2779039
theorem B5541311 : Blo 972592 5541311 := bstep (se 1 (by rfl) ⟨4155983, by rfl⟩ : syracuseStep 5541311 = 8311967) B8311967
theorem B18027575 : Blo 972592 18027575 := bstep (se 1 (by rfl) ⟨13520681, by rfl⟩ : syracuseStep 18027575 = 27041363) B27041363
theorem B1645535 : Blo 972592 1645535 := bstep (se 1 (by rfl) ⟨1234151, by rfl⟩ : syracuseStep 1645535 = 2468303) B2468303
theorem B5544935 : Blo 972592 5544935 := bstep (se 1 (by rfl) ⟨4158701, by rfl⟩ : syracuseStep 5544935 = 8317403) B8317403
theorem B86547527 : Blo 972592 86547527 := bstep (se 1 (by rfl) ⟨64910645, by rfl⟩ : syracuseStep 86547527 = 129821291) B129821291
theorem B1384895 : Blo 972592 1384895 := bstep (se 1 (by rfl) ⟨1038671, by rfl⟩ : syracuseStep 1384895 = 2077343) B2077343
theorem B15804143 : Blo 972592 15804143 := bstep (se 1 (by rfl) ⟨11853107, by rfl⟩ : syracuseStep 15804143 = 23706215) B23706215
theorem B1976167 : Blo 972592 1976167 := bstep (se 1 (by rfl) ⟨1482125, by rfl⟩ : syracuseStep 1976167 = 2964251) B2964251
theorem B3287465 : Blo 972592 3287465 := bstep (se 2 (by rfl) ⟨1232799, by rfl⟩ : syracuseStep 3287465 = 2465599) B2465599
theorem B50605883 : Blo 972592 50605883 := bstep (se 1 (by rfl) ⟨37954412, by rfl⟩ : syracuseStep 50605883 = 75908825) B75908825
theorem B1097599 : Blo 972592 1097599 := bstep (se 1 (by rfl) ⟨823199, by rfl⟩ : syracuseStep 1097599 = 1646399) B1646399
theorem B28099943 : Blo 972592 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B1460219 : Blo 972592 1460219 := bstep (se 1 (by rfl) ⟨1095164, by rfl⟩ : syracuseStep 1460219 = 2190329) B2190329
theorem B3295295 : Blo 972592 3295295 := bstep (se 1 (by rfl) ⟨2471471, by rfl⟩ : syracuseStep 3295295 = 4942943) B4942943
theorem B1461275 : Blo 972592 1461275 := bstep (se 1 (by rfl) ⟨1095956, by rfl⟩ : syracuseStep 1461275 = 2191913) B2191913
theorem B1461545 : Blo 972592 1461545 := bstep (se 2 (by rfl) ⟨548079, by rfl⟩ : syracuseStep 1461545 = 1096159) B1096159
theorem B4739741 : Blo 972592 4739741 := bstep (se 3 (by rfl) ⟨888701, by rfl⟩ : syracuseStep 4739741 = 1777403) B1777403
theorem B974527 : Blo 972592 974527 := bstep (se 1 (by rfl) ⟨730895, by rfl⟩ : syracuseStep 974527 = 1461791) B1461791
theorem B976287 : Blo 972592 976287 := bstep (se 1 (by rfl) ⟨732215, by rfl⟩ : syracuseStep 976287 = 1464431) B1464431
theorem B4942295 : Blo 972592 4942295 := bstep (se 1 (by rfl) ⟨3706721, by rfl⟩ : syracuseStep 4942295 = 7413443) B7413443
theorem B4680557 : Blo 972592 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B2190419 : Blo 972592 2190419 := bstep (se 1 (by rfl) ⟨1642814, by rfl⟩ : syracuseStep 2190419 = 3285629) B3285629
theorem B4156667 : Blo 972592 4156667 := bstep (se 1 (by rfl) ⟨3117500, by rfl⟩ : syracuseStep 4156667 = 6235001) B6235001
theorem B1282306139 : Blo 972592 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B2192615 : Blo 972592 2192615 := bstep (se 1 (by rfl) ⟨1644461, by rfl⟩ : syracuseStep 2192615 = 3288923) B3288923
theorem B3700025 : Blo 972592 3700025 := bstep (se 2 (by rfl) ⟨1387509, by rfl⟩ : syracuseStep 3700025 = 2775019) B2775019
theorem B10548551 : Blo 972592 10548551 := bstep (se 1 (by rfl) ⟨7911413, by rfl⟩ : syracuseStep 10548551 = 15822827) B15822827
theorem B36108737 : Blo 972592 36108737 := bstep (se 2 (by rfl) ⟨13540776, by rfl⟩ : syracuseStep 36108737 = 27081553) B27081553
theorem B69401087 : Blo 972592 69401087 := bstep (se 1 (by rfl) ⟨52050815, by rfl⟩ : syracuseStep 69401087 = 104101631) B104101631
theorem B158497357 : Blo 972592 158497357 := bstep (se 3 (by rfl) ⟨29718254, by rfl⟩ : syracuseStep 158497357 = 59436509) B59436509
theorem B2196863 : Blo 972592 2196863 := bstep (se 1 (by rfl) ⟨1647647, by rfl⟩ : syracuseStep 2196863 = 3295295) B3295295
theorem B3120371 : Blo 972592 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B211329809 : Blo 972592 211329809 := bstep (se 2 (by rfl) ⟨79248678, by rfl⟩ : syracuseStep 211329809 = 158497357) B158497357
theorem B2466683 : Blo 972592 2466683 := bstep (se 1 (by rfl) ⟨1850012, by rfl⟩ : syracuseStep 2466683 = 3700025) B3700025
theorem B3159827 : Blo 972592 3159827 := bstep (se 1 (by rfl) ⟨2369870, by rfl⟩ : syracuseStep 3159827 = 4739741) B4739741
theorem B1097023 : Blo 972592 1097023 := bstep (se 1 (by rfl) ⟨822767, by rfl⟩ : syracuseStep 1097023 = 1645535) B1645535
theorem B10536095 : Blo 972592 10536095 := bstep (se 1 (by rfl) ⟨7902071, by rfl⟩ : syracuseStep 10536095 = 15804143) B15804143
theorem B3294863 : Blo 972592 3294863 := bstep (se 1 (by rfl) ⟨2471147, by rfl⟩ : syracuseStep 3294863 = 4942295) B4942295
theorem B1460279 : Blo 972592 1460279 := bstep (se 1 (by rfl) ⟨1095209, by rfl⟩ : syracuseStep 1460279 = 2190419) B2190419
theorem B2771111 : Blo 972592 2771111 := bstep (se 1 (by rfl) ⟨2078333, by rfl⟩ : syracuseStep 2771111 = 4156667) B4156667
theorem B33737255 : Blo 972592 33737255 := bstep (se 1 (by rfl) ⟨25302941, by rfl⟩ : syracuseStep 33737255 = 50605883) B50605883
theorem B854870759 : Blo 972592 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B1461743 : Blo 972592 1461743 := bstep (se 1 (by rfl) ⟨1096307, by rfl⟩ : syracuseStep 1461743 = 2192615) B2192615
theorem B7032367 : Blo 972592 7032367 := bstep (se 1 (by rfl) ⟨5274275, by rfl⟩ : syracuseStep 7032367 = 10548551) B10548551
theorem B24072491 : Blo 972592 24072491 := bstep (se 1 (by rfl) ⟨18054368, by rfl⟩ : syracuseStep 24072491 = 36108737) B36108737
theorem B10539557 : Blo 972592 10539557 := bstep (se 4 (by rfl) ⟨988083, by rfl⟩ : syracuseStep 10539557 = 1976167) B1976167
theorem B1463465 : Blo 972592 1463465 := bstep (se 2 (by rfl) ⟨548799, by rfl⟩ : syracuseStep 1463465 = 1097599) B1097599
theorem B1463759 : Blo 972592 1463759 := bstep (se 1 (by rfl) ⟨1097819, by rfl⟩ : syracuseStep 1463759 = 2195639) B2195639
theorem B18733295 : Blo 972592 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B3693053 : Blo 972592 3693053 := bstep (se 3 (by rfl) ⟨692447, by rfl⟩ : syracuseStep 3693053 = 1384895) B1384895
theorem B973479 : Blo 972592 973479 := bstep (se 1 (by rfl) ⟨730109, by rfl⟩ : syracuseStep 973479 = 1460219) B1460219
theorem B974183 : Blo 972592 974183 := bstep (se 1 (by rfl) ⟨730637, by rfl⟩ : syracuseStep 974183 = 1461275) B1461275
theorem B974363 : Blo 972592 974363 := bstep (se 1 (by rfl) ⟨730772, by rfl⟩ : syracuseStep 974363 = 1461545) B1461545
theorem B3694207 : Blo 972592 3694207 := bstep (se 1 (by rfl) ⟨2770655, by rfl⟩ : syracuseStep 3694207 = 5541311) B5541311
theorem B12018383 : Blo 972592 12018383 := bstep (se 1 (by rfl) ⟨9013787, by rfl⟩ : syracuseStep 12018383 = 18027575) B18027575
theorem B4940513 : Blo 972592 4940513 := bstep (se 2 (by rfl) ⟨1852692, by rfl⟩ : syracuseStep 4940513 = 3705385) B3705385
theorem B3696623 : Blo 972592 3696623 := bstep (se 1 (by rfl) ⟨2772467, by rfl⟩ : syracuseStep 3696623 = 5544935) B5544935
theorem B57698351 : Blo 972592 57698351 := bstep (se 1 (by rfl) ⟨43273763, by rfl⟩ : syracuseStep 57698351 = 86547527) B86547527
theorem B2191643 : Blo 972592 2191643 := bstep (se 1 (by rfl) ⟨1643732, by rfl⟩ : syracuseStep 2191643 = 3287465) B3287465
theorem B46267391 : Blo 972592 46267391 := bstep (se 1 (by rfl) ⟨34700543, by rfl⟩ : syracuseStep 46267391 = 69401087) B69401087
theorem B2196575 : Blo 972592 2196575 := bstep (se 1 (by rfl) ⟨1647431, by rfl⟩ : syracuseStep 2196575 = 3294863) B3294863
theorem B12488863 : Blo 972592 12488863 := bstep (se 1 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 12488863 = 18733295) B18733295
theorem B2462035 : Blo 972592 2462035 := bstep (se 1 (by rfl) ⟨1846526, by rfl⟩ : syracuseStep 2462035 = 3693053) B3693053
theorem B9376489 : Blo 972592 9376489 := bstep (se 2 (by rfl) ⟨3516183, by rfl⟩ : syracuseStep 9376489 = 7032367) B7032367
theorem B1644455 : Blo 972592 1644455 := bstep (se 1 (by rfl) ⟨1233341, by rfl⟩ : syracuseStep 1644455 = 2466683) B2466683
theorem B2464415 : Blo 972592 2464415 := bstep (se 1 (by rfl) ⟨1848311, by rfl⟩ : syracuseStep 2464415 = 3696623) B3696623
theorem B2106551 : Blo 972592 2106551 := bstep (se 1 (by rfl) ⟨1579913, by rfl⟩ : syracuseStep 2106551 = 3159827) B3159827
theorem B30844927 : Blo 972592 30844927 := bstep (se 1 (by rfl) ⟨23133695, by rfl⟩ : syracuseStep 30844927 = 46267391) B46267391
theorem B4925609 : Blo 972592 4925609 := bstep (se 2 (by rfl) ⟨1847103, by rfl⟩ : syracuseStep 4925609 = 3694207) B3694207
theorem B22491503 : Blo 972592 22491503 := bstep (se 1 (by rfl) ⟨16868627, by rfl⟩ : syracuseStep 22491503 = 33737255) B33737255
theorem B569913839 : Blo 972592 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B7026371 : Blo 972592 7026371 := bstep (se 1 (by rfl) ⟨5269778, by rfl⟩ : syracuseStep 7026371 = 10539557) B10539557
theorem B28096253 : Blo 972592 28096253 := bstep (se 3 (by rfl) ⟨5268047, by rfl⟩ : syracuseStep 28096253 = 10536095) B10536095
theorem B2080247 : Blo 972592 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B7389629 : Blo 972592 7389629 := bstep (se 3 (by rfl) ⟨1385555, by rfl⟩ : syracuseStep 7389629 = 2771111) B2771111
theorem B8012255 : Blo 972592 8012255 := bstep (se 1 (by rfl) ⟨6009191, by rfl⟩ : syracuseStep 8012255 = 12018383) B12018383
theorem B3293675 : Blo 972592 3293675 := bstep (se 1 (by rfl) ⟨2470256, by rfl⟩ : syracuseStep 3293675 = 4940513) B4940513
theorem B140886539 : Blo 972592 140886539 := bstep (se 1 (by rfl) ⟨105664904, by rfl⟩ : syracuseStep 140886539 = 211329809) B211329809
theorem B1461095 : Blo 972592 1461095 := bstep (se 1 (by rfl) ⟨1095821, by rfl⟩ : syracuseStep 1461095 = 2191643) B2191643
theorem B1462697 : Blo 972592 1462697 := bstep (se 2 (by rfl) ⟨548511, by rfl⟩ : syracuseStep 1462697 = 1097023) B1097023
theorem B1464575 : Blo 972592 1464575 := bstep (se 1 (by rfl) ⟨1098431, by rfl⟩ : syracuseStep 1464575 = 2196863) B2196863
theorem B973519 : Blo 972592 973519 := bstep (se 1 (by rfl) ⟨730139, by rfl⟩ : syracuseStep 973519 = 1460279) B1460279
theorem B974495 : Blo 972592 974495 := bstep (se 1 (by rfl) ⟨730871, by rfl⟩ : syracuseStep 974495 = 1461743) B1461743
theorem B16048327 : Blo 972592 16048327 := bstep (se 1 (by rfl) ⟨12036245, by rfl⟩ : syracuseStep 16048327 = 24072491) B24072491
theorem B975643 : Blo 972592 975643 := bstep (se 1 (by rfl) ⟨731732, by rfl⟩ : syracuseStep 975643 = 1463465) B1463465
theorem B975839 : Blo 972592 975839 := bstep (se 1 (by rfl) ⟨731879, by rfl⟩ : syracuseStep 975839 = 1463759) B1463759
theorem B38465567 : Blo 972592 38465567 := bstep (se 1 (by rfl) ⟨28849175, by rfl⟩ : syracuseStep 38465567 = 57698351) B57698351
theorem B21397769 : Blo 972592 21397769 := bstep (se 2 (by rfl) ⟨8024163, by rfl⟩ : syracuseStep 21397769 = 16048327) B16048327
theorem B2195783 : Blo 972592 2195783 := bstep (se 1 (by rfl) ⟨1646837, by rfl⟩ : syracuseStep 2195783 = 3293675) B3293675
theorem B21366013 : Blo 972592 21366013 := bstep (se 3 (by rfl) ⟨4006127, by rfl⟩ : syracuseStep 21366013 = 8012255) B8012255
theorem B1642943 : Blo 972592 1642943 := bstep (se 1 (by rfl) ⟨1232207, by rfl⟩ : syracuseStep 1642943 = 2464415) B2464415
theorem B16651817 : Blo 972592 16651817 := bstep (se 2 (by rfl) ⟨6244431, by rfl⟩ : syracuseStep 16651817 = 12488863) B12488863
theorem B3282713 : Blo 972592 3282713 := bstep (se 2 (by rfl) ⟨1231017, by rfl⟩ : syracuseStep 3282713 = 2462035) B2462035
theorem B3283739 : Blo 972592 3283739 := bstep (se 1 (by rfl) ⟨2462804, by rfl⟩ : syracuseStep 3283739 = 4925609) B4925609
theorem B5547325 : Blo 972592 5547325 := bstep (se 3 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 5547325 = 2080247) B2080247
theorem B164506277 : Blo 972592 164506277 := bstep (se 4 (by rfl) ⟨15422463, by rfl⟩ : syracuseStep 164506277 = 30844927) B30844927
theorem B4926419 : Blo 972592 4926419 := bstep (se 1 (by rfl) ⟨3694814, by rfl⟩ : syracuseStep 4926419 = 7389629) B7389629
theorem B93924359 : Blo 972592 93924359 := bstep (se 1 (by rfl) ⟨70443269, by rfl⟩ : syracuseStep 93924359 = 140886539) B140886539
theorem B5617469 : Blo 972592 5617469 := bstep (se 3 (by rfl) ⟨1053275, by rfl⟩ : syracuseStep 5617469 = 2106551) B2106551
theorem B1096303 : Blo 972592 1096303 := bstep (se 1 (by rfl) ⟨822227, by rfl⟩ : syracuseStep 1096303 = 1644455) B1644455
theorem B12501985 : Blo 972592 12501985 := bstep (se 2 (by rfl) ⟨4688244, by rfl⟩ : syracuseStep 12501985 = 9376489) B9376489
theorem B25643711 : Blo 972592 25643711 := bstep (se 1 (by rfl) ⟨19232783, by rfl⟩ : syracuseStep 25643711 = 38465567) B38465567
theorem B14994335 : Blo 972592 14994335 := bstep (se 1 (by rfl) ⟨11245751, by rfl⟩ : syracuseStep 14994335 = 22491503) B22491503
theorem B18730835 : Blo 972592 18730835 := bstep (se 1 (by rfl) ⟨14048126, by rfl⟩ : syracuseStep 18730835 = 28096253) B28096253
theorem B1464383 : Blo 972592 1464383 := bstep (se 1 (by rfl) ⟨1098287, by rfl⟩ : syracuseStep 1464383 = 2196575) B2196575
theorem B974063 : Blo 972592 974063 := bstep (se 1 (by rfl) ⟨730547, by rfl⟩ : syracuseStep 974063 = 1461095) B1461095
theorem B975131 : Blo 972592 975131 := bstep (se 1 (by rfl) ⟨731348, by rfl⟩ : syracuseStep 975131 = 1462697) B1462697
theorem B976383 : Blo 972592 976383 := bstep (se 1 (by rfl) ⟨732287, by rfl⟩ : syracuseStep 976383 = 1464575) B1464575
theorem B379942559 : Blo 972592 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B4684247 : Blo 972592 4684247 := bstep (se 1 (by rfl) ⟨3513185, by rfl⟩ : syracuseStep 4684247 = 7026371) B7026371
theorem B9996223 : Blo 972592 9996223 := bstep (se 1 (by rfl) ⟨7497167, by rfl⟩ : syracuseStep 9996223 = 14994335) B14994335
theorem B12487223 : Blo 972592 12487223 := bstep (se 1 (by rfl) ⟨9365417, by rfl⟩ : syracuseStep 12487223 = 18730835) B18730835
theorem B14979917 : Blo 972592 14979917 := bstep (se 3 (by rfl) ⟨2808734, by rfl⟩ : syracuseStep 14979917 = 5617469) B5617469
theorem B3284279 : Blo 972592 3284279 := bstep (se 1 (by rfl) ⟨2463209, by rfl⟩ : syracuseStep 3284279 = 4926419) B4926419
theorem B3122831 : Blo 972592 3122831 := bstep (se 1 (by rfl) ⟨2342123, by rfl⟩ : syracuseStep 3122831 = 4684247) B4684247
theorem B14265179 : Blo 972592 14265179 := bstep (se 1 (by rfl) ⟨10698884, by rfl⟩ : syracuseStep 14265179 = 21397769) B21397769
theorem B28488017 : Blo 972592 28488017 := bstep (se 2 (by rfl) ⟨10683006, by rfl⟩ : syracuseStep 28488017 = 21366013) B21366013
theorem B1095295 : Blo 972592 1095295 := bstep (se 1 (by rfl) ⟨821471, by rfl⟩ : syracuseStep 1095295 = 1642943) B1642943
theorem B1461737 : Blo 972592 1461737 := bstep (se 2 (by rfl) ⟨548151, by rfl⟩ : syracuseStep 1461737 = 1096303) B1096303
theorem B1463855 : Blo 972592 1463855 := bstep (se 1 (by rfl) ⟨1097891, by rfl⟩ : syracuseStep 1463855 = 2195783) B2195783
theorem B16669313 : Blo 972592 16669313 := bstep (se 2 (by rfl) ⟨6250992, by rfl⟩ : syracuseStep 16669313 = 12501985) B12501985
theorem B7396433 : Blo 972592 7396433 := bstep (se 2 (by rfl) ⟨2773662, by rfl⟩ : syracuseStep 7396433 = 5547325) B5547325
theorem B17095807 : Blo 972592 17095807 := bstep (se 1 (by rfl) ⟨12821855, by rfl⟩ : syracuseStep 17095807 = 25643711) B25643711
theorem B11101211 : Blo 972592 11101211 := bstep (se 1 (by rfl) ⟨8325908, by rfl⟩ : syracuseStep 11101211 = 16651817) B16651817
theorem B2188475 : Blo 972592 2188475 := bstep (se 1 (by rfl) ⟨1641356, by rfl⟩ : syracuseStep 2188475 = 3282713) B3282713
theorem B976255 : Blo 972592 976255 := bstep (se 1 (by rfl) ⟨732191, by rfl⟩ : syracuseStep 976255 = 1464383) B1464383
theorem B2189159 : Blo 972592 2189159 := bstep (se 1 (by rfl) ⟨1641869, by rfl⟩ : syracuseStep 2189159 = 3283739) B3283739
theorem B109670851 : Blo 972592 109670851 := bstep (se 1 (by rfl) ⟨82253138, by rfl⟩ : syracuseStep 109670851 = 164506277) B164506277
theorem B62616239 : Blo 972592 62616239 := bstep (se 1 (by rfl) ⟨46962179, by rfl⟩ : syracuseStep 62616239 = 93924359) B93924359
theorem B253295039 : Blo 972592 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B8324815 : Blo 972592 8324815 := bstep (se 1 (by rfl) ⟨6243611, by rfl⟩ : syracuseStep 8324815 = 12487223) B12487223
theorem B39946445 : Blo 972592 39946445 := bstep (se 3 (by rfl) ⟨7489958, by rfl⟩ : syracuseStep 39946445 = 14979917) B14979917
theorem B584911205 : Blo 972592 584911205 := bstep (se 4 (by rfl) ⟨54835425, by rfl⟩ : syracuseStep 584911205 = 109670851) B109670851
theorem B8327549 : Blo 972592 8327549 := bstep (se 3 (by rfl) ⟨1561415, by rfl⟩ : syracuseStep 8327549 = 3122831) B3122831
theorem B11112875 : Blo 972592 11112875 := bstep (se 1 (by rfl) ⟨8334656, by rfl⟩ : syracuseStep 11112875 = 16669313) B16669313
theorem B9510119 : Blo 972592 9510119 := bstep (se 1 (by rfl) ⟨7132589, by rfl⟩ : syracuseStep 9510119 = 14265179) B14265179
theorem B168863359 : Blo 972592 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B4930955 : Blo 972592 4930955 := bstep (se 1 (by rfl) ⟨3698216, by rfl⟩ : syracuseStep 4930955 = 7396433) B7396433
theorem B1458983 : Blo 972592 1458983 := bstep (se 1 (by rfl) ⟨1094237, by rfl⟩ : syracuseStep 1458983 = 2188475) B2188475
theorem B1459439 : Blo 972592 1459439 := bstep (se 1 (by rfl) ⟨1094579, by rfl⟩ : syracuseStep 1459439 = 2189159) B2189159
theorem B1460393 : Blo 972592 1460393 := bstep (se 2 (by rfl) ⟨547647, by rfl⟩ : syracuseStep 1460393 = 1095295) B1095295
theorem B18992011 : Blo 972592 18992011 := bstep (se 1 (by rfl) ⟨14244008, by rfl⟩ : syracuseStep 18992011 = 28488017) B28488017
theorem B22794409 : Blo 972592 22794409 := bstep (se 2 (by rfl) ⟨8547903, by rfl⟩ : syracuseStep 22794409 = 17095807) B17095807
theorem B974491 : Blo 972592 974491 := bstep (se 1 (by rfl) ⟨730868, by rfl⟩ : syracuseStep 974491 = 1461737) B1461737
theorem B13328297 : Blo 972592 13328297 := bstep (se 2 (by rfl) ⟨4998111, by rfl⟩ : syracuseStep 13328297 = 9996223) B9996223
theorem B975903 : Blo 972592 975903 := bstep (se 1 (by rfl) ⟨731927, by rfl⟩ : syracuseStep 975903 = 1463855) B1463855
theorem B2189519 : Blo 972592 2189519 := bstep (se 1 (by rfl) ⟨1642139, by rfl⟩ : syracuseStep 2189519 = 3284279) B3284279
theorem B7400807 : Blo 972592 7400807 := bstep (se 1 (by rfl) ⟨5550605, by rfl⟩ : syracuseStep 7400807 = 11101211) B11101211
theorem B41744159 : Blo 972592 41744159 := bstep (se 1 (by rfl) ⟨31308119, by rfl⟩ : syracuseStep 41744159 = 62616239) B62616239
theorem B389940803 : Blo 972592 389940803 := bstep (se 1 (by rfl) ⟨292455602, by rfl⟩ : syracuseStep 389940803 = 584911205) B584911205
theorem B225151145 : Blo 972592 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B7408583 : Blo 972592 7408583 := bstep (se 1 (by rfl) ⟨5556437, by rfl⟩ : syracuseStep 7408583 = 11112875) B11112875
theorem B8885531 : Blo 972592 8885531 := bstep (se 1 (by rfl) ⟨6664148, by rfl⟩ : syracuseStep 8885531 = 13328297) B13328297
theorem B27829439 : Blo 972592 27829439 := bstep (se 1 (by rfl) ⟨20872079, by rfl⟩ : syracuseStep 27829439 = 41744159) B41744159
theorem B3287303 : Blo 972592 3287303 := bstep (se 1 (by rfl) ⟨2465477, by rfl⟩ : syracuseStep 3287303 = 4930955) B4930955
theorem B5551699 : Blo 972592 5551699 := bstep (se 1 (by rfl) ⟨4163774, by rfl⟩ : syracuseStep 5551699 = 8327549) B8327549
theorem B6340079 : Blo 972592 6340079 := bstep (se 1 (by rfl) ⟨4755059, by rfl⟩ : syracuseStep 6340079 = 9510119) B9510119
theorem B30392545 : Blo 972592 30392545 := bstep (se 2 (by rfl) ⟨11397204, by rfl⟩ : syracuseStep 30392545 = 22794409) B22794409
theorem B1459679 : Blo 972592 1459679 := bstep (se 1 (by rfl) ⟨1094759, by rfl⟩ : syracuseStep 1459679 = 2189519) B2189519
theorem B4933871 : Blo 972592 4933871 := bstep (se 1 (by rfl) ⟨3700403, by rfl⟩ : syracuseStep 4933871 = 7400807) B7400807
theorem B972655 : Blo 972592 972655 := bstep (se 1 (by rfl) ⟨729491, by rfl⟩ : syracuseStep 972655 = 1458983) B1458983
theorem B972959 : Blo 972592 972959 := bstep (se 1 (by rfl) ⟨729719, by rfl⟩ : syracuseStep 972959 = 1459439) B1459439
theorem B973595 : Blo 972592 973595 := bstep (se 1 (by rfl) ⟨730196, by rfl⟩ : syracuseStep 973595 = 1460393) B1460393
theorem B26630963 : Blo 972592 26630963 := bstep (se 1 (by rfl) ⟨19973222, by rfl⟩ : syracuseStep 26630963 = 39946445) B39946445
theorem B11099753 : Blo 972592 11099753 := bstep (se 2 (by rfl) ⟨4162407, by rfl⟩ : syracuseStep 11099753 = 8324815) B8324815
theorem B25322681 : Blo 972592 25322681 := bstep (se 2 (by rfl) ⟨9496005, by rfl⟩ : syracuseStep 25322681 = 18992011) B18992011
theorem B16881787 : Blo 972592 16881787 := bstep (se 1 (by rfl) ⟨12661340, by rfl⟩ : syracuseStep 16881787 = 25322681) B25322681
theorem B18552959 : Blo 972592 18552959 := bstep (se 1 (by rfl) ⟨13914719, by rfl⟩ : syracuseStep 18552959 = 27829439) B27829439
theorem B259960535 : Blo 972592 259960535 := bstep (se 1 (by rfl) ⟨194970401, by rfl⟩ : syracuseStep 259960535 = 389940803) B389940803
theorem B3289247 : Blo 972592 3289247 := bstep (se 1 (by rfl) ⟨2466935, by rfl⟩ : syracuseStep 3289247 = 4933871) B4933871
theorem B2401612213 : Blo 972592 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B40523393 : Blo 972592 40523393 := bstep (se 2 (by rfl) ⟨15196272, by rfl⟩ : syracuseStep 40523393 = 30392545) B30392545
theorem B973119 : Blo 972592 973119 := bstep (se 1 (by rfl) ⟨729839, by rfl⟩ : syracuseStep 973119 = 1459679) B1459679
theorem B4939055 : Blo 972592 4939055 := bstep (se 1 (by rfl) ⟨3704291, by rfl⟩ : syracuseStep 4939055 = 7408583) B7408583
theorem B5923687 : Blo 972592 5923687 := bstep (se 1 (by rfl) ⟨4442765, by rfl⟩ : syracuseStep 5923687 = 8885531) B8885531
theorem B17753975 : Blo 972592 17753975 := bstep (se 1 (by rfl) ⟨13315481, by rfl⟩ : syracuseStep 17753975 = 26630963) B26630963
theorem B7399835 : Blo 972592 7399835 := bstep (se 1 (by rfl) ⟨5549876, by rfl⟩ : syracuseStep 7399835 = 11099753) B11099753
theorem B2191535 : Blo 972592 2191535 := bstep (se 1 (by rfl) ⟨1643651, by rfl⟩ : syracuseStep 2191535 = 3287303) B3287303
theorem B7402265 : Blo 972592 7402265 := bstep (se 2 (by rfl) ⟨2775849, by rfl⟩ : syracuseStep 7402265 = 5551699) B5551699
theorem B16906877 : Blo 972592 16906877 := bstep (se 3 (by rfl) ⟨3170039, by rfl⟩ : syracuseStep 16906877 = 6340079) B6340079
theorem B7898249 : Blo 972592 7898249 := bstep (se 2 (by rfl) ⟨2961843, by rfl⟩ : syracuseStep 7898249 = 5923687) B5923687
theorem B11835983 : Blo 972592 11835983 := bstep (se 1 (by rfl) ⟨8876987, by rfl⟩ : syracuseStep 11835983 = 17753975) B17753975
theorem B12368639 : Blo 972592 12368639 := bstep (se 1 (by rfl) ⟨9276479, by rfl⟩ : syracuseStep 12368639 = 18552959) B18552959
theorem B3292703 : Blo 972592 3292703 := bstep (se 1 (by rfl) ⟨2469527, by rfl⟩ : syracuseStep 3292703 = 4939055) B4939055
theorem B4933223 : Blo 972592 4933223 := bstep (se 1 (by rfl) ⟨3699917, by rfl⟩ : syracuseStep 4933223 = 7399835) B7399835
theorem B1461023 : Blo 972592 1461023 := bstep (se 1 (by rfl) ⟨1095767, by rfl⟩ : syracuseStep 1461023 = 2191535) B2191535
theorem B4934843 : Blo 972592 4934843 := bstep (se 1 (by rfl) ⟨3701132, by rfl⟩ : syracuseStep 4934843 = 7402265) B7402265
theorem B108062381 : Blo 972592 108062381 := bstep (se 3 (by rfl) ⟨20261696, by rfl⟩ : syracuseStep 108062381 = 40523393) B40523393
theorem B3202149617 : Blo 972592 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B173307023 : Blo 972592 173307023 := bstep (se 1 (by rfl) ⟨129980267, by rfl⟩ : syracuseStep 173307023 = 259960535) B259960535
theorem B2192831 : Blo 972592 2192831 := bstep (se 1 (by rfl) ⟨1644623, by rfl⟩ : syracuseStep 2192831 = 3289247) B3289247
theorem B22509049 : Blo 972592 22509049 := bstep (se 2 (by rfl) ⟨8440893, by rfl⟩ : syracuseStep 22509049 = 16881787) B16881787
theorem B11271251 : Blo 972592 11271251 := bstep (se 1 (by rfl) ⟨8453438, by rfl⟩ : syracuseStep 11271251 = 16906877) B16906877
theorem B288166349 : Blo 972592 288166349 := bstep (se 3 (by rfl) ⟨54031190, by rfl⟩ : syracuseStep 288166349 = 108062381) B108062381
theorem B7514167 : Blo 972592 7514167 := bstep (se 1 (by rfl) ⟨5635625, by rfl⟩ : syracuseStep 7514167 = 11271251) B11271251
theorem B3288815 : Blo 972592 3288815 := bstep (se 1 (by rfl) ⟨2466611, by rfl⟩ : syracuseStep 3288815 = 4933223) B4933223
theorem B3289895 : Blo 972592 3289895 := bstep (se 1 (by rfl) ⟨2467421, by rfl⟩ : syracuseStep 3289895 = 4934843) B4934843
theorem B32983037 : Blo 972592 32983037 := bstep (se 3 (by rfl) ⟨6184319, by rfl⟩ : syracuseStep 32983037 = 12368639) B12368639
theorem B1461887 : Blo 972592 1461887 := bstep (se 1 (by rfl) ⟨1096415, by rfl⟩ : syracuseStep 1461887 = 2192831) B2192831
theorem B5265499 : Blo 972592 5265499 := bstep (se 1 (by rfl) ⟨3949124, by rfl⟩ : syracuseStep 5265499 = 7898249) B7898249
theorem B974015 : Blo 972592 974015 := bstep (se 1 (by rfl) ⟨730511, by rfl⟩ : syracuseStep 974015 = 1461023) B1461023
theorem B7890655 : Blo 972592 7890655 := bstep (se 1 (by rfl) ⟨5917991, by rfl⟩ : syracuseStep 7890655 = 11835983) B11835983
theorem B30012065 : Blo 972592 30012065 := bstep (se 2 (by rfl) ⟨11254524, by rfl⟩ : syracuseStep 30012065 = 22509049) B22509049
theorem B2134766411 : Blo 972592 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B115538015 : Blo 972592 115538015 := bstep (se 1 (by rfl) ⟨86653511, by rfl⟩ : syracuseStep 115538015 = 173307023) B173307023
theorem B2195135 : Blo 972592 2195135 := bstep (se 1 (by rfl) ⟨1646351, by rfl⟩ : syracuseStep 2195135 = 3292703) B3292703
theorem B21988691 : Blo 972592 21988691 := bstep (se 1 (by rfl) ⟨16491518, by rfl⟩ : syracuseStep 21988691 = 32983037) B32983037
theorem B10520873 : Blo 972592 10520873 := bstep (se 2 (by rfl) ⟨3945327, by rfl⟩ : syracuseStep 10520873 = 7890655) B7890655
theorem B7020665 : Blo 972592 7020665 := bstep (se 2 (by rfl) ⟨2632749, by rfl⟩ : syracuseStep 7020665 = 5265499) B5265499
theorem B20008043 : Blo 972592 20008043 := bstep (se 1 (by rfl) ⟨15006032, by rfl⟩ : syracuseStep 20008043 = 30012065) B30012065
theorem B77025343 : Blo 972592 77025343 := bstep (se 1 (by rfl) ⟨57769007, by rfl⟩ : syracuseStep 77025343 = 115538015) B115538015
theorem B1463423 : Blo 972592 1463423 := bstep (se 1 (by rfl) ⟨1097567, by rfl⟩ : syracuseStep 1463423 = 2195135) B2195135
theorem B974591 : Blo 972592 974591 := bstep (se 1 (by rfl) ⟨730943, by rfl⟩ : syracuseStep 974591 = 1461887) B1461887
theorem B10018889 : Blo 972592 10018889 := bstep (se 2 (by rfl) ⟨3757083, by rfl⟩ : syracuseStep 10018889 = 7514167) B7514167
theorem B192110899 : Blo 972592 192110899 := bstep (se 1 (by rfl) ⟨144083174, by rfl⟩ : syracuseStep 192110899 = 288166349) B288166349
theorem B2192543 : Blo 972592 2192543 := bstep (se 1 (by rfl) ⟨1644407, by rfl⟩ : syracuseStep 2192543 = 3288815) B3288815
theorem B2193263 : Blo 972592 2193263 := bstep (se 1 (by rfl) ⟨1644947, by rfl⟩ : syracuseStep 2193263 = 3289895) B3289895
theorem B1423177607 : Blo 972592 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B256147865 : Blo 972592 256147865 := bstep (se 2 (by rfl) ⟨96055449, by rfl⟩ : syracuseStep 256147865 = 192110899) B192110899
theorem B7013915 : Blo 972592 7013915 := bstep (se 1 (by rfl) ⟨5260436, by rfl⟩ : syracuseStep 7013915 = 10520873) B10520873
theorem B13338695 : Blo 972592 13338695 := bstep (se 1 (by rfl) ⟨10004021, by rfl⟩ : syracuseStep 13338695 = 20008043) B20008043
theorem B102700457 : Blo 972592 102700457 := bstep (se 2 (by rfl) ⟨38512671, by rfl⟩ : syracuseStep 102700457 = 77025343) B77025343
theorem B14659127 : Blo 972592 14659127 := bstep (se 1 (by rfl) ⟨10994345, by rfl⟩ : syracuseStep 14659127 = 21988691) B21988691
theorem B1461695 : Blo 972592 1461695 := bstep (se 1 (by rfl) ⟨1096271, by rfl⟩ : syracuseStep 1461695 = 2192543) B2192543
theorem B1462175 : Blo 972592 1462175 := bstep (se 1 (by rfl) ⟨1096631, by rfl⟩ : syracuseStep 1462175 = 2193263) B2193263
theorem B948785071 : Blo 972592 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B975615 : Blo 972592 975615 := bstep (se 1 (by rfl) ⟨731711, by rfl⟩ : syracuseStep 975615 = 1463423) B1463423
theorem B6679259 : Blo 972592 6679259 := bstep (se 1 (by rfl) ⟨5009444, by rfl⟩ : syracuseStep 6679259 = 10018889) B10018889
theorem B4680443 : Blo 972592 4680443 := bstep (se 1 (by rfl) ⟨3510332, by rfl⟩ : syracuseStep 4680443 = 7020665) B7020665
theorem B1265046761 : Blo 972592 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B3120295 : Blo 972592 3120295 := bstep (se 1 (by rfl) ⟨2340221, by rfl⟩ : syracuseStep 3120295 = 4680443) B4680443
theorem B9772751 : Blo 972592 9772751 := bstep (se 1 (by rfl) ⟨7329563, by rfl⟩ : syracuseStep 9772751 = 14659127) B14659127
theorem B170765243 : Blo 972592 170765243 := bstep (se 1 (by rfl) ⟨128073932, by rfl⟩ : syracuseStep 170765243 = 256147865) B256147865
theorem B8892463 : Blo 972592 8892463 := bstep (se 1 (by rfl) ⟨6669347, by rfl⟩ : syracuseStep 8892463 = 13338695) B13338695
theorem B68466971 : Blo 972592 68466971 := bstep (se 1 (by rfl) ⟨51350228, by rfl⟩ : syracuseStep 68466971 = 102700457) B102700457
theorem B4675943 : Blo 972592 4675943 := bstep (se 1 (by rfl) ⟨3506957, by rfl⟩ : syracuseStep 4675943 = 7013915) B7013915
theorem B974463 : Blo 972592 974463 := bstep (se 1 (by rfl) ⟨730847, by rfl⟩ : syracuseStep 974463 = 1461695) B1461695
theorem B974783 : Blo 972592 974783 := bstep (se 1 (by rfl) ⟨731087, by rfl⟩ : syracuseStep 974783 = 1462175) B1462175
theorem B4452839 : Blo 972592 4452839 := bstep (se 1 (by rfl) ⟨3339629, by rfl⟩ : syracuseStep 4452839 = 6679259) B6679259
theorem B3117295 : Blo 972592 3117295 := bstep (se 1 (by rfl) ⟨2337971, by rfl⟩ : syracuseStep 3117295 = 4675943) B4675943
theorem B113843495 : Blo 972592 113843495 := bstep (se 1 (by rfl) ⟨85382621, by rfl⟩ : syracuseStep 113843495 = 170765243) B170765243
theorem B26060669 : Blo 972592 26060669 := bstep (se 3 (by rfl) ⟨4886375, by rfl⟩ : syracuseStep 26060669 = 9772751) B9772751
theorem B843364507 : Blo 972592 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B2968559 : Blo 972592 2968559 := bstep (se 1 (by rfl) ⟨2226419, by rfl⟩ : syracuseStep 2968559 = 4452839) B4452839
theorem B11856617 : Blo 972592 11856617 := bstep (se 2 (by rfl) ⟨4446231, by rfl⟩ : syracuseStep 11856617 = 8892463) B8892463
theorem B45644647 : Blo 972592 45644647 := bstep (se 1 (by rfl) ⟨34233485, by rfl⟩ : syracuseStep 45644647 = 68466971) B68466971
theorem B4160393 : Blo 972592 4160393 := bstep (se 2 (by rfl) ⟨1560147, by rfl⟩ : syracuseStep 4160393 = 3120295) B3120295
theorem B75895663 : Blo 972592 75895663 := bstep (se 1 (by rfl) ⟨56921747, by rfl⟩ : syracuseStep 75895663 = 113843495) B113843495
theorem B17373779 : Blo 972592 17373779 := bstep (se 1 (by rfl) ⟨13030334, by rfl⟩ : syracuseStep 17373779 = 26060669) B26060669
theorem B7904411 : Blo 972592 7904411 := bstep (se 1 (by rfl) ⟨5928308, by rfl⟩ : syracuseStep 7904411 = 11856617) B11856617
theorem B60859529 : Blo 972592 60859529 := bstep (se 2 (by rfl) ⟨22822323, by rfl⟩ : syracuseStep 60859529 = 45644647) B45644647
theorem B16625573 : Blo 972592 16625573 := bstep (se 4 (by rfl) ⟨1558647, by rfl⟩ : syracuseStep 16625573 = 3117295) B3117295
theorem B1979039 : Blo 972592 1979039 := bstep (se 1 (by rfl) ⟨1484279, by rfl⟩ : syracuseStep 1979039 = 2968559) B2968559
theorem B1124486009 : Blo 972592 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B2773595 : Blo 972592 2773595 := bstep (se 1 (by rfl) ⟨2080196, by rfl⟩ : syracuseStep 2773595 = 4160393) B4160393
theorem B5277437 : Blo 972592 5277437 := bstep (se 3 (by rfl) ⟨989519, by rfl⟩ : syracuseStep 5277437 = 1979039) B1979039
theorem B40573019 : Blo 972592 40573019 := bstep (se 1 (by rfl) ⟨30429764, by rfl⟩ : syracuseStep 40573019 = 60859529) B60859529
theorem B101194217 : Blo 972592 101194217 := bstep (se 2 (by rfl) ⟨37947831, by rfl⟩ : syracuseStep 101194217 = 75895663) B75895663
theorem B11083715 : Blo 972592 11083715 := bstep (se 1 (by rfl) ⟨8312786, by rfl⟩ : syracuseStep 11083715 = 16625573) B16625573
theorem B1849063 : Blo 972592 1849063 := bstep (se 1 (by rfl) ⟨1386797, by rfl⟩ : syracuseStep 1849063 = 2773595) B2773595
theorem B11582519 : Blo 972592 11582519 := bstep (se 1 (by rfl) ⟨8686889, by rfl⟩ : syracuseStep 11582519 = 17373779) B17373779
theorem B749657339 : Blo 972592 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B5269607 : Blo 972592 5269607 := bstep (se 1 (by rfl) ⟨3952205, by rfl⟩ : syracuseStep 5269607 = 7904411) B7904411
theorem B3513071 : Blo 972592 3513071 := bstep (se 1 (by rfl) ⟨2634803, by rfl⟩ : syracuseStep 3513071 = 5269607) B5269607
theorem B2465417 : Blo 972592 2465417 := bstep (se 2 (by rfl) ⟨924531, by rfl⟩ : syracuseStep 2465417 = 1849063) B1849063
theorem B123546869 : Blo 972592 123546869 := bstep (se 5 (by rfl) ⟨5791259, by rfl⟩ : syracuseStep 123546869 = 11582519) B11582519
theorem B3518291 : Blo 972592 3518291 := bstep (se 1 (by rfl) ⟨2638718, by rfl⟩ : syracuseStep 3518291 = 5277437) B5277437
theorem B7389143 : Blo 972592 7389143 := bstep (se 1 (by rfl) ⟨5541857, by rfl⟩ : syracuseStep 7389143 = 11083715) B11083715
theorem B67462811 : Blo 972592 67462811 := bstep (se 1 (by rfl) ⟨50597108, by rfl⟩ : syracuseStep 67462811 = 101194217) B101194217
theorem B499771559 : Blo 972592 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B108194717 : Blo 972592 108194717 := bstep (se 3 (by rfl) ⟨20286509, by rfl⟩ : syracuseStep 108194717 = 40573019) B40573019
theorem B1643611 : Blo 972592 1643611 := bstep (se 1 (by rfl) ⟨1232708, by rfl⟩ : syracuseStep 1643611 = 2465417) B2465417
theorem B4926095 : Blo 972592 4926095 := bstep (se 1 (by rfl) ⟨3694571, by rfl⟩ : syracuseStep 4926095 = 7389143) B7389143
theorem B2342047 : Blo 972592 2342047 := bstep (se 1 (by rfl) ⟨1756535, by rfl⟩ : syracuseStep 2342047 = 3513071) B3513071
theorem B44975207 : Blo 972592 44975207 := bstep (se 1 (by rfl) ⟨33731405, by rfl⟩ : syracuseStep 44975207 = 67462811) B67462811
theorem B82364579 : Blo 972592 82364579 := bstep (se 1 (by rfl) ⟨61773434, by rfl⟩ : syracuseStep 82364579 = 123546869) B123546869
theorem B2345527 : Blo 972592 2345527 := bstep (se 1 (by rfl) ⟨1759145, by rfl⟩ : syracuseStep 2345527 = 3518291) B3518291
theorem B333181039 : Blo 972592 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B288519245 : Blo 972592 288519245 := bstep (se 3 (by rfl) ⟨54097358, by rfl⟩ : syracuseStep 288519245 = 108194717) B108194717
theorem B119933885 : Blo 972592 119933885 := bstep (se 3 (by rfl) ⟨22487603, by rfl⟩ : syracuseStep 119933885 = 44975207) B44975207
theorem B444241385 : Blo 972592 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B3284063 : Blo 972592 3284063 := bstep (se 1 (by rfl) ⟨2463047, by rfl⟩ : syracuseStep 3284063 = 4926095) B4926095
theorem B3122729 : Blo 972592 3122729 := bstep (se 2 (by rfl) ⟨1171023, by rfl⟩ : syracuseStep 3122729 = 2342047) B2342047
theorem B3127369 : Blo 972592 3127369 := bstep (se 2 (by rfl) ⟨1172763, by rfl⟩ : syracuseStep 3127369 = 2345527) B2345527
theorem B54909719 : Blo 972592 54909719 := bstep (se 1 (by rfl) ⟨41182289, by rfl⟩ : syracuseStep 54909719 = 82364579) B82364579
theorem B2191481 : Blo 972592 2191481 := bstep (se 2 (by rfl) ⟨821805, by rfl⟩ : syracuseStep 2191481 = 1643611) B1643611
theorem B192346163 : Blo 972592 192346163 := bstep (se 1 (by rfl) ⟨144259622, by rfl⟩ : syracuseStep 192346163 = 288519245) B288519245
theorem B79955923 : Blo 972592 79955923 := bstep (se 1 (by rfl) ⟨59966942, by rfl⟩ : syracuseStep 79955923 = 119933885) B119933885
theorem B296160923 : Blo 972592 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B36606479 : Blo 972592 36606479 := bstep (se 1 (by rfl) ⟨27454859, by rfl⟩ : syracuseStep 36606479 = 54909719) B54909719
theorem B4169825 : Blo 972592 4169825 := bstep (se 2 (by rfl) ⟨1563684, by rfl⟩ : syracuseStep 4169825 = 3127369) B3127369
theorem B128230775 : Blo 972592 128230775 := bstep (se 1 (by rfl) ⟨96173081, by rfl⟩ : syracuseStep 128230775 = 192346163) B192346163
theorem B2081819 : Blo 972592 2081819 := bstep (se 1 (by rfl) ⟨1561364, by rfl⟩ : syracuseStep 2081819 = 3122729) B3122729
theorem B1460987 : Blo 972592 1460987 := bstep (se 1 (by rfl) ⟨1095740, by rfl⟩ : syracuseStep 1460987 = 2191481) B2191481
theorem B2189375 : Blo 972592 2189375 := bstep (se 1 (by rfl) ⟨1642031, by rfl⟩ : syracuseStep 2189375 = 3284063) B3284063
theorem B97617277 : Blo 972592 97617277 := bstep (se 3 (by rfl) ⟨18303239, by rfl⟩ : syracuseStep 97617277 = 36606479) B36606479
theorem B197440615 : Blo 972592 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B106607897 : Blo 972592 106607897 := bstep (se 2 (by rfl) ⟨39977961, by rfl⟩ : syracuseStep 106607897 = 79955923) B79955923
theorem B5551517 : Blo 972592 5551517 := bstep (se 3 (by rfl) ⟨1040909, by rfl⟩ : syracuseStep 5551517 = 2081819) B2081819
theorem B1459583 : Blo 972592 1459583 := bstep (se 1 (by rfl) ⟨1094687, by rfl⟩ : syracuseStep 1459583 = 2189375) B2189375
theorem B973991 : Blo 972592 973991 := bstep (se 1 (by rfl) ⟨730493, by rfl⟩ : syracuseStep 973991 = 1460987) B1460987
theorem B2779883 : Blo 972592 2779883 := bstep (se 1 (by rfl) ⟨2084912, by rfl⟩ : syracuseStep 2779883 = 4169825) B4169825
theorem B85487183 : Blo 972592 85487183 := bstep (se 1 (by rfl) ⟨64115387, by rfl⟩ : syracuseStep 85487183 = 128230775) B128230775
theorem B520625477 : Blo 972592 520625477 := bstep (se 4 (by rfl) ⟨48808638, by rfl⟩ : syracuseStep 520625477 = 97617277) B97617277
theorem B56991455 : Blo 972592 56991455 := bstep (se 1 (by rfl) ⟨42743591, by rfl⟩ : syracuseStep 56991455 = 85487183) B85487183
theorem B1853255 : Blo 972592 1853255 := bstep (se 1 (by rfl) ⟨1389941, by rfl⟩ : syracuseStep 1853255 = 2779883) B2779883
theorem B973055 : Blo 972592 973055 := bstep (se 1 (by rfl) ⟨729791, by rfl⟩ : syracuseStep 973055 = 1459583) B1459583
theorem B263254153 : Blo 972592 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B71071931 : Blo 972592 71071931 := bstep (se 1 (by rfl) ⟨53303948, by rfl⟩ : syracuseStep 71071931 = 106607897) B106607897
theorem B3701011 : Blo 972592 3701011 := bstep (se 1 (by rfl) ⟨2775758, by rfl⟩ : syracuseStep 3701011 = 5551517) B5551517
theorem B347083651 : Blo 972592 347083651 := bstep (se 1 (by rfl) ⟨260312738, by rfl⟩ : syracuseStep 347083651 = 520625477) B520625477
theorem B37994303 : Blo 972592 37994303 := bstep (se 1 (by rfl) ⟨28495727, by rfl⟩ : syracuseStep 37994303 = 56991455) B56991455
theorem B4934681 : Blo 972592 4934681 := bstep (se 2 (by rfl) ⟨1850505, by rfl⟩ : syracuseStep 4934681 = 3701011) B3701011
theorem B1235503 : Blo 972592 1235503 := bstep (se 1 (by rfl) ⟨926627, by rfl⟩ : syracuseStep 1235503 = 1853255) B1853255
theorem B351005537 : Blo 972592 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B47381287 : Blo 972592 47381287 := bstep (se 1 (by rfl) ⟨35535965, by rfl⟩ : syracuseStep 47381287 = 71071931) B71071931
theorem B234003691 : Blo 972592 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B1647337 : Blo 972592 1647337 := bstep (se 2 (by rfl) ⟨617751, by rfl⟩ : syracuseStep 1647337 = 1235503) B1235503
theorem B3289787 : Blo 972592 3289787 := bstep (se 1 (by rfl) ⟨2467340, by rfl⟩ : syracuseStep 3289787 = 4934681) B4934681
theorem B462778201 : Blo 972592 462778201 := bstep (se 2 (by rfl) ⟨173541825, by rfl⟩ : syracuseStep 462778201 = 347083651) B347083651
theorem B63175049 : Blo 972592 63175049 := bstep (se 2 (by rfl) ⟨23690643, by rfl⟩ : syracuseStep 63175049 = 47381287) B47381287
theorem B101318141 : Blo 972592 101318141 := bstep (se 3 (by rfl) ⟨18997151, by rfl⟩ : syracuseStep 101318141 = 37994303) B37994303
theorem B2196449 : Blo 972592 2196449 := bstep (se 2 (by rfl) ⟨823668, by rfl⟩ : syracuseStep 2196449 = 1647337) B1647337
theorem B42116699 : Blo 972592 42116699 := bstep (se 1 (by rfl) ⟨31587524, by rfl⟩ : syracuseStep 42116699 = 63175049) B63175049
theorem B67545427 : Blo 972592 67545427 := bstep (se 1 (by rfl) ⟨50659070, by rfl⟩ : syracuseStep 67545427 = 101318141) B101318141
theorem B617037601 : Blo 972592 617037601 := bstep (se 2 (by rfl) ⟨231389100, by rfl⟩ : syracuseStep 617037601 = 462778201) B462778201
theorem B312004921 : Blo 972592 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B2193191 : Blo 972592 2193191 := bstep (se 1 (by rfl) ⟨1644893, by rfl⟩ : syracuseStep 2193191 = 3289787) B3289787
theorem B822716801 : Blo 972592 822716801 := bstep (se 2 (by rfl) ⟨308518800, by rfl⟩ : syracuseStep 822716801 = 617037601) B617037601
theorem B90060569 : Blo 972592 90060569 := bstep (se 2 (by rfl) ⟨33772713, by rfl⟩ : syracuseStep 90060569 = 67545427) B67545427
theorem B416006561 : Blo 972592 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B1462127 : Blo 972592 1462127 := bstep (se 1 (by rfl) ⟨1096595, by rfl⟩ : syracuseStep 1462127 = 2193191) B2193191
theorem B1464299 : Blo 972592 1464299 := bstep (se 1 (by rfl) ⟨1098224, by rfl⟩ : syracuseStep 1464299 = 2196449) B2196449
theorem B28077799 : Blo 972592 28077799 := bstep (se 1 (by rfl) ⟨21058349, by rfl⟩ : syracuseStep 28077799 = 42116699) B42116699
theorem B548477867 : Blo 972592 548477867 := bstep (se 1 (by rfl) ⟨411358400, by rfl⟩ : syracuseStep 548477867 = 822716801) B822716801
theorem B60040379 : Blo 972592 60040379 := bstep (se 1 (by rfl) ⟨45030284, by rfl⟩ : syracuseStep 60040379 = 90060569) B90060569
theorem B37437065 : Blo 972592 37437065 := bstep (se 2 (by rfl) ⟨14038899, by rfl⟩ : syracuseStep 37437065 = 28077799) B28077799
theorem B1109350829 : Blo 972592 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B974751 : Blo 972592 974751 := bstep (se 1 (by rfl) ⟨731063, by rfl⟩ : syracuseStep 974751 = 1462127) B1462127
theorem B976199 : Blo 972592 976199 := bstep (se 1 (by rfl) ⟨732149, by rfl⟩ : syracuseStep 976199 = 1464299) B1464299
theorem B40026919 : Blo 972592 40026919 := bstep (se 1 (by rfl) ⟨30020189, by rfl⟩ : syracuseStep 40026919 = 60040379) B60040379
theorem B24958043 : Blo 972592 24958043 := bstep (se 1 (by rfl) ⟨18718532, by rfl⟩ : syracuseStep 24958043 = 37437065) B37437065
theorem B739567219 : Blo 972592 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B365651911 : Blo 972592 365651911 := bstep (se 1 (by rfl) ⟨274238933, by rfl⟩ : syracuseStep 365651911 = 548477867) B548477867
theorem B986089625 : Blo 972592 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B487535881 : Blo 972592 487535881 := bstep (se 2 (by rfl) ⟨182825955, by rfl⟩ : syracuseStep 487535881 = 365651911) B365651911
theorem B53369225 : Blo 972592 53369225 := bstep (se 2 (by rfl) ⟨20013459, by rfl⟩ : syracuseStep 53369225 = 40026919) B40026919
theorem B16638695 : Blo 972592 16638695 := bstep (se 1 (by rfl) ⟨12479021, by rfl⟩ : syracuseStep 16638695 = 24958043) B24958043
theorem B657393083 : Blo 972592 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B11092463 : Blo 972592 11092463 := bstep (se 1 (by rfl) ⟨8319347, by rfl⟩ : syracuseStep 11092463 = 16638695) B16638695
theorem B35579483 : Blo 972592 35579483 := bstep (se 1 (by rfl) ⟨26684612, by rfl⟩ : syracuseStep 35579483 = 53369225) B53369225
theorem B650047841 : Blo 972592 650047841 := bstep (se 2 (by rfl) ⟨243767940, by rfl⟩ : syracuseStep 650047841 = 487535881) B487535881
theorem B433365227 : Blo 972592 433365227 := bstep (se 1 (by rfl) ⟨325023920, by rfl⟩ : syracuseStep 433365227 = 650047841) B650047841
theorem B7394975 : Blo 972592 7394975 := bstep (se 1 (by rfl) ⟨5546231, by rfl⟩ : syracuseStep 7394975 = 11092463) B11092463
theorem B438262055 : Blo 972592 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B23719655 : Blo 972592 23719655 := bstep (se 1 (by rfl) ⟨17789741, by rfl⟩ : syracuseStep 23719655 = 35579483) B35579483
theorem B4929983 : Blo 972592 4929983 := bstep (se 1 (by rfl) ⟨3697487, by rfl⟩ : syracuseStep 4929983 = 7394975) B7394975
theorem B292174703 : Blo 972592 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B15813103 : Blo 972592 15813103 := bstep (se 1 (by rfl) ⟨11859827, by rfl⟩ : syracuseStep 15813103 = 23719655) B23719655
theorem B288910151 : Blo 972592 288910151 := bstep (se 1 (by rfl) ⟨216682613, by rfl⟩ : syracuseStep 288910151 = 433365227) B433365227
theorem B3286655 : Blo 972592 3286655 := bstep (se 1 (by rfl) ⟨2464991, by rfl⟩ : syracuseStep 3286655 = 4929983) B4929983
theorem B194783135 : Blo 972592 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B21084137 : Blo 972592 21084137 := bstep (se 2 (by rfl) ⟨7906551, by rfl⟩ : syracuseStep 21084137 = 15813103) B15813103
theorem B192606767 : Blo 972592 192606767 := bstep (se 1 (by rfl) ⟨144455075, by rfl⟩ : syracuseStep 192606767 = 288910151) B288910151
theorem B519421693 : Blo 972592 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B128404511 : Blo 972592 128404511 := bstep (se 1 (by rfl) ⟨96303383, by rfl⟩ : syracuseStep 128404511 = 192606767) B192606767
theorem B2191103 : Blo 972592 2191103 := bstep (se 1 (by rfl) ⟨1643327, by rfl⟩ : syracuseStep 2191103 = 3286655) B3286655
theorem B14056091 : Blo 972592 14056091 := bstep (se 1 (by rfl) ⟨10542068, by rfl⟩ : syracuseStep 14056091 = 21084137) B21084137
theorem B692562257 : Blo 972592 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B85603007 : Blo 972592 85603007 := bstep (se 1 (by rfl) ⟨64202255, by rfl⟩ : syracuseStep 85603007 = 128404511) B128404511
theorem B1460735 : Blo 972592 1460735 := bstep (se 1 (by rfl) ⟨1095551, by rfl⟩ : syracuseStep 1460735 = 2191103) B2191103
theorem B9370727 : Blo 972592 9370727 := bstep (se 1 (by rfl) ⟨7028045, by rfl⟩ : syracuseStep 9370727 = 14056091) B14056091
theorem B461708171 : Blo 972592 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B57068671 : Blo 972592 57068671 := bstep (se 1 (by rfl) ⟨42801503, by rfl⟩ : syracuseStep 57068671 = 85603007) B85603007
theorem B6247151 : Blo 972592 6247151 := bstep (se 1 (by rfl) ⟨4685363, by rfl⟩ : syracuseStep 6247151 = 9370727) B9370727
theorem B973823 : Blo 972592 973823 := bstep (se 1 (by rfl) ⟨730367, by rfl⟩ : syracuseStep 973823 = 1460735) B1460735
theorem B4164767 : Blo 972592 4164767 := bstep (se 1 (by rfl) ⟨3123575, by rfl⟩ : syracuseStep 4164767 = 6247151) B6247151
theorem B76091561 : Blo 972592 76091561 := bstep (se 2 (by rfl) ⟨28534335, by rfl⟩ : syracuseStep 76091561 = 57068671) B57068671
theorem B307805447 : Blo 972592 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B50727707 : Blo 972592 50727707 := bstep (se 1 (by rfl) ⟨38045780, by rfl⟩ : syracuseStep 50727707 = 76091561) B76091561
theorem B205203631 : Blo 972592 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B2776511 : Blo 972592 2776511 := bstep (se 1 (by rfl) ⟨2082383, by rfl⟩ : syracuseStep 2776511 = 4164767) B4164767
theorem B33818471 : Blo 972592 33818471 := bstep (se 1 (by rfl) ⟨25363853, by rfl⟩ : syracuseStep 33818471 = 50727707) B50727707
theorem B1851007 : Blo 972592 1851007 := bstep (se 1 (by rfl) ⟨1388255, by rfl⟩ : syracuseStep 1851007 = 2776511) B2776511
theorem B273604841 : Blo 972592 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B22545647 : Blo 972592 22545647 := bstep (se 1 (by rfl) ⟨16909235, by rfl⟩ : syracuseStep 22545647 = 33818471) B33818471
theorem B2468009 : Blo 972592 2468009 := bstep (se 2 (by rfl) ⟨925503, by rfl⟩ : syracuseStep 2468009 = 1851007) B1851007
theorem B182403227 : Blo 972592 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B121602151 : Blo 972592 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B1645339 : Blo 972592 1645339 := bstep (se 1 (by rfl) ⟨1234004, by rfl⟩ : syracuseStep 1645339 = 2468009) B2468009
theorem B15030431 : Blo 972592 15030431 := bstep (se 1 (by rfl) ⟨11272823, by rfl⟩ : syracuseStep 15030431 = 22545647) B22545647
theorem B648544805 : Blo 972592 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B10020287 : Blo 972592 10020287 := bstep (se 1 (by rfl) ⟨7515215, by rfl⟩ : syracuseStep 10020287 = 15030431) B15030431
theorem B2193785 : Blo 972592 2193785 := bstep (se 2 (by rfl) ⟨822669, by rfl⟩ : syracuseStep 2193785 = 1645339) B1645339
theorem B1462523 : Blo 972592 1462523 := bstep (se 1 (by rfl) ⟨1096892, by rfl⟩ : syracuseStep 1462523 = 2193785) B2193785
theorem B432363203 : Blo 972592 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B6680191 : Blo 972592 6680191 := bstep (se 1 (by rfl) ⟨5010143, by rfl⟩ : syracuseStep 6680191 = 10020287) B10020287
theorem B288242135 : Blo 972592 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B975015 : Blo 972592 975015 := bstep (se 1 (by rfl) ⟨731261, by rfl⟩ : syracuseStep 975015 = 1462523) B1462523
theorem B8906921 : Blo 972592 8906921 := bstep (se 2 (by rfl) ⟨3340095, by rfl⟩ : syracuseStep 8906921 = 6680191) B6680191
theorem B5937947 : Blo 972592 5937947 := bstep (se 1 (by rfl) ⟨4453460, by rfl⟩ : syracuseStep 5937947 = 8906921) B8906921
theorem B192161423 : Blo 972592 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B128107615 : Blo 972592 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B3958631 : Blo 972592 3958631 := bstep (se 1 (by rfl) ⟨2968973, by rfl⟩ : syracuseStep 3958631 = 5937947) B5937947
theorem B2639087 : Blo 972592 2639087 := bstep (se 1 (by rfl) ⟨1979315, by rfl⟩ : syracuseStep 2639087 = 3958631) B3958631
theorem B170810153 : Blo 972592 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B113873435 : Blo 972592 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B1759391 : Blo 972592 1759391 := bstep (se 1 (by rfl) ⟨1319543, by rfl⟩ : syracuseStep 1759391 = 2639087) B2639087
theorem B75915623 : Blo 972592 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B1172927 : Blo 972592 1172927 := bstep (se 1 (by rfl) ⟨879695, by rfl⟩ : syracuseStep 1172927 = 1759391) B1759391
theorem B3127805 : Blo 972592 3127805 := bstep (se 3 (by rfl) ⟨586463, by rfl⟩ : syracuseStep 3127805 = 1172927) B1172927
theorem B50610415 : Blo 972592 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B67480553 : Blo 972592 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B2085203 : Blo 972592 2085203 := bstep (se 1 (by rfl) ⟨1563902, by rfl⟩ : syracuseStep 2085203 = 3127805) B3127805
theorem B1390135 : Blo 972592 1390135 := bstep (se 1 (by rfl) ⟨1042601, by rfl⟩ : syracuseStep 1390135 = 2085203) B2085203
theorem B44987035 : Blo 972592 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B59982713 : Blo 972592 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B1853513 : Blo 972592 1853513 := bstep (se 2 (by rfl) ⟨695067, by rfl⟩ : syracuseStep 1853513 = 1390135) B1390135
theorem B39988475 : Blo 972592 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B1235675 : Blo 972592 1235675 := bstep (se 1 (by rfl) ⟨926756, by rfl⟩ : syracuseStep 1235675 = 1853513) B1853513
theorem B3295133 : Blo 972592 3295133 := bstep (se 3 (by rfl) ⟨617837, by rfl⟩ : syracuseStep 3295133 = 1235675) B1235675
theorem B26658983 : Blo 972592 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B2196755 : Blo 972592 2196755 := bstep (se 1 (by rfl) ⟨1647566, by rfl⟩ : syracuseStep 2196755 = 3295133) B3295133
theorem B71090621 : Blo 972592 71090621 := bstep (se 3 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 71090621 = 26658983) B26658983
theorem B47393747 : Blo 972592 47393747 := bstep (se 1 (by rfl) ⟨35545310, by rfl⟩ : syracuseStep 47393747 = 71090621) B71090621
theorem B1464503 : Blo 972592 1464503 := bstep (se 1 (by rfl) ⟨1098377, by rfl⟩ : syracuseStep 1464503 = 2196755) B2196755
theorem B31595831 : Blo 972592 31595831 := bstep (se 1 (by rfl) ⟨23696873, by rfl⟩ : syracuseStep 31595831 = 47393747) B47393747
theorem B976335 : Blo 972592 976335 := bstep (se 1 (by rfl) ⟨732251, by rfl⟩ : syracuseStep 976335 = 1464503) B1464503
theorem B21063887 : Blo 972592 21063887 := bstep (se 1 (by rfl) ⟨15797915, by rfl⟩ : syracuseStep 21063887 = 31595831) B31595831
theorem B14042591 : Blo 972592 14042591 := bstep (se 1 (by rfl) ⟨10531943, by rfl⟩ : syracuseStep 14042591 = 21063887) B21063887
theorem B9361727 : Blo 972592 9361727 := bstep (se 1 (by rfl) ⟨7021295, by rfl⟩ : syracuseStep 9361727 = 14042591) B14042591
theorem B6241151 : Blo 972592 6241151 := bstep (se 1 (by rfl) ⟨4680863, by rfl⟩ : syracuseStep 6241151 = 9361727) B9361727
theorem B16643069 : Blo 972592 16643069 := bstep (se 3 (by rfl) ⟨3120575, by rfl⟩ : syracuseStep 16643069 = 6241151) B6241151
theorem B11095379 : Blo 972592 11095379 := bstep (se 1 (by rfl) ⟨8321534, by rfl⟩ : syracuseStep 11095379 = 16643069) B16643069
theorem B7396919 : Blo 972592 7396919 := bstep (se 1 (by rfl) ⟨5547689, by rfl⟩ : syracuseStep 7396919 = 11095379) B11095379
theorem B4931279 : Blo 972592 4931279 := bstep (se 1 (by rfl) ⟨3698459, by rfl⟩ : syracuseStep 4931279 = 7396919) B7396919
theorem B3287519 : Blo 972592 3287519 := bstep (se 1 (by rfl) ⟨2465639, by rfl⟩ : syracuseStep 3287519 = 4931279) B4931279
theorem B2191679 : Blo 972592 2191679 := bstep (se 1 (by rfl) ⟨1643759, by rfl⟩ : syracuseStep 2191679 = 3287519) B3287519
theorem B1461119 : Blo 972592 1461119 := bstep (se 1 (by rfl) ⟨1095839, by rfl⟩ : syracuseStep 1461119 = 2191679) B2191679
theorem B974079 : Blo 972592 974079 := bstep (se 1 (by rfl) ⟨730559, by rfl⟩ : syracuseStep 974079 = 1461119) B1461119

theorem C0 (j : ℕ) (h1 : 243148 ≤ j) (h2 : j ≤ 243847) : Blo 972592 (4 * j + 3) := by
  interval_cases j
  · exact B972595
  · exact B972599
  · exact B972603
  · exact B972607
  · exact B972611
  · exact B972615
  · exact B972619
  · exact B972623
  · exact B972627
  · exact B972631
  · exact B972635
  · exact B972639
  · exact B972643
  · exact B972647
  · exact B972651
  · exact B972655
  · exact B972659
  · exact B972663
  · exact B972667
  · exact B972671
  · exact B972675
  · exact B972679
  · exact B972683
  · exact B972687
  · exact B972691
  · exact B972695
  · exact B972699
  · exact B972703
  · exact B972707
  · exact B972711
  · exact B972715
  · exact B972719
  · exact B972723
  · exact B972727
  · exact B972731
  · exact B972735
  · exact B972739
  · exact B972743
  · exact B972747
  · exact B972751
  · exact B972755
  · exact B972759
  · exact B972763
  · exact B972767
  · exact B972771
  · exact B972775
  · exact B972779
  · exact B972783
  · exact B972787
  · exact B972791
  · exact B972795
  · exact B972799
  · exact B972803
  · exact B972807
  · exact B972811
  · exact B972815
  · exact B972819
  · exact B972823
  · exact B972827
  · exact B972831
  · exact B972835
  · exact B972839
  · exact B972843
  · exact B972847
  · exact B972851
  · exact B972855
  · exact B972859
  · exact B972863
  · exact B972867
  · exact B972871
  · exact B972875
  · exact B972879
  · exact B972883
  · exact B972887
  · exact B972891
  · exact B972895
  · exact B972899
  · exact B972903
  · exact B972907
  · exact B972911
  · exact B972915
  · exact B972919
  · exact B972923
  · exact B972927
  · exact B972931
  · exact B972935
  · exact B972939
  · exact B972943
  · exact B972947
  · exact B972951
  · exact B972955
  · exact B972959
  · exact B972963
  · exact B972967
  · exact B972971
  · exact B972975
  · exact B972979
  · exact B972983
  · exact B972987
  · exact B972991
  · exact B972995
  · exact B972999
  · exact B973003
  · exact B973007
  · exact B973011
  · exact B973015
  · exact B973019
  · exact B973023
  · exact B973027
  · exact B973031
  · exact B973035
  · exact B973039
  · exact B973043
  · exact B973047
  · exact B973051
  · exact B973055
  · exact B973059
  · exact B973063
  · exact B973067
  · exact B973071
  · exact B973075
  · exact B973079
  · exact B973083
  · exact B973087
  · exact B973091
  · exact B973095
  · exact B973099
  · exact B973103
  · exact B973107
  · exact B973111
  · exact B973115
  · exact B973119
  · exact B973123
  · exact B973127
  · exact B973131
  · exact B973135
  · exact B973139
  · exact B973143
  · exact B973147
  · exact B973151
  · exact B973155
  · exact B973159
  · exact B973163
  · exact B973167
  · exact B973171
  · exact B973175
  · exact B973179
  · exact B973183
  · exact B973187
  · exact B973191
  · exact B973195
  · exact B973199
  · exact B973203
  · exact B973207
  · exact B973211
  · exact B973215
  · exact B973219
  · exact B973223
  · exact B973227
  · exact B973231
  · exact B973235
  · exact B973239
  · exact B973243
  · exact B973247
  · exact B973251
  · exact B973255
  · exact B973259
  · exact B973263
  · exact B973267
  · exact B973271
  · exact B973275
  · exact B973279
  · exact B973283
  · exact B973287
  · exact B973291
  · exact B973295
  · exact B973299
  · exact B973303
  · exact B973307
  · exact B973311
  · exact B973315
  · exact B973319
  · exact B973323
  · exact B973327
  · exact B973331
  · exact B973335
  · exact B973339
  · exact B973343
  · exact B973347
  · exact B973351
  · exact B973355
  · exact B973359
  · exact B973363
  · exact B973367
  · exact B973371
  · exact B973375
  · exact B973379
  · exact B973383
  · exact B973387
  · exact B973391
  · exact B973395
  · exact B973399
  · exact B973403
  · exact B973407
  · exact B973411
  · exact B973415
  · exact B973419
  · exact B973423
  · exact B973427
  · exact B973431
  · exact B973435
  · exact B973439
  · exact B973443
  · exact B973447
  · exact B973451
  · exact B973455
  · exact B973459
  · exact B973463
  · exact B973467
  · exact B973471
  · exact B973475
  · exact B973479
  · exact B973483
  · exact B973487
  · exact B973491
  · exact B973495
  · exact B973499
  · exact B973503
  · exact B973507
  · exact B973511
  · exact B973515
  · exact B973519
  · exact B973523
  · exact B973527
  · exact B973531
  · exact B973535
  · exact B973539
  · exact B973543
  · exact B973547
  · exact B973551
  · exact B973555
  · exact B973559
  · exact B973563
  · exact B973567
  · exact B973571
  · exact B973575
  · exact B973579
  · exact B973583
  · exact B973587
  · exact B973591
  · exact B973595
  · exact B973599
  · exact B973603
  · exact B973607
  · exact B973611
  · exact B973615
  · exact B973619
  · exact B973623
  · exact B973627
  · exact B973631
  · exact B973635
  · exact B973639
  · exact B973643
  · exact B973647
  · exact B973651
  · exact B973655
  · exact B973659
  · exact B973663
  · exact B973667
  · exact B973671
  · exact B973675
  · exact B973679
  · exact B973683
  · exact B973687
  · exact B973691
  · exact B973695
  · exact B973699
  · exact B973703
  · exact B973707
  · exact B973711
  · exact B973715
  · exact B973719
  · exact B973723
  · exact B973727
  · exact B973731
  · exact B973735
  · exact B973739
  · exact B973743
  · exact B973747
  · exact B973751
  · exact B973755
  · exact B973759
  · exact B973763
  · exact B973767
  · exact B973771
  · exact B973775
  · exact B973779
  · exact B973783
  · exact B973787
  · exact B973791
  · exact B973795
  · exact B973799
  · exact B973803
  · exact B973807
  · exact B973811
  · exact B973815
  · exact B973819
  · exact B973823
  · exact B973827
  · exact B973831
  · exact B973835
  · exact B973839
  · exact B973843
  · exact B973847
  · exact B973851
  · exact B973855
  · exact B973859
  · exact B973863
  · exact B973867
  · exact B973871
  · exact B973875
  · exact B973879
  · exact B973883
  · exact B973887
  · exact B973891
  · exact B973895
  · exact B973899
  · exact B973903
  · exact B973907
  · exact B973911
  · exact B973915
  · exact B973919
  · exact B973923
  · exact B973927
  · exact B973931
  · exact B973935
  · exact B973939
  · exact B973943
  · exact B973947
  · exact B973951
  · exact B973955
  · exact B973959
  · exact B973963
  · exact B973967
  · exact B973971
  · exact B973975
  · exact B973979
  · exact B973983
  · exact B973987
  · exact B973991
  · exact B973995
  · exact B973999
  · exact B974003
  · exact B974007
  · exact B974011
  · exact B974015
  · exact B974019
  · exact B974023
  · exact B974027
  · exact B974031
  · exact B974035
  · exact B974039
  · exact B974043
  · exact B974047
  · exact B974051
  · exact B974055
  · exact B974059
  · exact B974063
  · exact B974067
  · exact B974071
  · exact B974075
  · exact B974079
  · exact B974083
  · exact B974087
  · exact B974091
  · exact B974095
  · exact B974099
  · exact B974103
  · exact B974107
  · exact B974111
  · exact B974115
  · exact B974119
  · exact B974123
  · exact B974127
  · exact B974131
  · exact B974135
  · exact B974139
  · exact B974143
  · exact B974147
  · exact B974151
  · exact B974155
  · exact B974159
  · exact B974163
  · exact B974167
  · exact B974171
  · exact B974175
  · exact B974179
  · exact B974183
  · exact B974187
  · exact B974191
  · exact B974195
  · exact B974199
  · exact B974203
  · exact B974207
  · exact B974211
  · exact B974215
  · exact B974219
  · exact B974223
  · exact B974227
  · exact B974231
  · exact B974235
  · exact B974239
  · exact B974243
  · exact B974247
  · exact B974251
  · exact B974255
  · exact B974259
  · exact B974263
  · exact B974267
  · exact B974271
  · exact B974275
  · exact B974279
  · exact B974283
  · exact B974287
  · exact B974291
  · exact B974295
  · exact B974299
  · exact B974303
  · exact B974307
  · exact B974311
  · exact B974315
  · exact B974319
  · exact B974323
  · exact B974327
  · exact B974331
  · exact B974335
  · exact B974339
  · exact B974343
  · exact B974347
  · exact B974351
  · exact B974355
  · exact B974359
  · exact B974363
  · exact B974367
  · exact B974371
  · exact B974375
  · exact B974379
  · exact B974383
  · exact B974387
  · exact B974391
  · exact B974395
  · exact B974399
  · exact B974403
  · exact B974407
  · exact B974411
  · exact B974415
  · exact B974419
  · exact B974423
  · exact B974427
  · exact B974431
  · exact B974435
  · exact B974439
  · exact B974443
  · exact B974447
  · exact B974451
  · exact B974455
  · exact B974459
  · exact B974463
  · exact B974467
  · exact B974471
  · exact B974475
  · exact B974479
  · exact B974483
  · exact B974487
  · exact B974491
  · exact B974495
  · exact B974499
  · exact B974503
  · exact B974507
  · exact B974511
  · exact B974515
  · exact B974519
  · exact B974523
  · exact B974527
  · exact B974531
  · exact B974535
  · exact B974539
  · exact B974543
  · exact B974547
  · exact B974551
  · exact B974555
  · exact B974559
  · exact B974563
  · exact B974567
  · exact B974571
  · exact B974575
  · exact B974579
  · exact B974583
  · exact B974587
  · exact B974591
  · exact B974595
  · exact B974599
  · exact B974603
  · exact B974607
  · exact B974611
  · exact B974615
  · exact B974619
  · exact B974623
  · exact B974627
  · exact B974631
  · exact B974635
  · exact B974639
  · exact B974643
  · exact B974647
  · exact B974651
  · exact B974655
  · exact B974659
  · exact B974663
  · exact B974667
  · exact B974671
  · exact B974675
  · exact B974679
  · exact B974683
  · exact B974687
  · exact B974691
  · exact B974695
  · exact B974699
  · exact B974703
  · exact B974707
  · exact B974711
  · exact B974715
  · exact B974719
  · exact B974723
  · exact B974727
  · exact B974731
  · exact B974735
  · exact B974739
  · exact B974743
  · exact B974747
  · exact B974751
  · exact B974755
  · exact B974759
  · exact B974763
  · exact B974767
  · exact B974771
  · exact B974775
  · exact B974779
  · exact B974783
  · exact B974787
  · exact B974791
  · exact B974795
  · exact B974799
  · exact B974803
  · exact B974807
  · exact B974811
  · exact B974815
  · exact B974819
  · exact B974823
  · exact B974827
  · exact B974831
  · exact B974835
  · exact B974839
  · exact B974843
  · exact B974847
  · exact B974851
  · exact B974855
  · exact B974859
  · exact B974863
  · exact B974867
  · exact B974871
  · exact B974875
  · exact B974879
  · exact B974883
  · exact B974887
  · exact B974891
  · exact B974895
  · exact B974899
  · exact B974903
  · exact B974907
  · exact B974911
  · exact B974915
  · exact B974919
  · exact B974923
  · exact B974927
  · exact B974931
  · exact B974935
  · exact B974939
  · exact B974943
  · exact B974947
  · exact B974951
  · exact B974955
  · exact B974959
  · exact B974963
  · exact B974967
  · exact B974971
  · exact B974975
  · exact B974979
  · exact B974983
  · exact B974987
  · exact B974991
  · exact B974995
  · exact B974999
  · exact B975003
  · exact B975007
  · exact B975011
  · exact B975015
  · exact B975019
  · exact B975023
  · exact B975027
  · exact B975031
  · exact B975035
  · exact B975039
  · exact B975043
  · exact B975047
  · exact B975051
  · exact B975055
  · exact B975059
  · exact B975063
  · exact B975067
  · exact B975071
  · exact B975075
  · exact B975079
  · exact B975083
  · exact B975087
  · exact B975091
  · exact B975095
  · exact B975099
  · exact B975103
  · exact B975107
  · exact B975111
  · exact B975115
  · exact B975119
  · exact B975123
  · exact B975127
  · exact B975131
  · exact B975135
  · exact B975139
  · exact B975143
  · exact B975147
  · exact B975151
  · exact B975155
  · exact B975159
  · exact B975163
  · exact B975167
  · exact B975171
  · exact B975175
  · exact B975179
  · exact B975183
  · exact B975187
  · exact B975191
  · exact B975195
  · exact B975199
  · exact B975203
  · exact B975207
  · exact B975211
  · exact B975215
  · exact B975219
  · exact B975223
  · exact B975227
  · exact B975231
  · exact B975235
  · exact B975239
  · exact B975243
  · exact B975247
  · exact B975251
  · exact B975255
  · exact B975259
  · exact B975263
  · exact B975267
  · exact B975271
  · exact B975275
  · exact B975279
  · exact B975283
  · exact B975287
  · exact B975291
  · exact B975295
  · exact B975299
  · exact B975303
  · exact B975307
  · exact B975311
  · exact B975315
  · exact B975319
  · exact B975323
  · exact B975327
  · exact B975331
  · exact B975335
  · exact B975339
  · exact B975343
  · exact B975347
  · exact B975351
  · exact B975355
  · exact B975359
  · exact B975363
  · exact B975367
  · exact B975371
  · exact B975375
  · exact B975379
  · exact B975383
  · exact B975387
  · exact B975391

theorem C1 (j : ℕ) (h1 : 243848 ≤ j) (h2 : j ≤ 244147) : Blo 972592 (4 * j + 3) := by
  interval_cases j
  · exact B975395
  · exact B975399
  · exact B975403
  · exact B975407
  · exact B975411
  · exact B975415
  · exact B975419
  · exact B975423
  · exact B975427
  · exact B975431
  · exact B975435
  · exact B975439
  · exact B975443
  · exact B975447
  · exact B975451
  · exact B975455
  · exact B975459
  · exact B975463
  · exact B975467
  · exact B975471
  · exact B975475
  · exact B975479
  · exact B975483
  · exact B975487
  · exact B975491
  · exact B975495
  · exact B975499
  · exact B975503
  · exact B975507
  · exact B975511
  · exact B975515
  · exact B975519
  · exact B975523
  · exact B975527
  · exact B975531
  · exact B975535
  · exact B975539
  · exact B975543
  · exact B975547
  · exact B975551
  · exact B975555
  · exact B975559
  · exact B975563
  · exact B975567
  · exact B975571
  · exact B975575
  · exact B975579
  · exact B975583
  · exact B975587
  · exact B975591
  · exact B975595
  · exact B975599
  · exact B975603
  · exact B975607
  · exact B975611
  · exact B975615
  · exact B975619
  · exact B975623
  · exact B975627
  · exact B975631
  · exact B975635
  · exact B975639
  · exact B975643
  · exact B975647
  · exact B975651
  · exact B975655
  · exact B975659
  · exact B975663
  · exact B975667
  · exact B975671
  · exact B975675
  · exact B975679
  · exact B975683
  · exact B975687
  · exact B975691
  · exact B975695
  · exact B975699
  · exact B975703
  · exact B975707
  · exact B975711
  · exact B975715
  · exact B975719
  · exact B975723
  · exact B975727
  · exact B975731
  · exact B975735
  · exact B975739
  · exact B975743
  · exact B975747
  · exact B975751
  · exact B975755
  · exact B975759
  · exact B975763
  · exact B975767
  · exact B975771
  · exact B975775
  · exact B975779
  · exact B975783
  · exact B975787
  · exact B975791
  · exact B975795
  · exact B975799
  · exact B975803
  · exact B975807
  · exact B975811
  · exact B975815
  · exact B975819
  · exact B975823
  · exact B975827
  · exact B975831
  · exact B975835
  · exact B975839
  · exact B975843
  · exact B975847
  · exact B975851
  · exact B975855
  · exact B975859
  · exact B975863
  · exact B975867
  · exact B975871
  · exact B975875
  · exact B975879
  · exact B975883
  · exact B975887
  · exact B975891
  · exact B975895
  · exact B975899
  · exact B975903
  · exact B975907
  · exact B975911
  · exact B975915
  · exact B975919
  · exact B975923
  · exact B975927
  · exact B975931
  · exact B975935
  · exact B975939
  · exact B975943
  · exact B975947
  · exact B975951
  · exact B975955
  · exact B975959
  · exact B975963
  · exact B975967
  · exact B975971
  · exact B975975
  · exact B975979
  · exact B975983
  · exact B975987
  · exact B975991
  · exact B975995
  · exact B975999
  · exact B976003
  · exact B976007
  · exact B976011
  · exact B976015
  · exact B976019
  · exact B976023
  · exact B976027
  · exact B976031
  · exact B976035
  · exact B976039
  · exact B976043
  · exact B976047
  · exact B976051
  · exact B976055
  · exact B976059
  · exact B976063
  · exact B976067
  · exact B976071
  · exact B976075
  · exact B976079
  · exact B976083
  · exact B976087
  · exact B976091
  · exact B976095
  · exact B976099
  · exact B976103
  · exact B976107
  · exact B976111
  · exact B976115
  · exact B976119
  · exact B976123
  · exact B976127
  · exact B976131
  · exact B976135
  · exact B976139
  · exact B976143
  · exact B976147
  · exact B976151
  · exact B976155
  · exact B976159
  · exact B976163
  · exact B976167
  · exact B976171
  · exact B976175
  · exact B976179
  · exact B976183
  · exact B976187
  · exact B976191
  · exact B976195
  · exact B976199
  · exact B976203
  · exact B976207
  · exact B976211
  · exact B976215
  · exact B976219
  · exact B976223
  · exact B976227
  · exact B976231
  · exact B976235
  · exact B976239
  · exact B976243
  · exact B976247
  · exact B976251
  · exact B976255
  · exact B976259
  · exact B976263
  · exact B976267
  · exact B976271
  · exact B976275
  · exact B976279
  · exact B976283
  · exact B976287
  · exact B976291
  · exact B976295
  · exact B976299
  · exact B976303
  · exact B976307
  · exact B976311
  · exact B976315
  · exact B976319
  · exact B976323
  · exact B976327
  · exact B976331
  · exact B976335
  · exact B976339
  · exact B976343
  · exact B976347
  · exact B976351
  · exact B976355
  · exact B976359
  · exact B976363
  · exact B976367
  · exact B976371
  · exact B976375
  · exact B976379
  · exact B976383
  · exact B976387
  · exact B976391
  · exact B976395
  · exact B976399
  · exact B976403
  · exact B976407
  · exact B976411
  · exact B976415
  · exact B976419
  · exact B976423
  · exact B976427
  · exact B976431
  · exact B976435
  · exact B976439
  · exact B976443
  · exact B976447
  · exact B976451
  · exact B976455
  · exact B976459
  · exact B976463
  · exact B976467
  · exact B976471
  · exact B976475
  · exact B976479
  · exact B976483
  · exact B976487
  · exact B976491
  · exact B976495
  · exact B976499
  · exact B976503
  · exact B976507
  · exact B976511
  · exact B976515
  · exact B976519
  · exact B976523
  · exact B976527
  · exact B976531
  · exact B976535
  · exact B976539
  · exact B976543
  · exact B976547
  · exact B976551
  · exact B976555
  · exact B976559
  · exact B976563
  · exact B976567
  · exact B976571
  · exact B976575
  · exact B976579
  · exact B976583
  · exact B976587
  · exact B976591

theorem solution (m : ℕ) (hlo : 972592 ≤ m) (hhi : m ≤ 976592) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 243148 ≤ j := by omega
    have hj2 : j ≤ 244147 := by omega
    have hb : Blo 972592 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 243848 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
