-- Prove2me | solution 1 for syracuse_descends_range_483789_487789
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:07.641034+00:00
-- url     : https://prove2.me/submissions/2822046f-ba1b-4e94-b42c-924dcb40fede

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


theorem B589853 : Blo 483789 589853 := bbase (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) (by norm_num)
theorem B2457701 : Blo 483789 2457701 := bbase (se 4 (by rfl) ⟨230409, by rfl⟩ : syracuseStep 2457701 = 460819) (by norm_num)
theorem B819301 : Blo 483789 819301 := bbase (se 4 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 819301 = 153619) (by norm_num)
theorem B819389 : Blo 483789 819389 := bbase (se 3 (by rfl) ⟨153635, by rfl⟩ : syracuseStep 819389 = 307271) (by norm_num)
theorem B1474757 : Blo 483789 1474757 := bbase (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) (by norm_num)
theorem B1638629 : Blo 483789 1638629 := bbase (se 4 (by rfl) ⟨153621, by rfl⟩ : syracuseStep 1638629 = 307243) (by norm_num)
theorem B819517 : Blo 483789 819517 := bbase (se 3 (by rfl) ⟨153659, by rfl⟩ : syracuseStep 819517 = 307319) (by norm_num)
theorem B491869 : Blo 483789 491869 := bbase (se 3 (by rfl) ⟨92225, by rfl⟩ : syracuseStep 491869 = 184451) (by norm_num)
theorem B819605 : Blo 483789 819605 := bbase (se 6 (by rfl) ⟨19209, by rfl⟩ : syracuseStep 819605 = 38419) (by norm_num)
theorem B819733 : Blo 483789 819733 := bbase (se 6 (by rfl) ⟨19212, by rfl⟩ : syracuseStep 819733 = 38425) (by norm_num)
theorem B819821 : Blo 483789 819821 := bbase (se 3 (by rfl) ⟨153716, by rfl⟩ : syracuseStep 819821 = 307433) (by norm_num)
theorem B1639061 : Blo 483789 1639061 := bbase (se 6 (by rfl) ⟨38415, by rfl⟩ : syracuseStep 1639061 = 76831) (by norm_num)
theorem B688837 : Blo 483789 688837 := bbase (se 4 (by rfl) ⟨64578, by rfl⟩ : syracuseStep 688837 = 129157) (by norm_num)
theorem B819949 : Blo 483789 819949 := bbase (se 3 (by rfl) ⟨153740, by rfl⟩ : syracuseStep 819949 = 307481) (by norm_num)
theorem B820037 : Blo 483789 820037 := bbase (se 4 (by rfl) ⟨76878, by rfl⟩ : syracuseStep 820037 = 153757) (by norm_num)
theorem B820165 : Blo 483789 820165 := bbase (se 4 (by rfl) ⟨76890, by rfl⟩ : syracuseStep 820165 = 153781) (by norm_num)
theorem B918533 : Blo 483789 918533 := bbase (se 4 (by rfl) ⟨86112, by rfl⟩ : syracuseStep 918533 = 172225) (by norm_num)
theorem B623641 : Blo 483789 623641 := bbase (se 2 (by rfl) ⟨233865, by rfl⟩ : syracuseStep 623641 = 467731) (by norm_num)
theorem B820253 : Blo 483789 820253 := bbase (se 3 (by rfl) ⟨153797, by rfl⟩ : syracuseStep 820253 = 307595) (by norm_num)
theorem B1639493 : Blo 483789 1639493 := bbase (se 4 (by rfl) ⟨153702, by rfl⟩ : syracuseStep 1639493 = 307405) (by norm_num)
theorem B918677 : Blo 483789 918677 := bbase (se 6 (by rfl) ⟨21531, by rfl⟩ : syracuseStep 918677 = 43063) (by norm_num)
theorem B525461 : Blo 483789 525461 := bbase (se 6 (by rfl) ⟨12315, by rfl⟩ : syracuseStep 525461 = 24631) (by norm_num)
theorem B820381 : Blo 483789 820381 := bbase (se 3 (by rfl) ⟨153821, by rfl⟩ : syracuseStep 820381 = 307643) (by norm_num)
theorem B3114197 : Blo 483789 3114197 := bbase (se 7 (by rfl) ⟨36494, by rfl⟩ : syracuseStep 3114197 = 72989) (by norm_num)
theorem B492761 : Blo 483789 492761 := bbase (se 2 (by rfl) ⟨184785, by rfl⟩ : syracuseStep 492761 = 369571) (by norm_num)
theorem B820469 : Blo 483789 820469 := bbase (se 5 (by rfl) ⟨38459, by rfl⟩ : syracuseStep 820469 = 76919) (by norm_num)
theorem B689429 : Blo 483789 689429 := bbase (se 6 (by rfl) ⟨16158, by rfl⟩ : syracuseStep 689429 = 32317) (by norm_num)
theorem B689509 : Blo 483789 689509 := bbase (se 4 (by rfl) ⟨64641, by rfl⟩ : syracuseStep 689509 = 129283) (by norm_num)
theorem B1246565 : Blo 483789 1246565 := bbase (se 4 (by rfl) ⟨116865, by rfl⟩ : syracuseStep 1246565 = 233731) (by norm_num)
theorem B2458997 : Blo 483789 2458997 := bbase (se 5 (by rfl) ⟨115265, by rfl⟩ : syracuseStep 2458997 = 230531) (by norm_num)
theorem B820597 : Blo 483789 820597 := bbase (se 5 (by rfl) ⟨38465, by rfl⟩ : syracuseStep 820597 = 76931) (by norm_num)
theorem B984469 : Blo 483789 984469 := bbase (se 6 (by rfl) ⟨23073, by rfl⟩ : syracuseStep 984469 = 46147) (by norm_num)
theorem B2491813 : Blo 483789 2491813 := bbase (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) (by norm_num)
theorem B918965 : Blo 483789 918965 := bbase (se 5 (by rfl) ⟨43076, by rfl⟩ : syracuseStep 918965 = 86153) (by norm_num)
theorem B820685 : Blo 483789 820685 := bbase (se 3 (by rfl) ⟨153878, by rfl⟩ : syracuseStep 820685 = 307757) (by norm_num)
theorem B689629 : Blo 483789 689629 := bbase (se 3 (by rfl) ⟨129305, by rfl⟩ : syracuseStep 689629 = 258611) (by norm_num)
theorem B1639925 : Blo 483789 1639925 := bbase (se 5 (by rfl) ⟨76871, by rfl⟩ : syracuseStep 1639925 = 153743) (by norm_num)
theorem B689725 : Blo 483789 689725 := bbase (se 3 (by rfl) ⟨129323, by rfl⟩ : syracuseStep 689725 = 258647) (by norm_num)
theorem B919117 : Blo 483789 919117 := bbase (se 3 (by rfl) ⟨172334, by rfl⟩ : syracuseStep 919117 = 344669) (by norm_num)
theorem B820813 : Blo 483789 820813 := bbase (se 3 (by rfl) ⟨153902, by rfl⟩ : syracuseStep 820813 = 307805) (by norm_num)
theorem B2000533 : Blo 483789 2000533 := bbase (se 6 (by rfl) ⟨46887, by rfl⟩ : syracuseStep 2000533 = 93775) (by norm_num)
theorem B820901 : Blo 483789 820901 := bbase (se 4 (by rfl) ⟨76959, by rfl⟩ : syracuseStep 820901 = 153919) (by norm_num)
theorem B821029 : Blo 483789 821029 := bbase (se 4 (by rfl) ⟨76971, by rfl⟩ : syracuseStep 821029 = 153943) (by norm_num)
theorem B3508085 : Blo 483789 3508085 := bbase (se 5 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 3508085 = 328883) (by norm_num)
theorem B919421 : Blo 483789 919421 := bbase (se 3 (by rfl) ⟨172391, by rfl⟩ : syracuseStep 919421 = 344783) (by norm_num)
theorem B821117 : Blo 483789 821117 := bbase (se 3 (by rfl) ⟨153959, by rfl⟩ : syracuseStep 821117 = 307919) (by norm_num)
theorem B1640357 : Blo 483789 1640357 := bbase (se 4 (by rfl) ⟨153783, by rfl⟩ : syracuseStep 1640357 = 307567) (by norm_num)
theorem B821245 : Blo 483789 821245 := bbase (se 3 (by rfl) ⟨153983, by rfl⟩ : syracuseStep 821245 = 307967) (by norm_num)
theorem B690221 : Blo 483789 690221 := bbase (se 3 (by rfl) ⟨129416, by rfl⟩ : syracuseStep 690221 = 258833) (by norm_num)
theorem B821333 : Blo 483789 821333 := bbase (se 8 (by rfl) ⟨4812, by rfl⟩ : syracuseStep 821333 = 9625) (by norm_num)
theorem B1476725 : Blo 483789 1476725 := bbase (se 5 (by rfl) ⟨69221, by rfl⟩ : syracuseStep 1476725 = 138443) (by norm_num)
theorem B591997 : Blo 483789 591997 := bbase (se 3 (by rfl) ⟨110999, by rfl⟩ : syracuseStep 591997 = 221999) (by norm_num)
theorem B821461 : Blo 483789 821461 := bbase (se 7 (by rfl) ⟨9626, by rfl⟩ : syracuseStep 821461 = 19253) (by norm_num)
theorem B821549 : Blo 483789 821549 := bbase (se 3 (by rfl) ⟨154040, by rfl⟩ : syracuseStep 821549 = 308081) (by norm_num)
theorem B4983125 : Blo 483789 4983125 := bbase (se 10 (by rfl) ⟨7299, by rfl⟩ : syracuseStep 4983125 = 14599) (by norm_num)
theorem B1640789 : Blo 483789 1640789 := bbase (se 10 (by rfl) ⟨2403, by rfl⟩ : syracuseStep 1640789 = 4807) (by norm_num)
theorem B821677 : Blo 483789 821677 := bbase (se 3 (by rfl) ⟨154064, by rfl⟩ : syracuseStep 821677 = 308129) (by norm_num)
theorem B821765 : Blo 483789 821765 := bbase (se 4 (by rfl) ⟨77040, by rfl⟩ : syracuseStep 821765 = 154081) (by norm_num)
theorem B1968677 : Blo 483789 1968677 := bbase (se 4 (by rfl) ⟨184563, by rfl⟩ : syracuseStep 1968677 = 369127) (by norm_num)
theorem B690773 : Blo 483789 690773 := bbase (se 8 (by rfl) ⟨4047, by rfl⟩ : syracuseStep 690773 = 8095) (by norm_num)
theorem B920173 : Blo 483789 920173 := bbase (se 3 (by rfl) ⟨172532, by rfl⟩ : syracuseStep 920173 = 345065) (by norm_num)
theorem B2460293 : Blo 483789 2460293 := bbase (se 4 (by rfl) ⟨230652, by rfl⟩ : syracuseStep 2460293 = 461305) (by norm_num)
theorem B821893 : Blo 483789 821893 := bbase (se 4 (by rfl) ⟨77052, by rfl⟩ : syracuseStep 821893 = 154105) (by norm_num)
theorem B985765 : Blo 483789 985765 := bbase (se 4 (by rfl) ⟨92415, by rfl⟩ : syracuseStep 985765 = 184831) (by norm_num)
theorem B494245 : Blo 483789 494245 := bbase (se 4 (by rfl) ⟨46335, by rfl⟩ : syracuseStep 494245 = 92671) (by norm_num)
theorem B985813 : Blo 483789 985813 := bbase (se 7 (by rfl) ⟨11552, by rfl⟩ : syracuseStep 985813 = 23105) (by norm_num)
theorem B821981 : Blo 483789 821981 := bbase (se 3 (by rfl) ⟨154121, by rfl⟩ : syracuseStep 821981 = 308243) (by norm_num)
theorem B920317 : Blo 483789 920317 := bbase (se 3 (by rfl) ⟨172559, by rfl⟩ : syracuseStep 920317 = 345119) (by norm_num)
theorem B1641221 : Blo 483789 1641221 := bbase (se 4 (by rfl) ⟨153864, by rfl⟩ : syracuseStep 1641221 = 307729) (by norm_num)
theorem B822109 : Blo 483789 822109 := bbase (se 3 (by rfl) ⟨154145, by rfl⟩ : syracuseStep 822109 = 308291) (by norm_num)
theorem B920477 : Blo 483789 920477 := bbase (se 3 (by rfl) ⟨172589, by rfl⟩ : syracuseStep 920477 = 345179) (by norm_num)
theorem B822197 : Blo 483789 822197 := bbase (se 5 (by rfl) ⟨38540, by rfl⟩ : syracuseStep 822197 = 77081) (by norm_num)
theorem B1313813 : Blo 483789 1313813 := bbase (se 6 (by rfl) ⟨30792, by rfl⟩ : syracuseStep 1313813 = 61585) (by norm_num)
theorem B920621 : Blo 483789 920621 := bbase (se 3 (by rfl) ⟨172616, by rfl⟩ : syracuseStep 920621 = 345233) (by norm_num)
theorem B822325 : Blo 483789 822325 := bbase (se 5 (by rfl) ⟨38546, by rfl⟩ : syracuseStep 822325 = 77093) (by norm_num)
theorem B822413 : Blo 483789 822413 := bbase (se 3 (by rfl) ⟨154202, by rfl⟩ : syracuseStep 822413 = 308405) (by norm_num)
theorem B2067605 : Blo 483789 2067605 := bbase (se 6 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 2067605 = 96919) (by norm_num)
theorem B1641653 : Blo 483789 1641653 := bbase (se 5 (by rfl) ⟨76952, by rfl⟩ : syracuseStep 1641653 = 153905) (by norm_num)
theorem B822541 : Blo 483789 822541 := bbase (se 3 (by rfl) ⟨154226, by rfl⟩ : syracuseStep 822541 = 308453) (by norm_num)
theorem B691525 : Blo 483789 691525 := bbase (se 4 (by rfl) ⟨64830, by rfl⟩ : syracuseStep 691525 = 129661) (by norm_num)
theorem B920909 : Blo 483789 920909 := bbase (se 3 (by rfl) ⟨172670, by rfl⟩ : syracuseStep 920909 = 345341) (by norm_num)
theorem B822629 : Blo 483789 822629 := bbase (se 4 (by rfl) ⟨77121, by rfl⟩ : syracuseStep 822629 = 154243) (by norm_num)
theorem B1314245 : Blo 483789 1314245 := bbase (se 4 (by rfl) ⟨123210, by rfl⟩ : syracuseStep 1314245 = 246421) (by norm_num)
theorem B921061 : Blo 483789 921061 := bbase (se 4 (by rfl) ⟨86349, by rfl⟩ : syracuseStep 921061 = 172699) (by norm_num)
theorem B822757 : Blo 483789 822757 := bbase (se 4 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 822757 = 154267) (by norm_num)
theorem B1379861 : Blo 483789 1379861 := bbase (se 6 (by rfl) ⟨32340, by rfl⟩ : syracuseStep 1379861 = 64681) (by norm_num)
theorem B4165141 : Blo 483789 4165141 := bbase (se 6 (by rfl) ⟨97620, by rfl⟩ : syracuseStep 4165141 = 195241) (by norm_num)
theorem B2428453 : Blo 483789 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B1838645 : Blo 483789 1838645 := bbase (se 5 (by rfl) ⟨86186, by rfl⟩ : syracuseStep 1838645 = 172373) (by norm_num)
theorem B1248821 : Blo 483789 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B822845 : Blo 483789 822845 := bbase (se 3 (by rfl) ⟨154283, by rfl⟩ : syracuseStep 822845 = 308567) (by norm_num)
theorem B1642085 : Blo 483789 1642085 := bbase (se 4 (by rfl) ⟨153945, by rfl⟩ : syracuseStep 1642085 = 307891) (by norm_num)
theorem B2756213 : Blo 483789 2756213 := bbase (se 5 (by rfl) ⟨129197, by rfl⟩ : syracuseStep 2756213 = 258395) (by norm_num)
theorem B822973 : Blo 483789 822973 := bbase (se 3 (by rfl) ⟨154307, by rfl⟩ : syracuseStep 822973 = 308615) (by norm_num)
theorem B921365 : Blo 483789 921365 := bbase (se 6 (by rfl) ⟨21594, by rfl⟩ : syracuseStep 921365 = 43189) (by norm_num)
theorem B823061 : Blo 483789 823061 := bbase (se 6 (by rfl) ⟨19290, by rfl⟩ : syracuseStep 823061 = 38581) (by norm_num)
theorem B986917 : Blo 483789 986917 := bbase (se 4 (by rfl) ⟨92523, by rfl⟩ : syracuseStep 986917 = 185047) (by norm_num)
theorem B1838933 : Blo 483789 1838933 := bbase (se 9 (by rfl) ⟨5387, by rfl⟩ : syracuseStep 1838933 = 10775) (by norm_num)
theorem B757621 : Blo 483789 757621 := bbase (se 5 (by rfl) ⟨35513, by rfl⟩ : syracuseStep 757621 = 71027) (by norm_num)
theorem B2461589 : Blo 483789 2461589 := bbase (se 6 (by rfl) ⟨57693, by rfl⟩ : syracuseStep 2461589 = 115387) (by norm_num)
theorem B1642517 : Blo 483789 1642517 := bbase (se 6 (by rfl) ⟨38496, by rfl⟩ : syracuseStep 1642517 = 76993) (by norm_num)
theorem B5050421 : Blo 483789 5050421 := bbase (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) (by norm_num)
theorem B692317 : Blo 483789 692317 := bbase (se 3 (by rfl) ⟨129809, by rfl⟩ : syracuseStep 692317 = 259619) (by norm_num)
theorem B790661 : Blo 483789 790661 := bbase (se 4 (by rfl) ⟨74124, by rfl⟩ : syracuseStep 790661 = 148249) (by norm_num)
theorem B1315045 : Blo 483789 1315045 := bbase (se 4 (by rfl) ⟨123285, by rfl⟩ : syracuseStep 1315045 = 246571) (by norm_num)
theorem B692653 : Blo 483789 692653 := bbase (se 3 (by rfl) ⟨129872, by rfl⟩ : syracuseStep 692653 = 259745) (by norm_num)
theorem B1642949 : Blo 483789 1642949 := bbase (se 4 (by rfl) ⟨154026, by rfl⟩ : syracuseStep 1642949 = 308053) (by norm_num)
theorem B922117 : Blo 483789 922117 := bbase (se 4 (by rfl) ⟨86448, by rfl⟩ : syracuseStep 922117 = 172897) (by norm_num)
theorem B3674645 : Blo 483789 3674645 := bbase (se 6 (by rfl) ⟨86124, by rfl⟩ : syracuseStep 3674645 = 172249) (by norm_num)
theorem B692869 : Blo 483789 692869 := bbase (se 4 (by rfl) ⟨64956, by rfl⟩ : syracuseStep 692869 = 129913) (by norm_num)
theorem B922261 : Blo 483789 922261 := bbase (se 6 (by rfl) ⟨21615, by rfl⟩ : syracuseStep 922261 = 43231) (by norm_num)
theorem B1217173 : Blo 483789 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B1381045 : Blo 483789 1381045 := bbase (se 5 (by rfl) ⟨64736, by rfl⟩ : syracuseStep 1381045 = 129473) (by norm_num)
theorem B725693 : Blo 483789 725693 := bbase (se 3 (by rfl) ⟨136067, by rfl⟩ : syracuseStep 725693 = 272135) (by norm_num)
theorem B725717 : Blo 483789 725717 := bbase (se 7 (by rfl) ⟨8504, by rfl⟩ : syracuseStep 725717 = 17009) (by norm_num)
theorem B725741 : Blo 483789 725741 := bbase (se 3 (by rfl) ⟨136076, by rfl⟩ : syracuseStep 725741 = 272153) (by norm_num)
theorem B725765 : Blo 483789 725765 := bbase (se 4 (by rfl) ⟨68040, by rfl⟩ : syracuseStep 725765 = 136081) (by norm_num)
theorem B725789 : Blo 483789 725789 := bbase (se 3 (by rfl) ⟨136085, by rfl⟩ : syracuseStep 725789 = 272171) (by norm_num)
theorem B725813 : Blo 483789 725813 := bbase (se 5 (by rfl) ⟨34022, by rfl⟩ : syracuseStep 725813 = 68045) (by norm_num)
theorem B922421 : Blo 483789 922421 := bbase (se 5 (by rfl) ⟨43238, by rfl⟩ : syracuseStep 922421 = 86477) (by norm_num)
theorem B725837 : Blo 483789 725837 := bbase (se 3 (by rfl) ⟨136094, by rfl⟩ : syracuseStep 725837 = 272189) (by norm_num)
theorem B1381205 : Blo 483789 1381205 := bbase (se 9 (by rfl) ⟨4046, by rfl⟩ : syracuseStep 1381205 = 8093) (by norm_num)
theorem B725861 : Blo 483789 725861 := bbase (se 4 (by rfl) ⟨68049, by rfl⟩ : syracuseStep 725861 = 136099) (by norm_num)
theorem B1643381 : Blo 483789 1643381 := bbase (se 5 (by rfl) ⟨77033, by rfl⟩ : syracuseStep 1643381 = 154067) (by norm_num)
theorem B725885 : Blo 483789 725885 := bbase (se 3 (by rfl) ⟨136103, by rfl⟩ : syracuseStep 725885 = 272207) (by norm_num)
theorem B2069381 : Blo 483789 2069381 := bbase (se 4 (by rfl) ⟨194004, by rfl⟩ : syracuseStep 2069381 = 388009) (by norm_num)
theorem B922501 : Blo 483789 922501 := bbase (se 4 (by rfl) ⟨86484, by rfl⟩ : syracuseStep 922501 = 172969) (by norm_num)
theorem B725909 : Blo 483789 725909 := bbase (se 6 (by rfl) ⟨17013, by rfl⟩ : syracuseStep 725909 = 34027) (by norm_num)
theorem B725933 : Blo 483789 725933 := bbase (se 3 (by rfl) ⟨136112, by rfl⟩ : syracuseStep 725933 = 272225) (by norm_num)
theorem B725957 : Blo 483789 725957 := bbase (se 4 (by rfl) ⟨68058, by rfl⟩ : syracuseStep 725957 = 136117) (by norm_num)
theorem B922565 : Blo 483789 922565 := bbase (se 4 (by rfl) ⟨86490, by rfl⟩ : syracuseStep 922565 = 172981) (by norm_num)
theorem B725981 : Blo 483789 725981 := bbase (se 3 (by rfl) ⟨136121, by rfl⟩ : syracuseStep 725981 = 272243) (by norm_num)
theorem B726005 : Blo 483789 726005 := bbase (se 5 (by rfl) ⟨34031, by rfl⟩ : syracuseStep 726005 = 68063) (by norm_num)
theorem B1840117 : Blo 483789 1840117 := bbase (se 5 (by rfl) ⟨86255, by rfl⟩ : syracuseStep 1840117 = 172511) (by norm_num)
theorem B693245 : Blo 483789 693245 := bbase (se 3 (by rfl) ⟨129983, by rfl⟩ : syracuseStep 693245 = 259967) (by norm_num)
theorem B726029 : Blo 483789 726029 := bbase (se 3 (by rfl) ⟨136130, by rfl⟩ : syracuseStep 726029 = 272261) (by norm_num)
theorem B726053 : Blo 483789 726053 := bbase (se 4 (by rfl) ⟨68067, by rfl⟩ : syracuseStep 726053 = 136135) (by norm_num)
theorem B726077 : Blo 483789 726077 := bbase (se 3 (by rfl) ⟨136139, by rfl⟩ : syracuseStep 726077 = 272279) (by norm_num)
theorem B1381445 : Blo 483789 1381445 := bbase (se 4 (by rfl) ⟨129510, by rfl⟩ : syracuseStep 1381445 = 259021) (by norm_num)
theorem B726101 : Blo 483789 726101 := bbase (se 8 (by rfl) ⟨4254, by rfl⟩ : syracuseStep 726101 = 8509) (by norm_num)
theorem B726125 : Blo 483789 726125 := bbase (se 3 (by rfl) ⟨136148, by rfl⟩ : syracuseStep 726125 = 272297) (by norm_num)
theorem B2069621 : Blo 483789 2069621 := bbase (se 5 (by rfl) ⟨97013, by rfl⟩ : syracuseStep 2069621 = 194027) (by norm_num)
theorem B726149 : Blo 483789 726149 := bbase (se 4 (by rfl) ⟨68076, by rfl⟩ : syracuseStep 726149 = 136153) (by norm_num)
theorem B726173 : Blo 483789 726173 := bbase (se 3 (by rfl) ⟨136157, by rfl⟩ : syracuseStep 726173 = 272315) (by norm_num)
theorem B2462885 : Blo 483789 2462885 := bbase (se 4 (by rfl) ⟨230895, by rfl⟩ : syracuseStep 2462885 = 461791) (by norm_num)
theorem B726197 : Blo 483789 726197 := bbase (se 5 (by rfl) ⟨34040, by rfl⟩ : syracuseStep 726197 = 68081) (by norm_num)
theorem B726221 : Blo 483789 726221 := bbase (se 3 (by rfl) ⟨136166, by rfl⟩ : syracuseStep 726221 = 272333) (by norm_num)
theorem B726245 : Blo 483789 726245 := bbase (se 4 (by rfl) ⟨68085, by rfl⟩ : syracuseStep 726245 = 136171) (by norm_num)
theorem B922853 : Blo 483789 922853 := bbase (se 4 (by rfl) ⟨86517, by rfl⟩ : syracuseStep 922853 = 173035) (by norm_num)
theorem B726269 : Blo 483789 726269 := bbase (se 3 (by rfl) ⟨136175, by rfl⟩ : syracuseStep 726269 = 272351) (by norm_num)
theorem B1381637 : Blo 483789 1381637 := bbase (se 4 (by rfl) ⟨129528, by rfl⟩ : syracuseStep 1381637 = 259057) (by norm_num)
theorem B726293 : Blo 483789 726293 := bbase (se 6 (by rfl) ⟨17022, by rfl⟩ : syracuseStep 726293 = 34045) (by norm_num)
theorem B1840421 : Blo 483789 1840421 := bbase (se 4 (by rfl) ⟨172539, by rfl⟩ : syracuseStep 1840421 = 345079) (by norm_num)
theorem B1643813 : Blo 483789 1643813 := bbase (se 4 (by rfl) ⟨154107, by rfl⟩ : syracuseStep 1643813 = 308215) (by norm_num)
theorem B726317 : Blo 483789 726317 := bbase (se 3 (by rfl) ⟨136184, by rfl⟩ : syracuseStep 726317 = 272369) (by norm_num)
theorem B726341 : Blo 483789 726341 := bbase (se 4 (by rfl) ⟨68094, by rfl⟩ : syracuseStep 726341 = 136189) (by norm_num)
theorem B726365 : Blo 483789 726365 := bbase (se 3 (by rfl) ⟨136193, by rfl⟩ : syracuseStep 726365 = 272387) (by norm_num)
theorem B726389 : Blo 483789 726389 := bbase (se 5 (by rfl) ⟨34049, by rfl⟩ : syracuseStep 726389 = 68099) (by norm_num)
theorem B923005 : Blo 483789 923005 := bbase (se 3 (by rfl) ⟨173063, by rfl⟩ : syracuseStep 923005 = 346127) (by norm_num)
theorem B726413 : Blo 483789 726413 := bbase (se 3 (by rfl) ⟨136202, by rfl⟩ : syracuseStep 726413 = 272405) (by norm_num)
theorem B726437 : Blo 483789 726437 := bbase (se 4 (by rfl) ⟨68103, by rfl⟩ : syracuseStep 726437 = 136207) (by norm_num)
theorem B726461 : Blo 483789 726461 := bbase (se 3 (by rfl) ⟨136211, by rfl⟩ : syracuseStep 726461 = 272423) (by norm_num)
theorem B726485 : Blo 483789 726485 := bbase (se 7 (by rfl) ⟨8513, by rfl⟩ : syracuseStep 726485 = 17027) (by norm_num)
theorem B2004437 : Blo 483789 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B4167125 : Blo 483789 4167125 := bbase (se 7 (by rfl) ⟨48833, by rfl⟩ : syracuseStep 4167125 = 97667) (by norm_num)
theorem B726509 : Blo 483789 726509 := bbase (se 3 (by rfl) ⟨136220, by rfl⟩ : syracuseStep 726509 = 272441) (by norm_num)
theorem B726533 : Blo 483789 726533 := bbase (se 4 (by rfl) ⟨68112, by rfl⟩ : syracuseStep 726533 = 136225) (by norm_num)
theorem B726557 : Blo 483789 726557 := bbase (se 3 (by rfl) ⟨136229, by rfl⟩ : syracuseStep 726557 = 272459) (by norm_num)
theorem B726581 : Blo 483789 726581 := bbase (se 5 (by rfl) ⟨34058, by rfl⟩ : syracuseStep 726581 = 68117) (by norm_num)
theorem B726605 : Blo 483789 726605 := bbase (se 3 (by rfl) ⟨136238, by rfl⟩ : syracuseStep 726605 = 272477) (by norm_num)
theorem B726629 : Blo 483789 726629 := bbase (se 4 (by rfl) ⟨68121, by rfl⟩ : syracuseStep 726629 = 136243) (by norm_num)
theorem B726653 : Blo 483789 726653 := bbase (se 3 (by rfl) ⟨136247, by rfl⟩ : syracuseStep 726653 = 272495) (by norm_num)
theorem B726677 : Blo 483789 726677 := bbase (se 6 (by rfl) ⟨17031, by rfl⟩ : syracuseStep 726677 = 34063) (by norm_num)
theorem B726701 : Blo 483789 726701 := bbase (se 3 (by rfl) ⟨136256, by rfl⟩ : syracuseStep 726701 = 272513) (by norm_num)
theorem B923309 : Blo 483789 923309 := bbase (se 3 (by rfl) ⟨173120, by rfl⟩ : syracuseStep 923309 = 346241) (by norm_num)
theorem B726725 : Blo 483789 726725 := bbase (se 4 (by rfl) ⟨68130, by rfl⟩ : syracuseStep 726725 = 136261) (by norm_num)
theorem B1644245 : Blo 483789 1644245 := bbase (se 7 (by rfl) ⟨19268, by rfl⟩ : syracuseStep 1644245 = 38537) (by norm_num)
theorem B726749 : Blo 483789 726749 := bbase (se 3 (by rfl) ⟨136265, by rfl⟩ : syracuseStep 726749 = 272531) (by norm_num)
theorem B726773 : Blo 483789 726773 := bbase (se 5 (by rfl) ⟨34067, by rfl⟩ : syracuseStep 726773 = 68135) (by norm_num)
theorem B2332421 : Blo 483789 2332421 := bbase (se 4 (by rfl) ⟨218664, by rfl⟩ : syracuseStep 2332421 = 437329) (by norm_num)
theorem B726797 : Blo 483789 726797 := bbase (se 3 (by rfl) ⟨136274, by rfl⟩ : syracuseStep 726797 = 272549) (by norm_num)
theorem B726821 : Blo 483789 726821 := bbase (se 4 (by rfl) ⟨68139, by rfl⟩ : syracuseStep 726821 = 136279) (by norm_num)
theorem B726845 : Blo 483789 726845 := bbase (se 3 (by rfl) ⟨136283, by rfl⟩ : syracuseStep 726845 = 272567) (by norm_num)
theorem B726869 : Blo 483789 726869 := bbase (se 9 (by rfl) ⟨2129, by rfl⟩ : syracuseStep 726869 = 4259) (by norm_num)
theorem B4659029 : Blo 483789 4659029 := bbase (se 9 (by rfl) ⟨13649, by rfl⟩ : syracuseStep 4659029 = 27299) (by norm_num)
theorem B726893 : Blo 483789 726893 := bbase (se 3 (by rfl) ⟨136292, by rfl⟩ : syracuseStep 726893 = 272585) (by norm_num)
theorem B726917 : Blo 483789 726917 := bbase (se 4 (by rfl) ⟨68148, by rfl⟩ : syracuseStep 726917 = 136297) (by norm_num)
theorem B726941 : Blo 483789 726941 := bbase (se 3 (by rfl) ⟨136301, by rfl⟩ : syracuseStep 726941 = 272603) (by norm_num)
theorem B726965 : Blo 483789 726965 := bbase (se 5 (by rfl) ⟨34076, by rfl⟩ : syracuseStep 726965 = 68153) (by norm_num)
theorem B1054661 : Blo 483789 1054661 := bbase (se 4 (by rfl) ⟨98874, by rfl⟩ : syracuseStep 1054661 = 197749) (by norm_num)
theorem B726989 : Blo 483789 726989 := bbase (se 3 (by rfl) ⟨136310, by rfl⟩ : syracuseStep 726989 = 272621) (by norm_num)
theorem B727013 : Blo 483789 727013 := bbase (se 4 (by rfl) ⟨68157, by rfl⟩ : syracuseStep 727013 = 136315) (by norm_num)
theorem B727037 : Blo 483789 727037 := bbase (se 3 (by rfl) ⟨136319, by rfl⟩ : syracuseStep 727037 = 272639) (by norm_num)
theorem B727061 : Blo 483789 727061 := bbase (se 6 (by rfl) ⟨17040, by rfl⟩ : syracuseStep 727061 = 34081) (by norm_num)
theorem B727085 : Blo 483789 727085 := bbase (se 3 (by rfl) ⟨136328, by rfl⟩ : syracuseStep 727085 = 272657) (by norm_num)
theorem B727109 : Blo 483789 727109 := bbase (se 4 (by rfl) ⟨68166, by rfl⟩ : syracuseStep 727109 = 136333) (by norm_num)
theorem B727133 : Blo 483789 727133 := bbase (se 3 (by rfl) ⟨136337, by rfl⟩ : syracuseStep 727133 = 272675) (by norm_num)
theorem B727157 : Blo 483789 727157 := bbase (se 5 (by rfl) ⟨34085, by rfl⟩ : syracuseStep 727157 = 68171) (by norm_num)
theorem B1644677 : Blo 483789 1644677 := bbase (se 4 (by rfl) ⟨154188, by rfl⟩ : syracuseStep 1644677 = 308377) (by norm_num)
theorem B727181 : Blo 483789 727181 := bbase (se 3 (by rfl) ⟨136346, by rfl⟩ : syracuseStep 727181 = 272693) (by norm_num)
theorem B727205 : Blo 483789 727205 := bbase (se 4 (by rfl) ⟨68175, by rfl⟩ : syracuseStep 727205 = 136351) (by norm_num)
theorem B727229 : Blo 483789 727229 := bbase (se 3 (by rfl) ⟨136355, by rfl⟩ : syracuseStep 727229 = 272711) (by norm_num)
theorem B727253 : Blo 483789 727253 := bbase (se 7 (by rfl) ⟨8522, by rfl⟩ : syracuseStep 727253 = 17045) (by norm_num)
theorem B2627797 : Blo 483789 2627797 := bbase (se 7 (by rfl) ⟨30794, by rfl⟩ : syracuseStep 2627797 = 61589) (by norm_num)
theorem B1382629 : Blo 483789 1382629 := bbase (se 4 (by rfl) ⟨129621, by rfl⟩ : syracuseStep 1382629 = 259243) (by norm_num)
theorem B727277 : Blo 483789 727277 := bbase (se 3 (by rfl) ⟨136364, by rfl⟩ : syracuseStep 727277 = 272729) (by norm_num)
theorem B727301 : Blo 483789 727301 := bbase (se 4 (by rfl) ⟨68184, by rfl⟩ : syracuseStep 727301 = 136369) (by norm_num)
theorem B727325 : Blo 483789 727325 := bbase (se 3 (by rfl) ⟨136373, by rfl⟩ : syracuseStep 727325 = 272747) (by norm_num)
theorem B727349 : Blo 483789 727349 := bbase (se 5 (by rfl) ⟨34094, by rfl⟩ : syracuseStep 727349 = 68189) (by norm_num)
theorem B727373 : Blo 483789 727373 := bbase (se 3 (by rfl) ⟨136382, by rfl⟩ : syracuseStep 727373 = 272765) (by norm_num)
theorem B727397 : Blo 483789 727397 := bbase (se 4 (by rfl) ⟨68193, by rfl⟩ : syracuseStep 727397 = 136387) (by norm_num)
theorem B727421 : Blo 483789 727421 := bbase (se 3 (by rfl) ⟨136391, by rfl⟩ : syracuseStep 727421 = 272783) (by norm_num)
theorem B727445 : Blo 483789 727445 := bbase (se 6 (by rfl) ⟨17049, by rfl⟩ : syracuseStep 727445 = 34099) (by norm_num)
theorem B924061 : Blo 483789 924061 := bbase (se 3 (by rfl) ⟨173261, by rfl⟩ : syracuseStep 924061 = 346523) (by norm_num)
theorem B2365861 : Blo 483789 2365861 := bbase (se 4 (by rfl) ⟨221799, by rfl⟩ : syracuseStep 2365861 = 443599) (by norm_num)
theorem B727469 : Blo 483789 727469 := bbase (se 3 (by rfl) ⟨136400, by rfl⟩ : syracuseStep 727469 = 272801) (by norm_num)
theorem B2464181 : Blo 483789 2464181 := bbase (se 5 (by rfl) ⟨115508, by rfl⟩ : syracuseStep 2464181 = 231017) (by norm_num)
theorem B727493 : Blo 483789 727493 := bbase (se 4 (by rfl) ⟨68202, by rfl⟩ : syracuseStep 727493 = 136405) (by norm_num)
theorem B727517 : Blo 483789 727517 := bbase (se 3 (by rfl) ⟨136409, by rfl⟩ : syracuseStep 727517 = 272819) (by norm_num)
theorem B727541 : Blo 483789 727541 := bbase (se 5 (by rfl) ⟨34103, by rfl⟩ : syracuseStep 727541 = 68207) (by norm_num)
theorem B727565 : Blo 483789 727565 := bbase (se 3 (by rfl) ⟨136418, by rfl⟩ : syracuseStep 727565 = 272837) (by norm_num)
theorem B727589 : Blo 483789 727589 := bbase (se 4 (by rfl) ⟨68211, by rfl⟩ : syracuseStep 727589 = 136423) (by norm_num)
theorem B924205 : Blo 483789 924205 := bbase (se 3 (by rfl) ⟨173288, by rfl⟩ : syracuseStep 924205 = 346577) (by norm_num)
theorem B1645109 : Blo 483789 1645109 := bbase (se 5 (by rfl) ⟨77114, by rfl⟩ : syracuseStep 1645109 = 154229) (by norm_num)
theorem B629305 : Blo 483789 629305 := bbase (se 2 (by rfl) ⟨235989, by rfl⟩ : syracuseStep 629305 = 471979) (by norm_num)
theorem B727613 : Blo 483789 727613 := bbase (se 3 (by rfl) ⟨136427, by rfl⟩ : syracuseStep 727613 = 272855) (by norm_num)
theorem B727637 : Blo 483789 727637 := bbase (se 8 (by rfl) ⟨4263, by rfl⟩ : syracuseStep 727637 = 8527) (by norm_num)
theorem B727661 : Blo 483789 727661 := bbase (se 3 (by rfl) ⟨136436, by rfl⟩ : syracuseStep 727661 = 272873) (by norm_num)
theorem B727685 : Blo 483789 727685 := bbase (se 4 (by rfl) ⟨68220, by rfl⟩ : syracuseStep 727685 = 136441) (by norm_num)
theorem B498317 : Blo 483789 498317 := bbase (se 3 (by rfl) ⟨93434, by rfl⟩ : syracuseStep 498317 = 186869) (by norm_num)
theorem B727709 : Blo 483789 727709 := bbase (se 3 (by rfl) ⟨136445, by rfl⟩ : syracuseStep 727709 = 272891) (by norm_num)
theorem B727733 : Blo 483789 727733 := bbase (se 5 (by rfl) ⟨34112, by rfl⟩ : syracuseStep 727733 = 68225) (by norm_num)
theorem B727757 : Blo 483789 727757 := bbase (se 3 (by rfl) ⟨136454, by rfl⟩ : syracuseStep 727757 = 272909) (by norm_num)
theorem B924365 : Blo 483789 924365 := bbase (se 3 (by rfl) ⟨173318, by rfl⟩ : syracuseStep 924365 = 346637) (by norm_num)
theorem B727781 : Blo 483789 727781 := bbase (se 4 (by rfl) ⟨68229, by rfl⟩ : syracuseStep 727781 = 136459) (by norm_num)
theorem B629497 : Blo 483789 629497 := bbase (se 2 (by rfl) ⟨236061, by rfl⟩ : syracuseStep 629497 = 472123) (by norm_num)
theorem B727805 : Blo 483789 727805 := bbase (se 3 (by rfl) ⟨136463, by rfl⟩ : syracuseStep 727805 = 272927) (by norm_num)
theorem B727829 : Blo 483789 727829 := bbase (se 6 (by rfl) ⟨17058, by rfl⟩ : syracuseStep 727829 = 34117) (by norm_num)
theorem B727853 : Blo 483789 727853 := bbase (se 3 (by rfl) ⟨136472, by rfl⟩ : syracuseStep 727853 = 272945) (by norm_num)
theorem B727877 : Blo 483789 727877 := bbase (se 4 (by rfl) ⟨68238, by rfl⟩ : syracuseStep 727877 = 136477) (by norm_num)
theorem B727901 : Blo 483789 727901 := bbase (se 3 (by rfl) ⟨136481, by rfl⟩ : syracuseStep 727901 = 272963) (by norm_num)
theorem B924509 : Blo 483789 924509 := bbase (se 3 (by rfl) ⟨173345, by rfl⟩ : syracuseStep 924509 = 346691) (by norm_num)
theorem B727925 : Blo 483789 727925 := bbase (se 5 (by rfl) ⟨34121, by rfl⟩ : syracuseStep 727925 = 68243) (by norm_num)
theorem B727949 : Blo 483789 727949 := bbase (se 3 (by rfl) ⟨136490, by rfl⟩ : syracuseStep 727949 = 272981) (by norm_num)
theorem B6986645 : Blo 483789 6986645 := bbase (se 6 (by rfl) ⟨163749, by rfl⟩ : syracuseStep 6986645 = 327499) (by norm_num)
theorem B727973 : Blo 483789 727973 := bbase (se 4 (by rfl) ⟨68247, by rfl⟩ : syracuseStep 727973 = 136495) (by norm_num)
theorem B727997 : Blo 483789 727997 := bbase (se 3 (by rfl) ⟨136499, by rfl⟩ : syracuseStep 727997 = 272999) (by norm_num)
theorem B728021 : Blo 483789 728021 := bbase (se 7 (by rfl) ⟨8531, by rfl⟩ : syracuseStep 728021 = 17063) (by norm_num)
theorem B1645541 : Blo 483789 1645541 := bbase (se 4 (by rfl) ⟨154269, by rfl⟩ : syracuseStep 1645541 = 308539) (by norm_num)
theorem B728045 : Blo 483789 728045 := bbase (se 3 (by rfl) ⟨136508, by rfl⟩ : syracuseStep 728045 = 273017) (by norm_num)
theorem B728069 : Blo 483789 728069 := bbase (se 4 (by rfl) ⟨68256, by rfl⟩ : syracuseStep 728069 = 136513) (by norm_num)
theorem B728093 : Blo 483789 728093 := bbase (se 3 (by rfl) ⟨136517, by rfl⟩ : syracuseStep 728093 = 273035) (by norm_num)
theorem B1088549 : Blo 483789 1088549 := bbase (se 4 (by rfl) ⟨102051, by rfl⟩ : syracuseStep 1088549 = 204103) (by norm_num)
theorem B728117 : Blo 483789 728117 := bbase (se 5 (by rfl) ⟨34130, by rfl⟩ : syracuseStep 728117 = 68261) (by norm_num)
theorem B728141 : Blo 483789 728141 := bbase (se 3 (by rfl) ⟨136526, by rfl⟩ : syracuseStep 728141 = 273053) (by norm_num)
theorem B728165 : Blo 483789 728165 := bbase (se 4 (by rfl) ⟨68265, by rfl⟩ : syracuseStep 728165 = 136531) (by norm_num)
theorem B1088621 : Blo 483789 1088621 := bbase (se 3 (by rfl) ⟨204116, by rfl⟩ : syracuseStep 1088621 = 408233) (by norm_num)
theorem B728189 : Blo 483789 728189 := bbase (se 3 (by rfl) ⟨136535, by rfl⟩ : syracuseStep 728189 = 273071) (by norm_num)
theorem B924797 : Blo 483789 924797 := bbase (se 3 (by rfl) ⟨173399, by rfl⟩ : syracuseStep 924797 = 346799) (by norm_num)
theorem B728213 : Blo 483789 728213 := bbase (se 6 (by rfl) ⟨17067, by rfl⟩ : syracuseStep 728213 = 34135) (by norm_num)
theorem B728237 : Blo 483789 728237 := bbase (se 3 (by rfl) ⟨136544, by rfl⟩ : syracuseStep 728237 = 273089) (by norm_num)
theorem B1088693 : Blo 483789 1088693 := bbase (se 5 (by rfl) ⟨51032, by rfl⟩ : syracuseStep 1088693 = 102065) (by norm_num)
theorem B3153077 : Blo 483789 3153077 := bbase (se 5 (by rfl) ⟨147800, by rfl⟩ : syracuseStep 3153077 = 295601) (by norm_num)
theorem B728261 : Blo 483789 728261 := bbase (se 4 (by rfl) ⟨68274, by rfl⟩ : syracuseStep 728261 = 136549) (by norm_num)
theorem B728285 : Blo 483789 728285 := bbase (se 3 (by rfl) ⟨136553, by rfl⟩ : syracuseStep 728285 = 273107) (by norm_num)
theorem B1023205 : Blo 483789 1023205 := bbase (se 4 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 1023205 = 191851) (by norm_num)
theorem B728309 : Blo 483789 728309 := bbase (se 5 (by rfl) ⟨34139, by rfl⟩ : syracuseStep 728309 = 68279) (by norm_num)
theorem B1088765 : Blo 483789 1088765 := bbase (se 3 (by rfl) ⟨204143, by rfl⟩ : syracuseStep 1088765 = 408287) (by norm_num)
theorem B728333 : Blo 483789 728333 := bbase (se 3 (by rfl) ⟨136562, by rfl⟩ : syracuseStep 728333 = 273125) (by norm_num)
theorem B924949 : Blo 483789 924949 := bbase (se 6 (by rfl) ⟨21678, by rfl⟩ : syracuseStep 924949 = 43357) (by norm_num)
theorem B728357 : Blo 483789 728357 := bbase (se 4 (by rfl) ⟨68283, by rfl⟩ : syracuseStep 728357 = 136567) (by norm_num)
theorem B1383733 : Blo 483789 1383733 := bbase (se 5 (by rfl) ⟨64862, by rfl⟩ : syracuseStep 1383733 = 129725) (by norm_num)
theorem B728381 : Blo 483789 728381 := bbase (se 3 (by rfl) ⟨136571, by rfl⟩ : syracuseStep 728381 = 273143) (by norm_num)
theorem B1088837 : Blo 483789 1088837 := bbase (se 4 (by rfl) ⟨102078, by rfl⟩ : syracuseStep 1088837 = 204157) (by norm_num)
theorem B728405 : Blo 483789 728405 := bbase (se 11 (by rfl) ⟨533, by rfl⟩ : syracuseStep 728405 = 1067) (by norm_num)
theorem B2071909 : Blo 483789 2071909 := bbase (se 4 (by rfl) ⟨194241, by rfl⟩ : syracuseStep 2071909 = 388483) (by norm_num)
theorem B1842533 : Blo 483789 1842533 := bbase (se 4 (by rfl) ⟨172737, by rfl⟩ : syracuseStep 1842533 = 345475) (by norm_num)
theorem B728429 : Blo 483789 728429 := bbase (se 3 (by rfl) ⟨136580, by rfl⟩ : syracuseStep 728429 = 273161) (by norm_num)
theorem B728453 : Blo 483789 728453 := bbase (se 4 (by rfl) ⟨68292, by rfl⟩ : syracuseStep 728453 = 136585) (by norm_num)
theorem B1088909 : Blo 483789 1088909 := bbase (se 3 (by rfl) ⟨204170, by rfl⟩ : syracuseStep 1088909 = 408341) (by norm_num)
theorem B1645973 : Blo 483789 1645973 := bbase (se 6 (by rfl) ⟨38577, by rfl⟩ : syracuseStep 1645973 = 77155) (by norm_num)
theorem B728477 : Blo 483789 728477 := bbase (se 3 (by rfl) ⟨136589, by rfl⟩ : syracuseStep 728477 = 273179) (by norm_num)
theorem B728501 : Blo 483789 728501 := bbase (se 5 (by rfl) ⟨34148, by rfl⟩ : syracuseStep 728501 = 68297) (by norm_num)
theorem B728525 : Blo 483789 728525 := bbase (se 3 (by rfl) ⟨136598, by rfl⟩ : syracuseStep 728525 = 273197) (by norm_num)
theorem B1088981 : Blo 483789 1088981 := bbase (se 7 (by rfl) ⟨12761, by rfl⟩ : syracuseStep 1088981 = 25523) (by norm_num)
theorem B728549 : Blo 483789 728549 := bbase (se 4 (by rfl) ⟨68301, by rfl⟩ : syracuseStep 728549 = 136603) (by norm_num)
theorem B728573 : Blo 483789 728573 := bbase (se 3 (by rfl) ⟨136607, by rfl⟩ : syracuseStep 728573 = 273215) (by norm_num)
theorem B3317269 : Blo 483789 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B728597 : Blo 483789 728597 := bbase (se 6 (by rfl) ⟨17076, by rfl⟩ : syracuseStep 728597 = 34153) (by norm_num)
theorem B1089053 : Blo 483789 1089053 := bbase (se 3 (by rfl) ⟨204197, by rfl⟩ : syracuseStep 1089053 = 408395) (by norm_num)
theorem B728621 : Blo 483789 728621 := bbase (se 3 (by rfl) ⟨136616, by rfl⟩ : syracuseStep 728621 = 273233) (by norm_num)
theorem B728645 : Blo 483789 728645 := bbase (se 4 (by rfl) ⟨68310, by rfl⟩ : syracuseStep 728645 = 136621) (by norm_num)
theorem B925253 : Blo 483789 925253 := bbase (se 4 (by rfl) ⟨86742, by rfl⟩ : syracuseStep 925253 = 173485) (by norm_num)
theorem B3513941 : Blo 483789 3513941 := bbase (se 8 (by rfl) ⟨20589, by rfl⟩ : syracuseStep 3513941 = 41179) (by norm_num)
theorem B728669 : Blo 483789 728669 := bbase (se 3 (by rfl) ⟨136625, by rfl⟩ : syracuseStep 728669 = 273251) (by norm_num)
theorem B1089125 : Blo 483789 1089125 := bbase (se 4 (by rfl) ⟨102105, by rfl⟩ : syracuseStep 1089125 = 204211) (by norm_num)
theorem B728693 : Blo 483789 728693 := bbase (se 5 (by rfl) ⟨34157, by rfl⟩ : syracuseStep 728693 = 68315) (by norm_num)
theorem B1842821 : Blo 483789 1842821 := bbase (se 4 (by rfl) ⟨172764, by rfl⟩ : syracuseStep 1842821 = 345529) (by norm_num)
theorem B728717 : Blo 483789 728717 := bbase (se 3 (by rfl) ⟨136634, by rfl⟩ : syracuseStep 728717 = 273269) (by norm_num)
theorem B728741 : Blo 483789 728741 := bbase (se 4 (by rfl) ⟨68319, by rfl⟩ : syracuseStep 728741 = 136639) (by norm_num)
theorem B1089197 : Blo 483789 1089197 := bbase (se 3 (by rfl) ⟨204224, by rfl⟩ : syracuseStep 1089197 = 408449) (by norm_num)
theorem B728765 : Blo 483789 728765 := bbase (se 3 (by rfl) ⟨136643, by rfl⟩ : syracuseStep 728765 = 273287) (by norm_num)
theorem B2465477 : Blo 483789 2465477 := bbase (se 4 (by rfl) ⟨231138, by rfl⟩ : syracuseStep 2465477 = 462277) (by norm_num)
theorem B18620117 : Blo 483789 18620117 := bbase (se 7 (by rfl) ⟨218204, by rfl⟩ : syracuseStep 18620117 = 436409) (by norm_num)
theorem B728789 : Blo 483789 728789 := bbase (se 7 (by rfl) ⟨8540, by rfl⟩ : syracuseStep 728789 = 17081) (by norm_num)
theorem B728813 : Blo 483789 728813 := bbase (se 3 (by rfl) ⟨136652, by rfl⟩ : syracuseStep 728813 = 273305) (by norm_num)
theorem B1089269 : Blo 483789 1089269 := bbase (se 5 (by rfl) ⟨51059, by rfl⟩ : syracuseStep 1089269 = 102119) (by norm_num)
theorem B728837 : Blo 483789 728837 := bbase (se 4 (by rfl) ⟨68328, by rfl⟩ : syracuseStep 728837 = 136657) (by norm_num)
theorem B728861 : Blo 483789 728861 := bbase (se 3 (by rfl) ⟨136661, by rfl⟩ : syracuseStep 728861 = 273323) (by norm_num)
theorem B728885 : Blo 483789 728885 := bbase (se 5 (by rfl) ⟨34166, by rfl⟩ : syracuseStep 728885 = 68333) (by norm_num)
theorem B1089341 : Blo 483789 1089341 := bbase (se 3 (by rfl) ⟨204251, by rfl⟩ : syracuseStep 1089341 = 408503) (by norm_num)
theorem B728909 : Blo 483789 728909 := bbase (se 3 (by rfl) ⟨136670, by rfl⟩ : syracuseStep 728909 = 273341) (by norm_num)
theorem B728933 : Blo 483789 728933 := bbase (se 4 (by rfl) ⟨68337, by rfl⟩ : syracuseStep 728933 = 136675) (by norm_num)
theorem B728957 : Blo 483789 728957 := bbase (se 3 (by rfl) ⟨136679, by rfl⟩ : syracuseStep 728957 = 273359) (by norm_num)
theorem B1089413 : Blo 483789 1089413 := bbase (se 4 (by rfl) ⟨102132, by rfl⟩ : syracuseStep 1089413 = 204265) (by norm_num)
theorem B728981 : Blo 483789 728981 := bbase (se 6 (by rfl) ⟨17085, by rfl⟩ : syracuseStep 728981 = 34171) (by norm_num)
theorem B729005 : Blo 483789 729005 := bbase (se 3 (by rfl) ⟨136688, by rfl⟩ : syracuseStep 729005 = 273377) (by norm_num)
theorem B729029 : Blo 483789 729029 := bbase (se 4 (by rfl) ⟨68346, by rfl⟩ : syracuseStep 729029 = 136693) (by norm_num)
theorem B1089485 : Blo 483789 1089485 := bbase (se 3 (by rfl) ⟨204278, by rfl⟩ : syracuseStep 1089485 = 408557) (by norm_num)
theorem B729053 : Blo 483789 729053 := bbase (se 3 (by rfl) ⟨136697, by rfl⟩ : syracuseStep 729053 = 273395) (by norm_num)
theorem B729077 : Blo 483789 729077 := bbase (se 5 (by rfl) ⟨34175, by rfl⟩ : syracuseStep 729077 = 68351) (by norm_num)
theorem B729101 : Blo 483789 729101 := bbase (se 3 (by rfl) ⟨136706, by rfl⟩ : syracuseStep 729101 = 273413) (by norm_num)
theorem B1089557 : Blo 483789 1089557 := bbase (se 6 (by rfl) ⟨25536, by rfl⟩ : syracuseStep 1089557 = 51073) (by norm_num)
theorem B729125 : Blo 483789 729125 := bbase (se 4 (by rfl) ⟨68355, by rfl⟩ : syracuseStep 729125 = 136711) (by norm_num)
theorem B729149 : Blo 483789 729149 := bbase (se 3 (by rfl) ⟨136715, by rfl⟩ : syracuseStep 729149 = 273431) (by norm_num)
theorem B729173 : Blo 483789 729173 := bbase (se 8 (by rfl) ⟨4272, by rfl⟩ : syracuseStep 729173 = 8545) (by norm_num)
theorem B1089629 : Blo 483789 1089629 := bbase (se 3 (by rfl) ⟨204305, by rfl⟩ : syracuseStep 1089629 = 408611) (by norm_num)
theorem B729197 : Blo 483789 729197 := bbase (se 3 (by rfl) ⟨136724, by rfl⟩ : syracuseStep 729197 = 273449) (by norm_num)
theorem B729221 : Blo 483789 729221 := bbase (se 4 (by rfl) ⟨68364, by rfl⟩ : syracuseStep 729221 = 136729) (by norm_num)
theorem B729245 : Blo 483789 729245 := bbase (se 3 (by rfl) ⟨136733, by rfl⟩ : syracuseStep 729245 = 273467) (by norm_num)
theorem B1089701 : Blo 483789 1089701 := bbase (se 4 (by rfl) ⟨102159, by rfl⟩ : syracuseStep 1089701 = 204319) (by norm_num)
theorem B729269 : Blo 483789 729269 := bbase (se 5 (by rfl) ⟨34184, by rfl⟩ : syracuseStep 729269 = 68369) (by norm_num)
theorem B729293 : Blo 483789 729293 := bbase (se 3 (by rfl) ⟨136742, by rfl⟩ : syracuseStep 729293 = 273485) (by norm_num)
theorem B729317 : Blo 483789 729317 := bbase (se 4 (by rfl) ⟨68373, by rfl⟩ : syracuseStep 729317 = 136747) (by norm_num)
theorem B1089773 : Blo 483789 1089773 := bbase (se 3 (by rfl) ⟨204332, by rfl⟩ : syracuseStep 1089773 = 408665) (by norm_num)
theorem B729341 : Blo 483789 729341 := bbase (se 3 (by rfl) ⟨136751, by rfl⟩ : syracuseStep 729341 = 273503) (by norm_num)
theorem B729365 : Blo 483789 729365 := bbase (se 6 (by rfl) ⟨17094, by rfl⟩ : syracuseStep 729365 = 34189) (by norm_num)
theorem B729389 : Blo 483789 729389 := bbase (se 3 (by rfl) ⟨136760, by rfl⟩ : syracuseStep 729389 = 273521) (by norm_num)
theorem B1089845 : Blo 483789 1089845 := bbase (se 5 (by rfl) ⟨51086, by rfl⟩ : syracuseStep 1089845 = 102173) (by norm_num)
theorem B926005 : Blo 483789 926005 := bbase (se 5 (by rfl) ⟨43406, by rfl⟩ : syracuseStep 926005 = 86813) (by norm_num)
theorem B729413 : Blo 483789 729413 := bbase (se 4 (by rfl) ⟨68382, by rfl⟩ : syracuseStep 729413 = 136765) (by norm_num)
theorem B729437 : Blo 483789 729437 := bbase (se 3 (by rfl) ⟨136769, by rfl⟩ : syracuseStep 729437 = 273539) (by norm_num)
theorem B729461 : Blo 483789 729461 := bbase (se 5 (by rfl) ⟨34193, by rfl⟩ : syracuseStep 729461 = 68387) (by norm_num)
theorem B1089917 : Blo 483789 1089917 := bbase (se 3 (by rfl) ⟨204359, by rfl⟩ : syracuseStep 1089917 = 408719) (by norm_num)
theorem B631181 : Blo 483789 631181 := bbase (se 3 (by rfl) ⟨118346, by rfl⟩ : syracuseStep 631181 = 236693) (by norm_num)
theorem B729485 : Blo 483789 729485 := bbase (se 3 (by rfl) ⟨136778, by rfl⟩ : syracuseStep 729485 = 273557) (by norm_num)
theorem B729509 : Blo 483789 729509 := bbase (se 4 (by rfl) ⟨68391, by rfl⟩ : syracuseStep 729509 = 136783) (by norm_num)
theorem B729533 : Blo 483789 729533 := bbase (se 3 (by rfl) ⟨136787, by rfl⟩ : syracuseStep 729533 = 273575) (by norm_num)
theorem B1089989 : Blo 483789 1089989 := bbase (se 4 (by rfl) ⟨102186, by rfl⟩ : syracuseStep 1089989 = 204373) (by norm_num)
theorem B729557 : Blo 483789 729557 := bbase (se 7 (by rfl) ⟨8549, by rfl⟩ : syracuseStep 729557 = 17099) (by norm_num)
theorem B729581 : Blo 483789 729581 := bbase (se 3 (by rfl) ⟨136796, by rfl⟩ : syracuseStep 729581 = 273593) (by norm_num)
theorem B729605 : Blo 483789 729605 := bbase (se 4 (by rfl) ⟨68400, by rfl⟩ : syracuseStep 729605 = 136801) (by norm_num)
theorem B1090061 : Blo 483789 1090061 := bbase (se 3 (by rfl) ⟨204386, by rfl⟩ : syracuseStep 1090061 = 408773) (by norm_num)
theorem B729629 : Blo 483789 729629 := bbase (se 3 (by rfl) ⟨136805, by rfl⟩ : syracuseStep 729629 = 273611) (by norm_num)
theorem B729653 : Blo 483789 729653 := bbase (se 5 (by rfl) ⟨34202, by rfl⟩ : syracuseStep 729653 = 68405) (by norm_num)
theorem B729677 : Blo 483789 729677 := bbase (se 3 (by rfl) ⟨136814, by rfl⟩ : syracuseStep 729677 = 273629) (by norm_num)
theorem B1090133 : Blo 483789 1090133 := bbase (se 8 (by rfl) ⟨6387, by rfl⟩ : syracuseStep 1090133 = 12775) (by norm_num)
theorem B729701 : Blo 483789 729701 := bbase (se 4 (by rfl) ⟨68409, by rfl⟩ : syracuseStep 729701 = 136819) (by norm_num)
theorem B729725 : Blo 483789 729725 := bbase (se 3 (by rfl) ⟨136823, by rfl⟩ : syracuseStep 729725 = 273647) (by norm_num)
theorem B729749 : Blo 483789 729749 := bbase (se 6 (by rfl) ⟨17103, by rfl⟩ : syracuseStep 729749 = 34207) (by norm_num)
theorem B1090205 : Blo 483789 1090205 := bbase (se 3 (by rfl) ⟨204413, by rfl⟩ : syracuseStep 1090205 = 408827) (by norm_num)
theorem B729773 : Blo 483789 729773 := bbase (se 3 (by rfl) ⟨136832, by rfl⟩ : syracuseStep 729773 = 273665) (by norm_num)
theorem B729797 : Blo 483789 729797 := bbase (se 4 (by rfl) ⟨68418, by rfl⟩ : syracuseStep 729797 = 136837) (by norm_num)
theorem B729821 : Blo 483789 729821 := bbase (se 3 (by rfl) ⟨136841, by rfl⟩ : syracuseStep 729821 = 273683) (by norm_num)
theorem B1090277 : Blo 483789 1090277 := bbase (se 4 (by rfl) ⟨102213, by rfl⟩ : syracuseStep 1090277 = 204427) (by norm_num)
theorem B729845 : Blo 483789 729845 := bbase (se 5 (by rfl) ⟨34211, by rfl⟩ : syracuseStep 729845 = 68423) (by norm_num)
theorem B729869 : Blo 483789 729869 := bbase (se 3 (by rfl) ⟨136850, by rfl⟩ : syracuseStep 729869 = 273701) (by norm_num)
theorem B1385237 : Blo 483789 1385237 := bbase (se 6 (by rfl) ⟨32466, by rfl⟩ : syracuseStep 1385237 = 64933) (by norm_num)
theorem B1844005 : Blo 483789 1844005 := bbase (se 4 (by rfl) ⟨172875, by rfl⟩ : syracuseStep 1844005 = 345751) (by norm_num)
theorem B729893 : Blo 483789 729893 := bbase (se 4 (by rfl) ⟨68427, by rfl⟩ : syracuseStep 729893 = 136855) (by norm_num)
theorem B1090349 : Blo 483789 1090349 := bbase (se 3 (by rfl) ⟨204440, by rfl⟩ : syracuseStep 1090349 = 408881) (by norm_num)
theorem B2073397 : Blo 483789 2073397 := bbase (se 5 (by rfl) ⟨97190, by rfl⟩ : syracuseStep 2073397 = 194381) (by norm_num)
theorem B729917 : Blo 483789 729917 := bbase (se 3 (by rfl) ⟨136859, by rfl⟩ : syracuseStep 729917 = 273719) (by norm_num)
theorem B2073413 : Blo 483789 2073413 := bbase (se 4 (by rfl) ⟨194382, by rfl⟩ : syracuseStep 2073413 = 388765) (by norm_num)
theorem B729941 : Blo 483789 729941 := bbase (se 9 (by rfl) ⟨2138, by rfl⟩ : syracuseStep 729941 = 4277) (by norm_num)
theorem B729965 : Blo 483789 729965 := bbase (se 3 (by rfl) ⟨136868, by rfl⟩ : syracuseStep 729965 = 273737) (by norm_num)
theorem B1090421 : Blo 483789 1090421 := bbase (se 5 (by rfl) ⟨51113, by rfl⟩ : syracuseStep 1090421 = 102227) (by norm_num)
theorem B729989 : Blo 483789 729989 := bbase (se 4 (by rfl) ⟨68436, by rfl⟩ : syracuseStep 729989 = 136873) (by norm_num)
theorem B730013 : Blo 483789 730013 := bbase (se 3 (by rfl) ⟨136877, by rfl⟩ : syracuseStep 730013 = 273755) (by norm_num)
theorem B730037 : Blo 483789 730037 := bbase (se 5 (by rfl) ⟨34220, by rfl⟩ : syracuseStep 730037 = 68441) (by norm_num)
theorem B1090493 : Blo 483789 1090493 := bbase (se 3 (by rfl) ⟨204467, by rfl⟩ : syracuseStep 1090493 = 408935) (by norm_num)
theorem B730061 : Blo 483789 730061 := bbase (se 3 (by rfl) ⟨136886, by rfl⟩ : syracuseStep 730061 = 273773) (by norm_num)
theorem B2466773 : Blo 483789 2466773 := bbase (se 7 (by rfl) ⟨28907, by rfl⟩ : syracuseStep 2466773 = 57815) (by norm_num)
theorem B730085 : Blo 483789 730085 := bbase (se 4 (by rfl) ⟨68445, by rfl⟩ : syracuseStep 730085 = 136891) (by norm_num)
theorem B730109 : Blo 483789 730109 := bbase (se 3 (by rfl) ⟨136895, by rfl⟩ : syracuseStep 730109 = 273791) (by norm_num)
theorem B1090565 : Blo 483789 1090565 := bbase (se 4 (by rfl) ⟨102240, by rfl⟩ : syracuseStep 1090565 = 204481) (by norm_num)
theorem B730133 : Blo 483789 730133 := bbase (se 6 (by rfl) ⟨17112, by rfl⟩ : syracuseStep 730133 = 34225) (by norm_num)
theorem B730157 : Blo 483789 730157 := bbase (se 3 (by rfl) ⟨136904, by rfl⟩ : syracuseStep 730157 = 273809) (by norm_num)
theorem B730181 : Blo 483789 730181 := bbase (se 4 (by rfl) ⟨68454, by rfl⟩ : syracuseStep 730181 = 136909) (by norm_num)
theorem B1090637 : Blo 483789 1090637 := bbase (se 3 (by rfl) ⟨204494, by rfl⟩ : syracuseStep 1090637 = 408989) (by norm_num)
theorem B1844309 : Blo 483789 1844309 := bbase (se 8 (by rfl) ⟨10806, by rfl⟩ : syracuseStep 1844309 = 21613) (by norm_num)
theorem B730205 : Blo 483789 730205 := bbase (se 3 (by rfl) ⟨136913, by rfl⟩ : syracuseStep 730205 = 273827) (by norm_num)
theorem B730229 : Blo 483789 730229 := bbase (se 5 (by rfl) ⟨34229, by rfl⟩ : syracuseStep 730229 = 68459) (by norm_num)
theorem B730253 : Blo 483789 730253 := bbase (se 3 (by rfl) ⟨136922, by rfl⟩ : syracuseStep 730253 = 273845) (by norm_num)
theorem B1090709 : Blo 483789 1090709 := bbase (se 6 (by rfl) ⟨25563, by rfl⟩ : syracuseStep 1090709 = 51127) (by norm_num)
theorem B730277 : Blo 483789 730277 := bbase (se 4 (by rfl) ⟨68463, by rfl⟩ : syracuseStep 730277 = 136927) (by norm_num)
theorem B730301 : Blo 483789 730301 := bbase (se 3 (by rfl) ⟨136931, by rfl⟩ : syracuseStep 730301 = 273863) (by norm_num)
theorem B730325 : Blo 483789 730325 := bbase (se 7 (by rfl) ⟨8558, by rfl⟩ : syracuseStep 730325 = 17117) (by norm_num)
theorem B1090781 : Blo 483789 1090781 := bbase (se 3 (by rfl) ⟨204521, by rfl⟩ : syracuseStep 1090781 = 409043) (by norm_num)
theorem B730349 : Blo 483789 730349 := bbase (se 3 (by rfl) ⟨136940, by rfl⟩ : syracuseStep 730349 = 273881) (by norm_num)
theorem B730373 : Blo 483789 730373 := bbase (se 4 (by rfl) ⟨68472, by rfl⟩ : syracuseStep 730373 = 136945) (by norm_num)
theorem B730397 : Blo 483789 730397 := bbase (se 3 (by rfl) ⟨136949, by rfl⟩ : syracuseStep 730397 = 273899) (by norm_num)
theorem B1090853 : Blo 483789 1090853 := bbase (se 4 (by rfl) ⟨102267, by rfl⟩ : syracuseStep 1090853 = 204535) (by norm_num)
theorem B730421 : Blo 483789 730421 := bbase (se 5 (by rfl) ⟨34238, by rfl⟩ : syracuseStep 730421 = 68477) (by norm_num)
theorem B730445 : Blo 483789 730445 := bbase (se 3 (by rfl) ⟨136958, by rfl⟩ : syracuseStep 730445 = 273917) (by norm_num)
theorem B730469 : Blo 483789 730469 := bbase (se 4 (by rfl) ⟨68481, by rfl⟩ : syracuseStep 730469 = 136963) (by norm_num)
theorem B1090925 : Blo 483789 1090925 := bbase (se 3 (by rfl) ⟨204548, by rfl⟩ : syracuseStep 1090925 = 409097) (by norm_num)
theorem B730493 : Blo 483789 730493 := bbase (se 3 (by rfl) ⟨136967, by rfl⟩ : syracuseStep 730493 = 273935) (by norm_num)
theorem B730517 : Blo 483789 730517 := bbase (se 6 (by rfl) ⟨17121, by rfl⟩ : syracuseStep 730517 = 34243) (by norm_num)
theorem B730541 : Blo 483789 730541 := bbase (se 3 (by rfl) ⟨136976, by rfl⟩ : syracuseStep 730541 = 273953) (by norm_num)
theorem B1090997 : Blo 483789 1090997 := bbase (se 5 (by rfl) ⟨51140, by rfl⟩ : syracuseStep 1090997 = 102281) (by norm_num)
theorem B730565 : Blo 483789 730565 := bbase (se 4 (by rfl) ⟨68490, by rfl⟩ : syracuseStep 730565 = 136981) (by norm_num)
theorem B730589 : Blo 483789 730589 := bbase (se 3 (by rfl) ⟨136985, by rfl⟩ : syracuseStep 730589 = 273971) (by norm_num)
theorem B730613 : Blo 483789 730613 := bbase (se 5 (by rfl) ⟨34247, by rfl⟩ : syracuseStep 730613 = 68495) (by norm_num)
theorem B1091069 : Blo 483789 1091069 := bbase (se 3 (by rfl) ⟨204575, by rfl⟩ : syracuseStep 1091069 = 409151) (by norm_num)
theorem B730637 : Blo 483789 730637 := bbase (se 3 (by rfl) ⟨136994, by rfl⟩ : syracuseStep 730637 = 273989) (by norm_num)
theorem B1123877 : Blo 483789 1123877 := bbase (se 4 (by rfl) ⟨105363, by rfl⟩ : syracuseStep 1123877 = 210727) (by norm_num)
theorem B730661 : Blo 483789 730661 := bbase (se 4 (by rfl) ⟨68499, by rfl⟩ : syracuseStep 730661 = 136999) (by norm_num)
theorem B730685 : Blo 483789 730685 := bbase (se 3 (by rfl) ⟨137003, by rfl⟩ : syracuseStep 730685 = 274007) (by norm_num)
theorem B1091141 : Blo 483789 1091141 := bbase (se 4 (by rfl) ⟨102294, by rfl⟩ : syracuseStep 1091141 = 204589) (by norm_num)
theorem B730709 : Blo 483789 730709 := bbase (se 8 (by rfl) ⟨4281, by rfl⟩ : syracuseStep 730709 = 8563) (by norm_num)
theorem B1975909 : Blo 483789 1975909 := bbase (se 4 (by rfl) ⟨185241, by rfl⟩ : syracuseStep 1975909 = 370483) (by norm_num)
theorem B730733 : Blo 483789 730733 := bbase (se 3 (by rfl) ⟨137012, by rfl⟩ : syracuseStep 730733 = 274025) (by norm_num)
theorem B730757 : Blo 483789 730757 := bbase (se 4 (by rfl) ⟨68508, by rfl⟩ : syracuseStep 730757 = 137017) (by norm_num)
theorem B1091213 : Blo 483789 1091213 := bbase (se 3 (by rfl) ⟨204602, by rfl⟩ : syracuseStep 1091213 = 409205) (by norm_num)
theorem B730781 : Blo 483789 730781 := bbase (se 3 (by rfl) ⟨137021, by rfl⟩ : syracuseStep 730781 = 274043) (by norm_num)
theorem B730805 : Blo 483789 730805 := bbase (se 5 (by rfl) ⟨34256, by rfl⟩ : syracuseStep 730805 = 68513) (by norm_num)
theorem B730829 : Blo 483789 730829 := bbase (se 3 (by rfl) ⟨137030, by rfl⟩ : syracuseStep 730829 = 274061) (by norm_num)
theorem B1091285 : Blo 483789 1091285 := bbase (se 7 (by rfl) ⟨12788, by rfl⟩ : syracuseStep 1091285 = 25577) (by norm_num)
theorem B730853 : Blo 483789 730853 := bbase (se 4 (by rfl) ⟨68517, by rfl⟩ : syracuseStep 730853 = 137035) (by norm_num)
theorem B730877 : Blo 483789 730877 := bbase (se 3 (by rfl) ⟨137039, by rfl⟩ : syracuseStep 730877 = 274079) (by norm_num)
theorem B730901 : Blo 483789 730901 := bbase (se 6 (by rfl) ⟨17130, by rfl⟩ : syracuseStep 730901 = 34261) (by norm_num)
theorem B1091357 : Blo 483789 1091357 := bbase (se 3 (by rfl) ⟨204629, by rfl⟩ : syracuseStep 1091357 = 409259) (by norm_num)
theorem B730925 : Blo 483789 730925 := bbase (se 3 (by rfl) ⟨137048, by rfl⟩ : syracuseStep 730925 = 274097) (by norm_num)
theorem B730949 : Blo 483789 730949 := bbase (se 4 (by rfl) ⟨68526, by rfl⟩ : syracuseStep 730949 = 137053) (by norm_num)
theorem B730973 : Blo 483789 730973 := bbase (se 3 (by rfl) ⟨137057, by rfl⟩ : syracuseStep 730973 = 274115) (by norm_num)
theorem B1091429 : Blo 483789 1091429 := bbase (se 4 (by rfl) ⟨102321, by rfl⟩ : syracuseStep 1091429 = 204643) (by norm_num)
theorem B730997 : Blo 483789 730997 := bbase (se 5 (by rfl) ⟨34265, by rfl⟩ : syracuseStep 730997 = 68531) (by norm_num)
theorem B1746821 : Blo 483789 1746821 := bbase (se 4 (by rfl) ⟨163764, by rfl⟩ : syracuseStep 1746821 = 327529) (by norm_num)
theorem B731021 : Blo 483789 731021 := bbase (se 3 (by rfl) ⟨137066, by rfl⟩ : syracuseStep 731021 = 274133) (by norm_num)
theorem B731045 : Blo 483789 731045 := bbase (se 4 (by rfl) ⟨68535, by rfl⟩ : syracuseStep 731045 = 137071) (by norm_num)
theorem B1091501 : Blo 483789 1091501 := bbase (se 3 (by rfl) ⟨204656, by rfl⟩ : syracuseStep 1091501 = 409313) (by norm_num)
theorem B731069 : Blo 483789 731069 := bbase (se 3 (by rfl) ⟨137075, by rfl⟩ : syracuseStep 731069 = 274151) (by norm_num)
theorem B731093 : Blo 483789 731093 := bbase (se 7 (by rfl) ⟨8567, by rfl⟩ : syracuseStep 731093 = 17135) (by norm_num)
theorem B731117 : Blo 483789 731117 := bbase (se 3 (by rfl) ⟨137084, by rfl⟩ : syracuseStep 731117 = 274169) (by norm_num)
theorem B1091573 : Blo 483789 1091573 := bbase (se 5 (by rfl) ⟨51167, by rfl⟩ : syracuseStep 1091573 = 102335) (by norm_num)
theorem B731141 : Blo 483789 731141 := bbase (se 4 (by rfl) ⟨68544, by rfl⟩ : syracuseStep 731141 = 137089) (by norm_num)
theorem B731165 : Blo 483789 731165 := bbase (se 3 (by rfl) ⟨137093, by rfl⟩ : syracuseStep 731165 = 274187) (by norm_num)
theorem B731189 : Blo 483789 731189 := bbase (se 5 (by rfl) ⟨34274, by rfl⟩ : syracuseStep 731189 = 68549) (by norm_num)
theorem B1091645 : Blo 483789 1091645 := bbase (se 3 (by rfl) ⟨204683, by rfl⟩ : syracuseStep 1091645 = 409367) (by norm_num)
theorem B731213 : Blo 483789 731213 := bbase (se 3 (by rfl) ⟨137102, by rfl⟩ : syracuseStep 731213 = 274205) (by norm_num)
theorem B731237 : Blo 483789 731237 := bbase (se 4 (by rfl) ⟨68553, by rfl⟩ : syracuseStep 731237 = 137107) (by norm_num)
theorem B731261 : Blo 483789 731261 := bbase (se 3 (by rfl) ⟨137111, by rfl⟩ : syracuseStep 731261 = 274223) (by norm_num)
theorem B1091717 : Blo 483789 1091717 := bbase (se 4 (by rfl) ⟨102348, by rfl⟩ : syracuseStep 1091717 = 204697) (by norm_num)
theorem B731285 : Blo 483789 731285 := bbase (se 6 (by rfl) ⟨17139, by rfl⟩ : syracuseStep 731285 = 34279) (by norm_num)
theorem B731309 : Blo 483789 731309 := bbase (se 3 (by rfl) ⟨137120, by rfl⟩ : syracuseStep 731309 = 274241) (by norm_num)
theorem B731333 : Blo 483789 731333 := bbase (se 4 (by rfl) ⟨68562, by rfl⟩ : syracuseStep 731333 = 137125) (by norm_num)
theorem B1091789 : Blo 483789 1091789 := bbase (se 3 (by rfl) ⟨204710, by rfl⟩ : syracuseStep 1091789 = 409421) (by norm_num)
theorem B1550549 : Blo 483789 1550549 := bbase (se 7 (by rfl) ⟨18170, by rfl⟩ : syracuseStep 1550549 = 36341) (by norm_num)
theorem B731357 : Blo 483789 731357 := bbase (se 3 (by rfl) ⟨137129, by rfl⟩ : syracuseStep 731357 = 274259) (by norm_num)
theorem B2468069 : Blo 483789 2468069 := bbase (se 4 (by rfl) ⟨231381, by rfl⟩ : syracuseStep 2468069 = 462763) (by norm_num)
theorem B731381 : Blo 483789 731381 := bbase (se 5 (by rfl) ⟨34283, by rfl⟩ : syracuseStep 731381 = 68567) (by norm_num)
theorem B731405 : Blo 483789 731405 := bbase (se 3 (by rfl) ⟨137138, by rfl⟩ : syracuseStep 731405 = 274277) (by norm_num)
theorem B1091861 : Blo 483789 1091861 := bbase (se 6 (by rfl) ⟨25590, by rfl⟩ : syracuseStep 1091861 = 51181) (by norm_num)
theorem B731429 : Blo 483789 731429 := bbase (se 4 (by rfl) ⟨68571, by rfl⟩ : syracuseStep 731429 = 137143) (by norm_num)
theorem B731453 : Blo 483789 731453 := bbase (se 3 (by rfl) ⟨137147, by rfl⟩ : syracuseStep 731453 = 274295) (by norm_num)
theorem B1386821 : Blo 483789 1386821 := bbase (se 4 (by rfl) ⟨130014, by rfl⟩ : syracuseStep 1386821 = 260029) (by norm_num)
theorem B731477 : Blo 483789 731477 := bbase (se 10 (by rfl) ⟨1071, by rfl⟩ : syracuseStep 731477 = 2143) (by norm_num)
theorem B1091933 : Blo 483789 1091933 := bbase (se 3 (by rfl) ⟨204737, by rfl⟩ : syracuseStep 1091933 = 409475) (by norm_num)
theorem B731501 : Blo 483789 731501 := bbase (se 3 (by rfl) ⟨137156, by rfl⟩ : syracuseStep 731501 = 274313) (by norm_num)
theorem B731525 : Blo 483789 731525 := bbase (se 4 (by rfl) ⟨68580, by rfl⟩ : syracuseStep 731525 = 137161) (by norm_num)
theorem B731549 : Blo 483789 731549 := bbase (se 3 (by rfl) ⟨137165, by rfl⟩ : syracuseStep 731549 = 274331) (by norm_num)
theorem B1092005 : Blo 483789 1092005 := bbase (se 4 (by rfl) ⟨102375, by rfl⟩ : syracuseStep 1092005 = 204751) (by norm_num)
theorem B731573 : Blo 483789 731573 := bbase (se 5 (by rfl) ⟨34292, by rfl⟩ : syracuseStep 731573 = 68585) (by norm_num)
theorem B731597 : Blo 483789 731597 := bbase (se 3 (by rfl) ⟨137174, by rfl⟩ : syracuseStep 731597 = 274349) (by norm_num)
theorem B731621 : Blo 483789 731621 := bbase (se 4 (by rfl) ⟨68589, by rfl⟩ : syracuseStep 731621 = 137179) (by norm_num)
theorem B1092077 : Blo 483789 1092077 := bbase (se 3 (by rfl) ⟨204764, by rfl⟩ : syracuseStep 1092077 = 409529) (by norm_num)
theorem B731645 : Blo 483789 731645 := bbase (se 3 (by rfl) ⟨137183, by rfl⟩ : syracuseStep 731645 = 274367) (by norm_num)
theorem B731669 : Blo 483789 731669 := bbase (se 6 (by rfl) ⟨17148, by rfl⟩ : syracuseStep 731669 = 34297) (by norm_num)
theorem B1092149 : Blo 483789 1092149 := bbase (se 5 (by rfl) ⟨51194, by rfl⟩ : syracuseStep 1092149 = 102389) (by norm_num)
theorem B1092221 : Blo 483789 1092221 := bbase (se 3 (by rfl) ⟨204791, by rfl⟩ : syracuseStep 1092221 = 409583) (by norm_num)
theorem B1092293 : Blo 483789 1092293 := bbase (se 4 (by rfl) ⟨102402, by rfl⟩ : syracuseStep 1092293 = 204805) (by norm_num)
theorem B2337493 : Blo 483789 2337493 := bbase (se 7 (by rfl) ⟨27392, by rfl⟩ : syracuseStep 2337493 = 54785) (by norm_num)
theorem B1092365 : Blo 483789 1092365 := bbase (se 3 (by rfl) ⟨204818, by rfl⟩ : syracuseStep 1092365 = 409637) (by norm_num)
theorem B1092437 : Blo 483789 1092437 := bbase (se 9 (by rfl) ⟨3200, by rfl⟩ : syracuseStep 1092437 = 6401) (by norm_num)
theorem B1092509 : Blo 483789 1092509 := bbase (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) (by norm_num)
theorem B1092581 : Blo 483789 1092581 := bbase (se 4 (by rfl) ⟨102429, by rfl⟩ : syracuseStep 1092581 = 204859) (by norm_num)
theorem B1387493 : Blo 483789 1387493 := bbase (se 4 (by rfl) ⟨130077, by rfl⟩ : syracuseStep 1387493 = 260155) (by norm_num)
theorem B2075669 : Blo 483789 2075669 := bbase (se 6 (by rfl) ⟨48648, by rfl⟩ : syracuseStep 2075669 = 97297) (by norm_num)
theorem B1092653 : Blo 483789 1092653 := bbase (se 3 (by rfl) ⟨204872, by rfl⟩ : syracuseStep 1092653 = 409745) (by norm_num)
theorem B1092725 : Blo 483789 1092725 := bbase (se 5 (by rfl) ⟨51221, by rfl⟩ : syracuseStep 1092725 = 102443) (by norm_num)
theorem B1846421 : Blo 483789 1846421 := bbase (se 6 (by rfl) ⟨43275, by rfl⟩ : syracuseStep 1846421 = 86551) (by norm_num)
theorem B1092797 : Blo 483789 1092797 := bbase (se 3 (by rfl) ⟨204899, by rfl⟩ : syracuseStep 1092797 = 409799) (by norm_num)
theorem B1092869 : Blo 483789 1092869 := bbase (se 4 (by rfl) ⟨102456, by rfl⟩ : syracuseStep 1092869 = 204913) (by norm_num)
theorem B1092941 : Blo 483789 1092941 := bbase (se 3 (by rfl) ⟨204926, by rfl⟩ : syracuseStep 1092941 = 409853) (by norm_num)
theorem B1093013 : Blo 483789 1093013 := bbase (se 6 (by rfl) ⟨25617, by rfl⟩ : syracuseStep 1093013 = 51235) (by norm_num)
theorem B1387925 : Blo 483789 1387925 := bbase (se 6 (by rfl) ⟨32529, by rfl⟩ : syracuseStep 1387925 = 65059) (by norm_num)
theorem B1846709 : Blo 483789 1846709 := bbase (se 5 (by rfl) ⟨86564, by rfl⟩ : syracuseStep 1846709 = 173129) (by norm_num)
theorem B2633141 : Blo 483789 2633141 := bbase (se 5 (by rfl) ⟨123428, by rfl⟩ : syracuseStep 2633141 = 246857) (by norm_num)
theorem B1093085 : Blo 483789 1093085 := bbase (se 3 (by rfl) ⟨204953, by rfl⟩ : syracuseStep 1093085 = 409907) (by norm_num)
theorem B2764277 : Blo 483789 2764277 := bbase (se 5 (by rfl) ⟨129575, by rfl⟩ : syracuseStep 2764277 = 259151) (by norm_num)
theorem B2469365 : Blo 483789 2469365 := bbase (se 5 (by rfl) ⟨115751, by rfl⟩ : syracuseStep 2469365 = 231503) (by norm_num)
theorem B1093157 : Blo 483789 1093157 := bbase (se 4 (by rfl) ⟨102483, by rfl⟩ : syracuseStep 1093157 = 204967) (by norm_num)
theorem B1551973 : Blo 483789 1551973 := bbase (se 4 (by rfl) ⟨145497, by rfl⟩ : syracuseStep 1551973 = 290995) (by norm_num)
theorem B1093229 : Blo 483789 1093229 := bbase (se 3 (by rfl) ⟨204980, by rfl⟩ : syracuseStep 1093229 = 409961) (by norm_num)
theorem B1093301 : Blo 483789 1093301 := bbase (se 5 (by rfl) ⟨51248, by rfl⟩ : syracuseStep 1093301 = 102497) (by norm_num)
theorem B1093373 : Blo 483789 1093373 := bbase (se 3 (by rfl) ⟨205007, by rfl⟩ : syracuseStep 1093373 = 410015) (by norm_num)
theorem B1093445 : Blo 483789 1093445 := bbase (se 4 (by rfl) ⟨102510, by rfl⟩ : syracuseStep 1093445 = 205021) (by norm_num)
theorem B2502485 : Blo 483789 2502485 := bbase (se 9 (by rfl) ⟨7331, by rfl⟩ : syracuseStep 2502485 = 14663) (by norm_num)
theorem B1093517 : Blo 483789 1093517 := bbase (se 3 (by rfl) ⟨205034, by rfl⟩ : syracuseStep 1093517 = 410069) (by norm_num)
theorem B3125141 : Blo 483789 3125141 := bbase (se 6 (by rfl) ⟨73245, by rfl⟩ : syracuseStep 3125141 = 146491) (by norm_num)
theorem B1224629 : Blo 483789 1224629 := bbase (se 5 (by rfl) ⟨57404, by rfl⟩ : syracuseStep 1224629 = 114809) (by norm_num)
theorem B1093589 : Blo 483789 1093589 := bbase (se 7 (by rfl) ⟨12815, by rfl⟩ : syracuseStep 1093589 = 25631) (by norm_num)
theorem B2109445 : Blo 483789 2109445 := bbase (se 4 (by rfl) ⟨197760, by rfl⟩ : syracuseStep 2109445 = 395521) (by norm_num)
theorem B1093661 : Blo 483789 1093661 := bbase (se 3 (by rfl) ⟨205061, by rfl⟩ : syracuseStep 1093661 = 410123) (by norm_num)
theorem B1552421 : Blo 483789 1552421 := bbase (se 4 (by rfl) ⟨145539, by rfl⟩ : syracuseStep 1552421 = 291079) (by norm_num)
theorem B1093733 : Blo 483789 1093733 := bbase (se 4 (by rfl) ⟨102537, by rfl⟩ : syracuseStep 1093733 = 205075) (by norm_num)
theorem B1224821 : Blo 483789 1224821 := bbase (se 5 (by rfl) ⟨57413, by rfl⟩ : syracuseStep 1224821 = 114827) (by norm_num)
theorem B3682421 : Blo 483789 3682421 := bbase (se 5 (by rfl) ⟨172613, by rfl⟩ : syracuseStep 3682421 = 345227) (by norm_num)
theorem B1388677 : Blo 483789 1388677 := bbase (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) (by norm_num)
theorem B1093805 : Blo 483789 1093805 := bbase (se 3 (by rfl) ⟨205088, by rfl⟩ : syracuseStep 1093805 = 410177) (by norm_num)
theorem B1093877 : Blo 483789 1093877 := bbase (se 5 (by rfl) ⟨51275, by rfl⟩ : syracuseStep 1093877 = 102551) (by norm_num)
theorem B1093949 : Blo 483789 1093949 := bbase (se 3 (by rfl) ⟨205115, by rfl⟩ : syracuseStep 1093949 = 410231) (by norm_num)
theorem B1094021 : Blo 483789 1094021 := bbase (se 4 (by rfl) ⟨102564, by rfl⟩ : syracuseStep 1094021 = 205129) (by norm_num)
theorem B1225165 : Blo 483789 1225165 := bbase (se 3 (by rfl) ⟨229718, by rfl⟩ : syracuseStep 1225165 = 459437) (by norm_num)
theorem B1094093 : Blo 483789 1094093 := bbase (se 3 (by rfl) ⟨205142, by rfl⟩ : syracuseStep 1094093 = 410285) (by norm_num)
theorem B831973 : Blo 483789 831973 := bbase (se 4 (by rfl) ⟨77997, by rfl⟩ : syracuseStep 831973 = 155995) (by norm_num)
theorem B1094165 : Blo 483789 1094165 := bbase (se 6 (by rfl) ⟨25644, by rfl⟩ : syracuseStep 1094165 = 51289) (by norm_num)
theorem B1225277 : Blo 483789 1225277 := bbase (se 3 (by rfl) ⟨229739, by rfl⟩ : syracuseStep 1225277 = 459479) (by norm_num)
theorem B1847893 : Blo 483789 1847893 := bbase (se 8 (by rfl) ⟨10827, by rfl⟩ : syracuseStep 1847893 = 21655) (by norm_num)
theorem B1094237 : Blo 483789 1094237 := bbase (se 3 (by rfl) ⟨205169, by rfl⟩ : syracuseStep 1094237 = 410339) (by norm_num)
theorem B2765461 : Blo 483789 2765461 := bbase (se 6 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 2765461 = 129631) (by norm_num)
theorem B1094309 : Blo 483789 1094309 := bbase (se 4 (by rfl) ⟨102591, by rfl⟩ : syracuseStep 1094309 = 205183) (by norm_num)
theorem B4207285 : Blo 483789 4207285 := bbase (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) (by norm_num)
theorem B1094381 : Blo 483789 1094381 := bbase (se 3 (by rfl) ⟨205196, by rfl⟩ : syracuseStep 1094381 = 410393) (by norm_num)
theorem B1225469 : Blo 483789 1225469 := bbase (se 3 (by rfl) ⟨229775, by rfl⟩ : syracuseStep 1225469 = 459551) (by norm_num)
theorem B1094453 : Blo 483789 1094453 := bbase (se 5 (by rfl) ⟨51302, by rfl⟩ : syracuseStep 1094453 = 102605) (by norm_num)
theorem B1094525 : Blo 483789 1094525 := bbase (se 3 (by rfl) ⟨205223, by rfl⟩ : syracuseStep 1094525 = 410447) (by norm_num)
theorem B1848197 : Blo 483789 1848197 := bbase (se 4 (by rfl) ⟨173268, by rfl⟩ : syracuseStep 1848197 = 346537) (by norm_num)
theorem B8893333 : Blo 483789 8893333 := bbase (se 6 (by rfl) ⟨208437, by rfl⟩ : syracuseStep 8893333 = 416875) (by norm_num)
theorem B1094597 : Blo 483789 1094597 := bbase (se 4 (by rfl) ⟨102618, by rfl⟩ : syracuseStep 1094597 = 205237) (by norm_num)
theorem B1094669 : Blo 483789 1094669 := bbase (se 3 (by rfl) ⟨205250, by rfl⟩ : syracuseStep 1094669 = 410501) (by norm_num)
theorem B1225813 : Blo 483789 1225813 := bbase (se 8 (by rfl) ⟨7182, by rfl⟩ : syracuseStep 1225813 = 14365) (by norm_num)
theorem B1094741 : Blo 483789 1094741 := bbase (se 8 (by rfl) ⟨6414, by rfl⟩ : syracuseStep 1094741 = 12829) (by norm_num)
theorem B1094813 : Blo 483789 1094813 := bbase (se 3 (by rfl) ⟨205277, by rfl⟩ : syracuseStep 1094813 = 410555) (by norm_num)
theorem B1225925 : Blo 483789 1225925 := bbase (se 4 (by rfl) ⟨114930, by rfl⟩ : syracuseStep 1225925 = 229861) (by norm_num)
theorem B1094885 : Blo 483789 1094885 := bbase (se 4 (by rfl) ⟨102645, by rfl⟩ : syracuseStep 1094885 = 205291) (by norm_num)
theorem B1094957 : Blo 483789 1094957 := bbase (se 3 (by rfl) ⟨205304, by rfl⟩ : syracuseStep 1094957 = 410609) (by norm_num)
theorem B1095029 : Blo 483789 1095029 := bbase (se 5 (by rfl) ⟨51329, by rfl⟩ : syracuseStep 1095029 = 102659) (by norm_num)
theorem B1226117 : Blo 483789 1226117 := bbase (se 4 (by rfl) ⟨114948, by rfl⟩ : syracuseStep 1226117 = 229897) (by norm_num)
theorem B832925 : Blo 483789 832925 := bbase (se 3 (by rfl) ⟨156173, by rfl⟩ : syracuseStep 832925 = 312347) (by norm_num)
theorem B1095101 : Blo 483789 1095101 := bbase (se 3 (by rfl) ⟨205331, by rfl⟩ : syracuseStep 1095101 = 410663) (by norm_num)
theorem B1258973 : Blo 483789 1258973 := bbase (se 3 (by rfl) ⟨236057, by rfl⟩ : syracuseStep 1258973 = 472115) (by norm_num)
theorem B1095173 : Blo 483789 1095173 := bbase (se 4 (by rfl) ⟨102672, by rfl⟩ : syracuseStep 1095173 = 205345) (by norm_num)
theorem B1095245 : Blo 483789 1095245 := bbase (se 3 (by rfl) ⟨205358, by rfl⟩ : syracuseStep 1095245 = 410717) (by norm_num)
theorem B1095317 : Blo 483789 1095317 := bbase (se 6 (by rfl) ⟨25671, by rfl⟩ : syracuseStep 1095317 = 51343) (by norm_num)
theorem B1226461 : Blo 483789 1226461 := bbase (se 3 (by rfl) ⟨229961, by rfl⟩ : syracuseStep 1226461 = 459923) (by norm_num)
theorem B1095389 : Blo 483789 1095389 := bbase (se 3 (by rfl) ⟨205385, by rfl⟩ : syracuseStep 1095389 = 410771) (by norm_num)
theorem B1095461 : Blo 483789 1095461 := bbase (se 4 (by rfl) ⟨102699, by rfl⟩ : syracuseStep 1095461 = 205399) (by norm_num)
theorem B1226573 : Blo 483789 1226573 := bbase (se 3 (by rfl) ⟨229982, by rfl⟩ : syracuseStep 1226573 = 459965) (by norm_num)
theorem B1095533 : Blo 483789 1095533 := bbase (se 3 (by rfl) ⟨205412, by rfl⟩ : syracuseStep 1095533 = 410825) (by norm_num)
theorem B2635669 : Blo 483789 2635669 := bbase (se 6 (by rfl) ⟨61773, by rfl⟩ : syracuseStep 2635669 = 123547) (by norm_num)
theorem B1095605 : Blo 483789 1095605 := bbase (se 5 (by rfl) ⟨51356, by rfl⟩ : syracuseStep 1095605 = 102713) (by norm_num)
theorem B1095677 : Blo 483789 1095677 := bbase (se 3 (by rfl) ⟨205439, by rfl⟩ : syracuseStep 1095677 = 410879) (by norm_num)
theorem B1226765 : Blo 483789 1226765 := bbase (se 3 (by rfl) ⟨230018, by rfl⟩ : syracuseStep 1226765 = 460037) (by norm_num)
theorem B1095749 : Blo 483789 1095749 := bbase (se 4 (by rfl) ⟨102726, by rfl⟩ : syracuseStep 1095749 = 205453) (by norm_num)
theorem B1095821 : Blo 483789 1095821 := bbase (se 3 (by rfl) ⟨205466, by rfl⟩ : syracuseStep 1095821 = 410933) (by norm_num)
theorem B1095893 : Blo 483789 1095893 := bbase (se 7 (by rfl) ⟨12842, by rfl⟩ : syracuseStep 1095893 = 25685) (by norm_num)
theorem B1554677 : Blo 483789 1554677 := bbase (se 5 (by rfl) ⟨72875, by rfl⟩ : syracuseStep 1554677 = 145751) (by norm_num)
theorem B1095965 : Blo 483789 1095965 := bbase (se 3 (by rfl) ⟨205493, by rfl⟩ : syracuseStep 1095965 = 410987) (by norm_num)
theorem B1227109 : Blo 483789 1227109 := bbase (se 4 (by rfl) ⟨115041, by rfl⟩ : syracuseStep 1227109 = 230083) (by norm_num)
theorem B1096037 : Blo 483789 1096037 := bbase (se 4 (by rfl) ⟨102753, by rfl⟩ : syracuseStep 1096037 = 205507) (by norm_num)
theorem B1096109 : Blo 483789 1096109 := bbase (se 3 (by rfl) ⟨205520, by rfl⟩ : syracuseStep 1096109 = 411041) (by norm_num)
theorem B1227221 : Blo 483789 1227221 := bbase (se 7 (by rfl) ⟨14381, by rfl⟩ : syracuseStep 1227221 = 28763) (by norm_num)
theorem B1096181 : Blo 483789 1096181 := bbase (se 5 (by rfl) ⟨51383, by rfl⟩ : syracuseStep 1096181 = 102767) (by norm_num)
theorem B6404629 : Blo 483789 6404629 := bbase (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) (by norm_num)
theorem B1325605 : Blo 483789 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B1096253 : Blo 483789 1096253 := bbase (se 3 (by rfl) ⟨205547, by rfl⟩ : syracuseStep 1096253 = 411095) (by norm_num)
theorem B2767445 : Blo 483789 2767445 := bbase (se 8 (by rfl) ⟨16215, by rfl⟩ : syracuseStep 2767445 = 32431) (by norm_num)
theorem B703085 : Blo 483789 703085 := bbase (se 3 (by rfl) ⟨131828, by rfl⟩ : syracuseStep 703085 = 263657) (by norm_num)
theorem B2341493 : Blo 483789 2341493 := bbase (se 5 (by rfl) ⟨109757, by rfl⟩ : syracuseStep 2341493 = 219515) (by norm_num)
theorem B1096325 : Blo 483789 1096325 := bbase (se 4 (by rfl) ⟨102780, by rfl⟩ : syracuseStep 1096325 = 205561) (by norm_num)
theorem B1227413 : Blo 483789 1227413 := bbase (se 6 (by rfl) ⟨28767, by rfl⟩ : syracuseStep 1227413 = 57535) (by norm_num)
theorem B1096397 : Blo 483789 1096397 := bbase (se 3 (by rfl) ⟨205574, by rfl⟩ : syracuseStep 1096397 = 411149) (by norm_num)
theorem B1096469 : Blo 483789 1096469 := bbase (se 6 (by rfl) ⟨25698, by rfl⟩ : syracuseStep 1096469 = 51397) (by norm_num)
theorem B1096541 : Blo 483789 1096541 := bbase (se 3 (by rfl) ⟨205601, by rfl⟩ : syracuseStep 1096541 = 411203) (by norm_num)
theorem B1096613 : Blo 483789 1096613 := bbase (se 4 (by rfl) ⟨102807, by rfl⟩ : syracuseStep 1096613 = 205615) (by norm_num)
theorem B1850309 : Blo 483789 1850309 := bbase (se 4 (by rfl) ⟨173466, by rfl⟩ : syracuseStep 1850309 = 346933) (by norm_num)
theorem B2079701 : Blo 483789 2079701 := bbase (se 7 (by rfl) ⟨24371, by rfl⟩ : syracuseStep 2079701 = 48743) (by norm_num)
theorem B1227757 : Blo 483789 1227757 := bbase (se 3 (by rfl) ⟨230204, by rfl⟩ : syracuseStep 1227757 = 460409) (by norm_num)
theorem B1096685 : Blo 483789 1096685 := bbase (se 3 (by rfl) ⟨205628, by rfl⟩ : syracuseStep 1096685 = 411257) (by norm_num)
theorem B1260533 : Blo 483789 1260533 := bbase (se 5 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 1260533 = 118175) (by norm_num)
theorem B1096757 : Blo 483789 1096757 := bbase (se 5 (by rfl) ⟨51410, by rfl⟩ : syracuseStep 1096757 = 102821) (by norm_num)
theorem B1227869 : Blo 483789 1227869 := bbase (se 3 (by rfl) ⟨230225, by rfl⟩ : syracuseStep 1227869 = 460451) (by norm_num)
theorem B1096829 : Blo 483789 1096829 := bbase (se 3 (by rfl) ⟨205655, by rfl⟩ : syracuseStep 1096829 = 411311) (by norm_num)
theorem B1752197 : Blo 483789 1752197 := bbase (se 4 (by rfl) ⟨164268, by rfl⟩ : syracuseStep 1752197 = 328537) (by norm_num)
theorem B1096901 : Blo 483789 1096901 := bbase (se 4 (by rfl) ⟨102834, by rfl⟩ : syracuseStep 1096901 = 205669) (by norm_num)
theorem B1850597 : Blo 483789 1850597 := bbase (se 4 (by rfl) ⟨173493, by rfl⟩ : syracuseStep 1850597 = 346987) (by norm_num)
theorem B1096973 : Blo 483789 1096973 := bbase (se 3 (by rfl) ⟨205682, by rfl⟩ : syracuseStep 1096973 = 411365) (by norm_num)
theorem B1228061 : Blo 483789 1228061 := bbase (se 3 (by rfl) ⟨230261, by rfl⟩ : syracuseStep 1228061 = 460523) (by norm_num)
theorem B1097045 : Blo 483789 1097045 := bbase (se 11 (by rfl) ⟨803, by rfl⟩ : syracuseStep 1097045 = 1607) (by norm_num)
theorem B1097117 : Blo 483789 1097117 := bbase (se 3 (by rfl) ⟨205709, by rfl⟩ : syracuseStep 1097117 = 411419) (by norm_num)
theorem B736685 : Blo 483789 736685 := bbase (se 3 (by rfl) ⟨138128, by rfl⟩ : syracuseStep 736685 = 276257) (by norm_num)
theorem B1097189 : Blo 483789 1097189 := bbase (se 4 (by rfl) ⟨102861, by rfl⟩ : syracuseStep 1097189 = 205723) (by norm_num)
theorem B4439573 : Blo 483789 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B2211365 : Blo 483789 2211365 := bbase (se 4 (by rfl) ⟨207315, by rfl⟩ : syracuseStep 2211365 = 414631) (by norm_num)
theorem B1097261 : Blo 483789 1097261 := bbase (se 3 (by rfl) ⟨205736, by rfl⟩ : syracuseStep 1097261 = 411473) (by norm_num)
theorem B933445 : Blo 483789 933445 := bbase (se 4 (by rfl) ⟨87510, by rfl⟩ : syracuseStep 933445 = 175021) (by norm_num)
theorem B1228405 : Blo 483789 1228405 := bbase (se 5 (by rfl) ⟨57581, by rfl⟩ : syracuseStep 1228405 = 115163) (by norm_num)
theorem B1097333 : Blo 483789 1097333 := bbase (se 5 (by rfl) ⟨51437, by rfl⟩ : syracuseStep 1097333 = 102875) (by norm_num)
theorem B2375333 : Blo 483789 2375333 := bbase (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) (by norm_num)
theorem B1097405 : Blo 483789 1097405 := bbase (se 3 (by rfl) ⟨205763, by rfl⟩ : syracuseStep 1097405 = 411527) (by norm_num)
theorem B1228517 : Blo 483789 1228517 := bbase (se 4 (by rfl) ⟨115173, by rfl⟩ : syracuseStep 1228517 = 230347) (by norm_num)
theorem B1097477 : Blo 483789 1097477 := bbase (se 4 (by rfl) ⟨102888, by rfl⟩ : syracuseStep 1097477 = 205777) (by norm_num)
theorem B1326917 : Blo 483789 1326917 := bbase (se 4 (by rfl) ⟨124398, by rfl⟩ : syracuseStep 1326917 = 248797) (by norm_num)
theorem B1228709 : Blo 483789 1228709 := bbase (se 4 (by rfl) ⟨115191, by rfl⟩ : syracuseStep 1228709 = 230383) (by norm_num)
theorem B1163317 : Blo 483789 1163317 := bbase (se 5 (by rfl) ⟨54530, by rfl⟩ : syracuseStep 1163317 = 109061) (by norm_num)
theorem B1229053 : Blo 483789 1229053 := bbase (se 3 (by rfl) ⟨230447, by rfl⟩ : syracuseStep 1229053 = 460895) (by norm_num)
theorem B1229165 : Blo 483789 1229165 := bbase (se 3 (by rfl) ⟨230468, by rfl⟩ : syracuseStep 1229165 = 460937) (by norm_num)
theorem B1851781 : Blo 483789 1851781 := bbase (se 4 (by rfl) ⟨173604, by rfl⟩ : syracuseStep 1851781 = 347209) (by norm_num)
theorem B1229357 : Blo 483789 1229357 := bbase (se 3 (by rfl) ⟨230504, by rfl⟩ : syracuseStep 1229357 = 461009) (by norm_num)
theorem B1000021 : Blo 483789 1000021 := bbase (se 8 (by rfl) ⟨5859, by rfl⟩ : syracuseStep 1000021 = 11719) (by norm_num)
theorem B1163933 : Blo 483789 1163933 := bbase (se 3 (by rfl) ⟨218237, by rfl⟩ : syracuseStep 1163933 = 436475) (by norm_num)
theorem B2081477 : Blo 483789 2081477 := bbase (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) (by norm_num)
theorem B2769653 : Blo 483789 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B738109 : Blo 483789 738109 := bbase (se 3 (by rfl) ⟨138395, by rfl⟩ : syracuseStep 738109 = 276791) (by norm_num)
theorem B4146005 : Blo 483789 4146005 := bbase (se 9 (by rfl) ⟨12146, by rfl⟩ : syracuseStep 4146005 = 24293) (by norm_num)
theorem B1229701 : Blo 483789 1229701 := bbase (se 4 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 1229701 = 230569) (by norm_num)
theorem B1229813 : Blo 483789 1229813 := bbase (se 5 (by rfl) ⟨57647, by rfl⟩ : syracuseStep 1229813 = 115295) (by norm_num)
theorem B1164365 : Blo 483789 1164365 := bbase (se 3 (by rfl) ⟨218318, by rfl⟩ : syracuseStep 1164365 = 436637) (by norm_num)
theorem B1000549 : Blo 483789 1000549 := bbase (se 4 (by rfl) ⟨93801, by rfl⟩ : syracuseStep 1000549 = 187603) (by norm_num)
theorem B738485 : Blo 483789 738485 := bbase (se 5 (by rfl) ⟨34616, by rfl⟩ : syracuseStep 738485 = 69233) (by norm_num)
theorem B1230005 : Blo 483789 1230005 := bbase (se 5 (by rfl) ⟨57656, by rfl⟩ : syracuseStep 1230005 = 115313) (by norm_num)
theorem B1033597 : Blo 483789 1033597 := bbase (se 3 (by rfl) ⟨193799, by rfl⟩ : syracuseStep 1033597 = 387599) (by norm_num)
theorem B1033717 : Blo 483789 1033717 := bbase (se 5 (by rfl) ⟨48455, by rfl⟩ : syracuseStep 1033717 = 96911) (by norm_num)
theorem B1230349 : Blo 483789 1230349 := bbase (se 3 (by rfl) ⟨230690, by rfl⟩ : syracuseStep 1230349 = 461381) (by norm_num)
theorem B1754693 : Blo 483789 1754693 := bbase (se 4 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 1754693 = 329005) (by norm_num)
theorem B1230461 : Blo 483789 1230461 := bbase (se 3 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 1230461 = 461423) (by norm_num)
theorem B2082469 : Blo 483789 2082469 := bbase (se 4 (by rfl) ⟨195231, by rfl⟩ : syracuseStep 2082469 = 390463) (by norm_num)
theorem B1033973 : Blo 483789 1033973 := bbase (se 5 (by rfl) ⟨48467, by rfl⟩ : syracuseStep 1033973 = 96935) (by norm_num)
theorem B935725 : Blo 483789 935725 := bbase (se 3 (by rfl) ⟨175448, by rfl⟩ : syracuseStep 935725 = 350897) (by norm_num)
theorem B1230653 : Blo 483789 1230653 := bbase (se 3 (by rfl) ⟨230747, by rfl⟩ : syracuseStep 1230653 = 461495) (by norm_num)
theorem B739277 : Blo 483789 739277 := bbase (se 3 (by rfl) ⟨138614, by rfl⟩ : syracuseStep 739277 = 277229) (by norm_num)
theorem B1001501 : Blo 483789 1001501 := bbase (se 3 (by rfl) ⟨187781, by rfl⟩ : syracuseStep 1001501 = 375563) (by norm_num)
theorem B1558597 : Blo 483789 1558597 := bbase (se 4 (by rfl) ⟨146118, by rfl⟩ : syracuseStep 1558597 = 292237) (by norm_num)
theorem B1755269 : Blo 483789 1755269 := bbase (se 4 (by rfl) ⟨164556, by rfl⟩ : syracuseStep 1755269 = 329113) (by norm_num)
theorem B1230997 : Blo 483789 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B1165565 : Blo 483789 1165565 := bbase (se 3 (by rfl) ⟨218543, by rfl⟩ : syracuseStep 1165565 = 437087) (by norm_num)
theorem B1231109 : Blo 483789 1231109 := bbase (se 4 (by rfl) ⟨115416, by rfl⟩ : syracuseStep 1231109 = 230833) (by norm_num)
theorem B9324821 : Blo 483789 9324821 := bbase (se 6 (by rfl) ⟨218550, by rfl⟩ : syracuseStep 9324821 = 437101) (by norm_num)
theorem B1558853 : Blo 483789 1558853 := bbase (se 4 (by rfl) ⟨146142, by rfl⟩ : syracuseStep 1558853 = 292285) (by norm_num)
theorem B1231301 : Blo 483789 1231301 := bbase (se 4 (by rfl) ⟨115434, by rfl⟩ : syracuseStep 1231301 = 230869) (by norm_num)
theorem B1755701 : Blo 483789 1755701 := bbase (se 5 (by rfl) ⟨82298, by rfl⟩ : syracuseStep 1755701 = 164597) (by norm_num)
theorem B2214469 : Blo 483789 2214469 := bbase (se 4 (by rfl) ⟨207606, by rfl⟩ : syracuseStep 2214469 = 415213) (by norm_num)
theorem B1034861 : Blo 483789 1034861 := bbase (se 3 (by rfl) ⟨194036, by rfl⟩ : syracuseStep 1034861 = 388073) (by norm_num)
theorem B1067717 : Blo 483789 1067717 := bbase (se 4 (by rfl) ⟨100098, by rfl⟩ : syracuseStep 1067717 = 200197) (by norm_num)
theorem B9358037 : Blo 483789 9358037 := bbase (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) (by norm_num)
theorem B1231645 : Blo 483789 1231645 := bbase (se 3 (by rfl) ⟨230933, by rfl⟩ : syracuseStep 1231645 = 461867) (by norm_num)
theorem B1035101 : Blo 483789 1035101 := bbase (se 3 (by rfl) ⟨194081, by rfl⟩ : syracuseStep 1035101 = 388163) (by norm_num)
theorem B1231757 : Blo 483789 1231757 := bbase (se 3 (by rfl) ⟨230954, by rfl⟩ : syracuseStep 1231757 = 461909) (by norm_num)
theorem B1657813 : Blo 483789 1657813 := bbase (se 7 (by rfl) ⟨19427, by rfl⟩ : syracuseStep 1657813 = 38855) (by norm_num)
theorem B740333 : Blo 483789 740333 := bbase (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) (by norm_num)
theorem B2870261 : Blo 483789 2870261 := bbase (se 5 (by rfl) ⟨134543, by rfl⟩ : syracuseStep 2870261 = 269087) (by norm_num)
theorem B1231949 : Blo 483789 1231949 := bbase (se 3 (by rfl) ⟨230990, by rfl⟩ : syracuseStep 1231949 = 461981) (by norm_num)
theorem B1035605 : Blo 483789 1035605 := bbase (se 11 (by rfl) ⟨758, by rfl⟩ : syracuseStep 1035605 = 1517) (by norm_num)
theorem B1035613 : Blo 483789 1035613 := bbase (se 3 (by rfl) ⟨194177, by rfl⟩ : syracuseStep 1035613 = 388355) (by norm_num)
theorem B1232293 : Blo 483789 1232293 := bbase (se 4 (by rfl) ⟨115527, by rfl⟩ : syracuseStep 1232293 = 231055) (by norm_num)
theorem B1232405 : Blo 483789 1232405 := bbase (se 6 (by rfl) ⟨28884, by rfl⟩ : syracuseStep 1232405 = 57769) (by norm_num)
theorem B544297 : Blo 483789 544297 := bbase (se 2 (by rfl) ⟨204111, by rfl⟩ : syracuseStep 544297 = 408223) (by norm_num)
theorem B4574773 : Blo 483789 4574773 := bbase (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) (by norm_num)
theorem B544333 : Blo 483789 544333 := bbase (se 3 (by rfl) ⟨102062, by rfl⟩ : syracuseStep 544333 = 204125) (by norm_num)
theorem B544369 : Blo 483789 544369 := bbase (se 2 (by rfl) ⟨204138, by rfl⟩ : syracuseStep 544369 = 408277) (by norm_num)
theorem B544405 : Blo 483789 544405 := bbase (se 6 (by rfl) ⟨12759, by rfl⟩ : syracuseStep 544405 = 25519) (by norm_num)
theorem B544441 : Blo 483789 544441 := bbase (se 2 (by rfl) ⟨204165, by rfl⟩ : syracuseStep 544441 = 408331) (by norm_num)
theorem B2215637 : Blo 483789 2215637 := bbase (se 7 (by rfl) ⟨25964, by rfl⟩ : syracuseStep 2215637 = 51929) (by norm_num)
theorem B3690197 : Blo 483789 3690197 := bbase (se 7 (by rfl) ⟨43244, by rfl⟩ : syracuseStep 3690197 = 86489) (by norm_num)
theorem B1232597 : Blo 483789 1232597 := bbase (se 7 (by rfl) ⟨14444, by rfl⟩ : syracuseStep 1232597 = 28889) (by norm_num)
theorem B544477 : Blo 483789 544477 := bbase (se 3 (by rfl) ⟨102089, by rfl⟩ : syracuseStep 544477 = 204179) (by norm_num)
theorem B4148981 : Blo 483789 4148981 := bbase (se 5 (by rfl) ⟨194483, by rfl⟩ : syracuseStep 4148981 = 388967) (by norm_num)
theorem B544513 : Blo 483789 544513 := bbase (se 2 (by rfl) ⟨204192, by rfl⟩ : syracuseStep 544513 = 408385) (by norm_num)
theorem B544549 : Blo 483789 544549 := bbase (se 4 (by rfl) ⟨51051, by rfl⟩ : syracuseStep 544549 = 102103) (by norm_num)
theorem B544585 : Blo 483789 544585 := bbase (se 2 (by rfl) ⟨204219, by rfl⟩ : syracuseStep 544585 = 408439) (by norm_num)
theorem B544621 : Blo 483789 544621 := bbase (se 3 (by rfl) ⟨102116, by rfl⟩ : syracuseStep 544621 = 204233) (by norm_num)
theorem B741253 : Blo 483789 741253 := bbase (se 4 (by rfl) ⟨69492, by rfl⟩ : syracuseStep 741253 = 138985) (by norm_num)
theorem B544657 : Blo 483789 544657 := bbase (se 2 (by rfl) ⟨204246, by rfl⟩ : syracuseStep 544657 = 408493) (by norm_num)
theorem B544693 : Blo 483789 544693 := bbase (se 5 (by rfl) ⟨25532, by rfl⟩ : syracuseStep 544693 = 51065) (by norm_num)
theorem B544729 : Blo 483789 544729 := bbase (se 2 (by rfl) ⟨204273, by rfl⟩ : syracuseStep 544729 = 408547) (by norm_num)
theorem B544765 : Blo 483789 544765 := bbase (se 3 (by rfl) ⟨102143, by rfl⟩ : syracuseStep 544765 = 204287) (by norm_num)
theorem B544801 : Blo 483789 544801 := bbase (se 2 (by rfl) ⟨204300, by rfl⟩ : syracuseStep 544801 = 408601) (by norm_num)
theorem B1232941 : Blo 483789 1232941 := bbase (se 3 (by rfl) ⟨231176, by rfl⟩ : syracuseStep 1232941 = 462353) (by norm_num)
theorem B544837 : Blo 483789 544837 := bbase (se 4 (by rfl) ⟨51078, by rfl⟩ : syracuseStep 544837 = 102157) (by norm_num)
theorem B872525 : Blo 483789 872525 := bbase (se 3 (by rfl) ⟨163598, by rfl⟩ : syracuseStep 872525 = 327197) (by norm_num)
theorem B544873 : Blo 483789 544873 := bbase (se 2 (by rfl) ⟨204327, by rfl⟩ : syracuseStep 544873 = 408655) (by norm_num)
theorem B544909 : Blo 483789 544909 := bbase (se 3 (by rfl) ⟨102170, by rfl⟩ : syracuseStep 544909 = 204341) (by norm_num)
theorem B1233053 : Blo 483789 1233053 := bbase (se 3 (by rfl) ⟨231197, by rfl⟩ : syracuseStep 1233053 = 462395) (by norm_num)
theorem B544945 : Blo 483789 544945 := bbase (se 2 (by rfl) ⟨204354, by rfl⟩ : syracuseStep 544945 = 408709) (by norm_num)
theorem B544981 : Blo 483789 544981 := bbase (se 7 (by rfl) ⟨6386, by rfl⟩ : syracuseStep 544981 = 12773) (by norm_num)
theorem B545017 : Blo 483789 545017 := bbase (se 2 (by rfl) ⟨204381, by rfl⟩ : syracuseStep 545017 = 408763) (by norm_num)
theorem B545053 : Blo 483789 545053 := bbase (se 3 (by rfl) ⟨102197, by rfl⟩ : syracuseStep 545053 = 204395) (by norm_num)
theorem B545089 : Blo 483789 545089 := bbase (se 2 (by rfl) ⟨204408, by rfl⟩ : syracuseStep 545089 = 408817) (by norm_num)
theorem B1233245 : Blo 483789 1233245 := bbase (se 3 (by rfl) ⟨231233, by rfl⟩ : syracuseStep 1233245 = 462467) (by norm_num)
theorem B545125 : Blo 483789 545125 := bbase (se 4 (by rfl) ⟨51105, by rfl⟩ : syracuseStep 545125 = 102211) (by norm_num)
theorem B545161 : Blo 483789 545161 := bbase (se 2 (by rfl) ⟨204435, by rfl⟩ : syracuseStep 545161 = 408871) (by norm_num)
theorem B545197 : Blo 483789 545197 := bbase (se 3 (by rfl) ⟨102224, by rfl⟩ : syracuseStep 545197 = 204449) (by norm_num)
theorem B1036741 : Blo 483789 1036741 := bbase (se 4 (by rfl) ⟨97194, by rfl⟩ : syracuseStep 1036741 = 194389) (by norm_num)
theorem B1331653 : Blo 483789 1331653 := bbase (se 4 (by rfl) ⟨124842, by rfl⟩ : syracuseStep 1331653 = 249685) (by norm_num)
theorem B545233 : Blo 483789 545233 := bbase (se 2 (by rfl) ⟨204462, by rfl⟩ : syracuseStep 545233 = 408925) (by norm_num)
theorem B1167853 : Blo 483789 1167853 := bbase (se 3 (by rfl) ⟨218972, by rfl⟩ : syracuseStep 1167853 = 437945) (by norm_num)
theorem B545269 : Blo 483789 545269 := bbase (se 5 (by rfl) ⟨25559, by rfl⟩ : syracuseStep 545269 = 51119) (by norm_num)
theorem B545305 : Blo 483789 545305 := bbase (se 2 (by rfl) ⟨204489, by rfl⟩ : syracuseStep 545305 = 408979) (by norm_num)
theorem B545341 : Blo 483789 545341 := bbase (se 3 (by rfl) ⟨102251, by rfl⟩ : syracuseStep 545341 = 204503) (by norm_num)
theorem B1167949 : Blo 483789 1167949 := bbase (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) (by norm_num)
theorem B545377 : Blo 483789 545377 := bbase (se 2 (by rfl) ⟨204516, by rfl⟩ : syracuseStep 545377 = 409033) (by norm_num)
theorem B545413 : Blo 483789 545413 := bbase (se 4 (by rfl) ⟨51132, by rfl⟩ : syracuseStep 545413 = 102265) (by norm_num)
theorem B873101 : Blo 483789 873101 := bbase (se 3 (by rfl) ⟨163706, by rfl⟩ : syracuseStep 873101 = 327413) (by norm_num)
theorem B545449 : Blo 483789 545449 := bbase (se 2 (by rfl) ⟨204543, by rfl⟩ : syracuseStep 545449 = 409087) (by norm_num)
theorem B1233589 : Blo 483789 1233589 := bbase (se 5 (by rfl) ⟨57824, by rfl⟩ : syracuseStep 1233589 = 115649) (by norm_num)
theorem B545485 : Blo 483789 545485 := bbase (se 3 (by rfl) ⟨102278, by rfl⟩ : syracuseStep 545485 = 204557) (by norm_num)
theorem B545521 : Blo 483789 545521 := bbase (se 2 (by rfl) ⟨204570, by rfl⟩ : syracuseStep 545521 = 409141) (by norm_num)
theorem B1168141 : Blo 483789 1168141 := bbase (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) (by norm_num)
theorem B545557 : Blo 483789 545557 := bbase (se 6 (by rfl) ⟨12786, by rfl⟩ : syracuseStep 545557 = 25573) (by norm_num)
theorem B1233701 : Blo 483789 1233701 := bbase (se 4 (by rfl) ⟨115659, by rfl⟩ : syracuseStep 1233701 = 231319) (by norm_num)
theorem B545593 : Blo 483789 545593 := bbase (se 2 (by rfl) ⟨204597, by rfl⟩ : syracuseStep 545593 = 409195) (by norm_num)
theorem B1037117 : Blo 483789 1037117 := bbase (se 3 (by rfl) ⟨194459, by rfl⟩ : syracuseStep 1037117 = 388919) (by norm_num)
theorem B545629 : Blo 483789 545629 := bbase (se 3 (by rfl) ⟨102305, by rfl⟩ : syracuseStep 545629 = 204611) (by norm_num)
theorem B545665 : Blo 483789 545665 := bbase (se 2 (by rfl) ⟨204624, by rfl⟩ : syracuseStep 545665 = 409249) (by norm_num)
theorem B545701 : Blo 483789 545701 := bbase (se 4 (by rfl) ⟨51159, by rfl⟩ : syracuseStep 545701 = 102319) (by norm_num)
theorem B545737 : Blo 483789 545737 := bbase (se 2 (by rfl) ⟨204651, by rfl⟩ : syracuseStep 545737 = 409303) (by norm_num)
theorem B1233893 : Blo 483789 1233893 := bbase (se 4 (by rfl) ⟨115677, by rfl⟩ : syracuseStep 1233893 = 231355) (by norm_num)
theorem B545773 : Blo 483789 545773 := bbase (se 3 (by rfl) ⟨102332, by rfl⟩ : syracuseStep 545773 = 204665) (by norm_num)
theorem B545809 : Blo 483789 545809 := bbase (se 2 (by rfl) ⟨204678, by rfl⟩ : syracuseStep 545809 = 409357) (by norm_num)
theorem B1561621 : Blo 483789 1561621 := bbase (se 6 (by rfl) ⟨36600, by rfl⟩ : syracuseStep 1561621 = 73201) (by norm_num)
theorem B545845 : Blo 483789 545845 := bbase (se 5 (by rfl) ⟨25586, by rfl⟩ : syracuseStep 545845 = 51173) (by norm_num)
theorem B1168469 : Blo 483789 1168469 := bbase (se 8 (by rfl) ⟨6846, by rfl⟩ : syracuseStep 1168469 = 13693) (by norm_num)
theorem B545881 : Blo 483789 545881 := bbase (se 2 (by rfl) ⟨204705, by rfl⟩ : syracuseStep 545881 = 409411) (by norm_num)
theorem B545917 : Blo 483789 545917 := bbase (se 3 (by rfl) ⟨102359, by rfl⟩ : syracuseStep 545917 = 204719) (by norm_num)
theorem B545953 : Blo 483789 545953 := bbase (se 2 (by rfl) ⟨204732, by rfl⟩ : syracuseStep 545953 = 409465) (by norm_num)
theorem B545989 : Blo 483789 545989 := bbase (se 4 (by rfl) ⟨51186, by rfl⟩ : syracuseStep 545989 = 102373) (by norm_num)
theorem B546025 : Blo 483789 546025 := bbase (se 2 (by rfl) ⟨204759, by rfl⟩ : syracuseStep 546025 = 409519) (by norm_num)
theorem B546061 : Blo 483789 546061 := bbase (se 3 (by rfl) ⟨102386, by rfl⟩ : syracuseStep 546061 = 204773) (by norm_num)
theorem B546097 : Blo 483789 546097 := bbase (se 2 (by rfl) ⟨204786, by rfl⟩ : syracuseStep 546097 = 409573) (by norm_num)
theorem B1234237 : Blo 483789 1234237 := bbase (se 3 (by rfl) ⟨231419, by rfl⟩ : syracuseStep 1234237 = 462839) (by norm_num)
theorem B546133 : Blo 483789 546133 := bbase (se 16 (by rfl) ⟨12, by rfl⟩ : syracuseStep 546133 = 25) (by norm_num)
theorem B546169 : Blo 483789 546169 := bbase (se 2 (by rfl) ⟨204813, by rfl⟩ : syracuseStep 546169 = 409627) (by norm_num)
theorem B546205 : Blo 483789 546205 := bbase (se 3 (by rfl) ⟨102413, by rfl⟩ : syracuseStep 546205 = 204827) (by norm_num)
theorem B1234349 : Blo 483789 1234349 := bbase (se 3 (by rfl) ⟨231440, by rfl⟩ : syracuseStep 1234349 = 462881) (by norm_num)
theorem B546241 : Blo 483789 546241 := bbase (se 2 (by rfl) ⟨204840, by rfl⟩ : syracuseStep 546241 = 409681) (by norm_num)
theorem B546277 : Blo 483789 546277 := bbase (se 4 (by rfl) ⟨51213, by rfl⟩ : syracuseStep 546277 = 102427) (by norm_num)
theorem B775685 : Blo 483789 775685 := bbase (se 4 (by rfl) ⟨72720, by rfl⟩ : syracuseStep 775685 = 145441) (by norm_num)
theorem B1168901 : Blo 483789 1168901 := bbase (se 4 (by rfl) ⟨109584, by rfl⟩ : syracuseStep 1168901 = 219169) (by norm_num)
theorem B546313 : Blo 483789 546313 := bbase (se 2 (by rfl) ⟨204867, by rfl⟩ : syracuseStep 546313 = 409735) (by norm_num)
theorem B546349 : Blo 483789 546349 := bbase (se 3 (by rfl) ⟨102440, by rfl⟩ : syracuseStep 546349 = 204881) (by norm_num)
theorem B546385 : Blo 483789 546385 := bbase (se 2 (by rfl) ⟨204894, by rfl⟩ : syracuseStep 546385 = 409789) (by norm_num)
theorem B1234541 : Blo 483789 1234541 := bbase (se 3 (by rfl) ⟨231476, by rfl⟩ : syracuseStep 1234541 = 462953) (by norm_num)
theorem B546421 : Blo 483789 546421 := bbase (se 5 (by rfl) ⟨25613, by rfl⟩ : syracuseStep 546421 = 51227) (by norm_num)
theorem B775813 : Blo 483789 775813 := bbase (se 4 (by rfl) ⟨72732, by rfl⟩ : syracuseStep 775813 = 145465) (by norm_num)
theorem B546457 : Blo 483789 546457 := bbase (se 2 (by rfl) ⟨204921, by rfl⟩ : syracuseStep 546457 = 409843) (by norm_num)
theorem B546493 : Blo 483789 546493 := bbase (se 3 (by rfl) ⟨102467, by rfl⟩ : syracuseStep 546493 = 204935) (by norm_num)
theorem B546529 : Blo 483789 546529 := bbase (se 2 (by rfl) ⟨204948, by rfl⟩ : syracuseStep 546529 = 409897) (by norm_num)
theorem B546565 : Blo 483789 546565 := bbase (se 4 (by rfl) ⟨51240, by rfl⟩ : syracuseStep 546565 = 102481) (by norm_num)
theorem B546601 : Blo 483789 546601 := bbase (se 2 (by rfl) ⟨204975, by rfl⟩ : syracuseStep 546601 = 409951) (by norm_num)
theorem B546637 : Blo 483789 546637 := bbase (se 3 (by rfl) ⟨102494, by rfl⟩ : syracuseStep 546637 = 204989) (by norm_num)
theorem B1169237 : Blo 483789 1169237 := bbase (se 9 (by rfl) ⟨3425, by rfl⟩ : syracuseStep 1169237 = 6851) (by norm_num)
theorem B546673 : Blo 483789 546673 := bbase (se 2 (by rfl) ⟨205002, by rfl⟩ : syracuseStep 546673 = 410005) (by norm_num)
theorem B546709 : Blo 483789 546709 := bbase (se 6 (by rfl) ⟨12813, by rfl⟩ : syracuseStep 546709 = 25627) (by norm_num)
theorem B874405 : Blo 483789 874405 := bbase (se 4 (by rfl) ⟨81975, by rfl⟩ : syracuseStep 874405 = 163951) (by norm_num)
theorem B546745 : Blo 483789 546745 := bbase (se 2 (by rfl) ⟨205029, by rfl⟩ : syracuseStep 546745 = 410059) (by norm_num)
theorem B546781 : Blo 483789 546781 := bbase (se 3 (by rfl) ⟨102521, by rfl⟩ : syracuseStep 546781 = 205043) (by norm_num)
theorem B546817 : Blo 483789 546817 := bbase (se 2 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 546817 = 410113) (by norm_num)
theorem B1660933 : Blo 483789 1660933 := bbase (se 4 (by rfl) ⟨155712, by rfl⟩ : syracuseStep 1660933 = 311425) (by norm_num)
theorem B546853 : Blo 483789 546853 := bbase (se 4 (by rfl) ⟨51267, by rfl⟩ : syracuseStep 546853 = 102535) (by norm_num)
theorem B546889 : Blo 483789 546889 := bbase (se 2 (by rfl) ⟨205083, by rfl⟩ : syracuseStep 546889 = 410167) (by norm_num)
theorem B612461 : Blo 483789 612461 := bbase (se 3 (by rfl) ⟨114836, by rfl⟩ : syracuseStep 612461 = 229673) (by norm_num)
theorem B546925 : Blo 483789 546925 := bbase (se 3 (by rfl) ⟨102548, by rfl⟩ : syracuseStep 546925 = 205097) (by norm_num)
theorem B546961 : Blo 483789 546961 := bbase (se 2 (by rfl) ⟨205110, by rfl⟩ : syracuseStep 546961 = 410221) (by norm_num)
theorem B612517 : Blo 483789 612517 := bbase (se 4 (by rfl) ⟨57423, by rfl⟩ : syracuseStep 612517 = 114847) (by norm_num)
theorem B3496117 : Blo 483789 3496117 := bbase (se 5 (by rfl) ⟨163880, by rfl⟩ : syracuseStep 3496117 = 327761) (by norm_num)
theorem B546997 : Blo 483789 546997 := bbase (se 5 (by rfl) ⟨25640, by rfl⟩ : syracuseStep 546997 = 51281) (by norm_num)
theorem B1104077 : Blo 483789 1104077 := bbase (se 3 (by rfl) ⟨207014, by rfl⟩ : syracuseStep 1104077 = 414029) (by norm_num)
theorem B547033 : Blo 483789 547033 := bbase (se 2 (by rfl) ⟨205137, by rfl⟩ : syracuseStep 547033 = 410275) (by norm_num)
theorem B547069 : Blo 483789 547069 := bbase (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) (by norm_num)
theorem B612613 : Blo 483789 612613 := bbase (se 4 (by rfl) ⟨57432, by rfl⟩ : syracuseStep 612613 = 114865) (by norm_num)
theorem B547105 : Blo 483789 547105 := bbase (se 2 (by rfl) ⟨205164, by rfl⟩ : syracuseStep 547105 = 410329) (by norm_num)
theorem B547141 : Blo 483789 547141 := bbase (se 4 (by rfl) ⟨51294, by rfl⟩ : syracuseStep 547141 = 102589) (by norm_num)
theorem B547177 : Blo 483789 547177 := bbase (se 2 (by rfl) ⟨205191, by rfl⟩ : syracuseStep 547177 = 410383) (by norm_num)
theorem B2218373 : Blo 483789 2218373 := bbase (se 4 (by rfl) ⟨207972, by rfl⟩ : syracuseStep 2218373 = 415945) (by norm_num)
theorem B547213 : Blo 483789 547213 := bbase (se 3 (by rfl) ⟨102602, by rfl⟩ : syracuseStep 547213 = 205205) (by norm_num)
theorem B1038757 : Blo 483789 1038757 := bbase (se 4 (by rfl) ⟨97383, by rfl⟩ : syracuseStep 1038757 = 194767) (by norm_num)
theorem B776621 : Blo 483789 776621 := bbase (se 3 (by rfl) ⟨145616, by rfl⟩ : syracuseStep 776621 = 291233) (by norm_num)
theorem B612785 : Blo 483789 612785 := bbase (se 2 (by rfl) ⟨229794, by rfl⟩ : syracuseStep 612785 = 459589) (by norm_num)
theorem B547249 : Blo 483789 547249 := bbase (se 2 (by rfl) ⟨205218, by rfl⟩ : syracuseStep 547249 = 410437) (by norm_num)
theorem B547285 : Blo 483789 547285 := bbase (se 7 (by rfl) ⟨6413, by rfl⟩ : syracuseStep 547285 = 12827) (by norm_num)
theorem B612841 : Blo 483789 612841 := bbase (se 2 (by rfl) ⟨229815, by rfl⟩ : syracuseStep 612841 = 459631) (by norm_num)
theorem B547321 : Blo 483789 547321 := bbase (se 2 (by rfl) ⟨205245, by rfl⟩ : syracuseStep 547321 = 410491) (by norm_num)
theorem B547357 : Blo 483789 547357 := bbase (se 3 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 547357 = 205259) (by norm_num)
theorem B547393 : Blo 483789 547393 := bbase (se 2 (by rfl) ⟨205272, by rfl⟩ : syracuseStep 547393 = 410545) (by norm_num)
theorem B612937 : Blo 483789 612937 := bbase (se 2 (by rfl) ⟨229851, by rfl⟩ : syracuseStep 612937 = 459703) (by norm_num)
theorem B547429 : Blo 483789 547429 := bbase (se 4 (by rfl) ⟨51321, by rfl⟩ : syracuseStep 547429 = 102643) (by norm_num)
theorem B875125 : Blo 483789 875125 := bbase (se 5 (by rfl) ⟨41021, by rfl⟩ : syracuseStep 875125 = 82043) (by norm_num)
theorem B547465 : Blo 483789 547465 := bbase (se 2 (by rfl) ⟨205299, by rfl⟩ : syracuseStep 547465 = 410599) (by norm_num)
theorem B547501 : Blo 483789 547501 := bbase (se 3 (by rfl) ⟨102656, by rfl⟩ : syracuseStep 547501 = 205313) (by norm_num)
theorem B776909 : Blo 483789 776909 := bbase (se 3 (by rfl) ⟨145670, by rfl⟩ : syracuseStep 776909 = 291341) (by norm_num)
theorem B547537 : Blo 483789 547537 := bbase (se 2 (by rfl) ⟨205326, by rfl⟩ : syracuseStep 547537 = 410653) (by norm_num)
theorem B613109 : Blo 483789 613109 := bbase (se 5 (by rfl) ⟨28739, by rfl⟩ : syracuseStep 613109 = 57479) (by norm_num)
theorem B547573 : Blo 483789 547573 := bbase (se 5 (by rfl) ⟨25667, by rfl⟩ : syracuseStep 547573 = 51335) (by norm_num)
theorem B547609 : Blo 483789 547609 := bbase (se 2 (by rfl) ⟨205353, by rfl⟩ : syracuseStep 547609 = 410707) (by norm_num)
theorem B613165 : Blo 483789 613165 := bbase (se 3 (by rfl) ⟨114968, by rfl⟩ : syracuseStep 613165 = 229937) (by norm_num)
theorem B547645 : Blo 483789 547645 := bbase (se 3 (by rfl) ⟨102683, by rfl⟩ : syracuseStep 547645 = 205367) (by norm_num)
theorem B547681 : Blo 483789 547681 := bbase (se 2 (by rfl) ⟨205380, by rfl⟩ : syracuseStep 547681 = 410761) (by norm_num)
theorem B1170293 : Blo 483789 1170293 := bbase (se 5 (by rfl) ⟨54857, by rfl⟩ : syracuseStep 1170293 = 109715) (by norm_num)
theorem B547717 : Blo 483789 547717 := bbase (se 4 (by rfl) ⟨51348, by rfl⟩ : syracuseStep 547717 = 102697) (by norm_num)
theorem B613261 : Blo 483789 613261 := bbase (se 3 (by rfl) ⟨114986, by rfl⟩ : syracuseStep 613261 = 229973) (by norm_num)
theorem B547753 : Blo 483789 547753 := bbase (se 2 (by rfl) ⟨205407, by rfl⟩ : syracuseStep 547753 = 410815) (by norm_num)
theorem B547789 : Blo 483789 547789 := bbase (se 3 (by rfl) ⟨102710, by rfl⟩ : syracuseStep 547789 = 205421) (by norm_num)
theorem B547825 : Blo 483789 547825 := bbase (se 2 (by rfl) ⟨205434, by rfl⟩ : syracuseStep 547825 = 410869) (by norm_num)
theorem B547861 : Blo 483789 547861 := bbase (se 6 (by rfl) ⟨12840, by rfl⟩ : syracuseStep 547861 = 25681) (by norm_num)
theorem B613433 : Blo 483789 613433 := bbase (se 2 (by rfl) ⟨230037, by rfl⟩ : syracuseStep 613433 = 460075) (by norm_num)
theorem B547897 : Blo 483789 547897 := bbase (se 2 (by rfl) ⟨205461, by rfl⟩ : syracuseStep 547897 = 410923) (by norm_num)
theorem B547933 : Blo 483789 547933 := bbase (se 3 (by rfl) ⟨102737, by rfl⟩ : syracuseStep 547933 = 205475) (by norm_num)
theorem B777325 : Blo 483789 777325 := bbase (se 3 (by rfl) ⟨145748, by rfl⟩ : syracuseStep 777325 = 291497) (by norm_num)
theorem B613489 : Blo 483789 613489 := bbase (se 2 (by rfl) ⟨230058, by rfl⟩ : syracuseStep 613489 = 460117) (by norm_num)
theorem B547969 : Blo 483789 547969 := bbase (se 2 (by rfl) ⟨205488, by rfl⟩ : syracuseStep 547969 = 410977) (by norm_num)
theorem B548005 : Blo 483789 548005 := bbase (se 4 (by rfl) ⟨51375, by rfl⟩ : syracuseStep 548005 = 102751) (by norm_num)
theorem B548041 : Blo 483789 548041 := bbase (se 2 (by rfl) ⟨205515, by rfl⟩ : syracuseStep 548041 = 411031) (by norm_num)
theorem B613585 : Blo 483789 613585 := bbase (se 2 (by rfl) ⟨230094, by rfl⟩ : syracuseStep 613585 = 460189) (by norm_num)
theorem B548077 : Blo 483789 548077 := bbase (se 3 (by rfl) ⟨102764, by rfl⟩ : syracuseStep 548077 = 205529) (by norm_num)
theorem B875789 : Blo 483789 875789 := bbase (se 3 (by rfl) ⟨164210, by rfl⟩ : syracuseStep 875789 = 328421) (by norm_num)
theorem B548113 : Blo 483789 548113 := bbase (se 2 (by rfl) ⟨205542, by rfl⟩ : syracuseStep 548113 = 411085) (by norm_num)
theorem B3104021 : Blo 483789 3104021 := bbase (se 6 (by rfl) ⟨72750, by rfl⟩ : syracuseStep 3104021 = 145501) (by norm_num)
theorem B1039645 : Blo 483789 1039645 := bbase (se 3 (by rfl) ⟨194933, by rfl⟩ : syracuseStep 1039645 = 389867) (by norm_num)
theorem B548149 : Blo 483789 548149 := bbase (se 5 (by rfl) ⟨25694, by rfl⟩ : syracuseStep 548149 = 51389) (by norm_num)
theorem B548185 : Blo 483789 548185 := bbase (se 2 (by rfl) ⟨205569, by rfl⟩ : syracuseStep 548185 = 411139) (by norm_num)
theorem B613757 : Blo 483789 613757 := bbase (se 3 (by rfl) ⟨115079, by rfl⟩ : syracuseStep 613757 = 230159) (by norm_num)
theorem B548221 : Blo 483789 548221 := bbase (se 3 (by rfl) ⟨102791, by rfl⟩ : syracuseStep 548221 = 205583) (by norm_num)
theorem B548257 : Blo 483789 548257 := bbase (se 2 (by rfl) ⟨205596, by rfl⟩ : syracuseStep 548257 = 411193) (by norm_num)
theorem B613813 : Blo 483789 613813 := bbase (se 5 (by rfl) ⟨28772, by rfl⟩ : syracuseStep 613813 = 57545) (by norm_num)
theorem B548293 : Blo 483789 548293 := bbase (se 4 (by rfl) ⟨51402, by rfl⟩ : syracuseStep 548293 = 102805) (by norm_num)
theorem B548329 : Blo 483789 548329 := bbase (se 2 (by rfl) ⟨205623, by rfl⟩ : syracuseStep 548329 = 411247) (by norm_num)
theorem B548365 : Blo 483789 548365 := bbase (se 3 (by rfl) ⟨102818, by rfl⟩ : syracuseStep 548365 = 205637) (by norm_num)
theorem B613909 : Blo 483789 613909 := bbase (se 6 (by rfl) ⟨14388, by rfl⟩ : syracuseStep 613909 = 28777) (by norm_num)
theorem B548401 : Blo 483789 548401 := bbase (se 2 (by rfl) ⟨205650, by rfl⟩ : syracuseStep 548401 = 411301) (by norm_num)
theorem B4677173 : Blo 483789 4677173 := bbase (se 5 (by rfl) ⟨219242, by rfl⟩ : syracuseStep 4677173 = 438485) (by norm_num)
theorem B548437 : Blo 483789 548437 := bbase (se 8 (by rfl) ⟨3213, by rfl⟩ : syracuseStep 548437 = 6427) (by norm_num)
theorem B1662565 : Blo 483789 1662565 := bbase (se 4 (by rfl) ⟨155865, by rfl⟩ : syracuseStep 1662565 = 311731) (by norm_num)
theorem B548473 : Blo 483789 548473 := bbase (se 2 (by rfl) ⟨205677, by rfl⟩ : syracuseStep 548473 = 411355) (by norm_num)
theorem B548509 : Blo 483789 548509 := bbase (se 3 (by rfl) ⟨102845, by rfl⟩ : syracuseStep 548509 = 205691) (by norm_num)
theorem B614081 : Blo 483789 614081 := bbase (se 2 (by rfl) ⟨230280, by rfl⟩ : syracuseStep 614081 = 460561) (by norm_num)
theorem B548545 : Blo 483789 548545 := bbase (se 2 (by rfl) ⟨205704, by rfl⟩ : syracuseStep 548545 = 411409) (by norm_num)
theorem B548581 : Blo 483789 548581 := bbase (se 4 (by rfl) ⟨51429, by rfl⟩ : syracuseStep 548581 = 102859) (by norm_num)
theorem B614137 : Blo 483789 614137 := bbase (se 2 (by rfl) ⟨230301, by rfl⟩ : syracuseStep 614137 = 460603) (by norm_num)
theorem B548617 : Blo 483789 548617 := bbase (se 2 (by rfl) ⟨205731, by rfl⟩ : syracuseStep 548617 = 411463) (by norm_num)
theorem B1040141 : Blo 483789 1040141 := bbase (se 3 (by rfl) ⟨195026, by rfl⟩ : syracuseStep 1040141 = 390053) (by norm_num)
theorem B548653 : Blo 483789 548653 := bbase (se 3 (by rfl) ⟨102872, by rfl⟩ : syracuseStep 548653 = 205745) (by norm_num)
theorem B548689 : Blo 483789 548689 := bbase (se 2 (by rfl) ⟨205758, by rfl⟩ : syracuseStep 548689 = 411517) (by norm_num)
theorem B614233 : Blo 483789 614233 := bbase (se 2 (by rfl) ⟨230337, by rfl⟩ : syracuseStep 614233 = 460675) (by norm_num)
theorem B548725 : Blo 483789 548725 := bbase (se 5 (by rfl) ⟨25721, by rfl⟩ : syracuseStep 548725 = 51443) (by norm_num)
theorem B548761 : Blo 483789 548761 := bbase (se 2 (by rfl) ⟨205785, by rfl⟩ : syracuseStep 548761 = 411571) (by norm_num)
theorem B1105829 : Blo 483789 1105829 := bbase (se 4 (by rfl) ⟨103671, by rfl⟩ : syracuseStep 1105829 = 207343) (by norm_num)
theorem B614405 : Blo 483789 614405 := bbase (se 4 (by rfl) ⟨57600, by rfl⟩ : syracuseStep 614405 = 115201) (by norm_num)
theorem B778261 : Blo 483789 778261 := bbase (se 6 (by rfl) ⟨18240, by rfl⟩ : syracuseStep 778261 = 36481) (by norm_num)
theorem B614461 : Blo 483789 614461 := bbase (se 3 (by rfl) ⟨115211, by rfl⟩ : syracuseStep 614461 = 230423) (by norm_num)
theorem B581725 : Blo 483789 581725 := bbase (se 3 (by rfl) ⟨109073, by rfl⟩ : syracuseStep 581725 = 218147) (by norm_num)
theorem B614557 : Blo 483789 614557 := bbase (se 3 (by rfl) ⟨115229, by rfl⟩ : syracuseStep 614557 = 230459) (by norm_num)
theorem B614729 : Blo 483789 614729 := bbase (se 2 (by rfl) ⟨230523, by rfl⟩ : syracuseStep 614729 = 461047) (by norm_num)
theorem B614785 : Blo 483789 614785 := bbase (se 2 (by rfl) ⟨230544, by rfl⟩ : syracuseStep 614785 = 461089) (by norm_num)
theorem B614881 : Blo 483789 614881 := bbase (se 2 (by rfl) ⟨230580, by rfl⟩ : syracuseStep 614881 = 461161) (by norm_num)
theorem B2449925 : Blo 483789 2449925 := bbase (se 4 (by rfl) ⟨229680, by rfl⟩ : syracuseStep 2449925 = 459361) (by norm_num)
theorem B2482741 : Blo 483789 2482741 := bbase (se 5 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 2482741 = 232757) (by norm_num)
theorem B516709 : Blo 483789 516709 := bbase (se 4 (by rfl) ⟨48441, by rfl⟩ : syracuseStep 516709 = 96883) (by norm_num)
theorem B516713 : Blo 483789 516713 := bbase (se 2 (by rfl) ⟨193767, by rfl⟩ : syracuseStep 516713 = 387535) (by norm_num)
theorem B1041005 : Blo 483789 1041005 := bbase (se 3 (by rfl) ⟨195188, by rfl⟩ : syracuseStep 1041005 = 390377) (by norm_num)
theorem B615053 : Blo 483789 615053 := bbase (se 3 (by rfl) ⟨115322, by rfl⟩ : syracuseStep 615053 = 230645) (by norm_num)
theorem B811661 : Blo 483789 811661 := bbase (se 3 (by rfl) ⟨152186, by rfl⟩ : syracuseStep 811661 = 304373) (by norm_num)
theorem B615109 : Blo 483789 615109 := bbase (se 4 (by rfl) ⟨57666, by rfl⟩ : syracuseStep 615109 = 115333) (by norm_num)
theorem B1041149 : Blo 483789 1041149 := bbase (se 3 (by rfl) ⟨195215, by rfl⟩ : syracuseStep 1041149 = 390431) (by norm_num)
theorem B582437 : Blo 483789 582437 := bbase (se 4 (by rfl) ⟨54603, by rfl⟩ : syracuseStep 582437 = 109207) (by norm_num)
theorem B615205 : Blo 483789 615205 := bbase (se 4 (by rfl) ⟨57675, by rfl⟩ : syracuseStep 615205 = 115351) (by norm_num)
theorem B615377 : Blo 483789 615377 := bbase (se 2 (by rfl) ⟨230766, by rfl⟩ : syracuseStep 615377 = 461533) (by norm_num)
theorem B615433 : Blo 483789 615433 := bbase (se 2 (by rfl) ⟨230787, by rfl⟩ : syracuseStep 615433 = 461575) (by norm_num)
theorem B615529 : Blo 483789 615529 := bbase (se 2 (by rfl) ⟨230823, by rfl⟩ : syracuseStep 615529 = 461647) (by norm_num)
theorem B582773 : Blo 483789 582773 := bbase (se 5 (by rfl) ⟨27317, by rfl⟩ : syracuseStep 582773 = 54635) (by norm_num)
theorem B517277 : Blo 483789 517277 := bbase (se 3 (by rfl) ⟨96989, by rfl⟩ : syracuseStep 517277 = 193979) (by norm_num)
theorem B779453 : Blo 483789 779453 := bbase (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) (by norm_num)
theorem B582889 : Blo 483789 582889 := bbase (se 2 (by rfl) ⟨218583, by rfl⟩ : syracuseStep 582889 = 437167) (by norm_num)
theorem B582913 : Blo 483789 582913 := bbase (se 2 (by rfl) ⟨218592, by rfl⟩ : syracuseStep 582913 = 437185) (by norm_num)
theorem B615701 : Blo 483789 615701 := bbase (se 6 (by rfl) ⟨14430, by rfl⟩ : syracuseStep 615701 = 28861) (by norm_num)
theorem B615757 : Blo 483789 615757 := bbase (se 3 (by rfl) ⟨115454, by rfl⟩ : syracuseStep 615757 = 230909) (by norm_num)
theorem B517465 : Blo 483789 517465 := bbase (se 2 (by rfl) ⟨194049, by rfl⟩ : syracuseStep 517465 = 388099) (by norm_num)
theorem B779645 : Blo 483789 779645 := bbase (se 3 (by rfl) ⟨146183, by rfl⟩ : syracuseStep 779645 = 292367) (by norm_num)
theorem B615853 : Blo 483789 615853 := bbase (se 3 (by rfl) ⟨115472, by rfl⟩ : syracuseStep 615853 = 230945) (by norm_num)
theorem B616025 : Blo 483789 616025 := bbase (se 2 (by rfl) ⟨231009, by rfl⟩ : syracuseStep 616025 = 462019) (by norm_num)
theorem B878197 : Blo 483789 878197 := bbase (se 5 (by rfl) ⟨41165, by rfl⟩ : syracuseStep 878197 = 82331) (by norm_num)
theorem B616081 : Blo 483789 616081 := bbase (se 2 (by rfl) ⟨231030, by rfl⟩ : syracuseStep 616081 = 462061) (by norm_num)
theorem B616177 : Blo 483789 616177 := bbase (se 2 (by rfl) ⟨231066, by rfl⟩ : syracuseStep 616177 = 462133) (by norm_num)
theorem B2451221 : Blo 483789 2451221 := bbase (se 6 (by rfl) ⟨57450, by rfl⟩ : syracuseStep 2451221 = 114901) (by norm_num)
theorem B616349 : Blo 483789 616349 := bbase (se 3 (by rfl) ⟨115565, by rfl⟩ : syracuseStep 616349 = 231131) (by norm_num)
theorem B583609 : Blo 483789 583609 := bbase (se 2 (by rfl) ⟨218853, by rfl⟩ : syracuseStep 583609 = 437707) (by norm_num)
theorem B616405 : Blo 483789 616405 := bbase (se 7 (by rfl) ⟨7223, by rfl⟩ : syracuseStep 616405 = 14447) (by norm_num)
theorem B15820757 : Blo 483789 15820757 := bbase (se 7 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 15820757 = 370799) (by norm_num)
theorem B583705 : Blo 483789 583705 := bbase (se 2 (by rfl) ⟨218889, by rfl⟩ : syracuseStep 583705 = 437779) (by norm_num)
theorem B616501 : Blo 483789 616501 := bbase (se 5 (by rfl) ⟨28898, by rfl⟩ : syracuseStep 616501 = 57797) (by norm_num)
theorem B878701 : Blo 483789 878701 := bbase (se 3 (by rfl) ⟨164756, by rfl⟩ : syracuseStep 878701 = 329513) (by norm_num)
theorem B518285 : Blo 483789 518285 := bbase (se 3 (by rfl) ⟨97178, by rfl⟩ : syracuseStep 518285 = 194357) (by norm_num)
theorem B616673 : Blo 483789 616673 := bbase (se 2 (by rfl) ⟨231252, by rfl⟩ : syracuseStep 616673 = 462505) (by norm_num)
theorem B616729 : Blo 483789 616729 := bbase (se 2 (by rfl) ⟨231273, by rfl⟩ : syracuseStep 616729 = 462547) (by norm_num)
theorem B616825 : Blo 483789 616825 := bbase (se 2 (by rfl) ⟨231309, by rfl⟩ : syracuseStep 616825 = 462619) (by norm_num)
theorem B616997 : Blo 483789 616997 := bbase (se 4 (by rfl) ⟨57843, by rfl⟩ : syracuseStep 616997 = 115687) (by norm_num)
theorem B518729 : Blo 483789 518729 := bbase (se 2 (by rfl) ⟨194523, by rfl⟩ : syracuseStep 518729 = 389047) (by norm_num)
theorem B617053 : Blo 483789 617053 := bbase (se 3 (by rfl) ⟨115697, by rfl⟩ : syracuseStep 617053 = 231395) (by norm_num)
theorem B617149 : Blo 483789 617149 := bbase (se 3 (by rfl) ⟨115715, by rfl⟩ : syracuseStep 617149 = 231431) (by norm_num)
theorem B1633013 : Blo 483789 1633013 := bbase (se 5 (by rfl) ⟨76547, by rfl⟩ : syracuseStep 1633013 = 153095) (by norm_num)
theorem B781093 : Blo 483789 781093 := bbase (se 4 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 781093 = 146455) (by norm_num)
theorem B551729 : Blo 483789 551729 := bbase (se 2 (by rfl) ⟨206898, by rfl⟩ : syracuseStep 551729 = 413797) (by norm_num)
theorem B518977 : Blo 483789 518977 := bbase (se 2 (by rfl) ⟨194616, by rfl⟩ : syracuseStep 518977 = 389233) (by norm_num)
theorem B617321 : Blo 483789 617321 := bbase (se 2 (by rfl) ⟨231495, by rfl⟩ : syracuseStep 617321 = 462991) (by norm_num)
theorem B551893 : Blo 483789 551893 := bbase (se 7 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 551893 = 12935) (by norm_num)
theorem B584705 : Blo 483789 584705 := bbase (se 2 (by rfl) ⟨219264, by rfl⟩ : syracuseStep 584705 = 438529) (by norm_num)
theorem B2452517 : Blo 483789 2452517 := bbase (se 4 (by rfl) ⟨229923, by rfl⟩ : syracuseStep 2452517 = 459847) (by norm_num)
theorem B1633445 : Blo 483789 1633445 := bbase (se 4 (by rfl) ⟨153135, by rfl⟩ : syracuseStep 1633445 = 306271) (by norm_num)
theorem B2616533 : Blo 483789 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B519409 : Blo 483789 519409 := bbase (se 2 (by rfl) ⟨194778, by rfl⟩ : syracuseStep 519409 = 389557) (by norm_num)
theorem B584993 : Blo 483789 584993 := bbase (se 2 (by rfl) ⟨219372, by rfl⟩ : syracuseStep 584993 = 438745) (by norm_num)
theorem B3697973 : Blo 483789 3697973 := bbase (se 5 (by rfl) ⟨173342, by rfl⟩ : syracuseStep 3697973 = 346685) (by norm_num)
theorem B519481 : Blo 483789 519481 := bbase (se 2 (by rfl) ⟨194805, by rfl⟩ : syracuseStep 519481 = 389611) (by norm_num)
theorem B2616725 : Blo 483789 2616725 := bbase (se 6 (by rfl) ⟨61329, by rfl⟩ : syracuseStep 2616725 = 122659) (by norm_num)
theorem B585157 : Blo 483789 585157 := bbase (se 4 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 585157 = 109717) (by norm_num)
theorem B2223557 : Blo 483789 2223557 := bbase (se 4 (by rfl) ⟨208458, by rfl⟩ : syracuseStep 2223557 = 416917) (by norm_num)
theorem B585185 : Blo 483789 585185 := bbase (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) (by norm_num)
theorem B1633877 : Blo 483789 1633877 := bbase (se 8 (by rfl) ⟨9573, by rfl⟩ : syracuseStep 1633877 = 19147) (by norm_num)
theorem B585301 : Blo 483789 585301 := bbase (se 8 (by rfl) ⟨3429, by rfl⟩ : syracuseStep 585301 = 6859) (by norm_num)
theorem B519853 : Blo 483789 519853 := bbase (se 3 (by rfl) ⟨97472, by rfl⟩ : syracuseStep 519853 = 194945) (by norm_num)
theorem B585397 : Blo 483789 585397 := bbase (se 5 (by rfl) ⟨27440, by rfl⟩ : syracuseStep 585397 = 54881) (by norm_num)
theorem B1109717 : Blo 483789 1109717 := bbase (se 7 (by rfl) ⟨13004, by rfl⟩ : syracuseStep 1109717 = 26009) (by norm_num)
theorem B1109909 : Blo 483789 1109909 := bbase (se 6 (by rfl) ⟨26013, by rfl⟩ : syracuseStep 1109909 = 52027) (by norm_num)
theorem B1666981 : Blo 483789 1666981 := bbase (se 4 (by rfl) ⟨156279, by rfl⟩ : syracuseStep 1666981 = 312559) (by norm_num)
theorem B1634309 : Blo 483789 1634309 := bbase (se 4 (by rfl) ⟨153216, by rfl⟩ : syracuseStep 1634309 = 306433) (by norm_num)
theorem B520229 : Blo 483789 520229 := bbase (se 4 (by rfl) ⟨48771, by rfl⟩ : syracuseStep 520229 = 97543) (by norm_num)
theorem B520301 : Blo 483789 520301 := bbase (se 3 (by rfl) ⟨97556, by rfl⟩ : syracuseStep 520301 = 195113) (by norm_num)
theorem B585877 : Blo 483789 585877 := bbase (se 6 (by rfl) ⟨13731, by rfl⟩ : syracuseStep 585877 = 27463) (by norm_num)
theorem B520489 : Blo 483789 520489 := bbase (se 2 (by rfl) ⟨195183, by rfl⟩ : syracuseStep 520489 = 390367) (by norm_num)
theorem B2453813 : Blo 483789 2453813 := bbase (se 5 (by rfl) ⟨115022, by rfl⟩ : syracuseStep 2453813 = 230045) (by norm_num)
theorem B1634741 : Blo 483789 1634741 := bbase (se 5 (by rfl) ⟨76628, by rfl⟩ : syracuseStep 1634741 = 153257) (by norm_num)
theorem B520673 : Blo 483789 520673 := bbase (se 2 (by rfl) ⟨195252, by rfl⟩ : syracuseStep 520673 = 390505) (by norm_num)
theorem B488141 : Blo 483789 488141 := bbase (se 3 (by rfl) ⟨91526, by rfl⟩ : syracuseStep 488141 = 183053) (by norm_num)
theorem B5665621 : Blo 483789 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B1635173 : Blo 483789 1635173 := bbase (se 4 (by rfl) ⟨153297, by rfl⟩ : syracuseStep 1635173 = 306595) (by norm_num)
theorem B553969 : Blo 483789 553969 := bbase (se 2 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 553969 = 415477) (by norm_num)
theorem B554009 : Blo 483789 554009 := bbase (se 2 (by rfl) ⟨207753, by rfl⟩ : syracuseStep 554009 = 415507) (by norm_num)
theorem B1635605 : Blo 483789 1635605 := bbase (se 6 (by rfl) ⟨38334, by rfl⟩ : syracuseStep 1635605 = 76669) (by norm_num)
theorem B816493 : Blo 483789 816493 := bbase (se 3 (by rfl) ⟨153092, by rfl⟩ : syracuseStep 816493 = 306185) (by norm_num)
theorem B816581 : Blo 483789 816581 := bbase (se 4 (by rfl) ⟨76554, by rfl⟩ : syracuseStep 816581 = 153109) (by norm_num)
theorem B816709 : Blo 483789 816709 := bbase (se 4 (by rfl) ⟨76566, by rfl⟩ : syracuseStep 816709 = 153133) (by norm_num)
theorem B2455109 : Blo 483789 2455109 := bbase (se 4 (by rfl) ⟨230166, by rfl⟩ : syracuseStep 2455109 = 460333) (by norm_num)
theorem B816797 : Blo 483789 816797 := bbase (se 3 (by rfl) ⟨153149, by rfl⟩ : syracuseStep 816797 = 306299) (by norm_num)
theorem B1111733 : Blo 483789 1111733 := bbase (se 5 (by rfl) ⟨52112, by rfl⟩ : syracuseStep 1111733 = 104225) (by norm_num)
theorem B2815669 : Blo 483789 2815669 := bbase (se 5 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 2815669 = 263969) (by norm_num)
theorem B1636037 : Blo 483789 1636037 := bbase (se 4 (by rfl) ⟨153378, by rfl⟩ : syracuseStep 1636037 = 306757) (by norm_num)
theorem B816925 : Blo 483789 816925 := bbase (se 3 (by rfl) ⟨153173, by rfl⟩ : syracuseStep 816925 = 306347) (by norm_num)
theorem B554845 : Blo 483789 554845 := bbase (se 3 (by rfl) ⟨104033, by rfl⟩ : syracuseStep 554845 = 208067) (by norm_num)
theorem B817013 : Blo 483789 817013 := bbase (se 5 (by rfl) ⟨38297, by rfl⟩ : syracuseStep 817013 = 76595) (by norm_num)
theorem B817141 : Blo 483789 817141 := bbase (se 5 (by rfl) ⟨38303, by rfl⟩ : syracuseStep 817141 = 76607) (by norm_num)
theorem B817229 : Blo 483789 817229 := bbase (se 3 (by rfl) ⟨153230, by rfl⟩ : syracuseStep 817229 = 306461) (by norm_num)
theorem B1636469 : Blo 483789 1636469 := bbase (se 5 (by rfl) ⟨76709, by rfl⟩ : syracuseStep 1636469 = 153419) (by norm_num)
theorem B817357 : Blo 483789 817357 := bbase (se 3 (by rfl) ⟨153254, by rfl⟩ : syracuseStep 817357 = 306509) (by norm_num)
theorem B555241 : Blo 483789 555241 := bbase (se 2 (by rfl) ⟨208215, by rfl⟩ : syracuseStep 555241 = 416431) (by norm_num)
theorem B817445 : Blo 483789 817445 := bbase (se 4 (by rfl) ⟨76635, by rfl⟩ : syracuseStep 817445 = 153271) (by norm_num)
theorem B19003733 : Blo 483789 19003733 := bbase (se 10 (by rfl) ⟨27837, by rfl⟩ : syracuseStep 19003733 = 55675) (by norm_num)
theorem B817573 : Blo 483789 817573 := bbase (se 4 (by rfl) ⟨76647, by rfl⟩ : syracuseStep 817573 = 153295) (by norm_num)
theorem B817661 : Blo 483789 817661 := bbase (se 3 (by rfl) ⟨153311, by rfl⟩ : syracuseStep 817661 = 306623) (by norm_num)
theorem B1243669 : Blo 483789 1243669 := bbase (se 6 (by rfl) ⟨29148, by rfl⟩ : syracuseStep 1243669 = 58297) (by norm_num)
theorem B981533 : Blo 483789 981533 := bbase (se 3 (by rfl) ⟨184037, by rfl⟩ : syracuseStep 981533 = 368075) (by norm_num)
theorem B1636901 : Blo 483789 1636901 := bbase (se 4 (by rfl) ⟨153459, by rfl⟩ : syracuseStep 1636901 = 306919) (by norm_num)
theorem B981613 : Blo 483789 981613 := bbase (se 3 (by rfl) ⟨184052, by rfl⟩ : syracuseStep 981613 = 368105) (by norm_num)
theorem B817789 : Blo 483789 817789 := bbase (se 3 (by rfl) ⟨153335, by rfl⟩ : syracuseStep 817789 = 306671) (by norm_num)
theorem B817877 : Blo 483789 817877 := bbase (se 7 (by rfl) ⟨9584, by rfl⟩ : syracuseStep 817877 = 19169) (by norm_num)
theorem B1178389 : Blo 483789 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B818005 : Blo 483789 818005 := bbase (se 9 (by rfl) ⟨2396, by rfl⟩ : syracuseStep 818005 = 4793) (by norm_num)
theorem B2456405 : Blo 483789 2456405 := bbase (se 9 (by rfl) ⟨7196, by rfl⟩ : syracuseStep 2456405 = 14393) (by norm_num)
theorem B621413 : Blo 483789 621413 := bbase (se 4 (by rfl) ⟨58257, by rfl⟩ : syracuseStep 621413 = 116515) (by norm_num)
theorem B818093 : Blo 483789 818093 := bbase (se 3 (by rfl) ⟨153392, by rfl⟩ : syracuseStep 818093 = 306785) (by norm_num)
theorem B1637333 : Blo 483789 1637333 := bbase (se 7 (by rfl) ⟨19187, by rfl⟩ : syracuseStep 1637333 = 38375) (by norm_num)
theorem B818221 : Blo 483789 818221 := bbase (se 3 (by rfl) ⟨153416, by rfl⟩ : syracuseStep 818221 = 306833) (by norm_num)
theorem B818309 : Blo 483789 818309 := bbase (se 4 (by rfl) ⟨76716, by rfl⟩ : syracuseStep 818309 = 153433) (by norm_num)
theorem B982181 : Blo 483789 982181 := bbase (se 4 (by rfl) ⟨92079, by rfl⟩ : syracuseStep 982181 = 184159) (by norm_num)
theorem B2489573 : Blo 483789 2489573 := bbase (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) (by norm_num)
theorem B818437 : Blo 483789 818437 := bbase (se 4 (by rfl) ⟨76728, by rfl⟩ : syracuseStep 818437 = 153457) (by norm_num)
theorem B818525 : Blo 483789 818525 := bbase (se 3 (by rfl) ⟨153473, by rfl⟩ : syracuseStep 818525 = 306947) (by norm_num)
theorem B1637765 : Blo 483789 1637765 := bbase (se 4 (by rfl) ⟨153540, by rfl⟩ : syracuseStep 1637765 = 307081) (by norm_num)
theorem B818653 : Blo 483789 818653 := bbase (se 3 (by rfl) ⟨153497, by rfl⟩ : syracuseStep 818653 = 306995) (by norm_num)
theorem B818741 : Blo 483789 818741 := bbase (se 5 (by rfl) ⟨38378, by rfl⟩ : syracuseStep 818741 = 76757) (by norm_num)
theorem B1638005 : Blo 483789 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B818869 : Blo 483789 818869 := bbase (se 5 (by rfl) ⟨38384, by rfl⟩ : syracuseStep 818869 = 76769) (by norm_num)
theorem B818957 : Blo 483789 818957 := bbase (se 3 (by rfl) ⟨153554, by rfl⟩ : syracuseStep 818957 = 307109) (by norm_num)
theorem B655133 : Blo 483789 655133 := bbase (se 3 (by rfl) ⟨122837, by rfl⟩ : syracuseStep 655133 = 245675) (by norm_num)
theorem B1638197 : Blo 483789 1638197 := bbase (se 5 (by rfl) ⟨76790, by rfl⟩ : syracuseStep 1638197 = 153581) (by norm_num)
theorem B5930837 : Blo 483789 5930837 := bbase (se 9 (by rfl) ⟨17375, by rfl⟩ : syracuseStep 5930837 = 34751) (by norm_num)
theorem B819085 : Blo 483789 819085 := bbase (se 3 (by rfl) ⟨153578, by rfl⟩ : syracuseStep 819085 = 307157) (by norm_num)
theorem B2326421 : Blo 483789 2326421 := bbase (se 6 (by rfl) ⟨54525, by rfl⟩ : syracuseStep 2326421 = 109051) (by norm_num)
theorem B655285 : Blo 483789 655285 := bbase (se 5 (by rfl) ⟨30716, by rfl⟩ : syracuseStep 655285 = 61433) (by norm_num)
theorem B819173 : Blo 483789 819173 := bbase (se 4 (by rfl) ⟨76797, by rfl⟩ : syracuseStep 819173 = 153595) (by norm_num)
theorem B1638413 : Blo 483789 1638413 := bstep (se 3 (by rfl) ⟨307202, by rfl⟩ : syracuseStep 1638413 = 614405) B614405
theorem B1638467 : Blo 483789 1638467 := bstep (se 1 (by rfl) ⟨1228850, by rfl⟩ : syracuseStep 1638467 = 2457701) B2457701
theorem B1572941 : Blo 483789 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B819281 : Blo 483789 819281 := bstep (se 2 (by rfl) ⟨307230, by rfl⟩ : syracuseStep 819281 = 614461) B614461
theorem B983171 : Blo 483789 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B3113093 : Blo 483789 3113093 := bstep (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) B583705
theorem B819409 : Blo 483789 819409 := bstep (se 2 (by rfl) ⟨307278, by rfl⟩ : syracuseStep 819409 = 614557) B614557
theorem B819443 : Blo 483789 819443 := bstep (se 1 (by rfl) ⟨614582, by rfl⟩ : syracuseStep 819443 = 1229165) B1229165
theorem B1638737 : Blo 483789 1638737 := bstep (se 2 (by rfl) ⟨614526, by rfl⟩ : syracuseStep 1638737 = 1229053) B1229053
theorem B819571 : Blo 483789 819571 := bstep (se 1 (by rfl) ⟨614678, by rfl⟩ : syracuseStep 819571 = 1229357) B1229357
theorem B655825 : Blo 483789 655825 := bstep (se 2 (by rfl) ⟨245934, by rfl⟩ : syracuseStep 655825 = 491869) B491869
theorem B819713 : Blo 483789 819713 := bstep (se 2 (by rfl) ⟨307392, by rfl⟩ : syracuseStep 819713 = 614785) B614785
theorem B819841 : Blo 483789 819841 := bstep (se 2 (by rfl) ⟨307440, by rfl⟩ : syracuseStep 819841 = 614881) B614881
theorem B819875 : Blo 483789 819875 := bstep (se 1 (by rfl) ⟨614906, by rfl⟩ : syracuseStep 819875 = 1229813) B1229813
theorem B3310321 : Blo 483789 3310321 := bstep (se 2 (by rfl) ⟨1241370, by rfl⟩ : syracuseStep 3310321 = 2482741) B2482741
theorem B492323 : Blo 483789 492323 := bstep (se 1 (by rfl) ⟨369242, by rfl⟩ : syracuseStep 492323 = 738485) B738485
theorem B820003 : Blo 483789 820003 := bstep (se 1 (by rfl) ⟨615002, by rfl⟩ : syracuseStep 820003 = 1230005) B1230005
theorem B1639277 : Blo 483789 1639277 := bstep (se 3 (by rfl) ⟨307364, by rfl⟩ : syracuseStep 1639277 = 614729) B614729
theorem B1639331 : Blo 483789 1639331 := bstep (se 1 (by rfl) ⟨1229498, by rfl⟩ : syracuseStep 1639331 = 2458997) B2458997
theorem B918449 : Blo 483789 918449 := bstep (se 2 (by rfl) ⟨344418, by rfl⟩ : syracuseStep 918449 = 688837) B688837
theorem B820145 : Blo 483789 820145 := bstep (se 2 (by rfl) ⟨307554, by rfl⟩ : syracuseStep 820145 = 615109) B615109
theorem B2458673 : Blo 483789 2458673 := bstep (se 2 (by rfl) ⟨922002, by rfl⟩ : syracuseStep 2458673 = 1844005) B1844005
theorem B820273 : Blo 483789 820273 := bstep (se 2 (by rfl) ⟨307602, by rfl⟩ : syracuseStep 820273 = 615205) B615205
theorem B984145 : Blo 483789 984145 := bstep (se 2 (by rfl) ⟨369054, by rfl⟩ : syracuseStep 984145 = 738109) B738109
theorem B820307 : Blo 483789 820307 := bstep (se 1 (by rfl) ⟨615230, by rfl⟩ : syracuseStep 820307 = 1230461) B1230461
theorem B689315 : Blo 483789 689315 := bstep (se 1 (by rfl) ⟨516986, by rfl⟩ : syracuseStep 689315 = 1033973) B1033973
theorem B1639601 : Blo 483789 1639601 := bstep (se 2 (by rfl) ⟨614850, by rfl⟩ : syracuseStep 1639601 = 1229701) B1229701
theorem B7013573 : Blo 483789 7013573 := bstep (se 4 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 7013573 = 1315045) B1315045
theorem B820435 : Blo 483789 820435 := bstep (se 1 (by rfl) ⟨615326, by rfl⟩ : syracuseStep 820435 = 1230653) B1230653
theorem B492851 : Blo 483789 492851 := bstep (se 1 (by rfl) ⟨369638, by rfl⟩ : syracuseStep 492851 = 739277) B739277
theorem B820577 : Blo 483789 820577 := bstep (se 2 (by rfl) ⟨307716, by rfl⟩ : syracuseStep 820577 = 615433) B615433
theorem B820705 : Blo 483789 820705 := bstep (se 2 (by rfl) ⟨307764, by rfl⟩ : syracuseStep 820705 = 615529) B615529
theorem B820739 : Blo 483789 820739 := bstep (se 1 (by rfl) ⟨615554, by rfl⟩ : syracuseStep 820739 = 1231109) B1231109
theorem B1377901 : Blo 483789 1377901 := bstep (se 3 (by rfl) ⟨258356, by rfl⟩ : syracuseStep 1377901 = 516713) B516713
theorem B820867 : Blo 483789 820867 := bstep (se 1 (by rfl) ⟨615650, by rfl⟩ : syracuseStep 820867 = 1231301) B1231301
theorem B1312451 : Blo 483789 1312451 := bstep (se 1 (by rfl) ⟨984338, by rfl⟩ : syracuseStep 1312451 = 1968677) B1968677
theorem B1640141 : Blo 483789 1640141 := bstep (se 3 (by rfl) ⟨307526, by rfl⟩ : syracuseStep 1640141 = 615053) B615053
theorem B2164429 : Blo 483789 2164429 := bstep (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) B811661
theorem B1640195 : Blo 483789 1640195 := bstep (se 1 (by rfl) ⟨1230146, by rfl⟩ : syracuseStep 1640195 = 2460293) B2460293
theorem B821009 : Blo 483789 821009 := bstep (se 2 (by rfl) ⟨307878, by rfl⟩ : syracuseStep 821009 = 615757) B615757
theorem B689953 : Blo 483789 689953 := bstep (se 2 (by rfl) ⟨258732, by rfl⟩ : syracuseStep 689953 = 517465) B517465
theorem B919345 : Blo 483789 919345 := bstep (se 2 (by rfl) ⟨344754, by rfl⟩ : syracuseStep 919345 = 689509) B689509
theorem B1378129 : Blo 483789 1378129 := bstep (se 2 (by rfl) ⟨516798, by rfl⟩ : syracuseStep 1378129 = 1033597) B1033597
theorem B1312625 : Blo 483789 1312625 := bstep (se 2 (by rfl) ⟨492234, by rfl⟩ : syracuseStep 1312625 = 984469) B984469
theorem B821137 : Blo 483789 821137 := bstep (se 2 (by rfl) ⟨307926, by rfl⟩ : syracuseStep 821137 = 615853) B615853
theorem B690067 : Blo 483789 690067 := bstep (se 1 (by rfl) ⟨517550, by rfl⟩ : syracuseStep 690067 = 1035101) B1035101
theorem B821171 : Blo 483789 821171 := bstep (se 1 (by rfl) ⟨615878, by rfl⟩ : syracuseStep 821171 = 1231757) B1231757
theorem B919505 : Blo 483789 919505 := bstep (se 2 (by rfl) ⟨344814, by rfl⟩ : syracuseStep 919505 = 689629) B689629
theorem B1378289 : Blo 483789 1378289 := bstep (se 2 (by rfl) ⟨516858, by rfl⟩ : syracuseStep 1378289 = 1033717) B1033717
theorem B1640465 : Blo 483789 1640465 := bstep (se 2 (by rfl) ⟨615174, by rfl⟩ : syracuseStep 1640465 = 1230349) B1230349
theorem B821299 : Blo 483789 821299 := bstep (se 1 (by rfl) ⟨615974, by rfl⟩ : syracuseStep 821299 = 1231949) B1231949
theorem B1378403 : Blo 483789 1378403 := bstep (se 1 (by rfl) ⟨1033802, by rfl⟩ : syracuseStep 1378403 = 2067605) B2067605
theorem B821441 : Blo 483789 821441 := bstep (se 2 (by rfl) ⟨308040, by rfl⟩ : syracuseStep 821441 = 616081) B616081
theorem B821569 : Blo 483789 821569 := bstep (se 2 (by rfl) ⟨308088, by rfl⟩ : syracuseStep 821569 = 616177) B616177
theorem B919907 : Blo 483789 919907 := bstep (se 1 (by rfl) ⟨689930, by rfl⟩ : syracuseStep 919907 = 1379861) B1379861
theorem B821603 : Blo 483789 821603 := bstep (se 1 (by rfl) ⟨616202, by rfl⟩ : syracuseStep 821603 = 1232405) B1232405
theorem B1247633 : Blo 483789 1247633 := bstep (se 2 (by rfl) ⟨467862, by rfl⟩ : syracuseStep 1247633 = 935725) B935725
theorem B1837475 : Blo 483789 1837475 := bstep (se 1 (by rfl) ⟨1378106, by rfl⟩ : syracuseStep 1837475 = 2756213) B2756213
theorem B1477091 : Blo 483789 1477091 := bstep (se 1 (by rfl) ⟨1107818, by rfl⟩ : syracuseStep 1477091 = 2215637) B2215637
theorem B2460131 : Blo 483789 2460131 := bstep (se 1 (by rfl) ⟨1845098, by rfl⟩ : syracuseStep 2460131 = 3690197) B3690197
theorem B821731 : Blo 483789 821731 := bstep (se 1 (by rfl) ⟨616298, by rfl⟩ : syracuseStep 821731 = 1232597) B1232597
theorem B1641005 : Blo 483789 1641005 := bstep (se 3 (by rfl) ⟨307688, by rfl⟩ : syracuseStep 1641005 = 615377) B615377
theorem B1641059 : Blo 483789 1641059 := bstep (se 1 (by rfl) ⟨1230794, by rfl⟩ : syracuseStep 1641059 = 2461589) B2461589
theorem B821873 : Blo 483789 821873 := bstep (se 2 (by rfl) ⟨308202, by rfl⟩ : syracuseStep 821873 = 616405) B616405
theorem B822001 : Blo 483789 822001 := bstep (se 2 (by rfl) ⟨308250, by rfl⟩ : syracuseStep 822001 = 616501) B616501
theorem B822035 : Blo 483789 822035 := bstep (se 1 (by rfl) ⟨616526, by rfl⟩ : syracuseStep 822035 = 1233053) B1233053
theorem B789329 : Blo 483789 789329 := bstep (se 2 (by rfl) ⟨295998, by rfl⟩ : syracuseStep 789329 = 591997) B591997
theorem B1641329 : Blo 483789 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B822163 : Blo 483789 822163 := bstep (se 1 (by rfl) ⟨616622, by rfl⟩ : syracuseStep 822163 = 1233245) B1233245
theorem B822305 : Blo 483789 822305 := bstep (se 2 (by rfl) ⟨308364, by rfl⟩ : syracuseStep 822305 = 616729) B616729
theorem B1379405 : Blo 483789 1379405 := bstep (se 3 (by rfl) ⟨258638, by rfl⟩ : syracuseStep 1379405 = 517277) B517277
theorem B822433 : Blo 483789 822433 := bstep (se 2 (by rfl) ⟨308412, by rfl⟩ : syracuseStep 822433 = 616825) B616825
theorem B822467 : Blo 483789 822467 := bstep (se 1 (by rfl) ⟨616850, by rfl⟩ : syracuseStep 822467 = 1233701) B1233701
theorem B2755781 : Blo 483789 2755781 := bstep (se 4 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 2755781 = 516709) B516709
theorem B691411 : Blo 483789 691411 := bstep (se 1 (by rfl) ⟨518558, by rfl⟩ : syracuseStep 691411 = 1037117) B1037117
theorem B920803 : Blo 483789 920803 := bstep (se 1 (by rfl) ⟨690602, by rfl⟩ : syracuseStep 920803 = 1381205) B1381205
theorem B1314029 : Blo 483789 1314029 := bstep (se 3 (by rfl) ⟨246380, by rfl⟩ : syracuseStep 1314029 = 492761) B492761
theorem B1379587 : Blo 483789 1379587 := bstep (se 1 (by rfl) ⟨1034690, by rfl⟩ : syracuseStep 1379587 = 2069381) B2069381
theorem B2460941 : Blo 483789 2460941 := bstep (se 3 (by rfl) ⟨461426, by rfl⟩ : syracuseStep 2460941 = 922853) B922853
theorem B822595 : Blo 483789 822595 := bstep (se 1 (by rfl) ⟨616946, by rfl⟩ : syracuseStep 822595 = 1233893) B1233893
theorem B920963 : Blo 483789 920963 := bstep (se 1 (by rfl) ⟨690722, by rfl⟩ : syracuseStep 920963 = 1381445) B1381445
theorem B1838477 : Blo 483789 1838477 := bstep (se 3 (by rfl) ⟨344714, by rfl⟩ : syracuseStep 1838477 = 689429) B689429
theorem B1641869 : Blo 483789 1641869 := bstep (se 3 (by rfl) ⟨307850, by rfl⟩ : syracuseStep 1641869 = 615701) B615701
theorem B1379747 : Blo 483789 1379747 := bstep (se 1 (by rfl) ⟨1034810, by rfl⟩ : syracuseStep 1379747 = 2069621) B2069621
theorem B2952625 : Blo 483789 2952625 := bstep (se 2 (by rfl) ⟨1107234, by rfl⟩ : syracuseStep 2952625 = 2214469) B2214469
theorem B1641923 : Blo 483789 1641923 := bstep (se 1 (by rfl) ⟨1231442, by rfl⟩ : syracuseStep 1641923 = 2462885) B2462885
theorem B822737 : Blo 483789 822737 := bstep (se 2 (by rfl) ⟨308526, by rfl⟩ : syracuseStep 822737 = 617053) B617053
theorem B1314353 : Blo 483789 1314353 := bstep (se 2 (by rfl) ⟨492882, by rfl⟩ : syracuseStep 1314353 = 985765) B985765
theorem B822865 : Blo 483789 822865 := bstep (se 2 (by rfl) ⟨308574, by rfl⟩ : syracuseStep 822865 = 617149) B617149
theorem B3116657 : Blo 483789 3116657 := bstep (se 2 (by rfl) ⟨1168746, by rfl⟩ : syracuseStep 3116657 = 2337493) B2337493
theorem B822899 : Blo 483789 822899 := bstep (se 1 (by rfl) ⟨617174, by rfl⟩ : syracuseStep 822899 = 1234349) B1234349
theorem B1642193 : Blo 483789 1642193 := bstep (se 2 (by rfl) ⟨615822, by rfl⟩ : syracuseStep 1642193 = 1231645) B1231645
theorem B823027 : Blo 483789 823027 := bstep (se 1 (by rfl) ⟨617270, by rfl⟩ : syracuseStep 823027 = 1234541) B1234541
theorem B5345165 : Blo 483789 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B1642733 : Blo 483789 1642733 := bstep (se 3 (by rfl) ⟨308012, by rfl⟩ : syracuseStep 1642733 = 616025) B616025
theorem B1478915 : Blo 483789 1478915 := bstep (se 1 (by rfl) ⟨1109186, by rfl⟩ : syracuseStep 1478915 = 2218373) B2218373
theorem B1642787 : Blo 483789 1642787 := bstep (se 1 (by rfl) ⟨1232090, by rfl⟩ : syracuseStep 1642787 = 2464181) B2464181
theorem B692545 : Blo 483789 692545 := bstep (se 2 (by rfl) ⟨259704, by rfl⟩ : syracuseStep 692545 = 519409) B519409
theorem B692641 : Blo 483789 692641 := bstep (se 2 (by rfl) ⟨259740, by rfl⟩ : syracuseStep 692641 = 519481) B519481
theorem B922033 : Blo 483789 922033 := bstep (se 2 (by rfl) ⟨345762, by rfl⟩ : syracuseStep 922033 = 691525) B691525
theorem B1380817 : Blo 483789 1380817 := bstep (se 2 (by rfl) ⟨517806, by rfl⟩ : syracuseStep 1380817 = 1035613) B1035613
theorem B1643057 : Blo 483789 1643057 := bstep (se 2 (by rfl) ⟨616146, by rfl⟩ : syracuseStep 1643057 = 1232293) B1232293
theorem B4657763 : Blo 483789 4657763 := bstep (se 1 (by rfl) ⟨3493322, by rfl⟩ : syracuseStep 4657763 = 6986645) B6986645
theorem B725699 : Blo 483789 725699 := bstep (se 1 (by rfl) ⟨544274, by rfl⟩ : syracuseStep 725699 = 1088549) B1088549
theorem B725729 : Blo 483789 725729 := bstep (se 2 (by rfl) ⟨272148, by rfl⟩ : syracuseStep 725729 = 544297) B544297
theorem B6099697 : Blo 483789 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B725747 : Blo 483789 725747 := bstep (se 1 (by rfl) ⟨544310, by rfl⟩ : syracuseStep 725747 = 1088621) B1088621
theorem B725777 : Blo 483789 725777 := bstep (se 2 (by rfl) ⟨272166, by rfl⟩ : syracuseStep 725777 = 544333) B544333
theorem B725795 : Blo 483789 725795 := bstep (se 1 (by rfl) ⟨544346, by rfl⟩ : syracuseStep 725795 = 1088693) B1088693
theorem B2102051 : Blo 483789 2102051 := bstep (se 1 (by rfl) ⟨1576538, by rfl⟩ : syracuseStep 2102051 = 3153077) B3153077
theorem B2069297 : Blo 483789 2069297 := bstep (se 2 (by rfl) ⟨775986, by rfl⟩ : syracuseStep 2069297 = 1551973) B1551973
theorem B725825 : Blo 483789 725825 := bstep (se 2 (by rfl) ⟨272184, by rfl⟩ : syracuseStep 725825 = 544369) B544369
theorem B725843 : Blo 483789 725843 := bstep (se 1 (by rfl) ⟨544382, by rfl⟩ : syracuseStep 725843 = 1088765) B1088765
theorem B2069347 : Blo 483789 2069347 := bstep (se 1 (by rfl) ⟨1552010, by rfl⟩ : syracuseStep 2069347 = 3104021) B3104021
theorem B725873 : Blo 483789 725873 := bstep (se 2 (by rfl) ⟨272202, by rfl⟩ : syracuseStep 725873 = 544405) B544405
theorem B725891 : Blo 483789 725891 := bstep (se 1 (by rfl) ⟨544418, by rfl⟩ : syracuseStep 725891 = 1088837) B1088837
theorem B693137 : Blo 483789 693137 := bstep (se 2 (by rfl) ⟨259926, by rfl⟩ : syracuseStep 693137 = 519853) B519853
theorem B725921 : Blo 483789 725921 := bstep (se 2 (by rfl) ⟨272220, by rfl⟩ : syracuseStep 725921 = 544441) B544441
theorem B725939 : Blo 483789 725939 := bstep (se 1 (by rfl) ⟨544454, by rfl⟩ : syracuseStep 725939 = 1088909) B1088909
theorem B725969 : Blo 483789 725969 := bstep (se 2 (by rfl) ⟨272238, by rfl⟩ : syracuseStep 725969 = 544477) B544477
theorem B725987 : Blo 483789 725987 := bstep (se 1 (by rfl) ⟨544490, by rfl⟩ : syracuseStep 725987 = 1088981) B1088981
theorem B726017 : Blo 483789 726017 := bstep (se 2 (by rfl) ⟨272256, by rfl⟩ : syracuseStep 726017 = 544513) B544513
theorem B726035 : Blo 483789 726035 := bstep (se 1 (by rfl) ⟨544526, by rfl⟩ : syracuseStep 726035 = 1089053) B1089053
theorem B3118115 : Blo 483789 3118115 := bstep (se 1 (by rfl) ⟨2338586, by rfl⟩ : syracuseStep 3118115 = 4677173) B4677173
theorem B726065 : Blo 483789 726065 := bstep (se 2 (by rfl) ⟨272274, by rfl⟩ : syracuseStep 726065 = 544549) B544549
theorem B1315889 : Blo 483789 1315889 := bstep (se 2 (by rfl) ⟨493458, by rfl⟩ : syracuseStep 1315889 = 986917) B986917
theorem B726083 : Blo 483789 726083 := bstep (se 1 (by rfl) ⟨544562, by rfl⟩ : syracuseStep 726083 = 1089125) B1089125
theorem B1643597 : Blo 483789 1643597 := bstep (se 3 (by rfl) ⟨308174, by rfl⟩ : syracuseStep 1643597 = 616349) B616349
theorem B726113 : Blo 483789 726113 := bstep (se 2 (by rfl) ⟨272292, by rfl⟩ : syracuseStep 726113 = 544585) B544585
theorem B726131 : Blo 483789 726131 := bstep (se 1 (by rfl) ⟨544598, by rfl⟩ : syracuseStep 726131 = 1089197) B1089197
theorem B1643651 : Blo 483789 1643651 := bstep (se 1 (by rfl) ⟨1232738, by rfl⟩ : syracuseStep 1643651 = 2465477) B2465477
theorem B726161 : Blo 483789 726161 := bstep (se 2 (by rfl) ⟨272310, by rfl⟩ : syracuseStep 726161 = 544621) B544621
theorem B726179 : Blo 483789 726179 := bstep (se 1 (by rfl) ⟨544634, by rfl⟩ : syracuseStep 726179 = 1089269) B1089269
theorem B988337 : Blo 483789 988337 := bstep (se 2 (by rfl) ⟨370626, by rfl⟩ : syracuseStep 988337 = 741253) B741253
theorem B726209 : Blo 483789 726209 := bstep (se 2 (by rfl) ⟨272328, by rfl⟩ : syracuseStep 726209 = 544657) B544657
theorem B726227 : Blo 483789 726227 := bstep (se 1 (by rfl) ⟨544670, by rfl⟩ : syracuseStep 726227 = 1089341) B1089341
theorem B726257 : Blo 483789 726257 := bstep (se 2 (by rfl) ⟨272346, by rfl⟩ : syracuseStep 726257 = 544693) B544693
theorem B726275 : Blo 483789 726275 := bstep (se 1 (by rfl) ⟨544706, by rfl⟩ : syracuseStep 726275 = 1089413) B1089413
theorem B2954501 : Blo 483789 2954501 := bstep (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) B553969
theorem B726305 : Blo 483789 726305 := bstep (se 2 (by rfl) ⟨272364, by rfl⟩ : syracuseStep 726305 = 544729) B544729
theorem B726323 : Blo 483789 726323 := bstep (se 1 (by rfl) ⟨544742, by rfl⟩ : syracuseStep 726323 = 1089485) B1089485
theorem B726353 : Blo 483789 726353 := bstep (se 2 (by rfl) ⟨272382, by rfl⟩ : syracuseStep 726353 = 544765) B544765
theorem B726371 : Blo 483789 726371 := bstep (se 1 (by rfl) ⟨544778, by rfl⟩ : syracuseStep 726371 = 1089557) B1089557
theorem B726401 : Blo 483789 726401 := bstep (se 2 (by rfl) ⟨272400, by rfl⟩ : syracuseStep 726401 = 544801) B544801
theorem B1643921 : Blo 483789 1643921 := bstep (se 2 (by rfl) ⟨616470, by rfl⟩ : syracuseStep 1643921 = 1232941) B1232941
theorem B726419 : Blo 483789 726419 := bstep (se 1 (by rfl) ⟨544814, by rfl⟩ : syracuseStep 726419 = 1089629) B1089629
theorem B726449 : Blo 483789 726449 := bstep (se 2 (by rfl) ⟨272418, by rfl⟩ : syracuseStep 726449 = 544837) B544837
theorem B726467 : Blo 483789 726467 := bstep (se 1 (by rfl) ⟨544850, by rfl⟩ : syracuseStep 726467 = 1089701) B1089701
theorem B1840589 : Blo 483789 1840589 := bstep (se 3 (by rfl) ⟨345110, by rfl⟩ : syracuseStep 1840589 = 690221) B690221
theorem B923089 : Blo 483789 923089 := bstep (se 2 (by rfl) ⟨346158, by rfl⟩ : syracuseStep 923089 = 692317) B692317
theorem B726497 : Blo 483789 726497 := bstep (se 2 (by rfl) ⟨272436, by rfl⟩ : syracuseStep 726497 = 544873) B544873
theorem B726515 : Blo 483789 726515 := bstep (se 1 (by rfl) ⟨544886, by rfl⟩ : syracuseStep 726515 = 1089773) B1089773
theorem B726545 : Blo 483789 726545 := bstep (se 2 (by rfl) ⟨272454, by rfl⟩ : syracuseStep 726545 = 544909) B544909
theorem B726563 : Blo 483789 726563 := bstep (se 1 (by rfl) ⟨544922, by rfl⟩ : syracuseStep 726563 = 1089845) B1089845
theorem B726593 : Blo 483789 726593 := bstep (se 2 (by rfl) ⟨272472, by rfl⟩ : syracuseStep 726593 = 544945) B544945
theorem B726611 : Blo 483789 726611 := bstep (se 1 (by rfl) ⟨544958, by rfl⟩ : syracuseStep 726611 = 1089917) B1089917
theorem B726641 : Blo 483789 726641 := bstep (se 2 (by rfl) ⟨272490, by rfl⟩ : syracuseStep 726641 = 544981) B544981
theorem B726659 : Blo 483789 726659 := bstep (se 1 (by rfl) ⟨544994, by rfl⟩ : syracuseStep 726659 = 1089989) B1089989
theorem B3937933 : Blo 483789 3937933 := bstep (se 3 (by rfl) ⟨738362, by rfl⟩ : syracuseStep 3937933 = 1476725) B1476725
theorem B726689 : Blo 483789 726689 := bstep (se 2 (by rfl) ⟨272508, by rfl⟩ : syracuseStep 726689 = 545017) B545017
theorem B726707 : Blo 483789 726707 := bstep (se 1 (by rfl) ⟨545030, by rfl⟩ : syracuseStep 726707 = 1090061) B1090061
theorem B1382093 : Blo 483789 1382093 := bstep (se 3 (by rfl) ⟨259142, by rfl⟩ : syracuseStep 1382093 = 518285) B518285
theorem B726737 : Blo 483789 726737 := bstep (se 2 (by rfl) ⟨272526, by rfl⟩ : syracuseStep 726737 = 545053) B545053
theorem B726755 : Blo 483789 726755 := bstep (se 1 (by rfl) ⟨545066, by rfl⟩ : syracuseStep 726755 = 1090133) B1090133
theorem B694003 : Blo 483789 694003 := bstep (se 1 (by rfl) ⟨520502, by rfl⟩ : syracuseStep 694003 = 1041005) B1041005
theorem B726785 : Blo 483789 726785 := bstep (se 2 (by rfl) ⟨272544, by rfl⟩ : syracuseStep 726785 = 545089) B545089
theorem B726803 : Blo 483789 726803 := bstep (se 1 (by rfl) ⟨545102, by rfl⟩ : syracuseStep 726803 = 1090205) B1090205
theorem B726833 : Blo 483789 726833 := bstep (se 2 (by rfl) ⟨272562, by rfl⟩ : syracuseStep 726833 = 545125) B545125
theorem B726851 : Blo 483789 726851 := bstep (se 1 (by rfl) ⟨545138, by rfl⟩ : syracuseStep 726851 = 1090277) B1090277
theorem B694099 : Blo 483789 694099 := bstep (se 1 (by rfl) ⟨520574, by rfl⟩ : syracuseStep 694099 = 1041149) B1041149
theorem B726881 : Blo 483789 726881 := bstep (se 2 (by rfl) ⟨272580, by rfl⟩ : syracuseStep 726881 = 545161) B545161
theorem B923491 : Blo 483789 923491 := bstep (se 1 (by rfl) ⟨692618, by rfl⟩ : syracuseStep 923491 = 1385237) B1385237
theorem B726899 : Blo 483789 726899 := bstep (se 1 (by rfl) ⟨545174, by rfl⟩ : syracuseStep 726899 = 1090349) B1090349
theorem B1382275 : Blo 483789 1382275 := bstep (se 1 (by rfl) ⟨1036706, by rfl⟩ : syracuseStep 1382275 = 2073413) B2073413
theorem B4134797 : Blo 483789 4134797 := bstep (se 3 (by rfl) ⟨775274, by rfl⟩ : syracuseStep 4134797 = 1550549) B1550549
theorem B726929 : Blo 483789 726929 := bstep (se 2 (by rfl) ⟨272598, by rfl⟩ : syracuseStep 726929 = 545197) B545197
theorem B923537 : Blo 483789 923537 := bstep (se 2 (by rfl) ⟨346326, by rfl⟩ : syracuseStep 923537 = 692653) B692653
theorem B726947 : Blo 483789 726947 := bstep (se 1 (by rfl) ⟨545210, by rfl⟩ : syracuseStep 726947 = 1090421) B1090421
theorem B1644461 : Blo 483789 1644461 := bstep (se 3 (by rfl) ⟨308336, by rfl⟩ : syracuseStep 1644461 = 616673) B616673
theorem B1382321 : Blo 483789 1382321 := bstep (se 2 (by rfl) ⟨518370, by rfl⟩ : syracuseStep 1382321 = 1036741) B1036741
theorem B1775537 : Blo 483789 1775537 := bstep (se 2 (by rfl) ⟨665826, by rfl⟩ : syracuseStep 1775537 = 1331653) B1331653
theorem B726977 : Blo 483789 726977 := bstep (se 2 (by rfl) ⟨272616, by rfl⟩ : syracuseStep 726977 = 545233) B545233
theorem B726995 : Blo 483789 726995 := bstep (se 1 (by rfl) ⟨545246, by rfl⟩ : syracuseStep 726995 = 1090493) B1090493
theorem B1644515 : Blo 483789 1644515 := bstep (se 1 (by rfl) ⟨1233386, by rfl⟩ : syracuseStep 1644515 = 2466773) B2466773
theorem B727025 : Blo 483789 727025 := bstep (se 2 (by rfl) ⟨272634, by rfl⟩ : syracuseStep 727025 = 545269) B545269
theorem B727043 : Blo 483789 727043 := bstep (se 1 (by rfl) ⟨545282, by rfl⟩ : syracuseStep 727043 = 1090565) B1090565
theorem B727073 : Blo 483789 727073 := bstep (se 2 (by rfl) ⟨272652, by rfl⟩ : syracuseStep 727073 = 545305) B545305
theorem B727091 : Blo 483789 727091 := bstep (se 1 (by rfl) ⟨545318, by rfl⟩ : syracuseStep 727091 = 1090637) B1090637
theorem B727121 : Blo 483789 727121 := bstep (se 2 (by rfl) ⟨272670, by rfl⟩ : syracuseStep 727121 = 545341) B545341
theorem B727139 : Blo 483789 727139 := bstep (se 1 (by rfl) ⟨545354, by rfl⟩ : syracuseStep 727139 = 1090709) B1090709
theorem B2463857 : Blo 483789 2463857 := bstep (se 2 (by rfl) ⟨923946, by rfl⟩ : syracuseStep 2463857 = 1847893) B1847893
theorem B727169 : Blo 483789 727169 := bstep (se 2 (by rfl) ⟨272688, by rfl⟩ : syracuseStep 727169 = 545377) B545377
theorem B727187 : Blo 483789 727187 := bstep (se 1 (by rfl) ⟨545390, by rfl⟩ : syracuseStep 727187 = 1090781) B1090781
theorem B727217 : Blo 483789 727217 := bstep (se 2 (by rfl) ⟨272706, by rfl⟩ : syracuseStep 727217 = 545413) B545413
theorem B923825 : Blo 483789 923825 := bstep (se 2 (by rfl) ⟨346434, by rfl⟩ : syracuseStep 923825 = 692869) B692869
theorem B727235 : Blo 483789 727235 := bstep (se 1 (by rfl) ⟨545426, by rfl⟩ : syracuseStep 727235 = 1090853) B1090853
theorem B727265 : Blo 483789 727265 := bstep (se 2 (by rfl) ⟨272724, by rfl⟩ : syracuseStep 727265 = 545449) B545449
theorem B1841393 : Blo 483789 1841393 := bstep (se 2 (by rfl) ⟨690522, by rfl⟩ : syracuseStep 1841393 = 1381045) B1381045
theorem B1644785 : Blo 483789 1644785 := bstep (se 2 (by rfl) ⟨616794, by rfl⟩ : syracuseStep 1644785 = 1233589) B1233589
theorem B727283 : Blo 483789 727283 := bstep (se 1 (by rfl) ⟨545462, by rfl⟩ : syracuseStep 727283 = 1090925) B1090925
theorem B727313 : Blo 483789 727313 := bstep (se 2 (by rfl) ⟨272742, by rfl⟩ : syracuseStep 727313 = 545485) B545485
theorem B727331 : Blo 483789 727331 := bstep (se 1 (by rfl) ⟨545498, by rfl⟩ : syracuseStep 727331 = 1090997) B1090997
theorem B727361 : Blo 483789 727361 := bstep (se 2 (by rfl) ⟨272760, by rfl⟩ : syracuseStep 727361 = 545521) B545521
theorem B727379 : Blo 483789 727379 := bstep (se 1 (by rfl) ⟨545534, by rfl⟩ : syracuseStep 727379 = 1091069) B1091069
theorem B727409 : Blo 483789 727409 := bstep (se 2 (by rfl) ⟨272778, by rfl⟩ : syracuseStep 727409 = 545557) B545557
theorem B727427 : Blo 483789 727427 := bstep (se 1 (by rfl) ⟨545570, by rfl⟩ : syracuseStep 727427 = 1091141) B1091141
theorem B727457 : Blo 483789 727457 := bstep (se 2 (by rfl) ⟨272796, by rfl⟩ : syracuseStep 727457 = 545593) B545593
theorem B727475 : Blo 483789 727475 := bstep (se 1 (by rfl) ⟨545606, by rfl⟩ : syracuseStep 727475 = 1091213) B1091213
theorem B727505 : Blo 483789 727505 := bstep (se 2 (by rfl) ⟨272814, by rfl⟩ : syracuseStep 727505 = 545629) B545629
theorem B727523 : Blo 483789 727523 := bstep (se 1 (by rfl) ⟨545642, by rfl⟩ : syracuseStep 727523 = 1091285) B1091285
theorem B727553 : Blo 483789 727553 := bstep (se 2 (by rfl) ⟨272832, by rfl⟩ : syracuseStep 727553 = 545665) B545665
theorem B727571 : Blo 483789 727571 := bstep (se 1 (by rfl) ⟨545678, by rfl⟩ : syracuseStep 727571 = 1091357) B1091357
theorem B727601 : Blo 483789 727601 := bstep (se 2 (by rfl) ⟨272850, by rfl⟩ : syracuseStep 727601 = 545701) B545701
theorem B727619 : Blo 483789 727619 := bstep (se 1 (by rfl) ⟨545714, by rfl⟩ : syracuseStep 727619 = 1091429) B1091429
theorem B727649 : Blo 483789 727649 := bstep (se 2 (by rfl) ⟨272868, by rfl⟩ : syracuseStep 727649 = 545737) B545737
theorem B727667 : Blo 483789 727667 := bstep (se 1 (by rfl) ⟨545750, by rfl⟩ : syracuseStep 727667 = 1091501) B1091501
theorem B727697 : Blo 483789 727697 := bstep (se 2 (by rfl) ⟨272886, by rfl⟩ : syracuseStep 727697 = 545773) B545773
theorem B727715 : Blo 483789 727715 := bstep (se 1 (by rfl) ⟨545786, by rfl⟩ : syracuseStep 727715 = 1091573) B1091573
theorem B727745 : Blo 483789 727745 := bstep (se 2 (by rfl) ⟨272904, by rfl⟩ : syracuseStep 727745 = 545809) B545809
theorem B727763 : Blo 483789 727763 := bstep (se 1 (by rfl) ⟨545822, by rfl⟩ : syracuseStep 727763 = 1091645) B1091645
theorem B727793 : Blo 483789 727793 := bstep (se 2 (by rfl) ⟨272922, by rfl⟩ : syracuseStep 727793 = 545845) B545845
theorem B727811 : Blo 483789 727811 := bstep (se 1 (by rfl) ⟨545858, by rfl⟩ : syracuseStep 727811 = 1091717) B1091717
theorem B1645325 : Blo 483789 1645325 := bstep (se 3 (by rfl) ⟨308498, by rfl⟩ : syracuseStep 1645325 = 616997) B616997
theorem B727841 : Blo 483789 727841 := bstep (se 2 (by rfl) ⟨272940, by rfl⟩ : syracuseStep 727841 = 545881) B545881
theorem B727859 : Blo 483789 727859 := bstep (se 1 (by rfl) ⟨545894, by rfl⟩ : syracuseStep 727859 = 1091789) B1091789
theorem B5315381 : Blo 483789 5315381 := bstep (se 5 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 5315381 = 498317) B498317
theorem B1645379 : Blo 483789 1645379 := bstep (se 1 (by rfl) ⟨1234034, by rfl⟩ : syracuseStep 1645379 = 2468069) B2468069
theorem B5544773 : Blo 483789 5544773 := bstep (se 4 (by rfl) ⟨519822, by rfl⟩ : syracuseStep 5544773 = 1039645) B1039645
theorem B727889 : Blo 483789 727889 := bstep (se 2 (by rfl) ⟨272958, by rfl⟩ : syracuseStep 727889 = 545917) B545917
theorem B727907 : Blo 483789 727907 := bstep (se 1 (by rfl) ⟨545930, by rfl⟩ : syracuseStep 727907 = 1091861) B1091861
theorem B727937 : Blo 483789 727937 := bstep (se 2 (by rfl) ⟨272976, by rfl⟩ : syracuseStep 727937 = 545953) B545953
theorem B924547 : Blo 483789 924547 := bstep (se 1 (by rfl) ⟨693410, by rfl⟩ : syracuseStep 924547 = 1386821) B1386821
theorem B1842061 : Blo 483789 1842061 := bstep (se 3 (by rfl) ⟨345386, by rfl⟩ : syracuseStep 1842061 = 690773) B690773
theorem B727955 : Blo 483789 727955 := bstep (se 1 (by rfl) ⟨545966, by rfl⟩ : syracuseStep 727955 = 1091933) B1091933
theorem B727985 : Blo 483789 727985 := bstep (se 2 (by rfl) ⟨272994, by rfl⟩ : syracuseStep 727985 = 545989) B545989
theorem B728003 : Blo 483789 728003 := bstep (se 1 (by rfl) ⟨546002, by rfl⟩ : syracuseStep 728003 = 1092005) B1092005
theorem B2759629 : Blo 483789 2759629 := bstep (se 3 (by rfl) ⟨517430, by rfl⟩ : syracuseStep 2759629 = 1034861) B1034861
theorem B728033 : Blo 483789 728033 := bstep (se 2 (by rfl) ⟨273012, by rfl⟩ : syracuseStep 728033 = 546025) B546025
theorem B728051 : Blo 483789 728051 := bstep (se 1 (by rfl) ⟨546038, by rfl⟩ : syracuseStep 728051 = 1092077) B1092077
theorem B728081 : Blo 483789 728081 := bstep (se 2 (by rfl) ⟨273030, by rfl⟩ : syracuseStep 728081 = 546061) B546061
theorem B728099 : Blo 483789 728099 := bstep (se 1 (by rfl) ⟨546074, by rfl⟩ : syracuseStep 728099 = 1092149) B1092149
theorem B728129 : Blo 483789 728129 := bstep (se 2 (by rfl) ⟨273048, by rfl⟩ : syracuseStep 728129 = 546097) B546097
theorem B1645649 : Blo 483789 1645649 := bstep (se 2 (by rfl) ⟨617118, by rfl⟩ : syracuseStep 1645649 = 1234237) B1234237
theorem B728147 : Blo 483789 728147 := bstep (se 1 (by rfl) ⟨546110, by rfl⟩ : syracuseStep 728147 = 1092221) B1092221
theorem B728177 : Blo 483789 728177 := bstep (se 2 (by rfl) ⟨273066, by rfl⟩ : syracuseStep 728177 = 546133) B546133
theorem B728195 : Blo 483789 728195 := bstep (se 1 (by rfl) ⟨546146, by rfl⟩ : syracuseStep 728195 = 1092293) B1092293
theorem B1088657 : Blo 483789 1088657 := bstep (se 2 (by rfl) ⟨408246, by rfl⟩ : syracuseStep 1088657 = 816493) B816493
theorem B728225 : Blo 483789 728225 := bstep (se 2 (by rfl) ⟨273084, by rfl⟩ : syracuseStep 728225 = 546169) B546169
theorem B1088675 : Blo 483789 1088675 := bstep (se 1 (by rfl) ⟨816506, by rfl⟩ : syracuseStep 1088675 = 1633013) B1633013
theorem B728243 : Blo 483789 728243 := bstep (se 1 (by rfl) ⟨546182, by rfl⟩ : syracuseStep 728243 = 1092365) B1092365
theorem B2071757 : Blo 483789 2071757 := bstep (se 3 (by rfl) ⟨388454, by rfl⟩ : syracuseStep 2071757 = 776909) B776909
theorem B728273 : Blo 483789 728273 := bstep (se 2 (by rfl) ⟨273102, by rfl⟩ : syracuseStep 728273 = 546205) B546205
theorem B728291 : Blo 483789 728291 := bstep (se 1 (by rfl) ⟨546218, by rfl⟩ : syracuseStep 728291 = 1092437) B1092437
theorem B728321 : Blo 483789 728321 := bstep (se 2 (by rfl) ⟨273120, by rfl⟩ : syracuseStep 728321 = 546241) B546241
theorem B728339 : Blo 483789 728339 := bstep (se 1 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 728339 = 1092509) B1092509
theorem B728369 : Blo 483789 728369 := bstep (se 2 (by rfl) ⟨273138, by rfl⟩ : syracuseStep 728369 = 546277) B546277
theorem B728387 : Blo 483789 728387 := bstep (se 1 (by rfl) ⟨546290, by rfl⟩ : syracuseStep 728387 = 1092581) B1092581
theorem B924995 : Blo 483789 924995 := bstep (se 1 (by rfl) ⟨693746, by rfl⟩ : syracuseStep 924995 = 1387493) B1387493
theorem B728417 : Blo 483789 728417 := bstep (se 2 (by rfl) ⟨273156, by rfl⟩ : syracuseStep 728417 = 546313) B546313
theorem B1383779 : Blo 483789 1383779 := bstep (se 1 (by rfl) ⟨1037834, by rfl⟩ : syracuseStep 1383779 = 2075669) B2075669
theorem B728435 : Blo 483789 728435 := bstep (se 1 (by rfl) ⟨546326, by rfl⟩ : syracuseStep 728435 = 1092653) B1092653
theorem B728465 : Blo 483789 728465 := bstep (se 2 (by rfl) ⟨273174, by rfl⟩ : syracuseStep 728465 = 546349) B546349
theorem B728483 : Blo 483789 728483 := bstep (se 1 (by rfl) ⟨546362, by rfl⟩ : syracuseStep 728483 = 1092725) B1092725
theorem B1088945 : Blo 483789 1088945 := bstep (se 2 (by rfl) ⟨408354, by rfl⟩ : syracuseStep 1088945 = 816709) B816709
theorem B728513 : Blo 483789 728513 := bstep (se 2 (by rfl) ⟨273192, by rfl⟩ : syracuseStep 728513 = 546385) B546385
theorem B1088963 : Blo 483789 1088963 := bstep (se 1 (by rfl) ⟨816722, by rfl⟩ : syracuseStep 1088963 = 1633445) B1633445
theorem B728531 : Blo 483789 728531 := bstep (se 1 (by rfl) ⟨546398, by rfl⟩ : syracuseStep 728531 = 1092797) B1092797
theorem B1744355 : Blo 483789 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B728561 : Blo 483789 728561 := bstep (se 2 (by rfl) ⟨273210, by rfl⟩ : syracuseStep 728561 = 546421) B546421
theorem B728579 : Blo 483789 728579 := bstep (se 1 (by rfl) ⟨546434, by rfl⟩ : syracuseStep 728579 = 1092869) B1092869
theorem B728609 : Blo 483789 728609 := bstep (se 2 (by rfl) ⟨273228, by rfl⟩ : syracuseStep 728609 = 546457) B546457
theorem B2465315 : Blo 483789 2465315 := bstep (se 1 (by rfl) ⟨1848986, by rfl⟩ : syracuseStep 2465315 = 3697973) B3697973
theorem B728627 : Blo 483789 728627 := bstep (se 1 (by rfl) ⟨546470, by rfl⟩ : syracuseStep 728627 = 1092941) B1092941
theorem B728657 : Blo 483789 728657 := bstep (se 2 (by rfl) ⟨273246, by rfl⟩ : syracuseStep 728657 = 546493) B546493
theorem B728675 : Blo 483789 728675 := bstep (se 1 (by rfl) ⟨546506, by rfl⟩ : syracuseStep 728675 = 1093013) B1093013
theorem B925283 : Blo 483789 925283 := bstep (se 1 (by rfl) ⟨693962, by rfl⟩ : syracuseStep 925283 = 1387925) B1387925
theorem B1646189 : Blo 483789 1646189 := bstep (se 3 (by rfl) ⟨308660, by rfl⟩ : syracuseStep 1646189 = 617321) B617321
theorem B728705 : Blo 483789 728705 := bstep (se 2 (by rfl) ⟨273264, by rfl⟩ : syracuseStep 728705 = 546529) B546529
theorem B1482371 : Blo 483789 1482371 := bstep (se 1 (by rfl) ⟨1111778, by rfl⟩ : syracuseStep 1482371 = 2223557) B2223557
theorem B3120781 : Blo 483789 3120781 := bstep (se 3 (by rfl) ⟨585146, by rfl⟩ : syracuseStep 3120781 = 1170293) B1170293
theorem B728723 : Blo 483789 728723 := bstep (se 1 (by rfl) ⟨546542, by rfl⟩ : syracuseStep 728723 = 1093085) B1093085
theorem B1842851 : Blo 483789 1842851 := bstep (se 1 (by rfl) ⟨1382138, by rfl⟩ : syracuseStep 1842851 = 2764277) B2764277
theorem B1646243 : Blo 483789 1646243 := bstep (se 1 (by rfl) ⟨1234682, by rfl⟩ : syracuseStep 1646243 = 2469365) B2469365
theorem B728753 : Blo 483789 728753 := bstep (se 2 (by rfl) ⟨273282, by rfl⟩ : syracuseStep 728753 = 546565) B546565
theorem B728771 : Blo 483789 728771 := bstep (se 1 (by rfl) ⟨546578, by rfl⟩ : syracuseStep 728771 = 1093157) B1093157
theorem B1089233 : Blo 483789 1089233 := bstep (se 2 (by rfl) ⟨408462, by rfl⟩ : syracuseStep 1089233 = 816925) B816925
theorem B728801 : Blo 483789 728801 := bstep (se 2 (by rfl) ⟨273300, by rfl⟩ : syracuseStep 728801 = 546601) B546601
theorem B1089251 : Blo 483789 1089251 := bstep (se 1 (by rfl) ⟨816938, by rfl⟩ : syracuseStep 1089251 = 1633877) B1633877
theorem B728819 : Blo 483789 728819 := bstep (se 1 (by rfl) ⟨546614, by rfl⟩ : syracuseStep 728819 = 1093229) B1093229
theorem B728849 : Blo 483789 728849 := bstep (se 2 (by rfl) ⟨273318, by rfl⟩ : syracuseStep 728849 = 546637) B546637
theorem B728867 : Blo 483789 728867 := bstep (se 1 (by rfl) ⟨546650, by rfl⟩ : syracuseStep 728867 = 1093301) B1093301
theorem B728897 : Blo 483789 728897 := bstep (se 2 (by rfl) ⟨273336, by rfl⟩ : syracuseStep 728897 = 546673) B546673
theorem B728915 : Blo 483789 728915 := bstep (se 1 (by rfl) ⟨546686, by rfl⟩ : syracuseStep 728915 = 1093373) B1093373
theorem B728945 : Blo 483789 728945 := bstep (se 2 (by rfl) ⟨273354, by rfl⟩ : syracuseStep 728945 = 546709) B546709
theorem B3514225 : Blo 483789 3514225 := bstep (se 2 (by rfl) ⟨1317834, by rfl⟩ : syracuseStep 3514225 = 2635669) B2635669
theorem B728963 : Blo 483789 728963 := bstep (se 1 (by rfl) ⟨546722, by rfl⟩ : syracuseStep 728963 = 1093445) B1093445
theorem B728993 : Blo 483789 728993 := bstep (se 2 (by rfl) ⟨273372, by rfl⟩ : syracuseStep 728993 = 546745) B546745
theorem B729011 : Blo 483789 729011 := bstep (se 1 (by rfl) ⟨546758, by rfl⟩ : syracuseStep 729011 = 1093517) B1093517
theorem B1974221 : Blo 483789 1974221 := bstep (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) B740333
theorem B729041 : Blo 483789 729041 := bstep (se 2 (by rfl) ⟨273390, by rfl⟩ : syracuseStep 729041 = 546781) B546781
theorem B729059 : Blo 483789 729059 := bstep (se 1 (by rfl) ⟨546794, by rfl⟩ : syracuseStep 729059 = 1093589) B1093589
theorem B1089521 : Blo 483789 1089521 := bstep (se 2 (by rfl) ⟨408570, by rfl⟩ : syracuseStep 1089521 = 817141) B817141
theorem B729089 : Blo 483789 729089 := bstep (se 2 (by rfl) ⟨273408, by rfl⟩ : syracuseStep 729089 = 546817) B546817
theorem B1089539 : Blo 483789 1089539 := bstep (se 1 (by rfl) ⟨817154, by rfl⟩ : syracuseStep 1089539 = 1634309) B1634309
theorem B729107 : Blo 483789 729107 := bstep (se 1 (by rfl) ⟨546830, by rfl⟩ : syracuseStep 729107 = 1093661) B1093661
theorem B729137 : Blo 483789 729137 := bstep (se 2 (by rfl) ⟨273426, by rfl⟩ : syracuseStep 729137 = 546853) B546853
theorem B729155 : Blo 483789 729155 := bstep (se 1 (by rfl) ⟨546866, by rfl⟩ : syracuseStep 729155 = 1093733) B1093733
theorem B729185 : Blo 483789 729185 := bstep (se 2 (by rfl) ⟨273444, by rfl⟩ : syracuseStep 729185 = 546889) B546889
theorem B729203 : Blo 483789 729203 := bstep (se 1 (by rfl) ⟨546902, by rfl⟩ : syracuseStep 729203 = 1093805) B1093805
theorem B729233 : Blo 483789 729233 := bstep (se 2 (by rfl) ⟨273462, by rfl⟩ : syracuseStep 729233 = 546925) B546925
theorem B729251 : Blo 483789 729251 := bstep (se 1 (by rfl) ⟨546938, by rfl⟩ : syracuseStep 729251 = 1093877) B1093877
theorem B729281 : Blo 483789 729281 := bstep (se 2 (by rfl) ⟨273480, by rfl⟩ : syracuseStep 729281 = 546961) B546961
theorem B729299 : Blo 483789 729299 := bstep (se 1 (by rfl) ⟨546974, by rfl⟩ : syracuseStep 729299 = 1093949) B1093949
theorem B4661489 : Blo 483789 4661489 := bstep (se 2 (by rfl) ⟨1748058, by rfl⟩ : syracuseStep 4661489 = 3496117) B3496117
theorem B729329 : Blo 483789 729329 := bstep (se 2 (by rfl) ⟨273498, by rfl⟩ : syracuseStep 729329 = 546997) B546997
theorem B729347 : Blo 483789 729347 := bstep (se 1 (by rfl) ⟨547010, by rfl⟩ : syracuseStep 729347 = 1094021) B1094021
theorem B1089809 : Blo 483789 1089809 := bstep (se 2 (by rfl) ⟨408678, by rfl⟩ : syracuseStep 1089809 = 817357) B817357
theorem B729377 : Blo 483789 729377 := bstep (se 2 (by rfl) ⟨273516, by rfl⟩ : syracuseStep 729377 = 547033) B547033
theorem B1089827 : Blo 483789 1089827 := bstep (se 1 (by rfl) ⟨817370, by rfl⟩ : syracuseStep 1089827 = 1634741) B1634741
theorem B1843505 : Blo 483789 1843505 := bstep (se 2 (by rfl) ⟨691314, by rfl⟩ : syracuseStep 1843505 = 1382629) B1382629
theorem B729395 : Blo 483789 729395 := bstep (se 1 (by rfl) ⟨547046, by rfl⟩ : syracuseStep 729395 = 1094093) B1094093
theorem B3678533 : Blo 483789 3678533 := bstep (se 4 (by rfl) ⟨344862, by rfl⟩ : syracuseStep 3678533 = 689725) B689725
theorem B2466125 : Blo 483789 2466125 := bstep (se 3 (by rfl) ⟨462398, by rfl⟩ : syracuseStep 2466125 = 924797) B924797
theorem B729425 : Blo 483789 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B729443 : Blo 483789 729443 := bstep (se 1 (by rfl) ⟨547082, by rfl⟩ : syracuseStep 729443 = 1094165) B1094165
theorem B729473 : Blo 483789 729473 := bstep (se 2 (by rfl) ⟨273552, by rfl⟩ : syracuseStep 729473 = 547105) B547105
theorem B729491 : Blo 483789 729491 := bstep (se 1 (by rfl) ⟨547118, by rfl⟩ : syracuseStep 729491 = 1094237) B1094237
theorem B729521 : Blo 483789 729521 := bstep (se 2 (by rfl) ⟨273570, by rfl⟩ : syracuseStep 729521 = 547141) B547141
theorem B729539 : Blo 483789 729539 := bstep (se 1 (by rfl) ⟨547154, by rfl⟩ : syracuseStep 729539 = 1094309) B1094309
theorem B729569 : Blo 483789 729569 := bstep (se 2 (by rfl) ⟨273588, by rfl⟩ : syracuseStep 729569 = 547177) B547177
theorem B729587 : Blo 483789 729587 := bstep (se 1 (by rfl) ⟨547190, by rfl⟩ : syracuseStep 729587 = 1094381) B1094381
theorem B729617 : Blo 483789 729617 := bstep (se 2 (by rfl) ⟨273606, by rfl⟩ : syracuseStep 729617 = 547213) B547213
theorem B729635 : Blo 483789 729635 := bstep (se 1 (by rfl) ⟨547226, by rfl⟩ : syracuseStep 729635 = 1094453) B1094453
theorem B1090097 : Blo 483789 1090097 := bstep (se 2 (by rfl) ⟨408786, by rfl⟩ : syracuseStep 1090097 = 817573) B817573
theorem B3154481 : Blo 483789 3154481 := bstep (se 2 (by rfl) ⟨1182930, by rfl⟩ : syracuseStep 3154481 = 2365861) B2365861
theorem B1385009 : Blo 483789 1385009 := bstep (se 2 (by rfl) ⟨519378, by rfl⟩ : syracuseStep 1385009 = 1038757) B1038757
theorem B729665 : Blo 483789 729665 := bstep (se 2 (by rfl) ⟨273624, by rfl⟩ : syracuseStep 729665 = 547249) B547249
theorem B1090115 : Blo 483789 1090115 := bstep (se 1 (by rfl) ⟨817586, by rfl⟩ : syracuseStep 1090115 = 1635173) B1635173
theorem B729683 : Blo 483789 729683 := bstep (se 1 (by rfl) ⟨547262, by rfl⟩ : syracuseStep 729683 = 1094525) B1094525
theorem B729713 : Blo 483789 729713 := bstep (se 2 (by rfl) ⟨273642, by rfl⟩ : syracuseStep 729713 = 547285) B547285
theorem B729731 : Blo 483789 729731 := bstep (se 1 (by rfl) ⟨547298, by rfl⟩ : syracuseStep 729731 = 1094597) B1094597
theorem B729761 : Blo 483789 729761 := bstep (se 2 (by rfl) ⟨273660, by rfl⟩ : syracuseStep 729761 = 547321) B547321
theorem B729779 : Blo 483789 729779 := bstep (se 1 (by rfl) ⟨547334, by rfl⟩ : syracuseStep 729779 = 1094669) B1094669
theorem B729809 : Blo 483789 729809 := bstep (se 2 (by rfl) ⟨273678, by rfl⟩ : syracuseStep 729809 = 547357) B547357
theorem B729827 : Blo 483789 729827 := bstep (se 1 (by rfl) ⟨547370, by rfl⟩ : syracuseStep 729827 = 1094741) B1094741
theorem B729857 : Blo 483789 729857 := bstep (se 2 (by rfl) ⟨273696, by rfl⟩ : syracuseStep 729857 = 547393) B547393
theorem B729875 : Blo 483789 729875 := bstep (se 1 (by rfl) ⟨547406, by rfl⟩ : syracuseStep 729875 = 1094813) B1094813
theorem B729905 : Blo 483789 729905 := bstep (se 2 (by rfl) ⟨273714, by rfl⟩ : syracuseStep 729905 = 547429) B547429
theorem B729923 : Blo 483789 729923 := bstep (se 1 (by rfl) ⟨547442, by rfl⟩ : syracuseStep 729923 = 1094885) B1094885
theorem B1090385 : Blo 483789 1090385 := bstep (se 2 (by rfl) ⟨408894, by rfl⟩ : syracuseStep 1090385 = 817789) B817789
theorem B729953 : Blo 483789 729953 := bstep (se 2 (by rfl) ⟨273732, by rfl⟩ : syracuseStep 729953 = 547465) B547465
theorem B1090403 : Blo 483789 1090403 := bstep (se 1 (by rfl) ⟨817802, by rfl⟩ : syracuseStep 1090403 = 1635605) B1635605
theorem B729971 : Blo 483789 729971 := bstep (se 1 (by rfl) ⟨547478, by rfl⟩ : syracuseStep 729971 = 1094957) B1094957
theorem B2761613 : Blo 483789 2761613 := bstep (se 3 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 2761613 = 1035605) B1035605
theorem B730001 : Blo 483789 730001 := bstep (se 2 (by rfl) ⟨273750, by rfl⟩ : syracuseStep 730001 = 547501) B547501
theorem B730019 : Blo 483789 730019 := bstep (se 1 (by rfl) ⟨547514, by rfl⟩ : syracuseStep 730019 = 1095029) B1095029
theorem B730049 : Blo 483789 730049 := bstep (se 2 (by rfl) ⟨273768, by rfl⟩ : syracuseStep 730049 = 547537) B547537
theorem B730067 : Blo 483789 730067 := bstep (se 1 (by rfl) ⟨547550, by rfl⟩ : syracuseStep 730067 = 1095101) B1095101
theorem B730097 : Blo 483789 730097 := bstep (se 2 (by rfl) ⟨273786, by rfl⟩ : syracuseStep 730097 = 547573) B547573
theorem B730115 : Blo 483789 730115 := bstep (se 1 (by rfl) ⟨547586, by rfl⟩ : syracuseStep 730115 = 1095173) B1095173
theorem B730145 : Blo 483789 730145 := bstep (se 2 (by rfl) ⟨273804, by rfl⟩ : syracuseStep 730145 = 547609) B547609
theorem B730163 : Blo 483789 730163 := bstep (se 1 (by rfl) ⟨547622, by rfl⟩ : syracuseStep 730163 = 1095245) B1095245
theorem B6628405 : Blo 483789 6628405 := bstep (se 5 (by rfl) ⟨310706, by rfl⟩ : syracuseStep 6628405 = 621413) B621413
theorem B730193 : Blo 483789 730193 := bstep (se 2 (by rfl) ⟨273822, by rfl⟩ : syracuseStep 730193 = 547645) B547645
theorem B730211 : Blo 483789 730211 := bstep (se 1 (by rfl) ⟨547658, by rfl⟩ : syracuseStep 730211 = 1095317) B1095317
theorem B1090673 : Blo 483789 1090673 := bstep (se 2 (by rfl) ⟨409002, by rfl⟩ : syracuseStep 1090673 = 818005) B818005
theorem B730241 : Blo 483789 730241 := bstep (se 2 (by rfl) ⟨273840, by rfl⟩ : syracuseStep 730241 = 547681) B547681
theorem B1090691 : Blo 483789 1090691 := bstep (se 1 (by rfl) ⟨818018, by rfl⟩ : syracuseStep 1090691 = 1636037) B1636037
theorem B730259 : Blo 483789 730259 := bstep (se 1 (by rfl) ⟨547694, by rfl⟩ : syracuseStep 730259 = 1095389) B1095389
theorem B730289 : Blo 483789 730289 := bstep (se 2 (by rfl) ⟨273858, by rfl⟩ : syracuseStep 730289 = 547717) B547717
theorem B730307 : Blo 483789 730307 := bstep (se 1 (by rfl) ⟨547730, by rfl⟩ : syracuseStep 730307 = 1095461) B1095461
theorem B730337 : Blo 483789 730337 := bstep (se 2 (by rfl) ⟨273876, by rfl⟩ : syracuseStep 730337 = 547753) B547753
theorem B730355 : Blo 483789 730355 := bstep (se 1 (by rfl) ⟨547766, by rfl⟩ : syracuseStep 730355 = 1095533) B1095533
theorem B730385 : Blo 483789 730385 := bstep (se 2 (by rfl) ⟨273894, by rfl⟩ : syracuseStep 730385 = 547789) B547789
theorem B730403 : Blo 483789 730403 := bstep (se 1 (by rfl) ⟨547802, by rfl⟩ : syracuseStep 730403 = 1095605) B1095605
theorem B730433 : Blo 483789 730433 := bstep (se 2 (by rfl) ⟨273912, by rfl⟩ : syracuseStep 730433 = 547825) B547825
theorem B730451 : Blo 483789 730451 := bstep (se 1 (by rfl) ⟨547838, by rfl⟩ : syracuseStep 730451 = 1095677) B1095677
theorem B730481 : Blo 483789 730481 := bstep (se 2 (by rfl) ⟨273930, by rfl⟩ : syracuseStep 730481 = 547861) B547861
theorem B730499 : Blo 483789 730499 := bstep (se 1 (by rfl) ⟨547874, by rfl⟩ : syracuseStep 730499 = 1095749) B1095749
theorem B1090961 : Blo 483789 1090961 := bstep (se 2 (by rfl) ⟨409110, by rfl⟩ : syracuseStep 1090961 = 818221) B818221
theorem B730529 : Blo 483789 730529 := bstep (se 2 (by rfl) ⟨273948, by rfl⟩ : syracuseStep 730529 = 547897) B547897
theorem B1090979 : Blo 483789 1090979 := bstep (se 1 (by rfl) ⟨818234, by rfl⟩ : syracuseStep 1090979 = 1636469) B1636469
theorem B730547 : Blo 483789 730547 := bstep (se 1 (by rfl) ⟨547910, by rfl⟩ : syracuseStep 730547 = 1095821) B1095821
theorem B730577 : Blo 483789 730577 := bstep (se 2 (by rfl) ⟨273966, by rfl⟩ : syracuseStep 730577 = 547933) B547933
theorem B730595 : Blo 483789 730595 := bstep (se 1 (by rfl) ⟨547946, by rfl⟩ : syracuseStep 730595 = 1095893) B1095893
theorem B730625 : Blo 483789 730625 := bstep (se 2 (by rfl) ⟨273984, by rfl⟩ : syracuseStep 730625 = 547969) B547969
theorem B730643 : Blo 483789 730643 := bstep (se 1 (by rfl) ⟨547982, by rfl⟩ : syracuseStep 730643 = 1095965) B1095965
theorem B730673 : Blo 483789 730673 := bstep (se 2 (by rfl) ⟨274002, by rfl⟩ : syracuseStep 730673 = 548005) B548005
theorem B730691 : Blo 483789 730691 := bstep (se 1 (by rfl) ⟨548018, by rfl⟩ : syracuseStep 730691 = 1096037) B1096037
theorem B730721 : Blo 483789 730721 := bstep (se 2 (by rfl) ⟨274020, by rfl⟩ : syracuseStep 730721 = 548041) B548041
theorem B730739 : Blo 483789 730739 := bstep (se 1 (by rfl) ⟨548054, by rfl⟩ : syracuseStep 730739 = 1096109) B1096109
theorem B4368013 : Blo 483789 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B730769 : Blo 483789 730769 := bstep (se 2 (by rfl) ⟨274038, by rfl⟩ : syracuseStep 730769 = 548077) B548077
theorem B730787 : Blo 483789 730787 := bstep (se 1 (by rfl) ⟨548090, by rfl⟩ : syracuseStep 730787 = 1096181) B1096181
theorem B1091249 : Blo 483789 1091249 := bstep (se 2 (by rfl) ⟨409218, by rfl⟩ : syracuseStep 1091249 = 818437) B818437
theorem B730817 : Blo 483789 730817 := bstep (se 2 (by rfl) ⟨274056, by rfl⟩ : syracuseStep 730817 = 548113) B548113
theorem B1091267 : Blo 483789 1091267 := bstep (se 1 (by rfl) ⟨818450, by rfl⟩ : syracuseStep 1091267 = 1636901) B1636901
theorem B730835 : Blo 483789 730835 := bstep (se 1 (by rfl) ⟨548126, by rfl⟩ : syracuseStep 730835 = 1096253) B1096253
theorem B1844963 : Blo 483789 1844963 := bstep (se 1 (by rfl) ⟨1383722, by rfl⟩ : syracuseStep 1844963 = 2767445) B2767445
theorem B1844977 : Blo 483789 1844977 := bstep (se 2 (by rfl) ⟨691866, by rfl⟩ : syracuseStep 1844977 = 1383733) B1383733
theorem B730865 : Blo 483789 730865 := bstep (se 2 (by rfl) ⟨274074, by rfl⟩ : syracuseStep 730865 = 548149) B548149
theorem B730883 : Blo 483789 730883 := bstep (se 1 (by rfl) ⟨548162, by rfl⟩ : syracuseStep 730883 = 1096325) B1096325
theorem B730913 : Blo 483789 730913 := bstep (se 2 (by rfl) ⟨274092, by rfl⟩ : syracuseStep 730913 = 548185) B548185
theorem B2762545 : Blo 483789 2762545 := bstep (se 2 (by rfl) ⟨1035954, by rfl⟩ : syracuseStep 2762545 = 2071909) B2071909
theorem B730931 : Blo 483789 730931 := bstep (se 1 (by rfl) ⟨548198, by rfl⟩ : syracuseStep 730931 = 1096397) B1096397
theorem B730961 : Blo 483789 730961 := bstep (se 2 (by rfl) ⟨274110, by rfl⟩ : syracuseStep 730961 = 548221) B548221
theorem B730979 : Blo 483789 730979 := bstep (se 1 (by rfl) ⟨548234, by rfl⟩ : syracuseStep 730979 = 1096469) B1096469
theorem B731009 : Blo 483789 731009 := bstep (se 2 (by rfl) ⟨274128, by rfl⟩ : syracuseStep 731009 = 548257) B548257
theorem B731027 : Blo 483789 731027 := bstep (se 1 (by rfl) ⟨548270, by rfl⟩ : syracuseStep 731027 = 1096541) B1096541
theorem B731057 : Blo 483789 731057 := bstep (se 2 (by rfl) ⟨274146, by rfl⟩ : syracuseStep 731057 = 548293) B548293
theorem B731075 : Blo 483789 731075 := bstep (se 1 (by rfl) ⟨548306, by rfl⟩ : syracuseStep 731075 = 1096613) B1096613
theorem B1091537 : Blo 483789 1091537 := bstep (se 2 (by rfl) ⟨409326, by rfl⟩ : syracuseStep 1091537 = 818653) B818653
theorem B731105 : Blo 483789 731105 := bstep (se 2 (by rfl) ⟨274164, by rfl⟩ : syracuseStep 731105 = 548329) B548329
theorem B1091555 : Blo 483789 1091555 := bstep (se 1 (by rfl) ⟨818666, by rfl⟩ : syracuseStep 1091555 = 1637333) B1637333
theorem B1386467 : Blo 483789 1386467 := bstep (se 1 (by rfl) ⟨1039850, by rfl⟩ : syracuseStep 1386467 = 2079701) B2079701
theorem B731123 : Blo 483789 731123 := bstep (se 1 (by rfl) ⟨548342, by rfl⟩ : syracuseStep 731123 = 1096685) B1096685
theorem B731153 : Blo 483789 731153 := bstep (se 2 (by rfl) ⟨274182, by rfl⟩ : syracuseStep 731153 = 548365) B548365
theorem B731171 : Blo 483789 731171 := bstep (se 1 (by rfl) ⟨548378, by rfl⟩ : syracuseStep 731171 = 1096757) B1096757
theorem B731201 : Blo 483789 731201 := bstep (se 2 (by rfl) ⟨274200, by rfl⟩ : syracuseStep 731201 = 548401) B548401
theorem B1747021 : Blo 483789 1747021 := bstep (se 3 (by rfl) ⟨327566, by rfl⟩ : syracuseStep 1747021 = 655133) B655133
theorem B731219 : Blo 483789 731219 := bstep (se 1 (by rfl) ⟨548414, by rfl⟩ : syracuseStep 731219 = 1096829) B1096829
theorem B731249 : Blo 483789 731249 := bstep (se 2 (by rfl) ⟨274218, by rfl⟩ : syracuseStep 731249 = 548437) B548437
theorem B731267 : Blo 483789 731267 := bstep (se 1 (by rfl) ⟨548450, by rfl⟩ : syracuseStep 731267 = 1096901) B1096901
theorem B731297 : Blo 483789 731297 := bstep (se 2 (by rfl) ⟨274236, by rfl⟩ : syracuseStep 731297 = 548473) B548473
theorem B731315 : Blo 483789 731315 := bstep (se 1 (by rfl) ⟨548486, by rfl⟩ : syracuseStep 731315 = 1096973) B1096973
theorem B8890565 : Blo 483789 8890565 := bstep (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) B1666981
theorem B731345 : Blo 483789 731345 := bstep (se 2 (by rfl) ⟨274254, by rfl⟩ : syracuseStep 731345 = 548509) B548509
theorem B731363 : Blo 483789 731363 := bstep (se 1 (by rfl) ⟨548522, by rfl⟩ : syracuseStep 731363 = 1097045) B1097045
theorem B1091825 : Blo 483789 1091825 := bstep (se 2 (by rfl) ⟨409434, by rfl⟩ : syracuseStep 1091825 = 818869) B818869
theorem B731393 : Blo 483789 731393 := bstep (se 2 (by rfl) ⟨274272, by rfl⟩ : syracuseStep 731393 = 548545) B548545
theorem B1091843 : Blo 483789 1091843 := bstep (se 1 (by rfl) ⟨818882, by rfl⟩ : syracuseStep 1091843 = 1637765) B1637765
theorem B731411 : Blo 483789 731411 := bstep (se 1 (by rfl) ⟨548558, by rfl⟩ : syracuseStep 731411 = 1097117) B1097117
theorem B731441 : Blo 483789 731441 := bstep (se 2 (by rfl) ⟨274290, by rfl⟩ : syracuseStep 731441 = 548581) B548581
theorem B731459 : Blo 483789 731459 := bstep (se 1 (by rfl) ⟨548594, by rfl⟩ : syracuseStep 731459 = 1097189) B1097189
theorem B731489 : Blo 483789 731489 := bstep (se 2 (by rfl) ⟨274308, by rfl⟩ : syracuseStep 731489 = 548617) B548617
theorem B2959715 : Blo 483789 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B731507 : Blo 483789 731507 := bstep (se 1 (by rfl) ⟨548630, by rfl⟩ : syracuseStep 731507 = 1097261) B1097261
theorem B6203789 : Blo 483789 6203789 := bstep (se 3 (by rfl) ⟨1163210, by rfl⟩ : syracuseStep 6203789 = 2326421) B2326421
theorem B731537 : Blo 483789 731537 := bstep (se 2 (by rfl) ⟨274326, by rfl⟩ : syracuseStep 731537 = 548653) B548653
theorem B731555 : Blo 483789 731555 := bstep (se 1 (by rfl) ⟨548666, by rfl⟩ : syracuseStep 731555 = 1097333) B1097333
theorem B731585 : Blo 483789 731585 := bstep (se 2 (by rfl) ⟨274344, by rfl⟩ : syracuseStep 731585 = 548689) B548689
theorem B1583555 : Blo 483789 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B731603 : Blo 483789 731603 := bstep (se 1 (by rfl) ⟨548702, by rfl⟩ : syracuseStep 731603 = 1097405) B1097405
theorem B731633 : Blo 483789 731633 := bstep (se 2 (by rfl) ⟨274362, by rfl⟩ : syracuseStep 731633 = 548725) B548725
theorem B731651 : Blo 483789 731651 := bstep (se 1 (by rfl) ⟨548738, by rfl⟩ : syracuseStep 731651 = 1097477) B1097477
theorem B1092113 : Blo 483789 1092113 := bstep (se 2 (by rfl) ⟨409542, by rfl⟩ : syracuseStep 1092113 = 819085) B819085
theorem B731681 : Blo 483789 731681 := bstep (se 2 (by rfl) ⟨274380, by rfl⟩ : syracuseStep 731681 = 548761) B548761
theorem B1092131 : Blo 483789 1092131 := bstep (se 1 (by rfl) ⟨819098, by rfl⟩ : syracuseStep 1092131 = 1638197) B1638197
theorem B11250373 : Blo 483789 11250373 := bstep (se 4 (by rfl) ⟨1054722, by rfl⟩ : syracuseStep 11250373 = 2109445) B2109445
theorem B1551089 : Blo 483789 1551089 := bstep (se 2 (by rfl) ⟨581658, by rfl⟩ : syracuseStep 1551089 = 1163317) B1163317
theorem B1387277 : Blo 483789 1387277 := bstep (se 3 (by rfl) ⟨260114, by rfl⟩ : syracuseStep 1387277 = 520229) B520229
theorem B1092401 : Blo 483789 1092401 := bstep (se 2 (by rfl) ⟨409650, by rfl⟩ : syracuseStep 1092401 = 819301) B819301
theorem B1092419 : Blo 483789 1092419 := bstep (se 1 (by rfl) ⟨819314, by rfl⟩ : syracuseStep 1092419 = 1638629) B1638629
theorem B5909429 : Blo 483789 5909429 := bstep (se 5 (by rfl) ⟨277004, by rfl⟩ : syracuseStep 5909429 = 554009) B554009
theorem B1387469 : Blo 483789 1387469 := bstep (se 3 (by rfl) ⟨260150, by rfl⟩ : syracuseStep 1387469 = 520301) B520301
theorem B2108429 : Blo 483789 2108429 := bstep (se 3 (by rfl) ⟨395330, by rfl⟩ : syracuseStep 2108429 = 790661) B790661
theorem B1092689 : Blo 483789 1092689 := bstep (se 2 (by rfl) ⟨409758, by rfl⟩ : syracuseStep 1092689 = 819517) B819517
theorem B1092707 : Blo 483789 1092707 := bstep (se 1 (by rfl) ⟨819530, by rfl⟩ : syracuseStep 1092707 = 1639061) B1639061
theorem B1846435 : Blo 483789 1846435 := bstep (se 1 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 1846435 = 2769653) B2769653
theorem B2469041 : Blo 483789 2469041 := bstep (se 2 (by rfl) ⟨925890, by rfl⟩ : syracuseStep 2469041 = 1851781) B1851781
theorem B2764003 : Blo 483789 2764003 := bstep (se 1 (by rfl) ⟨2073002, by rfl⟩ : syracuseStep 2764003 = 4146005) B4146005
theorem B1092977 : Blo 483789 1092977 := bstep (se 2 (by rfl) ⟨409866, by rfl⟩ : syracuseStep 1092977 = 819733) B819733
theorem B1092995 : Blo 483789 1092995 := bstep (se 1 (by rfl) ⟨819746, by rfl⟩ : syracuseStep 1092995 = 1639493) B1639493
theorem B2076131 : Blo 483789 2076131 := bstep (se 1 (by rfl) ⟨1557098, by rfl⟩ : syracuseStep 2076131 = 3114197) B3114197
theorem B831043 : Blo 483789 831043 := bstep (se 1 (by rfl) ⟨623282, by rfl⟩ : syracuseStep 831043 = 1246565) B1246565
theorem B1093265 : Blo 483789 1093265 := bstep (se 2 (by rfl) ⟨409974, by rfl⟩ : syracuseStep 1093265 = 819949) B819949
theorem B1093283 : Blo 483789 1093283 := bstep (se 1 (by rfl) ⟨819962, by rfl⟩ : syracuseStep 1093283 = 1639925) B1639925
theorem B1683149 : Blo 483789 1683149 := bstep (se 3 (by rfl) ⟨315590, by rfl⟩ : syracuseStep 1683149 = 631181) B631181
theorem B2764529 : Blo 483789 2764529 := bstep (se 2 (by rfl) ⟨1036698, by rfl⟩ : syracuseStep 2764529 = 2073397) B2073397
theorem B2338723 : Blo 483789 2338723 := bstep (se 1 (by rfl) ⟨1754042, by rfl⟩ : syracuseStep 2338723 = 3508085) B3508085
theorem B1388461 : Blo 483789 1388461 := bstep (se 3 (by rfl) ⟨260336, by rfl⟩ : syracuseStep 1388461 = 520673) B520673
theorem B1093553 : Blo 483789 1093553 := bstep (se 2 (by rfl) ⟨410082, by rfl⟩ : syracuseStep 1093553 = 820165) B820165
theorem B1093571 : Blo 483789 1093571 := bstep (se 1 (by rfl) ⟨820178, by rfl⟩ : syracuseStep 1093571 = 1640357) B1640357
theorem B667667 : Blo 483789 667667 := bstep (se 1 (by rfl) ⟨500750, by rfl⟩ : syracuseStep 667667 = 1001501) B1001501
theorem B831521 : Blo 483789 831521 := bstep (se 2 (by rfl) ⟨311820, by rfl⟩ : syracuseStep 831521 = 623641) B623641
theorem B1093841 : Blo 483789 1093841 := bstep (se 2 (by rfl) ⟨410190, by rfl⟩ : syracuseStep 1093841 = 820381) B820381
theorem B1093859 : Blo 483789 1093859 := bstep (se 1 (by rfl) ⟨820394, by rfl⟩ : syracuseStep 1093859 = 1640789) B1640789
theorem B6238691 : Blo 483789 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B1094129 : Blo 483789 1094129 := bstep (se 2 (by rfl) ⟨410298, by rfl⟩ : syracuseStep 1094129 = 820597) B820597
theorem B1094147 : Blo 483789 1094147 := bstep (se 1 (by rfl) ⟨820610, by rfl⟩ : syracuseStep 1094147 = 1641221) B1641221
theorem B5550605 : Blo 483789 5550605 := bstep (se 3 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 5550605 = 2081477) B2081477
theorem B1913507 : Blo 483789 1913507 := bstep (se 1 (by rfl) ⟨1435130, by rfl⟩ : syracuseStep 1913507 = 2870261) B2870261
theorem B1553165 : Blo 483789 1553165 := bstep (se 3 (by rfl) ⟨291218, by rfl⟩ : syracuseStep 1553165 = 582437) B582437
theorem B1225489 : Blo 483789 1225489 := bstep (se 2 (by rfl) ⟨459558, by rfl⟩ : syracuseStep 1225489 = 919117) B919117
theorem B1094417 : Blo 483789 1094417 := bstep (se 2 (by rfl) ⟨410406, by rfl⟩ : syracuseStep 1094417 = 820813) B820813
theorem B1094435 : Blo 483789 1094435 := bstep (se 1 (by rfl) ⟨820826, by rfl⟩ : syracuseStep 1094435 = 1641653) B1641653
theorem B2634545 : Blo 483789 2634545 := bstep (se 2 (by rfl) ⟨987954, by rfl⟩ : syracuseStep 2634545 = 1975909) B1975909
theorem B2667377 : Blo 483789 2667377 := bstep (se 2 (by rfl) ⟨1000266, by rfl⟩ : syracuseStep 2667377 = 2000533) B2000533
theorem B1225763 : Blo 483789 1225763 := bstep (se 1 (by rfl) ⟨919322, by rfl⟩ : syracuseStep 1225763 = 1838645) B1838645
theorem B832547 : Blo 483789 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B1094705 : Blo 483789 1094705 := bstep (se 2 (by rfl) ⟨410514, by rfl⟩ : syracuseStep 1094705 = 821029) B821029
theorem B1094723 : Blo 483789 1094723 := bstep (se 1 (by rfl) ⟨821042, by rfl⟩ : syracuseStep 1094723 = 1642085) B1642085
theorem B2765987 : Blo 483789 2765987 := bstep (se 1 (by rfl) ⟨2074490, by rfl⟩ : syracuseStep 2765987 = 4148981) B4148981
theorem B1225955 : Blo 483789 1225955 := bstep (se 1 (by rfl) ⟨919466, by rfl⟩ : syracuseStep 1225955 = 1838933) B1838933
theorem B1848653 : Blo 483789 1848653 := bstep (se 3 (by rfl) ⟨346622, by rfl⟩ : syracuseStep 1848653 = 693245) B693245
theorem B1094993 : Blo 483789 1094993 := bstep (se 2 (by rfl) ⟨410622, by rfl⟩ : syracuseStep 1094993 = 821245) B821245
theorem B1095011 : Blo 483789 1095011 := bstep (se 1 (by rfl) ⟨821258, by rfl⟩ : syracuseStep 1095011 = 1642517) B1642517
theorem B2078129 : Blo 483789 2078129 := bstep (se 2 (by rfl) ⟨779298, by rfl⟩ : syracuseStep 2078129 = 1558597) B1558597
theorem B1095281 : Blo 483789 1095281 := bstep (se 2 (by rfl) ⟨410730, by rfl⟩ : syracuseStep 1095281 = 821461) B821461
theorem B1095299 : Blo 483789 1095299 := bstep (se 1 (by rfl) ⟨821474, by rfl⟩ : syracuseStep 1095299 = 1642949) B1642949
theorem B3356293 : Blo 483789 3356293 := bstep (se 4 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 3356293 = 629305) B629305
theorem B1554061 : Blo 483789 1554061 := bstep (se 3 (by rfl) ⟨291386, by rfl⟩ : syracuseStep 1554061 = 582773) B582773
theorem B1095569 : Blo 483789 1095569 := bstep (se 2 (by rfl) ⟨410838, by rfl⟩ : syracuseStep 1095569 = 821677) B821677
theorem B1095587 : Blo 483789 1095587 := bstep (se 1 (by rfl) ⟨821690, by rfl⟩ : syracuseStep 1095587 = 1643381) B1643381
theorem B3684365 : Blo 483789 3684365 := bstep (se 3 (by rfl) ⟨690818, by rfl⟩ : syracuseStep 3684365 = 1381637) B1381637
theorem B1226897 : Blo 483789 1226897 := bstep (se 2 (by rfl) ⟨460086, by rfl⟩ : syracuseStep 1226897 = 920173) B920173
theorem B1095857 : Blo 483789 1095857 := bstep (se 2 (by rfl) ⟨410946, by rfl⟩ : syracuseStep 1095857 = 821893) B821893
theorem B1226947 : Blo 483789 1226947 := bstep (se 1 (by rfl) ⟨920210, by rfl⟩ : syracuseStep 1226947 = 1840421) B1840421
theorem B1095875 : Blo 483789 1095875 := bstep (se 1 (by rfl) ⟨821906, by rfl⟩ : syracuseStep 1095875 = 1643813) B1643813
theorem B2635973 : Blo 483789 2635973 := bstep (se 4 (by rfl) ⟨247122, by rfl⟩ : syracuseStep 2635973 = 494245) B494245
theorem B2079053 : Blo 483789 2079053 := bstep (se 3 (by rfl) ⟨389822, by rfl⟩ : syracuseStep 2079053 = 779645) B779645
theorem B1227089 : Blo 483789 1227089 := bstep (se 2 (by rfl) ⟨460158, by rfl⟩ : syracuseStep 1227089 = 920317) B920317
theorem B5257669 : Blo 483789 5257669 := bstep (se 4 (by rfl) ⟨492906, by rfl⟩ : syracuseStep 5257669 = 985813) B985813
theorem B1096145 : Blo 483789 1096145 := bstep (se 2 (by rfl) ⟨411054, by rfl⟩ : syracuseStep 1096145 = 822109) B822109
theorem B1096163 : Blo 483789 1096163 := bstep (se 1 (by rfl) ⟨822122, by rfl⟩ : syracuseStep 1096163 = 1644245) B1644245
theorem B1554947 : Blo 483789 1554947 := bstep (se 1 (by rfl) ⟨1166210, by rfl⟩ : syracuseStep 1554947 = 2332421) B2332421
theorem B735857 : Blo 483789 735857 := bstep (se 2 (by rfl) ⟨275946, by rfl⟩ : syracuseStep 735857 = 551893) B551893
theorem B2210417 : Blo 483789 2210417 := bstep (se 2 (by rfl) ⟨828906, by rfl⟩ : syracuseStep 2210417 = 1657813) B1657813
theorem B3357317 : Blo 483789 3357317 := bstep (se 4 (by rfl) ⟨314748, by rfl⟩ : syracuseStep 3357317 = 629497) B629497
theorem B1096433 : Blo 483789 1096433 := bstep (se 2 (by rfl) ⟨411162, by rfl⟩ : syracuseStep 1096433 = 822325) B822325
theorem B1096451 : Blo 483789 1096451 := bstep (se 1 (by rfl) ⟨822338, by rfl⟩ : syracuseStep 1096451 = 1644677) B1644677
theorem B2767877 : Blo 483789 2767877 := bstep (se 4 (by rfl) ⟨259488, by rfl⟩ : syracuseStep 2767877 = 518977) B518977
theorem B1096721 : Blo 483789 1096721 := bstep (se 2 (by rfl) ⟨411270, by rfl⟩ : syracuseStep 1096721 = 822541) B822541
theorem B1096739 : Blo 483789 1096739 := bstep (se 1 (by rfl) ⟨822554, by rfl⟩ : syracuseStep 1096739 = 1645109) B1645109
theorem B1228081 : Blo 483789 1228081 := bstep (se 2 (by rfl) ⟨460530, by rfl⟩ : syracuseStep 1228081 = 921061) B921061
theorem B1097009 : Blo 483789 1097009 := bstep (se 2 (by rfl) ⟨411378, by rfl⟩ : syracuseStep 1097009 = 822757) B822757
theorem B1097027 : Blo 483789 1097027 := bstep (se 1 (by rfl) ⟨822770, by rfl⟩ : syracuseStep 1097027 = 1645541) B1645541
theorem B5553521 : Blo 483789 5553521 := bstep (se 2 (by rfl) ⟨2082570, by rfl⟩ : syracuseStep 5553521 = 4165141) B4165141
theorem B47431109 : Blo 483789 47431109 := bstep (se 4 (by rfl) ⟨4446666, by rfl⟩ : syracuseStep 47431109 = 8893333) B8893333
theorem B1228355 : Blo 483789 1228355 := bstep (se 1 (by rfl) ⟨921266, by rfl⟩ : syracuseStep 1228355 = 1842533) B1842533
theorem B1097297 : Blo 483789 1097297 := bstep (se 2 (by rfl) ⟨411486, by rfl⟩ : syracuseStep 1097297 = 822973) B822973
theorem B1097315 : Blo 483789 1097315 := bstep (se 1 (by rfl) ⟨822986, by rfl⟩ : syracuseStep 1097315 = 1645973) B1645973
theorem B2342627 : Blo 483789 2342627 := bstep (se 1 (by rfl) ⟨1756970, by rfl⟩ : syracuseStep 2342627 = 3513941) B3513941
theorem B1228547 : Blo 483789 1228547 := bstep (se 1 (by rfl) ⟨921410, by rfl⟩ : syracuseStep 1228547 = 1842821) B1842821
theorem B737219 : Blo 483789 737219 := bstep (se 1 (by rfl) ⟨552914, by rfl⟩ : syracuseStep 737219 = 1105829) B1105829
theorem B1851569 : Blo 483789 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B1557137 : Blo 483789 1557137 := bstep (se 2 (by rfl) ⟨583926, by rfl⟩ : syracuseStep 1557137 = 1167853) B1167853
theorem B1229489 : Blo 483789 1229489 := bstep (se 2 (by rfl) ⟨461058, by rfl⟩ : syracuseStep 1229489 = 922117) B922117
theorem B1229539 : Blo 483789 1229539 := bstep (se 1 (by rfl) ⟨922154, by rfl⟩ : syracuseStep 1229539 = 1844309) B1844309
theorem B1557265 : Blo 483789 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B3687281 : Blo 483789 3687281 := bstep (se 2 (by rfl) ⟨1382730, by rfl⟩ : syracuseStep 3687281 = 2765461) B2765461
theorem B1229681 : Blo 483789 1229681 := bstep (se 2 (by rfl) ⟨461130, by rfl⟩ : syracuseStep 1229681 = 922261) B922261
theorem B1622897 : Blo 483789 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B13288333 : Blo 483789 13288333 := bstep (se 3 (by rfl) ⟨2491562, by rfl⟩ : syracuseStep 13288333 = 4983125) B4983125
theorem B1557521 : Blo 483789 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B7554161 : Blo 483789 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B1230001 : Blo 483789 1230001 := bstep (se 2 (by rfl) ⟨461250, by rfl⟩ : syracuseStep 1230001 = 922501) B922501
theorem B1164547 : Blo 483789 1164547 := bstep (se 1 (by rfl) ⟨873410, by rfl⟩ : syracuseStep 1164547 = 1746821) B1746821
theorem B2082161 : Blo 483789 2082161 := bstep (se 2 (by rfl) ⟨780810, by rfl⟩ : syracuseStep 2082161 = 1561621) B1561621
theorem B1230673 : Blo 483789 1230673 := bstep (se 2 (by rfl) ⟨461502, by rfl⟩ : syracuseStep 1230673 = 923005) B923005
theorem B1230947 : Blo 483789 1230947 := bstep (se 1 (by rfl) ⟨923210, by rfl⟩ : syracuseStep 1230947 = 1846421) B1846421
theorem B1034417 : Blo 483789 1034417 := bstep (se 2 (by rfl) ⟨387906, by rfl⟩ : syracuseStep 1034417 = 775813) B775813
theorem B13289669 : Blo 483789 13289669 := bstep (se 4 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 13289669 = 2491813) B2491813
theorem B3754225 : Blo 483789 3754225 := bstep (se 2 (by rfl) ⟨1407834, by rfl⟩ : syracuseStep 3754225 = 2815669) B2815669
theorem B1231139 : Blo 483789 1231139 := bstep (se 1 (by rfl) ⟨923354, by rfl⟩ : syracuseStep 1231139 = 1846709) B1846709
theorem B1755427 : Blo 483789 1755427 := bstep (se 1 (by rfl) ⟨1316570, by rfl⟩ : syracuseStep 1755427 = 2633141) B2633141
theorem B739793 : Blo 483789 739793 := bstep (se 2 (by rfl) ⟨277422, by rfl⟩ : syracuseStep 739793 = 554845) B554845
theorem B739811 : Blo 483789 739811 := bstep (se 1 (by rfl) ⟨554858, by rfl⟩ : syracuseStep 739811 = 1109717) B1109717
theorem B1165873 : Blo 483789 1165873 := bstep (se 2 (by rfl) ⟨437202, by rfl⟩ : syracuseStep 1165873 = 874405) B874405
theorem B739939 : Blo 483789 739939 := bstep (se 1 (by rfl) ⟨554954, by rfl⟩ : syracuseStep 739939 = 1109909) B1109909
theorem B2083427 : Blo 483789 2083427 := bstep (se 1 (by rfl) ⟨1562570, by rfl⟩ : syracuseStep 2083427 = 3125141) B3125141
theorem B3361421 : Blo 483789 3361421 := bstep (se 3 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 3361421 = 1260533) B1260533
theorem B1559213 : Blo 483789 1559213 := bstep (se 3 (by rfl) ⟨292352, by rfl⟩ : syracuseStep 1559213 = 584705) B584705
theorem B2214577 : Blo 483789 2214577 := bstep (se 2 (by rfl) ⟨830466, by rfl⟩ : syracuseStep 2214577 = 1660933) B1660933
theorem B1034947 : Blo 483789 1034947 := bstep (se 1 (by rfl) ⟨776210, by rfl⟩ : syracuseStep 1034947 = 1552421) B1552421
theorem B740321 : Blo 483789 740321 := bstep (se 2 (by rfl) ⟨277620, by rfl⟩ : syracuseStep 740321 = 555241) B555241
theorem B4672525 : Blo 483789 4672525 := bstep (se 3 (by rfl) ⟨876098, by rfl⟩ : syracuseStep 4672525 = 1752197) B1752197
theorem B1232081 : Blo 483789 1232081 := bstep (se 2 (by rfl) ⟨462030, by rfl⟩ : syracuseStep 1232081 = 924061) B924061
theorem B1232131 : Blo 483789 1232131 := bstep (se 1 (by rfl) ⟨924098, by rfl⟩ : syracuseStep 1232131 = 1848197) B1848197
theorem B6638861 : Blo 483789 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B1658225 : Blo 483789 1658225 := bstep (se 2 (by rfl) ⟨621834, by rfl⟩ : syracuseStep 1658225 = 1243669) B1243669
theorem B8539505 : Blo 483789 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B1232273 : Blo 483789 1232273 := bstep (se 2 (by rfl) ⟨462102, by rfl⟩ : syracuseStep 1232273 = 924205) B924205
theorem B1559981 : Blo 483789 1559981 := bstep (se 3 (by rfl) ⟨292496, by rfl⟩ : syracuseStep 1559981 = 584993) B584993
theorem B1166833 : Blo 483789 1166833 := bstep (se 2 (by rfl) ⟨437562, by rfl⟩ : syracuseStep 1166833 = 875125) B875125
theorem B544387 : Blo 483789 544387 := bstep (se 1 (by rfl) ⟨408290, by rfl⟩ : syracuseStep 544387 = 816581) B816581
theorem B839315 : Blo 483789 839315 := bstep (se 1 (by rfl) ⟨629486, by rfl⟩ : syracuseStep 839315 = 1258973) B1258973
theorem B544531 : Blo 483789 544531 := bstep (se 1 (by rfl) ⟨408398, by rfl⟩ : syracuseStep 544531 = 816797) B816797
theorem B741155 : Blo 483789 741155 := bstep (se 1 (by rfl) ⟨555866, by rfl⟩ : syracuseStep 741155 = 1111733) B1111733
theorem B544675 : Blo 483789 544675 := bstep (se 1 (by rfl) ⟨408506, by rfl⟩ : syracuseStep 544675 = 817013) B817013
theorem B1560493 : Blo 483789 1560493 := bstep (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) B585185
theorem B544819 : Blo 483789 544819 := bstep (se 1 (by rfl) ⟨408614, by rfl⟩ : syracuseStep 544819 = 817229) B817229
theorem B1036433 : Blo 483789 1036433 := bstep (se 2 (by rfl) ⟨388662, by rfl⟩ : syracuseStep 1036433 = 777325) B777325
theorem B1036451 : Blo 483789 1036451 := bstep (se 1 (by rfl) ⟨777338, by rfl⟩ : syracuseStep 1036451 = 1554677) B1554677
theorem B544963 : Blo 483789 544963 := bstep (se 1 (by rfl) ⟨408722, by rfl⟩ : syracuseStep 544963 = 817445) B817445
theorem B12669155 : Blo 483789 12669155 := bstep (se 1 (by rfl) ⟨9501866, by rfl⟩ : syracuseStep 12669155 = 19003733) B19003733
theorem B1364273 : Blo 483789 1364273 := bstep (se 2 (by rfl) ⟨511602, by rfl⟩ : syracuseStep 1364273 = 1023205) B1023205
theorem B545107 : Blo 483789 545107 := bstep (se 1 (by rfl) ⟨408830, by rfl⟩ : syracuseStep 545107 = 817661) B817661
theorem B1233265 : Blo 483789 1233265 := bstep (se 2 (by rfl) ⟨462474, by rfl⟩ : syracuseStep 1233265 = 924949) B924949
theorem B1560995 : Blo 483789 1560995 := bstep (se 1 (by rfl) ⟨1170746, by rfl⟩ : syracuseStep 1560995 = 2341493) B2341493
theorem B545251 : Blo 483789 545251 := bstep (se 1 (by rfl) ⟨408938, by rfl⟩ : syracuseStep 545251 = 817877) B817877
theorem B545395 : Blo 483789 545395 := bstep (se 1 (by rfl) ⟨409046, by rfl⟩ : syracuseStep 545395 = 818093) B818093
theorem B1233539 : Blo 483789 1233539 := bstep (se 1 (by rfl) ⟨925154, by rfl⟩ : syracuseStep 1233539 = 1850309) B1850309
theorem B2773709 : Blo 483789 2773709 := bstep (se 3 (by rfl) ⟨520070, by rfl⟩ : syracuseStep 2773709 = 1040141) B1040141
theorem B545539 : Blo 483789 545539 := bstep (se 1 (by rfl) ⟨409154, by rfl⟩ : syracuseStep 545539 = 818309) B818309
theorem B2216753 : Blo 483789 2216753 := bstep (se 2 (by rfl) ⟨831282, by rfl⟩ : syracuseStep 2216753 = 1662565) B1662565
theorem B1233731 : Blo 483789 1233731 := bstep (se 1 (by rfl) ⟨925298, by rfl⟩ : syracuseStep 1233731 = 1850597) B1850597
theorem B545683 : Blo 483789 545683 := bstep (se 1 (by rfl) ⟨409262, by rfl⟩ : syracuseStep 545683 = 818525) B818525
theorem B545827 : Blo 483789 545827 := bstep (se 1 (by rfl) ⟨409370, by rfl⟩ : syracuseStep 545827 = 818741) B818741
theorem B545971 : Blo 483789 545971 := bstep (se 1 (by rfl) ⟨409478, by rfl⟩ : syracuseStep 545971 = 818957) B818957
theorem B3953891 : Blo 483789 3953891 := bstep (se 1 (by rfl) ⟨2965418, by rfl⟩ : syracuseStep 3953891 = 5930837) B5930837
theorem B873713 : Blo 483789 873713 := bstep (se 2 (by rfl) ⟨327642, by rfl⟩ : syracuseStep 873713 = 655285) B655285
theorem B546115 : Blo 483789 546115 := bstep (se 1 (by rfl) ⟨409586, by rfl⟩ : syracuseStep 546115 = 819173) B819173
theorem B1037681 : Blo 483789 1037681 := bstep (se 2 (by rfl) ⟨389130, by rfl⟩ : syracuseStep 1037681 = 778261) B778261
theorem B546259 : Blo 483789 546259 := bstep (se 1 (by rfl) ⟨409694, by rfl⟩ : syracuseStep 546259 = 819389) B819389
theorem B546403 : Blo 483789 546403 := bstep (se 1 (by rfl) ⟨409802, by rfl⟩ : syracuseStep 546403 = 819605) B819605
theorem B1234673 : Blo 483789 1234673 := bstep (se 2 (by rfl) ⟨463002, by rfl⟩ : syracuseStep 1234673 = 926005) B926005
theorem B546547 : Blo 483789 546547 := bstep (se 1 (by rfl) ⟨409910, by rfl⟩ : syracuseStep 546547 = 819821) B819821
theorem B775955 : Blo 483789 775955 := bstep (se 1 (by rfl) ⟨581966, by rfl⟩ : syracuseStep 775955 = 1163933) B1163933
theorem B3102533 : Blo 483789 3102533 := bstep (se 4 (by rfl) ⟨290862, by rfl⟩ : syracuseStep 3102533 = 581725) B581725
theorem B546691 : Blo 483789 546691 := bstep (se 1 (by rfl) ⟨410018, by rfl⟩ : syracuseStep 546691 = 820037) B820037
theorem B612355 : Blo 483789 612355 := bstep (se 1 (by rfl) ⟨459266, by rfl⟩ : syracuseStep 612355 = 918533) B918533
theorem B546835 : Blo 483789 546835 := bstep (se 1 (by rfl) ⟨410126, by rfl⟩ : syracuseStep 546835 = 820253) B820253
theorem B776243 : Blo 483789 776243 := bstep (se 1 (by rfl) ⟨582182, by rfl⟩ : syracuseStep 776243 = 1164365) B1164365
theorem B612451 : Blo 483789 612451 := bstep (se 1 (by rfl) ⟨459338, by rfl⟩ : syracuseStep 612451 = 918677) B918677
theorem B1333361 : Blo 483789 1333361 := bstep (se 2 (by rfl) ⟨500010, by rfl⟩ : syracuseStep 1333361 = 1000021) B1000021
theorem B546979 : Blo 483789 546979 := bstep (se 1 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 546979 = 820469) B820469
theorem B547123 : Blo 483789 547123 := bstep (se 1 (by rfl) ⟨410342, by rfl⟩ : syracuseStep 547123 = 820685) B820685
theorem B1169795 : Blo 483789 1169795 := bstep (se 1 (by rfl) ⟨877346, by rfl⟩ : syracuseStep 1169795 = 1754693) B1754693
theorem B547267 : Blo 483789 547267 := bstep (se 1 (by rfl) ⟨410450, by rfl⟩ : syracuseStep 547267 = 820901) B820901
theorem B612947 : Blo 483789 612947 := bstep (se 1 (by rfl) ⟨459710, by rfl⟩ : syracuseStep 612947 = 919421) B919421
theorem B547411 : Blo 483789 547411 := bstep (se 1 (by rfl) ⟨410558, by rfl⟩ : syracuseStep 547411 = 821117) B821117
theorem B547555 : Blo 483789 547555 := bstep (se 1 (by rfl) ⟨410666, by rfl⟩ : syracuseStep 547555 = 821333) B821333
theorem B1170179 : Blo 483789 1170179 := bstep (se 1 (by rfl) ⟨877634, by rfl⟩ : syracuseStep 1170179 = 1755269) B1755269
theorem B1334065 : Blo 483789 1334065 := bstep (se 2 (by rfl) ⟨500274, by rfl⟩ : syracuseStep 1334065 = 1000549) B1000549
theorem B777043 : Blo 483789 777043 := bstep (se 1 (by rfl) ⟨582782, by rfl⟩ : syracuseStep 777043 = 1165565) B1165565
theorem B6216547 : Blo 483789 6216547 := bstep (se 1 (by rfl) ⟨4662410, by rfl⟩ : syracuseStep 6216547 = 9324821) B9324821
theorem B547699 : Blo 483789 547699 := bstep (se 1 (by rfl) ⟨410774, by rfl⟩ : syracuseStep 547699 = 821549) B821549
theorem B1039235 : Blo 483789 1039235 := bstep (se 1 (by rfl) ⟨779426, by rfl⟩ : syracuseStep 1039235 = 1558853) B1558853
theorem B2775941 : Blo 483789 2775941 := bstep (se 4 (by rfl) ⟨260244, by rfl⟩ : syracuseStep 2775941 = 520489) B520489
theorem B777185 : Blo 483789 777185 := bstep (se 2 (by rfl) ⟨291444, by rfl⟩ : syracuseStep 777185 = 582889) B582889
theorem B777217 : Blo 483789 777217 := bstep (se 2 (by rfl) ⟨291456, by rfl⟩ : syracuseStep 777217 = 582913) B582913
theorem B547843 : Blo 483789 547843 := bstep (se 1 (by rfl) ⟨410882, by rfl⟩ : syracuseStep 547843 = 821765) B821765
theorem B1170467 : Blo 483789 1170467 := bstep (se 1 (by rfl) ⟨877850, by rfl⟩ : syracuseStep 1170467 = 1755701) B1755701
theorem B711811 : Blo 483789 711811 := bstep (se 1 (by rfl) ⟨533858, by rfl⟩ : syracuseStep 711811 = 1067717) B1067717
theorem B547987 : Blo 483789 547987 := bstep (se 1 (by rfl) ⟨410990, by rfl⟩ : syracuseStep 547987 = 821981) B821981
theorem B613651 : Blo 483789 613651 := bstep (se 1 (by rfl) ⟨460238, by rfl⟩ : syracuseStep 613651 = 920477) B920477
theorem B548131 : Blo 483789 548131 := bstep (se 1 (by rfl) ⟨411098, by rfl⟩ : syracuseStep 548131 = 822197) B822197
theorem B875875 : Blo 483789 875875 := bstep (se 1 (by rfl) ⟨656906, by rfl⟩ : syracuseStep 875875 = 1313813) B1313813
theorem B613747 : Blo 483789 613747 := bstep (se 1 (by rfl) ⟨460310, by rfl⟩ : syracuseStep 613747 = 920621) B920621
theorem B548275 : Blo 483789 548275 := bstep (se 1 (by rfl) ⟨411206, by rfl⟩ : syracuseStep 548275 = 822413) B822413
theorem B1170929 : Blo 483789 1170929 := bstep (se 2 (by rfl) ⟨439098, by rfl⟩ : syracuseStep 1170929 = 878197) B878197
theorem B2776625 : Blo 483789 2776625 := bstep (se 2 (by rfl) ⟨1041234, by rfl⟩ : syracuseStep 2776625 = 2082469) B2082469
theorem B548419 : Blo 483789 548419 := bstep (se 1 (by rfl) ⟨411314, by rfl⟩ : syracuseStep 548419 = 822629) B822629
theorem B548563 : Blo 483789 548563 := bstep (se 1 (by rfl) ⟨411422, by rfl⟩ : syracuseStep 548563 = 822845) B822845
theorem B614243 : Blo 483789 614243 := bstep (se 1 (by rfl) ⟨460682, by rfl⟩ : syracuseStep 614243 = 921365) B921365
theorem B548707 : Blo 483789 548707 := bstep (se 1 (by rfl) ⟨411530, by rfl⟩ : syracuseStep 548707 = 823061) B823061
theorem B778145 : Blo 483789 778145 := bstep (se 2 (by rfl) ⟨291804, by rfl⟩ : syracuseStep 778145 = 583609) B583609
theorem B3366947 : Blo 483789 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B581683 : Blo 483789 581683 := bstep (se 1 (by rfl) ⟨436262, by rfl⟩ : syracuseStep 581683 = 872525) B872525
theorem B1171601 : Blo 483789 1171601 := bstep (se 2 (by rfl) ⟨439350, by rfl⟩ : syracuseStep 1171601 = 878701) B878701
theorem B2449763 : Blo 483789 2449763 := bstep (se 1 (by rfl) ⟨1837322, by rfl⟩ : syracuseStep 2449763 = 3674645) B3674645
theorem B1401229 : Blo 483789 1401229 := bstep (se 3 (by rfl) ⟨262730, by rfl⟩ : syracuseStep 1401229 = 525461) B525461
theorem B582067 : Blo 483789 582067 := bstep (se 1 (by rfl) ⟨436550, by rfl⟩ : syracuseStep 582067 = 873101) B873101
theorem B483795 : Blo 483789 483795 := bstep (se 1 (by rfl) ⟨362846, by rfl⟩ : syracuseStep 483795 = 725693) B725693
theorem B483811 : Blo 483789 483811 := bstep (se 1 (by rfl) ⟨362858, by rfl⟩ : syracuseStep 483811 = 725717) B725717
theorem B483827 : Blo 483789 483827 := bstep (se 1 (by rfl) ⟨362870, by rfl⟩ : syracuseStep 483827 = 725741) B725741
theorem B483843 : Blo 483789 483843 := bstep (se 1 (by rfl) ⟨362882, by rfl⟩ : syracuseStep 483843 = 725765) B725765
theorem B483859 : Blo 483789 483859 := bstep (se 1 (by rfl) ⟨362894, by rfl⟩ : syracuseStep 483859 = 725789) B725789
theorem B483875 : Blo 483789 483875 := bstep (se 1 (by rfl) ⟨362906, by rfl⟩ : syracuseStep 483875 = 725813) B725813
theorem B614947 : Blo 483789 614947 := bstep (se 1 (by rfl) ⟨461210, by rfl⟩ : syracuseStep 614947 = 922421) B922421
theorem B483891 : Blo 483789 483891 := bstep (se 1 (by rfl) ⟨362918, by rfl⟩ : syracuseStep 483891 = 725837) B725837
theorem B483907 : Blo 483789 483907 := bstep (se 1 (by rfl) ⟨362930, by rfl⟩ : syracuseStep 483907 = 725861) B725861
theorem B483923 : Blo 483789 483923 := bstep (se 1 (by rfl) ⟨362942, by rfl⟩ : syracuseStep 483923 = 725885) B725885
theorem B483939 : Blo 483789 483939 := bstep (se 1 (by rfl) ⟨362954, by rfl⟩ : syracuseStep 483939 = 725909) B725909
theorem B483955 : Blo 483789 483955 := bstep (se 1 (by rfl) ⟨362966, by rfl⟩ : syracuseStep 483955 = 725933) B725933
theorem B483971 : Blo 483789 483971 := bstep (se 1 (by rfl) ⟨362978, by rfl⟩ : syracuseStep 483971 = 725957) B725957
theorem B615043 : Blo 483789 615043 := bstep (se 1 (by rfl) ⟨461282, by rfl⟩ : syracuseStep 615043 = 922565) B922565
theorem B483987 : Blo 483789 483987 := bstep (se 1 (by rfl) ⟨362990, by rfl⟩ : syracuseStep 483987 = 725981) B725981
theorem B484003 : Blo 483789 484003 := bstep (se 1 (by rfl) ⟨363002, by rfl⟩ : syracuseStep 484003 = 726005) B726005
theorem B484019 : Blo 483789 484019 := bstep (se 1 (by rfl) ⟨363014, by rfl⟩ : syracuseStep 484019 = 726029) B726029
theorem B484035 : Blo 483789 484035 := bstep (se 1 (by rfl) ⟨363026, by rfl⟩ : syracuseStep 484035 = 726053) B726053
theorem B484051 : Blo 483789 484051 := bstep (se 1 (by rfl) ⟨363038, by rfl⟩ : syracuseStep 484051 = 726077) B726077
theorem B484067 : Blo 483789 484067 := bstep (se 1 (by rfl) ⟨363050, by rfl⟩ : syracuseStep 484067 = 726101) B726101
theorem B778979 : Blo 483789 778979 := bstep (se 1 (by rfl) ⟨584234, by rfl⟩ : syracuseStep 778979 = 1168469) B1168469
theorem B484083 : Blo 483789 484083 := bstep (se 1 (by rfl) ⟨363062, by rfl⟩ : syracuseStep 484083 = 726125) B726125
theorem B484099 : Blo 483789 484099 := bstep (se 1 (by rfl) ⟨363074, by rfl⟩ : syracuseStep 484099 = 726149) B726149
theorem B484115 : Blo 483789 484115 := bstep (se 1 (by rfl) ⟨363086, by rfl⟩ : syracuseStep 484115 = 726173) B726173
theorem B484131 : Blo 483789 484131 := bstep (se 1 (by rfl) ⟨363098, by rfl⟩ : syracuseStep 484131 = 726197) B726197
theorem B484147 : Blo 483789 484147 := bstep (se 1 (by rfl) ⟨363110, by rfl⟩ : syracuseStep 484147 = 726221) B726221
theorem B484163 : Blo 483789 484163 := bstep (se 1 (by rfl) ⟨363122, by rfl⟩ : syracuseStep 484163 = 726245) B726245
theorem B484179 : Blo 483789 484179 := bstep (se 1 (by rfl) ⟨363134, by rfl⟩ : syracuseStep 484179 = 726269) B726269
theorem B484195 : Blo 483789 484195 := bstep (se 1 (by rfl) ⟨363146, by rfl⟩ : syracuseStep 484195 = 726293) B726293
theorem B484211 : Blo 483789 484211 := bstep (se 1 (by rfl) ⟨363158, by rfl⟩ : syracuseStep 484211 = 726317) B726317
theorem B484227 : Blo 483789 484227 := bstep (se 1 (by rfl) ⟨363170, by rfl⟩ : syracuseStep 484227 = 726341) B726341
theorem B484243 : Blo 483789 484243 := bstep (se 1 (by rfl) ⟨363182, by rfl⟩ : syracuseStep 484243 = 726365) B726365
theorem B484259 : Blo 483789 484259 := bstep (se 1 (by rfl) ⟨363194, by rfl⟩ : syracuseStep 484259 = 726389) B726389
theorem B484275 : Blo 483789 484275 := bstep (se 1 (by rfl) ⟨363206, by rfl⟩ : syracuseStep 484275 = 726413) B726413
theorem B484291 : Blo 483789 484291 := bstep (se 1 (by rfl) ⟨363218, by rfl⟩ : syracuseStep 484291 = 726437) B726437
theorem B22438853 : Blo 483789 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B484307 : Blo 483789 484307 := bstep (se 1 (by rfl) ⟨363230, by rfl⟩ : syracuseStep 484307 = 726461) B726461
theorem B484323 : Blo 483789 484323 := bstep (se 1 (by rfl) ⟨363242, by rfl⟩ : syracuseStep 484323 = 726485) B726485
theorem B2778083 : Blo 483789 2778083 := bstep (se 1 (by rfl) ⟨2083562, by rfl⟩ : syracuseStep 2778083 = 4167125) B4167125
theorem B484339 : Blo 483789 484339 := bstep (se 1 (by rfl) ⟨363254, by rfl⟩ : syracuseStep 484339 = 726509) B726509
theorem B517123 : Blo 483789 517123 := bstep (se 1 (by rfl) ⟨387842, by rfl⟩ : syracuseStep 517123 = 775685) B775685
theorem B484355 : Blo 483789 484355 := bstep (se 1 (by rfl) ⟨363266, by rfl⟩ : syracuseStep 484355 = 726533) B726533
theorem B779267 : Blo 483789 779267 := bstep (se 1 (by rfl) ⟨584450, by rfl⟩ : syracuseStep 779267 = 1168901) B1168901
theorem B484371 : Blo 483789 484371 := bstep (se 1 (by rfl) ⟨363278, by rfl⟩ : syracuseStep 484371 = 726557) B726557
theorem B484387 : Blo 483789 484387 := bstep (se 1 (by rfl) ⟨363290, by rfl⟩ : syracuseStep 484387 = 726581) B726581
theorem B1041457 : Blo 483789 1041457 := bstep (se 2 (by rfl) ⟨390546, by rfl⟩ : syracuseStep 1041457 = 781093) B781093
theorem B484403 : Blo 483789 484403 := bstep (se 1 (by rfl) ⟨363302, by rfl⟩ : syracuseStep 484403 = 726605) B726605
theorem B484419 : Blo 483789 484419 := bstep (se 1 (by rfl) ⟨363314, by rfl⟩ : syracuseStep 484419 = 726629) B726629
theorem B484435 : Blo 483789 484435 := bstep (se 1 (by rfl) ⟨363326, by rfl⟩ : syracuseStep 484435 = 726653) B726653
theorem B484451 : Blo 483789 484451 := bstep (se 1 (by rfl) ⟨363338, by rfl⟩ : syracuseStep 484451 = 726677) B726677
theorem B484467 : Blo 483789 484467 := bstep (se 1 (by rfl) ⟨363350, by rfl⟩ : syracuseStep 484467 = 726701) B726701
theorem B615539 : Blo 483789 615539 := bstep (se 1 (by rfl) ⟨461654, by rfl⟩ : syracuseStep 615539 = 923309) B923309
theorem B484483 : Blo 483789 484483 := bstep (se 1 (by rfl) ⟨363362, by rfl⟩ : syracuseStep 484483 = 726725) B726725
theorem B2450573 : Blo 483789 2450573 := bstep (se 3 (by rfl) ⟨459482, by rfl⟩ : syracuseStep 2450573 = 918965) B918965
theorem B484499 : Blo 483789 484499 := bstep (se 1 (by rfl) ⟨363374, by rfl⟩ : syracuseStep 484499 = 726749) B726749
theorem B484515 : Blo 483789 484515 := bstep (se 1 (by rfl) ⟨363386, by rfl⟩ : syracuseStep 484515 = 726773) B726773
theorem B484531 : Blo 483789 484531 := bstep (se 1 (by rfl) ⟨363398, by rfl⟩ : syracuseStep 484531 = 726797) B726797
theorem B484547 : Blo 483789 484547 := bstep (se 1 (by rfl) ⟨363410, by rfl⟩ : syracuseStep 484547 = 726821) B726821
theorem B484563 : Blo 483789 484563 := bstep (se 1 (by rfl) ⟨363422, by rfl⟩ : syracuseStep 484563 = 726845) B726845
theorem B484579 : Blo 483789 484579 := bstep (se 1 (by rfl) ⟨363434, by rfl⟩ : syracuseStep 484579 = 726869) B726869
theorem B3106019 : Blo 483789 3106019 := bstep (se 1 (by rfl) ⟨2329514, by rfl⟩ : syracuseStep 3106019 = 4659029) B4659029
theorem B779491 : Blo 483789 779491 := bstep (se 1 (by rfl) ⟨584618, by rfl⟩ : syracuseStep 779491 = 1169237) B1169237
theorem B484595 : Blo 483789 484595 := bstep (se 1 (by rfl) ⟨363446, by rfl⟩ : syracuseStep 484595 = 726893) B726893
theorem B484611 : Blo 483789 484611 := bstep (se 1 (by rfl) ⟨363458, by rfl⟩ : syracuseStep 484611 = 726917) B726917
theorem B484627 : Blo 483789 484627 := bstep (se 1 (by rfl) ⟨363470, by rfl⟩ : syracuseStep 484627 = 726941) B726941
theorem B484643 : Blo 483789 484643 := bstep (se 1 (by rfl) ⟨363482, by rfl⟩ : syracuseStep 484643 = 726965) B726965
theorem B484659 : Blo 483789 484659 := bstep (se 1 (by rfl) ⟨363494, by rfl⟩ : syracuseStep 484659 = 726989) B726989
theorem B484675 : Blo 483789 484675 := bstep (se 1 (by rfl) ⟨363506, by rfl⟩ : syracuseStep 484675 = 727013) B727013
theorem B484691 : Blo 483789 484691 := bstep (se 1 (by rfl) ⟨363518, by rfl⟩ : syracuseStep 484691 = 727037) B727037
theorem B484707 : Blo 483789 484707 := bstep (se 1 (by rfl) ⟨363530, by rfl⟩ : syracuseStep 484707 = 727061) B727061
theorem B484723 : Blo 483789 484723 := bstep (se 1 (by rfl) ⟨363542, by rfl⟩ : syracuseStep 484723 = 727085) B727085
theorem B484739 : Blo 483789 484739 := bstep (se 1 (by rfl) ⟨363554, by rfl⟩ : syracuseStep 484739 = 727109) B727109
theorem B484755 : Blo 483789 484755 := bstep (se 1 (by rfl) ⟨363566, by rfl⟩ : syracuseStep 484755 = 727133) B727133
theorem B484771 : Blo 483789 484771 := bstep (se 1 (by rfl) ⟨363578, by rfl⟩ : syracuseStep 484771 = 727157) B727157
theorem B484787 : Blo 483789 484787 := bstep (se 1 (by rfl) ⟨363590, by rfl⟩ : syracuseStep 484787 = 727181) B727181
theorem B484803 : Blo 483789 484803 := bstep (se 1 (by rfl) ⟨363602, by rfl⟩ : syracuseStep 484803 = 727205) B727205
theorem B484819 : Blo 483789 484819 := bstep (se 1 (by rfl) ⟨363614, by rfl⟩ : syracuseStep 484819 = 727229) B727229
theorem B484835 : Blo 483789 484835 := bstep (se 1 (by rfl) ⟨363626, by rfl⟩ : syracuseStep 484835 = 727253) B727253
theorem B484851 : Blo 483789 484851 := bstep (se 1 (by rfl) ⟨363638, by rfl⟩ : syracuseStep 484851 = 727277) B727277
theorem B484867 : Blo 483789 484867 := bstep (se 1 (by rfl) ⟨363650, by rfl⟩ : syracuseStep 484867 = 727301) B727301
theorem B484883 : Blo 483789 484883 := bstep (se 1 (by rfl) ⟨363662, by rfl⟩ : syracuseStep 484883 = 727325) B727325
theorem B484899 : Blo 483789 484899 := bstep (se 1 (by rfl) ⟨363674, by rfl⟩ : syracuseStep 484899 = 727349) B727349
theorem B484915 : Blo 483789 484915 := bstep (se 1 (by rfl) ⟨363686, by rfl⟩ : syracuseStep 484915 = 727373) B727373
theorem B484931 : Blo 483789 484931 := bstep (se 1 (by rfl) ⟨363698, by rfl⟩ : syracuseStep 484931 = 727397) B727397
theorem B484947 : Blo 483789 484947 := bstep (se 1 (by rfl) ⟨363710, by rfl⟩ : syracuseStep 484947 = 727421) B727421
theorem B484963 : Blo 483789 484963 := bstep (se 1 (by rfl) ⟨363722, by rfl⟩ : syracuseStep 484963 = 727445) B727445
theorem B517747 : Blo 483789 517747 := bstep (se 1 (by rfl) ⟨388310, by rfl⟩ : syracuseStep 517747 = 776621) B776621
theorem B484979 : Blo 483789 484979 := bstep (se 1 (by rfl) ⟨363734, by rfl⟩ : syracuseStep 484979 = 727469) B727469
theorem B484995 : Blo 483789 484995 := bstep (se 1 (by rfl) ⟨363746, by rfl⟩ : syracuseStep 484995 = 727493) B727493
theorem B485011 : Blo 483789 485011 := bstep (se 1 (by rfl) ⟨363758, by rfl⟩ : syracuseStep 485011 = 727517) B727517
theorem B485027 : Blo 483789 485027 := bstep (se 1 (by rfl) ⟨363770, by rfl⟩ : syracuseStep 485027 = 727541) B727541
theorem B485043 : Blo 483789 485043 := bstep (se 1 (by rfl) ⟨363782, by rfl⟩ : syracuseStep 485043 = 727565) B727565
theorem B485059 : Blo 483789 485059 := bstep (se 1 (by rfl) ⟨363794, by rfl⟩ : syracuseStep 485059 = 727589) B727589
theorem B485075 : Blo 483789 485075 := bstep (se 1 (by rfl) ⟨363806, by rfl⟩ : syracuseStep 485075 = 727613) B727613
theorem B485091 : Blo 483789 485091 := bstep (se 1 (by rfl) ⟨363818, by rfl⟩ : syracuseStep 485091 = 727637) B727637
theorem B485107 : Blo 483789 485107 := bstep (se 1 (by rfl) ⟨363830, by rfl⟩ : syracuseStep 485107 = 727661) B727661
theorem B485123 : Blo 483789 485123 := bstep (se 1 (by rfl) ⟨363842, by rfl⟩ : syracuseStep 485123 = 727685) B727685
theorem B485139 : Blo 483789 485139 := bstep (se 1 (by rfl) ⟨363854, by rfl⟩ : syracuseStep 485139 = 727709) B727709
theorem B485155 : Blo 483789 485155 := bstep (se 1 (by rfl) ⟨363866, by rfl⟩ : syracuseStep 485155 = 727733) B727733
theorem B485171 : Blo 483789 485171 := bstep (se 1 (by rfl) ⟨363878, by rfl⟩ : syracuseStep 485171 = 727757) B727757
theorem B616243 : Blo 483789 616243 := bstep (se 1 (by rfl) ⟨462182, by rfl⟩ : syracuseStep 616243 = 924365) B924365
theorem B485187 : Blo 483789 485187 := bstep (se 1 (by rfl) ⟨363890, by rfl⟩ : syracuseStep 485187 = 727781) B727781
theorem B485203 : Blo 483789 485203 := bstep (se 1 (by rfl) ⟨363902, by rfl⟩ : syracuseStep 485203 = 727805) B727805
theorem B485219 : Blo 483789 485219 := bstep (se 1 (by rfl) ⟨363914, by rfl⟩ : syracuseStep 485219 = 727829) B727829
theorem B485235 : Blo 483789 485235 := bstep (se 1 (by rfl) ⟨363926, by rfl⟩ : syracuseStep 485235 = 727853) B727853
theorem B485251 : Blo 483789 485251 := bstep (se 1 (by rfl) ⟨363938, by rfl⟩ : syracuseStep 485251 = 727877) B727877
theorem B485267 : Blo 483789 485267 := bstep (se 1 (by rfl) ⟨363950, by rfl⟩ : syracuseStep 485267 = 727901) B727901
theorem B616339 : Blo 483789 616339 := bstep (se 1 (by rfl) ⟨462254, by rfl⟩ : syracuseStep 616339 = 924509) B924509
theorem B485283 : Blo 483789 485283 := bstep (se 1 (by rfl) ⟨363962, by rfl⟩ : syracuseStep 485283 = 727925) B727925
theorem B780209 : Blo 483789 780209 := bstep (se 2 (by rfl) ⟨292578, by rfl⟩ : syracuseStep 780209 = 585157) B585157
theorem B485299 : Blo 483789 485299 := bstep (se 1 (by rfl) ⟨363974, by rfl⟩ : syracuseStep 485299 = 727949) B727949
theorem B485315 : Blo 483789 485315 := bstep (se 1 (by rfl) ⟨363986, by rfl⟩ : syracuseStep 485315 = 727973) B727973
theorem B485331 : Blo 483789 485331 := bstep (se 1 (by rfl) ⟨363998, by rfl⟩ : syracuseStep 485331 = 727997) B727997
theorem B485347 : Blo 483789 485347 := bstep (se 1 (by rfl) ⟨364010, by rfl⟩ : syracuseStep 485347 = 728021) B728021
theorem B485363 : Blo 483789 485363 := bstep (se 1 (by rfl) ⟨364022, by rfl⟩ : syracuseStep 485363 = 728045) B728045
theorem B485379 : Blo 483789 485379 := bstep (se 1 (by rfl) ⟨364034, by rfl⟩ : syracuseStep 485379 = 728069) B728069
theorem B485395 : Blo 483789 485395 := bstep (se 1 (by rfl) ⟨364046, by rfl⟩ : syracuseStep 485395 = 728093) B728093
theorem B485411 : Blo 483789 485411 := bstep (se 1 (by rfl) ⟨364058, by rfl⟩ : syracuseStep 485411 = 728117) B728117
theorem B3237937 : Blo 483789 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B485427 : Blo 483789 485427 := bstep (se 1 (by rfl) ⟨364070, by rfl⟩ : syracuseStep 485427 = 728141) B728141
theorem B485443 : Blo 483789 485443 := bstep (se 1 (by rfl) ⟨364082, by rfl⟩ : syracuseStep 485443 = 728165) B728165
theorem B485459 : Blo 483789 485459 := bstep (se 1 (by rfl) ⟨364094, by rfl⟩ : syracuseStep 485459 = 728189) B728189
theorem B485475 : Blo 483789 485475 := bstep (se 1 (by rfl) ⟨364106, by rfl⟩ : syracuseStep 485475 = 728213) B728213
theorem B780401 : Blo 483789 780401 := bstep (se 2 (by rfl) ⟨292650, by rfl⟩ : syracuseStep 780401 = 585301) B585301
theorem B485491 : Blo 483789 485491 := bstep (se 1 (by rfl) ⟨364118, by rfl⟩ : syracuseStep 485491 = 728237) B728237
theorem B485507 : Blo 483789 485507 := bstep (se 1 (by rfl) ⟨364130, by rfl⟩ : syracuseStep 485507 = 728261) B728261
theorem B485523 : Blo 483789 485523 := bstep (se 1 (by rfl) ⟨364142, by rfl⟩ : syracuseStep 485523 = 728285) B728285
theorem B485539 : Blo 483789 485539 := bstep (se 1 (by rfl) ⟨364154, by rfl⟩ : syracuseStep 485539 = 728309) B728309
theorem B485555 : Blo 483789 485555 := bstep (se 1 (by rfl) ⟨364166, by rfl⟩ : syracuseStep 485555 = 728333) B728333
theorem B583859 : Blo 483789 583859 := bstep (se 1 (by rfl) ⟨437894, by rfl⟩ : syracuseStep 583859 = 875789) B875789
theorem B485571 : Blo 483789 485571 := bstep (se 1 (by rfl) ⟨364178, by rfl⟩ : syracuseStep 485571 = 728357) B728357
theorem B485587 : Blo 483789 485587 := bstep (se 1 (by rfl) ⟨364190, by rfl⟩ : syracuseStep 485587 = 728381) B728381
theorem B485603 : Blo 483789 485603 := bstep (se 1 (by rfl) ⟨364202, by rfl⟩ : syracuseStep 485603 = 728405) B728405
theorem B780529 : Blo 483789 780529 := bstep (se 2 (by rfl) ⟨292698, by rfl⟩ : syracuseStep 780529 = 585397) B585397
theorem B485619 : Blo 483789 485619 := bstep (se 1 (by rfl) ⟨364214, by rfl⟩ : syracuseStep 485619 = 728429) B728429
theorem B485635 : Blo 483789 485635 := bstep (se 1 (by rfl) ⟨364226, by rfl⟩ : syracuseStep 485635 = 728453) B728453
theorem B485651 : Blo 483789 485651 := bstep (se 1 (by rfl) ⟨364238, by rfl⟩ : syracuseStep 485651 = 728477) B728477
theorem B485667 : Blo 483789 485667 := bstep (se 1 (by rfl) ⟨364250, by rfl⟩ : syracuseStep 485667 = 728501) B728501
theorem B485683 : Blo 483789 485683 := bstep (se 1 (by rfl) ⟨364262, by rfl⟩ : syracuseStep 485683 = 728525) B728525
theorem B485699 : Blo 483789 485699 := bstep (se 1 (by rfl) ⟨364274, by rfl⟩ : syracuseStep 485699 = 728549) B728549
theorem B485715 : Blo 483789 485715 := bstep (se 1 (by rfl) ⟨364286, by rfl⟩ : syracuseStep 485715 = 728573) B728573
theorem B485731 : Blo 483789 485731 := bstep (se 1 (by rfl) ⟨364298, by rfl⟩ : syracuseStep 485731 = 728597) B728597
theorem B485747 : Blo 483789 485747 := bstep (se 1 (by rfl) ⟨364310, by rfl⟩ : syracuseStep 485747 = 728621) B728621
theorem B485763 : Blo 483789 485763 := bstep (se 1 (by rfl) ⟨364322, by rfl⟩ : syracuseStep 485763 = 728645) B728645
theorem B616835 : Blo 483789 616835 := bstep (se 1 (by rfl) ⟨462626, by rfl⟩ : syracuseStep 616835 = 925253) B925253
theorem B485779 : Blo 483789 485779 := bstep (se 1 (by rfl) ⟨364334, by rfl⟩ : syracuseStep 485779 = 728669) B728669
theorem B485795 : Blo 483789 485795 := bstep (se 1 (by rfl) ⟨364346, by rfl⟩ : syracuseStep 485795 = 728693) B728693
theorem B485811 : Blo 483789 485811 := bstep (se 1 (by rfl) ⟨364358, by rfl⟩ : syracuseStep 485811 = 728717) B728717
theorem B485827 : Blo 483789 485827 := bstep (se 1 (by rfl) ⟨364370, by rfl⟩ : syracuseStep 485827 = 728741) B728741
theorem B485843 : Blo 483789 485843 := bstep (se 1 (by rfl) ⟨364382, by rfl⟩ : syracuseStep 485843 = 728765) B728765
theorem B12413411 : Blo 483789 12413411 := bstep (se 1 (by rfl) ⟨9310058, by rfl⟩ : syracuseStep 12413411 = 18620117) B18620117
theorem B485859 : Blo 483789 485859 := bstep (se 1 (by rfl) ⟨364394, by rfl⟩ : syracuseStep 485859 = 728789) B728789
theorem B1010161 : Blo 483789 1010161 := bstep (se 2 (by rfl) ⟨378810, by rfl⟩ : syracuseStep 1010161 = 757621) B757621
theorem B485875 : Blo 483789 485875 := bstep (se 1 (by rfl) ⟨364406, by rfl⟩ : syracuseStep 485875 = 728813) B728813
theorem B485891 : Blo 483789 485891 := bstep (se 1 (by rfl) ⟨364418, by rfl⟩ : syracuseStep 485891 = 728837) B728837
theorem B2812429 : Blo 483789 2812429 := bstep (se 3 (by rfl) ⟨527330, by rfl⟩ : syracuseStep 2812429 = 1054661) B1054661
theorem B485907 : Blo 483789 485907 := bstep (se 1 (by rfl) ⟨364430, by rfl⟩ : syracuseStep 485907 = 728861) B728861
theorem B485923 : Blo 483789 485923 := bstep (se 1 (by rfl) ⟨364442, by rfl⟩ : syracuseStep 485923 = 728885) B728885
theorem B485939 : Blo 483789 485939 := bstep (se 1 (by rfl) ⟨364454, by rfl⟩ : syracuseStep 485939 = 728909) B728909
theorem B485955 : Blo 483789 485955 := bstep (se 1 (by rfl) ⟨364466, by rfl⟩ : syracuseStep 485955 = 728933) B728933
theorem B485971 : Blo 483789 485971 := bstep (se 1 (by rfl) ⟨364478, by rfl⟩ : syracuseStep 485971 = 728957) B728957
theorem B485987 : Blo 483789 485987 := bstep (se 1 (by rfl) ⟨364490, by rfl⟩ : syracuseStep 485987 = 728981) B728981
theorem B486003 : Blo 483789 486003 := bstep (se 1 (by rfl) ⟨364502, by rfl⟩ : syracuseStep 486003 = 729005) B729005
theorem B486019 : Blo 483789 486019 := bstep (se 1 (by rfl) ⟨364514, by rfl⟩ : syracuseStep 486019 = 729029) B729029
theorem B486035 : Blo 483789 486035 := bstep (se 1 (by rfl) ⟨364526, by rfl⟩ : syracuseStep 486035 = 729053) B729053
theorem B486051 : Blo 483789 486051 := bstep (se 1 (by rfl) ⟨364538, by rfl⟩ : syracuseStep 486051 = 729077) B729077
theorem B486067 : Blo 483789 486067 := bstep (se 1 (by rfl) ⟨364550, by rfl⟩ : syracuseStep 486067 = 729101) B729101
theorem B486083 : Blo 483789 486083 := bstep (se 1 (by rfl) ⟨364562, by rfl⟩ : syracuseStep 486083 = 729125) B729125
theorem B486099 : Blo 483789 486099 := bstep (se 1 (by rfl) ⟨364574, by rfl⟩ : syracuseStep 486099 = 729149) B729149
theorem B486115 : Blo 483789 486115 := bstep (se 1 (by rfl) ⟨364586, by rfl⟩ : syracuseStep 486115 = 729173) B729173
theorem B486131 : Blo 483789 486131 := bstep (se 1 (by rfl) ⟨364598, by rfl⟩ : syracuseStep 486131 = 729197) B729197
theorem B486147 : Blo 483789 486147 := bstep (se 1 (by rfl) ⟨364610, by rfl⟩ : syracuseStep 486147 = 729221) B729221
theorem B486163 : Blo 483789 486163 := bstep (se 1 (by rfl) ⟨364622, by rfl⟩ : syracuseStep 486163 = 729245) B729245
theorem B486179 : Blo 483789 486179 := bstep (se 1 (by rfl) ⟨364634, by rfl⟩ : syracuseStep 486179 = 729269) B729269
theorem B486195 : Blo 483789 486195 := bstep (se 1 (by rfl) ⟨364646, by rfl⟩ : syracuseStep 486195 = 729293) B729293
theorem B486211 : Blo 483789 486211 := bstep (se 1 (by rfl) ⟨364658, by rfl⟩ : syracuseStep 486211 = 729317) B729317
theorem B486227 : Blo 483789 486227 := bstep (se 1 (by rfl) ⟨364670, by rfl⟩ : syracuseStep 486227 = 729341) B729341
theorem B486243 : Blo 483789 486243 := bstep (se 1 (by rfl) ⟨364682, by rfl⟩ : syracuseStep 486243 = 729365) B729365
theorem B781169 : Blo 483789 781169 := bstep (se 2 (by rfl) ⟨292938, by rfl⟩ : syracuseStep 781169 = 585877) B585877
theorem B486259 : Blo 483789 486259 := bstep (se 1 (by rfl) ⟨364694, by rfl⟩ : syracuseStep 486259 = 729389) B729389
theorem B486275 : Blo 483789 486275 := bstep (se 1 (by rfl) ⟨364706, by rfl⟩ : syracuseStep 486275 = 729413) B729413
theorem B486291 : Blo 483789 486291 := bstep (se 1 (by rfl) ⟨364718, by rfl⟩ : syracuseStep 486291 = 729437) B729437
theorem B486307 : Blo 483789 486307 := bstep (se 1 (by rfl) ⟨364730, by rfl⟩ : syracuseStep 486307 = 729461) B729461
theorem B486323 : Blo 483789 486323 := bstep (se 1 (by rfl) ⟨364742, by rfl⟩ : syracuseStep 486323 = 729485) B729485
theorem B486339 : Blo 483789 486339 := bstep (se 1 (by rfl) ⟨364754, by rfl⟩ : syracuseStep 486339 = 729509) B729509
theorem B1633229 : Blo 483789 1633229 := bstep (se 3 (by rfl) ⟨306230, by rfl⟩ : syracuseStep 1633229 = 612461) B612461
theorem B486355 : Blo 483789 486355 := bstep (se 1 (by rfl) ⟨364766, by rfl⟩ : syracuseStep 486355 = 729533) B729533
theorem B486371 : Blo 483789 486371 := bstep (se 1 (by rfl) ⟨364778, by rfl⟩ : syracuseStep 486371 = 729557) B729557
theorem B486387 : Blo 483789 486387 := bstep (se 1 (by rfl) ⟨364790, by rfl⟩ : syracuseStep 486387 = 729581) B729581
theorem B1633283 : Blo 483789 1633283 := bstep (se 1 (by rfl) ⟨1224962, by rfl⟩ : syracuseStep 1633283 = 2449925) B2449925
theorem B486403 : Blo 483789 486403 := bstep (se 1 (by rfl) ⟨364802, by rfl⟩ : syracuseStep 486403 = 729605) B729605
theorem B486419 : Blo 483789 486419 := bstep (se 1 (by rfl) ⟨364814, by rfl⟩ : syracuseStep 486419 = 729629) B729629
theorem B486435 : Blo 483789 486435 := bstep (se 1 (by rfl) ⟨364826, by rfl⟩ : syracuseStep 486435 = 729653) B729653
theorem B486451 : Blo 483789 486451 := bstep (se 1 (by rfl) ⟨364838, by rfl⟩ : syracuseStep 486451 = 729677) B729677
theorem B486467 : Blo 483789 486467 := bstep (se 1 (by rfl) ⟨364850, by rfl⟩ : syracuseStep 486467 = 729701) B729701
theorem B486483 : Blo 483789 486483 := bstep (se 1 (by rfl) ⟨364862, by rfl⟩ : syracuseStep 486483 = 729725) B729725
theorem B486499 : Blo 483789 486499 := bstep (se 1 (by rfl) ⟨364874, by rfl⟩ : syracuseStep 486499 = 729749) B729749
theorem B486515 : Blo 483789 486515 := bstep (se 1 (by rfl) ⟨364886, by rfl⟩ : syracuseStep 486515 = 729773) B729773
theorem B486531 : Blo 483789 486531 := bstep (se 1 (by rfl) ⟨364898, by rfl⟩ : syracuseStep 486531 = 729797) B729797
theorem B486547 : Blo 483789 486547 := bstep (se 1 (by rfl) ⟨364910, by rfl⟩ : syracuseStep 486547 = 729821) B729821
theorem B486563 : Blo 483789 486563 := bstep (se 1 (by rfl) ⟨364922, by rfl⟩ : syracuseStep 486563 = 729845) B729845
theorem B486579 : Blo 483789 486579 := bstep (se 1 (by rfl) ⟨364934, by rfl⟩ : syracuseStep 486579 = 729869) B729869
theorem B486595 : Blo 483789 486595 := bstep (se 1 (by rfl) ⟨364946, by rfl⟩ : syracuseStep 486595 = 729893) B729893
theorem B2944205 : Blo 483789 2944205 := bstep (se 3 (by rfl) ⟨552038, by rfl⟩ : syracuseStep 2944205 = 1104077) B1104077
theorem B486611 : Blo 483789 486611 := bstep (se 1 (by rfl) ⟨364958, by rfl⟩ : syracuseStep 486611 = 729917) B729917
theorem B486627 : Blo 483789 486627 := bstep (se 1 (by rfl) ⟨364970, by rfl⟩ : syracuseStep 486627 = 729941) B729941
theorem B486643 : Blo 483789 486643 := bstep (se 1 (by rfl) ⟨364982, by rfl⟩ : syracuseStep 486643 = 729965) B729965
theorem B486659 : Blo 483789 486659 := bstep (se 1 (by rfl) ⟨364994, by rfl⟩ : syracuseStep 486659 = 729989) B729989
theorem B1633553 : Blo 483789 1633553 := bstep (se 2 (by rfl) ⟨612582, by rfl⟩ : syracuseStep 1633553 = 1225165) B1225165
theorem B486675 : Blo 483789 486675 := bstep (se 1 (by rfl) ⟨365006, by rfl⟩ : syracuseStep 486675 = 730013) B730013
theorem B486691 : Blo 483789 486691 := bstep (se 1 (by rfl) ⟨365018, by rfl⟩ : syracuseStep 486691 = 730037) B730037
theorem B1109297 : Blo 483789 1109297 := bstep (se 2 (by rfl) ⟨415986, by rfl⟩ : syracuseStep 1109297 = 831973) B831973
theorem B486707 : Blo 483789 486707 := bstep (se 1 (by rfl) ⟨365030, by rfl⟩ : syracuseStep 486707 = 730061) B730061
theorem B486723 : Blo 483789 486723 := bstep (se 1 (by rfl) ⟨365042, by rfl⟩ : syracuseStep 486723 = 730085) B730085
theorem B486739 : Blo 483789 486739 := bstep (se 1 (by rfl) ⟨365054, by rfl⟩ : syracuseStep 486739 = 730109) B730109
theorem B486755 : Blo 483789 486755 := bstep (se 1 (by rfl) ⟨365066, by rfl⟩ : syracuseStep 486755 = 730133) B730133
theorem B486771 : Blo 483789 486771 := bstep (se 1 (by rfl) ⟨365078, by rfl⟩ : syracuseStep 486771 = 730157) B730157
theorem B486787 : Blo 483789 486787 := bstep (se 1 (by rfl) ⟨365090, by rfl⟩ : syracuseStep 486787 = 730181) B730181
theorem B486803 : Blo 483789 486803 := bstep (se 1 (by rfl) ⟨365102, by rfl⟩ : syracuseStep 486803 = 730205) B730205
theorem B486819 : Blo 483789 486819 := bstep (se 1 (by rfl) ⟨365114, by rfl⟩ : syracuseStep 486819 = 730229) B730229
theorem B486835 : Blo 483789 486835 := bstep (se 1 (by rfl) ⟨365126, by rfl⟩ : syracuseStep 486835 = 730253) B730253
theorem B5533109 : Blo 483789 5533109 := bstep (se 5 (by rfl) ⟨259364, by rfl⟩ : syracuseStep 5533109 = 518729) B518729
theorem B486851 : Blo 483789 486851 := bstep (se 1 (by rfl) ⟨365138, by rfl⟩ : syracuseStep 486851 = 730277) B730277
theorem B519635 : Blo 483789 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B486867 : Blo 483789 486867 := bstep (se 1 (by rfl) ⟨365150, by rfl⟩ : syracuseStep 486867 = 730301) B730301
theorem B486883 : Blo 483789 486883 := bstep (se 1 (by rfl) ⟨365162, by rfl⟩ : syracuseStep 486883 = 730325) B730325
theorem B486899 : Blo 483789 486899 := bstep (se 1 (by rfl) ⟨365174, by rfl⟩ : syracuseStep 486899 = 730349) B730349
theorem B486915 : Blo 483789 486915 := bstep (se 1 (by rfl) ⟨365186, by rfl⟩ : syracuseStep 486915 = 730373) B730373
theorem B486931 : Blo 483789 486931 := bstep (se 1 (by rfl) ⟨365198, by rfl⟩ : syracuseStep 486931 = 730397) B730397
theorem B486947 : Blo 483789 486947 := bstep (se 1 (by rfl) ⟨365210, by rfl⟩ : syracuseStep 486947 = 730421) B730421
theorem B486963 : Blo 483789 486963 := bstep (se 1 (by rfl) ⟨365222, by rfl⟩ : syracuseStep 486963 = 730445) B730445
theorem B486979 : Blo 483789 486979 := bstep (se 1 (by rfl) ⟨365234, by rfl⟩ : syracuseStep 486979 = 730469) B730469
theorem B486995 : Blo 483789 486995 := bstep (se 1 (by rfl) ⟨365246, by rfl⟩ : syracuseStep 486995 = 730493) B730493
theorem B487011 : Blo 483789 487011 := bstep (se 1 (by rfl) ⟨365258, by rfl⟩ : syracuseStep 487011 = 730517) B730517
theorem B487027 : Blo 483789 487027 := bstep (se 1 (by rfl) ⟨365270, by rfl⟩ : syracuseStep 487027 = 730541) B730541
theorem B487043 : Blo 483789 487043 := bstep (se 1 (by rfl) ⟨365282, by rfl⟩ : syracuseStep 487043 = 730565) B730565
theorem B487059 : Blo 483789 487059 := bstep (se 1 (by rfl) ⟨365294, by rfl⟩ : syracuseStep 487059 = 730589) B730589
theorem B487075 : Blo 483789 487075 := bstep (se 1 (by rfl) ⟨365306, by rfl⟩ : syracuseStep 487075 = 730613) B730613
theorem B487091 : Blo 483789 487091 := bstep (se 1 (by rfl) ⟨365318, by rfl⟩ : syracuseStep 487091 = 730637) B730637
theorem B749251 : Blo 483789 749251 := bstep (se 1 (by rfl) ⟨561938, by rfl⟩ : syracuseStep 749251 = 1123877) B1123877
theorem B487107 : Blo 483789 487107 := bstep (se 1 (by rfl) ⟨365330, by rfl⟩ : syracuseStep 487107 = 730661) B730661
theorem B487123 : Blo 483789 487123 := bstep (se 1 (by rfl) ⟨365342, by rfl⟩ : syracuseStep 487123 = 730685) B730685
theorem B487139 : Blo 483789 487139 := bstep (se 1 (by rfl) ⟨365354, by rfl⟩ : syracuseStep 487139 = 730709) B730709
theorem B487155 : Blo 483789 487155 := bstep (se 1 (by rfl) ⟨365366, by rfl⟩ : syracuseStep 487155 = 730733) B730733
theorem B487171 : Blo 483789 487171 := bstep (se 1 (by rfl) ⟨365378, by rfl⟩ : syracuseStep 487171 = 730757) B730757
theorem B487187 : Blo 483789 487187 := bstep (se 1 (by rfl) ⟨365390, by rfl⟩ : syracuseStep 487187 = 730781) B730781
theorem B487203 : Blo 483789 487203 := bstep (se 1 (by rfl) ⟨365402, by rfl⟩ : syracuseStep 487203 = 730805) B730805
theorem B1634093 : Blo 483789 1634093 := bstep (se 3 (by rfl) ⟨306392, by rfl⟩ : syracuseStep 1634093 = 612785) B612785
theorem B487219 : Blo 483789 487219 := bstep (se 1 (by rfl) ⟨365414, by rfl⟩ : syracuseStep 487219 = 730829) B730829
theorem B7499573 : Blo 483789 7499573 := bstep (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) B703085
theorem B487235 : Blo 483789 487235 := bstep (se 1 (by rfl) ⟨365426, by rfl⟩ : syracuseStep 487235 = 730853) B730853
theorem B487251 : Blo 483789 487251 := bstep (se 1 (by rfl) ⟨365438, by rfl⟩ : syracuseStep 487251 = 730877) B730877
theorem B1634147 : Blo 483789 1634147 := bstep (se 1 (by rfl) ⟨1225610, by rfl⟩ : syracuseStep 1634147 = 2451221) B2451221
theorem B487267 : Blo 483789 487267 := bstep (se 1 (by rfl) ⟨365450, by rfl⟩ : syracuseStep 487267 = 730901) B730901
theorem B487283 : Blo 483789 487283 := bstep (se 1 (by rfl) ⟨365462, by rfl⟩ : syracuseStep 487283 = 730925) B730925
theorem B487299 : Blo 483789 487299 := bstep (se 1 (by rfl) ⟨365474, by rfl⟩ : syracuseStep 487299 = 730949) B730949
theorem B487315 : Blo 483789 487315 := bstep (se 1 (by rfl) ⟨365486, by rfl⟩ : syracuseStep 487315 = 730973) B730973
theorem B487331 : Blo 483789 487331 := bstep (se 1 (by rfl) ⟨365498, by rfl⟩ : syracuseStep 487331 = 730997) B730997
theorem B487347 : Blo 483789 487347 := bstep (se 1 (by rfl) ⟨365510, by rfl⟩ : syracuseStep 487347 = 731021) B731021
theorem B487363 : Blo 483789 487363 := bstep (se 1 (by rfl) ⟨365522, by rfl⟩ : syracuseStep 487363 = 731045) B731045
theorem B487379 : Blo 483789 487379 := bstep (se 1 (by rfl) ⟨365534, by rfl⟩ : syracuseStep 487379 = 731069) B731069
theorem B487395 : Blo 483789 487395 := bstep (se 1 (by rfl) ⟨365546, by rfl⟩ : syracuseStep 487395 = 731093) B731093
theorem B10547171 : Blo 483789 10547171 := bstep (se 1 (by rfl) ⟨7910378, by rfl⟩ : syracuseStep 10547171 = 15820757) B15820757
theorem B2453489 : Blo 483789 2453489 := bstep (se 2 (by rfl) ⟨920058, by rfl⟩ : syracuseStep 2453489 = 1840117) B1840117
theorem B487411 : Blo 483789 487411 := bstep (se 1 (by rfl) ⟨365558, by rfl⟩ : syracuseStep 487411 = 731117) B731117
theorem B487427 : Blo 483789 487427 := bstep (se 1 (by rfl) ⟨365570, by rfl⟩ : syracuseStep 487427 = 731141) B731141
theorem B487443 : Blo 483789 487443 := bstep (se 1 (by rfl) ⟨365582, by rfl⟩ : syracuseStep 487443 = 731165) B731165
theorem B487459 : Blo 483789 487459 := bstep (se 1 (by rfl) ⟨365594, by rfl⟩ : syracuseStep 487459 = 731189) B731189
theorem B487475 : Blo 483789 487475 := bstep (se 1 (by rfl) ⟨365606, by rfl⟩ : syracuseStep 487475 = 731213) B731213
theorem B487491 : Blo 483789 487491 := bstep (se 1 (by rfl) ⟨365618, by rfl⟩ : syracuseStep 487491 = 731237) B731237
theorem B487507 : Blo 483789 487507 := bstep (se 1 (by rfl) ⟨365630, by rfl⟩ : syracuseStep 487507 = 731261) B731261
theorem B487523 : Blo 483789 487523 := bstep (se 1 (by rfl) ⟨365642, by rfl⟩ : syracuseStep 487523 = 731285) B731285
theorem B1634417 : Blo 483789 1634417 := bstep (se 2 (by rfl) ⟨612906, by rfl⟩ : syracuseStep 1634417 = 1225813) B1225813
theorem B487539 : Blo 483789 487539 := bstep (se 1 (by rfl) ⟨365654, by rfl⟩ : syracuseStep 487539 = 731309) B731309
theorem B487555 : Blo 483789 487555 := bstep (se 1 (by rfl) ⟨365666, by rfl⟩ : syracuseStep 487555 = 731333) B731333
theorem B487571 : Blo 483789 487571 := bstep (se 1 (by rfl) ⟨365678, by rfl⟩ : syracuseStep 487571 = 731357) B731357
theorem B487587 : Blo 483789 487587 := bstep (se 1 (by rfl) ⟨365690, by rfl⟩ : syracuseStep 487587 = 731381) B731381
theorem B487603 : Blo 483789 487603 := bstep (se 1 (by rfl) ⟨365702, by rfl⟩ : syracuseStep 487603 = 731405) B731405
theorem B487619 : Blo 483789 487619 := bstep (se 1 (by rfl) ⟨365714, by rfl⟩ : syracuseStep 487619 = 731429) B731429
theorem B487635 : Blo 483789 487635 := bstep (se 1 (by rfl) ⟨365726, by rfl⟩ : syracuseStep 487635 = 731453) B731453
theorem B487651 : Blo 483789 487651 := bstep (se 1 (by rfl) ⟨365738, by rfl⟩ : syracuseStep 487651 = 731477) B731477
theorem B487667 : Blo 483789 487667 := bstep (se 1 (by rfl) ⟨365750, by rfl⟩ : syracuseStep 487667 = 731501) B731501
theorem B487683 : Blo 483789 487683 := bstep (se 1 (by rfl) ⟨365762, by rfl⟩ : syracuseStep 487683 = 731525) B731525
theorem B487699 : Blo 483789 487699 := bstep (se 1 (by rfl) ⟨365774, by rfl⟩ : syracuseStep 487699 = 731549) B731549
theorem B487715 : Blo 483789 487715 := bstep (se 1 (by rfl) ⟨365786, by rfl⟩ : syracuseStep 487715 = 731573) B731573
theorem B487731 : Blo 483789 487731 := bstep (se 1 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 487731 = 731597) B731597
theorem B487747 : Blo 483789 487747 := bstep (se 1 (by rfl) ⟨365810, by rfl⟩ : syracuseStep 487747 = 731621) B731621
theorem B487763 : Blo 483789 487763 := bstep (se 1 (by rfl) ⟨365822, by rfl⟩ : syracuseStep 487763 = 731645) B731645
theorem B487779 : Blo 483789 487779 := bstep (se 1 (by rfl) ⟨365834, by rfl⟩ : syracuseStep 487779 = 731669) B731669
theorem B1634957 : Blo 483789 1634957 := bstep (se 3 (by rfl) ⟨306554, by rfl⟩ : syracuseStep 1634957 = 613109) B613109
theorem B1635011 : Blo 483789 1635011 := bstep (se 1 (by rfl) ⟨1226258, by rfl⟩ : syracuseStep 1635011 = 2452517) B2452517
theorem B1471277 : Blo 483789 1471277 := bstep (se 3 (by rfl) ⟨275864, by rfl⟩ : syracuseStep 1471277 = 551729) B551729
theorem B5206837 : Blo 483789 5206837 := bstep (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) B488141
theorem B1635281 : Blo 483789 1635281 := bstep (se 2 (by rfl) ⟨613230, by rfl⟩ : syracuseStep 1635281 = 1226461) B1226461
theorem B1668323 : Blo 483789 1668323 := bstep (se 1 (by rfl) ⟨1251242, by rfl⟩ : syracuseStep 1668323 = 2502485) B2502485
theorem B816419 : Blo 483789 816419 := bstep (se 1 (by rfl) ⟨612314, by rfl⟩ : syracuseStep 816419 = 1224629) B1224629
theorem B816547 : Blo 483789 816547 := bstep (se 1 (by rfl) ⟨612410, by rfl⟩ : syracuseStep 816547 = 1224821) B1224821
theorem B2454947 : Blo 483789 2454947 := bstep (se 1 (by rfl) ⟨1841210, by rfl⟩ : syracuseStep 2454947 = 3682421) B3682421
theorem B1635821 : Blo 483789 1635821 := bstep (se 3 (by rfl) ⟨306716, by rfl⟩ : syracuseStep 1635821 = 613433) B613433
theorem B1635875 : Blo 483789 1635875 := bstep (se 1 (by rfl) ⟨1226906, by rfl⟩ : syracuseStep 1635875 = 2453813) B2453813
theorem B816689 : Blo 483789 816689 := bstep (se 2 (by rfl) ⟨306258, by rfl⟩ : syracuseStep 816689 = 612517) B612517
theorem B3503729 : Blo 483789 3503729 := bstep (se 2 (by rfl) ⟨1313898, by rfl⟩ : syracuseStep 3503729 = 2627797) B2627797
theorem B816817 : Blo 483789 816817 := bstep (se 2 (by rfl) ⟨306306, by rfl⟩ : syracuseStep 816817 = 612613) B612613
theorem B816851 : Blo 483789 816851 := bstep (se 1 (by rfl) ⟨612638, by rfl⟩ : syracuseStep 816851 = 1225277) B1225277
theorem B1636145 : Blo 483789 1636145 := bstep (se 2 (by rfl) ⟨613554, by rfl⟩ : syracuseStep 1636145 = 1227109) B1227109
theorem B816979 : Blo 483789 816979 := bstep (se 1 (by rfl) ⟨612734, by rfl⟩ : syracuseStep 816979 = 1225469) B1225469
theorem B817121 : Blo 483789 817121 := bstep (se 2 (by rfl) ⟨306420, by rfl⟩ : syracuseStep 817121 = 612841) B612841
theorem B1767473 : Blo 483789 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B817249 : Blo 483789 817249 := bstep (se 2 (by rfl) ⟨306468, by rfl⟩ : syracuseStep 817249 = 612937) B612937
theorem B817283 : Blo 483789 817283 := bstep (se 1 (by rfl) ⟨612962, by rfl⟩ : syracuseStep 817283 = 1225925) B1225925
theorem B1308817 : Blo 483789 1308817 := bstep (se 2 (by rfl) ⟨490806, by rfl⟩ : syracuseStep 1308817 = 981613) B981613
theorem B2455757 : Blo 483789 2455757 := bstep (se 3 (by rfl) ⟨460454, by rfl⟩ : syracuseStep 2455757 = 920909) B920909
theorem B817411 : Blo 483789 817411 := bstep (se 1 (by rfl) ⟨613058, by rfl⟩ : syracuseStep 817411 = 1226117) B1226117
theorem B555283 : Blo 483789 555283 := bstep (se 1 (by rfl) ⟨416462, by rfl⟩ : syracuseStep 555283 = 832925) B832925
theorem B1636685 : Blo 483789 1636685 := bstep (se 3 (by rfl) ⟨306878, by rfl⟩ : syracuseStep 1636685 = 613757) B613757
theorem B1571185 : Blo 483789 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B1636739 : Blo 483789 1636739 := bstep (se 1 (by rfl) ⟨1227554, by rfl⟩ : syracuseStep 1636739 = 2455109) B2455109
theorem B6977933 : Blo 483789 6977933 := bstep (se 3 (by rfl) ⟨1308362, by rfl⟩ : syracuseStep 6977933 = 2616725) B2616725
theorem B817553 : Blo 483789 817553 := bstep (se 2 (by rfl) ⟨306582, by rfl⟩ : syracuseStep 817553 = 613165) B613165
theorem B3504653 : Blo 483789 3504653 := bstep (se 3 (by rfl) ⟨657122, by rfl⟩ : syracuseStep 3504653 = 1314245) B1314245
theorem B817681 : Blo 483789 817681 := bstep (se 2 (by rfl) ⟨306630, by rfl⟩ : syracuseStep 817681 = 613261) B613261
theorem B817715 : Blo 483789 817715 := bstep (se 1 (by rfl) ⟨613286, by rfl⟩ : syracuseStep 817715 = 1226573) B1226573
theorem B1637009 : Blo 483789 1637009 := bstep (se 2 (by rfl) ⟨613878, by rfl⟩ : syracuseStep 1637009 = 1227757) B1227757
theorem B817843 : Blo 483789 817843 := bstep (se 1 (by rfl) ⟨613382, by rfl⟩ : syracuseStep 817843 = 1226765) B1226765
theorem B817985 : Blo 483789 817985 := bstep (se 2 (by rfl) ⟨306744, by rfl⟩ : syracuseStep 817985 = 613489) B613489
theorem B818113 : Blo 483789 818113 := bstep (se 2 (by rfl) ⟨306792, by rfl⟩ : syracuseStep 818113 = 613585) B613585
theorem B818147 : Blo 483789 818147 := bstep (se 1 (by rfl) ⟨613610, by rfl⟩ : syracuseStep 818147 = 1227221) B1227221
theorem B654355 : Blo 483789 654355 := bstep (se 1 (by rfl) ⟨490766, by rfl⟩ : syracuseStep 654355 = 981533) B981533
theorem B818275 : Blo 483789 818275 := bstep (se 1 (by rfl) ⟨613706, by rfl⟩ : syracuseStep 818275 = 1227413) B1227413
theorem B1637549 : Blo 483789 1637549 := bstep (se 3 (by rfl) ⟨307040, by rfl⟩ : syracuseStep 1637549 = 614081) B614081
theorem B1637603 : Blo 483789 1637603 := bstep (se 1 (by rfl) ⟨1228202, by rfl⟩ : syracuseStep 1637603 = 2456405) B2456405
theorem B818417 : Blo 483789 818417 := bstep (se 2 (by rfl) ⟨306906, by rfl⟩ : syracuseStep 818417 = 613813) B613813
theorem B4423025 : Blo 483789 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B818545 : Blo 483789 818545 := bstep (se 2 (by rfl) ⟨306954, by rfl⟩ : syracuseStep 818545 = 613909) B613909
theorem B818579 : Blo 483789 818579 := bstep (se 1 (by rfl) ⟨613934, by rfl⟩ : syracuseStep 818579 = 1227869) B1227869
theorem B1244593 : Blo 483789 1244593 := bstep (se 2 (by rfl) ⟨466722, by rfl⟩ : syracuseStep 1244593 = 933445) B933445
theorem B654787 : Blo 483789 654787 := bstep (se 1 (by rfl) ⟨491090, by rfl⟩ : syracuseStep 654787 = 982181) B982181
theorem B1637873 : Blo 483789 1637873 := bstep (se 2 (by rfl) ⟨614202, by rfl⟩ : syracuseStep 1637873 = 1228405) B1228405
theorem B818707 : Blo 483789 818707 := bstep (se 1 (by rfl) ⟨614030, by rfl⟩ : syracuseStep 818707 = 1228061) B1228061
theorem B491123 : Blo 483789 491123 := bstep (se 1 (by rfl) ⟨368342, by rfl⟩ : syracuseStep 491123 = 736685) B736685
theorem B818849 : Blo 483789 818849 := bstep (se 2 (by rfl) ⟨307068, by rfl⟩ : syracuseStep 818849 = 614137) B614137
theorem B1474243 : Blo 483789 1474243 := bstep (se 1 (by rfl) ⟨1105682, by rfl⟩ : syracuseStep 1474243 = 2211365) B2211365
theorem B818977 : Blo 483789 818977 := bstep (se 2 (by rfl) ⟨307116, by rfl⟩ : syracuseStep 818977 = 614233) B614233
theorem B819011 : Blo 483789 819011 := bstep (se 1 (by rfl) ⟨614258, by rfl⟩ : syracuseStep 819011 = 1228517) B1228517
theorem B884611 : Blo 483789 884611 := bstep (se 1 (by rfl) ⟨663458, by rfl⟩ : syracuseStep 884611 = 1326917) B1326917
theorem B819139 : Blo 483789 819139 := bstep (se 1 (by rfl) ⟨614354, by rfl⟩ : syracuseStep 819139 = 1228709) B1228709
theorem B1048627 : Blo 483789 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B655447 : Blo 483789 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B8978525 : Blo 483789 8978525 := bstep (se 3 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 8978525 = 3366947) B3366947
theorem B17268997 : Blo 483789 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B819659 : Blo 483789 819659 := bstep (se 1 (by rfl) ⟨614744, by rfl⟩ : syracuseStep 819659 = 1229489) B1229489
theorem B2458187 : Blo 483789 2458187 := bstep (se 1 (by rfl) ⟨1843640, by rfl⟩ : syracuseStep 2458187 = 3687281) B3687281
theorem B819787 : Blo 483789 819787 := bstep (se 1 (by rfl) ⟨614840, by rfl⟩ : syracuseStep 819787 = 1229681) B1229681
theorem B1081931 : Blo 483789 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B1639115 : Blo 483789 1639115 := bstep (se 1 (by rfl) ⟨1229336, by rfl⟩ : syracuseStep 1639115 = 2458673) B2458673
theorem B819929 : Blo 483789 819929 := bstep (se 2 (by rfl) ⟨307473, by rfl⟩ : syracuseStep 819929 = 614947) B614947
theorem B6980357 : Blo 483789 6980357 := bstep (se 4 (by rfl) ⟨654408, by rfl⟩ : syracuseStep 6980357 = 1308817) B1308817
theorem B820057 : Blo 483789 820057 := bstep (se 2 (by rfl) ⟨307521, by rfl⟩ : syracuseStep 820057 = 615043) B615043
theorem B1639385 : Blo 483789 1639385 := bstep (se 2 (by rfl) ⟨614769, by rfl⟩ : syracuseStep 1639385 = 1229539) B1229539
theorem B918859 : Blo 483789 918859 := bstep (se 1 (by rfl) ⟨689144, by rfl⟩ : syracuseStep 918859 = 1378289) B1378289
theorem B918935 : Blo 483789 918935 := bstep (se 1 (by rfl) ⟨689201, by rfl⟩ : syracuseStep 918935 = 1378403) B1378403
theorem B820631 : Blo 483789 820631 := bstep (se 1 (by rfl) ⟨615473, by rfl⟩ : syracuseStep 820631 = 1230947) B1230947
theorem B1312193 : Blo 483789 1312193 := bstep (se 2 (by rfl) ⟨492072, by rfl⟩ : syracuseStep 1312193 = 984145) B984145
theorem B820759 : Blo 483789 820759 := bstep (se 1 (by rfl) ⟨615569, by rfl⟩ : syracuseStep 820759 = 1231139) B1231139
theorem B984727 : Blo 483789 984727 := bstep (se 1 (by rfl) ⟨738545, by rfl⟩ : syracuseStep 984727 = 1477091) B1477091
theorem B1640087 : Blo 483789 1640087 := bstep (se 1 (by rfl) ⟨1230065, by rfl⟩ : syracuseStep 1640087 = 2460131) B2460131
theorem B526219 : Blo 483789 526219 := bstep (se 1 (by rfl) ⟨394664, by rfl⟩ : syracuseStep 526219 = 789329) B789329
theorem B493547 : Blo 483789 493547 := bstep (se 1 (by rfl) ⟨370160, by rfl⟩ : syracuseStep 493547 = 740321) B740321
theorem B919603 : Blo 483789 919603 := bstep (se 1 (by rfl) ⟨689702, by rfl⟩ : syracuseStep 919603 = 1379405) B1379405
theorem B7473221 : Blo 483789 7473221 := bstep (se 4 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 7473221 = 1401229) B1401229
theorem B1312861 : Blo 483789 1312861 := bstep (se 3 (by rfl) ⟨246161, by rfl⟩ : syracuseStep 1312861 = 492323) B492323
theorem B1837187 : Blo 483789 1837187 := bstep (se 1 (by rfl) ⟨1377890, by rfl⟩ : syracuseStep 1837187 = 2755781) B2755781
theorem B821387 : Blo 483789 821387 := bstep (se 1 (by rfl) ⟨616040, by rfl⟩ : syracuseStep 821387 = 1232081) B1232081
theorem B1837201 : Blo 483789 1837201 := bstep (se 2 (by rfl) ⟨688950, by rfl⟩ : syracuseStep 1837201 = 1377901) B1377901
theorem B690329 : Blo 483789 690329 := bstep (se 2 (by rfl) ⟨258873, by rfl⟩ : syracuseStep 690329 = 517747) B517747
theorem B1640627 : Blo 483789 1640627 := bstep (se 1 (by rfl) ⟨1230470, by rfl⟩ : syracuseStep 1640627 = 2460941) B2460941
theorem B821515 : Blo 483789 821515 := bstep (se 1 (by rfl) ⟨616136, by rfl⟩ : syracuseStep 821515 = 1232273) B1232273
theorem B2885905 : Blo 483789 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B919831 : Blo 483789 919831 := bstep (se 1 (by rfl) ⟨689873, by rfl⟩ : syracuseStep 919831 = 1379747) B1379747
theorem B7113005 : Blo 483789 7113005 := bstep (se 3 (by rfl) ⟨1333688, by rfl⟩ : syracuseStep 7113005 = 2667377) B2667377
theorem B2459969 : Blo 483789 2459969 := bstep (se 2 (by rfl) ⟨922488, by rfl⟩ : syracuseStep 2459969 = 1844977) B1844977
theorem B919937 : Blo 483789 919937 := bstep (se 2 (by rfl) ⟨344976, by rfl⟩ : syracuseStep 919937 = 689953) B689953
theorem B821657 : Blo 483789 821657 := bstep (se 2 (by rfl) ⟨308121, by rfl⟩ : syracuseStep 821657 = 616243) B616243
theorem B1837505 : Blo 483789 1837505 := bstep (se 2 (by rfl) ⟨689064, by rfl⟩ : syracuseStep 1837505 = 1378129) B1378129
theorem B1640897 : Blo 483789 1640897 := bstep (se 2 (by rfl) ⟨615336, by rfl⟩ : syracuseStep 1640897 = 1230673) B1230673
theorem B920089 : Blo 483789 920089 := bstep (se 2 (by rfl) ⟨345033, by rfl⟩ : syracuseStep 920089 = 690067) B690067
theorem B821785 : Blo 483789 821785 := bstep (se 2 (by rfl) ⟨308169, by rfl⟩ : syracuseStep 821785 = 616339) B616339
theorem B2329361 : Blo 483789 2329361 := bstep (se 2 (by rfl) ⟨873510, by rfl⟩ : syracuseStep 2329361 = 1747021) B1747021
theorem B690967 : Blo 483789 690967 := bstep (se 1 (by rfl) ⟨518225, by rfl⟩ : syracuseStep 690967 = 1036451) B1036451
theorem B985943 : Blo 483789 985943 := bstep (se 1 (by rfl) ⟨739457, by rfl⟩ : syracuseStep 985943 = 1478915) B1478915
theorem B1641437 : Blo 483789 1641437 := bstep (se 3 (by rfl) ⟨307769, by rfl⟩ : syracuseStep 1641437 = 615539) B615539
theorem B822359 : Blo 483789 822359 := bstep (se 1 (by rfl) ⟨616769, by rfl⟩ : syracuseStep 822359 = 1233539) B1233539
theorem B1838173 : Blo 483789 1838173 := bstep (se 3 (by rfl) ⟨344657, by rfl⟩ : syracuseStep 1838173 = 689315) B689315
theorem B1379531 : Blo 483789 1379531 := bstep (se 1 (by rfl) ⟨1034648, by rfl⟩ : syracuseStep 1379531 = 2069297) B2069297
theorem B1477835 : Blo 483789 1477835 := bstep (se 1 (by rfl) ⟨1108376, by rfl⟩ : syracuseStep 1477835 = 2216753) B2216753
theorem B822487 : Blo 483789 822487 := bstep (se 1 (by rfl) ⟨616865, by rfl⟩ : syracuseStep 822487 = 1233731) B1233731
theorem B1346881 : Blo 483789 1346881 := bstep (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) B1010161
theorem B658891 : Blo 483789 658891 := bstep (se 1 (by rfl) ⟨494168, by rfl⟩ : syracuseStep 658891 = 988337) B988337
theorem B986585 : Blo 483789 986585 := bstep (se 2 (by rfl) ⟨369969, by rfl⟩ : syracuseStep 986585 = 739939) B739939
theorem B1314269 : Blo 483789 1314269 := bstep (se 3 (by rfl) ⟨246425, by rfl⟩ : syracuseStep 1314269 = 492851) B492851
theorem B1969667 : Blo 483789 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B2952769 : Blo 483789 2952769 := bstep (se 2 (by rfl) ⟨1107288, by rfl⟩ : syracuseStep 2952769 = 2214577) B2214577
theorem B691787 : Blo 483789 691787 := bstep (se 1 (by rfl) ⟨518840, by rfl⟩ : syracuseStep 691787 = 1037681) B1037681
theorem B1379929 : Blo 483789 1379929 := bstep (se 2 (by rfl) ⟨517473, by rfl⟩ : syracuseStep 1379929 = 1034947) B1034947
theorem B921395 : Blo 483789 921395 := bstep (se 1 (by rfl) ⟨691046, by rfl⟩ : syracuseStep 921395 = 1382093) B1382093
theorem B823115 : Blo 483789 823115 := bstep (se 1 (by rfl) ⟨617336, by rfl⟩ : syracuseStep 823115 = 1234673) B1234673
theorem B2068355 : Blo 483789 2068355 := bstep (se 1 (by rfl) ⟨1551266, by rfl⟩ : syracuseStep 2068355 = 3102533) B3102533
theorem B2756531 : Blo 483789 2756531 := bstep (se 1 (by rfl) ⟨2067398, by rfl⟩ : syracuseStep 2756531 = 4134797) B4134797
theorem B921547 : Blo 483789 921547 := bstep (se 1 (by rfl) ⟨691160, by rfl⟩ : syracuseStep 921547 = 1382321) B1382321
theorem B1183691 : Blo 483789 1183691 := bstep (se 1 (by rfl) ⟨887768, by rfl⟩ : syracuseStep 1183691 = 1775537) B1775537
theorem B6230033 : Blo 483789 6230033 := bstep (se 2 (by rfl) ⟨2336262, by rfl⟩ : syracuseStep 6230033 = 4672525) B4672525
theorem B888907 : Blo 483789 888907 := bstep (se 1 (by rfl) ⟨666680, by rfl⟩ : syracuseStep 888907 = 1333361) B1333361
theorem B1642571 : Blo 483789 1642571 := bstep (se 1 (by rfl) ⟨1231928, by rfl⟩ : syracuseStep 1642571 = 2463857) B2463857
theorem B2461913 : Blo 483789 2461913 := bstep (se 2 (by rfl) ⟨923217, by rfl⟩ : syracuseStep 2461913 = 1846435) B1846435
theorem B921881 : Blo 483789 921881 := bstep (se 2 (by rfl) ⟨345705, by rfl⟩ : syracuseStep 921881 = 691411) B691411
theorem B1839449 : Blo 483789 1839449 := bstep (se 2 (by rfl) ⟨689793, by rfl⟩ : syracuseStep 1839449 = 1379587) B1379587
theorem B1642841 : Blo 483789 1642841 := bstep (se 2 (by rfl) ⟨616065, by rfl⟩ : syracuseStep 1642841 = 1232131) B1232131
theorem B3543587 : Blo 483789 3543587 := bstep (se 1 (by rfl) ⟨2657690, by rfl⟩ : syracuseStep 3543587 = 5315381) B5315381
theorem B3936833 : Blo 483789 3936833 := bstep (se 2 (by rfl) ⟨1476312, by rfl⟩ : syracuseStep 3936833 = 2952625) B2952625
theorem B725771 : Blo 483789 725771 := bstep (se 1 (by rfl) ⟨544328, by rfl⟩ : syracuseStep 725771 = 1088657) B1088657
theorem B725783 : Blo 483789 725783 := bstep (se 1 (by rfl) ⟨544337, by rfl⟩ : syracuseStep 725783 = 1088675) B1088675
theorem B1381171 : Blo 483789 1381171 := bstep (se 1 (by rfl) ⟨1035878, by rfl⟩ : syracuseStep 1381171 = 2071757) B2071757
theorem B725849 : Blo 483789 725849 := bstep (se 2 (by rfl) ⟨272193, by rfl⟩ : syracuseStep 725849 = 544387) B544387
theorem B922519 : Blo 483789 922519 := bstep (se 1 (by rfl) ⟨691889, by rfl⟩ : syracuseStep 922519 = 1383779) B1383779
theorem B725963 : Blo 483789 725963 := bstep (se 1 (by rfl) ⟨544472, by rfl⟩ : syracuseStep 725963 = 1088945) B1088945
theorem B725975 : Blo 483789 725975 := bstep (se 1 (by rfl) ⟨544481, by rfl⟩ : syracuseStep 725975 = 1088963) B1088963
theorem B1643543 : Blo 483789 1643543 := bstep (se 1 (by rfl) ⟨1232657, by rfl⟩ : syracuseStep 1643543 = 2465315) B2465315
theorem B726041 : Blo 483789 726041 := bstep (se 2 (by rfl) ⟨272265, by rfl⟩ : syracuseStep 726041 = 544531) B544531
theorem B988247 : Blo 483789 988247 := bstep (se 1 (by rfl) ⟨741185, by rfl⟩ : syracuseStep 988247 = 1482371) B1482371
theorem B726155 : Blo 483789 726155 := bstep (se 1 (by rfl) ⟨544616, by rfl⟩ : syracuseStep 726155 = 1089233) B1089233
theorem B726167 : Blo 483789 726167 := bstep (se 1 (by rfl) ⟨544625, by rfl⟩ : syracuseStep 726167 = 1089251) B1089251
theorem B726233 : Blo 483789 726233 := bstep (se 2 (by rfl) ⟨272337, by rfl⟩ : syracuseStep 726233 = 544675) B544675
theorem B3118297 : Blo 483789 3118297 := bstep (se 2 (by rfl) ⟨1169361, by rfl⟩ : syracuseStep 3118297 = 2338723) B2338723
theorem B1316147 : Blo 483789 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B726347 : Blo 483789 726347 := bstep (se 1 (by rfl) ⟨544760, by rfl⟩ : syracuseStep 726347 = 1089521) B1089521
theorem B726359 : Blo 483789 726359 := bstep (se 1 (by rfl) ⟨544769, by rfl⟩ : syracuseStep 726359 = 1089539) B1089539
theorem B2757989 : Blo 483789 2757989 := bstep (se 4 (by rfl) ⟨258561, by rfl⟩ : syracuseStep 2757989 = 517123) B517123
theorem B726425 : Blo 483789 726425 := bstep (se 2 (by rfl) ⟨272409, by rfl⟩ : syracuseStep 726425 = 544819) B544819
theorem B2069981 : Blo 483789 2069981 := bstep (se 3 (by rfl) ⟨388121, by rfl⟩ : syracuseStep 2069981 = 776243) B776243
theorem B726539 : Blo 483789 726539 := bstep (se 1 (by rfl) ⟨544904, by rfl⟩ : syracuseStep 726539 = 1089809) B1089809
theorem B726551 : Blo 483789 726551 := bstep (se 1 (by rfl) ⟨544913, by rfl⟩ : syracuseStep 726551 = 1089827) B1089827
theorem B1644083 : Blo 483789 1644083 := bstep (se 1 (by rfl) ⟨1233062, by rfl⟩ : syracuseStep 1644083 = 2466125) B2466125
theorem B726617 : Blo 483789 726617 := bstep (se 2 (by rfl) ⟨272481, by rfl⟩ : syracuseStep 726617 = 544963) B544963
theorem B726731 : Blo 483789 726731 := bstep (se 1 (by rfl) ⟨545048, by rfl⟩ : syracuseStep 726731 = 1090097) B1090097
theorem B2102987 : Blo 483789 2102987 := bstep (se 1 (by rfl) ⟨1577240, by rfl⟩ : syracuseStep 2102987 = 3154481) B3154481
theorem B923339 : Blo 483789 923339 := bstep (se 1 (by rfl) ⟨692504, by rfl⟩ : syracuseStep 923339 = 1385009) B1385009
theorem B726743 : Blo 483789 726743 := bstep (se 1 (by rfl) ⟨545057, by rfl⟩ : syracuseStep 726743 = 1090115) B1090115
theorem B923393 : Blo 483789 923393 := bstep (se 2 (by rfl) ⟨346272, by rfl⟩ : syracuseStep 923393 = 692545) B692545
theorem B726809 : Blo 483789 726809 := bstep (se 2 (by rfl) ⟨272553, by rfl⟩ : syracuseStep 726809 = 545107) B545107
theorem B2758445 : Blo 483789 2758445 := bstep (se 3 (by rfl) ⟨517208, by rfl⟩ : syracuseStep 2758445 = 1034417) B1034417
theorem B2463533 : Blo 483789 2463533 := bstep (se 3 (by rfl) ⟨461912, by rfl⟩ : syracuseStep 2463533 = 923825) B923825
theorem B1644353 : Blo 483789 1644353 := bstep (se 2 (by rfl) ⟨616632, by rfl⟩ : syracuseStep 1644353 = 1233265) B1233265
theorem B726923 : Blo 483789 726923 := bstep (se 1 (by rfl) ⟨545192, by rfl⟩ : syracuseStep 726923 = 1090385) B1090385
theorem B726935 : Blo 483789 726935 := bstep (se 1 (by rfl) ⟨545201, by rfl⟩ : syracuseStep 726935 = 1090403) B1090403
theorem B1841075 : Blo 483789 1841075 := bstep (se 1 (by rfl) ⟨1380806, by rfl⟩ : syracuseStep 1841075 = 2761613) B2761613
theorem B1841089 : Blo 483789 1841089 := bstep (se 2 (by rfl) ⟨690408, by rfl⟩ : syracuseStep 1841089 = 1380817) B1380817
theorem B727001 : Blo 483789 727001 := bstep (se 2 (by rfl) ⟨272625, by rfl⟩ : syracuseStep 727001 = 545251) B545251
theorem B727115 : Blo 483789 727115 := bstep (se 1 (by rfl) ⟨545336, by rfl⟩ : syracuseStep 727115 = 1090673) B1090673
theorem B727127 : Blo 483789 727127 := bstep (se 1 (by rfl) ⟨545345, by rfl⟩ : syracuseStep 727127 = 1090691) B1090691
theorem B2070679 : Blo 483789 2070679 := bstep (se 1 (by rfl) ⟨1553009, by rfl⟩ : syracuseStep 2070679 = 3106019) B3106019
theorem B727193 : Blo 483789 727193 := bstep (se 2 (by rfl) ⟨272697, by rfl⟩ : syracuseStep 727193 = 545395) B545395
theorem B727307 : Blo 483789 727307 := bstep (se 1 (by rfl) ⟨545480, by rfl⟩ : syracuseStep 727307 = 1090961) B1090961
theorem B727319 : Blo 483789 727319 := bstep (se 1 (by rfl) ⟨545489, by rfl⟩ : syracuseStep 727319 = 1090979) B1090979
theorem B727385 : Blo 483789 727385 := bstep (se 2 (by rfl) ⟨272769, by rfl⟩ : syracuseStep 727385 = 545539) B545539
theorem B1644893 : Blo 483789 1644893 := bstep (se 3 (by rfl) ⟨308417, by rfl⟩ : syracuseStep 1644893 = 616835) B616835
theorem B727499 : Blo 483789 727499 := bstep (se 1 (by rfl) ⟨545624, by rfl⟩ : syracuseStep 727499 = 1091249) B1091249
theorem B727511 : Blo 483789 727511 := bstep (se 1 (by rfl) ⟨545633, by rfl⟩ : syracuseStep 727511 = 1091267) B1091267
theorem B2759129 : Blo 483789 2759129 := bstep (se 2 (by rfl) ⟨1034673, by rfl⟩ : syracuseStep 2759129 = 2069347) B2069347
theorem B727577 : Blo 483789 727577 := bstep (se 2 (by rfl) ⟨272841, by rfl⟩ : syracuseStep 727577 = 545683) B545683
theorem B1972781 : Blo 483789 1972781 := bstep (se 3 (by rfl) ⟨369896, by rfl⟩ : syracuseStep 1972781 = 739793) B739793
theorem B1972829 : Blo 483789 1972829 := bstep (se 3 (by rfl) ⟨369905, by rfl⟩ : syracuseStep 1972829 = 739811) B739811
theorem B727691 : Blo 483789 727691 := bstep (se 1 (by rfl) ⟨545768, by rfl⟩ : syracuseStep 727691 = 1091537) B1091537
theorem B727703 : Blo 483789 727703 := bstep (se 1 (by rfl) ⟨545777, by rfl⟩ : syracuseStep 727703 = 1091555) B1091555
theorem B924311 : Blo 483789 924311 := bstep (se 1 (by rfl) ⟨693233, by rfl⟩ : syracuseStep 924311 = 1386467) B1386467
theorem B727769 : Blo 483789 727769 := bstep (se 2 (by rfl) ⟨272913, by rfl⟩ : syracuseStep 727769 = 545827) B545827
theorem B727883 : Blo 483789 727883 := bstep (se 1 (by rfl) ⟨545912, by rfl⟩ : syracuseStep 727883 = 1091825) B1091825
theorem B727895 : Blo 483789 727895 := bstep (se 1 (by rfl) ⟨545921, by rfl⟩ : syracuseStep 727895 = 1091843) B1091843
theorem B1973143 : Blo 483789 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B727961 : Blo 483789 727961 := bstep (se 2 (by rfl) ⟨272985, by rfl⟩ : syracuseStep 727961 = 545971) B545971
theorem B4135859 : Blo 483789 4135859 := bstep (se 1 (by rfl) ⟨3101894, by rfl⟩ : syracuseStep 4135859 = 6203789) B6203789
theorem B728075 : Blo 483789 728075 := bstep (se 1 (by rfl) ⟨546056, by rfl⟩ : syracuseStep 728075 = 1092113) B1092113
theorem B728087 : Blo 483789 728087 := bstep (se 1 (by rfl) ⟨546065, by rfl⟩ : syracuseStep 728087 = 1092131) B1092131
theorem B728153 : Blo 483789 728153 := bstep (se 2 (by rfl) ⟨273057, by rfl⟩ : syracuseStep 728153 = 546115) B546115
theorem B924851 : Blo 483789 924851 := bstep (se 1 (by rfl) ⟨693638, by rfl⟩ : syracuseStep 924851 = 1387277) B1387277
theorem B728267 : Blo 483789 728267 := bstep (se 1 (by rfl) ⟨546200, by rfl⟩ : syracuseStep 728267 = 1092401) B1092401
theorem B728279 : Blo 483789 728279 := bstep (se 1 (by rfl) ⟨546209, by rfl⟩ : syracuseStep 728279 = 1092419) B1092419
theorem B1088729 : Blo 483789 1088729 := bstep (se 2 (by rfl) ⟨408273, by rfl⟩ : syracuseStep 1088729 = 816547) B816547
theorem B728345 : Blo 483789 728345 := bstep (se 2 (by rfl) ⟨273129, by rfl⟩ : syracuseStep 728345 = 546259) B546259
theorem B3939619 : Blo 483789 3939619 := bstep (se 1 (by rfl) ⟨2954714, by rfl⟩ : syracuseStep 3939619 = 5909429) B5909429
theorem B1088819 : Blo 483789 1088819 := bstep (se 1 (by rfl) ⟨816614, by rfl⟩ : syracuseStep 1088819 = 1633229) B1633229
theorem B1088855 : Blo 483789 1088855 := bstep (se 1 (by rfl) ⟨816641, by rfl⟩ : syracuseStep 1088855 = 1633283) B1633283
theorem B728459 : Blo 483789 728459 := bstep (se 1 (by rfl) ⟨546344, by rfl⟩ : syracuseStep 728459 = 1092689) B1092689
theorem B728471 : Blo 483789 728471 := bstep (se 1 (by rfl) ⟨546353, by rfl⟩ : syracuseStep 728471 = 1092707) B1092707
theorem B1646027 : Blo 483789 1646027 := bstep (se 1 (by rfl) ⟨1234520, by rfl⟩ : syracuseStep 1646027 = 2469041) B2469041
theorem B728537 : Blo 483789 728537 := bstep (se 2 (by rfl) ⟨273201, by rfl⟩ : syracuseStep 728537 = 546403) B546403
theorem B1089035 : Blo 483789 1089035 := bstep (se 1 (by rfl) ⟨816776, by rfl⟩ : syracuseStep 1089035 = 1633553) B1633553
theorem B2072081 : Blo 483789 2072081 := bstep (se 2 (by rfl) ⟨777030, by rfl⟩ : syracuseStep 2072081 = 1554061) B1554061
theorem B5250577 : Blo 483789 5250577 := bstep (se 2 (by rfl) ⟨1968966, by rfl⟩ : syracuseStep 5250577 = 3937933) B3937933
theorem B1089089 : Blo 483789 1089089 := bstep (se 2 (by rfl) ⟨408408, by rfl⟩ : syracuseStep 1089089 = 816817) B816817
theorem B728651 : Blo 483789 728651 := bstep (se 1 (by rfl) ⟨546488, by rfl⟩ : syracuseStep 728651 = 1092977) B1092977
theorem B728663 : Blo 483789 728663 := bstep (se 1 (by rfl) ⟨546497, by rfl⟩ : syracuseStep 728663 = 1092995) B1092995
theorem B1384087 : Blo 483789 1384087 := bstep (se 1 (by rfl) ⟨1038065, by rfl⟩ : syracuseStep 1384087 = 2076131) B2076131
theorem B728729 : Blo 483789 728729 := bstep (se 2 (by rfl) ⟨273273, by rfl⟩ : syracuseStep 728729 = 546547) B546547
theorem B925337 : Blo 483789 925337 := bstep (se 2 (by rfl) ⟨347001, by rfl⟩ : syracuseStep 925337 = 694003) B694003
theorem B728843 : Blo 483789 728843 := bstep (se 1 (by rfl) ⟨546632, by rfl⟩ : syracuseStep 728843 = 1093265) B1093265
theorem B728855 : Blo 483789 728855 := bstep (se 1 (by rfl) ⟨546641, by rfl⟩ : syracuseStep 728855 = 1093283) B1093283
theorem B1089305 : Blo 483789 1089305 := bstep (se 2 (by rfl) ⟨408489, by rfl⟩ : syracuseStep 1089305 = 816979) B816979
theorem B1843019 : Blo 483789 1843019 := bstep (se 1 (by rfl) ⟨1382264, by rfl⟩ : syracuseStep 1843019 = 2764529) B2764529
theorem B1843033 : Blo 483789 1843033 := bstep (se 2 (by rfl) ⟨691137, by rfl⟩ : syracuseStep 1843033 = 1382275) B1382275
theorem B728921 : Blo 483789 728921 := bstep (se 2 (by rfl) ⟨273345, by rfl⟩ : syracuseStep 728921 = 546691) B546691
theorem B1089395 : Blo 483789 1089395 := bstep (se 1 (by rfl) ⟨817046, by rfl⟩ : syracuseStep 1089395 = 1634093) B1634093
theorem B1089431 : Blo 483789 1089431 := bstep (se 1 (by rfl) ⟨817073, by rfl⟩ : syracuseStep 1089431 = 1634147) B1634147
theorem B729035 : Blo 483789 729035 := bstep (se 1 (by rfl) ⟨546776, by rfl⟩ : syracuseStep 729035 = 1093553) B1093553
theorem B729047 : Blo 483789 729047 := bstep (se 1 (by rfl) ⟨546785, by rfl⟩ : syracuseStep 729047 = 1093571) B1093571
theorem B729113 : Blo 483789 729113 := bstep (se 2 (by rfl) ⟨273417, by rfl⟩ : syracuseStep 729113 = 546835) B546835
theorem B1089611 : Blo 483789 1089611 := bstep (se 1 (by rfl) ⟨817208, by rfl⟩ : syracuseStep 1089611 = 1634417) B1634417
theorem B1089665 : Blo 483789 1089665 := bstep (se 2 (by rfl) ⟨408624, by rfl⟩ : syracuseStep 1089665 = 817249) B817249
theorem B729227 : Blo 483789 729227 := bstep (se 1 (by rfl) ⟨546920, by rfl⟩ : syracuseStep 729227 = 1093841) B1093841
theorem B729239 : Blo 483789 729239 := bstep (se 1 (by rfl) ⟨546929, by rfl⟩ : syracuseStep 729239 = 1093859) B1093859
theorem B729305 : Blo 483789 729305 := bstep (se 2 (by rfl) ⟨273489, by rfl⟩ : syracuseStep 729305 = 546979) B546979
theorem B729419 : Blo 483789 729419 := bstep (se 1 (by rfl) ⟨547064, by rfl⟩ : syracuseStep 729419 = 1094129) B1094129
theorem B729431 : Blo 483789 729431 := bstep (se 1 (by rfl) ⟨547073, by rfl⟩ : syracuseStep 729431 = 1094147) B1094147
theorem B1089881 : Blo 483789 1089881 := bstep (se 2 (by rfl) ⟨408705, by rfl⟩ : syracuseStep 1089881 = 817411) B817411
theorem B4432229 : Blo 483789 4432229 := bstep (se 4 (by rfl) ⟨415521, by rfl⟩ : syracuseStep 4432229 = 831043) B831043
theorem B729497 : Blo 483789 729497 := bstep (se 2 (by rfl) ⟨273561, by rfl⟩ : syracuseStep 729497 = 547123) B547123
theorem B1089971 : Blo 483789 1089971 := bstep (se 1 (by rfl) ⟨817478, by rfl⟩ : syracuseStep 1089971 = 1634957) B1634957
theorem B1090007 : Blo 483789 1090007 := bstep (se 1 (by rfl) ⟨817505, by rfl⟩ : syracuseStep 1090007 = 1635011) B1635011
theorem B729611 : Blo 483789 729611 := bstep (se 1 (by rfl) ⟨547208, by rfl⟩ : syracuseStep 729611 = 1094417) B1094417
theorem B729623 : Blo 483789 729623 := bstep (se 1 (by rfl) ⟨547217, by rfl⟩ : syracuseStep 729623 = 1094435) B1094435
theorem B729689 : Blo 483789 729689 := bstep (se 2 (by rfl) ⟨273633, by rfl⟩ : syracuseStep 729689 = 547267) B547267
theorem B1090187 : Blo 483789 1090187 := bstep (se 1 (by rfl) ⟨817640, by rfl⟩ : syracuseStep 1090187 = 1635281) B1635281
theorem B1090241 : Blo 483789 1090241 := bstep (se 2 (by rfl) ⟨408840, by rfl⟩ : syracuseStep 1090241 = 817681) B817681
theorem B729803 : Blo 483789 729803 := bstep (se 1 (by rfl) ⟨547352, by rfl⟩ : syracuseStep 729803 = 1094705) B1094705
theorem B17703629 : Blo 483789 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B729815 : Blo 483789 729815 := bstep (se 1 (by rfl) ⟨547361, by rfl⟩ : syracuseStep 729815 = 1094723) B1094723
theorem B1843991 : Blo 483789 1843991 := bstep (se 1 (by rfl) ⟨1382993, by rfl⟩ : syracuseStep 1843991 = 2765987) B2765987
theorem B729881 : Blo 483789 729881 := bstep (se 2 (by rfl) ⟨273705, by rfl⟩ : syracuseStep 729881 = 547411) B547411
theorem B729995 : Blo 483789 729995 := bstep (se 1 (by rfl) ⟨547496, by rfl⟩ : syracuseStep 729995 = 1094993) B1094993
theorem B730007 : Blo 483789 730007 := bstep (se 1 (by rfl) ⟨547505, by rfl⟩ : syracuseStep 730007 = 1095011) B1095011
theorem B1090457 : Blo 483789 1090457 := bstep (se 2 (by rfl) ⟨408921, by rfl⟩ : syracuseStep 1090457 = 817843) B817843
theorem B1385419 : Blo 483789 1385419 := bstep (se 1 (by rfl) ⟨1039064, by rfl⟩ : syracuseStep 1385419 = 2078129) B2078129
theorem B730073 : Blo 483789 730073 := bstep (se 2 (by rfl) ⟨273777, by rfl⟩ : syracuseStep 730073 = 547555) B547555
theorem B1090547 : Blo 483789 1090547 := bstep (se 1 (by rfl) ⟨817910, by rfl⟩ : syracuseStep 1090547 = 1635821) B1635821
theorem B1090583 : Blo 483789 1090583 := bstep (se 1 (by rfl) ⟨817937, by rfl⟩ : syracuseStep 1090583 = 1635875) B1635875
theorem B1778753 : Blo 483789 1778753 := bstep (se 2 (by rfl) ⟨667032, by rfl⟩ : syracuseStep 1778753 = 1334065) B1334065
theorem B2335819 : Blo 483789 2335819 := bstep (se 1 (by rfl) ⟨1751864, by rfl⟩ : syracuseStep 2335819 = 3503729) B3503729
theorem B730187 : Blo 483789 730187 := bstep (se 1 (by rfl) ⟨547640, by rfl⟩ : syracuseStep 730187 = 1095281) B1095281
theorem B730199 : Blo 483789 730199 := bstep (se 1 (by rfl) ⟨547649, by rfl⟩ : syracuseStep 730199 = 1095299) B1095299
theorem B730265 : Blo 483789 730265 := bstep (se 2 (by rfl) ⟨273849, by rfl⟩ : syracuseStep 730265 = 547699) B547699
theorem B8332469 : Blo 483789 8332469 := bstep (se 5 (by rfl) ⟨390584, by rfl⟩ : syracuseStep 8332469 = 781169) B781169
theorem B1090763 : Blo 483789 1090763 := bstep (se 1 (by rfl) ⟨818072, by rfl⟩ : syracuseStep 1090763 = 1636145) B1636145
theorem B1385693 : Blo 483789 1385693 := bstep (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) B519635
theorem B1090817 : Blo 483789 1090817 := bstep (se 2 (by rfl) ⟨409056, by rfl⟩ : syracuseStep 1090817 = 818113) B818113
theorem B730379 : Blo 483789 730379 := bstep (se 1 (by rfl) ⟨547784, by rfl⟩ : syracuseStep 730379 = 1095569) B1095569
theorem B3679505 : Blo 483789 3679505 := bstep (se 2 (by rfl) ⟨1379814, by rfl⟩ : syracuseStep 3679505 = 2759629) B2759629
theorem B730391 : Blo 483789 730391 := bstep (se 1 (by rfl) ⟨547793, by rfl⟩ : syracuseStep 730391 = 1095587) B1095587
theorem B730457 : Blo 483789 730457 := bstep (se 2 (by rfl) ⟨273921, by rfl⟩ : syracuseStep 730457 = 547843) B547843
theorem B730571 : Blo 483789 730571 := bstep (se 1 (by rfl) ⟨547928, by rfl⟩ : syracuseStep 730571 = 1095857) B1095857
theorem B730583 : Blo 483789 730583 := bstep (se 1 (by rfl) ⟨547937, by rfl⟩ : syracuseStep 730583 = 1095875) B1095875
theorem B1091033 : Blo 483789 1091033 := bstep (se 2 (by rfl) ⟨409137, by rfl⟩ : syracuseStep 1091033 = 818275) B818275
theorem B730649 : Blo 483789 730649 := bstep (se 2 (by rfl) ⟨273993, by rfl⟩ : syracuseStep 730649 = 547987) B547987
theorem B1091123 : Blo 483789 1091123 := bstep (se 1 (by rfl) ⟨818342, by rfl⟩ : syracuseStep 1091123 = 1636685) B1636685
theorem B1386035 : Blo 483789 1386035 := bstep (se 1 (by rfl) ⟨1039526, by rfl⟩ : syracuseStep 1386035 = 2079053) B2079053
theorem B1091159 : Blo 483789 1091159 := bstep (se 1 (by rfl) ⟨818369, by rfl⟩ : syracuseStep 1091159 = 1636739) B1636739
theorem B2467421 : Blo 483789 2467421 := bstep (se 3 (by rfl) ⟨462641, by rfl⟩ : syracuseStep 2467421 = 925283) B925283
theorem B730763 : Blo 483789 730763 := bstep (se 1 (by rfl) ⟨548072, by rfl⟩ : syracuseStep 730763 = 1096145) B1096145
theorem B730775 : Blo 483789 730775 := bstep (se 1 (by rfl) ⟨548081, by rfl⟩ : syracuseStep 730775 = 1096163) B1096163
theorem B2336435 : Blo 483789 2336435 := bstep (se 1 (by rfl) ⟨1752326, by rfl⟩ : syracuseStep 2336435 = 3504653) B3504653
theorem B730841 : Blo 483789 730841 := bstep (se 2 (by rfl) ⟨274065, by rfl⟩ : syracuseStep 730841 = 548131) B548131
theorem B2238173 : Blo 483789 2238173 := bstep (se 3 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 2238173 = 839315) B839315
theorem B2238211 : Blo 483789 2238211 := bstep (se 1 (by rfl) ⟨1678658, by rfl⟩ : syracuseStep 2238211 = 3357317) B3357317
theorem B1091339 : Blo 483789 1091339 := bstep (se 1 (by rfl) ⟨818504, by rfl⟩ : syracuseStep 1091339 = 1637009) B1637009
theorem B1091393 : Blo 483789 1091393 := bstep (se 2 (by rfl) ⟨409272, by rfl⟩ : syracuseStep 1091393 = 818545) B818545
theorem B730955 : Blo 483789 730955 := bstep (se 1 (by rfl) ⟨548216, by rfl⟩ : syracuseStep 730955 = 1096433) B1096433
theorem B730967 : Blo 483789 730967 := bstep (se 1 (by rfl) ⟨548225, by rfl⟩ : syracuseStep 730967 = 1096451) B1096451
theorem B731033 : Blo 483789 731033 := bstep (se 2 (by rfl) ⟨274137, by rfl⟩ : syracuseStep 731033 = 548275) B548275
theorem B1845251 : Blo 483789 1845251 := bstep (se 1 (by rfl) ⟨1383938, by rfl⟩ : syracuseStep 1845251 = 2767877) B2767877
theorem B731147 : Blo 483789 731147 := bstep (se 1 (by rfl) ⟨548360, by rfl⟩ : syracuseStep 731147 = 1096721) B1096721
theorem B731159 : Blo 483789 731159 := bstep (se 1 (by rfl) ⟨548369, by rfl⟩ : syracuseStep 731159 = 1096739) B1096739
theorem B1091609 : Blo 483789 1091609 := bstep (se 2 (by rfl) ⟨409353, by rfl⟩ : syracuseStep 1091609 = 818707) B818707
theorem B731225 : Blo 483789 731225 := bstep (se 2 (by rfl) ⟨274209, by rfl⟩ : syracuseStep 731225 = 548419) B548419
theorem B1976413 : Blo 483789 1976413 := bstep (se 3 (by rfl) ⟨370577, by rfl⟩ : syracuseStep 1976413 = 741155) B741155
theorem B1091699 : Blo 483789 1091699 := bstep (se 1 (by rfl) ⟨818774, by rfl⟩ : syracuseStep 1091699 = 1637549) B1637549
theorem B1091735 : Blo 483789 1091735 := bstep (se 1 (by rfl) ⟨818801, by rfl⟩ : syracuseStep 1091735 = 1637603) B1637603
theorem B731339 : Blo 483789 731339 := bstep (se 1 (by rfl) ⟨548504, by rfl⟩ : syracuseStep 731339 = 1097009) B1097009
theorem B731351 : Blo 483789 731351 := bstep (se 1 (by rfl) ⟨548513, by rfl⟩ : syracuseStep 731351 = 1097027) B1097027
theorem B731417 : Blo 483789 731417 := bstep (se 2 (by rfl) ⟨274281, by rfl⟩ : syracuseStep 731417 = 548563) B548563
theorem B1091915 : Blo 483789 1091915 := bstep (se 1 (by rfl) ⟨818936, by rfl⟩ : syracuseStep 1091915 = 1637873) B1637873
theorem B1091969 : Blo 483789 1091969 := bstep (se 2 (by rfl) ⟨409488, by rfl⟩ : syracuseStep 1091969 = 818977) B818977
theorem B731531 : Blo 483789 731531 := bstep (se 1 (by rfl) ⟨548648, by rfl⟩ : syracuseStep 731531 = 1097297) B1097297
theorem B731543 : Blo 483789 731543 := bstep (se 1 (by rfl) ⟨548657, by rfl⟩ : syracuseStep 731543 = 1097315) B1097315
theorem B2075053 : Blo 483789 2075053 := bstep (se 3 (by rfl) ⟨389072, by rfl⟩ : syracuseStep 2075053 = 778145) B778145
theorem B731609 : Blo 483789 731609 := bstep (se 2 (by rfl) ⟨274353, by rfl⟩ : syracuseStep 731609 = 548707) B548707
theorem B1092185 : Blo 483789 1092185 := bstep (se 2 (by rfl) ⟨409569, by rfl⟩ : syracuseStep 1092185 = 819139) B819139
theorem B1092275 : Blo 483789 1092275 := bstep (se 1 (by rfl) ⟨819206, by rfl⟩ : syracuseStep 1092275 = 1638413) B1638413
theorem B1092311 : Blo 483789 1092311 := bstep (se 1 (by rfl) ⟨819233, by rfl⟩ : syracuseStep 1092311 = 1638467) B1638467
theorem B1780445 : Blo 483789 1780445 := bstep (se 3 (by rfl) ⟨333833, by rfl⟩ : syracuseStep 1780445 = 667667) B667667
theorem B2075395 : Blo 483789 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B1092491 : Blo 483789 1092491 := bstep (se 1 (by rfl) ⟨819368, by rfl⟩ : syracuseStep 1092491 = 1638737) B1638737
theorem B1092545 : Blo 483789 1092545 := bstep (se 2 (by rfl) ⟨409704, by rfl⟩ : syracuseStep 1092545 = 819409) B819409
theorem B2763821 : Blo 483789 2763821 := bstep (se 3 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 2763821 = 1036433) B1036433
theorem B1092761 : Blo 483789 1092761 := bstep (se 2 (by rfl) ⟨409785, by rfl⟩ : syracuseStep 1092761 = 819571) B819571
theorem B1092851 : Blo 483789 1092851 := bstep (se 1 (by rfl) ⟨819638, by rfl⟩ : syracuseStep 1092851 = 1639277) B1639277
theorem B1092887 : Blo 483789 1092887 := bstep (se 1 (by rfl) ⟨819665, by rfl⟩ : syracuseStep 1092887 = 1639331) B1639331
theorem B1093067 : Blo 483789 1093067 := bstep (se 1 (by rfl) ⟨819800, by rfl⟩ : syracuseStep 1093067 = 1639601) B1639601
theorem B1093121 : Blo 483789 1093121 := bstep (se 2 (by rfl) ⟨409920, by rfl⟩ : syracuseStep 1093121 = 819841) B819841
theorem B1388107 : Blo 483789 1388107 := bstep (se 1 (by rfl) ⟨1041080, by rfl⟩ : syracuseStep 1388107 = 2082161) B2082161
theorem B2076353 : Blo 483789 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B1093337 : Blo 483789 1093337 := bstep (se 2 (by rfl) ⟨410001, by rfl⟩ : syracuseStep 1093337 = 820003) B820003
theorem B1093427 : Blo 483789 1093427 := bstep (se 1 (by rfl) ⟨820070, by rfl⟩ : syracuseStep 1093427 = 1640141) B1640141
theorem B1093463 : Blo 483789 1093463 := bstep (se 1 (by rfl) ⟨820097, by rfl⟩ : syracuseStep 1093463 = 1640195) B1640195
theorem B1093643 : Blo 483789 1093643 := bstep (se 1 (by rfl) ⟨820232, by rfl⟩ : syracuseStep 1093643 = 1640465) B1640465
theorem B1093697 : Blo 483789 1093697 := bstep (se 2 (by rfl) ⟨410136, by rfl⟩ : syracuseStep 1093697 = 820273) B820273
theorem B1388609 : Blo 483789 1388609 := bstep (se 2 (by rfl) ⟨520728, by rfl⟩ : syracuseStep 1388609 = 1041457) B1041457
theorem B8859779 : Blo 483789 8859779 := bstep (se 1 (by rfl) ⟨6644834, by rfl⟩ : syracuseStep 8859779 = 13289669) B13289669
theorem B831755 : Blo 483789 831755 := bstep (se 1 (by rfl) ⟨623816, by rfl⟩ : syracuseStep 831755 = 1247633) B1247633
theorem B1224983 : Blo 483789 1224983 := bstep (se 1 (by rfl) ⟨918737, by rfl⟩ : syracuseStep 1224983 = 1837475) B1837475
theorem B1093913 : Blo 483789 1093913 := bstep (se 2 (by rfl) ⟨410217, by rfl⟩ : syracuseStep 1093913 = 820435) B820435
theorem B1552729 : Blo 483789 1552729 := bstep (se 2 (by rfl) ⟨582273, by rfl⟩ : syracuseStep 1552729 = 1164547) B1164547
theorem B1094003 : Blo 483789 1094003 := bstep (se 1 (by rfl) ⟨820502, by rfl⟩ : syracuseStep 1094003 = 1641005) B1641005
theorem B1094039 : Blo 483789 1094039 := bstep (se 1 (by rfl) ⟨820529, by rfl⟩ : syracuseStep 1094039 = 1641059) B1641059
theorem B1388951 : Blo 483789 1388951 := bstep (se 1 (by rfl) ⟨1041713, by rfl⟩ : syracuseStep 1388951 = 2083427) B2083427
theorem B2240947 : Blo 483789 2240947 := bstep (se 1 (by rfl) ⟨1680710, by rfl⟩ : syracuseStep 2240947 = 3361421) B3361421
theorem B1094219 : Blo 483789 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B1094273 : Blo 483789 1094273 := bstep (se 2 (by rfl) ⟨410352, by rfl⟩ : syracuseStep 1094273 = 820705) B820705
theorem B1094489 : Blo 483789 1094489 := bstep (se 2 (by rfl) ⟨410433, by rfl⟩ : syracuseStep 1094489 = 820867) B820867
theorem B1225651 : Blo 483789 1225651 := bstep (se 1 (by rfl) ⟨919238, by rfl⟩ : syracuseStep 1225651 = 1838477) B1838477
theorem B1094579 : Blo 483789 1094579 := bstep (se 1 (by rfl) ⟨820934, by rfl⟩ : syracuseStep 1094579 = 1641869) B1641869
theorem B1094615 : Blo 483789 1094615 := bstep (se 1 (by rfl) ⟨820961, by rfl⟩ : syracuseStep 1094615 = 1641923) B1641923
theorem B1848365 : Blo 483789 1848365 := bstep (se 3 (by rfl) ⟨346568, by rfl⟩ : syracuseStep 1848365 = 693137) B693137
theorem B1225793 : Blo 483789 1225793 := bstep (se 2 (by rfl) ⟨459672, by rfl⟩ : syracuseStep 1225793 = 919345) B919345
theorem B3683393 : Blo 483789 3683393 := bstep (se 2 (by rfl) ⟨1381272, by rfl⟩ : syracuseStep 3683393 = 2762545) B2762545
theorem B2077771 : Blo 483789 2077771 := bstep (se 1 (by rfl) ⟨1558328, by rfl⟩ : syracuseStep 2077771 = 3116657) B3116657
theorem B1094795 : Blo 483789 1094795 := bstep (se 1 (by rfl) ⟨821096, by rfl⟩ : syracuseStep 1094795 = 1642193) B1642193
theorem B1094849 : Blo 483789 1094849 := bstep (se 2 (by rfl) ⟨410568, by rfl⟩ : syracuseStep 1094849 = 821137) B821137
theorem B2078045 : Blo 483789 2078045 := bstep (se 3 (by rfl) ⟨389633, by rfl⟩ : syracuseStep 2078045 = 779267) B779267
theorem B1095065 : Blo 483789 1095065 := bstep (se 2 (by rfl) ⟨410649, by rfl⟩ : syracuseStep 1095065 = 821299) B821299
theorem B1095155 : Blo 483789 1095155 := bstep (se 1 (by rfl) ⟨821366, by rfl⟩ : syracuseStep 1095155 = 1642733) B1642733
theorem B1095191 : Blo 483789 1095191 := bstep (se 1 (by rfl) ⟨821393, by rfl⟩ : syracuseStep 1095191 = 1642787) B1642787
theorem B1095371 : Blo 483789 1095371 := bstep (se 1 (by rfl) ⟨821528, by rfl⟩ : syracuseStep 1095371 = 1643057) B1643057
theorem B2340569 : Blo 483789 2340569 := bstep (se 2 (by rfl) ⟨877713, by rfl⟩ : syracuseStep 2340569 = 1755427) B1755427
theorem B1095425 : Blo 483789 1095425 := bstep (se 2 (by rfl) ⟨410784, by rfl⟩ : syracuseStep 1095425 = 821569) B821569
theorem B1849139 : Blo 483789 1849139 := bstep (se 1 (by rfl) ⟨1386854, by rfl⟩ : syracuseStep 1849139 = 2773709) B2773709
theorem B1095641 : Blo 483789 1095641 := bstep (se 2 (by rfl) ⟨410865, by rfl⟩ : syracuseStep 1095641 = 821731) B821731
theorem B3749905 : Blo 483789 3749905 := bstep (se 2 (by rfl) ⟨1406214, by rfl⟩ : syracuseStep 3749905 = 2812429) B2812429
theorem B1095731 : Blo 483789 1095731 := bstep (se 1 (by rfl) ⟨821798, by rfl⟩ : syracuseStep 1095731 = 1643597) B1643597
theorem B1554497 : Blo 483789 1554497 := bstep (se 2 (by rfl) ⟨582936, by rfl⟩ : syracuseStep 1554497 = 1165873) B1165873
theorem B1095767 : Blo 483789 1095767 := bstep (se 1 (by rfl) ⟨821825, by rfl⟩ : syracuseStep 1095767 = 1643651) B1643651
theorem B1095947 : Blo 483789 1095947 := bstep (se 1 (by rfl) ⟨821960, by rfl⟩ : syracuseStep 1095947 = 1643921) B1643921
theorem B1227059 : Blo 483789 1227059 := bstep (se 1 (by rfl) ⟨920294, by rfl⟩ : syracuseStep 1227059 = 1840589) B1840589
theorem B1096001 : Blo 483789 1096001 := bstep (se 2 (by rfl) ⟨411000, by rfl⟩ : syracuseStep 1096001 = 822001) B822001
theorem B1096217 : Blo 483789 1096217 := bstep (se 2 (by rfl) ⟨411081, by rfl⟩ : syracuseStep 1096217 = 822163) B822163
theorem B1096307 : Blo 483789 1096307 := bstep (se 1 (by rfl) ⟨822230, by rfl⟩ : syracuseStep 1096307 = 1644461) B1644461
theorem B1096343 : Blo 483789 1096343 := bstep (se 1 (by rfl) ⟨822257, by rfl⟩ : syracuseStep 1096343 = 1644515) B1644515
theorem B1227595 : Blo 483789 1227595 := bstep (se 1 (by rfl) ⟨920696, by rfl⟩ : syracuseStep 1227595 = 1841393) B1841393
theorem B1096523 : Blo 483789 1096523 := bstep (se 1 (by rfl) ⟨822392, by rfl⟩ : syracuseStep 1096523 = 1644785) B1644785
theorem B1096577 : Blo 483789 1096577 := bstep (se 2 (by rfl) ⟨411216, by rfl⟩ : syracuseStep 1096577 = 822433) B822433
theorem B1227737 : Blo 483789 1227737 := bstep (se 2 (by rfl) ⟨460401, by rfl⟩ : syracuseStep 1227737 = 920803) B920803
theorem B3685337 : Blo 483789 3685337 := bstep (se 2 (by rfl) ⟨1382001, by rfl⟩ : syracuseStep 3685337 = 2764003) B2764003
theorem B1096793 : Blo 483789 1096793 := bstep (se 2 (by rfl) ⟨411297, by rfl⟩ : syracuseStep 1096793 = 822595) B822595
theorem B4144229 : Blo 483789 4144229 := bstep (se 4 (by rfl) ⟨388521, by rfl⟩ : syracuseStep 4144229 = 777043) B777043
theorem B1096883 : Blo 483789 1096883 := bstep (se 1 (by rfl) ⟨822662, by rfl⟩ : syracuseStep 1096883 = 1645325) B1645325
theorem B1096919 : Blo 483789 1096919 := bstep (se 1 (by rfl) ⟨822689, by rfl⟩ : syracuseStep 1096919 = 1645379) B1645379
theorem B1850627 : Blo 483789 1850627 := bstep (se 1 (by rfl) ⟨1387970, by rfl⟩ : syracuseStep 1850627 = 2775941) B2775941
theorem B1555777 : Blo 483789 1555777 := bstep (se 2 (by rfl) ⟨583416, by rfl⟩ : syracuseStep 1555777 = 1166833) B1166833
theorem B1097099 : Blo 483789 1097099 := bstep (se 1 (by rfl) ⟨822824, by rfl⟩ : syracuseStep 1097099 = 1645649) B1645649
theorem B1097153 : Blo 483789 1097153 := bstep (se 2 (by rfl) ⟨411432, by rfl⟩ : syracuseStep 1097153 = 822865) B822865
theorem B999001 : Blo 483789 999001 := bstep (se 2 (by rfl) ⟨374625, by rfl⟩ : syracuseStep 999001 = 749251) B749251
theorem B1097369 : Blo 483789 1097369 := bstep (se 2 (by rfl) ⟨411513, by rfl⟩ : syracuseStep 1097369 = 823027) B823027
theorem B1851083 : Blo 483789 1851083 := bstep (se 1 (by rfl) ⟨1388312, by rfl⟩ : syracuseStep 1851083 = 2776625) B2776625
theorem B1097459 : Blo 483789 1097459 := bstep (se 1 (by rfl) ⟨823094, by rfl⟩ : syracuseStep 1097459 = 1646189) B1646189
theorem B1228567 : Blo 483789 1228567 := bstep (se 1 (by rfl) ⟨921425, by rfl⟩ : syracuseStep 1228567 = 1842851) B1842851
theorem B1097495 : Blo 483789 1097495 := bstep (se 1 (by rfl) ⟨823121, by rfl⟩ : syracuseStep 1097495 = 1646243) B1646243
theorem B2080657 : Blo 483789 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B1851281 : Blo 483789 1851281 := bstep (se 2 (by rfl) ⟨694230, by rfl⟩ : syracuseStep 1851281 = 1388461) B1388461
theorem B1229003 : Blo 483789 1229003 := bstep (se 1 (by rfl) ⟨921752, by rfl⟩ : syracuseStep 1229003 = 1843505) B1843505
theorem B1556957 : Blo 483789 1556957 := bstep (se 3 (by rfl) ⟨291929, by rfl⟩ : syracuseStep 1556957 = 583859) B583859
theorem B23708173 : Blo 483789 23708173 := bstep (se 3 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 23708173 = 8890565) B8890565
theorem B1229377 : Blo 483789 1229377 := bstep (se 2 (by rfl) ⟨461016, by rfl⟩ : syracuseStep 1229377 = 922033) B922033
theorem B14959235 : Blo 483789 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B1852055 : Blo 483789 1852055 := bstep (se 1 (by rfl) ⟨1389041, by rfl⟩ : syracuseStep 1852055 = 2778083) B2778083
theorem B1229975 : Blo 483789 1229975 := bstep (se 1 (by rfl) ⟨922481, by rfl⟩ : syracuseStep 1229975 = 1844963) B1844963
theorem B8275607 : Blo 483789 8275607 := bstep (se 1 (by rfl) ⟨6206705, by rfl⟩ : syracuseStep 8275607 = 12413411) B12413411
theorem B1034059 : Blo 483789 1034059 := bstep (se 1 (by rfl) ⟨775544, by rfl⟩ : syracuseStep 1034059 = 1551089) B1551089
theorem B1230785 : Blo 483789 1230785 := bstep (se 2 (by rfl) ⟨461544, by rfl⟩ : syracuseStep 1230785 = 923089) B923089
theorem B4475057 : Blo 483789 4475057 := bstep (se 2 (by rfl) ⟨1678146, by rfl⟩ : syracuseStep 4475057 = 3356293) B3356293
theorem B739531 : Blo 483789 739531 := bstep (se 1 (by rfl) ⟨554648, by rfl⟩ : syracuseStep 739531 = 1109297) B1109297
theorem B3688739 : Blo 483789 3688739 := bstep (se 1 (by rfl) ⟨2766554, by rfl⟩ : syracuseStep 3688739 = 5533109) B5533109
theorem B2771293 : Blo 483789 2771293 := bstep (se 3 (by rfl) ⟨519617, by rfl⟩ : syracuseStep 2771293 = 1039235) B1039235
theorem B1231321 : Blo 483789 1231321 := bstep (se 2 (by rfl) ⟨461745, by rfl⟩ : syracuseStep 1231321 = 923491) B923491
theorem B4999715 : Blo 483789 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B7031447 : Blo 483789 7031447 := bstep (se 1 (by rfl) ⟨5273585, by rfl⟩ : syracuseStep 7031447 = 10547171) B10547171
theorem B740377 : Blo 483789 740377 := bstep (se 2 (by rfl) ⟨277641, by rfl⟩ : syracuseStep 740377 = 555283) B555283
theorem B1035443 : Blo 483789 1035443 := bstep (se 1 (by rfl) ⟨776582, by rfl⟩ : syracuseStep 1035443 = 1553165) B1553165
theorem B1756363 : Blo 483789 1756363 := bstep (se 1 (by rfl) ⟨1317272, by rfl⟩ : syracuseStep 1756363 = 2634545) B2634545
theorem B544279 : Blo 483789 544279 := bstep (se 1 (by rfl) ⟨408209, by rfl⟩ : syracuseStep 544279 = 816419) B816419
theorem B1232435 : Blo 483789 1232435 := bstep (se 1 (by rfl) ⟨924326, by rfl⟩ : syracuseStep 1232435 = 1848653) B1848653
theorem B544459 : Blo 483789 544459 := bstep (se 1 (by rfl) ⟨408344, by rfl⟩ : syracuseStep 544459 = 816689) B816689
theorem B544567 : Blo 483789 544567 := bstep (se 1 (by rfl) ⟨408425, by rfl⟩ : syracuseStep 544567 = 816851) B816851
theorem B1232729 : Blo 483789 1232729 := bstep (se 2 (by rfl) ⟨462273, by rfl⟩ : syracuseStep 1232729 = 924547) B924547
theorem B544747 : Blo 483789 544747 := bstep (se 1 (by rfl) ⟨408560, by rfl⟩ : syracuseStep 544747 = 817121) B817121
theorem B1036289 : Blo 483789 1036289 := bstep (se 2 (by rfl) ⟨388608, by rfl⟩ : syracuseStep 1036289 = 777217) B777217
theorem B872473 : Blo 483789 872473 := bstep (se 2 (by rfl) ⟨327177, by rfl⟩ : syracuseStep 872473 = 654355) B654355
theorem B544855 : Blo 483789 544855 := bstep (se 1 (by rfl) ⟨408641, by rfl⟩ : syracuseStep 544855 = 817283) B817283
theorem B1757315 : Blo 483789 1757315 := bstep (se 1 (by rfl) ⟨1317986, by rfl⟩ : syracuseStep 1757315 = 2635973) B2635973
theorem B545035 : Blo 483789 545035 := bstep (se 1 (by rfl) ⟨408776, by rfl⟩ : syracuseStep 545035 = 817553) B817553
theorem B1036631 : Blo 483789 1036631 := bstep (se 1 (by rfl) ⟨777473, by rfl⟩ : syracuseStep 1036631 = 1554947) B1554947
theorem B545143 : Blo 483789 545143 := bstep (se 1 (by rfl) ⟨408857, by rfl⟩ : syracuseStep 545143 = 817715) B817715
theorem B1167833 : Blo 483789 1167833 := bstep (se 2 (by rfl) ⟨437937, by rfl⟩ : syracuseStep 1167833 = 875875) B875875
theorem B545323 : Blo 483789 545323 := bstep (se 1 (by rfl) ⟨408992, by rfl⟩ : syracuseStep 545323 = 817985) B817985
theorem B1659457 : Blo 483789 1659457 := bstep (se 2 (by rfl) ⟨622296, by rfl⟩ : syracuseStep 1659457 = 1244593) B1244593
theorem B873049 : Blo 483789 873049 := bstep (se 2 (by rfl) ⟨327393, by rfl⟩ : syracuseStep 873049 = 654787) B654787
theorem B545431 : Blo 483789 545431 := bstep (se 1 (by rfl) ⟨409073, by rfl⟩ : syracuseStep 545431 = 818147) B818147
theorem B545611 : Blo 483789 545611 := bstep (se 1 (by rfl) ⟨409208, by rfl⟩ : syracuseStep 545611 = 818417) B818417
theorem B545719 : Blo 483789 545719 := bstep (se 1 (by rfl) ⟨409289, by rfl⟩ : syracuseStep 545719 = 818579) B818579
theorem B545899 : Blo 483789 545899 := bstep (se 1 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 545899 = 818849) B818849
theorem B1561751 : Blo 483789 1561751 := bstep (se 1 (by rfl) ⟨1171313, by rfl⟩ : syracuseStep 1561751 = 2342627) B2342627
theorem B546007 : Blo 483789 546007 := bstep (se 1 (by rfl) ⟨409505, by rfl⟩ : syracuseStep 546007 = 819011) B819011
theorem B546187 : Blo 483789 546187 := bstep (se 1 (by rfl) ⟨409640, by rfl⟩ : syracuseStep 546187 = 819281) B819281
theorem B775577 : Blo 483789 775577 := bstep (se 2 (by rfl) ⟨290841, by rfl⟩ : syracuseStep 775577 = 581683) B581683
theorem B1234379 : Blo 483789 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B546295 : Blo 483789 546295 := bstep (se 1 (by rfl) ⟨409721, by rfl⟩ : syracuseStep 546295 = 819443) B819443
theorem B546475 : Blo 483789 546475 := bstep (se 1 (by rfl) ⟨409856, by rfl⟩ : syracuseStep 546475 = 819713) B819713
theorem B1038091 : Blo 483789 1038091 := bstep (se 1 (by rfl) ⟨778568, by rfl⟩ : syracuseStep 1038091 = 1557137) B1557137
theorem B546583 : Blo 483789 546583 := bstep (se 1 (by rfl) ⟨409937, by rfl⟩ : syracuseStep 546583 = 819875) B819875
theorem B776089 : Blo 483789 776089 := bstep (se 2 (by rfl) ⟨291033, by rfl⟩ : syracuseStep 776089 = 582067) B582067
theorem B874433 : Blo 483789 874433 := bstep (se 2 (by rfl) ⟨327912, by rfl⟩ : syracuseStep 874433 = 655825) B655825
theorem B612299 : Blo 483789 612299 := bstep (se 1 (by rfl) ⟨459224, by rfl⟩ : syracuseStep 612299 = 918449) B918449
theorem B546763 : Blo 483789 546763 := bstep (se 1 (by rfl) ⟨410072, by rfl⟩ : syracuseStep 546763 = 820145) B820145
theorem B1038347 : Blo 483789 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B546871 : Blo 483789 546871 := bstep (se 1 (by rfl) ⟨410153, by rfl⟩ : syracuseStep 546871 = 820307) B820307
theorem B5036107 : Blo 483789 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B4675715 : Blo 483789 4675715 := bstep (se 1 (by rfl) ⟨3506786, by rfl⟩ : syracuseStep 4675715 = 7013573) B7013573
theorem B547051 : Blo 483789 547051 := bstep (se 1 (by rfl) ⟨410288, by rfl⟩ : syracuseStep 547051 = 820577) B820577
theorem B4413761 : Blo 483789 4413761 := bstep (se 2 (by rfl) ⟨1655160, by rfl⟩ : syracuseStep 4413761 = 3310321) B3310321
theorem B547159 : Blo 483789 547159 := bstep (se 1 (by rfl) ⟨410369, by rfl⟩ : syracuseStep 547159 = 820739) B820739
theorem B874967 : Blo 483789 874967 := bstep (se 1 (by rfl) ⟨656225, by rfl⟩ : syracuseStep 874967 = 1312451) B1312451
theorem B547339 : Blo 483789 547339 := bstep (se 1 (by rfl) ⟨410504, by rfl⟩ : syracuseStep 547339 = 821009) B821009
theorem B17717777 : Blo 483789 17717777 := bstep (se 2 (by rfl) ⟨6644166, by rfl⟩ : syracuseStep 17717777 = 13288333) B13288333
theorem B875083 : Blo 483789 875083 := bstep (se 1 (by rfl) ⟨656312, by rfl⟩ : syracuseStep 875083 = 1312625) B1312625
theorem B547447 : Blo 483789 547447 := bstep (se 1 (by rfl) ⟨410585, by rfl⟩ : syracuseStep 547447 = 821171) B821171
theorem B613003 : Blo 483789 613003 := bstep (se 1 (by rfl) ⟨459752, by rfl⟩ : syracuseStep 613003 = 919505) B919505
theorem B8837873 : Blo 483789 8837873 := bstep (se 2 (by rfl) ⟨3314202, by rfl⟩ : syracuseStep 8837873 = 6628405) B6628405
theorem B547627 : Blo 483789 547627 := bstep (se 1 (by rfl) ⟨410720, by rfl⟩ : syracuseStep 547627 = 821441) B821441
theorem B613271 : Blo 483789 613271 := bstep (se 1 (by rfl) ⟨459953, by rfl⟩ : syracuseStep 613271 = 919907) B919907
theorem B547735 : Blo 483789 547735 := bstep (se 1 (by rfl) ⟨410801, by rfl⟩ : syracuseStep 547735 = 821603) B821603
theorem B1039321 : Blo 483789 1039321 := bstep (se 2 (by rfl) ⟨389745, by rfl⟩ : syracuseStep 1039321 = 779491) B779491
theorem B547915 : Blo 483789 547915 := bstep (se 1 (by rfl) ⟨410936, by rfl⟩ : syracuseStep 547915 = 821873) B821873
theorem B1039475 : Blo 483789 1039475 := bstep (se 1 (by rfl) ⟨779606, by rfl⟩ : syracuseStep 1039475 = 1559213) B1559213
theorem B548023 : Blo 483789 548023 := bstep (se 1 (by rfl) ⟨411017, by rfl⟩ : syracuseStep 548023 = 822035) B822035
theorem B548203 : Blo 483789 548203 := bstep (se 1 (by rfl) ⟨411152, by rfl⟩ : syracuseStep 548203 = 822305) B822305
theorem B548311 : Blo 483789 548311 := bstep (se 1 (by rfl) ⟨411233, by rfl⟩ : syracuseStep 548311 = 822467) B822467
theorem B876019 : Blo 483789 876019 := bstep (se 1 (by rfl) ⟨657014, by rfl⟩ : syracuseStep 876019 = 1314029) B1314029
theorem B3694085 : Blo 483789 3694085 := bstep (se 4 (by rfl) ⟨346320, by rfl⟩ : syracuseStep 3694085 = 692641) B692641
theorem B1105483 : Blo 483789 1105483 := bstep (se 1 (by rfl) ⟨829112, by rfl⟩ : syracuseStep 1105483 = 1658225) B1658225
theorem B5693003 : Blo 483789 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B613975 : Blo 483789 613975 := bstep (se 1 (by rfl) ⟨460481, by rfl⟩ : syracuseStep 613975 = 920963) B920963
theorem B1039987 : Blo 483789 1039987 := bstep (se 1 (by rfl) ⟨779990, by rfl⟩ : syracuseStep 1039987 = 1559981) B1559981
theorem B548491 : Blo 483789 548491 := bstep (se 1 (by rfl) ⟨411368, by rfl⟩ : syracuseStep 548491 = 822737) B822737
theorem B548599 : Blo 483789 548599 := bstep (se 1 (by rfl) ⟨411449, by rfl⟩ : syracuseStep 548599 = 822899) B822899
theorem B3563443 : Blo 483789 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B8314973 : Blo 483789 8314973 := bstep (se 3 (by rfl) ⟨1559057, by rfl⟩ : syracuseStep 8314973 = 3118115) B3118115
theorem B8446103 : Blo 483789 8446103 := bstep (se 1 (by rfl) ⟨6334577, by rfl⟩ : syracuseStep 8446103 = 12669155) B12669155
theorem B909515 : Blo 483789 909515 := bstep (se 1 (by rfl) ⟨682136, by rfl⟩ : syracuseStep 909515 = 1364273) B1364273
theorem B93184277 : Blo 483789 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B1040663 : Blo 483789 1040663 := bstep (se 1 (by rfl) ⟨780497, by rfl⟩ : syracuseStep 1040663 = 1560995) B1560995
theorem B1040705 : Blo 483789 1040705 := bstep (se 2 (by rfl) ⟨390264, by rfl⟩ : syracuseStep 1040705 = 780529) B780529
theorem B5005633 : Blo 483789 5005633 := bstep (se 2 (by rfl) ⟨1877112, by rfl⟩ : syracuseStep 5005633 = 3754225) B3754225
theorem B3105175 : Blo 483789 3105175 := bstep (se 1 (by rfl) ⟨2328881, by rfl⟩ : syracuseStep 3105175 = 4657763) B4657763
theorem B483799 : Blo 483789 483799 := bstep (se 1 (by rfl) ⟨362849, by rfl⟩ : syracuseStep 483799 = 725699) B725699
theorem B483819 : Blo 483789 483819 := bstep (se 1 (by rfl) ⟨362864, by rfl⟩ : syracuseStep 483819 = 725729) B725729
theorem B483831 : Blo 483789 483831 := bstep (se 1 (by rfl) ⟨362873, by rfl⟩ : syracuseStep 483831 = 725747) B725747
theorem B483851 : Blo 483789 483851 := bstep (se 1 (by rfl) ⟨362888, by rfl⟩ : syracuseStep 483851 = 725777) B725777
theorem B483863 : Blo 483789 483863 := bstep (se 1 (by rfl) ⟨362897, by rfl⟩ : syracuseStep 483863 = 725795) B725795
theorem B1401367 : Blo 483789 1401367 := bstep (se 1 (by rfl) ⟨1051025, by rfl⟩ : syracuseStep 1401367 = 2102051) B2102051
theorem B483883 : Blo 483789 483883 := bstep (se 1 (by rfl) ⟨362912, by rfl⟩ : syracuseStep 483883 = 725825) B725825
theorem B483895 : Blo 483789 483895 := bstep (se 1 (by rfl) ⟨362921, by rfl⟩ : syracuseStep 483895 = 725843) B725843
theorem B483915 : Blo 483789 483915 := bstep (se 1 (by rfl) ⟨362936, by rfl⟩ : syracuseStep 483915 = 725873) B725873
theorem B483927 : Blo 483789 483927 := bstep (se 1 (by rfl) ⟨362945, by rfl⟩ : syracuseStep 483927 = 725891) B725891
theorem B10543709 : Blo 483789 10543709 := bstep (se 3 (by rfl) ⟨1976945, by rfl⟩ : syracuseStep 10543709 = 3953891) B3953891
theorem B483947 : Blo 483789 483947 := bstep (se 1 (by rfl) ⟨362960, by rfl⟩ : syracuseStep 483947 = 725921) B725921
theorem B483959 : Blo 483789 483959 := bstep (se 1 (by rfl) ⟨362969, by rfl⟩ : syracuseStep 483959 = 725939) B725939
theorem B483979 : Blo 483789 483979 := bstep (se 1 (by rfl) ⟨362984, by rfl⟩ : syracuseStep 483979 = 725969) B725969
theorem B483991 : Blo 483789 483991 := bstep (se 1 (by rfl) ⟨362993, by rfl⟩ : syracuseStep 483991 = 725987) B725987
theorem B484011 : Blo 483789 484011 := bstep (se 1 (by rfl) ⟨363008, by rfl⟩ : syracuseStep 484011 = 726017) B726017
theorem B484023 : Blo 483789 484023 := bstep (se 1 (by rfl) ⟨363017, by rfl⟩ : syracuseStep 484023 = 726035) B726035
theorem B484043 : Blo 483789 484043 := bstep (se 1 (by rfl) ⟨363032, by rfl⟩ : syracuseStep 484043 = 726065) B726065
theorem B877259 : Blo 483789 877259 := bstep (se 1 (by rfl) ⟨657944, by rfl⟩ : syracuseStep 877259 = 1315889) B1315889
theorem B484055 : Blo 483789 484055 := bstep (se 1 (by rfl) ⟨363041, by rfl⟩ : syracuseStep 484055 = 726083) B726083
theorem B484075 : Blo 483789 484075 := bstep (se 1 (by rfl) ⟨363056, by rfl⟩ : syracuseStep 484075 = 726113) B726113
theorem B484087 : Blo 483789 484087 := bstep (se 1 (by rfl) ⟨363065, by rfl⟩ : syracuseStep 484087 = 726131) B726131
theorem B484107 : Blo 483789 484107 := bstep (se 1 (by rfl) ⟨363080, by rfl⟩ : syracuseStep 484107 = 726161) B726161
theorem B484119 : Blo 483789 484119 := bstep (se 1 (by rfl) ⟨363089, by rfl⟩ : syracuseStep 484119 = 726179) B726179
theorem B484139 : Blo 483789 484139 := bstep (se 1 (by rfl) ⟨363104, by rfl⟩ : syracuseStep 484139 = 726209) B726209
theorem B484151 : Blo 483789 484151 := bstep (se 1 (by rfl) ⟨363113, by rfl⟩ : syracuseStep 484151 = 726227) B726227
theorem B484171 : Blo 483789 484171 := bstep (se 1 (by rfl) ⟨363128, by rfl⟩ : syracuseStep 484171 = 726257) B726257
theorem B582475 : Blo 483789 582475 := bstep (se 1 (by rfl) ⟨436856, by rfl⟩ : syracuseStep 582475 = 873713) B873713
theorem B484183 : Blo 483789 484183 := bstep (se 1 (by rfl) ⟨363137, by rfl⟩ : syracuseStep 484183 = 726275) B726275
theorem B484203 : Blo 483789 484203 := bstep (se 1 (by rfl) ⟨363152, by rfl⟩ : syracuseStep 484203 = 726305) B726305
theorem B484215 : Blo 483789 484215 := bstep (se 1 (by rfl) ⟨363161, by rfl⟩ : syracuseStep 484215 = 726323) B726323
theorem B484235 : Blo 483789 484235 := bstep (se 1 (by rfl) ⟨363176, by rfl⟩ : syracuseStep 484235 = 726353) B726353
theorem B484247 : Blo 483789 484247 := bstep (se 1 (by rfl) ⟨363185, by rfl⟩ : syracuseStep 484247 = 726371) B726371
theorem B484267 : Blo 483789 484267 := bstep (se 1 (by rfl) ⟨363200, by rfl⟩ : syracuseStep 484267 = 726401) B726401
theorem B15000497 : Blo 483789 15000497 := bstep (se 2 (by rfl) ⟨5625186, by rfl⟩ : syracuseStep 15000497 = 11250373) B11250373
theorem B484279 : Blo 483789 484279 := bstep (se 1 (by rfl) ⟨363209, by rfl⟩ : syracuseStep 484279 = 726419) B726419
theorem B484299 : Blo 483789 484299 := bstep (se 1 (by rfl) ⟨363224, by rfl⟩ : syracuseStep 484299 = 726449) B726449
theorem B484311 : Blo 483789 484311 := bstep (se 1 (by rfl) ⟨363233, by rfl⟩ : syracuseStep 484311 = 726467) B726467
theorem B484331 : Blo 483789 484331 := bstep (se 1 (by rfl) ⟨363248, by rfl⟩ : syracuseStep 484331 = 726497) B726497
theorem B484343 : Blo 483789 484343 := bstep (se 1 (by rfl) ⟨363257, by rfl⟩ : syracuseStep 484343 = 726515) B726515
theorem B484363 : Blo 483789 484363 := bstep (se 1 (by rfl) ⟨363272, by rfl⟩ : syracuseStep 484363 = 726545) B726545
theorem B26240021 : Blo 483789 26240021 := bstep (se 6 (by rfl) ⟨615000, by rfl⟩ : syracuseStep 26240021 = 1230001) B1230001
theorem B484375 : Blo 483789 484375 := bstep (se 1 (by rfl) ⟨363281, by rfl⟩ : syracuseStep 484375 = 726563) B726563
theorem B484395 : Blo 483789 484395 := bstep (se 1 (by rfl) ⟨363296, by rfl⟩ : syracuseStep 484395 = 726593) B726593
theorem B484407 : Blo 483789 484407 := bstep (se 1 (by rfl) ⟨363305, by rfl⟩ : syracuseStep 484407 = 726611) B726611
theorem B484427 : Blo 483789 484427 := bstep (se 1 (by rfl) ⟨363320, by rfl⟩ : syracuseStep 484427 = 726641) B726641
theorem B484439 : Blo 483789 484439 := bstep (se 1 (by rfl) ⟨363329, by rfl⟩ : syracuseStep 484439 = 726659) B726659
theorem B484459 : Blo 483789 484459 := bstep (se 1 (by rfl) ⟨363344, by rfl⟩ : syracuseStep 484459 = 726689) B726689
theorem B484471 : Blo 483789 484471 := bstep (se 1 (by rfl) ⟨363353, by rfl⟩ : syracuseStep 484471 = 726707) B726707
theorem B484491 : Blo 483789 484491 := bstep (se 1 (by rfl) ⟨363368, by rfl⟩ : syracuseStep 484491 = 726737) B726737
theorem B484503 : Blo 483789 484503 := bstep (se 1 (by rfl) ⟨363377, by rfl⟩ : syracuseStep 484503 = 726755) B726755
theorem B484523 : Blo 483789 484523 := bstep (se 1 (by rfl) ⟨363392, by rfl⟩ : syracuseStep 484523 = 726785) B726785
theorem B517303 : Blo 483789 517303 := bstep (se 1 (by rfl) ⟨387977, by rfl⟩ : syracuseStep 517303 = 775955) B775955
theorem B484535 : Blo 483789 484535 := bstep (se 1 (by rfl) ⟨363401, by rfl⟩ : syracuseStep 484535 = 726803) B726803
theorem B484555 : Blo 483789 484555 := bstep (se 1 (by rfl) ⟨363416, by rfl⟩ : syracuseStep 484555 = 726833) B726833
theorem B484567 : Blo 483789 484567 := bstep (se 1 (by rfl) ⟨363425, by rfl⟩ : syracuseStep 484567 = 726851) B726851
theorem B484587 : Blo 483789 484587 := bstep (se 1 (by rfl) ⟨363440, by rfl⟩ : syracuseStep 484587 = 726881) B726881
theorem B484599 : Blo 483789 484599 := bstep (se 1 (by rfl) ⟨363449, by rfl⟩ : syracuseStep 484599 = 726899) B726899
theorem B32531717 : Blo 483789 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B484619 : Blo 483789 484619 := bstep (se 1 (by rfl) ⟨363464, by rfl⟩ : syracuseStep 484619 = 726929) B726929
theorem B615691 : Blo 483789 615691 := bstep (se 1 (by rfl) ⟨461768, by rfl⟩ : syracuseStep 615691 = 923537) B923537
theorem B484631 : Blo 483789 484631 := bstep (se 1 (by rfl) ⟨363473, by rfl⟩ : syracuseStep 484631 = 726947) B726947
theorem B484651 : Blo 483789 484651 := bstep (se 1 (by rfl) ⟨363488, by rfl⟩ : syracuseStep 484651 = 726977) B726977
theorem B484663 : Blo 483789 484663 := bstep (se 1 (by rfl) ⟨363497, by rfl⟩ : syracuseStep 484663 = 726995) B726995
theorem B484683 : Blo 483789 484683 := bstep (se 1 (by rfl) ⟨363512, by rfl⟩ : syracuseStep 484683 = 727025) B727025
theorem B484695 : Blo 483789 484695 := bstep (se 1 (by rfl) ⟨363521, by rfl⟩ : syracuseStep 484695 = 727043) B727043
theorem B484715 : Blo 483789 484715 := bstep (se 1 (by rfl) ⟨363536, by rfl⟩ : syracuseStep 484715 = 727073) B727073
theorem B484727 : Blo 483789 484727 := bstep (se 1 (by rfl) ⟨363545, by rfl⟩ : syracuseStep 484727 = 727091) B727091
theorem B484747 : Blo 483789 484747 := bstep (se 1 (by rfl) ⟨363560, by rfl⟩ : syracuseStep 484747 = 727121) B727121
theorem B31450517 : Blo 483789 31450517 := bstep (se 6 (by rfl) ⟨737121, by rfl⟩ : syracuseStep 31450517 = 1474243) B1474243
theorem B484759 : Blo 483789 484759 := bstep (se 1 (by rfl) ⟨363569, by rfl⟩ : syracuseStep 484759 = 727139) B727139
theorem B484779 : Blo 483789 484779 := bstep (se 1 (by rfl) ⟨363584, by rfl⟩ : syracuseStep 484779 = 727169) B727169
theorem B484791 : Blo 483789 484791 := bstep (se 1 (by rfl) ⟨363593, by rfl⟩ : syracuseStep 484791 = 727187) B727187
theorem B484811 : Blo 483789 484811 := bstep (se 1 (by rfl) ⟨363608, by rfl⟩ : syracuseStep 484811 = 727217) B727217
theorem B484823 : Blo 483789 484823 := bstep (se 1 (by rfl) ⟨363617, by rfl⟩ : syracuseStep 484823 = 727235) B727235
theorem B484843 : Blo 483789 484843 := bstep (se 1 (by rfl) ⟨363632, by rfl⟩ : syracuseStep 484843 = 727265) B727265
theorem B484855 : Blo 483789 484855 := bstep (se 1 (by rfl) ⟨363641, by rfl⟩ : syracuseStep 484855 = 727283) B727283
theorem B484875 : Blo 483789 484875 := bstep (se 1 (by rfl) ⟨363656, by rfl⟩ : syracuseStep 484875 = 727313) B727313
theorem B484887 : Blo 483789 484887 := bstep (se 1 (by rfl) ⟨363665, by rfl⟩ : syracuseStep 484887 = 727331) B727331
theorem B484907 : Blo 483789 484907 := bstep (se 1 (by rfl) ⟨363680, by rfl⟩ : syracuseStep 484907 = 727361) B727361
theorem B484919 : Blo 483789 484919 := bstep (se 1 (by rfl) ⟨363689, by rfl⟩ : syracuseStep 484919 = 727379) B727379
theorem B484939 : Blo 483789 484939 := bstep (se 1 (by rfl) ⟨363704, by rfl⟩ : syracuseStep 484939 = 727409) B727409
theorem B484951 : Blo 483789 484951 := bstep (se 1 (by rfl) ⟨363713, by rfl⟩ : syracuseStep 484951 = 727427) B727427
theorem B779863 : Blo 483789 779863 := bstep (se 1 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 779863 = 1169795) B1169795
theorem B484971 : Blo 483789 484971 := bstep (se 1 (by rfl) ⟨363728, by rfl⟩ : syracuseStep 484971 = 727457) B727457
theorem B484983 : Blo 483789 484983 := bstep (se 1 (by rfl) ⟨363737, by rfl⟩ : syracuseStep 484983 = 727475) B727475
theorem B485003 : Blo 483789 485003 := bstep (se 1 (by rfl) ⟨363752, by rfl⟩ : syracuseStep 485003 = 727505) B727505
theorem B485015 : Blo 483789 485015 := bstep (se 1 (by rfl) ⟨363761, by rfl⟩ : syracuseStep 485015 = 727523) B727523
theorem B485035 : Blo 483789 485035 := bstep (se 1 (by rfl) ⟨363776, by rfl⟩ : syracuseStep 485035 = 727553) B727553
theorem B485047 : Blo 483789 485047 := bstep (se 1 (by rfl) ⟨363785, by rfl⟩ : syracuseStep 485047 = 727571) B727571
theorem B485067 : Blo 483789 485067 := bstep (se 1 (by rfl) ⟨363800, by rfl⟩ : syracuseStep 485067 = 727601) B727601
theorem B485079 : Blo 483789 485079 := bstep (se 1 (by rfl) ⟨363809, by rfl⟩ : syracuseStep 485079 = 727619) B727619
theorem B485099 : Blo 483789 485099 := bstep (se 1 (by rfl) ⟨363824, by rfl⟩ : syracuseStep 485099 = 727649) B727649
theorem B485111 : Blo 483789 485111 := bstep (se 1 (by rfl) ⟨363833, by rfl⟩ : syracuseStep 485111 = 727667) B727667
theorem B485131 : Blo 483789 485131 := bstep (se 1 (by rfl) ⟨363848, by rfl⟩ : syracuseStep 485131 = 727697) B727697
theorem B485143 : Blo 483789 485143 := bstep (se 1 (by rfl) ⟨363857, by rfl⟩ : syracuseStep 485143 = 727715) B727715
theorem B485163 : Blo 483789 485163 := bstep (se 1 (by rfl) ⟨363872, by rfl⟩ : syracuseStep 485163 = 727745) B727745
theorem B485175 : Blo 483789 485175 := bstep (se 1 (by rfl) ⟨363881, by rfl⟩ : syracuseStep 485175 = 727763) B727763
theorem B485195 : Blo 483789 485195 := bstep (se 1 (by rfl) ⟨363896, by rfl⟩ : syracuseStep 485195 = 727793) B727793
theorem B485207 : Blo 483789 485207 := bstep (se 1 (by rfl) ⟨363905, by rfl⟩ : syracuseStep 485207 = 727811) B727811
theorem B780119 : Blo 483789 780119 := bstep (se 1 (by rfl) ⟨585089, by rfl⟩ : syracuseStep 780119 = 1170179) B1170179
theorem B485227 : Blo 483789 485227 := bstep (se 1 (by rfl) ⟨363920, by rfl⟩ : syracuseStep 485227 = 727841) B727841
theorem B485239 : Blo 483789 485239 := bstep (se 1 (by rfl) ⟨363929, by rfl⟩ : syracuseStep 485239 = 727859) B727859
theorem B3696515 : Blo 483789 3696515 := bstep (se 1 (by rfl) ⟨2772386, by rfl⟩ : syracuseStep 3696515 = 5544773) B5544773
theorem B485259 : Blo 483789 485259 := bstep (se 1 (by rfl) ⟨363944, by rfl⟩ : syracuseStep 485259 = 727889) B727889
theorem B485271 : Blo 483789 485271 := bstep (se 1 (by rfl) ⟨363953, by rfl⟩ : syracuseStep 485271 = 727907) B727907
theorem B485291 : Blo 483789 485291 := bstep (se 1 (by rfl) ⟨363968, by rfl⟩ : syracuseStep 485291 = 727937) B727937
theorem B485303 : Blo 483789 485303 := bstep (se 1 (by rfl) ⟨363977, by rfl⟩ : syracuseStep 485303 = 727955) B727955
theorem B485323 : Blo 483789 485323 := bstep (se 1 (by rfl) ⟨363992, by rfl⟩ : syracuseStep 485323 = 727985) B727985
theorem B485335 : Blo 483789 485335 := bstep (se 1 (by rfl) ⟨364001, by rfl⟩ : syracuseStep 485335 = 728003) B728003
theorem B518123 : Blo 483789 518123 := bstep (se 1 (by rfl) ⟨388592, by rfl⟩ : syracuseStep 518123 = 777185) B777185
theorem B485355 : Blo 483789 485355 := bstep (se 1 (by rfl) ⟨364016, by rfl⟩ : syracuseStep 485355 = 728033) B728033
theorem B485367 : Blo 483789 485367 := bstep (se 1 (by rfl) ⟨364025, by rfl⟩ : syracuseStep 485367 = 728051) B728051
theorem B485387 : Blo 483789 485387 := bstep (se 1 (by rfl) ⟨364040, by rfl⟩ : syracuseStep 485387 = 728081) B728081
theorem B485399 : Blo 483789 485399 := bstep (se 1 (by rfl) ⟨364049, by rfl⟩ : syracuseStep 485399 = 728099) B728099
theorem B780311 : Blo 483789 780311 := bstep (se 1 (by rfl) ⟨585233, by rfl⟩ : syracuseStep 780311 = 1170467) B1170467
theorem B485419 : Blo 483789 485419 := bstep (se 1 (by rfl) ⟨364064, by rfl⟩ : syracuseStep 485419 = 728129) B728129
theorem B485431 : Blo 483789 485431 := bstep (se 1 (by rfl) ⟨364073, by rfl⟩ : syracuseStep 485431 = 728147) B728147
theorem B485451 : Blo 483789 485451 := bstep (se 1 (by rfl) ⟨364088, by rfl⟩ : syracuseStep 485451 = 728177) B728177
theorem B485463 : Blo 483789 485463 := bstep (se 1 (by rfl) ⟨364097, by rfl⟩ : syracuseStep 485463 = 728195) B728195
theorem B485483 : Blo 483789 485483 := bstep (se 1 (by rfl) ⟨364112, by rfl⟩ : syracuseStep 485483 = 728225) B728225
theorem B485495 : Blo 483789 485495 := bstep (se 1 (by rfl) ⟨364121, by rfl⟩ : syracuseStep 485495 = 728243) B728243
theorem B485515 : Blo 483789 485515 := bstep (se 1 (by rfl) ⟨364136, by rfl⟩ : syracuseStep 485515 = 728273) B728273
theorem B485527 : Blo 483789 485527 := bstep (se 1 (by rfl) ⟨364145, by rfl⟩ : syracuseStep 485527 = 728291) B728291
theorem B485547 : Blo 483789 485547 := bstep (se 1 (by rfl) ⟨364160, by rfl⟩ : syracuseStep 485547 = 728321) B728321
theorem B485559 : Blo 483789 485559 := bstep (se 1 (by rfl) ⟨364169, by rfl⟩ : syracuseStep 485559 = 728339) B728339
theorem B485579 : Blo 483789 485579 := bstep (se 1 (by rfl) ⟨364184, by rfl⟩ : syracuseStep 485579 = 728369) B728369
theorem B485591 : Blo 483789 485591 := bstep (se 1 (by rfl) ⟨364193, by rfl⟩ : syracuseStep 485591 = 728387) B728387
theorem B616663 : Blo 483789 616663 := bstep (se 1 (by rfl) ⟨462497, by rfl⟩ : syracuseStep 616663 = 924995) B924995
theorem B485611 : Blo 483789 485611 := bstep (se 1 (by rfl) ⟨364208, by rfl⟩ : syracuseStep 485611 = 728417) B728417
theorem B485623 : Blo 483789 485623 := bstep (se 1 (by rfl) ⟨364217, by rfl⟩ : syracuseStep 485623 = 728435) B728435
theorem B485643 : Blo 483789 485643 := bstep (se 1 (by rfl) ⟨364232, by rfl⟩ : syracuseStep 485643 = 728465) B728465
theorem B485655 : Blo 483789 485655 := bstep (se 1 (by rfl) ⟨364241, by rfl⟩ : syracuseStep 485655 = 728483) B728483
theorem B485675 : Blo 483789 485675 := bstep (se 1 (by rfl) ⟨364256, by rfl⟩ : syracuseStep 485675 = 728513) B728513
theorem B485687 : Blo 483789 485687 := bstep (se 1 (by rfl) ⟨364265, by rfl⟩ : syracuseStep 485687 = 728531) B728531
theorem B485707 : Blo 483789 485707 := bstep (se 1 (by rfl) ⟨364280, by rfl⟩ : syracuseStep 485707 = 728561) B728561
theorem B780619 : Blo 483789 780619 := bstep (se 1 (by rfl) ⟨585464, by rfl⟩ : syracuseStep 780619 = 1170929) B1170929
theorem B485719 : Blo 483789 485719 := bstep (se 1 (by rfl) ⟨364289, by rfl⟩ : syracuseStep 485719 = 728579) B728579
theorem B485739 : Blo 483789 485739 := bstep (se 1 (by rfl) ⟨364304, by rfl⟩ : syracuseStep 485739 = 728609) B728609
theorem B485751 : Blo 483789 485751 := bstep (se 1 (by rfl) ⟨364313, by rfl⟩ : syracuseStep 485751 = 728627) B728627
theorem B485771 : Blo 483789 485771 := bstep (se 1 (by rfl) ⟨364328, by rfl⟩ : syracuseStep 485771 = 728657) B728657
theorem B485783 : Blo 483789 485783 := bstep (se 1 (by rfl) ⟨364337, by rfl⟩ : syracuseStep 485783 = 728675) B728675
theorem B485803 : Blo 483789 485803 := bstep (se 1 (by rfl) ⟨364352, by rfl⟩ : syracuseStep 485803 = 728705) B728705
theorem B485815 : Blo 483789 485815 := bstep (se 1 (by rfl) ⟨364361, by rfl⟩ : syracuseStep 485815 = 728723) B728723
theorem B485835 : Blo 483789 485835 := bstep (se 1 (by rfl) ⟨364376, by rfl⟩ : syracuseStep 485835 = 728753) B728753
theorem B485847 : Blo 483789 485847 := bstep (se 1 (by rfl) ⟨364385, by rfl⟩ : syracuseStep 485847 = 728771) B728771
theorem B485867 : Blo 483789 485867 := bstep (se 1 (by rfl) ⟨364400, by rfl⟩ : syracuseStep 485867 = 728801) B728801
theorem B485879 : Blo 483789 485879 := bstep (se 1 (by rfl) ⟨364409, by rfl⟩ : syracuseStep 485879 = 728819) B728819
theorem B485899 : Blo 483789 485899 := bstep (se 1 (by rfl) ⟨364424, by rfl⟩ : syracuseStep 485899 = 728849) B728849
theorem B485911 : Blo 483789 485911 := bstep (se 1 (by rfl) ⟨364433, by rfl⟩ : syracuseStep 485911 = 728867) B728867
theorem B485931 : Blo 483789 485931 := bstep (se 1 (by rfl) ⟨364448, by rfl⟩ : syracuseStep 485931 = 728897) B728897
theorem B485943 : Blo 483789 485943 := bstep (se 1 (by rfl) ⟨364457, by rfl⟩ : syracuseStep 485943 = 728915) B728915
theorem B485963 : Blo 483789 485963 := bstep (se 1 (by rfl) ⟨364472, by rfl⟩ : syracuseStep 485963 = 728945) B728945
theorem B485975 : Blo 483789 485975 := bstep (se 1 (by rfl) ⟨364481, by rfl⟩ : syracuseStep 485975 = 728963) B728963
theorem B485995 : Blo 483789 485995 := bstep (se 1 (by rfl) ⟨364496, by rfl⟩ : syracuseStep 485995 = 728993) B728993
theorem B486007 : Blo 483789 486007 := bstep (se 1 (by rfl) ⟨364505, by rfl⟩ : syracuseStep 486007 = 729011) B729011
theorem B486027 : Blo 483789 486027 := bstep (se 1 (by rfl) ⟨364520, by rfl⟩ : syracuseStep 486027 = 729041) B729041
theorem B486039 : Blo 483789 486039 := bstep (se 1 (by rfl) ⟨364529, by rfl⟩ : syracuseStep 486039 = 729059) B729059
theorem B486059 : Blo 483789 486059 := bstep (se 1 (by rfl) ⟨364544, by rfl⟩ : syracuseStep 486059 = 729089) B729089
theorem B486071 : Blo 483789 486071 := bstep (se 1 (by rfl) ⟨364553, by rfl⟩ : syracuseStep 486071 = 729107) B729107
theorem B486091 : Blo 483789 486091 := bstep (se 1 (by rfl) ⟨364568, by rfl⟩ : syracuseStep 486091 = 729137) B729137
theorem B486103 : Blo 483789 486103 := bstep (se 1 (by rfl) ⟨364577, by rfl⟩ : syracuseStep 486103 = 729155) B729155
theorem B486123 : Blo 483789 486123 := bstep (se 1 (by rfl) ⟨364592, by rfl⟩ : syracuseStep 486123 = 729185) B729185
theorem B486135 : Blo 483789 486135 := bstep (se 1 (by rfl) ⟨364601, by rfl⟩ : syracuseStep 486135 = 729203) B729203
theorem B486155 : Blo 483789 486155 := bstep (se 1 (by rfl) ⟨364616, by rfl⟩ : syracuseStep 486155 = 729233) B729233
theorem B781067 : Blo 483789 781067 := bstep (se 1 (by rfl) ⟨585800, by rfl⟩ : syracuseStep 781067 = 1171601) B1171601
theorem B486167 : Blo 483789 486167 := bstep (se 1 (by rfl) ⟨364625, by rfl⟩ : syracuseStep 486167 = 729251) B729251
theorem B486187 : Blo 483789 486187 := bstep (se 1 (by rfl) ⟨364640, by rfl⟩ : syracuseStep 486187 = 729281) B729281
theorem B486199 : Blo 483789 486199 := bstep (se 1 (by rfl) ⟨364649, by rfl⟩ : syracuseStep 486199 = 729299) B729299
theorem B3107659 : Blo 483789 3107659 := bstep (se 1 (by rfl) ⟨2330744, by rfl⟩ : syracuseStep 3107659 = 4661489) B4661489
theorem B486219 : Blo 483789 486219 := bstep (se 1 (by rfl) ⟨364664, by rfl⟩ : syracuseStep 486219 = 729329) B729329
theorem B486231 : Blo 483789 486231 := bstep (se 1 (by rfl) ⟨364673, by rfl⟩ : syracuseStep 486231 = 729347) B729347
theorem B486251 : Blo 483789 486251 := bstep (se 1 (by rfl) ⟨364688, by rfl⟩ : syracuseStep 486251 = 729377) B729377
theorem B486263 : Blo 483789 486263 := bstep (se 1 (by rfl) ⟨364697, by rfl⟩ : syracuseStep 486263 = 729395) B729395
theorem B2452355 : Blo 483789 2452355 := bstep (se 1 (by rfl) ⟨1839266, by rfl⟩ : syracuseStep 2452355 = 3678533) B3678533
theorem B486283 : Blo 483789 486283 := bstep (se 1 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 486283 = 729425) B729425
theorem B1633175 : Blo 483789 1633175 := bstep (se 1 (by rfl) ⟨1224881, by rfl⟩ : syracuseStep 1633175 = 2449763) B2449763
theorem B486295 : Blo 483789 486295 := bstep (se 1 (by rfl) ⟨364721, by rfl⟩ : syracuseStep 486295 = 729443) B729443
theorem B486315 : Blo 483789 486315 := bstep (se 1 (by rfl) ⟨364736, by rfl⟩ : syracuseStep 486315 = 729473) B729473
theorem B486327 : Blo 483789 486327 := bstep (se 1 (by rfl) ⟨364745, by rfl⟩ : syracuseStep 486327 = 729491) B729491
theorem B486347 : Blo 483789 486347 := bstep (se 1 (by rfl) ⟨364760, by rfl⟩ : syracuseStep 486347 = 729521) B729521
theorem B486359 : Blo 483789 486359 := bstep (se 1 (by rfl) ⟨364769, by rfl⟩ : syracuseStep 486359 = 729539) B729539
theorem B486379 : Blo 483789 486379 := bstep (se 1 (by rfl) ⟨364784, by rfl⟩ : syracuseStep 486379 = 729569) B729569
theorem B486391 : Blo 483789 486391 := bstep (se 1 (by rfl) ⟨364793, by rfl⟩ : syracuseStep 486391 = 729587) B729587
theorem B486411 : Blo 483789 486411 := bstep (se 1 (by rfl) ⟨364808, by rfl⟩ : syracuseStep 486411 = 729617) B729617
theorem B486423 : Blo 483789 486423 := bstep (se 1 (by rfl) ⟨364817, by rfl⟩ : syracuseStep 486423 = 729635) B729635
theorem B486443 : Blo 483789 486443 := bstep (se 1 (by rfl) ⟨364832, by rfl⟩ : syracuseStep 486443 = 729665) B729665
theorem B486455 : Blo 483789 486455 := bstep (se 1 (by rfl) ⟨364841, by rfl⟩ : syracuseStep 486455 = 729683) B729683
theorem B486475 : Blo 483789 486475 := bstep (se 1 (by rfl) ⟨364856, by rfl⟩ : syracuseStep 486475 = 729713) B729713
theorem B486487 : Blo 483789 486487 := bstep (se 1 (by rfl) ⟨364865, by rfl⟩ : syracuseStep 486487 = 729731) B729731
theorem B486507 : Blo 483789 486507 := bstep (se 1 (by rfl) ⟨364880, by rfl⟩ : syracuseStep 486507 = 729761) B729761
theorem B486519 : Blo 483789 486519 := bstep (se 1 (by rfl) ⟨364889, by rfl⟩ : syracuseStep 486519 = 729779) B729779
theorem B486539 : Blo 483789 486539 := bstep (se 1 (by rfl) ⟨364904, by rfl⟩ : syracuseStep 486539 = 729809) B729809
theorem B519319 : Blo 483789 519319 := bstep (se 1 (by rfl) ⟨389489, by rfl⟩ : syracuseStep 519319 = 778979) B778979
theorem B486551 : Blo 483789 486551 := bstep (se 1 (by rfl) ⟨364913, by rfl⟩ : syracuseStep 486551 = 729827) B729827
theorem B486571 : Blo 483789 486571 := bstep (se 1 (by rfl) ⟨364928, by rfl⟩ : syracuseStep 486571 = 729857) B729857
theorem B486583 : Blo 483789 486583 := bstep (se 1 (by rfl) ⟨364937, by rfl⟩ : syracuseStep 486583 = 729875) B729875
theorem B486603 : Blo 483789 486603 := bstep (se 1 (by rfl) ⟨364952, by rfl⟩ : syracuseStep 486603 = 729905) B729905
theorem B486615 : Blo 483789 486615 := bstep (se 1 (by rfl) ⟨364961, by rfl⟩ : syracuseStep 486615 = 729923) B729923
theorem B486635 : Blo 483789 486635 := bstep (se 1 (by rfl) ⟨364976, by rfl⟩ : syracuseStep 486635 = 729953) B729953
theorem B486647 : Blo 483789 486647 := bstep (se 1 (by rfl) ⟨364985, by rfl⟩ : syracuseStep 486647 = 729971) B729971
theorem B486667 : Blo 483789 486667 := bstep (se 1 (by rfl) ⟨365000, by rfl⟩ : syracuseStep 486667 = 730001) B730001
theorem B486679 : Blo 483789 486679 := bstep (se 1 (by rfl) ⟨365009, by rfl⟩ : syracuseStep 486679 = 730019) B730019
theorem B486699 : Blo 483789 486699 := bstep (se 1 (by rfl) ⟨365024, by rfl⟩ : syracuseStep 486699 = 730049) B730049
theorem B486711 : Blo 483789 486711 := bstep (se 1 (by rfl) ⟨365033, by rfl⟩ : syracuseStep 486711 = 730067) B730067
theorem B486731 : Blo 483789 486731 := bstep (se 1 (by rfl) ⟨365048, by rfl⟩ : syracuseStep 486731 = 730097) B730097
theorem B486743 : Blo 483789 486743 := bstep (se 1 (by rfl) ⟨365057, by rfl⟩ : syracuseStep 486743 = 730115) B730115
theorem B3796325 : Blo 483789 3796325 := bstep (se 4 (by rfl) ⟨355905, by rfl⟩ : syracuseStep 3796325 = 711811) B711811
theorem B486763 : Blo 483789 486763 := bstep (se 1 (by rfl) ⟨365072, by rfl⟩ : syracuseStep 486763 = 730145) B730145
theorem B486775 : Blo 483789 486775 := bstep (se 1 (by rfl) ⟨365081, by rfl⟩ : syracuseStep 486775 = 730163) B730163
theorem B486795 : Blo 483789 486795 := bstep (se 1 (by rfl) ⟨365096, by rfl⟩ : syracuseStep 486795 = 730193) B730193
theorem B486807 : Blo 483789 486807 := bstep (se 1 (by rfl) ⟨365105, by rfl⟩ : syracuseStep 486807 = 730211) B730211
theorem B486827 : Blo 483789 486827 := bstep (se 1 (by rfl) ⟨365120, by rfl⟩ : syracuseStep 486827 = 730241) B730241
theorem B1633715 : Blo 483789 1633715 := bstep (se 1 (by rfl) ⟨1225286, by rfl⟩ : syracuseStep 1633715 = 2450573) B2450573
theorem B486839 : Blo 483789 486839 := bstep (se 1 (by rfl) ⟨365129, by rfl⟩ : syracuseStep 486839 = 730259) B730259
theorem B486859 : Blo 483789 486859 := bstep (se 1 (by rfl) ⟨365144, by rfl⟩ : syracuseStep 486859 = 730289) B730289
theorem B486871 : Blo 483789 486871 := bstep (se 1 (by rfl) ⟨365153, by rfl⟩ : syracuseStep 486871 = 730307) B730307
theorem B486891 : Blo 483789 486891 := bstep (se 1 (by rfl) ⟨365168, by rfl⟩ : syracuseStep 486891 = 730337) B730337
theorem B486903 : Blo 483789 486903 := bstep (se 1 (by rfl) ⟨365177, by rfl⟩ : syracuseStep 486903 = 730355) B730355
theorem B486923 : Blo 483789 486923 := bstep (se 1 (by rfl) ⟨365192, by rfl⟩ : syracuseStep 486923 = 730385) B730385
theorem B486935 : Blo 483789 486935 := bstep (se 1 (by rfl) ⟨365201, by rfl⟩ : syracuseStep 486935 = 730403) B730403
theorem B486955 : Blo 483789 486955 := bstep (se 1 (by rfl) ⟨365216, by rfl⟩ : syracuseStep 486955 = 730433) B730433
theorem B486967 : Blo 483789 486967 := bstep (se 1 (by rfl) ⟨365225, by rfl⟩ : syracuseStep 486967 = 730451) B730451
theorem B486987 : Blo 483789 486987 := bstep (se 1 (by rfl) ⟨365240, by rfl⟩ : syracuseStep 486987 = 730481) B730481
theorem B486999 : Blo 483789 486999 := bstep (se 1 (by rfl) ⟨365249, by rfl⟩ : syracuseStep 486999 = 730499) B730499
theorem B487019 : Blo 483789 487019 := bstep (se 1 (by rfl) ⟨365264, by rfl⟩ : syracuseStep 487019 = 730529) B730529
theorem B487031 : Blo 483789 487031 := bstep (se 1 (by rfl) ⟨365273, by rfl⟩ : syracuseStep 487031 = 730547) B730547
theorem B487051 : Blo 483789 487051 := bstep (se 1 (by rfl) ⟨365288, by rfl⟩ : syracuseStep 487051 = 730577) B730577
theorem B487063 : Blo 483789 487063 := bstep (se 1 (by rfl) ⟨365297, by rfl⟩ : syracuseStep 487063 = 730595) B730595
theorem B487083 : Blo 483789 487083 := bstep (se 1 (by rfl) ⟨365312, by rfl⟩ : syracuseStep 487083 = 730625) B730625
theorem B487095 : Blo 483789 487095 := bstep (se 1 (by rfl) ⟨365321, by rfl⟩ : syracuseStep 487095 = 730643) B730643
theorem B1633985 : Blo 483789 1633985 := bstep (se 2 (by rfl) ⟨612744, by rfl⟩ : syracuseStep 1633985 = 1225489) B1225489
theorem B487115 : Blo 483789 487115 := bstep (se 1 (by rfl) ⟨365336, by rfl⟩ : syracuseStep 487115 = 730673) B730673
theorem B487127 : Blo 483789 487127 := bstep (se 1 (by rfl) ⟨365345, by rfl⟩ : syracuseStep 487127 = 730691) B730691
theorem B487147 : Blo 483789 487147 := bstep (se 1 (by rfl) ⟨365360, by rfl⟩ : syracuseStep 487147 = 730721) B730721
theorem B6942449 : Blo 483789 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B487159 : Blo 483789 487159 := bstep (se 1 (by rfl) ⟨365369, by rfl⟩ : syracuseStep 487159 = 730739) B730739
theorem B487179 : Blo 483789 487179 := bstep (se 1 (by rfl) ⟨365384, by rfl⟩ : syracuseStep 487179 = 730769) B730769
theorem B487191 : Blo 483789 487191 := bstep (se 1 (by rfl) ⟨365393, by rfl⟩ : syracuseStep 487191 = 730787) B730787
theorem B487211 : Blo 483789 487211 := bstep (se 1 (by rfl) ⟨365408, by rfl⟩ : syracuseStep 487211 = 730817) B730817
theorem B487223 : Blo 483789 487223 := bstep (se 1 (by rfl) ⟨365417, by rfl⟩ : syracuseStep 487223 = 730835) B730835
theorem B487243 : Blo 483789 487243 := bstep (se 1 (by rfl) ⟨365432, by rfl⟩ : syracuseStep 487243 = 730865) B730865
theorem B487255 : Blo 483789 487255 := bstep (se 1 (by rfl) ⟨365441, by rfl⟩ : syracuseStep 487255 = 730883) B730883
theorem B4222813 : Blo 483789 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B487275 : Blo 483789 487275 := bstep (se 1 (by rfl) ⟨365456, by rfl⟩ : syracuseStep 487275 = 730913) B730913
theorem B487287 : Blo 483789 487287 := bstep (se 1 (by rfl) ⟨365465, by rfl⟩ : syracuseStep 487287 = 730931) B730931
theorem B487307 : Blo 483789 487307 := bstep (se 1 (by rfl) ⟨365480, by rfl⟩ : syracuseStep 487307 = 730961) B730961
theorem B487319 : Blo 483789 487319 := bstep (se 1 (by rfl) ⟨365489, by rfl⟩ : syracuseStep 487319 = 730979) B730979
theorem B487339 : Blo 483789 487339 := bstep (se 1 (by rfl) ⟨365504, by rfl⟩ : syracuseStep 487339 = 731009) B731009
theorem B487351 : Blo 483789 487351 := bstep (se 1 (by rfl) ⟨365513, by rfl⟩ : syracuseStep 487351 = 731027) B731027
theorem B520139 : Blo 483789 520139 := bstep (se 1 (by rfl) ⟨390104, by rfl⟩ : syracuseStep 520139 = 780209) B780209
theorem B487371 : Blo 483789 487371 := bstep (se 1 (by rfl) ⟨365528, by rfl⟩ : syracuseStep 487371 = 731057) B731057
theorem B487383 : Blo 483789 487383 := bstep (se 1 (by rfl) ⟨365537, by rfl⟩ : syracuseStep 487383 = 731075) B731075
theorem B487403 : Blo 483789 487403 := bstep (se 1 (by rfl) ⟨365552, by rfl⟩ : syracuseStep 487403 = 731105) B731105
theorem B487415 : Blo 483789 487415 := bstep (se 1 (by rfl) ⟨365561, by rfl⟩ : syracuseStep 487415 = 731123) B731123
theorem B487435 : Blo 483789 487435 := bstep (se 1 (by rfl) ⟨365576, by rfl⟩ : syracuseStep 487435 = 731153) B731153
theorem B487447 : Blo 483789 487447 := bstep (se 1 (by rfl) ⟨365585, by rfl⟩ : syracuseStep 487447 = 731171) B731171
theorem B487467 : Blo 483789 487467 := bstep (se 1 (by rfl) ⟨365600, by rfl⟩ : syracuseStep 487467 = 731201) B731201
theorem B487479 : Blo 483789 487479 := bstep (se 1 (by rfl) ⟨365609, by rfl⟩ : syracuseStep 487479 = 731219) B731219
theorem B520267 : Blo 483789 520267 := bstep (se 1 (by rfl) ⟨390200, by rfl⟩ : syracuseStep 520267 = 780401) B780401
theorem B487499 : Blo 483789 487499 := bstep (se 1 (by rfl) ⟨365624, by rfl⟩ : syracuseStep 487499 = 731249) B731249
theorem B487511 : Blo 483789 487511 := bstep (se 1 (by rfl) ⟨365633, by rfl⟩ : syracuseStep 487511 = 731267) B731267
theorem B487531 : Blo 483789 487531 := bstep (se 1 (by rfl) ⟨365648, by rfl⟩ : syracuseStep 487531 = 731297) B731297
theorem B487543 : Blo 483789 487543 := bstep (se 1 (by rfl) ⟨365657, by rfl⟩ : syracuseStep 487543 = 731315) B731315
theorem B487563 : Blo 483789 487563 := bstep (se 1 (by rfl) ⟨365672, by rfl⟩ : syracuseStep 487563 = 731345) B731345
theorem B487575 : Blo 483789 487575 := bstep (se 1 (by rfl) ⟨365681, by rfl⟩ : syracuseStep 487575 = 731363) B731363
theorem B487595 : Blo 483789 487595 := bstep (se 1 (by rfl) ⟨365696, by rfl⟩ : syracuseStep 487595 = 731393) B731393
theorem B487607 : Blo 483789 487607 := bstep (se 1 (by rfl) ⟨365705, by rfl⟩ : syracuseStep 487607 = 731411) B731411
theorem B487627 : Blo 483789 487627 := bstep (se 1 (by rfl) ⟨365720, by rfl⟩ : syracuseStep 487627 = 731441) B731441
theorem B487639 : Blo 483789 487639 := bstep (se 1 (by rfl) ⟨365729, by rfl⟩ : syracuseStep 487639 = 731459) B731459
theorem B1634525 : Blo 483789 1634525 := bstep (se 3 (by rfl) ⟨306473, by rfl⟩ : syracuseStep 1634525 = 612947) B612947
theorem B487659 : Blo 483789 487659 := bstep (se 1 (by rfl) ⟨365744, by rfl⟩ : syracuseStep 487659 = 731489) B731489
theorem B487671 : Blo 483789 487671 := bstep (se 1 (by rfl) ⟨365753, by rfl⟩ : syracuseStep 487671 = 731507) B731507
theorem B487691 : Blo 483789 487691 := bstep (se 1 (by rfl) ⟨365768, by rfl⟩ : syracuseStep 487691 = 731537) B731537
theorem B487703 : Blo 483789 487703 := bstep (se 1 (by rfl) ⟨365777, by rfl⟩ : syracuseStep 487703 = 731555) B731555
theorem B487723 : Blo 483789 487723 := bstep (se 1 (by rfl) ⟨365792, by rfl⟩ : syracuseStep 487723 = 731585) B731585
theorem B487735 : Blo 483789 487735 := bstep (se 1 (by rfl) ⟨365801, by rfl⟩ : syracuseStep 487735 = 731603) B731603
theorem B487755 : Blo 483789 487755 := bstep (se 1 (by rfl) ⟨365816, by rfl⟩ : syracuseStep 487755 = 731633) B731633
theorem B487767 : Blo 483789 487767 := bstep (se 1 (by rfl) ⟨365825, by rfl⟩ : syracuseStep 487767 = 731651) B731651
theorem B487787 : Blo 483789 487787 := bstep (se 1 (by rfl) ⟨365840, by rfl⟩ : syracuseStep 487787 = 731681) B731681
theorem B1405619 : Blo 483789 1405619 := bstep (se 1 (by rfl) ⟨1054214, by rfl⟩ : syracuseStep 1405619 = 2108429) B2108429
theorem B1962803 : Blo 483789 1962803 := bstep (se 1 (by rfl) ⟨1472102, by rfl⟩ : syracuseStep 1962803 = 2944205) B2944205
theorem B17953589 : Blo 483789 17953589 := bstep (se 5 (by rfl) ⟨841574, by rfl⟩ : syracuseStep 17953589 = 1683149) B1683149
theorem B3699917 : Blo 483789 3699917 := bstep (se 3 (by rfl) ⟨693734, by rfl⟩ : syracuseStep 3699917 = 1387469) B1387469
theorem B1635659 : Blo 483789 1635659 := bstep (se 1 (by rfl) ⟨1226744, by rfl⟩ : syracuseStep 1635659 = 2453489) B2453489
theorem B816473 : Blo 483789 816473 := bstep (se 2 (by rfl) ⟨306177, by rfl⟩ : syracuseStep 816473 = 612355) B612355
theorem B554347 : Blo 483789 554347 := bstep (se 1 (by rfl) ⟨415760, by rfl⟩ : syracuseStep 554347 = 831521) B831521
theorem B816601 : Blo 483789 816601 := bstep (se 2 (by rfl) ⟨306225, by rfl⟩ : syracuseStep 816601 = 612451) B612451
theorem B1635929 : Blo 483789 1635929 := bstep (se 2 (by rfl) ⟨613473, by rfl⟩ : syracuseStep 1635929 = 1226947) B1226947
theorem B4159127 : Blo 483789 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B3700403 : Blo 483789 3700403 := bstep (se 1 (by rfl) ⟨2775302, by rfl⟩ : syracuseStep 3700403 = 5550605) B5550605
theorem B1275671 : Blo 483789 1275671 := bstep (se 1 (by rfl) ⟨956753, by rfl⟩ : syracuseStep 1275671 = 1913507) B1913507
theorem B2094913 : Blo 483789 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B980851 : Blo 483789 980851 := bstep (se 1 (by rfl) ⟨735638, by rfl⟩ : syracuseStep 980851 = 1471277) B1471277
theorem B7010225 : Blo 483789 7010225 := bstep (se 2 (by rfl) ⟨2628834, by rfl⟩ : syracuseStep 7010225 = 5257669) B5257669
theorem B817175 : Blo 483789 817175 := bstep (se 1 (by rfl) ⟨612881, by rfl⟩ : syracuseStep 817175 = 1225763) B1225763
theorem B555031 : Blo 483789 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B817303 : Blo 483789 817303 := bstep (se 1 (by rfl) ⟨612977, by rfl⟩ : syracuseStep 817303 = 1225955) B1225955
theorem B1112215 : Blo 483789 1112215 := bstep (se 1 (by rfl) ⟨834161, by rfl⟩ : syracuseStep 1112215 = 1668323) B1668323
theorem B1636631 : Blo 483789 1636631 := bstep (se 1 (by rfl) ⟨1227473, by rfl⟩ : syracuseStep 1636631 = 2454947) B2454947
theorem B11794733 : Blo 483789 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B8288729 : Blo 483789 8288729 := bstep (se 2 (by rfl) ⟨3108273, by rfl⟩ : syracuseStep 8288729 = 6216547) B6216547
theorem B2456081 : Blo 483789 2456081 := bstep (se 2 (by rfl) ⟨921030, by rfl⟩ : syracuseStep 2456081 = 1842061) B1842061
theorem B4651613 : Blo 483789 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B2456243 : Blo 483789 2456243 := bstep (se 1 (by rfl) ⟨1842182, by rfl⟩ : syracuseStep 2456243 = 3684365) B3684365
theorem B1178315 : Blo 483789 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B817931 : Blo 483789 817931 := bstep (se 1 (by rfl) ⟨613448, by rfl⟩ : syracuseStep 817931 = 1226897) B1226897
theorem B3504941 : Blo 483789 3504941 := bstep (se 3 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 3504941 = 1314353) B1314353
theorem B1637171 : Blo 483789 1637171 := bstep (se 1 (by rfl) ⟨1227878, by rfl⟩ : syracuseStep 1637171 = 2455757) B2455757
theorem B818059 : Blo 483789 818059 := bstep (se 1 (by rfl) ⟨613544, by rfl⟩ : syracuseStep 818059 = 1227089) B1227089
theorem B4651955 : Blo 483789 4651955 := bstep (se 1 (by rfl) ⟨3488966, by rfl⟩ : syracuseStep 4651955 = 6977933) B6977933
theorem B1309661 : Blo 483789 1309661 := bstep (se 3 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 1309661 = 491123) B491123
theorem B818201 : Blo 483789 818201 := bstep (se 2 (by rfl) ⟨306825, by rfl⟩ : syracuseStep 818201 = 613651) B613651
theorem B1637441 : Blo 483789 1637441 := bstep (se 2 (by rfl) ⟨614040, by rfl⟩ : syracuseStep 1637441 = 1228081) B1228081
theorem B490571 : Blo 483789 490571 := bstep (se 1 (by rfl) ⟨367928, by rfl⟩ : syracuseStep 490571 = 735857) B735857
theorem B1473611 : Blo 483789 1473611 := bstep (se 1 (by rfl) ⟨1105208, by rfl⟩ : syracuseStep 1473611 = 2210417) B2210417
theorem B3701861 : Blo 483789 3701861 := bstep (se 4 (by rfl) ⟨347049, by rfl⟩ : syracuseStep 3701861 = 694099) B694099
theorem B818329 : Blo 483789 818329 := bstep (se 2 (by rfl) ⟨306873, by rfl⟩ : syracuseStep 818329 = 613747) B613747
theorem B4161041 : Blo 483789 4161041 := bstep (se 2 (by rfl) ⟨1560390, by rfl⟩ : syracuseStep 4161041 = 3120781) B3120781
theorem B3702347 : Blo 483789 3702347 := bstep (se 1 (by rfl) ⟨2776760, by rfl⟩ : syracuseStep 3702347 = 5553521) B5553521
theorem B1637981 : Blo 483789 1637981 := bstep (se 3 (by rfl) ⟨307121, by rfl⟩ : syracuseStep 1637981 = 614243) B614243
theorem B31620739 : Blo 483789 31620739 := bstep (se 1 (by rfl) ⟨23715554, by rfl⟩ : syracuseStep 31620739 = 47431109) B47431109
theorem B818903 : Blo 483789 818903 := bstep (se 1 (by rfl) ⟨614177, by rfl⟩ : syracuseStep 818903 = 1228355) B1228355
theorem B4685633 : Blo 483789 4685633 := bstep (se 2 (by rfl) ⟨1757112, by rfl⟩ : syracuseStep 4685633 = 3514225) B3514225
theorem B819031 : Blo 483789 819031 := bstep (se 1 (by rfl) ⟨614273, by rfl⟩ : syracuseStep 819031 = 1228547) B1228547
theorem B1179481 : Blo 483789 1179481 := bstep (se 2 (by rfl) ⟨442305, by rfl⟩ : syracuseStep 1179481 = 884611) B884611
theorem B1965917 : Blo 483789 1965917 := bstep (se 3 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 1965917 = 737219) B737219
theorem B819335 : Blo 483789 819335 := bstep (se 1 (by rfl) ⟨614501, by rfl⟩ : syracuseStep 819335 = 1229003) B1229003
theorem B4686173 : Blo 483789 4686173 := bstep (se 3 (by rfl) ⟨878657, by rfl⟩ : syracuseStep 4686173 = 1757315) B1757315
theorem B1638791 : Blo 483789 1638791 := bstep (se 1 (by rfl) ⟨1229093, by rfl⟩ : syracuseStep 1638791 = 2458187) B2458187
theorem B4653571 : Blo 483789 4653571 := bstep (se 1 (by rfl) ⟨3490178, by rfl⟩ : syracuseStep 4653571 = 6980357) B6980357
theorem B2425373 : Blo 483789 2425373 := bstep (se 3 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 2425373 = 909515) B909515
theorem B1868489 : Blo 483789 1868489 := bstep (se 2 (by rfl) ⟨700683, by rfl⟩ : syracuseStep 1868489 = 1401367) B1401367
theorem B2458349 : Blo 483789 2458349 := bstep (se 3 (by rfl) ⟨460940, by rfl⟩ : syracuseStep 2458349 = 921881) B921881
theorem B1639169 : Blo 483789 1639169 := bstep (se 2 (by rfl) ⟨614688, by rfl⟩ : syracuseStep 1639169 = 1229377) B1229377
theorem B819983 : Blo 483789 819983 := bstep (se 1 (by rfl) ⟨614987, by rfl⟩ : syracuseStep 819983 = 1229975) B1229975
theorem B820523 : Blo 483789 820523 := bstep (se 1 (by rfl) ⟨615392, by rfl⟩ : syracuseStep 820523 = 1230785) B1230785
theorem B4982147 : Blo 483789 4982147 := bstep (se 1 (by rfl) ⟨3736610, by rfl⟩ : syracuseStep 4982147 = 7473221) B7473221
theorem B3114425 : Blo 483789 3114425 := bstep (se 2 (by rfl) ⟨1167909, by rfl⟩ : syracuseStep 3114425 = 2335819) B2335819
theorem B2459159 : Blo 483789 2459159 := bstep (se 1 (by rfl) ⟨1844369, by rfl⟩ : syracuseStep 2459159 = 3688739) B3688739
theorem B2885149 : Blo 483789 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B1639979 : Blo 483789 1639979 := bstep (se 1 (by rfl) ⟨1229984, by rfl⟩ : syracuseStep 1639979 = 2459969) B2459969
theorem B689737 : Blo 483789 689737 := bstep (se 2 (by rfl) ⟨258651, by rfl⟩ : syracuseStep 689737 = 517303) B517303
theorem B820921 : Blo 483789 820921 := bstep (se 2 (by rfl) ⟨307845, by rfl⟩ : syracuseStep 820921 = 615691) B615691
theorem B4687631 : Blo 483789 4687631 := bstep (se 1 (by rfl) ⟨3515723, by rfl⟩ : syracuseStep 4687631 = 7031447) B7031447
theorem B690295 : Blo 483789 690295 := bstep (se 1 (by rfl) ⟨517721, by rfl⟩ : syracuseStep 690295 = 1035443) B1035443
theorem B919687 : Blo 483789 919687 := bstep (se 1 (by rfl) ⟨689765, by rfl⟩ : syracuseStep 919687 = 1379531) B1379531
theorem B985223 : Blo 483789 985223 := bstep (se 1 (by rfl) ⟨738917, by rfl⟩ : syracuseStep 985223 = 1477835) B1477835
theorem B1313111 : Blo 483789 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B821623 : Blo 483789 821623 := bstep (se 1 (by rfl) ⟨616217, by rfl⟩ : syracuseStep 821623 = 1232435) B1232435
theorem B1378745 : Blo 483789 1378745 := bstep (se 2 (by rfl) ⟨517029, by rfl⟩ : syracuseStep 1378745 = 1034059) B1034059
theorem B821819 : Blo 483789 821819 := bstep (se 1 (by rfl) ⟨616364, by rfl⟩ : syracuseStep 821819 = 1232729) B1232729
theorem B1837687 : Blo 483789 1837687 := bstep (se 1 (by rfl) ⟨1378265, by rfl⟩ : syracuseStep 1837687 = 2756531) B2756531
theorem B690859 : Blo 483789 690859 := bstep (se 1 (by rfl) ⟨518144, by rfl⟩ : syracuseStep 690859 = 1036289) B1036289
theorem B1641275 : Blo 483789 1641275 := bstep (se 1 (by rfl) ⟨1230956, by rfl⟩ : syracuseStep 1641275 = 2461913) B2461913
theorem B691087 : Blo 483789 691087 := bstep (se 1 (by rfl) ⟨518315, by rfl⟩ : syracuseStep 691087 = 1036631) B1036631
theorem B986041 : Blo 483789 986041 := bstep (se 2 (by rfl) ⟨369765, by rfl⟩ : syracuseStep 986041 = 739531) B739531
theorem B822217 : Blo 483789 822217 := bstep (se 2 (by rfl) ⟨308331, by rfl⟩ : syracuseStep 822217 = 616663) B616663
theorem B2362391 : Blo 483789 2362391 := bstep (se 1 (by rfl) ⟨1771793, by rfl⟩ : syracuseStep 2362391 = 3543587) B3543587
theorem B2624555 : Blo 483789 2624555 := bstep (se 1 (by rfl) ⟨1968416, by rfl⟩ : syracuseStep 2624555 = 3936833) B3936833
theorem B1641761 : Blo 483789 1641761 := bstep (se 2 (by rfl) ⟨615660, by rfl⟩ : syracuseStep 1641761 = 1231321) B1231321
theorem B3509725 : Blo 483789 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B1838659 : Blo 483789 1838659 := bstep (se 1 (by rfl) ⟨1378994, by rfl⟩ : syracuseStep 1838659 = 2757989) B2757989
theorem B822919 : Blo 483789 822919 := bstep (se 1 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 822919 = 1234379) B1234379
theorem B1379987 : Blo 483789 1379987 := bstep (se 1 (by rfl) ⟨1034990, by rfl⟩ : syracuseStep 1379987 = 2069981) B2069981
theorem B921289 : Blo 483789 921289 := bstep (se 2 (by rfl) ⟨345483, by rfl⟩ : syracuseStep 921289 = 690967) B690967
theorem B1838963 : Blo 483789 1838963 := bstep (se 1 (by rfl) ⟨1379222, by rfl⟩ : syracuseStep 1838963 = 2758445) B2758445
theorem B1642355 : Blo 483789 1642355 := bstep (se 1 (by rfl) ⟨1231766, by rfl⟩ : syracuseStep 1642355 = 2463533) B2463533
theorem B692231 : Blo 483789 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B987169 : Blo 483789 987169 := bstep (se 2 (by rfl) ⟨370188, by rfl⟩ : syracuseStep 987169 = 740377) B740377
theorem B3117143 : Blo 483789 3117143 := bstep (se 1 (by rfl) ⟨2337857, by rfl⟩ : syracuseStep 3117143 = 4675715) B4675715
theorem B692425 : Blo 483789 692425 := bstep (se 2 (by rfl) ⟨259659, by rfl⟩ : syracuseStep 692425 = 519319) B519319
theorem B1839419 : Blo 483789 1839419 := bstep (se 1 (by rfl) ⟨1379564, by rfl⟩ : syracuseStep 1839419 = 2759129) B2759129
theorem B1315187 : Blo 483789 1315187 := bstep (se 1 (by rfl) ⟨986390, by rfl⟩ : syracuseStep 1315187 = 1972781) B1972781
theorem B1315219 : Blo 483789 1315219 := bstep (se 1 (by rfl) ⟨986414, by rfl⟩ : syracuseStep 1315219 = 1972829) B1972829
theorem B2462237 : Blo 483789 2462237 := bstep (se 3 (by rfl) ⟨461669, by rfl⟩ : syracuseStep 2462237 = 923339) B923339
theorem B2757239 : Blo 483789 2757239 := bstep (se 1 (by rfl) ⟨2067929, by rfl⟩ : syracuseStep 2757239 = 4135859) B4135859
theorem B725705 : Blo 483789 725705 := bstep (se 2 (by rfl) ⟨272139, by rfl⟩ : syracuseStep 725705 = 544279) B544279
theorem B692983 : Blo 483789 692983 := bstep (se 1 (by rfl) ⟨519737, by rfl⟩ : syracuseStep 692983 = 1039475) B1039475
theorem B3937025 : Blo 483789 3937025 := bstep (se 2 (by rfl) ⟨1476384, by rfl⟩ : syracuseStep 3937025 = 2952769) B2952769
theorem B1839905 : Blo 483789 1839905 := bstep (se 2 (by rfl) ⟨689964, by rfl⟩ : syracuseStep 1839905 = 1379929) B1379929
theorem B10523429 : Blo 483789 10523429 := bstep (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) B1973143
theorem B725819 : Blo 483789 725819 := bstep (se 1 (by rfl) ⟨544364, by rfl⟩ : syracuseStep 725819 = 1088729) B1088729
theorem B725879 : Blo 483789 725879 := bstep (se 1 (by rfl) ⟨544409, by rfl⟩ : syracuseStep 725879 = 1088819) B1088819
theorem B725903 : Blo 483789 725903 := bstep (se 1 (by rfl) ⟨544427, by rfl⟩ : syracuseStep 725903 = 1088855) B1088855
theorem B725945 : Blo 483789 725945 := bstep (se 2 (by rfl) ⟨272229, by rfl⟩ : syracuseStep 725945 = 544459) B544459
theorem B2462723 : Blo 483789 2462723 := bstep (se 1 (by rfl) ⟨1847042, by rfl⟩ : syracuseStep 2462723 = 3694085) B3694085
theorem B726023 : Blo 483789 726023 := bstep (se 1 (by rfl) ⟨544517, by rfl⟩ : syracuseStep 726023 = 1089035) B1089035
theorem B1381387 : Blo 483789 1381387 := bstep (se 1 (by rfl) ⟨1036040, by rfl⟩ : syracuseStep 1381387 = 2072081) B2072081
theorem B726059 : Blo 483789 726059 := bstep (se 1 (by rfl) ⟨544544, by rfl⟩ : syracuseStep 726059 = 1089089) B1089089
theorem B726089 : Blo 483789 726089 := bstep (se 2 (by rfl) ⟨272283, by rfl⟩ : syracuseStep 726089 = 544567) B544567
theorem B2331821 : Blo 483789 2331821 := bstep (se 3 (by rfl) ⟨437216, by rfl⟩ : syracuseStep 2331821 = 874433) B874433
theorem B726203 : Blo 483789 726203 := bstep (se 1 (by rfl) ⟨544652, by rfl⟩ : syracuseStep 726203 = 1089305) B1089305
theorem B726263 : Blo 483789 726263 := bstep (se 1 (by rfl) ⟨544697, by rfl⟩ : syracuseStep 726263 = 1089395) B1089395
theorem B726287 : Blo 483789 726287 := bstep (se 1 (by rfl) ⟨544715, by rfl⟩ : syracuseStep 726287 = 1089431) B1089431
theorem B1381661 : Blo 483789 1381661 := bstep (se 3 (by rfl) ⟨259061, by rfl⟩ : syracuseStep 1381661 = 518123) B518123
theorem B1316125 : Blo 483789 1316125 := bstep (se 3 (by rfl) ⟨246773, by rfl⟩ : syracuseStep 1316125 = 493547) B493547
theorem B726329 : Blo 483789 726329 := bstep (se 2 (by rfl) ⟨272373, by rfl⟩ : syracuseStep 726329 = 544747) B544747
theorem B726407 : Blo 483789 726407 := bstep (se 1 (by rfl) ⟨544805, by rfl⟩ : syracuseStep 726407 = 1089611) B1089611
theorem B5543315 : Blo 483789 5543315 := bstep (se 1 (by rfl) ⟨4157486, by rfl⟩ : syracuseStep 5543315 = 8314973) B8314973
theorem B726443 : Blo 483789 726443 := bstep (se 1 (by rfl) ⟨544832, by rfl⟩ : syracuseStep 726443 = 1089665) B1089665
theorem B1185209 : Blo 483789 1185209 := bstep (se 2 (by rfl) ⟨444453, by rfl⟩ : syracuseStep 1185209 = 888907) B888907
theorem B693689 : Blo 483789 693689 := bstep (se 2 (by rfl) ⟨260133, by rfl⟩ : syracuseStep 693689 = 520267) B520267
theorem B726473 : Blo 483789 726473 := bstep (se 2 (by rfl) ⟨272427, by rfl⟩ : syracuseStep 726473 = 544855) B544855
theorem B693775 : Blo 483789 693775 := bstep (se 1 (by rfl) ⟨520331, by rfl⟩ : syracuseStep 693775 = 1040663) B1040663
theorem B693803 : Blo 483789 693803 := bstep (se 1 (by rfl) ⟨520352, by rfl⟩ : syracuseStep 693803 = 1040705) B1040705
theorem B726587 : Blo 483789 726587 := bstep (se 1 (by rfl) ⟨544940, by rfl⟩ : syracuseStep 726587 = 1089881) B1089881
theorem B2954819 : Blo 483789 2954819 := bstep (se 1 (by rfl) ⟨2216114, by rfl⟩ : syracuseStep 2954819 = 4432229) B4432229
theorem B726647 : Blo 483789 726647 := bstep (se 1 (by rfl) ⟨544985, by rfl⟩ : syracuseStep 726647 = 1089971) B1089971
theorem B726671 : Blo 483789 726671 := bstep (se 1 (by rfl) ⟨545003, by rfl⟩ : syracuseStep 726671 = 1090007) B1090007
theorem B726713 : Blo 483789 726713 := bstep (se 2 (by rfl) ⟨272517, by rfl⟩ : syracuseStep 726713 = 545035) B545035
theorem B1840877 : Blo 483789 1840877 := bstep (se 3 (by rfl) ⟨345164, by rfl⟩ : syracuseStep 1840877 = 690329) B690329
theorem B726791 : Blo 483789 726791 := bstep (se 1 (by rfl) ⟨545093, by rfl⟩ : syracuseStep 726791 = 1090187) B1090187
theorem B2070305 : Blo 483789 2070305 := bstep (se 2 (by rfl) ⟨776364, by rfl⟩ : syracuseStep 2070305 = 1552729) B1552729
theorem B726827 : Blo 483789 726827 := bstep (se 1 (by rfl) ⟨545120, by rfl⟩ : syracuseStep 726827 = 1090241) B1090241
theorem B11802419 : Blo 483789 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B726857 : Blo 483789 726857 := bstep (se 2 (by rfl) ⟨272571, by rfl⟩ : syracuseStep 726857 = 545143) B545143
theorem B2987929 : Blo 483789 2987929 := bstep (se 2 (by rfl) ⟨1120473, by rfl⟩ : syracuseStep 2987929 = 2240947) B2240947
theorem B726971 : Blo 483789 726971 := bstep (se 1 (by rfl) ⟨545228, by rfl⟩ : syracuseStep 726971 = 1090457) B1090457
theorem B10000331 : Blo 483789 10000331 := bstep (se 1 (by rfl) ⟨7500248, by rfl⟩ : syracuseStep 10000331 = 15000497) B15000497
theorem B727031 : Blo 483789 727031 := bstep (se 1 (by rfl) ⟨545273, by rfl⟩ : syracuseStep 727031 = 1090547) B1090547
theorem B727055 : Blo 483789 727055 := bstep (se 1 (by rfl) ⟨545291, by rfl⟩ : syracuseStep 727055 = 1090583) B1090583
theorem B1185835 : Blo 483789 1185835 := bstep (se 1 (by rfl) ⟨889376, by rfl⟩ : syracuseStep 1185835 = 1778753) B1778753
theorem B727097 : Blo 483789 727097 := bstep (se 2 (by rfl) ⟨272661, by rfl⟩ : syracuseStep 727097 = 545323) B545323
theorem B727175 : Blo 483789 727175 := bstep (se 1 (by rfl) ⟨545381, by rfl⟩ : syracuseStep 727175 = 1090763) B1090763
theorem B923795 : Blo 483789 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B727211 : Blo 483789 727211 := bstep (se 1 (by rfl) ⟨545408, by rfl⟩ : syracuseStep 727211 = 1090817) B1090817
theorem B727241 : Blo 483789 727241 := bstep (se 2 (by rfl) ⟨272715, by rfl⟩ : syracuseStep 727241 = 545431) B545431
theorem B727355 : Blo 483789 727355 := bstep (se 1 (by rfl) ⟨545516, by rfl⟩ : syracuseStep 727355 = 1091033) B1091033
theorem B727415 : Blo 483789 727415 := bstep (se 1 (by rfl) ⟨545561, by rfl⟩ : syracuseStep 727415 = 1091123) B1091123
theorem B924023 : Blo 483789 924023 := bstep (se 1 (by rfl) ⟨693017, by rfl⟩ : syracuseStep 924023 = 1386035) B1386035
theorem B727439 : Blo 483789 727439 := bstep (se 1 (by rfl) ⟨545579, by rfl⟩ : syracuseStep 727439 = 1091159) B1091159
theorem B1644947 : Blo 483789 1644947 := bstep (se 1 (by rfl) ⟨1233710, by rfl⟩ : syracuseStep 1644947 = 2467421) B2467421
theorem B1841561 : Blo 483789 1841561 := bstep (se 2 (by rfl) ⟨690585, by rfl⟩ : syracuseStep 1841561 = 1381171) B1381171
theorem B727481 : Blo 483789 727481 := bstep (se 2 (by rfl) ⟨272805, by rfl⟩ : syracuseStep 727481 = 545611) B545611
theorem B727559 : Blo 483789 727559 := bstep (se 1 (by rfl) ⟨545669, by rfl⟩ : syracuseStep 727559 = 1091339) B1091339
theorem B727595 : Blo 483789 727595 := bstep (se 1 (by rfl) ⟨545696, by rfl⟩ : syracuseStep 727595 = 1091393) B1091393
theorem B2333245 : Blo 483789 2333245 := bstep (se 3 (by rfl) ⟨437483, by rfl⟩ : syracuseStep 2333245 = 874967) B874967
theorem B727625 : Blo 483789 727625 := bstep (se 2 (by rfl) ⟨272859, by rfl⟩ : syracuseStep 727625 = 545719) B545719
theorem B2464343 : Blo 483789 2464343 := bstep (se 1 (by rfl) ⟨1848257, by rfl⟩ : syracuseStep 2464343 = 3696515) B3696515
theorem B727739 : Blo 483789 727739 := bstep (se 1 (by rfl) ⟨545804, by rfl⟩ : syracuseStep 727739 = 1091609) B1091609
theorem B727799 : Blo 483789 727799 := bstep (se 1 (by rfl) ⟨545849, by rfl⟩ : syracuseStep 727799 = 1091699) B1091699
theorem B727823 : Blo 483789 727823 := bstep (se 1 (by rfl) ⟨545867, by rfl⟩ : syracuseStep 727823 = 1091735) B1091735
theorem B727865 : Blo 483789 727865 := bstep (se 2 (by rfl) ⟨272949, by rfl⟩ : syracuseStep 727865 = 545899) B545899
theorem B727943 : Blo 483789 727943 := bstep (se 1 (by rfl) ⟨545957, by rfl⟩ : syracuseStep 727943 = 1091915) B1091915
theorem B727979 : Blo 483789 727979 := bstep (se 1 (by rfl) ⟨545984, by rfl⟩ : syracuseStep 727979 = 1091969) B1091969
theorem B728009 : Blo 483789 728009 := bstep (se 2 (by rfl) ⟨273003, by rfl⟩ : syracuseStep 728009 = 546007) B546007
theorem B8297477 : Blo 483789 8297477 := bstep (se 4 (by rfl) ⟨777888, by rfl⟩ : syracuseStep 8297477 = 1555777) B1555777
theorem B728123 : Blo 483789 728123 := bstep (se 1 (by rfl) ⟨546092, by rfl⟩ : syracuseStep 728123 = 1092185) B1092185
theorem B2464829 : Blo 483789 2464829 := bstep (se 3 (by rfl) ⟨462155, by rfl⟩ : syracuseStep 2464829 = 924311) B924311
theorem B728183 : Blo 483789 728183 := bstep (se 1 (by rfl) ⟨546137, by rfl⟩ : syracuseStep 728183 = 1092275) B1092275
theorem B728207 : Blo 483789 728207 := bstep (se 1 (by rfl) ⟨546155, by rfl⟩ : syracuseStep 728207 = 1092311) B1092311
theorem B1186963 : Blo 483789 1186963 := bstep (se 1 (by rfl) ⟨890222, by rfl⟩ : syracuseStep 1186963 = 1780445) B1780445
theorem B728249 : Blo 483789 728249 := bstep (se 2 (by rfl) ⟨273093, by rfl⟩ : syracuseStep 728249 = 546187) B546187
theorem B2956517 : Blo 483789 2956517 := bstep (se 4 (by rfl) ⟨277173, by rfl⟩ : syracuseStep 2956517 = 554347) B554347
theorem B728327 : Blo 483789 728327 := bstep (se 1 (by rfl) ⟨546245, by rfl⟩ : syracuseStep 728327 = 1092491) B1092491
theorem B1088783 : Blo 483789 1088783 := bstep (se 1 (by rfl) ⟨816587, by rfl⟩ : syracuseStep 1088783 = 1633175) B1633175
theorem B1088801 : Blo 483789 1088801 := bstep (se 2 (by rfl) ⟨408300, by rfl⟩ : syracuseStep 1088801 = 816601) B816601
theorem B728363 : Blo 483789 728363 := bstep (se 1 (by rfl) ⟨546272, by rfl⟩ : syracuseStep 728363 = 1092545) B1092545
theorem B728393 : Blo 483789 728393 := bstep (se 2 (by rfl) ⟨273147, by rfl⟩ : syracuseStep 728393 = 546295) B546295
theorem B1842547 : Blo 483789 1842547 := bstep (se 1 (by rfl) ⟨1381910, by rfl⟩ : syracuseStep 1842547 = 2763821) B2763821
theorem B728507 : Blo 483789 728507 := bstep (se 1 (by rfl) ⟨546380, by rfl⟩ : syracuseStep 728507 = 1092761) B1092761
theorem B728567 : Blo 483789 728567 := bstep (se 1 (by rfl) ⟨546425, by rfl⟩ : syracuseStep 728567 = 1092851) B1092851
theorem B728591 : Blo 483789 728591 := bstep (se 1 (by rfl) ⟨546443, by rfl⟩ : syracuseStep 728591 = 1092887) B1092887
theorem B728633 : Blo 483789 728633 := bstep (se 2 (by rfl) ⟨273237, by rfl⟩ : syracuseStep 728633 = 546475) B546475
theorem B2629181 : Blo 483789 2629181 := bstep (se 3 (by rfl) ⟨492971, by rfl⟩ : syracuseStep 2629181 = 985943) B985943
theorem B2530883 : Blo 483789 2530883 := bstep (se 1 (by rfl) ⟨1898162, by rfl⟩ : syracuseStep 2530883 = 3796325) B3796325
theorem B1089143 : Blo 483789 1089143 := bstep (se 1 (by rfl) ⟨816857, by rfl⟩ : syracuseStep 1089143 = 1633715) B1633715
theorem B728711 : Blo 483789 728711 := bstep (se 1 (by rfl) ⟨546533, by rfl⟩ : syracuseStep 728711 = 1093067) B1093067
theorem B728747 : Blo 483789 728747 := bstep (se 1 (by rfl) ⟨546560, by rfl⟩ : syracuseStep 728747 = 1093121) B1093121
theorem B1384121 : Blo 483789 1384121 := bstep (se 2 (by rfl) ⟨519045, by rfl⟩ : syracuseStep 1384121 = 1038091) B1038091
theorem B728777 : Blo 483789 728777 := bstep (se 2 (by rfl) ⟨273291, by rfl⟩ : syracuseStep 728777 = 546583) B546583
theorem B2793217 : Blo 483789 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B1089323 : Blo 483789 1089323 := bstep (se 1 (by rfl) ⟨816992, by rfl⟩ : syracuseStep 1089323 = 1633985) B1633985
theorem B1384235 : Blo 483789 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B728891 : Blo 483789 728891 := bstep (se 1 (by rfl) ⟨546668, by rfl⟩ : syracuseStep 728891 = 1093337) B1093337
theorem B728951 : Blo 483789 728951 := bstep (se 1 (by rfl) ⟨546713, by rfl⟩ : syracuseStep 728951 = 1093427) B1093427
theorem B728975 : Blo 483789 728975 := bstep (se 1 (by rfl) ⟨546731, by rfl⟩ : syracuseStep 728975 = 1093463) B1093463
theorem B729017 : Blo 483789 729017 := bstep (se 2 (by rfl) ⟨273381, by rfl⟩ : syracuseStep 729017 = 546763) B546763
theorem B729095 : Blo 483789 729095 := bstep (se 1 (by rfl) ⟨546821, by rfl⟩ : syracuseStep 729095 = 1093643) B1093643
theorem B729131 : Blo 483789 729131 := bstep (se 1 (by rfl) ⟨546848, by rfl⟩ : syracuseStep 729131 = 1093697) B1093697
theorem B925739 : Blo 483789 925739 := bstep (se 1 (by rfl) ⟨694304, by rfl⟩ : syracuseStep 925739 = 1388609) B1388609
theorem B729161 : Blo 483789 729161 := bstep (se 2 (by rfl) ⟨273435, by rfl⟩ : syracuseStep 729161 = 546871) B546871
theorem B5906519 : Blo 483789 5906519 := bstep (se 1 (by rfl) ⟨4429889, by rfl⟩ : syracuseStep 5906519 = 8859779) B8859779
theorem B1089683 : Blo 483789 1089683 := bstep (se 1 (by rfl) ⟨817262, by rfl⟩ : syracuseStep 1089683 = 1634525) B1634525
theorem B729275 : Blo 483789 729275 := bstep (se 1 (by rfl) ⟨546956, by rfl⟩ : syracuseStep 729275 = 1093913) B1093913
theorem B1089737 : Blo 483789 1089737 := bstep (se 2 (by rfl) ⟨408651, by rfl⟩ : syracuseStep 1089737 = 817303) B817303
theorem B2760905 : Blo 483789 2760905 := bstep (se 2 (by rfl) ⟨1035339, by rfl⟩ : syracuseStep 2760905 = 2070679) B2070679
theorem B1482953 : Blo 483789 1482953 := bstep (se 2 (by rfl) ⟨556107, by rfl⟩ : syracuseStep 1482953 = 1112215) B1112215
theorem B729335 : Blo 483789 729335 := bstep (se 1 (by rfl) ⟨547001, by rfl⟩ : syracuseStep 729335 = 1094003) B1094003
theorem B729359 : Blo 483789 729359 := bstep (se 1 (by rfl) ⟨547019, by rfl⟩ : syracuseStep 729359 = 1094039) B1094039
theorem B925967 : Blo 483789 925967 := bstep (se 1 (by rfl) ⟨694475, by rfl⟩ : syracuseStep 925967 = 1388951) B1388951
theorem B729401 : Blo 483789 729401 := bstep (se 2 (by rfl) ⟨273525, by rfl⟩ : syracuseStep 729401 = 547051) B547051
theorem B729479 : Blo 483789 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B729515 : Blo 483789 729515 := bstep (se 1 (by rfl) ⟨547136, by rfl⟩ : syracuseStep 729515 = 1094273) B1094273
theorem B729545 : Blo 483789 729545 := bstep (se 2 (by rfl) ⟨273579, by rfl⟩ : syracuseStep 729545 = 547159) B547159
theorem B11969059 : Blo 483789 11969059 := bstep (se 1 (by rfl) ⟨8976794, by rfl⟩ : syracuseStep 11969059 = 17953589) B17953589
theorem B729659 : Blo 483789 729659 := bstep (se 1 (by rfl) ⟨547244, by rfl⟩ : syracuseStep 729659 = 1094489) B1094489
theorem B729719 : Blo 483789 729719 := bstep (se 1 (by rfl) ⟨547289, by rfl⟩ : syracuseStep 729719 = 1094579) B1094579
theorem B729743 : Blo 483789 729743 := bstep (se 1 (by rfl) ⟨547307, by rfl⟩ : syracuseStep 729743 = 1094615) B1094615
theorem B729785 : Blo 483789 729785 := bstep (se 2 (by rfl) ⟨273669, by rfl⟩ : syracuseStep 729785 = 547339) B547339
theorem B729863 : Blo 483789 729863 := bstep (se 1 (by rfl) ⟨547397, by rfl⟩ : syracuseStep 729863 = 1094795) B1094795
theorem B5251877 : Blo 483789 5251877 := bstep (se 4 (by rfl) ⟨492363, by rfl⟩ : syracuseStep 5251877 = 984727) B984727
theorem B729899 : Blo 483789 729899 := bstep (se 1 (by rfl) ⟨547424, by rfl⟩ : syracuseStep 729899 = 1094849) B1094849
theorem B2466611 : Blo 483789 2466611 := bstep (se 1 (by rfl) ⟨1849958, by rfl⟩ : syracuseStep 2466611 = 3699917) B3699917
theorem B729929 : Blo 483789 729929 := bstep (se 2 (by rfl) ⟨273723, by rfl⟩ : syracuseStep 729929 = 547447) B547447
theorem B1090439 : Blo 483789 1090439 := bstep (se 1 (by rfl) ⟨817829, by rfl⟩ : syracuseStep 1090439 = 1635659) B1635659
theorem B1385363 : Blo 483789 1385363 := bstep (se 1 (by rfl) ⟨1039022, by rfl⟩ : syracuseStep 1385363 = 2078045) B2078045
theorem B730043 : Blo 483789 730043 := bstep (se 1 (by rfl) ⟨547532, by rfl⟩ : syracuseStep 730043 = 1095065) B1095065
theorem B730103 : Blo 483789 730103 := bstep (se 1 (by rfl) ⟨547577, by rfl⟩ : syracuseStep 730103 = 1095155) B1095155
theorem B730127 : Blo 483789 730127 := bstep (se 1 (by rfl) ⟨547595, by rfl⟩ : syracuseStep 730127 = 1095191) B1095191
theorem B730169 : Blo 483789 730169 := bstep (se 2 (by rfl) ⟨273813, by rfl⟩ : syracuseStep 730169 = 547627) B547627
theorem B1090619 : Blo 483789 1090619 := bstep (se 1 (by rfl) ⟨817964, by rfl⟩ : syracuseStep 1090619 = 1635929) B1635929
theorem B2466935 : Blo 483789 2466935 := bstep (se 1 (by rfl) ⟨1850201, by rfl⟩ : syracuseStep 2466935 = 3700403) B3700403
theorem B730247 : Blo 483789 730247 := bstep (se 1 (by rfl) ⟨547685, by rfl⟩ : syracuseStep 730247 = 1095371) B1095371
theorem B730283 : Blo 483789 730283 := bstep (se 1 (by rfl) ⟨547712, by rfl⟩ : syracuseStep 730283 = 1095425) B1095425
theorem B1090745 : Blo 483789 1090745 := bstep (se 2 (by rfl) ⟨409029, by rfl⟩ : syracuseStep 1090745 = 818059) B818059
theorem B730313 : Blo 483789 730313 := bstep (se 2 (by rfl) ⟨273867, by rfl⟩ : syracuseStep 730313 = 547735) B547735
theorem B2630893 : Blo 483789 2630893 := bstep (se 3 (by rfl) ⟨493292, by rfl⟩ : syracuseStep 2630893 = 986585) B986585
theorem B1385761 : Blo 483789 1385761 := bstep (se 2 (by rfl) ⟨519660, by rfl⟩ : syracuseStep 1385761 = 1039321) B1039321
theorem B730427 : Blo 483789 730427 := bstep (se 1 (by rfl) ⟨547820, by rfl⟩ : syracuseStep 730427 = 1095641) B1095641
theorem B11937125 : Blo 483789 11937125 := bstep (se 4 (by rfl) ⟨1119105, by rfl⟩ : syracuseStep 11937125 = 2238211) B2238211
theorem B730487 : Blo 483789 730487 := bstep (se 1 (by rfl) ⟨547865, by rfl⟩ : syracuseStep 730487 = 1095731) B1095731
theorem B730511 : Blo 483789 730511 := bstep (se 1 (by rfl) ⟨547883, by rfl⟩ : syracuseStep 730511 = 1095767) B1095767
theorem B730553 : Blo 483789 730553 := bstep (se 2 (by rfl) ⟨273957, by rfl⟩ : syracuseStep 730553 = 547915) B547915
theorem B730631 : Blo 483789 730631 := bstep (se 1 (by rfl) ⟨547973, by rfl⟩ : syracuseStep 730631 = 1095947) B1095947
theorem B1091087 : Blo 483789 1091087 := bstep (se 1 (by rfl) ⟨818315, by rfl⟩ : syracuseStep 1091087 = 1636631) B1636631
theorem B1844765 : Blo 483789 1844765 := bstep (se 3 (by rfl) ⟨345893, by rfl⟩ : syracuseStep 1844765 = 691787) B691787
theorem B1091105 : Blo 483789 1091105 := bstep (se 2 (by rfl) ⟨409164, by rfl⟩ : syracuseStep 1091105 = 818329) B818329
theorem B730667 : Blo 483789 730667 := bstep (se 1 (by rfl) ⟨548000, by rfl⟩ : syracuseStep 730667 = 1096001) B1096001
theorem B730697 : Blo 483789 730697 := bstep (se 2 (by rfl) ⟨274011, by rfl⟩ : syracuseStep 730697 = 548023) B548023
theorem B730811 : Blo 483789 730811 := bstep (se 1 (by rfl) ⟨548108, by rfl⟩ : syracuseStep 730811 = 1096217) B1096217
theorem B5252825 : Blo 483789 5252825 := bstep (se 2 (by rfl) ⟨1969809, by rfl⟩ : syracuseStep 5252825 = 3939619) B3939619
theorem B730871 : Blo 483789 730871 := bstep (se 1 (by rfl) ⟨548153, by rfl⟩ : syracuseStep 730871 = 1096307) B1096307
theorem B730895 : Blo 483789 730895 := bstep (se 1 (by rfl) ⟨548171, by rfl⟩ : syracuseStep 730895 = 1096343) B1096343
theorem B730937 : Blo 483789 730937 := bstep (se 2 (by rfl) ⟨274101, by rfl⟩ : syracuseStep 730937 = 548203) B548203
theorem B2336627 : Blo 483789 2336627 := bstep (se 1 (by rfl) ⟨1752470, by rfl⟩ : syracuseStep 2336627 = 3504941) B3504941
theorem B1091447 : Blo 483789 1091447 := bstep (se 1 (by rfl) ⟨818585, by rfl⟩ : syracuseStep 1091447 = 1637171) B1637171
theorem B731015 : Blo 483789 731015 := bstep (se 1 (by rfl) ⟨548261, by rfl⟩ : syracuseStep 731015 = 1096523) B1096523
theorem B731051 : Blo 483789 731051 := bstep (se 1 (by rfl) ⟨548288, by rfl⟩ : syracuseStep 731051 = 1096577) B1096577
theorem B731081 : Blo 483789 731081 := bstep (se 2 (by rfl) ⟨274155, by rfl⟩ : syracuseStep 731081 = 548311) B548311
theorem B1091627 : Blo 483789 1091627 := bstep (se 1 (by rfl) ⟨818720, by rfl⟩ : syracuseStep 1091627 = 1637441) B1637441
theorem B731195 : Blo 483789 731195 := bstep (se 1 (by rfl) ⟨548396, by rfl⟩ : syracuseStep 731195 = 1096793) B1096793
theorem B2762819 : Blo 483789 2762819 := bstep (se 1 (by rfl) ⟨2072114, by rfl⟩ : syracuseStep 2762819 = 4144229) B4144229
theorem B2467907 : Blo 483789 2467907 := bstep (se 1 (by rfl) ⟨1850930, by rfl⟩ : syracuseStep 2467907 = 3701861) B3701861
theorem B731255 : Blo 483789 731255 := bstep (se 1 (by rfl) ⟨548441, by rfl⟩ : syracuseStep 731255 = 1096883) B1096883
theorem B731279 : Blo 483789 731279 := bstep (se 1 (by rfl) ⟨548459, by rfl⟩ : syracuseStep 731279 = 1096919) B1096919
theorem B1386649 : Blo 483789 1386649 := bstep (se 2 (by rfl) ⟨519993, by rfl⟩ : syracuseStep 1386649 = 1039987) B1039987
theorem B731321 : Blo 483789 731321 := bstep (se 2 (by rfl) ⟨274245, by rfl⟩ : syracuseStep 731321 = 548491) B548491
theorem B1845449 : Blo 483789 1845449 := bstep (se 2 (by rfl) ⟨692043, by rfl⟩ : syracuseStep 1845449 = 1384087) B1384087
theorem B731399 : Blo 483789 731399 := bstep (se 1 (by rfl) ⟨548549, by rfl⟩ : syracuseStep 731399 = 1097099) B1097099
theorem B731435 : Blo 483789 731435 := bstep (se 1 (by rfl) ⟨548576, by rfl⟩ : syracuseStep 731435 = 1097153) B1097153
theorem B731465 : Blo 483789 731465 := bstep (se 2 (by rfl) ⟨274299, by rfl⟩ : syracuseStep 731465 = 548599) B548599
theorem B5515613 : Blo 483789 5515613 := bstep (se 3 (by rfl) ⟨1034177, by rfl⟩ : syracuseStep 5515613 = 2068355) B2068355
theorem B2468231 : Blo 483789 2468231 := bstep (se 1 (by rfl) ⟨1851173, by rfl⟩ : syracuseStep 2468231 = 3702347) B3702347
theorem B1091987 : Blo 483789 1091987 := bstep (se 1 (by rfl) ⟨818990, by rfl⟩ : syracuseStep 1091987 = 1637981) B1637981
theorem B731579 : Blo 483789 731579 := bstep (se 1 (by rfl) ⟨548684, by rfl⟩ : syracuseStep 731579 = 1097369) B1097369
theorem B1092041 : Blo 483789 1092041 := bstep (se 2 (by rfl) ⟨409515, by rfl⟩ : syracuseStep 1092041 = 819031) B819031
theorem B731639 : Blo 483789 731639 := bstep (se 1 (by rfl) ⟨548729, by rfl⟩ : syracuseStep 731639 = 1097459) B1097459
theorem B731663 : Blo 483789 731663 := bstep (se 1 (by rfl) ⟨548747, by rfl⟩ : syracuseStep 731663 = 1097495) B1097495
theorem B3156509 : Blo 483789 3156509 := bstep (se 3 (by rfl) ⟨591845, by rfl⟩ : syracuseStep 3156509 = 1183691) B1183691
theorem B1387037 : Blo 483789 1387037 := bstep (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) B520139
theorem B3123755 : Blo 483789 3123755 := bstep (se 1 (by rfl) ⟨2342816, by rfl⟩ : syracuseStep 3123755 = 4685633) B4685633
theorem B19999493 : Blo 483789 19999493 := bstep (se 4 (by rfl) ⟨1874952, by rfl⟩ : syracuseStep 19999493 = 3749905) B3749905
theorem B2960165 : Blo 483789 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B9972823 : Blo 483789 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B1092743 : Blo 483789 1092743 := bstep (se 1 (by rfl) ⟨819557, by rfl⟩ : syracuseStep 1092743 = 1639115) B1639115
theorem B4140233 : Blo 483789 4140233 := bstep (se 2 (by rfl) ⟨1552587, by rfl⟩ : syracuseStep 4140233 = 3105175) B3105175
theorem B1092923 : Blo 483789 1092923 := bstep (se 1 (by rfl) ⟨819692, by rfl⟩ : syracuseStep 1092923 = 1639385) B1639385
theorem B248491405 : Blo 483789 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B1093049 : Blo 483789 1093049 := bstep (se 2 (by rfl) ⟨409893, by rfl⟩ : syracuseStep 1093049 = 819787) B819787
theorem B5517071 : Blo 483789 5517071 := bstep (se 1 (by rfl) ⟨4137803, by rfl⟩ : syracuseStep 5517071 = 8275607) B8275607
theorem B1093391 : Blo 483789 1093391 := bstep (se 1 (by rfl) ⟨820043, by rfl⟩ : syracuseStep 1093391 = 1640087) B1640087
theorem B1093409 : Blo 483789 1093409 := bstep (se 2 (by rfl) ⟨410028, by rfl⟩ : syracuseStep 1093409 = 820057) B820057
theorem B1847225 : Blo 483789 1847225 := bstep (se 2 (by rfl) ⟨692709, by rfl⟩ : syracuseStep 1847225 = 1385419) B1385419
theorem B1224791 : Blo 483789 1224791 := bstep (se 1 (by rfl) ⟨918593, by rfl⟩ : syracuseStep 1224791 = 1837187) B1837187
theorem B1093751 : Blo 483789 1093751 := bstep (se 1 (by rfl) ⟨820313, by rfl⟩ : syracuseStep 1093751 = 1640627) B1640627
theorem B1225003 : Blo 483789 1225003 := bstep (se 1 (by rfl) ⟨918752, by rfl⟩ : syracuseStep 1225003 = 1837505) B1837505
theorem B1093931 : Blo 483789 1093931 := bstep (se 1 (by rfl) ⟨820448, by rfl⟩ : syracuseStep 1093931 = 1640897) B1640897
theorem B1225145 : Blo 483789 1225145 := bstep (se 2 (by rfl) ⟨459429, by rfl⟩ : syracuseStep 1225145 = 918859) B918859
theorem B1552907 : Blo 483789 1552907 := bstep (se 1 (by rfl) ⟨1164680, by rfl⟩ : syracuseStep 1552907 = 2329361) B2329361
theorem B1094291 : Blo 483789 1094291 := bstep (se 1 (by rfl) ⟨820718, by rfl⟩ : syracuseStep 1094291 = 1641437) B1641437
theorem B1094345 : Blo 483789 1094345 := bstep (se 2 (by rfl) ⟨410379, by rfl⟩ : syracuseStep 1094345 = 820759) B820759
theorem B1095047 : Blo 483789 1095047 := bstep (se 1 (by rfl) ⟨821285, by rfl⟩ : syracuseStep 1095047 = 1642571) B1642571
theorem B1226137 : Blo 483789 1226137 := bstep (se 2 (by rfl) ⟨459801, by rfl⟩ : syracuseStep 1226137 = 919603) B919603
theorem B1750481 : Blo 483789 1750481 := bstep (se 2 (by rfl) ⟨656430, by rfl⟩ : syracuseStep 1750481 = 1312861) B1312861
theorem B2635217 : Blo 483789 2635217 := bstep (se 2 (by rfl) ⟨988206, by rfl⟩ : syracuseStep 2635217 = 1976413) B1976413
theorem B1226299 : Blo 483789 1226299 := bstep (se 1 (by rfl) ⟨919724, by rfl⟩ : syracuseStep 1226299 = 1839449) B1839449
theorem B1095227 : Blo 483789 1095227 := bstep (se 1 (by rfl) ⟨821420, by rfl⟩ : syracuseStep 1095227 = 1642841) B1642841
theorem B2635325 : Blo 483789 2635325 := bstep (se 3 (by rfl) ⟨494123, by rfl⟩ : syracuseStep 2635325 = 988247) B988247
theorem B1095353 : Blo 483789 1095353 := bstep (se 2 (by rfl) ⟨410757, by rfl⟩ : syracuseStep 1095353 = 821515) B821515
theorem B3847873 : Blo 483789 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B1226441 : Blo 483789 1226441 := bstep (se 2 (by rfl) ⟨459915, by rfl⟩ : syracuseStep 1226441 = 919831) B919831
theorem B2766737 : Blo 483789 2766737 := bstep (se 2 (by rfl) ⟨1037526, by rfl⟩ : syracuseStep 2766737 = 2075053) B2075053
theorem B1095695 : Blo 483789 1095695 := bstep (se 1 (by rfl) ⟨821771, by rfl⟩ : syracuseStep 1095695 = 1643543) B1643543
theorem B86751245 : Blo 483789 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B1226785 : Blo 483789 1226785 := bstep (se 2 (by rfl) ⟨460044, by rfl⟩ : syracuseStep 1226785 = 920089) B920089
theorem B1095713 : Blo 483789 1095713 := bstep (se 2 (by rfl) ⟨410892, by rfl⟩ : syracuseStep 1095713 = 821785) B821785
theorem B2767193 : Blo 483789 2767193 := bstep (se 2 (by rfl) ⟨1037697, by rfl⟩ : syracuseStep 2767193 = 2075395) B2075395
theorem B1096055 : Blo 483789 1096055 := bstep (se 1 (by rfl) ⟨822041, by rfl⟩ : syracuseStep 1096055 = 1644083) B1644083
theorem B4143545 : Blo 483789 4143545 := bstep (se 2 (by rfl) ⟨1553829, by rfl⟩ : syracuseStep 4143545 = 3107659) B3107659
theorem B1096235 : Blo 483789 1096235 := bstep (se 1 (by rfl) ⟨822176, by rfl⟩ : syracuseStep 1096235 = 1644353) B1644353
theorem B1227383 : Blo 483789 1227383 := bstep (se 1 (by rfl) ⟨920537, by rfl⟩ : syracuseStep 1227383 = 1841075) B1841075
theorem B1096595 : Blo 483789 1096595 := bstep (se 1 (by rfl) ⟨822446, by rfl⟩ : syracuseStep 1096595 = 1644893) B1644893
theorem B2341817 : Blo 483789 2341817 := bstep (se 2 (by rfl) ⟨878181, by rfl⟩ : syracuseStep 2341817 = 1756363) B1756363
theorem B1096649 : Blo 483789 1096649 := bstep (se 2 (by rfl) ⟨411243, by rfl⟩ : syracuseStep 1096649 = 822487) B822487
theorem B11811851 : Blo 483789 11811851 := bstep (se 1 (by rfl) ⟨8858888, by rfl⟩ : syracuseStep 11811851 = 17717777) B17717777
theorem B1850809 : Blo 483789 1850809 := bstep (se 2 (by rfl) ⟨694053, by rfl⟩ : syracuseStep 1850809 = 1388107) B1388107
theorem B1097351 : Blo 483789 1097351 := bstep (se 1 (by rfl) ⟨823013, by rfl⟩ : syracuseStep 1097351 = 1646027) B1646027
theorem B1228679 : Blo 483789 1228679 := bstep (se 1 (by rfl) ⟨921509, by rfl⟩ : syracuseStep 1228679 = 1843019) B1843019
theorem B1228729 : Blo 483789 1228729 := bstep (se 2 (by rfl) ⟨460773, by rfl⟩ : syracuseStep 1228729 = 921547) B921547
theorem B1163297 : Blo 483789 1163297 := bstep (se 2 (by rfl) ⟨436236, by rfl⟩ : syracuseStep 1163297 = 872473) B872473
theorem B2080829 : Blo 483789 2080829 := bstep (se 3 (by rfl) ⟨390155, by rfl⟩ : syracuseStep 2080829 = 780311) B780311
theorem B7029139 : Blo 483789 7029139 := bstep (se 1 (by rfl) ⟨5271854, by rfl⟩ : syracuseStep 7029139 = 10543709) B10543709
theorem B1229327 : Blo 483789 1229327 := bstep (se 1 (by rfl) ⟨921995, by rfl⟩ : syracuseStep 1229327 = 1843991) B1843991
theorem B2212609 : Blo 483789 2212609 := bstep (se 2 (by rfl) ⟨829728, by rfl⟩ : syracuseStep 2212609 = 1659457) B1659457
theorem B1164065 : Blo 483789 1164065 := bstep (se 2 (by rfl) ⟨436524, by rfl⟩ : syracuseStep 1164065 = 873049) B873049
theorem B5554979 : Blo 483789 5554979 := bstep (se 1 (by rfl) ⟨4166234, by rfl⟩ : syracuseStep 5554979 = 8332469) B8332469
theorem B1557623 : Blo 483789 1557623 := bstep (se 1 (by rfl) ⟨1168217, by rfl⟩ : syracuseStep 1557623 = 2336435) B2336435
theorem B1492115 : Blo 483789 1492115 := bstep (se 1 (by rfl) ⟨1119086, by rfl⟩ : syracuseStep 1492115 = 2238173) B2238173
theorem B1230025 : Blo 483789 1230025 := bstep (se 2 (by rfl) ⟨461259, by rfl⟩ : syracuseStep 1230025 = 922519) B922519
theorem B1230167 : Blo 483789 1230167 := bstep (se 1 (by rfl) ⟨922625, by rfl⟩ : syracuseStep 1230167 = 1845251) B1845251
theorem B2770361 : Blo 483789 2770361 := bstep (se 2 (by rfl) ⟨1038885, by rfl⟩ : syracuseStep 2770361 = 2077771) B2077771
theorem B1034785 : Blo 483789 1034785 := bstep (se 2 (by rfl) ⟨388044, by rfl⟩ : syracuseStep 1034785 = 776089) B776089
theorem B937079 : Blo 483789 937079 := bstep (se 1 (by rfl) ⟨702809, by rfl⟩ : syracuseStep 937079 = 1405619) B1405619
theorem B1232243 : Blo 483789 1232243 := bstep (se 1 (by rfl) ⟨924182, by rfl⟩ : syracuseStep 1232243 = 1848365) B1848365
theorem B1166777 : Blo 483789 1166777 := bstep (se 2 (by rfl) ⟨437541, by rfl⟩ : syracuseStep 1166777 = 875083) B875083
theorem B544315 : Blo 483789 544315 := bstep (se 1 (by rfl) ⟨408236, by rfl⟩ : syracuseStep 544315 = 816473) B816473
theorem B2772751 : Blo 483789 2772751 := bstep (se 1 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 2772751 = 4159127) B4159127
theorem B1560379 : Blo 483789 1560379 := bstep (se 1 (by rfl) ⟨1170284, by rfl⟩ : syracuseStep 1560379 = 2340569) B2340569
theorem B1232759 : Blo 483789 1232759 := bstep (se 1 (by rfl) ⟨924569, by rfl⟩ : syracuseStep 1232759 = 1849139) B1849139
theorem B4673483 : Blo 483789 4673483 := bstep (se 1 (by rfl) ⟨3505112, by rfl⟩ : syracuseStep 4673483 = 7010225) B7010225
theorem B544783 : Blo 483789 544783 := bstep (se 1 (by rfl) ⟨408587, by rfl⟩ : syracuseStep 544783 = 817175) B817175
theorem B1036331 : Blo 483789 1036331 := bstep (se 1 (by rfl) ⟨777248, by rfl⟩ : syracuseStep 1036331 = 1554497) B1554497
theorem B5525819 : Blo 483789 5525819 := bstep (se 1 (by rfl) ⟨4144364, by rfl⟩ : syracuseStep 5525819 = 8288729) B8288729
theorem B3101075 : Blo 483789 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B545287 : Blo 483789 545287 := bstep (se 1 (by rfl) ⟨408965, by rfl⟩ : syracuseStep 545287 = 817931) B817931
theorem B3101303 : Blo 483789 3101303 := bstep (se 1 (by rfl) ⟨2325977, by rfl⟩ : syracuseStep 3101303 = 4651955) B4651955
theorem B873107 : Blo 483789 873107 := bstep (se 1 (by rfl) ⟨654830, by rfl⟩ : syracuseStep 873107 = 1309661) B1309661
theorem B1168025 : Blo 483789 1168025 := bstep (se 2 (by rfl) ⟨438009, by rfl⟩ : syracuseStep 1168025 = 876019) B876019
theorem B545467 : Blo 483789 545467 := bstep (se 1 (by rfl) ⟨409100, by rfl⟩ : syracuseStep 545467 = 818201) B818201
theorem B7000769 : Blo 483789 7000769 := bstep (se 2 (by rfl) ⟨2625288, by rfl⟩ : syracuseStep 7000769 = 5250577) B5250577
theorem B2806501 : Blo 483789 2806501 := bstep (se 4 (by rfl) ⟨263109, by rfl⟩ : syracuseStep 2806501 = 526219) B526219
theorem B1332001 : Blo 483789 1332001 := bstep (se 2 (by rfl) ⟨499500, by rfl⟩ : syracuseStep 1332001 = 999001) B999001
theorem B1233751 : Blo 483789 1233751 := bstep (se 1 (by rfl) ⟨925313, by rfl⟩ : syracuseStep 1233751 = 1850627) B1850627
theorem B42160985 : Blo 483789 42160985 := bstep (se 2 (by rfl) ⟨15810369, by rfl⟩ : syracuseStep 42160985 = 31620739) B31620739
theorem B2774027 : Blo 483789 2774027 := bstep (se 1 (by rfl) ⟨2080520, by rfl⟩ : syracuseStep 2774027 = 4161041) B4161041
theorem B1234055 : Blo 483789 1234055 := bstep (se 1 (by rfl) ⟨925541, by rfl⟩ : syracuseStep 1234055 = 1851083) B1851083
theorem B545935 : Blo 483789 545935 := bstep (se 1 (by rfl) ⟨409451, by rfl⟩ : syracuseStep 545935 = 818903) B818903
theorem B2774209 : Blo 483789 2774209 := bstep (se 2 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 2774209 = 2080657) B2080657
theorem B1234187 : Blo 483789 1234187 := bstep (se 1 (by rfl) ⟨925640, by rfl⟩ : syracuseStep 1234187 = 1851281) B1851281
theorem B5985683 : Blo 483789 5985683 := bstep (se 1 (by rfl) ⟨4489262, by rfl⟩ : syracuseStep 5985683 = 8978525) B8978525
theorem B1398169 : Blo 483789 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B873929 : Blo 483789 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B546439 : Blo 483789 546439 := bstep (se 1 (by rfl) ⟨409829, by rfl⟩ : syracuseStep 546439 = 819659) B819659
theorem B1037971 : Blo 483789 1037971 := bstep (se 1 (by rfl) ⟨778478, by rfl⟩ : syracuseStep 1037971 = 1556957) B1556957
theorem B23025329 : Blo 483789 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B6674177 : Blo 483789 6674177 := bstep (se 2 (by rfl) ⟨2502816, by rfl⟩ : syracuseStep 6674177 = 5005633) B5005633
theorem B1234703 : Blo 483789 1234703 := bstep (se 1 (by rfl) ⟨926027, by rfl⟩ : syracuseStep 1234703 = 1852055) B1852055
theorem B546619 : Blo 483789 546619 := bstep (se 1 (by rfl) ⟨409964, by rfl⟩ : syracuseStep 546619 = 819929) B819929
theorem B31610897 : Blo 483789 31610897 := bstep (se 2 (by rfl) ⟨11854086, by rfl⟩ : syracuseStep 31610897 = 23708173) B23708173
theorem B2218013 : Blo 483789 2218013 := bstep (se 3 (by rfl) ⟨415877, by rfl⟩ : syracuseStep 2218013 = 831755) B831755
theorem B5232757 : Blo 483789 5232757 := bstep (se 5 (by rfl) ⟨245285, by rfl⟩ : syracuseStep 5232757 = 490571) B490571
theorem B612623 : Blo 483789 612623 := bstep (se 1 (by rfl) ⟨459467, by rfl⟩ : syracuseStep 612623 = 918935) B918935
theorem B547087 : Blo 483789 547087 := bstep (se 1 (by rfl) ⟨410315, by rfl⟩ : syracuseStep 547087 = 820631) B820631
theorem B874795 : Blo 483789 874795 := bstep (se 1 (by rfl) ⟨656096, by rfl⟩ : syracuseStep 874795 = 1312193) B1312193
theorem B776633 : Blo 483789 776633 := bstep (se 2 (by rfl) ⟨291237, by rfl⟩ : syracuseStep 776633 = 582475) B582475
theorem B547591 : Blo 483789 547591 := bstep (se 1 (by rfl) ⟨410693, by rfl⟩ : syracuseStep 547591 = 821387) B821387
theorem B4742003 : Blo 483789 4742003 := bstep (se 1 (by rfl) ⟨3556502, by rfl⟩ : syracuseStep 4742003 = 7113005) B7113005
theorem B547771 : Blo 483789 547771 := bstep (se 1 (by rfl) ⟨410828, by rfl⟩ : syracuseStep 547771 = 821657) B821657
theorem B3333143 : Blo 483789 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B47733941 : Blo 483789 47733941 := bstep (se 5 (by rfl) ⟨2237528, by rfl⟩ : syracuseStep 47733941 = 4475057) B4475057
theorem B548239 : Blo 483789 548239 := bstep (se 1 (by rfl) ⟨411179, by rfl⟩ : syracuseStep 548239 = 822359) B822359
theorem B1039817 : Blo 483789 1039817 := bstep (se 2 (by rfl) ⟨389931, by rfl⟩ : syracuseStep 1039817 = 779863) B779863
theorem B5234141 : Blo 483789 5234141 := bstep (se 3 (by rfl) ⟨981401, by rfl⟩ : syracuseStep 5234141 = 1962803) B1962803
theorem B876179 : Blo 483789 876179 := bstep (se 1 (by rfl) ⟨657134, by rfl⟩ : syracuseStep 876179 = 1314269) B1314269
theorem B548743 : Blo 483789 548743 := bstep (se 1 (by rfl) ⟨411557, by rfl⟩ : syracuseStep 548743 = 823115) B823115
theorem B4153355 : Blo 483789 4153355 := bstep (se 1 (by rfl) ⟨3115016, by rfl⟩ : syracuseStep 4153355 = 6230033) B6230033
theorem B2449601 : Blo 483789 2449601 := bstep (se 2 (by rfl) ⟨918600, by rfl⟩ : syracuseStep 2449601 = 1837201) B1837201
theorem B778555 : Blo 483789 778555 := bstep (se 1 (by rfl) ⟨583916, by rfl⟩ : syracuseStep 778555 = 1167833) B1167833
theorem B1040825 : Blo 483789 1040825 := bstep (se 2 (by rfl) ⟨390309, by rfl⟩ : syracuseStep 1040825 = 780619) B780619
theorem B3695057 : Blo 483789 3695057 := bstep (se 2 (by rfl) ⟨1385646, by rfl⟩ : syracuseStep 3695057 = 2771293) B2771293
theorem B483847 : Blo 483789 483847 := bstep (se 1 (by rfl) ⟨362885, by rfl⟩ : syracuseStep 483847 = 725771) B725771
theorem B483855 : Blo 483789 483855 := bstep (se 1 (by rfl) ⟨362891, by rfl⟩ : syracuseStep 483855 = 725783) B725783
theorem B483899 : Blo 483789 483899 := bstep (se 1 (by rfl) ⟨362924, by rfl⟩ : syracuseStep 483899 = 725849) B725849
theorem B483975 : Blo 483789 483975 := bstep (se 1 (by rfl) ⟨362981, by rfl⟩ : syracuseStep 483975 = 725963) B725963
theorem B483983 : Blo 483789 483983 := bstep (se 1 (by rfl) ⟨362987, by rfl⟩ : syracuseStep 483983 = 725975) B725975
theorem B484027 : Blo 483789 484027 := bstep (se 1 (by rfl) ⟨363020, by rfl⟩ : syracuseStep 484027 = 726041) B726041
theorem B484103 : Blo 483789 484103 := bstep (se 1 (by rfl) ⟨363077, by rfl⟩ : syracuseStep 484103 = 726155) B726155
theorem B484111 : Blo 483789 484111 := bstep (se 1 (by rfl) ⟨363083, by rfl⟩ : syracuseStep 484111 = 726167) B726167
theorem B1041167 : Blo 483789 1041167 := bstep (se 1 (by rfl) ⟨780875, by rfl⟩ : syracuseStep 1041167 = 1561751) B1561751
theorem B484155 : Blo 483789 484155 := bstep (se 1 (by rfl) ⟨363116, by rfl⟩ : syracuseStep 484155 = 726233) B726233
theorem B484231 : Blo 483789 484231 := bstep (se 1 (by rfl) ⟨363173, by rfl⟩ : syracuseStep 484231 = 726347) B726347
theorem B484239 : Blo 483789 484239 := bstep (se 1 (by rfl) ⟨363179, by rfl⟩ : syracuseStep 484239 = 726359) B726359
theorem B517051 : Blo 483789 517051 := bstep (se 1 (by rfl) ⟨387788, by rfl⟩ : syracuseStep 517051 = 775577) B775577
theorem B484283 : Blo 483789 484283 := bstep (se 1 (by rfl) ⟨363212, by rfl⟩ : syracuseStep 484283 = 726425) B726425
theorem B484359 : Blo 483789 484359 := bstep (se 1 (by rfl) ⟨363269, by rfl⟩ : syracuseStep 484359 = 726539) B726539
theorem B484367 : Blo 483789 484367 := bstep (se 1 (by rfl) ⟨363275, by rfl⟩ : syracuseStep 484367 = 726551) B726551
theorem B484411 : Blo 483789 484411 := bstep (se 1 (by rfl) ⟨363308, by rfl⟩ : syracuseStep 484411 = 726617) B726617
theorem B484487 : Blo 483789 484487 := bstep (se 1 (by rfl) ⟨363365, by rfl⟩ : syracuseStep 484487 = 726731) B726731
theorem B1401991 : Blo 483789 1401991 := bstep (se 1 (by rfl) ⟨1051493, by rfl⟩ : syracuseStep 1401991 = 2102987) B2102987
theorem B484495 : Blo 483789 484495 := bstep (se 1 (by rfl) ⟨363371, by rfl⟩ : syracuseStep 484495 = 726743) B726743
theorem B615595 : Blo 483789 615595 := bstep (se 1 (by rfl) ⟨461696, by rfl⟩ : syracuseStep 615595 = 923393) B923393
theorem B484539 : Blo 483789 484539 := bstep (se 1 (by rfl) ⟨363404, by rfl⟩ : syracuseStep 484539 = 726809) B726809
theorem B484615 : Blo 483789 484615 := bstep (se 1 (by rfl) ⟨363461, by rfl⟩ : syracuseStep 484615 = 726923) B726923
theorem B484623 : Blo 483789 484623 := bstep (se 1 (by rfl) ⟨363467, by rfl⟩ : syracuseStep 484623 = 726935) B726935
theorem B484667 : Blo 483789 484667 := bstep (se 1 (by rfl) ⟨363500, by rfl⟩ : syracuseStep 484667 = 727001) B727001
theorem B484743 : Blo 483789 484743 := bstep (se 1 (by rfl) ⟨363557, by rfl⟩ : syracuseStep 484743 = 727115) B727115
theorem B484751 : Blo 483789 484751 := bstep (se 1 (by rfl) ⟨363563, by rfl⟩ : syracuseStep 484751 = 727127) B727127
theorem B484795 : Blo 483789 484795 := bstep (se 1 (by rfl) ⟨363596, by rfl⟩ : syracuseStep 484795 = 727193) B727193
theorem B2450897 : Blo 483789 2450897 := bstep (se 2 (by rfl) ⟨919086, by rfl⟩ : syracuseStep 2450897 = 1838173) B1838173
theorem B484871 : Blo 483789 484871 := bstep (se 1 (by rfl) ⟨363653, by rfl⟩ : syracuseStep 484871 = 727307) B727307
theorem B484879 : Blo 483789 484879 := bstep (se 1 (by rfl) ⟨363659, by rfl⟩ : syracuseStep 484879 = 727319) B727319
theorem B2942507 : Blo 483789 2942507 := bstep (se 1 (by rfl) ⟨2206880, by rfl⟩ : syracuseStep 2942507 = 4413761) B4413761
theorem B484923 : Blo 483789 484923 := bstep (se 1 (by rfl) ⟨363692, by rfl⟩ : syracuseStep 484923 = 727385) B727385
theorem B484999 : Blo 483789 484999 := bstep (se 1 (by rfl) ⟨363749, by rfl⟩ : syracuseStep 484999 = 727499) B727499
theorem B485007 : Blo 483789 485007 := bstep (se 1 (by rfl) ⟨363755, by rfl⟩ : syracuseStep 485007 = 727511) B727511
theorem B485051 : Blo 483789 485051 := bstep (se 1 (by rfl) ⟨363788, by rfl⟩ : syracuseStep 485051 = 727577) B727577
theorem B1795841 : Blo 483789 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B485127 : Blo 483789 485127 := bstep (se 1 (by rfl) ⟨363845, by rfl⟩ : syracuseStep 485127 = 727691) B727691
theorem B485135 : Blo 483789 485135 := bstep (se 1 (by rfl) ⟨363851, by rfl⟩ : syracuseStep 485135 = 727703) B727703
theorem B485179 : Blo 483789 485179 := bstep (se 1 (by rfl) ⟨363884, by rfl⟩ : syracuseStep 485179 = 727769) B727769
theorem B5891915 : Blo 483789 5891915 := bstep (se 1 (by rfl) ⟨4418936, by rfl⟩ : syracuseStep 5891915 = 8837873) B8837873
theorem B485255 : Blo 483789 485255 := bstep (se 1 (by rfl) ⟨363941, by rfl⟩ : syracuseStep 485255 = 727883) B727883
theorem B485263 : Blo 483789 485263 := bstep (se 1 (by rfl) ⟨363947, by rfl⟩ : syracuseStep 485263 = 727895) B727895
theorem B878521 : Blo 483789 878521 := bstep (se 2 (by rfl) ⟨329445, by rfl⟩ : syracuseStep 878521 = 658891) B658891
theorem B485307 : Blo 483789 485307 := bstep (se 1 (by rfl) ⟨363980, by rfl⟩ : syracuseStep 485307 = 727961) B727961
theorem B485383 : Blo 483789 485383 := bstep (se 1 (by rfl) ⟨364037, by rfl⟩ : syracuseStep 485383 = 728075) B728075
theorem B485391 : Blo 483789 485391 := bstep (se 1 (by rfl) ⟨364043, by rfl⟩ : syracuseStep 485391 = 728087) B728087
theorem B485435 : Blo 483789 485435 := bstep (se 1 (by rfl) ⟨364076, by rfl⟩ : syracuseStep 485435 = 728153) B728153
theorem B616567 : Blo 483789 616567 := bstep (se 1 (by rfl) ⟨462425, by rfl⟩ : syracuseStep 616567 = 924851) B924851
theorem B485511 : Blo 483789 485511 := bstep (se 1 (by rfl) ⟨364133, by rfl⟩ : syracuseStep 485511 = 728267) B728267
theorem B485519 : Blo 483789 485519 := bstep (se 1 (by rfl) ⟨364139, by rfl⟩ : syracuseStep 485519 = 728279) B728279
theorem B485563 : Blo 483789 485563 := bstep (se 1 (by rfl) ⟨364172, by rfl⟩ : syracuseStep 485563 = 728345) B728345
theorem B485639 : Blo 483789 485639 := bstep (se 1 (by rfl) ⟨364229, by rfl⟩ : syracuseStep 485639 = 728459) B728459
theorem B485647 : Blo 483789 485647 := bstep (se 1 (by rfl) ⟨364235, by rfl⟩ : syracuseStep 485647 = 728471) B728471
theorem B485691 : Blo 483789 485691 := bstep (se 1 (by rfl) ⟨364268, by rfl⟩ : syracuseStep 485691 = 728537) B728537
theorem B485767 : Blo 483789 485767 := bstep (se 1 (by rfl) ⟨364325, by rfl⟩ : syracuseStep 485767 = 728651) B728651
theorem B3795335 : Blo 483789 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B485775 : Blo 483789 485775 := bstep (se 1 (by rfl) ⟨364331, by rfl⟩ : syracuseStep 485775 = 728663) B728663
theorem B485819 : Blo 483789 485819 := bstep (se 1 (by rfl) ⟨364364, by rfl⟩ : syracuseStep 485819 = 728729) B728729
theorem B616891 : Blo 483789 616891 := bstep (se 1 (by rfl) ⟨462668, by rfl⟩ : syracuseStep 616891 = 925337) B925337
theorem B5630417 : Blo 483789 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B485895 : Blo 483789 485895 := bstep (se 1 (by rfl) ⟨364421, by rfl⟩ : syracuseStep 485895 = 728843) B728843
theorem B485903 : Blo 483789 485903 := bstep (se 1 (by rfl) ⟨364427, by rfl⟩ : syracuseStep 485903 = 728855) B728855
theorem B1632797 : Blo 483789 1632797 := bstep (se 3 (by rfl) ⟨306149, by rfl⟩ : syracuseStep 1632797 = 612299) B612299
theorem B485947 : Blo 483789 485947 := bstep (se 1 (by rfl) ⟨364460, by rfl⟩ : syracuseStep 485947 = 728921) B728921
theorem B486023 : Blo 483789 486023 := bstep (se 1 (by rfl) ⟨364517, by rfl⟩ : syracuseStep 486023 = 729035) B729035
theorem B486031 : Blo 483789 486031 := bstep (se 1 (by rfl) ⟨364523, by rfl⟩ : syracuseStep 486031 = 729047) B729047
theorem B486075 : Blo 483789 486075 := bstep (se 1 (by rfl) ⟨364556, by rfl⟩ : syracuseStep 486075 = 729113) B729113
theorem B486151 : Blo 483789 486151 := bstep (se 1 (by rfl) ⟨364613, by rfl⟩ : syracuseStep 486151 = 729227) B729227
theorem B486159 : Blo 483789 486159 := bstep (se 1 (by rfl) ⟨364619, by rfl⟩ : syracuseStep 486159 = 729239) B729239
theorem B5630735 : Blo 483789 5630735 := bstep (se 1 (by rfl) ⟨4223051, by rfl⟩ : syracuseStep 5630735 = 8446103) B8446103
theorem B486203 : Blo 483789 486203 := bstep (se 1 (by rfl) ⟨364652, by rfl⟩ : syracuseStep 486203 = 729305) B729305
theorem B486279 : Blo 483789 486279 := bstep (se 1 (by rfl) ⟨364709, by rfl⟩ : syracuseStep 486279 = 729419) B729419
theorem B486287 : Blo 483789 486287 := bstep (se 1 (by rfl) ⟨364715, by rfl⟩ : syracuseStep 486287 = 729431) B729431
theorem B486331 : Blo 483789 486331 := bstep (se 1 (by rfl) ⟨364748, by rfl⟩ : syracuseStep 486331 = 729497) B729497
theorem B486407 : Blo 483789 486407 := bstep (se 1 (by rfl) ⟨364805, by rfl⟩ : syracuseStep 486407 = 729611) B729611
theorem B486415 : Blo 483789 486415 := bstep (se 1 (by rfl) ⟨364811, by rfl⟩ : syracuseStep 486415 = 729623) B729623
theorem B486459 : Blo 483789 486459 := bstep (se 1 (by rfl) ⟨364844, by rfl⟩ : syracuseStep 486459 = 729689) B729689
theorem B486535 : Blo 483789 486535 := bstep (se 1 (by rfl) ⟨364901, by rfl⟩ : syracuseStep 486535 = 729803) B729803
theorem B584839 : Blo 483789 584839 := bstep (se 1 (by rfl) ⟨438629, by rfl⟩ : syracuseStep 584839 = 877259) B877259
theorem B486543 : Blo 483789 486543 := bstep (se 1 (by rfl) ⟨364907, by rfl⟩ : syracuseStep 486543 = 729815) B729815
theorem B486587 : Blo 483789 486587 := bstep (se 1 (by rfl) ⟨364940, by rfl⟩ : syracuseStep 486587 = 729881) B729881
theorem B486663 : Blo 483789 486663 := bstep (se 1 (by rfl) ⟨364997, by rfl⟩ : syracuseStep 486663 = 729995) B729995
theorem B486671 : Blo 483789 486671 := bstep (se 1 (by rfl) ⟨365003, by rfl⟩ : syracuseStep 486671 = 730007) B730007
theorem B486715 : Blo 483789 486715 := bstep (se 1 (by rfl) ⟨365036, by rfl⟩ : syracuseStep 486715 = 730073) B730073
theorem B17493347 : Blo 483789 17493347 := bstep (se 1 (by rfl) ⟨13120010, by rfl⟩ : syracuseStep 17493347 = 26240021) B26240021
theorem B486791 : Blo 483789 486791 := bstep (se 1 (by rfl) ⟨365093, by rfl⟩ : syracuseStep 486791 = 730187) B730187
theorem B486799 : Blo 483789 486799 := bstep (se 1 (by rfl) ⟨365099, by rfl⟩ : syracuseStep 486799 = 730199) B730199
theorem B486843 : Blo 483789 486843 := bstep (se 1 (by rfl) ⟨365132, by rfl⟩ : syracuseStep 486843 = 730265) B730265
theorem B486919 : Blo 483789 486919 := bstep (se 1 (by rfl) ⟨365189, by rfl⟩ : syracuseStep 486919 = 730379) B730379
theorem B2453003 : Blo 483789 2453003 := bstep (se 1 (by rfl) ⟨1839752, by rfl⟩ : syracuseStep 2453003 = 3679505) B3679505
theorem B486927 : Blo 483789 486927 := bstep (se 1 (by rfl) ⟨365195, by rfl⟩ : syracuseStep 486927 = 730391) B730391
theorem B486971 : Blo 483789 486971 := bstep (se 1 (by rfl) ⟨365228, by rfl⟩ : syracuseStep 486971 = 730457) B730457
theorem B20967011 : Blo 483789 20967011 := bstep (se 1 (by rfl) ⟨15725258, by rfl⟩ : syracuseStep 20967011 = 31450517) B31450517
theorem B487047 : Blo 483789 487047 := bstep (se 1 (by rfl) ⟨365285, by rfl⟩ : syracuseStep 487047 = 730571) B730571
theorem B487055 : Blo 483789 487055 := bstep (se 1 (by rfl) ⟨365291, by rfl⟩ : syracuseStep 487055 = 730583) B730583
theorem B2453165 : Blo 483789 2453165 := bstep (se 3 (by rfl) ⟨459968, by rfl⟩ : syracuseStep 2453165 = 919937) B919937
theorem B487099 : Blo 483789 487099 := bstep (se 1 (by rfl) ⟨365324, by rfl⟩ : syracuseStep 487099 = 730649) B730649
theorem B487175 : Blo 483789 487175 := bstep (se 1 (by rfl) ⟨365381, by rfl⟩ : syracuseStep 487175 = 730763) B730763
theorem B487183 : Blo 483789 487183 := bstep (se 1 (by rfl) ⟨365387, by rfl⟩ : syracuseStep 487183 = 730775) B730775
theorem B487227 : Blo 483789 487227 := bstep (se 1 (by rfl) ⟨365420, by rfl⟩ : syracuseStep 487227 = 730841) B730841
theorem B487303 : Blo 483789 487303 := bstep (se 1 (by rfl) ⟨365477, by rfl⟩ : syracuseStep 487303 = 730955) B730955
theorem B520079 : Blo 483789 520079 := bstep (se 1 (by rfl) ⟨390059, by rfl⟩ : syracuseStep 520079 = 780119) B780119
theorem B487311 : Blo 483789 487311 := bstep (se 1 (by rfl) ⟨365483, by rfl⟩ : syracuseStep 487311 = 730967) B730967
theorem B1634201 : Blo 483789 1634201 := bstep (se 2 (by rfl) ⟨612825, by rfl⟩ : syracuseStep 1634201 = 1225651) B1225651
theorem B487355 : Blo 483789 487355 := bstep (se 1 (by rfl) ⟨365516, by rfl⟩ : syracuseStep 487355 = 731033) B731033
theorem B487431 : Blo 483789 487431 := bstep (se 1 (by rfl) ⟨365573, by rfl⟩ : syracuseStep 487431 = 731147) B731147
theorem B487439 : Blo 483789 487439 := bstep (se 1 (by rfl) ⟨365579, by rfl⟩ : syracuseStep 487439 = 731159) B731159
theorem B487483 : Blo 483789 487483 := bstep (se 1 (by rfl) ⟨365612, by rfl⟩ : syracuseStep 487483 = 731225) B731225
theorem B487559 : Blo 483789 487559 := bstep (se 1 (by rfl) ⟨365669, by rfl⟩ : syracuseStep 487559 = 731339) B731339
theorem B487567 : Blo 483789 487567 := bstep (se 1 (by rfl) ⟨365675, by rfl⟩ : syracuseStep 487567 = 731351) B731351
theorem B487611 : Blo 483789 487611 := bstep (se 1 (by rfl) ⟨365708, by rfl⟩ : syracuseStep 487611 = 731417) B731417
theorem B487687 : Blo 483789 487687 := bstep (se 1 (by rfl) ⟨365765, by rfl⟩ : syracuseStep 487687 = 731531) B731531
theorem B487695 : Blo 483789 487695 := bstep (se 1 (by rfl) ⟨365771, by rfl⟩ : syracuseStep 487695 = 731543) B731543
theorem B4157729 : Blo 483789 4157729 := bstep (se 2 (by rfl) ⟨1559148, by rfl⟩ : syracuseStep 4157729 = 3118297) B3118297
theorem B487739 : Blo 483789 487739 := bstep (se 1 (by rfl) ⟨365804, by rfl⟩ : syracuseStep 487739 = 731609) B731609
theorem B520711 : Blo 483789 520711 := bstep (se 1 (by rfl) ⟨390533, by rfl⟩ : syracuseStep 520711 = 781067) B781067
theorem B1634903 : Blo 483789 1634903 := bstep (se 1 (by rfl) ⟨1226177, by rfl⟩ : syracuseStep 1634903 = 2452355) B2452355
theorem B1635389 : Blo 483789 1635389 := bstep (se 3 (by rfl) ⟨306635, by rfl⟩ : syracuseStep 1635389 = 613271) B613271
theorem B1307801 : Blo 483789 1307801 := bstep (se 2 (by rfl) ⟨490425, by rfl⟩ : syracuseStep 1307801 = 980851) B980851
theorem B2454785 : Blo 483789 2454785 := bstep (se 2 (by rfl) ⟨920544, by rfl⟩ : syracuseStep 2454785 = 1841089) B1841089
theorem B6714809 : Blo 483789 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B816655 : Blo 483789 816655 := bstep (se 1 (by rfl) ⟨612491, by rfl⟩ : syracuseStep 816655 = 1224983) B1224983
theorem B3929629 : Blo 483789 3929629 := bstep (se 3 (by rfl) ⟨736805, by rfl⟩ : syracuseStep 3929629 = 1473611) B1473611
theorem B817195 : Blo 483789 817195 := bstep (se 1 (by rfl) ⟨612896, by rfl⟩ : syracuseStep 817195 = 1225793) B1225793
theorem B2455595 : Blo 483789 2455595 := bstep (se 1 (by rfl) ⟨1841696, by rfl⟩ : syracuseStep 2455595 = 3683393) B3683393
theorem B817337 : Blo 483789 817337 := bstep (se 2 (by rfl) ⟨306501, by rfl⟩ : syracuseStep 817337 = 613003) B613003
theorem B1636793 : Blo 483789 1636793 := bstep (se 2 (by rfl) ⟨613797, by rfl⟩ : syracuseStep 1636793 = 1227595) B1227595
theorem B850447 : Blo 483789 850447 := bstep (se 1 (by rfl) ⟨637835, by rfl⟩ : syracuseStep 850447 = 1275671) B1275671
theorem B7863155 : Blo 483789 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B818039 : Blo 483789 818039 := bstep (se 1 (by rfl) ⟨613529, by rfl⟩ : syracuseStep 818039 = 1227059) B1227059
theorem B1637387 : Blo 483789 1637387 := bstep (se 1 (by rfl) ⟨1228040, by rfl⟩ : syracuseStep 1637387 = 2456081) B2456081
theorem B1637495 : Blo 483789 1637495 := bstep (se 1 (by rfl) ⟨1228121, by rfl⟩ : syracuseStep 1637495 = 2456243) B2456243
theorem B785543 : Blo 483789 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B18513197 : Blo 483789 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B818491 : Blo 483789 818491 := bstep (se 1 (by rfl) ⟨613868, by rfl⟩ : syracuseStep 818491 = 1227737) B1227737
theorem B2456891 : Blo 483789 2456891 := bstep (se 1 (by rfl) ⟨1842668, by rfl⟩ : syracuseStep 2456891 = 3685337) B3685337
theorem B1473977 : Blo 483789 1473977 := bstep (se 2 (by rfl) ⟨552741, by rfl⟩ : syracuseStep 1473977 = 1105483) B1105483
theorem B818633 : Blo 483789 818633 := bstep (se 2 (by rfl) ⟨306987, by rfl⟩ : syracuseStep 818633 = 613975) B613975
theorem B2457053 : Blo 483789 2457053 := bstep (se 3 (by rfl) ⟨460697, by rfl⟩ : syracuseStep 2457053 = 921395) B921395
theorem B5242445 : Blo 483789 5242445 := bstep (se 3 (by rfl) ⟨982958, by rfl⟩ : syracuseStep 5242445 = 1965917) B1965917
theorem B1638089 : Blo 483789 1638089 := bstep (se 2 (by rfl) ⟨614283, by rfl⟩ : syracuseStep 1638089 = 1228567) B1228567
theorem B1572641 : Blo 483789 1572641 := bstep (se 2 (by rfl) ⟨589740, by rfl⟩ : syracuseStep 1572641 = 1179481) B1179481
theorem B2457377 : Blo 483789 2457377 := bstep (se 2 (by rfl) ⟨921516, by rfl⟩ : syracuseStep 2457377 = 1843033) B1843033
theorem B4751257 : Blo 483789 4751257 := bstep (se 2 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 4751257 = 3563443) B3563443
theorem B819551 : Blo 483789 819551 := bstep (se 1 (by rfl) ⟨614663, by rfl⟩ : syracuseStep 819551 = 1229327) B1229327
theorem B1245659 : Blo 483789 1245659 := bstep (se 1 (by rfl) ⟨934244, by rfl⟩ : syracuseStep 1245659 = 1868489) B1868489
theorem B1638899 : Blo 483789 1638899 := bstep (se 1 (by rfl) ⟨1229174, by rfl⟩ : syracuseStep 1638899 = 2458349) B2458349
theorem B3703319 : Blo 483789 3703319 := bstep (se 1 (by rfl) ⟨2777489, by rfl⟩ : syracuseStep 3703319 = 5554979) B5554979
theorem B9372185 : Blo 483789 9372185 := bstep (se 2 (by rfl) ⟨3514569, by rfl⟩ : syracuseStep 9372185 = 7029139) B7029139
theorem B15958745 : Blo 483789 15958745 := bstep (se 2 (by rfl) ⟨5984529, by rfl⟩ : syracuseStep 15958745 = 11969059) B11969059
theorem B820111 : Blo 483789 820111 := bstep (se 1 (by rfl) ⟨615083, by rfl⟩ : syracuseStep 820111 = 1230167) B1230167
theorem B2950145 : Blo 483789 2950145 := bstep (se 2 (by rfl) ⟨1106304, by rfl⟩ : syracuseStep 2950145 = 2212609) B2212609
theorem B1639439 : Blo 483789 1639439 := bstep (se 1 (by rfl) ⟨1229579, by rfl⟩ : syracuseStep 1639439 = 2459159) B2459159
theorem B689401 : Blo 483789 689401 := bstep (se 2 (by rfl) ⟨258525, by rfl⟩ : syracuseStep 689401 = 517051) B517051
theorem B820793 : Blo 483789 820793 := bstep (se 2 (by rfl) ⟨307797, by rfl⟩ : syracuseStep 820793 = 615595) B615595
theorem B1640033 : Blo 483789 1640033 := bstep (se 2 (by rfl) ⟨615012, by rfl⟩ : syracuseStep 1640033 = 1230025) B1230025
theorem B919163 : Blo 483789 919163 := bstep (se 1 (by rfl) ⟨689372, by rfl⟩ : syracuseStep 919163 = 1378745) B1378745
theorem B3507857 : Blo 483789 3507857 := bstep (se 2 (by rfl) ⟨1315446, by rfl⟩ : syracuseStep 3507857 = 2630893) B2630893
theorem B3114733 : Blo 483789 3114733 := bstep (se 3 (by rfl) ⟨584012, by rfl⟩ : syracuseStep 3114733 = 1168025) B1168025
theorem B1574927 : Blo 483789 1574927 := bstep (se 1 (by rfl) ⟨1181195, by rfl⟩ : syracuseStep 1574927 = 2362391) B2362391
theorem B624719 : Blo 483789 624719 := bstep (se 1 (by rfl) ⟨468539, by rfl⟩ : syracuseStep 624719 = 937079) B937079
theorem B919649 : Blo 483789 919649 := bstep (se 2 (by rfl) ⟨344868, by rfl⟩ : syracuseStep 919649 = 689737) B689737
theorem B821495 : Blo 483789 821495 := bstep (se 1 (by rfl) ⟨616121, by rfl⟩ : syracuseStep 821495 = 1232243) B1232243
theorem B919991 : Blo 483789 919991 := bstep (se 1 (by rfl) ⟨689993, by rfl⟩ : syracuseStep 919991 = 1379987) B1379987
theorem B821839 : Blo 483789 821839 := bstep (se 1 (by rfl) ⟨616379, by rfl⟩ : syracuseStep 821839 = 1232759) B1232759
theorem B3115655 : Blo 483789 3115655 := bstep (se 1 (by rfl) ⟨2336741, by rfl⟩ : syracuseStep 3115655 = 4673483) B4673483
theorem B690887 : Blo 483789 690887 := bstep (se 1 (by rfl) ⟨518165, by rfl⟩ : syracuseStep 690887 = 1036331) B1036331
theorem B920393 : Blo 483789 920393 := bstep (se 2 (by rfl) ⟨345147, by rfl⟩ : syracuseStep 920393 = 690295) B690295
theorem B822089 : Blo 483789 822089 := bstep (se 2 (by rfl) ⟨308283, by rfl⟩ : syracuseStep 822089 = 616567) B616567
theorem B2067383 : Blo 483789 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B1641491 : Blo 483789 1641491 := bstep (se 1 (by rfl) ⟨1231118, by rfl⟩ : syracuseStep 1641491 = 2462237) B2462237
theorem B2067535 : Blo 483789 2067535 := bstep (se 1 (by rfl) ⟨1550651, by rfl⟩ : syracuseStep 2067535 = 3101303) B3101303
theorem B1838159 : Blo 483789 1838159 := bstep (se 1 (by rfl) ⟨1378619, by rfl⟩ : syracuseStep 1838159 = 2757239) B2757239
theorem B2624683 : Blo 483789 2624683 := bstep (se 1 (by rfl) ⟨1968512, by rfl⟩ : syracuseStep 2624683 = 3937025) B3937025
theorem B7015619 : Blo 483789 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B822521 : Blo 483789 822521 := bstep (se 2 (by rfl) ⟨308445, by rfl⟩ : syracuseStep 822521 = 616891) B616891
theorem B1641815 : Blo 483789 1641815 := bstep (se 1 (by rfl) ⟨1231361, by rfl⟩ : syracuseStep 1641815 = 2462723) B2462723
theorem B1379713 : Blo 483789 1379713 := bstep (se 2 (by rfl) ⟨517392, by rfl⟩ : syracuseStep 1379713 = 1034785) B1034785
theorem B822703 : Blo 483789 822703 := bstep (se 1 (by rfl) ⟨617027, by rfl⟩ : syracuseStep 822703 = 1234055) B1234055
theorem B822791 : Blo 483789 822791 := bstep (se 1 (by rfl) ⟨617093, by rfl⟩ : syracuseStep 822791 = 1234187) B1234187
theorem B921107 : Blo 483789 921107 := bstep (se 1 (by rfl) ⟨690830, by rfl⟩ : syracuseStep 921107 = 1381661) B1381661
theorem B921145 : Blo 483789 921145 := bstep (se 2 (by rfl) ⟨345429, by rfl⟩ : syracuseStep 921145 = 690859) B690859
theorem B790139 : Blo 483789 790139 := bstep (se 1 (by rfl) ⟨592604, by rfl⟩ : syracuseStep 790139 = 1185209) B1185209
theorem B1969879 : Blo 483789 1969879 := bstep (se 1 (by rfl) ⟨1477409, by rfl⟩ : syracuseStep 1969879 = 2954819) B2954819
theorem B823135 : Blo 483789 823135 := bstep (se 1 (by rfl) ⟨617351, by rfl⟩ : syracuseStep 823135 = 1234703) B1234703
theorem B921449 : Blo 483789 921449 := bstep (se 2 (by rfl) ⟨345543, by rfl⟩ : syracuseStep 921449 = 691087) B691087
theorem B1380203 : Blo 483789 1380203 := bstep (se 1 (by rfl) ⟨1035152, by rfl⟩ : syracuseStep 1380203 = 2070305) B2070305
theorem B2330477 : Blo 483789 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B7868279 : Blo 483789 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B1314721 : Blo 483789 1314721 := bstep (se 2 (by rfl) ⟨493020, by rfl⟩ : syracuseStep 1314721 = 986041) B986041
theorem B21073931 : Blo 483789 21073931 := bstep (se 1 (by rfl) ⟨15805448, by rfl⟩ : syracuseStep 21073931 = 31610897) B31610897
theorem B1478675 : Blo 483789 1478675 := bstep (se 1 (by rfl) ⟨1109006, by rfl⟩ : syracuseStep 1478675 = 2218013) B2218013
theorem B1642895 : Blo 483789 1642895 := bstep (se 1 (by rfl) ⟨1232171, by rfl⟩ : syracuseStep 1642895 = 2464343) B2464343
theorem B331321873 : Blo 483789 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B1643219 : Blo 483789 1643219 := bstep (se 1 (by rfl) ⟨1232414, by rfl⟩ : syracuseStep 1643219 = 2464829) B2464829
theorem B725753 : Blo 483789 725753 := bstep (se 2 (by rfl) ⟨272157, by rfl⟩ : syracuseStep 725753 = 544315) B544315
theorem B31822627 : Blo 483789 31822627 := bstep (se 1 (by rfl) ⟨23866970, by rfl⟩ : syracuseStep 31822627 = 47733941) B47733941
theorem B1971011 : Blo 483789 1971011 := bstep (se 1 (by rfl) ⟨1478258, by rfl⟩ : syracuseStep 1971011 = 2956517) B2956517
theorem B725855 : Blo 483789 725855 := bstep (se 1 (by rfl) ⟨544391, by rfl⟩ : syracuseStep 725855 = 1088783) B1088783
theorem B725867 : Blo 483789 725867 := bstep (se 1 (by rfl) ⟨544400, by rfl⟩ : syracuseStep 725867 = 1088801) B1088801
theorem B693211 : Blo 483789 693211 := bstep (se 1 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 693211 = 1039817) B1039817
theorem B6231005 : Blo 483789 6231005 := bstep (se 3 (by rfl) ⟨1168313, by rfl⟩ : syracuseStep 6231005 = 2336627) B2336627
theorem B726095 : Blo 483789 726095 := bstep (se 1 (by rfl) ⟨544571, by rfl⟩ : syracuseStep 726095 = 1089143) B1089143
theorem B922747 : Blo 483789 922747 := bstep (se 1 (by rfl) ⟨692060, by rfl⟩ : syracuseStep 922747 = 1384121) B1384121
theorem B726215 : Blo 483789 726215 := bstep (se 1 (by rfl) ⟨544661, by rfl⟩ : syracuseStep 726215 = 1089323) B1089323
theorem B922823 : Blo 483789 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B726377 : Blo 483789 726377 := bstep (se 2 (by rfl) ⟨272391, by rfl⟩ : syracuseStep 726377 = 544783) B544783
theorem B1316225 : Blo 483789 1316225 := bstep (se 2 (by rfl) ⟨493584, by rfl⟩ : syracuseStep 1316225 = 987169) B987169
theorem B3937679 : Blo 483789 3937679 := bstep (se 1 (by rfl) ⟨2953259, by rfl⟩ : syracuseStep 3937679 = 5906519) B5906519
theorem B726455 : Blo 483789 726455 := bstep (se 1 (by rfl) ⟨544841, by rfl⟩ : syracuseStep 726455 = 1089683) B1089683
theorem B726491 : Blo 483789 726491 := bstep (se 1 (by rfl) ⟨544868, by rfl⟩ : syracuseStep 726491 = 1089737) B1089737
theorem B1840603 : Blo 483789 1840603 := bstep (se 1 (by rfl) ⟨1380452, by rfl⟩ : syracuseStep 1840603 = 2760905) B2760905
theorem B923233 : Blo 483789 923233 := bstep (se 2 (by rfl) ⟨346212, by rfl⟩ : syracuseStep 923233 = 692425) B692425
theorem B693883 : Blo 483789 693883 := bstep (se 1 (by rfl) ⟨520412, by rfl⟩ : syracuseStep 693883 = 1040825) B1040825
theorem B2463371 : Blo 483789 2463371 := bstep (se 1 (by rfl) ⟨1847528, by rfl⟩ : syracuseStep 2463371 = 3695057) B3695057
theorem B2627261 : Blo 483789 2627261 := bstep (se 3 (by rfl) ⟨492611, by rfl⟩ : syracuseStep 2627261 = 985223) B985223
theorem B694111 : Blo 483789 694111 := bstep (se 1 (by rfl) ⟨520583, by rfl⟩ : syracuseStep 694111 = 1041167) B1041167
theorem B1644407 : Blo 483789 1644407 := bstep (se 1 (by rfl) ⟨1233305, by rfl⟩ : syracuseStep 1644407 = 2466611) B2466611
theorem B726959 : Blo 483789 726959 := bstep (se 1 (by rfl) ⟨545219, by rfl⟩ : syracuseStep 726959 = 1090439) B1090439
theorem B923575 : Blo 483789 923575 := bstep (se 1 (by rfl) ⟨692681, by rfl⟩ : syracuseStep 923575 = 1385363) B1385363
theorem B727049 : Blo 483789 727049 := bstep (se 2 (by rfl) ⟨272643, by rfl⟩ : syracuseStep 727049 = 545287) B545287
theorem B7477285 : Blo 483789 7477285 := bstep (se 4 (by rfl) ⟨700995, by rfl⟩ : syracuseStep 7477285 = 1401991) B1401991
theorem B3119141 : Blo 483789 3119141 := bstep (se 4 (by rfl) ⟨292419, by rfl⟩ : syracuseStep 3119141 = 584839) B584839
theorem B727079 : Blo 483789 727079 := bstep (se 1 (by rfl) ⟨545309, by rfl⟩ : syracuseStep 727079 = 1090619) B1090619
theorem B1644623 : Blo 483789 1644623 := bstep (se 1 (by rfl) ⟨1233467, by rfl⟩ : syracuseStep 1644623 = 2466935) B2466935
theorem B6330469 : Blo 483789 6330469 := bstep (se 4 (by rfl) ⟨593481, by rfl⟩ : syracuseStep 6330469 = 1186963) B1186963
theorem B727163 : Blo 483789 727163 := bstep (se 1 (by rfl) ⟨545372, by rfl⟩ : syracuseStep 727163 = 1090745) B1090745
theorem B727289 : Blo 483789 727289 := bstep (se 2 (by rfl) ⟨272733, by rfl⟩ : syracuseStep 727289 = 545467) B545467
theorem B3742001 : Blo 483789 3742001 := bstep (se 2 (by rfl) ⟨1403250, by rfl⟩ : syracuseStep 3742001 = 2806501) B2806501
theorem B923977 : Blo 483789 923977 := bstep (se 2 (by rfl) ⟨346491, by rfl⟩ : syracuseStep 923977 = 692983) B692983
theorem B727391 : Blo 483789 727391 := bstep (se 1 (by rfl) ⟨545543, by rfl⟩ : syracuseStep 727391 = 1091087) B1091087
theorem B727403 : Blo 483789 727403 := bstep (se 1 (by rfl) ⟨545552, by rfl⟩ : syracuseStep 727403 = 1091105) B1091105
theorem B1776001 : Blo 483789 1776001 := bstep (se 2 (by rfl) ⟨666000, by rfl⟩ : syracuseStep 1776001 = 1332001) B1332001
theorem B1645001 : Blo 483789 1645001 := bstep (se 2 (by rfl) ⟨616875, by rfl⟩ : syracuseStep 1645001 = 1233751) B1233751
theorem B2071021 : Blo 483789 2071021 := bstep (se 3 (by rfl) ⟨388316, by rfl⟩ : syracuseStep 2071021 = 776633) B776633
theorem B727631 : Blo 483789 727631 := bstep (se 1 (by rfl) ⟨545723, by rfl⟩ : syracuseStep 727631 = 1091447) B1091447
theorem B1841849 : Blo 483789 1841849 := bstep (se 2 (by rfl) ⟨690693, by rfl⟩ : syracuseStep 1841849 = 1381387) B1381387
theorem B727751 : Blo 483789 727751 := bstep (se 1 (by rfl) ⟨545813, by rfl⟩ : syracuseStep 727751 = 1091627) B1091627
theorem B1841879 : Blo 483789 1841879 := bstep (se 1 (by rfl) ⟨1381409, by rfl⟩ : syracuseStep 1841879 = 2762819) B2762819
theorem B1645271 : Blo 483789 1645271 := bstep (se 1 (by rfl) ⟨1233953, by rfl⟩ : syracuseStep 1645271 = 2467907) B2467907
theorem B727913 : Blo 483789 727913 := bstep (se 2 (by rfl) ⟨272967, by rfl⟩ : syracuseStep 727913 = 545935) B545935
theorem B3677075 : Blo 483789 3677075 := bstep (se 1 (by rfl) ⟨2757806, by rfl⟩ : syracuseStep 3677075 = 5515613) B5515613
theorem B2530223 : Blo 483789 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B1645487 : Blo 483789 1645487 := bstep (se 1 (by rfl) ⟨1234115, by rfl⟩ : syracuseStep 1645487 = 2468231) B2468231
theorem B727991 : Blo 483789 727991 := bstep (se 1 (by rfl) ⟨545993, by rfl⟩ : syracuseStep 727991 = 1091987) B1091987
theorem B728027 : Blo 483789 728027 := bstep (se 1 (by rfl) ⟨546020, by rfl⟩ : syracuseStep 728027 = 1092041) B1092041
theorem B1088531 : Blo 483789 1088531 := bstep (se 1 (by rfl) ⟨816398, by rfl⟩ : syracuseStep 1088531 = 1632797) B1632797
theorem B2104339 : Blo 483789 2104339 := bstep (se 1 (by rfl) ⟨1578254, by rfl⟩ : syracuseStep 2104339 = 3156509) B3156509
theorem B924691 : Blo 483789 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B1088873 : Blo 483789 1088873 := bstep (se 2 (by rfl) ⟨408327, by rfl⟩ : syracuseStep 1088873 = 816655) B816655
theorem B925033 : Blo 483789 925033 := bstep (se 2 (by rfl) ⟨346887, by rfl⟩ : syracuseStep 925033 = 693775) B693775
theorem B728495 : Blo 483789 728495 := bstep (se 1 (by rfl) ⟨546371, by rfl⟩ : syracuseStep 728495 = 1092743) B1092743
theorem B2760155 : Blo 483789 2760155 := bstep (se 1 (by rfl) ⟨2070116, by rfl⟩ : syracuseStep 2760155 = 4140233) B4140233
theorem B728585 : Blo 483789 728585 := bstep (se 2 (by rfl) ⟨273219, by rfl⟩ : syracuseStep 728585 = 546439) B546439
theorem B1383961 : Blo 483789 1383961 := bstep (se 2 (by rfl) ⟨518985, by rfl⟩ : syracuseStep 1383961 = 1037971) B1037971
theorem B728615 : Blo 483789 728615 := bstep (se 1 (by rfl) ⟨546461, by rfl⟩ : syracuseStep 728615 = 1092923) B1092923
theorem B728699 : Blo 483789 728699 := bstep (se 1 (by rfl) ⟨546524, by rfl⟩ : syracuseStep 728699 = 1093049) B1093049
theorem B728825 : Blo 483789 728825 := bstep (se 2 (by rfl) ⟨273309, by rfl⟩ : syracuseStep 728825 = 546619) B546619
theorem B3678047 : Blo 483789 3678047 := bstep (se 1 (by rfl) ⟨2758535, by rfl⟩ : syracuseStep 3678047 = 5517071) B5517071
theorem B728927 : Blo 483789 728927 := bstep (se 1 (by rfl) ⟨546695, by rfl⟩ : syracuseStep 728927 = 1093391) B1093391
theorem B728939 : Blo 483789 728939 := bstep (se 1 (by rfl) ⟨546704, by rfl⟩ : syracuseStep 728939 = 1093409) B1093409
theorem B1089467 : Blo 483789 1089467 := bstep (se 1 (by rfl) ⟨817100, by rfl⟩ : syracuseStep 1089467 = 1634201) B1634201
theorem B1089593 : Blo 483789 1089593 := bstep (se 2 (by rfl) ⟨408597, by rfl⟩ : syracuseStep 1089593 = 817195) B817195
theorem B1581113 : Blo 483789 1581113 := bstep (se 2 (by rfl) ⟨592917, by rfl⟩ : syracuseStep 1581113 = 1185835) B1185835
theorem B729167 : Blo 483789 729167 := bstep (se 1 (by rfl) ⟨546875, by rfl⟩ : syracuseStep 729167 = 1093751) B1093751
theorem B729287 : Blo 483789 729287 := bstep (se 1 (by rfl) ⟨546965, by rfl⟩ : syracuseStep 729287 = 1093931) B1093931
theorem B729449 : Blo 483789 729449 := bstep (se 2 (by rfl) ⟨273543, by rfl⟩ : syracuseStep 729449 = 547087) B547087
theorem B1089935 : Blo 483789 1089935 := bstep (se 1 (by rfl) ⟨817451, by rfl⟩ : syracuseStep 1089935 = 1634903) B1634903
theorem B729527 : Blo 483789 729527 := bstep (se 1 (by rfl) ⟨547145, by rfl⟩ : syracuseStep 729527 = 1094291) B1094291
theorem B729563 : Blo 483789 729563 := bstep (se 1 (by rfl) ⟨547172, by rfl⟩ : syracuseStep 729563 = 1094345) B1094345
theorem B1090259 : Blo 483789 1090259 := bstep (se 1 (by rfl) ⟨817694, by rfl⟩ : syracuseStep 1090259 = 1635389) B1635389
theorem B730031 : Blo 483789 730031 := bstep (se 1 (by rfl) ⟨547523, by rfl⟩ : syracuseStep 730031 = 1095047) B1095047
theorem B730121 : Blo 483789 730121 := bstep (se 2 (by rfl) ⟨273795, by rfl⟩ : syracuseStep 730121 = 547591) B547591
theorem B730151 : Blo 483789 730151 := bstep (se 1 (by rfl) ⟨547613, by rfl⟩ : syracuseStep 730151 = 1095227) B1095227
theorem B730235 : Blo 483789 730235 := bstep (se 1 (by rfl) ⟨547676, by rfl⟩ : syracuseStep 730235 = 1095353) B1095353
theorem B730361 : Blo 483789 730361 := bstep (se 2 (by rfl) ⟨273885, by rfl⟩ : syracuseStep 730361 = 547771) B547771
theorem B1844491 : Blo 483789 1844491 := bstep (se 1 (by rfl) ⟨1383368, by rfl⟩ : syracuseStep 1844491 = 2766737) B2766737
theorem B730463 : Blo 483789 730463 := bstep (se 1 (by rfl) ⟨547847, by rfl⟩ : syracuseStep 730463 = 1095695) B1095695
theorem B730475 : Blo 483789 730475 := bstep (se 1 (by rfl) ⟨547856, by rfl⟩ : syracuseStep 730475 = 1095713) B1095713
theorem B1844795 : Blo 483789 1844795 := bstep (se 1 (by rfl) ⟨1383596, by rfl⟩ : syracuseStep 1844795 = 2767193) B2767193
theorem B730703 : Blo 483789 730703 := bstep (se 1 (by rfl) ⟨548027, by rfl⟩ : syracuseStep 730703 = 1096055) B1096055
theorem B1091195 : Blo 483789 1091195 := bstep (se 1 (by rfl) ⟨818396, by rfl⟩ : syracuseStep 1091195 = 1636793) B1636793
theorem B2762363 : Blo 483789 2762363 := bstep (se 1 (by rfl) ⟨2071772, by rfl⟩ : syracuseStep 2762363 = 4143545) B4143545
theorem B730823 : Blo 483789 730823 := bstep (se 1 (by rfl) ⟨548117, by rfl⟩ : syracuseStep 730823 = 1096235) B1096235
theorem B1091321 : Blo 483789 1091321 := bstep (se 2 (by rfl) ⟨409245, by rfl⟩ : syracuseStep 1091321 = 818491) B818491
theorem B730985 : Blo 483789 730985 := bstep (se 2 (by rfl) ⟨274119, by rfl⟩ : syracuseStep 730985 = 548239) B548239
theorem B2467745 : Blo 483789 2467745 := bstep (se 2 (by rfl) ⟨925404, by rfl⟩ : syracuseStep 2467745 = 1850809) B1850809
theorem B731063 : Blo 483789 731063 := bstep (se 1 (by rfl) ⟨548297, by rfl⟩ : syracuseStep 731063 = 1096595) B1096595
theorem B731099 : Blo 483789 731099 := bstep (se 1 (by rfl) ⟨548324, by rfl⟩ : syracuseStep 731099 = 1096649) B1096649
theorem B1091591 : Blo 483789 1091591 := bstep (se 1 (by rfl) ⟨818693, by rfl⟩ : syracuseStep 1091591 = 1637387) B1637387
theorem B7874567 : Blo 483789 7874567 := bstep (se 1 (by rfl) ⟨5905925, by rfl⟩ : syracuseStep 7874567 = 11811851) B11811851
theorem B1091663 : Blo 483789 1091663 := bstep (se 1 (by rfl) ⟨818747, by rfl⟩ : syracuseStep 1091663 = 1637495) B1637495
theorem B1386877 : Blo 483789 1386877 := bstep (se 3 (by rfl) ⟨260039, by rfl⟩ : syracuseStep 1386877 = 520079) B520079
theorem B731567 : Blo 483789 731567 := bstep (se 1 (by rfl) ⟨548675, by rfl⟩ : syracuseStep 731567 = 1097351) B1097351
theorem B1092059 : Blo 483789 1092059 := bstep (se 1 (by rfl) ⟨819044, by rfl⟩ : syracuseStep 1092059 = 1638089) B1638089
theorem B731657 : Blo 483789 731657 := bstep (se 2 (by rfl) ⟨274371, by rfl⟩ : syracuseStep 731657 = 548743) B548743
theorem B6335009 : Blo 483789 6335009 := bstep (se 2 (by rfl) ⟨2375628, by rfl⟩ : syracuseStep 6335009 = 4751257) B4751257
theorem B1845949 : Blo 483789 1845949 := bstep (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) B692231
theorem B1387219 : Blo 483789 1387219 := bstep (se 1 (by rfl) ⟨1040414, by rfl⟩ : syracuseStep 1387219 = 2080829) B2080829
theorem B3124115 : Blo 483789 3124115 := bstep (se 1 (by rfl) ⟨2343086, by rfl⟩ : syracuseStep 3124115 = 4686173) B4686173
theorem B1092527 : Blo 483789 1092527 := bstep (se 1 (by rfl) ⟨819395, by rfl⟩ : syracuseStep 1092527 = 1638791) B1638791
theorem B1616915 : Blo 483789 1616915 := bstep (se 1 (by rfl) ⟨1212686, by rfl⟩ : syracuseStep 1616915 = 2425373) B2425373
theorem B1092779 : Blo 483789 1092779 := bstep (se 1 (by rfl) ⟨819584, by rfl⟩ : syracuseStep 1092779 = 1639169) B1639169
theorem B6204761 : Blo 483789 6204761 := bstep (se 2 (by rfl) ⟨2326785, by rfl⟩ : syracuseStep 6204761 = 4653571) B4653571
theorem B3321431 : Blo 483789 3321431 := bstep (se 1 (by rfl) ⟨2491073, by rfl⟩ : syracuseStep 3321431 = 4982147) B4982147
theorem B2076283 : Blo 483789 2076283 := bstep (se 1 (by rfl) ⟨1557212, by rfl⟩ : syracuseStep 2076283 = 3114425) B3114425
theorem B1846907 : Blo 483789 1846907 := bstep (se 1 (by rfl) ⟨1385180, by rfl⟩ : syracuseStep 1846907 = 2770361) B2770361
theorem B1093319 : Blo 483789 1093319 := bstep (se 1 (by rfl) ⟨819989, by rfl⟩ : syracuseStep 1093319 = 1639979) B1639979
theorem B3125087 : Blo 483789 3125087 := bstep (se 1 (by rfl) ⟨2343815, by rfl⟩ : syracuseStep 3125087 = 4687631) B4687631
theorem B1847681 : Blo 483789 1847681 := bstep (se 2 (by rfl) ⟨692880, by rfl⟩ : syracuseStep 1847681 = 1385761) B1385761
theorem B1094183 : Blo 483789 1094183 := bstep (se 1 (by rfl) ⟨820637, by rfl⟩ : syracuseStep 1094183 = 1641275) B1641275
theorem B1749703 : Blo 483789 1749703 := bstep (se 1 (by rfl) ⟨1312277, by rfl⟩ : syracuseStep 1749703 = 2624555) B2624555
theorem B3846865 : Blo 483789 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B1094507 : Blo 483789 1094507 := bstep (se 1 (by rfl) ⟨820880, by rfl⟩ : syracuseStep 1094507 = 1641761) B1641761
theorem B1094561 : Blo 483789 1094561 := bstep (se 2 (by rfl) ⟨410460, by rfl⟩ : syracuseStep 1094561 = 820921) B820921
theorem B1225975 : Blo 483789 1225975 := bstep (se 1 (by rfl) ⟨919481, by rfl⟩ : syracuseStep 1225975 = 1838963) B1838963
theorem B1094903 : Blo 483789 1094903 := bstep (se 1 (by rfl) ⟨821177, by rfl⟩ : syracuseStep 1094903 = 1642355) B1642355
theorem B2078095 : Blo 483789 2078095 := bstep (se 1 (by rfl) ⟨1558571, by rfl⟩ : syracuseStep 2078095 = 3117143) B3117143
theorem B1226249 : Blo 483789 1226249 := bstep (se 2 (by rfl) ⟨459843, by rfl⟩ : syracuseStep 1226249 = 919687) B919687
theorem B1848865 : Blo 483789 1848865 := bstep (se 2 (by rfl) ⟨693324, by rfl⟩ : syracuseStep 1848865 = 1386649) B1386649
theorem B1226279 : Blo 483789 1226279 := bstep (se 1 (by rfl) ⟨919709, by rfl⟩ : syracuseStep 1226279 = 1839419) B1839419
theorem B3683879 : Blo 483789 3683879 := bstep (se 1 (by rfl) ⟨2762909, by rfl⟩ : syracuseStep 3683879 = 5525819) B5525819
theorem B3978973 : Blo 483789 3978973 := bstep (se 3 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 3978973 = 1492115) B1492115
theorem B4667179 : Blo 483789 4667179 := bstep (se 1 (by rfl) ⟨3500384, by rfl⟩ : syracuseStep 4667179 = 7000769) B7000769
theorem B1095497 : Blo 483789 1095497 := bstep (se 2 (by rfl) ⟨410811, by rfl⟩ : syracuseStep 1095497 = 821623) B821623
theorem B1226603 : Blo 483789 1226603 := bstep (se 1 (by rfl) ⟨919952, by rfl⟩ : syracuseStep 1226603 = 1839905) B1839905
theorem B1849351 : Blo 483789 1849351 := bstep (se 1 (by rfl) ⟨1387013, by rfl⟩ : syracuseStep 1849351 = 2774027) B2774027
theorem B1554547 : Blo 483789 1554547 := bstep (se 1 (by rfl) ⟨1165910, by rfl⟩ : syracuseStep 1554547 = 2331821) B2331821
theorem B15350219 : Blo 483789 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B1849837 : Blo 483789 1849837 := bstep (se 3 (by rfl) ⟨346844, by rfl⟩ : syracuseStep 1849837 = 693689) B693689
theorem B1227251 : Blo 483789 1227251 := bstep (se 1 (by rfl) ⟨920438, by rfl⟩ : syracuseStep 1227251 = 1840877) B1840877
theorem B1096289 : Blo 483789 1096289 := bstep (se 2 (by rfl) ⟨411108, by rfl⟩ : syracuseStep 1096289 = 822217) B822217
theorem B6666887 : Blo 483789 6666887 := bstep (se 1 (by rfl) ⟨5000165, by rfl⟩ : syracuseStep 6666887 = 10000331) B10000331
theorem B1850141 : Blo 483789 1850141 := bstep (se 3 (by rfl) ⟨346901, by rfl⟩ : syracuseStep 1850141 = 693803) B693803
theorem B1096631 : Blo 483789 1096631 := bstep (se 1 (by rfl) ⟨822473, by rfl⟩ : syracuseStep 1096631 = 1644947) B1644947
theorem B1227707 : Blo 483789 1227707 := bstep (se 1 (by rfl) ⟨920780, by rfl⟩ : syracuseStep 1227707 = 1841561) B1841561
theorem B1097225 : Blo 483789 1097225 := bstep (se 2 (by rfl) ⟨411459, by rfl⟩ : syracuseStep 1097225 = 822919) B822919
theorem B1228385 : Blo 483789 1228385 := bstep (se 2 (by rfl) ⟨460644, by rfl⟩ : syracuseStep 1228385 = 921289) B921289
theorem B3489427 : Blo 483789 3489427 := bstep (se 1 (by rfl) ⟨2617070, by rfl⟩ : syracuseStep 3489427 = 5234141) B5234141
theorem B1752787 : Blo 483789 1752787 := bstep (se 1 (by rfl) ⟨1314590, by rfl⟩ : syracuseStep 1752787 = 2629181) B2629181
theorem B2080505 : Blo 483789 2080505 := bstep (se 2 (by rfl) ⟨780189, by rfl⟩ : syracuseStep 2080505 = 1560379) B1560379
theorem B2768903 : Blo 483789 2768903 := bstep (se 1 (by rfl) ⟨2076677, by rfl⟩ : syracuseStep 2768903 = 4153355) B4153355
theorem B1753625 : Blo 483789 1753625 := bstep (se 2 (by rfl) ⟨657609, by rfl⟩ : syracuseStep 1753625 = 1315219) B1315219
theorem B1229843 : Blo 483789 1229843 := bstep (se 1 (by rfl) ⟨922382, by rfl⟩ : syracuseStep 1229843 = 1844765) B1844765
theorem B1197227 : Blo 483789 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B1230299 : Blo 483789 1230299 := bstep (se 1 (by rfl) ⟨922724, by rfl⟩ : syracuseStep 1230299 = 1845449) B1845449
theorem B3753611 : Blo 483789 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B2082503 : Blo 483789 2082503 := bstep (se 1 (by rfl) ⟨1561877, by rfl⟩ : syracuseStep 2082503 = 3123755) B3123755
theorem B1754833 : Blo 483789 1754833 := bstep (se 2 (by rfl) ⟨658062, by rfl⟩ : syracuseStep 1754833 = 1316125) B1316125
theorem B3753823 : Blo 483789 3753823 := bstep (se 1 (by rfl) ⟨2815367, by rfl⟩ : syracuseStep 3753823 = 5630735) B5630735
theorem B5130497 : Blo 483789 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B13978007 : Blo 483789 13978007 := bstep (se 1 (by rfl) ⟨10483505, by rfl⟩ : syracuseStep 13978007 = 20967011) B20967011
theorem B3983905 : Blo 483789 3983905 := bstep (se 2 (by rfl) ⟨1493964, by rfl⟩ : syracuseStep 3983905 = 2987929) B2987929
theorem B1231483 : Blo 483789 1231483 := bstep (se 1 (by rfl) ⟨923612, by rfl⟩ : syracuseStep 1231483 = 1847225) B1847225
theorem B2771819 : Blo 483789 2771819 := bstep (se 1 (by rfl) ⟨2078864, by rfl⟩ : syracuseStep 2771819 = 4157729) B4157729
theorem B1035271 : Blo 483789 1035271 := bstep (se 1 (by rfl) ⟨776453, by rfl⟩ : syracuseStep 1035271 = 1552907) B1552907
theorem B1166393 : Blo 483789 1166393 := bstep (se 2 (by rfl) ⟨437397, by rfl⟩ : syracuseStep 1166393 = 874795) B874795
theorem B1133929 : Blo 483789 1133929 := bstep (se 2 (by rfl) ⟨425223, by rfl⟩ : syracuseStep 1133929 = 850447) B850447
theorem B871867 : Blo 483789 871867 := bstep (se 1 (by rfl) ⟨653900, by rfl⟩ : syracuseStep 871867 = 1307801) B1307801
theorem B4476539 : Blo 483789 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B1166987 : Blo 483789 1166987 := bstep (se 1 (by rfl) ⟨875240, by rfl⟩ : syracuseStep 1166987 = 1750481) B1750481
theorem B1756811 : Blo 483789 1756811 := bstep (se 1 (by rfl) ⟨1317608, by rfl⟩ : syracuseStep 1756811 = 2635217) B2635217
theorem B1756883 : Blo 483789 1756883 := bstep (se 1 (by rfl) ⟨1317662, by rfl⟩ : syracuseStep 1756883 = 2635325) B2635325
theorem B544891 : Blo 483789 544891 := bstep (se 1 (by rfl) ⟨408668, by rfl⟩ : syracuseStep 544891 = 817337) B817337
theorem B545359 : Blo 483789 545359 := bstep (se 1 (by rfl) ⟨409019, by rfl⟩ : syracuseStep 545359 = 818039) B818039
theorem B1561211 : Blo 483789 1561211 := bstep (se 1 (by rfl) ⟨1170908, by rfl⟩ : syracuseStep 1561211 = 2341817) B2341817
theorem B12342131 : Blo 483789 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B545755 : Blo 483789 545755 := bstep (se 1 (by rfl) ⟨409316, by rfl⟩ : syracuseStep 545755 = 818633) B818633
theorem B3724289 : Blo 483789 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B3494963 : Blo 483789 3494963 := bstep (se 1 (by rfl) ⟨2621222, by rfl⟩ : syracuseStep 3494963 = 5242445) B5242445
theorem B775531 : Blo 483789 775531 := bstep (se 1 (by rfl) ⟨581648, by rfl⟩ : syracuseStep 775531 = 1163297) B1163297
theorem B546223 : Blo 483789 546223 := bstep (se 1 (by rfl) ⟨409667, by rfl⟩ : syracuseStep 546223 = 819335) B819335
theorem B546655 : Blo 483789 546655 := bstep (se 1 (by rfl) ⟨409991, by rfl⟩ : syracuseStep 546655 = 819983) B819983
theorem B3954541 : Blo 483789 3954541 := bstep (se 3 (by rfl) ⟨741476, by rfl⟩ : syracuseStep 3954541 = 1482953) B1482953
theorem B1038415 : Blo 483789 1038415 := bstep (se 1 (by rfl) ⟨778811, by rfl⟩ : syracuseStep 1038415 = 1557623) B1557623
theorem B547015 : Blo 483789 547015 := bstep (se 1 (by rfl) ⟨410261, by rfl⟩ : syracuseStep 547015 = 820523) B820523
theorem B4152293 : Blo 483789 4152293 := bstep (se 4 (by rfl) ⟨389277, by rfl⟩ : syracuseStep 4152293 = 778555) B778555
theorem B547879 : Blo 483789 547879 := bstep (se 1 (by rfl) ⟨410909, by rfl⟩ : syracuseStep 547879 = 821819) B821819
theorem B3104173 : Blo 483789 3104173 := bstep (se 3 (by rfl) ⟨582032, by rfl⟩ : syracuseStep 3104173 = 1164065) B1164065
theorem B777851 : Blo 483789 777851 := bstep (se 1 (by rfl) ⟨583388, by rfl⟩ : syracuseStep 777851 = 1166777) B1166777
theorem B1171361 : Blo 483789 1171361 := bstep (se 2 (by rfl) ⟨439260, by rfl⟩ : syracuseStep 1171361 = 878521) B878521
theorem B2777125 : Blo 483789 2777125 := bstep (se 4 (by rfl) ⟨260355, by rfl⟩ : syracuseStep 2777125 = 520711) B520711
theorem B876791 : Blo 483789 876791 := bstep (se 1 (by rfl) ⟨657593, by rfl⟩ : syracuseStep 876791 = 1315187) B1315187
theorem B582071 : Blo 483789 582071 := bstep (se 1 (by rfl) ⟨436553, by rfl⟩ : syracuseStep 582071 = 873107) B873107
theorem B483803 : Blo 483789 483803 := bstep (se 1 (by rfl) ⟨362852, by rfl⟩ : syracuseStep 483803 = 725705) B725705
theorem B483879 : Blo 483789 483879 := bstep (se 1 (by rfl) ⟨362909, by rfl⟩ : syracuseStep 483879 = 725819) B725819
theorem B28107323 : Blo 483789 28107323 := bstep (se 1 (by rfl) ⟨21080492, by rfl⟩ : syracuseStep 28107323 = 42160985) B42160985
theorem B483919 : Blo 483789 483919 := bstep (se 1 (by rfl) ⟨362939, by rfl⟩ : syracuseStep 483919 = 725879) B725879
theorem B483935 : Blo 483789 483935 := bstep (se 1 (by rfl) ⟨362951, by rfl⟩ : syracuseStep 483935 = 725903) B725903
theorem B483963 : Blo 483789 483963 := bstep (se 1 (by rfl) ⟨362972, by rfl⟩ : syracuseStep 483963 = 725945) B725945
theorem B484015 : Blo 483789 484015 := bstep (se 1 (by rfl) ⟨363011, by rfl⟩ : syracuseStep 484015 = 726023) B726023
theorem B484039 : Blo 483789 484039 := bstep (se 1 (by rfl) ⟨363029, by rfl⟩ : syracuseStep 484039 = 726059) B726059
theorem B484059 : Blo 483789 484059 := bstep (se 1 (by rfl) ⟨363044, by rfl⟩ : syracuseStep 484059 = 726089) B726089
theorem B484135 : Blo 483789 484135 := bstep (se 1 (by rfl) ⟨363101, by rfl⟩ : syracuseStep 484135 = 726203) B726203
theorem B2450249 : Blo 483789 2450249 := bstep (se 2 (by rfl) ⟨918843, by rfl⟩ : syracuseStep 2450249 = 1837687) B1837687
theorem B484175 : Blo 483789 484175 := bstep (se 1 (by rfl) ⟨363131, by rfl⟩ : syracuseStep 484175 = 726263) B726263
theorem B484191 : Blo 483789 484191 := bstep (se 1 (by rfl) ⟨363143, by rfl⟩ : syracuseStep 484191 = 726287) B726287
theorem B484219 : Blo 483789 484219 := bstep (se 1 (by rfl) ⟨363164, by rfl⟩ : syracuseStep 484219 = 726329) B726329
theorem B484271 : Blo 483789 484271 := bstep (se 1 (by rfl) ⟨363203, by rfl⟩ : syracuseStep 484271 = 726407) B726407
theorem B3990455 : Blo 483789 3990455 := bstep (se 1 (by rfl) ⟨2992841, by rfl⟩ : syracuseStep 3990455 = 5985683) B5985683
theorem B3695543 : Blo 483789 3695543 := bstep (se 1 (by rfl) ⟨2771657, by rfl⟩ : syracuseStep 3695543 = 5543315) B5543315
theorem B484295 : Blo 483789 484295 := bstep (se 1 (by rfl) ⟨363221, by rfl⟩ : syracuseStep 484295 = 726443) B726443
theorem B484315 : Blo 483789 484315 := bstep (se 1 (by rfl) ⟨363236, by rfl⟩ : syracuseStep 484315 = 726473) B726473
theorem B484391 : Blo 483789 484391 := bstep (se 1 (by rfl) ⟨363293, by rfl⟩ : syracuseStep 484391 = 726587) B726587
theorem B484431 : Blo 483789 484431 := bstep (se 1 (by rfl) ⟨363323, by rfl⟩ : syracuseStep 484431 = 726647) B726647
theorem B484447 : Blo 483789 484447 := bstep (se 1 (by rfl) ⟨363335, by rfl⟩ : syracuseStep 484447 = 726671) B726671
theorem B484475 : Blo 483789 484475 := bstep (se 1 (by rfl) ⟨363356, by rfl⟩ : syracuseStep 484475 = 726713) B726713
theorem B4449451 : Blo 483789 4449451 := bstep (se 1 (by rfl) ⟨3337088, by rfl⟩ : syracuseStep 4449451 = 6674177) B6674177
theorem B484527 : Blo 483789 484527 := bstep (se 1 (by rfl) ⟨363395, by rfl⟩ : syracuseStep 484527 = 726791) B726791
theorem B484551 : Blo 483789 484551 := bstep (se 1 (by rfl) ⟨363413, by rfl⟩ : syracuseStep 484551 = 726827) B726827
theorem B484571 : Blo 483789 484571 := bstep (se 1 (by rfl) ⟨363428, by rfl⟩ : syracuseStep 484571 = 726857) B726857
theorem B484647 : Blo 483789 484647 := bstep (se 1 (by rfl) ⟨363485, by rfl⟩ : syracuseStep 484647 = 726971) B726971
theorem B484687 : Blo 483789 484687 := bstep (se 1 (by rfl) ⟨363515, by rfl⟩ : syracuseStep 484687 = 727031) B727031
theorem B484703 : Blo 483789 484703 := bstep (se 1 (by rfl) ⟨363527, by rfl⟩ : syracuseStep 484703 = 727055) B727055
theorem B484731 : Blo 483789 484731 := bstep (se 1 (by rfl) ⟨363548, by rfl⟩ : syracuseStep 484731 = 727097) B727097
theorem B484783 : Blo 483789 484783 := bstep (se 1 (by rfl) ⟨363587, by rfl⟩ : syracuseStep 484783 = 727175) B727175
theorem B615863 : Blo 483789 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B484807 : Blo 483789 484807 := bstep (se 1 (by rfl) ⟨363605, by rfl⟩ : syracuseStep 484807 = 727211) B727211
theorem B13297097 : Blo 483789 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B484827 : Blo 483789 484827 := bstep (se 1 (by rfl) ⟨363620, by rfl⟩ : syracuseStep 484827 = 727241) B727241
theorem B484903 : Blo 483789 484903 := bstep (se 1 (by rfl) ⟨363677, by rfl⟩ : syracuseStep 484903 = 727355) B727355
theorem B484943 : Blo 483789 484943 := bstep (se 1 (by rfl) ⟨363707, by rfl⟩ : syracuseStep 484943 = 727415) B727415
theorem B616015 : Blo 483789 616015 := bstep (se 1 (by rfl) ⟨462011, by rfl⟩ : syracuseStep 616015 = 924023) B924023
theorem B484959 : Blo 483789 484959 := bstep (se 1 (by rfl) ⟨363719, by rfl⟩ : syracuseStep 484959 = 727439) B727439
theorem B484987 : Blo 483789 484987 := bstep (se 1 (by rfl) ⟨363740, by rfl⟩ : syracuseStep 484987 = 727481) B727481
theorem B485039 : Blo 483789 485039 := bstep (se 1 (by rfl) ⟨363779, by rfl⟩ : syracuseStep 485039 = 727559) B727559
theorem B485063 : Blo 483789 485063 := bstep (se 1 (by rfl) ⟨363797, by rfl⟩ : syracuseStep 485063 = 727595) B727595
theorem B485083 : Blo 483789 485083 := bstep (se 1 (by rfl) ⟨363812, by rfl⟩ : syracuseStep 485083 = 727625) B727625
theorem B485159 : Blo 483789 485159 := bstep (se 1 (by rfl) ⟨363869, by rfl⟩ : syracuseStep 485159 = 727739) B727739
theorem B485199 : Blo 483789 485199 := bstep (se 1 (by rfl) ⟨363899, by rfl⟩ : syracuseStep 485199 = 727799) B727799
theorem B485215 : Blo 483789 485215 := bstep (se 1 (by rfl) ⟨363911, by rfl⟩ : syracuseStep 485215 = 727823) B727823
theorem B485243 : Blo 483789 485243 := bstep (se 1 (by rfl) ⟨363932, by rfl⟩ : syracuseStep 485243 = 727865) B727865
theorem B485295 : Blo 483789 485295 := bstep (se 1 (by rfl) ⟨363971, by rfl⟩ : syracuseStep 485295 = 727943) B727943
theorem B485319 : Blo 483789 485319 := bstep (se 1 (by rfl) ⟨363989, by rfl⟩ : syracuseStep 485319 = 727979) B727979
theorem B4679633 : Blo 483789 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B485339 : Blo 483789 485339 := bstep (se 1 (by rfl) ⟨364004, by rfl⟩ : syracuseStep 485339 = 728009) B728009
theorem B5531651 : Blo 483789 5531651 := bstep (se 1 (by rfl) ⟨4148738, by rfl⟩ : syracuseStep 5531651 = 8297477) B8297477
theorem B2222095 : Blo 483789 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B485415 : Blo 483789 485415 := bstep (se 1 (by rfl) ⟨364061, by rfl⟩ : syracuseStep 485415 = 728123) B728123
theorem B485455 : Blo 483789 485455 := bstep (se 1 (by rfl) ⟨364091, by rfl⟩ : syracuseStep 485455 = 728183) B728183
theorem B2451545 : Blo 483789 2451545 := bstep (se 2 (by rfl) ⟨919329, by rfl⟩ : syracuseStep 2451545 = 1838659) B1838659
theorem B485471 : Blo 483789 485471 := bstep (se 1 (by rfl) ⟨364103, by rfl⟩ : syracuseStep 485471 = 728207) B728207
theorem B485499 : Blo 483789 485499 := bstep (se 1 (by rfl) ⟨364124, by rfl⟩ : syracuseStep 485499 = 728249) B728249
theorem B485551 : Blo 483789 485551 := bstep (se 1 (by rfl) ⟨364163, by rfl⟩ : syracuseStep 485551 = 728327) B728327
theorem B485575 : Blo 483789 485575 := bstep (se 1 (by rfl) ⟨364181, by rfl⟩ : syracuseStep 485575 = 728363) B728363
theorem B485595 : Blo 483789 485595 := bstep (se 1 (by rfl) ⟨364196, by rfl⟩ : syracuseStep 485595 = 728393) B728393
theorem B485671 : Blo 483789 485671 := bstep (se 1 (by rfl) ⟨364253, by rfl⟩ : syracuseStep 485671 = 728507) B728507
theorem B485711 : Blo 483789 485711 := bstep (se 1 (by rfl) ⟨364283, by rfl⟩ : syracuseStep 485711 = 728567) B728567
theorem B485727 : Blo 483789 485727 := bstep (se 1 (by rfl) ⟨364295, by rfl⟩ : syracuseStep 485727 = 728591) B728591
theorem B3697001 : Blo 483789 3697001 := bstep (se 2 (by rfl) ⟨1386375, by rfl⟩ : syracuseStep 3697001 = 2772751) B2772751
theorem B485755 : Blo 483789 485755 := bstep (se 1 (by rfl) ⟨364316, by rfl⟩ : syracuseStep 485755 = 728633) B728633
theorem B485807 : Blo 483789 485807 := bstep (se 1 (by rfl) ⟨364355, by rfl⟩ : syracuseStep 485807 = 728711) B728711
theorem B584119 : Blo 483789 584119 := bstep (se 1 (by rfl) ⟨438089, by rfl⟩ : syracuseStep 584119 = 876179) B876179
theorem B485831 : Blo 483789 485831 := bstep (se 1 (by rfl) ⟨364373, by rfl⟩ : syracuseStep 485831 = 728747) B728747
theorem B485851 : Blo 483789 485851 := bstep (se 1 (by rfl) ⟨364388, by rfl⟩ : syracuseStep 485851 = 728777) B728777
theorem B485927 : Blo 483789 485927 := bstep (se 1 (by rfl) ⟨364445, by rfl⟩ : syracuseStep 485927 = 728891) B728891
theorem B485967 : Blo 483789 485967 := bstep (se 1 (by rfl) ⟨364475, by rfl⟩ : syracuseStep 485967 = 728951) B728951
theorem B485983 : Blo 483789 485983 := bstep (se 1 (by rfl) ⟨364487, by rfl⟩ : syracuseStep 485983 = 728975) B728975
theorem B486011 : Blo 483789 486011 := bstep (se 1 (by rfl) ⟨364508, by rfl⟩ : syracuseStep 486011 = 729017) B729017
theorem B486063 : Blo 483789 486063 := bstep (se 1 (by rfl) ⟨364547, by rfl⟩ : syracuseStep 486063 = 729095) B729095
theorem B486087 : Blo 483789 486087 := bstep (se 1 (by rfl) ⟨364565, by rfl⟩ : syracuseStep 486087 = 729131) B729131
theorem B617159 : Blo 483789 617159 := bstep (se 1 (by rfl) ⟨462869, by rfl⟩ : syracuseStep 617159 = 925739) B925739
theorem B486107 : Blo 483789 486107 := bstep (se 1 (by rfl) ⟨364580, by rfl⟩ : syracuseStep 486107 = 729161) B729161
theorem B486183 : Blo 483789 486183 := bstep (se 1 (by rfl) ⟨364637, by rfl⟩ : syracuseStep 486183 = 729275) B729275
theorem B1633067 : Blo 483789 1633067 := bstep (se 1 (by rfl) ⟨1224800, by rfl⟩ : syracuseStep 1633067 = 2449601) B2449601
theorem B486223 : Blo 483789 486223 := bstep (se 1 (by rfl) ⟨364667, by rfl⟩ : syracuseStep 486223 = 729335) B729335
theorem B486239 : Blo 483789 486239 := bstep (se 1 (by rfl) ⟨364679, by rfl⟩ : syracuseStep 486239 = 729359) B729359
theorem B617311 : Blo 483789 617311 := bstep (se 1 (by rfl) ⟨462983, by rfl⟩ : syracuseStep 617311 = 925967) B925967
theorem B486267 : Blo 483789 486267 := bstep (se 1 (by rfl) ⟨364700, by rfl⟩ : syracuseStep 486267 = 729401) B729401
theorem B486319 : Blo 483789 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B486343 : Blo 483789 486343 := bstep (se 1 (by rfl) ⟨364757, by rfl⟩ : syracuseStep 486343 = 729515) B729515
theorem B486363 : Blo 483789 486363 := bstep (se 1 (by rfl) ⟨364772, by rfl⟩ : syracuseStep 486363 = 729545) B729545
theorem B486439 : Blo 483789 486439 := bstep (se 1 (by rfl) ⟨364829, by rfl⟩ : syracuseStep 486439 = 729659) B729659
theorem B1633337 : Blo 483789 1633337 := bstep (se 2 (by rfl) ⟨612501, by rfl⟩ : syracuseStep 1633337 = 1225003) B1225003
theorem B486479 : Blo 483789 486479 := bstep (se 1 (by rfl) ⟨364859, by rfl⟩ : syracuseStep 486479 = 729719) B729719
theorem B486495 : Blo 483789 486495 := bstep (se 1 (by rfl) ⟨364871, by rfl⟩ : syracuseStep 486495 = 729743) B729743
theorem B486523 : Blo 483789 486523 := bstep (se 1 (by rfl) ⟨364892, by rfl⟩ : syracuseStep 486523 = 729785) B729785
theorem B486575 : Blo 483789 486575 := bstep (se 1 (by rfl) ⟨364931, by rfl⟩ : syracuseStep 486575 = 729863) B729863
theorem B3501251 : Blo 483789 3501251 := bstep (se 1 (by rfl) ⟨2625938, by rfl⟩ : syracuseStep 3501251 = 5251877) B5251877
theorem B486599 : Blo 483789 486599 := bstep (se 1 (by rfl) ⟨364949, by rfl⟩ : syracuseStep 486599 = 729899) B729899
theorem B486619 : Blo 483789 486619 := bstep (se 1 (by rfl) ⟨364964, by rfl⟩ : syracuseStep 486619 = 729929) B729929
theorem B486695 : Blo 483789 486695 := bstep (se 1 (by rfl) ⟨365021, by rfl⟩ : syracuseStep 486695 = 730043) B730043
theorem B486735 : Blo 483789 486735 := bstep (se 1 (by rfl) ⟨365051, by rfl⟩ : syracuseStep 486735 = 730103) B730103
theorem B486751 : Blo 483789 486751 := bstep (se 1 (by rfl) ⟨365063, by rfl⟩ : syracuseStep 486751 = 730127) B730127
theorem B486779 : Blo 483789 486779 := bstep (se 1 (by rfl) ⟨365084, by rfl⟩ : syracuseStep 486779 = 730169) B730169
theorem B1633661 : Blo 483789 1633661 := bstep (se 3 (by rfl) ⟨306311, by rfl⟩ : syracuseStep 1633661 = 612623) B612623
theorem B486831 : Blo 483789 486831 := bstep (se 1 (by rfl) ⟨365123, by rfl⟩ : syracuseStep 486831 = 730247) B730247
theorem B486855 : Blo 483789 486855 := bstep (se 1 (by rfl) ⟨365141, by rfl⟩ : syracuseStep 486855 = 730283) B730283
theorem B486875 : Blo 483789 486875 := bstep (se 1 (by rfl) ⟨365156, by rfl⟩ : syracuseStep 486875 = 730313) B730313
theorem B486951 : Blo 483789 486951 := bstep (se 1 (by rfl) ⟨365213, by rfl⟩ : syracuseStep 486951 = 730427) B730427
theorem B3501629 : Blo 483789 3501629 := bstep (se 3 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 3501629 = 1313111) B1313111
theorem B7958083 : Blo 483789 7958083 := bstep (se 1 (by rfl) ⟨5968562, by rfl⟩ : syracuseStep 7958083 = 11937125) B11937125
theorem B486991 : Blo 483789 486991 := bstep (se 1 (by rfl) ⟨365243, by rfl⟩ : syracuseStep 486991 = 730487) B730487
theorem B487007 : Blo 483789 487007 := bstep (se 1 (by rfl) ⟨365255, by rfl⟩ : syracuseStep 487007 = 730511) B730511
theorem B487035 : Blo 483789 487035 := bstep (se 1 (by rfl) ⟨365276, by rfl⟩ : syracuseStep 487035 = 730553) B730553
theorem B1633931 : Blo 483789 1633931 := bstep (se 1 (by rfl) ⟨1225448, by rfl⟩ : syracuseStep 1633931 = 2450897) B2450897
theorem B487087 : Blo 483789 487087 := bstep (se 1 (by rfl) ⟨365315, by rfl⟩ : syracuseStep 487087 = 730631) B730631
theorem B1961671 : Blo 483789 1961671 := bstep (se 1 (by rfl) ⟨1471253, by rfl⟩ : syracuseStep 1961671 = 2942507) B2942507
theorem B487111 : Blo 483789 487111 := bstep (se 1 (by rfl) ⟨365333, by rfl⟩ : syracuseStep 487111 = 730667) B730667
theorem B487131 : Blo 483789 487131 := bstep (se 1 (by rfl) ⟨365348, by rfl⟩ : syracuseStep 487131 = 730697) B730697
theorem B487207 : Blo 483789 487207 := bstep (se 1 (by rfl) ⟨365405, by rfl⟩ : syracuseStep 487207 = 730811) B730811
theorem B3501883 : Blo 483789 3501883 := bstep (se 1 (by rfl) ⟨2626412, by rfl⟩ : syracuseStep 3501883 = 5252825) B5252825
theorem B487247 : Blo 483789 487247 := bstep (se 1 (by rfl) ⟨365435, by rfl⟩ : syracuseStep 487247 = 730871) B730871
theorem B487263 : Blo 483789 487263 := bstep (se 1 (by rfl) ⟨365447, by rfl⟩ : syracuseStep 487263 = 730895) B730895
theorem B487291 : Blo 483789 487291 := bstep (se 1 (by rfl) ⟨365468, by rfl⟩ : syracuseStep 487291 = 730937) B730937
theorem B3927943 : Blo 483789 3927943 := bstep (se 1 (by rfl) ⟨2945957, by rfl⟩ : syracuseStep 3927943 = 5891915) B5891915
theorem B487343 : Blo 483789 487343 := bstep (se 1 (by rfl) ⟨365507, by rfl⟩ : syracuseStep 487343 = 731015) B731015
theorem B487367 : Blo 483789 487367 := bstep (se 1 (by rfl) ⟨365525, by rfl⟩ : syracuseStep 487367 = 731051) B731051
theorem B487387 : Blo 483789 487387 := bstep (se 1 (by rfl) ⟨365540, by rfl⟩ : syracuseStep 487387 = 731081) B731081
theorem B487463 : Blo 483789 487463 := bstep (se 1 (by rfl) ⟨365597, by rfl⟩ : syracuseStep 487463 = 731195) B731195
theorem B487503 : Blo 483789 487503 := bstep (se 1 (by rfl) ⟨365627, by rfl⟩ : syracuseStep 487503 = 731255) B731255
theorem B487519 : Blo 483789 487519 := bstep (se 1 (by rfl) ⟨365639, by rfl⟩ : syracuseStep 487519 = 731279) B731279
theorem B487547 : Blo 483789 487547 := bstep (se 1 (by rfl) ⟨365660, by rfl⟩ : syracuseStep 487547 = 731321) B731321
theorem B487599 : Blo 483789 487599 := bstep (se 1 (by rfl) ⟨365699, by rfl⟩ : syracuseStep 487599 = 731399) B731399
theorem B487623 : Blo 483789 487623 := bstep (se 1 (by rfl) ⟨365717, by rfl⟩ : syracuseStep 487623 = 731435) B731435
theorem B487643 : Blo 483789 487643 := bstep (se 1 (by rfl) ⟨365732, by rfl⟩ : syracuseStep 487643 = 731465) B731465
theorem B3698945 : Blo 483789 3698945 := bstep (se 2 (by rfl) ⟨1387104, by rfl⟩ : syracuseStep 3698945 = 2774209) B2774209
theorem B487719 : Blo 483789 487719 := bstep (se 1 (by rfl) ⟨365789, by rfl⟩ : syracuseStep 487719 = 731579) B731579
theorem B487759 : Blo 483789 487759 := bstep (se 1 (by rfl) ⟨365819, by rfl⟩ : syracuseStep 487759 = 731639) B731639
theorem B487775 : Blo 483789 487775 := bstep (se 1 (by rfl) ⟨365831, by rfl⟩ : syracuseStep 487775 = 731663) B731663
theorem B13332995 : Blo 483789 13332995 := bstep (se 1 (by rfl) ⟨9999746, by rfl⟩ : syracuseStep 13332995 = 19999493) B19999493
theorem B1864225 : Blo 483789 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B1634849 : Blo 483789 1634849 := bstep (se 2 (by rfl) ⟨613068, by rfl⟩ : syracuseStep 1634849 = 1226137) B1226137
theorem B5239505 : Blo 483789 5239505 := bstep (se 2 (by rfl) ⟨1964814, by rfl⟩ : syracuseStep 5239505 = 3929629) B3929629
theorem B1635065 : Blo 483789 1635065 := bstep (se 2 (by rfl) ⟨613149, by rfl⟩ : syracuseStep 1635065 = 1226299) B1226299
theorem B7893773 : Blo 483789 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B11662231 : Blo 483789 11662231 := bstep (se 1 (by rfl) ⟨8746673, by rfl⟩ : syracuseStep 11662231 = 17493347) B17493347
theorem B12645341 : Blo 483789 12645341 := bstep (se 3 (by rfl) ⟨2371001, by rfl⟩ : syracuseStep 12645341 = 4742003) B4742003
theorem B1635335 : Blo 483789 1635335 := bstep (se 1 (by rfl) ⟨1226501, by rfl⟩ : syracuseStep 1635335 = 2453003) B2453003
theorem B1635443 : Blo 483789 1635443 := bstep (se 1 (by rfl) ⟨1226582, by rfl⟩ : syracuseStep 1635443 = 2453165) B2453165
theorem B1635713 : Blo 483789 1635713 := bstep (se 2 (by rfl) ⟨613392, by rfl⟩ : syracuseStep 1635713 = 1226785) B1226785
theorem B816527 : Blo 483789 816527 := bstep (se 1 (by rfl) ⟨612395, by rfl⟩ : syracuseStep 816527 = 1224791) B1224791
theorem B6977009 : Blo 483789 6977009 := bstep (se 2 (by rfl) ⟨2616378, by rfl⟩ : syracuseStep 6977009 = 5232757) B5232757
theorem B816763 : Blo 483789 816763 := bstep (se 1 (by rfl) ⟨612572, by rfl⟩ : syracuseStep 816763 = 1225145) B1225145
theorem B2094781 : Blo 483789 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B3110993 : Blo 483789 3110993 := bstep (se 2 (by rfl) ⟨1166622, by rfl⟩ : syracuseStep 3110993 = 2333245) B2333245
theorem B1636523 : Blo 483789 1636523 := bstep (se 1 (by rfl) ⟨1227392, by rfl⟩ : syracuseStep 1636523 = 2454785) B2454785
theorem B817627 : Blo 483789 817627 := bstep (se 1 (by rfl) ⟨613220, by rfl⟩ : syracuseStep 817627 = 1226441) B1226441
theorem B3930605 : Blo 483789 3930605 := bstep (se 3 (by rfl) ⟨736988, by rfl⟩ : syracuseStep 3930605 = 1473977) B1473977
theorem B57834163 : Blo 483789 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B1637063 : Blo 483789 1637063 := bstep (se 1 (by rfl) ⟨1227797, by rfl⟩ : syracuseStep 1637063 = 2455595) B2455595
theorem B6749021 : Blo 483789 6749021 := bstep (se 3 (by rfl) ⟨1265441, by rfl⟩ : syracuseStep 6749021 = 2530883) B2530883
theorem B818255 : Blo 483789 818255 := bstep (se 1 (by rfl) ⟨613691, by rfl⟩ : syracuseStep 818255 = 1227383) B1227383
theorem B2456729 : Blo 483789 2456729 := bstep (se 2 (by rfl) ⟨921273, by rfl⟩ : syracuseStep 2456729 = 1842547) B1842547
theorem B5242103 : Blo 483789 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B1637927 : Blo 483789 1637927 := bstep (se 1 (by rfl) ⟨1228445, by rfl⟩ : syracuseStep 1637927 = 2456891) B2456891
theorem B1638035 : Blo 483789 1638035 := bstep (se 1 (by rfl) ⟨1228526, by rfl⟩ : syracuseStep 1638035 = 2457053) B2457053
theorem B1048427 : Blo 483789 1048427 := bstep (se 1 (by rfl) ⟨786320, by rfl⟩ : syracuseStep 1048427 = 1572641) B1572641
theorem B1638251 : Blo 483789 1638251 := bstep (se 1 (by rfl) ⟨1228688, by rfl⟩ : syracuseStep 1638251 = 2457377) B2457377
theorem B1638305 : Blo 483789 1638305 := bstep (se 2 (by rfl) ⟨614364, by rfl⟩ : syracuseStep 1638305 = 1228729) B1228729
theorem B819119 : Blo 483789 819119 := bstep (se 1 (by rfl) ⟨614339, by rfl⟩ : syracuseStep 819119 = 1228679) B1228679
theorem B3702833 : Blo 483789 3702833 := bstep (se 2 (by rfl) ⟨1388562, by rfl⟩ : syracuseStep 3702833 = 2777125) B2777125
theorem B1966763 : Blo 483789 1966763 := bstep (se 1 (by rfl) ⟨1475072, by rfl⟩ : syracuseStep 1966763 = 2950145) B2950145
theorem B819895 : Blo 483789 819895 := bstep (se 1 (by rfl) ⟨614921, by rfl⟩ : syracuseStep 819895 = 1229843) B1229843
theorem B820199 : Blo 483789 820199 := bstep (se 1 (by rfl) ⟨615149, by rfl⟩ : syracuseStep 820199 = 1230299) B1230299
theorem B1049951 : Blo 483789 1049951 := bstep (se 1 (by rfl) ⟨787463, by rfl⟩ : syracuseStep 1049951 = 1574927) B1574927
theorem B5932601 : Blo 483789 5932601 := bstep (se 2 (by rfl) ⟨2224725, by rfl⟩ : syracuseStep 5932601 = 4449451) B4449451
theorem B919201 : Blo 483789 919201 := bstep (se 2 (by rfl) ⟨344700, by rfl⟩ : syracuseStep 919201 = 689401) B689401
theorem B2459321 : Blo 483789 2459321 := bstep (se 2 (by rfl) ⟨922245, by rfl⟩ : syracuseStep 2459321 = 1844491) B1844491
theorem B1378255 : Blo 483789 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B821353 : Blo 483789 821353 := bstep (se 2 (by rfl) ⟨308007, by rfl⟩ : syracuseStep 821353 = 616015) B616015
theorem B2984359 : Blo 483789 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B920135 : Blo 483789 920135 := bstep (se 1 (by rfl) ⟨690101, by rfl⟩ : syracuseStep 920135 = 1380203) B1380203
theorem B985783 : Blo 483789 985783 := bstep (se 1 (by rfl) ⟨739337, by rfl⟩ : syracuseStep 985783 = 1478675) B1478675
theorem B8228087 : Blo 483789 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B2329975 : Blo 483789 2329975 := bstep (se 1 (by rfl) ⟨1747481, by rfl⟩ : syracuseStep 2329975 = 3494963) B3494963
theorem B5311873 : Blo 483789 5311873 := bstep (se 2 (by rfl) ⟨1991952, by rfl⟩ : syracuseStep 5311873 = 3983905) B3983905
theorem B1641977 : Blo 483789 1641977 := bstep (se 2 (by rfl) ⟨615741, by rfl⟩ : syracuseStep 1641977 = 1231483) B1231483
theorem B2461265 : Blo 483789 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B2625119 : Blo 483789 2625119 := bstep (se 1 (by rfl) ⟨1968839, by rfl⟩ : syracuseStep 2625119 = 3937679) B3937679
theorem B1642247 : Blo 483789 1642247 := bstep (se 1 (by rfl) ⟨1231685, by rfl⟩ : syracuseStep 1642247 = 2463371) B2463371
theorem B823081 : Blo 483789 823081 := bstep (se 2 (by rfl) ⟨308655, by rfl⟩ : syracuseStep 823081 = 617311) B617311
theorem B1642301 : Blo 483789 1642301 := bstep (se 3 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 1642301 = 615863) B615863
theorem B2756713 : Blo 483789 2756713 := bstep (se 2 (by rfl) ⟨1033767, by rfl⟩ : syracuseStep 2756713 = 2067535) B2067535
theorem B2494667 : Blo 483789 2494667 := bstep (se 1 (by rfl) ⟨1871000, by rfl⟩ : syracuseStep 2494667 = 3742001) B3742001
theorem B1511905 : Blo 483789 1511905 := bstep (se 2 (by rfl) ⟨566964, by rfl⟩ : syracuseStep 1511905 = 1133929) B1133929
theorem B1839617 : Blo 483789 1839617 := bstep (se 2 (by rfl) ⟨689856, by rfl⟩ : syracuseStep 1839617 = 1379713) B1379713
theorem B725687 : Blo 483789 725687 := bstep (se 1 (by rfl) ⟨544265, by rfl⟩ : syracuseStep 725687 = 1088531) B1088531
theorem B725915 : Blo 483789 725915 := bstep (se 1 (by rfl) ⟨544436, by rfl⟩ : syracuseStep 725915 = 1088873) B1088873
theorem B2626505 : Blo 483789 2626505 := bstep (se 2 (by rfl) ⟨984939, by rfl⟩ : syracuseStep 2626505 = 1969879) B1969879
theorem B1840103 : Blo 483789 1840103 := bstep (se 1 (by rfl) ⟨1380077, by rfl⟩ : syracuseStep 1840103 = 2760155) B2760155
theorem B726311 : Blo 483789 726311 := bstep (se 1 (by rfl) ⟨544733, by rfl⟩ : syracuseStep 726311 = 1089467) B1089467
theorem B726395 : Blo 483789 726395 := bstep (se 1 (by rfl) ⟨544796, by rfl⟩ : syracuseStep 726395 = 1089593) B1089593
theorem B1054075 : Blo 483789 1054075 := bstep (se 1 (by rfl) ⟨790556, by rfl⟩ : syracuseStep 1054075 = 1581113) B1581113
theorem B726521 : Blo 483789 726521 := bstep (se 2 (by rfl) ⟨272445, by rfl⟩ : syracuseStep 726521 = 544891) B544891
theorem B726623 : Blo 483789 726623 := bstep (se 1 (by rfl) ⟨544967, by rfl⟩ : syracuseStep 726623 = 1089935) B1089935
theorem B726839 : Blo 483789 726839 := bstep (se 1 (by rfl) ⟨545129, by rfl⟩ : syracuseStep 726839 = 1090259) B1090259
theorem B2660303 : Blo 483789 2660303 := bstep (se 1 (by rfl) ⟨1995227, by rfl⟩ : syracuseStep 2660303 = 3990455) B3990455
theorem B2463695 : Blo 483789 2463695 := bstep (se 1 (by rfl) ⟨1847771, by rfl⟩ : syracuseStep 2463695 = 3695543) B3695543
theorem B727145 : Blo 483789 727145 := bstep (se 2 (by rfl) ⟨272679, by rfl⟩ : syracuseStep 727145 = 545359) B545359
theorem B2332937 : Blo 483789 2332937 := bstep (se 2 (by rfl) ⟨874851, by rfl⟩ : syracuseStep 2332937 = 1749703) B1749703
theorem B727463 : Blo 483789 727463 := bstep (se 1 (by rfl) ⟨545597, by rfl⟩ : syracuseStep 727463 = 1091195) B1091195
theorem B1841575 : Blo 483789 1841575 := bstep (se 1 (by rfl) ⟨1381181, by rfl⟩ : syracuseStep 1841575 = 2762363) B2762363
theorem B727547 : Blo 483789 727547 := bstep (se 1 (by rfl) ⟨545660, by rfl⟩ : syracuseStep 727547 = 1091321) B1091321
theorem B1645163 : Blo 483789 1645163 := bstep (se 1 (by rfl) ⟨1233872, by rfl⟩ : syracuseStep 1645163 = 2467745) B2467745
theorem B727673 : Blo 483789 727673 := bstep (se 2 (by rfl) ⟨272877, by rfl⟩ : syracuseStep 727673 = 545755) B545755
theorem B924281 : Blo 483789 924281 := bstep (se 2 (by rfl) ⟨346605, by rfl⟩ : syracuseStep 924281 = 693211) B693211
theorem B727727 : Blo 483789 727727 := bstep (se 1 (by rfl) ⟨545795, by rfl⟩ : syracuseStep 727727 = 1091591) B1091591
theorem B5249711 : Blo 483789 5249711 := bstep (se 1 (by rfl) ⟨3937283, by rfl⟩ : syracuseStep 5249711 = 7874567) B7874567
theorem B727775 : Blo 483789 727775 := bstep (se 1 (by rfl) ⟨545831, by rfl⟩ : syracuseStep 727775 = 1091663) B1091663
theorem B2464667 : Blo 483789 2464667 := bstep (se 1 (by rfl) ⟨1848500, by rfl⟩ : syracuseStep 2464667 = 3697001) B3697001
theorem B728039 : Blo 483789 728039 := bstep (se 1 (by rfl) ⟨546029, by rfl⟩ : syracuseStep 728039 = 1092059) B1092059
theorem B1842365 : Blo 483789 1842365 := bstep (se 3 (by rfl) ⟨345443, by rfl⟩ : syracuseStep 1842365 = 690887) B690887
theorem B1645757 : Blo 483789 1645757 := bstep (se 3 (by rfl) ⟨308579, by rfl⟩ : syracuseStep 1645757 = 617159) B617159
theorem B1088711 : Blo 483789 1088711 := bstep (se 1 (by rfl) ⟨816533, by rfl⟩ : syracuseStep 1088711 = 1633067) B1633067
theorem B728297 : Blo 483789 728297 := bstep (se 2 (by rfl) ⟨273111, by rfl⟩ : syracuseStep 728297 = 546223) B546223
theorem B728351 : Blo 483789 728351 := bstep (se 1 (by rfl) ⟨546263, by rfl⟩ : syracuseStep 728351 = 1092527) B1092527
theorem B1088891 : Blo 483789 1088891 := bstep (se 1 (by rfl) ⟨816668, by rfl⟩ : syracuseStep 1088891 = 1633337) B1633337
theorem B2465153 : Blo 483789 2465153 := bstep (se 2 (by rfl) ⟨924432, by rfl⟩ : syracuseStep 2465153 = 1848865) B1848865
theorem B728519 : Blo 483789 728519 := bstep (se 1 (by rfl) ⟨546389, by rfl⟩ : syracuseStep 728519 = 1092779) B1092779
theorem B2334167 : Blo 483789 2334167 := bstep (se 1 (by rfl) ⟨1750625, by rfl⟩ : syracuseStep 2334167 = 3501251) B3501251
theorem B1089017 : Blo 483789 1089017 := bstep (se 2 (by rfl) ⟨408381, by rfl⟩ : syracuseStep 1089017 = 816763) B816763
theorem B925177 : Blo 483789 925177 := bstep (se 2 (by rfl) ⟨346941, by rfl⟩ : syracuseStep 925177 = 693883) B693883
theorem B4136507 : Blo 483789 4136507 := bstep (se 1 (by rfl) ⟨3102380, by rfl⟩ : syracuseStep 4136507 = 6204761) B6204761
theorem B17997389 : Blo 483789 17997389 := bstep (se 3 (by rfl) ⟨3374510, by rfl⟩ : syracuseStep 17997389 = 6749021) B6749021
theorem B2793041 : Blo 483789 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B1089107 : Blo 483789 1089107 := bstep (se 1 (by rfl) ⟨816830, by rfl⟩ : syracuseStep 1089107 = 1633661) B1633661
theorem B2334419 : Blo 483789 2334419 := bstep (se 1 (by rfl) ⟨1750814, by rfl⟩ : syracuseStep 2334419 = 3501629) B3501629
theorem B1089287 : Blo 483789 1089287 := bstep (se 1 (by rfl) ⟨816965, by rfl⟩ : syracuseStep 1089287 = 1633931) B1633931
theorem B728873 : Blo 483789 728873 := bstep (se 2 (by rfl) ⟨273327, by rfl⟩ : syracuseStep 728873 = 546655) B546655
theorem B925481 : Blo 483789 925481 := bstep (se 2 (by rfl) ⟨347055, by rfl⟩ : syracuseStep 925481 = 694111) B694111
theorem B728879 : Blo 483789 728879 := bstep (se 1 (by rfl) ⟨546659, by rfl⟩ : syracuseStep 728879 = 1093319) B1093319
theorem B2465801 : Blo 483789 2465801 := bstep (se 2 (by rfl) ⟨924675, by rfl⟩ : syracuseStep 2465801 = 1849351) B1849351
theorem B9969713 : Blo 483789 9969713 := bstep (se 2 (by rfl) ⟨3738642, by rfl⟩ : syracuseStep 9969713 = 7477285) B7477285
theorem B1384553 : Blo 483789 1384553 := bstep (se 2 (by rfl) ⟨519207, by rfl⟩ : syracuseStep 1384553 = 1038415) B1038415
theorem B2072729 : Blo 483789 2072729 := bstep (se 2 (by rfl) ⟨777273, by rfl⟩ : syracuseStep 2072729 = 1554547) B1554547
theorem B2465963 : Blo 483789 2465963 := bstep (se 1 (by rfl) ⟨1849472, by rfl⟩ : syracuseStep 2465963 = 3698945) B3698945
theorem B729353 : Blo 483789 729353 := bstep (se 2 (by rfl) ⟨273507, by rfl⟩ : syracuseStep 729353 = 547015) B547015
theorem B8888663 : Blo 483789 8888663 := bstep (se 1 (by rfl) ⟨6666497, by rfl⟩ : syracuseStep 8888663 = 13332995) B13332995
theorem B1089899 : Blo 483789 1089899 := bstep (se 1 (by rfl) ⟨817424, by rfl⟩ : syracuseStep 1089899 = 1634849) B1634849
theorem B729455 : Blo 483789 729455 := bstep (se 1 (by rfl) ⟨547091, by rfl⟩ : syracuseStep 729455 = 1094183) B1094183
theorem B1090043 : Blo 483789 1090043 := bstep (se 1 (by rfl) ⟨817532, by rfl⟩ : syracuseStep 1090043 = 1635065) B1635065
theorem B2368001 : Blo 483789 2368001 := bstep (se 2 (by rfl) ⟨888000, by rfl⟩ : syracuseStep 2368001 = 1776001) B1776001
theorem B729671 : Blo 483789 729671 := bstep (se 1 (by rfl) ⟨547253, by rfl⟩ : syracuseStep 729671 = 1094507) B1094507
theorem B729707 : Blo 483789 729707 := bstep (se 1 (by rfl) ⟨547280, by rfl⟩ : syracuseStep 729707 = 1094561) B1094561
theorem B1090169 : Blo 483789 1090169 := bstep (se 2 (by rfl) ⟨408813, by rfl⟩ : syracuseStep 1090169 = 817627) B817627
theorem B2761361 : Blo 483789 2761361 := bstep (se 2 (by rfl) ⟨1035510, by rfl⟩ : syracuseStep 2761361 = 2071021) B2071021
theorem B2466449 : Blo 483789 2466449 := bstep (se 2 (by rfl) ⟨924918, by rfl⟩ : syracuseStep 2466449 = 1849837) B1849837
theorem B8430227 : Blo 483789 8430227 := bstep (se 1 (by rfl) ⟨6322670, by rfl⟩ : syracuseStep 8430227 = 12645341) B12645341
theorem B1090223 : Blo 483789 1090223 := bstep (se 1 (by rfl) ⟨817667, by rfl⟩ : syracuseStep 1090223 = 1635335) B1635335
theorem B1090295 : Blo 483789 1090295 := bstep (se 1 (by rfl) ⟨817721, by rfl⟩ : syracuseStep 1090295 = 1635443) B1635443
theorem B729935 : Blo 483789 729935 := bstep (se 1 (by rfl) ⟨547451, by rfl⟩ : syracuseStep 729935 = 1094903) B1094903
theorem B77112217 : Blo 483789 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B1090475 : Blo 483789 1090475 := bstep (se 1 (by rfl) ⟨817856, by rfl⟩ : syracuseStep 1090475 = 1635713) B1635713
theorem B730331 : Blo 483789 730331 := bstep (se 1 (by rfl) ⟨547748, by rfl⟩ : syracuseStep 730331 = 1095497) B1095497
theorem B730505 : Blo 483789 730505 := bstep (se 2 (by rfl) ⟨273939, by rfl⟩ : syracuseStep 730505 = 547879) B547879
theorem B2073995 : Blo 483789 2073995 := bstep (se 1 (by rfl) ⟨1555496, by rfl⟩ : syracuseStep 2073995 = 3110993) B3110993
theorem B1091015 : Blo 483789 1091015 := bstep (se 1 (by rfl) ⟨818261, by rfl⟩ : syracuseStep 1091015 = 1636523) B1636523
theorem B10233479 : Blo 483789 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B2107037 : Blo 483789 2107037 := bstep (se 3 (by rfl) ⟨395069, by rfl⟩ : syracuseStep 2107037 = 790139) B790139
theorem B730859 : Blo 483789 730859 := bstep (se 1 (by rfl) ⟨548144, by rfl⟩ : syracuseStep 730859 = 1096289) B1096289
theorem B1091375 : Blo 483789 1091375 := bstep (se 1 (by rfl) ⟨818531, by rfl⟩ : syracuseStep 1091375 = 1637063) B1637063
theorem B4138897 : Blo 483789 4138897 := bstep (se 2 (by rfl) ⟨1552086, by rfl⟩ : syracuseStep 4138897 = 3104173) B3104173
theorem B731087 : Blo 483789 731087 := bstep (se 1 (by rfl) ⟨548315, by rfl⟩ : syracuseStep 731087 = 1096631) B1096631
theorem B1845281 : Blo 483789 1845281 := bstep (se 2 (by rfl) ⟨691980, by rfl⟩ : syracuseStep 1845281 = 1383961) B1383961
theorem B2337049 : Blo 483789 2337049 := bstep (se 2 (by rfl) ⟨876393, by rfl⟩ : syracuseStep 2337049 = 1752787) B1752787
theorem B20982077 : Blo 483789 20982077 := bstep (se 3 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 20982077 = 7868279) B7868279
theorem B731483 : Blo 483789 731483 := bstep (se 1 (by rfl) ⟨548612, by rfl⟩ : syracuseStep 731483 = 1097225) B1097225
theorem B1091951 : Blo 483789 1091951 := bstep (se 1 (by rfl) ⟨818963, by rfl⟩ : syracuseStep 1091951 = 1637927) B1637927
theorem B3123629 : Blo 483789 3123629 := bstep (se 3 (by rfl) ⟨585680, by rfl⟩ : syracuseStep 3123629 = 1171361) B1171361
theorem B1092023 : Blo 483789 1092023 := bstep (se 1 (by rfl) ⟨819017, by rfl⟩ : syracuseStep 1092023 = 1638035) B1638035
theorem B1387003 : Blo 483789 1387003 := bstep (se 1 (by rfl) ⟨1040252, by rfl⟩ : syracuseStep 1387003 = 2080505) B2080505
theorem B698951 : Blo 483789 698951 := bstep (se 1 (by rfl) ⟨524213, by rfl⟩ : syracuseStep 698951 = 1048427) B1048427
theorem B1092167 : Blo 483789 1092167 := bstep (se 1 (by rfl) ⟨819125, by rfl⟩ : syracuseStep 1092167 = 1638251) B1638251
theorem B1092203 : Blo 483789 1092203 := bstep (se 1 (by rfl) ⟨819152, by rfl⟩ : syracuseStep 1092203 = 1638305) B1638305
theorem B1845935 : Blo 483789 1845935 := bstep (se 1 (by rfl) ⟨1384451, by rfl⟩ : syracuseStep 1845935 = 2768903) B2768903
theorem B1092599 : Blo 483789 1092599 := bstep (se 1 (by rfl) ⟨819449, by rfl⟩ : syracuseStep 1092599 = 1638899) B1638899
theorem B2468879 : Blo 483789 2468879 := bstep (se 1 (by rfl) ⟨1851659, by rfl⟩ : syracuseStep 2468879 = 3703319) B3703319
theorem B2338109 : Blo 483789 2338109 := bstep (se 3 (by rfl) ⟨438395, by rfl⟩ : syracuseStep 2338109 = 876791) B876791
theorem B1092959 : Blo 483789 1092959 := bstep (se 1 (by rfl) ⟨819719, by rfl⟩ : syracuseStep 1092959 = 1639439) B1639439
theorem B1093355 : Blo 483789 1093355 := bstep (se 1 (by rfl) ⟨820016, by rfl⟩ : syracuseStep 1093355 = 1640033) B1640033
theorem B2502407 : Blo 483789 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B2338571 : Blo 483789 2338571 := bstep (se 1 (by rfl) ⟨1753928, by rfl⟩ : syracuseStep 2338571 = 3507857) B3507857
theorem B1388335 : Blo 483789 1388335 := bstep (se 1 (by rfl) ⟨1041251, by rfl⟩ : syracuseStep 1388335 = 2082503) B2082503
theorem B1093481 : Blo 483789 1093481 := bstep (se 2 (by rfl) ⟨410055, by rfl⟩ : syracuseStep 1093481 = 820111) B820111
theorem B3321757 : Blo 483789 3321757 := bstep (se 3 (by rfl) ⟨622829, by rfl⟩ : syracuseStep 3321757 = 1245659) B1245659
theorem B9318671 : Blo 483789 9318671 := bstep (se 1 (by rfl) ⟨6989003, by rfl⟩ : syracuseStep 9318671 = 13978007) B13978007
theorem B2077103 : Blo 483789 2077103 := bstep (se 1 (by rfl) ⟨1557827, by rfl⟩ : syracuseStep 2077103 = 3115655) B3115655
theorem B13972013 : Blo 483789 13972013 := bstep (se 3 (by rfl) ⟨2619752, by rfl⟩ : syracuseStep 13972013 = 5239505) B5239505
theorem B1847879 : Blo 483789 1847879 := bstep (se 1 (by rfl) ⟨1385909, by rfl⟩ : syracuseStep 1847879 = 2771819) B2771819
theorem B1094327 : Blo 483789 1094327 := bstep (se 1 (by rfl) ⟨820745, by rfl⟩ : syracuseStep 1094327 = 1641491) B1641491
theorem B1225439 : Blo 483789 1225439 := bstep (se 1 (by rfl) ⟨919079, by rfl⟩ : syracuseStep 1225439 = 1838159) B1838159
theorem B5256029 : Blo 483789 5256029 := bstep (se 3 (by rfl) ⟨985505, by rfl⟩ : syracuseStep 5256029 = 1971011) B1971011
theorem B1094543 : Blo 483789 1094543 := bstep (se 1 (by rfl) ⟨820907, by rfl⟩ : syracuseStep 1094543 = 1641815) B1641815
theorem B2339777 : Blo 483789 2339777 := bstep (se 2 (by rfl) ⟨877416, by rfl⟩ : syracuseStep 2339777 = 1754833) B1754833
theorem B1553651 : Blo 483789 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B2962793 : Blo 483789 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B1095263 : Blo 483789 1095263 := bstep (se 1 (by rfl) ⟨821447, by rfl⟩ : syracuseStep 1095263 = 1642895) B1642895
theorem B3192605 : Blo 483789 3192605 := bstep (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) B1197227
theorem B1095479 : Blo 483789 1095479 := bstep (se 1 (by rfl) ⟨821609, by rfl⟩ : syracuseStep 1095479 = 1643219) B1643219
theorem B1849169 : Blo 483789 1849169 := bstep (se 2 (by rfl) ⟨693438, by rfl⟩ : syracuseStep 1849169 = 1386877) B1386877
theorem B1095785 : Blo 483789 1095785 := bstep (se 2 (by rfl) ⟨410919, by rfl⟩ : syracuseStep 1095785 = 821839) B821839
theorem B1849625 : Blo 483789 1849625 := bstep (se 2 (by rfl) ⟨693609, by rfl⟩ : syracuseStep 1849625 = 1387219) B1387219
theorem B1751507 : Blo 483789 1751507 := bstep (se 1 (by rfl) ⟨1313630, by rfl⟩ : syracuseStep 1751507 = 2627261) B2627261
theorem B1096271 : Blo 483789 1096271 := bstep (se 1 (by rfl) ⟨822203, by rfl⟩ : syracuseStep 1096271 = 1644407) B1644407
theorem B2079427 : Blo 483789 2079427 := bstep (se 1 (by rfl) ⟨1559570, by rfl⟩ : syracuseStep 2079427 = 3119141) B3119141
theorem B1096415 : Blo 483789 1096415 := bstep (se 1 (by rfl) ⟨822311, by rfl⟩ : syracuseStep 1096415 = 1644623) B1644623
theorem B1096667 : Blo 483789 1096667 := bstep (se 1 (by rfl) ⟨822500, by rfl⟩ : syracuseStep 1096667 = 1645001) B1645001
theorem B1227899 : Blo 483789 1227899 := bstep (se 1 (by rfl) ⟨920924, by rfl⟩ : syracuseStep 1227899 = 1841849) B1841849
theorem B1227919 : Blo 483789 1227919 := bstep (se 1 (by rfl) ⟨920939, by rfl⟩ : syracuseStep 1227919 = 1841879) B1841879
theorem B1096847 : Blo 483789 1096847 := bstep (se 1 (by rfl) ⟨822635, by rfl⟩ : syracuseStep 1096847 = 1645271) B1645271
theorem B1096937 : Blo 483789 1096937 := bstep (se 2 (by rfl) ⟨411351, by rfl⟩ : syracuseStep 1096937 = 822703) B822703
theorem B6208757 : Blo 483789 6208757 := bstep (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) B582071
theorem B1686815 : Blo 483789 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B1096991 : Blo 483789 1096991 := bstep (se 1 (by rfl) ⟨822743, by rfl⟩ : syracuseStep 1096991 = 1645487) B1645487
theorem B2768195 : Blo 483789 2768195 := bstep (se 1 (by rfl) ⟨2076146, by rfl⟩ : syracuseStep 2768195 = 4152293) B4152293
theorem B1228193 : Blo 483789 1228193 := bstep (se 2 (by rfl) ⟨460572, by rfl⟩ : syracuseStep 1228193 = 921145) B921145
theorem B2768377 : Blo 483789 2768377 := bstep (se 2 (by rfl) ⟨1038141, by rfl⟩ : syracuseStep 2768377 = 2076283) B2076283
theorem B4669177 : Blo 483789 4669177 := bstep (se 2 (by rfl) ⟨1750941, by rfl⟩ : syracuseStep 4669177 = 3501883) B3501883
theorem B1097513 : Blo 483789 1097513 := bstep (se 2 (by rfl) ⟨411567, by rfl⟩ : syracuseStep 1097513 = 823135) B823135
theorem B1752961 : Blo 483789 1752961 := bstep (se 2 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 1752961 = 1314721) B1314721
theorem B5521445 : Blo 483789 5521445 := bstep (se 4 (by rfl) ⟨517635, by rfl⟩ : syracuseStep 5521445 = 1035271) B1035271
theorem B13681325 : Blo 483789 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B441762497 : Blo 483789 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B5129153 : Blo 483789 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B8864731 : Blo 483789 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B1229863 : Blo 483789 1229863 := bstep (se 1 (by rfl) ⟨922397, by rfl⟩ : syracuseStep 1229863 = 1844795) B1844795
theorem B15549641 : Blo 483789 15549641 := bstep (se 2 (by rfl) ⟨5831115, by rfl⟩ : syracuseStep 15549641 = 11662231) B11662231
theorem B3687767 : Blo 483789 3687767 := bstep (se 1 (by rfl) ⟨2765825, by rfl⟩ : syracuseStep 3687767 = 5531651) B5531651
theorem B1230329 : Blo 483789 1230329 := bstep (se 2 (by rfl) ⟨461373, by rfl⟩ : syracuseStep 1230329 = 922747) B922747
theorem B17778365 : Blo 483789 17778365 := bstep (se 3 (by rfl) ⟨3333443, by rfl⟩ : syracuseStep 17778365 = 6666887) B6666887
theorem B1034041 : Blo 483789 1034041 := bstep (se 2 (by rfl) ⟨387765, by rfl⟩ : syracuseStep 1034041 = 775531) B775531
theorem B2770793 : Blo 483789 2770793 := bstep (se 2 (by rfl) ⟨1039047, by rfl⟩ : syracuseStep 2770793 = 2078095) B2078095
theorem B2082743 : Blo 483789 2082743 := bstep (se 1 (by rfl) ⟨1562057, by rfl⟩ : syracuseStep 2082743 = 3124115) B3124115
theorem B1230977 : Blo 483789 1230977 := bstep (se 2 (by rfl) ⟨461616, by rfl⟩ : syracuseStep 1230977 = 923233) B923233
theorem B2214287 : Blo 483789 2214287 := bstep (se 1 (by rfl) ⟨1660715, by rfl⟩ : syracuseStep 2214287 = 3321431) B3321431
theorem B1231271 : Blo 483789 1231271 := bstep (se 1 (by rfl) ⟨923453, by rfl⟩ : syracuseStep 1231271 = 1846907) B1846907
theorem B2083391 : Blo 483789 2083391 := bstep (se 1 (by rfl) ⟨1562543, by rfl⟩ : syracuseStep 2083391 = 3125087) B3125087
theorem B1231433 : Blo 483789 1231433 := bstep (se 2 (by rfl) ⟨461787, by rfl⟩ : syracuseStep 1231433 = 923575) B923575
theorem B8440625 : Blo 483789 8440625 := bstep (se 2 (by rfl) ⟨3165234, by rfl⟩ : syracuseStep 8440625 = 6330469) B6330469
theorem B1231787 : Blo 483789 1231787 := bstep (se 1 (by rfl) ⟨923840, by rfl⟩ : syracuseStep 1231787 = 1847681) B1847681
theorem B1231969 : Blo 483789 1231969 := bstep (se 2 (by rfl) ⟨461988, by rfl⟩ : syracuseStep 1231969 = 923977) B923977
theorem B5262515 : Blo 483789 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B544351 : Blo 483789 544351 := bstep (se 1 (by rfl) ⟨408263, by rfl⟩ : syracuseStep 544351 = 816527) B816527
theorem B21221189 : Blo 483789 21221189 := bstep (se 4 (by rfl) ⟨1989486, by rfl⟩ : syracuseStep 21221189 = 3978973) B3978973
theorem B2805785 : Blo 483789 2805785 := bstep (se 2 (by rfl) ⟨1052169, by rfl⟩ : syracuseStep 2805785 = 2104339) B2104339
theorem B1232921 : Blo 483789 1232921 := bstep (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) B924691
theorem B1233377 : Blo 483789 1233377 := bstep (se 2 (by rfl) ⟨462516, by rfl⟩ : syracuseStep 1233377 = 925033) B925033
theorem B1233427 : Blo 483789 1233427 := bstep (se 1 (by rfl) ⟨925070, by rfl⟩ : syracuseStep 1233427 = 1850141) B1850141
theorem B545503 : Blo 483789 545503 := bstep (se 1 (by rfl) ⟨409127, by rfl⟩ : syracuseStep 545503 = 818255) B818255
theorem B3494735 : Blo 483789 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B546079 : Blo 483789 546079 := bstep (se 1 (by rfl) ⟨409559, by rfl⟩ : syracuseStep 546079 = 819119) B819119
theorem B546367 : Blo 483789 546367 := bstep (se 1 (by rfl) ⟨409775, by rfl⟩ : syracuseStep 546367 = 819551) B819551
theorem B1169083 : Blo 483789 1169083 := bstep (se 1 (by rfl) ⟨876812, by rfl⟩ : syracuseStep 1169083 = 1753625) B1753625
theorem B6248123 : Blo 483789 6248123 := bstep (se 1 (by rfl) ⟨4686092, by rfl⟩ : syracuseStep 6248123 = 9372185) B9372185
theorem B10639163 : Blo 483789 10639163 := bstep (se 1 (by rfl) ⟨7979372, by rfl⟩ : syracuseStep 10639163 = 15958745) B15958745
theorem B547195 : Blo 483789 547195 := bstep (se 1 (by rfl) ⟨410396, by rfl⟩ : syracuseStep 547195 = 820793) B820793
theorem B612775 : Blo 483789 612775 := bstep (se 1 (by rfl) ⟨459581, by rfl⟩ : syracuseStep 612775 = 919163) B919163
theorem B613099 : Blo 483789 613099 := bstep (se 1 (by rfl) ⟨459824, by rfl⟩ : syracuseStep 613099 = 919649) B919649
theorem B547663 : Blo 483789 547663 := bstep (se 1 (by rfl) ⟨410747, by rfl⟩ : syracuseStep 547663 = 821495) B821495
theorem B613327 : Blo 483789 613327 := bstep (se 1 (by rfl) ⟨459995, by rfl⟩ : syracuseStep 613327 = 919991) B919991
theorem B613595 : Blo 483789 613595 := bstep (se 1 (by rfl) ⟨460196, by rfl⟩ : syracuseStep 613595 = 920393) B920393
theorem B548059 : Blo 483789 548059 := bstep (se 1 (by rfl) ⟨411044, by rfl⟩ : syracuseStep 548059 = 822089) B822089
theorem B777595 : Blo 483789 777595 := bstep (se 1 (by rfl) ⟨583196, by rfl⟩ : syracuseStep 777595 = 1166393) B1166393
theorem B548347 : Blo 483789 548347 := bstep (se 1 (by rfl) ⟨411260, by rfl⟩ : syracuseStep 548347 = 822521) B822521
theorem B4152977 : Blo 483789 4152977 := bstep (se 2 (by rfl) ⟨1557366, by rfl⟩ : syracuseStep 4152977 = 3114733) B3114733
theorem B548527 : Blo 483789 548527 := bstep (se 1 (by rfl) ⟨411395, by rfl⟩ : syracuseStep 548527 = 822791) B822791
theorem B614071 : Blo 483789 614071 := bstep (se 1 (by rfl) ⟨460553, by rfl⟩ : syracuseStep 614071 = 921107) B921107
theorem B1171207 : Blo 483789 1171207 := bstep (se 1 (by rfl) ⟨878405, by rfl⟩ : syracuseStep 1171207 = 1756811) B1756811
theorem B5005097 : Blo 483789 5005097 := bstep (se 2 (by rfl) ⟨1876911, by rfl⟩ : syracuseStep 5005097 = 3753823) B3753823
theorem B1171255 : Blo 483789 1171255 := bstep (se 1 (by rfl) ⟨878441, by rfl⟩ : syracuseStep 1171255 = 1756883) B1756883
theorem B614299 : Blo 483789 614299 := bstep (se 1 (by rfl) ⟨460724, by rfl⟩ : syracuseStep 614299 = 921449) B921449
theorem B14049287 : Blo 483789 14049287 := bstep (se 1 (by rfl) ⟨10536965, by rfl⟩ : syracuseStep 14049287 = 21073931) B21073931
theorem B1040807 : Blo 483789 1040807 := bstep (se 1 (by rfl) ⟨780605, by rfl⟩ : syracuseStep 1040807 = 1561211) B1561211
theorem B483835 : Blo 483789 483835 := bstep (se 1 (by rfl) ⟨362876, by rfl⟩ : syracuseStep 483835 = 725753) B725753
theorem B483903 : Blo 483789 483903 := bstep (se 1 (by rfl) ⟨362927, by rfl⟩ : syracuseStep 483903 = 725855) B725855
theorem B483911 : Blo 483789 483911 := bstep (se 1 (by rfl) ⟨362933, by rfl⟩ : syracuseStep 483911 = 725867) B725867
theorem B778825 : Blo 483789 778825 := bstep (se 2 (by rfl) ⟨292059, by rfl⟩ : syracuseStep 778825 = 584119) B584119
theorem B4154003 : Blo 483789 4154003 := bstep (se 1 (by rfl) ⟨3115502, by rfl⟩ : syracuseStep 4154003 = 6231005) B6231005
theorem B2482859 : Blo 483789 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B484063 : Blo 483789 484063 := bstep (se 1 (by rfl) ⟨363047, by rfl⟩ : syracuseStep 484063 = 726095) B726095
theorem B484143 : Blo 483789 484143 := bstep (se 1 (by rfl) ⟨363107, by rfl⟩ : syracuseStep 484143 = 726215) B726215
theorem B615215 : Blo 483789 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B484251 : Blo 483789 484251 := bstep (se 1 (by rfl) ⟨363188, by rfl⟩ : syracuseStep 484251 = 726377) B726377
theorem B877483 : Blo 483789 877483 := bstep (se 1 (by rfl) ⟨658112, by rfl⟩ : syracuseStep 877483 = 1316225) B1316225
theorem B484303 : Blo 483789 484303 := bstep (se 1 (by rfl) ⟨363227, by rfl⟩ : syracuseStep 484303 = 726455) B726455
theorem B484327 : Blo 483789 484327 := bstep (se 1 (by rfl) ⟨363245, by rfl⟩ : syracuseStep 484327 = 726491) B726491
theorem B484639 : Blo 483789 484639 := bstep (se 1 (by rfl) ⟨363479, by rfl⟩ : syracuseStep 484639 = 726959) B726959
theorem B484699 : Blo 483789 484699 := bstep (se 1 (by rfl) ⟨363524, by rfl⟩ : syracuseStep 484699 = 727049) B727049
theorem B484719 : Blo 483789 484719 := bstep (se 1 (by rfl) ⟨363539, by rfl⟩ : syracuseStep 484719 = 727079) B727079
theorem B484775 : Blo 483789 484775 := bstep (se 1 (by rfl) ⟨363581, by rfl⟩ : syracuseStep 484775 = 727163) B727163
theorem B484859 : Blo 483789 484859 := bstep (se 1 (by rfl) ⟨363644, by rfl⟩ : syracuseStep 484859 = 727289) B727289
theorem B3499577 : Blo 483789 3499577 := bstep (se 2 (by rfl) ⟨1312341, by rfl⟩ : syracuseStep 3499577 = 2624683) B2624683
theorem B484927 : Blo 483789 484927 := bstep (se 1 (by rfl) ⟨363695, by rfl⟩ : syracuseStep 484927 = 727391) B727391
theorem B484935 : Blo 483789 484935 := bstep (se 1 (by rfl) ⟨363701, by rfl⟩ : syracuseStep 484935 = 727403) B727403
theorem B485087 : Blo 483789 485087 := bstep (se 1 (by rfl) ⟨363815, by rfl⟩ : syracuseStep 485087 = 727631) B727631
theorem B485167 : Blo 483789 485167 := bstep (se 1 (by rfl) ⟨363875, by rfl⟩ : syracuseStep 485167 = 727751) B727751
theorem B485275 : Blo 483789 485275 := bstep (se 1 (by rfl) ⟨363956, by rfl⟩ : syracuseStep 485275 = 727913) B727913
theorem B2451383 : Blo 483789 2451383 := bstep (se 1 (by rfl) ⟨1838537, by rfl⟩ : syracuseStep 2451383 = 3677075) B3677075
theorem B485327 : Blo 483789 485327 := bstep (se 1 (by rfl) ⟨363995, by rfl⟩ : syracuseStep 485327 = 727991) B727991
theorem B485351 : Blo 483789 485351 := bstep (se 1 (by rfl) ⟨364013, by rfl⟩ : syracuseStep 485351 = 728027) B728027
theorem B10610777 : Blo 483789 10610777 := bstep (se 2 (by rfl) ⟨3979041, by rfl⟩ : syracuseStep 10610777 = 7958083) B7958083
theorem B2615561 : Blo 483789 2615561 := bstep (se 2 (by rfl) ⟨980835, by rfl⟩ : syracuseStep 2615561 = 1961671) B1961671
theorem B485663 : Blo 483789 485663 := bstep (se 1 (by rfl) ⟨364247, by rfl⟩ : syracuseStep 485663 = 728495) B728495
theorem B485723 : Blo 483789 485723 := bstep (se 1 (by rfl) ⟨364292, by rfl⟩ : syracuseStep 485723 = 728585) B728585
theorem B485743 : Blo 483789 485743 := bstep (se 1 (by rfl) ⟨364307, by rfl⟩ : syracuseStep 485743 = 728615) B728615
theorem B518567 : Blo 483789 518567 := bstep (se 1 (by rfl) ⟨388925, by rfl⟩ : syracuseStep 518567 = 777851) B777851
theorem B485799 : Blo 483789 485799 := bstep (se 1 (by rfl) ⟨364349, by rfl⟩ : syracuseStep 485799 = 728699) B728699
theorem B485883 : Blo 483789 485883 := bstep (se 1 (by rfl) ⟨364412, by rfl⟩ : syracuseStep 485883 = 728825) B728825
theorem B5237257 : Blo 483789 5237257 := bstep (se 2 (by rfl) ⟨1963971, by rfl⟩ : syracuseStep 5237257 = 3927943) B3927943
theorem B12479021 : Blo 483789 12479021 := bstep (se 3 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 12479021 = 4679633) B4679633
theorem B2452031 : Blo 483789 2452031 := bstep (se 1 (by rfl) ⟨1839023, by rfl⟩ : syracuseStep 2452031 = 3678047) B3678047
theorem B485951 : Blo 483789 485951 := bstep (se 1 (by rfl) ⟨364463, by rfl⟩ : syracuseStep 485951 = 728927) B728927
theorem B485959 : Blo 483789 485959 := bstep (se 1 (by rfl) ⟨364469, by rfl⟩ : syracuseStep 485959 = 728939) B728939
theorem B486111 : Blo 483789 486111 := bstep (se 1 (by rfl) ⟨364583, by rfl⟩ : syracuseStep 486111 = 729167) B729167
theorem B486191 : Blo 483789 486191 := bstep (se 1 (by rfl) ⟨364643, by rfl⟩ : syracuseStep 486191 = 729287) B729287
theorem B1665917 : Blo 483789 1665917 := bstep (se 3 (by rfl) ⟨312359, by rfl⟩ : syracuseStep 1665917 = 624719) B624719
theorem B486299 : Blo 483789 486299 := bstep (se 1 (by rfl) ⟨364724, by rfl⟩ : syracuseStep 486299 = 729449) B729449
theorem B486351 : Blo 483789 486351 := bstep (se 1 (by rfl) ⟨364763, by rfl⟩ : syracuseStep 486351 = 729527) B729527
theorem B486375 : Blo 483789 486375 := bstep (se 1 (by rfl) ⟨364781, by rfl⟩ : syracuseStep 486375 = 729563) B729563
theorem B18738215 : Blo 483789 18738215 := bstep (se 1 (by rfl) ⟨14053661, by rfl⟩ : syracuseStep 18738215 = 28107323) B28107323
theorem B1633499 : Blo 483789 1633499 := bstep (se 1 (by rfl) ⟨1225124, by rfl⟩ : syracuseStep 1633499 = 2450249) B2450249
theorem B486687 : Blo 483789 486687 := bstep (se 1 (by rfl) ⟨365015, by rfl⟩ : syracuseStep 486687 = 730031) B730031
theorem B486747 : Blo 483789 486747 := bstep (se 1 (by rfl) ⟨365060, by rfl⟩ : syracuseStep 486747 = 730121) B730121
theorem B486767 : Blo 483789 486767 := bstep (se 1 (by rfl) ⟨365075, by rfl⟩ : syracuseStep 486767 = 730151) B730151
theorem B2485633 : Blo 483789 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B486823 : Blo 483789 486823 := bstep (se 1 (by rfl) ⟨365117, by rfl⟩ : syracuseStep 486823 = 730235) B730235
theorem B486907 : Blo 483789 486907 := bstep (se 1 (by rfl) ⟨365180, by rfl⟩ : syracuseStep 486907 = 730361) B730361
theorem B486975 : Blo 483789 486975 := bstep (se 1 (by rfl) ⟨365231, by rfl⟩ : syracuseStep 486975 = 730463) B730463
theorem B486983 : Blo 483789 486983 := bstep (se 1 (by rfl) ⟨365237, by rfl⟩ : syracuseStep 486983 = 730475) B730475
theorem B42430169 : Blo 483789 42430169 := bstep (se 2 (by rfl) ⟨15911313, by rfl⟩ : syracuseStep 42430169 = 31822627) B31822627
theorem B487135 : Blo 483789 487135 := bstep (se 1 (by rfl) ⟨365351, by rfl⟩ : syracuseStep 487135 = 730703) B730703
theorem B487215 : Blo 483789 487215 := bstep (se 1 (by rfl) ⟨365411, by rfl⟩ : syracuseStep 487215 = 730823) B730823
theorem B487323 : Blo 483789 487323 := bstep (se 1 (by rfl) ⟨365492, by rfl⟩ : syracuseStep 487323 = 730985) B730985
theorem B487375 : Blo 483789 487375 := bstep (se 1 (by rfl) ⟨365531, by rfl⟩ : syracuseStep 487375 = 731063) B731063
theorem B487399 : Blo 483789 487399 := bstep (se 1 (by rfl) ⟨365549, by rfl⟩ : syracuseStep 487399 = 731099) B731099
theorem B1634363 : Blo 483789 1634363 := bstep (se 1 (by rfl) ⟨1225772, by rfl⟩ : syracuseStep 1634363 = 2451545) B2451545
theorem B487711 : Blo 483789 487711 := bstep (se 1 (by rfl) ⟨365783, by rfl⟩ : syracuseStep 487711 = 731567) B731567
theorem B1634633 : Blo 483789 1634633 := bstep (se 2 (by rfl) ⟨612987, by rfl⟩ : syracuseStep 1634633 = 1225975) B1225975
theorem B487771 : Blo 483789 487771 := bstep (se 1 (by rfl) ⟨365828, by rfl⟩ : syracuseStep 487771 = 731657) B731657
theorem B4223339 : Blo 483789 4223339 := bstep (se 1 (by rfl) ⟨3167504, by rfl⟩ : syracuseStep 4223339 = 6335009) B6335009
theorem B2454137 : Blo 483789 2454137 := bstep (se 2 (by rfl) ⟨920301, by rfl⟩ : syracuseStep 2454137 = 1840603) B1840603
theorem B1077943 : Blo 483789 1077943 := bstep (se 1 (by rfl) ⟨808457, by rfl⟩ : syracuseStep 1077943 = 1616915) B1616915
theorem B4649957 : Blo 483789 4649957 := bstep (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) B871867
theorem B6222905 : Blo 483789 6222905 := bstep (se 2 (by rfl) ⟨2333589, by rfl⟩ : syracuseStep 6222905 = 4667179) B4667179
theorem B5272721 : Blo 483789 5272721 := bstep (se 2 (by rfl) ⟨1977270, by rfl⟩ : syracuseStep 5272721 = 3954541) B3954541
theorem B18708317 : Blo 483789 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B4651339 : Blo 483789 4651339 := bstep (se 1 (by rfl) ⟨3488504, by rfl⟩ : syracuseStep 4651339 = 6977009) B6977009
theorem B817499 : Blo 483789 817499 := bstep (se 1 (by rfl) ⟨613124, by rfl⟩ : syracuseStep 817499 = 1226249) B1226249
theorem B817519 : Blo 483789 817519 := bstep (se 1 (by rfl) ⟨613139, by rfl⟩ : syracuseStep 817519 = 1226279) B1226279
theorem B2455919 : Blo 483789 2455919 := bstep (se 1 (by rfl) ⟨1841939, by rfl⟩ : syracuseStep 2455919 = 3683879) B3683879
theorem B817735 : Blo 483789 817735 := bstep (se 1 (by rfl) ⟨613301, by rfl⟩ : syracuseStep 817735 = 1226603) B1226603
theorem B2620403 : Blo 483789 2620403 := bstep (se 1 (by rfl) ⟨1965302, by rfl⟩ : syracuseStep 2620403 = 3930605) B3930605
theorem B818167 : Blo 483789 818167 := bstep (se 1 (by rfl) ⟨613625, by rfl⟩ : syracuseStep 818167 = 1227251) B1227251
theorem B3111965 : Blo 483789 3111965 := bstep (se 3 (by rfl) ⟨583493, by rfl⟩ : syracuseStep 3111965 = 1166987) B1166987
theorem B818471 : Blo 483789 818471 := bstep (se 1 (by rfl) ⟨613853, by rfl⟩ : syracuseStep 818471 = 1227707) B1227707
theorem B1637819 : Blo 483789 1637819 := bstep (se 1 (by rfl) ⟨1228364, by rfl⟩ : syracuseStep 1637819 = 2456729) B2456729
theorem B4652569 : Blo 483789 4652569 := bstep (se 2 (by rfl) ⟨1744713, by rfl⟩ : syracuseStep 4652569 = 3489427) B3489427
theorem B818923 : Blo 483789 818923 := bstep (se 1 (by rfl) ⟨614192, by rfl⟩ : syracuseStep 818923 = 1228385) B1228385
theorem B1311175 : Blo 483789 1311175 := bstep (se 1 (by rfl) ⟨983381, by rfl⟩ : syracuseStep 1311175 = 1966763) B1966763
theorem B2458511 : Blo 483789 2458511 := bstep (se 1 (by rfl) ⟨1843883, by rfl⟩ : syracuseStep 2458511 = 3687767) B3687767
theorem B820219 : Blo 483789 820219 := bstep (se 1 (by rfl) ⟨615164, by rfl⟩ : syracuseStep 820219 = 1230329) B1230329
theorem B1639547 : Blo 483789 1639547 := bstep (se 1 (by rfl) ⟨1229660, by rfl⟩ : syracuseStep 1639547 = 2459321) B2459321
theorem B5538941 : Blo 483789 5538941 := bstep (se 3 (by rfl) ⟨1038551, by rfl⟩ : syracuseStep 5538941 = 2077103) B2077103
theorem B1639817 : Blo 483789 1639817 := bstep (se 2 (by rfl) ⟨614931, by rfl⟩ : syracuseStep 1639817 = 1229863) B1229863
theorem B820651 : Blo 483789 820651 := bstep (se 1 (by rfl) ⟨615488, by rfl⟩ : syracuseStep 820651 = 1230977) B1230977
theorem B1476191 : Blo 483789 1476191 := bstep (se 1 (by rfl) ⟨1107143, by rfl⟩ : syracuseStep 1476191 = 2214287) B2214287
theorem B820847 : Blo 483789 820847 := bstep (se 1 (by rfl) ⟨615635, by rfl⟩ : syracuseStep 820847 = 1231271) B1231271
theorem B820955 : Blo 483789 820955 := bstep (se 1 (by rfl) ⟨615716, by rfl⟩ : syracuseStep 820955 = 1231433) B1231433
theorem B6620957 : Blo 483789 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B821191 : Blo 483789 821191 := bstep (se 1 (by rfl) ⟨615893, by rfl⟩ : syracuseStep 821191 = 1231787) B1231787
theorem B3508343 : Blo 483789 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B1640573 : Blo 483789 1640573 := bstep (se 3 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 1640573 = 615215) B615215
theorem B1640843 : Blo 483789 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B1378721 : Blo 483789 1378721 := bstep (se 2 (by rfl) ⟨517020, by rfl⟩ : syracuseStep 1378721 = 1034041) B1034041
theorem B1837673 : Blo 483789 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B1870523 : Blo 483789 1870523 := bstep (se 1 (by rfl) ⟨1402892, by rfl⟩ : syracuseStep 1870523 = 2805785) B2805785
theorem B821947 : Blo 483789 821947 := bstep (se 1 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 821947 = 1232921) B1232921
theorem B822251 : Blo 483789 822251 := bstep (se 1 (by rfl) ⟨616688, by rfl⟩ : syracuseStep 822251 = 1233377) B1233377
theorem B3116065 : Blo 483789 3116065 := bstep (se 2 (by rfl) ⟨1168524, by rfl⟩ : syracuseStep 3116065 = 2337049) B2337049
theorem B2329823 : Blo 483789 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B6983009 : Blo 483789 6983009 := bstep (se 2 (by rfl) ⟨2618628, by rfl⟩ : syracuseStep 6983009 = 5237257) B5237257
theorem B1314377 : Blo 483789 1314377 := bstep (se 2 (by rfl) ⟨492891, by rfl⟩ : syracuseStep 1314377 = 985783) B985783
theorem B4165415 : Blo 483789 4165415 := bstep (se 1 (by rfl) ⟨3124061, by rfl⟩ : syracuseStep 4165415 = 6248123) B6248123
theorem B1773535 : Blo 483789 1773535 := bstep (se 1 (by rfl) ⟨1330151, by rfl⟩ : syracuseStep 1773535 = 2660303) B2660303
theorem B1642463 : Blo 483789 1642463 := bstep (se 1 (by rfl) ⟨1231847, by rfl⟩ : syracuseStep 1642463 = 2463695) B2463695
theorem B1642625 : Blo 483789 1642625 := bstep (se 2 (by rfl) ⟨615984, by rfl⟩ : syracuseStep 1642625 = 1231969) B1231969
theorem B3314177 : Blo 483789 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B7082497 : Blo 483789 7082497 := bstep (se 2 (by rfl) ⟨2655936, by rfl⟩ : syracuseStep 7082497 = 5311873) B5311873
theorem B1643111 : Blo 483789 1643111 := bstep (se 1 (by rfl) ⟨1232333, by rfl⟩ : syracuseStep 1643111 = 2464667) B2464667
theorem B725801 : Blo 483789 725801 := bstep (se 2 (by rfl) ⟨272175, by rfl⟩ : syracuseStep 725801 = 544351) B544351
theorem B725807 : Blo 483789 725807 := bstep (se 1 (by rfl) ⟨544355, by rfl⟩ : syracuseStep 725807 = 1088711) B1088711
theorem B725927 : Blo 483789 725927 := bstep (se 1 (by rfl) ⟨544445, by rfl⟩ : syracuseStep 725927 = 1088891) B1088891
theorem B1643435 : Blo 483789 1643435 := bstep (se 1 (by rfl) ⟨1232576, by rfl⟩ : syracuseStep 1643435 = 2465153) B2465153
theorem B726011 : Blo 483789 726011 := bstep (se 1 (by rfl) ⟨544508, by rfl⟩ : syracuseStep 726011 = 1089017) B1089017
theorem B2757671 : Blo 483789 2757671 := bstep (se 1 (by rfl) ⟨2068253, by rfl⟩ : syracuseStep 2757671 = 4136507) B4136507
theorem B11998259 : Blo 483789 11998259 := bstep (se 1 (by rfl) ⟨8998694, by rfl⟩ : syracuseStep 11998259 = 17997389) B17997389
theorem B726071 : Blo 483789 726071 := bstep (se 1 (by rfl) ⟨544553, by rfl⟩ : syracuseStep 726071 = 1089107) B1089107
theorem B726191 : Blo 483789 726191 := bstep (se 1 (by rfl) ⟨544643, by rfl⟩ : syracuseStep 726191 = 1089287) B1089287
theorem B4429009 : Blo 483789 4429009 := bstep (se 2 (by rfl) ⟨1660878, by rfl⟩ : syracuseStep 4429009 = 3321757) B3321757
theorem B1643867 : Blo 483789 1643867 := bstep (se 1 (by rfl) ⟨1232900, by rfl⟩ : syracuseStep 1643867 = 2465801) B2465801
theorem B1643975 : Blo 483789 1643975 := bstep (se 1 (by rfl) ⟨1232981, by rfl⟩ : syracuseStep 1643975 = 2465963) B2465963
theorem B3675617 : Blo 483789 3675617 := bstep (se 2 (by rfl) ⟨1378356, by rfl⟩ : syracuseStep 3675617 = 2756713) B2756713
theorem B726599 : Blo 483789 726599 := bstep (se 1 (by rfl) ⟨544949, by rfl⟩ : syracuseStep 726599 = 1089899) B1089899
theorem B726695 : Blo 483789 726695 := bstep (se 1 (by rfl) ⟨545021, by rfl⟩ : syracuseStep 726695 = 1090043) B1090043
theorem B726779 : Blo 483789 726779 := bstep (se 1 (by rfl) ⟨545084, by rfl⟩ : syracuseStep 726779 = 1090169) B1090169
theorem B1840907 : Blo 483789 1840907 := bstep (se 1 (by rfl) ⟨1380680, by rfl⟩ : syracuseStep 1840907 = 2761361) B2761361
theorem B1644299 : Blo 483789 1644299 := bstep (se 1 (by rfl) ⟨1233224, by rfl⟩ : syracuseStep 1644299 = 2466449) B2466449
theorem B726815 : Blo 483789 726815 := bstep (se 1 (by rfl) ⟨545111, by rfl⟩ : syracuseStep 726815 = 1090223) B1090223
theorem B726863 : Blo 483789 726863 := bstep (se 1 (by rfl) ⟨545147, by rfl⟩ : syracuseStep 726863 = 1090295) B1090295
theorem B726983 : Blo 483789 726983 := bstep (se 1 (by rfl) ⟨545237, by rfl⟩ : syracuseStep 726983 = 1090475) B1090475
theorem B1644569 : Blo 483789 1644569 := bstep (se 2 (by rfl) ⟨616713, by rfl⟩ : syracuseStep 1644569 = 1233427) B1233427
theorem B1382663 : Blo 483789 1382663 := bstep (se 1 (by rfl) ⟨1036997, by rfl⟩ : syracuseStep 1382663 = 2073995) B2073995
theorem B727337 : Blo 483789 727337 := bstep (se 2 (by rfl) ⟨272751, by rfl⟩ : syracuseStep 727337 = 545503) B545503
theorem B727343 : Blo 483789 727343 := bstep (se 1 (by rfl) ⟨545507, by rfl⟩ : syracuseStep 727343 = 1091015) B1091015
theorem B2333051 : Blo 483789 2333051 := bstep (se 1 (by rfl) ⟨1749788, by rfl⟩ : syracuseStep 2333051 = 3499577) B3499577
theorem B6822319 : Blo 483789 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B1382845 : Blo 483789 1382845 := bstep (se 3 (by rfl) ⟨259283, by rfl⟩ : syracuseStep 1382845 = 518567) B518567
theorem B727583 : Blo 483789 727583 := bstep (se 1 (by rfl) ⟨545687, by rfl⟩ : syracuseStep 727583 = 1091375) B1091375
theorem B1743707 : Blo 483789 1743707 := bstep (se 1 (by rfl) ⟨1307780, by rfl⟩ : syracuseStep 1743707 = 2615561) B2615561
theorem B727967 : Blo 483789 727967 := bstep (se 1 (by rfl) ⟨545975, by rfl⟩ : syracuseStep 727967 = 1091951) B1091951
theorem B728015 : Blo 483789 728015 := bstep (se 1 (by rfl) ⟨546011, by rfl⟩ : syracuseStep 728015 = 1092023) B1092023
theorem B728105 : Blo 483789 728105 := bstep (se 2 (by rfl) ⟨273039, by rfl⟩ : syracuseStep 728105 = 546079) B546079
theorem B728111 : Blo 483789 728111 := bstep (se 1 (by rfl) ⟨546083, by rfl⟩ : syracuseStep 728111 = 1092167) B1092167
theorem B728135 : Blo 483789 728135 := bstep (se 1 (by rfl) ⟨546101, by rfl⟩ : syracuseStep 728135 = 1092203) B1092203
theorem B13999229 : Blo 483789 13999229 := bstep (se 3 (by rfl) ⟨2624855, by rfl⟩ : syracuseStep 13999229 = 5249711) B5249711
theorem B12426533 : Blo 483789 12426533 := bstep (se 4 (by rfl) ⟨1164987, by rfl⟩ : syracuseStep 12426533 = 2329975) B2329975
theorem B728399 : Blo 483789 728399 := bstep (se 1 (by rfl) ⟨546299, by rfl⟩ : syracuseStep 728399 = 1092599) B1092599
theorem B1645919 : Blo 483789 1645919 := bstep (se 1 (by rfl) ⟨1234439, by rfl⟩ : syracuseStep 1645919 = 2468879) B2468879
theorem B12492143 : Blo 483789 12492143 := bstep (se 1 (by rfl) ⟨9369107, by rfl⟩ : syracuseStep 12492143 = 18738215) B18738215
theorem B728489 : Blo 483789 728489 := bstep (se 2 (by rfl) ⟨273183, by rfl⟩ : syracuseStep 728489 = 546367) B546367
theorem B1088999 : Blo 483789 1088999 := bstep (se 1 (by rfl) ⟨816749, by rfl⟩ : syracuseStep 1088999 = 1633499) B1633499
theorem B728639 : Blo 483789 728639 := bstep (se 1 (by rfl) ⟨546479, by rfl⟩ : syracuseStep 728639 = 1092959) B1092959
theorem B28286779 : Blo 483789 28286779 := bstep (se 1 (by rfl) ⟨21215084, by rfl⟩ : syracuseStep 28286779 = 42430169) B42430169
theorem B728903 : Blo 483789 728903 := bstep (se 1 (by rfl) ⟨546677, by rfl⟩ : syracuseStep 728903 = 1093355) B1093355
theorem B728987 : Blo 483789 728987 := bstep (se 1 (by rfl) ⟨546740, by rfl⟩ : syracuseStep 728987 = 1093481) B1093481
theorem B1089575 : Blo 483789 1089575 := bstep (se 1 (by rfl) ⟨817181, by rfl⟩ : syracuseStep 1089575 = 1634363) B1634363
theorem B1089755 : Blo 483789 1089755 := bstep (se 1 (by rfl) ⟨817316, by rfl⟩ : syracuseStep 1089755 = 1634633) B1634633
theorem B9314675 : Blo 483789 9314675 := bstep (se 1 (by rfl) ⟨6986006, by rfl⟩ : syracuseStep 9314675 = 13972013) B13972013
theorem B6201785 : Blo 483789 6201785 := bstep (se 2 (by rfl) ⟨2325669, by rfl⟩ : syracuseStep 6201785 = 4651339) B4651339
theorem B729551 : Blo 483789 729551 := bstep (se 1 (by rfl) ⟨547163, by rfl⟩ : syracuseStep 729551 = 1094327) B1094327
theorem B1090025 : Blo 483789 1090025 := bstep (se 2 (by rfl) ⟨408759, by rfl⟩ : syracuseStep 1090025 = 817519) B817519
theorem B729593 : Blo 483789 729593 := bstep (se 2 (by rfl) ⟨273597, by rfl⟩ : syracuseStep 729593 = 547195) B547195
theorem B729695 : Blo 483789 729695 := bstep (se 1 (by rfl) ⟨547271, by rfl⟩ : syracuseStep 729695 = 1094543) B1094543
theorem B1090313 : Blo 483789 1090313 := bstep (se 2 (by rfl) ⟨408867, by rfl⟩ : syracuseStep 1090313 = 817735) B817735
theorem B3515147 : Blo 483789 3515147 := bstep (se 1 (by rfl) ⟨2636360, by rfl⟩ : syracuseStep 3515147 = 5272721) B5272721
theorem B1975195 : Blo 483789 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B730175 : Blo 483789 730175 := bstep (se 1 (by rfl) ⟨547631, by rfl⟩ : syracuseStep 730175 = 1095263) B1095263
theorem B730217 : Blo 483789 730217 := bstep (se 2 (by rfl) ⟨273831, by rfl⟩ : syracuseStep 730217 = 547663) B547663
theorem B730319 : Blo 483789 730319 := bstep (se 1 (by rfl) ⟨547739, by rfl⟩ : syracuseStep 730319 = 1095479) B1095479
theorem B1090889 : Blo 483789 1090889 := bstep (se 2 (by rfl) ⟨409083, by rfl⟩ : syracuseStep 1090889 = 818167) B818167
theorem B730523 : Blo 483789 730523 := bstep (se 1 (by rfl) ⟨547892, by rfl⟩ : syracuseStep 730523 = 1095785) B1095785
theorem B730745 : Blo 483789 730745 := bstep (se 2 (by rfl) ⟨274029, by rfl⟩ : syracuseStep 730745 = 548059) B548059
theorem B730847 : Blo 483789 730847 := bstep (se 1 (by rfl) ⟨548135, by rfl⟩ : syracuseStep 730847 = 1096271) B1096271
theorem B730943 : Blo 483789 730943 := bstep (se 1 (by rfl) ⟨548207, by rfl⟩ : syracuseStep 730943 = 1096415) B1096415
theorem B731111 : Blo 483789 731111 := bstep (se 1 (by rfl) ⟨548333, by rfl⟩ : syracuseStep 731111 = 1096667) B1096667
theorem B1746935 : Blo 483789 1746935 := bstep (se 1 (by rfl) ⟨1310201, by rfl⟩ : syracuseStep 1746935 = 2620403) B2620403
theorem B731129 : Blo 483789 731129 := bstep (se 2 (by rfl) ⟨274173, by rfl⟩ : syracuseStep 731129 = 548347) B548347
theorem B2074643 : Blo 483789 2074643 := bstep (se 1 (by rfl) ⟨1555982, by rfl⟩ : syracuseStep 2074643 = 3111965) B3111965
theorem B6203425 : Blo 483789 6203425 := bstep (se 2 (by rfl) ⟨2326284, by rfl⟩ : syracuseStep 6203425 = 4652569) B4652569
theorem B731231 : Blo 483789 731231 := bstep (se 1 (by rfl) ⟨548423, by rfl⟩ : syracuseStep 731231 = 1096847) B1096847
theorem B731291 : Blo 483789 731291 := bstep (se 1 (by rfl) ⟨548468, by rfl⟩ : syracuseStep 731291 = 1096937) B1096937
theorem B4139171 : Blo 483789 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B1124543 : Blo 483789 1124543 := bstep (se 1 (by rfl) ⟨843407, by rfl⟩ : syracuseStep 1124543 = 1686815) B1686815
theorem B731327 : Blo 483789 731327 := bstep (se 1 (by rfl) ⟨548495, by rfl⟩ : syracuseStep 731327 = 1096991) B1096991
theorem B1845463 : Blo 483789 1845463 := bstep (se 1 (by rfl) ⟨1384097, by rfl⟩ : syracuseStep 1845463 = 2768195) B2768195
theorem B731369 : Blo 483789 731369 := bstep (se 2 (by rfl) ⟨274263, by rfl⟩ : syracuseStep 731369 = 548527) B548527
theorem B1091879 : Blo 483789 1091879 := bstep (se 1 (by rfl) ⟨818909, by rfl⟩ : syracuseStep 1091879 = 1637819) B1637819
theorem B1091897 : Blo 483789 1091897 := bstep (se 2 (by rfl) ⟨409461, by rfl⟩ : syracuseStep 1091897 = 818923) B818923
theorem B2337281 : Blo 483789 2337281 := bstep (se 2 (by rfl) ⟨876480, by rfl⟩ : syracuseStep 2337281 = 1752961) B1752961
theorem B731675 : Blo 483789 731675 := bstep (se 1 (by rfl) ⟨548756, by rfl⟩ : syracuseStep 731675 = 1097513) B1097513
theorem B3680963 : Blo 483789 3680963 := bstep (se 1 (by rfl) ⟨2760722, by rfl⟩ : syracuseStep 3680963 = 5521445) B5521445
theorem B2468555 : Blo 483789 2468555 := bstep (se 1 (by rfl) ⟨1851416, by rfl⟩ : syracuseStep 2468555 = 3702833) B3702833
theorem B9120883 : Blo 483789 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B3419435 : Blo 483789 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B10366427 : Blo 483789 10366427 := bstep (se 1 (by rfl) ⟨7774820, by rfl⟩ : syracuseStep 10366427 = 15549641) B15549641
theorem B23703101 : Blo 483789 23703101 := bstep (se 3 (by rfl) ⟨4444331, by rfl⟩ : syracuseStep 23703101 = 8888663) B8888663
theorem B699967 : Blo 483789 699967 := bstep (se 1 (by rfl) ⟨524975, by rfl⟩ : syracuseStep 699967 = 1049951) B1049951
theorem B1093193 : Blo 483789 1093193 := bstep (se 2 (by rfl) ⟨409947, by rfl⟩ : syracuseStep 1093193 = 819895) B819895
theorem B1847195 : Blo 483789 1847195 := bstep (se 1 (by rfl) ⟨1385396, by rfl⟩ : syracuseStep 1847195 = 2770793) B2770793
theorem B1388495 : Blo 483789 1388495 := bstep (se 1 (by rfl) ⟨1041371, by rfl⟩ : syracuseStep 1388495 = 2082743) B2082743
theorem B1388927 : Blo 483789 1388927 := bstep (se 1 (by rfl) ⟨1041695, by rfl⟩ : syracuseStep 1388927 = 2083391) B2083391
theorem B5485391 : Blo 483789 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B1225601 : Blo 483789 1225601 := bstep (se 2 (by rfl) ⟨459600, by rfl⟩ : syracuseStep 1225601 = 919201) B919201
theorem B1094651 : Blo 483789 1094651 := bstep (se 1 (by rfl) ⟨820988, by rfl⟩ : syracuseStep 1094651 = 1641977) B1641977
theorem B1750079 : Blo 483789 1750079 := bstep (se 1 (by rfl) ⟨1312559, by rfl⟩ : syracuseStep 1750079 = 2625119) B2625119
theorem B1094831 : Blo 483789 1094831 := bstep (se 1 (by rfl) ⟨821123, by rfl⟩ : syracuseStep 1094831 = 1642247) B1642247
theorem B5518529 : Blo 483789 5518529 := bstep (se 2 (by rfl) ⟨2069448, by rfl⟩ : syracuseStep 5518529 = 4138897) B4138897
theorem B1094867 : Blo 483789 1094867 := bstep (se 1 (by rfl) ⟨821150, by rfl⟩ : syracuseStep 1094867 = 1642301) B1642301
theorem B1095137 : Blo 483789 1095137 := bstep (se 2 (by rfl) ⟨410676, by rfl⟩ : syracuseStep 1095137 = 821353) B821353
theorem B1226411 : Blo 483789 1226411 := bstep (se 1 (by rfl) ⟨919808, by rfl⟩ : syracuseStep 1226411 = 1839617) B1839617
theorem B3979145 : Blo 483789 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B1751003 : Blo 483789 1751003 := bstep (se 1 (by rfl) ⟨1313252, by rfl⟩ : syracuseStep 1751003 = 2626505) B2626505
theorem B1226735 : Blo 483789 1226735 := bstep (se 1 (by rfl) ⟨920051, by rfl⟩ : syracuseStep 1226735 = 1840103) B1840103
theorem B1849337 : Blo 483789 1849337 := bstep (se 2 (by rfl) ⟨693501, by rfl⟩ : syracuseStep 1849337 = 1387003) B1387003
theorem B7092775 : Blo 483789 7092775 := bstep (se 1 (by rfl) ⟨5319581, by rfl⟩ : syracuseStep 7092775 = 10639163) B10639163
theorem B1555291 : Blo 483789 1555291 := bstep (se 1 (by rfl) ⟨1166468, by rfl⟩ : syracuseStep 1555291 = 2332937) B2332937
theorem B1096775 : Blo 483789 1096775 := bstep (se 1 (by rfl) ⟨822581, by rfl⟩ : syracuseStep 1096775 = 1645163) B1645163
theorem B1228243 : Blo 483789 1228243 := bstep (se 1 (by rfl) ⟨921182, by rfl⟩ : syracuseStep 1228243 = 1842365) B1842365
theorem B1097171 : Blo 483789 1097171 := bstep (se 1 (by rfl) ⟨822878, by rfl⟩ : syracuseStep 1097171 = 1645757) B1645757
theorem B1556111 : Blo 483789 1556111 := bstep (se 1 (by rfl) ⟨1167083, by rfl⟩ : syracuseStep 1556111 = 2334167) B2334167
theorem B1097441 : Blo 483789 1097441 := bstep (se 2 (by rfl) ⟨411540, by rfl⟩ : syracuseStep 1097441 = 823081) B823081
theorem B1851113 : Blo 483789 1851113 := bstep (se 2 (by rfl) ⟨694167, by rfl⟩ : syracuseStep 1851113 = 1388335) B1388335
theorem B2768651 : Blo 483789 2768651 := bstep (se 1 (by rfl) ⟨2076488, by rfl⟩ : syracuseStep 2768651 = 4152977) B4152977
theorem B1556279 : Blo 483789 1556279 := bstep (se 1 (by rfl) ⟨1167209, by rfl⟩ : syracuseStep 1556279 = 2334419) B2334419
theorem B2769335 : Blo 483789 2769335 := bstep (se 1 (by rfl) ⟨2077001, by rfl⟩ : syracuseStep 2769335 = 4154003) B4154003
theorem B5620151 : Blo 483789 5620151 := bstep (se 1 (by rfl) ⟨4215113, by rfl⟩ : syracuseStep 5620151 = 8430227) B8430227
theorem B2015873 : Blo 483789 2015873 := bstep (se 2 (by rfl) ⟨755952, by rfl⟩ : syracuseStep 2015873 = 1511905) B1511905
theorem B1230187 : Blo 483789 1230187 := bstep (se 1 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 1230187 = 1845281) B1845281
theorem B2082419 : Blo 483789 2082419 := bstep (se 1 (by rfl) ⟨1561814, by rfl⟩ : syracuseStep 2082419 = 3123629) B3123629
theorem B1230623 : Blo 483789 1230623 := bstep (se 1 (by rfl) ⟨922967, by rfl⟩ : syracuseStep 1230623 = 1845935) B1845935
theorem B1558739 : Blo 483789 1558739 := bstep (se 1 (by rfl) ⟨1169054, by rfl⟩ : syracuseStep 1558739 = 2338109) B2338109
theorem B1558777 : Blo 483789 1558777 := bstep (se 2 (by rfl) ⟨584541, by rfl⟩ : syracuseStep 1558777 = 1169083) B1169083
theorem B1559047 : Blo 483789 1559047 := bstep (se 1 (by rfl) ⟨1169285, by rfl⟩ : syracuseStep 1559047 = 2338571) B2338571
theorem B99830485 : Blo 483789 99830485 := bstep (se 7 (by rfl) ⟨1169888, by rfl⟩ : syracuseStep 99830485 = 2339777) B2339777
theorem B6212447 : Blo 483789 6212447 := bstep (se 1 (by rfl) ⟨4659335, by rfl⟩ : syracuseStep 6212447 = 9318671) B9318671
theorem B1231919 : Blo 483789 1231919 := bstep (se 1 (by rfl) ⟨923939, by rfl⟩ : syracuseStep 1231919 = 1847879) B1847879
theorem B3099971 : Blo 483789 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B4148603 : Blo 483789 4148603 := bstep (se 1 (by rfl) ⟨3111452, by rfl⟩ : syracuseStep 4148603 = 6222905) B6222905
theorem B1035767 : Blo 483789 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B2772569 : Blo 483789 2772569 := bstep (se 2 (by rfl) ⟨1039713, by rfl⟩ : syracuseStep 2772569 = 2079427) B2079427
theorem B1232779 : Blo 483789 1232779 := bstep (se 1 (by rfl) ⟨924584, by rfl⟩ : syracuseStep 1232779 = 1849169) B1849169
theorem B12472211 : Blo 483789 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B1233083 : Blo 483789 1233083 := bstep (se 1 (by rfl) ⟨924812, by rfl⟩ : syracuseStep 1233083 = 1849625) B1849625
theorem B544999 : Blo 483789 544999 := bstep (se 1 (by rfl) ⟨408749, by rfl⟩ : syracuseStep 544999 = 817499) B817499
theorem B1167671 : Blo 483789 1167671 := bstep (se 1 (by rfl) ⟨875753, by rfl⟩ : syracuseStep 1167671 = 1751507) B1751507
theorem B1036793 : Blo 483789 1036793 := bstep (se 2 (by rfl) ⟨388797, by rfl⟩ : syracuseStep 1036793 = 777595) B777595
theorem B3691169 : Blo 483789 3691169 := bstep (se 2 (by rfl) ⟨1384188, by rfl⟩ : syracuseStep 3691169 = 2768377) B2768377
theorem B1233569 : Blo 483789 1233569 := bstep (se 2 (by rfl) ⟨462588, by rfl⟩ : syracuseStep 1233569 = 925177) B925177
theorem B545647 : Blo 483789 545647 := bstep (se 1 (by rfl) ⟨409235, by rfl⟩ : syracuseStep 545647 = 818471) B818471
theorem B1561609 : Blo 483789 1561609 := bstep (se 2 (by rfl) ⟨585603, by rfl⟩ : syracuseStep 1561609 = 1171207) B1171207
theorem B1561673 : Blo 483789 1561673 := bstep (se 2 (by rfl) ⟨585627, by rfl⟩ : syracuseStep 1561673 = 1171255) B1171255
theorem B3692141 : Blo 483789 3692141 := bstep (se 3 (by rfl) ⟨692276, by rfl⟩ : syracuseStep 3692141 = 1384553) B1384553
theorem B5527277 : Blo 483789 5527277 := bstep (se 3 (by rfl) ⟨1036364, by rfl⟩ : syracuseStep 5527277 = 2072729) B2072729
theorem B294508331 : Blo 483789 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B546799 : Blo 483789 546799 := bstep (se 1 (by rfl) ⟨410099, by rfl⟩ : syracuseStep 546799 = 820199) B820199
theorem B1038433 : Blo 483789 1038433 := bstep (se 2 (by rfl) ⟨389412, by rfl⟩ : syracuseStep 1038433 = 778825) B778825
theorem B3955067 : Blo 483789 3955067 := bstep (se 1 (by rfl) ⟨2966300, by rfl⟩ : syracuseStep 3955067 = 5932601) B5932601
theorem B2775485 : Blo 483789 2775485 := bstep (se 3 (by rfl) ⟨520403, by rfl⟩ : syracuseStep 2775485 = 1040807) B1040807
theorem B11852243 : Blo 483789 11852243 := bstep (se 1 (by rfl) ⟨8889182, by rfl⟩ : syracuseStep 11852243 = 17778365) B17778365
theorem B102816289 : Blo 483789 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B1169977 : Blo 483789 1169977 := bstep (se 2 (by rfl) ⟨438741, by rfl⟩ : syracuseStep 1169977 = 877483) B877483
theorem B11819641 : Blo 483789 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B6314669 : Blo 483789 6314669 := bstep (se 3 (by rfl) ⟨1184000, by rfl⟩ : syracuseStep 6314669 = 2368001) B2368001
theorem B613423 : Blo 483789 613423 := bstep (se 1 (by rfl) ⟨460067, by rfl⟩ : syracuseStep 613423 = 920135) B920135
theorem B5627083 : Blo 483789 5627083 := bstep (se 1 (by rfl) ⟨4220312, by rfl⟩ : syracuseStep 5627083 = 8440625) B8440625
theorem B14147459 : Blo 483789 14147459 := bstep (se 1 (by rfl) ⟨10610594, by rfl⟩ : syracuseStep 14147459 = 21221189) B21221189
theorem B1663111 : Blo 483789 1663111 := bstep (se 1 (by rfl) ⟨1247333, by rfl⟩ : syracuseStep 1663111 = 2494667) B2494667
theorem B483791 : Blo 483789 483791 := bstep (se 1 (by rfl) ⟨362843, by rfl⟩ : syracuseStep 483791 = 725687) B725687
theorem B483943 : Blo 483789 483943 := bstep (se 1 (by rfl) ⟨362957, by rfl⟩ : syracuseStep 483943 = 725915) B725915
theorem B484207 : Blo 483789 484207 := bstep (se 1 (by rfl) ⟨363155, by rfl⟩ : syracuseStep 484207 = 726311) B726311
theorem B484263 : Blo 483789 484263 := bstep (se 1 (by rfl) ⟨363197, by rfl⟩ : syracuseStep 484263 = 726395) B726395
theorem B484347 : Blo 483789 484347 := bstep (se 1 (by rfl) ⟨363260, by rfl⟩ : syracuseStep 484347 = 726521) B726521
theorem B484415 : Blo 483789 484415 := bstep (se 1 (by rfl) ⟨363311, by rfl⟩ : syracuseStep 484415 = 726623) B726623
theorem B484559 : Blo 483789 484559 := bstep (se 1 (by rfl) ⟨363419, by rfl⟩ : syracuseStep 484559 = 726839) B726839
theorem B484763 : Blo 483789 484763 := bstep (se 1 (by rfl) ⟨363572, by rfl⟩ : syracuseStep 484763 = 727145) B727145
theorem B484975 : Blo 483789 484975 := bstep (se 1 (by rfl) ⟨363731, by rfl⟩ : syracuseStep 484975 = 727463) B727463
theorem B485031 : Blo 483789 485031 := bstep (se 1 (by rfl) ⟨363773, by rfl⟩ : syracuseStep 485031 = 727547) B727547
theorem B485115 : Blo 483789 485115 := bstep (se 1 (by rfl) ⟨363836, by rfl⟩ : syracuseStep 485115 = 727673) B727673
theorem B616187 : Blo 483789 616187 := bstep (se 1 (by rfl) ⟨462140, by rfl⟩ : syracuseStep 616187 = 924281) B924281
theorem B485151 : Blo 483789 485151 := bstep (se 1 (by rfl) ⟨363863, by rfl⟩ : syracuseStep 485151 = 727727) B727727
theorem B485183 : Blo 483789 485183 := bstep (se 1 (by rfl) ⟨363887, by rfl⟩ : syracuseStep 485183 = 727775) B727775
theorem B485359 : Blo 483789 485359 := bstep (se 1 (by rfl) ⟨364019, by rfl⟩ : syracuseStep 485359 = 728039) B728039
theorem B485531 : Blo 483789 485531 := bstep (se 1 (by rfl) ⟨364148, by rfl⟩ : syracuseStep 485531 = 728297) B728297
theorem B485567 : Blo 483789 485567 := bstep (se 1 (by rfl) ⟨364175, by rfl⟩ : syracuseStep 485567 = 728351) B728351
theorem B485679 : Blo 483789 485679 := bstep (se 1 (by rfl) ⟨364259, by rfl⟩ : syracuseStep 485679 = 728519) B728519
theorem B1862027 : Blo 483789 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B485915 : Blo 483789 485915 := bstep (se 1 (by rfl) ⟨364436, by rfl⟩ : syracuseStep 485915 = 728873) B728873
theorem B616987 : Blo 483789 616987 := bstep (se 1 (by rfl) ⟨462740, by rfl⟩ : syracuseStep 616987 = 925481) B925481
theorem B3336731 : Blo 483789 3336731 := bstep (se 1 (by rfl) ⟨2502548, by rfl⟩ : syracuseStep 3336731 = 5005097) B5005097
theorem B485919 : Blo 483789 485919 := bstep (se 1 (by rfl) ⟨364439, by rfl⟩ : syracuseStep 485919 = 728879) B728879
theorem B9366191 : Blo 483789 9366191 := bstep (se 1 (by rfl) ⟨7024643, by rfl⟩ : syracuseStep 9366191 = 14049287) B14049287
theorem B6646475 : Blo 483789 6646475 := bstep (se 1 (by rfl) ⟨4984856, by rfl⟩ : syracuseStep 6646475 = 9969713) B9969713
theorem B486235 : Blo 483789 486235 := bstep (se 1 (by rfl) ⟨364676, by rfl⟩ : syracuseStep 486235 = 729353) B729353
theorem B486303 : Blo 483789 486303 := bstep (se 1 (by rfl) ⟨364727, by rfl⟩ : syracuseStep 486303 = 729455) B729455
theorem B486447 : Blo 483789 486447 := bstep (se 1 (by rfl) ⟨364835, by rfl⟩ : syracuseStep 486447 = 729671) B729671
theorem B486471 : Blo 483789 486471 := bstep (se 1 (by rfl) ⟨364853, by rfl⟩ : syracuseStep 486471 = 729707) B729707
theorem B486623 : Blo 483789 486623 := bstep (se 1 (by rfl) ⟨364967, by rfl⟩ : syracuseStep 486623 = 729935) B729935
theorem B486887 : Blo 483789 486887 := bstep (se 1 (by rfl) ⟨365165, by rfl⟩ : syracuseStep 486887 = 730331) B730331
theorem B1437257 : Blo 483789 1437257 := bstep (se 2 (by rfl) ⟨538971, by rfl⟩ : syracuseStep 1437257 = 1077943) B1077943
theorem B487003 : Blo 483789 487003 := bstep (se 1 (by rfl) ⟨365252, by rfl⟩ : syracuseStep 487003 = 730505) B730505
theorem B1404691 : Blo 483789 1404691 := bstep (se 1 (by rfl) ⟨1053518, by rfl⟩ : syracuseStep 1404691 = 2107037) B2107037
theorem B487239 : Blo 483789 487239 := bstep (se 1 (by rfl) ⟨365429, by rfl⟩ : syracuseStep 487239 = 730859) B730859
theorem B1634255 : Blo 483789 1634255 := bstep (se 1 (by rfl) ⟨1225691, by rfl⟩ : syracuseStep 1634255 = 2451383) B2451383
theorem B487391 : Blo 483789 487391 := bstep (se 1 (by rfl) ⟨365543, by rfl⟩ : syracuseStep 487391 = 731087) B731087
theorem B7073851 : Blo 483789 7073851 := bstep (se 1 (by rfl) ⟨5305388, by rfl⟩ : syracuseStep 7073851 = 10610777) B10610777
theorem B1863869 : Blo 483789 1863869 := bstep (se 3 (by rfl) ⟨349475, by rfl⟩ : syracuseStep 1863869 = 698951) B698951
theorem B13988051 : Blo 483789 13988051 := bstep (se 1 (by rfl) ⟨10491038, by rfl⟩ : syracuseStep 13988051 = 20982077) B20982077
theorem B487655 : Blo 483789 487655 := bstep (se 1 (by rfl) ⟨365741, by rfl⟩ : syracuseStep 487655 = 731483) B731483
theorem B8319347 : Blo 483789 8319347 := bstep (se 1 (by rfl) ⟨6239510, by rfl⟩ : syracuseStep 8319347 = 12479021) B12479021
theorem B1634687 : Blo 483789 1634687 := bstep (se 1 (by rfl) ⟨1226015, by rfl⟩ : syracuseStep 1634687 = 2452031) B2452031
theorem B1405433 : Blo 483789 1405433 := bstep (se 2 (by rfl) ⟨527037, by rfl⟩ : syracuseStep 1405433 = 1054075) B1054075
theorem B1110611 : Blo 483789 1110611 := bstep (se 1 (by rfl) ⟨832958, by rfl⟩ : syracuseStep 1110611 = 1665917) B1665917
theorem B1668271 : Blo 483789 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B2815559 : Blo 483789 2815559 := bstep (se 1 (by rfl) ⟨2111669, by rfl⟩ : syracuseStep 2815559 = 4223339) B4223339
theorem B1636091 : Blo 483789 1636091 := bstep (se 1 (by rfl) ⟨1227068, by rfl⟩ : syracuseStep 1636091 = 2454137) B2454137
theorem B816959 : Blo 483789 816959 := bstep (se 1 (by rfl) ⟨612719, by rfl⟩ : syracuseStep 816959 = 1225439) B1225439
theorem B817033 : Blo 483789 817033 := bstep (se 2 (by rfl) ⟨306387, by rfl⟩ : syracuseStep 817033 = 612775) B612775
theorem B2455433 : Blo 483789 2455433 := bstep (se 2 (by rfl) ⟨920787, by rfl⟩ : syracuseStep 2455433 = 1841575) B1841575
theorem B3504019 : Blo 483789 3504019 := bstep (se 1 (by rfl) ⟨2628014, by rfl⟩ : syracuseStep 3504019 = 5256029) B5256029
theorem B1636253 : Blo 483789 1636253 := bstep (se 3 (by rfl) ⟨306797, by rfl⟩ : syracuseStep 1636253 = 613595) B613595
theorem B817465 : Blo 483789 817465 := bstep (se 2 (by rfl) ⟨306549, by rfl⟩ : syracuseStep 817465 = 613099) B613099
theorem B2128403 : Blo 483789 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B817769 : Blo 483789 817769 := bstep (se 2 (by rfl) ⟨306663, by rfl⟩ : syracuseStep 817769 = 613327) B613327
theorem B1637225 : Blo 483789 1637225 := bstep (se 2 (by rfl) ⟨613959, by rfl⟩ : syracuseStep 1637225 = 1227919) B1227919
theorem B1637279 : Blo 483789 1637279 := bstep (se 1 (by rfl) ⟨1227959, by rfl⟩ : syracuseStep 1637279 = 2455919) B2455919
theorem B818599 : Blo 483789 818599 := bstep (se 1 (by rfl) ⟨613949, by rfl⟩ : syracuseStep 818599 = 1227899) B1227899
theorem B818761 : Blo 483789 818761 := bstep (se 2 (by rfl) ⟨307035, by rfl⟩ : syracuseStep 818761 = 614071) B614071
theorem B818795 : Blo 483789 818795 := bstep (se 1 (by rfl) ⟨614096, by rfl⟩ : syracuseStep 818795 = 1228193) B1228193
theorem B6225569 : Blo 483789 6225569 := bstep (se 2 (by rfl) ⟨2334588, by rfl⟩ : syracuseStep 6225569 = 4669177) B4669177
theorem B819065 : Blo 483789 819065 := bstep (se 2 (by rfl) ⟨307149, by rfl⟩ : syracuseStep 819065 = 614299) B614299
theorem B1343915 : Blo 483789 1343915 := bstep (se 1 (by rfl) ⟨1007936, by rfl⟩ : syracuseStep 1343915 = 2015873) B2015873
theorem B1639007 : Blo 483789 1639007 := bstep (se 1 (by rfl) ⟨1229255, by rfl⟩ : syracuseStep 1639007 = 2458511) B2458511
theorem B3703805 : Blo 483789 3703805 := bstep (se 3 (by rfl) ⟨694463, by rfl⟩ : syracuseStep 3703805 = 1388927) B1388927
theorem B820415 : Blo 483789 820415 := bstep (se 1 (by rfl) ⟨615311, by rfl⟩ : syracuseStep 820415 = 1230623) B1230623
theorem B1247015 : Blo 483789 1247015 := bstep (se 1 (by rfl) ⟨935261, by rfl⟩ : syracuseStep 1247015 = 1870523) B1870523
theorem B1640249 : Blo 483789 1640249 := bstep (se 2 (by rfl) ⟨615093, by rfl⟩ : syracuseStep 1640249 = 1230187) B1230187
theorem B821279 : Blo 483789 821279 := bstep (se 1 (by rfl) ⟨615959, by rfl⟩ : syracuseStep 821279 = 1231919) B1231919
theorem B2066647 : Blo 483789 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B4655339 : Blo 483789 4655339 := bstep (se 1 (by rfl) ⟨3491504, by rfl⟩ : syracuseStep 4655339 = 6983009) B6983009
theorem B822055 : Blo 483789 822055 := bstep (se 1 (by rfl) ⟨616541, by rfl⟩ : syracuseStep 822055 = 1233083) B1233083
theorem B2460617 : Blo 483789 2460617 := bstep (se 2 (by rfl) ⟨922731, by rfl⟩ : syracuseStep 2460617 = 1845463) B1845463
theorem B691195 : Blo 483789 691195 := bstep (se 1 (by rfl) ⟨518396, by rfl⟩ : syracuseStep 691195 = 1036793) B1036793
theorem B2460779 : Blo 483789 2460779 := bstep (se 1 (by rfl) ⟨1845584, by rfl⟩ : syracuseStep 2460779 = 3691169) B3691169
theorem B822379 : Blo 483789 822379 := bstep (se 1 (by rfl) ⟨616784, by rfl⟩ : syracuseStep 822379 = 1233569) B1233569
theorem B1838447 : Blo 483789 1838447 := bstep (se 1 (by rfl) ⟨1378835, by rfl⟩ : syracuseStep 1838447 = 2757671) B2757671
theorem B7998839 : Blo 483789 7998839 := bstep (se 1 (by rfl) ⟨5999129, by rfl⟩ : syracuseStep 7998839 = 11998259) B11998259
theorem B822649 : Blo 483789 822649 := bstep (se 2 (by rfl) ⟨308493, by rfl⟩ : syracuseStep 822649 = 616987) B616987
theorem B133107313 : Blo 483789 133107313 := bstep (se 2 (by rfl) ⟨49915242, by rfl⟩ : syracuseStep 133107313 = 99830485) B99830485
theorem B2461427 : Blo 483789 2461427 := bstep (se 1 (by rfl) ⟨1846070, by rfl⟩ : syracuseStep 2461427 = 3692141) B3692141
theorem B12161177 : Blo 483789 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B921775 : Blo 483789 921775 := bstep (se 1 (by rfl) ⟨691331, by rfl⟩ : syracuseStep 921775 = 1382663) B1382663
theorem B3936509 : Blo 483789 3936509 := bstep (se 3 (by rfl) ⟨738095, by rfl⟩ : syracuseStep 3936509 = 1476191) B1476191
theorem B7901495 : Blo 483789 7901495 := bstep (se 1 (by rfl) ⟨5926121, by rfl⟩ : syracuseStep 7901495 = 11852243) B11852243
theorem B1643165 : Blo 483789 1643165 := bstep (se 3 (by rfl) ⟨308093, by rfl⟩ : syracuseStep 1643165 = 616187) B616187
theorem B8328095 : Blo 483789 8328095 := bstep (se 1 (by rfl) ⟨6246071, by rfl⟩ : syracuseStep 8328095 = 12492143) B12492143
theorem B725999 : Blo 483789 725999 := bstep (se 1 (by rfl) ⟨544499, by rfl⟩ : syracuseStep 725999 = 1088999) B1088999
theorem B1643705 : Blo 483789 1643705 := bstep (se 2 (by rfl) ⟨616389, by rfl⟩ : syracuseStep 1643705 = 1232779) B1232779
theorem B2364713 : Blo 483789 2364713 := bstep (se 2 (by rfl) ⟨886767, by rfl⟩ : syracuseStep 2364713 = 1773535) B1773535
theorem B726383 : Blo 483789 726383 := bstep (se 1 (by rfl) ⟨544787, by rfl⟩ : syracuseStep 726383 = 1089575) B1089575
theorem B726503 : Blo 483789 726503 := bstep (se 1 (by rfl) ⟨544877, by rfl⟩ : syracuseStep 726503 = 1089755) B1089755
theorem B4134523 : Blo 483789 4134523 := bstep (se 1 (by rfl) ⟨3100892, by rfl⟩ : syracuseStep 4134523 = 6201785) B6201785
theorem B726665 : Blo 483789 726665 := bstep (se 2 (by rfl) ⟨272499, by rfl⟩ : syracuseStep 726665 = 544999) B544999
theorem B726683 : Blo 483789 726683 := bstep (se 1 (by rfl) ⟨545012, by rfl⟩ : syracuseStep 726683 = 1090025) B1090025
theorem B726875 : Blo 483789 726875 := bstep (se 1 (by rfl) ⟨545156, by rfl⟩ : syracuseStep 726875 = 1090313) B1090313
theorem B727259 : Blo 483789 727259 := bstep (se 1 (by rfl) ⟨545444, by rfl⟩ : syracuseStep 727259 = 1090889) B1090889
theorem B3676589 : Blo 483789 3676589 := bstep (se 3 (by rfl) ⟨689360, by rfl⟩ : syracuseStep 3676589 = 1378721) B1378721
theorem B727529 : Blo 483789 727529 := bstep (se 2 (by rfl) ⟨272823, by rfl⟩ : syracuseStep 727529 = 545647) B545647
theorem B1383095 : Blo 483789 1383095 := bstep (se 1 (by rfl) ⟨1037321, by rfl⟩ : syracuseStep 1383095 = 2074643) B2074643
theorem B5675741 : Blo 483789 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B2759447 : Blo 483789 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B727919 : Blo 483789 727919 := bstep (se 1 (by rfl) ⟨545939, by rfl⟩ : syracuseStep 727919 = 1091879) B1091879
theorem B727931 : Blo 483789 727931 := bstep (se 1 (by rfl) ⟨545948, by rfl⟩ : syracuseStep 727931 = 1091897) B1091897
theorem B5905345 : Blo 483789 5905345 := bstep (se 2 (by rfl) ⟨2214504, by rfl⟩ : syracuseStep 5905345 = 4429009) B4429009
theorem B4430983 : Blo 483789 4430983 := bstep (se 1 (by rfl) ⟨3323237, by rfl⟩ : syracuseStep 4430983 = 6646475) B6646475
theorem B1645703 : Blo 483789 1645703 := bstep (se 1 (by rfl) ⟨1234277, by rfl⟩ : syracuseStep 1645703 = 2468555) B2468555
theorem B15802067 : Blo 483789 15802067 := bstep (se 1 (by rfl) ⟨11851550, by rfl⟩ : syracuseStep 15802067 = 23703101) B23703101
theorem B958171 : Blo 483789 958171 := bstep (se 1 (by rfl) ⟨718628, by rfl⟩ : syracuseStep 958171 = 1437257) B1437257
theorem B728795 : Blo 483789 728795 := bstep (se 1 (by rfl) ⟨546596, by rfl⟩ : syracuseStep 728795 = 1093193) B1093193
theorem B1089377 : Blo 483789 1089377 := bstep (se 2 (by rfl) ⟨408516, by rfl⟩ : syracuseStep 1089377 = 817033) B817033
theorem B1089503 : Blo 483789 1089503 := bstep (se 1 (by rfl) ⟨817127, by rfl⟩ : syracuseStep 1089503 = 1634255) B1634255
theorem B925663 : Blo 483789 925663 := bstep (se 1 (by rfl) ⟨694247, by rfl⟩ : syracuseStep 925663 = 1388495) B1388495
theorem B729065 : Blo 483789 729065 := bstep (se 2 (by rfl) ⟨273399, by rfl⟩ : syracuseStep 729065 = 546799) B546799
theorem B1384577 : Blo 483789 1384577 := bstep (se 2 (by rfl) ⟨519216, by rfl⟩ : syracuseStep 1384577 = 1038433) B1038433
theorem B5546231 : Blo 483789 5546231 := bstep (se 1 (by rfl) ⟨4159673, by rfl⟩ : syracuseStep 5546231 = 8319347) B8319347
theorem B1089791 : Blo 483789 1089791 := bstep (se 1 (by rfl) ⟨817343, by rfl⟩ : syracuseStep 1089791 = 1634687) B1634687
theorem B1089953 : Blo 483789 1089953 := bstep (se 2 (by rfl) ⟨408732, by rfl⟩ : syracuseStep 1089953 = 817465) B817465
theorem B1843793 : Blo 483789 1843793 := bstep (se 2 (by rfl) ⟨691422, by rfl⟩ : syracuseStep 1843793 = 1382845) B1382845
theorem B729767 : Blo 483789 729767 := bstep (se 1 (by rfl) ⟨547325, by rfl⟩ : syracuseStep 729767 = 1094651) B1094651
theorem B9118493 : Blo 483789 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B729887 : Blo 483789 729887 := bstep (se 1 (by rfl) ⟨547415, by rfl⟩ : syracuseStep 729887 = 1094831) B1094831
theorem B3679019 : Blo 483789 3679019 := bstep (se 1 (by rfl) ⟨2759264, by rfl⟩ : syracuseStep 3679019 = 5518529) B5518529
theorem B729911 : Blo 483789 729911 := bstep (se 1 (by rfl) ⟨547433, by rfl⟩ : syracuseStep 729911 = 1094867) B1094867
theorem B730091 : Blo 483789 730091 := bstep (se 1 (by rfl) ⟨547568, by rfl⟩ : syracuseStep 730091 = 1095137) B1095137
theorem B1877039 : Blo 483789 1877039 := bstep (se 1 (by rfl) ⟨1407779, by rfl⟩ : syracuseStep 1877039 = 2815559) B2815559
theorem B2073721 : Blo 483789 2073721 := bstep (se 2 (by rfl) ⟨777645, by rfl⟩ : syracuseStep 2073721 = 1555291) B1555291
theorem B1090727 : Blo 483789 1090727 := bstep (se 1 (by rfl) ⟨818045, by rfl⟩ : syracuseStep 1090727 = 1636091) B1636091
theorem B1090835 : Blo 483789 1090835 := bstep (se 1 (by rfl) ⟨818126, by rfl⟩ : syracuseStep 1090835 = 1636253) B1636253
theorem B2762045 : Blo 483789 2762045 := bstep (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) B1035767
theorem B1091465 : Blo 483789 1091465 := bstep (se 2 (by rfl) ⟨409299, by rfl⟩ : syracuseStep 1091465 = 818599) B818599
theorem B1091483 : Blo 483789 1091483 := bstep (se 1 (by rfl) ⟨818612, by rfl⟩ : syracuseStep 1091483 = 1637225) B1637225
theorem B1091519 : Blo 483789 1091519 := bstep (se 1 (by rfl) ⟨818639, by rfl⟩ : syracuseStep 1091519 = 1637279) B1637279
theorem B731183 : Blo 483789 731183 := bstep (se 1 (by rfl) ⟨548387, by rfl⟩ : syracuseStep 731183 = 1096775) B1096775
theorem B1091681 : Blo 483789 1091681 := bstep (se 2 (by rfl) ⟨409380, by rfl⟩ : syracuseStep 1091681 = 818761) B818761
theorem B731447 : Blo 483789 731447 := bstep (se 1 (by rfl) ⟨548585, by rfl⟩ : syracuseStep 731447 = 1097171) B1097171
theorem B731627 : Blo 483789 731627 := bstep (se 1 (by rfl) ⟨548720, by rfl⟩ : syracuseStep 731627 = 1097441) B1097441
theorem B1845767 : Blo 483789 1845767 := bstep (se 1 (by rfl) ⟨1384325, by rfl⟩ : syracuseStep 1845767 = 2768651) B2768651
theorem B1846223 : Blo 483789 1846223 := bstep (se 1 (by rfl) ⟨1384667, by rfl⟩ : syracuseStep 1846223 = 2769335) B2769335
theorem B3746767 : Blo 483789 3746767 := bstep (se 1 (by rfl) ⟨2810075, by rfl⟩ : syracuseStep 3746767 = 5620151) B5620151
theorem B1748233 : Blo 483789 1748233 := bstep (se 2 (by rfl) ⟨655587, by rfl⟩ : syracuseStep 1748233 = 1311175) B1311175
theorem B1093031 : Blo 483789 1093031 := bstep (se 1 (by rfl) ⟨819773, by rfl⟩ : syracuseStep 1093031 = 1639547) B1639547
theorem B1093211 : Blo 483789 1093211 := bstep (se 1 (by rfl) ⟨819908, by rfl⟩ : syracuseStep 1093211 = 1639817) B1639817
theorem B1388279 : Blo 483789 1388279 := bstep (se 1 (by rfl) ⟨1041209, by rfl⟩ : syracuseStep 1388279 = 2082419) B2082419
theorem B2633593 : Blo 483789 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B1093625 : Blo 483789 1093625 := bstep (se 2 (by rfl) ⟨410109, by rfl⟩ : syracuseStep 1093625 = 820219) B820219
theorem B2338895 : Blo 483789 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B1093715 : Blo 483789 1093715 := bstep (se 1 (by rfl) ⟨820286, by rfl⟩ : syracuseStep 1093715 = 1640573) B1640573
theorem B1093895 : Blo 483789 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B1225115 : Blo 483789 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B1094201 : Blo 483789 1094201 := bstep (se 2 (by rfl) ⟨410325, by rfl⟩ : syracuseStep 1094201 = 820651) B820651
theorem B4141631 : Blo 483789 4141631 := bstep (se 1 (by rfl) ⟨3106223, by rfl⟩ : syracuseStep 4141631 = 6212447) B6212447
theorem B1553215 : Blo 483789 1553215 := bstep (se 1 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 1553215 = 2329823) B2329823
theorem B2765735 : Blo 483789 2765735 := bstep (se 1 (by rfl) ⟨2074301, by rfl⟩ : syracuseStep 2765735 = 4148603) B4148603
theorem B1848379 : Blo 483789 1848379 := bstep (se 1 (by rfl) ⟨1386284, by rfl⟩ : syracuseStep 1848379 = 2772569) B2772569
theorem B1094921 : Blo 483789 1094921 := bstep (se 2 (by rfl) ⟨410595, by rfl⟩ : syracuseStep 1094921 = 821191) B821191
theorem B1094975 : Blo 483789 1094975 := bstep (se 1 (by rfl) ⟨821231, by rfl⟩ : syracuseStep 1094975 = 1642463) B1642463
theorem B8271233 : Blo 483789 8271233 := bstep (se 2 (by rfl) ⟨3101712, by rfl⟩ : syracuseStep 8271233 = 6203425) B6203425
theorem B1095083 : Blo 483789 1095083 := bstep (se 1 (by rfl) ⟨821312, by rfl⟩ : syracuseStep 1095083 = 1642625) B1642625
theorem B2078369 : Blo 483789 2078369 := bstep (se 2 (by rfl) ⟨779388, by rfl⟩ : syracuseStep 2078369 = 1558777) B1558777
theorem B2209451 : Blo 483789 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B1095407 : Blo 483789 1095407 := bstep (se 1 (by rfl) ⟨821555, by rfl⟩ : syracuseStep 1095407 = 1643111) B1643111
theorem B1095623 : Blo 483789 1095623 := bstep (se 1 (by rfl) ⟨821717, by rfl⟩ : syracuseStep 1095623 = 1643435) B1643435
theorem B2078729 : Blo 483789 2078729 := bstep (se 2 (by rfl) ⟨779523, by rfl⟩ : syracuseStep 2078729 = 1559047) B1559047
theorem B1095911 : Blo 483789 1095911 := bstep (se 1 (by rfl) ⟨821933, by rfl⟩ : syracuseStep 1095911 = 1643867) B1643867
theorem B1095929 : Blo 483789 1095929 := bstep (se 2 (by rfl) ⟨410973, by rfl⟩ : syracuseStep 1095929 = 821947) B821947
theorem B1095983 : Blo 483789 1095983 := bstep (se 1 (by rfl) ⟨821987, by rfl⟩ : syracuseStep 1095983 = 1643975) B1643975
theorem B3684851 : Blo 483789 3684851 := bstep (se 1 (by rfl) ⟨2763638, by rfl⟩ : syracuseStep 3684851 = 5527277) B5527277
theorem B1227271 : Blo 483789 1227271 := bstep (se 1 (by rfl) ⟨920453, by rfl⟩ : syracuseStep 1227271 = 1840907) B1840907
theorem B1096199 : Blo 483789 1096199 := bstep (se 1 (by rfl) ⟨822149, by rfl⟩ : syracuseStep 1096199 = 1644299) B1644299
theorem B1096379 : Blo 483789 1096379 := bstep (se 1 (by rfl) ⟨822284, by rfl⟩ : syracuseStep 1096379 = 1644569) B1644569
theorem B1555367 : Blo 483789 1555367 := bstep (se 1 (by rfl) ⟨1166525, by rfl⟩ : syracuseStep 1555367 = 2333051) B2333051
theorem B2636711 : Blo 483789 2636711 := bstep (se 1 (by rfl) ⟨1977533, by rfl⟩ : syracuseStep 2636711 = 3955067) B3955067
theorem B1850323 : Blo 483789 1850323 := bstep (se 1 (by rfl) ⟨1387742, by rfl⟩ : syracuseStep 1850323 = 2775485) B2775485
theorem B4209779 : Blo 483789 4209779 := bstep (se 1 (by rfl) ⟨3157334, by rfl⟩ : syracuseStep 4209779 = 6314669) B6314669
theorem B1162471 : Blo 483789 1162471 := bstep (se 1 (by rfl) ⟨871853, by rfl⟩ : syracuseStep 1162471 = 1743707) B1743707
theorem B933289 : Blo 483789 933289 := bstep (se 2 (by rfl) ⟨349983, by rfl⟩ : syracuseStep 933289 = 699967) B699967
theorem B1097279 : Blo 483789 1097279 := bstep (se 1 (by rfl) ⟨822959, by rfl⟩ : syracuseStep 1097279 = 1645919) B1645919
theorem B6209783 : Blo 483789 6209783 := bstep (se 1 (by rfl) ⟨4657337, by rfl⟩ : syracuseStep 6209783 = 9314675) B9314675
theorem B2998781 : Blo 483789 2998781 := bstep (se 3 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 2998781 = 1124543) B1124543
theorem B2343431 : Blo 483789 2343431 := bstep (se 1 (by rfl) ⟨1757573, by rfl⟩ : syracuseStep 2343431 = 3515147) B3515147
theorem B1164623 : Blo 483789 1164623 := bstep (se 1 (by rfl) ⟨873467, by rfl⟩ : syracuseStep 1164623 = 1746935) B1746935
theorem B2082145 : Blo 483789 2082145 := bstep (se 2 (by rfl) ⟨780804, by rfl⟩ : syracuseStep 2082145 = 1561609) B1561609
theorem B1558187 : Blo 483789 1558187 := bstep (se 1 (by rfl) ⟨1168640, by rfl⟩ : syracuseStep 1558187 = 2337281) B2337281
theorem B6244127 : Blo 483789 6244127 := bstep (se 1 (by rfl) ⟨4683095, by rfl⟩ : syracuseStep 6244127 = 9366191) B9366191
theorem B4672025 : Blo 483789 4672025 := bstep (se 2 (by rfl) ⟨1752009, by rfl⟩ : syracuseStep 4672025 = 3504019) B3504019
theorem B1231463 : Blo 483789 1231463 := bstep (se 1 (by rfl) ⟨923597, by rfl⟩ : syracuseStep 1231463 = 1847195) B1847195
theorem B9325367 : Blo 483789 9325367 := bstep (se 1 (by rfl) ⟨6994025, by rfl⟩ : syracuseStep 9325367 = 13988051) B13988051
theorem B936955 : Blo 483789 936955 := bstep (se 1 (by rfl) ⟨702716, by rfl⟩ : syracuseStep 936955 = 1405433) B1405433
theorem B740407 : Blo 483789 740407 := bstep (se 1 (by rfl) ⟨555305, by rfl⟩ : syracuseStep 740407 = 1110611) B1110611
theorem B3656927 : Blo 483789 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B9096425 : Blo 483789 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B1166719 : Blo 483789 1166719 := bstep (se 1 (by rfl) ⟨875039, by rfl⟩ : syracuseStep 1166719 = 1750079) B1750079
theorem B137088385 : Blo 483789 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B9457033 : Blo 483789 9457033 := bstep (se 2 (by rfl) ⟨3546387, by rfl⟩ : syracuseStep 9457033 = 7092775) B7092775
theorem B1559969 : Blo 483789 1559969 := bstep (se 2 (by rfl) ⟨584988, by rfl⟩ : syracuseStep 1559969 = 1169977) B1169977
theorem B544639 : Blo 483789 544639 := bstep (se 1 (by rfl) ⟨408479, by rfl⟩ : syracuseStep 544639 = 816959) B816959
theorem B1167335 : Blo 483789 1167335 := bstep (se 1 (by rfl) ⟨875501, by rfl⟩ : syracuseStep 1167335 = 1751003) B1751003
theorem B1232891 : Blo 483789 1232891 := bstep (se 1 (by rfl) ⟨924668, by rfl⟩ : syracuseStep 1232891 = 1849337) B1849337
theorem B7491685 : Blo 483789 7491685 := bstep (se 4 (by rfl) ⟨702345, by rfl⟩ : syracuseStep 7491685 = 1404691) B1404691
theorem B4149629 : Blo 483789 4149629 := bstep (se 3 (by rfl) ⟨778055, by rfl⟩ : syracuseStep 4149629 = 1556111) B1556111
theorem B545179 : Blo 483789 545179 := bstep (se 1 (by rfl) ⟨408884, by rfl⟩ : syracuseStep 545179 = 817769) B817769
theorem B545863 : Blo 483789 545863 := bstep (se 1 (by rfl) ⟨409397, by rfl⟩ : syracuseStep 545863 = 818795) B818795
theorem B4150379 : Blo 483789 4150379 := bstep (se 1 (by rfl) ⟨3112784, by rfl⟩ : syracuseStep 4150379 = 6225569) B6225569
theorem B1234075 : Blo 483789 1234075 := bstep (se 1 (by rfl) ⟨925556, by rfl⟩ : syracuseStep 1234075 = 1851113) B1851113
theorem B1037519 : Blo 483789 1037519 := bstep (se 1 (by rfl) ⟨778139, by rfl⟩ : syracuseStep 1037519 = 1556279) B1556279
theorem B546043 : Blo 483789 546043 := bstep (se 1 (by rfl) ⟨409532, by rfl⟩ : syracuseStep 546043 = 819065) B819065
theorem B4970317 : Blo 483789 4970317 := bstep (se 3 (by rfl) ⟨931934, by rfl⟩ : syracuseStep 4970317 = 1863869) B1863869
theorem B8869925 : Blo 483789 8869925 := bstep (se 4 (by rfl) ⟨831555, by rfl⟩ : syracuseStep 8869925 = 1663111) B1663111
theorem B3692627 : Blo 483789 3692627 := bstep (se 1 (by rfl) ⟨2769470, by rfl⟩ : syracuseStep 3692627 = 5538941) B5538941
theorem B547231 : Blo 483789 547231 := bstep (se 1 (by rfl) ⟨410423, by rfl⟩ : syracuseStep 547231 = 820847) B820847
theorem B547303 : Blo 483789 547303 := bstep (se 1 (by rfl) ⟨410477, by rfl⟩ : syracuseStep 547303 = 820955) B820955
theorem B4413971 : Blo 483789 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B1039159 : Blo 483789 1039159 := bstep (se 1 (by rfl) ⟨779369, by rfl⟩ : syracuseStep 1039159 = 1558739) B1558739
theorem B548167 : Blo 483789 548167 := bstep (se 1 (by rfl) ⟨411125, by rfl⟩ : syracuseStep 548167 = 822251) B822251
theorem B876251 : Blo 483789 876251 := bstep (se 1 (by rfl) ⟨657188, by rfl⟩ : syracuseStep 876251 = 1314377) B1314377
theorem B2776943 : Blo 483789 2776943 := bstep (se 1 (by rfl) ⟨2082707, by rfl⟩ : syracuseStep 2776943 = 4165415) B4165415
theorem B8314807 : Blo 483789 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B37773317 : Blo 483789 37773317 := bstep (se 4 (by rfl) ⟨3541248, by rfl⟩ : syracuseStep 37773317 = 7082497) B7082497
theorem B778447 : Blo 483789 778447 := bstep (se 1 (by rfl) ⟨583835, by rfl⟩ : syracuseStep 778447 = 1167671) B1167671
theorem B483867 : Blo 483789 483867 := bstep (se 1 (by rfl) ⟨362900, by rfl⟩ : syracuseStep 483867 = 725801) B725801
theorem B483871 : Blo 483789 483871 := bstep (se 1 (by rfl) ⟨362903, by rfl⟩ : syracuseStep 483871 = 725807) B725807
theorem B483951 : Blo 483789 483951 := bstep (se 1 (by rfl) ⟨362963, by rfl⟩ : syracuseStep 483951 = 725927) B725927
theorem B484007 : Blo 483789 484007 := bstep (se 1 (by rfl) ⟨363005, by rfl⟩ : syracuseStep 484007 = 726011) B726011
theorem B484047 : Blo 483789 484047 := bstep (se 1 (by rfl) ⟨363035, by rfl⟩ : syracuseStep 484047 = 726071) B726071
theorem B1041115 : Blo 483789 1041115 := bstep (se 1 (by rfl) ⟨780836, by rfl⟩ : syracuseStep 1041115 = 1561673) B1561673
theorem B484127 : Blo 483789 484127 := bstep (se 1 (by rfl) ⟨363095, by rfl⟩ : syracuseStep 484127 = 726191) B726191
theorem B2450411 : Blo 483789 2450411 := bstep (se 1 (by rfl) ⟨1837808, by rfl⟩ : syracuseStep 2450411 = 3675617) B3675617
theorem B484399 : Blo 483789 484399 := bstep (se 1 (by rfl) ⟨363299, by rfl⟩ : syracuseStep 484399 = 726599) B726599
theorem B484463 : Blo 483789 484463 := bstep (se 1 (by rfl) ⟨363347, by rfl⟩ : syracuseStep 484463 = 726695) B726695
theorem B484519 : Blo 483789 484519 := bstep (se 1 (by rfl) ⟨363389, by rfl⟩ : syracuseStep 484519 = 726779) B726779
theorem B484543 : Blo 483789 484543 := bstep (se 1 (by rfl) ⟨363407, by rfl⟩ : syracuseStep 484543 = 726815) B726815
theorem B196338887 : Blo 483789 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B484575 : Blo 483789 484575 := bstep (se 1 (by rfl) ⟨363431, by rfl⟩ : syracuseStep 484575 = 726863) B726863
theorem B484655 : Blo 483789 484655 := bstep (se 1 (by rfl) ⟨363491, by rfl⟩ : syracuseStep 484655 = 726983) B726983
theorem B4154753 : Blo 483789 4154753 := bstep (se 2 (by rfl) ⟨1558032, by rfl⟩ : syracuseStep 4154753 = 3116065) B3116065
theorem B484891 : Blo 483789 484891 := bstep (se 1 (by rfl) ⟨363668, by rfl⟩ : syracuseStep 484891 = 727337) B727337
theorem B484895 : Blo 483789 484895 := bstep (se 1 (by rfl) ⟨363671, by rfl⟩ : syracuseStep 484895 = 727343) B727343
theorem B485055 : Blo 483789 485055 := bstep (se 1 (by rfl) ⟨363791, by rfl⟩ : syracuseStep 485055 = 727583) B727583
theorem B485311 : Blo 483789 485311 := bstep (se 1 (by rfl) ⟨363983, by rfl⟩ : syracuseStep 485311 = 727967) B727967
theorem B485343 : Blo 483789 485343 := bstep (se 1 (by rfl) ⟨364007, by rfl⟩ : syracuseStep 485343 = 728015) B728015
theorem B485403 : Blo 483789 485403 := bstep (se 1 (by rfl) ⟨364052, by rfl⟩ : syracuseStep 485403 = 728105) B728105
theorem B485407 : Blo 483789 485407 := bstep (se 1 (by rfl) ⟨364055, by rfl⟩ : syracuseStep 485407 = 728111) B728111
theorem B485423 : Blo 483789 485423 := bstep (se 1 (by rfl) ⟨364067, by rfl⟩ : syracuseStep 485423 = 728135) B728135
theorem B9332819 : Blo 483789 9332819 := bstep (se 1 (by rfl) ⟨6999614, by rfl⟩ : syracuseStep 9332819 = 13999229) B13999229
theorem B8284355 : Blo 483789 8284355 := bstep (se 1 (by rfl) ⟨6213266, by rfl⟩ : syracuseStep 8284355 = 12426533) B12426533
theorem B485599 : Blo 483789 485599 := bstep (se 1 (by rfl) ⟨364199, by rfl⟩ : syracuseStep 485599 = 728399) B728399
theorem B485659 : Blo 483789 485659 := bstep (se 1 (by rfl) ⟨364244, by rfl⟩ : syracuseStep 485659 = 728489) B728489
theorem B485759 : Blo 483789 485759 := bstep (se 1 (by rfl) ⟨364319, by rfl⟩ : syracuseStep 485759 = 728639) B728639
theorem B485935 : Blo 483789 485935 := bstep (se 1 (by rfl) ⟨364451, by rfl⟩ : syracuseStep 485935 = 728903) B728903
theorem B9431639 : Blo 483789 9431639 := bstep (se 1 (by rfl) ⟨7073729, by rfl⟩ : syracuseStep 9431639 = 14147459) B14147459
theorem B485991 : Blo 483789 485991 := bstep (se 1 (by rfl) ⟨364493, by rfl⟩ : syracuseStep 485991 = 728987) B728987
theorem B9431801 : Blo 483789 9431801 := bstep (se 2 (by rfl) ⟨3536925, by rfl⟩ : syracuseStep 9431801 = 7073851) B7073851
theorem B486367 : Blo 483789 486367 := bstep (se 1 (by rfl) ⟨364775, by rfl⟩ : syracuseStep 486367 = 729551) B729551
theorem B486395 : Blo 483789 486395 := bstep (se 1 (by rfl) ⟨364796, by rfl⟩ : syracuseStep 486395 = 729593) B729593
theorem B486463 : Blo 483789 486463 := bstep (se 1 (by rfl) ⟨364847, by rfl⟩ : syracuseStep 486463 = 729695) B729695
theorem B486783 : Blo 483789 486783 := bstep (se 1 (by rfl) ⟨365087, by rfl⟩ : syracuseStep 486783 = 730175) B730175
theorem B486811 : Blo 483789 486811 := bstep (se 1 (by rfl) ⟨365108, by rfl⟩ : syracuseStep 486811 = 730217) B730217
theorem B486879 : Blo 483789 486879 := bstep (se 1 (by rfl) ⟨365159, by rfl⟩ : syracuseStep 486879 = 730319) B730319
theorem B487015 : Blo 483789 487015 := bstep (se 1 (by rfl) ⟨365261, by rfl⟩ : syracuseStep 487015 = 730523) B730523
theorem B487163 : Blo 483789 487163 := bstep (se 1 (by rfl) ⟨365372, by rfl⟩ : syracuseStep 487163 = 730745) B730745
theorem B487231 : Blo 483789 487231 := bstep (se 1 (by rfl) ⟨365423, by rfl⟩ : syracuseStep 487231 = 730847) B730847
theorem B487295 : Blo 483789 487295 := bstep (se 1 (by rfl) ⟨365471, by rfl⟩ : syracuseStep 487295 = 730943) B730943
theorem B487407 : Blo 483789 487407 := bstep (se 1 (by rfl) ⟨365555, by rfl⟩ : syracuseStep 487407 = 731111) B731111
theorem B487419 : Blo 483789 487419 := bstep (se 1 (by rfl) ⟨365564, by rfl⟩ : syracuseStep 487419 = 731129) B731129
theorem B487487 : Blo 483789 487487 := bstep (se 1 (by rfl) ⟨365615, by rfl⟩ : syracuseStep 487487 = 731231) B731231
theorem B487527 : Blo 483789 487527 := bstep (se 1 (by rfl) ⟨365645, by rfl⟩ : syracuseStep 487527 = 731291) B731291
theorem B487551 : Blo 483789 487551 := bstep (se 1 (by rfl) ⟨365663, by rfl⟩ : syracuseStep 487551 = 731327) B731327
theorem B487579 : Blo 483789 487579 := bstep (se 1 (by rfl) ⟨365684, by rfl⟩ : syracuseStep 487579 = 731369) B731369
theorem B2224361 : Blo 483789 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B1241351 : Blo 483789 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B2224487 : Blo 483789 2224487 := bstep (se 1 (by rfl) ⟨1668365, by rfl⟩ : syracuseStep 2224487 = 3336731) B3336731
theorem B487783 : Blo 483789 487783 := bstep (se 1 (by rfl) ⟨365837, by rfl⟩ : syracuseStep 487783 = 731675) B731675
theorem B2453975 : Blo 483789 2453975 := bstep (se 1 (by rfl) ⟨1840481, by rfl⟩ : syracuseStep 2453975 = 3680963) B3680963
theorem B6910951 : Blo 483789 6910951 := bstep (se 1 (by rfl) ⟨5183213, by rfl⟩ : syracuseStep 6910951 = 10366427) B10366427
theorem B817067 : Blo 483789 817067 := bstep (se 1 (by rfl) ⟨612800, by rfl⟩ : syracuseStep 817067 = 1225601) B1225601
theorem B15759521 : Blo 483789 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B817607 : Blo 483789 817607 := bstep (se 1 (by rfl) ⟨613205, by rfl⟩ : syracuseStep 817607 = 1226411) B1226411
theorem B2652763 : Blo 483789 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B1636955 : Blo 483789 1636955 := bstep (se 1 (by rfl) ⟨1227716, by rfl⟩ : syracuseStep 1636955 = 2455433) B2455433
theorem B817823 : Blo 483789 817823 := bstep (se 1 (by rfl) ⟨613367, by rfl⟩ : syracuseStep 817823 = 1226735) B1226735
theorem B817897 : Blo 483789 817897 := bstep (se 2 (by rfl) ⟨306711, by rfl⟩ : syracuseStep 817897 = 613423) B613423
theorem B7502777 : Blo 483789 7502777 := bstep (se 2 (by rfl) ⟨2813541, by rfl⟩ : syracuseStep 7502777 = 5627083) B5627083
theorem B1637657 : Blo 483789 1637657 := bstep (se 2 (by rfl) ⟨614121, by rfl⟩ : syracuseStep 1637657 = 1228243) B1228243
theorem B37715705 : Blo 483789 37715705 := bstep (se 2 (by rfl) ⟨14143389, by rfl⟩ : syracuseStep 37715705 = 28286779) B28286779
theorem B1999187 : Blo 483789 1999187 := bstep (se 1 (by rfl) ⟨1499390, by rfl⟩ : syracuseStep 1999187 = 2998781) B2998781
theorem B4162751 : Blo 483789 4162751 := bstep (se 1 (by rfl) ⟨3122063, by rfl⟩ : syracuseStep 4162751 = 6244127) B6244127
theorem B3114683 : Blo 483789 3114683 := bstep (se 1 (by rfl) ⟨2336012, by rfl⟩ : syracuseStep 3114683 = 4672025) B4672025
theorem B820975 : Blo 483789 820975 := bstep (se 1 (by rfl) ⟨615731, by rfl⟩ : syracuseStep 820975 = 1231463) B1231463
theorem B1640411 : Blo 483789 1640411 := bstep (se 1 (by rfl) ⟨1230308, by rfl⟩ : syracuseStep 1640411 = 2460617) B2460617
theorem B1640519 : Blo 483789 1640519 := bstep (se 1 (by rfl) ⟨1230389, by rfl⟩ : syracuseStep 1640519 = 2460779) B2460779
theorem B6064283 : Blo 483789 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B1640951 : Blo 483789 1640951 := bstep (se 1 (by rfl) ⟨1230713, by rfl⟩ : syracuseStep 1640951 = 2461427) B2461427
theorem B821927 : Blo 483789 821927 := bstep (se 1 (by rfl) ⟨616445, by rfl⟩ : syracuseStep 821927 = 1232891) B1232891
theorem B2624339 : Blo 483789 2624339 := bstep (se 1 (by rfl) ⟨1968254, by rfl⟩ : syracuseStep 2624339 = 3936509) B3936509
theorem B2755529 : Blo 483789 2755529 := bstep (se 2 (by rfl) ⟨1033323, by rfl⟩ : syracuseStep 2755529 = 2066647) B2066647
theorem B691679 : Blo 483789 691679 := bstep (se 1 (by rfl) ⟨518759, by rfl⟩ : syracuseStep 691679 = 1037519) B1037519
theorem B1576475 : Blo 483789 1576475 := bstep (se 1 (by rfl) ⟨1182356, by rfl⟩ : syracuseStep 1576475 = 2364713) B2364713
theorem B921593 : Blo 483789 921593 := bstep (se 2 (by rfl) ⟨345597, by rfl⟩ : syracuseStep 921593 = 691195) B691195
theorem B1249273 : Blo 483789 1249273 := bstep (se 2 (by rfl) ⟨468477, by rfl⟩ : syracuseStep 1249273 = 936955) B936955
theorem B2461751 : Blo 483789 2461751 := bstep (se 1 (by rfl) ⟨1846313, by rfl⟩ : syracuseStep 2461751 = 3692627) B3692627
theorem B987209 : Blo 483789 987209 := bstep (se 2 (by rfl) ⟨370203, by rfl⟩ : syracuseStep 987209 = 740407) B740407
theorem B2330977 : Blo 483789 2330977 := bstep (se 2 (by rfl) ⟨874116, by rfl⟩ : syracuseStep 2330977 = 1748233) B1748233
theorem B1839631 : Blo 483789 1839631 := bstep (se 1 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 1839631 = 2759447) B2759447
theorem B177476417 : Blo 483789 177476417 := bstep (se 2 (by rfl) ⟨66553656, by rfl⟩ : syracuseStep 177476417 = 133107313) B133107313
theorem B3511457 : Blo 483789 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B726185 : Blo 483789 726185 := bstep (se 2 (by rfl) ⟨272319, by rfl⟩ : syracuseStep 726185 = 544639) B544639
theorem B726251 : Blo 483789 726251 := bstep (se 1 (by rfl) ⟨544688, by rfl⟩ : syracuseStep 726251 = 1089377) B1089377
theorem B726335 : Blo 483789 726335 := bstep (se 1 (by rfl) ⟨544751, by rfl⟩ : syracuseStep 726335 = 1089503) B1089503
theorem B923051 : Blo 483789 923051 := bstep (se 1 (by rfl) ⟨692288, by rfl⟩ : syracuseStep 923051 = 1384577) B1384577
theorem B726527 : Blo 483789 726527 := bstep (se 1 (by rfl) ⟨544895, by rfl⟩ : syracuseStep 726527 = 1089791) B1089791
theorem B726635 : Blo 483789 726635 := bstep (se 1 (by rfl) ⟨544976, by rfl⟩ : syracuseStep 726635 = 1089953) B1089953
theorem B726905 : Blo 483789 726905 := bstep (se 2 (by rfl) ⟨272589, by rfl⟩ : syracuseStep 726905 = 545179) B545179
theorem B1251359 : Blo 483789 1251359 := bstep (se 1 (by rfl) ⟨938519, by rfl⟩ : syracuseStep 1251359 = 1877039) B1877039
theorem B727151 : Blo 483789 727151 := bstep (se 1 (by rfl) ⟨545363, by rfl⟩ : syracuseStep 727151 = 1090727) B1090727
theorem B727223 : Blo 483789 727223 := bstep (se 1 (by rfl) ⟨545417, by rfl⟩ : syracuseStep 727223 = 1090835) B1090835
theorem B1841363 : Blo 483789 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B2070953 : Blo 483789 2070953 := bstep (se 2 (by rfl) ⟨776607, by rfl⟩ : syracuseStep 2070953 = 1553215) B1553215
theorem B727643 : Blo 483789 727643 := bstep (se 1 (by rfl) ⟨545732, by rfl⟩ : syracuseStep 727643 = 1091465) B1091465
theorem B727655 : Blo 483789 727655 := bstep (se 1 (by rfl) ⟨545741, by rfl⟩ : syracuseStep 727655 = 1091483) B1091483
theorem B727679 : Blo 483789 727679 := bstep (se 1 (by rfl) ⟨545759, by rfl⟩ : syracuseStep 727679 = 1091519) B1091519
theorem B11770589 : Blo 483789 11770589 := bstep (se 3 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 11770589 = 4413971) B4413971
theorem B727787 : Blo 483789 727787 := bstep (se 1 (by rfl) ⟨545840, by rfl⟩ : syracuseStep 727787 = 1091681) B1091681
theorem B2464505 : Blo 483789 2464505 := bstep (se 2 (by rfl) ⟨924189, by rfl⟩ : syracuseStep 2464505 = 1848379) B1848379
theorem B727817 : Blo 483789 727817 := bstep (se 2 (by rfl) ⟨272931, by rfl⟩ : syracuseStep 727817 = 545863) B545863
theorem B1645433 : Blo 483789 1645433 := bstep (se 2 (by rfl) ⟨617037, by rfl⟩ : syracuseStep 1645433 = 1234075) B1234075
theorem B728057 : Blo 483789 728057 := bstep (se 2 (by rfl) ⟨273021, by rfl⟩ : syracuseStep 728057 = 546043) B546043
theorem B5512697 : Blo 483789 5512697 := bstep (se 2 (by rfl) ⟨2067261, by rfl⟩ : syracuseStep 5512697 = 4134523) B4134523
theorem B728687 : Blo 483789 728687 := bstep (se 1 (by rfl) ⟨546515, by rfl⟩ : syracuseStep 728687 = 1093031) B1093031
theorem B728807 : Blo 483789 728807 := bstep (se 1 (by rfl) ⟨546605, by rfl⟩ : syracuseStep 728807 = 1093211) B1093211
theorem B6627089 : Blo 483789 6627089 := bstep (se 2 (by rfl) ⟨2485158, by rfl⟩ : syracuseStep 6627089 = 4970317) B4970317
theorem B925519 : Blo 483789 925519 := bstep (se 1 (by rfl) ⟨694139, by rfl⟩ : syracuseStep 925519 = 1388279) B1388279
theorem B729083 : Blo 483789 729083 := bstep (se 1 (by rfl) ⟨546812, by rfl⟩ : syracuseStep 729083 = 1093625) B1093625
theorem B2924552213 : Blo 483789 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B729143 : Blo 483789 729143 := bstep (se 1 (by rfl) ⟨546857, by rfl⟩ : syracuseStep 729143 = 1093715) B1093715
theorem B1482907 : Blo 483789 1482907 := bstep (se 1 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 1482907 = 2224361) B2224361
theorem B827567 : Blo 483789 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B729263 : Blo 483789 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B1482991 : Blo 483789 1482991 := bstep (se 1 (by rfl) ⟨1112243, by rfl⟩ : syracuseStep 1482991 = 2224487) B2224487
theorem B729467 : Blo 483789 729467 := bstep (se 1 (by rfl) ⟨547100, by rfl⟩ : syracuseStep 729467 = 1094201) B1094201
theorem B2761087 : Blo 483789 2761087 := bstep (se 1 (by rfl) ⟨2070815, by rfl⟩ : syracuseStep 2761087 = 4141631) B4141631
theorem B729641 : Blo 483789 729641 := bstep (se 2 (by rfl) ⟨273615, by rfl⟩ : syracuseStep 729641 = 547231) B547231
theorem B1843823 : Blo 483789 1843823 := bstep (se 1 (by rfl) ⟨1382867, by rfl⟩ : syracuseStep 1843823 = 2765735) B2765735
theorem B729737 : Blo 483789 729737 := bstep (se 2 (by rfl) ⟨273651, by rfl⟩ : syracuseStep 729737 = 547303) B547303
theorem B729947 : Blo 483789 729947 := bstep (se 1 (by rfl) ⟨547460, by rfl⟩ : syracuseStep 729947 = 1094921) B1094921
theorem B729983 : Blo 483789 729983 := bstep (se 1 (by rfl) ⟨547487, by rfl⟩ : syracuseStep 729983 = 1094975) B1094975
theorem B5514155 : Blo 483789 5514155 := bstep (se 1 (by rfl) ⟨4135616, by rfl⟩ : syracuseStep 5514155 = 8271233) B8271233
theorem B730055 : Blo 483789 730055 := bstep (se 1 (by rfl) ⟨547541, by rfl⟩ : syracuseStep 730055 = 1095083) B1095083
theorem B1090529 : Blo 483789 1090529 := bstep (se 2 (by rfl) ⟨408948, by rfl⟩ : syracuseStep 1090529 = 817897) B817897
theorem B1385545 : Blo 483789 1385545 := bstep (se 2 (by rfl) ⟨519579, by rfl⟩ : syracuseStep 1385545 = 1039159) B1039159
theorem B1385579 : Blo 483789 1385579 := bstep (se 1 (by rfl) ⟨1039184, by rfl⟩ : syracuseStep 1385579 = 2078369) B2078369
theorem B730271 : Blo 483789 730271 := bstep (se 1 (by rfl) ⟨547703, by rfl⟩ : syracuseStep 730271 = 1095407) B1095407
theorem B7873793 : Blo 483789 7873793 := bstep (se 2 (by rfl) ⟨2952672, by rfl⟩ : syracuseStep 7873793 = 5905345) B5905345
theorem B2467097 : Blo 483789 2467097 := bstep (se 2 (by rfl) ⟨925161, by rfl⟩ : syracuseStep 2467097 = 1850323) B1850323
theorem B730415 : Blo 483789 730415 := bstep (se 1 (by rfl) ⟨547811, by rfl⟩ : syracuseStep 730415 = 1095623) B1095623
theorem B1385819 : Blo 483789 1385819 := bstep (se 1 (by rfl) ⟨1039364, by rfl⟩ : syracuseStep 1385819 = 2078729) B2078729
theorem B730607 : Blo 483789 730607 := bstep (se 1 (by rfl) ⟨547955, by rfl⟩ : syracuseStep 730607 = 1095911) B1095911
theorem B730619 : Blo 483789 730619 := bstep (se 1 (by rfl) ⟨547964, by rfl⟩ : syracuseStep 730619 = 1095929) B1095929
theorem B5907977 : Blo 483789 5907977 := bstep (se 2 (by rfl) ⟨2215491, by rfl⟩ : syracuseStep 5907977 = 4430983) B4430983
theorem B730655 : Blo 483789 730655 := bstep (se 1 (by rfl) ⟨547991, by rfl⟩ : syracuseStep 730655 = 1095983) B1095983
theorem B1549961 : Blo 483789 1549961 := bstep (se 2 (by rfl) ⟨581235, by rfl⟩ : syracuseStep 1549961 = 1162471) B1162471
theorem B730799 : Blo 483789 730799 := bstep (se 1 (by rfl) ⟨548099, by rfl⟩ : syracuseStep 730799 = 1096199) B1096199
theorem B1091303 : Blo 483789 1091303 := bstep (se 1 (by rfl) ⟨818477, by rfl⟩ : syracuseStep 1091303 = 1636955) B1636955
theorem B730889 : Blo 483789 730889 := bstep (se 2 (by rfl) ⟨274083, by rfl⟩ : syracuseStep 730889 = 548167) B548167
theorem B730919 : Blo 483789 730919 := bstep (se 1 (by rfl) ⟨548189, by rfl⟩ : syracuseStep 730919 = 1096379) B1096379
theorem B147433621 : Blo 483789 147433621 := bstep (se 6 (by rfl) ⟨3455475, by rfl⟩ : syracuseStep 147433621 = 6910951) B6910951
theorem B1091771 : Blo 483789 1091771 := bstep (se 1 (by rfl) ⟨818828, by rfl⟩ : syracuseStep 1091771 = 1637657) B1637657
theorem B731519 : Blo 483789 731519 := bstep (se 1 (by rfl) ⟨548639, by rfl⟩ : syracuseStep 731519 = 1097279) B1097279
theorem B25143803 : Blo 483789 25143803 := bstep (se 1 (by rfl) ⟨18857852, by rfl⟩ : syracuseStep 25143803 = 37715705) B37715705
theorem B11086409 : Blo 483789 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B4139855 : Blo 483789 4139855 := bstep (se 1 (by rfl) ⟨3104891, by rfl⟩ : syracuseStep 4139855 = 6209783) B6209783
theorem B895943 : Blo 483789 895943 := bstep (se 1 (by rfl) ⟨671957, by rfl⟩ : syracuseStep 895943 = 1343915) B1343915
theorem B1092671 : Blo 483789 1092671 := bstep (se 1 (by rfl) ⟨819503, by rfl⟩ : syracuseStep 1092671 = 1639007) B1639007
theorem B2469203 : Blo 483789 2469203 := bstep (se 1 (by rfl) ⟨1851902, by rfl⟩ : syracuseStep 2469203 = 3703805) B3703805
theorem B1388153 : Blo 483789 1388153 := bstep (se 2 (by rfl) ⟨520557, by rfl⟩ : syracuseStep 1388153 = 1041115) B1041115
theorem B831343 : Blo 483789 831343 := bstep (se 1 (by rfl) ⟨623507, by rfl⟩ : syracuseStep 831343 = 1247015) B1247015
theorem B1093499 : Blo 483789 1093499 := bstep (se 1 (by rfl) ⟨820124, by rfl⟩ : syracuseStep 1093499 = 1640249) B1640249
theorem B2764961 : Blo 483789 2764961 := bstep (se 2 (by rfl) ⟨1036860, by rfl⟩ : syracuseStep 2764961 = 2073721) B2073721
theorem B2437951 : Blo 483789 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B1225631 : Blo 483789 1225631 := bstep (se 1 (by rfl) ⟨919223, by rfl⟩ : syracuseStep 1225631 = 1838447) B1838447
theorem B8107451 : Blo 483789 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B2766419 : Blo 483789 2766419 := bstep (se 1 (by rfl) ⟨2074814, by rfl⟩ : syracuseStep 2766419 = 4149629) B4149629
theorem B1095443 : Blo 483789 1095443 := bstep (se 1 (by rfl) ⟨821582, by rfl⟩ : syracuseStep 1095443 = 1643165) B1643165
theorem B5552063 : Blo 483789 5552063 := bstep (se 1 (by rfl) ⟨4164047, by rfl⟩ : syracuseStep 5552063 = 8328095) B8328095
theorem B2766919 : Blo 483789 2766919 := bstep (se 1 (by rfl) ⟨2075189, by rfl⟩ : syracuseStep 2766919 = 4150379) B4150379
theorem B1095803 : Blo 483789 1095803 := bstep (se 1 (by rfl) ⟨821852, by rfl⟩ : syracuseStep 1095803 = 1643705) B1643705
theorem B1096073 : Blo 483789 1096073 := bstep (se 2 (by rfl) ⟨411027, by rfl⟩ : syracuseStep 1096073 = 822055) B822055
theorem B4995689 : Blo 483789 4995689 := bstep (se 2 (by rfl) ⟨1873383, by rfl⟩ : syracuseStep 4995689 = 3746767) B3746767
theorem B5913283 : Blo 483789 5913283 := bstep (se 1 (by rfl) ⟨4434962, by rfl⟩ : syracuseStep 5913283 = 8869925) B8869925
theorem B1096505 : Blo 483789 1096505 := bstep (se 2 (by rfl) ⟨411189, by rfl⟩ : syracuseStep 1096505 = 822379) B822379
theorem B3783827 : Blo 483789 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B1096865 : Blo 483789 1096865 := bstep (se 2 (by rfl) ⟨411324, by rfl⟩ : syracuseStep 1096865 = 822649) B822649
theorem B1555625 : Blo 483789 1555625 := bstep (se 2 (by rfl) ⟨583359, by rfl⟩ : syracuseStep 1555625 = 1166719) B1166719
theorem B1097135 : Blo 483789 1097135 := bstep (se 1 (by rfl) ⟨822851, by rfl⟩ : syracuseStep 1097135 = 1645703) B1645703
theorem B10534711 : Blo 483789 10534711 := bstep (se 1 (by rfl) ⟨7901033, by rfl⟩ : syracuseStep 10534711 = 15802067) B15802067
theorem B1851295 : Blo 483789 1851295 := bstep (se 1 (by rfl) ⟨1388471, by rfl⟩ : syracuseStep 1851295 = 2776943) B2776943
theorem B25182211 : Blo 483789 25182211 := bstep (se 1 (by rfl) ⟨18886658, by rfl⟩ : syracuseStep 25182211 = 37773317) B37773317
theorem B1229033 : Blo 483789 1229033 := bstep (se 2 (by rfl) ⟨460887, by rfl⟩ : syracuseStep 1229033 = 921775) B921775
theorem B1229195 : Blo 483789 1229195 := bstep (se 1 (by rfl) ⟨921896, by rfl⟩ : syracuseStep 1229195 = 1843793) B1843793
theorem B6078995 : Blo 483789 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B130892591 : Blo 483789 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B2769835 : Blo 483789 2769835 := bstep (se 1 (by rfl) ⟨2077376, by rfl⟩ : syracuseStep 2769835 = 4154753) B4154753
theorem B5522903 : Blo 483789 5522903 := bstep (se 1 (by rfl) ⟨4142177, by rfl⟩ : syracuseStep 5522903 = 8284355) B8284355
theorem B1230511 : Blo 483789 1230511 := bstep (se 1 (by rfl) ⟨922883, by rfl⟩ : syracuseStep 1230511 = 1845767) B1845767
theorem B3688253 : Blo 483789 3688253 := bstep (se 3 (by rfl) ⟨691547, by rfl⟩ : syracuseStep 3688253 = 1383095) B1383095
theorem B1230815 : Blo 483789 1230815 := bstep (se 1 (by rfl) ⟨923111, by rfl⟩ : syracuseStep 1230815 = 1846223) B1846223
theorem B4147645 : Blo 483789 4147645 := bstep (se 3 (by rfl) ⟨777683, by rfl⟩ : syracuseStep 4147645 = 1555367) B1555367
theorem B1559263 : Blo 483789 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B11226077 : Blo 483789 11226077 := bstep (se 3 (by rfl) ⟨2104889, by rfl⟩ : syracuseStep 11226077 = 4209779) B4209779
theorem B544711 : Blo 483789 544711 := bstep (se 1 (by rfl) ⟨408533, by rfl⟩ : syracuseStep 544711 = 817067) B817067
theorem B10506347 : Blo 483789 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B545071 : Blo 483789 545071 := bstep (se 1 (by rfl) ⟨408803, by rfl⟩ : syracuseStep 545071 = 817607) B817607
theorem B545215 : Blo 483789 545215 := bstep (se 1 (by rfl) ⟨408911, by rfl⟩ : syracuseStep 545215 = 817823) B817823
theorem B1757807 : Blo 483789 1757807 := bstep (se 1 (by rfl) ⟨1318355, by rfl⟩ : syracuseStep 1757807 = 2636711) B2636711
theorem B5001851 : Blo 483789 5001851 := bstep (se 1 (by rfl) ⟨3751388, by rfl⟩ : syracuseStep 5001851 = 7502777) B7502777
theorem B1234217 : Blo 483789 1234217 := bstep (se 2 (by rfl) ⟨462831, by rfl⟩ : syracuseStep 1234217 = 925663) B925663
theorem B1037929 : Blo 483789 1037929 := bstep (se 2 (by rfl) ⟨389223, by rfl⟩ : syracuseStep 1037929 = 778447) B778447
theorem B546943 : Blo 483789 546943 := bstep (se 1 (by rfl) ⟨410207, by rfl⟩ : syracuseStep 546943 = 820415) B820415
theorem B1038791 : Blo 483789 1038791 := bstep (se 1 (by rfl) ⟨779093, by rfl⟩ : syracuseStep 1038791 = 1558187) B1558187
theorem B6249149 : Blo 483789 6249149 := bstep (se 3 (by rfl) ⟨1171715, by rfl⟩ : syracuseStep 6249149 = 2343431) B2343431
theorem B547519 : Blo 483789 547519 := bstep (se 1 (by rfl) ⟨410639, by rfl⟩ : syracuseStep 547519 = 821279) B821279
theorem B3103559 : Blo 483789 3103559 := bstep (se 1 (by rfl) ⟨2327669, by rfl⟩ : syracuseStep 3103559 = 4655339) B4655339
theorem B2776193 : Blo 483789 2776193 := bstep (se 2 (by rfl) ⟨1041072, by rfl⟩ : syracuseStep 2776193 = 2082145) B2082145
theorem B6216911 : Blo 483789 6216911 := bstep (se 1 (by rfl) ⟨4662683, by rfl⟩ : syracuseStep 6216911 = 9325367) B9325367
theorem B5332559 : Blo 483789 5332559 := bstep (se 1 (by rfl) ⟨3999419, by rfl⟩ : syracuseStep 5332559 = 7998839) B7998839
theorem B1039979 : Blo 483789 1039979 := bstep (se 1 (by rfl) ⟨779984, by rfl⟩ : syracuseStep 1039979 = 1559969) B1559969
theorem B778223 : Blo 483789 778223 := bstep (se 1 (by rfl) ⟨583667, by rfl⟩ : syracuseStep 778223 = 1167335) B1167335
theorem B5267663 : Blo 483789 5267663 := bstep (se 1 (by rfl) ⟨3950747, by rfl⟩ : syracuseStep 5267663 = 7901495) B7901495
theorem B483999 : Blo 483789 483999 := bstep (se 1 (by rfl) ⟨362999, by rfl⟩ : syracuseStep 483999 = 725999) B725999
theorem B3105661 : Blo 483789 3105661 := bstep (se 3 (by rfl) ⟨582311, by rfl⟩ : syracuseStep 3105661 = 1164623) B1164623
theorem B484255 : Blo 483789 484255 := bstep (se 1 (by rfl) ⟨363191, by rfl⟩ : syracuseStep 484255 = 726383) B726383
theorem B484335 : Blo 483789 484335 := bstep (se 1 (by rfl) ⟨363251, by rfl⟩ : syracuseStep 484335 = 726503) B726503
theorem B484443 : Blo 483789 484443 := bstep (se 1 (by rfl) ⟨363332, by rfl⟩ : syracuseStep 484443 = 726665) B726665
theorem B484455 : Blo 483789 484455 := bstep (se 1 (by rfl) ⟨363341, by rfl⟩ : syracuseStep 484455 = 726683) B726683
theorem B484583 : Blo 483789 484583 := bstep (se 1 (by rfl) ⟨363437, by rfl⟩ : syracuseStep 484583 = 726875) B726875
theorem B484839 : Blo 483789 484839 := bstep (se 1 (by rfl) ⟨363629, by rfl⟩ : syracuseStep 484839 = 727259) B727259
theorem B2451059 : Blo 483789 2451059 := bstep (se 1 (by rfl) ⟨1838294, by rfl⟩ : syracuseStep 2451059 = 3676589) B3676589
theorem B485019 : Blo 483789 485019 := bstep (se 1 (by rfl) ⟨363764, by rfl⟩ : syracuseStep 485019 = 727529) B727529
theorem B5891869 : Blo 483789 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B12609377 : Blo 483789 12609377 := bstep (se 2 (by rfl) ⟨4728516, by rfl⟩ : syracuseStep 12609377 = 9457033) B9457033
theorem B485279 : Blo 483789 485279 := bstep (se 1 (by rfl) ⟨363959, by rfl⟩ : syracuseStep 485279 = 727919) B727919
theorem B485287 : Blo 483789 485287 := bstep (se 1 (by rfl) ⟨363965, by rfl⟩ : syracuseStep 485287 = 727931) B727931
theorem B485863 : Blo 483789 485863 := bstep (se 1 (by rfl) ⟨364397, by rfl⟩ : syracuseStep 485863 = 728795) B728795
theorem B584167 : Blo 483789 584167 := bstep (se 1 (by rfl) ⟨438125, by rfl⟩ : syracuseStep 584167 = 876251) B876251
theorem B486043 : Blo 483789 486043 := bstep (se 1 (by rfl) ⟨364532, by rfl⟩ : syracuseStep 486043 = 729065) B729065
theorem B9988913 : Blo 483789 9988913 := bstep (se 2 (by rfl) ⟨3745842, by rfl⟩ : syracuseStep 9988913 = 7491685) B7491685
theorem B3697487 : Blo 483789 3697487 := bstep (se 1 (by rfl) ⟨2773115, by rfl⟩ : syracuseStep 3697487 = 5546231) B5546231
theorem B486511 : Blo 483789 486511 := bstep (se 1 (by rfl) ⟨364883, by rfl⟩ : syracuseStep 486511 = 729767) B729767
theorem B486591 : Blo 483789 486591 := bstep (se 1 (by rfl) ⟨364943, by rfl⟩ : syracuseStep 486591 = 729887) B729887
theorem B2452679 : Blo 483789 2452679 := bstep (se 1 (by rfl) ⟨1839509, by rfl⟩ : syracuseStep 2452679 = 3679019) B3679019
theorem B486607 : Blo 483789 486607 := bstep (se 1 (by rfl) ⟨364955, by rfl⟩ : syracuseStep 486607 = 729911) B729911
theorem B1633607 : Blo 483789 1633607 := bstep (se 1 (by rfl) ⟨1225205, by rfl⟩ : syracuseStep 1633607 = 2450411) B2450411
theorem B486727 : Blo 483789 486727 := bstep (se 1 (by rfl) ⟨365045, by rfl⟩ : syracuseStep 486727 = 730091) B730091
theorem B487455 : Blo 483789 487455 := bstep (se 1 (by rfl) ⟨365591, by rfl⟩ : syracuseStep 487455 = 731183) B731183
theorem B6221879 : Blo 483789 6221879 := bstep (se 1 (by rfl) ⟨4666409, by rfl⟩ : syracuseStep 6221879 = 9332819) B9332819
theorem B487631 : Blo 483789 487631 := bstep (se 1 (by rfl) ⟨365723, by rfl⟩ : syracuseStep 487631 = 731447) B731447
theorem B487751 : Blo 483789 487751 := bstep (se 1 (by rfl) ⟨365813, by rfl⟩ : syracuseStep 487751 = 731627) B731627
theorem B6287759 : Blo 483789 6287759 := bstep (se 1 (by rfl) ⟨4715819, by rfl⟩ : syracuseStep 6287759 = 9431639) B9431639
theorem B6287867 : Blo 483789 6287867 := bstep (se 1 (by rfl) ⟨4715900, by rfl⟩ : syracuseStep 6287867 = 9431801) B9431801
theorem B4977541 : Blo 483789 4977541 := bstep (se 4 (by rfl) ⟨466644, by rfl⟩ : syracuseStep 4977541 = 933289) B933289
theorem B816743 : Blo 483789 816743 := bstep (se 1 (by rfl) ⟨612557, by rfl⟩ : syracuseStep 816743 = 1225115) B1225115
theorem B1635983 : Blo 483789 1635983 := bstep (se 1 (by rfl) ⟨1226987, by rfl⟩ : syracuseStep 1635983 = 2453975) B2453975
theorem B1636361 : Blo 483789 1636361 := bstep (se 2 (by rfl) ⟨613635, by rfl⟩ : syracuseStep 1636361 = 1227271) B1227271
theorem B3537017 : Blo 483789 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B2456567 : Blo 483789 2456567 := bstep (se 1 (by rfl) ⟨1842425, by rfl⟩ : syracuseStep 2456567 = 3684851) B3684851
theorem B1277561 : Blo 483789 1277561 := bstep (se 2 (by rfl) ⟨479085, by rfl⟩ : syracuseStep 1277561 = 958171) B958171
theorem B819355 : Blo 483789 819355 := bstep (se 1 (by rfl) ⟨614516, by rfl⟩ : syracuseStep 819355 = 1229033) B1229033
theorem B819463 : Blo 483789 819463 := bstep (se 1 (by rfl) ⟨614597, by rfl⟩ : syracuseStep 819463 = 1229195) B1229195
theorem B2458835 : Blo 483789 2458835 := bstep (se 1 (by rfl) ⟨1844126, by rfl⟩ : syracuseStep 2458835 = 3688253) B3688253
theorem B820543 : Blo 483789 820543 := bstep (se 1 (by rfl) ⟨615407, by rfl⟩ : syracuseStep 820543 = 1230815) B1230815
theorem B1837019 : Blo 483789 1837019 := bstep (se 1 (by rfl) ⟨1377764, by rfl⟩ : syracuseStep 1837019 = 2755529) B2755529
theorem B349046909 : Blo 483789 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B1640681 : Blo 483789 1640681 := bstep (se 2 (by rfl) ⟨615255, by rfl⟩ : syracuseStep 1640681 = 1230511) B1230511
theorem B1050983 : Blo 483789 1050983 := bstep (se 1 (by rfl) ⟨788237, by rfl⟩ : syracuseStep 1050983 = 1576475) B1576475
theorem B1641167 : Blo 483789 1641167 := bstep (se 1 (by rfl) ⟨1230875, by rfl⟩ : syracuseStep 1641167 = 2461751) B2461751
theorem B658139 : Blo 483789 658139 := bstep (se 1 (by rfl) ⟨493604, by rfl⟩ : syracuseStep 658139 = 987209) B987209
theorem B196578161 : Blo 483789 196578161 := bstep (se 2 (by rfl) ⟨73716810, by rfl⟩ : syracuseStep 196578161 = 147433621) B147433621
theorem B822811 : Blo 483789 822811 := bstep (se 1 (by rfl) ⟨617108, by rfl⟩ : syracuseStep 822811 = 1234217) B1234217
theorem B1380635 : Blo 483789 1380635 := bstep (se 1 (by rfl) ⟨1035476, by rfl⟩ : syracuseStep 1380635 = 2070953) B2070953
theorem B4166099 : Blo 483789 4166099 := bstep (se 1 (by rfl) ⟨3124574, by rfl⟩ : syracuseStep 4166099 = 6249149) B6249149
theorem B1643003 : Blo 483789 1643003 := bstep (se 1 (by rfl) ⟨1232252, by rfl⟩ : syracuseStep 1643003 = 2464505) B2464505
theorem B2069039 : Blo 483789 2069039 := bstep (se 1 (by rfl) ⟨1551779, by rfl⟩ : syracuseStep 2069039 = 3103559) B3103559
theorem B26546885 : Blo 483789 26546885 := bstep (se 4 (by rfl) ⟨2488770, by rfl⟩ : syracuseStep 26546885 = 4977541) B4977541
theorem B3675131 : Blo 483789 3675131 := bstep (se 1 (by rfl) ⟨2756348, by rfl⟩ : syracuseStep 3675131 = 5512697) B5512697
theorem B726281 : Blo 483789 726281 := bstep (se 2 (by rfl) ⟨272355, by rfl⟩ : syracuseStep 726281 = 544711) B544711
theorem B1949701475 : Blo 483789 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B3511775 : Blo 483789 3511775 := bstep (se 1 (by rfl) ⟨2633831, by rfl⟩ : syracuseStep 3511775 = 5267663) B5267663
theorem B726761 : Blo 483789 726761 := bstep (se 2 (by rfl) ⟨272535, by rfl⟩ : syracuseStep 726761 = 545071) B545071
theorem B726953 : Blo 483789 726953 := bstep (se 2 (by rfl) ⟨272607, by rfl⟩ : syracuseStep 726953 = 545215) B545215
theorem B3676103 : Blo 483789 3676103 := bstep (se 1 (by rfl) ⟨2757077, by rfl⟩ : syracuseStep 3676103 = 5514155) B5514155
theorem B727019 : Blo 483789 727019 := bstep (se 1 (by rfl) ⟨545264, by rfl⟩ : syracuseStep 727019 = 1090529) B1090529
theorem B923719 : Blo 483789 923719 := bstep (se 1 (by rfl) ⟨692789, by rfl⟩ : syracuseStep 923719 = 1385579) B1385579
theorem B5249195 : Blo 483789 5249195 := bstep (se 1 (by rfl) ⟨3936896, by rfl⟩ : syracuseStep 5249195 = 7873793) B7873793
theorem B1644731 : Blo 483789 1644731 := bstep (se 1 (by rfl) ⟨1233548, by rfl⟩ : syracuseStep 1644731 = 2467097) B2467097
theorem B923879 : Blo 483789 923879 := bstep (se 1 (by rfl) ⟨692909, by rfl⟩ : syracuseStep 923879 = 1385819) B1385819
theorem B3938651 : Blo 483789 3938651 := bstep (se 1 (by rfl) ⟨2953988, by rfl⟩ : syracuseStep 3938651 = 5907977) B5907977
theorem B3250601 : Blo 483789 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B727535 : Blo 483789 727535 := bstep (se 1 (by rfl) ⟨545651, by rfl⟩ : syracuseStep 727535 = 1091303) B1091303
theorem B727847 : Blo 483789 727847 := bstep (se 1 (by rfl) ⟨545885, by rfl⟩ : syracuseStep 727847 = 1091771) B1091771
theorem B6659275 : Blo 483789 6659275 := bstep (se 1 (by rfl) ⟨4994456, by rfl⟩ : syracuseStep 6659275 = 9988913) B9988913
theorem B2759903 : Blo 483789 2759903 := bstep (se 1 (by rfl) ⟨2069927, by rfl⟩ : syracuseStep 2759903 = 4139855) B4139855
theorem B2464991 : Blo 483789 2464991 := bstep (se 1 (by rfl) ⟨1848743, by rfl⟩ : syracuseStep 2464991 = 3697487) B3697487
theorem B597295 : Blo 483789 597295 := bstep (se 1 (by rfl) ⟨447971, by rfl⟩ : syracuseStep 597295 = 895943) B895943
theorem B728447 : Blo 483789 728447 := bstep (se 1 (by rfl) ⟨546335, by rfl⟩ : syracuseStep 728447 = 1092671) B1092671
theorem B1383905 : Blo 483789 1383905 := bstep (se 2 (by rfl) ⟨518964, by rfl⟩ : syracuseStep 1383905 = 1037929) B1037929
theorem B1089071 : Blo 483789 1089071 := bstep (se 1 (by rfl) ⟨816803, by rfl⟩ : syracuseStep 1089071 = 1633607) B1633607
theorem B1646135 : Blo 483789 1646135 := bstep (se 1 (by rfl) ⟨1234601, by rfl⟩ : syracuseStep 1646135 = 2469203) B2469203
theorem B925435 : Blo 483789 925435 := bstep (se 1 (by rfl) ⟨694076, by rfl⟩ : syracuseStep 925435 = 1388153) B1388153
theorem B728999 : Blo 483789 728999 := bstep (se 1 (by rfl) ⟨546749, by rfl⟩ : syracuseStep 728999 = 1093499) B1093499
theorem B1843307 : Blo 483789 1843307 := bstep (se 1 (by rfl) ⟨1382480, by rfl⟩ : syracuseStep 1843307 = 2764961) B2764961
theorem B729257 : Blo 483789 729257 := bstep (se 2 (by rfl) ⟨273471, by rfl⟩ : syracuseStep 729257 = 546943) B546943
theorem B730025 : Blo 483789 730025 := bstep (se 2 (by rfl) ⟨273759, by rfl⟩ : syracuseStep 730025 = 547519) B547519
theorem B1844279 : Blo 483789 1844279 := bstep (se 1 (by rfl) ⟨1383209, by rfl⟩ : syracuseStep 1844279 = 2766419) B2766419
theorem B1090655 : Blo 483789 1090655 := bstep (se 1 (by rfl) ⟨817991, by rfl⟩ : syracuseStep 1090655 = 1635983) B1635983
theorem B730295 : Blo 483789 730295 := bstep (se 1 (by rfl) ⟨547721, by rfl⟩ : syracuseStep 730295 = 1095443) B1095443
theorem B1844477 : Blo 483789 1844477 := bstep (se 3 (by rfl) ⟨345839, by rfl⟩ : syracuseStep 1844477 = 691679) B691679
theorem B1090907 : Blo 483789 1090907 := bstep (se 1 (by rfl) ⟨818180, by rfl⟩ : syracuseStep 1090907 = 1636361) B1636361
theorem B730535 : Blo 483789 730535 := bstep (se 1 (by rfl) ⟨547901, by rfl⟩ : syracuseStep 730535 = 1095803) B1095803
theorem B730715 : Blo 483789 730715 := bstep (se 1 (by rfl) ⟨548036, by rfl⟩ : syracuseStep 730715 = 1096073) B1096073
theorem B731003 : Blo 483789 731003 := bstep (se 1 (by rfl) ⟨548252, by rfl⟩ : syracuseStep 731003 = 1096505) B1096505
theorem B731243 : Blo 483789 731243 := bstep (se 1 (by rfl) ⟨548432, by rfl⟩ : syracuseStep 731243 = 1096865) B1096865
theorem B731423 : Blo 483789 731423 := bstep (se 1 (by rfl) ⟨548567, by rfl⟩ : syracuseStep 731423 = 1097135) B1097135
theorem B2468393 : Blo 483789 2468393 := bstep (se 2 (by rfl) ⟨925647, by rfl⟩ : syracuseStep 2468393 = 1851295) B1851295
theorem B1977209 : Blo 483789 1977209 := bstep (se 2 (by rfl) ⟨741453, by rfl⟩ : syracuseStep 1977209 = 1482907) B1482907
theorem B3681449 : Blo 483789 3681449 := bstep (se 2 (by rfl) ⟨1380543, by rfl⟩ : syracuseStep 3681449 = 2761087) B2761087
theorem B3681935 : Blo 483789 3681935 := bstep (se 1 (by rfl) ⟨2761451, by rfl⟩ : syracuseStep 3681935 = 5522903) B5522903
theorem B2076455 : Blo 483789 2076455 := bstep (se 1 (by rfl) ⟨1557341, by rfl⟩ : syracuseStep 2076455 = 3114683) B3114683
theorem B4140881 : Blo 483789 4140881 := bstep (se 2 (by rfl) ⟨1552830, by rfl⟩ : syracuseStep 4140881 = 3105661) B3105661
theorem B7909285 : Blo 483789 7909285 := bstep (se 4 (by rfl) ⟨741495, by rfl⟩ : syracuseStep 7909285 = 1482991) B1482991
theorem B1093607 : Blo 483789 1093607 := bstep (se 1 (by rfl) ⟨820205, by rfl⟩ : syracuseStep 1093607 = 1640411) B1640411
theorem B1093679 : Blo 483789 1093679 := bstep (se 1 (by rfl) ⟨820259, by rfl⟩ : syracuseStep 1093679 = 1640519) B1640519
theorem B1847393 : Blo 483789 1847393 := bstep (se 2 (by rfl) ⟨692772, by rfl⟩ : syracuseStep 1847393 = 1385545) B1385545
theorem B4042855 : Blo 483789 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B1093967 : Blo 483789 1093967 := bstep (se 1 (by rfl) ⟨820475, by rfl⟩ : syracuseStep 1093967 = 1640951) B1640951
theorem B1749559 : Blo 483789 1749559 := bstep (se 1 (by rfl) ⟨1312169, by rfl⟩ : syracuseStep 1749559 = 2624339) B2624339
theorem B7484051 : Blo 483789 7484051 := bstep (se 1 (by rfl) ⟨5613038, by rfl⟩ : syracuseStep 7484051 = 11226077) B11226077
theorem B1094633 : Blo 483789 1094633 := bstep (se 2 (by rfl) ⟨410487, by rfl⟩ : syracuseStep 1094633 = 820975) B820975
theorem B2340971 : Blo 483789 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B2079017 : Blo 483789 2079017 := bstep (se 2 (by rfl) ⟨779631, by rfl⟩ : syracuseStep 2079017 = 1559263) B1559263
theorem B834239 : Blo 483789 834239 := bstep (se 1 (by rfl) ⟨625679, by rfl⟩ : syracuseStep 834239 = 1251359) B1251359
theorem B1227575 : Blo 483789 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B7847059 : Blo 483789 7847059 := bstep (se 1 (by rfl) ⟨5885294, by rfl⟩ : syracuseStep 7847059 = 11770589) B11770589
theorem B1096955 : Blo 483789 1096955 := bstep (se 1 (by rfl) ⟨822716, by rfl⟩ : syracuseStep 1096955 = 1645433) B1645433
theorem B1850795 : Blo 483789 1850795 := bstep (se 1 (by rfl) ⟨1388096, by rfl⟩ : syracuseStep 1850795 = 2776193) B2776193
theorem B4144607 : Blo 483789 4144607 := bstep (se 1 (by rfl) ⟨3108455, by rfl⟩ : syracuseStep 4144607 = 6216911) B6216911
theorem B1229215 : Blo 483789 1229215 := bstep (se 1 (by rfl) ⟨921911, by rfl⟩ : syracuseStep 1229215 = 1843823) B1843823
theorem B1033307 : Blo 483789 1033307 := bstep (se 1 (by rfl) ⟨774980, by rfl⟩ : syracuseStep 1033307 = 1549961) B1549961
theorem B2770109 : Blo 483789 2770109 := bstep (se 3 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 2770109 = 1038791) B1038791
theorem B8406251 : Blo 483789 8406251 := bstep (se 1 (by rfl) ⟨6304688, by rfl⟩ : syracuseStep 8406251 = 12609377) B12609377
theorem B13321837 : Blo 483789 13321837 := bstep (se 3 (by rfl) ⟨2497844, by rfl⟩ : syracuseStep 13321837 = 4995689) B4995689
theorem B16762535 : Blo 483789 16762535 := bstep (se 1 (by rfl) ⟨12571901, by rfl⟩ : syracuseStep 16762535 = 25143803) B25143803
theorem B7390939 : Blo 483789 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B4147919 : Blo 483789 4147919 := bstep (se 1 (by rfl) ⟨3110939, by rfl⟩ : syracuseStep 4147919 = 6221879) B6221879
theorem B3689225 : Blo 483789 3689225 := bstep (se 2 (by rfl) ⟨1383459, by rfl⟩ : syracuseStep 3689225 = 2766919) B2766919
theorem B7884377 : Blo 483789 7884377 := bstep (se 2 (by rfl) ⟨2956641, by rfl⟩ : syracuseStep 7884377 = 5913283) B5913283
theorem B544495 : Blo 483789 544495 := bstep (se 1 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 544495 = 816743) B816743
theorem B2773277 : Blo 483789 2773277 := bstep (se 3 (by rfl) ⟨519989, by rfl⟩ : syracuseStep 2773277 = 1039979) B1039979
theorem B1037083 : Blo 483789 1037083 := bstep (se 1 (by rfl) ⟨777812, by rfl⟩ : syracuseStep 1037083 = 1555625) B1555625
theorem B14046281 : Blo 483789 14046281 := bstep (se 2 (by rfl) ⟨5267355, by rfl⟩ : syracuseStep 14046281 = 10534711) B10534711
theorem B1234025 : Blo 483789 1234025 := bstep (se 2 (by rfl) ⟨462759, by rfl⟩ : syracuseStep 1234025 = 925519) B925519
theorem B33576281 : Blo 483789 33576281 := bstep (se 2 (by rfl) ⟨12591105, by rfl⟩ : syracuseStep 33576281 = 25182211) B25182211
theorem B1332791 : Blo 483789 1332791 := bstep (se 1 (by rfl) ⟨999593, by rfl⟩ : syracuseStep 1332791 = 1999187) B1999187
theorem B4052663 : Blo 483789 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B2775167 : Blo 483789 2775167 := bstep (se 1 (by rfl) ⟨2081375, by rfl⟩ : syracuseStep 2775167 = 4162751) B4162751
theorem B3693113 : Blo 483789 3693113 := bstep (se 2 (by rfl) ⟨1384917, by rfl⟩ : syracuseStep 3693113 = 2769835) B2769835
theorem B547951 : Blo 483789 547951 := bstep (se 1 (by rfl) ⟨410963, by rfl⟩ : syracuseStep 547951 = 821927) B821927
theorem B7855825 : Blo 483789 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B614395 : Blo 483789 614395 := bstep (se 1 (by rfl) ⟨460796, by rfl⟩ : syracuseStep 614395 = 921593) B921593
theorem B7004231 : Blo 483789 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B1171871 : Blo 483789 1171871 := bstep (se 1 (by rfl) ⟨878903, by rfl⟩ : syracuseStep 1171871 = 1757807) B1757807
theorem B3334567 : Blo 483789 3334567 := bstep (se 1 (by rfl) ⟨2500925, by rfl⟩ : syracuseStep 3334567 = 5001851) B5001851
theorem B118317611 : Blo 483789 118317611 := bstep (se 1 (by rfl) ⟨88738208, by rfl⟩ : syracuseStep 118317611 = 177476417) B177476417
theorem B5530193 : Blo 483789 5530193 := bstep (se 2 (by rfl) ⟨2073822, by rfl⟩ : syracuseStep 5530193 = 4147645) B4147645
theorem B778889 : Blo 483789 778889 := bstep (se 2 (by rfl) ⟨292083, by rfl⟩ : syracuseStep 778889 = 584167) B584167
theorem B484123 : Blo 483789 484123 := bstep (se 1 (by rfl) ⟨363092, by rfl⟩ : syracuseStep 484123 = 726185) B726185
theorem B484167 : Blo 483789 484167 := bstep (se 1 (by rfl) ⟨363125, by rfl⟩ : syracuseStep 484167 = 726251) B726251
theorem B484223 : Blo 483789 484223 := bstep (se 1 (by rfl) ⟨363167, by rfl⟩ : syracuseStep 484223 = 726335) B726335
theorem B615367 : Blo 483789 615367 := bstep (se 1 (by rfl) ⟨461525, by rfl⟩ : syracuseStep 615367 = 923051) B923051
theorem B484351 : Blo 483789 484351 := bstep (se 1 (by rfl) ⟨363263, by rfl⟩ : syracuseStep 484351 = 726527) B726527
theorem B484423 : Blo 483789 484423 := bstep (se 1 (by rfl) ⟨363317, by rfl⟩ : syracuseStep 484423 = 726635) B726635
theorem B484603 : Blo 483789 484603 := bstep (se 1 (by rfl) ⟨363452, by rfl⟩ : syracuseStep 484603 = 726905) B726905
theorem B484767 : Blo 483789 484767 := bstep (se 1 (by rfl) ⟨363575, by rfl⟩ : syracuseStep 484767 = 727151) B727151
theorem B484815 : Blo 483789 484815 := bstep (se 1 (by rfl) ⟨363611, by rfl⟩ : syracuseStep 484815 = 727223) B727223
theorem B485095 : Blo 483789 485095 := bstep (se 1 (by rfl) ⟨363821, by rfl⟩ : syracuseStep 485095 = 727643) B727643
theorem B485103 : Blo 483789 485103 := bstep (se 1 (by rfl) ⟨363827, by rfl⟩ : syracuseStep 485103 = 727655) B727655
theorem B485119 : Blo 483789 485119 := bstep (se 1 (by rfl) ⟨363839, by rfl⟩ : syracuseStep 485119 = 727679) B727679
theorem B485191 : Blo 483789 485191 := bstep (se 1 (by rfl) ⟨363893, by rfl⟩ : syracuseStep 485191 = 727787) B727787
theorem B485211 : Blo 483789 485211 := bstep (se 1 (by rfl) ⟨363908, by rfl⟩ : syracuseStep 485211 = 727817) B727817
theorem B485371 : Blo 483789 485371 := bstep (se 1 (by rfl) ⟨364028, by rfl⟩ : syracuseStep 485371 = 728057) B728057
theorem B485791 : Blo 483789 485791 := bstep (se 1 (by rfl) ⟨364343, by rfl⟩ : syracuseStep 485791 = 728687) B728687
theorem B1108457 : Blo 483789 1108457 := bstep (se 2 (by rfl) ⟨415671, by rfl⟩ : syracuseStep 1108457 = 831343) B831343
theorem B485871 : Blo 483789 485871 := bstep (se 1 (by rfl) ⟨364403, by rfl⟩ : syracuseStep 485871 = 728807) B728807
theorem B4418059 : Blo 483789 4418059 := bstep (se 1 (by rfl) ⟨3313544, by rfl⟩ : syracuseStep 4418059 = 6627089) B6627089
theorem B518815 : Blo 483789 518815 := bstep (se 1 (by rfl) ⟨389111, by rfl⟩ : syracuseStep 518815 = 778223) B778223
theorem B1665697 : Blo 483789 1665697 := bstep (se 2 (by rfl) ⟨624636, by rfl⟩ : syracuseStep 1665697 = 1249273) B1249273
theorem B486055 : Blo 483789 486055 := bstep (se 1 (by rfl) ⟨364541, by rfl⟩ : syracuseStep 486055 = 729083) B729083
theorem B486095 : Blo 483789 486095 := bstep (se 1 (by rfl) ⟨364571, by rfl⟩ : syracuseStep 486095 = 729143) B729143
theorem B551711 : Blo 483789 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B486175 : Blo 483789 486175 := bstep (se 1 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 486175 = 729263) B729263
theorem B486311 : Blo 483789 486311 := bstep (se 1 (by rfl) ⟨364733, by rfl⟩ : syracuseStep 486311 = 729467) B729467
theorem B486427 : Blo 483789 486427 := bstep (se 1 (by rfl) ⟨364820, by rfl⟩ : syracuseStep 486427 = 729641) B729641
theorem B486491 : Blo 483789 486491 := bstep (se 1 (by rfl) ⟨364868, by rfl⟩ : syracuseStep 486491 = 729737) B729737
theorem B3107969 : Blo 483789 3107969 := bstep (se 2 (by rfl) ⟨1165488, by rfl⟩ : syracuseStep 3107969 = 2330977) B2330977
theorem B486631 : Blo 483789 486631 := bstep (se 1 (by rfl) ⟨364973, by rfl⟩ : syracuseStep 486631 = 729947) B729947
theorem B486655 : Blo 483789 486655 := bstep (se 1 (by rfl) ⟨364991, by rfl⟩ : syracuseStep 486655 = 729983) B729983
theorem B486703 : Blo 483789 486703 := bstep (se 1 (by rfl) ⟨365027, by rfl⟩ : syracuseStep 486703 = 730055) B730055
theorem B2452841 : Blo 483789 2452841 := bstep (se 2 (by rfl) ⟨919815, by rfl⟩ : syracuseStep 2452841 = 1839631) B1839631
theorem B486847 : Blo 483789 486847 := bstep (se 1 (by rfl) ⟨365135, by rfl⟩ : syracuseStep 486847 = 730271) B730271
theorem B486943 : Blo 483789 486943 := bstep (se 1 (by rfl) ⟨365207, by rfl⟩ : syracuseStep 486943 = 730415) B730415
theorem B487071 : Blo 483789 487071 := bstep (se 1 (by rfl) ⟨365303, by rfl⟩ : syracuseStep 487071 = 730607) B730607
theorem B487079 : Blo 483789 487079 := bstep (se 1 (by rfl) ⟨365309, by rfl⟩ : syracuseStep 487079 = 730619) B730619
theorem B487103 : Blo 483789 487103 := bstep (se 1 (by rfl) ⟨365327, by rfl⟩ : syracuseStep 487103 = 730655) B730655
theorem B1634039 : Blo 483789 1634039 := bstep (se 1 (by rfl) ⟨1225529, by rfl⟩ : syracuseStep 1634039 = 2451059) B2451059
theorem B487199 : Blo 483789 487199 := bstep (se 1 (by rfl) ⟨365399, by rfl⟩ : syracuseStep 487199 = 730799) B730799
theorem B487259 : Blo 483789 487259 := bstep (se 1 (by rfl) ⟨365444, by rfl⟩ : syracuseStep 487259 = 730889) B730889
theorem B487279 : Blo 483789 487279 := bstep (se 1 (by rfl) ⟨365459, by rfl⟩ : syracuseStep 487279 = 730919) B730919
theorem B487679 : Blo 483789 487679 := bstep (se 1 (by rfl) ⟨365759, by rfl⟩ : syracuseStep 487679 = 731519) B731519
theorem B1635119 : Blo 483789 1635119 := bstep (se 1 (by rfl) ⟨1226339, by rfl⟩ : syracuseStep 1635119 = 2452679) B2452679
theorem B4191839 : Blo 483789 4191839 := bstep (se 1 (by rfl) ⟨3143879, by rfl⟩ : syracuseStep 4191839 = 6287759) B6287759
theorem B4191911 : Blo 483789 4191911 := bstep (se 1 (by rfl) ⟨3143933, by rfl⟩ : syracuseStep 4191911 = 6287867) B6287867
theorem B817087 : Blo 483789 817087 := bstep (se 1 (by rfl) ⟨612815, by rfl⟩ : syracuseStep 817087 = 1225631) B1225631
theorem B5404967 : Blo 483789 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B3701375 : Blo 483789 3701375 := bstep (se 1 (by rfl) ⟨2776031, by rfl⟩ : syracuseStep 3701375 = 5552063) B5552063
theorem B2358011 : Blo 483789 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B14220157 : Blo 483789 14220157 := bstep (se 3 (by rfl) ⟨2666279, by rfl⟩ : syracuseStep 14220157 = 5332559) B5332559
theorem B1637711 : Blo 483789 1637711 := bstep (se 1 (by rfl) ⟨1228283, by rfl⟩ : syracuseStep 1637711 = 2456567) B2456567
theorem B2522551 : Blo 483789 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B851707 : Blo 483789 851707 := bstep (se 1 (by rfl) ⟨638780, by rfl⟩ : syracuseStep 851707 = 1277561) B1277561
theorem B1638953 : Blo 483789 1638953 := bstep (se 2 (by rfl) ⟨614607, by rfl⟩ : syracuseStep 1638953 = 1229215) B1229215
theorem B688871 : Blo 483789 688871 := bstep (se 1 (by rfl) ⟨516653, by rfl⟩ : syracuseStep 688871 = 1033307) B1033307
theorem B1639223 : Blo 483789 1639223 := bstep (se 1 (by rfl) ⟨1229417, by rfl⟩ : syracuseStep 1639223 = 2458835) B2458835
theorem B5604167 : Blo 483789 5604167 := bstep (se 1 (by rfl) ⟨4203125, by rfl⟩ : syracuseStep 5604167 = 8406251) B8406251
theorem B11175023 : Blo 483789 11175023 := bstep (se 1 (by rfl) ⟨8381267, by rfl⟩ : syracuseStep 11175023 = 16762535) B16762535
theorem B820489 : Blo 483789 820489 := bstep (se 2 (by rfl) ⟨307683, by rfl⟩ : syracuseStep 820489 = 615367) B615367
theorem B2459483 : Blo 483789 2459483 := bstep (se 1 (by rfl) ⟨1844612, by rfl⟩ : syracuseStep 2459483 = 3689225) B3689225
theorem B17762449 : Blo 483789 17762449 := bstep (se 2 (by rfl) ⟨6660918, by rfl⟩ : syracuseStep 17762449 = 13321837) B13321837
theorem B920423 : Blo 483789 920423 := bstep (se 1 (by rfl) ⟨690317, by rfl⟩ : syracuseStep 920423 = 1380635) B1380635
theorem B1379359 : Blo 483789 1379359 := bstep (se 1 (by rfl) ⟨1034519, by rfl⟩ : syracuseStep 1379359 = 2069039) B2069039
theorem B17697923 : Blo 483789 17697923 := bstep (se 1 (by rfl) ⟨13273442, by rfl⟩ : syracuseStep 17697923 = 26546885) B26546885
theorem B822683 : Blo 483789 822683 := bstep (se 1 (by rfl) ⟨617012, by rfl⟩ : syracuseStep 822683 = 1234025) B1234025
theorem B691753 : Blo 483789 691753 := bstep (se 2 (by rfl) ⟨259407, by rfl⟩ : syracuseStep 691753 = 518815) B518815
theorem B22384187 : Blo 483789 22384187 := bstep (se 1 (by rfl) ⟨16788140, by rfl⟩ : syracuseStep 22384187 = 33576281) B33576281
theorem B5199203933 : Blo 483789 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B888527 : Blo 483789 888527 := bstep (se 1 (by rfl) ⟨666395, by rfl⟩ : syracuseStep 888527 = 1332791) B1332791
theorem B2625767 : Blo 483789 2625767 := bstep (se 1 (by rfl) ⟨1969325, by rfl⟩ : syracuseStep 2625767 = 3938651) B3938651
theorem B2167067 : Blo 483789 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B2462075 : Blo 483789 2462075 := bstep (se 1 (by rfl) ⟨1846556, by rfl⟩ : syracuseStep 2462075 = 3693113) B3693113
theorem B1839935 : Blo 483789 1839935 := bstep (se 1 (by rfl) ⟨1379951, by rfl⟩ : syracuseStep 1839935 = 2759903) B2759903
theorem B1643327 : Blo 483789 1643327 := bstep (se 1 (by rfl) ⟨1232495, by rfl⟩ : syracuseStep 1643327 = 2464991) B2464991
theorem B725993 : Blo 483789 725993 := bstep (se 2 (by rfl) ⟨272247, by rfl⟩ : syracuseStep 725993 = 544495) B544495
theorem B922603 : Blo 483789 922603 := bstep (se 1 (by rfl) ⟨691952, by rfl⟩ : syracuseStep 922603 = 1383905) B1383905
theorem B726047 : Blo 483789 726047 := bstep (se 1 (by rfl) ⟨544535, by rfl⟩ : syracuseStep 726047 = 1089071) B1089071
theorem B78878407 : Blo 483789 78878407 := bstep (se 1 (by rfl) ⟨59158805, by rfl⟩ : syracuseStep 78878407 = 118317611) B118317611
theorem B727103 : Blo 483789 727103 := bstep (se 1 (by rfl) ⟨545327, by rfl⟩ : syracuseStep 727103 = 1090655) B1090655
theorem B2332745 : Blo 483789 2332745 := bstep (se 2 (by rfl) ⟨874779, by rfl⟩ : syracuseStep 2332745 = 1749559) B1749559
theorem B727271 : Blo 483789 727271 := bstep (se 1 (by rfl) ⟨545453, by rfl⟩ : syracuseStep 727271 = 1090907) B1090907
theorem B1382777 : Blo 483789 1382777 := bstep (se 2 (by rfl) ⟨518541, by rfl⟩ : syracuseStep 1382777 = 1037083) B1037083
theorem B1645595 : Blo 483789 1645595 := bstep (se 1 (by rfl) ⟨1234196, by rfl⟩ : syracuseStep 1645595 = 2468393) B2468393
theorem B1318139 : Blo 483789 1318139 := bstep (se 1 (by rfl) ⟨988604, by rfl⟩ : syracuseStep 1318139 = 1977209) B1977209
theorem B2071979 : Blo 483789 2071979 := bstep (se 1 (by rfl) ⟨1553984, by rfl⟩ : syracuseStep 2071979 = 3107969) B3107969
theorem B1089359 : Blo 483789 1089359 := bstep (se 1 (by rfl) ⟨817019, by rfl⟩ : syracuseStep 1089359 = 1634039) B1634039
theorem B1384303 : Blo 483789 1384303 := bstep (se 1 (by rfl) ⟨1038227, by rfl⟩ : syracuseStep 1384303 = 2076455) B2076455
theorem B2760587 : Blo 483789 2760587 := bstep (se 1 (by rfl) ⟨2070440, by rfl⟩ : syracuseStep 2760587 = 4140881) B4140881
theorem B1089449 : Blo 483789 1089449 := bstep (se 2 (by rfl) ⟨408543, by rfl⟩ : syracuseStep 1089449 = 817087) B817087
theorem B729071 : Blo 483789 729071 := bstep (se 1 (by rfl) ⟨546803, by rfl⟩ : syracuseStep 729071 = 1093607) B1093607
theorem B729119 : Blo 483789 729119 := bstep (se 1 (by rfl) ⟨546839, by rfl⟩ : syracuseStep 729119 = 1093679) B1093679
theorem B729311 : Blo 483789 729311 := bstep (se 1 (by rfl) ⟨546983, by rfl⟩ : syracuseStep 729311 = 1093967) B1093967
theorem B4989367 : Blo 483789 4989367 := bstep (se 1 (by rfl) ⟨3742025, by rfl⟩ : syracuseStep 4989367 = 7484051) B7484051
theorem B1090079 : Blo 483789 1090079 := bstep (se 1 (by rfl) ⟨817559, by rfl⟩ : syracuseStep 1090079 = 1635119) B1635119
theorem B729755 : Blo 483789 729755 := bstep (se 1 (by rfl) ⟨547316, by rfl⟩ : syracuseStep 729755 = 1094633) B1094633
theorem B2794559 : Blo 483789 2794559 := bstep (se 1 (by rfl) ⟨2095919, by rfl⟩ : syracuseStep 2794559 = 4191839) B4191839
theorem B2794607 : Blo 483789 2794607 := bstep (se 1 (by rfl) ⟨2095955, by rfl⟩ : syracuseStep 2794607 = 4191911) B4191911
theorem B730601 : Blo 483789 730601 := bstep (se 2 (by rfl) ⟨273975, by rfl⟩ : syracuseStep 730601 = 547951) B547951
theorem B10462745 : Blo 483789 10462745 := bstep (se 2 (by rfl) ⟨3923529, by rfl⟩ : syracuseStep 10462745 = 7847059) B7847059
theorem B1386011 : Blo 483789 1386011 := bstep (se 1 (by rfl) ⟨1039508, by rfl⟩ : syracuseStep 1386011 = 2079017) B2079017
theorem B796393 : Blo 483789 796393 := bstep (se 2 (by rfl) ⟨298647, by rfl⟩ : syracuseStep 796393 = 597295) B597295
theorem B2467583 : Blo 483789 2467583 := bstep (se 1 (by rfl) ⟨1850687, by rfl⟩ : syracuseStep 2467583 = 3701375) B3701375
theorem B731303 : Blo 483789 731303 := bstep (se 1 (by rfl) ⟨548477, by rfl⟩ : syracuseStep 731303 = 1096955) B1096955
theorem B1091807 : Blo 483789 1091807 := bstep (se 1 (by rfl) ⟨818855, by rfl⟩ : syracuseStep 1091807 = 1637711) B1637711
theorem B2763071 : Blo 483789 2763071 := bstep (se 1 (by rfl) ⟨2072303, by rfl⟩ : syracuseStep 2763071 = 4144607) B4144607
theorem B1092473 : Blo 483789 1092473 := bstep (se 2 (by rfl) ⟨409677, by rfl⟩ : syracuseStep 1092473 = 819355) B819355
theorem B1092617 : Blo 483789 1092617 := bstep (se 2 (by rfl) ⟨409731, by rfl⟩ : syracuseStep 1092617 = 819463) B819463
theorem B1846739 : Blo 483789 1846739 := bstep (se 1 (by rfl) ⟨1385054, by rfl⟩ : syracuseStep 1846739 = 2770109) B2770109
theorem B1224679 : Blo 483789 1224679 := bstep (se 1 (by rfl) ⟨918509, by rfl⟩ : syracuseStep 1224679 = 1837019) B1837019
theorem B232697939 : Blo 483789 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B1093787 : Blo 483789 1093787 := bstep (se 1 (by rfl) ⟨820340, by rfl⟩ : syracuseStep 1093787 = 1640681) B1640681
theorem B700655 : Blo 483789 700655 := bstep (se 1 (by rfl) ⟨525491, by rfl⟩ : syracuseStep 700655 = 1050983) B1050983
theorem B1094057 : Blo 483789 1094057 := bstep (se 2 (by rfl) ⟨410271, by rfl⟩ : syracuseStep 1094057 = 820543) B820543
theorem B2765279 : Blo 483789 2765279 := bstep (se 1 (by rfl) ⟨2073959, by rfl⟩ : syracuseStep 2765279 = 4147919) B4147919
theorem B1094111 : Blo 483789 1094111 := bstep (se 1 (by rfl) ⟨820583, by rfl⟩ : syracuseStep 1094111 = 1641167) B1641167
theorem B131052107 : Blo 483789 131052107 := bstep (se 1 (by rfl) ⟨98289080, by rfl⟩ : syracuseStep 131052107 = 196578161) B196578161
theorem B5256251 : Blo 483789 5256251 := bstep (se 1 (by rfl) ⟨3942188, by rfl⟩ : syracuseStep 5256251 = 7884377) B7884377
theorem B1848851 : Blo 483789 1848851 := bstep (se 1 (by rfl) ⟨1386638, by rfl⟩ : syracuseStep 1848851 = 2773277) B2773277
theorem B1095335 : Blo 483789 1095335 := bstep (se 1 (by rfl) ⟨821501, by rfl⟩ : syracuseStep 1095335 = 1643003) B1643003
theorem B2701775 : Blo 483789 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B1850111 : Blo 483789 1850111 := bstep (se 1 (by rfl) ⟨1387583, by rfl⟩ : syracuseStep 1850111 = 2775167) B2775167
theorem B1096487 : Blo 483789 1096487 := bstep (se 1 (by rfl) ⟨822365, by rfl⟩ : syracuseStep 1096487 = 1644731) B1644731
theorem B1097081 : Blo 483789 1097081 := bstep (se 2 (by rfl) ⟨411405, by rfl⟩ : syracuseStep 1097081 = 822811) B822811
theorem B1097423 : Blo 483789 1097423 := bstep (se 1 (by rfl) ⟨823067, by rfl⟩ : syracuseStep 1097423 = 1646135) B1646135
theorem B4669487 : Blo 483789 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B1228871 : Blo 483789 1228871 := bstep (se 1 (by rfl) ⟨921653, by rfl⟩ : syracuseStep 1228871 = 1843307) B1843307
theorem B5390473 : Blo 483789 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B3686795 : Blo 483789 3686795 := bstep (se 1 (by rfl) ⟨2765096, by rfl⟩ : syracuseStep 3686795 = 5530193) B5530193
theorem B1229519 : Blo 483789 1229519 := bstep (se 1 (by rfl) ⟨922139, by rfl⟩ : syracuseStep 1229519 = 1844279) B1844279
theorem B1229651 : Blo 483789 1229651 := bstep (se 1 (by rfl) ⟨922238, by rfl⟩ : syracuseStep 1229651 = 1844477) B1844477
theorem B738971 : Blo 483789 738971 := bstep (se 1 (by rfl) ⟨554228, by rfl⟩ : syracuseStep 738971 = 1108457) B1108457
theorem B1755037 : Blo 483789 1755037 := bstep (se 3 (by rfl) ⟨329069, by rfl⟩ : syracuseStep 1755037 = 658139) B658139
theorem B1231595 : Blo 483789 1231595 := bstep (se 1 (by rfl) ⟨923696, by rfl⟩ : syracuseStep 1231595 = 1847393) B1847393
theorem B1231625 : Blo 483789 1231625 := bstep (se 2 (by rfl) ⟨461859, by rfl⟩ : syracuseStep 1231625 = 923719) B923719
theorem B18960209 : Blo 483789 18960209 := bstep (se 2 (by rfl) ⟨7110078, by rfl⟩ : syracuseStep 18960209 = 14220157) B14220157
theorem B4542437 : Blo 483789 4542437 := bstep (se 4 (by rfl) ⟨425853, by rfl⟩ : syracuseStep 4542437 = 851707) B851707
theorem B1560647 : Blo 483789 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B3363401 : Blo 483789 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B10474433 : Blo 483789 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B1233863 : Blo 483789 1233863 := bstep (se 1 (by rfl) ⟨925397, by rfl⟩ : syracuseStep 1233863 = 1850795) B1850795
theorem B1233913 : Blo 483789 1233913 := bstep (se 2 (by rfl) ⟨462717, by rfl⟩ : syracuseStep 1233913 = 925435) B925435
theorem B4446089 : Blo 483789 4446089 := bstep (se 2 (by rfl) ⟨1667283, by rfl⟩ : syracuseStep 4446089 = 3334567) B3334567
theorem B9854585 : Blo 483789 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B2777399 : Blo 483789 2777399 := bstep (se 1 (by rfl) ⟨2083049, by rfl⟩ : syracuseStep 2777399 = 4166099) B4166099
theorem B2450087 : Blo 483789 2450087 := bstep (se 1 (by rfl) ⟨1837565, by rfl⟩ : syracuseStep 2450087 = 3675131) B3675131
theorem B5890745 : Blo 483789 5890745 := bstep (se 2 (by rfl) ⟨2209029, by rfl⟩ : syracuseStep 5890745 = 4418059) B4418059
theorem B9364187 : Blo 483789 9364187 := bstep (se 1 (by rfl) ⟨7023140, by rfl⟩ : syracuseStep 9364187 = 14046281) B14046281
theorem B484187 : Blo 483789 484187 := bstep (se 1 (by rfl) ⟨363140, by rfl⟩ : syracuseStep 484187 = 726281) B726281
theorem B2220929 : Blo 483789 2220929 := bstep (se 2 (by rfl) ⟨832848, by rfl⟩ : syracuseStep 2220929 = 1665697) B1665697
theorem B484507 : Blo 483789 484507 := bstep (se 1 (by rfl) ⟨363380, by rfl⟩ : syracuseStep 484507 = 726761) B726761
theorem B9364733 : Blo 483789 9364733 := bstep (se 3 (by rfl) ⟨1755887, by rfl⟩ : syracuseStep 9364733 = 3511775) B3511775
theorem B484635 : Blo 483789 484635 := bstep (se 1 (by rfl) ⟨363476, by rfl⟩ : syracuseStep 484635 = 726953) B726953
theorem B2450735 : Blo 483789 2450735 := bstep (se 1 (by rfl) ⟨1838051, by rfl⟩ : syracuseStep 2450735 = 3676103) B3676103
theorem B484679 : Blo 483789 484679 := bstep (se 1 (by rfl) ⟨363509, by rfl⟩ : syracuseStep 484679 = 727019) B727019
theorem B3499463 : Blo 483789 3499463 := bstep (se 1 (by rfl) ⟨2624597, by rfl⟩ : syracuseStep 3499463 = 5249195) B5249195
theorem B615919 : Blo 483789 615919 := bstep (se 1 (by rfl) ⟨461939, by rfl⟩ : syracuseStep 615919 = 923879) B923879
theorem B485023 : Blo 483789 485023 := bstep (se 1 (by rfl) ⟨363767, by rfl⟩ : syracuseStep 485023 = 727535) B727535
theorem B485231 : Blo 483789 485231 := bstep (se 1 (by rfl) ⟨363923, by rfl⟩ : syracuseStep 485231 = 727847) B727847
theorem B485631 : Blo 483789 485631 := bstep (se 1 (by rfl) ⟨364223, by rfl⟩ : syracuseStep 485631 = 728447) B728447
theorem B10545713 : Blo 483789 10545713 := bstep (se 2 (by rfl) ⟨3954642, by rfl⟩ : syracuseStep 10545713 = 7909285) B7909285
theorem B485999 : Blo 483789 485999 := bstep (se 1 (by rfl) ⟨364499, by rfl⟩ : syracuseStep 485999 = 728999) B728999
theorem B486171 : Blo 483789 486171 := bstep (se 1 (by rfl) ⟨364628, by rfl⟩ : syracuseStep 486171 = 729257) B729257
theorem B781247 : Blo 483789 781247 := bstep (se 1 (by rfl) ⟨585935, by rfl⟩ : syracuseStep 781247 = 1171871) B1171871
theorem B519259 : Blo 483789 519259 := bstep (se 1 (by rfl) ⟨389444, by rfl⟩ : syracuseStep 519259 = 778889) B778889
theorem B486683 : Blo 483789 486683 := bstep (se 1 (by rfl) ⟨365012, by rfl⟩ : syracuseStep 486683 = 730025) B730025
theorem B486863 : Blo 483789 486863 := bstep (se 1 (by rfl) ⟨365147, by rfl⟩ : syracuseStep 486863 = 730295) B730295
theorem B487023 : Blo 483789 487023 := bstep (se 1 (by rfl) ⟨365267, by rfl⟩ : syracuseStep 487023 = 730535) B730535
theorem B487143 : Blo 483789 487143 := bstep (se 1 (by rfl) ⟨365357, by rfl⟩ : syracuseStep 487143 = 730715) B730715
theorem B487335 : Blo 483789 487335 := bstep (se 1 (by rfl) ⟨365501, by rfl⟩ : syracuseStep 487335 = 731003) B731003
theorem B487495 : Blo 483789 487495 := bstep (se 1 (by rfl) ⟨365621, by rfl⟩ : syracuseStep 487495 = 731243) B731243
theorem B487615 : Blo 483789 487615 := bstep (se 1 (by rfl) ⟨365711, by rfl⟩ : syracuseStep 487615 = 731423) B731423
theorem B6288029 : Blo 483789 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B1471229 : Blo 483789 1471229 := bstep (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) B551711
theorem B2454299 : Blo 483789 2454299 := bstep (se 1 (by rfl) ⟨1840724, by rfl⟩ : syracuseStep 2454299 = 3681449) B3681449
theorem B1635227 : Blo 483789 1635227 := bstep (se 1 (by rfl) ⟨1226420, by rfl⟩ : syracuseStep 1635227 = 2452841) B2452841
theorem B2454623 : Blo 483789 2454623 := bstep (se 1 (by rfl) ⟨1840967, by rfl⟩ : syracuseStep 2454623 = 3681935) B3681935
theorem B3603311 : Blo 483789 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B8879033 : Blo 483789 8879033 := bstep (se 2 (by rfl) ⟨3329637, by rfl⟩ : syracuseStep 8879033 = 6659275) B6659275
theorem B556159 : Blo 483789 556159 := bstep (se 1 (by rfl) ⟨417119, by rfl⟩ : syracuseStep 556159 = 834239) B834239
theorem B818383 : Blo 483789 818383 := bstep (se 1 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 818383 = 1227575) B1227575
theorem B819193 : Blo 483789 819193 := bstep (se 2 (by rfl) ⟨307197, by rfl⟩ : syracuseStep 819193 = 614395) B614395
theorem B3112991 : Blo 483789 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B819247 : Blo 483789 819247 := bstep (se 1 (by rfl) ⟨614435, by rfl⟩ : syracuseStep 819247 = 1228871) B1228871
theorem B4161725 : Blo 483789 4161725 := bstep (se 3 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 4161725 = 1560647) B1560647
theorem B620527837 : Blo 483789 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B2457863 : Blo 483789 2457863 := bstep (se 1 (by rfl) ⟨1843397, by rfl⟩ : syracuseStep 2457863 = 3686795) B3686795
theorem B819679 : Blo 483789 819679 := bstep (se 1 (by rfl) ⟨614759, by rfl⟩ : syracuseStep 819679 = 1229519) B1229519
theorem B3736111 : Blo 483789 3736111 := bstep (se 1 (by rfl) ⟨2802083, by rfl⟩ : syracuseStep 3736111 = 5604167) B5604167
theorem B819767 : Blo 483789 819767 := bstep (se 1 (by rfl) ⟨614825, by rfl⟩ : syracuseStep 819767 = 1229651) B1229651
theorem B6652489 : Blo 483789 6652489 := bstep (se 2 (by rfl) ⟨2494683, by rfl⟩ : syracuseStep 6652489 = 4989367) B4989367
theorem B492647 : Blo 483789 492647 := bstep (se 1 (by rfl) ⟨369485, by rfl⟩ : syracuseStep 492647 = 738971) B738971
theorem B1639655 : Blo 483789 1639655 := bstep (se 1 (by rfl) ⟨1229741, by rfl⟩ : syracuseStep 1639655 = 2459483) B2459483
theorem B821063 : Blo 483789 821063 := bstep (se 1 (by rfl) ⟨615797, by rfl⟩ : syracuseStep 821063 = 1231595) B1231595
theorem B821083 : Blo 483789 821083 := bstep (se 1 (by rfl) ⟨615812, by rfl⟩ : syracuseStep 821083 = 1231625) B1231625
theorem B1836989 : Blo 483789 1836989 := bstep (se 3 (by rfl) ⟨344435, by rfl⟩ : syracuseStep 1836989 = 688871) B688871
theorem B821225 : Blo 483789 821225 := bstep (se 2 (by rfl) ⟨307959, by rfl⟩ : syracuseStep 821225 = 615919) B615919
theorem B11798615 : Blo 483789 11798615 := bstep (se 1 (by rfl) ⟨8848961, by rfl⟩ : syracuseStep 11798615 = 17697923) B17697923
theorem B3466135955 : Blo 483789 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B592351 : Blo 483789 592351 := bstep (se 1 (by rfl) ⟨444263, by rfl⟩ : syracuseStep 592351 = 888527) B888527
theorem B7473653 : Blo 483789 7473653 := bstep (se 5 (by rfl) ⟨350327, by rfl⟩ : syracuseStep 7473653 = 700655) B700655
theorem B1444711 : Blo 483789 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B1641383 : Blo 483789 1641383 := bstep (se 1 (by rfl) ⟨1231037, by rfl⟩ : syracuseStep 1641383 = 2462075) B2462075
theorem B6982955 : Blo 483789 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B822575 : Blo 483789 822575 := bstep (se 1 (by rfl) ⟨616931, by rfl⟩ : syracuseStep 822575 = 1233863) B1233863
theorem B1839145 : Blo 483789 1839145 := bstep (se 2 (by rfl) ⟨689679, by rfl⟩ : syracuseStep 1839145 = 1379359) B1379359
theorem B692345 : Blo 483789 692345 := bstep (se 2 (by rfl) ⟨259629, by rfl⟩ : syracuseStep 692345 = 519259) B519259
theorem B921851 : Blo 483789 921851 := bstep (se 1 (by rfl) ⟨691388, by rfl⟩ : syracuseStep 921851 = 1382777) B1382777
theorem B922337 : Blo 483789 922337 := bstep (se 2 (by rfl) ⟨345876, by rfl⟩ : syracuseStep 922337 = 691753) B691753
theorem B1381319 : Blo 483789 1381319 := bstep (se 1 (by rfl) ⟨1035989, by rfl⟩ : syracuseStep 1381319 = 2071979) B2071979
theorem B726239 : Blo 483789 726239 := bstep (se 1 (by rfl) ⟨544679, by rfl⟩ : syracuseStep 726239 = 1089359) B1089359
theorem B1840391 : Blo 483789 1840391 := bstep (se 1 (by rfl) ⟨1380293, by rfl⟩ : syracuseStep 1840391 = 2760587) B2760587
theorem B726299 : Blo 483789 726299 := bstep (se 1 (by rfl) ⟨544724, by rfl⟩ : syracuseStep 726299 = 1089449) B1089449
theorem B726719 : Blo 483789 726719 := bstep (se 1 (by rfl) ⟨545039, by rfl⟩ : syracuseStep 726719 = 1090079) B1090079
theorem B1480619 : Blo 483789 1480619 := bstep (se 1 (by rfl) ⟨1110464, by rfl⟩ : syracuseStep 1480619 = 2220929) B2220929
theorem B2332975 : Blo 483789 2332975 := bstep (se 1 (by rfl) ⟨1749731, by rfl⟩ : syracuseStep 2332975 = 3499463) B3499463
theorem B1645055 : Blo 483789 1645055 := bstep (se 1 (by rfl) ⟨1233791, by rfl⟩ : syracuseStep 1645055 = 2467583) B2467583
theorem B1645217 : Blo 483789 1645217 := bstep (se 2 (by rfl) ⟨616956, by rfl⟩ : syracuseStep 1645217 = 1233913) B1233913
theorem B727871 : Blo 483789 727871 := bstep (se 1 (by rfl) ⟨545903, by rfl⟩ : syracuseStep 727871 = 1091807) B1091807
theorem B1842047 : Blo 483789 1842047 := bstep (se 1 (by rfl) ⟨1381535, by rfl⟩ : syracuseStep 1842047 = 2763071) B2763071
theorem B728315 : Blo 483789 728315 := bstep (se 1 (by rfl) ⟨546236, by rfl⟩ : syracuseStep 728315 = 1092473) B1092473
theorem B728411 : Blo 483789 728411 := bstep (se 1 (by rfl) ⟨546308, by rfl⟩ : syracuseStep 728411 = 1092617) B1092617
theorem B729191 : Blo 483789 729191 := bstep (se 1 (by rfl) ⟨546893, by rfl⟩ : syracuseStep 729191 = 1093787) B1093787
theorem B729371 : Blo 483789 729371 := bstep (se 1 (by rfl) ⟨547028, by rfl⟩ : syracuseStep 729371 = 1094057) B1094057
theorem B1843519 : Blo 483789 1843519 := bstep (se 1 (by rfl) ⟨1382639, by rfl⟩ : syracuseStep 1843519 = 2765279) B2765279
theorem B729407 : Blo 483789 729407 := bstep (se 1 (by rfl) ⟨547055, by rfl⟩ : syracuseStep 729407 = 1094111) B1094111
theorem B87368071 : Blo 483789 87368071 := bstep (se 1 (by rfl) ⟨65526053, by rfl⟩ : syracuseStep 87368071 = 131052107) B131052107
theorem B1090151 : Blo 483789 1090151 := bstep (se 1 (by rfl) ⟨817613, by rfl⟩ : syracuseStep 1090151 = 1635227) B1635227
theorem B730223 : Blo 483789 730223 := bstep (se 1 (by rfl) ⟨547667, by rfl⟩ : syracuseStep 730223 = 1095335) B1095335
theorem B1091177 : Blo 483789 1091177 := bstep (se 2 (by rfl) ⟨409191, by rfl⟩ : syracuseStep 1091177 = 818383) B818383
theorem B730991 : Blo 483789 730991 := bstep (se 1 (by rfl) ⟨548243, by rfl⟩ : syracuseStep 730991 = 1096487) B1096487
theorem B2402207 : Blo 483789 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B731387 : Blo 483789 731387 := bstep (se 1 (by rfl) ⟨548540, by rfl⟩ : syracuseStep 731387 = 1097081) B1097081
theorem B731615 : Blo 483789 731615 := bstep (se 1 (by rfl) ⟨548711, by rfl⟩ : syracuseStep 731615 = 1097423) B1097423
theorem B1845737 : Blo 483789 1845737 := bstep (se 2 (by rfl) ⟨692151, by rfl⟩ : syracuseStep 1845737 = 1384303) B1384303
theorem B1092257 : Blo 483789 1092257 := bstep (se 2 (by rfl) ⟨409596, by rfl⟩ : syracuseStep 1092257 = 819193) B819193
theorem B7187297 : Blo 483789 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B1092635 : Blo 483789 1092635 := bstep (se 1 (by rfl) ⟨819476, by rfl⟩ : syracuseStep 1092635 = 1638953) B1638953
theorem B1092815 : Blo 483789 1092815 := bstep (se 1 (by rfl) ⟨819611, by rfl⟩ : syracuseStep 1092815 = 1639223) B1639223
theorem B7450015 : Blo 483789 7450015 := bstep (se 1 (by rfl) ⟨5587511, by rfl⟩ : syracuseStep 7450015 = 11175023) B11175023
theorem B1093985 : Blo 483789 1093985 := bstep (se 2 (by rfl) ⟨410244, by rfl⟩ : syracuseStep 1093985 = 820489) B820489
theorem B15708653 : Blo 483789 15708653 := bstep (se 3 (by rfl) ⟨2945372, by rfl⟩ : syracuseStep 15708653 = 5890745) B5890745
theorem B1061857 : Blo 483789 1061857 := bstep (se 2 (by rfl) ⟨398196, by rfl⟩ : syracuseStep 1061857 = 796393) B796393
theorem B14922791 : Blo 483789 14922791 := bstep (se 1 (by rfl) ⟨11192093, by rfl⟩ : syracuseStep 14922791 = 22384187) B22384187
theorem B2340049 : Blo 483789 2340049 := bstep (se 2 (by rfl) ⟨877518, by rfl⟩ : syracuseStep 2340049 = 1755037) B1755037
theorem B3028291 : Blo 483789 3028291 := bstep (se 1 (by rfl) ⟨2271218, by rfl⟩ : syracuseStep 3028291 = 4542437) B4542437
theorem B1750511 : Blo 483789 1750511 := bstep (se 1 (by rfl) ⟨1312883, by rfl⟩ : syracuseStep 1750511 = 2625767) B2625767
theorem B7452157 : Blo 483789 7452157 := bstep (se 3 (by rfl) ⟨1397279, by rfl⟩ : syracuseStep 7452157 = 2794559) B2794559
theorem B1226623 : Blo 483789 1226623 := bstep (se 1 (by rfl) ⟨919967, by rfl⟩ : syracuseStep 1226623 = 1839935) B1839935
theorem B1095551 : Blo 483789 1095551 := bstep (se 1 (by rfl) ⟨821663, by rfl⟩ : syracuseStep 1095551 = 1643327) B1643327
theorem B2964059 : Blo 483789 2964059 := bstep (se 1 (by rfl) ⟨2223044, by rfl⟩ : syracuseStep 2964059 = 4446089) B4446089
theorem B1555163 : Blo 483789 1555163 := bstep (se 1 (by rfl) ⟨1166372, by rfl⟩ : syracuseStep 1555163 = 2332745) B2332745
theorem B1097063 : Blo 483789 1097063 := bstep (se 1 (by rfl) ⟨822797, by rfl⟩ : syracuseStep 1097063 = 1645595) B1645595
theorem B6569723 : Blo 483789 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B1851599 : Blo 483789 1851599 := bstep (se 1 (by rfl) ⟨1388699, by rfl⟩ : syracuseStep 1851599 = 2777399) B2777399
theorem B6242791 : Blo 483789 6242791 := bstep (se 1 (by rfl) ⟨4682093, by rfl⟩ : syracuseStep 6242791 = 9364187) B9364187
theorem B6243155 : Blo 483789 6243155 := bstep (se 1 (by rfl) ⟨4682366, by rfl⟩ : syracuseStep 6243155 = 9364733) B9364733
theorem B1230137 : Blo 483789 1230137 := bstep (se 2 (by rfl) ⟨461301, by rfl⟩ : syracuseStep 1230137 = 922603) B922603
theorem B7030475 : Blo 483789 7030475 := bstep (se 1 (by rfl) ⟨5272856, by rfl⟩ : syracuseStep 7030475 = 10545713) B10545713
theorem B105171209 : Blo 483789 105171209 := bstep (se 2 (by rfl) ⟨39439203, by rfl⟩ : syracuseStep 105171209 = 78878407) B78878407
theorem B1231159 : Blo 483789 1231159 := bstep (se 1 (by rfl) ⟨923369, by rfl⟩ : syracuseStep 1231159 = 1846739) B1846739
theorem B1232567 : Blo 483789 1232567 := bstep (se 1 (by rfl) ⟨924425, by rfl⟩ : syracuseStep 1232567 = 1848851) B1848851
theorem B741545 : Blo 483789 741545 := bstep (se 2 (by rfl) ⟨278079, by rfl⟩ : syracuseStep 741545 = 556159) B556159
theorem B1233407 : Blo 483789 1233407 := bstep (se 1 (by rfl) ⟨925055, by rfl⟩ : syracuseStep 1233407 = 1850111) B1850111
theorem B5919355 : Blo 483789 5919355 := bstep (se 1 (by rfl) ⟨4439516, by rfl⟩ : syracuseStep 5919355 = 8879033) B8879033
theorem B8969069 : Blo 483789 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B548455 : Blo 483789 548455 := bstep (se 1 (by rfl) ⟨411341, by rfl⟩ : syracuseStep 548455 = 822683) B822683
theorem B12640139 : Blo 483789 12640139 := bstep (se 1 (by rfl) ⟨9480104, by rfl⟩ : syracuseStep 12640139 = 18960209) B18960209
theorem B23683265 : Blo 483789 23683265 := bstep (se 2 (by rfl) ⟨8881224, by rfl⟩ : syracuseStep 23683265 = 17762449) B17762449
theorem B483995 : Blo 483789 483995 := bstep (se 1 (by rfl) ⟨362996, by rfl⟩ : syracuseStep 483995 = 725993) B725993
theorem B484031 : Blo 483789 484031 := bstep (se 1 (by rfl) ⟨363023, by rfl⟩ : syracuseStep 484031 = 726047) B726047
theorem B484735 : Blo 483789 484735 := bstep (se 1 (by rfl) ⟨363551, by rfl⟩ : syracuseStep 484735 = 727103) B727103
theorem B3696029 : Blo 483789 3696029 := bstep (se 3 (by rfl) ⟨693005, by rfl⟩ : syracuseStep 3696029 = 1386011) B1386011
theorem B484847 : Blo 483789 484847 := bstep (se 1 (by rfl) ⟨363635, by rfl⟩ : syracuseStep 484847 = 727271) B727271
theorem B878759 : Blo 483789 878759 := bstep (se 1 (by rfl) ⟨659069, by rfl⟩ : syracuseStep 878759 = 1318139) B1318139
theorem B1632905 : Blo 483789 1632905 := bstep (se 2 (by rfl) ⟨612339, by rfl⟩ : syracuseStep 1632905 = 1224679) B1224679
theorem B486047 : Blo 483789 486047 := bstep (se 1 (by rfl) ⟨364535, by rfl⟩ : syracuseStep 486047 = 729071) B729071
theorem B486079 : Blo 483789 486079 := bstep (se 1 (by rfl) ⟨364559, by rfl⟩ : syracuseStep 486079 = 729119) B729119
theorem B486207 : Blo 483789 486207 := bstep (se 1 (by rfl) ⟨364655, by rfl⟩ : syracuseStep 486207 = 729311) B729311
theorem B486503 : Blo 483789 486503 := bstep (se 1 (by rfl) ⟨364877, by rfl⟩ : syracuseStep 486503 = 729755) B729755
theorem B1633391 : Blo 483789 1633391 := bstep (se 1 (by rfl) ⟨1225043, by rfl⟩ : syracuseStep 1633391 = 2450087) B2450087
theorem B1863071 : Blo 483789 1863071 := bstep (se 1 (by rfl) ⟨1397303, by rfl⟩ : syracuseStep 1863071 = 2794607) B2794607
theorem B1633823 : Blo 483789 1633823 := bstep (se 1 (by rfl) ⟨1225367, by rfl⟩ : syracuseStep 1633823 = 2450735) B2450735
theorem B487067 : Blo 483789 487067 := bstep (se 1 (by rfl) ⟨365300, by rfl⟩ : syracuseStep 487067 = 730601) B730601
theorem B6975163 : Blo 483789 6975163 := bstep (se 1 (by rfl) ⟨5231372, by rfl⟩ : syracuseStep 6975163 = 10462745) B10462745
theorem B487535 : Blo 483789 487535 := bstep (se 1 (by rfl) ⟨365651, by rfl⟩ : syracuseStep 487535 = 731303) B731303
theorem B520831 : Blo 483789 520831 := bstep (se 1 (by rfl) ⟨390623, by rfl⟩ : syracuseStep 520831 = 781247) B781247
theorem B2454461 : Blo 483789 2454461 := bstep (se 3 (by rfl) ⟨460211, by rfl⟩ : syracuseStep 2454461 = 920423) B920423
theorem B4192019 : Blo 483789 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B980819 : Blo 483789 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B1636199 : Blo 483789 1636199 := bstep (se 1 (by rfl) ⟨1227149, by rfl⟩ : syracuseStep 1636199 = 2454299) B2454299
theorem B3504167 : Blo 483789 3504167 := bstep (se 1 (by rfl) ⟨2628125, by rfl⟩ : syracuseStep 3504167 = 5256251) B5256251
theorem B1636415 : Blo 483789 1636415 := bstep (se 1 (by rfl) ⟨1227311, by rfl⟩ : syracuseStep 1636415 = 2454623) B2454623
theorem B1801183 : Blo 483789 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B1638575 : Blo 483789 1638575 := bstep (se 1 (by rfl) ⟨1228931, by rfl⟩ : syracuseStep 1638575 = 2457863) B2457863
theorem B2458025 : Blo 483789 2458025 := bstep (se 2 (by rfl) ⟨921759, by rfl⟩ : syracuseStep 2458025 = 1843519) B1843519
theorem B116490761 : Blo 483789 116490761 := bstep (se 2 (by rfl) ⟨43684035, by rfl⟩ : syracuseStep 116490761 = 87368071) B87368071
theorem B4162103 : Blo 483789 4162103 := bstep (se 1 (by rfl) ⟨3121577, by rfl⟩ : syracuseStep 4162103 = 6243155) B6243155
theorem B8323721 : Blo 483789 8323721 := bstep (se 2 (by rfl) ⟨3121395, by rfl⟩ : syracuseStep 8323721 = 6242791) B6242791
theorem B4981481 : Blo 483789 4981481 := bstep (se 2 (by rfl) ⟨1868055, by rfl⟩ : syracuseStep 4981481 = 3736111) B3736111
theorem B820091 : Blo 483789 820091 := bstep (se 1 (by rfl) ⟨615068, by rfl⟩ : syracuseStep 820091 = 1230137) B1230137
theorem B4686983 : Blo 483789 4686983 := bstep (se 1 (by rfl) ⟨3515237, by rfl⟩ : syracuseStep 4686983 = 7030475) B7030475
theorem B7865743 : Blo 483789 7865743 := bstep (se 1 (by rfl) ⟨5899307, by rfl⟩ : syracuseStep 7865743 = 11798615) B11798615
theorem B4982435 : Blo 483789 4982435 := bstep (se 1 (by rfl) ⟨3736826, by rfl⟩ : syracuseStep 4982435 = 7473653) B7473653
theorem B4655303 : Blo 483789 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B821711 : Blo 483789 821711 := bstep (se 1 (by rfl) ⟨616283, by rfl⟩ : syracuseStep 821711 = 1232567) B1232567
theorem B494363 : Blo 483789 494363 := bstep (se 1 (by rfl) ⟨370772, by rfl⟩ : syracuseStep 494363 = 741545) B741545
theorem B822271 : Blo 483789 822271 := bstep (se 1 (by rfl) ⟨616703, by rfl⟩ : syracuseStep 822271 = 1233407) B1233407
theorem B1641545 : Blo 483789 1641545 := bstep (se 2 (by rfl) ⟨615579, by rfl⟩ : syracuseStep 1641545 = 1231159) B1231159
theorem B920879 : Blo 483789 920879 := bstep (se 1 (by rfl) ⟨690659, by rfl⟩ : syracuseStep 920879 = 1381319) B1381319
theorem B987079 : Blo 483789 987079 := bstep (se 1 (by rfl) ⟨740309, by rfl⟩ : syracuseStep 987079 = 1480619) B1480619
theorem B9933353 : Blo 483789 9933353 := bstep (se 2 (by rfl) ⟨3725007, by rfl⟩ : syracuseStep 9933353 = 7450015) B7450015
theorem B8426759 : Blo 483789 8426759 := bstep (se 1 (by rfl) ⟨6320069, by rfl⟩ : syracuseStep 8426759 = 12640139) B12640139
theorem B726767 : Blo 483789 726767 := bstep (se 1 (by rfl) ⟨545075, by rfl⟩ : syracuseStep 726767 = 1090151) B1090151
theorem B694441 : Blo 483789 694441 := bstep (se 2 (by rfl) ⟨260415, by rfl⟩ : syracuseStep 694441 = 520831) B520831
theorem B2464019 : Blo 483789 2464019 := bstep (se 1 (by rfl) ⟨1848014, by rfl⟩ : syracuseStep 2464019 = 3696029) B3696029
theorem B727451 : Blo 483789 727451 := bstep (se 1 (by rfl) ⟨545588, by rfl⟩ : syracuseStep 727451 = 1091177) B1091177
theorem B1415809 : Blo 483789 1415809 := bstep (se 2 (by rfl) ⟨530928, by rfl⟩ : syracuseStep 1415809 = 1061857) B1061857
theorem B3120065 : Blo 483789 3120065 := bstep (se 2 (by rfl) ⟨1170024, by rfl⟩ : syracuseStep 3120065 = 2340049) B2340049
theorem B1088603 : Blo 483789 1088603 := bstep (se 1 (by rfl) ⟨816452, by rfl⟩ : syracuseStep 1088603 = 1632905) B1632905
theorem B728171 : Blo 483789 728171 := bstep (se 1 (by rfl) ⟨546128, by rfl⟩ : syracuseStep 728171 = 1092257) B1092257
theorem B9936209 : Blo 483789 9936209 := bstep (se 2 (by rfl) ⟨3726078, by rfl⟩ : syracuseStep 9936209 = 7452157) B7452157
theorem B728423 : Blo 483789 728423 := bstep (se 1 (by rfl) ⟨546317, by rfl⟩ : syracuseStep 728423 = 1092635) B1092635
theorem B1088927 : Blo 483789 1088927 := bstep (se 1 (by rfl) ⟨816695, by rfl⟩ : syracuseStep 1088927 = 1633391) B1633391
theorem B728543 : Blo 483789 728543 := bstep (se 1 (by rfl) ⟨546407, by rfl⟩ : syracuseStep 728543 = 1092815) B1092815
theorem B1089215 : Blo 483789 1089215 := bstep (se 1 (by rfl) ⟨816911, by rfl⟩ : syracuseStep 1089215 = 1633823) B1633823
theorem B729323 : Blo 483789 729323 := bstep (se 1 (by rfl) ⟨546992, by rfl⟩ : syracuseStep 729323 = 1093985) B1093985
theorem B2794679 : Blo 483789 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B1090799 : Blo 483789 1090799 := bstep (se 1 (by rfl) ⟨818099, by rfl⟩ : syracuseStep 1090799 = 1636199) B1636199
theorem B730367 : Blo 483789 730367 := bstep (se 1 (by rfl) ⟨547775, by rfl⟩ : syracuseStep 730367 = 1095551) B1095551
theorem B2401577 : Blo 483789 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B2336111 : Blo 483789 2336111 := bstep (se 1 (by rfl) ⟨1752083, by rfl⟩ : syracuseStep 2336111 = 3504167) B3504167
theorem B1090943 : Blo 483789 1090943 := bstep (se 1 (by rfl) ⟨818207, by rfl⟩ : syracuseStep 1090943 = 1636415) B1636415
theorem B1976039 : Blo 483789 1976039 := bstep (se 1 (by rfl) ⟨1482029, by rfl⟩ : syracuseStep 1976039 = 2964059) B2964059
theorem B731273 : Blo 483789 731273 := bstep (se 2 (by rfl) ⟨274227, by rfl⟩ : syracuseStep 731273 = 548455) B548455
theorem B731375 : Blo 483789 731375 := bstep (se 1 (by rfl) ⟨548531, by rfl⟩ : syracuseStep 731375 = 1097063) B1097063
theorem B2075327 : Blo 483789 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B1092329 : Blo 483789 1092329 := bstep (se 2 (by rfl) ⟨409623, by rfl⟩ : syracuseStep 1092329 = 819247) B819247
theorem B827370449 : Blo 483789 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B1846253 : Blo 483789 1846253 := bstep (se 3 (by rfl) ⟨346172, by rfl⟩ : syracuseStep 1846253 = 692345) B692345
theorem B1092905 : Blo 483789 1092905 := bstep (se 2 (by rfl) ⟨409839, by rfl⟩ : syracuseStep 1092905 = 819679) B819679
theorem B1093103 : Blo 483789 1093103 := bstep (se 1 (by rfl) ⟨819827, by rfl⟩ : syracuseStep 1093103 = 1639655) B1639655
theorem B5254901 : Blo 483789 5254901 := bstep (se 5 (by rfl) ⟨246323, by rfl⟩ : syracuseStep 5254901 = 492647) B492647
theorem B1224659 : Blo 483789 1224659 := bstep (se 1 (by rfl) ⟨918494, by rfl⟩ : syracuseStep 1224659 = 1836989) B1836989
theorem B1094255 : Blo 483789 1094255 := bstep (se 1 (by rfl) ⟨820691, by rfl⟩ : syracuseStep 1094255 = 1641383) B1641383
theorem B1094777 : Blo 483789 1094777 := bstep (se 2 (by rfl) ⟨410541, by rfl⟩ : syracuseStep 1094777 = 821083) B821083
theorem B3159205 : Blo 483789 3159205 := bstep (se 4 (by rfl) ⟨296175, by rfl⟩ : syracuseStep 3159205 = 592351) B592351
theorem B1226927 : Blo 483789 1226927 := bstep (se 1 (by rfl) ⟨920195, by rfl⟩ : syracuseStep 1226927 = 1840391) B1840391
theorem B4668029 : Blo 483789 4668029 := bstep (se 3 (by rfl) ⟨875255, by rfl⟩ : syracuseStep 4668029 = 1750511) B1750511
theorem B1096703 : Blo 483789 1096703 := bstep (se 1 (by rfl) ⟨822527, by rfl⟩ : syracuseStep 1096703 = 1645055) B1645055
theorem B1096811 : Blo 483789 1096811 := bstep (se 1 (by rfl) ⟨822608, by rfl⟩ : syracuseStep 1096811 = 1645217) B1645217
theorem B5979379 : Blo 483789 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B1228031 : Blo 483789 1228031 := bstep (se 1 (by rfl) ⟨921023, by rfl⟩ : syracuseStep 1228031 = 1842047) B1842047
theorem B64603541 : Blo 483789 64603541 := bstep (se 6 (by rfl) ⟨1514145, by rfl⟩ : syracuseStep 64603541 = 3028291) B3028291
theorem B1230491 : Blo 483789 1230491 := bstep (se 1 (by rfl) ⟨922868, by rfl⟩ : syracuseStep 1230491 = 1845737) B1845737
theorem B10472435 : Blo 483789 10472435 := bstep (se 1 (by rfl) ⟨7854326, by rfl⟩ : syracuseStep 10472435 = 15708653) B15708653
theorem B9948527 : Blo 483789 9948527 := bstep (se 1 (by rfl) ⟨7461395, by rfl⟩ : syracuseStep 9948527 = 14922791) B14922791
theorem B76664501 : Blo 483789 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B1036775 : Blo 483789 1036775 := bstep (se 1 (by rfl) ⟨777581, by rfl⟩ : syracuseStep 1036775 = 1555163) B1555163
theorem B4379815 : Blo 483789 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B2774483 : Blo 483789 2774483 := bstep (se 1 (by rfl) ⟨2080862, by rfl⟩ : syracuseStep 2774483 = 4161725) B4161725
theorem B1234399 : Blo 483789 1234399 := bstep (se 1 (by rfl) ⟨925799, by rfl⟩ : syracuseStep 1234399 = 1851599) B1851599
theorem B546511 : Blo 483789 546511 := bstep (se 1 (by rfl) ⟨409883, by rfl⟩ : syracuseStep 546511 = 819767) B819767
theorem B8869985 : Blo 483789 8869985 := bstep (se 2 (by rfl) ⟨3326244, by rfl⟩ : syracuseStep 8869985 = 6652489) B6652489
theorem B547375 : Blo 483789 547375 := bstep (se 1 (by rfl) ⟨410531, by rfl⟩ : syracuseStep 547375 = 821063) B821063
theorem B547483 : Blo 483789 547483 := bstep (se 1 (by rfl) ⟨410612, by rfl⟩ : syracuseStep 547483 = 821225) B821225
theorem B70114139 : Blo 483789 70114139 := bstep (se 1 (by rfl) ⟨52585604, by rfl⟩ : syracuseStep 70114139 = 105171209) B105171209
theorem B2310757303 : Blo 483789 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B548383 : Blo 483789 548383 := bstep (se 1 (by rfl) ⟨411287, by rfl⟩ : syracuseStep 548383 = 822575) B822575
theorem B614567 : Blo 483789 614567 := bstep (se 1 (by rfl) ⟨460925, by rfl⟩ : syracuseStep 614567 = 921851) B921851
theorem B614891 : Blo 483789 614891 := bstep (se 1 (by rfl) ⟨461168, by rfl⟩ : syracuseStep 614891 = 922337) B922337
theorem B484159 : Blo 483789 484159 := bstep (se 1 (by rfl) ⟨363119, by rfl⟩ : syracuseStep 484159 = 726239) B726239
theorem B484199 : Blo 483789 484199 := bstep (se 1 (by rfl) ⟨363149, by rfl⟩ : syracuseStep 484199 = 726299) B726299
theorem B484479 : Blo 483789 484479 := bstep (se 1 (by rfl) ⟨363359, by rfl⟩ : syracuseStep 484479 = 726719) B726719
theorem B1926281 : Blo 483789 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B485247 : Blo 483789 485247 := bstep (se 1 (by rfl) ⟨363935, by rfl⟩ : syracuseStep 485247 = 727871) B727871
theorem B485543 : Blo 483789 485543 := bstep (se 1 (by rfl) ⟨364157, by rfl⟩ : syracuseStep 485543 = 728315) B728315
theorem B485607 : Blo 483789 485607 := bstep (se 1 (by rfl) ⟨364205, by rfl⟩ : syracuseStep 485607 = 728411) B728411
theorem B9300217 : Blo 483789 9300217 := bstep (se 2 (by rfl) ⟨3487581, by rfl⟩ : syracuseStep 9300217 = 6975163) B6975163
theorem B2452193 : Blo 483789 2452193 := bstep (se 2 (by rfl) ⟨919572, by rfl⟩ : syracuseStep 2452193 = 1839145) B1839145
theorem B486127 : Blo 483789 486127 := bstep (se 1 (by rfl) ⟨364595, by rfl⟩ : syracuseStep 486127 = 729191) B729191
theorem B15788843 : Blo 483789 15788843 := bstep (se 1 (by rfl) ⟨11841632, by rfl⟩ : syracuseStep 15788843 = 23683265) B23683265
theorem B486247 : Blo 483789 486247 := bstep (se 1 (by rfl) ⟨364685, by rfl⟩ : syracuseStep 486247 = 729371) B729371
theorem B486271 : Blo 483789 486271 := bstep (se 1 (by rfl) ⟨364703, by rfl⟩ : syracuseStep 486271 = 729407) B729407
theorem B486815 : Blo 483789 486815 := bstep (se 1 (by rfl) ⟨365111, by rfl⟩ : syracuseStep 486815 = 730223) B730223
theorem B7892473 : Blo 483789 7892473 := bstep (se 2 (by rfl) ⟨2959677, by rfl⟩ : syracuseStep 7892473 = 5919355) B5919355
theorem B487327 : Blo 483789 487327 := bstep (se 1 (by rfl) ⟨365495, by rfl⟩ : syracuseStep 487327 = 730991) B730991
theorem B1601471 : Blo 483789 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B585839 : Blo 483789 585839 := bstep (se 1 (by rfl) ⟨439379, by rfl⟩ : syracuseStep 585839 = 878759) B878759
theorem B487591 : Blo 483789 487591 := bstep (se 1 (by rfl) ⟨365693, by rfl⟩ : syracuseStep 487591 = 731387) B731387
theorem B487743 : Blo 483789 487743 := bstep (se 1 (by rfl) ⟨365807, by rfl⟩ : syracuseStep 487743 = 731615) B731615
theorem B1242047 : Blo 483789 1242047 := bstep (se 1 (by rfl) ⟨931535, by rfl⟩ : syracuseStep 1242047 = 1863071) B1863071
theorem B1635497 : Blo 483789 1635497 := bstep (se 2 (by rfl) ⟨613311, by rfl⟩ : syracuseStep 1635497 = 1226623) B1226623
theorem B3110633 : Blo 483789 3110633 := bstep (se 2 (by rfl) ⟨1166487, by rfl⟩ : syracuseStep 3110633 = 2332975) B2332975
theorem B1636307 : Blo 483789 1636307 := bstep (se 1 (by rfl) ⟨1227230, by rfl⟩ : syracuseStep 1636307 = 2454461) B2454461
theorem B653879 : Blo 483789 653879 := bstep (se 1 (by rfl) ⟨490409, by rfl⟩ : syracuseStep 653879 = 980819) B980819
theorem B1638683 : Blo 483789 1638683 := bstep (se 1 (by rfl) ⟨1229012, by rfl⟩ : syracuseStep 1638683 = 2458025) B2458025
theorem B77660507 : Blo 483789 77660507 := bstep (se 1 (by rfl) ⟨58245380, by rfl⟩ : syracuseStep 77660507 = 116490761) B116490761
theorem B1638845 : Blo 483789 1638845 := bstep (se 3 (by rfl) ⟨307283, by rfl⟩ : syracuseStep 1638845 = 614567) B614567
theorem B820327 : Blo 483789 820327 := bstep (se 1 (by rfl) ⟨615245, by rfl⟩ : syracuseStep 820327 = 1230491) B1230491
theorem B1639709 : Blo 483789 1639709 := bstep (se 3 (by rfl) ⟨307445, by rfl⟩ : syracuseStep 1639709 = 614891) B614891
theorem B10487657 : Blo 483789 10487657 := bstep (se 2 (by rfl) ⟨3932871, by rfl⟩ : syracuseStep 10487657 = 7865743) B7865743
theorem B6981623 : Blo 483789 6981623 := bstep (se 1 (by rfl) ⟨5236217, by rfl⟩ : syracuseStep 6981623 = 10472435) B10472435
theorem B691183 : Blo 483789 691183 := bstep (se 1 (by rfl) ⟨518387, by rfl⟩ : syracuseStep 691183 = 1036775) B1036775
theorem B6622235 : Blo 483789 6622235 := bstep (se 1 (by rfl) ⟨4966676, by rfl⟩ : syracuseStep 6622235 = 9933353) B9933353
theorem B1642679 : Blo 483789 1642679 := bstep (se 1 (by rfl) ⟨1232009, by rfl⟩ : syracuseStep 1642679 = 2464019) B2464019
theorem B10523297 : Blo 483789 10523297 := bstep (se 2 (by rfl) ⟨3946236, by rfl⟩ : syracuseStep 10523297 = 7892473) B7892473
theorem B725735 : Blo 483789 725735 := bstep (se 1 (by rfl) ⟨544301, by rfl⟩ : syracuseStep 725735 = 1088603) B1088603
theorem B6624139 : Blo 483789 6624139 := bstep (se 1 (by rfl) ⟨4968104, by rfl⟩ : syracuseStep 6624139 = 9936209) B9936209
theorem B725951 : Blo 483789 725951 := bstep (se 1 (by rfl) ⟨544463, by rfl⟩ : syracuseStep 725951 = 1088927) B1088927
theorem B726143 : Blo 483789 726143 := bstep (se 1 (by rfl) ⟨544607, by rfl⟩ : syracuseStep 726143 = 1089215) B1089215
theorem B1316105 : Blo 483789 1316105 := bstep (se 2 (by rfl) ⟨493539, by rfl⟩ : syracuseStep 1316105 = 987079) B987079
theorem B1284187 : Blo 483789 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B727199 : Blo 483789 727199 := bstep (se 1 (by rfl) ⟨545399, by rfl⟩ : syracuseStep 727199 = 1090799) B1090799
theorem B16849093 : Blo 483789 16849093 := bstep (se 4 (by rfl) ⟨1579602, by rfl⟩ : syracuseStep 16849093 = 3159205) B3159205
theorem B727295 : Blo 483789 727295 := bstep (se 1 (by rfl) ⟨545471, by rfl⟩ : syracuseStep 727295 = 1090943) B1090943
theorem B1317359 : Blo 483789 1317359 := bstep (se 1 (by rfl) ⟨988019, by rfl⟩ : syracuseStep 1317359 = 1976039) B1976039
theorem B1743677 : Blo 483789 1743677 := bstep (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) B653879
theorem B1383551 : Blo 483789 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B728219 : Blo 483789 728219 := bstep (se 1 (by rfl) ⟨546164, by rfl⟩ : syracuseStep 728219 = 1092329) B1092329
theorem B10525895 : Blo 483789 10525895 := bstep (se 1 (by rfl) ⟨7894421, by rfl⟩ : syracuseStep 10525895 = 15788843) B15788843
theorem B1645865 : Blo 483789 1645865 := bstep (se 2 (by rfl) ⟨617199, by rfl⟩ : syracuseStep 1645865 = 1234399) B1234399
theorem B1318301 : Blo 483789 1318301 := bstep (se 3 (by rfl) ⟨247181, by rfl⟩ : syracuseStep 1318301 = 494363) B494363
theorem B728603 : Blo 483789 728603 := bstep (se 1 (by rfl) ⟨546452, by rfl⟩ : syracuseStep 728603 = 1092905) B1092905
theorem B728681 : Blo 483789 728681 := bstep (se 2 (by rfl) ⟨273255, by rfl⟩ : syracuseStep 728681 = 546511) B546511
theorem B728735 : Blo 483789 728735 := bstep (se 1 (by rfl) ⟨546551, by rfl⟩ : syracuseStep 728735 = 1093103) B1093103
theorem B925921 : Blo 483789 925921 := bstep (se 2 (by rfl) ⟨347220, by rfl⟩ : syracuseStep 925921 = 694441) B694441
theorem B729503 : Blo 483789 729503 := bstep (se 1 (by rfl) ⟨547127, by rfl⟩ : syracuseStep 729503 = 1094255) B1094255
theorem B828031 : Blo 483789 828031 := bstep (se 1 (by rfl) ⟨621023, by rfl⟩ : syracuseStep 828031 = 1242047) B1242047
theorem B729833 : Blo 483789 729833 := bstep (se 2 (by rfl) ⟨273687, by rfl⟩ : syracuseStep 729833 = 547375) B547375
theorem B729851 : Blo 483789 729851 := bstep (se 1 (by rfl) ⟨547388, by rfl⟩ : syracuseStep 729851 = 1094777) B1094777
theorem B1090331 : Blo 483789 1090331 := bstep (se 1 (by rfl) ⟨817748, by rfl⟩ : syracuseStep 1090331 = 1635497) B1635497
theorem B729977 : Blo 483789 729977 := bstep (se 2 (by rfl) ⟨273741, by rfl⟩ : syracuseStep 729977 = 547483) B547483
theorem B2073755 : Blo 483789 2073755 := bstep (se 1 (by rfl) ⟨1555316, by rfl⟩ : syracuseStep 2073755 = 3110633) B3110633
theorem B1090871 : Blo 483789 1090871 := bstep (se 1 (by rfl) ⟨818153, by rfl⟩ : syracuseStep 1090871 = 1636307) B1636307
theorem B7972505 : Blo 483789 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B731135 : Blo 483789 731135 := bstep (se 1 (by rfl) ⟨548351, by rfl⟩ : syracuseStep 731135 = 1096703) B1096703
theorem B731177 : Blo 483789 731177 := bstep (se 2 (by rfl) ⟨274191, by rfl⟩ : syracuseStep 731177 = 548383) B548383
theorem B731207 : Blo 483789 731207 := bstep (se 1 (by rfl) ⟨548405, by rfl⟩ : syracuseStep 731207 = 1096811) B1096811
theorem B4270589 : Blo 483789 4270589 := bstep (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) B1601471
theorem B1092383 : Blo 483789 1092383 := bstep (se 1 (by rfl) ⟨819287, by rfl⟩ : syracuseStep 1092383 = 1638575) B1638575
theorem B5549147 : Blo 483789 5549147 := bstep (se 1 (by rfl) ⟨4161860, by rfl⟩ : syracuseStep 5549147 = 8323721) B8323721
theorem B3124655 : Blo 483789 3124655 := bstep (se 1 (by rfl) ⟨2343491, by rfl⟩ : syracuseStep 3124655 = 4686983) B4686983
theorem B43069027 : Blo 483789 43069027 := bstep (se 1 (by rfl) ⟨32301770, by rfl⟩ : syracuseStep 43069027 = 64603541) B64603541
theorem B3321623 : Blo 483789 3321623 := bstep (se 1 (by rfl) ⟨2491217, by rfl⟩ : syracuseStep 3321623 = 4982435) B4982435
theorem B1094363 : Blo 483789 1094363 := bstep (se 1 (by rfl) ⟨820772, by rfl⟩ : syracuseStep 1094363 = 1641545) B1641545
theorem B6632351 : Blo 483789 6632351 := bstep (se 1 (by rfl) ⟨4974263, by rfl⟩ : syracuseStep 6632351 = 9948527) B9948527
theorem B12400289 : Blo 483789 12400289 := bstep (se 2 (by rfl) ⟨4650108, by rfl⟩ : syracuseStep 12400289 = 9300217) B9300217
theorem B1849655 : Blo 483789 1849655 := bstep (se 1 (by rfl) ⟨1387241, by rfl⟩ : syracuseStep 1849655 = 2774483) B2774483
theorem B1096361 : Blo 483789 1096361 := bstep (se 2 (by rfl) ⟨411135, by rfl⟩ : syracuseStep 1096361 = 822271) B822271
theorem B5913323 : Blo 483789 5913323 := bstep (se 1 (by rfl) ⟨4434992, by rfl⟩ : syracuseStep 5913323 = 8869985) B8869985
theorem B46742759 : Blo 483789 46742759 := bstep (se 1 (by rfl) ⟨35057069, by rfl⟩ : syracuseStep 46742759 = 70114139) B70114139
theorem B2080043 : Blo 483789 2080043 := bstep (se 1 (by rfl) ⟨1560032, by rfl⟩ : syracuseStep 2080043 = 3120065) B3120065
theorem B1557407 : Blo 483789 1557407 := bstep (se 1 (by rfl) ⟨1168055, by rfl⟩ : syracuseStep 1557407 = 2336111) B2336111
theorem B1230835 : Blo 483789 1230835 := bstep (se 1 (by rfl) ⟨923126, by rfl⟩ : syracuseStep 1230835 = 1846253) B1846253
theorem B53135797 : Blo 483789 53135797 := bstep (se 5 (by rfl) ⟨2490740, by rfl⟩ : syracuseStep 53135797 = 4981481) B4981481
theorem B1887745 : Blo 483789 1887745 := bstep (se 2 (by rfl) ⟨707904, by rfl⟩ : syracuseStep 1887745 = 1415809) B1415809
theorem B1562237 : Blo 483789 1562237 := bstep (se 3 (by rfl) ⟨292919, by rfl⟩ : syracuseStep 1562237 = 585839) B585839
theorem B2774735 : Blo 483789 2774735 := bstep (se 1 (by rfl) ⟨2081051, by rfl⟩ : syracuseStep 2774735 = 4162103) B4162103
theorem B546727 : Blo 483789 546727 := bstep (se 1 (by rfl) ⟨410045, by rfl⟩ : syracuseStep 546727 = 820091) B820091
theorem B3103535 : Blo 483789 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B547807 : Blo 483789 547807 := bstep (se 1 (by rfl) ⟨410855, by rfl⟩ : syracuseStep 547807 = 821711) B821711
theorem B613919 : Blo 483789 613919 := bstep (se 1 (by rfl) ⟨460439, by rfl⟩ : syracuseStep 613919 = 920879) B920879
theorem B51109667 : Blo 483789 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B22471357 : Blo 483789 22471357 := bstep (se 3 (by rfl) ⟨4213379, by rfl⟩ : syracuseStep 22471357 = 8426759) B8426759
theorem B484511 : Blo 483789 484511 := bstep (se 1 (by rfl) ⟨363383, by rfl⟩ : syracuseStep 484511 = 726767) B726767
theorem B484967 : Blo 483789 484967 := bstep (se 1 (by rfl) ⟨363725, by rfl⟩ : syracuseStep 484967 = 727451) B727451
theorem B485447 : Blo 483789 485447 := bstep (se 1 (by rfl) ⟨364085, by rfl⟩ : syracuseStep 485447 = 728171) B728171
theorem B485615 : Blo 483789 485615 := bstep (se 1 (by rfl) ⟨364211, by rfl⟩ : syracuseStep 485615 = 728423) B728423
theorem B485695 : Blo 483789 485695 := bstep (se 1 (by rfl) ⟨364271, by rfl⟩ : syracuseStep 485695 = 728543) B728543
theorem B486215 : Blo 483789 486215 := bstep (se 1 (by rfl) ⟨364661, by rfl⟩ : syracuseStep 486215 = 729323) B729323
theorem B1863119 : Blo 483789 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B486911 : Blo 483789 486911 := bstep (se 1 (by rfl) ⟨365183, by rfl⟩ : syracuseStep 486911 = 730367) B730367
theorem B1601051 : Blo 483789 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B23359013 : Blo 483789 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B487515 : Blo 483789 487515 := bstep (se 1 (by rfl) ⟨365636, by rfl⟩ : syracuseStep 487515 = 731273) B731273
theorem B487583 : Blo 483789 487583 := bstep (se 1 (by rfl) ⟨365687, by rfl⟩ : syracuseStep 487583 = 731375) B731375
theorem B1634795 : Blo 483789 1634795 := bstep (se 1 (by rfl) ⟨1226096, by rfl⟩ : syracuseStep 1634795 = 2452193) B2452193
theorem B551580299 : Blo 483789 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B3503267 : Blo 483789 3503267 := bstep (se 1 (by rfl) ⟨2627450, by rfl⟩ : syracuseStep 3503267 = 5254901) B5254901
theorem B816439 : Blo 483789 816439 := bstep (se 1 (by rfl) ⟨612329, by rfl⟩ : syracuseStep 816439 = 1224659) B1224659
theorem B3081009737 : Blo 483789 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B817951 : Blo 483789 817951 := bstep (se 1 (by rfl) ⟨613463, by rfl⟩ : syracuseStep 817951 = 1226927) B1226927
theorem B3112019 : Blo 483789 3112019 := bstep (se 1 (by rfl) ⟨2334014, by rfl⟩ : syracuseStep 3112019 = 4668029) B4668029
theorem B818687 : Blo 483789 818687 := bstep (se 1 (by rfl) ⟨614015, by rfl⟩ : syracuseStep 818687 = 1228031) B1228031
theorem B51773671 : Blo 483789 51773671 := bstep (se 1 (by rfl) ⟨38830253, by rfl⟩ : syracuseStep 51773671 = 77660507) B77660507
theorem B4654415 : Blo 483789 4654415 := bstep (se 1 (by rfl) ⟨3490811, by rfl⟩ : syracuseStep 4654415 = 6981623) B6981623
theorem B1641113 : Blo 483789 1641113 := bstep (se 2 (by rfl) ⟨615417, by rfl⟩ : syracuseStep 1641113 = 1230835) B1230835
theorem B7015531 : Blo 483789 7015531 := bstep (se 1 (by rfl) ⟨5261648, by rfl⟩ : syracuseStep 7015531 = 10523297) B10523297
theorem B70847729 : Blo 483789 70847729 := bstep (se 2 (by rfl) ⟨26567898, by rfl⟩ : syracuseStep 70847729 = 53135797) B53135797
theorem B2069023 : Blo 483789 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B922367 : Blo 483789 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B7017263 : Blo 483789 7017263 := bstep (se 1 (by rfl) ⟨5262947, by rfl⟩ : syracuseStep 7017263 = 10525895) B10525895
theorem B726887 : Blo 483789 726887 := bstep (se 1 (by rfl) ⟨545165, by rfl⟩ : syracuseStep 726887 = 1090331) B1090331
theorem B1382503 : Blo 483789 1382503 := bstep (se 1 (by rfl) ⟨1036877, by rfl⟩ : syracuseStep 1382503 = 2073755) B2073755
theorem B727247 : Blo 483789 727247 := bstep (se 1 (by rfl) ⟨545435, by rfl⟩ : syracuseStep 727247 = 1090871) B1090871
theorem B5315003 : Blo 483789 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B8216025965 : Blo 483789 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B1088585 : Blo 483789 1088585 := bstep (se 2 (by rfl) ⟨408219, by rfl⟩ : syracuseStep 1088585 = 816439) B816439
theorem B728255 : Blo 483789 728255 := bstep (se 1 (by rfl) ⟨546191, by rfl⟩ : syracuseStep 728255 = 1092383) B1092383
theorem B15572675 : Blo 483789 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B728969 : Blo 483789 728969 := bstep (se 2 (by rfl) ⟨273363, by rfl⟩ : syracuseStep 728969 = 546727) B546727
theorem B1712249 : Blo 483789 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B1089863 : Blo 483789 1089863 := bstep (se 1 (by rfl) ⟨817397, by rfl⟩ : syracuseStep 1089863 = 1634795) B1634795
theorem B729575 : Blo 483789 729575 := bstep (se 1 (by rfl) ⟨547181, by rfl⟩ : syracuseStep 729575 = 1094363) B1094363
theorem B2335511 : Blo 483789 2335511 := bstep (se 1 (by rfl) ⟨1751633, by rfl⟩ : syracuseStep 2335511 = 3503267) B3503267
theorem B1090601 : Blo 483789 1090601 := bstep (se 2 (by rfl) ⟨408975, by rfl⟩ : syracuseStep 1090601 = 817951) B817951
theorem B8266859 : Blo 483789 8266859 := bstep (se 1 (by rfl) ⟨6200144, by rfl⟩ : syracuseStep 8266859 = 12400289) B12400289
theorem B730409 : Blo 483789 730409 := bstep (se 2 (by rfl) ⟨273903, by rfl⟩ : syracuseStep 730409 = 547807) B547807
theorem B4269469 : Blo 483789 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B730907 : Blo 483789 730907 := bstep (se 1 (by rfl) ⟨548180, by rfl⟩ : syracuseStep 730907 = 1096361) B1096361
theorem B3942215 : Blo 483789 3942215 := bstep (se 1 (by rfl) ⟨2956661, by rfl⟩ : syracuseStep 3942215 = 5913323) B5913323
theorem B2074679 : Blo 483789 2074679 := bstep (se 1 (by rfl) ⟨1556009, by rfl⟩ : syracuseStep 2074679 = 3112019) B3112019
theorem B1386695 : Blo 483789 1386695 := bstep (se 1 (by rfl) ⟨1040021, by rfl⟩ : syracuseStep 1386695 = 2080043) B2080043
theorem B1092455 : Blo 483789 1092455 := bstep (se 1 (by rfl) ⟨819341, by rfl⟩ : syracuseStep 1092455 = 1638683) B1638683
theorem B1092563 : Blo 483789 1092563 := bstep (se 1 (by rfl) ⟨819422, by rfl⟩ : syracuseStep 1092563 = 1638845) B1638845
theorem B1093139 : Blo 483789 1093139 := bstep (se 1 (by rfl) ⟨819854, by rfl⟩ : syracuseStep 1093139 = 1639709) B1639709
theorem B29961809 : Blo 483789 29961809 := bstep (se 2 (by rfl) ⟨11235678, by rfl⟩ : syracuseStep 29961809 = 22471357) B22471357
theorem B6991771 : Blo 483789 6991771 := bstep (se 1 (by rfl) ⟨5243828, by rfl⟩ : syracuseStep 6991771 = 10487657) B10487657
theorem B1093769 : Blo 483789 1093769 := bstep (se 2 (by rfl) ⟨410163, by rfl⟩ : syracuseStep 1093769 = 820327) B820327
theorem B1095119 : Blo 483789 1095119 := bstep (se 1 (by rfl) ⟨821339, by rfl⟩ : syracuseStep 1095119 = 1642679) B1642679
theorem B1849823 : Blo 483789 1849823 := bstep (se 1 (by rfl) ⟨1387367, by rfl⟩ : syracuseStep 1849823 = 2774735) B2774735
theorem B1162451 : Blo 483789 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B57425369 : Blo 483789 57425369 := bstep (se 2 (by rfl) ⟨21534513, by rfl⟩ : syracuseStep 57425369 = 43069027) B43069027
theorem B1097243 : Blo 483789 1097243 := bstep (se 1 (by rfl) ⟨822932, by rfl⟩ : syracuseStep 1097243 = 1645865) B1645865
theorem B3686309 : Blo 483789 3686309 := bstep (se 4 (by rfl) ⟨345591, by rfl⟩ : syracuseStep 3686309 = 691183) B691183
theorem B8832185 : Blo 483789 8832185 := bstep (se 2 (by rfl) ⟨3312069, by rfl⟩ : syracuseStep 8832185 = 6624139) B6624139
theorem B2083103 : Blo 483789 2083103 := bstep (se 1 (by rfl) ⟨1562327, by rfl⟩ : syracuseStep 2083103 = 3124655) B3124655
theorem B2214415 : Blo 483789 2214415 := bstep (se 1 (by rfl) ⟨1660811, by rfl⟩ : syracuseStep 2214415 = 3321623) B3321623
theorem B22465457 : Blo 483789 22465457 := bstep (se 2 (by rfl) ⟨8424546, by rfl⟩ : syracuseStep 22465457 = 16849093) B16849093
theorem B4968317 : Blo 483789 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B1233103 : Blo 483789 1233103 := bstep (se 1 (by rfl) ⟨924827, by rfl⟩ : syracuseStep 1233103 = 1849655) B1849655
theorem B545791 : Blo 483789 545791 := bstep (se 1 (by rfl) ⟨409343, by rfl⟩ : syracuseStep 545791 = 818687) B818687
theorem B1234561 : Blo 483789 1234561 := bstep (se 2 (by rfl) ⟨462960, by rfl⟩ : syracuseStep 1234561 = 925921) B925921
theorem B1038271 : Blo 483789 1038271 := bstep (se 1 (by rfl) ⟨778703, by rfl⟩ : syracuseStep 1038271 = 1557407) B1557407
theorem B1104041 : Blo 483789 1104041 := bstep (se 2 (by rfl) ⟨414015, by rfl⟩ : syracuseStep 1104041 = 828031) B828031
theorem B4414823 : Blo 483789 4414823 := bstep (se 1 (by rfl) ⟨3311117, by rfl⟩ : syracuseStep 4414823 = 6622235) B6622235
theorem B483823 : Blo 483789 483823 := bstep (se 1 (by rfl) ⟨362867, by rfl⟩ : syracuseStep 483823 = 725735) B725735
theorem B483967 : Blo 483789 483967 := bstep (se 1 (by rfl) ⟨362975, by rfl⟩ : syracuseStep 483967 = 725951) B725951
theorem B484095 : Blo 483789 484095 := bstep (se 1 (by rfl) ⟨363071, by rfl⟩ : syracuseStep 484095 = 726143) B726143
theorem B877403 : Blo 483789 877403 := bstep (se 1 (by rfl) ⟨658052, by rfl⟩ : syracuseStep 877403 = 1316105) B1316105
theorem B1041491 : Blo 483789 1041491 := bstep (se 1 (by rfl) ⟨781118, by rfl⟩ : syracuseStep 1041491 = 1562237) B1562237
theorem B484799 : Blo 483789 484799 := bstep (se 1 (by rfl) ⟨363599, by rfl⟩ : syracuseStep 484799 = 727199) B727199
theorem B484863 : Blo 483789 484863 := bstep (se 1 (by rfl) ⟨363647, by rfl⟩ : syracuseStep 484863 = 727295) B727295
theorem B878239 : Blo 483789 878239 := bstep (se 1 (by rfl) ⟨658679, by rfl⟩ : syracuseStep 878239 = 1317359) B1317359
theorem B2516993 : Blo 483789 2516993 := bstep (se 2 (by rfl) ⟨943872, by rfl⟩ : syracuseStep 2516993 = 1887745) B1887745
theorem B485479 : Blo 483789 485479 := bstep (se 1 (by rfl) ⟨364109, by rfl⟩ : syracuseStep 485479 = 728219) B728219
theorem B878867 : Blo 483789 878867 := bstep (se 1 (by rfl) ⟨659150, by rfl⟩ : syracuseStep 878867 = 1318301) B1318301
theorem B485735 : Blo 483789 485735 := bstep (se 1 (by rfl) ⟨364301, by rfl⟩ : syracuseStep 485735 = 728603) B728603
theorem B485787 : Blo 483789 485787 := bstep (se 1 (by rfl) ⟨364340, by rfl⟩ : syracuseStep 485787 = 728681) B728681
theorem B485823 : Blo 483789 485823 := bstep (se 1 (by rfl) ⟨364367, by rfl⟩ : syracuseStep 485823 = 728735) B728735
theorem B34073111 : Blo 483789 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B486335 : Blo 483789 486335 := bstep (se 1 (by rfl) ⟨364751, by rfl⟩ : syracuseStep 486335 = 729503) B729503
theorem B486555 : Blo 483789 486555 := bstep (se 1 (by rfl) ⟨364916, by rfl⟩ : syracuseStep 486555 = 729833) B729833
theorem B486567 : Blo 483789 486567 := bstep (se 1 (by rfl) ⟨364925, by rfl⟩ : syracuseStep 486567 = 729851) B729851
theorem B486651 : Blo 483789 486651 := bstep (se 1 (by rfl) ⟨364988, by rfl⟩ : syracuseStep 486651 = 729977) B729977
theorem B487423 : Blo 483789 487423 := bstep (se 1 (by rfl) ⟨365567, by rfl⟩ : syracuseStep 487423 = 731135) B731135
theorem B487451 : Blo 483789 487451 := bstep (se 1 (by rfl) ⟨365588, by rfl⟩ : syracuseStep 487451 = 731177) B731177
theorem B487471 : Blo 483789 487471 := bstep (se 1 (by rfl) ⟨365603, by rfl⟩ : syracuseStep 487471 = 731207) B731207
theorem B2847059 : Blo 483789 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B3699431 : Blo 483789 3699431 := bstep (se 1 (by rfl) ⟨2774573, by rfl⟩ : syracuseStep 3699431 = 5549147) B5549147
theorem B367720199 : Blo 483789 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B4421567 : Blo 483789 4421567 := bstep (se 1 (by rfl) ⟨3316175, by rfl⟩ : syracuseStep 4421567 = 6632351) B6632351
theorem B1637117 : Blo 483789 1637117 := bstep (se 3 (by rfl) ⟨306959, by rfl⟩ : syracuseStep 1637117 = 613919) B613919
theorem B31161839 : Blo 483789 31161839 := bstep (se 1 (by rfl) ⟨23371379, by rfl⟩ : syracuseStep 31161839 = 46742759) B46742759
theorem B14976971 : Blo 483789 14976971 := bstep (se 1 (by rfl) ⟨11232728, by rfl⟩ : syracuseStep 14976971 = 22465457) B22465457
theorem B2459645 : Blo 483789 2459645 := bstep (se 3 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 2459645 = 922367) B922367
theorem B6228029 : Blo 483789 6228029 := bstep (se 3 (by rfl) ⟨1167755, by rfl⟩ : syracuseStep 6228029 = 2335511) B2335511
theorem B2952553 : Blo 483789 2952553 := bstep (se 2 (by rfl) ⟨1107207, by rfl⟩ : syracuseStep 2952553 = 2214415) B2214415
theorem B3543335 : Blo 483789 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B725723 : Blo 483789 725723 := bstep (se 1 (by rfl) ⟨544292, by rfl⟩ : syracuseStep 725723 = 1088585) B1088585
theorem B726575 : Blo 483789 726575 := bstep (se 1 (by rfl) ⟨544931, by rfl⟩ : syracuseStep 726575 = 1089863) B1089863
theorem B1644137 : Blo 483789 1644137 := bstep (se 2 (by rfl) ⟨616551, by rfl⟩ : syracuseStep 1644137 = 1233103) B1233103
theorem B727067 : Blo 483789 727067 := bstep (se 1 (by rfl) ⟨545300, by rfl⟩ : syracuseStep 727067 = 1090601) B1090601
theorem B2758697 : Blo 483789 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B694327 : Blo 483789 694327 := bstep (se 1 (by rfl) ⟨520745, by rfl⟩ : syracuseStep 694327 = 1041491) B1041491
theorem B5511239 : Blo 483789 5511239 := bstep (se 1 (by rfl) ⟨4133429, by rfl⟩ : syracuseStep 5511239 = 8266859) B8266859
theorem B2628143 : Blo 483789 2628143 := bstep (se 1 (by rfl) ⟨1971107, by rfl⟩ : syracuseStep 2628143 = 3942215) B3942215
theorem B727721 : Blo 483789 727721 := bstep (se 2 (by rfl) ⟨272895, by rfl⟩ : syracuseStep 727721 = 545791) B545791
theorem B1677995 : Blo 483789 1677995 := bstep (se 1 (by rfl) ⟨1258496, by rfl⟩ : syracuseStep 1677995 = 2516993) B2516993
theorem B1383119 : Blo 483789 1383119 := bstep (se 1 (by rfl) ⟨1037339, by rfl⟩ : syracuseStep 1383119 = 2074679) B2074679
theorem B924463 : Blo 483789 924463 := bstep (se 1 (by rfl) ⟨693347, by rfl⟩ : syracuseStep 924463 = 1386695) B1386695
theorem B22715407 : Blo 483789 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B728303 : Blo 483789 728303 := bstep (se 1 (by rfl) ⟨546227, by rfl⟩ : syracuseStep 728303 = 1092455) B1092455
theorem B728375 : Blo 483789 728375 := bstep (se 1 (by rfl) ⟨546281, by rfl⟩ : syracuseStep 728375 = 1092563) B1092563
theorem B1646081 : Blo 483789 1646081 := bstep (se 2 (by rfl) ⟨617280, by rfl⟩ : syracuseStep 1646081 = 1234561) B1234561
theorem B728759 : Blo 483789 728759 := bstep (se 1 (by rfl) ⟨546569, by rfl⟩ : syracuseStep 728759 = 1093139) B1093139
theorem B1384361 : Blo 483789 1384361 := bstep (se 2 (by rfl) ⟨519135, by rfl⟩ : syracuseStep 1384361 = 1038271) B1038271
theorem B729179 : Blo 483789 729179 := bstep (se 1 (by rfl) ⟨546884, by rfl⟩ : syracuseStep 729179 = 1093769) B1093769
theorem B1843337 : Blo 483789 1843337 := bstep (se 2 (by rfl) ⟨691251, by rfl⟩ : syracuseStep 1843337 = 1382503) B1382503
theorem B2466287 : Blo 483789 2466287 := bstep (se 1 (by rfl) ⟨1849715, by rfl⟩ : syracuseStep 2466287 = 3699431) B3699431
theorem B730079 : Blo 483789 730079 := bstep (se 1 (by rfl) ⟨547559, by rfl⟩ : syracuseStep 730079 = 1095119) B1095119
theorem B245146799 : Blo 483789 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B153134317 : Blo 483789 153134317 := bstep (se 3 (by rfl) ⟨28712684, by rfl⟩ : syracuseStep 153134317 = 57425369) B57425369
theorem B1091411 : Blo 483789 1091411 := bstep (se 1 (by rfl) ⟨818558, by rfl⟩ : syracuseStep 1091411 = 1637117) B1637117
theorem B41527133 : Blo 483789 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B13248845 : Blo 483789 13248845 := bstep (se 3 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 13248845 = 4968317) B4968317
theorem B731495 : Blo 483789 731495 := bstep (se 1 (by rfl) ⟨548621, by rfl⟩ : syracuseStep 731495 = 1097243) B1097243
theorem B1388735 : Blo 483789 1388735 := bstep (se 1 (by rfl) ⟨1041551, by rfl⟩ : syracuseStep 1388735 = 2083103) B2083103
theorem B1094075 : Blo 483789 1094075 := bstep (se 1 (by rfl) ⟨820556, by rfl⟩ : syracuseStep 1094075 = 1641113) B1641113
theorem B47231819 : Blo 483789 47231819 := bstep (se 1 (by rfl) ⟨35423864, by rfl⟩ : syracuseStep 47231819 = 70847729) B70847729
theorem B2339741 : Blo 483789 2339741 := bstep (se 3 (by rfl) ⟨438701, by rfl⟩ : syracuseStep 2339741 = 877403) B877403
theorem B9354041 : Blo 483789 9354041 := bstep (se 2 (by rfl) ⟨3507765, by rfl⟩ : syracuseStep 9354041 = 7015531) B7015531
theorem B5477350643 : Blo 483789 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B9322361 : Blo 483789 9322361 := bstep (se 2 (by rfl) ⟨3495885, by rfl⟩ : syracuseStep 9322361 = 6991771) B6991771
theorem B19974539 : Blo 483789 19974539 := bstep (se 1 (by rfl) ⟨14980904, by rfl⟩ : syracuseStep 19974539 = 29961809) B29961809
theorem B3099869 : Blo 483789 3099869 := bstep (se 3 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 3099869 = 1162451) B1162451
theorem B1233215 : Blo 483789 1233215 := bstep (se 1 (by rfl) ⟨924911, by rfl⟩ : syracuseStep 1233215 = 1849823) B1849823
theorem B69031561 : Blo 483789 69031561 := bstep (se 2 (by rfl) ⟨25886835, by rfl⟩ : syracuseStep 69031561 = 51773671) B51773671
theorem B5888123 : Blo 483789 5888123 := bstep (se 1 (by rfl) ⟨4416092, by rfl⟩ : syracuseStep 5888123 = 8832185) B8832185
theorem B3102943 : Blo 483789 3102943 := bstep (se 1 (by rfl) ⟨2327207, by rfl⟩ : syracuseStep 3102943 = 4654415) B4654415
theorem B5692625 : Blo 483789 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B1170985 : Blo 483789 1170985 := bstep (se 2 (by rfl) ⟨439119, by rfl⟩ : syracuseStep 1170985 = 878239) B878239
theorem B4678175 : Blo 483789 4678175 := bstep (se 1 (by rfl) ⟨3508631, by rfl⟩ : syracuseStep 4678175 = 7017263) B7017263
theorem B484591 : Blo 483789 484591 := bstep (se 1 (by rfl) ⟨363443, by rfl⟩ : syracuseStep 484591 = 726887) B726887
theorem B484831 : Blo 483789 484831 := bstep (se 1 (by rfl) ⟨363623, by rfl⟩ : syracuseStep 484831 = 727247) B727247
theorem B485503 : Blo 483789 485503 := bstep (se 1 (by rfl) ⟨364127, by rfl⟩ : syracuseStep 485503 = 728255) B728255
theorem B2943215 : Blo 483789 2943215 := bstep (se 1 (by rfl) ⟨2207411, by rfl⟩ : syracuseStep 2943215 = 4414823) B4414823
theorem B485979 : Blo 483789 485979 := bstep (se 1 (by rfl) ⟨364484, by rfl⟩ : syracuseStep 485979 = 728969) B728969
theorem B1141499 : Blo 483789 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B486383 : Blo 483789 486383 := bstep (se 1 (by rfl) ⟨364787, by rfl⟩ : syracuseStep 486383 = 729575) B729575
theorem B2944109 : Blo 483789 2944109 := bstep (se 3 (by rfl) ⟨552020, by rfl⟩ : syracuseStep 2944109 = 1104041) B1104041
theorem B486939 : Blo 483789 486939 := bstep (se 1 (by rfl) ⟨365204, by rfl⟩ : syracuseStep 486939 = 730409) B730409
theorem B487271 : Blo 483789 487271 := bstep (se 1 (by rfl) ⟨365453, by rfl⟩ : syracuseStep 487271 = 730907) B730907
theorem B585911 : Blo 483789 585911 := bstep (se 1 (by rfl) ⟨439433, by rfl⟩ : syracuseStep 585911 = 878867) B878867
theorem B1898039 : Blo 483789 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B83098237 : Blo 483789 83098237 := bstep (se 3 (by rfl) ⟨15580919, by rfl⟩ : syracuseStep 83098237 = 31161839) B31161839
theorem B2947711 : Blo 483789 2947711 := bstep (se 1 (by rfl) ⟨2210783, by rfl⟩ : syracuseStep 2947711 = 4421567) B4421567
theorem B2457539 : Blo 483789 2457539 := bstep (se 1 (by rfl) ⟨1843154, by rfl⟩ : syracuseStep 2457539 = 3686309) B3686309
theorem B1639763 : Blo 483789 1639763 := bstep (se 1 (by rfl) ⟨1229822, by rfl⟩ : syracuseStep 1639763 = 2459645) B2459645
theorem B2066579 : Blo 483789 2066579 := bstep (se 1 (by rfl) ⟨1549934, by rfl⟩ : syracuseStep 2066579 = 3099869) B3099869
theorem B2362223 : Blo 483789 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B822143 : Blo 483789 822143 := bstep (se 1 (by rfl) ⟨616607, by rfl⟩ : syracuseStep 822143 = 1233215) B1233215
theorem B1839131 : Blo 483789 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B3674159 : Blo 483789 3674159 := bstep (se 1 (by rfl) ⟨2755619, by rfl⟩ : syracuseStep 3674159 = 5511239) B5511239
theorem B1118663 : Blo 483789 1118663 := bstep (se 1 (by rfl) ⟨838997, by rfl⟩ : syracuseStep 1118663 = 1677995) B1677995
theorem B922079 : Blo 483789 922079 := bstep (se 1 (by rfl) ⟨691559, by rfl⟩ : syracuseStep 922079 = 1383119) B1383119
theorem B3936737 : Blo 483789 3936737 := bstep (se 2 (by rfl) ⟨1476276, by rfl⟩ : syracuseStep 3936737 = 2952553) B2952553
theorem B922907 : Blo 483789 922907 := bstep (se 1 (by rfl) ⟨692180, by rfl⟩ : syracuseStep 922907 = 1384361) B1384361
theorem B1644191 : Blo 483789 1644191 := bstep (se 1 (by rfl) ⟨1233143, by rfl⟩ : syracuseStep 1644191 = 2466287) B2466287
theorem B3118783 : Blo 483789 3118783 := bstep (se 1 (by rfl) ⟨2339087, by rfl⟩ : syracuseStep 3118783 = 4678175) B4678175
theorem B727607 : Blo 483789 727607 := bstep (se 1 (by rfl) ⟨545705, by rfl⟩ : syracuseStep 727607 = 1091411) B1091411
theorem B816716357 : Blo 483789 816716357 := bstep (se 4 (by rfl) ⟨76567158, by rfl⟩ : syracuseStep 816716357 = 153134317) B153134317
theorem B925769 : Blo 483789 925769 := bstep (se 2 (by rfl) ⟨347163, by rfl⟩ : syracuseStep 925769 = 694327) B694327
theorem B925823 : Blo 483789 925823 := bstep (se 1 (by rfl) ⟨694367, by rfl⟩ : syracuseStep 925823 = 1388735) B1388735
theorem B729383 : Blo 483789 729383 := bstep (se 1 (by rfl) ⟨547037, by rfl⟩ : syracuseStep 729383 = 1094075) B1094075
theorem B4137257 : Blo 483789 4137257 := bstep (se 2 (by rfl) ⟨1551471, by rfl⟩ : syracuseStep 4137257 = 3102943) B3102943
theorem B110797649 : Blo 483789 110797649 := bstep (se 2 (by rfl) ⟨41549118, by rfl⟩ : syracuseStep 110797649 = 83098237) B83098237
theorem B30287209 : Blo 483789 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B6236027 : Blo 483789 6236027 := bstep (se 1 (by rfl) ⟨4677020, by rfl⟩ : syracuseStep 6236027 = 9354041) B9354041
theorem B13316359 : Blo 483789 13316359 := bstep (se 1 (by rfl) ⟨9987269, by rfl⟩ : syracuseStep 13316359 = 19974539) B19974539
theorem B1096091 : Blo 483789 1096091 := bstep (se 1 (by rfl) ⟨822068, by rfl⟩ : syracuseStep 1096091 = 1644137) B1644137
theorem B5061437 : Blo 483789 5061437 := bstep (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) B1898039
theorem B1752095 : Blo 483789 1752095 := bstep (se 1 (by rfl) ⟨1314071, by rfl⟩ : syracuseStep 1752095 = 2628143) B2628143
theorem B1097387 : Blo 483789 1097387 := bstep (se 1 (by rfl) ⟨823040, by rfl⟩ : syracuseStep 1097387 = 1646081) B1646081
theorem B1228891 : Blo 483789 1228891 := bstep (se 1 (by rfl) ⟨921668, by rfl⟩ : syracuseStep 1228891 = 1843337) B1843337
theorem B163431199 : Blo 483789 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B8832563 : Blo 483789 8832563 := bstep (se 1 (by rfl) ⟨6624422, by rfl⟩ : syracuseStep 8832563 = 13248845) B13248845
theorem B1559827 : Blo 483789 1559827 := bstep (se 1 (by rfl) ⟨1169870, by rfl⟩ : syracuseStep 1559827 = 2339741) B2339741
theorem B1232617 : Blo 483789 1232617 := bstep (se 2 (by rfl) ⟨462231, by rfl⟩ : syracuseStep 1232617 = 924463) B924463
theorem B1561313 : Blo 483789 1561313 := bstep (se 2 (by rfl) ⟨585492, by rfl⟩ : syracuseStep 1561313 = 1170985) B1170985
theorem B6214907 : Blo 483789 6214907 := bstep (se 1 (by rfl) ⟨4661180, by rfl⟩ : syracuseStep 6214907 = 9322361) B9322361
theorem B1562429 : Blo 483789 1562429 := bstep (se 3 (by rfl) ⟨292955, by rfl⟩ : syracuseStep 1562429 = 585911) B585911
theorem B9984647 : Blo 483789 9984647 := bstep (se 1 (by rfl) ⟨7488485, by rfl⟩ : syracuseStep 9984647 = 14976971) B14976971
theorem B4152019 : Blo 483789 4152019 := bstep (se 1 (by rfl) ⟨3114014, by rfl⟩ : syracuseStep 4152019 = 6228029) B6228029
theorem B483815 : Blo 483789 483815 := bstep (se 1 (by rfl) ⟨362861, by rfl⟩ : syracuseStep 483815 = 725723) B725723
theorem B484383 : Blo 483789 484383 := bstep (se 1 (by rfl) ⟨363287, by rfl⟩ : syracuseStep 484383 = 726575) B726575
theorem B484711 : Blo 483789 484711 := bstep (se 1 (by rfl) ⟨363533, by rfl⟩ : syracuseStep 484711 = 727067) B727067
theorem B3925415 : Blo 483789 3925415 := bstep (se 1 (by rfl) ⟨2944061, by rfl⟩ : syracuseStep 3925415 = 5888123) B5888123
theorem B485147 : Blo 483789 485147 := bstep (se 1 (by rfl) ⟨363860, by rfl⟩ : syracuseStep 485147 = 727721) B727721
theorem B3795083 : Blo 483789 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B485535 : Blo 483789 485535 := bstep (se 1 (by rfl) ⟨364151, by rfl⟩ : syracuseStep 485535 = 728303) B728303
theorem B485583 : Blo 483789 485583 := bstep (se 1 (by rfl) ⟨364187, by rfl⟩ : syracuseStep 485583 = 728375) B728375
theorem B485839 : Blo 483789 485839 := bstep (se 1 (by rfl) ⟨364379, by rfl⟩ : syracuseStep 485839 = 728759) B728759
theorem B486119 : Blo 483789 486119 := bstep (se 1 (by rfl) ⟨364589, by rfl⟩ : syracuseStep 486119 = 729179) B729179
theorem B486719 : Blo 483789 486719 := bstep (se 1 (by rfl) ⟨365039, by rfl⟩ : syracuseStep 486719 = 730079) B730079
theorem B27684755 : Blo 483789 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B1962143 : Blo 483789 1962143 := bstep (se 1 (by rfl) ⟨1471607, by rfl⟩ : syracuseStep 1962143 = 2943215) B2943215
theorem B487663 : Blo 483789 487663 := bstep (se 1 (by rfl) ⟨365747, by rfl⟩ : syracuseStep 487663 = 731495) B731495
theorem B3043997 : Blo 483789 3043997 := bstep (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) B1141499
theorem B1962739 : Blo 483789 1962739 := bstep (se 1 (by rfl) ⟨1472054, by rfl⟩ : syracuseStep 1962739 = 2944109) B2944109
theorem B92042081 : Blo 483789 92042081 := bstep (se 2 (by rfl) ⟨34515780, by rfl⟩ : syracuseStep 92042081 = 69031561) B69031561
theorem B31487879 : Blo 483789 31487879 := bstep (se 1 (by rfl) ⟨23615909, by rfl⟩ : syracuseStep 31487879 = 47231819) B47231819
theorem B3930281 : Blo 483789 3930281 := bstep (se 2 (by rfl) ⟨1473855, by rfl⟩ : syracuseStep 3930281 = 2947711) B2947711
theorem B3651567095 : Blo 483789 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B1638359 : Blo 483789 1638359 := bstep (se 1 (by rfl) ⟨1228769, by rfl⟩ : syracuseStep 1638359 = 2457539) B2457539
theorem B1638521 : Blo 483789 1638521 := bstep (se 2 (by rfl) ⟨614445, by rfl⟩ : syracuseStep 1638521 = 1228891) B1228891
theorem B217908265 : Blo 483789 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B1377719 : Blo 483789 1377719 := bstep (se 1 (by rfl) ⟨1033289, by rfl⟩ : syracuseStep 1377719 = 2066579) B2066579
theorem B1574815 : Blo 483789 1574815 := bstep (se 1 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 1574815 = 2362223) B2362223
theorem B4163501 : Blo 483789 4163501 := bstep (se 3 (by rfl) ⟨780656, by rfl⟩ : syracuseStep 4163501 = 1561313) B1561313
theorem B2624491 : Blo 483789 2624491 := bstep (se 1 (by rfl) ⟨1968368, by rfl⟩ : syracuseStep 2624491 = 3936737) B3936737
theorem B544477571 : Blo 483789 544477571 := bstep (se 1 (by rfl) ⟨408358178, by rfl⟩ : syracuseStep 544477571 = 816716357) B816716357
theorem B6656431 : Blo 483789 6656431 := bstep (se 1 (by rfl) ⟨4992323, by rfl⟩ : syracuseStep 6656431 = 9984647) B9984647
theorem B4166477 : Blo 483789 4166477 := bstep (se 3 (by rfl) ⟨781214, by rfl⟩ : syracuseStep 4166477 = 1562429) B1562429
theorem B1643489 : Blo 483789 1643489 := bstep (se 2 (by rfl) ⟨616308, by rfl⟩ : syracuseStep 1643489 = 1232617) B1232617
theorem B2758171 : Blo 483789 2758171 := bstep (se 1 (by rfl) ⟨2068628, by rfl⟩ : syracuseStep 2758171 = 4137257) B4137257
theorem B73865099 : Blo 483789 73865099 := bstep (se 1 (by rfl) ⟨55398824, by rfl⟩ : syracuseStep 73865099 = 110797649) B110797649
theorem B2530055 : Blo 483789 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B18456503 : Blo 483789 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B730727 : Blo 483789 730727 := bstep (se 1 (by rfl) ⟨548045, by rfl⟩ : syracuseStep 730727 = 1096091) B1096091
theorem B2434378063 : Blo 483789 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B731591 : Blo 483789 731591 := bstep (se 1 (by rfl) ⟨548693, by rfl⟩ : syracuseStep 731591 = 1097387) B1097387
theorem B1092239 : Blo 483789 1092239 := bstep (se 1 (by rfl) ⟨819179, by rfl⟩ : syracuseStep 1092239 = 1638359) B1638359
theorem B2468717 : Blo 483789 2468717 := bstep (se 3 (by rfl) ⟨462884, by rfl⟩ : syracuseStep 2468717 = 925769) B925769
theorem B1093175 : Blo 483789 1093175 := bstep (se 1 (by rfl) ⟨819881, by rfl⟩ : syracuseStep 1093175 = 1639763) B1639763
theorem B40382945 : Blo 483789 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B1226087 : Blo 483789 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B4143271 : Blo 483789 4143271 := bstep (se 1 (by rfl) ⟨3107453, by rfl⟩ : syracuseStep 4143271 = 6214907) B6214907
theorem B1096127 : Blo 483789 1096127 := bstep (se 1 (by rfl) ⟨822095, by rfl⟩ : syracuseStep 1096127 = 1644191) B1644191
theorem B2079769 : Blo 483789 2079769 := bstep (se 2 (by rfl) ⟨779913, by rfl⟩ : syracuseStep 2079769 = 1559827) B1559827
theorem B61361387 : Blo 483789 61361387 := bstep (se 1 (by rfl) ⟨46021040, by rfl⟩ : syracuseStep 61361387 = 92042081) B92042081
theorem B20991919 : Blo 483789 20991919 := bstep (se 1 (by rfl) ⟨15743939, by rfl⟩ : syracuseStep 20991919 = 31487879) B31487879
theorem B1168063 : Blo 483789 1168063 := bstep (se 1 (by rfl) ⟨876047, by rfl⟩ : syracuseStep 1168063 = 1752095) B1752095
theorem B5888375 : Blo 483789 5888375 := bstep (se 1 (by rfl) ⟨4416281, by rfl⟩ : syracuseStep 5888375 = 8832563) B8832563
theorem B548095 : Blo 483789 548095 := bstep (se 1 (by rfl) ⟨411071, by rfl⟩ : syracuseStep 548095 = 822143) B822143
theorem B2449439 : Blo 483789 2449439 := bstep (se 1 (by rfl) ⟨1837079, by rfl⟩ : syracuseStep 2449439 = 3674159) B3674159
theorem B745775 : Blo 483789 745775 := bstep (se 1 (by rfl) ⟨559331, by rfl⟩ : syracuseStep 745775 = 1118663) B1118663
theorem B614719 : Blo 483789 614719 := bstep (se 1 (by rfl) ⟨461039, by rfl⟩ : syracuseStep 614719 = 922079) B922079
theorem B615271 : Blo 483789 615271 := bstep (se 1 (by rfl) ⟨461453, by rfl⟩ : syracuseStep 615271 = 922907) B922907
theorem B485071 : Blo 483789 485071 := bstep (se 1 (by rfl) ⟨363803, by rfl⟩ : syracuseStep 485071 = 727607) B727607
theorem B617215 : Blo 483789 617215 := bstep (se 1 (by rfl) ⟨462911, by rfl⟩ : syracuseStep 617215 = 925823) B925823
theorem B486255 : Blo 483789 486255 := bstep (se 1 (by rfl) ⟨364691, by rfl⟩ : syracuseStep 486255 = 729383) B729383
theorem B17755145 : Blo 483789 17755145 := bstep (se 2 (by rfl) ⟨6658179, by rfl⟩ : syracuseStep 17755145 = 13316359) B13316359
theorem B2616943 : Blo 483789 2616943 := bstep (se 1 (by rfl) ⟨1962707, by rfl⟩ : syracuseStep 2616943 = 3925415) B3925415
theorem B2616985 : Blo 483789 2616985 := bstep (se 2 (by rfl) ⟨981369, by rfl⟩ : syracuseStep 2616985 = 1962739) B1962739
theorem B4157351 : Blo 483789 4157351 := bstep (se 1 (by rfl) ⟨3118013, by rfl⟩ : syracuseStep 4157351 = 6236027) B6236027
theorem B4158377 : Blo 483789 4158377 := bstep (se 2 (by rfl) ⟨1559391, by rfl⟩ : syracuseStep 4158377 = 3118783) B3118783
theorem B1308095 : Blo 483789 1308095 := bstep (se 1 (by rfl) ⟨981071, by rfl⟩ : syracuseStep 1308095 = 1962143) B1962143
theorem B2029331 : Blo 483789 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B5536025 : Blo 483789 5536025 := bstep (se 2 (by rfl) ⟨2076009, by rfl⟩ : syracuseStep 5536025 = 4152019) B4152019
theorem B2620187 : Blo 483789 2620187 := bstep (se 1 (by rfl) ⟨1965140, by rfl⟩ : syracuseStep 2620187 = 3930281) B3930281
theorem B3374291 : Blo 483789 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B819625 : Blo 483789 819625 := bstep (se 2 (by rfl) ⟨307359, by rfl⟩ : syracuseStep 819625 = 614719) B614719
theorem B918479 : Blo 483789 918479 := bstep (se 1 (by rfl) ⟨688859, by rfl⟩ : syracuseStep 918479 = 1377719) B1377719
theorem B820361 : Blo 483789 820361 := bstep (se 2 (by rfl) ⟨307635, by rfl⟩ : syracuseStep 820361 = 615271) B615271
theorem B2099753 : Blo 483789 2099753 := bstep (se 2 (by rfl) ⟨787407, by rfl⟩ : syracuseStep 2099753 = 1574815) B1574815
theorem B3245837417 : Blo 483789 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B6229669 : Blo 483789 6229669 := bstep (se 4 (by rfl) ⟨584031, by rfl⟩ : syracuseStep 6229669 = 1168063) B1168063
theorem B822953 : Blo 483789 822953 := bstep (se 2 (by rfl) ⟨308607, by rfl⟩ : syracuseStep 822953 = 617215) B617215
theorem B5411549 : Blo 483789 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B27989225 : Blo 483789 27989225 := bstep (se 2 (by rfl) ⟨10495959, by rfl⟩ : syracuseStep 27989225 = 20991919) B20991919
theorem B497183 : Blo 483789 497183 := bstep (se 1 (by rfl) ⟨372887, by rfl⟩ : syracuseStep 497183 = 745775) B745775
theorem B728159 : Blo 483789 728159 := bstep (se 1 (by rfl) ⟨546119, by rfl⟩ : syracuseStep 728159 = 1092239) B1092239
theorem B1645811 : Blo 483789 1645811 := bstep (se 1 (by rfl) ⟨1234358, by rfl⟩ : syracuseStep 1645811 = 2468717) B2468717
theorem B11836763 : Blo 483789 11836763 := bstep (se 1 (by rfl) ⟨8877572, by rfl⟩ : syracuseStep 11836763 = 17755145) B17755145
theorem B3677561 : Blo 483789 3677561 := bstep (se 2 (by rfl) ⟨1379085, by rfl⟩ : syracuseStep 3677561 = 2758171) B2758171
theorem B728783 : Blo 483789 728783 := bstep (se 1 (by rfl) ⟨546587, by rfl⟩ : syracuseStep 728783 = 1093175) B1093175
theorem B730751 : Blo 483789 730751 := bstep (se 1 (by rfl) ⟨548063, by rfl⟩ : syracuseStep 730751 = 1096127) B1096127
theorem B730793 : Blo 483789 730793 := bstep (se 2 (by rfl) ⟨274047, by rfl⟩ : syracuseStep 730793 = 548095) B548095
theorem B1746791 : Blo 483789 1746791 := bstep (se 1 (by rfl) ⟨1310093, by rfl⟩ : syracuseStep 1746791 = 2620187) B2620187
theorem B1092347 : Blo 483789 1092347 := bstep (se 1 (by rfl) ⟨819260, by rfl⟩ : syracuseStep 1092347 = 1638521) B1638521
theorem B40907591 : Blo 483789 40907591 := bstep (se 1 (by rfl) ⟨30680693, by rfl⟩ : syracuseStep 40907591 = 61361387) B61361387
theorem B362985047 : Blo 483789 362985047 := bstep (se 1 (by rfl) ⟨272238785, by rfl⟩ : syracuseStep 362985047 = 544477571) B544477571
theorem B1095659 : Blo 483789 1095659 := bstep (se 1 (by rfl) ⟨821744, by rfl⟩ : syracuseStep 1095659 = 1643489) B1643489
theorem B3489257 : Blo 483789 3489257 := bstep (se 2 (by rfl) ⟨1308471, by rfl⟩ : syracuseStep 3489257 = 2616943) B2616943
theorem B3489313 : Blo 483789 3489313 := bstep (se 2 (by rfl) ⟨1308492, by rfl⟩ : syracuseStep 3489313 = 2616985) B2616985
theorem B2771567 : Blo 483789 2771567 := bstep (se 1 (by rfl) ⟨2078675, by rfl⟩ : syracuseStep 2771567 = 4157351) B4157351
theorem B5524361 : Blo 483789 5524361 := bstep (se 2 (by rfl) ⟨2071635, by rfl⟩ : syracuseStep 5524361 = 4143271) B4143271
theorem B26921963 : Blo 483789 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B2772251 : Blo 483789 2772251 := bstep (se 1 (by rfl) ⟨2079188, by rfl⟩ : syracuseStep 2772251 = 4158377) B4158377
theorem B872063 : Blo 483789 872063 := bstep (se 1 (by rfl) ⟨654047, by rfl⟩ : syracuseStep 872063 = 1308095) B1308095
theorem B2773025 : Blo 483789 2773025 := bstep (se 2 (by rfl) ⟨1039884, by rfl⟩ : syracuseStep 2773025 = 2079769) B2079769
theorem B3690683 : Blo 483789 3690683 := bstep (se 1 (by rfl) ⟨2768012, by rfl⟩ : syracuseStep 3690683 = 5536025) B5536025
theorem B2249527 : Blo 483789 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B2775667 : Blo 483789 2775667 := bstep (se 1 (by rfl) ⟨2081750, by rfl⟩ : syracuseStep 2775667 = 4163501) B4163501
theorem B290544353 : Blo 483789 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B2777651 : Blo 483789 2777651 := bstep (se 1 (by rfl) ⟨2083238, by rfl⟩ : syracuseStep 2777651 = 4166477) B4166477
theorem B49243399 : Blo 483789 49243399 := bstep (se 1 (by rfl) ⟨36932549, by rfl⟩ : syracuseStep 49243399 = 73865099) B73865099
theorem B3499321 : Blo 483789 3499321 := bstep (se 2 (by rfl) ⟨1312245, by rfl⟩ : syracuseStep 3499321 = 2624491) B2624491
theorem B3925583 : Blo 483789 3925583 := bstep (se 1 (by rfl) ⟨2944187, by rfl⟩ : syracuseStep 3925583 = 5888375) B5888375
theorem B1632959 : Blo 483789 1632959 := bstep (se 1 (by rfl) ⟨1224719, by rfl⟩ : syracuseStep 1632959 = 2449439) B2449439
theorem B8875241 : Blo 483789 8875241 := bstep (se 2 (by rfl) ⟨3328215, by rfl⟩ : syracuseStep 8875241 = 6656431) B6656431
theorem B487151 : Blo 483789 487151 := bstep (se 1 (by rfl) ⟨365363, by rfl⟩ : syracuseStep 487151 = 730727) B730727
theorem B487727 : Blo 483789 487727 := bstep (se 1 (by rfl) ⟨365795, by rfl⟩ : syracuseStep 487727 = 731591) B731591
theorem B6746813 : Blo 483789 6746813 := bstep (se 3 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 6746813 = 2530055) B2530055
theorem B817391 : Blo 483789 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B49217341 : Blo 483789 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B2460455 : Blo 483789 2460455 := bstep (se 1 (by rfl) ⟨1845341, by rfl⟩ : syracuseStep 2460455 = 3690683) B3690683
theorem B193696235 : Blo 483789 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B1088639 : Blo 483789 1088639 := bstep (se 1 (by rfl) ⟨816479, by rfl⟩ : syracuseStep 1088639 = 1632959) B1632959
theorem B728231 : Blo 483789 728231 := bstep (se 1 (by rfl) ⟨546173, by rfl⟩ : syracuseStep 728231 = 1092347) B1092347
theorem B4497875 : Blo 483789 4497875 := bstep (se 1 (by rfl) ⟨3373406, by rfl⟩ : syracuseStep 4497875 = 6746813) B6746813
theorem B27271727 : Blo 483789 27271727 := bstep (se 1 (by rfl) ⟨20453795, by rfl⟩ : syracuseStep 27271727 = 40907591) B40907591
theorem B730439 : Blo 483789 730439 := bstep (se 1 (by rfl) ⟨547829, by rfl⟩ : syracuseStep 730439 = 1095659) B1095659
theorem B1092833 : Blo 483789 1092833 := bstep (se 2 (by rfl) ⟨409812, by rfl⟩ : syracuseStep 1092833 = 819625) B819625
theorem B1847711 : Blo 483789 1847711 := bstep (se 1 (by rfl) ⟨1385783, by rfl⟩ : syracuseStep 1847711 = 2771567) B2771567
theorem B4665761 : Blo 483789 4665761 := bstep (se 2 (by rfl) ⟨1749660, by rfl⟩ : syracuseStep 4665761 = 3499321) B3499321
theorem B14430797 : Blo 483789 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B3682907 : Blo 483789 3682907 := bstep (se 1 (by rfl) ⟨2762180, by rfl⟩ : syracuseStep 3682907 = 5524361) B5524361
theorem B1848167 : Blo 483789 1848167 := bstep (se 1 (by rfl) ⟨1386125, by rfl⟩ : syracuseStep 1848167 = 2772251) B2772251
theorem B1848683 : Blo 483789 1848683 := bstep (se 1 (by rfl) ⟨1386512, by rfl⟩ : syracuseStep 1848683 = 2773025) B2773025
theorem B18659483 : Blo 483789 18659483 := bstep (se 1 (by rfl) ⟨13994612, by rfl⟩ : syracuseStep 18659483 = 27989225) B27989225
theorem B1325821 : Blo 483789 1325821 := bstep (se 3 (by rfl) ⟨248591, by rfl⟩ : syracuseStep 1325821 = 497183) B497183
theorem B1097207 : Blo 483789 1097207 := bstep (se 1 (by rfl) ⟨822905, by rfl⟩ : syracuseStep 1097207 = 1645811) B1645811
theorem B8306225 : Blo 483789 8306225 := bstep (se 2 (by rfl) ⟨3114834, by rfl⟩ : syracuseStep 8306225 = 6229669) B6229669
theorem B1050525845 : Blo 483789 1050525845 := bstep (se 6 (by rfl) ⟨24621699, by rfl⟩ : syracuseStep 1050525845 = 49243399) B49243399
theorem B1851767 : Blo 483789 1851767 := bstep (se 1 (by rfl) ⟨1388825, by rfl⟩ : syracuseStep 1851767 = 2777651) B2777651
theorem B2999369 : Blo 483789 2999369 := bstep (se 2 (by rfl) ⟨1124763, by rfl⟩ : syracuseStep 2999369 = 2249527) B2249527
theorem B1164527 : Blo 483789 1164527 := bstep (se 1 (by rfl) ⟨873395, by rfl⟩ : syracuseStep 1164527 = 1746791) B1746791
theorem B5916827 : Blo 483789 5916827 := bstep (se 1 (by rfl) ⟨4437620, by rfl⟩ : syracuseStep 5916827 = 8875241) B8875241
theorem B544927 : Blo 483789 544927 := bstep (se 1 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 544927 = 817391) B817391
theorem B65623121 : Blo 483789 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B546907 : Blo 483789 546907 := bstep (se 1 (by rfl) ⟨410180, by rfl⟩ : syracuseStep 546907 = 820361) B820361
theorem B1399835 : Blo 483789 1399835 := bstep (se 1 (by rfl) ⟨1049876, by rfl⟩ : syracuseStep 1399835 = 2099753) B2099753
theorem B17947975 : Blo 483789 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B2163891611 : Blo 483789 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B581375 : Blo 483789 581375 := bstep (se 1 (by rfl) ⟨436031, by rfl⟩ : syracuseStep 581375 = 872063) B872063
theorem B548635 : Blo 483789 548635 := bstep (se 1 (by rfl) ⟨411476, by rfl⟩ : syracuseStep 548635 = 822953) B822953
theorem B2449277 : Blo 483789 2449277 := bstep (se 3 (by rfl) ⟨459239, by rfl⟩ : syracuseStep 2449277 = 918479) B918479
theorem B485439 : Blo 483789 485439 := bstep (se 1 (by rfl) ⟨364079, by rfl⟩ : syracuseStep 485439 = 728159) B728159
theorem B7891175 : Blo 483789 7891175 := bstep (se 1 (by rfl) ⟨5918381, by rfl⟩ : syracuseStep 7891175 = 11836763) B11836763
theorem B2451707 : Blo 483789 2451707 := bstep (se 1 (by rfl) ⟨1838780, by rfl⟩ : syracuseStep 2451707 = 3677561) B3677561
theorem B485855 : Blo 483789 485855 := bstep (se 1 (by rfl) ⟨364391, by rfl⟩ : syracuseStep 485855 = 728783) B728783
theorem B2617055 : Blo 483789 2617055 := bstep (se 1 (by rfl) ⟨1962791, by rfl⟩ : syracuseStep 2617055 = 3925583) B3925583
theorem B487167 : Blo 483789 487167 := bstep (se 1 (by rfl) ⟨365375, by rfl⟩ : syracuseStep 487167 = 730751) B730751
theorem B487195 : Blo 483789 487195 := bstep (se 1 (by rfl) ⟨365396, by rfl⟩ : syracuseStep 487195 = 730793) B730793
theorem B3700889 : Blo 483789 3700889 := bstep (se 2 (by rfl) ⟨1387833, by rfl⟩ : syracuseStep 3700889 = 2775667) B2775667
theorem B241990031 : Blo 483789 241990031 := bstep (se 1 (by rfl) ⟨181492523, by rfl⟩ : syracuseStep 241990031 = 362985047) B362985047
theorem B4652417 : Blo 483789 4652417 := bstep (se 2 (by rfl) ⟨1744656, by rfl⟩ : syracuseStep 4652417 = 3489313) B3489313
theorem B2326171 : Blo 483789 2326171 := bstep (se 1 (by rfl) ⟨1744628, by rfl⟩ : syracuseStep 2326171 = 3489257) B3489257
theorem B700350563 : Blo 483789 700350563 := bstep (se 1 (by rfl) ⟨525262922, by rfl⟩ : syracuseStep 700350563 = 1050525845) B1050525845
theorem B1999579 : Blo 483789 1999579 := bstep (se 1 (by rfl) ⟨1499684, by rfl⟩ : syracuseStep 1999579 = 2999369) B2999369
theorem B1640303 : Blo 483789 1640303 := bstep (se 1 (by rfl) ⟨1230227, by rfl⟩ : syracuseStep 1640303 = 2460455) B2460455
theorem B43748747 : Blo 483789 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B725759 : Blo 483789 725759 := bstep (se 1 (by rfl) ⟨544319, by rfl⟩ : syracuseStep 725759 = 1088639) B1088639
theorem B726569 : Blo 483789 726569 := bstep (se 2 (by rfl) ⟨272463, by rfl⟩ : syracuseStep 726569 = 544927) B544927
theorem B728555 : Blo 483789 728555 := bstep (se 1 (by rfl) ⟨546416, by rfl⟩ : syracuseStep 728555 = 1092833) B1092833
theorem B1744703 : Blo 483789 1744703 := bstep (se 1 (by rfl) ⟨1308527, by rfl⟩ : syracuseStep 1744703 = 2617055) B2617055
theorem B729209 : Blo 483789 729209 := bstep (se 2 (by rfl) ⟨273453, by rfl⟩ : syracuseStep 729209 = 546907) B546907
theorem B2467259 : Blo 483789 2467259 := bstep (se 1 (by rfl) ⟨1850444, by rfl⟩ : syracuseStep 2467259 = 3700889) B3700889
theorem B161326687 : Blo 483789 161326687 := bstep (se 1 (by rfl) ⟨120995015, by rfl⟩ : syracuseStep 161326687 = 241990031) B241990031
theorem B23930633 : Blo 483789 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B1550333 : Blo 483789 1550333 := bstep (se 3 (by rfl) ⟨290687, by rfl⟩ : syracuseStep 1550333 = 581375) B581375
theorem B731471 : Blo 483789 731471 := bstep (se 1 (by rfl) ⟨548603, by rfl⟩ : syracuseStep 731471 = 1097207) B1097207
theorem B731513 : Blo 483789 731513 := bstep (se 2 (by rfl) ⟨274317, by rfl⟩ : syracuseStep 731513 = 548635) B548635
theorem B3944551 : Blo 483789 3944551 := bstep (se 1 (by rfl) ⟨2958413, by rfl⟩ : syracuseStep 3944551 = 5916827) B5916827
theorem B933223 : Blo 483789 933223 := bstep (se 1 (by rfl) ⟨699917, by rfl⟩ : syracuseStep 933223 = 1399835) B1399835
theorem B1442594407 : Blo 483789 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B2998583 : Blo 483789 2998583 := bstep (se 1 (by rfl) ⟨2248937, by rfl⟩ : syracuseStep 2998583 = 4497875) B4497875
theorem B5260783 : Blo 483789 5260783 := bstep (se 1 (by rfl) ⟨3945587, by rfl⟩ : syracuseStep 5260783 = 7891175) B7891175
theorem B1231807 : Blo 483789 1231807 := bstep (se 1 (by rfl) ⟨923855, by rfl⟩ : syracuseStep 1231807 = 1847711) B1847711
theorem B9620531 : Blo 483789 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B1232111 : Blo 483789 1232111 := bstep (se 1 (by rfl) ⟨924083, by rfl⟩ : syracuseStep 1232111 = 1848167) B1848167
theorem B1232455 : Blo 483789 1232455 := bstep (se 1 (by rfl) ⟨924341, by rfl⟩ : syracuseStep 1232455 = 1848683) B1848683
theorem B12439655 : Blo 483789 12439655 := bstep (se 1 (by rfl) ⟨9329741, by rfl⟩ : syracuseStep 12439655 = 18659483) B18659483
theorem B3101561 : Blo 483789 3101561 := bstep (se 2 (by rfl) ⟨1163085, by rfl⟩ : syracuseStep 3101561 = 2326171) B2326171
theorem B3101611 : Blo 483789 3101611 := bstep (se 1 (by rfl) ⟨2326208, by rfl⟩ : syracuseStep 3101611 = 4652417) B4652417
theorem B1234511 : Blo 483789 1234511 := bstep (se 1 (by rfl) ⟨925883, by rfl⟩ : syracuseStep 1234511 = 1851767) B1851767
theorem B776351 : Blo 483789 776351 := bstep (se 1 (by rfl) ⟨582263, by rfl⟩ : syracuseStep 776351 = 1164527) B1164527
theorem B129130823 : Blo 483789 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B485487 : Blo 483789 485487 := bstep (se 1 (by rfl) ⟨364115, by rfl⟩ : syracuseStep 485487 = 728231) B728231
theorem B1632851 : Blo 483789 1632851 := bstep (se 1 (by rfl) ⟨1224638, by rfl⟩ : syracuseStep 1632851 = 2449277) B2449277
theorem B18181151 : Blo 483789 18181151 := bstep (se 1 (by rfl) ⟨13635863, by rfl⟩ : syracuseStep 18181151 = 27271727) B27271727
theorem B486959 : Blo 483789 486959 := bstep (se 1 (by rfl) ⟨365219, by rfl⟩ : syracuseStep 486959 = 730439) B730439
theorem B1634471 : Blo 483789 1634471 := bstep (se 1 (by rfl) ⟨1225853, by rfl⟩ : syracuseStep 1634471 = 2451707) B2451707
theorem B3110507 : Blo 483789 3110507 := bstep (se 1 (by rfl) ⟨2332880, by rfl⟩ : syracuseStep 3110507 = 4665761) B4665761
theorem B2455271 : Blo 483789 2455271 := bstep (se 1 (by rfl) ⟨1841453, by rfl⟩ : syracuseStep 2455271 = 3682907) B3682907
theorem B1767761 : Blo 483789 1767761 := bstep (se 2 (by rfl) ⟨662910, by rfl⟩ : syracuseStep 1767761 = 1325821) B1325821
theorem B5537483 : Blo 483789 5537483 := bstep (se 1 (by rfl) ⟨4153112, by rfl⟩ : syracuseStep 5537483 = 8306225) B8306225
theorem B1999055 : Blo 483789 1999055 := bstep (se 1 (by rfl) ⟨1499291, by rfl⟩ : syracuseStep 1999055 = 2998583) B2998583
theorem B7014377 : Blo 483789 7014377 := bstep (se 2 (by rfl) ⟨2630391, by rfl⟩ : syracuseStep 7014377 = 5260783) B5260783
theorem B821407 : Blo 483789 821407 := bstep (se 1 (by rfl) ⟨616055, by rfl⟩ : syracuseStep 821407 = 1232111) B1232111
theorem B29165831 : Blo 483789 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B8293103 : Blo 483789 8293103 := bstep (se 1 (by rfl) ⟨6219827, by rfl⟩ : syracuseStep 8293103 = 12439655) B12439655
theorem B2067707 : Blo 483789 2067707 := bstep (se 1 (by rfl) ⟨1550780, by rfl⟩ : syracuseStep 2067707 = 3101561) B3101561
theorem B823007 : Blo 483789 823007 := bstep (se 1 (by rfl) ⟨617255, by rfl⟩ : syracuseStep 823007 = 1234511) B1234511
theorem B1642409 : Blo 483789 1642409 := bstep (se 2 (by rfl) ⟨615903, by rfl⟩ : syracuseStep 1642409 = 1231807) B1231807
theorem B1643273 : Blo 483789 1643273 := bstep (se 2 (by rfl) ⟨616227, by rfl⟩ : syracuseStep 1643273 = 1232455) B1232455
theorem B86087215 : Blo 483789 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B2070269 : Blo 483789 2070269 := bstep (se 3 (by rfl) ⟨388175, by rfl⟩ : syracuseStep 2070269 = 776351) B776351
theorem B1644839 : Blo 483789 1644839 := bstep (se 1 (by rfl) ⟨1233629, by rfl⟩ : syracuseStep 1644839 = 2467259) B2467259
theorem B4135481 : Blo 483789 4135481 := bstep (se 2 (by rfl) ⟨1550805, by rfl⟩ : syracuseStep 4135481 = 3101611) B3101611
theorem B1088567 : Blo 483789 1088567 := bstep (se 1 (by rfl) ⟨816425, by rfl⟩ : syracuseStep 1088567 = 1632851) B1632851
theorem B1089647 : Blo 483789 1089647 := bstep (se 1 (by rfl) ⟨817235, by rfl⟩ : syracuseStep 1089647 = 1634471) B1634471
theorem B2073671 : Blo 483789 2073671 := bstep (se 1 (by rfl) ⟨1555253, by rfl⟩ : syracuseStep 2073671 = 3110507) B3110507
theorem B1923459209 : Blo 483789 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B2666105 : Blo 483789 2666105 := bstep (se 2 (by rfl) ⟨999789, by rfl⟩ : syracuseStep 2666105 = 1999579) B1999579
theorem B1093535 : Blo 483789 1093535 := bstep (se 1 (by rfl) ⟨820151, by rfl⟩ : syracuseStep 1093535 = 1640303) B1640303
theorem B215102249 : Blo 483789 215102249 := bstep (se 2 (by rfl) ⟨80663343, by rfl⟩ : syracuseStep 215102249 = 161326687) B161326687
theorem B1163135 : Blo 483789 1163135 := bstep (se 1 (by rfl) ⟨872351, by rfl⟩ : syracuseStep 1163135 = 1744703) B1744703
theorem B5259401 : Blo 483789 5259401 := bstep (se 2 (by rfl) ⟨1972275, by rfl⟩ : syracuseStep 5259401 = 3944551) B3944551
theorem B1033555 : Blo 483789 1033555 := bstep (se 1 (by rfl) ⟨775166, by rfl⟩ : syracuseStep 1033555 = 1550333) B1550333
theorem B3691655 : Blo 483789 3691655 := bstep (se 1 (by rfl) ⟨2768741, by rfl⟩ : syracuseStep 3691655 = 5537483) B5537483
theorem B466900375 : Blo 483789 466900375 := bstep (se 1 (by rfl) ⟨350175281, by rfl⟩ : syracuseStep 466900375 = 700350563) B700350563
theorem B6413687 : Blo 483789 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B483839 : Blo 483789 483839 := bstep (se 1 (by rfl) ⟨362879, by rfl⟩ : syracuseStep 483839 = 725759) B725759
theorem B484379 : Blo 483789 484379 := bstep (se 1 (by rfl) ⟨363284, by rfl⟩ : syracuseStep 484379 = 726569) B726569
theorem B485703 : Blo 483789 485703 := bstep (se 1 (by rfl) ⟨364277, by rfl⟩ : syracuseStep 485703 = 728555) B728555
theorem B486139 : Blo 483789 486139 := bstep (se 1 (by rfl) ⟨364604, by rfl⟩ : syracuseStep 486139 = 729209) B729209
theorem B15953755 : Blo 483789 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B487647 : Blo 483789 487647 := bstep (se 1 (by rfl) ⟨365735, by rfl⟩ : syracuseStep 487647 = 731471) B731471
theorem B487675 : Blo 483789 487675 := bstep (se 1 (by rfl) ⟨365756, by rfl⟩ : syracuseStep 487675 = 731513) B731513
theorem B12120767 : Blo 483789 12120767 := bstep (se 1 (by rfl) ⟨9090575, by rfl⟩ : syracuseStep 12120767 = 18181151) B18181151
theorem B1636847 : Blo 483789 1636847 := bstep (se 1 (by rfl) ⟨1227635, by rfl⟩ : syracuseStep 1636847 = 2455271) B2455271
theorem B1178507 : Blo 483789 1178507 := bstep (se 1 (by rfl) ⟨883880, by rfl⟩ : syracuseStep 1178507 = 1767761) B1767761
theorem B1244297 : Blo 483789 1244297 := bstep (se 2 (by rfl) ⟨466611, by rfl⟩ : syracuseStep 1244297 = 933223) B933223
theorem B3506267 : Blo 483789 3506267 := bstep (se 1 (by rfl) ⟨2629700, by rfl⟩ : syracuseStep 3506267 = 5259401) B5259401
theorem B1378073 : Blo 483789 1378073 := bstep (se 2 (by rfl) ⟨516777, by rfl⟩ : syracuseStep 1378073 = 1033555) B1033555
theorem B1378471 : Blo 483789 1378471 := bstep (se 1 (by rfl) ⟨1033853, by rfl⟩ : syracuseStep 1378471 = 2067707) B2067707
theorem B2461103 : Blo 483789 2461103 := bstep (se 1 (by rfl) ⟨1845827, by rfl⟩ : syracuseStep 2461103 = 3691655) B3691655
theorem B1380179 : Blo 483789 1380179 := bstep (se 1 (by rfl) ⟨1035134, by rfl⟩ : syracuseStep 1380179 = 2070269) B2070269
theorem B2756987 : Blo 483789 2756987 := bstep (se 1 (by rfl) ⟨2067740, by rfl⟩ : syracuseStep 2756987 = 4135481) B4135481
theorem B725711 : Blo 483789 725711 := bstep (se 1 (by rfl) ⟨544283, by rfl⟩ : syracuseStep 725711 = 1088567) B1088567
theorem B21271673 : Blo 483789 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B726431 : Blo 483789 726431 := bstep (se 1 (by rfl) ⟨544823, by rfl⟩ : syracuseStep 726431 = 1089647) B1089647
theorem B1382447 : Blo 483789 1382447 := bstep (se 1 (by rfl) ⟨1036835, by rfl⟩ : syracuseStep 1382447 = 2073671) B2073671
theorem B622533833 : Blo 483789 622533833 := bstep (se 2 (by rfl) ⟨233450187, by rfl⟩ : syracuseStep 622533833 = 466900375) B466900375
theorem B1777403 : Blo 483789 1777403 := bstep (se 1 (by rfl) ⟨1333052, by rfl⟩ : syracuseStep 1777403 = 2666105) B2666105
theorem B729023 : Blo 483789 729023 := bstep (se 1 (by rfl) ⟨546767, by rfl⟩ : syracuseStep 729023 = 1093535) B1093535
theorem B143401499 : Blo 483789 143401499 := bstep (se 1 (by rfl) ⟨107551124, by rfl⟩ : syracuseStep 143401499 = 215102249) B215102249
theorem B1091231 : Blo 483789 1091231 := bstep (se 1 (by rfl) ⟨818423, by rfl⟩ : syracuseStep 1091231 = 1636847) B1636847
theorem B829531 : Blo 483789 829531 := bstep (se 1 (by rfl) ⟨622148, by rfl⟩ : syracuseStep 829531 = 1244297) B1244297
theorem B19443887 : Blo 483789 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B1094939 : Blo 483789 1094939 := bstep (se 1 (by rfl) ⟨821204, by rfl⟩ : syracuseStep 1094939 = 1642409) B1642409
theorem B1095209 : Blo 483789 1095209 := bstep (se 2 (by rfl) ⟨410703, by rfl⟩ : syracuseStep 1095209 = 821407) B821407
theorem B1095515 : Blo 483789 1095515 := bstep (se 1 (by rfl) ⟨821636, by rfl⟩ : syracuseStep 1095515 = 1643273) B1643273
theorem B1096559 : Blo 483789 1096559 := bstep (se 1 (by rfl) ⟨822419, by rfl⟩ : syracuseStep 1096559 = 1644839) B1644839
theorem B4275791 : Blo 483789 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B8080511 : Blo 483789 8080511 := bstep (se 1 (by rfl) ⟨6060383, by rfl⟩ : syracuseStep 8080511 = 12120767) B12120767
theorem B775423 : Blo 483789 775423 := bstep (se 1 (by rfl) ⟨581567, by rfl⟩ : syracuseStep 775423 = 1163135) B1163135
theorem B1332703 : Blo 483789 1332703 := bstep (se 1 (by rfl) ⟨999527, by rfl⟩ : syracuseStep 1332703 = 1999055) B1999055
theorem B4676251 : Blo 483789 4676251 := bstep (se 1 (by rfl) ⟨3507188, by rfl⟩ : syracuseStep 4676251 = 7014377) B7014377
theorem B5528735 : Blo 483789 5528735 := bstep (se 1 (by rfl) ⟨4146551, by rfl⟩ : syracuseStep 5528735 = 8293103) B8293103
theorem B548671 : Blo 483789 548671 := bstep (se 1 (by rfl) ⟨411503, by rfl⟩ : syracuseStep 548671 = 823007) B823007
theorem B1282306139 : Blo 483789 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B114782953 : Blo 483789 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B3142685 : Blo 483789 3142685 := bstep (se 3 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 3142685 = 1178507) B1178507
theorem B4424165 : Blo 483789 4424165 := bstep (se 4 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 4424165 = 829531) B829531
theorem B918715 : Blo 483789 918715 := bstep (se 1 (by rfl) ⟨689036, by rfl⟩ : syracuseStep 918715 = 1378073) B1378073
theorem B1640735 : Blo 483789 1640735 := bstep (se 1 (by rfl) ⟨1230551, by rfl⟩ : syracuseStep 1640735 = 2461103) B2461103
theorem B1837961 : Blo 483789 1837961 := bstep (se 2 (by rfl) ⟨689235, by rfl⟩ : syracuseStep 1837961 = 1378471) B1378471
theorem B1837991 : Blo 483789 1837991 := bstep (se 1 (by rfl) ⟨1378493, by rfl⟩ : syracuseStep 1837991 = 2756987) B2756987
theorem B56724461 : Blo 483789 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B921631 : Blo 483789 921631 := bstep (se 1 (by rfl) ⟨691223, by rfl⟩ : syracuseStep 921631 = 1382447) B1382447
theorem B727487 : Blo 483789 727487 := bstep (se 1 (by rfl) ⟨545615, by rfl⟩ : syracuseStep 727487 = 1091231) B1091231
theorem B729959 : Blo 483789 729959 := bstep (se 1 (by rfl) ⟨547469, by rfl⟩ : syracuseStep 729959 = 1094939) B1094939
theorem B6235001 : Blo 483789 6235001 := bstep (se 2 (by rfl) ⟨2338125, by rfl⟩ : syracuseStep 6235001 = 4676251) B4676251
theorem B730139 : Blo 483789 730139 := bstep (se 1 (by rfl) ⟨547604, by rfl⟩ : syracuseStep 730139 = 1095209) B1095209
theorem B730343 : Blo 483789 730343 := bstep (se 1 (by rfl) ⟨547757, by rfl⟩ : syracuseStep 730343 = 1095515) B1095515
theorem B731039 : Blo 483789 731039 := bstep (se 1 (by rfl) ⟨548279, by rfl⟩ : syracuseStep 731039 = 1096559) B1096559
theorem B3680477 : Blo 483789 3680477 := bstep (se 3 (by rfl) ⟨690089, by rfl⟩ : syracuseStep 3680477 = 1380179) B1380179
theorem B731561 : Blo 483789 731561 := bstep (se 2 (by rfl) ⟨274335, by rfl⟩ : syracuseStep 731561 = 548671) B548671
theorem B2337511 : Blo 483789 2337511 := bstep (se 1 (by rfl) ⟨1753133, by rfl⟩ : syracuseStep 2337511 = 3506267) B3506267
theorem B3685823 : Blo 483789 3685823 := bstep (se 1 (by rfl) ⟨2764367, by rfl⟩ : syracuseStep 3685823 = 5528735) B5528735
theorem B415022555 : Blo 483789 415022555 := bstep (se 1 (by rfl) ⟨311266916, by rfl⟩ : syracuseStep 415022555 = 622533833) B622533833
theorem B95600999 : Blo 483789 95600999 := bstep (se 1 (by rfl) ⟨71700749, by rfl⟩ : syracuseStep 95600999 = 143401499) B143401499
theorem B153043937 : Blo 483789 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B1033897 : Blo 483789 1033897 := bstep (se 2 (by rfl) ⟨387711, by rfl⟩ : syracuseStep 1033897 = 775423) B775423
theorem B854870759 : Blo 483789 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B12962591 : Blo 483789 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B21548029 : Blo 483789 21548029 := bstep (se 3 (by rfl) ⟨4040255, by rfl⟩ : syracuseStep 21548029 = 8080511) B8080511
theorem B4739741 : Blo 483789 4739741 := bstep (se 3 (by rfl) ⟨888701, by rfl⟩ : syracuseStep 4739741 = 1777403) B1777403
theorem B8380493 : Blo 483789 8380493 := bstep (se 3 (by rfl) ⟨1571342, by rfl⟩ : syracuseStep 8380493 = 3142685) B3142685
theorem B483807 : Blo 483789 483807 := bstep (se 1 (by rfl) ⟨362855, by rfl⟩ : syracuseStep 483807 = 725711) B725711
theorem B484287 : Blo 483789 484287 := bstep (se 1 (by rfl) ⟨363215, by rfl⟩ : syracuseStep 484287 = 726431) B726431
theorem B486015 : Blo 483789 486015 := bstep (se 1 (by rfl) ⟨364511, by rfl⟩ : syracuseStep 486015 = 729023) B729023
theorem B7107749 : Blo 483789 7107749 := bstep (se 4 (by rfl) ⟨666351, by rfl⟩ : syracuseStep 7107749 = 1332703) B1332703
theorem B2850527 : Blo 483789 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B63733999 : Blo 483789 63733999 := bstep (se 1 (by rfl) ⟨47800499, by rfl⟩ : syracuseStep 63733999 = 95600999) B95600999
theorem B2949443 : Blo 483789 2949443 := bstep (se 1 (by rfl) ⟨2212082, by rfl⟩ : syracuseStep 2949443 = 4424165) B4424165
theorem B37816307 : Blo 483789 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B1378529 : Blo 483789 1378529 := bstep (se 2 (by rfl) ⟨516948, by rfl⟩ : syracuseStep 1378529 = 1033897) B1033897
theorem B3116681 : Blo 483789 3116681 := bstep (se 2 (by rfl) ⟨1168755, by rfl⟩ : syracuseStep 3116681 = 2337511) B2337511
theorem B1093823 : Blo 483789 1093823 := bstep (se 1 (by rfl) ⟨820367, by rfl⟩ : syracuseStep 1093823 = 1640735) B1640735
theorem B1224953 : Blo 483789 1224953 := bstep (se 2 (by rfl) ⟨459357, by rfl⟩ : syracuseStep 1224953 = 918715) B918715
theorem B569913839 : Blo 483789 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B1225307 : Blo 483789 1225307 := bstep (se 1 (by rfl) ⟨918980, by rfl⟩ : syracuseStep 1225307 = 1837961) B1837961
theorem B1225327 : Blo 483789 1225327 := bstep (se 1 (by rfl) ⟨918995, by rfl⟩ : syracuseStep 1225327 = 1837991) B1837991
theorem B3159827 : Blo 483789 3159827 := bstep (se 1 (by rfl) ⟨2369870, by rfl⟩ : syracuseStep 3159827 = 4739741) B4739741
theorem B1228841 : Blo 483789 1228841 := bstep (se 2 (by rfl) ⟨460815, by rfl⟩ : syracuseStep 1228841 = 921631) B921631
theorem B5586995 : Blo 483789 5586995 := bstep (se 1 (by rfl) ⟨4190246, by rfl⟩ : syracuseStep 5586995 = 8380493) B8380493
theorem B4738499 : Blo 483789 4738499 := bstep (se 1 (by rfl) ⟨3553874, by rfl⟩ : syracuseStep 4738499 = 7107749) B7107749
theorem B276681703 : Blo 483789 276681703 := bstep (se 1 (by rfl) ⟨207511277, by rfl⟩ : syracuseStep 276681703 = 415022555) B415022555
theorem B102029291 : Blo 483789 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B8641727 : Blo 483789 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B28730705 : Blo 483789 28730705 := bstep (se 2 (by rfl) ⟨10774014, by rfl⟩ : syracuseStep 28730705 = 21548029) B21548029
theorem B484991 : Blo 483789 484991 := bstep (se 1 (by rfl) ⟨363743, by rfl⟩ : syracuseStep 484991 = 727487) B727487
theorem B486639 : Blo 483789 486639 := bstep (se 1 (by rfl) ⟨364979, by rfl⟩ : syracuseStep 486639 = 729959) B729959
theorem B4156667 : Blo 483789 4156667 := bstep (se 1 (by rfl) ⟨3117500, by rfl⟩ : syracuseStep 4156667 = 6235001) B6235001
theorem B486759 : Blo 483789 486759 := bstep (se 1 (by rfl) ⟨365069, by rfl⟩ : syracuseStep 486759 = 730139) B730139
theorem B486895 : Blo 483789 486895 := bstep (se 1 (by rfl) ⟨365171, by rfl⟩ : syracuseStep 486895 = 730343) B730343
theorem B487359 : Blo 483789 487359 := bstep (se 1 (by rfl) ⟨365519, by rfl⟩ : syracuseStep 487359 = 731039) B731039
theorem B2453651 : Blo 483789 2453651 := bstep (se 1 (by rfl) ⟨1840238, by rfl⟩ : syracuseStep 2453651 = 3680477) B3680477
theorem B487707 : Blo 483789 487707 := bstep (se 1 (by rfl) ⟨365780, by rfl⟩ : syracuseStep 487707 = 731561) B731561
theorem B2457215 : Blo 483789 2457215 := bstep (se 1 (by rfl) ⟨1842911, by rfl⟩ : syracuseStep 2457215 = 3685823) B3685823
theorem B1900351 : Blo 483789 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B819227 : Blo 483789 819227 := bstep (se 1 (by rfl) ⟨614420, by rfl⟩ : syracuseStep 819227 = 1228841) B1228841
theorem B1966295 : Blo 483789 1966295 := bstep (se 1 (by rfl) ⟨1474721, by rfl⟩ : syracuseStep 1966295 = 2949443) B2949443
theorem B919019 : Blo 483789 919019 := bstep (se 1 (by rfl) ⟨689264, by rfl⟩ : syracuseStep 919019 = 1378529) B1378529
theorem B368908937 : Blo 483789 368908937 := bstep (se 2 (by rfl) ⟨138340851, by rfl⟩ : syracuseStep 368908937 = 276681703) B276681703
theorem B729215 : Blo 483789 729215 := bstep (se 1 (by rfl) ⟨546911, by rfl⟩ : syracuseStep 729215 = 1093823) B1093823
theorem B2106551 : Blo 483789 2106551 := bstep (se 1 (by rfl) ⟨1579913, by rfl⟩ : syracuseStep 2106551 = 3159827) B3159827
theorem B10135205 : Blo 483789 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B84978665 : Blo 483789 84978665 := bstep (se 2 (by rfl) ⟨31866999, by rfl⟩ : syracuseStep 84978665 = 63733999) B63733999
theorem B25210871 : Blo 483789 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B3158999 : Blo 483789 3158999 := bstep (se 1 (by rfl) ⟨2369249, by rfl⟩ : syracuseStep 3158999 = 4738499) B4738499
theorem B2077787 : Blo 483789 2077787 := bstep (se 1 (by rfl) ⟨1558340, by rfl⟩ : syracuseStep 2077787 = 3116681) B3116681
theorem B306460853 : Blo 483789 306460853 := bstep (se 5 (by rfl) ⟨14365352, by rfl⟩ : syracuseStep 306460853 = 28730705) B28730705
theorem B2771111 : Blo 483789 2771111 := bstep (se 1 (by rfl) ⟨2078333, by rfl⟩ : syracuseStep 2771111 = 4156667) B4156667
theorem B3724663 : Blo 483789 3724663 := bstep (se 1 (by rfl) ⟨2793497, by rfl⟩ : syracuseStep 3724663 = 5586995) B5586995
theorem B68019527 : Blo 483789 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B5761151 : Blo 483789 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B1633769 : Blo 483789 1633769 := bstep (se 2 (by rfl) ⟨612663, by rfl⟩ : syracuseStep 1633769 = 1225327) B1225327
theorem B1635767 : Blo 483789 1635767 := bstep (se 1 (by rfl) ⟨1226825, by rfl⟩ : syracuseStep 1635767 = 2453651) B2453651
theorem B816635 : Blo 483789 816635 := bstep (se 1 (by rfl) ⟨612476, by rfl⟩ : syracuseStep 816635 = 1224953) B1224953
theorem B379942559 : Blo 483789 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B816871 : Blo 483789 816871 := bstep (se 1 (by rfl) ⟨612653, by rfl⟩ : syracuseStep 816871 = 1225307) B1225307
theorem B1638143 : Blo 483789 1638143 := bstep (se 1 (by rfl) ⟨1228607, by rfl⟩ : syracuseStep 1638143 = 2457215) B2457215
theorem B1310863 : Blo 483789 1310863 := bstep (se 1 (by rfl) ⟨983147, by rfl⟩ : syracuseStep 1310863 = 1966295) B1966295
theorem B6756803 : Blo 483789 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B3840767 : Blo 483789 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B1089161 : Blo 483789 1089161 := bstep (se 2 (by rfl) ⟨408435, by rfl⟩ : syracuseStep 1089161 = 816871) B816871
theorem B1089179 : Blo 483789 1089179 := bstep (se 1 (by rfl) ⟨816884, by rfl⟩ : syracuseStep 1089179 = 1633769) B1633769
theorem B2105999 : Blo 483789 2105999 := bstep (se 1 (by rfl) ⟨1579499, by rfl⟩ : syracuseStep 2105999 = 3158999) B3158999
theorem B1385191 : Blo 483789 1385191 := bstep (se 1 (by rfl) ⟨1038893, by rfl⟩ : syracuseStep 1385191 = 2077787) B2077787
theorem B1090511 : Blo 483789 1090511 := bstep (se 1 (by rfl) ⟨817883, by rfl⟩ : syracuseStep 1090511 = 1635767) B1635767
theorem B1092095 : Blo 483789 1092095 := bstep (se 1 (by rfl) ⟨819071, by rfl⟩ : syracuseStep 1092095 = 1638143) B1638143
theorem B1847407 : Blo 483789 1847407 := bstep (se 1 (by rfl) ⟨1385555, by rfl⟩ : syracuseStep 1847407 = 2771111) B2771111
theorem B5617469 : Blo 483789 5617469 := bstep (se 3 (by rfl) ⟨1053275, by rfl⟩ : syracuseStep 5617469 = 2106551) B2106551
theorem B245939291 : Blo 483789 245939291 := bstep (se 1 (by rfl) ⟨184454468, by rfl⟩ : syracuseStep 245939291 = 368908937) B368908937
theorem B4966217 : Blo 483789 4966217 := bstep (se 2 (by rfl) ⟨1862331, by rfl⟩ : syracuseStep 4966217 = 3724663) B3724663
theorem B544423 : Blo 483789 544423 := bstep (se 1 (by rfl) ⟨408317, by rfl⟩ : syracuseStep 544423 = 816635) B816635
theorem B546151 : Blo 483789 546151 := bstep (se 1 (by rfl) ⟨409613, by rfl⟩ : syracuseStep 546151 = 819227) B819227
theorem B612679 : Blo 483789 612679 := bstep (se 1 (by rfl) ⟨459509, by rfl⟩ : syracuseStep 612679 = 919019) B919019
theorem B486143 : Blo 483789 486143 := bstep (se 1 (by rfl) ⟨364607, by rfl⟩ : syracuseStep 486143 = 729215) B729215
theorem B45346351 : Blo 483789 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B56652443 : Blo 483789 56652443 := bstep (se 1 (by rfl) ⟨42489332, by rfl⟩ : syracuseStep 56652443 = 84978665) B84978665
theorem B16807247 : Blo 483789 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B253295039 : Blo 483789 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B204307235 : Blo 483789 204307235 := bstep (se 1 (by rfl) ⟨153230426, by rfl⟩ : syracuseStep 204307235 = 306460853) B306460853
theorem B3310811 : Blo 483789 3310811 := bstep (se 1 (by rfl) ⟨2483108, by rfl⟩ : syracuseStep 3310811 = 4966217) B4966217
theorem B2560511 : Blo 483789 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B60461801 : Blo 483789 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B14979917 : Blo 483789 14979917 := bstep (se 3 (by rfl) ⟨2808734, by rfl⟩ : syracuseStep 14979917 = 5617469) B5617469
theorem B725897 : Blo 483789 725897 := bstep (se 2 (by rfl) ⟨272211, by rfl⟩ : syracuseStep 725897 = 544423) B544423
theorem B726107 : Blo 483789 726107 := bstep (se 1 (by rfl) ⟨544580, by rfl⟩ : syracuseStep 726107 = 1089161) B1089161
theorem B726119 : Blo 483789 726119 := bstep (se 1 (by rfl) ⟨544589, by rfl⟩ : syracuseStep 726119 = 1089179) B1089179
theorem B2463209 : Blo 483789 2463209 := bstep (se 2 (by rfl) ⟨923703, by rfl⟩ : syracuseStep 2463209 = 1847407) B1847407
theorem B727007 : Blo 483789 727007 := bstep (se 1 (by rfl) ⟨545255, by rfl⟩ : syracuseStep 727007 = 1090511) B1090511
theorem B728063 : Blo 483789 728063 := bstep (se 1 (by rfl) ⟨546047, by rfl⟩ : syracuseStep 728063 = 1092095) B1092095
theorem B728201 : Blo 483789 728201 := bstep (se 2 (by rfl) ⟨273075, by rfl⟩ : syracuseStep 728201 = 546151) B546151
theorem B168863359 : Blo 483789 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B1747817 : Blo 483789 1747817 := bstep (se 2 (by rfl) ⟨655431, by rfl⟩ : syracuseStep 1747817 = 1310863) B1310863
theorem B1846921 : Blo 483789 1846921 := bstep (se 2 (by rfl) ⟨692595, by rfl⟩ : syracuseStep 1846921 = 1385191) B1385191
theorem B4504535 : Blo 483789 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B37768295 : Blo 483789 37768295 := bstep (se 1 (by rfl) ⟨28326221, by rfl⟩ : syracuseStep 37768295 = 56652443) B56652443
theorem B136204823 : Blo 483789 136204823 := bstep (se 1 (by rfl) ⟨102153617, by rfl⟩ : syracuseStep 136204823 = 204307235) B204307235
theorem B163959527 : Blo 483789 163959527 := bstep (se 1 (by rfl) ⟨122969645, by rfl⟩ : syracuseStep 163959527 = 245939291) B245939291
theorem B1403999 : Blo 483789 1403999 := bstep (se 1 (by rfl) ⟨1052999, by rfl⟩ : syracuseStep 1403999 = 2105999) B2105999
theorem B816905 : Blo 483789 816905 := bstep (se 2 (by rfl) ⟨306339, by rfl⟩ : syracuseStep 816905 = 612679) B612679
theorem B11204831 : Blo 483789 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B225151145 : Blo 483789 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B39946445 : Blo 483789 39946445 := bstep (se 3 (by rfl) ⟨7489958, by rfl⟩ : syracuseStep 39946445 = 14979917) B14979917
theorem B1707007 : Blo 483789 1707007 := bstep (se 1 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 1707007 = 2560511) B2560511
theorem B90803215 : Blo 483789 90803215 := bstep (se 1 (by rfl) ⟨68102411, by rfl⟩ : syracuseStep 90803215 = 136204823) B136204823
theorem B40307867 : Blo 483789 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B1642139 : Blo 483789 1642139 := bstep (se 1 (by rfl) ⟨1231604, by rfl⟩ : syracuseStep 1642139 = 2463209) B2463209
theorem B2462561 : Blo 483789 2462561 := bstep (se 2 (by rfl) ⟨923460, by rfl⟩ : syracuseStep 2462561 = 1846921) B1846921
theorem B2207207 : Blo 483789 2207207 := bstep (se 1 (by rfl) ⟨1655405, by rfl⟩ : syracuseStep 2207207 = 3310811) B3310811
theorem B25178863 : Blo 483789 25178863 := bstep (se 1 (by rfl) ⟨18884147, by rfl⟩ : syracuseStep 25178863 = 37768295) B37768295
theorem B1165211 : Blo 483789 1165211 := bstep (se 1 (by rfl) ⟨873908, by rfl⟩ : syracuseStep 1165211 = 1747817) B1747817
theorem B935999 : Blo 483789 935999 := bstep (se 1 (by rfl) ⟨701999, by rfl⟩ : syracuseStep 935999 = 1403999) B1403999
theorem B544603 : Blo 483789 544603 := bstep (se 1 (by rfl) ⟨408452, by rfl⟩ : syracuseStep 544603 = 816905) B816905
theorem B3003023 : Blo 483789 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B109306351 : Blo 483789 109306351 := bstep (se 1 (by rfl) ⟨81979763, by rfl⟩ : syracuseStep 109306351 = 163959527) B163959527
theorem B483931 : Blo 483789 483931 := bstep (se 1 (by rfl) ⟨362948, by rfl⟩ : syracuseStep 483931 = 725897) B725897
theorem B484071 : Blo 483789 484071 := bstep (se 1 (by rfl) ⟨363053, by rfl⟩ : syracuseStep 484071 = 726107) B726107
theorem B484079 : Blo 483789 484079 := bstep (se 1 (by rfl) ⟨363059, by rfl⟩ : syracuseStep 484079 = 726119) B726119
theorem B484671 : Blo 483789 484671 := bstep (se 1 (by rfl) ⟨363503, by rfl⟩ : syracuseStep 484671 = 727007) B727007
theorem B485375 : Blo 483789 485375 := bstep (se 1 (by rfl) ⟨364031, by rfl⟩ : syracuseStep 485375 = 728063) B728063
theorem B485467 : Blo 483789 485467 := bstep (se 1 (by rfl) ⟨364100, by rfl⟩ : syracuseStep 485467 = 728201) B728201
theorem B7469887 : Blo 483789 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B623999 : Blo 483789 623999 := bstep (se 1 (by rfl) ⟨467999, by rfl⟩ : syracuseStep 623999 = 935999) B935999
theorem B26871911 : Blo 483789 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B2002015 : Blo 483789 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B1641707 : Blo 483789 1641707 := bstep (se 1 (by rfl) ⟨1231280, by rfl⟩ : syracuseStep 1641707 = 2462561) B2462561
theorem B726137 : Blo 483789 726137 := bstep (se 2 (by rfl) ⟨272301, by rfl⟩ : syracuseStep 726137 = 544603) B544603
theorem B2401612213 : Blo 483789 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B1094759 : Blo 483789 1094759 := bstep (se 1 (by rfl) ⟨821069, by rfl⟩ : syracuseStep 1094759 = 1642139) B1642139
theorem B2276009 : Blo 483789 2276009 := bstep (se 2 (by rfl) ⟨853503, by rfl⟩ : syracuseStep 2276009 = 1707007) B1707007
theorem B33571817 : Blo 483789 33571817 := bstep (se 2 (by rfl) ⟨12589431, by rfl⟩ : syracuseStep 33571817 = 25178863) B25178863
theorem B5885885 : Blo 483789 5885885 := bstep (se 3 (by rfl) ⟨1103603, by rfl⟩ : syracuseStep 5885885 = 2207207) B2207207
theorem B145741801 : Blo 483789 145741801 := bstep (se 2 (by rfl) ⟨54653175, by rfl⟩ : syracuseStep 145741801 = 109306351) B109306351
theorem B776807 : Blo 483789 776807 := bstep (se 1 (by rfl) ⟨582605, by rfl⟩ : syracuseStep 776807 = 1165211) B1165211
theorem B26630963 : Blo 483789 26630963 := bstep (se 1 (by rfl) ⟨19973222, by rfl⟩ : syracuseStep 26630963 = 39946445) B39946445
theorem B121070953 : Blo 483789 121070953 := bstep (se 2 (by rfl) ⟨45401607, by rfl⟩ : syracuseStep 121070953 = 90803215) B90803215
theorem B9959849 : Blo 483789 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B22381211 : Blo 483789 22381211 := bstep (se 1 (by rfl) ⟨16785908, by rfl⟩ : syracuseStep 22381211 = 33571817) B33571817
theorem B194322401 : Blo 483789 194322401 := bstep (se 2 (by rfl) ⟨72870900, by rfl⟩ : syracuseStep 194322401 = 145741801) B145741801
theorem B729839 : Blo 483789 729839 := bstep (se 1 (by rfl) ⟨547379, by rfl⟩ : syracuseStep 729839 = 1094759) B1094759
theorem B1517339 : Blo 483789 1517339 := bstep (se 1 (by rfl) ⟨1138004, by rfl⟩ : syracuseStep 1517339 = 2276009) B2276009
theorem B161427937 : Blo 483789 161427937 := bstep (se 2 (by rfl) ⟨60535476, by rfl⟩ : syracuseStep 161427937 = 121070953) B121070953
theorem B1094471 : Blo 483789 1094471 := bstep (se 1 (by rfl) ⟨820853, by rfl⟩ : syracuseStep 1094471 = 1641707) B1641707
theorem B6639899 : Blo 483789 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B17914607 : Blo 483789 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B3923923 : Blo 483789 3923923 := bstep (se 1 (by rfl) ⟨2942942, by rfl⟩ : syracuseStep 3923923 = 5885885) B5885885
theorem B484091 : Blo 483789 484091 := bstep (se 1 (by rfl) ⟨363068, by rfl⟩ : syracuseStep 484091 = 726137) B726137
theorem B1663997 : Blo 483789 1663997 := bstep (se 3 (by rfl) ⟨311999, by rfl⟩ : syracuseStep 1663997 = 623999) B623999
theorem B517871 : Blo 483789 517871 := bstep (se 1 (by rfl) ⟨388403, by rfl⟩ : syracuseStep 517871 = 776807) B776807
theorem B17753975 : Blo 483789 17753975 := bstep (se 1 (by rfl) ⟨13315481, by rfl⟩ : syracuseStep 17753975 = 26630963) B26630963
theorem B10677413 : Blo 483789 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B3202149617 : Blo 483789 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B1380989 : Blo 483789 1380989 := bstep (se 3 (by rfl) ⟨258935, by rfl⟩ : syracuseStep 1380989 = 517871) B517871
theorem B11835983 : Blo 483789 11835983 := bstep (se 1 (by rfl) ⟨8876987, by rfl⟩ : syracuseStep 11835983 = 17753975) B17753975
theorem B7118275 : Blo 483789 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B729647 : Blo 483789 729647 := bstep (se 1 (by rfl) ⟨547235, by rfl⟩ : syracuseStep 729647 = 1094471) B1094471
theorem B14920807 : Blo 483789 14920807 := bstep (se 1 (by rfl) ⟨11190605, by rfl⟩ : syracuseStep 14920807 = 22381211) B22381211
theorem B17706397 : Blo 483789 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B4437325 : Blo 483789 4437325 := bstep (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) B1663997
theorem B11943071 : Blo 483789 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B129548267 : Blo 483789 129548267 := bstep (se 1 (by rfl) ⟨97161200, by rfl⟩ : syracuseStep 129548267 = 194322401) B194322401
theorem B215237249 : Blo 483789 215237249 := bstep (se 2 (by rfl) ⟨80713968, by rfl⟩ : syracuseStep 215237249 = 161427937) B161427937
theorem B5231897 : Blo 483789 5231897 := bstep (se 2 (by rfl) ⟨1961961, by rfl⟩ : syracuseStep 5231897 = 3923923) B3923923
theorem B486559 : Blo 483789 486559 := bstep (se 1 (by rfl) ⟨364919, by rfl⟩ : syracuseStep 486559 = 729839) B729839
theorem B1011559 : Blo 483789 1011559 := bstep (se 1 (by rfl) ⟨758669, by rfl⟩ : syracuseStep 1011559 = 1517339) B1517339
theorem B2134766411 : Blo 483789 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B143491499 : Blo 483789 143491499 := bstep (se 1 (by rfl) ⟨107618624, by rfl⟩ : syracuseStep 143491499 = 215237249) B215237249
theorem B920659 : Blo 483789 920659 := bstep (se 1 (by rfl) ⟨690494, by rfl⟩ : syracuseStep 920659 = 1380989) B1380989
theorem B19894409 : Blo 483789 19894409 := bstep (se 2 (by rfl) ⟨7460403, by rfl⟩ : syracuseStep 19894409 = 14920807) B14920807
theorem B1348745 : Blo 483789 1348745 := bstep (se 2 (by rfl) ⟨505779, by rfl⟩ : syracuseStep 1348745 = 1011559) B1011559
theorem B23665733 : Blo 483789 23665733 := bstep (se 4 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 23665733 = 4437325) B4437325
theorem B3487931 : Blo 483789 3487931 := bstep (se 1 (by rfl) ⟨2615948, by rfl⟩ : syracuseStep 3487931 = 5231897) B5231897
theorem B23608529 : Blo 483789 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B9491033 : Blo 483789 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B86365511 : Blo 483789 86365511 := bstep (se 1 (by rfl) ⟨64774133, by rfl⟩ : syracuseStep 86365511 = 129548267) B129548267
theorem B7890655 : Blo 483789 7890655 := bstep (se 1 (by rfl) ⟨5917991, by rfl⟩ : syracuseStep 7890655 = 11835983) B11835983
theorem B486431 : Blo 483789 486431 := bstep (se 1 (by rfl) ⟨364823, by rfl⟩ : syracuseStep 486431 = 729647) B729647
theorem B1423177607 : Blo 483789 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B7962047 : Blo 483789 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B10520873 : Blo 483789 10520873 := bstep (se 2 (by rfl) ⟨3945327, by rfl⟩ : syracuseStep 10520873 = 7890655) B7890655
theorem B57577007 : Blo 483789 57577007 := bstep (se 1 (by rfl) ⟨43182755, by rfl⟩ : syracuseStep 57577007 = 86365511) B86365511
theorem B15739019 : Blo 483789 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B95660999 : Blo 483789 95660999 := bstep (se 1 (by rfl) ⟨71745749, by rfl⟩ : syracuseStep 95660999 = 143491499) B143491499
theorem B25309421 : Blo 483789 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B1227545 : Blo 483789 1227545 := bstep (se 2 (by rfl) ⟨460329, by rfl⟩ : syracuseStep 1227545 = 920659) B920659
theorem B15777155 : Blo 483789 15777155 := bstep (se 1 (by rfl) ⟨11832866, by rfl⟩ : syracuseStep 15777155 = 23665733) B23665733
theorem B948785071 : Blo 483789 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B13262939 : Blo 483789 13262939 := bstep (se 1 (by rfl) ⟨9947204, by rfl⟩ : syracuseStep 13262939 = 19894409) B19894409
theorem B3596653 : Blo 483789 3596653 := bstep (se 3 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 3596653 = 1348745) B1348745
theorem B2325287 : Blo 483789 2325287 := bstep (se 1 (by rfl) ⟨1743965, by rfl⟩ : syracuseStep 2325287 = 3487931) B3487931
theorem B5308031 : Blo 483789 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B7013915 : Blo 483789 7013915 := bstep (se 1 (by rfl) ⟨5260436, by rfl⟩ : syracuseStep 7013915 = 10520873) B10520873
theorem B1265046761 : Blo 483789 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B10492679 : Blo 483789 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B63773999 : Blo 483789 63773999 := bstep (se 1 (by rfl) ⟨47830499, by rfl⟩ : syracuseStep 63773999 = 95660999) B95660999
theorem B1550191 : Blo 483789 1550191 := bstep (se 1 (by rfl) ⟨1162643, by rfl⟩ : syracuseStep 1550191 = 2325287) B2325287
theorem B4795537 : Blo 483789 4795537 := bstep (se 2 (by rfl) ⟨1798326, by rfl⟩ : syracuseStep 4795537 = 3596653) B3596653
theorem B38384671 : Blo 483789 38384671 := bstep (se 1 (by rfl) ⟨28788503, by rfl⟩ : syracuseStep 38384671 = 57577007) B57577007
theorem B8841959 : Blo 483789 8841959 := bstep (se 1 (by rfl) ⟨6631469, by rfl⟩ : syracuseStep 8841959 = 13262939) B13262939
theorem B16872947 : Blo 483789 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B818363 : Blo 483789 818363 := bstep (se 1 (by rfl) ⟨613772, by rfl⟩ : syracuseStep 818363 = 1227545) B1227545
theorem B10518103 : Blo 483789 10518103 := bstep (se 1 (by rfl) ⟨7888577, by rfl⟩ : syracuseStep 10518103 = 15777155) B15777155
theorem B3538687 : Blo 483789 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B2066921 : Blo 483789 2066921 := bstep (se 2 (by rfl) ⟨775095, by rfl⟩ : syracuseStep 2066921 = 1550191) B1550191
theorem B6394049 : Blo 483789 6394049 := bstep (se 2 (by rfl) ⟨2397768, by rfl⟩ : syracuseStep 6394049 = 4795537) B4795537
theorem B11248631 : Blo 483789 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B843364507 : Blo 483789 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B6995119 : Blo 483789 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B42515999 : Blo 483789 42515999 := bstep (se 1 (by rfl) ⟨31886999, by rfl⟩ : syracuseStep 42515999 = 63773999) B63773999
theorem B545575 : Blo 483789 545575 := bstep (se 1 (by rfl) ⟨409181, by rfl⟩ : syracuseStep 545575 = 818363) B818363
theorem B4675943 : Blo 483789 4675943 := bstep (se 1 (by rfl) ⟨3506957, by rfl⟩ : syracuseStep 4675943 = 7013915) B7013915
theorem B51179561 : Blo 483789 51179561 := bstep (se 2 (by rfl) ⟨19192335, by rfl⟩ : syracuseStep 51179561 = 38384671) B38384671
theorem B5894639 : Blo 483789 5894639 := bstep (se 1 (by rfl) ⟨4420979, by rfl⟩ : syracuseStep 5894639 = 8841959) B8841959
theorem B14024137 : Blo 483789 14024137 := bstep (se 2 (by rfl) ⟨5259051, by rfl⟩ : syracuseStep 14024137 = 10518103) B10518103
theorem B4718249 : Blo 483789 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B1377947 : Blo 483789 1377947 := bstep (se 1 (by rfl) ⟨1033460, by rfl⟩ : syracuseStep 1377947 = 2066921) B2066921
theorem B4262699 : Blo 483789 4262699 := bstep (se 1 (by rfl) ⟨3197024, by rfl⟩ : syracuseStep 4262699 = 6394049) B6394049
theorem B3117295 : Blo 483789 3117295 := bstep (se 1 (by rfl) ⟨2337971, by rfl⟩ : syracuseStep 3117295 = 4675943) B4675943
theorem B727433 : Blo 483789 727433 := bstep (se 2 (by rfl) ⟨272787, by rfl⟩ : syracuseStep 727433 = 545575) B545575
theorem B34119707 : Blo 483789 34119707 := bstep (se 1 (by rfl) ⟨25589780, by rfl⟩ : syracuseStep 34119707 = 51179561) B51179561
theorem B1124486009 : Blo 483789 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B9326825 : Blo 483789 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B18698849 : Blo 483789 18698849 := bstep (se 2 (by rfl) ⟨7012068, by rfl⟩ : syracuseStep 18698849 = 14024137) B14024137
theorem B7499087 : Blo 483789 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B3929759 : Blo 483789 3929759 := bstep (se 1 (by rfl) ⟨2947319, by rfl⟩ : syracuseStep 3929759 = 5894639) B5894639
theorem B28343999 : Blo 483789 28343999 := bstep (se 1 (by rfl) ⟨21257999, by rfl⟩ : syracuseStep 28343999 = 42515999) B42515999
theorem B3145499 : Blo 483789 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B918631 : Blo 483789 918631 := bstep (se 1 (by rfl) ⟨688973, by rfl⟩ : syracuseStep 918631 = 1377947) B1377947
theorem B12465899 : Blo 483789 12465899 := bstep (se 1 (by rfl) ⟨9349424, by rfl⟩ : syracuseStep 12465899 = 18698849) B18698849
theorem B4999391 : Blo 483789 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B18895999 : Blo 483789 18895999 := bstep (se 1 (by rfl) ⟨14171999, by rfl⟩ : syracuseStep 18895999 = 28343999) B28343999
theorem B90985885 : Blo 483789 90985885 := bstep (se 3 (by rfl) ⟨17059853, by rfl⟩ : syracuseStep 90985885 = 34119707) B34119707
theorem B2841799 : Blo 483789 2841799 := bstep (se 1 (by rfl) ⟨2131349, by rfl⟩ : syracuseStep 2841799 = 4262699) B4262699
theorem B749657339 : Blo 483789 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B6217883 : Blo 483789 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B484955 : Blo 483789 484955 := bstep (se 1 (by rfl) ⟨363716, by rfl⟩ : syracuseStep 484955 = 727433) B727433
theorem B4156393 : Blo 483789 4156393 := bstep (se 2 (by rfl) ⟨1558647, by rfl⟩ : syracuseStep 4156393 = 3117295) B3117295
theorem B2619839 : Blo 483789 2619839 := bstep (se 1 (by rfl) ⟨1964879, by rfl⟩ : syracuseStep 2619839 = 3929759) B3929759
theorem B2096999 : Blo 483789 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B5541857 : Blo 483789 5541857 := bstep (se 2 (by rfl) ⟨2078196, by rfl⟩ : syracuseStep 5541857 = 4156393) B4156393
theorem B1746559 : Blo 483789 1746559 := bstep (se 1 (by rfl) ⟨1309919, by rfl⟩ : syracuseStep 1746559 = 2619839) B2619839
theorem B1224841 : Blo 483789 1224841 := bstep (se 2 (by rfl) ⟨459315, by rfl⟩ : syracuseStep 1224841 = 918631) B918631
theorem B4145255 : Blo 483789 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B8310599 : Blo 483789 8310599 := bstep (se 1 (by rfl) ⟨6232949, by rfl⟩ : syracuseStep 8310599 = 12465899) B12465899
theorem B3789065 : Blo 483789 3789065 := bstep (se 2 (by rfl) ⟨1420899, by rfl⟩ : syracuseStep 3789065 = 2841799) B2841799
theorem B1397999 : Blo 483789 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B3332927 : Blo 483789 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B499771559 : Blo 483789 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B25194665 : Blo 483789 25194665 := bstep (se 2 (by rfl) ⟨9447999, by rfl⟩ : syracuseStep 25194665 = 18895999) B18895999
theorem B485258053 : Blo 483789 485258053 := bstep (se 4 (by rfl) ⟨45492942, by rfl⟩ : syracuseStep 485258053 = 90985885) B90985885
theorem B2328745 : Blo 483789 2328745 := bstep (se 2 (by rfl) ⟨873279, by rfl⟩ : syracuseStep 2328745 = 1746559) B1746559
theorem B5540399 : Blo 483789 5540399 := bstep (se 1 (by rfl) ⟨4155299, by rfl⟩ : syracuseStep 5540399 = 8310599) B8310599
theorem B647010737 : Blo 483789 647010737 := bstep (se 2 (by rfl) ⟨242629026, by rfl⟩ : syracuseStep 647010737 = 485258053) B485258053
theorem B2763503 : Blo 483789 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B10104173 : Blo 483789 10104173 := bstep (se 3 (by rfl) ⟨1894532, by rfl⟩ : syracuseStep 10104173 = 3789065) B3789065
theorem B931999 : Blo 483789 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B16796443 : Blo 483789 16796443 := bstep (se 1 (by rfl) ⟨12597332, by rfl⟩ : syracuseStep 16796443 = 25194665) B25194665
theorem B3694571 : Blo 483789 3694571 := bstep (se 1 (by rfl) ⟨2770928, by rfl⟩ : syracuseStep 3694571 = 5541857) B5541857
theorem B2221951 : Blo 483789 2221951 := bstep (se 1 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 2221951 = 3332927) B3332927
theorem B1633121 : Blo 483789 1633121 := bstep (se 2 (by rfl) ⟨612420, by rfl⟩ : syracuseStep 1633121 = 1224841) B1224841
theorem B333181039 : Blo 483789 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B2463047 : Blo 483789 2463047 := bstep (se 1 (by rfl) ⟨1847285, by rfl⟩ : syracuseStep 2463047 = 3694571) B3694571
theorem B444241385 : Blo 483789 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B1842335 : Blo 483789 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B1088747 : Blo 483789 1088747 := bstep (se 1 (by rfl) ⟨816560, by rfl⟩ : syracuseStep 1088747 = 1633121) B1633121
theorem B2962601 : Blo 483789 2962601 := bstep (se 2 (by rfl) ⟨1110975, by rfl⟩ : syracuseStep 2962601 = 2221951) B2221951
theorem B22395257 : Blo 483789 22395257 := bstep (se 2 (by rfl) ⟨8398221, by rfl⟩ : syracuseStep 22395257 = 16796443) B16796443
theorem B431340491 : Blo 483789 431340491 := bstep (se 1 (by rfl) ⟨323505368, by rfl⟩ : syracuseStep 431340491 = 647010737) B647010737
theorem B6736115 : Blo 483789 6736115 := bstep (se 1 (by rfl) ⟨5052086, by rfl⟩ : syracuseStep 6736115 = 10104173) B10104173
theorem B3693599 : Blo 483789 3693599 := bstep (se 1 (by rfl) ⟨2770199, by rfl⟩ : syracuseStep 3693599 = 5540399) B5540399
theorem B3104993 : Blo 483789 3104993 := bstep (se 2 (by rfl) ⟨1164372, by rfl⟩ : syracuseStep 3104993 = 2328745) B2328745
theorem B1242665 : Blo 483789 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B4490743 : Blo 483789 4490743 := bstep (se 1 (by rfl) ⟨3368057, by rfl⟩ : syracuseStep 4490743 = 6736115) B6736115
theorem B1642031 : Blo 483789 1642031 := bstep (se 1 (by rfl) ⟨1231523, by rfl⟩ : syracuseStep 1642031 = 2463047) B2463047
theorem B296160923 : Blo 483789 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B2462399 : Blo 483789 2462399 := bstep (se 1 (by rfl) ⟨1846799, by rfl⟩ : syracuseStep 2462399 = 3693599) B3693599
theorem B725831 : Blo 483789 725831 := bstep (se 1 (by rfl) ⟨544373, by rfl⟩ : syracuseStep 725831 = 1088747) B1088747
theorem B1975067 : Blo 483789 1975067 := bstep (se 1 (by rfl) ⟨1481300, by rfl⟩ : syracuseStep 1975067 = 2962601) B2962601
theorem B828443 : Blo 483789 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B1228223 : Blo 483789 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B14930171 : Blo 483789 14930171 := bstep (se 1 (by rfl) ⟨11197628, by rfl⟩ : syracuseStep 14930171 = 22395257) B22395257
theorem B287560327 : Blo 483789 287560327 := bstep (se 1 (by rfl) ⟨215670245, by rfl⟩ : syracuseStep 287560327 = 431340491) B431340491
theorem B8279981 : Blo 483789 8279981 := bstep (se 3 (by rfl) ⟨1552496, by rfl⟩ : syracuseStep 8279981 = 3104993) B3104993
theorem B1641599 : Blo 483789 1641599 := bstep (se 1 (by rfl) ⟨1231199, by rfl⟩ : syracuseStep 1641599 = 2462399) B2462399
theorem B1316711 : Blo 483789 1316711 := bstep (se 1 (by rfl) ⟨987533, by rfl⟩ : syracuseStep 1316711 = 1975067) B1975067
theorem B1094687 : Blo 483789 1094687 := bstep (se 1 (by rfl) ⟨821015, by rfl⟩ : syracuseStep 1094687 = 1642031) B1642031
theorem B197440615 : Blo 483789 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B5519987 : Blo 483789 5519987 := bstep (se 1 (by rfl) ⟨4139990, by rfl⟩ : syracuseStep 5519987 = 8279981) B8279981
theorem B5987657 : Blo 483789 5987657 := bstep (se 2 (by rfl) ⟨2245371, by rfl⟩ : syracuseStep 5987657 = 4490743) B4490743
theorem B9953447 : Blo 483789 9953447 := bstep (se 1 (by rfl) ⟨7465085, by rfl⟩ : syracuseStep 9953447 = 14930171) B14930171
theorem B483887 : Blo 483789 483887 := bstep (se 1 (by rfl) ⟨362915, by rfl⟩ : syracuseStep 483887 = 725831) B725831
theorem B552295 : Blo 483789 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B383413769 : Blo 483789 383413769 := bstep (se 2 (by rfl) ⟨143780163, by rfl⟩ : syracuseStep 383413769 = 287560327) B287560327
theorem B818815 : Blo 483789 818815 := bstep (se 1 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 818815 = 1228223) B1228223
theorem B26542525 : Blo 483789 26542525 := bstep (se 3 (by rfl) ⟨4976723, by rfl⟩ : syracuseStep 26542525 = 9953447) B9953447
theorem B729791 : Blo 483789 729791 := bstep (se 1 (by rfl) ⟨547343, by rfl⟩ : syracuseStep 729791 = 1094687) B1094687
theorem B3679991 : Blo 483789 3679991 := bstep (se 1 (by rfl) ⟨2759993, by rfl⟩ : syracuseStep 3679991 = 5519987) B5519987
theorem B1091753 : Blo 483789 1091753 := bstep (se 2 (by rfl) ⟨409407, by rfl⟩ : syracuseStep 1091753 = 818815) B818815
theorem B1094399 : Blo 483789 1094399 := bstep (se 1 (by rfl) ⟨820799, by rfl⟩ : syracuseStep 1094399 = 1641599) B1641599
theorem B736393 : Blo 483789 736393 := bstep (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) B552295
theorem B255609179 : Blo 483789 255609179 := bstep (se 1 (by rfl) ⟨191706884, by rfl⟩ : syracuseStep 255609179 = 383413769) B383413769
theorem B877807 : Blo 483789 877807 := bstep (se 1 (by rfl) ⟨658355, by rfl⟩ : syracuseStep 877807 = 1316711) B1316711
theorem B3991771 : Blo 483789 3991771 := bstep (se 1 (by rfl) ⟨2993828, by rfl⟩ : syracuseStep 3991771 = 5987657) B5987657
theorem B263254153 : Blo 483789 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B35390033 : Blo 483789 35390033 := bstep (se 2 (by rfl) ⟨13271262, by rfl⟩ : syracuseStep 35390033 = 26542525) B26542525
theorem B727835 : Blo 483789 727835 := bstep (se 1 (by rfl) ⟨545876, by rfl⟩ : syracuseStep 727835 = 1091753) B1091753
theorem B729599 : Blo 483789 729599 := bstep (se 1 (by rfl) ⟨547199, by rfl⟩ : syracuseStep 729599 = 1094399) B1094399
theorem B170406119 : Blo 483789 170406119 := bstep (se 1 (by rfl) ⟨127804589, by rfl⟩ : syracuseStep 170406119 = 255609179) B255609179
theorem B5322361 : Blo 483789 5322361 := bstep (se 2 (by rfl) ⟨1995885, by rfl⟩ : syracuseStep 5322361 = 3991771) B3991771
theorem B351005537 : Blo 483789 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B486527 : Blo 483789 486527 := bstep (se 1 (by rfl) ⟨364895, by rfl⟩ : syracuseStep 486527 = 729791) B729791
theorem B2453327 : Blo 483789 2453327 := bstep (se 1 (by rfl) ⟨1839995, by rfl⟩ : syracuseStep 2453327 = 3679991) B3679991
theorem B4681637 : Blo 483789 4681637 := bstep (se 4 (by rfl) ⟨438903, by rfl⟩ : syracuseStep 4681637 = 877807) B877807
theorem B981857 : Blo 483789 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B23593355 : Blo 483789 23593355 := bstep (se 1 (by rfl) ⟨17695016, by rfl⟩ : syracuseStep 23593355 = 35390033) B35390033
theorem B234003691 : Blo 483789 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B3121091 : Blo 483789 3121091 := bstep (se 1 (by rfl) ⟨2340818, by rfl⟩ : syracuseStep 3121091 = 4681637) B4681637
theorem B7096481 : Blo 483789 7096481 := bstep (se 2 (by rfl) ⟨2661180, by rfl⟩ : syracuseStep 7096481 = 5322361) B5322361
theorem B454416317 : Blo 483789 454416317 := bstep (se 3 (by rfl) ⟨85203059, by rfl⟩ : syracuseStep 454416317 = 170406119) B170406119
theorem B485223 : Blo 483789 485223 := bstep (se 1 (by rfl) ⟨363917, by rfl⟩ : syracuseStep 485223 = 727835) B727835
theorem B486399 : Blo 483789 486399 := bstep (se 1 (by rfl) ⟨364799, by rfl⟩ : syracuseStep 486399 = 729599) B729599
theorem B1635551 : Blo 483789 1635551 := bstep (se 1 (by rfl) ⟨1226663, by rfl⟩ : syracuseStep 1635551 = 2453327) B2453327
theorem B654571 : Blo 483789 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B15728903 : Blo 483789 15728903 := bstep (se 1 (by rfl) ⟨11796677, by rfl⟩ : syracuseStep 15728903 = 23593355) B23593355
theorem B302944211 : Blo 483789 302944211 := bstep (se 1 (by rfl) ⟨227208158, by rfl⟩ : syracuseStep 302944211 = 454416317) B454416317
theorem B1090367 : Blo 483789 1090367 := bstep (se 1 (by rfl) ⟨817775, by rfl⟩ : syracuseStep 1090367 = 1635551) B1635551
theorem B4730987 : Blo 483789 4730987 := bstep (se 1 (by rfl) ⟨3548240, by rfl⟩ : syracuseStep 4730987 = 7096481) B7096481
theorem B2080727 : Blo 483789 2080727 := bstep (se 1 (by rfl) ⟨1560545, by rfl⟩ : syracuseStep 2080727 = 3121091) B3121091
theorem B3491045 : Blo 483789 3491045 := bstep (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) B654571
theorem B312004921 : Blo 483789 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B10485935 : Blo 483789 10485935 := bstep (se 1 (by rfl) ⟨7864451, by rfl⟩ : syracuseStep 10485935 = 15728903) B15728903
theorem B2327363 : Blo 483789 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B726911 : Blo 483789 726911 := bstep (se 1 (by rfl) ⟨545183, by rfl⟩ : syracuseStep 726911 = 1090367) B1090367
theorem B3153991 : Blo 483789 3153991 := bstep (se 1 (by rfl) ⟨2365493, by rfl⟩ : syracuseStep 3153991 = 4730987) B4730987
theorem B1387151 : Blo 483789 1387151 := bstep (se 1 (by rfl) ⟨1040363, by rfl⟩ : syracuseStep 1387151 = 2080727) B2080727
theorem B201962807 : Blo 483789 201962807 := bstep (se 1 (by rfl) ⟨151472105, by rfl⟩ : syracuseStep 201962807 = 302944211) B302944211
theorem B416006561 : Blo 483789 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B924767 : Blo 483789 924767 := bstep (se 1 (by rfl) ⟨693575, by rfl⟩ : syracuseStep 924767 = 1387151) B1387151
theorem B4205321 : Blo 483789 4205321 := bstep (se 2 (by rfl) ⟨1576995, by rfl⟩ : syracuseStep 4205321 = 3153991) B3153991
theorem B6990623 : Blo 483789 6990623 := bstep (se 1 (by rfl) ⟨5242967, by rfl⟩ : syracuseStep 6990623 = 10485935) B10485935
theorem B1551575 : Blo 483789 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B1109350829 : Blo 483789 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B484607 : Blo 483789 484607 := bstep (se 1 (by rfl) ⟨363455, by rfl⟩ : syracuseStep 484607 = 726911) B726911
theorem B134641871 : Blo 483789 134641871 := bstep (se 1 (by rfl) ⟨100981403, by rfl⟩ : syracuseStep 134641871 = 201962807) B201962807
theorem B4660415 : Blo 483789 4660415 := bstep (se 1 (by rfl) ⟨3495311, by rfl⟩ : syracuseStep 4660415 = 6990623) B6990623
theorem B89761247 : Blo 483789 89761247 := bstep (se 1 (by rfl) ⟨67320935, by rfl⟩ : syracuseStep 89761247 = 134641871) B134641871
theorem B2803547 : Blo 483789 2803547 := bstep (se 1 (by rfl) ⟨2102660, by rfl⟩ : syracuseStep 2803547 = 4205321) B4205321
theorem B1034383 : Blo 483789 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B739567219 : Blo 483789 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B616511 : Blo 483789 616511 := bstep (se 1 (by rfl) ⟨462383, by rfl⟩ : syracuseStep 616511 = 924767) B924767
theorem B1869031 : Blo 483789 1869031 := bstep (se 1 (by rfl) ⟨1401773, by rfl⟩ : syracuseStep 1869031 = 2803547) B2803547
theorem B986089625 : Blo 483789 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B1379177 : Blo 483789 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B1644029 : Blo 483789 1644029 := bstep (se 3 (by rfl) ⟨308255, by rfl⟩ : syracuseStep 1644029 = 616511) B616511
theorem B59840831 : Blo 483789 59840831 := bstep (se 1 (by rfl) ⟨44880623, by rfl⟩ : syracuseStep 59840831 = 89761247) B89761247
theorem B3106943 : Blo 483789 3106943 := bstep (se 1 (by rfl) ⟨2330207, by rfl⟩ : syracuseStep 3106943 = 4660415) B4660415
theorem B657393083 : Blo 483789 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B2492041 : Blo 483789 2492041 := bstep (se 2 (by rfl) ⟨934515, by rfl⟩ : syracuseStep 2492041 = 1869031) B1869031
theorem B919451 : Blo 483789 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B2071295 : Blo 483789 2071295 := bstep (se 1 (by rfl) ⟨1553471, by rfl⟩ : syracuseStep 2071295 = 3106943) B3106943
theorem B1096019 : Blo 483789 1096019 := bstep (se 1 (by rfl) ⟨822014, by rfl⟩ : syracuseStep 1096019 = 1644029) B1644029
theorem B39893887 : Blo 483789 39893887 := bstep (se 1 (by rfl) ⟨29920415, by rfl⟩ : syracuseStep 39893887 = 59840831) B59840831
theorem B1380863 : Blo 483789 1380863 := bstep (se 1 (by rfl) ⟨1035647, by rfl⟩ : syracuseStep 1380863 = 2071295) B2071295
theorem B53191849 : Blo 483789 53191849 := bstep (se 2 (by rfl) ⟨19946943, by rfl⟩ : syracuseStep 53191849 = 39893887) B39893887
theorem B730679 : Blo 483789 730679 := bstep (se 1 (by rfl) ⟨548009, by rfl⟩ : syracuseStep 730679 = 1096019) B1096019
theorem B3322721 : Blo 483789 3322721 := bstep (se 2 (by rfl) ⟨1246020, by rfl⟩ : syracuseStep 3322721 = 2492041) B2492041
theorem B438262055 : Blo 483789 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B2451869 : Blo 483789 2451869 := bstep (se 3 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 2451869 = 919451) B919451
theorem B920575 : Blo 483789 920575 := bstep (se 1 (by rfl) ⟨690431, by rfl⟩ : syracuseStep 920575 = 1380863) B1380863
theorem B70922465 : Blo 483789 70922465 := bstep (se 2 (by rfl) ⟨26595924, by rfl⟩ : syracuseStep 70922465 = 53191849) B53191849
theorem B292174703 : Blo 483789 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B2215147 : Blo 483789 2215147 := bstep (se 1 (by rfl) ⟨1661360, by rfl⟩ : syracuseStep 2215147 = 3322721) B3322721
theorem B487119 : Blo 483789 487119 := bstep (se 1 (by rfl) ⟨365339, by rfl⟩ : syracuseStep 487119 = 730679) B730679
theorem B1634579 : Blo 483789 1634579 := bstep (se 1 (by rfl) ⟨1225934, by rfl⟩ : syracuseStep 1634579 = 2451869) B2451869
theorem B2953529 : Blo 483789 2953529 := bstep (se 2 (by rfl) ⟨1107573, by rfl⟩ : syracuseStep 2953529 = 2215147) B2215147
theorem B1089719 : Blo 483789 1089719 := bstep (se 1 (by rfl) ⟨817289, by rfl⟩ : syracuseStep 1089719 = 1634579) B1634579
theorem B194783135 : Blo 483789 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B1227433 : Blo 483789 1227433 := bstep (se 2 (by rfl) ⟨460287, by rfl⟩ : syracuseStep 1227433 = 920575) B920575
theorem B47281643 : Blo 483789 47281643 := bstep (se 1 (by rfl) ⟨35461232, by rfl⟩ : syracuseStep 47281643 = 70922465) B70922465
theorem B1969019 : Blo 483789 1969019 := bstep (se 1 (by rfl) ⟨1476764, by rfl⟩ : syracuseStep 1969019 = 2953529) B2953529
theorem B726479 : Blo 483789 726479 := bstep (se 1 (by rfl) ⟨544859, by rfl⟩ : syracuseStep 726479 = 1089719) B1089719
theorem B519421693 : Blo 483789 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B1636577 : Blo 483789 1636577 := bstep (se 2 (by rfl) ⟨613716, by rfl⟩ : syracuseStep 1636577 = 1227433) B1227433
theorem B31521095 : Blo 483789 31521095 := bstep (se 1 (by rfl) ⟨23640821, by rfl⟩ : syracuseStep 31521095 = 47281643) B47281643
theorem B1312679 : Blo 483789 1312679 := bstep (se 1 (by rfl) ⟨984509, by rfl⟩ : syracuseStep 1312679 = 1969019) B1969019
theorem B1091051 : Blo 483789 1091051 := bstep (se 1 (by rfl) ⟨818288, by rfl⟩ : syracuseStep 1091051 = 1636577) B1636577
theorem B21014063 : Blo 483789 21014063 := bstep (se 1 (by rfl) ⟨15760547, by rfl⟩ : syracuseStep 21014063 = 31521095) B31521095
theorem B692562257 : Blo 483789 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B484319 : Blo 483789 484319 := bstep (se 1 (by rfl) ⟨363239, by rfl⟩ : syracuseStep 484319 = 726479) B726479
theorem B727367 : Blo 483789 727367 := bstep (se 1 (by rfl) ⟨545525, by rfl⟩ : syracuseStep 727367 = 1091051) B1091051
theorem B461708171 : Blo 483789 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B14009375 : Blo 483789 14009375 := bstep (se 1 (by rfl) ⟨10507031, by rfl⟩ : syracuseStep 14009375 = 21014063) B21014063
theorem B875119 : Blo 483789 875119 := bstep (se 1 (by rfl) ⟨656339, by rfl⟩ : syracuseStep 875119 = 1312679) B1312679
theorem B9339583 : Blo 483789 9339583 := bstep (se 1 (by rfl) ⟨7004687, by rfl⟩ : syracuseStep 9339583 = 14009375) B14009375
theorem B307805447 : Blo 483789 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B1166825 : Blo 483789 1166825 := bstep (se 2 (by rfl) ⟨437559, by rfl⟩ : syracuseStep 1166825 = 875119) B875119
theorem B484911 : Blo 483789 484911 := bstep (se 1 (by rfl) ⟨363683, by rfl⟩ : syracuseStep 484911 = 727367) B727367
theorem B12452777 : Blo 483789 12452777 := bstep (se 2 (by rfl) ⟨4669791, by rfl⟩ : syracuseStep 12452777 = 9339583) B9339583
theorem B205203631 : Blo 483789 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B3111533 : Blo 483789 3111533 := bstep (se 3 (by rfl) ⟨583412, by rfl⟩ : syracuseStep 3111533 = 1166825) B1166825
theorem B2074355 : Blo 483789 2074355 := bstep (se 1 (by rfl) ⟨1555766, by rfl⟩ : syracuseStep 2074355 = 3111533) B3111533
theorem B8301851 : Blo 483789 8301851 := bstep (se 1 (by rfl) ⟨6226388, by rfl⟩ : syracuseStep 8301851 = 12452777) B12452777
theorem B273604841 : Blo 483789 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B1382903 : Blo 483789 1382903 := bstep (se 1 (by rfl) ⟨1037177, by rfl⟩ : syracuseStep 1382903 = 2074355) B2074355
theorem B182403227 : Blo 483789 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B5534567 : Blo 483789 5534567 := bstep (se 1 (by rfl) ⟨4150925, by rfl⟩ : syracuseStep 5534567 = 8301851) B8301851
theorem B121602151 : Blo 483789 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B921935 : Blo 483789 921935 := bstep (se 1 (by rfl) ⟨691451, by rfl⟩ : syracuseStep 921935 = 1382903) B1382903
theorem B3689711 : Blo 483789 3689711 := bstep (se 1 (by rfl) ⟨2767283, by rfl⟩ : syracuseStep 3689711 = 5534567) B5534567
theorem B648544805 : Blo 483789 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B2459807 : Blo 483789 2459807 := bstep (se 1 (by rfl) ⟨1844855, by rfl⟩ : syracuseStep 2459807 = 3689711) B3689711
theorem B614623 : Blo 483789 614623 := bstep (se 1 (by rfl) ⟨460967, by rfl⟩ : syracuseStep 614623 = 921935) B921935
theorem B819497 : Blo 483789 819497 := bstep (se 2 (by rfl) ⟨307311, by rfl⟩ : syracuseStep 819497 = 614623) B614623
theorem B1639871 : Blo 483789 1639871 := bstep (se 1 (by rfl) ⟨1229903, by rfl⟩ : syracuseStep 1639871 = 2459807) B2459807
theorem B432363203 : Blo 483789 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B1093247 : Blo 483789 1093247 := bstep (se 1 (by rfl) ⟨819935, by rfl⟩ : syracuseStep 1093247 = 1639871) B1639871
theorem B288242135 : Blo 483789 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B546331 : Blo 483789 546331 := bstep (se 1 (by rfl) ⟨409748, by rfl⟩ : syracuseStep 546331 = 819497) B819497
theorem B728441 : Blo 483789 728441 := bstep (se 2 (by rfl) ⟨273165, by rfl⟩ : syracuseStep 728441 = 546331) B546331
theorem B728831 : Blo 483789 728831 := bstep (se 1 (by rfl) ⟨546623, by rfl⟩ : syracuseStep 728831 = 1093247) B1093247
theorem B192161423 : Blo 483789 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B128107615 : Blo 483789 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B485627 : Blo 483789 485627 := bstep (se 1 (by rfl) ⟨364220, by rfl⟩ : syracuseStep 485627 = 728441) B728441
theorem B485887 : Blo 483789 485887 := bstep (se 1 (by rfl) ⟨364415, by rfl⟩ : syracuseStep 485887 = 728831) B728831
theorem B170810153 : Blo 483789 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B113873435 : Blo 483789 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B75915623 : Blo 483789 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B50610415 : Blo 483789 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B67480553 : Blo 483789 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B44987035 : Blo 483789 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B59982713 : Blo 483789 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B39988475 : Blo 483789 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B26658983 : Blo 483789 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B71090621 : Blo 483789 71090621 := bstep (se 3 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 71090621 = 26658983) B26658983
theorem B47393747 : Blo 483789 47393747 := bstep (se 1 (by rfl) ⟨35545310, by rfl⟩ : syracuseStep 47393747 = 71090621) B71090621
theorem B31595831 : Blo 483789 31595831 := bstep (se 1 (by rfl) ⟨23696873, by rfl⟩ : syracuseStep 31595831 = 47393747) B47393747
theorem B21063887 : Blo 483789 21063887 := bstep (se 1 (by rfl) ⟨15797915, by rfl⟩ : syracuseStep 21063887 = 31595831) B31595831
theorem B14042591 : Blo 483789 14042591 := bstep (se 1 (by rfl) ⟨10531943, by rfl⟩ : syracuseStep 14042591 = 21063887) B21063887
theorem B9361727 : Blo 483789 9361727 := bstep (se 1 (by rfl) ⟨7021295, by rfl⟩ : syracuseStep 9361727 = 14042591) B14042591
theorem B6241151 : Blo 483789 6241151 := bstep (se 1 (by rfl) ⟨4680863, by rfl⟩ : syracuseStep 6241151 = 9361727) B9361727
theorem B4160767 : Blo 483789 4160767 := bstep (se 1 (by rfl) ⟨3120575, by rfl⟩ : syracuseStep 4160767 = 6241151) B6241151
theorem B5547689 : Blo 483789 5547689 := bstep (se 2 (by rfl) ⟨2080383, by rfl⟩ : syracuseStep 5547689 = 4160767) B4160767
theorem B3698459 : Blo 483789 3698459 := bstep (se 1 (by rfl) ⟨2773844, by rfl⟩ : syracuseStep 3698459 = 5547689) B5547689
theorem B2465639 : Blo 483789 2465639 := bstep (se 1 (by rfl) ⟨1849229, by rfl⟩ : syracuseStep 2465639 = 3698459) B3698459
theorem B1643759 : Blo 483789 1643759 := bstep (se 1 (by rfl) ⟨1232819, by rfl⟩ : syracuseStep 1643759 = 2465639) B2465639
theorem B1095839 : Blo 483789 1095839 := bstep (se 1 (by rfl) ⟨821879, by rfl⟩ : syracuseStep 1095839 = 1643759) B1643759
theorem B730559 : Blo 483789 730559 := bstep (se 1 (by rfl) ⟨547919, by rfl⟩ : syracuseStep 730559 = 1095839) B1095839
theorem B487039 : Blo 483789 487039 := bstep (se 1 (by rfl) ⟨365279, by rfl⟩ : syracuseStep 487039 = 730559) B730559

theorem C0 (j : ℕ) (h1 : 120947 ≤ j) (h2 : j ≤ 121646) : Blo 483789 (4 * j + 3) := by
  interval_cases j
  · exact B483791
  · exact B483795
  · exact B483799
  · exact B483803
  · exact B483807
  · exact B483811
  · exact B483815
  · exact B483819
  · exact B483823
  · exact B483827
  · exact B483831
  · exact B483835
  · exact B483839
  · exact B483843
  · exact B483847
  · exact B483851
  · exact B483855
  · exact B483859
  · exact B483863
  · exact B483867
  · exact B483871
  · exact B483875
  · exact B483879
  · exact B483883
  · exact B483887
  · exact B483891
  · exact B483895
  · exact B483899
  · exact B483903
  · exact B483907
  · exact B483911
  · exact B483915
  · exact B483919
  · exact B483923
  · exact B483927
  · exact B483931
  · exact B483935
  · exact B483939
  · exact B483943
  · exact B483947
  · exact B483951
  · exact B483955
  · exact B483959
  · exact B483963
  · exact B483967
  · exact B483971
  · exact B483975
  · exact B483979
  · exact B483983
  · exact B483987
  · exact B483991
  · exact B483995
  · exact B483999
  · exact B484003
  · exact B484007
  · exact B484011
  · exact B484015
  · exact B484019
  · exact B484023
  · exact B484027
  · exact B484031
  · exact B484035
  · exact B484039
  · exact B484043
  · exact B484047
  · exact B484051
  · exact B484055
  · exact B484059
  · exact B484063
  · exact B484067
  · exact B484071
  · exact B484075
  · exact B484079
  · exact B484083
  · exact B484087
  · exact B484091
  · exact B484095
  · exact B484099
  · exact B484103
  · exact B484107
  · exact B484111
  · exact B484115
  · exact B484119
  · exact B484123
  · exact B484127
  · exact B484131
  · exact B484135
  · exact B484139
  · exact B484143
  · exact B484147
  · exact B484151
  · exact B484155
  · exact B484159
  · exact B484163
  · exact B484167
  · exact B484171
  · exact B484175
  · exact B484179
  · exact B484183
  · exact B484187
  · exact B484191
  · exact B484195
  · exact B484199
  · exact B484203
  · exact B484207
  · exact B484211
  · exact B484215
  · exact B484219
  · exact B484223
  · exact B484227
  · exact B484231
  · exact B484235
  · exact B484239
  · exact B484243
  · exact B484247
  · exact B484251
  · exact B484255
  · exact B484259
  · exact B484263
  · exact B484267
  · exact B484271
  · exact B484275
  · exact B484279
  · exact B484283
  · exact B484287
  · exact B484291
  · exact B484295
  · exact B484299
  · exact B484303
  · exact B484307
  · exact B484311
  · exact B484315
  · exact B484319
  · exact B484323
  · exact B484327
  · exact B484331
  · exact B484335
  · exact B484339
  · exact B484343
  · exact B484347
  · exact B484351
  · exact B484355
  · exact B484359
  · exact B484363
  · exact B484367
  · exact B484371
  · exact B484375
  · exact B484379
  · exact B484383
  · exact B484387
  · exact B484391
  · exact B484395
  · exact B484399
  · exact B484403
  · exact B484407
  · exact B484411
  · exact B484415
  · exact B484419
  · exact B484423
  · exact B484427
  · exact B484431
  · exact B484435
  · exact B484439
  · exact B484443
  · exact B484447
  · exact B484451
  · exact B484455
  · exact B484459
  · exact B484463
  · exact B484467
  · exact B484471
  · exact B484475
  · exact B484479
  · exact B484483
  · exact B484487
  · exact B484491
  · exact B484495
  · exact B484499
  · exact B484503
  · exact B484507
  · exact B484511
  · exact B484515
  · exact B484519
  · exact B484523
  · exact B484527
  · exact B484531
  · exact B484535
  · exact B484539
  · exact B484543
  · exact B484547
  · exact B484551
  · exact B484555
  · exact B484559
  · exact B484563
  · exact B484567
  · exact B484571
  · exact B484575
  · exact B484579
  · exact B484583
  · exact B484587
  · exact B484591
  · exact B484595
  · exact B484599
  · exact B484603
  · exact B484607
  · exact B484611
  · exact B484615
  · exact B484619
  · exact B484623
  · exact B484627
  · exact B484631
  · exact B484635
  · exact B484639
  · exact B484643
  · exact B484647
  · exact B484651
  · exact B484655
  · exact B484659
  · exact B484663
  · exact B484667
  · exact B484671
  · exact B484675
  · exact B484679
  · exact B484683
  · exact B484687
  · exact B484691
  · exact B484695
  · exact B484699
  · exact B484703
  · exact B484707
  · exact B484711
  · exact B484715
  · exact B484719
  · exact B484723
  · exact B484727
  · exact B484731
  · exact B484735
  · exact B484739
  · exact B484743
  · exact B484747
  · exact B484751
  · exact B484755
  · exact B484759
  · exact B484763
  · exact B484767
  · exact B484771
  · exact B484775
  · exact B484779
  · exact B484783
  · exact B484787
  · exact B484791
  · exact B484795
  · exact B484799
  · exact B484803
  · exact B484807
  · exact B484811
  · exact B484815
  · exact B484819
  · exact B484823
  · exact B484827
  · exact B484831
  · exact B484835
  · exact B484839
  · exact B484843
  · exact B484847
  · exact B484851
  · exact B484855
  · exact B484859
  · exact B484863
  · exact B484867
  · exact B484871
  · exact B484875
  · exact B484879
  · exact B484883
  · exact B484887
  · exact B484891
  · exact B484895
  · exact B484899
  · exact B484903
  · exact B484907
  · exact B484911
  · exact B484915
  · exact B484919
  · exact B484923
  · exact B484927
  · exact B484931
  · exact B484935
  · exact B484939
  · exact B484943
  · exact B484947
  · exact B484951
  · exact B484955
  · exact B484959
  · exact B484963
  · exact B484967
  · exact B484971
  · exact B484975
  · exact B484979
  · exact B484983
  · exact B484987
  · exact B484991
  · exact B484995
  · exact B484999
  · exact B485003
  · exact B485007
  · exact B485011
  · exact B485015
  · exact B485019
  · exact B485023
  · exact B485027
  · exact B485031
  · exact B485035
  · exact B485039
  · exact B485043
  · exact B485047
  · exact B485051
  · exact B485055
  · exact B485059
  · exact B485063
  · exact B485067
  · exact B485071
  · exact B485075
  · exact B485079
  · exact B485083
  · exact B485087
  · exact B485091
  · exact B485095
  · exact B485099
  · exact B485103
  · exact B485107
  · exact B485111
  · exact B485115
  · exact B485119
  · exact B485123
  · exact B485127
  · exact B485131
  · exact B485135
  · exact B485139
  · exact B485143
  · exact B485147
  · exact B485151
  · exact B485155
  · exact B485159
  · exact B485163
  · exact B485167
  · exact B485171
  · exact B485175
  · exact B485179
  · exact B485183
  · exact B485187
  · exact B485191
  · exact B485195
  · exact B485199
  · exact B485203
  · exact B485207
  · exact B485211
  · exact B485215
  · exact B485219
  · exact B485223
  · exact B485227
  · exact B485231
  · exact B485235
  · exact B485239
  · exact B485243
  · exact B485247
  · exact B485251
  · exact B485255
  · exact B485259
  · exact B485263
  · exact B485267
  · exact B485271
  · exact B485275
  · exact B485279
  · exact B485283
  · exact B485287
  · exact B485291
  · exact B485295
  · exact B485299
  · exact B485303
  · exact B485307
  · exact B485311
  · exact B485315
  · exact B485319
  · exact B485323
  · exact B485327
  · exact B485331
  · exact B485335
  · exact B485339
  · exact B485343
  · exact B485347
  · exact B485351
  · exact B485355
  · exact B485359
  · exact B485363
  · exact B485367
  · exact B485371
  · exact B485375
  · exact B485379
  · exact B485383
  · exact B485387
  · exact B485391
  · exact B485395
  · exact B485399
  · exact B485403
  · exact B485407
  · exact B485411
  · exact B485415
  · exact B485419
  · exact B485423
  · exact B485427
  · exact B485431
  · exact B485435
  · exact B485439
  · exact B485443
  · exact B485447
  · exact B485451
  · exact B485455
  · exact B485459
  · exact B485463
  · exact B485467
  · exact B485471
  · exact B485475
  · exact B485479
  · exact B485483
  · exact B485487
  · exact B485491
  · exact B485495
  · exact B485499
  · exact B485503
  · exact B485507
  · exact B485511
  · exact B485515
  · exact B485519
  · exact B485523
  · exact B485527
  · exact B485531
  · exact B485535
  · exact B485539
  · exact B485543
  · exact B485547
  · exact B485551
  · exact B485555
  · exact B485559
  · exact B485563
  · exact B485567
  · exact B485571
  · exact B485575
  · exact B485579
  · exact B485583
  · exact B485587
  · exact B485591
  · exact B485595
  · exact B485599
  · exact B485603
  · exact B485607
  · exact B485611
  · exact B485615
  · exact B485619
  · exact B485623
  · exact B485627
  · exact B485631
  · exact B485635
  · exact B485639
  · exact B485643
  · exact B485647
  · exact B485651
  · exact B485655
  · exact B485659
  · exact B485663
  · exact B485667
  · exact B485671
  · exact B485675
  · exact B485679
  · exact B485683
  · exact B485687
  · exact B485691
  · exact B485695
  · exact B485699
  · exact B485703
  · exact B485707
  · exact B485711
  · exact B485715
  · exact B485719
  · exact B485723
  · exact B485727
  · exact B485731
  · exact B485735
  · exact B485739
  · exact B485743
  · exact B485747
  · exact B485751
  · exact B485755
  · exact B485759
  · exact B485763
  · exact B485767
  · exact B485771
  · exact B485775
  · exact B485779
  · exact B485783
  · exact B485787
  · exact B485791
  · exact B485795
  · exact B485799
  · exact B485803
  · exact B485807
  · exact B485811
  · exact B485815
  · exact B485819
  · exact B485823
  · exact B485827
  · exact B485831
  · exact B485835
  · exact B485839
  · exact B485843
  · exact B485847
  · exact B485851
  · exact B485855
  · exact B485859
  · exact B485863
  · exact B485867
  · exact B485871
  · exact B485875
  · exact B485879
  · exact B485883
  · exact B485887
  · exact B485891
  · exact B485895
  · exact B485899
  · exact B485903
  · exact B485907
  · exact B485911
  · exact B485915
  · exact B485919
  · exact B485923
  · exact B485927
  · exact B485931
  · exact B485935
  · exact B485939
  · exact B485943
  · exact B485947
  · exact B485951
  · exact B485955
  · exact B485959
  · exact B485963
  · exact B485967
  · exact B485971
  · exact B485975
  · exact B485979
  · exact B485983
  · exact B485987
  · exact B485991
  · exact B485995
  · exact B485999
  · exact B486003
  · exact B486007
  · exact B486011
  · exact B486015
  · exact B486019
  · exact B486023
  · exact B486027
  · exact B486031
  · exact B486035
  · exact B486039
  · exact B486043
  · exact B486047
  · exact B486051
  · exact B486055
  · exact B486059
  · exact B486063
  · exact B486067
  · exact B486071
  · exact B486075
  · exact B486079
  · exact B486083
  · exact B486087
  · exact B486091
  · exact B486095
  · exact B486099
  · exact B486103
  · exact B486107
  · exact B486111
  · exact B486115
  · exact B486119
  · exact B486123
  · exact B486127
  · exact B486131
  · exact B486135
  · exact B486139
  · exact B486143
  · exact B486147
  · exact B486151
  · exact B486155
  · exact B486159
  · exact B486163
  · exact B486167
  · exact B486171
  · exact B486175
  · exact B486179
  · exact B486183
  · exact B486187
  · exact B486191
  · exact B486195
  · exact B486199
  · exact B486203
  · exact B486207
  · exact B486211
  · exact B486215
  · exact B486219
  · exact B486223
  · exact B486227
  · exact B486231
  · exact B486235
  · exact B486239
  · exact B486243
  · exact B486247
  · exact B486251
  · exact B486255
  · exact B486259
  · exact B486263
  · exact B486267
  · exact B486271
  · exact B486275
  · exact B486279
  · exact B486283
  · exact B486287
  · exact B486291
  · exact B486295
  · exact B486299
  · exact B486303
  · exact B486307
  · exact B486311
  · exact B486315
  · exact B486319
  · exact B486323
  · exact B486327
  · exact B486331
  · exact B486335
  · exact B486339
  · exact B486343
  · exact B486347
  · exact B486351
  · exact B486355
  · exact B486359
  · exact B486363
  · exact B486367
  · exact B486371
  · exact B486375
  · exact B486379
  · exact B486383
  · exact B486387
  · exact B486391
  · exact B486395
  · exact B486399
  · exact B486403
  · exact B486407
  · exact B486411
  · exact B486415
  · exact B486419
  · exact B486423
  · exact B486427
  · exact B486431
  · exact B486435
  · exact B486439
  · exact B486443
  · exact B486447
  · exact B486451
  · exact B486455
  · exact B486459
  · exact B486463
  · exact B486467
  · exact B486471
  · exact B486475
  · exact B486479
  · exact B486483
  · exact B486487
  · exact B486491
  · exact B486495
  · exact B486499
  · exact B486503
  · exact B486507
  · exact B486511
  · exact B486515
  · exact B486519
  · exact B486523
  · exact B486527
  · exact B486531
  · exact B486535
  · exact B486539
  · exact B486543
  · exact B486547
  · exact B486551
  · exact B486555
  · exact B486559
  · exact B486563
  · exact B486567
  · exact B486571
  · exact B486575
  · exact B486579
  · exact B486583
  · exact B486587

theorem C1 (j : ℕ) (h1 : 121647 ≤ j) (h2 : j ≤ 121946) : Blo 483789 (4 * j + 3) := by
  interval_cases j
  · exact B486591
  · exact B486595
  · exact B486599
  · exact B486603
  · exact B486607
  · exact B486611
  · exact B486615
  · exact B486619
  · exact B486623
  · exact B486627
  · exact B486631
  · exact B486635
  · exact B486639
  · exact B486643
  · exact B486647
  · exact B486651
  · exact B486655
  · exact B486659
  · exact B486663
  · exact B486667
  · exact B486671
  · exact B486675
  · exact B486679
  · exact B486683
  · exact B486687
  · exact B486691
  · exact B486695
  · exact B486699
  · exact B486703
  · exact B486707
  · exact B486711
  · exact B486715
  · exact B486719
  · exact B486723
  · exact B486727
  · exact B486731
  · exact B486735
  · exact B486739
  · exact B486743
  · exact B486747
  · exact B486751
  · exact B486755
  · exact B486759
  · exact B486763
  · exact B486767
  · exact B486771
  · exact B486775
  · exact B486779
  · exact B486783
  · exact B486787
  · exact B486791
  · exact B486795
  · exact B486799
  · exact B486803
  · exact B486807
  · exact B486811
  · exact B486815
  · exact B486819
  · exact B486823
  · exact B486827
  · exact B486831
  · exact B486835
  · exact B486839
  · exact B486843
  · exact B486847
  · exact B486851
  · exact B486855
  · exact B486859
  · exact B486863
  · exact B486867
  · exact B486871
  · exact B486875
  · exact B486879
  · exact B486883
  · exact B486887
  · exact B486891
  · exact B486895
  · exact B486899
  · exact B486903
  · exact B486907
  · exact B486911
  · exact B486915
  · exact B486919
  · exact B486923
  · exact B486927
  · exact B486931
  · exact B486935
  · exact B486939
  · exact B486943
  · exact B486947
  · exact B486951
  · exact B486955
  · exact B486959
  · exact B486963
  · exact B486967
  · exact B486971
  · exact B486975
  · exact B486979
  · exact B486983
  · exact B486987
  · exact B486991
  · exact B486995
  · exact B486999
  · exact B487003
  · exact B487007
  · exact B487011
  · exact B487015
  · exact B487019
  · exact B487023
  · exact B487027
  · exact B487031
  · exact B487035
  · exact B487039
  · exact B487043
  · exact B487047
  · exact B487051
  · exact B487055
  · exact B487059
  · exact B487063
  · exact B487067
  · exact B487071
  · exact B487075
  · exact B487079
  · exact B487083
  · exact B487087
  · exact B487091
  · exact B487095
  · exact B487099
  · exact B487103
  · exact B487107
  · exact B487111
  · exact B487115
  · exact B487119
  · exact B487123
  · exact B487127
  · exact B487131
  · exact B487135
  · exact B487139
  · exact B487143
  · exact B487147
  · exact B487151
  · exact B487155
  · exact B487159
  · exact B487163
  · exact B487167
  · exact B487171
  · exact B487175
  · exact B487179
  · exact B487183
  · exact B487187
  · exact B487191
  · exact B487195
  · exact B487199
  · exact B487203
  · exact B487207
  · exact B487211
  · exact B487215
  · exact B487219
  · exact B487223
  · exact B487227
  · exact B487231
  · exact B487235
  · exact B487239
  · exact B487243
  · exact B487247
  · exact B487251
  · exact B487255
  · exact B487259
  · exact B487263
  · exact B487267
  · exact B487271
  · exact B487275
  · exact B487279
  · exact B487283
  · exact B487287
  · exact B487291
  · exact B487295
  · exact B487299
  · exact B487303
  · exact B487307
  · exact B487311
  · exact B487315
  · exact B487319
  · exact B487323
  · exact B487327
  · exact B487331
  · exact B487335
  · exact B487339
  · exact B487343
  · exact B487347
  · exact B487351
  · exact B487355
  · exact B487359
  · exact B487363
  · exact B487367
  · exact B487371
  · exact B487375
  · exact B487379
  · exact B487383
  · exact B487387
  · exact B487391
  · exact B487395
  · exact B487399
  · exact B487403
  · exact B487407
  · exact B487411
  · exact B487415
  · exact B487419
  · exact B487423
  · exact B487427
  · exact B487431
  · exact B487435
  · exact B487439
  · exact B487443
  · exact B487447
  · exact B487451
  · exact B487455
  · exact B487459
  · exact B487463
  · exact B487467
  · exact B487471
  · exact B487475
  · exact B487479
  · exact B487483
  · exact B487487
  · exact B487491
  · exact B487495
  · exact B487499
  · exact B487503
  · exact B487507
  · exact B487511
  · exact B487515
  · exact B487519
  · exact B487523
  · exact B487527
  · exact B487531
  · exact B487535
  · exact B487539
  · exact B487543
  · exact B487547
  · exact B487551
  · exact B487555
  · exact B487559
  · exact B487563
  · exact B487567
  · exact B487571
  · exact B487575
  · exact B487579
  · exact B487583
  · exact B487587
  · exact B487591
  · exact B487595
  · exact B487599
  · exact B487603
  · exact B487607
  · exact B487611
  · exact B487615
  · exact B487619
  · exact B487623
  · exact B487627
  · exact B487631
  · exact B487635
  · exact B487639
  · exact B487643
  · exact B487647
  · exact B487651
  · exact B487655
  · exact B487659
  · exact B487663
  · exact B487667
  · exact B487671
  · exact B487675
  · exact B487679
  · exact B487683
  · exact B487687
  · exact B487691
  · exact B487695
  · exact B487699
  · exact B487703
  · exact B487707
  · exact B487711
  · exact B487715
  · exact B487719
  · exact B487723
  · exact B487727
  · exact B487731
  · exact B487735
  · exact B487739
  · exact B487743
  · exact B487747
  · exact B487751
  · exact B487755
  · exact B487759
  · exact B487763
  · exact B487767
  · exact B487771
  · exact B487775
  · exact B487779
  · exact B487783
  · exact B487787

theorem solution (m : ℕ) (hlo : 483789 ≤ m) (hhi : m ≤ 487789) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 120947 ≤ j := by omega
    have hj2 : j ≤ 121946 := by omega
    have hb : Blo 483789 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 121647 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
