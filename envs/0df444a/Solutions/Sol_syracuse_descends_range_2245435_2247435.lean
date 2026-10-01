-- Prove2me | solution 1 for syracuse_descends_range_2245435_2247435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:02.647083+00:00
-- url     : https://prove2.me/submissions/c90ee7de-570d-452c-bd07-c6270512ef90

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

theorem B3789173 : Blo 2245435 3789173 := bbase (se 5 (by rfl) ⟨177617, by rfl⟩ : syracuseStep 3789173 = 355235) (by norm_num)
theorem B2526115 : Blo 2245435 2526115 := bstep (se 1 (by rfl) ⟨1894586, by rfl⟩ : syracuseStep 2526115 = 3789173) B3789173
theorem B3368153 : Blo 2245435 3368153 := bstep (se 2 (by rfl) ⟨1263057, by rfl⟩ : syracuseStep 3368153 = 2526115) B2526115
theorem B2245435 : Blo 2245435 2245435 := bstep (se 1 (by rfl) ⟨1684076, by rfl⟩ : syracuseStep 2245435 = 3368153) B3368153
theorem B4046357 : Blo 2245435 4046357 := bbase (se 6 (by rfl) ⟨94836, by rfl⟩ : syracuseStep 4046357 = 189673) (by norm_num)
theorem B2697571 : Blo 2245435 2697571 := bstep (se 1 (by rfl) ⟨2023178, by rfl⟩ : syracuseStep 2697571 = 4046357) B4046357
theorem B3596761 : Blo 2245435 3596761 := bstep (se 2 (by rfl) ⟨1348785, by rfl⟩ : syracuseStep 3596761 = 2697571) B2697571
theorem B4795681 : Blo 2245435 4795681 := bstep (se 2 (by rfl) ⟨1798380, by rfl⟩ : syracuseStep 4795681 = 3596761) B3596761
theorem B6394241 : Blo 2245435 6394241 := bstep (se 2 (by rfl) ⟨2397840, by rfl⟩ : syracuseStep 6394241 = 4795681) B4795681
theorem B17051309 : Blo 2245435 17051309 := bstep (se 3 (by rfl) ⟨3197120, by rfl⟩ : syracuseStep 17051309 = 6394241) B6394241
theorem B11367539 : Blo 2245435 11367539 := bstep (se 1 (by rfl) ⟨8525654, by rfl⟩ : syracuseStep 11367539 = 17051309) B17051309
theorem B7578359 : Blo 2245435 7578359 := bstep (se 1 (by rfl) ⟨5683769, by rfl⟩ : syracuseStep 7578359 = 11367539) B11367539
theorem B5052239 : Blo 2245435 5052239 := bstep (se 1 (by rfl) ⟨3789179, by rfl⟩ : syracuseStep 5052239 = 7578359) B7578359
theorem B3368159 : Blo 2245435 3368159 := bstep (se 1 (by rfl) ⟨2526119, by rfl⟩ : syracuseStep 3368159 = 5052239) B5052239
theorem B2245439 : Blo 2245435 2245439 := bstep (se 1 (by rfl) ⟨1684079, by rfl⟩ : syracuseStep 2245439 = 3368159) B3368159
theorem B3368165 : Blo 2245435 3368165 := bbase (se 4 (by rfl) ⟨315765, by rfl⟩ : syracuseStep 3368165 = 631531) (by norm_num)
theorem B2245443 : Blo 2245435 2245443 := bstep (se 1 (by rfl) ⟨1684082, by rfl⟩ : syracuseStep 2245443 = 3368165) B3368165
theorem B2697581 : Blo 2245435 2697581 := bbase (se 3 (by rfl) ⟨505796, by rfl⟩ : syracuseStep 2697581 = 1011593) (by norm_num)
theorem B7193549 : Blo 2245435 7193549 := bstep (se 3 (by rfl) ⟨1348790, by rfl⟩ : syracuseStep 7193549 = 2697581) B2697581
theorem B4795699 : Blo 2245435 4795699 := bstep (se 1 (by rfl) ⟨3596774, by rfl⟩ : syracuseStep 4795699 = 7193549) B7193549
theorem B6394265 : Blo 2245435 6394265 := bstep (se 2 (by rfl) ⟨2397849, by rfl⟩ : syracuseStep 6394265 = 4795699) B4795699
theorem B4262843 : Blo 2245435 4262843 := bstep (se 1 (by rfl) ⟨3197132, by rfl⟩ : syracuseStep 4262843 = 6394265) B6394265
theorem B2841895 : Blo 2245435 2841895 := bstep (se 1 (by rfl) ⟨2131421, by rfl⟩ : syracuseStep 2841895 = 4262843) B4262843
theorem B3789193 : Blo 2245435 3789193 := bstep (se 2 (by rfl) ⟨1420947, by rfl⟩ : syracuseStep 3789193 = 2841895) B2841895
theorem B5052257 : Blo 2245435 5052257 := bstep (se 2 (by rfl) ⟨1894596, by rfl⟩ : syracuseStep 5052257 = 3789193) B3789193
theorem B3368171 : Blo 2245435 3368171 := bstep (se 1 (by rfl) ⟨2526128, by rfl⟩ : syracuseStep 3368171 = 5052257) B5052257
theorem B2245447 : Blo 2245435 2245447 := bstep (se 1 (by rfl) ⟨1684085, by rfl⟩ : syracuseStep 2245447 = 3368171) B3368171
theorem B2526133 : Blo 2245435 2526133 := bbase (se 5 (by rfl) ⟨118412, by rfl⟩ : syracuseStep 2526133 = 236825) (by norm_num)
theorem B3368177 : Blo 2245435 3368177 := bstep (se 2 (by rfl) ⟨1263066, by rfl⟩ : syracuseStep 3368177 = 2526133) B2526133
theorem B2245451 : Blo 2245435 2245451 := bstep (se 1 (by rfl) ⟨1684088, by rfl⟩ : syracuseStep 2245451 = 3368177) B3368177
theorem B2841905 : Blo 2245435 2841905 := bbase (se 2 (by rfl) ⟨1065714, by rfl⟩ : syracuseStep 2841905 = 2131429) (by norm_num)
theorem B7578413 : Blo 2245435 7578413 := bstep (se 3 (by rfl) ⟨1420952, by rfl⟩ : syracuseStep 7578413 = 2841905) B2841905
theorem B5052275 : Blo 2245435 5052275 := bstep (se 1 (by rfl) ⟨3789206, by rfl⟩ : syracuseStep 5052275 = 7578413) B7578413
theorem B3368183 : Blo 2245435 3368183 := bstep (se 1 (by rfl) ⟨2526137, by rfl⟩ : syracuseStep 3368183 = 5052275) B5052275
theorem B2245455 : Blo 2245435 2245455 := bstep (se 1 (by rfl) ⟨1684091, by rfl⟩ : syracuseStep 2245455 = 3368183) B3368183
theorem B3368189 : Blo 2245435 3368189 := bbase (se 3 (by rfl) ⟨631535, by rfl⟩ : syracuseStep 3368189 = 1263071) (by norm_num)
theorem B2245459 : Blo 2245435 2245459 := bstep (se 1 (by rfl) ⟨1684094, by rfl⟩ : syracuseStep 2245459 = 3368189) B3368189
theorem B5052293 : Blo 2245435 5052293 := bbase (se 4 (by rfl) ⟨473652, by rfl⟩ : syracuseStep 5052293 = 947305) (by norm_num)
theorem B3368195 : Blo 2245435 3368195 := bstep (se 1 (by rfl) ⟨2526146, by rfl⟩ : syracuseStep 3368195 = 5052293) B5052293
theorem B2245463 : Blo 2245435 2245463 := bstep (se 1 (by rfl) ⟨1684097, by rfl⟩ : syracuseStep 2245463 = 3368195) B3368195
theorem B2276105 : Blo 2245435 2276105 := bbase (se 2 (by rfl) ⟨853539, by rfl⟩ : syracuseStep 2276105 = 1707079) (by norm_num)
theorem B6069613 : Blo 2245435 6069613 := bstep (se 3 (by rfl) ⟨1138052, by rfl⟩ : syracuseStep 6069613 = 2276105) B2276105
theorem B8092817 : Blo 2245435 8092817 := bstep (se 2 (by rfl) ⟨3034806, by rfl⟩ : syracuseStep 8092817 = 6069613) B6069613
theorem B5395211 : Blo 2245435 5395211 := bstep (se 1 (by rfl) ⟨4046408, by rfl⟩ : syracuseStep 5395211 = 8092817) B8092817
theorem B3596807 : Blo 2245435 3596807 := bstep (se 1 (by rfl) ⟨2697605, by rfl⟩ : syracuseStep 3596807 = 5395211) B5395211
theorem B2397871 : Blo 2245435 2397871 := bstep (se 1 (by rfl) ⟨1798403, by rfl⟩ : syracuseStep 2397871 = 3596807) B3596807
theorem B3197161 : Blo 2245435 3197161 := bstep (se 2 (by rfl) ⟨1198935, by rfl⟩ : syracuseStep 3197161 = 2397871) B2397871
theorem B4262881 : Blo 2245435 4262881 := bstep (se 2 (by rfl) ⟨1598580, by rfl⟩ : syracuseStep 4262881 = 3197161) B3197161
theorem B5683841 : Blo 2245435 5683841 := bstep (se 2 (by rfl) ⟨2131440, by rfl⟩ : syracuseStep 5683841 = 4262881) B4262881
theorem B3789227 : Blo 2245435 3789227 := bstep (se 1 (by rfl) ⟨2841920, by rfl⟩ : syracuseStep 3789227 = 5683841) B5683841
theorem B2526151 : Blo 2245435 2526151 := bstep (se 1 (by rfl) ⟨1894613, by rfl⟩ : syracuseStep 2526151 = 3789227) B3789227
theorem B3368201 : Blo 2245435 3368201 := bstep (se 2 (by rfl) ⟨1263075, by rfl⟩ : syracuseStep 3368201 = 2526151) B2526151
theorem B2245467 : Blo 2245435 2245467 := bstep (se 1 (by rfl) ⟨1684100, by rfl⟩ : syracuseStep 2245467 = 3368201) B3368201
theorem B11367701 : Blo 2245435 11367701 := bbase (se 6 (by rfl) ⟨266430, by rfl⟩ : syracuseStep 11367701 = 532861) (by norm_num)
theorem B7578467 : Blo 2245435 7578467 := bstep (se 1 (by rfl) ⟨5683850, by rfl⟩ : syracuseStep 7578467 = 11367701) B11367701
theorem B5052311 : Blo 2245435 5052311 := bstep (se 1 (by rfl) ⟨3789233, by rfl⟩ : syracuseStep 5052311 = 7578467) B7578467
theorem B3368207 : Blo 2245435 3368207 := bstep (se 1 (by rfl) ⟨2526155, by rfl⟩ : syracuseStep 3368207 = 5052311) B5052311
theorem B2245471 : Blo 2245435 2245471 := bstep (se 1 (by rfl) ⟨1684103, by rfl⟩ : syracuseStep 2245471 = 3368207) B3368207
theorem B3368213 : Blo 2245435 3368213 := bbase (se 6 (by rfl) ⟨78942, by rfl⟩ : syracuseStep 3368213 = 157885) (by norm_num)
theorem B2245475 : Blo 2245435 2245475 := bstep (se 1 (by rfl) ⟨1684106, by rfl⟩ : syracuseStep 2245475 = 3368213) B3368213
theorem B48557141 : Blo 2245435 48557141 := bbase (se 8 (by rfl) ⟨284514, by rfl⟩ : syracuseStep 48557141 = 569029) (by norm_num)
theorem B32371427 : Blo 2245435 32371427 := bstep (se 1 (by rfl) ⟨24278570, by rfl⟩ : syracuseStep 32371427 = 48557141) B48557141
theorem B21580951 : Blo 2245435 21580951 := bstep (se 1 (by rfl) ⟨16185713, by rfl⟩ : syracuseStep 21580951 = 32371427) B32371427
theorem B28774601 : Blo 2245435 28774601 := bstep (se 2 (by rfl) ⟨10790475, by rfl⟩ : syracuseStep 28774601 = 21580951) B21580951
theorem B19183067 : Blo 2245435 19183067 := bstep (se 1 (by rfl) ⟨14387300, by rfl⟩ : syracuseStep 19183067 = 28774601) B28774601
theorem B12788711 : Blo 2245435 12788711 := bstep (se 1 (by rfl) ⟨9591533, by rfl⟩ : syracuseStep 12788711 = 19183067) B19183067
theorem B8525807 : Blo 2245435 8525807 := bstep (se 1 (by rfl) ⟨6394355, by rfl⟩ : syracuseStep 8525807 = 12788711) B12788711
theorem B5683871 : Blo 2245435 5683871 := bstep (se 1 (by rfl) ⟨4262903, by rfl⟩ : syracuseStep 5683871 = 8525807) B8525807
theorem B3789247 : Blo 2245435 3789247 := bstep (se 1 (by rfl) ⟨2841935, by rfl⟩ : syracuseStep 3789247 = 5683871) B5683871
theorem B5052329 : Blo 2245435 5052329 := bstep (se 2 (by rfl) ⟨1894623, by rfl⟩ : syracuseStep 5052329 = 3789247) B3789247
theorem B3368219 : Blo 2245435 3368219 := bstep (se 1 (by rfl) ⟨2526164, by rfl⟩ : syracuseStep 3368219 = 5052329) B5052329
theorem B2245479 : Blo 2245435 2245479 := bstep (se 1 (by rfl) ⟨1684109, by rfl⟩ : syracuseStep 2245479 = 3368219) B3368219
theorem B2526169 : Blo 2245435 2526169 := bbase (se 2 (by rfl) ⟨947313, by rfl⟩ : syracuseStep 2526169 = 1894627) (by norm_num)
theorem B3368225 : Blo 2245435 3368225 := bstep (se 2 (by rfl) ⟨1263084, by rfl⟩ : syracuseStep 3368225 = 2526169) B2526169
theorem B2245483 : Blo 2245435 2245483 := bstep (se 1 (by rfl) ⟨1684112, by rfl⟩ : syracuseStep 2245483 = 3368225) B3368225
theorem B3197189 : Blo 2245435 3197189 := bbase (se 4 (by rfl) ⟨299736, by rfl⟩ : syracuseStep 3197189 = 599473) (by norm_num)
theorem B8525837 : Blo 2245435 8525837 := bstep (se 3 (by rfl) ⟨1598594, by rfl⟩ : syracuseStep 8525837 = 3197189) B3197189
theorem B5683891 : Blo 2245435 5683891 := bstep (se 1 (by rfl) ⟨4262918, by rfl⟩ : syracuseStep 5683891 = 8525837) B8525837
theorem B7578521 : Blo 2245435 7578521 := bstep (se 2 (by rfl) ⟨2841945, by rfl⟩ : syracuseStep 7578521 = 5683891) B5683891
theorem B5052347 : Blo 2245435 5052347 := bstep (se 1 (by rfl) ⟨3789260, by rfl⟩ : syracuseStep 5052347 = 7578521) B7578521
theorem B3368231 : Blo 2245435 3368231 := bstep (se 1 (by rfl) ⟨2526173, by rfl⟩ : syracuseStep 3368231 = 5052347) B5052347
theorem B2245487 : Blo 2245435 2245487 := bstep (se 1 (by rfl) ⟨1684115, by rfl⟩ : syracuseStep 2245487 = 3368231) B3368231
theorem B3368237 : Blo 2245435 3368237 := bbase (se 3 (by rfl) ⟨631544, by rfl⟩ : syracuseStep 3368237 = 1263089) (by norm_num)
theorem B2245491 : Blo 2245435 2245491 := bstep (se 1 (by rfl) ⟨1684118, by rfl⟩ : syracuseStep 2245491 = 3368237) B3368237
theorem B5052365 : Blo 2245435 5052365 := bbase (se 3 (by rfl) ⟨947318, by rfl⟩ : syracuseStep 5052365 = 1894637) (by norm_num)
theorem B3368243 : Blo 2245435 3368243 := bstep (se 1 (by rfl) ⟨2526182, by rfl⟩ : syracuseStep 3368243 = 5052365) B5052365
theorem B2245495 : Blo 2245435 2245495 := bstep (se 1 (by rfl) ⟨1684121, by rfl⟩ : syracuseStep 2245495 = 3368243) B3368243
theorem B2841961 : Blo 2245435 2841961 := bbase (se 2 (by rfl) ⟨1065735, by rfl⟩ : syracuseStep 2841961 = 2131471) (by norm_num)
theorem B3789281 : Blo 2245435 3789281 := bstep (se 2 (by rfl) ⟨1420980, by rfl⟩ : syracuseStep 3789281 = 2841961) B2841961
theorem B2526187 : Blo 2245435 2526187 := bstep (se 1 (by rfl) ⟨1894640, by rfl⟩ : syracuseStep 2526187 = 3789281) B3789281
theorem B3368249 : Blo 2245435 3368249 := bstep (se 2 (by rfl) ⟨1263093, by rfl⟩ : syracuseStep 3368249 = 2526187) B2526187
theorem B2245499 : Blo 2245435 2245499 := bstep (se 1 (by rfl) ⟨1684124, by rfl⟩ : syracuseStep 2245499 = 3368249) B3368249
theorem B27313685 : Blo 2245435 27313685 := bbase (se 6 (by rfl) ⟨640164, by rfl⟩ : syracuseStep 27313685 = 1280329) (by norm_num)
theorem B18209123 : Blo 2245435 18209123 := bstep (se 1 (by rfl) ⟨13656842, by rfl⟩ : syracuseStep 18209123 = 27313685) B27313685
theorem B12139415 : Blo 2245435 12139415 := bstep (se 1 (by rfl) ⟨9104561, by rfl⟩ : syracuseStep 12139415 = 18209123) B18209123
theorem B8092943 : Blo 2245435 8092943 := bstep (se 1 (by rfl) ⟨6069707, by rfl⟩ : syracuseStep 8092943 = 12139415) B12139415
theorem B5395295 : Blo 2245435 5395295 := bstep (se 1 (by rfl) ⟨4046471, by rfl⟩ : syracuseStep 5395295 = 8092943) B8092943
theorem B14387453 : Blo 2245435 14387453 := bstep (se 3 (by rfl) ⟨2697647, by rfl⟩ : syracuseStep 14387453 = 5395295) B5395295
theorem B9591635 : Blo 2245435 9591635 := bstep (se 1 (by rfl) ⟨7193726, by rfl⟩ : syracuseStep 9591635 = 14387453) B14387453
theorem B25577693 : Blo 2245435 25577693 := bstep (se 3 (by rfl) ⟨4795817, by rfl⟩ : syracuseStep 25577693 = 9591635) B9591635
theorem B17051795 : Blo 2245435 17051795 := bstep (se 1 (by rfl) ⟨12788846, by rfl⟩ : syracuseStep 17051795 = 25577693) B25577693
theorem B11367863 : Blo 2245435 11367863 := bstep (se 1 (by rfl) ⟨8525897, by rfl⟩ : syracuseStep 11367863 = 17051795) B17051795
theorem B7578575 : Blo 2245435 7578575 := bstep (se 1 (by rfl) ⟨5683931, by rfl⟩ : syracuseStep 7578575 = 11367863) B11367863
theorem B5052383 : Blo 2245435 5052383 := bstep (se 1 (by rfl) ⟨3789287, by rfl⟩ : syracuseStep 5052383 = 7578575) B7578575
theorem B3368255 : Blo 2245435 3368255 := bstep (se 1 (by rfl) ⟨2526191, by rfl⟩ : syracuseStep 3368255 = 5052383) B5052383
theorem B2245503 : Blo 2245435 2245503 := bstep (se 1 (by rfl) ⟨1684127, by rfl⟩ : syracuseStep 2245503 = 3368255) B3368255
theorem B3368261 : Blo 2245435 3368261 := bbase (se 4 (by rfl) ⟨315774, by rfl⟩ : syracuseStep 3368261 = 631549) (by norm_num)
theorem B2245507 : Blo 2245435 2245507 := bstep (se 1 (by rfl) ⟨1684130, by rfl⟩ : syracuseStep 2245507 = 3368261) B3368261
theorem B3789301 : Blo 2245435 3789301 := bbase (se 5 (by rfl) ⟨177623, by rfl⟩ : syracuseStep 3789301 = 355247) (by norm_num)
theorem B5052401 : Blo 2245435 5052401 := bstep (se 2 (by rfl) ⟨1894650, by rfl⟩ : syracuseStep 5052401 = 3789301) B3789301
theorem B3368267 : Blo 2245435 3368267 := bstep (se 1 (by rfl) ⟨2526200, by rfl⟩ : syracuseStep 3368267 = 5052401) B5052401
theorem B2245511 : Blo 2245435 2245511 := bstep (se 1 (by rfl) ⟨1684133, by rfl⟩ : syracuseStep 2245511 = 3368267) B3368267
theorem B2526205 : Blo 2245435 2526205 := bbase (se 3 (by rfl) ⟨473663, by rfl⟩ : syracuseStep 2526205 = 947327) (by norm_num)
theorem B3368273 : Blo 2245435 3368273 := bstep (se 2 (by rfl) ⟨1263102, by rfl⟩ : syracuseStep 3368273 = 2526205) B2526205
theorem B2245515 : Blo 2245435 2245515 := bstep (se 1 (by rfl) ⟨1684136, by rfl⟩ : syracuseStep 2245515 = 3368273) B3368273
theorem B7578629 : Blo 2245435 7578629 := bbase (se 4 (by rfl) ⟨710496, by rfl⟩ : syracuseStep 7578629 = 1420993) (by norm_num)
theorem B5052419 : Blo 2245435 5052419 := bstep (se 1 (by rfl) ⟨3789314, by rfl⟩ : syracuseStep 5052419 = 7578629) B7578629
theorem B3368279 : Blo 2245435 3368279 := bstep (se 1 (by rfl) ⟨2526209, by rfl⟩ : syracuseStep 3368279 = 5052419) B5052419
theorem B2245519 : Blo 2245435 2245519 := bstep (se 1 (by rfl) ⟨1684139, by rfl⟩ : syracuseStep 2245519 = 3368279) B3368279
theorem B3368285 : Blo 2245435 3368285 := bbase (se 3 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 3368285 = 1263107) (by norm_num)
theorem B2245523 : Blo 2245435 2245523 := bstep (se 1 (by rfl) ⟨1684142, by rfl⟩ : syracuseStep 2245523 = 3368285) B3368285
theorem B5052437 : Blo 2245435 5052437 := bbase (se 6 (by rfl) ⟨118416, by rfl⟩ : syracuseStep 5052437 = 236833) (by norm_num)
theorem B3368291 : Blo 2245435 3368291 := bstep (se 1 (by rfl) ⟨2526218, by rfl⟩ : syracuseStep 3368291 = 5052437) B5052437
theorem B2245527 : Blo 2245435 2245527 := bstep (se 1 (by rfl) ⟨1684145, by rfl⟩ : syracuseStep 2245527 = 3368291) B3368291
theorem B8526005 : Blo 2245435 8526005 := bbase (se 5 (by rfl) ⟨399656, by rfl⟩ : syracuseStep 8526005 = 799313) (by norm_num)
theorem B5684003 : Blo 2245435 5684003 := bstep (se 1 (by rfl) ⟨4263002, by rfl⟩ : syracuseStep 5684003 = 8526005) B8526005
theorem B3789335 : Blo 2245435 3789335 := bstep (se 1 (by rfl) ⟨2842001, by rfl⟩ : syracuseStep 3789335 = 5684003) B5684003
theorem B2526223 : Blo 2245435 2526223 := bstep (se 1 (by rfl) ⟨1894667, by rfl⟩ : syracuseStep 2526223 = 3789335) B3789335
theorem B3368297 : Blo 2245435 3368297 := bstep (se 2 (by rfl) ⟨1263111, by rfl⟩ : syracuseStep 3368297 = 2526223) B2526223
theorem B2245531 : Blo 2245435 2245531 := bstep (se 1 (by rfl) ⟨1684148, by rfl⟩ : syracuseStep 2245531 = 3368297) B3368297
theorem B5395373 : Blo 2245435 5395373 := bbase (se 3 (by rfl) ⟨1011632, by rfl⟩ : syracuseStep 5395373 = 2023265) (by norm_num)
theorem B3596915 : Blo 2245435 3596915 := bstep (se 1 (by rfl) ⟨2697686, by rfl⟩ : syracuseStep 3596915 = 5395373) B5395373
theorem B2397943 : Blo 2245435 2397943 := bstep (se 1 (by rfl) ⟨1798457, by rfl⟩ : syracuseStep 2397943 = 3596915) B3596915
theorem B12789029 : Blo 2245435 12789029 := bstep (se 4 (by rfl) ⟨1198971, by rfl⟩ : syracuseStep 12789029 = 2397943) B2397943
theorem B8526019 : Blo 2245435 8526019 := bstep (se 1 (by rfl) ⟨6394514, by rfl⟩ : syracuseStep 8526019 = 12789029) B12789029
theorem B11368025 : Blo 2245435 11368025 := bstep (se 2 (by rfl) ⟨4263009, by rfl⟩ : syracuseStep 11368025 = 8526019) B8526019
theorem B7578683 : Blo 2245435 7578683 := bstep (se 1 (by rfl) ⟨5684012, by rfl⟩ : syracuseStep 7578683 = 11368025) B11368025
theorem B5052455 : Blo 2245435 5052455 := bstep (se 1 (by rfl) ⟨3789341, by rfl⟩ : syracuseStep 5052455 = 7578683) B7578683
theorem B3368303 : Blo 2245435 3368303 := bstep (se 1 (by rfl) ⟨2526227, by rfl⟩ : syracuseStep 3368303 = 5052455) B5052455
theorem B2245535 : Blo 2245435 2245535 := bstep (se 1 (by rfl) ⟨1684151, by rfl⟩ : syracuseStep 2245535 = 3368303) B3368303
theorem B3368309 : Blo 2245435 3368309 := bbase (se 5 (by rfl) ⟨157889, by rfl⟩ : syracuseStep 3368309 = 315779) (by norm_num)
theorem B2245539 : Blo 2245435 2245539 := bstep (se 1 (by rfl) ⟨1684154, by rfl⟩ : syracuseStep 2245539 = 3368309) B3368309
theorem B3197269 : Blo 2245435 3197269 := bbase (se 10 (by rfl) ⟨4683, by rfl⟩ : syracuseStep 3197269 = 9367) (by norm_num)
theorem B4263025 : Blo 2245435 4263025 := bstep (se 2 (by rfl) ⟨1598634, by rfl⟩ : syracuseStep 4263025 = 3197269) B3197269
theorem B5684033 : Blo 2245435 5684033 := bstep (se 2 (by rfl) ⟨2131512, by rfl⟩ : syracuseStep 5684033 = 4263025) B4263025
theorem B3789355 : Blo 2245435 3789355 := bstep (se 1 (by rfl) ⟨2842016, by rfl⟩ : syracuseStep 3789355 = 5684033) B5684033
theorem B5052473 : Blo 2245435 5052473 := bstep (se 2 (by rfl) ⟨1894677, by rfl⟩ : syracuseStep 5052473 = 3789355) B3789355
theorem B3368315 : Blo 2245435 3368315 := bstep (se 1 (by rfl) ⟨2526236, by rfl⟩ : syracuseStep 3368315 = 5052473) B5052473
theorem B2245543 : Blo 2245435 2245543 := bstep (se 1 (by rfl) ⟨1684157, by rfl⟩ : syracuseStep 2245543 = 3368315) B3368315
theorem B2526241 : Blo 2245435 2526241 := bbase (se 2 (by rfl) ⟨947340, by rfl⟩ : syracuseStep 2526241 = 1894681) (by norm_num)
theorem B3368321 : Blo 2245435 3368321 := bstep (se 2 (by rfl) ⟨1263120, by rfl⟩ : syracuseStep 3368321 = 2526241) B2526241
theorem B2245547 : Blo 2245435 2245547 := bstep (se 1 (by rfl) ⟨1684160, by rfl⟩ : syracuseStep 2245547 = 3368321) B3368321
theorem B5684053 : Blo 2245435 5684053 := bbase (se 9 (by rfl) ⟨16652, by rfl⟩ : syracuseStep 5684053 = 33305) (by norm_num)
theorem B7578737 : Blo 2245435 7578737 := bstep (se 2 (by rfl) ⟨2842026, by rfl⟩ : syracuseStep 7578737 = 5684053) B5684053
theorem B5052491 : Blo 2245435 5052491 := bstep (se 1 (by rfl) ⟨3789368, by rfl⟩ : syracuseStep 5052491 = 7578737) B7578737
theorem B3368327 : Blo 2245435 3368327 := bstep (se 1 (by rfl) ⟨2526245, by rfl⟩ : syracuseStep 3368327 = 5052491) B5052491
theorem B2245551 : Blo 2245435 2245551 := bstep (se 1 (by rfl) ⟨1684163, by rfl⟩ : syracuseStep 2245551 = 3368327) B3368327
theorem B3368333 : Blo 2245435 3368333 := bbase (se 3 (by rfl) ⟨631562, by rfl⟩ : syracuseStep 3368333 = 1263125) (by norm_num)
theorem B2245555 : Blo 2245435 2245555 := bstep (se 1 (by rfl) ⟨1684166, by rfl⟩ : syracuseStep 2245555 = 3368333) B3368333
theorem B5052509 : Blo 2245435 5052509 := bbase (se 3 (by rfl) ⟨947345, by rfl⟩ : syracuseStep 5052509 = 1894691) (by norm_num)
theorem B3368339 : Blo 2245435 3368339 := bstep (se 1 (by rfl) ⟨2526254, by rfl⟩ : syracuseStep 3368339 = 5052509) B5052509
theorem B2245559 : Blo 2245435 2245559 := bstep (se 1 (by rfl) ⟨1684169, by rfl⟩ : syracuseStep 2245559 = 3368339) B3368339
theorem B3789389 : Blo 2245435 3789389 := bbase (se 3 (by rfl) ⟨710510, by rfl⟩ : syracuseStep 3789389 = 1421021) (by norm_num)
theorem B2526259 : Blo 2245435 2526259 := bstep (se 1 (by rfl) ⟨1894694, by rfl⟩ : syracuseStep 2526259 = 3789389) B3789389
theorem B3368345 : Blo 2245435 3368345 := bstep (se 2 (by rfl) ⟨1263129, by rfl⟩ : syracuseStep 3368345 = 2526259) B2526259
theorem B2245563 : Blo 2245435 2245563 := bstep (se 1 (by rfl) ⟨1684172, by rfl⟩ : syracuseStep 2245563 = 3368345) B3368345
theorem B32372693 : Blo 2245435 32372693 := bbase (se 7 (by rfl) ⟨379367, by rfl⟩ : syracuseStep 32372693 = 758735) (by norm_num)
theorem B21581795 : Blo 2245435 21581795 := bstep (se 1 (by rfl) ⟨16186346, by rfl⟩ : syracuseStep 21581795 = 32372693) B32372693
theorem B14387863 : Blo 2245435 14387863 := bstep (se 1 (by rfl) ⟨10790897, by rfl⟩ : syracuseStep 14387863 = 21581795) B21581795
theorem B19183817 : Blo 2245435 19183817 := bstep (se 2 (by rfl) ⟨7193931, by rfl⟩ : syracuseStep 19183817 = 14387863) B14387863
theorem B12789211 : Blo 2245435 12789211 := bstep (se 1 (by rfl) ⟨9591908, by rfl⟩ : syracuseStep 12789211 = 19183817) B19183817
theorem B17052281 : Blo 2245435 17052281 := bstep (se 2 (by rfl) ⟨6394605, by rfl⟩ : syracuseStep 17052281 = 12789211) B12789211
theorem B11368187 : Blo 2245435 11368187 := bstep (se 1 (by rfl) ⟨8526140, by rfl⟩ : syracuseStep 11368187 = 17052281) B17052281
theorem B7578791 : Blo 2245435 7578791 := bstep (se 1 (by rfl) ⟨5684093, by rfl⟩ : syracuseStep 7578791 = 11368187) B11368187
theorem B5052527 : Blo 2245435 5052527 := bstep (se 1 (by rfl) ⟨3789395, by rfl⟩ : syracuseStep 5052527 = 7578791) B7578791
theorem B3368351 : Blo 2245435 3368351 := bstep (se 1 (by rfl) ⟨2526263, by rfl⟩ : syracuseStep 3368351 = 5052527) B5052527
theorem B2245567 : Blo 2245435 2245567 := bstep (se 1 (by rfl) ⟨1684175, by rfl⟩ : syracuseStep 2245567 = 3368351) B3368351
theorem B3368357 : Blo 2245435 3368357 := bbase (se 4 (by rfl) ⟨315783, by rfl⟩ : syracuseStep 3368357 = 631567) (by norm_num)
theorem B2245571 : Blo 2245435 2245571 := bstep (se 1 (by rfl) ⟨1684178, by rfl⟩ : syracuseStep 2245571 = 3368357) B3368357
theorem B2842057 : Blo 2245435 2842057 := bbase (se 2 (by rfl) ⟨1065771, by rfl⟩ : syracuseStep 2842057 = 2131543) (by norm_num)
theorem B3789409 : Blo 2245435 3789409 := bstep (se 2 (by rfl) ⟨1421028, by rfl⟩ : syracuseStep 3789409 = 2842057) B2842057
theorem B5052545 : Blo 2245435 5052545 := bstep (se 2 (by rfl) ⟨1894704, by rfl⟩ : syracuseStep 5052545 = 3789409) B3789409
theorem B3368363 : Blo 2245435 3368363 := bstep (se 1 (by rfl) ⟨2526272, by rfl⟩ : syracuseStep 3368363 = 5052545) B5052545
theorem B2245575 : Blo 2245435 2245575 := bstep (se 1 (by rfl) ⟨1684181, by rfl⟩ : syracuseStep 2245575 = 3368363) B3368363
theorem B2526277 : Blo 2245435 2526277 := bbase (se 4 (by rfl) ⟨236838, by rfl⟩ : syracuseStep 2526277 = 473677) (by norm_num)
theorem B3368369 : Blo 2245435 3368369 := bstep (se 2 (by rfl) ⟨1263138, by rfl⟩ : syracuseStep 3368369 = 2526277) B2526277
theorem B2245579 : Blo 2245435 2245579 := bstep (se 1 (by rfl) ⟨1684184, by rfl⟩ : syracuseStep 2245579 = 3368369) B3368369
theorem B4263101 : Blo 2245435 4263101 := bbase (se 3 (by rfl) ⟨799331, by rfl⟩ : syracuseStep 4263101 = 1598663) (by norm_num)
theorem B2842067 : Blo 2245435 2842067 := bstep (se 1 (by rfl) ⟨2131550, by rfl⟩ : syracuseStep 2842067 = 4263101) B4263101
theorem B7578845 : Blo 2245435 7578845 := bstep (se 3 (by rfl) ⟨1421033, by rfl⟩ : syracuseStep 7578845 = 2842067) B2842067
theorem B5052563 : Blo 2245435 5052563 := bstep (se 1 (by rfl) ⟨3789422, by rfl⟩ : syracuseStep 5052563 = 7578845) B7578845
theorem B3368375 : Blo 2245435 3368375 := bstep (se 1 (by rfl) ⟨2526281, by rfl⟩ : syracuseStep 3368375 = 5052563) B5052563
theorem B2245583 : Blo 2245435 2245583 := bstep (se 1 (by rfl) ⟨1684187, by rfl⟩ : syracuseStep 2245583 = 3368375) B3368375
theorem B3368381 : Blo 2245435 3368381 := bbase (se 3 (by rfl) ⟨631571, by rfl⟩ : syracuseStep 3368381 = 1263143) (by norm_num)
theorem B2245587 : Blo 2245435 2245587 := bstep (se 1 (by rfl) ⟨1684190, by rfl⟩ : syracuseStep 2245587 = 3368381) B3368381
theorem B5052581 : Blo 2245435 5052581 := bbase (se 4 (by rfl) ⟨473679, by rfl⟩ : syracuseStep 5052581 = 947359) (by norm_num)
theorem B3368387 : Blo 2245435 3368387 := bstep (se 1 (by rfl) ⟨2526290, by rfl⟩ : syracuseStep 3368387 = 5052581) B5052581
theorem B2245591 : Blo 2245435 2245591 := bstep (se 1 (by rfl) ⟨1684193, by rfl⟩ : syracuseStep 2245591 = 3368387) B3368387
theorem B5684165 : Blo 2245435 5684165 := bbase (se 4 (by rfl) ⟨532890, by rfl⟩ : syracuseStep 5684165 = 1065781) (by norm_num)
theorem B3789443 : Blo 2245435 3789443 := bstep (se 1 (by rfl) ⟨2842082, by rfl⟩ : syracuseStep 3789443 = 5684165) B5684165
theorem B2526295 : Blo 2245435 2526295 := bstep (se 1 (by rfl) ⟨1894721, by rfl⟩ : syracuseStep 2526295 = 3789443) B3789443
theorem B3368393 : Blo 2245435 3368393 := bstep (se 2 (by rfl) ⟨1263147, by rfl⟩ : syracuseStep 3368393 = 2526295) B2526295
theorem B2245595 : Blo 2245435 2245595 := bstep (se 1 (by rfl) ⟨1684196, by rfl⟩ : syracuseStep 2245595 = 3368393) B3368393
theorem B4046645 : Blo 2245435 4046645 := bbase (se 5 (by rfl) ⟨189686, by rfl⟩ : syracuseStep 4046645 = 379373) (by norm_num)
theorem B10791053 : Blo 2245435 10791053 := bstep (se 3 (by rfl) ⟨2023322, by rfl⟩ : syracuseStep 10791053 = 4046645) B4046645
theorem B7194035 : Blo 2245435 7194035 := bstep (se 1 (by rfl) ⟨5395526, by rfl⟩ : syracuseStep 7194035 = 10791053) B10791053
theorem B4796023 : Blo 2245435 4796023 := bstep (se 1 (by rfl) ⟨3597017, by rfl⟩ : syracuseStep 4796023 = 7194035) B7194035
theorem B6394697 : Blo 2245435 6394697 := bstep (se 2 (by rfl) ⟨2398011, by rfl⟩ : syracuseStep 6394697 = 4796023) B4796023
theorem B4263131 : Blo 2245435 4263131 := bstep (se 1 (by rfl) ⟨3197348, by rfl⟩ : syracuseStep 4263131 = 6394697) B6394697
theorem B11368349 : Blo 2245435 11368349 := bstep (se 3 (by rfl) ⟨2131565, by rfl⟩ : syracuseStep 11368349 = 4263131) B4263131
theorem B7578899 : Blo 2245435 7578899 := bstep (se 1 (by rfl) ⟨5684174, by rfl⟩ : syracuseStep 7578899 = 11368349) B11368349
theorem B5052599 : Blo 2245435 5052599 := bstep (se 1 (by rfl) ⟨3789449, by rfl⟩ : syracuseStep 5052599 = 7578899) B7578899
theorem B3368399 : Blo 2245435 3368399 := bstep (se 1 (by rfl) ⟨2526299, by rfl⟩ : syracuseStep 3368399 = 5052599) B5052599
theorem B2245599 : Blo 2245435 2245599 := bstep (se 1 (by rfl) ⟨1684199, by rfl⟩ : syracuseStep 2245599 = 3368399) B3368399
theorem B3368405 : Blo 2245435 3368405 := bbase (se 7 (by rfl) ⟨39473, by rfl⟩ : syracuseStep 3368405 = 78947) (by norm_num)
theorem B2245603 : Blo 2245435 2245603 := bstep (se 1 (by rfl) ⟨1684202, by rfl⟩ : syracuseStep 2245603 = 3368405) B3368405
theorem B8526293 : Blo 2245435 8526293 := bbase (se 7 (by rfl) ⟨99917, by rfl⟩ : syracuseStep 8526293 = 199835) (by norm_num)
theorem B5684195 : Blo 2245435 5684195 := bstep (se 1 (by rfl) ⟨4263146, by rfl⟩ : syracuseStep 5684195 = 8526293) B8526293
theorem B3789463 : Blo 2245435 3789463 := bstep (se 1 (by rfl) ⟨2842097, by rfl⟩ : syracuseStep 3789463 = 5684195) B5684195
theorem B5052617 : Blo 2245435 5052617 := bstep (se 2 (by rfl) ⟨1894731, by rfl⟩ : syracuseStep 5052617 = 3789463) B3789463
theorem B3368411 : Blo 2245435 3368411 := bstep (se 1 (by rfl) ⟨2526308, by rfl⟩ : syracuseStep 3368411 = 5052617) B5052617
theorem B2245607 : Blo 2245435 2245607 := bstep (se 1 (by rfl) ⟨1684205, by rfl⟩ : syracuseStep 2245607 = 3368411) B3368411
theorem B2526313 : Blo 2245435 2526313 := bbase (se 2 (by rfl) ⟨947367, by rfl⟩ : syracuseStep 2526313 = 1894735) (by norm_num)
theorem B3368417 : Blo 2245435 3368417 := bstep (se 2 (by rfl) ⟨1263156, by rfl⟩ : syracuseStep 3368417 = 2526313) B2526313
theorem B2245611 : Blo 2245435 2245611 := bstep (se 1 (by rfl) ⟨1684208, by rfl⟩ : syracuseStep 2245611 = 3368417) B3368417
theorem B5395565 : Blo 2245435 5395565 := bbase (se 3 (by rfl) ⟨1011668, by rfl⟩ : syracuseStep 5395565 = 2023337) (by norm_num)
theorem B3597043 : Blo 2245435 3597043 := bstep (se 1 (by rfl) ⟨2697782, by rfl⟩ : syracuseStep 3597043 = 5395565) B5395565
theorem B4796057 : Blo 2245435 4796057 := bstep (se 2 (by rfl) ⟨1798521, by rfl⟩ : syracuseStep 4796057 = 3597043) B3597043
theorem B12789485 : Blo 2245435 12789485 := bstep (se 3 (by rfl) ⟨2398028, by rfl⟩ : syracuseStep 12789485 = 4796057) B4796057
theorem B8526323 : Blo 2245435 8526323 := bstep (se 1 (by rfl) ⟨6394742, by rfl⟩ : syracuseStep 8526323 = 12789485) B12789485
theorem B5684215 : Blo 2245435 5684215 := bstep (se 1 (by rfl) ⟨4263161, by rfl⟩ : syracuseStep 5684215 = 8526323) B8526323
theorem B7578953 : Blo 2245435 7578953 := bstep (se 2 (by rfl) ⟨2842107, by rfl⟩ : syracuseStep 7578953 = 5684215) B5684215
theorem B5052635 : Blo 2245435 5052635 := bstep (se 1 (by rfl) ⟨3789476, by rfl⟩ : syracuseStep 5052635 = 7578953) B7578953
theorem B3368423 : Blo 2245435 3368423 := bstep (se 1 (by rfl) ⟨2526317, by rfl⟩ : syracuseStep 3368423 = 5052635) B5052635
theorem B2245615 : Blo 2245435 2245615 := bstep (se 1 (by rfl) ⟨1684211, by rfl⟩ : syracuseStep 2245615 = 3368423) B3368423
theorem B3368429 : Blo 2245435 3368429 := bbase (se 3 (by rfl) ⟨631580, by rfl⟩ : syracuseStep 3368429 = 1263161) (by norm_num)
theorem B2245619 : Blo 2245435 2245619 := bstep (se 1 (by rfl) ⟨1684214, by rfl⟩ : syracuseStep 2245619 = 3368429) B3368429
theorem B5052653 : Blo 2245435 5052653 := bbase (se 3 (by rfl) ⟨947372, by rfl⟩ : syracuseStep 5052653 = 1894745) (by norm_num)
theorem B3368435 : Blo 2245435 3368435 := bstep (se 1 (by rfl) ⟨2526326, by rfl⟩ : syracuseStep 3368435 = 5052653) B5052653
theorem B2245623 : Blo 2245435 2245623 := bstep (se 1 (by rfl) ⟨1684217, by rfl⟩ : syracuseStep 2245623 = 3368435) B3368435
theorem B3197389 : Blo 2245435 3197389 := bbase (se 3 (by rfl) ⟨599510, by rfl⟩ : syracuseStep 3197389 = 1199021) (by norm_num)
theorem B4263185 : Blo 2245435 4263185 := bstep (se 2 (by rfl) ⟨1598694, by rfl⟩ : syracuseStep 4263185 = 3197389) B3197389
theorem B2842123 : Blo 2245435 2842123 := bstep (se 1 (by rfl) ⟨2131592, by rfl⟩ : syracuseStep 2842123 = 4263185) B4263185
theorem B3789497 : Blo 2245435 3789497 := bstep (se 2 (by rfl) ⟨1421061, by rfl⟩ : syracuseStep 3789497 = 2842123) B2842123
theorem B2526331 : Blo 2245435 2526331 := bstep (se 1 (by rfl) ⟨1894748, by rfl⟩ : syracuseStep 2526331 = 3789497) B3789497
theorem B3368441 : Blo 2245435 3368441 := bstep (se 2 (by rfl) ⟨1263165, by rfl⟩ : syracuseStep 3368441 = 2526331) B2526331
theorem B2245627 : Blo 2245435 2245627 := bstep (se 1 (by rfl) ⟨1684220, by rfl⟩ : syracuseStep 2245627 = 3368441) B3368441
theorem B2734609 : Blo 2245435 2734609 := bbase (se 2 (by rfl) ⟨1025478, by rfl⟩ : syracuseStep 2734609 = 2050957) (by norm_num)
theorem B3646145 : Blo 2245435 3646145 := bstep (se 2 (by rfl) ⟨1367304, by rfl⟩ : syracuseStep 3646145 = 2734609) B2734609
theorem B9723053 : Blo 2245435 9723053 := bstep (se 3 (by rfl) ⟨1823072, by rfl⟩ : syracuseStep 9723053 = 3646145) B3646145
theorem B6482035 : Blo 2245435 6482035 := bstep (se 1 (by rfl) ⟨4861526, by rfl⟩ : syracuseStep 6482035 = 9723053) B9723053
theorem B8642713 : Blo 2245435 8642713 := bstep (se 2 (by rfl) ⟨3241017, by rfl⟩ : syracuseStep 8642713 = 6482035) B6482035
theorem B11523617 : Blo 2245435 11523617 := bstep (se 2 (by rfl) ⟨4321356, by rfl⟩ : syracuseStep 11523617 = 8642713) B8642713
theorem B7682411 : Blo 2245435 7682411 := bstep (se 1 (by rfl) ⟨5761808, by rfl⟩ : syracuseStep 7682411 = 11523617) B11523617
theorem B20486429 : Blo 2245435 20486429 := bstep (se 3 (by rfl) ⟨3841205, by rfl⟩ : syracuseStep 20486429 = 7682411) B7682411
theorem B13657619 : Blo 2245435 13657619 := bstep (se 1 (by rfl) ⟨10243214, by rfl⟩ : syracuseStep 13657619 = 20486429) B20486429
theorem B36420317 : Blo 2245435 36420317 := bstep (se 3 (by rfl) ⟨6828809, by rfl⟩ : syracuseStep 36420317 = 13657619) B13657619
theorem B24280211 : Blo 2245435 24280211 := bstep (se 1 (by rfl) ⟨18210158, by rfl⟩ : syracuseStep 24280211 = 36420317) B36420317
theorem B16186807 : Blo 2245435 16186807 := bstep (se 1 (by rfl) ⟨12140105, by rfl⟩ : syracuseStep 16186807 = 24280211) B24280211
theorem B86329637 : Blo 2245435 86329637 := bstep (se 4 (by rfl) ⟨8093403, by rfl⟩ : syracuseStep 86329637 = 16186807) B16186807
theorem B57553091 : Blo 2245435 57553091 := bstep (se 1 (by rfl) ⟨43164818, by rfl⟩ : syracuseStep 57553091 = 86329637) B86329637
theorem B38368727 : Blo 2245435 38368727 := bstep (se 1 (by rfl) ⟨28776545, by rfl⟩ : syracuseStep 38368727 = 57553091) B57553091
theorem B25579151 : Blo 2245435 25579151 := bstep (se 1 (by rfl) ⟨19184363, by rfl⟩ : syracuseStep 25579151 = 38368727) B38368727
theorem B17052767 : Blo 2245435 17052767 := bstep (se 1 (by rfl) ⟨12789575, by rfl⟩ : syracuseStep 17052767 = 25579151) B25579151
theorem B11368511 : Blo 2245435 11368511 := bstep (se 1 (by rfl) ⟨8526383, by rfl⟩ : syracuseStep 11368511 = 17052767) B17052767
theorem B7579007 : Blo 2245435 7579007 := bstep (se 1 (by rfl) ⟨5684255, by rfl⟩ : syracuseStep 7579007 = 11368511) B11368511
theorem B5052671 : Blo 2245435 5052671 := bstep (se 1 (by rfl) ⟨3789503, by rfl⟩ : syracuseStep 5052671 = 7579007) B7579007
theorem B3368447 : Blo 2245435 3368447 := bstep (se 1 (by rfl) ⟨2526335, by rfl⟩ : syracuseStep 3368447 = 5052671) B5052671
theorem B2245631 : Blo 2245435 2245631 := bstep (se 1 (by rfl) ⟨1684223, by rfl⟩ : syracuseStep 2245631 = 3368447) B3368447
theorem B3368453 : Blo 2245435 3368453 := bbase (se 4 (by rfl) ⟨315792, by rfl⟩ : syracuseStep 3368453 = 631585) (by norm_num)
theorem B2245635 : Blo 2245435 2245635 := bstep (se 1 (by rfl) ⟨1684226, by rfl⟩ : syracuseStep 2245635 = 3368453) B3368453
theorem B3789517 : Blo 2245435 3789517 := bbase (se 3 (by rfl) ⟨710534, by rfl⟩ : syracuseStep 3789517 = 1421069) (by norm_num)
theorem B5052689 : Blo 2245435 5052689 := bstep (se 2 (by rfl) ⟨1894758, by rfl⟩ : syracuseStep 5052689 = 3789517) B3789517
theorem B3368459 : Blo 2245435 3368459 := bstep (se 1 (by rfl) ⟨2526344, by rfl⟩ : syracuseStep 3368459 = 5052689) B5052689
theorem B2245639 : Blo 2245435 2245639 := bstep (se 1 (by rfl) ⟨1684229, by rfl⟩ : syracuseStep 2245639 = 3368459) B3368459
theorem B2526349 : Blo 2245435 2526349 := bbase (se 3 (by rfl) ⟨473690, by rfl⟩ : syracuseStep 2526349 = 947381) (by norm_num)
theorem B3368465 : Blo 2245435 3368465 := bstep (se 2 (by rfl) ⟨1263174, by rfl⟩ : syracuseStep 3368465 = 2526349) B2526349
theorem B2245643 : Blo 2245435 2245643 := bstep (se 1 (by rfl) ⟨1684232, by rfl⟩ : syracuseStep 2245643 = 3368465) B3368465
theorem B7579061 : Blo 2245435 7579061 := bbase (se 5 (by rfl) ⟨355268, by rfl⟩ : syracuseStep 7579061 = 710537) (by norm_num)
theorem B5052707 : Blo 2245435 5052707 := bstep (se 1 (by rfl) ⟨3789530, by rfl⟩ : syracuseStep 5052707 = 7579061) B7579061
theorem B3368471 : Blo 2245435 3368471 := bstep (se 1 (by rfl) ⟨2526353, by rfl⟩ : syracuseStep 3368471 = 5052707) B5052707
theorem B2245647 : Blo 2245435 2245647 := bstep (se 1 (by rfl) ⟨1684235, by rfl⟩ : syracuseStep 2245647 = 3368471) B3368471
theorem B3368477 : Blo 2245435 3368477 := bbase (se 3 (by rfl) ⟨631589, by rfl⟩ : syracuseStep 3368477 = 1263179) (by norm_num)
theorem B2245651 : Blo 2245435 2245651 := bstep (se 1 (by rfl) ⟨1684238, by rfl⟩ : syracuseStep 2245651 = 3368477) B3368477
theorem B5052725 : Blo 2245435 5052725 := bbase (se 5 (by rfl) ⟨236846, by rfl⟩ : syracuseStep 5052725 = 473693) (by norm_num)
theorem B3368483 : Blo 2245435 3368483 := bstep (se 1 (by rfl) ⟨2526362, by rfl⟩ : syracuseStep 3368483 = 5052725) B5052725
theorem B2245655 : Blo 2245435 2245655 := bstep (se 1 (by rfl) ⟨1684241, by rfl⟩ : syracuseStep 2245655 = 3368483) B3368483
theorem B6482117 : Blo 2245435 6482117 := bbase (se 4 (by rfl) ⟨607698, by rfl⟩ : syracuseStep 6482117 = 1215397) (by norm_num)
theorem B4321411 : Blo 2245435 4321411 := bstep (se 1 (by rfl) ⟨3241058, by rfl⟩ : syracuseStep 4321411 = 6482117) B6482117
theorem B23047525 : Blo 2245435 23047525 := bstep (se 4 (by rfl) ⟨2160705, by rfl⟩ : syracuseStep 23047525 = 4321411) B4321411
theorem B30730033 : Blo 2245435 30730033 := bstep (se 2 (by rfl) ⟨11523762, by rfl⟩ : syracuseStep 30730033 = 23047525) B23047525
theorem B40973377 : Blo 2245435 40973377 := bstep (se 2 (by rfl) ⟨15365016, by rfl⟩ : syracuseStep 40973377 = 30730033) B30730033
theorem B54631169 : Blo 2245435 54631169 := bstep (se 2 (by rfl) ⟨20486688, by rfl⟩ : syracuseStep 54631169 = 40973377) B40973377
theorem B36420779 : Blo 2245435 36420779 := bstep (se 1 (by rfl) ⟨27315584, by rfl⟩ : syracuseStep 36420779 = 54631169) B54631169
theorem B24280519 : Blo 2245435 24280519 := bstep (se 1 (by rfl) ⟨18210389, by rfl⟩ : syracuseStep 24280519 = 36420779) B36420779
theorem B32374025 : Blo 2245435 32374025 := bstep (se 2 (by rfl) ⟨12140259, by rfl⟩ : syracuseStep 32374025 = 24280519) B24280519
theorem B21582683 : Blo 2245435 21582683 := bstep (se 1 (by rfl) ⟨16187012, by rfl⟩ : syracuseStep 21582683 = 32374025) B32374025
theorem B14388455 : Blo 2245435 14388455 := bstep (se 1 (by rfl) ⟨10791341, by rfl⟩ : syracuseStep 14388455 = 21582683) B21582683
theorem B9592303 : Blo 2245435 9592303 := bstep (se 1 (by rfl) ⟨7194227, by rfl⟩ : syracuseStep 9592303 = 14388455) B14388455
theorem B12789737 : Blo 2245435 12789737 := bstep (se 2 (by rfl) ⟨4796151, by rfl⟩ : syracuseStep 12789737 = 9592303) B9592303
theorem B8526491 : Blo 2245435 8526491 := bstep (se 1 (by rfl) ⟨6394868, by rfl⟩ : syracuseStep 8526491 = 12789737) B12789737
theorem B5684327 : Blo 2245435 5684327 := bstep (se 1 (by rfl) ⟨4263245, by rfl⟩ : syracuseStep 5684327 = 8526491) B8526491
theorem B3789551 : Blo 2245435 3789551 := bstep (se 1 (by rfl) ⟨2842163, by rfl⟩ : syracuseStep 3789551 = 5684327) B5684327
theorem B2526367 : Blo 2245435 2526367 := bstep (se 1 (by rfl) ⟨1894775, by rfl⟩ : syracuseStep 2526367 = 3789551) B3789551
theorem B3368489 : Blo 2245435 3368489 := bstep (se 2 (by rfl) ⟨1263183, by rfl⟩ : syracuseStep 3368489 = 2526367) B2526367
theorem B2245659 : Blo 2245435 2245659 := bstep (se 1 (by rfl) ⟨1684244, by rfl⟩ : syracuseStep 2245659 = 3368489) B3368489
theorem B4927925 : Blo 2245435 4927925 := bbase (se 5 (by rfl) ⟨230996, by rfl⟩ : syracuseStep 4927925 = 461993) (by norm_num)
theorem B13141133 : Blo 2245435 13141133 := bstep (se 3 (by rfl) ⟨2463962, by rfl⟩ : syracuseStep 13141133 = 4927925) B4927925
theorem B8760755 : Blo 2245435 8760755 := bstep (se 1 (by rfl) ⟨6570566, by rfl⟩ : syracuseStep 8760755 = 13141133) B13141133
theorem B23362013 : Blo 2245435 23362013 := bstep (se 3 (by rfl) ⟨4380377, by rfl⟩ : syracuseStep 23362013 = 8760755) B8760755
theorem B15574675 : Blo 2245435 15574675 := bstep (se 1 (by rfl) ⟨11681006, by rfl⟩ : syracuseStep 15574675 = 23362013) B23362013
theorem B20766233 : Blo 2245435 20766233 := bstep (se 2 (by rfl) ⟨7787337, by rfl⟩ : syracuseStep 20766233 = 15574675) B15574675
theorem B13844155 : Blo 2245435 13844155 := bstep (se 1 (by rfl) ⟨10383116, by rfl⟩ : syracuseStep 13844155 = 20766233) B20766233
theorem B18458873 : Blo 2245435 18458873 := bstep (se 2 (by rfl) ⟨6922077, by rfl⟩ : syracuseStep 18458873 = 13844155) B13844155
theorem B12305915 : Blo 2245435 12305915 := bstep (se 1 (by rfl) ⟨9229436, by rfl⟩ : syracuseStep 12305915 = 18458873) B18458873
theorem B8203943 : Blo 2245435 8203943 := bstep (se 1 (by rfl) ⟨6152957, by rfl⟩ : syracuseStep 8203943 = 12305915) B12305915
theorem B5469295 : Blo 2245435 5469295 := bstep (se 1 (by rfl) ⟨4101971, by rfl⟩ : syracuseStep 5469295 = 8203943) B8203943
theorem B7292393 : Blo 2245435 7292393 := bstep (se 2 (by rfl) ⟨2734647, by rfl⟩ : syracuseStep 7292393 = 5469295) B5469295
theorem B77785525 : Blo 2245435 77785525 := bstep (se 5 (by rfl) ⟨3646196, by rfl⟩ : syracuseStep 77785525 = 7292393) B7292393
theorem B103714033 : Blo 2245435 103714033 := bstep (se 2 (by rfl) ⟨38892762, by rfl⟩ : syracuseStep 103714033 = 77785525) B77785525
theorem B138285377 : Blo 2245435 138285377 := bstep (se 2 (by rfl) ⟨51857016, by rfl⟩ : syracuseStep 138285377 = 103714033) B103714033
theorem B92190251 : Blo 2245435 92190251 := bstep (se 1 (by rfl) ⟨69142688, by rfl⟩ : syracuseStep 92190251 = 138285377) B138285377
theorem B245840669 : Blo 2245435 245840669 := bstep (se 3 (by rfl) ⟨46095125, by rfl⟩ : syracuseStep 245840669 = 92190251) B92190251
theorem B163893779 : Blo 2245435 163893779 := bstep (se 1 (by rfl) ⟨122920334, by rfl⟩ : syracuseStep 163893779 = 245840669) B245840669
theorem B109262519 : Blo 2245435 109262519 := bstep (se 1 (by rfl) ⟨81946889, by rfl⟩ : syracuseStep 109262519 = 163893779) B163893779
theorem B72841679 : Blo 2245435 72841679 := bstep (se 1 (by rfl) ⟨54631259, by rfl⟩ : syracuseStep 72841679 = 109262519) B109262519
theorem B48561119 : Blo 2245435 48561119 := bstep (se 1 (by rfl) ⟨36420839, by rfl⟩ : syracuseStep 48561119 = 72841679) B72841679
theorem B32374079 : Blo 2245435 32374079 := bstep (se 1 (by rfl) ⟨24280559, by rfl⟩ : syracuseStep 32374079 = 48561119) B48561119
theorem B21582719 : Blo 2245435 21582719 := bstep (se 1 (by rfl) ⟨16187039, by rfl⟩ : syracuseStep 21582719 = 32374079) B32374079
theorem B14388479 : Blo 2245435 14388479 := bstep (se 1 (by rfl) ⟨10791359, by rfl⟩ : syracuseStep 14388479 = 21582719) B21582719
theorem B9592319 : Blo 2245435 9592319 := bstep (se 1 (by rfl) ⟨7194239, by rfl⟩ : syracuseStep 9592319 = 14388479) B14388479
theorem B6394879 : Blo 2245435 6394879 := bstep (se 1 (by rfl) ⟨4796159, by rfl⟩ : syracuseStep 6394879 = 9592319) B9592319
theorem B8526505 : Blo 2245435 8526505 := bstep (se 2 (by rfl) ⟨3197439, by rfl⟩ : syracuseStep 8526505 = 6394879) B6394879
theorem B11368673 : Blo 2245435 11368673 := bstep (se 2 (by rfl) ⟨4263252, by rfl⟩ : syracuseStep 11368673 = 8526505) B8526505
theorem B7579115 : Blo 2245435 7579115 := bstep (se 1 (by rfl) ⟨5684336, by rfl⟩ : syracuseStep 7579115 = 11368673) B11368673
theorem B5052743 : Blo 2245435 5052743 := bstep (se 1 (by rfl) ⟨3789557, by rfl⟩ : syracuseStep 5052743 = 7579115) B7579115
theorem B3368495 : Blo 2245435 3368495 := bstep (se 1 (by rfl) ⟨2526371, by rfl⟩ : syracuseStep 3368495 = 5052743) B5052743
theorem B2245663 : Blo 2245435 2245663 := bstep (se 1 (by rfl) ⟨1684247, by rfl⟩ : syracuseStep 2245663 = 3368495) B3368495
theorem B3368501 : Blo 2245435 3368501 := bbase (se 5 (by rfl) ⟨157898, by rfl⟩ : syracuseStep 3368501 = 315797) (by norm_num)
theorem B2245667 : Blo 2245435 2245667 := bstep (se 1 (by rfl) ⟨1684250, by rfl⟩ : syracuseStep 2245667 = 3368501) B3368501
theorem B5684357 : Blo 2245435 5684357 := bbase (se 4 (by rfl) ⟨532908, by rfl⟩ : syracuseStep 5684357 = 1065817) (by norm_num)
theorem B3789571 : Blo 2245435 3789571 := bstep (se 1 (by rfl) ⟨2842178, by rfl⟩ : syracuseStep 3789571 = 5684357) B5684357
theorem B5052761 : Blo 2245435 5052761 := bstep (se 2 (by rfl) ⟨1894785, by rfl⟩ : syracuseStep 5052761 = 3789571) B3789571
theorem B3368507 : Blo 2245435 3368507 := bstep (se 1 (by rfl) ⟨2526380, by rfl⟩ : syracuseStep 3368507 = 5052761) B5052761
theorem B2245671 : Blo 2245435 2245671 := bstep (se 1 (by rfl) ⟨1684253, by rfl⟩ : syracuseStep 2245671 = 3368507) B3368507
theorem B2526385 : Blo 2245435 2526385 := bbase (se 2 (by rfl) ⟨947394, by rfl⟩ : syracuseStep 2526385 = 1894789) (by norm_num)
theorem B3368513 : Blo 2245435 3368513 := bstep (se 2 (by rfl) ⟨1263192, by rfl⟩ : syracuseStep 3368513 = 2526385) B2526385
theorem B2245675 : Blo 2245435 2245675 := bstep (se 1 (by rfl) ⟨1684256, by rfl⟩ : syracuseStep 2245675 = 3368513) B3368513
theorem B2398097 : Blo 2245435 2398097 := bbase (se 2 (by rfl) ⟨899286, by rfl⟩ : syracuseStep 2398097 = 1798573) (by norm_num)
theorem B6394925 : Blo 2245435 6394925 := bstep (se 3 (by rfl) ⟨1199048, by rfl⟩ : syracuseStep 6394925 = 2398097) B2398097
theorem B4263283 : Blo 2245435 4263283 := bstep (se 1 (by rfl) ⟨3197462, by rfl⟩ : syracuseStep 4263283 = 6394925) B6394925
theorem B5684377 : Blo 2245435 5684377 := bstep (se 2 (by rfl) ⟨2131641, by rfl⟩ : syracuseStep 5684377 = 4263283) B4263283
theorem B7579169 : Blo 2245435 7579169 := bstep (se 2 (by rfl) ⟨2842188, by rfl⟩ : syracuseStep 7579169 = 5684377) B5684377
theorem B5052779 : Blo 2245435 5052779 := bstep (se 1 (by rfl) ⟨3789584, by rfl⟩ : syracuseStep 5052779 = 7579169) B7579169
theorem B3368519 : Blo 2245435 3368519 := bstep (se 1 (by rfl) ⟨2526389, by rfl⟩ : syracuseStep 3368519 = 5052779) B5052779
theorem B2245679 : Blo 2245435 2245679 := bstep (se 1 (by rfl) ⟨1684259, by rfl⟩ : syracuseStep 2245679 = 3368519) B3368519
theorem B3368525 : Blo 2245435 3368525 := bbase (se 3 (by rfl) ⟨631598, by rfl⟩ : syracuseStep 3368525 = 1263197) (by norm_num)
theorem B2245683 : Blo 2245435 2245683 := bstep (se 1 (by rfl) ⟨1684262, by rfl⟩ : syracuseStep 2245683 = 3368525) B3368525
theorem B5052797 : Blo 2245435 5052797 := bbase (se 3 (by rfl) ⟨947399, by rfl⟩ : syracuseStep 5052797 = 1894799) (by norm_num)
theorem B3368531 : Blo 2245435 3368531 := bstep (se 1 (by rfl) ⟨2526398, by rfl⟩ : syracuseStep 3368531 = 5052797) B5052797
theorem B2245687 : Blo 2245435 2245687 := bstep (se 1 (by rfl) ⟨1684265, by rfl⟩ : syracuseStep 2245687 = 3368531) B3368531
theorem B3789605 : Blo 2245435 3789605 := bbase (se 4 (by rfl) ⟨355275, by rfl⟩ : syracuseStep 3789605 = 710551) (by norm_num)
theorem B2526403 : Blo 2245435 2526403 := bstep (se 1 (by rfl) ⟨1894802, by rfl⟩ : syracuseStep 2526403 = 3789605) B3789605
theorem B3368537 : Blo 2245435 3368537 := bstep (se 2 (by rfl) ⟨1263201, by rfl⟩ : syracuseStep 3368537 = 2526403) B2526403
theorem B2245691 : Blo 2245435 2245691 := bstep (se 1 (by rfl) ⟨1684268, by rfl⟩ : syracuseStep 2245691 = 3368537) B3368537
theorem B3197485 : Blo 2245435 3197485 := bbase (se 3 (by rfl) ⟨599528, by rfl⟩ : syracuseStep 3197485 = 1199057) (by norm_num)
theorem B17053253 : Blo 2245435 17053253 := bstep (se 4 (by rfl) ⟨1598742, by rfl⟩ : syracuseStep 17053253 = 3197485) B3197485
theorem B11368835 : Blo 2245435 11368835 := bstep (se 1 (by rfl) ⟨8526626, by rfl⟩ : syracuseStep 11368835 = 17053253) B17053253
theorem B7579223 : Blo 2245435 7579223 := bstep (se 1 (by rfl) ⟨5684417, by rfl⟩ : syracuseStep 7579223 = 11368835) B11368835
theorem B5052815 : Blo 2245435 5052815 := bstep (se 1 (by rfl) ⟨3789611, by rfl⟩ : syracuseStep 5052815 = 7579223) B7579223
theorem B3368543 : Blo 2245435 3368543 := bstep (se 1 (by rfl) ⟨2526407, by rfl⟩ : syracuseStep 3368543 = 5052815) B5052815
theorem B2245695 : Blo 2245435 2245695 := bstep (se 1 (by rfl) ⟨1684271, by rfl⟩ : syracuseStep 2245695 = 3368543) B3368543
theorem B3368549 : Blo 2245435 3368549 := bbase (se 4 (by rfl) ⟨315801, by rfl⟩ : syracuseStep 3368549 = 631603) (by norm_num)
theorem B2245699 : Blo 2245435 2245699 := bstep (se 1 (by rfl) ⟨1684274, by rfl⟩ : syracuseStep 2245699 = 3368549) B3368549
theorem B2697889 : Blo 2245435 2697889 := bbase (se 2 (by rfl) ⟨1011708, by rfl⟩ : syracuseStep 2697889 = 2023417) (by norm_num)
theorem B3597185 : Blo 2245435 3597185 := bstep (se 2 (by rfl) ⟨1348944, by rfl⟩ : syracuseStep 3597185 = 2697889) B2697889
theorem B2398123 : Blo 2245435 2398123 := bstep (se 1 (by rfl) ⟨1798592, by rfl⟩ : syracuseStep 2398123 = 3597185) B3597185
theorem B3197497 : Blo 2245435 3197497 := bstep (se 2 (by rfl) ⟨1199061, by rfl⟩ : syracuseStep 3197497 = 2398123) B2398123
theorem B4263329 : Blo 2245435 4263329 := bstep (se 2 (by rfl) ⟨1598748, by rfl⟩ : syracuseStep 4263329 = 3197497) B3197497
theorem B2842219 : Blo 2245435 2842219 := bstep (se 1 (by rfl) ⟨2131664, by rfl⟩ : syracuseStep 2842219 = 4263329) B4263329
theorem B3789625 : Blo 2245435 3789625 := bstep (se 2 (by rfl) ⟨1421109, by rfl⟩ : syracuseStep 3789625 = 2842219) B2842219
theorem B5052833 : Blo 2245435 5052833 := bstep (se 2 (by rfl) ⟨1894812, by rfl⟩ : syracuseStep 5052833 = 3789625) B3789625
theorem B3368555 : Blo 2245435 3368555 := bstep (se 1 (by rfl) ⟨2526416, by rfl⟩ : syracuseStep 3368555 = 5052833) B5052833
theorem B2245703 : Blo 2245435 2245703 := bstep (se 1 (by rfl) ⟨1684277, by rfl⟩ : syracuseStep 2245703 = 3368555) B3368555
theorem B2526421 : Blo 2245435 2526421 := bbase (se 7 (by rfl) ⟨29606, by rfl⟩ : syracuseStep 2526421 = 59213) (by norm_num)
theorem B3368561 : Blo 2245435 3368561 := bstep (se 2 (by rfl) ⟨1263210, by rfl⟩ : syracuseStep 3368561 = 2526421) B2526421
theorem B2245707 : Blo 2245435 2245707 := bstep (se 1 (by rfl) ⟨1684280, by rfl⟩ : syracuseStep 2245707 = 3368561) B3368561
theorem B2842229 : Blo 2245435 2842229 := bbase (se 5 (by rfl) ⟨133229, by rfl⟩ : syracuseStep 2842229 = 266459) (by norm_num)
theorem B7579277 : Blo 2245435 7579277 := bstep (se 3 (by rfl) ⟨1421114, by rfl⟩ : syracuseStep 7579277 = 2842229) B2842229
theorem B5052851 : Blo 2245435 5052851 := bstep (se 1 (by rfl) ⟨3789638, by rfl⟩ : syracuseStep 5052851 = 7579277) B7579277
theorem B3368567 : Blo 2245435 3368567 := bstep (se 1 (by rfl) ⟨2526425, by rfl⟩ : syracuseStep 3368567 = 5052851) B5052851
theorem B2245711 : Blo 2245435 2245711 := bstep (se 1 (by rfl) ⟨1684283, by rfl⟩ : syracuseStep 2245711 = 3368567) B3368567
theorem B3368573 : Blo 2245435 3368573 := bbase (se 3 (by rfl) ⟨631607, by rfl⟩ : syracuseStep 3368573 = 1263215) (by norm_num)
theorem B2245715 : Blo 2245435 2245715 := bstep (se 1 (by rfl) ⟨1684286, by rfl⟩ : syracuseStep 2245715 = 3368573) B3368573
theorem B5052869 : Blo 2245435 5052869 := bbase (se 4 (by rfl) ⟨473706, by rfl⟩ : syracuseStep 5052869 = 947413) (by norm_num)
theorem B3368579 : Blo 2245435 3368579 := bstep (se 1 (by rfl) ⟨2526434, by rfl⟩ : syracuseStep 3368579 = 5052869) B5052869
theorem B2245719 : Blo 2245435 2245719 := bstep (se 1 (by rfl) ⟨1684289, by rfl⟩ : syracuseStep 2245719 = 3368579) B3368579
theorem B4046869 : Blo 2245435 4046869 := bbase (se 6 (by rfl) ⟨94848, by rfl⟩ : syracuseStep 4046869 = 189697) (by norm_num)
theorem B5395825 : Blo 2245435 5395825 := bstep (se 2 (by rfl) ⟨2023434, by rfl⟩ : syracuseStep 5395825 = 4046869) B4046869
theorem B7194433 : Blo 2245435 7194433 := bstep (se 2 (by rfl) ⟨2697912, by rfl⟩ : syracuseStep 7194433 = 5395825) B5395825
theorem B9592577 : Blo 2245435 9592577 := bstep (se 2 (by rfl) ⟨3597216, by rfl⟩ : syracuseStep 9592577 = 7194433) B7194433
theorem B6395051 : Blo 2245435 6395051 := bstep (se 1 (by rfl) ⟨4796288, by rfl⟩ : syracuseStep 6395051 = 9592577) B9592577
theorem B4263367 : Blo 2245435 4263367 := bstep (se 1 (by rfl) ⟨3197525, by rfl⟩ : syracuseStep 4263367 = 6395051) B6395051
theorem B5684489 : Blo 2245435 5684489 := bstep (se 2 (by rfl) ⟨2131683, by rfl⟩ : syracuseStep 5684489 = 4263367) B4263367
theorem B3789659 : Blo 2245435 3789659 := bstep (se 1 (by rfl) ⟨2842244, by rfl⟩ : syracuseStep 3789659 = 5684489) B5684489
theorem B2526439 : Blo 2245435 2526439 := bstep (se 1 (by rfl) ⟨1894829, by rfl⟩ : syracuseStep 2526439 = 3789659) B3789659
theorem B3368585 : Blo 2245435 3368585 := bstep (se 2 (by rfl) ⟨1263219, by rfl⟩ : syracuseStep 3368585 = 2526439) B2526439
theorem B2245723 : Blo 2245435 2245723 := bstep (se 1 (by rfl) ⟨1684292, by rfl⟩ : syracuseStep 2245723 = 3368585) B3368585
theorem B11368997 : Blo 2245435 11368997 := bbase (se 4 (by rfl) ⟨1065843, by rfl⟩ : syracuseStep 11368997 = 2131687) (by norm_num)
theorem B7579331 : Blo 2245435 7579331 := bstep (se 1 (by rfl) ⟨5684498, by rfl⟩ : syracuseStep 7579331 = 11368997) B11368997
theorem B5052887 : Blo 2245435 5052887 := bstep (se 1 (by rfl) ⟨3789665, by rfl⟩ : syracuseStep 5052887 = 7579331) B7579331
theorem B3368591 : Blo 2245435 3368591 := bstep (se 1 (by rfl) ⟨2526443, by rfl⟩ : syracuseStep 3368591 = 5052887) B5052887
theorem B2245727 : Blo 2245435 2245727 := bstep (se 1 (by rfl) ⟨1684295, by rfl⟩ : syracuseStep 2245727 = 3368591) B3368591
theorem B3368597 : Blo 2245435 3368597 := bbase (se 6 (by rfl) ⟨78951, by rfl⟩ : syracuseStep 3368597 = 157903) (by norm_num)
theorem B2245731 : Blo 2245435 2245731 := bstep (se 1 (by rfl) ⟨1684298, by rfl⟩ : syracuseStep 2245731 = 3368597) B3368597
theorem B5395853 : Blo 2245435 5395853 := bbase (se 3 (by rfl) ⟨1011722, by rfl⟩ : syracuseStep 5395853 = 2023445) (by norm_num)
theorem B14388941 : Blo 2245435 14388941 := bstep (se 3 (by rfl) ⟨2697926, by rfl⟩ : syracuseStep 14388941 = 5395853) B5395853
theorem B9592627 : Blo 2245435 9592627 := bstep (se 1 (by rfl) ⟨7194470, by rfl⟩ : syracuseStep 9592627 = 14388941) B14388941
theorem B12790169 : Blo 2245435 12790169 := bstep (se 2 (by rfl) ⟨4796313, by rfl⟩ : syracuseStep 12790169 = 9592627) B9592627
theorem B8526779 : Blo 2245435 8526779 := bstep (se 1 (by rfl) ⟨6395084, by rfl⟩ : syracuseStep 8526779 = 12790169) B12790169
theorem B5684519 : Blo 2245435 5684519 := bstep (se 1 (by rfl) ⟨4263389, by rfl⟩ : syracuseStep 5684519 = 8526779) B8526779
theorem B3789679 : Blo 2245435 3789679 := bstep (se 1 (by rfl) ⟨2842259, by rfl⟩ : syracuseStep 3789679 = 5684519) B5684519
theorem B5052905 : Blo 2245435 5052905 := bstep (se 2 (by rfl) ⟨1894839, by rfl⟩ : syracuseStep 5052905 = 3789679) B3789679
theorem B3368603 : Blo 2245435 3368603 := bstep (se 1 (by rfl) ⟨2526452, by rfl⟩ : syracuseStep 3368603 = 5052905) B5052905
theorem B2245735 : Blo 2245435 2245735 := bstep (se 1 (by rfl) ⟨1684301, by rfl⟩ : syracuseStep 2245735 = 3368603) B3368603
theorem B2526457 : Blo 2245435 2526457 := bbase (se 2 (by rfl) ⟨947421, by rfl⟩ : syracuseStep 2526457 = 1894843) (by norm_num)
theorem B3368609 : Blo 2245435 3368609 := bstep (se 2 (by rfl) ⟨1263228, by rfl⟩ : syracuseStep 3368609 = 2526457) B2526457
theorem B2245739 : Blo 2245435 2245739 := bstep (se 1 (by rfl) ⟨1684304, by rfl⟩ : syracuseStep 2245739 = 3368609) B3368609
theorem B9592661 : Blo 2245435 9592661 := bbase (se 9 (by rfl) ⟨28103, by rfl⟩ : syracuseStep 9592661 = 56207) (by norm_num)
theorem B6395107 : Blo 2245435 6395107 := bstep (se 1 (by rfl) ⟨4796330, by rfl⟩ : syracuseStep 6395107 = 9592661) B9592661
theorem B8526809 : Blo 2245435 8526809 := bstep (se 2 (by rfl) ⟨3197553, by rfl⟩ : syracuseStep 8526809 = 6395107) B6395107
theorem B5684539 : Blo 2245435 5684539 := bstep (se 1 (by rfl) ⟨4263404, by rfl⟩ : syracuseStep 5684539 = 8526809) B8526809
theorem B7579385 : Blo 2245435 7579385 := bstep (se 2 (by rfl) ⟨2842269, by rfl⟩ : syracuseStep 7579385 = 5684539) B5684539
theorem B5052923 : Blo 2245435 5052923 := bstep (se 1 (by rfl) ⟨3789692, by rfl⟩ : syracuseStep 5052923 = 7579385) B7579385
theorem B3368615 : Blo 2245435 3368615 := bstep (se 1 (by rfl) ⟨2526461, by rfl⟩ : syracuseStep 3368615 = 5052923) B5052923
theorem B2245743 : Blo 2245435 2245743 := bstep (se 1 (by rfl) ⟨1684307, by rfl⟩ : syracuseStep 2245743 = 3368615) B3368615
theorem B3368621 : Blo 2245435 3368621 := bbase (se 3 (by rfl) ⟨631616, by rfl⟩ : syracuseStep 3368621 = 1263233) (by norm_num)
theorem B2245747 : Blo 2245435 2245747 := bstep (se 1 (by rfl) ⟨1684310, by rfl⟩ : syracuseStep 2245747 = 3368621) B3368621
theorem B5052941 : Blo 2245435 5052941 := bbase (se 3 (by rfl) ⟨947426, by rfl⟩ : syracuseStep 5052941 = 1894853) (by norm_num)
theorem B3368627 : Blo 2245435 3368627 := bstep (se 1 (by rfl) ⟨2526470, by rfl⟩ : syracuseStep 3368627 = 5052941) B5052941
theorem B2245751 : Blo 2245435 2245751 := bstep (se 1 (by rfl) ⟨1684313, by rfl⟩ : syracuseStep 2245751 = 3368627) B3368627
theorem B2842285 : Blo 2245435 2842285 := bbase (se 3 (by rfl) ⟨532928, by rfl⟩ : syracuseStep 2842285 = 1065857) (by norm_num)
theorem B3789713 : Blo 2245435 3789713 := bstep (se 2 (by rfl) ⟨1421142, by rfl⟩ : syracuseStep 3789713 = 2842285) B2842285
theorem B2526475 : Blo 2245435 2526475 := bstep (se 1 (by rfl) ⟨1894856, by rfl⟩ : syracuseStep 2526475 = 3789713) B3789713
theorem B3368633 : Blo 2245435 3368633 := bstep (se 2 (by rfl) ⟨1263237, by rfl⟩ : syracuseStep 3368633 = 2526475) B2526475
theorem B2245755 : Blo 2245435 2245755 := bstep (se 1 (by rfl) ⟨1684316, by rfl⟩ : syracuseStep 2245755 = 3368633) B3368633
theorem B4046933 : Blo 2245435 4046933 := bbase (se 8 (by rfl) ⟨23712, by rfl⟩ : syracuseStep 4046933 = 47425) (by norm_num)
theorem B2697955 : Blo 2245435 2697955 := bstep (se 1 (by rfl) ⟨2023466, by rfl⟩ : syracuseStep 2697955 = 4046933) B4046933
theorem B14389093 : Blo 2245435 14389093 := bstep (se 4 (by rfl) ⟨1348977, by rfl⟩ : syracuseStep 14389093 = 2697955) B2697955
theorem B19185457 : Blo 2245435 19185457 := bstep (se 2 (by rfl) ⟨7194546, by rfl⟩ : syracuseStep 19185457 = 14389093) B14389093
theorem B25580609 : Blo 2245435 25580609 := bstep (se 2 (by rfl) ⟨9592728, by rfl⟩ : syracuseStep 25580609 = 19185457) B19185457
theorem B17053739 : Blo 2245435 17053739 := bstep (se 1 (by rfl) ⟨12790304, by rfl⟩ : syracuseStep 17053739 = 25580609) B25580609
theorem B11369159 : Blo 2245435 11369159 := bstep (se 1 (by rfl) ⟨8526869, by rfl⟩ : syracuseStep 11369159 = 17053739) B17053739
theorem B7579439 : Blo 2245435 7579439 := bstep (se 1 (by rfl) ⟨5684579, by rfl⟩ : syracuseStep 7579439 = 11369159) B11369159
theorem B5052959 : Blo 2245435 5052959 := bstep (se 1 (by rfl) ⟨3789719, by rfl⟩ : syracuseStep 5052959 = 7579439) B7579439
theorem B3368639 : Blo 2245435 3368639 := bstep (se 1 (by rfl) ⟨2526479, by rfl⟩ : syracuseStep 3368639 = 5052959) B5052959
theorem B2245759 : Blo 2245435 2245759 := bstep (se 1 (by rfl) ⟨1684319, by rfl⟩ : syracuseStep 2245759 = 3368639) B3368639
theorem B3368645 : Blo 2245435 3368645 := bbase (se 4 (by rfl) ⟨315810, by rfl⟩ : syracuseStep 3368645 = 631621) (by norm_num)
theorem B2245763 : Blo 2245435 2245763 := bstep (se 1 (by rfl) ⟨1684322, by rfl⟩ : syracuseStep 2245763 = 3368645) B3368645
theorem B3789733 : Blo 2245435 3789733 := bbase (se 4 (by rfl) ⟨355287, by rfl⟩ : syracuseStep 3789733 = 710575) (by norm_num)
theorem B5052977 : Blo 2245435 5052977 := bstep (se 2 (by rfl) ⟨1894866, by rfl⟩ : syracuseStep 5052977 = 3789733) B3789733
theorem B3368651 : Blo 2245435 3368651 := bstep (se 1 (by rfl) ⟨2526488, by rfl⟩ : syracuseStep 3368651 = 5052977) B5052977
theorem B2245767 : Blo 2245435 2245767 := bstep (se 1 (by rfl) ⟨1684325, by rfl⟩ : syracuseStep 2245767 = 3368651) B3368651
theorem B2526493 : Blo 2245435 2526493 := bbase (se 3 (by rfl) ⟨473717, by rfl⟩ : syracuseStep 2526493 = 947435) (by norm_num)
theorem B3368657 : Blo 2245435 3368657 := bstep (se 2 (by rfl) ⟨1263246, by rfl⟩ : syracuseStep 3368657 = 2526493) B2526493
theorem B2245771 : Blo 2245435 2245771 := bstep (se 1 (by rfl) ⟨1684328, by rfl⟩ : syracuseStep 2245771 = 3368657) B3368657
theorem B7579493 : Blo 2245435 7579493 := bbase (se 4 (by rfl) ⟨710577, by rfl⟩ : syracuseStep 7579493 = 1421155) (by norm_num)
theorem B5052995 : Blo 2245435 5052995 := bstep (se 1 (by rfl) ⟨3789746, by rfl⟩ : syracuseStep 5052995 = 7579493) B7579493
theorem B3368663 : Blo 2245435 3368663 := bstep (se 1 (by rfl) ⟨2526497, by rfl⟩ : syracuseStep 3368663 = 5052995) B5052995
theorem B2245775 : Blo 2245435 2245775 := bstep (se 1 (by rfl) ⟨1684331, by rfl⟩ : syracuseStep 2245775 = 3368663) B3368663
theorem B3368669 : Blo 2245435 3368669 := bbase (se 3 (by rfl) ⟨631625, by rfl⟩ : syracuseStep 3368669 = 1263251) (by norm_num)
theorem B2245779 : Blo 2245435 2245779 := bstep (se 1 (by rfl) ⟨1684334, by rfl⟩ : syracuseStep 2245779 = 3368669) B3368669
theorem B5053013 : Blo 2245435 5053013 := bbase (se 8 (by rfl) ⟨29607, by rfl⟩ : syracuseStep 5053013 = 59215) (by norm_num)
theorem B3368675 : Blo 2245435 3368675 := bstep (se 1 (by rfl) ⟨2526506, by rfl⟩ : syracuseStep 3368675 = 5053013) B5053013
theorem B2245783 : Blo 2245435 2245783 := bstep (se 1 (by rfl) ⟨1684337, by rfl⟩ : syracuseStep 2245783 = 3368675) B3368675
theorem B2276429 : Blo 2245435 2276429 := bbase (se 3 (by rfl) ⟨426830, by rfl⟩ : syracuseStep 2276429 = 853661) (by norm_num)
theorem B6070477 : Blo 2245435 6070477 := bstep (se 3 (by rfl) ⟨1138214, by rfl⟩ : syracuseStep 6070477 = 2276429) B2276429
theorem B8093969 : Blo 2245435 8093969 := bstep (se 2 (by rfl) ⟨3035238, by rfl⟩ : syracuseStep 8093969 = 6070477) B6070477
theorem B5395979 : Blo 2245435 5395979 := bstep (se 1 (by rfl) ⟨4046984, by rfl⟩ : syracuseStep 5395979 = 8093969) B8093969
theorem B3597319 : Blo 2245435 3597319 := bstep (se 1 (by rfl) ⟨2697989, by rfl⟩ : syracuseStep 3597319 = 5395979) B5395979
theorem B4796425 : Blo 2245435 4796425 := bstep (se 2 (by rfl) ⟨1798659, by rfl⟩ : syracuseStep 4796425 = 3597319) B3597319
theorem B6395233 : Blo 2245435 6395233 := bstep (se 2 (by rfl) ⟨2398212, by rfl⟩ : syracuseStep 6395233 = 4796425) B4796425
theorem B8526977 : Blo 2245435 8526977 := bstep (se 2 (by rfl) ⟨3197616, by rfl⟩ : syracuseStep 8526977 = 6395233) B6395233
theorem B5684651 : Blo 2245435 5684651 := bstep (se 1 (by rfl) ⟨4263488, by rfl⟩ : syracuseStep 5684651 = 8526977) B8526977
theorem B3789767 : Blo 2245435 3789767 := bstep (se 1 (by rfl) ⟨2842325, by rfl⟩ : syracuseStep 3789767 = 5684651) B5684651
theorem B2526511 : Blo 2245435 2526511 := bstep (se 1 (by rfl) ⟨1894883, by rfl⟩ : syracuseStep 2526511 = 3789767) B3789767
theorem B3368681 : Blo 2245435 3368681 := bstep (se 2 (by rfl) ⟨1263255, by rfl⟩ : syracuseStep 3368681 = 2526511) B2526511
theorem B2245787 : Blo 2245435 2245787 := bstep (se 1 (by rfl) ⟨1684340, by rfl⟩ : syracuseStep 2245787 = 3368681) B3368681
theorem B6482501 : Blo 2245435 6482501 := bbase (se 4 (by rfl) ⟨607734, by rfl⟩ : syracuseStep 6482501 = 1215469) (by norm_num)
theorem B4321667 : Blo 2245435 4321667 := bstep (se 1 (by rfl) ⟨3241250, by rfl⟩ : syracuseStep 4321667 = 6482501) B6482501
theorem B2881111 : Blo 2245435 2881111 := bstep (se 1 (by rfl) ⟨2160833, by rfl⟩ : syracuseStep 2881111 = 4321667) B4321667
theorem B3841481 : Blo 2245435 3841481 := bstep (se 2 (by rfl) ⟨1440555, by rfl⟩ : syracuseStep 3841481 = 2881111) B2881111
theorem B2560987 : Blo 2245435 2560987 := bstep (se 1 (by rfl) ⟨1920740, by rfl⟩ : syracuseStep 2560987 = 3841481) B3841481
theorem B3414649 : Blo 2245435 3414649 := bstep (se 2 (by rfl) ⟨1280493, by rfl⟩ : syracuseStep 3414649 = 2560987) B2560987
theorem B4552865 : Blo 2245435 4552865 := bstep (se 2 (by rfl) ⟨1707324, by rfl⟩ : syracuseStep 4552865 = 3414649) B3414649
theorem B3035243 : Blo 2245435 3035243 := bstep (se 1 (by rfl) ⟨2276432, by rfl⟩ : syracuseStep 3035243 = 4552865) B4552865
theorem B8093981 : Blo 2245435 8093981 := bstep (se 3 (by rfl) ⟨1517621, by rfl⟩ : syracuseStep 8093981 = 3035243) B3035243
theorem B5395987 : Blo 2245435 5395987 := bstep (se 1 (by rfl) ⟨4046990, by rfl⟩ : syracuseStep 5395987 = 8093981) B8093981
theorem B28778597 : Blo 2245435 28778597 := bstep (se 4 (by rfl) ⟨2697993, by rfl⟩ : syracuseStep 28778597 = 5395987) B5395987
theorem B19185731 : Blo 2245435 19185731 := bstep (se 1 (by rfl) ⟨14389298, by rfl⟩ : syracuseStep 19185731 = 28778597) B28778597
theorem B12790487 : Blo 2245435 12790487 := bstep (se 1 (by rfl) ⟨9592865, by rfl⟩ : syracuseStep 12790487 = 19185731) B19185731
theorem B8526991 : Blo 2245435 8526991 := bstep (se 1 (by rfl) ⟨6395243, by rfl⟩ : syracuseStep 8526991 = 12790487) B12790487
theorem B11369321 : Blo 2245435 11369321 := bstep (se 2 (by rfl) ⟨4263495, by rfl⟩ : syracuseStep 11369321 = 8526991) B8526991
theorem B7579547 : Blo 2245435 7579547 := bstep (se 1 (by rfl) ⟨5684660, by rfl⟩ : syracuseStep 7579547 = 11369321) B11369321
theorem B5053031 : Blo 2245435 5053031 := bstep (se 1 (by rfl) ⟨3789773, by rfl⟩ : syracuseStep 5053031 = 7579547) B7579547
theorem B3368687 : Blo 2245435 3368687 := bstep (se 1 (by rfl) ⟨2526515, by rfl⟩ : syracuseStep 3368687 = 5053031) B5053031
theorem B2245791 : Blo 2245435 2245791 := bstep (se 1 (by rfl) ⟨1684343, by rfl⟩ : syracuseStep 2245791 = 3368687) B3368687
theorem B3368693 : Blo 2245435 3368693 := bbase (se 5 (by rfl) ⟨157907, by rfl⟩ : syracuseStep 3368693 = 315815) (by norm_num)
theorem B2245795 : Blo 2245435 2245795 := bstep (se 1 (by rfl) ⟨1684346, by rfl⟩ : syracuseStep 2245795 = 3368693) B3368693
theorem B9592901 : Blo 2245435 9592901 := bbase (se 4 (by rfl) ⟨899334, by rfl⟩ : syracuseStep 9592901 = 1798669) (by norm_num)
theorem B6395267 : Blo 2245435 6395267 := bstep (se 1 (by rfl) ⟨4796450, by rfl⟩ : syracuseStep 6395267 = 9592901) B9592901
theorem B4263511 : Blo 2245435 4263511 := bstep (se 1 (by rfl) ⟨3197633, by rfl⟩ : syracuseStep 4263511 = 6395267) B6395267
theorem B5684681 : Blo 2245435 5684681 := bstep (se 2 (by rfl) ⟨2131755, by rfl⟩ : syracuseStep 5684681 = 4263511) B4263511
theorem B3789787 : Blo 2245435 3789787 := bstep (se 1 (by rfl) ⟨2842340, by rfl⟩ : syracuseStep 3789787 = 5684681) B5684681
theorem B5053049 : Blo 2245435 5053049 := bstep (se 2 (by rfl) ⟨1894893, by rfl⟩ : syracuseStep 5053049 = 3789787) B3789787
theorem B3368699 : Blo 2245435 3368699 := bstep (se 1 (by rfl) ⟨2526524, by rfl⟩ : syracuseStep 3368699 = 5053049) B5053049
theorem B2245799 : Blo 2245435 2245799 := bstep (se 1 (by rfl) ⟨1684349, by rfl⟩ : syracuseStep 2245799 = 3368699) B3368699
theorem B2526529 : Blo 2245435 2526529 := bbase (se 2 (by rfl) ⟨947448, by rfl⟩ : syracuseStep 2526529 = 1894897) (by norm_num)
theorem B3368705 : Blo 2245435 3368705 := bstep (se 2 (by rfl) ⟨1263264, by rfl⟩ : syracuseStep 3368705 = 2526529) B2526529
theorem B2245803 : Blo 2245435 2245803 := bstep (se 1 (by rfl) ⟨1684352, by rfl⟩ : syracuseStep 2245803 = 3368705) B3368705
theorem B5684701 : Blo 2245435 5684701 := bbase (se 3 (by rfl) ⟨1065881, by rfl⟩ : syracuseStep 5684701 = 2131763) (by norm_num)
theorem B7579601 : Blo 2245435 7579601 := bstep (se 2 (by rfl) ⟨2842350, by rfl⟩ : syracuseStep 7579601 = 5684701) B5684701
theorem B5053067 : Blo 2245435 5053067 := bstep (se 1 (by rfl) ⟨3789800, by rfl⟩ : syracuseStep 5053067 = 7579601) B7579601
theorem B3368711 : Blo 2245435 3368711 := bstep (se 1 (by rfl) ⟨2526533, by rfl⟩ : syracuseStep 3368711 = 5053067) B5053067
theorem B2245807 : Blo 2245435 2245807 := bstep (se 1 (by rfl) ⟨1684355, by rfl⟩ : syracuseStep 2245807 = 3368711) B3368711
theorem B3368717 : Blo 2245435 3368717 := bbase (se 3 (by rfl) ⟨631634, by rfl⟩ : syracuseStep 3368717 = 1263269) (by norm_num)
theorem B2245811 : Blo 2245435 2245811 := bstep (se 1 (by rfl) ⟨1684358, by rfl⟩ : syracuseStep 2245811 = 3368717) B3368717
theorem B5053085 : Blo 2245435 5053085 := bbase (se 3 (by rfl) ⟨947453, by rfl⟩ : syracuseStep 5053085 = 1894907) (by norm_num)
theorem B3368723 : Blo 2245435 3368723 := bstep (se 1 (by rfl) ⟨2526542, by rfl⟩ : syracuseStep 3368723 = 5053085) B5053085
theorem B2245815 : Blo 2245435 2245815 := bstep (se 1 (by rfl) ⟨1684361, by rfl⟩ : syracuseStep 2245815 = 3368723) B3368723
theorem B3789821 : Blo 2245435 3789821 := bbase (se 3 (by rfl) ⟨710591, by rfl⟩ : syracuseStep 3789821 = 1421183) (by norm_num)
theorem B2526547 : Blo 2245435 2526547 := bstep (se 1 (by rfl) ⟨1894910, by rfl⟩ : syracuseStep 2526547 = 3789821) B3789821
theorem B3368729 : Blo 2245435 3368729 := bstep (se 2 (by rfl) ⟨1263273, by rfl⟩ : syracuseStep 3368729 = 2526547) B2526547
theorem B2245819 : Blo 2245435 2245819 := bstep (se 1 (by rfl) ⟨1684364, by rfl⟩ : syracuseStep 2245819 = 3368729) B3368729
theorem B4796501 : Blo 2245435 4796501 := bbase (se 8 (by rfl) ⟨28104, by rfl⟩ : syracuseStep 4796501 = 56209) (by norm_num)
theorem B12790669 : Blo 2245435 12790669 := bstep (se 3 (by rfl) ⟨2398250, by rfl⟩ : syracuseStep 12790669 = 4796501) B4796501
theorem B17054225 : Blo 2245435 17054225 := bstep (se 2 (by rfl) ⟨6395334, by rfl⟩ : syracuseStep 17054225 = 12790669) B12790669
theorem B11369483 : Blo 2245435 11369483 := bstep (se 1 (by rfl) ⟨8527112, by rfl⟩ : syracuseStep 11369483 = 17054225) B17054225
theorem B7579655 : Blo 2245435 7579655 := bstep (se 1 (by rfl) ⟨5684741, by rfl⟩ : syracuseStep 7579655 = 11369483) B11369483
theorem B5053103 : Blo 2245435 5053103 := bstep (se 1 (by rfl) ⟨3789827, by rfl⟩ : syracuseStep 5053103 = 7579655) B7579655
theorem B3368735 : Blo 2245435 3368735 := bstep (se 1 (by rfl) ⟨2526551, by rfl⟩ : syracuseStep 3368735 = 5053103) B5053103
theorem B2245823 : Blo 2245435 2245823 := bstep (se 1 (by rfl) ⟨1684367, by rfl⟩ : syracuseStep 2245823 = 3368735) B3368735
theorem B3368741 : Blo 2245435 3368741 := bbase (se 4 (by rfl) ⟨315819, by rfl⟩ : syracuseStep 3368741 = 631639) (by norm_num)
theorem B2245827 : Blo 2245435 2245827 := bstep (se 1 (by rfl) ⟨1684370, by rfl⟩ : syracuseStep 2245827 = 3368741) B3368741
theorem B2842381 : Blo 2245435 2842381 := bbase (se 3 (by rfl) ⟨532946, by rfl⟩ : syracuseStep 2842381 = 1065893) (by norm_num)
theorem B3789841 : Blo 2245435 3789841 := bstep (se 2 (by rfl) ⟨1421190, by rfl⟩ : syracuseStep 3789841 = 2842381) B2842381
theorem B5053121 : Blo 2245435 5053121 := bstep (se 2 (by rfl) ⟨1894920, by rfl⟩ : syracuseStep 5053121 = 3789841) B3789841
theorem B3368747 : Blo 2245435 3368747 := bstep (se 1 (by rfl) ⟨2526560, by rfl⟩ : syracuseStep 3368747 = 5053121) B5053121
theorem B2245831 : Blo 2245435 2245831 := bstep (se 1 (by rfl) ⟨1684373, by rfl⟩ : syracuseStep 2245831 = 3368747) B3368747
theorem B2526565 : Blo 2245435 2526565 := bbase (se 4 (by rfl) ⟨236865, by rfl⟩ : syracuseStep 2526565 = 473731) (by norm_num)
theorem B3368753 : Blo 2245435 3368753 := bstep (se 2 (by rfl) ⟨1263282, by rfl⟩ : syracuseStep 3368753 = 2526565) B2526565
theorem B2245835 : Blo 2245435 2245835 := bstep (se 1 (by rfl) ⟨1684376, by rfl⟩ : syracuseStep 2245835 = 3368753) B3368753
theorem B6395381 : Blo 2245435 6395381 := bbase (se 5 (by rfl) ⟨299783, by rfl⟩ : syracuseStep 6395381 = 599567) (by norm_num)
theorem B4263587 : Blo 2245435 4263587 := bstep (se 1 (by rfl) ⟨3197690, by rfl⟩ : syracuseStep 4263587 = 6395381) B6395381
theorem B2842391 : Blo 2245435 2842391 := bstep (se 1 (by rfl) ⟨2131793, by rfl⟩ : syracuseStep 2842391 = 4263587) B4263587
theorem B7579709 : Blo 2245435 7579709 := bstep (se 3 (by rfl) ⟨1421195, by rfl⟩ : syracuseStep 7579709 = 2842391) B2842391
theorem B5053139 : Blo 2245435 5053139 := bstep (se 1 (by rfl) ⟨3789854, by rfl⟩ : syracuseStep 5053139 = 7579709) B7579709
theorem B3368759 : Blo 2245435 3368759 := bstep (se 1 (by rfl) ⟨2526569, by rfl⟩ : syracuseStep 3368759 = 5053139) B5053139
theorem B2245839 : Blo 2245435 2245839 := bstep (se 1 (by rfl) ⟨1684379, by rfl⟩ : syracuseStep 2245839 = 3368759) B3368759
theorem B3368765 : Blo 2245435 3368765 := bbase (se 3 (by rfl) ⟨631643, by rfl⟩ : syracuseStep 3368765 = 1263287) (by norm_num)
theorem B2245843 : Blo 2245435 2245843 := bstep (se 1 (by rfl) ⟨1684382, by rfl⟩ : syracuseStep 2245843 = 3368765) B3368765
theorem B5053157 : Blo 2245435 5053157 := bbase (se 4 (by rfl) ⟨473733, by rfl⟩ : syracuseStep 5053157 = 947467) (by norm_num)
theorem B3368771 : Blo 2245435 3368771 := bstep (se 1 (by rfl) ⟨2526578, by rfl⟩ : syracuseStep 3368771 = 5053157) B5053157
theorem B2245847 : Blo 2245435 2245847 := bstep (se 1 (by rfl) ⟨1684385, by rfl⟩ : syracuseStep 2245847 = 3368771) B3368771
theorem B5684813 : Blo 2245435 5684813 := bbase (se 3 (by rfl) ⟨1065902, by rfl⟩ : syracuseStep 5684813 = 2131805) (by norm_num)
theorem B3789875 : Blo 2245435 3789875 := bstep (se 1 (by rfl) ⟨2842406, by rfl⟩ : syracuseStep 3789875 = 5684813) B5684813
theorem B2526583 : Blo 2245435 2526583 := bstep (se 1 (by rfl) ⟨1894937, by rfl⟩ : syracuseStep 2526583 = 3789875) B3789875
theorem B3368777 : Blo 2245435 3368777 := bstep (se 2 (by rfl) ⟨1263291, by rfl⟩ : syracuseStep 3368777 = 2526583) B2526583
theorem B2245851 : Blo 2245435 2245851 := bstep (se 1 (by rfl) ⟨1684388, by rfl⟩ : syracuseStep 2245851 = 3368777) B3368777
theorem B2398285 : Blo 2245435 2398285 := bbase (se 3 (by rfl) ⟨449678, by rfl⟩ : syracuseStep 2398285 = 899357) (by norm_num)
theorem B3197713 : Blo 2245435 3197713 := bstep (se 2 (by rfl) ⟨1199142, by rfl⟩ : syracuseStep 3197713 = 2398285) B2398285
theorem B4263617 : Blo 2245435 4263617 := bstep (se 2 (by rfl) ⟨1598856, by rfl⟩ : syracuseStep 4263617 = 3197713) B3197713
theorem B11369645 : Blo 2245435 11369645 := bstep (se 3 (by rfl) ⟨2131808, by rfl⟩ : syracuseStep 11369645 = 4263617) B4263617
theorem B7579763 : Blo 2245435 7579763 := bstep (se 1 (by rfl) ⟨5684822, by rfl⟩ : syracuseStep 7579763 = 11369645) B11369645
theorem B5053175 : Blo 2245435 5053175 := bstep (se 1 (by rfl) ⟨3789881, by rfl⟩ : syracuseStep 5053175 = 7579763) B7579763
theorem B3368783 : Blo 2245435 3368783 := bstep (se 1 (by rfl) ⟨2526587, by rfl⟩ : syracuseStep 3368783 = 5053175) B5053175
theorem B2245855 : Blo 2245435 2245855 := bstep (se 1 (by rfl) ⟨1684391, by rfl⟩ : syracuseStep 2245855 = 3368783) B3368783
theorem B3368789 : Blo 2245435 3368789 := bbase (se 9 (by rfl) ⟨9869, by rfl⟩ : syracuseStep 3368789 = 19739) (by norm_num)
theorem B2245859 : Blo 2245435 2245859 := bstep (se 1 (by rfl) ⟨1684394, by rfl⟩ : syracuseStep 2245859 = 3368789) B3368789
theorem B3035341 : Blo 2245435 3035341 := bbase (se 3 (by rfl) ⟨569126, by rfl⟩ : syracuseStep 3035341 = 1138253) (by norm_num)
theorem B4047121 : Blo 2245435 4047121 := bstep (se 2 (by rfl) ⟨1517670, by rfl⟩ : syracuseStep 4047121 = 3035341) B3035341
theorem B5396161 : Blo 2245435 5396161 := bstep (se 2 (by rfl) ⟨2023560, by rfl⟩ : syracuseStep 5396161 = 4047121) B4047121
theorem B7194881 : Blo 2245435 7194881 := bstep (se 2 (by rfl) ⟨2698080, by rfl⟩ : syracuseStep 7194881 = 5396161) B5396161
theorem B4796587 : Blo 2245435 4796587 := bstep (se 1 (by rfl) ⟨3597440, by rfl⟩ : syracuseStep 4796587 = 7194881) B7194881
theorem B6395449 : Blo 2245435 6395449 := bstep (se 2 (by rfl) ⟨2398293, by rfl⟩ : syracuseStep 6395449 = 4796587) B4796587
theorem B8527265 : Blo 2245435 8527265 := bstep (se 2 (by rfl) ⟨3197724, by rfl⟩ : syracuseStep 8527265 = 6395449) B6395449
theorem B5684843 : Blo 2245435 5684843 := bstep (se 1 (by rfl) ⟨4263632, by rfl⟩ : syracuseStep 5684843 = 8527265) B8527265
theorem B3789895 : Blo 2245435 3789895 := bstep (se 1 (by rfl) ⟨2842421, by rfl⟩ : syracuseStep 3789895 = 5684843) B5684843
theorem B5053193 : Blo 2245435 5053193 := bstep (se 2 (by rfl) ⟨1894947, by rfl⟩ : syracuseStep 5053193 = 3789895) B3789895
theorem B3368795 : Blo 2245435 3368795 := bstep (se 1 (by rfl) ⟨2526596, by rfl⟩ : syracuseStep 3368795 = 5053193) B5053193
theorem B2245863 : Blo 2245435 2245863 := bstep (se 1 (by rfl) ⟨1684397, by rfl⟩ : syracuseStep 2245863 = 3368795) B3368795
theorem B2526601 : Blo 2245435 2526601 := bbase (se 2 (by rfl) ⟨947475, by rfl⟩ : syracuseStep 2526601 = 1894951) (by norm_num)
theorem B3368801 : Blo 2245435 3368801 := bstep (se 2 (by rfl) ⟨1263300, by rfl⟩ : syracuseStep 3368801 = 2526601) B2526601
theorem B2245867 : Blo 2245435 2245867 := bstep (se 1 (by rfl) ⟨1684400, by rfl⟩ : syracuseStep 2245867 = 3368801) B3368801
theorem B5262877 : Blo 2245435 5262877 := bbase (se 3 (by rfl) ⟨986789, by rfl⟩ : syracuseStep 5262877 = 1973579) (by norm_num)
theorem B28068677 : Blo 2245435 28068677 := bstep (se 4 (by rfl) ⟨2631438, by rfl⟩ : syracuseStep 28068677 = 5262877) B5262877
theorem B18712451 : Blo 2245435 18712451 := bstep (se 1 (by rfl) ⟨14034338, by rfl⟩ : syracuseStep 18712451 = 28068677) B28068677
theorem B12474967 : Blo 2245435 12474967 := bstep (se 1 (by rfl) ⟨9356225, by rfl⟩ : syracuseStep 12474967 = 18712451) B18712451
theorem B16633289 : Blo 2245435 16633289 := bstep (se 2 (by rfl) ⟨6237483, by rfl⟩ : syracuseStep 16633289 = 12474967) B12474967
theorem B44355437 : Blo 2245435 44355437 := bstep (se 3 (by rfl) ⟨8316644, by rfl⟩ : syracuseStep 44355437 = 16633289) B16633289
theorem B29570291 : Blo 2245435 29570291 := bstep (se 1 (by rfl) ⟨22177718, by rfl⟩ : syracuseStep 29570291 = 44355437) B44355437
theorem B19713527 : Blo 2245435 19713527 := bstep (se 1 (by rfl) ⟨14785145, by rfl⟩ : syracuseStep 19713527 = 29570291) B29570291
theorem B13142351 : Blo 2245435 13142351 := bstep (se 1 (by rfl) ⟨9856763, by rfl⟩ : syracuseStep 13142351 = 19713527) B19713527
theorem B8761567 : Blo 2245435 8761567 := bstep (se 1 (by rfl) ⟨6571175, by rfl⟩ : syracuseStep 8761567 = 13142351) B13142351
theorem B11682089 : Blo 2245435 11682089 := bstep (se 2 (by rfl) ⟨4380783, by rfl⟩ : syracuseStep 11682089 = 8761567) B8761567
theorem B7788059 : Blo 2245435 7788059 := bstep (se 1 (by rfl) ⟨5841044, by rfl⟩ : syracuseStep 7788059 = 11682089) B11682089
theorem B5192039 : Blo 2245435 5192039 := bstep (se 1 (by rfl) ⟨3894029, by rfl⟩ : syracuseStep 5192039 = 7788059) B7788059
theorem B13845437 : Blo 2245435 13845437 := bstep (se 3 (by rfl) ⟨2596019, by rfl⟩ : syracuseStep 13845437 = 5192039) B5192039
theorem B9230291 : Blo 2245435 9230291 := bstep (se 1 (by rfl) ⟨6922718, by rfl⟩ : syracuseStep 9230291 = 13845437) B13845437
theorem B6153527 : Blo 2245435 6153527 := bstep (se 1 (by rfl) ⟨4615145, by rfl⟩ : syracuseStep 6153527 = 9230291) B9230291
theorem B16409405 : Blo 2245435 16409405 := bstep (se 3 (by rfl) ⟨3076763, by rfl⟩ : syracuseStep 16409405 = 6153527) B6153527
theorem B10939603 : Blo 2245435 10939603 := bstep (se 1 (by rfl) ⟨8204702, by rfl⟩ : syracuseStep 10939603 = 16409405) B16409405
theorem B14586137 : Blo 2245435 14586137 := bstep (se 2 (by rfl) ⟨5469801, by rfl⟩ : syracuseStep 14586137 = 10939603) B10939603
theorem B9724091 : Blo 2245435 9724091 := bstep (se 1 (by rfl) ⟨7293068, by rfl⟩ : syracuseStep 9724091 = 14586137) B14586137
theorem B25930909 : Blo 2245435 25930909 := bstep (se 3 (by rfl) ⟨4862045, by rfl⟩ : syracuseStep 25930909 = 9724091) B9724091
theorem B34574545 : Blo 2245435 34574545 := bstep (se 2 (by rfl) ⟨12965454, by rfl⟩ : syracuseStep 34574545 = 25930909) B25930909
theorem B184397573 : Blo 2245435 184397573 := bstep (se 4 (by rfl) ⟨17287272, by rfl⟩ : syracuseStep 184397573 = 34574545) B34574545
theorem B122931715 : Blo 2245435 122931715 := bstep (se 1 (by rfl) ⟨92198786, by rfl⟩ : syracuseStep 122931715 = 184397573) B184397573
theorem B163908953 : Blo 2245435 163908953 := bstep (se 2 (by rfl) ⟨61465857, by rfl⟩ : syracuseStep 163908953 = 122931715) B122931715
theorem B109272635 : Blo 2245435 109272635 := bstep (se 1 (by rfl) ⟨81954476, by rfl⟩ : syracuseStep 109272635 = 163908953) B163908953
theorem B72848423 : Blo 2245435 72848423 := bstep (se 1 (by rfl) ⟨54636317, by rfl⟩ : syracuseStep 72848423 = 109272635) B109272635
theorem B48565615 : Blo 2245435 48565615 := bstep (se 1 (by rfl) ⟨36424211, by rfl⟩ : syracuseStep 48565615 = 72848423) B72848423
theorem B64754153 : Blo 2245435 64754153 := bstep (se 2 (by rfl) ⟨24282807, by rfl⟩ : syracuseStep 64754153 = 48565615) B48565615
theorem B43169435 : Blo 2245435 43169435 := bstep (se 1 (by rfl) ⟨32377076, by rfl⟩ : syracuseStep 43169435 = 64754153) B64754153
theorem B28779623 : Blo 2245435 28779623 := bstep (se 1 (by rfl) ⟨21584717, by rfl⟩ : syracuseStep 28779623 = 43169435) B43169435
theorem B19186415 : Blo 2245435 19186415 := bstep (se 1 (by rfl) ⟨14389811, by rfl⟩ : syracuseStep 19186415 = 28779623) B28779623
theorem B12790943 : Blo 2245435 12790943 := bstep (se 1 (by rfl) ⟨9593207, by rfl⟩ : syracuseStep 12790943 = 19186415) B19186415
theorem B8527295 : Blo 2245435 8527295 := bstep (se 1 (by rfl) ⟨6395471, by rfl⟩ : syracuseStep 8527295 = 12790943) B12790943
theorem B5684863 : Blo 2245435 5684863 := bstep (se 1 (by rfl) ⟨4263647, by rfl⟩ : syracuseStep 5684863 = 8527295) B8527295
theorem B7579817 : Blo 2245435 7579817 := bstep (se 2 (by rfl) ⟨2842431, by rfl⟩ : syracuseStep 7579817 = 5684863) B5684863
theorem B5053211 : Blo 2245435 5053211 := bstep (se 1 (by rfl) ⟨3789908, by rfl⟩ : syracuseStep 5053211 = 7579817) B7579817
theorem B3368807 : Blo 2245435 3368807 := bstep (se 1 (by rfl) ⟨2526605, by rfl⟩ : syracuseStep 3368807 = 5053211) B5053211
theorem B2245871 : Blo 2245435 2245871 := bstep (se 1 (by rfl) ⟨1684403, by rfl⟩ : syracuseStep 2245871 = 3368807) B3368807
theorem B3368813 : Blo 2245435 3368813 := bbase (se 3 (by rfl) ⟨631652, by rfl⟩ : syracuseStep 3368813 = 1263305) (by norm_num)
theorem B2245875 : Blo 2245435 2245875 := bstep (se 1 (by rfl) ⟨1684406, by rfl⟩ : syracuseStep 2245875 = 3368813) B3368813
theorem B5053229 : Blo 2245435 5053229 := bbase (se 3 (by rfl) ⟨947480, by rfl⟩ : syracuseStep 5053229 = 1894961) (by norm_num)
theorem B3368819 : Blo 2245435 3368819 := bstep (se 1 (by rfl) ⟨2526614, by rfl⟩ : syracuseStep 3368819 = 5053229) B5053229
theorem B2245879 : Blo 2245435 2245879 := bstep (se 1 (by rfl) ⟨1684409, by rfl⟩ : syracuseStep 2245879 = 3368819) B3368819
theorem B2698105 : Blo 2245435 2698105 := bbase (se 2 (by rfl) ⟨1011789, by rfl⟩ : syracuseStep 2698105 = 2023579) (by norm_num)
theorem B3597473 : Blo 2245435 3597473 := bstep (se 2 (by rfl) ⟨1349052, by rfl⟩ : syracuseStep 3597473 = 2698105) B2698105
theorem B9593261 : Blo 2245435 9593261 := bstep (se 3 (by rfl) ⟨1798736, by rfl⟩ : syracuseStep 9593261 = 3597473) B3597473
theorem B6395507 : Blo 2245435 6395507 := bstep (se 1 (by rfl) ⟨4796630, by rfl⟩ : syracuseStep 6395507 = 9593261) B9593261
theorem B4263671 : Blo 2245435 4263671 := bstep (se 1 (by rfl) ⟨3197753, by rfl⟩ : syracuseStep 4263671 = 6395507) B6395507
theorem B2842447 : Blo 2245435 2842447 := bstep (se 1 (by rfl) ⟨2131835, by rfl⟩ : syracuseStep 2842447 = 4263671) B4263671
theorem B3789929 : Blo 2245435 3789929 := bstep (se 2 (by rfl) ⟨1421223, by rfl⟩ : syracuseStep 3789929 = 2842447) B2842447
theorem B2526619 : Blo 2245435 2526619 := bstep (se 1 (by rfl) ⟨1894964, by rfl⟩ : syracuseStep 2526619 = 3789929) B3789929
theorem B3368825 : Blo 2245435 3368825 := bstep (se 2 (by rfl) ⟨1263309, by rfl⟩ : syracuseStep 3368825 = 2526619) B2526619
theorem B2245883 : Blo 2245435 2245883 := bstep (se 1 (by rfl) ⟨1684412, by rfl⟩ : syracuseStep 2245883 = 3368825) B3368825
theorem B6829589 : Blo 2245435 6829589 := bbase (se 6 (by rfl) ⟨160068, by rfl⟩ : syracuseStep 6829589 = 320137) (by norm_num)
theorem B4553059 : Blo 2245435 4553059 := bstep (se 1 (by rfl) ⟨3414794, by rfl⟩ : syracuseStep 4553059 = 6829589) B6829589
theorem B6070745 : Blo 2245435 6070745 := bstep (se 2 (by rfl) ⟨2276529, by rfl⟩ : syracuseStep 6070745 = 4553059) B4553059
theorem B16188653 : Blo 2245435 16188653 := bstep (se 3 (by rfl) ⟨3035372, by rfl⟩ : syracuseStep 16188653 = 6070745) B6070745
theorem B10792435 : Blo 2245435 10792435 := bstep (se 1 (by rfl) ⟨8094326, by rfl⟩ : syracuseStep 10792435 = 16188653) B16188653
theorem B14389913 : Blo 2245435 14389913 := bstep (se 2 (by rfl) ⟨5396217, by rfl⟩ : syracuseStep 14389913 = 10792435) B10792435
theorem B38373101 : Blo 2245435 38373101 := bstep (se 3 (by rfl) ⟨7194956, by rfl⟩ : syracuseStep 38373101 = 14389913) B14389913
theorem B25582067 : Blo 2245435 25582067 := bstep (se 1 (by rfl) ⟨19186550, by rfl⟩ : syracuseStep 25582067 = 38373101) B38373101
theorem B17054711 : Blo 2245435 17054711 := bstep (se 1 (by rfl) ⟨12791033, by rfl⟩ : syracuseStep 17054711 = 25582067) B25582067
theorem B11369807 : Blo 2245435 11369807 := bstep (se 1 (by rfl) ⟨8527355, by rfl⟩ : syracuseStep 11369807 = 17054711) B17054711
theorem B7579871 : Blo 2245435 7579871 := bstep (se 1 (by rfl) ⟨5684903, by rfl⟩ : syracuseStep 7579871 = 11369807) B11369807
theorem B5053247 : Blo 2245435 5053247 := bstep (se 1 (by rfl) ⟨3789935, by rfl⟩ : syracuseStep 5053247 = 7579871) B7579871
theorem B3368831 : Blo 2245435 3368831 := bstep (se 1 (by rfl) ⟨2526623, by rfl⟩ : syracuseStep 3368831 = 5053247) B5053247
theorem B2245887 : Blo 2245435 2245887 := bstep (se 1 (by rfl) ⟨1684415, by rfl⟩ : syracuseStep 2245887 = 3368831) B3368831
theorem B3368837 : Blo 2245435 3368837 := bbase (se 4 (by rfl) ⟨315828, by rfl⟩ : syracuseStep 3368837 = 631657) (by norm_num)
theorem B2245891 : Blo 2245435 2245891 := bstep (se 1 (by rfl) ⟨1684418, by rfl⟩ : syracuseStep 2245891 = 3368837) B3368837
theorem B3789949 : Blo 2245435 3789949 := bbase (se 3 (by rfl) ⟨710615, by rfl⟩ : syracuseStep 3789949 = 1421231) (by norm_num)
theorem B5053265 : Blo 2245435 5053265 := bstep (se 2 (by rfl) ⟨1894974, by rfl⟩ : syracuseStep 5053265 = 3789949) B3789949
theorem B3368843 : Blo 2245435 3368843 := bstep (se 1 (by rfl) ⟨2526632, by rfl⟩ : syracuseStep 3368843 = 5053265) B5053265
theorem B2245895 : Blo 2245435 2245895 := bstep (se 1 (by rfl) ⟨1684421, by rfl⟩ : syracuseStep 2245895 = 3368843) B3368843
theorem B2526637 : Blo 2245435 2526637 := bbase (se 3 (by rfl) ⟨473744, by rfl⟩ : syracuseStep 2526637 = 947489) (by norm_num)
theorem B3368849 : Blo 2245435 3368849 := bstep (se 2 (by rfl) ⟨1263318, by rfl⟩ : syracuseStep 3368849 = 2526637) B2526637
theorem B2245899 : Blo 2245435 2245899 := bstep (se 1 (by rfl) ⟨1684424, by rfl⟩ : syracuseStep 2245899 = 3368849) B3368849
theorem B7579925 : Blo 2245435 7579925 := bbase (se 6 (by rfl) ⟨177654, by rfl⟩ : syracuseStep 7579925 = 355309) (by norm_num)
theorem B5053283 : Blo 2245435 5053283 := bstep (se 1 (by rfl) ⟨3789962, by rfl⟩ : syracuseStep 5053283 = 7579925) B7579925
theorem B3368855 : Blo 2245435 3368855 := bstep (se 1 (by rfl) ⟨2526641, by rfl⟩ : syracuseStep 3368855 = 5053283) B5053283
theorem B2245903 : Blo 2245435 2245903 := bstep (se 1 (by rfl) ⟨1684427, by rfl⟩ : syracuseStep 2245903 = 3368855) B3368855
theorem B3368861 : Blo 2245435 3368861 := bbase (se 3 (by rfl) ⟨631661, by rfl⟩ : syracuseStep 3368861 = 1263323) (by norm_num)
theorem B2245907 : Blo 2245435 2245907 := bstep (se 1 (by rfl) ⟨1684430, by rfl⟩ : syracuseStep 2245907 = 3368861) B3368861
theorem B5053301 : Blo 2245435 5053301 := bbase (se 5 (by rfl) ⟨236873, by rfl⟩ : syracuseStep 5053301 = 473747) (by norm_num)
theorem B3368867 : Blo 2245435 3368867 := bstep (se 1 (by rfl) ⟨2526650, by rfl⟩ : syracuseStep 3368867 = 5053301) B5053301
theorem B2245911 : Blo 2245435 2245911 := bstep (se 1 (by rfl) ⟨1684433, by rfl⟩ : syracuseStep 2245911 = 3368867) B3368867
theorem B13659349 : Blo 2245435 13659349 := bbase (se 7 (by rfl) ⟨160070, by rfl⟩ : syracuseStep 13659349 = 320141) (by norm_num)
theorem B18212465 : Blo 2245435 18212465 := bstep (se 2 (by rfl) ⟨6829674, by rfl⟩ : syracuseStep 18212465 = 13659349) B13659349
theorem B48566573 : Blo 2245435 48566573 := bstep (se 3 (by rfl) ⟨9106232, by rfl⟩ : syracuseStep 48566573 = 18212465) B18212465
theorem B32377715 : Blo 2245435 32377715 := bstep (se 1 (by rfl) ⟨24283286, by rfl⟩ : syracuseStep 32377715 = 48566573) B48566573
theorem B21585143 : Blo 2245435 21585143 := bstep (se 1 (by rfl) ⟨16188857, by rfl⟩ : syracuseStep 21585143 = 32377715) B32377715
theorem B14390095 : Blo 2245435 14390095 := bstep (se 1 (by rfl) ⟨10792571, by rfl⟩ : syracuseStep 14390095 = 21585143) B21585143
theorem B19186793 : Blo 2245435 19186793 := bstep (se 2 (by rfl) ⟨7195047, by rfl⟩ : syracuseStep 19186793 = 14390095) B14390095
theorem B12791195 : Blo 2245435 12791195 := bstep (se 1 (by rfl) ⟨9593396, by rfl⟩ : syracuseStep 12791195 = 19186793) B19186793
theorem B8527463 : Blo 2245435 8527463 := bstep (se 1 (by rfl) ⟨6395597, by rfl⟩ : syracuseStep 8527463 = 12791195) B12791195
theorem B5684975 : Blo 2245435 5684975 := bstep (se 1 (by rfl) ⟨4263731, by rfl⟩ : syracuseStep 5684975 = 8527463) B8527463
theorem B3789983 : Blo 2245435 3789983 := bstep (se 1 (by rfl) ⟨2842487, by rfl⟩ : syracuseStep 3789983 = 5684975) B5684975
theorem B2526655 : Blo 2245435 2526655 := bstep (se 1 (by rfl) ⟨1894991, by rfl⟩ : syracuseStep 2526655 = 3789983) B3789983
theorem B3368873 : Blo 2245435 3368873 := bstep (se 2 (by rfl) ⟨1263327, by rfl⟩ : syracuseStep 3368873 = 2526655) B2526655
theorem B2245915 : Blo 2245435 2245915 := bstep (se 1 (by rfl) ⟨1684436, by rfl⟩ : syracuseStep 2245915 = 3368873) B3368873
theorem B8527477 : Blo 2245435 8527477 := bbase (se 5 (by rfl) ⟨399725, by rfl⟩ : syracuseStep 8527477 = 799451) (by norm_num)
theorem B11369969 : Blo 2245435 11369969 := bstep (se 2 (by rfl) ⟨4263738, by rfl⟩ : syracuseStep 11369969 = 8527477) B8527477
theorem B7579979 : Blo 2245435 7579979 := bstep (se 1 (by rfl) ⟨5684984, by rfl⟩ : syracuseStep 7579979 = 11369969) B11369969
theorem B5053319 : Blo 2245435 5053319 := bstep (se 1 (by rfl) ⟨3789989, by rfl⟩ : syracuseStep 5053319 = 7579979) B7579979
theorem B3368879 : Blo 2245435 3368879 := bstep (se 1 (by rfl) ⟨2526659, by rfl⟩ : syracuseStep 3368879 = 5053319) B5053319
theorem B2245919 : Blo 2245435 2245919 := bstep (se 1 (by rfl) ⟨1684439, by rfl⟩ : syracuseStep 2245919 = 3368879) B3368879
theorem B3368885 : Blo 2245435 3368885 := bbase (se 5 (by rfl) ⟨157916, by rfl⟩ : syracuseStep 3368885 = 315833) (by norm_num)
theorem B2245923 : Blo 2245435 2245923 := bstep (se 1 (by rfl) ⟨1684442, by rfl⟩ : syracuseStep 2245923 = 3368885) B3368885
theorem B5685005 : Blo 2245435 5685005 := bbase (se 3 (by rfl) ⟨1065938, by rfl⟩ : syracuseStep 5685005 = 2131877) (by norm_num)
theorem B3790003 : Blo 2245435 3790003 := bstep (se 1 (by rfl) ⟨2842502, by rfl⟩ : syracuseStep 3790003 = 5685005) B5685005
theorem B5053337 : Blo 2245435 5053337 := bstep (se 2 (by rfl) ⟨1895001, by rfl⟩ : syracuseStep 5053337 = 3790003) B3790003
theorem B3368891 : Blo 2245435 3368891 := bstep (se 1 (by rfl) ⟨2526668, by rfl⟩ : syracuseStep 3368891 = 5053337) B5053337
theorem B2245927 : Blo 2245435 2245927 := bstep (se 1 (by rfl) ⟨1684445, by rfl⟩ : syracuseStep 2245927 = 3368891) B3368891
theorem B2526673 : Blo 2245435 2526673 := bbase (se 2 (by rfl) ⟨947502, by rfl⟩ : syracuseStep 2526673 = 1895005) (by norm_num)
theorem B3368897 : Blo 2245435 3368897 := bstep (se 2 (by rfl) ⟨1263336, by rfl⟩ : syracuseStep 3368897 = 2526673) B2526673
theorem B2245931 : Blo 2245435 2245931 := bstep (se 1 (by rfl) ⟨1684448, by rfl⟩ : syracuseStep 2245931 = 3368897) B3368897
theorem B4796741 : Blo 2245435 4796741 := bbase (se 4 (by rfl) ⟨449694, by rfl⟩ : syracuseStep 4796741 = 899389) (by norm_num)
theorem B3197827 : Blo 2245435 3197827 := bstep (se 1 (by rfl) ⟨2398370, by rfl⟩ : syracuseStep 3197827 = 4796741) B4796741
theorem B4263769 : Blo 2245435 4263769 := bstep (se 2 (by rfl) ⟨1598913, by rfl⟩ : syracuseStep 4263769 = 3197827) B3197827
theorem B5685025 : Blo 2245435 5685025 := bstep (se 2 (by rfl) ⟨2131884, by rfl⟩ : syracuseStep 5685025 = 4263769) B4263769
theorem B7580033 : Blo 2245435 7580033 := bstep (se 2 (by rfl) ⟨2842512, by rfl⟩ : syracuseStep 7580033 = 5685025) B5685025
theorem B5053355 : Blo 2245435 5053355 := bstep (se 1 (by rfl) ⟨3790016, by rfl⟩ : syracuseStep 5053355 = 7580033) B7580033
theorem B3368903 : Blo 2245435 3368903 := bstep (se 1 (by rfl) ⟨2526677, by rfl⟩ : syracuseStep 3368903 = 5053355) B5053355
theorem B2245935 : Blo 2245435 2245935 := bstep (se 1 (by rfl) ⟨1684451, by rfl⟩ : syracuseStep 2245935 = 3368903) B3368903
theorem B3368909 : Blo 2245435 3368909 := bbase (se 3 (by rfl) ⟨631670, by rfl⟩ : syracuseStep 3368909 = 1263341) (by norm_num)
theorem B2245939 : Blo 2245435 2245939 := bstep (se 1 (by rfl) ⟨1684454, by rfl⟩ : syracuseStep 2245939 = 3368909) B3368909
theorem B5053373 : Blo 2245435 5053373 := bbase (se 3 (by rfl) ⟨947507, by rfl⟩ : syracuseStep 5053373 = 1895015) (by norm_num)
theorem B3368915 : Blo 2245435 3368915 := bstep (se 1 (by rfl) ⟨2526686, by rfl⟩ : syracuseStep 3368915 = 5053373) B5053373
theorem B2245943 : Blo 2245435 2245943 := bstep (se 1 (by rfl) ⟨1684457, by rfl⟩ : syracuseStep 2245943 = 3368915) B3368915
theorem B3790037 : Blo 2245435 3790037 := bbase (se 7 (by rfl) ⟨44414, by rfl⟩ : syracuseStep 3790037 = 88829) (by norm_num)
theorem B2526691 : Blo 2245435 2526691 := bstep (se 1 (by rfl) ⟨1895018, by rfl⟩ : syracuseStep 2526691 = 3790037) B3790037
theorem B3368921 : Blo 2245435 3368921 := bstep (se 2 (by rfl) ⟨1263345, by rfl⟩ : syracuseStep 3368921 = 2526691) B2526691
theorem B2245947 : Blo 2245435 2245947 := bstep (se 1 (by rfl) ⟨1684460, by rfl⟩ : syracuseStep 2245947 = 3368921) B3368921
theorem B3597581 : Blo 2245435 3597581 := bbase (se 3 (by rfl) ⟨674546, by rfl⟩ : syracuseStep 3597581 = 1349093) (by norm_num)
theorem B9593549 : Blo 2245435 9593549 := bstep (se 3 (by rfl) ⟨1798790, by rfl⟩ : syracuseStep 9593549 = 3597581) B3597581
theorem B6395699 : Blo 2245435 6395699 := bstep (se 1 (by rfl) ⟨4796774, by rfl⟩ : syracuseStep 6395699 = 9593549) B9593549
theorem B17055197 : Blo 2245435 17055197 := bstep (se 3 (by rfl) ⟨3197849, by rfl⟩ : syracuseStep 17055197 = 6395699) B6395699
theorem B11370131 : Blo 2245435 11370131 := bstep (se 1 (by rfl) ⟨8527598, by rfl⟩ : syracuseStep 11370131 = 17055197) B17055197
theorem B7580087 : Blo 2245435 7580087 := bstep (se 1 (by rfl) ⟨5685065, by rfl⟩ : syracuseStep 7580087 = 11370131) B11370131
theorem B5053391 : Blo 2245435 5053391 := bstep (se 1 (by rfl) ⟨3790043, by rfl⟩ : syracuseStep 5053391 = 7580087) B7580087
theorem B3368927 : Blo 2245435 3368927 := bstep (se 1 (by rfl) ⟨2526695, by rfl⟩ : syracuseStep 3368927 = 5053391) B5053391
theorem B2245951 : Blo 2245435 2245951 := bstep (se 1 (by rfl) ⟨1684463, by rfl⟩ : syracuseStep 2245951 = 3368927) B3368927
theorem B3368933 : Blo 2245435 3368933 := bbase (se 4 (by rfl) ⟨315837, by rfl⟩ : syracuseStep 3368933 = 631675) (by norm_num)
theorem B2245955 : Blo 2245435 2245955 := bstep (se 1 (by rfl) ⟨1684466, by rfl⟩ : syracuseStep 2245955 = 3368933) B3368933
theorem B7195189 : Blo 2245435 7195189 := bbase (se 5 (by rfl) ⟨337274, by rfl⟩ : syracuseStep 7195189 = 674549) (by norm_num)
theorem B9593585 : Blo 2245435 9593585 := bstep (se 2 (by rfl) ⟨3597594, by rfl⟩ : syracuseStep 9593585 = 7195189) B7195189
theorem B6395723 : Blo 2245435 6395723 := bstep (se 1 (by rfl) ⟨4796792, by rfl⟩ : syracuseStep 6395723 = 9593585) B9593585
theorem B4263815 : Blo 2245435 4263815 := bstep (se 1 (by rfl) ⟨3197861, by rfl⟩ : syracuseStep 4263815 = 6395723) B6395723
theorem B2842543 : Blo 2245435 2842543 := bstep (se 1 (by rfl) ⟨2131907, by rfl⟩ : syracuseStep 2842543 = 4263815) B4263815
theorem B3790057 : Blo 2245435 3790057 := bstep (se 2 (by rfl) ⟨1421271, by rfl⟩ : syracuseStep 3790057 = 2842543) B2842543
theorem B5053409 : Blo 2245435 5053409 := bstep (se 2 (by rfl) ⟨1895028, by rfl⟩ : syracuseStep 5053409 = 3790057) B3790057
theorem B3368939 : Blo 2245435 3368939 := bstep (se 1 (by rfl) ⟨2526704, by rfl⟩ : syracuseStep 3368939 = 5053409) B5053409
theorem B2245959 : Blo 2245435 2245959 := bstep (se 1 (by rfl) ⟨1684469, by rfl⟩ : syracuseStep 2245959 = 3368939) B3368939
theorem B2526709 : Blo 2245435 2526709 := bbase (se 5 (by rfl) ⟨118439, by rfl⟩ : syracuseStep 2526709 = 236879) (by norm_num)
theorem B3368945 : Blo 2245435 3368945 := bstep (se 2 (by rfl) ⟨1263354, by rfl⟩ : syracuseStep 3368945 = 2526709) B2526709
theorem B2245963 : Blo 2245435 2245963 := bstep (se 1 (by rfl) ⟨1684472, by rfl⟩ : syracuseStep 2245963 = 3368945) B3368945
theorem B2842553 : Blo 2245435 2842553 := bbase (se 2 (by rfl) ⟨1065957, by rfl⟩ : syracuseStep 2842553 = 2131915) (by norm_num)
theorem B7580141 : Blo 2245435 7580141 := bstep (se 3 (by rfl) ⟨1421276, by rfl⟩ : syracuseStep 7580141 = 2842553) B2842553
theorem B5053427 : Blo 2245435 5053427 := bstep (se 1 (by rfl) ⟨3790070, by rfl⟩ : syracuseStep 5053427 = 7580141) B7580141
theorem B3368951 : Blo 2245435 3368951 := bstep (se 1 (by rfl) ⟨2526713, by rfl⟩ : syracuseStep 3368951 = 5053427) B5053427
theorem B2245967 : Blo 2245435 2245967 := bstep (se 1 (by rfl) ⟨1684475, by rfl⟩ : syracuseStep 2245967 = 3368951) B3368951
theorem B3368957 : Blo 2245435 3368957 := bbase (se 3 (by rfl) ⟨631679, by rfl⟩ : syracuseStep 3368957 = 1263359) (by norm_num)
theorem B2245971 : Blo 2245435 2245971 := bstep (se 1 (by rfl) ⟨1684478, by rfl⟩ : syracuseStep 2245971 = 3368957) B3368957
theorem B5053445 : Blo 2245435 5053445 := bbase (se 4 (by rfl) ⟨473760, by rfl⟩ : syracuseStep 5053445 = 947521) (by norm_num)
theorem B3368963 : Blo 2245435 3368963 := bstep (se 1 (by rfl) ⟨2526722, by rfl⟩ : syracuseStep 3368963 = 5053445) B5053445
theorem B2245975 : Blo 2245435 2245975 := bstep (se 1 (by rfl) ⟨1684481, by rfl⟩ : syracuseStep 2245975 = 3368963) B3368963
theorem B4263853 : Blo 2245435 4263853 := bbase (se 3 (by rfl) ⟨799472, by rfl⟩ : syracuseStep 4263853 = 1598945) (by norm_num)
theorem B5685137 : Blo 2245435 5685137 := bstep (se 2 (by rfl) ⟨2131926, by rfl⟩ : syracuseStep 5685137 = 4263853) B4263853
theorem B3790091 : Blo 2245435 3790091 := bstep (se 1 (by rfl) ⟨2842568, by rfl⟩ : syracuseStep 3790091 = 5685137) B5685137
theorem B2526727 : Blo 2245435 2526727 := bstep (se 1 (by rfl) ⟨1895045, by rfl⟩ : syracuseStep 2526727 = 3790091) B3790091
theorem B3368969 : Blo 2245435 3368969 := bstep (se 2 (by rfl) ⟨1263363, by rfl⟩ : syracuseStep 3368969 = 2526727) B2526727
theorem B2245979 : Blo 2245435 2245979 := bstep (se 1 (by rfl) ⟨1684484, by rfl⟩ : syracuseStep 2245979 = 3368969) B3368969
theorem B11370293 : Blo 2245435 11370293 := bbase (se 5 (by rfl) ⟨532982, by rfl⟩ : syracuseStep 11370293 = 1065965) (by norm_num)
theorem B7580195 : Blo 2245435 7580195 := bstep (se 1 (by rfl) ⟨5685146, by rfl⟩ : syracuseStep 7580195 = 11370293) B11370293
theorem B5053463 : Blo 2245435 5053463 := bstep (se 1 (by rfl) ⟨3790097, by rfl⟩ : syracuseStep 5053463 = 7580195) B7580195
theorem B3368975 : Blo 2245435 3368975 := bstep (se 1 (by rfl) ⟨2526731, by rfl⟩ : syracuseStep 3368975 = 5053463) B5053463
theorem B2245983 : Blo 2245435 2245983 := bstep (se 1 (by rfl) ⟨1684487, by rfl⟩ : syracuseStep 2245983 = 3368975) B3368975
theorem B3368981 : Blo 2245435 3368981 := bbase (se 6 (by rfl) ⟨78960, by rfl⟩ : syracuseStep 3368981 = 157921) (by norm_num)
theorem B2245987 : Blo 2245435 2245987 := bstep (se 1 (by rfl) ⟨1684490, by rfl⟩ : syracuseStep 2245987 = 3368981) B3368981
theorem B14390581 : Blo 2245435 14390581 := bbase (se 5 (by rfl) ⟨674558, by rfl⟩ : syracuseStep 14390581 = 1349117) (by norm_num)
theorem B19187441 : Blo 2245435 19187441 := bstep (se 2 (by rfl) ⟨7195290, by rfl⟩ : syracuseStep 19187441 = 14390581) B14390581
theorem B12791627 : Blo 2245435 12791627 := bstep (se 1 (by rfl) ⟨9593720, by rfl⟩ : syracuseStep 12791627 = 19187441) B19187441
theorem B8527751 : Blo 2245435 8527751 := bstep (se 1 (by rfl) ⟨6395813, by rfl⟩ : syracuseStep 8527751 = 12791627) B12791627
theorem B5685167 : Blo 2245435 5685167 := bstep (se 1 (by rfl) ⟨4263875, by rfl⟩ : syracuseStep 5685167 = 8527751) B8527751
theorem B3790111 : Blo 2245435 3790111 := bstep (se 1 (by rfl) ⟨2842583, by rfl⟩ : syracuseStep 3790111 = 5685167) B5685167
theorem B5053481 : Blo 2245435 5053481 := bstep (se 2 (by rfl) ⟨1895055, by rfl⟩ : syracuseStep 5053481 = 3790111) B3790111
theorem B3368987 : Blo 2245435 3368987 := bstep (se 1 (by rfl) ⟨2526740, by rfl⟩ : syracuseStep 3368987 = 5053481) B5053481
theorem B2245991 : Blo 2245435 2245991 := bstep (se 1 (by rfl) ⟨1684493, by rfl⟩ : syracuseStep 2245991 = 3368987) B3368987
theorem B2526745 : Blo 2245435 2526745 := bbase (se 2 (by rfl) ⟨947529, by rfl⟩ : syracuseStep 2526745 = 1895059) (by norm_num)
theorem B3368993 : Blo 2245435 3368993 := bstep (se 2 (by rfl) ⟨1263372, by rfl⟩ : syracuseStep 3368993 = 2526745) B2526745
theorem B2245995 : Blo 2245435 2245995 := bstep (se 1 (by rfl) ⟨1684496, by rfl⟩ : syracuseStep 2245995 = 3368993) B3368993
theorem B8527781 : Blo 2245435 8527781 := bbase (se 4 (by rfl) ⟨799479, by rfl⟩ : syracuseStep 8527781 = 1598959) (by norm_num)
theorem B5685187 : Blo 2245435 5685187 := bstep (se 1 (by rfl) ⟨4263890, by rfl⟩ : syracuseStep 5685187 = 8527781) B8527781
theorem B7580249 : Blo 2245435 7580249 := bstep (se 2 (by rfl) ⟨2842593, by rfl⟩ : syracuseStep 7580249 = 5685187) B5685187
theorem B5053499 : Blo 2245435 5053499 := bstep (se 1 (by rfl) ⟨3790124, by rfl⟩ : syracuseStep 5053499 = 7580249) B7580249
theorem B3368999 : Blo 2245435 3368999 := bstep (se 1 (by rfl) ⟨2526749, by rfl⟩ : syracuseStep 3368999 = 5053499) B5053499
theorem B2245999 : Blo 2245435 2245999 := bstep (se 1 (by rfl) ⟨1684499, by rfl⟩ : syracuseStep 2245999 = 3368999) B3368999
theorem B3369005 : Blo 2245435 3369005 := bbase (se 3 (by rfl) ⟨631688, by rfl⟩ : syracuseStep 3369005 = 1263377) (by norm_num)
theorem B2246003 : Blo 2245435 2246003 := bstep (se 1 (by rfl) ⟨1684502, by rfl⟩ : syracuseStep 2246003 = 3369005) B3369005
theorem B5053517 : Blo 2245435 5053517 := bbase (se 3 (by rfl) ⟨947534, by rfl⟩ : syracuseStep 5053517 = 1895069) (by norm_num)
theorem B3369011 : Blo 2245435 3369011 := bstep (se 1 (by rfl) ⟨2526758, by rfl⟩ : syracuseStep 3369011 = 5053517) B5053517
theorem B2246007 : Blo 2245435 2246007 := bstep (se 1 (by rfl) ⟨1684505, by rfl⟩ : syracuseStep 2246007 = 3369011) B3369011
theorem B2842609 : Blo 2245435 2842609 := bbase (se 2 (by rfl) ⟨1065978, by rfl⟩ : syracuseStep 2842609 = 2131957) (by norm_num)
theorem B3790145 : Blo 2245435 3790145 := bstep (se 2 (by rfl) ⟨1421304, by rfl⟩ : syracuseStep 3790145 = 2842609) B2842609
theorem B2526763 : Blo 2245435 2526763 := bstep (se 1 (by rfl) ⟨1895072, by rfl⟩ : syracuseStep 2526763 = 3790145) B3790145
theorem B3369017 : Blo 2245435 3369017 := bstep (se 2 (by rfl) ⟨1263381, by rfl⟩ : syracuseStep 3369017 = 2526763) B2526763
theorem B2246011 : Blo 2245435 2246011 := bstep (se 1 (by rfl) ⟨1684508, by rfl⟩ : syracuseStep 2246011 = 3369017) B3369017
theorem B21052853 : Blo 2245435 21052853 := bbase (se 5 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 21052853 = 1973705) (by norm_num)
theorem B14035235 : Blo 2245435 14035235 := bstep (se 1 (by rfl) ⟨10526426, by rfl⟩ : syracuseStep 14035235 = 21052853) B21052853
theorem B37427293 : Blo 2245435 37427293 := bstep (se 3 (by rfl) ⟨7017617, by rfl⟩ : syracuseStep 37427293 = 14035235) B14035235
theorem B49903057 : Blo 2245435 49903057 := bstep (se 2 (by rfl) ⟨18713646, by rfl⟩ : syracuseStep 49903057 = 37427293) B37427293
theorem B66537409 : Blo 2245435 66537409 := bstep (se 2 (by rfl) ⟨24951528, by rfl⟩ : syracuseStep 66537409 = 49903057) B49903057
theorem B88716545 : Blo 2245435 88716545 := bstep (se 2 (by rfl) ⟨33268704, by rfl⟩ : syracuseStep 88716545 = 66537409) B66537409
theorem B59144363 : Blo 2245435 59144363 := bstep (se 1 (by rfl) ⟨44358272, by rfl⟩ : syracuseStep 59144363 = 88716545) B88716545
theorem B39429575 : Blo 2245435 39429575 := bstep (se 1 (by rfl) ⟨29572181, by rfl⟩ : syracuseStep 39429575 = 59144363) B59144363
theorem B26286383 : Blo 2245435 26286383 := bstep (se 1 (by rfl) ⟨19714787, by rfl⟩ : syracuseStep 26286383 = 39429575) B39429575
theorem B17524255 : Blo 2245435 17524255 := bstep (se 1 (by rfl) ⟨13143191, by rfl⟩ : syracuseStep 17524255 = 26286383) B26286383
theorem B23365673 : Blo 2245435 23365673 := bstep (se 2 (by rfl) ⟨8762127, by rfl⟩ : syracuseStep 23365673 = 17524255) B17524255
theorem B15577115 : Blo 2245435 15577115 := bstep (se 1 (by rfl) ⟨11682836, by rfl⟩ : syracuseStep 15577115 = 23365673) B23365673
theorem B41538973 : Blo 2245435 41538973 := bstep (se 3 (by rfl) ⟨7788557, by rfl⟩ : syracuseStep 41538973 = 15577115) B15577115
theorem B55385297 : Blo 2245435 55385297 := bstep (se 2 (by rfl) ⟨20769486, by rfl⟩ : syracuseStep 55385297 = 41538973) B41538973
theorem B36923531 : Blo 2245435 36923531 := bstep (se 1 (by rfl) ⟨27692648, by rfl⟩ : syracuseStep 36923531 = 55385297) B55385297
theorem B98462749 : Blo 2245435 98462749 := bstep (se 3 (by rfl) ⟨18461765, by rfl⟩ : syracuseStep 98462749 = 36923531) B36923531
theorem B131283665 : Blo 2245435 131283665 := bstep (se 2 (by rfl) ⟨49231374, by rfl⟩ : syracuseStep 131283665 = 98462749) B98462749
theorem B87522443 : Blo 2245435 87522443 := bstep (se 1 (by rfl) ⟨65641832, by rfl⟩ : syracuseStep 87522443 = 131283665) B131283665
theorem B58348295 : Blo 2245435 58348295 := bstep (se 1 (by rfl) ⟨43761221, by rfl⟩ : syracuseStep 58348295 = 87522443) B87522443
theorem B38898863 : Blo 2245435 38898863 := bstep (se 1 (by rfl) ⟨29174147, by rfl⟩ : syracuseStep 38898863 = 58348295) B58348295
theorem B25932575 : Blo 2245435 25932575 := bstep (se 1 (by rfl) ⟨19449431, by rfl⟩ : syracuseStep 25932575 = 38898863) B38898863
theorem B69153533 : Blo 2245435 69153533 := bstep (se 3 (by rfl) ⟨12966287, by rfl⟩ : syracuseStep 69153533 = 25932575) B25932575
theorem B46102355 : Blo 2245435 46102355 := bstep (se 1 (by rfl) ⟨34576766, by rfl⟩ : syracuseStep 46102355 = 69153533) B69153533
theorem B30734903 : Blo 2245435 30734903 := bstep (se 1 (by rfl) ⟨23051177, by rfl⟩ : syracuseStep 30734903 = 46102355) B46102355
theorem B20489935 : Blo 2245435 20489935 := bstep (se 1 (by rfl) ⟨15367451, by rfl⟩ : syracuseStep 20489935 = 30734903) B30734903
theorem B27319913 : Blo 2245435 27319913 := bstep (se 2 (by rfl) ⟨10244967, by rfl⟩ : syracuseStep 27319913 = 20489935) B20489935
theorem B18213275 : Blo 2245435 18213275 := bstep (se 1 (by rfl) ⟨13659956, by rfl⟩ : syracuseStep 18213275 = 27319913) B27319913
theorem B12142183 : Blo 2245435 12142183 := bstep (se 1 (by rfl) ⟨9106637, by rfl⟩ : syracuseStep 12142183 = 18213275) B18213275
theorem B16189577 : Blo 2245435 16189577 := bstep (se 2 (by rfl) ⟨6071091, by rfl⟩ : syracuseStep 16189577 = 12142183) B12142183
theorem B10793051 : Blo 2245435 10793051 := bstep (se 1 (by rfl) ⟨8094788, by rfl⟩ : syracuseStep 10793051 = 16189577) B16189577
theorem B7195367 : Blo 2245435 7195367 := bstep (se 1 (by rfl) ⟨5396525, by rfl⟩ : syracuseStep 7195367 = 10793051) B10793051
theorem B4796911 : Blo 2245435 4796911 := bstep (se 1 (by rfl) ⟨3597683, by rfl⟩ : syracuseStep 4796911 = 7195367) B7195367
theorem B25583525 : Blo 2245435 25583525 := bstep (se 4 (by rfl) ⟨2398455, by rfl⟩ : syracuseStep 25583525 = 4796911) B4796911
theorem B17055683 : Blo 2245435 17055683 := bstep (se 1 (by rfl) ⟨12791762, by rfl⟩ : syracuseStep 17055683 = 25583525) B25583525
theorem B11370455 : Blo 2245435 11370455 := bstep (se 1 (by rfl) ⟨8527841, by rfl⟩ : syracuseStep 11370455 = 17055683) B17055683
theorem B7580303 : Blo 2245435 7580303 := bstep (se 1 (by rfl) ⟨5685227, by rfl⟩ : syracuseStep 7580303 = 11370455) B11370455
theorem B5053535 : Blo 2245435 5053535 := bstep (se 1 (by rfl) ⟨3790151, by rfl⟩ : syracuseStep 5053535 = 7580303) B7580303
theorem B3369023 : Blo 2245435 3369023 := bstep (se 1 (by rfl) ⟨2526767, by rfl⟩ : syracuseStep 3369023 = 5053535) B5053535
theorem B2246015 : Blo 2245435 2246015 := bstep (se 1 (by rfl) ⟨1684511, by rfl⟩ : syracuseStep 2246015 = 3369023) B3369023
theorem B3369029 : Blo 2245435 3369029 := bbase (se 4 (by rfl) ⟨315846, by rfl⟩ : syracuseStep 3369029 = 631693) (by norm_num)
theorem B2246019 : Blo 2245435 2246019 := bstep (se 1 (by rfl) ⟨1684514, by rfl⟩ : syracuseStep 2246019 = 3369029) B3369029
theorem B3790165 : Blo 2245435 3790165 := bbase (se 15 (by rfl) ⟨173, by rfl⟩ : syracuseStep 3790165 = 347) (by norm_num)
theorem B5053553 : Blo 2245435 5053553 := bstep (se 2 (by rfl) ⟨1895082, by rfl⟩ : syracuseStep 5053553 = 3790165) B3790165
theorem B3369035 : Blo 2245435 3369035 := bstep (se 1 (by rfl) ⟨2526776, by rfl⟩ : syracuseStep 3369035 = 5053553) B5053553
theorem B2246023 : Blo 2245435 2246023 := bstep (se 1 (by rfl) ⟨1684517, by rfl⟩ : syracuseStep 2246023 = 3369035) B3369035
theorem B2526781 : Blo 2245435 2526781 := bbase (se 3 (by rfl) ⟨473771, by rfl⟩ : syracuseStep 2526781 = 947543) (by norm_num)
theorem B3369041 : Blo 2245435 3369041 := bstep (se 2 (by rfl) ⟨1263390, by rfl⟩ : syracuseStep 3369041 = 2526781) B2526781
theorem B2246027 : Blo 2245435 2246027 := bstep (se 1 (by rfl) ⟨1684520, by rfl⟩ : syracuseStep 2246027 = 3369041) B3369041
theorem B7580357 : Blo 2245435 7580357 := bbase (se 4 (by rfl) ⟨710658, by rfl⟩ : syracuseStep 7580357 = 1421317) (by norm_num)
theorem B5053571 : Blo 2245435 5053571 := bstep (se 1 (by rfl) ⟨3790178, by rfl⟩ : syracuseStep 5053571 = 7580357) B7580357
theorem B3369047 : Blo 2245435 3369047 := bstep (se 1 (by rfl) ⟨2526785, by rfl⟩ : syracuseStep 3369047 = 5053571) B5053571
theorem B2246031 : Blo 2245435 2246031 := bstep (se 1 (by rfl) ⟨1684523, by rfl⟩ : syracuseStep 2246031 = 3369047) B3369047
theorem B3369053 : Blo 2245435 3369053 := bbase (se 3 (by rfl) ⟨631697, by rfl⟩ : syracuseStep 3369053 = 1263395) (by norm_num)
theorem B2246035 : Blo 2245435 2246035 := bstep (se 1 (by rfl) ⟨1684526, by rfl⟩ : syracuseStep 2246035 = 3369053) B3369053
theorem B5053589 : Blo 2245435 5053589 := bbase (se 6 (by rfl) ⟨118443, by rfl⟩ : syracuseStep 5053589 = 236887) (by norm_num)
theorem B3369059 : Blo 2245435 3369059 := bstep (se 1 (by rfl) ⟨2526794, by rfl⟩ : syracuseStep 3369059 = 5053589) B5053589
theorem B2246039 : Blo 2245435 2246039 := bstep (se 1 (by rfl) ⟨1684529, by rfl⟩ : syracuseStep 2246039 = 3369059) B3369059
theorem B3197981 : Blo 2245435 3197981 := bbase (se 3 (by rfl) ⟨599621, by rfl⟩ : syracuseStep 3197981 = 1199243) (by norm_num)
theorem B8527949 : Blo 2245435 8527949 := bstep (se 3 (by rfl) ⟨1598990, by rfl⟩ : syracuseStep 8527949 = 3197981) B3197981
theorem B5685299 : Blo 2245435 5685299 := bstep (se 1 (by rfl) ⟨4263974, by rfl⟩ : syracuseStep 5685299 = 8527949) B8527949
theorem B3790199 : Blo 2245435 3790199 := bstep (se 1 (by rfl) ⟨2842649, by rfl⟩ : syracuseStep 3790199 = 5685299) B5685299
theorem B2526799 : Blo 2245435 2526799 := bstep (se 1 (by rfl) ⟨1895099, by rfl⟩ : syracuseStep 2526799 = 3790199) B3790199
theorem B3369065 : Blo 2245435 3369065 := bstep (se 2 (by rfl) ⟨1263399, by rfl⟩ : syracuseStep 3369065 = 2526799) B2526799
theorem B2246043 : Blo 2245435 2246043 := bstep (se 1 (by rfl) ⟨1684532, by rfl⟩ : syracuseStep 2246043 = 3369065) B3369065
theorem B61470677 : Blo 2245435 61470677 := bbase (se 7 (by rfl) ⟨720359, by rfl⟩ : syracuseStep 61470677 = 1440719) (by norm_num)
theorem B40980451 : Blo 2245435 40980451 := bstep (se 1 (by rfl) ⟨30735338, by rfl⟩ : syracuseStep 40980451 = 61470677) B61470677
theorem B54640601 : Blo 2245435 54640601 := bstep (se 2 (by rfl) ⟨20490225, by rfl⟩ : syracuseStep 54640601 = 40980451) B40980451
theorem B36427067 : Blo 2245435 36427067 := bstep (se 1 (by rfl) ⟨27320300, by rfl⟩ : syracuseStep 36427067 = 54640601) B54640601
theorem B24284711 : Blo 2245435 24284711 := bstep (se 1 (by rfl) ⟨18213533, by rfl⟩ : syracuseStep 24284711 = 36427067) B36427067
theorem B16189807 : Blo 2245435 16189807 := bstep (se 1 (by rfl) ⟨12142355, by rfl⟩ : syracuseStep 16189807 = 24284711) B24284711
theorem B21586409 : Blo 2245435 21586409 := bstep (se 2 (by rfl) ⟨8094903, by rfl⟩ : syracuseStep 21586409 = 16189807) B16189807
theorem B14390939 : Blo 2245435 14390939 := bstep (se 1 (by rfl) ⟨10793204, by rfl⟩ : syracuseStep 14390939 = 21586409) B21586409
theorem B9593959 : Blo 2245435 9593959 := bstep (se 1 (by rfl) ⟨7195469, by rfl⟩ : syracuseStep 9593959 = 14390939) B14390939
theorem B12791945 : Blo 2245435 12791945 := bstep (se 2 (by rfl) ⟨4796979, by rfl⟩ : syracuseStep 12791945 = 9593959) B9593959
theorem B8527963 : Blo 2245435 8527963 := bstep (se 1 (by rfl) ⟨6395972, by rfl⟩ : syracuseStep 8527963 = 12791945) B12791945
theorem B11370617 : Blo 2245435 11370617 := bstep (se 2 (by rfl) ⟨4263981, by rfl⟩ : syracuseStep 11370617 = 8527963) B8527963
theorem B7580411 : Blo 2245435 7580411 := bstep (se 1 (by rfl) ⟨5685308, by rfl⟩ : syracuseStep 7580411 = 11370617) B11370617
theorem B5053607 : Blo 2245435 5053607 := bstep (se 1 (by rfl) ⟨3790205, by rfl⟩ : syracuseStep 5053607 = 7580411) B7580411
theorem B3369071 : Blo 2245435 3369071 := bstep (se 1 (by rfl) ⟨2526803, by rfl⟩ : syracuseStep 3369071 = 5053607) B5053607
theorem B2246047 : Blo 2245435 2246047 := bstep (se 1 (by rfl) ⟨1684535, by rfl⟩ : syracuseStep 2246047 = 3369071) B3369071
theorem B3369077 : Blo 2245435 3369077 := bbase (se 5 (by rfl) ⟨157925, by rfl⟩ : syracuseStep 3369077 = 315851) (by norm_num)
theorem B2246051 : Blo 2245435 2246051 := bstep (se 1 (by rfl) ⟨1684538, by rfl⟩ : syracuseStep 2246051 = 3369077) B3369077
theorem B4263997 : Blo 2245435 4263997 := bbase (se 3 (by rfl) ⟨799499, by rfl⟩ : syracuseStep 4263997 = 1598999) (by norm_num)
theorem B5685329 : Blo 2245435 5685329 := bstep (se 2 (by rfl) ⟨2131998, by rfl⟩ : syracuseStep 5685329 = 4263997) B4263997
theorem B3790219 : Blo 2245435 3790219 := bstep (se 1 (by rfl) ⟨2842664, by rfl⟩ : syracuseStep 3790219 = 5685329) B5685329
theorem B5053625 : Blo 2245435 5053625 := bstep (se 2 (by rfl) ⟨1895109, by rfl⟩ : syracuseStep 5053625 = 3790219) B3790219
theorem B3369083 : Blo 2245435 3369083 := bstep (se 1 (by rfl) ⟨2526812, by rfl⟩ : syracuseStep 3369083 = 5053625) B5053625
theorem B2246055 : Blo 2245435 2246055 := bstep (se 1 (by rfl) ⟨1684541, by rfl⟩ : syracuseStep 2246055 = 3369083) B3369083
theorem B2526817 : Blo 2245435 2526817 := bbase (se 2 (by rfl) ⟨947556, by rfl⟩ : syracuseStep 2526817 = 1895113) (by norm_num)
theorem B3369089 : Blo 2245435 3369089 := bstep (se 2 (by rfl) ⟨1263408, by rfl⟩ : syracuseStep 3369089 = 2526817) B2526817
theorem B2246059 : Blo 2245435 2246059 := bstep (se 1 (by rfl) ⟨1684544, by rfl⟩ : syracuseStep 2246059 = 3369089) B3369089
theorem B5685349 : Blo 2245435 5685349 := bbase (se 4 (by rfl) ⟨533001, by rfl⟩ : syracuseStep 5685349 = 1066003) (by norm_num)
theorem B7580465 : Blo 2245435 7580465 := bstep (se 2 (by rfl) ⟨2842674, by rfl⟩ : syracuseStep 7580465 = 5685349) B5685349
theorem B5053643 : Blo 2245435 5053643 := bstep (se 1 (by rfl) ⟨3790232, by rfl⟩ : syracuseStep 5053643 = 7580465) B7580465
theorem B3369095 : Blo 2245435 3369095 := bstep (se 1 (by rfl) ⟨2526821, by rfl⟩ : syracuseStep 3369095 = 5053643) B5053643
theorem B2246063 : Blo 2245435 2246063 := bstep (se 1 (by rfl) ⟨1684547, by rfl⟩ : syracuseStep 2246063 = 3369095) B3369095
theorem B3369101 : Blo 2245435 3369101 := bbase (se 3 (by rfl) ⟨631706, by rfl⟩ : syracuseStep 3369101 = 1263413) (by norm_num)
theorem B2246067 : Blo 2245435 2246067 := bstep (se 1 (by rfl) ⟨1684550, by rfl⟩ : syracuseStep 2246067 = 3369101) B3369101
theorem B5053661 : Blo 2245435 5053661 := bbase (se 3 (by rfl) ⟨947561, by rfl⟩ : syracuseStep 5053661 = 1895123) (by norm_num)
theorem B3369107 : Blo 2245435 3369107 := bstep (se 1 (by rfl) ⟨2526830, by rfl⟩ : syracuseStep 3369107 = 5053661) B5053661
theorem B2246071 : Blo 2245435 2246071 := bstep (se 1 (by rfl) ⟨1684553, by rfl⟩ : syracuseStep 2246071 = 3369107) B3369107
theorem B3790253 : Blo 2245435 3790253 := bbase (se 3 (by rfl) ⟨710672, by rfl⟩ : syracuseStep 3790253 = 1421345) (by norm_num)
theorem B2526835 : Blo 2245435 2526835 := bstep (se 1 (by rfl) ⟨1895126, by rfl⟩ : syracuseStep 2526835 = 3790253) B3790253
theorem B3369113 : Blo 2245435 3369113 := bstep (se 2 (by rfl) ⟨1263417, by rfl⟩ : syracuseStep 3369113 = 2526835) B2526835
theorem B2246075 : Blo 2245435 2246075 := bstep (se 1 (by rfl) ⟨1684556, by rfl⟩ : syracuseStep 2246075 = 3369113) B3369113
theorem B2339273 : Blo 2245435 2339273 := bbase (se 2 (by rfl) ⟨877227, by rfl⟩ : syracuseStep 2339273 = 1754455) (by norm_num)
theorem B6238061 : Blo 2245435 6238061 := bstep (se 3 (by rfl) ⟨1169636, by rfl⟩ : syracuseStep 6238061 = 2339273) B2339273
theorem B4158707 : Blo 2245435 4158707 := bstep (se 1 (by rfl) ⟨3119030, by rfl⟩ : syracuseStep 4158707 = 6238061) B6238061
theorem B11089885 : Blo 2245435 11089885 := bstep (se 3 (by rfl) ⟨2079353, by rfl⟩ : syracuseStep 11089885 = 4158707) B4158707
theorem B14786513 : Blo 2245435 14786513 := bstep (se 2 (by rfl) ⟨5544942, by rfl⟩ : syracuseStep 14786513 = 11089885) B11089885
theorem B9857675 : Blo 2245435 9857675 := bstep (se 1 (by rfl) ⟨7393256, by rfl⟩ : syracuseStep 9857675 = 14786513) B14786513
theorem B6571783 : Blo 2245435 6571783 := bstep (se 1 (by rfl) ⟨4928837, by rfl⟩ : syracuseStep 6571783 = 9857675) B9857675
theorem B8762377 : Blo 2245435 8762377 := bstep (se 2 (by rfl) ⟨3285891, by rfl⟩ : syracuseStep 8762377 = 6571783) B6571783
theorem B11683169 : Blo 2245435 11683169 := bstep (se 2 (by rfl) ⟨4381188, by rfl⟩ : syracuseStep 11683169 = 8762377) B8762377
theorem B7788779 : Blo 2245435 7788779 := bstep (se 1 (by rfl) ⟨5841584, by rfl⟩ : syracuseStep 7788779 = 11683169) B11683169
theorem B5192519 : Blo 2245435 5192519 := bstep (se 1 (by rfl) ⟨3894389, by rfl⟩ : syracuseStep 5192519 = 7788779) B7788779
theorem B13846717 : Blo 2245435 13846717 := bstep (se 3 (by rfl) ⟨2596259, by rfl⟩ : syracuseStep 13846717 = 5192519) B5192519
theorem B73849157 : Blo 2245435 73849157 := bstep (se 4 (by rfl) ⟨6923358, by rfl⟩ : syracuseStep 73849157 = 13846717) B13846717
theorem B49232771 : Blo 2245435 49232771 := bstep (se 1 (by rfl) ⟨36924578, by rfl⟩ : syracuseStep 49232771 = 73849157) B73849157
theorem B32821847 : Blo 2245435 32821847 := bstep (se 1 (by rfl) ⟨24616385, by rfl⟩ : syracuseStep 32821847 = 49232771) B49232771
theorem B21881231 : Blo 2245435 21881231 := bstep (se 1 (by rfl) ⟨16410923, by rfl⟩ : syracuseStep 21881231 = 32821847) B32821847
theorem B14587487 : Blo 2245435 14587487 := bstep (se 1 (by rfl) ⟨10940615, by rfl⟩ : syracuseStep 14587487 = 21881231) B21881231
theorem B9724991 : Blo 2245435 9724991 := bstep (se 1 (by rfl) ⟨7293743, by rfl⟩ : syracuseStep 9724991 = 14587487) B14587487
theorem B103733237 : Blo 2245435 103733237 := bstep (se 5 (by rfl) ⟨4862495, by rfl⟩ : syracuseStep 103733237 = 9724991) B9724991
theorem B276621965 : Blo 2245435 276621965 := bstep (se 3 (by rfl) ⟨51866618, by rfl⟩ : syracuseStep 276621965 = 103733237) B103733237
theorem B184414643 : Blo 2245435 184414643 := bstep (se 1 (by rfl) ⟨138310982, by rfl⟩ : syracuseStep 184414643 = 276621965) B276621965
theorem B122943095 : Blo 2245435 122943095 := bstep (se 1 (by rfl) ⟨92207321, by rfl⟩ : syracuseStep 122943095 = 184414643) B184414643
theorem B81962063 : Blo 2245435 81962063 := bstep (se 1 (by rfl) ⟨61471547, by rfl⟩ : syracuseStep 81962063 = 122943095) B122943095
theorem B54641375 : Blo 2245435 54641375 := bstep (se 1 (by rfl) ⟨40981031, by rfl⟩ : syracuseStep 54641375 = 81962063) B81962063
theorem B36427583 : Blo 2245435 36427583 := bstep (se 1 (by rfl) ⟨27320687, by rfl⟩ : syracuseStep 36427583 = 54641375) B54641375
theorem B97140221 : Blo 2245435 97140221 := bstep (se 3 (by rfl) ⟨18213791, by rfl⟩ : syracuseStep 97140221 = 36427583) B36427583
theorem B64760147 : Blo 2245435 64760147 := bstep (se 1 (by rfl) ⟨48570110, by rfl⟩ : syracuseStep 64760147 = 97140221) B97140221
theorem B43173431 : Blo 2245435 43173431 := bstep (se 1 (by rfl) ⟨32380073, by rfl⟩ : syracuseStep 43173431 = 64760147) B64760147
theorem B28782287 : Blo 2245435 28782287 := bstep (se 1 (by rfl) ⟨21586715, by rfl⟩ : syracuseStep 28782287 = 43173431) B43173431
theorem B19188191 : Blo 2245435 19188191 := bstep (se 1 (by rfl) ⟨14391143, by rfl⟩ : syracuseStep 19188191 = 28782287) B28782287
theorem B12792127 : Blo 2245435 12792127 := bstep (se 1 (by rfl) ⟨9594095, by rfl⟩ : syracuseStep 12792127 = 19188191) B19188191
theorem B17056169 : Blo 2245435 17056169 := bstep (se 2 (by rfl) ⟨6396063, by rfl⟩ : syracuseStep 17056169 = 12792127) B12792127
theorem B11370779 : Blo 2245435 11370779 := bstep (se 1 (by rfl) ⟨8528084, by rfl⟩ : syracuseStep 11370779 = 17056169) B17056169
theorem B7580519 : Blo 2245435 7580519 := bstep (se 1 (by rfl) ⟨5685389, by rfl⟩ : syracuseStep 7580519 = 11370779) B11370779
theorem B5053679 : Blo 2245435 5053679 := bstep (se 1 (by rfl) ⟨3790259, by rfl⟩ : syracuseStep 5053679 = 7580519) B7580519
theorem B3369119 : Blo 2245435 3369119 := bstep (se 1 (by rfl) ⟨2526839, by rfl⟩ : syracuseStep 3369119 = 5053679) B5053679
theorem B2246079 : Blo 2245435 2246079 := bstep (se 1 (by rfl) ⟨1684559, by rfl⟩ : syracuseStep 2246079 = 3369119) B3369119
theorem B3369125 : Blo 2245435 3369125 := bbase (se 4 (by rfl) ⟨315855, by rfl⟩ : syracuseStep 3369125 = 631711) (by norm_num)
theorem B2246083 : Blo 2245435 2246083 := bstep (se 1 (by rfl) ⟨1684562, by rfl⟩ : syracuseStep 2246083 = 3369125) B3369125
theorem B2842705 : Blo 2245435 2842705 := bbase (se 2 (by rfl) ⟨1066014, by rfl⟩ : syracuseStep 2842705 = 2132029) (by norm_num)
theorem B3790273 : Blo 2245435 3790273 := bstep (se 2 (by rfl) ⟨1421352, by rfl⟩ : syracuseStep 3790273 = 2842705) B2842705
theorem B5053697 : Blo 2245435 5053697 := bstep (se 2 (by rfl) ⟨1895136, by rfl⟩ : syracuseStep 5053697 = 3790273) B3790273
theorem B3369131 : Blo 2245435 3369131 := bstep (se 1 (by rfl) ⟨2526848, by rfl⟩ : syracuseStep 3369131 = 5053697) B5053697
theorem B2246087 : Blo 2245435 2246087 := bstep (se 1 (by rfl) ⟨1684565, by rfl⟩ : syracuseStep 2246087 = 3369131) B3369131
theorem B2526853 : Blo 2245435 2526853 := bbase (se 4 (by rfl) ⟨236892, by rfl⟩ : syracuseStep 2526853 = 473785) (by norm_num)
theorem B3369137 : Blo 2245435 3369137 := bstep (se 2 (by rfl) ⟨1263426, by rfl⟩ : syracuseStep 3369137 = 2526853) B2526853
theorem B2246091 : Blo 2245435 2246091 := bstep (se 1 (by rfl) ⟨1684568, by rfl⟩ : syracuseStep 2246091 = 3369137) B3369137
theorem B9857749 : Blo 2245435 9857749 := bbase (se 7 (by rfl) ⟨115520, by rfl⟩ : syracuseStep 9857749 = 231041) (by norm_num)
theorem B13143665 : Blo 2245435 13143665 := bstep (se 2 (by rfl) ⟨4928874, by rfl⟩ : syracuseStep 13143665 = 9857749) B9857749
theorem B35049773 : Blo 2245435 35049773 := bstep (se 3 (by rfl) ⟨6571832, by rfl⟩ : syracuseStep 35049773 = 13143665) B13143665
theorem B93466061 : Blo 2245435 93466061 := bstep (se 3 (by rfl) ⟨17524886, by rfl⟩ : syracuseStep 93466061 = 35049773) B35049773
theorem B62310707 : Blo 2245435 62310707 := bstep (se 1 (by rfl) ⟨46733030, by rfl⟩ : syracuseStep 62310707 = 93466061) B93466061
theorem B41540471 : Blo 2245435 41540471 := bstep (se 1 (by rfl) ⟨31155353, by rfl⟩ : syracuseStep 41540471 = 62310707) B62310707
theorem B27693647 : Blo 2245435 27693647 := bstep (se 1 (by rfl) ⟨20770235, by rfl⟩ : syracuseStep 27693647 = 41540471) B41540471
theorem B18462431 : Blo 2245435 18462431 := bstep (se 1 (by rfl) ⟨13846823, by rfl⟩ : syracuseStep 18462431 = 27693647) B27693647
theorem B12308287 : Blo 2245435 12308287 := bstep (se 1 (by rfl) ⟨9231215, by rfl⟩ : syracuseStep 12308287 = 18462431) B18462431
theorem B16411049 : Blo 2245435 16411049 := bstep (se 2 (by rfl) ⟨6154143, by rfl⟩ : syracuseStep 16411049 = 12308287) B12308287
theorem B10940699 : Blo 2245435 10940699 := bstep (se 1 (by rfl) ⟨8205524, by rfl⟩ : syracuseStep 10940699 = 16411049) B16411049
theorem B7293799 : Blo 2245435 7293799 := bstep (se 1 (by rfl) ⟨5470349, by rfl⟩ : syracuseStep 7293799 = 10940699) B10940699
theorem B9725065 : Blo 2245435 9725065 := bstep (se 2 (by rfl) ⟨3646899, by rfl⟩ : syracuseStep 9725065 = 7293799) B7293799
theorem B51867013 : Blo 2245435 51867013 := bstep (se 4 (by rfl) ⟨4862532, by rfl⟩ : syracuseStep 51867013 = 9725065) B9725065
theorem B69156017 : Blo 2245435 69156017 := bstep (se 2 (by rfl) ⟨25933506, by rfl⟩ : syracuseStep 69156017 = 51867013) B51867013
theorem B46104011 : Blo 2245435 46104011 := bstep (se 1 (by rfl) ⟨34578008, by rfl⟩ : syracuseStep 46104011 = 69156017) B69156017
theorem B30736007 : Blo 2245435 30736007 := bstep (se 1 (by rfl) ⟨23052005, by rfl⟩ : syracuseStep 30736007 = 46104011) B46104011
theorem B20490671 : Blo 2245435 20490671 := bstep (se 1 (by rfl) ⟨15368003, by rfl⟩ : syracuseStep 20490671 = 30736007) B30736007
theorem B13660447 : Blo 2245435 13660447 := bstep (se 1 (by rfl) ⟨10245335, by rfl⟩ : syracuseStep 13660447 = 20490671) B20490671
theorem B18213929 : Blo 2245435 18213929 := bstep (se 2 (by rfl) ⟨6830223, by rfl⟩ : syracuseStep 18213929 = 13660447) B13660447
theorem B12142619 : Blo 2245435 12142619 := bstep (se 1 (by rfl) ⟨9106964, by rfl⟩ : syracuseStep 12142619 = 18213929) B18213929
theorem B8095079 : Blo 2245435 8095079 := bstep (se 1 (by rfl) ⟨6071309, by rfl⟩ : syracuseStep 8095079 = 12142619) B12142619
theorem B5396719 : Blo 2245435 5396719 := bstep (se 1 (by rfl) ⟨4047539, by rfl⟩ : syracuseStep 5396719 = 8095079) B8095079
theorem B7195625 : Blo 2245435 7195625 := bstep (se 2 (by rfl) ⟨2698359, by rfl⟩ : syracuseStep 7195625 = 5396719) B5396719
theorem B4797083 : Blo 2245435 4797083 := bstep (se 1 (by rfl) ⟨3597812, by rfl⟩ : syracuseStep 4797083 = 7195625) B7195625
theorem B3198055 : Blo 2245435 3198055 := bstep (se 1 (by rfl) ⟨2398541, by rfl⟩ : syracuseStep 3198055 = 4797083) B4797083
theorem B4264073 : Blo 2245435 4264073 := bstep (se 2 (by rfl) ⟨1599027, by rfl⟩ : syracuseStep 4264073 = 3198055) B3198055
theorem B2842715 : Blo 2245435 2842715 := bstep (se 1 (by rfl) ⟨2132036, by rfl⟩ : syracuseStep 2842715 = 4264073) B4264073
theorem B7580573 : Blo 2245435 7580573 := bstep (se 3 (by rfl) ⟨1421357, by rfl⟩ : syracuseStep 7580573 = 2842715) B2842715
theorem B5053715 : Blo 2245435 5053715 := bstep (se 1 (by rfl) ⟨3790286, by rfl⟩ : syracuseStep 5053715 = 7580573) B7580573
theorem B3369143 : Blo 2245435 3369143 := bstep (se 1 (by rfl) ⟨2526857, by rfl⟩ : syracuseStep 3369143 = 5053715) B5053715
theorem B2246095 : Blo 2245435 2246095 := bstep (se 1 (by rfl) ⟨1684571, by rfl⟩ : syracuseStep 2246095 = 3369143) B3369143
theorem B3369149 : Blo 2245435 3369149 := bbase (se 3 (by rfl) ⟨631715, by rfl⟩ : syracuseStep 3369149 = 1263431) (by norm_num)
theorem B2246099 : Blo 2245435 2246099 := bstep (se 1 (by rfl) ⟨1684574, by rfl⟩ : syracuseStep 2246099 = 3369149) B3369149
theorem B5053733 : Blo 2245435 5053733 := bbase (se 4 (by rfl) ⟨473787, by rfl⟩ : syracuseStep 5053733 = 947575) (by norm_num)
theorem B3369155 : Blo 2245435 3369155 := bstep (se 1 (by rfl) ⟨2526866, by rfl⟩ : syracuseStep 3369155 = 5053733) B5053733
theorem B2246103 : Blo 2245435 2246103 := bstep (se 1 (by rfl) ⟨1684577, by rfl⟩ : syracuseStep 2246103 = 3369155) B3369155
theorem B5685461 : Blo 2245435 5685461 := bbase (se 7 (by rfl) ⟨66626, by rfl⟩ : syracuseStep 5685461 = 133253) (by norm_num)
theorem B3790307 : Blo 2245435 3790307 := bstep (se 1 (by rfl) ⟨2842730, by rfl⟩ : syracuseStep 3790307 = 5685461) B5685461
theorem B2526871 : Blo 2245435 2526871 := bstep (se 1 (by rfl) ⟨1895153, by rfl⟩ : syracuseStep 2526871 = 3790307) B3790307
theorem B3369161 : Blo 2245435 3369161 := bstep (se 2 (by rfl) ⟨1263435, by rfl⟩ : syracuseStep 3369161 = 2526871) B2526871
theorem B2246107 : Blo 2245435 2246107 := bstep (se 1 (by rfl) ⟨1684580, by rfl⟩ : syracuseStep 2246107 = 3369161) B3369161
theorem B10385189 : Blo 2245435 10385189 := bbase (se 4 (by rfl) ⟨973611, by rfl⟩ : syracuseStep 10385189 = 1947223) (by norm_num)
theorem B6923459 : Blo 2245435 6923459 := bstep (se 1 (by rfl) ⟨5192594, by rfl⟩ : syracuseStep 6923459 = 10385189) B10385189
theorem B4615639 : Blo 2245435 4615639 := bstep (se 1 (by rfl) ⟨3461729, by rfl⟩ : syracuseStep 4615639 = 6923459) B6923459
theorem B98466965 : Blo 2245435 98466965 := bstep (se 6 (by rfl) ⟨2307819, by rfl⟩ : syracuseStep 98466965 = 4615639) B4615639
theorem B65644643 : Blo 2245435 65644643 := bstep (se 1 (by rfl) ⟨49233482, by rfl⟩ : syracuseStep 65644643 = 98466965) B98466965
theorem B43763095 : Blo 2245435 43763095 := bstep (se 1 (by rfl) ⟨32822321, by rfl⟩ : syracuseStep 43763095 = 65644643) B65644643
theorem B58350793 : Blo 2245435 58350793 := bstep (se 2 (by rfl) ⟨21881547, by rfl⟩ : syracuseStep 58350793 = 43763095) B43763095
theorem B77801057 : Blo 2245435 77801057 := bstep (se 2 (by rfl) ⟨29175396, by rfl⟩ : syracuseStep 77801057 = 58350793) B58350793
theorem B51867371 : Blo 2245435 51867371 := bstep (se 1 (by rfl) ⟨38900528, by rfl⟩ : syracuseStep 51867371 = 77801057) B77801057
theorem B34578247 : Blo 2245435 34578247 := bstep (se 1 (by rfl) ⟨25933685, by rfl⟩ : syracuseStep 34578247 = 51867371) B51867371
theorem B46104329 : Blo 2245435 46104329 := bstep (se 2 (by rfl) ⟨17289123, by rfl⟩ : syracuseStep 46104329 = 34578247) B34578247
theorem B30736219 : Blo 2245435 30736219 := bstep (se 1 (by rfl) ⟨23052164, by rfl⟩ : syracuseStep 30736219 = 46104329) B46104329
theorem B40981625 : Blo 2245435 40981625 := bstep (se 2 (by rfl) ⟨15368109, by rfl⟩ : syracuseStep 40981625 = 30736219) B30736219
theorem B27321083 : Blo 2245435 27321083 := bstep (se 1 (by rfl) ⟨20490812, by rfl⟩ : syracuseStep 27321083 = 40981625) B40981625
theorem B18214055 : Blo 2245435 18214055 := bstep (se 1 (by rfl) ⟨13660541, by rfl⟩ : syracuseStep 18214055 = 27321083) B27321083
theorem B12142703 : Blo 2245435 12142703 := bstep (se 1 (by rfl) ⟨9107027, by rfl⟩ : syracuseStep 12142703 = 18214055) B18214055
theorem B8095135 : Blo 2245435 8095135 := bstep (se 1 (by rfl) ⟨6071351, by rfl⟩ : syracuseStep 8095135 = 12142703) B12142703
theorem B10793513 : Blo 2245435 10793513 := bstep (se 2 (by rfl) ⟨4047567, by rfl⟩ : syracuseStep 10793513 = 8095135) B8095135
theorem B7195675 : Blo 2245435 7195675 := bstep (se 1 (by rfl) ⟨5396756, by rfl⟩ : syracuseStep 7195675 = 10793513) B10793513
theorem B9594233 : Blo 2245435 9594233 := bstep (se 2 (by rfl) ⟨3597837, by rfl⟩ : syracuseStep 9594233 = 7195675) B7195675
theorem B6396155 : Blo 2245435 6396155 := bstep (se 1 (by rfl) ⟨4797116, by rfl⟩ : syracuseStep 6396155 = 9594233) B9594233
theorem B4264103 : Blo 2245435 4264103 := bstep (se 1 (by rfl) ⟨3198077, by rfl⟩ : syracuseStep 4264103 = 6396155) B6396155
theorem B11370941 : Blo 2245435 11370941 := bstep (se 3 (by rfl) ⟨2132051, by rfl⟩ : syracuseStep 11370941 = 4264103) B4264103
theorem B7580627 : Blo 2245435 7580627 := bstep (se 1 (by rfl) ⟨5685470, by rfl⟩ : syracuseStep 7580627 = 11370941) B11370941
theorem B5053751 : Blo 2245435 5053751 := bstep (se 1 (by rfl) ⟨3790313, by rfl⟩ : syracuseStep 5053751 = 7580627) B7580627
theorem B3369167 : Blo 2245435 3369167 := bstep (se 1 (by rfl) ⟨2526875, by rfl⟩ : syracuseStep 3369167 = 5053751) B5053751
theorem B2246111 : Blo 2245435 2246111 := bstep (se 1 (by rfl) ⟨1684583, by rfl⟩ : syracuseStep 2246111 = 3369167) B3369167
theorem B3369173 : Blo 2245435 3369173 := bbase (se 7 (by rfl) ⟨39482, by rfl⟩ : syracuseStep 3369173 = 78965) (by norm_num)
theorem B2246115 : Blo 2245435 2246115 := bstep (se 1 (by rfl) ⟨1684586, by rfl⟩ : syracuseStep 2246115 = 3369173) B3369173
theorem B7684085 : Blo 2245435 7684085 := bbase (se 5 (by rfl) ⟨360191, by rfl⟩ : syracuseStep 7684085 = 720383) (by norm_num)
theorem B20490893 : Blo 2245435 20490893 := bstep (se 3 (by rfl) ⟨3842042, by rfl⟩ : syracuseStep 20490893 = 7684085) B7684085
theorem B13660595 : Blo 2245435 13660595 := bstep (se 1 (by rfl) ⟨10245446, by rfl⟩ : syracuseStep 13660595 = 20490893) B20490893
theorem B9107063 : Blo 2245435 9107063 := bstep (se 1 (by rfl) ⟨6830297, by rfl⟩ : syracuseStep 9107063 = 13660595) B13660595
theorem B6071375 : Blo 2245435 6071375 := bstep (se 1 (by rfl) ⟨4553531, by rfl⟩ : syracuseStep 6071375 = 9107063) B9107063
theorem B4047583 : Blo 2245435 4047583 := bstep (se 1 (by rfl) ⟨3035687, by rfl⟩ : syracuseStep 4047583 = 6071375) B6071375
theorem B5396777 : Blo 2245435 5396777 := bstep (se 2 (by rfl) ⟨2023791, by rfl⟩ : syracuseStep 5396777 = 4047583) B4047583
theorem B3597851 : Blo 2245435 3597851 := bstep (se 1 (by rfl) ⟨2698388, by rfl⟩ : syracuseStep 3597851 = 5396777) B5396777
theorem B2398567 : Blo 2245435 2398567 := bstep (se 1 (by rfl) ⟨1798925, by rfl⟩ : syracuseStep 2398567 = 3597851) B3597851
theorem B3198089 : Blo 2245435 3198089 := bstep (se 2 (by rfl) ⟨1199283, by rfl⟩ : syracuseStep 3198089 = 2398567) B2398567
theorem B8528237 : Blo 2245435 8528237 := bstep (se 3 (by rfl) ⟨1599044, by rfl⟩ : syracuseStep 8528237 = 3198089) B3198089
theorem B5685491 : Blo 2245435 5685491 := bstep (se 1 (by rfl) ⟨4264118, by rfl⟩ : syracuseStep 5685491 = 8528237) B8528237
theorem B3790327 : Blo 2245435 3790327 := bstep (se 1 (by rfl) ⟨2842745, by rfl⟩ : syracuseStep 3790327 = 5685491) B5685491
theorem B5053769 : Blo 2245435 5053769 := bstep (se 2 (by rfl) ⟨1895163, by rfl⟩ : syracuseStep 5053769 = 3790327) B3790327
theorem B3369179 : Blo 2245435 3369179 := bstep (se 1 (by rfl) ⟨2526884, by rfl⟩ : syracuseStep 3369179 = 5053769) B5053769
theorem B2246119 : Blo 2245435 2246119 := bstep (se 1 (by rfl) ⟨1684589, by rfl⟩ : syracuseStep 2246119 = 3369179) B3369179
theorem B2526889 : Blo 2245435 2526889 := bbase (se 2 (by rfl) ⟨947583, by rfl⟩ : syracuseStep 2526889 = 1895167) (by norm_num)
theorem B3369185 : Blo 2245435 3369185 := bstep (se 2 (by rfl) ⟨1263444, by rfl⟩ : syracuseStep 3369185 = 2526889) B2526889
theorem B2246123 : Blo 2245435 2246123 := bstep (se 1 (by rfl) ⟨1684592, by rfl⟩ : syracuseStep 2246123 = 3369185) B3369185
theorem B9107093 : Blo 2245435 9107093 := bbase (se 6 (by rfl) ⟨213447, by rfl⟩ : syracuseStep 9107093 = 426895) (by norm_num)
theorem B6071395 : Blo 2245435 6071395 := bstep (se 1 (by rfl) ⟨4553546, by rfl⟩ : syracuseStep 6071395 = 9107093) B9107093
theorem B8095193 : Blo 2245435 8095193 := bstep (se 2 (by rfl) ⟨3035697, by rfl⟩ : syracuseStep 8095193 = 6071395) B6071395
theorem B5396795 : Blo 2245435 5396795 := bstep (se 1 (by rfl) ⟨4047596, by rfl⟩ : syracuseStep 5396795 = 8095193) B8095193
theorem B3597863 : Blo 2245435 3597863 := bstep (se 1 (by rfl) ⟨2698397, by rfl⟩ : syracuseStep 3597863 = 5396795) B5396795
theorem B9594301 : Blo 2245435 9594301 := bstep (se 3 (by rfl) ⟨1798931, by rfl⟩ : syracuseStep 9594301 = 3597863) B3597863
theorem B12792401 : Blo 2245435 12792401 := bstep (se 2 (by rfl) ⟨4797150, by rfl⟩ : syracuseStep 12792401 = 9594301) B9594301
theorem B8528267 : Blo 2245435 8528267 := bstep (se 1 (by rfl) ⟨6396200, by rfl⟩ : syracuseStep 8528267 = 12792401) B12792401
theorem B5685511 : Blo 2245435 5685511 := bstep (se 1 (by rfl) ⟨4264133, by rfl⟩ : syracuseStep 5685511 = 8528267) B8528267
theorem B7580681 : Blo 2245435 7580681 := bstep (se 2 (by rfl) ⟨2842755, by rfl⟩ : syracuseStep 7580681 = 5685511) B5685511
theorem B5053787 : Blo 2245435 5053787 := bstep (se 1 (by rfl) ⟨3790340, by rfl⟩ : syracuseStep 5053787 = 7580681) B7580681
theorem B3369191 : Blo 2245435 3369191 := bstep (se 1 (by rfl) ⟨2526893, by rfl⟩ : syracuseStep 3369191 = 5053787) B5053787
theorem B2246127 : Blo 2245435 2246127 := bstep (se 1 (by rfl) ⟨1684595, by rfl⟩ : syracuseStep 2246127 = 3369191) B3369191
theorem B3369197 : Blo 2245435 3369197 := bbase (se 3 (by rfl) ⟨631724, by rfl⟩ : syracuseStep 3369197 = 1263449) (by norm_num)
theorem B2246131 : Blo 2245435 2246131 := bstep (se 1 (by rfl) ⟨1684598, by rfl⟩ : syracuseStep 2246131 = 3369197) B3369197
theorem B5053805 : Blo 2245435 5053805 := bbase (se 3 (by rfl) ⟨947588, by rfl⟩ : syracuseStep 5053805 = 1895177) (by norm_num)
theorem B3369203 : Blo 2245435 3369203 := bstep (se 1 (by rfl) ⟨2526902, by rfl⟩ : syracuseStep 3369203 = 5053805) B5053805
theorem B2246135 : Blo 2245435 2246135 := bstep (se 1 (by rfl) ⟨1684601, by rfl⟩ : syracuseStep 2246135 = 3369203) B3369203
theorem B4264157 : Blo 2245435 4264157 := bbase (se 3 (by rfl) ⟨799529, by rfl⟩ : syracuseStep 4264157 = 1599059) (by norm_num)
theorem B2842771 : Blo 2245435 2842771 := bstep (se 1 (by rfl) ⟨2132078, by rfl⟩ : syracuseStep 2842771 = 4264157) B4264157
theorem B3790361 : Blo 2245435 3790361 := bstep (se 2 (by rfl) ⟨1421385, by rfl⟩ : syracuseStep 3790361 = 2842771) B2842771
theorem B2526907 : Blo 2245435 2526907 := bstep (se 1 (by rfl) ⟨1895180, by rfl⟩ : syracuseStep 2526907 = 3790361) B3790361
theorem B3369209 : Blo 2245435 3369209 := bstep (se 2 (by rfl) ⟨1263453, by rfl⟩ : syracuseStep 3369209 = 2526907) B2526907
theorem B2246139 : Blo 2245435 2246139 := bstep (se 1 (by rfl) ⟨1684604, by rfl⟩ : syracuseStep 2246139 = 3369209) B3369209
theorem B2276789 : Blo 2245435 2276789 := bbase (se 5 (by rfl) ⟨106724, by rfl⟩ : syracuseStep 2276789 = 213449) (by norm_num)
theorem B6071437 : Blo 2245435 6071437 := bstep (se 3 (by rfl) ⟨1138394, by rfl⟩ : syracuseStep 6071437 = 2276789) B2276789
theorem B8095249 : Blo 2245435 8095249 := bstep (se 2 (by rfl) ⟨3035718, by rfl⟩ : syracuseStep 8095249 = 6071437) B6071437
theorem B10793665 : Blo 2245435 10793665 := bstep (se 2 (by rfl) ⟨4047624, by rfl⟩ : syracuseStep 10793665 = 8095249) B8095249
theorem B57566213 : Blo 2245435 57566213 := bstep (se 4 (by rfl) ⟨5396832, by rfl⟩ : syracuseStep 57566213 = 10793665) B10793665
theorem B38377475 : Blo 2245435 38377475 := bstep (se 1 (by rfl) ⟨28783106, by rfl⟩ : syracuseStep 38377475 = 57566213) B57566213
theorem B25584983 : Blo 2245435 25584983 := bstep (se 1 (by rfl) ⟨19188737, by rfl⟩ : syracuseStep 25584983 = 38377475) B38377475
theorem B17056655 : Blo 2245435 17056655 := bstep (se 1 (by rfl) ⟨12792491, by rfl⟩ : syracuseStep 17056655 = 25584983) B25584983
theorem B11371103 : Blo 2245435 11371103 := bstep (se 1 (by rfl) ⟨8528327, by rfl⟩ : syracuseStep 11371103 = 17056655) B17056655
theorem B7580735 : Blo 2245435 7580735 := bstep (se 1 (by rfl) ⟨5685551, by rfl⟩ : syracuseStep 7580735 = 11371103) B11371103
theorem B5053823 : Blo 2245435 5053823 := bstep (se 1 (by rfl) ⟨3790367, by rfl⟩ : syracuseStep 5053823 = 7580735) B7580735
theorem B3369215 : Blo 2245435 3369215 := bstep (se 1 (by rfl) ⟨2526911, by rfl⟩ : syracuseStep 3369215 = 5053823) B5053823
theorem B2246143 : Blo 2245435 2246143 := bstep (se 1 (by rfl) ⟨1684607, by rfl⟩ : syracuseStep 2246143 = 3369215) B3369215
theorem B3369221 : Blo 2245435 3369221 := bbase (se 4 (by rfl) ⟨315864, by rfl⟩ : syracuseStep 3369221 = 631729) (by norm_num)
theorem B2246147 : Blo 2245435 2246147 := bstep (se 1 (by rfl) ⟨1684610, by rfl⟩ : syracuseStep 2246147 = 3369221) B3369221
theorem B3790381 : Blo 2245435 3790381 := bbase (se 3 (by rfl) ⟨710696, by rfl⟩ : syracuseStep 3790381 = 1421393) (by norm_num)
theorem B5053841 : Blo 2245435 5053841 := bstep (se 2 (by rfl) ⟨1895190, by rfl⟩ : syracuseStep 5053841 = 3790381) B3790381
theorem B3369227 : Blo 2245435 3369227 := bstep (se 1 (by rfl) ⟨2526920, by rfl⟩ : syracuseStep 3369227 = 5053841) B5053841
theorem B2246151 : Blo 2245435 2246151 := bstep (se 1 (by rfl) ⟨1684613, by rfl⟩ : syracuseStep 2246151 = 3369227) B3369227
theorem B2526925 : Blo 2245435 2526925 := bbase (se 3 (by rfl) ⟨473798, by rfl⟩ : syracuseStep 2526925 = 947597) (by norm_num)
theorem B3369233 : Blo 2245435 3369233 := bstep (se 2 (by rfl) ⟨1263462, by rfl⟩ : syracuseStep 3369233 = 2526925) B2526925
theorem B2246155 : Blo 2245435 2246155 := bstep (se 1 (by rfl) ⟨1684616, by rfl⟩ : syracuseStep 2246155 = 3369233) B3369233
theorem B7580789 : Blo 2245435 7580789 := bbase (se 5 (by rfl) ⟨355349, by rfl⟩ : syracuseStep 7580789 = 710699) (by norm_num)
theorem B5053859 : Blo 2245435 5053859 := bstep (se 1 (by rfl) ⟨3790394, by rfl⟩ : syracuseStep 5053859 = 7580789) B7580789
theorem B3369239 : Blo 2245435 3369239 := bstep (se 1 (by rfl) ⟨2526929, by rfl⟩ : syracuseStep 3369239 = 5053859) B5053859
theorem B2246159 : Blo 2245435 2246159 := bstep (se 1 (by rfl) ⟨1684619, by rfl⟩ : syracuseStep 2246159 = 3369239) B3369239
theorem B3369245 : Blo 2245435 3369245 := bbase (se 3 (by rfl) ⟨631733, by rfl⟩ : syracuseStep 3369245 = 1263467) (by norm_num)
theorem B2246163 : Blo 2245435 2246163 := bstep (se 1 (by rfl) ⟨1684622, by rfl⟩ : syracuseStep 2246163 = 3369245) B3369245
theorem B5053877 : Blo 2245435 5053877 := bbase (se 5 (by rfl) ⟨236900, by rfl⟩ : syracuseStep 5053877 = 473801) (by norm_num)
theorem B3369251 : Blo 2245435 3369251 := bstep (se 1 (by rfl) ⟨2526938, by rfl⟩ : syracuseStep 3369251 = 5053877) B5053877
theorem B2246167 : Blo 2245435 2246167 := bstep (se 1 (by rfl) ⟨1684625, by rfl⟩ : syracuseStep 2246167 = 3369251) B3369251
theorem B4797245 : Blo 2245435 4797245 := bbase (se 3 (by rfl) ⟨899483, by rfl⟩ : syracuseStep 4797245 = 1798967) (by norm_num)
theorem B12792653 : Blo 2245435 12792653 := bstep (se 3 (by rfl) ⟨2398622, by rfl⟩ : syracuseStep 12792653 = 4797245) B4797245
theorem B8528435 : Blo 2245435 8528435 := bstep (se 1 (by rfl) ⟨6396326, by rfl⟩ : syracuseStep 8528435 = 12792653) B12792653
theorem B5685623 : Blo 2245435 5685623 := bstep (se 1 (by rfl) ⟨4264217, by rfl⟩ : syracuseStep 5685623 = 8528435) B8528435
theorem B3790415 : Blo 2245435 3790415 := bstep (se 1 (by rfl) ⟨2842811, by rfl⟩ : syracuseStep 3790415 = 5685623) B5685623
theorem B2526943 : Blo 2245435 2526943 := bstep (se 1 (by rfl) ⟨1895207, by rfl⟩ : syracuseStep 2526943 = 3790415) B3790415
theorem B3369257 : Blo 2245435 3369257 := bstep (se 2 (by rfl) ⟨1263471, by rfl⟩ : syracuseStep 3369257 = 2526943) B2526943
theorem B2246171 : Blo 2245435 2246171 := bstep (se 1 (by rfl) ⟨1684628, by rfl⟩ : syracuseStep 2246171 = 3369257) B3369257
theorem B4797253 : Blo 2245435 4797253 := bbase (se 4 (by rfl) ⟨449742, by rfl⟩ : syracuseStep 4797253 = 899485) (by norm_num)
theorem B6396337 : Blo 2245435 6396337 := bstep (se 2 (by rfl) ⟨2398626, by rfl⟩ : syracuseStep 6396337 = 4797253) B4797253
theorem B8528449 : Blo 2245435 8528449 := bstep (se 2 (by rfl) ⟨3198168, by rfl⟩ : syracuseStep 8528449 = 6396337) B6396337
theorem B11371265 : Blo 2245435 11371265 := bstep (se 2 (by rfl) ⟨4264224, by rfl⟩ : syracuseStep 11371265 = 8528449) B8528449
theorem B7580843 : Blo 2245435 7580843 := bstep (se 1 (by rfl) ⟨5685632, by rfl⟩ : syracuseStep 7580843 = 11371265) B11371265
theorem B5053895 : Blo 2245435 5053895 := bstep (se 1 (by rfl) ⟨3790421, by rfl⟩ : syracuseStep 5053895 = 7580843) B7580843
theorem B3369263 : Blo 2245435 3369263 := bstep (se 1 (by rfl) ⟨2526947, by rfl⟩ : syracuseStep 3369263 = 5053895) B5053895
theorem B2246175 : Blo 2245435 2246175 := bstep (se 1 (by rfl) ⟨1684631, by rfl⟩ : syracuseStep 2246175 = 3369263) B3369263
theorem B3369269 : Blo 2245435 3369269 := bbase (se 5 (by rfl) ⟨157934, by rfl⟩ : syracuseStep 3369269 = 315869) (by norm_num)
theorem B2246179 : Blo 2245435 2246179 := bstep (se 1 (by rfl) ⟨1684634, by rfl⟩ : syracuseStep 2246179 = 3369269) B3369269
theorem B5685653 : Blo 2245435 5685653 := bbase (se 6 (by rfl) ⟨133257, by rfl⟩ : syracuseStep 5685653 = 266515) (by norm_num)
theorem B3790435 : Blo 2245435 3790435 := bstep (se 1 (by rfl) ⟨2842826, by rfl⟩ : syracuseStep 3790435 = 5685653) B5685653
theorem B5053913 : Blo 2245435 5053913 := bstep (se 2 (by rfl) ⟨1895217, by rfl⟩ : syracuseStep 5053913 = 3790435) B3790435
theorem B3369275 : Blo 2245435 3369275 := bstep (se 1 (by rfl) ⟨2526956, by rfl⟩ : syracuseStep 3369275 = 5053913) B5053913
theorem B2246183 : Blo 2245435 2246183 := bstep (se 1 (by rfl) ⟨1684637, by rfl⟩ : syracuseStep 2246183 = 3369275) B3369275
theorem B2526961 : Blo 2245435 2526961 := bbase (se 2 (by rfl) ⟨947610, by rfl⟩ : syracuseStep 2526961 = 1895221) (by norm_num)
theorem B3369281 : Blo 2245435 3369281 := bstep (se 2 (by rfl) ⟨1263480, by rfl⟩ : syracuseStep 3369281 = 2526961) B2526961
theorem B2246187 : Blo 2245435 2246187 := bstep (se 1 (by rfl) ⟨1684640, by rfl⟩ : syracuseStep 2246187 = 3369281) B3369281
theorem B34579477 : Blo 2245435 34579477 := bbase (se 6 (by rfl) ⟨810456, by rfl⟩ : syracuseStep 34579477 = 1620913) (by norm_num)
theorem B46105969 : Blo 2245435 46105969 := bstep (se 2 (by rfl) ⟨17289738, by rfl⟩ : syracuseStep 46105969 = 34579477) B34579477
theorem B61474625 : Blo 2245435 61474625 := bstep (se 2 (by rfl) ⟨23052984, by rfl⟩ : syracuseStep 61474625 = 46105969) B46105969
theorem B40983083 : Blo 2245435 40983083 := bstep (se 1 (by rfl) ⟨30737312, by rfl⟩ : syracuseStep 40983083 = 61474625) B61474625
theorem B27322055 : Blo 2245435 27322055 := bstep (se 1 (by rfl) ⟨20491541, by rfl⟩ : syracuseStep 27322055 = 40983083) B40983083
theorem B18214703 : Blo 2245435 18214703 := bstep (se 1 (by rfl) ⟨13661027, by rfl⟩ : syracuseStep 18214703 = 27322055) B27322055
theorem B12143135 : Blo 2245435 12143135 := bstep (se 1 (by rfl) ⟨9107351, by rfl⟩ : syracuseStep 12143135 = 18214703) B18214703
theorem B32381693 : Blo 2245435 32381693 := bstep (se 3 (by rfl) ⟨6071567, by rfl⟩ : syracuseStep 32381693 = 12143135) B12143135
theorem B21587795 : Blo 2245435 21587795 := bstep (se 1 (by rfl) ⟨16190846, by rfl⟩ : syracuseStep 21587795 = 32381693) B32381693
theorem B14391863 : Blo 2245435 14391863 := bstep (se 1 (by rfl) ⟨10793897, by rfl⟩ : syracuseStep 14391863 = 21587795) B21587795
theorem B9594575 : Blo 2245435 9594575 := bstep (se 1 (by rfl) ⟨7195931, by rfl⟩ : syracuseStep 9594575 = 14391863) B14391863
theorem B6396383 : Blo 2245435 6396383 := bstep (se 1 (by rfl) ⟨4797287, by rfl⟩ : syracuseStep 6396383 = 9594575) B9594575
theorem B4264255 : Blo 2245435 4264255 := bstep (se 1 (by rfl) ⟨3198191, by rfl⟩ : syracuseStep 4264255 = 6396383) B6396383
theorem B5685673 : Blo 2245435 5685673 := bstep (se 2 (by rfl) ⟨2132127, by rfl⟩ : syracuseStep 5685673 = 4264255) B4264255
theorem B7580897 : Blo 2245435 7580897 := bstep (se 2 (by rfl) ⟨2842836, by rfl⟩ : syracuseStep 7580897 = 5685673) B5685673
theorem B5053931 : Blo 2245435 5053931 := bstep (se 1 (by rfl) ⟨3790448, by rfl⟩ : syracuseStep 5053931 = 7580897) B7580897
theorem B3369287 : Blo 2245435 3369287 := bstep (se 1 (by rfl) ⟨2526965, by rfl⟩ : syracuseStep 3369287 = 5053931) B5053931
theorem B2246191 : Blo 2245435 2246191 := bstep (se 1 (by rfl) ⟨1684643, by rfl⟩ : syracuseStep 2246191 = 3369287) B3369287
theorem B3369293 : Blo 2245435 3369293 := bbase (se 3 (by rfl) ⟨631742, by rfl⟩ : syracuseStep 3369293 = 1263485) (by norm_num)
theorem B2246195 : Blo 2245435 2246195 := bstep (se 1 (by rfl) ⟨1684646, by rfl⟩ : syracuseStep 2246195 = 3369293) B3369293
theorem B5053949 : Blo 2245435 5053949 := bbase (se 3 (by rfl) ⟨947615, by rfl⟩ : syracuseStep 5053949 = 1895231) (by norm_num)
theorem B3369299 : Blo 2245435 3369299 := bstep (se 1 (by rfl) ⟨2526974, by rfl⟩ : syracuseStep 3369299 = 5053949) B5053949
theorem B2246199 : Blo 2245435 2246199 := bstep (se 1 (by rfl) ⟨1684649, by rfl⟩ : syracuseStep 2246199 = 3369299) B3369299
theorem B3790469 : Blo 2245435 3790469 := bbase (se 4 (by rfl) ⟨355356, by rfl⟩ : syracuseStep 3790469 = 710713) (by norm_num)
theorem B2526979 : Blo 2245435 2526979 := bstep (se 1 (by rfl) ⟨1895234, by rfl⟩ : syracuseStep 2526979 = 3790469) B3790469
theorem B3369305 : Blo 2245435 3369305 := bstep (se 2 (by rfl) ⟨1263489, by rfl⟩ : syracuseStep 3369305 = 2526979) B2526979
theorem B2246203 : Blo 2245435 2246203 := bstep (se 1 (by rfl) ⟨1684652, by rfl⟩ : syracuseStep 2246203 = 3369305) B3369305
theorem B17057141 : Blo 2245435 17057141 := bbase (se 5 (by rfl) ⟨799553, by rfl⟩ : syracuseStep 17057141 = 1599107) (by norm_num)
theorem B11371427 : Blo 2245435 11371427 := bstep (se 1 (by rfl) ⟨8528570, by rfl⟩ : syracuseStep 11371427 = 17057141) B17057141
theorem B7580951 : Blo 2245435 7580951 := bstep (se 1 (by rfl) ⟨5685713, by rfl⟩ : syracuseStep 7580951 = 11371427) B11371427
theorem B5053967 : Blo 2245435 5053967 := bstep (se 1 (by rfl) ⟨3790475, by rfl⟩ : syracuseStep 5053967 = 7580951) B7580951
theorem B3369311 : Blo 2245435 3369311 := bstep (se 1 (by rfl) ⟨2526983, by rfl⟩ : syracuseStep 3369311 = 5053967) B5053967
theorem B2246207 : Blo 2245435 2246207 := bstep (se 1 (by rfl) ⟨1684655, by rfl⟩ : syracuseStep 2246207 = 3369311) B3369311
theorem B3369317 : Blo 2245435 3369317 := bbase (se 4 (by rfl) ⟨315873, by rfl⟩ : syracuseStep 3369317 = 631747) (by norm_num)
theorem B2246211 : Blo 2245435 2246211 := bstep (se 1 (by rfl) ⟨1684658, by rfl⟩ : syracuseStep 2246211 = 3369317) B3369317
theorem B4264301 : Blo 2245435 4264301 := bbase (se 3 (by rfl) ⟨799556, by rfl⟩ : syracuseStep 4264301 = 1599113) (by norm_num)
theorem B2842867 : Blo 2245435 2842867 := bstep (se 1 (by rfl) ⟨2132150, by rfl⟩ : syracuseStep 2842867 = 4264301) B4264301
theorem B3790489 : Blo 2245435 3790489 := bstep (se 2 (by rfl) ⟨1421433, by rfl⟩ : syracuseStep 3790489 = 2842867) B2842867
theorem B5053985 : Blo 2245435 5053985 := bstep (se 2 (by rfl) ⟨1895244, by rfl⟩ : syracuseStep 5053985 = 3790489) B3790489
theorem B3369323 : Blo 2245435 3369323 := bstep (se 1 (by rfl) ⟨2526992, by rfl⟩ : syracuseStep 3369323 = 5053985) B5053985
theorem B2246215 : Blo 2245435 2246215 := bstep (se 1 (by rfl) ⟨1684661, by rfl⟩ : syracuseStep 2246215 = 3369323) B3369323
theorem B2526997 : Blo 2245435 2526997 := bbase (se 6 (by rfl) ⟨59226, by rfl⟩ : syracuseStep 2526997 = 118453) (by norm_num)
theorem B3369329 : Blo 2245435 3369329 := bstep (se 2 (by rfl) ⟨1263498, by rfl⟩ : syracuseStep 3369329 = 2526997) B2526997
theorem B2246219 : Blo 2245435 2246219 := bstep (se 1 (by rfl) ⟨1684664, by rfl⟩ : syracuseStep 2246219 = 3369329) B3369329
theorem B2842877 : Blo 2245435 2842877 := bbase (se 3 (by rfl) ⟨533039, by rfl⟩ : syracuseStep 2842877 = 1066079) (by norm_num)
theorem B7581005 : Blo 2245435 7581005 := bstep (se 3 (by rfl) ⟨1421438, by rfl⟩ : syracuseStep 7581005 = 2842877) B2842877
theorem B5054003 : Blo 2245435 5054003 := bstep (se 1 (by rfl) ⟨3790502, by rfl⟩ : syracuseStep 5054003 = 7581005) B7581005
theorem B3369335 : Blo 2245435 3369335 := bstep (se 1 (by rfl) ⟨2527001, by rfl⟩ : syracuseStep 3369335 = 5054003) B5054003
theorem B2246223 : Blo 2245435 2246223 := bstep (se 1 (by rfl) ⟨1684667, by rfl⟩ : syracuseStep 2246223 = 3369335) B3369335
theorem B3369341 : Blo 2245435 3369341 := bbase (se 3 (by rfl) ⟨631751, by rfl⟩ : syracuseStep 3369341 = 1263503) (by norm_num)
theorem B2246227 : Blo 2245435 2246227 := bstep (se 1 (by rfl) ⟨1684670, by rfl⟩ : syracuseStep 2246227 = 3369341) B3369341
theorem B5054021 : Blo 2245435 5054021 := bbase (se 4 (by rfl) ⟨473814, by rfl⟩ : syracuseStep 5054021 = 947629) (by norm_num)
theorem B3369347 : Blo 2245435 3369347 := bstep (se 1 (by rfl) ⟨2527010, by rfl⟩ : syracuseStep 3369347 = 5054021) B5054021
theorem B2246231 : Blo 2245435 2246231 := bstep (se 1 (by rfl) ⟨1684673, by rfl⟩ : syracuseStep 2246231 = 3369347) B3369347
theorem B3598037 : Blo 2245435 3598037 := bbase (se 7 (by rfl) ⟨42164, by rfl⟩ : syracuseStep 3598037 = 84329) (by norm_num)
theorem B2398691 : Blo 2245435 2398691 := bstep (se 1 (by rfl) ⟨1799018, by rfl⟩ : syracuseStep 2398691 = 3598037) B3598037
theorem B6396509 : Blo 2245435 6396509 := bstep (se 3 (by rfl) ⟨1199345, by rfl⟩ : syracuseStep 6396509 = 2398691) B2398691
theorem B4264339 : Blo 2245435 4264339 := bstep (se 1 (by rfl) ⟨3198254, by rfl⟩ : syracuseStep 4264339 = 6396509) B6396509
theorem B5685785 : Blo 2245435 5685785 := bstep (se 2 (by rfl) ⟨2132169, by rfl⟩ : syracuseStep 5685785 = 4264339) B4264339
theorem B3790523 : Blo 2245435 3790523 := bstep (se 1 (by rfl) ⟨2842892, by rfl⟩ : syracuseStep 3790523 = 5685785) B5685785
theorem B2527015 : Blo 2245435 2527015 := bstep (se 1 (by rfl) ⟨1895261, by rfl⟩ : syracuseStep 2527015 = 3790523) B3790523
theorem B3369353 : Blo 2245435 3369353 := bstep (se 2 (by rfl) ⟨1263507, by rfl⟩ : syracuseStep 3369353 = 2527015) B2527015
theorem B2246235 : Blo 2245435 2246235 := bstep (se 1 (by rfl) ⟨1684676, by rfl⟩ : syracuseStep 2246235 = 3369353) B3369353
theorem B11371589 : Blo 2245435 11371589 := bbase (se 4 (by rfl) ⟨1066086, by rfl⟩ : syracuseStep 11371589 = 2132173) (by norm_num)
theorem B7581059 : Blo 2245435 7581059 := bstep (se 1 (by rfl) ⟨5685794, by rfl⟩ : syracuseStep 7581059 = 11371589) B11371589
theorem B5054039 : Blo 2245435 5054039 := bstep (se 1 (by rfl) ⟨3790529, by rfl⟩ : syracuseStep 5054039 = 7581059) B7581059
theorem B3369359 : Blo 2245435 3369359 := bstep (se 1 (by rfl) ⟨2527019, by rfl⟩ : syracuseStep 3369359 = 5054039) B5054039
theorem B2246239 : Blo 2245435 2246239 := bstep (se 1 (by rfl) ⟨1684679, by rfl⟩ : syracuseStep 2246239 = 3369359) B3369359
theorem B3369365 : Blo 2245435 3369365 := bbase (se 6 (by rfl) ⟨78969, by rfl⟩ : syracuseStep 3369365 = 157939) (by norm_num)
theorem B2246243 : Blo 2245435 2246243 := bstep (se 1 (by rfl) ⟨1684682, by rfl⟩ : syracuseStep 2246243 = 3369365) B3369365
theorem B3509173 : Blo 2245435 3509173 := bbase (se 5 (by rfl) ⟨164492, by rfl⟩ : syracuseStep 3509173 = 328985) (by norm_num)
theorem B4678897 : Blo 2245435 4678897 := bstep (se 2 (by rfl) ⟨1754586, by rfl⟩ : syracuseStep 4678897 = 3509173) B3509173
theorem B6238529 : Blo 2245435 6238529 := bstep (se 2 (by rfl) ⟨2339448, by rfl⟩ : syracuseStep 6238529 = 4678897) B4678897
theorem B4159019 : Blo 2245435 4159019 := bstep (se 1 (by rfl) ⟨3119264, by rfl⟩ : syracuseStep 4159019 = 6238529) B6238529
theorem B11090717 : Blo 2245435 11090717 := bstep (se 3 (by rfl) ⟨2079509, by rfl⟩ : syracuseStep 11090717 = 4159019) B4159019
theorem B118300981 : Blo 2245435 118300981 := bstep (se 5 (by rfl) ⟨5545358, by rfl⟩ : syracuseStep 118300981 = 11090717) B11090717
theorem B157734641 : Blo 2245435 157734641 := bstep (se 2 (by rfl) ⟨59150490, by rfl⟩ : syracuseStep 157734641 = 118300981) B118300981
theorem B420625709 : Blo 2245435 420625709 := bstep (se 3 (by rfl) ⟨78867320, by rfl⟩ : syracuseStep 420625709 = 157734641) B157734641
theorem B280417139 : Blo 2245435 280417139 := bstep (se 1 (by rfl) ⟨210312854, by rfl⟩ : syracuseStep 280417139 = 420625709) B420625709
theorem B186944759 : Blo 2245435 186944759 := bstep (se 1 (by rfl) ⟨140208569, by rfl⟩ : syracuseStep 186944759 = 280417139) B280417139
theorem B124629839 : Blo 2245435 124629839 := bstep (se 1 (by rfl) ⟨93472379, by rfl⟩ : syracuseStep 124629839 = 186944759) B186944759
theorem B83086559 : Blo 2245435 83086559 := bstep (se 1 (by rfl) ⟨62314919, by rfl⟩ : syracuseStep 83086559 = 124629839) B124629839
theorem B55391039 : Blo 2245435 55391039 := bstep (se 1 (by rfl) ⟨41543279, by rfl⟩ : syracuseStep 55391039 = 83086559) B83086559
theorem B36927359 : Blo 2245435 36927359 := bstep (se 1 (by rfl) ⟨27695519, by rfl⟩ : syracuseStep 36927359 = 55391039) B55391039
theorem B24618239 : Blo 2245435 24618239 := bstep (se 1 (by rfl) ⟨18463679, by rfl⟩ : syracuseStep 24618239 = 36927359) B36927359
theorem B16412159 : Blo 2245435 16412159 := bstep (se 1 (by rfl) ⟨12309119, by rfl⟩ : syracuseStep 16412159 = 24618239) B24618239
theorem B10941439 : Blo 2245435 10941439 := bstep (se 1 (by rfl) ⟨8206079, by rfl⟩ : syracuseStep 10941439 = 16412159) B16412159
theorem B14588585 : Blo 2245435 14588585 := bstep (se 2 (by rfl) ⟨5470719, by rfl⟩ : syracuseStep 14588585 = 10941439) B10941439
theorem B9725723 : Blo 2245435 9725723 := bstep (se 1 (by rfl) ⟨7294292, by rfl⟩ : syracuseStep 9725723 = 14588585) B14588585
theorem B6483815 : Blo 2245435 6483815 := bstep (se 1 (by rfl) ⟨4862861, by rfl⟩ : syracuseStep 6483815 = 9725723) B9725723
theorem B4322543 : Blo 2245435 4322543 := bstep (se 1 (by rfl) ⟨3241907, by rfl⟩ : syracuseStep 4322543 = 6483815) B6483815
theorem B11526781 : Blo 2245435 11526781 := bstep (se 3 (by rfl) ⟨2161271, by rfl⟩ : syracuseStep 11526781 = 4322543) B4322543
theorem B15369041 : Blo 2245435 15369041 := bstep (se 2 (by rfl) ⟨5763390, by rfl⟩ : syracuseStep 15369041 = 11526781) B11526781
theorem B10246027 : Blo 2245435 10246027 := bstep (se 1 (by rfl) ⟨7684520, by rfl⟩ : syracuseStep 10246027 = 15369041) B15369041
theorem B13661369 : Blo 2245435 13661369 := bstep (se 2 (by rfl) ⟨5123013, by rfl⟩ : syracuseStep 13661369 = 10246027) B10246027
theorem B9107579 : Blo 2245435 9107579 := bstep (se 1 (by rfl) ⟨6830684, by rfl⟩ : syracuseStep 9107579 = 13661369) B13661369
theorem B24286877 : Blo 2245435 24286877 := bstep (se 3 (by rfl) ⟨4553789, by rfl⟩ : syracuseStep 24286877 = 9107579) B9107579
theorem B16191251 : Blo 2245435 16191251 := bstep (se 1 (by rfl) ⟨12143438, by rfl⟩ : syracuseStep 16191251 = 24286877) B24286877
theorem B10794167 : Blo 2245435 10794167 := bstep (se 1 (by rfl) ⟨8095625, by rfl⟩ : syracuseStep 10794167 = 16191251) B16191251
theorem B7196111 : Blo 2245435 7196111 := bstep (se 1 (by rfl) ⟨5397083, by rfl⟩ : syracuseStep 7196111 = 10794167) B10794167
theorem B4797407 : Blo 2245435 4797407 := bstep (se 1 (by rfl) ⟨3598055, by rfl⟩ : syracuseStep 4797407 = 7196111) B7196111
theorem B12793085 : Blo 2245435 12793085 := bstep (se 3 (by rfl) ⟨2398703, by rfl⟩ : syracuseStep 12793085 = 4797407) B4797407
theorem B8528723 : Blo 2245435 8528723 := bstep (se 1 (by rfl) ⟨6396542, by rfl⟩ : syracuseStep 8528723 = 12793085) B12793085
theorem B5685815 : Blo 2245435 5685815 := bstep (se 1 (by rfl) ⟨4264361, by rfl⟩ : syracuseStep 5685815 = 8528723) B8528723
theorem B3790543 : Blo 2245435 3790543 := bstep (se 1 (by rfl) ⟨2842907, by rfl⟩ : syracuseStep 3790543 = 5685815) B5685815
theorem B5054057 : Blo 2245435 5054057 := bstep (se 2 (by rfl) ⟨1895271, by rfl⟩ : syracuseStep 5054057 = 3790543) B3790543
theorem B3369371 : Blo 2245435 3369371 := bstep (se 1 (by rfl) ⟨2527028, by rfl⟩ : syracuseStep 3369371 = 5054057) B5054057
theorem B2246247 : Blo 2245435 2246247 := bstep (se 1 (by rfl) ⟨1684685, by rfl⟩ : syracuseStep 2246247 = 3369371) B3369371
theorem B2527033 : Blo 2245435 2527033 := bbase (se 2 (by rfl) ⟨947637, by rfl⟩ : syracuseStep 2527033 = 1895275) (by norm_num)
theorem B3369377 : Blo 2245435 3369377 := bstep (se 2 (by rfl) ⟨1263516, by rfl⟩ : syracuseStep 3369377 = 2527033) B2527033
theorem B2246251 : Blo 2245435 2246251 := bstep (se 1 (by rfl) ⟨1684688, by rfl⟩ : syracuseStep 2246251 = 3369377) B3369377
theorem B6396565 : Blo 2245435 6396565 := bbase (se 6 (by rfl) ⟨149919, by rfl⟩ : syracuseStep 6396565 = 299839) (by norm_num)
theorem B8528753 : Blo 2245435 8528753 := bstep (se 2 (by rfl) ⟨3198282, by rfl⟩ : syracuseStep 8528753 = 6396565) B6396565
theorem B5685835 : Blo 2245435 5685835 := bstep (se 1 (by rfl) ⟨4264376, by rfl⟩ : syracuseStep 5685835 = 8528753) B8528753
theorem B7581113 : Blo 2245435 7581113 := bstep (se 2 (by rfl) ⟨2842917, by rfl⟩ : syracuseStep 7581113 = 5685835) B5685835
theorem B5054075 : Blo 2245435 5054075 := bstep (se 1 (by rfl) ⟨3790556, by rfl⟩ : syracuseStep 5054075 = 7581113) B7581113
theorem B3369383 : Blo 2245435 3369383 := bstep (se 1 (by rfl) ⟨2527037, by rfl⟩ : syracuseStep 3369383 = 5054075) B5054075
theorem B2246255 : Blo 2245435 2246255 := bstep (se 1 (by rfl) ⟨1684691, by rfl⟩ : syracuseStep 2246255 = 3369383) B3369383
theorem B3369389 : Blo 2245435 3369389 := bbase (se 3 (by rfl) ⟨631760, by rfl⟩ : syracuseStep 3369389 = 1263521) (by norm_num)
theorem B2246259 : Blo 2245435 2246259 := bstep (se 1 (by rfl) ⟨1684694, by rfl⟩ : syracuseStep 2246259 = 3369389) B3369389
theorem B5054093 : Blo 2245435 5054093 := bbase (se 3 (by rfl) ⟨947642, by rfl⟩ : syracuseStep 5054093 = 1895285) (by norm_num)
theorem B3369395 : Blo 2245435 3369395 := bstep (se 1 (by rfl) ⟨2527046, by rfl⟩ : syracuseStep 3369395 = 5054093) B5054093
theorem B2246263 : Blo 2245435 2246263 := bstep (se 1 (by rfl) ⟨1684697, by rfl⟩ : syracuseStep 2246263 = 3369395) B3369395
theorem B2842933 : Blo 2245435 2842933 := bbase (se 5 (by rfl) ⟨133262, by rfl⟩ : syracuseStep 2842933 = 266525) (by norm_num)
theorem B3790577 : Blo 2245435 3790577 := bstep (se 2 (by rfl) ⟨1421466, by rfl⟩ : syracuseStep 3790577 = 2842933) B2842933
theorem B2527051 : Blo 2245435 2527051 := bstep (se 1 (by rfl) ⟨1895288, by rfl⟩ : syracuseStep 2527051 = 3790577) B3790577
theorem B3369401 : Blo 2245435 3369401 := bstep (se 2 (by rfl) ⟨1263525, by rfl⟩ : syracuseStep 3369401 = 2527051) B2527051
theorem B2246267 : Blo 2245435 2246267 := bstep (se 1 (by rfl) ⟨1684700, by rfl⟩ : syracuseStep 2246267 = 3369401) B3369401
theorem B8763125 : Blo 2245435 8763125 := bbase (se 5 (by rfl) ⟨410771, by rfl⟩ : syracuseStep 8763125 = 821543) (by norm_num)
theorem B23368333 : Blo 2245435 23368333 := bstep (se 3 (by rfl) ⟨4381562, by rfl⟩ : syracuseStep 23368333 = 8763125) B8763125
theorem B31157777 : Blo 2245435 31157777 := bstep (se 2 (by rfl) ⟨11684166, by rfl⟩ : syracuseStep 31157777 = 23368333) B23368333
theorem B20771851 : Blo 2245435 20771851 := bstep (se 1 (by rfl) ⟨15578888, by rfl⟩ : syracuseStep 20771851 = 31157777) B31157777
theorem B27695801 : Blo 2245435 27695801 := bstep (se 2 (by rfl) ⟨10385925, by rfl⟩ : syracuseStep 27695801 = 20771851) B20771851
theorem B73855469 : Blo 2245435 73855469 := bstep (se 3 (by rfl) ⟨13847900, by rfl⟩ : syracuseStep 73855469 = 27695801) B27695801
theorem B49236979 : Blo 2245435 49236979 := bstep (se 1 (by rfl) ⟨36927734, by rfl⟩ : syracuseStep 49236979 = 73855469) B73855469
theorem B65649305 : Blo 2245435 65649305 := bstep (se 2 (by rfl) ⟨24618489, by rfl⟩ : syracuseStep 65649305 = 49236979) B49236979
theorem B43766203 : Blo 2245435 43766203 := bstep (se 1 (by rfl) ⟨32824652, by rfl⟩ : syracuseStep 43766203 = 65649305) B65649305
theorem B58354937 : Blo 2245435 58354937 := bstep (se 2 (by rfl) ⟨21883101, by rfl⟩ : syracuseStep 58354937 = 43766203) B43766203
theorem B38903291 : Blo 2245435 38903291 := bstep (se 1 (by rfl) ⟨29177468, by rfl⟩ : syracuseStep 38903291 = 58354937) B58354937
theorem B25935527 : Blo 2245435 25935527 := bstep (se 1 (by rfl) ⟨19451645, by rfl⟩ : syracuseStep 25935527 = 38903291) B38903291
theorem B17290351 : Blo 2245435 17290351 := bstep (se 1 (by rfl) ⟨12967763, by rfl⟩ : syracuseStep 17290351 = 25935527) B25935527
theorem B92215205 : Blo 2245435 92215205 := bstep (se 4 (by rfl) ⟨8645175, by rfl⟩ : syracuseStep 92215205 = 17290351) B17290351
theorem B61476803 : Blo 2245435 61476803 := bstep (se 1 (by rfl) ⟨46107602, by rfl⟩ : syracuseStep 61476803 = 92215205) B92215205
theorem B40984535 : Blo 2245435 40984535 := bstep (se 1 (by rfl) ⟨30738401, by rfl⟩ : syracuseStep 40984535 = 61476803) B61476803
theorem B27323023 : Blo 2245435 27323023 := bstep (se 1 (by rfl) ⟨20492267, by rfl⟩ : syracuseStep 27323023 = 40984535) B40984535
theorem B36430697 : Blo 2245435 36430697 := bstep (se 2 (by rfl) ⟨13661511, by rfl⟩ : syracuseStep 36430697 = 27323023) B27323023
theorem B24287131 : Blo 2245435 24287131 := bstep (se 1 (by rfl) ⟨18215348, by rfl⟩ : syracuseStep 24287131 = 36430697) B36430697
theorem B32382841 : Blo 2245435 32382841 := bstep (se 2 (by rfl) ⟨12143565, by rfl⟩ : syracuseStep 32382841 = 24287131) B24287131
theorem B43177121 : Blo 2245435 43177121 := bstep (se 2 (by rfl) ⟨16191420, by rfl⟩ : syracuseStep 43177121 = 32382841) B32382841
theorem B28784747 : Blo 2245435 28784747 := bstep (se 1 (by rfl) ⟨21588560, by rfl⟩ : syracuseStep 28784747 = 43177121) B43177121
theorem B19189831 : Blo 2245435 19189831 := bstep (se 1 (by rfl) ⟨14392373, by rfl⟩ : syracuseStep 19189831 = 28784747) B28784747
theorem B25586441 : Blo 2245435 25586441 := bstep (se 2 (by rfl) ⟨9594915, by rfl⟩ : syracuseStep 25586441 = 19189831) B19189831
theorem B17057627 : Blo 2245435 17057627 := bstep (se 1 (by rfl) ⟨12793220, by rfl⟩ : syracuseStep 17057627 = 25586441) B25586441
theorem B11371751 : Blo 2245435 11371751 := bstep (se 1 (by rfl) ⟨8528813, by rfl⟩ : syracuseStep 11371751 = 17057627) B17057627
theorem B7581167 : Blo 2245435 7581167 := bstep (se 1 (by rfl) ⟨5685875, by rfl⟩ : syracuseStep 7581167 = 11371751) B11371751
theorem B5054111 : Blo 2245435 5054111 := bstep (se 1 (by rfl) ⟨3790583, by rfl⟩ : syracuseStep 5054111 = 7581167) B7581167
theorem B3369407 : Blo 2245435 3369407 := bstep (se 1 (by rfl) ⟨2527055, by rfl⟩ : syracuseStep 3369407 = 5054111) B5054111
theorem B2246271 : Blo 2245435 2246271 := bstep (se 1 (by rfl) ⟨1684703, by rfl⟩ : syracuseStep 2246271 = 3369407) B3369407
theorem B3369413 : Blo 2245435 3369413 := bbase (se 4 (by rfl) ⟨315882, by rfl⟩ : syracuseStep 3369413 = 631765) (by norm_num)
theorem B2246275 : Blo 2245435 2246275 := bstep (se 1 (by rfl) ⟨1684706, by rfl⟩ : syracuseStep 2246275 = 3369413) B3369413
theorem B3790597 : Blo 2245435 3790597 := bbase (se 4 (by rfl) ⟨355368, by rfl⟩ : syracuseStep 3790597 = 710737) (by norm_num)
theorem B5054129 : Blo 2245435 5054129 := bstep (se 2 (by rfl) ⟨1895298, by rfl⟩ : syracuseStep 5054129 = 3790597) B3790597
theorem B3369419 : Blo 2245435 3369419 := bstep (se 1 (by rfl) ⟨2527064, by rfl⟩ : syracuseStep 3369419 = 5054129) B5054129
theorem B2246279 : Blo 2245435 2246279 := bstep (se 1 (by rfl) ⟨1684709, by rfl⟩ : syracuseStep 2246279 = 3369419) B3369419
theorem B2527069 : Blo 2245435 2527069 := bbase (se 3 (by rfl) ⟨473825, by rfl⟩ : syracuseStep 2527069 = 947651) (by norm_num)
theorem B3369425 : Blo 2245435 3369425 := bstep (se 2 (by rfl) ⟨1263534, by rfl⟩ : syracuseStep 3369425 = 2527069) B2527069
theorem B2246283 : Blo 2245435 2246283 := bstep (se 1 (by rfl) ⟨1684712, by rfl⟩ : syracuseStep 2246283 = 3369425) B3369425
theorem B7581221 : Blo 2245435 7581221 := bbase (se 4 (by rfl) ⟨710739, by rfl⟩ : syracuseStep 7581221 = 1421479) (by norm_num)
theorem B5054147 : Blo 2245435 5054147 := bstep (se 1 (by rfl) ⟨3790610, by rfl⟩ : syracuseStep 5054147 = 7581221) B7581221
theorem B3369431 : Blo 2245435 3369431 := bstep (se 1 (by rfl) ⟨2527073, by rfl⟩ : syracuseStep 3369431 = 5054147) B5054147
theorem B2246287 : Blo 2245435 2246287 := bstep (se 1 (by rfl) ⟨1684715, by rfl⟩ : syracuseStep 2246287 = 3369431) B3369431
theorem B3369437 : Blo 2245435 3369437 := bbase (se 3 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 3369437 = 1263539) (by norm_num)
theorem B2246291 : Blo 2245435 2246291 := bstep (se 1 (by rfl) ⟨1684718, by rfl⟩ : syracuseStep 2246291 = 3369437) B3369437
theorem B5054165 : Blo 2245435 5054165 := bbase (se 7 (by rfl) ⟨59228, by rfl⟩ : syracuseStep 5054165 = 118457) (by norm_num)
theorem B3369443 : Blo 2245435 3369443 := bstep (se 1 (by rfl) ⟨2527082, by rfl⟩ : syracuseStep 3369443 = 5054165) B5054165
theorem B2246295 : Blo 2245435 2246295 := bstep (se 1 (by rfl) ⟨1684721, by rfl⟩ : syracuseStep 2246295 = 3369443) B3369443
theorem B6071861 : Blo 2245435 6071861 := bbase (se 5 (by rfl) ⟨284618, by rfl⟩ : syracuseStep 6071861 = 569237) (by norm_num)
theorem B4047907 : Blo 2245435 4047907 := bstep (se 1 (by rfl) ⟨3035930, by rfl⟩ : syracuseStep 4047907 = 6071861) B6071861
theorem B5397209 : Blo 2245435 5397209 := bstep (se 2 (by rfl) ⟨2023953, by rfl⟩ : syracuseStep 5397209 = 4047907) B4047907
theorem B3598139 : Blo 2245435 3598139 := bstep (se 1 (by rfl) ⟨2698604, by rfl⟩ : syracuseStep 3598139 = 5397209) B5397209
theorem B9595037 : Blo 2245435 9595037 := bstep (se 3 (by rfl) ⟨1799069, by rfl⟩ : syracuseStep 9595037 = 3598139) B3598139
theorem B6396691 : Blo 2245435 6396691 := bstep (se 1 (by rfl) ⟨4797518, by rfl⟩ : syracuseStep 6396691 = 9595037) B9595037
theorem B8528921 : Blo 2245435 8528921 := bstep (se 2 (by rfl) ⟨3198345, by rfl⟩ : syracuseStep 8528921 = 6396691) B6396691
theorem B5685947 : Blo 2245435 5685947 := bstep (se 1 (by rfl) ⟨4264460, by rfl⟩ : syracuseStep 5685947 = 8528921) B8528921
theorem B3790631 : Blo 2245435 3790631 := bstep (se 1 (by rfl) ⟨2842973, by rfl⟩ : syracuseStep 3790631 = 5685947) B5685947
theorem B2527087 : Blo 2245435 2527087 := bstep (se 1 (by rfl) ⟨1895315, by rfl⟩ : syracuseStep 2527087 = 3790631) B3790631
theorem B3369449 : Blo 2245435 3369449 := bstep (se 2 (by rfl) ⟨1263543, by rfl⟩ : syracuseStep 3369449 = 2527087) B2527087
theorem B2246299 : Blo 2245435 2246299 := bstep (se 1 (by rfl) ⟨1684724, by rfl⟩ : syracuseStep 2246299 = 3369449) B3369449
theorem B3077357 : Blo 2245435 3077357 := bbase (se 3 (by rfl) ⟨577004, by rfl⟩ : syracuseStep 3077357 = 1154009) (by norm_num)
theorem B8206285 : Blo 2245435 8206285 := bstep (se 3 (by rfl) ⟨1538678, by rfl⟩ : syracuseStep 8206285 = 3077357) B3077357
theorem B10941713 : Blo 2245435 10941713 := bstep (se 2 (by rfl) ⟨4103142, by rfl⟩ : syracuseStep 10941713 = 8206285) B8206285
theorem B7294475 : Blo 2245435 7294475 := bstep (se 1 (by rfl) ⟨5470856, by rfl⟩ : syracuseStep 7294475 = 10941713) B10941713
theorem B4862983 : Blo 2245435 4862983 := bstep (se 1 (by rfl) ⟨3647237, by rfl⟩ : syracuseStep 4862983 = 7294475) B7294475
theorem B6483977 : Blo 2245435 6483977 := bstep (se 2 (by rfl) ⟨2431491, by rfl⟩ : syracuseStep 6483977 = 4862983) B4862983
theorem B4322651 : Blo 2245435 4322651 := bstep (se 1 (by rfl) ⟨3241988, by rfl⟩ : syracuseStep 4322651 = 6483977) B6483977
theorem B11527069 : Blo 2245435 11527069 := bstep (se 3 (by rfl) ⟨2161325, by rfl⟩ : syracuseStep 11527069 = 4322651) B4322651
theorem B15369425 : Blo 2245435 15369425 := bstep (se 2 (by rfl) ⟨5763534, by rfl⟩ : syracuseStep 15369425 = 11527069) B11527069
theorem B10246283 : Blo 2245435 10246283 := bstep (se 1 (by rfl) ⟨7684712, by rfl⟩ : syracuseStep 10246283 = 15369425) B15369425
theorem B6830855 : Blo 2245435 6830855 := bstep (se 1 (by rfl) ⟨5123141, by rfl⟩ : syracuseStep 6830855 = 10246283) B10246283
theorem B4553903 : Blo 2245435 4553903 := bstep (se 1 (by rfl) ⟨3415427, by rfl⟩ : syracuseStep 4553903 = 6830855) B6830855
theorem B3035935 : Blo 2245435 3035935 := bstep (se 1 (by rfl) ⟨2276951, by rfl⟩ : syracuseStep 3035935 = 4553903) B4553903
theorem B4047913 : Blo 2245435 4047913 := bstep (se 2 (by rfl) ⟨1517967, by rfl⟩ : syracuseStep 4047913 = 3035935) B3035935
theorem B21588869 : Blo 2245435 21588869 := bstep (se 4 (by rfl) ⟨2023956, by rfl⟩ : syracuseStep 21588869 = 4047913) B4047913
theorem B14392579 : Blo 2245435 14392579 := bstep (se 1 (by rfl) ⟨10794434, by rfl⟩ : syracuseStep 14392579 = 21588869) B21588869
theorem B19190105 : Blo 2245435 19190105 := bstep (se 2 (by rfl) ⟨7196289, by rfl⟩ : syracuseStep 19190105 = 14392579) B14392579
theorem B12793403 : Blo 2245435 12793403 := bstep (se 1 (by rfl) ⟨9595052, by rfl⟩ : syracuseStep 12793403 = 19190105) B19190105
theorem B8528935 : Blo 2245435 8528935 := bstep (se 1 (by rfl) ⟨6396701, by rfl⟩ : syracuseStep 8528935 = 12793403) B12793403
theorem B11371913 : Blo 2245435 11371913 := bstep (se 2 (by rfl) ⟨4264467, by rfl⟩ : syracuseStep 11371913 = 8528935) B8528935
theorem B7581275 : Blo 2245435 7581275 := bstep (se 1 (by rfl) ⟨5685956, by rfl⟩ : syracuseStep 7581275 = 11371913) B11371913
theorem B5054183 : Blo 2245435 5054183 := bstep (se 1 (by rfl) ⟨3790637, by rfl⟩ : syracuseStep 5054183 = 7581275) B7581275
theorem B3369455 : Blo 2245435 3369455 := bstep (se 1 (by rfl) ⟨2527091, by rfl⟩ : syracuseStep 3369455 = 5054183) B5054183
theorem B2246303 : Blo 2245435 2246303 := bstep (se 1 (by rfl) ⟨1684727, by rfl⟩ : syracuseStep 2246303 = 3369455) B3369455
theorem B3369461 : Blo 2245435 3369461 := bbase (se 5 (by rfl) ⟨157943, by rfl⟩ : syracuseStep 3369461 = 315887) (by norm_num)
theorem B2246307 : Blo 2245435 2246307 := bstep (se 1 (by rfl) ⟨1684730, by rfl⟩ : syracuseStep 2246307 = 3369461) B3369461
theorem B6396725 : Blo 2245435 6396725 := bbase (se 5 (by rfl) ⟨299846, by rfl⟩ : syracuseStep 6396725 = 599693) (by norm_num)
theorem B4264483 : Blo 2245435 4264483 := bstep (se 1 (by rfl) ⟨3198362, by rfl⟩ : syracuseStep 4264483 = 6396725) B6396725
theorem B5685977 : Blo 2245435 5685977 := bstep (se 2 (by rfl) ⟨2132241, by rfl⟩ : syracuseStep 5685977 = 4264483) B4264483
theorem B3790651 : Blo 2245435 3790651 := bstep (se 1 (by rfl) ⟨2842988, by rfl⟩ : syracuseStep 3790651 = 5685977) B5685977
theorem B5054201 : Blo 2245435 5054201 := bstep (se 2 (by rfl) ⟨1895325, by rfl⟩ : syracuseStep 5054201 = 3790651) B3790651
theorem B3369467 : Blo 2245435 3369467 := bstep (se 1 (by rfl) ⟨2527100, by rfl⟩ : syracuseStep 3369467 = 5054201) B5054201
theorem B2246311 : Blo 2245435 2246311 := bstep (se 1 (by rfl) ⟨1684733, by rfl⟩ : syracuseStep 2246311 = 3369467) B3369467
theorem B2527105 : Blo 2245435 2527105 := bbase (se 2 (by rfl) ⟨947664, by rfl⟩ : syracuseStep 2527105 = 1895329) (by norm_num)
theorem B3369473 : Blo 2245435 3369473 := bstep (se 2 (by rfl) ⟨1263552, by rfl⟩ : syracuseStep 3369473 = 2527105) B2527105
theorem B2246315 : Blo 2245435 2246315 := bstep (se 1 (by rfl) ⟨1684736, by rfl⟩ : syracuseStep 2246315 = 3369473) B3369473
theorem B5685997 : Blo 2245435 5685997 := bbase (se 3 (by rfl) ⟨1066124, by rfl⟩ : syracuseStep 5685997 = 2132249) (by norm_num)
theorem B7581329 : Blo 2245435 7581329 := bstep (se 2 (by rfl) ⟨2842998, by rfl⟩ : syracuseStep 7581329 = 5685997) B5685997
theorem B5054219 : Blo 2245435 5054219 := bstep (se 1 (by rfl) ⟨3790664, by rfl⟩ : syracuseStep 5054219 = 7581329) B7581329
theorem B3369479 : Blo 2245435 3369479 := bstep (se 1 (by rfl) ⟨2527109, by rfl⟩ : syracuseStep 3369479 = 5054219) B5054219
theorem B2246319 : Blo 2245435 2246319 := bstep (se 1 (by rfl) ⟨1684739, by rfl⟩ : syracuseStep 2246319 = 3369479) B3369479
theorem B3369485 : Blo 2245435 3369485 := bbase (se 3 (by rfl) ⟨631778, by rfl⟩ : syracuseStep 3369485 = 1263557) (by norm_num)
theorem B2246323 : Blo 2245435 2246323 := bstep (se 1 (by rfl) ⟨1684742, by rfl⟩ : syracuseStep 2246323 = 3369485) B3369485
theorem B5054237 : Blo 2245435 5054237 := bbase (se 3 (by rfl) ⟨947669, by rfl⟩ : syracuseStep 5054237 = 1895339) (by norm_num)
theorem B3369491 : Blo 2245435 3369491 := bstep (se 1 (by rfl) ⟨2527118, by rfl⟩ : syracuseStep 3369491 = 5054237) B5054237
theorem B2246327 : Blo 2245435 2246327 := bstep (se 1 (by rfl) ⟨1684745, by rfl⟩ : syracuseStep 2246327 = 3369491) B3369491
theorem B3790685 : Blo 2245435 3790685 := bbase (se 3 (by rfl) ⟨710753, by rfl⟩ : syracuseStep 3790685 = 1421507) (by norm_num)
theorem B2527123 : Blo 2245435 2527123 := bstep (se 1 (by rfl) ⟨1895342, by rfl⟩ : syracuseStep 2527123 = 3790685) B3790685
theorem B3369497 : Blo 2245435 3369497 := bstep (se 2 (by rfl) ⟨1263561, by rfl⟩ : syracuseStep 3369497 = 2527123) B2527123
theorem B2246331 : Blo 2245435 2246331 := bstep (se 1 (by rfl) ⟨1684748, by rfl⟩ : syracuseStep 2246331 = 3369497) B3369497
theorem B9595189 : Blo 2245435 9595189 := bbase (se 5 (by rfl) ⟨449774, by rfl⟩ : syracuseStep 9595189 = 899549) (by norm_num)
theorem B12793585 : Blo 2245435 12793585 := bstep (se 2 (by rfl) ⟨4797594, by rfl⟩ : syracuseStep 12793585 = 9595189) B9595189
theorem B17058113 : Blo 2245435 17058113 := bstep (se 2 (by rfl) ⟨6396792, by rfl⟩ : syracuseStep 17058113 = 12793585) B12793585
theorem B11372075 : Blo 2245435 11372075 := bstep (se 1 (by rfl) ⟨8529056, by rfl⟩ : syracuseStep 11372075 = 17058113) B17058113
theorem B7581383 : Blo 2245435 7581383 := bstep (se 1 (by rfl) ⟨5686037, by rfl⟩ : syracuseStep 7581383 = 11372075) B11372075
theorem B5054255 : Blo 2245435 5054255 := bstep (se 1 (by rfl) ⟨3790691, by rfl⟩ : syracuseStep 5054255 = 7581383) B7581383
theorem B3369503 : Blo 2245435 3369503 := bstep (se 1 (by rfl) ⟨2527127, by rfl⟩ : syracuseStep 3369503 = 5054255) B5054255
theorem B2246335 : Blo 2245435 2246335 := bstep (se 1 (by rfl) ⟨1684751, by rfl⟩ : syracuseStep 2246335 = 3369503) B3369503
theorem B3369509 : Blo 2245435 3369509 := bbase (se 4 (by rfl) ⟨315891, by rfl⟩ : syracuseStep 3369509 = 631783) (by norm_num)
theorem B2246339 : Blo 2245435 2246339 := bstep (se 1 (by rfl) ⟨1684754, by rfl⟩ : syracuseStep 2246339 = 3369509) B3369509
theorem B2843029 : Blo 2245435 2843029 := bbase (se 6 (by rfl) ⟨66633, by rfl⟩ : syracuseStep 2843029 = 133267) (by norm_num)
theorem B3790705 : Blo 2245435 3790705 := bstep (se 2 (by rfl) ⟨1421514, by rfl⟩ : syracuseStep 3790705 = 2843029) B2843029
theorem B5054273 : Blo 2245435 5054273 := bstep (se 2 (by rfl) ⟨1895352, by rfl⟩ : syracuseStep 5054273 = 3790705) B3790705
theorem B3369515 : Blo 2245435 3369515 := bstep (se 1 (by rfl) ⟨2527136, by rfl⟩ : syracuseStep 3369515 = 5054273) B5054273
theorem B2246343 : Blo 2245435 2246343 := bstep (se 1 (by rfl) ⟨1684757, by rfl⟩ : syracuseStep 2246343 = 3369515) B3369515
theorem B2527141 : Blo 2245435 2527141 := bbase (se 4 (by rfl) ⟨236919, by rfl⟩ : syracuseStep 2527141 = 473839) (by norm_num)
theorem B3369521 : Blo 2245435 3369521 := bstep (se 2 (by rfl) ⟨1263570, by rfl⟩ : syracuseStep 3369521 = 2527141) B2527141
theorem B2246347 : Blo 2245435 2246347 := bstep (se 1 (by rfl) ⟨1684760, by rfl⟩ : syracuseStep 2246347 = 3369521) B3369521
theorem B2881829 : Blo 2245435 2881829 := bbase (se 4 (by rfl) ⟨270171, by rfl⟩ : syracuseStep 2881829 = 540343) (by norm_num)
theorem B7684877 : Blo 2245435 7684877 := bstep (se 3 (by rfl) ⟨1440914, by rfl⟩ : syracuseStep 7684877 = 2881829) B2881829
theorem B5123251 : Blo 2245435 5123251 := bstep (se 1 (by rfl) ⟨3842438, by rfl⟩ : syracuseStep 5123251 = 7684877) B7684877
theorem B6831001 : Blo 2245435 6831001 := bstep (se 2 (by rfl) ⟨2561625, by rfl⟩ : syracuseStep 6831001 = 5123251) B5123251
theorem B9108001 : Blo 2245435 9108001 := bstep (se 2 (by rfl) ⟨3415500, by rfl⟩ : syracuseStep 9108001 = 6831001) B6831001
theorem B12144001 : Blo 2245435 12144001 := bstep (se 2 (by rfl) ⟨4554000, by rfl⟩ : syracuseStep 12144001 = 9108001) B9108001
theorem B16192001 : Blo 2245435 16192001 := bstep (se 2 (by rfl) ⟨6072000, by rfl⟩ : syracuseStep 16192001 = 12144001) B12144001
theorem B10794667 : Blo 2245435 10794667 := bstep (se 1 (by rfl) ⟨8096000, by rfl⟩ : syracuseStep 10794667 = 16192001) B16192001
theorem B14392889 : Blo 2245435 14392889 := bstep (se 2 (by rfl) ⟨5397333, by rfl⟩ : syracuseStep 14392889 = 10794667) B10794667
theorem B9595259 : Blo 2245435 9595259 := bstep (se 1 (by rfl) ⟨7196444, by rfl⟩ : syracuseStep 9595259 = 14392889) B14392889
theorem B6396839 : Blo 2245435 6396839 := bstep (se 1 (by rfl) ⟨4797629, by rfl⟩ : syracuseStep 6396839 = 9595259) B9595259
theorem B4264559 : Blo 2245435 4264559 := bstep (se 1 (by rfl) ⟨3198419, by rfl⟩ : syracuseStep 4264559 = 6396839) B6396839
theorem B2843039 : Blo 2245435 2843039 := bstep (se 1 (by rfl) ⟨2132279, by rfl⟩ : syracuseStep 2843039 = 4264559) B4264559
theorem B7581437 : Blo 2245435 7581437 := bstep (se 3 (by rfl) ⟨1421519, by rfl⟩ : syracuseStep 7581437 = 2843039) B2843039
theorem B5054291 : Blo 2245435 5054291 := bstep (se 1 (by rfl) ⟨3790718, by rfl⟩ : syracuseStep 5054291 = 7581437) B7581437
theorem B3369527 : Blo 2245435 3369527 := bstep (se 1 (by rfl) ⟨2527145, by rfl⟩ : syracuseStep 3369527 = 5054291) B5054291
theorem B2246351 : Blo 2245435 2246351 := bstep (se 1 (by rfl) ⟨1684763, by rfl⟩ : syracuseStep 2246351 = 3369527) B3369527
theorem B3369533 : Blo 2245435 3369533 := bbase (se 3 (by rfl) ⟨631787, by rfl⟩ : syracuseStep 3369533 = 1263575) (by norm_num)
theorem B2246355 : Blo 2245435 2246355 := bstep (se 1 (by rfl) ⟨1684766, by rfl⟩ : syracuseStep 2246355 = 3369533) B3369533
theorem B5054309 : Blo 2245435 5054309 := bbase (se 4 (by rfl) ⟨473841, by rfl⟩ : syracuseStep 5054309 = 947683) (by norm_num)
theorem B3369539 : Blo 2245435 3369539 := bstep (se 1 (by rfl) ⟨2527154, by rfl⟩ : syracuseStep 3369539 = 5054309) B5054309
theorem B2246359 : Blo 2245435 2246359 := bstep (se 1 (by rfl) ⟨1684769, by rfl⟩ : syracuseStep 2246359 = 3369539) B3369539
theorem B5686109 : Blo 2245435 5686109 := bbase (se 3 (by rfl) ⟨1066145, by rfl⟩ : syracuseStep 5686109 = 2132291) (by norm_num)
theorem B3790739 : Blo 2245435 3790739 := bstep (se 1 (by rfl) ⟨2843054, by rfl⟩ : syracuseStep 3790739 = 5686109) B5686109
theorem B2527159 : Blo 2245435 2527159 := bstep (se 1 (by rfl) ⟨1895369, by rfl⟩ : syracuseStep 2527159 = 3790739) B3790739
theorem B3369545 : Blo 2245435 3369545 := bstep (se 2 (by rfl) ⟨1263579, by rfl⟩ : syracuseStep 3369545 = 2527159) B2527159
theorem B2246363 : Blo 2245435 2246363 := bstep (se 1 (by rfl) ⟨1684772, by rfl⟩ : syracuseStep 2246363 = 3369545) B3369545
theorem B4264589 : Blo 2245435 4264589 := bbase (se 3 (by rfl) ⟨799610, by rfl⟩ : syracuseStep 4264589 = 1599221) (by norm_num)
theorem B11372237 : Blo 2245435 11372237 := bstep (se 3 (by rfl) ⟨2132294, by rfl⟩ : syracuseStep 11372237 = 4264589) B4264589
theorem B7581491 : Blo 2245435 7581491 := bstep (se 1 (by rfl) ⟨5686118, by rfl⟩ : syracuseStep 7581491 = 11372237) B11372237
theorem B5054327 : Blo 2245435 5054327 := bstep (se 1 (by rfl) ⟨3790745, by rfl⟩ : syracuseStep 5054327 = 7581491) B7581491
theorem B3369551 : Blo 2245435 3369551 := bstep (se 1 (by rfl) ⟨2527163, by rfl⟩ : syracuseStep 3369551 = 5054327) B5054327
theorem B2246367 : Blo 2245435 2246367 := bstep (se 1 (by rfl) ⟨1684775, by rfl⟩ : syracuseStep 2246367 = 3369551) B3369551
theorem B3369557 : Blo 2245435 3369557 := bbase (se 8 (by rfl) ⟨19743, by rfl⟩ : syracuseStep 3369557 = 39487) (by norm_num)
theorem B2246371 : Blo 2245435 2246371 := bstep (se 1 (by rfl) ⟨1684778, by rfl⟩ : syracuseStep 2246371 = 3369557) B3369557
theorem B2561653 : Blo 2245435 2561653 := bbase (se 5 (by rfl) ⟨120077, by rfl⟩ : syracuseStep 2561653 = 240155) (by norm_num)
theorem B3415537 : Blo 2245435 3415537 := bstep (se 2 (by rfl) ⟨1280826, by rfl⟩ : syracuseStep 3415537 = 2561653) B2561653
theorem B18216197 : Blo 2245435 18216197 := bstep (se 4 (by rfl) ⟨1707768, by rfl⟩ : syracuseStep 18216197 = 3415537) B3415537
theorem B12144131 : Blo 2245435 12144131 := bstep (se 1 (by rfl) ⟨9108098, by rfl⟩ : syracuseStep 12144131 = 18216197) B18216197
theorem B8096087 : Blo 2245435 8096087 := bstep (se 1 (by rfl) ⟨6072065, by rfl⟩ : syracuseStep 8096087 = 12144131) B12144131
theorem B5397391 : Blo 2245435 5397391 := bstep (se 1 (by rfl) ⟨4048043, by rfl⟩ : syracuseStep 5397391 = 8096087) B8096087
theorem B7196521 : Blo 2245435 7196521 := bstep (se 2 (by rfl) ⟨2698695, by rfl⟩ : syracuseStep 7196521 = 5397391) B5397391
theorem B9595361 : Blo 2245435 9595361 := bstep (se 2 (by rfl) ⟨3598260, by rfl⟩ : syracuseStep 9595361 = 7196521) B7196521
theorem B6396907 : Blo 2245435 6396907 := bstep (se 1 (by rfl) ⟨4797680, by rfl⟩ : syracuseStep 6396907 = 9595361) B9595361
theorem B8529209 : Blo 2245435 8529209 := bstep (se 2 (by rfl) ⟨3198453, by rfl⟩ : syracuseStep 8529209 = 6396907) B6396907
theorem B5686139 : Blo 2245435 5686139 := bstep (se 1 (by rfl) ⟨4264604, by rfl⟩ : syracuseStep 5686139 = 8529209) B8529209
theorem B3790759 : Blo 2245435 3790759 := bstep (se 1 (by rfl) ⟨2843069, by rfl⟩ : syracuseStep 3790759 = 5686139) B5686139
theorem B5054345 : Blo 2245435 5054345 := bstep (se 2 (by rfl) ⟨1895379, by rfl⟩ : syracuseStep 5054345 = 3790759) B3790759
theorem B3369563 : Blo 2245435 3369563 := bstep (se 1 (by rfl) ⟨2527172, by rfl⟩ : syracuseStep 3369563 = 5054345) B5054345
theorem B2246375 : Blo 2245435 2246375 := bstep (se 1 (by rfl) ⟨1684781, by rfl⟩ : syracuseStep 2246375 = 3369563) B3369563
theorem B2527177 : Blo 2245435 2527177 := bbase (se 2 (by rfl) ⟨947691, by rfl⟩ : syracuseStep 2527177 = 1895383) (by norm_num)
theorem B3369569 : Blo 2245435 3369569 := bstep (se 2 (by rfl) ⟨1263588, by rfl⟩ : syracuseStep 3369569 = 2527177) B2527177
theorem B2246379 : Blo 2245435 2246379 := bstep (se 1 (by rfl) ⟨1684784, by rfl⟩ : syracuseStep 2246379 = 3369569) B3369569
theorem B2698705 : Blo 2245435 2698705 := bbase (se 2 (by rfl) ⟨1012014, by rfl⟩ : syracuseStep 2698705 = 2024029) (by norm_num)
theorem B3598273 : Blo 2245435 3598273 := bstep (se 2 (by rfl) ⟨1349352, by rfl⟩ : syracuseStep 3598273 = 2698705) B2698705
theorem B19190789 : Blo 2245435 19190789 := bstep (se 4 (by rfl) ⟨1799136, by rfl⟩ : syracuseStep 19190789 = 3598273) B3598273
theorem B12793859 : Blo 2245435 12793859 := bstep (se 1 (by rfl) ⟨9595394, by rfl⟩ : syracuseStep 12793859 = 19190789) B19190789
theorem B8529239 : Blo 2245435 8529239 := bstep (se 1 (by rfl) ⟨6396929, by rfl⟩ : syracuseStep 8529239 = 12793859) B12793859
theorem B5686159 : Blo 2245435 5686159 := bstep (se 1 (by rfl) ⟨4264619, by rfl⟩ : syracuseStep 5686159 = 8529239) B8529239
theorem B7581545 : Blo 2245435 7581545 := bstep (se 2 (by rfl) ⟨2843079, by rfl⟩ : syracuseStep 7581545 = 5686159) B5686159
theorem B5054363 : Blo 2245435 5054363 := bstep (se 1 (by rfl) ⟨3790772, by rfl⟩ : syracuseStep 5054363 = 7581545) B7581545
theorem B3369575 : Blo 2245435 3369575 := bstep (se 1 (by rfl) ⟨2527181, by rfl⟩ : syracuseStep 3369575 = 5054363) B5054363
theorem B2246383 : Blo 2245435 2246383 := bstep (se 1 (by rfl) ⟨1684787, by rfl⟩ : syracuseStep 2246383 = 3369575) B3369575
theorem B3369581 : Blo 2245435 3369581 := bbase (se 3 (by rfl) ⟨631796, by rfl⟩ : syracuseStep 3369581 = 1263593) (by norm_num)
theorem B2246387 : Blo 2245435 2246387 := bstep (se 1 (by rfl) ⟨1684790, by rfl⟩ : syracuseStep 2246387 = 3369581) B3369581
theorem B5054381 : Blo 2245435 5054381 := bbase (se 3 (by rfl) ⟨947696, by rfl⟩ : syracuseStep 5054381 = 1895393) (by norm_num)
theorem B3369587 : Blo 2245435 3369587 := bstep (se 1 (by rfl) ⟨2527190, by rfl⟩ : syracuseStep 3369587 = 5054381) B5054381
theorem B2246391 : Blo 2245435 2246391 := bstep (se 1 (by rfl) ⟨1684793, by rfl⟩ : syracuseStep 2246391 = 3369587) B3369587
theorem B6396965 : Blo 2245435 6396965 := bbase (se 4 (by rfl) ⟨599715, by rfl⟩ : syracuseStep 6396965 = 1199431) (by norm_num)
theorem B4264643 : Blo 2245435 4264643 := bstep (se 1 (by rfl) ⟨3198482, by rfl⟩ : syracuseStep 4264643 = 6396965) B6396965
theorem B2843095 : Blo 2245435 2843095 := bstep (se 1 (by rfl) ⟨2132321, by rfl⟩ : syracuseStep 2843095 = 4264643) B4264643
theorem B3790793 : Blo 2245435 3790793 := bstep (se 2 (by rfl) ⟨1421547, by rfl⟩ : syracuseStep 3790793 = 2843095) B2843095
theorem B2527195 : Blo 2245435 2527195 := bstep (se 1 (by rfl) ⟨1895396, by rfl⟩ : syracuseStep 2527195 = 3790793) B3790793
theorem B3369593 : Blo 2245435 3369593 := bstep (se 2 (by rfl) ⟨1263597, by rfl⟩ : syracuseStep 3369593 = 2527195) B2527195
theorem B2246395 : Blo 2245435 2246395 := bstep (se 1 (by rfl) ⟨1684796, by rfl⟩ : syracuseStep 2246395 = 3369593) B3369593
theorem B19452757 : Blo 2245435 19452757 := bbase (se 9 (by rfl) ⟨56990, by rfl⟩ : syracuseStep 19452757 = 113981) (by norm_num)
theorem B25937009 : Blo 2245435 25937009 := bstep (se 2 (by rfl) ⟨9726378, by rfl⟩ : syracuseStep 25937009 = 19452757) B19452757
theorem B17291339 : Blo 2245435 17291339 := bstep (se 1 (by rfl) ⟨12968504, by rfl⟩ : syracuseStep 17291339 = 25937009) B25937009
theorem B11527559 : Blo 2245435 11527559 := bstep (se 1 (by rfl) ⟨8645669, by rfl⟩ : syracuseStep 11527559 = 17291339) B17291339
theorem B7685039 : Blo 2245435 7685039 := bstep (se 1 (by rfl) ⟨5763779, by rfl⟩ : syracuseStep 7685039 = 11527559) B11527559
theorem B5123359 : Blo 2245435 5123359 := bstep (se 1 (by rfl) ⟨3842519, by rfl⟩ : syracuseStep 5123359 = 7685039) B7685039
theorem B6831145 : Blo 2245435 6831145 := bstep (se 2 (by rfl) ⟨2561679, by rfl⟩ : syracuseStep 6831145 = 5123359) B5123359
theorem B36432773 : Blo 2245435 36432773 := bstep (se 4 (by rfl) ⟨3415572, by rfl⟩ : syracuseStep 36432773 = 6831145) B6831145
theorem B24288515 : Blo 2245435 24288515 := bstep (se 1 (by rfl) ⟨18216386, by rfl⟩ : syracuseStep 24288515 = 36432773) B36432773
theorem B16192343 : Blo 2245435 16192343 := bstep (se 1 (by rfl) ⟨12144257, by rfl⟩ : syracuseStep 16192343 = 24288515) B24288515
theorem B43179581 : Blo 2245435 43179581 := bstep (se 3 (by rfl) ⟨8096171, by rfl⟩ : syracuseStep 43179581 = 16192343) B16192343
theorem B28786387 : Blo 2245435 28786387 := bstep (se 1 (by rfl) ⟨21589790, by rfl⟩ : syracuseStep 28786387 = 43179581) B43179581
theorem B38381849 : Blo 2245435 38381849 := bstep (se 2 (by rfl) ⟨14393193, by rfl⟩ : syracuseStep 38381849 = 28786387) B28786387
theorem B25587899 : Blo 2245435 25587899 := bstep (se 1 (by rfl) ⟨19190924, by rfl⟩ : syracuseStep 25587899 = 38381849) B38381849
theorem B17058599 : Blo 2245435 17058599 := bstep (se 1 (by rfl) ⟨12793949, by rfl⟩ : syracuseStep 17058599 = 25587899) B25587899
theorem B11372399 : Blo 2245435 11372399 := bstep (se 1 (by rfl) ⟨8529299, by rfl⟩ : syracuseStep 11372399 = 17058599) B17058599
theorem B7581599 : Blo 2245435 7581599 := bstep (se 1 (by rfl) ⟨5686199, by rfl⟩ : syracuseStep 7581599 = 11372399) B11372399
theorem B5054399 : Blo 2245435 5054399 := bstep (se 1 (by rfl) ⟨3790799, by rfl⟩ : syracuseStep 5054399 = 7581599) B7581599
theorem B3369599 : Blo 2245435 3369599 := bstep (se 1 (by rfl) ⟨2527199, by rfl⟩ : syracuseStep 3369599 = 5054399) B5054399
theorem B2246399 : Blo 2245435 2246399 := bstep (se 1 (by rfl) ⟨1684799, by rfl⟩ : syracuseStep 2246399 = 3369599) B3369599
theorem B3369605 : Blo 2245435 3369605 := bbase (se 4 (by rfl) ⟨315900, by rfl⟩ : syracuseStep 3369605 = 631801) (by norm_num)
theorem B2246403 : Blo 2245435 2246403 := bstep (se 1 (by rfl) ⟨1684802, by rfl⟩ : syracuseStep 2246403 = 3369605) B3369605
theorem B3790813 : Blo 2245435 3790813 := bbase (se 3 (by rfl) ⟨710777, by rfl⟩ : syracuseStep 3790813 = 1421555) (by norm_num)
theorem B5054417 : Blo 2245435 5054417 := bstep (se 2 (by rfl) ⟨1895406, by rfl⟩ : syracuseStep 5054417 = 3790813) B3790813
theorem B3369611 : Blo 2245435 3369611 := bstep (se 1 (by rfl) ⟨2527208, by rfl⟩ : syracuseStep 3369611 = 5054417) B5054417
theorem B2246407 : Blo 2245435 2246407 := bstep (se 1 (by rfl) ⟨1684805, by rfl⟩ : syracuseStep 2246407 = 3369611) B3369611
theorem B2527213 : Blo 2245435 2527213 := bbase (se 3 (by rfl) ⟨473852, by rfl⟩ : syracuseStep 2527213 = 947705) (by norm_num)
theorem B3369617 : Blo 2245435 3369617 := bstep (se 2 (by rfl) ⟨1263606, by rfl⟩ : syracuseStep 3369617 = 2527213) B2527213
theorem B2246411 : Blo 2245435 2246411 := bstep (se 1 (by rfl) ⟨1684808, by rfl⟩ : syracuseStep 2246411 = 3369617) B3369617
theorem B7581653 : Blo 2245435 7581653 := bbase (se 7 (by rfl) ⟨88847, by rfl⟩ : syracuseStep 7581653 = 177695) (by norm_num)
theorem B5054435 : Blo 2245435 5054435 := bstep (se 1 (by rfl) ⟨3790826, by rfl⟩ : syracuseStep 5054435 = 7581653) B7581653
theorem B3369623 : Blo 2245435 3369623 := bstep (se 1 (by rfl) ⟨2527217, by rfl⟩ : syracuseStep 3369623 = 5054435) B5054435
theorem B2246415 : Blo 2245435 2246415 := bstep (se 1 (by rfl) ⟨1684811, by rfl⟩ : syracuseStep 2246415 = 3369623) B3369623
theorem B3369629 : Blo 2245435 3369629 := bbase (se 3 (by rfl) ⟨631805, by rfl⟩ : syracuseStep 3369629 = 1263611) (by norm_num)
theorem B2246419 : Blo 2245435 2246419 := bstep (se 1 (by rfl) ⟨1684814, by rfl⟩ : syracuseStep 2246419 = 3369629) B3369629
theorem B5054453 : Blo 2245435 5054453 := bbase (se 5 (by rfl) ⟨236927, by rfl⟩ : syracuseStep 5054453 = 473855) (by norm_num)
theorem B3369635 : Blo 2245435 3369635 := bstep (se 1 (by rfl) ⟨2527226, by rfl⟩ : syracuseStep 3369635 = 5054453) B5054453
theorem B2246423 : Blo 2245435 2246423 := bstep (se 1 (by rfl) ⟨1684817, by rfl⟩ : syracuseStep 2246423 = 3369635) B3369635
theorem B3509453 : Blo 2245435 3509453 := bbase (se 3 (by rfl) ⟨658022, by rfl⟩ : syracuseStep 3509453 = 1316045) (by norm_num)
theorem B2339635 : Blo 2245435 2339635 := bstep (se 1 (by rfl) ⟨1754726, by rfl⟩ : syracuseStep 2339635 = 3509453) B3509453
theorem B3119513 : Blo 2245435 3119513 := bstep (se 2 (by rfl) ⟨1169817, by rfl⟩ : syracuseStep 3119513 = 2339635) B2339635
theorem B8318701 : Blo 2245435 8318701 := bstep (se 3 (by rfl) ⟨1559756, by rfl⟩ : syracuseStep 8318701 = 3119513) B3119513
theorem B11091601 : Blo 2245435 11091601 := bstep (se 2 (by rfl) ⟨4159350, by rfl⟩ : syracuseStep 11091601 = 8318701) B8318701
theorem B59155205 : Blo 2245435 59155205 := bstep (se 4 (by rfl) ⟨5545800, by rfl⟩ : syracuseStep 59155205 = 11091601) B11091601
theorem B157747213 : Blo 2245435 157747213 := bstep (se 3 (by rfl) ⟨29577602, by rfl⟩ : syracuseStep 157747213 = 59155205) B59155205
theorem B210329617 : Blo 2245435 210329617 := bstep (se 2 (by rfl) ⟨78873606, by rfl⟩ : syracuseStep 210329617 = 157747213) B157747213
theorem B280439489 : Blo 2245435 280439489 := bstep (se 2 (by rfl) ⟨105164808, by rfl⟩ : syracuseStep 280439489 = 210329617) B210329617
theorem B186959659 : Blo 2245435 186959659 := bstep (se 1 (by rfl) ⟨140219744, by rfl⟩ : syracuseStep 186959659 = 280439489) B280439489
theorem B249279545 : Blo 2245435 249279545 := bstep (se 2 (by rfl) ⟨93479829, by rfl⟩ : syracuseStep 249279545 = 186959659) B186959659
theorem B664745453 : Blo 2245435 664745453 := bstep (se 3 (by rfl) ⟨124639772, by rfl⟩ : syracuseStep 664745453 = 249279545) B249279545
theorem B443163635 : Blo 2245435 443163635 := bstep (se 1 (by rfl) ⟨332372726, by rfl⟩ : syracuseStep 443163635 = 664745453) B664745453
theorem B295442423 : Blo 2245435 295442423 := bstep (se 1 (by rfl) ⟨221581817, by rfl⟩ : syracuseStep 295442423 = 443163635) B443163635
theorem B196961615 : Blo 2245435 196961615 := bstep (se 1 (by rfl) ⟨147721211, by rfl⟩ : syracuseStep 196961615 = 295442423) B295442423
theorem B131307743 : Blo 2245435 131307743 := bstep (se 1 (by rfl) ⟨98480807, by rfl⟩ : syracuseStep 131307743 = 196961615) B196961615
theorem B87538495 : Blo 2245435 87538495 := bstep (se 1 (by rfl) ⟨65653871, by rfl⟩ : syracuseStep 87538495 = 131307743) B131307743
theorem B116717993 : Blo 2245435 116717993 := bstep (se 2 (by rfl) ⟨43769247, by rfl⟩ : syracuseStep 116717993 = 87538495) B87538495
theorem B77811995 : Blo 2245435 77811995 := bstep (se 1 (by rfl) ⟨58358996, by rfl⟩ : syracuseStep 77811995 = 116717993) B116717993
theorem B51874663 : Blo 2245435 51874663 := bstep (se 1 (by rfl) ⟨38905997, by rfl⟩ : syracuseStep 51874663 = 77811995) B77811995
theorem B69166217 : Blo 2245435 69166217 := bstep (se 2 (by rfl) ⟨25937331, by rfl⟩ : syracuseStep 69166217 = 51874663) B51874663
theorem B46110811 : Blo 2245435 46110811 := bstep (se 1 (by rfl) ⟨34583108, by rfl⟩ : syracuseStep 46110811 = 69166217) B69166217
theorem B61481081 : Blo 2245435 61481081 := bstep (se 2 (by rfl) ⟨23055405, by rfl⟩ : syracuseStep 61481081 = 46110811) B46110811
theorem B40987387 : Blo 2245435 40987387 := bstep (se 1 (by rfl) ⟨30740540, by rfl⟩ : syracuseStep 40987387 = 61481081) B61481081
theorem B218599397 : Blo 2245435 218599397 := bstep (se 4 (by rfl) ⟨20493693, by rfl⟩ : syracuseStep 218599397 = 40987387) B40987387
theorem B145732931 : Blo 2245435 145732931 := bstep (se 1 (by rfl) ⟨109299698, by rfl⟩ : syracuseStep 145732931 = 218599397) B218599397
theorem B97155287 : Blo 2245435 97155287 := bstep (se 1 (by rfl) ⟨72866465, by rfl⟩ : syracuseStep 97155287 = 145732931) B145732931
theorem B64770191 : Blo 2245435 64770191 := bstep (se 1 (by rfl) ⟨48577643, by rfl⟩ : syracuseStep 64770191 = 97155287) B97155287
theorem B43180127 : Blo 2245435 43180127 := bstep (se 1 (by rfl) ⟨32385095, by rfl⟩ : syracuseStep 43180127 = 64770191) B64770191
theorem B28786751 : Blo 2245435 28786751 := bstep (se 1 (by rfl) ⟨21590063, by rfl⟩ : syracuseStep 28786751 = 43180127) B43180127
theorem B19191167 : Blo 2245435 19191167 := bstep (se 1 (by rfl) ⟨14393375, by rfl⟩ : syracuseStep 19191167 = 28786751) B28786751
theorem B12794111 : Blo 2245435 12794111 := bstep (se 1 (by rfl) ⟨9595583, by rfl⟩ : syracuseStep 12794111 = 19191167) B19191167
theorem B8529407 : Blo 2245435 8529407 := bstep (se 1 (by rfl) ⟨6397055, by rfl⟩ : syracuseStep 8529407 = 12794111) B12794111
theorem B5686271 : Blo 2245435 5686271 := bstep (se 1 (by rfl) ⟨4264703, by rfl⟩ : syracuseStep 5686271 = 8529407) B8529407
theorem B3790847 : Blo 2245435 3790847 := bstep (se 1 (by rfl) ⟨2843135, by rfl⟩ : syracuseStep 3790847 = 5686271) B5686271
theorem B2527231 : Blo 2245435 2527231 := bstep (se 1 (by rfl) ⟨1895423, by rfl⟩ : syracuseStep 2527231 = 3790847) B3790847
theorem B3369641 : Blo 2245435 3369641 := bstep (se 2 (by rfl) ⟨1263615, by rfl⟩ : syracuseStep 3369641 = 2527231) B2527231
theorem B2246427 : Blo 2245435 2246427 := bstep (se 1 (by rfl) ⟨1684820, by rfl⟩ : syracuseStep 2246427 = 3369641) B3369641
theorem B3198533 : Blo 2245435 3198533 := bbase (se 4 (by rfl) ⟨299862, by rfl⟩ : syracuseStep 3198533 = 599725) (by norm_num)
theorem B8529421 : Blo 2245435 8529421 := bstep (se 3 (by rfl) ⟨1599266, by rfl⟩ : syracuseStep 8529421 = 3198533) B3198533
theorem B11372561 : Blo 2245435 11372561 := bstep (se 2 (by rfl) ⟨4264710, by rfl⟩ : syracuseStep 11372561 = 8529421) B8529421
theorem B7581707 : Blo 2245435 7581707 := bstep (se 1 (by rfl) ⟨5686280, by rfl⟩ : syracuseStep 7581707 = 11372561) B11372561
theorem B5054471 : Blo 2245435 5054471 := bstep (se 1 (by rfl) ⟨3790853, by rfl⟩ : syracuseStep 5054471 = 7581707) B7581707
theorem B3369647 : Blo 2245435 3369647 := bstep (se 1 (by rfl) ⟨2527235, by rfl⟩ : syracuseStep 3369647 = 5054471) B5054471
theorem B2246431 : Blo 2245435 2246431 := bstep (se 1 (by rfl) ⟨1684823, by rfl⟩ : syracuseStep 2246431 = 3369647) B3369647
theorem B3369653 : Blo 2245435 3369653 := bbase (se 5 (by rfl) ⟨157952, by rfl⟩ : syracuseStep 3369653 = 315905) (by norm_num)
theorem B2246435 : Blo 2245435 2246435 := bstep (se 1 (by rfl) ⟨1684826, by rfl⟩ : syracuseStep 2246435 = 3369653) B3369653
theorem B5686301 : Blo 2245435 5686301 := bbase (se 3 (by rfl) ⟨1066181, by rfl⟩ : syracuseStep 5686301 = 2132363) (by norm_num)
theorem B3790867 : Blo 2245435 3790867 := bstep (se 1 (by rfl) ⟨2843150, by rfl⟩ : syracuseStep 3790867 = 5686301) B5686301
theorem B5054489 : Blo 2245435 5054489 := bstep (se 2 (by rfl) ⟨1895433, by rfl⟩ : syracuseStep 5054489 = 3790867) B3790867
theorem B3369659 : Blo 2245435 3369659 := bstep (se 1 (by rfl) ⟨2527244, by rfl⟩ : syracuseStep 3369659 = 5054489) B5054489
theorem B2246439 : Blo 2245435 2246439 := bstep (se 1 (by rfl) ⟨1684829, by rfl⟩ : syracuseStep 2246439 = 3369659) B3369659
theorem B2527249 : Blo 2245435 2527249 := bbase (se 2 (by rfl) ⟨947718, by rfl⟩ : syracuseStep 2527249 = 1895437) (by norm_num)
theorem B3369665 : Blo 2245435 3369665 := bstep (se 2 (by rfl) ⟨1263624, by rfl⟩ : syracuseStep 3369665 = 2527249) B2527249
theorem B2246443 : Blo 2245435 2246443 := bstep (se 1 (by rfl) ⟨1684832, by rfl⟩ : syracuseStep 2246443 = 3369665) B3369665
theorem B4264741 : Blo 2245435 4264741 := bbase (se 4 (by rfl) ⟨399819, by rfl⟩ : syracuseStep 4264741 = 799639) (by norm_num)
theorem B5686321 : Blo 2245435 5686321 := bstep (se 2 (by rfl) ⟨2132370, by rfl⟩ : syracuseStep 5686321 = 4264741) B4264741
theorem B7581761 : Blo 2245435 7581761 := bstep (se 2 (by rfl) ⟨2843160, by rfl⟩ : syracuseStep 7581761 = 5686321) B5686321
theorem B5054507 : Blo 2245435 5054507 := bstep (se 1 (by rfl) ⟨3790880, by rfl⟩ : syracuseStep 5054507 = 7581761) B7581761
theorem B3369671 : Blo 2245435 3369671 := bstep (se 1 (by rfl) ⟨2527253, by rfl⟩ : syracuseStep 3369671 = 5054507) B5054507
theorem B2246447 : Blo 2245435 2246447 := bstep (se 1 (by rfl) ⟨1684835, by rfl⟩ : syracuseStep 2246447 = 3369671) B3369671
theorem B3369677 : Blo 2245435 3369677 := bbase (se 3 (by rfl) ⟨631814, by rfl⟩ : syracuseStep 3369677 = 1263629) (by norm_num)
theorem B2246451 : Blo 2245435 2246451 := bstep (se 1 (by rfl) ⟨1684838, by rfl⟩ : syracuseStep 2246451 = 3369677) B3369677
theorem B5054525 : Blo 2245435 5054525 := bbase (se 3 (by rfl) ⟨947723, by rfl⟩ : syracuseStep 5054525 = 1895447) (by norm_num)
theorem B3369683 : Blo 2245435 3369683 := bstep (se 1 (by rfl) ⟨2527262, by rfl⟩ : syracuseStep 3369683 = 5054525) B5054525
theorem B2246455 : Blo 2245435 2246455 := bstep (se 1 (by rfl) ⟨1684841, by rfl⟩ : syracuseStep 2246455 = 3369683) B3369683
theorem B3790901 : Blo 2245435 3790901 := bbase (se 5 (by rfl) ⟨177698, by rfl⟩ : syracuseStep 3790901 = 355397) (by norm_num)
theorem B2527267 : Blo 2245435 2527267 := bstep (se 1 (by rfl) ⟨1895450, by rfl⟩ : syracuseStep 2527267 = 3790901) B3790901
theorem B3369689 : Blo 2245435 3369689 := bstep (se 2 (by rfl) ⟨1263633, by rfl⟩ : syracuseStep 3369689 = 2527267) B2527267
theorem B2246459 : Blo 2245435 2246459 := bstep (se 1 (by rfl) ⟨1684844, by rfl⟩ : syracuseStep 2246459 = 3369689) B3369689
theorem B6397157 : Blo 2245435 6397157 := bbase (se 4 (by rfl) ⟨599733, by rfl⟩ : syracuseStep 6397157 = 1199467) (by norm_num)
theorem B17059085 : Blo 2245435 17059085 := bstep (se 3 (by rfl) ⟨3198578, by rfl⟩ : syracuseStep 17059085 = 6397157) B6397157
theorem B11372723 : Blo 2245435 11372723 := bstep (se 1 (by rfl) ⟨8529542, by rfl⟩ : syracuseStep 11372723 = 17059085) B17059085
theorem B7581815 : Blo 2245435 7581815 := bstep (se 1 (by rfl) ⟨5686361, by rfl⟩ : syracuseStep 7581815 = 11372723) B11372723
theorem B5054543 : Blo 2245435 5054543 := bstep (se 1 (by rfl) ⟨3790907, by rfl⟩ : syracuseStep 5054543 = 7581815) B7581815
theorem B3369695 : Blo 2245435 3369695 := bstep (se 1 (by rfl) ⟨2527271, by rfl⟩ : syracuseStep 3369695 = 5054543) B5054543
theorem B2246463 : Blo 2245435 2246463 := bstep (se 1 (by rfl) ⟨1684847, by rfl⟩ : syracuseStep 2246463 = 3369695) B3369695
theorem B3369701 : Blo 2245435 3369701 := bbase (se 4 (by rfl) ⟨315909, by rfl⟩ : syracuseStep 3369701 = 631819) (by norm_num)
theorem B2246467 : Blo 2245435 2246467 := bstep (se 1 (by rfl) ⟨1684850, by rfl⟩ : syracuseStep 2246467 = 3369701) B3369701
theorem B4554245 : Blo 2245435 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B12144653 : Blo 2245435 12144653 := bstep (se 3 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 12144653 = 4554245) B4554245
theorem B8096435 : Blo 2245435 8096435 := bstep (se 1 (by rfl) ⟨6072326, by rfl⟩ : syracuseStep 8096435 = 12144653) B12144653
theorem B5397623 : Blo 2245435 5397623 := bstep (se 1 (by rfl) ⟨4048217, by rfl⟩ : syracuseStep 5397623 = 8096435) B8096435
theorem B3598415 : Blo 2245435 3598415 := bstep (se 1 (by rfl) ⟨2698811, by rfl⟩ : syracuseStep 3598415 = 5397623) B5397623
theorem B2398943 : Blo 2245435 2398943 := bstep (se 1 (by rfl) ⟨1799207, by rfl⟩ : syracuseStep 2398943 = 3598415) B3598415
theorem B6397181 : Blo 2245435 6397181 := bstep (se 3 (by rfl) ⟨1199471, by rfl⟩ : syracuseStep 6397181 = 2398943) B2398943
theorem B4264787 : Blo 2245435 4264787 := bstep (se 1 (by rfl) ⟨3198590, by rfl⟩ : syracuseStep 4264787 = 6397181) B6397181
theorem B2843191 : Blo 2245435 2843191 := bstep (se 1 (by rfl) ⟨2132393, by rfl⟩ : syracuseStep 2843191 = 4264787) B4264787
theorem B3790921 : Blo 2245435 3790921 := bstep (se 2 (by rfl) ⟨1421595, by rfl⟩ : syracuseStep 3790921 = 2843191) B2843191
theorem B5054561 : Blo 2245435 5054561 := bstep (se 2 (by rfl) ⟨1895460, by rfl⟩ : syracuseStep 5054561 = 3790921) B3790921
theorem B3369707 : Blo 2245435 3369707 := bstep (se 1 (by rfl) ⟨2527280, by rfl⟩ : syracuseStep 3369707 = 5054561) B5054561
theorem B2246471 : Blo 2245435 2246471 := bstep (se 1 (by rfl) ⟨1684853, by rfl⟩ : syracuseStep 2246471 = 3369707) B3369707
theorem B2527285 : Blo 2245435 2527285 := bbase (se 5 (by rfl) ⟨118466, by rfl⟩ : syracuseStep 2527285 = 236933) (by norm_num)
theorem B3369713 : Blo 2245435 3369713 := bstep (se 2 (by rfl) ⟨1263642, by rfl⟩ : syracuseStep 3369713 = 2527285) B2527285
theorem B2246475 : Blo 2245435 2246475 := bstep (se 1 (by rfl) ⟨1684856, by rfl⟩ : syracuseStep 2246475 = 3369713) B3369713
theorem B2843201 : Blo 2245435 2843201 := bbase (se 2 (by rfl) ⟨1066200, by rfl⟩ : syracuseStep 2843201 = 2132401) (by norm_num)
theorem B7581869 : Blo 2245435 7581869 := bstep (se 3 (by rfl) ⟨1421600, by rfl⟩ : syracuseStep 7581869 = 2843201) B2843201
theorem B5054579 : Blo 2245435 5054579 := bstep (se 1 (by rfl) ⟨3790934, by rfl⟩ : syracuseStep 5054579 = 7581869) B7581869
theorem B3369719 : Blo 2245435 3369719 := bstep (se 1 (by rfl) ⟨2527289, by rfl⟩ : syracuseStep 3369719 = 5054579) B5054579
theorem B2246479 : Blo 2245435 2246479 := bstep (se 1 (by rfl) ⟨1684859, by rfl⟩ : syracuseStep 2246479 = 3369719) B3369719
theorem B3369725 : Blo 2245435 3369725 := bbase (se 3 (by rfl) ⟨631823, by rfl⟩ : syracuseStep 3369725 = 1263647) (by norm_num)
theorem B2246483 : Blo 2245435 2246483 := bstep (se 1 (by rfl) ⟨1684862, by rfl⟩ : syracuseStep 2246483 = 3369725) B3369725
theorem B5054597 : Blo 2245435 5054597 := bbase (se 4 (by rfl) ⟨473868, by rfl⟩ : syracuseStep 5054597 = 947737) (by norm_num)
theorem B3369731 : Blo 2245435 3369731 := bstep (se 1 (by rfl) ⟨2527298, by rfl⟩ : syracuseStep 3369731 = 5054597) B5054597
theorem B2246487 : Blo 2245435 2246487 := bstep (se 1 (by rfl) ⟨1684865, by rfl⟩ : syracuseStep 2246487 = 3369731) B3369731
theorem B2464873 : Blo 2245435 2464873 := bbase (se 2 (by rfl) ⟨924327, by rfl⟩ : syracuseStep 2464873 = 1848655) (by norm_num)
theorem B13145989 : Blo 2245435 13145989 := bstep (se 4 (by rfl) ⟨1232436, by rfl⟩ : syracuseStep 13145989 = 2464873) B2464873
theorem B17527985 : Blo 2245435 17527985 := bstep (se 2 (by rfl) ⟨6572994, by rfl⟩ : syracuseStep 17527985 = 13145989) B13145989
theorem B11685323 : Blo 2245435 11685323 := bstep (se 1 (by rfl) ⟨8763992, by rfl⟩ : syracuseStep 11685323 = 17527985) B17527985
theorem B7790215 : Blo 2245435 7790215 := bstep (se 1 (by rfl) ⟨5842661, by rfl⟩ : syracuseStep 7790215 = 11685323) B11685323
theorem B10386953 : Blo 2245435 10386953 := bstep (se 2 (by rfl) ⟨3895107, by rfl⟩ : syracuseStep 10386953 = 7790215) B7790215
theorem B6924635 : Blo 2245435 6924635 := bstep (se 1 (by rfl) ⟨5193476, by rfl⟩ : syracuseStep 6924635 = 10386953) B10386953
theorem B4616423 : Blo 2245435 4616423 := bstep (se 1 (by rfl) ⟨3462317, by rfl⟩ : syracuseStep 4616423 = 6924635) B6924635
theorem B3077615 : Blo 2245435 3077615 := bstep (se 1 (by rfl) ⟨2308211, by rfl⟩ : syracuseStep 3077615 = 4616423) B4616423
theorem B8206973 : Blo 2245435 8206973 := bstep (se 3 (by rfl) ⟨1538807, by rfl⟩ : syracuseStep 8206973 = 3077615) B3077615
theorem B5471315 : Blo 2245435 5471315 := bstep (se 1 (by rfl) ⟨4103486, by rfl⟩ : syracuseStep 5471315 = 8206973) B8206973
theorem B3647543 : Blo 2245435 3647543 := bstep (se 1 (by rfl) ⟨2735657, by rfl⟩ : syracuseStep 3647543 = 5471315) B5471315
theorem B38907125 : Blo 2245435 38907125 := bstep (se 5 (by rfl) ⟨1823771, by rfl⟩ : syracuseStep 38907125 = 3647543) B3647543
theorem B25938083 : Blo 2245435 25938083 := bstep (se 1 (by rfl) ⟨19453562, by rfl⟩ : syracuseStep 25938083 = 38907125) B38907125
theorem B17292055 : Blo 2245435 17292055 := bstep (se 1 (by rfl) ⟨12969041, by rfl⟩ : syracuseStep 17292055 = 25938083) B25938083
theorem B23056073 : Blo 2245435 23056073 := bstep (se 2 (by rfl) ⟨8646027, by rfl⟩ : syracuseStep 23056073 = 17292055) B17292055
theorem B15370715 : Blo 2245435 15370715 := bstep (se 1 (by rfl) ⟨11528036, by rfl⟩ : syracuseStep 15370715 = 23056073) B23056073
theorem B10247143 : Blo 2245435 10247143 := bstep (se 1 (by rfl) ⟨7685357, by rfl⟩ : syracuseStep 10247143 = 15370715) B15370715
theorem B13662857 : Blo 2245435 13662857 := bstep (se 2 (by rfl) ⟨5123571, by rfl⟩ : syracuseStep 13662857 = 10247143) B10247143
theorem B9108571 : Blo 2245435 9108571 := bstep (se 1 (by rfl) ⟨6831428, by rfl⟩ : syracuseStep 9108571 = 13662857) B13662857
theorem B12144761 : Blo 2245435 12144761 := bstep (se 2 (by rfl) ⟨4554285, by rfl⟩ : syracuseStep 12144761 = 9108571) B9108571
theorem B8096507 : Blo 2245435 8096507 := bstep (se 1 (by rfl) ⟨6072380, by rfl⟩ : syracuseStep 8096507 = 12144761) B12144761
theorem B5397671 : Blo 2245435 5397671 := bstep (se 1 (by rfl) ⟨4048253, by rfl⟩ : syracuseStep 5397671 = 8096507) B8096507
theorem B3598447 : Blo 2245435 3598447 := bstep (se 1 (by rfl) ⟨2698835, by rfl⟩ : syracuseStep 3598447 = 5397671) B5397671
theorem B4797929 : Blo 2245435 4797929 := bstep (se 2 (by rfl) ⟨1799223, by rfl⟩ : syracuseStep 4797929 = 3598447) B3598447
theorem B3198619 : Blo 2245435 3198619 := bstep (se 1 (by rfl) ⟨2398964, by rfl⟩ : syracuseStep 3198619 = 4797929) B4797929
theorem B4264825 : Blo 2245435 4264825 := bstep (se 2 (by rfl) ⟨1599309, by rfl⟩ : syracuseStep 4264825 = 3198619) B3198619
theorem B5686433 : Blo 2245435 5686433 := bstep (se 2 (by rfl) ⟨2132412, by rfl⟩ : syracuseStep 5686433 = 4264825) B4264825
theorem B3790955 : Blo 2245435 3790955 := bstep (se 1 (by rfl) ⟨2843216, by rfl⟩ : syracuseStep 3790955 = 5686433) B5686433
theorem B2527303 : Blo 2245435 2527303 := bstep (se 1 (by rfl) ⟨1895477, by rfl⟩ : syracuseStep 2527303 = 3790955) B3790955
theorem B3369737 : Blo 2245435 3369737 := bstep (se 2 (by rfl) ⟨1263651, by rfl⟩ : syracuseStep 3369737 = 2527303) B2527303
theorem B2246491 : Blo 2245435 2246491 := bstep (se 1 (by rfl) ⟨1684868, by rfl⟩ : syracuseStep 2246491 = 3369737) B3369737
theorem B11372885 : Blo 2245435 11372885 := bbase (se 10 (by rfl) ⟨16659, by rfl⟩ : syracuseStep 11372885 = 33319) (by norm_num)
theorem B7581923 : Blo 2245435 7581923 := bstep (se 1 (by rfl) ⟨5686442, by rfl⟩ : syracuseStep 7581923 = 11372885) B11372885
theorem B5054615 : Blo 2245435 5054615 := bstep (se 1 (by rfl) ⟨3790961, by rfl⟩ : syracuseStep 5054615 = 7581923) B7581923
theorem B3369743 : Blo 2245435 3369743 := bstep (se 1 (by rfl) ⟨2527307, by rfl⟩ : syracuseStep 3369743 = 5054615) B5054615
theorem B2246495 : Blo 2245435 2246495 := bstep (se 1 (by rfl) ⟨1684871, by rfl⟩ : syracuseStep 2246495 = 3369743) B3369743
theorem B3369749 : Blo 2245435 3369749 := bbase (se 6 (by rfl) ⟨78978, by rfl⟩ : syracuseStep 3369749 = 157957) (by norm_num)
theorem B2246499 : Blo 2245435 2246499 := bstep (se 1 (by rfl) ⟨1684874, by rfl⟩ : syracuseStep 2246499 = 3369749) B3369749
theorem B12144821 : Blo 2245435 12144821 := bbase (se 5 (by rfl) ⟨569288, by rfl⟩ : syracuseStep 12144821 = 1138577) (by norm_num)
theorem B32386189 : Blo 2245435 32386189 := bstep (se 3 (by rfl) ⟨6072410, by rfl⟩ : syracuseStep 32386189 = 12144821) B12144821
theorem B43181585 : Blo 2245435 43181585 := bstep (se 2 (by rfl) ⟨16193094, by rfl⟩ : syracuseStep 43181585 = 32386189) B32386189
theorem B28787723 : Blo 2245435 28787723 := bstep (se 1 (by rfl) ⟨21590792, by rfl⟩ : syracuseStep 28787723 = 43181585) B43181585
theorem B19191815 : Blo 2245435 19191815 := bstep (se 1 (by rfl) ⟨14393861, by rfl⟩ : syracuseStep 19191815 = 28787723) B28787723
theorem B12794543 : Blo 2245435 12794543 := bstep (se 1 (by rfl) ⟨9595907, by rfl⟩ : syracuseStep 12794543 = 19191815) B19191815
theorem B8529695 : Blo 2245435 8529695 := bstep (se 1 (by rfl) ⟨6397271, by rfl⟩ : syracuseStep 8529695 = 12794543) B12794543
theorem B5686463 : Blo 2245435 5686463 := bstep (se 1 (by rfl) ⟨4264847, by rfl⟩ : syracuseStep 5686463 = 8529695) B8529695
theorem B3790975 : Blo 2245435 3790975 := bstep (se 1 (by rfl) ⟨2843231, by rfl⟩ : syracuseStep 3790975 = 5686463) B5686463
theorem B5054633 : Blo 2245435 5054633 := bstep (se 2 (by rfl) ⟨1895487, by rfl⟩ : syracuseStep 5054633 = 3790975) B3790975
theorem B3369755 : Blo 2245435 3369755 := bstep (se 1 (by rfl) ⟨2527316, by rfl⟩ : syracuseStep 3369755 = 5054633) B5054633
theorem B2246503 : Blo 2245435 2246503 := bstep (se 1 (by rfl) ⟨1684877, by rfl⟩ : syracuseStep 2246503 = 3369755) B3369755
theorem B2527321 : Blo 2245435 2527321 := bbase (se 2 (by rfl) ⟨947745, by rfl⟩ : syracuseStep 2527321 = 1895491) (by norm_num)
theorem B3369761 : Blo 2245435 3369761 := bstep (se 2 (by rfl) ⟨1263660, by rfl⟩ : syracuseStep 3369761 = 2527321) B2527321
theorem B2246507 : Blo 2245435 2246507 := bstep (se 1 (by rfl) ⟨1684880, by rfl⟩ : syracuseStep 2246507 = 3369761) B3369761
theorem B2561809 : Blo 2245435 2561809 := bbase (se 2 (by rfl) ⟨960678, by rfl⟩ : syracuseStep 2561809 = 1921357) (by norm_num)
theorem B3415745 : Blo 2245435 3415745 := bstep (se 2 (by rfl) ⟨1280904, by rfl⟩ : syracuseStep 3415745 = 2561809) B2561809
theorem B2277163 : Blo 2245435 2277163 := bstep (se 1 (by rfl) ⟨1707872, by rfl⟩ : syracuseStep 2277163 = 3415745) B3415745
theorem B3036217 : Blo 2245435 3036217 := bstep (se 2 (by rfl) ⟨1138581, by rfl⟩ : syracuseStep 3036217 = 2277163) B2277163
theorem B4048289 : Blo 2245435 4048289 := bstep (se 2 (by rfl) ⟨1518108, by rfl⟩ : syracuseStep 4048289 = 3036217) B3036217
theorem B2698859 : Blo 2245435 2698859 := bstep (se 1 (by rfl) ⟨2024144, by rfl⟩ : syracuseStep 2698859 = 4048289) B4048289
theorem B7196957 : Blo 2245435 7196957 := bstep (se 3 (by rfl) ⟨1349429, by rfl⟩ : syracuseStep 7196957 = 2698859) B2698859
theorem B4797971 : Blo 2245435 4797971 := bstep (se 1 (by rfl) ⟨3598478, by rfl⟩ : syracuseStep 4797971 = 7196957) B7196957
theorem B3198647 : Blo 2245435 3198647 := bstep (se 1 (by rfl) ⟨2398985, by rfl⟩ : syracuseStep 3198647 = 4797971) B4797971
theorem B8529725 : Blo 2245435 8529725 := bstep (se 3 (by rfl) ⟨1599323, by rfl⟩ : syracuseStep 8529725 = 3198647) B3198647
theorem B5686483 : Blo 2245435 5686483 := bstep (se 1 (by rfl) ⟨4264862, by rfl⟩ : syracuseStep 5686483 = 8529725) B8529725
theorem B7581977 : Blo 2245435 7581977 := bstep (se 2 (by rfl) ⟨2843241, by rfl⟩ : syracuseStep 7581977 = 5686483) B5686483
theorem B5054651 : Blo 2245435 5054651 := bstep (se 1 (by rfl) ⟨3790988, by rfl⟩ : syracuseStep 5054651 = 7581977) B7581977
theorem B3369767 : Blo 2245435 3369767 := bstep (se 1 (by rfl) ⟨2527325, by rfl⟩ : syracuseStep 3369767 = 5054651) B5054651
theorem B2246511 : Blo 2245435 2246511 := bstep (se 1 (by rfl) ⟨1684883, by rfl⟩ : syracuseStep 2246511 = 3369767) B3369767
theorem B3369773 : Blo 2245435 3369773 := bbase (se 3 (by rfl) ⟨631832, by rfl⟩ : syracuseStep 3369773 = 1263665) (by norm_num)
theorem B2246515 : Blo 2245435 2246515 := bstep (se 1 (by rfl) ⟨1684886, by rfl⟩ : syracuseStep 2246515 = 3369773) B3369773
theorem B5054669 : Blo 2245435 5054669 := bbase (se 3 (by rfl) ⟨947750, by rfl⟩ : syracuseStep 5054669 = 1895501) (by norm_num)
theorem B3369779 : Blo 2245435 3369779 := bstep (se 1 (by rfl) ⟨2527334, by rfl⟩ : syracuseStep 3369779 = 5054669) B5054669
theorem B2246519 : Blo 2245435 2246519 := bstep (se 1 (by rfl) ⟨1684889, by rfl⟩ : syracuseStep 2246519 = 3369779) B3369779
theorem B2843257 : Blo 2245435 2843257 := bbase (se 2 (by rfl) ⟨1066221, by rfl⟩ : syracuseStep 2843257 = 2132443) (by norm_num)
theorem B3791009 : Blo 2245435 3791009 := bstep (se 2 (by rfl) ⟨1421628, by rfl⟩ : syracuseStep 3791009 = 2843257) B2843257
theorem B2527339 : Blo 2245435 2527339 := bstep (se 1 (by rfl) ⟨1895504, by rfl⟩ : syracuseStep 2527339 = 3791009) B3791009
theorem B3369785 : Blo 2245435 3369785 := bstep (se 2 (by rfl) ⟨1263669, by rfl⟩ : syracuseStep 3369785 = 2527339) B2527339
theorem B2246523 : Blo 2245435 2246523 := bstep (se 1 (by rfl) ⟨1684892, by rfl⟩ : syracuseStep 2246523 = 3369785) B3369785
theorem B4441853 : Blo 2245435 4441853 := bbase (se 3 (by rfl) ⟨832847, by rfl⟩ : syracuseStep 4441853 = 1665695) (by norm_num)
theorem B2961235 : Blo 2245435 2961235 := bstep (se 1 (by rfl) ⟨2220926, by rfl⟩ : syracuseStep 2961235 = 4441853) B4441853
theorem B3948313 : Blo 2245435 3948313 := bstep (se 2 (by rfl) ⟨1480617, by rfl⟩ : syracuseStep 3948313 = 2961235) B2961235
theorem B5264417 : Blo 2245435 5264417 := bstep (se 2 (by rfl) ⟨1974156, by rfl⟩ : syracuseStep 5264417 = 3948313) B3948313
theorem B3509611 : Blo 2245435 3509611 := bstep (se 1 (by rfl) ⟨2632208, by rfl⟩ : syracuseStep 3509611 = 5264417) B5264417
theorem B18717925 : Blo 2245435 18717925 := bstep (se 4 (by rfl) ⟨1754805, by rfl⟩ : syracuseStep 18717925 = 3509611) B3509611
theorem B24957233 : Blo 2245435 24957233 := bstep (se 2 (by rfl) ⟨9358962, by rfl⟩ : syracuseStep 24957233 = 18717925) B18717925
theorem B16638155 : Blo 2245435 16638155 := bstep (se 1 (by rfl) ⟨12478616, by rfl⟩ : syracuseStep 16638155 = 24957233) B24957233
theorem B11092103 : Blo 2245435 11092103 := bstep (se 1 (by rfl) ⟨8319077, by rfl⟩ : syracuseStep 11092103 = 16638155) B16638155
theorem B7394735 : Blo 2245435 7394735 := bstep (se 1 (by rfl) ⟨5546051, by rfl⟩ : syracuseStep 7394735 = 11092103) B11092103
theorem B4929823 : Blo 2245435 4929823 := bstep (se 1 (by rfl) ⟨3697367, by rfl⟩ : syracuseStep 4929823 = 7394735) B7394735
theorem B6573097 : Blo 2245435 6573097 := bstep (se 2 (by rfl) ⟨2464911, by rfl⟩ : syracuseStep 6573097 = 4929823) B4929823
theorem B8764129 : Blo 2245435 8764129 := bstep (se 2 (by rfl) ⟨3286548, by rfl⟩ : syracuseStep 8764129 = 6573097) B6573097
theorem B46742021 : Blo 2245435 46742021 := bstep (se 4 (by rfl) ⟨4382064, by rfl⟩ : syracuseStep 46742021 = 8764129) B8764129
theorem B31161347 : Blo 2245435 31161347 := bstep (se 1 (by rfl) ⟨23371010, by rfl⟩ : syracuseStep 31161347 = 46742021) B46742021
theorem B20774231 : Blo 2245435 20774231 := bstep (se 1 (by rfl) ⟨15580673, by rfl⟩ : syracuseStep 20774231 = 31161347) B31161347
theorem B13849487 : Blo 2245435 13849487 := bstep (se 1 (by rfl) ⟨10387115, by rfl⟩ : syracuseStep 13849487 = 20774231) B20774231
theorem B9232991 : Blo 2245435 9232991 := bstep (se 1 (by rfl) ⟨6924743, by rfl⟩ : syracuseStep 9232991 = 13849487) B13849487
theorem B6155327 : Blo 2245435 6155327 := bstep (se 1 (by rfl) ⟨4616495, by rfl⟩ : syracuseStep 6155327 = 9232991) B9232991
theorem B4103551 : Blo 2245435 4103551 := bstep (se 1 (by rfl) ⟨3077663, by rfl⟩ : syracuseStep 4103551 = 6155327) B6155327
theorem B5471401 : Blo 2245435 5471401 := bstep (se 2 (by rfl) ⟨2051775, by rfl⟩ : syracuseStep 5471401 = 4103551) B4103551
theorem B7295201 : Blo 2245435 7295201 := bstep (se 2 (by rfl) ⟨2735700, by rfl⟩ : syracuseStep 7295201 = 5471401) B5471401
theorem B4863467 : Blo 2245435 4863467 := bstep (se 1 (by rfl) ⟨3647600, by rfl⟩ : syracuseStep 4863467 = 7295201) B7295201
theorem B3242311 : Blo 2245435 3242311 := bstep (se 1 (by rfl) ⟨2431733, by rfl⟩ : syracuseStep 3242311 = 4863467) B4863467
theorem B17292325 : Blo 2245435 17292325 := bstep (se 4 (by rfl) ⟨1621155, by rfl⟩ : syracuseStep 17292325 = 3242311) B3242311
theorem B23056433 : Blo 2245435 23056433 := bstep (se 2 (by rfl) ⟨8646162, by rfl⟩ : syracuseStep 23056433 = 17292325) B17292325
theorem B15370955 : Blo 2245435 15370955 := bstep (se 1 (by rfl) ⟨11528216, by rfl⟩ : syracuseStep 15370955 = 23056433) B23056433
theorem B10247303 : Blo 2245435 10247303 := bstep (se 1 (by rfl) ⟨7685477, by rfl⟩ : syracuseStep 10247303 = 15370955) B15370955
theorem B6831535 : Blo 2245435 6831535 := bstep (se 1 (by rfl) ⟨5123651, by rfl⟩ : syracuseStep 6831535 = 10247303) B10247303
theorem B9108713 : Blo 2245435 9108713 := bstep (se 2 (by rfl) ⟨3415767, by rfl⟩ : syracuseStep 9108713 = 6831535) B6831535
theorem B24289901 : Blo 2245435 24289901 := bstep (se 3 (by rfl) ⟨4554356, by rfl⟩ : syracuseStep 24289901 = 9108713) B9108713
theorem B16193267 : Blo 2245435 16193267 := bstep (se 1 (by rfl) ⟨12144950, by rfl⟩ : syracuseStep 16193267 = 24289901) B24289901
theorem B10795511 : Blo 2245435 10795511 := bstep (se 1 (by rfl) ⟨8096633, by rfl⟩ : syracuseStep 10795511 = 16193267) B16193267
theorem B7197007 : Blo 2245435 7197007 := bstep (se 1 (by rfl) ⟨5397755, by rfl⟩ : syracuseStep 7197007 = 10795511) B10795511
theorem B9596009 : Blo 2245435 9596009 := bstep (se 2 (by rfl) ⟨3598503, by rfl⟩ : syracuseStep 9596009 = 7197007) B7197007
theorem B25589357 : Blo 2245435 25589357 := bstep (se 3 (by rfl) ⟨4798004, by rfl⟩ : syracuseStep 25589357 = 9596009) B9596009
theorem B17059571 : Blo 2245435 17059571 := bstep (se 1 (by rfl) ⟨12794678, by rfl⟩ : syracuseStep 17059571 = 25589357) B25589357
theorem B11373047 : Blo 2245435 11373047 := bstep (se 1 (by rfl) ⟨8529785, by rfl⟩ : syracuseStep 11373047 = 17059571) B17059571
theorem B7582031 : Blo 2245435 7582031 := bstep (se 1 (by rfl) ⟨5686523, by rfl⟩ : syracuseStep 7582031 = 11373047) B11373047
theorem B5054687 : Blo 2245435 5054687 := bstep (se 1 (by rfl) ⟨3791015, by rfl⟩ : syracuseStep 5054687 = 7582031) B7582031
theorem B3369791 : Blo 2245435 3369791 := bstep (se 1 (by rfl) ⟨2527343, by rfl⟩ : syracuseStep 3369791 = 5054687) B5054687
theorem B2246527 : Blo 2245435 2246527 := bstep (se 1 (by rfl) ⟨1684895, by rfl⟩ : syracuseStep 2246527 = 3369791) B3369791
theorem B3369797 : Blo 2245435 3369797 := bbase (se 4 (by rfl) ⟨315918, by rfl⟩ : syracuseStep 3369797 = 631837) (by norm_num)
theorem B2246531 : Blo 2245435 2246531 := bstep (se 1 (by rfl) ⟨1684898, by rfl⟩ : syracuseStep 2246531 = 3369797) B3369797
theorem B3791029 : Blo 2245435 3791029 := bbase (se 5 (by rfl) ⟨177704, by rfl⟩ : syracuseStep 3791029 = 355409) (by norm_num)
theorem B5054705 : Blo 2245435 5054705 := bstep (se 2 (by rfl) ⟨1895514, by rfl⟩ : syracuseStep 5054705 = 3791029) B3791029
theorem B3369803 : Blo 2245435 3369803 := bstep (se 1 (by rfl) ⟨2527352, by rfl⟩ : syracuseStep 3369803 = 5054705) B5054705
theorem B2246535 : Blo 2245435 2246535 := bstep (se 1 (by rfl) ⟨1684901, by rfl⟩ : syracuseStep 2246535 = 3369803) B3369803
theorem B2527357 : Blo 2245435 2527357 := bbase (se 3 (by rfl) ⟨473879, by rfl⟩ : syracuseStep 2527357 = 947759) (by norm_num)
theorem B3369809 : Blo 2245435 3369809 := bstep (se 2 (by rfl) ⟨1263678, by rfl⟩ : syracuseStep 3369809 = 2527357) B2527357
theorem B2246539 : Blo 2245435 2246539 := bstep (se 1 (by rfl) ⟨1684904, by rfl⟩ : syracuseStep 2246539 = 3369809) B3369809
theorem B7582085 : Blo 2245435 7582085 := bbase (se 4 (by rfl) ⟨710820, by rfl⟩ : syracuseStep 7582085 = 1421641) (by norm_num)
theorem B5054723 : Blo 2245435 5054723 := bstep (se 1 (by rfl) ⟨3791042, by rfl⟩ : syracuseStep 5054723 = 7582085) B7582085
theorem B3369815 : Blo 2245435 3369815 := bstep (se 1 (by rfl) ⟨2527361, by rfl⟩ : syracuseStep 3369815 = 5054723) B5054723
theorem B2246543 : Blo 2245435 2246543 := bstep (se 1 (by rfl) ⟨1684907, by rfl⟩ : syracuseStep 2246543 = 3369815) B3369815
theorem B3369821 : Blo 2245435 3369821 := bbase (se 3 (by rfl) ⟨631841, by rfl⟩ : syracuseStep 3369821 = 1263683) (by norm_num)
theorem B2246547 : Blo 2245435 2246547 := bstep (se 1 (by rfl) ⟨1684910, by rfl⟩ : syracuseStep 2246547 = 3369821) B3369821
theorem B5054741 : Blo 2245435 5054741 := bbase (se 6 (by rfl) ⟨118470, by rfl⟩ : syracuseStep 5054741 = 236941) (by norm_num)
theorem B3369827 : Blo 2245435 3369827 := bstep (se 1 (by rfl) ⟨2527370, by rfl⟩ : syracuseStep 3369827 = 5054741) B5054741
theorem B2246551 : Blo 2245435 2246551 := bstep (se 1 (by rfl) ⟨1684913, by rfl⟩ : syracuseStep 2246551 = 3369827) B3369827
theorem B8529893 : Blo 2245435 8529893 := bbase (se 4 (by rfl) ⟨799677, by rfl⟩ : syracuseStep 8529893 = 1599355) (by norm_num)
theorem B5686595 : Blo 2245435 5686595 := bstep (se 1 (by rfl) ⟨4264946, by rfl⟩ : syracuseStep 5686595 = 8529893) B8529893
theorem B3791063 : Blo 2245435 3791063 := bstep (se 1 (by rfl) ⟨2843297, by rfl⟩ : syracuseStep 3791063 = 5686595) B5686595
theorem B2527375 : Blo 2245435 2527375 := bstep (se 1 (by rfl) ⟨1895531, by rfl⟩ : syracuseStep 2527375 = 3791063) B3791063
theorem B3369833 : Blo 2245435 3369833 := bstep (se 2 (by rfl) ⟨1263687, by rfl⟩ : syracuseStep 3369833 = 2527375) B2527375
theorem B2246555 : Blo 2245435 2246555 := bstep (se 1 (by rfl) ⟨1684916, by rfl⟩ : syracuseStep 2246555 = 3369833) B3369833
theorem B2735741 : Blo 2245435 2735741 := bbase (se 3 (by rfl) ⟨512951, by rfl⟩ : syracuseStep 2735741 = 1025903) (by norm_num)
theorem B7295309 : Blo 2245435 7295309 := bstep (se 3 (by rfl) ⟨1367870, by rfl⟩ : syracuseStep 7295309 = 2735741) B2735741
theorem B4863539 : Blo 2245435 4863539 := bstep (se 1 (by rfl) ⟨3647654, by rfl⟩ : syracuseStep 4863539 = 7295309) B7295309
theorem B3242359 : Blo 2245435 3242359 := bstep (se 1 (by rfl) ⟨2431769, by rfl⟩ : syracuseStep 3242359 = 4863539) B4863539
theorem B4323145 : Blo 2245435 4323145 := bstep (se 2 (by rfl) ⟨1621179, by rfl⟩ : syracuseStep 4323145 = 3242359) B3242359
theorem B5764193 : Blo 2245435 5764193 := bstep (se 2 (by rfl) ⟨2161572, by rfl⟩ : syracuseStep 5764193 = 4323145) B4323145
theorem B3842795 : Blo 2245435 3842795 := bstep (se 1 (by rfl) ⟨2882096, by rfl⟩ : syracuseStep 3842795 = 5764193) B5764193
theorem B2561863 : Blo 2245435 2561863 := bstep (se 1 (by rfl) ⟨1921397, by rfl⟩ : syracuseStep 2561863 = 3842795) B3842795
theorem B3415817 : Blo 2245435 3415817 := bstep (se 2 (by rfl) ⟨1280931, by rfl⟩ : syracuseStep 3415817 = 2561863) B2561863
theorem B9108845 : Blo 2245435 9108845 := bstep (se 3 (by rfl) ⟨1707908, by rfl⟩ : syracuseStep 9108845 = 3415817) B3415817
theorem B6072563 : Blo 2245435 6072563 := bstep (se 1 (by rfl) ⟨4554422, by rfl⟩ : syracuseStep 6072563 = 9108845) B9108845
theorem B4048375 : Blo 2245435 4048375 := bstep (se 1 (by rfl) ⟨3036281, by rfl⟩ : syracuseStep 4048375 = 6072563) B6072563
theorem B5397833 : Blo 2245435 5397833 := bstep (se 2 (by rfl) ⟨2024187, by rfl⟩ : syracuseStep 5397833 = 4048375) B4048375
theorem B3598555 : Blo 2245435 3598555 := bstep (se 1 (by rfl) ⟨2698916, by rfl⟩ : syracuseStep 3598555 = 5397833) B5397833
theorem B4798073 : Blo 2245435 4798073 := bstep (se 2 (by rfl) ⟨1799277, by rfl⟩ : syracuseStep 4798073 = 3598555) B3598555
theorem B12794861 : Blo 2245435 12794861 := bstep (se 3 (by rfl) ⟨2399036, by rfl⟩ : syracuseStep 12794861 = 4798073) B4798073
theorem B8529907 : Blo 2245435 8529907 := bstep (se 1 (by rfl) ⟨6397430, by rfl⟩ : syracuseStep 8529907 = 12794861) B12794861
theorem B11373209 : Blo 2245435 11373209 := bstep (se 2 (by rfl) ⟨4264953, by rfl⟩ : syracuseStep 11373209 = 8529907) B8529907
theorem B7582139 : Blo 2245435 7582139 := bstep (se 1 (by rfl) ⟨5686604, by rfl⟩ : syracuseStep 7582139 = 11373209) B11373209
theorem B5054759 : Blo 2245435 5054759 := bstep (se 1 (by rfl) ⟨3791069, by rfl⟩ : syracuseStep 5054759 = 7582139) B7582139
theorem B3369839 : Blo 2245435 3369839 := bstep (se 1 (by rfl) ⟨2527379, by rfl⟩ : syracuseStep 3369839 = 5054759) B5054759
theorem B2246559 : Blo 2245435 2246559 := bstep (se 1 (by rfl) ⟨1684919, by rfl⟩ : syracuseStep 2246559 = 3369839) B3369839
theorem B3369845 : Blo 2245435 3369845 := bbase (se 5 (by rfl) ⟨157961, by rfl⟩ : syracuseStep 3369845 = 315923) (by norm_num)
theorem B2246563 : Blo 2245435 2246563 := bstep (se 1 (by rfl) ⟨1684922, by rfl⟩ : syracuseStep 2246563 = 3369845) B3369845
theorem B5397853 : Blo 2245435 5397853 := bbase (se 3 (by rfl) ⟨1012097, by rfl⟩ : syracuseStep 5397853 = 2024195) (by norm_num)
theorem B7197137 : Blo 2245435 7197137 := bstep (se 2 (by rfl) ⟨2698926, by rfl⟩ : syracuseStep 7197137 = 5397853) B5397853
theorem B4798091 : Blo 2245435 4798091 := bstep (se 1 (by rfl) ⟨3598568, by rfl⟩ : syracuseStep 4798091 = 7197137) B7197137
theorem B3198727 : Blo 2245435 3198727 := bstep (se 1 (by rfl) ⟨2399045, by rfl⟩ : syracuseStep 3198727 = 4798091) B4798091
theorem B4264969 : Blo 2245435 4264969 := bstep (se 2 (by rfl) ⟨1599363, by rfl⟩ : syracuseStep 4264969 = 3198727) B3198727
theorem B5686625 : Blo 2245435 5686625 := bstep (se 2 (by rfl) ⟨2132484, by rfl⟩ : syracuseStep 5686625 = 4264969) B4264969
theorem B3791083 : Blo 2245435 3791083 := bstep (se 1 (by rfl) ⟨2843312, by rfl⟩ : syracuseStep 3791083 = 5686625) B5686625
theorem B5054777 : Blo 2245435 5054777 := bstep (se 2 (by rfl) ⟨1895541, by rfl⟩ : syracuseStep 5054777 = 3791083) B3791083
theorem B3369851 : Blo 2245435 3369851 := bstep (se 1 (by rfl) ⟨2527388, by rfl⟩ : syracuseStep 3369851 = 5054777) B5054777
theorem B2246567 : Blo 2245435 2246567 := bstep (se 1 (by rfl) ⟨1684925, by rfl⟩ : syracuseStep 2246567 = 3369851) B3369851
theorem B2527393 : Blo 2245435 2527393 := bbase (se 2 (by rfl) ⟨947772, by rfl⟩ : syracuseStep 2527393 = 1895545) (by norm_num)
theorem B3369857 : Blo 2245435 3369857 := bstep (se 2 (by rfl) ⟨1263696, by rfl⟩ : syracuseStep 3369857 = 2527393) B2527393
theorem B2246571 : Blo 2245435 2246571 := bstep (se 1 (by rfl) ⟨1684928, by rfl⟩ : syracuseStep 2246571 = 3369857) B3369857
theorem B5686645 : Blo 2245435 5686645 := bbase (se 5 (by rfl) ⟨266561, by rfl⟩ : syracuseStep 5686645 = 533123) (by norm_num)
theorem B7582193 : Blo 2245435 7582193 := bstep (se 2 (by rfl) ⟨2843322, by rfl⟩ : syracuseStep 7582193 = 5686645) B5686645
theorem B5054795 : Blo 2245435 5054795 := bstep (se 1 (by rfl) ⟨3791096, by rfl⟩ : syracuseStep 5054795 = 7582193) B7582193
theorem B3369863 : Blo 2245435 3369863 := bstep (se 1 (by rfl) ⟨2527397, by rfl⟩ : syracuseStep 3369863 = 5054795) B5054795
theorem B2246575 : Blo 2245435 2246575 := bstep (se 1 (by rfl) ⟨1684931, by rfl⟩ : syracuseStep 2246575 = 3369863) B3369863
theorem B3369869 : Blo 2245435 3369869 := bbase (se 3 (by rfl) ⟨631850, by rfl⟩ : syracuseStep 3369869 = 1263701) (by norm_num)
theorem B2246579 : Blo 2245435 2246579 := bstep (se 1 (by rfl) ⟨1684934, by rfl⟩ : syracuseStep 2246579 = 3369869) B3369869
theorem B5054813 : Blo 2245435 5054813 := bbase (se 3 (by rfl) ⟨947777, by rfl⟩ : syracuseStep 5054813 = 1895555) (by norm_num)
theorem B3369875 : Blo 2245435 3369875 := bstep (se 1 (by rfl) ⟨2527406, by rfl⟩ : syracuseStep 3369875 = 5054813) B5054813
theorem B2246583 : Blo 2245435 2246583 := bstep (se 1 (by rfl) ⟨1684937, by rfl⟩ : syracuseStep 2246583 = 3369875) B3369875
theorem B3791117 : Blo 2245435 3791117 := bbase (se 3 (by rfl) ⟨710834, by rfl⟩ : syracuseStep 3791117 = 1421669) (by norm_num)
theorem B2527411 : Blo 2245435 2527411 := bstep (se 1 (by rfl) ⟨1895558, by rfl⟩ : syracuseStep 2527411 = 3791117) B3791117
theorem B3369881 : Blo 2245435 3369881 := bstep (se 2 (by rfl) ⟨1263705, by rfl⟩ : syracuseStep 3369881 = 2527411) B2527411
theorem B2246587 : Blo 2245435 2246587 := bstep (se 1 (by rfl) ⟨1684940, by rfl⟩ : syracuseStep 2246587 = 3369881) B3369881
theorem B19192565 : Blo 2245435 19192565 := bbase (se 5 (by rfl) ⟨899651, by rfl⟩ : syracuseStep 19192565 = 1799303) (by norm_num)
theorem B12795043 : Blo 2245435 12795043 := bstep (se 1 (by rfl) ⟨9596282, by rfl⟩ : syracuseStep 12795043 = 19192565) B19192565
theorem B17060057 : Blo 2245435 17060057 := bstep (se 2 (by rfl) ⟨6397521, by rfl⟩ : syracuseStep 17060057 = 12795043) B12795043
theorem B11373371 : Blo 2245435 11373371 := bstep (se 1 (by rfl) ⟨8530028, by rfl⟩ : syracuseStep 11373371 = 17060057) B17060057
theorem B7582247 : Blo 2245435 7582247 := bstep (se 1 (by rfl) ⟨5686685, by rfl⟩ : syracuseStep 7582247 = 11373371) B11373371
theorem B5054831 : Blo 2245435 5054831 := bstep (se 1 (by rfl) ⟨3791123, by rfl⟩ : syracuseStep 5054831 = 7582247) B7582247
theorem B3369887 : Blo 2245435 3369887 := bstep (se 1 (by rfl) ⟨2527415, by rfl⟩ : syracuseStep 3369887 = 5054831) B5054831
theorem B2246591 : Blo 2245435 2246591 := bstep (se 1 (by rfl) ⟨1684943, by rfl⟩ : syracuseStep 2246591 = 3369887) B3369887
theorem B3369893 : Blo 2245435 3369893 := bbase (se 4 (by rfl) ⟨315927, by rfl⟩ : syracuseStep 3369893 = 631855) (by norm_num)
theorem B2246595 : Blo 2245435 2246595 := bstep (se 1 (by rfl) ⟨1684946, by rfl⟩ : syracuseStep 2246595 = 3369893) B3369893
theorem B2843353 : Blo 2245435 2843353 := bbase (se 2 (by rfl) ⟨1066257, by rfl⟩ : syracuseStep 2843353 = 2132515) (by norm_num)
theorem B3791137 : Blo 2245435 3791137 := bstep (se 2 (by rfl) ⟨1421676, by rfl⟩ : syracuseStep 3791137 = 2843353) B2843353
theorem B5054849 : Blo 2245435 5054849 := bstep (se 2 (by rfl) ⟨1895568, by rfl⟩ : syracuseStep 5054849 = 3791137) B3791137
theorem B3369899 : Blo 2245435 3369899 := bstep (se 1 (by rfl) ⟨2527424, by rfl⟩ : syracuseStep 3369899 = 5054849) B5054849
theorem B2246599 : Blo 2245435 2246599 := bstep (se 1 (by rfl) ⟨1684949, by rfl⟩ : syracuseStep 2246599 = 3369899) B3369899
theorem B2527429 : Blo 2245435 2527429 := bbase (se 4 (by rfl) ⟨236946, by rfl⟩ : syracuseStep 2527429 = 473893) (by norm_num)
theorem B3369905 : Blo 2245435 3369905 := bstep (se 2 (by rfl) ⟨1263714, by rfl⟩ : syracuseStep 3369905 = 2527429) B2527429
theorem B2246603 : Blo 2245435 2246603 := bstep (se 1 (by rfl) ⟨1684952, by rfl⟩ : syracuseStep 2246603 = 3369905) B3369905
theorem B4265045 : Blo 2245435 4265045 := bbase (se 8 (by rfl) ⟨24990, by rfl⟩ : syracuseStep 4265045 = 49981) (by norm_num)
theorem B2843363 : Blo 2245435 2843363 := bstep (se 1 (by rfl) ⟨2132522, by rfl⟩ : syracuseStep 2843363 = 4265045) B4265045
theorem B7582301 : Blo 2245435 7582301 := bstep (se 3 (by rfl) ⟨1421681, by rfl⟩ : syracuseStep 7582301 = 2843363) B2843363
theorem B5054867 : Blo 2245435 5054867 := bstep (se 1 (by rfl) ⟨3791150, by rfl⟩ : syracuseStep 5054867 = 7582301) B7582301
theorem B3369911 : Blo 2245435 3369911 := bstep (se 1 (by rfl) ⟨2527433, by rfl⟩ : syracuseStep 3369911 = 5054867) B5054867
theorem B2246607 : Blo 2245435 2246607 := bstep (se 1 (by rfl) ⟨1684955, by rfl⟩ : syracuseStep 2246607 = 3369911) B3369911
theorem B3369917 : Blo 2245435 3369917 := bbase (se 3 (by rfl) ⟨631859, by rfl⟩ : syracuseStep 3369917 = 1263719) (by norm_num)
theorem B2246611 : Blo 2245435 2246611 := bstep (se 1 (by rfl) ⟨1684958, by rfl⟩ : syracuseStep 2246611 = 3369917) B3369917
theorem B5054885 : Blo 2245435 5054885 := bbase (se 4 (by rfl) ⟨473895, by rfl⟩ : syracuseStep 5054885 = 947791) (by norm_num)
theorem B3369923 : Blo 2245435 3369923 := bstep (se 1 (by rfl) ⟨2527442, by rfl⟩ : syracuseStep 3369923 = 5054885) B5054885
theorem B2246615 : Blo 2245435 2246615 := bstep (se 1 (by rfl) ⟨1684961, by rfl⟩ : syracuseStep 2246615 = 3369923) B3369923
theorem B5686757 : Blo 2245435 5686757 := bbase (se 4 (by rfl) ⟨533133, by rfl⟩ : syracuseStep 5686757 = 1066267) (by norm_num)
theorem B3791171 : Blo 2245435 3791171 := bstep (se 1 (by rfl) ⟨2843378, by rfl⟩ : syracuseStep 3791171 = 5686757) B5686757
theorem B2527447 : Blo 2245435 2527447 := bstep (se 1 (by rfl) ⟨1895585, by rfl⟩ : syracuseStep 2527447 = 3791171) B3791171
theorem B3369929 : Blo 2245435 3369929 := bstep (se 2 (by rfl) ⟨1263723, by rfl⟩ : syracuseStep 3369929 = 2527447) B2527447
theorem B2246619 : Blo 2245435 2246619 := bstep (se 1 (by rfl) ⟨1684964, by rfl⟩ : syracuseStep 2246619 = 3369929) B3369929
theorem B2399105 : Blo 2245435 2399105 := bbase (se 2 (by rfl) ⟨899664, by rfl⟩ : syracuseStep 2399105 = 1799329) (by norm_num)
theorem B6397613 : Blo 2245435 6397613 := bstep (se 3 (by rfl) ⟨1199552, by rfl⟩ : syracuseStep 6397613 = 2399105) B2399105
theorem B4265075 : Blo 2245435 4265075 := bstep (se 1 (by rfl) ⟨3198806, by rfl⟩ : syracuseStep 4265075 = 6397613) B6397613
theorem B11373533 : Blo 2245435 11373533 := bstep (se 3 (by rfl) ⟨2132537, by rfl⟩ : syracuseStep 11373533 = 4265075) B4265075
theorem B7582355 : Blo 2245435 7582355 := bstep (se 1 (by rfl) ⟨5686766, by rfl⟩ : syracuseStep 7582355 = 11373533) B11373533
theorem B5054903 : Blo 2245435 5054903 := bstep (se 1 (by rfl) ⟨3791177, by rfl⟩ : syracuseStep 5054903 = 7582355) B7582355
theorem B3369935 : Blo 2245435 3369935 := bstep (se 1 (by rfl) ⟨2527451, by rfl⟩ : syracuseStep 3369935 = 5054903) B5054903
theorem B2246623 : Blo 2245435 2246623 := bstep (se 1 (by rfl) ⟨1684967, by rfl⟩ : syracuseStep 2246623 = 3369935) B3369935
theorem B3369941 : Blo 2245435 3369941 := bbase (se 7 (by rfl) ⟨39491, by rfl⟩ : syracuseStep 3369941 = 78983) (by norm_num)
theorem B2246627 : Blo 2245435 2246627 := bstep (se 1 (by rfl) ⟨1684970, by rfl⟩ : syracuseStep 2246627 = 3369941) B3369941
theorem B8530181 : Blo 2245435 8530181 := bbase (se 4 (by rfl) ⟨799704, by rfl⟩ : syracuseStep 8530181 = 1599409) (by norm_num)
theorem B5686787 : Blo 2245435 5686787 := bstep (se 1 (by rfl) ⟨4265090, by rfl⟩ : syracuseStep 5686787 = 8530181) B8530181
theorem B3791191 : Blo 2245435 3791191 := bstep (se 1 (by rfl) ⟨2843393, by rfl⟩ : syracuseStep 3791191 = 5686787) B5686787
theorem B5054921 : Blo 2245435 5054921 := bstep (se 2 (by rfl) ⟨1895595, by rfl⟩ : syracuseStep 5054921 = 3791191) B3791191
theorem B3369947 : Blo 2245435 3369947 := bstep (se 1 (by rfl) ⟨2527460, by rfl⟩ : syracuseStep 3369947 = 5054921) B5054921
theorem B2246631 : Blo 2245435 2246631 := bstep (se 1 (by rfl) ⟨1684973, by rfl⟩ : syracuseStep 2246631 = 3369947) B3369947
theorem B2527465 : Blo 2245435 2527465 := bbase (se 2 (by rfl) ⟨947799, by rfl⟩ : syracuseStep 2527465 = 1895599) (by norm_num)
theorem B3369953 : Blo 2245435 3369953 := bstep (se 2 (by rfl) ⟨1263732, by rfl⟩ : syracuseStep 3369953 = 2527465) B2527465
theorem B2246635 : Blo 2245435 2246635 := bstep (se 1 (by rfl) ⟨1684976, by rfl⟩ : syracuseStep 2246635 = 3369953) B3369953
theorem B12795317 : Blo 2245435 12795317 := bbase (se 5 (by rfl) ⟨599780, by rfl⟩ : syracuseStep 12795317 = 1199561) (by norm_num)
theorem B8530211 : Blo 2245435 8530211 := bstep (se 1 (by rfl) ⟨6397658, by rfl⟩ : syracuseStep 8530211 = 12795317) B12795317
theorem B5686807 : Blo 2245435 5686807 := bstep (se 1 (by rfl) ⟨4265105, by rfl⟩ : syracuseStep 5686807 = 8530211) B8530211
theorem B7582409 : Blo 2245435 7582409 := bstep (se 2 (by rfl) ⟨2843403, by rfl⟩ : syracuseStep 7582409 = 5686807) B5686807
theorem B5054939 : Blo 2245435 5054939 := bstep (se 1 (by rfl) ⟨3791204, by rfl⟩ : syracuseStep 5054939 = 7582409) B7582409
theorem B3369959 : Blo 2245435 3369959 := bstep (se 1 (by rfl) ⟨2527469, by rfl⟩ : syracuseStep 3369959 = 5054939) B5054939
theorem B2246639 : Blo 2245435 2246639 := bstep (se 1 (by rfl) ⟨1684979, by rfl⟩ : syracuseStep 2246639 = 3369959) B3369959
theorem B3369965 : Blo 2245435 3369965 := bbase (se 3 (by rfl) ⟨631868, by rfl⟩ : syracuseStep 3369965 = 1263737) (by norm_num)
theorem B2246643 : Blo 2245435 2246643 := bstep (se 1 (by rfl) ⟨1684982, by rfl⟩ : syracuseStep 2246643 = 3369965) B3369965
theorem B5054957 : Blo 2245435 5054957 := bbase (se 3 (by rfl) ⟨947804, by rfl⟩ : syracuseStep 5054957 = 1895609) (by norm_num)
theorem B3369971 : Blo 2245435 3369971 := bstep (se 1 (by rfl) ⟨2527478, by rfl⟩ : syracuseStep 3369971 = 5054957) B5054957
theorem B2246647 : Blo 2245435 2246647 := bstep (se 1 (by rfl) ⟨1684985, by rfl⟩ : syracuseStep 2246647 = 3369971) B3369971
theorem B13663829 : Blo 2245435 13663829 := bbase (se 8 (by rfl) ⟨80061, by rfl⟩ : syracuseStep 13663829 = 160123) (by norm_num)
theorem B36436877 : Blo 2245435 36436877 := bstep (se 3 (by rfl) ⟨6831914, by rfl⟩ : syracuseStep 36436877 = 13663829) B13663829
theorem B24291251 : Blo 2245435 24291251 := bstep (se 1 (by rfl) ⟨18218438, by rfl⟩ : syracuseStep 24291251 = 36436877) B36436877
theorem B16194167 : Blo 2245435 16194167 := bstep (se 1 (by rfl) ⟨12145625, by rfl⟩ : syracuseStep 16194167 = 24291251) B24291251
theorem B10796111 : Blo 2245435 10796111 := bstep (se 1 (by rfl) ⟨8097083, by rfl⟩ : syracuseStep 10796111 = 16194167) B16194167
theorem B7197407 : Blo 2245435 7197407 := bstep (se 1 (by rfl) ⟨5398055, by rfl⟩ : syracuseStep 7197407 = 10796111) B10796111
theorem B4798271 : Blo 2245435 4798271 := bstep (se 1 (by rfl) ⟨3598703, by rfl⟩ : syracuseStep 4798271 = 7197407) B7197407
theorem B3198847 : Blo 2245435 3198847 := bstep (se 1 (by rfl) ⟨2399135, by rfl⟩ : syracuseStep 3198847 = 4798271) B4798271
theorem B4265129 : Blo 2245435 4265129 := bstep (se 2 (by rfl) ⟨1599423, by rfl⟩ : syracuseStep 4265129 = 3198847) B3198847
theorem B2843419 : Blo 2245435 2843419 := bstep (se 1 (by rfl) ⟨2132564, by rfl⟩ : syracuseStep 2843419 = 4265129) B4265129
theorem B3791225 : Blo 2245435 3791225 := bstep (se 2 (by rfl) ⟨1421709, by rfl⟩ : syracuseStep 3791225 = 2843419) B2843419
theorem B2527483 : Blo 2245435 2527483 := bstep (se 1 (by rfl) ⟨1895612, by rfl⟩ : syracuseStep 2527483 = 3791225) B3791225
theorem B3369977 : Blo 2245435 3369977 := bstep (se 2 (by rfl) ⟨1263741, by rfl⟩ : syracuseStep 3369977 = 2527483) B2527483
theorem B2246651 : Blo 2245435 2246651 := bstep (se 1 (by rfl) ⟨1684988, by rfl⟩ : syracuseStep 2246651 = 3369977) B3369977
theorem B2632357 : Blo 2245435 2632357 := bbase (se 4 (by rfl) ⟨246783, by rfl⟩ : syracuseStep 2632357 = 493567) (by norm_num)
theorem B14039237 : Blo 2245435 14039237 := bstep (se 4 (by rfl) ⟨1316178, by rfl⟩ : syracuseStep 14039237 = 2632357) B2632357
theorem B9359491 : Blo 2245435 9359491 := bstep (se 1 (by rfl) ⟨7019618, by rfl⟩ : syracuseStep 9359491 = 14039237) B14039237
theorem B12479321 : Blo 2245435 12479321 := bstep (se 2 (by rfl) ⟨4679745, by rfl⟩ : syracuseStep 12479321 = 9359491) B9359491
theorem B8319547 : Blo 2245435 8319547 := bstep (se 1 (by rfl) ⟨6239660, by rfl⟩ : syracuseStep 8319547 = 12479321) B12479321
theorem B11092729 : Blo 2245435 11092729 := bstep (se 2 (by rfl) ⟨4159773, by rfl⟩ : syracuseStep 11092729 = 8319547) B8319547
theorem B14790305 : Blo 2245435 14790305 := bstep (se 2 (by rfl) ⟨5546364, by rfl⟩ : syracuseStep 14790305 = 11092729) B11092729
theorem B9860203 : Blo 2245435 9860203 := bstep (se 1 (by rfl) ⟨7395152, by rfl⟩ : syracuseStep 9860203 = 14790305) B14790305
theorem B13146937 : Blo 2245435 13146937 := bstep (se 2 (by rfl) ⟨4930101, by rfl⟩ : syracuseStep 13146937 = 9860203) B9860203
theorem B70116997 : Blo 2245435 70116997 := bstep (se 4 (by rfl) ⟨6573468, by rfl⟩ : syracuseStep 70116997 = 13146937) B13146937
theorem B93489329 : Blo 2245435 93489329 := bstep (se 2 (by rfl) ⟨35058498, by rfl⟩ : syracuseStep 93489329 = 70116997) B70116997
theorem B62326219 : Blo 2245435 62326219 := bstep (se 1 (by rfl) ⟨46744664, by rfl⟩ : syracuseStep 62326219 = 93489329) B93489329
theorem B83101625 : Blo 2245435 83101625 := bstep (se 2 (by rfl) ⟨31163109, by rfl⟩ : syracuseStep 83101625 = 62326219) B62326219
theorem B55401083 : Blo 2245435 55401083 := bstep (se 1 (by rfl) ⟨41550812, by rfl⟩ : syracuseStep 55401083 = 83101625) B83101625
theorem B36934055 : Blo 2245435 36934055 := bstep (se 1 (by rfl) ⟨27700541, by rfl⟩ : syracuseStep 36934055 = 55401083) B55401083
theorem B24622703 : Blo 2245435 24622703 := bstep (se 1 (by rfl) ⟨18467027, by rfl⟩ : syracuseStep 24622703 = 36934055) B36934055
theorem B16415135 : Blo 2245435 16415135 := bstep (se 1 (by rfl) ⟨12311351, by rfl⟩ : syracuseStep 16415135 = 24622703) B24622703
theorem B10943423 : Blo 2245435 10943423 := bstep (se 1 (by rfl) ⟨8207567, by rfl⟩ : syracuseStep 10943423 = 16415135) B16415135
theorem B7295615 : Blo 2245435 7295615 := bstep (se 1 (by rfl) ⟨5471711, by rfl⟩ : syracuseStep 7295615 = 10943423) B10943423
theorem B4863743 : Blo 2245435 4863743 := bstep (se 1 (by rfl) ⟨3647807, by rfl⟩ : syracuseStep 4863743 = 7295615) B7295615
theorem B3242495 : Blo 2245435 3242495 := bstep (se 1 (by rfl) ⟨2431871, by rfl⟩ : syracuseStep 3242495 = 4863743) B4863743
theorem B8646653 : Blo 2245435 8646653 := bstep (se 3 (by rfl) ⟨1621247, by rfl⟩ : syracuseStep 8646653 = 3242495) B3242495
theorem B23057741 : Blo 2245435 23057741 := bstep (se 3 (by rfl) ⟨4323326, by rfl⟩ : syracuseStep 23057741 = 8646653) B8646653
theorem B61487309 : Blo 2245435 61487309 := bstep (se 3 (by rfl) ⟨11528870, by rfl⟩ : syracuseStep 61487309 = 23057741) B23057741
theorem B163966157 : Blo 2245435 163966157 := bstep (se 3 (by rfl) ⟨30743654, by rfl⟩ : syracuseStep 163966157 = 61487309) B61487309
theorem B109310771 : Blo 2245435 109310771 := bstep (se 1 (by rfl) ⟨81983078, by rfl⟩ : syracuseStep 109310771 = 163966157) B163966157
theorem B72873847 : Blo 2245435 72873847 := bstep (se 1 (by rfl) ⟨54655385, by rfl⟩ : syracuseStep 72873847 = 109310771) B109310771
theorem B97165129 : Blo 2245435 97165129 := bstep (se 2 (by rfl) ⟨36436923, by rfl⟩ : syracuseStep 97165129 = 72873847) B72873847
theorem B129553505 : Blo 2245435 129553505 := bstep (se 2 (by rfl) ⟨48582564, by rfl⟩ : syracuseStep 129553505 = 97165129) B97165129
theorem B86369003 : Blo 2245435 86369003 := bstep (se 1 (by rfl) ⟨64776752, by rfl⟩ : syracuseStep 86369003 = 129553505) B129553505
theorem B57579335 : Blo 2245435 57579335 := bstep (se 1 (by rfl) ⟨43184501, by rfl⟩ : syracuseStep 57579335 = 86369003) B86369003
theorem B38386223 : Blo 2245435 38386223 := bstep (se 1 (by rfl) ⟨28789667, by rfl⟩ : syracuseStep 38386223 = 57579335) B57579335
theorem B25590815 : Blo 2245435 25590815 := bstep (se 1 (by rfl) ⟨19193111, by rfl⟩ : syracuseStep 25590815 = 38386223) B38386223
theorem B17060543 : Blo 2245435 17060543 := bstep (se 1 (by rfl) ⟨12795407, by rfl⟩ : syracuseStep 17060543 = 25590815) B25590815
theorem B11373695 : Blo 2245435 11373695 := bstep (se 1 (by rfl) ⟨8530271, by rfl⟩ : syracuseStep 11373695 = 17060543) B17060543
theorem B7582463 : Blo 2245435 7582463 := bstep (se 1 (by rfl) ⟨5686847, by rfl⟩ : syracuseStep 7582463 = 11373695) B11373695
theorem B5054975 : Blo 2245435 5054975 := bstep (se 1 (by rfl) ⟨3791231, by rfl⟩ : syracuseStep 5054975 = 7582463) B7582463
theorem B3369983 : Blo 2245435 3369983 := bstep (se 1 (by rfl) ⟨2527487, by rfl⟩ : syracuseStep 3369983 = 5054975) B5054975
theorem B2246655 : Blo 2245435 2246655 := bstep (se 1 (by rfl) ⟨1684991, by rfl⟩ : syracuseStep 2246655 = 3369983) B3369983
theorem B3369989 : Blo 2245435 3369989 := bbase (se 4 (by rfl) ⟨315936, by rfl⟩ : syracuseStep 3369989 = 631873) (by norm_num)
theorem B2246659 : Blo 2245435 2246659 := bstep (se 1 (by rfl) ⟨1684994, by rfl⟩ : syracuseStep 2246659 = 3369989) B3369989
theorem B3791245 : Blo 2245435 3791245 := bbase (se 3 (by rfl) ⟨710858, by rfl⟩ : syracuseStep 3791245 = 1421717) (by norm_num)
theorem B5054993 : Blo 2245435 5054993 := bstep (se 2 (by rfl) ⟨1895622, by rfl⟩ : syracuseStep 5054993 = 3791245) B3791245
theorem B3369995 : Blo 2245435 3369995 := bstep (se 1 (by rfl) ⟨2527496, by rfl⟩ : syracuseStep 3369995 = 5054993) B5054993
theorem B2246663 : Blo 2245435 2246663 := bstep (se 1 (by rfl) ⟨1684997, by rfl⟩ : syracuseStep 2246663 = 3369995) B3369995
theorem B2527501 : Blo 2245435 2527501 := bbase (se 3 (by rfl) ⟨473906, by rfl⟩ : syracuseStep 2527501 = 947813) (by norm_num)
theorem B3370001 : Blo 2245435 3370001 := bstep (se 2 (by rfl) ⟨1263750, by rfl⟩ : syracuseStep 3370001 = 2527501) B2527501
theorem B2246667 : Blo 2245435 2246667 := bstep (se 1 (by rfl) ⟨1685000, by rfl⟩ : syracuseStep 2246667 = 3370001) B3370001
theorem B7582517 : Blo 2245435 7582517 := bbase (se 5 (by rfl) ⟨355430, by rfl⟩ : syracuseStep 7582517 = 710861) (by norm_num)
theorem B5055011 : Blo 2245435 5055011 := bstep (se 1 (by rfl) ⟨3791258, by rfl⟩ : syracuseStep 5055011 = 7582517) B7582517
theorem B3370007 : Blo 2245435 3370007 := bstep (se 1 (by rfl) ⟨2527505, by rfl⟩ : syracuseStep 3370007 = 5055011) B5055011
theorem B2246671 : Blo 2245435 2246671 := bstep (se 1 (by rfl) ⟨1685003, by rfl⟩ : syracuseStep 2246671 = 3370007) B3370007
theorem B3370013 : Blo 2245435 3370013 := bbase (se 3 (by rfl) ⟨631877, by rfl⟩ : syracuseStep 3370013 = 1263755) (by norm_num)
theorem B2246675 : Blo 2245435 2246675 := bstep (se 1 (by rfl) ⟨1685006, by rfl⟩ : syracuseStep 2246675 = 3370013) B3370013
theorem B5055029 : Blo 2245435 5055029 := bbase (se 5 (by rfl) ⟨236954, by rfl⟩ : syracuseStep 5055029 = 473909) (by norm_num)
theorem B3370019 : Blo 2245435 3370019 := bstep (se 1 (by rfl) ⟨2527514, by rfl⟩ : syracuseStep 3370019 = 5055029) B5055029
theorem B2246679 : Blo 2245435 2246679 := bstep (se 1 (by rfl) ⟨1685009, by rfl⟩ : syracuseStep 2246679 = 3370019) B3370019
theorem B9596677 : Blo 2245435 9596677 := bbase (se 4 (by rfl) ⟨899688, by rfl⟩ : syracuseStep 9596677 = 1799377) (by norm_num)
theorem B12795569 : Blo 2245435 12795569 := bstep (se 2 (by rfl) ⟨4798338, by rfl⟩ : syracuseStep 12795569 = 9596677) B9596677
theorem B8530379 : Blo 2245435 8530379 := bstep (se 1 (by rfl) ⟨6397784, by rfl⟩ : syracuseStep 8530379 = 12795569) B12795569
theorem B5686919 : Blo 2245435 5686919 := bstep (se 1 (by rfl) ⟨4265189, by rfl⟩ : syracuseStep 5686919 = 8530379) B8530379
theorem B3791279 : Blo 2245435 3791279 := bstep (se 1 (by rfl) ⟨2843459, by rfl⟩ : syracuseStep 3791279 = 5686919) B5686919
theorem B2527519 : Blo 2245435 2527519 := bstep (se 1 (by rfl) ⟨1895639, by rfl⟩ : syracuseStep 2527519 = 3791279) B3791279
theorem B3370025 : Blo 2245435 3370025 := bstep (se 2 (by rfl) ⟨1263759, by rfl⟩ : syracuseStep 3370025 = 2527519) B2527519
theorem B2246683 : Blo 2245435 2246683 := bstep (se 1 (by rfl) ⟨1685012, by rfl⟩ : syracuseStep 2246683 = 3370025) B3370025
theorem B9596693 : Blo 2245435 9596693 := bbase (se 6 (by rfl) ⟨224922, by rfl⟩ : syracuseStep 9596693 = 449845) (by norm_num)
theorem B6397795 : Blo 2245435 6397795 := bstep (se 1 (by rfl) ⟨4798346, by rfl⟩ : syracuseStep 6397795 = 9596693) B9596693
theorem B8530393 : Blo 2245435 8530393 := bstep (se 2 (by rfl) ⟨3198897, by rfl⟩ : syracuseStep 8530393 = 6397795) B6397795
theorem B11373857 : Blo 2245435 11373857 := bstep (se 2 (by rfl) ⟨4265196, by rfl⟩ : syracuseStep 11373857 = 8530393) B8530393
theorem B7582571 : Blo 2245435 7582571 := bstep (se 1 (by rfl) ⟨5686928, by rfl⟩ : syracuseStep 7582571 = 11373857) B11373857
theorem B5055047 : Blo 2245435 5055047 := bstep (se 1 (by rfl) ⟨3791285, by rfl⟩ : syracuseStep 5055047 = 7582571) B7582571
theorem B3370031 : Blo 2245435 3370031 := bstep (se 1 (by rfl) ⟨2527523, by rfl⟩ : syracuseStep 3370031 = 5055047) B5055047
theorem B2246687 : Blo 2245435 2246687 := bstep (se 1 (by rfl) ⟨1685015, by rfl⟩ : syracuseStep 2246687 = 3370031) B3370031
theorem B3370037 : Blo 2245435 3370037 := bbase (se 5 (by rfl) ⟨157970, by rfl⟩ : syracuseStep 3370037 = 315941) (by norm_num)
theorem B2246691 : Blo 2245435 2246691 := bstep (se 1 (by rfl) ⟨1685018, by rfl⟩ : syracuseStep 2246691 = 3370037) B3370037
theorem B5686949 : Blo 2245435 5686949 := bbase (se 4 (by rfl) ⟨533151, by rfl⟩ : syracuseStep 5686949 = 1066303) (by norm_num)
theorem B3791299 : Blo 2245435 3791299 := bstep (se 1 (by rfl) ⟨2843474, by rfl⟩ : syracuseStep 3791299 = 5686949) B5686949
theorem B5055065 : Blo 2245435 5055065 := bstep (se 2 (by rfl) ⟨1895649, by rfl⟩ : syracuseStep 5055065 = 3791299) B3791299
theorem B3370043 : Blo 2245435 3370043 := bstep (se 1 (by rfl) ⟨2527532, by rfl⟩ : syracuseStep 3370043 = 5055065) B5055065
theorem B2246695 : Blo 2245435 2246695 := bstep (se 1 (by rfl) ⟨1685021, by rfl⟩ : syracuseStep 2246695 = 3370043) B3370043
theorem B2527537 : Blo 2245435 2527537 := bbase (se 2 (by rfl) ⟨947826, by rfl⟩ : syracuseStep 2527537 = 1895653) (by norm_num)
theorem B3370049 : Blo 2245435 3370049 := bstep (se 2 (by rfl) ⟨1263768, by rfl⟩ : syracuseStep 3370049 = 2527537) B2527537
theorem B2246699 : Blo 2245435 2246699 := bstep (se 1 (by rfl) ⟨1685024, by rfl⟩ : syracuseStep 2246699 = 3370049) B3370049
theorem B4798381 : Blo 2245435 4798381 := bbase (se 3 (by rfl) ⟨899696, by rfl⟩ : syracuseStep 4798381 = 1799393) (by norm_num)
theorem B6397841 : Blo 2245435 6397841 := bstep (se 2 (by rfl) ⟨2399190, by rfl⟩ : syracuseStep 6397841 = 4798381) B4798381
theorem B4265227 : Blo 2245435 4265227 := bstep (se 1 (by rfl) ⟨3198920, by rfl⟩ : syracuseStep 4265227 = 6397841) B6397841
theorem B5686969 : Blo 2245435 5686969 := bstep (se 2 (by rfl) ⟨2132613, by rfl⟩ : syracuseStep 5686969 = 4265227) B4265227
theorem B7582625 : Blo 2245435 7582625 := bstep (se 2 (by rfl) ⟨2843484, by rfl⟩ : syracuseStep 7582625 = 5686969) B5686969
theorem B5055083 : Blo 2245435 5055083 := bstep (se 1 (by rfl) ⟨3791312, by rfl⟩ : syracuseStep 5055083 = 7582625) B7582625
theorem B3370055 : Blo 2245435 3370055 := bstep (se 1 (by rfl) ⟨2527541, by rfl⟩ : syracuseStep 3370055 = 5055083) B5055083
theorem B2246703 : Blo 2245435 2246703 := bstep (se 1 (by rfl) ⟨1685027, by rfl⟩ : syracuseStep 2246703 = 3370055) B3370055
theorem B3370061 : Blo 2245435 3370061 := bbase (se 3 (by rfl) ⟨631886, by rfl⟩ : syracuseStep 3370061 = 1263773) (by norm_num)
theorem B2246707 : Blo 2245435 2246707 := bstep (se 1 (by rfl) ⟨1685030, by rfl⟩ : syracuseStep 2246707 = 3370061) B3370061
theorem B5055101 : Blo 2245435 5055101 := bbase (se 3 (by rfl) ⟨947831, by rfl⟩ : syracuseStep 5055101 = 1895663) (by norm_num)
theorem B3370067 : Blo 2245435 3370067 := bstep (se 1 (by rfl) ⟨2527550, by rfl⟩ : syracuseStep 3370067 = 5055101) B5055101
theorem B2246711 : Blo 2245435 2246711 := bstep (se 1 (by rfl) ⟨1685033, by rfl⟩ : syracuseStep 2246711 = 3370067) B3370067
theorem B3791333 : Blo 2245435 3791333 := bbase (se 4 (by rfl) ⟨355437, by rfl⟩ : syracuseStep 3791333 = 710875) (by norm_num)
theorem B2527555 : Blo 2245435 2527555 := bstep (se 1 (by rfl) ⟨1895666, by rfl⟩ : syracuseStep 2527555 = 3791333) B3791333
theorem B3370073 : Blo 2245435 3370073 := bstep (se 2 (by rfl) ⟨1263777, by rfl⟩ : syracuseStep 3370073 = 2527555) B2527555
theorem B2246715 : Blo 2245435 2246715 := bstep (se 1 (by rfl) ⟨1685036, by rfl⟩ : syracuseStep 2246715 = 3370073) B3370073
theorem B9109493 : Blo 2245435 9109493 := bbase (se 5 (by rfl) ⟨427007, by rfl⟩ : syracuseStep 9109493 = 854015) (by norm_num)
theorem B6072995 : Blo 2245435 6072995 := bstep (se 1 (by rfl) ⟨4554746, by rfl⟩ : syracuseStep 6072995 = 9109493) B9109493
theorem B16194653 : Blo 2245435 16194653 := bstep (se 3 (by rfl) ⟨3036497, by rfl⟩ : syracuseStep 16194653 = 6072995) B6072995
theorem B10796435 : Blo 2245435 10796435 := bstep (se 1 (by rfl) ⟨8097326, by rfl⟩ : syracuseStep 10796435 = 16194653) B16194653
theorem B7197623 : Blo 2245435 7197623 := bstep (se 1 (by rfl) ⟨5398217, by rfl⟩ : syracuseStep 7197623 = 10796435) B10796435
theorem B4798415 : Blo 2245435 4798415 := bstep (se 1 (by rfl) ⟨3598811, by rfl⟩ : syracuseStep 4798415 = 7197623) B7197623
theorem B3198943 : Blo 2245435 3198943 := bstep (se 1 (by rfl) ⟨2399207, by rfl⟩ : syracuseStep 3198943 = 4798415) B4798415
theorem B17061029 : Blo 2245435 17061029 := bstep (se 4 (by rfl) ⟨1599471, by rfl⟩ : syracuseStep 17061029 = 3198943) B3198943
theorem B11374019 : Blo 2245435 11374019 := bstep (se 1 (by rfl) ⟨8530514, by rfl⟩ : syracuseStep 11374019 = 17061029) B17061029
theorem B7582679 : Blo 2245435 7582679 := bstep (se 1 (by rfl) ⟨5687009, by rfl⟩ : syracuseStep 7582679 = 11374019) B11374019
theorem B5055119 : Blo 2245435 5055119 := bstep (se 1 (by rfl) ⟨3791339, by rfl⟩ : syracuseStep 5055119 = 7582679) B7582679
theorem B3370079 : Blo 2245435 3370079 := bstep (se 1 (by rfl) ⟨2527559, by rfl⟩ : syracuseStep 3370079 = 5055119) B5055119
theorem B2246719 : Blo 2245435 2246719 := bstep (se 1 (by rfl) ⟨1685039, by rfl⟩ : syracuseStep 2246719 = 3370079) B3370079
theorem B3370085 : Blo 2245435 3370085 := bbase (se 4 (by rfl) ⟨315945, by rfl⟩ : syracuseStep 3370085 = 631891) (by norm_num)
theorem B2246723 : Blo 2245435 2246723 := bstep (se 1 (by rfl) ⟨1685042, by rfl⟩ : syracuseStep 2246723 = 3370085) B3370085
theorem B4323469 : Blo 2245435 4323469 := bbase (se 3 (by rfl) ⟨810650, by rfl⟩ : syracuseStep 4323469 = 1621301) (by norm_num)
theorem B5764625 : Blo 2245435 5764625 := bstep (se 2 (by rfl) ⟨2161734, by rfl⟩ : syracuseStep 5764625 = 4323469) B4323469
theorem B3843083 : Blo 2245435 3843083 := bstep (se 1 (by rfl) ⟨2882312, by rfl⟩ : syracuseStep 3843083 = 5764625) B5764625
theorem B10248221 : Blo 2245435 10248221 := bstep (se 3 (by rfl) ⟨1921541, by rfl⟩ : syracuseStep 10248221 = 3843083) B3843083
theorem B6832147 : Blo 2245435 6832147 := bstep (se 1 (by rfl) ⟨5124110, by rfl⟩ : syracuseStep 6832147 = 10248221) B10248221
theorem B9109529 : Blo 2245435 9109529 := bstep (se 2 (by rfl) ⟨3416073, by rfl⟩ : syracuseStep 9109529 = 6832147) B6832147
theorem B6073019 : Blo 2245435 6073019 := bstep (se 1 (by rfl) ⟨4554764, by rfl⟩ : syracuseStep 6073019 = 9109529) B9109529
theorem B4048679 : Blo 2245435 4048679 := bstep (se 1 (by rfl) ⟨3036509, by rfl⟩ : syracuseStep 4048679 = 6073019) B6073019
theorem B2699119 : Blo 2245435 2699119 := bstep (se 1 (by rfl) ⟨2024339, by rfl⟩ : syracuseStep 2699119 = 4048679) B4048679
theorem B3598825 : Blo 2245435 3598825 := bstep (se 2 (by rfl) ⟨1349559, by rfl⟩ : syracuseStep 3598825 = 2699119) B2699119
theorem B4798433 : Blo 2245435 4798433 := bstep (se 2 (by rfl) ⟨1799412, by rfl⟩ : syracuseStep 4798433 = 3598825) B3598825
theorem B3198955 : Blo 2245435 3198955 := bstep (se 1 (by rfl) ⟨2399216, by rfl⟩ : syracuseStep 3198955 = 4798433) B4798433
theorem B4265273 : Blo 2245435 4265273 := bstep (se 2 (by rfl) ⟨1599477, by rfl⟩ : syracuseStep 4265273 = 3198955) B3198955
theorem B2843515 : Blo 2245435 2843515 := bstep (se 1 (by rfl) ⟨2132636, by rfl⟩ : syracuseStep 2843515 = 4265273) B4265273
theorem B3791353 : Blo 2245435 3791353 := bstep (se 2 (by rfl) ⟨1421757, by rfl⟩ : syracuseStep 3791353 = 2843515) B2843515
theorem B5055137 : Blo 2245435 5055137 := bstep (se 2 (by rfl) ⟨1895676, by rfl⟩ : syracuseStep 5055137 = 3791353) B3791353
theorem B3370091 : Blo 2245435 3370091 := bstep (se 1 (by rfl) ⟨2527568, by rfl⟩ : syracuseStep 3370091 = 5055137) B5055137
theorem B2246727 : Blo 2245435 2246727 := bstep (se 1 (by rfl) ⟨1685045, by rfl⟩ : syracuseStep 2246727 = 3370091) B3370091
theorem B2527573 : Blo 2245435 2527573 := bbase (se 10 (by rfl) ⟨3702, by rfl⟩ : syracuseStep 2527573 = 7405) (by norm_num)
theorem B3370097 : Blo 2245435 3370097 := bstep (se 2 (by rfl) ⟨1263786, by rfl⟩ : syracuseStep 3370097 = 2527573) B2527573
theorem B2246731 : Blo 2245435 2246731 := bstep (se 1 (by rfl) ⟨1685048, by rfl⟩ : syracuseStep 2246731 = 3370097) B3370097
theorem B2843525 : Blo 2245435 2843525 := bbase (se 4 (by rfl) ⟨266580, by rfl⟩ : syracuseStep 2843525 = 533161) (by norm_num)
theorem B7582733 : Blo 2245435 7582733 := bstep (se 3 (by rfl) ⟨1421762, by rfl⟩ : syracuseStep 7582733 = 2843525) B2843525
theorem B5055155 : Blo 2245435 5055155 := bstep (se 1 (by rfl) ⟨3791366, by rfl⟩ : syracuseStep 5055155 = 7582733) B7582733
theorem B3370103 : Blo 2245435 3370103 := bstep (se 1 (by rfl) ⟨2527577, by rfl⟩ : syracuseStep 3370103 = 5055155) B5055155
theorem B2246735 : Blo 2245435 2246735 := bstep (se 1 (by rfl) ⟨1685051, by rfl⟩ : syracuseStep 2246735 = 3370103) B3370103
theorem B3370109 : Blo 2245435 3370109 := bbase (se 3 (by rfl) ⟨631895, by rfl⟩ : syracuseStep 3370109 = 1263791) (by norm_num)
theorem B2246739 : Blo 2245435 2246739 := bstep (se 1 (by rfl) ⟨1685054, by rfl⟩ : syracuseStep 2246739 = 3370109) B3370109
theorem B5055173 : Blo 2245435 5055173 := bbase (se 4 (by rfl) ⟨473922, by rfl⟩ : syracuseStep 5055173 = 947845) (by norm_num)
theorem B3370115 : Blo 2245435 3370115 := bstep (se 1 (by rfl) ⟨2527586, by rfl⟩ : syracuseStep 3370115 = 5055173) B5055173
theorem B2246743 : Blo 2245435 2246743 := bstep (se 1 (by rfl) ⟨1685057, by rfl⟩ : syracuseStep 2246743 = 3370115) B3370115
theorem B21593141 : Blo 2245435 21593141 := bbase (se 5 (by rfl) ⟨1012178, by rfl⟩ : syracuseStep 21593141 = 2024357) (by norm_num)
theorem B14395427 : Blo 2245435 14395427 := bstep (se 1 (by rfl) ⟨10796570, by rfl⟩ : syracuseStep 14395427 = 21593141) B21593141
theorem B9596951 : Blo 2245435 9596951 := bstep (se 1 (by rfl) ⟨7197713, by rfl⟩ : syracuseStep 9596951 = 14395427) B14395427
theorem B6397967 : Blo 2245435 6397967 := bstep (se 1 (by rfl) ⟨4798475, by rfl⟩ : syracuseStep 6397967 = 9596951) B9596951
theorem B4265311 : Blo 2245435 4265311 := bstep (se 1 (by rfl) ⟨3198983, by rfl⟩ : syracuseStep 4265311 = 6397967) B6397967
theorem B5687081 : Blo 2245435 5687081 := bstep (se 2 (by rfl) ⟨2132655, by rfl⟩ : syracuseStep 5687081 = 4265311) B4265311
theorem B3791387 : Blo 2245435 3791387 := bstep (se 1 (by rfl) ⟨2843540, by rfl⟩ : syracuseStep 3791387 = 5687081) B5687081
theorem B2527591 : Blo 2245435 2527591 := bstep (se 1 (by rfl) ⟨1895693, by rfl⟩ : syracuseStep 2527591 = 3791387) B3791387
theorem B3370121 : Blo 2245435 3370121 := bstep (se 2 (by rfl) ⟨1263795, by rfl⟩ : syracuseStep 3370121 = 2527591) B2527591
theorem B2246747 : Blo 2245435 2246747 := bstep (se 1 (by rfl) ⟨1685060, by rfl⟩ : syracuseStep 2246747 = 3370121) B3370121
theorem B11374181 : Blo 2245435 11374181 := bbase (se 4 (by rfl) ⟨1066329, by rfl⟩ : syracuseStep 11374181 = 2132659) (by norm_num)
theorem B7582787 : Blo 2245435 7582787 := bstep (se 1 (by rfl) ⟨5687090, by rfl⟩ : syracuseStep 7582787 = 11374181) B11374181
theorem B5055191 : Blo 2245435 5055191 := bstep (se 1 (by rfl) ⟨3791393, by rfl⟩ : syracuseStep 5055191 = 7582787) B7582787
theorem B3370127 : Blo 2245435 3370127 := bstep (se 1 (by rfl) ⟨2527595, by rfl⟩ : syracuseStep 3370127 = 5055191) B5055191
theorem B2246751 : Blo 2245435 2246751 := bstep (se 1 (by rfl) ⟨1685063, by rfl⟩ : syracuseStep 2246751 = 3370127) B3370127
theorem B3370133 : Blo 2245435 3370133 := bbase (se 6 (by rfl) ⟨78987, by rfl⟩ : syracuseStep 3370133 = 157975) (by norm_num)
theorem B2246755 : Blo 2245435 2246755 := bstep (se 1 (by rfl) ⟨1685066, by rfl⟩ : syracuseStep 2246755 = 3370133) B3370133
theorem B20496725 : Blo 2245435 20496725 := bbase (se 10 (by rfl) ⟨30024, by rfl⟩ : syracuseStep 20496725 = 60049) (by norm_num)
theorem B13664483 : Blo 2245435 13664483 := bstep (se 1 (by rfl) ⟨10248362, by rfl⟩ : syracuseStep 13664483 = 20496725) B20496725
theorem B9109655 : Blo 2245435 9109655 := bstep (se 1 (by rfl) ⟨6832241, by rfl⟩ : syracuseStep 9109655 = 13664483) B13664483
theorem B6073103 : Blo 2245435 6073103 := bstep (se 1 (by rfl) ⟨4554827, by rfl⟩ : syracuseStep 6073103 = 9109655) B9109655
theorem B16194941 : Blo 2245435 16194941 := bstep (se 3 (by rfl) ⟨3036551, by rfl⟩ : syracuseStep 16194941 = 6073103) B6073103
theorem B10796627 : Blo 2245435 10796627 := bstep (se 1 (by rfl) ⟨8097470, by rfl⟩ : syracuseStep 10796627 = 16194941) B16194941
theorem B7197751 : Blo 2245435 7197751 := bstep (se 1 (by rfl) ⟨5398313, by rfl⟩ : syracuseStep 7197751 = 10796627) B10796627
theorem B9597001 : Blo 2245435 9597001 := bstep (se 2 (by rfl) ⟨3598875, by rfl⟩ : syracuseStep 9597001 = 7197751) B7197751
theorem B12796001 : Blo 2245435 12796001 := bstep (se 2 (by rfl) ⟨4798500, by rfl⟩ : syracuseStep 12796001 = 9597001) B9597001
theorem B8530667 : Blo 2245435 8530667 := bstep (se 1 (by rfl) ⟨6398000, by rfl⟩ : syracuseStep 8530667 = 12796001) B12796001
theorem B5687111 : Blo 2245435 5687111 := bstep (se 1 (by rfl) ⟨4265333, by rfl⟩ : syracuseStep 5687111 = 8530667) B8530667
theorem B3791407 : Blo 2245435 3791407 := bstep (se 1 (by rfl) ⟨2843555, by rfl⟩ : syracuseStep 3791407 = 5687111) B5687111
theorem B5055209 : Blo 2245435 5055209 := bstep (se 2 (by rfl) ⟨1895703, by rfl⟩ : syracuseStep 5055209 = 3791407) B3791407
theorem B3370139 : Blo 2245435 3370139 := bstep (se 1 (by rfl) ⟨2527604, by rfl⟩ : syracuseStep 3370139 = 5055209) B5055209
theorem B2246759 : Blo 2245435 2246759 := bstep (se 1 (by rfl) ⟨1685069, by rfl⟩ : syracuseStep 2246759 = 3370139) B3370139
theorem B2527609 : Blo 2245435 2527609 := bbase (se 2 (by rfl) ⟨947853, by rfl⟩ : syracuseStep 2527609 = 1895707) (by norm_num)
theorem B3370145 : Blo 2245435 3370145 := bstep (se 2 (by rfl) ⟨1263804, by rfl⟩ : syracuseStep 3370145 = 2527609) B2527609
theorem B2246763 : Blo 2245435 2246763 := bstep (se 1 (by rfl) ⟨1685072, by rfl⟩ : syracuseStep 2246763 = 3370145) B3370145
theorem B4103989 : Blo 2245435 4103989 := bbase (se 5 (by rfl) ⟨192374, by rfl⟩ : syracuseStep 4103989 = 384749) (by norm_num)
theorem B21887941 : Blo 2245435 21887941 := bstep (se 4 (by rfl) ⟨2051994, by rfl⟩ : syracuseStep 21887941 = 4103989) B4103989
theorem B29183921 : Blo 2245435 29183921 := bstep (se 2 (by rfl) ⟨10943970, by rfl⟩ : syracuseStep 29183921 = 21887941) B21887941
theorem B19455947 : Blo 2245435 19455947 := bstep (se 1 (by rfl) ⟨14591960, by rfl⟩ : syracuseStep 19455947 = 29183921) B29183921
theorem B12970631 : Blo 2245435 12970631 := bstep (se 1 (by rfl) ⟨9727973, by rfl⟩ : syracuseStep 12970631 = 19455947) B19455947
theorem B8647087 : Blo 2245435 8647087 := bstep (se 1 (by rfl) ⟨6485315, by rfl⟩ : syracuseStep 8647087 = 12970631) B12970631
theorem B11529449 : Blo 2245435 11529449 := bstep (se 2 (by rfl) ⟨4323543, by rfl⟩ : syracuseStep 11529449 = 8647087) B8647087
theorem B7686299 : Blo 2245435 7686299 := bstep (se 1 (by rfl) ⟨5764724, by rfl⟩ : syracuseStep 7686299 = 11529449) B11529449
theorem B20496797 : Blo 2245435 20496797 := bstep (se 3 (by rfl) ⟨3843149, by rfl⟩ : syracuseStep 20496797 = 7686299) B7686299
theorem B13664531 : Blo 2245435 13664531 := bstep (se 1 (by rfl) ⟨10248398, by rfl⟩ : syracuseStep 13664531 = 20496797) B20496797
theorem B9109687 : Blo 2245435 9109687 := bstep (se 1 (by rfl) ⟨6832265, by rfl⟩ : syracuseStep 9109687 = 13664531) B13664531
theorem B12146249 : Blo 2245435 12146249 := bstep (se 2 (by rfl) ⟨4554843, by rfl⟩ : syracuseStep 12146249 = 9109687) B9109687
theorem B8097499 : Blo 2245435 8097499 := bstep (se 1 (by rfl) ⟨6073124, by rfl⟩ : syracuseStep 8097499 = 12146249) B12146249
theorem B10796665 : Blo 2245435 10796665 := bstep (se 2 (by rfl) ⟨4048749, by rfl⟩ : syracuseStep 10796665 = 8097499) B8097499
theorem B14395553 : Blo 2245435 14395553 := bstep (se 2 (by rfl) ⟨5398332, by rfl⟩ : syracuseStep 14395553 = 10796665) B10796665
theorem B9597035 : Blo 2245435 9597035 := bstep (se 1 (by rfl) ⟨7197776, by rfl⟩ : syracuseStep 9597035 = 14395553) B14395553
theorem B6398023 : Blo 2245435 6398023 := bstep (se 1 (by rfl) ⟨4798517, by rfl⟩ : syracuseStep 6398023 = 9597035) B9597035
theorem B8530697 : Blo 2245435 8530697 := bstep (se 2 (by rfl) ⟨3199011, by rfl⟩ : syracuseStep 8530697 = 6398023) B6398023
theorem B5687131 : Blo 2245435 5687131 := bstep (se 1 (by rfl) ⟨4265348, by rfl⟩ : syracuseStep 5687131 = 8530697) B8530697
theorem B7582841 : Blo 2245435 7582841 := bstep (se 2 (by rfl) ⟨2843565, by rfl⟩ : syracuseStep 7582841 = 5687131) B5687131
theorem B5055227 : Blo 2245435 5055227 := bstep (se 1 (by rfl) ⟨3791420, by rfl⟩ : syracuseStep 5055227 = 7582841) B7582841
theorem B3370151 : Blo 2245435 3370151 := bstep (se 1 (by rfl) ⟨2527613, by rfl⟩ : syracuseStep 3370151 = 5055227) B5055227
theorem B2246767 : Blo 2245435 2246767 := bstep (se 1 (by rfl) ⟨1685075, by rfl⟩ : syracuseStep 2246767 = 3370151) B3370151
theorem B3370157 : Blo 2245435 3370157 := bbase (se 3 (by rfl) ⟨631904, by rfl⟩ : syracuseStep 3370157 = 1263809) (by norm_num)
theorem B2246771 : Blo 2245435 2246771 := bstep (se 1 (by rfl) ⟨1685078, by rfl⟩ : syracuseStep 2246771 = 3370157) B3370157
theorem B5055245 : Blo 2245435 5055245 := bbase (se 3 (by rfl) ⟨947858, by rfl⟩ : syracuseStep 5055245 = 1895717) (by norm_num)
theorem B3370163 : Blo 2245435 3370163 := bstep (se 1 (by rfl) ⟨2527622, by rfl⟩ : syracuseStep 3370163 = 5055245) B5055245
theorem B2246775 : Blo 2245435 2246775 := bstep (se 1 (by rfl) ⟨1685081, by rfl⟩ : syracuseStep 2246775 = 3370163) B3370163
theorem B2843581 : Blo 2245435 2843581 := bbase (se 3 (by rfl) ⟨533171, by rfl⟩ : syracuseStep 2843581 = 1066343) (by norm_num)
theorem B3791441 : Blo 2245435 3791441 := bstep (se 2 (by rfl) ⟨1421790, by rfl⟩ : syracuseStep 3791441 = 2843581) B2843581
theorem B2527627 : Blo 2245435 2527627 := bstep (se 1 (by rfl) ⟨1895720, by rfl⟩ : syracuseStep 2527627 = 3791441) B3791441
theorem B3370169 : Blo 2245435 3370169 := bstep (se 2 (by rfl) ⟨1263813, by rfl⟩ : syracuseStep 3370169 = 2527627) B2527627
theorem B2246779 : Blo 2245435 2246779 := bstep (se 1 (by rfl) ⟨1685084, by rfl⟩ : syracuseStep 2246779 = 3370169) B3370169
theorem B10796741 : Blo 2245435 10796741 := bbase (se 4 (by rfl) ⟨1012194, by rfl⟩ : syracuseStep 10796741 = 2024389) (by norm_num)
theorem B7197827 : Blo 2245435 7197827 := bstep (se 1 (by rfl) ⟨5398370, by rfl⟩ : syracuseStep 7197827 = 10796741) B10796741
theorem B19194205 : Blo 2245435 19194205 := bstep (se 3 (by rfl) ⟨3598913, by rfl⟩ : syracuseStep 19194205 = 7197827) B7197827
theorem B25592273 : Blo 2245435 25592273 := bstep (se 2 (by rfl) ⟨9597102, by rfl⟩ : syracuseStep 25592273 = 19194205) B19194205
theorem B17061515 : Blo 2245435 17061515 := bstep (se 1 (by rfl) ⟨12796136, by rfl⟩ : syracuseStep 17061515 = 25592273) B25592273
theorem B11374343 : Blo 2245435 11374343 := bstep (se 1 (by rfl) ⟨8530757, by rfl⟩ : syracuseStep 11374343 = 17061515) B17061515
theorem B7582895 : Blo 2245435 7582895 := bstep (se 1 (by rfl) ⟨5687171, by rfl⟩ : syracuseStep 7582895 = 11374343) B11374343
theorem B5055263 : Blo 2245435 5055263 := bstep (se 1 (by rfl) ⟨3791447, by rfl⟩ : syracuseStep 5055263 = 7582895) B7582895
theorem B3370175 : Blo 2245435 3370175 := bstep (se 1 (by rfl) ⟨2527631, by rfl⟩ : syracuseStep 3370175 = 5055263) B5055263
theorem B2246783 : Blo 2245435 2246783 := bstep (se 1 (by rfl) ⟨1685087, by rfl⟩ : syracuseStep 2246783 = 3370175) B3370175
theorem B3370181 : Blo 2245435 3370181 := bbase (se 4 (by rfl) ⟨315954, by rfl⟩ : syracuseStep 3370181 = 631909) (by norm_num)
theorem B2246787 : Blo 2245435 2246787 := bstep (se 1 (by rfl) ⟨1685090, by rfl⟩ : syracuseStep 2246787 = 3370181) B3370181
theorem B3791461 : Blo 2245435 3791461 := bbase (se 4 (by rfl) ⟨355449, by rfl⟩ : syracuseStep 3791461 = 710899) (by norm_num)
theorem B5055281 : Blo 2245435 5055281 := bstep (se 2 (by rfl) ⟨1895730, by rfl⟩ : syracuseStep 5055281 = 3791461) B3791461
theorem B3370187 : Blo 2245435 3370187 := bstep (se 1 (by rfl) ⟨2527640, by rfl⟩ : syracuseStep 3370187 = 5055281) B5055281
theorem B2246791 : Blo 2245435 2246791 := bstep (se 1 (by rfl) ⟨1685093, by rfl⟩ : syracuseStep 2246791 = 3370187) B3370187
theorem B2527645 : Blo 2245435 2527645 := bbase (se 3 (by rfl) ⟨473933, by rfl⟩ : syracuseStep 2527645 = 947867) (by norm_num)
theorem B3370193 : Blo 2245435 3370193 := bstep (se 2 (by rfl) ⟨1263822, by rfl⟩ : syracuseStep 3370193 = 2527645) B2527645
theorem B2246795 : Blo 2245435 2246795 := bstep (se 1 (by rfl) ⟨1685096, by rfl⟩ : syracuseStep 2246795 = 3370193) B3370193
theorem B7582949 : Blo 2245435 7582949 := bbase (se 4 (by rfl) ⟨710901, by rfl⟩ : syracuseStep 7582949 = 1421803) (by norm_num)
theorem B5055299 : Blo 2245435 5055299 := bstep (se 1 (by rfl) ⟨3791474, by rfl⟩ : syracuseStep 5055299 = 7582949) B7582949
theorem B3370199 : Blo 2245435 3370199 := bstep (se 1 (by rfl) ⟨2527649, by rfl⟩ : syracuseStep 3370199 = 5055299) B5055299
theorem B2246799 : Blo 2245435 2246799 := bstep (se 1 (by rfl) ⟨1685099, by rfl⟩ : syracuseStep 2246799 = 3370199) B3370199
theorem B3370205 : Blo 2245435 3370205 := bbase (se 3 (by rfl) ⟨631913, by rfl⟩ : syracuseStep 3370205 = 1263827) (by norm_num)
theorem B2246803 : Blo 2245435 2246803 := bstep (se 1 (by rfl) ⟨1685102, by rfl⟩ : syracuseStep 2246803 = 3370205) B3370205
theorem B5055317 : Blo 2245435 5055317 := bbase (se 9 (by rfl) ⟨14810, by rfl⟩ : syracuseStep 5055317 = 29621) (by norm_num)
theorem B3370211 : Blo 2245435 3370211 := bstep (se 1 (by rfl) ⟨2527658, by rfl⟩ : syracuseStep 3370211 = 5055317) B5055317
theorem B2246807 : Blo 2245435 2246807 := bstep (se 1 (by rfl) ⟨1685105, by rfl⟩ : syracuseStep 2246807 = 3370211) B3370211
theorem B6398149 : Blo 2245435 6398149 := bbase (se 4 (by rfl) ⟨599826, by rfl⟩ : syracuseStep 6398149 = 1199653) (by norm_num)
theorem B8530865 : Blo 2245435 8530865 := bstep (se 2 (by rfl) ⟨3199074, by rfl⟩ : syracuseStep 8530865 = 6398149) B6398149
theorem B5687243 : Blo 2245435 5687243 := bstep (se 1 (by rfl) ⟨4265432, by rfl⟩ : syracuseStep 5687243 = 8530865) B8530865
theorem B3791495 : Blo 2245435 3791495 := bstep (se 1 (by rfl) ⟨2843621, by rfl⟩ : syracuseStep 3791495 = 5687243) B5687243
theorem B2527663 : Blo 2245435 2527663 := bstep (se 1 (by rfl) ⟨1895747, by rfl⟩ : syracuseStep 2527663 = 3791495) B3791495
theorem B3370217 : Blo 2245435 3370217 := bstep (se 2 (by rfl) ⟨1263831, by rfl⟩ : syracuseStep 3370217 = 2527663) B2527663
theorem B2246811 : Blo 2245435 2246811 := bstep (se 1 (by rfl) ⟨1685108, by rfl⟩ : syracuseStep 2246811 = 3370217) B3370217
theorem B5472101 : Blo 2245435 5472101 := bbase (se 4 (by rfl) ⟨513009, by rfl⟩ : syracuseStep 5472101 = 1026019) (by norm_num)
theorem B3648067 : Blo 2245435 3648067 := bstep (se 1 (by rfl) ⟨2736050, by rfl⟩ : syracuseStep 3648067 = 5472101) B5472101
theorem B19456357 : Blo 2245435 19456357 := bstep (se 4 (by rfl) ⟨1824033, by rfl⟩ : syracuseStep 19456357 = 3648067) B3648067
theorem B25941809 : Blo 2245435 25941809 := bstep (se 2 (by rfl) ⟨9728178, by rfl⟩ : syracuseStep 25941809 = 19456357) B19456357
theorem B17294539 : Blo 2245435 17294539 := bstep (se 1 (by rfl) ⟨12970904, by rfl⟩ : syracuseStep 17294539 = 25941809) B25941809
theorem B23059385 : Blo 2245435 23059385 := bstep (se 2 (by rfl) ⟨8647269, by rfl⟩ : syracuseStep 23059385 = 17294539) B17294539
theorem B15372923 : Blo 2245435 15372923 := bstep (se 1 (by rfl) ⟨11529692, by rfl⟩ : syracuseStep 15372923 = 23059385) B23059385
theorem B40994461 : Blo 2245435 40994461 := bstep (se 3 (by rfl) ⟨7686461, by rfl⟩ : syracuseStep 40994461 = 15372923) B15372923
theorem B54659281 : Blo 2245435 54659281 := bstep (se 2 (by rfl) ⟨20497230, by rfl⟩ : syracuseStep 54659281 = 40994461) B40994461
theorem B72879041 : Blo 2245435 72879041 := bstep (se 2 (by rfl) ⟨27329640, by rfl⟩ : syracuseStep 72879041 = 54659281) B54659281
theorem B48586027 : Blo 2245435 48586027 := bstep (se 1 (by rfl) ⟨36439520, by rfl⟩ : syracuseStep 48586027 = 72879041) B72879041
theorem B64781369 : Blo 2245435 64781369 := bstep (se 2 (by rfl) ⟨24293013, by rfl⟩ : syracuseStep 64781369 = 48586027) B48586027
theorem B43187579 : Blo 2245435 43187579 := bstep (se 1 (by rfl) ⟨32390684, by rfl⟩ : syracuseStep 43187579 = 64781369) B64781369
theorem B28791719 : Blo 2245435 28791719 := bstep (se 1 (by rfl) ⟨21593789, by rfl⟩ : syracuseStep 28791719 = 43187579) B43187579
theorem B19194479 : Blo 2245435 19194479 := bstep (se 1 (by rfl) ⟨14395859, by rfl⟩ : syracuseStep 19194479 = 28791719) B28791719
theorem B12796319 : Blo 2245435 12796319 := bstep (se 1 (by rfl) ⟨9597239, by rfl⟩ : syracuseStep 12796319 = 19194479) B19194479
theorem B8530879 : Blo 2245435 8530879 := bstep (se 1 (by rfl) ⟨6398159, by rfl⟩ : syracuseStep 8530879 = 12796319) B12796319
theorem B11374505 : Blo 2245435 11374505 := bstep (se 2 (by rfl) ⟨4265439, by rfl⟩ : syracuseStep 11374505 = 8530879) B8530879
theorem B7583003 : Blo 2245435 7583003 := bstep (se 1 (by rfl) ⟨5687252, by rfl⟩ : syracuseStep 7583003 = 11374505) B11374505
theorem B5055335 : Blo 2245435 5055335 := bstep (se 1 (by rfl) ⟨3791501, by rfl⟩ : syracuseStep 5055335 = 7583003) B7583003
theorem B3370223 : Blo 2245435 3370223 := bstep (se 1 (by rfl) ⟨2527667, by rfl⟩ : syracuseStep 3370223 = 5055335) B5055335
theorem B2246815 : Blo 2245435 2246815 := bstep (se 1 (by rfl) ⟨1685111, by rfl⟩ : syracuseStep 2246815 = 3370223) B3370223
theorem B3370229 : Blo 2245435 3370229 := bbase (se 5 (by rfl) ⟨157979, by rfl⟩ : syracuseStep 3370229 = 315959) (by norm_num)
theorem B2246819 : Blo 2245435 2246819 := bstep (se 1 (by rfl) ⟨1685114, by rfl⟩ : syracuseStep 2246819 = 3370229) B3370229
theorem B18219829 : Blo 2245435 18219829 := bbase (se 5 (by rfl) ⟨854054, by rfl⟩ : syracuseStep 18219829 = 1708109) (by norm_num)
theorem B24293105 : Blo 2245435 24293105 := bstep (se 2 (by rfl) ⟨9109914, by rfl⟩ : syracuseStep 24293105 = 18219829) B18219829
theorem B16195403 : Blo 2245435 16195403 := bstep (se 1 (by rfl) ⟨12146552, by rfl⟩ : syracuseStep 16195403 = 24293105) B24293105
theorem B10796935 : Blo 2245435 10796935 := bstep (se 1 (by rfl) ⟨8097701, by rfl⟩ : syracuseStep 10796935 = 16195403) B16195403
theorem B14395913 : Blo 2245435 14395913 := bstep (se 2 (by rfl) ⟨5398467, by rfl⟩ : syracuseStep 14395913 = 10796935) B10796935
theorem B9597275 : Blo 2245435 9597275 := bstep (se 1 (by rfl) ⟨7197956, by rfl⟩ : syracuseStep 9597275 = 14395913) B14395913
theorem B6398183 : Blo 2245435 6398183 := bstep (se 1 (by rfl) ⟨4798637, by rfl⟩ : syracuseStep 6398183 = 9597275) B9597275
theorem B4265455 : Blo 2245435 4265455 := bstep (se 1 (by rfl) ⟨3199091, by rfl⟩ : syracuseStep 4265455 = 6398183) B6398183
theorem B5687273 : Blo 2245435 5687273 := bstep (se 2 (by rfl) ⟨2132727, by rfl⟩ : syracuseStep 5687273 = 4265455) B4265455
theorem B3791515 : Blo 2245435 3791515 := bstep (se 1 (by rfl) ⟨2843636, by rfl⟩ : syracuseStep 3791515 = 5687273) B5687273
theorem B5055353 : Blo 2245435 5055353 := bstep (se 2 (by rfl) ⟨1895757, by rfl⟩ : syracuseStep 5055353 = 3791515) B3791515
theorem B3370235 : Blo 2245435 3370235 := bstep (se 1 (by rfl) ⟨2527676, by rfl⟩ : syracuseStep 3370235 = 5055353) B5055353
theorem B2246823 : Blo 2245435 2246823 := bstep (se 1 (by rfl) ⟨1685117, by rfl⟩ : syracuseStep 2246823 = 3370235) B3370235
theorem B2527681 : Blo 2245435 2527681 := bbase (se 2 (by rfl) ⟨947880, by rfl⟩ : syracuseStep 2527681 = 1895761) (by norm_num)
theorem B3370241 : Blo 2245435 3370241 := bstep (se 2 (by rfl) ⟨1263840, by rfl⟩ : syracuseStep 3370241 = 2527681) B2527681
theorem B2246827 : Blo 2245435 2246827 := bstep (se 1 (by rfl) ⟨1685120, by rfl⟩ : syracuseStep 2246827 = 3370241) B3370241
theorem B5687293 : Blo 2245435 5687293 := bbase (se 3 (by rfl) ⟨1066367, by rfl⟩ : syracuseStep 5687293 = 2132735) (by norm_num)
theorem B7583057 : Blo 2245435 7583057 := bstep (se 2 (by rfl) ⟨2843646, by rfl⟩ : syracuseStep 7583057 = 5687293) B5687293
theorem B5055371 : Blo 2245435 5055371 := bstep (se 1 (by rfl) ⟨3791528, by rfl⟩ : syracuseStep 5055371 = 7583057) B7583057
theorem B3370247 : Blo 2245435 3370247 := bstep (se 1 (by rfl) ⟨2527685, by rfl⟩ : syracuseStep 3370247 = 5055371) B5055371
theorem B2246831 : Blo 2245435 2246831 := bstep (se 1 (by rfl) ⟨1685123, by rfl⟩ : syracuseStep 2246831 = 3370247) B3370247
theorem B3370253 : Blo 2245435 3370253 := bbase (se 3 (by rfl) ⟨631922, by rfl⟩ : syracuseStep 3370253 = 1263845) (by norm_num)
theorem B2246835 : Blo 2245435 2246835 := bstep (se 1 (by rfl) ⟨1685126, by rfl⟩ : syracuseStep 2246835 = 3370253) B3370253
theorem B5055389 : Blo 2245435 5055389 := bbase (se 3 (by rfl) ⟨947885, by rfl⟩ : syracuseStep 5055389 = 1895771) (by norm_num)
theorem B3370259 : Blo 2245435 3370259 := bstep (se 1 (by rfl) ⟨2527694, by rfl⟩ : syracuseStep 3370259 = 5055389) B5055389
theorem B2246839 : Blo 2245435 2246839 := bstep (se 1 (by rfl) ⟨1685129, by rfl⟩ : syracuseStep 2246839 = 3370259) B3370259
theorem B3791549 : Blo 2245435 3791549 := bbase (se 3 (by rfl) ⟨710915, by rfl⟩ : syracuseStep 3791549 = 1421831) (by norm_num)
theorem B2527699 : Blo 2245435 2527699 := bstep (se 1 (by rfl) ⟨1895774, by rfl⟩ : syracuseStep 2527699 = 3791549) B3791549
theorem B3370265 : Blo 2245435 3370265 := bstep (se 2 (by rfl) ⟨1263849, by rfl⟩ : syracuseStep 3370265 = 2527699) B2527699
theorem B2246843 : Blo 2245435 2246843 := bstep (se 1 (by rfl) ⟨1685132, by rfl⟩ : syracuseStep 2246843 = 3370265) B3370265
theorem B12796501 : Blo 2245435 12796501 := bbase (se 8 (by rfl) ⟨74979, by rfl⟩ : syracuseStep 12796501 = 149959) (by norm_num)
theorem B17062001 : Blo 2245435 17062001 := bstep (se 2 (by rfl) ⟨6398250, by rfl⟩ : syracuseStep 17062001 = 12796501) B12796501
theorem B11374667 : Blo 2245435 11374667 := bstep (se 1 (by rfl) ⟨8531000, by rfl⟩ : syracuseStep 11374667 = 17062001) B17062001
theorem B7583111 : Blo 2245435 7583111 := bstep (se 1 (by rfl) ⟨5687333, by rfl⟩ : syracuseStep 7583111 = 11374667) B11374667
theorem B5055407 : Blo 2245435 5055407 := bstep (se 1 (by rfl) ⟨3791555, by rfl⟩ : syracuseStep 5055407 = 7583111) B7583111
theorem B3370271 : Blo 2245435 3370271 := bstep (se 1 (by rfl) ⟨2527703, by rfl⟩ : syracuseStep 3370271 = 5055407) B5055407
theorem B2246847 : Blo 2245435 2246847 := bstep (se 1 (by rfl) ⟨1685135, by rfl⟩ : syracuseStep 2246847 = 3370271) B3370271
theorem B3370277 : Blo 2245435 3370277 := bbase (se 4 (by rfl) ⟨315963, by rfl⟩ : syracuseStep 3370277 = 631927) (by norm_num)
theorem B2246851 : Blo 2245435 2246851 := bstep (se 1 (by rfl) ⟨1685138, by rfl⟩ : syracuseStep 2246851 = 3370277) B3370277
theorem B2843677 : Blo 2245435 2843677 := bbase (se 3 (by rfl) ⟨533189, by rfl⟩ : syracuseStep 2843677 = 1066379) (by norm_num)
theorem B3791569 : Blo 2245435 3791569 := bstep (se 2 (by rfl) ⟨1421838, by rfl⟩ : syracuseStep 3791569 = 2843677) B2843677
theorem B5055425 : Blo 2245435 5055425 := bstep (se 2 (by rfl) ⟨1895784, by rfl⟩ : syracuseStep 5055425 = 3791569) B3791569
theorem B3370283 : Blo 2245435 3370283 := bstep (se 1 (by rfl) ⟨2527712, by rfl⟩ : syracuseStep 3370283 = 5055425) B5055425
theorem B2246855 : Blo 2245435 2246855 := bstep (se 1 (by rfl) ⟨1685141, by rfl⟩ : syracuseStep 2246855 = 3370283) B3370283
theorem B2527717 : Blo 2245435 2527717 := bbase (se 4 (by rfl) ⟨236973, by rfl⟩ : syracuseStep 2527717 = 473947) (by norm_num)
theorem B3370289 : Blo 2245435 3370289 := bstep (se 2 (by rfl) ⟨1263858, by rfl⟩ : syracuseStep 3370289 = 2527717) B2527717
theorem B2246859 : Blo 2245435 2246859 := bstep (se 1 (by rfl) ⟨1685144, by rfl⟩ : syracuseStep 2246859 = 3370289) B3370289
theorem B7198085 : Blo 2245435 7198085 := bbase (se 4 (by rfl) ⟨674820, by rfl⟩ : syracuseStep 7198085 = 1349641) (by norm_num)
theorem B4798723 : Blo 2245435 4798723 := bstep (se 1 (by rfl) ⟨3599042, by rfl⟩ : syracuseStep 4798723 = 7198085) B7198085
theorem B6398297 : Blo 2245435 6398297 := bstep (se 2 (by rfl) ⟨2399361, by rfl⟩ : syracuseStep 6398297 = 4798723) B4798723
theorem B4265531 : Blo 2245435 4265531 := bstep (se 1 (by rfl) ⟨3199148, by rfl⟩ : syracuseStep 4265531 = 6398297) B6398297
theorem B2843687 : Blo 2245435 2843687 := bstep (se 1 (by rfl) ⟨2132765, by rfl⟩ : syracuseStep 2843687 = 4265531) B4265531
theorem B7583165 : Blo 2245435 7583165 := bstep (se 3 (by rfl) ⟨1421843, by rfl⟩ : syracuseStep 7583165 = 2843687) B2843687
theorem B5055443 : Blo 2245435 5055443 := bstep (se 1 (by rfl) ⟨3791582, by rfl⟩ : syracuseStep 5055443 = 7583165) B7583165
theorem B3370295 : Blo 2245435 3370295 := bstep (se 1 (by rfl) ⟨2527721, by rfl⟩ : syracuseStep 3370295 = 5055443) B5055443
theorem B2246863 : Blo 2245435 2246863 := bstep (se 1 (by rfl) ⟨1685147, by rfl⟩ : syracuseStep 2246863 = 3370295) B3370295
theorem B3370301 : Blo 2245435 3370301 := bbase (se 3 (by rfl) ⟨631931, by rfl⟩ : syracuseStep 3370301 = 1263863) (by norm_num)
theorem B2246867 : Blo 2245435 2246867 := bstep (se 1 (by rfl) ⟨1685150, by rfl⟩ : syracuseStep 2246867 = 3370301) B3370301
theorem B5055461 : Blo 2245435 5055461 := bbase (se 4 (by rfl) ⟨473949, by rfl⟩ : syracuseStep 5055461 = 947899) (by norm_num)
theorem B3370307 : Blo 2245435 3370307 := bstep (se 1 (by rfl) ⟨2527730, by rfl⟩ : syracuseStep 3370307 = 5055461) B5055461
theorem B2246871 : Blo 2245435 2246871 := bstep (se 1 (by rfl) ⟨1685153, by rfl⟩ : syracuseStep 2246871 = 3370307) B3370307
theorem B5687405 : Blo 2245435 5687405 := bbase (se 3 (by rfl) ⟨1066388, by rfl⟩ : syracuseStep 5687405 = 2132777) (by norm_num)
theorem B3791603 : Blo 2245435 3791603 := bstep (se 1 (by rfl) ⟨2843702, by rfl⟩ : syracuseStep 3791603 = 5687405) B5687405
theorem B2527735 : Blo 2245435 2527735 := bstep (se 1 (by rfl) ⟨1895801, by rfl⟩ : syracuseStep 2527735 = 3791603) B3791603
theorem B3370313 : Blo 2245435 3370313 := bstep (se 2 (by rfl) ⟨1263867, by rfl⟩ : syracuseStep 3370313 = 2527735) B2527735
theorem B2246875 : Blo 2245435 2246875 := bstep (se 1 (by rfl) ⟨1685156, by rfl⟩ : syracuseStep 2246875 = 3370313) B3370313
theorem B4798757 : Blo 2245435 4798757 := bbase (se 4 (by rfl) ⟨449883, by rfl⟩ : syracuseStep 4798757 = 899767) (by norm_num)
theorem B3199171 : Blo 2245435 3199171 := bstep (se 1 (by rfl) ⟨2399378, by rfl⟩ : syracuseStep 3199171 = 4798757) B4798757
theorem B4265561 : Blo 2245435 4265561 := bstep (se 2 (by rfl) ⟨1599585, by rfl⟩ : syracuseStep 4265561 = 3199171) B3199171
theorem B11374829 : Blo 2245435 11374829 := bstep (se 3 (by rfl) ⟨2132780, by rfl⟩ : syracuseStep 11374829 = 4265561) B4265561
theorem B7583219 : Blo 2245435 7583219 := bstep (se 1 (by rfl) ⟨5687414, by rfl⟩ : syracuseStep 7583219 = 11374829) B11374829
theorem B5055479 : Blo 2245435 5055479 := bstep (se 1 (by rfl) ⟨3791609, by rfl⟩ : syracuseStep 5055479 = 7583219) B7583219
theorem B3370319 : Blo 2245435 3370319 := bstep (se 1 (by rfl) ⟨2527739, by rfl⟩ : syracuseStep 3370319 = 5055479) B5055479
theorem B2246879 : Blo 2245435 2246879 := bstep (se 1 (by rfl) ⟨1685159, by rfl⟩ : syracuseStep 2246879 = 3370319) B3370319
theorem B3370325 : Blo 2245435 3370325 := bbase (se 11 (by rfl) ⟨2468, by rfl⟩ : syracuseStep 3370325 = 4937) (by norm_num)
theorem B2246883 : Blo 2245435 2246883 := bstep (se 1 (by rfl) ⟨1685162, by rfl⟩ : syracuseStep 2246883 = 3370325) B3370325
theorem B2597197 : Blo 2245435 2597197 := bbase (se 3 (by rfl) ⟨486974, by rfl⟩ : syracuseStep 2597197 = 973949) (by norm_num)
theorem B3462929 : Blo 2245435 3462929 := bstep (se 2 (by rfl) ⟨1298598, by rfl⟩ : syracuseStep 3462929 = 2597197) B2597197
theorem B2308619 : Blo 2245435 2308619 := bstep (se 1 (by rfl) ⟨1731464, by rfl⟩ : syracuseStep 2308619 = 3462929) B3462929
theorem B6156317 : Blo 2245435 6156317 := bstep (se 3 (by rfl) ⟨1154309, by rfl⟩ : syracuseStep 6156317 = 2308619) B2308619
theorem B4104211 : Blo 2245435 4104211 := bstep (se 1 (by rfl) ⟨3078158, by rfl⟩ : syracuseStep 4104211 = 6156317) B6156317
theorem B5472281 : Blo 2245435 5472281 := bstep (se 2 (by rfl) ⟨2052105, by rfl⟩ : syracuseStep 5472281 = 4104211) B4104211
theorem B3648187 : Blo 2245435 3648187 := bstep (se 1 (by rfl) ⟨2736140, by rfl⟩ : syracuseStep 3648187 = 5472281) B5472281
theorem B4864249 : Blo 2245435 4864249 := bstep (se 2 (by rfl) ⟨1824093, by rfl⟩ : syracuseStep 4864249 = 3648187) B3648187
theorem B6485665 : Blo 2245435 6485665 := bstep (se 2 (by rfl) ⟨2432124, by rfl⟩ : syracuseStep 6485665 = 4864249) B4864249
theorem B8647553 : Blo 2245435 8647553 := bstep (se 2 (by rfl) ⟨3242832, by rfl⟩ : syracuseStep 8647553 = 6485665) B6485665
theorem B5765035 : Blo 2245435 5765035 := bstep (se 1 (by rfl) ⟨4323776, by rfl⟩ : syracuseStep 5765035 = 8647553) B8647553
theorem B7686713 : Blo 2245435 7686713 := bstep (se 2 (by rfl) ⟨2882517, by rfl⟩ : syracuseStep 7686713 = 5765035) B5765035
theorem B5124475 : Blo 2245435 5124475 := bstep (se 1 (by rfl) ⟨3843356, by rfl⟩ : syracuseStep 5124475 = 7686713) B7686713
theorem B6832633 : Blo 2245435 6832633 := bstep (se 2 (by rfl) ⟨2562237, by rfl⟩ : syracuseStep 6832633 = 5124475) B5124475
theorem B9110177 : Blo 2245435 9110177 := bstep (se 2 (by rfl) ⟨3416316, by rfl⟩ : syracuseStep 9110177 = 6832633) B6832633
theorem B6073451 : Blo 2245435 6073451 := bstep (se 1 (by rfl) ⟨4555088, by rfl⟩ : syracuseStep 6073451 = 9110177) B9110177
theorem B4048967 : Blo 2245435 4048967 := bstep (se 1 (by rfl) ⟨3036725, by rfl⟩ : syracuseStep 4048967 = 6073451) B6073451
theorem B2699311 : Blo 2245435 2699311 := bstep (se 1 (by rfl) ⟨2024483, by rfl⟩ : syracuseStep 2699311 = 4048967) B4048967
theorem B3599081 : Blo 2245435 3599081 := bstep (se 2 (by rfl) ⟨1349655, by rfl⟩ : syracuseStep 3599081 = 2699311) B2699311
theorem B2399387 : Blo 2245435 2399387 := bstep (se 1 (by rfl) ⟨1799540, by rfl⟩ : syracuseStep 2399387 = 3599081) B3599081
theorem B6398365 : Blo 2245435 6398365 := bstep (se 3 (by rfl) ⟨1199693, by rfl⟩ : syracuseStep 6398365 = 2399387) B2399387
theorem B8531153 : Blo 2245435 8531153 := bstep (se 2 (by rfl) ⟨3199182, by rfl⟩ : syracuseStep 8531153 = 6398365) B6398365
theorem B5687435 : Blo 2245435 5687435 := bstep (se 1 (by rfl) ⟨4265576, by rfl⟩ : syracuseStep 5687435 = 8531153) B8531153
theorem B3791623 : Blo 2245435 3791623 := bstep (se 1 (by rfl) ⟨2843717, by rfl⟩ : syracuseStep 3791623 = 5687435) B5687435
theorem B5055497 : Blo 2245435 5055497 := bstep (se 2 (by rfl) ⟨1895811, by rfl⟩ : syracuseStep 5055497 = 3791623) B3791623
theorem B3370331 : Blo 2245435 3370331 := bstep (se 1 (by rfl) ⟨2527748, by rfl⟩ : syracuseStep 3370331 = 5055497) B5055497
theorem B2246887 : Blo 2245435 2246887 := bstep (se 1 (by rfl) ⟨1685165, by rfl⟩ : syracuseStep 2246887 = 3370331) B3370331
theorem B2527753 : Blo 2245435 2527753 := bbase (se 2 (by rfl) ⟨947907, by rfl⟩ : syracuseStep 2527753 = 1895815) (by norm_num)
theorem B3370337 : Blo 2245435 3370337 := bstep (se 2 (by rfl) ⟨1263876, by rfl⟩ : syracuseStep 3370337 = 2527753) B2527753
theorem B2246891 : Blo 2245435 2246891 := bstep (se 1 (by rfl) ⟨1685168, by rfl⟩ : syracuseStep 2246891 = 3370337) B3370337
theorem B3895805 : Blo 2245435 3895805 := bbase (se 3 (by rfl) ⟨730463, by rfl⟩ : syracuseStep 3895805 = 1460927) (by norm_num)
theorem B2597203 : Blo 2245435 2597203 := bstep (se 1 (by rfl) ⟨1947902, by rfl⟩ : syracuseStep 2597203 = 3895805) B3895805
theorem B13851749 : Blo 2245435 13851749 := bstep (se 4 (by rfl) ⟨1298601, by rfl⟩ : syracuseStep 13851749 = 2597203) B2597203
theorem B9234499 : Blo 2245435 9234499 := bstep (se 1 (by rfl) ⟨6925874, by rfl⟩ : syracuseStep 9234499 = 13851749) B13851749
theorem B12312665 : Blo 2245435 12312665 := bstep (se 2 (by rfl) ⟨4617249, by rfl⟩ : syracuseStep 12312665 = 9234499) B9234499
theorem B8208443 : Blo 2245435 8208443 := bstep (se 1 (by rfl) ⟨6156332, by rfl⟩ : syracuseStep 8208443 = 12312665) B12312665
theorem B21889181 : Blo 2245435 21889181 := bstep (se 3 (by rfl) ⟨4104221, by rfl⟩ : syracuseStep 21889181 = 8208443) B8208443
theorem B14592787 : Blo 2245435 14592787 := bstep (se 1 (by rfl) ⟨10944590, by rfl⟩ : syracuseStep 14592787 = 21889181) B21889181
theorem B77828197 : Blo 2245435 77828197 := bstep (se 4 (by rfl) ⟨7296393, by rfl⟩ : syracuseStep 77828197 = 14592787) B14592787
theorem B103770929 : Blo 2245435 103770929 := bstep (se 2 (by rfl) ⟨38914098, by rfl⟩ : syracuseStep 103770929 = 77828197) B77828197
theorem B276722477 : Blo 2245435 276722477 := bstep (se 3 (by rfl) ⟨51885464, by rfl⟩ : syracuseStep 276722477 = 103770929) B103770929
theorem B184481651 : Blo 2245435 184481651 := bstep (se 1 (by rfl) ⟨138361238, by rfl⟩ : syracuseStep 184481651 = 276722477) B276722477
theorem B122987767 : Blo 2245435 122987767 := bstep (se 1 (by rfl) ⟨92240825, by rfl⟩ : syracuseStep 122987767 = 184481651) B184481651
theorem B163983689 : Blo 2245435 163983689 := bstep (se 2 (by rfl) ⟨61493883, by rfl⟩ : syracuseStep 163983689 = 122987767) B122987767
theorem B109322459 : Blo 2245435 109322459 := bstep (se 1 (by rfl) ⟨81991844, by rfl⟩ : syracuseStep 109322459 = 163983689) B163983689
theorem B72881639 : Blo 2245435 72881639 := bstep (se 1 (by rfl) ⟨54661229, by rfl⟩ : syracuseStep 72881639 = 109322459) B109322459
theorem B48587759 : Blo 2245435 48587759 := bstep (se 1 (by rfl) ⟨36440819, by rfl⟩ : syracuseStep 48587759 = 72881639) B72881639
theorem B32391839 : Blo 2245435 32391839 := bstep (se 1 (by rfl) ⟨24293879, by rfl⟩ : syracuseStep 32391839 = 48587759) B48587759
theorem B21594559 : Blo 2245435 21594559 := bstep (se 1 (by rfl) ⟨16195919, by rfl⟩ : syracuseStep 21594559 = 32391839) B32391839
theorem B28792745 : Blo 2245435 28792745 := bstep (se 2 (by rfl) ⟨10797279, by rfl⟩ : syracuseStep 28792745 = 21594559) B21594559
theorem B19195163 : Blo 2245435 19195163 := bstep (se 1 (by rfl) ⟨14396372, by rfl⟩ : syracuseStep 19195163 = 28792745) B28792745
theorem B12796775 : Blo 2245435 12796775 := bstep (se 1 (by rfl) ⟨9597581, by rfl⟩ : syracuseStep 12796775 = 19195163) B19195163
theorem B8531183 : Blo 2245435 8531183 := bstep (se 1 (by rfl) ⟨6398387, by rfl⟩ : syracuseStep 8531183 = 12796775) B12796775
theorem B5687455 : Blo 2245435 5687455 := bstep (se 1 (by rfl) ⟨4265591, by rfl⟩ : syracuseStep 5687455 = 8531183) B8531183
theorem B7583273 : Blo 2245435 7583273 := bstep (se 2 (by rfl) ⟨2843727, by rfl⟩ : syracuseStep 7583273 = 5687455) B5687455
theorem B5055515 : Blo 2245435 5055515 := bstep (se 1 (by rfl) ⟨3791636, by rfl⟩ : syracuseStep 5055515 = 7583273) B7583273
theorem B3370343 : Blo 2245435 3370343 := bstep (se 1 (by rfl) ⟨2527757, by rfl⟩ : syracuseStep 3370343 = 5055515) B5055515
theorem B2246895 : Blo 2245435 2246895 := bstep (se 1 (by rfl) ⟨1685171, by rfl⟩ : syracuseStep 2246895 = 3370343) B3370343
theorem B3370349 : Blo 2245435 3370349 := bbase (se 3 (by rfl) ⟨631940, by rfl⟩ : syracuseStep 3370349 = 1263881) (by norm_num)
theorem B2246899 : Blo 2245435 2246899 := bstep (se 1 (by rfl) ⟨1685174, by rfl⟩ : syracuseStep 2246899 = 3370349) B3370349
theorem B5055533 : Blo 2245435 5055533 := bbase (se 3 (by rfl) ⟨947912, by rfl⟩ : syracuseStep 5055533 = 1895825) (by norm_num)
theorem B3370355 : Blo 2245435 3370355 := bstep (se 1 (by rfl) ⟨2527766, by rfl⟩ : syracuseStep 3370355 = 5055533) B5055533
theorem B2246903 : Blo 2245435 2246903 := bstep (se 1 (by rfl) ⟨1685177, by rfl⟩ : syracuseStep 2246903 = 3370355) B3370355
theorem B6574213 : Blo 2245435 6574213 := bbase (se 4 (by rfl) ⟨616332, by rfl⟩ : syracuseStep 6574213 = 1232665) (by norm_num)
theorem B8765617 : Blo 2245435 8765617 := bstep (se 2 (by rfl) ⟨3287106, by rfl⟩ : syracuseStep 8765617 = 6574213) B6574213
theorem B11687489 : Blo 2245435 11687489 := bstep (se 2 (by rfl) ⟨4382808, by rfl⟩ : syracuseStep 11687489 = 8765617) B8765617
theorem B7791659 : Blo 2245435 7791659 := bstep (se 1 (by rfl) ⟨5843744, by rfl⟩ : syracuseStep 7791659 = 11687489) B11687489
theorem B5194439 : Blo 2245435 5194439 := bstep (se 1 (by rfl) ⟨3895829, by rfl⟩ : syracuseStep 5194439 = 7791659) B7791659
theorem B3462959 : Blo 2245435 3462959 := bstep (se 1 (by rfl) ⟨2597219, by rfl⟩ : syracuseStep 3462959 = 5194439) B5194439
theorem B9234557 : Blo 2245435 9234557 := bstep (se 3 (by rfl) ⟨1731479, by rfl⟩ : syracuseStep 9234557 = 3462959) B3462959
theorem B6156371 : Blo 2245435 6156371 := bstep (se 1 (by rfl) ⟨4617278, by rfl⟩ : syracuseStep 6156371 = 9234557) B9234557
theorem B16416989 : Blo 2245435 16416989 := bstep (se 3 (by rfl) ⟨3078185, by rfl⟩ : syracuseStep 16416989 = 6156371) B6156371
theorem B10944659 : Blo 2245435 10944659 := bstep (se 1 (by rfl) ⟨8208494, by rfl⟩ : syracuseStep 10944659 = 16416989) B16416989
theorem B29185757 : Blo 2245435 29185757 := bstep (se 3 (by rfl) ⟨5472329, by rfl⟩ : syracuseStep 29185757 = 10944659) B10944659
theorem B19457171 : Blo 2245435 19457171 := bstep (se 1 (by rfl) ⟨14592878, by rfl⟩ : syracuseStep 19457171 = 29185757) B29185757
theorem B12971447 : Blo 2245435 12971447 := bstep (se 1 (by rfl) ⟨9728585, by rfl⟩ : syracuseStep 12971447 = 19457171) B19457171
theorem B8647631 : Blo 2245435 8647631 := bstep (se 1 (by rfl) ⟨6485723, by rfl⟩ : syracuseStep 8647631 = 12971447) B12971447
theorem B5765087 : Blo 2245435 5765087 := bstep (se 1 (by rfl) ⟨4323815, by rfl⟩ : syracuseStep 5765087 = 8647631) B8647631
theorem B3843391 : Blo 2245435 3843391 := bstep (se 1 (by rfl) ⟨2882543, by rfl⟩ : syracuseStep 3843391 = 5765087) B5765087
theorem B5124521 : Blo 2245435 5124521 := bstep (se 2 (by rfl) ⟨1921695, by rfl⟩ : syracuseStep 5124521 = 3843391) B3843391
theorem B3416347 : Blo 2245435 3416347 := bstep (se 1 (by rfl) ⟨2562260, by rfl⟩ : syracuseStep 3416347 = 5124521) B5124521
theorem B4555129 : Blo 2245435 4555129 := bstep (se 2 (by rfl) ⟨1708173, by rfl⟩ : syracuseStep 4555129 = 3416347) B3416347
theorem B6073505 : Blo 2245435 6073505 := bstep (se 2 (by rfl) ⟨2277564, by rfl⟩ : syracuseStep 6073505 = 4555129) B4555129
theorem B4049003 : Blo 2245435 4049003 := bstep (se 1 (by rfl) ⟨3036752, by rfl⟩ : syracuseStep 4049003 = 6073505) B6073505
theorem B2699335 : Blo 2245435 2699335 := bstep (se 1 (by rfl) ⟨2024501, by rfl⟩ : syracuseStep 2699335 = 4049003) B4049003
theorem B14396453 : Blo 2245435 14396453 := bstep (se 4 (by rfl) ⟨1349667, by rfl⟩ : syracuseStep 14396453 = 2699335) B2699335
theorem B9597635 : Blo 2245435 9597635 := bstep (se 1 (by rfl) ⟨7198226, by rfl⟩ : syracuseStep 9597635 = 14396453) B14396453
theorem B6398423 : Blo 2245435 6398423 := bstep (se 1 (by rfl) ⟨4798817, by rfl⟩ : syracuseStep 6398423 = 9597635) B9597635
theorem B4265615 : Blo 2245435 4265615 := bstep (se 1 (by rfl) ⟨3199211, by rfl⟩ : syracuseStep 4265615 = 6398423) B6398423
theorem B2843743 : Blo 2245435 2843743 := bstep (se 1 (by rfl) ⟨2132807, by rfl⟩ : syracuseStep 2843743 = 4265615) B4265615
theorem B3791657 : Blo 2245435 3791657 := bstep (se 2 (by rfl) ⟨1421871, by rfl⟩ : syracuseStep 3791657 = 2843743) B2843743
theorem B2527771 : Blo 2245435 2527771 := bstep (se 1 (by rfl) ⟨1895828, by rfl⟩ : syracuseStep 2527771 = 3791657) B3791657
theorem B3370361 : Blo 2245435 3370361 := bstep (se 2 (by rfl) ⟨1263885, by rfl⟩ : syracuseStep 3370361 = 2527771) B2527771
theorem B2246907 : Blo 2245435 2246907 := bstep (se 1 (by rfl) ⟨1685180, by rfl⟩ : syracuseStep 2246907 = 3370361) B3370361
theorem B3036757 : Blo 2245435 3036757 := bbase (se 8 (by rfl) ⟨17793, by rfl⟩ : syracuseStep 3036757 = 35587) (by norm_num)
theorem B4049009 : Blo 2245435 4049009 := bstep (se 2 (by rfl) ⟨1518378, by rfl⟩ : syracuseStep 4049009 = 3036757) B3036757
theorem B2699339 : Blo 2245435 2699339 := bstep (se 1 (by rfl) ⟨2024504, by rfl⟩ : syracuseStep 2699339 = 4049009) B4049009
theorem B7198237 : Blo 2245435 7198237 := bstep (se 3 (by rfl) ⟨1349669, by rfl⟩ : syracuseStep 7198237 = 2699339) B2699339
theorem B38390597 : Blo 2245435 38390597 := bstep (se 4 (by rfl) ⟨3599118, by rfl⟩ : syracuseStep 38390597 = 7198237) B7198237
theorem B25593731 : Blo 2245435 25593731 := bstep (se 1 (by rfl) ⟨19195298, by rfl⟩ : syracuseStep 25593731 = 38390597) B38390597
theorem B17062487 : Blo 2245435 17062487 := bstep (se 1 (by rfl) ⟨12796865, by rfl⟩ : syracuseStep 17062487 = 25593731) B25593731
theorem B11374991 : Blo 2245435 11374991 := bstep (se 1 (by rfl) ⟨8531243, by rfl⟩ : syracuseStep 11374991 = 17062487) B17062487
theorem B7583327 : Blo 2245435 7583327 := bstep (se 1 (by rfl) ⟨5687495, by rfl⟩ : syracuseStep 7583327 = 11374991) B11374991
theorem B5055551 : Blo 2245435 5055551 := bstep (se 1 (by rfl) ⟨3791663, by rfl⟩ : syracuseStep 5055551 = 7583327) B7583327
theorem B3370367 : Blo 2245435 3370367 := bstep (se 1 (by rfl) ⟨2527775, by rfl⟩ : syracuseStep 3370367 = 5055551) B5055551
theorem B2246911 : Blo 2245435 2246911 := bstep (se 1 (by rfl) ⟨1685183, by rfl⟩ : syracuseStep 2246911 = 3370367) B3370367
theorem B3370373 : Blo 2245435 3370373 := bbase (se 4 (by rfl) ⟨315972, by rfl⟩ : syracuseStep 3370373 = 631945) (by norm_num)
theorem B2246915 : Blo 2245435 2246915 := bstep (se 1 (by rfl) ⟨1685186, by rfl⟩ : syracuseStep 2246915 = 3370373) B3370373
theorem B3791677 : Blo 2245435 3791677 := bbase (se 3 (by rfl) ⟨710939, by rfl⟩ : syracuseStep 3791677 = 1421879) (by norm_num)
theorem B5055569 : Blo 2245435 5055569 := bstep (se 2 (by rfl) ⟨1895838, by rfl⟩ : syracuseStep 5055569 = 3791677) B3791677
theorem B3370379 : Blo 2245435 3370379 := bstep (se 1 (by rfl) ⟨2527784, by rfl⟩ : syracuseStep 3370379 = 5055569) B5055569
theorem B2246919 : Blo 2245435 2246919 := bstep (se 1 (by rfl) ⟨1685189, by rfl⟩ : syracuseStep 2246919 = 3370379) B3370379
theorem B2527789 : Blo 2245435 2527789 := bbase (se 3 (by rfl) ⟨473960, by rfl⟩ : syracuseStep 2527789 = 947921) (by norm_num)
theorem B3370385 : Blo 2245435 3370385 := bstep (se 2 (by rfl) ⟨1263894, by rfl⟩ : syracuseStep 3370385 = 2527789) B2527789
theorem B2246923 : Blo 2245435 2246923 := bstep (se 1 (by rfl) ⟨1685192, by rfl⟩ : syracuseStep 2246923 = 3370385) B3370385
theorem B7583381 : Blo 2245435 7583381 := bbase (se 6 (by rfl) ⟨177735, by rfl⟩ : syracuseStep 7583381 = 355471) (by norm_num)
theorem B5055587 : Blo 2245435 5055587 := bstep (se 1 (by rfl) ⟨3791690, by rfl⟩ : syracuseStep 5055587 = 7583381) B7583381
theorem B3370391 : Blo 2245435 3370391 := bstep (se 1 (by rfl) ⟨2527793, by rfl⟩ : syracuseStep 3370391 = 5055587) B5055587
theorem B2246927 : Blo 2245435 2246927 := bstep (se 1 (by rfl) ⟨1685195, by rfl⟩ : syracuseStep 2246927 = 3370391) B3370391
theorem B3370397 : Blo 2245435 3370397 := bbase (se 3 (by rfl) ⟨631949, by rfl⟩ : syracuseStep 3370397 = 1263899) (by norm_num)
theorem B2246931 : Blo 2245435 2246931 := bstep (se 1 (by rfl) ⟨1685198, by rfl⟩ : syracuseStep 2246931 = 3370397) B3370397
theorem B5055605 : Blo 2245435 5055605 := bbase (se 5 (by rfl) ⟨236981, by rfl⟩ : syracuseStep 5055605 = 473963) (by norm_num)
theorem B3370403 : Blo 2245435 3370403 := bstep (se 1 (by rfl) ⟨2527802, by rfl⟩ : syracuseStep 3370403 = 5055605) B5055605
theorem B2246935 : Blo 2245435 2246935 := bstep (se 1 (by rfl) ⟨1685201, by rfl⟩ : syracuseStep 2246935 = 3370403) B3370403
theorem B19195541 : Blo 2245435 19195541 := bbase (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) (by norm_num)
theorem B12797027 : Blo 2245435 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B8531351 : Blo 2245435 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B5687567 : Blo 2245435 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B3791711 : Blo 2245435 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B2527807 : Blo 2245435 2527807 := bstep (se 1 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 2527807 = 3791711) B3791711
theorem B3370409 : Blo 2245435 3370409 := bstep (se 2 (by rfl) ⟨1263903, by rfl⟩ : syracuseStep 3370409 = 2527807) B2527807
theorem B2246939 : Blo 2245435 2246939 := bstep (se 1 (by rfl) ⟨1685204, by rfl⟩ : syracuseStep 2246939 = 3370409) B3370409
theorem B8531365 : Blo 2245435 8531365 := bbase (se 4 (by rfl) ⟨799815, by rfl⟩ : syracuseStep 8531365 = 1599631) (by norm_num)
theorem B11375153 : Blo 2245435 11375153 := bstep (se 2 (by rfl) ⟨4265682, by rfl⟩ : syracuseStep 11375153 = 8531365) B8531365
theorem B7583435 : Blo 2245435 7583435 := bstep (se 1 (by rfl) ⟨5687576, by rfl⟩ : syracuseStep 7583435 = 11375153) B11375153
theorem B5055623 : Blo 2245435 5055623 := bstep (se 1 (by rfl) ⟨3791717, by rfl⟩ : syracuseStep 5055623 = 7583435) B7583435
theorem B3370415 : Blo 2245435 3370415 := bstep (se 1 (by rfl) ⟨2527811, by rfl⟩ : syracuseStep 3370415 = 5055623) B5055623
theorem B2246943 : Blo 2245435 2246943 := bstep (se 1 (by rfl) ⟨1685207, by rfl⟩ : syracuseStep 2246943 = 3370415) B3370415
theorem B3370421 : Blo 2245435 3370421 := bbase (se 5 (by rfl) ⟨157988, by rfl⟩ : syracuseStep 3370421 = 315977) (by norm_num)
theorem B2246947 : Blo 2245435 2246947 := bstep (se 1 (by rfl) ⟨1685210, by rfl⟩ : syracuseStep 2246947 = 3370421) B3370421
theorem B5687597 : Blo 2245435 5687597 := bbase (se 3 (by rfl) ⟨1066424, by rfl⟩ : syracuseStep 5687597 = 2132849) (by norm_num)
theorem B3791731 : Blo 2245435 3791731 := bstep (se 1 (by rfl) ⟨2843798, by rfl⟩ : syracuseStep 3791731 = 5687597) B5687597
theorem B5055641 : Blo 2245435 5055641 := bstep (se 2 (by rfl) ⟨1895865, by rfl⟩ : syracuseStep 5055641 = 3791731) B3791731
theorem B3370427 : Blo 2245435 3370427 := bstep (se 1 (by rfl) ⟨2527820, by rfl⟩ : syracuseStep 3370427 = 5055641) B5055641
theorem B2246951 : Blo 2245435 2246951 := bstep (se 1 (by rfl) ⟨1685213, by rfl⟩ : syracuseStep 2246951 = 3370427) B3370427
theorem B2527825 : Blo 2245435 2527825 := bbase (se 2 (by rfl) ⟨947934, by rfl⟩ : syracuseStep 2527825 = 1895869) (by norm_num)
theorem B3370433 : Blo 2245435 3370433 := bstep (se 2 (by rfl) ⟨1263912, by rfl⟩ : syracuseStep 3370433 = 2527825) B2527825
theorem B2246955 : Blo 2245435 2246955 := bstep (se 1 (by rfl) ⟨1685216, by rfl⟩ : syracuseStep 2246955 = 3370433) B3370433
theorem B3199285 : Blo 2245435 3199285 := bbase (se 5 (by rfl) ⟨149966, by rfl⟩ : syracuseStep 3199285 = 299933) (by norm_num)
theorem B4265713 : Blo 2245435 4265713 := bstep (se 2 (by rfl) ⟨1599642, by rfl⟩ : syracuseStep 4265713 = 3199285) B3199285
theorem B5687617 : Blo 2245435 5687617 := bstep (se 2 (by rfl) ⟨2132856, by rfl⟩ : syracuseStep 5687617 = 4265713) B4265713
theorem B7583489 : Blo 2245435 7583489 := bstep (se 2 (by rfl) ⟨2843808, by rfl⟩ : syracuseStep 7583489 = 5687617) B5687617
theorem B5055659 : Blo 2245435 5055659 := bstep (se 1 (by rfl) ⟨3791744, by rfl⟩ : syracuseStep 5055659 = 7583489) B7583489
theorem B3370439 : Blo 2245435 3370439 := bstep (se 1 (by rfl) ⟨2527829, by rfl⟩ : syracuseStep 3370439 = 5055659) B5055659
theorem B2246959 : Blo 2245435 2246959 := bstep (se 1 (by rfl) ⟨1685219, by rfl⟩ : syracuseStep 2246959 = 3370439) B3370439
theorem B3370445 : Blo 2245435 3370445 := bbase (se 3 (by rfl) ⟨631958, by rfl⟩ : syracuseStep 3370445 = 1263917) (by norm_num)
theorem B2246963 : Blo 2245435 2246963 := bstep (se 1 (by rfl) ⟨1685222, by rfl⟩ : syracuseStep 2246963 = 3370445) B3370445
theorem B5055677 : Blo 2245435 5055677 := bbase (se 3 (by rfl) ⟨947939, by rfl⟩ : syracuseStep 5055677 = 1895879) (by norm_num)
theorem B3370451 : Blo 2245435 3370451 := bstep (se 1 (by rfl) ⟨2527838, by rfl⟩ : syracuseStep 3370451 = 5055677) B5055677
theorem B2246967 : Blo 2245435 2246967 := bstep (se 1 (by rfl) ⟨1685225, by rfl⟩ : syracuseStep 2246967 = 3370451) B3370451
theorem B3791765 : Blo 2245435 3791765 := bbase (se 6 (by rfl) ⟨88869, by rfl⟩ : syracuseStep 3791765 = 177739) (by norm_num)
theorem B2527843 : Blo 2245435 2527843 := bstep (se 1 (by rfl) ⟨1895882, by rfl⟩ : syracuseStep 2527843 = 3791765) B3791765
theorem B3370457 : Blo 2245435 3370457 := bstep (se 2 (by rfl) ⟨1263921, by rfl⟩ : syracuseStep 3370457 = 2527843) B2527843
theorem B2246971 : Blo 2245435 2246971 := bstep (se 1 (by rfl) ⟨1685228, by rfl⟩ : syracuseStep 2246971 = 3370457) B3370457
theorem B14396885 : Blo 2245435 14396885 := bbase (se 7 (by rfl) ⟨168713, by rfl⟩ : syracuseStep 14396885 = 337427) (by norm_num)
theorem B9597923 : Blo 2245435 9597923 := bstep (se 1 (by rfl) ⟨7198442, by rfl⟩ : syracuseStep 9597923 = 14396885) B14396885
theorem B6398615 : Blo 2245435 6398615 := bstep (se 1 (by rfl) ⟨4798961, by rfl⟩ : syracuseStep 6398615 = 9597923) B9597923
theorem B17062973 : Blo 2245435 17062973 := bstep (se 3 (by rfl) ⟨3199307, by rfl⟩ : syracuseStep 17062973 = 6398615) B6398615
theorem B11375315 : Blo 2245435 11375315 := bstep (se 1 (by rfl) ⟨8531486, by rfl⟩ : syracuseStep 11375315 = 17062973) B17062973
theorem B7583543 : Blo 2245435 7583543 := bstep (se 1 (by rfl) ⟨5687657, by rfl⟩ : syracuseStep 7583543 = 11375315) B11375315
theorem B5055695 : Blo 2245435 5055695 := bstep (se 1 (by rfl) ⟨3791771, by rfl⟩ : syracuseStep 5055695 = 7583543) B7583543
theorem B3370463 : Blo 2245435 3370463 := bstep (se 1 (by rfl) ⟨2527847, by rfl⟩ : syracuseStep 3370463 = 5055695) B5055695
theorem B2246975 : Blo 2245435 2246975 := bstep (se 1 (by rfl) ⟨1685231, by rfl⟩ : syracuseStep 2246975 = 3370463) B3370463
theorem B3370469 : Blo 2245435 3370469 := bbase (se 4 (by rfl) ⟨315981, by rfl⟩ : syracuseStep 3370469 = 631963) (by norm_num)
theorem B2246979 : Blo 2245435 2246979 := bstep (se 1 (by rfl) ⟨1685234, by rfl⟩ : syracuseStep 2246979 = 3370469) B3370469
theorem B2277641 : Blo 2245435 2277641 := bbase (se 2 (by rfl) ⟨854115, by rfl⟩ : syracuseStep 2277641 = 1708231) (by norm_num)
theorem B6073709 : Blo 2245435 6073709 := bstep (se 3 (by rfl) ⟨1138820, by rfl⟩ : syracuseStep 6073709 = 2277641) B2277641
theorem B16196557 : Blo 2245435 16196557 := bstep (se 3 (by rfl) ⟨3036854, by rfl⟩ : syracuseStep 16196557 = 6073709) B6073709
theorem B21595409 : Blo 2245435 21595409 := bstep (se 2 (by rfl) ⟨8098278, by rfl⟩ : syracuseStep 21595409 = 16196557) B16196557
theorem B14396939 : Blo 2245435 14396939 := bstep (se 1 (by rfl) ⟨10797704, by rfl⟩ : syracuseStep 14396939 = 21595409) B21595409
theorem B9597959 : Blo 2245435 9597959 := bstep (se 1 (by rfl) ⟨7198469, by rfl⟩ : syracuseStep 9597959 = 14396939) B14396939
theorem B6398639 : Blo 2245435 6398639 := bstep (se 1 (by rfl) ⟨4798979, by rfl⟩ : syracuseStep 6398639 = 9597959) B9597959
theorem B4265759 : Blo 2245435 4265759 := bstep (se 1 (by rfl) ⟨3199319, by rfl⟩ : syracuseStep 4265759 = 6398639) B6398639
theorem B2843839 : Blo 2245435 2843839 := bstep (se 1 (by rfl) ⟨2132879, by rfl⟩ : syracuseStep 2843839 = 4265759) B4265759
theorem B3791785 : Blo 2245435 3791785 := bstep (se 2 (by rfl) ⟨1421919, by rfl⟩ : syracuseStep 3791785 = 2843839) B2843839
theorem B5055713 : Blo 2245435 5055713 := bstep (se 2 (by rfl) ⟨1895892, by rfl⟩ : syracuseStep 5055713 = 3791785) B3791785
theorem B3370475 : Blo 2245435 3370475 := bstep (se 1 (by rfl) ⟨2527856, by rfl⟩ : syracuseStep 3370475 = 5055713) B5055713
theorem B2246983 : Blo 2245435 2246983 := bstep (se 1 (by rfl) ⟨1685237, by rfl⟩ : syracuseStep 2246983 = 3370475) B3370475
theorem B2527861 : Blo 2245435 2527861 := bbase (se 5 (by rfl) ⟨118493, by rfl⟩ : syracuseStep 2527861 = 236987) (by norm_num)
theorem B3370481 : Blo 2245435 3370481 := bstep (se 2 (by rfl) ⟨1263930, by rfl⟩ : syracuseStep 3370481 = 2527861) B2527861
theorem B2246987 : Blo 2245435 2246987 := bstep (se 1 (by rfl) ⟨1685240, by rfl⟩ : syracuseStep 2246987 = 3370481) B3370481
theorem B2843849 : Blo 2245435 2843849 := bbase (se 2 (by rfl) ⟨1066443, by rfl⟩ : syracuseStep 2843849 = 2132887) (by norm_num)
theorem B7583597 : Blo 2245435 7583597 := bstep (se 3 (by rfl) ⟨1421924, by rfl⟩ : syracuseStep 7583597 = 2843849) B2843849
theorem B5055731 : Blo 2245435 5055731 := bstep (se 1 (by rfl) ⟨3791798, by rfl⟩ : syracuseStep 5055731 = 7583597) B7583597
theorem B3370487 : Blo 2245435 3370487 := bstep (se 1 (by rfl) ⟨2527865, by rfl⟩ : syracuseStep 3370487 = 5055731) B5055731
theorem B2246991 : Blo 2245435 2246991 := bstep (se 1 (by rfl) ⟨1685243, by rfl⟩ : syracuseStep 2246991 = 3370487) B3370487
theorem B3370493 : Blo 2245435 3370493 := bbase (se 3 (by rfl) ⟨631967, by rfl⟩ : syracuseStep 3370493 = 1263935) (by norm_num)
theorem B2246995 : Blo 2245435 2246995 := bstep (se 1 (by rfl) ⟨1685246, by rfl⟩ : syracuseStep 2246995 = 3370493) B3370493
theorem B5055749 : Blo 2245435 5055749 := bbase (se 4 (by rfl) ⟨473976, by rfl⟩ : syracuseStep 5055749 = 947953) (by norm_num)
theorem B3370499 : Blo 2245435 3370499 := bstep (se 1 (by rfl) ⟨2527874, by rfl⟩ : syracuseStep 3370499 = 5055749) B5055749
theorem B2246999 : Blo 2245435 2246999 := bstep (se 1 (by rfl) ⟨1685249, by rfl⟩ : syracuseStep 2246999 = 3370499) B3370499
theorem B4265797 : Blo 2245435 4265797 := bbase (se 4 (by rfl) ⟨399918, by rfl⟩ : syracuseStep 4265797 = 799837) (by norm_num)
theorem B5687729 : Blo 2245435 5687729 := bstep (se 2 (by rfl) ⟨2132898, by rfl⟩ : syracuseStep 5687729 = 4265797) B4265797
theorem B3791819 : Blo 2245435 3791819 := bstep (se 1 (by rfl) ⟨2843864, by rfl⟩ : syracuseStep 3791819 = 5687729) B5687729
theorem B2527879 : Blo 2245435 2527879 := bstep (se 1 (by rfl) ⟨1895909, by rfl⟩ : syracuseStep 2527879 = 3791819) B3791819
theorem B3370505 : Blo 2245435 3370505 := bstep (se 2 (by rfl) ⟨1263939, by rfl⟩ : syracuseStep 3370505 = 2527879) B2527879
theorem B2247003 : Blo 2245435 2247003 := bstep (se 1 (by rfl) ⟨1685252, by rfl⟩ : syracuseStep 2247003 = 3370505) B3370505
theorem B11375477 : Blo 2245435 11375477 := bbase (se 5 (by rfl) ⟨533225, by rfl⟩ : syracuseStep 11375477 = 1066451) (by norm_num)
theorem B7583651 : Blo 2245435 7583651 := bstep (se 1 (by rfl) ⟨5687738, by rfl⟩ : syracuseStep 7583651 = 11375477) B11375477
theorem B5055767 : Blo 2245435 5055767 := bstep (se 1 (by rfl) ⟨3791825, by rfl⟩ : syracuseStep 5055767 = 7583651) B7583651
theorem B3370511 : Blo 2245435 3370511 := bstep (se 1 (by rfl) ⟨2527883, by rfl⟩ : syracuseStep 3370511 = 5055767) B5055767
theorem B2247007 : Blo 2245435 2247007 := bstep (se 1 (by rfl) ⟨1685255, by rfl⟩ : syracuseStep 2247007 = 3370511) B3370511
theorem B3370517 : Blo 2245435 3370517 := bbase (se 6 (by rfl) ⟨78996, by rfl⟩ : syracuseStep 3370517 = 157993) (by norm_num)
theorem B2247011 : Blo 2245435 2247011 := bstep (se 1 (by rfl) ⟨1685258, by rfl⟩ : syracuseStep 2247011 = 3370517) B3370517
theorem B9110693 : Blo 2245435 9110693 := bbase (se 4 (by rfl) ⟨854127, by rfl⟩ : syracuseStep 9110693 = 1708255) (by norm_num)
theorem B6073795 : Blo 2245435 6073795 := bstep (se 1 (by rfl) ⟨4555346, by rfl⟩ : syracuseStep 6073795 = 9110693) B9110693
theorem B8098393 : Blo 2245435 8098393 := bstep (se 2 (by rfl) ⟨3036897, by rfl⟩ : syracuseStep 8098393 = 6073795) B6073795
theorem B10797857 : Blo 2245435 10797857 := bstep (se 2 (by rfl) ⟨4049196, by rfl⟩ : syracuseStep 10797857 = 8098393) B8098393
theorem B7198571 : Blo 2245435 7198571 := bstep (se 1 (by rfl) ⟨5398928, by rfl⟩ : syracuseStep 7198571 = 10797857) B10797857
theorem B19196189 : Blo 2245435 19196189 := bstep (se 3 (by rfl) ⟨3599285, by rfl⟩ : syracuseStep 19196189 = 7198571) B7198571
theorem B12797459 : Blo 2245435 12797459 := bstep (se 1 (by rfl) ⟨9598094, by rfl⟩ : syracuseStep 12797459 = 19196189) B19196189
theorem B8531639 : Blo 2245435 8531639 := bstep (se 1 (by rfl) ⟨6398729, by rfl⟩ : syracuseStep 8531639 = 12797459) B12797459
theorem B5687759 : Blo 2245435 5687759 := bstep (se 1 (by rfl) ⟨4265819, by rfl⟩ : syracuseStep 5687759 = 8531639) B8531639
theorem B3791839 : Blo 2245435 3791839 := bstep (se 1 (by rfl) ⟨2843879, by rfl⟩ : syracuseStep 3791839 = 5687759) B5687759
theorem B5055785 : Blo 2245435 5055785 := bstep (se 2 (by rfl) ⟨1895919, by rfl⟩ : syracuseStep 5055785 = 3791839) B3791839
theorem B3370523 : Blo 2245435 3370523 := bstep (se 1 (by rfl) ⟨2527892, by rfl⟩ : syracuseStep 3370523 = 5055785) B5055785
theorem B2247015 : Blo 2245435 2247015 := bstep (se 1 (by rfl) ⟨1685261, by rfl⟩ : syracuseStep 2247015 = 3370523) B3370523
theorem B2527897 : Blo 2245435 2527897 := bbase (se 2 (by rfl) ⟨947961, by rfl⟩ : syracuseStep 2527897 = 1895923) (by norm_num)
theorem B3370529 : Blo 2245435 3370529 := bstep (se 2 (by rfl) ⟨1263948, by rfl⟩ : syracuseStep 3370529 = 2527897) B2527897
theorem B2247019 : Blo 2245435 2247019 := bstep (se 1 (by rfl) ⟨1685264, by rfl⟩ : syracuseStep 2247019 = 3370529) B3370529
theorem B8531669 : Blo 2245435 8531669 := bbase (se 7 (by rfl) ⟨99980, by rfl⟩ : syracuseStep 8531669 = 199961) (by norm_num)
theorem B5687779 : Blo 2245435 5687779 := bstep (se 1 (by rfl) ⟨4265834, by rfl⟩ : syracuseStep 5687779 = 8531669) B8531669
theorem B7583705 : Blo 2245435 7583705 := bstep (se 2 (by rfl) ⟨2843889, by rfl⟩ : syracuseStep 7583705 = 5687779) B5687779
theorem B5055803 : Blo 2245435 5055803 := bstep (se 1 (by rfl) ⟨3791852, by rfl⟩ : syracuseStep 5055803 = 7583705) B7583705
theorem B3370535 : Blo 2245435 3370535 := bstep (se 1 (by rfl) ⟨2527901, by rfl⟩ : syracuseStep 3370535 = 5055803) B5055803
theorem B2247023 : Blo 2245435 2247023 := bstep (se 1 (by rfl) ⟨1685267, by rfl⟩ : syracuseStep 2247023 = 3370535) B3370535
theorem B3370541 : Blo 2245435 3370541 := bbase (se 3 (by rfl) ⟨631976, by rfl⟩ : syracuseStep 3370541 = 1263953) (by norm_num)
theorem B2247027 : Blo 2245435 2247027 := bstep (se 1 (by rfl) ⟨1685270, by rfl⟩ : syracuseStep 2247027 = 3370541) B3370541
theorem B5055821 : Blo 2245435 5055821 := bbase (se 3 (by rfl) ⟨947966, by rfl⟩ : syracuseStep 5055821 = 1895933) (by norm_num)
theorem B3370547 : Blo 2245435 3370547 := bstep (se 1 (by rfl) ⟨2527910, by rfl⟩ : syracuseStep 3370547 = 5055821) B5055821
theorem B2247031 : Blo 2245435 2247031 := bstep (se 1 (by rfl) ⟨1685273, by rfl⟩ : syracuseStep 2247031 = 3370547) B3370547
theorem B2843905 : Blo 2245435 2843905 := bbase (se 2 (by rfl) ⟨1066464, by rfl⟩ : syracuseStep 2843905 = 2132929) (by norm_num)
theorem B3791873 : Blo 2245435 3791873 := bstep (se 2 (by rfl) ⟨1421952, by rfl⟩ : syracuseStep 3791873 = 2843905) B2843905
theorem B2527915 : Blo 2245435 2527915 := bstep (se 1 (by rfl) ⟨1895936, by rfl⟩ : syracuseStep 2527915 = 3791873) B3791873
theorem B3370553 : Blo 2245435 3370553 := bstep (se 2 (by rfl) ⟨1263957, by rfl⟩ : syracuseStep 3370553 = 2527915) B2527915
theorem B2247035 : Blo 2245435 2247035 := bstep (se 1 (by rfl) ⟨1685276, by rfl⟩ : syracuseStep 2247035 = 3370553) B3370553
theorem B2399549 : Blo 2245435 2399549 := bbase (se 3 (by rfl) ⟨449915, by rfl⟩ : syracuseStep 2399549 = 899831) (by norm_num)
theorem B25595189 : Blo 2245435 25595189 := bstep (se 5 (by rfl) ⟨1199774, by rfl⟩ : syracuseStep 25595189 = 2399549) B2399549
theorem B17063459 : Blo 2245435 17063459 := bstep (se 1 (by rfl) ⟨12797594, by rfl⟩ : syracuseStep 17063459 = 25595189) B25595189
theorem B11375639 : Blo 2245435 11375639 := bstep (se 1 (by rfl) ⟨8531729, by rfl⟩ : syracuseStep 11375639 = 17063459) B17063459
theorem B7583759 : Blo 2245435 7583759 := bstep (se 1 (by rfl) ⟨5687819, by rfl⟩ : syracuseStep 7583759 = 11375639) B11375639
theorem B5055839 : Blo 2245435 5055839 := bstep (se 1 (by rfl) ⟨3791879, by rfl⟩ : syracuseStep 5055839 = 7583759) B7583759
theorem B3370559 : Blo 2245435 3370559 := bstep (se 1 (by rfl) ⟨2527919, by rfl⟩ : syracuseStep 3370559 = 5055839) B5055839
theorem B2247039 : Blo 2245435 2247039 := bstep (se 1 (by rfl) ⟨1685279, by rfl⟩ : syracuseStep 2247039 = 3370559) B3370559
theorem B3370565 : Blo 2245435 3370565 := bbase (se 4 (by rfl) ⟨315990, by rfl⟩ : syracuseStep 3370565 = 631981) (by norm_num)
theorem B2247043 : Blo 2245435 2247043 := bstep (se 1 (by rfl) ⟨1685282, by rfl⟩ : syracuseStep 2247043 = 3370565) B3370565
theorem B3791893 : Blo 2245435 3791893 := bbase (se 6 (by rfl) ⟨88872, by rfl⟩ : syracuseStep 3791893 = 177745) (by norm_num)
theorem B5055857 : Blo 2245435 5055857 := bstep (se 2 (by rfl) ⟨1895946, by rfl⟩ : syracuseStep 5055857 = 3791893) B3791893
theorem B3370571 : Blo 2245435 3370571 := bstep (se 1 (by rfl) ⟨2527928, by rfl⟩ : syracuseStep 3370571 = 5055857) B5055857
theorem B2247047 : Blo 2245435 2247047 := bstep (se 1 (by rfl) ⟨1685285, by rfl⟩ : syracuseStep 2247047 = 3370571) B3370571
theorem B2527933 : Blo 2245435 2527933 := bbase (se 3 (by rfl) ⟨473987, by rfl⟩ : syracuseStep 2527933 = 947975) (by norm_num)
theorem B3370577 : Blo 2245435 3370577 := bstep (se 2 (by rfl) ⟨1263966, by rfl⟩ : syracuseStep 3370577 = 2527933) B2527933
theorem B2247051 : Blo 2245435 2247051 := bstep (se 1 (by rfl) ⟨1685288, by rfl⟩ : syracuseStep 2247051 = 3370577) B3370577
theorem B7583813 : Blo 2245435 7583813 := bbase (se 4 (by rfl) ⟨710982, by rfl⟩ : syracuseStep 7583813 = 1421965) (by norm_num)
theorem B5055875 : Blo 2245435 5055875 := bstep (se 1 (by rfl) ⟨3791906, by rfl⟩ : syracuseStep 5055875 = 7583813) B7583813
theorem B3370583 : Blo 2245435 3370583 := bstep (se 1 (by rfl) ⟨2527937, by rfl⟩ : syracuseStep 3370583 = 5055875) B5055875
theorem B2247055 : Blo 2245435 2247055 := bstep (se 1 (by rfl) ⟨1685291, by rfl⟩ : syracuseStep 2247055 = 3370583) B3370583
theorem B3370589 : Blo 2245435 3370589 := bbase (se 3 (by rfl) ⟨631985, by rfl⟩ : syracuseStep 3370589 = 1263971) (by norm_num)
theorem B2247059 : Blo 2245435 2247059 := bstep (se 1 (by rfl) ⟨1685294, by rfl⟩ : syracuseStep 2247059 = 3370589) B3370589
theorem B5055893 : Blo 2245435 5055893 := bbase (se 6 (by rfl) ⟨118497, by rfl⟩ : syracuseStep 5055893 = 236995) (by norm_num)
theorem B3370595 : Blo 2245435 3370595 := bstep (se 1 (by rfl) ⟨2527946, by rfl⟩ : syracuseStep 3370595 = 5055893) B5055893
theorem B2247063 : Blo 2245435 2247063 := bstep (se 1 (by rfl) ⟨1685297, by rfl⟩ : syracuseStep 2247063 = 3370595) B3370595
theorem B4555453 : Blo 2245435 4555453 := bbase (se 3 (by rfl) ⟨854147, by rfl⟩ : syracuseStep 4555453 = 1708295) (by norm_num)
theorem B6073937 : Blo 2245435 6073937 := bstep (se 2 (by rfl) ⟨2277726, by rfl⟩ : syracuseStep 6073937 = 4555453) B4555453
theorem B4049291 : Blo 2245435 4049291 := bstep (se 1 (by rfl) ⟨3036968, by rfl⟩ : syracuseStep 4049291 = 6073937) B6073937
theorem B10798109 : Blo 2245435 10798109 := bstep (se 3 (by rfl) ⟨2024645, by rfl⟩ : syracuseStep 10798109 = 4049291) B4049291
theorem B7198739 : Blo 2245435 7198739 := bstep (se 1 (by rfl) ⟨5399054, by rfl⟩ : syracuseStep 7198739 = 10798109) B10798109
theorem B4799159 : Blo 2245435 4799159 := bstep (se 1 (by rfl) ⟨3599369, by rfl⟩ : syracuseStep 4799159 = 7198739) B7198739
theorem B3199439 : Blo 2245435 3199439 := bstep (se 1 (by rfl) ⟨2399579, by rfl⟩ : syracuseStep 3199439 = 4799159) B4799159
theorem B8531837 : Blo 2245435 8531837 := bstep (se 3 (by rfl) ⟨1599719, by rfl⟩ : syracuseStep 8531837 = 3199439) B3199439
theorem B5687891 : Blo 2245435 5687891 := bstep (se 1 (by rfl) ⟨4265918, by rfl⟩ : syracuseStep 5687891 = 8531837) B8531837
theorem B3791927 : Blo 2245435 3791927 := bstep (se 1 (by rfl) ⟨2843945, by rfl⟩ : syracuseStep 3791927 = 5687891) B5687891
theorem B2527951 : Blo 2245435 2527951 := bstep (se 1 (by rfl) ⟨1895963, by rfl⟩ : syracuseStep 2527951 = 3791927) B3791927
theorem B3370601 : Blo 2245435 3370601 := bstep (se 2 (by rfl) ⟨1263975, by rfl⟩ : syracuseStep 3370601 = 2527951) B2527951
theorem B2247067 : Blo 2245435 2247067 := bstep (se 1 (by rfl) ⟨1685300, by rfl⟩ : syracuseStep 2247067 = 3370601) B3370601
theorem B12147893 : Blo 2245435 12147893 := bbase (se 5 (by rfl) ⟨569432, by rfl⟩ : syracuseStep 12147893 = 1138865) (by norm_num)
theorem B8098595 : Blo 2245435 8098595 := bstep (se 1 (by rfl) ⟨6073946, by rfl⟩ : syracuseStep 8098595 = 12147893) B12147893
theorem B5399063 : Blo 2245435 5399063 := bstep (se 1 (by rfl) ⟨4049297, by rfl⟩ : syracuseStep 5399063 = 8098595) B8098595
theorem B3599375 : Blo 2245435 3599375 := bstep (se 1 (by rfl) ⟨2699531, by rfl⟩ : syracuseStep 3599375 = 5399063) B5399063
theorem B9598333 : Blo 2245435 9598333 := bstep (se 3 (by rfl) ⟨1799687, by rfl⟩ : syracuseStep 9598333 = 3599375) B3599375
theorem B12797777 : Blo 2245435 12797777 := bstep (se 2 (by rfl) ⟨4799166, by rfl⟩ : syracuseStep 12797777 = 9598333) B9598333
theorem B8531851 : Blo 2245435 8531851 := bstep (se 1 (by rfl) ⟨6398888, by rfl⟩ : syracuseStep 8531851 = 12797777) B12797777
theorem B11375801 : Blo 2245435 11375801 := bstep (se 2 (by rfl) ⟨4265925, by rfl⟩ : syracuseStep 11375801 = 8531851) B8531851
theorem B7583867 : Blo 2245435 7583867 := bstep (se 1 (by rfl) ⟨5687900, by rfl⟩ : syracuseStep 7583867 = 11375801) B11375801
theorem B5055911 : Blo 2245435 5055911 := bstep (se 1 (by rfl) ⟨3791933, by rfl⟩ : syracuseStep 5055911 = 7583867) B7583867
theorem B3370607 : Blo 2245435 3370607 := bstep (se 1 (by rfl) ⟨2527955, by rfl⟩ : syracuseStep 3370607 = 5055911) B5055911
theorem B2247071 : Blo 2245435 2247071 := bstep (se 1 (by rfl) ⟨1685303, by rfl⟩ : syracuseStep 2247071 = 3370607) B3370607
theorem B3370613 : Blo 2245435 3370613 := bbase (se 5 (by rfl) ⟨157997, by rfl⟩ : syracuseStep 3370613 = 315995) (by norm_num)
theorem B2247075 : Blo 2245435 2247075 := bstep (se 1 (by rfl) ⟨1685306, by rfl⟩ : syracuseStep 2247075 = 3370613) B3370613
theorem B4265941 : Blo 2245435 4265941 := bbase (se 7 (by rfl) ⟨49991, by rfl⟩ : syracuseStep 4265941 = 99983) (by norm_num)
theorem B5687921 : Blo 2245435 5687921 := bstep (se 2 (by rfl) ⟨2132970, by rfl⟩ : syracuseStep 5687921 = 4265941) B4265941
theorem B3791947 : Blo 2245435 3791947 := bstep (se 1 (by rfl) ⟨2843960, by rfl⟩ : syracuseStep 3791947 = 5687921) B5687921
theorem B5055929 : Blo 2245435 5055929 := bstep (se 2 (by rfl) ⟨1895973, by rfl⟩ : syracuseStep 5055929 = 3791947) B3791947
theorem B3370619 : Blo 2245435 3370619 := bstep (se 1 (by rfl) ⟨2527964, by rfl⟩ : syracuseStep 3370619 = 5055929) B5055929
theorem B2247079 : Blo 2245435 2247079 := bstep (se 1 (by rfl) ⟨1685309, by rfl⟩ : syracuseStep 2247079 = 3370619) B3370619
theorem B2527969 : Blo 2245435 2527969 := bbase (se 2 (by rfl) ⟨947988, by rfl⟩ : syracuseStep 2527969 = 1895977) (by norm_num)
theorem B3370625 : Blo 2245435 3370625 := bstep (se 2 (by rfl) ⟨1263984, by rfl⟩ : syracuseStep 3370625 = 2527969) B2527969
theorem B2247083 : Blo 2245435 2247083 := bstep (se 1 (by rfl) ⟨1685312, by rfl⟩ : syracuseStep 2247083 = 3370625) B3370625
theorem B5687941 : Blo 2245435 5687941 := bbase (se 4 (by rfl) ⟨533244, by rfl⟩ : syracuseStep 5687941 = 1066489) (by norm_num)
theorem B7583921 : Blo 2245435 7583921 := bstep (se 2 (by rfl) ⟨2843970, by rfl⟩ : syracuseStep 7583921 = 5687941) B5687941
theorem B5055947 : Blo 2245435 5055947 := bstep (se 1 (by rfl) ⟨3791960, by rfl⟩ : syracuseStep 5055947 = 7583921) B7583921
theorem B3370631 : Blo 2245435 3370631 := bstep (se 1 (by rfl) ⟨2527973, by rfl⟩ : syracuseStep 3370631 = 5055947) B5055947
theorem B2247087 : Blo 2245435 2247087 := bstep (se 1 (by rfl) ⟨1685315, by rfl⟩ : syracuseStep 2247087 = 3370631) B3370631
theorem B3370637 : Blo 2245435 3370637 := bbase (se 3 (by rfl) ⟨631994, by rfl⟩ : syracuseStep 3370637 = 1263989) (by norm_num)
theorem B2247091 : Blo 2245435 2247091 := bstep (se 1 (by rfl) ⟨1685318, by rfl⟩ : syracuseStep 2247091 = 3370637) B3370637
theorem B5055965 : Blo 2245435 5055965 := bbase (se 3 (by rfl) ⟨947993, by rfl⟩ : syracuseStep 5055965 = 1895987) (by norm_num)
theorem B3370643 : Blo 2245435 3370643 := bstep (se 1 (by rfl) ⟨2527982, by rfl⟩ : syracuseStep 3370643 = 5055965) B5055965
theorem B2247095 : Blo 2245435 2247095 := bstep (se 1 (by rfl) ⟨1685321, by rfl⟩ : syracuseStep 2247095 = 3370643) B3370643
theorem B3791981 : Blo 2245435 3791981 := bbase (se 3 (by rfl) ⟨710996, by rfl⟩ : syracuseStep 3791981 = 1421993) (by norm_num)
theorem B2527987 : Blo 2245435 2527987 := bstep (se 1 (by rfl) ⟨1895990, by rfl⟩ : syracuseStep 2527987 = 3791981) B3791981
theorem B3370649 : Blo 2245435 3370649 := bstep (se 2 (by rfl) ⟨1263993, by rfl⟩ : syracuseStep 3370649 = 2527987) B2527987
theorem B2247099 : Blo 2245435 2247099 := bstep (se 1 (by rfl) ⟨1685324, by rfl⟩ : syracuseStep 2247099 = 3370649) B3370649
theorem B8098709 : Blo 2245435 8098709 := bbase (se 6 (by rfl) ⟨189813, by rfl⟩ : syracuseStep 8098709 = 379627) (by norm_num)
theorem B21596557 : Blo 2245435 21596557 := bstep (se 3 (by rfl) ⟨4049354, by rfl⟩ : syracuseStep 21596557 = 8098709) B8098709
theorem B28795409 : Blo 2245435 28795409 := bstep (se 2 (by rfl) ⟨10798278, by rfl⟩ : syracuseStep 28795409 = 21596557) B21596557
theorem B19196939 : Blo 2245435 19196939 := bstep (se 1 (by rfl) ⟨14397704, by rfl⟩ : syracuseStep 19196939 = 28795409) B28795409
theorem B12797959 : Blo 2245435 12797959 := bstep (se 1 (by rfl) ⟨9598469, by rfl⟩ : syracuseStep 12797959 = 19196939) B19196939
theorem B17063945 : Blo 2245435 17063945 := bstep (se 2 (by rfl) ⟨6398979, by rfl⟩ : syracuseStep 17063945 = 12797959) B12797959
theorem B11375963 : Blo 2245435 11375963 := bstep (se 1 (by rfl) ⟨8531972, by rfl⟩ : syracuseStep 11375963 = 17063945) B17063945
theorem B7583975 : Blo 2245435 7583975 := bstep (se 1 (by rfl) ⟨5687981, by rfl⟩ : syracuseStep 7583975 = 11375963) B11375963
theorem B5055983 : Blo 2245435 5055983 := bstep (se 1 (by rfl) ⟨3791987, by rfl⟩ : syracuseStep 5055983 = 7583975) B7583975
theorem B3370655 : Blo 2245435 3370655 := bstep (se 1 (by rfl) ⟨2527991, by rfl⟩ : syracuseStep 3370655 = 5055983) B5055983
theorem B2247103 : Blo 2245435 2247103 := bstep (se 1 (by rfl) ⟨1685327, by rfl⟩ : syracuseStep 2247103 = 3370655) B3370655
theorem B3370661 : Blo 2245435 3370661 := bbase (se 4 (by rfl) ⟨315999, by rfl⟩ : syracuseStep 3370661 = 631999) (by norm_num)
theorem B2247107 : Blo 2245435 2247107 := bstep (se 1 (by rfl) ⟨1685330, by rfl⟩ : syracuseStep 2247107 = 3370661) B3370661
theorem B2844001 : Blo 2245435 2844001 := bbase (se 2 (by rfl) ⟨1066500, by rfl⟩ : syracuseStep 2844001 = 2133001) (by norm_num)
theorem B3792001 : Blo 2245435 3792001 := bstep (se 2 (by rfl) ⟨1422000, by rfl⟩ : syracuseStep 3792001 = 2844001) B2844001
theorem B5056001 : Blo 2245435 5056001 := bstep (se 2 (by rfl) ⟨1896000, by rfl⟩ : syracuseStep 5056001 = 3792001) B3792001
theorem B3370667 : Blo 2245435 3370667 := bstep (se 1 (by rfl) ⟨2528000, by rfl⟩ : syracuseStep 3370667 = 5056001) B5056001
theorem B2247111 : Blo 2245435 2247111 := bstep (se 1 (by rfl) ⟨1685333, by rfl⟩ : syracuseStep 2247111 = 3370667) B3370667
theorem B2528005 : Blo 2245435 2528005 := bbase (se 4 (by rfl) ⟨237000, by rfl⟩ : syracuseStep 2528005 = 474001) (by norm_num)
theorem B3370673 : Blo 2245435 3370673 := bstep (se 2 (by rfl) ⟨1264002, by rfl⟩ : syracuseStep 3370673 = 2528005) B2528005
theorem B2247115 : Blo 2245435 2247115 := bstep (se 1 (by rfl) ⟨1685336, by rfl⟩ : syracuseStep 2247115 = 3370673) B3370673
theorem B3599453 : Blo 2245435 3599453 := bbase (se 3 (by rfl) ⟨674897, by rfl⟩ : syracuseStep 3599453 = 1349795) (by norm_num)
theorem B2399635 : Blo 2245435 2399635 := bstep (se 1 (by rfl) ⟨1799726, by rfl⟩ : syracuseStep 2399635 = 3599453) B3599453
theorem B3199513 : Blo 2245435 3199513 := bstep (se 2 (by rfl) ⟨1199817, by rfl⟩ : syracuseStep 3199513 = 2399635) B2399635
theorem B4266017 : Blo 2245435 4266017 := bstep (se 2 (by rfl) ⟨1599756, by rfl⟩ : syracuseStep 4266017 = 3199513) B3199513
theorem B2844011 : Blo 2245435 2844011 := bstep (se 1 (by rfl) ⟨2133008, by rfl⟩ : syracuseStep 2844011 = 4266017) B4266017
theorem B7584029 : Blo 2245435 7584029 := bstep (se 3 (by rfl) ⟨1422005, by rfl⟩ : syracuseStep 7584029 = 2844011) B2844011
theorem B5056019 : Blo 2245435 5056019 := bstep (se 1 (by rfl) ⟨3792014, by rfl⟩ : syracuseStep 5056019 = 7584029) B7584029
theorem B3370679 : Blo 2245435 3370679 := bstep (se 1 (by rfl) ⟨2528009, by rfl⟩ : syracuseStep 3370679 = 5056019) B5056019
theorem B2247119 : Blo 2245435 2247119 := bstep (se 1 (by rfl) ⟨1685339, by rfl⟩ : syracuseStep 2247119 = 3370679) B3370679
theorem B3370685 : Blo 2245435 3370685 := bbase (se 3 (by rfl) ⟨632003, by rfl⟩ : syracuseStep 3370685 = 1264007) (by norm_num)
theorem B2247123 : Blo 2245435 2247123 := bstep (se 1 (by rfl) ⟨1685342, by rfl⟩ : syracuseStep 2247123 = 3370685) B3370685
theorem B5056037 : Blo 2245435 5056037 := bbase (se 4 (by rfl) ⟨474003, by rfl⟩ : syracuseStep 5056037 = 948007) (by norm_num)
theorem B3370691 : Blo 2245435 3370691 := bstep (se 1 (by rfl) ⟨2528018, by rfl⟩ : syracuseStep 3370691 = 5056037) B5056037
theorem B2247127 : Blo 2245435 2247127 := bstep (se 1 (by rfl) ⟨1685345, by rfl⟩ : syracuseStep 2247127 = 3370691) B3370691
theorem B5688053 : Blo 2245435 5688053 := bbase (se 5 (by rfl) ⟨266627, by rfl⟩ : syracuseStep 5688053 = 533255) (by norm_num)
theorem B3792035 : Blo 2245435 3792035 := bstep (se 1 (by rfl) ⟨2844026, by rfl⟩ : syracuseStep 3792035 = 5688053) B5688053
theorem B2528023 : Blo 2245435 2528023 := bstep (se 1 (by rfl) ⟨1896017, by rfl⟩ : syracuseStep 2528023 = 3792035) B3792035
theorem B3370697 : Blo 2245435 3370697 := bstep (se 2 (by rfl) ⟨1264011, by rfl⟩ : syracuseStep 3370697 = 2528023) B2528023
theorem B2247131 : Blo 2245435 2247131 := bstep (se 1 (by rfl) ⟨1685348, by rfl⟩ : syracuseStep 2247131 = 3370697) B3370697
theorem B5765669 : Blo 2245435 5765669 := bbase (se 4 (by rfl) ⟨540531, by rfl⟩ : syracuseStep 5765669 = 1081063) (by norm_num)
theorem B3843779 : Blo 2245435 3843779 := bstep (se 1 (by rfl) ⟨2882834, by rfl⟩ : syracuseStep 3843779 = 5765669) B5765669
theorem B10250077 : Blo 2245435 10250077 := bstep (se 3 (by rfl) ⟨1921889, by rfl⟩ : syracuseStep 10250077 = 3843779) B3843779
theorem B13666769 : Blo 2245435 13666769 := bstep (se 2 (by rfl) ⟨5125038, by rfl⟩ : syracuseStep 13666769 = 10250077) B10250077
theorem B9111179 : Blo 2245435 9111179 := bstep (se 1 (by rfl) ⟨6833384, by rfl⟩ : syracuseStep 9111179 = 13666769) B13666769
theorem B6074119 : Blo 2245435 6074119 := bstep (se 1 (by rfl) ⟨4555589, by rfl⟩ : syracuseStep 6074119 = 9111179) B9111179
theorem B32395301 : Blo 2245435 32395301 := bstep (se 4 (by rfl) ⟨3037059, by rfl⟩ : syracuseStep 32395301 = 6074119) B6074119
theorem B21596867 : Blo 2245435 21596867 := bstep (se 1 (by rfl) ⟨16197650, by rfl⟩ : syracuseStep 21596867 = 32395301) B32395301
theorem B14397911 : Blo 2245435 14397911 := bstep (se 1 (by rfl) ⟨10798433, by rfl⟩ : syracuseStep 14397911 = 21596867) B21596867
theorem B9598607 : Blo 2245435 9598607 := bstep (se 1 (by rfl) ⟨7198955, by rfl⟩ : syracuseStep 9598607 = 14397911) B14397911
theorem B6399071 : Blo 2245435 6399071 := bstep (se 1 (by rfl) ⟨4799303, by rfl⟩ : syracuseStep 6399071 = 9598607) B9598607
theorem B4266047 : Blo 2245435 4266047 := bstep (se 1 (by rfl) ⟨3199535, by rfl⟩ : syracuseStep 4266047 = 6399071) B6399071
theorem B11376125 : Blo 2245435 11376125 := bstep (se 3 (by rfl) ⟨2133023, by rfl⟩ : syracuseStep 11376125 = 4266047) B4266047
theorem B7584083 : Blo 2245435 7584083 := bstep (se 1 (by rfl) ⟨5688062, by rfl⟩ : syracuseStep 7584083 = 11376125) B11376125
theorem B5056055 : Blo 2245435 5056055 := bstep (se 1 (by rfl) ⟨3792041, by rfl⟩ : syracuseStep 5056055 = 7584083) B7584083
theorem B3370703 : Blo 2245435 3370703 := bstep (se 1 (by rfl) ⟨2528027, by rfl⟩ : syracuseStep 3370703 = 5056055) B5056055
theorem B2247135 : Blo 2245435 2247135 := bstep (se 1 (by rfl) ⟨1685351, by rfl⟩ : syracuseStep 2247135 = 3370703) B3370703
theorem B3370709 : Blo 2245435 3370709 := bbase (se 7 (by rfl) ⟨39500, by rfl⟩ : syracuseStep 3370709 = 79001) (by norm_num)
theorem B2247139 : Blo 2245435 2247139 := bstep (se 1 (by rfl) ⟨1685354, by rfl⟩ : syracuseStep 2247139 = 3370709) B3370709
theorem B5399237 : Blo 2245435 5399237 := bbase (se 4 (by rfl) ⟨506178, by rfl⟩ : syracuseStep 5399237 = 1012357) (by norm_num)
theorem B3599491 : Blo 2245435 3599491 := bstep (se 1 (by rfl) ⟨2699618, by rfl⟩ : syracuseStep 3599491 = 5399237) B5399237
theorem B4799321 : Blo 2245435 4799321 := bstep (se 2 (by rfl) ⟨1799745, by rfl⟩ : syracuseStep 4799321 = 3599491) B3599491
theorem B3199547 : Blo 2245435 3199547 := bstep (se 1 (by rfl) ⟨2399660, by rfl⟩ : syracuseStep 3199547 = 4799321) B4799321
theorem B8532125 : Blo 2245435 8532125 := bstep (se 3 (by rfl) ⟨1599773, by rfl⟩ : syracuseStep 8532125 = 3199547) B3199547
theorem B5688083 : Blo 2245435 5688083 := bstep (se 1 (by rfl) ⟨4266062, by rfl⟩ : syracuseStep 5688083 = 8532125) B8532125
theorem B3792055 : Blo 2245435 3792055 := bstep (se 1 (by rfl) ⟨2844041, by rfl⟩ : syracuseStep 3792055 = 5688083) B5688083
theorem B5056073 : Blo 2245435 5056073 := bstep (se 2 (by rfl) ⟨1896027, by rfl⟩ : syracuseStep 5056073 = 3792055) B3792055
theorem B3370715 : Blo 2245435 3370715 := bstep (se 1 (by rfl) ⟨2528036, by rfl⟩ : syracuseStep 3370715 = 5056073) B5056073
theorem B2247143 : Blo 2245435 2247143 := bstep (se 1 (by rfl) ⟨1685357, by rfl⟩ : syracuseStep 2247143 = 3370715) B3370715
theorem B2528041 : Blo 2245435 2528041 := bbase (se 2 (by rfl) ⟨948015, by rfl⟩ : syracuseStep 2528041 = 1896031) (by norm_num)
theorem B3370721 : Blo 2245435 3370721 := bstep (se 2 (by rfl) ⟨1264020, by rfl⟩ : syracuseStep 3370721 = 2528041) B2528041
theorem B2247147 : Blo 2245435 2247147 := bstep (se 1 (by rfl) ⟨1685360, by rfl⟩ : syracuseStep 2247147 = 3370721) B3370721
theorem B3416717 : Blo 2245435 3416717 := bbase (se 3 (by rfl) ⟨640634, by rfl⟩ : syracuseStep 3416717 = 1281269) (by norm_num)
theorem B2277811 : Blo 2245435 2277811 := bstep (se 1 (by rfl) ⟨1708358, by rfl⟩ : syracuseStep 2277811 = 3416717) B3416717
theorem B12148325 : Blo 2245435 12148325 := bstep (se 4 (by rfl) ⟨1138905, by rfl⟩ : syracuseStep 12148325 = 2277811) B2277811
theorem B8098883 : Blo 2245435 8098883 := bstep (se 1 (by rfl) ⟨6074162, by rfl⟩ : syracuseStep 8098883 = 12148325) B12148325
theorem B5399255 : Blo 2245435 5399255 := bstep (se 1 (by rfl) ⟨4049441, by rfl⟩ : syracuseStep 5399255 = 8098883) B8098883
theorem B14398013 : Blo 2245435 14398013 := bstep (se 3 (by rfl) ⟨2699627, by rfl⟩ : syracuseStep 14398013 = 5399255) B5399255
theorem B9598675 : Blo 2245435 9598675 := bstep (se 1 (by rfl) ⟨7199006, by rfl⟩ : syracuseStep 9598675 = 14398013) B14398013
theorem B12798233 : Blo 2245435 12798233 := bstep (se 2 (by rfl) ⟨4799337, by rfl⟩ : syracuseStep 12798233 = 9598675) B9598675
theorem B8532155 : Blo 2245435 8532155 := bstep (se 1 (by rfl) ⟨6399116, by rfl⟩ : syracuseStep 8532155 = 12798233) B12798233
theorem B5688103 : Blo 2245435 5688103 := bstep (se 1 (by rfl) ⟨4266077, by rfl⟩ : syracuseStep 5688103 = 8532155) B8532155
theorem B7584137 : Blo 2245435 7584137 := bstep (se 2 (by rfl) ⟨2844051, by rfl⟩ : syracuseStep 7584137 = 5688103) B5688103
theorem B5056091 : Blo 2245435 5056091 := bstep (se 1 (by rfl) ⟨3792068, by rfl⟩ : syracuseStep 5056091 = 7584137) B7584137
theorem B3370727 : Blo 2245435 3370727 := bstep (se 1 (by rfl) ⟨2528045, by rfl⟩ : syracuseStep 3370727 = 5056091) B5056091
theorem B2247151 : Blo 2245435 2247151 := bstep (se 1 (by rfl) ⟨1685363, by rfl⟩ : syracuseStep 2247151 = 3370727) B3370727
theorem B3370733 : Blo 2245435 3370733 := bbase (se 3 (by rfl) ⟨632012, by rfl⟩ : syracuseStep 3370733 = 1264025) (by norm_num)
theorem B2247155 : Blo 2245435 2247155 := bstep (se 1 (by rfl) ⟨1685366, by rfl⟩ : syracuseStep 2247155 = 3370733) B3370733
theorem B5056109 : Blo 2245435 5056109 := bbase (se 3 (by rfl) ⟨948020, by rfl⟩ : syracuseStep 5056109 = 1896041) (by norm_num)
theorem B3370739 : Blo 2245435 3370739 := bstep (se 1 (by rfl) ⟨2528054, by rfl⟩ : syracuseStep 3370739 = 5056109) B5056109
theorem B2247159 : Blo 2245435 2247159 := bstep (se 1 (by rfl) ⟨1685369, by rfl⟩ : syracuseStep 2247159 = 3370739) B3370739
theorem B4266101 : Blo 2245435 4266101 := bbase (se 5 (by rfl) ⟨199973, by rfl⟩ : syracuseStep 4266101 = 399947) (by norm_num)
theorem B2844067 : Blo 2245435 2844067 := bstep (se 1 (by rfl) ⟨2133050, by rfl⟩ : syracuseStep 2844067 = 4266101) B4266101
theorem B3792089 : Blo 2245435 3792089 := bstep (se 2 (by rfl) ⟨1422033, by rfl⟩ : syracuseStep 3792089 = 2844067) B2844067
theorem B2528059 : Blo 2245435 2528059 := bstep (se 1 (by rfl) ⟨1896044, by rfl⟩ : syracuseStep 2528059 = 3792089) B3792089
theorem B3370745 : Blo 2245435 3370745 := bstep (se 2 (by rfl) ⟨1264029, by rfl⟩ : syracuseStep 3370745 = 2528059) B2528059
theorem B2247163 : Blo 2245435 2247163 := bstep (se 1 (by rfl) ⟨1685372, by rfl⟩ : syracuseStep 2247163 = 3370745) B3370745
theorem B5765749 : Blo 2245435 5765749 := bbase (se 5 (by rfl) ⟨270269, by rfl⟩ : syracuseStep 5765749 = 540539) (by norm_num)
theorem B30750661 : Blo 2245435 30750661 := bstep (se 4 (by rfl) ⟨2882874, by rfl⟩ : syracuseStep 30750661 = 5765749) B5765749
theorem B164003525 : Blo 2245435 164003525 := bstep (se 4 (by rfl) ⟨15375330, by rfl⟩ : syracuseStep 164003525 = 30750661) B30750661
theorem B109335683 : Blo 2245435 109335683 := bstep (se 1 (by rfl) ⟨82001762, by rfl⟩ : syracuseStep 109335683 = 164003525) B164003525
theorem B72890455 : Blo 2245435 72890455 := bstep (se 1 (by rfl) ⟨54667841, by rfl⟩ : syracuseStep 72890455 = 109335683) B109335683
theorem B97187273 : Blo 2245435 97187273 := bstep (se 2 (by rfl) ⟨36445227, by rfl⟩ : syracuseStep 97187273 = 72890455) B72890455
theorem B64791515 : Blo 2245435 64791515 := bstep (se 1 (by rfl) ⟨48593636, by rfl⟩ : syracuseStep 64791515 = 97187273) B97187273
theorem B43194343 : Blo 2245435 43194343 := bstep (se 1 (by rfl) ⟨32395757, by rfl⟩ : syracuseStep 43194343 = 64791515) B64791515
theorem B57592457 : Blo 2245435 57592457 := bstep (se 2 (by rfl) ⟨21597171, by rfl⟩ : syracuseStep 57592457 = 43194343) B43194343
theorem B38394971 : Blo 2245435 38394971 := bstep (se 1 (by rfl) ⟨28796228, by rfl⟩ : syracuseStep 38394971 = 57592457) B57592457
theorem B25596647 : Blo 2245435 25596647 := bstep (se 1 (by rfl) ⟨19197485, by rfl⟩ : syracuseStep 25596647 = 38394971) B38394971
theorem B17064431 : Blo 2245435 17064431 := bstep (se 1 (by rfl) ⟨12798323, by rfl⟩ : syracuseStep 17064431 = 25596647) B25596647
theorem B11376287 : Blo 2245435 11376287 := bstep (se 1 (by rfl) ⟨8532215, by rfl⟩ : syracuseStep 11376287 = 17064431) B17064431
theorem B7584191 : Blo 2245435 7584191 := bstep (se 1 (by rfl) ⟨5688143, by rfl⟩ : syracuseStep 7584191 = 11376287) B11376287
theorem B5056127 : Blo 2245435 5056127 := bstep (se 1 (by rfl) ⟨3792095, by rfl⟩ : syracuseStep 5056127 = 7584191) B7584191
theorem B3370751 : Blo 2245435 3370751 := bstep (se 1 (by rfl) ⟨2528063, by rfl⟩ : syracuseStep 3370751 = 5056127) B5056127
theorem B2247167 : Blo 2245435 2247167 := bstep (se 1 (by rfl) ⟨1685375, by rfl⟩ : syracuseStep 2247167 = 3370751) B3370751
theorem B3370757 : Blo 2245435 3370757 := bbase (se 4 (by rfl) ⟨316008, by rfl⟩ : syracuseStep 3370757 = 632017) (by norm_num)
theorem B2247171 : Blo 2245435 2247171 := bstep (se 1 (by rfl) ⟨1685378, by rfl⟩ : syracuseStep 2247171 = 3370757) B3370757
theorem B3792109 : Blo 2245435 3792109 := bbase (se 3 (by rfl) ⟨711020, by rfl⟩ : syracuseStep 3792109 = 1422041) (by norm_num)
theorem B5056145 : Blo 2245435 5056145 := bstep (se 2 (by rfl) ⟨1896054, by rfl⟩ : syracuseStep 5056145 = 3792109) B3792109
theorem B3370763 : Blo 2245435 3370763 := bstep (se 1 (by rfl) ⟨2528072, by rfl⟩ : syracuseStep 3370763 = 5056145) B5056145
theorem B2247175 : Blo 2245435 2247175 := bstep (se 1 (by rfl) ⟨1685381, by rfl⟩ : syracuseStep 2247175 = 3370763) B3370763
theorem B2528077 : Blo 2245435 2528077 := bbase (se 3 (by rfl) ⟨474014, by rfl⟩ : syracuseStep 2528077 = 948029) (by norm_num)
theorem B3370769 : Blo 2245435 3370769 := bstep (se 2 (by rfl) ⟨1264038, by rfl⟩ : syracuseStep 3370769 = 2528077) B2528077
theorem B2247179 : Blo 2245435 2247179 := bstep (se 1 (by rfl) ⟨1685384, by rfl⟩ : syracuseStep 2247179 = 3370769) B3370769
theorem B7584245 : Blo 2245435 7584245 := bbase (se 5 (by rfl) ⟨355511, by rfl⟩ : syracuseStep 7584245 = 711023) (by norm_num)
theorem B5056163 : Blo 2245435 5056163 := bstep (se 1 (by rfl) ⟨3792122, by rfl⟩ : syracuseStep 5056163 = 7584245) B7584245
theorem B3370775 : Blo 2245435 3370775 := bstep (se 1 (by rfl) ⟨2528081, by rfl⟩ : syracuseStep 3370775 = 5056163) B5056163
theorem B2247183 : Blo 2245435 2247183 := bstep (se 1 (by rfl) ⟨1685387, by rfl⟩ : syracuseStep 2247183 = 3370775) B3370775
theorem B3370781 : Blo 2245435 3370781 := bbase (se 3 (by rfl) ⟨632021, by rfl⟩ : syracuseStep 3370781 = 1264043) (by norm_num)
theorem B2247187 : Blo 2245435 2247187 := bstep (se 1 (by rfl) ⟨1685390, by rfl⟩ : syracuseStep 2247187 = 3370781) B3370781
theorem B5056181 : Blo 2245435 5056181 := bbase (se 5 (by rfl) ⟨237008, by rfl⟩ : syracuseStep 5056181 = 474017) (by norm_num)
theorem B3370787 : Blo 2245435 3370787 := bstep (se 1 (by rfl) ⟨2528090, by rfl⟩ : syracuseStep 3370787 = 5056181) B5056181
theorem B2247191 : Blo 2245435 2247191 := bstep (se 1 (by rfl) ⟨1685393, by rfl⟩ : syracuseStep 2247191 = 3370787) B3370787
theorem B12798485 : Blo 2245435 12798485 := bbase (se 6 (by rfl) ⟨299964, by rfl⟩ : syracuseStep 12798485 = 599929) (by norm_num)
theorem B8532323 : Blo 2245435 8532323 := bstep (se 1 (by rfl) ⟨6399242, by rfl⟩ : syracuseStep 8532323 = 12798485) B12798485
theorem B5688215 : Blo 2245435 5688215 := bstep (se 1 (by rfl) ⟨4266161, by rfl⟩ : syracuseStep 5688215 = 8532323) B8532323
theorem B3792143 : Blo 2245435 3792143 := bstep (se 1 (by rfl) ⟨2844107, by rfl⟩ : syracuseStep 3792143 = 5688215) B5688215
theorem B2528095 : Blo 2245435 2528095 := bstep (se 1 (by rfl) ⟨1896071, by rfl⟩ : syracuseStep 2528095 = 3792143) B3792143
theorem B3370793 : Blo 2245435 3370793 := bstep (se 2 (by rfl) ⟨1264047, by rfl⟩ : syracuseStep 3370793 = 2528095) B2528095
theorem B2247195 : Blo 2245435 2247195 := bstep (se 1 (by rfl) ⟨1685396, by rfl⟩ : syracuseStep 2247195 = 3370793) B3370793
theorem B6399253 : Blo 2245435 6399253 := bbase (se 6 (by rfl) ⟨149982, by rfl⟩ : syracuseStep 6399253 = 299965) (by norm_num)
theorem B8532337 : Blo 2245435 8532337 := bstep (se 2 (by rfl) ⟨3199626, by rfl⟩ : syracuseStep 8532337 = 6399253) B6399253
theorem B11376449 : Blo 2245435 11376449 := bstep (se 2 (by rfl) ⟨4266168, by rfl⟩ : syracuseStep 11376449 = 8532337) B8532337
theorem B7584299 : Blo 2245435 7584299 := bstep (se 1 (by rfl) ⟨5688224, by rfl⟩ : syracuseStep 7584299 = 11376449) B11376449
theorem B5056199 : Blo 2245435 5056199 := bstep (se 1 (by rfl) ⟨3792149, by rfl⟩ : syracuseStep 5056199 = 7584299) B7584299
theorem B3370799 : Blo 2245435 3370799 := bstep (se 1 (by rfl) ⟨2528099, by rfl⟩ : syracuseStep 3370799 = 5056199) B5056199
theorem B2247199 : Blo 2245435 2247199 := bstep (se 1 (by rfl) ⟨1685399, by rfl⟩ : syracuseStep 2247199 = 3370799) B3370799
theorem B3370805 : Blo 2245435 3370805 := bbase (se 5 (by rfl) ⟨158006, by rfl⟩ : syracuseStep 3370805 = 316013) (by norm_num)
theorem B2247203 : Blo 2245435 2247203 := bstep (se 1 (by rfl) ⟨1685402, by rfl⟩ : syracuseStep 2247203 = 3370805) B3370805
theorem B5688245 : Blo 2245435 5688245 := bbase (se 5 (by rfl) ⟨266636, by rfl⟩ : syracuseStep 5688245 = 533273) (by norm_num)
theorem B3792163 : Blo 2245435 3792163 := bstep (se 1 (by rfl) ⟨2844122, by rfl⟩ : syracuseStep 3792163 = 5688245) B5688245
theorem B5056217 : Blo 2245435 5056217 := bstep (se 2 (by rfl) ⟨1896081, by rfl⟩ : syracuseStep 5056217 = 3792163) B3792163
theorem B3370811 : Blo 2245435 3370811 := bstep (se 1 (by rfl) ⟨2528108, by rfl⟩ : syracuseStep 3370811 = 5056217) B5056217
theorem B2247207 : Blo 2245435 2247207 := bstep (se 1 (by rfl) ⟨1685405, by rfl⟩ : syracuseStep 2247207 = 3370811) B3370811
theorem B2528113 : Blo 2245435 2528113 := bbase (se 2 (by rfl) ⟨948042, by rfl⟩ : syracuseStep 2528113 = 1896085) (by norm_num)
theorem B3370817 : Blo 2245435 3370817 := bstep (se 2 (by rfl) ⟨1264056, by rfl⟩ : syracuseStep 3370817 = 2528113) B2528113
theorem B2247211 : Blo 2245435 2247211 := bstep (se 1 (by rfl) ⟨1685408, by rfl⟩ : syracuseStep 2247211 = 3370817) B3370817
theorem B9598949 : Blo 2245435 9598949 := bbase (se 4 (by rfl) ⟨899901, by rfl⟩ : syracuseStep 9598949 = 1799803) (by norm_num)
theorem B6399299 : Blo 2245435 6399299 := bstep (se 1 (by rfl) ⟨4799474, by rfl⟩ : syracuseStep 6399299 = 9598949) B9598949
theorem B4266199 : Blo 2245435 4266199 := bstep (se 1 (by rfl) ⟨3199649, by rfl⟩ : syracuseStep 4266199 = 6399299) B6399299
theorem B5688265 : Blo 2245435 5688265 := bstep (se 2 (by rfl) ⟨2133099, by rfl⟩ : syracuseStep 5688265 = 4266199) B4266199
theorem B7584353 : Blo 2245435 7584353 := bstep (se 2 (by rfl) ⟨2844132, by rfl⟩ : syracuseStep 7584353 = 5688265) B5688265
theorem B5056235 : Blo 2245435 5056235 := bstep (se 1 (by rfl) ⟨3792176, by rfl⟩ : syracuseStep 5056235 = 7584353) B7584353
theorem B3370823 : Blo 2245435 3370823 := bstep (se 1 (by rfl) ⟨2528117, by rfl⟩ : syracuseStep 3370823 = 5056235) B5056235
theorem B2247215 : Blo 2245435 2247215 := bstep (se 1 (by rfl) ⟨1685411, by rfl⟩ : syracuseStep 2247215 = 3370823) B3370823
theorem B3370829 : Blo 2245435 3370829 := bbase (se 3 (by rfl) ⟨632030, by rfl⟩ : syracuseStep 3370829 = 1264061) (by norm_num)
theorem B2247219 : Blo 2245435 2247219 := bstep (se 1 (by rfl) ⟨1685414, by rfl⟩ : syracuseStep 2247219 = 3370829) B3370829
theorem B5056253 : Blo 2245435 5056253 := bbase (se 3 (by rfl) ⟨948047, by rfl⟩ : syracuseStep 5056253 = 1896095) (by norm_num)
theorem B3370835 : Blo 2245435 3370835 := bstep (se 1 (by rfl) ⟨2528126, by rfl⟩ : syracuseStep 3370835 = 5056253) B5056253
theorem B2247223 : Blo 2245435 2247223 := bstep (se 1 (by rfl) ⟨1685417, by rfl⟩ : syracuseStep 2247223 = 3370835) B3370835
theorem B3792197 : Blo 2245435 3792197 := bbase (se 4 (by rfl) ⟨355518, by rfl⟩ : syracuseStep 3792197 = 711037) (by norm_num)
theorem B2528131 : Blo 2245435 2528131 := bstep (se 1 (by rfl) ⟨1896098, by rfl⟩ : syracuseStep 2528131 = 3792197) B3792197
theorem B3370841 : Blo 2245435 3370841 := bstep (se 2 (by rfl) ⟨1264065, by rfl⟩ : syracuseStep 3370841 = 2528131) B2528131
theorem B2247227 : Blo 2245435 2247227 := bstep (se 1 (by rfl) ⟨1685420, by rfl⟩ : syracuseStep 2247227 = 3370841) B3370841
theorem B17064917 : Blo 2245435 17064917 := bbase (se 7 (by rfl) ⟨199979, by rfl⟩ : syracuseStep 17064917 = 399959) (by norm_num)
theorem B11376611 : Blo 2245435 11376611 := bstep (se 1 (by rfl) ⟨8532458, by rfl⟩ : syracuseStep 11376611 = 17064917) B17064917
theorem B7584407 : Blo 2245435 7584407 := bstep (se 1 (by rfl) ⟨5688305, by rfl⟩ : syracuseStep 7584407 = 11376611) B11376611
theorem B5056271 : Blo 2245435 5056271 := bstep (se 1 (by rfl) ⟨3792203, by rfl⟩ : syracuseStep 5056271 = 7584407) B7584407
theorem B3370847 : Blo 2245435 3370847 := bstep (se 1 (by rfl) ⟨2528135, by rfl⟩ : syracuseStep 3370847 = 5056271) B5056271
theorem B2247231 : Blo 2245435 2247231 := bstep (se 1 (by rfl) ⟨1685423, by rfl⟩ : syracuseStep 2247231 = 3370847) B3370847
theorem B3370853 : Blo 2245435 3370853 := bbase (se 4 (by rfl) ⟨316017, by rfl⟩ : syracuseStep 3370853 = 632035) (by norm_num)
theorem B2247235 : Blo 2245435 2247235 := bstep (se 1 (by rfl) ⟨1685426, by rfl⟩ : syracuseStep 2247235 = 3370853) B3370853
theorem B4266245 : Blo 2245435 4266245 := bbase (se 4 (by rfl) ⟨399960, by rfl⟩ : syracuseStep 4266245 = 799921) (by norm_num)
theorem B2844163 : Blo 2245435 2844163 := bstep (se 1 (by rfl) ⟨2133122, by rfl⟩ : syracuseStep 2844163 = 4266245) B4266245
theorem B3792217 : Blo 2245435 3792217 := bstep (se 2 (by rfl) ⟨1422081, by rfl⟩ : syracuseStep 3792217 = 2844163) B2844163
theorem B5056289 : Blo 2245435 5056289 := bstep (se 2 (by rfl) ⟨1896108, by rfl⟩ : syracuseStep 5056289 = 3792217) B3792217
theorem B3370859 : Blo 2245435 3370859 := bstep (se 1 (by rfl) ⟨2528144, by rfl⟩ : syracuseStep 3370859 = 5056289) B5056289
theorem B2247239 : Blo 2245435 2247239 := bstep (se 1 (by rfl) ⟨1685429, by rfl⟩ : syracuseStep 2247239 = 3370859) B3370859
theorem B2528149 : Blo 2245435 2528149 := bbase (se 6 (by rfl) ⟨59253, by rfl⟩ : syracuseStep 2528149 = 118507) (by norm_num)
theorem B3370865 : Blo 2245435 3370865 := bstep (se 2 (by rfl) ⟨1264074, by rfl⟩ : syracuseStep 3370865 = 2528149) B2528149
theorem B2247243 : Blo 2245435 2247243 := bstep (se 1 (by rfl) ⟨1685432, by rfl⟩ : syracuseStep 2247243 = 3370865) B3370865
theorem B2844173 : Blo 2245435 2844173 := bbase (se 3 (by rfl) ⟨533282, by rfl⟩ : syracuseStep 2844173 = 1066565) (by norm_num)
theorem B7584461 : Blo 2245435 7584461 := bstep (se 3 (by rfl) ⟨1422086, by rfl⟩ : syracuseStep 7584461 = 2844173) B2844173
theorem B5056307 : Blo 2245435 5056307 := bstep (se 1 (by rfl) ⟨3792230, by rfl⟩ : syracuseStep 5056307 = 7584461) B7584461
theorem B3370871 : Blo 2245435 3370871 := bstep (se 1 (by rfl) ⟨2528153, by rfl⟩ : syracuseStep 3370871 = 5056307) B5056307
theorem B2247247 : Blo 2245435 2247247 := bstep (se 1 (by rfl) ⟨1685435, by rfl⟩ : syracuseStep 2247247 = 3370871) B3370871
theorem B3370877 : Blo 2245435 3370877 := bbase (se 3 (by rfl) ⟨632039, by rfl⟩ : syracuseStep 3370877 = 1264079) (by norm_num)
theorem B2247251 : Blo 2245435 2247251 := bstep (se 1 (by rfl) ⟨1685438, by rfl⟩ : syracuseStep 2247251 = 3370877) B3370877
theorem B5056325 : Blo 2245435 5056325 := bbase (se 4 (by rfl) ⟨474030, by rfl⟩ : syracuseStep 5056325 = 948061) (by norm_num)
theorem B3370883 : Blo 2245435 3370883 := bstep (se 1 (by rfl) ⟨2528162, by rfl⟩ : syracuseStep 3370883 = 5056325) B5056325
theorem B2247255 : Blo 2245435 2247255 := bstep (se 1 (by rfl) ⟨1685441, by rfl⟩ : syracuseStep 2247255 = 3370883) B3370883
theorem B3599677 : Blo 2245435 3599677 := bbase (se 3 (by rfl) ⟨674939, by rfl⟩ : syracuseStep 3599677 = 1349879) (by norm_num)
theorem B4799569 : Blo 2245435 4799569 := bstep (se 2 (by rfl) ⟨1799838, by rfl⟩ : syracuseStep 4799569 = 3599677) B3599677
theorem B6399425 : Blo 2245435 6399425 := bstep (se 2 (by rfl) ⟨2399784, by rfl⟩ : syracuseStep 6399425 = 4799569) B4799569
theorem B4266283 : Blo 2245435 4266283 := bstep (se 1 (by rfl) ⟨3199712, by rfl⟩ : syracuseStep 4266283 = 6399425) B6399425
theorem B5688377 : Blo 2245435 5688377 := bstep (se 2 (by rfl) ⟨2133141, by rfl⟩ : syracuseStep 5688377 = 4266283) B4266283
theorem B3792251 : Blo 2245435 3792251 := bstep (se 1 (by rfl) ⟨2844188, by rfl⟩ : syracuseStep 3792251 = 5688377) B5688377
theorem B2528167 : Blo 2245435 2528167 := bstep (se 1 (by rfl) ⟨1896125, by rfl⟩ : syracuseStep 2528167 = 3792251) B3792251
theorem B3370889 : Blo 2245435 3370889 := bstep (se 2 (by rfl) ⟨1264083, by rfl⟩ : syracuseStep 3370889 = 2528167) B2528167
theorem B2247259 : Blo 2245435 2247259 := bstep (se 1 (by rfl) ⟨1685444, by rfl⟩ : syracuseStep 2247259 = 3370889) B3370889
theorem B11376773 : Blo 2245435 11376773 := bbase (se 4 (by rfl) ⟨1066572, by rfl⟩ : syracuseStep 11376773 = 2133145) (by norm_num)
theorem B7584515 : Blo 2245435 7584515 := bstep (se 1 (by rfl) ⟨5688386, by rfl⟩ : syracuseStep 7584515 = 11376773) B11376773
theorem B5056343 : Blo 2245435 5056343 := bstep (se 1 (by rfl) ⟨3792257, by rfl⟩ : syracuseStep 5056343 = 7584515) B7584515
theorem B3370895 : Blo 2245435 3370895 := bstep (se 1 (by rfl) ⟨2528171, by rfl⟩ : syracuseStep 3370895 = 5056343) B5056343
theorem B2247263 : Blo 2245435 2247263 := bstep (se 1 (by rfl) ⟨1685447, by rfl⟩ : syracuseStep 2247263 = 3370895) B3370895
theorem B3370901 : Blo 2245435 3370901 := bbase (se 6 (by rfl) ⟨79005, by rfl⟩ : syracuseStep 3370901 = 158011) (by norm_num)
theorem B2247267 : Blo 2245435 2247267 := bstep (se 1 (by rfl) ⟨1685450, by rfl⟩ : syracuseStep 2247267 = 3370901) B3370901
theorem B2399797 : Blo 2245435 2399797 := bbase (se 5 (by rfl) ⟨112490, by rfl⟩ : syracuseStep 2399797 = 224981) (by norm_num)
theorem B12798917 : Blo 2245435 12798917 := bstep (se 4 (by rfl) ⟨1199898, by rfl⟩ : syracuseStep 12798917 = 2399797) B2399797
theorem B8532611 : Blo 2245435 8532611 := bstep (se 1 (by rfl) ⟨6399458, by rfl⟩ : syracuseStep 8532611 = 12798917) B12798917
theorem B5688407 : Blo 2245435 5688407 := bstep (se 1 (by rfl) ⟨4266305, by rfl⟩ : syracuseStep 5688407 = 8532611) B8532611
theorem B3792271 : Blo 2245435 3792271 := bstep (se 1 (by rfl) ⟨2844203, by rfl⟩ : syracuseStep 3792271 = 5688407) B5688407
theorem B5056361 : Blo 2245435 5056361 := bstep (se 2 (by rfl) ⟨1896135, by rfl⟩ : syracuseStep 5056361 = 3792271) B3792271
theorem B3370907 : Blo 2245435 3370907 := bstep (se 1 (by rfl) ⟨2528180, by rfl⟩ : syracuseStep 3370907 = 5056361) B5056361
theorem B2247271 : Blo 2245435 2247271 := bstep (se 1 (by rfl) ⟨1685453, by rfl⟩ : syracuseStep 2247271 = 3370907) B3370907
theorem B2528185 : Blo 2245435 2528185 := bbase (se 2 (by rfl) ⟨948069, by rfl⟩ : syracuseStep 2528185 = 1896139) (by norm_num)
theorem B3370913 : Blo 2245435 3370913 := bstep (se 2 (by rfl) ⟨1264092, by rfl⟩ : syracuseStep 3370913 = 2528185) B2528185
theorem B2247275 : Blo 2245435 2247275 := bstep (se 1 (by rfl) ⟨1685456, by rfl⟩ : syracuseStep 2247275 = 3370913) B3370913
theorem B2277941 : Blo 2245435 2277941 := bbase (se 5 (by rfl) ⟨106778, by rfl⟩ : syracuseStep 2277941 = 213557) (by norm_num)
theorem B6074509 : Blo 2245435 6074509 := bstep (se 3 (by rfl) ⟨1138970, by rfl⟩ : syracuseStep 6074509 = 2277941) B2277941
theorem B8099345 : Blo 2245435 8099345 := bstep (se 2 (by rfl) ⟨3037254, by rfl⟩ : syracuseStep 8099345 = 6074509) B6074509
theorem B5399563 : Blo 2245435 5399563 := bstep (se 1 (by rfl) ⟨4049672, by rfl⟩ : syracuseStep 5399563 = 8099345) B8099345
theorem B7199417 : Blo 2245435 7199417 := bstep (se 2 (by rfl) ⟨2699781, by rfl⟩ : syracuseStep 7199417 = 5399563) B5399563
theorem B4799611 : Blo 2245435 4799611 := bstep (se 1 (by rfl) ⟨3599708, by rfl⟩ : syracuseStep 4799611 = 7199417) B7199417
theorem B6399481 : Blo 2245435 6399481 := bstep (se 2 (by rfl) ⟨2399805, by rfl⟩ : syracuseStep 6399481 = 4799611) B4799611
theorem B8532641 : Blo 2245435 8532641 := bstep (se 2 (by rfl) ⟨3199740, by rfl⟩ : syracuseStep 8532641 = 6399481) B6399481
theorem B5688427 : Blo 2245435 5688427 := bstep (se 1 (by rfl) ⟨4266320, by rfl⟩ : syracuseStep 5688427 = 8532641) B8532641
theorem B7584569 : Blo 2245435 7584569 := bstep (se 2 (by rfl) ⟨2844213, by rfl⟩ : syracuseStep 7584569 = 5688427) B5688427
theorem B5056379 : Blo 2245435 5056379 := bstep (se 1 (by rfl) ⟨3792284, by rfl⟩ : syracuseStep 5056379 = 7584569) B7584569
theorem B3370919 : Blo 2245435 3370919 := bstep (se 1 (by rfl) ⟨2528189, by rfl⟩ : syracuseStep 3370919 = 5056379) B5056379
theorem B2247279 : Blo 2245435 2247279 := bstep (se 1 (by rfl) ⟨1685459, by rfl⟩ : syracuseStep 2247279 = 3370919) B3370919
theorem B3370925 : Blo 2245435 3370925 := bbase (se 3 (by rfl) ⟨632048, by rfl⟩ : syracuseStep 3370925 = 1264097) (by norm_num)
theorem B2247283 : Blo 2245435 2247283 := bstep (se 1 (by rfl) ⟨1685462, by rfl⟩ : syracuseStep 2247283 = 3370925) B3370925
theorem B5056397 : Blo 2245435 5056397 := bbase (se 3 (by rfl) ⟨948074, by rfl⟩ : syracuseStep 5056397 = 1896149) (by norm_num)
theorem B3370931 : Blo 2245435 3370931 := bstep (se 1 (by rfl) ⟨2528198, by rfl⟩ : syracuseStep 3370931 = 5056397) B5056397
theorem B2247287 : Blo 2245435 2247287 := bstep (se 1 (by rfl) ⟨1685465, by rfl⟩ : syracuseStep 2247287 = 3370931) B3370931
theorem B2844229 : Blo 2245435 2844229 := bbase (se 4 (by rfl) ⟨266646, by rfl⟩ : syracuseStep 2844229 = 533293) (by norm_num)
theorem B3792305 : Blo 2245435 3792305 := bstep (se 2 (by rfl) ⟨1422114, by rfl⟩ : syracuseStep 3792305 = 2844229) B2844229
theorem B2528203 : Blo 2245435 2528203 := bstep (se 1 (by rfl) ⟨1896152, by rfl⟩ : syracuseStep 2528203 = 3792305) B3792305
theorem B3370937 : Blo 2245435 3370937 := bstep (se 2 (by rfl) ⟨1264101, by rfl⟩ : syracuseStep 3370937 = 2528203) B2528203
theorem B2247291 : Blo 2245435 2247291 := bstep (se 1 (by rfl) ⟨1685468, by rfl⟩ : syracuseStep 2247291 = 3370937) B3370937
theorem B6927109 : Blo 2245435 6927109 := bbase (se 4 (by rfl) ⟨649416, by rfl⟩ : syracuseStep 6927109 = 1298833) (by norm_num)
theorem B36944581 : Blo 2245435 36944581 := bstep (se 4 (by rfl) ⟨3463554, by rfl⟩ : syracuseStep 36944581 = 6927109) B6927109
theorem B49259441 : Blo 2245435 49259441 := bstep (se 2 (by rfl) ⟨18472290, by rfl⟩ : syracuseStep 49259441 = 36944581) B36944581
theorem B32839627 : Blo 2245435 32839627 := bstep (se 1 (by rfl) ⟨24629720, by rfl⟩ : syracuseStep 32839627 = 49259441) B49259441
theorem B43786169 : Blo 2245435 43786169 := bstep (se 2 (by rfl) ⟨16419813, by rfl⟩ : syracuseStep 43786169 = 32839627) B32839627
theorem B29190779 : Blo 2245435 29190779 := bstep (se 1 (by rfl) ⟨21893084, by rfl⟩ : syracuseStep 29190779 = 43786169) B43786169
theorem B19460519 : Blo 2245435 19460519 := bstep (se 1 (by rfl) ⟨14595389, by rfl⟩ : syracuseStep 19460519 = 29190779) B29190779
theorem B12973679 : Blo 2245435 12973679 := bstep (se 1 (by rfl) ⟨9730259, by rfl⟩ : syracuseStep 12973679 = 19460519) B19460519
theorem B8649119 : Blo 2245435 8649119 := bstep (se 1 (by rfl) ⟨6486839, by rfl⟩ : syracuseStep 8649119 = 12973679) B12973679
theorem B5766079 : Blo 2245435 5766079 := bstep (se 1 (by rfl) ⟨4324559, by rfl⟩ : syracuseStep 5766079 = 8649119) B8649119
theorem B7688105 : Blo 2245435 7688105 := bstep (se 2 (by rfl) ⟨2883039, by rfl⟩ : syracuseStep 7688105 = 5766079) B5766079
theorem B5125403 : Blo 2245435 5125403 := bstep (se 1 (by rfl) ⟨3844052, by rfl⟩ : syracuseStep 5125403 = 7688105) B7688105
theorem B13667741 : Blo 2245435 13667741 := bstep (se 3 (by rfl) ⟨2562701, by rfl⟩ : syracuseStep 13667741 = 5125403) B5125403
theorem B9111827 : Blo 2245435 9111827 := bstep (se 1 (by rfl) ⟨6833870, by rfl⟩ : syracuseStep 9111827 = 13667741) B13667741
theorem B6074551 : Blo 2245435 6074551 := bstep (se 1 (by rfl) ⟨4555913, by rfl⟩ : syracuseStep 6074551 = 9111827) B9111827
theorem B8099401 : Blo 2245435 8099401 := bstep (se 2 (by rfl) ⟨3037275, by rfl⟩ : syracuseStep 8099401 = 6074551) B6074551
theorem B10799201 : Blo 2245435 10799201 := bstep (se 2 (by rfl) ⟨4049700, by rfl⟩ : syracuseStep 10799201 = 8099401) B8099401
theorem B28797869 : Blo 2245435 28797869 := bstep (se 3 (by rfl) ⟨5399600, by rfl⟩ : syracuseStep 28797869 = 10799201) B10799201
theorem B19198579 : Blo 2245435 19198579 := bstep (se 1 (by rfl) ⟨14398934, by rfl⟩ : syracuseStep 19198579 = 28797869) B28797869
theorem B25598105 : Blo 2245435 25598105 := bstep (se 2 (by rfl) ⟨9599289, by rfl⟩ : syracuseStep 25598105 = 19198579) B19198579
theorem B17065403 : Blo 2245435 17065403 := bstep (se 1 (by rfl) ⟨12799052, by rfl⟩ : syracuseStep 17065403 = 25598105) B25598105
theorem B11376935 : Blo 2245435 11376935 := bstep (se 1 (by rfl) ⟨8532701, by rfl⟩ : syracuseStep 11376935 = 17065403) B17065403
theorem B7584623 : Blo 2245435 7584623 := bstep (se 1 (by rfl) ⟨5688467, by rfl⟩ : syracuseStep 7584623 = 11376935) B11376935
theorem B5056415 : Blo 2245435 5056415 := bstep (se 1 (by rfl) ⟨3792311, by rfl⟩ : syracuseStep 5056415 = 7584623) B7584623
theorem B3370943 : Blo 2245435 3370943 := bstep (se 1 (by rfl) ⟨2528207, by rfl⟩ : syracuseStep 3370943 = 5056415) B5056415
theorem B2247295 : Blo 2245435 2247295 := bstep (se 1 (by rfl) ⟨1685471, by rfl⟩ : syracuseStep 2247295 = 3370943) B3370943
theorem B3370949 : Blo 2245435 3370949 := bbase (se 4 (by rfl) ⟨316026, by rfl⟩ : syracuseStep 3370949 = 632053) (by norm_num)
theorem B2247299 : Blo 2245435 2247299 := bstep (se 1 (by rfl) ⟨1685474, by rfl⟩ : syracuseStep 2247299 = 3370949) B3370949
theorem B3792325 : Blo 2245435 3792325 := bbase (se 4 (by rfl) ⟨355530, by rfl⟩ : syracuseStep 3792325 = 711061) (by norm_num)
theorem B5056433 : Blo 2245435 5056433 := bstep (se 2 (by rfl) ⟨1896162, by rfl⟩ : syracuseStep 5056433 = 3792325) B3792325
theorem B3370955 : Blo 2245435 3370955 := bstep (se 1 (by rfl) ⟨2528216, by rfl⟩ : syracuseStep 3370955 = 5056433) B5056433
theorem B2247303 : Blo 2245435 2247303 := bstep (se 1 (by rfl) ⟨1685477, by rfl⟩ : syracuseStep 2247303 = 3370955) B3370955
theorem B2528221 : Blo 2245435 2528221 := bbase (se 3 (by rfl) ⟨474041, by rfl⟩ : syracuseStep 2528221 = 948083) (by norm_num)
theorem B3370961 : Blo 2245435 3370961 := bstep (se 2 (by rfl) ⟨1264110, by rfl⟩ : syracuseStep 3370961 = 2528221) B2528221
theorem B2247307 : Blo 2245435 2247307 := bstep (se 1 (by rfl) ⟨1685480, by rfl⟩ : syracuseStep 2247307 = 3370961) B3370961
theorem B7584677 : Blo 2245435 7584677 := bbase (se 4 (by rfl) ⟨711063, by rfl⟩ : syracuseStep 7584677 = 1422127) (by norm_num)
theorem B5056451 : Blo 2245435 5056451 := bstep (se 1 (by rfl) ⟨3792338, by rfl⟩ : syracuseStep 5056451 = 7584677) B7584677
theorem B3370967 : Blo 2245435 3370967 := bstep (se 1 (by rfl) ⟨2528225, by rfl⟩ : syracuseStep 3370967 = 5056451) B5056451
theorem B2247311 : Blo 2245435 2247311 := bstep (se 1 (by rfl) ⟨1685483, by rfl⟩ : syracuseStep 2247311 = 3370967) B3370967
theorem B3370973 : Blo 2245435 3370973 := bbase (se 3 (by rfl) ⟨632057, by rfl⟩ : syracuseStep 3370973 = 1264115) (by norm_num)
theorem B2247315 : Blo 2245435 2247315 := bstep (se 1 (by rfl) ⟨1685486, by rfl⟩ : syracuseStep 2247315 = 3370973) B3370973
theorem B5056469 : Blo 2245435 5056469 := bbase (se 7 (by rfl) ⟨59255, by rfl⟩ : syracuseStep 5056469 = 118511) (by norm_num)
theorem B3370979 : Blo 2245435 3370979 := bstep (se 1 (by rfl) ⟨2528234, by rfl⟩ : syracuseStep 3370979 = 5056469) B5056469
theorem B2247319 : Blo 2245435 2247319 := bstep (se 1 (by rfl) ⟨1685489, by rfl⟩ : syracuseStep 2247319 = 3370979) B3370979
theorem B5399669 : Blo 2245435 5399669 := bbase (se 5 (by rfl) ⟨253109, by rfl⟩ : syracuseStep 5399669 = 506219) (by norm_num)
theorem B14399117 : Blo 2245435 14399117 := bstep (se 3 (by rfl) ⟨2699834, by rfl⟩ : syracuseStep 14399117 = 5399669) B5399669
theorem B9599411 : Blo 2245435 9599411 := bstep (se 1 (by rfl) ⟨7199558, by rfl⟩ : syracuseStep 9599411 = 14399117) B14399117
theorem B6399607 : Blo 2245435 6399607 := bstep (se 1 (by rfl) ⟨4799705, by rfl⟩ : syracuseStep 6399607 = 9599411) B9599411
theorem B8532809 : Blo 2245435 8532809 := bstep (se 2 (by rfl) ⟨3199803, by rfl⟩ : syracuseStep 8532809 = 6399607) B6399607
theorem B5688539 : Blo 2245435 5688539 := bstep (se 1 (by rfl) ⟨4266404, by rfl⟩ : syracuseStep 5688539 = 8532809) B8532809
theorem B3792359 : Blo 2245435 3792359 := bstep (se 1 (by rfl) ⟨2844269, by rfl⟩ : syracuseStep 3792359 = 5688539) B5688539
theorem B2528239 : Blo 2245435 2528239 := bstep (se 1 (by rfl) ⟨1896179, by rfl⟩ : syracuseStep 2528239 = 3792359) B3792359
theorem B3370985 : Blo 2245435 3370985 := bstep (se 2 (by rfl) ⟨1264119, by rfl⟩ : syracuseStep 3370985 = 2528239) B2528239
theorem B2247323 : Blo 2245435 2247323 := bstep (se 1 (by rfl) ⟨1685492, by rfl⟩ : syracuseStep 2247323 = 3370985) B3370985
theorem B20501909 : Blo 2245435 20501909 := bbase (se 6 (by rfl) ⟨480513, by rfl⟩ : syracuseStep 20501909 = 961027) (by norm_num)
theorem B13667939 : Blo 2245435 13667939 := bstep (se 1 (by rfl) ⟨10250954, by rfl⟩ : syracuseStep 13667939 = 20501909) B20501909
theorem B9111959 : Blo 2245435 9111959 := bstep (se 1 (by rfl) ⟨6833969, by rfl⟩ : syracuseStep 9111959 = 13667939) B13667939
theorem B6074639 : Blo 2245435 6074639 := bstep (se 1 (by rfl) ⟨4555979, by rfl⟩ : syracuseStep 6074639 = 9111959) B9111959
theorem B4049759 : Blo 2245435 4049759 := bstep (se 1 (by rfl) ⟨3037319, by rfl⟩ : syracuseStep 4049759 = 6074639) B6074639
theorem B2699839 : Blo 2245435 2699839 := bstep (se 1 (by rfl) ⟨2024879, by rfl⟩ : syracuseStep 2699839 = 4049759) B4049759
theorem B3599785 : Blo 2245435 3599785 := bstep (se 2 (by rfl) ⟨1349919, by rfl⟩ : syracuseStep 3599785 = 2699839) B2699839
theorem B19198853 : Blo 2245435 19198853 := bstep (se 4 (by rfl) ⟨1799892, by rfl⟩ : syracuseStep 19198853 = 3599785) B3599785
theorem B12799235 : Blo 2245435 12799235 := bstep (se 1 (by rfl) ⟨9599426, by rfl⟩ : syracuseStep 12799235 = 19198853) B19198853
theorem B8532823 : Blo 2245435 8532823 := bstep (se 1 (by rfl) ⟨6399617, by rfl⟩ : syracuseStep 8532823 = 12799235) B12799235
theorem B11377097 : Blo 2245435 11377097 := bstep (se 2 (by rfl) ⟨4266411, by rfl⟩ : syracuseStep 11377097 = 8532823) B8532823
theorem B7584731 : Blo 2245435 7584731 := bstep (se 1 (by rfl) ⟨5688548, by rfl⟩ : syracuseStep 7584731 = 11377097) B11377097
theorem B5056487 : Blo 2245435 5056487 := bstep (se 1 (by rfl) ⟨3792365, by rfl⟩ : syracuseStep 5056487 = 7584731) B7584731
theorem B3370991 : Blo 2245435 3370991 := bstep (se 1 (by rfl) ⟨2528243, by rfl⟩ : syracuseStep 3370991 = 5056487) B5056487
theorem B2247327 : Blo 2245435 2247327 := bstep (se 1 (by rfl) ⟨1685495, by rfl⟩ : syracuseStep 2247327 = 3370991) B3370991
theorem B3370997 : Blo 2245435 3370997 := bbase (se 5 (by rfl) ⟨158015, by rfl⟩ : syracuseStep 3370997 = 316031) (by norm_num)
theorem B2247331 : Blo 2245435 2247331 := bstep (se 1 (by rfl) ⟨1685498, by rfl⟩ : syracuseStep 2247331 = 3370997) B3370997
theorem B2699849 : Blo 2245435 2699849 := bbase (se 2 (by rfl) ⟨1012443, by rfl⟩ : syracuseStep 2699849 = 2024887) (by norm_num)
theorem B7199597 : Blo 2245435 7199597 := bstep (se 3 (by rfl) ⟨1349924, by rfl⟩ : syracuseStep 7199597 = 2699849) B2699849
theorem B4799731 : Blo 2245435 4799731 := bstep (se 1 (by rfl) ⟨3599798, by rfl⟩ : syracuseStep 4799731 = 7199597) B7199597
theorem B6399641 : Blo 2245435 6399641 := bstep (se 2 (by rfl) ⟨2399865, by rfl⟩ : syracuseStep 6399641 = 4799731) B4799731
theorem B4266427 : Blo 2245435 4266427 := bstep (se 1 (by rfl) ⟨3199820, by rfl⟩ : syracuseStep 4266427 = 6399641) B6399641
theorem B5688569 : Blo 2245435 5688569 := bstep (se 2 (by rfl) ⟨2133213, by rfl⟩ : syracuseStep 5688569 = 4266427) B4266427
theorem B3792379 : Blo 2245435 3792379 := bstep (se 1 (by rfl) ⟨2844284, by rfl⟩ : syracuseStep 3792379 = 5688569) B5688569
theorem B5056505 : Blo 2245435 5056505 := bstep (se 2 (by rfl) ⟨1896189, by rfl⟩ : syracuseStep 5056505 = 3792379) B3792379
theorem B3371003 : Blo 2245435 3371003 := bstep (se 1 (by rfl) ⟨2528252, by rfl⟩ : syracuseStep 3371003 = 5056505) B5056505
theorem B2247335 : Blo 2245435 2247335 := bstep (se 1 (by rfl) ⟨1685501, by rfl⟩ : syracuseStep 2247335 = 3371003) B3371003
theorem B2528257 : Blo 2245435 2528257 := bbase (se 2 (by rfl) ⟨948096, by rfl⟩ : syracuseStep 2528257 = 1896193) (by norm_num)
theorem B3371009 : Blo 2245435 3371009 := bstep (se 2 (by rfl) ⟨1264128, by rfl⟩ : syracuseStep 3371009 = 2528257) B2528257
theorem B2247339 : Blo 2245435 2247339 := bstep (se 1 (by rfl) ⟨1685504, by rfl⟩ : syracuseStep 2247339 = 3371009) B3371009
theorem B5688589 : Blo 2245435 5688589 := bbase (se 3 (by rfl) ⟨1066610, by rfl⟩ : syracuseStep 5688589 = 2133221) (by norm_num)
theorem B7584785 : Blo 2245435 7584785 := bstep (se 2 (by rfl) ⟨2844294, by rfl⟩ : syracuseStep 7584785 = 5688589) B5688589
theorem B5056523 : Blo 2245435 5056523 := bstep (se 1 (by rfl) ⟨3792392, by rfl⟩ : syracuseStep 5056523 = 7584785) B7584785
theorem B3371015 : Blo 2245435 3371015 := bstep (se 1 (by rfl) ⟨2528261, by rfl⟩ : syracuseStep 3371015 = 5056523) B5056523
theorem B2247343 : Blo 2245435 2247343 := bstep (se 1 (by rfl) ⟨1685507, by rfl⟩ : syracuseStep 2247343 = 3371015) B3371015
theorem B3371021 : Blo 2245435 3371021 := bbase (se 3 (by rfl) ⟨632066, by rfl⟩ : syracuseStep 3371021 = 1264133) (by norm_num)
theorem B2247347 : Blo 2245435 2247347 := bstep (se 1 (by rfl) ⟨1685510, by rfl⟩ : syracuseStep 2247347 = 3371021) B3371021
theorem B5056541 : Blo 2245435 5056541 := bbase (se 3 (by rfl) ⟨948101, by rfl⟩ : syracuseStep 5056541 = 1896203) (by norm_num)
theorem B3371027 : Blo 2245435 3371027 := bstep (se 1 (by rfl) ⟨2528270, by rfl⟩ : syracuseStep 3371027 = 5056541) B5056541
theorem B2247351 : Blo 2245435 2247351 := bstep (se 1 (by rfl) ⟨1685513, by rfl⟩ : syracuseStep 2247351 = 3371027) B3371027
theorem B3792413 : Blo 2245435 3792413 := bbase (se 3 (by rfl) ⟨711077, by rfl⟩ : syracuseStep 3792413 = 1422155) (by norm_num)
theorem B2528275 : Blo 2245435 2528275 := bstep (se 1 (by rfl) ⟨1896206, by rfl⟩ : syracuseStep 2528275 = 3792413) B3792413
theorem B3371033 : Blo 2245435 3371033 := bstep (se 2 (by rfl) ⟨1264137, by rfl⟩ : syracuseStep 3371033 = 2528275) B2528275
theorem B2247355 : Blo 2245435 2247355 := bstep (se 1 (by rfl) ⟨1685516, by rfl⟩ : syracuseStep 2247355 = 3371033) B3371033
theorem B10799509 : Blo 2245435 10799509 := bbase (se 6 (by rfl) ⟨253113, by rfl⟩ : syracuseStep 10799509 = 506227) (by norm_num)
theorem B14399345 : Blo 2245435 14399345 := bstep (se 2 (by rfl) ⟨5399754, by rfl⟩ : syracuseStep 14399345 = 10799509) B10799509
theorem B9599563 : Blo 2245435 9599563 := bstep (se 1 (by rfl) ⟨7199672, by rfl⟩ : syracuseStep 9599563 = 14399345) B14399345
theorem B12799417 : Blo 2245435 12799417 := bstep (se 2 (by rfl) ⟨4799781, by rfl⟩ : syracuseStep 12799417 = 9599563) B9599563
theorem B17065889 : Blo 2245435 17065889 := bstep (se 2 (by rfl) ⟨6399708, by rfl⟩ : syracuseStep 17065889 = 12799417) B12799417
theorem B11377259 : Blo 2245435 11377259 := bstep (se 1 (by rfl) ⟨8532944, by rfl⟩ : syracuseStep 11377259 = 17065889) B17065889
theorem B7584839 : Blo 2245435 7584839 := bstep (se 1 (by rfl) ⟨5688629, by rfl⟩ : syracuseStep 7584839 = 11377259) B11377259
theorem B5056559 : Blo 2245435 5056559 := bstep (se 1 (by rfl) ⟨3792419, by rfl⟩ : syracuseStep 5056559 = 7584839) B7584839
theorem B3371039 : Blo 2245435 3371039 := bstep (se 1 (by rfl) ⟨2528279, by rfl⟩ : syracuseStep 3371039 = 5056559) B5056559
theorem B2247359 : Blo 2245435 2247359 := bstep (se 1 (by rfl) ⟨1685519, by rfl⟩ : syracuseStep 2247359 = 3371039) B3371039
theorem B3371045 : Blo 2245435 3371045 := bbase (se 4 (by rfl) ⟨316035, by rfl⟩ : syracuseStep 3371045 = 632071) (by norm_num)
theorem B2247363 : Blo 2245435 2247363 := bstep (se 1 (by rfl) ⟨1685522, by rfl⟩ : syracuseStep 2247363 = 3371045) B3371045
theorem B2844325 : Blo 2245435 2844325 := bbase (se 4 (by rfl) ⟨266655, by rfl⟩ : syracuseStep 2844325 = 533311) (by norm_num)
theorem B3792433 : Blo 2245435 3792433 := bstep (se 2 (by rfl) ⟨1422162, by rfl⟩ : syracuseStep 3792433 = 2844325) B2844325
theorem B5056577 : Blo 2245435 5056577 := bstep (se 2 (by rfl) ⟨1896216, by rfl⟩ : syracuseStep 5056577 = 3792433) B3792433
theorem B3371051 : Blo 2245435 3371051 := bstep (se 1 (by rfl) ⟨2528288, by rfl⟩ : syracuseStep 3371051 = 5056577) B5056577
theorem B2247367 : Blo 2245435 2247367 := bstep (se 1 (by rfl) ⟨1685525, by rfl⟩ : syracuseStep 2247367 = 3371051) B3371051
theorem B2528293 : Blo 2245435 2528293 := bbase (se 4 (by rfl) ⟨237027, by rfl⟩ : syracuseStep 2528293 = 474055) (by norm_num)
theorem B3371057 : Blo 2245435 3371057 := bstep (se 2 (by rfl) ⟨1264146, by rfl⟩ : syracuseStep 3371057 = 2528293) B2528293
theorem B2247371 : Blo 2245435 2247371 := bstep (se 1 (by rfl) ⟨1685528, by rfl⟩ : syracuseStep 2247371 = 3371057) B3371057
theorem B2699897 : Blo 2245435 2699897 := bbase (se 2 (by rfl) ⟨1012461, by rfl⟩ : syracuseStep 2699897 = 2024923) (by norm_num)
theorem B7199725 : Blo 2245435 7199725 := bstep (se 3 (by rfl) ⟨1349948, by rfl⟩ : syracuseStep 7199725 = 2699897) B2699897
theorem B9599633 : Blo 2245435 9599633 := bstep (se 2 (by rfl) ⟨3599862, by rfl⟩ : syracuseStep 9599633 = 7199725) B7199725
theorem B6399755 : Blo 2245435 6399755 := bstep (se 1 (by rfl) ⟨4799816, by rfl⟩ : syracuseStep 6399755 = 9599633) B9599633
theorem B4266503 : Blo 2245435 4266503 := bstep (se 1 (by rfl) ⟨3199877, by rfl⟩ : syracuseStep 4266503 = 6399755) B6399755
theorem B2844335 : Blo 2245435 2844335 := bstep (se 1 (by rfl) ⟨2133251, by rfl⟩ : syracuseStep 2844335 = 4266503) B4266503
theorem B7584893 : Blo 2245435 7584893 := bstep (se 3 (by rfl) ⟨1422167, by rfl⟩ : syracuseStep 7584893 = 2844335) B2844335
theorem B5056595 : Blo 2245435 5056595 := bstep (se 1 (by rfl) ⟨3792446, by rfl⟩ : syracuseStep 5056595 = 7584893) B7584893
theorem B3371063 : Blo 2245435 3371063 := bstep (se 1 (by rfl) ⟨2528297, by rfl⟩ : syracuseStep 3371063 = 5056595) B5056595
theorem B2247375 : Blo 2245435 2247375 := bstep (se 1 (by rfl) ⟨1685531, by rfl⟩ : syracuseStep 2247375 = 3371063) B3371063
theorem B3371069 : Blo 2245435 3371069 := bbase (se 3 (by rfl) ⟨632075, by rfl⟩ : syracuseStep 3371069 = 1264151) (by norm_num)
theorem B2247379 : Blo 2245435 2247379 := bstep (se 1 (by rfl) ⟨1685534, by rfl⟩ : syracuseStep 2247379 = 3371069) B3371069
theorem B5056613 : Blo 2245435 5056613 := bbase (se 4 (by rfl) ⟨474057, by rfl⟩ : syracuseStep 5056613 = 948115) (by norm_num)
theorem B3371075 : Blo 2245435 3371075 := bstep (se 1 (by rfl) ⟨2528306, by rfl⟩ : syracuseStep 3371075 = 5056613) B5056613
theorem B2247383 : Blo 2245435 2247383 := bstep (se 1 (by rfl) ⟨1685537, by rfl⟩ : syracuseStep 2247383 = 3371075) B3371075
theorem B5688701 : Blo 2245435 5688701 := bbase (se 3 (by rfl) ⟨1066631, by rfl⟩ : syracuseStep 5688701 = 2133263) (by norm_num)
theorem B3792467 : Blo 2245435 3792467 := bstep (se 1 (by rfl) ⟨2844350, by rfl⟩ : syracuseStep 3792467 = 5688701) B5688701
theorem B2528311 : Blo 2245435 2528311 := bstep (se 1 (by rfl) ⟨1896233, by rfl⟩ : syracuseStep 2528311 = 3792467) B3792467
theorem B3371081 : Blo 2245435 3371081 := bstep (se 2 (by rfl) ⟨1264155, by rfl⟩ : syracuseStep 3371081 = 2528311) B2528311
theorem B2247387 : Blo 2245435 2247387 := bstep (se 1 (by rfl) ⟨1685540, by rfl⟩ : syracuseStep 2247387 = 3371081) B3371081
theorem B4266533 : Blo 2245435 4266533 := bbase (se 4 (by rfl) ⟨399987, by rfl⟩ : syracuseStep 4266533 = 799975) (by norm_num)
theorem B11377421 : Blo 2245435 11377421 := bstep (se 3 (by rfl) ⟨2133266, by rfl⟩ : syracuseStep 11377421 = 4266533) B4266533
theorem B7584947 : Blo 2245435 7584947 := bstep (se 1 (by rfl) ⟨5688710, by rfl⟩ : syracuseStep 7584947 = 11377421) B11377421
theorem B5056631 : Blo 2245435 5056631 := bstep (se 1 (by rfl) ⟨3792473, by rfl⟩ : syracuseStep 5056631 = 7584947) B7584947
theorem B3371087 : Blo 2245435 3371087 := bstep (se 1 (by rfl) ⟨2528315, by rfl⟩ : syracuseStep 3371087 = 5056631) B5056631
theorem B2247391 : Blo 2245435 2247391 := bstep (se 1 (by rfl) ⟨1685543, by rfl⟩ : syracuseStep 2247391 = 3371087) B3371087
theorem B3371093 : Blo 2245435 3371093 := bbase (se 8 (by rfl) ⟨19752, by rfl⟩ : syracuseStep 3371093 = 39505) (by norm_num)
theorem B2247395 : Blo 2245435 2247395 := bstep (se 1 (by rfl) ⟨1685546, by rfl⟩ : syracuseStep 2247395 = 3371093) B3371093
theorem B4556125 : Blo 2245435 4556125 := bbase (se 3 (by rfl) ⟨854273, by rfl⟩ : syracuseStep 4556125 = 1708547) (by norm_num)
theorem B6074833 : Blo 2245435 6074833 := bstep (se 2 (by rfl) ⟨2278062, by rfl⟩ : syracuseStep 6074833 = 4556125) B4556125
theorem B8099777 : Blo 2245435 8099777 := bstep (se 2 (by rfl) ⟨3037416, by rfl⟩ : syracuseStep 8099777 = 6074833) B6074833
theorem B21599405 : Blo 2245435 21599405 := bstep (se 3 (by rfl) ⟨4049888, by rfl⟩ : syracuseStep 21599405 = 8099777) B8099777
theorem B14399603 : Blo 2245435 14399603 := bstep (se 1 (by rfl) ⟨10799702, by rfl⟩ : syracuseStep 14399603 = 21599405) B21599405
theorem B9599735 : Blo 2245435 9599735 := bstep (se 1 (by rfl) ⟨7199801, by rfl⟩ : syracuseStep 9599735 = 14399603) B14399603
theorem B6399823 : Blo 2245435 6399823 := bstep (se 1 (by rfl) ⟨4799867, by rfl⟩ : syracuseStep 6399823 = 9599735) B9599735
theorem B8533097 : Blo 2245435 8533097 := bstep (se 2 (by rfl) ⟨3199911, by rfl⟩ : syracuseStep 8533097 = 6399823) B6399823
theorem B5688731 : Blo 2245435 5688731 := bstep (se 1 (by rfl) ⟨4266548, by rfl⟩ : syracuseStep 5688731 = 8533097) B8533097
theorem B3792487 : Blo 2245435 3792487 := bstep (se 1 (by rfl) ⟨2844365, by rfl⟩ : syracuseStep 3792487 = 5688731) B5688731
theorem B5056649 : Blo 2245435 5056649 := bstep (se 2 (by rfl) ⟨1896243, by rfl⟩ : syracuseStep 5056649 = 3792487) B3792487
theorem B3371099 : Blo 2245435 3371099 := bstep (se 1 (by rfl) ⟨2528324, by rfl⟩ : syracuseStep 3371099 = 5056649) B5056649
theorem B2247399 : Blo 2245435 2247399 := bstep (se 1 (by rfl) ⟨1685549, by rfl⟩ : syracuseStep 2247399 = 3371099) B3371099
theorem B2528329 : Blo 2245435 2528329 := bbase (se 2 (by rfl) ⟨948123, by rfl⟩ : syracuseStep 2528329 = 1896247) (by norm_num)
theorem B3371105 : Blo 2245435 3371105 := bstep (se 2 (by rfl) ⟨1264164, by rfl⟩ : syracuseStep 3371105 = 2528329) B2528329
theorem B2247403 : Blo 2245435 2247403 := bstep (se 1 (by rfl) ⟨1685552, by rfl⟩ : syracuseStep 2247403 = 3371105) B3371105
theorem B3078869 : Blo 2245435 3078869 := bbase (se 7 (by rfl) ⟨36080, by rfl⟩ : syracuseStep 3078869 = 72161) (by norm_num)
theorem B8210317 : Blo 2245435 8210317 := bstep (se 3 (by rfl) ⟨1539434, by rfl⟩ : syracuseStep 8210317 = 3078869) B3078869
theorem B10947089 : Blo 2245435 10947089 := bstep (se 2 (by rfl) ⟨4105158, by rfl⟩ : syracuseStep 10947089 = 8210317) B8210317
theorem B29192237 : Blo 2245435 29192237 := bstep (se 3 (by rfl) ⟨5473544, by rfl⟩ : syracuseStep 29192237 = 10947089) B10947089
theorem B19461491 : Blo 2245435 19461491 := bstep (se 1 (by rfl) ⟨14596118, by rfl⟩ : syracuseStep 19461491 = 29192237) B29192237
theorem B12974327 : Blo 2245435 12974327 := bstep (se 1 (by rfl) ⟨9730745, by rfl⟩ : syracuseStep 12974327 = 19461491) B19461491
theorem B8649551 : Blo 2245435 8649551 := bstep (se 1 (by rfl) ⟨6487163, by rfl⟩ : syracuseStep 8649551 = 12974327) B12974327
theorem B23065469 : Blo 2245435 23065469 := bstep (se 3 (by rfl) ⟨4324775, by rfl⟩ : syracuseStep 23065469 = 8649551) B8649551
theorem B15376979 : Blo 2245435 15376979 := bstep (se 1 (by rfl) ⟨11532734, by rfl⟩ : syracuseStep 15376979 = 23065469) B23065469
theorem B10251319 : Blo 2245435 10251319 := bstep (se 1 (by rfl) ⟨7688489, by rfl⟩ : syracuseStep 10251319 = 15376979) B15376979
theorem B13668425 : Blo 2245435 13668425 := bstep (se 2 (by rfl) ⟨5125659, by rfl⟩ : syracuseStep 13668425 = 10251319) B10251319
theorem B9112283 : Blo 2245435 9112283 := bstep (se 1 (by rfl) ⟨6834212, by rfl⟩ : syracuseStep 9112283 = 13668425) B13668425
theorem B6074855 : Blo 2245435 6074855 := bstep (se 1 (by rfl) ⟨4556141, by rfl⟩ : syracuseStep 6074855 = 9112283) B9112283
theorem B4049903 : Blo 2245435 4049903 := bstep (se 1 (by rfl) ⟨3037427, by rfl⟩ : syracuseStep 4049903 = 6074855) B6074855
theorem B2699935 : Blo 2245435 2699935 := bstep (se 1 (by rfl) ⟨2024951, by rfl⟩ : syracuseStep 2699935 = 4049903) B4049903
theorem B14399653 : Blo 2245435 14399653 := bstep (se 4 (by rfl) ⟨1349967, by rfl⟩ : syracuseStep 14399653 = 2699935) B2699935
theorem B19199537 : Blo 2245435 19199537 := bstep (se 2 (by rfl) ⟨7199826, by rfl⟩ : syracuseStep 19199537 = 14399653) B14399653
theorem B12799691 : Blo 2245435 12799691 := bstep (se 1 (by rfl) ⟨9599768, by rfl⟩ : syracuseStep 12799691 = 19199537) B19199537
theorem B8533127 : Blo 2245435 8533127 := bstep (se 1 (by rfl) ⟨6399845, by rfl⟩ : syracuseStep 8533127 = 12799691) B12799691
theorem B5688751 : Blo 2245435 5688751 := bstep (se 1 (by rfl) ⟨4266563, by rfl⟩ : syracuseStep 5688751 = 8533127) B8533127
theorem B7585001 : Blo 2245435 7585001 := bstep (se 2 (by rfl) ⟨2844375, by rfl⟩ : syracuseStep 7585001 = 5688751) B5688751
theorem B5056667 : Blo 2245435 5056667 := bstep (se 1 (by rfl) ⟨3792500, by rfl⟩ : syracuseStep 5056667 = 7585001) B7585001
theorem B3371111 : Blo 2245435 3371111 := bstep (se 1 (by rfl) ⟨2528333, by rfl⟩ : syracuseStep 3371111 = 5056667) B5056667
theorem B2247407 : Blo 2245435 2247407 := bstep (se 1 (by rfl) ⟨1685555, by rfl⟩ : syracuseStep 2247407 = 3371111) B3371111
theorem B3371117 : Blo 2245435 3371117 := bbase (se 3 (by rfl) ⟨632084, by rfl⟩ : syracuseStep 3371117 = 1264169) (by norm_num)
theorem B2247411 : Blo 2245435 2247411 := bstep (se 1 (by rfl) ⟨1685558, by rfl⟩ : syracuseStep 2247411 = 3371117) B3371117
theorem B5056685 : Blo 2245435 5056685 := bbase (se 3 (by rfl) ⟨948128, by rfl⟩ : syracuseStep 5056685 = 1896257) (by norm_num)
theorem B3371123 : Blo 2245435 3371123 := bstep (se 1 (by rfl) ⟨2528342, by rfl⟩ : syracuseStep 3371123 = 5056685) B5056685
theorem B2247415 : Blo 2245435 2247415 := bstep (se 1 (by rfl) ⟨1685561, by rfl⟩ : syracuseStep 2247415 = 3371123) B3371123
theorem B3417125 : Blo 2245435 3417125 := bbase (se 4 (by rfl) ⟨320355, by rfl⟩ : syracuseStep 3417125 = 640711) (by norm_num)
theorem B9112333 : Blo 2245435 9112333 := bstep (se 3 (by rfl) ⟨1708562, by rfl⟩ : syracuseStep 9112333 = 3417125) B3417125
theorem B12149777 : Blo 2245435 12149777 := bstep (se 2 (by rfl) ⟨4556166, by rfl⟩ : syracuseStep 12149777 = 9112333) B9112333
theorem B8099851 : Blo 2245435 8099851 := bstep (se 1 (by rfl) ⟨6074888, by rfl⟩ : syracuseStep 8099851 = 12149777) B12149777
theorem B10799801 : Blo 2245435 10799801 := bstep (se 2 (by rfl) ⟨4049925, by rfl⟩ : syracuseStep 10799801 = 8099851) B8099851
theorem B7199867 : Blo 2245435 7199867 := bstep (se 1 (by rfl) ⟨5399900, by rfl⟩ : syracuseStep 7199867 = 10799801) B10799801
theorem B4799911 : Blo 2245435 4799911 := bstep (se 1 (by rfl) ⟨3599933, by rfl⟩ : syracuseStep 4799911 = 7199867) B7199867
theorem B6399881 : Blo 2245435 6399881 := bstep (se 2 (by rfl) ⟨2399955, by rfl⟩ : syracuseStep 6399881 = 4799911) B4799911
theorem B4266587 : Blo 2245435 4266587 := bstep (se 1 (by rfl) ⟨3199940, by rfl⟩ : syracuseStep 4266587 = 6399881) B6399881
theorem B2844391 : Blo 2245435 2844391 := bstep (se 1 (by rfl) ⟨2133293, by rfl⟩ : syracuseStep 2844391 = 4266587) B4266587
theorem B3792521 : Blo 2245435 3792521 := bstep (se 2 (by rfl) ⟨1422195, by rfl⟩ : syracuseStep 3792521 = 2844391) B2844391
theorem B2528347 : Blo 2245435 2528347 := bstep (se 1 (by rfl) ⟨1896260, by rfl⟩ : syracuseStep 2528347 = 3792521) B3792521
theorem B3371129 : Blo 2245435 3371129 := bstep (se 2 (by rfl) ⟨1264173, by rfl⟩ : syracuseStep 3371129 = 2528347) B2528347
theorem B2247419 : Blo 2245435 2247419 := bstep (se 1 (by rfl) ⟨1685564, by rfl⟩ : syracuseStep 2247419 = 3371129) B3371129
theorem B28799509 : Blo 2245435 28799509 := bbase (se 6 (by rfl) ⟨674988, by rfl⟩ : syracuseStep 28799509 = 1349977) (by norm_num)
theorem B38399345 : Blo 2245435 38399345 := bstep (se 2 (by rfl) ⟨14399754, by rfl⟩ : syracuseStep 38399345 = 28799509) B28799509
theorem B25599563 : Blo 2245435 25599563 := bstep (se 1 (by rfl) ⟨19199672, by rfl⟩ : syracuseStep 25599563 = 38399345) B38399345
theorem B17066375 : Blo 2245435 17066375 := bstep (se 1 (by rfl) ⟨12799781, by rfl⟩ : syracuseStep 17066375 = 25599563) B25599563
theorem B11377583 : Blo 2245435 11377583 := bstep (se 1 (by rfl) ⟨8533187, by rfl⟩ : syracuseStep 11377583 = 17066375) B17066375
theorem B7585055 : Blo 2245435 7585055 := bstep (se 1 (by rfl) ⟨5688791, by rfl⟩ : syracuseStep 7585055 = 11377583) B11377583
theorem B5056703 : Blo 2245435 5056703 := bstep (se 1 (by rfl) ⟨3792527, by rfl⟩ : syracuseStep 5056703 = 7585055) B7585055
theorem B3371135 : Blo 2245435 3371135 := bstep (se 1 (by rfl) ⟨2528351, by rfl⟩ : syracuseStep 3371135 = 5056703) B5056703
theorem B2247423 : Blo 2245435 2247423 := bstep (se 1 (by rfl) ⟨1685567, by rfl⟩ : syracuseStep 2247423 = 3371135) B3371135
theorem B3371141 : Blo 2245435 3371141 := bbase (se 4 (by rfl) ⟨316044, by rfl⟩ : syracuseStep 3371141 = 632089) (by norm_num)
theorem B2247427 : Blo 2245435 2247427 := bstep (se 1 (by rfl) ⟨1685570, by rfl⟩ : syracuseStep 2247427 = 3371141) B3371141
theorem B3792541 : Blo 2245435 3792541 := bbase (se 3 (by rfl) ⟨711101, by rfl⟩ : syracuseStep 3792541 = 1422203) (by norm_num)
theorem B5056721 : Blo 2245435 5056721 := bstep (se 2 (by rfl) ⟨1896270, by rfl⟩ : syracuseStep 5056721 = 3792541) B3792541
theorem B3371147 : Blo 2245435 3371147 := bstep (se 1 (by rfl) ⟨2528360, by rfl⟩ : syracuseStep 3371147 = 5056721) B5056721
theorem B2247431 : Blo 2245435 2247431 := bstep (se 1 (by rfl) ⟨1685573, by rfl⟩ : syracuseStep 2247431 = 3371147) B3371147
theorem B2528365 : Blo 2245435 2528365 := bbase (se 3 (by rfl) ⟨474068, by rfl⟩ : syracuseStep 2528365 = 948137) (by norm_num)
theorem B3371153 : Blo 2245435 3371153 := bstep (se 2 (by rfl) ⟨1264182, by rfl⟩ : syracuseStep 3371153 = 2528365) B2528365
theorem B2247435 : Blo 2245435 2247435 := bstep (se 1 (by rfl) ⟨1685576, by rfl⟩ : syracuseStep 2247435 = 3371153) B3371153
theorem C0 (j : ℕ) (h1 : 561358 ≤ j) (h2 : j ≤ 561858) : Blo 2245435 (4 * j + 3) := by
  interval_cases j
  · exact B2245435
  · exact B2245439
  · exact B2245443
  · exact B2245447
  · exact B2245451
  · exact B2245455
  · exact B2245459
  · exact B2245463
  · exact B2245467
  · exact B2245471
  · exact B2245475
  · exact B2245479
  · exact B2245483
  · exact B2245487
  · exact B2245491
  · exact B2245495
  · exact B2245499
  · exact B2245503
  · exact B2245507
  · exact B2245511
  · exact B2245515
  · exact B2245519
  · exact B2245523
  · exact B2245527
  · exact B2245531
  · exact B2245535
  · exact B2245539
  · exact B2245543
  · exact B2245547
  · exact B2245551
  · exact B2245555
  · exact B2245559
  · exact B2245563
  · exact B2245567
  · exact B2245571
  · exact B2245575
  · exact B2245579
  · exact B2245583
  · exact B2245587
  · exact B2245591
  · exact B2245595
  · exact B2245599
  · exact B2245603
  · exact B2245607
  · exact B2245611
  · exact B2245615
  · exact B2245619
  · exact B2245623
  · exact B2245627
  · exact B2245631
  · exact B2245635
  · exact B2245639
  · exact B2245643
  · exact B2245647
  · exact B2245651
  · exact B2245655
  · exact B2245659
  · exact B2245663
  · exact B2245667
  · exact B2245671
  · exact B2245675
  · exact B2245679
  · exact B2245683
  · exact B2245687
  · exact B2245691
  · exact B2245695
  · exact B2245699
  · exact B2245703
  · exact B2245707
  · exact B2245711
  · exact B2245715
  · exact B2245719
  · exact B2245723
  · exact B2245727
  · exact B2245731
  · exact B2245735
  · exact B2245739
  · exact B2245743
  · exact B2245747
  · exact B2245751
  · exact B2245755
  · exact B2245759
  · exact B2245763
  · exact B2245767
  · exact B2245771
  · exact B2245775
  · exact B2245779
  · exact B2245783
  · exact B2245787
  · exact B2245791
  · exact B2245795
  · exact B2245799
  · exact B2245803
  · exact B2245807
  · exact B2245811
  · exact B2245815
  · exact B2245819
  · exact B2245823
  · exact B2245827
  · exact B2245831
  · exact B2245835
  · exact B2245839
  · exact B2245843
  · exact B2245847
  · exact B2245851
  · exact B2245855
  · exact B2245859
  · exact B2245863
  · exact B2245867
  · exact B2245871
  · exact B2245875
  · exact B2245879
  · exact B2245883
  · exact B2245887
  · exact B2245891
  · exact B2245895
  · exact B2245899
  · exact B2245903
  · exact B2245907
  · exact B2245911
  · exact B2245915
  · exact B2245919
  · exact B2245923
  · exact B2245927
  · exact B2245931
  · exact B2245935
  · exact B2245939
  · exact B2245943
  · exact B2245947
  · exact B2245951
  · exact B2245955
  · exact B2245959
  · exact B2245963
  · exact B2245967
  · exact B2245971
  · exact B2245975
  · exact B2245979
  · exact B2245983
  · exact B2245987
  · exact B2245991
  · exact B2245995
  · exact B2245999
  · exact B2246003
  · exact B2246007
  · exact B2246011
  · exact B2246015
  · exact B2246019
  · exact B2246023
  · exact B2246027
  · exact B2246031
  · exact B2246035
  · exact B2246039
  · exact B2246043
  · exact B2246047
  · exact B2246051
  · exact B2246055
  · exact B2246059
  · exact B2246063
  · exact B2246067
  · exact B2246071
  · exact B2246075
  · exact B2246079
  · exact B2246083
  · exact B2246087
  · exact B2246091
  · exact B2246095
  · exact B2246099
  · exact B2246103
  · exact B2246107
  · exact B2246111
  · exact B2246115
  · exact B2246119
  · exact B2246123
  · exact B2246127
  · exact B2246131
  · exact B2246135
  · exact B2246139
  · exact B2246143
  · exact B2246147
  · exact B2246151
  · exact B2246155
  · exact B2246159
  · exact B2246163
  · exact B2246167
  · exact B2246171
  · exact B2246175
  · exact B2246179
  · exact B2246183
  · exact B2246187
  · exact B2246191
  · exact B2246195
  · exact B2246199
  · exact B2246203
  · exact B2246207
  · exact B2246211
  · exact B2246215
  · exact B2246219
  · exact B2246223
  · exact B2246227
  · exact B2246231
  · exact B2246235
  · exact B2246239
  · exact B2246243
  · exact B2246247
  · exact B2246251
  · exact B2246255
  · exact B2246259
  · exact B2246263
  · exact B2246267
  · exact B2246271
  · exact B2246275
  · exact B2246279
  · exact B2246283
  · exact B2246287
  · exact B2246291
  · exact B2246295
  · exact B2246299
  · exact B2246303
  · exact B2246307
  · exact B2246311
  · exact B2246315
  · exact B2246319
  · exact B2246323
  · exact B2246327
  · exact B2246331
  · exact B2246335
  · exact B2246339
  · exact B2246343
  · exact B2246347
  · exact B2246351
  · exact B2246355
  · exact B2246359
  · exact B2246363
  · exact B2246367
  · exact B2246371
  · exact B2246375
  · exact B2246379
  · exact B2246383
  · exact B2246387
  · exact B2246391
  · exact B2246395
  · exact B2246399
  · exact B2246403
  · exact B2246407
  · exact B2246411
  · exact B2246415
  · exact B2246419
  · exact B2246423
  · exact B2246427
  · exact B2246431
  · exact B2246435
  · exact B2246439
  · exact B2246443
  · exact B2246447
  · exact B2246451
  · exact B2246455
  · exact B2246459
  · exact B2246463
  · exact B2246467
  · exact B2246471
  · exact B2246475
  · exact B2246479
  · exact B2246483
  · exact B2246487
  · exact B2246491
  · exact B2246495
  · exact B2246499
  · exact B2246503
  · exact B2246507
  · exact B2246511
  · exact B2246515
  · exact B2246519
  · exact B2246523
  · exact B2246527
  · exact B2246531
  · exact B2246535
  · exact B2246539
  · exact B2246543
  · exact B2246547
  · exact B2246551
  · exact B2246555
  · exact B2246559
  · exact B2246563
  · exact B2246567
  · exact B2246571
  · exact B2246575
  · exact B2246579
  · exact B2246583
  · exact B2246587
  · exact B2246591
  · exact B2246595
  · exact B2246599
  · exact B2246603
  · exact B2246607
  · exact B2246611
  · exact B2246615
  · exact B2246619
  · exact B2246623
  · exact B2246627
  · exact B2246631
  · exact B2246635
  · exact B2246639
  · exact B2246643
  · exact B2246647
  · exact B2246651
  · exact B2246655
  · exact B2246659
  · exact B2246663
  · exact B2246667
  · exact B2246671
  · exact B2246675
  · exact B2246679
  · exact B2246683
  · exact B2246687
  · exact B2246691
  · exact B2246695
  · exact B2246699
  · exact B2246703
  · exact B2246707
  · exact B2246711
  · exact B2246715
  · exact B2246719
  · exact B2246723
  · exact B2246727
  · exact B2246731
  · exact B2246735
  · exact B2246739
  · exact B2246743
  · exact B2246747
  · exact B2246751
  · exact B2246755
  · exact B2246759
  · exact B2246763
  · exact B2246767
  · exact B2246771
  · exact B2246775
  · exact B2246779
  · exact B2246783
  · exact B2246787
  · exact B2246791
  · exact B2246795
  · exact B2246799
  · exact B2246803
  · exact B2246807
  · exact B2246811
  · exact B2246815
  · exact B2246819
  · exact B2246823
  · exact B2246827
  · exact B2246831
  · exact B2246835
  · exact B2246839
  · exact B2246843
  · exact B2246847
  · exact B2246851
  · exact B2246855
  · exact B2246859
  · exact B2246863
  · exact B2246867
  · exact B2246871
  · exact B2246875
  · exact B2246879
  · exact B2246883
  · exact B2246887
  · exact B2246891
  · exact B2246895
  · exact B2246899
  · exact B2246903
  · exact B2246907
  · exact B2246911
  · exact B2246915
  · exact B2246919
  · exact B2246923
  · exact B2246927
  · exact B2246931
  · exact B2246935
  · exact B2246939
  · exact B2246943
  · exact B2246947
  · exact B2246951
  · exact B2246955
  · exact B2246959
  · exact B2246963
  · exact B2246967
  · exact B2246971
  · exact B2246975
  · exact B2246979
  · exact B2246983
  · exact B2246987
  · exact B2246991
  · exact B2246995
  · exact B2246999
  · exact B2247003
  · exact B2247007
  · exact B2247011
  · exact B2247015
  · exact B2247019
  · exact B2247023
  · exact B2247027
  · exact B2247031
  · exact B2247035
  · exact B2247039
  · exact B2247043
  · exact B2247047
  · exact B2247051
  · exact B2247055
  · exact B2247059
  · exact B2247063
  · exact B2247067
  · exact B2247071
  · exact B2247075
  · exact B2247079
  · exact B2247083
  · exact B2247087
  · exact B2247091
  · exact B2247095
  · exact B2247099
  · exact B2247103
  · exact B2247107
  · exact B2247111
  · exact B2247115
  · exact B2247119
  · exact B2247123
  · exact B2247127
  · exact B2247131
  · exact B2247135
  · exact B2247139
  · exact B2247143
  · exact B2247147
  · exact B2247151
  · exact B2247155
  · exact B2247159
  · exact B2247163
  · exact B2247167
  · exact B2247171
  · exact B2247175
  · exact B2247179
  · exact B2247183
  · exact B2247187
  · exact B2247191
  · exact B2247195
  · exact B2247199
  · exact B2247203
  · exact B2247207
  · exact B2247211
  · exact B2247215
  · exact B2247219
  · exact B2247223
  · exact B2247227
  · exact B2247231
  · exact B2247235
  · exact B2247239
  · exact B2247243
  · exact B2247247
  · exact B2247251
  · exact B2247255
  · exact B2247259
  · exact B2247263
  · exact B2247267
  · exact B2247271
  · exact B2247275
  · exact B2247279
  · exact B2247283
  · exact B2247287
  · exact B2247291
  · exact B2247295
  · exact B2247299
  · exact B2247303
  · exact B2247307
  · exact B2247311
  · exact B2247315
  · exact B2247319
  · exact B2247323
  · exact B2247327
  · exact B2247331
  · exact B2247335
  · exact B2247339
  · exact B2247343
  · exact B2247347
  · exact B2247351
  · exact B2247355
  · exact B2247359
  · exact B2247363
  · exact B2247367
  · exact B2247371
  · exact B2247375
  · exact B2247379
  · exact B2247383
  · exact B2247387
  · exact B2247391
  · exact B2247395
  · exact B2247399
  · exact B2247403
  · exact B2247407
  · exact B2247411
  · exact B2247415
  · exact B2247419
  · exact B2247423
  · exact B2247427
  · exact B2247431
  · exact B2247435
theorem solution (m : ℕ) (hlo : 2245435 ≤ m) (hhi : m ≤ 2247435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 561358 ≤ j := by omega
    have hj2 : j ≤ 561858 := by omega
    have hb : Blo 2245435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
