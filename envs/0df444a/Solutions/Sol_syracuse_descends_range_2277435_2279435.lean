-- Prove2me | solution 1 for syracuse_descends_range_2277435_2279435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:33.550762+00:00
-- url     : https://prove2.me/submissions/37882406-39c3-4755-ad9b-dcda8be72419

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

theorem B3843173 : Blo 2277435 3843173 := bbase (se 4 (by rfl) ⟨360297, by rfl⟩ : syracuseStep 3843173 = 720595) (by norm_num)
theorem B2562115 : Blo 2277435 2562115 := bstep (se 1 (by rfl) ⟨1921586, by rfl⟩ : syracuseStep 2562115 = 3843173) B3843173
theorem B3416153 : Blo 2277435 3416153 := bstep (se 2 (by rfl) ⟨1281057, by rfl⟩ : syracuseStep 3416153 = 2562115) B2562115
theorem B2277435 : Blo 2277435 2277435 := bstep (se 1 (by rfl) ⟨1708076, by rfl⟩ : syracuseStep 2277435 = 3416153) B3416153
theorem B5472029 : Blo 2277435 5472029 := bbase (se 3 (by rfl) ⟨1026005, by rfl⟩ : syracuseStep 5472029 = 2052011) (by norm_num)
theorem B3648019 : Blo 2277435 3648019 := bstep (se 1 (by rfl) ⟨2736014, by rfl⟩ : syracuseStep 3648019 = 5472029) B5472029
theorem B4864025 : Blo 2277435 4864025 := bstep (se 2 (by rfl) ⟨1824009, by rfl⟩ : syracuseStep 4864025 = 3648019) B3648019
theorem B3242683 : Blo 2277435 3242683 := bstep (se 1 (by rfl) ⟨2432012, by rfl⟩ : syracuseStep 3242683 = 4864025) B4864025
theorem B17294309 : Blo 2277435 17294309 := bstep (se 4 (by rfl) ⟨1621341, by rfl⟩ : syracuseStep 17294309 = 3242683) B3242683
theorem B11529539 : Blo 2277435 11529539 := bstep (se 1 (by rfl) ⟨8647154, by rfl⟩ : syracuseStep 11529539 = 17294309) B17294309
theorem B7686359 : Blo 2277435 7686359 := bstep (se 1 (by rfl) ⟨5764769, by rfl⟩ : syracuseStep 7686359 = 11529539) B11529539
theorem B5124239 : Blo 2277435 5124239 := bstep (se 1 (by rfl) ⟨3843179, by rfl⟩ : syracuseStep 5124239 = 7686359) B7686359
theorem B3416159 : Blo 2277435 3416159 := bstep (se 1 (by rfl) ⟨2562119, by rfl⟩ : syracuseStep 3416159 = 5124239) B5124239
theorem B2277439 : Blo 2277435 2277439 := bstep (se 1 (by rfl) ⟨1708079, by rfl⟩ : syracuseStep 2277439 = 3416159) B3416159
theorem B3416165 : Blo 2277435 3416165 := bbase (se 4 (by rfl) ⟨320265, by rfl⟩ : syracuseStep 3416165 = 640531) (by norm_num)
theorem B2277443 : Blo 2277435 2277443 := bstep (se 1 (by rfl) ⟨1708082, by rfl⟩ : syracuseStep 2277443 = 3416165) B3416165
theorem B4104037 : Blo 2277435 4104037 := bbase (se 4 (by rfl) ⟨384753, by rfl⟩ : syracuseStep 4104037 = 769507) (by norm_num)
theorem B5472049 : Blo 2277435 5472049 := bstep (se 2 (by rfl) ⟨2052018, by rfl⟩ : syracuseStep 5472049 = 4104037) B4104037
theorem B7296065 : Blo 2277435 7296065 := bstep (se 2 (by rfl) ⟨2736024, by rfl⟩ : syracuseStep 7296065 = 5472049) B5472049
theorem B4864043 : Blo 2277435 4864043 := bstep (se 1 (by rfl) ⟨3648032, by rfl⟩ : syracuseStep 4864043 = 7296065) B7296065
theorem B3242695 : Blo 2277435 3242695 := bstep (se 1 (by rfl) ⟨2432021, by rfl⟩ : syracuseStep 3242695 = 4864043) B4864043
theorem B4323593 : Blo 2277435 4323593 := bstep (se 2 (by rfl) ⟨1621347, by rfl⟩ : syracuseStep 4323593 = 3242695) B3242695
theorem B2882395 : Blo 2277435 2882395 := bstep (se 1 (by rfl) ⟨2161796, by rfl⟩ : syracuseStep 2882395 = 4323593) B4323593
theorem B3843193 : Blo 2277435 3843193 := bstep (se 2 (by rfl) ⟨1441197, by rfl⟩ : syracuseStep 3843193 = 2882395) B2882395
theorem B5124257 : Blo 2277435 5124257 := bstep (se 2 (by rfl) ⟨1921596, by rfl⟩ : syracuseStep 5124257 = 3843193) B3843193
theorem B3416171 : Blo 2277435 3416171 := bstep (se 1 (by rfl) ⟨2562128, by rfl⟩ : syracuseStep 3416171 = 5124257) B5124257
theorem B2277447 : Blo 2277435 2277447 := bstep (se 1 (by rfl) ⟨1708085, by rfl⟩ : syracuseStep 2277447 = 3416171) B3416171
theorem B2562133 : Blo 2277435 2562133 := bbase (se 8 (by rfl) ⟨15012, by rfl⟩ : syracuseStep 2562133 = 30025) (by norm_num)
theorem B3416177 : Blo 2277435 3416177 := bstep (se 2 (by rfl) ⟨1281066, by rfl⟩ : syracuseStep 3416177 = 2562133) B2562133
theorem B2277451 : Blo 2277435 2277451 := bstep (se 1 (by rfl) ⟨1708088, by rfl⟩ : syracuseStep 2277451 = 3416177) B3416177
theorem B2882405 : Blo 2277435 2882405 := bbase (se 4 (by rfl) ⟨270225, by rfl⟩ : syracuseStep 2882405 = 540451) (by norm_num)
theorem B7686413 : Blo 2277435 7686413 := bstep (se 3 (by rfl) ⟨1441202, by rfl⟩ : syracuseStep 7686413 = 2882405) B2882405
theorem B5124275 : Blo 2277435 5124275 := bstep (se 1 (by rfl) ⟨3843206, by rfl⟩ : syracuseStep 5124275 = 7686413) B7686413
theorem B3416183 : Blo 2277435 3416183 := bstep (se 1 (by rfl) ⟨2562137, by rfl⟩ : syracuseStep 3416183 = 5124275) B5124275
theorem B2277455 : Blo 2277435 2277455 := bstep (se 1 (by rfl) ⟨1708091, by rfl⟩ : syracuseStep 2277455 = 3416183) B3416183
theorem B3416189 : Blo 2277435 3416189 := bbase (se 3 (by rfl) ⟨640535, by rfl⟩ : syracuseStep 3416189 = 1281071) (by norm_num)
theorem B2277459 : Blo 2277435 2277459 := bstep (se 1 (by rfl) ⟨1708094, by rfl⟩ : syracuseStep 2277459 = 3416189) B3416189
theorem B5124293 : Blo 2277435 5124293 := bbase (se 4 (by rfl) ⟨480402, by rfl⟩ : syracuseStep 5124293 = 960805) (by norm_num)
theorem B3416195 : Blo 2277435 3416195 := bstep (se 1 (by rfl) ⟨2562146, by rfl⟩ : syracuseStep 3416195 = 5124293) B5124293
theorem B2277463 : Blo 2277435 2277463 := bstep (se 1 (by rfl) ⟨1708097, by rfl⟩ : syracuseStep 2277463 = 3416195) B3416195
theorem B2308541 : Blo 2277435 2308541 := bbase (se 3 (by rfl) ⟨432851, by rfl⟩ : syracuseStep 2308541 = 865703) (by norm_num)
theorem B6156109 : Blo 2277435 6156109 := bstep (se 3 (by rfl) ⟨1154270, by rfl⟩ : syracuseStep 6156109 = 2308541) B2308541
theorem B8208145 : Blo 2277435 8208145 := bstep (se 2 (by rfl) ⟨3078054, by rfl⟩ : syracuseStep 8208145 = 6156109) B6156109
theorem B10944193 : Blo 2277435 10944193 := bstep (se 2 (by rfl) ⟨4104072, by rfl⟩ : syracuseStep 10944193 = 8208145) B8208145
theorem B14592257 : Blo 2277435 14592257 := bstep (se 2 (by rfl) ⟨5472096, by rfl⟩ : syracuseStep 14592257 = 10944193) B10944193
theorem B9728171 : Blo 2277435 9728171 := bstep (se 1 (by rfl) ⟨7296128, by rfl⟩ : syracuseStep 9728171 = 14592257) B14592257
theorem B6485447 : Blo 2277435 6485447 := bstep (se 1 (by rfl) ⟨4864085, by rfl⟩ : syracuseStep 6485447 = 9728171) B9728171
theorem B4323631 : Blo 2277435 4323631 := bstep (se 1 (by rfl) ⟨3242723, by rfl⟩ : syracuseStep 4323631 = 6485447) B6485447
theorem B5764841 : Blo 2277435 5764841 := bstep (se 2 (by rfl) ⟨2161815, by rfl⟩ : syracuseStep 5764841 = 4323631) B4323631
theorem B3843227 : Blo 2277435 3843227 := bstep (se 1 (by rfl) ⟨2882420, by rfl⟩ : syracuseStep 3843227 = 5764841) B5764841
theorem B2562151 : Blo 2277435 2562151 := bstep (se 1 (by rfl) ⟨1921613, by rfl⟩ : syracuseStep 2562151 = 3843227) B3843227
theorem B3416201 : Blo 2277435 3416201 := bstep (se 2 (by rfl) ⟨1281075, by rfl⟩ : syracuseStep 3416201 = 2562151) B2562151
theorem B2277467 : Blo 2277435 2277467 := bstep (se 1 (by rfl) ⟨1708100, by rfl⟩ : syracuseStep 2277467 = 3416201) B3416201
theorem B11529701 : Blo 2277435 11529701 := bbase (se 4 (by rfl) ⟨1080909, by rfl⟩ : syracuseStep 11529701 = 2161819) (by norm_num)
theorem B7686467 : Blo 2277435 7686467 := bstep (se 1 (by rfl) ⟨5764850, by rfl⟩ : syracuseStep 7686467 = 11529701) B11529701
theorem B5124311 : Blo 2277435 5124311 := bstep (se 1 (by rfl) ⟨3843233, by rfl⟩ : syracuseStep 5124311 = 7686467) B7686467
theorem B3416207 : Blo 2277435 3416207 := bstep (se 1 (by rfl) ⟨2562155, by rfl⟩ : syracuseStep 3416207 = 5124311) B5124311
theorem B2277471 : Blo 2277435 2277471 := bstep (se 1 (by rfl) ⟨1708103, by rfl⟩ : syracuseStep 2277471 = 3416207) B3416207
theorem B3416213 : Blo 2277435 3416213 := bbase (se 6 (by rfl) ⟨80067, by rfl⟩ : syracuseStep 3416213 = 160135) (by norm_num)
theorem B2277475 : Blo 2277435 2277475 := bstep (se 1 (by rfl) ⟨1708106, by rfl⟩ : syracuseStep 2277475 = 3416213) B3416213
theorem B5472125 : Blo 2277435 5472125 := bbase (se 3 (by rfl) ⟨1026023, by rfl⟩ : syracuseStep 5472125 = 2052047) (by norm_num)
theorem B3648083 : Blo 2277435 3648083 := bstep (se 1 (by rfl) ⟨2736062, by rfl⟩ : syracuseStep 3648083 = 5472125) B5472125
theorem B9728221 : Blo 2277435 9728221 := bstep (se 3 (by rfl) ⟨1824041, by rfl⟩ : syracuseStep 9728221 = 3648083) B3648083
theorem B12970961 : Blo 2277435 12970961 := bstep (se 2 (by rfl) ⟨4864110, by rfl⟩ : syracuseStep 12970961 = 9728221) B9728221
theorem B8647307 : Blo 2277435 8647307 := bstep (se 1 (by rfl) ⟨6485480, by rfl⟩ : syracuseStep 8647307 = 12970961) B12970961
theorem B5764871 : Blo 2277435 5764871 := bstep (se 1 (by rfl) ⟨4323653, by rfl⟩ : syracuseStep 5764871 = 8647307) B8647307
theorem B3843247 : Blo 2277435 3843247 := bstep (se 1 (by rfl) ⟨2882435, by rfl⟩ : syracuseStep 3843247 = 5764871) B5764871
theorem B5124329 : Blo 2277435 5124329 := bstep (se 2 (by rfl) ⟨1921623, by rfl⟩ : syracuseStep 5124329 = 3843247) B3843247
theorem B3416219 : Blo 2277435 3416219 := bstep (se 1 (by rfl) ⟨2562164, by rfl⟩ : syracuseStep 3416219 = 5124329) B5124329
theorem B2277479 : Blo 2277435 2277479 := bstep (se 1 (by rfl) ⟨1708109, by rfl⟩ : syracuseStep 2277479 = 3416219) B3416219
theorem B2562169 : Blo 2277435 2562169 := bbase (se 2 (by rfl) ⟨960813, by rfl⟩ : syracuseStep 2562169 = 1921627) (by norm_num)
theorem B3416225 : Blo 2277435 3416225 := bstep (se 2 (by rfl) ⟨1281084, by rfl⟩ : syracuseStep 3416225 = 2562169) B2562169
theorem B2277483 : Blo 2277435 2277483 := bstep (se 1 (by rfl) ⟨1708112, by rfl⟩ : syracuseStep 2277483 = 3416225) B3416225
theorem B8765317 : Blo 2277435 8765317 := bbase (se 4 (by rfl) ⟨821748, by rfl⟩ : syracuseStep 8765317 = 1643497) (by norm_num)
theorem B11687089 : Blo 2277435 11687089 := bstep (se 2 (by rfl) ⟨4382658, by rfl⟩ : syracuseStep 11687089 = 8765317) B8765317
theorem B15582785 : Blo 2277435 15582785 := bstep (se 2 (by rfl) ⟨5843544, by rfl⟩ : syracuseStep 15582785 = 11687089) B11687089
theorem B166216373 : Blo 2277435 166216373 := bstep (se 5 (by rfl) ⟨7791392, by rfl⟩ : syracuseStep 166216373 = 15582785) B15582785
theorem B110810915 : Blo 2277435 110810915 := bstep (se 1 (by rfl) ⟨83108186, by rfl⟩ : syracuseStep 110810915 = 166216373) B166216373
theorem B73873943 : Blo 2277435 73873943 := bstep (se 1 (by rfl) ⟨55405457, by rfl⟩ : syracuseStep 73873943 = 110810915) B110810915
theorem B49249295 : Blo 2277435 49249295 := bstep (se 1 (by rfl) ⟨36936971, by rfl⟩ : syracuseStep 49249295 = 73873943) B73873943
theorem B32832863 : Blo 2277435 32832863 := bstep (se 1 (by rfl) ⟨24624647, by rfl⟩ : syracuseStep 32832863 = 49249295) B49249295
theorem B21888575 : Blo 2277435 21888575 := bstep (se 1 (by rfl) ⟨16416431, by rfl⟩ : syracuseStep 21888575 = 32832863) B32832863
theorem B14592383 : Blo 2277435 14592383 := bstep (se 1 (by rfl) ⟨10944287, by rfl⟩ : syracuseStep 14592383 = 21888575) B21888575
theorem B9728255 : Blo 2277435 9728255 := bstep (se 1 (by rfl) ⟨7296191, by rfl⟩ : syracuseStep 9728255 = 14592383) B14592383
theorem B6485503 : Blo 2277435 6485503 := bstep (se 1 (by rfl) ⟨4864127, by rfl⟩ : syracuseStep 6485503 = 9728255) B9728255
theorem B8647337 : Blo 2277435 8647337 := bstep (se 2 (by rfl) ⟨3242751, by rfl⟩ : syracuseStep 8647337 = 6485503) B6485503
theorem B5764891 : Blo 2277435 5764891 := bstep (se 1 (by rfl) ⟨4323668, by rfl⟩ : syracuseStep 5764891 = 8647337) B8647337
theorem B7686521 : Blo 2277435 7686521 := bstep (se 2 (by rfl) ⟨2882445, by rfl⟩ : syracuseStep 7686521 = 5764891) B5764891
theorem B5124347 : Blo 2277435 5124347 := bstep (se 1 (by rfl) ⟨3843260, by rfl⟩ : syracuseStep 5124347 = 7686521) B7686521
theorem B3416231 : Blo 2277435 3416231 := bstep (se 1 (by rfl) ⟨2562173, by rfl⟩ : syracuseStep 3416231 = 5124347) B5124347
theorem B2277487 : Blo 2277435 2277487 := bstep (se 1 (by rfl) ⟨1708115, by rfl⟩ : syracuseStep 2277487 = 3416231) B3416231
theorem B3416237 : Blo 2277435 3416237 := bbase (se 3 (by rfl) ⟨640544, by rfl⟩ : syracuseStep 3416237 = 1281089) (by norm_num)
theorem B2277491 : Blo 2277435 2277491 := bstep (se 1 (by rfl) ⟨1708118, by rfl⟩ : syracuseStep 2277491 = 3416237) B3416237
theorem B5124365 : Blo 2277435 5124365 := bbase (se 3 (by rfl) ⟨960818, by rfl⟩ : syracuseStep 5124365 = 1921637) (by norm_num)
theorem B3416243 : Blo 2277435 3416243 := bstep (se 1 (by rfl) ⟨2562182, by rfl⟩ : syracuseStep 3416243 = 5124365) B5124365
theorem B2277495 : Blo 2277435 2277495 := bstep (se 1 (by rfl) ⟨1708121, by rfl⟩ : syracuseStep 2277495 = 3416243) B3416243
theorem B2882461 : Blo 2277435 2882461 := bbase (se 3 (by rfl) ⟨540461, by rfl⟩ : syracuseStep 2882461 = 1080923) (by norm_num)
theorem B3843281 : Blo 2277435 3843281 := bstep (se 2 (by rfl) ⟨1441230, by rfl⟩ : syracuseStep 3843281 = 2882461) B2882461
theorem B2562187 : Blo 2277435 2562187 := bstep (se 1 (by rfl) ⟨1921640, by rfl⟩ : syracuseStep 2562187 = 3843281) B3843281
theorem B3416249 : Blo 2277435 3416249 := bstep (se 2 (by rfl) ⟨1281093, by rfl⟩ : syracuseStep 3416249 = 2562187) B2562187
theorem B2277499 : Blo 2277435 2277499 := bstep (se 1 (by rfl) ⟨1708124, by rfl⟩ : syracuseStep 2277499 = 3416249) B3416249
theorem B6925733 : Blo 2277435 6925733 := bbase (se 4 (by rfl) ⟨649287, by rfl⟩ : syracuseStep 6925733 = 1298575) (by norm_num)
theorem B4617155 : Blo 2277435 4617155 := bstep (se 1 (by rfl) ⟨3462866, by rfl⟩ : syracuseStep 4617155 = 6925733) B6925733
theorem B3078103 : Blo 2277435 3078103 := bstep (se 1 (by rfl) ⟨2308577, by rfl⟩ : syracuseStep 3078103 = 4617155) B4617155
theorem B4104137 : Blo 2277435 4104137 := bstep (se 2 (by rfl) ⟨1539051, by rfl⟩ : syracuseStep 4104137 = 3078103) B3078103
theorem B2736091 : Blo 2277435 2736091 := bstep (se 1 (by rfl) ⟨2052068, by rfl⟩ : syracuseStep 2736091 = 4104137) B4104137
theorem B3648121 : Blo 2277435 3648121 := bstep (se 2 (by rfl) ⟨1368045, by rfl⟩ : syracuseStep 3648121 = 2736091) B2736091
theorem B19456645 : Blo 2277435 19456645 := bstep (se 4 (by rfl) ⟨1824060, by rfl⟩ : syracuseStep 19456645 = 3648121) B3648121
theorem B25942193 : Blo 2277435 25942193 := bstep (se 2 (by rfl) ⟨9728322, by rfl⟩ : syracuseStep 25942193 = 19456645) B19456645
theorem B17294795 : Blo 2277435 17294795 := bstep (se 1 (by rfl) ⟨12971096, by rfl⟩ : syracuseStep 17294795 = 25942193) B25942193
theorem B11529863 : Blo 2277435 11529863 := bstep (se 1 (by rfl) ⟨8647397, by rfl⟩ : syracuseStep 11529863 = 17294795) B17294795
theorem B7686575 : Blo 2277435 7686575 := bstep (se 1 (by rfl) ⟨5764931, by rfl⟩ : syracuseStep 7686575 = 11529863) B11529863
theorem B5124383 : Blo 2277435 5124383 := bstep (se 1 (by rfl) ⟨3843287, by rfl⟩ : syracuseStep 5124383 = 7686575) B7686575
theorem B3416255 : Blo 2277435 3416255 := bstep (se 1 (by rfl) ⟨2562191, by rfl⟩ : syracuseStep 3416255 = 5124383) B5124383
theorem B2277503 : Blo 2277435 2277503 := bstep (se 1 (by rfl) ⟨1708127, by rfl⟩ : syracuseStep 2277503 = 3416255) B3416255
theorem B3416261 : Blo 2277435 3416261 := bbase (se 4 (by rfl) ⟨320274, by rfl⟩ : syracuseStep 3416261 = 640549) (by norm_num)
theorem B2277507 : Blo 2277435 2277507 := bstep (se 1 (by rfl) ⟨1708130, by rfl⟩ : syracuseStep 2277507 = 3416261) B3416261
theorem B3843301 : Blo 2277435 3843301 := bbase (se 4 (by rfl) ⟨360309, by rfl⟩ : syracuseStep 3843301 = 720619) (by norm_num)
theorem B5124401 : Blo 2277435 5124401 := bstep (se 2 (by rfl) ⟨1921650, by rfl⟩ : syracuseStep 5124401 = 3843301) B3843301
theorem B3416267 : Blo 2277435 3416267 := bstep (se 1 (by rfl) ⟨2562200, by rfl⟩ : syracuseStep 3416267 = 5124401) B5124401
theorem B2277511 : Blo 2277435 2277511 := bstep (se 1 (by rfl) ⟨1708133, by rfl⟩ : syracuseStep 2277511 = 3416267) B3416267
theorem B2562205 : Blo 2277435 2562205 := bbase (se 3 (by rfl) ⟨480413, by rfl⟩ : syracuseStep 2562205 = 960827) (by norm_num)
theorem B3416273 : Blo 2277435 3416273 := bstep (se 2 (by rfl) ⟨1281102, by rfl⟩ : syracuseStep 3416273 = 2562205) B2562205
theorem B2277515 : Blo 2277435 2277515 := bstep (se 1 (by rfl) ⟨1708136, by rfl⟩ : syracuseStep 2277515 = 3416273) B3416273
theorem B7686629 : Blo 2277435 7686629 := bbase (se 4 (by rfl) ⟨720621, by rfl⟩ : syracuseStep 7686629 = 1441243) (by norm_num)
theorem B5124419 : Blo 2277435 5124419 := bstep (se 1 (by rfl) ⟨3843314, by rfl⟩ : syracuseStep 5124419 = 7686629) B7686629
theorem B3416279 : Blo 2277435 3416279 := bstep (se 1 (by rfl) ⟨2562209, by rfl⟩ : syracuseStep 3416279 = 5124419) B5124419
theorem B2277519 : Blo 2277435 2277519 := bstep (se 1 (by rfl) ⟨1708139, by rfl⟩ : syracuseStep 2277519 = 3416279) B3416279
theorem B3416285 : Blo 2277435 3416285 := bbase (se 3 (by rfl) ⟨640553, by rfl⟩ : syracuseStep 3416285 = 1281107) (by norm_num)
theorem B2277523 : Blo 2277435 2277523 := bstep (se 1 (by rfl) ⟨1708142, by rfl⟩ : syracuseStep 2277523 = 3416285) B3416285
theorem B5124437 : Blo 2277435 5124437 := bbase (se 10 (by rfl) ⟨7506, by rfl⟩ : syracuseStep 5124437 = 15013) (by norm_num)
theorem B3416291 : Blo 2277435 3416291 := bstep (se 1 (by rfl) ⟨2562218, by rfl⟩ : syracuseStep 3416291 = 5124437) B5124437
theorem B2277527 : Blo 2277435 2277527 := bstep (se 1 (by rfl) ⟨1708145, by rfl⟩ : syracuseStep 2277527 = 3416291) B3416291
theorem B4930589 : Blo 2277435 4930589 := bbase (se 3 (by rfl) ⟨924485, by rfl⟩ : syracuseStep 4930589 = 1848971) (by norm_num)
theorem B13148237 : Blo 2277435 13148237 := bstep (se 3 (by rfl) ⟨2465294, by rfl⟩ : syracuseStep 13148237 = 4930589) B4930589
theorem B8765491 : Blo 2277435 8765491 := bstep (se 1 (by rfl) ⟨6574118, by rfl⟩ : syracuseStep 8765491 = 13148237) B13148237
theorem B11687321 : Blo 2277435 11687321 := bstep (se 2 (by rfl) ⟨4382745, by rfl⟩ : syracuseStep 11687321 = 8765491) B8765491
theorem B7791547 : Blo 2277435 7791547 := bstep (se 1 (by rfl) ⟨5843660, by rfl⟩ : syracuseStep 7791547 = 11687321) B11687321
theorem B10388729 : Blo 2277435 10388729 := bstep (se 2 (by rfl) ⟨3895773, by rfl⟩ : syracuseStep 10388729 = 7791547) B7791547
theorem B6925819 : Blo 2277435 6925819 := bstep (se 1 (by rfl) ⟨5194364, by rfl⟩ : syracuseStep 6925819 = 10388729) B10388729
theorem B9234425 : Blo 2277435 9234425 := bstep (se 2 (by rfl) ⟨3462909, by rfl⟩ : syracuseStep 9234425 = 6925819) B6925819
theorem B6156283 : Blo 2277435 6156283 := bstep (se 1 (by rfl) ⟨4617212, by rfl⟩ : syracuseStep 6156283 = 9234425) B9234425
theorem B8208377 : Blo 2277435 8208377 := bstep (se 2 (by rfl) ⟨3078141, by rfl⟩ : syracuseStep 8208377 = 6156283) B6156283
theorem B5472251 : Blo 2277435 5472251 := bstep (se 1 (by rfl) ⟨4104188, by rfl⟩ : syracuseStep 5472251 = 8208377) B8208377
theorem B3648167 : Blo 2277435 3648167 := bstep (se 1 (by rfl) ⟨2736125, by rfl⟩ : syracuseStep 3648167 = 5472251) B5472251
theorem B2432111 : Blo 2277435 2432111 := bstep (se 1 (by rfl) ⟨1824083, by rfl⟩ : syracuseStep 2432111 = 3648167) B3648167
theorem B6485629 : Blo 2277435 6485629 := bstep (se 3 (by rfl) ⟨1216055, by rfl⟩ : syracuseStep 6485629 = 2432111) B2432111
theorem B8647505 : Blo 2277435 8647505 := bstep (se 2 (by rfl) ⟨3242814, by rfl⟩ : syracuseStep 8647505 = 6485629) B6485629
theorem B5765003 : Blo 2277435 5765003 := bstep (se 1 (by rfl) ⟨4323752, by rfl⟩ : syracuseStep 5765003 = 8647505) B8647505
theorem B3843335 : Blo 2277435 3843335 := bstep (se 1 (by rfl) ⟨2882501, by rfl⟩ : syracuseStep 3843335 = 5765003) B5765003
theorem B2562223 : Blo 2277435 2562223 := bstep (se 1 (by rfl) ⟨1921667, by rfl⟩ : syracuseStep 2562223 = 3843335) B3843335
theorem B3416297 : Blo 2277435 3416297 := bstep (se 2 (by rfl) ⟨1281111, by rfl⟩ : syracuseStep 3416297 = 2562223) B2562223
theorem B2277531 : Blo 2277435 2277531 := bstep (se 1 (by rfl) ⟨1708148, by rfl⟩ : syracuseStep 2277531 = 3416297) B3416297
theorem B43778069 : Blo 2277435 43778069 := bbase (se 6 (by rfl) ⟨1026048, by rfl⟩ : syracuseStep 43778069 = 2052097) (by norm_num)
theorem B29185379 : Blo 2277435 29185379 := bstep (se 1 (by rfl) ⟨21889034, by rfl⟩ : syracuseStep 29185379 = 43778069) B43778069
theorem B19456919 : Blo 2277435 19456919 := bstep (se 1 (by rfl) ⟨14592689, by rfl⟩ : syracuseStep 19456919 = 29185379) B29185379
theorem B12971279 : Blo 2277435 12971279 := bstep (se 1 (by rfl) ⟨9728459, by rfl⟩ : syracuseStep 12971279 = 19456919) B19456919
theorem B8647519 : Blo 2277435 8647519 := bstep (se 1 (by rfl) ⟨6485639, by rfl⟩ : syracuseStep 8647519 = 12971279) B12971279
theorem B11530025 : Blo 2277435 11530025 := bstep (se 2 (by rfl) ⟨4323759, by rfl⟩ : syracuseStep 11530025 = 8647519) B8647519
theorem B7686683 : Blo 2277435 7686683 := bstep (se 1 (by rfl) ⟨5765012, by rfl⟩ : syracuseStep 7686683 = 11530025) B11530025
theorem B5124455 : Blo 2277435 5124455 := bstep (se 1 (by rfl) ⟨3843341, by rfl⟩ : syracuseStep 5124455 = 7686683) B7686683
theorem B3416303 : Blo 2277435 3416303 := bstep (se 1 (by rfl) ⟨2562227, by rfl⟩ : syracuseStep 3416303 = 5124455) B5124455
theorem B2277535 : Blo 2277435 2277535 := bstep (se 1 (by rfl) ⟨1708151, by rfl⟩ : syracuseStep 2277535 = 3416303) B3416303
theorem B3416309 : Blo 2277435 3416309 := bbase (se 5 (by rfl) ⟨160139, by rfl⟩ : syracuseStep 3416309 = 320279) (by norm_num)
theorem B2277539 : Blo 2277435 2277539 := bstep (se 1 (by rfl) ⟨1708154, by rfl⟩ : syracuseStep 2277539 = 3416309) B3416309
theorem B3510173 : Blo 2277435 3510173 := bbase (se 3 (by rfl) ⟨658157, by rfl⟩ : syracuseStep 3510173 = 1316315) (by norm_num)
theorem B9360461 : Blo 2277435 9360461 := bstep (se 3 (by rfl) ⟨1755086, by rfl⟩ : syracuseStep 9360461 = 3510173) B3510173
theorem B6240307 : Blo 2277435 6240307 := bstep (se 1 (by rfl) ⟨4680230, by rfl⟩ : syracuseStep 6240307 = 9360461) B9360461
theorem B8320409 : Blo 2277435 8320409 := bstep (se 2 (by rfl) ⟨3120153, by rfl⟩ : syracuseStep 8320409 = 6240307) B6240307
theorem B5546939 : Blo 2277435 5546939 := bstep (se 1 (by rfl) ⟨4160204, by rfl⟩ : syracuseStep 5546939 = 8320409) B8320409
theorem B59167349 : Blo 2277435 59167349 := bstep (se 5 (by rfl) ⟨2773469, by rfl⟩ : syracuseStep 59167349 = 5546939) B5546939
theorem B39444899 : Blo 2277435 39444899 := bstep (se 1 (by rfl) ⟨29583674, by rfl⟩ : syracuseStep 39444899 = 59167349) B59167349
theorem B105186397 : Blo 2277435 105186397 := bstep (se 3 (by rfl) ⟨19722449, by rfl⟩ : syracuseStep 105186397 = 39444899) B39444899
theorem B140248529 : Blo 2277435 140248529 := bstep (se 2 (by rfl) ⟨52593198, by rfl⟩ : syracuseStep 140248529 = 105186397) B105186397
theorem B93499019 : Blo 2277435 93499019 := bstep (se 1 (by rfl) ⟨70124264, by rfl⟩ : syracuseStep 93499019 = 140248529) B140248529
theorem B62332679 : Blo 2277435 62332679 := bstep (se 1 (by rfl) ⟨46749509, by rfl⟩ : syracuseStep 62332679 = 93499019) B93499019
theorem B41555119 : Blo 2277435 41555119 := bstep (se 1 (by rfl) ⟨31166339, by rfl⟩ : syracuseStep 41555119 = 62332679) B62332679
theorem B55406825 : Blo 2277435 55406825 := bstep (se 2 (by rfl) ⟨20777559, by rfl⟩ : syracuseStep 55406825 = 41555119) B41555119
theorem B36937883 : Blo 2277435 36937883 := bstep (se 1 (by rfl) ⟨27703412, by rfl⟩ : syracuseStep 36937883 = 55406825) B55406825
theorem B24625255 : Blo 2277435 24625255 := bstep (se 1 (by rfl) ⟨18468941, by rfl⟩ : syracuseStep 24625255 = 36937883) B36937883
theorem B32833673 : Blo 2277435 32833673 := bstep (se 2 (by rfl) ⟨12312627, by rfl⟩ : syracuseStep 32833673 = 24625255) B24625255
theorem B21889115 : Blo 2277435 21889115 := bstep (se 1 (by rfl) ⟨16416836, by rfl⟩ : syracuseStep 21889115 = 32833673) B32833673
theorem B14592743 : Blo 2277435 14592743 := bstep (se 1 (by rfl) ⟨10944557, by rfl⟩ : syracuseStep 14592743 = 21889115) B21889115
theorem B9728495 : Blo 2277435 9728495 := bstep (se 1 (by rfl) ⟨7296371, by rfl⟩ : syracuseStep 9728495 = 14592743) B14592743
theorem B6485663 : Blo 2277435 6485663 := bstep (se 1 (by rfl) ⟨4864247, by rfl⟩ : syracuseStep 6485663 = 9728495) B9728495
theorem B4323775 : Blo 2277435 4323775 := bstep (se 1 (by rfl) ⟨3242831, by rfl⟩ : syracuseStep 4323775 = 6485663) B6485663
theorem B5765033 : Blo 2277435 5765033 := bstep (se 2 (by rfl) ⟨2161887, by rfl⟩ : syracuseStep 5765033 = 4323775) B4323775
theorem B3843355 : Blo 2277435 3843355 := bstep (se 1 (by rfl) ⟨2882516, by rfl⟩ : syracuseStep 3843355 = 5765033) B5765033
theorem B5124473 : Blo 2277435 5124473 := bstep (se 2 (by rfl) ⟨1921677, by rfl⟩ : syracuseStep 5124473 = 3843355) B3843355
theorem B3416315 : Blo 2277435 3416315 := bstep (se 1 (by rfl) ⟨2562236, by rfl⟩ : syracuseStep 3416315 = 5124473) B5124473
theorem B2277543 : Blo 2277435 2277543 := bstep (se 1 (by rfl) ⟨1708157, by rfl⟩ : syracuseStep 2277543 = 3416315) B3416315
theorem B2562241 : Blo 2277435 2562241 := bbase (se 2 (by rfl) ⟨960840, by rfl⟩ : syracuseStep 2562241 = 1921681) (by norm_num)
theorem B3416321 : Blo 2277435 3416321 := bstep (se 2 (by rfl) ⟨1281120, by rfl⟩ : syracuseStep 3416321 = 2562241) B2562241
theorem B2277547 : Blo 2277435 2277547 := bstep (se 1 (by rfl) ⟨1708160, by rfl⟩ : syracuseStep 2277547 = 3416321) B3416321
theorem B5765053 : Blo 2277435 5765053 := bbase (se 3 (by rfl) ⟨1080947, by rfl⟩ : syracuseStep 5765053 = 2161895) (by norm_num)
theorem B7686737 : Blo 2277435 7686737 := bstep (se 2 (by rfl) ⟨2882526, by rfl⟩ : syracuseStep 7686737 = 5765053) B5765053
theorem B5124491 : Blo 2277435 5124491 := bstep (se 1 (by rfl) ⟨3843368, by rfl⟩ : syracuseStep 5124491 = 7686737) B7686737
theorem B3416327 : Blo 2277435 3416327 := bstep (se 1 (by rfl) ⟨2562245, by rfl⟩ : syracuseStep 3416327 = 5124491) B5124491
theorem B2277551 : Blo 2277435 2277551 := bstep (se 1 (by rfl) ⟨1708163, by rfl⟩ : syracuseStep 2277551 = 3416327) B3416327
theorem B3416333 : Blo 2277435 3416333 := bbase (se 3 (by rfl) ⟨640562, by rfl⟩ : syracuseStep 3416333 = 1281125) (by norm_num)
theorem B2277555 : Blo 2277435 2277555 := bstep (se 1 (by rfl) ⟨1708166, by rfl⟩ : syracuseStep 2277555 = 3416333) B3416333
theorem B5124509 : Blo 2277435 5124509 := bbase (se 3 (by rfl) ⟨960845, by rfl⟩ : syracuseStep 5124509 = 1921691) (by norm_num)
theorem B3416339 : Blo 2277435 3416339 := bstep (se 1 (by rfl) ⟨2562254, by rfl⟩ : syracuseStep 3416339 = 5124509) B5124509
theorem B2277559 : Blo 2277435 2277559 := bstep (se 1 (by rfl) ⟨1708169, by rfl⟩ : syracuseStep 2277559 = 3416339) B3416339
theorem B3843389 : Blo 2277435 3843389 := bbase (se 3 (by rfl) ⟨720635, by rfl⟩ : syracuseStep 3843389 = 1441271) (by norm_num)
theorem B2562259 : Blo 2277435 2562259 := bstep (se 1 (by rfl) ⟨1921694, by rfl⟩ : syracuseStep 2562259 = 3843389) B3843389
theorem B3416345 : Blo 2277435 3416345 := bstep (se 2 (by rfl) ⟨1281129, by rfl⟩ : syracuseStep 3416345 = 2562259) B2562259
theorem B2277563 : Blo 2277435 2277563 := bstep (se 1 (by rfl) ⟨1708172, by rfl⟩ : syracuseStep 2277563 = 3416345) B3416345
theorem B2432149 : Blo 2277435 2432149 := bbase (se 6 (by rfl) ⟨57003, by rfl⟩ : syracuseStep 2432149 = 114007) (by norm_num)
theorem B12971461 : Blo 2277435 12971461 := bstep (se 4 (by rfl) ⟨1216074, by rfl⟩ : syracuseStep 12971461 = 2432149) B2432149
theorem B17295281 : Blo 2277435 17295281 := bstep (se 2 (by rfl) ⟨6485730, by rfl⟩ : syracuseStep 17295281 = 12971461) B12971461
theorem B11530187 : Blo 2277435 11530187 := bstep (se 1 (by rfl) ⟨8647640, by rfl⟩ : syracuseStep 11530187 = 17295281) B17295281
theorem B7686791 : Blo 2277435 7686791 := bstep (se 1 (by rfl) ⟨5765093, by rfl⟩ : syracuseStep 7686791 = 11530187) B11530187
theorem B5124527 : Blo 2277435 5124527 := bstep (se 1 (by rfl) ⟨3843395, by rfl⟩ : syracuseStep 5124527 = 7686791) B7686791
theorem B3416351 : Blo 2277435 3416351 := bstep (se 1 (by rfl) ⟨2562263, by rfl⟩ : syracuseStep 3416351 = 5124527) B5124527
theorem B2277567 : Blo 2277435 2277567 := bstep (se 1 (by rfl) ⟨1708175, by rfl⟩ : syracuseStep 2277567 = 3416351) B3416351
theorem B3416357 : Blo 2277435 3416357 := bbase (se 4 (by rfl) ⟨320283, by rfl⟩ : syracuseStep 3416357 = 640567) (by norm_num)
theorem B2277571 : Blo 2277435 2277571 := bstep (se 1 (by rfl) ⟨1708178, by rfl⟩ : syracuseStep 2277571 = 3416357) B3416357
theorem B2882557 : Blo 2277435 2882557 := bbase (se 3 (by rfl) ⟨540479, by rfl⟩ : syracuseStep 2882557 = 1080959) (by norm_num)
theorem B3843409 : Blo 2277435 3843409 := bstep (se 2 (by rfl) ⟨1441278, by rfl⟩ : syracuseStep 3843409 = 2882557) B2882557
theorem B5124545 : Blo 2277435 5124545 := bstep (se 2 (by rfl) ⟨1921704, by rfl⟩ : syracuseStep 5124545 = 3843409) B3843409
theorem B3416363 : Blo 2277435 3416363 := bstep (se 1 (by rfl) ⟨2562272, by rfl⟩ : syracuseStep 3416363 = 5124545) B5124545
theorem B2277575 : Blo 2277435 2277575 := bstep (se 1 (by rfl) ⟨1708181, by rfl⟩ : syracuseStep 2277575 = 3416363) B3416363
theorem B2562277 : Blo 2277435 2562277 := bbase (se 4 (by rfl) ⟨240213, by rfl⟩ : syracuseStep 2562277 = 480427) (by norm_num)
theorem B3416369 : Blo 2277435 3416369 := bstep (se 2 (by rfl) ⟨1281138, by rfl⟩ : syracuseStep 3416369 = 2562277) B2562277
theorem B2277579 : Blo 2277435 2277579 := bstep (se 1 (by rfl) ⟨1708184, by rfl⟩ : syracuseStep 2277579 = 3416369) B3416369
theorem B4864333 : Blo 2277435 4864333 := bbase (se 3 (by rfl) ⟨912062, by rfl⟩ : syracuseStep 4864333 = 1824125) (by norm_num)
theorem B6485777 : Blo 2277435 6485777 := bstep (se 2 (by rfl) ⟨2432166, by rfl⟩ : syracuseStep 6485777 = 4864333) B4864333
theorem B4323851 : Blo 2277435 4323851 := bstep (se 1 (by rfl) ⟨3242888, by rfl⟩ : syracuseStep 4323851 = 6485777) B6485777
theorem B2882567 : Blo 2277435 2882567 := bstep (se 1 (by rfl) ⟨2161925, by rfl⟩ : syracuseStep 2882567 = 4323851) B4323851
theorem B7686845 : Blo 2277435 7686845 := bstep (se 3 (by rfl) ⟨1441283, by rfl⟩ : syracuseStep 7686845 = 2882567) B2882567
theorem B5124563 : Blo 2277435 5124563 := bstep (se 1 (by rfl) ⟨3843422, by rfl⟩ : syracuseStep 5124563 = 7686845) B7686845
theorem B3416375 : Blo 2277435 3416375 := bstep (se 1 (by rfl) ⟨2562281, by rfl⟩ : syracuseStep 3416375 = 5124563) B5124563
theorem B2277583 : Blo 2277435 2277583 := bstep (se 1 (by rfl) ⟨1708187, by rfl⟩ : syracuseStep 2277583 = 3416375) B3416375
theorem B3416381 : Blo 2277435 3416381 := bbase (se 3 (by rfl) ⟨640571, by rfl⟩ : syracuseStep 3416381 = 1281143) (by norm_num)
theorem B2277587 : Blo 2277435 2277587 := bstep (se 1 (by rfl) ⟨1708190, by rfl⟩ : syracuseStep 2277587 = 3416381) B3416381
theorem B5124581 : Blo 2277435 5124581 := bbase (se 4 (by rfl) ⟨480429, by rfl⟩ : syracuseStep 5124581 = 960859) (by norm_num)
theorem B3416387 : Blo 2277435 3416387 := bstep (se 1 (by rfl) ⟨2562290, by rfl⟩ : syracuseStep 3416387 = 5124581) B5124581
theorem B2277591 : Blo 2277435 2277591 := bstep (se 1 (by rfl) ⟨1708193, by rfl⟩ : syracuseStep 2277591 = 3416387) B3416387
theorem B5765165 : Blo 2277435 5765165 := bbase (se 3 (by rfl) ⟨1080968, by rfl⟩ : syracuseStep 5765165 = 2161937) (by norm_num)
theorem B3843443 : Blo 2277435 3843443 := bstep (se 1 (by rfl) ⟨2882582, by rfl⟩ : syracuseStep 3843443 = 5765165) B5765165
theorem B2562295 : Blo 2277435 2562295 := bstep (se 1 (by rfl) ⟨1921721, by rfl⟩ : syracuseStep 2562295 = 3843443) B3843443
theorem B3416393 : Blo 2277435 3416393 := bstep (se 2 (by rfl) ⟨1281147, by rfl⟩ : syracuseStep 3416393 = 2562295) B2562295
theorem B2277595 : Blo 2277435 2277595 := bstep (se 1 (by rfl) ⟨1708196, by rfl⟩ : syracuseStep 2277595 = 3416393) B3416393
theorem B18469397 : Blo 2277435 18469397 := bbase (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) (by norm_num)
theorem B12312931 : Blo 2277435 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B16417241 : Blo 2277435 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B10944827 : Blo 2277435 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B7296551 : Blo 2277435 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B4864367 : Blo 2277435 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B3242911 : Blo 2277435 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B4323881 : Blo 2277435 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B11530349 : Blo 2277435 11530349 := bstep (se 3 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 11530349 = 4323881) B4323881
theorem B7686899 : Blo 2277435 7686899 := bstep (se 1 (by rfl) ⟨5765174, by rfl⟩ : syracuseStep 7686899 = 11530349) B11530349
theorem B5124599 : Blo 2277435 5124599 := bstep (se 1 (by rfl) ⟨3843449, by rfl⟩ : syracuseStep 5124599 = 7686899) B7686899
theorem B3416399 : Blo 2277435 3416399 := bstep (se 1 (by rfl) ⟨2562299, by rfl⟩ : syracuseStep 3416399 = 5124599) B5124599
theorem B2277599 : Blo 2277435 2277599 := bstep (se 1 (by rfl) ⟨1708199, by rfl⟩ : syracuseStep 2277599 = 3416399) B3416399
theorem B3416405 : Blo 2277435 3416405 := bbase (se 10 (by rfl) ⟨5004, by rfl⟩ : syracuseStep 3416405 = 10009) (by norm_num)
theorem B2277603 : Blo 2277435 2277603 := bstep (se 1 (by rfl) ⟨1708202, by rfl⟩ : syracuseStep 2277603 = 3416405) B3416405
theorem B6485845 : Blo 2277435 6485845 := bbase (se 9 (by rfl) ⟨19001, by rfl⟩ : syracuseStep 6485845 = 38003) (by norm_num)
theorem B8647793 : Blo 2277435 8647793 := bstep (se 2 (by rfl) ⟨3242922, by rfl⟩ : syracuseStep 8647793 = 6485845) B6485845
theorem B5765195 : Blo 2277435 5765195 := bstep (se 1 (by rfl) ⟨4323896, by rfl⟩ : syracuseStep 5765195 = 8647793) B8647793
theorem B3843463 : Blo 2277435 3843463 := bstep (se 1 (by rfl) ⟨2882597, by rfl⟩ : syracuseStep 3843463 = 5765195) B5765195
theorem B5124617 : Blo 2277435 5124617 := bstep (se 2 (by rfl) ⟨1921731, by rfl⟩ : syracuseStep 5124617 = 3843463) B3843463
theorem B3416411 : Blo 2277435 3416411 := bstep (se 1 (by rfl) ⟨2562308, by rfl⟩ : syracuseStep 3416411 = 5124617) B5124617
theorem B2277607 : Blo 2277435 2277607 := bstep (se 1 (by rfl) ⟨1708205, by rfl⟩ : syracuseStep 2277607 = 3416411) B3416411
theorem B2562313 : Blo 2277435 2562313 := bbase (se 2 (by rfl) ⟨960867, by rfl⟩ : syracuseStep 2562313 = 1921735) (by norm_num)
theorem B3416417 : Blo 2277435 3416417 := bstep (se 2 (by rfl) ⟨1281156, by rfl⟩ : syracuseStep 3416417 = 2562313) B2562313
theorem B2277611 : Blo 2277435 2277611 := bstep (se 1 (by rfl) ⟨1708208, by rfl⟩ : syracuseStep 2277611 = 3416417) B3416417
theorem B8208677 : Blo 2277435 8208677 := bbase (se 4 (by rfl) ⟨769563, by rfl⟩ : syracuseStep 8208677 = 1539127) (by norm_num)
theorem B5472451 : Blo 2277435 5472451 := bstep (se 1 (by rfl) ⟨4104338, by rfl⟩ : syracuseStep 5472451 = 8208677) B8208677
theorem B29186405 : Blo 2277435 29186405 := bstep (se 4 (by rfl) ⟨2736225, by rfl⟩ : syracuseStep 29186405 = 5472451) B5472451
theorem B19457603 : Blo 2277435 19457603 := bstep (se 1 (by rfl) ⟨14593202, by rfl⟩ : syracuseStep 19457603 = 29186405) B29186405
theorem B12971735 : Blo 2277435 12971735 := bstep (se 1 (by rfl) ⟨9728801, by rfl⟩ : syracuseStep 12971735 = 19457603) B19457603
theorem B8647823 : Blo 2277435 8647823 := bstep (se 1 (by rfl) ⟨6485867, by rfl⟩ : syracuseStep 8647823 = 12971735) B12971735
theorem B5765215 : Blo 2277435 5765215 := bstep (se 1 (by rfl) ⟨4323911, by rfl⟩ : syracuseStep 5765215 = 8647823) B8647823
theorem B7686953 : Blo 2277435 7686953 := bstep (se 2 (by rfl) ⟨2882607, by rfl⟩ : syracuseStep 7686953 = 5765215) B5765215
theorem B5124635 : Blo 2277435 5124635 := bstep (se 1 (by rfl) ⟨3843476, by rfl⟩ : syracuseStep 5124635 = 7686953) B7686953
theorem B3416423 : Blo 2277435 3416423 := bstep (se 1 (by rfl) ⟨2562317, by rfl⟩ : syracuseStep 3416423 = 5124635) B5124635
theorem B2277615 : Blo 2277435 2277615 := bstep (se 1 (by rfl) ⟨1708211, by rfl⟩ : syracuseStep 2277615 = 3416423) B3416423
theorem B3416429 : Blo 2277435 3416429 := bbase (se 3 (by rfl) ⟨640580, by rfl⟩ : syracuseStep 3416429 = 1281161) (by norm_num)
theorem B2277619 : Blo 2277435 2277619 := bstep (se 1 (by rfl) ⟨1708214, by rfl⟩ : syracuseStep 2277619 = 3416429) B3416429
theorem B5124653 : Blo 2277435 5124653 := bbase (se 3 (by rfl) ⟨960872, by rfl⟩ : syracuseStep 5124653 = 1921745) (by norm_num)
theorem B3416435 : Blo 2277435 3416435 := bstep (se 1 (by rfl) ⟨2562326, by rfl⟩ : syracuseStep 3416435 = 5124653) B5124653
theorem B2277623 : Blo 2277435 2277623 := bstep (se 1 (by rfl) ⟨1708217, by rfl⟩ : syracuseStep 2277623 = 3416435) B3416435
theorem B11094293 : Blo 2277435 11094293 := bbase (se 6 (by rfl) ⟨260022, by rfl⟩ : syracuseStep 11094293 = 520045) (by norm_num)
theorem B7396195 : Blo 2277435 7396195 := bstep (se 1 (by rfl) ⟨5547146, by rfl⟩ : syracuseStep 7396195 = 11094293) B11094293
theorem B9861593 : Blo 2277435 9861593 := bstep (se 2 (by rfl) ⟨3698097, by rfl⟩ : syracuseStep 9861593 = 7396195) B7396195
theorem B26297581 : Blo 2277435 26297581 := bstep (se 3 (by rfl) ⟨4930796, by rfl⟩ : syracuseStep 26297581 = 9861593) B9861593
theorem B35063441 : Blo 2277435 35063441 := bstep (se 2 (by rfl) ⟨13148790, by rfl⟩ : syracuseStep 35063441 = 26297581) B26297581
theorem B23375627 : Blo 2277435 23375627 := bstep (se 1 (by rfl) ⟨17531720, by rfl⟩ : syracuseStep 23375627 = 35063441) B35063441
theorem B15583751 : Blo 2277435 15583751 := bstep (se 1 (by rfl) ⟨11687813, by rfl⟩ : syracuseStep 15583751 = 23375627) B23375627
theorem B10389167 : Blo 2277435 10389167 := bstep (se 1 (by rfl) ⟨7791875, by rfl⟩ : syracuseStep 10389167 = 15583751) B15583751
theorem B6926111 : Blo 2277435 6926111 := bstep (se 1 (by rfl) ⟨5194583, by rfl⟩ : syracuseStep 6926111 = 10389167) B10389167
theorem B4617407 : Blo 2277435 4617407 := bstep (se 1 (by rfl) ⟨3463055, by rfl⟩ : syracuseStep 4617407 = 6926111) B6926111
theorem B3078271 : Blo 2277435 3078271 := bstep (se 1 (by rfl) ⟨2308703, by rfl⟩ : syracuseStep 3078271 = 4617407) B4617407
theorem B4104361 : Blo 2277435 4104361 := bstep (se 2 (by rfl) ⟨1539135, by rfl⟩ : syracuseStep 4104361 = 3078271) B3078271
theorem B21889925 : Blo 2277435 21889925 := bstep (se 4 (by rfl) ⟨2052180, by rfl⟩ : syracuseStep 21889925 = 4104361) B4104361
theorem B14593283 : Blo 2277435 14593283 := bstep (se 1 (by rfl) ⟨10944962, by rfl⟩ : syracuseStep 14593283 = 21889925) B21889925
theorem B9728855 : Blo 2277435 9728855 := bstep (se 1 (by rfl) ⟨7296641, by rfl⟩ : syracuseStep 9728855 = 14593283) B14593283
theorem B6485903 : Blo 2277435 6485903 := bstep (se 1 (by rfl) ⟨4864427, by rfl⟩ : syracuseStep 6485903 = 9728855) B9728855
theorem B4323935 : Blo 2277435 4323935 := bstep (se 1 (by rfl) ⟨3242951, by rfl⟩ : syracuseStep 4323935 = 6485903) B6485903
theorem B2882623 : Blo 2277435 2882623 := bstep (se 1 (by rfl) ⟨2161967, by rfl⟩ : syracuseStep 2882623 = 4323935) B4323935
theorem B3843497 : Blo 2277435 3843497 := bstep (se 2 (by rfl) ⟨1441311, by rfl⟩ : syracuseStep 3843497 = 2882623) B2882623
theorem B2562331 : Blo 2277435 2562331 := bstep (se 1 (by rfl) ⟨1921748, by rfl⟩ : syracuseStep 2562331 = 3843497) B3843497
theorem B3416441 : Blo 2277435 3416441 := bstep (se 2 (by rfl) ⟨1281165, by rfl⟩ : syracuseStep 3416441 = 2562331) B2562331
theorem B2277627 : Blo 2277435 2277627 := bstep (se 1 (by rfl) ⟨1708220, by rfl⟩ : syracuseStep 2277627 = 3416441) B3416441
theorem B38915477 : Blo 2277435 38915477 := bbase (se 6 (by rfl) ⟨912081, by rfl⟩ : syracuseStep 38915477 = 1824163) (by norm_num)
theorem B25943651 : Blo 2277435 25943651 := bstep (se 1 (by rfl) ⟨19457738, by rfl⟩ : syracuseStep 25943651 = 38915477) B38915477
theorem B17295767 : Blo 2277435 17295767 := bstep (se 1 (by rfl) ⟨12971825, by rfl⟩ : syracuseStep 17295767 = 25943651) B25943651
theorem B11530511 : Blo 2277435 11530511 := bstep (se 1 (by rfl) ⟨8647883, by rfl⟩ : syracuseStep 11530511 = 17295767) B17295767
theorem B7687007 : Blo 2277435 7687007 := bstep (se 1 (by rfl) ⟨5765255, by rfl⟩ : syracuseStep 7687007 = 11530511) B11530511
theorem B5124671 : Blo 2277435 5124671 := bstep (se 1 (by rfl) ⟨3843503, by rfl⟩ : syracuseStep 5124671 = 7687007) B7687007
theorem B3416447 : Blo 2277435 3416447 := bstep (se 1 (by rfl) ⟨2562335, by rfl⟩ : syracuseStep 3416447 = 5124671) B5124671
theorem B2277631 : Blo 2277435 2277631 := bstep (se 1 (by rfl) ⟨1708223, by rfl⟩ : syracuseStep 2277631 = 3416447) B3416447
theorem B3416453 : Blo 2277435 3416453 := bbase (se 4 (by rfl) ⟨320292, by rfl⟩ : syracuseStep 3416453 = 640585) (by norm_num)
theorem B2277635 : Blo 2277435 2277635 := bstep (se 1 (by rfl) ⟨1708226, by rfl⟩ : syracuseStep 2277635 = 3416453) B3416453
theorem B3843517 : Blo 2277435 3843517 := bbase (se 3 (by rfl) ⟨720659, by rfl⟩ : syracuseStep 3843517 = 1441319) (by norm_num)
theorem B5124689 : Blo 2277435 5124689 := bstep (se 2 (by rfl) ⟨1921758, by rfl⟩ : syracuseStep 5124689 = 3843517) B3843517
theorem B3416459 : Blo 2277435 3416459 := bstep (se 1 (by rfl) ⟨2562344, by rfl⟩ : syracuseStep 3416459 = 5124689) B5124689
theorem B2277639 : Blo 2277435 2277639 := bstep (se 1 (by rfl) ⟨1708229, by rfl⟩ : syracuseStep 2277639 = 3416459) B3416459
theorem B2562349 : Blo 2277435 2562349 := bbase (se 3 (by rfl) ⟨480440, by rfl⟩ : syracuseStep 2562349 = 960881) (by norm_num)
theorem B3416465 : Blo 2277435 3416465 := bstep (se 2 (by rfl) ⟨1281174, by rfl⟩ : syracuseStep 3416465 = 2562349) B2562349
theorem B2277643 : Blo 2277435 2277643 := bstep (se 1 (by rfl) ⟨1708232, by rfl⟩ : syracuseStep 2277643 = 3416465) B3416465
theorem B7687061 : Blo 2277435 7687061 := bbase (se 6 (by rfl) ⟨180165, by rfl⟩ : syracuseStep 7687061 = 360331) (by norm_num)
theorem B5124707 : Blo 2277435 5124707 := bstep (se 1 (by rfl) ⟨3843530, by rfl⟩ : syracuseStep 5124707 = 7687061) B7687061
theorem B3416471 : Blo 2277435 3416471 := bstep (se 1 (by rfl) ⟨2562353, by rfl⟩ : syracuseStep 3416471 = 5124707) B5124707
theorem B2277647 : Blo 2277435 2277647 := bstep (se 1 (by rfl) ⟨1708235, by rfl⟩ : syracuseStep 2277647 = 3416471) B3416471
theorem B3416477 : Blo 2277435 3416477 := bbase (se 3 (by rfl) ⟨640589, by rfl⟩ : syracuseStep 3416477 = 1281179) (by norm_num)
theorem B2277651 : Blo 2277435 2277651 := bstep (se 1 (by rfl) ⟨1708238, by rfl⟩ : syracuseStep 2277651 = 3416477) B3416477
theorem B5124725 : Blo 2277435 5124725 := bbase (se 5 (by rfl) ⟨240221, by rfl⟩ : syracuseStep 5124725 = 480443) (by norm_num)
theorem B3416483 : Blo 2277435 3416483 := bstep (se 1 (by rfl) ⟨2562362, by rfl⟩ : syracuseStep 3416483 = 5124725) B5124725
theorem B2277655 : Blo 2277435 2277655 := bstep (se 1 (by rfl) ⟨1708241, by rfl⟩ : syracuseStep 2277655 = 3416483) B3416483
theorem B26297941 : Blo 2277435 26297941 := bbase (se 8 (by rfl) ⟨154089, by rfl⟩ : syracuseStep 26297941 = 308179) (by norm_num)
theorem B35063921 : Blo 2277435 35063921 := bstep (se 2 (by rfl) ⟨13148970, by rfl⟩ : syracuseStep 35063921 = 26297941) B26297941
theorem B23375947 : Blo 2277435 23375947 := bstep (se 1 (by rfl) ⟨17531960, by rfl⟩ : syracuseStep 23375947 = 35063921) B35063921
theorem B31167929 : Blo 2277435 31167929 := bstep (se 2 (by rfl) ⟨11687973, by rfl⟩ : syracuseStep 31167929 = 23375947) B23375947
theorem B20778619 : Blo 2277435 20778619 := bstep (se 1 (by rfl) ⟨15583964, by rfl⟩ : syracuseStep 20778619 = 31167929) B31167929
theorem B27704825 : Blo 2277435 27704825 := bstep (se 2 (by rfl) ⟨10389309, by rfl⟩ : syracuseStep 27704825 = 20778619) B20778619
theorem B18469883 : Blo 2277435 18469883 := bstep (se 1 (by rfl) ⟨13852412, by rfl⟩ : syracuseStep 18469883 = 27704825) B27704825
theorem B12313255 : Blo 2277435 12313255 := bstep (se 1 (by rfl) ⟨9234941, by rfl⟩ : syracuseStep 12313255 = 18469883) B18469883
theorem B16417673 : Blo 2277435 16417673 := bstep (se 2 (by rfl) ⟨6156627, by rfl⟩ : syracuseStep 16417673 = 12313255) B12313255
theorem B10945115 : Blo 2277435 10945115 := bstep (se 1 (by rfl) ⟨8208836, by rfl⟩ : syracuseStep 10945115 = 16417673) B16417673
theorem B7296743 : Blo 2277435 7296743 := bstep (se 1 (by rfl) ⟨5472557, by rfl⟩ : syracuseStep 7296743 = 10945115) B10945115
theorem B19457981 : Blo 2277435 19457981 := bstep (se 3 (by rfl) ⟨3648371, by rfl⟩ : syracuseStep 19457981 = 7296743) B7296743
theorem B12971987 : Blo 2277435 12971987 := bstep (se 1 (by rfl) ⟨9728990, by rfl⟩ : syracuseStep 12971987 = 19457981) B19457981
theorem B8647991 : Blo 2277435 8647991 := bstep (se 1 (by rfl) ⟨6485993, by rfl⟩ : syracuseStep 8647991 = 12971987) B12971987
theorem B5765327 : Blo 2277435 5765327 := bstep (se 1 (by rfl) ⟨4323995, by rfl⟩ : syracuseStep 5765327 = 8647991) B8647991
theorem B3843551 : Blo 2277435 3843551 := bstep (se 1 (by rfl) ⟨2882663, by rfl⟩ : syracuseStep 3843551 = 5765327) B5765327
theorem B2562367 : Blo 2277435 2562367 := bstep (se 1 (by rfl) ⟨1921775, by rfl⟩ : syracuseStep 2562367 = 3843551) B3843551
theorem B3416489 : Blo 2277435 3416489 := bstep (se 2 (by rfl) ⟨1281183, by rfl⟩ : syracuseStep 3416489 = 2562367) B2562367
theorem B2277659 : Blo 2277435 2277659 := bstep (se 1 (by rfl) ⟨1708244, by rfl⟩ : syracuseStep 2277659 = 3416489) B3416489
theorem B8648005 : Blo 2277435 8648005 := bbase (se 4 (by rfl) ⟨810750, by rfl⟩ : syracuseStep 8648005 = 1621501) (by norm_num)
theorem B11530673 : Blo 2277435 11530673 := bstep (se 2 (by rfl) ⟨4324002, by rfl⟩ : syracuseStep 11530673 = 8648005) B8648005
theorem B7687115 : Blo 2277435 7687115 := bstep (se 1 (by rfl) ⟨5765336, by rfl⟩ : syracuseStep 7687115 = 11530673) B11530673
theorem B5124743 : Blo 2277435 5124743 := bstep (se 1 (by rfl) ⟨3843557, by rfl⟩ : syracuseStep 5124743 = 7687115) B7687115
theorem B3416495 : Blo 2277435 3416495 := bstep (se 1 (by rfl) ⟨2562371, by rfl⟩ : syracuseStep 3416495 = 5124743) B5124743
theorem B2277663 : Blo 2277435 2277663 := bstep (se 1 (by rfl) ⟨1708247, by rfl⟩ : syracuseStep 2277663 = 3416495) B3416495
theorem B3416501 : Blo 2277435 3416501 := bbase (se 5 (by rfl) ⟨160148, by rfl⟩ : syracuseStep 3416501 = 320297) (by norm_num)
theorem B2277667 : Blo 2277435 2277667 := bstep (se 1 (by rfl) ⟨1708250, by rfl⟩ : syracuseStep 2277667 = 3416501) B3416501
theorem B5765357 : Blo 2277435 5765357 := bbase (se 3 (by rfl) ⟨1081004, by rfl⟩ : syracuseStep 5765357 = 2162009) (by norm_num)
theorem B3843571 : Blo 2277435 3843571 := bstep (se 1 (by rfl) ⟨2882678, by rfl⟩ : syracuseStep 3843571 = 5765357) B5765357
theorem B5124761 : Blo 2277435 5124761 := bstep (se 2 (by rfl) ⟨1921785, by rfl⟩ : syracuseStep 5124761 = 3843571) B3843571
theorem B3416507 : Blo 2277435 3416507 := bstep (se 1 (by rfl) ⟨2562380, by rfl⟩ : syracuseStep 3416507 = 5124761) B5124761
theorem B2277671 : Blo 2277435 2277671 := bstep (se 1 (by rfl) ⟨1708253, by rfl⟩ : syracuseStep 2277671 = 3416507) B3416507
theorem B2562385 : Blo 2277435 2562385 := bbase (se 2 (by rfl) ⟨960894, by rfl⟩ : syracuseStep 2562385 = 1921789) (by norm_num)
theorem B3416513 : Blo 2277435 3416513 := bstep (se 2 (by rfl) ⟨1281192, by rfl⟩ : syracuseStep 3416513 = 2562385) B2562385
theorem B2277675 : Blo 2277435 2277675 := bstep (se 1 (by rfl) ⟨1708256, by rfl⟩ : syracuseStep 2277675 = 3416513) B3416513
theorem B2432269 : Blo 2277435 2432269 := bbase (se 3 (by rfl) ⟨456050, by rfl⟩ : syracuseStep 2432269 = 912101) (by norm_num)
theorem B3243025 : Blo 2277435 3243025 := bstep (se 2 (by rfl) ⟨1216134, by rfl⟩ : syracuseStep 3243025 = 2432269) B2432269
theorem B4324033 : Blo 2277435 4324033 := bstep (se 2 (by rfl) ⟨1621512, by rfl⟩ : syracuseStep 4324033 = 3243025) B3243025
theorem B5765377 : Blo 2277435 5765377 := bstep (se 2 (by rfl) ⟨2162016, by rfl⟩ : syracuseStep 5765377 = 4324033) B4324033
theorem B7687169 : Blo 2277435 7687169 := bstep (se 2 (by rfl) ⟨2882688, by rfl⟩ : syracuseStep 7687169 = 5765377) B5765377
theorem B5124779 : Blo 2277435 5124779 := bstep (se 1 (by rfl) ⟨3843584, by rfl⟩ : syracuseStep 5124779 = 7687169) B7687169
theorem B3416519 : Blo 2277435 3416519 := bstep (se 1 (by rfl) ⟨2562389, by rfl⟩ : syracuseStep 3416519 = 5124779) B5124779
theorem B2277679 : Blo 2277435 2277679 := bstep (se 1 (by rfl) ⟨1708259, by rfl⟩ : syracuseStep 2277679 = 3416519) B3416519
theorem B3416525 : Blo 2277435 3416525 := bbase (se 3 (by rfl) ⟨640598, by rfl⟩ : syracuseStep 3416525 = 1281197) (by norm_num)
theorem B2277683 : Blo 2277435 2277683 := bstep (se 1 (by rfl) ⟨1708262, by rfl⟩ : syracuseStep 2277683 = 3416525) B3416525
theorem B5124797 : Blo 2277435 5124797 := bbase (se 3 (by rfl) ⟨960899, by rfl⟩ : syracuseStep 5124797 = 1921799) (by norm_num)
theorem B3416531 : Blo 2277435 3416531 := bstep (se 1 (by rfl) ⟨2562398, by rfl⟩ : syracuseStep 3416531 = 5124797) B5124797
theorem B2277687 : Blo 2277435 2277687 := bstep (se 1 (by rfl) ⟨1708265, by rfl⟩ : syracuseStep 2277687 = 3416531) B3416531
theorem B3843605 : Blo 2277435 3843605 := bbase (se 6 (by rfl) ⟨90084, by rfl⟩ : syracuseStep 3843605 = 180169) (by norm_num)
theorem B2562403 : Blo 2277435 2562403 := bstep (se 1 (by rfl) ⟨1921802, by rfl⟩ : syracuseStep 2562403 = 3843605) B3843605
theorem B3416537 : Blo 2277435 3416537 := bstep (se 2 (by rfl) ⟨1281201, by rfl⟩ : syracuseStep 3416537 = 2562403) B2562403
theorem B2277691 : Blo 2277435 2277691 := bstep (se 1 (by rfl) ⟨1708268, by rfl⟩ : syracuseStep 2277691 = 3416537) B3416537
theorem B8208965 : Blo 2277435 8208965 := bbase (se 4 (by rfl) ⟨769590, by rfl⟩ : syracuseStep 8208965 = 1539181) (by norm_num)
theorem B21890573 : Blo 2277435 21890573 := bstep (se 3 (by rfl) ⟨4104482, by rfl⟩ : syracuseStep 21890573 = 8208965) B8208965
theorem B14593715 : Blo 2277435 14593715 := bstep (se 1 (by rfl) ⟨10945286, by rfl⟩ : syracuseStep 14593715 = 21890573) B21890573
theorem B9729143 : Blo 2277435 9729143 := bstep (se 1 (by rfl) ⟨7296857, by rfl⟩ : syracuseStep 9729143 = 14593715) B14593715
theorem B6486095 : Blo 2277435 6486095 := bstep (se 1 (by rfl) ⟨4864571, by rfl⟩ : syracuseStep 6486095 = 9729143) B9729143
theorem B17296253 : Blo 2277435 17296253 := bstep (se 3 (by rfl) ⟨3243047, by rfl⟩ : syracuseStep 17296253 = 6486095) B6486095
theorem B11530835 : Blo 2277435 11530835 := bstep (se 1 (by rfl) ⟨8648126, by rfl⟩ : syracuseStep 11530835 = 17296253) B17296253
theorem B7687223 : Blo 2277435 7687223 := bstep (se 1 (by rfl) ⟨5765417, by rfl⟩ : syracuseStep 7687223 = 11530835) B11530835
theorem B5124815 : Blo 2277435 5124815 := bstep (se 1 (by rfl) ⟨3843611, by rfl⟩ : syracuseStep 5124815 = 7687223) B7687223
theorem B3416543 : Blo 2277435 3416543 := bstep (se 1 (by rfl) ⟨2562407, by rfl⟩ : syracuseStep 3416543 = 5124815) B5124815
theorem B2277695 : Blo 2277435 2277695 := bstep (se 1 (by rfl) ⟨1708271, by rfl⟩ : syracuseStep 2277695 = 3416543) B3416543
theorem B3416549 : Blo 2277435 3416549 := bbase (se 4 (by rfl) ⟨320301, by rfl⟩ : syracuseStep 3416549 = 640603) (by norm_num)
theorem B2277699 : Blo 2277435 2277699 := bstep (se 1 (by rfl) ⟨1708274, by rfl⟩ : syracuseStep 2277699 = 3416549) B3416549
theorem B7792133 : Blo 2277435 7792133 := bbase (se 4 (by rfl) ⟨730512, by rfl⟩ : syracuseStep 7792133 = 1461025) (by norm_num)
theorem B20779021 : Blo 2277435 20779021 := bstep (se 3 (by rfl) ⟨3896066, by rfl⟩ : syracuseStep 20779021 = 7792133) B7792133
theorem B27705361 : Blo 2277435 27705361 := bstep (se 2 (by rfl) ⟨10389510, by rfl⟩ : syracuseStep 27705361 = 20779021) B20779021
theorem B36940481 : Blo 2277435 36940481 := bstep (se 2 (by rfl) ⟨13852680, by rfl⟩ : syracuseStep 36940481 = 27705361) B27705361
theorem B24626987 : Blo 2277435 24626987 := bstep (se 1 (by rfl) ⟨18470240, by rfl⟩ : syracuseStep 24626987 = 36940481) B36940481
theorem B16417991 : Blo 2277435 16417991 := bstep (se 1 (by rfl) ⟨12313493, by rfl⟩ : syracuseStep 16417991 = 24626987) B24626987
theorem B10945327 : Blo 2277435 10945327 := bstep (se 1 (by rfl) ⟨8208995, by rfl⟩ : syracuseStep 10945327 = 16417991) B16417991
theorem B14593769 : Blo 2277435 14593769 := bstep (se 2 (by rfl) ⟨5472663, by rfl⟩ : syracuseStep 14593769 = 10945327) B10945327
theorem B9729179 : Blo 2277435 9729179 := bstep (se 1 (by rfl) ⟨7296884, by rfl⟩ : syracuseStep 9729179 = 14593769) B14593769
theorem B6486119 : Blo 2277435 6486119 := bstep (se 1 (by rfl) ⟨4864589, by rfl⟩ : syracuseStep 6486119 = 9729179) B9729179
theorem B4324079 : Blo 2277435 4324079 := bstep (se 1 (by rfl) ⟨3243059, by rfl⟩ : syracuseStep 4324079 = 6486119) B6486119
theorem B2882719 : Blo 2277435 2882719 := bstep (se 1 (by rfl) ⟨2162039, by rfl⟩ : syracuseStep 2882719 = 4324079) B4324079
theorem B3843625 : Blo 2277435 3843625 := bstep (se 2 (by rfl) ⟨1441359, by rfl⟩ : syracuseStep 3843625 = 2882719) B2882719
theorem B5124833 : Blo 2277435 5124833 := bstep (se 2 (by rfl) ⟨1921812, by rfl⟩ : syracuseStep 5124833 = 3843625) B3843625
theorem B3416555 : Blo 2277435 3416555 := bstep (se 1 (by rfl) ⟨2562416, by rfl⟩ : syracuseStep 3416555 = 5124833) B5124833
theorem B2277703 : Blo 2277435 2277703 := bstep (se 1 (by rfl) ⟨1708277, by rfl⟩ : syracuseStep 2277703 = 3416555) B3416555
theorem B2562421 : Blo 2277435 2562421 := bbase (se 5 (by rfl) ⟨120113, by rfl⟩ : syracuseStep 2562421 = 240227) (by norm_num)
theorem B3416561 : Blo 2277435 3416561 := bstep (se 2 (by rfl) ⟨1281210, by rfl⟩ : syracuseStep 3416561 = 2562421) B2562421
theorem B2277707 : Blo 2277435 2277707 := bstep (se 1 (by rfl) ⟨1708280, by rfl⟩ : syracuseStep 2277707 = 3416561) B3416561
theorem B2882729 : Blo 2277435 2882729 := bbase (se 2 (by rfl) ⟨1081023, by rfl⟩ : syracuseStep 2882729 = 2162047) (by norm_num)
theorem B7687277 : Blo 2277435 7687277 := bstep (se 3 (by rfl) ⟨1441364, by rfl⟩ : syracuseStep 7687277 = 2882729) B2882729
theorem B5124851 : Blo 2277435 5124851 := bstep (se 1 (by rfl) ⟨3843638, by rfl⟩ : syracuseStep 5124851 = 7687277) B7687277
theorem B3416567 : Blo 2277435 3416567 := bstep (se 1 (by rfl) ⟨2562425, by rfl⟩ : syracuseStep 3416567 = 5124851) B5124851
theorem B2277711 : Blo 2277435 2277711 := bstep (se 1 (by rfl) ⟨1708283, by rfl⟩ : syracuseStep 2277711 = 3416567) B3416567
theorem B3416573 : Blo 2277435 3416573 := bbase (se 3 (by rfl) ⟨640607, by rfl⟩ : syracuseStep 3416573 = 1281215) (by norm_num)
theorem B2277715 : Blo 2277435 2277715 := bstep (se 1 (by rfl) ⟨1708286, by rfl⟩ : syracuseStep 2277715 = 3416573) B3416573
theorem B5124869 : Blo 2277435 5124869 := bbase (se 4 (by rfl) ⟨480456, by rfl⟩ : syracuseStep 5124869 = 960913) (by norm_num)
theorem B3416579 : Blo 2277435 3416579 := bstep (se 1 (by rfl) ⟨2562434, by rfl⟩ : syracuseStep 3416579 = 5124869) B5124869
theorem B2277719 : Blo 2277435 2277719 := bstep (se 1 (by rfl) ⟨1708289, by rfl⟩ : syracuseStep 2277719 = 3416579) B3416579
theorem B4324117 : Blo 2277435 4324117 := bbase (se 6 (by rfl) ⟨101346, by rfl⟩ : syracuseStep 4324117 = 202693) (by norm_num)
theorem B5765489 : Blo 2277435 5765489 := bstep (se 2 (by rfl) ⟨2162058, by rfl⟩ : syracuseStep 5765489 = 4324117) B4324117
theorem B3843659 : Blo 2277435 3843659 := bstep (se 1 (by rfl) ⟨2882744, by rfl⟩ : syracuseStep 3843659 = 5765489) B5765489
theorem B2562439 : Blo 2277435 2562439 := bstep (se 1 (by rfl) ⟨1921829, by rfl⟩ : syracuseStep 2562439 = 3843659) B3843659
theorem B3416585 : Blo 2277435 3416585 := bstep (se 2 (by rfl) ⟨1281219, by rfl⟩ : syracuseStep 3416585 = 2562439) B2562439
theorem B2277723 : Blo 2277435 2277723 := bstep (se 1 (by rfl) ⟨1708292, by rfl⟩ : syracuseStep 2277723 = 3416585) B3416585
theorem B11530997 : Blo 2277435 11530997 := bbase (se 5 (by rfl) ⟨540515, by rfl⟩ : syracuseStep 11530997 = 1081031) (by norm_num)
theorem B7687331 : Blo 2277435 7687331 := bstep (se 1 (by rfl) ⟨5765498, by rfl⟩ : syracuseStep 7687331 = 11530997) B11530997
theorem B5124887 : Blo 2277435 5124887 := bstep (se 1 (by rfl) ⟨3843665, by rfl⟩ : syracuseStep 5124887 = 7687331) B7687331
theorem B3416591 : Blo 2277435 3416591 := bstep (se 1 (by rfl) ⟨2562443, by rfl⟩ : syracuseStep 3416591 = 5124887) B5124887
theorem B2277727 : Blo 2277435 2277727 := bstep (se 1 (by rfl) ⟨1708295, by rfl⟩ : syracuseStep 2277727 = 3416591) B3416591
theorem B3416597 : Blo 2277435 3416597 := bbase (se 6 (by rfl) ⟨80076, by rfl⟩ : syracuseStep 3416597 = 160153) (by norm_num)
theorem B2277731 : Blo 2277435 2277731 := bstep (se 1 (by rfl) ⟨1708298, by rfl⟩ : syracuseStep 2277731 = 3416597) B3416597
theorem B3648493 : Blo 2277435 3648493 := bbase (se 3 (by rfl) ⟨684092, by rfl⟩ : syracuseStep 3648493 = 1368185) (by norm_num)
theorem B19458629 : Blo 2277435 19458629 := bstep (se 4 (by rfl) ⟨1824246, by rfl⟩ : syracuseStep 19458629 = 3648493) B3648493
theorem B12972419 : Blo 2277435 12972419 := bstep (se 1 (by rfl) ⟨9729314, by rfl⟩ : syracuseStep 12972419 = 19458629) B19458629
theorem B8648279 : Blo 2277435 8648279 := bstep (se 1 (by rfl) ⟨6486209, by rfl⟩ : syracuseStep 8648279 = 12972419) B12972419
theorem B5765519 : Blo 2277435 5765519 := bstep (se 1 (by rfl) ⟨4324139, by rfl⟩ : syracuseStep 5765519 = 8648279) B8648279
theorem B3843679 : Blo 2277435 3843679 := bstep (se 1 (by rfl) ⟨2882759, by rfl⟩ : syracuseStep 3843679 = 5765519) B5765519
theorem B5124905 : Blo 2277435 5124905 := bstep (se 2 (by rfl) ⟨1921839, by rfl⟩ : syracuseStep 5124905 = 3843679) B3843679
theorem B3416603 : Blo 2277435 3416603 := bstep (se 1 (by rfl) ⟨2562452, by rfl⟩ : syracuseStep 3416603 = 5124905) B5124905
theorem B2277735 : Blo 2277435 2277735 := bstep (se 1 (by rfl) ⟨1708301, by rfl⟩ : syracuseStep 2277735 = 3416603) B3416603
theorem B2562457 : Blo 2277435 2562457 := bbase (se 2 (by rfl) ⟨960921, by rfl⟩ : syracuseStep 2562457 = 1921843) (by norm_num)
theorem B3416609 : Blo 2277435 3416609 := bstep (se 2 (by rfl) ⟨1281228, by rfl⟩ : syracuseStep 3416609 = 2562457) B2562457
theorem B2277739 : Blo 2277435 2277739 := bstep (se 1 (by rfl) ⟨1708304, by rfl⟩ : syracuseStep 2277739 = 3416609) B3416609
theorem B8648309 : Blo 2277435 8648309 := bbase (se 5 (by rfl) ⟨405389, by rfl⟩ : syracuseStep 8648309 = 810779) (by norm_num)
theorem B5765539 : Blo 2277435 5765539 := bstep (se 1 (by rfl) ⟨4324154, by rfl⟩ : syracuseStep 5765539 = 8648309) B8648309
theorem B7687385 : Blo 2277435 7687385 := bstep (se 2 (by rfl) ⟨2882769, by rfl⟩ : syracuseStep 7687385 = 5765539) B5765539
theorem B5124923 : Blo 2277435 5124923 := bstep (se 1 (by rfl) ⟨3843692, by rfl⟩ : syracuseStep 5124923 = 7687385) B7687385
theorem B3416615 : Blo 2277435 3416615 := bstep (se 1 (by rfl) ⟨2562461, by rfl⟩ : syracuseStep 3416615 = 5124923) B5124923
theorem B2277743 : Blo 2277435 2277743 := bstep (se 1 (by rfl) ⟨1708307, by rfl⟩ : syracuseStep 2277743 = 3416615) B3416615
theorem B3416621 : Blo 2277435 3416621 := bbase (se 3 (by rfl) ⟨640616, by rfl⟩ : syracuseStep 3416621 = 1281233) (by norm_num)
theorem B2277747 : Blo 2277435 2277747 := bstep (se 1 (by rfl) ⟨1708310, by rfl⟩ : syracuseStep 2277747 = 3416621) B3416621
theorem B5124941 : Blo 2277435 5124941 := bbase (se 3 (by rfl) ⟨960926, by rfl⟩ : syracuseStep 5124941 = 1921853) (by norm_num)
theorem B3416627 : Blo 2277435 3416627 := bstep (se 1 (by rfl) ⟨2562470, by rfl⟩ : syracuseStep 3416627 = 5124941) B5124941
theorem B2277751 : Blo 2277435 2277751 := bstep (se 1 (by rfl) ⟨1708313, by rfl⟩ : syracuseStep 2277751 = 3416627) B3416627
theorem B2882785 : Blo 2277435 2882785 := bbase (se 2 (by rfl) ⟨1081044, by rfl⟩ : syracuseStep 2882785 = 2162089) (by norm_num)
theorem B3843713 : Blo 2277435 3843713 := bstep (se 2 (by rfl) ⟨1441392, by rfl⟩ : syracuseStep 3843713 = 2882785) B2882785
theorem B2562475 : Blo 2277435 2562475 := bstep (se 1 (by rfl) ⟨1921856, by rfl⟩ : syracuseStep 2562475 = 3843713) B3843713
theorem B3416633 : Blo 2277435 3416633 := bstep (se 2 (by rfl) ⟨1281237, by rfl⟩ : syracuseStep 3416633 = 2562475) B2562475
theorem B2277755 : Blo 2277435 2277755 := bstep (se 1 (by rfl) ⟨1708316, by rfl⟩ : syracuseStep 2277755 = 3416633) B3416633
theorem B25945109 : Blo 2277435 25945109 := bbase (se 6 (by rfl) ⟨608088, by rfl⟩ : syracuseStep 25945109 = 1216177) (by norm_num)
theorem B17296739 : Blo 2277435 17296739 := bstep (se 1 (by rfl) ⟨12972554, by rfl⟩ : syracuseStep 17296739 = 25945109) B25945109
theorem B11531159 : Blo 2277435 11531159 := bstep (se 1 (by rfl) ⟨8648369, by rfl⟩ : syracuseStep 11531159 = 17296739) B17296739
theorem B7687439 : Blo 2277435 7687439 := bstep (se 1 (by rfl) ⟨5765579, by rfl⟩ : syracuseStep 7687439 = 11531159) B11531159
theorem B5124959 : Blo 2277435 5124959 := bstep (se 1 (by rfl) ⟨3843719, by rfl⟩ : syracuseStep 5124959 = 7687439) B7687439
theorem B3416639 : Blo 2277435 3416639 := bstep (se 1 (by rfl) ⟨2562479, by rfl⟩ : syracuseStep 3416639 = 5124959) B5124959
theorem B2277759 : Blo 2277435 2277759 := bstep (se 1 (by rfl) ⟨1708319, by rfl⟩ : syracuseStep 2277759 = 3416639) B3416639
theorem B3416645 : Blo 2277435 3416645 := bbase (se 4 (by rfl) ⟨320310, by rfl⟩ : syracuseStep 3416645 = 640621) (by norm_num)
theorem B2277763 : Blo 2277435 2277763 := bstep (se 1 (by rfl) ⟨1708322, by rfl⟩ : syracuseStep 2277763 = 3416645) B3416645
theorem B3843733 : Blo 2277435 3843733 := bbase (se 6 (by rfl) ⟨90087, by rfl⟩ : syracuseStep 3843733 = 180175) (by norm_num)
theorem B5124977 : Blo 2277435 5124977 := bstep (se 2 (by rfl) ⟨1921866, by rfl⟩ : syracuseStep 5124977 = 3843733) B3843733
theorem B3416651 : Blo 2277435 3416651 := bstep (se 1 (by rfl) ⟨2562488, by rfl⟩ : syracuseStep 3416651 = 5124977) B5124977
theorem B2277767 : Blo 2277435 2277767 := bstep (se 1 (by rfl) ⟨1708325, by rfl⟩ : syracuseStep 2277767 = 3416651) B3416651
theorem B2562493 : Blo 2277435 2562493 := bbase (se 3 (by rfl) ⟨480467, by rfl⟩ : syracuseStep 2562493 = 960935) (by norm_num)
theorem B3416657 : Blo 2277435 3416657 := bstep (se 2 (by rfl) ⟨1281246, by rfl⟩ : syracuseStep 3416657 = 2562493) B2562493
theorem B2277771 : Blo 2277435 2277771 := bstep (se 1 (by rfl) ⟨1708328, by rfl⟩ : syracuseStep 2277771 = 3416657) B3416657
theorem B7687493 : Blo 2277435 7687493 := bbase (se 4 (by rfl) ⟨720702, by rfl⟩ : syracuseStep 7687493 = 1441405) (by norm_num)
theorem B5124995 : Blo 2277435 5124995 := bstep (se 1 (by rfl) ⟨3843746, by rfl⟩ : syracuseStep 5124995 = 7687493) B7687493
theorem B3416663 : Blo 2277435 3416663 := bstep (se 1 (by rfl) ⟨2562497, by rfl⟩ : syracuseStep 3416663 = 5124995) B5124995
theorem B2277775 : Blo 2277435 2277775 := bstep (se 1 (by rfl) ⟨1708331, by rfl⟩ : syracuseStep 2277775 = 3416663) B3416663
theorem B3416669 : Blo 2277435 3416669 := bbase (se 3 (by rfl) ⟨640625, by rfl⟩ : syracuseStep 3416669 = 1281251) (by norm_num)
theorem B2277779 : Blo 2277435 2277779 := bstep (se 1 (by rfl) ⟨1708334, by rfl⟩ : syracuseStep 2277779 = 3416669) B3416669
theorem B5125013 : Blo 2277435 5125013 := bbase (se 6 (by rfl) ⟨120117, by rfl⟩ : syracuseStep 5125013 = 240235) (by norm_num)
theorem B3416675 : Blo 2277435 3416675 := bstep (se 1 (by rfl) ⟨2562506, by rfl⟩ : syracuseStep 3416675 = 5125013) B5125013
theorem B2277783 : Blo 2277435 2277783 := bstep (se 1 (by rfl) ⟨1708337, by rfl⟩ : syracuseStep 2277783 = 3416675) B3416675
theorem B2736433 : Blo 2277435 2736433 := bbase (se 2 (by rfl) ⟨1026162, by rfl⟩ : syracuseStep 2736433 = 2052325) (by norm_num)
theorem B3648577 : Blo 2277435 3648577 := bstep (se 2 (by rfl) ⟨1368216, by rfl⟩ : syracuseStep 3648577 = 2736433) B2736433
theorem B4864769 : Blo 2277435 4864769 := bstep (se 2 (by rfl) ⟨1824288, by rfl⟩ : syracuseStep 4864769 = 3648577) B3648577
theorem B3243179 : Blo 2277435 3243179 := bstep (se 1 (by rfl) ⟨2432384, by rfl⟩ : syracuseStep 3243179 = 4864769) B4864769
theorem B8648477 : Blo 2277435 8648477 := bstep (se 3 (by rfl) ⟨1621589, by rfl⟩ : syracuseStep 8648477 = 3243179) B3243179
theorem B5765651 : Blo 2277435 5765651 := bstep (se 1 (by rfl) ⟨4324238, by rfl⟩ : syracuseStep 5765651 = 8648477) B8648477
theorem B3843767 : Blo 2277435 3843767 := bstep (se 1 (by rfl) ⟨2882825, by rfl⟩ : syracuseStep 3843767 = 5765651) B5765651
theorem B2562511 : Blo 2277435 2562511 := bstep (se 1 (by rfl) ⟨1921883, by rfl⟩ : syracuseStep 2562511 = 3843767) B3843767
theorem B3416681 : Blo 2277435 3416681 := bstep (se 2 (by rfl) ⟨1281255, by rfl⟩ : syracuseStep 3416681 = 2562511) B2562511
theorem B2277787 : Blo 2277435 2277787 := bstep (se 1 (by rfl) ⟨1708340, by rfl⟩ : syracuseStep 2277787 = 3416681) B3416681
theorem B2736437 : Blo 2277435 2736437 := bbase (se 5 (by rfl) ⟨128270, by rfl⟩ : syracuseStep 2736437 = 256541) (by norm_num)
theorem B7297165 : Blo 2277435 7297165 := bstep (se 3 (by rfl) ⟨1368218, by rfl⟩ : syracuseStep 7297165 = 2736437) B2736437
theorem B9729553 : Blo 2277435 9729553 := bstep (se 2 (by rfl) ⟨3648582, by rfl⟩ : syracuseStep 9729553 = 7297165) B7297165
theorem B12972737 : Blo 2277435 12972737 := bstep (se 2 (by rfl) ⟨4864776, by rfl⟩ : syracuseStep 12972737 = 9729553) B9729553
theorem B8648491 : Blo 2277435 8648491 := bstep (se 1 (by rfl) ⟨6486368, by rfl⟩ : syracuseStep 8648491 = 12972737) B12972737
theorem B11531321 : Blo 2277435 11531321 := bstep (se 2 (by rfl) ⟨4324245, by rfl⟩ : syracuseStep 11531321 = 8648491) B8648491
theorem B7687547 : Blo 2277435 7687547 := bstep (se 1 (by rfl) ⟨5765660, by rfl⟩ : syracuseStep 7687547 = 11531321) B11531321
theorem B5125031 : Blo 2277435 5125031 := bstep (se 1 (by rfl) ⟨3843773, by rfl⟩ : syracuseStep 5125031 = 7687547) B7687547
theorem B3416687 : Blo 2277435 3416687 := bstep (se 1 (by rfl) ⟨2562515, by rfl⟩ : syracuseStep 3416687 = 5125031) B5125031
theorem B2277791 : Blo 2277435 2277791 := bstep (se 1 (by rfl) ⟨1708343, by rfl⟩ : syracuseStep 2277791 = 3416687) B3416687
theorem B3416693 : Blo 2277435 3416693 := bbase (se 5 (by rfl) ⟨160157, by rfl⟩ : syracuseStep 3416693 = 320315) (by norm_num)
theorem B2277795 : Blo 2277435 2277795 := bstep (se 1 (by rfl) ⟨1708346, by rfl⟩ : syracuseStep 2277795 = 3416693) B3416693
theorem B4324261 : Blo 2277435 4324261 := bbase (se 4 (by rfl) ⟨405399, by rfl⟩ : syracuseStep 4324261 = 810799) (by norm_num)
theorem B5765681 : Blo 2277435 5765681 := bstep (se 2 (by rfl) ⟨2162130, by rfl⟩ : syracuseStep 5765681 = 4324261) B4324261
theorem B3843787 : Blo 2277435 3843787 := bstep (se 1 (by rfl) ⟨2882840, by rfl⟩ : syracuseStep 3843787 = 5765681) B5765681
theorem B5125049 : Blo 2277435 5125049 := bstep (se 2 (by rfl) ⟨1921893, by rfl⟩ : syracuseStep 5125049 = 3843787) B3843787
theorem B3416699 : Blo 2277435 3416699 := bstep (se 1 (by rfl) ⟨2562524, by rfl⟩ : syracuseStep 3416699 = 5125049) B5125049
theorem B2277799 : Blo 2277435 2277799 := bstep (se 1 (by rfl) ⟨1708349, by rfl⟩ : syracuseStep 2277799 = 3416699) B3416699
theorem B2562529 : Blo 2277435 2562529 := bbase (se 2 (by rfl) ⟨960948, by rfl⟩ : syracuseStep 2562529 = 1921897) (by norm_num)
theorem B3416705 : Blo 2277435 3416705 := bstep (se 2 (by rfl) ⟨1281264, by rfl⟩ : syracuseStep 3416705 = 2562529) B2562529
theorem B2277803 : Blo 2277435 2277803 := bstep (se 1 (by rfl) ⟨1708352, by rfl⟩ : syracuseStep 2277803 = 3416705) B3416705
theorem B5765701 : Blo 2277435 5765701 := bbase (se 4 (by rfl) ⟨540534, by rfl⟩ : syracuseStep 5765701 = 1081069) (by norm_num)
theorem B7687601 : Blo 2277435 7687601 := bstep (se 2 (by rfl) ⟨2882850, by rfl⟩ : syracuseStep 7687601 = 5765701) B5765701
theorem B5125067 : Blo 2277435 5125067 := bstep (se 1 (by rfl) ⟨3843800, by rfl⟩ : syracuseStep 5125067 = 7687601) B7687601
theorem B3416711 : Blo 2277435 3416711 := bstep (se 1 (by rfl) ⟨2562533, by rfl⟩ : syracuseStep 3416711 = 5125067) B5125067
theorem B2277807 : Blo 2277435 2277807 := bstep (se 1 (by rfl) ⟨1708355, by rfl⟩ : syracuseStep 2277807 = 3416711) B3416711
theorem B3416717 : Blo 2277435 3416717 := bbase (se 3 (by rfl) ⟨640634, by rfl⟩ : syracuseStep 3416717 = 1281269) (by norm_num)
theorem B2277811 : Blo 2277435 2277811 := bstep (se 1 (by rfl) ⟨1708358, by rfl⟩ : syracuseStep 2277811 = 3416717) B3416717
theorem B5125085 : Blo 2277435 5125085 := bbase (se 3 (by rfl) ⟨960953, by rfl⟩ : syracuseStep 5125085 = 1921907) (by norm_num)
theorem B3416723 : Blo 2277435 3416723 := bstep (se 1 (by rfl) ⟨2562542, by rfl⟩ : syracuseStep 3416723 = 5125085) B5125085
theorem B2277815 : Blo 2277435 2277815 := bstep (se 1 (by rfl) ⟨1708361, by rfl⟩ : syracuseStep 2277815 = 3416723) B3416723
theorem B3843821 : Blo 2277435 3843821 := bbase (se 3 (by rfl) ⟨720716, by rfl⟩ : syracuseStep 3843821 = 1441433) (by norm_num)
theorem B2562547 : Blo 2277435 2562547 := bstep (se 1 (by rfl) ⟨1921910, by rfl⟩ : syracuseStep 2562547 = 3843821) B3843821
theorem B3416729 : Blo 2277435 3416729 := bstep (se 2 (by rfl) ⟨1281273, by rfl⟩ : syracuseStep 3416729 = 2562547) B2562547
theorem B2277819 : Blo 2277435 2277819 := bstep (se 1 (by rfl) ⟨1708364, by rfl⟩ : syracuseStep 2277819 = 3416729) B3416729
theorem B5195029 : Blo 2277435 5195029 := bbase (se 6 (by rfl) ⟨121758, by rfl⟩ : syracuseStep 5195029 = 243517) (by norm_num)
theorem B6926705 : Blo 2277435 6926705 := bstep (se 2 (by rfl) ⟨2597514, by rfl⟩ : syracuseStep 6926705 = 5195029) B5195029
theorem B4617803 : Blo 2277435 4617803 := bstep (se 1 (by rfl) ⟨3463352, by rfl⟩ : syracuseStep 4617803 = 6926705) B6926705
theorem B3078535 : Blo 2277435 3078535 := bstep (se 1 (by rfl) ⟨2308901, by rfl⟩ : syracuseStep 3078535 = 4617803) B4617803
theorem B4104713 : Blo 2277435 4104713 := bstep (se 2 (by rfl) ⟨1539267, by rfl⟩ : syracuseStep 4104713 = 3078535) B3078535
theorem B10945901 : Blo 2277435 10945901 := bstep (se 3 (by rfl) ⟨2052356, by rfl⟩ : syracuseStep 10945901 = 4104713) B4104713
theorem B29189069 : Blo 2277435 29189069 := bstep (se 3 (by rfl) ⟨5472950, by rfl⟩ : syracuseStep 29189069 = 10945901) B10945901
theorem B19459379 : Blo 2277435 19459379 := bstep (se 1 (by rfl) ⟨14594534, by rfl⟩ : syracuseStep 19459379 = 29189069) B29189069
theorem B12972919 : Blo 2277435 12972919 := bstep (se 1 (by rfl) ⟨9729689, by rfl⟩ : syracuseStep 12972919 = 19459379) B19459379
theorem B17297225 : Blo 2277435 17297225 := bstep (se 2 (by rfl) ⟨6486459, by rfl⟩ : syracuseStep 17297225 = 12972919) B12972919
theorem B11531483 : Blo 2277435 11531483 := bstep (se 1 (by rfl) ⟨8648612, by rfl⟩ : syracuseStep 11531483 = 17297225) B17297225
theorem B7687655 : Blo 2277435 7687655 := bstep (se 1 (by rfl) ⟨5765741, by rfl⟩ : syracuseStep 7687655 = 11531483) B11531483
theorem B5125103 : Blo 2277435 5125103 := bstep (se 1 (by rfl) ⟨3843827, by rfl⟩ : syracuseStep 5125103 = 7687655) B7687655
theorem B3416735 : Blo 2277435 3416735 := bstep (se 1 (by rfl) ⟨2562551, by rfl⟩ : syracuseStep 3416735 = 5125103) B5125103
theorem B2277823 : Blo 2277435 2277823 := bstep (se 1 (by rfl) ⟨1708367, by rfl⟩ : syracuseStep 2277823 = 3416735) B3416735
theorem B3416741 : Blo 2277435 3416741 := bbase (se 4 (by rfl) ⟨320319, by rfl⟩ : syracuseStep 3416741 = 640639) (by norm_num)
theorem B2277827 : Blo 2277435 2277827 := bstep (se 1 (by rfl) ⟨1708370, by rfl⟩ : syracuseStep 2277827 = 3416741) B3416741
theorem B2882881 : Blo 2277435 2882881 := bbase (se 2 (by rfl) ⟨1081080, by rfl⟩ : syracuseStep 2882881 = 2162161) (by norm_num)
theorem B3843841 : Blo 2277435 3843841 := bstep (se 2 (by rfl) ⟨1441440, by rfl⟩ : syracuseStep 3843841 = 2882881) B2882881
theorem B5125121 : Blo 2277435 5125121 := bstep (se 2 (by rfl) ⟨1921920, by rfl⟩ : syracuseStep 5125121 = 3843841) B3843841
theorem B3416747 : Blo 2277435 3416747 := bstep (se 1 (by rfl) ⟨2562560, by rfl⟩ : syracuseStep 3416747 = 5125121) B5125121
theorem B2277831 : Blo 2277435 2277831 := bstep (se 1 (by rfl) ⟨1708373, by rfl⟩ : syracuseStep 2277831 = 3416747) B3416747
theorem B2562565 : Blo 2277435 2562565 := bbase (se 4 (by rfl) ⟨240240, by rfl⟩ : syracuseStep 2562565 = 480481) (by norm_num)
theorem B3416753 : Blo 2277435 3416753 := bstep (se 2 (by rfl) ⟨1281282, by rfl⟩ : syracuseStep 3416753 = 2562565) B2562565
theorem B2277835 : Blo 2277435 2277835 := bstep (se 1 (by rfl) ⟨1708376, by rfl⟩ : syracuseStep 2277835 = 3416753) B3416753
theorem B3243253 : Blo 2277435 3243253 := bbase (se 5 (by rfl) ⟨152027, by rfl⟩ : syracuseStep 3243253 = 304055) (by norm_num)
theorem B4324337 : Blo 2277435 4324337 := bstep (se 2 (by rfl) ⟨1621626, by rfl⟩ : syracuseStep 4324337 = 3243253) B3243253
theorem B2882891 : Blo 2277435 2882891 := bstep (se 1 (by rfl) ⟨2162168, by rfl⟩ : syracuseStep 2882891 = 4324337) B4324337
theorem B7687709 : Blo 2277435 7687709 := bstep (se 3 (by rfl) ⟨1441445, by rfl⟩ : syracuseStep 7687709 = 2882891) B2882891
theorem B5125139 : Blo 2277435 5125139 := bstep (se 1 (by rfl) ⟨3843854, by rfl⟩ : syracuseStep 5125139 = 7687709) B7687709
theorem B3416759 : Blo 2277435 3416759 := bstep (se 1 (by rfl) ⟨2562569, by rfl⟩ : syracuseStep 3416759 = 5125139) B5125139
theorem B2277839 : Blo 2277435 2277839 := bstep (se 1 (by rfl) ⟨1708379, by rfl⟩ : syracuseStep 2277839 = 3416759) B3416759
theorem B3416765 : Blo 2277435 3416765 := bbase (se 3 (by rfl) ⟨640643, by rfl⟩ : syracuseStep 3416765 = 1281287) (by norm_num)
theorem B2277843 : Blo 2277435 2277843 := bstep (se 1 (by rfl) ⟨1708382, by rfl⟩ : syracuseStep 2277843 = 3416765) B3416765
theorem B5125157 : Blo 2277435 5125157 := bbase (se 4 (by rfl) ⟨480483, by rfl⟩ : syracuseStep 5125157 = 960967) (by norm_num)
theorem B3416771 : Blo 2277435 3416771 := bstep (se 1 (by rfl) ⟨2562578, by rfl⟩ : syracuseStep 3416771 = 5125157) B5125157
theorem B2277847 : Blo 2277435 2277847 := bstep (se 1 (by rfl) ⟨1708385, by rfl⟩ : syracuseStep 2277847 = 3416771) B3416771
theorem B5765813 : Blo 2277435 5765813 := bbase (se 5 (by rfl) ⟨270272, by rfl⟩ : syracuseStep 5765813 = 540545) (by norm_num)
theorem B3843875 : Blo 2277435 3843875 := bstep (se 1 (by rfl) ⟨2882906, by rfl⟩ : syracuseStep 3843875 = 5765813) B5765813
theorem B2562583 : Blo 2277435 2562583 := bstep (se 1 (by rfl) ⟨1921937, by rfl⟩ : syracuseStep 2562583 = 3843875) B3843875
theorem B3416777 : Blo 2277435 3416777 := bstep (se 2 (by rfl) ⟨1281291, by rfl⟩ : syracuseStep 3416777 = 2562583) B2562583
theorem B2277851 : Blo 2277435 2277851 := bstep (se 1 (by rfl) ⟨1708388, by rfl⟩ : syracuseStep 2277851 = 3416777) B3416777
theorem B14594741 : Blo 2277435 14594741 := bbase (se 5 (by rfl) ⟨684128, by rfl⟩ : syracuseStep 14594741 = 1368257) (by norm_num)
theorem B9729827 : Blo 2277435 9729827 := bstep (se 1 (by rfl) ⟨7297370, by rfl⟩ : syracuseStep 9729827 = 14594741) B14594741
theorem B6486551 : Blo 2277435 6486551 := bstep (se 1 (by rfl) ⟨4864913, by rfl⟩ : syracuseStep 6486551 = 9729827) B9729827
theorem B4324367 : Blo 2277435 4324367 := bstep (se 1 (by rfl) ⟨3243275, by rfl⟩ : syracuseStep 4324367 = 6486551) B6486551
theorem B11531645 : Blo 2277435 11531645 := bstep (se 3 (by rfl) ⟨2162183, by rfl⟩ : syracuseStep 11531645 = 4324367) B4324367
theorem B7687763 : Blo 2277435 7687763 := bstep (se 1 (by rfl) ⟨5765822, by rfl⟩ : syracuseStep 7687763 = 11531645) B11531645
theorem B5125175 : Blo 2277435 5125175 := bstep (se 1 (by rfl) ⟨3843881, by rfl⟩ : syracuseStep 5125175 = 7687763) B7687763
theorem B3416783 : Blo 2277435 3416783 := bstep (se 1 (by rfl) ⟨2562587, by rfl⟩ : syracuseStep 3416783 = 5125175) B5125175
theorem B2277855 : Blo 2277435 2277855 := bstep (se 1 (by rfl) ⟨1708391, by rfl⟩ : syracuseStep 2277855 = 3416783) B3416783
theorem B3416789 : Blo 2277435 3416789 := bbase (se 7 (by rfl) ⟨40040, by rfl⟩ : syracuseStep 3416789 = 80081) (by norm_num)
theorem B2277859 : Blo 2277435 2277859 := bstep (se 1 (by rfl) ⟨1708394, by rfl⟩ : syracuseStep 2277859 = 3416789) B3416789
theorem B7297397 : Blo 2277435 7297397 := bbase (se 5 (by rfl) ⟨342065, by rfl⟩ : syracuseStep 7297397 = 684131) (by norm_num)
theorem B4864931 : Blo 2277435 4864931 := bstep (se 1 (by rfl) ⟨3648698, by rfl⟩ : syracuseStep 4864931 = 7297397) B7297397
theorem B3243287 : Blo 2277435 3243287 := bstep (se 1 (by rfl) ⟨2432465, by rfl⟩ : syracuseStep 3243287 = 4864931) B4864931
theorem B8648765 : Blo 2277435 8648765 := bstep (se 3 (by rfl) ⟨1621643, by rfl⟩ : syracuseStep 8648765 = 3243287) B3243287
theorem B5765843 : Blo 2277435 5765843 := bstep (se 1 (by rfl) ⟨4324382, by rfl⟩ : syracuseStep 5765843 = 8648765) B8648765
theorem B3843895 : Blo 2277435 3843895 := bstep (se 1 (by rfl) ⟨2882921, by rfl⟩ : syracuseStep 3843895 = 5765843) B5765843
theorem B5125193 : Blo 2277435 5125193 := bstep (se 2 (by rfl) ⟨1921947, by rfl⟩ : syracuseStep 5125193 = 3843895) B3843895
theorem B3416795 : Blo 2277435 3416795 := bstep (se 1 (by rfl) ⟨2562596, by rfl⟩ : syracuseStep 3416795 = 5125193) B5125193
theorem B2277863 : Blo 2277435 2277863 := bstep (se 1 (by rfl) ⟨1708397, by rfl⟩ : syracuseStep 2277863 = 3416795) B3416795
theorem B2562601 : Blo 2277435 2562601 := bbase (se 2 (by rfl) ⟨960975, by rfl⟩ : syracuseStep 2562601 = 1921951) (by norm_num)
theorem B3416801 : Blo 2277435 3416801 := bstep (se 2 (by rfl) ⟨1281300, by rfl⟩ : syracuseStep 3416801 = 2562601) B2562601
theorem B2277867 : Blo 2277435 2277867 := bstep (se 1 (by rfl) ⟨1708400, by rfl⟩ : syracuseStep 2277867 = 3416801) B3416801
theorem B17533589 : Blo 2277435 17533589 := bbase (se 6 (by rfl) ⟨410943, by rfl⟩ : syracuseStep 17533589 = 821887) (by norm_num)
theorem B187024949 : Blo 2277435 187024949 := bstep (se 5 (by rfl) ⟨8766794, by rfl⟩ : syracuseStep 187024949 = 17533589) B17533589
theorem B124683299 : Blo 2277435 124683299 := bstep (se 1 (by rfl) ⟨93512474, by rfl⟩ : syracuseStep 124683299 = 187024949) B187024949
theorem B83122199 : Blo 2277435 83122199 := bstep (se 1 (by rfl) ⟨62341649, by rfl⟩ : syracuseStep 83122199 = 124683299) B124683299
theorem B55414799 : Blo 2277435 55414799 := bstep (se 1 (by rfl) ⟨41561099, by rfl⟩ : syracuseStep 55414799 = 83122199) B83122199
theorem B36943199 : Blo 2277435 36943199 := bstep (se 1 (by rfl) ⟨27707399, by rfl⟩ : syracuseStep 36943199 = 55414799) B55414799
theorem B24628799 : Blo 2277435 24628799 := bstep (se 1 (by rfl) ⟨18471599, by rfl⟩ : syracuseStep 24628799 = 36943199) B36943199
theorem B16419199 : Blo 2277435 16419199 := bstep (se 1 (by rfl) ⟨12314399, by rfl⟩ : syracuseStep 16419199 = 24628799) B24628799
theorem B21892265 : Blo 2277435 21892265 := bstep (se 2 (by rfl) ⟨8209599, by rfl⟩ : syracuseStep 21892265 = 16419199) B16419199
theorem B14594843 : Blo 2277435 14594843 := bstep (se 1 (by rfl) ⟨10946132, by rfl⟩ : syracuseStep 14594843 = 21892265) B21892265
theorem B9729895 : Blo 2277435 9729895 := bstep (se 1 (by rfl) ⟨7297421, by rfl⟩ : syracuseStep 9729895 = 14594843) B14594843
theorem B12973193 : Blo 2277435 12973193 := bstep (se 2 (by rfl) ⟨4864947, by rfl⟩ : syracuseStep 12973193 = 9729895) B9729895
theorem B8648795 : Blo 2277435 8648795 := bstep (se 1 (by rfl) ⟨6486596, by rfl⟩ : syracuseStep 8648795 = 12973193) B12973193
theorem B5765863 : Blo 2277435 5765863 := bstep (se 1 (by rfl) ⟨4324397, by rfl⟩ : syracuseStep 5765863 = 8648795) B8648795
theorem B7687817 : Blo 2277435 7687817 := bstep (se 2 (by rfl) ⟨2882931, by rfl⟩ : syracuseStep 7687817 = 5765863) B5765863
theorem B5125211 : Blo 2277435 5125211 := bstep (se 1 (by rfl) ⟨3843908, by rfl⟩ : syracuseStep 5125211 = 7687817) B7687817
theorem B3416807 : Blo 2277435 3416807 := bstep (se 1 (by rfl) ⟨2562605, by rfl⟩ : syracuseStep 3416807 = 5125211) B5125211
theorem B2277871 : Blo 2277435 2277871 := bstep (se 1 (by rfl) ⟨1708403, by rfl⟩ : syracuseStep 2277871 = 3416807) B3416807
theorem B3416813 : Blo 2277435 3416813 := bbase (se 3 (by rfl) ⟨640652, by rfl⟩ : syracuseStep 3416813 = 1281305) (by norm_num)
theorem B2277875 : Blo 2277435 2277875 := bstep (se 1 (by rfl) ⟨1708406, by rfl⟩ : syracuseStep 2277875 = 3416813) B3416813
theorem B5125229 : Blo 2277435 5125229 := bbase (se 3 (by rfl) ⟨960980, by rfl⟩ : syracuseStep 5125229 = 1921961) (by norm_num)
theorem B3416819 : Blo 2277435 3416819 := bstep (se 1 (by rfl) ⟨2562614, by rfl⟩ : syracuseStep 3416819 = 5125229) B5125229
theorem B2277879 : Blo 2277435 2277879 := bstep (se 1 (by rfl) ⟨1708409, by rfl⟩ : syracuseStep 2277879 = 3416819) B3416819
theorem B4324421 : Blo 2277435 4324421 := bbase (se 4 (by rfl) ⟨405414, by rfl⟩ : syracuseStep 4324421 = 810829) (by norm_num)
theorem B2882947 : Blo 2277435 2882947 := bstep (se 1 (by rfl) ⟨2162210, by rfl⟩ : syracuseStep 2882947 = 4324421) B4324421
theorem B3843929 : Blo 2277435 3843929 := bstep (se 2 (by rfl) ⟨1441473, by rfl⟩ : syracuseStep 3843929 = 2882947) B2882947
theorem B2562619 : Blo 2277435 2562619 := bstep (se 1 (by rfl) ⟨1921964, by rfl⟩ : syracuseStep 2562619 = 3843929) B3843929
theorem B3416825 : Blo 2277435 3416825 := bstep (se 2 (by rfl) ⟨1281309, by rfl⟩ : syracuseStep 3416825 = 2562619) B2562619
theorem B2277883 : Blo 2277435 2277883 := bstep (se 1 (by rfl) ⟨1708412, by rfl⟩ : syracuseStep 2277883 = 3416825) B3416825
theorem B14794069 : Blo 2277435 14794069 := bbase (se 11 (by rfl) ⟨10835, by rfl⟩ : syracuseStep 14794069 = 21671) (by norm_num)
theorem B19725425 : Blo 2277435 19725425 := bstep (se 2 (by rfl) ⟨7397034, by rfl⟩ : syracuseStep 19725425 = 14794069) B14794069
theorem B13150283 : Blo 2277435 13150283 := bstep (se 1 (by rfl) ⟨9862712, by rfl⟩ : syracuseStep 13150283 = 19725425) B19725425
theorem B35067421 : Blo 2277435 35067421 := bstep (se 3 (by rfl) ⟨6575141, by rfl⟩ : syracuseStep 35067421 = 13150283) B13150283
theorem B46756561 : Blo 2277435 46756561 := bstep (se 2 (by rfl) ⟨17533710, by rfl⟩ : syracuseStep 46756561 = 35067421) B35067421
theorem B62342081 : Blo 2277435 62342081 := bstep (se 2 (by rfl) ⟨23378280, by rfl⟩ : syracuseStep 62342081 = 46756561) B46756561
theorem B41561387 : Blo 2277435 41561387 := bstep (se 1 (by rfl) ⟨31171040, by rfl⟩ : syracuseStep 41561387 = 62342081) B62342081
theorem B27707591 : Blo 2277435 27707591 := bstep (se 1 (by rfl) ⟨20780693, by rfl⟩ : syracuseStep 27707591 = 41561387) B41561387
theorem B18471727 : Blo 2277435 18471727 := bstep (se 1 (by rfl) ⟨13853795, by rfl⟩ : syracuseStep 18471727 = 27707591) B27707591
theorem B24628969 : Blo 2277435 24628969 := bstep (se 2 (by rfl) ⟨9235863, by rfl⟩ : syracuseStep 24628969 = 18471727) B18471727
theorem B32838625 : Blo 2277435 32838625 := bstep (se 2 (by rfl) ⟨12314484, by rfl⟩ : syracuseStep 32838625 = 24628969) B24628969
theorem B43784833 : Blo 2277435 43784833 := bstep (se 2 (by rfl) ⟨16419312, by rfl⟩ : syracuseStep 43784833 = 32838625) B32838625
theorem B58379777 : Blo 2277435 58379777 := bstep (se 2 (by rfl) ⟨21892416, by rfl⟩ : syracuseStep 58379777 = 43784833) B43784833
theorem B38919851 : Blo 2277435 38919851 := bstep (se 1 (by rfl) ⟨29189888, by rfl⟩ : syracuseStep 38919851 = 58379777) B58379777
theorem B25946567 : Blo 2277435 25946567 := bstep (se 1 (by rfl) ⟨19459925, by rfl⟩ : syracuseStep 25946567 = 38919851) B38919851
theorem B17297711 : Blo 2277435 17297711 := bstep (se 1 (by rfl) ⟨12973283, by rfl⟩ : syracuseStep 17297711 = 25946567) B25946567
theorem B11531807 : Blo 2277435 11531807 := bstep (se 1 (by rfl) ⟨8648855, by rfl⟩ : syracuseStep 11531807 = 17297711) B17297711
theorem B7687871 : Blo 2277435 7687871 := bstep (se 1 (by rfl) ⟨5765903, by rfl⟩ : syracuseStep 7687871 = 11531807) B11531807
theorem B5125247 : Blo 2277435 5125247 := bstep (se 1 (by rfl) ⟨3843935, by rfl⟩ : syracuseStep 5125247 = 7687871) B7687871
theorem B3416831 : Blo 2277435 3416831 := bstep (se 1 (by rfl) ⟨2562623, by rfl⟩ : syracuseStep 3416831 = 5125247) B5125247
theorem B2277887 : Blo 2277435 2277887 := bstep (se 1 (by rfl) ⟨1708415, by rfl⟩ : syracuseStep 2277887 = 3416831) B3416831
theorem B3416837 : Blo 2277435 3416837 := bbase (se 4 (by rfl) ⟨320328, by rfl⟩ : syracuseStep 3416837 = 640657) (by norm_num)
theorem B2277891 : Blo 2277435 2277891 := bstep (se 1 (by rfl) ⟨1708418, by rfl⟩ : syracuseStep 2277891 = 3416837) B3416837
theorem B3843949 : Blo 2277435 3843949 := bbase (se 3 (by rfl) ⟨720740, by rfl⟩ : syracuseStep 3843949 = 1441481) (by norm_num)
theorem B5125265 : Blo 2277435 5125265 := bstep (se 2 (by rfl) ⟨1921974, by rfl⟩ : syracuseStep 5125265 = 3843949) B3843949
theorem B3416843 : Blo 2277435 3416843 := bstep (se 1 (by rfl) ⟨2562632, by rfl⟩ : syracuseStep 3416843 = 5125265) B5125265
theorem B2277895 : Blo 2277435 2277895 := bstep (se 1 (by rfl) ⟨1708421, by rfl⟩ : syracuseStep 2277895 = 3416843) B3416843
theorem B2562637 : Blo 2277435 2562637 := bbase (se 3 (by rfl) ⟨480494, by rfl⟩ : syracuseStep 2562637 = 960989) (by norm_num)
theorem B3416849 : Blo 2277435 3416849 := bstep (se 2 (by rfl) ⟨1281318, by rfl⟩ : syracuseStep 3416849 = 2562637) B2562637
theorem B2277899 : Blo 2277435 2277899 := bstep (se 1 (by rfl) ⟨1708424, by rfl⟩ : syracuseStep 2277899 = 3416849) B3416849
theorem B7687925 : Blo 2277435 7687925 := bbase (se 5 (by rfl) ⟨360371, by rfl⟩ : syracuseStep 7687925 = 720743) (by norm_num)
theorem B5125283 : Blo 2277435 5125283 := bstep (se 1 (by rfl) ⟨3843962, by rfl⟩ : syracuseStep 5125283 = 7687925) B7687925
theorem B3416855 : Blo 2277435 3416855 := bstep (se 1 (by rfl) ⟨2562641, by rfl⟩ : syracuseStep 3416855 = 5125283) B5125283
theorem B2277903 : Blo 2277435 2277903 := bstep (se 1 (by rfl) ⟨1708427, by rfl⟩ : syracuseStep 2277903 = 3416855) B3416855
theorem B3416861 : Blo 2277435 3416861 := bbase (se 3 (by rfl) ⟨640661, by rfl⟩ : syracuseStep 3416861 = 1281323) (by norm_num)
theorem B2277907 : Blo 2277435 2277907 := bstep (se 1 (by rfl) ⟨1708430, by rfl⟩ : syracuseStep 2277907 = 3416861) B3416861
theorem B5125301 : Blo 2277435 5125301 := bbase (se 5 (by rfl) ⟨240248, by rfl⟩ : syracuseStep 5125301 = 480497) (by norm_num)
theorem B3416867 : Blo 2277435 3416867 := bstep (se 1 (by rfl) ⟨2562650, by rfl⟩ : syracuseStep 3416867 = 5125301) B5125301
theorem B2277911 : Blo 2277435 2277911 := bstep (se 1 (by rfl) ⟨1708433, by rfl⟩ : syracuseStep 2277911 = 3416867) B3416867
theorem B2432521 : Blo 2277435 2432521 := bbase (se 2 (by rfl) ⟨912195, by rfl⟩ : syracuseStep 2432521 = 1824391) (by norm_num)
theorem B12973445 : Blo 2277435 12973445 := bstep (se 4 (by rfl) ⟨1216260, by rfl⟩ : syracuseStep 12973445 = 2432521) B2432521
theorem B8648963 : Blo 2277435 8648963 := bstep (se 1 (by rfl) ⟨6486722, by rfl⟩ : syracuseStep 8648963 = 12973445) B12973445
theorem B5765975 : Blo 2277435 5765975 := bstep (se 1 (by rfl) ⟨4324481, by rfl⟩ : syracuseStep 5765975 = 8648963) B8648963
theorem B3843983 : Blo 2277435 3843983 := bstep (se 1 (by rfl) ⟨2882987, by rfl⟩ : syracuseStep 3843983 = 5765975) B5765975
theorem B2562655 : Blo 2277435 2562655 := bstep (se 1 (by rfl) ⟨1921991, by rfl⟩ : syracuseStep 2562655 = 3843983) B3843983
theorem B3416873 : Blo 2277435 3416873 := bstep (se 2 (by rfl) ⟨1281327, by rfl⟩ : syracuseStep 3416873 = 2562655) B2562655
theorem B2277915 : Blo 2277435 2277915 := bstep (se 1 (by rfl) ⟨1708436, by rfl⟩ : syracuseStep 2277915 = 3416873) B3416873
theorem B2432525 : Blo 2277435 2432525 := bbase (se 3 (by rfl) ⟨456098, by rfl⟩ : syracuseStep 2432525 = 912197) (by norm_num)
theorem B6486733 : Blo 2277435 6486733 := bstep (se 3 (by rfl) ⟨1216262, by rfl⟩ : syracuseStep 6486733 = 2432525) B2432525
theorem B8648977 : Blo 2277435 8648977 := bstep (se 2 (by rfl) ⟨3243366, by rfl⟩ : syracuseStep 8648977 = 6486733) B6486733
theorem B11531969 : Blo 2277435 11531969 := bstep (se 2 (by rfl) ⟨4324488, by rfl⟩ : syracuseStep 11531969 = 8648977) B8648977
theorem B7687979 : Blo 2277435 7687979 := bstep (se 1 (by rfl) ⟨5765984, by rfl⟩ : syracuseStep 7687979 = 11531969) B11531969
theorem B5125319 : Blo 2277435 5125319 := bstep (se 1 (by rfl) ⟨3843989, by rfl⟩ : syracuseStep 5125319 = 7687979) B7687979
theorem B3416879 : Blo 2277435 3416879 := bstep (se 1 (by rfl) ⟨2562659, by rfl⟩ : syracuseStep 3416879 = 5125319) B5125319
theorem B2277919 : Blo 2277435 2277919 := bstep (se 1 (by rfl) ⟨1708439, by rfl⟩ : syracuseStep 2277919 = 3416879) B3416879
theorem B3416885 : Blo 2277435 3416885 := bbase (se 5 (by rfl) ⟨160166, by rfl⟩ : syracuseStep 3416885 = 320333) (by norm_num)
theorem B2277923 : Blo 2277435 2277923 := bstep (se 1 (by rfl) ⟨1708442, by rfl⟩ : syracuseStep 2277923 = 3416885) B3416885
theorem B5766005 : Blo 2277435 5766005 := bbase (se 5 (by rfl) ⟨270281, by rfl⟩ : syracuseStep 5766005 = 540563) (by norm_num)
theorem B3844003 : Blo 2277435 3844003 := bstep (se 1 (by rfl) ⟨2883002, by rfl⟩ : syracuseStep 3844003 = 5766005) B5766005
theorem B5125337 : Blo 2277435 5125337 := bstep (se 2 (by rfl) ⟨1922001, by rfl⟩ : syracuseStep 5125337 = 3844003) B3844003
theorem B3416891 : Blo 2277435 3416891 := bstep (se 1 (by rfl) ⟨2562668, by rfl⟩ : syracuseStep 3416891 = 5125337) B5125337
theorem B2277927 : Blo 2277435 2277927 := bstep (se 1 (by rfl) ⟨1708445, by rfl⟩ : syracuseStep 2277927 = 3416891) B3416891
theorem B2562673 : Blo 2277435 2562673 := bbase (se 2 (by rfl) ⟨961002, by rfl⟩ : syracuseStep 2562673 = 1922005) (by norm_num)
theorem B3416897 : Blo 2277435 3416897 := bstep (se 2 (by rfl) ⟨1281336, by rfl⟩ : syracuseStep 3416897 = 2562673) B2562673
theorem B2277931 : Blo 2277435 2277931 := bstep (se 1 (by rfl) ⟨1708448, by rfl⟩ : syracuseStep 2277931 = 3416897) B3416897
theorem B3698597 : Blo 2277435 3698597 := bbase (se 4 (by rfl) ⟨346743, by rfl⟩ : syracuseStep 3698597 = 693487) (by norm_num)
theorem B2465731 : Blo 2277435 2465731 := bstep (se 1 (by rfl) ⟨1849298, by rfl⟩ : syracuseStep 2465731 = 3698597) B3698597
theorem B13150565 : Blo 2277435 13150565 := bstep (se 4 (by rfl) ⟨1232865, by rfl⟩ : syracuseStep 13150565 = 2465731) B2465731
theorem B8767043 : Blo 2277435 8767043 := bstep (se 1 (by rfl) ⟨6575282, by rfl⟩ : syracuseStep 8767043 = 13150565) B13150565
theorem B5844695 : Blo 2277435 5844695 := bstep (se 1 (by rfl) ⟨4383521, by rfl⟩ : syracuseStep 5844695 = 8767043) B8767043
theorem B15585853 : Blo 2277435 15585853 := bstep (se 3 (by rfl) ⟨2922347, by rfl⟩ : syracuseStep 15585853 = 5844695) B5844695
theorem B20781137 : Blo 2277435 20781137 := bstep (se 2 (by rfl) ⟨7792926, by rfl⟩ : syracuseStep 20781137 = 15585853) B15585853
theorem B13854091 : Blo 2277435 13854091 := bstep (se 1 (by rfl) ⟨10390568, by rfl⟩ : syracuseStep 13854091 = 20781137) B20781137
theorem B18472121 : Blo 2277435 18472121 := bstep (se 2 (by rfl) ⟨6927045, by rfl⟩ : syracuseStep 18472121 = 13854091) B13854091
theorem B12314747 : Blo 2277435 12314747 := bstep (se 1 (by rfl) ⟨9236060, by rfl⟩ : syracuseStep 12314747 = 18472121) B18472121
theorem B8209831 : Blo 2277435 8209831 := bstep (se 1 (by rfl) ⟨6157373, by rfl⟩ : syracuseStep 8209831 = 12314747) B12314747
theorem B10946441 : Blo 2277435 10946441 := bstep (se 2 (by rfl) ⟨4104915, by rfl⟩ : syracuseStep 10946441 = 8209831) B8209831
theorem B7297627 : Blo 2277435 7297627 := bstep (se 1 (by rfl) ⟨5473220, by rfl⟩ : syracuseStep 7297627 = 10946441) B10946441
theorem B9730169 : Blo 2277435 9730169 := bstep (se 2 (by rfl) ⟨3648813, by rfl⟩ : syracuseStep 9730169 = 7297627) B7297627
theorem B6486779 : Blo 2277435 6486779 := bstep (se 1 (by rfl) ⟨4865084, by rfl⟩ : syracuseStep 6486779 = 9730169) B9730169
theorem B4324519 : Blo 2277435 4324519 := bstep (se 1 (by rfl) ⟨3243389, by rfl⟩ : syracuseStep 4324519 = 6486779) B6486779
theorem B5766025 : Blo 2277435 5766025 := bstep (se 2 (by rfl) ⟨2162259, by rfl⟩ : syracuseStep 5766025 = 4324519) B4324519
theorem B7688033 : Blo 2277435 7688033 := bstep (se 2 (by rfl) ⟨2883012, by rfl⟩ : syracuseStep 7688033 = 5766025) B5766025
theorem B5125355 : Blo 2277435 5125355 := bstep (se 1 (by rfl) ⟨3844016, by rfl⟩ : syracuseStep 5125355 = 7688033) B7688033
theorem B3416903 : Blo 2277435 3416903 := bstep (se 1 (by rfl) ⟨2562677, by rfl⟩ : syracuseStep 3416903 = 5125355) B5125355
theorem B2277935 : Blo 2277435 2277935 := bstep (se 1 (by rfl) ⟨1708451, by rfl⟩ : syracuseStep 2277935 = 3416903) B3416903
theorem B3416909 : Blo 2277435 3416909 := bbase (se 3 (by rfl) ⟨640670, by rfl⟩ : syracuseStep 3416909 = 1281341) (by norm_num)
theorem B2277939 : Blo 2277435 2277939 := bstep (se 1 (by rfl) ⟨1708454, by rfl⟩ : syracuseStep 2277939 = 3416909) B3416909
theorem B5125373 : Blo 2277435 5125373 := bbase (se 3 (by rfl) ⟨961007, by rfl⟩ : syracuseStep 5125373 = 1922015) (by norm_num)
theorem B3416915 : Blo 2277435 3416915 := bstep (se 1 (by rfl) ⟨2562686, by rfl⟩ : syracuseStep 3416915 = 5125373) B5125373
theorem B2277943 : Blo 2277435 2277943 := bstep (se 1 (by rfl) ⟨1708457, by rfl⟩ : syracuseStep 2277943 = 3416915) B3416915
theorem B3844037 : Blo 2277435 3844037 := bbase (se 4 (by rfl) ⟨360378, by rfl⟩ : syracuseStep 3844037 = 720757) (by norm_num)
theorem B2562691 : Blo 2277435 2562691 := bstep (se 1 (by rfl) ⟨1922018, by rfl⟩ : syracuseStep 2562691 = 3844037) B3844037
theorem B3416921 : Blo 2277435 3416921 := bstep (se 2 (by rfl) ⟨1281345, by rfl⟩ : syracuseStep 3416921 = 2562691) B2562691
theorem B2277947 : Blo 2277435 2277947 := bstep (se 1 (by rfl) ⟨1708460, by rfl⟩ : syracuseStep 2277947 = 3416921) B3416921
theorem B17298197 : Blo 2277435 17298197 := bbase (se 6 (by rfl) ⟨405426, by rfl⟩ : syracuseStep 17298197 = 810853) (by norm_num)
theorem B11532131 : Blo 2277435 11532131 := bstep (se 1 (by rfl) ⟨8649098, by rfl⟩ : syracuseStep 11532131 = 17298197) B17298197
theorem B7688087 : Blo 2277435 7688087 := bstep (se 1 (by rfl) ⟨5766065, by rfl⟩ : syracuseStep 7688087 = 11532131) B11532131
theorem B5125391 : Blo 2277435 5125391 := bstep (se 1 (by rfl) ⟨3844043, by rfl⟩ : syracuseStep 5125391 = 7688087) B7688087
theorem B3416927 : Blo 2277435 3416927 := bstep (se 1 (by rfl) ⟨2562695, by rfl⟩ : syracuseStep 3416927 = 5125391) B5125391
theorem B2277951 : Blo 2277435 2277951 := bstep (se 1 (by rfl) ⟨1708463, by rfl⟩ : syracuseStep 2277951 = 3416927) B3416927
theorem B3416933 : Blo 2277435 3416933 := bbase (se 4 (by rfl) ⟨320337, by rfl⟩ : syracuseStep 3416933 = 640675) (by norm_num)
theorem B2277955 : Blo 2277435 2277955 := bstep (se 1 (by rfl) ⟨1708466, by rfl⟩ : syracuseStep 2277955 = 3416933) B3416933
theorem B4324565 : Blo 2277435 4324565 := bbase (se 7 (by rfl) ⟨50678, by rfl⟩ : syracuseStep 4324565 = 101357) (by norm_num)
theorem B2883043 : Blo 2277435 2883043 := bstep (se 1 (by rfl) ⟨2162282, by rfl⟩ : syracuseStep 2883043 = 4324565) B4324565
theorem B3844057 : Blo 2277435 3844057 := bstep (se 2 (by rfl) ⟨1441521, by rfl⟩ : syracuseStep 3844057 = 2883043) B2883043
theorem B5125409 : Blo 2277435 5125409 := bstep (se 2 (by rfl) ⟨1922028, by rfl⟩ : syracuseStep 5125409 = 3844057) B3844057
theorem B3416939 : Blo 2277435 3416939 := bstep (se 1 (by rfl) ⟨2562704, by rfl⟩ : syracuseStep 3416939 = 5125409) B5125409
theorem B2277959 : Blo 2277435 2277959 := bstep (se 1 (by rfl) ⟨1708469, by rfl⟩ : syracuseStep 2277959 = 3416939) B3416939
theorem B2562709 : Blo 2277435 2562709 := bbase (se 6 (by rfl) ⟨60063, by rfl⟩ : syracuseStep 2562709 = 120127) (by norm_num)
theorem B3416945 : Blo 2277435 3416945 := bstep (se 2 (by rfl) ⟨1281354, by rfl⟩ : syracuseStep 3416945 = 2562709) B2562709
theorem B2277963 : Blo 2277435 2277963 := bstep (se 1 (by rfl) ⟨1708472, by rfl⟩ : syracuseStep 2277963 = 3416945) B3416945
theorem B2883053 : Blo 2277435 2883053 := bbase (se 3 (by rfl) ⟨540572, by rfl⟩ : syracuseStep 2883053 = 1081145) (by norm_num)
theorem B7688141 : Blo 2277435 7688141 := bstep (se 3 (by rfl) ⟨1441526, by rfl⟩ : syracuseStep 7688141 = 2883053) B2883053
theorem B5125427 : Blo 2277435 5125427 := bstep (se 1 (by rfl) ⟨3844070, by rfl⟩ : syracuseStep 5125427 = 7688141) B7688141
theorem B3416951 : Blo 2277435 3416951 := bstep (se 1 (by rfl) ⟨2562713, by rfl⟩ : syracuseStep 3416951 = 5125427) B5125427
theorem B2277967 : Blo 2277435 2277967 := bstep (se 1 (by rfl) ⟨1708475, by rfl⟩ : syracuseStep 2277967 = 3416951) B3416951
theorem B3416957 : Blo 2277435 3416957 := bbase (se 3 (by rfl) ⟨640679, by rfl⟩ : syracuseStep 3416957 = 1281359) (by norm_num)
theorem B2277971 : Blo 2277435 2277971 := bstep (se 1 (by rfl) ⟨1708478, by rfl⟩ : syracuseStep 2277971 = 3416957) B3416957
theorem B5125445 : Blo 2277435 5125445 := bbase (se 4 (by rfl) ⟨480510, by rfl⟩ : syracuseStep 5125445 = 961021) (by norm_num)
theorem B3416963 : Blo 2277435 3416963 := bstep (se 1 (by rfl) ⟨2562722, by rfl⟩ : syracuseStep 3416963 = 5125445) B5125445
theorem B2277975 : Blo 2277435 2277975 := bstep (se 1 (by rfl) ⟨1708481, by rfl⟩ : syracuseStep 2277975 = 3416963) B3416963
theorem B3698669 : Blo 2277435 3698669 := bbase (se 3 (by rfl) ⟨693500, by rfl⟩ : syracuseStep 3698669 = 1387001) (by norm_num)
theorem B9863117 : Blo 2277435 9863117 := bstep (se 3 (by rfl) ⟨1849334, by rfl⟩ : syracuseStep 9863117 = 3698669) B3698669
theorem B6575411 : Blo 2277435 6575411 := bstep (se 1 (by rfl) ⟨4931558, by rfl⟩ : syracuseStep 6575411 = 9863117) B9863117
theorem B4383607 : Blo 2277435 4383607 := bstep (se 1 (by rfl) ⟨3287705, by rfl⟩ : syracuseStep 4383607 = 6575411) B6575411
theorem B5844809 : Blo 2277435 5844809 := bstep (se 2 (by rfl) ⟨2191803, by rfl⟩ : syracuseStep 5844809 = 4383607) B4383607
theorem B15586157 : Blo 2277435 15586157 := bstep (se 3 (by rfl) ⟨2922404, by rfl⟩ : syracuseStep 15586157 = 5844809) B5844809
theorem B10390771 : Blo 2277435 10390771 := bstep (se 1 (by rfl) ⟨7793078, by rfl⟩ : syracuseStep 10390771 = 15586157) B15586157
theorem B13854361 : Blo 2277435 13854361 := bstep (se 2 (by rfl) ⟨5195385, by rfl⟩ : syracuseStep 13854361 = 10390771) B10390771
theorem B18472481 : Blo 2277435 18472481 := bstep (se 2 (by rfl) ⟨6927180, by rfl⟩ : syracuseStep 18472481 = 13854361) B13854361
theorem B12314987 : Blo 2277435 12314987 := bstep (se 1 (by rfl) ⟨9236240, by rfl⟩ : syracuseStep 12314987 = 18472481) B18472481
theorem B8209991 : Blo 2277435 8209991 := bstep (se 1 (by rfl) ⟨6157493, by rfl⟩ : syracuseStep 8209991 = 12314987) B12314987
theorem B5473327 : Blo 2277435 5473327 := bstep (se 1 (by rfl) ⟨4104995, by rfl⟩ : syracuseStep 5473327 = 8209991) B8209991
theorem B7297769 : Blo 2277435 7297769 := bstep (se 2 (by rfl) ⟨2736663, by rfl⟩ : syracuseStep 7297769 = 5473327) B5473327
theorem B4865179 : Blo 2277435 4865179 := bstep (se 1 (by rfl) ⟨3648884, by rfl⟩ : syracuseStep 4865179 = 7297769) B7297769
theorem B6486905 : Blo 2277435 6486905 := bstep (se 2 (by rfl) ⟨2432589, by rfl⟩ : syracuseStep 6486905 = 4865179) B4865179
theorem B4324603 : Blo 2277435 4324603 := bstep (se 1 (by rfl) ⟨3243452, by rfl⟩ : syracuseStep 4324603 = 6486905) B6486905
theorem B5766137 : Blo 2277435 5766137 := bstep (se 2 (by rfl) ⟨2162301, by rfl⟩ : syracuseStep 5766137 = 4324603) B4324603
theorem B3844091 : Blo 2277435 3844091 := bstep (se 1 (by rfl) ⟨2883068, by rfl⟩ : syracuseStep 3844091 = 5766137) B5766137
theorem B2562727 : Blo 2277435 2562727 := bstep (se 1 (by rfl) ⟨1922045, by rfl⟩ : syracuseStep 2562727 = 3844091) B3844091
theorem B3416969 : Blo 2277435 3416969 := bstep (se 2 (by rfl) ⟨1281363, by rfl⟩ : syracuseStep 3416969 = 2562727) B2562727
theorem B2277979 : Blo 2277435 2277979 := bstep (se 1 (by rfl) ⟨1708484, by rfl⟩ : syracuseStep 2277979 = 3416969) B3416969
theorem B11532293 : Blo 2277435 11532293 := bbase (se 4 (by rfl) ⟨1081152, by rfl⟩ : syracuseStep 11532293 = 2162305) (by norm_num)
theorem B7688195 : Blo 2277435 7688195 := bstep (se 1 (by rfl) ⟨5766146, by rfl⟩ : syracuseStep 7688195 = 11532293) B11532293
theorem B5125463 : Blo 2277435 5125463 := bstep (se 1 (by rfl) ⟨3844097, by rfl⟩ : syracuseStep 5125463 = 7688195) B7688195
theorem B3416975 : Blo 2277435 3416975 := bstep (se 1 (by rfl) ⟨2562731, by rfl⟩ : syracuseStep 3416975 = 5125463) B5125463
theorem B2277983 : Blo 2277435 2277983 := bstep (se 1 (by rfl) ⟨1708487, by rfl⟩ : syracuseStep 2277983 = 3416975) B3416975
theorem B3416981 : Blo 2277435 3416981 := bbase (se 6 (by rfl) ⟨80085, by rfl⟩ : syracuseStep 3416981 = 160171) (by norm_num)
theorem B2277987 : Blo 2277435 2277987 := bstep (se 1 (by rfl) ⟨1708490, by rfl⟩ : syracuseStep 2277987 = 3416981) B3416981
theorem B12973877 : Blo 2277435 12973877 := bbase (se 5 (by rfl) ⟨608150, by rfl⟩ : syracuseStep 12973877 = 1216301) (by norm_num)
theorem B8649251 : Blo 2277435 8649251 := bstep (se 1 (by rfl) ⟨6486938, by rfl⟩ : syracuseStep 8649251 = 12973877) B12973877
theorem B5766167 : Blo 2277435 5766167 := bstep (se 1 (by rfl) ⟨4324625, by rfl⟩ : syracuseStep 5766167 = 8649251) B8649251
theorem B3844111 : Blo 2277435 3844111 := bstep (se 1 (by rfl) ⟨2883083, by rfl⟩ : syracuseStep 3844111 = 5766167) B5766167
theorem B5125481 : Blo 2277435 5125481 := bstep (se 2 (by rfl) ⟨1922055, by rfl⟩ : syracuseStep 5125481 = 3844111) B3844111
theorem B3416987 : Blo 2277435 3416987 := bstep (se 1 (by rfl) ⟨2562740, by rfl⟩ : syracuseStep 3416987 = 5125481) B5125481
theorem B2277991 : Blo 2277435 2277991 := bstep (se 1 (by rfl) ⟨1708493, by rfl⟩ : syracuseStep 2277991 = 3416987) B3416987
theorem B2562745 : Blo 2277435 2562745 := bbase (se 2 (by rfl) ⟨961029, by rfl⟩ : syracuseStep 2562745 = 1922059) (by norm_num)
theorem B3416993 : Blo 2277435 3416993 := bstep (se 2 (by rfl) ⟨1281372, by rfl⟩ : syracuseStep 3416993 = 2562745) B2562745
theorem B2277995 : Blo 2277435 2277995 := bstep (se 1 (by rfl) ⟨1708496, by rfl⟩ : syracuseStep 2277995 = 3416993) B3416993
theorem B4865221 : Blo 2277435 4865221 := bbase (se 4 (by rfl) ⟨456114, by rfl⟩ : syracuseStep 4865221 = 912229) (by norm_num)
theorem B6486961 : Blo 2277435 6486961 := bstep (se 2 (by rfl) ⟨2432610, by rfl⟩ : syracuseStep 6486961 = 4865221) B4865221
theorem B8649281 : Blo 2277435 8649281 := bstep (se 2 (by rfl) ⟨3243480, by rfl⟩ : syracuseStep 8649281 = 6486961) B6486961
theorem B5766187 : Blo 2277435 5766187 := bstep (se 1 (by rfl) ⟨4324640, by rfl⟩ : syracuseStep 5766187 = 8649281) B8649281
theorem B7688249 : Blo 2277435 7688249 := bstep (se 2 (by rfl) ⟨2883093, by rfl⟩ : syracuseStep 7688249 = 5766187) B5766187
theorem B5125499 : Blo 2277435 5125499 := bstep (se 1 (by rfl) ⟨3844124, by rfl⟩ : syracuseStep 5125499 = 7688249) B7688249
theorem B3416999 : Blo 2277435 3416999 := bstep (se 1 (by rfl) ⟨2562749, by rfl⟩ : syracuseStep 3416999 = 5125499) B5125499
theorem B2277999 : Blo 2277435 2277999 := bstep (se 1 (by rfl) ⟨1708499, by rfl⟩ : syracuseStep 2277999 = 3416999) B3416999
theorem B3417005 : Blo 2277435 3417005 := bbase (se 3 (by rfl) ⟨640688, by rfl⟩ : syracuseStep 3417005 = 1281377) (by norm_num)
theorem B2278003 : Blo 2277435 2278003 := bstep (se 1 (by rfl) ⟨1708502, by rfl⟩ : syracuseStep 2278003 = 3417005) B3417005
theorem B5125517 : Blo 2277435 5125517 := bbase (se 3 (by rfl) ⟨961034, by rfl⟩ : syracuseStep 5125517 = 1922069) (by norm_num)
theorem B3417011 : Blo 2277435 3417011 := bstep (se 1 (by rfl) ⟨2562758, by rfl⟩ : syracuseStep 3417011 = 5125517) B5125517
theorem B2278007 : Blo 2277435 2278007 := bstep (se 1 (by rfl) ⟨1708505, by rfl⟩ : syracuseStep 2278007 = 3417011) B3417011
theorem B2883109 : Blo 2277435 2883109 := bbase (se 4 (by rfl) ⟨270291, by rfl⟩ : syracuseStep 2883109 = 540583) (by norm_num)
theorem B3844145 : Blo 2277435 3844145 := bstep (se 2 (by rfl) ⟨1441554, by rfl⟩ : syracuseStep 3844145 = 2883109) B2883109
theorem B2562763 : Blo 2277435 2562763 := bstep (se 1 (by rfl) ⟨1922072, by rfl⟩ : syracuseStep 2562763 = 3844145) B3844145
theorem B3417017 : Blo 2277435 3417017 := bstep (se 2 (by rfl) ⟨1281381, by rfl⟩ : syracuseStep 3417017 = 2562763) B2562763
theorem B2278011 : Blo 2277435 2278011 := bstep (se 1 (by rfl) ⟨1708508, by rfl⟩ : syracuseStep 2278011 = 3417017) B3417017
theorem B8767349 : Blo 2277435 8767349 := bbase (se 5 (by rfl) ⟨410969, by rfl⟩ : syracuseStep 8767349 = 821939) (by norm_num)
theorem B5844899 : Blo 2277435 5844899 := bstep (se 1 (by rfl) ⟨4383674, by rfl⟩ : syracuseStep 5844899 = 8767349) B8767349
theorem B15586397 : Blo 2277435 15586397 := bstep (se 3 (by rfl) ⟨2922449, by rfl⟩ : syracuseStep 15586397 = 5844899) B5844899
theorem B10390931 : Blo 2277435 10390931 := bstep (se 1 (by rfl) ⟨7793198, by rfl⟩ : syracuseStep 10390931 = 15586397) B15586397
theorem B6927287 : Blo 2277435 6927287 := bstep (se 1 (by rfl) ⟨5195465, by rfl⟩ : syracuseStep 6927287 = 10390931) B10390931
theorem B73891061 : Blo 2277435 73891061 := bstep (se 5 (by rfl) ⟨3463643, by rfl⟩ : syracuseStep 73891061 = 6927287) B6927287
theorem B49260707 : Blo 2277435 49260707 := bstep (se 1 (by rfl) ⟨36945530, by rfl⟩ : syracuseStep 49260707 = 73891061) B73891061
theorem B32840471 : Blo 2277435 32840471 := bstep (se 1 (by rfl) ⟨24630353, by rfl⟩ : syracuseStep 32840471 = 49260707) B49260707
theorem B21893647 : Blo 2277435 21893647 := bstep (se 1 (by rfl) ⟨16420235, by rfl⟩ : syracuseStep 21893647 = 32840471) B32840471
theorem B29191529 : Blo 2277435 29191529 := bstep (se 2 (by rfl) ⟨10946823, by rfl⟩ : syracuseStep 29191529 = 21893647) B21893647
theorem B19461019 : Blo 2277435 19461019 := bstep (se 1 (by rfl) ⟨14595764, by rfl⟩ : syracuseStep 19461019 = 29191529) B29191529
theorem B25948025 : Blo 2277435 25948025 := bstep (se 2 (by rfl) ⟨9730509, by rfl⟩ : syracuseStep 25948025 = 19461019) B19461019
theorem B17298683 : Blo 2277435 17298683 := bstep (se 1 (by rfl) ⟨12974012, by rfl⟩ : syracuseStep 17298683 = 25948025) B25948025
theorem B11532455 : Blo 2277435 11532455 := bstep (se 1 (by rfl) ⟨8649341, by rfl⟩ : syracuseStep 11532455 = 17298683) B17298683
theorem B7688303 : Blo 2277435 7688303 := bstep (se 1 (by rfl) ⟨5766227, by rfl⟩ : syracuseStep 7688303 = 11532455) B11532455
theorem B5125535 : Blo 2277435 5125535 := bstep (se 1 (by rfl) ⟨3844151, by rfl⟩ : syracuseStep 5125535 = 7688303) B7688303
theorem B3417023 : Blo 2277435 3417023 := bstep (se 1 (by rfl) ⟨2562767, by rfl⟩ : syracuseStep 3417023 = 5125535) B5125535
theorem B2278015 : Blo 2277435 2278015 := bstep (se 1 (by rfl) ⟨1708511, by rfl⟩ : syracuseStep 2278015 = 3417023) B3417023
theorem B3417029 : Blo 2277435 3417029 := bbase (se 4 (by rfl) ⟨320346, by rfl⟩ : syracuseStep 3417029 = 640693) (by norm_num)
theorem B2278019 : Blo 2277435 2278019 := bstep (se 1 (by rfl) ⟨1708514, by rfl⟩ : syracuseStep 2278019 = 3417029) B3417029
theorem B3844165 : Blo 2277435 3844165 := bbase (se 4 (by rfl) ⟨360390, by rfl⟩ : syracuseStep 3844165 = 720781) (by norm_num)
theorem B5125553 : Blo 2277435 5125553 := bstep (se 2 (by rfl) ⟨1922082, by rfl⟩ : syracuseStep 5125553 = 3844165) B3844165
theorem B3417035 : Blo 2277435 3417035 := bstep (se 1 (by rfl) ⟨2562776, by rfl⟩ : syracuseStep 3417035 = 5125553) B5125553
theorem B2278023 : Blo 2277435 2278023 := bstep (se 1 (by rfl) ⟨1708517, by rfl⟩ : syracuseStep 2278023 = 3417035) B3417035
theorem B2562781 : Blo 2277435 2562781 := bbase (se 3 (by rfl) ⟨480521, by rfl⟩ : syracuseStep 2562781 = 961043) (by norm_num)
theorem B3417041 : Blo 2277435 3417041 := bstep (se 2 (by rfl) ⟨1281390, by rfl⟩ : syracuseStep 3417041 = 2562781) B2562781
theorem B2278027 : Blo 2277435 2278027 := bstep (se 1 (by rfl) ⟨1708520, by rfl⟩ : syracuseStep 2278027 = 3417041) B3417041
theorem B7688357 : Blo 2277435 7688357 := bbase (se 4 (by rfl) ⟨720783, by rfl⟩ : syracuseStep 7688357 = 1441567) (by norm_num)
theorem B5125571 : Blo 2277435 5125571 := bstep (se 1 (by rfl) ⟨3844178, by rfl⟩ : syracuseStep 5125571 = 7688357) B7688357
theorem B3417047 : Blo 2277435 3417047 := bstep (se 1 (by rfl) ⟨2562785, by rfl⟩ : syracuseStep 3417047 = 5125571) B5125571
theorem B2278031 : Blo 2277435 2278031 := bstep (se 1 (by rfl) ⟨1708523, by rfl⟩ : syracuseStep 2278031 = 3417047) B3417047
theorem B3417053 : Blo 2277435 3417053 := bbase (se 3 (by rfl) ⟨640697, by rfl⟩ : syracuseStep 3417053 = 1281395) (by norm_num)
theorem B2278035 : Blo 2277435 2278035 := bstep (se 1 (by rfl) ⟨1708526, by rfl⟩ : syracuseStep 2278035 = 3417053) B3417053
theorem B5125589 : Blo 2277435 5125589 := bbase (se 7 (by rfl) ⟨60065, by rfl⟩ : syracuseStep 5125589 = 120131) (by norm_num)
theorem B3417059 : Blo 2277435 3417059 := bstep (se 1 (by rfl) ⟨2562794, by rfl⟩ : syracuseStep 3417059 = 5125589) B5125589
theorem B2278039 : Blo 2277435 2278039 := bstep (se 1 (by rfl) ⟨1708529, by rfl⟩ : syracuseStep 2278039 = 3417059) B3417059
theorem B5844973 : Blo 2277435 5844973 := bbase (se 3 (by rfl) ⟨1095932, by rfl⟩ : syracuseStep 5844973 = 2191865) (by norm_num)
theorem B7793297 : Blo 2277435 7793297 := bstep (se 2 (by rfl) ⟨2922486, by rfl⟩ : syracuseStep 7793297 = 5844973) B5844973
theorem B5195531 : Blo 2277435 5195531 := bstep (se 1 (by rfl) ⟨3896648, by rfl⟩ : syracuseStep 5195531 = 7793297) B7793297
theorem B3463687 : Blo 2277435 3463687 := bstep (se 1 (by rfl) ⟨2597765, by rfl⟩ : syracuseStep 3463687 = 5195531) B5195531
theorem B18472997 : Blo 2277435 18472997 := bstep (se 4 (by rfl) ⟨1731843, by rfl⟩ : syracuseStep 18472997 = 3463687) B3463687
theorem B12315331 : Blo 2277435 12315331 := bstep (se 1 (by rfl) ⟨9236498, by rfl⟩ : syracuseStep 12315331 = 18472997) B18472997
theorem B16420441 : Blo 2277435 16420441 := bstep (se 2 (by rfl) ⟨6157665, by rfl⟩ : syracuseStep 16420441 = 12315331) B12315331
theorem B21893921 : Blo 2277435 21893921 := bstep (se 2 (by rfl) ⟨8210220, by rfl⟩ : syracuseStep 21893921 = 16420441) B16420441
theorem B14595947 : Blo 2277435 14595947 := bstep (se 1 (by rfl) ⟨10946960, by rfl⟩ : syracuseStep 14595947 = 21893921) B21893921
theorem B9730631 : Blo 2277435 9730631 := bstep (se 1 (by rfl) ⟨7297973, by rfl⟩ : syracuseStep 9730631 = 14595947) B14595947
theorem B6487087 : Blo 2277435 6487087 := bstep (se 1 (by rfl) ⟨4865315, by rfl⟩ : syracuseStep 6487087 = 9730631) B9730631
theorem B8649449 : Blo 2277435 8649449 := bstep (se 2 (by rfl) ⟨3243543, by rfl⟩ : syracuseStep 8649449 = 6487087) B6487087
theorem B5766299 : Blo 2277435 5766299 := bstep (se 1 (by rfl) ⟨4324724, by rfl⟩ : syracuseStep 5766299 = 8649449) B8649449
theorem B3844199 : Blo 2277435 3844199 := bstep (se 1 (by rfl) ⟨2883149, by rfl⟩ : syracuseStep 3844199 = 5766299) B5766299
theorem B2562799 : Blo 2277435 2562799 := bstep (se 1 (by rfl) ⟨1922099, by rfl⟩ : syracuseStep 2562799 = 3844199) B3844199
theorem B3417065 : Blo 2277435 3417065 := bstep (se 2 (by rfl) ⟨1281399, by rfl⟩ : syracuseStep 3417065 = 2562799) B2562799
theorem B2278043 : Blo 2277435 2278043 := bstep (se 1 (by rfl) ⟨1708532, by rfl⟩ : syracuseStep 2278043 = 3417065) B3417065
theorem B4105117 : Blo 2277435 4105117 := bbase (se 3 (by rfl) ⟨769709, by rfl⟩ : syracuseStep 4105117 = 1539419) (by norm_num)
theorem B5473489 : Blo 2277435 5473489 := bstep (se 2 (by rfl) ⟨2052558, by rfl⟩ : syracuseStep 5473489 = 4105117) B4105117
theorem B7297985 : Blo 2277435 7297985 := bstep (se 2 (by rfl) ⟨2736744, by rfl⟩ : syracuseStep 7297985 = 5473489) B5473489
theorem B19461293 : Blo 2277435 19461293 := bstep (se 3 (by rfl) ⟨3648992, by rfl⟩ : syracuseStep 19461293 = 7297985) B7297985
theorem B12974195 : Blo 2277435 12974195 := bstep (se 1 (by rfl) ⟨9730646, by rfl⟩ : syracuseStep 12974195 = 19461293) B19461293
theorem B8649463 : Blo 2277435 8649463 := bstep (se 1 (by rfl) ⟨6487097, by rfl⟩ : syracuseStep 8649463 = 12974195) B12974195
theorem B11532617 : Blo 2277435 11532617 := bstep (se 2 (by rfl) ⟨4324731, by rfl⟩ : syracuseStep 11532617 = 8649463) B8649463
theorem B7688411 : Blo 2277435 7688411 := bstep (se 1 (by rfl) ⟨5766308, by rfl⟩ : syracuseStep 7688411 = 11532617) B11532617
theorem B5125607 : Blo 2277435 5125607 := bstep (se 1 (by rfl) ⟨3844205, by rfl⟩ : syracuseStep 5125607 = 7688411) B7688411
theorem B3417071 : Blo 2277435 3417071 := bstep (se 1 (by rfl) ⟨2562803, by rfl⟩ : syracuseStep 3417071 = 5125607) B5125607
theorem B2278047 : Blo 2277435 2278047 := bstep (se 1 (by rfl) ⟨1708535, by rfl⟩ : syracuseStep 2278047 = 3417071) B3417071
theorem B3417077 : Blo 2277435 3417077 := bbase (se 5 (by rfl) ⟨160175, by rfl⟩ : syracuseStep 3417077 = 320351) (by norm_num)
theorem B2278051 : Blo 2277435 2278051 := bstep (se 1 (by rfl) ⟨1708538, by rfl⟩ : syracuseStep 2278051 = 3417077) B3417077
theorem B4865341 : Blo 2277435 4865341 := bbase (se 3 (by rfl) ⟨912251, by rfl⟩ : syracuseStep 4865341 = 1824503) (by norm_num)
theorem B6487121 : Blo 2277435 6487121 := bstep (se 2 (by rfl) ⟨2432670, by rfl⟩ : syracuseStep 6487121 = 4865341) B4865341
theorem B4324747 : Blo 2277435 4324747 := bstep (se 1 (by rfl) ⟨3243560, by rfl⟩ : syracuseStep 4324747 = 6487121) B6487121
theorem B5766329 : Blo 2277435 5766329 := bstep (se 2 (by rfl) ⟨2162373, by rfl⟩ : syracuseStep 5766329 = 4324747) B4324747
theorem B3844219 : Blo 2277435 3844219 := bstep (se 1 (by rfl) ⟨2883164, by rfl⟩ : syracuseStep 3844219 = 5766329) B5766329
theorem B5125625 : Blo 2277435 5125625 := bstep (se 2 (by rfl) ⟨1922109, by rfl⟩ : syracuseStep 5125625 = 3844219) B3844219
theorem B3417083 : Blo 2277435 3417083 := bstep (se 1 (by rfl) ⟨2562812, by rfl⟩ : syracuseStep 3417083 = 5125625) B5125625
theorem B2278055 : Blo 2277435 2278055 := bstep (se 1 (by rfl) ⟨1708541, by rfl⟩ : syracuseStep 2278055 = 3417083) B3417083
theorem B2562817 : Blo 2277435 2562817 := bbase (se 2 (by rfl) ⟨961056, by rfl⟩ : syracuseStep 2562817 = 1922113) (by norm_num)
theorem B3417089 : Blo 2277435 3417089 := bstep (se 2 (by rfl) ⟨1281408, by rfl⟩ : syracuseStep 3417089 = 2562817) B2562817
theorem B2278059 : Blo 2277435 2278059 := bstep (se 1 (by rfl) ⟨1708544, by rfl⟩ : syracuseStep 2278059 = 3417089) B3417089
theorem B5766349 : Blo 2277435 5766349 := bbase (se 3 (by rfl) ⟨1081190, by rfl⟩ : syracuseStep 5766349 = 2162381) (by norm_num)
theorem B7688465 : Blo 2277435 7688465 := bstep (se 2 (by rfl) ⟨2883174, by rfl⟩ : syracuseStep 7688465 = 5766349) B5766349
theorem B5125643 : Blo 2277435 5125643 := bstep (se 1 (by rfl) ⟨3844232, by rfl⟩ : syracuseStep 5125643 = 7688465) B7688465
theorem B3417095 : Blo 2277435 3417095 := bstep (se 1 (by rfl) ⟨2562821, by rfl⟩ : syracuseStep 3417095 = 5125643) B5125643
theorem B2278063 : Blo 2277435 2278063 := bstep (se 1 (by rfl) ⟨1708547, by rfl⟩ : syracuseStep 2278063 = 3417095) B3417095
theorem B3417101 : Blo 2277435 3417101 := bbase (se 3 (by rfl) ⟨640706, by rfl⟩ : syracuseStep 3417101 = 1281413) (by norm_num)
theorem B2278067 : Blo 2277435 2278067 := bstep (se 1 (by rfl) ⟨1708550, by rfl⟩ : syracuseStep 2278067 = 3417101) B3417101
theorem B5125661 : Blo 2277435 5125661 := bbase (se 3 (by rfl) ⟨961061, by rfl⟩ : syracuseStep 5125661 = 1922123) (by norm_num)
theorem B3417107 : Blo 2277435 3417107 := bstep (se 1 (by rfl) ⟨2562830, by rfl⟩ : syracuseStep 3417107 = 5125661) B5125661
theorem B2278071 : Blo 2277435 2278071 := bstep (se 1 (by rfl) ⟨1708553, by rfl⟩ : syracuseStep 2278071 = 3417107) B3417107
theorem B3844253 : Blo 2277435 3844253 := bbase (se 3 (by rfl) ⟨720797, by rfl⟩ : syracuseStep 3844253 = 1441595) (by norm_num)
theorem B2562835 : Blo 2277435 2562835 := bstep (se 1 (by rfl) ⟨1922126, by rfl⟩ : syracuseStep 2562835 = 3844253) B3844253
theorem B3417113 : Blo 2277435 3417113 := bstep (se 2 (by rfl) ⟨1281417, by rfl⟩ : syracuseStep 3417113 = 2562835) B2562835
theorem B2278075 : Blo 2277435 2278075 := bstep (se 1 (by rfl) ⟨1708556, by rfl⟩ : syracuseStep 2278075 = 3417113) B3417113
theorem B3463741 : Blo 2277435 3463741 := bbase (se 3 (by rfl) ⟨649451, by rfl⟩ : syracuseStep 3463741 = 1298903) (by norm_num)
theorem B18473285 : Blo 2277435 18473285 := bstep (se 4 (by rfl) ⟨1731870, by rfl⟩ : syracuseStep 18473285 = 3463741) B3463741
theorem B49262093 : Blo 2277435 49262093 := bstep (se 3 (by rfl) ⟨9236642, by rfl⟩ : syracuseStep 49262093 = 18473285) B18473285
theorem B32841395 : Blo 2277435 32841395 := bstep (se 1 (by rfl) ⟨24631046, by rfl⟩ : syracuseStep 32841395 = 49262093) B49262093
theorem B21894263 : Blo 2277435 21894263 := bstep (se 1 (by rfl) ⟨16420697, by rfl⟩ : syracuseStep 21894263 = 32841395) B32841395
theorem B14596175 : Blo 2277435 14596175 := bstep (se 1 (by rfl) ⟨10947131, by rfl⟩ : syracuseStep 14596175 = 21894263) B21894263
theorem B9730783 : Blo 2277435 9730783 := bstep (se 1 (by rfl) ⟨7298087, by rfl⟩ : syracuseStep 9730783 = 14596175) B14596175
theorem B12974377 : Blo 2277435 12974377 := bstep (se 2 (by rfl) ⟨4865391, by rfl⟩ : syracuseStep 12974377 = 9730783) B9730783
theorem B17299169 : Blo 2277435 17299169 := bstep (se 2 (by rfl) ⟨6487188, by rfl⟩ : syracuseStep 17299169 = 12974377) B12974377
theorem B11532779 : Blo 2277435 11532779 := bstep (se 1 (by rfl) ⟨8649584, by rfl⟩ : syracuseStep 11532779 = 17299169) B17299169
theorem B7688519 : Blo 2277435 7688519 := bstep (se 1 (by rfl) ⟨5766389, by rfl⟩ : syracuseStep 7688519 = 11532779) B11532779
theorem B5125679 : Blo 2277435 5125679 := bstep (se 1 (by rfl) ⟨3844259, by rfl⟩ : syracuseStep 5125679 = 7688519) B7688519
theorem B3417119 : Blo 2277435 3417119 := bstep (se 1 (by rfl) ⟨2562839, by rfl⟩ : syracuseStep 3417119 = 5125679) B5125679
theorem B2278079 : Blo 2277435 2278079 := bstep (se 1 (by rfl) ⟨1708559, by rfl⟩ : syracuseStep 2278079 = 3417119) B3417119
theorem B3417125 : Blo 2277435 3417125 := bbase (se 4 (by rfl) ⟨320355, by rfl⟩ : syracuseStep 3417125 = 640711) (by norm_num)
theorem B2278083 : Blo 2277435 2278083 := bstep (se 1 (by rfl) ⟨1708562, by rfl⟩ : syracuseStep 2278083 = 3417125) B3417125
theorem B2883205 : Blo 2277435 2883205 := bbase (se 4 (by rfl) ⟨270300, by rfl⟩ : syracuseStep 2883205 = 540601) (by norm_num)
theorem B3844273 : Blo 2277435 3844273 := bstep (se 2 (by rfl) ⟨1441602, by rfl⟩ : syracuseStep 3844273 = 2883205) B2883205
theorem B5125697 : Blo 2277435 5125697 := bstep (se 2 (by rfl) ⟨1922136, by rfl⟩ : syracuseStep 5125697 = 3844273) B3844273
theorem B3417131 : Blo 2277435 3417131 := bstep (se 1 (by rfl) ⟨2562848, by rfl⟩ : syracuseStep 3417131 = 5125697) B5125697
theorem B2278087 : Blo 2277435 2278087 := bstep (se 1 (by rfl) ⟨1708565, by rfl⟩ : syracuseStep 2278087 = 3417131) B3417131
theorem B2562853 : Blo 2277435 2562853 := bbase (se 4 (by rfl) ⟨240267, by rfl⟩ : syracuseStep 2562853 = 480535) (by norm_num)
theorem B3417137 : Blo 2277435 3417137 := bstep (se 2 (by rfl) ⟨1281426, by rfl⟩ : syracuseStep 3417137 = 2562853) B2562853
theorem B2278091 : Blo 2277435 2278091 := bstep (se 1 (by rfl) ⟨1708568, by rfl⟩ : syracuseStep 2278091 = 3417137) B3417137
theorem B9730853 : Blo 2277435 9730853 := bbase (se 4 (by rfl) ⟨912267, by rfl⟩ : syracuseStep 9730853 = 1824535) (by norm_num)
theorem B6487235 : Blo 2277435 6487235 := bstep (se 1 (by rfl) ⟨4865426, by rfl⟩ : syracuseStep 6487235 = 9730853) B9730853
theorem B4324823 : Blo 2277435 4324823 := bstep (se 1 (by rfl) ⟨3243617, by rfl⟩ : syracuseStep 4324823 = 6487235) B6487235
theorem B2883215 : Blo 2277435 2883215 := bstep (se 1 (by rfl) ⟨2162411, by rfl⟩ : syracuseStep 2883215 = 4324823) B4324823
theorem B7688573 : Blo 2277435 7688573 := bstep (se 3 (by rfl) ⟨1441607, by rfl⟩ : syracuseStep 7688573 = 2883215) B2883215
theorem B5125715 : Blo 2277435 5125715 := bstep (se 1 (by rfl) ⟨3844286, by rfl⟩ : syracuseStep 5125715 = 7688573) B7688573
theorem B3417143 : Blo 2277435 3417143 := bstep (se 1 (by rfl) ⟨2562857, by rfl⟩ : syracuseStep 3417143 = 5125715) B5125715
theorem B2278095 : Blo 2277435 2278095 := bstep (se 1 (by rfl) ⟨1708571, by rfl⟩ : syracuseStep 2278095 = 3417143) B3417143
theorem B3417149 : Blo 2277435 3417149 := bbase (se 3 (by rfl) ⟨640715, by rfl⟩ : syracuseStep 3417149 = 1281431) (by norm_num)
theorem B2278099 : Blo 2277435 2278099 := bstep (se 1 (by rfl) ⟨1708574, by rfl⟩ : syracuseStep 2278099 = 3417149) B3417149
theorem B5125733 : Blo 2277435 5125733 := bbase (se 4 (by rfl) ⟨480537, by rfl⟩ : syracuseStep 5125733 = 961075) (by norm_num)
theorem B3417155 : Blo 2277435 3417155 := bstep (se 1 (by rfl) ⟨2562866, by rfl⟩ : syracuseStep 3417155 = 5125733) B5125733
theorem B2278103 : Blo 2277435 2278103 := bstep (se 1 (by rfl) ⟨1708577, by rfl⟩ : syracuseStep 2278103 = 3417155) B3417155
theorem B5766461 : Blo 2277435 5766461 := bbase (se 3 (by rfl) ⟨1081211, by rfl⟩ : syracuseStep 5766461 = 2162423) (by norm_num)
theorem B3844307 : Blo 2277435 3844307 := bstep (se 1 (by rfl) ⟨2883230, by rfl⟩ : syracuseStep 3844307 = 5766461) B5766461
theorem B2562871 : Blo 2277435 2562871 := bstep (se 1 (by rfl) ⟨1922153, by rfl⟩ : syracuseStep 2562871 = 3844307) B3844307
theorem B3417161 : Blo 2277435 3417161 := bstep (se 2 (by rfl) ⟨1281435, by rfl⟩ : syracuseStep 3417161 = 2562871) B2562871
theorem B2278107 : Blo 2277435 2278107 := bstep (se 1 (by rfl) ⟨1708580, by rfl⟩ : syracuseStep 2278107 = 3417161) B3417161
theorem B4324853 : Blo 2277435 4324853 := bbase (se 5 (by rfl) ⟨202727, by rfl⟩ : syracuseStep 4324853 = 405455) (by norm_num)
theorem B11532941 : Blo 2277435 11532941 := bstep (se 3 (by rfl) ⟨2162426, by rfl⟩ : syracuseStep 11532941 = 4324853) B4324853
theorem B7688627 : Blo 2277435 7688627 := bstep (se 1 (by rfl) ⟨5766470, by rfl⟩ : syracuseStep 7688627 = 11532941) B11532941
theorem B5125751 : Blo 2277435 5125751 := bstep (se 1 (by rfl) ⟨3844313, by rfl⟩ : syracuseStep 5125751 = 7688627) B7688627
theorem B3417167 : Blo 2277435 3417167 := bstep (se 1 (by rfl) ⟨2562875, by rfl⟩ : syracuseStep 3417167 = 5125751) B5125751
theorem B2278111 : Blo 2277435 2278111 := bstep (se 1 (by rfl) ⟨1708583, by rfl⟩ : syracuseStep 2278111 = 3417167) B3417167
theorem B3417173 : Blo 2277435 3417173 := bbase (se 8 (by rfl) ⟨20022, by rfl⟩ : syracuseStep 3417173 = 40045) (by norm_num)
theorem B2278115 : Blo 2277435 2278115 := bstep (se 1 (by rfl) ⟨1708586, by rfl⟩ : syracuseStep 2278115 = 3417173) B3417173
theorem B5924917 : Blo 2277435 5924917 := bbase (se 5 (by rfl) ⟨277730, by rfl⟩ : syracuseStep 5924917 = 555461) (by norm_num)
theorem B7899889 : Blo 2277435 7899889 := bstep (se 2 (by rfl) ⟨2962458, by rfl⟩ : syracuseStep 7899889 = 5924917) B5924917
theorem B10533185 : Blo 2277435 10533185 := bstep (se 2 (by rfl) ⟨3949944, by rfl⟩ : syracuseStep 10533185 = 7899889) B7899889
theorem B7022123 : Blo 2277435 7022123 := bstep (se 1 (by rfl) ⟨5266592, by rfl⟩ : syracuseStep 7022123 = 10533185) B10533185
theorem B4681415 : Blo 2277435 4681415 := bstep (se 1 (by rfl) ⟨3511061, by rfl⟩ : syracuseStep 4681415 = 7022123) B7022123
theorem B12483773 : Blo 2277435 12483773 := bstep (se 3 (by rfl) ⟨2340707, by rfl⟩ : syracuseStep 12483773 = 4681415) B4681415
theorem B8322515 : Blo 2277435 8322515 := bstep (se 1 (by rfl) ⟨6241886, by rfl⟩ : syracuseStep 8322515 = 12483773) B12483773
theorem B5548343 : Blo 2277435 5548343 := bstep (se 1 (by rfl) ⟨4161257, by rfl⟩ : syracuseStep 5548343 = 8322515) B8322515
theorem B59182325 : Blo 2277435 59182325 := bstep (se 5 (by rfl) ⟨2774171, by rfl⟩ : syracuseStep 59182325 = 5548343) B5548343
theorem B39454883 : Blo 2277435 39454883 := bstep (se 1 (by rfl) ⟨29591162, by rfl⟩ : syracuseStep 39454883 = 59182325) B59182325
theorem B26303255 : Blo 2277435 26303255 := bstep (se 1 (by rfl) ⟨19727441, by rfl⟩ : syracuseStep 26303255 = 39454883) B39454883
theorem B17535503 : Blo 2277435 17535503 := bstep (se 1 (by rfl) ⟨13151627, by rfl⟩ : syracuseStep 17535503 = 26303255) B26303255
theorem B11690335 : Blo 2277435 11690335 := bstep (se 1 (by rfl) ⟨8767751, by rfl⟩ : syracuseStep 11690335 = 17535503) B17535503
theorem B15587113 : Blo 2277435 15587113 := bstep (se 2 (by rfl) ⟨5845167, by rfl⟩ : syracuseStep 15587113 = 11690335) B11690335
theorem B20782817 : Blo 2277435 20782817 := bstep (se 2 (by rfl) ⟨7793556, by rfl⟩ : syracuseStep 20782817 = 15587113) B15587113
theorem B13855211 : Blo 2277435 13855211 := bstep (se 1 (by rfl) ⟨10391408, by rfl⟩ : syracuseStep 13855211 = 20782817) B20782817
theorem B9236807 : Blo 2277435 9236807 := bstep (se 1 (by rfl) ⟨6927605, by rfl⟩ : syracuseStep 9236807 = 13855211) B13855211
theorem B6157871 : Blo 2277435 6157871 := bstep (se 1 (by rfl) ⟨4618403, by rfl⟩ : syracuseStep 6157871 = 9236807) B9236807
theorem B4105247 : Blo 2277435 4105247 := bstep (se 1 (by rfl) ⟨3078935, by rfl⟩ : syracuseStep 4105247 = 6157871) B6157871
theorem B10947325 : Blo 2277435 10947325 := bstep (se 3 (by rfl) ⟨2052623, by rfl⟩ : syracuseStep 10947325 = 4105247) B4105247
theorem B14596433 : Blo 2277435 14596433 := bstep (se 2 (by rfl) ⟨5473662, by rfl⟩ : syracuseStep 14596433 = 10947325) B10947325
theorem B9730955 : Blo 2277435 9730955 := bstep (se 1 (by rfl) ⟨7298216, by rfl⟩ : syracuseStep 9730955 = 14596433) B14596433
theorem B6487303 : Blo 2277435 6487303 := bstep (se 1 (by rfl) ⟨4865477, by rfl⟩ : syracuseStep 6487303 = 9730955) B9730955
theorem B8649737 : Blo 2277435 8649737 := bstep (se 2 (by rfl) ⟨3243651, by rfl⟩ : syracuseStep 8649737 = 6487303) B6487303
theorem B5766491 : Blo 2277435 5766491 := bstep (se 1 (by rfl) ⟨4324868, by rfl⟩ : syracuseStep 5766491 = 8649737) B8649737
theorem B3844327 : Blo 2277435 3844327 := bstep (se 1 (by rfl) ⟨2883245, by rfl⟩ : syracuseStep 3844327 = 5766491) B5766491
theorem B5125769 : Blo 2277435 5125769 := bstep (se 2 (by rfl) ⟨1922163, by rfl⟩ : syracuseStep 5125769 = 3844327) B3844327
theorem B3417179 : Blo 2277435 3417179 := bstep (se 1 (by rfl) ⟨2562884, by rfl⟩ : syracuseStep 3417179 = 5125769) B5125769
theorem B2278119 : Blo 2277435 2278119 := bstep (se 1 (by rfl) ⟨1708589, by rfl⟩ : syracuseStep 2278119 = 3417179) B3417179
theorem B2562889 : Blo 2277435 2562889 := bbase (se 2 (by rfl) ⟨961083, by rfl⟩ : syracuseStep 2562889 = 1922167) (by norm_num)
theorem B3417185 : Blo 2277435 3417185 := bstep (se 2 (by rfl) ⟨1281444, by rfl⟩ : syracuseStep 3417185 = 2562889) B2562889
theorem B2278123 : Blo 2277435 2278123 := bstep (se 1 (by rfl) ⟨1708592, by rfl⟩ : syracuseStep 2278123 = 3417185) B3417185
theorem B4105261 : Blo 2277435 4105261 := bbase (se 3 (by rfl) ⟨769736, by rfl⟩ : syracuseStep 4105261 = 1539473) (by norm_num)
theorem B21894725 : Blo 2277435 21894725 := bstep (se 4 (by rfl) ⟨2052630, by rfl⟩ : syracuseStep 21894725 = 4105261) B4105261
theorem B14596483 : Blo 2277435 14596483 := bstep (se 1 (by rfl) ⟨10947362, by rfl⟩ : syracuseStep 14596483 = 21894725) B21894725
theorem B19461977 : Blo 2277435 19461977 := bstep (se 2 (by rfl) ⟨7298241, by rfl⟩ : syracuseStep 19461977 = 14596483) B14596483
theorem B12974651 : Blo 2277435 12974651 := bstep (se 1 (by rfl) ⟨9730988, by rfl⟩ : syracuseStep 12974651 = 19461977) B19461977
theorem B8649767 : Blo 2277435 8649767 := bstep (se 1 (by rfl) ⟨6487325, by rfl⟩ : syracuseStep 8649767 = 12974651) B12974651
theorem B5766511 : Blo 2277435 5766511 := bstep (se 1 (by rfl) ⟨4324883, by rfl⟩ : syracuseStep 5766511 = 8649767) B8649767
theorem B7688681 : Blo 2277435 7688681 := bstep (se 2 (by rfl) ⟨2883255, by rfl⟩ : syracuseStep 7688681 = 5766511) B5766511
theorem B5125787 : Blo 2277435 5125787 := bstep (se 1 (by rfl) ⟨3844340, by rfl⟩ : syracuseStep 5125787 = 7688681) B7688681
theorem B3417191 : Blo 2277435 3417191 := bstep (se 1 (by rfl) ⟨2562893, by rfl⟩ : syracuseStep 3417191 = 5125787) B5125787
theorem B2278127 : Blo 2277435 2278127 := bstep (se 1 (by rfl) ⟨1708595, by rfl⟩ : syracuseStep 2278127 = 3417191) B3417191
theorem B3417197 : Blo 2277435 3417197 := bbase (se 3 (by rfl) ⟨640724, by rfl⟩ : syracuseStep 3417197 = 1281449) (by norm_num)
theorem B2278131 : Blo 2277435 2278131 := bstep (se 1 (by rfl) ⟨1708598, by rfl⟩ : syracuseStep 2278131 = 3417197) B3417197
theorem B5125805 : Blo 2277435 5125805 := bbase (se 3 (by rfl) ⟨961088, by rfl⟩ : syracuseStep 5125805 = 1922177) (by norm_num)
theorem B3417203 : Blo 2277435 3417203 := bstep (se 1 (by rfl) ⟨2562902, by rfl⟩ : syracuseStep 3417203 = 5125805) B5125805
theorem B2278135 : Blo 2277435 2278135 := bstep (se 1 (by rfl) ⟨1708601, by rfl⟩ : syracuseStep 2278135 = 3417203) B3417203
theorem B3649141 : Blo 2277435 3649141 := bbase (se 5 (by rfl) ⟨171053, by rfl⟩ : syracuseStep 3649141 = 342107) (by norm_num)
theorem B4865521 : Blo 2277435 4865521 := bstep (se 2 (by rfl) ⟨1824570, by rfl⟩ : syracuseStep 4865521 = 3649141) B3649141
theorem B6487361 : Blo 2277435 6487361 := bstep (se 2 (by rfl) ⟨2432760, by rfl⟩ : syracuseStep 6487361 = 4865521) B4865521
theorem B4324907 : Blo 2277435 4324907 := bstep (se 1 (by rfl) ⟨3243680, by rfl⟩ : syracuseStep 4324907 = 6487361) B6487361
theorem B2883271 : Blo 2277435 2883271 := bstep (se 1 (by rfl) ⟨2162453, by rfl⟩ : syracuseStep 2883271 = 4324907) B4324907
theorem B3844361 : Blo 2277435 3844361 := bstep (se 2 (by rfl) ⟨1441635, by rfl⟩ : syracuseStep 3844361 = 2883271) B2883271
theorem B2562907 : Blo 2277435 2562907 := bstep (se 1 (by rfl) ⟨1922180, by rfl⟩ : syracuseStep 2562907 = 3844361) B3844361
theorem B3417209 : Blo 2277435 3417209 := bstep (se 2 (by rfl) ⟨1281453, by rfl⟩ : syracuseStep 3417209 = 2562907) B2562907
theorem B2278139 : Blo 2277435 2278139 := bstep (se 1 (by rfl) ⟨1708604, by rfl⟩ : syracuseStep 2278139 = 3417209) B3417209
theorem B5845229 : Blo 2277435 5845229 := bbase (se 3 (by rfl) ⟨1095980, by rfl⟩ : syracuseStep 5845229 = 2191961) (by norm_num)
theorem B3896819 : Blo 2277435 3896819 := bstep (se 1 (by rfl) ⟨2922614, by rfl⟩ : syracuseStep 3896819 = 5845229) B5845229
theorem B2597879 : Blo 2277435 2597879 := bstep (se 1 (by rfl) ⟨1948409, by rfl⟩ : syracuseStep 2597879 = 3896819) B3896819
theorem B6927677 : Blo 2277435 6927677 := bstep (se 3 (by rfl) ⟨1298939, by rfl⟩ : syracuseStep 6927677 = 2597879) B2597879
theorem B4618451 : Blo 2277435 4618451 := bstep (se 1 (by rfl) ⟨3463838, by rfl⟩ : syracuseStep 4618451 = 6927677) B6927677
theorem B12315869 : Blo 2277435 12315869 := bstep (se 3 (by rfl) ⟨2309225, by rfl⟩ : syracuseStep 12315869 = 4618451) B4618451
theorem B8210579 : Blo 2277435 8210579 := bstep (se 1 (by rfl) ⟨6157934, by rfl⟩ : syracuseStep 8210579 = 12315869) B12315869
theorem B21894877 : Blo 2277435 21894877 := bstep (se 3 (by rfl) ⟨4105289, by rfl⟩ : syracuseStep 21894877 = 8210579) B8210579
theorem B29193169 : Blo 2277435 29193169 := bstep (se 2 (by rfl) ⟨10947438, by rfl⟩ : syracuseStep 29193169 = 21894877) B21894877
theorem B38924225 : Blo 2277435 38924225 := bstep (se 2 (by rfl) ⟨14596584, by rfl⟩ : syracuseStep 38924225 = 29193169) B29193169
theorem B25949483 : Blo 2277435 25949483 := bstep (se 1 (by rfl) ⟨19462112, by rfl⟩ : syracuseStep 25949483 = 38924225) B38924225
theorem B17299655 : Blo 2277435 17299655 := bstep (se 1 (by rfl) ⟨12974741, by rfl⟩ : syracuseStep 17299655 = 25949483) B25949483
theorem B11533103 : Blo 2277435 11533103 := bstep (se 1 (by rfl) ⟨8649827, by rfl⟩ : syracuseStep 11533103 = 17299655) B17299655
theorem B7688735 : Blo 2277435 7688735 := bstep (se 1 (by rfl) ⟨5766551, by rfl⟩ : syracuseStep 7688735 = 11533103) B11533103
theorem B5125823 : Blo 2277435 5125823 := bstep (se 1 (by rfl) ⟨3844367, by rfl⟩ : syracuseStep 5125823 = 7688735) B7688735
theorem B3417215 : Blo 2277435 3417215 := bstep (se 1 (by rfl) ⟨2562911, by rfl⟩ : syracuseStep 3417215 = 5125823) B5125823
theorem B2278143 : Blo 2277435 2278143 := bstep (se 1 (by rfl) ⟨1708607, by rfl⟩ : syracuseStep 2278143 = 3417215) B3417215
theorem B3417221 : Blo 2277435 3417221 := bbase (se 4 (by rfl) ⟨320364, by rfl⟩ : syracuseStep 3417221 = 640729) (by norm_num)
theorem B2278147 : Blo 2277435 2278147 := bstep (se 1 (by rfl) ⟨1708610, by rfl⟩ : syracuseStep 2278147 = 3417221) B3417221
theorem B3844381 : Blo 2277435 3844381 := bbase (se 3 (by rfl) ⟨720821, by rfl⟩ : syracuseStep 3844381 = 1441643) (by norm_num)
theorem B5125841 : Blo 2277435 5125841 := bstep (se 2 (by rfl) ⟨1922190, by rfl⟩ : syracuseStep 5125841 = 3844381) B3844381
theorem B3417227 : Blo 2277435 3417227 := bstep (se 1 (by rfl) ⟨2562920, by rfl⟩ : syracuseStep 3417227 = 5125841) B5125841
theorem B2278151 : Blo 2277435 2278151 := bstep (se 1 (by rfl) ⟨1708613, by rfl⟩ : syracuseStep 2278151 = 3417227) B3417227
theorem B2562925 : Blo 2277435 2562925 := bbase (se 3 (by rfl) ⟨480548, by rfl⟩ : syracuseStep 2562925 = 961097) (by norm_num)
theorem B3417233 : Blo 2277435 3417233 := bstep (se 2 (by rfl) ⟨1281462, by rfl⟩ : syracuseStep 3417233 = 2562925) B2562925
theorem B2278155 : Blo 2277435 2278155 := bstep (se 1 (by rfl) ⟨1708616, by rfl⟩ : syracuseStep 2278155 = 3417233) B3417233
theorem B7688789 : Blo 2277435 7688789 := bbase (se 8 (by rfl) ⟨45051, by rfl⟩ : syracuseStep 7688789 = 90103) (by norm_num)
theorem B5125859 : Blo 2277435 5125859 := bstep (se 1 (by rfl) ⟨3844394, by rfl⟩ : syracuseStep 5125859 = 7688789) B7688789
theorem B3417239 : Blo 2277435 3417239 := bstep (se 1 (by rfl) ⟨2562929, by rfl⟩ : syracuseStep 3417239 = 5125859) B5125859
theorem B2278159 : Blo 2277435 2278159 := bstep (se 1 (by rfl) ⟨1708619, by rfl⟩ : syracuseStep 2278159 = 3417239) B3417239
theorem B3417245 : Blo 2277435 3417245 := bbase (se 3 (by rfl) ⟨640733, by rfl⟩ : syracuseStep 3417245 = 1281467) (by norm_num)
theorem B2278163 : Blo 2277435 2278163 := bstep (se 1 (by rfl) ⟨1708622, by rfl⟩ : syracuseStep 2278163 = 3417245) B3417245
theorem B5125877 : Blo 2277435 5125877 := bbase (se 5 (by rfl) ⟨240275, by rfl⟩ : syracuseStep 5125877 = 480551) (by norm_num)
theorem B3417251 : Blo 2277435 3417251 := bstep (se 1 (by rfl) ⟨2562938, by rfl⟩ : syracuseStep 3417251 = 5125877) B5125877
theorem B2278167 : Blo 2277435 2278167 := bstep (se 1 (by rfl) ⟨1708625, by rfl⟩ : syracuseStep 2278167 = 3417251) B3417251
theorem B5845301 : Blo 2277435 5845301 := bbase (se 5 (by rfl) ⟨273998, by rfl⟩ : syracuseStep 5845301 = 547997) (by norm_num)
theorem B3896867 : Blo 2277435 3896867 := bstep (se 1 (by rfl) ⟨2922650, by rfl⟩ : syracuseStep 3896867 = 5845301) B5845301
theorem B10391645 : Blo 2277435 10391645 := bstep (se 3 (by rfl) ⟨1948433, by rfl⟩ : syracuseStep 10391645 = 3896867) B3896867
theorem B6927763 : Blo 2277435 6927763 := bstep (se 1 (by rfl) ⟨5195822, by rfl⟩ : syracuseStep 6927763 = 10391645) B10391645
theorem B9237017 : Blo 2277435 9237017 := bstep (se 2 (by rfl) ⟨3463881, by rfl⟩ : syracuseStep 9237017 = 6927763) B6927763
theorem B24632045 : Blo 2277435 24632045 := bstep (se 3 (by rfl) ⟨4618508, by rfl⟩ : syracuseStep 24632045 = 9237017) B9237017
theorem B16421363 : Blo 2277435 16421363 := bstep (se 1 (by rfl) ⟨12316022, by rfl⟩ : syracuseStep 16421363 = 24632045) B24632045
theorem B10947575 : Blo 2277435 10947575 := bstep (se 1 (by rfl) ⟨8210681, by rfl⟩ : syracuseStep 10947575 = 16421363) B16421363
theorem B29193533 : Blo 2277435 29193533 := bstep (se 3 (by rfl) ⟨5473787, by rfl⟩ : syracuseStep 29193533 = 10947575) B10947575
theorem B19462355 : Blo 2277435 19462355 := bstep (se 1 (by rfl) ⟨14596766, by rfl⟩ : syracuseStep 19462355 = 29193533) B29193533
theorem B12974903 : Blo 2277435 12974903 := bstep (se 1 (by rfl) ⟨9731177, by rfl⟩ : syracuseStep 12974903 = 19462355) B19462355
theorem B8649935 : Blo 2277435 8649935 := bstep (se 1 (by rfl) ⟨6487451, by rfl⟩ : syracuseStep 8649935 = 12974903) B12974903
theorem B5766623 : Blo 2277435 5766623 := bstep (se 1 (by rfl) ⟨4324967, by rfl⟩ : syracuseStep 5766623 = 8649935) B8649935
theorem B3844415 : Blo 2277435 3844415 := bstep (se 1 (by rfl) ⟨2883311, by rfl⟩ : syracuseStep 3844415 = 5766623) B5766623
theorem B2562943 : Blo 2277435 2562943 := bstep (se 1 (by rfl) ⟨1922207, by rfl⟩ : syracuseStep 2562943 = 3844415) B3844415
theorem B3417257 : Blo 2277435 3417257 := bstep (se 2 (by rfl) ⟨1281471, by rfl⟩ : syracuseStep 3417257 = 2562943) B2562943
theorem B2278171 : Blo 2277435 2278171 := bstep (se 1 (by rfl) ⟨1708628, by rfl⟩ : syracuseStep 2278171 = 3417257) B3417257
theorem B4865597 : Blo 2277435 4865597 := bbase (se 3 (by rfl) ⟨912299, by rfl⟩ : syracuseStep 4865597 = 1824599) (by norm_num)
theorem B3243731 : Blo 2277435 3243731 := bstep (se 1 (by rfl) ⟨2432798, by rfl⟩ : syracuseStep 3243731 = 4865597) B4865597
theorem B8649949 : Blo 2277435 8649949 := bstep (se 3 (by rfl) ⟨1621865, by rfl⟩ : syracuseStep 8649949 = 3243731) B3243731
theorem B11533265 : Blo 2277435 11533265 := bstep (se 2 (by rfl) ⟨4324974, by rfl⟩ : syracuseStep 11533265 = 8649949) B8649949
theorem B7688843 : Blo 2277435 7688843 := bstep (se 1 (by rfl) ⟨5766632, by rfl⟩ : syracuseStep 7688843 = 11533265) B11533265
theorem B5125895 : Blo 2277435 5125895 := bstep (se 1 (by rfl) ⟨3844421, by rfl⟩ : syracuseStep 5125895 = 7688843) B7688843
theorem B3417263 : Blo 2277435 3417263 := bstep (se 1 (by rfl) ⟨2562947, by rfl⟩ : syracuseStep 3417263 = 5125895) B5125895
theorem B2278175 : Blo 2277435 2278175 := bstep (se 1 (by rfl) ⟨1708631, by rfl⟩ : syracuseStep 2278175 = 3417263) B3417263
theorem B3417269 : Blo 2277435 3417269 := bbase (se 5 (by rfl) ⟨160184, by rfl⟩ : syracuseStep 3417269 = 320369) (by norm_num)
theorem B2278179 : Blo 2277435 2278179 := bstep (se 1 (by rfl) ⟨1708634, by rfl⟩ : syracuseStep 2278179 = 3417269) B3417269
theorem B5766653 : Blo 2277435 5766653 := bbase (se 3 (by rfl) ⟨1081247, by rfl⟩ : syracuseStep 5766653 = 2162495) (by norm_num)
theorem B3844435 : Blo 2277435 3844435 := bstep (se 1 (by rfl) ⟨2883326, by rfl⟩ : syracuseStep 3844435 = 5766653) B5766653
theorem B5125913 : Blo 2277435 5125913 := bstep (se 2 (by rfl) ⟨1922217, by rfl⟩ : syracuseStep 5125913 = 3844435) B3844435
theorem B3417275 : Blo 2277435 3417275 := bstep (se 1 (by rfl) ⟨2562956, by rfl⟩ : syracuseStep 3417275 = 5125913) B5125913
theorem B2278183 : Blo 2277435 2278183 := bstep (se 1 (by rfl) ⟨1708637, by rfl⟩ : syracuseStep 2278183 = 3417275) B3417275
theorem B2562961 : Blo 2277435 2562961 := bbase (se 2 (by rfl) ⟨961110, by rfl⟩ : syracuseStep 2562961 = 1922221) (by norm_num)
theorem B3417281 : Blo 2277435 3417281 := bstep (se 2 (by rfl) ⟨1281480, by rfl⟩ : syracuseStep 3417281 = 2562961) B2562961
theorem B2278187 : Blo 2277435 2278187 := bstep (se 1 (by rfl) ⟨1708640, by rfl⟩ : syracuseStep 2278187 = 3417281) B3417281
theorem B4325005 : Blo 2277435 4325005 := bbase (se 3 (by rfl) ⟨810938, by rfl⟩ : syracuseStep 4325005 = 1621877) (by norm_num)
theorem B5766673 : Blo 2277435 5766673 := bstep (se 2 (by rfl) ⟨2162502, by rfl⟩ : syracuseStep 5766673 = 4325005) B4325005
theorem B7688897 : Blo 2277435 7688897 := bstep (se 2 (by rfl) ⟨2883336, by rfl⟩ : syracuseStep 7688897 = 5766673) B5766673
theorem B5125931 : Blo 2277435 5125931 := bstep (se 1 (by rfl) ⟨3844448, by rfl⟩ : syracuseStep 5125931 = 7688897) B7688897
theorem B3417287 : Blo 2277435 3417287 := bstep (se 1 (by rfl) ⟨2562965, by rfl⟩ : syracuseStep 3417287 = 5125931) B5125931
theorem B2278191 : Blo 2277435 2278191 := bstep (se 1 (by rfl) ⟨1708643, by rfl⟩ : syracuseStep 2278191 = 3417287) B3417287
theorem B3417293 : Blo 2277435 3417293 := bbase (se 3 (by rfl) ⟨640742, by rfl⟩ : syracuseStep 3417293 = 1281485) (by norm_num)
theorem B2278195 : Blo 2277435 2278195 := bstep (se 1 (by rfl) ⟨1708646, by rfl⟩ : syracuseStep 2278195 = 3417293) B3417293
theorem B5125949 : Blo 2277435 5125949 := bbase (se 3 (by rfl) ⟨961115, by rfl⟩ : syracuseStep 5125949 = 1922231) (by norm_num)
theorem B3417299 : Blo 2277435 3417299 := bstep (se 1 (by rfl) ⟨2562974, by rfl⟩ : syracuseStep 3417299 = 5125949) B5125949
theorem B2278199 : Blo 2277435 2278199 := bstep (se 1 (by rfl) ⟨1708649, by rfl⟩ : syracuseStep 2278199 = 3417299) B3417299
theorem B3844469 : Blo 2277435 3844469 := bbase (se 5 (by rfl) ⟨180209, by rfl⟩ : syracuseStep 3844469 = 360419) (by norm_num)
theorem B2562979 : Blo 2277435 2562979 := bstep (se 1 (by rfl) ⟨1922234, by rfl⟩ : syracuseStep 2562979 = 3844469) B3844469
theorem B3417305 : Blo 2277435 3417305 := bstep (se 2 (by rfl) ⟨1281489, by rfl⟩ : syracuseStep 3417305 = 2562979) B2562979
theorem B2278203 : Blo 2277435 2278203 := bstep (se 1 (by rfl) ⟨1708652, by rfl⟩ : syracuseStep 2278203 = 3417305) B3417305
theorem B2736937 : Blo 2277435 2736937 := bbase (se 2 (by rfl) ⟨1026351, by rfl⟩ : syracuseStep 2736937 = 2052703) (by norm_num)
theorem B3649249 : Blo 2277435 3649249 := bstep (se 2 (by rfl) ⟨1368468, by rfl⟩ : syracuseStep 3649249 = 2736937) B2736937
theorem B4865665 : Blo 2277435 4865665 := bstep (se 2 (by rfl) ⟨1824624, by rfl⟩ : syracuseStep 4865665 = 3649249) B3649249
theorem B6487553 : Blo 2277435 6487553 := bstep (se 2 (by rfl) ⟨2432832, by rfl⟩ : syracuseStep 6487553 = 4865665) B4865665
theorem B17300141 : Blo 2277435 17300141 := bstep (se 3 (by rfl) ⟨3243776, by rfl⟩ : syracuseStep 17300141 = 6487553) B6487553
theorem B11533427 : Blo 2277435 11533427 := bstep (se 1 (by rfl) ⟨8650070, by rfl⟩ : syracuseStep 11533427 = 17300141) B17300141
theorem B7688951 : Blo 2277435 7688951 := bstep (se 1 (by rfl) ⟨5766713, by rfl⟩ : syracuseStep 7688951 = 11533427) B11533427
theorem B5125967 : Blo 2277435 5125967 := bstep (se 1 (by rfl) ⟨3844475, by rfl⟩ : syracuseStep 5125967 = 7688951) B7688951
theorem B3417311 : Blo 2277435 3417311 := bstep (se 1 (by rfl) ⟨2562983, by rfl⟩ : syracuseStep 3417311 = 5125967) B5125967
theorem B2278207 : Blo 2277435 2278207 := bstep (se 1 (by rfl) ⟨1708655, by rfl⟩ : syracuseStep 2278207 = 3417311) B3417311
theorem B3417317 : Blo 2277435 3417317 := bbase (se 4 (by rfl) ⟨320373, by rfl⟩ : syracuseStep 3417317 = 640747) (by norm_num)
theorem B2278211 : Blo 2277435 2278211 := bstep (se 1 (by rfl) ⟨1708658, by rfl⟩ : syracuseStep 2278211 = 3417317) B3417317
theorem B4105421 : Blo 2277435 4105421 := bbase (se 3 (by rfl) ⟨769766, by rfl⟩ : syracuseStep 4105421 = 1539533) (by norm_num)
theorem B2736947 : Blo 2277435 2736947 := bstep (se 1 (by rfl) ⟨2052710, by rfl⟩ : syracuseStep 2736947 = 4105421) B4105421
theorem B7298525 : Blo 2277435 7298525 := bstep (se 3 (by rfl) ⟨1368473, by rfl⟩ : syracuseStep 7298525 = 2736947) B2736947
theorem B4865683 : Blo 2277435 4865683 := bstep (se 1 (by rfl) ⟨3649262, by rfl⟩ : syracuseStep 4865683 = 7298525) B7298525
theorem B6487577 : Blo 2277435 6487577 := bstep (se 2 (by rfl) ⟨2432841, by rfl⟩ : syracuseStep 6487577 = 4865683) B4865683
theorem B4325051 : Blo 2277435 4325051 := bstep (se 1 (by rfl) ⟨3243788, by rfl⟩ : syracuseStep 4325051 = 6487577) B6487577
theorem B2883367 : Blo 2277435 2883367 := bstep (se 1 (by rfl) ⟨2162525, by rfl⟩ : syracuseStep 2883367 = 4325051) B4325051
theorem B3844489 : Blo 2277435 3844489 := bstep (se 2 (by rfl) ⟨1441683, by rfl⟩ : syracuseStep 3844489 = 2883367) B2883367
theorem B5125985 : Blo 2277435 5125985 := bstep (se 2 (by rfl) ⟨1922244, by rfl⟩ : syracuseStep 5125985 = 3844489) B3844489
theorem B3417323 : Blo 2277435 3417323 := bstep (se 1 (by rfl) ⟨2562992, by rfl⟩ : syracuseStep 3417323 = 5125985) B5125985
theorem B2278215 : Blo 2277435 2278215 := bstep (se 1 (by rfl) ⟨1708661, by rfl⟩ : syracuseStep 2278215 = 3417323) B3417323
theorem B2562997 : Blo 2277435 2562997 := bbase (se 5 (by rfl) ⟨120140, by rfl⟩ : syracuseStep 2562997 = 240281) (by norm_num)
theorem B3417329 : Blo 2277435 3417329 := bstep (se 2 (by rfl) ⟨1281498, by rfl⟩ : syracuseStep 3417329 = 2562997) B2562997
theorem B2278219 : Blo 2277435 2278219 := bstep (se 1 (by rfl) ⟨1708664, by rfl⟩ : syracuseStep 2278219 = 3417329) B3417329
theorem B2883377 : Blo 2277435 2883377 := bbase (se 2 (by rfl) ⟨1081266, by rfl⟩ : syracuseStep 2883377 = 2162533) (by norm_num)
theorem B7689005 : Blo 2277435 7689005 := bstep (se 3 (by rfl) ⟨1441688, by rfl⟩ : syracuseStep 7689005 = 2883377) B2883377
theorem B5126003 : Blo 2277435 5126003 := bstep (se 1 (by rfl) ⟨3844502, by rfl⟩ : syracuseStep 5126003 = 7689005) B7689005
theorem B3417335 : Blo 2277435 3417335 := bstep (se 1 (by rfl) ⟨2563001, by rfl⟩ : syracuseStep 3417335 = 5126003) B5126003
theorem B2278223 : Blo 2277435 2278223 := bstep (se 1 (by rfl) ⟨1708667, by rfl⟩ : syracuseStep 2278223 = 3417335) B3417335
theorem B3417341 : Blo 2277435 3417341 := bbase (se 3 (by rfl) ⟨640751, by rfl⟩ : syracuseStep 3417341 = 1281503) (by norm_num)
theorem B2278227 : Blo 2277435 2278227 := bstep (se 1 (by rfl) ⟨1708670, by rfl⟩ : syracuseStep 2278227 = 3417341) B3417341
theorem B5126021 : Blo 2277435 5126021 := bbase (se 4 (by rfl) ⟨480564, by rfl⟩ : syracuseStep 5126021 = 961129) (by norm_num)
theorem B3417347 : Blo 2277435 3417347 := bstep (se 1 (by rfl) ⟨2563010, by rfl⟩ : syracuseStep 3417347 = 5126021) B5126021
theorem B2278231 : Blo 2277435 2278231 := bstep (se 1 (by rfl) ⟨1708673, by rfl⟩ : syracuseStep 2278231 = 3417347) B3417347
theorem B12316373 : Blo 2277435 12316373 := bbase (se 7 (by rfl) ⟨144332, by rfl⟩ : syracuseStep 12316373 = 288665) (by norm_num)
theorem B8210915 : Blo 2277435 8210915 := bstep (se 1 (by rfl) ⟨6158186, by rfl⟩ : syracuseStep 8210915 = 12316373) B12316373
theorem B5473943 : Blo 2277435 5473943 := bstep (se 1 (by rfl) ⟨4105457, by rfl⟩ : syracuseStep 5473943 = 8210915) B8210915
theorem B3649295 : Blo 2277435 3649295 := bstep (se 1 (by rfl) ⟨2736971, by rfl⟩ : syracuseStep 3649295 = 5473943) B5473943
theorem B2432863 : Blo 2277435 2432863 := bstep (se 1 (by rfl) ⟨1824647, by rfl⟩ : syracuseStep 2432863 = 3649295) B3649295
theorem B3243817 : Blo 2277435 3243817 := bstep (se 2 (by rfl) ⟨1216431, by rfl⟩ : syracuseStep 3243817 = 2432863) B2432863
theorem B4325089 : Blo 2277435 4325089 := bstep (se 2 (by rfl) ⟨1621908, by rfl⟩ : syracuseStep 4325089 = 3243817) B3243817
theorem B5766785 : Blo 2277435 5766785 := bstep (se 2 (by rfl) ⟨2162544, by rfl⟩ : syracuseStep 5766785 = 4325089) B4325089
theorem B3844523 : Blo 2277435 3844523 := bstep (se 1 (by rfl) ⟨2883392, by rfl⟩ : syracuseStep 3844523 = 5766785) B5766785
theorem B2563015 : Blo 2277435 2563015 := bstep (se 1 (by rfl) ⟨1922261, by rfl⟩ : syracuseStep 2563015 = 3844523) B3844523
theorem B3417353 : Blo 2277435 3417353 := bstep (se 2 (by rfl) ⟨1281507, by rfl⟩ : syracuseStep 3417353 = 2563015) B2563015
theorem B2278235 : Blo 2277435 2278235 := bstep (se 1 (by rfl) ⟨1708676, by rfl⟩ : syracuseStep 2278235 = 3417353) B3417353
theorem B11533589 : Blo 2277435 11533589 := bbase (se 6 (by rfl) ⟨270318, by rfl⟩ : syracuseStep 11533589 = 540637) (by norm_num)
theorem B7689059 : Blo 2277435 7689059 := bstep (se 1 (by rfl) ⟨5766794, by rfl⟩ : syracuseStep 7689059 = 11533589) B11533589
theorem B5126039 : Blo 2277435 5126039 := bstep (se 1 (by rfl) ⟨3844529, by rfl⟩ : syracuseStep 5126039 = 7689059) B7689059
theorem B3417359 : Blo 2277435 3417359 := bstep (se 1 (by rfl) ⟨2563019, by rfl⟩ : syracuseStep 3417359 = 5126039) B5126039
theorem B2278239 : Blo 2277435 2278239 := bstep (se 1 (by rfl) ⟨1708679, by rfl⟩ : syracuseStep 2278239 = 3417359) B3417359
theorem B3417365 : Blo 2277435 3417365 := bbase (se 6 (by rfl) ⟨80094, by rfl⟩ : syracuseStep 3417365 = 160189) (by norm_num)
theorem B2278243 : Blo 2277435 2278243 := bstep (se 1 (by rfl) ⟨1708682, by rfl⟩ : syracuseStep 2278243 = 3417365) B3417365
theorem B3749573 : Blo 2277435 3749573 := bbase (se 4 (by rfl) ⟨351522, by rfl⟩ : syracuseStep 3749573 = 703045) (by norm_num)
theorem B2499715 : Blo 2277435 2499715 := bstep (se 1 (by rfl) ⟨1874786, by rfl⟩ : syracuseStep 2499715 = 3749573) B3749573
theorem B3332953 : Blo 2277435 3332953 := bstep (se 2 (by rfl) ⟨1249857, by rfl⟩ : syracuseStep 3332953 = 2499715) B2499715
theorem B17775749 : Blo 2277435 17775749 := bstep (se 4 (by rfl) ⟨1666476, by rfl⟩ : syracuseStep 17775749 = 3332953) B3332953
theorem B11850499 : Blo 2277435 11850499 := bstep (se 1 (by rfl) ⟨8887874, by rfl⟩ : syracuseStep 11850499 = 17775749) B17775749
theorem B15800665 : Blo 2277435 15800665 := bstep (se 2 (by rfl) ⟨5925249, by rfl⟩ : syracuseStep 15800665 = 11850499) B11850499
theorem B21067553 : Blo 2277435 21067553 := bstep (se 2 (by rfl) ⟨7900332, by rfl⟩ : syracuseStep 21067553 = 15800665) B15800665
theorem B14045035 : Blo 2277435 14045035 := bstep (se 1 (by rfl) ⟨10533776, by rfl⟩ : syracuseStep 14045035 = 21067553) B21067553
theorem B18726713 : Blo 2277435 18726713 := bstep (se 2 (by rfl) ⟨7022517, by rfl⟩ : syracuseStep 18726713 = 14045035) B14045035
theorem B12484475 : Blo 2277435 12484475 := bstep (se 1 (by rfl) ⟨9363356, by rfl⟩ : syracuseStep 12484475 = 18726713) B18726713
theorem B8322983 : Blo 2277435 8322983 := bstep (se 1 (by rfl) ⟨6242237, by rfl⟩ : syracuseStep 8322983 = 12484475) B12484475
theorem B5548655 : Blo 2277435 5548655 := bstep (se 1 (by rfl) ⟨4161491, by rfl⟩ : syracuseStep 5548655 = 8322983) B8322983
theorem B3699103 : Blo 2277435 3699103 := bstep (se 1 (by rfl) ⟨2774327, by rfl⟩ : syracuseStep 3699103 = 5548655) B5548655
theorem B4932137 : Blo 2277435 4932137 := bstep (se 2 (by rfl) ⟨1849551, by rfl⟩ : syracuseStep 4932137 = 3699103) B3699103
theorem B13152365 : Blo 2277435 13152365 := bstep (se 3 (by rfl) ⟨2466068, by rfl⟩ : syracuseStep 13152365 = 4932137) B4932137
theorem B8768243 : Blo 2277435 8768243 := bstep (se 1 (by rfl) ⟨6576182, by rfl⟩ : syracuseStep 8768243 = 13152365) B13152365
theorem B5845495 : Blo 2277435 5845495 := bstep (se 1 (by rfl) ⟨4384121, by rfl⟩ : syracuseStep 5845495 = 8768243) B8768243
theorem B7793993 : Blo 2277435 7793993 := bstep (se 2 (by rfl) ⟨2922747, by rfl⟩ : syracuseStep 7793993 = 5845495) B5845495
theorem B5195995 : Blo 2277435 5195995 := bstep (se 1 (by rfl) ⟨3896996, by rfl⟩ : syracuseStep 5195995 = 7793993) B7793993
theorem B27711973 : Blo 2277435 27711973 := bstep (se 4 (by rfl) ⟨2597997, by rfl⟩ : syracuseStep 27711973 = 5195995) B5195995
theorem B36949297 : Blo 2277435 36949297 := bstep (se 2 (by rfl) ⟨13855986, by rfl⟩ : syracuseStep 36949297 = 27711973) B27711973
theorem B49265729 : Blo 2277435 49265729 := bstep (se 2 (by rfl) ⟨18474648, by rfl⟩ : syracuseStep 49265729 = 36949297) B36949297
theorem B32843819 : Blo 2277435 32843819 := bstep (se 1 (by rfl) ⟨24632864, by rfl⟩ : syracuseStep 32843819 = 49265729) B49265729
theorem B21895879 : Blo 2277435 21895879 := bstep (se 1 (by rfl) ⟨16421909, by rfl⟩ : syracuseStep 21895879 = 32843819) B32843819
theorem B29194505 : Blo 2277435 29194505 := bstep (se 2 (by rfl) ⟨10947939, by rfl⟩ : syracuseStep 29194505 = 21895879) B21895879
theorem B19463003 : Blo 2277435 19463003 := bstep (se 1 (by rfl) ⟨14597252, by rfl⟩ : syracuseStep 19463003 = 29194505) B29194505
theorem B12975335 : Blo 2277435 12975335 := bstep (se 1 (by rfl) ⟨9731501, by rfl⟩ : syracuseStep 12975335 = 19463003) B19463003
theorem B8650223 : Blo 2277435 8650223 := bstep (se 1 (by rfl) ⟨6487667, by rfl⟩ : syracuseStep 8650223 = 12975335) B12975335
theorem B5766815 : Blo 2277435 5766815 := bstep (se 1 (by rfl) ⟨4325111, by rfl⟩ : syracuseStep 5766815 = 8650223) B8650223
theorem B3844543 : Blo 2277435 3844543 := bstep (se 1 (by rfl) ⟨2883407, by rfl⟩ : syracuseStep 3844543 = 5766815) B5766815
theorem B5126057 : Blo 2277435 5126057 := bstep (se 2 (by rfl) ⟨1922271, by rfl⟩ : syracuseStep 5126057 = 3844543) B3844543
theorem B3417371 : Blo 2277435 3417371 := bstep (se 1 (by rfl) ⟨2563028, by rfl⟩ : syracuseStep 3417371 = 5126057) B5126057
theorem B2278247 : Blo 2277435 2278247 := bstep (se 1 (by rfl) ⟨1708685, by rfl⟩ : syracuseStep 2278247 = 3417371) B3417371
theorem B2563033 : Blo 2277435 2563033 := bbase (se 2 (by rfl) ⟨961137, by rfl⟩ : syracuseStep 2563033 = 1922275) (by norm_num)
theorem B3417377 : Blo 2277435 3417377 := bstep (se 2 (by rfl) ⟨1281516, by rfl⟩ : syracuseStep 3417377 = 2563033) B2563033
theorem B2278251 : Blo 2277435 2278251 := bstep (se 1 (by rfl) ⟨1708688, by rfl⟩ : syracuseStep 2278251 = 3417377) B3417377
theorem B3243845 : Blo 2277435 3243845 := bbase (se 4 (by rfl) ⟨304110, by rfl⟩ : syracuseStep 3243845 = 608221) (by norm_num)
theorem B8650253 : Blo 2277435 8650253 := bstep (se 3 (by rfl) ⟨1621922, by rfl⟩ : syracuseStep 8650253 = 3243845) B3243845
theorem B5766835 : Blo 2277435 5766835 := bstep (se 1 (by rfl) ⟨4325126, by rfl⟩ : syracuseStep 5766835 = 8650253) B8650253
theorem B7689113 : Blo 2277435 7689113 := bstep (se 2 (by rfl) ⟨2883417, by rfl⟩ : syracuseStep 7689113 = 5766835) B5766835
theorem B5126075 : Blo 2277435 5126075 := bstep (se 1 (by rfl) ⟨3844556, by rfl⟩ : syracuseStep 5126075 = 7689113) B7689113
theorem B3417383 : Blo 2277435 3417383 := bstep (se 1 (by rfl) ⟨2563037, by rfl⟩ : syracuseStep 3417383 = 5126075) B5126075
theorem B2278255 : Blo 2277435 2278255 := bstep (se 1 (by rfl) ⟨1708691, by rfl⟩ : syracuseStep 2278255 = 3417383) B3417383
theorem B3417389 : Blo 2277435 3417389 := bbase (se 3 (by rfl) ⟨640760, by rfl⟩ : syracuseStep 3417389 = 1281521) (by norm_num)
theorem B2278259 : Blo 2277435 2278259 := bstep (se 1 (by rfl) ⟨1708694, by rfl⟩ : syracuseStep 2278259 = 3417389) B3417389
theorem B5126093 : Blo 2277435 5126093 := bbase (se 3 (by rfl) ⟨961142, by rfl⟩ : syracuseStep 5126093 = 1922285) (by norm_num)
theorem B3417395 : Blo 2277435 3417395 := bstep (se 1 (by rfl) ⟨2563046, by rfl⟩ : syracuseStep 3417395 = 5126093) B5126093
theorem B2278263 : Blo 2277435 2278263 := bstep (se 1 (by rfl) ⟨1708697, by rfl⟩ : syracuseStep 2278263 = 3417395) B3417395
theorem B2883433 : Blo 2277435 2883433 := bbase (se 2 (by rfl) ⟨1081287, by rfl⟩ : syracuseStep 2883433 = 2162575) (by norm_num)
theorem B3844577 : Blo 2277435 3844577 := bstep (se 2 (by rfl) ⟨1441716, by rfl⟩ : syracuseStep 3844577 = 2883433) B2883433
theorem B2563051 : Blo 2277435 2563051 := bstep (se 1 (by rfl) ⟨1922288, by rfl⟩ : syracuseStep 2563051 = 3844577) B3844577
theorem B3417401 : Blo 2277435 3417401 := bstep (se 2 (by rfl) ⟨1281525, by rfl⟩ : syracuseStep 3417401 = 2563051) B2563051
theorem B2278267 : Blo 2277435 2278267 := bstep (se 1 (by rfl) ⟨1708700, by rfl⟩ : syracuseStep 2278267 = 3417401) B3417401
theorem B10392101 : Blo 2277435 10392101 := bbase (se 4 (by rfl) ⟨974259, by rfl⟩ : syracuseStep 10392101 = 1948519) (by norm_num)
theorem B6928067 : Blo 2277435 6928067 := bstep (se 1 (by rfl) ⟨5196050, by rfl⟩ : syracuseStep 6928067 = 10392101) B10392101
theorem B4618711 : Blo 2277435 4618711 := bstep (se 1 (by rfl) ⟨3464033, by rfl⟩ : syracuseStep 4618711 = 6928067) B6928067
theorem B6158281 : Blo 2277435 6158281 := bstep (se 2 (by rfl) ⟨2309355, by rfl⟩ : syracuseStep 6158281 = 4618711) B4618711
theorem B8211041 : Blo 2277435 8211041 := bstep (se 2 (by rfl) ⟨3079140, by rfl⟩ : syracuseStep 8211041 = 6158281) B6158281
theorem B5474027 : Blo 2277435 5474027 := bstep (se 1 (by rfl) ⟨4105520, by rfl⟩ : syracuseStep 5474027 = 8211041) B8211041
theorem B14597405 : Blo 2277435 14597405 := bstep (se 3 (by rfl) ⟨2737013, by rfl⟩ : syracuseStep 14597405 = 5474027) B5474027
theorem B9731603 : Blo 2277435 9731603 := bstep (se 1 (by rfl) ⟨7298702, by rfl⟩ : syracuseStep 9731603 = 14597405) B14597405
theorem B25950941 : Blo 2277435 25950941 := bstep (se 3 (by rfl) ⟨4865801, by rfl⟩ : syracuseStep 25950941 = 9731603) B9731603
theorem B17300627 : Blo 2277435 17300627 := bstep (se 1 (by rfl) ⟨12975470, by rfl⟩ : syracuseStep 17300627 = 25950941) B25950941
theorem B11533751 : Blo 2277435 11533751 := bstep (se 1 (by rfl) ⟨8650313, by rfl⟩ : syracuseStep 11533751 = 17300627) B17300627
theorem B7689167 : Blo 2277435 7689167 := bstep (se 1 (by rfl) ⟨5766875, by rfl⟩ : syracuseStep 7689167 = 11533751) B11533751
theorem B5126111 : Blo 2277435 5126111 := bstep (se 1 (by rfl) ⟨3844583, by rfl⟩ : syracuseStep 5126111 = 7689167) B7689167
theorem B3417407 : Blo 2277435 3417407 := bstep (se 1 (by rfl) ⟨2563055, by rfl⟩ : syracuseStep 3417407 = 5126111) B5126111
theorem B2278271 : Blo 2277435 2278271 := bstep (se 1 (by rfl) ⟨1708703, by rfl⟩ : syracuseStep 2278271 = 3417407) B3417407
theorem B3417413 : Blo 2277435 3417413 := bbase (se 4 (by rfl) ⟨320382, by rfl⟩ : syracuseStep 3417413 = 640765) (by norm_num)
theorem B2278275 : Blo 2277435 2278275 := bstep (se 1 (by rfl) ⟨1708706, by rfl⟩ : syracuseStep 2278275 = 3417413) B3417413
theorem B3844597 : Blo 2277435 3844597 := bbase (se 5 (by rfl) ⟨180215, by rfl⟩ : syracuseStep 3844597 = 360431) (by norm_num)
theorem B5126129 : Blo 2277435 5126129 := bstep (se 2 (by rfl) ⟨1922298, by rfl⟩ : syracuseStep 5126129 = 3844597) B3844597
theorem B3417419 : Blo 2277435 3417419 := bstep (se 1 (by rfl) ⟨2563064, by rfl⟩ : syracuseStep 3417419 = 5126129) B5126129
theorem B2278279 : Blo 2277435 2278279 := bstep (se 1 (by rfl) ⟨1708709, by rfl⟩ : syracuseStep 2278279 = 3417419) B3417419
theorem B2563069 : Blo 2277435 2563069 := bbase (se 3 (by rfl) ⟨480575, by rfl⟩ : syracuseStep 2563069 = 961151) (by norm_num)
theorem B3417425 : Blo 2277435 3417425 := bstep (se 2 (by rfl) ⟨1281534, by rfl⟩ : syracuseStep 3417425 = 2563069) B2563069
theorem B2278283 : Blo 2277435 2278283 := bstep (se 1 (by rfl) ⟨1708712, by rfl⟩ : syracuseStep 2278283 = 3417425) B3417425
theorem B7689221 : Blo 2277435 7689221 := bbase (se 4 (by rfl) ⟨720864, by rfl⟩ : syracuseStep 7689221 = 1441729) (by norm_num)
theorem B5126147 : Blo 2277435 5126147 := bstep (se 1 (by rfl) ⟨3844610, by rfl⟩ : syracuseStep 5126147 = 7689221) B7689221
theorem B3417431 : Blo 2277435 3417431 := bstep (se 1 (by rfl) ⟨2563073, by rfl⟩ : syracuseStep 3417431 = 5126147) B5126147
theorem B2278287 : Blo 2277435 2278287 := bstep (se 1 (by rfl) ⟨1708715, by rfl⟩ : syracuseStep 2278287 = 3417431) B3417431
theorem B3417437 : Blo 2277435 3417437 := bbase (se 3 (by rfl) ⟨640769, by rfl⟩ : syracuseStep 3417437 = 1281539) (by norm_num)
theorem B2278291 : Blo 2277435 2278291 := bstep (se 1 (by rfl) ⟨1708718, by rfl⟩ : syracuseStep 2278291 = 3417437) B3417437
theorem B5126165 : Blo 2277435 5126165 := bbase (se 6 (by rfl) ⟨120144, by rfl⟩ : syracuseStep 5126165 = 240289) (by norm_num)
theorem B3417443 : Blo 2277435 3417443 := bstep (se 1 (by rfl) ⟨2563082, by rfl⟩ : syracuseStep 3417443 = 5126165) B5126165
theorem B2278295 : Blo 2277435 2278295 := bstep (se 1 (by rfl) ⟨1708721, by rfl⟩ : syracuseStep 2278295 = 3417443) B3417443
theorem B8650421 : Blo 2277435 8650421 := bbase (se 5 (by rfl) ⟨405488, by rfl⟩ : syracuseStep 8650421 = 810977) (by norm_num)
theorem B5766947 : Blo 2277435 5766947 := bstep (se 1 (by rfl) ⟨4325210, by rfl⟩ : syracuseStep 5766947 = 8650421) B8650421
theorem B3844631 : Blo 2277435 3844631 := bstep (se 1 (by rfl) ⟨2883473, by rfl⟩ : syracuseStep 3844631 = 5766947) B5766947
theorem B2563087 : Blo 2277435 2563087 := bstep (se 1 (by rfl) ⟨1922315, by rfl⟩ : syracuseStep 2563087 = 3844631) B3844631
theorem B3417449 : Blo 2277435 3417449 := bstep (se 2 (by rfl) ⟨1281543, by rfl⟩ : syracuseStep 3417449 = 2563087) B2563087
theorem B2278299 : Blo 2277435 2278299 := bstep (se 1 (by rfl) ⟨1708724, by rfl⟩ : syracuseStep 2278299 = 3417449) B3417449
theorem B5196125 : Blo 2277435 5196125 := bbase (se 3 (by rfl) ⟨974273, by rfl⟩ : syracuseStep 5196125 = 1948547) (by norm_num)
theorem B3464083 : Blo 2277435 3464083 := bstep (se 1 (by rfl) ⟨2598062, by rfl⟩ : syracuseStep 3464083 = 5196125) B5196125
theorem B4618777 : Blo 2277435 4618777 := bstep (se 2 (by rfl) ⟨1732041, by rfl⟩ : syracuseStep 4618777 = 3464083) B3464083
theorem B6158369 : Blo 2277435 6158369 := bstep (se 2 (by rfl) ⟨2309388, by rfl⟩ : syracuseStep 6158369 = 4618777) B4618777
theorem B4105579 : Blo 2277435 4105579 := bstep (se 1 (by rfl) ⟨3079184, by rfl⟩ : syracuseStep 4105579 = 6158369) B6158369
theorem B5474105 : Blo 2277435 5474105 := bstep (se 2 (by rfl) ⟨2052789, by rfl⟩ : syracuseStep 5474105 = 4105579) B4105579
theorem B3649403 : Blo 2277435 3649403 := bstep (se 1 (by rfl) ⟨2737052, by rfl⟩ : syracuseStep 3649403 = 5474105) B5474105
theorem B2432935 : Blo 2277435 2432935 := bstep (se 1 (by rfl) ⟨1824701, by rfl⟩ : syracuseStep 2432935 = 3649403) B3649403
theorem B12975653 : Blo 2277435 12975653 := bstep (se 4 (by rfl) ⟨1216467, by rfl⟩ : syracuseStep 12975653 = 2432935) B2432935
theorem B8650435 : Blo 2277435 8650435 := bstep (se 1 (by rfl) ⟨6487826, by rfl⟩ : syracuseStep 8650435 = 12975653) B12975653
theorem B11533913 : Blo 2277435 11533913 := bstep (se 2 (by rfl) ⟨4325217, by rfl⟩ : syracuseStep 11533913 = 8650435) B8650435
theorem B7689275 : Blo 2277435 7689275 := bstep (se 1 (by rfl) ⟨5766956, by rfl⟩ : syracuseStep 7689275 = 11533913) B11533913
theorem B5126183 : Blo 2277435 5126183 := bstep (se 1 (by rfl) ⟨3844637, by rfl⟩ : syracuseStep 5126183 = 7689275) B7689275
theorem B3417455 : Blo 2277435 3417455 := bstep (se 1 (by rfl) ⟨2563091, by rfl⟩ : syracuseStep 3417455 = 5126183) B5126183
theorem B2278303 : Blo 2277435 2278303 := bstep (se 1 (by rfl) ⟨1708727, by rfl⟩ : syracuseStep 2278303 = 3417455) B3417455
theorem B3417461 : Blo 2277435 3417461 := bbase (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) (by norm_num)
theorem B2278307 : Blo 2277435 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B3243925 : Blo 2277435 3243925 := bbase (se 6 (by rfl) ⟨76029, by rfl⟩ : syracuseStep 3243925 = 152059) (by norm_num)
theorem B4325233 : Blo 2277435 4325233 := bstep (se 2 (by rfl) ⟨1621962, by rfl⟩ : syracuseStep 4325233 = 3243925) B3243925
theorem B5766977 : Blo 2277435 5766977 := bstep (se 2 (by rfl) ⟨2162616, by rfl⟩ : syracuseStep 5766977 = 4325233) B4325233
theorem B3844651 : Blo 2277435 3844651 := bstep (se 1 (by rfl) ⟨2883488, by rfl⟩ : syracuseStep 3844651 = 5766977) B5766977
theorem B5126201 : Blo 2277435 5126201 := bstep (se 2 (by rfl) ⟨1922325, by rfl⟩ : syracuseStep 5126201 = 3844651) B3844651
theorem B3417467 : Blo 2277435 3417467 := bstep (se 1 (by rfl) ⟨2563100, by rfl⟩ : syracuseStep 3417467 = 5126201) B5126201
theorem B2278311 : Blo 2277435 2278311 := bstep (se 1 (by rfl) ⟨1708733, by rfl⟩ : syracuseStep 2278311 = 3417467) B3417467
theorem B2563105 : Blo 2277435 2563105 := bbase (se 2 (by rfl) ⟨961164, by rfl⟩ : syracuseStep 2563105 = 1922329) (by norm_num)
theorem B3417473 : Blo 2277435 3417473 := bstep (se 2 (by rfl) ⟨1281552, by rfl⟩ : syracuseStep 3417473 = 2563105) B2563105
theorem B2278315 : Blo 2277435 2278315 := bstep (se 1 (by rfl) ⟨1708736, by rfl⟩ : syracuseStep 2278315 = 3417473) B3417473
theorem B5766997 : Blo 2277435 5766997 := bbase (se 9 (by rfl) ⟨16895, by rfl⟩ : syracuseStep 5766997 = 33791) (by norm_num)
theorem B7689329 : Blo 2277435 7689329 := bstep (se 2 (by rfl) ⟨2883498, by rfl⟩ : syracuseStep 7689329 = 5766997) B5766997
theorem B5126219 : Blo 2277435 5126219 := bstep (se 1 (by rfl) ⟨3844664, by rfl⟩ : syracuseStep 5126219 = 7689329) B7689329
theorem B3417479 : Blo 2277435 3417479 := bstep (se 1 (by rfl) ⟨2563109, by rfl⟩ : syracuseStep 3417479 = 5126219) B5126219
theorem B2278319 : Blo 2277435 2278319 := bstep (se 1 (by rfl) ⟨1708739, by rfl⟩ : syracuseStep 2278319 = 3417479) B3417479
theorem B3417485 : Blo 2277435 3417485 := bbase (se 3 (by rfl) ⟨640778, by rfl⟩ : syracuseStep 3417485 = 1281557) (by norm_num)
theorem B2278323 : Blo 2277435 2278323 := bstep (se 1 (by rfl) ⟨1708742, by rfl⟩ : syracuseStep 2278323 = 3417485) B3417485
theorem B5126237 : Blo 2277435 5126237 := bbase (se 3 (by rfl) ⟨961169, by rfl⟩ : syracuseStep 5126237 = 1922339) (by norm_num)
theorem B3417491 : Blo 2277435 3417491 := bstep (se 1 (by rfl) ⟨2563118, by rfl⟩ : syracuseStep 3417491 = 5126237) B5126237
theorem B2278327 : Blo 2277435 2278327 := bstep (se 1 (by rfl) ⟨1708745, by rfl⟩ : syracuseStep 2278327 = 3417491) B3417491
theorem B3844685 : Blo 2277435 3844685 := bbase (se 3 (by rfl) ⟨720878, by rfl⟩ : syracuseStep 3844685 = 1441757) (by norm_num)
theorem B2563123 : Blo 2277435 2563123 := bstep (se 1 (by rfl) ⟨1922342, by rfl⟩ : syracuseStep 2563123 = 3844685) B3844685
theorem B3417497 : Blo 2277435 3417497 := bstep (se 2 (by rfl) ⟨1281561, by rfl⟩ : syracuseStep 3417497 = 2563123) B2563123
theorem B2278331 : Blo 2277435 2278331 := bstep (se 1 (by rfl) ⟨1708748, by rfl⟩ : syracuseStep 2278331 = 3417497) B3417497
theorem B2633545 : Blo 2277435 2633545 := bbase (se 2 (by rfl) ⟨987579, by rfl⟩ : syracuseStep 2633545 = 1975159) (by norm_num)
theorem B3511393 : Blo 2277435 3511393 := bstep (se 2 (by rfl) ⟨1316772, by rfl⟩ : syracuseStep 3511393 = 2633545) B2633545
theorem B74909717 : Blo 2277435 74909717 := bstep (se 6 (by rfl) ⟨1755696, by rfl⟩ : syracuseStep 74909717 = 3511393) B3511393
theorem B49939811 : Blo 2277435 49939811 := bstep (se 1 (by rfl) ⟨37454858, by rfl⟩ : syracuseStep 49939811 = 74909717) B74909717
theorem B33293207 : Blo 2277435 33293207 := bstep (se 1 (by rfl) ⟨24969905, by rfl⟩ : syracuseStep 33293207 = 49939811) B49939811
theorem B22195471 : Blo 2277435 22195471 := bstep (se 1 (by rfl) ⟨16646603, by rfl⟩ : syracuseStep 22195471 = 33293207) B33293207
theorem B29593961 : Blo 2277435 29593961 := bstep (se 2 (by rfl) ⟨11097735, by rfl⟩ : syracuseStep 29593961 = 22195471) B22195471
theorem B19729307 : Blo 2277435 19729307 := bstep (se 1 (by rfl) ⟨14796980, by rfl⟩ : syracuseStep 19729307 = 29593961) B29593961
theorem B13152871 : Blo 2277435 13152871 := bstep (se 1 (by rfl) ⟨9864653, by rfl⟩ : syracuseStep 13152871 = 19729307) B19729307
theorem B17537161 : Blo 2277435 17537161 := bstep (se 2 (by rfl) ⟨6576435, by rfl⟩ : syracuseStep 17537161 = 13152871) B13152871
theorem B23382881 : Blo 2277435 23382881 := bstep (se 2 (by rfl) ⟨8768580, by rfl⟩ : syracuseStep 23382881 = 17537161) B17537161
theorem B15588587 : Blo 2277435 15588587 := bstep (se 1 (by rfl) ⟨11691440, by rfl⟩ : syracuseStep 15588587 = 23382881) B23382881
theorem B10392391 : Blo 2277435 10392391 := bstep (se 1 (by rfl) ⟨7794293, by rfl⟩ : syracuseStep 10392391 = 15588587) B15588587
theorem B13856521 : Blo 2277435 13856521 := bstep (se 2 (by rfl) ⟨5196195, by rfl⟩ : syracuseStep 13856521 = 10392391) B10392391
theorem B18475361 : Blo 2277435 18475361 := bstep (se 2 (by rfl) ⟨6928260, by rfl⟩ : syracuseStep 18475361 = 13856521) B13856521
theorem B12316907 : Blo 2277435 12316907 := bstep (se 1 (by rfl) ⟨9237680, by rfl⟩ : syracuseStep 12316907 = 18475361) B18475361
theorem B32845085 : Blo 2277435 32845085 := bstep (se 3 (by rfl) ⟨6158453, by rfl⟩ : syracuseStep 32845085 = 12316907) B12316907
theorem B21896723 : Blo 2277435 21896723 := bstep (se 1 (by rfl) ⟨16422542, by rfl⟩ : syracuseStep 21896723 = 32845085) B32845085
theorem B14597815 : Blo 2277435 14597815 := bstep (se 1 (by rfl) ⟨10948361, by rfl⟩ : syracuseStep 14597815 = 21896723) B21896723
theorem B19463753 : Blo 2277435 19463753 := bstep (se 2 (by rfl) ⟨7298907, by rfl⟩ : syracuseStep 19463753 = 14597815) B14597815
theorem B12975835 : Blo 2277435 12975835 := bstep (se 1 (by rfl) ⟨9731876, by rfl⟩ : syracuseStep 12975835 = 19463753) B19463753
theorem B17301113 : Blo 2277435 17301113 := bstep (se 2 (by rfl) ⟨6487917, by rfl⟩ : syracuseStep 17301113 = 12975835) B12975835
theorem B11534075 : Blo 2277435 11534075 := bstep (se 1 (by rfl) ⟨8650556, by rfl⟩ : syracuseStep 11534075 = 17301113) B17301113
theorem B7689383 : Blo 2277435 7689383 := bstep (se 1 (by rfl) ⟨5767037, by rfl⟩ : syracuseStep 7689383 = 11534075) B11534075
theorem B5126255 : Blo 2277435 5126255 := bstep (se 1 (by rfl) ⟨3844691, by rfl⟩ : syracuseStep 5126255 = 7689383) B7689383
theorem B3417503 : Blo 2277435 3417503 := bstep (se 1 (by rfl) ⟨2563127, by rfl⟩ : syracuseStep 3417503 = 5126255) B5126255
theorem B2278335 : Blo 2277435 2278335 := bstep (se 1 (by rfl) ⟨1708751, by rfl⟩ : syracuseStep 2278335 = 3417503) B3417503
theorem B3417509 : Blo 2277435 3417509 := bbase (se 4 (by rfl) ⟨320391, by rfl⟩ : syracuseStep 3417509 = 640783) (by norm_num)
theorem B2278339 : Blo 2277435 2278339 := bstep (se 1 (by rfl) ⟨1708754, by rfl⟩ : syracuseStep 2278339 = 3417509) B3417509
theorem B2883529 : Blo 2277435 2883529 := bbase (se 2 (by rfl) ⟨1081323, by rfl⟩ : syracuseStep 2883529 = 2162647) (by norm_num)
theorem B3844705 : Blo 2277435 3844705 := bstep (se 2 (by rfl) ⟨1441764, by rfl⟩ : syracuseStep 3844705 = 2883529) B2883529
theorem B5126273 : Blo 2277435 5126273 := bstep (se 2 (by rfl) ⟨1922352, by rfl⟩ : syracuseStep 5126273 = 3844705) B3844705
theorem B3417515 : Blo 2277435 3417515 := bstep (se 1 (by rfl) ⟨2563136, by rfl⟩ : syracuseStep 3417515 = 5126273) B5126273
theorem B2278343 : Blo 2277435 2278343 := bstep (se 1 (by rfl) ⟨1708757, by rfl⟩ : syracuseStep 2278343 = 3417515) B3417515
theorem B2563141 : Blo 2277435 2563141 := bbase (se 4 (by rfl) ⟨240294, by rfl⟩ : syracuseStep 2563141 = 480589) (by norm_num)
theorem B3417521 : Blo 2277435 3417521 := bstep (se 2 (by rfl) ⟨1281570, by rfl⟩ : syracuseStep 3417521 = 2563141) B2563141
theorem B2278347 : Blo 2277435 2278347 := bstep (se 1 (by rfl) ⟨1708760, by rfl⟩ : syracuseStep 2278347 = 3417521) B3417521
theorem B4325309 : Blo 2277435 4325309 := bbase (se 3 (by rfl) ⟨810995, by rfl⟩ : syracuseStep 4325309 = 1621991) (by norm_num)
theorem B2883539 : Blo 2277435 2883539 := bstep (se 1 (by rfl) ⟨2162654, by rfl⟩ : syracuseStep 2883539 = 4325309) B4325309
theorem B7689437 : Blo 2277435 7689437 := bstep (se 3 (by rfl) ⟨1441769, by rfl⟩ : syracuseStep 7689437 = 2883539) B2883539
theorem B5126291 : Blo 2277435 5126291 := bstep (se 1 (by rfl) ⟨3844718, by rfl⟩ : syracuseStep 5126291 = 7689437) B7689437
theorem B3417527 : Blo 2277435 3417527 := bstep (se 1 (by rfl) ⟨2563145, by rfl⟩ : syracuseStep 3417527 = 5126291) B5126291
theorem B2278351 : Blo 2277435 2278351 := bstep (se 1 (by rfl) ⟨1708763, by rfl⟩ : syracuseStep 2278351 = 3417527) B3417527
theorem B3417533 : Blo 2277435 3417533 := bbase (se 3 (by rfl) ⟨640787, by rfl⟩ : syracuseStep 3417533 = 1281575) (by norm_num)
theorem B2278355 : Blo 2277435 2278355 := bstep (se 1 (by rfl) ⟨1708766, by rfl⟩ : syracuseStep 2278355 = 3417533) B3417533
theorem B5126309 : Blo 2277435 5126309 := bbase (se 4 (by rfl) ⟨480591, by rfl⟩ : syracuseStep 5126309 = 961183) (by norm_num)
theorem B3417539 : Blo 2277435 3417539 := bstep (se 1 (by rfl) ⟨2563154, by rfl⟩ : syracuseStep 3417539 = 5126309) B5126309
theorem B2278359 : Blo 2277435 2278359 := bstep (se 1 (by rfl) ⟨1708769, by rfl⟩ : syracuseStep 2278359 = 3417539) B3417539
theorem B5767109 : Blo 2277435 5767109 := bbase (se 4 (by rfl) ⟨540666, by rfl⟩ : syracuseStep 5767109 = 1081333) (by norm_num)
theorem B3844739 : Blo 2277435 3844739 := bstep (se 1 (by rfl) ⟨2883554, by rfl⟩ : syracuseStep 3844739 = 5767109) B5767109
theorem B2563159 : Blo 2277435 2563159 := bstep (se 1 (by rfl) ⟨1922369, by rfl⟩ : syracuseStep 2563159 = 3844739) B3844739
theorem B3417545 : Blo 2277435 3417545 := bstep (se 2 (by rfl) ⟨1281579, by rfl⟩ : syracuseStep 3417545 = 2563159) B2563159
theorem B2278363 : Blo 2277435 2278363 := bstep (se 1 (by rfl) ⟨1708772, by rfl⟩ : syracuseStep 2278363 = 3417545) B3417545
theorem B10948517 : Blo 2277435 10948517 := bbase (se 4 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 10948517 = 2052847) (by norm_num)
theorem B7299011 : Blo 2277435 7299011 := bstep (se 1 (by rfl) ⟨5474258, by rfl⟩ : syracuseStep 7299011 = 10948517) B10948517
theorem B4866007 : Blo 2277435 4866007 := bstep (se 1 (by rfl) ⟨3649505, by rfl⟩ : syracuseStep 4866007 = 7299011) B7299011
theorem B6488009 : Blo 2277435 6488009 := bstep (se 2 (by rfl) ⟨2433003, by rfl⟩ : syracuseStep 6488009 = 4866007) B4866007
theorem B4325339 : Blo 2277435 4325339 := bstep (se 1 (by rfl) ⟨3244004, by rfl⟩ : syracuseStep 4325339 = 6488009) B6488009
theorem B11534237 : Blo 2277435 11534237 := bstep (se 3 (by rfl) ⟨2162669, by rfl⟩ : syracuseStep 11534237 = 4325339) B4325339
theorem B7689491 : Blo 2277435 7689491 := bstep (se 1 (by rfl) ⟨5767118, by rfl⟩ : syracuseStep 7689491 = 11534237) B11534237
theorem B5126327 : Blo 2277435 5126327 := bstep (se 1 (by rfl) ⟨3844745, by rfl⟩ : syracuseStep 5126327 = 7689491) B7689491
theorem B3417551 : Blo 2277435 3417551 := bstep (se 1 (by rfl) ⟨2563163, by rfl⟩ : syracuseStep 3417551 = 5126327) B5126327
theorem B2278367 : Blo 2277435 2278367 := bstep (se 1 (by rfl) ⟨1708775, by rfl⟩ : syracuseStep 2278367 = 3417551) B3417551
theorem B3417557 : Blo 2277435 3417557 := bbase (se 7 (by rfl) ⟨40049, by rfl⟩ : syracuseStep 3417557 = 80099) (by norm_num)
theorem B2278371 : Blo 2277435 2278371 := bstep (se 1 (by rfl) ⟨1708778, by rfl⟩ : syracuseStep 2278371 = 3417557) B3417557
theorem B8650709 : Blo 2277435 8650709 := bbase (se 7 (by rfl) ⟨101375, by rfl⟩ : syracuseStep 8650709 = 202751) (by norm_num)
theorem B5767139 : Blo 2277435 5767139 := bstep (se 1 (by rfl) ⟨4325354, by rfl⟩ : syracuseStep 5767139 = 8650709) B8650709
theorem B3844759 : Blo 2277435 3844759 := bstep (se 1 (by rfl) ⟨2883569, by rfl⟩ : syracuseStep 3844759 = 5767139) B5767139
theorem B5126345 : Blo 2277435 5126345 := bstep (se 2 (by rfl) ⟨1922379, by rfl⟩ : syracuseStep 5126345 = 3844759) B3844759
theorem B3417563 : Blo 2277435 3417563 := bstep (se 1 (by rfl) ⟨2563172, by rfl⟩ : syracuseStep 3417563 = 5126345) B5126345
theorem B2278375 : Blo 2277435 2278375 := bstep (se 1 (by rfl) ⟨1708781, by rfl⟩ : syracuseStep 2278375 = 3417563) B3417563
theorem B2563177 : Blo 2277435 2563177 := bbase (se 2 (by rfl) ⟨961191, by rfl⟩ : syracuseStep 2563177 = 1922383) (by norm_num)
theorem B3417569 : Blo 2277435 3417569 := bstep (se 2 (by rfl) ⟨1281588, by rfl⟩ : syracuseStep 3417569 = 2563177) B2563177
theorem B2278379 : Blo 2277435 2278379 := bstep (se 1 (by rfl) ⟨1708784, by rfl⟩ : syracuseStep 2278379 = 3417569) B3417569
theorem B2466217 : Blo 2277435 2466217 := bbase (se 2 (by rfl) ⟨924831, by rfl⟩ : syracuseStep 2466217 = 1849663) (by norm_num)
theorem B3288289 : Blo 2277435 3288289 := bstep (se 2 (by rfl) ⟨1233108, by rfl⟩ : syracuseStep 3288289 = 2466217) B2466217
theorem B4384385 : Blo 2277435 4384385 := bstep (se 2 (by rfl) ⟨1644144, by rfl⟩ : syracuseStep 4384385 = 3288289) B3288289
theorem B2922923 : Blo 2277435 2922923 := bstep (se 1 (by rfl) ⟨2192192, by rfl⟩ : syracuseStep 2922923 = 4384385) B4384385
theorem B7794461 : Blo 2277435 7794461 := bstep (se 3 (by rfl) ⟨1461461, by rfl⟩ : syracuseStep 7794461 = 2922923) B2922923
theorem B5196307 : Blo 2277435 5196307 := bstep (se 1 (by rfl) ⟨3897230, by rfl⟩ : syracuseStep 5196307 = 7794461) B7794461
theorem B6928409 : Blo 2277435 6928409 := bstep (se 2 (by rfl) ⟨2598153, by rfl⟩ : syracuseStep 6928409 = 5196307) B5196307
theorem B4618939 : Blo 2277435 4618939 := bstep (se 1 (by rfl) ⟨3464204, by rfl⟩ : syracuseStep 4618939 = 6928409) B6928409
theorem B6158585 : Blo 2277435 6158585 := bstep (se 2 (by rfl) ⟨2309469, by rfl⟩ : syracuseStep 6158585 = 4618939) B4618939
theorem B4105723 : Blo 2277435 4105723 := bstep (se 1 (by rfl) ⟨3079292, by rfl⟩ : syracuseStep 4105723 = 6158585) B6158585
theorem B5474297 : Blo 2277435 5474297 := bstep (se 2 (by rfl) ⟨2052861, by rfl⟩ : syracuseStep 5474297 = 4105723) B4105723
theorem B3649531 : Blo 2277435 3649531 := bstep (se 1 (by rfl) ⟨2737148, by rfl⟩ : syracuseStep 3649531 = 5474297) B5474297
theorem B4866041 : Blo 2277435 4866041 := bstep (se 2 (by rfl) ⟨1824765, by rfl⟩ : syracuseStep 4866041 = 3649531) B3649531
theorem B12976109 : Blo 2277435 12976109 := bstep (se 3 (by rfl) ⟨2433020, by rfl⟩ : syracuseStep 12976109 = 4866041) B4866041
theorem B8650739 : Blo 2277435 8650739 := bstep (se 1 (by rfl) ⟨6488054, by rfl⟩ : syracuseStep 8650739 = 12976109) B12976109
theorem B5767159 : Blo 2277435 5767159 := bstep (se 1 (by rfl) ⟨4325369, by rfl⟩ : syracuseStep 5767159 = 8650739) B8650739
theorem B7689545 : Blo 2277435 7689545 := bstep (se 2 (by rfl) ⟨2883579, by rfl⟩ : syracuseStep 7689545 = 5767159) B5767159
theorem B5126363 : Blo 2277435 5126363 := bstep (se 1 (by rfl) ⟨3844772, by rfl⟩ : syracuseStep 5126363 = 7689545) B7689545
theorem B3417575 : Blo 2277435 3417575 := bstep (se 1 (by rfl) ⟨2563181, by rfl⟩ : syracuseStep 3417575 = 5126363) B5126363
theorem B2278383 : Blo 2277435 2278383 := bstep (se 1 (by rfl) ⟨1708787, by rfl⟩ : syracuseStep 2278383 = 3417575) B3417575
theorem B3417581 : Blo 2277435 3417581 := bbase (se 3 (by rfl) ⟨640796, by rfl⟩ : syracuseStep 3417581 = 1281593) (by norm_num)
theorem B2278387 : Blo 2277435 2278387 := bstep (se 1 (by rfl) ⟨1708790, by rfl⟩ : syracuseStep 2278387 = 3417581) B3417581
theorem B5126381 : Blo 2277435 5126381 := bbase (se 3 (by rfl) ⟨961196, by rfl⟩ : syracuseStep 5126381 = 1922393) (by norm_num)
theorem B3417587 : Blo 2277435 3417587 := bstep (se 1 (by rfl) ⟨2563190, by rfl⟩ : syracuseStep 3417587 = 5126381) B5126381
theorem B2278391 : Blo 2277435 2278391 := bstep (se 1 (by rfl) ⟨1708793, by rfl⟩ : syracuseStep 2278391 = 3417587) B3417587
theorem B3244045 : Blo 2277435 3244045 := bbase (se 3 (by rfl) ⟨608258, by rfl⟩ : syracuseStep 3244045 = 1216517) (by norm_num)
theorem B4325393 : Blo 2277435 4325393 := bstep (se 2 (by rfl) ⟨1622022, by rfl⟩ : syracuseStep 4325393 = 3244045) B3244045
theorem B2883595 : Blo 2277435 2883595 := bstep (se 1 (by rfl) ⟨2162696, by rfl⟩ : syracuseStep 2883595 = 4325393) B4325393
theorem B3844793 : Blo 2277435 3844793 := bstep (se 2 (by rfl) ⟨1441797, by rfl⟩ : syracuseStep 3844793 = 2883595) B2883595
theorem B2563195 : Blo 2277435 2563195 := bstep (se 1 (by rfl) ⟨1922396, by rfl⟩ : syracuseStep 2563195 = 3844793) B3844793
theorem B3417593 : Blo 2277435 3417593 := bstep (se 2 (by rfl) ⟨1281597, by rfl⟩ : syracuseStep 3417593 = 2563195) B2563195
theorem B2278395 : Blo 2277435 2278395 := bstep (se 1 (by rfl) ⟨1708796, by rfl⟩ : syracuseStep 2278395 = 3417593) B3417593
theorem B3800981 : Blo 2277435 3800981 := bbase (se 6 (by rfl) ⟨89085, by rfl⟩ : syracuseStep 3800981 = 178171) (by norm_num)
theorem B2533987 : Blo 2277435 2533987 := bstep (se 1 (by rfl) ⟨1900490, by rfl⟩ : syracuseStep 2533987 = 3800981) B3800981
theorem B3378649 : Blo 2277435 3378649 := bstep (se 2 (by rfl) ⟨1266993, by rfl⟩ : syracuseStep 3378649 = 2533987) B2533987
theorem B4504865 : Blo 2277435 4504865 := bstep (se 2 (by rfl) ⟨1689324, by rfl⟩ : syracuseStep 4504865 = 3378649) B3378649
theorem B48051893 : Blo 2277435 48051893 := bstep (se 5 (by rfl) ⟨2252432, by rfl⟩ : syracuseStep 48051893 = 4504865) B4504865
theorem B128138381 : Blo 2277435 128138381 := bstep (se 3 (by rfl) ⟨24025946, by rfl⟩ : syracuseStep 128138381 = 48051893) B48051893
theorem B85425587 : Blo 2277435 85425587 := bstep (se 1 (by rfl) ⟨64069190, by rfl⟩ : syracuseStep 85425587 = 128138381) B128138381
theorem B56950391 : Blo 2277435 56950391 := bstep (se 1 (by rfl) ⟨42712793, by rfl⟩ : syracuseStep 56950391 = 85425587) B85425587
theorem B37966927 : Blo 2277435 37966927 := bstep (se 1 (by rfl) ⟨28475195, by rfl⟩ : syracuseStep 37966927 = 56950391) B56950391
theorem B50622569 : Blo 2277435 50622569 := bstep (se 2 (by rfl) ⟨18983463, by rfl⟩ : syracuseStep 50622569 = 37966927) B37966927
theorem B33748379 : Blo 2277435 33748379 := bstep (se 1 (by rfl) ⟨25311284, by rfl⟩ : syracuseStep 33748379 = 50622569) B50622569
theorem B22498919 : Blo 2277435 22498919 := bstep (se 1 (by rfl) ⟨16874189, by rfl⟩ : syracuseStep 22498919 = 33748379) B33748379
theorem B14999279 : Blo 2277435 14999279 := bstep (se 1 (by rfl) ⟨11249459, by rfl⟩ : syracuseStep 14999279 = 22498919) B22498919
theorem B159992309 : Blo 2277435 159992309 := bstep (se 5 (by rfl) ⟨7499639, by rfl⟩ : syracuseStep 159992309 = 14999279) B14999279
theorem B106661539 : Blo 2277435 106661539 := bstep (se 1 (by rfl) ⟨79996154, by rfl⟩ : syracuseStep 106661539 = 159992309) B159992309
theorem B568861541 : Blo 2277435 568861541 := bstep (se 4 (by rfl) ⟨53330769, by rfl⟩ : syracuseStep 568861541 = 106661539) B106661539
theorem B379241027 : Blo 2277435 379241027 := bstep (se 1 (by rfl) ⟨284430770, by rfl⟩ : syracuseStep 379241027 = 568861541) B568861541
theorem B252827351 : Blo 2277435 252827351 := bstep (se 1 (by rfl) ⟨189620513, by rfl⟩ : syracuseStep 252827351 = 379241027) B379241027
theorem B168551567 : Blo 2277435 168551567 := bstep (se 1 (by rfl) ⟨126413675, by rfl⟩ : syracuseStep 168551567 = 252827351) B252827351
theorem B112367711 : Blo 2277435 112367711 := bstep (se 1 (by rfl) ⟨84275783, by rfl⟩ : syracuseStep 112367711 = 168551567) B168551567
theorem B74911807 : Blo 2277435 74911807 := bstep (se 1 (by rfl) ⟨56183855, by rfl⟩ : syracuseStep 74911807 = 112367711) B112367711
theorem B99882409 : Blo 2277435 99882409 := bstep (se 2 (by rfl) ⟨37455903, by rfl⟩ : syracuseStep 99882409 = 74911807) B74911807
theorem B133176545 : Blo 2277435 133176545 := bstep (se 2 (by rfl) ⟨49941204, by rfl⟩ : syracuseStep 133176545 = 99882409) B99882409
theorem B88784363 : Blo 2277435 88784363 := bstep (se 1 (by rfl) ⟨66588272, by rfl⟩ : syracuseStep 88784363 = 133176545) B133176545
theorem B236758301 : Blo 2277435 236758301 := bstep (se 3 (by rfl) ⟨44392181, by rfl⟩ : syracuseStep 236758301 = 88784363) B88784363
theorem B157838867 : Blo 2277435 157838867 := bstep (se 1 (by rfl) ⟨118379150, by rfl⟩ : syracuseStep 157838867 = 236758301) B236758301
theorem B105225911 : Blo 2277435 105225911 := bstep (se 1 (by rfl) ⟨78919433, by rfl⟩ : syracuseStep 105225911 = 157838867) B157838867
theorem B70150607 : Blo 2277435 70150607 := bstep (se 1 (by rfl) ⟨52612955, by rfl⟩ : syracuseStep 70150607 = 105225911) B105225911
theorem B46767071 : Blo 2277435 46767071 := bstep (se 1 (by rfl) ⟨35075303, by rfl⟩ : syracuseStep 46767071 = 70150607) B70150607
theorem B31178047 : Blo 2277435 31178047 := bstep (se 1 (by rfl) ⟨23383535, by rfl⟩ : syracuseStep 31178047 = 46767071) B46767071
theorem B41570729 : Blo 2277435 41570729 := bstep (se 2 (by rfl) ⟨15589023, by rfl⟩ : syracuseStep 41570729 = 31178047) B31178047
theorem B27713819 : Blo 2277435 27713819 := bstep (se 1 (by rfl) ⟨20785364, by rfl⟩ : syracuseStep 27713819 = 41570729) B41570729
theorem B18475879 : Blo 2277435 18475879 := bstep (se 1 (by rfl) ⟨13856909, by rfl⟩ : syracuseStep 18475879 = 27713819) B27713819
theorem B24634505 : Blo 2277435 24634505 := bstep (se 2 (by rfl) ⟨9237939, by rfl⟩ : syracuseStep 24634505 = 18475879) B18475879
theorem B16423003 : Blo 2277435 16423003 := bstep (se 1 (by rfl) ⟨12317252, by rfl⟩ : syracuseStep 16423003 = 24634505) B24634505
theorem B87589349 : Blo 2277435 87589349 := bstep (se 4 (by rfl) ⟨8211501, by rfl⟩ : syracuseStep 87589349 = 16423003) B16423003
theorem B58392899 : Blo 2277435 58392899 := bstep (se 1 (by rfl) ⟨43794674, by rfl⟩ : syracuseStep 58392899 = 87589349) B87589349
theorem B38928599 : Blo 2277435 38928599 := bstep (se 1 (by rfl) ⟨29196449, by rfl⟩ : syracuseStep 38928599 = 58392899) B58392899
theorem B25952399 : Blo 2277435 25952399 := bstep (se 1 (by rfl) ⟨19464299, by rfl⟩ : syracuseStep 25952399 = 38928599) B38928599
theorem B17301599 : Blo 2277435 17301599 := bstep (se 1 (by rfl) ⟨12976199, by rfl⟩ : syracuseStep 17301599 = 25952399) B25952399
theorem B11534399 : Blo 2277435 11534399 := bstep (se 1 (by rfl) ⟨8650799, by rfl⟩ : syracuseStep 11534399 = 17301599) B17301599
theorem B7689599 : Blo 2277435 7689599 := bstep (se 1 (by rfl) ⟨5767199, by rfl⟩ : syracuseStep 7689599 = 11534399) B11534399
theorem B5126399 : Blo 2277435 5126399 := bstep (se 1 (by rfl) ⟨3844799, by rfl⟩ : syracuseStep 5126399 = 7689599) B7689599
theorem B3417599 : Blo 2277435 3417599 := bstep (se 1 (by rfl) ⟨2563199, by rfl⟩ : syracuseStep 3417599 = 5126399) B5126399
theorem B2278399 : Blo 2277435 2278399 := bstep (se 1 (by rfl) ⟨1708799, by rfl⟩ : syracuseStep 2278399 = 3417599) B3417599
theorem B3417605 : Blo 2277435 3417605 := bbase (se 4 (by rfl) ⟨320400, by rfl⟩ : syracuseStep 3417605 = 640801) (by norm_num)
theorem B2278403 : Blo 2277435 2278403 := bstep (se 1 (by rfl) ⟨1708802, by rfl⟩ : syracuseStep 2278403 = 3417605) B3417605
theorem B3844813 : Blo 2277435 3844813 := bbase (se 3 (by rfl) ⟨720902, by rfl⟩ : syracuseStep 3844813 = 1441805) (by norm_num)
theorem B5126417 : Blo 2277435 5126417 := bstep (se 2 (by rfl) ⟨1922406, by rfl⟩ : syracuseStep 5126417 = 3844813) B3844813
theorem B3417611 : Blo 2277435 3417611 := bstep (se 1 (by rfl) ⟨2563208, by rfl⟩ : syracuseStep 3417611 = 5126417) B5126417
theorem B2278407 : Blo 2277435 2278407 := bstep (se 1 (by rfl) ⟨1708805, by rfl⟩ : syracuseStep 2278407 = 3417611) B3417611
theorem B2563213 : Blo 2277435 2563213 := bbase (se 3 (by rfl) ⟨480602, by rfl⟩ : syracuseStep 2563213 = 961205) (by norm_num)
theorem B3417617 : Blo 2277435 3417617 := bstep (se 2 (by rfl) ⟨1281606, by rfl⟩ : syracuseStep 3417617 = 2563213) B2563213
theorem B2278411 : Blo 2277435 2278411 := bstep (se 1 (by rfl) ⟨1708808, by rfl⟩ : syracuseStep 2278411 = 3417617) B3417617
theorem B7689653 : Blo 2277435 7689653 := bbase (se 5 (by rfl) ⟨360452, by rfl⟩ : syracuseStep 7689653 = 720905) (by norm_num)
theorem B5126435 : Blo 2277435 5126435 := bstep (se 1 (by rfl) ⟨3844826, by rfl⟩ : syracuseStep 5126435 = 7689653) B7689653
theorem B3417623 : Blo 2277435 3417623 := bstep (se 1 (by rfl) ⟨2563217, by rfl⟩ : syracuseStep 3417623 = 5126435) B5126435
theorem B2278415 : Blo 2277435 2278415 := bstep (se 1 (by rfl) ⟨1708811, by rfl⟩ : syracuseStep 2278415 = 3417623) B3417623
theorem B3417629 : Blo 2277435 3417629 := bbase (se 3 (by rfl) ⟨640805, by rfl⟩ : syracuseStep 3417629 = 1281611) (by norm_num)
theorem B2278419 : Blo 2277435 2278419 := bstep (se 1 (by rfl) ⟨1708814, by rfl⟩ : syracuseStep 2278419 = 3417629) B3417629
theorem B5126453 : Blo 2277435 5126453 := bbase (se 5 (by rfl) ⟨240302, by rfl⟩ : syracuseStep 5126453 = 480605) (by norm_num)
theorem B3417635 : Blo 2277435 3417635 := bstep (se 1 (by rfl) ⟨2563226, by rfl⟩ : syracuseStep 3417635 = 5126453) B5126453
theorem B2278423 : Blo 2277435 2278423 := bstep (se 1 (by rfl) ⟨1708817, by rfl⟩ : syracuseStep 2278423 = 3417635) B3417635
theorem B23383829 : Blo 2277435 23383829 := bbase (se 6 (by rfl) ⟨548058, by rfl⟩ : syracuseStep 23383829 = 1096117) (by norm_num)
theorem B15589219 : Blo 2277435 15589219 := bstep (se 1 (by rfl) ⟨11691914, by rfl⟩ : syracuseStep 15589219 = 23383829) B23383829
theorem B20785625 : Blo 2277435 20785625 := bstep (se 2 (by rfl) ⟨7794609, by rfl⟩ : syracuseStep 20785625 = 15589219) B15589219
theorem B13857083 : Blo 2277435 13857083 := bstep (se 1 (by rfl) ⟨10392812, by rfl⟩ : syracuseStep 13857083 = 20785625) B20785625
theorem B9238055 : Blo 2277435 9238055 := bstep (se 1 (by rfl) ⟨6928541, by rfl⟩ : syracuseStep 9238055 = 13857083) B13857083
theorem B24634813 : Blo 2277435 24634813 := bstep (se 3 (by rfl) ⟨4619027, by rfl⟩ : syracuseStep 24634813 = 9238055) B9238055
theorem B32846417 : Blo 2277435 32846417 := bstep (se 2 (by rfl) ⟨12317406, by rfl⟩ : syracuseStep 32846417 = 24634813) B24634813
theorem B21897611 : Blo 2277435 21897611 := bstep (se 1 (by rfl) ⟨16423208, by rfl⟩ : syracuseStep 21897611 = 32846417) B32846417
theorem B14598407 : Blo 2277435 14598407 := bstep (se 1 (by rfl) ⟨10948805, by rfl⟩ : syracuseStep 14598407 = 21897611) B21897611
theorem B9732271 : Blo 2277435 9732271 := bstep (se 1 (by rfl) ⟨7299203, by rfl⟩ : syracuseStep 9732271 = 14598407) B14598407
theorem B12976361 : Blo 2277435 12976361 := bstep (se 2 (by rfl) ⟨4866135, by rfl⟩ : syracuseStep 12976361 = 9732271) B9732271
theorem B8650907 : Blo 2277435 8650907 := bstep (se 1 (by rfl) ⟨6488180, by rfl⟩ : syracuseStep 8650907 = 12976361) B12976361
theorem B5767271 : Blo 2277435 5767271 := bstep (se 1 (by rfl) ⟨4325453, by rfl⟩ : syracuseStep 5767271 = 8650907) B8650907
theorem B3844847 : Blo 2277435 3844847 := bstep (se 1 (by rfl) ⟨2883635, by rfl⟩ : syracuseStep 3844847 = 5767271) B5767271
theorem B2563231 : Blo 2277435 2563231 := bstep (se 1 (by rfl) ⟨1922423, by rfl⟩ : syracuseStep 2563231 = 3844847) B3844847
theorem B3417641 : Blo 2277435 3417641 := bstep (se 2 (by rfl) ⟨1281615, by rfl⟩ : syracuseStep 3417641 = 2563231) B2563231
theorem B2278427 : Blo 2277435 2278427 := bstep (se 1 (by rfl) ⟨1708820, by rfl⟩ : syracuseStep 2278427 = 3417641) B3417641
theorem B6242741 : Blo 2277435 6242741 := bbase (se 5 (by rfl) ⟨292628, by rfl⟩ : syracuseStep 6242741 = 585257) (by norm_num)
theorem B4161827 : Blo 2277435 4161827 := bstep (se 1 (by rfl) ⟨3121370, by rfl⟩ : syracuseStep 4161827 = 6242741) B6242741
theorem B11098205 : Blo 2277435 11098205 := bstep (se 3 (by rfl) ⟨2080913, by rfl⟩ : syracuseStep 11098205 = 4161827) B4161827
theorem B7398803 : Blo 2277435 7398803 := bstep (se 1 (by rfl) ⟨5549102, by rfl⟩ : syracuseStep 7398803 = 11098205) B11098205
theorem B19730141 : Blo 2277435 19730141 := bstep (se 3 (by rfl) ⟨3699401, by rfl⟩ : syracuseStep 19730141 = 7398803) B7398803
theorem B13153427 : Blo 2277435 13153427 := bstep (se 1 (by rfl) ⟨9865070, by rfl⟩ : syracuseStep 13153427 = 19730141) B19730141
theorem B8768951 : Blo 2277435 8768951 := bstep (se 1 (by rfl) ⟨6576713, by rfl⟩ : syracuseStep 8768951 = 13153427) B13153427
theorem B5845967 : Blo 2277435 5845967 := bstep (se 1 (by rfl) ⟨4384475, by rfl⟩ : syracuseStep 5845967 = 8768951) B8768951
theorem B3897311 : Blo 2277435 3897311 := bstep (se 1 (by rfl) ⟨2922983, by rfl⟩ : syracuseStep 3897311 = 5845967) B5845967
theorem B10392829 : Blo 2277435 10392829 := bstep (se 3 (by rfl) ⟨1948655, by rfl⟩ : syracuseStep 10392829 = 3897311) B3897311
theorem B55428421 : Blo 2277435 55428421 := bstep (se 4 (by rfl) ⟨5196414, by rfl⟩ : syracuseStep 55428421 = 10392829) B10392829
theorem B73904561 : Blo 2277435 73904561 := bstep (se 2 (by rfl) ⟨27714210, by rfl⟩ : syracuseStep 73904561 = 55428421) B55428421
theorem B49269707 : Blo 2277435 49269707 := bstep (se 1 (by rfl) ⟨36952280, by rfl⟩ : syracuseStep 49269707 = 73904561) B73904561
theorem B32846471 : Blo 2277435 32846471 := bstep (se 1 (by rfl) ⟨24634853, by rfl⟩ : syracuseStep 32846471 = 49269707) B49269707
theorem B21897647 : Blo 2277435 21897647 := bstep (se 1 (by rfl) ⟨16423235, by rfl⟩ : syracuseStep 21897647 = 32846471) B32846471
theorem B14598431 : Blo 2277435 14598431 := bstep (se 1 (by rfl) ⟨10948823, by rfl⟩ : syracuseStep 14598431 = 21897647) B21897647
theorem B9732287 : Blo 2277435 9732287 := bstep (se 1 (by rfl) ⟨7299215, by rfl⟩ : syracuseStep 9732287 = 14598431) B14598431
theorem B6488191 : Blo 2277435 6488191 := bstep (se 1 (by rfl) ⟨4866143, by rfl⟩ : syracuseStep 6488191 = 9732287) B9732287
theorem B8650921 : Blo 2277435 8650921 := bstep (se 2 (by rfl) ⟨3244095, by rfl⟩ : syracuseStep 8650921 = 6488191) B6488191
theorem B11534561 : Blo 2277435 11534561 := bstep (se 2 (by rfl) ⟨4325460, by rfl⟩ : syracuseStep 11534561 = 8650921) B8650921
theorem B7689707 : Blo 2277435 7689707 := bstep (se 1 (by rfl) ⟨5767280, by rfl⟩ : syracuseStep 7689707 = 11534561) B11534561
theorem B5126471 : Blo 2277435 5126471 := bstep (se 1 (by rfl) ⟨3844853, by rfl⟩ : syracuseStep 5126471 = 7689707) B7689707
theorem B3417647 : Blo 2277435 3417647 := bstep (se 1 (by rfl) ⟨2563235, by rfl⟩ : syracuseStep 3417647 = 5126471) B5126471
theorem B2278431 : Blo 2277435 2278431 := bstep (se 1 (by rfl) ⟨1708823, by rfl⟩ : syracuseStep 2278431 = 3417647) B3417647
theorem B3417653 : Blo 2277435 3417653 := bbase (se 5 (by rfl) ⟨160202, by rfl⟩ : syracuseStep 3417653 = 320405) (by norm_num)
theorem B2278435 : Blo 2277435 2278435 := bstep (se 1 (by rfl) ⟨1708826, by rfl⟩ : syracuseStep 2278435 = 3417653) B3417653
theorem B5767301 : Blo 2277435 5767301 := bbase (se 4 (by rfl) ⟨540684, by rfl⟩ : syracuseStep 5767301 = 1081369) (by norm_num)
theorem B3844867 : Blo 2277435 3844867 := bstep (se 1 (by rfl) ⟨2883650, by rfl⟩ : syracuseStep 3844867 = 5767301) B5767301
theorem B5126489 : Blo 2277435 5126489 := bstep (se 2 (by rfl) ⟨1922433, by rfl⟩ : syracuseStep 5126489 = 3844867) B3844867
theorem B3417659 : Blo 2277435 3417659 := bstep (se 1 (by rfl) ⟨2563244, by rfl⟩ : syracuseStep 3417659 = 5126489) B5126489
theorem B2278439 : Blo 2277435 2278439 := bstep (se 1 (by rfl) ⟨1708829, by rfl⟩ : syracuseStep 2278439 = 3417659) B3417659
theorem B2563249 : Blo 2277435 2563249 := bbase (se 2 (by rfl) ⟨961218, by rfl⟩ : syracuseStep 2563249 = 1922437) (by norm_num)
theorem B3417665 : Blo 2277435 3417665 := bstep (se 2 (by rfl) ⟨1281624, by rfl⟩ : syracuseStep 3417665 = 2563249) B2563249
theorem B2278443 : Blo 2277435 2278443 := bstep (se 1 (by rfl) ⟨1708832, by rfl⟩ : syracuseStep 2278443 = 3417665) B3417665
theorem B2433089 : Blo 2277435 2433089 := bbase (se 2 (by rfl) ⟨912408, by rfl⟩ : syracuseStep 2433089 = 1824817) (by norm_num)
theorem B6488237 : Blo 2277435 6488237 := bstep (se 3 (by rfl) ⟨1216544, by rfl⟩ : syracuseStep 6488237 = 2433089) B2433089
theorem B4325491 : Blo 2277435 4325491 := bstep (se 1 (by rfl) ⟨3244118, by rfl⟩ : syracuseStep 4325491 = 6488237) B6488237
theorem B5767321 : Blo 2277435 5767321 := bstep (se 2 (by rfl) ⟨2162745, by rfl⟩ : syracuseStep 5767321 = 4325491) B4325491
theorem B7689761 : Blo 2277435 7689761 := bstep (se 2 (by rfl) ⟨2883660, by rfl⟩ : syracuseStep 7689761 = 5767321) B5767321
theorem B5126507 : Blo 2277435 5126507 := bstep (se 1 (by rfl) ⟨3844880, by rfl⟩ : syracuseStep 5126507 = 7689761) B7689761
theorem B3417671 : Blo 2277435 3417671 := bstep (se 1 (by rfl) ⟨2563253, by rfl⟩ : syracuseStep 3417671 = 5126507) B5126507
theorem B2278447 : Blo 2277435 2278447 := bstep (se 1 (by rfl) ⟨1708835, by rfl⟩ : syracuseStep 2278447 = 3417671) B3417671
theorem B3417677 : Blo 2277435 3417677 := bbase (se 3 (by rfl) ⟨640814, by rfl⟩ : syracuseStep 3417677 = 1281629) (by norm_num)
theorem B2278451 : Blo 2277435 2278451 := bstep (se 1 (by rfl) ⟨1708838, by rfl⟩ : syracuseStep 2278451 = 3417677) B3417677
theorem B5126525 : Blo 2277435 5126525 := bbase (se 3 (by rfl) ⟨961223, by rfl⟩ : syracuseStep 5126525 = 1922447) (by norm_num)
theorem B3417683 : Blo 2277435 3417683 := bstep (se 1 (by rfl) ⟨2563262, by rfl⟩ : syracuseStep 3417683 = 5126525) B5126525
theorem B2278455 : Blo 2277435 2278455 := bstep (se 1 (by rfl) ⟨1708841, by rfl⟩ : syracuseStep 2278455 = 3417683) B3417683
theorem B3844901 : Blo 2277435 3844901 := bbase (se 4 (by rfl) ⟨360459, by rfl⟩ : syracuseStep 3844901 = 720919) (by norm_num)
theorem B2563267 : Blo 2277435 2563267 := bstep (se 1 (by rfl) ⟨1922450, by rfl⟩ : syracuseStep 2563267 = 3844901) B3844901
theorem B3417689 : Blo 2277435 3417689 := bstep (se 2 (by rfl) ⟨1281633, by rfl⟩ : syracuseStep 3417689 = 2563267) B2563267
theorem B2278459 : Blo 2277435 2278459 := bstep (se 1 (by rfl) ⟨1708844, by rfl⟩ : syracuseStep 2278459 = 3417689) B3417689
theorem B3244141 : Blo 2277435 3244141 := bbase (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) (by norm_num)
theorem B17302085 : Blo 2277435 17302085 := bstep (se 4 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 17302085 = 3244141) B3244141
theorem B11534723 : Blo 2277435 11534723 := bstep (se 1 (by rfl) ⟨8651042, by rfl⟩ : syracuseStep 11534723 = 17302085) B17302085
theorem B7689815 : Blo 2277435 7689815 := bstep (se 1 (by rfl) ⟨5767361, by rfl⟩ : syracuseStep 7689815 = 11534723) B11534723
theorem B5126543 : Blo 2277435 5126543 := bstep (se 1 (by rfl) ⟨3844907, by rfl⟩ : syracuseStep 5126543 = 7689815) B7689815
theorem B3417695 : Blo 2277435 3417695 := bstep (se 1 (by rfl) ⟨2563271, by rfl⟩ : syracuseStep 3417695 = 5126543) B5126543
theorem B2278463 : Blo 2277435 2278463 := bstep (se 1 (by rfl) ⟨1708847, by rfl⟩ : syracuseStep 2278463 = 3417695) B3417695
theorem B3417701 : Blo 2277435 3417701 := bbase (se 4 (by rfl) ⟨320409, by rfl⟩ : syracuseStep 3417701 = 640819) (by norm_num)
theorem B2278467 : Blo 2277435 2278467 := bstep (se 1 (by rfl) ⟨1708850, by rfl⟩ : syracuseStep 2278467 = 3417701) B3417701
theorem B3699469 : Blo 2277435 3699469 := bbase (se 3 (by rfl) ⟨693650, by rfl⟩ : syracuseStep 3699469 = 1387301) (by norm_num)
theorem B4932625 : Blo 2277435 4932625 := bstep (se 2 (by rfl) ⟨1849734, by rfl⟩ : syracuseStep 4932625 = 3699469) B3699469
theorem B6576833 : Blo 2277435 6576833 := bstep (se 2 (by rfl) ⟨2466312, by rfl⟩ : syracuseStep 6576833 = 4932625) B4932625
theorem B17538221 : Blo 2277435 17538221 := bstep (se 3 (by rfl) ⟨3288416, by rfl⟩ : syracuseStep 17538221 = 6576833) B6576833
theorem B11692147 : Blo 2277435 11692147 := bstep (se 1 (by rfl) ⟨8769110, by rfl⟩ : syracuseStep 11692147 = 17538221) B17538221
theorem B15589529 : Blo 2277435 15589529 := bstep (se 2 (by rfl) ⟨5846073, by rfl⟩ : syracuseStep 15589529 = 11692147) B11692147
theorem B10393019 : Blo 2277435 10393019 := bstep (se 1 (by rfl) ⟨7794764, by rfl⟩ : syracuseStep 10393019 = 15589529) B15589529
theorem B6928679 : Blo 2277435 6928679 := bstep (se 1 (by rfl) ⟨5196509, by rfl⟩ : syracuseStep 6928679 = 10393019) B10393019
theorem B4619119 : Blo 2277435 4619119 := bstep (se 1 (by rfl) ⟨3464339, by rfl⟩ : syracuseStep 4619119 = 6928679) B6928679
theorem B6158825 : Blo 2277435 6158825 := bstep (se 2 (by rfl) ⟨2309559, by rfl⟩ : syracuseStep 6158825 = 4619119) B4619119
theorem B4105883 : Blo 2277435 4105883 := bstep (se 1 (by rfl) ⟨3079412, by rfl⟩ : syracuseStep 4105883 = 6158825) B6158825
theorem B2737255 : Blo 2277435 2737255 := bstep (se 1 (by rfl) ⟨2052941, by rfl⟩ : syracuseStep 2737255 = 4105883) B4105883
theorem B3649673 : Blo 2277435 3649673 := bstep (se 2 (by rfl) ⟨1368627, by rfl⟩ : syracuseStep 3649673 = 2737255) B2737255
theorem B2433115 : Blo 2277435 2433115 := bstep (se 1 (by rfl) ⟨1824836, by rfl⟩ : syracuseStep 2433115 = 3649673) B3649673
theorem B3244153 : Blo 2277435 3244153 := bstep (se 2 (by rfl) ⟨1216557, by rfl⟩ : syracuseStep 3244153 = 2433115) B2433115
theorem B4325537 : Blo 2277435 4325537 := bstep (se 2 (by rfl) ⟨1622076, by rfl⟩ : syracuseStep 4325537 = 3244153) B3244153
theorem B2883691 : Blo 2277435 2883691 := bstep (se 1 (by rfl) ⟨2162768, by rfl⟩ : syracuseStep 2883691 = 4325537) B4325537
theorem B3844921 : Blo 2277435 3844921 := bstep (se 2 (by rfl) ⟨1441845, by rfl⟩ : syracuseStep 3844921 = 2883691) B2883691
theorem B5126561 : Blo 2277435 5126561 := bstep (se 2 (by rfl) ⟨1922460, by rfl⟩ : syracuseStep 5126561 = 3844921) B3844921
theorem B3417707 : Blo 2277435 3417707 := bstep (se 1 (by rfl) ⟨2563280, by rfl⟩ : syracuseStep 3417707 = 5126561) B5126561
theorem B2278471 : Blo 2277435 2278471 := bstep (se 1 (by rfl) ⟨1708853, by rfl⟩ : syracuseStep 2278471 = 3417707) B3417707
theorem B2563285 : Blo 2277435 2563285 := bbase (se 7 (by rfl) ⟨30038, by rfl⟩ : syracuseStep 2563285 = 60077) (by norm_num)
theorem B3417713 : Blo 2277435 3417713 := bstep (se 2 (by rfl) ⟨1281642, by rfl⟩ : syracuseStep 3417713 = 2563285) B2563285
theorem B2278475 : Blo 2277435 2278475 := bstep (se 1 (by rfl) ⟨1708856, by rfl⟩ : syracuseStep 2278475 = 3417713) B3417713
theorem B2883701 : Blo 2277435 2883701 := bbase (se 5 (by rfl) ⟨135173, by rfl⟩ : syracuseStep 2883701 = 270347) (by norm_num)
theorem B7689869 : Blo 2277435 7689869 := bstep (se 3 (by rfl) ⟨1441850, by rfl⟩ : syracuseStep 7689869 = 2883701) B2883701
theorem B5126579 : Blo 2277435 5126579 := bstep (se 1 (by rfl) ⟨3844934, by rfl⟩ : syracuseStep 5126579 = 7689869) B7689869
theorem B3417719 : Blo 2277435 3417719 := bstep (se 1 (by rfl) ⟨2563289, by rfl⟩ : syracuseStep 3417719 = 5126579) B5126579
theorem B2278479 : Blo 2277435 2278479 := bstep (se 1 (by rfl) ⟨1708859, by rfl⟩ : syracuseStep 2278479 = 3417719) B3417719
theorem B3417725 : Blo 2277435 3417725 := bbase (se 3 (by rfl) ⟨640823, by rfl⟩ : syracuseStep 3417725 = 1281647) (by norm_num)
theorem B2278483 : Blo 2277435 2278483 := bstep (se 1 (by rfl) ⟨1708862, by rfl⟩ : syracuseStep 2278483 = 3417725) B3417725
theorem B5126597 : Blo 2277435 5126597 := bbase (se 4 (by rfl) ⟨480618, by rfl⟩ : syracuseStep 5126597 = 961237) (by norm_num)
theorem B3417731 : Blo 2277435 3417731 := bstep (se 1 (by rfl) ⟨2563298, by rfl⟩ : syracuseStep 3417731 = 5126597) B5126597
theorem B2278487 : Blo 2277435 2278487 := bstep (se 1 (by rfl) ⟨1708865, by rfl⟩ : syracuseStep 2278487 = 3417731) B3417731
theorem B5474557 : Blo 2277435 5474557 := bbase (se 3 (by rfl) ⟨1026479, by rfl⟩ : syracuseStep 5474557 = 2052959) (by norm_num)
theorem B7299409 : Blo 2277435 7299409 := bstep (se 2 (by rfl) ⟨2737278, by rfl⟩ : syracuseStep 7299409 = 5474557) B5474557
theorem B9732545 : Blo 2277435 9732545 := bstep (se 2 (by rfl) ⟨3649704, by rfl⟩ : syracuseStep 9732545 = 7299409) B7299409
theorem B6488363 : Blo 2277435 6488363 := bstep (se 1 (by rfl) ⟨4866272, by rfl⟩ : syracuseStep 6488363 = 9732545) B9732545
theorem B4325575 : Blo 2277435 4325575 := bstep (se 1 (by rfl) ⟨3244181, by rfl⟩ : syracuseStep 4325575 = 6488363) B6488363
theorem B5767433 : Blo 2277435 5767433 := bstep (se 2 (by rfl) ⟨2162787, by rfl⟩ : syracuseStep 5767433 = 4325575) B4325575
theorem B3844955 : Blo 2277435 3844955 := bstep (se 1 (by rfl) ⟨2883716, by rfl⟩ : syracuseStep 3844955 = 5767433) B5767433
theorem B2563303 : Blo 2277435 2563303 := bstep (se 1 (by rfl) ⟨1922477, by rfl⟩ : syracuseStep 2563303 = 3844955) B3844955
theorem B3417737 : Blo 2277435 3417737 := bstep (se 2 (by rfl) ⟨1281651, by rfl⟩ : syracuseStep 3417737 = 2563303) B2563303
theorem B2278491 : Blo 2277435 2278491 := bstep (se 1 (by rfl) ⟨1708868, by rfl⟩ : syracuseStep 2278491 = 3417737) B3417737
theorem B11534885 : Blo 2277435 11534885 := bbase (se 4 (by rfl) ⟨1081395, by rfl⟩ : syracuseStep 11534885 = 2162791) (by norm_num)
theorem B7689923 : Blo 2277435 7689923 := bstep (se 1 (by rfl) ⟨5767442, by rfl⟩ : syracuseStep 7689923 = 11534885) B11534885
theorem B5126615 : Blo 2277435 5126615 := bstep (se 1 (by rfl) ⟨3844961, by rfl⟩ : syracuseStep 5126615 = 7689923) B7689923
theorem B3417743 : Blo 2277435 3417743 := bstep (se 1 (by rfl) ⟨2563307, by rfl⟩ : syracuseStep 3417743 = 5126615) B5126615
theorem B2278495 : Blo 2277435 2278495 := bstep (se 1 (by rfl) ⟨1708871, by rfl⟩ : syracuseStep 2278495 = 3417743) B3417743
theorem B3417749 : Blo 2277435 3417749 := bbase (se 6 (by rfl) ⟨80103, by rfl⟩ : syracuseStep 3417749 = 160207) (by norm_num)
theorem B2278499 : Blo 2277435 2278499 := bstep (se 1 (by rfl) ⟨1708874, by rfl⟩ : syracuseStep 2278499 = 3417749) B3417749
theorem B5196581 : Blo 2277435 5196581 := bbase (se 4 (by rfl) ⟨487179, by rfl⟩ : syracuseStep 5196581 = 974359) (by norm_num)
theorem B3464387 : Blo 2277435 3464387 := bstep (se 1 (by rfl) ⟨2598290, by rfl⟩ : syracuseStep 3464387 = 5196581) B5196581
theorem B2309591 : Blo 2277435 2309591 := bstep (se 1 (by rfl) ⟨1732193, by rfl⟩ : syracuseStep 2309591 = 3464387) B3464387
theorem B6158909 : Blo 2277435 6158909 := bstep (se 3 (by rfl) ⟨1154795, by rfl⟩ : syracuseStep 6158909 = 2309591) B2309591
theorem B4105939 : Blo 2277435 4105939 := bstep (se 1 (by rfl) ⟨3079454, by rfl⟩ : syracuseStep 4105939 = 6158909) B6158909
theorem B5474585 : Blo 2277435 5474585 := bstep (se 2 (by rfl) ⟨2052969, by rfl⟩ : syracuseStep 5474585 = 4105939) B4105939
theorem B14598893 : Blo 2277435 14598893 := bstep (se 3 (by rfl) ⟨2737292, by rfl⟩ : syracuseStep 14598893 = 5474585) B5474585
theorem B9732595 : Blo 2277435 9732595 := bstep (se 1 (by rfl) ⟨7299446, by rfl⟩ : syracuseStep 9732595 = 14598893) B14598893
theorem B12976793 : Blo 2277435 12976793 := bstep (se 2 (by rfl) ⟨4866297, by rfl⟩ : syracuseStep 12976793 = 9732595) B9732595
theorem B8651195 : Blo 2277435 8651195 := bstep (se 1 (by rfl) ⟨6488396, by rfl⟩ : syracuseStep 8651195 = 12976793) B12976793
theorem B5767463 : Blo 2277435 5767463 := bstep (se 1 (by rfl) ⟨4325597, by rfl⟩ : syracuseStep 5767463 = 8651195) B8651195
theorem B3844975 : Blo 2277435 3844975 := bstep (se 1 (by rfl) ⟨2883731, by rfl⟩ : syracuseStep 3844975 = 5767463) B5767463
theorem B5126633 : Blo 2277435 5126633 := bstep (se 2 (by rfl) ⟨1922487, by rfl⟩ : syracuseStep 5126633 = 3844975) B3844975
theorem B3417755 : Blo 2277435 3417755 := bstep (se 1 (by rfl) ⟨2563316, by rfl⟩ : syracuseStep 3417755 = 5126633) B5126633
theorem B2278503 : Blo 2277435 2278503 := bstep (se 1 (by rfl) ⟨1708877, by rfl⟩ : syracuseStep 2278503 = 3417755) B3417755
theorem B2563321 : Blo 2277435 2563321 := bbase (se 2 (by rfl) ⟨961245, by rfl⟩ : syracuseStep 2563321 = 1922491) (by norm_num)
theorem B3417761 : Blo 2277435 3417761 := bstep (se 2 (by rfl) ⟨1281660, by rfl⟩ : syracuseStep 3417761 = 2563321) B2563321
theorem B2278507 : Blo 2277435 2278507 := bstep (se 1 (by rfl) ⟨1708880, by rfl⟩ : syracuseStep 2278507 = 3417761) B3417761
theorem B9732629 : Blo 2277435 9732629 := bbase (se 6 (by rfl) ⟨228108, by rfl⟩ : syracuseStep 9732629 = 456217) (by norm_num)
theorem B6488419 : Blo 2277435 6488419 := bstep (se 1 (by rfl) ⟨4866314, by rfl⟩ : syracuseStep 6488419 = 9732629) B9732629
theorem B8651225 : Blo 2277435 8651225 := bstep (se 2 (by rfl) ⟨3244209, by rfl⟩ : syracuseStep 8651225 = 6488419) B6488419
theorem B5767483 : Blo 2277435 5767483 := bstep (se 1 (by rfl) ⟨4325612, by rfl⟩ : syracuseStep 5767483 = 8651225) B8651225
theorem B7689977 : Blo 2277435 7689977 := bstep (se 2 (by rfl) ⟨2883741, by rfl⟩ : syracuseStep 7689977 = 5767483) B5767483
theorem B5126651 : Blo 2277435 5126651 := bstep (se 1 (by rfl) ⟨3844988, by rfl⟩ : syracuseStep 5126651 = 7689977) B7689977
theorem B3417767 : Blo 2277435 3417767 := bstep (se 1 (by rfl) ⟨2563325, by rfl⟩ : syracuseStep 3417767 = 5126651) B5126651
theorem B2278511 : Blo 2277435 2278511 := bstep (se 1 (by rfl) ⟨1708883, by rfl⟩ : syracuseStep 2278511 = 3417767) B3417767
theorem B3417773 : Blo 2277435 3417773 := bbase (se 3 (by rfl) ⟨640832, by rfl⟩ : syracuseStep 3417773 = 1281665) (by norm_num)
theorem B2278515 : Blo 2277435 2278515 := bstep (se 1 (by rfl) ⟨1708886, by rfl⟩ : syracuseStep 2278515 = 3417773) B3417773
theorem B5126669 : Blo 2277435 5126669 := bbase (se 3 (by rfl) ⟨961250, by rfl⟩ : syracuseStep 5126669 = 1922501) (by norm_num)
theorem B3417779 : Blo 2277435 3417779 := bstep (se 1 (by rfl) ⟨2563334, by rfl⟩ : syracuseStep 3417779 = 5126669) B5126669
theorem B2278519 : Blo 2277435 2278519 := bstep (se 1 (by rfl) ⟨1708889, by rfl⟩ : syracuseStep 2278519 = 3417779) B3417779
theorem B2883757 : Blo 2277435 2883757 := bbase (se 3 (by rfl) ⟨540704, by rfl⟩ : syracuseStep 2883757 = 1081409) (by norm_num)
theorem B3845009 : Blo 2277435 3845009 := bstep (se 2 (by rfl) ⟨1441878, by rfl⟩ : syracuseStep 3845009 = 2883757) B2883757
theorem B2563339 : Blo 2277435 2563339 := bstep (se 1 (by rfl) ⟨1922504, by rfl⟩ : syracuseStep 2563339 = 3845009) B3845009
theorem B3417785 : Blo 2277435 3417785 := bstep (se 2 (by rfl) ⟨1281669, by rfl⟩ : syracuseStep 3417785 = 2563339) B2563339
theorem B2278523 : Blo 2277435 2278523 := bstep (se 1 (by rfl) ⟨1708892, by rfl⟩ : syracuseStep 2278523 = 3417785) B3417785
theorem B2737321 : Blo 2277435 2737321 := bbase (se 2 (by rfl) ⟨1026495, by rfl⟩ : syracuseStep 2737321 = 2052991) (by norm_num)
theorem B14599045 : Blo 2277435 14599045 := bstep (se 4 (by rfl) ⟨1368660, by rfl⟩ : syracuseStep 14599045 = 2737321) B2737321
theorem B19465393 : Blo 2277435 19465393 := bstep (se 2 (by rfl) ⟨7299522, by rfl⟩ : syracuseStep 19465393 = 14599045) B14599045
theorem B25953857 : Blo 2277435 25953857 := bstep (se 2 (by rfl) ⟨9732696, by rfl⟩ : syracuseStep 25953857 = 19465393) B19465393
theorem B17302571 : Blo 2277435 17302571 := bstep (se 1 (by rfl) ⟨12976928, by rfl⟩ : syracuseStep 17302571 = 25953857) B25953857
theorem B11535047 : Blo 2277435 11535047 := bstep (se 1 (by rfl) ⟨8651285, by rfl⟩ : syracuseStep 11535047 = 17302571) B17302571
theorem B7690031 : Blo 2277435 7690031 := bstep (se 1 (by rfl) ⟨5767523, by rfl⟩ : syracuseStep 7690031 = 11535047) B11535047
theorem B5126687 : Blo 2277435 5126687 := bstep (se 1 (by rfl) ⟨3845015, by rfl⟩ : syracuseStep 5126687 = 7690031) B7690031
theorem B3417791 : Blo 2277435 3417791 := bstep (se 1 (by rfl) ⟨2563343, by rfl⟩ : syracuseStep 3417791 = 5126687) B5126687
theorem B2278527 : Blo 2277435 2278527 := bstep (se 1 (by rfl) ⟨1708895, by rfl⟩ : syracuseStep 2278527 = 3417791) B3417791
theorem B3417797 : Blo 2277435 3417797 := bbase (se 4 (by rfl) ⟨320418, by rfl⟩ : syracuseStep 3417797 = 640837) (by norm_num)
theorem B2278531 : Blo 2277435 2278531 := bstep (se 1 (by rfl) ⟨1708898, by rfl⟩ : syracuseStep 2278531 = 3417797) B3417797
theorem B3845029 : Blo 2277435 3845029 := bbase (se 4 (by rfl) ⟨360471, by rfl⟩ : syracuseStep 3845029 = 720943) (by norm_num)
theorem B5126705 : Blo 2277435 5126705 := bstep (se 2 (by rfl) ⟨1922514, by rfl⟩ : syracuseStep 5126705 = 3845029) B3845029
theorem B3417803 : Blo 2277435 3417803 := bstep (se 1 (by rfl) ⟨2563352, by rfl⟩ : syracuseStep 3417803 = 5126705) B5126705
theorem B2278535 : Blo 2277435 2278535 := bstep (se 1 (by rfl) ⟨1708901, by rfl⟩ : syracuseStep 2278535 = 3417803) B3417803
theorem B2563357 : Blo 2277435 2563357 := bbase (se 3 (by rfl) ⟨480629, by rfl⟩ : syracuseStep 2563357 = 961259) (by norm_num)
theorem B3417809 : Blo 2277435 3417809 := bstep (se 2 (by rfl) ⟨1281678, by rfl⟩ : syracuseStep 3417809 = 2563357) B2563357
theorem B2278539 : Blo 2277435 2278539 := bstep (se 1 (by rfl) ⟨1708904, by rfl⟩ : syracuseStep 2278539 = 3417809) B3417809
theorem B7690085 : Blo 2277435 7690085 := bbase (se 4 (by rfl) ⟨720945, by rfl⟩ : syracuseStep 7690085 = 1441891) (by norm_num)
theorem B5126723 : Blo 2277435 5126723 := bstep (se 1 (by rfl) ⟨3845042, by rfl⟩ : syracuseStep 5126723 = 7690085) B7690085
theorem B3417815 : Blo 2277435 3417815 := bstep (se 1 (by rfl) ⟨2563361, by rfl⟩ : syracuseStep 3417815 = 5126723) B5126723
theorem B2278543 : Blo 2277435 2278543 := bstep (se 1 (by rfl) ⟨1708907, by rfl⟩ : syracuseStep 2278543 = 3417815) B3417815
theorem B3417821 : Blo 2277435 3417821 := bbase (se 3 (by rfl) ⟨640841, by rfl⟩ : syracuseStep 3417821 = 1281683) (by norm_num)
theorem B2278547 : Blo 2277435 2278547 := bstep (se 1 (by rfl) ⟨1708910, by rfl⟩ : syracuseStep 2278547 = 3417821) B3417821
theorem B5126741 : Blo 2277435 5126741 := bbase (se 8 (by rfl) ⟨30039, by rfl⟩ : syracuseStep 5126741 = 60079) (by norm_num)
theorem B3417827 : Blo 2277435 3417827 := bstep (se 1 (by rfl) ⟨2563370, by rfl⟩ : syracuseStep 3417827 = 5126741) B5126741
theorem B2278551 : Blo 2277435 2278551 := bstep (se 1 (by rfl) ⟨1708913, by rfl⟩ : syracuseStep 2278551 = 3417827) B3417827
theorem B12318101 : Blo 2277435 12318101 := bbase (se 6 (by rfl) ⟨288705, by rfl⟩ : syracuseStep 12318101 = 577411) (by norm_num)
theorem B8212067 : Blo 2277435 8212067 := bstep (se 1 (by rfl) ⟨6159050, by rfl⟩ : syracuseStep 8212067 = 12318101) B12318101
theorem B5474711 : Blo 2277435 5474711 := bstep (se 1 (by rfl) ⟨4106033, by rfl⟩ : syracuseStep 5474711 = 8212067) B8212067
theorem B3649807 : Blo 2277435 3649807 := bstep (se 1 (by rfl) ⟨2737355, by rfl⟩ : syracuseStep 3649807 = 5474711) B5474711
theorem B4866409 : Blo 2277435 4866409 := bstep (se 2 (by rfl) ⟨1824903, by rfl⟩ : syracuseStep 4866409 = 3649807) B3649807
theorem B6488545 : Blo 2277435 6488545 := bstep (se 2 (by rfl) ⟨2433204, by rfl⟩ : syracuseStep 6488545 = 4866409) B4866409
theorem B8651393 : Blo 2277435 8651393 := bstep (se 2 (by rfl) ⟨3244272, by rfl⟩ : syracuseStep 8651393 = 6488545) B6488545
theorem B5767595 : Blo 2277435 5767595 := bstep (se 1 (by rfl) ⟨4325696, by rfl⟩ : syracuseStep 5767595 = 8651393) B8651393
theorem B3845063 : Blo 2277435 3845063 := bstep (se 1 (by rfl) ⟨2883797, by rfl⟩ : syracuseStep 3845063 = 5767595) B5767595
theorem B2563375 : Blo 2277435 2563375 := bstep (se 1 (by rfl) ⟨1922531, by rfl⟩ : syracuseStep 2563375 = 3845063) B3845063
theorem B3417833 : Blo 2277435 3417833 := bstep (se 2 (by rfl) ⟨1281687, by rfl⟩ : syracuseStep 3417833 = 2563375) B2563375
theorem B2278555 : Blo 2277435 2278555 := bstep (se 1 (by rfl) ⟨1708916, by rfl⟩ : syracuseStep 2278555 = 3417833) B3417833
theorem B13154165 : Blo 2277435 13154165 := bbase (se 5 (by rfl) ⟨616601, by rfl⟩ : syracuseStep 13154165 = 1233203) (by norm_num)
theorem B8769443 : Blo 2277435 8769443 := bstep (se 1 (by rfl) ⟨6577082, by rfl⟩ : syracuseStep 8769443 = 13154165) B13154165
theorem B23385181 : Blo 2277435 23385181 := bstep (se 3 (by rfl) ⟨4384721, by rfl⟩ : syracuseStep 23385181 = 8769443) B8769443
theorem B31180241 : Blo 2277435 31180241 := bstep (se 2 (by rfl) ⟨11692590, by rfl⟩ : syracuseStep 31180241 = 23385181) B23385181
theorem B20786827 : Blo 2277435 20786827 := bstep (se 1 (by rfl) ⟨15590120, by rfl⟩ : syracuseStep 20786827 = 31180241) B31180241
theorem B27715769 : Blo 2277435 27715769 := bstep (se 2 (by rfl) ⟨10393413, by rfl⟩ : syracuseStep 27715769 = 20786827) B20786827
theorem B18477179 : Blo 2277435 18477179 := bstep (se 1 (by rfl) ⟨13857884, by rfl⟩ : syracuseStep 18477179 = 27715769) B27715769
theorem B12318119 : Blo 2277435 12318119 := bstep (se 1 (by rfl) ⟨9238589, by rfl⟩ : syracuseStep 12318119 = 18477179) B18477179
theorem B8212079 : Blo 2277435 8212079 := bstep (se 1 (by rfl) ⟨6159059, by rfl⟩ : syracuseStep 8212079 = 12318119) B12318119
theorem B5474719 : Blo 2277435 5474719 := bstep (se 1 (by rfl) ⟨4106039, by rfl⟩ : syracuseStep 5474719 = 8212079) B8212079
theorem B29198501 : Blo 2277435 29198501 := bstep (se 4 (by rfl) ⟨2737359, by rfl⟩ : syracuseStep 29198501 = 5474719) B5474719
theorem B19465667 : Blo 2277435 19465667 := bstep (se 1 (by rfl) ⟨14599250, by rfl⟩ : syracuseStep 19465667 = 29198501) B29198501
theorem B12977111 : Blo 2277435 12977111 := bstep (se 1 (by rfl) ⟨9732833, by rfl⟩ : syracuseStep 12977111 = 19465667) B19465667
theorem B8651407 : Blo 2277435 8651407 := bstep (se 1 (by rfl) ⟨6488555, by rfl⟩ : syracuseStep 8651407 = 12977111) B12977111
theorem B11535209 : Blo 2277435 11535209 := bstep (se 2 (by rfl) ⟨4325703, by rfl⟩ : syracuseStep 11535209 = 8651407) B8651407
theorem B7690139 : Blo 2277435 7690139 := bstep (se 1 (by rfl) ⟨5767604, by rfl⟩ : syracuseStep 7690139 = 11535209) B11535209
theorem B5126759 : Blo 2277435 5126759 := bstep (se 1 (by rfl) ⟨3845069, by rfl⟩ : syracuseStep 5126759 = 7690139) B7690139
theorem B3417839 : Blo 2277435 3417839 := bstep (se 1 (by rfl) ⟨2563379, by rfl⟩ : syracuseStep 3417839 = 5126759) B5126759
theorem B2278559 : Blo 2277435 2278559 := bstep (se 1 (by rfl) ⟨1708919, by rfl⟩ : syracuseStep 2278559 = 3417839) B3417839
theorem B3417845 : Blo 2277435 3417845 := bbase (se 5 (by rfl) ⟨160211, by rfl⟩ : syracuseStep 3417845 = 320423) (by norm_num)
theorem B2278563 : Blo 2277435 2278563 := bstep (se 1 (by rfl) ⟨1708922, by rfl⟩ : syracuseStep 2278563 = 3417845) B3417845
theorem B9732869 : Blo 2277435 9732869 := bbase (se 4 (by rfl) ⟨912456, by rfl⟩ : syracuseStep 9732869 = 1824913) (by norm_num)
theorem B6488579 : Blo 2277435 6488579 := bstep (se 1 (by rfl) ⟨4866434, by rfl⟩ : syracuseStep 6488579 = 9732869) B9732869
theorem B4325719 : Blo 2277435 4325719 := bstep (se 1 (by rfl) ⟨3244289, by rfl⟩ : syracuseStep 4325719 = 6488579) B6488579
theorem B5767625 : Blo 2277435 5767625 := bstep (se 2 (by rfl) ⟨2162859, by rfl⟩ : syracuseStep 5767625 = 4325719) B4325719
theorem B3845083 : Blo 2277435 3845083 := bstep (se 1 (by rfl) ⟨2883812, by rfl⟩ : syracuseStep 3845083 = 5767625) B5767625
theorem B5126777 : Blo 2277435 5126777 := bstep (se 2 (by rfl) ⟨1922541, by rfl⟩ : syracuseStep 5126777 = 3845083) B3845083
theorem B3417851 : Blo 2277435 3417851 := bstep (se 1 (by rfl) ⟨2563388, by rfl⟩ : syracuseStep 3417851 = 5126777) B5126777
theorem B2278567 : Blo 2277435 2278567 := bstep (se 1 (by rfl) ⟨1708925, by rfl⟩ : syracuseStep 2278567 = 3417851) B3417851
theorem B2563393 : Blo 2277435 2563393 := bbase (se 2 (by rfl) ⟨961272, by rfl⟩ : syracuseStep 2563393 = 1922545) (by norm_num)
theorem B3417857 : Blo 2277435 3417857 := bstep (se 2 (by rfl) ⟨1281696, by rfl⟩ : syracuseStep 3417857 = 2563393) B2563393
theorem B2278571 : Blo 2277435 2278571 := bstep (se 1 (by rfl) ⟨1708928, by rfl⟩ : syracuseStep 2278571 = 3417857) B3417857
theorem B5767645 : Blo 2277435 5767645 := bbase (se 3 (by rfl) ⟨1081433, by rfl⟩ : syracuseStep 5767645 = 2162867) (by norm_num)
theorem B7690193 : Blo 2277435 7690193 := bstep (se 2 (by rfl) ⟨2883822, by rfl⟩ : syracuseStep 7690193 = 5767645) B5767645
theorem B5126795 : Blo 2277435 5126795 := bstep (se 1 (by rfl) ⟨3845096, by rfl⟩ : syracuseStep 5126795 = 7690193) B7690193
theorem B3417863 : Blo 2277435 3417863 := bstep (se 1 (by rfl) ⟨2563397, by rfl⟩ : syracuseStep 3417863 = 5126795) B5126795
theorem B2278575 : Blo 2277435 2278575 := bstep (se 1 (by rfl) ⟨1708931, by rfl⟩ : syracuseStep 2278575 = 3417863) B3417863
theorem B3417869 : Blo 2277435 3417869 := bbase (se 3 (by rfl) ⟨640850, by rfl⟩ : syracuseStep 3417869 = 1281701) (by norm_num)
theorem B2278579 : Blo 2277435 2278579 := bstep (se 1 (by rfl) ⟨1708934, by rfl⟩ : syracuseStep 2278579 = 3417869) B3417869
theorem B5126813 : Blo 2277435 5126813 := bbase (se 3 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 5126813 = 1922555) (by norm_num)
theorem B3417875 : Blo 2277435 3417875 := bstep (se 1 (by rfl) ⟨2563406, by rfl⟩ : syracuseStep 3417875 = 5126813) B5126813
theorem B2278583 : Blo 2277435 2278583 := bstep (se 1 (by rfl) ⟨1708937, by rfl⟩ : syracuseStep 2278583 = 3417875) B3417875
theorem B3845117 : Blo 2277435 3845117 := bbase (se 3 (by rfl) ⟨720959, by rfl⟩ : syracuseStep 3845117 = 1441919) (by norm_num)
theorem B2563411 : Blo 2277435 2563411 := bstep (se 1 (by rfl) ⟨1922558, by rfl⟩ : syracuseStep 2563411 = 3845117) B3845117
theorem B3417881 : Blo 2277435 3417881 := bstep (se 2 (by rfl) ⟨1281705, by rfl⟩ : syracuseStep 3417881 = 2563411) B2563411
theorem B2278587 : Blo 2277435 2278587 := bstep (se 1 (by rfl) ⟨1708940, by rfl⟩ : syracuseStep 2278587 = 3417881) B3417881
theorem B4866485 : Blo 2277435 4866485 := bbase (se 5 (by rfl) ⟨228116, by rfl⟩ : syracuseStep 4866485 = 456233) (by norm_num)
theorem B12977293 : Blo 2277435 12977293 := bstep (se 3 (by rfl) ⟨2433242, by rfl⟩ : syracuseStep 12977293 = 4866485) B4866485
theorem B17303057 : Blo 2277435 17303057 := bstep (se 2 (by rfl) ⟨6488646, by rfl⟩ : syracuseStep 17303057 = 12977293) B12977293
theorem B11535371 : Blo 2277435 11535371 := bstep (se 1 (by rfl) ⟨8651528, by rfl⟩ : syracuseStep 11535371 = 17303057) B17303057
theorem B7690247 : Blo 2277435 7690247 := bstep (se 1 (by rfl) ⟨5767685, by rfl⟩ : syracuseStep 7690247 = 11535371) B11535371
theorem B5126831 : Blo 2277435 5126831 := bstep (se 1 (by rfl) ⟨3845123, by rfl⟩ : syracuseStep 5126831 = 7690247) B7690247
theorem B3417887 : Blo 2277435 3417887 := bstep (se 1 (by rfl) ⟨2563415, by rfl⟩ : syracuseStep 3417887 = 5126831) B5126831
theorem B2278591 : Blo 2277435 2278591 := bstep (se 1 (by rfl) ⟨1708943, by rfl⟩ : syracuseStep 2278591 = 3417887) B3417887
theorem B3417893 : Blo 2277435 3417893 := bbase (se 4 (by rfl) ⟨320427, by rfl⟩ : syracuseStep 3417893 = 640855) (by norm_num)
theorem B2278595 : Blo 2277435 2278595 := bstep (se 1 (by rfl) ⟨1708946, by rfl⟩ : syracuseStep 2278595 = 3417893) B3417893
theorem B2883853 : Blo 2277435 2883853 := bbase (se 3 (by rfl) ⟨540722, by rfl⟩ : syracuseStep 2883853 = 1081445) (by norm_num)
theorem B3845137 : Blo 2277435 3845137 := bstep (se 2 (by rfl) ⟨1441926, by rfl⟩ : syracuseStep 3845137 = 2883853) B2883853
theorem B5126849 : Blo 2277435 5126849 := bstep (se 2 (by rfl) ⟨1922568, by rfl⟩ : syracuseStep 5126849 = 3845137) B3845137
theorem B3417899 : Blo 2277435 3417899 := bstep (se 1 (by rfl) ⟨2563424, by rfl⟩ : syracuseStep 3417899 = 5126849) B5126849
theorem B2278599 : Blo 2277435 2278599 := bstep (se 1 (by rfl) ⟨1708949, by rfl⟩ : syracuseStep 2278599 = 3417899) B3417899
theorem B2563429 : Blo 2277435 2563429 := bbase (se 4 (by rfl) ⟨240321, by rfl⟩ : syracuseStep 2563429 = 480643) (by norm_num)
theorem B3417905 : Blo 2277435 3417905 := bstep (se 2 (by rfl) ⟨1281714, by rfl⟩ : syracuseStep 3417905 = 2563429) B2563429
theorem B2278603 : Blo 2277435 2278603 := bstep (se 1 (by rfl) ⟨1708952, by rfl⟩ : syracuseStep 2278603 = 3417905) B3417905
theorem B6488693 : Blo 2277435 6488693 := bbase (se 5 (by rfl) ⟨304157, by rfl⟩ : syracuseStep 6488693 = 608315) (by norm_num)
theorem B4325795 : Blo 2277435 4325795 := bstep (se 1 (by rfl) ⟨3244346, by rfl⟩ : syracuseStep 4325795 = 6488693) B6488693
theorem B2883863 : Blo 2277435 2883863 := bstep (se 1 (by rfl) ⟨2162897, by rfl⟩ : syracuseStep 2883863 = 4325795) B4325795
theorem B7690301 : Blo 2277435 7690301 := bstep (se 3 (by rfl) ⟨1441931, by rfl⟩ : syracuseStep 7690301 = 2883863) B2883863
theorem B5126867 : Blo 2277435 5126867 := bstep (se 1 (by rfl) ⟨3845150, by rfl⟩ : syracuseStep 5126867 = 7690301) B7690301
theorem B3417911 : Blo 2277435 3417911 := bstep (se 1 (by rfl) ⟨2563433, by rfl⟩ : syracuseStep 3417911 = 5126867) B5126867
theorem B2278607 : Blo 2277435 2278607 := bstep (se 1 (by rfl) ⟨1708955, by rfl⟩ : syracuseStep 2278607 = 3417911) B3417911
theorem B3417917 : Blo 2277435 3417917 := bbase (se 3 (by rfl) ⟨640859, by rfl⟩ : syracuseStep 3417917 = 1281719) (by norm_num)
theorem B2278611 : Blo 2277435 2278611 := bstep (se 1 (by rfl) ⟨1708958, by rfl⟩ : syracuseStep 2278611 = 3417917) B3417917
theorem B5126885 : Blo 2277435 5126885 := bbase (se 4 (by rfl) ⟨480645, by rfl⟩ : syracuseStep 5126885 = 961291) (by norm_num)
theorem B3417923 : Blo 2277435 3417923 := bstep (se 1 (by rfl) ⟨2563442, by rfl⟩ : syracuseStep 3417923 = 5126885) B5126885
theorem B2278615 : Blo 2277435 2278615 := bstep (se 1 (by rfl) ⟨1708961, by rfl⟩ : syracuseStep 2278615 = 3417923) B3417923
theorem B5767757 : Blo 2277435 5767757 := bbase (se 3 (by rfl) ⟨1081454, by rfl⟩ : syracuseStep 5767757 = 2162909) (by norm_num)
theorem B3845171 : Blo 2277435 3845171 := bstep (se 1 (by rfl) ⟨2883878, by rfl⟩ : syracuseStep 3845171 = 5767757) B5767757
theorem B2563447 : Blo 2277435 2563447 := bstep (se 1 (by rfl) ⟨1922585, by rfl⟩ : syracuseStep 2563447 = 3845171) B3845171
theorem B3417929 : Blo 2277435 3417929 := bstep (se 2 (by rfl) ⟨1281723, by rfl⟩ : syracuseStep 3417929 = 2563447) B2563447
theorem B2278619 : Blo 2277435 2278619 := bstep (se 1 (by rfl) ⟨1708964, by rfl⟩ : syracuseStep 2278619 = 3417929) B3417929
theorem B2433277 : Blo 2277435 2433277 := bbase (se 3 (by rfl) ⟨456239, by rfl⟩ : syracuseStep 2433277 = 912479) (by norm_num)
theorem B3244369 : Blo 2277435 3244369 := bstep (se 2 (by rfl) ⟨1216638, by rfl⟩ : syracuseStep 3244369 = 2433277) B2433277
theorem B4325825 : Blo 2277435 4325825 := bstep (se 2 (by rfl) ⟨1622184, by rfl⟩ : syracuseStep 4325825 = 3244369) B3244369
theorem B11535533 : Blo 2277435 11535533 := bstep (se 3 (by rfl) ⟨2162912, by rfl⟩ : syracuseStep 11535533 = 4325825) B4325825
theorem B7690355 : Blo 2277435 7690355 := bstep (se 1 (by rfl) ⟨5767766, by rfl⟩ : syracuseStep 7690355 = 11535533) B11535533
theorem B5126903 : Blo 2277435 5126903 := bstep (se 1 (by rfl) ⟨3845177, by rfl⟩ : syracuseStep 5126903 = 7690355) B7690355
theorem B3417935 : Blo 2277435 3417935 := bstep (se 1 (by rfl) ⟨2563451, by rfl⟩ : syracuseStep 3417935 = 5126903) B5126903
theorem B2278623 : Blo 2277435 2278623 := bstep (se 1 (by rfl) ⟨1708967, by rfl⟩ : syracuseStep 2278623 = 3417935) B3417935
theorem B3417941 : Blo 2277435 3417941 := bbase (se 9 (by rfl) ⟨10013, by rfl⟩ : syracuseStep 3417941 = 20027) (by norm_num)
theorem B2278627 : Blo 2277435 2278627 := bstep (se 1 (by rfl) ⟨1708970, by rfl⟩ : syracuseStep 2278627 = 3417941) B3417941
theorem B5474893 : Blo 2277435 5474893 := bbase (se 3 (by rfl) ⟨1026542, by rfl⟩ : syracuseStep 5474893 = 2053085) (by norm_num)
theorem B7299857 : Blo 2277435 7299857 := bstep (se 2 (by rfl) ⟨2737446, by rfl⟩ : syracuseStep 7299857 = 5474893) B5474893
theorem B4866571 : Blo 2277435 4866571 := bstep (se 1 (by rfl) ⟨3649928, by rfl⟩ : syracuseStep 4866571 = 7299857) B7299857
theorem B6488761 : Blo 2277435 6488761 := bstep (se 2 (by rfl) ⟨2433285, by rfl⟩ : syracuseStep 6488761 = 4866571) B4866571
theorem B8651681 : Blo 2277435 8651681 := bstep (se 2 (by rfl) ⟨3244380, by rfl⟩ : syracuseStep 8651681 = 6488761) B6488761
theorem B5767787 : Blo 2277435 5767787 := bstep (se 1 (by rfl) ⟨4325840, by rfl⟩ : syracuseStep 5767787 = 8651681) B8651681
theorem B3845191 : Blo 2277435 3845191 := bstep (se 1 (by rfl) ⟨2883893, by rfl⟩ : syracuseStep 3845191 = 5767787) B5767787
theorem B5126921 : Blo 2277435 5126921 := bstep (se 2 (by rfl) ⟨1922595, by rfl⟩ : syracuseStep 5126921 = 3845191) B3845191
theorem B3417947 : Blo 2277435 3417947 := bstep (se 1 (by rfl) ⟨2563460, by rfl⟩ : syracuseStep 3417947 = 5126921) B5126921
theorem B2278631 : Blo 2277435 2278631 := bstep (se 1 (by rfl) ⟨1708973, by rfl⟩ : syracuseStep 2278631 = 3417947) B3417947
theorem B2563465 : Blo 2277435 2563465 := bbase (se 2 (by rfl) ⟨961299, by rfl⟩ : syracuseStep 2563465 = 1922599) (by norm_num)
theorem B3417953 : Blo 2277435 3417953 := bstep (se 2 (by rfl) ⟨1281732, by rfl⟩ : syracuseStep 3417953 = 2563465) B2563465
theorem B2278635 : Blo 2277435 2278635 := bstep (se 1 (by rfl) ⟨1708976, by rfl⟩ : syracuseStep 2278635 = 3417953) B3417953
theorem B14047445 : Blo 2277435 14047445 := bbase (se 7 (by rfl) ⟨164618, by rfl⟩ : syracuseStep 14047445 = 329237) (by norm_num)
theorem B37459853 : Blo 2277435 37459853 := bstep (se 3 (by rfl) ⟨7023722, by rfl⟩ : syracuseStep 37459853 = 14047445) B14047445
theorem B24973235 : Blo 2277435 24973235 := bstep (se 1 (by rfl) ⟨18729926, by rfl⟩ : syracuseStep 24973235 = 37459853) B37459853
theorem B16648823 : Blo 2277435 16648823 := bstep (se 1 (by rfl) ⟨12486617, by rfl⟩ : syracuseStep 16648823 = 24973235) B24973235
theorem B11099215 : Blo 2277435 11099215 := bstep (se 1 (by rfl) ⟨8324411, by rfl⟩ : syracuseStep 11099215 = 16648823) B16648823
theorem B14798953 : Blo 2277435 14798953 := bstep (se 2 (by rfl) ⟨5549607, by rfl⟩ : syracuseStep 14798953 = 11099215) B11099215
theorem B78927749 : Blo 2277435 78927749 := bstep (se 4 (by rfl) ⟨7399476, by rfl⟩ : syracuseStep 78927749 = 14798953) B14798953
theorem B52618499 : Blo 2277435 52618499 := bstep (se 1 (by rfl) ⟨39463874, by rfl⟩ : syracuseStep 52618499 = 78927749) B78927749
theorem B35078999 : Blo 2277435 35078999 := bstep (se 1 (by rfl) ⟨26309249, by rfl⟩ : syracuseStep 35078999 = 52618499) B52618499
theorem B93543997 : Blo 2277435 93543997 := bstep (se 3 (by rfl) ⟨17539499, by rfl⟩ : syracuseStep 93543997 = 35078999) B35078999
theorem B124725329 : Blo 2277435 124725329 := bstep (se 2 (by rfl) ⟨46771998, by rfl⟩ : syracuseStep 124725329 = 93543997) B93543997
theorem B83150219 : Blo 2277435 83150219 := bstep (se 1 (by rfl) ⟨62362664, by rfl⟩ : syracuseStep 83150219 = 124725329) B124725329
theorem B55433479 : Blo 2277435 55433479 := bstep (se 1 (by rfl) ⟨41575109, by rfl⟩ : syracuseStep 55433479 = 83150219) B83150219
theorem B73911305 : Blo 2277435 73911305 := bstep (se 2 (by rfl) ⟨27716739, by rfl⟩ : syracuseStep 73911305 = 55433479) B55433479
theorem B49274203 : Blo 2277435 49274203 := bstep (se 1 (by rfl) ⟨36955652, by rfl⟩ : syracuseStep 49274203 = 73911305) B73911305
theorem B65698937 : Blo 2277435 65698937 := bstep (se 2 (by rfl) ⟨24637101, by rfl⟩ : syracuseStep 65698937 = 49274203) B49274203
theorem B43799291 : Blo 2277435 43799291 := bstep (se 1 (by rfl) ⟨32849468, by rfl⟩ : syracuseStep 43799291 = 65698937) B65698937
theorem B29199527 : Blo 2277435 29199527 := bstep (se 1 (by rfl) ⟨21899645, by rfl⟩ : syracuseStep 29199527 = 43799291) B43799291
theorem B19466351 : Blo 2277435 19466351 := bstep (se 1 (by rfl) ⟨14599763, by rfl⟩ : syracuseStep 19466351 = 29199527) B29199527
theorem B12977567 : Blo 2277435 12977567 := bstep (se 1 (by rfl) ⟨9733175, by rfl⟩ : syracuseStep 12977567 = 19466351) B19466351
theorem B8651711 : Blo 2277435 8651711 := bstep (se 1 (by rfl) ⟨6488783, by rfl⟩ : syracuseStep 8651711 = 12977567) B12977567
theorem B5767807 : Blo 2277435 5767807 := bstep (se 1 (by rfl) ⟨4325855, by rfl⟩ : syracuseStep 5767807 = 8651711) B8651711
theorem B7690409 : Blo 2277435 7690409 := bstep (se 2 (by rfl) ⟨2883903, by rfl⟩ : syracuseStep 7690409 = 5767807) B5767807
theorem B5126939 : Blo 2277435 5126939 := bstep (se 1 (by rfl) ⟨3845204, by rfl⟩ : syracuseStep 5126939 = 7690409) B7690409
theorem B3417959 : Blo 2277435 3417959 := bstep (se 1 (by rfl) ⟨2563469, by rfl⟩ : syracuseStep 3417959 = 5126939) B5126939
theorem B2278639 : Blo 2277435 2278639 := bstep (se 1 (by rfl) ⟨1708979, by rfl⟩ : syracuseStep 2278639 = 3417959) B3417959
theorem B3417965 : Blo 2277435 3417965 := bbase (se 3 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 3417965 = 1281737) (by norm_num)
theorem B2278643 : Blo 2277435 2278643 := bstep (se 1 (by rfl) ⟨1708982, by rfl⟩ : syracuseStep 2278643 = 3417965) B3417965
theorem B5126957 : Blo 2277435 5126957 := bbase (se 3 (by rfl) ⟨961304, by rfl⟩ : syracuseStep 5126957 = 1922609) (by norm_num)
theorem B3417971 : Blo 2277435 3417971 := bstep (se 1 (by rfl) ⟨2563478, by rfl⟩ : syracuseStep 3417971 = 5126957) B5126957
theorem B2278647 : Blo 2277435 2278647 := bstep (se 1 (by rfl) ⟨1708985, by rfl⟩ : syracuseStep 2278647 = 3417971) B3417971
theorem B4384901 : Blo 2277435 4384901 := bbase (se 4 (by rfl) ⟨411084, by rfl⟩ : syracuseStep 4384901 = 822169) (by norm_num)
theorem B11693069 : Blo 2277435 11693069 := bstep (se 3 (by rfl) ⟨2192450, by rfl⟩ : syracuseStep 11693069 = 4384901) B4384901
theorem B7795379 : Blo 2277435 7795379 := bstep (se 1 (by rfl) ⟨5846534, by rfl⟩ : syracuseStep 7795379 = 11693069) B11693069
theorem B20787677 : Blo 2277435 20787677 := bstep (se 3 (by rfl) ⟨3897689, by rfl⟩ : syracuseStep 20787677 = 7795379) B7795379
theorem B13858451 : Blo 2277435 13858451 := bstep (se 1 (by rfl) ⟨10393838, by rfl⟩ : syracuseStep 13858451 = 20787677) B20787677
theorem B9238967 : Blo 2277435 9238967 := bstep (se 1 (by rfl) ⟨6929225, by rfl⟩ : syracuseStep 9238967 = 13858451) B13858451
theorem B6159311 : Blo 2277435 6159311 := bstep (se 1 (by rfl) ⟨4619483, by rfl⟩ : syracuseStep 6159311 = 9238967) B9238967
theorem B4106207 : Blo 2277435 4106207 := bstep (se 1 (by rfl) ⟨3079655, by rfl⟩ : syracuseStep 4106207 = 6159311) B6159311
theorem B2737471 : Blo 2277435 2737471 := bstep (se 1 (by rfl) ⟨2053103, by rfl⟩ : syracuseStep 2737471 = 4106207) B4106207
theorem B3649961 : Blo 2277435 3649961 := bstep (se 2 (by rfl) ⟨1368735, by rfl⟩ : syracuseStep 3649961 = 2737471) B2737471
theorem B9733229 : Blo 2277435 9733229 := bstep (se 3 (by rfl) ⟨1824980, by rfl⟩ : syracuseStep 9733229 = 3649961) B3649961
theorem B6488819 : Blo 2277435 6488819 := bstep (se 1 (by rfl) ⟨4866614, by rfl⟩ : syracuseStep 6488819 = 9733229) B9733229
theorem B4325879 : Blo 2277435 4325879 := bstep (se 1 (by rfl) ⟨3244409, by rfl⟩ : syracuseStep 4325879 = 6488819) B6488819
theorem B2883919 : Blo 2277435 2883919 := bstep (se 1 (by rfl) ⟨2162939, by rfl⟩ : syracuseStep 2883919 = 4325879) B4325879
theorem B3845225 : Blo 2277435 3845225 := bstep (se 2 (by rfl) ⟨1441959, by rfl⟩ : syracuseStep 3845225 = 2883919) B2883919
theorem B2563483 : Blo 2277435 2563483 := bstep (se 1 (by rfl) ⟨1922612, by rfl⟩ : syracuseStep 2563483 = 3845225) B3845225
theorem B3417977 : Blo 2277435 3417977 := bstep (se 2 (by rfl) ⟨1281741, by rfl⟩ : syracuseStep 3417977 = 2563483) B2563483
theorem B2278651 : Blo 2277435 2278651 := bstep (se 1 (by rfl) ⟨1708988, by rfl⟩ : syracuseStep 2278651 = 3417977) B3417977
theorem B19732085 : Blo 2277435 19732085 := bbase (se 5 (by rfl) ⟨924941, by rfl⟩ : syracuseStep 19732085 = 1849883) (by norm_num)
theorem B13154723 : Blo 2277435 13154723 := bstep (se 1 (by rfl) ⟨9866042, by rfl⟩ : syracuseStep 13154723 = 19732085) B19732085
theorem B8769815 : Blo 2277435 8769815 := bstep (se 1 (by rfl) ⟨6577361, by rfl⟩ : syracuseStep 8769815 = 13154723) B13154723
theorem B5846543 : Blo 2277435 5846543 := bstep (se 1 (by rfl) ⟨4384907, by rfl⟩ : syracuseStep 5846543 = 8769815) B8769815
theorem B3897695 : Blo 2277435 3897695 := bstep (se 1 (by rfl) ⟨2923271, by rfl⟩ : syracuseStep 3897695 = 5846543) B5846543
theorem B2598463 : Blo 2277435 2598463 := bstep (se 1 (by rfl) ⟨1948847, by rfl⟩ : syracuseStep 2598463 = 3897695) B3897695
theorem B3464617 : Blo 2277435 3464617 := bstep (se 2 (by rfl) ⟨1299231, by rfl⟩ : syracuseStep 3464617 = 2598463) B2598463
theorem B4619489 : Blo 2277435 4619489 := bstep (se 2 (by rfl) ⟨1732308, by rfl⟩ : syracuseStep 4619489 = 3464617) B3464617
theorem B12318637 : Blo 2277435 12318637 := bstep (se 3 (by rfl) ⟨2309744, by rfl⟩ : syracuseStep 12318637 = 4619489) B4619489
theorem B16424849 : Blo 2277435 16424849 := bstep (se 2 (by rfl) ⟨6159318, by rfl⟩ : syracuseStep 16424849 = 12318637) B12318637
theorem B10949899 : Blo 2277435 10949899 := bstep (se 1 (by rfl) ⟨8212424, by rfl⟩ : syracuseStep 10949899 = 16424849) B16424849
theorem B14599865 : Blo 2277435 14599865 := bstep (se 2 (by rfl) ⟨5474949, by rfl⟩ : syracuseStep 14599865 = 10949899) B10949899
theorem B38932973 : Blo 2277435 38932973 := bstep (se 3 (by rfl) ⟨7299932, by rfl⟩ : syracuseStep 38932973 = 14599865) B14599865
theorem B25955315 : Blo 2277435 25955315 := bstep (se 1 (by rfl) ⟨19466486, by rfl⟩ : syracuseStep 25955315 = 38932973) B38932973
theorem B17303543 : Blo 2277435 17303543 := bstep (se 1 (by rfl) ⟨12977657, by rfl⟩ : syracuseStep 17303543 = 25955315) B25955315
theorem B11535695 : Blo 2277435 11535695 := bstep (se 1 (by rfl) ⟨8651771, by rfl⟩ : syracuseStep 11535695 = 17303543) B17303543
theorem B7690463 : Blo 2277435 7690463 := bstep (se 1 (by rfl) ⟨5767847, by rfl⟩ : syracuseStep 7690463 = 11535695) B11535695
theorem B5126975 : Blo 2277435 5126975 := bstep (se 1 (by rfl) ⟨3845231, by rfl⟩ : syracuseStep 5126975 = 7690463) B7690463
theorem B3417983 : Blo 2277435 3417983 := bstep (se 1 (by rfl) ⟨2563487, by rfl⟩ : syracuseStep 3417983 = 5126975) B5126975
theorem B2278655 : Blo 2277435 2278655 := bstep (se 1 (by rfl) ⟨1708991, by rfl⟩ : syracuseStep 2278655 = 3417983) B3417983
theorem B3417989 : Blo 2277435 3417989 := bbase (se 4 (by rfl) ⟨320436, by rfl⟩ : syracuseStep 3417989 = 640873) (by norm_num)
theorem B2278659 : Blo 2277435 2278659 := bstep (se 1 (by rfl) ⟨1708994, by rfl⟩ : syracuseStep 2278659 = 3417989) B3417989
theorem B3845245 : Blo 2277435 3845245 := bbase (se 3 (by rfl) ⟨720983, by rfl⟩ : syracuseStep 3845245 = 1441967) (by norm_num)
theorem B5126993 : Blo 2277435 5126993 := bstep (se 2 (by rfl) ⟨1922622, by rfl⟩ : syracuseStep 5126993 = 3845245) B3845245
theorem B3417995 : Blo 2277435 3417995 := bstep (se 1 (by rfl) ⟨2563496, by rfl⟩ : syracuseStep 3417995 = 5126993) B5126993
theorem B2278663 : Blo 2277435 2278663 := bstep (se 1 (by rfl) ⟨1708997, by rfl⟩ : syracuseStep 2278663 = 3417995) B3417995
theorem B2563501 : Blo 2277435 2563501 := bbase (se 3 (by rfl) ⟨480656, by rfl⟩ : syracuseStep 2563501 = 961313) (by norm_num)
theorem B3418001 : Blo 2277435 3418001 := bstep (se 2 (by rfl) ⟨1281750, by rfl⟩ : syracuseStep 3418001 = 2563501) B2563501
theorem B2278667 : Blo 2277435 2278667 := bstep (se 1 (by rfl) ⟨1709000, by rfl⟩ : syracuseStep 2278667 = 3418001) B3418001
theorem B7690517 : Blo 2277435 7690517 := bbase (se 6 (by rfl) ⟨180246, by rfl⟩ : syracuseStep 7690517 = 360493) (by norm_num)
theorem B5127011 : Blo 2277435 5127011 := bstep (se 1 (by rfl) ⟨3845258, by rfl⟩ : syracuseStep 5127011 = 7690517) B7690517
theorem B3418007 : Blo 2277435 3418007 := bstep (se 1 (by rfl) ⟨2563505, by rfl⟩ : syracuseStep 3418007 = 5127011) B5127011
theorem B2278671 : Blo 2277435 2278671 := bstep (se 1 (by rfl) ⟨1709003, by rfl⟩ : syracuseStep 2278671 = 3418007) B3418007
theorem B3418013 : Blo 2277435 3418013 := bbase (se 3 (by rfl) ⟨640877, by rfl⟩ : syracuseStep 3418013 = 1281755) (by norm_num)
theorem B2278675 : Blo 2277435 2278675 := bstep (se 1 (by rfl) ⟨1709006, by rfl⟩ : syracuseStep 2278675 = 3418013) B3418013
theorem B5127029 : Blo 2277435 5127029 := bbase (se 5 (by rfl) ⟨240329, by rfl⟩ : syracuseStep 5127029 = 480659) (by norm_num)
theorem B3418019 : Blo 2277435 3418019 := bstep (se 1 (by rfl) ⟨2563514, by rfl⟩ : syracuseStep 3418019 = 5127029) B5127029
theorem B2278679 : Blo 2277435 2278679 := bstep (se 1 (by rfl) ⟨1709009, by rfl⟩ : syracuseStep 2278679 = 3418019) B3418019
theorem B7399621 : Blo 2277435 7399621 := bbase (se 4 (by rfl) ⟨693714, by rfl⟩ : syracuseStep 7399621 = 1387429) (by norm_num)
theorem B9866161 : Blo 2277435 9866161 := bstep (se 2 (by rfl) ⟨3699810, by rfl⟩ : syracuseStep 9866161 = 7399621) B7399621
theorem B13154881 : Blo 2277435 13154881 := bstep (se 2 (by rfl) ⟨4933080, by rfl⟩ : syracuseStep 13154881 = 9866161) B9866161
theorem B17539841 : Blo 2277435 17539841 := bstep (se 2 (by rfl) ⟨6577440, by rfl⟩ : syracuseStep 17539841 = 13154881) B13154881
theorem B46772909 : Blo 2277435 46772909 := bstep (se 3 (by rfl) ⟨8769920, by rfl⟩ : syracuseStep 46772909 = 17539841) B17539841
theorem B31181939 : Blo 2277435 31181939 := bstep (se 1 (by rfl) ⟨23386454, by rfl⟩ : syracuseStep 31181939 = 46772909) B46772909
theorem B20787959 : Blo 2277435 20787959 := bstep (se 1 (by rfl) ⟨15590969, by rfl⟩ : syracuseStep 20787959 = 31181939) B31181939
theorem B55434557 : Blo 2277435 55434557 := bstep (se 3 (by rfl) ⟨10393979, by rfl⟩ : syracuseStep 55434557 = 20787959) B20787959
theorem B36956371 : Blo 2277435 36956371 := bstep (se 1 (by rfl) ⟨27717278, by rfl⟩ : syracuseStep 36956371 = 55434557) B55434557
theorem B49275161 : Blo 2277435 49275161 := bstep (se 2 (by rfl) ⟨18478185, by rfl⟩ : syracuseStep 49275161 = 36956371) B36956371
theorem B32850107 : Blo 2277435 32850107 := bstep (se 1 (by rfl) ⟨24637580, by rfl⟩ : syracuseStep 32850107 = 49275161) B49275161
theorem B21900071 : Blo 2277435 21900071 := bstep (se 1 (by rfl) ⟨16425053, by rfl⟩ : syracuseStep 21900071 = 32850107) B32850107
theorem B14600047 : Blo 2277435 14600047 := bstep (se 1 (by rfl) ⟨10950035, by rfl⟩ : syracuseStep 14600047 = 21900071) B21900071
theorem B19466729 : Blo 2277435 19466729 := bstep (se 2 (by rfl) ⟨7300023, by rfl⟩ : syracuseStep 19466729 = 14600047) B14600047
theorem B12977819 : Blo 2277435 12977819 := bstep (se 1 (by rfl) ⟨9733364, by rfl⟩ : syracuseStep 12977819 = 19466729) B19466729
theorem B8651879 : Blo 2277435 8651879 := bstep (se 1 (by rfl) ⟨6488909, by rfl⟩ : syracuseStep 8651879 = 12977819) B12977819
theorem B5767919 : Blo 2277435 5767919 := bstep (se 1 (by rfl) ⟨4325939, by rfl⟩ : syracuseStep 5767919 = 8651879) B8651879
theorem B3845279 : Blo 2277435 3845279 := bstep (se 1 (by rfl) ⟨2883959, by rfl⟩ : syracuseStep 3845279 = 5767919) B5767919
theorem B2563519 : Blo 2277435 2563519 := bstep (se 1 (by rfl) ⟨1922639, by rfl⟩ : syracuseStep 2563519 = 3845279) B3845279
theorem B3418025 : Blo 2277435 3418025 := bstep (se 2 (by rfl) ⟨1281759, by rfl⟩ : syracuseStep 3418025 = 2563519) B2563519
theorem B2278683 : Blo 2277435 2278683 := bstep (se 1 (by rfl) ⟨1709012, by rfl⟩ : syracuseStep 2278683 = 3418025) B3418025
theorem B8651893 : Blo 2277435 8651893 := bbase (se 5 (by rfl) ⟨405557, by rfl⟩ : syracuseStep 8651893 = 811115) (by norm_num)
theorem B11535857 : Blo 2277435 11535857 := bstep (se 2 (by rfl) ⟨4325946, by rfl⟩ : syracuseStep 11535857 = 8651893) B8651893
theorem B7690571 : Blo 2277435 7690571 := bstep (se 1 (by rfl) ⟨5767928, by rfl⟩ : syracuseStep 7690571 = 11535857) B11535857
theorem B5127047 : Blo 2277435 5127047 := bstep (se 1 (by rfl) ⟨3845285, by rfl⟩ : syracuseStep 5127047 = 7690571) B7690571
theorem B3418031 : Blo 2277435 3418031 := bstep (se 1 (by rfl) ⟨2563523, by rfl⟩ : syracuseStep 3418031 = 5127047) B5127047
theorem B2278687 : Blo 2277435 2278687 := bstep (se 1 (by rfl) ⟨1709015, by rfl⟩ : syracuseStep 2278687 = 3418031) B3418031
theorem B3418037 : Blo 2277435 3418037 := bbase (se 5 (by rfl) ⟨160220, by rfl⟩ : syracuseStep 3418037 = 320441) (by norm_num)
theorem B2278691 : Blo 2277435 2278691 := bstep (se 1 (by rfl) ⟨1709018, by rfl⟩ : syracuseStep 2278691 = 3418037) B3418037
theorem B5767949 : Blo 2277435 5767949 := bbase (se 3 (by rfl) ⟨1081490, by rfl⟩ : syracuseStep 5767949 = 2162981) (by norm_num)
theorem B3845299 : Blo 2277435 3845299 := bstep (se 1 (by rfl) ⟨2883974, by rfl⟩ : syracuseStep 3845299 = 5767949) B5767949
theorem B5127065 : Blo 2277435 5127065 := bstep (se 2 (by rfl) ⟨1922649, by rfl⟩ : syracuseStep 5127065 = 3845299) B3845299
theorem B3418043 : Blo 2277435 3418043 := bstep (se 1 (by rfl) ⟨2563532, by rfl⟩ : syracuseStep 3418043 = 5127065) B5127065
theorem B2278695 : Blo 2277435 2278695 := bstep (se 1 (by rfl) ⟨1709021, by rfl⟩ : syracuseStep 2278695 = 3418043) B3418043
theorem B2563537 : Blo 2277435 2563537 := bbase (se 2 (by rfl) ⟨961326, by rfl⟩ : syracuseStep 2563537 = 1922653) (by norm_num)
theorem B3418049 : Blo 2277435 3418049 := bstep (se 2 (by rfl) ⟨1281768, by rfl⟩ : syracuseStep 3418049 = 2563537) B2563537
theorem B2278699 : Blo 2277435 2278699 := bstep (se 1 (by rfl) ⟨1709024, by rfl⟩ : syracuseStep 2278699 = 3418049) B3418049
theorem B4866725 : Blo 2277435 4866725 := bbase (se 4 (by rfl) ⟨456255, by rfl⟩ : syracuseStep 4866725 = 912511) (by norm_num)
theorem B3244483 : Blo 2277435 3244483 := bstep (se 1 (by rfl) ⟨2433362, by rfl⟩ : syracuseStep 3244483 = 4866725) B4866725
theorem B4325977 : Blo 2277435 4325977 := bstep (se 2 (by rfl) ⟨1622241, by rfl⟩ : syracuseStep 4325977 = 3244483) B3244483
theorem B5767969 : Blo 2277435 5767969 := bstep (se 2 (by rfl) ⟨2162988, by rfl⟩ : syracuseStep 5767969 = 4325977) B4325977
theorem B7690625 : Blo 2277435 7690625 := bstep (se 2 (by rfl) ⟨2883984, by rfl⟩ : syracuseStep 7690625 = 5767969) B5767969
theorem B5127083 : Blo 2277435 5127083 := bstep (se 1 (by rfl) ⟨3845312, by rfl⟩ : syracuseStep 5127083 = 7690625) B7690625
theorem B3418055 : Blo 2277435 3418055 := bstep (se 1 (by rfl) ⟨2563541, by rfl⟩ : syracuseStep 3418055 = 5127083) B5127083
theorem B2278703 : Blo 2277435 2278703 := bstep (se 1 (by rfl) ⟨1709027, by rfl⟩ : syracuseStep 2278703 = 3418055) B3418055
theorem B3418061 : Blo 2277435 3418061 := bbase (se 3 (by rfl) ⟨640886, by rfl⟩ : syracuseStep 3418061 = 1281773) (by norm_num)
theorem B2278707 : Blo 2277435 2278707 := bstep (se 1 (by rfl) ⟨1709030, by rfl⟩ : syracuseStep 2278707 = 3418061) B3418061
theorem B5127101 : Blo 2277435 5127101 := bbase (se 3 (by rfl) ⟨961331, by rfl⟩ : syracuseStep 5127101 = 1922663) (by norm_num)
theorem B3418067 : Blo 2277435 3418067 := bstep (se 1 (by rfl) ⟨2563550, by rfl⟩ : syracuseStep 3418067 = 5127101) B5127101
theorem B2278711 : Blo 2277435 2278711 := bstep (se 1 (by rfl) ⟨1709033, by rfl⟩ : syracuseStep 2278711 = 3418067) B3418067
theorem B3845333 : Blo 2277435 3845333 := bbase (se 7 (by rfl) ⟨45062, by rfl⟩ : syracuseStep 3845333 = 90125) (by norm_num)
theorem B2563555 : Blo 2277435 2563555 := bstep (se 1 (by rfl) ⟨1922666, by rfl⟩ : syracuseStep 2563555 = 3845333) B3845333
theorem B3418073 : Blo 2277435 3418073 := bstep (se 2 (by rfl) ⟨1281777, by rfl⟩ : syracuseStep 3418073 = 2563555) B2563555
theorem B2278715 : Blo 2277435 2278715 := bstep (se 1 (by rfl) ⟨1709036, by rfl⟩ : syracuseStep 2278715 = 3418073) B3418073
theorem B3650069 : Blo 2277435 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B9733517 : Blo 2277435 9733517 := bstep (se 3 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 9733517 = 3650069) B3650069
theorem B6489011 : Blo 2277435 6489011 := bstep (se 1 (by rfl) ⟨4866758, by rfl⟩ : syracuseStep 6489011 = 9733517) B9733517
theorem B17304029 : Blo 2277435 17304029 := bstep (se 3 (by rfl) ⟨3244505, by rfl⟩ : syracuseStep 17304029 = 6489011) B6489011
theorem B11536019 : Blo 2277435 11536019 := bstep (se 1 (by rfl) ⟨8652014, by rfl⟩ : syracuseStep 11536019 = 17304029) B17304029
theorem B7690679 : Blo 2277435 7690679 := bstep (se 1 (by rfl) ⟨5768009, by rfl⟩ : syracuseStep 7690679 = 11536019) B11536019
theorem B5127119 : Blo 2277435 5127119 := bstep (se 1 (by rfl) ⟨3845339, by rfl⟩ : syracuseStep 5127119 = 7690679) B7690679
theorem B3418079 : Blo 2277435 3418079 := bstep (se 1 (by rfl) ⟨2563559, by rfl⟩ : syracuseStep 3418079 = 5127119) B5127119
theorem B2278719 : Blo 2277435 2278719 := bstep (se 1 (by rfl) ⟨1709039, by rfl⟩ : syracuseStep 2278719 = 3418079) B3418079
theorem B3418085 : Blo 2277435 3418085 := bbase (se 4 (by rfl) ⟨320445, by rfl⟩ : syracuseStep 3418085 = 640891) (by norm_num)
theorem B2278723 : Blo 2277435 2278723 := bstep (se 1 (by rfl) ⟨1709042, by rfl⟩ : syracuseStep 2278723 = 3418085) B3418085
theorem B7300165 : Blo 2277435 7300165 := bbase (se 4 (by rfl) ⟨684390, by rfl⟩ : syracuseStep 7300165 = 1368781) (by norm_num)
theorem B9733553 : Blo 2277435 9733553 := bstep (se 2 (by rfl) ⟨3650082, by rfl⟩ : syracuseStep 9733553 = 7300165) B7300165
theorem B6489035 : Blo 2277435 6489035 := bstep (se 1 (by rfl) ⟨4866776, by rfl⟩ : syracuseStep 6489035 = 9733553) B9733553
theorem B4326023 : Blo 2277435 4326023 := bstep (se 1 (by rfl) ⟨3244517, by rfl⟩ : syracuseStep 4326023 = 6489035) B6489035
theorem B2884015 : Blo 2277435 2884015 := bstep (se 1 (by rfl) ⟨2163011, by rfl⟩ : syracuseStep 2884015 = 4326023) B4326023
theorem B3845353 : Blo 2277435 3845353 := bstep (se 2 (by rfl) ⟨1442007, by rfl⟩ : syracuseStep 3845353 = 2884015) B2884015
theorem B5127137 : Blo 2277435 5127137 := bstep (se 2 (by rfl) ⟨1922676, by rfl⟩ : syracuseStep 5127137 = 3845353) B3845353
theorem B3418091 : Blo 2277435 3418091 := bstep (se 1 (by rfl) ⟨2563568, by rfl⟩ : syracuseStep 3418091 = 5127137) B5127137
theorem B2278727 : Blo 2277435 2278727 := bstep (se 1 (by rfl) ⟨1709045, by rfl⟩ : syracuseStep 2278727 = 3418091) B3418091
theorem B2563573 : Blo 2277435 2563573 := bbase (se 5 (by rfl) ⟨120167, by rfl⟩ : syracuseStep 2563573 = 240335) (by norm_num)
theorem B3418097 : Blo 2277435 3418097 := bstep (se 2 (by rfl) ⟨1281786, by rfl⟩ : syracuseStep 3418097 = 2563573) B2563573
theorem B2278731 : Blo 2277435 2278731 := bstep (se 1 (by rfl) ⟨1709048, by rfl⟩ : syracuseStep 2278731 = 3418097) B3418097
theorem B2884025 : Blo 2277435 2884025 := bbase (se 2 (by rfl) ⟨1081509, by rfl⟩ : syracuseStep 2884025 = 2163019) (by norm_num)
theorem B7690733 : Blo 2277435 7690733 := bstep (se 3 (by rfl) ⟨1442012, by rfl⟩ : syracuseStep 7690733 = 2884025) B2884025
theorem B5127155 : Blo 2277435 5127155 := bstep (se 1 (by rfl) ⟨3845366, by rfl⟩ : syracuseStep 5127155 = 7690733) B7690733
theorem B3418103 : Blo 2277435 3418103 := bstep (se 1 (by rfl) ⟨2563577, by rfl⟩ : syracuseStep 3418103 = 5127155) B5127155
theorem B2278735 : Blo 2277435 2278735 := bstep (se 1 (by rfl) ⟨1709051, by rfl⟩ : syracuseStep 2278735 = 3418103) B3418103
theorem B3418109 : Blo 2277435 3418109 := bbase (se 3 (by rfl) ⟨640895, by rfl⟩ : syracuseStep 3418109 = 1281791) (by norm_num)
theorem B2278739 : Blo 2277435 2278739 := bstep (se 1 (by rfl) ⟨1709054, by rfl⟩ : syracuseStep 2278739 = 3418109) B3418109
theorem B5127173 : Blo 2277435 5127173 := bbase (se 4 (by rfl) ⟨480672, by rfl⟩ : syracuseStep 5127173 = 961345) (by norm_num)
theorem B3418115 : Blo 2277435 3418115 := bstep (se 1 (by rfl) ⟨2563586, by rfl⟩ : syracuseStep 3418115 = 5127173) B5127173
theorem B2278743 : Blo 2277435 2278743 := bstep (se 1 (by rfl) ⟨1709057, by rfl⟩ : syracuseStep 2278743 = 3418115) B3418115
theorem B4326061 : Blo 2277435 4326061 := bbase (se 3 (by rfl) ⟨811136, by rfl⟩ : syracuseStep 4326061 = 1622273) (by norm_num)
theorem B5768081 : Blo 2277435 5768081 := bstep (se 2 (by rfl) ⟨2163030, by rfl⟩ : syracuseStep 5768081 = 4326061) B4326061
theorem B3845387 : Blo 2277435 3845387 := bstep (se 1 (by rfl) ⟨2884040, by rfl⟩ : syracuseStep 3845387 = 5768081) B5768081
theorem B2563591 : Blo 2277435 2563591 := bstep (se 1 (by rfl) ⟨1922693, by rfl⟩ : syracuseStep 2563591 = 3845387) B3845387
theorem B3418121 : Blo 2277435 3418121 := bstep (se 2 (by rfl) ⟨1281795, by rfl⟩ : syracuseStep 3418121 = 2563591) B2563591
theorem B2278747 : Blo 2277435 2278747 := bstep (se 1 (by rfl) ⟨1709060, by rfl⟩ : syracuseStep 2278747 = 3418121) B3418121
theorem B11536181 : Blo 2277435 11536181 := bbase (se 5 (by rfl) ⟨540758, by rfl⟩ : syracuseStep 11536181 = 1081517) (by norm_num)
theorem B7690787 : Blo 2277435 7690787 := bstep (se 1 (by rfl) ⟨5768090, by rfl⟩ : syracuseStep 7690787 = 11536181) B11536181
theorem B5127191 : Blo 2277435 5127191 := bstep (se 1 (by rfl) ⟨3845393, by rfl⟩ : syracuseStep 5127191 = 7690787) B7690787
theorem B3418127 : Blo 2277435 3418127 := bstep (se 1 (by rfl) ⟨2563595, by rfl⟩ : syracuseStep 3418127 = 5127191) B5127191
theorem B2278751 : Blo 2277435 2278751 := bstep (se 1 (by rfl) ⟨1709063, by rfl⟩ : syracuseStep 2278751 = 3418127) B3418127
theorem B3418133 : Blo 2277435 3418133 := bbase (se 6 (by rfl) ⟨80112, by rfl⟩ : syracuseStep 3418133 = 160225) (by norm_num)
theorem B2278755 : Blo 2277435 2278755 := bstep (se 1 (by rfl) ⟨1709066, by rfl⟩ : syracuseStep 2278755 = 3418133) B3418133
theorem B14600533 : Blo 2277435 14600533 := bbase (se 10 (by rfl) ⟨21387, by rfl⟩ : syracuseStep 14600533 = 42775) (by norm_num)
theorem B19467377 : Blo 2277435 19467377 := bstep (se 2 (by rfl) ⟨7300266, by rfl⟩ : syracuseStep 19467377 = 14600533) B14600533
theorem B12978251 : Blo 2277435 12978251 := bstep (se 1 (by rfl) ⟨9733688, by rfl⟩ : syracuseStep 12978251 = 19467377) B19467377
theorem B8652167 : Blo 2277435 8652167 := bstep (se 1 (by rfl) ⟨6489125, by rfl⟩ : syracuseStep 8652167 = 12978251) B12978251
theorem B5768111 : Blo 2277435 5768111 := bstep (se 1 (by rfl) ⟨4326083, by rfl⟩ : syracuseStep 5768111 = 8652167) B8652167
theorem B3845407 : Blo 2277435 3845407 := bstep (se 1 (by rfl) ⟨2884055, by rfl⟩ : syracuseStep 3845407 = 5768111) B5768111
theorem B5127209 : Blo 2277435 5127209 := bstep (se 2 (by rfl) ⟨1922703, by rfl⟩ : syracuseStep 5127209 = 3845407) B3845407
theorem B3418139 : Blo 2277435 3418139 := bstep (se 1 (by rfl) ⟨2563604, by rfl⟩ : syracuseStep 3418139 = 5127209) B5127209
theorem B2278759 : Blo 2277435 2278759 := bstep (se 1 (by rfl) ⟨1709069, by rfl⟩ : syracuseStep 2278759 = 3418139) B3418139
theorem B2563609 : Blo 2277435 2563609 := bbase (se 2 (by rfl) ⟨961353, by rfl⟩ : syracuseStep 2563609 = 1922707) (by norm_num)
theorem B3418145 : Blo 2277435 3418145 := bstep (se 2 (by rfl) ⟨1281804, by rfl⟩ : syracuseStep 3418145 = 2563609) B2563609
theorem B2278763 : Blo 2277435 2278763 := bstep (se 1 (by rfl) ⟨1709072, by rfl⟩ : syracuseStep 2278763 = 3418145) B3418145
theorem B8652197 : Blo 2277435 8652197 := bbase (se 4 (by rfl) ⟨811143, by rfl⟩ : syracuseStep 8652197 = 1622287) (by norm_num)
theorem B5768131 : Blo 2277435 5768131 := bstep (se 1 (by rfl) ⟨4326098, by rfl⟩ : syracuseStep 5768131 = 8652197) B8652197
theorem B7690841 : Blo 2277435 7690841 := bstep (se 2 (by rfl) ⟨2884065, by rfl⟩ : syracuseStep 7690841 = 5768131) B5768131
theorem B5127227 : Blo 2277435 5127227 := bstep (se 1 (by rfl) ⟨3845420, by rfl⟩ : syracuseStep 5127227 = 7690841) B7690841
theorem B3418151 : Blo 2277435 3418151 := bstep (se 1 (by rfl) ⟨2563613, by rfl⟩ : syracuseStep 3418151 = 5127227) B5127227
theorem B2278767 : Blo 2277435 2278767 := bstep (se 1 (by rfl) ⟨1709075, by rfl⟩ : syracuseStep 2278767 = 3418151) B3418151
theorem B3418157 : Blo 2277435 3418157 := bbase (se 3 (by rfl) ⟨640904, by rfl⟩ : syracuseStep 3418157 = 1281809) (by norm_num)
theorem B2278771 : Blo 2277435 2278771 := bstep (se 1 (by rfl) ⟨1709078, by rfl⟩ : syracuseStep 2278771 = 3418157) B3418157
theorem B5127245 : Blo 2277435 5127245 := bbase (se 3 (by rfl) ⟨961358, by rfl⟩ : syracuseStep 5127245 = 1922717) (by norm_num)
theorem B3418163 : Blo 2277435 3418163 := bstep (se 1 (by rfl) ⟨2563622, by rfl⟩ : syracuseStep 3418163 = 5127245) B5127245
theorem B2278775 : Blo 2277435 2278775 := bstep (se 1 (by rfl) ⟨1709081, by rfl⟩ : syracuseStep 2278775 = 3418163) B3418163
theorem B2884081 : Blo 2277435 2884081 := bbase (se 2 (by rfl) ⟨1081530, by rfl⟩ : syracuseStep 2884081 = 2163061) (by norm_num)
theorem B3845441 : Blo 2277435 3845441 := bstep (se 2 (by rfl) ⟨1442040, by rfl⟩ : syracuseStep 3845441 = 2884081) B2884081
theorem B2563627 : Blo 2277435 2563627 := bstep (se 1 (by rfl) ⟨1922720, by rfl⟩ : syracuseStep 2563627 = 3845441) B3845441
theorem B3418169 : Blo 2277435 3418169 := bstep (se 2 (by rfl) ⟨1281813, by rfl⟩ : syracuseStep 3418169 = 2563627) B2563627
theorem B2278779 : Blo 2277435 2278779 := bstep (se 1 (by rfl) ⟨1709084, by rfl⟩ : syracuseStep 2278779 = 3418169) B3418169
theorem B4619749 : Blo 2277435 4619749 := bbase (se 4 (by rfl) ⟨433101, by rfl⟩ : syracuseStep 4619749 = 866203) (by norm_num)
theorem B6159665 : Blo 2277435 6159665 := bstep (se 2 (by rfl) ⟨2309874, by rfl⟩ : syracuseStep 6159665 = 4619749) B4619749
theorem B16425773 : Blo 2277435 16425773 := bstep (se 3 (by rfl) ⟨3079832, by rfl⟩ : syracuseStep 16425773 = 6159665) B6159665
theorem B10950515 : Blo 2277435 10950515 := bstep (se 1 (by rfl) ⟨8212886, by rfl⟩ : syracuseStep 10950515 = 16425773) B16425773
theorem B7300343 : Blo 2277435 7300343 := bstep (se 1 (by rfl) ⟨5475257, by rfl⟩ : syracuseStep 7300343 = 10950515) B10950515
theorem B4866895 : Blo 2277435 4866895 := bstep (se 1 (by rfl) ⟨3650171, by rfl⟩ : syracuseStep 4866895 = 7300343) B7300343
theorem B25956773 : Blo 2277435 25956773 := bstep (se 4 (by rfl) ⟨2433447, by rfl⟩ : syracuseStep 25956773 = 4866895) B4866895
theorem B17304515 : Blo 2277435 17304515 := bstep (se 1 (by rfl) ⟨12978386, by rfl⟩ : syracuseStep 17304515 = 25956773) B25956773
theorem B11536343 : Blo 2277435 11536343 := bstep (se 1 (by rfl) ⟨8652257, by rfl⟩ : syracuseStep 11536343 = 17304515) B17304515
theorem B7690895 : Blo 2277435 7690895 := bstep (se 1 (by rfl) ⟨5768171, by rfl⟩ : syracuseStep 7690895 = 11536343) B11536343
theorem B5127263 : Blo 2277435 5127263 := bstep (se 1 (by rfl) ⟨3845447, by rfl⟩ : syracuseStep 5127263 = 7690895) B7690895
theorem B3418175 : Blo 2277435 3418175 := bstep (se 1 (by rfl) ⟨2563631, by rfl⟩ : syracuseStep 3418175 = 5127263) B5127263
theorem B2278783 : Blo 2277435 2278783 := bstep (se 1 (by rfl) ⟨1709087, by rfl⟩ : syracuseStep 2278783 = 3418175) B3418175
theorem B3418181 : Blo 2277435 3418181 := bbase (se 4 (by rfl) ⟨320454, by rfl⟩ : syracuseStep 3418181 = 640909) (by norm_num)
theorem B2278787 : Blo 2277435 2278787 := bstep (se 1 (by rfl) ⟨1709090, by rfl⟩ : syracuseStep 2278787 = 3418181) B3418181
theorem B3845461 : Blo 2277435 3845461 := bbase (se 11 (by rfl) ⟨2816, by rfl⟩ : syracuseStep 3845461 = 5633) (by norm_num)
theorem B5127281 : Blo 2277435 5127281 := bstep (se 2 (by rfl) ⟨1922730, by rfl⟩ : syracuseStep 5127281 = 3845461) B3845461
theorem B3418187 : Blo 2277435 3418187 := bstep (se 1 (by rfl) ⟨2563640, by rfl⟩ : syracuseStep 3418187 = 5127281) B5127281
theorem B2278791 : Blo 2277435 2278791 := bstep (se 1 (by rfl) ⟨1709093, by rfl⟩ : syracuseStep 2278791 = 3418187) B3418187
theorem B2563645 : Blo 2277435 2563645 := bbase (se 3 (by rfl) ⟨480683, by rfl⟩ : syracuseStep 2563645 = 961367) (by norm_num)
theorem B3418193 : Blo 2277435 3418193 := bstep (se 2 (by rfl) ⟨1281822, by rfl⟩ : syracuseStep 3418193 = 2563645) B2563645
theorem B2278795 : Blo 2277435 2278795 := bstep (se 1 (by rfl) ⟨1709096, by rfl⟩ : syracuseStep 2278795 = 3418193) B3418193
theorem B7690949 : Blo 2277435 7690949 := bbase (se 4 (by rfl) ⟨721026, by rfl⟩ : syracuseStep 7690949 = 1442053) (by norm_num)
theorem B5127299 : Blo 2277435 5127299 := bstep (se 1 (by rfl) ⟨3845474, by rfl⟩ : syracuseStep 5127299 = 7690949) B7690949
theorem B3418199 : Blo 2277435 3418199 := bstep (se 1 (by rfl) ⟨2563649, by rfl⟩ : syracuseStep 3418199 = 5127299) B5127299
theorem B2278799 : Blo 2277435 2278799 := bstep (se 1 (by rfl) ⟨1709099, by rfl⟩ : syracuseStep 2278799 = 3418199) B3418199
theorem B3418205 : Blo 2277435 3418205 := bbase (se 3 (by rfl) ⟨640913, by rfl⟩ : syracuseStep 3418205 = 1281827) (by norm_num)
theorem B2278803 : Blo 2277435 2278803 := bstep (se 1 (by rfl) ⟨1709102, by rfl⟩ : syracuseStep 2278803 = 3418205) B3418205
theorem B5127317 : Blo 2277435 5127317 := bbase (se 6 (by rfl) ⟨120171, by rfl⟩ : syracuseStep 5127317 = 240343) (by norm_num)
theorem B3418211 : Blo 2277435 3418211 := bstep (se 1 (by rfl) ⟨2563658, by rfl⟩ : syracuseStep 3418211 = 5127317) B5127317
theorem B2278807 : Blo 2277435 2278807 := bstep (se 1 (by rfl) ⟨1709105, by rfl⟩ : syracuseStep 2278807 = 3418211) B3418211
theorem B3244637 : Blo 2277435 3244637 := bbase (se 3 (by rfl) ⟨608369, by rfl⟩ : syracuseStep 3244637 = 1216739) (by norm_num)
theorem B8652365 : Blo 2277435 8652365 := bstep (se 3 (by rfl) ⟨1622318, by rfl⟩ : syracuseStep 8652365 = 3244637) B3244637
theorem B5768243 : Blo 2277435 5768243 := bstep (se 1 (by rfl) ⟨4326182, by rfl⟩ : syracuseStep 5768243 = 8652365) B8652365
theorem B3845495 : Blo 2277435 3845495 := bstep (se 1 (by rfl) ⟨2884121, by rfl⟩ : syracuseStep 3845495 = 5768243) B5768243
theorem B2563663 : Blo 2277435 2563663 := bstep (se 1 (by rfl) ⟨1922747, by rfl⟩ : syracuseStep 2563663 = 3845495) B3845495
theorem B3418217 : Blo 2277435 3418217 := bstep (se 2 (by rfl) ⟨1281831, by rfl⟩ : syracuseStep 3418217 = 2563663) B2563663
theorem B2278811 : Blo 2277435 2278811 := bstep (se 1 (by rfl) ⟨1709108, by rfl⟩ : syracuseStep 2278811 = 3418217) B3418217
theorem B10394581 : Blo 2277435 10394581 := bbase (se 7 (by rfl) ⟨121811, by rfl⟩ : syracuseStep 10394581 = 243623) (by norm_num)
theorem B13859441 : Blo 2277435 13859441 := bstep (se 2 (by rfl) ⟨5197290, by rfl⟩ : syracuseStep 13859441 = 10394581) B10394581
theorem B9239627 : Blo 2277435 9239627 := bstep (se 1 (by rfl) ⟨6929720, by rfl⟩ : syracuseStep 9239627 = 13859441) B13859441
theorem B24639005 : Blo 2277435 24639005 := bstep (se 3 (by rfl) ⟨4619813, by rfl⟩ : syracuseStep 24639005 = 9239627) B9239627
theorem B16426003 : Blo 2277435 16426003 := bstep (se 1 (by rfl) ⟨12319502, by rfl⟩ : syracuseStep 16426003 = 24639005) B24639005
theorem B21901337 : Blo 2277435 21901337 := bstep (se 2 (by rfl) ⟨8213001, by rfl⟩ : syracuseStep 21901337 = 16426003) B16426003
theorem B14600891 : Blo 2277435 14600891 := bstep (se 1 (by rfl) ⟨10950668, by rfl⟩ : syracuseStep 14600891 = 21901337) B21901337
theorem B9733927 : Blo 2277435 9733927 := bstep (se 1 (by rfl) ⟨7300445, by rfl⟩ : syracuseStep 9733927 = 14600891) B14600891
theorem B12978569 : Blo 2277435 12978569 := bstep (se 2 (by rfl) ⟨4866963, by rfl⟩ : syracuseStep 12978569 = 9733927) B9733927
theorem B8652379 : Blo 2277435 8652379 := bstep (se 1 (by rfl) ⟨6489284, by rfl⟩ : syracuseStep 8652379 = 12978569) B12978569
theorem B11536505 : Blo 2277435 11536505 := bstep (se 2 (by rfl) ⟨4326189, by rfl⟩ : syracuseStep 11536505 = 8652379) B8652379
theorem B7691003 : Blo 2277435 7691003 := bstep (se 1 (by rfl) ⟨5768252, by rfl⟩ : syracuseStep 7691003 = 11536505) B11536505
theorem B5127335 : Blo 2277435 5127335 := bstep (se 1 (by rfl) ⟨3845501, by rfl⟩ : syracuseStep 5127335 = 7691003) B7691003
theorem B3418223 : Blo 2277435 3418223 := bstep (se 1 (by rfl) ⟨2563667, by rfl⟩ : syracuseStep 3418223 = 5127335) B5127335
theorem B2278815 : Blo 2277435 2278815 := bstep (se 1 (by rfl) ⟨1709111, by rfl⟩ : syracuseStep 2278815 = 3418223) B3418223
theorem B3418229 : Blo 2277435 3418229 := bbase (se 5 (by rfl) ⟨160229, by rfl⟩ : syracuseStep 3418229 = 320459) (by norm_num)
theorem B2278819 : Blo 2277435 2278819 := bstep (se 1 (by rfl) ⟨1709114, by rfl⟩ : syracuseStep 2278819 = 3418229) B3418229
theorem B4326205 : Blo 2277435 4326205 := bbase (se 3 (by rfl) ⟨811163, by rfl⟩ : syracuseStep 4326205 = 1622327) (by norm_num)
theorem B5768273 : Blo 2277435 5768273 := bstep (se 2 (by rfl) ⟨2163102, by rfl⟩ : syracuseStep 5768273 = 4326205) B4326205
theorem B3845515 : Blo 2277435 3845515 := bstep (se 1 (by rfl) ⟨2884136, by rfl⟩ : syracuseStep 3845515 = 5768273) B5768273
theorem B5127353 : Blo 2277435 5127353 := bstep (se 2 (by rfl) ⟨1922757, by rfl⟩ : syracuseStep 5127353 = 3845515) B3845515
theorem B3418235 : Blo 2277435 3418235 := bstep (se 1 (by rfl) ⟨2563676, by rfl⟩ : syracuseStep 3418235 = 5127353) B5127353
theorem B2278823 : Blo 2277435 2278823 := bstep (se 1 (by rfl) ⟨1709117, by rfl⟩ : syracuseStep 2278823 = 3418235) B3418235
theorem B2563681 : Blo 2277435 2563681 := bbase (se 2 (by rfl) ⟨961380, by rfl⟩ : syracuseStep 2563681 = 1922761) (by norm_num)
theorem B3418241 : Blo 2277435 3418241 := bstep (se 2 (by rfl) ⟨1281840, by rfl⟩ : syracuseStep 3418241 = 2563681) B2563681
theorem B2278827 : Blo 2277435 2278827 := bstep (se 1 (by rfl) ⟨1709120, by rfl⟩ : syracuseStep 2278827 = 3418241) B3418241
theorem B5768293 : Blo 2277435 5768293 := bbase (se 4 (by rfl) ⟨540777, by rfl⟩ : syracuseStep 5768293 = 1081555) (by norm_num)
theorem B7691057 : Blo 2277435 7691057 := bstep (se 2 (by rfl) ⟨2884146, by rfl⟩ : syracuseStep 7691057 = 5768293) B5768293
theorem B5127371 : Blo 2277435 5127371 := bstep (se 1 (by rfl) ⟨3845528, by rfl⟩ : syracuseStep 5127371 = 7691057) B7691057
theorem B3418247 : Blo 2277435 3418247 := bstep (se 1 (by rfl) ⟨2563685, by rfl⟩ : syracuseStep 3418247 = 5127371) B5127371
theorem B2278831 : Blo 2277435 2278831 := bstep (se 1 (by rfl) ⟨1709123, by rfl⟩ : syracuseStep 2278831 = 3418247) B3418247
theorem B3418253 : Blo 2277435 3418253 := bbase (se 3 (by rfl) ⟨640922, by rfl⟩ : syracuseStep 3418253 = 1281845) (by norm_num)
theorem B2278835 : Blo 2277435 2278835 := bstep (se 1 (by rfl) ⟨1709126, by rfl⟩ : syracuseStep 2278835 = 3418253) B3418253
theorem B5127389 : Blo 2277435 5127389 := bbase (se 3 (by rfl) ⟨961385, by rfl⟩ : syracuseStep 5127389 = 1922771) (by norm_num)
theorem B3418259 : Blo 2277435 3418259 := bstep (se 1 (by rfl) ⟨2563694, by rfl⟩ : syracuseStep 3418259 = 5127389) B5127389
theorem B2278839 : Blo 2277435 2278839 := bstep (se 1 (by rfl) ⟨1709129, by rfl⟩ : syracuseStep 2278839 = 3418259) B3418259
theorem B3845549 : Blo 2277435 3845549 := bbase (se 3 (by rfl) ⟨721040, by rfl⟩ : syracuseStep 3845549 = 1442081) (by norm_num)
theorem B2563699 : Blo 2277435 2563699 := bstep (se 1 (by rfl) ⟨1922774, by rfl⟩ : syracuseStep 2563699 = 3845549) B3845549
theorem B3418265 : Blo 2277435 3418265 := bstep (se 2 (by rfl) ⟨1281849, by rfl⟩ : syracuseStep 3418265 = 2563699) B2563699
theorem B2278843 : Blo 2277435 2278843 := bstep (se 1 (by rfl) ⟨1709132, by rfl⟩ : syracuseStep 2278843 = 3418265) B3418265
theorem B3464909 : Blo 2277435 3464909 := bbase (se 3 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 3464909 = 1299341) (by norm_num)
theorem B2309939 : Blo 2277435 2309939 := bstep (se 1 (by rfl) ⟨1732454, by rfl⟩ : syracuseStep 2309939 = 3464909) B3464909
theorem B98557397 : Blo 2277435 98557397 := bstep (se 7 (by rfl) ⟨1154969, by rfl⟩ : syracuseStep 98557397 = 2309939) B2309939
theorem B65704931 : Blo 2277435 65704931 := bstep (se 1 (by rfl) ⟨49278698, by rfl⟩ : syracuseStep 65704931 = 98557397) B98557397
theorem B43803287 : Blo 2277435 43803287 := bstep (se 1 (by rfl) ⟨32852465, by rfl⟩ : syracuseStep 43803287 = 65704931) B65704931
theorem B29202191 : Blo 2277435 29202191 := bstep (se 1 (by rfl) ⟨21901643, by rfl⟩ : syracuseStep 29202191 = 43803287) B43803287
theorem B19468127 : Blo 2277435 19468127 := bstep (se 1 (by rfl) ⟨14601095, by rfl⟩ : syracuseStep 19468127 = 29202191) B29202191
theorem B12978751 : Blo 2277435 12978751 := bstep (se 1 (by rfl) ⟨9734063, by rfl⟩ : syracuseStep 12978751 = 19468127) B19468127
theorem B17305001 : Blo 2277435 17305001 := bstep (se 2 (by rfl) ⟨6489375, by rfl⟩ : syracuseStep 17305001 = 12978751) B12978751
theorem B11536667 : Blo 2277435 11536667 := bstep (se 1 (by rfl) ⟨8652500, by rfl⟩ : syracuseStep 11536667 = 17305001) B17305001
theorem B7691111 : Blo 2277435 7691111 := bstep (se 1 (by rfl) ⟨5768333, by rfl⟩ : syracuseStep 7691111 = 11536667) B11536667
theorem B5127407 : Blo 2277435 5127407 := bstep (se 1 (by rfl) ⟨3845555, by rfl⟩ : syracuseStep 5127407 = 7691111) B7691111
theorem B3418271 : Blo 2277435 3418271 := bstep (se 1 (by rfl) ⟨2563703, by rfl⟩ : syracuseStep 3418271 = 5127407) B5127407
theorem B2278847 : Blo 2277435 2278847 := bstep (se 1 (by rfl) ⟨1709135, by rfl⟩ : syracuseStep 2278847 = 3418271) B3418271
theorem B3418277 : Blo 2277435 3418277 := bbase (se 4 (by rfl) ⟨320463, by rfl⟩ : syracuseStep 3418277 = 640927) (by norm_num)
theorem B2278851 : Blo 2277435 2278851 := bstep (se 1 (by rfl) ⟨1709138, by rfl⟩ : syracuseStep 2278851 = 3418277) B3418277
theorem B2884177 : Blo 2277435 2884177 := bbase (se 2 (by rfl) ⟨1081566, by rfl⟩ : syracuseStep 2884177 = 2163133) (by norm_num)
theorem B3845569 : Blo 2277435 3845569 := bstep (se 2 (by rfl) ⟨1442088, by rfl⟩ : syracuseStep 3845569 = 2884177) B2884177
theorem B5127425 : Blo 2277435 5127425 := bstep (se 2 (by rfl) ⟨1922784, by rfl⟩ : syracuseStep 5127425 = 3845569) B3845569
theorem B3418283 : Blo 2277435 3418283 := bstep (se 1 (by rfl) ⟨2563712, by rfl⟩ : syracuseStep 3418283 = 5127425) B5127425
theorem B2278855 : Blo 2277435 2278855 := bstep (se 1 (by rfl) ⟨1709141, by rfl⟩ : syracuseStep 2278855 = 3418283) B3418283
theorem B2563717 : Blo 2277435 2563717 := bbase (se 4 (by rfl) ⟨240348, by rfl⟩ : syracuseStep 2563717 = 480697) (by norm_num)
theorem B3418289 : Blo 2277435 3418289 := bstep (se 2 (by rfl) ⟨1281858, by rfl⟩ : syracuseStep 3418289 = 2563717) B2563717
theorem B2278859 : Blo 2277435 2278859 := bstep (se 1 (by rfl) ⟨1709144, by rfl⟩ : syracuseStep 2278859 = 3418289) B3418289
theorem B2598701 : Blo 2277435 2598701 := bbase (se 3 (by rfl) ⟨487256, by rfl⟩ : syracuseStep 2598701 = 974513) (by norm_num)
theorem B6929869 : Blo 2277435 6929869 := bstep (se 3 (by rfl) ⟨1299350, by rfl⟩ : syracuseStep 6929869 = 2598701) B2598701
theorem B9239825 : Blo 2277435 9239825 := bstep (se 2 (by rfl) ⟨3464934, by rfl⟩ : syracuseStep 9239825 = 6929869) B6929869
theorem B6159883 : Blo 2277435 6159883 := bstep (se 1 (by rfl) ⟨4619912, by rfl⟩ : syracuseStep 6159883 = 9239825) B9239825
theorem B8213177 : Blo 2277435 8213177 := bstep (se 2 (by rfl) ⟨3079941, by rfl⟩ : syracuseStep 8213177 = 6159883) B6159883
theorem B5475451 : Blo 2277435 5475451 := bstep (se 1 (by rfl) ⟨4106588, by rfl⟩ : syracuseStep 5475451 = 8213177) B8213177
theorem B7300601 : Blo 2277435 7300601 := bstep (se 2 (by rfl) ⟨2737725, by rfl⟩ : syracuseStep 7300601 = 5475451) B5475451
theorem B4867067 : Blo 2277435 4867067 := bstep (se 1 (by rfl) ⟨3650300, by rfl⟩ : syracuseStep 4867067 = 7300601) B7300601
theorem B3244711 : Blo 2277435 3244711 := bstep (se 1 (by rfl) ⟨2433533, by rfl⟩ : syracuseStep 3244711 = 4867067) B4867067
theorem B4326281 : Blo 2277435 4326281 := bstep (se 2 (by rfl) ⟨1622355, by rfl⟩ : syracuseStep 4326281 = 3244711) B3244711
theorem B2884187 : Blo 2277435 2884187 := bstep (se 1 (by rfl) ⟨2163140, by rfl⟩ : syracuseStep 2884187 = 4326281) B4326281
theorem B7691165 : Blo 2277435 7691165 := bstep (se 3 (by rfl) ⟨1442093, by rfl⟩ : syracuseStep 7691165 = 2884187) B2884187
theorem B5127443 : Blo 2277435 5127443 := bstep (se 1 (by rfl) ⟨3845582, by rfl⟩ : syracuseStep 5127443 = 7691165) B7691165
theorem B3418295 : Blo 2277435 3418295 := bstep (se 1 (by rfl) ⟨2563721, by rfl⟩ : syracuseStep 3418295 = 5127443) B5127443
theorem B2278863 : Blo 2277435 2278863 := bstep (se 1 (by rfl) ⟨1709147, by rfl⟩ : syracuseStep 2278863 = 3418295) B3418295
theorem B3418301 : Blo 2277435 3418301 := bbase (se 3 (by rfl) ⟨640931, by rfl⟩ : syracuseStep 3418301 = 1281863) (by norm_num)
theorem B2278867 : Blo 2277435 2278867 := bstep (se 1 (by rfl) ⟨1709150, by rfl⟩ : syracuseStep 2278867 = 3418301) B3418301
theorem B5127461 : Blo 2277435 5127461 := bbase (se 4 (by rfl) ⟨480699, by rfl⟩ : syracuseStep 5127461 = 961399) (by norm_num)
theorem B3418307 : Blo 2277435 3418307 := bstep (se 1 (by rfl) ⟨2563730, by rfl⟩ : syracuseStep 3418307 = 5127461) B5127461
theorem B2278871 : Blo 2277435 2278871 := bstep (se 1 (by rfl) ⟨1709153, by rfl⟩ : syracuseStep 2278871 = 3418307) B3418307
theorem B5768405 : Blo 2277435 5768405 := bbase (se 7 (by rfl) ⟨67598, by rfl⟩ : syracuseStep 5768405 = 135197) (by norm_num)
theorem B3845603 : Blo 2277435 3845603 := bstep (se 1 (by rfl) ⟨2884202, by rfl⟩ : syracuseStep 3845603 = 5768405) B5768405
theorem B2563735 : Blo 2277435 2563735 := bstep (se 1 (by rfl) ⟨1922801, by rfl⟩ : syracuseStep 2563735 = 3845603) B3845603
theorem B3418313 : Blo 2277435 3418313 := bstep (se 2 (by rfl) ⟨1281867, by rfl⟩ : syracuseStep 3418313 = 2563735) B2563735
theorem B2278875 : Blo 2277435 2278875 := bstep (se 1 (by rfl) ⟨1709156, by rfl⟩ : syracuseStep 2278875 = 3418313) B3418313
theorem B6159925 : Blo 2277435 6159925 := bbase (se 5 (by rfl) ⟨288746, by rfl⟩ : syracuseStep 6159925 = 577493) (by norm_num)
theorem B8213233 : Blo 2277435 8213233 := bstep (se 2 (by rfl) ⟨3079962, by rfl⟩ : syracuseStep 8213233 = 6159925) B6159925
theorem B10950977 : Blo 2277435 10950977 := bstep (se 2 (by rfl) ⟨4106616, by rfl⟩ : syracuseStep 10950977 = 8213233) B8213233
theorem B7300651 : Blo 2277435 7300651 := bstep (se 1 (by rfl) ⟨5475488, by rfl⟩ : syracuseStep 7300651 = 10950977) B10950977
theorem B9734201 : Blo 2277435 9734201 := bstep (se 2 (by rfl) ⟨3650325, by rfl⟩ : syracuseStep 9734201 = 7300651) B7300651
theorem B6489467 : Blo 2277435 6489467 := bstep (se 1 (by rfl) ⟨4867100, by rfl⟩ : syracuseStep 6489467 = 9734201) B9734201
theorem B4326311 : Blo 2277435 4326311 := bstep (se 1 (by rfl) ⟨3244733, by rfl⟩ : syracuseStep 4326311 = 6489467) B6489467
theorem B11536829 : Blo 2277435 11536829 := bstep (se 3 (by rfl) ⟨2163155, by rfl⟩ : syracuseStep 11536829 = 4326311) B4326311
theorem B7691219 : Blo 2277435 7691219 := bstep (se 1 (by rfl) ⟨5768414, by rfl⟩ : syracuseStep 7691219 = 11536829) B11536829
theorem B5127479 : Blo 2277435 5127479 := bstep (se 1 (by rfl) ⟨3845609, by rfl⟩ : syracuseStep 5127479 = 7691219) B7691219
theorem B3418319 : Blo 2277435 3418319 := bstep (se 1 (by rfl) ⟨2563739, by rfl⟩ : syracuseStep 3418319 = 5127479) B5127479
theorem B2278879 : Blo 2277435 2278879 := bstep (se 1 (by rfl) ⟨1709159, by rfl⟩ : syracuseStep 2278879 = 3418319) B3418319
theorem B3418325 : Blo 2277435 3418325 := bbase (se 7 (by rfl) ⟨40058, by rfl⟩ : syracuseStep 3418325 = 80117) (by norm_num)
theorem B2278883 : Blo 2277435 2278883 := bstep (se 1 (by rfl) ⟨1709162, by rfl⟩ : syracuseStep 2278883 = 3418325) B3418325
theorem B5475509 : Blo 2277435 5475509 := bbase (se 5 (by rfl) ⟨256664, by rfl⟩ : syracuseStep 5475509 = 513329) (by norm_num)
theorem B3650339 : Blo 2277435 3650339 := bstep (se 1 (by rfl) ⟨2737754, by rfl⟩ : syracuseStep 3650339 = 5475509) B5475509
theorem B2433559 : Blo 2277435 2433559 := bstep (se 1 (by rfl) ⟨1825169, by rfl⟩ : syracuseStep 2433559 = 3650339) B3650339
theorem B3244745 : Blo 2277435 3244745 := bstep (se 2 (by rfl) ⟨1216779, by rfl⟩ : syracuseStep 3244745 = 2433559) B2433559
theorem B8652653 : Blo 2277435 8652653 := bstep (se 3 (by rfl) ⟨1622372, by rfl⟩ : syracuseStep 8652653 = 3244745) B3244745
theorem B5768435 : Blo 2277435 5768435 := bstep (se 1 (by rfl) ⟨4326326, by rfl⟩ : syracuseStep 5768435 = 8652653) B8652653
theorem B3845623 : Blo 2277435 3845623 := bstep (se 1 (by rfl) ⟨2884217, by rfl⟩ : syracuseStep 3845623 = 5768435) B5768435
theorem B5127497 : Blo 2277435 5127497 := bstep (se 2 (by rfl) ⟨1922811, by rfl⟩ : syracuseStep 5127497 = 3845623) B3845623
theorem B3418331 : Blo 2277435 3418331 := bstep (se 1 (by rfl) ⟨2563748, by rfl⟩ : syracuseStep 3418331 = 5127497) B5127497
theorem B2278887 : Blo 2277435 2278887 := bstep (se 1 (by rfl) ⟨1709165, by rfl⟩ : syracuseStep 2278887 = 3418331) B3418331
theorem B2563753 : Blo 2277435 2563753 := bbase (se 2 (by rfl) ⟨961407, by rfl⟩ : syracuseStep 2563753 = 1922815) (by norm_num)
theorem B3418337 : Blo 2277435 3418337 := bstep (se 2 (by rfl) ⟨1281876, by rfl⟩ : syracuseStep 3418337 = 2563753) B2563753
theorem B2278891 : Blo 2277435 2278891 := bstep (se 1 (by rfl) ⟨1709168, by rfl⟩ : syracuseStep 2278891 = 3418337) B3418337
theorem B2598737 : Blo 2277435 2598737 := bbase (se 2 (by rfl) ⟨974526, by rfl⟩ : syracuseStep 2598737 = 1949053) (by norm_num)
theorem B6929965 : Blo 2277435 6929965 := bstep (se 3 (by rfl) ⟨1299368, by rfl⟩ : syracuseStep 6929965 = 2598737) B2598737
theorem B9239953 : Blo 2277435 9239953 := bstep (se 2 (by rfl) ⟨3464982, by rfl⟩ : syracuseStep 9239953 = 6929965) B6929965
theorem B12319937 : Blo 2277435 12319937 := bstep (se 2 (by rfl) ⟨4619976, by rfl⟩ : syracuseStep 12319937 = 9239953) B9239953
theorem B8213291 : Blo 2277435 8213291 := bstep (se 1 (by rfl) ⟨6159968, by rfl⟩ : syracuseStep 8213291 = 12319937) B12319937
theorem B5475527 : Blo 2277435 5475527 := bstep (se 1 (by rfl) ⟨4106645, by rfl⟩ : syracuseStep 5475527 = 8213291) B8213291
theorem B3650351 : Blo 2277435 3650351 := bstep (se 1 (by rfl) ⟨2737763, by rfl⟩ : syracuseStep 3650351 = 5475527) B5475527
theorem B9734269 : Blo 2277435 9734269 := bstep (se 3 (by rfl) ⟨1825175, by rfl⟩ : syracuseStep 9734269 = 3650351) B3650351
theorem B12979025 : Blo 2277435 12979025 := bstep (se 2 (by rfl) ⟨4867134, by rfl⟩ : syracuseStep 12979025 = 9734269) B9734269
theorem B8652683 : Blo 2277435 8652683 := bstep (se 1 (by rfl) ⟨6489512, by rfl⟩ : syracuseStep 8652683 = 12979025) B12979025
theorem B5768455 : Blo 2277435 5768455 := bstep (se 1 (by rfl) ⟨4326341, by rfl⟩ : syracuseStep 5768455 = 8652683) B8652683
theorem B7691273 : Blo 2277435 7691273 := bstep (se 2 (by rfl) ⟨2884227, by rfl⟩ : syracuseStep 7691273 = 5768455) B5768455
theorem B5127515 : Blo 2277435 5127515 := bstep (se 1 (by rfl) ⟨3845636, by rfl⟩ : syracuseStep 5127515 = 7691273) B7691273
theorem B3418343 : Blo 2277435 3418343 := bstep (se 1 (by rfl) ⟨2563757, by rfl⟩ : syracuseStep 3418343 = 5127515) B5127515
theorem B2278895 : Blo 2277435 2278895 := bstep (se 1 (by rfl) ⟨1709171, by rfl⟩ : syracuseStep 2278895 = 3418343) B3418343
theorem B3418349 : Blo 2277435 3418349 := bbase (se 3 (by rfl) ⟨640940, by rfl⟩ : syracuseStep 3418349 = 1281881) (by norm_num)
theorem B2278899 : Blo 2277435 2278899 := bstep (se 1 (by rfl) ⟨1709174, by rfl⟩ : syracuseStep 2278899 = 3418349) B3418349
theorem B5127533 : Blo 2277435 5127533 := bbase (se 3 (by rfl) ⟨961412, by rfl⟩ : syracuseStep 5127533 = 1922825) (by norm_num)
theorem B3418355 : Blo 2277435 3418355 := bstep (se 1 (by rfl) ⟨2563766, by rfl⟩ : syracuseStep 3418355 = 5127533) B5127533
theorem B2278903 : Blo 2277435 2278903 := bstep (se 1 (by rfl) ⟨1709177, by rfl⟩ : syracuseStep 2278903 = 3418355) B3418355
theorem B4326365 : Blo 2277435 4326365 := bbase (se 3 (by rfl) ⟨811193, by rfl⟩ : syracuseStep 4326365 = 1622387) (by norm_num)
theorem B2884243 : Blo 2277435 2884243 := bstep (se 1 (by rfl) ⟨2163182, by rfl⟩ : syracuseStep 2884243 = 4326365) B4326365
theorem B3845657 : Blo 2277435 3845657 := bstep (se 2 (by rfl) ⟨1442121, by rfl⟩ : syracuseStep 3845657 = 2884243) B2884243
theorem B2563771 : Blo 2277435 2563771 := bstep (se 1 (by rfl) ⟨1922828, by rfl⟩ : syracuseStep 2563771 = 3845657) B3845657
theorem B3418361 : Blo 2277435 3418361 := bstep (se 2 (by rfl) ⟨1281885, by rfl⟩ : syracuseStep 3418361 = 2563771) B2563771
theorem B2278907 : Blo 2277435 2278907 := bstep (se 1 (by rfl) ⟨1709180, by rfl⟩ : syracuseStep 2278907 = 3418361) B3418361
theorem B12320021 : Blo 2277435 12320021 := bbase (se 6 (by rfl) ⟨288750, by rfl⟩ : syracuseStep 12320021 = 577501) (by norm_num)
theorem B8213347 : Blo 2277435 8213347 := bstep (se 1 (by rfl) ⟨6160010, by rfl⟩ : syracuseStep 8213347 = 12320021) B12320021
theorem B10951129 : Blo 2277435 10951129 := bstep (se 2 (by rfl) ⟨4106673, by rfl⟩ : syracuseStep 10951129 = 8213347) B8213347
theorem B58406021 : Blo 2277435 58406021 := bstep (se 4 (by rfl) ⟨5475564, by rfl⟩ : syracuseStep 58406021 = 10951129) B10951129
theorem B38937347 : Blo 2277435 38937347 := bstep (se 1 (by rfl) ⟨29203010, by rfl⟩ : syracuseStep 38937347 = 58406021) B58406021
theorem B25958231 : Blo 2277435 25958231 := bstep (se 1 (by rfl) ⟨19468673, by rfl⟩ : syracuseStep 25958231 = 38937347) B38937347
theorem B17305487 : Blo 2277435 17305487 := bstep (se 1 (by rfl) ⟨12979115, by rfl⟩ : syracuseStep 17305487 = 25958231) B25958231
theorem B11536991 : Blo 2277435 11536991 := bstep (se 1 (by rfl) ⟨8652743, by rfl⟩ : syracuseStep 11536991 = 17305487) B17305487
theorem B7691327 : Blo 2277435 7691327 := bstep (se 1 (by rfl) ⟨5768495, by rfl⟩ : syracuseStep 7691327 = 11536991) B11536991
theorem B5127551 : Blo 2277435 5127551 := bstep (se 1 (by rfl) ⟨3845663, by rfl⟩ : syracuseStep 5127551 = 7691327) B7691327
theorem B3418367 : Blo 2277435 3418367 := bstep (se 1 (by rfl) ⟨2563775, by rfl⟩ : syracuseStep 3418367 = 5127551) B5127551
theorem B2278911 : Blo 2277435 2278911 := bstep (se 1 (by rfl) ⟨1709183, by rfl⟩ : syracuseStep 2278911 = 3418367) B3418367
theorem B3418373 : Blo 2277435 3418373 := bbase (se 4 (by rfl) ⟨320472, by rfl⟩ : syracuseStep 3418373 = 640945) (by norm_num)
theorem B2278915 : Blo 2277435 2278915 := bstep (se 1 (by rfl) ⟨1709186, by rfl⟩ : syracuseStep 2278915 = 3418373) B3418373
theorem B3845677 : Blo 2277435 3845677 := bbase (se 3 (by rfl) ⟨721064, by rfl⟩ : syracuseStep 3845677 = 1442129) (by norm_num)
theorem B5127569 : Blo 2277435 5127569 := bstep (se 2 (by rfl) ⟨1922838, by rfl⟩ : syracuseStep 5127569 = 3845677) B3845677
theorem B3418379 : Blo 2277435 3418379 := bstep (se 1 (by rfl) ⟨2563784, by rfl⟩ : syracuseStep 3418379 = 5127569) B5127569
theorem B2278919 : Blo 2277435 2278919 := bstep (se 1 (by rfl) ⟨1709189, by rfl⟩ : syracuseStep 2278919 = 3418379) B3418379
theorem B2563789 : Blo 2277435 2563789 := bbase (se 3 (by rfl) ⟨480710, by rfl⟩ : syracuseStep 2563789 = 961421) (by norm_num)
theorem B3418385 : Blo 2277435 3418385 := bstep (se 2 (by rfl) ⟨1281894, by rfl⟩ : syracuseStep 3418385 = 2563789) B2563789
theorem B2278923 : Blo 2277435 2278923 := bstep (se 1 (by rfl) ⟨1709192, by rfl⟩ : syracuseStep 2278923 = 3418385) B3418385
theorem B7691381 : Blo 2277435 7691381 := bbase (se 5 (by rfl) ⟨360533, by rfl⟩ : syracuseStep 7691381 = 721067) (by norm_num)
theorem B5127587 : Blo 2277435 5127587 := bstep (se 1 (by rfl) ⟨3845690, by rfl⟩ : syracuseStep 5127587 = 7691381) B7691381
theorem B3418391 : Blo 2277435 3418391 := bstep (se 1 (by rfl) ⟨2563793, by rfl⟩ : syracuseStep 3418391 = 5127587) B5127587
theorem B2278927 : Blo 2277435 2278927 := bstep (se 1 (by rfl) ⟨1709195, by rfl⟩ : syracuseStep 2278927 = 3418391) B3418391
theorem B3418397 : Blo 2277435 3418397 := bbase (se 3 (by rfl) ⟨640949, by rfl⟩ : syracuseStep 3418397 = 1281899) (by norm_num)
theorem B2278931 : Blo 2277435 2278931 := bstep (se 1 (by rfl) ⟨1709198, by rfl⟩ : syracuseStep 2278931 = 3418397) B3418397
theorem B5127605 : Blo 2277435 5127605 := bbase (se 5 (by rfl) ⟨240356, by rfl⟩ : syracuseStep 5127605 = 480713) (by norm_num)
theorem B3418403 : Blo 2277435 3418403 := bstep (se 1 (by rfl) ⟨2563802, by rfl⟩ : syracuseStep 3418403 = 5127605) B5127605
theorem B2278935 : Blo 2277435 2278935 := bstep (se 1 (by rfl) ⟨1709201, by rfl⟩ : syracuseStep 2278935 = 3418403) B3418403
theorem B4867229 : Blo 2277435 4867229 := bbase (se 3 (by rfl) ⟨912605, by rfl⟩ : syracuseStep 4867229 = 1825211) (by norm_num)
theorem B12979277 : Blo 2277435 12979277 := bstep (se 3 (by rfl) ⟨2433614, by rfl⟩ : syracuseStep 12979277 = 4867229) B4867229
theorem B8652851 : Blo 2277435 8652851 := bstep (se 1 (by rfl) ⟨6489638, by rfl⟩ : syracuseStep 8652851 = 12979277) B12979277
theorem B5768567 : Blo 2277435 5768567 := bstep (se 1 (by rfl) ⟨4326425, by rfl⟩ : syracuseStep 5768567 = 8652851) B8652851
theorem B3845711 : Blo 2277435 3845711 := bstep (se 1 (by rfl) ⟨2884283, by rfl⟩ : syracuseStep 3845711 = 5768567) B5768567
theorem B2563807 : Blo 2277435 2563807 := bstep (se 1 (by rfl) ⟨1922855, by rfl⟩ : syracuseStep 2563807 = 3845711) B3845711
theorem B3418409 : Blo 2277435 3418409 := bstep (se 2 (by rfl) ⟨1281903, by rfl⟩ : syracuseStep 3418409 = 2563807) B2563807
theorem B2278939 : Blo 2277435 2278939 := bstep (se 1 (by rfl) ⟨1709204, by rfl⟩ : syracuseStep 2278939 = 3418409) B3418409
theorem B4867237 : Blo 2277435 4867237 := bbase (se 4 (by rfl) ⟨456303, by rfl⟩ : syracuseStep 4867237 = 912607) (by norm_num)
theorem B6489649 : Blo 2277435 6489649 := bstep (se 2 (by rfl) ⟨2433618, by rfl⟩ : syracuseStep 6489649 = 4867237) B4867237
theorem B8652865 : Blo 2277435 8652865 := bstep (se 2 (by rfl) ⟨3244824, by rfl⟩ : syracuseStep 8652865 = 6489649) B6489649
theorem B11537153 : Blo 2277435 11537153 := bstep (se 2 (by rfl) ⟨4326432, by rfl⟩ : syracuseStep 11537153 = 8652865) B8652865
theorem B7691435 : Blo 2277435 7691435 := bstep (se 1 (by rfl) ⟨5768576, by rfl⟩ : syracuseStep 7691435 = 11537153) B11537153
theorem B5127623 : Blo 2277435 5127623 := bstep (se 1 (by rfl) ⟨3845717, by rfl⟩ : syracuseStep 5127623 = 7691435) B7691435
theorem B3418415 : Blo 2277435 3418415 := bstep (se 1 (by rfl) ⟨2563811, by rfl⟩ : syracuseStep 3418415 = 5127623) B5127623
theorem B2278943 : Blo 2277435 2278943 := bstep (se 1 (by rfl) ⟨1709207, by rfl⟩ : syracuseStep 2278943 = 3418415) B3418415
theorem B3418421 : Blo 2277435 3418421 := bbase (se 5 (by rfl) ⟨160238, by rfl⟩ : syracuseStep 3418421 = 320477) (by norm_num)
theorem B2278947 : Blo 2277435 2278947 := bstep (se 1 (by rfl) ⟨1709210, by rfl⟩ : syracuseStep 2278947 = 3418421) B3418421
theorem B5768597 : Blo 2277435 5768597 := bbase (se 6 (by rfl) ⟨135201, by rfl⟩ : syracuseStep 5768597 = 270403) (by norm_num)
theorem B3845731 : Blo 2277435 3845731 := bstep (se 1 (by rfl) ⟨2884298, by rfl⟩ : syracuseStep 3845731 = 5768597) B5768597
theorem B5127641 : Blo 2277435 5127641 := bstep (se 2 (by rfl) ⟨1922865, by rfl⟩ : syracuseStep 5127641 = 3845731) B3845731
theorem B3418427 : Blo 2277435 3418427 := bstep (se 1 (by rfl) ⟨2563820, by rfl⟩ : syracuseStep 3418427 = 5127641) B5127641
theorem B2278951 : Blo 2277435 2278951 := bstep (se 1 (by rfl) ⟨1709213, by rfl⟩ : syracuseStep 2278951 = 3418427) B3418427
theorem B2563825 : Blo 2277435 2563825 := bbase (se 2 (by rfl) ⟨961434, by rfl⟩ : syracuseStep 2563825 = 1922869) (by norm_num)
theorem B3418433 : Blo 2277435 3418433 := bstep (se 2 (by rfl) ⟨1281912, by rfl⟩ : syracuseStep 3418433 = 2563825) B2563825
theorem B2278955 : Blo 2277435 2278955 := bstep (se 1 (by rfl) ⟨1709216, by rfl⟩ : syracuseStep 2278955 = 3418433) B3418433
theorem B2310053 : Blo 2277435 2310053 := bbase (se 4 (by rfl) ⟨216567, by rfl⟩ : syracuseStep 2310053 = 433135) (by norm_num)
theorem B6160141 : Blo 2277435 6160141 := bstep (se 3 (by rfl) ⟨1155026, by rfl⟩ : syracuseStep 6160141 = 2310053) B2310053
theorem B32854085 : Blo 2277435 32854085 := bstep (se 4 (by rfl) ⟨3080070, by rfl⟩ : syracuseStep 32854085 = 6160141) B6160141
theorem B21902723 : Blo 2277435 21902723 := bstep (se 1 (by rfl) ⟨16427042, by rfl⟩ : syracuseStep 21902723 = 32854085) B32854085
theorem B14601815 : Blo 2277435 14601815 := bstep (se 1 (by rfl) ⟨10951361, by rfl⟩ : syracuseStep 14601815 = 21902723) B21902723
theorem B9734543 : Blo 2277435 9734543 := bstep (se 1 (by rfl) ⟨7300907, by rfl⟩ : syracuseStep 9734543 = 14601815) B14601815
theorem B6489695 : Blo 2277435 6489695 := bstep (se 1 (by rfl) ⟨4867271, by rfl⟩ : syracuseStep 6489695 = 9734543) B9734543
theorem B4326463 : Blo 2277435 4326463 := bstep (se 1 (by rfl) ⟨3244847, by rfl⟩ : syracuseStep 4326463 = 6489695) B6489695
theorem B5768617 : Blo 2277435 5768617 := bstep (se 2 (by rfl) ⟨2163231, by rfl⟩ : syracuseStep 5768617 = 4326463) B4326463
theorem B7691489 : Blo 2277435 7691489 := bstep (se 2 (by rfl) ⟨2884308, by rfl⟩ : syracuseStep 7691489 = 5768617) B5768617
theorem B5127659 : Blo 2277435 5127659 := bstep (se 1 (by rfl) ⟨3845744, by rfl⟩ : syracuseStep 5127659 = 7691489) B7691489
theorem B3418439 : Blo 2277435 3418439 := bstep (se 1 (by rfl) ⟨2563829, by rfl⟩ : syracuseStep 3418439 = 5127659) B5127659
theorem B2278959 : Blo 2277435 2278959 := bstep (se 1 (by rfl) ⟨1709219, by rfl⟩ : syracuseStep 2278959 = 3418439) B3418439
theorem B3418445 : Blo 2277435 3418445 := bbase (se 3 (by rfl) ⟨640958, by rfl⟩ : syracuseStep 3418445 = 1281917) (by norm_num)
theorem B2278963 : Blo 2277435 2278963 := bstep (se 1 (by rfl) ⟨1709222, by rfl⟩ : syracuseStep 2278963 = 3418445) B3418445
theorem B5127677 : Blo 2277435 5127677 := bbase (se 3 (by rfl) ⟨961439, by rfl⟩ : syracuseStep 5127677 = 1922879) (by norm_num)
theorem B3418451 : Blo 2277435 3418451 := bstep (se 1 (by rfl) ⟨2563838, by rfl⟩ : syracuseStep 3418451 = 5127677) B5127677
theorem B2278967 : Blo 2277435 2278967 := bstep (se 1 (by rfl) ⟨1709225, by rfl⟩ : syracuseStep 2278967 = 3418451) B3418451
theorem B3845765 : Blo 2277435 3845765 := bbase (se 4 (by rfl) ⟨360540, by rfl⟩ : syracuseStep 3845765 = 721081) (by norm_num)
theorem B2563843 : Blo 2277435 2563843 := bstep (se 1 (by rfl) ⟨1922882, by rfl⟩ : syracuseStep 2563843 = 3845765) B3845765
theorem B3418457 : Blo 2277435 3418457 := bstep (se 2 (by rfl) ⟨1281921, by rfl⟩ : syracuseStep 3418457 = 2563843) B2563843
theorem B2278971 : Blo 2277435 2278971 := bstep (se 1 (by rfl) ⟨1709228, by rfl⟩ : syracuseStep 2278971 = 3418457) B3418457
theorem B17305973 : Blo 2277435 17305973 := bbase (se 5 (by rfl) ⟨811217, by rfl⟩ : syracuseStep 17305973 = 1622435) (by norm_num)
theorem B11537315 : Blo 2277435 11537315 := bstep (se 1 (by rfl) ⟨8652986, by rfl⟩ : syracuseStep 11537315 = 17305973) B17305973
theorem B7691543 : Blo 2277435 7691543 := bstep (se 1 (by rfl) ⟨5768657, by rfl⟩ : syracuseStep 7691543 = 11537315) B11537315
theorem B5127695 : Blo 2277435 5127695 := bstep (se 1 (by rfl) ⟨3845771, by rfl⟩ : syracuseStep 5127695 = 7691543) B7691543
theorem B3418463 : Blo 2277435 3418463 := bstep (se 1 (by rfl) ⟨2563847, by rfl⟩ : syracuseStep 3418463 = 5127695) B5127695
theorem B2278975 : Blo 2277435 2278975 := bstep (se 1 (by rfl) ⟨1709231, by rfl⟩ : syracuseStep 2278975 = 3418463) B3418463
theorem B3418469 : Blo 2277435 3418469 := bbase (se 4 (by rfl) ⟨320481, by rfl⟩ : syracuseStep 3418469 = 640963) (by norm_num)
theorem B2278979 : Blo 2277435 2278979 := bstep (se 1 (by rfl) ⟨1709234, by rfl⟩ : syracuseStep 2278979 = 3418469) B3418469
theorem B4326509 : Blo 2277435 4326509 := bbase (se 3 (by rfl) ⟨811220, by rfl⟩ : syracuseStep 4326509 = 1622441) (by norm_num)
theorem B2884339 : Blo 2277435 2884339 := bstep (se 1 (by rfl) ⟨2163254, by rfl⟩ : syracuseStep 2884339 = 4326509) B4326509
theorem B3845785 : Blo 2277435 3845785 := bstep (se 2 (by rfl) ⟨1442169, by rfl⟩ : syracuseStep 3845785 = 2884339) B2884339
theorem B5127713 : Blo 2277435 5127713 := bstep (se 2 (by rfl) ⟨1922892, by rfl⟩ : syracuseStep 5127713 = 3845785) B3845785
theorem B3418475 : Blo 2277435 3418475 := bstep (se 1 (by rfl) ⟨2563856, by rfl⟩ : syracuseStep 3418475 = 5127713) B5127713
theorem B2278983 : Blo 2277435 2278983 := bstep (se 1 (by rfl) ⟨1709237, by rfl⟩ : syracuseStep 2278983 = 3418475) B3418475
theorem B2563861 : Blo 2277435 2563861 := bbase (se 6 (by rfl) ⟨60090, by rfl⟩ : syracuseStep 2563861 = 120181) (by norm_num)
theorem B3418481 : Blo 2277435 3418481 := bstep (se 2 (by rfl) ⟨1281930, by rfl⟩ : syracuseStep 3418481 = 2563861) B2563861
theorem B2278987 : Blo 2277435 2278987 := bstep (se 1 (by rfl) ⟨1709240, by rfl⟩ : syracuseStep 2278987 = 3418481) B3418481
theorem B2884349 : Blo 2277435 2884349 := bbase (se 3 (by rfl) ⟨540815, by rfl⟩ : syracuseStep 2884349 = 1081631) (by norm_num)
theorem B7691597 : Blo 2277435 7691597 := bstep (se 3 (by rfl) ⟨1442174, by rfl⟩ : syracuseStep 7691597 = 2884349) B2884349
theorem B5127731 : Blo 2277435 5127731 := bstep (se 1 (by rfl) ⟨3845798, by rfl⟩ : syracuseStep 5127731 = 7691597) B7691597
theorem B3418487 : Blo 2277435 3418487 := bstep (se 1 (by rfl) ⟨2563865, by rfl⟩ : syracuseStep 3418487 = 5127731) B5127731
theorem B2278991 : Blo 2277435 2278991 := bstep (se 1 (by rfl) ⟨1709243, by rfl⟩ : syracuseStep 2278991 = 3418487) B3418487
theorem B3418493 : Blo 2277435 3418493 := bbase (se 3 (by rfl) ⟨640967, by rfl⟩ : syracuseStep 3418493 = 1281935) (by norm_num)
theorem B2278995 : Blo 2277435 2278995 := bstep (se 1 (by rfl) ⟨1709246, by rfl⟩ : syracuseStep 2278995 = 3418493) B3418493
theorem B5127749 : Blo 2277435 5127749 := bbase (se 4 (by rfl) ⟨480726, by rfl⟩ : syracuseStep 5127749 = 961453) (by norm_num)
theorem B3418499 : Blo 2277435 3418499 := bstep (se 1 (by rfl) ⟨2563874, by rfl⟩ : syracuseStep 3418499 = 5127749) B5127749
theorem B2278999 : Blo 2277435 2278999 := bstep (se 1 (by rfl) ⟨1709249, by rfl⟩ : syracuseStep 2278999 = 3418499) B3418499
theorem B3650525 : Blo 2277435 3650525 := bbase (se 3 (by rfl) ⟨684473, by rfl⟩ : syracuseStep 3650525 = 1368947) (by norm_num)
theorem B2433683 : Blo 2277435 2433683 := bstep (se 1 (by rfl) ⟨1825262, by rfl⟩ : syracuseStep 2433683 = 3650525) B3650525
theorem B6489821 : Blo 2277435 6489821 := bstep (se 3 (by rfl) ⟨1216841, by rfl⟩ : syracuseStep 6489821 = 2433683) B2433683
theorem B4326547 : Blo 2277435 4326547 := bstep (se 1 (by rfl) ⟨3244910, by rfl⟩ : syracuseStep 4326547 = 6489821) B6489821
theorem B5768729 : Blo 2277435 5768729 := bstep (se 2 (by rfl) ⟨2163273, by rfl⟩ : syracuseStep 5768729 = 4326547) B4326547
theorem B3845819 : Blo 2277435 3845819 := bstep (se 1 (by rfl) ⟨2884364, by rfl⟩ : syracuseStep 3845819 = 5768729) B5768729
theorem B2563879 : Blo 2277435 2563879 := bstep (se 1 (by rfl) ⟨1922909, by rfl⟩ : syracuseStep 2563879 = 3845819) B3845819
theorem B3418505 : Blo 2277435 3418505 := bstep (se 2 (by rfl) ⟨1281939, by rfl⟩ : syracuseStep 3418505 = 2563879) B2563879
theorem B2279003 : Blo 2277435 2279003 := bstep (se 1 (by rfl) ⟨1709252, by rfl⟩ : syracuseStep 2279003 = 3418505) B3418505
theorem B11537477 : Blo 2277435 11537477 := bbase (se 4 (by rfl) ⟨1081638, by rfl⟩ : syracuseStep 11537477 = 2163277) (by norm_num)
theorem B7691651 : Blo 2277435 7691651 := bstep (se 1 (by rfl) ⟨5768738, by rfl⟩ : syracuseStep 7691651 = 11537477) B11537477
theorem B5127767 : Blo 2277435 5127767 := bstep (se 1 (by rfl) ⟨3845825, by rfl⟩ : syracuseStep 5127767 = 7691651) B7691651
theorem B3418511 : Blo 2277435 3418511 := bstep (se 1 (by rfl) ⟨2563883, by rfl⟩ : syracuseStep 3418511 = 5127767) B5127767
theorem B2279007 : Blo 2277435 2279007 := bstep (se 1 (by rfl) ⟨1709255, by rfl⟩ : syracuseStep 2279007 = 3418511) B3418511
theorem B3418517 : Blo 2277435 3418517 := bbase (se 6 (by rfl) ⟨80121, by rfl⟩ : syracuseStep 3418517 = 160243) (by norm_num)
theorem B2279011 : Blo 2277435 2279011 := bstep (se 1 (by rfl) ⟨1709258, by rfl⟩ : syracuseStep 2279011 = 3418517) B3418517
theorem B2923733 : Blo 2277435 2923733 := bbase (se 7 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 2923733 = 68525) (by norm_num)
theorem B7796621 : Blo 2277435 7796621 := bstep (se 3 (by rfl) ⟨1461866, by rfl⟩ : syracuseStep 7796621 = 2923733) B2923733
theorem B20790989 : Blo 2277435 20790989 := bstep (se 3 (by rfl) ⟨3898310, by rfl⟩ : syracuseStep 20790989 = 7796621) B7796621
theorem B13860659 : Blo 2277435 13860659 := bstep (se 1 (by rfl) ⟨10395494, by rfl⟩ : syracuseStep 13860659 = 20790989) B20790989
theorem B36961757 : Blo 2277435 36961757 := bstep (se 3 (by rfl) ⟨6930329, by rfl⟩ : syracuseStep 36961757 = 13860659) B13860659
theorem B24641171 : Blo 2277435 24641171 := bstep (se 1 (by rfl) ⟨18480878, by rfl⟩ : syracuseStep 24641171 = 36961757) B36961757
theorem B16427447 : Blo 2277435 16427447 := bstep (se 1 (by rfl) ⟨12320585, by rfl⟩ : syracuseStep 16427447 = 24641171) B24641171
theorem B10951631 : Blo 2277435 10951631 := bstep (se 1 (by rfl) ⟨8213723, by rfl⟩ : syracuseStep 10951631 = 16427447) B16427447
theorem B7301087 : Blo 2277435 7301087 := bstep (se 1 (by rfl) ⟨5475815, by rfl⟩ : syracuseStep 7301087 = 10951631) B10951631
theorem B4867391 : Blo 2277435 4867391 := bstep (se 1 (by rfl) ⟨3650543, by rfl⟩ : syracuseStep 4867391 = 7301087) B7301087
theorem B12979709 : Blo 2277435 12979709 := bstep (se 3 (by rfl) ⟨2433695, by rfl⟩ : syracuseStep 12979709 = 4867391) B4867391
theorem B8653139 : Blo 2277435 8653139 := bstep (se 1 (by rfl) ⟨6489854, by rfl⟩ : syracuseStep 8653139 = 12979709) B12979709
theorem B5768759 : Blo 2277435 5768759 := bstep (se 1 (by rfl) ⟨4326569, by rfl⟩ : syracuseStep 5768759 = 8653139) B8653139
theorem B3845839 : Blo 2277435 3845839 := bstep (se 1 (by rfl) ⟨2884379, by rfl⟩ : syracuseStep 3845839 = 5768759) B5768759
theorem B5127785 : Blo 2277435 5127785 := bstep (se 2 (by rfl) ⟨1922919, by rfl⟩ : syracuseStep 5127785 = 3845839) B3845839
theorem B3418523 : Blo 2277435 3418523 := bstep (se 1 (by rfl) ⟨2563892, by rfl⟩ : syracuseStep 3418523 = 5127785) B5127785
theorem B2279015 : Blo 2277435 2279015 := bstep (se 1 (by rfl) ⟨1709261, by rfl⟩ : syracuseStep 2279015 = 3418523) B3418523
theorem B2563897 : Blo 2277435 2563897 := bbase (se 2 (by rfl) ⟨961461, by rfl⟩ : syracuseStep 2563897 = 1922923) (by norm_num)
theorem B3418529 : Blo 2277435 3418529 := bstep (se 2 (by rfl) ⟨1281948, by rfl⟩ : syracuseStep 3418529 = 2563897) B2563897
theorem B2279019 : Blo 2277435 2279019 := bstep (se 1 (by rfl) ⟨1709264, by rfl⟩ : syracuseStep 2279019 = 3418529) B3418529
theorem B6489877 : Blo 2277435 6489877 := bbase (se 6 (by rfl) ⟨152106, by rfl⟩ : syracuseStep 6489877 = 304213) (by norm_num)
theorem B8653169 : Blo 2277435 8653169 := bstep (se 2 (by rfl) ⟨3244938, by rfl⟩ : syracuseStep 8653169 = 6489877) B6489877
theorem B5768779 : Blo 2277435 5768779 := bstep (se 1 (by rfl) ⟨4326584, by rfl⟩ : syracuseStep 5768779 = 8653169) B8653169
theorem B7691705 : Blo 2277435 7691705 := bstep (se 2 (by rfl) ⟨2884389, by rfl⟩ : syracuseStep 7691705 = 5768779) B5768779
theorem B5127803 : Blo 2277435 5127803 := bstep (se 1 (by rfl) ⟨3845852, by rfl⟩ : syracuseStep 5127803 = 7691705) B7691705
theorem B3418535 : Blo 2277435 3418535 := bstep (se 1 (by rfl) ⟨2563901, by rfl⟩ : syracuseStep 3418535 = 5127803) B5127803
theorem B2279023 : Blo 2277435 2279023 := bstep (se 1 (by rfl) ⟨1709267, by rfl⟩ : syracuseStep 2279023 = 3418535) B3418535
theorem B3418541 : Blo 2277435 3418541 := bbase (se 3 (by rfl) ⟨640976, by rfl⟩ : syracuseStep 3418541 = 1281953) (by norm_num)
theorem B2279027 : Blo 2277435 2279027 := bstep (se 1 (by rfl) ⟨1709270, by rfl⟩ : syracuseStep 2279027 = 3418541) B3418541
theorem B5127821 : Blo 2277435 5127821 := bbase (se 3 (by rfl) ⟨961466, by rfl⟩ : syracuseStep 5127821 = 1922933) (by norm_num)
theorem B3418547 : Blo 2277435 3418547 := bstep (se 1 (by rfl) ⟨2563910, by rfl⟩ : syracuseStep 3418547 = 5127821) B5127821
theorem B2279031 : Blo 2277435 2279031 := bstep (se 1 (by rfl) ⟨1709273, by rfl⟩ : syracuseStep 2279031 = 3418547) B3418547
theorem B2884405 : Blo 2277435 2884405 := bbase (se 5 (by rfl) ⟨135206, by rfl⟩ : syracuseStep 2884405 = 270413) (by norm_num)
theorem B3845873 : Blo 2277435 3845873 := bstep (se 2 (by rfl) ⟨1442202, by rfl⟩ : syracuseStep 3845873 = 2884405) B2884405
theorem B2563915 : Blo 2277435 2563915 := bstep (se 1 (by rfl) ⟨1922936, by rfl⟩ : syracuseStep 2563915 = 3845873) B3845873
theorem B3418553 : Blo 2277435 3418553 := bstep (se 2 (by rfl) ⟨1281957, by rfl⟩ : syracuseStep 3418553 = 2563915) B2563915
theorem B2279035 : Blo 2277435 2279035 := bstep (se 1 (by rfl) ⟨1709276, by rfl⟩ : syracuseStep 2279035 = 3418553) B3418553
theorem B7604101 : Blo 2277435 7604101 := bbase (se 4 (by rfl) ⟨712884, by rfl⟩ : syracuseStep 7604101 = 1425769) (by norm_num)
theorem B40555205 : Blo 2277435 40555205 := bstep (se 4 (by rfl) ⟨3802050, by rfl⟩ : syracuseStep 40555205 = 7604101) B7604101
theorem B27036803 : Blo 2277435 27036803 := bstep (se 1 (by rfl) ⟨20277602, by rfl⟩ : syracuseStep 27036803 = 40555205) B40555205
theorem B18024535 : Blo 2277435 18024535 := bstep (se 1 (by rfl) ⟨13518401, by rfl⟩ : syracuseStep 18024535 = 27036803) B27036803
theorem B24032713 : Blo 2277435 24032713 := bstep (se 2 (by rfl) ⟨9012267, by rfl⟩ : syracuseStep 24032713 = 18024535) B18024535
theorem B32043617 : Blo 2277435 32043617 := bstep (se 2 (by rfl) ⟨12016356, by rfl⟩ : syracuseStep 32043617 = 24032713) B24032713
theorem B21362411 : Blo 2277435 21362411 := bstep (se 1 (by rfl) ⟨16021808, by rfl⟩ : syracuseStep 21362411 = 32043617) B32043617
theorem B56966429 : Blo 2277435 56966429 := bstep (se 3 (by rfl) ⟨10681205, by rfl⟩ : syracuseStep 56966429 = 21362411) B21362411
theorem B151910477 : Blo 2277435 151910477 := bstep (se 3 (by rfl) ⟨28483214, by rfl⟩ : syracuseStep 151910477 = 56966429) B56966429
theorem B101273651 : Blo 2277435 101273651 := bstep (se 1 (by rfl) ⟨75955238, by rfl⟩ : syracuseStep 101273651 = 151910477) B151910477
theorem B67515767 : Blo 2277435 67515767 := bstep (se 1 (by rfl) ⟨50636825, by rfl⟩ : syracuseStep 67515767 = 101273651) B101273651
theorem B45010511 : Blo 2277435 45010511 := bstep (se 1 (by rfl) ⟨33757883, by rfl⟩ : syracuseStep 45010511 = 67515767) B67515767
theorem B30007007 : Blo 2277435 30007007 := bstep (se 1 (by rfl) ⟨22505255, by rfl⟩ : syracuseStep 30007007 = 45010511) B45010511
theorem B20004671 : Blo 2277435 20004671 := bstep (se 1 (by rfl) ⟨15003503, by rfl⟩ : syracuseStep 20004671 = 30007007) B30007007
theorem B13336447 : Blo 2277435 13336447 := bstep (se 1 (by rfl) ⟨10002335, by rfl⟩ : syracuseStep 13336447 = 20004671) B20004671
theorem B17781929 : Blo 2277435 17781929 := bstep (se 2 (by rfl) ⟨6668223, by rfl⟩ : syracuseStep 17781929 = 13336447) B13336447
theorem B11854619 : Blo 2277435 11854619 := bstep (se 1 (by rfl) ⟨8890964, by rfl⟩ : syracuseStep 11854619 = 17781929) B17781929
theorem B7903079 : Blo 2277435 7903079 := bstep (se 1 (by rfl) ⟨5927309, by rfl⟩ : syracuseStep 7903079 = 11854619) B11854619
theorem B5268719 : Blo 2277435 5268719 := bstep (se 1 (by rfl) ⟨3951539, by rfl⟩ : syracuseStep 5268719 = 7903079) B7903079
theorem B3512479 : Blo 2277435 3512479 := bstep (se 1 (by rfl) ⟨2634359, by rfl⟩ : syracuseStep 3512479 = 5268719) B5268719
theorem B4683305 : Blo 2277435 4683305 := bstep (se 2 (by rfl) ⟨1756239, by rfl⟩ : syracuseStep 4683305 = 3512479) B3512479
theorem B12488813 : Blo 2277435 12488813 := bstep (se 3 (by rfl) ⟨2341652, by rfl⟩ : syracuseStep 12488813 = 4683305) B4683305
theorem B8325875 : Blo 2277435 8325875 := bstep (se 1 (by rfl) ⟨6244406, by rfl⟩ : syracuseStep 8325875 = 12488813) B12488813
theorem B22202333 : Blo 2277435 22202333 := bstep (se 3 (by rfl) ⟨4162937, by rfl⟩ : syracuseStep 22202333 = 8325875) B8325875
theorem B14801555 : Blo 2277435 14801555 := bstep (se 1 (by rfl) ⟨11101166, by rfl⟩ : syracuseStep 14801555 = 22202333) B22202333
theorem B9867703 : Blo 2277435 9867703 := bstep (se 1 (by rfl) ⟨7400777, by rfl⟩ : syracuseStep 9867703 = 14801555) B14801555
theorem B13156937 : Blo 2277435 13156937 := bstep (se 2 (by rfl) ⟨4933851, by rfl⟩ : syracuseStep 13156937 = 9867703) B9867703
theorem B8771291 : Blo 2277435 8771291 := bstep (se 1 (by rfl) ⟨6578468, by rfl⟩ : syracuseStep 8771291 = 13156937) B13156937
theorem B5847527 : Blo 2277435 5847527 := bstep (se 1 (by rfl) ⟨4385645, by rfl⟩ : syracuseStep 5847527 = 8771291) B8771291
theorem B3898351 : Blo 2277435 3898351 := bstep (se 1 (by rfl) ⟨2923763, by rfl⟩ : syracuseStep 3898351 = 5847527) B5847527
theorem B5197801 : Blo 2277435 5197801 := bstep (se 2 (by rfl) ⟨1949175, by rfl⟩ : syracuseStep 5197801 = 3898351) B3898351
theorem B6930401 : Blo 2277435 6930401 := bstep (se 2 (by rfl) ⟨2598900, by rfl⟩ : syracuseStep 6930401 = 5197801) B5197801
theorem B18481069 : Blo 2277435 18481069 := bstep (se 3 (by rfl) ⟨3465200, by rfl⟩ : syracuseStep 18481069 = 6930401) B6930401
theorem B24641425 : Blo 2277435 24641425 := bstep (se 2 (by rfl) ⟨9240534, by rfl⟩ : syracuseStep 24641425 = 18481069) B18481069
theorem B32855233 : Blo 2277435 32855233 := bstep (se 2 (by rfl) ⟨12320712, by rfl⟩ : syracuseStep 32855233 = 24641425) B24641425
theorem B43806977 : Blo 2277435 43806977 := bstep (se 2 (by rfl) ⟨16427616, by rfl⟩ : syracuseStep 43806977 = 32855233) B32855233
theorem B29204651 : Blo 2277435 29204651 := bstep (se 1 (by rfl) ⟨21903488, by rfl⟩ : syracuseStep 29204651 = 43806977) B43806977
theorem B19469767 : Blo 2277435 19469767 := bstep (se 1 (by rfl) ⟨14602325, by rfl⟩ : syracuseStep 19469767 = 29204651) B29204651
theorem B25959689 : Blo 2277435 25959689 := bstep (se 2 (by rfl) ⟨9734883, by rfl⟩ : syracuseStep 25959689 = 19469767) B19469767
theorem B17306459 : Blo 2277435 17306459 := bstep (se 1 (by rfl) ⟨12979844, by rfl⟩ : syracuseStep 17306459 = 25959689) B25959689
theorem B11537639 : Blo 2277435 11537639 := bstep (se 1 (by rfl) ⟨8653229, by rfl⟩ : syracuseStep 11537639 = 17306459) B17306459
theorem B7691759 : Blo 2277435 7691759 := bstep (se 1 (by rfl) ⟨5768819, by rfl⟩ : syracuseStep 7691759 = 11537639) B11537639
theorem B5127839 : Blo 2277435 5127839 := bstep (se 1 (by rfl) ⟨3845879, by rfl⟩ : syracuseStep 5127839 = 7691759) B7691759
theorem B3418559 : Blo 2277435 3418559 := bstep (se 1 (by rfl) ⟨2563919, by rfl⟩ : syracuseStep 3418559 = 5127839) B5127839
theorem B2279039 : Blo 2277435 2279039 := bstep (se 1 (by rfl) ⟨1709279, by rfl⟩ : syracuseStep 2279039 = 3418559) B3418559
theorem B3418565 : Blo 2277435 3418565 := bbase (se 4 (by rfl) ⟨320490, by rfl⟩ : syracuseStep 3418565 = 640981) (by norm_num)
theorem B2279043 : Blo 2277435 2279043 := bstep (se 1 (by rfl) ⟨1709282, by rfl⟩ : syracuseStep 2279043 = 3418565) B3418565
theorem B3845893 : Blo 2277435 3845893 := bbase (se 4 (by rfl) ⟨360552, by rfl⟩ : syracuseStep 3845893 = 721105) (by norm_num)
theorem B5127857 : Blo 2277435 5127857 := bstep (se 2 (by rfl) ⟨1922946, by rfl⟩ : syracuseStep 5127857 = 3845893) B3845893
theorem B3418571 : Blo 2277435 3418571 := bstep (se 1 (by rfl) ⟨2563928, by rfl⟩ : syracuseStep 3418571 = 5127857) B5127857
theorem B2279047 : Blo 2277435 2279047 := bstep (se 1 (by rfl) ⟨1709285, by rfl⟩ : syracuseStep 2279047 = 3418571) B3418571
theorem B2563933 : Blo 2277435 2563933 := bbase (se 3 (by rfl) ⟨480737, by rfl⟩ : syracuseStep 2563933 = 961475) (by norm_num)
theorem B3418577 : Blo 2277435 3418577 := bstep (se 2 (by rfl) ⟨1281966, by rfl⟩ : syracuseStep 3418577 = 2563933) B2563933
theorem B2279051 : Blo 2277435 2279051 := bstep (se 1 (by rfl) ⟨1709288, by rfl⟩ : syracuseStep 2279051 = 3418577) B3418577
theorem B7691813 : Blo 2277435 7691813 := bbase (se 4 (by rfl) ⟨721107, by rfl⟩ : syracuseStep 7691813 = 1442215) (by norm_num)
theorem B5127875 : Blo 2277435 5127875 := bstep (se 1 (by rfl) ⟨3845906, by rfl⟩ : syracuseStep 5127875 = 7691813) B7691813
theorem B3418583 : Blo 2277435 3418583 := bstep (se 1 (by rfl) ⟨2563937, by rfl⟩ : syracuseStep 3418583 = 5127875) B5127875
theorem B2279055 : Blo 2277435 2279055 := bstep (se 1 (by rfl) ⟨1709291, by rfl⟩ : syracuseStep 2279055 = 3418583) B3418583
theorem B3418589 : Blo 2277435 3418589 := bbase (se 3 (by rfl) ⟨640985, by rfl⟩ : syracuseStep 3418589 = 1281971) (by norm_num)
theorem B2279059 : Blo 2277435 2279059 := bstep (se 1 (by rfl) ⟨1709294, by rfl⟩ : syracuseStep 2279059 = 3418589) B3418589
theorem B5127893 : Blo 2277435 5127893 := bbase (se 7 (by rfl) ⟨60092, by rfl⟩ : syracuseStep 5127893 = 120185) (by norm_num)
theorem B3418595 : Blo 2277435 3418595 := bstep (se 1 (by rfl) ⟨2563946, by rfl⟩ : syracuseStep 3418595 = 5127893) B5127893
theorem B2279063 : Blo 2277435 2279063 := bstep (se 1 (by rfl) ⟨1709297, by rfl⟩ : syracuseStep 2279063 = 3418595) B3418595
theorem B5475941 : Blo 2277435 5475941 := bbase (se 4 (by rfl) ⟨513369, by rfl⟩ : syracuseStep 5475941 = 1026739) (by norm_num)
theorem B3650627 : Blo 2277435 3650627 := bstep (se 1 (by rfl) ⟨2737970, by rfl⟩ : syracuseStep 3650627 = 5475941) B5475941
theorem B9735005 : Blo 2277435 9735005 := bstep (se 3 (by rfl) ⟨1825313, by rfl⟩ : syracuseStep 9735005 = 3650627) B3650627
theorem B6490003 : Blo 2277435 6490003 := bstep (se 1 (by rfl) ⟨4867502, by rfl⟩ : syracuseStep 6490003 = 9735005) B9735005
theorem B8653337 : Blo 2277435 8653337 := bstep (se 2 (by rfl) ⟨3245001, by rfl⟩ : syracuseStep 8653337 = 6490003) B6490003
theorem B5768891 : Blo 2277435 5768891 := bstep (se 1 (by rfl) ⟨4326668, by rfl⟩ : syracuseStep 5768891 = 8653337) B8653337
theorem B3845927 : Blo 2277435 3845927 := bstep (se 1 (by rfl) ⟨2884445, by rfl⟩ : syracuseStep 3845927 = 5768891) B5768891
theorem B2563951 : Blo 2277435 2563951 := bstep (se 1 (by rfl) ⟨1922963, by rfl⟩ : syracuseStep 2563951 = 3845927) B3845927
theorem B3418601 : Blo 2277435 3418601 := bstep (se 2 (by rfl) ⟨1281975, by rfl⟩ : syracuseStep 3418601 = 2563951) B2563951
theorem B2279067 : Blo 2277435 2279067 := bstep (se 1 (by rfl) ⟨1709300, by rfl⟩ : syracuseStep 2279067 = 3418601) B3418601
theorem B21903797 : Blo 2277435 21903797 := bbase (se 5 (by rfl) ⟨1026740, by rfl⟩ : syracuseStep 21903797 = 2053481) (by norm_num)
theorem B14602531 : Blo 2277435 14602531 := bstep (se 1 (by rfl) ⟨10951898, by rfl⟩ : syracuseStep 14602531 = 21903797) B21903797
theorem B19470041 : Blo 2277435 19470041 := bstep (se 2 (by rfl) ⟨7301265, by rfl⟩ : syracuseStep 19470041 = 14602531) B14602531
theorem B12980027 : Blo 2277435 12980027 := bstep (se 1 (by rfl) ⟨9735020, by rfl⟩ : syracuseStep 12980027 = 19470041) B19470041
theorem B8653351 : Blo 2277435 8653351 := bstep (se 1 (by rfl) ⟨6490013, by rfl⟩ : syracuseStep 8653351 = 12980027) B12980027
theorem B11537801 : Blo 2277435 11537801 := bstep (se 2 (by rfl) ⟨4326675, by rfl⟩ : syracuseStep 11537801 = 8653351) B8653351
theorem B7691867 : Blo 2277435 7691867 := bstep (se 1 (by rfl) ⟨5768900, by rfl⟩ : syracuseStep 7691867 = 11537801) B11537801
theorem B5127911 : Blo 2277435 5127911 := bstep (se 1 (by rfl) ⟨3845933, by rfl⟩ : syracuseStep 5127911 = 7691867) B7691867
theorem B3418607 : Blo 2277435 3418607 := bstep (se 1 (by rfl) ⟨2563955, by rfl⟩ : syracuseStep 3418607 = 5127911) B5127911
theorem B2279071 : Blo 2277435 2279071 := bstep (se 1 (by rfl) ⟨1709303, by rfl⟩ : syracuseStep 2279071 = 3418607) B3418607
theorem B3418613 : Blo 2277435 3418613 := bbase (se 5 (by rfl) ⟨160247, by rfl⟩ : syracuseStep 3418613 = 320495) (by norm_num)
theorem B2279075 : Blo 2277435 2279075 := bstep (se 1 (by rfl) ⟨1709306, by rfl⟩ : syracuseStep 2279075 = 3418613) B3418613
theorem B6490037 : Blo 2277435 6490037 := bbase (se 5 (by rfl) ⟨304220, by rfl⟩ : syracuseStep 6490037 = 608441) (by norm_num)
theorem B4326691 : Blo 2277435 4326691 := bstep (se 1 (by rfl) ⟨3245018, by rfl⟩ : syracuseStep 4326691 = 6490037) B6490037
theorem B5768921 : Blo 2277435 5768921 := bstep (se 2 (by rfl) ⟨2163345, by rfl⟩ : syracuseStep 5768921 = 4326691) B4326691
theorem B3845947 : Blo 2277435 3845947 := bstep (se 1 (by rfl) ⟨2884460, by rfl⟩ : syracuseStep 3845947 = 5768921) B5768921
theorem B5127929 : Blo 2277435 5127929 := bstep (se 2 (by rfl) ⟨1922973, by rfl⟩ : syracuseStep 5127929 = 3845947) B3845947
theorem B3418619 : Blo 2277435 3418619 := bstep (se 1 (by rfl) ⟨2563964, by rfl⟩ : syracuseStep 3418619 = 5127929) B5127929
theorem B2279079 : Blo 2277435 2279079 := bstep (se 1 (by rfl) ⟨1709309, by rfl⟩ : syracuseStep 2279079 = 3418619) B3418619
theorem B2563969 : Blo 2277435 2563969 := bbase (se 2 (by rfl) ⟨961488, by rfl⟩ : syracuseStep 2563969 = 1922977) (by norm_num)
theorem B3418625 : Blo 2277435 3418625 := bstep (se 2 (by rfl) ⟨1281984, by rfl⟩ : syracuseStep 3418625 = 2563969) B2563969
theorem B2279083 : Blo 2277435 2279083 := bstep (se 1 (by rfl) ⟨1709312, by rfl⟩ : syracuseStep 2279083 = 3418625) B3418625
theorem B5768941 : Blo 2277435 5768941 := bbase (se 3 (by rfl) ⟨1081676, by rfl⟩ : syracuseStep 5768941 = 2163353) (by norm_num)
theorem B7691921 : Blo 2277435 7691921 := bstep (se 2 (by rfl) ⟨2884470, by rfl⟩ : syracuseStep 7691921 = 5768941) B5768941
theorem B5127947 : Blo 2277435 5127947 := bstep (se 1 (by rfl) ⟨3845960, by rfl⟩ : syracuseStep 5127947 = 7691921) B7691921
theorem B3418631 : Blo 2277435 3418631 := bstep (se 1 (by rfl) ⟨2563973, by rfl⟩ : syracuseStep 3418631 = 5127947) B5127947
theorem B2279087 : Blo 2277435 2279087 := bstep (se 1 (by rfl) ⟨1709315, by rfl⟩ : syracuseStep 2279087 = 3418631) B3418631
theorem B3418637 : Blo 2277435 3418637 := bbase (se 3 (by rfl) ⟨640994, by rfl⟩ : syracuseStep 3418637 = 1281989) (by norm_num)
theorem B2279091 : Blo 2277435 2279091 := bstep (se 1 (by rfl) ⟨1709318, by rfl⟩ : syracuseStep 2279091 = 3418637) B3418637
theorem B5127965 : Blo 2277435 5127965 := bbase (se 3 (by rfl) ⟨961493, by rfl⟩ : syracuseStep 5127965 = 1922987) (by norm_num)
theorem B3418643 : Blo 2277435 3418643 := bstep (se 1 (by rfl) ⟨2563982, by rfl⟩ : syracuseStep 3418643 = 5127965) B5127965
theorem B2279095 : Blo 2277435 2279095 := bstep (se 1 (by rfl) ⟨1709321, by rfl⟩ : syracuseStep 2279095 = 3418643) B3418643
theorem B3845981 : Blo 2277435 3845981 := bbase (se 3 (by rfl) ⟨721121, by rfl⟩ : syracuseStep 3845981 = 1442243) (by norm_num)
theorem B2563987 : Blo 2277435 2563987 := bstep (se 1 (by rfl) ⟨1922990, by rfl⟩ : syracuseStep 2563987 = 3845981) B3845981
theorem B3418649 : Blo 2277435 3418649 := bstep (se 2 (by rfl) ⟨1281993, by rfl⟩ : syracuseStep 3418649 = 2563987) B2563987
theorem B2279099 : Blo 2277435 2279099 := bstep (se 1 (by rfl) ⟨1709324, by rfl⟩ : syracuseStep 2279099 = 3418649) B3418649
theorem B9735157 : Blo 2277435 9735157 := bbase (se 5 (by rfl) ⟨456335, by rfl⟩ : syracuseStep 9735157 = 912671) (by norm_num)
theorem B12980209 : Blo 2277435 12980209 := bstep (se 2 (by rfl) ⟨4867578, by rfl⟩ : syracuseStep 12980209 = 9735157) B9735157
theorem B17306945 : Blo 2277435 17306945 := bstep (se 2 (by rfl) ⟨6490104, by rfl⟩ : syracuseStep 17306945 = 12980209) B12980209
theorem B11537963 : Blo 2277435 11537963 := bstep (se 1 (by rfl) ⟨8653472, by rfl⟩ : syracuseStep 11537963 = 17306945) B17306945
theorem B7691975 : Blo 2277435 7691975 := bstep (se 1 (by rfl) ⟨5768981, by rfl⟩ : syracuseStep 7691975 = 11537963) B11537963
theorem B5127983 : Blo 2277435 5127983 := bstep (se 1 (by rfl) ⟨3845987, by rfl⟩ : syracuseStep 5127983 = 7691975) B7691975
theorem B3418655 : Blo 2277435 3418655 := bstep (se 1 (by rfl) ⟨2563991, by rfl⟩ : syracuseStep 3418655 = 5127983) B5127983
theorem B2279103 : Blo 2277435 2279103 := bstep (se 1 (by rfl) ⟨1709327, by rfl⟩ : syracuseStep 2279103 = 3418655) B3418655
theorem B3418661 : Blo 2277435 3418661 := bbase (se 4 (by rfl) ⟨320499, by rfl⟩ : syracuseStep 3418661 = 640999) (by norm_num)
theorem B2279107 : Blo 2277435 2279107 := bstep (se 1 (by rfl) ⟨1709330, by rfl⟩ : syracuseStep 2279107 = 3418661) B3418661
theorem B2884501 : Blo 2277435 2884501 := bbase (se 6 (by rfl) ⟨67605, by rfl⟩ : syracuseStep 2884501 = 135211) (by norm_num)
theorem B3846001 : Blo 2277435 3846001 := bstep (se 2 (by rfl) ⟨1442250, by rfl⟩ : syracuseStep 3846001 = 2884501) B2884501
theorem B5128001 : Blo 2277435 5128001 := bstep (se 2 (by rfl) ⟨1923000, by rfl⟩ : syracuseStep 5128001 = 3846001) B3846001
theorem B3418667 : Blo 2277435 3418667 := bstep (se 1 (by rfl) ⟨2564000, by rfl⟩ : syracuseStep 3418667 = 5128001) B5128001
theorem B2279111 : Blo 2277435 2279111 := bstep (se 1 (by rfl) ⟨1709333, by rfl⟩ : syracuseStep 2279111 = 3418667) B3418667
theorem B2564005 : Blo 2277435 2564005 := bbase (se 4 (by rfl) ⟨240375, by rfl⟩ : syracuseStep 2564005 = 480751) (by norm_num)
theorem B3418673 : Blo 2277435 3418673 := bstep (se 2 (by rfl) ⟨1282002, by rfl⟩ : syracuseStep 3418673 = 2564005) B2564005
theorem B2279115 : Blo 2277435 2279115 := bstep (se 1 (by rfl) ⟨1709336, by rfl⟩ : syracuseStep 2279115 = 3418673) B3418673
theorem B5550781 : Blo 2277435 5550781 := bbase (se 3 (by rfl) ⟨1040771, by rfl⟩ : syracuseStep 5550781 = 2081543) (by norm_num)
theorem B7401041 : Blo 2277435 7401041 := bstep (se 2 (by rfl) ⟨2775390, by rfl⟩ : syracuseStep 7401041 = 5550781) B5550781
theorem B4934027 : Blo 2277435 4934027 := bstep (se 1 (by rfl) ⟨3700520, by rfl⟩ : syracuseStep 4934027 = 7401041) B7401041
theorem B3289351 : Blo 2277435 3289351 := bstep (se 1 (by rfl) ⟨2467013, by rfl⟩ : syracuseStep 3289351 = 4934027) B4934027
theorem B4385801 : Blo 2277435 4385801 := bstep (se 2 (by rfl) ⟨1644675, by rfl⟩ : syracuseStep 4385801 = 3289351) B3289351
theorem B2923867 : Blo 2277435 2923867 := bstep (se 1 (by rfl) ⟨2192900, by rfl⟩ : syracuseStep 2923867 = 4385801) B4385801
theorem B15593957 : Blo 2277435 15593957 := bstep (se 4 (by rfl) ⟨1461933, by rfl⟩ : syracuseStep 15593957 = 2923867) B2923867
theorem B10395971 : Blo 2277435 10395971 := bstep (se 1 (by rfl) ⟨7796978, by rfl⟩ : syracuseStep 10395971 = 15593957) B15593957
theorem B6930647 : Blo 2277435 6930647 := bstep (se 1 (by rfl) ⟨5197985, by rfl⟩ : syracuseStep 6930647 = 10395971) B10395971
theorem B4620431 : Blo 2277435 4620431 := bstep (se 1 (by rfl) ⟨3465323, by rfl⟩ : syracuseStep 4620431 = 6930647) B6930647
theorem B3080287 : Blo 2277435 3080287 := bstep (se 1 (by rfl) ⟨2310215, by rfl⟩ : syracuseStep 3080287 = 4620431) B4620431
theorem B16428197 : Blo 2277435 16428197 := bstep (se 4 (by rfl) ⟨1540143, by rfl⟩ : syracuseStep 16428197 = 3080287) B3080287
theorem B10952131 : Blo 2277435 10952131 := bstep (se 1 (by rfl) ⟨8214098, by rfl⟩ : syracuseStep 10952131 = 16428197) B16428197
theorem B14602841 : Blo 2277435 14602841 := bstep (se 2 (by rfl) ⟨5476065, by rfl⟩ : syracuseStep 14602841 = 10952131) B10952131
theorem B9735227 : Blo 2277435 9735227 := bstep (se 1 (by rfl) ⟨7301420, by rfl⟩ : syracuseStep 9735227 = 14602841) B14602841
theorem B6490151 : Blo 2277435 6490151 := bstep (se 1 (by rfl) ⟨4867613, by rfl⟩ : syracuseStep 6490151 = 9735227) B9735227
theorem B4326767 : Blo 2277435 4326767 := bstep (se 1 (by rfl) ⟨3245075, by rfl⟩ : syracuseStep 4326767 = 6490151) B6490151
theorem B2884511 : Blo 2277435 2884511 := bstep (se 1 (by rfl) ⟨2163383, by rfl⟩ : syracuseStep 2884511 = 4326767) B4326767
theorem B7692029 : Blo 2277435 7692029 := bstep (se 3 (by rfl) ⟨1442255, by rfl⟩ : syracuseStep 7692029 = 2884511) B2884511
theorem B5128019 : Blo 2277435 5128019 := bstep (se 1 (by rfl) ⟨3846014, by rfl⟩ : syracuseStep 5128019 = 7692029) B7692029
theorem B3418679 : Blo 2277435 3418679 := bstep (se 1 (by rfl) ⟨2564009, by rfl⟩ : syracuseStep 3418679 = 5128019) B5128019
theorem B2279119 : Blo 2277435 2279119 := bstep (se 1 (by rfl) ⟨1709339, by rfl⟩ : syracuseStep 2279119 = 3418679) B3418679
theorem B3418685 : Blo 2277435 3418685 := bbase (se 3 (by rfl) ⟨641003, by rfl⟩ : syracuseStep 3418685 = 1282007) (by norm_num)
theorem B2279123 : Blo 2277435 2279123 := bstep (se 1 (by rfl) ⟨1709342, by rfl⟩ : syracuseStep 2279123 = 3418685) B3418685
theorem B5128037 : Blo 2277435 5128037 := bbase (se 4 (by rfl) ⟨480753, by rfl⟩ : syracuseStep 5128037 = 961507) (by norm_num)
theorem B3418691 : Blo 2277435 3418691 := bstep (se 1 (by rfl) ⟨2564018, by rfl⟩ : syracuseStep 3418691 = 5128037) B5128037
theorem B2279127 : Blo 2277435 2279127 := bstep (se 1 (by rfl) ⟨1709345, by rfl⟩ : syracuseStep 2279127 = 3418691) B3418691
theorem B5769053 : Blo 2277435 5769053 := bbase (se 3 (by rfl) ⟨1081697, by rfl⟩ : syracuseStep 5769053 = 2163395) (by norm_num)
theorem B3846035 : Blo 2277435 3846035 := bstep (se 1 (by rfl) ⟨2884526, by rfl⟩ : syracuseStep 3846035 = 5769053) B5769053
theorem B2564023 : Blo 2277435 2564023 := bstep (se 1 (by rfl) ⟨1923017, by rfl⟩ : syracuseStep 2564023 = 3846035) B3846035
theorem B3418697 : Blo 2277435 3418697 := bstep (se 2 (by rfl) ⟨1282011, by rfl⟩ : syracuseStep 3418697 = 2564023) B2564023
theorem B2279131 : Blo 2277435 2279131 := bstep (se 1 (by rfl) ⟨1709348, by rfl⟩ : syracuseStep 2279131 = 3418697) B3418697
theorem B4326797 : Blo 2277435 4326797 := bbase (se 3 (by rfl) ⟨811274, by rfl⟩ : syracuseStep 4326797 = 1622549) (by norm_num)
theorem B11538125 : Blo 2277435 11538125 := bstep (se 3 (by rfl) ⟨2163398, by rfl⟩ : syracuseStep 11538125 = 4326797) B4326797
theorem B7692083 : Blo 2277435 7692083 := bstep (se 1 (by rfl) ⟨5769062, by rfl⟩ : syracuseStep 7692083 = 11538125) B11538125
theorem B5128055 : Blo 2277435 5128055 := bstep (se 1 (by rfl) ⟨3846041, by rfl⟩ : syracuseStep 5128055 = 7692083) B7692083
theorem B3418703 : Blo 2277435 3418703 := bstep (se 1 (by rfl) ⟨2564027, by rfl⟩ : syracuseStep 3418703 = 5128055) B5128055
theorem B2279135 : Blo 2277435 2279135 := bstep (se 1 (by rfl) ⟨1709351, by rfl⟩ : syracuseStep 2279135 = 3418703) B3418703
theorem B3418709 : Blo 2277435 3418709 := bbase (se 8 (by rfl) ⟨20031, by rfl⟩ : syracuseStep 3418709 = 40063) (by norm_num)
theorem B2279139 : Blo 2277435 2279139 := bstep (se 1 (by rfl) ⟨1709354, by rfl⟩ : syracuseStep 2279139 = 3418709) B3418709
theorem B4934077 : Blo 2277435 4934077 := bbase (se 3 (by rfl) ⟨925139, by rfl⟩ : syracuseStep 4934077 = 1850279) (by norm_num)
theorem B105260309 : Blo 2277435 105260309 := bstep (se 6 (by rfl) ⟨2467038, by rfl⟩ : syracuseStep 105260309 = 4934077) B4934077
theorem B70173539 : Blo 2277435 70173539 := bstep (se 1 (by rfl) ⟨52630154, by rfl⟩ : syracuseStep 70173539 = 105260309) B105260309
theorem B46782359 : Blo 2277435 46782359 := bstep (se 1 (by rfl) ⟨35086769, by rfl⟩ : syracuseStep 46782359 = 70173539) B70173539
theorem B31188239 : Blo 2277435 31188239 := bstep (se 1 (by rfl) ⟨23391179, by rfl⟩ : syracuseStep 31188239 = 46782359) B46782359
theorem B20792159 : Blo 2277435 20792159 := bstep (se 1 (by rfl) ⟨15594119, by rfl⟩ : syracuseStep 20792159 = 31188239) B31188239
theorem B13861439 : Blo 2277435 13861439 := bstep (se 1 (by rfl) ⟨10396079, by rfl⟩ : syracuseStep 13861439 = 20792159) B20792159
theorem B9240959 : Blo 2277435 9240959 := bstep (se 1 (by rfl) ⟨6930719, by rfl⟩ : syracuseStep 9240959 = 13861439) B13861439
theorem B6160639 : Blo 2277435 6160639 := bstep (se 1 (by rfl) ⟨4620479, by rfl⟩ : syracuseStep 6160639 = 9240959) B9240959
theorem B8214185 : Blo 2277435 8214185 := bstep (se 2 (by rfl) ⟨3080319, by rfl⟩ : syracuseStep 8214185 = 6160639) B6160639
theorem B5476123 : Blo 2277435 5476123 := bstep (se 1 (by rfl) ⟨4107092, by rfl⟩ : syracuseStep 5476123 = 8214185) B8214185
theorem B7301497 : Blo 2277435 7301497 := bstep (se 2 (by rfl) ⟨2738061, by rfl⟩ : syracuseStep 7301497 = 5476123) B5476123
theorem B9735329 : Blo 2277435 9735329 := bstep (se 2 (by rfl) ⟨3650748, by rfl⟩ : syracuseStep 9735329 = 7301497) B7301497
theorem B6490219 : Blo 2277435 6490219 := bstep (se 1 (by rfl) ⟨4867664, by rfl⟩ : syracuseStep 6490219 = 9735329) B9735329
theorem B8653625 : Blo 2277435 8653625 := bstep (se 2 (by rfl) ⟨3245109, by rfl⟩ : syracuseStep 8653625 = 6490219) B6490219
theorem B5769083 : Blo 2277435 5769083 := bstep (se 1 (by rfl) ⟨4326812, by rfl⟩ : syracuseStep 5769083 = 8653625) B8653625
theorem B3846055 : Blo 2277435 3846055 := bstep (se 1 (by rfl) ⟨2884541, by rfl⟩ : syracuseStep 3846055 = 5769083) B5769083
theorem B5128073 : Blo 2277435 5128073 := bstep (se 2 (by rfl) ⟨1923027, by rfl⟩ : syracuseStep 5128073 = 3846055) B3846055
theorem B3418715 : Blo 2277435 3418715 := bstep (se 1 (by rfl) ⟨2564036, by rfl⟩ : syracuseStep 3418715 = 5128073) B5128073
theorem B2279143 : Blo 2277435 2279143 := bstep (se 1 (by rfl) ⟨1709357, by rfl⟩ : syracuseStep 2279143 = 3418715) B3418715
theorem B2564041 : Blo 2277435 2564041 := bbase (se 2 (by rfl) ⟨961515, by rfl⟩ : syracuseStep 2564041 = 1923031) (by norm_num)
theorem B3418721 : Blo 2277435 3418721 := bstep (se 2 (by rfl) ⟨1282020, by rfl⟩ : syracuseStep 3418721 = 2564041) B2564041
theorem B2279147 : Blo 2277435 2279147 := bstep (se 1 (by rfl) ⟨1709360, by rfl⟩ : syracuseStep 2279147 = 3418721) B3418721
theorem B6160661 : Blo 2277435 6160661 := bbase (se 6 (by rfl) ⟨144390, by rfl⟩ : syracuseStep 6160661 = 288781) (by norm_num)
theorem B4107107 : Blo 2277435 4107107 := bstep (se 1 (by rfl) ⟨3080330, by rfl⟩ : syracuseStep 4107107 = 6160661) B6160661
theorem B2738071 : Blo 2277435 2738071 := bstep (se 1 (by rfl) ⟨2053553, by rfl⟩ : syracuseStep 2738071 = 4107107) B4107107
theorem B3650761 : Blo 2277435 3650761 := bstep (se 2 (by rfl) ⟨1369035, by rfl⟩ : syracuseStep 3650761 = 2738071) B2738071
theorem B19470725 : Blo 2277435 19470725 := bstep (se 4 (by rfl) ⟨1825380, by rfl⟩ : syracuseStep 19470725 = 3650761) B3650761
theorem B12980483 : Blo 2277435 12980483 := bstep (se 1 (by rfl) ⟨9735362, by rfl⟩ : syracuseStep 12980483 = 19470725) B19470725
theorem B8653655 : Blo 2277435 8653655 := bstep (se 1 (by rfl) ⟨6490241, by rfl⟩ : syracuseStep 8653655 = 12980483) B12980483
theorem B5769103 : Blo 2277435 5769103 := bstep (se 1 (by rfl) ⟨4326827, by rfl⟩ : syracuseStep 5769103 = 8653655) B8653655
theorem B7692137 : Blo 2277435 7692137 := bstep (se 2 (by rfl) ⟨2884551, by rfl⟩ : syracuseStep 7692137 = 5769103) B5769103
theorem B5128091 : Blo 2277435 5128091 := bstep (se 1 (by rfl) ⟨3846068, by rfl⟩ : syracuseStep 5128091 = 7692137) B7692137
theorem B3418727 : Blo 2277435 3418727 := bstep (se 1 (by rfl) ⟨2564045, by rfl⟩ : syracuseStep 3418727 = 5128091) B5128091
theorem B2279151 : Blo 2277435 2279151 := bstep (se 1 (by rfl) ⟨1709363, by rfl⟩ : syracuseStep 2279151 = 3418727) B3418727
theorem B3418733 : Blo 2277435 3418733 := bbase (se 3 (by rfl) ⟨641012, by rfl⟩ : syracuseStep 3418733 = 1282025) (by norm_num)
theorem B2279155 : Blo 2277435 2279155 := bstep (se 1 (by rfl) ⟨1709366, by rfl⟩ : syracuseStep 2279155 = 3418733) B3418733
theorem B5128109 : Blo 2277435 5128109 := bbase (se 3 (by rfl) ⟨961520, by rfl⟩ : syracuseStep 5128109 = 1923041) (by norm_num)
theorem B3418739 : Blo 2277435 3418739 := bstep (se 1 (by rfl) ⟨2564054, by rfl⟩ : syracuseStep 3418739 = 5128109) B5128109
theorem B2279159 : Blo 2277435 2279159 := bstep (se 1 (by rfl) ⟨1709369, by rfl⟩ : syracuseStep 2279159 = 3418739) B3418739
theorem B6490277 : Blo 2277435 6490277 := bbase (se 4 (by rfl) ⟨608463, by rfl⟩ : syracuseStep 6490277 = 1216927) (by norm_num)
theorem B4326851 : Blo 2277435 4326851 := bstep (se 1 (by rfl) ⟨3245138, by rfl⟩ : syracuseStep 4326851 = 6490277) B6490277
theorem B2884567 : Blo 2277435 2884567 := bstep (se 1 (by rfl) ⟨2163425, by rfl⟩ : syracuseStep 2884567 = 4326851) B4326851
theorem B3846089 : Blo 2277435 3846089 := bstep (se 2 (by rfl) ⟨1442283, by rfl⟩ : syracuseStep 3846089 = 2884567) B2884567
theorem B2564059 : Blo 2277435 2564059 := bstep (se 1 (by rfl) ⟨1923044, by rfl⟩ : syracuseStep 2564059 = 3846089) B3846089
theorem B3418745 : Blo 2277435 3418745 := bstep (se 2 (by rfl) ⟨1282029, by rfl⟩ : syracuseStep 3418745 = 2564059) B2564059
theorem B2279163 : Blo 2277435 2279163 := bstep (se 1 (by rfl) ⟨1709372, by rfl⟩ : syracuseStep 2279163 = 3418745) B3418745
theorem B6578837 : Blo 2277435 6578837 := bbase (se 6 (by rfl) ⟨154191, by rfl⟩ : syracuseStep 6578837 = 308383) (by norm_num)
theorem B4385891 : Blo 2277435 4385891 := bstep (se 1 (by rfl) ⟨3289418, by rfl⟩ : syracuseStep 4385891 = 6578837) B6578837
theorem B11695709 : Blo 2277435 11695709 := bstep (se 3 (by rfl) ⟨2192945, by rfl⟩ : syracuseStep 11695709 = 4385891) B4385891
theorem B31188557 : Blo 2277435 31188557 := bstep (se 3 (by rfl) ⟨5847854, by rfl⟩ : syracuseStep 31188557 = 11695709) B11695709
theorem B20792371 : Blo 2277435 20792371 := bstep (se 1 (by rfl) ⟨15594278, by rfl⟩ : syracuseStep 20792371 = 31188557) B31188557
theorem B27723161 : Blo 2277435 27723161 := bstep (se 2 (by rfl) ⟨10396185, by rfl⟩ : syracuseStep 27723161 = 20792371) B20792371
theorem B18482107 : Blo 2277435 18482107 := bstep (se 1 (by rfl) ⟨13861580, by rfl⟩ : syracuseStep 18482107 = 27723161) B27723161
theorem B24642809 : Blo 2277435 24642809 := bstep (se 2 (by rfl) ⟨9241053, by rfl⟩ : syracuseStep 24642809 = 18482107) B18482107
theorem B16428539 : Blo 2277435 16428539 := bstep (se 1 (by rfl) ⟨12321404, by rfl⟩ : syracuseStep 16428539 = 24642809) B24642809
theorem B43809437 : Blo 2277435 43809437 := bstep (se 3 (by rfl) ⟨8214269, by rfl⟩ : syracuseStep 43809437 = 16428539) B16428539
theorem B29206291 : Blo 2277435 29206291 := bstep (se 1 (by rfl) ⟨21904718, by rfl⟩ : syracuseStep 29206291 = 43809437) B43809437
theorem B38941721 : Blo 2277435 38941721 := bstep (se 2 (by rfl) ⟨14603145, by rfl⟩ : syracuseStep 38941721 = 29206291) B29206291
theorem B25961147 : Blo 2277435 25961147 := bstep (se 1 (by rfl) ⟨19470860, by rfl⟩ : syracuseStep 25961147 = 38941721) B38941721
theorem B17307431 : Blo 2277435 17307431 := bstep (se 1 (by rfl) ⟨12980573, by rfl⟩ : syracuseStep 17307431 = 25961147) B25961147
theorem B11538287 : Blo 2277435 11538287 := bstep (se 1 (by rfl) ⟨8653715, by rfl⟩ : syracuseStep 11538287 = 17307431) B17307431
theorem B7692191 : Blo 2277435 7692191 := bstep (se 1 (by rfl) ⟨5769143, by rfl⟩ : syracuseStep 7692191 = 11538287) B11538287
theorem B5128127 : Blo 2277435 5128127 := bstep (se 1 (by rfl) ⟨3846095, by rfl⟩ : syracuseStep 5128127 = 7692191) B7692191
theorem B3418751 : Blo 2277435 3418751 := bstep (se 1 (by rfl) ⟨2564063, by rfl⟩ : syracuseStep 3418751 = 5128127) B5128127
theorem B2279167 : Blo 2277435 2279167 := bstep (se 1 (by rfl) ⟨1709375, by rfl⟩ : syracuseStep 2279167 = 3418751) B3418751
theorem B3418757 : Blo 2277435 3418757 := bbase (se 4 (by rfl) ⟨320508, by rfl⟩ : syracuseStep 3418757 = 641017) (by norm_num)
theorem B2279171 : Blo 2277435 2279171 := bstep (se 1 (by rfl) ⟨1709378, by rfl⟩ : syracuseStep 2279171 = 3418757) B3418757
theorem B3846109 : Blo 2277435 3846109 := bbase (se 3 (by rfl) ⟨721145, by rfl⟩ : syracuseStep 3846109 = 1442291) (by norm_num)
theorem B5128145 : Blo 2277435 5128145 := bstep (se 2 (by rfl) ⟨1923054, by rfl⟩ : syracuseStep 5128145 = 3846109) B3846109
theorem B3418763 : Blo 2277435 3418763 := bstep (se 1 (by rfl) ⟨2564072, by rfl⟩ : syracuseStep 3418763 = 5128145) B5128145
theorem B2279175 : Blo 2277435 2279175 := bstep (se 1 (by rfl) ⟨1709381, by rfl⟩ : syracuseStep 2279175 = 3418763) B3418763
theorem B2564077 : Blo 2277435 2564077 := bbase (se 3 (by rfl) ⟨480764, by rfl⟩ : syracuseStep 2564077 = 961529) (by norm_num)
theorem B3418769 : Blo 2277435 3418769 := bstep (se 2 (by rfl) ⟨1282038, by rfl⟩ : syracuseStep 3418769 = 2564077) B2564077
theorem B2279179 : Blo 2277435 2279179 := bstep (se 1 (by rfl) ⟨1709384, by rfl⟩ : syracuseStep 2279179 = 3418769) B3418769
theorem B7692245 : Blo 2277435 7692245 := bbase (se 7 (by rfl) ⟨90143, by rfl⟩ : syracuseStep 7692245 = 180287) (by norm_num)
theorem B5128163 : Blo 2277435 5128163 := bstep (se 1 (by rfl) ⟨3846122, by rfl⟩ : syracuseStep 5128163 = 7692245) B7692245
theorem B3418775 : Blo 2277435 3418775 := bstep (se 1 (by rfl) ⟨2564081, by rfl⟩ : syracuseStep 3418775 = 5128163) B5128163
theorem B2279183 : Blo 2277435 2279183 := bstep (se 1 (by rfl) ⟨1709387, by rfl⟩ : syracuseStep 2279183 = 3418775) B3418775
theorem B3418781 : Blo 2277435 3418781 := bbase (se 3 (by rfl) ⟨641021, by rfl⟩ : syracuseStep 3418781 = 1282043) (by norm_num)
theorem B2279187 : Blo 2277435 2279187 := bstep (se 1 (by rfl) ⟨1709390, by rfl⟩ : syracuseStep 2279187 = 3418781) B3418781
theorem B5128181 : Blo 2277435 5128181 := bbase (se 5 (by rfl) ⟨240383, by rfl⟩ : syracuseStep 5128181 = 480767) (by norm_num)
theorem B3418787 : Blo 2277435 3418787 := bstep (se 1 (by rfl) ⟨2564090, by rfl⟩ : syracuseStep 3418787 = 5128181) B5128181
theorem B2279191 : Blo 2277435 2279191 := bstep (se 1 (by rfl) ⟨1709393, by rfl⟩ : syracuseStep 2279191 = 3418787) B3418787
theorem B54077269 : Blo 2277435 54077269 := bbase (se 9 (by rfl) ⟨158429, by rfl⟩ : syracuseStep 54077269 = 316859) (by norm_num)
theorem B72103025 : Blo 2277435 72103025 := bstep (se 2 (by rfl) ⟨27038634, by rfl⟩ : syracuseStep 72103025 = 54077269) B54077269
theorem B48068683 : Blo 2277435 48068683 := bstep (se 1 (by rfl) ⟨36051512, by rfl⟩ : syracuseStep 48068683 = 72103025) B72103025
theorem B256366309 : Blo 2277435 256366309 := bstep (se 4 (by rfl) ⟨24034341, by rfl⟩ : syracuseStep 256366309 = 48068683) B48068683
theorem B341821745 : Blo 2277435 341821745 := bstep (se 2 (by rfl) ⟨128183154, by rfl⟩ : syracuseStep 341821745 = 256366309) B256366309
theorem B227881163 : Blo 2277435 227881163 := bstep (se 1 (by rfl) ⟨170910872, by rfl⟩ : syracuseStep 227881163 = 341821745) B341821745
theorem B151920775 : Blo 2277435 151920775 := bstep (se 1 (by rfl) ⟨113940581, by rfl⟩ : syracuseStep 151920775 = 227881163) B227881163
theorem B810244133 : Blo 2277435 810244133 := bstep (se 4 (by rfl) ⟨75960387, by rfl⟩ : syracuseStep 810244133 = 151920775) B151920775
theorem B540162755 : Blo 2277435 540162755 := bstep (se 1 (by rfl) ⟨405122066, by rfl⟩ : syracuseStep 540162755 = 810244133) B810244133
theorem B360108503 : Blo 2277435 360108503 := bstep (se 1 (by rfl) ⟨270081377, by rfl⟩ : syracuseStep 360108503 = 540162755) B540162755
theorem B240072335 : Blo 2277435 240072335 := bstep (se 1 (by rfl) ⟨180054251, by rfl⟩ : syracuseStep 240072335 = 360108503) B360108503
theorem B160048223 : Blo 2277435 160048223 := bstep (se 1 (by rfl) ⟨120036167, by rfl⟩ : syracuseStep 160048223 = 240072335) B240072335
theorem B106698815 : Blo 2277435 106698815 := bstep (se 1 (by rfl) ⟨80024111, by rfl⟩ : syracuseStep 106698815 = 160048223) B160048223
theorem B71132543 : Blo 2277435 71132543 := bstep (se 1 (by rfl) ⟨53349407, by rfl⟩ : syracuseStep 71132543 = 106698815) B106698815
theorem B47421695 : Blo 2277435 47421695 := bstep (se 1 (by rfl) ⟨35566271, by rfl⟩ : syracuseStep 47421695 = 71132543) B71132543
theorem B126457853 : Blo 2277435 126457853 := bstep (se 3 (by rfl) ⟨23710847, by rfl⟩ : syracuseStep 126457853 = 47421695) B47421695
theorem B337220941 : Blo 2277435 337220941 := bstep (se 3 (by rfl) ⟨63228926, by rfl⟩ : syracuseStep 337220941 = 126457853) B126457853
theorem B449627921 : Blo 2277435 449627921 := bstep (se 2 (by rfl) ⟨168610470, by rfl⟩ : syracuseStep 449627921 = 337220941) B337220941
theorem B299751947 : Blo 2277435 299751947 := bstep (se 1 (by rfl) ⟨224813960, by rfl⟩ : syracuseStep 299751947 = 449627921) B449627921
theorem B199834631 : Blo 2277435 199834631 := bstep (se 1 (by rfl) ⟨149875973, by rfl⟩ : syracuseStep 199834631 = 299751947) B299751947
theorem B133223087 : Blo 2277435 133223087 := bstep (se 1 (by rfl) ⟨99917315, by rfl⟩ : syracuseStep 133223087 = 199834631) B199834631
theorem B355261565 : Blo 2277435 355261565 := bstep (se 3 (by rfl) ⟨66611543, by rfl⟩ : syracuseStep 355261565 = 133223087) B133223087
theorem B236841043 : Blo 2277435 236841043 := bstep (se 1 (by rfl) ⟨177630782, by rfl⟩ : syracuseStep 236841043 = 355261565) B355261565
theorem B315788057 : Blo 2277435 315788057 := bstep (se 2 (by rfl) ⟨118420521, by rfl⟩ : syracuseStep 315788057 = 236841043) B236841043
theorem B210525371 : Blo 2277435 210525371 := bstep (se 1 (by rfl) ⟨157894028, by rfl⟩ : syracuseStep 210525371 = 315788057) B315788057
theorem B140350247 : Blo 2277435 140350247 := bstep (se 1 (by rfl) ⟨105262685, by rfl⟩ : syracuseStep 140350247 = 210525371) B210525371
theorem B93566831 : Blo 2277435 93566831 := bstep (se 1 (by rfl) ⟨70175123, by rfl⟩ : syracuseStep 93566831 = 140350247) B140350247
theorem B249511549 : Blo 2277435 249511549 := bstep (se 3 (by rfl) ⟨46783415, by rfl⟩ : syracuseStep 249511549 = 93566831) B93566831
theorem B332682065 : Blo 2277435 332682065 := bstep (se 2 (by rfl) ⟨124755774, by rfl⟩ : syracuseStep 332682065 = 249511549) B249511549
theorem B221788043 : Blo 2277435 221788043 := bstep (se 1 (by rfl) ⟨166341032, by rfl⟩ : syracuseStep 221788043 = 332682065) B332682065
theorem B147858695 : Blo 2277435 147858695 := bstep (se 1 (by rfl) ⟨110894021, by rfl⟩ : syracuseStep 147858695 = 221788043) B221788043
theorem B98572463 : Blo 2277435 98572463 := bstep (se 1 (by rfl) ⟨73929347, by rfl⟩ : syracuseStep 98572463 = 147858695) B147858695
theorem B65714975 : Blo 2277435 65714975 := bstep (se 1 (by rfl) ⟨49286231, by rfl⟩ : syracuseStep 65714975 = 98572463) B98572463
theorem B43809983 : Blo 2277435 43809983 := bstep (se 1 (by rfl) ⟨32857487, by rfl⟩ : syracuseStep 43809983 = 65714975) B65714975
theorem B29206655 : Blo 2277435 29206655 := bstep (se 1 (by rfl) ⟨21904991, by rfl⟩ : syracuseStep 29206655 = 43809983) B43809983
theorem B19471103 : Blo 2277435 19471103 := bstep (se 1 (by rfl) ⟨14603327, by rfl⟩ : syracuseStep 19471103 = 29206655) B29206655
theorem B12980735 : Blo 2277435 12980735 := bstep (se 1 (by rfl) ⟨9735551, by rfl⟩ : syracuseStep 12980735 = 19471103) B19471103
theorem B8653823 : Blo 2277435 8653823 := bstep (se 1 (by rfl) ⟨6490367, by rfl⟩ : syracuseStep 8653823 = 12980735) B12980735
theorem B5769215 : Blo 2277435 5769215 := bstep (se 1 (by rfl) ⟨4326911, by rfl⟩ : syracuseStep 5769215 = 8653823) B8653823
theorem B3846143 : Blo 2277435 3846143 := bstep (se 1 (by rfl) ⟨2884607, by rfl⟩ : syracuseStep 3846143 = 5769215) B5769215
theorem B2564095 : Blo 2277435 2564095 := bstep (se 1 (by rfl) ⟨1923071, by rfl⟩ : syracuseStep 2564095 = 3846143) B3846143
theorem B3418793 : Blo 2277435 3418793 := bstep (se 2 (by rfl) ⟨1282047, by rfl⟩ : syracuseStep 3418793 = 2564095) B2564095
theorem B2279195 : Blo 2277435 2279195 := bstep (se 1 (by rfl) ⟨1709396, by rfl⟩ : syracuseStep 2279195 = 3418793) B3418793
theorem B3245189 : Blo 2277435 3245189 := bbase (se 4 (by rfl) ⟨304236, by rfl⟩ : syracuseStep 3245189 = 608473) (by norm_num)
theorem B8653837 : Blo 2277435 8653837 := bstep (se 3 (by rfl) ⟨1622594, by rfl⟩ : syracuseStep 8653837 = 3245189) B3245189
theorem B11538449 : Blo 2277435 11538449 := bstep (se 2 (by rfl) ⟨4326918, by rfl⟩ : syracuseStep 11538449 = 8653837) B8653837
theorem B7692299 : Blo 2277435 7692299 := bstep (se 1 (by rfl) ⟨5769224, by rfl⟩ : syracuseStep 7692299 = 11538449) B11538449
theorem B5128199 : Blo 2277435 5128199 := bstep (se 1 (by rfl) ⟨3846149, by rfl⟩ : syracuseStep 5128199 = 7692299) B7692299
theorem B3418799 : Blo 2277435 3418799 := bstep (se 1 (by rfl) ⟨2564099, by rfl⟩ : syracuseStep 3418799 = 5128199) B5128199
theorem B2279199 : Blo 2277435 2279199 := bstep (se 1 (by rfl) ⟨1709399, by rfl⟩ : syracuseStep 2279199 = 3418799) B3418799
theorem B3418805 : Blo 2277435 3418805 := bbase (se 5 (by rfl) ⟨160256, by rfl⟩ : syracuseStep 3418805 = 320513) (by norm_num)
theorem B2279203 : Blo 2277435 2279203 := bstep (se 1 (by rfl) ⟨1709402, by rfl⟩ : syracuseStep 2279203 = 3418805) B3418805
theorem B5769245 : Blo 2277435 5769245 := bbase (se 3 (by rfl) ⟨1081733, by rfl⟩ : syracuseStep 5769245 = 2163467) (by norm_num)
theorem B3846163 : Blo 2277435 3846163 := bstep (se 1 (by rfl) ⟨2884622, by rfl⟩ : syracuseStep 3846163 = 5769245) B5769245
theorem B5128217 : Blo 2277435 5128217 := bstep (se 2 (by rfl) ⟨1923081, by rfl⟩ : syracuseStep 5128217 = 3846163) B3846163
theorem B3418811 : Blo 2277435 3418811 := bstep (se 1 (by rfl) ⟨2564108, by rfl⟩ : syracuseStep 3418811 = 5128217) B5128217
theorem B2279207 : Blo 2277435 2279207 := bstep (se 1 (by rfl) ⟨1709405, by rfl⟩ : syracuseStep 2279207 = 3418811) B3418811
theorem B2564113 : Blo 2277435 2564113 := bbase (se 2 (by rfl) ⟨961542, by rfl⟩ : syracuseStep 2564113 = 1923085) (by norm_num)
theorem B3418817 : Blo 2277435 3418817 := bstep (se 2 (by rfl) ⟨1282056, by rfl⟩ : syracuseStep 3418817 = 2564113) B2564113
theorem B2279211 : Blo 2277435 2279211 := bstep (se 1 (by rfl) ⟨1709408, by rfl⟩ : syracuseStep 2279211 = 3418817) B3418817
theorem B4326949 : Blo 2277435 4326949 := bbase (se 4 (by rfl) ⟨405651, by rfl⟩ : syracuseStep 4326949 = 811303) (by norm_num)
theorem B5769265 : Blo 2277435 5769265 := bstep (se 2 (by rfl) ⟨2163474, by rfl⟩ : syracuseStep 5769265 = 4326949) B4326949
theorem B7692353 : Blo 2277435 7692353 := bstep (se 2 (by rfl) ⟨2884632, by rfl⟩ : syracuseStep 7692353 = 5769265) B5769265
theorem B5128235 : Blo 2277435 5128235 := bstep (se 1 (by rfl) ⟨3846176, by rfl⟩ : syracuseStep 5128235 = 7692353) B7692353
theorem B3418823 : Blo 2277435 3418823 := bstep (se 1 (by rfl) ⟨2564117, by rfl⟩ : syracuseStep 3418823 = 5128235) B5128235
theorem B2279215 : Blo 2277435 2279215 := bstep (se 1 (by rfl) ⟨1709411, by rfl⟩ : syracuseStep 2279215 = 3418823) B3418823
theorem B3418829 : Blo 2277435 3418829 := bbase (se 3 (by rfl) ⟨641030, by rfl⟩ : syracuseStep 3418829 = 1282061) (by norm_num)
theorem B2279219 : Blo 2277435 2279219 := bstep (se 1 (by rfl) ⟨1709414, by rfl⟩ : syracuseStep 2279219 = 3418829) B3418829
theorem B5128253 : Blo 2277435 5128253 := bbase (se 3 (by rfl) ⟨961547, by rfl⟩ : syracuseStep 5128253 = 1923095) (by norm_num)
theorem B3418835 : Blo 2277435 3418835 := bstep (se 1 (by rfl) ⟨2564126, by rfl⟩ : syracuseStep 3418835 = 5128253) B5128253
theorem B2279223 : Blo 2277435 2279223 := bstep (se 1 (by rfl) ⟨1709417, by rfl⟩ : syracuseStep 2279223 = 3418835) B3418835
theorem B3846197 : Blo 2277435 3846197 := bbase (se 5 (by rfl) ⟨180290, by rfl⟩ : syracuseStep 3846197 = 360581) (by norm_num)
theorem B2564131 : Blo 2277435 2564131 := bstep (se 1 (by rfl) ⟨1923098, by rfl⟩ : syracuseStep 2564131 = 3846197) B3846197
theorem B3418841 : Blo 2277435 3418841 := bstep (se 2 (by rfl) ⟨1282065, by rfl⟩ : syracuseStep 3418841 = 2564131) B2564131
theorem B2279227 : Blo 2277435 2279227 := bstep (se 1 (by rfl) ⟨1709420, by rfl⟩ : syracuseStep 2279227 = 3418841) B3418841
theorem B6490469 : Blo 2277435 6490469 := bbase (se 4 (by rfl) ⟨608481, by rfl⟩ : syracuseStep 6490469 = 1216963) (by norm_num)
theorem B17307917 : Blo 2277435 17307917 := bstep (se 3 (by rfl) ⟨3245234, by rfl⟩ : syracuseStep 17307917 = 6490469) B6490469
theorem B11538611 : Blo 2277435 11538611 := bstep (se 1 (by rfl) ⟨8653958, by rfl⟩ : syracuseStep 11538611 = 17307917) B17307917
theorem B7692407 : Blo 2277435 7692407 := bstep (se 1 (by rfl) ⟨5769305, by rfl⟩ : syracuseStep 7692407 = 11538611) B11538611
theorem B5128271 : Blo 2277435 5128271 := bstep (se 1 (by rfl) ⟨3846203, by rfl⟩ : syracuseStep 5128271 = 7692407) B7692407
theorem B3418847 : Blo 2277435 3418847 := bstep (se 1 (by rfl) ⟨2564135, by rfl⟩ : syracuseStep 3418847 = 5128271) B5128271
theorem B2279231 : Blo 2277435 2279231 := bstep (se 1 (by rfl) ⟨1709423, by rfl⟩ : syracuseStep 2279231 = 3418847) B3418847
theorem B3418853 : Blo 2277435 3418853 := bbase (se 4 (by rfl) ⟨320517, by rfl⟩ : syracuseStep 3418853 = 641035) (by norm_num)
theorem B2279235 : Blo 2277435 2279235 := bstep (se 1 (by rfl) ⟨1709426, by rfl⟩ : syracuseStep 2279235 = 3418853) B3418853
theorem B8214533 : Blo 2277435 8214533 := bbase (se 4 (by rfl) ⟨770112, by rfl⟩ : syracuseStep 8214533 = 1540225) (by norm_num)
theorem B5476355 : Blo 2277435 5476355 := bstep (se 1 (by rfl) ⟨4107266, by rfl⟩ : syracuseStep 5476355 = 8214533) B8214533
theorem B3650903 : Blo 2277435 3650903 := bstep (se 1 (by rfl) ⟨2738177, by rfl⟩ : syracuseStep 3650903 = 5476355) B5476355
theorem B2433935 : Blo 2277435 2433935 := bstep (se 1 (by rfl) ⟨1825451, by rfl⟩ : syracuseStep 2433935 = 3650903) B3650903
theorem B6490493 : Blo 2277435 6490493 := bstep (se 3 (by rfl) ⟨1216967, by rfl⟩ : syracuseStep 6490493 = 2433935) B2433935
theorem B4326995 : Blo 2277435 4326995 := bstep (se 1 (by rfl) ⟨3245246, by rfl⟩ : syracuseStep 4326995 = 6490493) B6490493
theorem B2884663 : Blo 2277435 2884663 := bstep (se 1 (by rfl) ⟨2163497, by rfl⟩ : syracuseStep 2884663 = 4326995) B4326995
theorem B3846217 : Blo 2277435 3846217 := bstep (se 2 (by rfl) ⟨1442331, by rfl⟩ : syracuseStep 3846217 = 2884663) B2884663
theorem B5128289 : Blo 2277435 5128289 := bstep (se 2 (by rfl) ⟨1923108, by rfl⟩ : syracuseStep 5128289 = 3846217) B3846217
theorem B3418859 : Blo 2277435 3418859 := bstep (se 1 (by rfl) ⟨2564144, by rfl⟩ : syracuseStep 3418859 = 5128289) B5128289
theorem B2279239 : Blo 2277435 2279239 := bstep (se 1 (by rfl) ⟨1709429, by rfl⟩ : syracuseStep 2279239 = 3418859) B3418859
theorem B2564149 : Blo 2277435 2564149 := bbase (se 5 (by rfl) ⟨120194, by rfl⟩ : syracuseStep 2564149 = 240389) (by norm_num)
theorem B3418865 : Blo 2277435 3418865 := bstep (se 2 (by rfl) ⟨1282074, by rfl⟩ : syracuseStep 3418865 = 2564149) B2564149
theorem B2279243 : Blo 2277435 2279243 := bstep (se 1 (by rfl) ⟨1709432, by rfl⟩ : syracuseStep 2279243 = 3418865) B3418865
theorem B2884673 : Blo 2277435 2884673 := bbase (se 2 (by rfl) ⟨1081752, by rfl⟩ : syracuseStep 2884673 = 2163505) (by norm_num)
theorem B7692461 : Blo 2277435 7692461 := bstep (se 3 (by rfl) ⟨1442336, by rfl⟩ : syracuseStep 7692461 = 2884673) B2884673
theorem B5128307 : Blo 2277435 5128307 := bstep (se 1 (by rfl) ⟨3846230, by rfl⟩ : syracuseStep 5128307 = 7692461) B7692461
theorem B3418871 : Blo 2277435 3418871 := bstep (se 1 (by rfl) ⟨2564153, by rfl⟩ : syracuseStep 3418871 = 5128307) B5128307
theorem B2279247 : Blo 2277435 2279247 := bstep (se 1 (by rfl) ⟨1709435, by rfl⟩ : syracuseStep 2279247 = 3418871) B3418871
theorem B3418877 : Blo 2277435 3418877 := bbase (se 3 (by rfl) ⟨641039, by rfl⟩ : syracuseStep 3418877 = 1282079) (by norm_num)
theorem B2279251 : Blo 2277435 2279251 := bstep (se 1 (by rfl) ⟨1709438, by rfl⟩ : syracuseStep 2279251 = 3418877) B3418877
theorem B5128325 : Blo 2277435 5128325 := bbase (se 4 (by rfl) ⟨480780, by rfl⟩ : syracuseStep 5128325 = 961561) (by norm_num)
theorem B3418883 : Blo 2277435 3418883 := bstep (se 1 (by rfl) ⟨2564162, by rfl⟩ : syracuseStep 3418883 = 5128325) B5128325
theorem B2279255 : Blo 2277435 2279255 := bstep (se 1 (by rfl) ⟨1709441, by rfl⟩ : syracuseStep 2279255 = 3418883) B3418883
theorem B3080477 : Blo 2277435 3080477 := bbase (se 3 (by rfl) ⟨577589, by rfl⟩ : syracuseStep 3080477 = 1155179) (by norm_num)
theorem B8214605 : Blo 2277435 8214605 := bstep (se 3 (by rfl) ⟨1540238, by rfl⟩ : syracuseStep 8214605 = 3080477) B3080477
theorem B5476403 : Blo 2277435 5476403 := bstep (se 1 (by rfl) ⟨4107302, by rfl⟩ : syracuseStep 5476403 = 8214605) B8214605
theorem B3650935 : Blo 2277435 3650935 := bstep (se 1 (by rfl) ⟨2738201, by rfl⟩ : syracuseStep 3650935 = 5476403) B5476403
theorem B4867913 : Blo 2277435 4867913 := bstep (se 2 (by rfl) ⟨1825467, by rfl⟩ : syracuseStep 4867913 = 3650935) B3650935
theorem B3245275 : Blo 2277435 3245275 := bstep (se 1 (by rfl) ⟨2433956, by rfl⟩ : syracuseStep 3245275 = 4867913) B4867913
theorem B4327033 : Blo 2277435 4327033 := bstep (se 2 (by rfl) ⟨1622637, by rfl⟩ : syracuseStep 4327033 = 3245275) B3245275
theorem B5769377 : Blo 2277435 5769377 := bstep (se 2 (by rfl) ⟨2163516, by rfl⟩ : syracuseStep 5769377 = 4327033) B4327033
theorem B3846251 : Blo 2277435 3846251 := bstep (se 1 (by rfl) ⟨2884688, by rfl⟩ : syracuseStep 3846251 = 5769377) B5769377
theorem B2564167 : Blo 2277435 2564167 := bstep (se 1 (by rfl) ⟨1923125, by rfl⟩ : syracuseStep 2564167 = 3846251) B3846251
theorem B3418889 : Blo 2277435 3418889 := bstep (se 2 (by rfl) ⟨1282083, by rfl⟩ : syracuseStep 3418889 = 2564167) B2564167
theorem B2279259 : Blo 2277435 2279259 := bstep (se 1 (by rfl) ⟨1709444, by rfl⟩ : syracuseStep 2279259 = 3418889) B3418889
theorem B11538773 : Blo 2277435 11538773 := bbase (se 10 (by rfl) ⟨16902, by rfl⟩ : syracuseStep 11538773 = 33805) (by norm_num)
theorem B7692515 : Blo 2277435 7692515 := bstep (se 1 (by rfl) ⟨5769386, by rfl⟩ : syracuseStep 7692515 = 11538773) B11538773
theorem B5128343 : Blo 2277435 5128343 := bstep (se 1 (by rfl) ⟨3846257, by rfl⟩ : syracuseStep 5128343 = 7692515) B7692515
theorem B3418895 : Blo 2277435 3418895 := bstep (se 1 (by rfl) ⟨2564171, by rfl⟩ : syracuseStep 3418895 = 5128343) B5128343
theorem B2279263 : Blo 2277435 2279263 := bstep (se 1 (by rfl) ⟨1709447, by rfl⟩ : syracuseStep 2279263 = 3418895) B3418895
theorem B3418901 : Blo 2277435 3418901 := bbase (se 6 (by rfl) ⟨80130, by rfl⟩ : syracuseStep 3418901 = 160261) (by norm_num)
theorem B2279267 : Blo 2277435 2279267 := bstep (se 1 (by rfl) ⟨1709450, by rfl⟩ : syracuseStep 2279267 = 3418901) B3418901
theorem B32858581 : Blo 2277435 32858581 := bbase (se 7 (by rfl) ⟨385061, by rfl⟩ : syracuseStep 32858581 = 770123) (by norm_num)
theorem B43811441 : Blo 2277435 43811441 := bstep (se 2 (by rfl) ⟨16429290, by rfl⟩ : syracuseStep 43811441 = 32858581) B32858581
theorem B29207627 : Blo 2277435 29207627 := bstep (se 1 (by rfl) ⟨21905720, by rfl⟩ : syracuseStep 29207627 = 43811441) B43811441
theorem B19471751 : Blo 2277435 19471751 := bstep (se 1 (by rfl) ⟨14603813, by rfl⟩ : syracuseStep 19471751 = 29207627) B29207627
theorem B12981167 : Blo 2277435 12981167 := bstep (se 1 (by rfl) ⟨9735875, by rfl⟩ : syracuseStep 12981167 = 19471751) B19471751
theorem B8654111 : Blo 2277435 8654111 := bstep (se 1 (by rfl) ⟨6490583, by rfl⟩ : syracuseStep 8654111 = 12981167) B12981167
theorem B5769407 : Blo 2277435 5769407 := bstep (se 1 (by rfl) ⟨4327055, by rfl⟩ : syracuseStep 5769407 = 8654111) B8654111
theorem B3846271 : Blo 2277435 3846271 := bstep (se 1 (by rfl) ⟨2884703, by rfl⟩ : syracuseStep 3846271 = 5769407) B5769407
theorem B5128361 : Blo 2277435 5128361 := bstep (se 2 (by rfl) ⟨1923135, by rfl⟩ : syracuseStep 5128361 = 3846271) B3846271
theorem B3418907 : Blo 2277435 3418907 := bstep (se 1 (by rfl) ⟨2564180, by rfl⟩ : syracuseStep 3418907 = 5128361) B5128361
theorem B2279271 : Blo 2277435 2279271 := bstep (se 1 (by rfl) ⟨1709453, by rfl⟩ : syracuseStep 2279271 = 3418907) B3418907
theorem B2564185 : Blo 2277435 2564185 := bbase (se 2 (by rfl) ⟨961569, by rfl⟩ : syracuseStep 2564185 = 1923139) (by norm_num)
theorem B3418913 : Blo 2277435 3418913 := bstep (se 2 (by rfl) ⟨1282092, by rfl⟩ : syracuseStep 3418913 = 2564185) B2564185
theorem B2279275 : Blo 2277435 2279275 := bstep (se 1 (by rfl) ⟨1709456, by rfl⟩ : syracuseStep 2279275 = 3418913) B3418913
theorem B2738225 : Blo 2277435 2738225 := bbase (se 2 (by rfl) ⟨1026834, by rfl⟩ : syracuseStep 2738225 = 2053669) (by norm_num)
theorem B7301933 : Blo 2277435 7301933 := bstep (se 3 (by rfl) ⟨1369112, by rfl⟩ : syracuseStep 7301933 = 2738225) B2738225
theorem B4867955 : Blo 2277435 4867955 := bstep (se 1 (by rfl) ⟨3650966, by rfl⟩ : syracuseStep 4867955 = 7301933) B7301933
theorem B3245303 : Blo 2277435 3245303 := bstep (se 1 (by rfl) ⟨2433977, by rfl⟩ : syracuseStep 3245303 = 4867955) B4867955
theorem B8654141 : Blo 2277435 8654141 := bstep (se 3 (by rfl) ⟨1622651, by rfl⟩ : syracuseStep 8654141 = 3245303) B3245303
theorem B5769427 : Blo 2277435 5769427 := bstep (se 1 (by rfl) ⟨4327070, by rfl⟩ : syracuseStep 5769427 = 8654141) B8654141
theorem B7692569 : Blo 2277435 7692569 := bstep (se 2 (by rfl) ⟨2884713, by rfl⟩ : syracuseStep 7692569 = 5769427) B5769427
theorem B5128379 : Blo 2277435 5128379 := bstep (se 1 (by rfl) ⟨3846284, by rfl⟩ : syracuseStep 5128379 = 7692569) B7692569
theorem B3418919 : Blo 2277435 3418919 := bstep (se 1 (by rfl) ⟨2564189, by rfl⟩ : syracuseStep 3418919 = 5128379) B5128379
theorem B2279279 : Blo 2277435 2279279 := bstep (se 1 (by rfl) ⟨1709459, by rfl⟩ : syracuseStep 2279279 = 3418919) B3418919
theorem B3418925 : Blo 2277435 3418925 := bbase (se 3 (by rfl) ⟨641048, by rfl⟩ : syracuseStep 3418925 = 1282097) (by norm_num)
theorem B2279283 : Blo 2277435 2279283 := bstep (se 1 (by rfl) ⟨1709462, by rfl⟩ : syracuseStep 2279283 = 3418925) B3418925
theorem B5128397 : Blo 2277435 5128397 := bbase (se 3 (by rfl) ⟨961574, by rfl⟩ : syracuseStep 5128397 = 1923149) (by norm_num)
theorem B3418931 : Blo 2277435 3418931 := bstep (se 1 (by rfl) ⟨2564198, by rfl⟩ : syracuseStep 3418931 = 5128397) B5128397
theorem B2279287 : Blo 2277435 2279287 := bstep (se 1 (by rfl) ⟨1709465, by rfl⟩ : syracuseStep 2279287 = 3418931) B3418931
theorem B2884729 : Blo 2277435 2884729 := bbase (se 2 (by rfl) ⟨1081773, by rfl⟩ : syracuseStep 2884729 = 2163547) (by norm_num)
theorem B3846305 : Blo 2277435 3846305 := bstep (se 2 (by rfl) ⟨1442364, by rfl⟩ : syracuseStep 3846305 = 2884729) B2884729
theorem B2564203 : Blo 2277435 2564203 := bstep (se 1 (by rfl) ⟨1923152, by rfl⟩ : syracuseStep 2564203 = 3846305) B3846305
theorem B3418937 : Blo 2277435 3418937 := bstep (se 2 (by rfl) ⟨1282101, by rfl⟩ : syracuseStep 3418937 = 2564203) B2564203
theorem B2279291 : Blo 2277435 2279291 := bstep (se 1 (by rfl) ⟨1709468, by rfl⟩ : syracuseStep 2279291 = 3418937) B3418937
theorem B36966293 : Blo 2277435 36966293 := bbase (se 6 (by rfl) ⟨866397, by rfl⟩ : syracuseStep 36966293 = 1732795) (by norm_num)
theorem B24644195 : Blo 2277435 24644195 := bstep (se 1 (by rfl) ⟨18483146, by rfl⟩ : syracuseStep 24644195 = 36966293) B36966293
theorem B16429463 : Blo 2277435 16429463 := bstep (se 1 (by rfl) ⟨12322097, by rfl⟩ : syracuseStep 16429463 = 24644195) B24644195
theorem B10952975 : Blo 2277435 10952975 := bstep (se 1 (by rfl) ⟨8214731, by rfl⟩ : syracuseStep 10952975 = 16429463) B16429463
theorem B7301983 : Blo 2277435 7301983 := bstep (se 1 (by rfl) ⟨5476487, by rfl⟩ : syracuseStep 7301983 = 10952975) B10952975
theorem B9735977 : Blo 2277435 9735977 := bstep (se 2 (by rfl) ⟨3650991, by rfl⟩ : syracuseStep 9735977 = 7301983) B7301983
theorem B25962605 : Blo 2277435 25962605 := bstep (se 3 (by rfl) ⟨4867988, by rfl⟩ : syracuseStep 25962605 = 9735977) B9735977
theorem B17308403 : Blo 2277435 17308403 := bstep (se 1 (by rfl) ⟨12981302, by rfl⟩ : syracuseStep 17308403 = 25962605) B25962605
theorem B11538935 : Blo 2277435 11538935 := bstep (se 1 (by rfl) ⟨8654201, by rfl⟩ : syracuseStep 11538935 = 17308403) B17308403
theorem B7692623 : Blo 2277435 7692623 := bstep (se 1 (by rfl) ⟨5769467, by rfl⟩ : syracuseStep 7692623 = 11538935) B11538935
theorem B5128415 : Blo 2277435 5128415 := bstep (se 1 (by rfl) ⟨3846311, by rfl⟩ : syracuseStep 5128415 = 7692623) B7692623
theorem B3418943 : Blo 2277435 3418943 := bstep (se 1 (by rfl) ⟨2564207, by rfl⟩ : syracuseStep 3418943 = 5128415) B5128415
theorem B2279295 : Blo 2277435 2279295 := bstep (se 1 (by rfl) ⟨1709471, by rfl⟩ : syracuseStep 2279295 = 3418943) B3418943
theorem B3418949 : Blo 2277435 3418949 := bbase (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) (by norm_num)
theorem B2279299 : Blo 2277435 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B3846325 : Blo 2277435 3846325 := bbase (se 5 (by rfl) ⟨180296, by rfl⟩ : syracuseStep 3846325 = 360593) (by norm_num)
theorem B5128433 : Blo 2277435 5128433 := bstep (se 2 (by rfl) ⟨1923162, by rfl⟩ : syracuseStep 5128433 = 3846325) B3846325
theorem B3418955 : Blo 2277435 3418955 := bstep (se 1 (by rfl) ⟨2564216, by rfl⟩ : syracuseStep 3418955 = 5128433) B5128433
theorem B2279303 : Blo 2277435 2279303 := bstep (se 1 (by rfl) ⟨1709477, by rfl⟩ : syracuseStep 2279303 = 3418955) B3418955
theorem B2564221 : Blo 2277435 2564221 := bbase (se 3 (by rfl) ⟨480791, by rfl⟩ : syracuseStep 2564221 = 961583) (by norm_num)
theorem B3418961 : Blo 2277435 3418961 := bstep (se 2 (by rfl) ⟨1282110, by rfl⟩ : syracuseStep 3418961 = 2564221) B2564221
theorem B2279307 : Blo 2277435 2279307 := bstep (se 1 (by rfl) ⟨1709480, by rfl⟩ : syracuseStep 2279307 = 3418961) B3418961
theorem B7692677 : Blo 2277435 7692677 := bbase (se 4 (by rfl) ⟨721188, by rfl⟩ : syracuseStep 7692677 = 1442377) (by norm_num)
theorem B5128451 : Blo 2277435 5128451 := bstep (se 1 (by rfl) ⟨3846338, by rfl⟩ : syracuseStep 5128451 = 7692677) B7692677
theorem B3418967 : Blo 2277435 3418967 := bstep (se 1 (by rfl) ⟨2564225, by rfl⟩ : syracuseStep 3418967 = 5128451) B5128451
theorem B2279311 : Blo 2277435 2279311 := bstep (se 1 (by rfl) ⟨1709483, by rfl⟩ : syracuseStep 2279311 = 3418967) B3418967
theorem B3418973 : Blo 2277435 3418973 := bbase (se 3 (by rfl) ⟨641057, by rfl⟩ : syracuseStep 3418973 = 1282115) (by norm_num)
theorem B2279315 : Blo 2277435 2279315 := bstep (se 1 (by rfl) ⟨1709486, by rfl⟩ : syracuseStep 2279315 = 3418973) B3418973
theorem B5128469 : Blo 2277435 5128469 := bbase (se 6 (by rfl) ⟨120198, by rfl⟩ : syracuseStep 5128469 = 240397) (by norm_num)
theorem B3418979 : Blo 2277435 3418979 := bstep (se 1 (by rfl) ⟨2564234, by rfl⟩ : syracuseStep 3418979 = 5128469) B5128469
theorem B2279319 : Blo 2277435 2279319 := bstep (se 1 (by rfl) ⟨1709489, by rfl⟩ : syracuseStep 2279319 = 3418979) B3418979
theorem B8654309 : Blo 2277435 8654309 := bbase (se 4 (by rfl) ⟨811341, by rfl⟩ : syracuseStep 8654309 = 1622683) (by norm_num)
theorem B5769539 : Blo 2277435 5769539 := bstep (se 1 (by rfl) ⟨4327154, by rfl⟩ : syracuseStep 5769539 = 8654309) B8654309
theorem B3846359 : Blo 2277435 3846359 := bstep (se 1 (by rfl) ⟨2884769, by rfl⟩ : syracuseStep 3846359 = 5769539) B5769539
theorem B2564239 : Blo 2277435 2564239 := bstep (se 1 (by rfl) ⟨1923179, by rfl⟩ : syracuseStep 2564239 = 3846359) B3846359
theorem B3418985 : Blo 2277435 3418985 := bstep (se 2 (by rfl) ⟨1282119, by rfl⟩ : syracuseStep 3418985 = 2564239) B2564239
theorem B2279323 : Blo 2277435 2279323 := bstep (se 1 (by rfl) ⟨1709492, by rfl⟩ : syracuseStep 2279323 = 3418985) B3418985
theorem B5476565 : Blo 2277435 5476565 := bbase (se 7 (by rfl) ⟨64178, by rfl⟩ : syracuseStep 5476565 = 128357) (by norm_num)
theorem B3651043 : Blo 2277435 3651043 := bstep (se 1 (by rfl) ⟨2738282, by rfl⟩ : syracuseStep 3651043 = 5476565) B5476565
theorem B4868057 : Blo 2277435 4868057 := bstep (se 2 (by rfl) ⟨1825521, by rfl⟩ : syracuseStep 4868057 = 3651043) B3651043
theorem B12981485 : Blo 2277435 12981485 := bstep (se 3 (by rfl) ⟨2434028, by rfl⟩ : syracuseStep 12981485 = 4868057) B4868057
theorem B8654323 : Blo 2277435 8654323 := bstep (se 1 (by rfl) ⟨6490742, by rfl⟩ : syracuseStep 8654323 = 12981485) B12981485
theorem B11539097 : Blo 2277435 11539097 := bstep (se 2 (by rfl) ⟨4327161, by rfl⟩ : syracuseStep 11539097 = 8654323) B8654323
theorem B7692731 : Blo 2277435 7692731 := bstep (se 1 (by rfl) ⟨5769548, by rfl⟩ : syracuseStep 7692731 = 11539097) B11539097
theorem B5128487 : Blo 2277435 5128487 := bstep (se 1 (by rfl) ⟨3846365, by rfl⟩ : syracuseStep 5128487 = 7692731) B7692731
theorem B3418991 : Blo 2277435 3418991 := bstep (se 1 (by rfl) ⟨2564243, by rfl⟩ : syracuseStep 3418991 = 5128487) B5128487
theorem B2279327 : Blo 2277435 2279327 := bstep (se 1 (by rfl) ⟨1709495, by rfl⟩ : syracuseStep 2279327 = 3418991) B3418991
theorem B3418997 : Blo 2277435 3418997 := bbase (se 5 (by rfl) ⟨160265, by rfl⟩ : syracuseStep 3418997 = 320531) (by norm_num)
theorem B2279331 : Blo 2277435 2279331 := bstep (se 1 (by rfl) ⟨1709498, by rfl⟩ : syracuseStep 2279331 = 3418997) B3418997
theorem B24980885 : Blo 2277435 24980885 := bbase (se 6 (by rfl) ⟨585489, by rfl⟩ : syracuseStep 24980885 = 1170979) (by norm_num)
theorem B16653923 : Blo 2277435 16653923 := bstep (se 1 (by rfl) ⟨12490442, by rfl⟩ : syracuseStep 16653923 = 24980885) B24980885
theorem B11102615 : Blo 2277435 11102615 := bstep (se 1 (by rfl) ⟨8326961, by rfl⟩ : syracuseStep 11102615 = 16653923) B16653923
theorem B7401743 : Blo 2277435 7401743 := bstep (se 1 (by rfl) ⟨5551307, by rfl⟩ : syracuseStep 7401743 = 11102615) B11102615
theorem B4934495 : Blo 2277435 4934495 := bstep (se 1 (by rfl) ⟨3700871, by rfl⟩ : syracuseStep 4934495 = 7401743) B7401743
theorem B3289663 : Blo 2277435 3289663 := bstep (se 1 (by rfl) ⟨2467247, by rfl⟩ : syracuseStep 3289663 = 4934495) B4934495
theorem B4386217 : Blo 2277435 4386217 := bstep (se 2 (by rfl) ⟨1644831, by rfl⟩ : syracuseStep 4386217 = 3289663) B3289663
theorem B5848289 : Blo 2277435 5848289 := bstep (se 2 (by rfl) ⟨2193108, by rfl⟩ : syracuseStep 5848289 = 4386217) B4386217
theorem B3898859 : Blo 2277435 3898859 := bstep (se 1 (by rfl) ⟨2924144, by rfl⟩ : syracuseStep 3898859 = 5848289) B5848289
theorem B10396957 : Blo 2277435 10396957 := bstep (se 3 (by rfl) ⟨1949429, by rfl⟩ : syracuseStep 10396957 = 3898859) B3898859
theorem B13862609 : Blo 2277435 13862609 := bstep (se 2 (by rfl) ⟨5198478, by rfl⟩ : syracuseStep 13862609 = 10396957) B10396957
theorem B9241739 : Blo 2277435 9241739 := bstep (se 1 (by rfl) ⟨6931304, by rfl⟩ : syracuseStep 9241739 = 13862609) B13862609
theorem B6161159 : Blo 2277435 6161159 := bstep (se 1 (by rfl) ⟨4620869, by rfl⟩ : syracuseStep 6161159 = 9241739) B9241739
theorem B4107439 : Blo 2277435 4107439 := bstep (se 1 (by rfl) ⟨3080579, by rfl⟩ : syracuseStep 4107439 = 6161159) B6161159
theorem B5476585 : Blo 2277435 5476585 := bstep (se 2 (by rfl) ⟨2053719, by rfl⟩ : syracuseStep 5476585 = 4107439) B4107439
theorem B7302113 : Blo 2277435 7302113 := bstep (se 2 (by rfl) ⟨2738292, by rfl⟩ : syracuseStep 7302113 = 5476585) B5476585
theorem B4868075 : Blo 2277435 4868075 := bstep (se 1 (by rfl) ⟨3651056, by rfl⟩ : syracuseStep 4868075 = 7302113) B7302113
theorem B3245383 : Blo 2277435 3245383 := bstep (se 1 (by rfl) ⟨2434037, by rfl⟩ : syracuseStep 3245383 = 4868075) B4868075
theorem B4327177 : Blo 2277435 4327177 := bstep (se 2 (by rfl) ⟨1622691, by rfl⟩ : syracuseStep 4327177 = 3245383) B3245383
theorem B5769569 : Blo 2277435 5769569 := bstep (se 2 (by rfl) ⟨2163588, by rfl⟩ : syracuseStep 5769569 = 4327177) B4327177
theorem B3846379 : Blo 2277435 3846379 := bstep (se 1 (by rfl) ⟨2884784, by rfl⟩ : syracuseStep 3846379 = 5769569) B5769569
theorem B5128505 : Blo 2277435 5128505 := bstep (se 2 (by rfl) ⟨1923189, by rfl⟩ : syracuseStep 5128505 = 3846379) B3846379
theorem B3419003 : Blo 2277435 3419003 := bstep (se 1 (by rfl) ⟨2564252, by rfl⟩ : syracuseStep 3419003 = 5128505) B5128505
theorem B2279335 : Blo 2277435 2279335 := bstep (se 1 (by rfl) ⟨1709501, by rfl⟩ : syracuseStep 2279335 = 3419003) B3419003
theorem B2564257 : Blo 2277435 2564257 := bbase (se 2 (by rfl) ⟨961596, by rfl⟩ : syracuseStep 2564257 = 1923193) (by norm_num)
theorem B3419009 : Blo 2277435 3419009 := bstep (se 2 (by rfl) ⟨1282128, by rfl⟩ : syracuseStep 3419009 = 2564257) B2564257
theorem B2279339 : Blo 2277435 2279339 := bstep (se 1 (by rfl) ⟨1709504, by rfl⟩ : syracuseStep 2279339 = 3419009) B3419009
theorem B5769589 : Blo 2277435 5769589 := bbase (se 5 (by rfl) ⟨270449, by rfl⟩ : syracuseStep 5769589 = 540899) (by norm_num)
theorem B7692785 : Blo 2277435 7692785 := bstep (se 2 (by rfl) ⟨2884794, by rfl⟩ : syracuseStep 7692785 = 5769589) B5769589
theorem B5128523 : Blo 2277435 5128523 := bstep (se 1 (by rfl) ⟨3846392, by rfl⟩ : syracuseStep 5128523 = 7692785) B7692785
theorem B3419015 : Blo 2277435 3419015 := bstep (se 1 (by rfl) ⟨2564261, by rfl⟩ : syracuseStep 3419015 = 5128523) B5128523
theorem B2279343 : Blo 2277435 2279343 := bstep (se 1 (by rfl) ⟨1709507, by rfl⟩ : syracuseStep 2279343 = 3419015) B3419015
theorem B3419021 : Blo 2277435 3419021 := bbase (se 3 (by rfl) ⟨641066, by rfl⟩ : syracuseStep 3419021 = 1282133) (by norm_num)
theorem B2279347 : Blo 2277435 2279347 := bstep (se 1 (by rfl) ⟨1709510, by rfl⟩ : syracuseStep 2279347 = 3419021) B3419021
theorem B5128541 : Blo 2277435 5128541 := bbase (se 3 (by rfl) ⟨961601, by rfl⟩ : syracuseStep 5128541 = 1923203) (by norm_num)
theorem B3419027 : Blo 2277435 3419027 := bstep (se 1 (by rfl) ⟨2564270, by rfl⟩ : syracuseStep 3419027 = 5128541) B5128541
theorem B2279351 : Blo 2277435 2279351 := bstep (se 1 (by rfl) ⟨1709513, by rfl⟩ : syracuseStep 2279351 = 3419027) B3419027
theorem B3846413 : Blo 2277435 3846413 := bbase (se 3 (by rfl) ⟨721202, by rfl⟩ : syracuseStep 3846413 = 1442405) (by norm_num)
theorem B2564275 : Blo 2277435 2564275 := bstep (se 1 (by rfl) ⟨1923206, by rfl⟩ : syracuseStep 2564275 = 3846413) B3846413
theorem B3419033 : Blo 2277435 3419033 := bstep (se 2 (by rfl) ⟨1282137, by rfl⟩ : syracuseStep 3419033 = 2564275) B2564275
theorem B2279355 : Blo 2277435 2279355 := bstep (se 1 (by rfl) ⟨1709516, by rfl⟩ : syracuseStep 2279355 = 3419033) B3419033
theorem B19472501 : Blo 2277435 19472501 := bbase (se 5 (by rfl) ⟨912773, by rfl⟩ : syracuseStep 19472501 = 1825547) (by norm_num)
theorem B12981667 : Blo 2277435 12981667 := bstep (se 1 (by rfl) ⟨9736250, by rfl⟩ : syracuseStep 12981667 = 19472501) B19472501
theorem B17308889 : Blo 2277435 17308889 := bstep (se 2 (by rfl) ⟨6490833, by rfl⟩ : syracuseStep 17308889 = 12981667) B12981667
theorem B11539259 : Blo 2277435 11539259 := bstep (se 1 (by rfl) ⟨8654444, by rfl⟩ : syracuseStep 11539259 = 17308889) B17308889
theorem B7692839 : Blo 2277435 7692839 := bstep (se 1 (by rfl) ⟨5769629, by rfl⟩ : syracuseStep 7692839 = 11539259) B11539259
theorem B5128559 : Blo 2277435 5128559 := bstep (se 1 (by rfl) ⟨3846419, by rfl⟩ : syracuseStep 5128559 = 7692839) B7692839
theorem B3419039 : Blo 2277435 3419039 := bstep (se 1 (by rfl) ⟨2564279, by rfl⟩ : syracuseStep 3419039 = 5128559) B5128559
theorem B2279359 : Blo 2277435 2279359 := bstep (se 1 (by rfl) ⟨1709519, by rfl⟩ : syracuseStep 2279359 = 3419039) B3419039
theorem B3419045 : Blo 2277435 3419045 := bbase (se 4 (by rfl) ⟨320535, by rfl⟩ : syracuseStep 3419045 = 641071) (by norm_num)
theorem B2279363 : Blo 2277435 2279363 := bstep (se 1 (by rfl) ⟨1709522, by rfl⟩ : syracuseStep 2279363 = 3419045) B3419045
theorem B2884825 : Blo 2277435 2884825 := bbase (se 2 (by rfl) ⟨1081809, by rfl⟩ : syracuseStep 2884825 = 2163619) (by norm_num)
theorem B3846433 : Blo 2277435 3846433 := bstep (se 2 (by rfl) ⟨1442412, by rfl⟩ : syracuseStep 3846433 = 2884825) B2884825
theorem B5128577 : Blo 2277435 5128577 := bstep (se 2 (by rfl) ⟨1923216, by rfl⟩ : syracuseStep 5128577 = 3846433) B3846433
theorem B3419051 : Blo 2277435 3419051 := bstep (se 1 (by rfl) ⟨2564288, by rfl⟩ : syracuseStep 3419051 = 5128577) B5128577
theorem B2279367 : Blo 2277435 2279367 := bstep (se 1 (by rfl) ⟨1709525, by rfl⟩ : syracuseStep 2279367 = 3419051) B3419051
theorem B2564293 : Blo 2277435 2564293 := bbase (se 4 (by rfl) ⟨240402, by rfl⟩ : syracuseStep 2564293 = 480805) (by norm_num)
theorem B3419057 : Blo 2277435 3419057 := bstep (se 2 (by rfl) ⟨1282146, by rfl⟩ : syracuseStep 3419057 = 2564293) B2564293
theorem B2279371 : Blo 2277435 2279371 := bstep (se 1 (by rfl) ⟨1709528, by rfl⟩ : syracuseStep 2279371 = 3419057) B3419057
theorem B4327253 : Blo 2277435 4327253 := bbase (se 9 (by rfl) ⟨12677, by rfl⟩ : syracuseStep 4327253 = 25355) (by norm_num)
theorem B2884835 : Blo 2277435 2884835 := bstep (se 1 (by rfl) ⟨2163626, by rfl⟩ : syracuseStep 2884835 = 4327253) B4327253
theorem B7692893 : Blo 2277435 7692893 := bstep (se 3 (by rfl) ⟨1442417, by rfl⟩ : syracuseStep 7692893 = 2884835) B2884835
theorem B5128595 : Blo 2277435 5128595 := bstep (se 1 (by rfl) ⟨3846446, by rfl⟩ : syracuseStep 5128595 = 7692893) B7692893
theorem B3419063 : Blo 2277435 3419063 := bstep (se 1 (by rfl) ⟨2564297, by rfl⟩ : syracuseStep 3419063 = 5128595) B5128595
theorem B2279375 : Blo 2277435 2279375 := bstep (se 1 (by rfl) ⟨1709531, by rfl⟩ : syracuseStep 2279375 = 3419063) B3419063
theorem B3419069 : Blo 2277435 3419069 := bbase (se 3 (by rfl) ⟨641075, by rfl⟩ : syracuseStep 3419069 = 1282151) (by norm_num)
theorem B2279379 : Blo 2277435 2279379 := bstep (se 1 (by rfl) ⟨1709534, by rfl⟩ : syracuseStep 2279379 = 3419069) B3419069
theorem B5128613 : Blo 2277435 5128613 := bbase (se 4 (by rfl) ⟨480807, by rfl⟩ : syracuseStep 5128613 = 961615) (by norm_num)
theorem B3419075 : Blo 2277435 3419075 := bstep (se 1 (by rfl) ⟨2564306, by rfl⟩ : syracuseStep 3419075 = 5128613) B5128613
theorem B2279383 : Blo 2277435 2279383 := bstep (se 1 (by rfl) ⟨1709537, by rfl⟩ : syracuseStep 2279383 = 3419075) B3419075
theorem B5769701 : Blo 2277435 5769701 := bbase (se 4 (by rfl) ⟨540909, by rfl⟩ : syracuseStep 5769701 = 1081819) (by norm_num)
theorem B3846467 : Blo 2277435 3846467 := bstep (se 1 (by rfl) ⟨2884850, by rfl⟩ : syracuseStep 3846467 = 5769701) B5769701
theorem B2564311 : Blo 2277435 2564311 := bstep (se 1 (by rfl) ⟨1923233, by rfl⟩ : syracuseStep 2564311 = 3846467) B3846467
theorem B3419081 : Blo 2277435 3419081 := bstep (se 2 (by rfl) ⟨1282155, by rfl⟩ : syracuseStep 3419081 = 2564311) B2564311
theorem B2279387 : Blo 2277435 2279387 := bstep (se 1 (by rfl) ⟨1709540, by rfl⟩ : syracuseStep 2279387 = 3419081) B3419081
theorem B2434097 : Blo 2277435 2434097 := bbase (se 2 (by rfl) ⟨912786, by rfl⟩ : syracuseStep 2434097 = 1825573) (by norm_num)
theorem B6490925 : Blo 2277435 6490925 := bstep (se 3 (by rfl) ⟨1217048, by rfl⟩ : syracuseStep 6490925 = 2434097) B2434097
theorem B4327283 : Blo 2277435 4327283 := bstep (se 1 (by rfl) ⟨3245462, by rfl⟩ : syracuseStep 4327283 = 6490925) B6490925
theorem B11539421 : Blo 2277435 11539421 := bstep (se 3 (by rfl) ⟨2163641, by rfl⟩ : syracuseStep 11539421 = 4327283) B4327283
theorem B7692947 : Blo 2277435 7692947 := bstep (se 1 (by rfl) ⟨5769710, by rfl⟩ : syracuseStep 7692947 = 11539421) B11539421
theorem B5128631 : Blo 2277435 5128631 := bstep (se 1 (by rfl) ⟨3846473, by rfl⟩ : syracuseStep 5128631 = 7692947) B7692947
theorem B3419087 : Blo 2277435 3419087 := bstep (se 1 (by rfl) ⟨2564315, by rfl⟩ : syracuseStep 3419087 = 5128631) B5128631
theorem B2279391 : Blo 2277435 2279391 := bstep (se 1 (by rfl) ⟨1709543, by rfl⟩ : syracuseStep 2279391 = 3419087) B3419087
theorem B3419093 : Blo 2277435 3419093 := bbase (se 7 (by rfl) ⟨40067, by rfl⟩ : syracuseStep 3419093 = 80135) (by norm_num)
theorem B2279395 : Blo 2277435 2279395 := bstep (se 1 (by rfl) ⟨1709546, by rfl⟩ : syracuseStep 2279395 = 3419093) B3419093
theorem B8654597 : Blo 2277435 8654597 := bbase (se 4 (by rfl) ⟨811368, by rfl⟩ : syracuseStep 8654597 = 1622737) (by norm_num)
theorem B5769731 : Blo 2277435 5769731 := bstep (se 1 (by rfl) ⟨4327298, by rfl⟩ : syracuseStep 5769731 = 8654597) B8654597
theorem B3846487 : Blo 2277435 3846487 := bstep (se 1 (by rfl) ⟨2884865, by rfl⟩ : syracuseStep 3846487 = 5769731) B5769731
theorem B5128649 : Blo 2277435 5128649 := bstep (se 2 (by rfl) ⟨1923243, by rfl⟩ : syracuseStep 5128649 = 3846487) B3846487
theorem B3419099 : Blo 2277435 3419099 := bstep (se 1 (by rfl) ⟨2564324, by rfl⟩ : syracuseStep 3419099 = 5128649) B5128649
theorem B2279399 : Blo 2277435 2279399 := bstep (se 1 (by rfl) ⟨1709549, by rfl⟩ : syracuseStep 2279399 = 3419099) B3419099
theorem B2564329 : Blo 2277435 2564329 := bbase (se 2 (by rfl) ⟨961623, by rfl⟩ : syracuseStep 2564329 = 1923247) (by norm_num)
theorem B3419105 : Blo 2277435 3419105 := bstep (se 2 (by rfl) ⟨1282164, by rfl⟩ : syracuseStep 3419105 = 2564329) B2564329
theorem B2279403 : Blo 2277435 2279403 := bstep (se 1 (by rfl) ⟨1709552, by rfl⟩ : syracuseStep 2279403 = 3419105) B3419105
theorem B12981941 : Blo 2277435 12981941 := bbase (se 5 (by rfl) ⟨608528, by rfl⟩ : syracuseStep 12981941 = 1217057) (by norm_num)
theorem B8654627 : Blo 2277435 8654627 := bstep (se 1 (by rfl) ⟨6490970, by rfl⟩ : syracuseStep 8654627 = 12981941) B12981941
theorem B5769751 : Blo 2277435 5769751 := bstep (se 1 (by rfl) ⟨4327313, by rfl⟩ : syracuseStep 5769751 = 8654627) B8654627
theorem B7693001 : Blo 2277435 7693001 := bstep (se 2 (by rfl) ⟨2884875, by rfl⟩ : syracuseStep 7693001 = 5769751) B5769751
theorem B5128667 : Blo 2277435 5128667 := bstep (se 1 (by rfl) ⟨3846500, by rfl⟩ : syracuseStep 5128667 = 7693001) B7693001
theorem B3419111 : Blo 2277435 3419111 := bstep (se 1 (by rfl) ⟨2564333, by rfl⟩ : syracuseStep 3419111 = 5128667) B5128667
theorem B2279407 : Blo 2277435 2279407 := bstep (se 1 (by rfl) ⟨1709555, by rfl⟩ : syracuseStep 2279407 = 3419111) B3419111
theorem B3419117 : Blo 2277435 3419117 := bbase (se 3 (by rfl) ⟨641084, by rfl⟩ : syracuseStep 3419117 = 1282169) (by norm_num)
theorem B2279411 : Blo 2277435 2279411 := bstep (se 1 (by rfl) ⟨1709558, by rfl⟩ : syracuseStep 2279411 = 3419117) B3419117
theorem B5128685 : Blo 2277435 5128685 := bbase (se 3 (by rfl) ⟨961628, by rfl⟩ : syracuseStep 5128685 = 1923257) (by norm_num)
theorem B3419123 : Blo 2277435 3419123 := bstep (se 1 (by rfl) ⟨2564342, by rfl⟩ : syracuseStep 3419123 = 5128685) B5128685
theorem B2279415 : Blo 2277435 2279415 := bstep (se 1 (by rfl) ⟨1709561, by rfl⟩ : syracuseStep 2279415 = 3419123) B3419123
theorem B5269597 : Blo 2277435 5269597 := bbase (se 3 (by rfl) ⟨988049, by rfl⟩ : syracuseStep 5269597 = 1976099) (by norm_num)
theorem B28104517 : Blo 2277435 28104517 := bstep (se 4 (by rfl) ⟨2634798, by rfl⟩ : syracuseStep 28104517 = 5269597) B5269597
theorem B37472689 : Blo 2277435 37472689 := bstep (se 2 (by rfl) ⟨14052258, by rfl⟩ : syracuseStep 37472689 = 28104517) B28104517
theorem B199854341 : Blo 2277435 199854341 := bstep (se 4 (by rfl) ⟨18736344, by rfl⟩ : syracuseStep 199854341 = 37472689) B37472689
theorem B133236227 : Blo 2277435 133236227 := bstep (se 1 (by rfl) ⟨99927170, by rfl⟩ : syracuseStep 133236227 = 199854341) B199854341
theorem B88824151 : Blo 2277435 88824151 := bstep (se 1 (by rfl) ⟨66618113, by rfl⟩ : syracuseStep 88824151 = 133236227) B133236227
theorem B118432201 : Blo 2277435 118432201 := bstep (se 2 (by rfl) ⟨44412075, by rfl⟩ : syracuseStep 118432201 = 88824151) B88824151
theorem B157909601 : Blo 2277435 157909601 := bstep (se 2 (by rfl) ⟨59216100, by rfl⟩ : syracuseStep 157909601 = 118432201) B118432201
theorem B105273067 : Blo 2277435 105273067 := bstep (se 1 (by rfl) ⟨78954800, by rfl⟩ : syracuseStep 105273067 = 157909601) B157909601
theorem B140364089 : Blo 2277435 140364089 := bstep (se 2 (by rfl) ⟨52636533, by rfl⟩ : syracuseStep 140364089 = 105273067) B105273067
theorem B93576059 : Blo 2277435 93576059 := bstep (se 1 (by rfl) ⟨70182044, by rfl⟩ : syracuseStep 93576059 = 140364089) B140364089
theorem B62384039 : Blo 2277435 62384039 := bstep (se 1 (by rfl) ⟨46788029, by rfl⟩ : syracuseStep 62384039 = 93576059) B93576059
theorem B41589359 : Blo 2277435 41589359 := bstep (se 1 (by rfl) ⟨31192019, by rfl⟩ : syracuseStep 41589359 = 62384039) B62384039
theorem B27726239 : Blo 2277435 27726239 := bstep (se 1 (by rfl) ⟨20794679, by rfl⟩ : syracuseStep 27726239 = 41589359) B41589359
theorem B18484159 : Blo 2277435 18484159 := bstep (se 1 (by rfl) ⟨13863119, by rfl⟩ : syracuseStep 18484159 = 27726239) B27726239
theorem B24645545 : Blo 2277435 24645545 := bstep (se 2 (by rfl) ⟨9242079, by rfl⟩ : syracuseStep 24645545 = 18484159) B18484159
theorem B16430363 : Blo 2277435 16430363 := bstep (se 1 (by rfl) ⟨12322772, by rfl⟩ : syracuseStep 16430363 = 24645545) B24645545
theorem B10953575 : Blo 2277435 10953575 := bstep (se 1 (by rfl) ⟨8215181, by rfl⟩ : syracuseStep 10953575 = 16430363) B16430363
theorem B7302383 : Blo 2277435 7302383 := bstep (se 1 (by rfl) ⟨5476787, by rfl⟩ : syracuseStep 7302383 = 10953575) B10953575
theorem B4868255 : Blo 2277435 4868255 := bstep (se 1 (by rfl) ⟨3651191, by rfl⟩ : syracuseStep 4868255 = 7302383) B7302383
theorem B3245503 : Blo 2277435 3245503 := bstep (se 1 (by rfl) ⟨2434127, by rfl⟩ : syracuseStep 3245503 = 4868255) B4868255
theorem B4327337 : Blo 2277435 4327337 := bstep (se 2 (by rfl) ⟨1622751, by rfl⟩ : syracuseStep 4327337 = 3245503) B3245503
theorem B2884891 : Blo 2277435 2884891 := bstep (se 1 (by rfl) ⟨2163668, by rfl⟩ : syracuseStep 2884891 = 4327337) B4327337
theorem B3846521 : Blo 2277435 3846521 := bstep (se 2 (by rfl) ⟨1442445, by rfl⟩ : syracuseStep 3846521 = 2884891) B2884891
theorem B2564347 : Blo 2277435 2564347 := bstep (se 1 (by rfl) ⟨1923260, by rfl⟩ : syracuseStep 2564347 = 3846521) B3846521
theorem B3419129 : Blo 2277435 3419129 := bstep (se 2 (by rfl) ⟨1282173, by rfl⟩ : syracuseStep 3419129 = 2564347) B2564347
theorem B2279419 : Blo 2277435 2279419 := bstep (se 1 (by rfl) ⟨1709564, by rfl⟩ : syracuseStep 2279419 = 3419129) B3419129
theorem B4446229 : Blo 2277435 4446229 := bbase (se 6 (by rfl) ⟨104208, by rfl⟩ : syracuseStep 4446229 = 208417) (by norm_num)
theorem B5928305 : Blo 2277435 5928305 := bstep (se 2 (by rfl) ⟨2223114, by rfl⟩ : syracuseStep 5928305 = 4446229) B4446229
theorem B15808813 : Blo 2277435 15808813 := bstep (se 3 (by rfl) ⟨2964152, by rfl⟩ : syracuseStep 15808813 = 5928305) B5928305
theorem B84313669 : Blo 2277435 84313669 := bstep (se 4 (by rfl) ⟨7904406, by rfl⟩ : syracuseStep 84313669 = 15808813) B15808813
theorem B112418225 : Blo 2277435 112418225 := bstep (se 2 (by rfl) ⟨42156834, by rfl⟩ : syracuseStep 112418225 = 84313669) B84313669
theorem B74945483 : Blo 2277435 74945483 := bstep (se 1 (by rfl) ⟨56209112, by rfl⟩ : syracuseStep 74945483 = 112418225) B112418225
theorem B49963655 : Blo 2277435 49963655 := bstep (se 1 (by rfl) ⟨37472741, by rfl⟩ : syracuseStep 49963655 = 74945483) B74945483
theorem B33309103 : Blo 2277435 33309103 := bstep (se 1 (by rfl) ⟨24981827, by rfl⟩ : syracuseStep 33309103 = 49963655) B49963655
theorem B44412137 : Blo 2277435 44412137 := bstep (se 2 (by rfl) ⟨16654551, by rfl⟩ : syracuseStep 44412137 = 33309103) B33309103
theorem B29608091 : Blo 2277435 29608091 := bstep (se 1 (by rfl) ⟨22206068, by rfl⟩ : syracuseStep 29608091 = 44412137) B44412137
theorem B19738727 : Blo 2277435 19738727 := bstep (se 1 (by rfl) ⟨14804045, by rfl⟩ : syracuseStep 19738727 = 29608091) B29608091
theorem B13159151 : Blo 2277435 13159151 := bstep (se 1 (by rfl) ⟨9869363, by rfl⟩ : syracuseStep 13159151 = 19738727) B19738727
theorem B8772767 : Blo 2277435 8772767 := bstep (se 1 (by rfl) ⟨6579575, by rfl⟩ : syracuseStep 8772767 = 13159151) B13159151
theorem B5848511 : Blo 2277435 5848511 := bstep (se 1 (by rfl) ⟨4386383, by rfl⟩ : syracuseStep 5848511 = 8772767) B8772767
theorem B15596029 : Blo 2277435 15596029 := bstep (se 3 (by rfl) ⟨2924255, by rfl⟩ : syracuseStep 15596029 = 5848511) B5848511
theorem B83178821 : Blo 2277435 83178821 := bstep (se 4 (by rfl) ⟨7798014, by rfl⟩ : syracuseStep 83178821 = 15596029) B15596029
theorem B55452547 : Blo 2277435 55452547 := bstep (se 1 (by rfl) ⟨41589410, by rfl⟩ : syracuseStep 55452547 = 83178821) B83178821
theorem B73936729 : Blo 2277435 73936729 := bstep (se 2 (by rfl) ⟨27726273, by rfl⟩ : syracuseStep 73936729 = 55452547) B55452547
theorem B98582305 : Blo 2277435 98582305 := bstep (se 2 (by rfl) ⟨36968364, by rfl⟩ : syracuseStep 98582305 = 73936729) B73936729
theorem B131443073 : Blo 2277435 131443073 := bstep (se 2 (by rfl) ⟨49291152, by rfl⟩ : syracuseStep 131443073 = 98582305) B98582305
theorem B87628715 : Blo 2277435 87628715 := bstep (se 1 (by rfl) ⟨65721536, by rfl⟩ : syracuseStep 87628715 = 131443073) B131443073
theorem B58419143 : Blo 2277435 58419143 := bstep (se 1 (by rfl) ⟨43814357, by rfl⟩ : syracuseStep 58419143 = 87628715) B87628715
theorem B38946095 : Blo 2277435 38946095 := bstep (se 1 (by rfl) ⟨29209571, by rfl⟩ : syracuseStep 38946095 = 58419143) B58419143
theorem B25964063 : Blo 2277435 25964063 := bstep (se 1 (by rfl) ⟨19473047, by rfl⟩ : syracuseStep 25964063 = 38946095) B38946095
theorem B17309375 : Blo 2277435 17309375 := bstep (se 1 (by rfl) ⟨12982031, by rfl⟩ : syracuseStep 17309375 = 25964063) B25964063
theorem B11539583 : Blo 2277435 11539583 := bstep (se 1 (by rfl) ⟨8654687, by rfl⟩ : syracuseStep 11539583 = 17309375) B17309375
theorem B7693055 : Blo 2277435 7693055 := bstep (se 1 (by rfl) ⟨5769791, by rfl⟩ : syracuseStep 7693055 = 11539583) B11539583
theorem B5128703 : Blo 2277435 5128703 := bstep (se 1 (by rfl) ⟨3846527, by rfl⟩ : syracuseStep 5128703 = 7693055) B7693055
theorem B3419135 : Blo 2277435 3419135 := bstep (se 1 (by rfl) ⟨2564351, by rfl⟩ : syracuseStep 3419135 = 5128703) B5128703
theorem B2279423 : Blo 2277435 2279423 := bstep (se 1 (by rfl) ⟨1709567, by rfl⟩ : syracuseStep 2279423 = 3419135) B3419135
theorem B3419141 : Blo 2277435 3419141 := bbase (se 4 (by rfl) ⟨320544, by rfl⟩ : syracuseStep 3419141 = 641089) (by norm_num)
theorem B2279427 : Blo 2277435 2279427 := bstep (se 1 (by rfl) ⟨1709570, by rfl⟩ : syracuseStep 2279427 = 3419141) B3419141
theorem B3846541 : Blo 2277435 3846541 := bbase (se 3 (by rfl) ⟨721226, by rfl⟩ : syracuseStep 3846541 = 1442453) (by norm_num)
theorem B5128721 : Blo 2277435 5128721 := bstep (se 2 (by rfl) ⟨1923270, by rfl⟩ : syracuseStep 5128721 = 3846541) B3846541
theorem B3419147 : Blo 2277435 3419147 := bstep (se 1 (by rfl) ⟨2564360, by rfl⟩ : syracuseStep 3419147 = 5128721) B5128721
theorem B2279431 : Blo 2277435 2279431 := bstep (se 1 (by rfl) ⟨1709573, by rfl⟩ : syracuseStep 2279431 = 3419147) B3419147
theorem B2564365 : Blo 2277435 2564365 := bbase (se 3 (by rfl) ⟨480818, by rfl⟩ : syracuseStep 2564365 = 961637) (by norm_num)
theorem B3419153 : Blo 2277435 3419153 := bstep (se 2 (by rfl) ⟨1282182, by rfl⟩ : syracuseStep 3419153 = 2564365) B2564365
theorem B2279435 : Blo 2277435 2279435 := bstep (se 1 (by rfl) ⟨1709576, by rfl⟩ : syracuseStep 2279435 = 3419153) B3419153
theorem C0 (j : ℕ) (h1 : 569358 ≤ j) (h2 : j ≤ 569858) : Blo 2277435 (4 * j + 3) := by
  interval_cases j
  · exact B2277435
  · exact B2277439
  · exact B2277443
  · exact B2277447
  · exact B2277451
  · exact B2277455
  · exact B2277459
  · exact B2277463
  · exact B2277467
  · exact B2277471
  · exact B2277475
  · exact B2277479
  · exact B2277483
  · exact B2277487
  · exact B2277491
  · exact B2277495
  · exact B2277499
  · exact B2277503
  · exact B2277507
  · exact B2277511
  · exact B2277515
  · exact B2277519
  · exact B2277523
  · exact B2277527
  · exact B2277531
  · exact B2277535
  · exact B2277539
  · exact B2277543
  · exact B2277547
  · exact B2277551
  · exact B2277555
  · exact B2277559
  · exact B2277563
  · exact B2277567
  · exact B2277571
  · exact B2277575
  · exact B2277579
  · exact B2277583
  · exact B2277587
  · exact B2277591
  · exact B2277595
  · exact B2277599
  · exact B2277603
  · exact B2277607
  · exact B2277611
  · exact B2277615
  · exact B2277619
  · exact B2277623
  · exact B2277627
  · exact B2277631
  · exact B2277635
  · exact B2277639
  · exact B2277643
  · exact B2277647
  · exact B2277651
  · exact B2277655
  · exact B2277659
  · exact B2277663
  · exact B2277667
  · exact B2277671
  · exact B2277675
  · exact B2277679
  · exact B2277683
  · exact B2277687
  · exact B2277691
  · exact B2277695
  · exact B2277699
  · exact B2277703
  · exact B2277707
  · exact B2277711
  · exact B2277715
  · exact B2277719
  · exact B2277723
  · exact B2277727
  · exact B2277731
  · exact B2277735
  · exact B2277739
  · exact B2277743
  · exact B2277747
  · exact B2277751
  · exact B2277755
  · exact B2277759
  · exact B2277763
  · exact B2277767
  · exact B2277771
  · exact B2277775
  · exact B2277779
  · exact B2277783
  · exact B2277787
  · exact B2277791
  · exact B2277795
  · exact B2277799
  · exact B2277803
  · exact B2277807
  · exact B2277811
  · exact B2277815
  · exact B2277819
  · exact B2277823
  · exact B2277827
  · exact B2277831
  · exact B2277835
  · exact B2277839
  · exact B2277843
  · exact B2277847
  · exact B2277851
  · exact B2277855
  · exact B2277859
  · exact B2277863
  · exact B2277867
  · exact B2277871
  · exact B2277875
  · exact B2277879
  · exact B2277883
  · exact B2277887
  · exact B2277891
  · exact B2277895
  · exact B2277899
  · exact B2277903
  · exact B2277907
  · exact B2277911
  · exact B2277915
  · exact B2277919
  · exact B2277923
  · exact B2277927
  · exact B2277931
  · exact B2277935
  · exact B2277939
  · exact B2277943
  · exact B2277947
  · exact B2277951
  · exact B2277955
  · exact B2277959
  · exact B2277963
  · exact B2277967
  · exact B2277971
  · exact B2277975
  · exact B2277979
  · exact B2277983
  · exact B2277987
  · exact B2277991
  · exact B2277995
  · exact B2277999
  · exact B2278003
  · exact B2278007
  · exact B2278011
  · exact B2278015
  · exact B2278019
  · exact B2278023
  · exact B2278027
  · exact B2278031
  · exact B2278035
  · exact B2278039
  · exact B2278043
  · exact B2278047
  · exact B2278051
  · exact B2278055
  · exact B2278059
  · exact B2278063
  · exact B2278067
  · exact B2278071
  · exact B2278075
  · exact B2278079
  · exact B2278083
  · exact B2278087
  · exact B2278091
  · exact B2278095
  · exact B2278099
  · exact B2278103
  · exact B2278107
  · exact B2278111
  · exact B2278115
  · exact B2278119
  · exact B2278123
  · exact B2278127
  · exact B2278131
  · exact B2278135
  · exact B2278139
  · exact B2278143
  · exact B2278147
  · exact B2278151
  · exact B2278155
  · exact B2278159
  · exact B2278163
  · exact B2278167
  · exact B2278171
  · exact B2278175
  · exact B2278179
  · exact B2278183
  · exact B2278187
  · exact B2278191
  · exact B2278195
  · exact B2278199
  · exact B2278203
  · exact B2278207
  · exact B2278211
  · exact B2278215
  · exact B2278219
  · exact B2278223
  · exact B2278227
  · exact B2278231
  · exact B2278235
  · exact B2278239
  · exact B2278243
  · exact B2278247
  · exact B2278251
  · exact B2278255
  · exact B2278259
  · exact B2278263
  · exact B2278267
  · exact B2278271
  · exact B2278275
  · exact B2278279
  · exact B2278283
  · exact B2278287
  · exact B2278291
  · exact B2278295
  · exact B2278299
  · exact B2278303
  · exact B2278307
  · exact B2278311
  · exact B2278315
  · exact B2278319
  · exact B2278323
  · exact B2278327
  · exact B2278331
  · exact B2278335
  · exact B2278339
  · exact B2278343
  · exact B2278347
  · exact B2278351
  · exact B2278355
  · exact B2278359
  · exact B2278363
  · exact B2278367
  · exact B2278371
  · exact B2278375
  · exact B2278379
  · exact B2278383
  · exact B2278387
  · exact B2278391
  · exact B2278395
  · exact B2278399
  · exact B2278403
  · exact B2278407
  · exact B2278411
  · exact B2278415
  · exact B2278419
  · exact B2278423
  · exact B2278427
  · exact B2278431
  · exact B2278435
  · exact B2278439
  · exact B2278443
  · exact B2278447
  · exact B2278451
  · exact B2278455
  · exact B2278459
  · exact B2278463
  · exact B2278467
  · exact B2278471
  · exact B2278475
  · exact B2278479
  · exact B2278483
  · exact B2278487
  · exact B2278491
  · exact B2278495
  · exact B2278499
  · exact B2278503
  · exact B2278507
  · exact B2278511
  · exact B2278515
  · exact B2278519
  · exact B2278523
  · exact B2278527
  · exact B2278531
  · exact B2278535
  · exact B2278539
  · exact B2278543
  · exact B2278547
  · exact B2278551
  · exact B2278555
  · exact B2278559
  · exact B2278563
  · exact B2278567
  · exact B2278571
  · exact B2278575
  · exact B2278579
  · exact B2278583
  · exact B2278587
  · exact B2278591
  · exact B2278595
  · exact B2278599
  · exact B2278603
  · exact B2278607
  · exact B2278611
  · exact B2278615
  · exact B2278619
  · exact B2278623
  · exact B2278627
  · exact B2278631
  · exact B2278635
  · exact B2278639
  · exact B2278643
  · exact B2278647
  · exact B2278651
  · exact B2278655
  · exact B2278659
  · exact B2278663
  · exact B2278667
  · exact B2278671
  · exact B2278675
  · exact B2278679
  · exact B2278683
  · exact B2278687
  · exact B2278691
  · exact B2278695
  · exact B2278699
  · exact B2278703
  · exact B2278707
  · exact B2278711
  · exact B2278715
  · exact B2278719
  · exact B2278723
  · exact B2278727
  · exact B2278731
  · exact B2278735
  · exact B2278739
  · exact B2278743
  · exact B2278747
  · exact B2278751
  · exact B2278755
  · exact B2278759
  · exact B2278763
  · exact B2278767
  · exact B2278771
  · exact B2278775
  · exact B2278779
  · exact B2278783
  · exact B2278787
  · exact B2278791
  · exact B2278795
  · exact B2278799
  · exact B2278803
  · exact B2278807
  · exact B2278811
  · exact B2278815
  · exact B2278819
  · exact B2278823
  · exact B2278827
  · exact B2278831
  · exact B2278835
  · exact B2278839
  · exact B2278843
  · exact B2278847
  · exact B2278851
  · exact B2278855
  · exact B2278859
  · exact B2278863
  · exact B2278867
  · exact B2278871
  · exact B2278875
  · exact B2278879
  · exact B2278883
  · exact B2278887
  · exact B2278891
  · exact B2278895
  · exact B2278899
  · exact B2278903
  · exact B2278907
  · exact B2278911
  · exact B2278915
  · exact B2278919
  · exact B2278923
  · exact B2278927
  · exact B2278931
  · exact B2278935
  · exact B2278939
  · exact B2278943
  · exact B2278947
  · exact B2278951
  · exact B2278955
  · exact B2278959
  · exact B2278963
  · exact B2278967
  · exact B2278971
  · exact B2278975
  · exact B2278979
  · exact B2278983
  · exact B2278987
  · exact B2278991
  · exact B2278995
  · exact B2278999
  · exact B2279003
  · exact B2279007
  · exact B2279011
  · exact B2279015
  · exact B2279019
  · exact B2279023
  · exact B2279027
  · exact B2279031
  · exact B2279035
  · exact B2279039
  · exact B2279043
  · exact B2279047
  · exact B2279051
  · exact B2279055
  · exact B2279059
  · exact B2279063
  · exact B2279067
  · exact B2279071
  · exact B2279075
  · exact B2279079
  · exact B2279083
  · exact B2279087
  · exact B2279091
  · exact B2279095
  · exact B2279099
  · exact B2279103
  · exact B2279107
  · exact B2279111
  · exact B2279115
  · exact B2279119
  · exact B2279123
  · exact B2279127
  · exact B2279131
  · exact B2279135
  · exact B2279139
  · exact B2279143
  · exact B2279147
  · exact B2279151
  · exact B2279155
  · exact B2279159
  · exact B2279163
  · exact B2279167
  · exact B2279171
  · exact B2279175
  · exact B2279179
  · exact B2279183
  · exact B2279187
  · exact B2279191
  · exact B2279195
  · exact B2279199
  · exact B2279203
  · exact B2279207
  · exact B2279211
  · exact B2279215
  · exact B2279219
  · exact B2279223
  · exact B2279227
  · exact B2279231
  · exact B2279235
  · exact B2279239
  · exact B2279243
  · exact B2279247
  · exact B2279251
  · exact B2279255
  · exact B2279259
  · exact B2279263
  · exact B2279267
  · exact B2279271
  · exact B2279275
  · exact B2279279
  · exact B2279283
  · exact B2279287
  · exact B2279291
  · exact B2279295
  · exact B2279299
  · exact B2279303
  · exact B2279307
  · exact B2279311
  · exact B2279315
  · exact B2279319
  · exact B2279323
  · exact B2279327
  · exact B2279331
  · exact B2279335
  · exact B2279339
  · exact B2279343
  · exact B2279347
  · exact B2279351
  · exact B2279355
  · exact B2279359
  · exact B2279363
  · exact B2279367
  · exact B2279371
  · exact B2279375
  · exact B2279379
  · exact B2279383
  · exact B2279387
  · exact B2279391
  · exact B2279395
  · exact B2279399
  · exact B2279403
  · exact B2279407
  · exact B2279411
  · exact B2279415
  · exact B2279419
  · exact B2279423
  · exact B2279427
  · exact B2279431
  · exact B2279435
theorem solution (m : ℕ) (hlo : 2277435 ≤ m) (hhi : m ≤ 2279435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 569358 ≤ j := by omega
    have hj2 : j ≤ 569858 := by omega
    have hb : Blo 2277435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
