-- Prove2me | solution 1 for syracuse_descends_range_2175435_2177435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:51.917145+00:00
-- url     : https://prove2.me/submissions/686d0a94-7f6f-4c8b-9fda-63d5c4d5a2b0

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

theorem B2447365 : Blo 2175435 2447365 := bbase (se 4 (by rfl) ⟨229440, by rfl⟩ : syracuseStep 2447365 = 458881) (by norm_num)
theorem B3263153 : Blo 2175435 3263153 := bstep (se 2 (by rfl) ⟨1223682, by rfl⟩ : syracuseStep 3263153 = 2447365) B2447365
theorem B2175435 : Blo 2175435 2175435 := bstep (se 1 (by rfl) ⟨1631576, by rfl⟩ : syracuseStep 2175435 = 3263153) B3263153
theorem B3097453 : Blo 2175435 3097453 := bbase (se 3 (by rfl) ⟨580772, by rfl⟩ : syracuseStep 3097453 = 1161545) (by norm_num)
theorem B4129937 : Blo 2175435 4129937 := bstep (se 2 (by rfl) ⟨1548726, by rfl⟩ : syracuseStep 4129937 = 3097453) B3097453
theorem B2753291 : Blo 2175435 2753291 := bstep (se 1 (by rfl) ⟨2064968, by rfl⟩ : syracuseStep 2753291 = 4129937) B4129937
theorem B7342109 : Blo 2175435 7342109 := bstep (se 3 (by rfl) ⟨1376645, by rfl⟩ : syracuseStep 7342109 = 2753291) B2753291
theorem B4894739 : Blo 2175435 4894739 := bstep (se 1 (by rfl) ⟨3671054, by rfl⟩ : syracuseStep 4894739 = 7342109) B7342109
theorem B3263159 : Blo 2175435 3263159 := bstep (se 1 (by rfl) ⟨2447369, by rfl⟩ : syracuseStep 3263159 = 4894739) B4894739
theorem B2175439 : Blo 2175435 2175439 := bstep (se 1 (by rfl) ⟨1631579, by rfl⟩ : syracuseStep 2175439 = 3263159) B3263159
theorem B3263165 : Blo 2175435 3263165 := bbase (se 3 (by rfl) ⟨611843, by rfl⟩ : syracuseStep 3263165 = 1223687) (by norm_num)
theorem B2175443 : Blo 2175435 2175443 := bstep (se 1 (by rfl) ⟨1631582, by rfl⟩ : syracuseStep 2175443 = 3263165) B3263165
theorem B4894757 : Blo 2175435 4894757 := bbase (se 4 (by rfl) ⟨458883, by rfl⟩ : syracuseStep 4894757 = 917767) (by norm_num)
theorem B3263171 : Blo 2175435 3263171 := bstep (se 1 (by rfl) ⟨2447378, by rfl⟩ : syracuseStep 3263171 = 4894757) B4894757
theorem B2175447 : Blo 2175435 2175447 := bstep (se 1 (by rfl) ⟨1631585, by rfl⟩ : syracuseStep 2175447 = 3263171) B3263171
theorem B5506613 : Blo 2175435 5506613 := bbase (se 5 (by rfl) ⟨258122, by rfl⟩ : syracuseStep 5506613 = 516245) (by norm_num)
theorem B3671075 : Blo 2175435 3671075 := bstep (se 1 (by rfl) ⟨2753306, by rfl⟩ : syracuseStep 3671075 = 5506613) B5506613
theorem B2447383 : Blo 2175435 2447383 := bstep (se 1 (by rfl) ⟨1835537, by rfl⟩ : syracuseStep 2447383 = 3671075) B3671075
theorem B3263177 : Blo 2175435 3263177 := bstep (se 2 (by rfl) ⟨1223691, by rfl⟩ : syracuseStep 3263177 = 2447383) B2447383
theorem B2175451 : Blo 2175435 2175451 := bstep (se 1 (by rfl) ⟨1631588, by rfl⟩ : syracuseStep 2175451 = 3263177) B3263177
theorem B2205137 : Blo 2175435 2205137 := bbase (se 2 (by rfl) ⟨826926, by rfl⟩ : syracuseStep 2205137 = 1653853) (by norm_num)
theorem B5880365 : Blo 2175435 5880365 := bstep (se 3 (by rfl) ⟨1102568, by rfl⟩ : syracuseStep 5880365 = 2205137) B2205137
theorem B3920243 : Blo 2175435 3920243 := bstep (se 1 (by rfl) ⟨2940182, by rfl⟩ : syracuseStep 3920243 = 5880365) B5880365
theorem B10453981 : Blo 2175435 10453981 := bstep (se 3 (by rfl) ⟨1960121, by rfl⟩ : syracuseStep 10453981 = 3920243) B3920243
theorem B13938641 : Blo 2175435 13938641 := bstep (se 2 (by rfl) ⟨5226990, by rfl⟩ : syracuseStep 13938641 = 10453981) B10453981
theorem B9292427 : Blo 2175435 9292427 := bstep (se 1 (by rfl) ⟨6969320, by rfl⟩ : syracuseStep 9292427 = 13938641) B13938641
theorem B6194951 : Blo 2175435 6194951 := bstep (se 1 (by rfl) ⟨4646213, by rfl⟩ : syracuseStep 6194951 = 9292427) B9292427
theorem B4129967 : Blo 2175435 4129967 := bstep (se 1 (by rfl) ⟨3097475, by rfl⟩ : syracuseStep 4129967 = 6194951) B6194951
theorem B11013245 : Blo 2175435 11013245 := bstep (se 3 (by rfl) ⟨2064983, by rfl⟩ : syracuseStep 11013245 = 4129967) B4129967
theorem B7342163 : Blo 2175435 7342163 := bstep (se 1 (by rfl) ⟨5506622, by rfl⟩ : syracuseStep 7342163 = 11013245) B11013245
theorem B4894775 : Blo 2175435 4894775 := bstep (se 1 (by rfl) ⟨3671081, by rfl⟩ : syracuseStep 4894775 = 7342163) B7342163
theorem B3263183 : Blo 2175435 3263183 := bstep (se 1 (by rfl) ⟨2447387, by rfl⟩ : syracuseStep 3263183 = 4894775) B4894775
theorem B2175455 : Blo 2175435 2175455 := bstep (se 1 (by rfl) ⟨1631591, by rfl⟩ : syracuseStep 2175455 = 3263183) B3263183
theorem B3263189 : Blo 2175435 3263189 := bbase (se 7 (by rfl) ⟨38240, by rfl⟩ : syracuseStep 3263189 = 76481) (by norm_num)
theorem B2175459 : Blo 2175435 2175459 := bstep (se 1 (by rfl) ⟨1631594, by rfl⟩ : syracuseStep 2175459 = 3263189) B3263189
theorem B10454021 : Blo 2175435 10454021 := bbase (se 4 (by rfl) ⟨980064, by rfl⟩ : syracuseStep 10454021 = 1960129) (by norm_num)
theorem B6969347 : Blo 2175435 6969347 := bstep (se 1 (by rfl) ⟨5227010, by rfl⟩ : syracuseStep 6969347 = 10454021) B10454021
theorem B4646231 : Blo 2175435 4646231 := bstep (se 1 (by rfl) ⟨3484673, by rfl⟩ : syracuseStep 4646231 = 6969347) B6969347
theorem B3097487 : Blo 2175435 3097487 := bstep (se 1 (by rfl) ⟨2323115, by rfl⟩ : syracuseStep 3097487 = 4646231) B4646231
theorem B8259965 : Blo 2175435 8259965 := bstep (se 3 (by rfl) ⟨1548743, by rfl⟩ : syracuseStep 8259965 = 3097487) B3097487
theorem B5506643 : Blo 2175435 5506643 := bstep (se 1 (by rfl) ⟨4129982, by rfl⟩ : syracuseStep 5506643 = 8259965) B8259965
theorem B3671095 : Blo 2175435 3671095 := bstep (se 1 (by rfl) ⟨2753321, by rfl⟩ : syracuseStep 3671095 = 5506643) B5506643
theorem B4894793 : Blo 2175435 4894793 := bstep (se 2 (by rfl) ⟨1835547, by rfl⟩ : syracuseStep 4894793 = 3671095) B3671095
theorem B3263195 : Blo 2175435 3263195 := bstep (se 1 (by rfl) ⟨2447396, by rfl⟩ : syracuseStep 3263195 = 4894793) B4894793
theorem B2175463 : Blo 2175435 2175463 := bstep (se 1 (by rfl) ⟨1631597, by rfl⟩ : syracuseStep 2175463 = 3263195) B3263195
theorem B2447401 : Blo 2175435 2447401 := bbase (se 2 (by rfl) ⟨917775, by rfl⟩ : syracuseStep 2447401 = 1835551) (by norm_num)
theorem B3263201 : Blo 2175435 3263201 := bstep (se 2 (by rfl) ⟨1223700, by rfl⟩ : syracuseStep 3263201 = 2447401) B2447401
theorem B2175467 : Blo 2175435 2175467 := bstep (se 1 (by rfl) ⟨1631600, by rfl⟩ : syracuseStep 2175467 = 3263201) B3263201
theorem B2685317 : Blo 2175435 2685317 := bbase (se 4 (by rfl) ⟨251748, by rfl⟩ : syracuseStep 2685317 = 503497) (by norm_num)
theorem B28643381 : Blo 2175435 28643381 := bstep (se 5 (by rfl) ⟨1342658, by rfl⟩ : syracuseStep 28643381 = 2685317) B2685317
theorem B19095587 : Blo 2175435 19095587 := bstep (se 1 (by rfl) ⟨14321690, by rfl⟩ : syracuseStep 19095587 = 28643381) B28643381
theorem B12730391 : Blo 2175435 12730391 := bstep (se 1 (by rfl) ⟨9547793, by rfl⟩ : syracuseStep 12730391 = 19095587) B19095587
theorem B8486927 : Blo 2175435 8486927 := bstep (se 1 (by rfl) ⟨6365195, by rfl⟩ : syracuseStep 8486927 = 12730391) B12730391
theorem B5657951 : Blo 2175435 5657951 := bstep (se 1 (by rfl) ⟨4243463, by rfl⟩ : syracuseStep 5657951 = 8486927) B8486927
theorem B15087869 : Blo 2175435 15087869 := bstep (se 3 (by rfl) ⟨2828975, by rfl⟩ : syracuseStep 15087869 = 5657951) B5657951
theorem B10058579 : Blo 2175435 10058579 := bstep (se 1 (by rfl) ⟨7543934, by rfl⟩ : syracuseStep 10058579 = 15087869) B15087869
theorem B6705719 : Blo 2175435 6705719 := bstep (se 1 (by rfl) ⟨5029289, by rfl⟩ : syracuseStep 6705719 = 10058579) B10058579
theorem B4470479 : Blo 2175435 4470479 := bstep (se 1 (by rfl) ⟨3352859, by rfl⟩ : syracuseStep 4470479 = 6705719) B6705719
theorem B2980319 : Blo 2175435 2980319 := bstep (se 1 (by rfl) ⟨2235239, by rfl⟩ : syracuseStep 2980319 = 4470479) B4470479
theorem B7947517 : Blo 2175435 7947517 := bstep (se 3 (by rfl) ⟨1490159, by rfl⟩ : syracuseStep 7947517 = 2980319) B2980319
theorem B10596689 : Blo 2175435 10596689 := bstep (se 2 (by rfl) ⟨3973758, by rfl⟩ : syracuseStep 10596689 = 7947517) B7947517
theorem B7064459 : Blo 2175435 7064459 := bstep (se 1 (by rfl) ⟨5298344, by rfl⟩ : syracuseStep 7064459 = 10596689) B10596689
theorem B4709639 : Blo 2175435 4709639 := bstep (se 1 (by rfl) ⟨3532229, by rfl⟩ : syracuseStep 4709639 = 7064459) B7064459
theorem B3139759 : Blo 2175435 3139759 := bstep (se 1 (by rfl) ⟨2354819, by rfl⟩ : syracuseStep 3139759 = 4709639) B4709639
theorem B16745381 : Blo 2175435 16745381 := bstep (se 4 (by rfl) ⟨1569879, by rfl⟩ : syracuseStep 16745381 = 3139759) B3139759
theorem B11163587 : Blo 2175435 11163587 := bstep (se 1 (by rfl) ⟨8372690, by rfl⟩ : syracuseStep 11163587 = 16745381) B16745381
theorem B29769565 : Blo 2175435 29769565 := bstep (se 3 (by rfl) ⟨5581793, by rfl⟩ : syracuseStep 29769565 = 11163587) B11163587
theorem B39692753 : Blo 2175435 39692753 := bstep (se 2 (by rfl) ⟨14884782, by rfl⟩ : syracuseStep 39692753 = 29769565) B29769565
theorem B26461835 : Blo 2175435 26461835 := bstep (se 1 (by rfl) ⟨19846376, by rfl⟩ : syracuseStep 26461835 = 39692753) B39692753
theorem B17641223 : Blo 2175435 17641223 := bstep (se 1 (by rfl) ⟨13230917, by rfl⟩ : syracuseStep 17641223 = 26461835) B26461835
theorem B11760815 : Blo 2175435 11760815 := bstep (se 1 (by rfl) ⟨8820611, by rfl⟩ : syracuseStep 11760815 = 17641223) B17641223
theorem B31362173 : Blo 2175435 31362173 := bstep (se 3 (by rfl) ⟨5880407, by rfl⟩ : syracuseStep 31362173 = 11760815) B11760815
theorem B20908115 : Blo 2175435 20908115 := bstep (se 1 (by rfl) ⟨15681086, by rfl⟩ : syracuseStep 20908115 = 31362173) B31362173
theorem B13938743 : Blo 2175435 13938743 := bstep (se 1 (by rfl) ⟨10454057, by rfl⟩ : syracuseStep 13938743 = 20908115) B20908115
theorem B9292495 : Blo 2175435 9292495 := bstep (se 1 (by rfl) ⟨6969371, by rfl⟩ : syracuseStep 9292495 = 13938743) B13938743
theorem B12389993 : Blo 2175435 12389993 := bstep (se 2 (by rfl) ⟨4646247, by rfl⟩ : syracuseStep 12389993 = 9292495) B9292495
theorem B8259995 : Blo 2175435 8259995 := bstep (se 1 (by rfl) ⟨6194996, by rfl⟩ : syracuseStep 8259995 = 12389993) B12389993
theorem B5506663 : Blo 2175435 5506663 := bstep (se 1 (by rfl) ⟨4129997, by rfl⟩ : syracuseStep 5506663 = 8259995) B8259995
theorem B7342217 : Blo 2175435 7342217 := bstep (se 2 (by rfl) ⟨2753331, by rfl⟩ : syracuseStep 7342217 = 5506663) B5506663
theorem B4894811 : Blo 2175435 4894811 := bstep (se 1 (by rfl) ⟨3671108, by rfl⟩ : syracuseStep 4894811 = 7342217) B7342217
theorem B3263207 : Blo 2175435 3263207 := bstep (se 1 (by rfl) ⟨2447405, by rfl⟩ : syracuseStep 3263207 = 4894811) B4894811
theorem B2175471 : Blo 2175435 2175471 := bstep (se 1 (by rfl) ⟨1631603, by rfl⟩ : syracuseStep 2175471 = 3263207) B3263207
theorem B3263213 : Blo 2175435 3263213 := bbase (se 3 (by rfl) ⟨611852, by rfl⟩ : syracuseStep 3263213 = 1223705) (by norm_num)
theorem B2175475 : Blo 2175435 2175475 := bstep (se 1 (by rfl) ⟨1631606, by rfl⟩ : syracuseStep 2175475 = 3263213) B3263213
theorem B4894829 : Blo 2175435 4894829 := bbase (se 3 (by rfl) ⟨917780, by rfl⟩ : syracuseStep 4894829 = 1835561) (by norm_num)
theorem B3263219 : Blo 2175435 3263219 := bstep (se 1 (by rfl) ⟨2447414, by rfl⟩ : syracuseStep 3263219 = 4894829) B4894829
theorem B2175479 : Blo 2175435 2175479 := bstep (se 1 (by rfl) ⟨1631609, by rfl⟩ : syracuseStep 2175479 = 3263219) B3263219
theorem B4130021 : Blo 2175435 4130021 := bbase (se 4 (by rfl) ⟨387189, by rfl⟩ : syracuseStep 4130021 = 774379) (by norm_num)
theorem B2753347 : Blo 2175435 2753347 := bstep (se 1 (by rfl) ⟨2065010, by rfl⟩ : syracuseStep 2753347 = 4130021) B4130021
theorem B3671129 : Blo 2175435 3671129 := bstep (se 2 (by rfl) ⟨1376673, by rfl⟩ : syracuseStep 3671129 = 2753347) B2753347
theorem B2447419 : Blo 2175435 2447419 := bstep (se 1 (by rfl) ⟨1835564, by rfl⟩ : syracuseStep 2447419 = 3671129) B3671129
theorem B3263225 : Blo 2175435 3263225 := bstep (se 2 (by rfl) ⟨1223709, by rfl⟩ : syracuseStep 3263225 = 2447419) B2447419
theorem B2175483 : Blo 2175435 2175483 := bstep (se 1 (by rfl) ⟨1631612, by rfl⟩ : syracuseStep 2175483 = 3263225) B3263225
theorem B41816533 : Blo 2175435 41816533 := bbase (se 7 (by rfl) ⟨490037, by rfl⟩ : syracuseStep 41816533 = 980075) (by norm_num)
theorem B55755377 : Blo 2175435 55755377 := bstep (se 2 (by rfl) ⟨20908266, by rfl⟩ : syracuseStep 55755377 = 41816533) B41816533
theorem B37170251 : Blo 2175435 37170251 := bstep (se 1 (by rfl) ⟨27877688, by rfl⟩ : syracuseStep 37170251 = 55755377) B55755377
theorem B24780167 : Blo 2175435 24780167 := bstep (se 1 (by rfl) ⟨18585125, by rfl⟩ : syracuseStep 24780167 = 37170251) B37170251
theorem B16520111 : Blo 2175435 16520111 := bstep (se 1 (by rfl) ⟨12390083, by rfl⟩ : syracuseStep 16520111 = 24780167) B24780167
theorem B11013407 : Blo 2175435 11013407 := bstep (se 1 (by rfl) ⟨8260055, by rfl⟩ : syracuseStep 11013407 = 16520111) B16520111
theorem B7342271 : Blo 2175435 7342271 := bstep (se 1 (by rfl) ⟨5506703, by rfl⟩ : syracuseStep 7342271 = 11013407) B11013407
theorem B4894847 : Blo 2175435 4894847 := bstep (se 1 (by rfl) ⟨3671135, by rfl⟩ : syracuseStep 4894847 = 7342271) B7342271
theorem B3263231 : Blo 2175435 3263231 := bstep (se 1 (by rfl) ⟨2447423, by rfl⟩ : syracuseStep 3263231 = 4894847) B4894847
theorem B2175487 : Blo 2175435 2175487 := bstep (se 1 (by rfl) ⟨1631615, by rfl⟩ : syracuseStep 2175487 = 3263231) B3263231
theorem B3263237 : Blo 2175435 3263237 := bbase (se 4 (by rfl) ⟨305928, by rfl⟩ : syracuseStep 3263237 = 611857) (by norm_num)
theorem B2175491 : Blo 2175435 2175491 := bstep (se 1 (by rfl) ⟨1631618, by rfl⟩ : syracuseStep 2175491 = 3263237) B3263237
theorem B3671149 : Blo 2175435 3671149 := bbase (se 3 (by rfl) ⟨688340, by rfl⟩ : syracuseStep 3671149 = 1376681) (by norm_num)
theorem B4894865 : Blo 2175435 4894865 := bstep (se 2 (by rfl) ⟨1835574, by rfl⟩ : syracuseStep 4894865 = 3671149) B3671149
theorem B3263243 : Blo 2175435 3263243 := bstep (se 1 (by rfl) ⟨2447432, by rfl⟩ : syracuseStep 3263243 = 4894865) B4894865
theorem B2175495 : Blo 2175435 2175495 := bstep (se 1 (by rfl) ⟨1631621, by rfl⟩ : syracuseStep 2175495 = 3263243) B3263243
theorem B2447437 : Blo 2175435 2447437 := bbase (se 3 (by rfl) ⟨458894, by rfl⟩ : syracuseStep 2447437 = 917789) (by norm_num)
theorem B3263249 : Blo 2175435 3263249 := bstep (se 2 (by rfl) ⟨1223718, by rfl⟩ : syracuseStep 3263249 = 2447437) B2447437
theorem B2175499 : Blo 2175435 2175499 := bstep (se 1 (by rfl) ⟨1631624, by rfl⟩ : syracuseStep 2175499 = 3263249) B3263249
theorem B7342325 : Blo 2175435 7342325 := bbase (se 5 (by rfl) ⟨344171, by rfl⟩ : syracuseStep 7342325 = 688343) (by norm_num)
theorem B4894883 : Blo 2175435 4894883 := bstep (se 1 (by rfl) ⟨3671162, by rfl⟩ : syracuseStep 4894883 = 7342325) B7342325
theorem B3263255 : Blo 2175435 3263255 := bstep (se 1 (by rfl) ⟨2447441, by rfl⟩ : syracuseStep 3263255 = 4894883) B4894883
theorem B2175503 : Blo 2175435 2175503 := bstep (se 1 (by rfl) ⟨1631627, by rfl⟩ : syracuseStep 2175503 = 3263255) B3263255
theorem B3263261 : Blo 2175435 3263261 := bbase (se 3 (by rfl) ⟨611861, by rfl⟩ : syracuseStep 3263261 = 1223723) (by norm_num)
theorem B2175507 : Blo 2175435 2175507 := bstep (se 1 (by rfl) ⟨1631630, by rfl⟩ : syracuseStep 2175507 = 3263261) B3263261
theorem B4894901 : Blo 2175435 4894901 := bbase (se 5 (by rfl) ⟨229448, by rfl⟩ : syracuseStep 4894901 = 458897) (by norm_num)
theorem B3263267 : Blo 2175435 3263267 := bstep (se 1 (by rfl) ⟨2447450, by rfl⟩ : syracuseStep 3263267 = 4894901) B4894901
theorem B2175511 : Blo 2175435 2175511 := bstep (se 1 (by rfl) ⟨1631633, by rfl⟩ : syracuseStep 2175511 = 3263267) B3263267
theorem B3484757 : Blo 2175435 3484757 := bbase (se 8 (by rfl) ⟨20418, by rfl⟩ : syracuseStep 3484757 = 40837) (by norm_num)
theorem B2323171 : Blo 2175435 2323171 := bstep (se 1 (by rfl) ⟨1742378, by rfl⟩ : syracuseStep 2323171 = 3484757) B3484757
theorem B12390245 : Blo 2175435 12390245 := bstep (se 4 (by rfl) ⟨1161585, by rfl⟩ : syracuseStep 12390245 = 2323171) B2323171
theorem B8260163 : Blo 2175435 8260163 := bstep (se 1 (by rfl) ⟨6195122, by rfl⟩ : syracuseStep 8260163 = 12390245) B12390245
theorem B5506775 : Blo 2175435 5506775 := bstep (se 1 (by rfl) ⟨4130081, by rfl⟩ : syracuseStep 5506775 = 8260163) B8260163
theorem B3671183 : Blo 2175435 3671183 := bstep (se 1 (by rfl) ⟨2753387, by rfl⟩ : syracuseStep 3671183 = 5506775) B5506775
theorem B2447455 : Blo 2175435 2447455 := bstep (se 1 (by rfl) ⟨1835591, by rfl⟩ : syracuseStep 2447455 = 3671183) B3671183
theorem B3263273 : Blo 2175435 3263273 := bstep (se 2 (by rfl) ⟨1223727, by rfl⟩ : syracuseStep 3263273 = 2447455) B2447455
theorem B2175515 : Blo 2175435 2175515 := bstep (se 1 (by rfl) ⟨1631636, by rfl⟩ : syracuseStep 2175515 = 3263273) B3263273
theorem B5658077 : Blo 2175435 5658077 := bbase (se 3 (by rfl) ⟨1060889, by rfl⟩ : syracuseStep 5658077 = 2121779) (by norm_num)
theorem B3772051 : Blo 2175435 3772051 := bstep (se 1 (by rfl) ⟨2829038, by rfl⟩ : syracuseStep 3772051 = 5658077) B5658077
theorem B20117605 : Blo 2175435 20117605 := bstep (se 4 (by rfl) ⟨1886025, by rfl⟩ : syracuseStep 20117605 = 3772051) B3772051
theorem B26823473 : Blo 2175435 26823473 := bstep (se 2 (by rfl) ⟨10058802, by rfl⟩ : syracuseStep 26823473 = 20117605) B20117605
theorem B17882315 : Blo 2175435 17882315 := bstep (se 1 (by rfl) ⟨13411736, by rfl⟩ : syracuseStep 17882315 = 26823473) B26823473
theorem B11921543 : Blo 2175435 11921543 := bstep (se 1 (by rfl) ⟨8941157, by rfl⟩ : syracuseStep 11921543 = 17882315) B17882315
theorem B7947695 : Blo 2175435 7947695 := bstep (se 1 (by rfl) ⟨5960771, by rfl⟩ : syracuseStep 7947695 = 11921543) B11921543
theorem B5298463 : Blo 2175435 5298463 := bstep (se 1 (by rfl) ⟨3973847, by rfl⟩ : syracuseStep 5298463 = 7947695) B7947695
theorem B28258469 : Blo 2175435 28258469 := bstep (se 4 (by rfl) ⟨2649231, by rfl⟩ : syracuseStep 28258469 = 5298463) B5298463
theorem B18838979 : Blo 2175435 18838979 := bstep (se 1 (by rfl) ⟨14129234, by rfl⟩ : syracuseStep 18838979 = 28258469) B28258469
theorem B12559319 : Blo 2175435 12559319 := bstep (se 1 (by rfl) ⟨9419489, by rfl⟩ : syracuseStep 12559319 = 18838979) B18838979
theorem B8372879 : Blo 2175435 8372879 := bstep (se 1 (by rfl) ⟨6279659, by rfl⟩ : syracuseStep 8372879 = 12559319) B12559319
theorem B5581919 : Blo 2175435 5581919 := bstep (se 1 (by rfl) ⟨4186439, by rfl⟩ : syracuseStep 5581919 = 8372879) B8372879
theorem B14885117 : Blo 2175435 14885117 := bstep (se 3 (by rfl) ⟨2790959, by rfl⟩ : syracuseStep 14885117 = 5581919) B5581919
theorem B9923411 : Blo 2175435 9923411 := bstep (se 1 (by rfl) ⟨7442558, by rfl⟩ : syracuseStep 9923411 = 14885117) B14885117
theorem B6615607 : Blo 2175435 6615607 := bstep (se 1 (by rfl) ⟨4961705, by rfl⟩ : syracuseStep 6615607 = 9923411) B9923411
theorem B8820809 : Blo 2175435 8820809 := bstep (se 2 (by rfl) ⟨3307803, by rfl⟩ : syracuseStep 8820809 = 6615607) B6615607
theorem B5880539 : Blo 2175435 5880539 := bstep (se 1 (by rfl) ⟨4410404, by rfl⟩ : syracuseStep 5880539 = 8820809) B8820809
theorem B3920359 : Blo 2175435 3920359 := bstep (se 1 (by rfl) ⟨2940269, by rfl⟩ : syracuseStep 3920359 = 5880539) B5880539
theorem B5227145 : Blo 2175435 5227145 := bstep (se 2 (by rfl) ⟨1960179, by rfl⟩ : syracuseStep 5227145 = 3920359) B3920359
theorem B3484763 : Blo 2175435 3484763 := bstep (se 1 (by rfl) ⟨2613572, by rfl⟩ : syracuseStep 3484763 = 5227145) B5227145
theorem B2323175 : Blo 2175435 2323175 := bstep (se 1 (by rfl) ⟨1742381, by rfl⟩ : syracuseStep 2323175 = 3484763) B3484763
theorem B6195133 : Blo 2175435 6195133 := bstep (se 3 (by rfl) ⟨1161587, by rfl⟩ : syracuseStep 6195133 = 2323175) B2323175
theorem B8260177 : Blo 2175435 8260177 := bstep (se 2 (by rfl) ⟨3097566, by rfl⟩ : syracuseStep 8260177 = 6195133) B6195133
theorem B11013569 : Blo 2175435 11013569 := bstep (se 2 (by rfl) ⟨4130088, by rfl⟩ : syracuseStep 11013569 = 8260177) B8260177
theorem B7342379 : Blo 2175435 7342379 := bstep (se 1 (by rfl) ⟨5506784, by rfl⟩ : syracuseStep 7342379 = 11013569) B11013569
theorem B4894919 : Blo 2175435 4894919 := bstep (se 1 (by rfl) ⟨3671189, by rfl⟩ : syracuseStep 4894919 = 7342379) B7342379
theorem B3263279 : Blo 2175435 3263279 := bstep (se 1 (by rfl) ⟨2447459, by rfl⟩ : syracuseStep 3263279 = 4894919) B4894919
theorem B2175519 : Blo 2175435 2175519 := bstep (se 1 (by rfl) ⟨1631639, by rfl⟩ : syracuseStep 2175519 = 3263279) B3263279
theorem B3263285 : Blo 2175435 3263285 := bbase (se 5 (by rfl) ⟨152966, by rfl⟩ : syracuseStep 3263285 = 305933) (by norm_num)
theorem B2175523 : Blo 2175435 2175523 := bstep (se 1 (by rfl) ⟨1631642, by rfl⟩ : syracuseStep 2175523 = 3263285) B3263285
theorem B5506805 : Blo 2175435 5506805 := bbase (se 5 (by rfl) ⟨258131, by rfl⟩ : syracuseStep 5506805 = 516263) (by norm_num)
theorem B3671203 : Blo 2175435 3671203 := bstep (se 1 (by rfl) ⟨2753402, by rfl⟩ : syracuseStep 3671203 = 5506805) B5506805
theorem B4894937 : Blo 2175435 4894937 := bstep (se 2 (by rfl) ⟨1835601, by rfl⟩ : syracuseStep 4894937 = 3671203) B3671203
theorem B3263291 : Blo 2175435 3263291 := bstep (se 1 (by rfl) ⟨2447468, by rfl⟩ : syracuseStep 3263291 = 4894937) B4894937
theorem B2175527 : Blo 2175435 2175527 := bstep (se 1 (by rfl) ⟨1631645, by rfl⟩ : syracuseStep 2175527 = 3263291) B3263291
theorem B2447473 : Blo 2175435 2447473 := bbase (se 2 (by rfl) ⟨917802, by rfl⟩ : syracuseStep 2447473 = 1835605) (by norm_num)
theorem B3263297 : Blo 2175435 3263297 := bstep (se 2 (by rfl) ⟨1223736, by rfl⟩ : syracuseStep 3263297 = 2447473) B2447473
theorem B2175531 : Blo 2175435 2175531 := bstep (se 1 (by rfl) ⟨1631648, by rfl⟩ : syracuseStep 2175531 = 3263297) B3263297
theorem B4961741 : Blo 2175435 4961741 := bbase (se 3 (by rfl) ⟨930326, by rfl⟩ : syracuseStep 4961741 = 1860653) (by norm_num)
theorem B13231309 : Blo 2175435 13231309 := bstep (se 3 (by rfl) ⟨2480870, by rfl⟩ : syracuseStep 13231309 = 4961741) B4961741
theorem B17641745 : Blo 2175435 17641745 := bstep (se 2 (by rfl) ⟨6615654, by rfl⟩ : syracuseStep 17641745 = 13231309) B13231309
theorem B11761163 : Blo 2175435 11761163 := bstep (se 1 (by rfl) ⟨8820872, by rfl⟩ : syracuseStep 11761163 = 17641745) B17641745
theorem B7840775 : Blo 2175435 7840775 := bstep (se 1 (by rfl) ⟨5880581, by rfl⟩ : syracuseStep 7840775 = 11761163) B11761163
theorem B5227183 : Blo 2175435 5227183 := bstep (se 1 (by rfl) ⟨3920387, by rfl⟩ : syracuseStep 5227183 = 7840775) B7840775
theorem B6969577 : Blo 2175435 6969577 := bstep (se 2 (by rfl) ⟨2613591, by rfl⟩ : syracuseStep 6969577 = 5227183) B5227183
theorem B9292769 : Blo 2175435 9292769 := bstep (se 2 (by rfl) ⟨3484788, by rfl⟩ : syracuseStep 9292769 = 6969577) B6969577
theorem B6195179 : Blo 2175435 6195179 := bstep (se 1 (by rfl) ⟨4646384, by rfl⟩ : syracuseStep 6195179 = 9292769) B9292769
theorem B4130119 : Blo 2175435 4130119 := bstep (se 1 (by rfl) ⟨3097589, by rfl⟩ : syracuseStep 4130119 = 6195179) B6195179
theorem B5506825 : Blo 2175435 5506825 := bstep (se 2 (by rfl) ⟨2065059, by rfl⟩ : syracuseStep 5506825 = 4130119) B4130119
theorem B7342433 : Blo 2175435 7342433 := bstep (se 2 (by rfl) ⟨2753412, by rfl⟩ : syracuseStep 7342433 = 5506825) B5506825
theorem B4894955 : Blo 2175435 4894955 := bstep (se 1 (by rfl) ⟨3671216, by rfl⟩ : syracuseStep 4894955 = 7342433) B7342433
theorem B3263303 : Blo 2175435 3263303 := bstep (se 1 (by rfl) ⟨2447477, by rfl⟩ : syracuseStep 3263303 = 4894955) B4894955
theorem B2175535 : Blo 2175435 2175535 := bstep (se 1 (by rfl) ⟨1631651, by rfl⟩ : syracuseStep 2175535 = 3263303) B3263303
theorem B3263309 : Blo 2175435 3263309 := bbase (se 3 (by rfl) ⟨611870, by rfl⟩ : syracuseStep 3263309 = 1223741) (by norm_num)
theorem B2175539 : Blo 2175435 2175539 := bstep (se 1 (by rfl) ⟨1631654, by rfl⟩ : syracuseStep 2175539 = 3263309) B3263309
theorem B4894973 : Blo 2175435 4894973 := bbase (se 3 (by rfl) ⟨917807, by rfl⟩ : syracuseStep 4894973 = 1835615) (by norm_num)
theorem B3263315 : Blo 2175435 3263315 := bstep (se 1 (by rfl) ⟨2447486, by rfl⟩ : syracuseStep 3263315 = 4894973) B4894973
theorem B2175543 : Blo 2175435 2175543 := bstep (se 1 (by rfl) ⟨1631657, by rfl⟩ : syracuseStep 2175543 = 3263315) B3263315
theorem B3671237 : Blo 2175435 3671237 := bbase (se 4 (by rfl) ⟨344178, by rfl⟩ : syracuseStep 3671237 = 688357) (by norm_num)
theorem B2447491 : Blo 2175435 2447491 := bstep (se 1 (by rfl) ⟨1835618, by rfl⟩ : syracuseStep 2447491 = 3671237) B3671237
theorem B3263321 : Blo 2175435 3263321 := bstep (se 2 (by rfl) ⟨1223745, by rfl⟩ : syracuseStep 3263321 = 2447491) B2447491
theorem B2175547 : Blo 2175435 2175547 := bstep (se 1 (by rfl) ⟨1631660, by rfl⟩ : syracuseStep 2175547 = 3263321) B3263321
theorem B16520597 : Blo 2175435 16520597 := bbase (se 6 (by rfl) ⟨387201, by rfl⟩ : syracuseStep 16520597 = 774403) (by norm_num)
theorem B11013731 : Blo 2175435 11013731 := bstep (se 1 (by rfl) ⟨8260298, by rfl⟩ : syracuseStep 11013731 = 16520597) B16520597
theorem B7342487 : Blo 2175435 7342487 := bstep (se 1 (by rfl) ⟨5506865, by rfl⟩ : syracuseStep 7342487 = 11013731) B11013731
theorem B4894991 : Blo 2175435 4894991 := bstep (se 1 (by rfl) ⟨3671243, by rfl⟩ : syracuseStep 4894991 = 7342487) B7342487
theorem B3263327 : Blo 2175435 3263327 := bstep (se 1 (by rfl) ⟨2447495, by rfl⟩ : syracuseStep 3263327 = 4894991) B4894991
theorem B2175551 : Blo 2175435 2175551 := bstep (se 1 (by rfl) ⟨1631663, by rfl⟩ : syracuseStep 2175551 = 3263327) B3263327
theorem B3263333 : Blo 2175435 3263333 := bbase (se 4 (by rfl) ⟨305937, by rfl⟩ : syracuseStep 3263333 = 611875) (by norm_num)
theorem B2175555 : Blo 2175435 2175555 := bstep (se 1 (by rfl) ⟨1631666, by rfl⟩ : syracuseStep 2175555 = 3263333) B3263333
theorem B4130165 : Blo 2175435 4130165 := bbase (se 5 (by rfl) ⟨193601, by rfl⟩ : syracuseStep 4130165 = 387203) (by norm_num)
theorem B2753443 : Blo 2175435 2753443 := bstep (se 1 (by rfl) ⟨2065082, by rfl⟩ : syracuseStep 2753443 = 4130165) B4130165
theorem B3671257 : Blo 2175435 3671257 := bstep (se 2 (by rfl) ⟨1376721, by rfl⟩ : syracuseStep 3671257 = 2753443) B2753443
theorem B4895009 : Blo 2175435 4895009 := bstep (se 2 (by rfl) ⟨1835628, by rfl⟩ : syracuseStep 4895009 = 3671257) B3671257
theorem B3263339 : Blo 2175435 3263339 := bstep (se 1 (by rfl) ⟨2447504, by rfl⟩ : syracuseStep 3263339 = 4895009) B4895009
theorem B2175559 : Blo 2175435 2175559 := bstep (se 1 (by rfl) ⟨1631669, by rfl⟩ : syracuseStep 2175559 = 3263339) B3263339
theorem B2447509 : Blo 2175435 2447509 := bbase (se 6 (by rfl) ⟨57363, by rfl⟩ : syracuseStep 2447509 = 114727) (by norm_num)
theorem B3263345 : Blo 2175435 3263345 := bstep (se 2 (by rfl) ⟨1223754, by rfl⟩ : syracuseStep 3263345 = 2447509) B2447509
theorem B2175563 : Blo 2175435 2175563 := bstep (se 1 (by rfl) ⟨1631672, by rfl⟩ : syracuseStep 2175563 = 3263345) B3263345
theorem B2753453 : Blo 2175435 2753453 := bbase (se 3 (by rfl) ⟨516272, by rfl⟩ : syracuseStep 2753453 = 1032545) (by norm_num)
theorem B7342541 : Blo 2175435 7342541 := bstep (se 3 (by rfl) ⟨1376726, by rfl⟩ : syracuseStep 7342541 = 2753453) B2753453
theorem B4895027 : Blo 2175435 4895027 := bstep (se 1 (by rfl) ⟨3671270, by rfl⟩ : syracuseStep 4895027 = 7342541) B7342541
theorem B3263351 : Blo 2175435 3263351 := bstep (se 1 (by rfl) ⟨2447513, by rfl⟩ : syracuseStep 3263351 = 4895027) B4895027
theorem B2175567 : Blo 2175435 2175567 := bstep (se 1 (by rfl) ⟨1631675, by rfl⟩ : syracuseStep 2175567 = 3263351) B3263351
theorem B3263357 : Blo 2175435 3263357 := bbase (se 3 (by rfl) ⟨611879, by rfl⟩ : syracuseStep 3263357 = 1223759) (by norm_num)
theorem B2175571 : Blo 2175435 2175571 := bstep (se 1 (by rfl) ⟨1631678, by rfl⟩ : syracuseStep 2175571 = 3263357) B3263357
theorem B4895045 : Blo 2175435 4895045 := bbase (se 4 (by rfl) ⟨458910, by rfl⟩ : syracuseStep 4895045 = 917821) (by norm_num)
theorem B3263363 : Blo 2175435 3263363 := bstep (se 1 (by rfl) ⟨2447522, by rfl⟩ : syracuseStep 3263363 = 4895045) B4895045
theorem B2175575 : Blo 2175435 2175575 := bstep (se 1 (by rfl) ⟨1631681, by rfl⟩ : syracuseStep 2175575 = 3263363) B3263363
theorem B2791037 : Blo 2175435 2791037 := bbase (se 3 (by rfl) ⟨523319, by rfl⟩ : syracuseStep 2791037 = 1046639) (by norm_num)
theorem B7442765 : Blo 2175435 7442765 := bstep (se 3 (by rfl) ⟨1395518, by rfl⟩ : syracuseStep 7442765 = 2791037) B2791037
theorem B4961843 : Blo 2175435 4961843 := bstep (se 1 (by rfl) ⟨3721382, by rfl⟩ : syracuseStep 4961843 = 7442765) B7442765
theorem B3307895 : Blo 2175435 3307895 := bstep (se 1 (by rfl) ⟨2480921, by rfl⟩ : syracuseStep 3307895 = 4961843) B4961843
theorem B2205263 : Blo 2175435 2205263 := bstep (se 1 (by rfl) ⟨1653947, by rfl⟩ : syracuseStep 2205263 = 3307895) B3307895
theorem B5880701 : Blo 2175435 5880701 := bstep (se 3 (by rfl) ⟨1102631, by rfl⟩ : syracuseStep 5880701 = 2205263) B2205263
theorem B15681869 : Blo 2175435 15681869 := bstep (se 3 (by rfl) ⟨2940350, by rfl⟩ : syracuseStep 15681869 = 5880701) B5880701
theorem B10454579 : Blo 2175435 10454579 := bstep (se 1 (by rfl) ⟨7840934, by rfl⟩ : syracuseStep 10454579 = 15681869) B15681869
theorem B6969719 : Blo 2175435 6969719 := bstep (se 1 (by rfl) ⟨5227289, by rfl⟩ : syracuseStep 6969719 = 10454579) B10454579
theorem B4646479 : Blo 2175435 4646479 := bstep (se 1 (by rfl) ⟨3484859, by rfl⟩ : syracuseStep 4646479 = 6969719) B6969719
theorem B6195305 : Blo 2175435 6195305 := bstep (se 2 (by rfl) ⟨2323239, by rfl⟩ : syracuseStep 6195305 = 4646479) B4646479
theorem B4130203 : Blo 2175435 4130203 := bstep (se 1 (by rfl) ⟨3097652, by rfl⟩ : syracuseStep 4130203 = 6195305) B6195305
theorem B5506937 : Blo 2175435 5506937 := bstep (se 2 (by rfl) ⟨2065101, by rfl⟩ : syracuseStep 5506937 = 4130203) B4130203
theorem B3671291 : Blo 2175435 3671291 := bstep (se 1 (by rfl) ⟨2753468, by rfl⟩ : syracuseStep 3671291 = 5506937) B5506937
theorem B2447527 : Blo 2175435 2447527 := bstep (se 1 (by rfl) ⟨1835645, by rfl⟩ : syracuseStep 2447527 = 3671291) B3671291
theorem B3263369 : Blo 2175435 3263369 := bstep (se 2 (by rfl) ⟨1223763, by rfl⟩ : syracuseStep 3263369 = 2447527) B2447527
theorem B2175579 : Blo 2175435 2175579 := bstep (se 1 (by rfl) ⟨1631684, by rfl⟩ : syracuseStep 2175579 = 3263369) B3263369
theorem B11013893 : Blo 2175435 11013893 := bbase (se 4 (by rfl) ⟨1032552, by rfl⟩ : syracuseStep 11013893 = 2065105) (by norm_num)
theorem B7342595 : Blo 2175435 7342595 := bstep (se 1 (by rfl) ⟨5506946, by rfl⟩ : syracuseStep 7342595 = 11013893) B11013893
theorem B4895063 : Blo 2175435 4895063 := bstep (se 1 (by rfl) ⟨3671297, by rfl⟩ : syracuseStep 4895063 = 7342595) B7342595
theorem B3263375 : Blo 2175435 3263375 := bstep (se 1 (by rfl) ⟨2447531, by rfl⟩ : syracuseStep 3263375 = 4895063) B4895063
theorem B2175583 : Blo 2175435 2175583 := bstep (se 1 (by rfl) ⟨1631687, by rfl⟩ : syracuseStep 2175583 = 3263375) B3263375
theorem B3263381 : Blo 2175435 3263381 := bbase (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) (by norm_num)
theorem B2175587 : Blo 2175435 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B12390677 : Blo 2175435 12390677 := bbase (se 6 (by rfl) ⟨290406, by rfl⟩ : syracuseStep 12390677 = 580813) (by norm_num)
theorem B8260451 : Blo 2175435 8260451 := bstep (se 1 (by rfl) ⟨6195338, by rfl⟩ : syracuseStep 8260451 = 12390677) B12390677
theorem B5506967 : Blo 2175435 5506967 := bstep (se 1 (by rfl) ⟨4130225, by rfl⟩ : syracuseStep 5506967 = 8260451) B8260451
theorem B3671311 : Blo 2175435 3671311 := bstep (se 1 (by rfl) ⟨2753483, by rfl⟩ : syracuseStep 3671311 = 5506967) B5506967
theorem B4895081 : Blo 2175435 4895081 := bstep (se 2 (by rfl) ⟨1835655, by rfl⟩ : syracuseStep 4895081 = 3671311) B3671311
theorem B3263387 : Blo 2175435 3263387 := bstep (se 1 (by rfl) ⟨2447540, by rfl⟩ : syracuseStep 3263387 = 4895081) B4895081
theorem B2175591 : Blo 2175435 2175591 := bstep (se 1 (by rfl) ⟨1631693, by rfl⟩ : syracuseStep 2175591 = 3263387) B3263387
theorem B2447545 : Blo 2175435 2447545 := bbase (se 2 (by rfl) ⟨917829, by rfl⟩ : syracuseStep 2447545 = 1835659) (by norm_num)
theorem B3263393 : Blo 2175435 3263393 := bstep (se 2 (by rfl) ⟨1223772, by rfl⟩ : syracuseStep 3263393 = 2447545) B2447545
theorem B2175595 : Blo 2175435 2175595 := bstep (se 1 (by rfl) ⟨1631696, by rfl⟩ : syracuseStep 2175595 = 3263393) B3263393
theorem B3307925 : Blo 2175435 3307925 := bbase (se 6 (by rfl) ⟨77529, by rfl⟩ : syracuseStep 3307925 = 155059) (by norm_num)
theorem B8821133 : Blo 2175435 8821133 := bstep (se 3 (by rfl) ⟨1653962, by rfl⟩ : syracuseStep 8821133 = 3307925) B3307925
theorem B5880755 : Blo 2175435 5880755 := bstep (se 1 (by rfl) ⟨4410566, by rfl⟩ : syracuseStep 5880755 = 8821133) B8821133
theorem B3920503 : Blo 2175435 3920503 := bstep (se 1 (by rfl) ⟨2940377, by rfl⟩ : syracuseStep 3920503 = 5880755) B5880755
theorem B5227337 : Blo 2175435 5227337 := bstep (se 2 (by rfl) ⟨1960251, by rfl⟩ : syracuseStep 5227337 = 3920503) B3920503
theorem B3484891 : Blo 2175435 3484891 := bstep (se 1 (by rfl) ⟨2613668, by rfl⟩ : syracuseStep 3484891 = 5227337) B5227337
theorem B4646521 : Blo 2175435 4646521 := bstep (se 2 (by rfl) ⟨1742445, by rfl⟩ : syracuseStep 4646521 = 3484891) B3484891
theorem B6195361 : Blo 2175435 6195361 := bstep (se 2 (by rfl) ⟨2323260, by rfl⟩ : syracuseStep 6195361 = 4646521) B4646521
theorem B8260481 : Blo 2175435 8260481 := bstep (se 2 (by rfl) ⟨3097680, by rfl⟩ : syracuseStep 8260481 = 6195361) B6195361
theorem B5506987 : Blo 2175435 5506987 := bstep (se 1 (by rfl) ⟨4130240, by rfl⟩ : syracuseStep 5506987 = 8260481) B8260481
theorem B7342649 : Blo 2175435 7342649 := bstep (se 2 (by rfl) ⟨2753493, by rfl⟩ : syracuseStep 7342649 = 5506987) B5506987
theorem B4895099 : Blo 2175435 4895099 := bstep (se 1 (by rfl) ⟨3671324, by rfl⟩ : syracuseStep 4895099 = 7342649) B7342649
theorem B3263399 : Blo 2175435 3263399 := bstep (se 1 (by rfl) ⟨2447549, by rfl⟩ : syracuseStep 3263399 = 4895099) B4895099
theorem B2175599 : Blo 2175435 2175599 := bstep (se 1 (by rfl) ⟨1631699, by rfl⟩ : syracuseStep 2175599 = 3263399) B3263399
theorem B3263405 : Blo 2175435 3263405 := bbase (se 3 (by rfl) ⟨611888, by rfl⟩ : syracuseStep 3263405 = 1223777) (by norm_num)
theorem B2175603 : Blo 2175435 2175603 := bstep (se 1 (by rfl) ⟨1631702, by rfl⟩ : syracuseStep 2175603 = 3263405) B3263405
theorem B4895117 : Blo 2175435 4895117 := bbase (se 3 (by rfl) ⟨917834, by rfl⟩ : syracuseStep 4895117 = 1835669) (by norm_num)
theorem B3263411 : Blo 2175435 3263411 := bstep (se 1 (by rfl) ⟨2447558, by rfl⟩ : syracuseStep 3263411 = 4895117) B4895117
theorem B2175607 : Blo 2175435 2175607 := bstep (se 1 (by rfl) ⟨1631705, by rfl⟩ : syracuseStep 2175607 = 3263411) B3263411
theorem B2753509 : Blo 2175435 2753509 := bbase (se 4 (by rfl) ⟨258141, by rfl⟩ : syracuseStep 2753509 = 516283) (by norm_num)
theorem B3671345 : Blo 2175435 3671345 := bstep (se 2 (by rfl) ⟨1376754, by rfl⟩ : syracuseStep 3671345 = 2753509) B2753509
theorem B2447563 : Blo 2175435 2447563 := bstep (se 1 (by rfl) ⟨1835672, by rfl⟩ : syracuseStep 2447563 = 3671345) B3671345
theorem B3263417 : Blo 2175435 3263417 := bstep (se 2 (by rfl) ⟨1223781, by rfl⟩ : syracuseStep 3263417 = 2447563) B2447563
theorem B2175611 : Blo 2175435 2175611 := bstep (se 1 (by rfl) ⟨1631708, by rfl⟩ : syracuseStep 2175611 = 3263417) B3263417
theorem B17642389 : Blo 2175435 17642389 := bbase (se 6 (by rfl) ⟨413493, by rfl⟩ : syracuseStep 17642389 = 826987) (by norm_num)
theorem B23523185 : Blo 2175435 23523185 := bstep (se 2 (by rfl) ⟨8821194, by rfl⟩ : syracuseStep 23523185 = 17642389) B17642389
theorem B15682123 : Blo 2175435 15682123 := bstep (se 1 (by rfl) ⟨11761592, by rfl⟩ : syracuseStep 15682123 = 23523185) B23523185
theorem B20909497 : Blo 2175435 20909497 := bstep (se 2 (by rfl) ⟨7841061, by rfl⟩ : syracuseStep 20909497 = 15682123) B15682123
theorem B27879329 : Blo 2175435 27879329 := bstep (se 2 (by rfl) ⟨10454748, by rfl⟩ : syracuseStep 27879329 = 20909497) B20909497
theorem B18586219 : Blo 2175435 18586219 := bstep (se 1 (by rfl) ⟨13939664, by rfl⟩ : syracuseStep 18586219 = 27879329) B27879329
theorem B24781625 : Blo 2175435 24781625 := bstep (se 2 (by rfl) ⟨9293109, by rfl⟩ : syracuseStep 24781625 = 18586219) B18586219
theorem B16521083 : Blo 2175435 16521083 := bstep (se 1 (by rfl) ⟨12390812, by rfl⟩ : syracuseStep 16521083 = 24781625) B24781625
theorem B11014055 : Blo 2175435 11014055 := bstep (se 1 (by rfl) ⟨8260541, by rfl⟩ : syracuseStep 11014055 = 16521083) B16521083
theorem B7342703 : Blo 2175435 7342703 := bstep (se 1 (by rfl) ⟨5507027, by rfl⟩ : syracuseStep 7342703 = 11014055) B11014055
theorem B4895135 : Blo 2175435 4895135 := bstep (se 1 (by rfl) ⟨3671351, by rfl⟩ : syracuseStep 4895135 = 7342703) B7342703
theorem B3263423 : Blo 2175435 3263423 := bstep (se 1 (by rfl) ⟨2447567, by rfl⟩ : syracuseStep 3263423 = 4895135) B4895135
theorem B2175615 : Blo 2175435 2175615 := bstep (se 1 (by rfl) ⟨1631711, by rfl⟩ : syracuseStep 2175615 = 3263423) B3263423
theorem B3263429 : Blo 2175435 3263429 := bbase (se 4 (by rfl) ⟨305946, by rfl⟩ : syracuseStep 3263429 = 611893) (by norm_num)
theorem B2175619 : Blo 2175435 2175619 := bstep (se 1 (by rfl) ⟨1631714, by rfl⟩ : syracuseStep 2175619 = 3263429) B3263429
theorem B3671365 : Blo 2175435 3671365 := bbase (se 4 (by rfl) ⟨344190, by rfl⟩ : syracuseStep 3671365 = 688381) (by norm_num)
theorem B4895153 : Blo 2175435 4895153 := bstep (se 2 (by rfl) ⟨1835682, by rfl⟩ : syracuseStep 4895153 = 3671365) B3671365
theorem B3263435 : Blo 2175435 3263435 := bstep (se 1 (by rfl) ⟨2447576, by rfl⟩ : syracuseStep 3263435 = 4895153) B4895153
theorem B2175623 : Blo 2175435 2175623 := bstep (se 1 (by rfl) ⟨1631717, by rfl⟩ : syracuseStep 2175623 = 3263435) B3263435
theorem B2447581 : Blo 2175435 2447581 := bbase (se 3 (by rfl) ⟨458921, by rfl⟩ : syracuseStep 2447581 = 917843) (by norm_num)
theorem B3263441 : Blo 2175435 3263441 := bstep (se 2 (by rfl) ⟨1223790, by rfl⟩ : syracuseStep 3263441 = 2447581) B2447581
theorem B2175627 : Blo 2175435 2175627 := bstep (se 1 (by rfl) ⟨1631720, by rfl⟩ : syracuseStep 2175627 = 3263441) B3263441
theorem B7342757 : Blo 2175435 7342757 := bbase (se 4 (by rfl) ⟨688383, by rfl⟩ : syracuseStep 7342757 = 1376767) (by norm_num)
theorem B4895171 : Blo 2175435 4895171 := bstep (se 1 (by rfl) ⟨3671378, by rfl⟩ : syracuseStep 4895171 = 7342757) B7342757
theorem B3263447 : Blo 2175435 3263447 := bstep (se 1 (by rfl) ⟨2447585, by rfl⟩ : syracuseStep 3263447 = 4895171) B4895171
theorem B2175631 : Blo 2175435 2175631 := bstep (se 1 (by rfl) ⟨1631723, by rfl⟩ : syracuseStep 2175631 = 3263447) B3263447
theorem B3263453 : Blo 2175435 3263453 := bbase (se 3 (by rfl) ⟨611897, by rfl⟩ : syracuseStep 3263453 = 1223795) (by norm_num)
theorem B2175635 : Blo 2175435 2175635 := bstep (se 1 (by rfl) ⟨1631726, by rfl⟩ : syracuseStep 2175635 = 3263453) B3263453
theorem B4895189 : Blo 2175435 4895189 := bbase (se 7 (by rfl) ⟨57365, by rfl⟩ : syracuseStep 4895189 = 114731) (by norm_num)
theorem B3263459 : Blo 2175435 3263459 := bstep (se 1 (by rfl) ⟨2447594, by rfl⟩ : syracuseStep 3263459 = 4895189) B4895189
theorem B2175639 : Blo 2175435 2175639 := bstep (se 1 (by rfl) ⟨1631729, by rfl⟩ : syracuseStep 2175639 = 3263459) B3263459
theorem B16746709 : Blo 2175435 16746709 := bbase (se 7 (by rfl) ⟨196250, by rfl⟩ : syracuseStep 16746709 = 392501) (by norm_num)
theorem B22328945 : Blo 2175435 22328945 := bstep (se 2 (by rfl) ⟨8373354, by rfl⟩ : syracuseStep 22328945 = 16746709) B16746709
theorem B14885963 : Blo 2175435 14885963 := bstep (se 1 (by rfl) ⟨11164472, by rfl⟩ : syracuseStep 14885963 = 22328945) B22328945
theorem B9923975 : Blo 2175435 9923975 := bstep (se 1 (by rfl) ⟨7442981, by rfl⟩ : syracuseStep 9923975 = 14885963) B14885963
theorem B6615983 : Blo 2175435 6615983 := bstep (se 1 (by rfl) ⟨4961987, by rfl⟩ : syracuseStep 6615983 = 9923975) B9923975
theorem B4410655 : Blo 2175435 4410655 := bstep (se 1 (by rfl) ⟨3307991, by rfl⟩ : syracuseStep 4410655 = 6615983) B6615983
theorem B23523493 : Blo 2175435 23523493 := bstep (se 4 (by rfl) ⟨2205327, by rfl⟩ : syracuseStep 23523493 = 4410655) B4410655
theorem B31364657 : Blo 2175435 31364657 := bstep (se 2 (by rfl) ⟨11761746, by rfl⟩ : syracuseStep 31364657 = 23523493) B23523493
theorem B20909771 : Blo 2175435 20909771 := bstep (se 1 (by rfl) ⟨15682328, by rfl⟩ : syracuseStep 20909771 = 31364657) B31364657
theorem B13939847 : Blo 2175435 13939847 := bstep (se 1 (by rfl) ⟨10454885, by rfl⟩ : syracuseStep 13939847 = 20909771) B20909771
theorem B9293231 : Blo 2175435 9293231 := bstep (se 1 (by rfl) ⟨6969923, by rfl⟩ : syracuseStep 9293231 = 13939847) B13939847
theorem B6195487 : Blo 2175435 6195487 := bstep (se 1 (by rfl) ⟨4646615, by rfl⟩ : syracuseStep 6195487 = 9293231) B9293231
theorem B8260649 : Blo 2175435 8260649 := bstep (se 2 (by rfl) ⟨3097743, by rfl⟩ : syracuseStep 8260649 = 6195487) B6195487
theorem B5507099 : Blo 2175435 5507099 := bstep (se 1 (by rfl) ⟨4130324, by rfl⟩ : syracuseStep 5507099 = 8260649) B8260649
theorem B3671399 : Blo 2175435 3671399 := bstep (se 1 (by rfl) ⟨2753549, by rfl⟩ : syracuseStep 3671399 = 5507099) B5507099
theorem B2447599 : Blo 2175435 2447599 := bstep (se 1 (by rfl) ⟨1835699, by rfl⟩ : syracuseStep 2447599 = 3671399) B3671399
theorem B3263465 : Blo 2175435 3263465 := bstep (se 2 (by rfl) ⟨1223799, by rfl⟩ : syracuseStep 3263465 = 2447599) B2447599
theorem B2175643 : Blo 2175435 2175643 := bstep (se 1 (by rfl) ⟨1631732, by rfl⟩ : syracuseStep 2175643 = 3263465) B3263465
theorem B3307997 : Blo 2175435 3307997 := bbase (se 3 (by rfl) ⟨620249, by rfl⟩ : syracuseStep 3307997 = 1240499) (by norm_num)
theorem B8821325 : Blo 2175435 8821325 := bstep (se 3 (by rfl) ⟨1653998, by rfl⟩ : syracuseStep 8821325 = 3307997) B3307997
theorem B23523533 : Blo 2175435 23523533 := bstep (se 3 (by rfl) ⟨4410662, by rfl⟩ : syracuseStep 23523533 = 8821325) B8821325
theorem B15682355 : Blo 2175435 15682355 := bstep (se 1 (by rfl) ⟨11761766, by rfl⟩ : syracuseStep 15682355 = 23523533) B23523533
theorem B10454903 : Blo 2175435 10454903 := bstep (se 1 (by rfl) ⟨7841177, by rfl⟩ : syracuseStep 10454903 = 15682355) B15682355
theorem B6969935 : Blo 2175435 6969935 := bstep (se 1 (by rfl) ⟨5227451, by rfl⟩ : syracuseStep 6969935 = 10454903) B10454903
theorem B18586493 : Blo 2175435 18586493 := bstep (se 3 (by rfl) ⟨3484967, by rfl⟩ : syracuseStep 18586493 = 6969935) B6969935
theorem B12390995 : Blo 2175435 12390995 := bstep (se 1 (by rfl) ⟨9293246, by rfl⟩ : syracuseStep 12390995 = 18586493) B18586493
theorem B8260663 : Blo 2175435 8260663 := bstep (se 1 (by rfl) ⟨6195497, by rfl⟩ : syracuseStep 8260663 = 12390995) B12390995
theorem B11014217 : Blo 2175435 11014217 := bstep (se 2 (by rfl) ⟨4130331, by rfl⟩ : syracuseStep 11014217 = 8260663) B8260663
theorem B7342811 : Blo 2175435 7342811 := bstep (se 1 (by rfl) ⟨5507108, by rfl⟩ : syracuseStep 7342811 = 11014217) B11014217
theorem B4895207 : Blo 2175435 4895207 := bstep (se 1 (by rfl) ⟨3671405, by rfl⟩ : syracuseStep 4895207 = 7342811) B7342811
theorem B3263471 : Blo 2175435 3263471 := bstep (se 1 (by rfl) ⟨2447603, by rfl⟩ : syracuseStep 3263471 = 4895207) B4895207
theorem B2175647 : Blo 2175435 2175647 := bstep (se 1 (by rfl) ⟨1631735, by rfl⟩ : syracuseStep 2175647 = 3263471) B3263471
theorem B3263477 : Blo 2175435 3263477 := bbase (se 5 (by rfl) ⟨152975, by rfl⟩ : syracuseStep 3263477 = 305951) (by norm_num)
theorem B2175651 : Blo 2175435 2175651 := bstep (se 1 (by rfl) ⟨1631738, by rfl⟩ : syracuseStep 2175651 = 3263477) B3263477
theorem B3484981 : Blo 2175435 3484981 := bbase (se 5 (by rfl) ⟨163358, by rfl⟩ : syracuseStep 3484981 = 326717) (by norm_num)
theorem B4646641 : Blo 2175435 4646641 := bstep (se 2 (by rfl) ⟨1742490, by rfl⟩ : syracuseStep 4646641 = 3484981) B3484981
theorem B6195521 : Blo 2175435 6195521 := bstep (se 2 (by rfl) ⟨2323320, by rfl⟩ : syracuseStep 6195521 = 4646641) B4646641
theorem B4130347 : Blo 2175435 4130347 := bstep (se 1 (by rfl) ⟨3097760, by rfl⟩ : syracuseStep 4130347 = 6195521) B6195521
theorem B5507129 : Blo 2175435 5507129 := bstep (se 2 (by rfl) ⟨2065173, by rfl⟩ : syracuseStep 5507129 = 4130347) B4130347
theorem B3671419 : Blo 2175435 3671419 := bstep (se 1 (by rfl) ⟨2753564, by rfl⟩ : syracuseStep 3671419 = 5507129) B5507129
theorem B4895225 : Blo 2175435 4895225 := bstep (se 2 (by rfl) ⟨1835709, by rfl⟩ : syracuseStep 4895225 = 3671419) B3671419
theorem B3263483 : Blo 2175435 3263483 := bstep (se 1 (by rfl) ⟨2447612, by rfl⟩ : syracuseStep 3263483 = 4895225) B4895225
theorem B2175655 : Blo 2175435 2175655 := bstep (se 1 (by rfl) ⟨1631741, by rfl⟩ : syracuseStep 2175655 = 3263483) B3263483
theorem B2447617 : Blo 2175435 2447617 := bbase (se 2 (by rfl) ⟨917856, by rfl⟩ : syracuseStep 2447617 = 1835713) (by norm_num)
theorem B3263489 : Blo 2175435 3263489 := bstep (se 2 (by rfl) ⟨1223808, by rfl⟩ : syracuseStep 3263489 = 2447617) B2447617
theorem B2175659 : Blo 2175435 2175659 := bstep (se 1 (by rfl) ⟨1631744, by rfl⟩ : syracuseStep 2175659 = 3263489) B3263489
theorem B5507149 : Blo 2175435 5507149 := bbase (se 3 (by rfl) ⟨1032590, by rfl⟩ : syracuseStep 5507149 = 2065181) (by norm_num)
theorem B7342865 : Blo 2175435 7342865 := bstep (se 2 (by rfl) ⟨2753574, by rfl⟩ : syracuseStep 7342865 = 5507149) B5507149
theorem B4895243 : Blo 2175435 4895243 := bstep (se 1 (by rfl) ⟨3671432, by rfl⟩ : syracuseStep 4895243 = 7342865) B7342865
theorem B3263495 : Blo 2175435 3263495 := bstep (se 1 (by rfl) ⟨2447621, by rfl⟩ : syracuseStep 3263495 = 4895243) B4895243
theorem B2175663 : Blo 2175435 2175663 := bstep (se 1 (by rfl) ⟨1631747, by rfl⟩ : syracuseStep 2175663 = 3263495) B3263495
theorem B3263501 : Blo 2175435 3263501 := bbase (se 3 (by rfl) ⟨611906, by rfl⟩ : syracuseStep 3263501 = 1223813) (by norm_num)
theorem B2175667 : Blo 2175435 2175667 := bstep (se 1 (by rfl) ⟨1631750, by rfl⟩ : syracuseStep 2175667 = 3263501) B3263501
theorem B4895261 : Blo 2175435 4895261 := bbase (se 3 (by rfl) ⟨917861, by rfl⟩ : syracuseStep 4895261 = 1835723) (by norm_num)
theorem B3263507 : Blo 2175435 3263507 := bstep (se 1 (by rfl) ⟨2447630, by rfl⟩ : syracuseStep 3263507 = 4895261) B4895261
theorem B2175671 : Blo 2175435 2175671 := bstep (se 1 (by rfl) ⟨1631753, by rfl⟩ : syracuseStep 2175671 = 3263507) B3263507
theorem B3671453 : Blo 2175435 3671453 := bbase (se 3 (by rfl) ⟨688397, by rfl⟩ : syracuseStep 3671453 = 1376795) (by norm_num)
theorem B2447635 : Blo 2175435 2447635 := bstep (se 1 (by rfl) ⟨1835726, by rfl⟩ : syracuseStep 2447635 = 3671453) B3671453
theorem B3263513 : Blo 2175435 3263513 := bstep (se 2 (by rfl) ⟨1223817, by rfl⟩ : syracuseStep 3263513 = 2447635) B2447635
theorem B2175675 : Blo 2175435 2175675 := bstep (se 1 (by rfl) ⟨1631756, by rfl⟩ : syracuseStep 2175675 = 3263513) B3263513
theorem B5735693 : Blo 2175435 5735693 := bbase (se 3 (by rfl) ⟨1075442, by rfl⟩ : syracuseStep 5735693 = 2150885) (by norm_num)
theorem B3823795 : Blo 2175435 3823795 := bstep (se 1 (by rfl) ⟨2867846, by rfl⟩ : syracuseStep 3823795 = 5735693) B5735693
theorem B5098393 : Blo 2175435 5098393 := bstep (se 2 (by rfl) ⟨1911897, by rfl⟩ : syracuseStep 5098393 = 3823795) B3823795
theorem B6797857 : Blo 2175435 6797857 := bstep (se 2 (by rfl) ⟨2549196, by rfl⟩ : syracuseStep 6797857 = 5098393) B5098393
theorem B9063809 : Blo 2175435 9063809 := bstep (se 2 (by rfl) ⟨3398928, by rfl⟩ : syracuseStep 9063809 = 6797857) B6797857
theorem B6042539 : Blo 2175435 6042539 := bstep (se 1 (by rfl) ⟨4531904, by rfl⟩ : syracuseStep 6042539 = 9063809) B9063809
theorem B16113437 : Blo 2175435 16113437 := bstep (se 3 (by rfl) ⟨3021269, by rfl⟩ : syracuseStep 16113437 = 6042539) B6042539
theorem B10742291 : Blo 2175435 10742291 := bstep (se 1 (by rfl) ⟨8056718, by rfl⟩ : syracuseStep 10742291 = 16113437) B16113437
theorem B7161527 : Blo 2175435 7161527 := bstep (se 1 (by rfl) ⟨5371145, by rfl⟩ : syracuseStep 7161527 = 10742291) B10742291
theorem B4774351 : Blo 2175435 4774351 := bstep (se 1 (by rfl) ⟨3580763, by rfl⟩ : syracuseStep 4774351 = 7161527) B7161527
theorem B6365801 : Blo 2175435 6365801 := bstep (se 2 (by rfl) ⟨2387175, by rfl⟩ : syracuseStep 6365801 = 4774351) B4774351
theorem B16975469 : Blo 2175435 16975469 := bstep (se 3 (by rfl) ⟨3182900, by rfl⟩ : syracuseStep 16975469 = 6365801) B6365801
theorem B11316979 : Blo 2175435 11316979 := bstep (se 1 (by rfl) ⟨8487734, by rfl⟩ : syracuseStep 11316979 = 16975469) B16975469
theorem B60357221 : Blo 2175435 60357221 := bstep (se 4 (by rfl) ⟨5658489, by rfl⟩ : syracuseStep 60357221 = 11316979) B11316979
theorem B40238147 : Blo 2175435 40238147 := bstep (se 1 (by rfl) ⟨30178610, by rfl⟩ : syracuseStep 40238147 = 60357221) B60357221
theorem B26825431 : Blo 2175435 26825431 := bstep (se 1 (by rfl) ⟨20119073, by rfl⟩ : syracuseStep 26825431 = 40238147) B40238147
theorem B35767241 : Blo 2175435 35767241 := bstep (se 2 (by rfl) ⟨13412715, by rfl⟩ : syracuseStep 35767241 = 26825431) B26825431
theorem B23844827 : Blo 2175435 23844827 := bstep (se 1 (by rfl) ⟨17883620, by rfl⟩ : syracuseStep 23844827 = 35767241) B35767241
theorem B63586205 : Blo 2175435 63586205 := bstep (se 3 (by rfl) ⟨11922413, by rfl⟩ : syracuseStep 63586205 = 23844827) B23844827
theorem B42390803 : Blo 2175435 42390803 := bstep (se 1 (by rfl) ⟨31793102, by rfl⟩ : syracuseStep 42390803 = 63586205) B63586205
theorem B28260535 : Blo 2175435 28260535 := bstep (se 1 (by rfl) ⟨21195401, by rfl⟩ : syracuseStep 28260535 = 42390803) B42390803
theorem B37680713 : Blo 2175435 37680713 := bstep (se 2 (by rfl) ⟨14130267, by rfl⟩ : syracuseStep 37680713 = 28260535) B28260535
theorem B25120475 : Blo 2175435 25120475 := bstep (se 1 (by rfl) ⟨18840356, by rfl⟩ : syracuseStep 25120475 = 37680713) B37680713
theorem B16746983 : Blo 2175435 16746983 := bstep (se 1 (by rfl) ⟨12560237, by rfl⟩ : syracuseStep 16746983 = 25120475) B25120475
theorem B11164655 : Blo 2175435 11164655 := bstep (se 1 (by rfl) ⟨8373491, by rfl⟩ : syracuseStep 11164655 = 16746983) B16746983
theorem B7443103 : Blo 2175435 7443103 := bstep (se 1 (by rfl) ⟨5582327, by rfl⟩ : syracuseStep 7443103 = 11164655) B11164655
theorem B9924137 : Blo 2175435 9924137 := bstep (se 2 (by rfl) ⟨3721551, by rfl⟩ : syracuseStep 9924137 = 7443103) B7443103
theorem B6616091 : Blo 2175435 6616091 := bstep (se 1 (by rfl) ⟨4962068, by rfl⟩ : syracuseStep 6616091 = 9924137) B9924137
theorem B17642909 : Blo 2175435 17642909 := bstep (se 3 (by rfl) ⟨3308045, by rfl⟩ : syracuseStep 17642909 = 6616091) B6616091
theorem B11761939 : Blo 2175435 11761939 := bstep (se 1 (by rfl) ⟨8821454, by rfl⟩ : syracuseStep 11761939 = 17642909) B17642909
theorem B15682585 : Blo 2175435 15682585 := bstep (se 2 (by rfl) ⟨5880969, by rfl⟩ : syracuseStep 15682585 = 11761939) B11761939
theorem B20910113 : Blo 2175435 20910113 := bstep (se 2 (by rfl) ⟨7841292, by rfl⟩ : syracuseStep 20910113 = 15682585) B15682585
theorem B13940075 : Blo 2175435 13940075 := bstep (se 1 (by rfl) ⟨10455056, by rfl⟩ : syracuseStep 13940075 = 20910113) B20910113
theorem B9293383 : Blo 2175435 9293383 := bstep (se 1 (by rfl) ⟨6970037, by rfl⟩ : syracuseStep 9293383 = 13940075) B13940075
theorem B12391177 : Blo 2175435 12391177 := bstep (se 2 (by rfl) ⟨4646691, by rfl⟩ : syracuseStep 12391177 = 9293383) B9293383
theorem B16521569 : Blo 2175435 16521569 := bstep (se 2 (by rfl) ⟨6195588, by rfl⟩ : syracuseStep 16521569 = 12391177) B12391177
theorem B11014379 : Blo 2175435 11014379 := bstep (se 1 (by rfl) ⟨8260784, by rfl⟩ : syracuseStep 11014379 = 16521569) B16521569
theorem B7342919 : Blo 2175435 7342919 := bstep (se 1 (by rfl) ⟨5507189, by rfl⟩ : syracuseStep 7342919 = 11014379) B11014379
theorem B4895279 : Blo 2175435 4895279 := bstep (se 1 (by rfl) ⟨3671459, by rfl⟩ : syracuseStep 4895279 = 7342919) B7342919
theorem B3263519 : Blo 2175435 3263519 := bstep (se 1 (by rfl) ⟨2447639, by rfl⟩ : syracuseStep 3263519 = 4895279) B4895279
theorem B2175679 : Blo 2175435 2175679 := bstep (se 1 (by rfl) ⟨1631759, by rfl⟩ : syracuseStep 2175679 = 3263519) B3263519
theorem B3263525 : Blo 2175435 3263525 := bbase (se 4 (by rfl) ⟨305955, by rfl⟩ : syracuseStep 3263525 = 611911) (by norm_num)
theorem B2175683 : Blo 2175435 2175683 := bstep (se 1 (by rfl) ⟨1631762, by rfl⟩ : syracuseStep 2175683 = 3263525) B3263525
theorem B2753605 : Blo 2175435 2753605 := bbase (se 4 (by rfl) ⟨258150, by rfl⟩ : syracuseStep 2753605 = 516301) (by norm_num)
theorem B3671473 : Blo 2175435 3671473 := bstep (se 2 (by rfl) ⟨1376802, by rfl⟩ : syracuseStep 3671473 = 2753605) B2753605
theorem B4895297 : Blo 2175435 4895297 := bstep (se 2 (by rfl) ⟨1835736, by rfl⟩ : syracuseStep 4895297 = 3671473) B3671473
theorem B3263531 : Blo 2175435 3263531 := bstep (se 1 (by rfl) ⟨2447648, by rfl⟩ : syracuseStep 3263531 = 4895297) B4895297
theorem B2175687 : Blo 2175435 2175687 := bstep (se 1 (by rfl) ⟨1631765, by rfl⟩ : syracuseStep 2175687 = 3263531) B3263531
theorem B2447653 : Blo 2175435 2447653 := bbase (se 4 (by rfl) ⟨229467, by rfl⟩ : syracuseStep 2447653 = 458935) (by norm_num)
theorem B3263537 : Blo 2175435 3263537 := bstep (se 2 (by rfl) ⟨1223826, by rfl⟩ : syracuseStep 3263537 = 2447653) B2447653
theorem B2175691 : Blo 2175435 2175691 := bstep (se 1 (by rfl) ⟨1631768, by rfl⟩ : syracuseStep 2175691 = 3263537) B3263537
theorem B3485045 : Blo 2175435 3485045 := bbase (se 5 (by rfl) ⟨163361, by rfl⟩ : syracuseStep 3485045 = 326723) (by norm_num)
theorem B9293453 : Blo 2175435 9293453 := bstep (se 3 (by rfl) ⟨1742522, by rfl⟩ : syracuseStep 9293453 = 3485045) B3485045
theorem B6195635 : Blo 2175435 6195635 := bstep (se 1 (by rfl) ⟨4646726, by rfl⟩ : syracuseStep 6195635 = 9293453) B9293453
theorem B4130423 : Blo 2175435 4130423 := bstep (se 1 (by rfl) ⟨3097817, by rfl⟩ : syracuseStep 4130423 = 6195635) B6195635
theorem B2753615 : Blo 2175435 2753615 := bstep (se 1 (by rfl) ⟨2065211, by rfl⟩ : syracuseStep 2753615 = 4130423) B4130423
theorem B7342973 : Blo 2175435 7342973 := bstep (se 3 (by rfl) ⟨1376807, by rfl⟩ : syracuseStep 7342973 = 2753615) B2753615
theorem B4895315 : Blo 2175435 4895315 := bstep (se 1 (by rfl) ⟨3671486, by rfl⟩ : syracuseStep 4895315 = 7342973) B7342973
theorem B3263543 : Blo 2175435 3263543 := bstep (se 1 (by rfl) ⟨2447657, by rfl⟩ : syracuseStep 3263543 = 4895315) B4895315
theorem B2175695 : Blo 2175435 2175695 := bstep (se 1 (by rfl) ⟨1631771, by rfl⟩ : syracuseStep 2175695 = 3263543) B3263543
theorem B3263549 : Blo 2175435 3263549 := bbase (se 3 (by rfl) ⟨611915, by rfl⟩ : syracuseStep 3263549 = 1223831) (by norm_num)
theorem B2175699 : Blo 2175435 2175699 := bstep (se 1 (by rfl) ⟨1631774, by rfl⟩ : syracuseStep 2175699 = 3263549) B3263549
theorem B4895333 : Blo 2175435 4895333 := bbase (se 4 (by rfl) ⟨458937, by rfl⟩ : syracuseStep 4895333 = 917875) (by norm_num)
theorem B3263555 : Blo 2175435 3263555 := bstep (se 1 (by rfl) ⟨2447666, by rfl⟩ : syracuseStep 3263555 = 4895333) B4895333
theorem B2175703 : Blo 2175435 2175703 := bstep (se 1 (by rfl) ⟨1631777, by rfl⟩ : syracuseStep 2175703 = 3263555) B3263555
theorem B5507261 : Blo 2175435 5507261 := bbase (se 3 (by rfl) ⟨1032611, by rfl⟩ : syracuseStep 5507261 = 2065223) (by norm_num)
theorem B3671507 : Blo 2175435 3671507 := bstep (se 1 (by rfl) ⟨2753630, by rfl⟩ : syracuseStep 3671507 = 5507261) B5507261
theorem B2447671 : Blo 2175435 2447671 := bstep (se 1 (by rfl) ⟨1835753, by rfl⟩ : syracuseStep 2447671 = 3671507) B3671507
theorem B3263561 : Blo 2175435 3263561 := bstep (se 2 (by rfl) ⟨1223835, by rfl⟩ : syracuseStep 3263561 = 2447671) B2447671
theorem B2175707 : Blo 2175435 2175707 := bstep (se 1 (by rfl) ⟨1631780, by rfl⟩ : syracuseStep 2175707 = 3263561) B3263561
theorem B4130453 : Blo 2175435 4130453 := bbase (se 6 (by rfl) ⟨96807, by rfl⟩ : syracuseStep 4130453 = 193615) (by norm_num)
theorem B11014541 : Blo 2175435 11014541 := bstep (se 3 (by rfl) ⟨2065226, by rfl⟩ : syracuseStep 11014541 = 4130453) B4130453
theorem B7343027 : Blo 2175435 7343027 := bstep (se 1 (by rfl) ⟨5507270, by rfl⟩ : syracuseStep 7343027 = 11014541) B11014541
theorem B4895351 : Blo 2175435 4895351 := bstep (se 1 (by rfl) ⟨3671513, by rfl⟩ : syracuseStep 4895351 = 7343027) B7343027
theorem B3263567 : Blo 2175435 3263567 := bstep (se 1 (by rfl) ⟨2447675, by rfl⟩ : syracuseStep 3263567 = 4895351) B4895351
theorem B2175711 : Blo 2175435 2175711 := bstep (se 1 (by rfl) ⟨1631783, by rfl⟩ : syracuseStep 2175711 = 3263567) B3263567
theorem B3263573 : Blo 2175435 3263573 := bbase (se 8 (by rfl) ⟨19122, by rfl⟩ : syracuseStep 3263573 = 38245) (by norm_num)
theorem B2175715 : Blo 2175435 2175715 := bstep (se 1 (by rfl) ⟨1631786, by rfl⟩ : syracuseStep 2175715 = 3263573) B3263573
theorem B3721621 : Blo 2175435 3721621 := bbase (se 6 (by rfl) ⟨87225, by rfl⟩ : syracuseStep 3721621 = 174451) (by norm_num)
theorem B4962161 : Blo 2175435 4962161 := bstep (se 2 (by rfl) ⟨1860810, by rfl⟩ : syracuseStep 4962161 = 3721621) B3721621
theorem B13232429 : Blo 2175435 13232429 := bstep (se 3 (by rfl) ⟨2481080, by rfl⟩ : syracuseStep 13232429 = 4962161) B4962161
theorem B8821619 : Blo 2175435 8821619 := bstep (se 1 (by rfl) ⟨6616214, by rfl⟩ : syracuseStep 8821619 = 13232429) B13232429
theorem B5881079 : Blo 2175435 5881079 := bstep (se 1 (by rfl) ⟨4410809, by rfl⟩ : syracuseStep 5881079 = 8821619) B8821619
theorem B3920719 : Blo 2175435 3920719 := bstep (se 1 (by rfl) ⟨2940539, by rfl⟩ : syracuseStep 3920719 = 5881079) B5881079
theorem B5227625 : Blo 2175435 5227625 := bstep (se 2 (by rfl) ⟨1960359, by rfl⟩ : syracuseStep 5227625 = 3920719) B3920719
theorem B13940333 : Blo 2175435 13940333 := bstep (se 3 (by rfl) ⟨2613812, by rfl⟩ : syracuseStep 13940333 = 5227625) B5227625
theorem B9293555 : Blo 2175435 9293555 := bstep (se 1 (by rfl) ⟨6970166, by rfl⟩ : syracuseStep 9293555 = 13940333) B13940333
theorem B6195703 : Blo 2175435 6195703 := bstep (se 1 (by rfl) ⟨4646777, by rfl⟩ : syracuseStep 6195703 = 9293555) B9293555
theorem B8260937 : Blo 2175435 8260937 := bstep (se 2 (by rfl) ⟨3097851, by rfl⟩ : syracuseStep 8260937 = 6195703) B6195703
theorem B5507291 : Blo 2175435 5507291 := bstep (se 1 (by rfl) ⟨4130468, by rfl⟩ : syracuseStep 5507291 = 8260937) B8260937
theorem B3671527 : Blo 2175435 3671527 := bstep (se 1 (by rfl) ⟨2753645, by rfl⟩ : syracuseStep 3671527 = 5507291) B5507291
theorem B4895369 : Blo 2175435 4895369 := bstep (se 2 (by rfl) ⟨1835763, by rfl⟩ : syracuseStep 4895369 = 3671527) B3671527
theorem B3263579 : Blo 2175435 3263579 := bstep (se 1 (by rfl) ⟨2447684, by rfl⟩ : syracuseStep 3263579 = 4895369) B4895369
theorem B2175719 : Blo 2175435 2175719 := bstep (se 1 (by rfl) ⟨1631789, by rfl⟩ : syracuseStep 2175719 = 3263579) B3263579
theorem B2447689 : Blo 2175435 2447689 := bbase (se 2 (by rfl) ⟨917883, by rfl⟩ : syracuseStep 2447689 = 1835767) (by norm_num)
theorem B3263585 : Blo 2175435 3263585 := bstep (se 2 (by rfl) ⟨1223844, by rfl⟩ : syracuseStep 3263585 = 2447689) B2447689
theorem B2175723 : Blo 2175435 2175723 := bstep (se 1 (by rfl) ⟨1631792, by rfl⟩ : syracuseStep 2175723 = 3263585) B3263585
theorem B3399005 : Blo 2175435 3399005 := bbase (se 3 (by rfl) ⟨637313, by rfl⟩ : syracuseStep 3399005 = 1274627) (by norm_num)
theorem B2266003 : Blo 2175435 2266003 := bstep (se 1 (by rfl) ⟨1699502, by rfl⟩ : syracuseStep 2266003 = 3399005) B3399005
theorem B3021337 : Blo 2175435 3021337 := bstep (se 2 (by rfl) ⟨1133001, by rfl⟩ : syracuseStep 3021337 = 2266003) B2266003
theorem B4028449 : Blo 2175435 4028449 := bstep (se 2 (by rfl) ⟨1510668, by rfl⟩ : syracuseStep 4028449 = 3021337) B3021337
theorem B5371265 : Blo 2175435 5371265 := bstep (se 2 (by rfl) ⟨2014224, by rfl⟩ : syracuseStep 5371265 = 4028449) B4028449
theorem B3580843 : Blo 2175435 3580843 := bstep (se 1 (by rfl) ⟨2685632, by rfl⟩ : syracuseStep 3580843 = 5371265) B5371265
theorem B4774457 : Blo 2175435 4774457 := bstep (se 2 (by rfl) ⟨1790421, by rfl⟩ : syracuseStep 4774457 = 3580843) B3580843
theorem B3182971 : Blo 2175435 3182971 := bstep (se 1 (by rfl) ⟨2387228, by rfl⟩ : syracuseStep 3182971 = 4774457) B4774457
theorem B4243961 : Blo 2175435 4243961 := bstep (se 2 (by rfl) ⟨1591485, by rfl⟩ : syracuseStep 4243961 = 3182971) B3182971
theorem B11317229 : Blo 2175435 11317229 := bstep (se 3 (by rfl) ⟨2121980, by rfl⟩ : syracuseStep 11317229 = 4243961) B4243961
theorem B7544819 : Blo 2175435 7544819 := bstep (se 1 (by rfl) ⟨5658614, by rfl⟩ : syracuseStep 7544819 = 11317229) B11317229
theorem B5029879 : Blo 2175435 5029879 := bstep (se 1 (by rfl) ⟨3772409, by rfl⟩ : syracuseStep 5029879 = 7544819) B7544819
theorem B6706505 : Blo 2175435 6706505 := bstep (se 2 (by rfl) ⟨2514939, by rfl⟩ : syracuseStep 6706505 = 5029879) B5029879
theorem B4471003 : Blo 2175435 4471003 := bstep (se 1 (by rfl) ⟨3353252, by rfl⟩ : syracuseStep 4471003 = 6706505) B6706505
theorem B5961337 : Blo 2175435 5961337 := bstep (se 2 (by rfl) ⟨2235501, by rfl⟩ : syracuseStep 5961337 = 4471003) B4471003
theorem B127175189 : Blo 2175435 127175189 := bstep (se 6 (by rfl) ⟨2980668, by rfl⟩ : syracuseStep 127175189 = 5961337) B5961337
theorem B339133837 : Blo 2175435 339133837 := bstep (se 3 (by rfl) ⟨63587594, by rfl⟩ : syracuseStep 339133837 = 127175189) B127175189
theorem B452178449 : Blo 2175435 452178449 := bstep (se 2 (by rfl) ⟨169566918, by rfl⟩ : syracuseStep 452178449 = 339133837) B339133837
theorem B301452299 : Blo 2175435 301452299 := bstep (se 1 (by rfl) ⟨226089224, by rfl⟩ : syracuseStep 301452299 = 452178449) B452178449
theorem B200968199 : Blo 2175435 200968199 := bstep (se 1 (by rfl) ⟨150726149, by rfl⟩ : syracuseStep 200968199 = 301452299) B301452299
theorem B133978799 : Blo 2175435 133978799 := bstep (se 1 (by rfl) ⟨100484099, by rfl⟩ : syracuseStep 133978799 = 200968199) B200968199
theorem B89319199 : Blo 2175435 89319199 := bstep (se 1 (by rfl) ⟨66989399, by rfl⟩ : syracuseStep 89319199 = 133978799) B133978799
theorem B119092265 : Blo 2175435 119092265 := bstep (se 2 (by rfl) ⟨44659599, by rfl⟩ : syracuseStep 119092265 = 89319199) B89319199
theorem B79394843 : Blo 2175435 79394843 := bstep (se 1 (by rfl) ⟨59546132, by rfl⟩ : syracuseStep 79394843 = 119092265) B119092265
theorem B52929895 : Blo 2175435 52929895 := bstep (se 1 (by rfl) ⟨39697421, by rfl⟩ : syracuseStep 52929895 = 79394843) B79394843
theorem B70573193 : Blo 2175435 70573193 := bstep (se 2 (by rfl) ⟨26464947, by rfl⟩ : syracuseStep 70573193 = 52929895) B52929895
theorem B47048795 : Blo 2175435 47048795 := bstep (se 1 (by rfl) ⟨35286596, by rfl⟩ : syracuseStep 47048795 = 70573193) B70573193
theorem B31365863 : Blo 2175435 31365863 := bstep (se 1 (by rfl) ⟨23524397, by rfl⟩ : syracuseStep 31365863 = 47048795) B47048795
theorem B20910575 : Blo 2175435 20910575 := bstep (se 1 (by rfl) ⟨15682931, by rfl⟩ : syracuseStep 20910575 = 31365863) B31365863
theorem B13940383 : Blo 2175435 13940383 := bstep (se 1 (by rfl) ⟨10455287, by rfl⟩ : syracuseStep 13940383 = 20910575) B20910575
theorem B18587177 : Blo 2175435 18587177 := bstep (se 2 (by rfl) ⟨6970191, by rfl⟩ : syracuseStep 18587177 = 13940383) B13940383
theorem B12391451 : Blo 2175435 12391451 := bstep (se 1 (by rfl) ⟨9293588, by rfl⟩ : syracuseStep 12391451 = 18587177) B18587177
theorem B8260967 : Blo 2175435 8260967 := bstep (se 1 (by rfl) ⟨6195725, by rfl⟩ : syracuseStep 8260967 = 12391451) B12391451
theorem B5507311 : Blo 2175435 5507311 := bstep (se 1 (by rfl) ⟨4130483, by rfl⟩ : syracuseStep 5507311 = 8260967) B8260967
theorem B7343081 : Blo 2175435 7343081 := bstep (se 2 (by rfl) ⟨2753655, by rfl⟩ : syracuseStep 7343081 = 5507311) B5507311
theorem B4895387 : Blo 2175435 4895387 := bstep (se 1 (by rfl) ⟨3671540, by rfl⟩ : syracuseStep 4895387 = 7343081) B7343081
theorem B3263591 : Blo 2175435 3263591 := bstep (se 1 (by rfl) ⟨2447693, by rfl⟩ : syracuseStep 3263591 = 4895387) B4895387
theorem B2175727 : Blo 2175435 2175727 := bstep (se 1 (by rfl) ⟨1631795, by rfl⟩ : syracuseStep 2175727 = 3263591) B3263591
theorem B3263597 : Blo 2175435 3263597 := bbase (se 3 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 3263597 = 1223849) (by norm_num)
theorem B2175731 : Blo 2175435 2175731 := bstep (se 1 (by rfl) ⟨1631798, by rfl⟩ : syracuseStep 2175731 = 3263597) B3263597
theorem B4895405 : Blo 2175435 4895405 := bbase (se 3 (by rfl) ⟨917888, by rfl⟩ : syracuseStep 4895405 = 1835777) (by norm_num)
theorem B3263603 : Blo 2175435 3263603 := bstep (se 1 (by rfl) ⟨2447702, by rfl⟩ : syracuseStep 3263603 = 4895405) B4895405
theorem B2175735 : Blo 2175435 2175735 := bstep (se 1 (by rfl) ⟨1631801, by rfl⟩ : syracuseStep 2175735 = 3263603) B3263603
theorem B4646821 : Blo 2175435 4646821 := bbase (se 4 (by rfl) ⟨435639, by rfl⟩ : syracuseStep 4646821 = 871279) (by norm_num)
theorem B6195761 : Blo 2175435 6195761 := bstep (se 2 (by rfl) ⟨2323410, by rfl⟩ : syracuseStep 6195761 = 4646821) B4646821
theorem B4130507 : Blo 2175435 4130507 := bstep (se 1 (by rfl) ⟨3097880, by rfl⟩ : syracuseStep 4130507 = 6195761) B6195761
theorem B2753671 : Blo 2175435 2753671 := bstep (se 1 (by rfl) ⟨2065253, by rfl⟩ : syracuseStep 2753671 = 4130507) B4130507
theorem B3671561 : Blo 2175435 3671561 := bstep (se 2 (by rfl) ⟨1376835, by rfl⟩ : syracuseStep 3671561 = 2753671) B2753671
theorem B2447707 : Blo 2175435 2447707 := bstep (se 1 (by rfl) ⟨1835780, by rfl⟩ : syracuseStep 2447707 = 3671561) B3671561
theorem B3263609 : Blo 2175435 3263609 := bstep (se 2 (by rfl) ⟨1223853, by rfl⟩ : syracuseStep 3263609 = 2447707) B2447707
theorem B2175739 : Blo 2175435 2175739 := bstep (se 1 (by rfl) ⟨1631804, by rfl⟩ : syracuseStep 2175739 = 3263609) B3263609
theorem B3721661 : Blo 2175435 3721661 := bbase (se 3 (by rfl) ⟨697811, by rfl⟩ : syracuseStep 3721661 = 1395623) (by norm_num)
theorem B2481107 : Blo 2175435 2481107 := bstep (se 1 (by rfl) ⟨1860830, by rfl⟩ : syracuseStep 2481107 = 3721661) B3721661
theorem B6616285 : Blo 2175435 6616285 := bstep (se 3 (by rfl) ⟨1240553, by rfl⟩ : syracuseStep 6616285 = 2481107) B2481107
theorem B35286853 : Blo 2175435 35286853 := bstep (se 4 (by rfl) ⟨3308142, by rfl⟩ : syracuseStep 35286853 = 6616285) B6616285
theorem B47049137 : Blo 2175435 47049137 := bstep (se 2 (by rfl) ⟨17643426, by rfl⟩ : syracuseStep 47049137 = 35286853) B35286853
theorem B31366091 : Blo 2175435 31366091 := bstep (se 1 (by rfl) ⟨23524568, by rfl⟩ : syracuseStep 31366091 = 47049137) B47049137
theorem B20910727 : Blo 2175435 20910727 := bstep (se 1 (by rfl) ⟨15683045, by rfl⟩ : syracuseStep 20910727 = 31366091) B31366091
theorem B27880969 : Blo 2175435 27880969 := bstep (se 2 (by rfl) ⟨10455363, by rfl⟩ : syracuseStep 27880969 = 20910727) B20910727
theorem B37174625 : Blo 2175435 37174625 := bstep (se 2 (by rfl) ⟨13940484, by rfl⟩ : syracuseStep 37174625 = 27880969) B27880969
theorem B24783083 : Blo 2175435 24783083 := bstep (se 1 (by rfl) ⟨18587312, by rfl⟩ : syracuseStep 24783083 = 37174625) B37174625
theorem B16522055 : Blo 2175435 16522055 := bstep (se 1 (by rfl) ⟨12391541, by rfl⟩ : syracuseStep 16522055 = 24783083) B24783083
theorem B11014703 : Blo 2175435 11014703 := bstep (se 1 (by rfl) ⟨8261027, by rfl⟩ : syracuseStep 11014703 = 16522055) B16522055
theorem B7343135 : Blo 2175435 7343135 := bstep (se 1 (by rfl) ⟨5507351, by rfl⟩ : syracuseStep 7343135 = 11014703) B11014703
theorem B4895423 : Blo 2175435 4895423 := bstep (se 1 (by rfl) ⟨3671567, by rfl⟩ : syracuseStep 4895423 = 7343135) B7343135
theorem B3263615 : Blo 2175435 3263615 := bstep (se 1 (by rfl) ⟨2447711, by rfl⟩ : syracuseStep 3263615 = 4895423) B4895423
theorem B2175743 : Blo 2175435 2175743 := bstep (se 1 (by rfl) ⟨1631807, by rfl⟩ : syracuseStep 2175743 = 3263615) B3263615
theorem B3263621 : Blo 2175435 3263621 := bbase (se 4 (by rfl) ⟨305964, by rfl⟩ : syracuseStep 3263621 = 611929) (by norm_num)
theorem B2175747 : Blo 2175435 2175747 := bstep (se 1 (by rfl) ⟨1631810, by rfl⟩ : syracuseStep 2175747 = 3263621) B3263621
theorem B3671581 : Blo 2175435 3671581 := bbase (se 3 (by rfl) ⟨688421, by rfl⟩ : syracuseStep 3671581 = 1376843) (by norm_num)
theorem B4895441 : Blo 2175435 4895441 := bstep (se 2 (by rfl) ⟨1835790, by rfl⟩ : syracuseStep 4895441 = 3671581) B3671581
theorem B3263627 : Blo 2175435 3263627 := bstep (se 1 (by rfl) ⟨2447720, by rfl⟩ : syracuseStep 3263627 = 4895441) B4895441
theorem B2175751 : Blo 2175435 2175751 := bstep (se 1 (by rfl) ⟨1631813, by rfl⟩ : syracuseStep 2175751 = 3263627) B3263627
theorem B2447725 : Blo 2175435 2447725 := bbase (se 3 (by rfl) ⟨458948, by rfl⟩ : syracuseStep 2447725 = 917897) (by norm_num)
theorem B3263633 : Blo 2175435 3263633 := bstep (se 2 (by rfl) ⟨1223862, by rfl⟩ : syracuseStep 3263633 = 2447725) B2447725
theorem B2175755 : Blo 2175435 2175755 := bstep (se 1 (by rfl) ⟨1631816, by rfl⟩ : syracuseStep 2175755 = 3263633) B3263633
theorem B7343189 : Blo 2175435 7343189 := bbase (se 8 (by rfl) ⟨43026, by rfl⟩ : syracuseStep 7343189 = 86053) (by norm_num)
theorem B4895459 : Blo 2175435 4895459 := bstep (se 1 (by rfl) ⟨3671594, by rfl⟩ : syracuseStep 4895459 = 7343189) B7343189
theorem B3263639 : Blo 2175435 3263639 := bstep (se 1 (by rfl) ⟨2447729, by rfl⟩ : syracuseStep 3263639 = 4895459) B4895459
theorem B2175759 : Blo 2175435 2175759 := bstep (se 1 (by rfl) ⟨1631819, by rfl⟩ : syracuseStep 2175759 = 3263639) B3263639
theorem B3263645 : Blo 2175435 3263645 := bbase (se 3 (by rfl) ⟨611933, by rfl⟩ : syracuseStep 3263645 = 1223867) (by norm_num)
theorem B2175763 : Blo 2175435 2175763 := bstep (se 1 (by rfl) ⟨1631822, by rfl⟩ : syracuseStep 2175763 = 3263645) B3263645
theorem B4895477 : Blo 2175435 4895477 := bbase (se 5 (by rfl) ⟨229475, by rfl⟩ : syracuseStep 4895477 = 458951) (by norm_num)
theorem B3263651 : Blo 2175435 3263651 := bstep (se 1 (by rfl) ⟨2447738, by rfl⟩ : syracuseStep 3263651 = 4895477) B4895477
theorem B2175767 : Blo 2175435 2175767 := bstep (se 1 (by rfl) ⟨1631825, by rfl⟩ : syracuseStep 2175767 = 3263651) B3263651
theorem B3920813 : Blo 2175435 3920813 := bbase (se 3 (by rfl) ⟨735152, by rfl⟩ : syracuseStep 3920813 = 1470305) (by norm_num)
theorem B2613875 : Blo 2175435 2613875 := bstep (se 1 (by rfl) ⟨1960406, by rfl⟩ : syracuseStep 2613875 = 3920813) B3920813
theorem B27881333 : Blo 2175435 27881333 := bstep (se 5 (by rfl) ⟨1306937, by rfl⟩ : syracuseStep 27881333 = 2613875) B2613875
theorem B18587555 : Blo 2175435 18587555 := bstep (se 1 (by rfl) ⟨13940666, by rfl⟩ : syracuseStep 18587555 = 27881333) B27881333
theorem B12391703 : Blo 2175435 12391703 := bstep (se 1 (by rfl) ⟨9293777, by rfl⟩ : syracuseStep 12391703 = 18587555) B18587555
theorem B8261135 : Blo 2175435 8261135 := bstep (se 1 (by rfl) ⟨6195851, by rfl⟩ : syracuseStep 8261135 = 12391703) B12391703
theorem B5507423 : Blo 2175435 5507423 := bstep (se 1 (by rfl) ⟨4130567, by rfl⟩ : syracuseStep 5507423 = 8261135) B8261135
theorem B3671615 : Blo 2175435 3671615 := bstep (se 1 (by rfl) ⟨2753711, by rfl⟩ : syracuseStep 3671615 = 5507423) B5507423
theorem B2447743 : Blo 2175435 2447743 := bstep (se 1 (by rfl) ⟨1835807, by rfl⟩ : syracuseStep 2447743 = 3671615) B3671615
theorem B3263657 : Blo 2175435 3263657 := bstep (se 2 (by rfl) ⟨1223871, by rfl⟩ : syracuseStep 3263657 = 2447743) B2447743
theorem B2175771 : Blo 2175435 2175771 := bstep (se 1 (by rfl) ⟨1631828, by rfl⟩ : syracuseStep 2175771 = 3263657) B3263657
theorem B3485173 : Blo 2175435 3485173 := bbase (se 5 (by rfl) ⟨163367, by rfl⟩ : syracuseStep 3485173 = 326735) (by norm_num)
theorem B4646897 : Blo 2175435 4646897 := bstep (se 2 (by rfl) ⟨1742586, by rfl⟩ : syracuseStep 4646897 = 3485173) B3485173
theorem B3097931 : Blo 2175435 3097931 := bstep (se 1 (by rfl) ⟨2323448, by rfl⟩ : syracuseStep 3097931 = 4646897) B4646897
theorem B8261149 : Blo 2175435 8261149 := bstep (se 3 (by rfl) ⟨1548965, by rfl⟩ : syracuseStep 8261149 = 3097931) B3097931
theorem B11014865 : Blo 2175435 11014865 := bstep (se 2 (by rfl) ⟨4130574, by rfl⟩ : syracuseStep 11014865 = 8261149) B8261149
theorem B7343243 : Blo 2175435 7343243 := bstep (se 1 (by rfl) ⟨5507432, by rfl⟩ : syracuseStep 7343243 = 11014865) B11014865
theorem B4895495 : Blo 2175435 4895495 := bstep (se 1 (by rfl) ⟨3671621, by rfl⟩ : syracuseStep 4895495 = 7343243) B7343243
theorem B3263663 : Blo 2175435 3263663 := bstep (se 1 (by rfl) ⟨2447747, by rfl⟩ : syracuseStep 3263663 = 4895495) B4895495
theorem B2175775 : Blo 2175435 2175775 := bstep (se 1 (by rfl) ⟨1631831, by rfl⟩ : syracuseStep 2175775 = 3263663) B3263663
theorem B3263669 : Blo 2175435 3263669 := bbase (se 5 (by rfl) ⟨152984, by rfl⟩ : syracuseStep 3263669 = 305969) (by norm_num)
theorem B2175779 : Blo 2175435 2175779 := bstep (se 1 (by rfl) ⟨1631834, by rfl⟩ : syracuseStep 2175779 = 3263669) B3263669
theorem B5507453 : Blo 2175435 5507453 := bbase (se 3 (by rfl) ⟨1032647, by rfl⟩ : syracuseStep 5507453 = 2065295) (by norm_num)
theorem B3671635 : Blo 2175435 3671635 := bstep (se 1 (by rfl) ⟨2753726, by rfl⟩ : syracuseStep 3671635 = 5507453) B5507453
theorem B4895513 : Blo 2175435 4895513 := bstep (se 2 (by rfl) ⟨1835817, by rfl⟩ : syracuseStep 4895513 = 3671635) B3671635
theorem B3263675 : Blo 2175435 3263675 := bstep (se 1 (by rfl) ⟨2447756, by rfl⟩ : syracuseStep 3263675 = 4895513) B4895513
theorem B2175783 : Blo 2175435 2175783 := bstep (se 1 (by rfl) ⟨1631837, by rfl⟩ : syracuseStep 2175783 = 3263675) B3263675
theorem B2447761 : Blo 2175435 2447761 := bbase (se 2 (by rfl) ⟨917910, by rfl⟩ : syracuseStep 2447761 = 1835821) (by norm_num)
theorem B3263681 : Blo 2175435 3263681 := bstep (se 2 (by rfl) ⟨1223880, by rfl⟩ : syracuseStep 3263681 = 2447761) B2447761
theorem B2175787 : Blo 2175435 2175787 := bstep (se 1 (by rfl) ⟨1631840, by rfl⟩ : syracuseStep 2175787 = 3263681) B3263681
theorem B4130605 : Blo 2175435 4130605 := bbase (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) (by norm_num)
theorem B5507473 : Blo 2175435 5507473 := bstep (se 2 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 5507473 = 4130605) B4130605
theorem B7343297 : Blo 2175435 7343297 := bstep (se 2 (by rfl) ⟨2753736, by rfl⟩ : syracuseStep 7343297 = 5507473) B5507473
theorem B4895531 : Blo 2175435 4895531 := bstep (se 1 (by rfl) ⟨3671648, by rfl⟩ : syracuseStep 4895531 = 7343297) B7343297
theorem B3263687 : Blo 2175435 3263687 := bstep (se 1 (by rfl) ⟨2447765, by rfl⟩ : syracuseStep 3263687 = 4895531) B4895531
theorem B2175791 : Blo 2175435 2175791 := bstep (se 1 (by rfl) ⟨1631843, by rfl⟩ : syracuseStep 2175791 = 3263687) B3263687
theorem B3263693 : Blo 2175435 3263693 := bbase (se 3 (by rfl) ⟨611942, by rfl⟩ : syracuseStep 3263693 = 1223885) (by norm_num)
theorem B2175795 : Blo 2175435 2175795 := bstep (se 1 (by rfl) ⟨1631846, by rfl⟩ : syracuseStep 2175795 = 3263693) B3263693
theorem B4895549 : Blo 2175435 4895549 := bbase (se 3 (by rfl) ⟨917915, by rfl⟩ : syracuseStep 4895549 = 1835831) (by norm_num)
theorem B3263699 : Blo 2175435 3263699 := bstep (se 1 (by rfl) ⟨2447774, by rfl⟩ : syracuseStep 3263699 = 4895549) B4895549
theorem B2175799 : Blo 2175435 2175799 := bstep (se 1 (by rfl) ⟨1631849, by rfl⟩ : syracuseStep 2175799 = 3263699) B3263699
theorem B3671669 : Blo 2175435 3671669 := bbase (se 5 (by rfl) ⟨172109, by rfl⟩ : syracuseStep 3671669 = 344219) (by norm_num)
theorem B2447779 : Blo 2175435 2447779 := bstep (se 1 (by rfl) ⟨1835834, by rfl⟩ : syracuseStep 2447779 = 3671669) B3671669
theorem B3263705 : Blo 2175435 3263705 := bstep (se 2 (by rfl) ⟨1223889, by rfl⟩ : syracuseStep 3263705 = 2447779) B2447779
theorem B2175803 : Blo 2175435 2175803 := bstep (se 1 (by rfl) ⟨1631852, by rfl⟩ : syracuseStep 2175803 = 3263705) B3263705
theorem B4646965 : Blo 2175435 4646965 := bbase (se 5 (by rfl) ⟨217826, by rfl⟩ : syracuseStep 4646965 = 435653) (by norm_num)
theorem B6195953 : Blo 2175435 6195953 := bstep (se 2 (by rfl) ⟨2323482, by rfl⟩ : syracuseStep 6195953 = 4646965) B4646965
theorem B16522541 : Blo 2175435 16522541 := bstep (se 3 (by rfl) ⟨3097976, by rfl⟩ : syracuseStep 16522541 = 6195953) B6195953
theorem B11015027 : Blo 2175435 11015027 := bstep (se 1 (by rfl) ⟨8261270, by rfl⟩ : syracuseStep 11015027 = 16522541) B16522541
theorem B7343351 : Blo 2175435 7343351 := bstep (se 1 (by rfl) ⟨5507513, by rfl⟩ : syracuseStep 7343351 = 11015027) B11015027
theorem B4895567 : Blo 2175435 4895567 := bstep (se 1 (by rfl) ⟨3671675, by rfl⟩ : syracuseStep 4895567 = 7343351) B7343351
theorem B3263711 : Blo 2175435 3263711 := bstep (se 1 (by rfl) ⟨2447783, by rfl⟩ : syracuseStep 3263711 = 4895567) B4895567
theorem B2175807 : Blo 2175435 2175807 := bstep (se 1 (by rfl) ⟨1631855, by rfl⟩ : syracuseStep 2175807 = 3263711) B3263711
theorem B3263717 : Blo 2175435 3263717 := bbase (se 4 (by rfl) ⟨305973, by rfl⟩ : syracuseStep 3263717 = 611947) (by norm_num)
theorem B2175811 : Blo 2175435 2175811 := bstep (se 1 (by rfl) ⟨1631858, by rfl⟩ : syracuseStep 2175811 = 3263717) B3263717
theorem B2355193 : Blo 2175435 2355193 := bbase (se 2 (by rfl) ⟨883197, by rfl⟩ : syracuseStep 2355193 = 1766395) (by norm_num)
theorem B3140257 : Blo 2175435 3140257 := bstep (se 2 (by rfl) ⟨1177596, by rfl⟩ : syracuseStep 3140257 = 2355193) B2355193
theorem B4187009 : Blo 2175435 4187009 := bstep (se 2 (by rfl) ⟨1570128, by rfl⟩ : syracuseStep 4187009 = 3140257) B3140257
theorem B11165357 : Blo 2175435 11165357 := bstep (se 3 (by rfl) ⟨2093504, by rfl⟩ : syracuseStep 11165357 = 4187009) B4187009
theorem B7443571 : Blo 2175435 7443571 := bstep (se 1 (by rfl) ⟨5582678, by rfl⟩ : syracuseStep 7443571 = 11165357) B11165357
theorem B9924761 : Blo 2175435 9924761 := bstep (se 2 (by rfl) ⟨3721785, by rfl⟩ : syracuseStep 9924761 = 7443571) B7443571
theorem B6616507 : Blo 2175435 6616507 := bstep (se 1 (by rfl) ⟨4962380, by rfl⟩ : syracuseStep 6616507 = 9924761) B9924761
theorem B8822009 : Blo 2175435 8822009 := bstep (se 2 (by rfl) ⟨3308253, by rfl⟩ : syracuseStep 8822009 = 6616507) B6616507
theorem B5881339 : Blo 2175435 5881339 := bstep (se 1 (by rfl) ⟨4411004, by rfl⟩ : syracuseStep 5881339 = 8822009) B8822009
theorem B7841785 : Blo 2175435 7841785 := bstep (se 2 (by rfl) ⟨2940669, by rfl⟩ : syracuseStep 7841785 = 5881339) B5881339
theorem B10455713 : Blo 2175435 10455713 := bstep (se 2 (by rfl) ⟨3920892, by rfl⟩ : syracuseStep 10455713 = 7841785) B7841785
theorem B6970475 : Blo 2175435 6970475 := bstep (se 1 (by rfl) ⟨5227856, by rfl⟩ : syracuseStep 6970475 = 10455713) B10455713
theorem B4646983 : Blo 2175435 4646983 := bstep (se 1 (by rfl) ⟨3485237, by rfl⟩ : syracuseStep 4646983 = 6970475) B6970475
theorem B6195977 : Blo 2175435 6195977 := bstep (se 2 (by rfl) ⟨2323491, by rfl⟩ : syracuseStep 6195977 = 4646983) B4646983
theorem B4130651 : Blo 2175435 4130651 := bstep (se 1 (by rfl) ⟨3097988, by rfl⟩ : syracuseStep 4130651 = 6195977) B6195977
theorem B2753767 : Blo 2175435 2753767 := bstep (se 1 (by rfl) ⟨2065325, by rfl⟩ : syracuseStep 2753767 = 4130651) B4130651
theorem B3671689 : Blo 2175435 3671689 := bstep (se 2 (by rfl) ⟨1376883, by rfl⟩ : syracuseStep 3671689 = 2753767) B2753767
theorem B4895585 : Blo 2175435 4895585 := bstep (se 2 (by rfl) ⟨1835844, by rfl⟩ : syracuseStep 4895585 = 3671689) B3671689
theorem B3263723 : Blo 2175435 3263723 := bstep (se 1 (by rfl) ⟨2447792, by rfl⟩ : syracuseStep 3263723 = 4895585) B4895585
theorem B2175815 : Blo 2175435 2175815 := bstep (se 1 (by rfl) ⟨1631861, by rfl⟩ : syracuseStep 2175815 = 3263723) B3263723
theorem B2447797 : Blo 2175435 2447797 := bbase (se 5 (by rfl) ⟨114740, by rfl⟩ : syracuseStep 2447797 = 229481) (by norm_num)
theorem B3263729 : Blo 2175435 3263729 := bstep (se 2 (by rfl) ⟨1223898, by rfl⟩ : syracuseStep 3263729 = 2447797) B2447797
theorem B2175819 : Blo 2175435 2175819 := bstep (se 1 (by rfl) ⟨1631864, by rfl⟩ : syracuseStep 2175819 = 3263729) B3263729
theorem B2753777 : Blo 2175435 2753777 := bbase (se 2 (by rfl) ⟨1032666, by rfl⟩ : syracuseStep 2753777 = 2065333) (by norm_num)
theorem B7343405 : Blo 2175435 7343405 := bstep (se 3 (by rfl) ⟨1376888, by rfl⟩ : syracuseStep 7343405 = 2753777) B2753777
theorem B4895603 : Blo 2175435 4895603 := bstep (se 1 (by rfl) ⟨3671702, by rfl⟩ : syracuseStep 4895603 = 7343405) B7343405
theorem B3263735 : Blo 2175435 3263735 := bstep (se 1 (by rfl) ⟨2447801, by rfl⟩ : syracuseStep 3263735 = 4895603) B4895603
theorem B2175823 : Blo 2175435 2175823 := bstep (se 1 (by rfl) ⟨1631867, by rfl⟩ : syracuseStep 2175823 = 3263735) B3263735
theorem B3263741 : Blo 2175435 3263741 := bbase (se 3 (by rfl) ⟨611951, by rfl⟩ : syracuseStep 3263741 = 1223903) (by norm_num)
theorem B2175827 : Blo 2175435 2175827 := bstep (se 1 (by rfl) ⟨1631870, by rfl⟩ : syracuseStep 2175827 = 3263741) B3263741
theorem B4895621 : Blo 2175435 4895621 := bbase (se 4 (by rfl) ⟨458964, by rfl⟩ : syracuseStep 4895621 = 917929) (by norm_num)
theorem B3263747 : Blo 2175435 3263747 := bstep (se 1 (by rfl) ⟨2447810, by rfl⟩ : syracuseStep 3263747 = 4895621) B4895621
theorem B2175831 : Blo 2175435 2175831 := bstep (se 1 (by rfl) ⟨1631873, by rfl⟩ : syracuseStep 2175831 = 3263747) B3263747
theorem B2323513 : Blo 2175435 2323513 := bbase (se 2 (by rfl) ⟨871317, by rfl⟩ : syracuseStep 2323513 = 1742635) (by norm_num)
theorem B3098017 : Blo 2175435 3098017 := bstep (se 2 (by rfl) ⟨1161756, by rfl⟩ : syracuseStep 3098017 = 2323513) B2323513
theorem B4130689 : Blo 2175435 4130689 := bstep (se 2 (by rfl) ⟨1549008, by rfl⟩ : syracuseStep 4130689 = 3098017) B3098017
theorem B5507585 : Blo 2175435 5507585 := bstep (se 2 (by rfl) ⟨2065344, by rfl⟩ : syracuseStep 5507585 = 4130689) B4130689
theorem B3671723 : Blo 2175435 3671723 := bstep (se 1 (by rfl) ⟨2753792, by rfl⟩ : syracuseStep 3671723 = 5507585) B5507585
theorem B2447815 : Blo 2175435 2447815 := bstep (se 1 (by rfl) ⟨1835861, by rfl⟩ : syracuseStep 2447815 = 3671723) B3671723
theorem B3263753 : Blo 2175435 3263753 := bstep (se 2 (by rfl) ⟨1223907, by rfl⟩ : syracuseStep 3263753 = 2447815) B2447815
theorem B2175835 : Blo 2175435 2175835 := bstep (se 1 (by rfl) ⟨1631876, by rfl⟩ : syracuseStep 2175835 = 3263753) B3263753
theorem B11015189 : Blo 2175435 11015189 := bbase (se 6 (by rfl) ⟨258168, by rfl⟩ : syracuseStep 11015189 = 516337) (by norm_num)
theorem B7343459 : Blo 2175435 7343459 := bstep (se 1 (by rfl) ⟨5507594, by rfl⟩ : syracuseStep 7343459 = 11015189) B11015189
theorem B4895639 : Blo 2175435 4895639 := bstep (se 1 (by rfl) ⟨3671729, by rfl⟩ : syracuseStep 4895639 = 7343459) B7343459
theorem B3263759 : Blo 2175435 3263759 := bstep (se 1 (by rfl) ⟨2447819, by rfl⟩ : syracuseStep 3263759 = 4895639) B4895639
theorem B2175839 : Blo 2175435 2175839 := bstep (se 1 (by rfl) ⟨1631879, by rfl⟩ : syracuseStep 2175839 = 3263759) B3263759
theorem B3263765 : Blo 2175435 3263765 := bbase (se 6 (by rfl) ⟨76494, by rfl⟩ : syracuseStep 3263765 = 152989) (by norm_num)
theorem B2175843 : Blo 2175435 2175843 := bstep (se 1 (by rfl) ⟨1631882, by rfl⟩ : syracuseStep 2175843 = 3263765) B3263765
theorem B15683797 : Blo 2175435 15683797 := bbase (se 7 (by rfl) ⟨183794, by rfl⟩ : syracuseStep 15683797 = 367589) (by norm_num)
theorem B20911729 : Blo 2175435 20911729 := bstep (se 2 (by rfl) ⟨7841898, by rfl⟩ : syracuseStep 20911729 = 15683797) B15683797
theorem B27882305 : Blo 2175435 27882305 := bstep (se 2 (by rfl) ⟨10455864, by rfl⟩ : syracuseStep 27882305 = 20911729) B20911729
theorem B18588203 : Blo 2175435 18588203 := bstep (se 1 (by rfl) ⟨13941152, by rfl⟩ : syracuseStep 18588203 = 27882305) B27882305
theorem B12392135 : Blo 2175435 12392135 := bstep (se 1 (by rfl) ⟨9294101, by rfl⟩ : syracuseStep 12392135 = 18588203) B18588203
theorem B8261423 : Blo 2175435 8261423 := bstep (se 1 (by rfl) ⟨6196067, by rfl⟩ : syracuseStep 8261423 = 12392135) B12392135
theorem B5507615 : Blo 2175435 5507615 := bstep (se 1 (by rfl) ⟨4130711, by rfl⟩ : syracuseStep 5507615 = 8261423) B8261423
theorem B3671743 : Blo 2175435 3671743 := bstep (se 1 (by rfl) ⟨2753807, by rfl⟩ : syracuseStep 3671743 = 5507615) B5507615
theorem B4895657 : Blo 2175435 4895657 := bstep (se 2 (by rfl) ⟨1835871, by rfl⟩ : syracuseStep 4895657 = 3671743) B3671743
theorem B3263771 : Blo 2175435 3263771 := bstep (se 1 (by rfl) ⟨2447828, by rfl⟩ : syracuseStep 3263771 = 4895657) B4895657
theorem B2175847 : Blo 2175435 2175847 := bstep (se 1 (by rfl) ⟨1631885, by rfl⟩ : syracuseStep 2175847 = 3263771) B3263771
theorem B2447833 : Blo 2175435 2447833 := bbase (se 2 (by rfl) ⟨917937, by rfl⟩ : syracuseStep 2447833 = 1835875) (by norm_num)
theorem B3263777 : Blo 2175435 3263777 := bstep (se 2 (by rfl) ⟨1223916, by rfl⟩ : syracuseStep 3263777 = 2447833) B2447833
theorem B2175851 : Blo 2175435 2175851 := bstep (se 1 (by rfl) ⟨1631888, by rfl⟩ : syracuseStep 2175851 = 3263777) B3263777
theorem B3098045 : Blo 2175435 3098045 := bbase (se 3 (by rfl) ⟨580883, by rfl⟩ : syracuseStep 3098045 = 1161767) (by norm_num)
theorem B8261453 : Blo 2175435 8261453 := bstep (se 3 (by rfl) ⟨1549022, by rfl⟩ : syracuseStep 8261453 = 3098045) B3098045
theorem B5507635 : Blo 2175435 5507635 := bstep (se 1 (by rfl) ⟨4130726, by rfl⟩ : syracuseStep 5507635 = 8261453) B8261453
theorem B7343513 : Blo 2175435 7343513 := bstep (se 2 (by rfl) ⟨2753817, by rfl⟩ : syracuseStep 7343513 = 5507635) B5507635
theorem B4895675 : Blo 2175435 4895675 := bstep (se 1 (by rfl) ⟨3671756, by rfl⟩ : syracuseStep 4895675 = 7343513) B7343513
theorem B3263783 : Blo 2175435 3263783 := bstep (se 1 (by rfl) ⟨2447837, by rfl⟩ : syracuseStep 3263783 = 4895675) B4895675
theorem B2175855 : Blo 2175435 2175855 := bstep (se 1 (by rfl) ⟨1631891, by rfl⟩ : syracuseStep 2175855 = 3263783) B3263783
theorem B3263789 : Blo 2175435 3263789 := bbase (se 3 (by rfl) ⟨611960, by rfl⟩ : syracuseStep 3263789 = 1223921) (by norm_num)
theorem B2175859 : Blo 2175435 2175859 := bstep (se 1 (by rfl) ⟨1631894, by rfl⟩ : syracuseStep 2175859 = 3263789) B3263789
theorem B4895693 : Blo 2175435 4895693 := bbase (se 3 (by rfl) ⟨917942, by rfl⟩ : syracuseStep 4895693 = 1835885) (by norm_num)
theorem B3263795 : Blo 2175435 3263795 := bstep (se 1 (by rfl) ⟨2447846, by rfl⟩ : syracuseStep 3263795 = 4895693) B4895693
theorem B2175863 : Blo 2175435 2175863 := bstep (se 1 (by rfl) ⟨1631897, by rfl⟩ : syracuseStep 2175863 = 3263795) B3263795
theorem B2753833 : Blo 2175435 2753833 := bbase (se 2 (by rfl) ⟨1032687, by rfl⟩ : syracuseStep 2753833 = 2065375) (by norm_num)
theorem B3671777 : Blo 2175435 3671777 := bstep (se 2 (by rfl) ⟨1376916, by rfl⟩ : syracuseStep 3671777 = 2753833) B2753833
theorem B2447851 : Blo 2175435 2447851 := bstep (se 1 (by rfl) ⟨1835888, by rfl⟩ : syracuseStep 2447851 = 3671777) B3671777
theorem B3263801 : Blo 2175435 3263801 := bstep (se 2 (by rfl) ⟨1223925, by rfl⟩ : syracuseStep 3263801 = 2447851) B2447851
theorem B2175867 : Blo 2175435 2175867 := bstep (se 1 (by rfl) ⟨1631900, by rfl⟩ : syracuseStep 2175867 = 3263801) B3263801
theorem B9925013 : Blo 2175435 9925013 := bbase (se 6 (by rfl) ⟨232617, by rfl⟩ : syracuseStep 9925013 = 465235) (by norm_num)
theorem B6616675 : Blo 2175435 6616675 := bstep (se 1 (by rfl) ⟨4962506, by rfl⟩ : syracuseStep 6616675 = 9925013) B9925013
theorem B8822233 : Blo 2175435 8822233 := bstep (se 2 (by rfl) ⟨3308337, by rfl⟩ : syracuseStep 8822233 = 6616675) B6616675
theorem B11762977 : Blo 2175435 11762977 := bstep (se 2 (by rfl) ⟨4411116, by rfl⟩ : syracuseStep 11762977 = 8822233) B8822233
theorem B15683969 : Blo 2175435 15683969 := bstep (se 2 (by rfl) ⟨5881488, by rfl⟩ : syracuseStep 15683969 = 11762977) B11762977
theorem B10455979 : Blo 2175435 10455979 := bstep (se 1 (by rfl) ⟨7841984, by rfl⟩ : syracuseStep 10455979 = 15683969) B15683969
theorem B13941305 : Blo 2175435 13941305 := bstep (se 2 (by rfl) ⟨5227989, by rfl⟩ : syracuseStep 13941305 = 10455979) B10455979
theorem B9294203 : Blo 2175435 9294203 := bstep (se 1 (by rfl) ⟨6970652, by rfl⟩ : syracuseStep 9294203 = 13941305) B13941305
theorem B24784541 : Blo 2175435 24784541 := bstep (se 3 (by rfl) ⟨4647101, by rfl⟩ : syracuseStep 24784541 = 9294203) B9294203
theorem B16523027 : Blo 2175435 16523027 := bstep (se 1 (by rfl) ⟨12392270, by rfl⟩ : syracuseStep 16523027 = 24784541) B24784541
theorem B11015351 : Blo 2175435 11015351 := bstep (se 1 (by rfl) ⟨8261513, by rfl⟩ : syracuseStep 11015351 = 16523027) B16523027
theorem B7343567 : Blo 2175435 7343567 := bstep (se 1 (by rfl) ⟨5507675, by rfl⟩ : syracuseStep 7343567 = 11015351) B11015351
theorem B4895711 : Blo 2175435 4895711 := bstep (se 1 (by rfl) ⟨3671783, by rfl⟩ : syracuseStep 4895711 = 7343567) B7343567
theorem B3263807 : Blo 2175435 3263807 := bstep (se 1 (by rfl) ⟨2447855, by rfl⟩ : syracuseStep 3263807 = 4895711) B4895711
theorem B2175871 : Blo 2175435 2175871 := bstep (se 1 (by rfl) ⟨1631903, by rfl⟩ : syracuseStep 2175871 = 3263807) B3263807
theorem B3263813 : Blo 2175435 3263813 := bbase (se 4 (by rfl) ⟨305982, by rfl⟩ : syracuseStep 3263813 = 611965) (by norm_num)
theorem B2175875 : Blo 2175435 2175875 := bstep (se 1 (by rfl) ⟨1631906, by rfl⟩ : syracuseStep 2175875 = 3263813) B3263813
theorem B3671797 : Blo 2175435 3671797 := bbase (se 5 (by rfl) ⟨172115, by rfl⟩ : syracuseStep 3671797 = 344231) (by norm_num)
theorem B4895729 : Blo 2175435 4895729 := bstep (se 2 (by rfl) ⟨1835898, by rfl⟩ : syracuseStep 4895729 = 3671797) B3671797
theorem B3263819 : Blo 2175435 3263819 := bstep (se 1 (by rfl) ⟨2447864, by rfl⟩ : syracuseStep 3263819 = 4895729) B4895729
theorem B2175879 : Blo 2175435 2175879 := bstep (se 1 (by rfl) ⟨1631909, by rfl⟩ : syracuseStep 2175879 = 3263819) B3263819
theorem B2447869 : Blo 2175435 2447869 := bbase (se 3 (by rfl) ⟨458975, by rfl⟩ : syracuseStep 2447869 = 917951) (by norm_num)
theorem B3263825 : Blo 2175435 3263825 := bstep (se 2 (by rfl) ⟨1223934, by rfl⟩ : syracuseStep 3263825 = 2447869) B2447869
theorem B2175883 : Blo 2175435 2175883 := bstep (se 1 (by rfl) ⟨1631912, by rfl⟩ : syracuseStep 2175883 = 3263825) B3263825
theorem B7343621 : Blo 2175435 7343621 := bbase (se 4 (by rfl) ⟨688464, by rfl⟩ : syracuseStep 7343621 = 1376929) (by norm_num)
theorem B4895747 : Blo 2175435 4895747 := bstep (se 1 (by rfl) ⟨3671810, by rfl⟩ : syracuseStep 4895747 = 7343621) B7343621
theorem B3263831 : Blo 2175435 3263831 := bstep (se 1 (by rfl) ⟨2447873, by rfl⟩ : syracuseStep 3263831 = 4895747) B4895747
theorem B2175887 : Blo 2175435 2175887 := bstep (se 1 (by rfl) ⟨1631915, by rfl⟩ : syracuseStep 2175887 = 3263831) B3263831
theorem B3263837 : Blo 2175435 3263837 := bbase (se 3 (by rfl) ⟨611969, by rfl⟩ : syracuseStep 3263837 = 1223939) (by norm_num)
theorem B2175891 : Blo 2175435 2175891 := bstep (se 1 (by rfl) ⟨1631918, by rfl⟩ : syracuseStep 2175891 = 3263837) B3263837
theorem B4895765 : Blo 2175435 4895765 := bbase (se 6 (by rfl) ⟨114744, by rfl⟩ : syracuseStep 4895765 = 229489) (by norm_num)
theorem B3263843 : Blo 2175435 3263843 := bstep (se 1 (by rfl) ⟨2447882, by rfl⟩ : syracuseStep 3263843 = 4895765) B4895765
theorem B2175895 : Blo 2175435 2175895 := bstep (se 1 (by rfl) ⟨1631921, by rfl⟩ : syracuseStep 2175895 = 3263843) B3263843
theorem B8261621 : Blo 2175435 8261621 := bbase (se 5 (by rfl) ⟨387263, by rfl⟩ : syracuseStep 8261621 = 774527) (by norm_num)
theorem B5507747 : Blo 2175435 5507747 := bstep (se 1 (by rfl) ⟨4130810, by rfl⟩ : syracuseStep 5507747 = 8261621) B8261621
theorem B3671831 : Blo 2175435 3671831 := bstep (se 1 (by rfl) ⟨2753873, by rfl⟩ : syracuseStep 3671831 = 5507747) B5507747
theorem B2447887 : Blo 2175435 2447887 := bstep (se 1 (by rfl) ⟨1835915, by rfl⟩ : syracuseStep 2447887 = 3671831) B3671831
theorem B3263849 : Blo 2175435 3263849 := bstep (se 2 (by rfl) ⟨1223943, by rfl⟩ : syracuseStep 3263849 = 2447887) B2447887
theorem B2175899 : Blo 2175435 2175899 := bstep (se 1 (by rfl) ⟨1631924, by rfl⟩ : syracuseStep 2175899 = 3263849) B3263849
theorem B2323585 : Blo 2175435 2323585 := bbase (se 2 (by rfl) ⟨871344, by rfl⟩ : syracuseStep 2323585 = 1742689) (by norm_num)
theorem B12392453 : Blo 2175435 12392453 := bstep (se 4 (by rfl) ⟨1161792, by rfl⟩ : syracuseStep 12392453 = 2323585) B2323585
theorem B8261635 : Blo 2175435 8261635 := bstep (se 1 (by rfl) ⟨6196226, by rfl⟩ : syracuseStep 8261635 = 12392453) B12392453
theorem B11015513 : Blo 2175435 11015513 := bstep (se 2 (by rfl) ⟨4130817, by rfl⟩ : syracuseStep 11015513 = 8261635) B8261635
theorem B7343675 : Blo 2175435 7343675 := bstep (se 1 (by rfl) ⟨5507756, by rfl⟩ : syracuseStep 7343675 = 11015513) B11015513
theorem B4895783 : Blo 2175435 4895783 := bstep (se 1 (by rfl) ⟨3671837, by rfl⟩ : syracuseStep 4895783 = 7343675) B7343675
theorem B3263855 : Blo 2175435 3263855 := bstep (se 1 (by rfl) ⟨2447891, by rfl⟩ : syracuseStep 3263855 = 4895783) B4895783
theorem B2175903 : Blo 2175435 2175903 := bstep (se 1 (by rfl) ⟨1631927, by rfl⟩ : syracuseStep 2175903 = 3263855) B3263855
theorem B3263861 : Blo 2175435 3263861 := bbase (se 5 (by rfl) ⟨152993, by rfl⟩ : syracuseStep 3263861 = 305987) (by norm_num)
theorem B2175907 : Blo 2175435 2175907 := bstep (se 1 (by rfl) ⟨1631930, by rfl⟩ : syracuseStep 2175907 = 3263861) B3263861
theorem B3098125 : Blo 2175435 3098125 := bbase (se 3 (by rfl) ⟨580898, by rfl⟩ : syracuseStep 3098125 = 1161797) (by norm_num)
theorem B4130833 : Blo 2175435 4130833 := bstep (se 2 (by rfl) ⟨1549062, by rfl⟩ : syracuseStep 4130833 = 3098125) B3098125
theorem B5507777 : Blo 2175435 5507777 := bstep (se 2 (by rfl) ⟨2065416, by rfl⟩ : syracuseStep 5507777 = 4130833) B4130833
theorem B3671851 : Blo 2175435 3671851 := bstep (se 1 (by rfl) ⟨2753888, by rfl⟩ : syracuseStep 3671851 = 5507777) B5507777
theorem B4895801 : Blo 2175435 4895801 := bstep (se 2 (by rfl) ⟨1835925, by rfl⟩ : syracuseStep 4895801 = 3671851) B3671851
theorem B3263867 : Blo 2175435 3263867 := bstep (se 1 (by rfl) ⟨2447900, by rfl⟩ : syracuseStep 3263867 = 4895801) B4895801
theorem B2175911 : Blo 2175435 2175911 := bstep (se 1 (by rfl) ⟨1631933, by rfl⟩ : syracuseStep 2175911 = 3263867) B3263867
theorem B2447905 : Blo 2175435 2447905 := bbase (se 2 (by rfl) ⟨917964, by rfl⟩ : syracuseStep 2447905 = 1835929) (by norm_num)
theorem B3263873 : Blo 2175435 3263873 := bstep (se 2 (by rfl) ⟨1223952, by rfl⟩ : syracuseStep 3263873 = 2447905) B2447905
theorem B2175915 : Blo 2175435 2175915 := bstep (se 1 (by rfl) ⟨1631936, by rfl⟩ : syracuseStep 2175915 = 3263873) B3263873
theorem B5507797 : Blo 2175435 5507797 := bbase (se 7 (by rfl) ⟨64544, by rfl⟩ : syracuseStep 5507797 = 129089) (by norm_num)
theorem B7343729 : Blo 2175435 7343729 := bstep (se 2 (by rfl) ⟨2753898, by rfl⟩ : syracuseStep 7343729 = 5507797) B5507797
theorem B4895819 : Blo 2175435 4895819 := bstep (se 1 (by rfl) ⟨3671864, by rfl⟩ : syracuseStep 4895819 = 7343729) B7343729
theorem B3263879 : Blo 2175435 3263879 := bstep (se 1 (by rfl) ⟨2447909, by rfl⟩ : syracuseStep 3263879 = 4895819) B4895819
theorem B2175919 : Blo 2175435 2175919 := bstep (se 1 (by rfl) ⟨1631939, by rfl⟩ : syracuseStep 2175919 = 3263879) B3263879
theorem B3263885 : Blo 2175435 3263885 := bbase (se 3 (by rfl) ⟨611978, by rfl⟩ : syracuseStep 3263885 = 1223957) (by norm_num)
theorem B2175923 : Blo 2175435 2175923 := bstep (se 1 (by rfl) ⟨1631942, by rfl⟩ : syracuseStep 2175923 = 3263885) B3263885
theorem B4895837 : Blo 2175435 4895837 := bbase (se 3 (by rfl) ⟨917969, by rfl⟩ : syracuseStep 4895837 = 1835939) (by norm_num)
theorem B3263891 : Blo 2175435 3263891 := bstep (se 1 (by rfl) ⟨2447918, by rfl⟩ : syracuseStep 3263891 = 4895837) B4895837
theorem B2175927 : Blo 2175435 2175927 := bstep (se 1 (by rfl) ⟨1631945, by rfl⟩ : syracuseStep 2175927 = 3263891) B3263891
theorem B3671885 : Blo 2175435 3671885 := bbase (se 3 (by rfl) ⟨688478, by rfl⟩ : syracuseStep 3671885 = 1376957) (by norm_num)
theorem B2447923 : Blo 2175435 2447923 := bstep (se 1 (by rfl) ⟨1835942, by rfl⟩ : syracuseStep 2447923 = 3671885) B3671885
theorem B3263897 : Blo 2175435 3263897 := bstep (se 2 (by rfl) ⟨1223961, by rfl⟩ : syracuseStep 3263897 = 2447923) B2447923
theorem B2175931 : Blo 2175435 2175931 := bstep (se 1 (by rfl) ⟨1631948, by rfl⟩ : syracuseStep 2175931 = 3263897) B3263897
theorem B14887957 : Blo 2175435 14887957 := bbase (se 6 (by rfl) ⟨348936, by rfl⟩ : syracuseStep 14887957 = 697873) (by norm_num)
theorem B19850609 : Blo 2175435 19850609 := bstep (se 2 (by rfl) ⟨7443978, by rfl⟩ : syracuseStep 19850609 = 14887957) B14887957
theorem B13233739 : Blo 2175435 13233739 := bstep (se 1 (by rfl) ⟨9925304, by rfl⟩ : syracuseStep 13233739 = 19850609) B19850609
theorem B17644985 : Blo 2175435 17644985 := bstep (se 2 (by rfl) ⟨6616869, by rfl⟩ : syracuseStep 17644985 = 13233739) B13233739
theorem B11763323 : Blo 2175435 11763323 := bstep (se 1 (by rfl) ⟨8822492, by rfl⟩ : syracuseStep 11763323 = 17644985) B17644985
theorem B7842215 : Blo 2175435 7842215 := bstep (se 1 (by rfl) ⟨5881661, by rfl⟩ : syracuseStep 7842215 = 11763323) B11763323
theorem B20912573 : Blo 2175435 20912573 := bstep (se 3 (by rfl) ⟨3921107, by rfl⟩ : syracuseStep 20912573 = 7842215) B7842215
theorem B13941715 : Blo 2175435 13941715 := bstep (se 1 (by rfl) ⟨10456286, by rfl⟩ : syracuseStep 13941715 = 20912573) B20912573
theorem B18588953 : Blo 2175435 18588953 := bstep (se 2 (by rfl) ⟨6970857, by rfl⟩ : syracuseStep 18588953 = 13941715) B13941715
theorem B12392635 : Blo 2175435 12392635 := bstep (se 1 (by rfl) ⟨9294476, by rfl⟩ : syracuseStep 12392635 = 18588953) B18588953
theorem B16523513 : Blo 2175435 16523513 := bstep (se 2 (by rfl) ⟨6196317, by rfl⟩ : syracuseStep 16523513 = 12392635) B12392635
theorem B11015675 : Blo 2175435 11015675 := bstep (se 1 (by rfl) ⟨8261756, by rfl⟩ : syracuseStep 11015675 = 16523513) B16523513
theorem B7343783 : Blo 2175435 7343783 := bstep (se 1 (by rfl) ⟨5507837, by rfl⟩ : syracuseStep 7343783 = 11015675) B11015675
theorem B4895855 : Blo 2175435 4895855 := bstep (se 1 (by rfl) ⟨3671891, by rfl⟩ : syracuseStep 4895855 = 7343783) B7343783
theorem B3263903 : Blo 2175435 3263903 := bstep (se 1 (by rfl) ⟨2447927, by rfl⟩ : syracuseStep 3263903 = 4895855) B4895855
theorem B2175935 : Blo 2175435 2175935 := bstep (se 1 (by rfl) ⟨1631951, by rfl⟩ : syracuseStep 2175935 = 3263903) B3263903
theorem B3263909 : Blo 2175435 3263909 := bbase (se 4 (by rfl) ⟨305991, by rfl⟩ : syracuseStep 3263909 = 611983) (by norm_num)
theorem B2175939 : Blo 2175435 2175939 := bstep (se 1 (by rfl) ⟨1631954, by rfl⟩ : syracuseStep 2175939 = 3263909) B3263909
theorem B2753929 : Blo 2175435 2753929 := bbase (se 2 (by rfl) ⟨1032723, by rfl⟩ : syracuseStep 2753929 = 2065447) (by norm_num)
theorem B3671905 : Blo 2175435 3671905 := bstep (se 2 (by rfl) ⟨1376964, by rfl⟩ : syracuseStep 3671905 = 2753929) B2753929
theorem B4895873 : Blo 2175435 4895873 := bstep (se 2 (by rfl) ⟨1835952, by rfl⟩ : syracuseStep 4895873 = 3671905) B3671905
theorem B3263915 : Blo 2175435 3263915 := bstep (se 1 (by rfl) ⟨2447936, by rfl⟩ : syracuseStep 3263915 = 4895873) B4895873
theorem B2175943 : Blo 2175435 2175943 := bstep (se 1 (by rfl) ⟨1631957, by rfl⟩ : syracuseStep 2175943 = 3263915) B3263915
theorem B2447941 : Blo 2175435 2447941 := bbase (se 4 (by rfl) ⟨229494, by rfl⟩ : syracuseStep 2447941 = 458989) (by norm_num)
theorem B3263921 : Blo 2175435 3263921 := bstep (se 2 (by rfl) ⟨1223970, by rfl⟩ : syracuseStep 3263921 = 2447941) B2447941
theorem B2175947 : Blo 2175435 2175947 := bstep (se 1 (by rfl) ⟨1631960, by rfl⟩ : syracuseStep 2175947 = 3263921) B3263921
theorem B4130909 : Blo 2175435 4130909 := bbase (se 3 (by rfl) ⟨774545, by rfl⟩ : syracuseStep 4130909 = 1549091) (by norm_num)
theorem B2753939 : Blo 2175435 2753939 := bstep (se 1 (by rfl) ⟨2065454, by rfl⟩ : syracuseStep 2753939 = 4130909) B4130909
theorem B7343837 : Blo 2175435 7343837 := bstep (se 3 (by rfl) ⟨1376969, by rfl⟩ : syracuseStep 7343837 = 2753939) B2753939
theorem B4895891 : Blo 2175435 4895891 := bstep (se 1 (by rfl) ⟨3671918, by rfl⟩ : syracuseStep 4895891 = 7343837) B7343837
theorem B3263927 : Blo 2175435 3263927 := bstep (se 1 (by rfl) ⟨2447945, by rfl⟩ : syracuseStep 3263927 = 4895891) B4895891
theorem B2175951 : Blo 2175435 2175951 := bstep (se 1 (by rfl) ⟨1631963, by rfl⟩ : syracuseStep 2175951 = 3263927) B3263927
theorem B3263933 : Blo 2175435 3263933 := bbase (se 3 (by rfl) ⟨611987, by rfl⟩ : syracuseStep 3263933 = 1223975) (by norm_num)
theorem B2175955 : Blo 2175435 2175955 := bstep (se 1 (by rfl) ⟨1631966, by rfl⟩ : syracuseStep 2175955 = 3263933) B3263933
theorem B4895909 : Blo 2175435 4895909 := bbase (se 4 (by rfl) ⟨458991, by rfl⟩ : syracuseStep 4895909 = 917983) (by norm_num)
theorem B3263939 : Blo 2175435 3263939 := bstep (se 1 (by rfl) ⟨2447954, by rfl⟩ : syracuseStep 3263939 = 4895909) B4895909
theorem B2175959 : Blo 2175435 2175959 := bstep (se 1 (by rfl) ⟨1631969, by rfl⟩ : syracuseStep 2175959 = 3263939) B3263939
theorem B5507909 : Blo 2175435 5507909 := bbase (se 4 (by rfl) ⟨516366, by rfl⟩ : syracuseStep 5507909 = 1032733) (by norm_num)
theorem B3671939 : Blo 2175435 3671939 := bstep (se 1 (by rfl) ⟨2753954, by rfl⟩ : syracuseStep 3671939 = 5507909) B5507909
theorem B2447959 : Blo 2175435 2447959 := bstep (se 1 (by rfl) ⟨1835969, by rfl⟩ : syracuseStep 2447959 = 3671939) B3671939
theorem B3263945 : Blo 2175435 3263945 := bstep (se 2 (by rfl) ⟨1223979, by rfl⟩ : syracuseStep 3263945 = 2447959) B2447959
theorem B2175963 : Blo 2175435 2175963 := bstep (se 1 (by rfl) ⟨1631972, by rfl⟩ : syracuseStep 2175963 = 3263945) B3263945
theorem B5228221 : Blo 2175435 5228221 := bbase (se 3 (by rfl) ⟨980291, by rfl⟩ : syracuseStep 5228221 = 1960583) (by norm_num)
theorem B6970961 : Blo 2175435 6970961 := bstep (se 2 (by rfl) ⟨2614110, by rfl⟩ : syracuseStep 6970961 = 5228221) B5228221
theorem B4647307 : Blo 2175435 4647307 := bstep (se 1 (by rfl) ⟨3485480, by rfl⟩ : syracuseStep 4647307 = 6970961) B6970961
theorem B6196409 : Blo 2175435 6196409 := bstep (se 2 (by rfl) ⟨2323653, by rfl⟩ : syracuseStep 6196409 = 4647307) B4647307
theorem B4130939 : Blo 2175435 4130939 := bstep (se 1 (by rfl) ⟨3098204, by rfl⟩ : syracuseStep 4130939 = 6196409) B6196409
theorem B11015837 : Blo 2175435 11015837 := bstep (se 3 (by rfl) ⟨2065469, by rfl⟩ : syracuseStep 11015837 = 4130939) B4130939
theorem B7343891 : Blo 2175435 7343891 := bstep (se 1 (by rfl) ⟨5507918, by rfl⟩ : syracuseStep 7343891 = 11015837) B11015837
theorem B4895927 : Blo 2175435 4895927 := bstep (se 1 (by rfl) ⟨3671945, by rfl⟩ : syracuseStep 4895927 = 7343891) B7343891
theorem B3263951 : Blo 2175435 3263951 := bstep (se 1 (by rfl) ⟨2447963, by rfl⟩ : syracuseStep 3263951 = 4895927) B4895927
theorem B2175967 : Blo 2175435 2175967 := bstep (se 1 (by rfl) ⟨1631975, by rfl⟩ : syracuseStep 2175967 = 3263951) B3263951
theorem B3263957 : Blo 2175435 3263957 := bbase (se 7 (by rfl) ⟨38249, by rfl⟩ : syracuseStep 3263957 = 76499) (by norm_num)
theorem B2175971 : Blo 2175435 2175971 := bstep (se 1 (by rfl) ⟨1631978, by rfl⟩ : syracuseStep 2175971 = 3263957) B3263957
theorem B8261909 : Blo 2175435 8261909 := bbase (se 6 (by rfl) ⟨193638, by rfl⟩ : syracuseStep 8261909 = 387277) (by norm_num)
theorem B5507939 : Blo 2175435 5507939 := bstep (se 1 (by rfl) ⟨4130954, by rfl⟩ : syracuseStep 5507939 = 8261909) B8261909
theorem B3671959 : Blo 2175435 3671959 := bstep (se 1 (by rfl) ⟨2753969, by rfl⟩ : syracuseStep 3671959 = 5507939) B5507939
theorem B4895945 : Blo 2175435 4895945 := bstep (se 2 (by rfl) ⟨1835979, by rfl⟩ : syracuseStep 4895945 = 3671959) B3671959
theorem B3263963 : Blo 2175435 3263963 := bstep (se 1 (by rfl) ⟨2447972, by rfl⟩ : syracuseStep 3263963 = 4895945) B4895945
theorem B2175975 : Blo 2175435 2175975 := bstep (se 1 (by rfl) ⟨1631981, by rfl⟩ : syracuseStep 2175975 = 3263963) B3263963
theorem B2447977 : Blo 2175435 2447977 := bbase (se 2 (by rfl) ⟨917991, by rfl⟩ : syracuseStep 2447977 = 1835983) (by norm_num)
theorem B3263969 : Blo 2175435 3263969 := bstep (se 2 (by rfl) ⟨1223988, by rfl⟩ : syracuseStep 3263969 = 2447977) B2447977
theorem B2175979 : Blo 2175435 2175979 := bstep (se 1 (by rfl) ⟨1631984, by rfl⟩ : syracuseStep 2175979 = 3263969) B3263969
theorem B4647341 : Blo 2175435 4647341 := bbase (se 3 (by rfl) ⟨871376, by rfl⟩ : syracuseStep 4647341 = 1742753) (by norm_num)
theorem B12392909 : Blo 2175435 12392909 := bstep (se 3 (by rfl) ⟨2323670, by rfl⟩ : syracuseStep 12392909 = 4647341) B4647341
theorem B8261939 : Blo 2175435 8261939 := bstep (se 1 (by rfl) ⟨6196454, by rfl⟩ : syracuseStep 8261939 = 12392909) B12392909
theorem B5507959 : Blo 2175435 5507959 := bstep (se 1 (by rfl) ⟨4130969, by rfl⟩ : syracuseStep 5507959 = 8261939) B8261939
theorem B7343945 : Blo 2175435 7343945 := bstep (se 2 (by rfl) ⟨2753979, by rfl⟩ : syracuseStep 7343945 = 5507959) B5507959
theorem B4895963 : Blo 2175435 4895963 := bstep (se 1 (by rfl) ⟨3671972, by rfl⟩ : syracuseStep 4895963 = 7343945) B7343945
theorem B3263975 : Blo 2175435 3263975 := bstep (se 1 (by rfl) ⟨2447981, by rfl⟩ : syracuseStep 3263975 = 4895963) B4895963
theorem B2175983 : Blo 2175435 2175983 := bstep (se 1 (by rfl) ⟨1631987, by rfl⟩ : syracuseStep 2175983 = 3263975) B3263975
theorem B3263981 : Blo 2175435 3263981 := bbase (se 3 (by rfl) ⟨611996, by rfl⟩ : syracuseStep 3263981 = 1223993) (by norm_num)
theorem B2175987 : Blo 2175435 2175987 := bstep (se 1 (by rfl) ⟨1631990, by rfl⟩ : syracuseStep 2175987 = 3263981) B3263981
theorem B4895981 : Blo 2175435 4895981 := bbase (se 3 (by rfl) ⟨917996, by rfl⟩ : syracuseStep 4895981 = 1835993) (by norm_num)
theorem B3263987 : Blo 2175435 3263987 := bstep (se 1 (by rfl) ⟨2447990, by rfl⟩ : syracuseStep 3263987 = 4895981) B4895981
theorem B2175991 : Blo 2175435 2175991 := bstep (se 1 (by rfl) ⟨1631993, by rfl⟩ : syracuseStep 2175991 = 3263987) B3263987
theorem B3098245 : Blo 2175435 3098245 := bbase (se 4 (by rfl) ⟨290460, by rfl⟩ : syracuseStep 3098245 = 580921) (by norm_num)
theorem B4130993 : Blo 2175435 4130993 := bstep (se 2 (by rfl) ⟨1549122, by rfl⟩ : syracuseStep 4130993 = 3098245) B3098245
theorem B2753995 : Blo 2175435 2753995 := bstep (se 1 (by rfl) ⟨2065496, by rfl⟩ : syracuseStep 2753995 = 4130993) B4130993
theorem B3671993 : Blo 2175435 3671993 := bstep (se 2 (by rfl) ⟨1376997, by rfl⟩ : syracuseStep 3671993 = 2753995) B2753995
theorem B2447995 : Blo 2175435 2447995 := bstep (se 1 (by rfl) ⟨1835996, by rfl⟩ : syracuseStep 2447995 = 3671993) B3671993
theorem B3263993 : Blo 2175435 3263993 := bstep (se 2 (by rfl) ⟨1223997, by rfl⟩ : syracuseStep 3263993 = 2447995) B2447995
theorem B2175995 : Blo 2175435 2175995 := bstep (se 1 (by rfl) ⟨1631996, by rfl⟩ : syracuseStep 2175995 = 3263993) B3263993
theorem B2940917 : Blo 2175435 2940917 := bbase (se 5 (by rfl) ⟨137855, by rfl⟩ : syracuseStep 2940917 = 275711) (by norm_num)
theorem B31369781 : Blo 2175435 31369781 := bstep (se 5 (by rfl) ⟨1470458, by rfl⟩ : syracuseStep 31369781 = 2940917) B2940917
theorem B83652749 : Blo 2175435 83652749 := bstep (se 3 (by rfl) ⟨15684890, by rfl⟩ : syracuseStep 83652749 = 31369781) B31369781
theorem B55768499 : Blo 2175435 55768499 := bstep (se 1 (by rfl) ⟨41826374, by rfl⟩ : syracuseStep 55768499 = 83652749) B83652749
theorem B37178999 : Blo 2175435 37178999 := bstep (se 1 (by rfl) ⟨27884249, by rfl⟩ : syracuseStep 37178999 = 55768499) B55768499
theorem B24785999 : Blo 2175435 24785999 := bstep (se 1 (by rfl) ⟨18589499, by rfl⟩ : syracuseStep 24785999 = 37178999) B37178999
theorem B16523999 : Blo 2175435 16523999 := bstep (se 1 (by rfl) ⟨12392999, by rfl⟩ : syracuseStep 16523999 = 24785999) B24785999
theorem B11015999 : Blo 2175435 11015999 := bstep (se 1 (by rfl) ⟨8261999, by rfl⟩ : syracuseStep 11015999 = 16523999) B16523999
theorem B7343999 : Blo 2175435 7343999 := bstep (se 1 (by rfl) ⟨5507999, by rfl⟩ : syracuseStep 7343999 = 11015999) B11015999
theorem B4895999 : Blo 2175435 4895999 := bstep (se 1 (by rfl) ⟨3671999, by rfl⟩ : syracuseStep 4895999 = 7343999) B7343999
theorem B3263999 : Blo 2175435 3263999 := bstep (se 1 (by rfl) ⟨2447999, by rfl⟩ : syracuseStep 3263999 = 4895999) B4895999
theorem B2175999 : Blo 2175435 2175999 := bstep (se 1 (by rfl) ⟨1631999, by rfl⟩ : syracuseStep 2175999 = 3263999) B3263999
theorem B3264005 : Blo 2175435 3264005 := bbase (se 4 (by rfl) ⟨306000, by rfl⟩ : syracuseStep 3264005 = 612001) (by norm_num)
theorem B2176003 : Blo 2175435 2176003 := bstep (se 1 (by rfl) ⟨1632002, by rfl⟩ : syracuseStep 2176003 = 3264005) B3264005
theorem B3672013 : Blo 2175435 3672013 := bbase (se 3 (by rfl) ⟨688502, by rfl⟩ : syracuseStep 3672013 = 1377005) (by norm_num)
theorem B4896017 : Blo 2175435 4896017 := bstep (se 2 (by rfl) ⟨1836006, by rfl⟩ : syracuseStep 4896017 = 3672013) B3672013
theorem B3264011 : Blo 2175435 3264011 := bstep (se 1 (by rfl) ⟨2448008, by rfl⟩ : syracuseStep 3264011 = 4896017) B4896017
theorem B2176007 : Blo 2175435 2176007 := bstep (se 1 (by rfl) ⟨1632005, by rfl⟩ : syracuseStep 2176007 = 3264011) B3264011
theorem B2448013 : Blo 2175435 2448013 := bbase (se 3 (by rfl) ⟨459002, by rfl⟩ : syracuseStep 2448013 = 918005) (by norm_num)
theorem B3264017 : Blo 2175435 3264017 := bstep (se 2 (by rfl) ⟨1224006, by rfl⟩ : syracuseStep 3264017 = 2448013) B2448013
theorem B2176011 : Blo 2175435 2176011 := bstep (se 1 (by rfl) ⟨1632008, by rfl⟩ : syracuseStep 2176011 = 3264017) B3264017
theorem B7344053 : Blo 2175435 7344053 := bbase (se 5 (by rfl) ⟨344252, by rfl⟩ : syracuseStep 7344053 = 688505) (by norm_num)
theorem B4896035 : Blo 2175435 4896035 := bstep (se 1 (by rfl) ⟨3672026, by rfl⟩ : syracuseStep 4896035 = 7344053) B7344053
theorem B3264023 : Blo 2175435 3264023 := bstep (se 1 (by rfl) ⟨2448017, by rfl⟩ : syracuseStep 3264023 = 4896035) B4896035
theorem B2176015 : Blo 2175435 2176015 := bstep (se 1 (by rfl) ⟨1632011, by rfl⟩ : syracuseStep 2176015 = 3264023) B3264023
theorem B3264029 : Blo 2175435 3264029 := bbase (se 3 (by rfl) ⟨612005, by rfl⟩ : syracuseStep 3264029 = 1224011) (by norm_num)
theorem B2176019 : Blo 2175435 2176019 := bstep (se 1 (by rfl) ⟨1632014, by rfl⟩ : syracuseStep 2176019 = 3264029) B3264029
theorem B4896053 : Blo 2175435 4896053 := bbase (se 5 (by rfl) ⟨229502, by rfl⟩ : syracuseStep 4896053 = 459005) (by norm_num)
theorem B3264035 : Blo 2175435 3264035 := bstep (se 1 (by rfl) ⟨2448026, by rfl⟩ : syracuseStep 3264035 = 4896053) B4896053
theorem B2176023 : Blo 2175435 2176023 := bstep (se 1 (by rfl) ⟨1632017, by rfl⟩ : syracuseStep 2176023 = 3264035) B3264035
theorem B20913461 : Blo 2175435 20913461 := bbase (se 5 (by rfl) ⟨980318, by rfl⟩ : syracuseStep 20913461 = 1960637) (by norm_num)
theorem B13942307 : Blo 2175435 13942307 := bstep (se 1 (by rfl) ⟨10456730, by rfl⟩ : syracuseStep 13942307 = 20913461) B20913461
theorem B9294871 : Blo 2175435 9294871 := bstep (se 1 (by rfl) ⟨6971153, by rfl⟩ : syracuseStep 9294871 = 13942307) B13942307
theorem B12393161 : Blo 2175435 12393161 := bstep (se 2 (by rfl) ⟨4647435, by rfl⟩ : syracuseStep 12393161 = 9294871) B9294871
theorem B8262107 : Blo 2175435 8262107 := bstep (se 1 (by rfl) ⟨6196580, by rfl⟩ : syracuseStep 8262107 = 12393161) B12393161
theorem B5508071 : Blo 2175435 5508071 := bstep (se 1 (by rfl) ⟨4131053, by rfl⟩ : syracuseStep 5508071 = 8262107) B8262107
theorem B3672047 : Blo 2175435 3672047 := bstep (se 1 (by rfl) ⟨2754035, by rfl⟩ : syracuseStep 3672047 = 5508071) B5508071
theorem B2448031 : Blo 2175435 2448031 := bstep (se 1 (by rfl) ⟨1836023, by rfl⟩ : syracuseStep 2448031 = 3672047) B3672047
theorem B3264041 : Blo 2175435 3264041 := bstep (se 2 (by rfl) ⟨1224015, by rfl⟩ : syracuseStep 3264041 = 2448031) B2448031
theorem B2176027 : Blo 2175435 2176027 := bstep (se 1 (by rfl) ⟨1632020, by rfl⟩ : syracuseStep 2176027 = 3264041) B3264041
theorem B3308581 : Blo 2175435 3308581 := bbase (se 4 (by rfl) ⟨310179, by rfl⟩ : syracuseStep 3308581 = 620359) (by norm_num)
theorem B4411441 : Blo 2175435 4411441 := bstep (se 2 (by rfl) ⟨1654290, by rfl⟩ : syracuseStep 4411441 = 3308581) B3308581
theorem B23527685 : Blo 2175435 23527685 := bstep (se 4 (by rfl) ⟨2205720, by rfl⟩ : syracuseStep 23527685 = 4411441) B4411441
theorem B15685123 : Blo 2175435 15685123 := bstep (se 1 (by rfl) ⟨11763842, by rfl⟩ : syracuseStep 15685123 = 23527685) B23527685
theorem B20913497 : Blo 2175435 20913497 := bstep (se 2 (by rfl) ⟨7842561, by rfl⟩ : syracuseStep 20913497 = 15685123) B15685123
theorem B13942331 : Blo 2175435 13942331 := bstep (se 1 (by rfl) ⟨10456748, by rfl⟩ : syracuseStep 13942331 = 20913497) B20913497
theorem B9294887 : Blo 2175435 9294887 := bstep (se 1 (by rfl) ⟨6971165, by rfl⟩ : syracuseStep 9294887 = 13942331) B13942331
theorem B6196591 : Blo 2175435 6196591 := bstep (se 1 (by rfl) ⟨4647443, by rfl⟩ : syracuseStep 6196591 = 9294887) B9294887
theorem B8262121 : Blo 2175435 8262121 := bstep (se 2 (by rfl) ⟨3098295, by rfl⟩ : syracuseStep 8262121 = 6196591) B6196591
theorem B11016161 : Blo 2175435 11016161 := bstep (se 2 (by rfl) ⟨4131060, by rfl⟩ : syracuseStep 11016161 = 8262121) B8262121
theorem B7344107 : Blo 2175435 7344107 := bstep (se 1 (by rfl) ⟨5508080, by rfl⟩ : syracuseStep 7344107 = 11016161) B11016161
theorem B4896071 : Blo 2175435 4896071 := bstep (se 1 (by rfl) ⟨3672053, by rfl⟩ : syracuseStep 4896071 = 7344107) B7344107
theorem B3264047 : Blo 2175435 3264047 := bstep (se 1 (by rfl) ⟨2448035, by rfl⟩ : syracuseStep 3264047 = 4896071) B4896071
theorem B2176031 : Blo 2175435 2176031 := bstep (se 1 (by rfl) ⟨1632023, by rfl⟩ : syracuseStep 2176031 = 3264047) B3264047
theorem B3264053 : Blo 2175435 3264053 := bbase (se 5 (by rfl) ⟨153002, by rfl⟩ : syracuseStep 3264053 = 306005) (by norm_num)
theorem B2176035 : Blo 2175435 2176035 := bstep (se 1 (by rfl) ⟨1632026, by rfl⟩ : syracuseStep 2176035 = 3264053) B3264053
theorem B5508101 : Blo 2175435 5508101 := bbase (se 4 (by rfl) ⟨516384, by rfl⟩ : syracuseStep 5508101 = 1032769) (by norm_num)
theorem B3672067 : Blo 2175435 3672067 := bstep (se 1 (by rfl) ⟨2754050, by rfl⟩ : syracuseStep 3672067 = 5508101) B5508101
theorem B4896089 : Blo 2175435 4896089 := bstep (se 2 (by rfl) ⟨1836033, by rfl⟩ : syracuseStep 4896089 = 3672067) B3672067
theorem B3264059 : Blo 2175435 3264059 := bstep (se 1 (by rfl) ⟨2448044, by rfl⟩ : syracuseStep 3264059 = 4896089) B4896089
theorem B2176039 : Blo 2175435 2176039 := bstep (se 1 (by rfl) ⟨1632029, by rfl⟩ : syracuseStep 2176039 = 3264059) B3264059
theorem B2448049 : Blo 2175435 2448049 := bbase (se 2 (by rfl) ⟨918018, by rfl⟩ : syracuseStep 2448049 = 1836037) (by norm_num)
theorem B3264065 : Blo 2175435 3264065 := bstep (se 2 (by rfl) ⟨1224024, by rfl⟩ : syracuseStep 3264065 = 2448049) B2448049
theorem B2176043 : Blo 2175435 2176043 := bstep (se 1 (by rfl) ⟨1632032, by rfl⟩ : syracuseStep 2176043 = 3264065) B3264065
theorem B4906349 : Blo 2175435 4906349 := bbase (se 3 (by rfl) ⟨919940, by rfl⟩ : syracuseStep 4906349 = 1839881) (by norm_num)
theorem B3270899 : Blo 2175435 3270899 := bstep (se 1 (by rfl) ⟨2453174, by rfl⟩ : syracuseStep 3270899 = 4906349) B4906349
theorem B8722397 : Blo 2175435 8722397 := bstep (se 3 (by rfl) ⟨1635449, by rfl⟩ : syracuseStep 8722397 = 3270899) B3270899
theorem B5814931 : Blo 2175435 5814931 := bstep (se 1 (by rfl) ⟨4361198, by rfl⟩ : syracuseStep 5814931 = 8722397) B8722397
theorem B7753241 : Blo 2175435 7753241 := bstep (se 2 (by rfl) ⟨2907465, by rfl⟩ : syracuseStep 7753241 = 5814931) B5814931
theorem B5168827 : Blo 2175435 5168827 := bstep (se 1 (by rfl) ⟨3876620, by rfl⟩ : syracuseStep 5168827 = 7753241) B7753241
theorem B6891769 : Blo 2175435 6891769 := bstep (se 2 (by rfl) ⟨2584413, by rfl⟩ : syracuseStep 6891769 = 5168827) B5168827
theorem B36756101 : Blo 2175435 36756101 := bstep (se 4 (by rfl) ⟨3445884, by rfl⟩ : syracuseStep 36756101 = 6891769) B6891769
theorem B24504067 : Blo 2175435 24504067 := bstep (se 1 (by rfl) ⟨18378050, by rfl⟩ : syracuseStep 24504067 = 36756101) B36756101
theorem B32672089 : Blo 2175435 32672089 := bstep (se 2 (by rfl) ⟨12252033, by rfl⟩ : syracuseStep 32672089 = 24504067) B24504067
theorem B43562785 : Blo 2175435 43562785 := bstep (se 2 (by rfl) ⟨16336044, by rfl⟩ : syracuseStep 43562785 = 32672089) B32672089
theorem B58083713 : Blo 2175435 58083713 := bstep (se 2 (by rfl) ⟨21781392, by rfl⟩ : syracuseStep 58083713 = 43562785) B43562785
theorem B38722475 : Blo 2175435 38722475 := bstep (se 1 (by rfl) ⟨29041856, by rfl⟩ : syracuseStep 38722475 = 58083713) B58083713
theorem B103259933 : Blo 2175435 103259933 := bstep (se 3 (by rfl) ⟨19361237, by rfl⟩ : syracuseStep 103259933 = 38722475) B38722475
theorem B68839955 : Blo 2175435 68839955 := bstep (se 1 (by rfl) ⟨51629966, by rfl⟩ : syracuseStep 68839955 = 103259933) B103259933
theorem B45893303 : Blo 2175435 45893303 := bstep (se 1 (by rfl) ⟨34419977, by rfl⟩ : syracuseStep 45893303 = 68839955) B68839955
theorem B30595535 : Blo 2175435 30595535 := bstep (se 1 (by rfl) ⟨22946651, by rfl⟩ : syracuseStep 30595535 = 45893303) B45893303
theorem B20397023 : Blo 2175435 20397023 := bstep (se 1 (by rfl) ⟨15297767, by rfl⟩ : syracuseStep 20397023 = 30595535) B30595535
theorem B13598015 : Blo 2175435 13598015 := bstep (se 1 (by rfl) ⟨10198511, by rfl⟩ : syracuseStep 13598015 = 20397023) B20397023
theorem B36261373 : Blo 2175435 36261373 := bstep (se 3 (by rfl) ⟨6799007, by rfl⟩ : syracuseStep 36261373 = 13598015) B13598015
theorem B48348497 : Blo 2175435 48348497 := bstep (se 2 (by rfl) ⟨18130686, by rfl⟩ : syracuseStep 48348497 = 36261373) B36261373
theorem B32232331 : Blo 2175435 32232331 := bstep (se 1 (by rfl) ⟨24174248, by rfl⟩ : syracuseStep 32232331 = 48348497) B48348497
theorem B42976441 : Blo 2175435 42976441 := bstep (se 2 (by rfl) ⟨16116165, by rfl⟩ : syracuseStep 42976441 = 32232331) B32232331
theorem B57301921 : Blo 2175435 57301921 := bstep (se 2 (by rfl) ⟨21488220, by rfl⟩ : syracuseStep 57301921 = 42976441) B42976441
theorem B76402561 : Blo 2175435 76402561 := bstep (se 2 (by rfl) ⟨28650960, by rfl⟩ : syracuseStep 76402561 = 57301921) B57301921
theorem B101870081 : Blo 2175435 101870081 := bstep (se 2 (by rfl) ⟨38201280, by rfl⟩ : syracuseStep 101870081 = 76402561) B76402561
theorem B67913387 : Blo 2175435 67913387 := bstep (se 1 (by rfl) ⟨50935040, by rfl⟩ : syracuseStep 67913387 = 101870081) B101870081
theorem B45275591 : Blo 2175435 45275591 := bstep (se 1 (by rfl) ⟨33956693, by rfl⟩ : syracuseStep 45275591 = 67913387) B67913387
theorem B30183727 : Blo 2175435 30183727 := bstep (se 1 (by rfl) ⟨22637795, by rfl⟩ : syracuseStep 30183727 = 45275591) B45275591
theorem B40244969 : Blo 2175435 40244969 := bstep (se 2 (by rfl) ⟨15091863, by rfl⟩ : syracuseStep 40244969 = 30183727) B30183727
theorem B107319917 : Blo 2175435 107319917 := bstep (se 3 (by rfl) ⟨20122484, by rfl⟩ : syracuseStep 107319917 = 40244969) B40244969
theorem B286186445 : Blo 2175435 286186445 := bstep (se 3 (by rfl) ⟨53659958, by rfl⟩ : syracuseStep 286186445 = 107319917) B107319917
theorem B190790963 : Blo 2175435 190790963 := bstep (se 1 (by rfl) ⟨143093222, by rfl⟩ : syracuseStep 190790963 = 286186445) B286186445
theorem B127193975 : Blo 2175435 127193975 := bstep (se 1 (by rfl) ⟨95395481, by rfl⟩ : syracuseStep 127193975 = 190790963) B190790963
theorem B84795983 : Blo 2175435 84795983 := bstep (se 1 (by rfl) ⟨63596987, by rfl⟩ : syracuseStep 84795983 = 127193975) B127193975
theorem B56530655 : Blo 2175435 56530655 := bstep (se 1 (by rfl) ⟨42397991, by rfl⟩ : syracuseStep 56530655 = 84795983) B84795983
theorem B37687103 : Blo 2175435 37687103 := bstep (se 1 (by rfl) ⟨28265327, by rfl⟩ : syracuseStep 37687103 = 56530655) B56530655
theorem B25124735 : Blo 2175435 25124735 := bstep (se 1 (by rfl) ⟨18843551, by rfl⟩ : syracuseStep 25124735 = 37687103) B37687103
theorem B16749823 : Blo 2175435 16749823 := bstep (se 1 (by rfl) ⟨12562367, by rfl⟩ : syracuseStep 16749823 = 25124735) B25124735
theorem B22333097 : Blo 2175435 22333097 := bstep (se 2 (by rfl) ⟨8374911, by rfl⟩ : syracuseStep 22333097 = 16749823) B16749823
theorem B14888731 : Blo 2175435 14888731 := bstep (se 1 (by rfl) ⟨11166548, by rfl⟩ : syracuseStep 14888731 = 22333097) B22333097
theorem B19851641 : Blo 2175435 19851641 := bstep (se 2 (by rfl) ⟨7444365, by rfl⟩ : syracuseStep 19851641 = 14888731) B14888731
theorem B13234427 : Blo 2175435 13234427 := bstep (se 1 (by rfl) ⟨9925820, by rfl⟩ : syracuseStep 13234427 = 19851641) B19851641
theorem B8822951 : Blo 2175435 8822951 := bstep (se 1 (by rfl) ⟨6617213, by rfl⟩ : syracuseStep 8822951 = 13234427) B13234427
theorem B5881967 : Blo 2175435 5881967 := bstep (se 1 (by rfl) ⟨4411475, by rfl⟩ : syracuseStep 5881967 = 8822951) B8822951
theorem B3921311 : Blo 2175435 3921311 := bstep (se 1 (by rfl) ⟨2940983, by rfl⟩ : syracuseStep 3921311 = 5881967) B5881967
theorem B2614207 : Blo 2175435 2614207 := bstep (se 1 (by rfl) ⟨1960655, by rfl⟩ : syracuseStep 2614207 = 3921311) B3921311
theorem B3485609 : Blo 2175435 3485609 := bstep (se 2 (by rfl) ⟨1307103, by rfl⟩ : syracuseStep 3485609 = 2614207) B2614207
theorem B2323739 : Blo 2175435 2323739 := bstep (se 1 (by rfl) ⟨1742804, by rfl⟩ : syracuseStep 2323739 = 3485609) B3485609
theorem B6196637 : Blo 2175435 6196637 := bstep (se 3 (by rfl) ⟨1161869, by rfl⟩ : syracuseStep 6196637 = 2323739) B2323739
theorem B4131091 : Blo 2175435 4131091 := bstep (se 1 (by rfl) ⟨3098318, by rfl⟩ : syracuseStep 4131091 = 6196637) B6196637
theorem B5508121 : Blo 2175435 5508121 := bstep (se 2 (by rfl) ⟨2065545, by rfl⟩ : syracuseStep 5508121 = 4131091) B4131091
theorem B7344161 : Blo 2175435 7344161 := bstep (se 2 (by rfl) ⟨2754060, by rfl⟩ : syracuseStep 7344161 = 5508121) B5508121
theorem B4896107 : Blo 2175435 4896107 := bstep (se 1 (by rfl) ⟨3672080, by rfl⟩ : syracuseStep 4896107 = 7344161) B7344161
theorem B3264071 : Blo 2175435 3264071 := bstep (se 1 (by rfl) ⟨2448053, by rfl⟩ : syracuseStep 3264071 = 4896107) B4896107
theorem B2176047 : Blo 2175435 2176047 := bstep (se 1 (by rfl) ⟨1632035, by rfl⟩ : syracuseStep 2176047 = 3264071) B3264071
theorem B3264077 : Blo 2175435 3264077 := bbase (se 3 (by rfl) ⟨612014, by rfl⟩ : syracuseStep 3264077 = 1224029) (by norm_num)
theorem B2176051 : Blo 2175435 2176051 := bstep (se 1 (by rfl) ⟨1632038, by rfl⟩ : syracuseStep 2176051 = 3264077) B3264077
theorem B4896125 : Blo 2175435 4896125 := bbase (se 3 (by rfl) ⟨918023, by rfl⟩ : syracuseStep 4896125 = 1836047) (by norm_num)
theorem B3264083 : Blo 2175435 3264083 := bstep (se 1 (by rfl) ⟨2448062, by rfl⟩ : syracuseStep 3264083 = 4896125) B4896125
theorem B2176055 : Blo 2175435 2176055 := bstep (se 1 (by rfl) ⟨1632041, by rfl⟩ : syracuseStep 2176055 = 3264083) B3264083
theorem B3672101 : Blo 2175435 3672101 := bbase (se 4 (by rfl) ⟨344259, by rfl⟩ : syracuseStep 3672101 = 688519) (by norm_num)
theorem B2448067 : Blo 2175435 2448067 := bstep (se 1 (by rfl) ⟨1836050, by rfl⟩ : syracuseStep 2448067 = 3672101) B3672101
theorem B3264089 : Blo 2175435 3264089 := bstep (se 2 (by rfl) ⟨1224033, by rfl⟩ : syracuseStep 3264089 = 2448067) B2448067
theorem B2176059 : Blo 2175435 2176059 := bstep (se 1 (by rfl) ⟨1632044, by rfl⟩ : syracuseStep 2176059 = 3264089) B3264089
theorem B3098341 : Blo 2175435 3098341 := bbase (se 4 (by rfl) ⟨290469, by rfl⟩ : syracuseStep 3098341 = 580939) (by norm_num)
theorem B16524485 : Blo 2175435 16524485 := bstep (se 4 (by rfl) ⟨1549170, by rfl⟩ : syracuseStep 16524485 = 3098341) B3098341
theorem B11016323 : Blo 2175435 11016323 := bstep (se 1 (by rfl) ⟨8262242, by rfl⟩ : syracuseStep 11016323 = 16524485) B16524485
theorem B7344215 : Blo 2175435 7344215 := bstep (se 1 (by rfl) ⟨5508161, by rfl⟩ : syracuseStep 7344215 = 11016323) B11016323
theorem B4896143 : Blo 2175435 4896143 := bstep (se 1 (by rfl) ⟨3672107, by rfl⟩ : syracuseStep 4896143 = 7344215) B7344215
theorem B3264095 : Blo 2175435 3264095 := bstep (se 1 (by rfl) ⟨2448071, by rfl⟩ : syracuseStep 3264095 = 4896143) B4896143
theorem B2176063 : Blo 2175435 2176063 := bstep (se 1 (by rfl) ⟨1632047, by rfl⟩ : syracuseStep 2176063 = 3264095) B3264095
theorem B3264101 : Blo 2175435 3264101 := bbase (se 4 (by rfl) ⟨306009, by rfl⟩ : syracuseStep 3264101 = 612019) (by norm_num)
theorem B2176067 : Blo 2175435 2176067 := bstep (se 1 (by rfl) ⟨1632050, by rfl⟩ : syracuseStep 2176067 = 3264101) B3264101
theorem B2323765 : Blo 2175435 2323765 := bbase (se 5 (by rfl) ⟨108926, by rfl⟩ : syracuseStep 2323765 = 217853) (by norm_num)
theorem B3098353 : Blo 2175435 3098353 := bstep (se 2 (by rfl) ⟨1161882, by rfl⟩ : syracuseStep 3098353 = 2323765) B2323765
theorem B4131137 : Blo 2175435 4131137 := bstep (se 2 (by rfl) ⟨1549176, by rfl⟩ : syracuseStep 4131137 = 3098353) B3098353
theorem B2754091 : Blo 2175435 2754091 := bstep (se 1 (by rfl) ⟨2065568, by rfl⟩ : syracuseStep 2754091 = 4131137) B4131137
theorem B3672121 : Blo 2175435 3672121 := bstep (se 2 (by rfl) ⟨1377045, by rfl⟩ : syracuseStep 3672121 = 2754091) B2754091
theorem B4896161 : Blo 2175435 4896161 := bstep (se 2 (by rfl) ⟨1836060, by rfl⟩ : syracuseStep 4896161 = 3672121) B3672121
theorem B3264107 : Blo 2175435 3264107 := bstep (se 1 (by rfl) ⟨2448080, by rfl⟩ : syracuseStep 3264107 = 4896161) B4896161
theorem B2176071 : Blo 2175435 2176071 := bstep (se 1 (by rfl) ⟨1632053, by rfl⟩ : syracuseStep 2176071 = 3264107) B3264107
theorem B2448085 : Blo 2175435 2448085 := bbase (se 7 (by rfl) ⟨28688, by rfl⟩ : syracuseStep 2448085 = 57377) (by norm_num)
theorem B3264113 : Blo 2175435 3264113 := bstep (se 2 (by rfl) ⟨1224042, by rfl⟩ : syracuseStep 3264113 = 2448085) B2448085
theorem B2176075 : Blo 2175435 2176075 := bstep (se 1 (by rfl) ⟨1632056, by rfl⟩ : syracuseStep 2176075 = 3264113) B3264113
theorem B2754101 : Blo 2175435 2754101 := bbase (se 5 (by rfl) ⟨129098, by rfl⟩ : syracuseStep 2754101 = 258197) (by norm_num)
theorem B7344269 : Blo 2175435 7344269 := bstep (se 3 (by rfl) ⟨1377050, by rfl⟩ : syracuseStep 7344269 = 2754101) B2754101
theorem B4896179 : Blo 2175435 4896179 := bstep (se 1 (by rfl) ⟨3672134, by rfl⟩ : syracuseStep 4896179 = 7344269) B7344269
theorem B3264119 : Blo 2175435 3264119 := bstep (se 1 (by rfl) ⟨2448089, by rfl⟩ : syracuseStep 3264119 = 4896179) B4896179
theorem B2176079 : Blo 2175435 2176079 := bstep (se 1 (by rfl) ⟨1632059, by rfl⟩ : syracuseStep 2176079 = 3264119) B3264119
theorem B3264125 : Blo 2175435 3264125 := bbase (se 3 (by rfl) ⟨612023, by rfl⟩ : syracuseStep 3264125 = 1224047) (by norm_num)
theorem B2176083 : Blo 2175435 2176083 := bstep (se 1 (by rfl) ⟨1632062, by rfl⟩ : syracuseStep 2176083 = 3264125) B3264125
theorem B4896197 : Blo 2175435 4896197 := bbase (se 4 (by rfl) ⟨459018, by rfl⟩ : syracuseStep 4896197 = 918037) (by norm_num)
theorem B3264131 : Blo 2175435 3264131 := bstep (se 1 (by rfl) ⟨2448098, by rfl⟩ : syracuseStep 3264131 = 4896197) B4896197
theorem B2176087 : Blo 2175435 2176087 := bstep (se 1 (by rfl) ⟨1632065, by rfl⟩ : syracuseStep 2176087 = 3264131) B3264131
theorem B2791693 : Blo 2175435 2791693 := bbase (se 3 (by rfl) ⟨523442, by rfl⟩ : syracuseStep 2791693 = 1046885) (by norm_num)
theorem B3722257 : Blo 2175435 3722257 := bstep (se 2 (by rfl) ⟨1395846, by rfl⟩ : syracuseStep 3722257 = 2791693) B2791693
theorem B19852037 : Blo 2175435 19852037 := bstep (se 4 (by rfl) ⟨1861128, by rfl⟩ : syracuseStep 19852037 = 3722257) B3722257
theorem B13234691 : Blo 2175435 13234691 := bstep (se 1 (by rfl) ⟨9926018, by rfl⟩ : syracuseStep 13234691 = 19852037) B19852037
theorem B35292509 : Blo 2175435 35292509 := bstep (se 3 (by rfl) ⟨6617345, by rfl⟩ : syracuseStep 35292509 = 13234691) B13234691
theorem B23528339 : Blo 2175435 23528339 := bstep (se 1 (by rfl) ⟨17646254, by rfl⟩ : syracuseStep 23528339 = 35292509) B35292509
theorem B15685559 : Blo 2175435 15685559 := bstep (se 1 (by rfl) ⟨11764169, by rfl⟩ : syracuseStep 15685559 = 23528339) B23528339
theorem B10457039 : Blo 2175435 10457039 := bstep (se 1 (by rfl) ⟨7842779, by rfl⟩ : syracuseStep 10457039 = 15685559) B15685559
theorem B6971359 : Blo 2175435 6971359 := bstep (se 1 (by rfl) ⟨5228519, by rfl⟩ : syracuseStep 6971359 = 10457039) B10457039
theorem B9295145 : Blo 2175435 9295145 := bstep (se 2 (by rfl) ⟨3485679, by rfl⟩ : syracuseStep 9295145 = 6971359) B6971359
theorem B6196763 : Blo 2175435 6196763 := bstep (se 1 (by rfl) ⟨4647572, by rfl⟩ : syracuseStep 6196763 = 9295145) B9295145
theorem B4131175 : Blo 2175435 4131175 := bstep (se 1 (by rfl) ⟨3098381, by rfl⟩ : syracuseStep 4131175 = 6196763) B6196763
theorem B5508233 : Blo 2175435 5508233 := bstep (se 2 (by rfl) ⟨2065587, by rfl⟩ : syracuseStep 5508233 = 4131175) B4131175
theorem B3672155 : Blo 2175435 3672155 := bstep (se 1 (by rfl) ⟨2754116, by rfl⟩ : syracuseStep 3672155 = 5508233) B5508233
theorem B2448103 : Blo 2175435 2448103 := bstep (se 1 (by rfl) ⟨1836077, by rfl⟩ : syracuseStep 2448103 = 3672155) B3672155
theorem B3264137 : Blo 2175435 3264137 := bstep (se 2 (by rfl) ⟨1224051, by rfl⟩ : syracuseStep 3264137 = 2448103) B2448103
theorem B2176091 : Blo 2175435 2176091 := bstep (se 1 (by rfl) ⟨1632068, by rfl⟩ : syracuseStep 2176091 = 3264137) B3264137
theorem B11016485 : Blo 2175435 11016485 := bbase (se 4 (by rfl) ⟨1032795, by rfl⟩ : syracuseStep 11016485 = 2065591) (by norm_num)
theorem B7344323 : Blo 2175435 7344323 := bstep (se 1 (by rfl) ⟨5508242, by rfl⟩ : syracuseStep 7344323 = 11016485) B11016485
theorem B4896215 : Blo 2175435 4896215 := bstep (se 1 (by rfl) ⟨3672161, by rfl⟩ : syracuseStep 4896215 = 7344323) B7344323
theorem B3264143 : Blo 2175435 3264143 := bstep (se 1 (by rfl) ⟨2448107, by rfl⟩ : syracuseStep 3264143 = 4896215) B4896215
theorem B2176095 : Blo 2175435 2176095 := bstep (se 1 (by rfl) ⟨1632071, by rfl⟩ : syracuseStep 2176095 = 3264143) B3264143
theorem B3264149 : Blo 2175435 3264149 := bbase (se 6 (by rfl) ⟨76503, by rfl⟩ : syracuseStep 3264149 = 153007) (by norm_num)
theorem B2176099 : Blo 2175435 2176099 := bstep (se 1 (by rfl) ⟨1632074, by rfl⟩ : syracuseStep 2176099 = 3264149) B3264149
theorem B6617381 : Blo 2175435 6617381 := bbase (se 4 (by rfl) ⟨620379, by rfl⟩ : syracuseStep 6617381 = 1240759) (by norm_num)
theorem B17646349 : Blo 2175435 17646349 := bstep (se 3 (by rfl) ⟨3308690, by rfl⟩ : syracuseStep 17646349 = 6617381) B6617381
theorem B23528465 : Blo 2175435 23528465 := bstep (se 2 (by rfl) ⟨8823174, by rfl⟩ : syracuseStep 23528465 = 17646349) B17646349
theorem B15685643 : Blo 2175435 15685643 := bstep (se 1 (by rfl) ⟨11764232, by rfl⟩ : syracuseStep 15685643 = 23528465) B23528465
theorem B10457095 : Blo 2175435 10457095 := bstep (se 1 (by rfl) ⟨7842821, by rfl⟩ : syracuseStep 10457095 = 15685643) B15685643
theorem B13942793 : Blo 2175435 13942793 := bstep (se 2 (by rfl) ⟨5228547, by rfl⟩ : syracuseStep 13942793 = 10457095) B10457095
theorem B9295195 : Blo 2175435 9295195 := bstep (se 1 (by rfl) ⟨6971396, by rfl⟩ : syracuseStep 9295195 = 13942793) B13942793
theorem B12393593 : Blo 2175435 12393593 := bstep (se 2 (by rfl) ⟨4647597, by rfl⟩ : syracuseStep 12393593 = 9295195) B9295195
theorem B8262395 : Blo 2175435 8262395 := bstep (se 1 (by rfl) ⟨6196796, by rfl⟩ : syracuseStep 8262395 = 12393593) B12393593
theorem B5508263 : Blo 2175435 5508263 := bstep (se 1 (by rfl) ⟨4131197, by rfl⟩ : syracuseStep 5508263 = 8262395) B8262395
theorem B3672175 : Blo 2175435 3672175 := bstep (se 1 (by rfl) ⟨2754131, by rfl⟩ : syracuseStep 3672175 = 5508263) B5508263
theorem B4896233 : Blo 2175435 4896233 := bstep (se 2 (by rfl) ⟨1836087, by rfl⟩ : syracuseStep 4896233 = 3672175) B3672175
theorem B3264155 : Blo 2175435 3264155 := bstep (se 1 (by rfl) ⟨2448116, by rfl⟩ : syracuseStep 3264155 = 4896233) B4896233
theorem B2176103 : Blo 2175435 2176103 := bstep (se 1 (by rfl) ⟨1632077, by rfl⟩ : syracuseStep 2176103 = 3264155) B3264155
theorem B2448121 : Blo 2175435 2448121 := bbase (se 2 (by rfl) ⟨918045, by rfl⟩ : syracuseStep 2448121 = 1836091) (by norm_num)
theorem B3264161 : Blo 2175435 3264161 := bstep (se 2 (by rfl) ⟨1224060, by rfl⟩ : syracuseStep 3264161 = 2448121) B2448121
theorem B2176107 : Blo 2175435 2176107 := bstep (se 1 (by rfl) ⟨1632080, by rfl⟩ : syracuseStep 2176107 = 3264161) B3264161
theorem B11764277 : Blo 2175435 11764277 := bbase (se 5 (by rfl) ⟨551450, by rfl⟩ : syracuseStep 11764277 = 1102901) (by norm_num)
theorem B7842851 : Blo 2175435 7842851 := bstep (se 1 (by rfl) ⟨5882138, by rfl⟩ : syracuseStep 7842851 = 11764277) B11764277
theorem B5228567 : Blo 2175435 5228567 := bstep (se 1 (by rfl) ⟨3921425, by rfl⟩ : syracuseStep 5228567 = 7842851) B7842851
theorem B3485711 : Blo 2175435 3485711 := bstep (se 1 (by rfl) ⟨2614283, by rfl⟩ : syracuseStep 3485711 = 5228567) B5228567
theorem B9295229 : Blo 2175435 9295229 := bstep (se 3 (by rfl) ⟨1742855, by rfl⟩ : syracuseStep 9295229 = 3485711) B3485711
theorem B6196819 : Blo 2175435 6196819 := bstep (se 1 (by rfl) ⟨4647614, by rfl⟩ : syracuseStep 6196819 = 9295229) B9295229
theorem B8262425 : Blo 2175435 8262425 := bstep (se 2 (by rfl) ⟨3098409, by rfl⟩ : syracuseStep 8262425 = 6196819) B6196819
theorem B5508283 : Blo 2175435 5508283 := bstep (se 1 (by rfl) ⟨4131212, by rfl⟩ : syracuseStep 5508283 = 8262425) B8262425
theorem B7344377 : Blo 2175435 7344377 := bstep (se 2 (by rfl) ⟨2754141, by rfl⟩ : syracuseStep 7344377 = 5508283) B5508283
theorem B4896251 : Blo 2175435 4896251 := bstep (se 1 (by rfl) ⟨3672188, by rfl⟩ : syracuseStep 4896251 = 7344377) B7344377
theorem B3264167 : Blo 2175435 3264167 := bstep (se 1 (by rfl) ⟨2448125, by rfl⟩ : syracuseStep 3264167 = 4896251) B4896251
theorem B2176111 : Blo 2175435 2176111 := bstep (se 1 (by rfl) ⟨1632083, by rfl⟩ : syracuseStep 2176111 = 3264167) B3264167
theorem B3264173 : Blo 2175435 3264173 := bbase (se 3 (by rfl) ⟨612032, by rfl⟩ : syracuseStep 3264173 = 1224065) (by norm_num)
theorem B2176115 : Blo 2175435 2176115 := bstep (se 1 (by rfl) ⟨1632086, by rfl⟩ : syracuseStep 2176115 = 3264173) B3264173
theorem B4896269 : Blo 2175435 4896269 := bbase (se 3 (by rfl) ⟨918050, by rfl⟩ : syracuseStep 4896269 = 1836101) (by norm_num)
theorem B3264179 : Blo 2175435 3264179 := bstep (se 1 (by rfl) ⟨2448134, by rfl⟩ : syracuseStep 3264179 = 4896269) B4896269
theorem B2176119 : Blo 2175435 2176119 := bstep (se 1 (by rfl) ⟨1632089, by rfl⟩ : syracuseStep 2176119 = 3264179) B3264179
theorem B2754157 : Blo 2175435 2754157 := bbase (se 3 (by rfl) ⟨516404, by rfl⟩ : syracuseStep 2754157 = 1032809) (by norm_num)
theorem B3672209 : Blo 2175435 3672209 := bstep (se 2 (by rfl) ⟨1377078, by rfl⟩ : syracuseStep 3672209 = 2754157) B2754157
theorem B2448139 : Blo 2175435 2448139 := bstep (se 1 (by rfl) ⟨1836104, by rfl⟩ : syracuseStep 2448139 = 3672209) B3672209
theorem B3264185 : Blo 2175435 3264185 := bstep (se 2 (by rfl) ⟨1224069, by rfl⟩ : syracuseStep 3264185 = 2448139) B2448139
theorem B2176123 : Blo 2175435 2176123 := bstep (se 1 (by rfl) ⟨1632092, by rfl⟩ : syracuseStep 2176123 = 3264185) B3264185
theorem B21199765 : Blo 2175435 21199765 := bbase (se 6 (by rfl) ⟨496869, by rfl⟩ : syracuseStep 21199765 = 993739) (by norm_num)
theorem B28266353 : Blo 2175435 28266353 := bstep (se 2 (by rfl) ⟨10599882, by rfl⟩ : syracuseStep 28266353 = 21199765) B21199765
theorem B18844235 : Blo 2175435 18844235 := bstep (se 1 (by rfl) ⟨14133176, by rfl⟩ : syracuseStep 18844235 = 28266353) B28266353
theorem B12562823 : Blo 2175435 12562823 := bstep (se 1 (by rfl) ⟨9422117, by rfl⟩ : syracuseStep 12562823 = 18844235) B18844235
theorem B33500861 : Blo 2175435 33500861 := bstep (se 3 (by rfl) ⟨6281411, by rfl⟩ : syracuseStep 33500861 = 12562823) B12562823
theorem B22333907 : Blo 2175435 22333907 := bstep (se 1 (by rfl) ⟨16750430, by rfl⟩ : syracuseStep 22333907 = 33500861) B33500861
theorem B14889271 : Blo 2175435 14889271 := bstep (se 1 (by rfl) ⟨11166953, by rfl⟩ : syracuseStep 14889271 = 22333907) B22333907
theorem B19852361 : Blo 2175435 19852361 := bstep (se 2 (by rfl) ⟨7444635, by rfl⟩ : syracuseStep 19852361 = 14889271) B14889271
theorem B13234907 : Blo 2175435 13234907 := bstep (se 1 (by rfl) ⟨9926180, by rfl⟩ : syracuseStep 13234907 = 19852361) B19852361
theorem B8823271 : Blo 2175435 8823271 := bstep (se 1 (by rfl) ⟨6617453, by rfl⟩ : syracuseStep 8823271 = 13234907) B13234907
theorem B11764361 : Blo 2175435 11764361 := bstep (se 2 (by rfl) ⟨4411635, by rfl⟩ : syracuseStep 11764361 = 8823271) B8823271
theorem B7842907 : Blo 2175435 7842907 := bstep (se 1 (by rfl) ⟨5882180, by rfl⟩ : syracuseStep 7842907 = 11764361) B11764361
theorem B10457209 : Blo 2175435 10457209 := bstep (se 2 (by rfl) ⟨3921453, by rfl⟩ : syracuseStep 10457209 = 7842907) B7842907
theorem B13942945 : Blo 2175435 13942945 := bstep (se 2 (by rfl) ⟨5228604, by rfl⟩ : syracuseStep 13942945 = 10457209) B10457209
theorem B18590593 : Blo 2175435 18590593 := bstep (se 2 (by rfl) ⟨6971472, by rfl⟩ : syracuseStep 18590593 = 13942945) B13942945
theorem B24787457 : Blo 2175435 24787457 := bstep (se 2 (by rfl) ⟨9295296, by rfl⟩ : syracuseStep 24787457 = 18590593) B18590593
theorem B16524971 : Blo 2175435 16524971 := bstep (se 1 (by rfl) ⟨12393728, by rfl⟩ : syracuseStep 16524971 = 24787457) B24787457
theorem B11016647 : Blo 2175435 11016647 := bstep (se 1 (by rfl) ⟨8262485, by rfl⟩ : syracuseStep 11016647 = 16524971) B16524971
theorem B7344431 : Blo 2175435 7344431 := bstep (se 1 (by rfl) ⟨5508323, by rfl⟩ : syracuseStep 7344431 = 11016647) B11016647
theorem B4896287 : Blo 2175435 4896287 := bstep (se 1 (by rfl) ⟨3672215, by rfl⟩ : syracuseStep 4896287 = 7344431) B7344431
theorem B3264191 : Blo 2175435 3264191 := bstep (se 1 (by rfl) ⟨2448143, by rfl⟩ : syracuseStep 3264191 = 4896287) B4896287
theorem B2176127 : Blo 2175435 2176127 := bstep (se 1 (by rfl) ⟨1632095, by rfl⟩ : syracuseStep 2176127 = 3264191) B3264191
theorem B3264197 : Blo 2175435 3264197 := bbase (se 4 (by rfl) ⟨306018, by rfl⟩ : syracuseStep 3264197 = 612037) (by norm_num)
theorem B2176131 : Blo 2175435 2176131 := bstep (se 1 (by rfl) ⟨1632098, by rfl⟩ : syracuseStep 2176131 = 3264197) B3264197
theorem B3672229 : Blo 2175435 3672229 := bbase (se 4 (by rfl) ⟨344271, by rfl⟩ : syracuseStep 3672229 = 688543) (by norm_num)
theorem B4896305 : Blo 2175435 4896305 := bstep (se 2 (by rfl) ⟨1836114, by rfl⟩ : syracuseStep 4896305 = 3672229) B3672229
theorem B3264203 : Blo 2175435 3264203 := bstep (se 1 (by rfl) ⟨2448152, by rfl⟩ : syracuseStep 3264203 = 4896305) B4896305
theorem B2176135 : Blo 2175435 2176135 := bstep (se 1 (by rfl) ⟨1632101, by rfl⟩ : syracuseStep 2176135 = 3264203) B3264203
theorem B2448157 : Blo 2175435 2448157 := bbase (se 3 (by rfl) ⟨459029, by rfl⟩ : syracuseStep 2448157 = 918059) (by norm_num)
theorem B3264209 : Blo 2175435 3264209 := bstep (se 2 (by rfl) ⟨1224078, by rfl⟩ : syracuseStep 3264209 = 2448157) B2448157
theorem B2176139 : Blo 2175435 2176139 := bstep (se 1 (by rfl) ⟨1632104, by rfl⟩ : syracuseStep 2176139 = 3264209) B3264209
theorem B7344485 : Blo 2175435 7344485 := bbase (se 4 (by rfl) ⟨688545, by rfl⟩ : syracuseStep 7344485 = 1377091) (by norm_num)
theorem B4896323 : Blo 2175435 4896323 := bstep (se 1 (by rfl) ⟨3672242, by rfl⟩ : syracuseStep 4896323 = 7344485) B7344485
theorem B3264215 : Blo 2175435 3264215 := bstep (se 1 (by rfl) ⟨2448161, by rfl⟩ : syracuseStep 3264215 = 4896323) B4896323
theorem B2176143 : Blo 2175435 2176143 := bstep (se 1 (by rfl) ⟨1632107, by rfl⟩ : syracuseStep 2176143 = 3264215) B3264215
theorem B3264221 : Blo 2175435 3264221 := bbase (se 3 (by rfl) ⟨612041, by rfl⟩ : syracuseStep 3264221 = 1224083) (by norm_num)
theorem B2176147 : Blo 2175435 2176147 := bstep (se 1 (by rfl) ⟨1632110, by rfl⟩ : syracuseStep 2176147 = 3264221) B3264221
theorem B4896341 : Blo 2175435 4896341 := bbase (se 8 (by rfl) ⟨28689, by rfl⟩ : syracuseStep 4896341 = 57379) (by norm_num)
theorem B3264227 : Blo 2175435 3264227 := bstep (se 1 (by rfl) ⟨2448170, by rfl⟩ : syracuseStep 3264227 = 4896341) B4896341
theorem B2176151 : Blo 2175435 2176151 := bstep (se 1 (by rfl) ⟨1632113, by rfl⟩ : syracuseStep 2176151 = 3264227) B3264227
theorem B4647709 : Blo 2175435 4647709 := bbase (se 3 (by rfl) ⟨871445, by rfl⟩ : syracuseStep 4647709 = 1742891) (by norm_num)
theorem B6196945 : Blo 2175435 6196945 := bstep (se 2 (by rfl) ⟨2323854, by rfl⟩ : syracuseStep 6196945 = 4647709) B4647709
theorem B8262593 : Blo 2175435 8262593 := bstep (se 2 (by rfl) ⟨3098472, by rfl⟩ : syracuseStep 8262593 = 6196945) B6196945
theorem B5508395 : Blo 2175435 5508395 := bstep (se 1 (by rfl) ⟨4131296, by rfl⟩ : syracuseStep 5508395 = 8262593) B8262593
theorem B3672263 : Blo 2175435 3672263 := bstep (se 1 (by rfl) ⟨2754197, by rfl⟩ : syracuseStep 3672263 = 5508395) B5508395
theorem B2448175 : Blo 2175435 2448175 := bstep (se 1 (by rfl) ⟨1836131, by rfl⟩ : syracuseStep 2448175 = 3672263) B3672263
theorem B3264233 : Blo 2175435 3264233 := bstep (se 2 (by rfl) ⟨1224087, by rfl⟩ : syracuseStep 3264233 = 2448175) B2448175
theorem B2176155 : Blo 2175435 2176155 := bstep (se 1 (by rfl) ⟨1632116, by rfl⟩ : syracuseStep 2176155 = 3264233) B3264233
theorem B7066693 : Blo 2175435 7066693 := bbase (se 4 (by rfl) ⟨662502, by rfl⟩ : syracuseStep 7066693 = 1325005) (by norm_num)
theorem B9422257 : Blo 2175435 9422257 := bstep (se 2 (by rfl) ⟨3533346, by rfl⟩ : syracuseStep 9422257 = 7066693) B7066693
theorem B12563009 : Blo 2175435 12563009 := bstep (se 2 (by rfl) ⟨4711128, by rfl⟩ : syracuseStep 12563009 = 9422257) B9422257
theorem B8375339 : Blo 2175435 8375339 := bstep (se 1 (by rfl) ⟨6281504, by rfl⟩ : syracuseStep 8375339 = 12563009) B12563009
theorem B22334237 : Blo 2175435 22334237 := bstep (se 3 (by rfl) ⟨4187669, by rfl⟩ : syracuseStep 22334237 = 8375339) B8375339
theorem B14889491 : Blo 2175435 14889491 := bstep (se 1 (by rfl) ⟨11167118, by rfl⟩ : syracuseStep 14889491 = 22334237) B22334237
theorem B9926327 : Blo 2175435 9926327 := bstep (se 1 (by rfl) ⟨7444745, by rfl⟩ : syracuseStep 9926327 = 14889491) B14889491
theorem B6617551 : Blo 2175435 6617551 := bstep (se 1 (by rfl) ⟨4963163, by rfl⟩ : syracuseStep 6617551 = 9926327) B9926327
theorem B8823401 : Blo 2175435 8823401 := bstep (se 2 (by rfl) ⟨3308775, by rfl⟩ : syracuseStep 8823401 = 6617551) B6617551
theorem B5882267 : Blo 2175435 5882267 := bstep (se 1 (by rfl) ⟨4411700, by rfl⟩ : syracuseStep 5882267 = 8823401) B8823401
theorem B15686045 : Blo 2175435 15686045 := bstep (se 3 (by rfl) ⟨2941133, by rfl⟩ : syracuseStep 15686045 = 5882267) B5882267
theorem B10457363 : Blo 2175435 10457363 := bstep (se 1 (by rfl) ⟨7843022, by rfl⟩ : syracuseStep 10457363 = 15686045) B15686045
theorem B27886301 : Blo 2175435 27886301 := bstep (se 3 (by rfl) ⟨5228681, by rfl⟩ : syracuseStep 27886301 = 10457363) B10457363
theorem B18590867 : Blo 2175435 18590867 := bstep (se 1 (by rfl) ⟨13943150, by rfl⟩ : syracuseStep 18590867 = 27886301) B27886301
theorem B12393911 : Blo 2175435 12393911 := bstep (se 1 (by rfl) ⟨9295433, by rfl⟩ : syracuseStep 12393911 = 18590867) B18590867
theorem B8262607 : Blo 2175435 8262607 := bstep (se 1 (by rfl) ⟨6196955, by rfl⟩ : syracuseStep 8262607 = 12393911) B12393911
theorem B11016809 : Blo 2175435 11016809 := bstep (se 2 (by rfl) ⟨4131303, by rfl⟩ : syracuseStep 11016809 = 8262607) B8262607
theorem B7344539 : Blo 2175435 7344539 := bstep (se 1 (by rfl) ⟨5508404, by rfl⟩ : syracuseStep 7344539 = 11016809) B11016809
theorem B4896359 : Blo 2175435 4896359 := bstep (se 1 (by rfl) ⟨3672269, by rfl⟩ : syracuseStep 4896359 = 7344539) B7344539
theorem B3264239 : Blo 2175435 3264239 := bstep (se 1 (by rfl) ⟨2448179, by rfl⟩ : syracuseStep 3264239 = 4896359) B4896359
theorem B2176159 : Blo 2175435 2176159 := bstep (se 1 (by rfl) ⟨1632119, by rfl⟩ : syracuseStep 2176159 = 3264239) B3264239
theorem B3264245 : Blo 2175435 3264245 := bbase (se 5 (by rfl) ⟨153011, by rfl⟩ : syracuseStep 3264245 = 306023) (by norm_num)
theorem B2176163 : Blo 2175435 2176163 := bstep (se 1 (by rfl) ⟨1632122, by rfl⟩ : syracuseStep 2176163 = 3264245) B3264245
theorem B3308789 : Blo 2175435 3308789 := bbase (se 5 (by rfl) ⟨155099, by rfl⟩ : syracuseStep 3308789 = 310199) (by norm_num)
theorem B8823437 : Blo 2175435 8823437 := bstep (se 3 (by rfl) ⟨1654394, by rfl⟩ : syracuseStep 8823437 = 3308789) B3308789
theorem B5882291 : Blo 2175435 5882291 := bstep (se 1 (by rfl) ⟨4411718, by rfl⟩ : syracuseStep 5882291 = 8823437) B8823437
theorem B3921527 : Blo 2175435 3921527 := bstep (se 1 (by rfl) ⟨2941145, by rfl⟩ : syracuseStep 3921527 = 5882291) B5882291
theorem B2614351 : Blo 2175435 2614351 := bstep (se 1 (by rfl) ⟨1960763, by rfl⟩ : syracuseStep 2614351 = 3921527) B3921527
theorem B3485801 : Blo 2175435 3485801 := bstep (se 2 (by rfl) ⟨1307175, by rfl⟩ : syracuseStep 3485801 = 2614351) B2614351
theorem B9295469 : Blo 2175435 9295469 := bstep (se 3 (by rfl) ⟨1742900, by rfl⟩ : syracuseStep 9295469 = 3485801) B3485801
theorem B6196979 : Blo 2175435 6196979 := bstep (se 1 (by rfl) ⟨4647734, by rfl⟩ : syracuseStep 6196979 = 9295469) B9295469
theorem B4131319 : Blo 2175435 4131319 := bstep (se 1 (by rfl) ⟨3098489, by rfl⟩ : syracuseStep 4131319 = 6196979) B6196979
theorem B5508425 : Blo 2175435 5508425 := bstep (se 2 (by rfl) ⟨2065659, by rfl⟩ : syracuseStep 5508425 = 4131319) B4131319
theorem B3672283 : Blo 2175435 3672283 := bstep (se 1 (by rfl) ⟨2754212, by rfl⟩ : syracuseStep 3672283 = 5508425) B5508425
theorem B4896377 : Blo 2175435 4896377 := bstep (se 2 (by rfl) ⟨1836141, by rfl⟩ : syracuseStep 4896377 = 3672283) B3672283
theorem B3264251 : Blo 2175435 3264251 := bstep (se 1 (by rfl) ⟨2448188, by rfl⟩ : syracuseStep 3264251 = 4896377) B4896377
theorem B2176167 : Blo 2175435 2176167 := bstep (se 1 (by rfl) ⟨1632125, by rfl⟩ : syracuseStep 2176167 = 3264251) B3264251
theorem B2448193 : Blo 2175435 2448193 := bbase (se 2 (by rfl) ⟨918072, by rfl⟩ : syracuseStep 2448193 = 1836145) (by norm_num)
theorem B3264257 : Blo 2175435 3264257 := bstep (se 2 (by rfl) ⟨1224096, by rfl⟩ : syracuseStep 3264257 = 2448193) B2448193
theorem B2176171 : Blo 2175435 2176171 := bstep (se 1 (by rfl) ⟨1632128, by rfl⟩ : syracuseStep 2176171 = 3264257) B3264257
theorem B5508445 : Blo 2175435 5508445 := bbase (se 3 (by rfl) ⟨1032833, by rfl⟩ : syracuseStep 5508445 = 2065667) (by norm_num)
theorem B7344593 : Blo 2175435 7344593 := bstep (se 2 (by rfl) ⟨2754222, by rfl⟩ : syracuseStep 7344593 = 5508445) B5508445
theorem B4896395 : Blo 2175435 4896395 := bstep (se 1 (by rfl) ⟨3672296, by rfl⟩ : syracuseStep 4896395 = 7344593) B7344593
theorem B3264263 : Blo 2175435 3264263 := bstep (se 1 (by rfl) ⟨2448197, by rfl⟩ : syracuseStep 3264263 = 4896395) B4896395
theorem B2176175 : Blo 2175435 2176175 := bstep (se 1 (by rfl) ⟨1632131, by rfl⟩ : syracuseStep 2176175 = 3264263) B3264263
theorem B3264269 : Blo 2175435 3264269 := bbase (se 3 (by rfl) ⟨612050, by rfl⟩ : syracuseStep 3264269 = 1224101) (by norm_num)
theorem B2176179 : Blo 2175435 2176179 := bstep (se 1 (by rfl) ⟨1632134, by rfl⟩ : syracuseStep 2176179 = 3264269) B3264269
theorem B4896413 : Blo 2175435 4896413 := bbase (se 3 (by rfl) ⟨918077, by rfl⟩ : syracuseStep 4896413 = 1836155) (by norm_num)
theorem B3264275 : Blo 2175435 3264275 := bstep (se 1 (by rfl) ⟨2448206, by rfl⟩ : syracuseStep 3264275 = 4896413) B4896413
theorem B2176183 : Blo 2175435 2176183 := bstep (se 1 (by rfl) ⟨1632137, by rfl⟩ : syracuseStep 2176183 = 3264275) B3264275
theorem B3672317 : Blo 2175435 3672317 := bbase (se 3 (by rfl) ⟨688559, by rfl⟩ : syracuseStep 3672317 = 1377119) (by norm_num)
theorem B2448211 : Blo 2175435 2448211 := bstep (se 1 (by rfl) ⟨1836158, by rfl⟩ : syracuseStep 2448211 = 3672317) B3672317
theorem B3264281 : Blo 2175435 3264281 := bstep (se 2 (by rfl) ⟨1224105, by rfl⟩ : syracuseStep 3264281 = 2448211) B2448211
theorem B2176187 : Blo 2175435 2176187 := bstep (se 1 (by rfl) ⟨1632140, by rfl⟩ : syracuseStep 2176187 = 3264281) B3264281
theorem B3722429 : Blo 2175435 3722429 := bbase (se 3 (by rfl) ⟨697955, by rfl⟩ : syracuseStep 3722429 = 1395911) (by norm_num)
theorem B2481619 : Blo 2175435 2481619 := bstep (se 1 (by rfl) ⟨1861214, by rfl⟩ : syracuseStep 2481619 = 3722429) B3722429
theorem B3308825 : Blo 2175435 3308825 := bstep (se 2 (by rfl) ⟨1240809, by rfl⟩ : syracuseStep 3308825 = 2481619) B2481619
theorem B2205883 : Blo 2175435 2205883 := bstep (se 1 (by rfl) ⟨1654412, by rfl⟩ : syracuseStep 2205883 = 3308825) B3308825
theorem B11764709 : Blo 2175435 11764709 := bstep (se 4 (by rfl) ⟨1102941, by rfl⟩ : syracuseStep 11764709 = 2205883) B2205883
theorem B7843139 : Blo 2175435 7843139 := bstep (se 1 (by rfl) ⟨5882354, by rfl⟩ : syracuseStep 7843139 = 11764709) B11764709
theorem B5228759 : Blo 2175435 5228759 := bstep (se 1 (by rfl) ⟨3921569, by rfl⟩ : syracuseStep 5228759 = 7843139) B7843139
theorem B3485839 : Blo 2175435 3485839 := bstep (se 1 (by rfl) ⟨2614379, by rfl⟩ : syracuseStep 3485839 = 5228759) B5228759
theorem B4647785 : Blo 2175435 4647785 := bstep (se 2 (by rfl) ⟨1742919, by rfl⟩ : syracuseStep 4647785 = 3485839) B3485839
theorem B12394093 : Blo 2175435 12394093 := bstep (se 3 (by rfl) ⟨2323892, by rfl⟩ : syracuseStep 12394093 = 4647785) B4647785
theorem B16525457 : Blo 2175435 16525457 := bstep (se 2 (by rfl) ⟨6197046, by rfl⟩ : syracuseStep 16525457 = 12394093) B12394093
theorem B11016971 : Blo 2175435 11016971 := bstep (se 1 (by rfl) ⟨8262728, by rfl⟩ : syracuseStep 11016971 = 16525457) B16525457
theorem B7344647 : Blo 2175435 7344647 := bstep (se 1 (by rfl) ⟨5508485, by rfl⟩ : syracuseStep 7344647 = 11016971) B11016971
theorem B4896431 : Blo 2175435 4896431 := bstep (se 1 (by rfl) ⟨3672323, by rfl⟩ : syracuseStep 4896431 = 7344647) B7344647
theorem B3264287 : Blo 2175435 3264287 := bstep (se 1 (by rfl) ⟨2448215, by rfl⟩ : syracuseStep 3264287 = 4896431) B4896431
theorem B2176191 : Blo 2175435 2176191 := bstep (se 1 (by rfl) ⟨1632143, by rfl⟩ : syracuseStep 2176191 = 3264287) B3264287
theorem B3264293 : Blo 2175435 3264293 := bbase (se 4 (by rfl) ⟨306027, by rfl⟩ : syracuseStep 3264293 = 612055) (by norm_num)
theorem B2176195 : Blo 2175435 2176195 := bstep (se 1 (by rfl) ⟨1632146, by rfl⟩ : syracuseStep 2176195 = 3264293) B3264293
theorem B2754253 : Blo 2175435 2754253 := bbase (se 3 (by rfl) ⟨516422, by rfl⟩ : syracuseStep 2754253 = 1032845) (by norm_num)
theorem B3672337 : Blo 2175435 3672337 := bstep (se 2 (by rfl) ⟨1377126, by rfl⟩ : syracuseStep 3672337 = 2754253) B2754253
theorem B4896449 : Blo 2175435 4896449 := bstep (se 2 (by rfl) ⟨1836168, by rfl⟩ : syracuseStep 4896449 = 3672337) B3672337
theorem B3264299 : Blo 2175435 3264299 := bstep (se 1 (by rfl) ⟨2448224, by rfl⟩ : syracuseStep 3264299 = 4896449) B4896449
theorem B2176199 : Blo 2175435 2176199 := bstep (se 1 (by rfl) ⟨1632149, by rfl⟩ : syracuseStep 2176199 = 3264299) B3264299
theorem B2448229 : Blo 2175435 2448229 := bbase (se 4 (by rfl) ⟨229521, by rfl⟩ : syracuseStep 2448229 = 459043) (by norm_num)
theorem B3264305 : Blo 2175435 3264305 := bstep (se 2 (by rfl) ⟨1224114, by rfl⟩ : syracuseStep 3264305 = 2448229) B2448229
theorem B2176203 : Blo 2175435 2176203 := bstep (se 1 (by rfl) ⟨1632152, by rfl⟩ : syracuseStep 2176203 = 3264305) B3264305
theorem B6197093 : Blo 2175435 6197093 := bbase (se 4 (by rfl) ⟨580977, by rfl⟩ : syracuseStep 6197093 = 1161955) (by norm_num)
theorem B4131395 : Blo 2175435 4131395 := bstep (se 1 (by rfl) ⟨3098546, by rfl⟩ : syracuseStep 4131395 = 6197093) B6197093
theorem B2754263 : Blo 2175435 2754263 := bstep (se 1 (by rfl) ⟨2065697, by rfl⟩ : syracuseStep 2754263 = 4131395) B4131395
theorem B7344701 : Blo 2175435 7344701 := bstep (se 3 (by rfl) ⟨1377131, by rfl⟩ : syracuseStep 7344701 = 2754263) B2754263
theorem B4896467 : Blo 2175435 4896467 := bstep (se 1 (by rfl) ⟨3672350, by rfl⟩ : syracuseStep 4896467 = 7344701) B7344701
theorem B3264311 : Blo 2175435 3264311 := bstep (se 1 (by rfl) ⟨2448233, by rfl⟩ : syracuseStep 3264311 = 4896467) B4896467
theorem B2176207 : Blo 2175435 2176207 := bstep (se 1 (by rfl) ⟨1632155, by rfl⟩ : syracuseStep 2176207 = 3264311) B3264311
theorem B3264317 : Blo 2175435 3264317 := bbase (se 3 (by rfl) ⟨612059, by rfl⟩ : syracuseStep 3264317 = 1224119) (by norm_num)
theorem B2176211 : Blo 2175435 2176211 := bstep (se 1 (by rfl) ⟨1632158, by rfl⟩ : syracuseStep 2176211 = 3264317) B3264317
theorem B4896485 : Blo 2175435 4896485 := bbase (se 4 (by rfl) ⟨459045, by rfl⟩ : syracuseStep 4896485 = 918091) (by norm_num)
theorem B3264323 : Blo 2175435 3264323 := bstep (se 1 (by rfl) ⟨2448242, by rfl⟩ : syracuseStep 3264323 = 4896485) B4896485
theorem B2176215 : Blo 2175435 2176215 := bstep (se 1 (by rfl) ⟨1632161, by rfl⟩ : syracuseStep 2176215 = 3264323) B3264323
theorem B5508557 : Blo 2175435 5508557 := bbase (se 3 (by rfl) ⟨1032854, by rfl⟩ : syracuseStep 5508557 = 2065709) (by norm_num)
theorem B3672371 : Blo 2175435 3672371 := bstep (se 1 (by rfl) ⟨2754278, by rfl⟩ : syracuseStep 3672371 = 5508557) B5508557
theorem B2448247 : Blo 2175435 2448247 := bstep (se 1 (by rfl) ⟨1836185, by rfl⟩ : syracuseStep 2448247 = 3672371) B3672371
theorem B3264329 : Blo 2175435 3264329 := bstep (se 2 (by rfl) ⟨1224123, by rfl⟩ : syracuseStep 3264329 = 2448247) B2448247
theorem B2176219 : Blo 2175435 2176219 := bstep (se 1 (by rfl) ⟨1632164, by rfl⟩ : syracuseStep 2176219 = 3264329) B3264329
theorem B5228837 : Blo 2175435 5228837 := bbase (se 4 (by rfl) ⟨490203, by rfl⟩ : syracuseStep 5228837 = 980407) (by norm_num)
theorem B3485891 : Blo 2175435 3485891 := bstep (se 1 (by rfl) ⟨2614418, by rfl⟩ : syracuseStep 3485891 = 5228837) B5228837
theorem B2323927 : Blo 2175435 2323927 := bstep (se 1 (by rfl) ⟨1742945, by rfl⟩ : syracuseStep 2323927 = 3485891) B3485891
theorem B3098569 : Blo 2175435 3098569 := bstep (se 2 (by rfl) ⟨1161963, by rfl⟩ : syracuseStep 3098569 = 2323927) B2323927
theorem B4131425 : Blo 2175435 4131425 := bstep (se 2 (by rfl) ⟨1549284, by rfl⟩ : syracuseStep 4131425 = 3098569) B3098569
theorem B11017133 : Blo 2175435 11017133 := bstep (se 3 (by rfl) ⟨2065712, by rfl⟩ : syracuseStep 11017133 = 4131425) B4131425
theorem B7344755 : Blo 2175435 7344755 := bstep (se 1 (by rfl) ⟨5508566, by rfl⟩ : syracuseStep 7344755 = 11017133) B11017133
theorem B4896503 : Blo 2175435 4896503 := bstep (se 1 (by rfl) ⟨3672377, by rfl⟩ : syracuseStep 4896503 = 7344755) B7344755
theorem B3264335 : Blo 2175435 3264335 := bstep (se 1 (by rfl) ⟨2448251, by rfl⟩ : syracuseStep 3264335 = 4896503) B4896503
theorem B2176223 : Blo 2175435 2176223 := bstep (se 1 (by rfl) ⟨1632167, by rfl⟩ : syracuseStep 2176223 = 3264335) B3264335
theorem B3264341 : Blo 2175435 3264341 := bbase (se 9 (by rfl) ⟨9563, by rfl⟩ : syracuseStep 3264341 = 19127) (by norm_num)
theorem B2176227 : Blo 2175435 2176227 := bstep (se 1 (by rfl) ⟨1632170, by rfl⟩ : syracuseStep 2176227 = 3264341) B3264341
theorem B3183709 : Blo 2175435 3183709 := bbase (se 3 (by rfl) ⟨596945, by rfl⟩ : syracuseStep 3183709 = 1193891) (by norm_num)
theorem B4244945 : Blo 2175435 4244945 := bstep (se 2 (by rfl) ⟨1591854, by rfl⟩ : syracuseStep 4244945 = 3183709) B3183709
theorem B11319853 : Blo 2175435 11319853 := bstep (se 3 (by rfl) ⟨2122472, by rfl⟩ : syracuseStep 11319853 = 4244945) B4244945
theorem B15093137 : Blo 2175435 15093137 := bstep (se 2 (by rfl) ⟨5659926, by rfl⟩ : syracuseStep 15093137 = 11319853) B11319853
theorem B10062091 : Blo 2175435 10062091 := bstep (se 1 (by rfl) ⟨7546568, by rfl⟩ : syracuseStep 10062091 = 15093137) B15093137
theorem B13416121 : Blo 2175435 13416121 := bstep (se 2 (by rfl) ⟨5031045, by rfl⟩ : syracuseStep 13416121 = 10062091) B10062091
theorem B17888161 : Blo 2175435 17888161 := bstep (se 2 (by rfl) ⟨6708060, by rfl⟩ : syracuseStep 17888161 = 13416121) B13416121
theorem B23850881 : Blo 2175435 23850881 := bstep (se 2 (by rfl) ⟨8944080, by rfl⟩ : syracuseStep 23850881 = 17888161) B17888161
theorem B15900587 : Blo 2175435 15900587 := bstep (se 1 (by rfl) ⟨11925440, by rfl⟩ : syracuseStep 15900587 = 23850881) B23850881
theorem B10600391 : Blo 2175435 10600391 := bstep (se 1 (by rfl) ⟨7950293, by rfl⟩ : syracuseStep 10600391 = 15900587) B15900587
theorem B7066927 : Blo 2175435 7066927 := bstep (se 1 (by rfl) ⟨5300195, by rfl⟩ : syracuseStep 7066927 = 10600391) B10600391
theorem B9422569 : Blo 2175435 9422569 := bstep (se 2 (by rfl) ⟨3533463, by rfl⟩ : syracuseStep 9422569 = 7066927) B7066927
theorem B12563425 : Blo 2175435 12563425 := bstep (se 2 (by rfl) ⟨4711284, by rfl⟩ : syracuseStep 12563425 = 9422569) B9422569
theorem B16751233 : Blo 2175435 16751233 := bstep (se 2 (by rfl) ⟨6281712, by rfl⟩ : syracuseStep 16751233 = 12563425) B12563425
theorem B22334977 : Blo 2175435 22334977 := bstep (se 2 (by rfl) ⟨8375616, by rfl⟩ : syracuseStep 22334977 = 16751233) B16751233
theorem B29779969 : Blo 2175435 29779969 := bstep (se 2 (by rfl) ⟨11167488, by rfl⟩ : syracuseStep 29779969 = 22334977) B22334977
theorem B39706625 : Blo 2175435 39706625 := bstep (se 2 (by rfl) ⟨14889984, by rfl⟩ : syracuseStep 39706625 = 29779969) B29779969
theorem B26471083 : Blo 2175435 26471083 := bstep (se 1 (by rfl) ⟨19853312, by rfl⟩ : syracuseStep 26471083 = 39706625) B39706625
theorem B35294777 : Blo 2175435 35294777 := bstep (se 2 (by rfl) ⟨13235541, by rfl⟩ : syracuseStep 35294777 = 26471083) B26471083
theorem B23529851 : Blo 2175435 23529851 := bstep (se 1 (by rfl) ⟨17647388, by rfl⟩ : syracuseStep 23529851 = 35294777) B35294777
theorem B15686567 : Blo 2175435 15686567 := bstep (se 1 (by rfl) ⟨11764925, by rfl⟩ : syracuseStep 15686567 = 23529851) B23529851
theorem B10457711 : Blo 2175435 10457711 := bstep (se 1 (by rfl) ⟨7843283, by rfl⟩ : syracuseStep 10457711 = 15686567) B15686567
theorem B6971807 : Blo 2175435 6971807 := bstep (se 1 (by rfl) ⟨5228855, by rfl⟩ : syracuseStep 6971807 = 10457711) B10457711
theorem B4647871 : Blo 2175435 4647871 := bstep (se 1 (by rfl) ⟨3485903, by rfl⟩ : syracuseStep 4647871 = 6971807) B6971807
theorem B6197161 : Blo 2175435 6197161 := bstep (se 2 (by rfl) ⟨2323935, by rfl⟩ : syracuseStep 6197161 = 4647871) B4647871
theorem B8262881 : Blo 2175435 8262881 := bstep (se 2 (by rfl) ⟨3098580, by rfl⟩ : syracuseStep 8262881 = 6197161) B6197161
theorem B5508587 : Blo 2175435 5508587 := bstep (se 1 (by rfl) ⟨4131440, by rfl⟩ : syracuseStep 5508587 = 8262881) B8262881
theorem B3672391 : Blo 2175435 3672391 := bstep (se 1 (by rfl) ⟨2754293, by rfl⟩ : syracuseStep 3672391 = 5508587) B5508587
theorem B4896521 : Blo 2175435 4896521 := bstep (se 2 (by rfl) ⟨1836195, by rfl⟩ : syracuseStep 4896521 = 3672391) B3672391
theorem B3264347 : Blo 2175435 3264347 := bstep (se 1 (by rfl) ⟨2448260, by rfl⟩ : syracuseStep 3264347 = 4896521) B4896521
theorem B2176231 : Blo 2175435 2176231 := bstep (se 1 (by rfl) ⟨1632173, by rfl⟩ : syracuseStep 2176231 = 3264347) B3264347
theorem B2448265 : Blo 2175435 2448265 := bbase (se 2 (by rfl) ⟨918099, by rfl⟩ : syracuseStep 2448265 = 1836199) (by norm_num)
theorem B3264353 : Blo 2175435 3264353 := bstep (se 2 (by rfl) ⟨1224132, by rfl⟩ : syracuseStep 3264353 = 2448265) B2448265
theorem B2176235 : Blo 2175435 2176235 := bstep (se 1 (by rfl) ⟨1632176, by rfl⟩ : syracuseStep 2176235 = 3264353) B3264353
theorem B3722509 : Blo 2175435 3722509 := bbase (se 3 (by rfl) ⟨697970, by rfl⟩ : syracuseStep 3722509 = 1395941) (by norm_num)
theorem B19853381 : Blo 2175435 19853381 := bstep (se 4 (by rfl) ⟨1861254, by rfl⟩ : syracuseStep 19853381 = 3722509) B3722509
theorem B52942349 : Blo 2175435 52942349 := bstep (se 3 (by rfl) ⟨9926690, by rfl⟩ : syracuseStep 52942349 = 19853381) B19853381
theorem B141179597 : Blo 2175435 141179597 := bstep (se 3 (by rfl) ⟨26471174, by rfl⟩ : syracuseStep 141179597 = 52942349) B52942349
theorem B94119731 : Blo 2175435 94119731 := bstep (se 1 (by rfl) ⟨70589798, by rfl⟩ : syracuseStep 94119731 = 141179597) B141179597
theorem B62746487 : Blo 2175435 62746487 := bstep (se 1 (by rfl) ⟨47059865, by rfl⟩ : syracuseStep 62746487 = 94119731) B94119731
theorem B41830991 : Blo 2175435 41830991 := bstep (se 1 (by rfl) ⟨31373243, by rfl⟩ : syracuseStep 41830991 = 62746487) B62746487
theorem B27887327 : Blo 2175435 27887327 := bstep (se 1 (by rfl) ⟨20915495, by rfl⟩ : syracuseStep 27887327 = 41830991) B41830991
theorem B18591551 : Blo 2175435 18591551 := bstep (se 1 (by rfl) ⟨13943663, by rfl⟩ : syracuseStep 18591551 = 27887327) B27887327
theorem B12394367 : Blo 2175435 12394367 := bstep (se 1 (by rfl) ⟨9295775, by rfl⟩ : syracuseStep 12394367 = 18591551) B18591551
theorem B8262911 : Blo 2175435 8262911 := bstep (se 1 (by rfl) ⟨6197183, by rfl⟩ : syracuseStep 8262911 = 12394367) B12394367
theorem B5508607 : Blo 2175435 5508607 := bstep (se 1 (by rfl) ⟨4131455, by rfl⟩ : syracuseStep 5508607 = 8262911) B8262911
theorem B7344809 : Blo 2175435 7344809 := bstep (se 2 (by rfl) ⟨2754303, by rfl⟩ : syracuseStep 7344809 = 5508607) B5508607
theorem B4896539 : Blo 2175435 4896539 := bstep (se 1 (by rfl) ⟨3672404, by rfl⟩ : syracuseStep 4896539 = 7344809) B7344809
theorem B3264359 : Blo 2175435 3264359 := bstep (se 1 (by rfl) ⟨2448269, by rfl⟩ : syracuseStep 3264359 = 4896539) B4896539
theorem B2176239 : Blo 2175435 2176239 := bstep (se 1 (by rfl) ⟨1632179, by rfl⟩ : syracuseStep 2176239 = 3264359) B3264359
theorem B3264365 : Blo 2175435 3264365 := bbase (se 3 (by rfl) ⟨612068, by rfl⟩ : syracuseStep 3264365 = 1224137) (by norm_num)
theorem B2176243 : Blo 2175435 2176243 := bstep (se 1 (by rfl) ⟨1632182, by rfl⟩ : syracuseStep 2176243 = 3264365) B3264365
theorem B4896557 : Blo 2175435 4896557 := bbase (se 3 (by rfl) ⟨918104, by rfl⟩ : syracuseStep 4896557 = 1836209) (by norm_num)
theorem B3264371 : Blo 2175435 3264371 := bstep (se 1 (by rfl) ⟨2448278, by rfl⟩ : syracuseStep 3264371 = 4896557) B4896557
theorem B2176247 : Blo 2175435 2176247 := bstep (se 1 (by rfl) ⟨1632185, by rfl⟩ : syracuseStep 2176247 = 3264371) B3264371
theorem B9295829 : Blo 2175435 9295829 := bbase (se 7 (by rfl) ⟨108935, by rfl⟩ : syracuseStep 9295829 = 217871) (by norm_num)
theorem B6197219 : Blo 2175435 6197219 := bstep (se 1 (by rfl) ⟨4647914, by rfl⟩ : syracuseStep 6197219 = 9295829) B9295829
theorem B4131479 : Blo 2175435 4131479 := bstep (se 1 (by rfl) ⟨3098609, by rfl⟩ : syracuseStep 4131479 = 6197219) B6197219
theorem B2754319 : Blo 2175435 2754319 := bstep (se 1 (by rfl) ⟨2065739, by rfl⟩ : syracuseStep 2754319 = 4131479) B4131479
theorem B3672425 : Blo 2175435 3672425 := bstep (se 2 (by rfl) ⟨1377159, by rfl⟩ : syracuseStep 3672425 = 2754319) B2754319
theorem B2448283 : Blo 2175435 2448283 := bstep (se 1 (by rfl) ⟨1836212, by rfl⟩ : syracuseStep 2448283 = 3672425) B3672425
theorem B3264377 : Blo 2175435 3264377 := bstep (se 2 (by rfl) ⟨1224141, by rfl⟩ : syracuseStep 3264377 = 2448283) B2448283
theorem B2176251 : Blo 2175435 2176251 := bstep (se 1 (by rfl) ⟨1632188, by rfl⟩ : syracuseStep 2176251 = 3264377) B3264377
theorem B13943765 : Blo 2175435 13943765 := bbase (se 7 (by rfl) ⟨163403, by rfl⟩ : syracuseStep 13943765 = 326807) (by norm_num)
theorem B37183373 : Blo 2175435 37183373 := bstep (se 3 (by rfl) ⟨6971882, by rfl⟩ : syracuseStep 37183373 = 13943765) B13943765
theorem B24788915 : Blo 2175435 24788915 := bstep (se 1 (by rfl) ⟨18591686, by rfl⟩ : syracuseStep 24788915 = 37183373) B37183373
theorem B16525943 : Blo 2175435 16525943 := bstep (se 1 (by rfl) ⟨12394457, by rfl⟩ : syracuseStep 16525943 = 24788915) B24788915
theorem B11017295 : Blo 2175435 11017295 := bstep (se 1 (by rfl) ⟨8262971, by rfl⟩ : syracuseStep 11017295 = 16525943) B16525943
theorem B7344863 : Blo 2175435 7344863 := bstep (se 1 (by rfl) ⟨5508647, by rfl⟩ : syracuseStep 7344863 = 11017295) B11017295
theorem B4896575 : Blo 2175435 4896575 := bstep (se 1 (by rfl) ⟨3672431, by rfl⟩ : syracuseStep 4896575 = 7344863) B7344863
theorem B3264383 : Blo 2175435 3264383 := bstep (se 1 (by rfl) ⟨2448287, by rfl⟩ : syracuseStep 3264383 = 4896575) B4896575
theorem B2176255 : Blo 2175435 2176255 := bstep (se 1 (by rfl) ⟨1632191, by rfl⟩ : syracuseStep 2176255 = 3264383) B3264383
theorem B3264389 : Blo 2175435 3264389 := bbase (se 4 (by rfl) ⟨306036, by rfl⟩ : syracuseStep 3264389 = 612073) (by norm_num)
theorem B2176259 : Blo 2175435 2176259 := bstep (se 1 (by rfl) ⟨1632194, by rfl⟩ : syracuseStep 2176259 = 3264389) B3264389
theorem B3672445 : Blo 2175435 3672445 := bbase (se 3 (by rfl) ⟨688583, by rfl⟩ : syracuseStep 3672445 = 1377167) (by norm_num)
theorem B4896593 : Blo 2175435 4896593 := bstep (se 2 (by rfl) ⟨1836222, by rfl⟩ : syracuseStep 4896593 = 3672445) B3672445
theorem B3264395 : Blo 2175435 3264395 := bstep (se 1 (by rfl) ⟨2448296, by rfl⟩ : syracuseStep 3264395 = 4896593) B4896593
theorem B2176263 : Blo 2175435 2176263 := bstep (se 1 (by rfl) ⟨1632197, by rfl⟩ : syracuseStep 2176263 = 3264395) B3264395
theorem B2448301 : Blo 2175435 2448301 := bbase (se 3 (by rfl) ⟨459056, by rfl⟩ : syracuseStep 2448301 = 918113) (by norm_num)
theorem B3264401 : Blo 2175435 3264401 := bstep (se 2 (by rfl) ⟨1224150, by rfl⟩ : syracuseStep 3264401 = 2448301) B2448301
theorem B2176267 : Blo 2175435 2176267 := bstep (se 1 (by rfl) ⟨1632200, by rfl⟩ : syracuseStep 2176267 = 3264401) B3264401
theorem B7344917 : Blo 2175435 7344917 := bbase (se 6 (by rfl) ⟨172146, by rfl⟩ : syracuseStep 7344917 = 344293) (by norm_num)
theorem B4896611 : Blo 2175435 4896611 := bstep (se 1 (by rfl) ⟨3672458, by rfl⟩ : syracuseStep 4896611 = 7344917) B7344917
theorem B3264407 : Blo 2175435 3264407 := bstep (se 1 (by rfl) ⟨2448305, by rfl⟩ : syracuseStep 3264407 = 4896611) B4896611
theorem B2176271 : Blo 2175435 2176271 := bstep (se 1 (by rfl) ⟨1632203, by rfl⟩ : syracuseStep 2176271 = 3264407) B3264407
theorem B3264413 : Blo 2175435 3264413 := bbase (se 3 (by rfl) ⟨612077, by rfl⟩ : syracuseStep 3264413 = 1224155) (by norm_num)
theorem B2176275 : Blo 2175435 2176275 := bstep (se 1 (by rfl) ⟨1632206, by rfl⟩ : syracuseStep 2176275 = 3264413) B3264413
theorem B4896629 : Blo 2175435 4896629 := bbase (se 5 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 4896629 = 459059) (by norm_num)
theorem B3264419 : Blo 2175435 3264419 := bstep (se 1 (by rfl) ⟨2448314, by rfl⟩ : syracuseStep 3264419 = 4896629) B4896629
theorem B2176279 : Blo 2175435 2176279 := bstep (se 1 (by rfl) ⟨1632209, by rfl⟩ : syracuseStep 2176279 = 3264419) B3264419
theorem B4187909 : Blo 2175435 4187909 := bbase (se 4 (by rfl) ⟨392616, by rfl⟩ : syracuseStep 4187909 = 785233) (by norm_num)
theorem B11167757 : Blo 2175435 11167757 := bstep (se 3 (by rfl) ⟨2093954, by rfl⟩ : syracuseStep 11167757 = 4187909) B4187909
theorem B7445171 : Blo 2175435 7445171 := bstep (se 1 (by rfl) ⟨5583878, by rfl⟩ : syracuseStep 7445171 = 11167757) B11167757
theorem B4963447 : Blo 2175435 4963447 := bstep (se 1 (by rfl) ⟨3722585, by rfl⟩ : syracuseStep 4963447 = 7445171) B7445171
theorem B6617929 : Blo 2175435 6617929 := bstep (se 2 (by rfl) ⟨2481723, by rfl⟩ : syracuseStep 6617929 = 4963447) B4963447
theorem B8823905 : Blo 2175435 8823905 := bstep (se 2 (by rfl) ⟨3308964, by rfl⟩ : syracuseStep 8823905 = 6617929) B6617929
theorem B5882603 : Blo 2175435 5882603 := bstep (se 1 (by rfl) ⟨4411952, by rfl⟩ : syracuseStep 5882603 = 8823905) B8823905
theorem B15686941 : Blo 2175435 15686941 := bstep (se 3 (by rfl) ⟨2941301, by rfl⟩ : syracuseStep 15686941 = 5882603) B5882603
theorem B20915921 : Blo 2175435 20915921 := bstep (se 2 (by rfl) ⟨7843470, by rfl⟩ : syracuseStep 20915921 = 15686941) B15686941
theorem B13943947 : Blo 2175435 13943947 := bstep (se 1 (by rfl) ⟨10457960, by rfl⟩ : syracuseStep 13943947 = 20915921) B20915921
theorem B18591929 : Blo 2175435 18591929 := bstep (se 2 (by rfl) ⟨6971973, by rfl⟩ : syracuseStep 18591929 = 13943947) B13943947
theorem B12394619 : Blo 2175435 12394619 := bstep (se 1 (by rfl) ⟨9295964, by rfl⟩ : syracuseStep 12394619 = 18591929) B18591929
theorem B8263079 : Blo 2175435 8263079 := bstep (se 1 (by rfl) ⟨6197309, by rfl⟩ : syracuseStep 8263079 = 12394619) B12394619
theorem B5508719 : Blo 2175435 5508719 := bstep (se 1 (by rfl) ⟨4131539, by rfl⟩ : syracuseStep 5508719 = 8263079) B8263079
theorem B3672479 : Blo 2175435 3672479 := bstep (se 1 (by rfl) ⟨2754359, by rfl⟩ : syracuseStep 3672479 = 5508719) B5508719
theorem B2448319 : Blo 2175435 2448319 := bstep (se 1 (by rfl) ⟨1836239, by rfl⟩ : syracuseStep 2448319 = 3672479) B3672479
theorem B3264425 : Blo 2175435 3264425 := bstep (se 2 (by rfl) ⟨1224159, by rfl⟩ : syracuseStep 3264425 = 2448319) B2448319
theorem B2176283 : Blo 2175435 2176283 := bstep (se 1 (by rfl) ⟨1632212, by rfl⟩ : syracuseStep 2176283 = 3264425) B3264425
theorem B8263093 : Blo 2175435 8263093 := bbase (se 5 (by rfl) ⟨387332, by rfl⟩ : syracuseStep 8263093 = 774665) (by norm_num)
theorem B11017457 : Blo 2175435 11017457 := bstep (se 2 (by rfl) ⟨4131546, by rfl⟩ : syracuseStep 11017457 = 8263093) B8263093
theorem B7344971 : Blo 2175435 7344971 := bstep (se 1 (by rfl) ⟨5508728, by rfl⟩ : syracuseStep 7344971 = 11017457) B11017457
theorem B4896647 : Blo 2175435 4896647 := bstep (se 1 (by rfl) ⟨3672485, by rfl⟩ : syracuseStep 4896647 = 7344971) B7344971
theorem B3264431 : Blo 2175435 3264431 := bstep (se 1 (by rfl) ⟨2448323, by rfl⟩ : syracuseStep 3264431 = 4896647) B4896647
theorem B2176287 : Blo 2175435 2176287 := bstep (se 1 (by rfl) ⟨1632215, by rfl⟩ : syracuseStep 2176287 = 3264431) B3264431
theorem B3264437 : Blo 2175435 3264437 := bbase (se 5 (by rfl) ⟨153020, by rfl⟩ : syracuseStep 3264437 = 306041) (by norm_num)
theorem B2176291 : Blo 2175435 2176291 := bstep (se 1 (by rfl) ⟨1632218, by rfl⟩ : syracuseStep 2176291 = 3264437) B3264437
theorem B5508749 : Blo 2175435 5508749 := bbase (se 3 (by rfl) ⟨1032890, by rfl⟩ : syracuseStep 5508749 = 2065781) (by norm_num)
theorem B3672499 : Blo 2175435 3672499 := bstep (se 1 (by rfl) ⟨2754374, by rfl⟩ : syracuseStep 3672499 = 5508749) B5508749
theorem B4896665 : Blo 2175435 4896665 := bstep (se 2 (by rfl) ⟨1836249, by rfl⟩ : syracuseStep 4896665 = 3672499) B3672499
theorem B3264443 : Blo 2175435 3264443 := bstep (se 1 (by rfl) ⟨2448332, by rfl⟩ : syracuseStep 3264443 = 4896665) B4896665
theorem B2176295 : Blo 2175435 2176295 := bstep (se 1 (by rfl) ⟨1632221, by rfl⟩ : syracuseStep 2176295 = 3264443) B3264443
theorem B2448337 : Blo 2175435 2448337 := bbase (se 2 (by rfl) ⟨918126, by rfl⟩ : syracuseStep 2448337 = 1836253) (by norm_num)
theorem B3264449 : Blo 2175435 3264449 := bstep (se 2 (by rfl) ⟨1224168, by rfl⟩ : syracuseStep 3264449 = 2448337) B2448337
theorem B2176299 : Blo 2175435 2176299 := bstep (se 1 (by rfl) ⟨1632224, by rfl⟩ : syracuseStep 2176299 = 3264449) B3264449
theorem B5229029 : Blo 2175435 5229029 := bbase (se 4 (by rfl) ⟨490221, by rfl⟩ : syracuseStep 5229029 = 980443) (by norm_num)
theorem B3486019 : Blo 2175435 3486019 := bstep (se 1 (by rfl) ⟨2614514, by rfl⟩ : syracuseStep 3486019 = 5229029) B5229029
theorem B4648025 : Blo 2175435 4648025 := bstep (se 2 (by rfl) ⟨1743009, by rfl⟩ : syracuseStep 4648025 = 3486019) B3486019
theorem B3098683 : Blo 2175435 3098683 := bstep (se 1 (by rfl) ⟨2324012, by rfl⟩ : syracuseStep 3098683 = 4648025) B4648025
theorem B4131577 : Blo 2175435 4131577 := bstep (se 2 (by rfl) ⟨1549341, by rfl⟩ : syracuseStep 4131577 = 3098683) B3098683
theorem B5508769 : Blo 2175435 5508769 := bstep (se 2 (by rfl) ⟨2065788, by rfl⟩ : syracuseStep 5508769 = 4131577) B4131577
theorem B7345025 : Blo 2175435 7345025 := bstep (se 2 (by rfl) ⟨2754384, by rfl⟩ : syracuseStep 7345025 = 5508769) B5508769
theorem B4896683 : Blo 2175435 4896683 := bstep (se 1 (by rfl) ⟨3672512, by rfl⟩ : syracuseStep 4896683 = 7345025) B7345025
theorem B3264455 : Blo 2175435 3264455 := bstep (se 1 (by rfl) ⟨2448341, by rfl⟩ : syracuseStep 3264455 = 4896683) B4896683
theorem B2176303 : Blo 2175435 2176303 := bstep (se 1 (by rfl) ⟨1632227, by rfl⟩ : syracuseStep 2176303 = 3264455) B3264455
theorem B3264461 : Blo 2175435 3264461 := bbase (se 3 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 3264461 = 1224173) (by norm_num)
theorem B2176307 : Blo 2175435 2176307 := bstep (se 1 (by rfl) ⟨1632230, by rfl⟩ : syracuseStep 2176307 = 3264461) B3264461
theorem B4896701 : Blo 2175435 4896701 := bbase (se 3 (by rfl) ⟨918131, by rfl⟩ : syracuseStep 4896701 = 1836263) (by norm_num)
theorem B3264467 : Blo 2175435 3264467 := bstep (se 1 (by rfl) ⟨2448350, by rfl⟩ : syracuseStep 3264467 = 4896701) B4896701
theorem B2176311 : Blo 2175435 2176311 := bstep (se 1 (by rfl) ⟨1632233, by rfl⟩ : syracuseStep 2176311 = 3264467) B3264467
theorem B3672533 : Blo 2175435 3672533 := bbase (se 7 (by rfl) ⟨43037, by rfl⟩ : syracuseStep 3672533 = 86075) (by norm_num)
theorem B2448355 : Blo 2175435 2448355 := bstep (se 1 (by rfl) ⟨1836266, by rfl⟩ : syracuseStep 2448355 = 3672533) B3672533
theorem B3264473 : Blo 2175435 3264473 := bstep (se 2 (by rfl) ⟨1224177, by rfl⟩ : syracuseStep 3264473 = 2448355) B2448355
theorem B2176315 : Blo 2175435 2176315 := bstep (se 1 (by rfl) ⟨1632236, by rfl⟩ : syracuseStep 2176315 = 3264473) B3264473
theorem B9296117 : Blo 2175435 9296117 := bbase (se 5 (by rfl) ⟨435755, by rfl⟩ : syracuseStep 9296117 = 871511) (by norm_num)
theorem B6197411 : Blo 2175435 6197411 := bstep (se 1 (by rfl) ⟨4648058, by rfl⟩ : syracuseStep 6197411 = 9296117) B9296117
theorem B16526429 : Blo 2175435 16526429 := bstep (se 3 (by rfl) ⟨3098705, by rfl⟩ : syracuseStep 16526429 = 6197411) B6197411
theorem B11017619 : Blo 2175435 11017619 := bstep (se 1 (by rfl) ⟨8263214, by rfl⟩ : syracuseStep 11017619 = 16526429) B16526429
theorem B7345079 : Blo 2175435 7345079 := bstep (se 1 (by rfl) ⟨5508809, by rfl⟩ : syracuseStep 7345079 = 11017619) B11017619
theorem B4896719 : Blo 2175435 4896719 := bstep (se 1 (by rfl) ⟨3672539, by rfl⟩ : syracuseStep 4896719 = 7345079) B7345079
theorem B3264479 : Blo 2175435 3264479 := bstep (se 1 (by rfl) ⟨2448359, by rfl⟩ : syracuseStep 3264479 = 4896719) B4896719
theorem B2176319 : Blo 2175435 2176319 := bstep (se 1 (by rfl) ⟨1632239, by rfl⟩ : syracuseStep 2176319 = 3264479) B3264479
theorem B3264485 : Blo 2175435 3264485 := bbase (se 4 (by rfl) ⟨306045, by rfl⟩ : syracuseStep 3264485 = 612091) (by norm_num)
theorem B2176323 : Blo 2175435 2176323 := bstep (se 1 (by rfl) ⟨1632242, by rfl⟩ : syracuseStep 2176323 = 3264485) B3264485
theorem B8824085 : Blo 2175435 8824085 := bbase (se 6 (by rfl) ⟨206814, by rfl⟩ : syracuseStep 8824085 = 413629) (by norm_num)
theorem B5882723 : Blo 2175435 5882723 := bstep (se 1 (by rfl) ⟨4412042, by rfl⟩ : syracuseStep 5882723 = 8824085) B8824085
theorem B3921815 : Blo 2175435 3921815 := bstep (se 1 (by rfl) ⟨2941361, by rfl⟩ : syracuseStep 3921815 = 5882723) B5882723
theorem B10458173 : Blo 2175435 10458173 := bstep (se 3 (by rfl) ⟨1960907, by rfl⟩ : syracuseStep 10458173 = 3921815) B3921815
theorem B6972115 : Blo 2175435 6972115 := bstep (se 1 (by rfl) ⟨5229086, by rfl⟩ : syracuseStep 6972115 = 10458173) B10458173
theorem B9296153 : Blo 2175435 9296153 := bstep (se 2 (by rfl) ⟨3486057, by rfl⟩ : syracuseStep 9296153 = 6972115) B6972115
theorem B6197435 : Blo 2175435 6197435 := bstep (se 1 (by rfl) ⟨4648076, by rfl⟩ : syracuseStep 6197435 = 9296153) B9296153
theorem B4131623 : Blo 2175435 4131623 := bstep (se 1 (by rfl) ⟨3098717, by rfl⟩ : syracuseStep 4131623 = 6197435) B6197435
theorem B2754415 : Blo 2175435 2754415 := bstep (se 1 (by rfl) ⟨2065811, by rfl⟩ : syracuseStep 2754415 = 4131623) B4131623
theorem B3672553 : Blo 2175435 3672553 := bstep (se 2 (by rfl) ⟨1377207, by rfl⟩ : syracuseStep 3672553 = 2754415) B2754415
theorem B4896737 : Blo 2175435 4896737 := bstep (se 2 (by rfl) ⟨1836276, by rfl⟩ : syracuseStep 4896737 = 3672553) B3672553
theorem B3264491 : Blo 2175435 3264491 := bstep (se 1 (by rfl) ⟨2448368, by rfl⟩ : syracuseStep 3264491 = 4896737) B4896737
theorem B2176327 : Blo 2175435 2176327 := bstep (se 1 (by rfl) ⟨1632245, by rfl⟩ : syracuseStep 2176327 = 3264491) B3264491
theorem B2448373 : Blo 2175435 2448373 := bbase (se 5 (by rfl) ⟨114767, by rfl⟩ : syracuseStep 2448373 = 229535) (by norm_num)
theorem B3264497 : Blo 2175435 3264497 := bstep (se 2 (by rfl) ⟨1224186, by rfl⟩ : syracuseStep 3264497 = 2448373) B2448373
theorem B2176331 : Blo 2175435 2176331 := bstep (se 1 (by rfl) ⟨1632248, by rfl⟩ : syracuseStep 2176331 = 3264497) B3264497
theorem B2754425 : Blo 2175435 2754425 := bbase (se 2 (by rfl) ⟨1032909, by rfl⟩ : syracuseStep 2754425 = 2065819) (by norm_num)
theorem B7345133 : Blo 2175435 7345133 := bstep (se 3 (by rfl) ⟨1377212, by rfl⟩ : syracuseStep 7345133 = 2754425) B2754425
theorem B4896755 : Blo 2175435 4896755 := bstep (se 1 (by rfl) ⟨3672566, by rfl⟩ : syracuseStep 4896755 = 7345133) B7345133
theorem B3264503 : Blo 2175435 3264503 := bstep (se 1 (by rfl) ⟨2448377, by rfl⟩ : syracuseStep 3264503 = 4896755) B4896755
theorem B2176335 : Blo 2175435 2176335 := bstep (se 1 (by rfl) ⟨1632251, by rfl⟩ : syracuseStep 2176335 = 3264503) B3264503
theorem B3264509 : Blo 2175435 3264509 := bbase (se 3 (by rfl) ⟨612095, by rfl⟩ : syracuseStep 3264509 = 1224191) (by norm_num)
theorem B2176339 : Blo 2175435 2176339 := bstep (se 1 (by rfl) ⟨1632254, by rfl⟩ : syracuseStep 2176339 = 3264509) B3264509
theorem B4896773 : Blo 2175435 4896773 := bbase (se 4 (by rfl) ⟨459072, by rfl⟩ : syracuseStep 4896773 = 918145) (by norm_num)
theorem B3264515 : Blo 2175435 3264515 := bstep (se 1 (by rfl) ⟨2448386, by rfl⟩ : syracuseStep 3264515 = 4896773) B4896773
theorem B2176343 : Blo 2175435 2176343 := bstep (se 1 (by rfl) ⟨1632257, by rfl⟩ : syracuseStep 2176343 = 3264515) B3264515
theorem B4131661 : Blo 2175435 4131661 := bbase (se 3 (by rfl) ⟨774686, by rfl⟩ : syracuseStep 4131661 = 1549373) (by norm_num)
theorem B5508881 : Blo 2175435 5508881 := bstep (se 2 (by rfl) ⟨2065830, by rfl⟩ : syracuseStep 5508881 = 4131661) B4131661
theorem B3672587 : Blo 2175435 3672587 := bstep (se 1 (by rfl) ⟨2754440, by rfl⟩ : syracuseStep 3672587 = 5508881) B5508881
theorem B2448391 : Blo 2175435 2448391 := bstep (se 1 (by rfl) ⟨1836293, by rfl⟩ : syracuseStep 2448391 = 3672587) B3672587
theorem B3264521 : Blo 2175435 3264521 := bstep (se 2 (by rfl) ⟨1224195, by rfl⟩ : syracuseStep 3264521 = 2448391) B2448391
theorem B2176347 : Blo 2175435 2176347 := bstep (se 1 (by rfl) ⟨1632260, by rfl⟩ : syracuseStep 2176347 = 3264521) B3264521
theorem B11017781 : Blo 2175435 11017781 := bbase (se 5 (by rfl) ⟨516458, by rfl⟩ : syracuseStep 11017781 = 1032917) (by norm_num)
theorem B7345187 : Blo 2175435 7345187 := bstep (se 1 (by rfl) ⟨5508890, by rfl⟩ : syracuseStep 7345187 = 11017781) B11017781
theorem B4896791 : Blo 2175435 4896791 := bstep (se 1 (by rfl) ⟨3672593, by rfl⟩ : syracuseStep 4896791 = 7345187) B7345187
theorem B3264527 : Blo 2175435 3264527 := bstep (se 1 (by rfl) ⟨2448395, by rfl⟩ : syracuseStep 3264527 = 4896791) B4896791
theorem B2176351 : Blo 2175435 2176351 := bstep (se 1 (by rfl) ⟨1632263, by rfl⟩ : syracuseStep 2176351 = 3264527) B3264527
theorem B3264533 : Blo 2175435 3264533 := bbase (se 6 (by rfl) ⟨76512, by rfl⟩ : syracuseStep 3264533 = 153025) (by norm_num)
theorem B2176355 : Blo 2175435 2176355 := bstep (se 1 (by rfl) ⟨1632266, by rfl⟩ : syracuseStep 2176355 = 3264533) B3264533
theorem B10458325 : Blo 2175435 10458325 := bbase (se 7 (by rfl) ⟨122558, by rfl⟩ : syracuseStep 10458325 = 245117) (by norm_num)
theorem B13944433 : Blo 2175435 13944433 := bstep (se 2 (by rfl) ⟨5229162, by rfl⟩ : syracuseStep 13944433 = 10458325) B10458325
theorem B18592577 : Blo 2175435 18592577 := bstep (se 2 (by rfl) ⟨6972216, by rfl⟩ : syracuseStep 18592577 = 13944433) B13944433
theorem B12395051 : Blo 2175435 12395051 := bstep (se 1 (by rfl) ⟨9296288, by rfl⟩ : syracuseStep 12395051 = 18592577) B18592577
theorem B8263367 : Blo 2175435 8263367 := bstep (se 1 (by rfl) ⟨6197525, by rfl⟩ : syracuseStep 8263367 = 12395051) B12395051
theorem B5508911 : Blo 2175435 5508911 := bstep (se 1 (by rfl) ⟨4131683, by rfl⟩ : syracuseStep 5508911 = 8263367) B8263367
theorem B3672607 : Blo 2175435 3672607 := bstep (se 1 (by rfl) ⟨2754455, by rfl⟩ : syracuseStep 3672607 = 5508911) B5508911
theorem B4896809 : Blo 2175435 4896809 := bstep (se 2 (by rfl) ⟨1836303, by rfl⟩ : syracuseStep 4896809 = 3672607) B3672607
theorem B3264539 : Blo 2175435 3264539 := bstep (se 1 (by rfl) ⟨2448404, by rfl⟩ : syracuseStep 3264539 = 4896809) B4896809
theorem B2176359 : Blo 2175435 2176359 := bstep (se 1 (by rfl) ⟨1632269, by rfl⟩ : syracuseStep 2176359 = 3264539) B3264539
theorem B2448409 : Blo 2175435 2448409 := bbase (se 2 (by rfl) ⟨918153, by rfl⟩ : syracuseStep 2448409 = 1836307) (by norm_num)
theorem B3264545 : Blo 2175435 3264545 := bstep (se 2 (by rfl) ⟨1224204, by rfl⟩ : syracuseStep 3264545 = 2448409) B2448409
theorem B2176363 : Blo 2175435 2176363 := bstep (se 1 (by rfl) ⟨1632272, by rfl⟩ : syracuseStep 2176363 = 3264545) B3264545
theorem B8263397 : Blo 2175435 8263397 := bbase (se 4 (by rfl) ⟨774693, by rfl⟩ : syracuseStep 8263397 = 1549387) (by norm_num)
theorem B5508931 : Blo 2175435 5508931 := bstep (se 1 (by rfl) ⟨4131698, by rfl⟩ : syracuseStep 5508931 = 8263397) B8263397
theorem B7345241 : Blo 2175435 7345241 := bstep (se 2 (by rfl) ⟨2754465, by rfl⟩ : syracuseStep 7345241 = 5508931) B5508931
theorem B4896827 : Blo 2175435 4896827 := bstep (se 1 (by rfl) ⟨3672620, by rfl⟩ : syracuseStep 4896827 = 7345241) B7345241
theorem B3264551 : Blo 2175435 3264551 := bstep (se 1 (by rfl) ⟨2448413, by rfl⟩ : syracuseStep 3264551 = 4896827) B4896827
theorem B2176367 : Blo 2175435 2176367 := bstep (se 1 (by rfl) ⟨1632275, by rfl⟩ : syracuseStep 2176367 = 3264551) B3264551
theorem B3264557 : Blo 2175435 3264557 := bbase (se 3 (by rfl) ⟨612104, by rfl⟩ : syracuseStep 3264557 = 1224209) (by norm_num)
theorem B2176371 : Blo 2175435 2176371 := bstep (se 1 (by rfl) ⟨1632278, by rfl⟩ : syracuseStep 2176371 = 3264557) B3264557
theorem B4896845 : Blo 2175435 4896845 := bbase (se 3 (by rfl) ⟨918158, by rfl⟩ : syracuseStep 4896845 = 1836317) (by norm_num)
theorem B3264563 : Blo 2175435 3264563 := bstep (se 1 (by rfl) ⟨2448422, by rfl⟩ : syracuseStep 3264563 = 4896845) B4896845
theorem B2176375 : Blo 2175435 2176375 := bstep (se 1 (by rfl) ⟨1632281, by rfl⟩ : syracuseStep 2176375 = 3264563) B3264563
theorem B2754481 : Blo 2175435 2754481 := bbase (se 2 (by rfl) ⟨1032930, by rfl⟩ : syracuseStep 2754481 = 2065861) (by norm_num)
theorem B3672641 : Blo 2175435 3672641 := bstep (se 2 (by rfl) ⟨1377240, by rfl⟩ : syracuseStep 3672641 = 2754481) B2754481
theorem B2448427 : Blo 2175435 2448427 := bstep (se 1 (by rfl) ⟨1836320, by rfl⟩ : syracuseStep 2448427 = 3672641) B3672641
theorem B3264569 : Blo 2175435 3264569 := bstep (se 2 (by rfl) ⟨1224213, by rfl⟩ : syracuseStep 3264569 = 2448427) B2448427
theorem B2176379 : Blo 2175435 2176379 := bstep (se 1 (by rfl) ⟨1632284, by rfl⟩ : syracuseStep 2176379 = 3264569) B3264569
theorem B6972293 : Blo 2175435 6972293 := bbase (se 4 (by rfl) ⟨653652, by rfl⟩ : syracuseStep 6972293 = 1307305) (by norm_num)
theorem B4648195 : Blo 2175435 4648195 := bstep (se 1 (by rfl) ⟨3486146, by rfl⟩ : syracuseStep 4648195 = 6972293) B6972293
theorem B24790373 : Blo 2175435 24790373 := bstep (se 4 (by rfl) ⟨2324097, by rfl⟩ : syracuseStep 24790373 = 4648195) B4648195
theorem B16526915 : Blo 2175435 16526915 := bstep (se 1 (by rfl) ⟨12395186, by rfl⟩ : syracuseStep 16526915 = 24790373) B24790373
theorem B11017943 : Blo 2175435 11017943 := bstep (se 1 (by rfl) ⟨8263457, by rfl⟩ : syracuseStep 11017943 = 16526915) B16526915
theorem B7345295 : Blo 2175435 7345295 := bstep (se 1 (by rfl) ⟨5508971, by rfl⟩ : syracuseStep 7345295 = 11017943) B11017943
theorem B4896863 : Blo 2175435 4896863 := bstep (se 1 (by rfl) ⟨3672647, by rfl⟩ : syracuseStep 4896863 = 7345295) B7345295
theorem B3264575 : Blo 2175435 3264575 := bstep (se 1 (by rfl) ⟨2448431, by rfl⟩ : syracuseStep 3264575 = 4896863) B4896863
theorem B2176383 : Blo 2175435 2176383 := bstep (se 1 (by rfl) ⟨1632287, by rfl⟩ : syracuseStep 2176383 = 3264575) B3264575
theorem B3264581 : Blo 2175435 3264581 := bbase (se 4 (by rfl) ⟨306054, by rfl⟩ : syracuseStep 3264581 = 612109) (by norm_num)
theorem B2176387 : Blo 2175435 2176387 := bstep (se 1 (by rfl) ⟨1632290, by rfl⟩ : syracuseStep 2176387 = 3264581) B3264581
theorem B3672661 : Blo 2175435 3672661 := bbase (se 8 (by rfl) ⟨21519, by rfl⟩ : syracuseStep 3672661 = 43039) (by norm_num)
theorem B4896881 : Blo 2175435 4896881 := bstep (se 2 (by rfl) ⟨1836330, by rfl⟩ : syracuseStep 4896881 = 3672661) B3672661
theorem B3264587 : Blo 2175435 3264587 := bstep (se 1 (by rfl) ⟨2448440, by rfl⟩ : syracuseStep 3264587 = 4896881) B4896881
theorem B2176391 : Blo 2175435 2176391 := bstep (se 1 (by rfl) ⟨1632293, by rfl⟩ : syracuseStep 2176391 = 3264587) B3264587
theorem B2448445 : Blo 2175435 2448445 := bbase (se 3 (by rfl) ⟨459083, by rfl⟩ : syracuseStep 2448445 = 918167) (by norm_num)
theorem B3264593 : Blo 2175435 3264593 := bstep (se 2 (by rfl) ⟨1224222, by rfl⟩ : syracuseStep 3264593 = 2448445) B2448445
theorem B2176395 : Blo 2175435 2176395 := bstep (se 1 (by rfl) ⟨1632296, by rfl⟩ : syracuseStep 2176395 = 3264593) B3264593
theorem B7345349 : Blo 2175435 7345349 := bbase (se 4 (by rfl) ⟨688626, by rfl⟩ : syracuseStep 7345349 = 1377253) (by norm_num)
theorem B4896899 : Blo 2175435 4896899 := bstep (se 1 (by rfl) ⟨3672674, by rfl⟩ : syracuseStep 4896899 = 7345349) B7345349
theorem B3264599 : Blo 2175435 3264599 := bstep (se 1 (by rfl) ⟨2448449, by rfl⟩ : syracuseStep 3264599 = 4896899) B4896899
theorem B2176399 : Blo 2175435 2176399 := bstep (se 1 (by rfl) ⟨1632299, by rfl⟩ : syracuseStep 2176399 = 3264599) B3264599
theorem B3264605 : Blo 2175435 3264605 := bbase (se 3 (by rfl) ⟨612113, by rfl⟩ : syracuseStep 3264605 = 1224227) (by norm_num)
theorem B2176403 : Blo 2175435 2176403 := bstep (se 1 (by rfl) ⟨1632302, by rfl⟩ : syracuseStep 2176403 = 3264605) B3264605
theorem B4896917 : Blo 2175435 4896917 := bbase (se 6 (by rfl) ⟨114771, by rfl⟩ : syracuseStep 4896917 = 229543) (by norm_num)
theorem B3264611 : Blo 2175435 3264611 := bstep (se 1 (by rfl) ⟨2448458, by rfl⟩ : syracuseStep 3264611 = 4896917) B4896917
theorem B2176407 : Blo 2175435 2176407 := bstep (se 1 (by rfl) ⟨1632305, by rfl⟩ : syracuseStep 2176407 = 3264611) B3264611
theorem B3098837 : Blo 2175435 3098837 := bbase (se 7 (by rfl) ⟨36314, by rfl⟩ : syracuseStep 3098837 = 72629) (by norm_num)
theorem B8263565 : Blo 2175435 8263565 := bstep (se 3 (by rfl) ⟨1549418, by rfl⟩ : syracuseStep 8263565 = 3098837) B3098837
theorem B5509043 : Blo 2175435 5509043 := bstep (se 1 (by rfl) ⟨4131782, by rfl⟩ : syracuseStep 5509043 = 8263565) B8263565
theorem B3672695 : Blo 2175435 3672695 := bstep (se 1 (by rfl) ⟨2754521, by rfl⟩ : syracuseStep 3672695 = 5509043) B5509043
theorem B2448463 : Blo 2175435 2448463 := bstep (se 1 (by rfl) ⟨1836347, by rfl⟩ : syracuseStep 2448463 = 3672695) B3672695
theorem B3264617 : Blo 2175435 3264617 := bstep (se 2 (by rfl) ⟨1224231, by rfl⟩ : syracuseStep 3264617 = 2448463) B2448463
theorem B2176411 : Blo 2175435 2176411 := bstep (se 1 (by rfl) ⟨1632308, by rfl⟩ : syracuseStep 2176411 = 3264617) B3264617
theorem B7445621 : Blo 2175435 7445621 := bbase (se 5 (by rfl) ⟨349013, by rfl⟩ : syracuseStep 7445621 = 698027) (by norm_num)
theorem B19854989 : Blo 2175435 19854989 := bstep (se 3 (by rfl) ⟨3722810, by rfl⟩ : syracuseStep 19854989 = 7445621) B7445621
theorem B13236659 : Blo 2175435 13236659 := bstep (se 1 (by rfl) ⟨9927494, by rfl⟩ : syracuseStep 13236659 = 19854989) B19854989
theorem B8824439 : Blo 2175435 8824439 := bstep (se 1 (by rfl) ⟨6618329, by rfl⟩ : syracuseStep 8824439 = 13236659) B13236659
theorem B5882959 : Blo 2175435 5882959 := bstep (se 1 (by rfl) ⟨4412219, by rfl⟩ : syracuseStep 5882959 = 8824439) B8824439
theorem B31375781 : Blo 2175435 31375781 := bstep (se 4 (by rfl) ⟨2941479, by rfl⟩ : syracuseStep 31375781 = 5882959) B5882959
theorem B20917187 : Blo 2175435 20917187 := bstep (se 1 (by rfl) ⟨15687890, by rfl⟩ : syracuseStep 20917187 = 31375781) B31375781
theorem B13944791 : Blo 2175435 13944791 := bstep (se 1 (by rfl) ⟨10458593, by rfl⟩ : syracuseStep 13944791 = 20917187) B20917187
theorem B9296527 : Blo 2175435 9296527 := bstep (se 1 (by rfl) ⟨6972395, by rfl⟩ : syracuseStep 9296527 = 13944791) B13944791
theorem B12395369 : Blo 2175435 12395369 := bstep (se 2 (by rfl) ⟨4648263, by rfl⟩ : syracuseStep 12395369 = 9296527) B9296527
theorem B8263579 : Blo 2175435 8263579 := bstep (se 1 (by rfl) ⟨6197684, by rfl⟩ : syracuseStep 8263579 = 12395369) B12395369
theorem B11018105 : Blo 2175435 11018105 := bstep (se 2 (by rfl) ⟨4131789, by rfl⟩ : syracuseStep 11018105 = 8263579) B8263579
theorem B7345403 : Blo 2175435 7345403 := bstep (se 1 (by rfl) ⟨5509052, by rfl⟩ : syracuseStep 7345403 = 11018105) B11018105
theorem B4896935 : Blo 2175435 4896935 := bstep (se 1 (by rfl) ⟨3672701, by rfl⟩ : syracuseStep 4896935 = 7345403) B7345403
theorem B3264623 : Blo 2175435 3264623 := bstep (se 1 (by rfl) ⟨2448467, by rfl⟩ : syracuseStep 3264623 = 4896935) B4896935
theorem B2176415 : Blo 2175435 2176415 := bstep (se 1 (by rfl) ⟨1632311, by rfl⟩ : syracuseStep 2176415 = 3264623) B3264623
theorem B3264629 : Blo 2175435 3264629 := bbase (se 5 (by rfl) ⟨153029, by rfl⟩ : syracuseStep 3264629 = 306059) (by norm_num)
theorem B2176419 : Blo 2175435 2176419 := bstep (se 1 (by rfl) ⟨1632314, by rfl⟩ : syracuseStep 2176419 = 3264629) B3264629
theorem B4131805 : Blo 2175435 4131805 := bbase (se 3 (by rfl) ⟨774713, by rfl⟩ : syracuseStep 4131805 = 1549427) (by norm_num)
theorem B5509073 : Blo 2175435 5509073 := bstep (se 2 (by rfl) ⟨2065902, by rfl⟩ : syracuseStep 5509073 = 4131805) B4131805
theorem B3672715 : Blo 2175435 3672715 := bstep (se 1 (by rfl) ⟨2754536, by rfl⟩ : syracuseStep 3672715 = 5509073) B5509073
theorem B4896953 : Blo 2175435 4896953 := bstep (se 2 (by rfl) ⟨1836357, by rfl⟩ : syracuseStep 4896953 = 3672715) B3672715
theorem B3264635 : Blo 2175435 3264635 := bstep (se 1 (by rfl) ⟨2448476, by rfl⟩ : syracuseStep 3264635 = 4896953) B4896953
theorem B2176423 : Blo 2175435 2176423 := bstep (se 1 (by rfl) ⟨1632317, by rfl⟩ : syracuseStep 2176423 = 3264635) B3264635
theorem B2448481 : Blo 2175435 2448481 := bbase (se 2 (by rfl) ⟨918180, by rfl⟩ : syracuseStep 2448481 = 1836361) (by norm_num)
theorem B3264641 : Blo 2175435 3264641 := bstep (se 2 (by rfl) ⟨1224240, by rfl⟩ : syracuseStep 3264641 = 2448481) B2448481
theorem B2176427 : Blo 2175435 2176427 := bstep (se 1 (by rfl) ⟨1632320, by rfl⟩ : syracuseStep 2176427 = 3264641) B3264641
theorem B5509093 : Blo 2175435 5509093 := bbase (se 4 (by rfl) ⟨516477, by rfl⟩ : syracuseStep 5509093 = 1032955) (by norm_num)
theorem B7345457 : Blo 2175435 7345457 := bstep (se 2 (by rfl) ⟨2754546, by rfl⟩ : syracuseStep 7345457 = 5509093) B5509093
theorem B4896971 : Blo 2175435 4896971 := bstep (se 1 (by rfl) ⟨3672728, by rfl⟩ : syracuseStep 4896971 = 7345457) B7345457
theorem B3264647 : Blo 2175435 3264647 := bstep (se 1 (by rfl) ⟨2448485, by rfl⟩ : syracuseStep 3264647 = 4896971) B4896971
theorem B2176431 : Blo 2175435 2176431 := bstep (se 1 (by rfl) ⟨1632323, by rfl⟩ : syracuseStep 2176431 = 3264647) B3264647
theorem B3264653 : Blo 2175435 3264653 := bbase (se 3 (by rfl) ⟨612122, by rfl⟩ : syracuseStep 3264653 = 1224245) (by norm_num)
theorem B2176435 : Blo 2175435 2176435 := bstep (se 1 (by rfl) ⟨1632326, by rfl⟩ : syracuseStep 2176435 = 3264653) B3264653
theorem B4896989 : Blo 2175435 4896989 := bbase (se 3 (by rfl) ⟨918185, by rfl⟩ : syracuseStep 4896989 = 1836371) (by norm_num)
theorem B3264659 : Blo 2175435 3264659 := bstep (se 1 (by rfl) ⟨2448494, by rfl⟩ : syracuseStep 3264659 = 4896989) B4896989
theorem B2176439 : Blo 2175435 2176439 := bstep (se 1 (by rfl) ⟨1632329, by rfl⟩ : syracuseStep 2176439 = 3264659) B3264659
theorem B3672749 : Blo 2175435 3672749 := bbase (se 3 (by rfl) ⟨688640, by rfl⟩ : syracuseStep 3672749 = 1377281) (by norm_num)
theorem B2448499 : Blo 2175435 2448499 := bstep (se 1 (by rfl) ⟨1836374, by rfl⟩ : syracuseStep 2448499 = 3672749) B3672749
theorem B3264665 : Blo 2175435 3264665 := bstep (se 2 (by rfl) ⟨1224249, by rfl⟩ : syracuseStep 3264665 = 2448499) B2448499
theorem B2176443 : Blo 2175435 2176443 := bstep (se 1 (by rfl) ⟨1632332, by rfl⟩ : syracuseStep 2176443 = 3264665) B3264665
theorem B22641941 : Blo 2175435 22641941 := bbase (se 6 (by rfl) ⟨530670, by rfl⟩ : syracuseStep 22641941 = 1061341) (by norm_num)
theorem B60378509 : Blo 2175435 60378509 := bstep (se 3 (by rfl) ⟨11320970, by rfl⟩ : syracuseStep 60378509 = 22641941) B22641941
theorem B40252339 : Blo 2175435 40252339 := bstep (se 1 (by rfl) ⟨30189254, by rfl⟩ : syracuseStep 40252339 = 60378509) B60378509
theorem B53669785 : Blo 2175435 53669785 := bstep (se 2 (by rfl) ⟨20126169, by rfl⟩ : syracuseStep 53669785 = 40252339) B40252339
theorem B71559713 : Blo 2175435 71559713 := bstep (se 2 (by rfl) ⟨26834892, by rfl⟩ : syracuseStep 71559713 = 53669785) B53669785
theorem B190825901 : Blo 2175435 190825901 := bstep (se 3 (by rfl) ⟨35779856, by rfl⟩ : syracuseStep 190825901 = 71559713) B71559713
theorem B127217267 : Blo 2175435 127217267 := bstep (se 1 (by rfl) ⟨95412950, by rfl⟩ : syracuseStep 127217267 = 190825901) B190825901
theorem B84811511 : Blo 2175435 84811511 := bstep (se 1 (by rfl) ⟨63608633, by rfl⟩ : syracuseStep 84811511 = 127217267) B127217267
theorem B56541007 : Blo 2175435 56541007 := bstep (se 1 (by rfl) ⟨42405755, by rfl⟩ : syracuseStep 56541007 = 84811511) B84811511
theorem B75388009 : Blo 2175435 75388009 := bstep (se 2 (by rfl) ⟨28270503, by rfl⟩ : syracuseStep 75388009 = 56541007) B56541007
theorem B100517345 : Blo 2175435 100517345 := bstep (se 2 (by rfl) ⟨37694004, by rfl⟩ : syracuseStep 100517345 = 75388009) B75388009
theorem B67011563 : Blo 2175435 67011563 := bstep (se 1 (by rfl) ⟨50258672, by rfl⟩ : syracuseStep 67011563 = 100517345) B100517345
theorem B178697501 : Blo 2175435 178697501 := bstep (se 3 (by rfl) ⟨33505781, by rfl⟩ : syracuseStep 178697501 = 67011563) B67011563
theorem B119131667 : Blo 2175435 119131667 := bstep (se 1 (by rfl) ⟨89348750, by rfl⟩ : syracuseStep 119131667 = 178697501) B178697501
theorem B79421111 : Blo 2175435 79421111 := bstep (se 1 (by rfl) ⟨59565833, by rfl⟩ : syracuseStep 79421111 = 119131667) B119131667
theorem B52947407 : Blo 2175435 52947407 := bstep (se 1 (by rfl) ⟨39710555, by rfl⟩ : syracuseStep 52947407 = 79421111) B79421111
theorem B35298271 : Blo 2175435 35298271 := bstep (se 1 (by rfl) ⟨26473703, by rfl⟩ : syracuseStep 35298271 = 52947407) B52947407
theorem B47064361 : Blo 2175435 47064361 := bstep (se 2 (by rfl) ⟨17649135, by rfl⟩ : syracuseStep 47064361 = 35298271) B35298271
theorem B62752481 : Blo 2175435 62752481 := bstep (se 2 (by rfl) ⟨23532180, by rfl⟩ : syracuseStep 62752481 = 47064361) B47064361
theorem B41834987 : Blo 2175435 41834987 := bstep (se 1 (by rfl) ⟨31376240, by rfl⟩ : syracuseStep 41834987 = 62752481) B62752481
theorem B27889991 : Blo 2175435 27889991 := bstep (se 1 (by rfl) ⟨20917493, by rfl⟩ : syracuseStep 27889991 = 41834987) B41834987
theorem B18593327 : Blo 2175435 18593327 := bstep (se 1 (by rfl) ⟨13944995, by rfl⟩ : syracuseStep 18593327 = 27889991) B27889991
theorem B12395551 : Blo 2175435 12395551 := bstep (se 1 (by rfl) ⟨9296663, by rfl⟩ : syracuseStep 12395551 = 18593327) B18593327
theorem B16527401 : Blo 2175435 16527401 := bstep (se 2 (by rfl) ⟨6197775, by rfl⟩ : syracuseStep 16527401 = 12395551) B12395551
theorem B11018267 : Blo 2175435 11018267 := bstep (se 1 (by rfl) ⟨8263700, by rfl⟩ : syracuseStep 11018267 = 16527401) B16527401
theorem B7345511 : Blo 2175435 7345511 := bstep (se 1 (by rfl) ⟨5509133, by rfl⟩ : syracuseStep 7345511 = 11018267) B11018267
theorem B4897007 : Blo 2175435 4897007 := bstep (se 1 (by rfl) ⟨3672755, by rfl⟩ : syracuseStep 4897007 = 7345511) B7345511
theorem B3264671 : Blo 2175435 3264671 := bstep (se 1 (by rfl) ⟨2448503, by rfl⟩ : syracuseStep 3264671 = 4897007) B4897007
theorem B2176447 : Blo 2175435 2176447 := bstep (se 1 (by rfl) ⟨1632335, by rfl⟩ : syracuseStep 2176447 = 3264671) B3264671
theorem B3264677 : Blo 2175435 3264677 := bbase (se 4 (by rfl) ⟨306063, by rfl⟩ : syracuseStep 3264677 = 612127) (by norm_num)
theorem B2176451 : Blo 2175435 2176451 := bstep (se 1 (by rfl) ⟨1632338, by rfl⟩ : syracuseStep 2176451 = 3264677) B3264677
theorem B2754577 : Blo 2175435 2754577 := bbase (se 2 (by rfl) ⟨1032966, by rfl⟩ : syracuseStep 2754577 = 2065933) (by norm_num)
theorem B3672769 : Blo 2175435 3672769 := bstep (se 2 (by rfl) ⟨1377288, by rfl⟩ : syracuseStep 3672769 = 2754577) B2754577
theorem B4897025 : Blo 2175435 4897025 := bstep (se 2 (by rfl) ⟨1836384, by rfl⟩ : syracuseStep 4897025 = 3672769) B3672769
theorem B3264683 : Blo 2175435 3264683 := bstep (se 1 (by rfl) ⟨2448512, by rfl⟩ : syracuseStep 3264683 = 4897025) B4897025
theorem B2176455 : Blo 2175435 2176455 := bstep (se 1 (by rfl) ⟨1632341, by rfl⟩ : syracuseStep 2176455 = 3264683) B3264683
theorem B2448517 : Blo 2175435 2448517 := bbase (se 4 (by rfl) ⟨229548, by rfl⟩ : syracuseStep 2448517 = 459097) (by norm_num)
theorem B3264689 : Blo 2175435 3264689 := bstep (se 2 (by rfl) ⟨1224258, by rfl⟩ : syracuseStep 3264689 = 2448517) B2448517
theorem B2176459 : Blo 2175435 2176459 := bstep (se 1 (by rfl) ⟨1632344, by rfl⟩ : syracuseStep 2176459 = 3264689) B3264689
theorem B5300765 : Blo 2175435 5300765 := bbase (se 3 (by rfl) ⟨993893, by rfl⟩ : syracuseStep 5300765 = 1987787) (by norm_num)
theorem B3533843 : Blo 2175435 3533843 := bstep (se 1 (by rfl) ⟨2650382, by rfl⟩ : syracuseStep 3533843 = 5300765) B5300765
theorem B2355895 : Blo 2175435 2355895 := bstep (se 1 (by rfl) ⟨1766921, by rfl⟩ : syracuseStep 2355895 = 3533843) B3533843
theorem B3141193 : Blo 2175435 3141193 := bstep (se 2 (by rfl) ⟨1177947, by rfl⟩ : syracuseStep 3141193 = 2355895) B2355895
theorem B4188257 : Blo 2175435 4188257 := bstep (se 2 (by rfl) ⟨1570596, by rfl⟩ : syracuseStep 4188257 = 3141193) B3141193
theorem B2792171 : Blo 2175435 2792171 := bstep (se 1 (by rfl) ⟨2094128, by rfl⟩ : syracuseStep 2792171 = 4188257) B4188257
theorem B7445789 : Blo 2175435 7445789 := bstep (se 3 (by rfl) ⟨1396085, by rfl⟩ : syracuseStep 7445789 = 2792171) B2792171
theorem B4963859 : Blo 2175435 4963859 := bstep (se 1 (by rfl) ⟨3722894, by rfl⟩ : syracuseStep 4963859 = 7445789) B7445789
theorem B3309239 : Blo 2175435 3309239 := bstep (se 1 (by rfl) ⟨2481929, by rfl⟩ : syracuseStep 3309239 = 4963859) B4963859
theorem B2206159 : Blo 2175435 2206159 := bstep (se 1 (by rfl) ⟨1654619, by rfl⟩ : syracuseStep 2206159 = 3309239) B3309239
theorem B11766181 : Blo 2175435 11766181 := bstep (se 4 (by rfl) ⟨1103079, by rfl⟩ : syracuseStep 11766181 = 2206159) B2206159
theorem B15688241 : Blo 2175435 15688241 := bstep (se 2 (by rfl) ⟨5883090, by rfl⟩ : syracuseStep 15688241 = 11766181) B11766181
theorem B10458827 : Blo 2175435 10458827 := bstep (se 1 (by rfl) ⟨7844120, by rfl⟩ : syracuseStep 10458827 = 15688241) B15688241
theorem B6972551 : Blo 2175435 6972551 := bstep (se 1 (by rfl) ⟨5229413, by rfl⟩ : syracuseStep 6972551 = 10458827) B10458827
theorem B4648367 : Blo 2175435 4648367 := bstep (se 1 (by rfl) ⟨3486275, by rfl⟩ : syracuseStep 4648367 = 6972551) B6972551
theorem B3098911 : Blo 2175435 3098911 := bstep (se 1 (by rfl) ⟨2324183, by rfl⟩ : syracuseStep 3098911 = 4648367) B4648367
theorem B4131881 : Blo 2175435 4131881 := bstep (se 2 (by rfl) ⟨1549455, by rfl⟩ : syracuseStep 4131881 = 3098911) B3098911
theorem B2754587 : Blo 2175435 2754587 := bstep (se 1 (by rfl) ⟨2065940, by rfl⟩ : syracuseStep 2754587 = 4131881) B4131881
theorem B7345565 : Blo 2175435 7345565 := bstep (se 3 (by rfl) ⟨1377293, by rfl⟩ : syracuseStep 7345565 = 2754587) B2754587
theorem B4897043 : Blo 2175435 4897043 := bstep (se 1 (by rfl) ⟨3672782, by rfl⟩ : syracuseStep 4897043 = 7345565) B7345565
theorem B3264695 : Blo 2175435 3264695 := bstep (se 1 (by rfl) ⟨2448521, by rfl⟩ : syracuseStep 3264695 = 4897043) B4897043
theorem B2176463 : Blo 2175435 2176463 := bstep (se 1 (by rfl) ⟨1632347, by rfl⟩ : syracuseStep 2176463 = 3264695) B3264695
theorem B3264701 : Blo 2175435 3264701 := bbase (se 3 (by rfl) ⟨612131, by rfl⟩ : syracuseStep 3264701 = 1224263) (by norm_num)
theorem B2176467 : Blo 2175435 2176467 := bstep (se 1 (by rfl) ⟨1632350, by rfl⟩ : syracuseStep 2176467 = 3264701) B3264701
theorem B4897061 : Blo 2175435 4897061 := bbase (se 4 (by rfl) ⟨459099, by rfl⟩ : syracuseStep 4897061 = 918199) (by norm_num)
theorem B3264707 : Blo 2175435 3264707 := bstep (se 1 (by rfl) ⟨2448530, by rfl⟩ : syracuseStep 3264707 = 4897061) B4897061
theorem B2176471 : Blo 2175435 2176471 := bstep (se 1 (by rfl) ⟨1632353, by rfl⟩ : syracuseStep 2176471 = 3264707) B3264707
theorem B5509205 : Blo 2175435 5509205 := bbase (se 8 (by rfl) ⟨32280, by rfl⟩ : syracuseStep 5509205 = 64561) (by norm_num)
theorem B3672803 : Blo 2175435 3672803 := bstep (se 1 (by rfl) ⟨2754602, by rfl⟩ : syracuseStep 3672803 = 5509205) B5509205
theorem B2448535 : Blo 2175435 2448535 := bstep (se 1 (by rfl) ⟨1836401, by rfl⟩ : syracuseStep 2448535 = 3672803) B3672803
theorem B3264713 : Blo 2175435 3264713 := bstep (se 2 (by rfl) ⟨1224267, by rfl⟩ : syracuseStep 3264713 = 2448535) B2448535
theorem B2176475 : Blo 2175435 2176475 := bstep (se 1 (by rfl) ⟨1632356, by rfl⟩ : syracuseStep 2176475 = 3264713) B3264713
theorem B19104437 : Blo 2175435 19104437 := bbase (se 5 (by rfl) ⟨895520, by rfl⟩ : syracuseStep 19104437 = 1791041) (by norm_num)
theorem B12736291 : Blo 2175435 12736291 := bstep (se 1 (by rfl) ⟨9552218, by rfl⟩ : syracuseStep 12736291 = 19104437) B19104437
theorem B16981721 : Blo 2175435 16981721 := bstep (se 2 (by rfl) ⟨6368145, by rfl⟩ : syracuseStep 16981721 = 12736291) B12736291
theorem B11321147 : Blo 2175435 11321147 := bstep (se 1 (by rfl) ⟨8490860, by rfl⟩ : syracuseStep 11321147 = 16981721) B16981721
theorem B30189725 : Blo 2175435 30189725 := bstep (se 3 (by rfl) ⟨5660573, by rfl⟩ : syracuseStep 30189725 = 11321147) B11321147
theorem B20126483 : Blo 2175435 20126483 := bstep (se 1 (by rfl) ⟨15094862, by rfl⟩ : syracuseStep 20126483 = 30189725) B30189725
theorem B13417655 : Blo 2175435 13417655 := bstep (se 1 (by rfl) ⟨10063241, by rfl⟩ : syracuseStep 13417655 = 20126483) B20126483
theorem B35780413 : Blo 2175435 35780413 := bstep (se 3 (by rfl) ⟨6708827, by rfl⟩ : syracuseStep 35780413 = 13417655) B13417655
theorem B47707217 : Blo 2175435 47707217 := bstep (se 2 (by rfl) ⟨17890206, by rfl⟩ : syracuseStep 47707217 = 35780413) B35780413
theorem B31804811 : Blo 2175435 31804811 := bstep (se 1 (by rfl) ⟨23853608, by rfl⟩ : syracuseStep 31804811 = 47707217) B47707217
theorem B21203207 : Blo 2175435 21203207 := bstep (se 1 (by rfl) ⟨15902405, by rfl⟩ : syracuseStep 21203207 = 31804811) B31804811
theorem B14135471 : Blo 2175435 14135471 := bstep (se 1 (by rfl) ⟨10601603, by rfl⟩ : syracuseStep 14135471 = 21203207) B21203207
theorem B9423647 : Blo 2175435 9423647 := bstep (se 1 (by rfl) ⟨7067735, by rfl⟩ : syracuseStep 9423647 = 14135471) B14135471
theorem B6282431 : Blo 2175435 6282431 := bstep (se 1 (by rfl) ⟨4711823, by rfl⟩ : syracuseStep 6282431 = 9423647) B9423647
theorem B4188287 : Blo 2175435 4188287 := bstep (se 1 (by rfl) ⟨3141215, by rfl⟩ : syracuseStep 4188287 = 6282431) B6282431
theorem B11168765 : Blo 2175435 11168765 := bstep (se 3 (by rfl) ⟨2094143, by rfl⟩ : syracuseStep 11168765 = 4188287) B4188287
theorem B7445843 : Blo 2175435 7445843 := bstep (se 1 (by rfl) ⟨5584382, by rfl⟩ : syracuseStep 7445843 = 11168765) B11168765
theorem B4963895 : Blo 2175435 4963895 := bstep (se 1 (by rfl) ⟨3722921, by rfl⟩ : syracuseStep 4963895 = 7445843) B7445843
theorem B3309263 : Blo 2175435 3309263 := bstep (se 1 (by rfl) ⟨2481947, by rfl⟩ : syracuseStep 3309263 = 4963895) B4963895
theorem B2206175 : Blo 2175435 2206175 := bstep (se 1 (by rfl) ⟨1654631, by rfl⟩ : syracuseStep 2206175 = 3309263) B3309263
theorem B5883133 : Blo 2175435 5883133 := bstep (se 3 (by rfl) ⟨1103087, by rfl⟩ : syracuseStep 5883133 = 2206175) B2206175
theorem B7844177 : Blo 2175435 7844177 := bstep (se 2 (by rfl) ⟨2941566, by rfl⟩ : syracuseStep 7844177 = 5883133) B5883133
theorem B5229451 : Blo 2175435 5229451 := bstep (se 1 (by rfl) ⟨3922088, by rfl⟩ : syracuseStep 5229451 = 7844177) B7844177
theorem B6972601 : Blo 2175435 6972601 := bstep (se 2 (by rfl) ⟨2614725, by rfl⟩ : syracuseStep 6972601 = 5229451) B5229451
theorem B9296801 : Blo 2175435 9296801 := bstep (se 2 (by rfl) ⟨3486300, by rfl⟩ : syracuseStep 9296801 = 6972601) B6972601
theorem B6197867 : Blo 2175435 6197867 := bstep (se 1 (by rfl) ⟨4648400, by rfl⟩ : syracuseStep 6197867 = 9296801) B9296801
theorem B4131911 : Blo 2175435 4131911 := bstep (se 1 (by rfl) ⟨3098933, by rfl⟩ : syracuseStep 4131911 = 6197867) B6197867
theorem B11018429 : Blo 2175435 11018429 := bstep (se 3 (by rfl) ⟨2065955, by rfl⟩ : syracuseStep 11018429 = 4131911) B4131911
theorem B7345619 : Blo 2175435 7345619 := bstep (se 1 (by rfl) ⟨5509214, by rfl⟩ : syracuseStep 7345619 = 11018429) B11018429
theorem B4897079 : Blo 2175435 4897079 := bstep (se 1 (by rfl) ⟨3672809, by rfl⟩ : syracuseStep 4897079 = 7345619) B7345619
theorem B3264719 : Blo 2175435 3264719 := bstep (se 1 (by rfl) ⟨2448539, by rfl⟩ : syracuseStep 3264719 = 4897079) B4897079
theorem B2176479 : Blo 2175435 2176479 := bstep (se 1 (by rfl) ⟨1632359, by rfl⟩ : syracuseStep 2176479 = 3264719) B3264719
theorem B3264725 : Blo 2175435 3264725 := bbase (se 7 (by rfl) ⟨38258, by rfl⟩ : syracuseStep 3264725 = 76517) (by norm_num)
theorem B2176483 : Blo 2175435 2176483 := bstep (se 1 (by rfl) ⟨1632362, by rfl⟩ : syracuseStep 2176483 = 3264725) B3264725
theorem B2324209 : Blo 2175435 2324209 := bbase (se 2 (by rfl) ⟨871578, by rfl⟩ : syracuseStep 2324209 = 1743157) (by norm_num)
theorem B3098945 : Blo 2175435 3098945 := bstep (se 2 (by rfl) ⟨1162104, by rfl⟩ : syracuseStep 3098945 = 2324209) B2324209
theorem B8263853 : Blo 2175435 8263853 := bstep (se 3 (by rfl) ⟨1549472, by rfl⟩ : syracuseStep 8263853 = 3098945) B3098945
theorem B5509235 : Blo 2175435 5509235 := bstep (se 1 (by rfl) ⟨4131926, by rfl⟩ : syracuseStep 5509235 = 8263853) B8263853
theorem B3672823 : Blo 2175435 3672823 := bstep (se 1 (by rfl) ⟨2754617, by rfl⟩ : syracuseStep 3672823 = 5509235) B5509235
theorem B4897097 : Blo 2175435 4897097 := bstep (se 2 (by rfl) ⟨1836411, by rfl⟩ : syracuseStep 4897097 = 3672823) B3672823
theorem B3264731 : Blo 2175435 3264731 := bstep (se 1 (by rfl) ⟨2448548, by rfl⟩ : syracuseStep 3264731 = 4897097) B4897097
theorem B2176487 : Blo 2175435 2176487 := bstep (se 1 (by rfl) ⟨1632365, by rfl⟩ : syracuseStep 2176487 = 3264731) B3264731
theorem B2448553 : Blo 2175435 2448553 := bbase (se 2 (by rfl) ⟨918207, by rfl⟩ : syracuseStep 2448553 = 1836415) (by norm_num)
theorem B3264737 : Blo 2175435 3264737 := bstep (se 2 (by rfl) ⟨1224276, by rfl⟩ : syracuseStep 3264737 = 2448553) B2448553
theorem B2176491 : Blo 2175435 2176491 := bstep (se 1 (by rfl) ⟨1632368, by rfl⟩ : syracuseStep 2176491 = 3264737) B3264737
theorem B9296869 : Blo 2175435 9296869 := bbase (se 4 (by rfl) ⟨871581, by rfl⟩ : syracuseStep 9296869 = 1743163) (by norm_num)
theorem B12395825 : Blo 2175435 12395825 := bstep (se 2 (by rfl) ⟨4648434, by rfl⟩ : syracuseStep 12395825 = 9296869) B9296869
theorem B8263883 : Blo 2175435 8263883 := bstep (se 1 (by rfl) ⟨6197912, by rfl⟩ : syracuseStep 8263883 = 12395825) B12395825
theorem B5509255 : Blo 2175435 5509255 := bstep (se 1 (by rfl) ⟨4131941, by rfl⟩ : syracuseStep 5509255 = 8263883) B8263883
theorem B7345673 : Blo 2175435 7345673 := bstep (se 2 (by rfl) ⟨2754627, by rfl⟩ : syracuseStep 7345673 = 5509255) B5509255
theorem B4897115 : Blo 2175435 4897115 := bstep (se 1 (by rfl) ⟨3672836, by rfl⟩ : syracuseStep 4897115 = 7345673) B7345673
theorem B3264743 : Blo 2175435 3264743 := bstep (se 1 (by rfl) ⟨2448557, by rfl⟩ : syracuseStep 3264743 = 4897115) B4897115
theorem B2176495 : Blo 2175435 2176495 := bstep (se 1 (by rfl) ⟨1632371, by rfl⟩ : syracuseStep 2176495 = 3264743) B3264743
theorem B3264749 : Blo 2175435 3264749 := bbase (se 3 (by rfl) ⟨612140, by rfl⟩ : syracuseStep 3264749 = 1224281) (by norm_num)
theorem B2176499 : Blo 2175435 2176499 := bstep (se 1 (by rfl) ⟨1632374, by rfl⟩ : syracuseStep 2176499 = 3264749) B3264749
theorem B4897133 : Blo 2175435 4897133 := bbase (se 3 (by rfl) ⟨918212, by rfl⟩ : syracuseStep 4897133 = 1836425) (by norm_num)
theorem B3264755 : Blo 2175435 3264755 := bstep (se 1 (by rfl) ⟨2448566, by rfl⟩ : syracuseStep 3264755 = 4897133) B4897133
theorem B2176503 : Blo 2175435 2176503 := bstep (se 1 (by rfl) ⟨1632377, by rfl⟩ : syracuseStep 2176503 = 3264755) B3264755
theorem B4131965 : Blo 2175435 4131965 := bbase (se 3 (by rfl) ⟨774743, by rfl⟩ : syracuseStep 4131965 = 1549487) (by norm_num)
theorem B2754643 : Blo 2175435 2754643 := bstep (se 1 (by rfl) ⟨2065982, by rfl⟩ : syracuseStep 2754643 = 4131965) B4131965
theorem B3672857 : Blo 2175435 3672857 := bstep (se 2 (by rfl) ⟨1377321, by rfl⟩ : syracuseStep 3672857 = 2754643) B2754643
theorem B2448571 : Blo 2175435 2448571 := bstep (se 1 (by rfl) ⟨1836428, by rfl⟩ : syracuseStep 2448571 = 3672857) B3672857
theorem B3264761 : Blo 2175435 3264761 := bstep (se 2 (by rfl) ⟨1224285, by rfl⟩ : syracuseStep 3264761 = 2448571) B2448571
theorem B2176507 : Blo 2175435 2176507 := bstep (se 1 (by rfl) ⟨1632380, by rfl⟩ : syracuseStep 2176507 = 3264761) B3264761
theorem B3582133 : Blo 2175435 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B19104709 : Blo 2175435 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B25472945 : Blo 2175435 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B67927853 : Blo 2175435 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B181140941 : Blo 2175435 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B120760627 : Blo 2175435 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B161014169 : Blo 2175435 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B107342779 : Blo 2175435 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B143123705 : Blo 2175435 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B95415803 : Blo 2175435 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B63610535 : Blo 2175435 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B42407023 : Blo 2175435 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B56542697 : Blo 2175435 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B37695131 : Blo 2175435 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B25130087 : Blo 2175435 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B16753391 : Blo 2175435 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B11168927 : Blo 2175435 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B7445951 : Blo 2175435 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B4963967 : Blo 2175435 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B3309311 : Blo 2175435 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B2206207 : Blo 2175435 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B11766437 : Blo 2175435 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B7844291 : Blo 2175435 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B5229527 : Blo 2175435 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B55781621 : Blo 2175435 55781621 := bstep (se 5 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 55781621 = 5229527) B5229527
theorem B37187747 : Blo 2175435 37187747 := bstep (se 1 (by rfl) ⟨27890810, by rfl⟩ : syracuseStep 37187747 = 55781621) B55781621
theorem B24791831 : Blo 2175435 24791831 := bstep (se 1 (by rfl) ⟨18593873, by rfl⟩ : syracuseStep 24791831 = 37187747) B37187747
theorem B16527887 : Blo 2175435 16527887 := bstep (se 1 (by rfl) ⟨12395915, by rfl⟩ : syracuseStep 16527887 = 24791831) B24791831
theorem B11018591 : Blo 2175435 11018591 := bstep (se 1 (by rfl) ⟨8263943, by rfl⟩ : syracuseStep 11018591 = 16527887) B16527887
theorem B7345727 : Blo 2175435 7345727 := bstep (se 1 (by rfl) ⟨5509295, by rfl⟩ : syracuseStep 7345727 = 11018591) B11018591
theorem B4897151 : Blo 2175435 4897151 := bstep (se 1 (by rfl) ⟨3672863, by rfl⟩ : syracuseStep 4897151 = 7345727) B7345727
theorem B3264767 : Blo 2175435 3264767 := bstep (se 1 (by rfl) ⟨2448575, by rfl⟩ : syracuseStep 3264767 = 4897151) B4897151
theorem B2176511 : Blo 2175435 2176511 := bstep (se 1 (by rfl) ⟨1632383, by rfl⟩ : syracuseStep 2176511 = 3264767) B3264767
theorem B3264773 : Blo 2175435 3264773 := bbase (se 4 (by rfl) ⟨306072, by rfl⟩ : syracuseStep 3264773 = 612145) (by norm_num)
theorem B2176515 : Blo 2175435 2176515 := bstep (se 1 (by rfl) ⟨1632386, by rfl⟩ : syracuseStep 2176515 = 3264773) B3264773
theorem B3672877 : Blo 2175435 3672877 := bbase (se 3 (by rfl) ⟨688664, by rfl⟩ : syracuseStep 3672877 = 1377329) (by norm_num)
theorem B4897169 : Blo 2175435 4897169 := bstep (se 2 (by rfl) ⟨1836438, by rfl⟩ : syracuseStep 4897169 = 3672877) B3672877
theorem B3264779 : Blo 2175435 3264779 := bstep (se 1 (by rfl) ⟨2448584, by rfl⟩ : syracuseStep 3264779 = 4897169) B4897169
theorem B2176519 : Blo 2175435 2176519 := bstep (se 1 (by rfl) ⟨1632389, by rfl⟩ : syracuseStep 2176519 = 3264779) B3264779
theorem B2448589 : Blo 2175435 2448589 := bbase (se 3 (by rfl) ⟨459110, by rfl⟩ : syracuseStep 2448589 = 918221) (by norm_num)
theorem B3264785 : Blo 2175435 3264785 := bstep (se 2 (by rfl) ⟨1224294, by rfl⟩ : syracuseStep 3264785 = 2448589) B2448589
theorem B2176523 : Blo 2175435 2176523 := bstep (se 1 (by rfl) ⟨1632392, by rfl⟩ : syracuseStep 2176523 = 3264785) B3264785
theorem B7345781 : Blo 2175435 7345781 := bbase (se 5 (by rfl) ⟨344333, by rfl⟩ : syracuseStep 7345781 = 688667) (by norm_num)
theorem B4897187 : Blo 2175435 4897187 := bstep (se 1 (by rfl) ⟨3672890, by rfl⟩ : syracuseStep 4897187 = 7345781) B7345781
theorem B3264791 : Blo 2175435 3264791 := bstep (se 1 (by rfl) ⟨2448593, by rfl⟩ : syracuseStep 3264791 = 4897187) B4897187
theorem B2176527 : Blo 2175435 2176527 := bstep (se 1 (by rfl) ⟨1632395, by rfl⟩ : syracuseStep 2176527 = 3264791) B3264791
theorem B3264797 : Blo 2175435 3264797 := bbase (se 3 (by rfl) ⟨612149, by rfl⟩ : syracuseStep 3264797 = 1224299) (by norm_num)
theorem B2176531 : Blo 2175435 2176531 := bstep (se 1 (by rfl) ⟨1632398, by rfl⟩ : syracuseStep 2176531 = 3264797) B3264797
theorem B4897205 : Blo 2175435 4897205 := bbase (se 5 (by rfl) ⟨229556, by rfl⟩ : syracuseStep 4897205 = 459113) (by norm_num)
theorem B3264803 : Blo 2175435 3264803 := bstep (se 1 (by rfl) ⟨2448602, by rfl⟩ : syracuseStep 3264803 = 4897205) B4897205
theorem B2176535 : Blo 2175435 2176535 := bstep (se 1 (by rfl) ⟨1632401, by rfl⟩ : syracuseStep 2176535 = 3264803) B3264803
theorem B3486397 : Blo 2175435 3486397 := bbase (se 3 (by rfl) ⟨653699, by rfl⟩ : syracuseStep 3486397 = 1307399) (by norm_num)
theorem B4648529 : Blo 2175435 4648529 := bstep (se 2 (by rfl) ⟨1743198, by rfl⟩ : syracuseStep 4648529 = 3486397) B3486397
theorem B12396077 : Blo 2175435 12396077 := bstep (se 3 (by rfl) ⟨2324264, by rfl⟩ : syracuseStep 12396077 = 4648529) B4648529
theorem B8264051 : Blo 2175435 8264051 := bstep (se 1 (by rfl) ⟨6198038, by rfl⟩ : syracuseStep 8264051 = 12396077) B12396077
theorem B5509367 : Blo 2175435 5509367 := bstep (se 1 (by rfl) ⟨4132025, by rfl⟩ : syracuseStep 5509367 = 8264051) B8264051
theorem B3672911 : Blo 2175435 3672911 := bstep (se 1 (by rfl) ⟨2754683, by rfl⟩ : syracuseStep 3672911 = 5509367) B5509367
theorem B2448607 : Blo 2175435 2448607 := bstep (se 1 (by rfl) ⟨1836455, by rfl⟩ : syracuseStep 2448607 = 3672911) B3672911
theorem B3264809 : Blo 2175435 3264809 := bstep (se 2 (by rfl) ⟨1224303, by rfl⟩ : syracuseStep 3264809 = 2448607) B2448607
theorem B2176539 : Blo 2175435 2176539 := bstep (se 1 (by rfl) ⟨1632404, by rfl⟩ : syracuseStep 2176539 = 3264809) B3264809
theorem B5229605 : Blo 2175435 5229605 := bbase (se 4 (by rfl) ⟨490275, by rfl⟩ : syracuseStep 5229605 = 980551) (by norm_num)
theorem B3486403 : Blo 2175435 3486403 := bstep (se 1 (by rfl) ⟨2614802, by rfl⟩ : syracuseStep 3486403 = 5229605) B5229605
theorem B4648537 : Blo 2175435 4648537 := bstep (se 2 (by rfl) ⟨1743201, by rfl⟩ : syracuseStep 4648537 = 3486403) B3486403
theorem B6198049 : Blo 2175435 6198049 := bstep (se 2 (by rfl) ⟨2324268, by rfl⟩ : syracuseStep 6198049 = 4648537) B4648537
theorem B8264065 : Blo 2175435 8264065 := bstep (se 2 (by rfl) ⟨3099024, by rfl⟩ : syracuseStep 8264065 = 6198049) B6198049
theorem B11018753 : Blo 2175435 11018753 := bstep (se 2 (by rfl) ⟨4132032, by rfl⟩ : syracuseStep 11018753 = 8264065) B8264065
theorem B7345835 : Blo 2175435 7345835 := bstep (se 1 (by rfl) ⟨5509376, by rfl⟩ : syracuseStep 7345835 = 11018753) B11018753
theorem B4897223 : Blo 2175435 4897223 := bstep (se 1 (by rfl) ⟨3672917, by rfl⟩ : syracuseStep 4897223 = 7345835) B7345835
theorem B3264815 : Blo 2175435 3264815 := bstep (se 1 (by rfl) ⟨2448611, by rfl⟩ : syracuseStep 3264815 = 4897223) B4897223
theorem B2176543 : Blo 2175435 2176543 := bstep (se 1 (by rfl) ⟨1632407, by rfl⟩ : syracuseStep 2176543 = 3264815) B3264815
theorem B3264821 : Blo 2175435 3264821 := bbase (se 5 (by rfl) ⟨153038, by rfl⟩ : syracuseStep 3264821 = 306077) (by norm_num)
theorem B2176547 : Blo 2175435 2176547 := bstep (se 1 (by rfl) ⟨1632410, by rfl⟩ : syracuseStep 2176547 = 3264821) B3264821
theorem B5509397 : Blo 2175435 5509397 := bbase (se 6 (by rfl) ⟨129126, by rfl⟩ : syracuseStep 5509397 = 258253) (by norm_num)
theorem B3672931 : Blo 2175435 3672931 := bstep (se 1 (by rfl) ⟨2754698, by rfl⟩ : syracuseStep 3672931 = 5509397) B5509397
theorem B4897241 : Blo 2175435 4897241 := bstep (se 2 (by rfl) ⟨1836465, by rfl⟩ : syracuseStep 4897241 = 3672931) B3672931
theorem B3264827 : Blo 2175435 3264827 := bstep (se 1 (by rfl) ⟨2448620, by rfl⟩ : syracuseStep 3264827 = 4897241) B4897241
theorem B2176551 : Blo 2175435 2176551 := bstep (se 1 (by rfl) ⟨1632413, by rfl⟩ : syracuseStep 2176551 = 3264827) B3264827
theorem B2448625 : Blo 2175435 2448625 := bbase (se 2 (by rfl) ⟨918234, by rfl⟩ : syracuseStep 2448625 = 1836469) (by norm_num)
theorem B3264833 : Blo 2175435 3264833 := bstep (se 2 (by rfl) ⟨1224312, by rfl⟩ : syracuseStep 3264833 = 2448625) B2448625
theorem B2176555 : Blo 2175435 2176555 := bstep (se 1 (by rfl) ⟨1632416, by rfl⟩ : syracuseStep 2176555 = 3264833) B3264833
theorem B5883349 : Blo 2175435 5883349 := bbase (se 7 (by rfl) ⟨68945, by rfl⟩ : syracuseStep 5883349 = 137891) (by norm_num)
theorem B7844465 : Blo 2175435 7844465 := bstep (se 2 (by rfl) ⟨2941674, by rfl⟩ : syracuseStep 7844465 = 5883349) B5883349
theorem B20918573 : Blo 2175435 20918573 := bstep (se 3 (by rfl) ⟨3922232, by rfl⟩ : syracuseStep 20918573 = 7844465) B7844465
theorem B13945715 : Blo 2175435 13945715 := bstep (se 1 (by rfl) ⟨10459286, by rfl⟩ : syracuseStep 13945715 = 20918573) B20918573
theorem B9297143 : Blo 2175435 9297143 := bstep (se 1 (by rfl) ⟨6972857, by rfl⟩ : syracuseStep 9297143 = 13945715) B13945715
theorem B6198095 : Blo 2175435 6198095 := bstep (se 1 (by rfl) ⟨4648571, by rfl⟩ : syracuseStep 6198095 = 9297143) B9297143
theorem B4132063 : Blo 2175435 4132063 := bstep (se 1 (by rfl) ⟨3099047, by rfl⟩ : syracuseStep 4132063 = 6198095) B6198095
theorem B5509417 : Blo 2175435 5509417 := bstep (se 2 (by rfl) ⟨2066031, by rfl⟩ : syracuseStep 5509417 = 4132063) B4132063
theorem B7345889 : Blo 2175435 7345889 := bstep (se 2 (by rfl) ⟨2754708, by rfl⟩ : syracuseStep 7345889 = 5509417) B5509417
theorem B4897259 : Blo 2175435 4897259 := bstep (se 1 (by rfl) ⟨3672944, by rfl⟩ : syracuseStep 4897259 = 7345889) B7345889
theorem B3264839 : Blo 2175435 3264839 := bstep (se 1 (by rfl) ⟨2448629, by rfl⟩ : syracuseStep 3264839 = 4897259) B4897259
theorem B2176559 : Blo 2175435 2176559 := bstep (se 1 (by rfl) ⟨1632419, by rfl⟩ : syracuseStep 2176559 = 3264839) B3264839
theorem B3264845 : Blo 2175435 3264845 := bbase (se 3 (by rfl) ⟨612158, by rfl⟩ : syracuseStep 3264845 = 1224317) (by norm_num)
theorem B2176563 : Blo 2175435 2176563 := bstep (se 1 (by rfl) ⟨1632422, by rfl⟩ : syracuseStep 2176563 = 3264845) B3264845
theorem B4897277 : Blo 2175435 4897277 := bbase (se 3 (by rfl) ⟨918239, by rfl⟩ : syracuseStep 4897277 = 1836479) (by norm_num)
theorem B3264851 : Blo 2175435 3264851 := bstep (se 1 (by rfl) ⟨2448638, by rfl⟩ : syracuseStep 3264851 = 4897277) B4897277
theorem B2176567 : Blo 2175435 2176567 := bstep (se 1 (by rfl) ⟨1632425, by rfl⟩ : syracuseStep 2176567 = 3264851) B3264851
theorem B3672965 : Blo 2175435 3672965 := bbase (se 4 (by rfl) ⟨344340, by rfl⟩ : syracuseStep 3672965 = 688681) (by norm_num)
theorem B2448643 : Blo 2175435 2448643 := bstep (se 1 (by rfl) ⟨1836482, by rfl⟩ : syracuseStep 2448643 = 3672965) B3672965
theorem B3264857 : Blo 2175435 3264857 := bstep (se 2 (by rfl) ⟨1224321, by rfl⟩ : syracuseStep 3264857 = 2448643) B2448643
theorem B2176571 : Blo 2175435 2176571 := bstep (se 1 (by rfl) ⟨1632428, by rfl⟩ : syracuseStep 2176571 = 3264857) B3264857
theorem B16528373 : Blo 2175435 16528373 := bbase (se 5 (by rfl) ⟨774767, by rfl⟩ : syracuseStep 16528373 = 1549535) (by norm_num)
theorem B11018915 : Blo 2175435 11018915 := bstep (se 1 (by rfl) ⟨8264186, by rfl⟩ : syracuseStep 11018915 = 16528373) B16528373
theorem B7345943 : Blo 2175435 7345943 := bstep (se 1 (by rfl) ⟨5509457, by rfl⟩ : syracuseStep 7345943 = 11018915) B11018915
theorem B4897295 : Blo 2175435 4897295 := bstep (se 1 (by rfl) ⟨3672971, by rfl⟩ : syracuseStep 4897295 = 7345943) B7345943
theorem B3264863 : Blo 2175435 3264863 := bstep (se 1 (by rfl) ⟨2448647, by rfl⟩ : syracuseStep 3264863 = 4897295) B4897295
theorem B2176575 : Blo 2175435 2176575 := bstep (se 1 (by rfl) ⟨1632431, by rfl⟩ : syracuseStep 2176575 = 3264863) B3264863
theorem B3264869 : Blo 2175435 3264869 := bbase (se 4 (by rfl) ⟨306081, by rfl⟩ : syracuseStep 3264869 = 612163) (by norm_num)
theorem B2176579 : Blo 2175435 2176579 := bstep (se 1 (by rfl) ⟨1632434, by rfl⟩ : syracuseStep 2176579 = 3264869) B3264869
theorem B4132109 : Blo 2175435 4132109 := bbase (se 3 (by rfl) ⟨774770, by rfl⟩ : syracuseStep 4132109 = 1549541) (by norm_num)
theorem B2754739 : Blo 2175435 2754739 := bstep (se 1 (by rfl) ⟨2066054, by rfl⟩ : syracuseStep 2754739 = 4132109) B4132109
theorem B3672985 : Blo 2175435 3672985 := bstep (se 2 (by rfl) ⟨1377369, by rfl⟩ : syracuseStep 3672985 = 2754739) B2754739
theorem B4897313 : Blo 2175435 4897313 := bstep (se 2 (by rfl) ⟨1836492, by rfl⟩ : syracuseStep 4897313 = 3672985) B3672985
theorem B3264875 : Blo 2175435 3264875 := bstep (se 1 (by rfl) ⟨2448656, by rfl⟩ : syracuseStep 3264875 = 4897313) B4897313
theorem B2176583 : Blo 2175435 2176583 := bstep (se 1 (by rfl) ⟨1632437, by rfl⟩ : syracuseStep 2176583 = 3264875) B3264875
theorem B2448661 : Blo 2175435 2448661 := bbase (se 6 (by rfl) ⟨57390, by rfl⟩ : syracuseStep 2448661 = 114781) (by norm_num)
theorem B3264881 : Blo 2175435 3264881 := bstep (se 2 (by rfl) ⟨1224330, by rfl⟩ : syracuseStep 3264881 = 2448661) B2448661
theorem B2176587 : Blo 2175435 2176587 := bstep (se 1 (by rfl) ⟨1632440, by rfl⟩ : syracuseStep 2176587 = 3264881) B3264881
theorem B2754749 : Blo 2175435 2754749 := bbase (se 3 (by rfl) ⟨516515, by rfl⟩ : syracuseStep 2754749 = 1033031) (by norm_num)
theorem B7345997 : Blo 2175435 7345997 := bstep (se 3 (by rfl) ⟨1377374, by rfl⟩ : syracuseStep 7345997 = 2754749) B2754749
theorem B4897331 : Blo 2175435 4897331 := bstep (se 1 (by rfl) ⟨3672998, by rfl⟩ : syracuseStep 4897331 = 7345997) B7345997
theorem B3264887 : Blo 2175435 3264887 := bstep (se 1 (by rfl) ⟨2448665, by rfl⟩ : syracuseStep 3264887 = 4897331) B4897331
theorem B2176591 : Blo 2175435 2176591 := bstep (se 1 (by rfl) ⟨1632443, by rfl⟩ : syracuseStep 2176591 = 3264887) B3264887
theorem B3264893 : Blo 2175435 3264893 := bbase (se 3 (by rfl) ⟨612167, by rfl⟩ : syracuseStep 3264893 = 1224335) (by norm_num)
theorem B2176595 : Blo 2175435 2176595 := bstep (se 1 (by rfl) ⟨1632446, by rfl⟩ : syracuseStep 2176595 = 3264893) B3264893
theorem B4897349 : Blo 2175435 4897349 := bbase (se 4 (by rfl) ⟨459126, by rfl⟩ : syracuseStep 4897349 = 918253) (by norm_num)
theorem B3264899 : Blo 2175435 3264899 := bstep (se 1 (by rfl) ⟨2448674, by rfl⟩ : syracuseStep 3264899 = 4897349) B4897349
theorem B2176599 : Blo 2175435 2176599 := bstep (se 1 (by rfl) ⟨1632449, by rfl⟩ : syracuseStep 2176599 = 3264899) B3264899
theorem B2324333 : Blo 2175435 2324333 := bbase (se 3 (by rfl) ⟨435812, by rfl⟩ : syracuseStep 2324333 = 871625) (by norm_num)
theorem B6198221 : Blo 2175435 6198221 := bstep (se 3 (by rfl) ⟨1162166, by rfl⟩ : syracuseStep 6198221 = 2324333) B2324333
theorem B4132147 : Blo 2175435 4132147 := bstep (se 1 (by rfl) ⟨3099110, by rfl⟩ : syracuseStep 4132147 = 6198221) B6198221
theorem B5509529 : Blo 2175435 5509529 := bstep (se 2 (by rfl) ⟨2066073, by rfl⟩ : syracuseStep 5509529 = 4132147) B4132147
theorem B3673019 : Blo 2175435 3673019 := bstep (se 1 (by rfl) ⟨2754764, by rfl⟩ : syracuseStep 3673019 = 5509529) B5509529
theorem B2448679 : Blo 2175435 2448679 := bstep (se 1 (by rfl) ⟨1836509, by rfl⟩ : syracuseStep 2448679 = 3673019) B3673019
theorem B3264905 : Blo 2175435 3264905 := bstep (se 2 (by rfl) ⟨1224339, by rfl⟩ : syracuseStep 3264905 = 2448679) B2448679
theorem B2176603 : Blo 2175435 2176603 := bstep (se 1 (by rfl) ⟨1632452, by rfl⟩ : syracuseStep 2176603 = 3264905) B3264905
theorem B11019077 : Blo 2175435 11019077 := bbase (se 4 (by rfl) ⟨1033038, by rfl⟩ : syracuseStep 11019077 = 2066077) (by norm_num)
theorem B7346051 : Blo 2175435 7346051 := bstep (se 1 (by rfl) ⟨5509538, by rfl⟩ : syracuseStep 7346051 = 11019077) B11019077
theorem B4897367 : Blo 2175435 4897367 := bstep (se 1 (by rfl) ⟨3673025, by rfl⟩ : syracuseStep 4897367 = 7346051) B7346051
theorem B3264911 : Blo 2175435 3264911 := bstep (se 1 (by rfl) ⟨2448683, by rfl⟩ : syracuseStep 3264911 = 4897367) B4897367
theorem B2176607 : Blo 2175435 2176607 := bstep (se 1 (by rfl) ⟨1632455, by rfl⟩ : syracuseStep 2176607 = 3264911) B3264911
theorem B3264917 : Blo 2175435 3264917 := bbase (se 6 (by rfl) ⟨76521, by rfl⟩ : syracuseStep 3264917 = 153043) (by norm_num)
theorem B2176611 : Blo 2175435 2176611 := bstep (se 1 (by rfl) ⟨1632458, by rfl⟩ : syracuseStep 2176611 = 3264917) B3264917
theorem B2614889 : Blo 2175435 2614889 := bbase (se 2 (by rfl) ⟨980583, by rfl⟩ : syracuseStep 2614889 = 1961167) (by norm_num)
theorem B6973037 : Blo 2175435 6973037 := bstep (se 3 (by rfl) ⟨1307444, by rfl⟩ : syracuseStep 6973037 = 2614889) B2614889
theorem B4648691 : Blo 2175435 4648691 := bstep (se 1 (by rfl) ⟨3486518, by rfl⟩ : syracuseStep 4648691 = 6973037) B6973037
theorem B12396509 : Blo 2175435 12396509 := bstep (se 3 (by rfl) ⟨2324345, by rfl⟩ : syracuseStep 12396509 = 4648691) B4648691
theorem B8264339 : Blo 2175435 8264339 := bstep (se 1 (by rfl) ⟨6198254, by rfl⟩ : syracuseStep 8264339 = 12396509) B12396509
theorem B5509559 : Blo 2175435 5509559 := bstep (se 1 (by rfl) ⟨4132169, by rfl⟩ : syracuseStep 5509559 = 8264339) B8264339
theorem B3673039 : Blo 2175435 3673039 := bstep (se 1 (by rfl) ⟨2754779, by rfl⟩ : syracuseStep 3673039 = 5509559) B5509559
theorem B4897385 : Blo 2175435 4897385 := bstep (se 2 (by rfl) ⟨1836519, by rfl⟩ : syracuseStep 4897385 = 3673039) B3673039
theorem B3264923 : Blo 2175435 3264923 := bstep (se 1 (by rfl) ⟨2448692, by rfl⟩ : syracuseStep 3264923 = 4897385) B4897385
theorem B2176615 : Blo 2175435 2176615 := bstep (se 1 (by rfl) ⟨1632461, by rfl⟩ : syracuseStep 2176615 = 3264923) B3264923
theorem B2448697 : Blo 2175435 2448697 := bbase (se 2 (by rfl) ⟨918261, by rfl⟩ : syracuseStep 2448697 = 1836523) (by norm_num)
theorem B3264929 : Blo 2175435 3264929 := bstep (se 2 (by rfl) ⟨1224348, by rfl⟩ : syracuseStep 3264929 = 2448697) B2448697
theorem B2176619 : Blo 2175435 2176619 := bstep (se 1 (by rfl) ⟨1632464, by rfl⟩ : syracuseStep 2176619 = 3264929) B3264929
theorem B6198277 : Blo 2175435 6198277 := bbase (se 4 (by rfl) ⟨581088, by rfl⟩ : syracuseStep 6198277 = 1162177) (by norm_num)
theorem B8264369 : Blo 2175435 8264369 := bstep (se 2 (by rfl) ⟨3099138, by rfl⟩ : syracuseStep 8264369 = 6198277) B6198277
theorem B5509579 : Blo 2175435 5509579 := bstep (se 1 (by rfl) ⟨4132184, by rfl⟩ : syracuseStep 5509579 = 8264369) B8264369
theorem B7346105 : Blo 2175435 7346105 := bstep (se 2 (by rfl) ⟨2754789, by rfl⟩ : syracuseStep 7346105 = 5509579) B5509579
theorem B4897403 : Blo 2175435 4897403 := bstep (se 1 (by rfl) ⟨3673052, by rfl⟩ : syracuseStep 4897403 = 7346105) B7346105
theorem B3264935 : Blo 2175435 3264935 := bstep (se 1 (by rfl) ⟨2448701, by rfl⟩ : syracuseStep 3264935 = 4897403) B4897403
theorem B2176623 : Blo 2175435 2176623 := bstep (se 1 (by rfl) ⟨1632467, by rfl⟩ : syracuseStep 2176623 = 3264935) B3264935
theorem B3264941 : Blo 2175435 3264941 := bbase (se 3 (by rfl) ⟨612176, by rfl⟩ : syracuseStep 3264941 = 1224353) (by norm_num)
theorem B2176627 : Blo 2175435 2176627 := bstep (se 1 (by rfl) ⟨1632470, by rfl⟩ : syracuseStep 2176627 = 3264941) B3264941
theorem B4897421 : Blo 2175435 4897421 := bbase (se 3 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 4897421 = 1836533) (by norm_num)
theorem B3264947 : Blo 2175435 3264947 := bstep (se 1 (by rfl) ⟨2448710, by rfl⟩ : syracuseStep 3264947 = 4897421) B4897421
theorem B2176631 : Blo 2175435 2176631 := bstep (se 1 (by rfl) ⟨1632473, by rfl⟩ : syracuseStep 2176631 = 3264947) B3264947
theorem B2754805 : Blo 2175435 2754805 := bbase (se 5 (by rfl) ⟨129131, by rfl⟩ : syracuseStep 2754805 = 258263) (by norm_num)
theorem B3673073 : Blo 2175435 3673073 := bstep (se 2 (by rfl) ⟨1377402, by rfl⟩ : syracuseStep 3673073 = 2754805) B2754805
theorem B2448715 : Blo 2175435 2448715 := bstep (se 1 (by rfl) ⟨1836536, by rfl⟩ : syracuseStep 2448715 = 3673073) B3673073
theorem B3264953 : Blo 2175435 3264953 := bstep (se 2 (by rfl) ⟨1224357, by rfl⟩ : syracuseStep 3264953 = 2448715) B2448715
theorem B2176635 : Blo 2175435 2176635 := bstep (se 1 (by rfl) ⟨1632476, by rfl⟩ : syracuseStep 2176635 = 3264953) B3264953
theorem B41838677 : Blo 2175435 41838677 := bbase (se 8 (by rfl) ⟨245148, by rfl⟩ : syracuseStep 41838677 = 490297) (by norm_num)
theorem B27892451 : Blo 2175435 27892451 := bstep (se 1 (by rfl) ⟨20919338, by rfl⟩ : syracuseStep 27892451 = 41838677) B41838677
theorem B18594967 : Blo 2175435 18594967 := bstep (se 1 (by rfl) ⟨13946225, by rfl⟩ : syracuseStep 18594967 = 27892451) B27892451
theorem B24793289 : Blo 2175435 24793289 := bstep (se 2 (by rfl) ⟨9297483, by rfl⟩ : syracuseStep 24793289 = 18594967) B18594967
theorem B16528859 : Blo 2175435 16528859 := bstep (se 1 (by rfl) ⟨12396644, by rfl⟩ : syracuseStep 16528859 = 24793289) B24793289
theorem B11019239 : Blo 2175435 11019239 := bstep (se 1 (by rfl) ⟨8264429, by rfl⟩ : syracuseStep 11019239 = 16528859) B16528859
theorem B7346159 : Blo 2175435 7346159 := bstep (se 1 (by rfl) ⟨5509619, by rfl⟩ : syracuseStep 7346159 = 11019239) B11019239
theorem B4897439 : Blo 2175435 4897439 := bstep (se 1 (by rfl) ⟨3673079, by rfl⟩ : syracuseStep 4897439 = 7346159) B7346159
theorem B3264959 : Blo 2175435 3264959 := bstep (se 1 (by rfl) ⟨2448719, by rfl⟩ : syracuseStep 3264959 = 4897439) B4897439
theorem B2176639 : Blo 2175435 2176639 := bstep (se 1 (by rfl) ⟨1632479, by rfl⟩ : syracuseStep 2176639 = 3264959) B3264959
theorem B3264965 : Blo 2175435 3264965 := bbase (se 4 (by rfl) ⟨306090, by rfl⟩ : syracuseStep 3264965 = 612181) (by norm_num)
theorem B2176643 : Blo 2175435 2176643 := bstep (se 1 (by rfl) ⟨1632482, by rfl⟩ : syracuseStep 2176643 = 3264965) B3264965
theorem B3673093 : Blo 2175435 3673093 := bbase (se 4 (by rfl) ⟨344352, by rfl⟩ : syracuseStep 3673093 = 688705) (by norm_num)
theorem B4897457 : Blo 2175435 4897457 := bstep (se 2 (by rfl) ⟨1836546, by rfl⟩ : syracuseStep 4897457 = 3673093) B3673093
theorem B3264971 : Blo 2175435 3264971 := bstep (se 1 (by rfl) ⟨2448728, by rfl⟩ : syracuseStep 3264971 = 4897457) B4897457
theorem B2176647 : Blo 2175435 2176647 := bstep (se 1 (by rfl) ⟨1632485, by rfl⟩ : syracuseStep 2176647 = 3264971) B3264971
theorem B2448733 : Blo 2175435 2448733 := bbase (se 3 (by rfl) ⟨459137, by rfl⟩ : syracuseStep 2448733 = 918275) (by norm_num)
theorem B3264977 : Blo 2175435 3264977 := bstep (se 2 (by rfl) ⟨1224366, by rfl⟩ : syracuseStep 3264977 = 2448733) B2448733
theorem B2176651 : Blo 2175435 2176651 := bstep (se 1 (by rfl) ⟨1632488, by rfl⟩ : syracuseStep 2176651 = 3264977) B3264977
theorem B7346213 : Blo 2175435 7346213 := bbase (se 4 (by rfl) ⟨688707, by rfl⟩ : syracuseStep 7346213 = 1377415) (by norm_num)
theorem B4897475 : Blo 2175435 4897475 := bstep (se 1 (by rfl) ⟨3673106, by rfl⟩ : syracuseStep 4897475 = 7346213) B7346213
theorem B3264983 : Blo 2175435 3264983 := bstep (se 1 (by rfl) ⟨2448737, by rfl⟩ : syracuseStep 3264983 = 4897475) B4897475
theorem B2176655 : Blo 2175435 2176655 := bstep (se 1 (by rfl) ⟨1632491, by rfl⟩ : syracuseStep 2176655 = 3264983) B3264983
theorem B3264989 : Blo 2175435 3264989 := bbase (se 3 (by rfl) ⟨612185, by rfl⟩ : syracuseStep 3264989 = 1224371) (by norm_num)
theorem B2176659 : Blo 2175435 2176659 := bstep (se 1 (by rfl) ⟨1632494, by rfl⟩ : syracuseStep 2176659 = 3264989) B3264989
theorem B4897493 : Blo 2175435 4897493 := bbase (se 7 (by rfl) ⟨57392, by rfl⟩ : syracuseStep 4897493 = 114785) (by norm_num)
theorem B3264995 : Blo 2175435 3264995 := bstep (se 1 (by rfl) ⟨2448746, by rfl⟩ : syracuseStep 3264995 = 4897493) B4897493
theorem B2176663 : Blo 2175435 2176663 := bstep (se 1 (by rfl) ⟨1632497, by rfl⟩ : syracuseStep 2176663 = 3264995) B3264995
theorem B9297605 : Blo 2175435 9297605 := bbase (se 4 (by rfl) ⟨871650, by rfl⟩ : syracuseStep 9297605 = 1743301) (by norm_num)
theorem B6198403 : Blo 2175435 6198403 := bstep (se 1 (by rfl) ⟨4648802, by rfl⟩ : syracuseStep 6198403 = 9297605) B9297605
theorem B8264537 : Blo 2175435 8264537 := bstep (se 2 (by rfl) ⟨3099201, by rfl⟩ : syracuseStep 8264537 = 6198403) B6198403
theorem B5509691 : Blo 2175435 5509691 := bstep (se 1 (by rfl) ⟨4132268, by rfl⟩ : syracuseStep 5509691 = 8264537) B8264537
theorem B3673127 : Blo 2175435 3673127 := bstep (se 1 (by rfl) ⟨2754845, by rfl⟩ : syracuseStep 3673127 = 5509691) B5509691
theorem B2448751 : Blo 2175435 2448751 := bstep (se 1 (by rfl) ⟨1836563, by rfl⟩ : syracuseStep 2448751 = 3673127) B3673127
theorem B3265001 : Blo 2175435 3265001 := bstep (se 2 (by rfl) ⟨1224375, by rfl⟩ : syracuseStep 3265001 = 2448751) B2448751
theorem B2176667 : Blo 2175435 2176667 := bstep (se 1 (by rfl) ⟨1632500, by rfl⟩ : syracuseStep 2176667 = 3265001) B3265001
theorem B9928661 : Blo 2175435 9928661 := bbase (se 7 (by rfl) ⟨116351, by rfl⟩ : syracuseStep 9928661 = 232703) (by norm_num)
theorem B105905717 : Blo 2175435 105905717 := bstep (se 5 (by rfl) ⟨4964330, by rfl⟩ : syracuseStep 105905717 = 9928661) B9928661
theorem B70603811 : Blo 2175435 70603811 := bstep (se 1 (by rfl) ⟨52952858, by rfl⟩ : syracuseStep 70603811 = 105905717) B105905717
theorem B47069207 : Blo 2175435 47069207 := bstep (se 1 (by rfl) ⟨35301905, by rfl⟩ : syracuseStep 47069207 = 70603811) B70603811
theorem B31379471 : Blo 2175435 31379471 := bstep (se 1 (by rfl) ⟨23534603, by rfl⟩ : syracuseStep 31379471 = 47069207) B47069207
theorem B20919647 : Blo 2175435 20919647 := bstep (se 1 (by rfl) ⟨15689735, by rfl⟩ : syracuseStep 20919647 = 31379471) B31379471
theorem B13946431 : Blo 2175435 13946431 := bstep (se 1 (by rfl) ⟨10459823, by rfl⟩ : syracuseStep 13946431 = 20919647) B20919647
theorem B18595241 : Blo 2175435 18595241 := bstep (se 2 (by rfl) ⟨6973215, by rfl⟩ : syracuseStep 18595241 = 13946431) B13946431
theorem B12396827 : Blo 2175435 12396827 := bstep (se 1 (by rfl) ⟨9297620, by rfl⟩ : syracuseStep 12396827 = 18595241) B18595241
theorem B8264551 : Blo 2175435 8264551 := bstep (se 1 (by rfl) ⟨6198413, by rfl⟩ : syracuseStep 8264551 = 12396827) B12396827
theorem B11019401 : Blo 2175435 11019401 := bstep (se 2 (by rfl) ⟨4132275, by rfl⟩ : syracuseStep 11019401 = 8264551) B8264551
theorem B7346267 : Blo 2175435 7346267 := bstep (se 1 (by rfl) ⟨5509700, by rfl⟩ : syracuseStep 7346267 = 11019401) B11019401
theorem B4897511 : Blo 2175435 4897511 := bstep (se 1 (by rfl) ⟨3673133, by rfl⟩ : syracuseStep 4897511 = 7346267) B7346267
theorem B3265007 : Blo 2175435 3265007 := bstep (se 1 (by rfl) ⟨2448755, by rfl⟩ : syracuseStep 3265007 = 4897511) B4897511
theorem B2176671 : Blo 2175435 2176671 := bstep (se 1 (by rfl) ⟨1632503, by rfl⟩ : syracuseStep 2176671 = 3265007) B3265007
theorem B3265013 : Blo 2175435 3265013 := bbase (se 5 (by rfl) ⟨153047, by rfl⟩ : syracuseStep 3265013 = 306095) (by norm_num)
theorem B2176675 : Blo 2175435 2176675 := bstep (se 1 (by rfl) ⟨1632506, by rfl⟩ : syracuseStep 2176675 = 3265013) B3265013
theorem B6198437 : Blo 2175435 6198437 := bbase (se 4 (by rfl) ⟨581103, by rfl⟩ : syracuseStep 6198437 = 1162207) (by norm_num)
theorem B4132291 : Blo 2175435 4132291 := bstep (se 1 (by rfl) ⟨3099218, by rfl⟩ : syracuseStep 4132291 = 6198437) B6198437
theorem B5509721 : Blo 2175435 5509721 := bstep (se 2 (by rfl) ⟨2066145, by rfl⟩ : syracuseStep 5509721 = 4132291) B4132291
theorem B3673147 : Blo 2175435 3673147 := bstep (se 1 (by rfl) ⟨2754860, by rfl⟩ : syracuseStep 3673147 = 5509721) B5509721
theorem B4897529 : Blo 2175435 4897529 := bstep (se 2 (by rfl) ⟨1836573, by rfl⟩ : syracuseStep 4897529 = 3673147) B3673147
theorem B3265019 : Blo 2175435 3265019 := bstep (se 1 (by rfl) ⟨2448764, by rfl⟩ : syracuseStep 3265019 = 4897529) B4897529
theorem B2176679 : Blo 2175435 2176679 := bstep (se 1 (by rfl) ⟨1632509, by rfl⟩ : syracuseStep 2176679 = 3265019) B3265019
theorem B2448769 : Blo 2175435 2448769 := bbase (se 2 (by rfl) ⟨918288, by rfl⟩ : syracuseStep 2448769 = 1836577) (by norm_num)
theorem B3265025 : Blo 2175435 3265025 := bstep (se 2 (by rfl) ⟨1224384, by rfl⟩ : syracuseStep 3265025 = 2448769) B2448769
theorem B2176683 : Blo 2175435 2176683 := bstep (se 1 (by rfl) ⟨1632512, by rfl⟩ : syracuseStep 2176683 = 3265025) B3265025
theorem B5509741 : Blo 2175435 5509741 := bbase (se 3 (by rfl) ⟨1033076, by rfl⟩ : syracuseStep 5509741 = 2066153) (by norm_num)
theorem B7346321 : Blo 2175435 7346321 := bstep (se 2 (by rfl) ⟨2754870, by rfl⟩ : syracuseStep 7346321 = 5509741) B5509741
theorem B4897547 : Blo 2175435 4897547 := bstep (se 1 (by rfl) ⟨3673160, by rfl⟩ : syracuseStep 4897547 = 7346321) B7346321
theorem B3265031 : Blo 2175435 3265031 := bstep (se 1 (by rfl) ⟨2448773, by rfl⟩ : syracuseStep 3265031 = 4897547) B4897547
theorem B2176687 : Blo 2175435 2176687 := bstep (se 1 (by rfl) ⟨1632515, by rfl⟩ : syracuseStep 2176687 = 3265031) B3265031
theorem B3265037 : Blo 2175435 3265037 := bbase (se 3 (by rfl) ⟨612194, by rfl⟩ : syracuseStep 3265037 = 1224389) (by norm_num)
theorem B2176691 : Blo 2175435 2176691 := bstep (se 1 (by rfl) ⟨1632518, by rfl⟩ : syracuseStep 2176691 = 3265037) B3265037
theorem B4897565 : Blo 2175435 4897565 := bbase (se 3 (by rfl) ⟨918293, by rfl⟩ : syracuseStep 4897565 = 1836587) (by norm_num)
theorem B3265043 : Blo 2175435 3265043 := bstep (se 1 (by rfl) ⟨2448782, by rfl⟩ : syracuseStep 3265043 = 4897565) B4897565
theorem B2176695 : Blo 2175435 2176695 := bstep (se 1 (by rfl) ⟨1632521, by rfl⟩ : syracuseStep 2176695 = 3265043) B3265043
theorem B3673181 : Blo 2175435 3673181 := bbase (se 3 (by rfl) ⟨688721, by rfl⟩ : syracuseStep 3673181 = 1377443) (by norm_num)
theorem B2448787 : Blo 2175435 2448787 := bstep (se 1 (by rfl) ⟨1836590, by rfl⟩ : syracuseStep 2448787 = 3673181) B3673181
theorem B3265049 : Blo 2175435 3265049 := bstep (se 2 (by rfl) ⟨1224393, by rfl⟩ : syracuseStep 3265049 = 2448787) B2448787
theorem B2176699 : Blo 2175435 2176699 := bstep (se 1 (by rfl) ⟨1632524, by rfl⟩ : syracuseStep 2176699 = 3265049) B3265049
theorem B5229989 : Blo 2175435 5229989 := bbase (se 4 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 5229989 = 980623) (by norm_num)
theorem B3486659 : Blo 2175435 3486659 := bstep (se 1 (by rfl) ⟨2614994, by rfl⟩ : syracuseStep 3486659 = 5229989) B5229989
theorem B9297757 : Blo 2175435 9297757 := bstep (se 3 (by rfl) ⟨1743329, by rfl⟩ : syracuseStep 9297757 = 3486659) B3486659
theorem B12397009 : Blo 2175435 12397009 := bstep (se 2 (by rfl) ⟨4648878, by rfl⟩ : syracuseStep 12397009 = 9297757) B9297757
theorem B16529345 : Blo 2175435 16529345 := bstep (se 2 (by rfl) ⟨6198504, by rfl⟩ : syracuseStep 16529345 = 12397009) B12397009
theorem B11019563 : Blo 2175435 11019563 := bstep (se 1 (by rfl) ⟨8264672, by rfl⟩ : syracuseStep 11019563 = 16529345) B16529345
theorem B7346375 : Blo 2175435 7346375 := bstep (se 1 (by rfl) ⟨5509781, by rfl⟩ : syracuseStep 7346375 = 11019563) B11019563
theorem B4897583 : Blo 2175435 4897583 := bstep (se 1 (by rfl) ⟨3673187, by rfl⟩ : syracuseStep 4897583 = 7346375) B7346375
theorem B3265055 : Blo 2175435 3265055 := bstep (se 1 (by rfl) ⟨2448791, by rfl⟩ : syracuseStep 3265055 = 4897583) B4897583
theorem B2176703 : Blo 2175435 2176703 := bstep (se 1 (by rfl) ⟨1632527, by rfl⟩ : syracuseStep 2176703 = 3265055) B3265055
theorem B3265061 : Blo 2175435 3265061 := bbase (se 4 (by rfl) ⟨306099, by rfl⟩ : syracuseStep 3265061 = 612199) (by norm_num)
theorem B2176707 : Blo 2175435 2176707 := bstep (se 1 (by rfl) ⟨1632530, by rfl⟩ : syracuseStep 2176707 = 3265061) B3265061
theorem B2754901 : Blo 2175435 2754901 := bbase (se 10 (by rfl) ⟨4035, by rfl⟩ : syracuseStep 2754901 = 8071) (by norm_num)
theorem B3673201 : Blo 2175435 3673201 := bstep (se 2 (by rfl) ⟨1377450, by rfl⟩ : syracuseStep 3673201 = 2754901) B2754901
theorem B4897601 : Blo 2175435 4897601 := bstep (se 2 (by rfl) ⟨1836600, by rfl⟩ : syracuseStep 4897601 = 3673201) B3673201
theorem B3265067 : Blo 2175435 3265067 := bstep (se 1 (by rfl) ⟨2448800, by rfl⟩ : syracuseStep 3265067 = 4897601) B4897601
theorem B2176711 : Blo 2175435 2176711 := bstep (se 1 (by rfl) ⟨1632533, by rfl⟩ : syracuseStep 2176711 = 3265067) B3265067
theorem B2448805 : Blo 2175435 2448805 := bbase (se 4 (by rfl) ⟨229575, by rfl⟩ : syracuseStep 2448805 = 459151) (by norm_num)
theorem B3265073 : Blo 2175435 3265073 := bstep (se 2 (by rfl) ⟨1224402, by rfl⟩ : syracuseStep 3265073 = 2448805) B2448805
theorem B2176715 : Blo 2175435 2176715 := bstep (se 1 (by rfl) ⟨1632536, by rfl⟩ : syracuseStep 2176715 = 3265073) B3265073
theorem B13946741 : Blo 2175435 13946741 := bbase (se 5 (by rfl) ⟨653753, by rfl⟩ : syracuseStep 13946741 = 1307507) (by norm_num)
theorem B9297827 : Blo 2175435 9297827 := bstep (se 1 (by rfl) ⟨6973370, by rfl⟩ : syracuseStep 9297827 = 13946741) B13946741
theorem B6198551 : Blo 2175435 6198551 := bstep (se 1 (by rfl) ⟨4648913, by rfl⟩ : syracuseStep 6198551 = 9297827) B9297827
theorem B4132367 : Blo 2175435 4132367 := bstep (se 1 (by rfl) ⟨3099275, by rfl⟩ : syracuseStep 4132367 = 6198551) B6198551
theorem B2754911 : Blo 2175435 2754911 := bstep (se 1 (by rfl) ⟨2066183, by rfl⟩ : syracuseStep 2754911 = 4132367) B4132367
theorem B7346429 : Blo 2175435 7346429 := bstep (se 3 (by rfl) ⟨1377455, by rfl⟩ : syracuseStep 7346429 = 2754911) B2754911
theorem B4897619 : Blo 2175435 4897619 := bstep (se 1 (by rfl) ⟨3673214, by rfl⟩ : syracuseStep 4897619 = 7346429) B7346429
theorem B3265079 : Blo 2175435 3265079 := bstep (se 1 (by rfl) ⟨2448809, by rfl⟩ : syracuseStep 3265079 = 4897619) B4897619
theorem B2176719 : Blo 2175435 2176719 := bstep (se 1 (by rfl) ⟨1632539, by rfl⟩ : syracuseStep 2176719 = 3265079) B3265079
theorem B3265085 : Blo 2175435 3265085 := bbase (se 3 (by rfl) ⟨612203, by rfl⟩ : syracuseStep 3265085 = 1224407) (by norm_num)
theorem B2176723 : Blo 2175435 2176723 := bstep (se 1 (by rfl) ⟨1632542, by rfl⟩ : syracuseStep 2176723 = 3265085) B3265085
theorem B4897637 : Blo 2175435 4897637 := bbase (se 4 (by rfl) ⟨459153, by rfl⟩ : syracuseStep 4897637 = 918307) (by norm_num)
theorem B3265091 : Blo 2175435 3265091 := bstep (se 1 (by rfl) ⟨2448818, by rfl⟩ : syracuseStep 3265091 = 4897637) B4897637
theorem B2176727 : Blo 2175435 2176727 := bstep (se 1 (by rfl) ⟨1632545, by rfl⟩ : syracuseStep 2176727 = 3265091) B3265091
theorem B5509853 : Blo 2175435 5509853 := bbase (se 3 (by rfl) ⟨1033097, by rfl⟩ : syracuseStep 5509853 = 2066195) (by norm_num)
theorem B3673235 : Blo 2175435 3673235 := bstep (se 1 (by rfl) ⟨2754926, by rfl⟩ : syracuseStep 3673235 = 5509853) B5509853
theorem B2448823 : Blo 2175435 2448823 := bstep (se 1 (by rfl) ⟨1836617, by rfl⟩ : syracuseStep 2448823 = 3673235) B3673235
theorem B3265097 : Blo 2175435 3265097 := bstep (se 2 (by rfl) ⟨1224411, by rfl⟩ : syracuseStep 3265097 = 2448823) B2448823
theorem B2176731 : Blo 2175435 2176731 := bstep (se 1 (by rfl) ⟨1632548, by rfl⟩ : syracuseStep 2176731 = 3265097) B3265097
theorem B4132397 : Blo 2175435 4132397 := bbase (se 3 (by rfl) ⟨774824, by rfl⟩ : syracuseStep 4132397 = 1549649) (by norm_num)
theorem B11019725 : Blo 2175435 11019725 := bstep (se 3 (by rfl) ⟨2066198, by rfl⟩ : syracuseStep 11019725 = 4132397) B4132397
theorem B7346483 : Blo 2175435 7346483 := bstep (se 1 (by rfl) ⟨5509862, by rfl⟩ : syracuseStep 7346483 = 11019725) B11019725
theorem B4897655 : Blo 2175435 4897655 := bstep (se 1 (by rfl) ⟨3673241, by rfl⟩ : syracuseStep 4897655 = 7346483) B7346483
theorem B3265103 : Blo 2175435 3265103 := bstep (se 1 (by rfl) ⟨2448827, by rfl⟩ : syracuseStep 3265103 = 4897655) B4897655
theorem B2176735 : Blo 2175435 2176735 := bstep (se 1 (by rfl) ⟨1632551, by rfl⟩ : syracuseStep 2176735 = 3265103) B3265103
theorem B3265109 : Blo 2175435 3265109 := bbase (se 8 (by rfl) ⟨19131, by rfl⟩ : syracuseStep 3265109 = 38263) (by norm_num)
theorem B2176739 : Blo 2175435 2176739 := bstep (se 1 (by rfl) ⟨1632554, by rfl⟩ : syracuseStep 2176739 = 3265109) B3265109
theorem B4412885 : Blo 2175435 4412885 := bbase (se 7 (by rfl) ⟨51713, by rfl⟩ : syracuseStep 4412885 = 103427) (by norm_num)
theorem B11767693 : Blo 2175435 11767693 := bstep (se 3 (by rfl) ⟨2206442, by rfl⟩ : syracuseStep 11767693 = 4412885) B4412885
theorem B15690257 : Blo 2175435 15690257 := bstep (se 2 (by rfl) ⟨5883846, by rfl⟩ : syracuseStep 15690257 = 11767693) B11767693
theorem B10460171 : Blo 2175435 10460171 := bstep (se 1 (by rfl) ⟨7845128, by rfl⟩ : syracuseStep 10460171 = 15690257) B15690257
theorem B6973447 : Blo 2175435 6973447 := bstep (se 1 (by rfl) ⟨5230085, by rfl⟩ : syracuseStep 6973447 = 10460171) B10460171
theorem B9297929 : Blo 2175435 9297929 := bstep (se 2 (by rfl) ⟨3486723, by rfl⟩ : syracuseStep 9297929 = 6973447) B6973447
theorem B6198619 : Blo 2175435 6198619 := bstep (se 1 (by rfl) ⟨4648964, by rfl⟩ : syracuseStep 6198619 = 9297929) B9297929
theorem B8264825 : Blo 2175435 8264825 := bstep (se 2 (by rfl) ⟨3099309, by rfl⟩ : syracuseStep 8264825 = 6198619) B6198619
theorem B5509883 : Blo 2175435 5509883 := bstep (se 1 (by rfl) ⟨4132412, by rfl⟩ : syracuseStep 5509883 = 8264825) B8264825
theorem B3673255 : Blo 2175435 3673255 := bstep (se 1 (by rfl) ⟨2754941, by rfl⟩ : syracuseStep 3673255 = 5509883) B5509883
theorem B4897673 : Blo 2175435 4897673 := bstep (se 2 (by rfl) ⟨1836627, by rfl⟩ : syracuseStep 4897673 = 3673255) B3673255
theorem B3265115 : Blo 2175435 3265115 := bstep (se 1 (by rfl) ⟨2448836, by rfl⟩ : syracuseStep 3265115 = 4897673) B4897673
theorem B2176743 : Blo 2175435 2176743 := bstep (se 1 (by rfl) ⟨1632557, by rfl⟩ : syracuseStep 2176743 = 3265115) B3265115
theorem B2448841 : Blo 2175435 2448841 := bbase (se 2 (by rfl) ⟨918315, by rfl⟩ : syracuseStep 2448841 = 1836631) (by norm_num)
theorem B3265121 : Blo 2175435 3265121 := bstep (se 2 (by rfl) ⟨1224420, by rfl⟩ : syracuseStep 3265121 = 2448841) B2448841
theorem B2176747 : Blo 2175435 2176747 := bstep (se 1 (by rfl) ⟨1632560, by rfl⟩ : syracuseStep 2176747 = 3265121) B3265121
theorem B18595925 : Blo 2175435 18595925 := bbase (se 8 (by rfl) ⟨108960, by rfl⟩ : syracuseStep 18595925 = 217921) (by norm_num)
theorem B12397283 : Blo 2175435 12397283 := bstep (se 1 (by rfl) ⟨9297962, by rfl⟩ : syracuseStep 12397283 = 18595925) B18595925
theorem B8264855 : Blo 2175435 8264855 := bstep (se 1 (by rfl) ⟨6198641, by rfl⟩ : syracuseStep 8264855 = 12397283) B12397283
theorem B5509903 : Blo 2175435 5509903 := bstep (se 1 (by rfl) ⟨4132427, by rfl⟩ : syracuseStep 5509903 = 8264855) B8264855
theorem B7346537 : Blo 2175435 7346537 := bstep (se 2 (by rfl) ⟨2754951, by rfl⟩ : syracuseStep 7346537 = 5509903) B5509903
theorem B4897691 : Blo 2175435 4897691 := bstep (se 1 (by rfl) ⟨3673268, by rfl⟩ : syracuseStep 4897691 = 7346537) B7346537
theorem B3265127 : Blo 2175435 3265127 := bstep (se 1 (by rfl) ⟨2448845, by rfl⟩ : syracuseStep 3265127 = 4897691) B4897691
theorem B2176751 : Blo 2175435 2176751 := bstep (se 1 (by rfl) ⟨1632563, by rfl⟩ : syracuseStep 2176751 = 3265127) B3265127
theorem B3265133 : Blo 2175435 3265133 := bbase (se 3 (by rfl) ⟨612212, by rfl⟩ : syracuseStep 3265133 = 1224425) (by norm_num)
theorem B2176755 : Blo 2175435 2176755 := bstep (se 1 (by rfl) ⟨1632566, by rfl⟩ : syracuseStep 2176755 = 3265133) B3265133
theorem B4897709 : Blo 2175435 4897709 := bbase (se 3 (by rfl) ⟨918320, by rfl⟩ : syracuseStep 4897709 = 1836641) (by norm_num)
theorem B3265139 : Blo 2175435 3265139 := bstep (se 1 (by rfl) ⟨2448854, by rfl⟩ : syracuseStep 3265139 = 4897709) B4897709
theorem B2176759 : Blo 2175435 2176759 := bstep (se 1 (by rfl) ⟨1632569, by rfl⟩ : syracuseStep 2176759 = 3265139) B3265139
theorem B6198677 : Blo 2175435 6198677 := bbase (se 6 (by rfl) ⟨145281, by rfl⟩ : syracuseStep 6198677 = 290563) (by norm_num)
theorem B4132451 : Blo 2175435 4132451 := bstep (se 1 (by rfl) ⟨3099338, by rfl⟩ : syracuseStep 4132451 = 6198677) B6198677
theorem B2754967 : Blo 2175435 2754967 := bstep (se 1 (by rfl) ⟨2066225, by rfl⟩ : syracuseStep 2754967 = 4132451) B4132451
theorem B3673289 : Blo 2175435 3673289 := bstep (se 2 (by rfl) ⟨1377483, by rfl⟩ : syracuseStep 3673289 = 2754967) B2754967
theorem B2448859 : Blo 2175435 2448859 := bstep (se 1 (by rfl) ⟨1836644, by rfl⟩ : syracuseStep 2448859 = 3673289) B3673289
theorem B3265145 : Blo 2175435 3265145 := bstep (se 2 (by rfl) ⟨1224429, by rfl⟩ : syracuseStep 3265145 = 2448859) B2448859
theorem B2176763 : Blo 2175435 2176763 := bstep (se 1 (by rfl) ⟨1632572, by rfl⟩ : syracuseStep 2176763 = 3265145) B3265145
theorem B4412933 : Blo 2175435 4412933 := bbase (se 4 (by rfl) ⟨413712, by rfl⟩ : syracuseStep 4412933 = 827425) (by norm_num)
theorem B2941955 : Blo 2175435 2941955 := bstep (se 1 (by rfl) ⟨2206466, by rfl⟩ : syracuseStep 2941955 = 4412933) B4412933
theorem B31380853 : Blo 2175435 31380853 := bstep (se 5 (by rfl) ⟨1470977, by rfl⟩ : syracuseStep 31380853 = 2941955) B2941955
theorem B41841137 : Blo 2175435 41841137 := bstep (se 2 (by rfl) ⟨15690426, by rfl⟩ : syracuseStep 41841137 = 31380853) B31380853
theorem B27894091 : Blo 2175435 27894091 := bstep (se 1 (by rfl) ⟨20920568, by rfl⟩ : syracuseStep 27894091 = 41841137) B41841137
theorem B37192121 : Blo 2175435 37192121 := bstep (se 2 (by rfl) ⟨13947045, by rfl⟩ : syracuseStep 37192121 = 27894091) B27894091
theorem B24794747 : Blo 2175435 24794747 := bstep (se 1 (by rfl) ⟨18596060, by rfl⟩ : syracuseStep 24794747 = 37192121) B37192121
theorem B16529831 : Blo 2175435 16529831 := bstep (se 1 (by rfl) ⟨12397373, by rfl⟩ : syracuseStep 16529831 = 24794747) B24794747
theorem B11019887 : Blo 2175435 11019887 := bstep (se 1 (by rfl) ⟨8264915, by rfl⟩ : syracuseStep 11019887 = 16529831) B16529831
theorem B7346591 : Blo 2175435 7346591 := bstep (se 1 (by rfl) ⟨5509943, by rfl⟩ : syracuseStep 7346591 = 11019887) B11019887
theorem B4897727 : Blo 2175435 4897727 := bstep (se 1 (by rfl) ⟨3673295, by rfl⟩ : syracuseStep 4897727 = 7346591) B7346591
theorem B3265151 : Blo 2175435 3265151 := bstep (se 1 (by rfl) ⟨2448863, by rfl⟩ : syracuseStep 3265151 = 4897727) B4897727
theorem B2176767 : Blo 2175435 2176767 := bstep (se 1 (by rfl) ⟨1632575, by rfl⟩ : syracuseStep 2176767 = 3265151) B3265151
theorem B3265157 : Blo 2175435 3265157 := bbase (se 4 (by rfl) ⟨306108, by rfl⟩ : syracuseStep 3265157 = 612217) (by norm_num)
theorem B2176771 : Blo 2175435 2176771 := bstep (se 1 (by rfl) ⟨1632578, by rfl⟩ : syracuseStep 2176771 = 3265157) B3265157
theorem B3673309 : Blo 2175435 3673309 := bbase (se 3 (by rfl) ⟨688745, by rfl⟩ : syracuseStep 3673309 = 1377491) (by norm_num)
theorem B4897745 : Blo 2175435 4897745 := bstep (se 2 (by rfl) ⟨1836654, by rfl⟩ : syracuseStep 4897745 = 3673309) B3673309
theorem B3265163 : Blo 2175435 3265163 := bstep (se 1 (by rfl) ⟨2448872, by rfl⟩ : syracuseStep 3265163 = 4897745) B4897745
theorem B2176775 : Blo 2175435 2176775 := bstep (se 1 (by rfl) ⟨1632581, by rfl⟩ : syracuseStep 2176775 = 3265163) B3265163
theorem B2448877 : Blo 2175435 2448877 := bbase (se 3 (by rfl) ⟨459164, by rfl⟩ : syracuseStep 2448877 = 918329) (by norm_num)
theorem B3265169 : Blo 2175435 3265169 := bstep (se 2 (by rfl) ⟨1224438, by rfl⟩ : syracuseStep 3265169 = 2448877) B2448877
theorem B2176779 : Blo 2175435 2176779 := bstep (se 1 (by rfl) ⟨1632584, by rfl⟩ : syracuseStep 2176779 = 3265169) B3265169
theorem B7346645 : Blo 2175435 7346645 := bbase (se 7 (by rfl) ⟨86093, by rfl⟩ : syracuseStep 7346645 = 172187) (by norm_num)
theorem B4897763 : Blo 2175435 4897763 := bstep (se 1 (by rfl) ⟨3673322, by rfl⟩ : syracuseStep 4897763 = 7346645) B7346645
theorem B3265175 : Blo 2175435 3265175 := bstep (se 1 (by rfl) ⟨2448881, by rfl⟩ : syracuseStep 3265175 = 4897763) B4897763
theorem B2176783 : Blo 2175435 2176783 := bstep (se 1 (by rfl) ⟨1632587, by rfl⟩ : syracuseStep 2176783 = 3265175) B3265175
theorem B3265181 : Blo 2175435 3265181 := bbase (se 3 (by rfl) ⟨612221, by rfl⟩ : syracuseStep 3265181 = 1224443) (by norm_num)
theorem B2176787 : Blo 2175435 2176787 := bstep (se 1 (by rfl) ⟨1632590, by rfl⟩ : syracuseStep 2176787 = 3265181) B3265181
theorem B4897781 : Blo 2175435 4897781 := bbase (se 5 (by rfl) ⟨229583, by rfl⟩ : syracuseStep 4897781 = 459167) (by norm_num)
theorem B3265187 : Blo 2175435 3265187 := bstep (se 1 (by rfl) ⟨2448890, by rfl⟩ : syracuseStep 3265187 = 4897781) B4897781
theorem B2176791 : Blo 2175435 2176791 := bstep (se 1 (by rfl) ⟨1632593, by rfl⟩ : syracuseStep 2176791 = 3265187) B3265187
theorem B3723461 : Blo 2175435 3723461 := bbase (se 4 (by rfl) ⟨349074, by rfl⟩ : syracuseStep 3723461 = 698149) (by norm_num)
theorem B2482307 : Blo 2175435 2482307 := bstep (se 1 (by rfl) ⟨1861730, by rfl⟩ : syracuseStep 2482307 = 3723461) B3723461
theorem B26477941 : Blo 2175435 26477941 := bstep (se 5 (by rfl) ⟨1241153, by rfl⟩ : syracuseStep 26477941 = 2482307) B2482307
theorem B35303921 : Blo 2175435 35303921 := bstep (se 2 (by rfl) ⟨13238970, by rfl⟩ : syracuseStep 35303921 = 26477941) B26477941
theorem B23535947 : Blo 2175435 23535947 := bstep (se 1 (by rfl) ⟨17651960, by rfl⟩ : syracuseStep 23535947 = 35303921) B35303921
theorem B62762525 : Blo 2175435 62762525 := bstep (se 3 (by rfl) ⟨11767973, by rfl⟩ : syracuseStep 62762525 = 23535947) B23535947
theorem B41841683 : Blo 2175435 41841683 := bstep (se 1 (by rfl) ⟨31381262, by rfl⟩ : syracuseStep 41841683 = 62762525) B62762525
theorem B27894455 : Blo 2175435 27894455 := bstep (se 1 (by rfl) ⟨20920841, by rfl⟩ : syracuseStep 27894455 = 41841683) B41841683
theorem B18596303 : Blo 2175435 18596303 := bstep (se 1 (by rfl) ⟨13947227, by rfl⟩ : syracuseStep 18596303 = 27894455) B27894455
theorem B12397535 : Blo 2175435 12397535 := bstep (se 1 (by rfl) ⟨9298151, by rfl⟩ : syracuseStep 12397535 = 18596303) B18596303
theorem B8265023 : Blo 2175435 8265023 := bstep (se 1 (by rfl) ⟨6198767, by rfl⟩ : syracuseStep 8265023 = 12397535) B12397535
theorem B5510015 : Blo 2175435 5510015 := bstep (se 1 (by rfl) ⟨4132511, by rfl⟩ : syracuseStep 5510015 = 8265023) B8265023
theorem B3673343 : Blo 2175435 3673343 := bstep (se 1 (by rfl) ⟨2755007, by rfl⟩ : syracuseStep 3673343 = 5510015) B5510015
theorem B2448895 : Blo 2175435 2448895 := bstep (se 1 (by rfl) ⟨1836671, by rfl⟩ : syracuseStep 2448895 = 3673343) B3673343
theorem B3265193 : Blo 2175435 3265193 := bstep (se 2 (by rfl) ⟨1224447, by rfl⟩ : syracuseStep 3265193 = 2448895) B2448895
theorem B2176795 : Blo 2175435 2176795 := bstep (se 1 (by rfl) ⟨1632596, by rfl⟩ : syracuseStep 2176795 = 3265193) B3265193
theorem B3099389 : Blo 2175435 3099389 := bbase (se 3 (by rfl) ⟨581135, by rfl⟩ : syracuseStep 3099389 = 1162271) (by norm_num)
theorem B8265037 : Blo 2175435 8265037 := bstep (se 3 (by rfl) ⟨1549694, by rfl⟩ : syracuseStep 8265037 = 3099389) B3099389
theorem B11020049 : Blo 2175435 11020049 := bstep (se 2 (by rfl) ⟨4132518, by rfl⟩ : syracuseStep 11020049 = 8265037) B8265037
theorem B7346699 : Blo 2175435 7346699 := bstep (se 1 (by rfl) ⟨5510024, by rfl⟩ : syracuseStep 7346699 = 11020049) B11020049
theorem B4897799 : Blo 2175435 4897799 := bstep (se 1 (by rfl) ⟨3673349, by rfl⟩ : syracuseStep 4897799 = 7346699) B7346699
theorem B3265199 : Blo 2175435 3265199 := bstep (se 1 (by rfl) ⟨2448899, by rfl⟩ : syracuseStep 3265199 = 4897799) B4897799
theorem B2176799 : Blo 2175435 2176799 := bstep (se 1 (by rfl) ⟨1632599, by rfl⟩ : syracuseStep 2176799 = 3265199) B3265199
theorem B3265205 : Blo 2175435 3265205 := bbase (se 5 (by rfl) ⟨153056, by rfl⟩ : syracuseStep 3265205 = 306113) (by norm_num)
theorem B2176803 : Blo 2175435 2176803 := bstep (se 1 (by rfl) ⟨1632602, by rfl⟩ : syracuseStep 2176803 = 3265205) B3265205
theorem B5510045 : Blo 2175435 5510045 := bbase (se 3 (by rfl) ⟨1033133, by rfl⟩ : syracuseStep 5510045 = 2066267) (by norm_num)
theorem B3673363 : Blo 2175435 3673363 := bstep (se 1 (by rfl) ⟨2755022, by rfl⟩ : syracuseStep 3673363 = 5510045) B5510045
theorem B4897817 : Blo 2175435 4897817 := bstep (se 2 (by rfl) ⟨1836681, by rfl⟩ : syracuseStep 4897817 = 3673363) B3673363
theorem B3265211 : Blo 2175435 3265211 := bstep (se 1 (by rfl) ⟨2448908, by rfl⟩ : syracuseStep 3265211 = 4897817) B4897817
theorem B2176807 : Blo 2175435 2176807 := bstep (se 1 (by rfl) ⟨1632605, by rfl⟩ : syracuseStep 2176807 = 3265211) B3265211
theorem B2448913 : Blo 2175435 2448913 := bbase (se 2 (by rfl) ⟨918342, by rfl⟩ : syracuseStep 2448913 = 1836685) (by norm_num)
theorem B3265217 : Blo 2175435 3265217 := bstep (se 2 (by rfl) ⟨1224456, by rfl⟩ : syracuseStep 3265217 = 2448913) B2448913
theorem B2176811 : Blo 2175435 2176811 := bstep (se 1 (by rfl) ⟨1632608, by rfl⟩ : syracuseStep 2176811 = 3265217) B3265217
theorem B4132549 : Blo 2175435 4132549 := bbase (se 4 (by rfl) ⟨387426, by rfl⟩ : syracuseStep 4132549 = 774853) (by norm_num)
theorem B5510065 : Blo 2175435 5510065 := bstep (se 2 (by rfl) ⟨2066274, by rfl⟩ : syracuseStep 5510065 = 4132549) B4132549
theorem B7346753 : Blo 2175435 7346753 := bstep (se 2 (by rfl) ⟨2755032, by rfl⟩ : syracuseStep 7346753 = 5510065) B5510065
theorem B4897835 : Blo 2175435 4897835 := bstep (se 1 (by rfl) ⟨3673376, by rfl⟩ : syracuseStep 4897835 = 7346753) B7346753
theorem B3265223 : Blo 2175435 3265223 := bstep (se 1 (by rfl) ⟨2448917, by rfl⟩ : syracuseStep 3265223 = 4897835) B4897835
theorem B2176815 : Blo 2175435 2176815 := bstep (se 1 (by rfl) ⟨1632611, by rfl⟩ : syracuseStep 2176815 = 3265223) B3265223
theorem B3265229 : Blo 2175435 3265229 := bbase (se 3 (by rfl) ⟨612230, by rfl⟩ : syracuseStep 3265229 = 1224461) (by norm_num)
theorem B2176819 : Blo 2175435 2176819 := bstep (se 1 (by rfl) ⟨1632614, by rfl⟩ : syracuseStep 2176819 = 3265229) B3265229
theorem B4897853 : Blo 2175435 4897853 := bbase (se 3 (by rfl) ⟨918347, by rfl⟩ : syracuseStep 4897853 = 1836695) (by norm_num)
theorem B3265235 : Blo 2175435 3265235 := bstep (se 1 (by rfl) ⟨2448926, by rfl⟩ : syracuseStep 3265235 = 4897853) B4897853
theorem B2176823 : Blo 2175435 2176823 := bstep (se 1 (by rfl) ⟨1632617, by rfl⟩ : syracuseStep 2176823 = 3265235) B3265235
theorem B3673397 : Blo 2175435 3673397 := bbase (se 5 (by rfl) ⟨172190, by rfl⟩ : syracuseStep 3673397 = 344381) (by norm_num)
theorem B2448931 : Blo 2175435 2448931 := bstep (se 1 (by rfl) ⟨1836698, by rfl⟩ : syracuseStep 2448931 = 3673397) B3673397
theorem B3265241 : Blo 2175435 3265241 := bstep (se 2 (by rfl) ⟨1224465, by rfl⟩ : syracuseStep 3265241 = 2448931) B2448931
theorem B2176827 : Blo 2175435 2176827 := bstep (se 1 (by rfl) ⟨1632620, by rfl⟩ : syracuseStep 2176827 = 3265241) B3265241
theorem B6198869 : Blo 2175435 6198869 := bbase (se 8 (by rfl) ⟨36321, by rfl⟩ : syracuseStep 6198869 = 72643) (by norm_num)
theorem B16530317 : Blo 2175435 16530317 := bstep (se 3 (by rfl) ⟨3099434, by rfl⟩ : syracuseStep 16530317 = 6198869) B6198869
theorem B11020211 : Blo 2175435 11020211 := bstep (se 1 (by rfl) ⟨8265158, by rfl⟩ : syracuseStep 11020211 = 16530317) B16530317
theorem B7346807 : Blo 2175435 7346807 := bstep (se 1 (by rfl) ⟨5510105, by rfl⟩ : syracuseStep 7346807 = 11020211) B11020211
theorem B4897871 : Blo 2175435 4897871 := bstep (se 1 (by rfl) ⟨3673403, by rfl⟩ : syracuseStep 4897871 = 7346807) B7346807
theorem B3265247 : Blo 2175435 3265247 := bstep (se 1 (by rfl) ⟨2448935, by rfl⟩ : syracuseStep 3265247 = 4897871) B4897871
theorem B2176831 : Blo 2175435 2176831 := bstep (se 1 (by rfl) ⟨1632623, by rfl⟩ : syracuseStep 2176831 = 3265247) B3265247
theorem B3265253 : Blo 2175435 3265253 := bbase (se 4 (by rfl) ⟨306117, by rfl⟩ : syracuseStep 3265253 = 612235) (by norm_num)
theorem B2176835 : Blo 2175435 2176835 := bstep (se 1 (by rfl) ⟨1632626, by rfl⟩ : syracuseStep 2176835 = 3265253) B3265253
theorem B2324585 : Blo 2175435 2324585 := bbase (se 2 (by rfl) ⟨871719, by rfl⟩ : syracuseStep 2324585 = 1743439) (by norm_num)
theorem B6198893 : Blo 2175435 6198893 := bstep (se 3 (by rfl) ⟨1162292, by rfl⟩ : syracuseStep 6198893 = 2324585) B2324585
theorem B4132595 : Blo 2175435 4132595 := bstep (se 1 (by rfl) ⟨3099446, by rfl⟩ : syracuseStep 4132595 = 6198893) B6198893
theorem B2755063 : Blo 2175435 2755063 := bstep (se 1 (by rfl) ⟨2066297, by rfl⟩ : syracuseStep 2755063 = 4132595) B4132595
theorem B3673417 : Blo 2175435 3673417 := bstep (se 2 (by rfl) ⟨1377531, by rfl⟩ : syracuseStep 3673417 = 2755063) B2755063
theorem B4897889 : Blo 2175435 4897889 := bstep (se 2 (by rfl) ⟨1836708, by rfl⟩ : syracuseStep 4897889 = 3673417) B3673417
theorem B3265259 : Blo 2175435 3265259 := bstep (se 1 (by rfl) ⟨2448944, by rfl⟩ : syracuseStep 3265259 = 4897889) B4897889
theorem B2176839 : Blo 2175435 2176839 := bstep (se 1 (by rfl) ⟨1632629, by rfl⟩ : syracuseStep 2176839 = 3265259) B3265259
theorem B2448949 : Blo 2175435 2448949 := bbase (se 5 (by rfl) ⟨114794, by rfl⟩ : syracuseStep 2448949 = 229589) (by norm_num)
theorem B3265265 : Blo 2175435 3265265 := bstep (se 2 (by rfl) ⟨1224474, by rfl⟩ : syracuseStep 3265265 = 2448949) B2448949
theorem B2176843 : Blo 2175435 2176843 := bstep (se 1 (by rfl) ⟨1632632, by rfl⟩ : syracuseStep 2176843 = 3265265) B3265265
theorem B2755073 : Blo 2175435 2755073 := bbase (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) (by norm_num)
theorem B7346861 : Blo 2175435 7346861 := bstep (se 3 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 7346861 = 2755073) B2755073
theorem B4897907 : Blo 2175435 4897907 := bstep (se 1 (by rfl) ⟨3673430, by rfl⟩ : syracuseStep 4897907 = 7346861) B7346861
theorem B3265271 : Blo 2175435 3265271 := bstep (se 1 (by rfl) ⟨2448953, by rfl⟩ : syracuseStep 3265271 = 4897907) B4897907
theorem B2176847 : Blo 2175435 2176847 := bstep (se 1 (by rfl) ⟨1632635, by rfl⟩ : syracuseStep 2176847 = 3265271) B3265271
theorem B3265277 : Blo 2175435 3265277 := bbase (se 3 (by rfl) ⟨612239, by rfl⟩ : syracuseStep 3265277 = 1224479) (by norm_num)
theorem B2176851 : Blo 2175435 2176851 := bstep (se 1 (by rfl) ⟨1632638, by rfl⟩ : syracuseStep 2176851 = 3265277) B3265277
theorem B4897925 : Blo 2175435 4897925 := bbase (se 4 (by rfl) ⟨459180, by rfl⟩ : syracuseStep 4897925 = 918361) (by norm_num)
theorem B3265283 : Blo 2175435 3265283 := bstep (se 1 (by rfl) ⟨2448962, by rfl⟩ : syracuseStep 3265283 = 4897925) B4897925
theorem B2176855 : Blo 2175435 2176855 := bstep (se 1 (by rfl) ⟨1632641, by rfl⟩ : syracuseStep 2176855 = 3265283) B3265283
theorem B4649213 : Blo 2175435 4649213 := bbase (se 3 (by rfl) ⟨871727, by rfl⟩ : syracuseStep 4649213 = 1743455) (by norm_num)
theorem B3099475 : Blo 2175435 3099475 := bstep (se 1 (by rfl) ⟨2324606, by rfl⟩ : syracuseStep 3099475 = 4649213) B4649213
theorem B4132633 : Blo 2175435 4132633 := bstep (se 2 (by rfl) ⟨1549737, by rfl⟩ : syracuseStep 4132633 = 3099475) B3099475
theorem B5510177 : Blo 2175435 5510177 := bstep (se 2 (by rfl) ⟨2066316, by rfl⟩ : syracuseStep 5510177 = 4132633) B4132633
theorem B3673451 : Blo 2175435 3673451 := bstep (se 1 (by rfl) ⟨2755088, by rfl⟩ : syracuseStep 3673451 = 5510177) B5510177
theorem B2448967 : Blo 2175435 2448967 := bstep (se 1 (by rfl) ⟨1836725, by rfl⟩ : syracuseStep 2448967 = 3673451) B3673451
theorem B3265289 : Blo 2175435 3265289 := bstep (se 2 (by rfl) ⟨1224483, by rfl⟩ : syracuseStep 3265289 = 2448967) B2448967
theorem B2176859 : Blo 2175435 2176859 := bstep (se 1 (by rfl) ⟨1632644, by rfl⟩ : syracuseStep 2176859 = 3265289) B3265289
theorem B11020373 : Blo 2175435 11020373 := bbase (se 8 (by rfl) ⟨64572, by rfl⟩ : syracuseStep 11020373 = 129145) (by norm_num)
theorem B7346915 : Blo 2175435 7346915 := bstep (se 1 (by rfl) ⟨5510186, by rfl⟩ : syracuseStep 7346915 = 11020373) B11020373
theorem B4897943 : Blo 2175435 4897943 := bstep (se 1 (by rfl) ⟨3673457, by rfl⟩ : syracuseStep 4897943 = 7346915) B7346915
theorem B3265295 : Blo 2175435 3265295 := bstep (se 1 (by rfl) ⟨2448971, by rfl⟩ : syracuseStep 3265295 = 4897943) B4897943
theorem B2176863 : Blo 2175435 2176863 := bstep (se 1 (by rfl) ⟨1632647, by rfl⟩ : syracuseStep 2176863 = 3265295) B3265295
theorem B3265301 : Blo 2175435 3265301 := bbase (se 6 (by rfl) ⟨76530, by rfl⟩ : syracuseStep 3265301 = 153061) (by norm_num)
theorem B2176867 : Blo 2175435 2176867 := bstep (se 1 (by rfl) ⟨1632650, by rfl⟩ : syracuseStep 2176867 = 3265301) B3265301
theorem B7845589 : Blo 2175435 7845589 := bbase (se 7 (by rfl) ⟨91940, by rfl⟩ : syracuseStep 7845589 = 183881) (by norm_num)
theorem B41843141 : Blo 2175435 41843141 := bstep (se 4 (by rfl) ⟨3922794, by rfl⟩ : syracuseStep 41843141 = 7845589) B7845589
theorem B27895427 : Blo 2175435 27895427 := bstep (se 1 (by rfl) ⟨20921570, by rfl⟩ : syracuseStep 27895427 = 41843141) B41843141
theorem B18596951 : Blo 2175435 18596951 := bstep (se 1 (by rfl) ⟨13947713, by rfl⟩ : syracuseStep 18596951 = 27895427) B27895427
theorem B12397967 : Blo 2175435 12397967 := bstep (se 1 (by rfl) ⟨9298475, by rfl⟩ : syracuseStep 12397967 = 18596951) B18596951
theorem B8265311 : Blo 2175435 8265311 := bstep (se 1 (by rfl) ⟨6198983, by rfl⟩ : syracuseStep 8265311 = 12397967) B12397967
theorem B5510207 : Blo 2175435 5510207 := bstep (se 1 (by rfl) ⟨4132655, by rfl⟩ : syracuseStep 5510207 = 8265311) B8265311
theorem B3673471 : Blo 2175435 3673471 := bstep (se 1 (by rfl) ⟨2755103, by rfl⟩ : syracuseStep 3673471 = 5510207) B5510207
theorem B4897961 : Blo 2175435 4897961 := bstep (se 2 (by rfl) ⟨1836735, by rfl⟩ : syracuseStep 4897961 = 3673471) B3673471
theorem B3265307 : Blo 2175435 3265307 := bstep (se 1 (by rfl) ⟨2448980, by rfl⟩ : syracuseStep 3265307 = 4897961) B4897961
theorem B2176871 : Blo 2175435 2176871 := bstep (se 1 (by rfl) ⟨1632653, by rfl⟩ : syracuseStep 2176871 = 3265307) B3265307
theorem B2448985 : Blo 2175435 2448985 := bbase (se 2 (by rfl) ⟨918369, by rfl⟩ : syracuseStep 2448985 = 1836739) (by norm_num)
theorem B3265313 : Blo 2175435 3265313 := bstep (se 2 (by rfl) ⟨1224492, by rfl⟩ : syracuseStep 3265313 = 2448985) B2448985
theorem B2176875 : Blo 2175435 2176875 := bstep (se 1 (by rfl) ⟨1632656, by rfl⟩ : syracuseStep 2176875 = 3265313) B3265313
theorem B3534517 : Blo 2175435 3534517 := bbase (se 5 (by rfl) ⟨165680, by rfl⟩ : syracuseStep 3534517 = 331361) (by norm_num)
theorem B4712689 : Blo 2175435 4712689 := bstep (se 2 (by rfl) ⟨1767258, by rfl⟩ : syracuseStep 4712689 = 3534517) B3534517
theorem B6283585 : Blo 2175435 6283585 := bstep (se 2 (by rfl) ⟨2356344, by rfl⟩ : syracuseStep 6283585 = 4712689) B4712689
theorem B8378113 : Blo 2175435 8378113 := bstep (se 2 (by rfl) ⟨3141792, by rfl⟩ : syracuseStep 8378113 = 6283585) B6283585
theorem B11170817 : Blo 2175435 11170817 := bstep (se 2 (by rfl) ⟨4189056, by rfl⟩ : syracuseStep 11170817 = 8378113) B8378113
theorem B7447211 : Blo 2175435 7447211 := bstep (se 1 (by rfl) ⟨5585408, by rfl⟩ : syracuseStep 7447211 = 11170817) B11170817
theorem B4964807 : Blo 2175435 4964807 := bstep (se 1 (by rfl) ⟨3723605, by rfl⟩ : syracuseStep 4964807 = 7447211) B7447211
theorem B3309871 : Blo 2175435 3309871 := bstep (se 1 (by rfl) ⟨2482403, by rfl⟩ : syracuseStep 3309871 = 4964807) B4964807
theorem B4413161 : Blo 2175435 4413161 := bstep (se 2 (by rfl) ⟨1654935, by rfl⟩ : syracuseStep 4413161 = 3309871) B3309871
theorem B11768429 : Blo 2175435 11768429 := bstep (se 3 (by rfl) ⟨2206580, by rfl⟩ : syracuseStep 11768429 = 4413161) B4413161
theorem B7845619 : Blo 2175435 7845619 := bstep (se 1 (by rfl) ⟨5884214, by rfl⟩ : syracuseStep 7845619 = 11768429) B11768429
theorem B10460825 : Blo 2175435 10460825 := bstep (se 2 (by rfl) ⟨3922809, by rfl⟩ : syracuseStep 10460825 = 7845619) B7845619
theorem B6973883 : Blo 2175435 6973883 := bstep (se 1 (by rfl) ⟨5230412, by rfl⟩ : syracuseStep 6973883 = 10460825) B10460825
theorem B4649255 : Blo 2175435 4649255 := bstep (se 1 (by rfl) ⟨3486941, by rfl⟩ : syracuseStep 4649255 = 6973883) B6973883
theorem B3099503 : Blo 2175435 3099503 := bstep (se 1 (by rfl) ⟨2324627, by rfl⟩ : syracuseStep 3099503 = 4649255) B4649255
theorem B8265341 : Blo 2175435 8265341 := bstep (se 3 (by rfl) ⟨1549751, by rfl⟩ : syracuseStep 8265341 = 3099503) B3099503
theorem B5510227 : Blo 2175435 5510227 := bstep (se 1 (by rfl) ⟨4132670, by rfl⟩ : syracuseStep 5510227 = 8265341) B8265341
theorem B7346969 : Blo 2175435 7346969 := bstep (se 2 (by rfl) ⟨2755113, by rfl⟩ : syracuseStep 7346969 = 5510227) B5510227
theorem B4897979 : Blo 2175435 4897979 := bstep (se 1 (by rfl) ⟨3673484, by rfl⟩ : syracuseStep 4897979 = 7346969) B7346969
theorem B3265319 : Blo 2175435 3265319 := bstep (se 1 (by rfl) ⟨2448989, by rfl⟩ : syracuseStep 3265319 = 4897979) B4897979
theorem B2176879 : Blo 2175435 2176879 := bstep (se 1 (by rfl) ⟨1632659, by rfl⟩ : syracuseStep 2176879 = 3265319) B3265319
theorem B3265325 : Blo 2175435 3265325 := bbase (se 3 (by rfl) ⟨612248, by rfl⟩ : syracuseStep 3265325 = 1224497) (by norm_num)
theorem B2176883 : Blo 2175435 2176883 := bstep (se 1 (by rfl) ⟨1632662, by rfl⟩ : syracuseStep 2176883 = 3265325) B3265325
theorem B4897997 : Blo 2175435 4897997 := bbase (se 3 (by rfl) ⟨918374, by rfl⟩ : syracuseStep 4897997 = 1836749) (by norm_num)
theorem B3265331 : Blo 2175435 3265331 := bstep (se 1 (by rfl) ⟨2448998, by rfl⟩ : syracuseStep 3265331 = 4897997) B4897997
theorem B2176887 : Blo 2175435 2176887 := bstep (se 1 (by rfl) ⟨1632665, by rfl⟩ : syracuseStep 2176887 = 3265331) B3265331
theorem B2755129 : Blo 2175435 2755129 := bbase (se 2 (by rfl) ⟨1033173, by rfl⟩ : syracuseStep 2755129 = 2066347) (by norm_num)
theorem B3673505 : Blo 2175435 3673505 := bstep (se 2 (by rfl) ⟨1377564, by rfl⟩ : syracuseStep 3673505 = 2755129) B2755129
theorem B2449003 : Blo 2175435 2449003 := bstep (se 1 (by rfl) ⟨1836752, by rfl⟩ : syracuseStep 2449003 = 3673505) B3673505
theorem B3265337 : Blo 2175435 3265337 := bstep (se 2 (by rfl) ⟨1224501, by rfl⟩ : syracuseStep 3265337 = 2449003) B2449003
theorem B2176891 : Blo 2175435 2176891 := bstep (se 1 (by rfl) ⟨1632668, by rfl⟩ : syracuseStep 2176891 = 3265337) B3265337
theorem B2615225 : Blo 2175435 2615225 := bbase (se 2 (by rfl) ⟨980709, by rfl⟩ : syracuseStep 2615225 = 1961419) (by norm_num)
theorem B6973933 : Blo 2175435 6973933 := bstep (se 3 (by rfl) ⟨1307612, by rfl⟩ : syracuseStep 6973933 = 2615225) B2615225
theorem B9298577 : Blo 2175435 9298577 := bstep (se 2 (by rfl) ⟨3486966, by rfl⟩ : syracuseStep 9298577 = 6973933) B6973933
theorem B24796205 : Blo 2175435 24796205 := bstep (se 3 (by rfl) ⟨4649288, by rfl⟩ : syracuseStep 24796205 = 9298577) B9298577
theorem B16530803 : Blo 2175435 16530803 := bstep (se 1 (by rfl) ⟨12398102, by rfl⟩ : syracuseStep 16530803 = 24796205) B24796205
theorem B11020535 : Blo 2175435 11020535 := bstep (se 1 (by rfl) ⟨8265401, by rfl⟩ : syracuseStep 11020535 = 16530803) B16530803
theorem B7347023 : Blo 2175435 7347023 := bstep (se 1 (by rfl) ⟨5510267, by rfl⟩ : syracuseStep 7347023 = 11020535) B11020535
theorem B4898015 : Blo 2175435 4898015 := bstep (se 1 (by rfl) ⟨3673511, by rfl⟩ : syracuseStep 4898015 = 7347023) B7347023
theorem B3265343 : Blo 2175435 3265343 := bstep (se 1 (by rfl) ⟨2449007, by rfl⟩ : syracuseStep 3265343 = 4898015) B4898015
theorem B2176895 : Blo 2175435 2176895 := bstep (se 1 (by rfl) ⟨1632671, by rfl⟩ : syracuseStep 2176895 = 3265343) B3265343
theorem B3265349 : Blo 2175435 3265349 := bbase (se 4 (by rfl) ⟨306126, by rfl⟩ : syracuseStep 3265349 = 612253) (by norm_num)
theorem B2176899 : Blo 2175435 2176899 := bstep (se 1 (by rfl) ⟨1632674, by rfl⟩ : syracuseStep 2176899 = 3265349) B3265349
theorem B3673525 : Blo 2175435 3673525 := bbase (se 5 (by rfl) ⟨172196, by rfl⟩ : syracuseStep 3673525 = 344393) (by norm_num)
theorem B4898033 : Blo 2175435 4898033 := bstep (se 2 (by rfl) ⟨1836762, by rfl⟩ : syracuseStep 4898033 = 3673525) B3673525
theorem B3265355 : Blo 2175435 3265355 := bstep (se 1 (by rfl) ⟨2449016, by rfl⟩ : syracuseStep 3265355 = 4898033) B4898033
theorem B2176903 : Blo 2175435 2176903 := bstep (se 1 (by rfl) ⟨1632677, by rfl⟩ : syracuseStep 2176903 = 3265355) B3265355
theorem B2449021 : Blo 2175435 2449021 := bbase (se 3 (by rfl) ⟨459191, by rfl⟩ : syracuseStep 2449021 = 918383) (by norm_num)
theorem B3265361 : Blo 2175435 3265361 := bstep (se 2 (by rfl) ⟨1224510, by rfl⟩ : syracuseStep 3265361 = 2449021) B2449021
theorem B2176907 : Blo 2175435 2176907 := bstep (se 1 (by rfl) ⟨1632680, by rfl⟩ : syracuseStep 2176907 = 3265361) B3265361
theorem B7347077 : Blo 2175435 7347077 := bbase (se 4 (by rfl) ⟨688788, by rfl⟩ : syracuseStep 7347077 = 1377577) (by norm_num)
theorem B4898051 : Blo 2175435 4898051 := bstep (se 1 (by rfl) ⟨3673538, by rfl⟩ : syracuseStep 4898051 = 7347077) B7347077
theorem B3265367 : Blo 2175435 3265367 := bstep (se 1 (by rfl) ⟨2449025, by rfl⟩ : syracuseStep 3265367 = 4898051) B4898051
theorem B2176911 : Blo 2175435 2176911 := bstep (se 1 (by rfl) ⟨1632683, by rfl⟩ : syracuseStep 2176911 = 3265367) B3265367
theorem B3265373 : Blo 2175435 3265373 := bbase (se 3 (by rfl) ⟨612257, by rfl⟩ : syracuseStep 3265373 = 1224515) (by norm_num)
theorem B2176915 : Blo 2175435 2176915 := bstep (se 1 (by rfl) ⟨1632686, by rfl⟩ : syracuseStep 2176915 = 3265373) B3265373
theorem B4898069 : Blo 2175435 4898069 := bbase (se 6 (by rfl) ⟨114798, by rfl⟩ : syracuseStep 4898069 = 229597) (by norm_num)
theorem B3265379 : Blo 2175435 3265379 := bstep (se 1 (by rfl) ⟨2449034, by rfl⟩ : syracuseStep 3265379 = 4898069) B4898069
theorem B2176919 : Blo 2175435 2176919 := bstep (se 1 (by rfl) ⟨1632689, by rfl⟩ : syracuseStep 2176919 = 3265379) B3265379
theorem B8265509 : Blo 2175435 8265509 := bbase (se 4 (by rfl) ⟨774891, by rfl⟩ : syracuseStep 8265509 = 1549783) (by norm_num)
theorem B5510339 : Blo 2175435 5510339 := bstep (se 1 (by rfl) ⟨4132754, by rfl⟩ : syracuseStep 5510339 = 8265509) B8265509
theorem B3673559 : Blo 2175435 3673559 := bstep (se 1 (by rfl) ⟨2755169, by rfl⟩ : syracuseStep 3673559 = 5510339) B5510339
theorem B2449039 : Blo 2175435 2449039 := bstep (se 1 (by rfl) ⟨1836779, by rfl⟩ : syracuseStep 2449039 = 3673559) B3673559
theorem B3265385 : Blo 2175435 3265385 := bstep (se 2 (by rfl) ⟨1224519, by rfl⟩ : syracuseStep 3265385 = 2449039) B2449039
theorem B2176923 : Blo 2175435 2176923 := bstep (se 1 (by rfl) ⟨1632692, by rfl⟩ : syracuseStep 2176923 = 3265385) B3265385
theorem B4649357 : Blo 2175435 4649357 := bbase (se 3 (by rfl) ⟨871754, by rfl⟩ : syracuseStep 4649357 = 1743509) (by norm_num)
theorem B12398285 : Blo 2175435 12398285 := bstep (se 3 (by rfl) ⟨2324678, by rfl⟩ : syracuseStep 12398285 = 4649357) B4649357
theorem B8265523 : Blo 2175435 8265523 := bstep (se 1 (by rfl) ⟨6199142, by rfl⟩ : syracuseStep 8265523 = 12398285) B12398285
theorem B11020697 : Blo 2175435 11020697 := bstep (se 2 (by rfl) ⟨4132761, by rfl⟩ : syracuseStep 11020697 = 8265523) B8265523
theorem B7347131 : Blo 2175435 7347131 := bstep (se 1 (by rfl) ⟨5510348, by rfl⟩ : syracuseStep 7347131 = 11020697) B11020697
theorem B4898087 : Blo 2175435 4898087 := bstep (se 1 (by rfl) ⟨3673565, by rfl⟩ : syracuseStep 4898087 = 7347131) B7347131
theorem B3265391 : Blo 2175435 3265391 := bstep (se 1 (by rfl) ⟨2449043, by rfl⟩ : syracuseStep 3265391 = 4898087) B4898087
theorem B2176927 : Blo 2175435 2176927 := bstep (se 1 (by rfl) ⟨1632695, by rfl⟩ : syracuseStep 2176927 = 3265391) B3265391
theorem B3265397 : Blo 2175435 3265397 := bbase (se 5 (by rfl) ⟨153065, by rfl⟩ : syracuseStep 3265397 = 306131) (by norm_num)
theorem B2176931 : Blo 2175435 2176931 := bstep (se 1 (by rfl) ⟨1632698, by rfl⟩ : syracuseStep 2176931 = 3265397) B3265397
theorem B11929301 : Blo 2175435 11929301 := bbase (se 7 (by rfl) ⟨139796, by rfl⟩ : syracuseStep 11929301 = 279593) (by norm_num)
theorem B7952867 : Blo 2175435 7952867 := bstep (se 1 (by rfl) ⟨5964650, by rfl⟩ : syracuseStep 7952867 = 11929301) B11929301
theorem B5301911 : Blo 2175435 5301911 := bstep (se 1 (by rfl) ⟨3976433, by rfl⟩ : syracuseStep 5301911 = 7952867) B7952867
theorem B3534607 : Blo 2175435 3534607 := bstep (se 1 (by rfl) ⟨2650955, by rfl⟩ : syracuseStep 3534607 = 5301911) B5301911
theorem B18851237 : Blo 2175435 18851237 := bstep (se 4 (by rfl) ⟨1767303, by rfl⟩ : syracuseStep 18851237 = 3534607) B3534607
theorem B12567491 : Blo 2175435 12567491 := bstep (se 1 (by rfl) ⟨9425618, by rfl⟩ : syracuseStep 12567491 = 18851237) B18851237
theorem B8378327 : Blo 2175435 8378327 := bstep (se 1 (by rfl) ⟨6283745, by rfl⟩ : syracuseStep 8378327 = 12567491) B12567491
theorem B22342205 : Blo 2175435 22342205 := bstep (se 3 (by rfl) ⟨4189163, by rfl⟩ : syracuseStep 22342205 = 8378327) B8378327
theorem B14894803 : Blo 2175435 14894803 := bstep (se 1 (by rfl) ⟨11171102, by rfl⟩ : syracuseStep 14894803 = 22342205) B22342205
theorem B19859737 : Blo 2175435 19859737 := bstep (se 2 (by rfl) ⟨7447401, by rfl⟩ : syracuseStep 19859737 = 14894803) B14894803
theorem B26479649 : Blo 2175435 26479649 := bstep (se 2 (by rfl) ⟨9929868, by rfl⟩ : syracuseStep 26479649 = 19859737) B19859737
theorem B17653099 : Blo 2175435 17653099 := bstep (se 1 (by rfl) ⟨13239824, by rfl⟩ : syracuseStep 17653099 = 26479649) B26479649
theorem B23537465 : Blo 2175435 23537465 := bstep (se 2 (by rfl) ⟨8826549, by rfl⟩ : syracuseStep 23537465 = 17653099) B17653099
theorem B15691643 : Blo 2175435 15691643 := bstep (se 1 (by rfl) ⟨11768732, by rfl⟩ : syracuseStep 15691643 = 23537465) B23537465
theorem B10461095 : Blo 2175435 10461095 := bstep (se 1 (by rfl) ⟨7845821, by rfl⟩ : syracuseStep 10461095 = 15691643) B15691643
theorem B6974063 : Blo 2175435 6974063 := bstep (se 1 (by rfl) ⟨5230547, by rfl⟩ : syracuseStep 6974063 = 10461095) B10461095
theorem B4649375 : Blo 2175435 4649375 := bstep (se 1 (by rfl) ⟨3487031, by rfl⟩ : syracuseStep 4649375 = 6974063) B6974063
theorem B3099583 : Blo 2175435 3099583 := bstep (se 1 (by rfl) ⟨2324687, by rfl⟩ : syracuseStep 3099583 = 4649375) B4649375
theorem B4132777 : Blo 2175435 4132777 := bstep (se 2 (by rfl) ⟨1549791, by rfl⟩ : syracuseStep 4132777 = 3099583) B3099583
theorem B5510369 : Blo 2175435 5510369 := bstep (se 2 (by rfl) ⟨2066388, by rfl⟩ : syracuseStep 5510369 = 4132777) B4132777
theorem B3673579 : Blo 2175435 3673579 := bstep (se 1 (by rfl) ⟨2755184, by rfl⟩ : syracuseStep 3673579 = 5510369) B5510369
theorem B4898105 : Blo 2175435 4898105 := bstep (se 2 (by rfl) ⟨1836789, by rfl⟩ : syracuseStep 4898105 = 3673579) B3673579
theorem B3265403 : Blo 2175435 3265403 := bstep (se 1 (by rfl) ⟨2449052, by rfl⟩ : syracuseStep 3265403 = 4898105) B4898105
theorem B2176935 : Blo 2175435 2176935 := bstep (se 1 (by rfl) ⟨1632701, by rfl⟩ : syracuseStep 2176935 = 3265403) B3265403
theorem B2449057 : Blo 2175435 2449057 := bbase (se 2 (by rfl) ⟨918396, by rfl⟩ : syracuseStep 2449057 = 1836793) (by norm_num)
theorem B3265409 : Blo 2175435 3265409 := bstep (se 2 (by rfl) ⟨1224528, by rfl⟩ : syracuseStep 3265409 = 2449057) B2449057
theorem B2176939 : Blo 2175435 2176939 := bstep (se 1 (by rfl) ⟨1632704, by rfl⟩ : syracuseStep 2176939 = 3265409) B3265409
theorem B5510389 : Blo 2175435 5510389 := bbase (se 5 (by rfl) ⟨258299, by rfl⟩ : syracuseStep 5510389 = 516599) (by norm_num)
theorem B7347185 : Blo 2175435 7347185 := bstep (se 2 (by rfl) ⟨2755194, by rfl⟩ : syracuseStep 7347185 = 5510389) B5510389
theorem B4898123 : Blo 2175435 4898123 := bstep (se 1 (by rfl) ⟨3673592, by rfl⟩ : syracuseStep 4898123 = 7347185) B7347185
theorem B3265415 : Blo 2175435 3265415 := bstep (se 1 (by rfl) ⟨2449061, by rfl⟩ : syracuseStep 3265415 = 4898123) B4898123
theorem B2176943 : Blo 2175435 2176943 := bstep (se 1 (by rfl) ⟨1632707, by rfl⟩ : syracuseStep 2176943 = 3265415) B3265415
theorem B3265421 : Blo 2175435 3265421 := bbase (se 3 (by rfl) ⟨612266, by rfl⟩ : syracuseStep 3265421 = 1224533) (by norm_num)
theorem B2176947 : Blo 2175435 2176947 := bstep (se 1 (by rfl) ⟨1632710, by rfl⟩ : syracuseStep 2176947 = 3265421) B3265421
theorem B4898141 : Blo 2175435 4898141 := bbase (se 3 (by rfl) ⟨918401, by rfl⟩ : syracuseStep 4898141 = 1836803) (by norm_num)
theorem B3265427 : Blo 2175435 3265427 := bstep (se 1 (by rfl) ⟨2449070, by rfl⟩ : syracuseStep 3265427 = 4898141) B4898141
theorem B2176951 : Blo 2175435 2176951 := bstep (se 1 (by rfl) ⟨1632713, by rfl⟩ : syracuseStep 2176951 = 3265427) B3265427
theorem B3673613 : Blo 2175435 3673613 := bbase (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) (by norm_num)
theorem B2449075 : Blo 2175435 2449075 := bstep (se 1 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 2449075 = 3673613) B3673613
theorem B3265433 : Blo 2175435 3265433 := bstep (se 2 (by rfl) ⟨1224537, by rfl⟩ : syracuseStep 3265433 = 2449075) B2449075
theorem B2176955 : Blo 2175435 2176955 := bstep (se 1 (by rfl) ⟨1632716, by rfl⟩ : syracuseStep 2176955 = 3265433) B3265433
theorem B3487069 : Blo 2175435 3487069 := bbase (se 3 (by rfl) ⟨653825, by rfl⟩ : syracuseStep 3487069 = 1307651) (by norm_num)
theorem B18597701 : Blo 2175435 18597701 := bstep (se 4 (by rfl) ⟨1743534, by rfl⟩ : syracuseStep 18597701 = 3487069) B3487069
theorem B12398467 : Blo 2175435 12398467 := bstep (se 1 (by rfl) ⟨9298850, by rfl⟩ : syracuseStep 12398467 = 18597701) B18597701
theorem B16531289 : Blo 2175435 16531289 := bstep (se 2 (by rfl) ⟨6199233, by rfl⟩ : syracuseStep 16531289 = 12398467) B12398467
theorem B11020859 : Blo 2175435 11020859 := bstep (se 1 (by rfl) ⟨8265644, by rfl⟩ : syracuseStep 11020859 = 16531289) B16531289
theorem B7347239 : Blo 2175435 7347239 := bstep (se 1 (by rfl) ⟨5510429, by rfl⟩ : syracuseStep 7347239 = 11020859) B11020859
theorem B4898159 : Blo 2175435 4898159 := bstep (se 1 (by rfl) ⟨3673619, by rfl⟩ : syracuseStep 4898159 = 7347239) B7347239
theorem B3265439 : Blo 2175435 3265439 := bstep (se 1 (by rfl) ⟨2449079, by rfl⟩ : syracuseStep 3265439 = 4898159) B4898159
theorem B2176959 : Blo 2175435 2176959 := bstep (se 1 (by rfl) ⟨1632719, by rfl⟩ : syracuseStep 2176959 = 3265439) B3265439
theorem B3265445 : Blo 2175435 3265445 := bbase (se 4 (by rfl) ⟨306135, by rfl⟩ : syracuseStep 3265445 = 612271) (by norm_num)
theorem B2176963 : Blo 2175435 2176963 := bstep (se 1 (by rfl) ⟨1632722, by rfl⟩ : syracuseStep 2176963 = 3265445) B3265445
theorem B2755225 : Blo 2175435 2755225 := bbase (se 2 (by rfl) ⟨1033209, by rfl⟩ : syracuseStep 2755225 = 2066419) (by norm_num)
theorem B3673633 : Blo 2175435 3673633 := bstep (se 2 (by rfl) ⟨1377612, by rfl⟩ : syracuseStep 3673633 = 2755225) B2755225
theorem B4898177 : Blo 2175435 4898177 := bstep (se 2 (by rfl) ⟨1836816, by rfl⟩ : syracuseStep 4898177 = 3673633) B3673633
theorem B3265451 : Blo 2175435 3265451 := bstep (se 1 (by rfl) ⟨2449088, by rfl⟩ : syracuseStep 3265451 = 4898177) B4898177
theorem B2176967 : Blo 2175435 2176967 := bstep (se 1 (by rfl) ⟨1632725, by rfl⟩ : syracuseStep 2176967 = 3265451) B3265451
theorem B2449093 : Blo 2175435 2449093 := bbase (se 4 (by rfl) ⟨229602, by rfl⟩ : syracuseStep 2449093 = 459205) (by norm_num)
theorem B3265457 : Blo 2175435 3265457 := bstep (se 2 (by rfl) ⟨1224546, by rfl⟩ : syracuseStep 3265457 = 2449093) B2449093
theorem B2176971 : Blo 2175435 2176971 := bstep (se 1 (by rfl) ⟨1632728, by rfl⟩ : syracuseStep 2176971 = 3265457) B3265457
theorem B4132853 : Blo 2175435 4132853 := bbase (se 5 (by rfl) ⟨193727, by rfl⟩ : syracuseStep 4132853 = 387455) (by norm_num)
theorem B2755235 : Blo 2175435 2755235 := bstep (se 1 (by rfl) ⟨2066426, by rfl⟩ : syracuseStep 2755235 = 4132853) B4132853
theorem B7347293 : Blo 2175435 7347293 := bstep (se 3 (by rfl) ⟨1377617, by rfl⟩ : syracuseStep 7347293 = 2755235) B2755235
theorem B4898195 : Blo 2175435 4898195 := bstep (se 1 (by rfl) ⟨3673646, by rfl⟩ : syracuseStep 4898195 = 7347293) B7347293
theorem B3265463 : Blo 2175435 3265463 := bstep (se 1 (by rfl) ⟨2449097, by rfl⟩ : syracuseStep 3265463 = 4898195) B4898195
theorem B2176975 : Blo 2175435 2176975 := bstep (se 1 (by rfl) ⟨1632731, by rfl⟩ : syracuseStep 2176975 = 3265463) B3265463
theorem B3265469 : Blo 2175435 3265469 := bbase (se 3 (by rfl) ⟨612275, by rfl⟩ : syracuseStep 3265469 = 1224551) (by norm_num)
theorem B2176979 : Blo 2175435 2176979 := bstep (se 1 (by rfl) ⟨1632734, by rfl⟩ : syracuseStep 2176979 = 3265469) B3265469
theorem B4898213 : Blo 2175435 4898213 := bbase (se 4 (by rfl) ⟨459207, by rfl⟩ : syracuseStep 4898213 = 918415) (by norm_num)
theorem B3265475 : Blo 2175435 3265475 := bstep (se 1 (by rfl) ⟨2449106, by rfl⟩ : syracuseStep 3265475 = 4898213) B4898213
theorem B2176983 : Blo 2175435 2176983 := bstep (se 1 (by rfl) ⟨1632737, by rfl⟩ : syracuseStep 2176983 = 3265475) B3265475
theorem B5510501 : Blo 2175435 5510501 := bbase (se 4 (by rfl) ⟨516609, by rfl⟩ : syracuseStep 5510501 = 1033219) (by norm_num)
theorem B3673667 : Blo 2175435 3673667 := bstep (se 1 (by rfl) ⟨2755250, by rfl⟩ : syracuseStep 3673667 = 5510501) B5510501
theorem B2449111 : Blo 2175435 2449111 := bstep (se 1 (by rfl) ⟨1836833, by rfl⟩ : syracuseStep 2449111 = 3673667) B3673667
theorem B3265481 : Blo 2175435 3265481 := bstep (se 2 (by rfl) ⟨1224555, by rfl⟩ : syracuseStep 3265481 = 2449111) B2449111
theorem B2176987 : Blo 2175435 2176987 := bstep (se 1 (by rfl) ⟨1632740, by rfl⟩ : syracuseStep 2176987 = 3265481) B3265481
theorem B2615341 : Blo 2175435 2615341 := bbase (se 3 (by rfl) ⟨490376, by rfl⟩ : syracuseStep 2615341 = 980753) (by norm_num)
theorem B3487121 : Blo 2175435 3487121 := bstep (se 2 (by rfl) ⟨1307670, by rfl⟩ : syracuseStep 3487121 = 2615341) B2615341
theorem B2324747 : Blo 2175435 2324747 := bstep (se 1 (by rfl) ⟨1743560, by rfl⟩ : syracuseStep 2324747 = 3487121) B3487121
theorem B6199325 : Blo 2175435 6199325 := bstep (se 3 (by rfl) ⟨1162373, by rfl⟩ : syracuseStep 6199325 = 2324747) B2324747
theorem B4132883 : Blo 2175435 4132883 := bstep (se 1 (by rfl) ⟨3099662, by rfl⟩ : syracuseStep 4132883 = 6199325) B6199325
theorem B11021021 : Blo 2175435 11021021 := bstep (se 3 (by rfl) ⟨2066441, by rfl⟩ : syracuseStep 11021021 = 4132883) B4132883
theorem B7347347 : Blo 2175435 7347347 := bstep (se 1 (by rfl) ⟨5510510, by rfl⟩ : syracuseStep 7347347 = 11021021) B11021021
theorem B4898231 : Blo 2175435 4898231 := bstep (se 1 (by rfl) ⟨3673673, by rfl⟩ : syracuseStep 4898231 = 7347347) B7347347
theorem B3265487 : Blo 2175435 3265487 := bstep (se 1 (by rfl) ⟨2449115, by rfl⟩ : syracuseStep 3265487 = 4898231) B4898231
theorem B2176991 : Blo 2175435 2176991 := bstep (se 1 (by rfl) ⟨1632743, by rfl⟩ : syracuseStep 2176991 = 3265487) B3265487
theorem B3265493 : Blo 2175435 3265493 := bbase (se 7 (by rfl) ⟨38267, by rfl⟩ : syracuseStep 3265493 = 76535) (by norm_num)
theorem B2176995 : Blo 2175435 2176995 := bstep (se 1 (by rfl) ⟨1632746, by rfl⟩ : syracuseStep 2176995 = 3265493) B3265493
theorem B8265797 : Blo 2175435 8265797 := bbase (se 4 (by rfl) ⟨774918, by rfl⟩ : syracuseStep 8265797 = 1549837) (by norm_num)
theorem B5510531 : Blo 2175435 5510531 := bstep (se 1 (by rfl) ⟨4132898, by rfl⟩ : syracuseStep 5510531 = 8265797) B8265797
theorem B3673687 : Blo 2175435 3673687 := bstep (se 1 (by rfl) ⟨2755265, by rfl⟩ : syracuseStep 3673687 = 5510531) B5510531
theorem B4898249 : Blo 2175435 4898249 := bstep (se 2 (by rfl) ⟨1836843, by rfl⟩ : syracuseStep 4898249 = 3673687) B3673687
theorem B3265499 : Blo 2175435 3265499 := bstep (se 1 (by rfl) ⟨2449124, by rfl⟩ : syracuseStep 3265499 = 4898249) B4898249
theorem B2176999 : Blo 2175435 2176999 := bstep (se 1 (by rfl) ⟨1632749, by rfl⟩ : syracuseStep 2176999 = 3265499) B3265499
theorem B2449129 : Blo 2175435 2449129 := bbase (se 2 (by rfl) ⟨918423, by rfl⟩ : syracuseStep 2449129 = 1836847) (by norm_num)
theorem B3265505 : Blo 2175435 3265505 := bstep (se 2 (by rfl) ⟨1224564, by rfl⟩ : syracuseStep 3265505 = 2449129) B2449129
theorem B2177003 : Blo 2175435 2177003 := bstep (se 1 (by rfl) ⟨1632752, by rfl⟩ : syracuseStep 2177003 = 3265505) B3265505
theorem B12398741 : Blo 2175435 12398741 := bbase (se 6 (by rfl) ⟨290595, by rfl⟩ : syracuseStep 12398741 = 581191) (by norm_num)
theorem B8265827 : Blo 2175435 8265827 := bstep (se 1 (by rfl) ⟨6199370, by rfl⟩ : syracuseStep 8265827 = 12398741) B12398741
theorem B5510551 : Blo 2175435 5510551 := bstep (se 1 (by rfl) ⟨4132913, by rfl⟩ : syracuseStep 5510551 = 8265827) B8265827
theorem B7347401 : Blo 2175435 7347401 := bstep (se 2 (by rfl) ⟨2755275, by rfl⟩ : syracuseStep 7347401 = 5510551) B5510551
theorem B4898267 : Blo 2175435 4898267 := bstep (se 1 (by rfl) ⟨3673700, by rfl⟩ : syracuseStep 4898267 = 7347401) B7347401
theorem B3265511 : Blo 2175435 3265511 := bstep (se 1 (by rfl) ⟨2449133, by rfl⟩ : syracuseStep 3265511 = 4898267) B4898267
theorem B2177007 : Blo 2175435 2177007 := bstep (se 1 (by rfl) ⟨1632755, by rfl⟩ : syracuseStep 2177007 = 3265511) B3265511
theorem B3265517 : Blo 2175435 3265517 := bbase (se 3 (by rfl) ⟨612284, by rfl⟩ : syracuseStep 3265517 = 1224569) (by norm_num)
theorem B2177011 : Blo 2175435 2177011 := bstep (se 1 (by rfl) ⟨1632758, by rfl⟩ : syracuseStep 2177011 = 3265517) B3265517
theorem B4898285 : Blo 2175435 4898285 := bbase (se 3 (by rfl) ⟨918428, by rfl⟩ : syracuseStep 4898285 = 1836857) (by norm_num)
theorem B3265523 : Blo 2175435 3265523 := bstep (se 1 (by rfl) ⟨2449142, by rfl⟩ : syracuseStep 3265523 = 4898285) B4898285
theorem B2177015 : Blo 2175435 2177015 := bstep (se 1 (by rfl) ⟨1632761, by rfl⟩ : syracuseStep 2177015 = 3265523) B3265523
theorem B3310085 : Blo 2175435 3310085 := bbase (se 4 (by rfl) ⟨310320, by rfl⟩ : syracuseStep 3310085 = 620641) (by norm_num)
theorem B8826893 : Blo 2175435 8826893 := bstep (se 3 (by rfl) ⟨1655042, by rfl⟩ : syracuseStep 8826893 = 3310085) B3310085
theorem B5884595 : Blo 2175435 5884595 := bstep (se 1 (by rfl) ⟨4413446, by rfl⟩ : syracuseStep 5884595 = 8826893) B8826893
theorem B3923063 : Blo 2175435 3923063 := bstep (se 1 (by rfl) ⟨2942297, by rfl⟩ : syracuseStep 3923063 = 5884595) B5884595
theorem B2615375 : Blo 2175435 2615375 := bstep (se 1 (by rfl) ⟨1961531, by rfl⟩ : syracuseStep 2615375 = 3923063) B3923063
theorem B6974333 : Blo 2175435 6974333 := bstep (se 3 (by rfl) ⟨1307687, by rfl⟩ : syracuseStep 6974333 = 2615375) B2615375
theorem B4649555 : Blo 2175435 4649555 := bstep (se 1 (by rfl) ⟨3487166, by rfl⟩ : syracuseStep 4649555 = 6974333) B6974333
theorem B3099703 : Blo 2175435 3099703 := bstep (se 1 (by rfl) ⟨2324777, by rfl⟩ : syracuseStep 3099703 = 4649555) B4649555
theorem B4132937 : Blo 2175435 4132937 := bstep (se 2 (by rfl) ⟨1549851, by rfl⟩ : syracuseStep 4132937 = 3099703) B3099703
theorem B2755291 : Blo 2175435 2755291 := bstep (se 1 (by rfl) ⟨2066468, by rfl⟩ : syracuseStep 2755291 = 4132937) B4132937
theorem B3673721 : Blo 2175435 3673721 := bstep (se 2 (by rfl) ⟨1377645, by rfl⟩ : syracuseStep 3673721 = 2755291) B2755291
theorem B2449147 : Blo 2175435 2449147 := bstep (se 1 (by rfl) ⟨1836860, by rfl⟩ : syracuseStep 2449147 = 3673721) B3673721
theorem B3265529 : Blo 2175435 3265529 := bstep (se 2 (by rfl) ⟨1224573, by rfl⟩ : syracuseStep 3265529 = 2449147) B2449147
theorem B2177019 : Blo 2175435 2177019 := bstep (se 1 (by rfl) ⟨1632764, by rfl⟩ : syracuseStep 2177019 = 3265529) B3265529
theorem B2516437 : Blo 2175435 2516437 := bbase (se 7 (by rfl) ⟨29489, by rfl⟩ : syracuseStep 2516437 = 58979) (by norm_num)
theorem B13420997 : Blo 2175435 13420997 := bstep (se 4 (by rfl) ⟨1258218, by rfl⟩ : syracuseStep 13420997 = 2516437) B2516437
theorem B8947331 : Blo 2175435 8947331 := bstep (se 1 (by rfl) ⟨6710498, by rfl⟩ : syracuseStep 8947331 = 13420997) B13420997
theorem B95438197 : Blo 2175435 95438197 := bstep (se 5 (by rfl) ⟨4473665, by rfl⟩ : syracuseStep 95438197 = 8947331) B8947331
theorem B127250929 : Blo 2175435 127250929 := bstep (se 2 (by rfl) ⟨47719098, by rfl⟩ : syracuseStep 127250929 = 95438197) B95438197
theorem B169667905 : Blo 2175435 169667905 := bstep (se 2 (by rfl) ⟨63625464, by rfl⟩ : syracuseStep 169667905 = 127250929) B127250929
theorem B226223873 : Blo 2175435 226223873 := bstep (se 2 (by rfl) ⟨84833952, by rfl⟩ : syracuseStep 226223873 = 169667905) B169667905
theorem B150815915 : Blo 2175435 150815915 := bstep (se 1 (by rfl) ⟨113111936, by rfl⟩ : syracuseStep 150815915 = 226223873) B226223873
theorem B100543943 : Blo 2175435 100543943 := bstep (se 1 (by rfl) ⟨75407957, by rfl⟩ : syracuseStep 100543943 = 150815915) B150815915
theorem B67029295 : Blo 2175435 67029295 := bstep (se 1 (by rfl) ⟨50271971, by rfl⟩ : syracuseStep 67029295 = 100543943) B100543943
theorem B89372393 : Blo 2175435 89372393 := bstep (se 2 (by rfl) ⟨33514647, by rfl⟩ : syracuseStep 89372393 = 67029295) B67029295
theorem B59581595 : Blo 2175435 59581595 := bstep (se 1 (by rfl) ⟨44686196, by rfl⟩ : syracuseStep 59581595 = 89372393) B89372393
theorem B158884253 : Blo 2175435 158884253 := bstep (se 3 (by rfl) ⟨29790797, by rfl⟩ : syracuseStep 158884253 = 59581595) B59581595
theorem B105922835 : Blo 2175435 105922835 := bstep (se 1 (by rfl) ⟨79442126, by rfl⟩ : syracuseStep 105922835 = 158884253) B158884253
theorem B70615223 : Blo 2175435 70615223 := bstep (se 1 (by rfl) ⟨52961417, by rfl⟩ : syracuseStep 70615223 = 105922835) B105922835
theorem B47076815 : Blo 2175435 47076815 := bstep (se 1 (by rfl) ⟨35307611, by rfl⟩ : syracuseStep 47076815 = 70615223) B70615223
theorem B125538173 : Blo 2175435 125538173 := bstep (se 3 (by rfl) ⟨23538407, by rfl⟩ : syracuseStep 125538173 = 47076815) B47076815
theorem B83692115 : Blo 2175435 83692115 := bstep (se 1 (by rfl) ⟨62769086, by rfl⟩ : syracuseStep 83692115 = 125538173) B125538173
theorem B55794743 : Blo 2175435 55794743 := bstep (se 1 (by rfl) ⟨41846057, by rfl⟩ : syracuseStep 55794743 = 83692115) B83692115
theorem B37196495 : Blo 2175435 37196495 := bstep (se 1 (by rfl) ⟨27897371, by rfl⟩ : syracuseStep 37196495 = 55794743) B55794743
theorem B24797663 : Blo 2175435 24797663 := bstep (se 1 (by rfl) ⟨18598247, by rfl⟩ : syracuseStep 24797663 = 37196495) B37196495
theorem B16531775 : Blo 2175435 16531775 := bstep (se 1 (by rfl) ⟨12398831, by rfl⟩ : syracuseStep 16531775 = 24797663) B24797663
theorem B11021183 : Blo 2175435 11021183 := bstep (se 1 (by rfl) ⟨8265887, by rfl⟩ : syracuseStep 11021183 = 16531775) B16531775
theorem B7347455 : Blo 2175435 7347455 := bstep (se 1 (by rfl) ⟨5510591, by rfl⟩ : syracuseStep 7347455 = 11021183) B11021183
theorem B4898303 : Blo 2175435 4898303 := bstep (se 1 (by rfl) ⟨3673727, by rfl⟩ : syracuseStep 4898303 = 7347455) B7347455
theorem B3265535 : Blo 2175435 3265535 := bstep (se 1 (by rfl) ⟨2449151, by rfl⟩ : syracuseStep 3265535 = 4898303) B4898303
theorem B2177023 : Blo 2175435 2177023 := bstep (se 1 (by rfl) ⟨1632767, by rfl⟩ : syracuseStep 2177023 = 3265535) B3265535
theorem B3265541 : Blo 2175435 3265541 := bbase (se 4 (by rfl) ⟨306144, by rfl⟩ : syracuseStep 3265541 = 612289) (by norm_num)
theorem B2177027 : Blo 2175435 2177027 := bstep (se 1 (by rfl) ⟨1632770, by rfl⟩ : syracuseStep 2177027 = 3265541) B3265541
theorem B3673741 : Blo 2175435 3673741 := bbase (se 3 (by rfl) ⟨688826, by rfl⟩ : syracuseStep 3673741 = 1377653) (by norm_num)
theorem B4898321 : Blo 2175435 4898321 := bstep (se 2 (by rfl) ⟨1836870, by rfl⟩ : syracuseStep 4898321 = 3673741) B3673741
theorem B3265547 : Blo 2175435 3265547 := bstep (se 1 (by rfl) ⟨2449160, by rfl⟩ : syracuseStep 3265547 = 4898321) B4898321
theorem B2177031 : Blo 2175435 2177031 := bstep (se 1 (by rfl) ⟨1632773, by rfl⟩ : syracuseStep 2177031 = 3265547) B3265547
theorem B2449165 : Blo 2175435 2449165 := bbase (se 3 (by rfl) ⟨459218, by rfl⟩ : syracuseStep 2449165 = 918437) (by norm_num)
theorem B3265553 : Blo 2175435 3265553 := bstep (se 2 (by rfl) ⟨1224582, by rfl⟩ : syracuseStep 3265553 = 2449165) B2449165
theorem B2177035 : Blo 2175435 2177035 := bstep (se 1 (by rfl) ⟨1632776, by rfl⟩ : syracuseStep 2177035 = 3265553) B3265553
theorem B7347509 : Blo 2175435 7347509 := bbase (se 5 (by rfl) ⟨344414, by rfl⟩ : syracuseStep 7347509 = 688829) (by norm_num)
theorem B4898339 : Blo 2175435 4898339 := bstep (se 1 (by rfl) ⟨3673754, by rfl⟩ : syracuseStep 4898339 = 7347509) B7347509
theorem B3265559 : Blo 2175435 3265559 := bstep (se 1 (by rfl) ⟨2449169, by rfl⟩ : syracuseStep 3265559 = 4898339) B4898339
theorem B2177039 : Blo 2175435 2177039 := bstep (se 1 (by rfl) ⟨1632779, by rfl⟩ : syracuseStep 2177039 = 3265559) B3265559
theorem B3265565 : Blo 2175435 3265565 := bbase (se 3 (by rfl) ⟨612293, by rfl⟩ : syracuseStep 3265565 = 1224587) (by norm_num)
theorem B2177043 : Blo 2175435 2177043 := bstep (se 1 (by rfl) ⟨1632782, by rfl⟩ : syracuseStep 2177043 = 3265565) B3265565
theorem B4898357 : Blo 2175435 4898357 := bbase (se 5 (by rfl) ⟨229610, by rfl⟩ : syracuseStep 4898357 = 459221) (by norm_num)
theorem B3265571 : Blo 2175435 3265571 := bstep (se 1 (by rfl) ⟨2449178, by rfl⟩ : syracuseStep 3265571 = 4898357) B4898357
theorem B2177047 : Blo 2175435 2177047 := bstep (se 1 (by rfl) ⟨1632785, by rfl⟩ : syracuseStep 2177047 = 3265571) B3265571
theorem B2615413 : Blo 2175435 2615413 := bbase (se 5 (by rfl) ⟨122597, by rfl⟩ : syracuseStep 2615413 = 245195) (by norm_num)
theorem B3487217 : Blo 2175435 3487217 := bstep (se 2 (by rfl) ⟨1307706, by rfl⟩ : syracuseStep 3487217 = 2615413) B2615413
theorem B9299245 : Blo 2175435 9299245 := bstep (se 3 (by rfl) ⟨1743608, by rfl⟩ : syracuseStep 9299245 = 3487217) B3487217
theorem B12398993 : Blo 2175435 12398993 := bstep (se 2 (by rfl) ⟨4649622, by rfl⟩ : syracuseStep 12398993 = 9299245) B9299245
theorem B8265995 : Blo 2175435 8265995 := bstep (se 1 (by rfl) ⟨6199496, by rfl⟩ : syracuseStep 8265995 = 12398993) B12398993
theorem B5510663 : Blo 2175435 5510663 := bstep (se 1 (by rfl) ⟨4132997, by rfl⟩ : syracuseStep 5510663 = 8265995) B8265995
theorem B3673775 : Blo 2175435 3673775 := bstep (se 1 (by rfl) ⟨2755331, by rfl⟩ : syracuseStep 3673775 = 5510663) B5510663
theorem B2449183 : Blo 2175435 2449183 := bstep (se 1 (by rfl) ⟨1836887, by rfl⟩ : syracuseStep 2449183 = 3673775) B3673775
theorem B3265577 : Blo 2175435 3265577 := bstep (se 2 (by rfl) ⟨1224591, by rfl⟩ : syracuseStep 3265577 = 2449183) B2449183
theorem B2177051 : Blo 2175435 2177051 := bstep (se 1 (by rfl) ⟨1632788, by rfl⟩ : syracuseStep 2177051 = 3265577) B3265577
theorem B5585861 : Blo 2175435 5585861 := bbase (se 4 (by rfl) ⟨523674, by rfl⟩ : syracuseStep 5585861 = 1047349) (by norm_num)
theorem B3723907 : Blo 2175435 3723907 := bstep (se 1 (by rfl) ⟨2792930, by rfl⟩ : syracuseStep 3723907 = 5585861) B5585861
theorem B4965209 : Blo 2175435 4965209 := bstep (se 2 (by rfl) ⟨1861953, by rfl⟩ : syracuseStep 4965209 = 3723907) B3723907
theorem B3310139 : Blo 2175435 3310139 := bstep (se 1 (by rfl) ⟨2482604, by rfl⟩ : syracuseStep 3310139 = 4965209) B4965209
theorem B2206759 : Blo 2175435 2206759 := bstep (se 1 (by rfl) ⟨1655069, by rfl⟩ : syracuseStep 2206759 = 3310139) B3310139
theorem B2942345 : Blo 2175435 2942345 := bstep (se 2 (by rfl) ⟨1103379, by rfl⟩ : syracuseStep 2942345 = 2206759) B2206759
theorem B7846253 : Blo 2175435 7846253 := bstep (se 3 (by rfl) ⟨1471172, by rfl⟩ : syracuseStep 7846253 = 2942345) B2942345
theorem B5230835 : Blo 2175435 5230835 := bstep (se 1 (by rfl) ⟨3923126, by rfl⟩ : syracuseStep 5230835 = 7846253) B7846253
theorem B3487223 : Blo 2175435 3487223 := bstep (se 1 (by rfl) ⟨2615417, by rfl⟩ : syracuseStep 3487223 = 5230835) B5230835
theorem B9299261 : Blo 2175435 9299261 := bstep (se 3 (by rfl) ⟨1743611, by rfl⟩ : syracuseStep 9299261 = 3487223) B3487223
theorem B6199507 : Blo 2175435 6199507 := bstep (se 1 (by rfl) ⟨4649630, by rfl⟩ : syracuseStep 6199507 = 9299261) B9299261
theorem B8266009 : Blo 2175435 8266009 := bstep (se 2 (by rfl) ⟨3099753, by rfl⟩ : syracuseStep 8266009 = 6199507) B6199507
theorem B11021345 : Blo 2175435 11021345 := bstep (se 2 (by rfl) ⟨4133004, by rfl⟩ : syracuseStep 11021345 = 8266009) B8266009
theorem B7347563 : Blo 2175435 7347563 := bstep (se 1 (by rfl) ⟨5510672, by rfl⟩ : syracuseStep 7347563 = 11021345) B11021345
theorem B4898375 : Blo 2175435 4898375 := bstep (se 1 (by rfl) ⟨3673781, by rfl⟩ : syracuseStep 4898375 = 7347563) B7347563
theorem B3265583 : Blo 2175435 3265583 := bstep (se 1 (by rfl) ⟨2449187, by rfl⟩ : syracuseStep 3265583 = 4898375) B4898375
theorem B2177055 : Blo 2175435 2177055 := bstep (se 1 (by rfl) ⟨1632791, by rfl⟩ : syracuseStep 2177055 = 3265583) B3265583
theorem B3265589 : Blo 2175435 3265589 := bbase (se 5 (by rfl) ⟨153074, by rfl⟩ : syracuseStep 3265589 = 306149) (by norm_num)
theorem B2177059 : Blo 2175435 2177059 := bstep (se 1 (by rfl) ⟨1632794, by rfl⟩ : syracuseStep 2177059 = 3265589) B3265589
theorem B5510693 : Blo 2175435 5510693 := bbase (se 4 (by rfl) ⟨516627, by rfl⟩ : syracuseStep 5510693 = 1033255) (by norm_num)
theorem B3673795 : Blo 2175435 3673795 := bstep (se 1 (by rfl) ⟨2755346, by rfl⟩ : syracuseStep 3673795 = 5510693) B5510693
theorem B4898393 : Blo 2175435 4898393 := bstep (se 2 (by rfl) ⟨1836897, by rfl⟩ : syracuseStep 4898393 = 3673795) B3673795
theorem B3265595 : Blo 2175435 3265595 := bstep (se 1 (by rfl) ⟨2449196, by rfl⟩ : syracuseStep 3265595 = 4898393) B4898393
theorem B2177063 : Blo 2175435 2177063 := bstep (se 1 (by rfl) ⟨1632797, by rfl⟩ : syracuseStep 2177063 = 3265595) B3265595
theorem B2449201 : Blo 2175435 2449201 := bbase (se 2 (by rfl) ⟨918450, by rfl⟩ : syracuseStep 2449201 = 1836901) (by norm_num)
theorem B3265601 : Blo 2175435 3265601 := bstep (se 2 (by rfl) ⟨1224600, by rfl⟩ : syracuseStep 3265601 = 2449201) B2449201
theorem B2177067 : Blo 2175435 2177067 := bstep (se 1 (by rfl) ⟨1632800, by rfl⟩ : syracuseStep 2177067 = 3265601) B3265601
theorem B2615437 : Blo 2175435 2615437 := bbase (se 3 (by rfl) ⟨490394, by rfl⟩ : syracuseStep 2615437 = 980789) (by norm_num)
theorem B3487249 : Blo 2175435 3487249 := bstep (se 2 (by rfl) ⟨1307718, by rfl⟩ : syracuseStep 3487249 = 2615437) B2615437
theorem B4649665 : Blo 2175435 4649665 := bstep (se 2 (by rfl) ⟨1743624, by rfl⟩ : syracuseStep 4649665 = 3487249) B3487249
theorem B6199553 : Blo 2175435 6199553 := bstep (se 2 (by rfl) ⟨2324832, by rfl⟩ : syracuseStep 6199553 = 4649665) B4649665
theorem B4133035 : Blo 2175435 4133035 := bstep (se 1 (by rfl) ⟨3099776, by rfl⟩ : syracuseStep 4133035 = 6199553) B6199553
theorem B5510713 : Blo 2175435 5510713 := bstep (se 2 (by rfl) ⟨2066517, by rfl⟩ : syracuseStep 5510713 = 4133035) B4133035
theorem B7347617 : Blo 2175435 7347617 := bstep (se 2 (by rfl) ⟨2755356, by rfl⟩ : syracuseStep 7347617 = 5510713) B5510713
theorem B4898411 : Blo 2175435 4898411 := bstep (se 1 (by rfl) ⟨3673808, by rfl⟩ : syracuseStep 4898411 = 7347617) B7347617
theorem B3265607 : Blo 2175435 3265607 := bstep (se 1 (by rfl) ⟨2449205, by rfl⟩ : syracuseStep 3265607 = 4898411) B4898411
theorem B2177071 : Blo 2175435 2177071 := bstep (se 1 (by rfl) ⟨1632803, by rfl⟩ : syracuseStep 2177071 = 3265607) B3265607
theorem B3265613 : Blo 2175435 3265613 := bbase (se 3 (by rfl) ⟨612302, by rfl⟩ : syracuseStep 3265613 = 1224605) (by norm_num)
theorem B2177075 : Blo 2175435 2177075 := bstep (se 1 (by rfl) ⟨1632806, by rfl⟩ : syracuseStep 2177075 = 3265613) B3265613
theorem B4898429 : Blo 2175435 4898429 := bbase (se 3 (by rfl) ⟨918455, by rfl⟩ : syracuseStep 4898429 = 1836911) (by norm_num)
theorem B3265619 : Blo 2175435 3265619 := bstep (se 1 (by rfl) ⟨2449214, by rfl⟩ : syracuseStep 3265619 = 4898429) B4898429
theorem B2177079 : Blo 2175435 2177079 := bstep (se 1 (by rfl) ⟨1632809, by rfl⟩ : syracuseStep 2177079 = 3265619) B3265619
theorem B3673829 : Blo 2175435 3673829 := bbase (se 4 (by rfl) ⟨344421, by rfl⟩ : syracuseStep 3673829 = 688843) (by norm_num)
theorem B2449219 : Blo 2175435 2449219 := bstep (se 1 (by rfl) ⟨1836914, by rfl⟩ : syracuseStep 2449219 = 3673829) B3673829
theorem B3265625 : Blo 2175435 3265625 := bstep (se 2 (by rfl) ⟨1224609, by rfl⟩ : syracuseStep 3265625 = 2449219) B2449219
theorem B2177083 : Blo 2175435 2177083 := bstep (se 1 (by rfl) ⟨1632812, by rfl⟩ : syracuseStep 2177083 = 3265625) B3265625
theorem B6974549 : Blo 2175435 6974549 := bbase (se 8 (by rfl) ⟨40866, by rfl⟩ : syracuseStep 6974549 = 81733) (by norm_num)
theorem B4649699 : Blo 2175435 4649699 := bstep (se 1 (by rfl) ⟨3487274, by rfl⟩ : syracuseStep 4649699 = 6974549) B6974549
theorem B3099799 : Blo 2175435 3099799 := bstep (se 1 (by rfl) ⟨2324849, by rfl⟩ : syracuseStep 3099799 = 4649699) B4649699
theorem B16532261 : Blo 2175435 16532261 := bstep (se 4 (by rfl) ⟨1549899, by rfl⟩ : syracuseStep 16532261 = 3099799) B3099799
theorem B11021507 : Blo 2175435 11021507 := bstep (se 1 (by rfl) ⟨8266130, by rfl⟩ : syracuseStep 11021507 = 16532261) B16532261
theorem B7347671 : Blo 2175435 7347671 := bstep (se 1 (by rfl) ⟨5510753, by rfl⟩ : syracuseStep 7347671 = 11021507) B11021507
theorem B4898447 : Blo 2175435 4898447 := bstep (se 1 (by rfl) ⟨3673835, by rfl⟩ : syracuseStep 4898447 = 7347671) B7347671
theorem B3265631 : Blo 2175435 3265631 := bstep (se 1 (by rfl) ⟨2449223, by rfl⟩ : syracuseStep 3265631 = 4898447) B4898447
theorem B2177087 : Blo 2175435 2177087 := bstep (se 1 (by rfl) ⟨1632815, by rfl⟩ : syracuseStep 2177087 = 3265631) B3265631
theorem B3265637 : Blo 2175435 3265637 := bbase (se 4 (by rfl) ⟨306153, by rfl⟩ : syracuseStep 3265637 = 612307) (by norm_num)
theorem B2177091 : Blo 2175435 2177091 := bstep (se 1 (by rfl) ⟨1632818, by rfl⟩ : syracuseStep 2177091 = 3265637) B3265637
theorem B4649717 : Blo 2175435 4649717 := bbase (se 5 (by rfl) ⟨217955, by rfl⟩ : syracuseStep 4649717 = 435911) (by norm_num)
theorem B3099811 : Blo 2175435 3099811 := bstep (se 1 (by rfl) ⟨2324858, by rfl⟩ : syracuseStep 3099811 = 4649717) B4649717
theorem B4133081 : Blo 2175435 4133081 := bstep (se 2 (by rfl) ⟨1549905, by rfl⟩ : syracuseStep 4133081 = 3099811) B3099811
theorem B2755387 : Blo 2175435 2755387 := bstep (se 1 (by rfl) ⟨2066540, by rfl⟩ : syracuseStep 2755387 = 4133081) B4133081
theorem B3673849 : Blo 2175435 3673849 := bstep (se 2 (by rfl) ⟨1377693, by rfl⟩ : syracuseStep 3673849 = 2755387) B2755387
theorem B4898465 : Blo 2175435 4898465 := bstep (se 2 (by rfl) ⟨1836924, by rfl⟩ : syracuseStep 4898465 = 3673849) B3673849
theorem B3265643 : Blo 2175435 3265643 := bstep (se 1 (by rfl) ⟨2449232, by rfl⟩ : syracuseStep 3265643 = 4898465) B4898465
theorem B2177095 : Blo 2175435 2177095 := bstep (se 1 (by rfl) ⟨1632821, by rfl⟩ : syracuseStep 2177095 = 3265643) B3265643
theorem B2449237 : Blo 2175435 2449237 := bbase (se 9 (by rfl) ⟨7175, by rfl⟩ : syracuseStep 2449237 = 14351) (by norm_num)
theorem B3265649 : Blo 2175435 3265649 := bstep (se 2 (by rfl) ⟨1224618, by rfl⟩ : syracuseStep 3265649 = 2449237) B2449237
theorem B2177099 : Blo 2175435 2177099 := bstep (se 1 (by rfl) ⟨1632824, by rfl⟩ : syracuseStep 2177099 = 3265649) B3265649
theorem B2755397 : Blo 2175435 2755397 := bbase (se 4 (by rfl) ⟨258318, by rfl⟩ : syracuseStep 2755397 = 516637) (by norm_num)
theorem B7347725 : Blo 2175435 7347725 := bstep (se 3 (by rfl) ⟨1377698, by rfl⟩ : syracuseStep 7347725 = 2755397) B2755397
theorem B4898483 : Blo 2175435 4898483 := bstep (se 1 (by rfl) ⟨3673862, by rfl⟩ : syracuseStep 4898483 = 7347725) B7347725
theorem B3265655 : Blo 2175435 3265655 := bstep (se 1 (by rfl) ⟨2449241, by rfl⟩ : syracuseStep 3265655 = 4898483) B4898483
theorem B2177103 : Blo 2175435 2177103 := bstep (se 1 (by rfl) ⟨1632827, by rfl⟩ : syracuseStep 2177103 = 3265655) B3265655
theorem B3265661 : Blo 2175435 3265661 := bbase (se 3 (by rfl) ⟨612311, by rfl⟩ : syracuseStep 3265661 = 1224623) (by norm_num)
theorem B2177107 : Blo 2175435 2177107 := bstep (se 1 (by rfl) ⟨1632830, by rfl⟩ : syracuseStep 2177107 = 3265661) B3265661
theorem B4898501 : Blo 2175435 4898501 := bbase (se 4 (by rfl) ⟨459234, by rfl⟩ : syracuseStep 4898501 = 918469) (by norm_num)
theorem B3265667 : Blo 2175435 3265667 := bstep (se 1 (by rfl) ⟨2449250, by rfl⟩ : syracuseStep 3265667 = 4898501) B4898501
theorem B2177111 : Blo 2175435 2177111 := bstep (se 1 (by rfl) ⟨1632833, by rfl⟩ : syracuseStep 2177111 = 3265667) B3265667
theorem B5586013 : Blo 2175435 5586013 := bbase (se 3 (by rfl) ⟨1047377, by rfl⟩ : syracuseStep 5586013 = 2094755) (by norm_num)
theorem B7448017 : Blo 2175435 7448017 := bstep (se 2 (by rfl) ⟨2793006, by rfl⟩ : syracuseStep 7448017 = 5586013) B5586013
theorem B9930689 : Blo 2175435 9930689 := bstep (se 2 (by rfl) ⟨3724008, by rfl⟩ : syracuseStep 9930689 = 7448017) B7448017
theorem B6620459 : Blo 2175435 6620459 := bstep (se 1 (by rfl) ⟨4965344, by rfl⟩ : syracuseStep 6620459 = 9930689) B9930689
theorem B70618229 : Blo 2175435 70618229 := bstep (se 5 (by rfl) ⟨3310229, by rfl⟩ : syracuseStep 70618229 = 6620459) B6620459
theorem B47078819 : Blo 2175435 47078819 := bstep (se 1 (by rfl) ⟨35309114, by rfl⟩ : syracuseStep 47078819 = 70618229) B70618229
theorem B31385879 : Blo 2175435 31385879 := bstep (se 1 (by rfl) ⟨23539409, by rfl⟩ : syracuseStep 31385879 = 47078819) B47078819
theorem B20923919 : Blo 2175435 20923919 := bstep (se 1 (by rfl) ⟨15692939, by rfl⟩ : syracuseStep 20923919 = 31385879) B31385879
theorem B13949279 : Blo 2175435 13949279 := bstep (se 1 (by rfl) ⟨10461959, by rfl⟩ : syracuseStep 13949279 = 20923919) B20923919
theorem B9299519 : Blo 2175435 9299519 := bstep (se 1 (by rfl) ⟨6974639, by rfl⟩ : syracuseStep 9299519 = 13949279) B13949279
theorem B6199679 : Blo 2175435 6199679 := bstep (se 1 (by rfl) ⟨4649759, by rfl⟩ : syracuseStep 6199679 = 9299519) B9299519
theorem B4133119 : Blo 2175435 4133119 := bstep (se 1 (by rfl) ⟨3099839, by rfl⟩ : syracuseStep 4133119 = 6199679) B6199679
theorem B5510825 : Blo 2175435 5510825 := bstep (se 2 (by rfl) ⟨2066559, by rfl⟩ : syracuseStep 5510825 = 4133119) B4133119
theorem B3673883 : Blo 2175435 3673883 := bstep (se 1 (by rfl) ⟨2755412, by rfl⟩ : syracuseStep 3673883 = 5510825) B5510825
theorem B2449255 : Blo 2175435 2449255 := bstep (se 1 (by rfl) ⟨1836941, by rfl⟩ : syracuseStep 2449255 = 3673883) B3673883
theorem B3265673 : Blo 2175435 3265673 := bstep (se 2 (by rfl) ⟨1224627, by rfl⟩ : syracuseStep 3265673 = 2449255) B2449255
theorem B2177115 : Blo 2175435 2177115 := bstep (se 1 (by rfl) ⟨1632836, by rfl⟩ : syracuseStep 2177115 = 3265673) B3265673
theorem B11021669 : Blo 2175435 11021669 := bbase (se 4 (by rfl) ⟨1033281, by rfl⟩ : syracuseStep 11021669 = 2066563) (by norm_num)
theorem B7347779 : Blo 2175435 7347779 := bstep (se 1 (by rfl) ⟨5510834, by rfl⟩ : syracuseStep 7347779 = 11021669) B11021669
theorem B4898519 : Blo 2175435 4898519 := bstep (se 1 (by rfl) ⟨3673889, by rfl⟩ : syracuseStep 4898519 = 7347779) B7347779
theorem B3265679 : Blo 2175435 3265679 := bstep (se 1 (by rfl) ⟨2449259, by rfl⟩ : syracuseStep 3265679 = 4898519) B4898519
theorem B2177119 : Blo 2175435 2177119 := bstep (se 1 (by rfl) ⟨1632839, by rfl⟩ : syracuseStep 2177119 = 3265679) B3265679
theorem B3265685 : Blo 2175435 3265685 := bbase (se 6 (by rfl) ⟨76539, by rfl⟩ : syracuseStep 3265685 = 153079) (by norm_num)
theorem B2177123 : Blo 2175435 2177123 := bstep (se 1 (by rfl) ⟨1632842, by rfl⟩ : syracuseStep 2177123 = 3265685) B3265685
theorem B6974677 : Blo 2175435 6974677 := bbase (se 7 (by rfl) ⟨81734, by rfl⟩ : syracuseStep 6974677 = 163469) (by norm_num)
theorem B9299569 : Blo 2175435 9299569 := bstep (se 2 (by rfl) ⟨3487338, by rfl⟩ : syracuseStep 9299569 = 6974677) B6974677
theorem B12399425 : Blo 2175435 12399425 := bstep (se 2 (by rfl) ⟨4649784, by rfl⟩ : syracuseStep 12399425 = 9299569) B9299569
theorem B8266283 : Blo 2175435 8266283 := bstep (se 1 (by rfl) ⟨6199712, by rfl⟩ : syracuseStep 8266283 = 12399425) B12399425
theorem B5510855 : Blo 2175435 5510855 := bstep (se 1 (by rfl) ⟨4133141, by rfl⟩ : syracuseStep 5510855 = 8266283) B8266283
theorem B3673903 : Blo 2175435 3673903 := bstep (se 1 (by rfl) ⟨2755427, by rfl⟩ : syracuseStep 3673903 = 5510855) B5510855
theorem B4898537 : Blo 2175435 4898537 := bstep (se 2 (by rfl) ⟨1836951, by rfl⟩ : syracuseStep 4898537 = 3673903) B3673903
theorem B3265691 : Blo 2175435 3265691 := bstep (se 1 (by rfl) ⟨2449268, by rfl⟩ : syracuseStep 3265691 = 4898537) B4898537
theorem B2177127 : Blo 2175435 2177127 := bstep (se 1 (by rfl) ⟨1632845, by rfl⟩ : syracuseStep 2177127 = 3265691) B3265691
theorem B2449273 : Blo 2175435 2449273 := bbase (se 2 (by rfl) ⟨918477, by rfl⟩ : syracuseStep 2449273 = 1836955) (by norm_num)
theorem B3265697 : Blo 2175435 3265697 := bstep (se 2 (by rfl) ⟨1224636, by rfl⟩ : syracuseStep 3265697 = 2449273) B2449273
theorem B2177131 : Blo 2175435 2177131 := bstep (se 1 (by rfl) ⟨1632848, by rfl⟩ : syracuseStep 2177131 = 3265697) B3265697
theorem B2942453 : Blo 2175435 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B7846541 : Blo 2175435 7846541 := bstep (se 3 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 7846541 = 2942453) B2942453
theorem B5231027 : Blo 2175435 5231027 := bstep (se 1 (by rfl) ⟨3923270, by rfl⟩ : syracuseStep 5231027 = 7846541) B7846541
theorem B13949405 : Blo 2175435 13949405 := bstep (se 3 (by rfl) ⟨2615513, by rfl⟩ : syracuseStep 13949405 = 5231027) B5231027
theorem B9299603 : Blo 2175435 9299603 := bstep (se 1 (by rfl) ⟨6974702, by rfl⟩ : syracuseStep 9299603 = 13949405) B13949405
theorem B6199735 : Blo 2175435 6199735 := bstep (se 1 (by rfl) ⟨4649801, by rfl⟩ : syracuseStep 6199735 = 9299603) B9299603
theorem B8266313 : Blo 2175435 8266313 := bstep (se 2 (by rfl) ⟨3099867, by rfl⟩ : syracuseStep 8266313 = 6199735) B6199735
theorem B5510875 : Blo 2175435 5510875 := bstep (se 1 (by rfl) ⟨4133156, by rfl⟩ : syracuseStep 5510875 = 8266313) B8266313
theorem B7347833 : Blo 2175435 7347833 := bstep (se 2 (by rfl) ⟨2755437, by rfl⟩ : syracuseStep 7347833 = 5510875) B5510875
theorem B4898555 : Blo 2175435 4898555 := bstep (se 1 (by rfl) ⟨3673916, by rfl⟩ : syracuseStep 4898555 = 7347833) B7347833
theorem B3265703 : Blo 2175435 3265703 := bstep (se 1 (by rfl) ⟨2449277, by rfl⟩ : syracuseStep 3265703 = 4898555) B4898555
theorem B2177135 : Blo 2175435 2177135 := bstep (se 1 (by rfl) ⟨1632851, by rfl⟩ : syracuseStep 2177135 = 3265703) B3265703
theorem B3265709 : Blo 2175435 3265709 := bbase (se 3 (by rfl) ⟨612320, by rfl⟩ : syracuseStep 3265709 = 1224641) (by norm_num)
theorem B2177139 : Blo 2175435 2177139 := bstep (se 1 (by rfl) ⟨1632854, by rfl⟩ : syracuseStep 2177139 = 3265709) B3265709
theorem B4898573 : Blo 2175435 4898573 := bbase (se 3 (by rfl) ⟨918482, by rfl⟩ : syracuseStep 4898573 = 1836965) (by norm_num)
theorem B3265715 : Blo 2175435 3265715 := bstep (se 1 (by rfl) ⟨2449286, by rfl⟩ : syracuseStep 3265715 = 4898573) B4898573
theorem B2177143 : Blo 2175435 2177143 := bstep (se 1 (by rfl) ⟨1632857, by rfl⟩ : syracuseStep 2177143 = 3265715) B3265715
theorem B2755453 : Blo 2175435 2755453 := bbase (se 3 (by rfl) ⟨516647, by rfl⟩ : syracuseStep 2755453 = 1033295) (by norm_num)
theorem B3673937 : Blo 2175435 3673937 := bstep (se 2 (by rfl) ⟨1377726, by rfl⟩ : syracuseStep 3673937 = 2755453) B2755453
theorem B2449291 : Blo 2175435 2449291 := bstep (se 1 (by rfl) ⟨1836968, by rfl⟩ : syracuseStep 2449291 = 3673937) B3673937
theorem B3265721 : Blo 2175435 3265721 := bstep (se 2 (by rfl) ⟨1224645, by rfl⟩ : syracuseStep 3265721 = 2449291) B2449291
theorem B2177147 : Blo 2175435 2177147 := bstep (se 1 (by rfl) ⟨1632860, by rfl⟩ : syracuseStep 2177147 = 3265721) B3265721
theorem B5884949 : Blo 2175435 5884949 := bbase (se 6 (by rfl) ⟨137928, by rfl⟩ : syracuseStep 5884949 = 275857) (by norm_num)
theorem B3923299 : Blo 2175435 3923299 := bstep (se 1 (by rfl) ⟨2942474, by rfl⟩ : syracuseStep 3923299 = 5884949) B5884949
theorem B5231065 : Blo 2175435 5231065 := bstep (se 2 (by rfl) ⟨1961649, by rfl⟩ : syracuseStep 5231065 = 3923299) B3923299
theorem B6974753 : Blo 2175435 6974753 := bstep (se 2 (by rfl) ⟨2615532, by rfl⟩ : syracuseStep 6974753 = 5231065) B5231065
theorem B18599341 : Blo 2175435 18599341 := bstep (se 3 (by rfl) ⟨3487376, by rfl⟩ : syracuseStep 18599341 = 6974753) B6974753
theorem B24799121 : Blo 2175435 24799121 := bstep (se 2 (by rfl) ⟨9299670, by rfl⟩ : syracuseStep 24799121 = 18599341) B18599341
theorem B16532747 : Blo 2175435 16532747 := bstep (se 1 (by rfl) ⟨12399560, by rfl⟩ : syracuseStep 16532747 = 24799121) B24799121
theorem B11021831 : Blo 2175435 11021831 := bstep (se 1 (by rfl) ⟨8266373, by rfl⟩ : syracuseStep 11021831 = 16532747) B16532747
theorem B7347887 : Blo 2175435 7347887 := bstep (se 1 (by rfl) ⟨5510915, by rfl⟩ : syracuseStep 7347887 = 11021831) B11021831
theorem B4898591 : Blo 2175435 4898591 := bstep (se 1 (by rfl) ⟨3673943, by rfl⟩ : syracuseStep 4898591 = 7347887) B7347887
theorem B3265727 : Blo 2175435 3265727 := bstep (se 1 (by rfl) ⟨2449295, by rfl⟩ : syracuseStep 3265727 = 4898591) B4898591
theorem B2177151 : Blo 2175435 2177151 := bstep (se 1 (by rfl) ⟨1632863, by rfl⟩ : syracuseStep 2177151 = 3265727) B3265727
theorem B3265733 : Blo 2175435 3265733 := bbase (se 4 (by rfl) ⟨306162, by rfl⟩ : syracuseStep 3265733 = 612325) (by norm_num)
theorem B2177155 : Blo 2175435 2177155 := bstep (se 1 (by rfl) ⟨1632866, by rfl⟩ : syracuseStep 2177155 = 3265733) B3265733
theorem B3673957 : Blo 2175435 3673957 := bbase (se 4 (by rfl) ⟨344433, by rfl⟩ : syracuseStep 3673957 = 688867) (by norm_num)
theorem B4898609 : Blo 2175435 4898609 := bstep (se 2 (by rfl) ⟨1836978, by rfl⟩ : syracuseStep 4898609 = 3673957) B3673957
theorem B3265739 : Blo 2175435 3265739 := bstep (se 1 (by rfl) ⟨2449304, by rfl⟩ : syracuseStep 3265739 = 4898609) B4898609
theorem B2177159 : Blo 2175435 2177159 := bstep (se 1 (by rfl) ⟨1632869, by rfl⟩ : syracuseStep 2177159 = 3265739) B3265739
theorem B2449309 : Blo 2175435 2449309 := bbase (se 3 (by rfl) ⟨459245, by rfl⟩ : syracuseStep 2449309 = 918491) (by norm_num)
theorem B3265745 : Blo 2175435 3265745 := bstep (se 2 (by rfl) ⟨1224654, by rfl⟩ : syracuseStep 3265745 = 2449309) B2449309
theorem B2177163 : Blo 2175435 2177163 := bstep (se 1 (by rfl) ⟨1632872, by rfl⟩ : syracuseStep 2177163 = 3265745) B3265745
theorem B7347941 : Blo 2175435 7347941 := bbase (se 4 (by rfl) ⟨688869, by rfl⟩ : syracuseStep 7347941 = 1377739) (by norm_num)
theorem B4898627 : Blo 2175435 4898627 := bstep (se 1 (by rfl) ⟨3673970, by rfl⟩ : syracuseStep 4898627 = 7347941) B7347941
theorem B3265751 : Blo 2175435 3265751 := bstep (se 1 (by rfl) ⟨2449313, by rfl⟩ : syracuseStep 3265751 = 4898627) B4898627
theorem B2177167 : Blo 2175435 2177167 := bstep (se 1 (by rfl) ⟨1632875, by rfl⟩ : syracuseStep 2177167 = 3265751) B3265751
theorem B3265757 : Blo 2175435 3265757 := bbase (se 3 (by rfl) ⟨612329, by rfl⟩ : syracuseStep 3265757 = 1224659) (by norm_num)
theorem B2177171 : Blo 2175435 2177171 := bstep (se 1 (by rfl) ⟨1632878, by rfl⟩ : syracuseStep 2177171 = 3265757) B3265757
theorem B4898645 : Blo 2175435 4898645 := bbase (se 9 (by rfl) ⟨14351, by rfl⟩ : syracuseStep 4898645 = 28703) (by norm_num)
theorem B3265763 : Blo 2175435 3265763 := bstep (se 1 (by rfl) ⟨2449322, by rfl⟩ : syracuseStep 3265763 = 4898645) B4898645
theorem B2177175 : Blo 2175435 2177175 := bstep (se 1 (by rfl) ⟨1632881, by rfl⟩ : syracuseStep 2177175 = 3265763) B3265763
theorem B6199861 : Blo 2175435 6199861 := bbase (se 5 (by rfl) ⟨290618, by rfl⟩ : syracuseStep 6199861 = 581237) (by norm_num)
theorem B8266481 : Blo 2175435 8266481 := bstep (se 2 (by rfl) ⟨3099930, by rfl⟩ : syracuseStep 8266481 = 6199861) B6199861
theorem B5510987 : Blo 2175435 5510987 := bstep (se 1 (by rfl) ⟨4133240, by rfl⟩ : syracuseStep 5510987 = 8266481) B8266481
theorem B3673991 : Blo 2175435 3673991 := bstep (se 1 (by rfl) ⟨2755493, by rfl⟩ : syracuseStep 3673991 = 5510987) B5510987
theorem B2449327 : Blo 2175435 2449327 := bstep (se 1 (by rfl) ⟨1836995, by rfl⟩ : syracuseStep 2449327 = 3673991) B3673991
theorem B3265769 : Blo 2175435 3265769 := bstep (se 2 (by rfl) ⟨1224663, by rfl⟩ : syracuseStep 3265769 = 2449327) B2449327
theorem B2177179 : Blo 2175435 2177179 := bstep (se 1 (by rfl) ⟨1632884, by rfl⟩ : syracuseStep 2177179 = 3265769) B3265769
theorem B50275669 : Blo 2175435 50275669 := bbase (se 12 (by rfl) ⟨18411, by rfl⟩ : syracuseStep 50275669 = 36823) (by norm_num)
theorem B67034225 : Blo 2175435 67034225 := bstep (se 2 (by rfl) ⟨25137834, by rfl⟩ : syracuseStep 67034225 = 50275669) B50275669
theorem B44689483 : Blo 2175435 44689483 := bstep (se 1 (by rfl) ⟨33517112, by rfl⟩ : syracuseStep 44689483 = 67034225) B67034225
theorem B59585977 : Blo 2175435 59585977 := bstep (se 2 (by rfl) ⟨22344741, by rfl⟩ : syracuseStep 59585977 = 44689483) B44689483
theorem B79447969 : Blo 2175435 79447969 := bstep (se 2 (by rfl) ⟨29792988, by rfl⟩ : syracuseStep 79447969 = 59585977) B59585977
theorem B105930625 : Blo 2175435 105930625 := bstep (se 2 (by rfl) ⟨39723984, by rfl⟩ : syracuseStep 105930625 = 79447969) B79447969
theorem B141240833 : Blo 2175435 141240833 := bstep (se 2 (by rfl) ⟨52965312, by rfl⟩ : syracuseStep 141240833 = 105930625) B105930625
theorem B94160555 : Blo 2175435 94160555 := bstep (se 1 (by rfl) ⟨70620416, by rfl⟩ : syracuseStep 94160555 = 141240833) B141240833
theorem B62773703 : Blo 2175435 62773703 := bstep (se 1 (by rfl) ⟨47080277, by rfl⟩ : syracuseStep 62773703 = 94160555) B94160555
theorem B41849135 : Blo 2175435 41849135 := bstep (se 1 (by rfl) ⟨31386851, by rfl⟩ : syracuseStep 41849135 = 62773703) B62773703
theorem B27899423 : Blo 2175435 27899423 := bstep (se 1 (by rfl) ⟨20924567, by rfl⟩ : syracuseStep 27899423 = 41849135) B41849135
theorem B18599615 : Blo 2175435 18599615 := bstep (se 1 (by rfl) ⟨13949711, by rfl⟩ : syracuseStep 18599615 = 27899423) B27899423
theorem B12399743 : Blo 2175435 12399743 := bstep (se 1 (by rfl) ⟨9299807, by rfl⟩ : syracuseStep 12399743 = 18599615) B18599615
theorem B8266495 : Blo 2175435 8266495 := bstep (se 1 (by rfl) ⟨6199871, by rfl⟩ : syracuseStep 8266495 = 12399743) B12399743
theorem B11021993 : Blo 2175435 11021993 := bstep (se 2 (by rfl) ⟨4133247, by rfl⟩ : syracuseStep 11021993 = 8266495) B8266495
theorem B7347995 : Blo 2175435 7347995 := bstep (se 1 (by rfl) ⟨5510996, by rfl⟩ : syracuseStep 7347995 = 11021993) B11021993
theorem B4898663 : Blo 2175435 4898663 := bstep (se 1 (by rfl) ⟨3673997, by rfl⟩ : syracuseStep 4898663 = 7347995) B7347995
theorem B3265775 : Blo 2175435 3265775 := bstep (se 1 (by rfl) ⟨2449331, by rfl⟩ : syracuseStep 3265775 = 4898663) B4898663
theorem B2177183 : Blo 2175435 2177183 := bstep (se 1 (by rfl) ⟨1632887, by rfl⟩ : syracuseStep 2177183 = 3265775) B3265775
theorem B3265781 : Blo 2175435 3265781 := bbase (se 5 (by rfl) ⟨153083, by rfl⟩ : syracuseStep 3265781 = 306167) (by norm_num)
theorem B2177187 : Blo 2175435 2177187 := bstep (se 1 (by rfl) ⟨1632890, by rfl⟩ : syracuseStep 2177187 = 3265781) B3265781
theorem B2615581 : Blo 2175435 2615581 := bbase (se 3 (by rfl) ⟨490421, by rfl⟩ : syracuseStep 2615581 = 980843) (by norm_num)
theorem B13949765 : Blo 2175435 13949765 := bstep (se 4 (by rfl) ⟨1307790, by rfl⟩ : syracuseStep 13949765 = 2615581) B2615581
theorem B9299843 : Blo 2175435 9299843 := bstep (se 1 (by rfl) ⟨6974882, by rfl⟩ : syracuseStep 9299843 = 13949765) B13949765
theorem B6199895 : Blo 2175435 6199895 := bstep (se 1 (by rfl) ⟨4649921, by rfl⟩ : syracuseStep 6199895 = 9299843) B9299843
theorem B4133263 : Blo 2175435 4133263 := bstep (se 1 (by rfl) ⟨3099947, by rfl⟩ : syracuseStep 4133263 = 6199895) B6199895
theorem B5511017 : Blo 2175435 5511017 := bstep (se 2 (by rfl) ⟨2066631, by rfl⟩ : syracuseStep 5511017 = 4133263) B4133263
theorem B3674011 : Blo 2175435 3674011 := bstep (se 1 (by rfl) ⟨2755508, by rfl⟩ : syracuseStep 3674011 = 5511017) B5511017
theorem B4898681 : Blo 2175435 4898681 := bstep (se 2 (by rfl) ⟨1837005, by rfl⟩ : syracuseStep 4898681 = 3674011) B3674011
theorem B3265787 : Blo 2175435 3265787 := bstep (se 1 (by rfl) ⟨2449340, by rfl⟩ : syracuseStep 3265787 = 4898681) B4898681
theorem B2177191 : Blo 2175435 2177191 := bstep (se 1 (by rfl) ⟨1632893, by rfl⟩ : syracuseStep 2177191 = 3265787) B3265787
theorem B2449345 : Blo 2175435 2449345 := bbase (se 2 (by rfl) ⟨918504, by rfl⟩ : syracuseStep 2449345 = 1837009) (by norm_num)
theorem B3265793 : Blo 2175435 3265793 := bstep (se 2 (by rfl) ⟨1224672, by rfl⟩ : syracuseStep 3265793 = 2449345) B2449345
theorem B2177195 : Blo 2175435 2177195 := bstep (se 1 (by rfl) ⟨1632896, by rfl⟩ : syracuseStep 2177195 = 3265793) B3265793
theorem B5511037 : Blo 2175435 5511037 := bbase (se 3 (by rfl) ⟨1033319, by rfl⟩ : syracuseStep 5511037 = 2066639) (by norm_num)
theorem B7348049 : Blo 2175435 7348049 := bstep (se 2 (by rfl) ⟨2755518, by rfl⟩ : syracuseStep 7348049 = 5511037) B5511037
theorem B4898699 : Blo 2175435 4898699 := bstep (se 1 (by rfl) ⟨3674024, by rfl⟩ : syracuseStep 4898699 = 7348049) B7348049
theorem B3265799 : Blo 2175435 3265799 := bstep (se 1 (by rfl) ⟨2449349, by rfl⟩ : syracuseStep 3265799 = 4898699) B4898699
theorem B2177199 : Blo 2175435 2177199 := bstep (se 1 (by rfl) ⟨1632899, by rfl⟩ : syracuseStep 2177199 = 3265799) B3265799
theorem B3265805 : Blo 2175435 3265805 := bbase (se 3 (by rfl) ⟨612338, by rfl⟩ : syracuseStep 3265805 = 1224677) (by norm_num)
theorem B2177203 : Blo 2175435 2177203 := bstep (se 1 (by rfl) ⟨1632902, by rfl⟩ : syracuseStep 2177203 = 3265805) B3265805
theorem B4898717 : Blo 2175435 4898717 := bbase (se 3 (by rfl) ⟨918509, by rfl⟩ : syracuseStep 4898717 = 1837019) (by norm_num)
theorem B3265811 : Blo 2175435 3265811 := bstep (se 1 (by rfl) ⟨2449358, by rfl⟩ : syracuseStep 3265811 = 4898717) B4898717
theorem B2177207 : Blo 2175435 2177207 := bstep (se 1 (by rfl) ⟨1632905, by rfl⟩ : syracuseStep 2177207 = 3265811) B3265811
theorem B3674045 : Blo 2175435 3674045 := bbase (se 3 (by rfl) ⟨688883, by rfl⟩ : syracuseStep 3674045 = 1377767) (by norm_num)
theorem B2449363 : Blo 2175435 2449363 := bstep (se 1 (by rfl) ⟨1837022, by rfl⟩ : syracuseStep 2449363 = 3674045) B3674045
theorem B3265817 : Blo 2175435 3265817 := bstep (se 2 (by rfl) ⟨1224681, by rfl⟩ : syracuseStep 3265817 = 2449363) B2449363
theorem B2177211 : Blo 2175435 2177211 := bstep (se 1 (by rfl) ⟨1632908, by rfl⟩ : syracuseStep 2177211 = 3265817) B3265817
theorem B12399925 : Blo 2175435 12399925 := bbase (se 5 (by rfl) ⟨581246, by rfl⟩ : syracuseStep 12399925 = 1162493) (by norm_num)
theorem B16533233 : Blo 2175435 16533233 := bstep (se 2 (by rfl) ⟨6199962, by rfl⟩ : syracuseStep 16533233 = 12399925) B12399925
theorem B11022155 : Blo 2175435 11022155 := bstep (se 1 (by rfl) ⟨8266616, by rfl⟩ : syracuseStep 11022155 = 16533233) B16533233
theorem B7348103 : Blo 2175435 7348103 := bstep (se 1 (by rfl) ⟨5511077, by rfl⟩ : syracuseStep 7348103 = 11022155) B11022155
theorem B4898735 : Blo 2175435 4898735 := bstep (se 1 (by rfl) ⟨3674051, by rfl⟩ : syracuseStep 4898735 = 7348103) B7348103
theorem B3265823 : Blo 2175435 3265823 := bstep (se 1 (by rfl) ⟨2449367, by rfl⟩ : syracuseStep 3265823 = 4898735) B4898735
theorem B2177215 : Blo 2175435 2177215 := bstep (se 1 (by rfl) ⟨1632911, by rfl⟩ : syracuseStep 2177215 = 3265823) B3265823
theorem B3265829 : Blo 2175435 3265829 := bbase (se 4 (by rfl) ⟨306171, by rfl⟩ : syracuseStep 3265829 = 612343) (by norm_num)
theorem B2177219 : Blo 2175435 2177219 := bstep (se 1 (by rfl) ⟨1632914, by rfl⟩ : syracuseStep 2177219 = 3265829) B3265829
theorem B2755549 : Blo 2175435 2755549 := bbase (se 3 (by rfl) ⟨516665, by rfl⟩ : syracuseStep 2755549 = 1033331) (by norm_num)
theorem B3674065 : Blo 2175435 3674065 := bstep (se 2 (by rfl) ⟨1377774, by rfl⟩ : syracuseStep 3674065 = 2755549) B2755549
theorem B4898753 : Blo 2175435 4898753 := bstep (se 2 (by rfl) ⟨1837032, by rfl⟩ : syracuseStep 4898753 = 3674065) B3674065
theorem B3265835 : Blo 2175435 3265835 := bstep (se 1 (by rfl) ⟨2449376, by rfl⟩ : syracuseStep 3265835 = 4898753) B4898753
theorem B2177223 : Blo 2175435 2177223 := bstep (se 1 (by rfl) ⟨1632917, by rfl⟩ : syracuseStep 2177223 = 3265835) B3265835
theorem B2449381 : Blo 2175435 2449381 := bbase (se 4 (by rfl) ⟨229629, by rfl⟩ : syracuseStep 2449381 = 459259) (by norm_num)
theorem B3265841 : Blo 2175435 3265841 := bstep (se 2 (by rfl) ⟨1224690, by rfl⟩ : syracuseStep 3265841 = 2449381) B2449381
theorem B2177227 : Blo 2175435 2177227 := bstep (se 1 (by rfl) ⟨1632920, by rfl⟩ : syracuseStep 2177227 = 3265841) B3265841
theorem B10462517 : Blo 2175435 10462517 := bbase (se 5 (by rfl) ⟨490430, by rfl⟩ : syracuseStep 10462517 = 980861) (by norm_num)
theorem B6975011 : Blo 2175435 6975011 := bstep (se 1 (by rfl) ⟨5231258, by rfl⟩ : syracuseStep 6975011 = 10462517) B10462517
theorem B4650007 : Blo 2175435 4650007 := bstep (se 1 (by rfl) ⟨3487505, by rfl⟩ : syracuseStep 4650007 = 6975011) B6975011
theorem B6200009 : Blo 2175435 6200009 := bstep (se 2 (by rfl) ⟨2325003, by rfl⟩ : syracuseStep 6200009 = 4650007) B4650007
theorem B4133339 : Blo 2175435 4133339 := bstep (se 1 (by rfl) ⟨3100004, by rfl⟩ : syracuseStep 4133339 = 6200009) B6200009
theorem B2755559 : Blo 2175435 2755559 := bstep (se 1 (by rfl) ⟨2066669, by rfl⟩ : syracuseStep 2755559 = 4133339) B4133339
theorem B7348157 : Blo 2175435 7348157 := bstep (se 3 (by rfl) ⟨1377779, by rfl⟩ : syracuseStep 7348157 = 2755559) B2755559
theorem B4898771 : Blo 2175435 4898771 := bstep (se 1 (by rfl) ⟨3674078, by rfl⟩ : syracuseStep 4898771 = 7348157) B7348157
theorem B3265847 : Blo 2175435 3265847 := bstep (se 1 (by rfl) ⟨2449385, by rfl⟩ : syracuseStep 3265847 = 4898771) B4898771
theorem B2177231 : Blo 2175435 2177231 := bstep (se 1 (by rfl) ⟨1632923, by rfl⟩ : syracuseStep 2177231 = 3265847) B3265847
theorem B3265853 : Blo 2175435 3265853 := bbase (se 3 (by rfl) ⟨612347, by rfl⟩ : syracuseStep 3265853 = 1224695) (by norm_num)
theorem B2177235 : Blo 2175435 2177235 := bstep (se 1 (by rfl) ⟨1632926, by rfl⟩ : syracuseStep 2177235 = 3265853) B3265853
theorem B4898789 : Blo 2175435 4898789 := bbase (se 4 (by rfl) ⟨459261, by rfl⟩ : syracuseStep 4898789 = 918523) (by norm_num)
theorem B3265859 : Blo 2175435 3265859 := bstep (se 1 (by rfl) ⟨2449394, by rfl⟩ : syracuseStep 3265859 = 4898789) B4898789
theorem B2177239 : Blo 2175435 2177239 := bstep (se 1 (by rfl) ⟨1632929, by rfl⟩ : syracuseStep 2177239 = 3265859) B3265859
theorem B5511149 : Blo 2175435 5511149 := bbase (se 3 (by rfl) ⟨1033340, by rfl⟩ : syracuseStep 5511149 = 2066681) (by norm_num)
theorem B3674099 : Blo 2175435 3674099 := bstep (se 1 (by rfl) ⟨2755574, by rfl⟩ : syracuseStep 3674099 = 5511149) B5511149
theorem B2449399 : Blo 2175435 2449399 := bstep (se 1 (by rfl) ⟨1837049, by rfl⟩ : syracuseStep 2449399 = 3674099) B3674099
theorem B3265865 : Blo 2175435 3265865 := bstep (se 2 (by rfl) ⟨1224699, by rfl⟩ : syracuseStep 3265865 = 2449399) B2449399
theorem B2177243 : Blo 2175435 2177243 := bstep (se 1 (by rfl) ⟨1632932, by rfl⟩ : syracuseStep 2177243 = 3265865) B3265865
theorem B2942605 : Blo 2175435 2942605 := bbase (se 3 (by rfl) ⟨551738, by rfl⟩ : syracuseStep 2942605 = 1103477) (by norm_num)
theorem B3923473 : Blo 2175435 3923473 := bstep (se 2 (by rfl) ⟨1471302, by rfl⟩ : syracuseStep 3923473 = 2942605) B2942605
theorem B5231297 : Blo 2175435 5231297 := bstep (se 2 (by rfl) ⟨1961736, by rfl⟩ : syracuseStep 5231297 = 3923473) B3923473
theorem B3487531 : Blo 2175435 3487531 := bstep (se 1 (by rfl) ⟨2615648, by rfl⟩ : syracuseStep 3487531 = 5231297) B5231297
theorem B4650041 : Blo 2175435 4650041 := bstep (se 2 (by rfl) ⟨1743765, by rfl⟩ : syracuseStep 4650041 = 3487531) B3487531
theorem B3100027 : Blo 2175435 3100027 := bstep (se 1 (by rfl) ⟨2325020, by rfl⟩ : syracuseStep 3100027 = 4650041) B4650041
theorem B4133369 : Blo 2175435 4133369 := bstep (se 2 (by rfl) ⟨1550013, by rfl⟩ : syracuseStep 4133369 = 3100027) B3100027
theorem B11022317 : Blo 2175435 11022317 := bstep (se 3 (by rfl) ⟨2066684, by rfl⟩ : syracuseStep 11022317 = 4133369) B4133369
theorem B7348211 : Blo 2175435 7348211 := bstep (se 1 (by rfl) ⟨5511158, by rfl⟩ : syracuseStep 7348211 = 11022317) B11022317
theorem B4898807 : Blo 2175435 4898807 := bstep (se 1 (by rfl) ⟨3674105, by rfl⟩ : syracuseStep 4898807 = 7348211) B7348211
theorem B3265871 : Blo 2175435 3265871 := bstep (se 1 (by rfl) ⟨2449403, by rfl⟩ : syracuseStep 3265871 = 4898807) B4898807
theorem B2177247 : Blo 2175435 2177247 := bstep (se 1 (by rfl) ⟨1632935, by rfl⟩ : syracuseStep 2177247 = 3265871) B3265871
theorem B3265877 : Blo 2175435 3265877 := bbase (se 15 (by rfl) ⟨149, by rfl⟩ : syracuseStep 3265877 = 299) (by norm_num)
theorem B2177251 : Blo 2175435 2177251 := bstep (se 1 (by rfl) ⟨1632938, by rfl⟩ : syracuseStep 2177251 = 3265877) B3265877
theorem B2325029 : Blo 2175435 2325029 := bbase (se 4 (by rfl) ⟨217971, by rfl⟩ : syracuseStep 2325029 = 435943) (by norm_num)
theorem B6200077 : Blo 2175435 6200077 := bstep (se 3 (by rfl) ⟨1162514, by rfl⟩ : syracuseStep 6200077 = 2325029) B2325029
theorem B8266769 : Blo 2175435 8266769 := bstep (se 2 (by rfl) ⟨3100038, by rfl⟩ : syracuseStep 8266769 = 6200077) B6200077
theorem B5511179 : Blo 2175435 5511179 := bstep (se 1 (by rfl) ⟨4133384, by rfl⟩ : syracuseStep 5511179 = 8266769) B8266769
theorem B3674119 : Blo 2175435 3674119 := bstep (se 1 (by rfl) ⟨2755589, by rfl⟩ : syracuseStep 3674119 = 5511179) B5511179
theorem B4898825 : Blo 2175435 4898825 := bstep (se 2 (by rfl) ⟨1837059, by rfl⟩ : syracuseStep 4898825 = 3674119) B3674119
theorem B3265883 : Blo 2175435 3265883 := bstep (se 1 (by rfl) ⟨2449412, by rfl⟩ : syracuseStep 3265883 = 4898825) B4898825
theorem B2177255 : Blo 2175435 2177255 := bstep (se 1 (by rfl) ⟨1632941, by rfl⟩ : syracuseStep 2177255 = 3265883) B3265883
theorem B2449417 : Blo 2175435 2449417 := bbase (se 2 (by rfl) ⟨918531, by rfl⟩ : syracuseStep 2449417 = 1837063) (by norm_num)
theorem B3265889 : Blo 2175435 3265889 := bstep (se 2 (by rfl) ⟨1224708, by rfl⟩ : syracuseStep 3265889 = 2449417) B2449417
theorem B2177259 : Blo 2175435 2177259 := bstep (se 1 (by rfl) ⟨1632944, by rfl⟩ : syracuseStep 2177259 = 3265889) B3265889
theorem B8827877 : Blo 2175435 8827877 := bbase (se 4 (by rfl) ⟨827613, by rfl⟩ : syracuseStep 8827877 = 1655227) (by norm_num)
theorem B23541005 : Blo 2175435 23541005 := bstep (se 3 (by rfl) ⟨4413938, by rfl⟩ : syracuseStep 23541005 = 8827877) B8827877
theorem B15694003 : Blo 2175435 15694003 := bstep (se 1 (by rfl) ⟨11770502, by rfl⟩ : syracuseStep 15694003 = 23541005) B23541005
theorem B20925337 : Blo 2175435 20925337 := bstep (se 2 (by rfl) ⟨7847001, by rfl⟩ : syracuseStep 20925337 = 15694003) B15694003
theorem B27900449 : Blo 2175435 27900449 := bstep (se 2 (by rfl) ⟨10462668, by rfl⟩ : syracuseStep 27900449 = 20925337) B20925337
theorem B18600299 : Blo 2175435 18600299 := bstep (se 1 (by rfl) ⟨13950224, by rfl⟩ : syracuseStep 18600299 = 27900449) B27900449
theorem B12400199 : Blo 2175435 12400199 := bstep (se 1 (by rfl) ⟨9300149, by rfl⟩ : syracuseStep 12400199 = 18600299) B18600299
theorem B8266799 : Blo 2175435 8266799 := bstep (se 1 (by rfl) ⟨6200099, by rfl⟩ : syracuseStep 8266799 = 12400199) B12400199
theorem B5511199 : Blo 2175435 5511199 := bstep (se 1 (by rfl) ⟨4133399, by rfl⟩ : syracuseStep 5511199 = 8266799) B8266799
theorem B7348265 : Blo 2175435 7348265 := bstep (se 2 (by rfl) ⟨2755599, by rfl⟩ : syracuseStep 7348265 = 5511199) B5511199
theorem B4898843 : Blo 2175435 4898843 := bstep (se 1 (by rfl) ⟨3674132, by rfl⟩ : syracuseStep 4898843 = 7348265) B7348265
theorem B3265895 : Blo 2175435 3265895 := bstep (se 1 (by rfl) ⟨2449421, by rfl⟩ : syracuseStep 3265895 = 4898843) B4898843
theorem B2177263 : Blo 2175435 2177263 := bstep (se 1 (by rfl) ⟨1632947, by rfl⟩ : syracuseStep 2177263 = 3265895) B3265895
theorem B3265901 : Blo 2175435 3265901 := bbase (se 3 (by rfl) ⟨612356, by rfl⟩ : syracuseStep 3265901 = 1224713) (by norm_num)
theorem B2177267 : Blo 2175435 2177267 := bstep (se 1 (by rfl) ⟨1632950, by rfl⟩ : syracuseStep 2177267 = 3265901) B3265901
theorem B4898861 : Blo 2175435 4898861 := bbase (se 3 (by rfl) ⟨918536, by rfl⟩ : syracuseStep 4898861 = 1837073) (by norm_num)
theorem B3265907 : Blo 2175435 3265907 := bstep (se 1 (by rfl) ⟨2449430, by rfl⟩ : syracuseStep 3265907 = 4898861) B4898861
theorem B2177271 : Blo 2175435 2177271 := bstep (se 1 (by rfl) ⟨1632953, by rfl⟩ : syracuseStep 2177271 = 3265907) B3265907
theorem B5302741 : Blo 2175435 5302741 := bbase (se 7 (by rfl) ⟨62141, by rfl⟩ : syracuseStep 5302741 = 124283) (by norm_num)
theorem B7070321 : Blo 2175435 7070321 := bstep (se 2 (by rfl) ⟨2651370, by rfl⟩ : syracuseStep 7070321 = 5302741) B5302741
theorem B4713547 : Blo 2175435 4713547 := bstep (se 1 (by rfl) ⟨3535160, by rfl⟩ : syracuseStep 4713547 = 7070321) B7070321
theorem B6284729 : Blo 2175435 6284729 := bstep (se 2 (by rfl) ⟨2356773, by rfl⟩ : syracuseStep 6284729 = 4713547) B4713547
theorem B4189819 : Blo 2175435 4189819 := bstep (se 1 (by rfl) ⟨3142364, by rfl⟩ : syracuseStep 4189819 = 6284729) B6284729
theorem B5586425 : Blo 2175435 5586425 := bstep (se 2 (by rfl) ⟨2094909, by rfl⟩ : syracuseStep 5586425 = 4189819) B4189819
theorem B3724283 : Blo 2175435 3724283 := bstep (se 1 (by rfl) ⟨2793212, by rfl⟩ : syracuseStep 3724283 = 5586425) B5586425
theorem B2482855 : Blo 2175435 2482855 := bstep (se 1 (by rfl) ⟨1862141, by rfl⟩ : syracuseStep 2482855 = 3724283) B3724283
theorem B13241893 : Blo 2175435 13241893 := bstep (se 4 (by rfl) ⟨1241427, by rfl⟩ : syracuseStep 13241893 = 2482855) B2482855
theorem B17655857 : Blo 2175435 17655857 := bstep (se 2 (by rfl) ⟨6620946, by rfl⟩ : syracuseStep 17655857 = 13241893) B13241893
theorem B11770571 : Blo 2175435 11770571 := bstep (se 1 (by rfl) ⟨8827928, by rfl⟩ : syracuseStep 11770571 = 17655857) B17655857
theorem B7847047 : Blo 2175435 7847047 := bstep (se 1 (by rfl) ⟨5885285, by rfl⟩ : syracuseStep 7847047 = 11770571) B11770571
theorem B10462729 : Blo 2175435 10462729 := bstep (se 2 (by rfl) ⟨3923523, by rfl⟩ : syracuseStep 10462729 = 7847047) B7847047
theorem B13950305 : Blo 2175435 13950305 := bstep (se 2 (by rfl) ⟨5231364, by rfl⟩ : syracuseStep 13950305 = 10462729) B10462729
theorem B9300203 : Blo 2175435 9300203 := bstep (se 1 (by rfl) ⟨6975152, by rfl⟩ : syracuseStep 9300203 = 13950305) B13950305
theorem B6200135 : Blo 2175435 6200135 := bstep (se 1 (by rfl) ⟨4650101, by rfl⟩ : syracuseStep 6200135 = 9300203) B9300203
theorem B4133423 : Blo 2175435 4133423 := bstep (se 1 (by rfl) ⟨3100067, by rfl⟩ : syracuseStep 4133423 = 6200135) B6200135
theorem B2755615 : Blo 2175435 2755615 := bstep (se 1 (by rfl) ⟨2066711, by rfl⟩ : syracuseStep 2755615 = 4133423) B4133423
theorem B3674153 : Blo 2175435 3674153 := bstep (se 2 (by rfl) ⟨1377807, by rfl⟩ : syracuseStep 3674153 = 2755615) B2755615
theorem B2449435 : Blo 2175435 2449435 := bstep (se 1 (by rfl) ⟨1837076, by rfl⟩ : syracuseStep 2449435 = 3674153) B3674153
theorem B3265913 : Blo 2175435 3265913 := bstep (se 2 (by rfl) ⟨1224717, by rfl⟩ : syracuseStep 3265913 = 2449435) B2449435
theorem B2177275 : Blo 2175435 2177275 := bstep (se 1 (by rfl) ⟨1632956, by rfl⟩ : syracuseStep 2177275 = 3265913) B3265913
theorem B2793217 : Blo 2175435 2793217 := bbase (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) (by norm_num)
theorem B3724289 : Blo 2175435 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B2482859 : Blo 2175435 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B6620957 : Blo 2175435 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B4413971 : Blo 2175435 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B11770589 : Blo 2175435 11770589 := bstep (se 3 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 11770589 = 4413971) B4413971
theorem B7847059 : Blo 2175435 7847059 := bstep (se 1 (by rfl) ⟨5885294, by rfl⟩ : syracuseStep 7847059 = 11770589) B11770589
theorem B10462745 : Blo 2175435 10462745 := bstep (se 2 (by rfl) ⟨3923529, by rfl⟩ : syracuseStep 10462745 = 7847059) B7847059
theorem B6975163 : Blo 2175435 6975163 := bstep (se 1 (by rfl) ⟨5231372, by rfl⟩ : syracuseStep 6975163 = 10462745) B10462745
theorem B37200869 : Blo 2175435 37200869 := bstep (se 4 (by rfl) ⟨3487581, by rfl⟩ : syracuseStep 37200869 = 6975163) B6975163
theorem B24800579 : Blo 2175435 24800579 := bstep (se 1 (by rfl) ⟨18600434, by rfl⟩ : syracuseStep 24800579 = 37200869) B37200869
theorem B16533719 : Blo 2175435 16533719 := bstep (se 1 (by rfl) ⟨12400289, by rfl⟩ : syracuseStep 16533719 = 24800579) B24800579
theorem B11022479 : Blo 2175435 11022479 := bstep (se 1 (by rfl) ⟨8266859, by rfl⟩ : syracuseStep 11022479 = 16533719) B16533719
theorem B7348319 : Blo 2175435 7348319 := bstep (se 1 (by rfl) ⟨5511239, by rfl⟩ : syracuseStep 7348319 = 11022479) B11022479
theorem B4898879 : Blo 2175435 4898879 := bstep (se 1 (by rfl) ⟨3674159, by rfl⟩ : syracuseStep 4898879 = 7348319) B7348319
theorem B3265919 : Blo 2175435 3265919 := bstep (se 1 (by rfl) ⟨2449439, by rfl⟩ : syracuseStep 3265919 = 4898879) B4898879
theorem B2177279 : Blo 2175435 2177279 := bstep (se 1 (by rfl) ⟨1632959, by rfl⟩ : syracuseStep 2177279 = 3265919) B3265919
theorem B3265925 : Blo 2175435 3265925 := bbase (se 4 (by rfl) ⟨306180, by rfl⟩ : syracuseStep 3265925 = 612361) (by norm_num)
theorem B2177283 : Blo 2175435 2177283 := bstep (se 1 (by rfl) ⟨1632962, by rfl⟩ : syracuseStep 2177283 = 3265925) B3265925
theorem B3674173 : Blo 2175435 3674173 := bbase (se 3 (by rfl) ⟨688907, by rfl⟩ : syracuseStep 3674173 = 1377815) (by norm_num)
theorem B4898897 : Blo 2175435 4898897 := bstep (se 2 (by rfl) ⟨1837086, by rfl⟩ : syracuseStep 4898897 = 3674173) B3674173
theorem B3265931 : Blo 2175435 3265931 := bstep (se 1 (by rfl) ⟨2449448, by rfl⟩ : syracuseStep 3265931 = 4898897) B4898897
theorem B2177287 : Blo 2175435 2177287 := bstep (se 1 (by rfl) ⟨1632965, by rfl⟩ : syracuseStep 2177287 = 3265931) B3265931
theorem B2449453 : Blo 2175435 2449453 := bbase (se 3 (by rfl) ⟨459272, by rfl⟩ : syracuseStep 2449453 = 918545) (by norm_num)
theorem B3265937 : Blo 2175435 3265937 := bstep (se 2 (by rfl) ⟨1224726, by rfl⟩ : syracuseStep 3265937 = 2449453) B2449453
theorem B2177291 : Blo 2175435 2177291 := bstep (se 1 (by rfl) ⟨1632968, by rfl⟩ : syracuseStep 2177291 = 3265937) B3265937
theorem B7348373 : Blo 2175435 7348373 := bbase (se 6 (by rfl) ⟨172227, by rfl⟩ : syracuseStep 7348373 = 344455) (by norm_num)
theorem B4898915 : Blo 2175435 4898915 := bstep (se 1 (by rfl) ⟨3674186, by rfl⟩ : syracuseStep 4898915 = 7348373) B7348373
theorem B3265943 : Blo 2175435 3265943 := bstep (se 1 (by rfl) ⟨2449457, by rfl⟩ : syracuseStep 3265943 = 4898915) B4898915
theorem B2177295 : Blo 2175435 2177295 := bstep (se 1 (by rfl) ⟨1632971, by rfl⟩ : syracuseStep 2177295 = 3265943) B3265943
theorem B3265949 : Blo 2175435 3265949 := bbase (se 3 (by rfl) ⟨612365, by rfl⟩ : syracuseStep 3265949 = 1224731) (by norm_num)
theorem B2177299 : Blo 2175435 2177299 := bstep (se 1 (by rfl) ⟨1632974, by rfl⟩ : syracuseStep 2177299 = 3265949) B3265949
theorem B4898933 : Blo 2175435 4898933 := bbase (se 5 (by rfl) ⟨229637, by rfl⟩ : syracuseStep 4898933 = 459275) (by norm_num)
theorem B3265955 : Blo 2175435 3265955 := bstep (se 1 (by rfl) ⟨2449466, by rfl⟩ : syracuseStep 3265955 = 4898933) B4898933
theorem B2177303 : Blo 2175435 2177303 := bstep (se 1 (by rfl) ⟨1632977, by rfl⟩ : syracuseStep 2177303 = 3265955) B3265955
theorem B3923581 : Blo 2175435 3923581 := bbase (se 3 (by rfl) ⟨735671, by rfl⟩ : syracuseStep 3923581 = 1471343) (by norm_num)
theorem B5231441 : Blo 2175435 5231441 := bstep (se 2 (by rfl) ⟨1961790, by rfl⟩ : syracuseStep 5231441 = 3923581) B3923581
theorem B3487627 : Blo 2175435 3487627 := bstep (se 1 (by rfl) ⟨2615720, by rfl⟩ : syracuseStep 3487627 = 5231441) B5231441
theorem B18600677 : Blo 2175435 18600677 := bstep (se 4 (by rfl) ⟨1743813, by rfl⟩ : syracuseStep 18600677 = 3487627) B3487627
theorem B12400451 : Blo 2175435 12400451 := bstep (se 1 (by rfl) ⟨9300338, by rfl⟩ : syracuseStep 12400451 = 18600677) B18600677
theorem B8266967 : Blo 2175435 8266967 := bstep (se 1 (by rfl) ⟨6200225, by rfl⟩ : syracuseStep 8266967 = 12400451) B12400451
theorem B5511311 : Blo 2175435 5511311 := bstep (se 1 (by rfl) ⟨4133483, by rfl⟩ : syracuseStep 5511311 = 8266967) B8266967
theorem B3674207 : Blo 2175435 3674207 := bstep (se 1 (by rfl) ⟨2755655, by rfl⟩ : syracuseStep 3674207 = 5511311) B5511311
theorem B2449471 : Blo 2175435 2449471 := bstep (se 1 (by rfl) ⟨1837103, by rfl⟩ : syracuseStep 2449471 = 3674207) B3674207
theorem B3265961 : Blo 2175435 3265961 := bstep (se 2 (by rfl) ⟨1224735, by rfl⟩ : syracuseStep 3265961 = 2449471) B2449471
theorem B2177307 : Blo 2175435 2177307 := bstep (se 1 (by rfl) ⟨1632980, by rfl⟩ : syracuseStep 2177307 = 3265961) B3265961
theorem B8266981 : Blo 2175435 8266981 := bbase (se 4 (by rfl) ⟨775029, by rfl⟩ : syracuseStep 8266981 = 1550059) (by norm_num)
theorem B11022641 : Blo 2175435 11022641 := bstep (se 2 (by rfl) ⟨4133490, by rfl⟩ : syracuseStep 11022641 = 8266981) B8266981
theorem B7348427 : Blo 2175435 7348427 := bstep (se 1 (by rfl) ⟨5511320, by rfl⟩ : syracuseStep 7348427 = 11022641) B11022641
theorem B4898951 : Blo 2175435 4898951 := bstep (se 1 (by rfl) ⟨3674213, by rfl⟩ : syracuseStep 4898951 = 7348427) B7348427
theorem B3265967 : Blo 2175435 3265967 := bstep (se 1 (by rfl) ⟨2449475, by rfl⟩ : syracuseStep 3265967 = 4898951) B4898951
theorem B2177311 : Blo 2175435 2177311 := bstep (se 1 (by rfl) ⟨1632983, by rfl⟩ : syracuseStep 2177311 = 3265967) B3265967
theorem B3265973 : Blo 2175435 3265973 := bbase (se 5 (by rfl) ⟨153092, by rfl⟩ : syracuseStep 3265973 = 306185) (by norm_num)
theorem B2177315 : Blo 2175435 2177315 := bstep (se 1 (by rfl) ⟨1632986, by rfl⟩ : syracuseStep 2177315 = 3265973) B3265973
theorem B5511341 : Blo 2175435 5511341 := bbase (se 3 (by rfl) ⟨1033376, by rfl⟩ : syracuseStep 5511341 = 2066753) (by norm_num)
theorem B3674227 : Blo 2175435 3674227 := bstep (se 1 (by rfl) ⟨2755670, by rfl⟩ : syracuseStep 3674227 = 5511341) B5511341
theorem B4898969 : Blo 2175435 4898969 := bstep (se 2 (by rfl) ⟨1837113, by rfl⟩ : syracuseStep 4898969 = 3674227) B3674227
theorem B3265979 : Blo 2175435 3265979 := bstep (se 1 (by rfl) ⟨2449484, by rfl⟩ : syracuseStep 3265979 = 4898969) B4898969
theorem B2177319 : Blo 2175435 2177319 := bstep (se 1 (by rfl) ⟨1632989, by rfl⟩ : syracuseStep 2177319 = 3265979) B3265979
theorem B2449489 : Blo 2175435 2449489 := bbase (se 2 (by rfl) ⟨918558, by rfl⟩ : syracuseStep 2449489 = 1837117) (by norm_num)
theorem B3265985 : Blo 2175435 3265985 := bstep (se 2 (by rfl) ⟨1224744, by rfl⟩ : syracuseStep 3265985 = 2449489) B2449489
theorem B2177323 : Blo 2175435 2177323 := bstep (se 1 (by rfl) ⟨1632992, by rfl⟩ : syracuseStep 2177323 = 3265985) B3265985
theorem B3100141 : Blo 2175435 3100141 := bbase (se 3 (by rfl) ⟨581276, by rfl⟩ : syracuseStep 3100141 = 1162553) (by norm_num)
theorem B4133521 : Blo 2175435 4133521 := bstep (se 2 (by rfl) ⟨1550070, by rfl⟩ : syracuseStep 4133521 = 3100141) B3100141
theorem B5511361 : Blo 2175435 5511361 := bstep (se 2 (by rfl) ⟨2066760, by rfl⟩ : syracuseStep 5511361 = 4133521) B4133521
theorem B7348481 : Blo 2175435 7348481 := bstep (se 2 (by rfl) ⟨2755680, by rfl⟩ : syracuseStep 7348481 = 5511361) B5511361
theorem B4898987 : Blo 2175435 4898987 := bstep (se 1 (by rfl) ⟨3674240, by rfl⟩ : syracuseStep 4898987 = 7348481) B7348481
theorem B3265991 : Blo 2175435 3265991 := bstep (se 1 (by rfl) ⟨2449493, by rfl⟩ : syracuseStep 3265991 = 4898987) B4898987
theorem B2177327 : Blo 2175435 2177327 := bstep (se 1 (by rfl) ⟨1632995, by rfl⟩ : syracuseStep 2177327 = 3265991) B3265991
theorem B3265997 : Blo 2175435 3265997 := bbase (se 3 (by rfl) ⟨612374, by rfl⟩ : syracuseStep 3265997 = 1224749) (by norm_num)
theorem B2177331 : Blo 2175435 2177331 := bstep (se 1 (by rfl) ⟨1632998, by rfl⟩ : syracuseStep 2177331 = 3265997) B3265997
theorem B4899005 : Blo 2175435 4899005 := bbase (se 3 (by rfl) ⟨918563, by rfl⟩ : syracuseStep 4899005 = 1837127) (by norm_num)
theorem B3266003 : Blo 2175435 3266003 := bstep (se 1 (by rfl) ⟨2449502, by rfl⟩ : syracuseStep 3266003 = 4899005) B4899005
theorem B2177335 : Blo 2175435 2177335 := bstep (se 1 (by rfl) ⟨1633001, by rfl⟩ : syracuseStep 2177335 = 3266003) B3266003
theorem B3674261 : Blo 2175435 3674261 := bbase (se 6 (by rfl) ⟨86115, by rfl⟩ : syracuseStep 3674261 = 172231) (by norm_num)
theorem B2449507 : Blo 2175435 2449507 := bstep (se 1 (by rfl) ⟨1837130, by rfl⟩ : syracuseStep 2449507 = 3674261) B3674261
theorem B3266009 : Blo 2175435 3266009 := bstep (se 2 (by rfl) ⟨1224753, by rfl⟩ : syracuseStep 3266009 = 2449507) B2449507
theorem B2177339 : Blo 2175435 2177339 := bstep (se 1 (by rfl) ⟨1633004, by rfl⟩ : syracuseStep 2177339 = 3266009) B3266009
theorem B3923645 : Blo 2175435 3923645 := bbase (se 3 (by rfl) ⟨735683, by rfl⟩ : syracuseStep 3923645 = 1471367) (by norm_num)
theorem B10463053 : Blo 2175435 10463053 := bstep (se 3 (by rfl) ⟨1961822, by rfl⟩ : syracuseStep 10463053 = 3923645) B3923645
theorem B13950737 : Blo 2175435 13950737 := bstep (se 2 (by rfl) ⟨5231526, by rfl⟩ : syracuseStep 13950737 = 10463053) B10463053
theorem B9300491 : Blo 2175435 9300491 := bstep (se 1 (by rfl) ⟨6975368, by rfl⟩ : syracuseStep 9300491 = 13950737) B13950737
theorem B6200327 : Blo 2175435 6200327 := bstep (se 1 (by rfl) ⟨4650245, by rfl⟩ : syracuseStep 6200327 = 9300491) B9300491
theorem B16534205 : Blo 2175435 16534205 := bstep (se 3 (by rfl) ⟨3100163, by rfl⟩ : syracuseStep 16534205 = 6200327) B6200327
theorem B11022803 : Blo 2175435 11022803 := bstep (se 1 (by rfl) ⟨8267102, by rfl⟩ : syracuseStep 11022803 = 16534205) B16534205
theorem B7348535 : Blo 2175435 7348535 := bstep (se 1 (by rfl) ⟨5511401, by rfl⟩ : syracuseStep 7348535 = 11022803) B11022803
theorem B4899023 : Blo 2175435 4899023 := bstep (se 1 (by rfl) ⟨3674267, by rfl⟩ : syracuseStep 4899023 = 7348535) B7348535
theorem B3266015 : Blo 2175435 3266015 := bstep (se 1 (by rfl) ⟨2449511, by rfl⟩ : syracuseStep 3266015 = 4899023) B4899023
theorem B2177343 : Blo 2175435 2177343 := bstep (se 1 (by rfl) ⟨1633007, by rfl⟩ : syracuseStep 2177343 = 3266015) B3266015
theorem B3266021 : Blo 2175435 3266021 := bbase (se 4 (by rfl) ⟨306189, by rfl⟩ : syracuseStep 3266021 = 612379) (by norm_num)
theorem B2177347 : Blo 2175435 2177347 := bstep (se 1 (by rfl) ⟨1633010, by rfl⟩ : syracuseStep 2177347 = 3266021) B3266021
theorem B39727061 : Blo 2175435 39727061 := bbase (se 7 (by rfl) ⟨465551, by rfl⟩ : syracuseStep 39727061 = 931103) (by norm_num)
theorem B26484707 : Blo 2175435 26484707 := bstep (se 1 (by rfl) ⟨19863530, by rfl⟩ : syracuseStep 26484707 = 39727061) B39727061
theorem B17656471 : Blo 2175435 17656471 := bstep (se 1 (by rfl) ⟨13242353, by rfl⟩ : syracuseStep 17656471 = 26484707) B26484707
theorem B23541961 : Blo 2175435 23541961 := bstep (se 2 (by rfl) ⟨8828235, by rfl⟩ : syracuseStep 23541961 = 17656471) B17656471
theorem B31389281 : Blo 2175435 31389281 := bstep (se 2 (by rfl) ⟨11770980, by rfl⟩ : syracuseStep 31389281 = 23541961) B23541961
theorem B20926187 : Blo 2175435 20926187 := bstep (se 1 (by rfl) ⟨15694640, by rfl⟩ : syracuseStep 20926187 = 31389281) B31389281
theorem B13950791 : Blo 2175435 13950791 := bstep (se 1 (by rfl) ⟨10463093, by rfl⟩ : syracuseStep 13950791 = 20926187) B20926187
theorem B9300527 : Blo 2175435 9300527 := bstep (se 1 (by rfl) ⟨6975395, by rfl⟩ : syracuseStep 9300527 = 13950791) B13950791
theorem B6200351 : Blo 2175435 6200351 := bstep (se 1 (by rfl) ⟨4650263, by rfl⟩ : syracuseStep 6200351 = 9300527) B9300527
theorem B4133567 : Blo 2175435 4133567 := bstep (se 1 (by rfl) ⟨3100175, by rfl⟩ : syracuseStep 4133567 = 6200351) B6200351
theorem B2755711 : Blo 2175435 2755711 := bstep (se 1 (by rfl) ⟨2066783, by rfl⟩ : syracuseStep 2755711 = 4133567) B4133567
theorem B3674281 : Blo 2175435 3674281 := bstep (se 2 (by rfl) ⟨1377855, by rfl⟩ : syracuseStep 3674281 = 2755711) B2755711
theorem B4899041 : Blo 2175435 4899041 := bstep (se 2 (by rfl) ⟨1837140, by rfl⟩ : syracuseStep 4899041 = 3674281) B3674281
theorem B3266027 : Blo 2175435 3266027 := bstep (se 1 (by rfl) ⟨2449520, by rfl⟩ : syracuseStep 3266027 = 4899041) B4899041
theorem B2177351 : Blo 2175435 2177351 := bstep (se 1 (by rfl) ⟨1633013, by rfl⟩ : syracuseStep 2177351 = 3266027) B3266027
theorem B2449525 : Blo 2175435 2449525 := bbase (se 5 (by rfl) ⟨114821, by rfl⟩ : syracuseStep 2449525 = 229643) (by norm_num)
theorem B3266033 : Blo 2175435 3266033 := bstep (se 2 (by rfl) ⟨1224762, by rfl⟩ : syracuseStep 3266033 = 2449525) B2449525
theorem B2177355 : Blo 2175435 2177355 := bstep (se 1 (by rfl) ⟨1633016, by rfl⟩ : syracuseStep 2177355 = 3266033) B3266033
theorem B2755721 : Blo 2175435 2755721 := bbase (se 2 (by rfl) ⟨1033395, by rfl⟩ : syracuseStep 2755721 = 2066791) (by norm_num)
theorem B7348589 : Blo 2175435 7348589 := bstep (se 3 (by rfl) ⟨1377860, by rfl⟩ : syracuseStep 7348589 = 2755721) B2755721
theorem B4899059 : Blo 2175435 4899059 := bstep (se 1 (by rfl) ⟨3674294, by rfl⟩ : syracuseStep 4899059 = 7348589) B7348589
theorem B3266039 : Blo 2175435 3266039 := bstep (se 1 (by rfl) ⟨2449529, by rfl⟩ : syracuseStep 3266039 = 4899059) B4899059
theorem B2177359 : Blo 2175435 2177359 := bstep (se 1 (by rfl) ⟨1633019, by rfl⟩ : syracuseStep 2177359 = 3266039) B3266039
theorem B3266045 : Blo 2175435 3266045 := bbase (se 3 (by rfl) ⟨612383, by rfl⟩ : syracuseStep 3266045 = 1224767) (by norm_num)
theorem B2177363 : Blo 2175435 2177363 := bstep (se 1 (by rfl) ⟨1633022, by rfl⟩ : syracuseStep 2177363 = 3266045) B3266045
theorem B4899077 : Blo 2175435 4899077 := bbase (se 4 (by rfl) ⟨459288, by rfl⟩ : syracuseStep 4899077 = 918577) (by norm_num)
theorem B3266051 : Blo 2175435 3266051 := bstep (se 1 (by rfl) ⟨2449538, by rfl⟩ : syracuseStep 3266051 = 4899077) B4899077
theorem B2177367 : Blo 2175435 2177367 := bstep (se 1 (by rfl) ⟨1633025, by rfl⟩ : syracuseStep 2177367 = 3266051) B3266051
theorem B4133605 : Blo 2175435 4133605 := bbase (se 4 (by rfl) ⟨387525, by rfl⟩ : syracuseStep 4133605 = 775051) (by norm_num)
theorem B5511473 : Blo 2175435 5511473 := bstep (se 2 (by rfl) ⟨2066802, by rfl⟩ : syracuseStep 5511473 = 4133605) B4133605
theorem B3674315 : Blo 2175435 3674315 := bstep (se 1 (by rfl) ⟨2755736, by rfl⟩ : syracuseStep 3674315 = 5511473) B5511473
theorem B2449543 : Blo 2175435 2449543 := bstep (se 1 (by rfl) ⟨1837157, by rfl⟩ : syracuseStep 2449543 = 3674315) B3674315
theorem B3266057 : Blo 2175435 3266057 := bstep (se 2 (by rfl) ⟨1224771, by rfl⟩ : syracuseStep 3266057 = 2449543) B2449543
theorem B2177371 : Blo 2175435 2177371 := bstep (se 1 (by rfl) ⟨1633028, by rfl⟩ : syracuseStep 2177371 = 3266057) B3266057
theorem B11022965 : Blo 2175435 11022965 := bbase (se 5 (by rfl) ⟨516701, by rfl⟩ : syracuseStep 11022965 = 1033403) (by norm_num)
theorem B7348643 : Blo 2175435 7348643 := bstep (se 1 (by rfl) ⟨5511482, by rfl⟩ : syracuseStep 7348643 = 11022965) B11022965
theorem B4899095 : Blo 2175435 4899095 := bstep (se 1 (by rfl) ⟨3674321, by rfl⟩ : syracuseStep 4899095 = 7348643) B7348643
theorem B3266063 : Blo 2175435 3266063 := bstep (se 1 (by rfl) ⟨2449547, by rfl⟩ : syracuseStep 3266063 = 4899095) B4899095
theorem B2177375 : Blo 2175435 2177375 := bstep (se 1 (by rfl) ⟨1633031, by rfl⟩ : syracuseStep 2177375 = 3266063) B3266063
theorem B3266069 : Blo 2175435 3266069 := bbase (se 6 (by rfl) ⟨76548, by rfl⟩ : syracuseStep 3266069 = 153097) (by norm_num)
theorem B2177379 : Blo 2175435 2177379 := bstep (se 1 (by rfl) ⟨1633034, by rfl⟩ : syracuseStep 2177379 = 3266069) B3266069
theorem B3310637 : Blo 2175435 3310637 := bbase (se 3 (by rfl) ⟨620744, by rfl⟩ : syracuseStep 3310637 = 1241489) (by norm_num)
theorem B8828365 : Blo 2175435 8828365 := bstep (se 3 (by rfl) ⟨1655318, by rfl⟩ : syracuseStep 8828365 = 3310637) B3310637
theorem B11771153 : Blo 2175435 11771153 := bstep (se 2 (by rfl) ⟨4414182, by rfl⟩ : syracuseStep 11771153 = 8828365) B8828365
theorem B7847435 : Blo 2175435 7847435 := bstep (se 1 (by rfl) ⟨5885576, by rfl⟩ : syracuseStep 7847435 = 11771153) B11771153
theorem B5231623 : Blo 2175435 5231623 := bstep (se 1 (by rfl) ⟨3923717, by rfl⟩ : syracuseStep 5231623 = 7847435) B7847435
theorem B6975497 : Blo 2175435 6975497 := bstep (se 2 (by rfl) ⟨2615811, by rfl⟩ : syracuseStep 6975497 = 5231623) B5231623
theorem B18601325 : Blo 2175435 18601325 := bstep (se 3 (by rfl) ⟨3487748, by rfl⟩ : syracuseStep 18601325 = 6975497) B6975497
theorem B12400883 : Blo 2175435 12400883 := bstep (se 1 (by rfl) ⟨9300662, by rfl⟩ : syracuseStep 12400883 = 18601325) B18601325
theorem B8267255 : Blo 2175435 8267255 := bstep (se 1 (by rfl) ⟨6200441, by rfl⟩ : syracuseStep 8267255 = 12400883) B12400883
theorem B5511503 : Blo 2175435 5511503 := bstep (se 1 (by rfl) ⟨4133627, by rfl⟩ : syracuseStep 5511503 = 8267255) B8267255
theorem B3674335 : Blo 2175435 3674335 := bstep (se 1 (by rfl) ⟨2755751, by rfl⟩ : syracuseStep 3674335 = 5511503) B5511503
theorem B4899113 : Blo 2175435 4899113 := bstep (se 2 (by rfl) ⟨1837167, by rfl⟩ : syracuseStep 4899113 = 3674335) B3674335
theorem B3266075 : Blo 2175435 3266075 := bstep (se 1 (by rfl) ⟨2449556, by rfl⟩ : syracuseStep 3266075 = 4899113) B4899113
theorem B2177383 : Blo 2175435 2177383 := bstep (se 1 (by rfl) ⟨1633037, by rfl⟩ : syracuseStep 2177383 = 3266075) B3266075
theorem B2449561 : Blo 2175435 2449561 := bbase (se 2 (by rfl) ⟨918585, by rfl⟩ : syracuseStep 2449561 = 1837171) (by norm_num)
theorem B3266081 : Blo 2175435 3266081 := bstep (se 2 (by rfl) ⟨1224780, by rfl⟩ : syracuseStep 3266081 = 2449561) B2449561
theorem B2177387 : Blo 2175435 2177387 := bstep (se 1 (by rfl) ⟨1633040, by rfl⟩ : syracuseStep 2177387 = 3266081) B3266081
theorem B8267285 : Blo 2175435 8267285 := bbase (se 6 (by rfl) ⟨193764, by rfl⟩ : syracuseStep 8267285 = 387529) (by norm_num)
theorem B5511523 : Blo 2175435 5511523 := bstep (se 1 (by rfl) ⟨4133642, by rfl⟩ : syracuseStep 5511523 = 8267285) B8267285
theorem B7348697 : Blo 2175435 7348697 := bstep (se 2 (by rfl) ⟨2755761, by rfl⟩ : syracuseStep 7348697 = 5511523) B5511523
theorem B4899131 : Blo 2175435 4899131 := bstep (se 1 (by rfl) ⟨3674348, by rfl⟩ : syracuseStep 4899131 = 7348697) B7348697
theorem B3266087 : Blo 2175435 3266087 := bstep (se 1 (by rfl) ⟨2449565, by rfl⟩ : syracuseStep 3266087 = 4899131) B4899131
theorem B2177391 : Blo 2175435 2177391 := bstep (se 1 (by rfl) ⟨1633043, by rfl⟩ : syracuseStep 2177391 = 3266087) B3266087
theorem B3266093 : Blo 2175435 3266093 := bbase (se 3 (by rfl) ⟨612392, by rfl⟩ : syracuseStep 3266093 = 1224785) (by norm_num)
theorem B2177395 : Blo 2175435 2177395 := bstep (se 1 (by rfl) ⟨1633046, by rfl⟩ : syracuseStep 2177395 = 3266093) B3266093
theorem B4899149 : Blo 2175435 4899149 := bbase (se 3 (by rfl) ⟨918590, by rfl⟩ : syracuseStep 4899149 = 1837181) (by norm_num)
theorem B3266099 : Blo 2175435 3266099 := bstep (se 1 (by rfl) ⟨2449574, by rfl⟩ : syracuseStep 3266099 = 4899149) B4899149
theorem B2177399 : Blo 2175435 2177399 := bstep (se 1 (by rfl) ⟨1633049, by rfl⟩ : syracuseStep 2177399 = 3266099) B3266099
theorem B2755777 : Blo 2175435 2755777 := bbase (se 2 (by rfl) ⟨1033416, by rfl⟩ : syracuseStep 2755777 = 2066833) (by norm_num)
theorem B3674369 : Blo 2175435 3674369 := bstep (se 2 (by rfl) ⟨1377888, by rfl⟩ : syracuseStep 3674369 = 2755777) B2755777
theorem B2449579 : Blo 2175435 2449579 := bstep (se 1 (by rfl) ⟨1837184, by rfl⟩ : syracuseStep 2449579 = 3674369) B3674369
theorem B3266105 : Blo 2175435 3266105 := bstep (se 2 (by rfl) ⟨1224789, by rfl⟩ : syracuseStep 3266105 = 2449579) B2449579
theorem B2177403 : Blo 2175435 2177403 := bstep (se 1 (by rfl) ⟨1633052, by rfl⟩ : syracuseStep 2177403 = 3266105) B3266105
theorem B2942821 : Blo 2175435 2942821 := bbase (se 4 (by rfl) ⟨275889, by rfl⟩ : syracuseStep 2942821 = 551779) (by norm_num)
theorem B3923761 : Blo 2175435 3923761 := bstep (se 2 (by rfl) ⟨1471410, by rfl⟩ : syracuseStep 3923761 = 2942821) B2942821
theorem B5231681 : Blo 2175435 5231681 := bstep (se 2 (by rfl) ⟨1961880, by rfl⟩ : syracuseStep 5231681 = 3923761) B3923761
theorem B3487787 : Blo 2175435 3487787 := bstep (se 1 (by rfl) ⟨2615840, by rfl⟩ : syracuseStep 3487787 = 5231681) B5231681
theorem B2325191 : Blo 2175435 2325191 := bstep (se 1 (by rfl) ⟨1743893, by rfl⟩ : syracuseStep 2325191 = 3487787) B3487787
theorem B24802037 : Blo 2175435 24802037 := bstep (se 5 (by rfl) ⟨1162595, by rfl⟩ : syracuseStep 24802037 = 2325191) B2325191
theorem B16534691 : Blo 2175435 16534691 := bstep (se 1 (by rfl) ⟨12401018, by rfl⟩ : syracuseStep 16534691 = 24802037) B24802037
theorem B11023127 : Blo 2175435 11023127 := bstep (se 1 (by rfl) ⟨8267345, by rfl⟩ : syracuseStep 11023127 = 16534691) B16534691
theorem B7348751 : Blo 2175435 7348751 := bstep (se 1 (by rfl) ⟨5511563, by rfl⟩ : syracuseStep 7348751 = 11023127) B11023127
theorem B4899167 : Blo 2175435 4899167 := bstep (se 1 (by rfl) ⟨3674375, by rfl⟩ : syracuseStep 4899167 = 7348751) B7348751
theorem B3266111 : Blo 2175435 3266111 := bstep (se 1 (by rfl) ⟨2449583, by rfl⟩ : syracuseStep 3266111 = 4899167) B4899167
theorem B2177407 : Blo 2175435 2177407 := bstep (se 1 (by rfl) ⟨1633055, by rfl⟩ : syracuseStep 2177407 = 3266111) B3266111
theorem B3266117 : Blo 2175435 3266117 := bbase (se 4 (by rfl) ⟨306198, by rfl⟩ : syracuseStep 3266117 = 612397) (by norm_num)
theorem B2177411 : Blo 2175435 2177411 := bstep (se 1 (by rfl) ⟨1633058, by rfl⟩ : syracuseStep 2177411 = 3266117) B3266117
theorem B3674389 : Blo 2175435 3674389 := bbase (se 6 (by rfl) ⟨86118, by rfl⟩ : syracuseStep 3674389 = 172237) (by norm_num)
theorem B4899185 : Blo 2175435 4899185 := bstep (se 2 (by rfl) ⟨1837194, by rfl⟩ : syracuseStep 4899185 = 3674389) B3674389
theorem B3266123 : Blo 2175435 3266123 := bstep (se 1 (by rfl) ⟨2449592, by rfl⟩ : syracuseStep 3266123 = 4899185) B4899185
theorem B2177415 : Blo 2175435 2177415 := bstep (se 1 (by rfl) ⟨1633061, by rfl⟩ : syracuseStep 2177415 = 3266123) B3266123
theorem B2449597 : Blo 2175435 2449597 := bbase (se 3 (by rfl) ⟨459299, by rfl⟩ : syracuseStep 2449597 = 918599) (by norm_num)
theorem B3266129 : Blo 2175435 3266129 := bstep (se 2 (by rfl) ⟨1224798, by rfl⟩ : syracuseStep 3266129 = 2449597) B2449597
theorem B2177419 : Blo 2175435 2177419 := bstep (se 1 (by rfl) ⟨1633064, by rfl⟩ : syracuseStep 2177419 = 3266129) B3266129
theorem B7348805 : Blo 2175435 7348805 := bbase (se 4 (by rfl) ⟨688950, by rfl⟩ : syracuseStep 7348805 = 1377901) (by norm_num)
theorem B4899203 : Blo 2175435 4899203 := bstep (se 1 (by rfl) ⟨3674402, by rfl⟩ : syracuseStep 4899203 = 7348805) B7348805
theorem B3266135 : Blo 2175435 3266135 := bstep (se 1 (by rfl) ⟨2449601, by rfl⟩ : syracuseStep 3266135 = 4899203) B4899203
theorem B2177423 : Blo 2175435 2177423 := bstep (se 1 (by rfl) ⟨1633067, by rfl⟩ : syracuseStep 2177423 = 3266135) B3266135
theorem B3266141 : Blo 2175435 3266141 := bbase (se 3 (by rfl) ⟨612401, by rfl⟩ : syracuseStep 3266141 = 1224803) (by norm_num)
theorem B2177427 : Blo 2175435 2177427 := bstep (se 1 (by rfl) ⟨1633070, by rfl⟩ : syracuseStep 2177427 = 3266141) B3266141
theorem B4899221 : Blo 2175435 4899221 := bbase (se 6 (by rfl) ⟨114825, by rfl⟩ : syracuseStep 4899221 = 229651) (by norm_num)
theorem B3266147 : Blo 2175435 3266147 := bstep (se 1 (by rfl) ⟨2449610, by rfl⟩ : syracuseStep 3266147 = 4899221) B4899221
theorem B2177431 : Blo 2175435 2177431 := bstep (se 1 (by rfl) ⟨1633073, by rfl⟩ : syracuseStep 2177431 = 3266147) B3266147
theorem B5231749 : Blo 2175435 5231749 := bbase (se 4 (by rfl) ⟨490476, by rfl⟩ : syracuseStep 5231749 = 980953) (by norm_num)
theorem B6975665 : Blo 2175435 6975665 := bstep (se 2 (by rfl) ⟨2615874, by rfl⟩ : syracuseStep 6975665 = 5231749) B5231749
theorem B4650443 : Blo 2175435 4650443 := bstep (se 1 (by rfl) ⟨3487832, by rfl⟩ : syracuseStep 4650443 = 6975665) B6975665
theorem B3100295 : Blo 2175435 3100295 := bstep (se 1 (by rfl) ⟨2325221, by rfl⟩ : syracuseStep 3100295 = 4650443) B4650443
theorem B8267453 : Blo 2175435 8267453 := bstep (se 3 (by rfl) ⟨1550147, by rfl⟩ : syracuseStep 8267453 = 3100295) B3100295
theorem B5511635 : Blo 2175435 5511635 := bstep (se 1 (by rfl) ⟨4133726, by rfl⟩ : syracuseStep 5511635 = 8267453) B8267453
theorem B3674423 : Blo 2175435 3674423 := bstep (se 1 (by rfl) ⟨2755817, by rfl⟩ : syracuseStep 3674423 = 5511635) B5511635
theorem B2449615 : Blo 2175435 2449615 := bstep (se 1 (by rfl) ⟨1837211, by rfl⟩ : syracuseStep 2449615 = 3674423) B3674423
theorem B3266153 : Blo 2175435 3266153 := bstep (se 2 (by rfl) ⟨1224807, by rfl⟩ : syracuseStep 3266153 = 2449615) B2449615
theorem B2177435 : Blo 2175435 2177435 := bstep (se 1 (by rfl) ⟨1633076, by rfl⟩ : syracuseStep 2177435 = 3266153) B3266153
theorem C0 (j : ℕ) (h1 : 543858 ≤ j) (h2 : j ≤ 544358) : Blo 2175435 (4 * j + 3) := by
  interval_cases j
  · exact B2175435
  · exact B2175439
  · exact B2175443
  · exact B2175447
  · exact B2175451
  · exact B2175455
  · exact B2175459
  · exact B2175463
  · exact B2175467
  · exact B2175471
  · exact B2175475
  · exact B2175479
  · exact B2175483
  · exact B2175487
  · exact B2175491
  · exact B2175495
  · exact B2175499
  · exact B2175503
  · exact B2175507
  · exact B2175511
  · exact B2175515
  · exact B2175519
  · exact B2175523
  · exact B2175527
  · exact B2175531
  · exact B2175535
  · exact B2175539
  · exact B2175543
  · exact B2175547
  · exact B2175551
  · exact B2175555
  · exact B2175559
  · exact B2175563
  · exact B2175567
  · exact B2175571
  · exact B2175575
  · exact B2175579
  · exact B2175583
  · exact B2175587
  · exact B2175591
  · exact B2175595
  · exact B2175599
  · exact B2175603
  · exact B2175607
  · exact B2175611
  · exact B2175615
  · exact B2175619
  · exact B2175623
  · exact B2175627
  · exact B2175631
  · exact B2175635
  · exact B2175639
  · exact B2175643
  · exact B2175647
  · exact B2175651
  · exact B2175655
  · exact B2175659
  · exact B2175663
  · exact B2175667
  · exact B2175671
  · exact B2175675
  · exact B2175679
  · exact B2175683
  · exact B2175687
  · exact B2175691
  · exact B2175695
  · exact B2175699
  · exact B2175703
  · exact B2175707
  · exact B2175711
  · exact B2175715
  · exact B2175719
  · exact B2175723
  · exact B2175727
  · exact B2175731
  · exact B2175735
  · exact B2175739
  · exact B2175743
  · exact B2175747
  · exact B2175751
  · exact B2175755
  · exact B2175759
  · exact B2175763
  · exact B2175767
  · exact B2175771
  · exact B2175775
  · exact B2175779
  · exact B2175783
  · exact B2175787
  · exact B2175791
  · exact B2175795
  · exact B2175799
  · exact B2175803
  · exact B2175807
  · exact B2175811
  · exact B2175815
  · exact B2175819
  · exact B2175823
  · exact B2175827
  · exact B2175831
  · exact B2175835
  · exact B2175839
  · exact B2175843
  · exact B2175847
  · exact B2175851
  · exact B2175855
  · exact B2175859
  · exact B2175863
  · exact B2175867
  · exact B2175871
  · exact B2175875
  · exact B2175879
  · exact B2175883
  · exact B2175887
  · exact B2175891
  · exact B2175895
  · exact B2175899
  · exact B2175903
  · exact B2175907
  · exact B2175911
  · exact B2175915
  · exact B2175919
  · exact B2175923
  · exact B2175927
  · exact B2175931
  · exact B2175935
  · exact B2175939
  · exact B2175943
  · exact B2175947
  · exact B2175951
  · exact B2175955
  · exact B2175959
  · exact B2175963
  · exact B2175967
  · exact B2175971
  · exact B2175975
  · exact B2175979
  · exact B2175983
  · exact B2175987
  · exact B2175991
  · exact B2175995
  · exact B2175999
  · exact B2176003
  · exact B2176007
  · exact B2176011
  · exact B2176015
  · exact B2176019
  · exact B2176023
  · exact B2176027
  · exact B2176031
  · exact B2176035
  · exact B2176039
  · exact B2176043
  · exact B2176047
  · exact B2176051
  · exact B2176055
  · exact B2176059
  · exact B2176063
  · exact B2176067
  · exact B2176071
  · exact B2176075
  · exact B2176079
  · exact B2176083
  · exact B2176087
  · exact B2176091
  · exact B2176095
  · exact B2176099
  · exact B2176103
  · exact B2176107
  · exact B2176111
  · exact B2176115
  · exact B2176119
  · exact B2176123
  · exact B2176127
  · exact B2176131
  · exact B2176135
  · exact B2176139
  · exact B2176143
  · exact B2176147
  · exact B2176151
  · exact B2176155
  · exact B2176159
  · exact B2176163
  · exact B2176167
  · exact B2176171
  · exact B2176175
  · exact B2176179
  · exact B2176183
  · exact B2176187
  · exact B2176191
  · exact B2176195
  · exact B2176199
  · exact B2176203
  · exact B2176207
  · exact B2176211
  · exact B2176215
  · exact B2176219
  · exact B2176223
  · exact B2176227
  · exact B2176231
  · exact B2176235
  · exact B2176239
  · exact B2176243
  · exact B2176247
  · exact B2176251
  · exact B2176255
  · exact B2176259
  · exact B2176263
  · exact B2176267
  · exact B2176271
  · exact B2176275
  · exact B2176279
  · exact B2176283
  · exact B2176287
  · exact B2176291
  · exact B2176295
  · exact B2176299
  · exact B2176303
  · exact B2176307
  · exact B2176311
  · exact B2176315
  · exact B2176319
  · exact B2176323
  · exact B2176327
  · exact B2176331
  · exact B2176335
  · exact B2176339
  · exact B2176343
  · exact B2176347
  · exact B2176351
  · exact B2176355
  · exact B2176359
  · exact B2176363
  · exact B2176367
  · exact B2176371
  · exact B2176375
  · exact B2176379
  · exact B2176383
  · exact B2176387
  · exact B2176391
  · exact B2176395
  · exact B2176399
  · exact B2176403
  · exact B2176407
  · exact B2176411
  · exact B2176415
  · exact B2176419
  · exact B2176423
  · exact B2176427
  · exact B2176431
  · exact B2176435
  · exact B2176439
  · exact B2176443
  · exact B2176447
  · exact B2176451
  · exact B2176455
  · exact B2176459
  · exact B2176463
  · exact B2176467
  · exact B2176471
  · exact B2176475
  · exact B2176479
  · exact B2176483
  · exact B2176487
  · exact B2176491
  · exact B2176495
  · exact B2176499
  · exact B2176503
  · exact B2176507
  · exact B2176511
  · exact B2176515
  · exact B2176519
  · exact B2176523
  · exact B2176527
  · exact B2176531
  · exact B2176535
  · exact B2176539
  · exact B2176543
  · exact B2176547
  · exact B2176551
  · exact B2176555
  · exact B2176559
  · exact B2176563
  · exact B2176567
  · exact B2176571
  · exact B2176575
  · exact B2176579
  · exact B2176583
  · exact B2176587
  · exact B2176591
  · exact B2176595
  · exact B2176599
  · exact B2176603
  · exact B2176607
  · exact B2176611
  · exact B2176615
  · exact B2176619
  · exact B2176623
  · exact B2176627
  · exact B2176631
  · exact B2176635
  · exact B2176639
  · exact B2176643
  · exact B2176647
  · exact B2176651
  · exact B2176655
  · exact B2176659
  · exact B2176663
  · exact B2176667
  · exact B2176671
  · exact B2176675
  · exact B2176679
  · exact B2176683
  · exact B2176687
  · exact B2176691
  · exact B2176695
  · exact B2176699
  · exact B2176703
  · exact B2176707
  · exact B2176711
  · exact B2176715
  · exact B2176719
  · exact B2176723
  · exact B2176727
  · exact B2176731
  · exact B2176735
  · exact B2176739
  · exact B2176743
  · exact B2176747
  · exact B2176751
  · exact B2176755
  · exact B2176759
  · exact B2176763
  · exact B2176767
  · exact B2176771
  · exact B2176775
  · exact B2176779
  · exact B2176783
  · exact B2176787
  · exact B2176791
  · exact B2176795
  · exact B2176799
  · exact B2176803
  · exact B2176807
  · exact B2176811
  · exact B2176815
  · exact B2176819
  · exact B2176823
  · exact B2176827
  · exact B2176831
  · exact B2176835
  · exact B2176839
  · exact B2176843
  · exact B2176847
  · exact B2176851
  · exact B2176855
  · exact B2176859
  · exact B2176863
  · exact B2176867
  · exact B2176871
  · exact B2176875
  · exact B2176879
  · exact B2176883
  · exact B2176887
  · exact B2176891
  · exact B2176895
  · exact B2176899
  · exact B2176903
  · exact B2176907
  · exact B2176911
  · exact B2176915
  · exact B2176919
  · exact B2176923
  · exact B2176927
  · exact B2176931
  · exact B2176935
  · exact B2176939
  · exact B2176943
  · exact B2176947
  · exact B2176951
  · exact B2176955
  · exact B2176959
  · exact B2176963
  · exact B2176967
  · exact B2176971
  · exact B2176975
  · exact B2176979
  · exact B2176983
  · exact B2176987
  · exact B2176991
  · exact B2176995
  · exact B2176999
  · exact B2177003
  · exact B2177007
  · exact B2177011
  · exact B2177015
  · exact B2177019
  · exact B2177023
  · exact B2177027
  · exact B2177031
  · exact B2177035
  · exact B2177039
  · exact B2177043
  · exact B2177047
  · exact B2177051
  · exact B2177055
  · exact B2177059
  · exact B2177063
  · exact B2177067
  · exact B2177071
  · exact B2177075
  · exact B2177079
  · exact B2177083
  · exact B2177087
  · exact B2177091
  · exact B2177095
  · exact B2177099
  · exact B2177103
  · exact B2177107
  · exact B2177111
  · exact B2177115
  · exact B2177119
  · exact B2177123
  · exact B2177127
  · exact B2177131
  · exact B2177135
  · exact B2177139
  · exact B2177143
  · exact B2177147
  · exact B2177151
  · exact B2177155
  · exact B2177159
  · exact B2177163
  · exact B2177167
  · exact B2177171
  · exact B2177175
  · exact B2177179
  · exact B2177183
  · exact B2177187
  · exact B2177191
  · exact B2177195
  · exact B2177199
  · exact B2177203
  · exact B2177207
  · exact B2177211
  · exact B2177215
  · exact B2177219
  · exact B2177223
  · exact B2177227
  · exact B2177231
  · exact B2177235
  · exact B2177239
  · exact B2177243
  · exact B2177247
  · exact B2177251
  · exact B2177255
  · exact B2177259
  · exact B2177263
  · exact B2177267
  · exact B2177271
  · exact B2177275
  · exact B2177279
  · exact B2177283
  · exact B2177287
  · exact B2177291
  · exact B2177295
  · exact B2177299
  · exact B2177303
  · exact B2177307
  · exact B2177311
  · exact B2177315
  · exact B2177319
  · exact B2177323
  · exact B2177327
  · exact B2177331
  · exact B2177335
  · exact B2177339
  · exact B2177343
  · exact B2177347
  · exact B2177351
  · exact B2177355
  · exact B2177359
  · exact B2177363
  · exact B2177367
  · exact B2177371
  · exact B2177375
  · exact B2177379
  · exact B2177383
  · exact B2177387
  · exact B2177391
  · exact B2177395
  · exact B2177399
  · exact B2177403
  · exact B2177407
  · exact B2177411
  · exact B2177415
  · exact B2177419
  · exact B2177423
  · exact B2177427
  · exact B2177431
  · exact B2177435
theorem solution (m : ℕ) (hlo : 2175435 ≤ m) (hhi : m ≤ 2177435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 543858 ≤ j := by omega
    have hj2 : j ≤ 544358 := by omega
    have hb : Blo 2175435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
