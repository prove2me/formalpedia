-- Prove2me | solution 1 for syracuse_descends_range_2089435_2091435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:24.557962+00:00
-- url     : https://prove2.me/submissions/1b71e74d-b083-4c14-a70f-b878cccc513b

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

theorem B5288885 : Blo 2089435 5288885 := bbase (se 5 (by rfl) ⟨247916, by rfl⟩ : syracuseStep 5288885 = 495833) (by norm_num)
theorem B3525923 : Blo 2089435 3525923 := bstep (se 1 (by rfl) ⟨2644442, by rfl⟩ : syracuseStep 3525923 = 5288885) B5288885
theorem B2350615 : Blo 2089435 2350615 := bstep (se 1 (by rfl) ⟨1762961, by rfl⟩ : syracuseStep 2350615 = 3525923) B3525923
theorem B3134153 : Blo 2089435 3134153 := bstep (se 2 (by rfl) ⟨1175307, by rfl⟩ : syracuseStep 3134153 = 2350615) B2350615
theorem B2089435 : Blo 2089435 2089435 := bstep (se 1 (by rfl) ⟨1567076, by rfl⟩ : syracuseStep 2089435 = 3134153) B3134153
theorem B17409077 : Blo 2089435 17409077 := bbase (se 5 (by rfl) ⟨816050, by rfl⟩ : syracuseStep 17409077 = 1632101) (by norm_num)
theorem B11606051 : Blo 2089435 11606051 := bstep (se 1 (by rfl) ⟨8704538, by rfl⟩ : syracuseStep 11606051 = 17409077) B17409077
theorem B7737367 : Blo 2089435 7737367 := bstep (se 1 (by rfl) ⟨5803025, by rfl⟩ : syracuseStep 7737367 = 11606051) B11606051
theorem B10316489 : Blo 2089435 10316489 := bstep (se 2 (by rfl) ⟨3868683, by rfl⟩ : syracuseStep 10316489 = 7737367) B7737367
theorem B110042549 : Blo 2089435 110042549 := bstep (se 5 (by rfl) ⟨5158244, by rfl⟩ : syracuseStep 110042549 = 10316489) B10316489
theorem B73361699 : Blo 2089435 73361699 := bstep (se 1 (by rfl) ⟨55021274, by rfl⟩ : syracuseStep 73361699 = 110042549) B110042549
theorem B48907799 : Blo 2089435 48907799 := bstep (se 1 (by rfl) ⟨36680849, by rfl⟩ : syracuseStep 48907799 = 73361699) B73361699
theorem B32605199 : Blo 2089435 32605199 := bstep (se 1 (by rfl) ⟨24453899, by rfl⟩ : syracuseStep 32605199 = 48907799) B48907799
theorem B21736799 : Blo 2089435 21736799 := bstep (se 1 (by rfl) ⟨16302599, by rfl⟩ : syracuseStep 21736799 = 32605199) B32605199
theorem B14491199 : Blo 2089435 14491199 := bstep (se 1 (by rfl) ⟨10868399, by rfl⟩ : syracuseStep 14491199 = 21736799) B21736799
theorem B9660799 : Blo 2089435 9660799 := bstep (se 1 (by rfl) ⟨7245599, by rfl⟩ : syracuseStep 9660799 = 14491199) B14491199
theorem B12881065 : Blo 2089435 12881065 := bstep (se 2 (by rfl) ⟨4830399, by rfl⟩ : syracuseStep 12881065 = 9660799) B9660799
theorem B17174753 : Blo 2089435 17174753 := bstep (se 2 (by rfl) ⟨6440532, by rfl⟩ : syracuseStep 17174753 = 12881065) B12881065
theorem B11449835 : Blo 2089435 11449835 := bstep (se 1 (by rfl) ⟨8587376, by rfl⟩ : syracuseStep 11449835 = 17174753) B17174753
theorem B7633223 : Blo 2089435 7633223 := bstep (se 1 (by rfl) ⟨5724917, by rfl⟩ : syracuseStep 7633223 = 11449835) B11449835
theorem B5088815 : Blo 2089435 5088815 := bstep (se 1 (by rfl) ⟨3816611, by rfl⟩ : syracuseStep 5088815 = 7633223) B7633223
theorem B3392543 : Blo 2089435 3392543 := bstep (se 1 (by rfl) ⟨2544407, by rfl⟩ : syracuseStep 3392543 = 5088815) B5088815
theorem B9046781 : Blo 2089435 9046781 := bstep (se 3 (by rfl) ⟨1696271, by rfl⟩ : syracuseStep 9046781 = 3392543) B3392543
theorem B6031187 : Blo 2089435 6031187 := bstep (se 1 (by rfl) ⟨4523390, by rfl⟩ : syracuseStep 6031187 = 9046781) B9046781
theorem B4020791 : Blo 2089435 4020791 := bstep (se 1 (by rfl) ⟨3015593, by rfl⟩ : syracuseStep 4020791 = 6031187) B6031187
theorem B42888437 : Blo 2089435 42888437 := bstep (se 5 (by rfl) ⟨2010395, by rfl⟩ : syracuseStep 42888437 = 4020791) B4020791
theorem B28592291 : Blo 2089435 28592291 := bstep (se 1 (by rfl) ⟨21444218, by rfl⟩ : syracuseStep 28592291 = 42888437) B42888437
theorem B19061527 : Blo 2089435 19061527 := bstep (se 1 (by rfl) ⟨14296145, by rfl⟩ : syracuseStep 19061527 = 28592291) B28592291
theorem B25415369 : Blo 2089435 25415369 := bstep (se 2 (by rfl) ⟨9530763, by rfl⟩ : syracuseStep 25415369 = 19061527) B19061527
theorem B16943579 : Blo 2089435 16943579 := bstep (se 1 (by rfl) ⟨12707684, by rfl⟩ : syracuseStep 16943579 = 25415369) B25415369
theorem B11295719 : Blo 2089435 11295719 := bstep (se 1 (by rfl) ⟨8471789, by rfl⟩ : syracuseStep 11295719 = 16943579) B16943579
theorem B7530479 : Blo 2089435 7530479 := bstep (se 1 (by rfl) ⟨5647859, by rfl⟩ : syracuseStep 7530479 = 11295719) B11295719
theorem B5020319 : Blo 2089435 5020319 := bstep (se 1 (by rfl) ⟨3765239, by rfl⟩ : syracuseStep 5020319 = 7530479) B7530479
theorem B13387517 : Blo 2089435 13387517 := bstep (se 3 (by rfl) ⟨2510159, by rfl⟩ : syracuseStep 13387517 = 5020319) B5020319
theorem B8925011 : Blo 2089435 8925011 := bstep (se 1 (by rfl) ⟨6693758, by rfl⟩ : syracuseStep 8925011 = 13387517) B13387517
theorem B5950007 : Blo 2089435 5950007 := bstep (se 1 (by rfl) ⟨4462505, by rfl⟩ : syracuseStep 5950007 = 8925011) B8925011
theorem B3966671 : Blo 2089435 3966671 := bstep (se 1 (by rfl) ⟨2975003, by rfl⟩ : syracuseStep 3966671 = 5950007) B5950007
theorem B10577789 : Blo 2089435 10577789 := bstep (se 3 (by rfl) ⟨1983335, by rfl⟩ : syracuseStep 10577789 = 3966671) B3966671
theorem B7051859 : Blo 2089435 7051859 := bstep (se 1 (by rfl) ⟨5288894, by rfl⟩ : syracuseStep 7051859 = 10577789) B10577789
theorem B4701239 : Blo 2089435 4701239 := bstep (se 1 (by rfl) ⟨3525929, by rfl⟩ : syracuseStep 4701239 = 7051859) B7051859
theorem B3134159 : Blo 2089435 3134159 := bstep (se 1 (by rfl) ⟨2350619, by rfl⟩ : syracuseStep 3134159 = 4701239) B4701239
theorem B2089439 : Blo 2089435 2089439 := bstep (se 1 (by rfl) ⟨1567079, by rfl⟩ : syracuseStep 2089439 = 3134159) B3134159
theorem B3134165 : Blo 2089435 3134165 := bbase (se 7 (by rfl) ⟨36728, by rfl⟩ : syracuseStep 3134165 = 73457) (by norm_num)
theorem B2089443 : Blo 2089435 2089443 := bstep (se 1 (by rfl) ⟨1567082, by rfl⟩ : syracuseStep 2089443 = 3134165) B3134165
theorem B2823941 : Blo 2089435 2823941 := bbase (se 4 (by rfl) ⟨264744, by rfl⟩ : syracuseStep 2823941 = 529489) (by norm_num)
theorem B7530509 : Blo 2089435 7530509 := bstep (se 3 (by rfl) ⟨1411970, by rfl⟩ : syracuseStep 7530509 = 2823941) B2823941
theorem B5020339 : Blo 2089435 5020339 := bstep (se 1 (by rfl) ⟨3765254, by rfl⟩ : syracuseStep 5020339 = 7530509) B7530509
theorem B6693785 : Blo 2089435 6693785 := bstep (se 2 (by rfl) ⟨2510169, by rfl⟩ : syracuseStep 6693785 = 5020339) B5020339
theorem B4462523 : Blo 2089435 4462523 := bstep (se 1 (by rfl) ⟨3346892, by rfl⟩ : syracuseStep 4462523 = 6693785) B6693785
theorem B2975015 : Blo 2089435 2975015 := bstep (se 1 (by rfl) ⟨2231261, by rfl⟩ : syracuseStep 2975015 = 4462523) B4462523
theorem B7933373 : Blo 2089435 7933373 := bstep (se 3 (by rfl) ⟨1487507, by rfl⟩ : syracuseStep 7933373 = 2975015) B2975015
theorem B5288915 : Blo 2089435 5288915 := bstep (se 1 (by rfl) ⟨3966686, by rfl⟩ : syracuseStep 5288915 = 7933373) B7933373
theorem B3525943 : Blo 2089435 3525943 := bstep (se 1 (by rfl) ⟨2644457, by rfl⟩ : syracuseStep 3525943 = 5288915) B5288915
theorem B4701257 : Blo 2089435 4701257 := bstep (se 2 (by rfl) ⟨1762971, by rfl⟩ : syracuseStep 4701257 = 3525943) B3525943
theorem B3134171 : Blo 2089435 3134171 := bstep (se 1 (by rfl) ⟨2350628, by rfl⟩ : syracuseStep 3134171 = 4701257) B4701257
theorem B2089447 : Blo 2089435 2089447 := bstep (se 1 (by rfl) ⟨1567085, by rfl⟩ : syracuseStep 2089447 = 3134171) B3134171
theorem B2350633 : Blo 2089435 2350633 := bbase (se 2 (by rfl) ⟨881487, by rfl⟩ : syracuseStep 2350633 = 1762975) (by norm_num)
theorem B3134177 : Blo 2089435 3134177 := bstep (se 2 (by rfl) ⟨1175316, by rfl⟩ : syracuseStep 3134177 = 2350633) B2350633
theorem B2089451 : Blo 2089435 2089451 := bstep (se 1 (by rfl) ⟨1567088, by rfl⟩ : syracuseStep 2089451 = 3134177) B3134177
theorem B20081429 : Blo 2089435 20081429 := bbase (se 6 (by rfl) ⟨470658, by rfl⟩ : syracuseStep 20081429 = 941317) (by norm_num)
theorem B13387619 : Blo 2089435 13387619 := bstep (se 1 (by rfl) ⟨10040714, by rfl⟩ : syracuseStep 13387619 = 20081429) B20081429
theorem B8925079 : Blo 2089435 8925079 := bstep (se 1 (by rfl) ⟨6693809, by rfl⟩ : syracuseStep 8925079 = 13387619) B13387619
theorem B11900105 : Blo 2089435 11900105 := bstep (se 2 (by rfl) ⟨4462539, by rfl⟩ : syracuseStep 11900105 = 8925079) B8925079
theorem B7933403 : Blo 2089435 7933403 := bstep (se 1 (by rfl) ⟨5950052, by rfl⟩ : syracuseStep 7933403 = 11900105) B11900105
theorem B5288935 : Blo 2089435 5288935 := bstep (se 1 (by rfl) ⟨3966701, by rfl⟩ : syracuseStep 5288935 = 7933403) B7933403
theorem B7051913 : Blo 2089435 7051913 := bstep (se 2 (by rfl) ⟨2644467, by rfl⟩ : syracuseStep 7051913 = 5288935) B5288935
theorem B4701275 : Blo 2089435 4701275 := bstep (se 1 (by rfl) ⟨3525956, by rfl⟩ : syracuseStep 4701275 = 7051913) B7051913
theorem B3134183 : Blo 2089435 3134183 := bstep (se 1 (by rfl) ⟨2350637, by rfl⟩ : syracuseStep 3134183 = 4701275) B4701275
theorem B2089455 : Blo 2089435 2089455 := bstep (se 1 (by rfl) ⟨1567091, by rfl⟩ : syracuseStep 2089455 = 3134183) B3134183
theorem B3134189 : Blo 2089435 3134189 := bbase (se 3 (by rfl) ⟨587660, by rfl⟩ : syracuseStep 3134189 = 1175321) (by norm_num)
theorem B2089459 : Blo 2089435 2089459 := bstep (se 1 (by rfl) ⟨1567094, by rfl⟩ : syracuseStep 2089459 = 3134189) B3134189
theorem B4701293 : Blo 2089435 4701293 := bbase (se 3 (by rfl) ⟨881492, by rfl⟩ : syracuseStep 4701293 = 1762985) (by norm_num)
theorem B3134195 : Blo 2089435 3134195 := bstep (se 1 (by rfl) ⟨2350646, by rfl⟩ : syracuseStep 3134195 = 4701293) B4701293
theorem B2089463 : Blo 2089435 2089463 := bstep (se 1 (by rfl) ⟨1567097, by rfl⟩ : syracuseStep 2089463 = 3134195) B3134195
theorem B3966725 : Blo 2089435 3966725 := bbase (se 4 (by rfl) ⟨371880, by rfl⟩ : syracuseStep 3966725 = 743761) (by norm_num)
theorem B2644483 : Blo 2089435 2644483 := bstep (se 1 (by rfl) ⟨1983362, by rfl⟩ : syracuseStep 2644483 = 3966725) B3966725
theorem B3525977 : Blo 2089435 3525977 := bstep (se 2 (by rfl) ⟨1322241, by rfl⟩ : syracuseStep 3525977 = 2644483) B2644483
theorem B2350651 : Blo 2089435 2350651 := bstep (se 1 (by rfl) ⟨1762988, by rfl⟩ : syracuseStep 2350651 = 3525977) B3525977
theorem B3134201 : Blo 2089435 3134201 := bstep (se 2 (by rfl) ⟨1175325, by rfl⟩ : syracuseStep 3134201 = 2350651) B2350651
theorem B2089467 : Blo 2089435 2089467 := bstep (se 1 (by rfl) ⟨1567100, by rfl⟩ : syracuseStep 2089467 = 3134201) B3134201
theorem B4020853 : Blo 2089435 4020853 := bbase (se 5 (by rfl) ⟨188477, by rfl⟩ : syracuseStep 4020853 = 376955) (by norm_num)
theorem B5361137 : Blo 2089435 5361137 := bstep (se 2 (by rfl) ⟨2010426, by rfl⟩ : syracuseStep 5361137 = 4020853) B4020853
theorem B3574091 : Blo 2089435 3574091 := bstep (se 1 (by rfl) ⟨2680568, by rfl⟩ : syracuseStep 3574091 = 5361137) B5361137
theorem B2382727 : Blo 2089435 2382727 := bstep (se 1 (by rfl) ⟨1787045, by rfl⟩ : syracuseStep 2382727 = 3574091) B3574091
theorem B3176969 : Blo 2089435 3176969 := bstep (se 2 (by rfl) ⟨1191363, by rfl⟩ : syracuseStep 3176969 = 2382727) B2382727
theorem B8471917 : Blo 2089435 8471917 := bstep (se 3 (by rfl) ⟨1588484, by rfl⟩ : syracuseStep 8471917 = 3176969) B3176969
theorem B45183557 : Blo 2089435 45183557 := bstep (se 4 (by rfl) ⟨4235958, by rfl⟩ : syracuseStep 45183557 = 8471917) B8471917
theorem B30122371 : Blo 2089435 30122371 := bstep (se 1 (by rfl) ⟨22591778, by rfl⟩ : syracuseStep 30122371 = 45183557) B45183557
theorem B40163161 : Blo 2089435 40163161 := bstep (se 2 (by rfl) ⟨15061185, by rfl⟩ : syracuseStep 40163161 = 30122371) B30122371
theorem B53550881 : Blo 2089435 53550881 := bstep (se 2 (by rfl) ⟨20081580, by rfl⟩ : syracuseStep 53550881 = 40163161) B40163161
theorem B35700587 : Blo 2089435 35700587 := bstep (se 1 (by rfl) ⟨26775440, by rfl⟩ : syracuseStep 35700587 = 53550881) B53550881
theorem B23800391 : Blo 2089435 23800391 := bstep (se 1 (by rfl) ⟨17850293, by rfl⟩ : syracuseStep 23800391 = 35700587) B35700587
theorem B15866927 : Blo 2089435 15866927 := bstep (se 1 (by rfl) ⟨11900195, by rfl⟩ : syracuseStep 15866927 = 23800391) B23800391
theorem B10577951 : Blo 2089435 10577951 := bstep (se 1 (by rfl) ⟨7933463, by rfl⟩ : syracuseStep 10577951 = 15866927) B15866927
theorem B7051967 : Blo 2089435 7051967 := bstep (se 1 (by rfl) ⟨5288975, by rfl⟩ : syracuseStep 7051967 = 10577951) B10577951
theorem B4701311 : Blo 2089435 4701311 := bstep (se 1 (by rfl) ⟨3525983, by rfl⟩ : syracuseStep 4701311 = 7051967) B7051967
theorem B3134207 : Blo 2089435 3134207 := bstep (se 1 (by rfl) ⟨2350655, by rfl⟩ : syracuseStep 3134207 = 4701311) B4701311
theorem B2089471 : Blo 2089435 2089471 := bstep (se 1 (by rfl) ⟨1567103, by rfl⟩ : syracuseStep 2089471 = 3134207) B3134207
theorem B3134213 : Blo 2089435 3134213 := bbase (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) (by norm_num)
theorem B2089475 : Blo 2089435 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B3525997 : Blo 2089435 3525997 := bbase (se 3 (by rfl) ⟨661124, by rfl⟩ : syracuseStep 3525997 = 1322249) (by norm_num)
theorem B4701329 : Blo 2089435 4701329 := bstep (se 2 (by rfl) ⟨1762998, by rfl⟩ : syracuseStep 4701329 = 3525997) B3525997
theorem B3134219 : Blo 2089435 3134219 := bstep (se 1 (by rfl) ⟨2350664, by rfl⟩ : syracuseStep 3134219 = 4701329) B4701329
theorem B2089479 : Blo 2089435 2089479 := bstep (se 1 (by rfl) ⟨1567109, by rfl⟩ : syracuseStep 2089479 = 3134219) B3134219
theorem B2350669 : Blo 2089435 2350669 := bbase (se 3 (by rfl) ⟨440750, by rfl⟩ : syracuseStep 2350669 = 881501) (by norm_num)
theorem B3134225 : Blo 2089435 3134225 := bstep (se 2 (by rfl) ⟨1175334, by rfl⟩ : syracuseStep 3134225 = 2350669) B2350669
theorem B2089483 : Blo 2089435 2089483 := bstep (se 1 (by rfl) ⟨1567112, by rfl⟩ : syracuseStep 2089483 = 3134225) B3134225
theorem B7052021 : Blo 2089435 7052021 := bbase (se 5 (by rfl) ⟨330563, by rfl⟩ : syracuseStep 7052021 = 661127) (by norm_num)
theorem B4701347 : Blo 2089435 4701347 := bstep (se 1 (by rfl) ⟨3526010, by rfl⟩ : syracuseStep 4701347 = 7052021) B7052021
theorem B3134231 : Blo 2089435 3134231 := bstep (se 1 (by rfl) ⟨2350673, by rfl⟩ : syracuseStep 3134231 = 4701347) B4701347
theorem B2089487 : Blo 2089435 2089487 := bstep (se 1 (by rfl) ⟨1567115, by rfl⟩ : syracuseStep 2089487 = 3134231) B3134231
theorem B3134237 : Blo 2089435 3134237 := bbase (se 3 (by rfl) ⟨587669, by rfl⟩ : syracuseStep 3134237 = 1175339) (by norm_num)
theorem B2089491 : Blo 2089435 2089491 := bstep (se 1 (by rfl) ⟨1567118, by rfl⟩ : syracuseStep 2089491 = 3134237) B3134237
theorem B4701365 : Blo 2089435 4701365 := bbase (se 5 (by rfl) ⟨220376, by rfl⟩ : syracuseStep 4701365 = 440753) (by norm_num)
theorem B3134243 : Blo 2089435 3134243 := bstep (se 1 (by rfl) ⟨2350682, by rfl⟩ : syracuseStep 3134243 = 4701365) B4701365
theorem B2089495 : Blo 2089435 2089495 := bstep (se 1 (by rfl) ⟨1567121, by rfl⟩ : syracuseStep 2089495 = 3134243) B3134243
theorem B2231317 : Blo 2089435 2231317 := bbase (se 6 (by rfl) ⟨52296, by rfl⟩ : syracuseStep 2231317 = 104593) (by norm_num)
theorem B11900357 : Blo 2089435 11900357 := bstep (se 4 (by rfl) ⟨1115658, by rfl⟩ : syracuseStep 11900357 = 2231317) B2231317
theorem B7933571 : Blo 2089435 7933571 := bstep (se 1 (by rfl) ⟨5950178, by rfl⟩ : syracuseStep 7933571 = 11900357) B11900357
theorem B5289047 : Blo 2089435 5289047 := bstep (se 1 (by rfl) ⟨3966785, by rfl⟩ : syracuseStep 5289047 = 7933571) B7933571
theorem B3526031 : Blo 2089435 3526031 := bstep (se 1 (by rfl) ⟨2644523, by rfl⟩ : syracuseStep 3526031 = 5289047) B5289047
theorem B2350687 : Blo 2089435 2350687 := bstep (se 1 (by rfl) ⟨1763015, by rfl⟩ : syracuseStep 2350687 = 3526031) B3526031
theorem B3134249 : Blo 2089435 3134249 := bstep (se 2 (by rfl) ⟨1175343, by rfl⟩ : syracuseStep 3134249 = 2350687) B2350687
theorem B2089499 : Blo 2089435 2089499 := bstep (se 1 (by rfl) ⟨1567124, by rfl⟩ : syracuseStep 2089499 = 3134249) B3134249
theorem B2231321 : Blo 2089435 2231321 := bbase (se 2 (by rfl) ⟨836745, by rfl⟩ : syracuseStep 2231321 = 1673491) (by norm_num)
theorem B5950189 : Blo 2089435 5950189 := bstep (se 3 (by rfl) ⟨1115660, by rfl⟩ : syracuseStep 5950189 = 2231321) B2231321
theorem B7933585 : Blo 2089435 7933585 := bstep (se 2 (by rfl) ⟨2975094, by rfl⟩ : syracuseStep 7933585 = 5950189) B5950189
theorem B10578113 : Blo 2089435 10578113 := bstep (se 2 (by rfl) ⟨3966792, by rfl⟩ : syracuseStep 10578113 = 7933585) B7933585
theorem B7052075 : Blo 2089435 7052075 := bstep (se 1 (by rfl) ⟨5289056, by rfl⟩ : syracuseStep 7052075 = 10578113) B10578113
theorem B4701383 : Blo 2089435 4701383 := bstep (se 1 (by rfl) ⟨3526037, by rfl⟩ : syracuseStep 4701383 = 7052075) B7052075
theorem B3134255 : Blo 2089435 3134255 := bstep (se 1 (by rfl) ⟨2350691, by rfl⟩ : syracuseStep 3134255 = 4701383) B4701383
theorem B2089503 : Blo 2089435 2089503 := bstep (se 1 (by rfl) ⟨1567127, by rfl⟩ : syracuseStep 2089503 = 3134255) B3134255
theorem B3134261 : Blo 2089435 3134261 := bbase (se 5 (by rfl) ⟨146918, by rfl⟩ : syracuseStep 3134261 = 293837) (by norm_num)
theorem B2089507 : Blo 2089435 2089507 := bstep (se 1 (by rfl) ⟨1567130, by rfl⟩ : syracuseStep 2089507 = 3134261) B3134261
theorem B5289077 : Blo 2089435 5289077 := bbase (se 5 (by rfl) ⟨247925, by rfl⟩ : syracuseStep 5289077 = 495851) (by norm_num)
theorem B3526051 : Blo 2089435 3526051 := bstep (se 1 (by rfl) ⟨2644538, by rfl⟩ : syracuseStep 3526051 = 5289077) B5289077
theorem B4701401 : Blo 2089435 4701401 := bstep (se 2 (by rfl) ⟨1763025, by rfl⟩ : syracuseStep 4701401 = 3526051) B3526051
theorem B3134267 : Blo 2089435 3134267 := bstep (se 1 (by rfl) ⟨2350700, by rfl⟩ : syracuseStep 3134267 = 4701401) B4701401
theorem B2089511 : Blo 2089435 2089511 := bstep (se 1 (by rfl) ⟨1567133, by rfl⟩ : syracuseStep 2089511 = 3134267) B3134267
theorem B2350705 : Blo 2089435 2350705 := bbase (se 2 (by rfl) ⟨881514, by rfl⟩ : syracuseStep 2350705 = 1763029) (by norm_num)
theorem B3134273 : Blo 2089435 3134273 := bstep (se 2 (by rfl) ⟨1175352, by rfl⟩ : syracuseStep 3134273 = 2350705) B2350705
theorem B2089515 : Blo 2089435 2089515 := bstep (se 1 (by rfl) ⟨1567136, by rfl⟩ : syracuseStep 2089515 = 3134273) B3134273
theorem B3816757 : Blo 2089435 3816757 := bbase (se 5 (by rfl) ⟨178910, by rfl⟩ : syracuseStep 3816757 = 357821) (by norm_num)
theorem B5089009 : Blo 2089435 5089009 := bstep (se 2 (by rfl) ⟨1908378, by rfl⟩ : syracuseStep 5089009 = 3816757) B3816757
theorem B6785345 : Blo 2089435 6785345 := bstep (se 2 (by rfl) ⟨2544504, by rfl⟩ : syracuseStep 6785345 = 5089009) B5089009
theorem B4523563 : Blo 2089435 4523563 := bstep (se 1 (by rfl) ⟨3392672, by rfl⟩ : syracuseStep 4523563 = 6785345) B6785345
theorem B24125669 : Blo 2089435 24125669 := bstep (se 4 (by rfl) ⟨2261781, by rfl⟩ : syracuseStep 24125669 = 4523563) B4523563
theorem B16083779 : Blo 2089435 16083779 := bstep (se 1 (by rfl) ⟨12062834, by rfl⟩ : syracuseStep 16083779 = 24125669) B24125669
theorem B42890077 : Blo 2089435 42890077 := bstep (se 3 (by rfl) ⟨8041889, by rfl⟩ : syracuseStep 42890077 = 16083779) B16083779
theorem B57186769 : Blo 2089435 57186769 := bstep (se 2 (by rfl) ⟨21445038, by rfl⟩ : syracuseStep 57186769 = 42890077) B42890077
theorem B76249025 : Blo 2089435 76249025 := bstep (se 2 (by rfl) ⟨28593384, by rfl⟩ : syracuseStep 76249025 = 57186769) B57186769
theorem B50832683 : Blo 2089435 50832683 := bstep (se 1 (by rfl) ⟨38124512, by rfl⟩ : syracuseStep 50832683 = 76249025) B76249025
theorem B33888455 : Blo 2089435 33888455 := bstep (se 1 (by rfl) ⟨25416341, by rfl⟩ : syracuseStep 33888455 = 50832683) B50832683
theorem B22592303 : Blo 2089435 22592303 := bstep (se 1 (by rfl) ⟨16944227, by rfl⟩ : syracuseStep 22592303 = 33888455) B33888455
theorem B15061535 : Blo 2089435 15061535 := bstep (se 1 (by rfl) ⟨11296151, by rfl⟩ : syracuseStep 15061535 = 22592303) B22592303
theorem B10041023 : Blo 2089435 10041023 := bstep (se 1 (by rfl) ⟨7530767, by rfl⟩ : syracuseStep 10041023 = 15061535) B15061535
theorem B6694015 : Blo 2089435 6694015 := bstep (se 1 (by rfl) ⟨5020511, by rfl⟩ : syracuseStep 6694015 = 10041023) B10041023
theorem B8925353 : Blo 2089435 8925353 := bstep (se 2 (by rfl) ⟨3347007, by rfl⟩ : syracuseStep 8925353 = 6694015) B6694015
theorem B5950235 : Blo 2089435 5950235 := bstep (se 1 (by rfl) ⟨4462676, by rfl⟩ : syracuseStep 5950235 = 8925353) B8925353
theorem B3966823 : Blo 2089435 3966823 := bstep (se 1 (by rfl) ⟨2975117, by rfl⟩ : syracuseStep 3966823 = 5950235) B5950235
theorem B5289097 : Blo 2089435 5289097 := bstep (se 2 (by rfl) ⟨1983411, by rfl⟩ : syracuseStep 5289097 = 3966823) B3966823
theorem B7052129 : Blo 2089435 7052129 := bstep (se 2 (by rfl) ⟨2644548, by rfl⟩ : syracuseStep 7052129 = 5289097) B5289097
theorem B4701419 : Blo 2089435 4701419 := bstep (se 1 (by rfl) ⟨3526064, by rfl⟩ : syracuseStep 4701419 = 7052129) B7052129
theorem B3134279 : Blo 2089435 3134279 := bstep (se 1 (by rfl) ⟨2350709, by rfl⟩ : syracuseStep 3134279 = 4701419) B4701419
theorem B2089519 : Blo 2089435 2089519 := bstep (se 1 (by rfl) ⟨1567139, by rfl⟩ : syracuseStep 2089519 = 3134279) B3134279
theorem B3134285 : Blo 2089435 3134285 := bbase (se 3 (by rfl) ⟨587678, by rfl⟩ : syracuseStep 3134285 = 1175357) (by norm_num)
theorem B2089523 : Blo 2089435 2089523 := bstep (se 1 (by rfl) ⟨1567142, by rfl⟩ : syracuseStep 2089523 = 3134285) B3134285
theorem B4701437 : Blo 2089435 4701437 := bbase (se 3 (by rfl) ⟨881519, by rfl⟩ : syracuseStep 4701437 = 1763039) (by norm_num)
theorem B3134291 : Blo 2089435 3134291 := bstep (se 1 (by rfl) ⟨2350718, by rfl⟩ : syracuseStep 3134291 = 4701437) B4701437
theorem B2089527 : Blo 2089435 2089527 := bstep (se 1 (by rfl) ⟨1567145, by rfl⟩ : syracuseStep 2089527 = 3134291) B3134291
theorem B3526085 : Blo 2089435 3526085 := bbase (se 4 (by rfl) ⟨330570, by rfl⟩ : syracuseStep 3526085 = 661141) (by norm_num)
theorem B2350723 : Blo 2089435 2350723 := bstep (se 1 (by rfl) ⟨1763042, by rfl⟩ : syracuseStep 2350723 = 3526085) B3526085
theorem B3134297 : Blo 2089435 3134297 := bstep (se 2 (by rfl) ⟨1175361, by rfl⟩ : syracuseStep 3134297 = 2350723) B2350723
theorem B2089531 : Blo 2089435 2089531 := bstep (se 1 (by rfl) ⟨1567148, by rfl⟩ : syracuseStep 2089531 = 3134297) B3134297
theorem B15867413 : Blo 2089435 15867413 := bbase (se 6 (by rfl) ⟨371892, by rfl⟩ : syracuseStep 15867413 = 743785) (by norm_num)
theorem B10578275 : Blo 2089435 10578275 := bstep (se 1 (by rfl) ⟨7933706, by rfl⟩ : syracuseStep 10578275 = 15867413) B15867413
theorem B7052183 : Blo 2089435 7052183 := bstep (se 1 (by rfl) ⟨5289137, by rfl⟩ : syracuseStep 7052183 = 10578275) B10578275
theorem B4701455 : Blo 2089435 4701455 := bstep (se 1 (by rfl) ⟨3526091, by rfl⟩ : syracuseStep 4701455 = 7052183) B7052183
theorem B3134303 : Blo 2089435 3134303 := bstep (se 1 (by rfl) ⟨2350727, by rfl⟩ : syracuseStep 3134303 = 4701455) B4701455
theorem B2089535 : Blo 2089435 2089535 := bstep (se 1 (by rfl) ⟨1567151, by rfl⟩ : syracuseStep 2089535 = 3134303) B3134303
theorem B3134309 : Blo 2089435 3134309 := bbase (se 4 (by rfl) ⟨293841, by rfl⟩ : syracuseStep 3134309 = 587683) (by norm_num)
theorem B2089539 : Blo 2089435 2089539 := bstep (se 1 (by rfl) ⟨1567154, by rfl⟩ : syracuseStep 2089539 = 3134309) B3134309
theorem B3966869 : Blo 2089435 3966869 := bbase (se 6 (by rfl) ⟨92973, by rfl⟩ : syracuseStep 3966869 = 185947) (by norm_num)
theorem B2644579 : Blo 2089435 2644579 := bstep (se 1 (by rfl) ⟨1983434, by rfl⟩ : syracuseStep 2644579 = 3966869) B3966869
theorem B3526105 : Blo 2089435 3526105 := bstep (se 2 (by rfl) ⟨1322289, by rfl⟩ : syracuseStep 3526105 = 2644579) B2644579
theorem B4701473 : Blo 2089435 4701473 := bstep (se 2 (by rfl) ⟨1763052, by rfl⟩ : syracuseStep 4701473 = 3526105) B3526105
theorem B3134315 : Blo 2089435 3134315 := bstep (se 1 (by rfl) ⟨2350736, by rfl⟩ : syracuseStep 3134315 = 4701473) B4701473
theorem B2089543 : Blo 2089435 2089543 := bstep (se 1 (by rfl) ⟨1567157, by rfl⟩ : syracuseStep 2089543 = 3134315) B3134315
theorem B2350741 : Blo 2089435 2350741 := bbase (se 6 (by rfl) ⟨55095, by rfl⟩ : syracuseStep 2350741 = 110191) (by norm_num)
theorem B3134321 : Blo 2089435 3134321 := bstep (se 2 (by rfl) ⟨1175370, by rfl⟩ : syracuseStep 3134321 = 2350741) B2350741
theorem B2089547 : Blo 2089435 2089547 := bstep (se 1 (by rfl) ⟨1567160, by rfl⟩ : syracuseStep 2089547 = 3134321) B3134321
theorem B2644589 : Blo 2089435 2644589 := bbase (se 3 (by rfl) ⟨495860, by rfl⟩ : syracuseStep 2644589 = 991721) (by norm_num)
theorem B7052237 : Blo 2089435 7052237 := bstep (se 3 (by rfl) ⟨1322294, by rfl⟩ : syracuseStep 7052237 = 2644589) B2644589
theorem B4701491 : Blo 2089435 4701491 := bstep (se 1 (by rfl) ⟨3526118, by rfl⟩ : syracuseStep 4701491 = 7052237) B7052237
theorem B3134327 : Blo 2089435 3134327 := bstep (se 1 (by rfl) ⟨2350745, by rfl⟩ : syracuseStep 3134327 = 4701491) B4701491
theorem B2089551 : Blo 2089435 2089551 := bstep (se 1 (by rfl) ⟨1567163, by rfl⟩ : syracuseStep 2089551 = 3134327) B3134327
theorem B3134333 : Blo 2089435 3134333 := bbase (se 3 (by rfl) ⟨587687, by rfl⟩ : syracuseStep 3134333 = 1175375) (by norm_num)
theorem B2089555 : Blo 2089435 2089555 := bstep (se 1 (by rfl) ⟨1567166, by rfl⟩ : syracuseStep 2089555 = 3134333) B3134333
theorem B4701509 : Blo 2089435 4701509 := bbase (se 4 (by rfl) ⟨440766, by rfl⟩ : syracuseStep 4701509 = 881533) (by norm_num)
theorem B3134339 : Blo 2089435 3134339 := bstep (se 1 (by rfl) ⟨2350754, by rfl⟩ : syracuseStep 3134339 = 4701509) B4701509
theorem B2089559 : Blo 2089435 2089559 := bstep (se 1 (by rfl) ⟨1567169, by rfl⟩ : syracuseStep 2089559 = 3134339) B3134339
theorem B2510309 : Blo 2089435 2510309 := bbase (se 4 (by rfl) ⟨235341, by rfl⟩ : syracuseStep 2510309 = 470683) (by norm_num)
theorem B6694157 : Blo 2089435 6694157 := bstep (se 3 (by rfl) ⟨1255154, by rfl⟩ : syracuseStep 6694157 = 2510309) B2510309
theorem B4462771 : Blo 2089435 4462771 := bstep (se 1 (by rfl) ⟨3347078, by rfl⟩ : syracuseStep 4462771 = 6694157) B6694157
theorem B5950361 : Blo 2089435 5950361 := bstep (se 2 (by rfl) ⟨2231385, by rfl⟩ : syracuseStep 5950361 = 4462771) B4462771
theorem B3966907 : Blo 2089435 3966907 := bstep (se 1 (by rfl) ⟨2975180, by rfl⟩ : syracuseStep 3966907 = 5950361) B5950361
theorem B5289209 : Blo 2089435 5289209 := bstep (se 2 (by rfl) ⟨1983453, by rfl⟩ : syracuseStep 5289209 = 3966907) B3966907
theorem B3526139 : Blo 2089435 3526139 := bstep (se 1 (by rfl) ⟨2644604, by rfl⟩ : syracuseStep 3526139 = 5289209) B5289209
theorem B2350759 : Blo 2089435 2350759 := bstep (se 1 (by rfl) ⟨1763069, by rfl⟩ : syracuseStep 2350759 = 3526139) B3526139
theorem B3134345 : Blo 2089435 3134345 := bstep (se 2 (by rfl) ⟨1175379, by rfl⟩ : syracuseStep 3134345 = 2350759) B2350759
theorem B2089563 : Blo 2089435 2089563 := bstep (se 1 (by rfl) ⟨1567172, by rfl⟩ : syracuseStep 2089563 = 3134345) B3134345
theorem B10578437 : Blo 2089435 10578437 := bbase (se 4 (by rfl) ⟨991728, by rfl⟩ : syracuseStep 10578437 = 1983457) (by norm_num)
theorem B7052291 : Blo 2089435 7052291 := bstep (se 1 (by rfl) ⟨5289218, by rfl⟩ : syracuseStep 7052291 = 10578437) B10578437
theorem B4701527 : Blo 2089435 4701527 := bstep (se 1 (by rfl) ⟨3526145, by rfl⟩ : syracuseStep 4701527 = 7052291) B7052291
theorem B3134351 : Blo 2089435 3134351 := bstep (se 1 (by rfl) ⟨2350763, by rfl⟩ : syracuseStep 3134351 = 4701527) B4701527
theorem B2089567 : Blo 2089435 2089567 := bstep (se 1 (by rfl) ⟨1567175, by rfl⟩ : syracuseStep 2089567 = 3134351) B3134351
theorem B3134357 : Blo 2089435 3134357 := bbase (se 6 (by rfl) ⟨73461, by rfl⟩ : syracuseStep 3134357 = 146923) (by norm_num)
theorem B2089571 : Blo 2089435 2089571 := bstep (se 1 (by rfl) ⟨1567178, by rfl⟩ : syracuseStep 2089571 = 3134357) B3134357
theorem B11900789 : Blo 2089435 11900789 := bbase (se 5 (by rfl) ⟨557849, by rfl⟩ : syracuseStep 11900789 = 1115699) (by norm_num)
theorem B7933859 : Blo 2089435 7933859 := bstep (se 1 (by rfl) ⟨5950394, by rfl⟩ : syracuseStep 7933859 = 11900789) B11900789
theorem B5289239 : Blo 2089435 5289239 := bstep (se 1 (by rfl) ⟨3966929, by rfl⟩ : syracuseStep 5289239 = 7933859) B7933859
theorem B3526159 : Blo 2089435 3526159 := bstep (se 1 (by rfl) ⟨2644619, by rfl⟩ : syracuseStep 3526159 = 5289239) B5289239
theorem B4701545 : Blo 2089435 4701545 := bstep (se 2 (by rfl) ⟨1763079, by rfl⟩ : syracuseStep 4701545 = 3526159) B3526159
theorem B3134363 : Blo 2089435 3134363 := bstep (se 1 (by rfl) ⟨2350772, by rfl⟩ : syracuseStep 3134363 = 4701545) B4701545
theorem B2089575 : Blo 2089435 2089575 := bstep (se 1 (by rfl) ⟨1567181, by rfl⟩ : syracuseStep 2089575 = 3134363) B3134363
theorem B2350777 : Blo 2089435 2350777 := bbase (se 2 (by rfl) ⟨881541, by rfl⟩ : syracuseStep 2350777 = 1763083) (by norm_num)
theorem B3134369 : Blo 2089435 3134369 := bstep (se 2 (by rfl) ⟨1175388, by rfl⟩ : syracuseStep 3134369 = 2350777) B2350777
theorem B2089579 : Blo 2089435 2089579 := bstep (se 1 (by rfl) ⟨1567184, by rfl⟩ : syracuseStep 2089579 = 3134369) B3134369
theorem B4462813 : Blo 2089435 4462813 := bbase (se 3 (by rfl) ⟨836777, by rfl⟩ : syracuseStep 4462813 = 1673555) (by norm_num)
theorem B5950417 : Blo 2089435 5950417 := bstep (se 2 (by rfl) ⟨2231406, by rfl⟩ : syracuseStep 5950417 = 4462813) B4462813
theorem B7933889 : Blo 2089435 7933889 := bstep (se 2 (by rfl) ⟨2975208, by rfl⟩ : syracuseStep 7933889 = 5950417) B5950417
theorem B5289259 : Blo 2089435 5289259 := bstep (se 1 (by rfl) ⟨3966944, by rfl⟩ : syracuseStep 5289259 = 7933889) B7933889
theorem B7052345 : Blo 2089435 7052345 := bstep (se 2 (by rfl) ⟨2644629, by rfl⟩ : syracuseStep 7052345 = 5289259) B5289259
theorem B4701563 : Blo 2089435 4701563 := bstep (se 1 (by rfl) ⟨3526172, by rfl⟩ : syracuseStep 4701563 = 7052345) B7052345
theorem B3134375 : Blo 2089435 3134375 := bstep (se 1 (by rfl) ⟨2350781, by rfl⟩ : syracuseStep 3134375 = 4701563) B4701563
theorem B2089583 : Blo 2089435 2089583 := bstep (se 1 (by rfl) ⟨1567187, by rfl⟩ : syracuseStep 2089583 = 3134375) B3134375
theorem B3134381 : Blo 2089435 3134381 := bbase (se 3 (by rfl) ⟨587696, by rfl⟩ : syracuseStep 3134381 = 1175393) (by norm_num)
theorem B2089587 : Blo 2089435 2089587 := bstep (se 1 (by rfl) ⟨1567190, by rfl⟩ : syracuseStep 2089587 = 3134381) B3134381
theorem B4701581 : Blo 2089435 4701581 := bbase (se 3 (by rfl) ⟨881546, by rfl⟩ : syracuseStep 4701581 = 1763093) (by norm_num)
theorem B3134387 : Blo 2089435 3134387 := bstep (se 1 (by rfl) ⟨2350790, by rfl⟩ : syracuseStep 3134387 = 4701581) B4701581
theorem B2089591 : Blo 2089435 2089591 := bstep (se 1 (by rfl) ⟨1567193, by rfl⟩ : syracuseStep 2089591 = 3134387) B3134387
theorem B2644645 : Blo 2089435 2644645 := bbase (se 4 (by rfl) ⟨247935, by rfl⟩ : syracuseStep 2644645 = 495871) (by norm_num)
theorem B3526193 : Blo 2089435 3526193 := bstep (se 2 (by rfl) ⟨1322322, by rfl⟩ : syracuseStep 3526193 = 2644645) B2644645
theorem B2350795 : Blo 2089435 2350795 := bstep (se 1 (by rfl) ⟨1763096, by rfl⟩ : syracuseStep 2350795 = 3526193) B3526193
theorem B3134393 : Blo 2089435 3134393 := bstep (se 2 (by rfl) ⟨1175397, by rfl⟩ : syracuseStep 3134393 = 2350795) B2350795
theorem B2089595 : Blo 2089435 2089595 := bstep (se 1 (by rfl) ⟨1567196, by rfl⟩ : syracuseStep 2089595 = 3134393) B3134393
theorem B14297237 : Blo 2089435 14297237 := bbase (se 6 (by rfl) ⟨335091, by rfl⟩ : syracuseStep 14297237 = 670183) (by norm_num)
theorem B9531491 : Blo 2089435 9531491 := bstep (se 1 (by rfl) ⟨7148618, by rfl⟩ : syracuseStep 9531491 = 14297237) B14297237
theorem B25417309 : Blo 2089435 25417309 := bstep (se 3 (by rfl) ⟨4765745, by rfl⟩ : syracuseStep 25417309 = 9531491) B9531491
theorem B33889745 : Blo 2089435 33889745 := bstep (se 2 (by rfl) ⟨12708654, by rfl⟩ : syracuseStep 33889745 = 25417309) B25417309
theorem B22593163 : Blo 2089435 22593163 := bstep (se 1 (by rfl) ⟨16944872, by rfl⟩ : syracuseStep 22593163 = 33889745) B33889745
theorem B30124217 : Blo 2089435 30124217 := bstep (se 2 (by rfl) ⟨11296581, by rfl⟩ : syracuseStep 30124217 = 22593163) B22593163
theorem B20082811 : Blo 2089435 20082811 := bstep (se 1 (by rfl) ⟨15062108, by rfl⟩ : syracuseStep 20082811 = 30124217) B30124217
theorem B26777081 : Blo 2089435 26777081 := bstep (se 2 (by rfl) ⟨10041405, by rfl⟩ : syracuseStep 26777081 = 20082811) B20082811
theorem B17851387 : Blo 2089435 17851387 := bstep (se 1 (by rfl) ⟨13388540, by rfl⟩ : syracuseStep 17851387 = 26777081) B26777081
theorem B23801849 : Blo 2089435 23801849 := bstep (se 2 (by rfl) ⟨8925693, by rfl⟩ : syracuseStep 23801849 = 17851387) B17851387
theorem B15867899 : Blo 2089435 15867899 := bstep (se 1 (by rfl) ⟨11900924, by rfl⟩ : syracuseStep 15867899 = 23801849) B23801849
theorem B10578599 : Blo 2089435 10578599 := bstep (se 1 (by rfl) ⟨7933949, by rfl⟩ : syracuseStep 10578599 = 15867899) B15867899
theorem B7052399 : Blo 2089435 7052399 := bstep (se 1 (by rfl) ⟨5289299, by rfl⟩ : syracuseStep 7052399 = 10578599) B10578599
theorem B4701599 : Blo 2089435 4701599 := bstep (se 1 (by rfl) ⟨3526199, by rfl⟩ : syracuseStep 4701599 = 7052399) B7052399
theorem B3134399 : Blo 2089435 3134399 := bstep (se 1 (by rfl) ⟨2350799, by rfl⟩ : syracuseStep 3134399 = 4701599) B4701599
theorem B2089599 : Blo 2089435 2089599 := bstep (se 1 (by rfl) ⟨1567199, by rfl⟩ : syracuseStep 2089599 = 3134399) B3134399
theorem B3134405 : Blo 2089435 3134405 := bbase (se 4 (by rfl) ⟨293850, by rfl⟩ : syracuseStep 3134405 = 587701) (by norm_num)
theorem B2089603 : Blo 2089435 2089603 := bstep (se 1 (by rfl) ⟨1567202, by rfl⟩ : syracuseStep 2089603 = 3134405) B3134405
theorem B3526213 : Blo 2089435 3526213 := bbase (se 4 (by rfl) ⟨330582, by rfl⟩ : syracuseStep 3526213 = 661165) (by norm_num)
theorem B4701617 : Blo 2089435 4701617 := bstep (se 2 (by rfl) ⟨1763106, by rfl⟩ : syracuseStep 4701617 = 3526213) B3526213
theorem B3134411 : Blo 2089435 3134411 := bstep (se 1 (by rfl) ⟨2350808, by rfl⟩ : syracuseStep 3134411 = 4701617) B4701617
theorem B2089607 : Blo 2089435 2089607 := bstep (se 1 (by rfl) ⟨1567205, by rfl⟩ : syracuseStep 2089607 = 3134411) B3134411
theorem B2350813 : Blo 2089435 2350813 := bbase (se 3 (by rfl) ⟨440777, by rfl⟩ : syracuseStep 2350813 = 881555) (by norm_num)
theorem B3134417 : Blo 2089435 3134417 := bstep (se 2 (by rfl) ⟨1175406, by rfl⟩ : syracuseStep 3134417 = 2350813) B2350813
theorem B2089611 : Blo 2089435 2089611 := bstep (se 1 (by rfl) ⟨1567208, by rfl⟩ : syracuseStep 2089611 = 3134417) B3134417
theorem B7052453 : Blo 2089435 7052453 := bbase (se 4 (by rfl) ⟨661167, by rfl⟩ : syracuseStep 7052453 = 1322335) (by norm_num)
theorem B4701635 : Blo 2089435 4701635 := bstep (se 1 (by rfl) ⟨3526226, by rfl⟩ : syracuseStep 4701635 = 7052453) B7052453
theorem B3134423 : Blo 2089435 3134423 := bstep (se 1 (by rfl) ⟨2350817, by rfl⟩ : syracuseStep 3134423 = 4701635) B4701635
theorem B2089615 : Blo 2089435 2089615 := bstep (se 1 (by rfl) ⟨1567211, by rfl⟩ : syracuseStep 2089615 = 3134423) B3134423
theorem B3134429 : Blo 2089435 3134429 := bbase (se 3 (by rfl) ⟨587705, by rfl⟩ : syracuseStep 3134429 = 1175411) (by norm_num)
theorem B2089619 : Blo 2089435 2089619 := bstep (se 1 (by rfl) ⟨1567214, by rfl⟩ : syracuseStep 2089619 = 3134429) B3134429
theorem B4701653 : Blo 2089435 4701653 := bbase (se 7 (by rfl) ⟨55097, by rfl⟩ : syracuseStep 4701653 = 110195) (by norm_num)
theorem B3134435 : Blo 2089435 3134435 := bstep (se 1 (by rfl) ⟨2350826, by rfl⟩ : syracuseStep 3134435 = 4701653) B4701653
theorem B2089623 : Blo 2089435 2089623 := bstep (se 1 (by rfl) ⟨1567217, by rfl⟩ : syracuseStep 2089623 = 3134435) B3134435
theorem B7531157 : Blo 2089435 7531157 := bbase (se 6 (by rfl) ⟨176511, by rfl⟩ : syracuseStep 7531157 = 353023) (by norm_num)
theorem B20083085 : Blo 2089435 20083085 := bstep (se 3 (by rfl) ⟨3765578, by rfl⟩ : syracuseStep 20083085 = 7531157) B7531157
theorem B13388723 : Blo 2089435 13388723 := bstep (se 1 (by rfl) ⟨10041542, by rfl⟩ : syracuseStep 13388723 = 20083085) B20083085
theorem B8925815 : Blo 2089435 8925815 := bstep (se 1 (by rfl) ⟨6694361, by rfl⟩ : syracuseStep 8925815 = 13388723) B13388723
theorem B5950543 : Blo 2089435 5950543 := bstep (se 1 (by rfl) ⟨4462907, by rfl⟩ : syracuseStep 5950543 = 8925815) B8925815
theorem B7934057 : Blo 2089435 7934057 := bstep (se 2 (by rfl) ⟨2975271, by rfl⟩ : syracuseStep 7934057 = 5950543) B5950543
theorem B5289371 : Blo 2089435 5289371 := bstep (se 1 (by rfl) ⟨3967028, by rfl⟩ : syracuseStep 5289371 = 7934057) B7934057
theorem B3526247 : Blo 2089435 3526247 := bstep (se 1 (by rfl) ⟨2644685, by rfl⟩ : syracuseStep 3526247 = 5289371) B5289371
theorem B2350831 : Blo 2089435 2350831 := bstep (se 1 (by rfl) ⟨1763123, by rfl⟩ : syracuseStep 2350831 = 3526247) B3526247
theorem B3134441 : Blo 2089435 3134441 := bstep (se 2 (by rfl) ⟨1175415, by rfl⟩ : syracuseStep 3134441 = 2350831) B2350831
theorem B2089627 : Blo 2089435 2089627 := bstep (se 1 (by rfl) ⟨1567220, by rfl⟩ : syracuseStep 2089627 = 3134441) B3134441
theorem B6694373 : Blo 2089435 6694373 := bbase (se 4 (by rfl) ⟨627597, by rfl⟩ : syracuseStep 6694373 = 1255195) (by norm_num)
theorem B17851661 : Blo 2089435 17851661 := bstep (se 3 (by rfl) ⟨3347186, by rfl⟩ : syracuseStep 17851661 = 6694373) B6694373
theorem B11901107 : Blo 2089435 11901107 := bstep (se 1 (by rfl) ⟨8925830, by rfl⟩ : syracuseStep 11901107 = 17851661) B17851661
theorem B7934071 : Blo 2089435 7934071 := bstep (se 1 (by rfl) ⟨5950553, by rfl⟩ : syracuseStep 7934071 = 11901107) B11901107
theorem B10578761 : Blo 2089435 10578761 := bstep (se 2 (by rfl) ⟨3967035, by rfl⟩ : syracuseStep 10578761 = 7934071) B7934071
theorem B7052507 : Blo 2089435 7052507 := bstep (se 1 (by rfl) ⟨5289380, by rfl⟩ : syracuseStep 7052507 = 10578761) B10578761
theorem B4701671 : Blo 2089435 4701671 := bstep (se 1 (by rfl) ⟨3526253, by rfl⟩ : syracuseStep 4701671 = 7052507) B7052507
theorem B3134447 : Blo 2089435 3134447 := bstep (se 1 (by rfl) ⟨2350835, by rfl⟩ : syracuseStep 3134447 = 4701671) B4701671
theorem B2089631 : Blo 2089435 2089631 := bstep (se 1 (by rfl) ⟨1567223, by rfl⟩ : syracuseStep 2089631 = 3134447) B3134447
theorem B3134453 : Blo 2089435 3134453 := bbase (se 5 (by rfl) ⟨146927, by rfl⟩ : syracuseStep 3134453 = 293855) (by norm_num)
theorem B2089635 : Blo 2089435 2089635 := bstep (se 1 (by rfl) ⟨1567226, by rfl⟩ : syracuseStep 2089635 = 3134453) B3134453
theorem B4462933 : Blo 2089435 4462933 := bbase (se 10 (by rfl) ⟨6537, by rfl⟩ : syracuseStep 4462933 = 13075) (by norm_num)
theorem B5950577 : Blo 2089435 5950577 := bstep (se 2 (by rfl) ⟨2231466, by rfl⟩ : syracuseStep 5950577 = 4462933) B4462933
theorem B3967051 : Blo 2089435 3967051 := bstep (se 1 (by rfl) ⟨2975288, by rfl⟩ : syracuseStep 3967051 = 5950577) B5950577
theorem B5289401 : Blo 2089435 5289401 := bstep (se 2 (by rfl) ⟨1983525, by rfl⟩ : syracuseStep 5289401 = 3967051) B3967051
theorem B3526267 : Blo 2089435 3526267 := bstep (se 1 (by rfl) ⟨2644700, by rfl⟩ : syracuseStep 3526267 = 5289401) B5289401
theorem B4701689 : Blo 2089435 4701689 := bstep (se 2 (by rfl) ⟨1763133, by rfl⟩ : syracuseStep 4701689 = 3526267) B3526267
theorem B3134459 : Blo 2089435 3134459 := bstep (se 1 (by rfl) ⟨2350844, by rfl⟩ : syracuseStep 3134459 = 4701689) B4701689
theorem B2089639 : Blo 2089435 2089639 := bstep (se 1 (by rfl) ⟨1567229, by rfl⟩ : syracuseStep 2089639 = 3134459) B3134459
theorem B2350849 : Blo 2089435 2350849 := bbase (se 2 (by rfl) ⟨881568, by rfl⟩ : syracuseStep 2350849 = 1763137) (by norm_num)
theorem B3134465 : Blo 2089435 3134465 := bstep (se 2 (by rfl) ⟨1175424, by rfl⟩ : syracuseStep 3134465 = 2350849) B2350849
theorem B2089643 : Blo 2089435 2089643 := bstep (se 1 (by rfl) ⟨1567232, by rfl⟩ : syracuseStep 2089643 = 3134465) B3134465
theorem B5289421 : Blo 2089435 5289421 := bbase (se 3 (by rfl) ⟨991766, by rfl⟩ : syracuseStep 5289421 = 1983533) (by norm_num)
theorem B7052561 : Blo 2089435 7052561 := bstep (se 2 (by rfl) ⟨2644710, by rfl⟩ : syracuseStep 7052561 = 5289421) B5289421
theorem B4701707 : Blo 2089435 4701707 := bstep (se 1 (by rfl) ⟨3526280, by rfl⟩ : syracuseStep 4701707 = 7052561) B7052561
theorem B3134471 : Blo 2089435 3134471 := bstep (se 1 (by rfl) ⟨2350853, by rfl⟩ : syracuseStep 3134471 = 4701707) B4701707
theorem B2089647 : Blo 2089435 2089647 := bstep (se 1 (by rfl) ⟨1567235, by rfl⟩ : syracuseStep 2089647 = 3134471) B3134471
theorem B3134477 : Blo 2089435 3134477 := bbase (se 3 (by rfl) ⟨587714, by rfl⟩ : syracuseStep 3134477 = 1175429) (by norm_num)
theorem B2089651 : Blo 2089435 2089651 := bstep (se 1 (by rfl) ⟨1567238, by rfl⟩ : syracuseStep 2089651 = 3134477) B3134477
theorem B4701725 : Blo 2089435 4701725 := bbase (se 3 (by rfl) ⟨881573, by rfl⟩ : syracuseStep 4701725 = 1763147) (by norm_num)
theorem B3134483 : Blo 2089435 3134483 := bstep (se 1 (by rfl) ⟨2350862, by rfl⟩ : syracuseStep 3134483 = 4701725) B4701725
theorem B2089655 : Blo 2089435 2089655 := bstep (se 1 (by rfl) ⟨1567241, by rfl⟩ : syracuseStep 2089655 = 3134483) B3134483
theorem B3526301 : Blo 2089435 3526301 := bbase (se 3 (by rfl) ⟨661181, by rfl⟩ : syracuseStep 3526301 = 1322363) (by norm_num)
theorem B2350867 : Blo 2089435 2350867 := bstep (se 1 (by rfl) ⟨1763150, by rfl⟩ : syracuseStep 2350867 = 3526301) B3526301
theorem B3134489 : Blo 2089435 3134489 := bstep (se 2 (by rfl) ⟨1175433, by rfl⟩ : syracuseStep 3134489 = 2350867) B2350867
theorem B2089659 : Blo 2089435 2089659 := bstep (se 1 (by rfl) ⟨1567244, by rfl⟩ : syracuseStep 2089659 = 3134489) B3134489
theorem B30125141 : Blo 2089435 30125141 := bbase (se 8 (by rfl) ⟨176514, by rfl⟩ : syracuseStep 30125141 = 353029) (by norm_num)
theorem B20083427 : Blo 2089435 20083427 := bstep (se 1 (by rfl) ⟨15062570, by rfl⟩ : syracuseStep 20083427 = 30125141) B30125141
theorem B13388951 : Blo 2089435 13388951 := bstep (se 1 (by rfl) ⟨10041713, by rfl⟩ : syracuseStep 13388951 = 20083427) B20083427
theorem B8925967 : Blo 2089435 8925967 := bstep (se 1 (by rfl) ⟨6694475, by rfl⟩ : syracuseStep 8925967 = 13388951) B13388951
theorem B11901289 : Blo 2089435 11901289 := bstep (se 2 (by rfl) ⟨4462983, by rfl⟩ : syracuseStep 11901289 = 8925967) B8925967
theorem B15868385 : Blo 2089435 15868385 := bstep (se 2 (by rfl) ⟨5950644, by rfl⟩ : syracuseStep 15868385 = 11901289) B11901289
theorem B10578923 : Blo 2089435 10578923 := bstep (se 1 (by rfl) ⟨7934192, by rfl⟩ : syracuseStep 10578923 = 15868385) B15868385
theorem B7052615 : Blo 2089435 7052615 := bstep (se 1 (by rfl) ⟨5289461, by rfl⟩ : syracuseStep 7052615 = 10578923) B10578923
theorem B4701743 : Blo 2089435 4701743 := bstep (se 1 (by rfl) ⟨3526307, by rfl⟩ : syracuseStep 4701743 = 7052615) B7052615
theorem B3134495 : Blo 2089435 3134495 := bstep (se 1 (by rfl) ⟨2350871, by rfl⟩ : syracuseStep 3134495 = 4701743) B4701743
theorem B2089663 : Blo 2089435 2089663 := bstep (se 1 (by rfl) ⟨1567247, by rfl⟩ : syracuseStep 2089663 = 3134495) B3134495
theorem B3134501 : Blo 2089435 3134501 := bbase (se 4 (by rfl) ⟨293859, by rfl⟩ : syracuseStep 3134501 = 587719) (by norm_num)
theorem B2089667 : Blo 2089435 2089667 := bstep (se 1 (by rfl) ⟨1567250, by rfl⟩ : syracuseStep 2089667 = 3134501) B3134501
theorem B2644741 : Blo 2089435 2644741 := bbase (se 4 (by rfl) ⟨247944, by rfl⟩ : syracuseStep 2644741 = 495889) (by norm_num)
theorem B3526321 : Blo 2089435 3526321 := bstep (se 2 (by rfl) ⟨1322370, by rfl⟩ : syracuseStep 3526321 = 2644741) B2644741
theorem B4701761 : Blo 2089435 4701761 := bstep (se 2 (by rfl) ⟨1763160, by rfl⟩ : syracuseStep 4701761 = 3526321) B3526321
theorem B3134507 : Blo 2089435 3134507 := bstep (se 1 (by rfl) ⟨2350880, by rfl⟩ : syracuseStep 3134507 = 4701761) B4701761
theorem B2089671 : Blo 2089435 2089671 := bstep (se 1 (by rfl) ⟨1567253, by rfl⟩ : syracuseStep 2089671 = 3134507) B3134507
theorem B2350885 : Blo 2089435 2350885 := bbase (se 4 (by rfl) ⟨220395, by rfl⟩ : syracuseStep 2350885 = 440791) (by norm_num)
theorem B3134513 : Blo 2089435 3134513 := bstep (se 2 (by rfl) ⟨1175442, by rfl⟩ : syracuseStep 3134513 = 2350885) B2350885
theorem B2089675 : Blo 2089435 2089675 := bstep (se 1 (by rfl) ⟨1567256, by rfl⟩ : syracuseStep 2089675 = 3134513) B3134513
theorem B8926037 : Blo 2089435 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B5950691 : Blo 2089435 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B3967127 : Blo 2089435 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B2644751 : Blo 2089435 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B7052669 : Blo 2089435 7052669 := bstep (se 3 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 7052669 = 2644751) B2644751
theorem B4701779 : Blo 2089435 4701779 := bstep (se 1 (by rfl) ⟨3526334, by rfl⟩ : syracuseStep 4701779 = 7052669) B7052669
theorem B3134519 : Blo 2089435 3134519 := bstep (se 1 (by rfl) ⟨2350889, by rfl⟩ : syracuseStep 3134519 = 4701779) B4701779
theorem B2089679 : Blo 2089435 2089679 := bstep (se 1 (by rfl) ⟨1567259, by rfl⟩ : syracuseStep 2089679 = 3134519) B3134519
theorem B3134525 : Blo 2089435 3134525 := bbase (se 3 (by rfl) ⟨587723, by rfl⟩ : syracuseStep 3134525 = 1175447) (by norm_num)
theorem B2089683 : Blo 2089435 2089683 := bstep (se 1 (by rfl) ⟨1567262, by rfl⟩ : syracuseStep 2089683 = 3134525) B3134525
theorem B4701797 : Blo 2089435 4701797 := bbase (se 4 (by rfl) ⟨440793, by rfl⟩ : syracuseStep 4701797 = 881587) (by norm_num)
theorem B3134531 : Blo 2089435 3134531 := bstep (se 1 (by rfl) ⟨2350898, by rfl⟩ : syracuseStep 3134531 = 4701797) B4701797
theorem B2089687 : Blo 2089435 2089687 := bstep (se 1 (by rfl) ⟨1567265, by rfl⟩ : syracuseStep 2089687 = 3134531) B3134531
theorem B5289533 : Blo 2089435 5289533 := bbase (se 3 (by rfl) ⟨991787, by rfl⟩ : syracuseStep 5289533 = 1983575) (by norm_num)
theorem B3526355 : Blo 2089435 3526355 := bstep (se 1 (by rfl) ⟨2644766, by rfl⟩ : syracuseStep 3526355 = 5289533) B5289533
theorem B2350903 : Blo 2089435 2350903 := bstep (se 1 (by rfl) ⟨1763177, by rfl⟩ : syracuseStep 2350903 = 3526355) B3526355
theorem B3134537 : Blo 2089435 3134537 := bstep (se 2 (by rfl) ⟨1175451, by rfl⟩ : syracuseStep 3134537 = 2350903) B2350903
theorem B2089691 : Blo 2089435 2089691 := bstep (se 1 (by rfl) ⟨1567268, by rfl⟩ : syracuseStep 2089691 = 3134537) B3134537
theorem B3967157 : Blo 2089435 3967157 := bbase (se 5 (by rfl) ⟨185960, by rfl⟩ : syracuseStep 3967157 = 371921) (by norm_num)
theorem B10579085 : Blo 2089435 10579085 := bstep (se 3 (by rfl) ⟨1983578, by rfl⟩ : syracuseStep 10579085 = 3967157) B3967157
theorem B7052723 : Blo 2089435 7052723 := bstep (se 1 (by rfl) ⟨5289542, by rfl⟩ : syracuseStep 7052723 = 10579085) B10579085
theorem B4701815 : Blo 2089435 4701815 := bstep (se 1 (by rfl) ⟨3526361, by rfl⟩ : syracuseStep 4701815 = 7052723) B7052723
theorem B3134543 : Blo 2089435 3134543 := bstep (se 1 (by rfl) ⟨2350907, by rfl⟩ : syracuseStep 3134543 = 4701815) B4701815
theorem B2089695 : Blo 2089435 2089695 := bstep (se 1 (by rfl) ⟨1567271, by rfl⟩ : syracuseStep 2089695 = 3134543) B3134543
theorem B3134549 : Blo 2089435 3134549 := bbase (se 8 (by rfl) ⟨18366, by rfl⟩ : syracuseStep 3134549 = 36733) (by norm_num)
theorem B2089699 : Blo 2089435 2089699 := bstep (se 1 (by rfl) ⟨1567274, by rfl⟩ : syracuseStep 2089699 = 3134549) B3134549
theorem B4021301 : Blo 2089435 4021301 := bbase (se 5 (by rfl) ⟨188498, by rfl⟩ : syracuseStep 4021301 = 376997) (by norm_num)
theorem B2680867 : Blo 2089435 2680867 := bstep (se 1 (by rfl) ⟨2010650, by rfl⟩ : syracuseStep 2680867 = 4021301) B4021301
theorem B3574489 : Blo 2089435 3574489 := bstep (se 2 (by rfl) ⟨1340433, by rfl⟩ : syracuseStep 3574489 = 2680867) B2680867
theorem B4765985 : Blo 2089435 4765985 := bstep (se 2 (by rfl) ⟨1787244, by rfl⟩ : syracuseStep 4765985 = 3574489) B3574489
theorem B3177323 : Blo 2089435 3177323 := bstep (se 1 (by rfl) ⟨2382992, by rfl⟩ : syracuseStep 3177323 = 4765985) B4765985
theorem B2118215 : Blo 2089435 2118215 := bstep (se 1 (by rfl) ⟨1588661, by rfl⟩ : syracuseStep 2118215 = 3177323) B3177323
theorem B5648573 : Blo 2089435 5648573 := bstep (se 3 (by rfl) ⟨1059107, by rfl⟩ : syracuseStep 5648573 = 2118215) B2118215
theorem B15062861 : Blo 2089435 15062861 := bstep (se 3 (by rfl) ⟨2824286, by rfl⟩ : syracuseStep 15062861 = 5648573) B5648573
theorem B10041907 : Blo 2089435 10041907 := bstep (se 1 (by rfl) ⟨7531430, by rfl⟩ : syracuseStep 10041907 = 15062861) B15062861
theorem B13389209 : Blo 2089435 13389209 := bstep (se 2 (by rfl) ⟨5020953, by rfl⟩ : syracuseStep 13389209 = 10041907) B10041907
theorem B8926139 : Blo 2089435 8926139 := bstep (se 1 (by rfl) ⟨6694604, by rfl⟩ : syracuseStep 8926139 = 13389209) B13389209
theorem B5950759 : Blo 2089435 5950759 := bstep (se 1 (by rfl) ⟨4463069, by rfl⟩ : syracuseStep 5950759 = 8926139) B8926139
theorem B7934345 : Blo 2089435 7934345 := bstep (se 2 (by rfl) ⟨2975379, by rfl⟩ : syracuseStep 7934345 = 5950759) B5950759
theorem B5289563 : Blo 2089435 5289563 := bstep (se 1 (by rfl) ⟨3967172, by rfl⟩ : syracuseStep 5289563 = 7934345) B7934345
theorem B3526375 : Blo 2089435 3526375 := bstep (se 1 (by rfl) ⟨2644781, by rfl⟩ : syracuseStep 3526375 = 5289563) B5289563
theorem B4701833 : Blo 2089435 4701833 := bstep (se 2 (by rfl) ⟨1763187, by rfl⟩ : syracuseStep 4701833 = 3526375) B3526375
theorem B3134555 : Blo 2089435 3134555 := bstep (se 1 (by rfl) ⟨2350916, by rfl⟩ : syracuseStep 3134555 = 4701833) B4701833
theorem B2089703 : Blo 2089435 2089703 := bstep (se 1 (by rfl) ⟨1567277, by rfl⟩ : syracuseStep 2089703 = 3134555) B3134555
theorem B2350921 : Blo 2089435 2350921 := bbase (se 2 (by rfl) ⟨881595, by rfl⟩ : syracuseStep 2350921 = 1763191) (by norm_num)
theorem B3134561 : Blo 2089435 3134561 := bstep (se 2 (by rfl) ⟨1175460, by rfl⟩ : syracuseStep 3134561 = 2350921) B2350921
theorem B2089707 : Blo 2089435 2089707 := bstep (se 1 (by rfl) ⟨1567280, by rfl⟩ : syracuseStep 2089707 = 3134561) B3134561
theorem B2680877 : Blo 2089435 2680877 := bbase (se 3 (by rfl) ⟨502664, by rfl⟩ : syracuseStep 2680877 = 1005329) (by norm_num)
theorem B7149005 : Blo 2089435 7149005 := bstep (se 3 (by rfl) ⟨1340438, by rfl⟩ : syracuseStep 7149005 = 2680877) B2680877
theorem B4766003 : Blo 2089435 4766003 := bstep (se 1 (by rfl) ⟨3574502, by rfl⟩ : syracuseStep 4766003 = 7149005) B7149005
theorem B3177335 : Blo 2089435 3177335 := bstep (se 1 (by rfl) ⟨2383001, by rfl⟩ : syracuseStep 3177335 = 4766003) B4766003
theorem B2118223 : Blo 2089435 2118223 := bstep (se 1 (by rfl) ⟨1588667, by rfl⟩ : syracuseStep 2118223 = 3177335) B3177335
theorem B2824297 : Blo 2089435 2824297 := bstep (se 2 (by rfl) ⟨1059111, by rfl⟩ : syracuseStep 2824297 = 2118223) B2118223
theorem B15062917 : Blo 2089435 15062917 := bstep (se 4 (by rfl) ⟨1412148, by rfl⟩ : syracuseStep 15062917 = 2824297) B2824297
theorem B20083889 : Blo 2089435 20083889 := bstep (se 2 (by rfl) ⟨7531458, by rfl⟩ : syracuseStep 20083889 = 15062917) B15062917
theorem B13389259 : Blo 2089435 13389259 := bstep (se 1 (by rfl) ⟨10041944, by rfl⟩ : syracuseStep 13389259 = 20083889) B20083889
theorem B17852345 : Blo 2089435 17852345 := bstep (se 2 (by rfl) ⟨6694629, by rfl⟩ : syracuseStep 17852345 = 13389259) B13389259
theorem B11901563 : Blo 2089435 11901563 := bstep (se 1 (by rfl) ⟨8926172, by rfl⟩ : syracuseStep 11901563 = 17852345) B17852345
theorem B7934375 : Blo 2089435 7934375 := bstep (se 1 (by rfl) ⟨5950781, by rfl⟩ : syracuseStep 7934375 = 11901563) B11901563
theorem B5289583 : Blo 2089435 5289583 := bstep (se 1 (by rfl) ⟨3967187, by rfl⟩ : syracuseStep 5289583 = 7934375) B7934375
theorem B7052777 : Blo 2089435 7052777 := bstep (se 2 (by rfl) ⟨2644791, by rfl⟩ : syracuseStep 7052777 = 5289583) B5289583
theorem B4701851 : Blo 2089435 4701851 := bstep (se 1 (by rfl) ⟨3526388, by rfl⟩ : syracuseStep 4701851 = 7052777) B7052777
theorem B3134567 : Blo 2089435 3134567 := bstep (se 1 (by rfl) ⟨2350925, by rfl⟩ : syracuseStep 3134567 = 4701851) B4701851
theorem B2089711 : Blo 2089435 2089711 := bstep (se 1 (by rfl) ⟨1567283, by rfl⟩ : syracuseStep 2089711 = 3134567) B3134567
theorem B3134573 : Blo 2089435 3134573 := bbase (se 3 (by rfl) ⟨587732, by rfl⟩ : syracuseStep 3134573 = 1175465) (by norm_num)
theorem B2089715 : Blo 2089435 2089715 := bstep (se 1 (by rfl) ⟨1567286, by rfl⟩ : syracuseStep 2089715 = 3134573) B3134573
theorem B4701869 : Blo 2089435 4701869 := bbase (se 3 (by rfl) ⟨881600, by rfl⟩ : syracuseStep 4701869 = 1763201) (by norm_num)
theorem B3134579 : Blo 2089435 3134579 := bstep (se 1 (by rfl) ⟨2350934, by rfl⟩ : syracuseStep 3134579 = 4701869) B4701869
theorem B2089719 : Blo 2089435 2089719 := bstep (se 1 (by rfl) ⟨1567289, by rfl⟩ : syracuseStep 2089719 = 3134579) B3134579
theorem B5648629 : Blo 2089435 5648629 := bbase (se 5 (by rfl) ⟨264779, by rfl⟩ : syracuseStep 5648629 = 529559) (by norm_num)
theorem B7531505 : Blo 2089435 7531505 := bstep (se 2 (by rfl) ⟨2824314, by rfl⟩ : syracuseStep 7531505 = 5648629) B5648629
theorem B5021003 : Blo 2089435 5021003 := bstep (se 1 (by rfl) ⟨3765752, by rfl⟩ : syracuseStep 5021003 = 7531505) B7531505
theorem B3347335 : Blo 2089435 3347335 := bstep (se 1 (by rfl) ⟨2510501, by rfl⟩ : syracuseStep 3347335 = 5021003) B5021003
theorem B4463113 : Blo 2089435 4463113 := bstep (se 2 (by rfl) ⟨1673667, by rfl⟩ : syracuseStep 4463113 = 3347335) B3347335
theorem B5950817 : Blo 2089435 5950817 := bstep (se 2 (by rfl) ⟨2231556, by rfl⟩ : syracuseStep 5950817 = 4463113) B4463113
theorem B3967211 : Blo 2089435 3967211 := bstep (se 1 (by rfl) ⟨2975408, by rfl⟩ : syracuseStep 3967211 = 5950817) B5950817
theorem B2644807 : Blo 2089435 2644807 := bstep (se 1 (by rfl) ⟨1983605, by rfl⟩ : syracuseStep 2644807 = 3967211) B3967211
theorem B3526409 : Blo 2089435 3526409 := bstep (se 2 (by rfl) ⟨1322403, by rfl⟩ : syracuseStep 3526409 = 2644807) B2644807
theorem B2350939 : Blo 2089435 2350939 := bstep (se 1 (by rfl) ⟨1763204, by rfl⟩ : syracuseStep 2350939 = 3526409) B3526409
theorem B3134585 : Blo 2089435 3134585 := bstep (se 2 (by rfl) ⟨1175469, by rfl⟩ : syracuseStep 3134585 = 2350939) B2350939
theorem B2089723 : Blo 2089435 2089723 := bstep (se 1 (by rfl) ⟨1567292, by rfl⟩ : syracuseStep 2089723 = 3134585) B3134585
theorem B4524013 : Blo 2089435 4524013 := bbase (se 3 (by rfl) ⟨848252, by rfl⟩ : syracuseStep 4524013 = 1696505) (by norm_num)
theorem B6032017 : Blo 2089435 6032017 := bstep (se 2 (by rfl) ⟨2262006, by rfl⟩ : syracuseStep 6032017 = 4524013) B4524013
theorem B8042689 : Blo 2089435 8042689 := bstep (se 2 (by rfl) ⟨3016008, by rfl⟩ : syracuseStep 8042689 = 6032017) B6032017
theorem B10723585 : Blo 2089435 10723585 := bstep (se 2 (by rfl) ⟨4021344, by rfl⟩ : syracuseStep 10723585 = 8042689) B8042689
theorem B14298113 : Blo 2089435 14298113 := bstep (se 2 (by rfl) ⟨5361792, by rfl⟩ : syracuseStep 14298113 = 10723585) B10723585
theorem B9532075 : Blo 2089435 9532075 := bstep (se 1 (by rfl) ⟨7149056, by rfl⟩ : syracuseStep 9532075 = 14298113) B14298113
theorem B12709433 : Blo 2089435 12709433 := bstep (se 2 (by rfl) ⟨4766037, by rfl⟩ : syracuseStep 12709433 = 9532075) B9532075
theorem B33891821 : Blo 2089435 33891821 := bstep (se 3 (by rfl) ⟨6354716, by rfl⟩ : syracuseStep 33891821 = 12709433) B12709433
theorem B22594547 : Blo 2089435 22594547 := bstep (se 1 (by rfl) ⟨16945910, by rfl⟩ : syracuseStep 22594547 = 33891821) B33891821
theorem B15063031 : Blo 2089435 15063031 := bstep (se 1 (by rfl) ⟨11297273, by rfl⟩ : syracuseStep 15063031 = 22594547) B22594547
theorem B20084041 : Blo 2089435 20084041 := bstep (se 2 (by rfl) ⟨7531515, by rfl⟩ : syracuseStep 20084041 = 15063031) B15063031
theorem B26778721 : Blo 2089435 26778721 := bstep (se 2 (by rfl) ⟨10042020, by rfl⟩ : syracuseStep 26778721 = 20084041) B20084041
theorem B35704961 : Blo 2089435 35704961 := bstep (se 2 (by rfl) ⟨13389360, by rfl⟩ : syracuseStep 35704961 = 26778721) B26778721
theorem B23803307 : Blo 2089435 23803307 := bstep (se 1 (by rfl) ⟨17852480, by rfl⟩ : syracuseStep 23803307 = 35704961) B35704961
theorem B15868871 : Blo 2089435 15868871 := bstep (se 1 (by rfl) ⟨11901653, by rfl⟩ : syracuseStep 15868871 = 23803307) B23803307
theorem B10579247 : Blo 2089435 10579247 := bstep (se 1 (by rfl) ⟨7934435, by rfl⟩ : syracuseStep 10579247 = 15868871) B15868871
theorem B7052831 : Blo 2089435 7052831 := bstep (se 1 (by rfl) ⟨5289623, by rfl⟩ : syracuseStep 7052831 = 10579247) B10579247
theorem B4701887 : Blo 2089435 4701887 := bstep (se 1 (by rfl) ⟨3526415, by rfl⟩ : syracuseStep 4701887 = 7052831) B7052831
theorem B3134591 : Blo 2089435 3134591 := bstep (se 1 (by rfl) ⟨2350943, by rfl⟩ : syracuseStep 3134591 = 4701887) B4701887
theorem B2089727 : Blo 2089435 2089727 := bstep (se 1 (by rfl) ⟨1567295, by rfl⟩ : syracuseStep 2089727 = 3134591) B3134591
theorem B3134597 : Blo 2089435 3134597 := bbase (se 4 (by rfl) ⟨293868, by rfl⟩ : syracuseStep 3134597 = 587737) (by norm_num)
theorem B2089731 : Blo 2089435 2089731 := bstep (se 1 (by rfl) ⟨1567298, by rfl⟩ : syracuseStep 2089731 = 3134597) B3134597
theorem B3526429 : Blo 2089435 3526429 := bbase (se 3 (by rfl) ⟨661205, by rfl⟩ : syracuseStep 3526429 = 1322411) (by norm_num)
theorem B4701905 : Blo 2089435 4701905 := bstep (se 2 (by rfl) ⟨1763214, by rfl⟩ : syracuseStep 4701905 = 3526429) B3526429
theorem B3134603 : Blo 2089435 3134603 := bstep (se 1 (by rfl) ⟨2350952, by rfl⟩ : syracuseStep 3134603 = 4701905) B4701905
theorem B2089735 : Blo 2089435 2089735 := bstep (se 1 (by rfl) ⟨1567301, by rfl⟩ : syracuseStep 2089735 = 3134603) B3134603
theorem B2350957 : Blo 2089435 2350957 := bbase (se 3 (by rfl) ⟨440804, by rfl⟩ : syracuseStep 2350957 = 881609) (by norm_num)
theorem B3134609 : Blo 2089435 3134609 := bstep (se 2 (by rfl) ⟨1175478, by rfl⟩ : syracuseStep 3134609 = 2350957) B2350957
theorem B2089739 : Blo 2089435 2089739 := bstep (se 1 (by rfl) ⟨1567304, by rfl⟩ : syracuseStep 2089739 = 3134609) B3134609
theorem B7052885 : Blo 2089435 7052885 := bbase (se 8 (by rfl) ⟨41325, by rfl⟩ : syracuseStep 7052885 = 82651) (by norm_num)
theorem B4701923 : Blo 2089435 4701923 := bstep (se 1 (by rfl) ⟨3526442, by rfl⟩ : syracuseStep 4701923 = 7052885) B7052885
theorem B3134615 : Blo 2089435 3134615 := bstep (se 1 (by rfl) ⟨2350961, by rfl⟩ : syracuseStep 3134615 = 4701923) B4701923
theorem B2089743 : Blo 2089435 2089743 := bstep (se 1 (by rfl) ⟨1567307, by rfl⟩ : syracuseStep 2089743 = 3134615) B3134615
theorem B3134621 : Blo 2089435 3134621 := bbase (se 3 (by rfl) ⟨587741, by rfl⟩ : syracuseStep 3134621 = 1175483) (by norm_num)
theorem B2089747 : Blo 2089435 2089747 := bstep (se 1 (by rfl) ⟨1567310, by rfl⟩ : syracuseStep 2089747 = 3134621) B3134621
theorem B4701941 : Blo 2089435 4701941 := bbase (se 5 (by rfl) ⟨220403, by rfl⟩ : syracuseStep 4701941 = 440807) (by norm_num)
theorem B3134627 : Blo 2089435 3134627 := bstep (se 1 (by rfl) ⟨2350970, by rfl⟩ : syracuseStep 3134627 = 4701941) B4701941
theorem B2089751 : Blo 2089435 2089751 := bstep (se 1 (by rfl) ⟨1567313, by rfl⟩ : syracuseStep 2089751 = 3134627) B3134627
theorem B2824357 : Blo 2089435 2824357 := bbase (se 4 (by rfl) ⟨264783, by rfl⟩ : syracuseStep 2824357 = 529567) (by norm_num)
theorem B3765809 : Blo 2089435 3765809 := bstep (se 2 (by rfl) ⟨1412178, by rfl⟩ : syracuseStep 3765809 = 2824357) B2824357
theorem B10042157 : Blo 2089435 10042157 := bstep (se 3 (by rfl) ⟨1882904, by rfl⟩ : syracuseStep 10042157 = 3765809) B3765809
theorem B26779085 : Blo 2089435 26779085 := bstep (se 3 (by rfl) ⟨5021078, by rfl⟩ : syracuseStep 26779085 = 10042157) B10042157
theorem B17852723 : Blo 2089435 17852723 := bstep (se 1 (by rfl) ⟨13389542, by rfl⟩ : syracuseStep 17852723 = 26779085) B26779085
theorem B11901815 : Blo 2089435 11901815 := bstep (se 1 (by rfl) ⟨8926361, by rfl⟩ : syracuseStep 11901815 = 17852723) B17852723
theorem B7934543 : Blo 2089435 7934543 := bstep (se 1 (by rfl) ⟨5950907, by rfl⟩ : syracuseStep 7934543 = 11901815) B11901815
theorem B5289695 : Blo 2089435 5289695 := bstep (se 1 (by rfl) ⟨3967271, by rfl⟩ : syracuseStep 5289695 = 7934543) B7934543
theorem B3526463 : Blo 2089435 3526463 := bstep (se 1 (by rfl) ⟨2644847, by rfl⟩ : syracuseStep 3526463 = 5289695) B5289695
theorem B2350975 : Blo 2089435 2350975 := bstep (se 1 (by rfl) ⟨1763231, by rfl⟩ : syracuseStep 2350975 = 3526463) B3526463
theorem B3134633 : Blo 2089435 3134633 := bstep (se 2 (by rfl) ⟨1175487, by rfl⟩ : syracuseStep 3134633 = 2350975) B2350975
theorem B2089755 : Blo 2089435 2089755 := bstep (se 1 (by rfl) ⟨1567316, by rfl⟩ : syracuseStep 2089755 = 3134633) B3134633
theorem B4463189 : Blo 2089435 4463189 := bbase (se 8 (by rfl) ⟨26151, by rfl⟩ : syracuseStep 4463189 = 52303) (by norm_num)
theorem B2975459 : Blo 2089435 2975459 := bstep (se 1 (by rfl) ⟨2231594, by rfl⟩ : syracuseStep 2975459 = 4463189) B4463189
theorem B7934557 : Blo 2089435 7934557 := bstep (se 3 (by rfl) ⟨1487729, by rfl⟩ : syracuseStep 7934557 = 2975459) B2975459
theorem B10579409 : Blo 2089435 10579409 := bstep (se 2 (by rfl) ⟨3967278, by rfl⟩ : syracuseStep 10579409 = 7934557) B7934557
theorem B7052939 : Blo 2089435 7052939 := bstep (se 1 (by rfl) ⟨5289704, by rfl⟩ : syracuseStep 7052939 = 10579409) B10579409
theorem B4701959 : Blo 2089435 4701959 := bstep (se 1 (by rfl) ⟨3526469, by rfl⟩ : syracuseStep 4701959 = 7052939) B7052939
theorem B3134639 : Blo 2089435 3134639 := bstep (se 1 (by rfl) ⟨2350979, by rfl⟩ : syracuseStep 3134639 = 4701959) B4701959
theorem B2089759 : Blo 2089435 2089759 := bstep (se 1 (by rfl) ⟨1567319, by rfl⟩ : syracuseStep 2089759 = 3134639) B3134639
theorem B3134645 : Blo 2089435 3134645 := bbase (se 5 (by rfl) ⟨146936, by rfl⟩ : syracuseStep 3134645 = 293873) (by norm_num)
theorem B2089763 : Blo 2089435 2089763 := bstep (se 1 (by rfl) ⟨1567322, by rfl⟩ : syracuseStep 2089763 = 3134645) B3134645
theorem B5289725 : Blo 2089435 5289725 := bbase (se 3 (by rfl) ⟨991823, by rfl⟩ : syracuseStep 5289725 = 1983647) (by norm_num)
theorem B3526483 : Blo 2089435 3526483 := bstep (se 1 (by rfl) ⟨2644862, by rfl⟩ : syracuseStep 3526483 = 5289725) B5289725
theorem B4701977 : Blo 2089435 4701977 := bstep (se 2 (by rfl) ⟨1763241, by rfl⟩ : syracuseStep 4701977 = 3526483) B3526483
theorem B3134651 : Blo 2089435 3134651 := bstep (se 1 (by rfl) ⟨2350988, by rfl⟩ : syracuseStep 3134651 = 4701977) B4701977
theorem B2089767 : Blo 2089435 2089767 := bstep (se 1 (by rfl) ⟨1567325, by rfl⟩ : syracuseStep 2089767 = 3134651) B3134651
theorem B2350993 : Blo 2089435 2350993 := bbase (se 2 (by rfl) ⟨881622, by rfl⟩ : syracuseStep 2350993 = 1763245) (by norm_num)
theorem B3134657 : Blo 2089435 3134657 := bstep (se 2 (by rfl) ⟨1175496, by rfl⟩ : syracuseStep 3134657 = 2350993) B2350993
theorem B2089771 : Blo 2089435 2089771 := bstep (se 1 (by rfl) ⟨1567328, by rfl⟩ : syracuseStep 2089771 = 3134657) B3134657
theorem B3967309 : Blo 2089435 3967309 := bbase (se 3 (by rfl) ⟨743870, by rfl⟩ : syracuseStep 3967309 = 1487741) (by norm_num)
theorem B5289745 : Blo 2089435 5289745 := bstep (se 2 (by rfl) ⟨1983654, by rfl⟩ : syracuseStep 5289745 = 3967309) B3967309
theorem B7052993 : Blo 2089435 7052993 := bstep (se 2 (by rfl) ⟨2644872, by rfl⟩ : syracuseStep 7052993 = 5289745) B5289745
theorem B4701995 : Blo 2089435 4701995 := bstep (se 1 (by rfl) ⟨3526496, by rfl⟩ : syracuseStep 4701995 = 7052993) B7052993
theorem B3134663 : Blo 2089435 3134663 := bstep (se 1 (by rfl) ⟨2350997, by rfl⟩ : syracuseStep 3134663 = 4701995) B4701995
theorem B2089775 : Blo 2089435 2089775 := bstep (se 1 (by rfl) ⟨1567331, by rfl⟩ : syracuseStep 2089775 = 3134663) B3134663
theorem B3134669 : Blo 2089435 3134669 := bbase (se 3 (by rfl) ⟨587750, by rfl⟩ : syracuseStep 3134669 = 1175501) (by norm_num)
theorem B2089779 : Blo 2089435 2089779 := bstep (se 1 (by rfl) ⟨1567334, by rfl⟩ : syracuseStep 2089779 = 3134669) B3134669
theorem B4702013 : Blo 2089435 4702013 := bbase (se 3 (by rfl) ⟨881627, by rfl⟩ : syracuseStep 4702013 = 1763255) (by norm_num)
theorem B3134675 : Blo 2089435 3134675 := bstep (se 1 (by rfl) ⟨2351006, by rfl⟩ : syracuseStep 3134675 = 4702013) B4702013
theorem B2089783 : Blo 2089435 2089783 := bstep (se 1 (by rfl) ⟨1567337, by rfl⟩ : syracuseStep 2089783 = 3134675) B3134675
theorem B3526517 : Blo 2089435 3526517 := bbase (se 5 (by rfl) ⟨165305, by rfl⟩ : syracuseStep 3526517 = 330611) (by norm_num)
theorem B2351011 : Blo 2089435 2351011 := bstep (se 1 (by rfl) ⟨1763258, by rfl⟩ : syracuseStep 2351011 = 3526517) B3526517
theorem B3134681 : Blo 2089435 3134681 := bstep (se 2 (by rfl) ⟨1175505, by rfl⟩ : syracuseStep 3134681 = 2351011) B2351011
theorem B2089787 : Blo 2089435 2089787 := bstep (se 1 (by rfl) ⟨1567340, by rfl⟩ : syracuseStep 2089787 = 3134681) B3134681
theorem B5021165 : Blo 2089435 5021165 := bbase (se 3 (by rfl) ⟨941468, by rfl⟩ : syracuseStep 5021165 = 1882937) (by norm_num)
theorem B3347443 : Blo 2089435 3347443 := bstep (se 1 (by rfl) ⟨2510582, by rfl⟩ : syracuseStep 3347443 = 5021165) B5021165
theorem B4463257 : Blo 2089435 4463257 := bstep (se 2 (by rfl) ⟨1673721, by rfl⟩ : syracuseStep 4463257 = 3347443) B3347443
theorem B5951009 : Blo 2089435 5951009 := bstep (se 2 (by rfl) ⟨2231628, by rfl⟩ : syracuseStep 5951009 = 4463257) B4463257
theorem B15869357 : Blo 2089435 15869357 := bstep (se 3 (by rfl) ⟨2975504, by rfl⟩ : syracuseStep 15869357 = 5951009) B5951009
theorem B10579571 : Blo 2089435 10579571 := bstep (se 1 (by rfl) ⟨7934678, by rfl⟩ : syracuseStep 10579571 = 15869357) B15869357
theorem B7053047 : Blo 2089435 7053047 := bstep (se 1 (by rfl) ⟨5289785, by rfl⟩ : syracuseStep 7053047 = 10579571) B10579571
theorem B4702031 : Blo 2089435 4702031 := bstep (se 1 (by rfl) ⟨3526523, by rfl⟩ : syracuseStep 4702031 = 7053047) B7053047
theorem B3134687 : Blo 2089435 3134687 := bstep (se 1 (by rfl) ⟨2351015, by rfl⟩ : syracuseStep 3134687 = 4702031) B4702031
theorem B2089791 : Blo 2089435 2089791 := bstep (se 1 (by rfl) ⟨1567343, by rfl⟩ : syracuseStep 2089791 = 3134687) B3134687
theorem B3134693 : Blo 2089435 3134693 := bbase (se 4 (by rfl) ⟨293877, by rfl⟩ : syracuseStep 3134693 = 587755) (by norm_num)
theorem B2089795 : Blo 2089435 2089795 := bstep (se 1 (by rfl) ⟨1567346, by rfl⟩ : syracuseStep 2089795 = 3134693) B3134693
theorem B2118313 : Blo 2089435 2118313 := bbase (se 2 (by rfl) ⟨794367, by rfl⟩ : syracuseStep 2118313 = 1588735) (by norm_num)
theorem B2824417 : Blo 2089435 2824417 := bstep (se 2 (by rfl) ⟨1059156, by rfl⟩ : syracuseStep 2824417 = 2118313) B2118313
theorem B3765889 : Blo 2089435 3765889 := bstep (se 2 (by rfl) ⟨1412208, by rfl⟩ : syracuseStep 3765889 = 2824417) B2824417
theorem B5021185 : Blo 2089435 5021185 := bstep (se 2 (by rfl) ⟨1882944, by rfl⟩ : syracuseStep 5021185 = 3765889) B3765889
theorem B6694913 : Blo 2089435 6694913 := bstep (se 2 (by rfl) ⟨2510592, by rfl⟩ : syracuseStep 6694913 = 5021185) B5021185
theorem B4463275 : Blo 2089435 4463275 := bstep (se 1 (by rfl) ⟨3347456, by rfl⟩ : syracuseStep 4463275 = 6694913) B6694913
theorem B5951033 : Blo 2089435 5951033 := bstep (se 2 (by rfl) ⟨2231637, by rfl⟩ : syracuseStep 5951033 = 4463275) B4463275
theorem B3967355 : Blo 2089435 3967355 := bstep (se 1 (by rfl) ⟨2975516, by rfl⟩ : syracuseStep 3967355 = 5951033) B5951033
theorem B2644903 : Blo 2089435 2644903 := bstep (se 1 (by rfl) ⟨1983677, by rfl⟩ : syracuseStep 2644903 = 3967355) B3967355
theorem B3526537 : Blo 2089435 3526537 := bstep (se 2 (by rfl) ⟨1322451, by rfl⟩ : syracuseStep 3526537 = 2644903) B2644903
theorem B4702049 : Blo 2089435 4702049 := bstep (se 2 (by rfl) ⟨1763268, by rfl⟩ : syracuseStep 4702049 = 3526537) B3526537
theorem B3134699 : Blo 2089435 3134699 := bstep (se 1 (by rfl) ⟨2351024, by rfl⟩ : syracuseStep 3134699 = 4702049) B4702049
theorem B2089799 : Blo 2089435 2089799 := bstep (se 1 (by rfl) ⟨1567349, by rfl⟩ : syracuseStep 2089799 = 3134699) B3134699
theorem B2351029 : Blo 2089435 2351029 := bbase (se 5 (by rfl) ⟨110204, by rfl⟩ : syracuseStep 2351029 = 220409) (by norm_num)
theorem B3134705 : Blo 2089435 3134705 := bstep (se 2 (by rfl) ⟨1175514, by rfl⟩ : syracuseStep 3134705 = 2351029) B2351029
theorem B2089803 : Blo 2089435 2089803 := bstep (se 1 (by rfl) ⟨1567352, by rfl⟩ : syracuseStep 2089803 = 3134705) B3134705
theorem B2644913 : Blo 2089435 2644913 := bbase (se 2 (by rfl) ⟨991842, by rfl⟩ : syracuseStep 2644913 = 1983685) (by norm_num)
theorem B7053101 : Blo 2089435 7053101 := bstep (se 3 (by rfl) ⟨1322456, by rfl⟩ : syracuseStep 7053101 = 2644913) B2644913
theorem B4702067 : Blo 2089435 4702067 := bstep (se 1 (by rfl) ⟨3526550, by rfl⟩ : syracuseStep 4702067 = 7053101) B7053101
theorem B3134711 : Blo 2089435 3134711 := bstep (se 1 (by rfl) ⟨2351033, by rfl⟩ : syracuseStep 3134711 = 4702067) B4702067
theorem B2089807 : Blo 2089435 2089807 := bstep (se 1 (by rfl) ⟨1567355, by rfl⟩ : syracuseStep 2089807 = 3134711) B3134711
theorem B3134717 : Blo 2089435 3134717 := bbase (se 3 (by rfl) ⟨587759, by rfl⟩ : syracuseStep 3134717 = 1175519) (by norm_num)
theorem B2089811 : Blo 2089435 2089811 := bstep (se 1 (by rfl) ⟨1567358, by rfl⟩ : syracuseStep 2089811 = 3134717) B3134717
theorem B4702085 : Blo 2089435 4702085 := bbase (se 4 (by rfl) ⟨440820, by rfl⟩ : syracuseStep 4702085 = 881641) (by norm_num)
theorem B3134723 : Blo 2089435 3134723 := bstep (se 1 (by rfl) ⟨2351042, by rfl⟩ : syracuseStep 3134723 = 4702085) B4702085
theorem B2089815 : Blo 2089435 2089815 := bstep (se 1 (by rfl) ⟨1567361, by rfl⟩ : syracuseStep 2089815 = 3134723) B3134723
theorem B2510617 : Blo 2089435 2510617 := bbase (se 2 (by rfl) ⟨941481, by rfl⟩ : syracuseStep 2510617 = 1882963) (by norm_num)
theorem B3347489 : Blo 2089435 3347489 := bstep (se 2 (by rfl) ⟨1255308, by rfl⟩ : syracuseStep 3347489 = 2510617) B2510617
theorem B2231659 : Blo 2089435 2231659 := bstep (se 1 (by rfl) ⟨1673744, by rfl⟩ : syracuseStep 2231659 = 3347489) B3347489
theorem B2975545 : Blo 2089435 2975545 := bstep (se 2 (by rfl) ⟨1115829, by rfl⟩ : syracuseStep 2975545 = 2231659) B2231659
theorem B3967393 : Blo 2089435 3967393 := bstep (se 2 (by rfl) ⟨1487772, by rfl⟩ : syracuseStep 3967393 = 2975545) B2975545
theorem B5289857 : Blo 2089435 5289857 := bstep (se 2 (by rfl) ⟨1983696, by rfl⟩ : syracuseStep 5289857 = 3967393) B3967393
theorem B3526571 : Blo 2089435 3526571 := bstep (se 1 (by rfl) ⟨2644928, by rfl⟩ : syracuseStep 3526571 = 5289857) B5289857
theorem B2351047 : Blo 2089435 2351047 := bstep (se 1 (by rfl) ⟨1763285, by rfl⟩ : syracuseStep 2351047 = 3526571) B3526571
theorem B3134729 : Blo 2089435 3134729 := bstep (se 2 (by rfl) ⟨1175523, by rfl⟩ : syracuseStep 3134729 = 2351047) B2351047
theorem B2089819 : Blo 2089435 2089819 := bstep (se 1 (by rfl) ⟨1567364, by rfl⟩ : syracuseStep 2089819 = 3134729) B3134729
theorem B10579733 : Blo 2089435 10579733 := bbase (se 6 (by rfl) ⟨247962, by rfl⟩ : syracuseStep 10579733 = 495925) (by norm_num)
theorem B7053155 : Blo 2089435 7053155 := bstep (se 1 (by rfl) ⟨5289866, by rfl⟩ : syracuseStep 7053155 = 10579733) B10579733
theorem B4702103 : Blo 2089435 4702103 := bstep (se 1 (by rfl) ⟨3526577, by rfl⟩ : syracuseStep 4702103 = 7053155) B7053155
theorem B3134735 : Blo 2089435 3134735 := bstep (se 1 (by rfl) ⟨2351051, by rfl⟩ : syracuseStep 3134735 = 4702103) B4702103
theorem B2089823 : Blo 2089435 2089823 := bstep (se 1 (by rfl) ⟨1567367, by rfl⟩ : syracuseStep 2089823 = 3134735) B3134735
theorem B3134741 : Blo 2089435 3134741 := bbase (se 6 (by rfl) ⟨73470, by rfl⟩ : syracuseStep 3134741 = 146941) (by norm_num)
theorem B2089827 : Blo 2089435 2089827 := bstep (se 1 (by rfl) ⟨1567370, by rfl⟩ : syracuseStep 2089827 = 3134741) B3134741
theorem B3177517 : Blo 2089435 3177517 := bbase (se 3 (by rfl) ⟨595784, by rfl⟩ : syracuseStep 3177517 = 1191569) (by norm_num)
theorem B4236689 : Blo 2089435 4236689 := bstep (se 2 (by rfl) ⟨1588758, by rfl⟩ : syracuseStep 4236689 = 3177517) B3177517
theorem B11297837 : Blo 2089435 11297837 := bstep (se 3 (by rfl) ⟨2118344, by rfl⟩ : syracuseStep 11297837 = 4236689) B4236689
theorem B30127565 : Blo 2089435 30127565 := bstep (se 3 (by rfl) ⟨5648918, by rfl⟩ : syracuseStep 30127565 = 11297837) B11297837
theorem B20085043 : Blo 2089435 20085043 := bstep (se 1 (by rfl) ⟨15063782, by rfl⟩ : syracuseStep 20085043 = 30127565) B30127565
theorem B26780057 : Blo 2089435 26780057 := bstep (se 2 (by rfl) ⟨10042521, by rfl⟩ : syracuseStep 26780057 = 20085043) B20085043
theorem B17853371 : Blo 2089435 17853371 := bstep (se 1 (by rfl) ⟨13390028, by rfl⟩ : syracuseStep 17853371 = 26780057) B26780057
theorem B11902247 : Blo 2089435 11902247 := bstep (se 1 (by rfl) ⟨8926685, by rfl⟩ : syracuseStep 11902247 = 17853371) B17853371
theorem B7934831 : Blo 2089435 7934831 := bstep (se 1 (by rfl) ⟨5951123, by rfl⟩ : syracuseStep 7934831 = 11902247) B11902247
theorem B5289887 : Blo 2089435 5289887 := bstep (se 1 (by rfl) ⟨3967415, by rfl⟩ : syracuseStep 5289887 = 7934831) B7934831
theorem B3526591 : Blo 2089435 3526591 := bstep (se 1 (by rfl) ⟨2644943, by rfl⟩ : syracuseStep 3526591 = 5289887) B5289887
theorem B4702121 : Blo 2089435 4702121 := bstep (se 2 (by rfl) ⟨1763295, by rfl⟩ : syracuseStep 4702121 = 3526591) B3526591
theorem B3134747 : Blo 2089435 3134747 := bstep (se 1 (by rfl) ⟨2351060, by rfl⟩ : syracuseStep 3134747 = 4702121) B4702121
theorem B2089831 : Blo 2089435 2089831 := bstep (se 1 (by rfl) ⟨1567373, by rfl⟩ : syracuseStep 2089831 = 3134747) B3134747
theorem B2351065 : Blo 2089435 2351065 := bbase (se 2 (by rfl) ⟨881649, by rfl⟩ : syracuseStep 2351065 = 1763299) (by norm_num)
theorem B3134753 : Blo 2089435 3134753 := bstep (se 2 (by rfl) ⟨1175532, by rfl⟩ : syracuseStep 3134753 = 2351065) B2351065
theorem B2089835 : Blo 2089435 2089835 := bstep (se 1 (by rfl) ⟨1567376, by rfl⟩ : syracuseStep 2089835 = 3134753) B3134753
theorem B2975573 : Blo 2089435 2975573 := bbase (se 9 (by rfl) ⟨8717, by rfl⟩ : syracuseStep 2975573 = 17435) (by norm_num)
theorem B7934861 : Blo 2089435 7934861 := bstep (se 3 (by rfl) ⟨1487786, by rfl⟩ : syracuseStep 7934861 = 2975573) B2975573
theorem B5289907 : Blo 2089435 5289907 := bstep (se 1 (by rfl) ⟨3967430, by rfl⟩ : syracuseStep 5289907 = 7934861) B7934861
theorem B7053209 : Blo 2089435 7053209 := bstep (se 2 (by rfl) ⟨2644953, by rfl⟩ : syracuseStep 7053209 = 5289907) B5289907
theorem B4702139 : Blo 2089435 4702139 := bstep (se 1 (by rfl) ⟨3526604, by rfl⟩ : syracuseStep 4702139 = 7053209) B7053209
theorem B3134759 : Blo 2089435 3134759 := bstep (se 1 (by rfl) ⟨2351069, by rfl⟩ : syracuseStep 3134759 = 4702139) B4702139
theorem B2089839 : Blo 2089435 2089839 := bstep (se 1 (by rfl) ⟨1567379, by rfl⟩ : syracuseStep 2089839 = 3134759) B3134759
theorem B3134765 : Blo 2089435 3134765 := bbase (se 3 (by rfl) ⟨587768, by rfl⟩ : syracuseStep 3134765 = 1175537) (by norm_num)
theorem B2089843 : Blo 2089435 2089843 := bstep (se 1 (by rfl) ⟨1567382, by rfl⟩ : syracuseStep 2089843 = 3134765) B3134765
theorem B4702157 : Blo 2089435 4702157 := bbase (se 3 (by rfl) ⟨881654, by rfl⟩ : syracuseStep 4702157 = 1763309) (by norm_num)
theorem B3134771 : Blo 2089435 3134771 := bstep (se 1 (by rfl) ⟨2351078, by rfl⟩ : syracuseStep 3134771 = 4702157) B4702157
theorem B2089847 : Blo 2089435 2089847 := bstep (se 1 (by rfl) ⟨1567385, by rfl⟩ : syracuseStep 2089847 = 3134771) B3134771
theorem B2644969 : Blo 2089435 2644969 := bbase (se 2 (by rfl) ⟨991863, by rfl⟩ : syracuseStep 2644969 = 1983727) (by norm_num)
theorem B3526625 : Blo 2089435 3526625 := bstep (se 2 (by rfl) ⟨1322484, by rfl⟩ : syracuseStep 3526625 = 2644969) B2644969
theorem B2351083 : Blo 2089435 2351083 := bstep (se 1 (by rfl) ⟨1763312, by rfl⟩ : syracuseStep 2351083 = 3526625) B3526625
theorem B3134777 : Blo 2089435 3134777 := bstep (se 2 (by rfl) ⟨1175541, by rfl⟩ : syracuseStep 3134777 = 2351083) B2351083
theorem B2089851 : Blo 2089435 2089851 := bstep (se 1 (by rfl) ⟨1567388, by rfl⟩ : syracuseStep 2089851 = 3134777) B3134777
theorem B3765989 : Blo 2089435 3765989 := bbase (se 4 (by rfl) ⟨353061, by rfl⟩ : syracuseStep 3765989 = 706123) (by norm_num)
theorem B2510659 : Blo 2089435 2510659 := bstep (se 1 (by rfl) ⟨1882994, by rfl⟩ : syracuseStep 2510659 = 3765989) B3765989
theorem B13390181 : Blo 2089435 13390181 := bstep (se 4 (by rfl) ⟨1255329, by rfl⟩ : syracuseStep 13390181 = 2510659) B2510659
theorem B8926787 : Blo 2089435 8926787 := bstep (se 1 (by rfl) ⟨6695090, by rfl⟩ : syracuseStep 8926787 = 13390181) B13390181
theorem B23804765 : Blo 2089435 23804765 := bstep (se 3 (by rfl) ⟨4463393, by rfl⟩ : syracuseStep 23804765 = 8926787) B8926787
theorem B15869843 : Blo 2089435 15869843 := bstep (se 1 (by rfl) ⟨11902382, by rfl⟩ : syracuseStep 15869843 = 23804765) B23804765
theorem B10579895 : Blo 2089435 10579895 := bstep (se 1 (by rfl) ⟨7934921, by rfl⟩ : syracuseStep 10579895 = 15869843) B15869843
theorem B7053263 : Blo 2089435 7053263 := bstep (se 1 (by rfl) ⟨5289947, by rfl⟩ : syracuseStep 7053263 = 10579895) B10579895
theorem B4702175 : Blo 2089435 4702175 := bstep (se 1 (by rfl) ⟨3526631, by rfl⟩ : syracuseStep 4702175 = 7053263) B7053263
theorem B3134783 : Blo 2089435 3134783 := bstep (se 1 (by rfl) ⟨2351087, by rfl⟩ : syracuseStep 3134783 = 4702175) B4702175
theorem B2089855 : Blo 2089435 2089855 := bstep (se 1 (by rfl) ⟨1567391, by rfl⟩ : syracuseStep 2089855 = 3134783) B3134783
theorem B3134789 : Blo 2089435 3134789 := bbase (se 4 (by rfl) ⟨293886, by rfl⟩ : syracuseStep 3134789 = 587773) (by norm_num)
theorem B2089859 : Blo 2089435 2089859 := bstep (se 1 (by rfl) ⟨1567394, by rfl⟩ : syracuseStep 2089859 = 3134789) B3134789
theorem B3526645 : Blo 2089435 3526645 := bbase (se 5 (by rfl) ⟨165311, by rfl⟩ : syracuseStep 3526645 = 330623) (by norm_num)
theorem B4702193 : Blo 2089435 4702193 := bstep (se 2 (by rfl) ⟨1763322, by rfl⟩ : syracuseStep 4702193 = 3526645) B3526645
theorem B3134795 : Blo 2089435 3134795 := bstep (se 1 (by rfl) ⟨2351096, by rfl⟩ : syracuseStep 3134795 = 4702193) B4702193
theorem B2089863 : Blo 2089435 2089863 := bstep (se 1 (by rfl) ⟨1567397, by rfl⟩ : syracuseStep 2089863 = 3134795) B3134795
theorem B2351101 : Blo 2089435 2351101 := bbase (se 3 (by rfl) ⟨440831, by rfl⟩ : syracuseStep 2351101 = 881663) (by norm_num)
theorem B3134801 : Blo 2089435 3134801 := bstep (se 2 (by rfl) ⟨1175550, by rfl⟩ : syracuseStep 3134801 = 2351101) B2351101
theorem B2089867 : Blo 2089435 2089867 := bstep (se 1 (by rfl) ⟨1567400, by rfl⟩ : syracuseStep 2089867 = 3134801) B3134801
theorem B7053317 : Blo 2089435 7053317 := bbase (se 4 (by rfl) ⟨661248, by rfl⟩ : syracuseStep 7053317 = 1322497) (by norm_num)
theorem B4702211 : Blo 2089435 4702211 := bstep (se 1 (by rfl) ⟨3526658, by rfl⟩ : syracuseStep 4702211 = 7053317) B7053317
theorem B3134807 : Blo 2089435 3134807 := bstep (se 1 (by rfl) ⟨2351105, by rfl⟩ : syracuseStep 3134807 = 4702211) B4702211
theorem B2089871 : Blo 2089435 2089871 := bstep (se 1 (by rfl) ⟨1567403, by rfl⟩ : syracuseStep 2089871 = 3134807) B3134807
theorem B3134813 : Blo 2089435 3134813 := bbase (se 3 (by rfl) ⟨587777, by rfl⟩ : syracuseStep 3134813 = 1175555) (by norm_num)
theorem B2089875 : Blo 2089435 2089875 := bstep (se 1 (by rfl) ⟨1567406, by rfl⟩ : syracuseStep 2089875 = 3134813) B3134813
theorem B4702229 : Blo 2089435 4702229 := bbase (se 6 (by rfl) ⟨110208, by rfl⟩ : syracuseStep 4702229 = 220417) (by norm_num)
theorem B3134819 : Blo 2089435 3134819 := bstep (se 1 (by rfl) ⟨2351114, by rfl⟩ : syracuseStep 3134819 = 4702229) B4702229
theorem B2089879 : Blo 2089435 2089879 := bstep (se 1 (by rfl) ⟨1567409, by rfl⟩ : syracuseStep 2089879 = 3134819) B3134819
theorem B7935029 : Blo 2089435 7935029 := bbase (se 5 (by rfl) ⟨371954, by rfl⟩ : syracuseStep 7935029 = 743909) (by norm_num)
theorem B5290019 : Blo 2089435 5290019 := bstep (se 1 (by rfl) ⟨3967514, by rfl⟩ : syracuseStep 5290019 = 7935029) B7935029
theorem B3526679 : Blo 2089435 3526679 := bstep (se 1 (by rfl) ⟨2645009, by rfl⟩ : syracuseStep 3526679 = 5290019) B5290019
theorem B2351119 : Blo 2089435 2351119 := bstep (se 1 (by rfl) ⟨1763339, by rfl⟩ : syracuseStep 2351119 = 3526679) B3526679
theorem B3134825 : Blo 2089435 3134825 := bstep (se 2 (by rfl) ⟨1175559, by rfl⟩ : syracuseStep 3134825 = 2351119) B2351119
theorem B2089883 : Blo 2089435 2089883 := bstep (se 1 (by rfl) ⟨1567412, by rfl⟩ : syracuseStep 2089883 = 3134825) B3134825
theorem B3347597 : Blo 2089435 3347597 := bbase (se 3 (by rfl) ⟨627674, by rfl⟩ : syracuseStep 3347597 = 1255349) (by norm_num)
theorem B2231731 : Blo 2089435 2231731 := bstep (se 1 (by rfl) ⟨1673798, by rfl⟩ : syracuseStep 2231731 = 3347597) B3347597
theorem B11902565 : Blo 2089435 11902565 := bstep (se 4 (by rfl) ⟨1115865, by rfl⟩ : syracuseStep 11902565 = 2231731) B2231731
theorem B7935043 : Blo 2089435 7935043 := bstep (se 1 (by rfl) ⟨5951282, by rfl⟩ : syracuseStep 7935043 = 11902565) B11902565
theorem B10580057 : Blo 2089435 10580057 := bstep (se 2 (by rfl) ⟨3967521, by rfl⟩ : syracuseStep 10580057 = 7935043) B7935043
theorem B7053371 : Blo 2089435 7053371 := bstep (se 1 (by rfl) ⟨5290028, by rfl⟩ : syracuseStep 7053371 = 10580057) B10580057
theorem B4702247 : Blo 2089435 4702247 := bstep (se 1 (by rfl) ⟨3526685, by rfl⟩ : syracuseStep 4702247 = 7053371) B7053371
theorem B3134831 : Blo 2089435 3134831 := bstep (se 1 (by rfl) ⟨2351123, by rfl⟩ : syracuseStep 3134831 = 4702247) B4702247
theorem B2089887 : Blo 2089435 2089887 := bstep (se 1 (by rfl) ⟨1567415, by rfl⟩ : syracuseStep 2089887 = 3134831) B3134831
theorem B3134837 : Blo 2089435 3134837 := bbase (se 5 (by rfl) ⟨146945, by rfl⟩ : syracuseStep 3134837 = 293891) (by norm_num)
theorem B2089891 : Blo 2089435 2089891 := bstep (se 1 (by rfl) ⟨1567418, by rfl⟩ : syracuseStep 2089891 = 3134837) B3134837
theorem B2975653 : Blo 2089435 2975653 := bbase (se 4 (by rfl) ⟨278967, by rfl⟩ : syracuseStep 2975653 = 557935) (by norm_num)
theorem B3967537 : Blo 2089435 3967537 := bstep (se 2 (by rfl) ⟨1487826, by rfl⟩ : syracuseStep 3967537 = 2975653) B2975653
theorem B5290049 : Blo 2089435 5290049 := bstep (se 2 (by rfl) ⟨1983768, by rfl⟩ : syracuseStep 5290049 = 3967537) B3967537
theorem B3526699 : Blo 2089435 3526699 := bstep (se 1 (by rfl) ⟨2645024, by rfl⟩ : syracuseStep 3526699 = 5290049) B5290049
theorem B4702265 : Blo 2089435 4702265 := bstep (se 2 (by rfl) ⟨1763349, by rfl⟩ : syracuseStep 4702265 = 3526699) B3526699
theorem B3134843 : Blo 2089435 3134843 := bstep (se 1 (by rfl) ⟨2351132, by rfl⟩ : syracuseStep 3134843 = 4702265) B4702265
theorem B2089895 : Blo 2089435 2089895 := bstep (se 1 (by rfl) ⟨1567421, by rfl⟩ : syracuseStep 2089895 = 3134843) B3134843
theorem B2351137 : Blo 2089435 2351137 := bbase (se 2 (by rfl) ⟨881676, by rfl⟩ : syracuseStep 2351137 = 1763353) (by norm_num)
theorem B3134849 : Blo 2089435 3134849 := bstep (se 2 (by rfl) ⟨1175568, by rfl⟩ : syracuseStep 3134849 = 2351137) B2351137
theorem B2089899 : Blo 2089435 2089899 := bstep (se 1 (by rfl) ⟨1567424, by rfl⟩ : syracuseStep 2089899 = 3134849) B3134849
theorem B5290069 : Blo 2089435 5290069 := bbase (se 8 (by rfl) ⟨30996, by rfl⟩ : syracuseStep 5290069 = 61993) (by norm_num)
theorem B7053425 : Blo 2089435 7053425 := bstep (se 2 (by rfl) ⟨2645034, by rfl⟩ : syracuseStep 7053425 = 5290069) B5290069
theorem B4702283 : Blo 2089435 4702283 := bstep (se 1 (by rfl) ⟨3526712, by rfl⟩ : syracuseStep 4702283 = 7053425) B7053425
theorem B3134855 : Blo 2089435 3134855 := bstep (se 1 (by rfl) ⟨2351141, by rfl⟩ : syracuseStep 3134855 = 4702283) B4702283
theorem B2089903 : Blo 2089435 2089903 := bstep (se 1 (by rfl) ⟨1567427, by rfl⟩ : syracuseStep 2089903 = 3134855) B3134855
theorem B3134861 : Blo 2089435 3134861 := bbase (se 3 (by rfl) ⟨587786, by rfl⟩ : syracuseStep 3134861 = 1175573) (by norm_num)
theorem B2089907 : Blo 2089435 2089907 := bstep (se 1 (by rfl) ⟨1567430, by rfl⟩ : syracuseStep 2089907 = 3134861) B3134861
theorem B4702301 : Blo 2089435 4702301 := bbase (se 3 (by rfl) ⟨881681, by rfl⟩ : syracuseStep 4702301 = 1763363) (by norm_num)
theorem B3134867 : Blo 2089435 3134867 := bstep (se 1 (by rfl) ⟨2351150, by rfl⟩ : syracuseStep 3134867 = 4702301) B4702301
theorem B2089911 : Blo 2089435 2089911 := bstep (se 1 (by rfl) ⟨1567433, by rfl⟩ : syracuseStep 2089911 = 3134867) B3134867
theorem B3526733 : Blo 2089435 3526733 := bbase (se 3 (by rfl) ⟨661262, by rfl⟩ : syracuseStep 3526733 = 1322525) (by norm_num)
theorem B2351155 : Blo 2089435 2351155 := bstep (se 1 (by rfl) ⟨1763366, by rfl⟩ : syracuseStep 2351155 = 3526733) B3526733
theorem B3134873 : Blo 2089435 3134873 := bstep (se 2 (by rfl) ⟨1175577, by rfl⟩ : syracuseStep 3134873 = 2351155) B2351155
theorem B2089915 : Blo 2089435 2089915 := bstep (se 1 (by rfl) ⟨1567436, by rfl⟩ : syracuseStep 2089915 = 3134873) B3134873
theorem B2176633 : Blo 2089435 2176633 := bbase (se 2 (by rfl) ⟨816237, by rfl⟩ : syracuseStep 2176633 = 1632475) (by norm_num)
theorem B2902177 : Blo 2089435 2902177 := bstep (se 2 (by rfl) ⟨1088316, by rfl⟩ : syracuseStep 2902177 = 2176633) B2176633
theorem B15478277 : Blo 2089435 15478277 := bstep (se 4 (by rfl) ⟨1451088, by rfl⟩ : syracuseStep 15478277 = 2902177) B2902177
theorem B41275405 : Blo 2089435 41275405 := bstep (se 3 (by rfl) ⟨7739138, by rfl⟩ : syracuseStep 41275405 = 15478277) B15478277
theorem B55033873 : Blo 2089435 55033873 := bstep (se 2 (by rfl) ⟨20637702, by rfl⟩ : syracuseStep 55033873 = 41275405) B41275405
theorem B293513989 : Blo 2089435 293513989 := bstep (se 4 (by rfl) ⟨27516936, by rfl⟩ : syracuseStep 293513989 = 55033873) B55033873
theorem B391351985 : Blo 2089435 391351985 := bstep (se 2 (by rfl) ⟨146756994, by rfl⟩ : syracuseStep 391351985 = 293513989) B293513989
theorem B260901323 : Blo 2089435 260901323 := bstep (se 1 (by rfl) ⟨195675992, by rfl⟩ : syracuseStep 260901323 = 391351985) B391351985
theorem B173934215 : Blo 2089435 173934215 := bstep (se 1 (by rfl) ⟨130450661, by rfl⟩ : syracuseStep 173934215 = 260901323) B260901323
theorem B115956143 : Blo 2089435 115956143 := bstep (se 1 (by rfl) ⟨86967107, by rfl⟩ : syracuseStep 115956143 = 173934215) B173934215
theorem B77304095 : Blo 2089435 77304095 := bstep (se 1 (by rfl) ⟨57978071, by rfl⟩ : syracuseStep 77304095 = 115956143) B115956143
theorem B51536063 : Blo 2089435 51536063 := bstep (se 1 (by rfl) ⟨38652047, by rfl⟩ : syracuseStep 51536063 = 77304095) B77304095
theorem B34357375 : Blo 2089435 34357375 := bstep (se 1 (by rfl) ⟨25768031, by rfl⟩ : syracuseStep 34357375 = 51536063) B51536063
theorem B45809833 : Blo 2089435 45809833 := bstep (se 2 (by rfl) ⟨17178687, by rfl⟩ : syracuseStep 45809833 = 34357375) B34357375
theorem B61079777 : Blo 2089435 61079777 := bstep (se 2 (by rfl) ⟨22904916, by rfl⟩ : syracuseStep 61079777 = 45809833) B45809833
theorem B40719851 : Blo 2089435 40719851 := bstep (se 1 (by rfl) ⟨30539888, by rfl⟩ : syracuseStep 40719851 = 61079777) B61079777
theorem B27146567 : Blo 2089435 27146567 := bstep (se 1 (by rfl) ⟨20359925, by rfl⟩ : syracuseStep 27146567 = 40719851) B40719851
theorem B72390845 : Blo 2089435 72390845 := bstep (se 3 (by rfl) ⟨13573283, by rfl⟩ : syracuseStep 72390845 = 27146567) B27146567
theorem B193042253 : Blo 2089435 193042253 := bstep (se 3 (by rfl) ⟨36195422, by rfl⟩ : syracuseStep 193042253 = 72390845) B72390845
theorem B128694835 : Blo 2089435 128694835 := bstep (se 1 (by rfl) ⟨96521126, by rfl⟩ : syracuseStep 128694835 = 193042253) B193042253
theorem B171593113 : Blo 2089435 171593113 := bstep (se 2 (by rfl) ⟨64347417, by rfl⟩ : syracuseStep 171593113 = 128694835) B128694835
theorem B228790817 : Blo 2089435 228790817 := bstep (se 2 (by rfl) ⟨85796556, by rfl⟩ : syracuseStep 228790817 = 171593113) B171593113
theorem B152527211 : Blo 2089435 152527211 := bstep (se 1 (by rfl) ⟨114395408, by rfl⟩ : syracuseStep 152527211 = 228790817) B228790817
theorem B101684807 : Blo 2089435 101684807 := bstep (se 1 (by rfl) ⟨76263605, by rfl⟩ : syracuseStep 101684807 = 152527211) B152527211
theorem B67789871 : Blo 2089435 67789871 := bstep (se 1 (by rfl) ⟨50842403, by rfl⟩ : syracuseStep 67789871 = 101684807) B101684807
theorem B45193247 : Blo 2089435 45193247 := bstep (se 1 (by rfl) ⟨33894935, by rfl⟩ : syracuseStep 45193247 = 67789871) B67789871
theorem B30128831 : Blo 2089435 30128831 := bstep (se 1 (by rfl) ⟨22596623, by rfl⟩ : syracuseStep 30128831 = 45193247) B45193247
theorem B20085887 : Blo 2089435 20085887 := bstep (se 1 (by rfl) ⟨15064415, by rfl⟩ : syracuseStep 20085887 = 30128831) B30128831
theorem B13390591 : Blo 2089435 13390591 := bstep (se 1 (by rfl) ⟨10042943, by rfl⟩ : syracuseStep 13390591 = 20085887) B20085887
theorem B17854121 : Blo 2089435 17854121 := bstep (se 2 (by rfl) ⟨6695295, by rfl⟩ : syracuseStep 17854121 = 13390591) B13390591
theorem B11902747 : Blo 2089435 11902747 := bstep (se 1 (by rfl) ⟨8927060, by rfl⟩ : syracuseStep 11902747 = 17854121) B17854121
theorem B15870329 : Blo 2089435 15870329 := bstep (se 2 (by rfl) ⟨5951373, by rfl⟩ : syracuseStep 15870329 = 11902747) B11902747
theorem B10580219 : Blo 2089435 10580219 := bstep (se 1 (by rfl) ⟨7935164, by rfl⟩ : syracuseStep 10580219 = 15870329) B15870329
theorem B7053479 : Blo 2089435 7053479 := bstep (se 1 (by rfl) ⟨5290109, by rfl⟩ : syracuseStep 7053479 = 10580219) B10580219
theorem B4702319 : Blo 2089435 4702319 := bstep (se 1 (by rfl) ⟨3526739, by rfl⟩ : syracuseStep 4702319 = 7053479) B7053479
theorem B3134879 : Blo 2089435 3134879 := bstep (se 1 (by rfl) ⟨2351159, by rfl⟩ : syracuseStep 3134879 = 4702319) B4702319
theorem B2089919 : Blo 2089435 2089919 := bstep (se 1 (by rfl) ⟨1567439, by rfl⟩ : syracuseStep 2089919 = 3134879) B3134879
theorem B3134885 : Blo 2089435 3134885 := bbase (se 4 (by rfl) ⟨293895, by rfl⟩ : syracuseStep 3134885 = 587791) (by norm_num)
theorem B2089923 : Blo 2089435 2089923 := bstep (se 1 (by rfl) ⟨1567442, by rfl⟩ : syracuseStep 2089923 = 3134885) B3134885
theorem B2645065 : Blo 2089435 2645065 := bbase (se 2 (by rfl) ⟨991899, by rfl⟩ : syracuseStep 2645065 = 1983799) (by norm_num)
theorem B3526753 : Blo 2089435 3526753 := bstep (se 2 (by rfl) ⟨1322532, by rfl⟩ : syracuseStep 3526753 = 2645065) B2645065
theorem B4702337 : Blo 2089435 4702337 := bstep (se 2 (by rfl) ⟨1763376, by rfl⟩ : syracuseStep 4702337 = 3526753) B3526753
theorem B3134891 : Blo 2089435 3134891 := bstep (se 1 (by rfl) ⟨2351168, by rfl⟩ : syracuseStep 3134891 = 4702337) B4702337
theorem B2089927 : Blo 2089435 2089927 := bstep (se 1 (by rfl) ⟨1567445, by rfl⟩ : syracuseStep 2089927 = 3134891) B3134891
theorem B2351173 : Blo 2089435 2351173 := bbase (se 4 (by rfl) ⟨220422, by rfl⟩ : syracuseStep 2351173 = 440845) (by norm_num)
theorem B3134897 : Blo 2089435 3134897 := bstep (se 2 (by rfl) ⟨1175586, by rfl⟩ : syracuseStep 3134897 = 2351173) B2351173
theorem B2089931 : Blo 2089435 2089931 := bstep (se 1 (by rfl) ⟨1567448, by rfl⟩ : syracuseStep 2089931 = 3134897) B3134897
theorem B3967613 : Blo 2089435 3967613 := bbase (se 3 (by rfl) ⟨743927, by rfl⟩ : syracuseStep 3967613 = 1487855) (by norm_num)
theorem B2645075 : Blo 2089435 2645075 := bstep (se 1 (by rfl) ⟨1983806, by rfl⟩ : syracuseStep 2645075 = 3967613) B3967613
theorem B7053533 : Blo 2089435 7053533 := bstep (se 3 (by rfl) ⟨1322537, by rfl⟩ : syracuseStep 7053533 = 2645075) B2645075
theorem B4702355 : Blo 2089435 4702355 := bstep (se 1 (by rfl) ⟨3526766, by rfl⟩ : syracuseStep 4702355 = 7053533) B7053533
theorem B3134903 : Blo 2089435 3134903 := bstep (se 1 (by rfl) ⟨2351177, by rfl⟩ : syracuseStep 3134903 = 4702355) B4702355
theorem B2089935 : Blo 2089435 2089935 := bstep (se 1 (by rfl) ⟨1567451, by rfl⟩ : syracuseStep 2089935 = 3134903) B3134903
theorem B3134909 : Blo 2089435 3134909 := bbase (se 3 (by rfl) ⟨587795, by rfl⟩ : syracuseStep 3134909 = 1175591) (by norm_num)
theorem B2089939 : Blo 2089435 2089939 := bstep (se 1 (by rfl) ⟨1567454, by rfl⟩ : syracuseStep 2089939 = 3134909) B3134909
theorem B4702373 : Blo 2089435 4702373 := bbase (se 4 (by rfl) ⟨440847, by rfl⟩ : syracuseStep 4702373 = 881695) (by norm_num)
theorem B3134915 : Blo 2089435 3134915 := bstep (se 1 (by rfl) ⟨2351186, by rfl⟩ : syracuseStep 3134915 = 4702373) B4702373
theorem B2089943 : Blo 2089435 2089943 := bstep (se 1 (by rfl) ⟨1567457, by rfl⟩ : syracuseStep 2089943 = 3134915) B3134915
theorem B5290181 : Blo 2089435 5290181 := bbase (se 4 (by rfl) ⟨495954, by rfl⟩ : syracuseStep 5290181 = 991909) (by norm_num)
theorem B3526787 : Blo 2089435 3526787 := bstep (se 1 (by rfl) ⟨2645090, by rfl⟩ : syracuseStep 3526787 = 5290181) B5290181
theorem B2351191 : Blo 2089435 2351191 := bstep (se 1 (by rfl) ⟨1763393, by rfl⟩ : syracuseStep 2351191 = 3526787) B3526787
theorem B3134921 : Blo 2089435 3134921 := bstep (se 2 (by rfl) ⟨1175595, by rfl⟩ : syracuseStep 3134921 = 2351191) B2351191
theorem B2089947 : Blo 2089435 2089947 := bstep (se 1 (by rfl) ⟨1567460, by rfl⟩ : syracuseStep 2089947 = 3134921) B3134921
theorem B4294741 : Blo 2089435 4294741 := bbase (se 8 (by rfl) ⟨25164, by rfl⟩ : syracuseStep 4294741 = 50329) (by norm_num)
theorem B5726321 : Blo 2089435 5726321 := bstep (se 2 (by rfl) ⟨2147370, by rfl⟩ : syracuseStep 5726321 = 4294741) B4294741
theorem B3817547 : Blo 2089435 3817547 := bstep (se 1 (by rfl) ⟨2863160, by rfl⟩ : syracuseStep 3817547 = 5726321) B5726321
theorem B2545031 : Blo 2089435 2545031 := bstep (se 1 (by rfl) ⟨1908773, by rfl⟩ : syracuseStep 2545031 = 3817547) B3817547
theorem B6786749 : Blo 2089435 6786749 := bstep (se 3 (by rfl) ⟨1272515, by rfl⟩ : syracuseStep 6786749 = 2545031) B2545031
theorem B4524499 : Blo 2089435 4524499 := bstep (se 1 (by rfl) ⟨3393374, by rfl⟩ : syracuseStep 4524499 = 6786749) B6786749
theorem B6032665 : Blo 2089435 6032665 := bstep (se 2 (by rfl) ⟨2262249, by rfl⟩ : syracuseStep 6032665 = 4524499) B4524499
theorem B8043553 : Blo 2089435 8043553 := bstep (se 2 (by rfl) ⟨3016332, by rfl⟩ : syracuseStep 8043553 = 6032665) B6032665
theorem B10724737 : Blo 2089435 10724737 := bstep (se 2 (by rfl) ⟨4021776, by rfl⟩ : syracuseStep 10724737 = 8043553) B8043553
theorem B14299649 : Blo 2089435 14299649 := bstep (se 2 (by rfl) ⟨5362368, by rfl⟩ : syracuseStep 14299649 = 10724737) B10724737
theorem B9533099 : Blo 2089435 9533099 := bstep (se 1 (by rfl) ⟨7149824, by rfl⟩ : syracuseStep 9533099 = 14299649) B14299649
theorem B25421597 : Blo 2089435 25421597 := bstep (se 3 (by rfl) ⟨4766549, by rfl⟩ : syracuseStep 25421597 = 9533099) B9533099
theorem B16947731 : Blo 2089435 16947731 := bstep (se 1 (by rfl) ⟨12710798, by rfl⟩ : syracuseStep 16947731 = 25421597) B25421597
theorem B11298487 : Blo 2089435 11298487 := bstep (se 1 (by rfl) ⟨8473865, by rfl⟩ : syracuseStep 11298487 = 16947731) B16947731
theorem B15064649 : Blo 2089435 15064649 := bstep (se 2 (by rfl) ⟨5649243, by rfl⟩ : syracuseStep 15064649 = 11298487) B11298487
theorem B10043099 : Blo 2089435 10043099 := bstep (se 1 (by rfl) ⟨7532324, by rfl⟩ : syracuseStep 10043099 = 15064649) B15064649
theorem B6695399 : Blo 2089435 6695399 := bstep (se 1 (by rfl) ⟨5021549, by rfl⟩ : syracuseStep 6695399 = 10043099) B10043099
theorem B4463599 : Blo 2089435 4463599 := bstep (se 1 (by rfl) ⟨3347699, by rfl⟩ : syracuseStep 4463599 = 6695399) B6695399
theorem B5951465 : Blo 2089435 5951465 := bstep (se 2 (by rfl) ⟨2231799, by rfl⟩ : syracuseStep 5951465 = 4463599) B4463599
theorem B3967643 : Blo 2089435 3967643 := bstep (se 1 (by rfl) ⟨2975732, by rfl⟩ : syracuseStep 3967643 = 5951465) B5951465
theorem B10580381 : Blo 2089435 10580381 := bstep (se 3 (by rfl) ⟨1983821, by rfl⟩ : syracuseStep 10580381 = 3967643) B3967643
theorem B7053587 : Blo 2089435 7053587 := bstep (se 1 (by rfl) ⟨5290190, by rfl⟩ : syracuseStep 7053587 = 10580381) B10580381
theorem B4702391 : Blo 2089435 4702391 := bstep (se 1 (by rfl) ⟨3526793, by rfl⟩ : syracuseStep 4702391 = 7053587) B7053587
theorem B3134927 : Blo 2089435 3134927 := bstep (se 1 (by rfl) ⟨2351195, by rfl⟩ : syracuseStep 3134927 = 4702391) B4702391
theorem B2089951 : Blo 2089435 2089951 := bstep (se 1 (by rfl) ⟨1567463, by rfl⟩ : syracuseStep 2089951 = 3134927) B3134927
theorem B3134933 : Blo 2089435 3134933 := bbase (se 7 (by rfl) ⟨36737, by rfl⟩ : syracuseStep 3134933 = 73475) (by norm_num)
theorem B2089955 : Blo 2089435 2089955 := bstep (se 1 (by rfl) ⟨1567466, by rfl⟩ : syracuseStep 2089955 = 3134933) B3134933
theorem B7935317 : Blo 2089435 7935317 := bbase (se 14 (by rfl) ⟨726, by rfl⟩ : syracuseStep 7935317 = 1453) (by norm_num)
theorem B5290211 : Blo 2089435 5290211 := bstep (se 1 (by rfl) ⟨3967658, by rfl⟩ : syracuseStep 5290211 = 7935317) B7935317
theorem B3526807 : Blo 2089435 3526807 := bstep (se 1 (by rfl) ⟨2645105, by rfl⟩ : syracuseStep 3526807 = 5290211) B5290211
theorem B4702409 : Blo 2089435 4702409 := bstep (se 2 (by rfl) ⟨1763403, by rfl⟩ : syracuseStep 4702409 = 3526807) B3526807
theorem B3134939 : Blo 2089435 3134939 := bstep (se 1 (by rfl) ⟨2351204, by rfl⟩ : syracuseStep 3134939 = 4702409) B4702409
theorem B2089959 : Blo 2089435 2089959 := bstep (se 1 (by rfl) ⟨1567469, by rfl⟩ : syracuseStep 2089959 = 3134939) B3134939
theorem B2351209 : Blo 2089435 2351209 := bbase (se 2 (by rfl) ⟨881703, by rfl⟩ : syracuseStep 2351209 = 1763407) (by norm_num)
theorem B3134945 : Blo 2089435 3134945 := bstep (se 2 (by rfl) ⟨1175604, by rfl⟩ : syracuseStep 3134945 = 2351209) B2351209
theorem B2089963 : Blo 2089435 2089963 := bstep (se 1 (by rfl) ⟨1567472, by rfl⟩ : syracuseStep 2089963 = 3134945) B3134945
theorem B3347725 : Blo 2089435 3347725 := bbase (se 3 (by rfl) ⟨627698, by rfl⟩ : syracuseStep 3347725 = 1255397) (by norm_num)
theorem B4463633 : Blo 2089435 4463633 := bstep (se 2 (by rfl) ⟨1673862, by rfl⟩ : syracuseStep 4463633 = 3347725) B3347725
theorem B11903021 : Blo 2089435 11903021 := bstep (se 3 (by rfl) ⟨2231816, by rfl⟩ : syracuseStep 11903021 = 4463633) B4463633
theorem B7935347 : Blo 2089435 7935347 := bstep (se 1 (by rfl) ⟨5951510, by rfl⟩ : syracuseStep 7935347 = 11903021) B11903021
theorem B5290231 : Blo 2089435 5290231 := bstep (se 1 (by rfl) ⟨3967673, by rfl⟩ : syracuseStep 5290231 = 7935347) B7935347
theorem B7053641 : Blo 2089435 7053641 := bstep (se 2 (by rfl) ⟨2645115, by rfl⟩ : syracuseStep 7053641 = 5290231) B5290231
theorem B4702427 : Blo 2089435 4702427 := bstep (se 1 (by rfl) ⟨3526820, by rfl⟩ : syracuseStep 4702427 = 7053641) B7053641
theorem B3134951 : Blo 2089435 3134951 := bstep (se 1 (by rfl) ⟨2351213, by rfl⟩ : syracuseStep 3134951 = 4702427) B4702427
theorem B2089967 : Blo 2089435 2089967 := bstep (se 1 (by rfl) ⟨1567475, by rfl⟩ : syracuseStep 2089967 = 3134951) B3134951
theorem B3134957 : Blo 2089435 3134957 := bbase (se 3 (by rfl) ⟨587804, by rfl⟩ : syracuseStep 3134957 = 1175609) (by norm_num)
theorem B2089971 : Blo 2089435 2089971 := bstep (se 1 (by rfl) ⟨1567478, by rfl⟩ : syracuseStep 2089971 = 3134957) B3134957
theorem B4702445 : Blo 2089435 4702445 := bbase (se 3 (by rfl) ⟨881708, by rfl⟩ : syracuseStep 4702445 = 1763417) (by norm_num)
theorem B3134963 : Blo 2089435 3134963 := bstep (se 1 (by rfl) ⟨2351222, by rfl⟩ : syracuseStep 3134963 = 4702445) B4702445
theorem B2089975 : Blo 2089435 2089975 := bstep (se 1 (by rfl) ⟨1567481, by rfl⟩ : syracuseStep 2089975 = 3134963) B3134963
theorem B2975773 : Blo 2089435 2975773 := bbase (se 3 (by rfl) ⟨557957, by rfl⟩ : syracuseStep 2975773 = 1115915) (by norm_num)
theorem B3967697 : Blo 2089435 3967697 := bstep (se 2 (by rfl) ⟨1487886, by rfl⟩ : syracuseStep 3967697 = 2975773) B2975773
theorem B2645131 : Blo 2089435 2645131 := bstep (se 1 (by rfl) ⟨1983848, by rfl⟩ : syracuseStep 2645131 = 3967697) B3967697
theorem B3526841 : Blo 2089435 3526841 := bstep (se 2 (by rfl) ⟨1322565, by rfl⟩ : syracuseStep 3526841 = 2645131) B2645131
theorem B2351227 : Blo 2089435 2351227 := bstep (se 1 (by rfl) ⟨1763420, by rfl⟩ : syracuseStep 2351227 = 3526841) B3526841
theorem B3134969 : Blo 2089435 3134969 := bstep (se 2 (by rfl) ⟨1175613, by rfl⟩ : syracuseStep 3134969 = 2351227) B2351227
theorem B2089979 : Blo 2089435 2089979 := bstep (se 1 (by rfl) ⟨1567484, by rfl⟩ : syracuseStep 2089979 = 3134969) B3134969
theorem B4236997 : Blo 2089435 4236997 := bbase (se 4 (by rfl) ⟨397218, by rfl⟩ : syracuseStep 4236997 = 794437) (by norm_num)
theorem B5649329 : Blo 2089435 5649329 := bstep (se 2 (by rfl) ⟨2118498, by rfl⟩ : syracuseStep 5649329 = 4236997) B4236997
theorem B3766219 : Blo 2089435 3766219 := bstep (se 1 (by rfl) ⟨2824664, by rfl⟩ : syracuseStep 3766219 = 5649329) B5649329
theorem B80346005 : Blo 2089435 80346005 := bstep (se 6 (by rfl) ⟨1883109, by rfl⟩ : syracuseStep 80346005 = 3766219) B3766219
theorem B53564003 : Blo 2089435 53564003 := bstep (se 1 (by rfl) ⟨40173002, by rfl⟩ : syracuseStep 53564003 = 80346005) B80346005
theorem B35709335 : Blo 2089435 35709335 := bstep (se 1 (by rfl) ⟨26782001, by rfl⟩ : syracuseStep 35709335 = 53564003) B53564003
theorem B23806223 : Blo 2089435 23806223 := bstep (se 1 (by rfl) ⟨17854667, by rfl⟩ : syracuseStep 23806223 = 35709335) B35709335
theorem B15870815 : Blo 2089435 15870815 := bstep (se 1 (by rfl) ⟨11903111, by rfl⟩ : syracuseStep 15870815 = 23806223) B23806223
theorem B10580543 : Blo 2089435 10580543 := bstep (se 1 (by rfl) ⟨7935407, by rfl⟩ : syracuseStep 10580543 = 15870815) B15870815
theorem B7053695 : Blo 2089435 7053695 := bstep (se 1 (by rfl) ⟨5290271, by rfl⟩ : syracuseStep 7053695 = 10580543) B10580543
theorem B4702463 : Blo 2089435 4702463 := bstep (se 1 (by rfl) ⟨3526847, by rfl⟩ : syracuseStep 4702463 = 7053695) B7053695
theorem B3134975 : Blo 2089435 3134975 := bstep (se 1 (by rfl) ⟨2351231, by rfl⟩ : syracuseStep 3134975 = 4702463) B4702463
theorem B2089983 : Blo 2089435 2089983 := bstep (se 1 (by rfl) ⟨1567487, by rfl⟩ : syracuseStep 2089983 = 3134975) B3134975
theorem B3134981 : Blo 2089435 3134981 := bbase (se 4 (by rfl) ⟨293904, by rfl⟩ : syracuseStep 3134981 = 587809) (by norm_num)
theorem B2089987 : Blo 2089435 2089987 := bstep (se 1 (by rfl) ⟨1567490, by rfl⟩ : syracuseStep 2089987 = 3134981) B3134981
theorem B3526861 : Blo 2089435 3526861 := bbase (se 3 (by rfl) ⟨661286, by rfl⟩ : syracuseStep 3526861 = 1322573) (by norm_num)
theorem B4702481 : Blo 2089435 4702481 := bstep (se 2 (by rfl) ⟨1763430, by rfl⟩ : syracuseStep 4702481 = 3526861) B3526861
theorem B3134987 : Blo 2089435 3134987 := bstep (se 1 (by rfl) ⟨2351240, by rfl⟩ : syracuseStep 3134987 = 4702481) B4702481
theorem B2089991 : Blo 2089435 2089991 := bstep (se 1 (by rfl) ⟨1567493, by rfl⟩ : syracuseStep 2089991 = 3134987) B3134987
theorem B2351245 : Blo 2089435 2351245 := bbase (se 3 (by rfl) ⟨440858, by rfl⟩ : syracuseStep 2351245 = 881717) (by norm_num)
theorem B3134993 : Blo 2089435 3134993 := bstep (se 2 (by rfl) ⟨1175622, by rfl⟩ : syracuseStep 3134993 = 2351245) B2351245
theorem B2089995 : Blo 2089435 2089995 := bstep (se 1 (by rfl) ⟨1567496, by rfl⟩ : syracuseStep 2089995 = 3134993) B3134993
theorem B7053749 : Blo 2089435 7053749 := bbase (se 5 (by rfl) ⟨330644, by rfl⟩ : syracuseStep 7053749 = 661289) (by norm_num)
theorem B4702499 : Blo 2089435 4702499 := bstep (se 1 (by rfl) ⟨3526874, by rfl⟩ : syracuseStep 4702499 = 7053749) B7053749
theorem B3134999 : Blo 2089435 3134999 := bstep (se 1 (by rfl) ⟨2351249, by rfl⟩ : syracuseStep 3134999 = 4702499) B4702499
theorem B2089999 : Blo 2089435 2089999 := bstep (se 1 (by rfl) ⟨1567499, by rfl⟩ : syracuseStep 2089999 = 3134999) B3134999
theorem B3135005 : Blo 2089435 3135005 := bbase (se 3 (by rfl) ⟨587813, by rfl⟩ : syracuseStep 3135005 = 1175627) (by norm_num)
theorem B2090003 : Blo 2089435 2090003 := bstep (se 1 (by rfl) ⟨1567502, by rfl⟩ : syracuseStep 2090003 = 3135005) B3135005
theorem B4702517 : Blo 2089435 4702517 := bbase (se 5 (by rfl) ⟨220430, by rfl⟩ : syracuseStep 4702517 = 440861) (by norm_num)
theorem B3135011 : Blo 2089435 3135011 := bstep (se 1 (by rfl) ⟨2351258, by rfl⟩ : syracuseStep 3135011 = 4702517) B4702517
theorem B2090007 : Blo 2089435 2090007 := bstep (se 1 (by rfl) ⟨1567505, by rfl⟩ : syracuseStep 2090007 = 3135011) B3135011
theorem B4076765 : Blo 2089435 4076765 := bbase (se 3 (by rfl) ⟨764393, by rfl⟩ : syracuseStep 4076765 = 1528787) (by norm_num)
theorem B2717843 : Blo 2089435 2717843 := bstep (se 1 (by rfl) ⟨2038382, by rfl⟩ : syracuseStep 2717843 = 4076765) B4076765
theorem B28990325 : Blo 2089435 28990325 := bstep (se 5 (by rfl) ⟨1358921, by rfl⟩ : syracuseStep 28990325 = 2717843) B2717843
theorem B19326883 : Blo 2089435 19326883 := bstep (se 1 (by rfl) ⟨14495162, by rfl⟩ : syracuseStep 19326883 = 28990325) B28990325
theorem B25769177 : Blo 2089435 25769177 := bstep (se 2 (by rfl) ⟨9663441, by rfl⟩ : syracuseStep 25769177 = 19326883) B19326883
theorem B17179451 : Blo 2089435 17179451 := bstep (se 1 (by rfl) ⟨12884588, by rfl⟩ : syracuseStep 17179451 = 25769177) B25769177
theorem B11452967 : Blo 2089435 11452967 := bstep (se 1 (by rfl) ⟨8589725, by rfl⟩ : syracuseStep 11452967 = 17179451) B17179451
theorem B7635311 : Blo 2089435 7635311 := bstep (se 1 (by rfl) ⟨5726483, by rfl⟩ : syracuseStep 7635311 = 11452967) B11452967
theorem B5090207 : Blo 2089435 5090207 := bstep (se 1 (by rfl) ⟨3817655, by rfl⟩ : syracuseStep 5090207 = 7635311) B7635311
theorem B54295541 : Blo 2089435 54295541 := bstep (se 5 (by rfl) ⟨2545103, by rfl⟩ : syracuseStep 54295541 = 5090207) B5090207
theorem B36197027 : Blo 2089435 36197027 := bstep (se 1 (by rfl) ⟨27147770, by rfl⟩ : syracuseStep 36197027 = 54295541) B54295541
theorem B24131351 : Blo 2089435 24131351 := bstep (se 1 (by rfl) ⟨18098513, by rfl⟩ : syracuseStep 24131351 = 36197027) B36197027
theorem B16087567 : Blo 2089435 16087567 := bstep (se 1 (by rfl) ⟨12065675, by rfl⟩ : syracuseStep 16087567 = 24131351) B24131351
theorem B21450089 : Blo 2089435 21450089 := bstep (se 2 (by rfl) ⟨8043783, by rfl⟩ : syracuseStep 21450089 = 16087567) B16087567
theorem B14300059 : Blo 2089435 14300059 := bstep (se 1 (by rfl) ⟨10725044, by rfl⟩ : syracuseStep 14300059 = 21450089) B21450089
theorem B19066745 : Blo 2089435 19066745 := bstep (se 2 (by rfl) ⟨7150029, by rfl⟩ : syracuseStep 19066745 = 14300059) B14300059
theorem B12711163 : Blo 2089435 12711163 := bstep (se 1 (by rfl) ⟨9533372, by rfl⟩ : syracuseStep 12711163 = 19066745) B19066745
theorem B16948217 : Blo 2089435 16948217 := bstep (se 2 (by rfl) ⟨6355581, by rfl⟩ : syracuseStep 16948217 = 12711163) B12711163
theorem B45195245 : Blo 2089435 45195245 := bstep (se 3 (by rfl) ⟨8474108, by rfl⟩ : syracuseStep 45195245 = 16948217) B16948217
theorem B30130163 : Blo 2089435 30130163 := bstep (se 1 (by rfl) ⟨22597622, by rfl⟩ : syracuseStep 30130163 = 45195245) B45195245
theorem B20086775 : Blo 2089435 20086775 := bstep (se 1 (by rfl) ⟨15065081, by rfl⟩ : syracuseStep 20086775 = 30130163) B30130163
theorem B13391183 : Blo 2089435 13391183 := bstep (se 1 (by rfl) ⟨10043387, by rfl⟩ : syracuseStep 13391183 = 20086775) B20086775
theorem B8927455 : Blo 2089435 8927455 := bstep (se 1 (by rfl) ⟨6695591, by rfl⟩ : syracuseStep 8927455 = 13391183) B13391183
theorem B11903273 : Blo 2089435 11903273 := bstep (se 2 (by rfl) ⟨4463727, by rfl⟩ : syracuseStep 11903273 = 8927455) B8927455
theorem B7935515 : Blo 2089435 7935515 := bstep (se 1 (by rfl) ⟨5951636, by rfl⟩ : syracuseStep 7935515 = 11903273) B11903273
theorem B5290343 : Blo 2089435 5290343 := bstep (se 1 (by rfl) ⟨3967757, by rfl⟩ : syracuseStep 5290343 = 7935515) B7935515
theorem B3526895 : Blo 2089435 3526895 := bstep (se 1 (by rfl) ⟨2645171, by rfl⟩ : syracuseStep 3526895 = 5290343) B5290343
theorem B2351263 : Blo 2089435 2351263 := bstep (se 1 (by rfl) ⟨1763447, by rfl⟩ : syracuseStep 2351263 = 3526895) B3526895
theorem B3135017 : Blo 2089435 3135017 := bstep (se 2 (by rfl) ⟨1175631, by rfl⟩ : syracuseStep 3135017 = 2351263) B2351263
theorem B2090011 : Blo 2089435 2090011 := bstep (se 1 (by rfl) ⟨1567508, by rfl⟩ : syracuseStep 2090011 = 3135017) B3135017
theorem B2754929 : Blo 2089435 2754929 := bbase (se 2 (by rfl) ⟨1033098, by rfl⟩ : syracuseStep 2754929 = 2066197) (by norm_num)
theorem B7346477 : Blo 2089435 7346477 := bstep (se 3 (by rfl) ⟨1377464, by rfl⟩ : syracuseStep 7346477 = 2754929) B2754929
theorem B19590605 : Blo 2089435 19590605 := bstep (se 3 (by rfl) ⟨3673238, by rfl⟩ : syracuseStep 19590605 = 7346477) B7346477
theorem B13060403 : Blo 2089435 13060403 := bstep (se 1 (by rfl) ⟨9795302, by rfl⟩ : syracuseStep 13060403 = 19590605) B19590605
theorem B8706935 : Blo 2089435 8706935 := bstep (se 1 (by rfl) ⟨6530201, by rfl⟩ : syracuseStep 8706935 = 13060403) B13060403
theorem B5804623 : Blo 2089435 5804623 := bstep (se 1 (by rfl) ⟨4353467, by rfl⟩ : syracuseStep 5804623 = 8706935) B8706935
theorem B7739497 : Blo 2089435 7739497 := bstep (se 2 (by rfl) ⟨2902311, by rfl⟩ : syracuseStep 7739497 = 5804623) B5804623
theorem B10319329 : Blo 2089435 10319329 := bstep (se 2 (by rfl) ⟨3869748, by rfl⟩ : syracuseStep 10319329 = 7739497) B7739497
theorem B13759105 : Blo 2089435 13759105 := bstep (se 2 (by rfl) ⟨5159664, by rfl⟩ : syracuseStep 13759105 = 10319329) B10319329
theorem B18345473 : Blo 2089435 18345473 := bstep (se 2 (by rfl) ⟨6879552, by rfl⟩ : syracuseStep 18345473 = 13759105) B13759105
theorem B12230315 : Blo 2089435 12230315 := bstep (se 1 (by rfl) ⟨9172736, by rfl⟩ : syracuseStep 12230315 = 18345473) B18345473
theorem B8153543 : Blo 2089435 8153543 := bstep (se 1 (by rfl) ⟨6115157, by rfl⟩ : syracuseStep 8153543 = 12230315) B12230315
theorem B5435695 : Blo 2089435 5435695 := bstep (se 1 (by rfl) ⟨4076771, by rfl⟩ : syracuseStep 5435695 = 8153543) B8153543
theorem B7247593 : Blo 2089435 7247593 := bstep (se 2 (by rfl) ⟨2717847, by rfl⟩ : syracuseStep 7247593 = 5435695) B5435695
theorem B9663457 : Blo 2089435 9663457 := bstep (se 2 (by rfl) ⟨3623796, by rfl⟩ : syracuseStep 9663457 = 7247593) B7247593
theorem B12884609 : Blo 2089435 12884609 := bstep (se 2 (by rfl) ⟨4831728, by rfl⟩ : syracuseStep 12884609 = 9663457) B9663457
theorem B34358957 : Blo 2089435 34358957 := bstep (se 3 (by rfl) ⟨6442304, by rfl⟩ : syracuseStep 34358957 = 12884609) B12884609
theorem B22905971 : Blo 2089435 22905971 := bstep (se 1 (by rfl) ⟨17179478, by rfl⟩ : syracuseStep 22905971 = 34358957) B34358957
theorem B15270647 : Blo 2089435 15270647 := bstep (se 1 (by rfl) ⟨11452985, by rfl⟩ : syracuseStep 15270647 = 22905971) B22905971
theorem B40721725 : Blo 2089435 40721725 := bstep (se 3 (by rfl) ⟨7635323, by rfl⟩ : syracuseStep 40721725 = 15270647) B15270647
theorem B54295633 : Blo 2089435 54295633 := bstep (se 2 (by rfl) ⟨20360862, by rfl⟩ : syracuseStep 54295633 = 40721725) B40721725
theorem B72394177 : Blo 2089435 72394177 := bstep (se 2 (by rfl) ⟨27147816, by rfl⟩ : syracuseStep 72394177 = 54295633) B54295633
theorem B96525569 : Blo 2089435 96525569 := bstep (se 2 (by rfl) ⟨36197088, by rfl⟩ : syracuseStep 96525569 = 72394177) B72394177
theorem B64350379 : Blo 2089435 64350379 := bstep (se 1 (by rfl) ⟨48262784, by rfl⟩ : syracuseStep 64350379 = 96525569) B96525569
theorem B85800505 : Blo 2089435 85800505 := bstep (se 2 (by rfl) ⟨32175189, by rfl⟩ : syracuseStep 85800505 = 64350379) B64350379
theorem B114400673 : Blo 2089435 114400673 := bstep (se 2 (by rfl) ⟨42900252, by rfl⟩ : syracuseStep 114400673 = 85800505) B85800505
theorem B76267115 : Blo 2089435 76267115 := bstep (se 1 (by rfl) ⟨57200336, by rfl⟩ : syracuseStep 76267115 = 114400673) B114400673
theorem B50844743 : Blo 2089435 50844743 := bstep (se 1 (by rfl) ⟨38133557, by rfl⟩ : syracuseStep 50844743 = 76267115) B76267115
theorem B33896495 : Blo 2089435 33896495 := bstep (se 1 (by rfl) ⟨25422371, by rfl⟩ : syracuseStep 33896495 = 50844743) B50844743
theorem B22597663 : Blo 2089435 22597663 := bstep (se 1 (by rfl) ⟨16948247, by rfl⟩ : syracuseStep 22597663 = 33896495) B33896495
theorem B30130217 : Blo 2089435 30130217 := bstep (se 2 (by rfl) ⟨11298831, by rfl⟩ : syracuseStep 30130217 = 22597663) B22597663
theorem B20086811 : Blo 2089435 20086811 := bstep (se 1 (by rfl) ⟨15065108, by rfl⟩ : syracuseStep 20086811 = 30130217) B30130217
theorem B13391207 : Blo 2089435 13391207 := bstep (se 1 (by rfl) ⟨10043405, by rfl⟩ : syracuseStep 13391207 = 20086811) B20086811
theorem B8927471 : Blo 2089435 8927471 := bstep (se 1 (by rfl) ⟨6695603, by rfl⟩ : syracuseStep 8927471 = 13391207) B13391207
theorem B5951647 : Blo 2089435 5951647 := bstep (se 1 (by rfl) ⟨4463735, by rfl⟩ : syracuseStep 5951647 = 8927471) B8927471
theorem B7935529 : Blo 2089435 7935529 := bstep (se 2 (by rfl) ⟨2975823, by rfl⟩ : syracuseStep 7935529 = 5951647) B5951647
theorem B10580705 : Blo 2089435 10580705 := bstep (se 2 (by rfl) ⟨3967764, by rfl⟩ : syracuseStep 10580705 = 7935529) B7935529
theorem B7053803 : Blo 2089435 7053803 := bstep (se 1 (by rfl) ⟨5290352, by rfl⟩ : syracuseStep 7053803 = 10580705) B10580705
theorem B4702535 : Blo 2089435 4702535 := bstep (se 1 (by rfl) ⟨3526901, by rfl⟩ : syracuseStep 4702535 = 7053803) B7053803
theorem B3135023 : Blo 2089435 3135023 := bstep (se 1 (by rfl) ⟨2351267, by rfl⟩ : syracuseStep 3135023 = 4702535) B4702535
theorem B2090015 : Blo 2089435 2090015 := bstep (se 1 (by rfl) ⟨1567511, by rfl⟩ : syracuseStep 2090015 = 3135023) B3135023
theorem B3135029 : Blo 2089435 3135029 := bbase (se 5 (by rfl) ⟨146954, by rfl⟩ : syracuseStep 3135029 = 293909) (by norm_num)
theorem B2090019 : Blo 2089435 2090019 := bstep (se 1 (by rfl) ⟨1567514, by rfl⟩ : syracuseStep 2090019 = 3135029) B3135029
theorem B5290373 : Blo 2089435 5290373 := bbase (se 4 (by rfl) ⟨495972, by rfl⟩ : syracuseStep 5290373 = 991945) (by norm_num)
theorem B3526915 : Blo 2089435 3526915 := bstep (se 1 (by rfl) ⟨2645186, by rfl⟩ : syracuseStep 3526915 = 5290373) B5290373
theorem B4702553 : Blo 2089435 4702553 := bstep (se 2 (by rfl) ⟨1763457, by rfl⟩ : syracuseStep 4702553 = 3526915) B3526915
theorem B3135035 : Blo 2089435 3135035 := bstep (se 1 (by rfl) ⟨2351276, by rfl⟩ : syracuseStep 3135035 = 4702553) B4702553
theorem B2090023 : Blo 2089435 2090023 := bstep (se 1 (by rfl) ⟨1567517, by rfl⟩ : syracuseStep 2090023 = 3135035) B3135035
theorem B2351281 : Blo 2089435 2351281 := bbase (se 2 (by rfl) ⟨881730, by rfl⟩ : syracuseStep 2351281 = 1763461) (by norm_num)
theorem B3135041 : Blo 2089435 3135041 := bstep (se 2 (by rfl) ⟨1175640, by rfl⟩ : syracuseStep 3135041 = 2351281) B2351281
theorem B2090027 : Blo 2089435 2090027 := bstep (se 1 (by rfl) ⟨1567520, by rfl⟩ : syracuseStep 2090027 = 3135041) B3135041
theorem B2231885 : Blo 2089435 2231885 := bbase (se 3 (by rfl) ⟨418478, by rfl⟩ : syracuseStep 2231885 = 836957) (by norm_num)
theorem B5951693 : Blo 2089435 5951693 := bstep (se 3 (by rfl) ⟨1115942, by rfl⟩ : syracuseStep 5951693 = 2231885) B2231885
theorem B3967795 : Blo 2089435 3967795 := bstep (se 1 (by rfl) ⟨2975846, by rfl⟩ : syracuseStep 3967795 = 5951693) B5951693
theorem B5290393 : Blo 2089435 5290393 := bstep (se 2 (by rfl) ⟨1983897, by rfl⟩ : syracuseStep 5290393 = 3967795) B3967795
theorem B7053857 : Blo 2089435 7053857 := bstep (se 2 (by rfl) ⟨2645196, by rfl⟩ : syracuseStep 7053857 = 5290393) B5290393
theorem B4702571 : Blo 2089435 4702571 := bstep (se 1 (by rfl) ⟨3526928, by rfl⟩ : syracuseStep 4702571 = 7053857) B7053857
theorem B3135047 : Blo 2089435 3135047 := bstep (se 1 (by rfl) ⟨2351285, by rfl⟩ : syracuseStep 3135047 = 4702571) B4702571
theorem B2090031 : Blo 2089435 2090031 := bstep (se 1 (by rfl) ⟨1567523, by rfl⟩ : syracuseStep 2090031 = 3135047) B3135047
theorem B3135053 : Blo 2089435 3135053 := bbase (se 3 (by rfl) ⟨587822, by rfl⟩ : syracuseStep 3135053 = 1175645) (by norm_num)
theorem B2090035 : Blo 2089435 2090035 := bstep (se 1 (by rfl) ⟨1567526, by rfl⟩ : syracuseStep 2090035 = 3135053) B3135053
theorem B4702589 : Blo 2089435 4702589 := bbase (se 3 (by rfl) ⟨881735, by rfl⟩ : syracuseStep 4702589 = 1763471) (by norm_num)
theorem B3135059 : Blo 2089435 3135059 := bstep (se 1 (by rfl) ⟨2351294, by rfl⟩ : syracuseStep 3135059 = 4702589) B4702589
theorem B2090039 : Blo 2089435 2090039 := bstep (se 1 (by rfl) ⟨1567529, by rfl⟩ : syracuseStep 2090039 = 3135059) B3135059
theorem B3526949 : Blo 2089435 3526949 := bbase (se 4 (by rfl) ⟨330651, by rfl⟩ : syracuseStep 3526949 = 661303) (by norm_num)
theorem B2351299 : Blo 2089435 2351299 := bstep (se 1 (by rfl) ⟨1763474, by rfl⟩ : syracuseStep 2351299 = 3526949) B3526949
theorem B3135065 : Blo 2089435 3135065 := bstep (se 2 (by rfl) ⟨1175649, by rfl⟩ : syracuseStep 3135065 = 2351299) B2351299
theorem B2090043 : Blo 2089435 2090043 := bstep (se 1 (by rfl) ⟨1567532, by rfl⟩ : syracuseStep 2090043 = 3135065) B3135065
theorem B2975869 : Blo 2089435 2975869 := bbase (se 3 (by rfl) ⟨557975, by rfl⟩ : syracuseStep 2975869 = 1115951) (by norm_num)
theorem B15871301 : Blo 2089435 15871301 := bstep (se 4 (by rfl) ⟨1487934, by rfl⟩ : syracuseStep 15871301 = 2975869) B2975869
theorem B10580867 : Blo 2089435 10580867 := bstep (se 1 (by rfl) ⟨7935650, by rfl⟩ : syracuseStep 10580867 = 15871301) B15871301
theorem B7053911 : Blo 2089435 7053911 := bstep (se 1 (by rfl) ⟨5290433, by rfl⟩ : syracuseStep 7053911 = 10580867) B10580867
theorem B4702607 : Blo 2089435 4702607 := bstep (se 1 (by rfl) ⟨3526955, by rfl⟩ : syracuseStep 4702607 = 7053911) B7053911
theorem B3135071 : Blo 2089435 3135071 := bstep (se 1 (by rfl) ⟨2351303, by rfl⟩ : syracuseStep 3135071 = 4702607) B4702607
theorem B2090047 : Blo 2089435 2090047 := bstep (se 1 (by rfl) ⟨1567535, by rfl⟩ : syracuseStep 2090047 = 3135071) B3135071
theorem B3135077 : Blo 2089435 3135077 := bbase (se 4 (by rfl) ⟨293913, by rfl⟩ : syracuseStep 3135077 = 587827) (by norm_num)
theorem B2090051 : Blo 2089435 2090051 := bstep (se 1 (by rfl) ⟨1567538, by rfl⟩ : syracuseStep 2090051 = 3135077) B3135077
theorem B4766789 : Blo 2089435 4766789 := bbase (se 4 (by rfl) ⟨446886, by rfl⟩ : syracuseStep 4766789 = 893773) (by norm_num)
theorem B12711437 : Blo 2089435 12711437 := bstep (se 3 (by rfl) ⟨2383394, by rfl⟩ : syracuseStep 12711437 = 4766789) B4766789
theorem B8474291 : Blo 2089435 8474291 := bstep (se 1 (by rfl) ⟨6355718, by rfl⟩ : syracuseStep 8474291 = 12711437) B12711437
theorem B5649527 : Blo 2089435 5649527 := bstep (se 1 (by rfl) ⟨4237145, by rfl⟩ : syracuseStep 5649527 = 8474291) B8474291
theorem B3766351 : Blo 2089435 3766351 := bstep (se 1 (by rfl) ⟨2824763, by rfl⟩ : syracuseStep 3766351 = 5649527) B5649527
theorem B5021801 : Blo 2089435 5021801 := bstep (se 2 (by rfl) ⟨1883175, by rfl⟩ : syracuseStep 5021801 = 3766351) B3766351
theorem B3347867 : Blo 2089435 3347867 := bstep (se 1 (by rfl) ⟨2510900, by rfl⟩ : syracuseStep 3347867 = 5021801) B5021801
theorem B2231911 : Blo 2089435 2231911 := bstep (se 1 (by rfl) ⟨1673933, by rfl⟩ : syracuseStep 2231911 = 3347867) B3347867
theorem B2975881 : Blo 2089435 2975881 := bstep (se 2 (by rfl) ⟨1115955, by rfl⟩ : syracuseStep 2975881 = 2231911) B2231911
theorem B3967841 : Blo 2089435 3967841 := bstep (se 2 (by rfl) ⟨1487940, by rfl⟩ : syracuseStep 3967841 = 2975881) B2975881
theorem B2645227 : Blo 2089435 2645227 := bstep (se 1 (by rfl) ⟨1983920, by rfl⟩ : syracuseStep 2645227 = 3967841) B3967841
theorem B3526969 : Blo 2089435 3526969 := bstep (se 2 (by rfl) ⟨1322613, by rfl⟩ : syracuseStep 3526969 = 2645227) B2645227
theorem B4702625 : Blo 2089435 4702625 := bstep (se 2 (by rfl) ⟨1763484, by rfl⟩ : syracuseStep 4702625 = 3526969) B3526969
theorem B3135083 : Blo 2089435 3135083 := bstep (se 1 (by rfl) ⟨2351312, by rfl⟩ : syracuseStep 3135083 = 4702625) B4702625
theorem B2090055 : Blo 2089435 2090055 := bstep (se 1 (by rfl) ⟨1567541, by rfl⟩ : syracuseStep 2090055 = 3135083) B3135083
theorem B2351317 : Blo 2089435 2351317 := bbase (se 7 (by rfl) ⟨27554, by rfl⟩ : syracuseStep 2351317 = 55109) (by norm_num)
theorem B3135089 : Blo 2089435 3135089 := bstep (se 2 (by rfl) ⟨1175658, by rfl⟩ : syracuseStep 3135089 = 2351317) B2351317
theorem B2090059 : Blo 2089435 2090059 := bstep (se 1 (by rfl) ⟨1567544, by rfl⟩ : syracuseStep 2090059 = 3135089) B3135089
theorem B2645237 : Blo 2089435 2645237 := bbase (se 5 (by rfl) ⟨123995, by rfl⟩ : syracuseStep 2645237 = 247991) (by norm_num)
theorem B7053965 : Blo 2089435 7053965 := bstep (se 3 (by rfl) ⟨1322618, by rfl⟩ : syracuseStep 7053965 = 2645237) B2645237
theorem B4702643 : Blo 2089435 4702643 := bstep (se 1 (by rfl) ⟨3526982, by rfl⟩ : syracuseStep 4702643 = 7053965) B7053965
theorem B3135095 : Blo 2089435 3135095 := bstep (se 1 (by rfl) ⟨2351321, by rfl⟩ : syracuseStep 3135095 = 4702643) B4702643
theorem B2090063 : Blo 2089435 2090063 := bstep (se 1 (by rfl) ⟨1567547, by rfl⟩ : syracuseStep 2090063 = 3135095) B3135095
theorem B3135101 : Blo 2089435 3135101 := bbase (se 3 (by rfl) ⟨587831, by rfl⟩ : syracuseStep 3135101 = 1175663) (by norm_num)
theorem B2090067 : Blo 2089435 2090067 := bstep (se 1 (by rfl) ⟨1567550, by rfl⟩ : syracuseStep 2090067 = 3135101) B3135101
theorem B4702661 : Blo 2089435 4702661 := bbase (se 4 (by rfl) ⟨440874, by rfl⟩ : syracuseStep 4702661 = 881749) (by norm_num)
theorem B3135107 : Blo 2089435 3135107 := bstep (se 1 (by rfl) ⟨2351330, by rfl⟩ : syracuseStep 3135107 = 4702661) B4702661
theorem B2090071 : Blo 2089435 2090071 := bstep (se 1 (by rfl) ⟨1567553, by rfl⟩ : syracuseStep 2090071 = 3135107) B3135107
theorem B6695797 : Blo 2089435 6695797 := bbase (se 5 (by rfl) ⟨313865, by rfl⟩ : syracuseStep 6695797 = 627731) (by norm_num)
theorem B8927729 : Blo 2089435 8927729 := bstep (se 2 (by rfl) ⟨3347898, by rfl⟩ : syracuseStep 8927729 = 6695797) B6695797
theorem B5951819 : Blo 2089435 5951819 := bstep (se 1 (by rfl) ⟨4463864, by rfl⟩ : syracuseStep 5951819 = 8927729) B8927729
theorem B3967879 : Blo 2089435 3967879 := bstep (se 1 (by rfl) ⟨2975909, by rfl⟩ : syracuseStep 3967879 = 5951819) B5951819
theorem B5290505 : Blo 2089435 5290505 := bstep (se 2 (by rfl) ⟨1983939, by rfl⟩ : syracuseStep 5290505 = 3967879) B3967879
theorem B3527003 : Blo 2089435 3527003 := bstep (se 1 (by rfl) ⟨2645252, by rfl⟩ : syracuseStep 3527003 = 5290505) B5290505
theorem B2351335 : Blo 2089435 2351335 := bstep (se 1 (by rfl) ⟨1763501, by rfl⟩ : syracuseStep 2351335 = 3527003) B3527003
theorem B3135113 : Blo 2089435 3135113 := bstep (se 2 (by rfl) ⟨1175667, by rfl⟩ : syracuseStep 3135113 = 2351335) B2351335
theorem B2090075 : Blo 2089435 2090075 := bstep (se 1 (by rfl) ⟨1567556, by rfl⟩ : syracuseStep 2090075 = 3135113) B3135113
theorem B10581029 : Blo 2089435 10581029 := bbase (se 4 (by rfl) ⟨991971, by rfl⟩ : syracuseStep 10581029 = 1983943) (by norm_num)
theorem B7054019 : Blo 2089435 7054019 := bstep (se 1 (by rfl) ⟨5290514, by rfl⟩ : syracuseStep 7054019 = 10581029) B10581029
theorem B4702679 : Blo 2089435 4702679 := bstep (se 1 (by rfl) ⟨3527009, by rfl⟩ : syracuseStep 4702679 = 7054019) B7054019
theorem B3135119 : Blo 2089435 3135119 := bstep (se 1 (by rfl) ⟨2351339, by rfl⟩ : syracuseStep 3135119 = 4702679) B4702679
theorem B2090079 : Blo 2089435 2090079 := bstep (se 1 (by rfl) ⟨1567559, by rfl⟩ : syracuseStep 2090079 = 3135119) B3135119
theorem B3135125 : Blo 2089435 3135125 := bbase (se 6 (by rfl) ⟨73479, by rfl⟩ : syracuseStep 3135125 = 146959) (by norm_num)
theorem B2090083 : Blo 2089435 2090083 := bstep (se 1 (by rfl) ⟨1567562, by rfl⟩ : syracuseStep 2090083 = 3135125) B3135125
theorem B13391669 : Blo 2089435 13391669 := bbase (se 5 (by rfl) ⟨627734, by rfl⟩ : syracuseStep 13391669 = 1255469) (by norm_num)
theorem B8927779 : Blo 2089435 8927779 := bstep (se 1 (by rfl) ⟨6695834, by rfl⟩ : syracuseStep 8927779 = 13391669) B13391669
theorem B11903705 : Blo 2089435 11903705 := bstep (se 2 (by rfl) ⟨4463889, by rfl⟩ : syracuseStep 11903705 = 8927779) B8927779
theorem B7935803 : Blo 2089435 7935803 := bstep (se 1 (by rfl) ⟨5951852, by rfl⟩ : syracuseStep 7935803 = 11903705) B11903705
theorem B5290535 : Blo 2089435 5290535 := bstep (se 1 (by rfl) ⟨3967901, by rfl⟩ : syracuseStep 5290535 = 7935803) B7935803
theorem B3527023 : Blo 2089435 3527023 := bstep (se 1 (by rfl) ⟨2645267, by rfl⟩ : syracuseStep 3527023 = 5290535) B5290535
theorem B4702697 : Blo 2089435 4702697 := bstep (se 2 (by rfl) ⟨1763511, by rfl⟩ : syracuseStep 4702697 = 3527023) B3527023
theorem B3135131 : Blo 2089435 3135131 := bstep (se 1 (by rfl) ⟨2351348, by rfl⟩ : syracuseStep 3135131 = 4702697) B4702697
theorem B2090087 : Blo 2089435 2090087 := bstep (se 1 (by rfl) ⟨1567565, by rfl⟩ : syracuseStep 2090087 = 3135131) B3135131
theorem B2351353 : Blo 2089435 2351353 := bbase (se 2 (by rfl) ⟨881757, by rfl⟩ : syracuseStep 2351353 = 1763515) (by norm_num)
theorem B3135137 : Blo 2089435 3135137 := bstep (se 2 (by rfl) ⟨1175676, by rfl⟩ : syracuseStep 3135137 = 2351353) B2351353
theorem B2090091 : Blo 2089435 2090091 := bstep (se 1 (by rfl) ⟨1567568, by rfl⟩ : syracuseStep 2090091 = 3135137) B3135137
theorem B8927813 : Blo 2089435 8927813 := bbase (se 4 (by rfl) ⟨836982, by rfl⟩ : syracuseStep 8927813 = 1673965) (by norm_num)
theorem B5951875 : Blo 2089435 5951875 := bstep (se 1 (by rfl) ⟨4463906, by rfl⟩ : syracuseStep 5951875 = 8927813) B8927813
theorem B7935833 : Blo 2089435 7935833 := bstep (se 2 (by rfl) ⟨2975937, by rfl⟩ : syracuseStep 7935833 = 5951875) B5951875
theorem B5290555 : Blo 2089435 5290555 := bstep (se 1 (by rfl) ⟨3967916, by rfl⟩ : syracuseStep 5290555 = 7935833) B7935833
theorem B7054073 : Blo 2089435 7054073 := bstep (se 2 (by rfl) ⟨2645277, by rfl⟩ : syracuseStep 7054073 = 5290555) B5290555
theorem B4702715 : Blo 2089435 4702715 := bstep (se 1 (by rfl) ⟨3527036, by rfl⟩ : syracuseStep 4702715 = 7054073) B7054073
theorem B3135143 : Blo 2089435 3135143 := bstep (se 1 (by rfl) ⟨2351357, by rfl⟩ : syracuseStep 3135143 = 4702715) B4702715
theorem B2090095 : Blo 2089435 2090095 := bstep (se 1 (by rfl) ⟨1567571, by rfl⟩ : syracuseStep 2090095 = 3135143) B3135143
theorem B3135149 : Blo 2089435 3135149 := bbase (se 3 (by rfl) ⟨587840, by rfl⟩ : syracuseStep 3135149 = 1175681) (by norm_num)
theorem B2090099 : Blo 2089435 2090099 := bstep (se 1 (by rfl) ⟨1567574, by rfl⟩ : syracuseStep 2090099 = 3135149) B3135149
theorem B4702733 : Blo 2089435 4702733 := bbase (se 3 (by rfl) ⟨881762, by rfl⟩ : syracuseStep 4702733 = 1763525) (by norm_num)
theorem B3135155 : Blo 2089435 3135155 := bstep (se 1 (by rfl) ⟨2351366, by rfl⟩ : syracuseStep 3135155 = 4702733) B4702733
theorem B2090103 : Blo 2089435 2090103 := bstep (se 1 (by rfl) ⟨1567577, by rfl⟩ : syracuseStep 2090103 = 3135155) B3135155
theorem B2645293 : Blo 2089435 2645293 := bbase (se 3 (by rfl) ⟨495992, by rfl⟩ : syracuseStep 2645293 = 991985) (by norm_num)
theorem B3527057 : Blo 2089435 3527057 := bstep (se 2 (by rfl) ⟨1322646, by rfl⟩ : syracuseStep 3527057 = 2645293) B2645293
theorem B2351371 : Blo 2089435 2351371 := bstep (se 1 (by rfl) ⟨1763528, by rfl⟩ : syracuseStep 2351371 = 3527057) B3527057
theorem B3135161 : Blo 2089435 3135161 := bstep (se 2 (by rfl) ⟨1175685, by rfl⟩ : syracuseStep 3135161 = 2351371) B2351371
theorem B2090107 : Blo 2089435 2090107 := bstep (se 1 (by rfl) ⟨1567580, by rfl⟩ : syracuseStep 2090107 = 3135161) B3135161
theorem B5021933 : Blo 2089435 5021933 := bbase (se 3 (by rfl) ⟨941612, by rfl⟩ : syracuseStep 5021933 = 1883225) (by norm_num)
theorem B13391821 : Blo 2089435 13391821 := bstep (se 3 (by rfl) ⟨2510966, by rfl⟩ : syracuseStep 13391821 = 5021933) B5021933
theorem B17855761 : Blo 2089435 17855761 := bstep (se 2 (by rfl) ⟨6695910, by rfl⟩ : syracuseStep 17855761 = 13391821) B13391821
theorem B23807681 : Blo 2089435 23807681 := bstep (se 2 (by rfl) ⟨8927880, by rfl⟩ : syracuseStep 23807681 = 17855761) B17855761
theorem B15871787 : Blo 2089435 15871787 := bstep (se 1 (by rfl) ⟨11903840, by rfl⟩ : syracuseStep 15871787 = 23807681) B23807681
theorem B10581191 : Blo 2089435 10581191 := bstep (se 1 (by rfl) ⟨7935893, by rfl⟩ : syracuseStep 10581191 = 15871787) B15871787
theorem B7054127 : Blo 2089435 7054127 := bstep (se 1 (by rfl) ⟨5290595, by rfl⟩ : syracuseStep 7054127 = 10581191) B10581191
theorem B4702751 : Blo 2089435 4702751 := bstep (se 1 (by rfl) ⟨3527063, by rfl⟩ : syracuseStep 4702751 = 7054127) B7054127
theorem B3135167 : Blo 2089435 3135167 := bstep (se 1 (by rfl) ⟨2351375, by rfl⟩ : syracuseStep 3135167 = 4702751) B4702751
theorem B2090111 : Blo 2089435 2090111 := bstep (se 1 (by rfl) ⟨1567583, by rfl⟩ : syracuseStep 2090111 = 3135167) B3135167
theorem B3135173 : Blo 2089435 3135173 := bbase (se 4 (by rfl) ⟨293922, by rfl⟩ : syracuseStep 3135173 = 587845) (by norm_num)
theorem B2090115 : Blo 2089435 2090115 := bstep (se 1 (by rfl) ⟨1567586, by rfl⟩ : syracuseStep 2090115 = 3135173) B3135173
theorem B3527077 : Blo 2089435 3527077 := bbase (se 4 (by rfl) ⟨330663, by rfl⟩ : syracuseStep 3527077 = 661327) (by norm_num)
theorem B4702769 : Blo 2089435 4702769 := bstep (se 2 (by rfl) ⟨1763538, by rfl⟩ : syracuseStep 4702769 = 3527077) B3527077
theorem B3135179 : Blo 2089435 3135179 := bstep (se 1 (by rfl) ⟨2351384, by rfl⟩ : syracuseStep 3135179 = 4702769) B4702769
theorem B2090119 : Blo 2089435 2090119 := bstep (se 1 (by rfl) ⟨1567589, by rfl⟩ : syracuseStep 2090119 = 3135179) B3135179
theorem B2351389 : Blo 2089435 2351389 := bbase (se 3 (by rfl) ⟨440885, by rfl⟩ : syracuseStep 2351389 = 881771) (by norm_num)
theorem B3135185 : Blo 2089435 3135185 := bstep (se 2 (by rfl) ⟨1175694, by rfl⟩ : syracuseStep 3135185 = 2351389) B2351389
theorem B2090123 : Blo 2089435 2090123 := bstep (se 1 (by rfl) ⟨1567592, by rfl⟩ : syracuseStep 2090123 = 3135185) B3135185
theorem B7054181 : Blo 2089435 7054181 := bbase (se 4 (by rfl) ⟨661329, by rfl⟩ : syracuseStep 7054181 = 1322659) (by norm_num)
theorem B4702787 : Blo 2089435 4702787 := bstep (se 1 (by rfl) ⟨3527090, by rfl⟩ : syracuseStep 4702787 = 7054181) B7054181
theorem B3135191 : Blo 2089435 3135191 := bstep (se 1 (by rfl) ⟨2351393, by rfl⟩ : syracuseStep 3135191 = 4702787) B4702787
theorem B2090127 : Blo 2089435 2090127 := bstep (se 1 (by rfl) ⟨1567595, by rfl⟩ : syracuseStep 2090127 = 3135191) B3135191
theorem B3135197 : Blo 2089435 3135197 := bbase (se 3 (by rfl) ⟨587849, by rfl⟩ : syracuseStep 3135197 = 1175699) (by norm_num)
theorem B2090131 : Blo 2089435 2090131 := bstep (se 1 (by rfl) ⟨1567598, by rfl⟩ : syracuseStep 2090131 = 3135197) B3135197
theorem B4702805 : Blo 2089435 4702805 := bbase (se 8 (by rfl) ⟨27555, by rfl⟩ : syracuseStep 4702805 = 55111) (by norm_num)
theorem B3135203 : Blo 2089435 3135203 := bstep (se 1 (by rfl) ⟨2351402, by rfl⟩ : syracuseStep 3135203 = 4702805) B4702805
theorem B2090135 : Blo 2089435 2090135 := bstep (se 1 (by rfl) ⟨1567601, by rfl⟩ : syracuseStep 2090135 = 3135203) B3135203
theorem B2511001 : Blo 2089435 2511001 := bbase (se 2 (by rfl) ⟨941625, by rfl⟩ : syracuseStep 2511001 = 1883251) (by norm_num)
theorem B3348001 : Blo 2089435 3348001 := bstep (se 2 (by rfl) ⟨1255500, by rfl⟩ : syracuseStep 3348001 = 2511001) B2511001
theorem B4464001 : Blo 2089435 4464001 := bstep (se 2 (by rfl) ⟨1674000, by rfl⟩ : syracuseStep 4464001 = 3348001) B3348001
theorem B5952001 : Blo 2089435 5952001 := bstep (se 2 (by rfl) ⟨2232000, by rfl⟩ : syracuseStep 5952001 = 4464001) B4464001
theorem B7936001 : Blo 2089435 7936001 := bstep (se 2 (by rfl) ⟨2976000, by rfl⟩ : syracuseStep 7936001 = 5952001) B5952001
theorem B5290667 : Blo 2089435 5290667 := bstep (se 1 (by rfl) ⟨3968000, by rfl⟩ : syracuseStep 5290667 = 7936001) B7936001
theorem B3527111 : Blo 2089435 3527111 := bstep (se 1 (by rfl) ⟨2645333, by rfl⟩ : syracuseStep 3527111 = 5290667) B5290667
theorem B2351407 : Blo 2089435 2351407 := bstep (se 1 (by rfl) ⟨1763555, by rfl⟩ : syracuseStep 2351407 = 3527111) B3527111
theorem B3135209 : Blo 2089435 3135209 := bstep (se 2 (by rfl) ⟨1175703, by rfl⟩ : syracuseStep 3135209 = 2351407) B2351407
theorem B2090139 : Blo 2089435 2090139 := bstep (se 1 (by rfl) ⟨1567604, by rfl⟩ : syracuseStep 2090139 = 3135209) B3135209
theorem B2511005 : Blo 2089435 2511005 := bbase (se 3 (by rfl) ⟨470813, by rfl⟩ : syracuseStep 2511005 = 941627) (by norm_num)
theorem B26784053 : Blo 2089435 26784053 := bstep (se 5 (by rfl) ⟨1255502, by rfl⟩ : syracuseStep 26784053 = 2511005) B2511005
theorem B17856035 : Blo 2089435 17856035 := bstep (se 1 (by rfl) ⟨13392026, by rfl⟩ : syracuseStep 17856035 = 26784053) B26784053
theorem B11904023 : Blo 2089435 11904023 := bstep (se 1 (by rfl) ⟨8928017, by rfl⟩ : syracuseStep 11904023 = 17856035) B17856035
theorem B7936015 : Blo 2089435 7936015 := bstep (se 1 (by rfl) ⟨5952011, by rfl⟩ : syracuseStep 7936015 = 11904023) B11904023
theorem B10581353 : Blo 2089435 10581353 := bstep (se 2 (by rfl) ⟨3968007, by rfl⟩ : syracuseStep 10581353 = 7936015) B7936015
theorem B7054235 : Blo 2089435 7054235 := bstep (se 1 (by rfl) ⟨5290676, by rfl⟩ : syracuseStep 7054235 = 10581353) B10581353
theorem B4702823 : Blo 2089435 4702823 := bstep (se 1 (by rfl) ⟨3527117, by rfl⟩ : syracuseStep 4702823 = 7054235) B7054235
theorem B3135215 : Blo 2089435 3135215 := bstep (se 1 (by rfl) ⟨2351411, by rfl⟩ : syracuseStep 3135215 = 4702823) B4702823
theorem B2090143 : Blo 2089435 2090143 := bstep (se 1 (by rfl) ⟨1567607, by rfl⟩ : syracuseStep 2090143 = 3135215) B3135215
theorem B3135221 : Blo 2089435 3135221 := bbase (se 5 (by rfl) ⟨146963, by rfl⟩ : syracuseStep 3135221 = 293927) (by norm_num)
theorem B2090147 : Blo 2089435 2090147 := bstep (se 1 (by rfl) ⟨1567610, by rfl⟩ : syracuseStep 2090147 = 3135221) B3135221
theorem B8928053 : Blo 2089435 8928053 := bbase (se 5 (by rfl) ⟨418502, by rfl⟩ : syracuseStep 8928053 = 837005) (by norm_num)
theorem B5952035 : Blo 2089435 5952035 := bstep (se 1 (by rfl) ⟨4464026, by rfl⟩ : syracuseStep 5952035 = 8928053) B8928053
theorem B3968023 : Blo 2089435 3968023 := bstep (se 1 (by rfl) ⟨2976017, by rfl⟩ : syracuseStep 3968023 = 5952035) B5952035
theorem B5290697 : Blo 2089435 5290697 := bstep (se 2 (by rfl) ⟨1984011, by rfl⟩ : syracuseStep 5290697 = 3968023) B3968023
theorem B3527131 : Blo 2089435 3527131 := bstep (se 1 (by rfl) ⟨2645348, by rfl⟩ : syracuseStep 3527131 = 5290697) B5290697
theorem B4702841 : Blo 2089435 4702841 := bstep (se 2 (by rfl) ⟨1763565, by rfl⟩ : syracuseStep 4702841 = 3527131) B3527131
theorem B3135227 : Blo 2089435 3135227 := bstep (se 1 (by rfl) ⟨2351420, by rfl⟩ : syracuseStep 3135227 = 4702841) B4702841
theorem B2090151 : Blo 2089435 2090151 := bstep (se 1 (by rfl) ⟨1567613, by rfl⟩ : syracuseStep 2090151 = 3135227) B3135227
theorem B2351425 : Blo 2089435 2351425 := bbase (se 2 (by rfl) ⟨881784, by rfl⟩ : syracuseStep 2351425 = 1763569) (by norm_num)
theorem B3135233 : Blo 2089435 3135233 := bstep (se 2 (by rfl) ⟨1175712, by rfl⟩ : syracuseStep 3135233 = 2351425) B2351425
theorem B2090155 : Blo 2089435 2090155 := bstep (se 1 (by rfl) ⟨1567616, by rfl⟩ : syracuseStep 2090155 = 3135233) B3135233
theorem B5290717 : Blo 2089435 5290717 := bbase (se 3 (by rfl) ⟨992009, by rfl⟩ : syracuseStep 5290717 = 1984019) (by norm_num)
theorem B7054289 : Blo 2089435 7054289 := bstep (se 2 (by rfl) ⟨2645358, by rfl⟩ : syracuseStep 7054289 = 5290717) B5290717
theorem B4702859 : Blo 2089435 4702859 := bstep (se 1 (by rfl) ⟨3527144, by rfl⟩ : syracuseStep 4702859 = 7054289) B7054289
theorem B3135239 : Blo 2089435 3135239 := bstep (se 1 (by rfl) ⟨2351429, by rfl⟩ : syracuseStep 3135239 = 4702859) B4702859
theorem B2090159 : Blo 2089435 2090159 := bstep (se 1 (by rfl) ⟨1567619, by rfl⟩ : syracuseStep 2090159 = 3135239) B3135239
theorem B3135245 : Blo 2089435 3135245 := bbase (se 3 (by rfl) ⟨587858, by rfl⟩ : syracuseStep 3135245 = 1175717) (by norm_num)
theorem B2090163 : Blo 2089435 2090163 := bstep (se 1 (by rfl) ⟨1567622, by rfl⟩ : syracuseStep 2090163 = 3135245) B3135245
theorem B4702877 : Blo 2089435 4702877 := bbase (se 3 (by rfl) ⟨881789, by rfl⟩ : syracuseStep 4702877 = 1763579) (by norm_num)
theorem B3135251 : Blo 2089435 3135251 := bstep (se 1 (by rfl) ⟨2351438, by rfl⟩ : syracuseStep 3135251 = 4702877) B4702877
theorem B2090167 : Blo 2089435 2090167 := bstep (se 1 (by rfl) ⟨1567625, by rfl⟩ : syracuseStep 2090167 = 3135251) B3135251
theorem B3527165 : Blo 2089435 3527165 := bbase (se 3 (by rfl) ⟨661343, by rfl⟩ : syracuseStep 3527165 = 1322687) (by norm_num)
theorem B2351443 : Blo 2089435 2351443 := bstep (se 1 (by rfl) ⟨1763582, by rfl⟩ : syracuseStep 2351443 = 3527165) B3527165
theorem B3135257 : Blo 2089435 3135257 := bstep (se 2 (by rfl) ⟨1175721, by rfl⟩ : syracuseStep 3135257 = 2351443) B2351443
theorem B2090171 : Blo 2089435 2090171 := bstep (se 1 (by rfl) ⟨1567628, by rfl⟩ : syracuseStep 2090171 = 3135257) B3135257
theorem B4464077 : Blo 2089435 4464077 := bbase (se 3 (by rfl) ⟨837014, by rfl⟩ : syracuseStep 4464077 = 1674029) (by norm_num)
theorem B11904205 : Blo 2089435 11904205 := bstep (se 3 (by rfl) ⟨2232038, by rfl⟩ : syracuseStep 11904205 = 4464077) B4464077
theorem B15872273 : Blo 2089435 15872273 := bstep (se 2 (by rfl) ⟨5952102, by rfl⟩ : syracuseStep 15872273 = 11904205) B11904205
theorem B10581515 : Blo 2089435 10581515 := bstep (se 1 (by rfl) ⟨7936136, by rfl⟩ : syracuseStep 10581515 = 15872273) B15872273
theorem B7054343 : Blo 2089435 7054343 := bstep (se 1 (by rfl) ⟨5290757, by rfl⟩ : syracuseStep 7054343 = 10581515) B10581515
theorem B4702895 : Blo 2089435 4702895 := bstep (se 1 (by rfl) ⟨3527171, by rfl⟩ : syracuseStep 4702895 = 7054343) B7054343
theorem B3135263 : Blo 2089435 3135263 := bstep (se 1 (by rfl) ⟨2351447, by rfl⟩ : syracuseStep 3135263 = 4702895) B4702895
theorem B2090175 : Blo 2089435 2090175 := bstep (se 1 (by rfl) ⟨1567631, by rfl⟩ : syracuseStep 2090175 = 3135263) B3135263
theorem B3135269 : Blo 2089435 3135269 := bbase (se 4 (by rfl) ⟨293931, by rfl⟩ : syracuseStep 3135269 = 587863) (by norm_num)
theorem B2090179 : Blo 2089435 2090179 := bstep (se 1 (by rfl) ⟨1567634, by rfl⟩ : syracuseStep 2090179 = 3135269) B3135269
theorem B2645389 : Blo 2089435 2645389 := bbase (se 3 (by rfl) ⟨496010, by rfl⟩ : syracuseStep 2645389 = 992021) (by norm_num)
theorem B3527185 : Blo 2089435 3527185 := bstep (se 2 (by rfl) ⟨1322694, by rfl⟩ : syracuseStep 3527185 = 2645389) B2645389
theorem B4702913 : Blo 2089435 4702913 := bstep (se 2 (by rfl) ⟨1763592, by rfl⟩ : syracuseStep 4702913 = 3527185) B3527185
theorem B3135275 : Blo 2089435 3135275 := bstep (se 1 (by rfl) ⟨2351456, by rfl⟩ : syracuseStep 3135275 = 4702913) B4702913
theorem B2090183 : Blo 2089435 2090183 := bstep (se 1 (by rfl) ⟨1567637, by rfl⟩ : syracuseStep 2090183 = 3135275) B3135275
theorem B2351461 : Blo 2089435 2351461 := bbase (se 4 (by rfl) ⟨220449, by rfl⟩ : syracuseStep 2351461 = 440899) (by norm_num)
theorem B3135281 : Blo 2089435 3135281 := bstep (se 2 (by rfl) ⟨1175730, by rfl⟩ : syracuseStep 3135281 = 2351461) B2351461
theorem B2090187 : Blo 2089435 2090187 := bstep (se 1 (by rfl) ⟨1567640, by rfl⟩ : syracuseStep 2090187 = 3135281) B3135281
theorem B5952149 : Blo 2089435 5952149 := bbase (se 6 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 5952149 = 279007) (by norm_num)
theorem B3968099 : Blo 2089435 3968099 := bstep (se 1 (by rfl) ⟨2976074, by rfl⟩ : syracuseStep 3968099 = 5952149) B5952149
theorem B2645399 : Blo 2089435 2645399 := bstep (se 1 (by rfl) ⟨1984049, by rfl⟩ : syracuseStep 2645399 = 3968099) B3968099
theorem B7054397 : Blo 2089435 7054397 := bstep (se 3 (by rfl) ⟨1322699, by rfl⟩ : syracuseStep 7054397 = 2645399) B2645399
theorem B4702931 : Blo 2089435 4702931 := bstep (se 1 (by rfl) ⟨3527198, by rfl⟩ : syracuseStep 4702931 = 7054397) B7054397
theorem B3135287 : Blo 2089435 3135287 := bstep (se 1 (by rfl) ⟨2351465, by rfl⟩ : syracuseStep 3135287 = 4702931) B4702931
theorem B2090191 : Blo 2089435 2090191 := bstep (se 1 (by rfl) ⟨1567643, by rfl⟩ : syracuseStep 2090191 = 3135287) B3135287
theorem B3135293 : Blo 2089435 3135293 := bbase (se 3 (by rfl) ⟨587867, by rfl⟩ : syracuseStep 3135293 = 1175735) (by norm_num)
theorem B2090195 : Blo 2089435 2090195 := bstep (se 1 (by rfl) ⟨1567646, by rfl⟩ : syracuseStep 2090195 = 3135293) B3135293
theorem B4702949 : Blo 2089435 4702949 := bbase (se 4 (by rfl) ⟨440901, by rfl⟩ : syracuseStep 4702949 = 881803) (by norm_num)
theorem B3135299 : Blo 2089435 3135299 := bstep (se 1 (by rfl) ⟨2351474, by rfl⟩ : syracuseStep 3135299 = 4702949) B4702949
theorem B2090199 : Blo 2089435 2090199 := bstep (se 1 (by rfl) ⟨1567649, by rfl⟩ : syracuseStep 2090199 = 3135299) B3135299
theorem B5290829 : Blo 2089435 5290829 := bbase (se 3 (by rfl) ⟨992030, by rfl⟩ : syracuseStep 5290829 = 1984061) (by norm_num)
theorem B3527219 : Blo 2089435 3527219 := bstep (se 1 (by rfl) ⟨2645414, by rfl⟩ : syracuseStep 3527219 = 5290829) B5290829
theorem B2351479 : Blo 2089435 2351479 := bstep (se 1 (by rfl) ⟨1763609, by rfl⟩ : syracuseStep 2351479 = 3527219) B3527219
theorem B3135305 : Blo 2089435 3135305 := bstep (se 2 (by rfl) ⟨1175739, by rfl⟩ : syracuseStep 3135305 = 2351479) B2351479
theorem B2090203 : Blo 2089435 2090203 := bstep (se 1 (by rfl) ⟨1567652, by rfl⟩ : syracuseStep 2090203 = 3135305) B3135305
theorem B2232073 : Blo 2089435 2232073 := bbase (se 2 (by rfl) ⟨837027, by rfl⟩ : syracuseStep 2232073 = 1674055) (by norm_num)
theorem B2976097 : Blo 2089435 2976097 := bstep (se 2 (by rfl) ⟨1116036, by rfl⟩ : syracuseStep 2976097 = 2232073) B2232073
theorem B3968129 : Blo 2089435 3968129 := bstep (se 2 (by rfl) ⟨1488048, by rfl⟩ : syracuseStep 3968129 = 2976097) B2976097
theorem B10581677 : Blo 2089435 10581677 := bstep (se 3 (by rfl) ⟨1984064, by rfl⟩ : syracuseStep 10581677 = 3968129) B3968129
theorem B7054451 : Blo 2089435 7054451 := bstep (se 1 (by rfl) ⟨5290838, by rfl⟩ : syracuseStep 7054451 = 10581677) B10581677
theorem B4702967 : Blo 2089435 4702967 := bstep (se 1 (by rfl) ⟨3527225, by rfl⟩ : syracuseStep 4702967 = 7054451) B7054451
theorem B3135311 : Blo 2089435 3135311 := bstep (se 1 (by rfl) ⟨2351483, by rfl⟩ : syracuseStep 3135311 = 4702967) B4702967
theorem B2090207 : Blo 2089435 2090207 := bstep (se 1 (by rfl) ⟨1567655, by rfl⟩ : syracuseStep 2090207 = 3135311) B3135311
theorem B3135317 : Blo 2089435 3135317 := bbase (se 9 (by rfl) ⟨9185, by rfl⟩ : syracuseStep 3135317 = 18371) (by norm_num)
theorem B2090211 : Blo 2089435 2090211 := bstep (se 1 (by rfl) ⟨1567658, by rfl⟩ : syracuseStep 2090211 = 3135317) B3135317
theorem B6696245 : Blo 2089435 6696245 := bbase (se 5 (by rfl) ⟨313886, by rfl⟩ : syracuseStep 6696245 = 627773) (by norm_num)
theorem B4464163 : Blo 2089435 4464163 := bstep (se 1 (by rfl) ⟨3348122, by rfl⟩ : syracuseStep 4464163 = 6696245) B6696245
theorem B5952217 : Blo 2089435 5952217 := bstep (se 2 (by rfl) ⟨2232081, by rfl⟩ : syracuseStep 5952217 = 4464163) B4464163
theorem B7936289 : Blo 2089435 7936289 := bstep (se 2 (by rfl) ⟨2976108, by rfl⟩ : syracuseStep 7936289 = 5952217) B5952217
theorem B5290859 : Blo 2089435 5290859 := bstep (se 1 (by rfl) ⟨3968144, by rfl⟩ : syracuseStep 5290859 = 7936289) B7936289
theorem B3527239 : Blo 2089435 3527239 := bstep (se 1 (by rfl) ⟨2645429, by rfl⟩ : syracuseStep 3527239 = 5290859) B5290859
theorem B4702985 : Blo 2089435 4702985 := bstep (se 2 (by rfl) ⟨1763619, by rfl⟩ : syracuseStep 4702985 = 3527239) B3527239
theorem B3135323 : Blo 2089435 3135323 := bstep (se 1 (by rfl) ⟨2351492, by rfl⟩ : syracuseStep 3135323 = 4702985) B4702985
theorem B2090215 : Blo 2089435 2090215 := bstep (se 1 (by rfl) ⟨1567661, by rfl⟩ : syracuseStep 2090215 = 3135323) B3135323
theorem B2351497 : Blo 2089435 2351497 := bbase (se 2 (by rfl) ⟨881811, by rfl⟩ : syracuseStep 2351497 = 1763623) (by norm_num)
theorem B3135329 : Blo 2089435 3135329 := bstep (se 2 (by rfl) ⟨1175748, by rfl⟩ : syracuseStep 3135329 = 2351497) B2351497
theorem B2090219 : Blo 2089435 2090219 := bstep (se 1 (by rfl) ⟨1567664, by rfl⟩ : syracuseStep 2090219 = 3135329) B3135329
theorem B24463061 : Blo 2089435 24463061 := bbase (se 7 (by rfl) ⟨286676, by rfl⟩ : syracuseStep 24463061 = 573353) (by norm_num)
theorem B16308707 : Blo 2089435 16308707 := bstep (se 1 (by rfl) ⟨12231530, by rfl⟩ : syracuseStep 16308707 = 24463061) B24463061
theorem B43489885 : Blo 2089435 43489885 := bstep (se 3 (by rfl) ⟨8154353, by rfl⟩ : syracuseStep 43489885 = 16308707) B16308707
theorem B57986513 : Blo 2089435 57986513 := bstep (se 2 (by rfl) ⟨21744942, by rfl⟩ : syracuseStep 57986513 = 43489885) B43489885
theorem B38657675 : Blo 2089435 38657675 := bstep (se 1 (by rfl) ⟨28993256, by rfl⟩ : syracuseStep 38657675 = 57986513) B57986513
theorem B25771783 : Blo 2089435 25771783 := bstep (se 1 (by rfl) ⟨19328837, by rfl⟩ : syracuseStep 25771783 = 38657675) B38657675
theorem B34362377 : Blo 2089435 34362377 := bstep (se 2 (by rfl) ⟨12885891, by rfl⟩ : syracuseStep 34362377 = 25771783) B25771783
theorem B22908251 : Blo 2089435 22908251 := bstep (se 1 (by rfl) ⟨17181188, by rfl⟩ : syracuseStep 22908251 = 34362377) B34362377
theorem B15272167 : Blo 2089435 15272167 := bstep (se 1 (by rfl) ⟨11454125, by rfl⟩ : syracuseStep 15272167 = 22908251) B22908251
theorem B20362889 : Blo 2089435 20362889 := bstep (se 2 (by rfl) ⟨7636083, by rfl⟩ : syracuseStep 20362889 = 15272167) B15272167
theorem B13575259 : Blo 2089435 13575259 := bstep (se 1 (by rfl) ⟨10181444, by rfl⟩ : syracuseStep 13575259 = 20362889) B20362889
theorem B18100345 : Blo 2089435 18100345 := bstep (se 2 (by rfl) ⟨6787629, by rfl⟩ : syracuseStep 18100345 = 13575259) B13575259
theorem B24133793 : Blo 2089435 24133793 := bstep (se 2 (by rfl) ⟨9050172, by rfl⟩ : syracuseStep 24133793 = 18100345) B18100345
theorem B64356781 : Blo 2089435 64356781 := bstep (se 3 (by rfl) ⟨12066896, by rfl⟩ : syracuseStep 64356781 = 24133793) B24133793
theorem B85809041 : Blo 2089435 85809041 := bstep (se 2 (by rfl) ⟨32178390, by rfl⟩ : syracuseStep 85809041 = 64356781) B64356781
theorem B57206027 : Blo 2089435 57206027 := bstep (se 1 (by rfl) ⟨42904520, by rfl⟩ : syracuseStep 57206027 = 85809041) B85809041
theorem B38137351 : Blo 2089435 38137351 := bstep (se 1 (by rfl) ⟨28603013, by rfl⟩ : syracuseStep 38137351 = 57206027) B57206027
theorem B50849801 : Blo 2089435 50849801 := bstep (se 2 (by rfl) ⟨19068675, by rfl⟩ : syracuseStep 50849801 = 38137351) B38137351
theorem B33899867 : Blo 2089435 33899867 := bstep (se 1 (by rfl) ⟨25424900, by rfl⟩ : syracuseStep 33899867 = 50849801) B50849801
theorem B22599911 : Blo 2089435 22599911 := bstep (se 1 (by rfl) ⟨16949933, by rfl⟩ : syracuseStep 22599911 = 33899867) B33899867
theorem B60266429 : Blo 2089435 60266429 := bstep (se 3 (by rfl) ⟨11299955, by rfl⟩ : syracuseStep 60266429 = 22599911) B22599911
theorem B40177619 : Blo 2089435 40177619 := bstep (se 1 (by rfl) ⟨30133214, by rfl⟩ : syracuseStep 40177619 = 60266429) B60266429
theorem B26785079 : Blo 2089435 26785079 := bstep (se 1 (by rfl) ⟨20088809, by rfl⟩ : syracuseStep 26785079 = 40177619) B40177619
theorem B17856719 : Blo 2089435 17856719 := bstep (se 1 (by rfl) ⟨13392539, by rfl⟩ : syracuseStep 17856719 = 26785079) B26785079
theorem B11904479 : Blo 2089435 11904479 := bstep (se 1 (by rfl) ⟨8928359, by rfl⟩ : syracuseStep 11904479 = 17856719) B17856719
theorem B7936319 : Blo 2089435 7936319 := bstep (se 1 (by rfl) ⟨5952239, by rfl⟩ : syracuseStep 7936319 = 11904479) B11904479
theorem B5290879 : Blo 2089435 5290879 := bstep (se 1 (by rfl) ⟨3968159, by rfl⟩ : syracuseStep 5290879 = 7936319) B7936319
theorem B7054505 : Blo 2089435 7054505 := bstep (se 2 (by rfl) ⟨2645439, by rfl⟩ : syracuseStep 7054505 = 5290879) B5290879
theorem B4703003 : Blo 2089435 4703003 := bstep (se 1 (by rfl) ⟨3527252, by rfl⟩ : syracuseStep 4703003 = 7054505) B7054505
theorem B3135335 : Blo 2089435 3135335 := bstep (se 1 (by rfl) ⟨2351501, by rfl⟩ : syracuseStep 3135335 = 4703003) B4703003
theorem B2090223 : Blo 2089435 2090223 := bstep (se 1 (by rfl) ⟨1567667, by rfl⟩ : syracuseStep 2090223 = 3135335) B3135335
theorem B3135341 : Blo 2089435 3135341 := bbase (se 3 (by rfl) ⟨587876, by rfl⟩ : syracuseStep 3135341 = 1175753) (by norm_num)
theorem B2090227 : Blo 2089435 2090227 := bstep (se 1 (by rfl) ⟨1567670, by rfl⟩ : syracuseStep 2090227 = 3135341) B3135341
theorem B4703021 : Blo 2089435 4703021 := bbase (se 3 (by rfl) ⟨881816, by rfl⟩ : syracuseStep 4703021 = 1763633) (by norm_num)
theorem B3135347 : Blo 2089435 3135347 := bstep (se 1 (by rfl) ⟨2351510, by rfl⟩ : syracuseStep 3135347 = 4703021) B4703021
theorem B2090231 : Blo 2089435 2090231 := bstep (se 1 (by rfl) ⟨1567673, by rfl⟩ : syracuseStep 2090231 = 3135347) B3135347
theorem B3178133 : Blo 2089435 3178133 := bbase (se 6 (by rfl) ⟨74487, by rfl⟩ : syracuseStep 3178133 = 148975) (by norm_num)
theorem B2118755 : Blo 2089435 2118755 := bstep (se 1 (by rfl) ⟨1589066, by rfl⟩ : syracuseStep 2118755 = 3178133) B3178133
theorem B5650013 : Blo 2089435 5650013 := bstep (se 3 (by rfl) ⟨1059377, by rfl⟩ : syracuseStep 5650013 = 2118755) B2118755
theorem B3766675 : Blo 2089435 3766675 := bstep (se 1 (by rfl) ⟨2825006, by rfl⟩ : syracuseStep 3766675 = 5650013) B5650013
theorem B5022233 : Blo 2089435 5022233 := bstep (se 2 (by rfl) ⟨1883337, by rfl⟩ : syracuseStep 5022233 = 3766675) B3766675
theorem B3348155 : Blo 2089435 3348155 := bstep (se 1 (by rfl) ⟨2511116, by rfl⟩ : syracuseStep 3348155 = 5022233) B5022233
theorem B8928413 : Blo 2089435 8928413 := bstep (se 3 (by rfl) ⟨1674077, by rfl⟩ : syracuseStep 8928413 = 3348155) B3348155
theorem B5952275 : Blo 2089435 5952275 := bstep (se 1 (by rfl) ⟨4464206, by rfl⟩ : syracuseStep 5952275 = 8928413) B8928413
theorem B3968183 : Blo 2089435 3968183 := bstep (se 1 (by rfl) ⟨2976137, by rfl⟩ : syracuseStep 3968183 = 5952275) B5952275
theorem B2645455 : Blo 2089435 2645455 := bstep (se 1 (by rfl) ⟨1984091, by rfl⟩ : syracuseStep 2645455 = 3968183) B3968183
theorem B3527273 : Blo 2089435 3527273 := bstep (se 2 (by rfl) ⟨1322727, by rfl⟩ : syracuseStep 3527273 = 2645455) B2645455
theorem B2351515 : Blo 2089435 2351515 := bstep (se 1 (by rfl) ⟨1763636, by rfl⟩ : syracuseStep 2351515 = 3527273) B3527273
theorem B3135353 : Blo 2089435 3135353 := bstep (se 2 (by rfl) ⟨1175757, by rfl⟩ : syracuseStep 3135353 = 2351515) B2351515
theorem B2090235 : Blo 2089435 2090235 := bstep (se 1 (by rfl) ⟨1567676, by rfl⟩ : syracuseStep 2090235 = 3135353) B3135353
theorem B5650021 : Blo 2089435 5650021 := bbase (se 4 (by rfl) ⟨529689, by rfl⟩ : syracuseStep 5650021 = 1059379) (by norm_num)
theorem B7533361 : Blo 2089435 7533361 := bstep (se 2 (by rfl) ⟨2825010, by rfl⟩ : syracuseStep 7533361 = 5650021) B5650021
theorem B10044481 : Blo 2089435 10044481 := bstep (se 2 (by rfl) ⟨3766680, by rfl⟩ : syracuseStep 10044481 = 7533361) B7533361
theorem B13392641 : Blo 2089435 13392641 := bstep (se 2 (by rfl) ⟨5022240, by rfl⟩ : syracuseStep 13392641 = 10044481) B10044481
theorem B35713709 : Blo 2089435 35713709 := bstep (se 3 (by rfl) ⟨6696320, by rfl⟩ : syracuseStep 35713709 = 13392641) B13392641
theorem B23809139 : Blo 2089435 23809139 := bstep (se 1 (by rfl) ⟨17856854, by rfl⟩ : syracuseStep 23809139 = 35713709) B35713709
theorem B15872759 : Blo 2089435 15872759 := bstep (se 1 (by rfl) ⟨11904569, by rfl⟩ : syracuseStep 15872759 = 23809139) B23809139
theorem B10581839 : Blo 2089435 10581839 := bstep (se 1 (by rfl) ⟨7936379, by rfl⟩ : syracuseStep 10581839 = 15872759) B15872759
theorem B7054559 : Blo 2089435 7054559 := bstep (se 1 (by rfl) ⟨5290919, by rfl⟩ : syracuseStep 7054559 = 10581839) B10581839
theorem B4703039 : Blo 2089435 4703039 := bstep (se 1 (by rfl) ⟨3527279, by rfl⟩ : syracuseStep 4703039 = 7054559) B7054559
theorem B3135359 : Blo 2089435 3135359 := bstep (se 1 (by rfl) ⟨2351519, by rfl⟩ : syracuseStep 3135359 = 4703039) B4703039
theorem B2090239 : Blo 2089435 2090239 := bstep (se 1 (by rfl) ⟨1567679, by rfl⟩ : syracuseStep 2090239 = 3135359) B3135359
theorem B3135365 : Blo 2089435 3135365 := bbase (se 4 (by rfl) ⟨293940, by rfl⟩ : syracuseStep 3135365 = 587881) (by norm_num)
theorem B2090243 : Blo 2089435 2090243 := bstep (se 1 (by rfl) ⟨1567682, by rfl⟩ : syracuseStep 2090243 = 3135365) B3135365
theorem B3527293 : Blo 2089435 3527293 := bbase (se 3 (by rfl) ⟨661367, by rfl⟩ : syracuseStep 3527293 = 1322735) (by norm_num)
theorem B4703057 : Blo 2089435 4703057 := bstep (se 2 (by rfl) ⟨1763646, by rfl⟩ : syracuseStep 4703057 = 3527293) B3527293
theorem B3135371 : Blo 2089435 3135371 := bstep (se 1 (by rfl) ⟨2351528, by rfl⟩ : syracuseStep 3135371 = 4703057) B4703057
theorem B2090247 : Blo 2089435 2090247 := bstep (se 1 (by rfl) ⟨1567685, by rfl⟩ : syracuseStep 2090247 = 3135371) B3135371
theorem B2351533 : Blo 2089435 2351533 := bbase (se 3 (by rfl) ⟨440912, by rfl⟩ : syracuseStep 2351533 = 881825) (by norm_num)
theorem B3135377 : Blo 2089435 3135377 := bstep (se 2 (by rfl) ⟨1175766, by rfl⟩ : syracuseStep 3135377 = 2351533) B2351533
theorem B2090251 : Blo 2089435 2090251 := bstep (se 1 (by rfl) ⟨1567688, by rfl⟩ : syracuseStep 2090251 = 3135377) B3135377
theorem B7054613 : Blo 2089435 7054613 := bbase (se 6 (by rfl) ⟨165342, by rfl⟩ : syracuseStep 7054613 = 330685) (by norm_num)
theorem B4703075 : Blo 2089435 4703075 := bstep (se 1 (by rfl) ⟨3527306, by rfl⟩ : syracuseStep 4703075 = 7054613) B7054613
theorem B3135383 : Blo 2089435 3135383 := bstep (se 1 (by rfl) ⟨2351537, by rfl⟩ : syracuseStep 3135383 = 4703075) B4703075
theorem B2090255 : Blo 2089435 2090255 := bstep (se 1 (by rfl) ⟨1567691, by rfl⟩ : syracuseStep 2090255 = 3135383) B3135383
theorem B3135389 : Blo 2089435 3135389 := bbase (se 3 (by rfl) ⟨587885, by rfl⟩ : syracuseStep 3135389 = 1175771) (by norm_num)
theorem B2090259 : Blo 2089435 2090259 := bstep (se 1 (by rfl) ⟨1567694, by rfl⟩ : syracuseStep 2090259 = 3135389) B3135389
theorem B4703093 : Blo 2089435 4703093 := bbase (se 5 (by rfl) ⟨220457, by rfl⟩ : syracuseStep 4703093 = 440915) (by norm_num)
theorem B3135395 : Blo 2089435 3135395 := bstep (se 1 (by rfl) ⟨2351546, by rfl⟩ : syracuseStep 3135395 = 4703093) B4703093
theorem B2090263 : Blo 2089435 2090263 := bstep (se 1 (by rfl) ⟨1567697, by rfl⟩ : syracuseStep 2090263 = 3135395) B3135395
theorem B16950293 : Blo 2089435 16950293 := bbase (se 6 (by rfl) ⟨397272, by rfl⟩ : syracuseStep 16950293 = 794545) (by norm_num)
theorem B11300195 : Blo 2089435 11300195 := bstep (se 1 (by rfl) ⟨8475146, by rfl⟩ : syracuseStep 11300195 = 16950293) B16950293
theorem B30133853 : Blo 2089435 30133853 := bstep (se 3 (by rfl) ⟨5650097, by rfl⟩ : syracuseStep 30133853 = 11300195) B11300195
theorem B20089235 : Blo 2089435 20089235 := bstep (se 1 (by rfl) ⟨15066926, by rfl⟩ : syracuseStep 20089235 = 30133853) B30133853
theorem B13392823 : Blo 2089435 13392823 := bstep (se 1 (by rfl) ⟨10044617, by rfl⟩ : syracuseStep 13392823 = 20089235) B20089235
theorem B17857097 : Blo 2089435 17857097 := bstep (se 2 (by rfl) ⟨6696411, by rfl⟩ : syracuseStep 17857097 = 13392823) B13392823
theorem B11904731 : Blo 2089435 11904731 := bstep (se 1 (by rfl) ⟨8928548, by rfl⟩ : syracuseStep 11904731 = 17857097) B17857097
theorem B7936487 : Blo 2089435 7936487 := bstep (se 1 (by rfl) ⟨5952365, by rfl⟩ : syracuseStep 7936487 = 11904731) B11904731
theorem B5290991 : Blo 2089435 5290991 := bstep (se 1 (by rfl) ⟨3968243, by rfl⟩ : syracuseStep 5290991 = 7936487) B7936487
theorem B3527327 : Blo 2089435 3527327 := bstep (se 1 (by rfl) ⟨2645495, by rfl⟩ : syracuseStep 3527327 = 5290991) B5290991
theorem B2351551 : Blo 2089435 2351551 := bstep (se 1 (by rfl) ⟨1763663, by rfl⟩ : syracuseStep 2351551 = 3527327) B3527327
theorem B3135401 : Blo 2089435 3135401 := bstep (se 2 (by rfl) ⟨1175775, by rfl⟩ : syracuseStep 3135401 = 2351551) B2351551
theorem B2090267 : Blo 2089435 2090267 := bstep (se 1 (by rfl) ⟨1567700, by rfl⟩ : syracuseStep 2090267 = 3135401) B3135401
theorem B7936501 : Blo 2089435 7936501 := bbase (se 5 (by rfl) ⟨372023, by rfl⟩ : syracuseStep 7936501 = 744047) (by norm_num)
theorem B10582001 : Blo 2089435 10582001 := bstep (se 2 (by rfl) ⟨3968250, by rfl⟩ : syracuseStep 10582001 = 7936501) B7936501
theorem B7054667 : Blo 2089435 7054667 := bstep (se 1 (by rfl) ⟨5291000, by rfl⟩ : syracuseStep 7054667 = 10582001) B10582001
theorem B4703111 : Blo 2089435 4703111 := bstep (se 1 (by rfl) ⟨3527333, by rfl⟩ : syracuseStep 4703111 = 7054667) B7054667
theorem B3135407 : Blo 2089435 3135407 := bstep (se 1 (by rfl) ⟨2351555, by rfl⟩ : syracuseStep 3135407 = 4703111) B4703111
theorem B2090271 : Blo 2089435 2090271 := bstep (se 1 (by rfl) ⟨1567703, by rfl⟩ : syracuseStep 2090271 = 3135407) B3135407
theorem B3135413 : Blo 2089435 3135413 := bbase (se 5 (by rfl) ⟨146972, by rfl⟩ : syracuseStep 3135413 = 293945) (by norm_num)
theorem B2090275 : Blo 2089435 2090275 := bstep (se 1 (by rfl) ⟨1567706, by rfl⟩ : syracuseStep 2090275 = 3135413) B3135413
theorem B5291021 : Blo 2089435 5291021 := bbase (se 3 (by rfl) ⟨992066, by rfl⟩ : syracuseStep 5291021 = 1984133) (by norm_num)
theorem B3527347 : Blo 2089435 3527347 := bstep (se 1 (by rfl) ⟨2645510, by rfl⟩ : syracuseStep 3527347 = 5291021) B5291021
theorem B4703129 : Blo 2089435 4703129 := bstep (se 2 (by rfl) ⟨1763673, by rfl⟩ : syracuseStep 4703129 = 3527347) B3527347
theorem B3135419 : Blo 2089435 3135419 := bstep (se 1 (by rfl) ⟨2351564, by rfl⟩ : syracuseStep 3135419 = 4703129) B4703129
theorem B2090279 : Blo 2089435 2090279 := bstep (se 1 (by rfl) ⟨1567709, by rfl⟩ : syracuseStep 2090279 = 3135419) B3135419
theorem B2351569 : Blo 2089435 2351569 := bbase (se 2 (by rfl) ⟨881838, by rfl⟩ : syracuseStep 2351569 = 1763677) (by norm_num)
theorem B3135425 : Blo 2089435 3135425 := bstep (se 2 (by rfl) ⟨1175784, by rfl⟩ : syracuseStep 3135425 = 2351569) B2351569
theorem B2090283 : Blo 2089435 2090283 := bstep (se 1 (by rfl) ⟨1567712, by rfl⟩ : syracuseStep 2090283 = 3135425) B3135425
theorem B4464317 : Blo 2089435 4464317 := bbase (se 3 (by rfl) ⟨837059, by rfl⟩ : syracuseStep 4464317 = 1674119) (by norm_num)
theorem B2976211 : Blo 2089435 2976211 := bstep (se 1 (by rfl) ⟨2232158, by rfl⟩ : syracuseStep 2976211 = 4464317) B4464317
theorem B3968281 : Blo 2089435 3968281 := bstep (se 2 (by rfl) ⟨1488105, by rfl⟩ : syracuseStep 3968281 = 2976211) B2976211
theorem B5291041 : Blo 2089435 5291041 := bstep (se 2 (by rfl) ⟨1984140, by rfl⟩ : syracuseStep 5291041 = 3968281) B3968281
theorem B7054721 : Blo 2089435 7054721 := bstep (se 2 (by rfl) ⟨2645520, by rfl⟩ : syracuseStep 7054721 = 5291041) B5291041
theorem B4703147 : Blo 2089435 4703147 := bstep (se 1 (by rfl) ⟨3527360, by rfl⟩ : syracuseStep 4703147 = 7054721) B7054721
theorem B3135431 : Blo 2089435 3135431 := bstep (se 1 (by rfl) ⟨2351573, by rfl⟩ : syracuseStep 3135431 = 4703147) B4703147
theorem B2090287 : Blo 2089435 2090287 := bstep (se 1 (by rfl) ⟨1567715, by rfl⟩ : syracuseStep 2090287 = 3135431) B3135431
theorem B3135437 : Blo 2089435 3135437 := bbase (se 3 (by rfl) ⟨587894, by rfl⟩ : syracuseStep 3135437 = 1175789) (by norm_num)
theorem B2090291 : Blo 2089435 2090291 := bstep (se 1 (by rfl) ⟨1567718, by rfl⟩ : syracuseStep 2090291 = 3135437) B3135437
theorem B4703165 : Blo 2089435 4703165 := bbase (se 3 (by rfl) ⟨881843, by rfl⟩ : syracuseStep 4703165 = 1763687) (by norm_num)
theorem B3135443 : Blo 2089435 3135443 := bstep (se 1 (by rfl) ⟨2351582, by rfl⟩ : syracuseStep 3135443 = 4703165) B4703165
theorem B2090295 : Blo 2089435 2090295 := bstep (se 1 (by rfl) ⟨1567721, by rfl⟩ : syracuseStep 2090295 = 3135443) B3135443
theorem B3527381 : Blo 2089435 3527381 := bbase (se 7 (by rfl) ⟨41336, by rfl⟩ : syracuseStep 3527381 = 82673) (by norm_num)
theorem B2351587 : Blo 2089435 2351587 := bstep (se 1 (by rfl) ⟨1763690, by rfl⟩ : syracuseStep 2351587 = 3527381) B3527381
theorem B3135449 : Blo 2089435 3135449 := bstep (se 2 (by rfl) ⟨1175793, by rfl⟩ : syracuseStep 3135449 = 2351587) B2351587
theorem B2090299 : Blo 2089435 2090299 := bstep (se 1 (by rfl) ⟨1567724, by rfl⟩ : syracuseStep 2090299 = 3135449) B3135449
theorem B4587005 : Blo 2089435 4587005 := bbase (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) (by norm_num)
theorem B3058003 : Blo 2089435 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B16309349 : Blo 2089435 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B10872899 : Blo 2089435 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B7248599 : Blo 2089435 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B4832399 : Blo 2089435 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B12886397 : Blo 2089435 12886397 := bstep (se 3 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 12886397 = 4832399) B4832399
theorem B8590931 : Blo 2089435 8590931 := bstep (se 1 (by rfl) ⟨6443198, by rfl⟩ : syracuseStep 8590931 = 12886397) B12886397
theorem B5727287 : Blo 2089435 5727287 := bstep (se 1 (by rfl) ⟨4295465, by rfl⟩ : syracuseStep 5727287 = 8590931) B8590931
theorem B3818191 : Blo 2089435 3818191 := bstep (se 1 (by rfl) ⟨2863643, by rfl⟩ : syracuseStep 3818191 = 5727287) B5727287
theorem B5090921 : Blo 2089435 5090921 := bstep (se 2 (by rfl) ⟨1909095, by rfl⟩ : syracuseStep 5090921 = 3818191) B3818191
theorem B3393947 : Blo 2089435 3393947 := bstep (se 1 (by rfl) ⟨2545460, by rfl⟩ : syracuseStep 3393947 = 5090921) B5090921
theorem B9050525 : Blo 2089435 9050525 := bstep (se 3 (by rfl) ⟨1696973, by rfl⟩ : syracuseStep 9050525 = 3393947) B3393947
theorem B6033683 : Blo 2089435 6033683 := bstep (se 1 (by rfl) ⟨4525262, by rfl⟩ : syracuseStep 6033683 = 9050525) B9050525
theorem B4022455 : Blo 2089435 4022455 := bstep (se 1 (by rfl) ⟨3016841, by rfl⟩ : syracuseStep 4022455 = 6033683) B6033683
theorem B5363273 : Blo 2089435 5363273 := bstep (se 2 (by rfl) ⟨2011227, by rfl⟩ : syracuseStep 5363273 = 4022455) B4022455
theorem B3575515 : Blo 2089435 3575515 := bstep (se 1 (by rfl) ⟨2681636, by rfl⟩ : syracuseStep 3575515 = 5363273) B5363273
theorem B4767353 : Blo 2089435 4767353 := bstep (se 2 (by rfl) ⟨1787757, by rfl⟩ : syracuseStep 4767353 = 3575515) B3575515
theorem B3178235 : Blo 2089435 3178235 := bstep (se 1 (by rfl) ⟨2383676, by rfl⟩ : syracuseStep 3178235 = 4767353) B4767353
theorem B8475293 : Blo 2089435 8475293 := bstep (se 3 (by rfl) ⟨1589117, by rfl⟩ : syracuseStep 8475293 = 3178235) B3178235
theorem B5650195 : Blo 2089435 5650195 := bstep (se 1 (by rfl) ⟨4237646, by rfl⟩ : syracuseStep 5650195 = 8475293) B8475293
theorem B7533593 : Blo 2089435 7533593 := bstep (se 2 (by rfl) ⟨2825097, by rfl⟩ : syracuseStep 7533593 = 5650195) B5650195
theorem B5022395 : Blo 2089435 5022395 := bstep (se 1 (by rfl) ⟨3766796, by rfl⟩ : syracuseStep 5022395 = 7533593) B7533593
theorem B3348263 : Blo 2089435 3348263 := bstep (se 1 (by rfl) ⟨2511197, by rfl⟩ : syracuseStep 3348263 = 5022395) B5022395
theorem B8928701 : Blo 2089435 8928701 := bstep (se 3 (by rfl) ⟨1674131, by rfl⟩ : syracuseStep 8928701 = 3348263) B3348263
theorem B5952467 : Blo 2089435 5952467 := bstep (se 1 (by rfl) ⟨4464350, by rfl⟩ : syracuseStep 5952467 = 8928701) B8928701
theorem B15873245 : Blo 2089435 15873245 := bstep (se 3 (by rfl) ⟨2976233, by rfl⟩ : syracuseStep 15873245 = 5952467) B5952467
theorem B10582163 : Blo 2089435 10582163 := bstep (se 1 (by rfl) ⟨7936622, by rfl⟩ : syracuseStep 10582163 = 15873245) B15873245
theorem B7054775 : Blo 2089435 7054775 := bstep (se 1 (by rfl) ⟨5291081, by rfl⟩ : syracuseStep 7054775 = 10582163) B10582163
theorem B4703183 : Blo 2089435 4703183 := bstep (se 1 (by rfl) ⟨3527387, by rfl⟩ : syracuseStep 4703183 = 7054775) B7054775
theorem B3135455 : Blo 2089435 3135455 := bstep (se 1 (by rfl) ⟨2351591, by rfl⟩ : syracuseStep 3135455 = 4703183) B4703183
theorem B2090303 : Blo 2089435 2090303 := bstep (se 1 (by rfl) ⟨1567727, by rfl⟩ : syracuseStep 2090303 = 3135455) B3135455
theorem B3135461 : Blo 2089435 3135461 := bbase (se 4 (by rfl) ⟨293949, by rfl⟩ : syracuseStep 3135461 = 587899) (by norm_num)
theorem B2090307 : Blo 2089435 2090307 := bstep (se 1 (by rfl) ⟨1567730, by rfl⟩ : syracuseStep 2090307 = 3135461) B3135461
theorem B21453173 : Blo 2089435 21453173 := bbase (se 5 (by rfl) ⟨1005617, by rfl⟩ : syracuseStep 21453173 = 2011235) (by norm_num)
theorem B14302115 : Blo 2089435 14302115 := bstep (se 1 (by rfl) ⟨10726586, by rfl⟩ : syracuseStep 14302115 = 21453173) B21453173
theorem B9534743 : Blo 2089435 9534743 := bstep (se 1 (by rfl) ⟨7151057, by rfl⟩ : syracuseStep 9534743 = 14302115) B14302115
theorem B6356495 : Blo 2089435 6356495 := bstep (se 1 (by rfl) ⟨4767371, by rfl⟩ : syracuseStep 6356495 = 9534743) B9534743
theorem B16950653 : Blo 2089435 16950653 := bstep (se 3 (by rfl) ⟨3178247, by rfl⟩ : syracuseStep 16950653 = 6356495) B6356495
theorem B11300435 : Blo 2089435 11300435 := bstep (se 1 (by rfl) ⟨8475326, by rfl⟩ : syracuseStep 11300435 = 16950653) B16950653
theorem B7533623 : Blo 2089435 7533623 := bstep (se 1 (by rfl) ⟨5650217, by rfl⟩ : syracuseStep 7533623 = 11300435) B11300435
theorem B5022415 : Blo 2089435 5022415 := bstep (se 1 (by rfl) ⟨3766811, by rfl⟩ : syracuseStep 5022415 = 7533623) B7533623
theorem B6696553 : Blo 2089435 6696553 := bstep (se 2 (by rfl) ⟨2511207, by rfl⟩ : syracuseStep 6696553 = 5022415) B5022415
theorem B8928737 : Blo 2089435 8928737 := bstep (se 2 (by rfl) ⟨3348276, by rfl⟩ : syracuseStep 8928737 = 6696553) B6696553
theorem B5952491 : Blo 2089435 5952491 := bstep (se 1 (by rfl) ⟨4464368, by rfl⟩ : syracuseStep 5952491 = 8928737) B8928737
theorem B3968327 : Blo 2089435 3968327 := bstep (se 1 (by rfl) ⟨2976245, by rfl⟩ : syracuseStep 3968327 = 5952491) B5952491
theorem B2645551 : Blo 2089435 2645551 := bstep (se 1 (by rfl) ⟨1984163, by rfl⟩ : syracuseStep 2645551 = 3968327) B3968327
theorem B3527401 : Blo 2089435 3527401 := bstep (se 2 (by rfl) ⟨1322775, by rfl⟩ : syracuseStep 3527401 = 2645551) B2645551
theorem B4703201 : Blo 2089435 4703201 := bstep (se 2 (by rfl) ⟨1763700, by rfl⟩ : syracuseStep 4703201 = 3527401) B3527401
theorem B3135467 : Blo 2089435 3135467 := bstep (se 1 (by rfl) ⟨2351600, by rfl⟩ : syracuseStep 3135467 = 4703201) B4703201
theorem B2090311 : Blo 2089435 2090311 := bstep (se 1 (by rfl) ⟨1567733, by rfl⟩ : syracuseStep 2090311 = 3135467) B3135467
theorem B2351605 : Blo 2089435 2351605 := bbase (se 5 (by rfl) ⟨110231, by rfl⟩ : syracuseStep 2351605 = 220463) (by norm_num)
theorem B3135473 : Blo 2089435 3135473 := bstep (se 2 (by rfl) ⟨1175802, by rfl⟩ : syracuseStep 3135473 = 2351605) B2351605
theorem B2090315 : Blo 2089435 2090315 := bstep (se 1 (by rfl) ⟨1567736, by rfl⟩ : syracuseStep 2090315 = 3135473) B3135473
theorem B2645561 : Blo 2089435 2645561 := bbase (se 2 (by rfl) ⟨992085, by rfl⟩ : syracuseStep 2645561 = 1984171) (by norm_num)
theorem B7054829 : Blo 2089435 7054829 := bstep (se 3 (by rfl) ⟨1322780, by rfl⟩ : syracuseStep 7054829 = 2645561) B2645561
theorem B4703219 : Blo 2089435 4703219 := bstep (se 1 (by rfl) ⟨3527414, by rfl⟩ : syracuseStep 4703219 = 7054829) B7054829
theorem B3135479 : Blo 2089435 3135479 := bstep (se 1 (by rfl) ⟨2351609, by rfl⟩ : syracuseStep 3135479 = 4703219) B4703219
theorem B2090319 : Blo 2089435 2090319 := bstep (se 1 (by rfl) ⟨1567739, by rfl⟩ : syracuseStep 2090319 = 3135479) B3135479
theorem B3135485 : Blo 2089435 3135485 := bbase (se 3 (by rfl) ⟨587903, by rfl⟩ : syracuseStep 3135485 = 1175807) (by norm_num)
theorem B2090323 : Blo 2089435 2090323 := bstep (se 1 (by rfl) ⟨1567742, by rfl⟩ : syracuseStep 2090323 = 3135485) B3135485
theorem B4703237 : Blo 2089435 4703237 := bbase (se 4 (by rfl) ⟨440928, by rfl⟩ : syracuseStep 4703237 = 881857) (by norm_num)
theorem B3135491 : Blo 2089435 3135491 := bstep (se 1 (by rfl) ⟨2351618, by rfl⟩ : syracuseStep 3135491 = 4703237) B4703237
theorem B2090327 : Blo 2089435 2090327 := bstep (se 1 (by rfl) ⟨1567745, by rfl⟩ : syracuseStep 2090327 = 3135491) B3135491
theorem B3968365 : Blo 2089435 3968365 := bbase (se 3 (by rfl) ⟨744068, by rfl⟩ : syracuseStep 3968365 = 1488137) (by norm_num)
theorem B5291153 : Blo 2089435 5291153 := bstep (se 2 (by rfl) ⟨1984182, by rfl⟩ : syracuseStep 5291153 = 3968365) B3968365
theorem B3527435 : Blo 2089435 3527435 := bstep (se 1 (by rfl) ⟨2645576, by rfl⟩ : syracuseStep 3527435 = 5291153) B5291153
theorem B2351623 : Blo 2089435 2351623 := bstep (se 1 (by rfl) ⟨1763717, by rfl⟩ : syracuseStep 2351623 = 3527435) B3527435
theorem B3135497 : Blo 2089435 3135497 := bstep (se 2 (by rfl) ⟨1175811, by rfl⟩ : syracuseStep 3135497 = 2351623) B2351623
theorem B2090331 : Blo 2089435 2090331 := bstep (se 1 (by rfl) ⟨1567748, by rfl⟩ : syracuseStep 2090331 = 3135497) B3135497
theorem B10582325 : Blo 2089435 10582325 := bbase (se 5 (by rfl) ⟨496046, by rfl⟩ : syracuseStep 10582325 = 992093) (by norm_num)
theorem B7054883 : Blo 2089435 7054883 := bstep (se 1 (by rfl) ⟨5291162, by rfl⟩ : syracuseStep 7054883 = 10582325) B10582325
theorem B4703255 : Blo 2089435 4703255 := bstep (se 1 (by rfl) ⟨3527441, by rfl⟩ : syracuseStep 4703255 = 7054883) B7054883
theorem B3135503 : Blo 2089435 3135503 := bstep (se 1 (by rfl) ⟨2351627, by rfl⟩ : syracuseStep 3135503 = 4703255) B4703255
theorem B2090335 : Blo 2089435 2090335 := bstep (se 1 (by rfl) ⟨1567751, by rfl⟩ : syracuseStep 2090335 = 3135503) B3135503
theorem B3135509 : Blo 2089435 3135509 := bbase (se 6 (by rfl) ⟨73488, by rfl⟩ : syracuseStep 3135509 = 146977) (by norm_num)
theorem B2090339 : Blo 2089435 2090339 := bstep (se 1 (by rfl) ⟨1567754, by rfl⟩ : syracuseStep 2090339 = 3135509) B3135509
theorem B6788021 : Blo 2089435 6788021 := bbase (se 5 (by rfl) ⟨318188, by rfl⟩ : syracuseStep 6788021 = 636377) (by norm_num)
theorem B18101389 : Blo 2089435 18101389 := bstep (se 3 (by rfl) ⟨3394010, by rfl⟩ : syracuseStep 18101389 = 6788021) B6788021
theorem B24135185 : Blo 2089435 24135185 := bstep (se 2 (by rfl) ⟨9050694, by rfl⟩ : syracuseStep 24135185 = 18101389) B18101389
theorem B64360493 : Blo 2089435 64360493 := bstep (se 3 (by rfl) ⟨12067592, by rfl⟩ : syracuseStep 64360493 = 24135185) B24135185
theorem B42906995 : Blo 2089435 42906995 := bstep (se 1 (by rfl) ⟨32180246, by rfl⟩ : syracuseStep 42906995 = 64360493) B64360493
theorem B28604663 : Blo 2089435 28604663 := bstep (se 1 (by rfl) ⟨21453497, by rfl⟩ : syracuseStep 28604663 = 42906995) B42906995
theorem B19069775 : Blo 2089435 19069775 := bstep (se 1 (by rfl) ⟨14302331, by rfl⟩ : syracuseStep 19069775 = 28604663) B28604663
theorem B12713183 : Blo 2089435 12713183 := bstep (se 1 (by rfl) ⟨9534887, by rfl⟩ : syracuseStep 12713183 = 19069775) B19069775
theorem B8475455 : Blo 2089435 8475455 := bstep (se 1 (by rfl) ⟨6356591, by rfl⟩ : syracuseStep 8475455 = 12713183) B12713183
theorem B5650303 : Blo 2089435 5650303 := bstep (se 1 (by rfl) ⟨4237727, by rfl⟩ : syracuseStep 5650303 = 8475455) B8475455
theorem B7533737 : Blo 2089435 7533737 := bstep (se 2 (by rfl) ⟨2825151, by rfl⟩ : syracuseStep 7533737 = 5650303) B5650303
theorem B5022491 : Blo 2089435 5022491 := bstep (se 1 (by rfl) ⟨3766868, by rfl⟩ : syracuseStep 5022491 = 7533737) B7533737
theorem B13393309 : Blo 2089435 13393309 := bstep (se 3 (by rfl) ⟨2511245, by rfl⟩ : syracuseStep 13393309 = 5022491) B5022491
theorem B17857745 : Blo 2089435 17857745 := bstep (se 2 (by rfl) ⟨6696654, by rfl⟩ : syracuseStep 17857745 = 13393309) B13393309
theorem B11905163 : Blo 2089435 11905163 := bstep (se 1 (by rfl) ⟨8928872, by rfl⟩ : syracuseStep 11905163 = 17857745) B17857745
theorem B7936775 : Blo 2089435 7936775 := bstep (se 1 (by rfl) ⟨5952581, by rfl⟩ : syracuseStep 7936775 = 11905163) B11905163
theorem B5291183 : Blo 2089435 5291183 := bstep (se 1 (by rfl) ⟨3968387, by rfl⟩ : syracuseStep 5291183 = 7936775) B7936775
theorem B3527455 : Blo 2089435 3527455 := bstep (se 1 (by rfl) ⟨2645591, by rfl⟩ : syracuseStep 3527455 = 5291183) B5291183
theorem B4703273 : Blo 2089435 4703273 := bstep (se 2 (by rfl) ⟨1763727, by rfl⟩ : syracuseStep 4703273 = 3527455) B3527455
theorem B3135515 : Blo 2089435 3135515 := bstep (se 1 (by rfl) ⟨2351636, by rfl⟩ : syracuseStep 3135515 = 4703273) B4703273
theorem B2090343 : Blo 2089435 2090343 := bstep (se 1 (by rfl) ⟨1567757, by rfl⟩ : syracuseStep 2090343 = 3135515) B3135515
theorem B2351641 : Blo 2089435 2351641 := bbase (se 2 (by rfl) ⟨881865, by rfl⟩ : syracuseStep 2351641 = 1763731) (by norm_num)
theorem B3135521 : Blo 2089435 3135521 := bstep (se 2 (by rfl) ⟨1175820, by rfl⟩ : syracuseStep 3135521 = 2351641) B2351641
theorem B2090347 : Blo 2089435 2090347 := bstep (se 1 (by rfl) ⟨1567760, by rfl⟩ : syracuseStep 2090347 = 3135521) B3135521
theorem B7936805 : Blo 2089435 7936805 := bbase (se 4 (by rfl) ⟨744075, by rfl⟩ : syracuseStep 7936805 = 1488151) (by norm_num)
theorem B5291203 : Blo 2089435 5291203 := bstep (se 1 (by rfl) ⟨3968402, by rfl⟩ : syracuseStep 5291203 = 7936805) B7936805
theorem B7054937 : Blo 2089435 7054937 := bstep (se 2 (by rfl) ⟨2645601, by rfl⟩ : syracuseStep 7054937 = 5291203) B5291203
theorem B4703291 : Blo 2089435 4703291 := bstep (se 1 (by rfl) ⟨3527468, by rfl⟩ : syracuseStep 4703291 = 7054937) B7054937
theorem B3135527 : Blo 2089435 3135527 := bstep (se 1 (by rfl) ⟨2351645, by rfl⟩ : syracuseStep 3135527 = 4703291) B4703291
theorem B2090351 : Blo 2089435 2090351 := bstep (se 1 (by rfl) ⟨1567763, by rfl⟩ : syracuseStep 2090351 = 3135527) B3135527
theorem B3135533 : Blo 2089435 3135533 := bbase (se 3 (by rfl) ⟨587912, by rfl⟩ : syracuseStep 3135533 = 1175825) (by norm_num)
theorem B2090355 : Blo 2089435 2090355 := bstep (se 1 (by rfl) ⟨1567766, by rfl⟩ : syracuseStep 2090355 = 3135533) B3135533
theorem B4703309 : Blo 2089435 4703309 := bbase (se 3 (by rfl) ⟨881870, by rfl⟩ : syracuseStep 4703309 = 1763741) (by norm_num)
theorem B3135539 : Blo 2089435 3135539 := bstep (se 1 (by rfl) ⟨2351654, by rfl⟩ : syracuseStep 3135539 = 4703309) B4703309
theorem B2090359 : Blo 2089435 2090359 := bstep (se 1 (by rfl) ⟨1567769, by rfl⟩ : syracuseStep 2090359 = 3135539) B3135539
theorem B2645617 : Blo 2089435 2645617 := bbase (se 2 (by rfl) ⟨992106, by rfl⟩ : syracuseStep 2645617 = 1984213) (by norm_num)
theorem B3527489 : Blo 2089435 3527489 := bstep (se 2 (by rfl) ⟨1322808, by rfl⟩ : syracuseStep 3527489 = 2645617) B2645617
theorem B2351659 : Blo 2089435 2351659 := bstep (se 1 (by rfl) ⟨1763744, by rfl⟩ : syracuseStep 2351659 = 3527489) B3527489
theorem B3135545 : Blo 2089435 3135545 := bstep (se 2 (by rfl) ⟨1175829, by rfl⟩ : syracuseStep 3135545 = 2351659) B2351659
theorem B2090363 : Blo 2089435 2090363 := bstep (se 1 (by rfl) ⟨1567772, by rfl⟩ : syracuseStep 2090363 = 3135545) B3135545
theorem B2545537 : Blo 2089435 2545537 := bbase (se 2 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 2545537 = 1909153) (by norm_num)
theorem B3394049 : Blo 2089435 3394049 := bstep (se 2 (by rfl) ⟨1272768, by rfl⟩ : syracuseStep 3394049 = 2545537) B2545537
theorem B9050797 : Blo 2089435 9050797 := bstep (se 3 (by rfl) ⟨1697024, by rfl⟩ : syracuseStep 9050797 = 3394049) B3394049
theorem B48270917 : Blo 2089435 48270917 := bstep (se 4 (by rfl) ⟨4525398, by rfl⟩ : syracuseStep 48270917 = 9050797) B9050797
theorem B128722445 : Blo 2089435 128722445 := bstep (se 3 (by rfl) ⟨24135458, by rfl⟩ : syracuseStep 128722445 = 48270917) B48270917
theorem B85814963 : Blo 2089435 85814963 := bstep (se 1 (by rfl) ⟨64361222, by rfl⟩ : syracuseStep 85814963 = 128722445) B128722445
theorem B57209975 : Blo 2089435 57209975 := bstep (se 1 (by rfl) ⟨42907481, by rfl⟩ : syracuseStep 57209975 = 85814963) B85814963
theorem B38139983 : Blo 2089435 38139983 := bstep (se 1 (by rfl) ⟨28604987, by rfl⟩ : syracuseStep 38139983 = 57209975) B57209975
theorem B25426655 : Blo 2089435 25426655 := bstep (se 1 (by rfl) ⟨19069991, by rfl⟩ : syracuseStep 25426655 = 38139983) B38139983
theorem B16951103 : Blo 2089435 16951103 := bstep (se 1 (by rfl) ⟨12713327, by rfl⟩ : syracuseStep 16951103 = 25426655) B25426655
theorem B11300735 : Blo 2089435 11300735 := bstep (se 1 (by rfl) ⟨8475551, by rfl⟩ : syracuseStep 11300735 = 16951103) B16951103
theorem B7533823 : Blo 2089435 7533823 := bstep (se 1 (by rfl) ⟨5650367, by rfl⟩ : syracuseStep 7533823 = 11300735) B11300735
theorem B10045097 : Blo 2089435 10045097 := bstep (se 2 (by rfl) ⟨3766911, by rfl⟩ : syracuseStep 10045097 = 7533823) B7533823
theorem B6696731 : Blo 2089435 6696731 := bstep (se 1 (by rfl) ⟨5022548, by rfl⟩ : syracuseStep 6696731 = 10045097) B10045097
theorem B4464487 : Blo 2089435 4464487 := bstep (se 1 (by rfl) ⟨3348365, by rfl⟩ : syracuseStep 4464487 = 6696731) B6696731
theorem B23810597 : Blo 2089435 23810597 := bstep (se 4 (by rfl) ⟨2232243, by rfl⟩ : syracuseStep 23810597 = 4464487) B4464487
theorem B15873731 : Blo 2089435 15873731 := bstep (se 1 (by rfl) ⟨11905298, by rfl⟩ : syracuseStep 15873731 = 23810597) B23810597
theorem B10582487 : Blo 2089435 10582487 := bstep (se 1 (by rfl) ⟨7936865, by rfl⟩ : syracuseStep 10582487 = 15873731) B15873731
theorem B7054991 : Blo 2089435 7054991 := bstep (se 1 (by rfl) ⟨5291243, by rfl⟩ : syracuseStep 7054991 = 10582487) B10582487
theorem B4703327 : Blo 2089435 4703327 := bstep (se 1 (by rfl) ⟨3527495, by rfl⟩ : syracuseStep 4703327 = 7054991) B7054991
theorem B3135551 : Blo 2089435 3135551 := bstep (se 1 (by rfl) ⟨2351663, by rfl⟩ : syracuseStep 3135551 = 4703327) B4703327
theorem B2090367 : Blo 2089435 2090367 := bstep (se 1 (by rfl) ⟨1567775, by rfl⟩ : syracuseStep 2090367 = 3135551) B3135551
theorem B3135557 : Blo 2089435 3135557 := bbase (se 4 (by rfl) ⟨293958, by rfl⟩ : syracuseStep 3135557 = 587917) (by norm_num)
theorem B2090371 : Blo 2089435 2090371 := bstep (se 1 (by rfl) ⟨1567778, by rfl⟩ : syracuseStep 2090371 = 3135557) B3135557
theorem B3527509 : Blo 2089435 3527509 := bbase (se 9 (by rfl) ⟨10334, by rfl⟩ : syracuseStep 3527509 = 20669) (by norm_num)
theorem B4703345 : Blo 2089435 4703345 := bstep (se 2 (by rfl) ⟨1763754, by rfl⟩ : syracuseStep 4703345 = 3527509) B3527509
theorem B3135563 : Blo 2089435 3135563 := bstep (se 1 (by rfl) ⟨2351672, by rfl⟩ : syracuseStep 3135563 = 4703345) B4703345
theorem B2090375 : Blo 2089435 2090375 := bstep (se 1 (by rfl) ⟨1567781, by rfl⟩ : syracuseStep 2090375 = 3135563) B3135563
theorem B2351677 : Blo 2089435 2351677 := bbase (se 3 (by rfl) ⟨440939, by rfl⟩ : syracuseStep 2351677 = 881879) (by norm_num)
theorem B3135569 : Blo 2089435 3135569 := bstep (se 2 (by rfl) ⟨1175838, by rfl⟩ : syracuseStep 3135569 = 2351677) B2351677
theorem B2090379 : Blo 2089435 2090379 := bstep (se 1 (by rfl) ⟨1567784, by rfl⟩ : syracuseStep 2090379 = 3135569) B3135569
theorem B7055045 : Blo 2089435 7055045 := bbase (se 4 (by rfl) ⟨661410, by rfl⟩ : syracuseStep 7055045 = 1322821) (by norm_num)
theorem B4703363 : Blo 2089435 4703363 := bstep (se 1 (by rfl) ⟨3527522, by rfl⟩ : syracuseStep 4703363 = 7055045) B7055045
theorem B3135575 : Blo 2089435 3135575 := bstep (se 1 (by rfl) ⟨2351681, by rfl⟩ : syracuseStep 3135575 = 4703363) B4703363
theorem B2090383 : Blo 2089435 2090383 := bstep (se 1 (by rfl) ⟨1567787, by rfl⟩ : syracuseStep 2090383 = 3135575) B3135575
theorem B3135581 : Blo 2089435 3135581 := bbase (se 3 (by rfl) ⟨587921, by rfl⟩ : syracuseStep 3135581 = 1175843) (by norm_num)
theorem B2090387 : Blo 2089435 2090387 := bstep (se 1 (by rfl) ⟨1567790, by rfl⟩ : syracuseStep 2090387 = 3135581) B3135581
theorem B4703381 : Blo 2089435 4703381 := bbase (se 6 (by rfl) ⟨110235, by rfl⟩ : syracuseStep 4703381 = 220471) (by norm_num)
theorem B3135587 : Blo 2089435 3135587 := bstep (se 1 (by rfl) ⟨2351690, by rfl⟩ : syracuseStep 3135587 = 4703381) B4703381
theorem B2090391 : Blo 2089435 2090391 := bstep (se 1 (by rfl) ⟨1567793, by rfl⟩ : syracuseStep 2090391 = 3135587) B3135587
theorem B2976365 : Blo 2089435 2976365 := bbase (se 3 (by rfl) ⟨558068, by rfl⟩ : syracuseStep 2976365 = 1116137) (by norm_num)
theorem B7936973 : Blo 2089435 7936973 := bstep (se 3 (by rfl) ⟨1488182, by rfl⟩ : syracuseStep 7936973 = 2976365) B2976365
theorem B5291315 : Blo 2089435 5291315 := bstep (se 1 (by rfl) ⟨3968486, by rfl⟩ : syracuseStep 5291315 = 7936973) B7936973
theorem B3527543 : Blo 2089435 3527543 := bstep (se 1 (by rfl) ⟨2645657, by rfl⟩ : syracuseStep 3527543 = 5291315) B5291315
theorem B2351695 : Blo 2089435 2351695 := bstep (se 1 (by rfl) ⟨1763771, by rfl⟩ : syracuseStep 2351695 = 3527543) B3527543
theorem B3135593 : Blo 2089435 3135593 := bstep (se 2 (by rfl) ⟨1175847, by rfl⟩ : syracuseStep 3135593 = 2351695) B2351695
theorem B2090395 : Blo 2089435 2090395 := bstep (se 1 (by rfl) ⟨1567796, by rfl⟩ : syracuseStep 2090395 = 3135593) B3135593
theorem B3178381 : Blo 2089435 3178381 := bbase (se 3 (by rfl) ⟨595946, by rfl⟩ : syracuseStep 3178381 = 1191893) (by norm_num)
theorem B4237841 : Blo 2089435 4237841 := bstep (se 2 (by rfl) ⟨1589190, by rfl⟩ : syracuseStep 4237841 = 3178381) B3178381
theorem B2825227 : Blo 2089435 2825227 := bstep (se 1 (by rfl) ⟨2118920, by rfl⟩ : syracuseStep 2825227 = 4237841) B4237841
theorem B3766969 : Blo 2089435 3766969 := bstep (se 2 (by rfl) ⟨1412613, by rfl⟩ : syracuseStep 3766969 = 2825227) B2825227
theorem B20090501 : Blo 2089435 20090501 := bstep (se 4 (by rfl) ⟨1883484, by rfl⟩ : syracuseStep 20090501 = 3766969) B3766969
theorem B13393667 : Blo 2089435 13393667 := bstep (se 1 (by rfl) ⟨10045250, by rfl⟩ : syracuseStep 13393667 = 20090501) B20090501
theorem B8929111 : Blo 2089435 8929111 := bstep (se 1 (by rfl) ⟨6696833, by rfl⟩ : syracuseStep 8929111 = 13393667) B13393667
theorem B11905481 : Blo 2089435 11905481 := bstep (se 2 (by rfl) ⟨4464555, by rfl⟩ : syracuseStep 11905481 = 8929111) B8929111
theorem B7936987 : Blo 2089435 7936987 := bstep (se 1 (by rfl) ⟨5952740, by rfl⟩ : syracuseStep 7936987 = 11905481) B11905481
theorem B10582649 : Blo 2089435 10582649 := bstep (se 2 (by rfl) ⟨3968493, by rfl⟩ : syracuseStep 10582649 = 7936987) B7936987
theorem B7055099 : Blo 2089435 7055099 := bstep (se 1 (by rfl) ⟨5291324, by rfl⟩ : syracuseStep 7055099 = 10582649) B10582649
theorem B4703399 : Blo 2089435 4703399 := bstep (se 1 (by rfl) ⟨3527549, by rfl⟩ : syracuseStep 4703399 = 7055099) B7055099
theorem B3135599 : Blo 2089435 3135599 := bstep (se 1 (by rfl) ⟨2351699, by rfl⟩ : syracuseStep 3135599 = 4703399) B4703399
theorem B2090399 : Blo 2089435 2090399 := bstep (se 1 (by rfl) ⟨1567799, by rfl⟩ : syracuseStep 2090399 = 3135599) B3135599
theorem B3135605 : Blo 2089435 3135605 := bbase (se 5 (by rfl) ⟨146981, by rfl⟩ : syracuseStep 3135605 = 293963) (by norm_num)
theorem B2090403 : Blo 2089435 2090403 := bstep (se 1 (by rfl) ⟨1567802, by rfl⟩ : syracuseStep 2090403 = 3135605) B3135605
theorem B3968509 : Blo 2089435 3968509 := bbase (se 3 (by rfl) ⟨744095, by rfl⟩ : syracuseStep 3968509 = 1488191) (by norm_num)
theorem B5291345 : Blo 2089435 5291345 := bstep (se 2 (by rfl) ⟨1984254, by rfl⟩ : syracuseStep 5291345 = 3968509) B3968509
theorem B3527563 : Blo 2089435 3527563 := bstep (se 1 (by rfl) ⟨2645672, by rfl⟩ : syracuseStep 3527563 = 5291345) B5291345
theorem B4703417 : Blo 2089435 4703417 := bstep (se 2 (by rfl) ⟨1763781, by rfl⟩ : syracuseStep 4703417 = 3527563) B3527563
theorem B3135611 : Blo 2089435 3135611 := bstep (se 1 (by rfl) ⟨2351708, by rfl⟩ : syracuseStep 3135611 = 4703417) B4703417
theorem B2090407 : Blo 2089435 2090407 := bstep (se 1 (by rfl) ⟨1567805, by rfl⟩ : syracuseStep 2090407 = 3135611) B3135611
theorem B2351713 : Blo 2089435 2351713 := bbase (se 2 (by rfl) ⟨881892, by rfl⟩ : syracuseStep 2351713 = 1763785) (by norm_num)
theorem B3135617 : Blo 2089435 3135617 := bstep (se 2 (by rfl) ⟨1175856, by rfl⟩ : syracuseStep 3135617 = 2351713) B2351713
theorem B2090411 : Blo 2089435 2090411 := bstep (se 1 (by rfl) ⟨1567808, by rfl⟩ : syracuseStep 2090411 = 3135617) B3135617
theorem B5291365 : Blo 2089435 5291365 := bbase (se 4 (by rfl) ⟨496065, by rfl⟩ : syracuseStep 5291365 = 992131) (by norm_num)
theorem B7055153 : Blo 2089435 7055153 := bstep (se 2 (by rfl) ⟨2645682, by rfl⟩ : syracuseStep 7055153 = 5291365) B5291365
theorem B4703435 : Blo 2089435 4703435 := bstep (se 1 (by rfl) ⟨3527576, by rfl⟩ : syracuseStep 4703435 = 7055153) B7055153
theorem B3135623 : Blo 2089435 3135623 := bstep (se 1 (by rfl) ⟨2351717, by rfl⟩ : syracuseStep 3135623 = 4703435) B4703435
theorem B2090415 : Blo 2089435 2090415 := bstep (se 1 (by rfl) ⟨1567811, by rfl⟩ : syracuseStep 2090415 = 3135623) B3135623
theorem B3135629 : Blo 2089435 3135629 := bbase (se 3 (by rfl) ⟨587930, by rfl⟩ : syracuseStep 3135629 = 1175861) (by norm_num)
theorem B2090419 : Blo 2089435 2090419 := bstep (se 1 (by rfl) ⟨1567814, by rfl⟩ : syracuseStep 2090419 = 3135629) B3135629
theorem B4703453 : Blo 2089435 4703453 := bbase (se 3 (by rfl) ⟨881897, by rfl⟩ : syracuseStep 4703453 = 1763795) (by norm_num)
theorem B3135635 : Blo 2089435 3135635 := bstep (se 1 (by rfl) ⟨2351726, by rfl⟩ : syracuseStep 3135635 = 4703453) B4703453
theorem B2090423 : Blo 2089435 2090423 := bstep (se 1 (by rfl) ⟨1567817, by rfl⟩ : syracuseStep 2090423 = 3135635) B3135635
theorem B3527597 : Blo 2089435 3527597 := bbase (se 3 (by rfl) ⟨661424, by rfl⟩ : syracuseStep 3527597 = 1322849) (by norm_num)
theorem B2351731 : Blo 2089435 2351731 := bstep (se 1 (by rfl) ⟨1763798, by rfl⟩ : syracuseStep 2351731 = 3527597) B3527597
theorem B3135641 : Blo 2089435 3135641 := bstep (se 2 (by rfl) ⟨1175865, by rfl⟩ : syracuseStep 3135641 = 2351731) B2351731
theorem B2090427 : Blo 2089435 2090427 := bstep (se 1 (by rfl) ⟨1567820, by rfl⟩ : syracuseStep 2090427 = 3135641) B3135641
theorem B9665381 : Blo 2089435 9665381 := bbase (se 4 (by rfl) ⟨906129, by rfl⟩ : syracuseStep 9665381 = 1812259) (by norm_num)
theorem B6443587 : Blo 2089435 6443587 := bstep (se 1 (by rfl) ⟨4832690, by rfl⟩ : syracuseStep 6443587 = 9665381) B9665381
theorem B8591449 : Blo 2089435 8591449 := bstep (se 2 (by rfl) ⟨3221793, by rfl⟩ : syracuseStep 8591449 = 6443587) B6443587
theorem B11455265 : Blo 2089435 11455265 := bstep (se 2 (by rfl) ⟨4295724, by rfl⟩ : syracuseStep 11455265 = 8591449) B8591449
theorem B7636843 : Blo 2089435 7636843 := bstep (se 1 (by rfl) ⟨5727632, by rfl⟩ : syracuseStep 7636843 = 11455265) B11455265
theorem B10182457 : Blo 2089435 10182457 := bstep (se 2 (by rfl) ⟨3818421, by rfl⟩ : syracuseStep 10182457 = 7636843) B7636843
theorem B13576609 : Blo 2089435 13576609 := bstep (se 2 (by rfl) ⟨5091228, by rfl⟩ : syracuseStep 13576609 = 10182457) B10182457
theorem B18102145 : Blo 2089435 18102145 := bstep (se 2 (by rfl) ⟨6788304, by rfl⟩ : syracuseStep 18102145 = 13576609) B13576609
theorem B24136193 : Blo 2089435 24136193 := bstep (se 2 (by rfl) ⟨9051072, by rfl⟩ : syracuseStep 24136193 = 18102145) B18102145
theorem B16090795 : Blo 2089435 16090795 := bstep (se 1 (by rfl) ⟨12068096, by rfl⟩ : syracuseStep 16090795 = 24136193) B24136193
theorem B85817573 : Blo 2089435 85817573 := bstep (se 4 (by rfl) ⟨8045397, by rfl⟩ : syracuseStep 85817573 = 16090795) B16090795
theorem B57211715 : Blo 2089435 57211715 := bstep (se 1 (by rfl) ⟨42908786, by rfl⟩ : syracuseStep 57211715 = 85817573) B85817573
theorem B152564573 : Blo 2089435 152564573 := bstep (se 3 (by rfl) ⟨28605857, by rfl⟩ : syracuseStep 152564573 = 57211715) B57211715
theorem B101709715 : Blo 2089435 101709715 := bstep (se 1 (by rfl) ⟨76282286, by rfl⟩ : syracuseStep 101709715 = 152564573) B152564573
theorem B135612953 : Blo 2089435 135612953 := bstep (se 2 (by rfl) ⟨50854857, by rfl⟩ : syracuseStep 135612953 = 101709715) B101709715
theorem B90408635 : Blo 2089435 90408635 := bstep (se 1 (by rfl) ⟨67806476, by rfl⟩ : syracuseStep 90408635 = 135612953) B135612953
theorem B60272423 : Blo 2089435 60272423 := bstep (se 1 (by rfl) ⟨45204317, by rfl⟩ : syracuseStep 60272423 = 90408635) B90408635
theorem B40181615 : Blo 2089435 40181615 := bstep (se 1 (by rfl) ⟨30136211, by rfl⟩ : syracuseStep 40181615 = 60272423) B60272423
theorem B26787743 : Blo 2089435 26787743 := bstep (se 1 (by rfl) ⟨20090807, by rfl⟩ : syracuseStep 26787743 = 40181615) B40181615
theorem B17858495 : Blo 2089435 17858495 := bstep (se 1 (by rfl) ⟨13393871, by rfl⟩ : syracuseStep 17858495 = 26787743) B26787743
theorem B11905663 : Blo 2089435 11905663 := bstep (se 1 (by rfl) ⟨8929247, by rfl⟩ : syracuseStep 11905663 = 17858495) B17858495
theorem B15874217 : Blo 2089435 15874217 := bstep (se 2 (by rfl) ⟨5952831, by rfl⟩ : syracuseStep 15874217 = 11905663) B11905663
theorem B10582811 : Blo 2089435 10582811 := bstep (se 1 (by rfl) ⟨7937108, by rfl⟩ : syracuseStep 10582811 = 15874217) B15874217
theorem B7055207 : Blo 2089435 7055207 := bstep (se 1 (by rfl) ⟨5291405, by rfl⟩ : syracuseStep 7055207 = 10582811) B10582811
theorem B4703471 : Blo 2089435 4703471 := bstep (se 1 (by rfl) ⟨3527603, by rfl⟩ : syracuseStep 4703471 = 7055207) B7055207
theorem B3135647 : Blo 2089435 3135647 := bstep (se 1 (by rfl) ⟨2351735, by rfl⟩ : syracuseStep 3135647 = 4703471) B4703471
theorem B2090431 : Blo 2089435 2090431 := bstep (se 1 (by rfl) ⟨1567823, by rfl⟩ : syracuseStep 2090431 = 3135647) B3135647
theorem B3135653 : Blo 2089435 3135653 := bbase (se 4 (by rfl) ⟨293967, by rfl⟩ : syracuseStep 3135653 = 587935) (by norm_num)
theorem B2090435 : Blo 2089435 2090435 := bstep (se 1 (by rfl) ⟨1567826, by rfl⟩ : syracuseStep 2090435 = 3135653) B3135653
theorem B2645713 : Blo 2089435 2645713 := bbase (se 2 (by rfl) ⟨992142, by rfl⟩ : syracuseStep 2645713 = 1984285) (by norm_num)
theorem B3527617 : Blo 2089435 3527617 := bstep (se 2 (by rfl) ⟨1322856, by rfl⟩ : syracuseStep 3527617 = 2645713) B2645713
theorem B4703489 : Blo 2089435 4703489 := bstep (se 2 (by rfl) ⟨1763808, by rfl⟩ : syracuseStep 4703489 = 3527617) B3527617
theorem B3135659 : Blo 2089435 3135659 := bstep (se 1 (by rfl) ⟨2351744, by rfl⟩ : syracuseStep 3135659 = 4703489) B4703489
theorem B2090439 : Blo 2089435 2090439 := bstep (se 1 (by rfl) ⟨1567829, by rfl⟩ : syracuseStep 2090439 = 3135659) B3135659
theorem B2351749 : Blo 2089435 2351749 := bbase (se 4 (by rfl) ⟨220476, by rfl⟩ : syracuseStep 2351749 = 440953) (by norm_num)
theorem B3135665 : Blo 2089435 3135665 := bstep (se 2 (by rfl) ⟨1175874, by rfl⟩ : syracuseStep 3135665 = 2351749) B2351749
theorem B2090443 : Blo 2089435 2090443 := bstep (se 1 (by rfl) ⟨1567832, by rfl⟩ : syracuseStep 2090443 = 3135665) B3135665
theorem B2825293 : Blo 2089435 2825293 := bbase (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) (by norm_num)
theorem B3767057 : Blo 2089435 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B2511371 : Blo 2089435 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B6696989 : Blo 2089435 6696989 := bstep (se 3 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 6696989 = 2511371) B2511371
theorem B4464659 : Blo 2089435 4464659 := bstep (se 1 (by rfl) ⟨3348494, by rfl⟩ : syracuseStep 4464659 = 6696989) B6696989
theorem B2976439 : Blo 2089435 2976439 := bstep (se 1 (by rfl) ⟨2232329, by rfl⟩ : syracuseStep 2976439 = 4464659) B4464659
theorem B3968585 : Blo 2089435 3968585 := bstep (se 2 (by rfl) ⟨1488219, by rfl⟩ : syracuseStep 3968585 = 2976439) B2976439
theorem B2645723 : Blo 2089435 2645723 := bstep (se 1 (by rfl) ⟨1984292, by rfl⟩ : syracuseStep 2645723 = 3968585) B3968585
theorem B7055261 : Blo 2089435 7055261 := bstep (se 3 (by rfl) ⟨1322861, by rfl⟩ : syracuseStep 7055261 = 2645723) B2645723
theorem B4703507 : Blo 2089435 4703507 := bstep (se 1 (by rfl) ⟨3527630, by rfl⟩ : syracuseStep 4703507 = 7055261) B7055261
theorem B3135671 : Blo 2089435 3135671 := bstep (se 1 (by rfl) ⟨2351753, by rfl⟩ : syracuseStep 3135671 = 4703507) B4703507
theorem B2090447 : Blo 2089435 2090447 := bstep (se 1 (by rfl) ⟨1567835, by rfl⟩ : syracuseStep 2090447 = 3135671) B3135671
theorem B3135677 : Blo 2089435 3135677 := bbase (se 3 (by rfl) ⟨587939, by rfl⟩ : syracuseStep 3135677 = 1175879) (by norm_num)
theorem B2090451 : Blo 2089435 2090451 := bstep (se 1 (by rfl) ⟨1567838, by rfl⟩ : syracuseStep 2090451 = 3135677) B3135677
theorem B4703525 : Blo 2089435 4703525 := bbase (se 4 (by rfl) ⟨440955, by rfl⟩ : syracuseStep 4703525 = 881911) (by norm_num)
theorem B3135683 : Blo 2089435 3135683 := bstep (se 1 (by rfl) ⟨2351762, by rfl⟩ : syracuseStep 3135683 = 4703525) B4703525
theorem B2090455 : Blo 2089435 2090455 := bstep (se 1 (by rfl) ⟨1567841, by rfl⟩ : syracuseStep 2090455 = 3135683) B3135683
theorem B5291477 : Blo 2089435 5291477 := bbase (se 7 (by rfl) ⟨62009, by rfl⟩ : syracuseStep 5291477 = 124019) (by norm_num)
theorem B3527651 : Blo 2089435 3527651 := bstep (se 1 (by rfl) ⟨2645738, by rfl⟩ : syracuseStep 3527651 = 5291477) B5291477
theorem B2351767 : Blo 2089435 2351767 := bstep (se 1 (by rfl) ⟨1763825, by rfl⟩ : syracuseStep 2351767 = 3527651) B3527651
theorem B3135689 : Blo 2089435 3135689 := bstep (se 2 (by rfl) ⟨1175883, by rfl⟩ : syracuseStep 3135689 = 2351767) B2351767
theorem B2090459 : Blo 2089435 2090459 := bstep (se 1 (by rfl) ⟨1567844, by rfl⟩ : syracuseStep 2090459 = 3135689) B3135689
theorem B8475941 : Blo 2089435 8475941 := bbase (se 4 (by rfl) ⟨794619, by rfl⟩ : syracuseStep 8475941 = 1589239) (by norm_num)
theorem B22602509 : Blo 2089435 22602509 := bstep (se 3 (by rfl) ⟨4237970, by rfl⟩ : syracuseStep 22602509 = 8475941) B8475941
theorem B15068339 : Blo 2089435 15068339 := bstep (se 1 (by rfl) ⟨11301254, by rfl⟩ : syracuseStep 15068339 = 22602509) B22602509
theorem B10045559 : Blo 2089435 10045559 := bstep (se 1 (by rfl) ⟨7534169, by rfl⟩ : syracuseStep 10045559 = 15068339) B15068339
theorem B6697039 : Blo 2089435 6697039 := bstep (se 1 (by rfl) ⟨5022779, by rfl⟩ : syracuseStep 6697039 = 10045559) B10045559
theorem B8929385 : Blo 2089435 8929385 := bstep (se 2 (by rfl) ⟨3348519, by rfl⟩ : syracuseStep 8929385 = 6697039) B6697039
theorem B5952923 : Blo 2089435 5952923 := bstep (se 1 (by rfl) ⟨4464692, by rfl⟩ : syracuseStep 5952923 = 8929385) B8929385
theorem B3968615 : Blo 2089435 3968615 := bstep (se 1 (by rfl) ⟨2976461, by rfl⟩ : syracuseStep 3968615 = 5952923) B5952923
theorem B10582973 : Blo 2089435 10582973 := bstep (se 3 (by rfl) ⟨1984307, by rfl⟩ : syracuseStep 10582973 = 3968615) B3968615
theorem B7055315 : Blo 2089435 7055315 := bstep (se 1 (by rfl) ⟨5291486, by rfl⟩ : syracuseStep 7055315 = 10582973) B10582973
theorem B4703543 : Blo 2089435 4703543 := bstep (se 1 (by rfl) ⟨3527657, by rfl⟩ : syracuseStep 4703543 = 7055315) B7055315
theorem B3135695 : Blo 2089435 3135695 := bstep (se 1 (by rfl) ⟨2351771, by rfl⟩ : syracuseStep 3135695 = 4703543) B4703543
theorem B2090463 : Blo 2089435 2090463 := bstep (se 1 (by rfl) ⟨1567847, by rfl⟩ : syracuseStep 2090463 = 3135695) B3135695
theorem B3135701 : Blo 2089435 3135701 := bbase (se 7 (by rfl) ⟨36746, by rfl⟩ : syracuseStep 3135701 = 73493) (by norm_num)
theorem B2090467 : Blo 2089435 2090467 := bstep (se 1 (by rfl) ⟨1567850, by rfl⟩ : syracuseStep 2090467 = 3135701) B3135701
theorem B3348533 : Blo 2089435 3348533 := bbase (se 5 (by rfl) ⟨156962, by rfl⟩ : syracuseStep 3348533 = 313925) (by norm_num)
theorem B2232355 : Blo 2089435 2232355 := bstep (se 1 (by rfl) ⟨1674266, by rfl⟩ : syracuseStep 2232355 = 3348533) B3348533
theorem B2976473 : Blo 2089435 2976473 := bstep (se 2 (by rfl) ⟨1116177, by rfl⟩ : syracuseStep 2976473 = 2232355) B2232355
theorem B7937261 : Blo 2089435 7937261 := bstep (se 3 (by rfl) ⟨1488236, by rfl⟩ : syracuseStep 7937261 = 2976473) B2976473
theorem B5291507 : Blo 2089435 5291507 := bstep (se 1 (by rfl) ⟨3968630, by rfl⟩ : syracuseStep 5291507 = 7937261) B7937261
theorem B3527671 : Blo 2089435 3527671 := bstep (se 1 (by rfl) ⟨2645753, by rfl⟩ : syracuseStep 3527671 = 5291507) B5291507
theorem B4703561 : Blo 2089435 4703561 := bstep (se 2 (by rfl) ⟨1763835, by rfl⟩ : syracuseStep 4703561 = 3527671) B3527671
theorem B3135707 : Blo 2089435 3135707 := bstep (se 1 (by rfl) ⟨2351780, by rfl⟩ : syracuseStep 3135707 = 4703561) B4703561
theorem B2090471 : Blo 2089435 2090471 := bstep (se 1 (by rfl) ⟨1567853, by rfl⟩ : syracuseStep 2090471 = 3135707) B3135707
theorem B2351785 : Blo 2089435 2351785 := bbase (se 2 (by rfl) ⟨881919, by rfl⟩ : syracuseStep 2351785 = 1763839) (by norm_num)
theorem B3135713 : Blo 2089435 3135713 := bstep (se 2 (by rfl) ⟨1175892, by rfl⟩ : syracuseStep 3135713 = 2351785) B2351785
theorem B2090475 : Blo 2089435 2090475 := bstep (se 1 (by rfl) ⟨1567856, by rfl⟩ : syracuseStep 2090475 = 3135713) B3135713
theorem B2511409 : Blo 2089435 2511409 := bbase (se 2 (by rfl) ⟨941778, by rfl⟩ : syracuseStep 2511409 = 1883557) (by norm_num)
theorem B3348545 : Blo 2089435 3348545 := bstep (se 2 (by rfl) ⟨1255704, by rfl⟩ : syracuseStep 3348545 = 2511409) B2511409
theorem B8929453 : Blo 2089435 8929453 := bstep (se 3 (by rfl) ⟨1674272, by rfl⟩ : syracuseStep 8929453 = 3348545) B3348545
theorem B11905937 : Blo 2089435 11905937 := bstep (se 2 (by rfl) ⟨4464726, by rfl⟩ : syracuseStep 11905937 = 8929453) B8929453
theorem B7937291 : Blo 2089435 7937291 := bstep (se 1 (by rfl) ⟨5952968, by rfl⟩ : syracuseStep 7937291 = 11905937) B11905937
theorem B5291527 : Blo 2089435 5291527 := bstep (se 1 (by rfl) ⟨3968645, by rfl⟩ : syracuseStep 5291527 = 7937291) B7937291
theorem B7055369 : Blo 2089435 7055369 := bstep (se 2 (by rfl) ⟨2645763, by rfl⟩ : syracuseStep 7055369 = 5291527) B5291527
theorem B4703579 : Blo 2089435 4703579 := bstep (se 1 (by rfl) ⟨3527684, by rfl⟩ : syracuseStep 4703579 = 7055369) B7055369
theorem B3135719 : Blo 2089435 3135719 := bstep (se 1 (by rfl) ⟨2351789, by rfl⟩ : syracuseStep 3135719 = 4703579) B4703579
theorem B2090479 : Blo 2089435 2090479 := bstep (se 1 (by rfl) ⟨1567859, by rfl⟩ : syracuseStep 2090479 = 3135719) B3135719
theorem B3135725 : Blo 2089435 3135725 := bbase (se 3 (by rfl) ⟨587948, by rfl⟩ : syracuseStep 3135725 = 1175897) (by norm_num)
theorem B2090483 : Blo 2089435 2090483 := bstep (se 1 (by rfl) ⟨1567862, by rfl⟩ : syracuseStep 2090483 = 3135725) B3135725
theorem B4703597 : Blo 2089435 4703597 := bbase (se 3 (by rfl) ⟨881924, by rfl⟩ : syracuseStep 4703597 = 1763849) (by norm_num)
theorem B3135731 : Blo 2089435 3135731 := bstep (se 1 (by rfl) ⟨2351798, by rfl⟩ : syracuseStep 3135731 = 4703597) B4703597
theorem B2090487 : Blo 2089435 2090487 := bstep (se 1 (by rfl) ⟨1567865, by rfl⟩ : syracuseStep 2090487 = 3135731) B3135731
theorem B3968669 : Blo 2089435 3968669 := bbase (se 3 (by rfl) ⟨744125, by rfl⟩ : syracuseStep 3968669 = 1488251) (by norm_num)
theorem B2645779 : Blo 2089435 2645779 := bstep (se 1 (by rfl) ⟨1984334, by rfl⟩ : syracuseStep 2645779 = 3968669) B3968669
theorem B3527705 : Blo 2089435 3527705 := bstep (se 2 (by rfl) ⟨1322889, by rfl⟩ : syracuseStep 3527705 = 2645779) B2645779
theorem B2351803 : Blo 2089435 2351803 := bstep (se 1 (by rfl) ⟨1763852, by rfl⟩ : syracuseStep 2351803 = 3527705) B3527705
theorem B3135737 : Blo 2089435 3135737 := bstep (se 2 (by rfl) ⟨1175901, by rfl⟩ : syracuseStep 3135737 = 2351803) B2351803
theorem B2090491 : Blo 2089435 2090491 := bstep (se 1 (by rfl) ⟨1567868, by rfl⟩ : syracuseStep 2090491 = 3135737) B3135737
theorem B33904277 : Blo 2089435 33904277 := bbase (se 6 (by rfl) ⟨794631, by rfl⟩ : syracuseStep 33904277 = 1589263) (by norm_num)
theorem B22602851 : Blo 2089435 22602851 := bstep (se 1 (by rfl) ⟨16952138, by rfl⟩ : syracuseStep 22602851 = 33904277) B33904277
theorem B15068567 : Blo 2089435 15068567 := bstep (se 1 (by rfl) ⟨11301425, by rfl⟩ : syracuseStep 15068567 = 22602851) B22602851
theorem B10045711 : Blo 2089435 10045711 := bstep (se 1 (by rfl) ⟨7534283, by rfl⟩ : syracuseStep 10045711 = 15068567) B15068567
theorem B53577125 : Blo 2089435 53577125 := bstep (se 4 (by rfl) ⟨5022855, by rfl⟩ : syracuseStep 53577125 = 10045711) B10045711
theorem B35718083 : Blo 2089435 35718083 := bstep (se 1 (by rfl) ⟨26788562, by rfl⟩ : syracuseStep 35718083 = 53577125) B53577125
theorem B23812055 : Blo 2089435 23812055 := bstep (se 1 (by rfl) ⟨17859041, by rfl⟩ : syracuseStep 23812055 = 35718083) B35718083
theorem B15874703 : Blo 2089435 15874703 := bstep (se 1 (by rfl) ⟨11906027, by rfl⟩ : syracuseStep 15874703 = 23812055) B23812055
theorem B10583135 : Blo 2089435 10583135 := bstep (se 1 (by rfl) ⟨7937351, by rfl⟩ : syracuseStep 10583135 = 15874703) B15874703
theorem B7055423 : Blo 2089435 7055423 := bstep (se 1 (by rfl) ⟨5291567, by rfl⟩ : syracuseStep 7055423 = 10583135) B10583135
theorem B4703615 : Blo 2089435 4703615 := bstep (se 1 (by rfl) ⟨3527711, by rfl⟩ : syracuseStep 4703615 = 7055423) B7055423
theorem B3135743 : Blo 2089435 3135743 := bstep (se 1 (by rfl) ⟨2351807, by rfl⟩ : syracuseStep 3135743 = 4703615) B4703615
theorem B2090495 : Blo 2089435 2090495 := bstep (se 1 (by rfl) ⟨1567871, by rfl⟩ : syracuseStep 2090495 = 3135743) B3135743
theorem B3135749 : Blo 2089435 3135749 := bbase (se 4 (by rfl) ⟨293976, by rfl⟩ : syracuseStep 3135749 = 587953) (by norm_num)
theorem B2090499 : Blo 2089435 2090499 := bstep (se 1 (by rfl) ⟨1567874, by rfl⟩ : syracuseStep 2090499 = 3135749) B3135749
theorem B3527725 : Blo 2089435 3527725 := bbase (se 3 (by rfl) ⟨661448, by rfl⟩ : syracuseStep 3527725 = 1322897) (by norm_num)
theorem B4703633 : Blo 2089435 4703633 := bstep (se 2 (by rfl) ⟨1763862, by rfl⟩ : syracuseStep 4703633 = 3527725) B3527725
theorem B3135755 : Blo 2089435 3135755 := bstep (se 1 (by rfl) ⟨2351816, by rfl⟩ : syracuseStep 3135755 = 4703633) B4703633
theorem B2090503 : Blo 2089435 2090503 := bstep (se 1 (by rfl) ⟨1567877, by rfl⟩ : syracuseStep 2090503 = 3135755) B3135755
theorem B2351821 : Blo 2089435 2351821 := bbase (se 3 (by rfl) ⟨440966, by rfl⟩ : syracuseStep 2351821 = 881933) (by norm_num)
theorem B3135761 : Blo 2089435 3135761 := bstep (se 2 (by rfl) ⟨1175910, by rfl⟩ : syracuseStep 3135761 = 2351821) B2351821
theorem B2090507 : Blo 2089435 2090507 := bstep (se 1 (by rfl) ⟨1567880, by rfl⟩ : syracuseStep 2090507 = 3135761) B3135761
theorem B7055477 : Blo 2089435 7055477 := bbase (se 5 (by rfl) ⟨330725, by rfl⟩ : syracuseStep 7055477 = 661451) (by norm_num)
theorem B4703651 : Blo 2089435 4703651 := bstep (se 1 (by rfl) ⟨3527738, by rfl⟩ : syracuseStep 4703651 = 7055477) B7055477
theorem B3135767 : Blo 2089435 3135767 := bstep (se 1 (by rfl) ⟨2351825, by rfl⟩ : syracuseStep 3135767 = 4703651) B4703651
theorem B2090511 : Blo 2089435 2090511 := bstep (se 1 (by rfl) ⟨1567883, by rfl⟩ : syracuseStep 2090511 = 3135767) B3135767
theorem B3135773 : Blo 2089435 3135773 := bbase (se 3 (by rfl) ⟨587957, by rfl⟩ : syracuseStep 3135773 = 1175915) (by norm_num)
theorem B2090515 : Blo 2089435 2090515 := bstep (se 1 (by rfl) ⟨1567886, by rfl⟩ : syracuseStep 2090515 = 3135773) B3135773
theorem B4703669 : Blo 2089435 4703669 := bbase (se 5 (by rfl) ⟨220484, by rfl⟩ : syracuseStep 4703669 = 440969) (by norm_num)
theorem B3135779 : Blo 2089435 3135779 := bstep (se 1 (by rfl) ⟨2351834, by rfl⟩ : syracuseStep 3135779 = 4703669) B4703669
theorem B2090519 : Blo 2089435 2090519 := bstep (se 1 (by rfl) ⟨1567889, by rfl⟩ : syracuseStep 2090519 = 3135779) B3135779
theorem B4464821 : Blo 2089435 4464821 := bbase (se 5 (by rfl) ⟨209288, by rfl⟩ : syracuseStep 4464821 = 418577) (by norm_num)
theorem B11906189 : Blo 2089435 11906189 := bstep (se 3 (by rfl) ⟨2232410, by rfl⟩ : syracuseStep 11906189 = 4464821) B4464821
theorem B7937459 : Blo 2089435 7937459 := bstep (se 1 (by rfl) ⟨5953094, by rfl⟩ : syracuseStep 7937459 = 11906189) B11906189
theorem B5291639 : Blo 2089435 5291639 := bstep (se 1 (by rfl) ⟨3968729, by rfl⟩ : syracuseStep 5291639 = 7937459) B7937459
theorem B3527759 : Blo 2089435 3527759 := bstep (se 1 (by rfl) ⟨2645819, by rfl⟩ : syracuseStep 3527759 = 5291639) B5291639
theorem B2351839 : Blo 2089435 2351839 := bstep (se 1 (by rfl) ⟨1763879, by rfl⟩ : syracuseStep 2351839 = 3527759) B3527759
theorem B3135785 : Blo 2089435 3135785 := bstep (se 2 (by rfl) ⟨1175919, by rfl⟩ : syracuseStep 3135785 = 2351839) B2351839
theorem B2090523 : Blo 2089435 2090523 := bstep (se 1 (by rfl) ⟨1567892, by rfl⟩ : syracuseStep 2090523 = 3135785) B3135785
theorem B4464829 : Blo 2089435 4464829 := bbase (se 3 (by rfl) ⟨837155, by rfl⟩ : syracuseStep 4464829 = 1674311) (by norm_num)
theorem B5953105 : Blo 2089435 5953105 := bstep (se 2 (by rfl) ⟨2232414, by rfl⟩ : syracuseStep 5953105 = 4464829) B4464829
theorem B7937473 : Blo 2089435 7937473 := bstep (se 2 (by rfl) ⟨2976552, by rfl⟩ : syracuseStep 7937473 = 5953105) B5953105
theorem B10583297 : Blo 2089435 10583297 := bstep (se 2 (by rfl) ⟨3968736, by rfl⟩ : syracuseStep 10583297 = 7937473) B7937473
theorem B7055531 : Blo 2089435 7055531 := bstep (se 1 (by rfl) ⟨5291648, by rfl⟩ : syracuseStep 7055531 = 10583297) B10583297
theorem B4703687 : Blo 2089435 4703687 := bstep (se 1 (by rfl) ⟨3527765, by rfl⟩ : syracuseStep 4703687 = 7055531) B7055531
theorem B3135791 : Blo 2089435 3135791 := bstep (se 1 (by rfl) ⟨2351843, by rfl⟩ : syracuseStep 3135791 = 4703687) B4703687
theorem B2090527 : Blo 2089435 2090527 := bstep (se 1 (by rfl) ⟨1567895, by rfl⟩ : syracuseStep 2090527 = 3135791) B3135791
theorem B3135797 : Blo 2089435 3135797 := bbase (se 5 (by rfl) ⟨146990, by rfl⟩ : syracuseStep 3135797 = 293981) (by norm_num)
theorem B2090531 : Blo 2089435 2090531 := bstep (se 1 (by rfl) ⟨1567898, by rfl⟩ : syracuseStep 2090531 = 3135797) B3135797
theorem B5291669 : Blo 2089435 5291669 := bbase (se 6 (by rfl) ⟨124023, by rfl⟩ : syracuseStep 5291669 = 248047) (by norm_num)
theorem B3527779 : Blo 2089435 3527779 := bstep (se 1 (by rfl) ⟨2645834, by rfl⟩ : syracuseStep 3527779 = 5291669) B5291669
theorem B4703705 : Blo 2089435 4703705 := bstep (se 2 (by rfl) ⟨1763889, by rfl⟩ : syracuseStep 4703705 = 3527779) B3527779
theorem B3135803 : Blo 2089435 3135803 := bstep (se 1 (by rfl) ⟨2351852, by rfl⟩ : syracuseStep 3135803 = 4703705) B4703705
theorem B2090535 : Blo 2089435 2090535 := bstep (se 1 (by rfl) ⟨1567901, by rfl⟩ : syracuseStep 2090535 = 3135803) B3135803
theorem B2351857 : Blo 2089435 2351857 := bbase (se 2 (by rfl) ⟨881946, by rfl⟩ : syracuseStep 2351857 = 1763893) (by norm_num)
theorem B3135809 : Blo 2089435 3135809 := bstep (se 2 (by rfl) ⟨1175928, by rfl⟩ : syracuseStep 3135809 = 2351857) B2351857
theorem B2090539 : Blo 2089435 2090539 := bstep (se 1 (by rfl) ⟨1567904, by rfl⟩ : syracuseStep 2090539 = 3135809) B3135809
theorem B6034373 : Blo 2089435 6034373 := bbase (se 4 (by rfl) ⟨565722, by rfl⟩ : syracuseStep 6034373 = 1131445) (by norm_num)
theorem B4022915 : Blo 2089435 4022915 := bstep (se 1 (by rfl) ⟨3017186, by rfl⟩ : syracuseStep 4022915 = 6034373) B6034373
theorem B42911093 : Blo 2089435 42911093 := bstep (se 5 (by rfl) ⟨2011457, by rfl⟩ : syracuseStep 42911093 = 4022915) B4022915
theorem B114429581 : Blo 2089435 114429581 := bstep (se 3 (by rfl) ⟨21455546, by rfl⟩ : syracuseStep 114429581 = 42911093) B42911093
theorem B76286387 : Blo 2089435 76286387 := bstep (se 1 (by rfl) ⟨57214790, by rfl⟩ : syracuseStep 76286387 = 114429581) B114429581
theorem B50857591 : Blo 2089435 50857591 := bstep (se 1 (by rfl) ⟨38143193, by rfl⟩ : syracuseStep 50857591 = 76286387) B76286387
theorem B67810121 : Blo 2089435 67810121 := bstep (se 2 (by rfl) ⟨25428795, by rfl⟩ : syracuseStep 67810121 = 50857591) B50857591
theorem B45206747 : Blo 2089435 45206747 := bstep (se 1 (by rfl) ⟨33905060, by rfl⟩ : syracuseStep 45206747 = 67810121) B67810121
theorem B30137831 : Blo 2089435 30137831 := bstep (se 1 (by rfl) ⟨22603373, by rfl⟩ : syracuseStep 30137831 = 45206747) B45206747
theorem B20091887 : Blo 2089435 20091887 := bstep (se 1 (by rfl) ⟨15068915, by rfl⟩ : syracuseStep 20091887 = 30137831) B30137831
theorem B13394591 : Blo 2089435 13394591 := bstep (se 1 (by rfl) ⟨10045943, by rfl⟩ : syracuseStep 13394591 = 20091887) B20091887
theorem B8929727 : Blo 2089435 8929727 := bstep (se 1 (by rfl) ⟨6697295, by rfl⟩ : syracuseStep 8929727 = 13394591) B13394591
theorem B5953151 : Blo 2089435 5953151 := bstep (se 1 (by rfl) ⟨4464863, by rfl⟩ : syracuseStep 5953151 = 8929727) B8929727
theorem B3968767 : Blo 2089435 3968767 := bstep (se 1 (by rfl) ⟨2976575, by rfl⟩ : syracuseStep 3968767 = 5953151) B5953151
theorem B5291689 : Blo 2089435 5291689 := bstep (se 2 (by rfl) ⟨1984383, by rfl⟩ : syracuseStep 5291689 = 3968767) B3968767
theorem B7055585 : Blo 2089435 7055585 := bstep (se 2 (by rfl) ⟨2645844, by rfl⟩ : syracuseStep 7055585 = 5291689) B5291689
theorem B4703723 : Blo 2089435 4703723 := bstep (se 1 (by rfl) ⟨3527792, by rfl⟩ : syracuseStep 4703723 = 7055585) B7055585
theorem B3135815 : Blo 2089435 3135815 := bstep (se 1 (by rfl) ⟨2351861, by rfl⟩ : syracuseStep 3135815 = 4703723) B4703723
theorem B2090543 : Blo 2089435 2090543 := bstep (se 1 (by rfl) ⟨1567907, by rfl⟩ : syracuseStep 2090543 = 3135815) B3135815
theorem B3135821 : Blo 2089435 3135821 := bbase (se 3 (by rfl) ⟨587966, by rfl⟩ : syracuseStep 3135821 = 1175933) (by norm_num)
theorem B2090547 : Blo 2089435 2090547 := bstep (se 1 (by rfl) ⟨1567910, by rfl⟩ : syracuseStep 2090547 = 3135821) B3135821
theorem B4703741 : Blo 2089435 4703741 := bbase (se 3 (by rfl) ⟨881951, by rfl⟩ : syracuseStep 4703741 = 1763903) (by norm_num)
theorem B3135827 : Blo 2089435 3135827 := bstep (se 1 (by rfl) ⟨2351870, by rfl⟩ : syracuseStep 3135827 = 4703741) B4703741
theorem B2090551 : Blo 2089435 2090551 := bstep (se 1 (by rfl) ⟨1567913, by rfl⟩ : syracuseStep 2090551 = 3135827) B3135827
theorem B3527813 : Blo 2089435 3527813 := bbase (se 4 (by rfl) ⟨330732, by rfl⟩ : syracuseStep 3527813 = 661465) (by norm_num)
theorem B2351875 : Blo 2089435 2351875 := bstep (se 1 (by rfl) ⟨1763906, by rfl⟩ : syracuseStep 2351875 = 3527813) B3527813
theorem B3135833 : Blo 2089435 3135833 := bstep (se 2 (by rfl) ⟨1175937, by rfl⟩ : syracuseStep 3135833 = 2351875) B2351875
theorem B2090555 : Blo 2089435 2090555 := bstep (se 1 (by rfl) ⟨1567916, by rfl⟩ : syracuseStep 2090555 = 3135833) B3135833
theorem B15875189 : Blo 2089435 15875189 := bbase (se 5 (by rfl) ⟨744149, by rfl⟩ : syracuseStep 15875189 = 1488299) (by norm_num)
theorem B10583459 : Blo 2089435 10583459 := bstep (se 1 (by rfl) ⟨7937594, by rfl⟩ : syracuseStep 10583459 = 15875189) B15875189
theorem B7055639 : Blo 2089435 7055639 := bstep (se 1 (by rfl) ⟨5291729, by rfl⟩ : syracuseStep 7055639 = 10583459) B10583459
theorem B4703759 : Blo 2089435 4703759 := bstep (se 1 (by rfl) ⟨3527819, by rfl⟩ : syracuseStep 4703759 = 7055639) B7055639
theorem B3135839 : Blo 2089435 3135839 := bstep (se 1 (by rfl) ⟨2351879, by rfl⟩ : syracuseStep 3135839 = 4703759) B4703759
theorem B2090559 : Blo 2089435 2090559 := bstep (se 1 (by rfl) ⟨1567919, by rfl⟩ : syracuseStep 2090559 = 3135839) B3135839
theorem B3135845 : Blo 2089435 3135845 := bbase (se 4 (by rfl) ⟨293985, by rfl⟩ : syracuseStep 3135845 = 587971) (by norm_num)
theorem B2090563 : Blo 2089435 2090563 := bstep (se 1 (by rfl) ⟨1567922, by rfl⟩ : syracuseStep 2090563 = 3135845) B3135845
theorem B3968813 : Blo 2089435 3968813 := bbase (se 3 (by rfl) ⟨744152, by rfl⟩ : syracuseStep 3968813 = 1488305) (by norm_num)
theorem B2645875 : Blo 2089435 2645875 := bstep (se 1 (by rfl) ⟨1984406, by rfl⟩ : syracuseStep 2645875 = 3968813) B3968813
theorem B3527833 : Blo 2089435 3527833 := bstep (se 2 (by rfl) ⟨1322937, by rfl⟩ : syracuseStep 3527833 = 2645875) B2645875
theorem B4703777 : Blo 2089435 4703777 := bstep (se 2 (by rfl) ⟨1763916, by rfl⟩ : syracuseStep 4703777 = 3527833) B3527833
theorem B3135851 : Blo 2089435 3135851 := bstep (se 1 (by rfl) ⟨2351888, by rfl⟩ : syracuseStep 3135851 = 4703777) B4703777
theorem B2090567 : Blo 2089435 2090567 := bstep (se 1 (by rfl) ⟨1567925, by rfl⟩ : syracuseStep 2090567 = 3135851) B3135851
theorem B2351893 : Blo 2089435 2351893 := bbase (se 6 (by rfl) ⟨55122, by rfl⟩ : syracuseStep 2351893 = 110245) (by norm_num)
theorem B3135857 : Blo 2089435 3135857 := bstep (se 2 (by rfl) ⟨1175946, by rfl⟩ : syracuseStep 3135857 = 2351893) B2351893
theorem B2090571 : Blo 2089435 2090571 := bstep (se 1 (by rfl) ⟨1567928, by rfl⟩ : syracuseStep 2090571 = 3135857) B3135857
theorem B2645885 : Blo 2089435 2645885 := bbase (se 3 (by rfl) ⟨496103, by rfl⟩ : syracuseStep 2645885 = 992207) (by norm_num)
theorem B7055693 : Blo 2089435 7055693 := bstep (se 3 (by rfl) ⟨1322942, by rfl⟩ : syracuseStep 7055693 = 2645885) B2645885
theorem B4703795 : Blo 2089435 4703795 := bstep (se 1 (by rfl) ⟨3527846, by rfl⟩ : syracuseStep 4703795 = 7055693) B7055693
theorem B3135863 : Blo 2089435 3135863 := bstep (se 1 (by rfl) ⟨2351897, by rfl⟩ : syracuseStep 3135863 = 4703795) B4703795
theorem B2090575 : Blo 2089435 2090575 := bstep (se 1 (by rfl) ⟨1567931, by rfl⟩ : syracuseStep 2090575 = 3135863) B3135863
theorem B3135869 : Blo 2089435 3135869 := bbase (se 3 (by rfl) ⟨587975, by rfl⟩ : syracuseStep 3135869 = 1175951) (by norm_num)
theorem B2090579 : Blo 2089435 2090579 := bstep (se 1 (by rfl) ⟨1567934, by rfl⟩ : syracuseStep 2090579 = 3135869) B3135869
theorem B4703813 : Blo 2089435 4703813 := bbase (se 4 (by rfl) ⟨440982, by rfl⟩ : syracuseStep 4703813 = 881965) (by norm_num)
theorem B3135875 : Blo 2089435 3135875 := bstep (se 1 (by rfl) ⟨2351906, by rfl⟩ : syracuseStep 3135875 = 4703813) B4703813
theorem B2090583 : Blo 2089435 2090583 := bstep (se 1 (by rfl) ⟨1567937, by rfl⟩ : syracuseStep 2090583 = 3135875) B3135875
theorem B4525877 : Blo 2089435 4525877 := bbase (se 5 (by rfl) ⟨212150, by rfl⟩ : syracuseStep 4525877 = 424301) (by norm_num)
theorem B12069005 : Blo 2089435 12069005 := bstep (se 3 (by rfl) ⟨2262938, by rfl⟩ : syracuseStep 12069005 = 4525877) B4525877
theorem B32184013 : Blo 2089435 32184013 := bstep (se 3 (by rfl) ⟨6034502, by rfl⟩ : syracuseStep 32184013 = 12069005) B12069005
theorem B42912017 : Blo 2089435 42912017 := bstep (se 2 (by rfl) ⟨16092006, by rfl⟩ : syracuseStep 42912017 = 32184013) B32184013
theorem B28608011 : Blo 2089435 28608011 := bstep (se 1 (by rfl) ⟨21456008, by rfl⟩ : syracuseStep 28608011 = 42912017) B42912017
theorem B19072007 : Blo 2089435 19072007 := bstep (se 1 (by rfl) ⟨14304005, by rfl⟩ : syracuseStep 19072007 = 28608011) B28608011
theorem B12714671 : Blo 2089435 12714671 := bstep (se 1 (by rfl) ⟨9536003, by rfl⟩ : syracuseStep 12714671 = 19072007) B19072007
theorem B8476447 : Blo 2089435 8476447 := bstep (se 1 (by rfl) ⟨6357335, by rfl⟩ : syracuseStep 8476447 = 12714671) B12714671
theorem B11301929 : Blo 2089435 11301929 := bstep (se 2 (by rfl) ⟨4238223, by rfl⟩ : syracuseStep 11301929 = 8476447) B8476447
theorem B7534619 : Blo 2089435 7534619 := bstep (se 1 (by rfl) ⟨5650964, by rfl⟩ : syracuseStep 7534619 = 11301929) B11301929
theorem B5023079 : Blo 2089435 5023079 := bstep (se 1 (by rfl) ⟨3767309, by rfl⟩ : syracuseStep 5023079 = 7534619) B7534619
theorem B3348719 : Blo 2089435 3348719 := bstep (se 1 (by rfl) ⟨2511539, by rfl⟩ : syracuseStep 3348719 = 5023079) B5023079
theorem B2232479 : Blo 2089435 2232479 := bstep (se 1 (by rfl) ⟨1674359, by rfl⟩ : syracuseStep 2232479 = 3348719) B3348719
theorem B5953277 : Blo 2089435 5953277 := bstep (se 3 (by rfl) ⟨1116239, by rfl⟩ : syracuseStep 5953277 = 2232479) B2232479
theorem B3968851 : Blo 2089435 3968851 := bstep (se 1 (by rfl) ⟨2976638, by rfl⟩ : syracuseStep 3968851 = 5953277) B5953277
theorem B5291801 : Blo 2089435 5291801 := bstep (se 2 (by rfl) ⟨1984425, by rfl⟩ : syracuseStep 5291801 = 3968851) B3968851
theorem B3527867 : Blo 2089435 3527867 := bstep (se 1 (by rfl) ⟨2645900, by rfl⟩ : syracuseStep 3527867 = 5291801) B5291801
theorem B2351911 : Blo 2089435 2351911 := bstep (se 1 (by rfl) ⟨1763933, by rfl⟩ : syracuseStep 2351911 = 3527867) B3527867
theorem B3135881 : Blo 2089435 3135881 := bstep (se 2 (by rfl) ⟨1175955, by rfl⟩ : syracuseStep 3135881 = 2351911) B2351911
theorem B2090587 : Blo 2089435 2090587 := bstep (se 1 (by rfl) ⟨1567940, by rfl⟩ : syracuseStep 2090587 = 3135881) B3135881
theorem B10583621 : Blo 2089435 10583621 := bbase (se 4 (by rfl) ⟨992214, by rfl⟩ : syracuseStep 10583621 = 1984429) (by norm_num)
theorem B7055747 : Blo 2089435 7055747 := bstep (se 1 (by rfl) ⟨5291810, by rfl⟩ : syracuseStep 7055747 = 10583621) B10583621
theorem B4703831 : Blo 2089435 4703831 := bstep (se 1 (by rfl) ⟨3527873, by rfl⟩ : syracuseStep 4703831 = 7055747) B7055747
theorem B3135887 : Blo 2089435 3135887 := bstep (se 1 (by rfl) ⟨2351915, by rfl⟩ : syracuseStep 3135887 = 4703831) B4703831
theorem B2090591 : Blo 2089435 2090591 := bstep (se 1 (by rfl) ⟨1567943, by rfl⟩ : syracuseStep 2090591 = 3135887) B3135887
theorem B3135893 : Blo 2089435 3135893 := bbase (se 6 (by rfl) ⟨73497, by rfl⟩ : syracuseStep 3135893 = 146995) (by norm_num)
theorem B2090595 : Blo 2089435 2090595 := bstep (se 1 (by rfl) ⟨1567946, by rfl⟩ : syracuseStep 2090595 = 3135893) B3135893
theorem B10046213 : Blo 2089435 10046213 := bbase (se 4 (by rfl) ⟨941832, by rfl⟩ : syracuseStep 10046213 = 1883665) (by norm_num)
theorem B6697475 : Blo 2089435 6697475 := bstep (se 1 (by rfl) ⟨5023106, by rfl⟩ : syracuseStep 6697475 = 10046213) B10046213
theorem B4464983 : Blo 2089435 4464983 := bstep (se 1 (by rfl) ⟨3348737, by rfl⟩ : syracuseStep 4464983 = 6697475) B6697475
theorem B11906621 : Blo 2089435 11906621 := bstep (se 3 (by rfl) ⟨2232491, by rfl⟩ : syracuseStep 11906621 = 4464983) B4464983
theorem B7937747 : Blo 2089435 7937747 := bstep (se 1 (by rfl) ⟨5953310, by rfl⟩ : syracuseStep 7937747 = 11906621) B11906621
theorem B5291831 : Blo 2089435 5291831 := bstep (se 1 (by rfl) ⟨3968873, by rfl⟩ : syracuseStep 5291831 = 7937747) B7937747
theorem B3527887 : Blo 2089435 3527887 := bstep (se 1 (by rfl) ⟨2645915, by rfl⟩ : syracuseStep 3527887 = 5291831) B5291831
theorem B4703849 : Blo 2089435 4703849 := bstep (se 2 (by rfl) ⟨1763943, by rfl⟩ : syracuseStep 4703849 = 3527887) B3527887
theorem B3135899 : Blo 2089435 3135899 := bstep (se 1 (by rfl) ⟨2351924, by rfl⟩ : syracuseStep 3135899 = 4703849) B4703849
theorem B2090599 : Blo 2089435 2090599 := bstep (se 1 (by rfl) ⟨1567949, by rfl⟩ : syracuseStep 2090599 = 3135899) B3135899
theorem B2351929 : Blo 2089435 2351929 := bbase (se 2 (by rfl) ⟨881973, by rfl⟩ : syracuseStep 2351929 = 1763947) (by norm_num)
theorem B3135905 : Blo 2089435 3135905 := bstep (se 2 (by rfl) ⟨1175964, by rfl⟩ : syracuseStep 3135905 = 2351929) B2351929
theorem B2090603 : Blo 2089435 2090603 := bstep (se 1 (by rfl) ⟨1567952, by rfl⟩ : syracuseStep 2090603 = 3135905) B3135905
theorem B5953333 : Blo 2089435 5953333 := bbase (se 5 (by rfl) ⟨279062, by rfl⟩ : syracuseStep 5953333 = 558125) (by norm_num)
theorem B7937777 : Blo 2089435 7937777 := bstep (se 2 (by rfl) ⟨2976666, by rfl⟩ : syracuseStep 7937777 = 5953333) B5953333
theorem B5291851 : Blo 2089435 5291851 := bstep (se 1 (by rfl) ⟨3968888, by rfl⟩ : syracuseStep 5291851 = 7937777) B7937777
theorem B7055801 : Blo 2089435 7055801 := bstep (se 2 (by rfl) ⟨2645925, by rfl⟩ : syracuseStep 7055801 = 5291851) B5291851
theorem B4703867 : Blo 2089435 4703867 := bstep (se 1 (by rfl) ⟨3527900, by rfl⟩ : syracuseStep 4703867 = 7055801) B7055801
theorem B3135911 : Blo 2089435 3135911 := bstep (se 1 (by rfl) ⟨2351933, by rfl⟩ : syracuseStep 3135911 = 4703867) B4703867
theorem B2090607 : Blo 2089435 2090607 := bstep (se 1 (by rfl) ⟨1567955, by rfl⟩ : syracuseStep 2090607 = 3135911) B3135911
theorem B3135917 : Blo 2089435 3135917 := bbase (se 3 (by rfl) ⟨587984, by rfl⟩ : syracuseStep 3135917 = 1175969) (by norm_num)
theorem B2090611 : Blo 2089435 2090611 := bstep (se 1 (by rfl) ⟨1567958, by rfl⟩ : syracuseStep 2090611 = 3135917) B3135917
theorem B4703885 : Blo 2089435 4703885 := bbase (se 3 (by rfl) ⟨881978, by rfl⟩ : syracuseStep 4703885 = 1763957) (by norm_num)
theorem B3135923 : Blo 2089435 3135923 := bstep (se 1 (by rfl) ⟨2351942, by rfl⟩ : syracuseStep 3135923 = 4703885) B4703885
theorem B2090615 : Blo 2089435 2090615 := bstep (se 1 (by rfl) ⟨1567961, by rfl⟩ : syracuseStep 2090615 = 3135923) B3135923
theorem B2645941 : Blo 2089435 2645941 := bbase (se 5 (by rfl) ⟨124028, by rfl⟩ : syracuseStep 2645941 = 248057) (by norm_num)
theorem B3527921 : Blo 2089435 3527921 := bstep (se 2 (by rfl) ⟨1322970, by rfl⟩ : syracuseStep 3527921 = 2645941) B2645941
theorem B2351947 : Blo 2089435 2351947 := bstep (se 1 (by rfl) ⟨1763960, by rfl⟩ : syracuseStep 2351947 = 3527921) B3527921
theorem B3135929 : Blo 2089435 3135929 := bstep (se 2 (by rfl) ⟨1175973, by rfl⟩ : syracuseStep 3135929 = 2351947) B2351947
theorem B2090619 : Blo 2089435 2090619 := bstep (se 1 (by rfl) ⟨1567964, by rfl⟩ : syracuseStep 2090619 = 3135929) B3135929
theorem B2384041 : Blo 2089435 2384041 := bbase (se 2 (by rfl) ⟨894015, by rfl⟩ : syracuseStep 2384041 = 1788031) (by norm_num)
theorem B3178721 : Blo 2089435 3178721 := bstep (se 2 (by rfl) ⟨1192020, by rfl⟩ : syracuseStep 3178721 = 2384041) B2384041
theorem B2119147 : Blo 2089435 2119147 := bstep (se 1 (by rfl) ⟨1589360, by rfl⟩ : syracuseStep 2119147 = 3178721) B3178721
theorem B45208469 : Blo 2089435 45208469 := bstep (se 6 (by rfl) ⟨1059573, by rfl⟩ : syracuseStep 45208469 = 2119147) B2119147
theorem B30138979 : Blo 2089435 30138979 := bstep (se 1 (by rfl) ⟨22604234, by rfl⟩ : syracuseStep 30138979 = 45208469) B45208469
theorem B40185305 : Blo 2089435 40185305 := bstep (se 2 (by rfl) ⟨15069489, by rfl⟩ : syracuseStep 40185305 = 30138979) B30138979
theorem B26790203 : Blo 2089435 26790203 := bstep (se 1 (by rfl) ⟨20092652, by rfl⟩ : syracuseStep 26790203 = 40185305) B40185305
theorem B17860135 : Blo 2089435 17860135 := bstep (se 1 (by rfl) ⟨13395101, by rfl⟩ : syracuseStep 17860135 = 26790203) B26790203
theorem B23813513 : Blo 2089435 23813513 := bstep (se 2 (by rfl) ⟨8930067, by rfl⟩ : syracuseStep 23813513 = 17860135) B17860135
theorem B15875675 : Blo 2089435 15875675 := bstep (se 1 (by rfl) ⟨11906756, by rfl⟩ : syracuseStep 15875675 = 23813513) B23813513
theorem B10583783 : Blo 2089435 10583783 := bstep (se 1 (by rfl) ⟨7937837, by rfl⟩ : syracuseStep 10583783 = 15875675) B15875675
theorem B7055855 : Blo 2089435 7055855 := bstep (se 1 (by rfl) ⟨5291891, by rfl⟩ : syracuseStep 7055855 = 10583783) B10583783
theorem B4703903 : Blo 2089435 4703903 := bstep (se 1 (by rfl) ⟨3527927, by rfl⟩ : syracuseStep 4703903 = 7055855) B7055855
theorem B3135935 : Blo 2089435 3135935 := bstep (se 1 (by rfl) ⟨2351951, by rfl⟩ : syracuseStep 3135935 = 4703903) B4703903
theorem B2090623 : Blo 2089435 2090623 := bstep (se 1 (by rfl) ⟨1567967, by rfl⟩ : syracuseStep 2090623 = 3135935) B3135935
theorem B3135941 : Blo 2089435 3135941 := bbase (se 4 (by rfl) ⟨293994, by rfl⟩ : syracuseStep 3135941 = 587989) (by norm_num)
theorem B2090627 : Blo 2089435 2090627 := bstep (se 1 (by rfl) ⟨1567970, by rfl⟩ : syracuseStep 2090627 = 3135941) B3135941
theorem B3527941 : Blo 2089435 3527941 := bbase (se 4 (by rfl) ⟨330744, by rfl⟩ : syracuseStep 3527941 = 661489) (by norm_num)
theorem B4703921 : Blo 2089435 4703921 := bstep (se 2 (by rfl) ⟨1763970, by rfl⟩ : syracuseStep 4703921 = 3527941) B3527941
theorem B3135947 : Blo 2089435 3135947 := bstep (se 1 (by rfl) ⟨2351960, by rfl⟩ : syracuseStep 3135947 = 4703921) B4703921
theorem B2090631 : Blo 2089435 2090631 := bstep (se 1 (by rfl) ⟨1567973, by rfl⟩ : syracuseStep 2090631 = 3135947) B3135947
theorem B2351965 : Blo 2089435 2351965 := bbase (se 3 (by rfl) ⟨440993, by rfl⟩ : syracuseStep 2351965 = 881987) (by norm_num)
theorem B3135953 : Blo 2089435 3135953 := bstep (se 2 (by rfl) ⟨1175982, by rfl⟩ : syracuseStep 3135953 = 2351965) B2351965
theorem B2090635 : Blo 2089435 2090635 := bstep (se 1 (by rfl) ⟨1567976, by rfl⟩ : syracuseStep 2090635 = 3135953) B3135953
theorem B7055909 : Blo 2089435 7055909 := bbase (se 4 (by rfl) ⟨661491, by rfl⟩ : syracuseStep 7055909 = 1322983) (by norm_num)
theorem B4703939 : Blo 2089435 4703939 := bstep (se 1 (by rfl) ⟨3527954, by rfl⟩ : syracuseStep 4703939 = 7055909) B7055909
theorem B3135959 : Blo 2089435 3135959 := bstep (se 1 (by rfl) ⟨2351969, by rfl⟩ : syracuseStep 3135959 = 4703939) B4703939
theorem B2090639 : Blo 2089435 2090639 := bstep (se 1 (by rfl) ⟨1567979, by rfl⟩ : syracuseStep 2090639 = 3135959) B3135959
theorem B3135965 : Blo 2089435 3135965 := bbase (se 3 (by rfl) ⟨587993, by rfl⟩ : syracuseStep 3135965 = 1175987) (by norm_num)
theorem B2090643 : Blo 2089435 2090643 := bstep (se 1 (by rfl) ⟨1567982, by rfl⟩ : syracuseStep 2090643 = 3135965) B3135965
theorem B4703957 : Blo 2089435 4703957 := bbase (se 7 (by rfl) ⟨55124, by rfl⟩ : syracuseStep 4703957 = 110249) (by norm_num)
theorem B3135971 : Blo 2089435 3135971 := bstep (se 1 (by rfl) ⟨2351978, by rfl⟩ : syracuseStep 3135971 = 4703957) B4703957
theorem B2090647 : Blo 2089435 2090647 := bstep (se 1 (by rfl) ⟨1567985, by rfl⟩ : syracuseStep 2090647 = 3135971) B3135971
theorem B3348821 : Blo 2089435 3348821 := bbase (se 10 (by rfl) ⟨4905, by rfl⟩ : syracuseStep 3348821 = 9811) (by norm_num)
theorem B8930189 : Blo 2089435 8930189 := bstep (se 3 (by rfl) ⟨1674410, by rfl⟩ : syracuseStep 8930189 = 3348821) B3348821
theorem B5953459 : Blo 2089435 5953459 := bstep (se 1 (by rfl) ⟨4465094, by rfl⟩ : syracuseStep 5953459 = 8930189) B8930189
theorem B7937945 : Blo 2089435 7937945 := bstep (se 2 (by rfl) ⟨2976729, by rfl⟩ : syracuseStep 7937945 = 5953459) B5953459
theorem B5291963 : Blo 2089435 5291963 := bstep (se 1 (by rfl) ⟨3968972, by rfl⟩ : syracuseStep 5291963 = 7937945) B7937945
theorem B3527975 : Blo 2089435 3527975 := bstep (se 1 (by rfl) ⟨2645981, by rfl⟩ : syracuseStep 3527975 = 5291963) B5291963
theorem B2351983 : Blo 2089435 2351983 := bstep (se 1 (by rfl) ⟨1763987, by rfl⟩ : syracuseStep 2351983 = 3527975) B3527975
theorem B3135977 : Blo 2089435 3135977 := bstep (se 2 (by rfl) ⟨1175991, by rfl⟩ : syracuseStep 3135977 = 2351983) B2351983
theorem B2090651 : Blo 2089435 2090651 := bstep (se 1 (by rfl) ⟨1567988, by rfl⟩ : syracuseStep 2090651 = 3135977) B3135977
theorem B9536309 : Blo 2089435 9536309 := bbase (se 5 (by rfl) ⟨447014, by rfl⟩ : syracuseStep 9536309 = 894029) (by norm_num)
theorem B6357539 : Blo 2089435 6357539 := bstep (se 1 (by rfl) ⟨4768154, by rfl⟩ : syracuseStep 6357539 = 9536309) B9536309
theorem B16953437 : Blo 2089435 16953437 := bstep (se 3 (by rfl) ⟨3178769, by rfl⟩ : syracuseStep 16953437 = 6357539) B6357539
theorem B11302291 : Blo 2089435 11302291 := bstep (se 1 (by rfl) ⟨8476718, by rfl⟩ : syracuseStep 11302291 = 16953437) B16953437
theorem B15069721 : Blo 2089435 15069721 := bstep (se 2 (by rfl) ⟨5651145, by rfl⟩ : syracuseStep 15069721 = 11302291) B11302291
theorem B20092961 : Blo 2089435 20092961 := bstep (se 2 (by rfl) ⟨7534860, by rfl⟩ : syracuseStep 20092961 = 15069721) B15069721
theorem B13395307 : Blo 2089435 13395307 := bstep (se 1 (by rfl) ⟨10046480, by rfl⟩ : syracuseStep 13395307 = 20092961) B20092961
theorem B17860409 : Blo 2089435 17860409 := bstep (se 2 (by rfl) ⟨6697653, by rfl⟩ : syracuseStep 17860409 = 13395307) B13395307
theorem B11906939 : Blo 2089435 11906939 := bstep (se 1 (by rfl) ⟨8930204, by rfl⟩ : syracuseStep 11906939 = 17860409) B17860409
theorem B7937959 : Blo 2089435 7937959 := bstep (se 1 (by rfl) ⟨5953469, by rfl⟩ : syracuseStep 7937959 = 11906939) B11906939
theorem B10583945 : Blo 2089435 10583945 := bstep (se 2 (by rfl) ⟨3968979, by rfl⟩ : syracuseStep 10583945 = 7937959) B7937959
theorem B7055963 : Blo 2089435 7055963 := bstep (se 1 (by rfl) ⟨5291972, by rfl⟩ : syracuseStep 7055963 = 10583945) B10583945
theorem B4703975 : Blo 2089435 4703975 := bstep (se 1 (by rfl) ⟨3527981, by rfl⟩ : syracuseStep 4703975 = 7055963) B7055963
theorem B3135983 : Blo 2089435 3135983 := bstep (se 1 (by rfl) ⟨2351987, by rfl⟩ : syracuseStep 3135983 = 4703975) B4703975
theorem B2090655 : Blo 2089435 2090655 := bstep (se 1 (by rfl) ⟨1567991, by rfl⟩ : syracuseStep 2090655 = 3135983) B3135983
theorem B3135989 : Blo 2089435 3135989 := bbase (se 5 (by rfl) ⟨146999, by rfl⟩ : syracuseStep 3135989 = 293999) (by norm_num)
theorem B2090659 : Blo 2089435 2090659 := bstep (se 1 (by rfl) ⟨1567994, by rfl⟩ : syracuseStep 2090659 = 3135989) B3135989
theorem B5953493 : Blo 2089435 5953493 := bbase (se 7 (by rfl) ⟨69767, by rfl⟩ : syracuseStep 5953493 = 139535) (by norm_num)
theorem B3968995 : Blo 2089435 3968995 := bstep (se 1 (by rfl) ⟨2976746, by rfl⟩ : syracuseStep 3968995 = 5953493) B5953493
theorem B5291993 : Blo 2089435 5291993 := bstep (se 2 (by rfl) ⟨1984497, by rfl⟩ : syracuseStep 5291993 = 3968995) B3968995
theorem B3527995 : Blo 2089435 3527995 := bstep (se 1 (by rfl) ⟨2645996, by rfl⟩ : syracuseStep 3527995 = 5291993) B5291993
theorem B4703993 : Blo 2089435 4703993 := bstep (se 2 (by rfl) ⟨1763997, by rfl⟩ : syracuseStep 4703993 = 3527995) B3527995
theorem B3135995 : Blo 2089435 3135995 := bstep (se 1 (by rfl) ⟨2351996, by rfl⟩ : syracuseStep 3135995 = 4703993) B4703993
theorem B2090663 : Blo 2089435 2090663 := bstep (se 1 (by rfl) ⟨1567997, by rfl⟩ : syracuseStep 2090663 = 3135995) B3135995
theorem B2352001 : Blo 2089435 2352001 := bbase (se 2 (by rfl) ⟨882000, by rfl⟩ : syracuseStep 2352001 = 1764001) (by norm_num)
theorem B3136001 : Blo 2089435 3136001 := bstep (se 2 (by rfl) ⟨1176000, by rfl⟩ : syracuseStep 3136001 = 2352001) B2352001
theorem B2090667 : Blo 2089435 2090667 := bstep (se 1 (by rfl) ⟨1568000, by rfl⟩ : syracuseStep 2090667 = 3136001) B3136001
theorem B5292013 : Blo 2089435 5292013 := bbase (se 3 (by rfl) ⟨992252, by rfl⟩ : syracuseStep 5292013 = 1984505) (by norm_num)
theorem B7056017 : Blo 2089435 7056017 := bstep (se 2 (by rfl) ⟨2646006, by rfl⟩ : syracuseStep 7056017 = 5292013) B5292013
theorem B4704011 : Blo 2089435 4704011 := bstep (se 1 (by rfl) ⟨3528008, by rfl⟩ : syracuseStep 4704011 = 7056017) B7056017
theorem B3136007 : Blo 2089435 3136007 := bstep (se 1 (by rfl) ⟨2352005, by rfl⟩ : syracuseStep 3136007 = 4704011) B4704011
theorem B2090671 : Blo 2089435 2090671 := bstep (se 1 (by rfl) ⟨1568003, by rfl⟩ : syracuseStep 2090671 = 3136007) B3136007
theorem B3136013 : Blo 2089435 3136013 := bbase (se 3 (by rfl) ⟨588002, by rfl⟩ : syracuseStep 3136013 = 1176005) (by norm_num)
theorem B2090675 : Blo 2089435 2090675 := bstep (se 1 (by rfl) ⟨1568006, by rfl⟩ : syracuseStep 2090675 = 3136013) B3136013
theorem B4704029 : Blo 2089435 4704029 := bbase (se 3 (by rfl) ⟨882005, by rfl⟩ : syracuseStep 4704029 = 1764011) (by norm_num)
theorem B3136019 : Blo 2089435 3136019 := bstep (se 1 (by rfl) ⟨2352014, by rfl⟩ : syracuseStep 3136019 = 4704029) B4704029
theorem B2090679 : Blo 2089435 2090679 := bstep (se 1 (by rfl) ⟨1568009, by rfl⟩ : syracuseStep 2090679 = 3136019) B3136019
theorem B3528029 : Blo 2089435 3528029 := bbase (se 3 (by rfl) ⟨661505, by rfl⟩ : syracuseStep 3528029 = 1323011) (by norm_num)
theorem B2352019 : Blo 2089435 2352019 := bstep (se 1 (by rfl) ⟨1764014, by rfl⟩ : syracuseStep 2352019 = 3528029) B3528029
theorem B3136025 : Blo 2089435 3136025 := bstep (se 2 (by rfl) ⟨1176009, by rfl⟩ : syracuseStep 3136025 = 2352019) B2352019
theorem B2090683 : Blo 2089435 2090683 := bstep (se 1 (by rfl) ⟨1568012, by rfl⟩ : syracuseStep 2090683 = 3136025) B3136025
theorem B8930341 : Blo 2089435 8930341 := bbase (se 4 (by rfl) ⟨837219, by rfl⟩ : syracuseStep 8930341 = 1674439) (by norm_num)
theorem B11907121 : Blo 2089435 11907121 := bstep (se 2 (by rfl) ⟨4465170, by rfl⟩ : syracuseStep 11907121 = 8930341) B8930341
theorem B15876161 : Blo 2089435 15876161 := bstep (se 2 (by rfl) ⟨5953560, by rfl⟩ : syracuseStep 15876161 = 11907121) B11907121
theorem B10584107 : Blo 2089435 10584107 := bstep (se 1 (by rfl) ⟨7938080, by rfl⟩ : syracuseStep 10584107 = 15876161) B15876161
theorem B7056071 : Blo 2089435 7056071 := bstep (se 1 (by rfl) ⟨5292053, by rfl⟩ : syracuseStep 7056071 = 10584107) B10584107
theorem B4704047 : Blo 2089435 4704047 := bstep (se 1 (by rfl) ⟨3528035, by rfl⟩ : syracuseStep 4704047 = 7056071) B7056071
theorem B3136031 : Blo 2089435 3136031 := bstep (se 1 (by rfl) ⟨2352023, by rfl⟩ : syracuseStep 3136031 = 4704047) B4704047
theorem B2090687 : Blo 2089435 2090687 := bstep (se 1 (by rfl) ⟨1568015, by rfl⟩ : syracuseStep 2090687 = 3136031) B3136031
theorem B3136037 : Blo 2089435 3136037 := bbase (se 4 (by rfl) ⟨294003, by rfl⟩ : syracuseStep 3136037 = 588007) (by norm_num)
theorem B2090691 : Blo 2089435 2090691 := bstep (se 1 (by rfl) ⟨1568018, by rfl⟩ : syracuseStep 2090691 = 3136037) B3136037
theorem B2646037 : Blo 2089435 2646037 := bbase (se 6 (by rfl) ⟨62016, by rfl⟩ : syracuseStep 2646037 = 124033) (by norm_num)
theorem B3528049 : Blo 2089435 3528049 := bstep (se 2 (by rfl) ⟨1323018, by rfl⟩ : syracuseStep 3528049 = 2646037) B2646037
theorem B4704065 : Blo 2089435 4704065 := bstep (se 2 (by rfl) ⟨1764024, by rfl⟩ : syracuseStep 4704065 = 3528049) B3528049
theorem B3136043 : Blo 2089435 3136043 := bstep (se 1 (by rfl) ⟨2352032, by rfl⟩ : syracuseStep 3136043 = 4704065) B4704065
theorem B2090695 : Blo 2089435 2090695 := bstep (se 1 (by rfl) ⟨1568021, by rfl⟩ : syracuseStep 2090695 = 3136043) B3136043
theorem B2352037 : Blo 2089435 2352037 := bbase (se 4 (by rfl) ⟨220503, by rfl⟩ : syracuseStep 2352037 = 441007) (by norm_num)
theorem B3136049 : Blo 2089435 3136049 := bstep (se 2 (by rfl) ⟨1176018, by rfl⟩ : syracuseStep 3136049 = 2352037) B2352037
theorem B2090699 : Blo 2089435 2090699 := bstep (se 1 (by rfl) ⟨1568024, by rfl⟩ : syracuseStep 2090699 = 3136049) B3136049
theorem B6034837 : Blo 2089435 6034837 := bbase (se 6 (by rfl) ⟨141441, by rfl⟩ : syracuseStep 6034837 = 282883) (by norm_num)
theorem B8046449 : Blo 2089435 8046449 := bstep (se 2 (by rfl) ⟨3017418, by rfl⟩ : syracuseStep 8046449 = 6034837) B6034837
theorem B5364299 : Blo 2089435 5364299 := bstep (se 1 (by rfl) ⟨4023224, by rfl⟩ : syracuseStep 5364299 = 8046449) B8046449
theorem B3576199 : Blo 2089435 3576199 := bstep (se 1 (by rfl) ⟨2682149, by rfl⟩ : syracuseStep 3576199 = 5364299) B5364299
theorem B4768265 : Blo 2089435 4768265 := bstep (se 2 (by rfl) ⟨1788099, by rfl⟩ : syracuseStep 4768265 = 3576199) B3576199
theorem B12715373 : Blo 2089435 12715373 := bstep (se 3 (by rfl) ⟨2384132, by rfl⟩ : syracuseStep 12715373 = 4768265) B4768265
theorem B8476915 : Blo 2089435 8476915 := bstep (se 1 (by rfl) ⟨6357686, by rfl⟩ : syracuseStep 8476915 = 12715373) B12715373
theorem B11302553 : Blo 2089435 11302553 := bstep (se 2 (by rfl) ⟨4238457, by rfl⟩ : syracuseStep 11302553 = 8476915) B8476915
theorem B7535035 : Blo 2089435 7535035 := bstep (se 1 (by rfl) ⟨5651276, by rfl⟩ : syracuseStep 7535035 = 11302553) B11302553
theorem B10046713 : Blo 2089435 10046713 := bstep (se 2 (by rfl) ⟨3767517, by rfl⟩ : syracuseStep 10046713 = 7535035) B7535035
theorem B13395617 : Blo 2089435 13395617 := bstep (se 2 (by rfl) ⟨5023356, by rfl⟩ : syracuseStep 13395617 = 10046713) B10046713
theorem B8930411 : Blo 2089435 8930411 := bstep (se 1 (by rfl) ⟨6697808, by rfl⟩ : syracuseStep 8930411 = 13395617) B13395617
theorem B5953607 : Blo 2089435 5953607 := bstep (se 1 (by rfl) ⟨4465205, by rfl⟩ : syracuseStep 5953607 = 8930411) B8930411
theorem B3969071 : Blo 2089435 3969071 := bstep (se 1 (by rfl) ⟨2976803, by rfl⟩ : syracuseStep 3969071 = 5953607) B5953607
theorem B2646047 : Blo 2089435 2646047 := bstep (se 1 (by rfl) ⟨1984535, by rfl⟩ : syracuseStep 2646047 = 3969071) B3969071
theorem B7056125 : Blo 2089435 7056125 := bstep (se 3 (by rfl) ⟨1323023, by rfl⟩ : syracuseStep 7056125 = 2646047) B2646047
theorem B4704083 : Blo 2089435 4704083 := bstep (se 1 (by rfl) ⟨3528062, by rfl⟩ : syracuseStep 4704083 = 7056125) B7056125
theorem B3136055 : Blo 2089435 3136055 := bstep (se 1 (by rfl) ⟨2352041, by rfl⟩ : syracuseStep 3136055 = 4704083) B4704083
theorem B2090703 : Blo 2089435 2090703 := bstep (se 1 (by rfl) ⟨1568027, by rfl⟩ : syracuseStep 2090703 = 3136055) B3136055
theorem B3136061 : Blo 2089435 3136061 := bbase (se 3 (by rfl) ⟨588011, by rfl⟩ : syracuseStep 3136061 = 1176023) (by norm_num)
theorem B2090707 : Blo 2089435 2090707 := bstep (se 1 (by rfl) ⟨1568030, by rfl⟩ : syracuseStep 2090707 = 3136061) B3136061
theorem B4704101 : Blo 2089435 4704101 := bbase (se 4 (by rfl) ⟨441009, by rfl⟩ : syracuseStep 4704101 = 882019) (by norm_num)
theorem B3136067 : Blo 2089435 3136067 := bstep (se 1 (by rfl) ⟨2352050, by rfl⟩ : syracuseStep 3136067 = 4704101) B4704101
theorem B2090711 : Blo 2089435 2090711 := bstep (se 1 (by rfl) ⟨1568033, by rfl⟩ : syracuseStep 2090711 = 3136067) B3136067
theorem B5292125 : Blo 2089435 5292125 := bbase (se 3 (by rfl) ⟨992273, by rfl⟩ : syracuseStep 5292125 = 1984547) (by norm_num)
theorem B3528083 : Blo 2089435 3528083 := bstep (se 1 (by rfl) ⟨2646062, by rfl⟩ : syracuseStep 3528083 = 5292125) B5292125
theorem B2352055 : Blo 2089435 2352055 := bstep (se 1 (by rfl) ⟨1764041, by rfl⟩ : syracuseStep 2352055 = 3528083) B3528083
theorem B3136073 : Blo 2089435 3136073 := bstep (se 2 (by rfl) ⟨1176027, by rfl⟩ : syracuseStep 3136073 = 2352055) B2352055
theorem B2090715 : Blo 2089435 2090715 := bstep (se 1 (by rfl) ⟨1568036, by rfl⟩ : syracuseStep 2090715 = 3136073) B3136073
theorem B3969101 : Blo 2089435 3969101 := bbase (se 3 (by rfl) ⟨744206, by rfl⟩ : syracuseStep 3969101 = 1488413) (by norm_num)
theorem B10584269 : Blo 2089435 10584269 := bstep (se 3 (by rfl) ⟨1984550, by rfl⟩ : syracuseStep 10584269 = 3969101) B3969101
theorem B7056179 : Blo 2089435 7056179 := bstep (se 1 (by rfl) ⟨5292134, by rfl⟩ : syracuseStep 7056179 = 10584269) B10584269
theorem B4704119 : Blo 2089435 4704119 := bstep (se 1 (by rfl) ⟨3528089, by rfl⟩ : syracuseStep 4704119 = 7056179) B7056179
theorem B3136079 : Blo 2089435 3136079 := bstep (se 1 (by rfl) ⟨2352059, by rfl⟩ : syracuseStep 3136079 = 4704119) B4704119
theorem B2090719 : Blo 2089435 2090719 := bstep (se 1 (by rfl) ⟨1568039, by rfl⟩ : syracuseStep 2090719 = 3136079) B3136079
theorem B3136085 : Blo 2089435 3136085 := bbase (se 8 (by rfl) ⟨18375, by rfl⟩ : syracuseStep 3136085 = 36751) (by norm_num)
theorem B2090723 : Blo 2089435 2090723 := bstep (se 1 (by rfl) ⟨1568042, by rfl⟩ : syracuseStep 2090723 = 3136085) B3136085
theorem B2682181 : Blo 2089435 2682181 := bbase (se 4 (by rfl) ⟨251454, by rfl⟩ : syracuseStep 2682181 = 502909) (by norm_num)
theorem B3576241 : Blo 2089435 3576241 := bstep (se 2 (by rfl) ⟨1341090, by rfl⟩ : syracuseStep 3576241 = 2682181) B2682181
theorem B4768321 : Blo 2089435 4768321 := bstep (se 2 (by rfl) ⟨1788120, by rfl⟩ : syracuseStep 4768321 = 3576241) B3576241
theorem B6357761 : Blo 2089435 6357761 := bstep (se 2 (by rfl) ⟨2384160, by rfl⟩ : syracuseStep 6357761 = 4768321) B4768321
theorem B4238507 : Blo 2089435 4238507 := bstep (se 1 (by rfl) ⟨3178880, by rfl⟩ : syracuseStep 4238507 = 6357761) B6357761
theorem B2825671 : Blo 2089435 2825671 := bstep (se 1 (by rfl) ⟨2119253, by rfl⟩ : syracuseStep 2825671 = 4238507) B4238507
theorem B3767561 : Blo 2089435 3767561 := bstep (se 2 (by rfl) ⟨1412835, by rfl⟩ : syracuseStep 3767561 = 2825671) B2825671
theorem B2511707 : Blo 2089435 2511707 := bstep (se 1 (by rfl) ⟨1883780, by rfl⟩ : syracuseStep 2511707 = 3767561) B3767561
theorem B6697885 : Blo 2089435 6697885 := bstep (se 3 (by rfl) ⟨1255853, by rfl⟩ : syracuseStep 6697885 = 2511707) B2511707
theorem B8930513 : Blo 2089435 8930513 := bstep (se 2 (by rfl) ⟨3348942, by rfl⟩ : syracuseStep 8930513 = 6697885) B6697885
theorem B5953675 : Blo 2089435 5953675 := bstep (se 1 (by rfl) ⟨4465256, by rfl⟩ : syracuseStep 5953675 = 8930513) B8930513
theorem B7938233 : Blo 2089435 7938233 := bstep (se 2 (by rfl) ⟨2976837, by rfl⟩ : syracuseStep 7938233 = 5953675) B5953675
theorem B5292155 : Blo 2089435 5292155 := bstep (se 1 (by rfl) ⟨3969116, by rfl⟩ : syracuseStep 5292155 = 7938233) B7938233
theorem B3528103 : Blo 2089435 3528103 := bstep (se 1 (by rfl) ⟨2646077, by rfl⟩ : syracuseStep 3528103 = 5292155) B5292155
theorem B4704137 : Blo 2089435 4704137 := bstep (se 2 (by rfl) ⟨1764051, by rfl⟩ : syracuseStep 4704137 = 3528103) B3528103
theorem B3136091 : Blo 2089435 3136091 := bstep (se 1 (by rfl) ⟨2352068, by rfl⟩ : syracuseStep 3136091 = 4704137) B4704137
theorem B2090727 : Blo 2089435 2090727 := bstep (se 1 (by rfl) ⟨1568045, by rfl⟩ : syracuseStep 2090727 = 3136091) B3136091
theorem B2352073 : Blo 2089435 2352073 := bbase (se 2 (by rfl) ⟨882027, by rfl⟩ : syracuseStep 2352073 = 1764055) (by norm_num)
theorem B3136097 : Blo 2089435 3136097 := bstep (se 2 (by rfl) ⟨1176036, by rfl⟩ : syracuseStep 3136097 = 2352073) B2352073
theorem B2090731 : Blo 2089435 2090731 := bstep (se 1 (by rfl) ⟨1568048, by rfl⟩ : syracuseStep 2090731 = 3136097) B3136097
theorem B8477045 : Blo 2089435 8477045 := bbase (se 5 (by rfl) ⟨397361, by rfl⟩ : syracuseStep 8477045 = 794723) (by norm_num)
theorem B5651363 : Blo 2089435 5651363 := bstep (se 1 (by rfl) ⟨4238522, by rfl⟩ : syracuseStep 5651363 = 8477045) B8477045
theorem B3767575 : Blo 2089435 3767575 := bstep (se 1 (by rfl) ⟨2825681, by rfl⟩ : syracuseStep 3767575 = 5651363) B5651363
theorem B5023433 : Blo 2089435 5023433 := bstep (se 2 (by rfl) ⟨1883787, by rfl⟩ : syracuseStep 5023433 = 3767575) B3767575
theorem B3348955 : Blo 2089435 3348955 := bstep (se 1 (by rfl) ⟨2511716, by rfl⟩ : syracuseStep 3348955 = 5023433) B5023433
theorem B17861093 : Blo 2089435 17861093 := bstep (se 4 (by rfl) ⟨1674477, by rfl⟩ : syracuseStep 17861093 = 3348955) B3348955
theorem B11907395 : Blo 2089435 11907395 := bstep (se 1 (by rfl) ⟨8930546, by rfl⟩ : syracuseStep 11907395 = 17861093) B17861093
theorem B7938263 : Blo 2089435 7938263 := bstep (se 1 (by rfl) ⟨5953697, by rfl⟩ : syracuseStep 7938263 = 11907395) B11907395
theorem B5292175 : Blo 2089435 5292175 := bstep (se 1 (by rfl) ⟨3969131, by rfl⟩ : syracuseStep 5292175 = 7938263) B7938263
theorem B7056233 : Blo 2089435 7056233 := bstep (se 2 (by rfl) ⟨2646087, by rfl⟩ : syracuseStep 7056233 = 5292175) B5292175
theorem B4704155 : Blo 2089435 4704155 := bstep (se 1 (by rfl) ⟨3528116, by rfl⟩ : syracuseStep 4704155 = 7056233) B7056233
theorem B3136103 : Blo 2089435 3136103 := bstep (se 1 (by rfl) ⟨2352077, by rfl⟩ : syracuseStep 3136103 = 4704155) B4704155
theorem B2090735 : Blo 2089435 2090735 := bstep (se 1 (by rfl) ⟨1568051, by rfl⟩ : syracuseStep 2090735 = 3136103) B3136103
theorem B3136109 : Blo 2089435 3136109 := bbase (se 3 (by rfl) ⟨588020, by rfl⟩ : syracuseStep 3136109 = 1176041) (by norm_num)
theorem B2090739 : Blo 2089435 2090739 := bstep (se 1 (by rfl) ⟨1568054, by rfl⟩ : syracuseStep 2090739 = 3136109) B3136109
theorem B4704173 : Blo 2089435 4704173 := bbase (se 3 (by rfl) ⟨882032, by rfl⟩ : syracuseStep 4704173 = 1764065) (by norm_num)
theorem B3136115 : Blo 2089435 3136115 := bstep (se 1 (by rfl) ⟨2352086, by rfl⟩ : syracuseStep 3136115 = 4704173) B4704173
theorem B2090743 : Blo 2089435 2090743 := bstep (se 1 (by rfl) ⟨1568057, by rfl⟩ : syracuseStep 2090743 = 3136115) B3136115
theorem B5953733 : Blo 2089435 5953733 := bbase (se 4 (by rfl) ⟨558162, by rfl⟩ : syracuseStep 5953733 = 1116325) (by norm_num)
theorem B3969155 : Blo 2089435 3969155 := bstep (se 1 (by rfl) ⟨2976866, by rfl⟩ : syracuseStep 3969155 = 5953733) B5953733
theorem B2646103 : Blo 2089435 2646103 := bstep (se 1 (by rfl) ⟨1984577, by rfl⟩ : syracuseStep 2646103 = 3969155) B3969155
theorem B3528137 : Blo 2089435 3528137 := bstep (se 2 (by rfl) ⟨1323051, by rfl⟩ : syracuseStep 3528137 = 2646103) B2646103
theorem B2352091 : Blo 2089435 2352091 := bstep (se 1 (by rfl) ⟨1764068, by rfl⟩ : syracuseStep 2352091 = 3528137) B3528137
theorem B3136121 : Blo 2089435 3136121 := bstep (se 2 (by rfl) ⟨1176045, by rfl⟩ : syracuseStep 3136121 = 2352091) B2352091
theorem B2090747 : Blo 2089435 2090747 := bstep (se 1 (by rfl) ⟨1568060, by rfl⟩ : syracuseStep 2090747 = 3136121) B3136121
theorem B2119277 : Blo 2089435 2119277 := bbase (se 3 (by rfl) ⟨397364, by rfl⟩ : syracuseStep 2119277 = 794729) (by norm_num)
theorem B5651405 : Blo 2089435 5651405 := bstep (se 3 (by rfl) ⟨1059638, by rfl⟩ : syracuseStep 5651405 = 2119277) B2119277
theorem B3767603 : Blo 2089435 3767603 := bstep (se 1 (by rfl) ⟨2825702, by rfl⟩ : syracuseStep 3767603 = 5651405) B5651405
theorem B40187765 : Blo 2089435 40187765 := bstep (se 5 (by rfl) ⟨1883801, by rfl⟩ : syracuseStep 40187765 = 3767603) B3767603
theorem B26791843 : Blo 2089435 26791843 := bstep (se 1 (by rfl) ⟨20093882, by rfl⟩ : syracuseStep 26791843 = 40187765) B40187765
theorem B35722457 : Blo 2089435 35722457 := bstep (se 2 (by rfl) ⟨13395921, by rfl⟩ : syracuseStep 35722457 = 26791843) B26791843
theorem B23814971 : Blo 2089435 23814971 := bstep (se 1 (by rfl) ⟨17861228, by rfl⟩ : syracuseStep 23814971 = 35722457) B35722457
theorem B15876647 : Blo 2089435 15876647 := bstep (se 1 (by rfl) ⟨11907485, by rfl⟩ : syracuseStep 15876647 = 23814971) B23814971
theorem B10584431 : Blo 2089435 10584431 := bstep (se 1 (by rfl) ⟨7938323, by rfl⟩ : syracuseStep 10584431 = 15876647) B15876647
theorem B7056287 : Blo 2089435 7056287 := bstep (se 1 (by rfl) ⟨5292215, by rfl⟩ : syracuseStep 7056287 = 10584431) B10584431
theorem B4704191 : Blo 2089435 4704191 := bstep (se 1 (by rfl) ⟨3528143, by rfl⟩ : syracuseStep 4704191 = 7056287) B7056287
theorem B3136127 : Blo 2089435 3136127 := bstep (se 1 (by rfl) ⟨2352095, by rfl⟩ : syracuseStep 3136127 = 4704191) B4704191
theorem B2090751 : Blo 2089435 2090751 := bstep (se 1 (by rfl) ⟨1568063, by rfl⟩ : syracuseStep 2090751 = 3136127) B3136127
theorem B3136133 : Blo 2089435 3136133 := bbase (se 4 (by rfl) ⟨294012, by rfl⟩ : syracuseStep 3136133 = 588025) (by norm_num)
theorem B2090755 : Blo 2089435 2090755 := bstep (se 1 (by rfl) ⟨1568066, by rfl⟩ : syracuseStep 2090755 = 3136133) B3136133
theorem B3528157 : Blo 2089435 3528157 := bbase (se 3 (by rfl) ⟨661529, by rfl⟩ : syracuseStep 3528157 = 1323059) (by norm_num)
theorem B4704209 : Blo 2089435 4704209 := bstep (se 2 (by rfl) ⟨1764078, by rfl⟩ : syracuseStep 4704209 = 3528157) B3528157
theorem B3136139 : Blo 2089435 3136139 := bstep (se 1 (by rfl) ⟨2352104, by rfl⟩ : syracuseStep 3136139 = 4704209) B4704209
theorem B2090759 : Blo 2089435 2090759 := bstep (se 1 (by rfl) ⟨1568069, by rfl⟩ : syracuseStep 2090759 = 3136139) B3136139
theorem B2352109 : Blo 2089435 2352109 := bbase (se 3 (by rfl) ⟨441020, by rfl⟩ : syracuseStep 2352109 = 882041) (by norm_num)
theorem B3136145 : Blo 2089435 3136145 := bstep (se 2 (by rfl) ⟨1176054, by rfl⟩ : syracuseStep 3136145 = 2352109) B2352109
theorem B2090763 : Blo 2089435 2090763 := bstep (se 1 (by rfl) ⟨1568072, by rfl⟩ : syracuseStep 2090763 = 3136145) B3136145
theorem B7056341 : Blo 2089435 7056341 := bbase (se 7 (by rfl) ⟨82691, by rfl⟩ : syracuseStep 7056341 = 165383) (by norm_num)
theorem B4704227 : Blo 2089435 4704227 := bstep (se 1 (by rfl) ⟨3528170, by rfl⟩ : syracuseStep 4704227 = 7056341) B7056341
theorem B3136151 : Blo 2089435 3136151 := bstep (se 1 (by rfl) ⟨2352113, by rfl⟩ : syracuseStep 3136151 = 4704227) B4704227
theorem B2090767 : Blo 2089435 2090767 := bstep (se 1 (by rfl) ⟨1568075, by rfl⟩ : syracuseStep 2090767 = 3136151) B3136151
theorem B3136157 : Blo 2089435 3136157 := bbase (se 3 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 3136157 = 1176059) (by norm_num)
theorem B2090771 : Blo 2089435 2090771 := bstep (se 1 (by rfl) ⟨1568078, by rfl⟩ : syracuseStep 2090771 = 3136157) B3136157
theorem B4704245 : Blo 2089435 4704245 := bbase (se 5 (by rfl) ⟨220511, by rfl⟩ : syracuseStep 4704245 = 441023) (by norm_num)
theorem B3136163 : Blo 2089435 3136163 := bstep (se 1 (by rfl) ⟨2352122, by rfl⟩ : syracuseStep 3136163 = 4704245) B4704245
theorem B2090775 : Blo 2089435 2090775 := bstep (se 1 (by rfl) ⟨1568081, by rfl⟩ : syracuseStep 2090775 = 3136163) B3136163
theorem B4526293 : Blo 2089435 4526293 := bbase (se 7 (by rfl) ⟨53042, by rfl⟩ : syracuseStep 4526293 = 106085) (by norm_num)
theorem B6035057 : Blo 2089435 6035057 := bstep (se 2 (by rfl) ⟨2263146, by rfl⟩ : syracuseStep 6035057 = 4526293) B4526293
theorem B4023371 : Blo 2089435 4023371 := bstep (se 1 (by rfl) ⟨3017528, by rfl⟩ : syracuseStep 4023371 = 6035057) B6035057
theorem B2682247 : Blo 2089435 2682247 := bstep (se 1 (by rfl) ⟨2011685, by rfl⟩ : syracuseStep 2682247 = 4023371) B4023371
theorem B3576329 : Blo 2089435 3576329 := bstep (se 2 (by rfl) ⟨1341123, by rfl⟩ : syracuseStep 3576329 = 2682247) B2682247
theorem B2384219 : Blo 2089435 2384219 := bstep (se 1 (by rfl) ⟨1788164, by rfl⟩ : syracuseStep 2384219 = 3576329) B3576329
theorem B6357917 : Blo 2089435 6357917 := bstep (se 3 (by rfl) ⟨1192109, by rfl⟩ : syracuseStep 6357917 = 2384219) B2384219
theorem B4238611 : Blo 2089435 4238611 := bstep (se 1 (by rfl) ⟨3178958, by rfl⟩ : syracuseStep 4238611 = 6357917) B6357917
theorem B90423701 : Blo 2089435 90423701 := bstep (se 6 (by rfl) ⟨2119305, by rfl⟩ : syracuseStep 90423701 = 4238611) B4238611
theorem B60282467 : Blo 2089435 60282467 := bstep (se 1 (by rfl) ⟨45211850, by rfl⟩ : syracuseStep 60282467 = 90423701) B90423701
theorem B40188311 : Blo 2089435 40188311 := bstep (se 1 (by rfl) ⟨30141233, by rfl⟩ : syracuseStep 40188311 = 60282467) B60282467
theorem B26792207 : Blo 2089435 26792207 := bstep (se 1 (by rfl) ⟨20094155, by rfl⟩ : syracuseStep 26792207 = 40188311) B40188311
theorem B17861471 : Blo 2089435 17861471 := bstep (se 1 (by rfl) ⟨13396103, by rfl⟩ : syracuseStep 17861471 = 26792207) B26792207
theorem B11907647 : Blo 2089435 11907647 := bstep (se 1 (by rfl) ⟨8930735, by rfl⟩ : syracuseStep 11907647 = 17861471) B17861471
theorem B7938431 : Blo 2089435 7938431 := bstep (se 1 (by rfl) ⟨5953823, by rfl⟩ : syracuseStep 7938431 = 11907647) B11907647
theorem B5292287 : Blo 2089435 5292287 := bstep (se 1 (by rfl) ⟨3969215, by rfl⟩ : syracuseStep 5292287 = 7938431) B7938431
theorem B3528191 : Blo 2089435 3528191 := bstep (se 1 (by rfl) ⟨2646143, by rfl⟩ : syracuseStep 3528191 = 5292287) B5292287
theorem B2352127 : Blo 2089435 2352127 := bstep (se 1 (by rfl) ⟨1764095, by rfl⟩ : syracuseStep 2352127 = 3528191) B3528191
theorem B3136169 : Blo 2089435 3136169 := bstep (se 2 (by rfl) ⟨1176063, by rfl⟩ : syracuseStep 3136169 = 2352127) B2352127
theorem B2090779 : Blo 2089435 2090779 := bstep (se 1 (by rfl) ⟨1568084, by rfl⟩ : syracuseStep 2090779 = 3136169) B3136169
theorem B2976917 : Blo 2089435 2976917 := bbase (se 6 (by rfl) ⟨69771, by rfl⟩ : syracuseStep 2976917 = 139543) (by norm_num)
theorem B7938445 : Blo 2089435 7938445 := bstep (se 3 (by rfl) ⟨1488458, by rfl⟩ : syracuseStep 7938445 = 2976917) B2976917
theorem B10584593 : Blo 2089435 10584593 := bstep (se 2 (by rfl) ⟨3969222, by rfl⟩ : syracuseStep 10584593 = 7938445) B7938445
theorem B7056395 : Blo 2089435 7056395 := bstep (se 1 (by rfl) ⟨5292296, by rfl⟩ : syracuseStep 7056395 = 10584593) B10584593
theorem B4704263 : Blo 2089435 4704263 := bstep (se 1 (by rfl) ⟨3528197, by rfl⟩ : syracuseStep 4704263 = 7056395) B7056395
theorem B3136175 : Blo 2089435 3136175 := bstep (se 1 (by rfl) ⟨2352131, by rfl⟩ : syracuseStep 3136175 = 4704263) B4704263
theorem B2090783 : Blo 2089435 2090783 := bstep (se 1 (by rfl) ⟨1568087, by rfl⟩ : syracuseStep 2090783 = 3136175) B3136175
theorem B3136181 : Blo 2089435 3136181 := bbase (se 5 (by rfl) ⟨147008, by rfl⟩ : syracuseStep 3136181 = 294017) (by norm_num)
theorem B2090787 : Blo 2089435 2090787 := bstep (se 1 (by rfl) ⟨1568090, by rfl⟩ : syracuseStep 2090787 = 3136181) B3136181
theorem B5292317 : Blo 2089435 5292317 := bbase (se 3 (by rfl) ⟨992309, by rfl⟩ : syracuseStep 5292317 = 1984619) (by norm_num)
theorem B3528211 : Blo 2089435 3528211 := bstep (se 1 (by rfl) ⟨2646158, by rfl⟩ : syracuseStep 3528211 = 5292317) B5292317
theorem B4704281 : Blo 2089435 4704281 := bstep (se 2 (by rfl) ⟨1764105, by rfl⟩ : syracuseStep 4704281 = 3528211) B3528211
theorem B3136187 : Blo 2089435 3136187 := bstep (se 1 (by rfl) ⟨2352140, by rfl⟩ : syracuseStep 3136187 = 4704281) B4704281
theorem B2090791 : Blo 2089435 2090791 := bstep (se 1 (by rfl) ⟨1568093, by rfl⟩ : syracuseStep 2090791 = 3136187) B3136187
theorem B2352145 : Blo 2089435 2352145 := bbase (se 2 (by rfl) ⟨882054, by rfl⟩ : syracuseStep 2352145 = 1764109) (by norm_num)
theorem B3136193 : Blo 2089435 3136193 := bstep (se 2 (by rfl) ⟨1176072, by rfl⟩ : syracuseStep 3136193 = 2352145) B2352145
theorem B2090795 : Blo 2089435 2090795 := bstep (se 1 (by rfl) ⟨1568096, by rfl⟩ : syracuseStep 2090795 = 3136193) B3136193
theorem B3969253 : Blo 2089435 3969253 := bbase (se 4 (by rfl) ⟨372117, by rfl⟩ : syracuseStep 3969253 = 744235) (by norm_num)
theorem B5292337 : Blo 2089435 5292337 := bstep (se 2 (by rfl) ⟨1984626, by rfl⟩ : syracuseStep 5292337 = 3969253) B3969253
theorem B7056449 : Blo 2089435 7056449 := bstep (se 2 (by rfl) ⟨2646168, by rfl⟩ : syracuseStep 7056449 = 5292337) B5292337
theorem B4704299 : Blo 2089435 4704299 := bstep (se 1 (by rfl) ⟨3528224, by rfl⟩ : syracuseStep 4704299 = 7056449) B7056449
theorem B3136199 : Blo 2089435 3136199 := bstep (se 1 (by rfl) ⟨2352149, by rfl⟩ : syracuseStep 3136199 = 4704299) B4704299
theorem B2090799 : Blo 2089435 2090799 := bstep (se 1 (by rfl) ⟨1568099, by rfl⟩ : syracuseStep 2090799 = 3136199) B3136199
theorem B3136205 : Blo 2089435 3136205 := bbase (se 3 (by rfl) ⟨588038, by rfl⟩ : syracuseStep 3136205 = 1176077) (by norm_num)
theorem B2090803 : Blo 2089435 2090803 := bstep (se 1 (by rfl) ⟨1568102, by rfl⟩ : syracuseStep 2090803 = 3136205) B3136205
theorem B4704317 : Blo 2089435 4704317 := bbase (se 3 (by rfl) ⟨882059, by rfl⟩ : syracuseStep 4704317 = 1764119) (by norm_num)
theorem B3136211 : Blo 2089435 3136211 := bstep (se 1 (by rfl) ⟨2352158, by rfl⟩ : syracuseStep 3136211 = 4704317) B4704317
theorem B2090807 : Blo 2089435 2090807 := bstep (se 1 (by rfl) ⟨1568105, by rfl⟩ : syracuseStep 2090807 = 3136211) B3136211
theorem B3528245 : Blo 2089435 3528245 := bbase (se 5 (by rfl) ⟨165386, by rfl⟩ : syracuseStep 3528245 = 330773) (by norm_num)
theorem B2352163 : Blo 2089435 2352163 := bstep (se 1 (by rfl) ⟨1764122, by rfl⟩ : syracuseStep 2352163 = 3528245) B3528245
theorem B3136217 : Blo 2089435 3136217 := bstep (se 2 (by rfl) ⟨1176081, by rfl⟩ : syracuseStep 3136217 = 2352163) B2352163
theorem B2090811 : Blo 2089435 2090811 := bstep (se 1 (by rfl) ⟨1568108, by rfl⟩ : syracuseStep 2090811 = 3136217) B3136217
theorem B5953925 : Blo 2089435 5953925 := bbase (se 4 (by rfl) ⟨558180, by rfl⟩ : syracuseStep 5953925 = 1116361) (by norm_num)
theorem B15877133 : Blo 2089435 15877133 := bstep (se 3 (by rfl) ⟨2976962, by rfl⟩ : syracuseStep 15877133 = 5953925) B5953925
theorem B10584755 : Blo 2089435 10584755 := bstep (se 1 (by rfl) ⟨7938566, by rfl⟩ : syracuseStep 10584755 = 15877133) B15877133
theorem B7056503 : Blo 2089435 7056503 := bstep (se 1 (by rfl) ⟨5292377, by rfl⟩ : syracuseStep 7056503 = 10584755) B10584755
theorem B4704335 : Blo 2089435 4704335 := bstep (se 1 (by rfl) ⟨3528251, by rfl⟩ : syracuseStep 4704335 = 7056503) B7056503
theorem B3136223 : Blo 2089435 3136223 := bstep (se 1 (by rfl) ⟨2352167, by rfl⟩ : syracuseStep 3136223 = 4704335) B4704335
theorem B2090815 : Blo 2089435 2090815 := bstep (se 1 (by rfl) ⟨1568111, by rfl⟩ : syracuseStep 2090815 = 3136223) B3136223
theorem B3136229 : Blo 2089435 3136229 := bbase (se 4 (by rfl) ⟨294021, by rfl⟩ : syracuseStep 3136229 = 588043) (by norm_num)
theorem B2090819 : Blo 2089435 2090819 := bstep (se 1 (by rfl) ⟨1568114, by rfl⟩ : syracuseStep 2090819 = 3136229) B3136229
theorem B4768541 : Blo 2089435 4768541 := bbase (se 3 (by rfl) ⟨894101, by rfl⟩ : syracuseStep 4768541 = 1788203) (by norm_num)
theorem B3179027 : Blo 2089435 3179027 := bstep (se 1 (by rfl) ⟨2384270, by rfl⟩ : syracuseStep 3179027 = 4768541) B4768541
theorem B8477405 : Blo 2089435 8477405 := bstep (se 3 (by rfl) ⟨1589513, by rfl⟩ : syracuseStep 8477405 = 3179027) B3179027
theorem B5651603 : Blo 2089435 5651603 := bstep (se 1 (by rfl) ⟨4238702, by rfl⟩ : syracuseStep 5651603 = 8477405) B8477405
theorem B3767735 : Blo 2089435 3767735 := bstep (se 1 (by rfl) ⟨2825801, by rfl⟩ : syracuseStep 3767735 = 5651603) B5651603
theorem B2511823 : Blo 2089435 2511823 := bstep (se 1 (by rfl) ⟨1883867, by rfl⟩ : syracuseStep 2511823 = 3767735) B3767735
theorem B3349097 : Blo 2089435 3349097 := bstep (se 2 (by rfl) ⟨1255911, by rfl⟩ : syracuseStep 3349097 = 2511823) B2511823
theorem B2232731 : Blo 2089435 2232731 := bstep (se 1 (by rfl) ⟨1674548, by rfl⟩ : syracuseStep 2232731 = 3349097) B3349097
theorem B5953949 : Blo 2089435 5953949 := bstep (se 3 (by rfl) ⟨1116365, by rfl⟩ : syracuseStep 5953949 = 2232731) B2232731
theorem B3969299 : Blo 2089435 3969299 := bstep (se 1 (by rfl) ⟨2976974, by rfl⟩ : syracuseStep 3969299 = 5953949) B5953949
theorem B2646199 : Blo 2089435 2646199 := bstep (se 1 (by rfl) ⟨1984649, by rfl⟩ : syracuseStep 2646199 = 3969299) B3969299
theorem B3528265 : Blo 2089435 3528265 := bstep (se 2 (by rfl) ⟨1323099, by rfl⟩ : syracuseStep 3528265 = 2646199) B2646199
theorem B4704353 : Blo 2089435 4704353 := bstep (se 2 (by rfl) ⟨1764132, by rfl⟩ : syracuseStep 4704353 = 3528265) B3528265
theorem B3136235 : Blo 2089435 3136235 := bstep (se 1 (by rfl) ⟨2352176, by rfl⟩ : syracuseStep 3136235 = 4704353) B4704353
theorem B2090823 : Blo 2089435 2090823 := bstep (se 1 (by rfl) ⟨1568117, by rfl⟩ : syracuseStep 2090823 = 3136235) B3136235
theorem B2352181 : Blo 2089435 2352181 := bbase (se 5 (by rfl) ⟨110258, by rfl⟩ : syracuseStep 2352181 = 220517) (by norm_num)
theorem B3136241 : Blo 2089435 3136241 := bstep (se 2 (by rfl) ⟨1176090, by rfl⟩ : syracuseStep 3136241 = 2352181) B2352181
theorem B2090827 : Blo 2089435 2090827 := bstep (se 1 (by rfl) ⟨1568120, by rfl⟩ : syracuseStep 2090827 = 3136241) B3136241
theorem B2646209 : Blo 2089435 2646209 := bbase (se 2 (by rfl) ⟨992328, by rfl⟩ : syracuseStep 2646209 = 1984657) (by norm_num)
theorem B7056557 : Blo 2089435 7056557 := bstep (se 3 (by rfl) ⟨1323104, by rfl⟩ : syracuseStep 7056557 = 2646209) B2646209
theorem B4704371 : Blo 2089435 4704371 := bstep (se 1 (by rfl) ⟨3528278, by rfl⟩ : syracuseStep 4704371 = 7056557) B7056557
theorem B3136247 : Blo 2089435 3136247 := bstep (se 1 (by rfl) ⟨2352185, by rfl⟩ : syracuseStep 3136247 = 4704371) B4704371
theorem B2090831 : Blo 2089435 2090831 := bstep (se 1 (by rfl) ⟨1568123, by rfl⟩ : syracuseStep 2090831 = 3136247) B3136247
theorem B3136253 : Blo 2089435 3136253 := bbase (se 3 (by rfl) ⟨588047, by rfl⟩ : syracuseStep 3136253 = 1176095) (by norm_num)
theorem B2090835 : Blo 2089435 2090835 := bstep (se 1 (by rfl) ⟨1568126, by rfl⟩ : syracuseStep 2090835 = 3136253) B3136253
theorem B4704389 : Blo 2089435 4704389 := bbase (se 4 (by rfl) ⟨441036, by rfl⟩ : syracuseStep 4704389 = 882073) (by norm_num)
theorem B3136259 : Blo 2089435 3136259 := bstep (se 1 (by rfl) ⟨2352194, by rfl⟩ : syracuseStep 3136259 = 4704389) B4704389
theorem B2090839 : Blo 2089435 2090839 := bstep (se 1 (by rfl) ⟨1568129, by rfl⟩ : syracuseStep 2090839 = 3136259) B3136259
theorem B9537173 : Blo 2089435 9537173 := bbase (se 6 (by rfl) ⟨223527, by rfl⟩ : syracuseStep 9537173 = 447055) (by norm_num)
theorem B6358115 : Blo 2089435 6358115 := bstep (se 1 (by rfl) ⟨4768586, by rfl⟩ : syracuseStep 6358115 = 9537173) B9537173
theorem B4238743 : Blo 2089435 4238743 := bstep (se 1 (by rfl) ⟨3179057, by rfl⟩ : syracuseStep 4238743 = 6358115) B6358115
theorem B5651657 : Blo 2089435 5651657 := bstep (se 2 (by rfl) ⟨2119371, by rfl⟩ : syracuseStep 5651657 = 4238743) B4238743
theorem B3767771 : Blo 2089435 3767771 := bstep (se 1 (by rfl) ⟨2825828, by rfl⟩ : syracuseStep 3767771 = 5651657) B5651657
theorem B2511847 : Blo 2089435 2511847 := bstep (se 1 (by rfl) ⟨1883885, by rfl⟩ : syracuseStep 2511847 = 3767771) B3767771
theorem B3349129 : Blo 2089435 3349129 := bstep (se 2 (by rfl) ⟨1255923, by rfl⟩ : syracuseStep 3349129 = 2511847) B2511847
theorem B4465505 : Blo 2089435 4465505 := bstep (se 2 (by rfl) ⟨1674564, by rfl⟩ : syracuseStep 4465505 = 3349129) B3349129
theorem B2977003 : Blo 2089435 2977003 := bstep (se 1 (by rfl) ⟨2232752, by rfl⟩ : syracuseStep 2977003 = 4465505) B4465505
theorem B3969337 : Blo 2089435 3969337 := bstep (se 2 (by rfl) ⟨1488501, by rfl⟩ : syracuseStep 3969337 = 2977003) B2977003
theorem B5292449 : Blo 2089435 5292449 := bstep (se 2 (by rfl) ⟨1984668, by rfl⟩ : syracuseStep 5292449 = 3969337) B3969337
theorem B3528299 : Blo 2089435 3528299 := bstep (se 1 (by rfl) ⟨2646224, by rfl⟩ : syracuseStep 3528299 = 5292449) B5292449
theorem B2352199 : Blo 2089435 2352199 := bstep (se 1 (by rfl) ⟨1764149, by rfl⟩ : syracuseStep 2352199 = 3528299) B3528299
theorem B3136265 : Blo 2089435 3136265 := bstep (se 2 (by rfl) ⟨1176099, by rfl⟩ : syracuseStep 3136265 = 2352199) B2352199
theorem B2090843 : Blo 2089435 2090843 := bstep (se 1 (by rfl) ⟨1568132, by rfl⟩ : syracuseStep 2090843 = 3136265) B3136265
theorem B10584917 : Blo 2089435 10584917 := bbase (se 9 (by rfl) ⟨31010, by rfl⟩ : syracuseStep 10584917 = 62021) (by norm_num)
theorem B7056611 : Blo 2089435 7056611 := bstep (se 1 (by rfl) ⟨5292458, by rfl⟩ : syracuseStep 7056611 = 10584917) B10584917
theorem B4704407 : Blo 2089435 4704407 := bstep (se 1 (by rfl) ⟨3528305, by rfl⟩ : syracuseStep 4704407 = 7056611) B7056611
theorem B3136271 : Blo 2089435 3136271 := bstep (se 1 (by rfl) ⟨2352203, by rfl⟩ : syracuseStep 3136271 = 4704407) B4704407
theorem B2090847 : Blo 2089435 2090847 := bstep (se 1 (by rfl) ⟨1568135, by rfl⟩ : syracuseStep 2090847 = 3136271) B3136271
theorem B3136277 : Blo 2089435 3136277 := bbase (se 6 (by rfl) ⟨73506, by rfl⟩ : syracuseStep 3136277 = 147013) (by norm_num)
theorem B2090851 : Blo 2089435 2090851 := bstep (se 1 (by rfl) ⟨1568138, by rfl⟩ : syracuseStep 2090851 = 3136277) B3136277
theorem B9537221 : Blo 2089435 9537221 := bbase (se 4 (by rfl) ⟨894114, by rfl⟩ : syracuseStep 9537221 = 1788229) (by norm_num)
theorem B25432589 : Blo 2089435 25432589 := bstep (se 3 (by rfl) ⟨4768610, by rfl⟩ : syracuseStep 25432589 = 9537221) B9537221
theorem B67820237 : Blo 2089435 67820237 := bstep (se 3 (by rfl) ⟨12716294, by rfl⟩ : syracuseStep 67820237 = 25432589) B25432589
theorem B45213491 : Blo 2089435 45213491 := bstep (se 1 (by rfl) ⟨33910118, by rfl⟩ : syracuseStep 45213491 = 67820237) B67820237
theorem B30142327 : Blo 2089435 30142327 := bstep (se 1 (by rfl) ⟨22606745, by rfl⟩ : syracuseStep 30142327 = 45213491) B45213491
theorem B40189769 : Blo 2089435 40189769 := bstep (se 2 (by rfl) ⟨15071163, by rfl⟩ : syracuseStep 40189769 = 30142327) B30142327
theorem B26793179 : Blo 2089435 26793179 := bstep (se 1 (by rfl) ⟨20094884, by rfl⟩ : syracuseStep 26793179 = 40189769) B40189769
theorem B17862119 : Blo 2089435 17862119 := bstep (se 1 (by rfl) ⟨13396589, by rfl⟩ : syracuseStep 17862119 = 26793179) B26793179
theorem B11908079 : Blo 2089435 11908079 := bstep (se 1 (by rfl) ⟨8931059, by rfl⟩ : syracuseStep 11908079 = 17862119) B17862119
theorem B7938719 : Blo 2089435 7938719 := bstep (se 1 (by rfl) ⟨5954039, by rfl⟩ : syracuseStep 7938719 = 11908079) B11908079
theorem B5292479 : Blo 2089435 5292479 := bstep (se 1 (by rfl) ⟨3969359, by rfl⟩ : syracuseStep 5292479 = 7938719) B7938719
theorem B3528319 : Blo 2089435 3528319 := bstep (se 1 (by rfl) ⟨2646239, by rfl⟩ : syracuseStep 3528319 = 5292479) B5292479
theorem B4704425 : Blo 2089435 4704425 := bstep (se 2 (by rfl) ⟨1764159, by rfl⟩ : syracuseStep 4704425 = 3528319) B3528319
theorem B3136283 : Blo 2089435 3136283 := bstep (se 1 (by rfl) ⟨2352212, by rfl⟩ : syracuseStep 3136283 = 4704425) B4704425
theorem B2090855 : Blo 2089435 2090855 := bstep (se 1 (by rfl) ⟨1568141, by rfl⟩ : syracuseStep 2090855 = 3136283) B3136283
theorem B2352217 : Blo 2089435 2352217 := bbase (se 2 (by rfl) ⟨882081, by rfl⟩ : syracuseStep 2352217 = 1764163) (by norm_num)
theorem B3136289 : Blo 2089435 3136289 := bstep (se 2 (by rfl) ⟨1176108, by rfl⟩ : syracuseStep 3136289 = 2352217) B2352217
theorem B2090859 : Blo 2089435 2090859 := bstep (se 1 (by rfl) ⟨1568144, by rfl⟩ : syracuseStep 2090859 = 3136289) B3136289
theorem B5023741 : Blo 2089435 5023741 := bbase (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) (by norm_num)
theorem B6698321 : Blo 2089435 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B4465547 : Blo 2089435 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B2977031 : Blo 2089435 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B7938749 : Blo 2089435 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B5292499 : Blo 2089435 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B7056665 : Blo 2089435 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B4704443 : Blo 2089435 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B3136295 : Blo 2089435 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B2090863 : Blo 2089435 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B3136301 : Blo 2089435 3136301 := bbase (se 3 (by rfl) ⟨588056, by rfl⟩ : syracuseStep 3136301 = 1176113) (by norm_num)
theorem B2090867 : Blo 2089435 2090867 := bstep (se 1 (by rfl) ⟨1568150, by rfl⟩ : syracuseStep 2090867 = 3136301) B3136301
theorem B4704461 : Blo 2089435 4704461 := bbase (se 3 (by rfl) ⟨882086, by rfl⟩ : syracuseStep 4704461 = 1764173) (by norm_num)
theorem B3136307 : Blo 2089435 3136307 := bstep (se 1 (by rfl) ⟨2352230, by rfl⟩ : syracuseStep 3136307 = 4704461) B4704461
theorem B2090871 : Blo 2089435 2090871 := bstep (se 1 (by rfl) ⟨1568153, by rfl⟩ : syracuseStep 2090871 = 3136307) B3136307
theorem B2646265 : Blo 2089435 2646265 := bbase (se 2 (by rfl) ⟨992349, by rfl⟩ : syracuseStep 2646265 = 1984699) (by norm_num)
theorem B3528353 : Blo 2089435 3528353 := bstep (se 2 (by rfl) ⟨1323132, by rfl⟩ : syracuseStep 3528353 = 2646265) B2646265
theorem B2352235 : Blo 2089435 2352235 := bstep (se 1 (by rfl) ⟨1764176, by rfl⟩ : syracuseStep 2352235 = 3528353) B3528353
theorem B3136313 : Blo 2089435 3136313 := bstep (se 2 (by rfl) ⟨1176117, by rfl⟩ : syracuseStep 3136313 = 2352235) B2352235
theorem B2090875 : Blo 2089435 2090875 := bstep (se 1 (by rfl) ⟨1568156, by rfl⟩ : syracuseStep 2090875 = 3136313) B3136313
theorem B10047557 : Blo 2089435 10047557 := bbase (se 4 (by rfl) ⟨941958, by rfl⟩ : syracuseStep 10047557 = 1883917) (by norm_num)
theorem B6698371 : Blo 2089435 6698371 := bstep (se 1 (by rfl) ⟨5023778, by rfl⟩ : syracuseStep 6698371 = 10047557) B10047557
theorem B8931161 : Blo 2089435 8931161 := bstep (se 2 (by rfl) ⟨3349185, by rfl⟩ : syracuseStep 8931161 = 6698371) B6698371
theorem B23816429 : Blo 2089435 23816429 := bstep (se 3 (by rfl) ⟨4465580, by rfl⟩ : syracuseStep 23816429 = 8931161) B8931161
theorem B15877619 : Blo 2089435 15877619 := bstep (se 1 (by rfl) ⟨11908214, by rfl⟩ : syracuseStep 15877619 = 23816429) B23816429
theorem B10585079 : Blo 2089435 10585079 := bstep (se 1 (by rfl) ⟨7938809, by rfl⟩ : syracuseStep 10585079 = 15877619) B15877619
theorem B7056719 : Blo 2089435 7056719 := bstep (se 1 (by rfl) ⟨5292539, by rfl⟩ : syracuseStep 7056719 = 10585079) B10585079
theorem B4704479 : Blo 2089435 4704479 := bstep (se 1 (by rfl) ⟨3528359, by rfl⟩ : syracuseStep 4704479 = 7056719) B7056719
theorem B3136319 : Blo 2089435 3136319 := bstep (se 1 (by rfl) ⟨2352239, by rfl⟩ : syracuseStep 3136319 = 4704479) B4704479
theorem B2090879 : Blo 2089435 2090879 := bstep (se 1 (by rfl) ⟨1568159, by rfl⟩ : syracuseStep 2090879 = 3136319) B3136319
theorem B3136325 : Blo 2089435 3136325 := bbase (se 4 (by rfl) ⟨294030, by rfl⟩ : syracuseStep 3136325 = 588061) (by norm_num)
theorem B2090883 : Blo 2089435 2090883 := bstep (se 1 (by rfl) ⟨1568162, by rfl⟩ : syracuseStep 2090883 = 3136325) B3136325
theorem B3528373 : Blo 2089435 3528373 := bbase (se 5 (by rfl) ⟨165392, by rfl⟩ : syracuseStep 3528373 = 330785) (by norm_num)
theorem B4704497 : Blo 2089435 4704497 := bstep (se 2 (by rfl) ⟨1764186, by rfl⟩ : syracuseStep 4704497 = 3528373) B3528373
theorem B3136331 : Blo 2089435 3136331 := bstep (se 1 (by rfl) ⟨2352248, by rfl⟩ : syracuseStep 3136331 = 4704497) B4704497
theorem B2090887 : Blo 2089435 2090887 := bstep (se 1 (by rfl) ⟨1568165, by rfl⟩ : syracuseStep 2090887 = 3136331) B3136331
theorem B2352253 : Blo 2089435 2352253 := bbase (se 3 (by rfl) ⟨441047, by rfl⟩ : syracuseStep 2352253 = 882095) (by norm_num)
theorem B3136337 : Blo 2089435 3136337 := bstep (se 2 (by rfl) ⟨1176126, by rfl⟩ : syracuseStep 3136337 = 2352253) B2352253
theorem B2090891 : Blo 2089435 2090891 := bstep (se 1 (by rfl) ⟨1568168, by rfl⟩ : syracuseStep 2090891 = 3136337) B3136337
theorem B7056773 : Blo 2089435 7056773 := bbase (se 4 (by rfl) ⟨661572, by rfl⟩ : syracuseStep 7056773 = 1323145) (by norm_num)
theorem B4704515 : Blo 2089435 4704515 := bstep (se 1 (by rfl) ⟨3528386, by rfl⟩ : syracuseStep 4704515 = 7056773) B7056773
theorem B3136343 : Blo 2089435 3136343 := bstep (se 1 (by rfl) ⟨2352257, by rfl⟩ : syracuseStep 3136343 = 4704515) B4704515
theorem B2090895 : Blo 2089435 2090895 := bstep (se 1 (by rfl) ⟨1568171, by rfl⟩ : syracuseStep 2090895 = 3136343) B3136343
theorem B3136349 : Blo 2089435 3136349 := bbase (se 3 (by rfl) ⟨588065, by rfl⟩ : syracuseStep 3136349 = 1176131) (by norm_num)
theorem B2090899 : Blo 2089435 2090899 := bstep (se 1 (by rfl) ⟨1568174, by rfl⟩ : syracuseStep 2090899 = 3136349) B3136349
theorem B4704533 : Blo 2089435 4704533 := bbase (se 6 (by rfl) ⟨110262, by rfl⟩ : syracuseStep 4704533 = 220525) (by norm_num)
theorem B3136355 : Blo 2089435 3136355 := bstep (se 1 (by rfl) ⟨2352266, by rfl⟩ : syracuseStep 3136355 = 4704533) B4704533
theorem B2090903 : Blo 2089435 2090903 := bstep (se 1 (by rfl) ⟨1568177, by rfl⟩ : syracuseStep 2090903 = 3136355) B3136355
theorem B7938917 : Blo 2089435 7938917 := bbase (se 4 (by rfl) ⟨744273, by rfl⟩ : syracuseStep 7938917 = 1488547) (by norm_num)
theorem B5292611 : Blo 2089435 5292611 := bstep (se 1 (by rfl) ⟨3969458, by rfl⟩ : syracuseStep 5292611 = 7938917) B7938917
theorem B3528407 : Blo 2089435 3528407 := bstep (se 1 (by rfl) ⟨2646305, by rfl⟩ : syracuseStep 3528407 = 5292611) B5292611
theorem B2352271 : Blo 2089435 2352271 := bstep (se 1 (by rfl) ⟨1764203, by rfl⟩ : syracuseStep 2352271 = 3528407) B3528407
theorem B3136361 : Blo 2089435 3136361 := bstep (se 2 (by rfl) ⟨1176135, by rfl⟩ : syracuseStep 3136361 = 2352271) B2352271
theorem B2090907 : Blo 2089435 2090907 := bstep (se 1 (by rfl) ⟨1568180, by rfl⟩ : syracuseStep 2090907 = 3136361) B3136361
theorem B3349237 : Blo 2089435 3349237 := bbase (se 5 (by rfl) ⟨156995, by rfl⟩ : syracuseStep 3349237 = 313991) (by norm_num)
theorem B4465649 : Blo 2089435 4465649 := bstep (se 2 (by rfl) ⟨1674618, by rfl⟩ : syracuseStep 4465649 = 3349237) B3349237
theorem B11908397 : Blo 2089435 11908397 := bstep (se 3 (by rfl) ⟨2232824, by rfl⟩ : syracuseStep 11908397 = 4465649) B4465649
theorem B7938931 : Blo 2089435 7938931 := bstep (se 1 (by rfl) ⟨5954198, by rfl⟩ : syracuseStep 7938931 = 11908397) B11908397
theorem B10585241 : Blo 2089435 10585241 := bstep (se 2 (by rfl) ⟨3969465, by rfl⟩ : syracuseStep 10585241 = 7938931) B7938931
theorem B7056827 : Blo 2089435 7056827 := bstep (se 1 (by rfl) ⟨5292620, by rfl⟩ : syracuseStep 7056827 = 10585241) B10585241
theorem B4704551 : Blo 2089435 4704551 := bstep (se 1 (by rfl) ⟨3528413, by rfl⟩ : syracuseStep 4704551 = 7056827) B7056827
theorem B3136367 : Blo 2089435 3136367 := bstep (se 1 (by rfl) ⟨2352275, by rfl⟩ : syracuseStep 3136367 = 4704551) B4704551
theorem B2090911 : Blo 2089435 2090911 := bstep (se 1 (by rfl) ⟨1568183, by rfl⟩ : syracuseStep 2090911 = 3136367) B3136367
theorem B3136373 : Blo 2089435 3136373 := bbase (se 5 (by rfl) ⟨147017, by rfl⟩ : syracuseStep 3136373 = 294035) (by norm_num)
theorem B2090915 : Blo 2089435 2090915 := bstep (se 1 (by rfl) ⟨1568186, by rfl⟩ : syracuseStep 2090915 = 3136373) B3136373
theorem B6698501 : Blo 2089435 6698501 := bbase (se 4 (by rfl) ⟨627984, by rfl⟩ : syracuseStep 6698501 = 1255969) (by norm_num)
theorem B4465667 : Blo 2089435 4465667 := bstep (se 1 (by rfl) ⟨3349250, by rfl⟩ : syracuseStep 4465667 = 6698501) B6698501
theorem B2977111 : Blo 2089435 2977111 := bstep (se 1 (by rfl) ⟨2232833, by rfl⟩ : syracuseStep 2977111 = 4465667) B4465667
theorem B3969481 : Blo 2089435 3969481 := bstep (se 2 (by rfl) ⟨1488555, by rfl⟩ : syracuseStep 3969481 = 2977111) B2977111
theorem B5292641 : Blo 2089435 5292641 := bstep (se 2 (by rfl) ⟨1984740, by rfl⟩ : syracuseStep 5292641 = 3969481) B3969481
theorem B3528427 : Blo 2089435 3528427 := bstep (se 1 (by rfl) ⟨2646320, by rfl⟩ : syracuseStep 3528427 = 5292641) B5292641
theorem B4704569 : Blo 2089435 4704569 := bstep (se 2 (by rfl) ⟨1764213, by rfl⟩ : syracuseStep 4704569 = 3528427) B3528427
theorem B3136379 : Blo 2089435 3136379 := bstep (se 1 (by rfl) ⟨2352284, by rfl⟩ : syracuseStep 3136379 = 4704569) B4704569
theorem B2090919 : Blo 2089435 2090919 := bstep (se 1 (by rfl) ⟨1568189, by rfl⟩ : syracuseStep 2090919 = 3136379) B3136379
theorem B2352289 : Blo 2089435 2352289 := bbase (se 2 (by rfl) ⟨882108, by rfl⟩ : syracuseStep 2352289 = 1764217) (by norm_num)
theorem B3136385 : Blo 2089435 3136385 := bstep (se 2 (by rfl) ⟨1176144, by rfl⟩ : syracuseStep 3136385 = 2352289) B2352289
theorem B2090923 : Blo 2089435 2090923 := bstep (se 1 (by rfl) ⟨1568192, by rfl⟩ : syracuseStep 2090923 = 3136385) B3136385
theorem B5292661 : Blo 2089435 5292661 := bbase (se 5 (by rfl) ⟨248093, by rfl⟩ : syracuseStep 5292661 = 496187) (by norm_num)
theorem B7056881 : Blo 2089435 7056881 := bstep (se 2 (by rfl) ⟨2646330, by rfl⟩ : syracuseStep 7056881 = 5292661) B5292661
theorem B4704587 : Blo 2089435 4704587 := bstep (se 1 (by rfl) ⟨3528440, by rfl⟩ : syracuseStep 4704587 = 7056881) B7056881
theorem B3136391 : Blo 2089435 3136391 := bstep (se 1 (by rfl) ⟨2352293, by rfl⟩ : syracuseStep 3136391 = 4704587) B4704587
theorem B2090927 : Blo 2089435 2090927 := bstep (se 1 (by rfl) ⟨1568195, by rfl⟩ : syracuseStep 2090927 = 3136391) B3136391
theorem B3136397 : Blo 2089435 3136397 := bbase (se 3 (by rfl) ⟨588074, by rfl⟩ : syracuseStep 3136397 = 1176149) (by norm_num)
theorem B2090931 : Blo 2089435 2090931 := bstep (se 1 (by rfl) ⟨1568198, by rfl⟩ : syracuseStep 2090931 = 3136397) B3136397
theorem B4704605 : Blo 2089435 4704605 := bbase (se 3 (by rfl) ⟨882113, by rfl⟩ : syracuseStep 4704605 = 1764227) (by norm_num)
theorem B3136403 : Blo 2089435 3136403 := bstep (se 1 (by rfl) ⟨2352302, by rfl⟩ : syracuseStep 3136403 = 4704605) B4704605
theorem B2090935 : Blo 2089435 2090935 := bstep (se 1 (by rfl) ⟨1568201, by rfl⟩ : syracuseStep 2090935 = 3136403) B3136403
theorem B3528461 : Blo 2089435 3528461 := bbase (se 3 (by rfl) ⟨661586, by rfl⟩ : syracuseStep 3528461 = 1323173) (by norm_num)
theorem B2352307 : Blo 2089435 2352307 := bstep (se 1 (by rfl) ⟨1764230, by rfl⟩ : syracuseStep 2352307 = 3528461) B3528461
theorem B3136409 : Blo 2089435 3136409 := bstep (se 2 (by rfl) ⟨1176153, by rfl⟩ : syracuseStep 3136409 = 2352307) B2352307
theorem B2090939 : Blo 2089435 2090939 := bstep (se 1 (by rfl) ⟨1568204, by rfl⟩ : syracuseStep 2090939 = 3136409) B3136409
theorem B17862869 : Blo 2089435 17862869 := bbase (se 7 (by rfl) ⟨209330, by rfl⟩ : syracuseStep 17862869 = 418661) (by norm_num)
theorem B11908579 : Blo 2089435 11908579 := bstep (se 1 (by rfl) ⟨8931434, by rfl⟩ : syracuseStep 11908579 = 17862869) B17862869
theorem B15878105 : Blo 2089435 15878105 := bstep (se 2 (by rfl) ⟨5954289, by rfl⟩ : syracuseStep 15878105 = 11908579) B11908579
theorem B10585403 : Blo 2089435 10585403 := bstep (se 1 (by rfl) ⟨7939052, by rfl⟩ : syracuseStep 10585403 = 15878105) B15878105
theorem B7056935 : Blo 2089435 7056935 := bstep (se 1 (by rfl) ⟨5292701, by rfl⟩ : syracuseStep 7056935 = 10585403) B10585403
theorem B4704623 : Blo 2089435 4704623 := bstep (se 1 (by rfl) ⟨3528467, by rfl⟩ : syracuseStep 4704623 = 7056935) B7056935
theorem B3136415 : Blo 2089435 3136415 := bstep (se 1 (by rfl) ⟨2352311, by rfl⟩ : syracuseStep 3136415 = 4704623) B4704623
theorem B2090943 : Blo 2089435 2090943 := bstep (se 1 (by rfl) ⟨1568207, by rfl⟩ : syracuseStep 2090943 = 3136415) B3136415
theorem B3136421 : Blo 2089435 3136421 := bbase (se 4 (by rfl) ⟨294039, by rfl⟩ : syracuseStep 3136421 = 588079) (by norm_num)
theorem B2090947 : Blo 2089435 2090947 := bstep (se 1 (by rfl) ⟨1568210, by rfl⟩ : syracuseStep 2090947 = 3136421) B3136421
theorem B2646361 : Blo 2089435 2646361 := bbase (se 2 (by rfl) ⟨992385, by rfl⟩ : syracuseStep 2646361 = 1984771) (by norm_num)
theorem B3528481 : Blo 2089435 3528481 := bstep (se 2 (by rfl) ⟨1323180, by rfl⟩ : syracuseStep 3528481 = 2646361) B2646361
theorem B4704641 : Blo 2089435 4704641 := bstep (se 2 (by rfl) ⟨1764240, by rfl⟩ : syracuseStep 4704641 = 3528481) B3528481
theorem B3136427 : Blo 2089435 3136427 := bstep (se 1 (by rfl) ⟨2352320, by rfl⟩ : syracuseStep 3136427 = 4704641) B4704641
theorem B2090951 : Blo 2089435 2090951 := bstep (se 1 (by rfl) ⟨1568213, by rfl⟩ : syracuseStep 2090951 = 3136427) B3136427
theorem B2352325 : Blo 2089435 2352325 := bbase (se 4 (by rfl) ⟨220530, by rfl⟩ : syracuseStep 2352325 = 441061) (by norm_num)
theorem B3136433 : Blo 2089435 3136433 := bstep (se 2 (by rfl) ⟨1176162, by rfl⟩ : syracuseStep 3136433 = 2352325) B2352325
theorem B2090955 : Blo 2089435 2090955 := bstep (se 1 (by rfl) ⟨1568216, by rfl⟩ : syracuseStep 2090955 = 3136433) B3136433
theorem B3969557 : Blo 2089435 3969557 := bbase (se 6 (by rfl) ⟨93036, by rfl⟩ : syracuseStep 3969557 = 186073) (by norm_num)
theorem B2646371 : Blo 2089435 2646371 := bstep (se 1 (by rfl) ⟨1984778, by rfl⟩ : syracuseStep 2646371 = 3969557) B3969557
theorem B7056989 : Blo 2089435 7056989 := bstep (se 3 (by rfl) ⟨1323185, by rfl⟩ : syracuseStep 7056989 = 2646371) B2646371
theorem B4704659 : Blo 2089435 4704659 := bstep (se 1 (by rfl) ⟨3528494, by rfl⟩ : syracuseStep 4704659 = 7056989) B7056989
theorem B3136439 : Blo 2089435 3136439 := bstep (se 1 (by rfl) ⟨2352329, by rfl⟩ : syracuseStep 3136439 = 4704659) B4704659
theorem B2090959 : Blo 2089435 2090959 := bstep (se 1 (by rfl) ⟨1568219, by rfl⟩ : syracuseStep 2090959 = 3136439) B3136439
theorem B3136445 : Blo 2089435 3136445 := bbase (se 3 (by rfl) ⟨588083, by rfl⟩ : syracuseStep 3136445 = 1176167) (by norm_num)
theorem B2090963 : Blo 2089435 2090963 := bstep (se 1 (by rfl) ⟨1568222, by rfl⟩ : syracuseStep 2090963 = 3136445) B3136445
theorem B4704677 : Blo 2089435 4704677 := bbase (se 4 (by rfl) ⟨441063, by rfl⟩ : syracuseStep 4704677 = 882127) (by norm_num)
theorem B3136451 : Blo 2089435 3136451 := bstep (se 1 (by rfl) ⟨2352338, by rfl⟩ : syracuseStep 3136451 = 4704677) B4704677
theorem B2090967 : Blo 2089435 2090967 := bstep (se 1 (by rfl) ⟨1568225, by rfl⟩ : syracuseStep 2090967 = 3136451) B3136451
theorem B5292773 : Blo 2089435 5292773 := bbase (se 4 (by rfl) ⟨496197, by rfl⟩ : syracuseStep 5292773 = 992395) (by norm_num)
theorem B3528515 : Blo 2089435 3528515 := bstep (se 1 (by rfl) ⟨2646386, by rfl⟩ : syracuseStep 3528515 = 5292773) B5292773
theorem B2352343 : Blo 2089435 2352343 := bstep (se 1 (by rfl) ⟨1764257, by rfl⟩ : syracuseStep 2352343 = 3528515) B3528515
theorem B3136457 : Blo 2089435 3136457 := bstep (se 2 (by rfl) ⟨1176171, by rfl⟩ : syracuseStep 3136457 = 2352343) B2352343
theorem B2090971 : Blo 2089435 2090971 := bstep (se 1 (by rfl) ⟨1568228, by rfl⟩ : syracuseStep 2090971 = 3136457) B3136457
theorem B2232893 : Blo 2089435 2232893 := bbase (se 3 (by rfl) ⟨418667, by rfl⟩ : syracuseStep 2232893 = 837335) (by norm_num)
theorem B5954381 : Blo 2089435 5954381 := bstep (se 3 (by rfl) ⟨1116446, by rfl⟩ : syracuseStep 5954381 = 2232893) B2232893
theorem B3969587 : Blo 2089435 3969587 := bstep (se 1 (by rfl) ⟨2977190, by rfl⟩ : syracuseStep 3969587 = 5954381) B5954381
theorem B10585565 : Blo 2089435 10585565 := bstep (se 3 (by rfl) ⟨1984793, by rfl⟩ : syracuseStep 10585565 = 3969587) B3969587
theorem B7057043 : Blo 2089435 7057043 := bstep (se 1 (by rfl) ⟨5292782, by rfl⟩ : syracuseStep 7057043 = 10585565) B10585565
theorem B4704695 : Blo 2089435 4704695 := bstep (se 1 (by rfl) ⟨3528521, by rfl⟩ : syracuseStep 4704695 = 7057043) B7057043
theorem B3136463 : Blo 2089435 3136463 := bstep (se 1 (by rfl) ⟨2352347, by rfl⟩ : syracuseStep 3136463 = 4704695) B4704695
theorem B2090975 : Blo 2089435 2090975 := bstep (se 1 (by rfl) ⟨1568231, by rfl⟩ : syracuseStep 2090975 = 3136463) B3136463
theorem B3136469 : Blo 2089435 3136469 := bbase (se 7 (by rfl) ⟨36755, by rfl⟩ : syracuseStep 3136469 = 73511) (by norm_num)
theorem B2090979 : Blo 2089435 2090979 := bstep (se 1 (by rfl) ⟨1568234, by rfl⟩ : syracuseStep 2090979 = 3136469) B3136469
theorem B7939205 : Blo 2089435 7939205 := bbase (se 4 (by rfl) ⟨744300, by rfl⟩ : syracuseStep 7939205 = 1488601) (by norm_num)
theorem B5292803 : Blo 2089435 5292803 := bstep (se 1 (by rfl) ⟨3969602, by rfl⟩ : syracuseStep 5292803 = 7939205) B7939205
theorem B3528535 : Blo 2089435 3528535 := bstep (se 1 (by rfl) ⟨2646401, by rfl⟩ : syracuseStep 3528535 = 5292803) B5292803
theorem B4704713 : Blo 2089435 4704713 := bstep (se 2 (by rfl) ⟨1764267, by rfl⟩ : syracuseStep 4704713 = 3528535) B3528535
theorem B3136475 : Blo 2089435 3136475 := bstep (se 1 (by rfl) ⟨2352356, by rfl⟩ : syracuseStep 3136475 = 4704713) B4704713
theorem B2090983 : Blo 2089435 2090983 := bstep (se 1 (by rfl) ⟨1568237, by rfl⟩ : syracuseStep 2090983 = 3136475) B3136475
theorem B2352361 : Blo 2089435 2352361 := bbase (se 2 (by rfl) ⟨882135, by rfl⟩ : syracuseStep 2352361 = 1764271) (by norm_num)
theorem B3136481 : Blo 2089435 3136481 := bstep (se 2 (by rfl) ⟨1176180, by rfl⟩ : syracuseStep 3136481 = 2352361) B2352361
theorem B2090987 : Blo 2089435 2090987 := bstep (se 1 (by rfl) ⟨1568240, by rfl⟩ : syracuseStep 2090987 = 3136481) B3136481
theorem B11908853 : Blo 2089435 11908853 := bbase (se 5 (by rfl) ⟨558227, by rfl⟩ : syracuseStep 11908853 = 1116455) (by norm_num)
theorem B7939235 : Blo 2089435 7939235 := bstep (se 1 (by rfl) ⟨5954426, by rfl⟩ : syracuseStep 7939235 = 11908853) B11908853
theorem B5292823 : Blo 2089435 5292823 := bstep (se 1 (by rfl) ⟨3969617, by rfl⟩ : syracuseStep 5292823 = 7939235) B7939235
theorem B7057097 : Blo 2089435 7057097 := bstep (se 2 (by rfl) ⟨2646411, by rfl⟩ : syracuseStep 7057097 = 5292823) B5292823
theorem B4704731 : Blo 2089435 4704731 := bstep (se 1 (by rfl) ⟨3528548, by rfl⟩ : syracuseStep 4704731 = 7057097) B7057097
theorem B3136487 : Blo 2089435 3136487 := bstep (se 1 (by rfl) ⟨2352365, by rfl⟩ : syracuseStep 3136487 = 4704731) B4704731
theorem B2090991 : Blo 2089435 2090991 := bstep (se 1 (by rfl) ⟨1568243, by rfl⟩ : syracuseStep 2090991 = 3136487) B3136487
theorem B3136493 : Blo 2089435 3136493 := bbase (se 3 (by rfl) ⟨588092, by rfl⟩ : syracuseStep 3136493 = 1176185) (by norm_num)
theorem B2090995 : Blo 2089435 2090995 := bstep (se 1 (by rfl) ⟨1568246, by rfl⟩ : syracuseStep 2090995 = 3136493) B3136493
theorem B4704749 : Blo 2089435 4704749 := bbase (se 3 (by rfl) ⟨882140, by rfl⟩ : syracuseStep 4704749 = 1764281) (by norm_num)
theorem B3136499 : Blo 2089435 3136499 := bstep (se 1 (by rfl) ⟨2352374, by rfl⟩ : syracuseStep 3136499 = 4704749) B4704749
theorem B2090999 : Blo 2089435 2090999 := bstep (se 1 (by rfl) ⟨1568249, by rfl⟩ : syracuseStep 2090999 = 3136499) B3136499
theorem B7251029 : Blo 2089435 7251029 := bbase (se 8 (by rfl) ⟨42486, by rfl⟩ : syracuseStep 7251029 = 84973) (by norm_num)
theorem B4834019 : Blo 2089435 4834019 := bstep (se 1 (by rfl) ⟨3625514, by rfl⟩ : syracuseStep 4834019 = 7251029) B7251029
theorem B3222679 : Blo 2089435 3222679 := bstep (se 1 (by rfl) ⟨2417009, by rfl⟩ : syracuseStep 3222679 = 4834019) B4834019
theorem B4296905 : Blo 2089435 4296905 := bstep (se 2 (by rfl) ⟨1611339, by rfl⟩ : syracuseStep 4296905 = 3222679) B3222679
theorem B2864603 : Blo 2089435 2864603 := bstep (se 1 (by rfl) ⟨2148452, by rfl⟩ : syracuseStep 2864603 = 4296905) B4296905
theorem B7638941 : Blo 2089435 7638941 := bstep (se 3 (by rfl) ⟨1432301, by rfl⟩ : syracuseStep 7638941 = 2864603) B2864603
theorem B5092627 : Blo 2089435 5092627 := bstep (se 1 (by rfl) ⟨3819470, by rfl⟩ : syracuseStep 5092627 = 7638941) B7638941
theorem B6790169 : Blo 2089435 6790169 := bstep (se 2 (by rfl) ⟨2546313, by rfl⟩ : syracuseStep 6790169 = 5092627) B5092627
theorem B4526779 : Blo 2089435 4526779 := bstep (se 1 (by rfl) ⟨3395084, by rfl⟩ : syracuseStep 4526779 = 6790169) B6790169
theorem B6035705 : Blo 2089435 6035705 := bstep (se 2 (by rfl) ⟨2263389, by rfl⟩ : syracuseStep 6035705 = 4526779) B4526779
theorem B4023803 : Blo 2089435 4023803 := bstep (se 1 (by rfl) ⟨3017852, by rfl⟩ : syracuseStep 4023803 = 6035705) B6035705
theorem B10730141 : Blo 2089435 10730141 := bstep (se 3 (by rfl) ⟨2011901, by rfl⟩ : syracuseStep 10730141 = 4023803) B4023803
theorem B7153427 : Blo 2089435 7153427 := bstep (se 1 (by rfl) ⟨5365070, by rfl⟩ : syracuseStep 7153427 = 10730141) B10730141
theorem B4768951 : Blo 2089435 4768951 := bstep (se 1 (by rfl) ⟨3576713, by rfl⟩ : syracuseStep 4768951 = 7153427) B7153427
theorem B6358601 : Blo 2089435 6358601 := bstep (se 2 (by rfl) ⟨2384475, by rfl⟩ : syracuseStep 6358601 = 4768951) B4768951
theorem B4239067 : Blo 2089435 4239067 := bstep (se 1 (by rfl) ⟨3179300, by rfl⟩ : syracuseStep 4239067 = 6358601) B6358601
theorem B5652089 : Blo 2089435 5652089 := bstep (se 2 (by rfl) ⟨2119533, by rfl⟩ : syracuseStep 5652089 = 4239067) B4239067
theorem B3768059 : Blo 2089435 3768059 := bstep (se 1 (by rfl) ⟨2826044, by rfl⟩ : syracuseStep 3768059 = 5652089) B5652089
theorem B10048157 : Blo 2089435 10048157 := bstep (se 3 (by rfl) ⟨1884029, by rfl⟩ : syracuseStep 10048157 = 3768059) B3768059
theorem B6698771 : Blo 2089435 6698771 := bstep (se 1 (by rfl) ⟨5024078, by rfl⟩ : syracuseStep 6698771 = 10048157) B10048157
theorem B4465847 : Blo 2089435 4465847 := bstep (se 1 (by rfl) ⟨3349385, by rfl⟩ : syracuseStep 4465847 = 6698771) B6698771
theorem B2977231 : Blo 2089435 2977231 := bstep (se 1 (by rfl) ⟨2232923, by rfl⟩ : syracuseStep 2977231 = 4465847) B4465847
theorem B3969641 : Blo 2089435 3969641 := bstep (se 2 (by rfl) ⟨1488615, by rfl⟩ : syracuseStep 3969641 = 2977231) B2977231
theorem B2646427 : Blo 2089435 2646427 := bstep (se 1 (by rfl) ⟨1984820, by rfl⟩ : syracuseStep 2646427 = 3969641) B3969641
theorem B3528569 : Blo 2089435 3528569 := bstep (se 2 (by rfl) ⟨1323213, by rfl⟩ : syracuseStep 3528569 = 2646427) B2646427
theorem B2352379 : Blo 2089435 2352379 := bstep (se 1 (by rfl) ⟨1764284, by rfl⟩ : syracuseStep 2352379 = 3528569) B3528569
theorem B3136505 : Blo 2089435 3136505 := bstep (se 2 (by rfl) ⟨1176189, by rfl⟩ : syracuseStep 3136505 = 2352379) B2352379
theorem B2091003 : Blo 2089435 2091003 := bstep (se 1 (by rfl) ⟨1568252, by rfl⟩ : syracuseStep 2091003 = 3136505) B3136505
theorem B57227477 : Blo 2089435 57227477 := bbase (se 7 (by rfl) ⟨670634, by rfl⟩ : syracuseStep 57227477 = 1341269) (by norm_num)
theorem B152606605 : Blo 2089435 152606605 := bstep (se 3 (by rfl) ⟨28613738, by rfl⟩ : syracuseStep 152606605 = 57227477) B57227477
theorem B203475473 : Blo 2089435 203475473 := bstep (se 2 (by rfl) ⟨76303302, by rfl⟩ : syracuseStep 203475473 = 152606605) B152606605
theorem B135650315 : Blo 2089435 135650315 := bstep (se 1 (by rfl) ⟨101737736, by rfl⟩ : syracuseStep 135650315 = 203475473) B203475473
theorem B90433543 : Blo 2089435 90433543 := bstep (se 1 (by rfl) ⟨67825157, by rfl⟩ : syracuseStep 90433543 = 135650315) B135650315
theorem B120578057 : Blo 2089435 120578057 := bstep (se 2 (by rfl) ⟨45216771, by rfl⟩ : syracuseStep 120578057 = 90433543) B90433543
theorem B80385371 : Blo 2089435 80385371 := bstep (se 1 (by rfl) ⟨60289028, by rfl⟩ : syracuseStep 80385371 = 120578057) B120578057
theorem B53590247 : Blo 2089435 53590247 := bstep (se 1 (by rfl) ⟨40192685, by rfl⟩ : syracuseStep 53590247 = 80385371) B80385371
theorem B35726831 : Blo 2089435 35726831 := bstep (se 1 (by rfl) ⟨26795123, by rfl⟩ : syracuseStep 35726831 = 53590247) B53590247
theorem B23817887 : Blo 2089435 23817887 := bstep (se 1 (by rfl) ⟨17863415, by rfl⟩ : syracuseStep 23817887 = 35726831) B35726831
theorem B15878591 : Blo 2089435 15878591 := bstep (se 1 (by rfl) ⟨11908943, by rfl⟩ : syracuseStep 15878591 = 23817887) B23817887
theorem B10585727 : Blo 2089435 10585727 := bstep (se 1 (by rfl) ⟨7939295, by rfl⟩ : syracuseStep 10585727 = 15878591) B15878591
theorem B7057151 : Blo 2089435 7057151 := bstep (se 1 (by rfl) ⟨5292863, by rfl⟩ : syracuseStep 7057151 = 10585727) B10585727
theorem B4704767 : Blo 2089435 4704767 := bstep (se 1 (by rfl) ⟨3528575, by rfl⟩ : syracuseStep 4704767 = 7057151) B7057151
theorem B3136511 : Blo 2089435 3136511 := bstep (se 1 (by rfl) ⟨2352383, by rfl⟩ : syracuseStep 3136511 = 4704767) B4704767
theorem B2091007 : Blo 2089435 2091007 := bstep (se 1 (by rfl) ⟨1568255, by rfl⟩ : syracuseStep 2091007 = 3136511) B3136511
theorem B3136517 : Blo 2089435 3136517 := bbase (se 4 (by rfl) ⟨294048, by rfl⟩ : syracuseStep 3136517 = 588097) (by norm_num)
theorem B2091011 : Blo 2089435 2091011 := bstep (se 1 (by rfl) ⟨1568258, by rfl⟩ : syracuseStep 2091011 = 3136517) B3136517
theorem B3528589 : Blo 2089435 3528589 := bbase (se 3 (by rfl) ⟨661610, by rfl⟩ : syracuseStep 3528589 = 1323221) (by norm_num)
theorem B4704785 : Blo 2089435 4704785 := bstep (se 2 (by rfl) ⟨1764294, by rfl⟩ : syracuseStep 4704785 = 3528589) B3528589
theorem B3136523 : Blo 2089435 3136523 := bstep (se 1 (by rfl) ⟨2352392, by rfl⟩ : syracuseStep 3136523 = 4704785) B4704785
theorem B2091015 : Blo 2089435 2091015 := bstep (se 1 (by rfl) ⟨1568261, by rfl⟩ : syracuseStep 2091015 = 3136523) B3136523
theorem B2352397 : Blo 2089435 2352397 := bbase (se 3 (by rfl) ⟨441074, by rfl⟩ : syracuseStep 2352397 = 882149) (by norm_num)
theorem B3136529 : Blo 2089435 3136529 := bstep (se 2 (by rfl) ⟨1176198, by rfl⟩ : syracuseStep 3136529 = 2352397) B2352397
theorem B2091019 : Blo 2089435 2091019 := bstep (se 1 (by rfl) ⟨1568264, by rfl⟩ : syracuseStep 2091019 = 3136529) B3136529
theorem B7057205 : Blo 2089435 7057205 := bbase (se 5 (by rfl) ⟨330806, by rfl⟩ : syracuseStep 7057205 = 661613) (by norm_num)
theorem B4704803 : Blo 2089435 4704803 := bstep (se 1 (by rfl) ⟨3528602, by rfl⟩ : syracuseStep 4704803 = 7057205) B7057205
theorem B3136535 : Blo 2089435 3136535 := bstep (se 1 (by rfl) ⟨2352401, by rfl⟩ : syracuseStep 3136535 = 4704803) B4704803
theorem B2091023 : Blo 2089435 2091023 := bstep (se 1 (by rfl) ⟨1568267, by rfl⟩ : syracuseStep 2091023 = 3136535) B3136535
theorem B3136541 : Blo 2089435 3136541 := bbase (se 3 (by rfl) ⟨588101, by rfl⟩ : syracuseStep 3136541 = 1176203) (by norm_num)
theorem B2091027 : Blo 2089435 2091027 := bstep (se 1 (by rfl) ⟨1568270, by rfl⟩ : syracuseStep 2091027 = 3136541) B3136541
theorem B4704821 : Blo 2089435 4704821 := bbase (se 5 (by rfl) ⟨220538, by rfl⟩ : syracuseStep 4704821 = 441077) (by norm_num)
theorem B3136547 : Blo 2089435 3136547 := bstep (se 1 (by rfl) ⟨2352410, by rfl⟩ : syracuseStep 3136547 = 4704821) B4704821
theorem B2091031 : Blo 2089435 2091031 := bstep (se 1 (by rfl) ⟨1568273, by rfl⟩ : syracuseStep 2091031 = 3136547) B3136547
theorem B8931829 : Blo 2089435 8931829 := bbase (se 5 (by rfl) ⟨418679, by rfl⟩ : syracuseStep 8931829 = 837359) (by norm_num)
theorem B11909105 : Blo 2089435 11909105 := bstep (se 2 (by rfl) ⟨4465914, by rfl⟩ : syracuseStep 11909105 = 8931829) B8931829
theorem B7939403 : Blo 2089435 7939403 := bstep (se 1 (by rfl) ⟨5954552, by rfl⟩ : syracuseStep 7939403 = 11909105) B11909105
theorem B5292935 : Blo 2089435 5292935 := bstep (se 1 (by rfl) ⟨3969701, by rfl⟩ : syracuseStep 5292935 = 7939403) B7939403
theorem B3528623 : Blo 2089435 3528623 := bstep (se 1 (by rfl) ⟨2646467, by rfl⟩ : syracuseStep 3528623 = 5292935) B5292935
theorem B2352415 : Blo 2089435 2352415 := bstep (se 1 (by rfl) ⟨1764311, by rfl⟩ : syracuseStep 2352415 = 3528623) B3528623
theorem B3136553 : Blo 2089435 3136553 := bstep (se 2 (by rfl) ⟨1176207, by rfl⟩ : syracuseStep 3136553 = 2352415) B2352415
theorem B2091035 : Blo 2089435 2091035 := bstep (se 1 (by rfl) ⟨1568276, by rfl⟩ : syracuseStep 2091035 = 3136553) B3136553
theorem B8931845 : Blo 2089435 8931845 := bbase (se 4 (by rfl) ⟨837360, by rfl⟩ : syracuseStep 8931845 = 1674721) (by norm_num)
theorem B5954563 : Blo 2089435 5954563 := bstep (se 1 (by rfl) ⟨4465922, by rfl⟩ : syracuseStep 5954563 = 8931845) B8931845
theorem B7939417 : Blo 2089435 7939417 := bstep (se 2 (by rfl) ⟨2977281, by rfl⟩ : syracuseStep 7939417 = 5954563) B5954563
theorem B10585889 : Blo 2089435 10585889 := bstep (se 2 (by rfl) ⟨3969708, by rfl⟩ : syracuseStep 10585889 = 7939417) B7939417
theorem B7057259 : Blo 2089435 7057259 := bstep (se 1 (by rfl) ⟨5292944, by rfl⟩ : syracuseStep 7057259 = 10585889) B10585889
theorem B4704839 : Blo 2089435 4704839 := bstep (se 1 (by rfl) ⟨3528629, by rfl⟩ : syracuseStep 4704839 = 7057259) B7057259
theorem B3136559 : Blo 2089435 3136559 := bstep (se 1 (by rfl) ⟨2352419, by rfl⟩ : syracuseStep 3136559 = 4704839) B4704839
theorem B2091039 : Blo 2089435 2091039 := bstep (se 1 (by rfl) ⟨1568279, by rfl⟩ : syracuseStep 2091039 = 3136559) B3136559
theorem B3136565 : Blo 2089435 3136565 := bbase (se 5 (by rfl) ⟨147026, by rfl⟩ : syracuseStep 3136565 = 294053) (by norm_num)
theorem B2091043 : Blo 2089435 2091043 := bstep (se 1 (by rfl) ⟨1568282, by rfl⟩ : syracuseStep 2091043 = 3136565) B3136565
theorem B5292965 : Blo 2089435 5292965 := bbase (se 4 (by rfl) ⟨496215, by rfl⟩ : syracuseStep 5292965 = 992431) (by norm_num)
theorem B3528643 : Blo 2089435 3528643 := bstep (se 1 (by rfl) ⟨2646482, by rfl⟩ : syracuseStep 3528643 = 5292965) B5292965
theorem B4704857 : Blo 2089435 4704857 := bstep (se 2 (by rfl) ⟨1764321, by rfl⟩ : syracuseStep 4704857 = 3528643) B3528643
theorem B3136571 : Blo 2089435 3136571 := bstep (se 1 (by rfl) ⟨2352428, by rfl⟩ : syracuseStep 3136571 = 4704857) B4704857
theorem B2091047 : Blo 2089435 2091047 := bstep (se 1 (by rfl) ⟨1568285, by rfl⟩ : syracuseStep 2091047 = 3136571) B3136571
theorem B2352433 : Blo 2089435 2352433 := bbase (se 2 (by rfl) ⟨882162, by rfl⟩ : syracuseStep 2352433 = 1764325) (by norm_num)
theorem B3136577 : Blo 2089435 3136577 := bstep (se 2 (by rfl) ⟨1176216, by rfl⟩ : syracuseStep 3136577 = 2352433) B2352433
theorem B2091051 : Blo 2089435 2091051 := bstep (se 1 (by rfl) ⟨1568288, by rfl⟩ : syracuseStep 2091051 = 3136577) B3136577
theorem B4465957 : Blo 2089435 4465957 := bbase (se 4 (by rfl) ⟨418683, by rfl⟩ : syracuseStep 4465957 = 837367) (by norm_num)
theorem B5954609 : Blo 2089435 5954609 := bstep (se 2 (by rfl) ⟨2232978, by rfl⟩ : syracuseStep 5954609 = 4465957) B4465957
theorem B3969739 : Blo 2089435 3969739 := bstep (se 1 (by rfl) ⟨2977304, by rfl⟩ : syracuseStep 3969739 = 5954609) B5954609
theorem B5292985 : Blo 2089435 5292985 := bstep (se 2 (by rfl) ⟨1984869, by rfl⟩ : syracuseStep 5292985 = 3969739) B3969739
theorem B7057313 : Blo 2089435 7057313 := bstep (se 2 (by rfl) ⟨2646492, by rfl⟩ : syracuseStep 7057313 = 5292985) B5292985
theorem B4704875 : Blo 2089435 4704875 := bstep (se 1 (by rfl) ⟨3528656, by rfl⟩ : syracuseStep 4704875 = 7057313) B7057313
theorem B3136583 : Blo 2089435 3136583 := bstep (se 1 (by rfl) ⟨2352437, by rfl⟩ : syracuseStep 3136583 = 4704875) B4704875
theorem B2091055 : Blo 2089435 2091055 := bstep (se 1 (by rfl) ⟨1568291, by rfl⟩ : syracuseStep 2091055 = 3136583) B3136583
theorem B3136589 : Blo 2089435 3136589 := bbase (se 3 (by rfl) ⟨588110, by rfl⟩ : syracuseStep 3136589 = 1176221) (by norm_num)
theorem B2091059 : Blo 2089435 2091059 := bstep (se 1 (by rfl) ⟨1568294, by rfl⟩ : syracuseStep 2091059 = 3136589) B3136589
theorem B4704893 : Blo 2089435 4704893 := bbase (se 3 (by rfl) ⟨882167, by rfl⟩ : syracuseStep 4704893 = 1764335) (by norm_num)
theorem B3136595 : Blo 2089435 3136595 := bstep (se 1 (by rfl) ⟨2352446, by rfl⟩ : syracuseStep 3136595 = 4704893) B4704893
theorem B2091063 : Blo 2089435 2091063 := bstep (se 1 (by rfl) ⟨1568297, by rfl⟩ : syracuseStep 2091063 = 3136595) B3136595
theorem B3528677 : Blo 2089435 3528677 := bbase (se 4 (by rfl) ⟨330813, by rfl⟩ : syracuseStep 3528677 = 661627) (by norm_num)
theorem B2352451 : Blo 2089435 2352451 := bstep (se 1 (by rfl) ⟨1764338, by rfl⟩ : syracuseStep 2352451 = 3528677) B3528677
theorem B3136601 : Blo 2089435 3136601 := bstep (se 2 (by rfl) ⟨1176225, by rfl⟩ : syracuseStep 3136601 = 2352451) B2352451
theorem B2091067 : Blo 2089435 2091067 := bstep (se 1 (by rfl) ⟨1568300, by rfl⟩ : syracuseStep 2091067 = 3136601) B3136601
theorem B10730485 : Blo 2089435 10730485 := bbase (se 5 (by rfl) ⟨502991, by rfl⟩ : syracuseStep 10730485 = 1005983) (by norm_num)
theorem B14307313 : Blo 2089435 14307313 := bstep (se 2 (by rfl) ⟨5365242, by rfl⟩ : syracuseStep 14307313 = 10730485) B10730485
theorem B19076417 : Blo 2089435 19076417 := bstep (se 2 (by rfl) ⟨7153656, by rfl⟩ : syracuseStep 19076417 = 14307313) B14307313
theorem B12717611 : Blo 2089435 12717611 := bstep (se 1 (by rfl) ⟨9538208, by rfl⟩ : syracuseStep 12717611 = 19076417) B19076417
theorem B8478407 : Blo 2089435 8478407 := bstep (se 1 (by rfl) ⟨6358805, by rfl⟩ : syracuseStep 8478407 = 12717611) B12717611
theorem B5652271 : Blo 2089435 5652271 := bstep (se 1 (by rfl) ⟨4239203, by rfl⟩ : syracuseStep 5652271 = 8478407) B8478407
theorem B7536361 : Blo 2089435 7536361 := bstep (se 2 (by rfl) ⟨2826135, by rfl⟩ : syracuseStep 7536361 = 5652271) B5652271
theorem B10048481 : Blo 2089435 10048481 := bstep (se 2 (by rfl) ⟨3768180, by rfl⟩ : syracuseStep 10048481 = 7536361) B7536361
theorem B6698987 : Blo 2089435 6698987 := bstep (se 1 (by rfl) ⟨5024240, by rfl⟩ : syracuseStep 6698987 = 10048481) B10048481
theorem B4465991 : Blo 2089435 4465991 := bstep (se 1 (by rfl) ⟨3349493, by rfl⟩ : syracuseStep 4465991 = 6698987) B6698987
theorem B2977327 : Blo 2089435 2977327 := bstep (se 1 (by rfl) ⟨2232995, by rfl⟩ : syracuseStep 2977327 = 4465991) B4465991
theorem B15879077 : Blo 2089435 15879077 := bstep (se 4 (by rfl) ⟨1488663, by rfl⟩ : syracuseStep 15879077 = 2977327) B2977327
theorem B10586051 : Blo 2089435 10586051 := bstep (se 1 (by rfl) ⟨7939538, by rfl⟩ : syracuseStep 10586051 = 15879077) B15879077
theorem B7057367 : Blo 2089435 7057367 := bstep (se 1 (by rfl) ⟨5293025, by rfl⟩ : syracuseStep 7057367 = 10586051) B10586051
theorem B4704911 : Blo 2089435 4704911 := bstep (se 1 (by rfl) ⟨3528683, by rfl⟩ : syracuseStep 4704911 = 7057367) B7057367
theorem B3136607 : Blo 2089435 3136607 := bstep (se 1 (by rfl) ⟨2352455, by rfl⟩ : syracuseStep 3136607 = 4704911) B4704911
theorem B2091071 : Blo 2089435 2091071 := bstep (se 1 (by rfl) ⟨1568303, by rfl⟩ : syracuseStep 2091071 = 3136607) B3136607
theorem B3136613 : Blo 2089435 3136613 := bbase (se 4 (by rfl) ⟨294057, by rfl⟩ : syracuseStep 3136613 = 588115) (by norm_num)
theorem B2091075 : Blo 2089435 2091075 := bstep (se 1 (by rfl) ⟨1568306, by rfl⟩ : syracuseStep 2091075 = 3136613) B3136613
theorem B5024261 : Blo 2089435 5024261 := bbase (se 4 (by rfl) ⟨471024, by rfl⟩ : syracuseStep 5024261 = 942049) (by norm_num)
theorem B3349507 : Blo 2089435 3349507 := bstep (se 1 (by rfl) ⟨2512130, by rfl⟩ : syracuseStep 3349507 = 5024261) B5024261
theorem B4466009 : Blo 2089435 4466009 := bstep (se 2 (by rfl) ⟨1674753, by rfl⟩ : syracuseStep 4466009 = 3349507) B3349507
theorem B2977339 : Blo 2089435 2977339 := bstep (se 1 (by rfl) ⟨2233004, by rfl⟩ : syracuseStep 2977339 = 4466009) B4466009
theorem B3969785 : Blo 2089435 3969785 := bstep (se 2 (by rfl) ⟨1488669, by rfl⟩ : syracuseStep 3969785 = 2977339) B2977339
theorem B2646523 : Blo 2089435 2646523 := bstep (se 1 (by rfl) ⟨1984892, by rfl⟩ : syracuseStep 2646523 = 3969785) B3969785
theorem B3528697 : Blo 2089435 3528697 := bstep (se 2 (by rfl) ⟨1323261, by rfl⟩ : syracuseStep 3528697 = 2646523) B2646523
theorem B4704929 : Blo 2089435 4704929 := bstep (se 2 (by rfl) ⟨1764348, by rfl⟩ : syracuseStep 4704929 = 3528697) B3528697
theorem B3136619 : Blo 2089435 3136619 := bstep (se 1 (by rfl) ⟨2352464, by rfl⟩ : syracuseStep 3136619 = 4704929) B4704929
theorem B2091079 : Blo 2089435 2091079 := bstep (se 1 (by rfl) ⟨1568309, by rfl⟩ : syracuseStep 2091079 = 3136619) B3136619
theorem B2352469 : Blo 2089435 2352469 := bbase (se 12 (by rfl) ⟨861, by rfl⟩ : syracuseStep 2352469 = 1723) (by norm_num)
theorem B3136625 : Blo 2089435 3136625 := bstep (se 2 (by rfl) ⟨1176234, by rfl⟩ : syracuseStep 3136625 = 2352469) B2352469
theorem B2091083 : Blo 2089435 2091083 := bstep (se 1 (by rfl) ⟨1568312, by rfl⟩ : syracuseStep 2091083 = 3136625) B3136625
theorem B2646533 : Blo 2089435 2646533 := bbase (se 4 (by rfl) ⟨248112, by rfl⟩ : syracuseStep 2646533 = 496225) (by norm_num)
theorem B7057421 : Blo 2089435 7057421 := bstep (se 3 (by rfl) ⟨1323266, by rfl⟩ : syracuseStep 7057421 = 2646533) B2646533
theorem B4704947 : Blo 2089435 4704947 := bstep (se 1 (by rfl) ⟨3528710, by rfl⟩ : syracuseStep 4704947 = 7057421) B7057421
theorem B3136631 : Blo 2089435 3136631 := bstep (se 1 (by rfl) ⟨2352473, by rfl⟩ : syracuseStep 3136631 = 4704947) B4704947
theorem B2091087 : Blo 2089435 2091087 := bstep (se 1 (by rfl) ⟨1568315, by rfl⟩ : syracuseStep 2091087 = 3136631) B3136631
theorem B3136637 : Blo 2089435 3136637 := bbase (se 3 (by rfl) ⟨588119, by rfl⟩ : syracuseStep 3136637 = 1176239) (by norm_num)
theorem B2091091 : Blo 2089435 2091091 := bstep (se 1 (by rfl) ⟨1568318, by rfl⟩ : syracuseStep 2091091 = 3136637) B3136637
theorem B4704965 : Blo 2089435 4704965 := bbase (se 4 (by rfl) ⟨441090, by rfl⟩ : syracuseStep 4704965 = 882181) (by norm_num)
theorem B3136643 : Blo 2089435 3136643 := bstep (se 1 (by rfl) ⟨2352482, by rfl⟩ : syracuseStep 3136643 = 4704965) B4704965
theorem B2091095 : Blo 2089435 2091095 := bstep (se 1 (by rfl) ⟨1568321, by rfl⟩ : syracuseStep 2091095 = 3136643) B3136643
theorem B8047973 : Blo 2089435 8047973 := bbase (se 4 (by rfl) ⟨754497, by rfl⟩ : syracuseStep 8047973 = 1508995) (by norm_num)
theorem B5365315 : Blo 2089435 5365315 := bstep (se 1 (by rfl) ⟨4023986, by rfl⟩ : syracuseStep 5365315 = 8047973) B8047973
theorem B7153753 : Blo 2089435 7153753 := bstep (se 2 (by rfl) ⟨2682657, by rfl⟩ : syracuseStep 7153753 = 5365315) B5365315
theorem B9538337 : Blo 2089435 9538337 := bstep (se 2 (by rfl) ⟨3576876, by rfl⟩ : syracuseStep 9538337 = 7153753) B7153753
theorem B6358891 : Blo 2089435 6358891 := bstep (se 1 (by rfl) ⟨4769168, by rfl⟩ : syracuseStep 6358891 = 9538337) B9538337
theorem B8478521 : Blo 2089435 8478521 := bstep (se 2 (by rfl) ⟨3179445, by rfl⟩ : syracuseStep 8478521 = 6358891) B6358891
theorem B5652347 : Blo 2089435 5652347 := bstep (se 1 (by rfl) ⟨4239260, by rfl⟩ : syracuseStep 5652347 = 8478521) B8478521
theorem B15072925 : Blo 2089435 15072925 := bstep (se 3 (by rfl) ⟨2826173, by rfl⟩ : syracuseStep 15072925 = 5652347) B5652347
theorem B20097233 : Blo 2089435 20097233 := bstep (se 2 (by rfl) ⟨7536462, by rfl⟩ : syracuseStep 20097233 = 15072925) B15072925
theorem B13398155 : Blo 2089435 13398155 := bstep (se 1 (by rfl) ⟨10048616, by rfl⟩ : syracuseStep 13398155 = 20097233) B20097233
theorem B8932103 : Blo 2089435 8932103 := bstep (se 1 (by rfl) ⟨6699077, by rfl⟩ : syracuseStep 8932103 = 13398155) B13398155
theorem B5954735 : Blo 2089435 5954735 := bstep (se 1 (by rfl) ⟨4466051, by rfl⟩ : syracuseStep 5954735 = 8932103) B8932103
theorem B3969823 : Blo 2089435 3969823 := bstep (se 1 (by rfl) ⟨2977367, by rfl⟩ : syracuseStep 3969823 = 5954735) B5954735
theorem B5293097 : Blo 2089435 5293097 := bstep (se 2 (by rfl) ⟨1984911, by rfl⟩ : syracuseStep 5293097 = 3969823) B3969823
theorem B3528731 : Blo 2089435 3528731 := bstep (se 1 (by rfl) ⟨2646548, by rfl⟩ : syracuseStep 3528731 = 5293097) B5293097
theorem B2352487 : Blo 2089435 2352487 := bstep (se 1 (by rfl) ⟨1764365, by rfl⟩ : syracuseStep 2352487 = 3528731) B3528731
theorem B3136649 : Blo 2089435 3136649 := bstep (se 2 (by rfl) ⟨1176243, by rfl⟩ : syracuseStep 3136649 = 2352487) B2352487
theorem B2091099 : Blo 2089435 2091099 := bstep (se 1 (by rfl) ⟨1568324, by rfl⟩ : syracuseStep 2091099 = 3136649) B3136649
theorem B10586213 : Blo 2089435 10586213 := bbase (se 4 (by rfl) ⟨992457, by rfl⟩ : syracuseStep 10586213 = 1984915) (by norm_num)
theorem B7057475 : Blo 2089435 7057475 := bstep (se 1 (by rfl) ⟨5293106, by rfl⟩ : syracuseStep 7057475 = 10586213) B10586213
theorem B4704983 : Blo 2089435 4704983 := bstep (se 1 (by rfl) ⟨3528737, by rfl⟩ : syracuseStep 4704983 = 7057475) B7057475
theorem B3136655 : Blo 2089435 3136655 := bstep (se 1 (by rfl) ⟨2352491, by rfl⟩ : syracuseStep 3136655 = 4704983) B4704983
theorem B2091103 : Blo 2089435 2091103 := bstep (se 1 (by rfl) ⟨1568327, by rfl⟩ : syracuseStep 2091103 = 3136655) B3136655
theorem B3136661 : Blo 2089435 3136661 := bbase (se 6 (by rfl) ⟨73515, by rfl⟩ : syracuseStep 3136661 = 147031) (by norm_num)
theorem B2091107 : Blo 2089435 2091107 := bstep (se 1 (by rfl) ⟨1568330, by rfl⟩ : syracuseStep 2091107 = 3136661) B3136661
theorem B6790517 : Blo 2089435 6790517 := bbase (se 5 (by rfl) ⟨318305, by rfl⟩ : syracuseStep 6790517 = 636611) (by norm_num)
theorem B4527011 : Blo 2089435 4527011 := bstep (se 1 (by rfl) ⟨3395258, by rfl⟩ : syracuseStep 4527011 = 6790517) B6790517
theorem B3018007 : Blo 2089435 3018007 := bstep (se 1 (by rfl) ⟨2263505, by rfl⟩ : syracuseStep 3018007 = 4527011) B4527011
theorem B4024009 : Blo 2089435 4024009 := bstep (se 2 (by rfl) ⟨1509003, by rfl⟩ : syracuseStep 4024009 = 3018007) B3018007
theorem B21461381 : Blo 2089435 21461381 := bstep (se 4 (by rfl) ⟨2012004, by rfl⟩ : syracuseStep 21461381 = 4024009) B4024009
theorem B14307587 : Blo 2089435 14307587 := bstep (se 1 (by rfl) ⟨10730690, by rfl⟩ : syracuseStep 14307587 = 21461381) B21461381
theorem B9538391 : Blo 2089435 9538391 := bstep (se 1 (by rfl) ⟨7153793, by rfl⟩ : syracuseStep 9538391 = 14307587) B14307587
theorem B6358927 : Blo 2089435 6358927 := bstep (se 1 (by rfl) ⟨4769195, by rfl⟩ : syracuseStep 6358927 = 9538391) B9538391
theorem B8478569 : Blo 2089435 8478569 := bstep (se 2 (by rfl) ⟨3179463, by rfl⟩ : syracuseStep 8478569 = 6358927) B6358927
theorem B5652379 : Blo 2089435 5652379 := bstep (se 1 (by rfl) ⟨4239284, by rfl⟩ : syracuseStep 5652379 = 8478569) B8478569
theorem B7536505 : Blo 2089435 7536505 := bstep (se 2 (by rfl) ⟨2826189, by rfl⟩ : syracuseStep 7536505 = 5652379) B5652379
theorem B10048673 : Blo 2089435 10048673 := bstep (se 2 (by rfl) ⟨3768252, by rfl⟩ : syracuseStep 10048673 = 7536505) B7536505
theorem B6699115 : Blo 2089435 6699115 := bstep (se 1 (by rfl) ⟨5024336, by rfl⟩ : syracuseStep 6699115 = 10048673) B10048673
theorem B8932153 : Blo 2089435 8932153 := bstep (se 2 (by rfl) ⟨3349557, by rfl⟩ : syracuseStep 8932153 = 6699115) B6699115
theorem B11909537 : Blo 2089435 11909537 := bstep (se 2 (by rfl) ⟨4466076, by rfl⟩ : syracuseStep 11909537 = 8932153) B8932153
theorem B7939691 : Blo 2089435 7939691 := bstep (se 1 (by rfl) ⟨5954768, by rfl⟩ : syracuseStep 7939691 = 11909537) B11909537
theorem B5293127 : Blo 2089435 5293127 := bstep (se 1 (by rfl) ⟨3969845, by rfl⟩ : syracuseStep 5293127 = 7939691) B7939691
theorem B3528751 : Blo 2089435 3528751 := bstep (se 1 (by rfl) ⟨2646563, by rfl⟩ : syracuseStep 3528751 = 5293127) B5293127
theorem B4705001 : Blo 2089435 4705001 := bstep (se 2 (by rfl) ⟨1764375, by rfl⟩ : syracuseStep 4705001 = 3528751) B3528751
theorem B3136667 : Blo 2089435 3136667 := bstep (se 1 (by rfl) ⟨2352500, by rfl⟩ : syracuseStep 3136667 = 4705001) B4705001
theorem B2091111 : Blo 2089435 2091111 := bstep (se 1 (by rfl) ⟨1568333, by rfl⟩ : syracuseStep 2091111 = 3136667) B3136667
theorem B2352505 : Blo 2089435 2352505 := bbase (se 2 (by rfl) ⟨882189, by rfl⟩ : syracuseStep 2352505 = 1764379) (by norm_num)
theorem B3136673 : Blo 2089435 3136673 := bstep (se 2 (by rfl) ⟨1176252, by rfl⟩ : syracuseStep 3136673 = 2352505) B2352505
theorem B2091115 : Blo 2089435 2091115 := bstep (se 1 (by rfl) ⟨1568336, by rfl⟩ : syracuseStep 2091115 = 3136673) B3136673
theorem B4769213 : Blo 2089435 4769213 := bbase (se 3 (by rfl) ⟨894227, by rfl⟩ : syracuseStep 4769213 = 1788455) (by norm_num)
theorem B12717901 : Blo 2089435 12717901 := bstep (se 3 (by rfl) ⟨2384606, by rfl⟩ : syracuseStep 12717901 = 4769213) B4769213
theorem B16957201 : Blo 2089435 16957201 := bstep (se 2 (by rfl) ⟨6358950, by rfl⟩ : syracuseStep 16957201 = 12717901) B12717901
theorem B22609601 : Blo 2089435 22609601 := bstep (se 2 (by rfl) ⟨8478600, by rfl⟩ : syracuseStep 22609601 = 16957201) B16957201
theorem B15073067 : Blo 2089435 15073067 := bstep (se 1 (by rfl) ⟨11304800, by rfl⟩ : syracuseStep 15073067 = 22609601) B22609601
theorem B10048711 : Blo 2089435 10048711 := bstep (se 1 (by rfl) ⟨7536533, by rfl⟩ : syracuseStep 10048711 = 15073067) B15073067
theorem B13398281 : Blo 2089435 13398281 := bstep (se 2 (by rfl) ⟨5024355, by rfl⟩ : syracuseStep 13398281 = 10048711) B10048711
theorem B8932187 : Blo 2089435 8932187 := bstep (se 1 (by rfl) ⟨6699140, by rfl⟩ : syracuseStep 8932187 = 13398281) B13398281
theorem B5954791 : Blo 2089435 5954791 := bstep (se 1 (by rfl) ⟨4466093, by rfl⟩ : syracuseStep 5954791 = 8932187) B8932187
theorem B7939721 : Blo 2089435 7939721 := bstep (se 2 (by rfl) ⟨2977395, by rfl⟩ : syracuseStep 7939721 = 5954791) B5954791
theorem B5293147 : Blo 2089435 5293147 := bstep (se 1 (by rfl) ⟨3969860, by rfl⟩ : syracuseStep 5293147 = 7939721) B7939721
theorem B7057529 : Blo 2089435 7057529 := bstep (se 2 (by rfl) ⟨2646573, by rfl⟩ : syracuseStep 7057529 = 5293147) B5293147
theorem B4705019 : Blo 2089435 4705019 := bstep (se 1 (by rfl) ⟨3528764, by rfl⟩ : syracuseStep 4705019 = 7057529) B7057529
theorem B3136679 : Blo 2089435 3136679 := bstep (se 1 (by rfl) ⟨2352509, by rfl⟩ : syracuseStep 3136679 = 4705019) B4705019
theorem B2091119 : Blo 2089435 2091119 := bstep (se 1 (by rfl) ⟨1568339, by rfl⟩ : syracuseStep 2091119 = 3136679) B3136679
theorem B3136685 : Blo 2089435 3136685 := bbase (se 3 (by rfl) ⟨588128, by rfl⟩ : syracuseStep 3136685 = 1176257) (by norm_num)
theorem B2091123 : Blo 2089435 2091123 := bstep (se 1 (by rfl) ⟨1568342, by rfl⟩ : syracuseStep 2091123 = 3136685) B3136685
theorem B4705037 : Blo 2089435 4705037 := bbase (se 3 (by rfl) ⟨882194, by rfl⟩ : syracuseStep 4705037 = 1764389) (by norm_num)
theorem B3136691 : Blo 2089435 3136691 := bstep (se 1 (by rfl) ⟨2352518, by rfl⟩ : syracuseStep 3136691 = 4705037) B4705037
theorem B2091127 : Blo 2089435 2091127 := bstep (se 1 (by rfl) ⟨1568345, by rfl⟩ : syracuseStep 2091127 = 3136691) B3136691
theorem B2646589 : Blo 2089435 2646589 := bbase (se 3 (by rfl) ⟨496235, by rfl⟩ : syracuseStep 2646589 = 992471) (by norm_num)
theorem B3528785 : Blo 2089435 3528785 := bstep (se 2 (by rfl) ⟨1323294, by rfl⟩ : syracuseStep 3528785 = 2646589) B2646589
theorem B2352523 : Blo 2089435 2352523 := bstep (se 1 (by rfl) ⟨1764392, by rfl⟩ : syracuseStep 2352523 = 3528785) B3528785
theorem B3136697 : Blo 2089435 3136697 := bstep (se 2 (by rfl) ⟨1176261, by rfl⟩ : syracuseStep 3136697 = 2352523) B2352523
theorem B2091131 : Blo 2089435 2091131 := bstep (se 1 (by rfl) ⟨1568348, by rfl⟩ : syracuseStep 2091131 = 3136697) B3136697
theorem B2546473 : Blo 2089435 2546473 := bbase (se 2 (by rfl) ⟨954927, by rfl⟩ : syracuseStep 2546473 = 1909855) (by norm_num)
theorem B3395297 : Blo 2089435 3395297 := bstep (se 2 (by rfl) ⟨1273236, by rfl⟩ : syracuseStep 3395297 = 2546473) B2546473
theorem B9054125 : Blo 2089435 9054125 := bstep (se 3 (by rfl) ⟨1697648, by rfl⟩ : syracuseStep 9054125 = 3395297) B3395297
theorem B6036083 : Blo 2089435 6036083 := bstep (se 1 (by rfl) ⟨4527062, by rfl⟩ : syracuseStep 6036083 = 9054125) B9054125
theorem B4024055 : Blo 2089435 4024055 := bstep (se 1 (by rfl) ⟨3018041, by rfl⟩ : syracuseStep 4024055 = 6036083) B6036083
theorem B2682703 : Blo 2089435 2682703 := bstep (se 1 (by rfl) ⟨2012027, by rfl⟩ : syracuseStep 2682703 = 4024055) B4024055
theorem B14307749 : Blo 2089435 14307749 := bstep (se 4 (by rfl) ⟨1341351, by rfl⟩ : syracuseStep 14307749 = 2682703) B2682703
theorem B9538499 : Blo 2089435 9538499 := bstep (se 1 (by rfl) ⟨7153874, by rfl⟩ : syracuseStep 9538499 = 14307749) B14307749
theorem B6358999 : Blo 2089435 6358999 := bstep (se 1 (by rfl) ⟨4769249, by rfl⟩ : syracuseStep 6358999 = 9538499) B9538499
theorem B8478665 : Blo 2089435 8478665 := bstep (se 2 (by rfl) ⟨3179499, by rfl⟩ : syracuseStep 8478665 = 6358999) B6358999
theorem B5652443 : Blo 2089435 5652443 := bstep (se 1 (by rfl) ⟨4239332, by rfl⟩ : syracuseStep 5652443 = 8478665) B8478665
theorem B15073181 : Blo 2089435 15073181 := bstep (se 3 (by rfl) ⟨2826221, by rfl⟩ : syracuseStep 15073181 = 5652443) B5652443
theorem B10048787 : Blo 2089435 10048787 := bstep (se 1 (by rfl) ⟨7536590, by rfl⟩ : syracuseStep 10048787 = 15073181) B15073181
theorem B6699191 : Blo 2089435 6699191 := bstep (se 1 (by rfl) ⟨5024393, by rfl⟩ : syracuseStep 6699191 = 10048787) B10048787
theorem B17864509 : Blo 2089435 17864509 := bstep (se 3 (by rfl) ⟨3349595, by rfl⟩ : syracuseStep 17864509 = 6699191) B6699191
theorem B23819345 : Blo 2089435 23819345 := bstep (se 2 (by rfl) ⟨8932254, by rfl⟩ : syracuseStep 23819345 = 17864509) B17864509
theorem B15879563 : Blo 2089435 15879563 := bstep (se 1 (by rfl) ⟨11909672, by rfl⟩ : syracuseStep 15879563 = 23819345) B23819345
theorem B10586375 : Blo 2089435 10586375 := bstep (se 1 (by rfl) ⟨7939781, by rfl⟩ : syracuseStep 10586375 = 15879563) B15879563
theorem B7057583 : Blo 2089435 7057583 := bstep (se 1 (by rfl) ⟨5293187, by rfl⟩ : syracuseStep 7057583 = 10586375) B10586375
theorem B4705055 : Blo 2089435 4705055 := bstep (se 1 (by rfl) ⟨3528791, by rfl⟩ : syracuseStep 4705055 = 7057583) B7057583
theorem B3136703 : Blo 2089435 3136703 := bstep (se 1 (by rfl) ⟨2352527, by rfl⟩ : syracuseStep 3136703 = 4705055) B4705055
theorem B2091135 : Blo 2089435 2091135 := bstep (se 1 (by rfl) ⟨1568351, by rfl⟩ : syracuseStep 2091135 = 3136703) B3136703
theorem B3136709 : Blo 2089435 3136709 := bbase (se 4 (by rfl) ⟨294066, by rfl⟩ : syracuseStep 3136709 = 588133) (by norm_num)
theorem B2091139 : Blo 2089435 2091139 := bstep (se 1 (by rfl) ⟨1568354, by rfl⟩ : syracuseStep 2091139 = 3136709) B3136709
theorem B3528805 : Blo 2089435 3528805 := bbase (se 4 (by rfl) ⟨330825, by rfl⟩ : syracuseStep 3528805 = 661651) (by norm_num)
theorem B4705073 : Blo 2089435 4705073 := bstep (se 2 (by rfl) ⟨1764402, by rfl⟩ : syracuseStep 4705073 = 3528805) B3528805
theorem B3136715 : Blo 2089435 3136715 := bstep (se 1 (by rfl) ⟨2352536, by rfl⟩ : syracuseStep 3136715 = 4705073) B4705073
theorem B2091143 : Blo 2089435 2091143 := bstep (se 1 (by rfl) ⟨1568357, by rfl⟩ : syracuseStep 2091143 = 3136715) B3136715
theorem B2352541 : Blo 2089435 2352541 := bbase (se 3 (by rfl) ⟨441101, by rfl⟩ : syracuseStep 2352541 = 882203) (by norm_num)
theorem B3136721 : Blo 2089435 3136721 := bstep (se 2 (by rfl) ⟨1176270, by rfl⟩ : syracuseStep 3136721 = 2352541) B2352541
theorem B2091147 : Blo 2089435 2091147 := bstep (se 1 (by rfl) ⟨1568360, by rfl⟩ : syracuseStep 2091147 = 3136721) B3136721
theorem B7057637 : Blo 2089435 7057637 := bbase (se 4 (by rfl) ⟨661653, by rfl⟩ : syracuseStep 7057637 = 1323307) (by norm_num)
theorem B4705091 : Blo 2089435 4705091 := bstep (se 1 (by rfl) ⟨3528818, by rfl⟩ : syracuseStep 4705091 = 7057637) B7057637
theorem B3136727 : Blo 2089435 3136727 := bstep (se 1 (by rfl) ⟨2352545, by rfl⟩ : syracuseStep 3136727 = 4705091) B4705091
theorem B2091151 : Blo 2089435 2091151 := bstep (se 1 (by rfl) ⟨1568363, by rfl⟩ : syracuseStep 2091151 = 3136727) B3136727
theorem B3136733 : Blo 2089435 3136733 := bbase (se 3 (by rfl) ⟨588137, by rfl⟩ : syracuseStep 3136733 = 1176275) (by norm_num)
theorem B2091155 : Blo 2089435 2091155 := bstep (se 1 (by rfl) ⟨1568366, by rfl⟩ : syracuseStep 2091155 = 3136733) B3136733
theorem B4705109 : Blo 2089435 4705109 := bbase (se 9 (by rfl) ⟨13784, by rfl⟩ : syracuseStep 4705109 = 27569) (by norm_num)
theorem B3136739 : Blo 2089435 3136739 := bstep (se 1 (by rfl) ⟨2352554, by rfl⟩ : syracuseStep 3136739 = 4705109) B4705109
theorem B2091159 : Blo 2089435 2091159 := bstep (se 1 (by rfl) ⟨1568369, by rfl⟩ : syracuseStep 2091159 = 3136739) B3136739
theorem B5954917 : Blo 2089435 5954917 := bbase (se 4 (by rfl) ⟨558273, by rfl⟩ : syracuseStep 5954917 = 1116547) (by norm_num)
theorem B7939889 : Blo 2089435 7939889 := bstep (se 2 (by rfl) ⟨2977458, by rfl⟩ : syracuseStep 7939889 = 5954917) B5954917
theorem B5293259 : Blo 2089435 5293259 := bstep (se 1 (by rfl) ⟨3969944, by rfl⟩ : syracuseStep 5293259 = 7939889) B7939889
theorem B3528839 : Blo 2089435 3528839 := bstep (se 1 (by rfl) ⟨2646629, by rfl⟩ : syracuseStep 3528839 = 5293259) B5293259
theorem B2352559 : Blo 2089435 2352559 := bstep (se 1 (by rfl) ⟨1764419, by rfl⟩ : syracuseStep 2352559 = 3528839) B3528839
theorem B3136745 : Blo 2089435 3136745 := bstep (se 2 (by rfl) ⟨1176279, by rfl⟩ : syracuseStep 3136745 = 2352559) B2352559
theorem B2091163 : Blo 2089435 2091163 := bstep (se 1 (by rfl) ⟨1568372, by rfl⟩ : syracuseStep 2091163 = 3136745) B3136745
theorem B4239397 : Blo 2089435 4239397 := bbase (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) (by norm_num)
theorem B22610117 : Blo 2089435 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B60293645 : Blo 2089435 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B40195763 : Blo 2089435 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B26797175 : Blo 2089435 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B17864783 : Blo 2089435 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B11909855 : Blo 2089435 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B7939903 : Blo 2089435 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B10586537 : Blo 2089435 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B7057691 : Blo 2089435 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B4705127 : Blo 2089435 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B3136751 : Blo 2089435 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B2091167 : Blo 2089435 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B3136757 : Blo 2089435 3136757 := bbase (se 5 (by rfl) ⟨147035, by rfl⟩ : syracuseStep 3136757 = 294071) (by norm_num)
theorem B2091171 : Blo 2089435 2091171 := bstep (se 1 (by rfl) ⟨1568378, by rfl⟩ : syracuseStep 2091171 = 3136757) B3136757
theorem B10048981 : Blo 2089435 10048981 := bbase (se 7 (by rfl) ⟨117761, by rfl⟩ : syracuseStep 10048981 = 235523) (by norm_num)
theorem B13398641 : Blo 2089435 13398641 := bstep (se 2 (by rfl) ⟨5024490, by rfl⟩ : syracuseStep 13398641 = 10048981) B10048981
theorem B8932427 : Blo 2089435 8932427 := bstep (se 1 (by rfl) ⟨6699320, by rfl⟩ : syracuseStep 8932427 = 13398641) B13398641
theorem B5954951 : Blo 2089435 5954951 := bstep (se 1 (by rfl) ⟨4466213, by rfl⟩ : syracuseStep 5954951 = 8932427) B8932427
theorem B3969967 : Blo 2089435 3969967 := bstep (se 1 (by rfl) ⟨2977475, by rfl⟩ : syracuseStep 3969967 = 5954951) B5954951
theorem B5293289 : Blo 2089435 5293289 := bstep (se 2 (by rfl) ⟨1984983, by rfl⟩ : syracuseStep 5293289 = 3969967) B3969967
theorem B3528859 : Blo 2089435 3528859 := bstep (se 1 (by rfl) ⟨2646644, by rfl⟩ : syracuseStep 3528859 = 5293289) B5293289
theorem B4705145 : Blo 2089435 4705145 := bstep (se 2 (by rfl) ⟨1764429, by rfl⟩ : syracuseStep 4705145 = 3528859) B3528859
theorem B3136763 : Blo 2089435 3136763 := bstep (se 1 (by rfl) ⟨2352572, by rfl⟩ : syracuseStep 3136763 = 4705145) B4705145
theorem B2091175 : Blo 2089435 2091175 := bstep (se 1 (by rfl) ⟨1568381, by rfl⟩ : syracuseStep 2091175 = 3136763) B3136763
theorem B2352577 : Blo 2089435 2352577 := bbase (se 2 (by rfl) ⟨882216, by rfl⟩ : syracuseStep 2352577 = 1764433) (by norm_num)
theorem B3136769 : Blo 2089435 3136769 := bstep (se 2 (by rfl) ⟨1176288, by rfl⟩ : syracuseStep 3136769 = 2352577) B2352577
theorem B2091179 : Blo 2089435 2091179 := bstep (se 1 (by rfl) ⟨1568384, by rfl⟩ : syracuseStep 2091179 = 3136769) B3136769
theorem B5293309 : Blo 2089435 5293309 := bbase (se 3 (by rfl) ⟨992495, by rfl⟩ : syracuseStep 5293309 = 1984991) (by norm_num)
theorem B7057745 : Blo 2089435 7057745 := bstep (se 2 (by rfl) ⟨2646654, by rfl⟩ : syracuseStep 7057745 = 5293309) B5293309
theorem B4705163 : Blo 2089435 4705163 := bstep (se 1 (by rfl) ⟨3528872, by rfl⟩ : syracuseStep 4705163 = 7057745) B7057745
theorem B3136775 : Blo 2089435 3136775 := bstep (se 1 (by rfl) ⟨2352581, by rfl⟩ : syracuseStep 3136775 = 4705163) B4705163
theorem B2091183 : Blo 2089435 2091183 := bstep (se 1 (by rfl) ⟨1568387, by rfl⟩ : syracuseStep 2091183 = 3136775) B3136775
theorem B3136781 : Blo 2089435 3136781 := bbase (se 3 (by rfl) ⟨588146, by rfl⟩ : syracuseStep 3136781 = 1176293) (by norm_num)
theorem B2091187 : Blo 2089435 2091187 := bstep (se 1 (by rfl) ⟨1568390, by rfl⟩ : syracuseStep 2091187 = 3136781) B3136781
theorem B4705181 : Blo 2089435 4705181 := bbase (se 3 (by rfl) ⟨882221, by rfl⟩ : syracuseStep 4705181 = 1764443) (by norm_num)
theorem B3136787 : Blo 2089435 3136787 := bstep (se 1 (by rfl) ⟨2352590, by rfl⟩ : syracuseStep 3136787 = 4705181) B4705181
theorem B2091191 : Blo 2089435 2091191 := bstep (se 1 (by rfl) ⟨1568393, by rfl⟩ : syracuseStep 2091191 = 3136787) B3136787
theorem B3528893 : Blo 2089435 3528893 := bbase (se 3 (by rfl) ⟨661667, by rfl⟩ : syracuseStep 3528893 = 1323335) (by norm_num)
theorem B2352595 : Blo 2089435 2352595 := bstep (se 1 (by rfl) ⟨1764446, by rfl⟩ : syracuseStep 2352595 = 3528893) B3528893
theorem B3136793 : Blo 2089435 3136793 := bstep (se 2 (by rfl) ⟨1176297, by rfl⟩ : syracuseStep 3136793 = 2352595) B2352595
theorem B2091195 : Blo 2089435 2091195 := bstep (se 1 (by rfl) ⟨1568396, by rfl⟩ : syracuseStep 2091195 = 3136793) B3136793
theorem B11910037 : Blo 2089435 11910037 := bbase (se 6 (by rfl) ⟨279141, by rfl⟩ : syracuseStep 11910037 = 558283) (by norm_num)
theorem B15880049 : Blo 2089435 15880049 := bstep (se 2 (by rfl) ⟨5955018, by rfl⟩ : syracuseStep 15880049 = 11910037) B11910037
theorem B10586699 : Blo 2089435 10586699 := bstep (se 1 (by rfl) ⟨7940024, by rfl⟩ : syracuseStep 10586699 = 15880049) B15880049
theorem B7057799 : Blo 2089435 7057799 := bstep (se 1 (by rfl) ⟨5293349, by rfl⟩ : syracuseStep 7057799 = 10586699) B10586699
theorem B4705199 : Blo 2089435 4705199 := bstep (se 1 (by rfl) ⟨3528899, by rfl⟩ : syracuseStep 4705199 = 7057799) B7057799
theorem B3136799 : Blo 2089435 3136799 := bstep (se 1 (by rfl) ⟨2352599, by rfl⟩ : syracuseStep 3136799 = 4705199) B4705199
theorem B2091199 : Blo 2089435 2091199 := bstep (se 1 (by rfl) ⟨1568399, by rfl⟩ : syracuseStep 2091199 = 3136799) B3136799
theorem B3136805 : Blo 2089435 3136805 := bbase (se 4 (by rfl) ⟨294075, by rfl⟩ : syracuseStep 3136805 = 588151) (by norm_num)
theorem B2091203 : Blo 2089435 2091203 := bstep (se 1 (by rfl) ⟨1568402, by rfl⟩ : syracuseStep 2091203 = 3136805) B3136805
theorem B2646685 : Blo 2089435 2646685 := bbase (se 3 (by rfl) ⟨496253, by rfl⟩ : syracuseStep 2646685 = 992507) (by norm_num)
theorem B3528913 : Blo 2089435 3528913 := bstep (se 2 (by rfl) ⟨1323342, by rfl⟩ : syracuseStep 3528913 = 2646685) B2646685
theorem B4705217 : Blo 2089435 4705217 := bstep (se 2 (by rfl) ⟨1764456, by rfl⟩ : syracuseStep 4705217 = 3528913) B3528913
theorem B3136811 : Blo 2089435 3136811 := bstep (se 1 (by rfl) ⟨2352608, by rfl⟩ : syracuseStep 3136811 = 4705217) B4705217
theorem B2091207 : Blo 2089435 2091207 := bstep (se 1 (by rfl) ⟨1568405, by rfl⟩ : syracuseStep 2091207 = 3136811) B3136811
theorem B2352613 : Blo 2089435 2352613 := bbase (se 4 (by rfl) ⟨220557, by rfl⟩ : syracuseStep 2352613 = 441115) (by norm_num)
theorem B3136817 : Blo 2089435 3136817 := bstep (se 2 (by rfl) ⟨1176306, by rfl⟩ : syracuseStep 3136817 = 2352613) B2352613
theorem B2091211 : Blo 2089435 2091211 := bstep (se 1 (by rfl) ⟨1568408, by rfl⟩ : syracuseStep 2091211 = 3136817) B3136817
theorem B5652661 : Blo 2089435 5652661 := bbase (se 5 (by rfl) ⟨264968, by rfl⟩ : syracuseStep 5652661 = 529937) (by norm_num)
theorem B7536881 : Blo 2089435 7536881 := bstep (se 2 (by rfl) ⟨2826330, by rfl⟩ : syracuseStep 7536881 = 5652661) B5652661
theorem B5024587 : Blo 2089435 5024587 := bstep (se 1 (by rfl) ⟨3768440, by rfl⟩ : syracuseStep 5024587 = 7536881) B7536881
theorem B6699449 : Blo 2089435 6699449 := bstep (se 2 (by rfl) ⟨2512293, by rfl⟩ : syracuseStep 6699449 = 5024587) B5024587
theorem B4466299 : Blo 2089435 4466299 := bstep (se 1 (by rfl) ⟨3349724, by rfl⟩ : syracuseStep 4466299 = 6699449) B6699449
theorem B5955065 : Blo 2089435 5955065 := bstep (se 2 (by rfl) ⟨2233149, by rfl⟩ : syracuseStep 5955065 = 4466299) B4466299
theorem B3970043 : Blo 2089435 3970043 := bstep (se 1 (by rfl) ⟨2977532, by rfl⟩ : syracuseStep 3970043 = 5955065) B5955065
theorem B2646695 : Blo 2089435 2646695 := bstep (se 1 (by rfl) ⟨1985021, by rfl⟩ : syracuseStep 2646695 = 3970043) B3970043
theorem B7057853 : Blo 2089435 7057853 := bstep (se 3 (by rfl) ⟨1323347, by rfl⟩ : syracuseStep 7057853 = 2646695) B2646695
theorem B4705235 : Blo 2089435 4705235 := bstep (se 1 (by rfl) ⟨3528926, by rfl⟩ : syracuseStep 4705235 = 7057853) B7057853
theorem B3136823 : Blo 2089435 3136823 := bstep (se 1 (by rfl) ⟨2352617, by rfl⟩ : syracuseStep 3136823 = 4705235) B4705235
theorem B2091215 : Blo 2089435 2091215 := bstep (se 1 (by rfl) ⟨1568411, by rfl⟩ : syracuseStep 2091215 = 3136823) B3136823
theorem B3136829 : Blo 2089435 3136829 := bbase (se 3 (by rfl) ⟨588155, by rfl⟩ : syracuseStep 3136829 = 1176311) (by norm_num)
theorem B2091219 : Blo 2089435 2091219 := bstep (se 1 (by rfl) ⟨1568414, by rfl⟩ : syracuseStep 2091219 = 3136829) B3136829
theorem B4705253 : Blo 2089435 4705253 := bbase (se 4 (by rfl) ⟨441117, by rfl⟩ : syracuseStep 4705253 = 882235) (by norm_num)
theorem B3136835 : Blo 2089435 3136835 := bstep (se 1 (by rfl) ⟨2352626, by rfl⟩ : syracuseStep 3136835 = 4705253) B4705253
theorem B2091223 : Blo 2089435 2091223 := bstep (se 1 (by rfl) ⟨1568417, by rfl⟩ : syracuseStep 2091223 = 3136835) B3136835
theorem B5293421 : Blo 2089435 5293421 := bbase (se 3 (by rfl) ⟨992516, by rfl⟩ : syracuseStep 5293421 = 1985033) (by norm_num)
theorem B3528947 : Blo 2089435 3528947 := bstep (se 1 (by rfl) ⟨2646710, by rfl⟩ : syracuseStep 3528947 = 5293421) B5293421
theorem B2352631 : Blo 2089435 2352631 := bstep (se 1 (by rfl) ⟨1764473, by rfl⟩ : syracuseStep 2352631 = 3528947) B3528947
theorem B3136841 : Blo 2089435 3136841 := bstep (se 2 (by rfl) ⟨1176315, by rfl⟩ : syracuseStep 3136841 = 2352631) B2352631
theorem B2091227 : Blo 2089435 2091227 := bstep (se 1 (by rfl) ⟨1568420, by rfl⟩ : syracuseStep 2091227 = 3136841) B3136841
theorem B4466333 : Blo 2089435 4466333 := bbase (se 3 (by rfl) ⟨837437, by rfl⟩ : syracuseStep 4466333 = 1674875) (by norm_num)
theorem B2977555 : Blo 2089435 2977555 := bstep (se 1 (by rfl) ⟨2233166, by rfl⟩ : syracuseStep 2977555 = 4466333) B4466333
theorem B3970073 : Blo 2089435 3970073 := bstep (se 2 (by rfl) ⟨1488777, by rfl⟩ : syracuseStep 3970073 = 2977555) B2977555
theorem B10586861 : Blo 2089435 10586861 := bstep (se 3 (by rfl) ⟨1985036, by rfl⟩ : syracuseStep 10586861 = 3970073) B3970073
theorem B7057907 : Blo 2089435 7057907 := bstep (se 1 (by rfl) ⟨5293430, by rfl⟩ : syracuseStep 7057907 = 10586861) B10586861
theorem B4705271 : Blo 2089435 4705271 := bstep (se 1 (by rfl) ⟨3528953, by rfl⟩ : syracuseStep 4705271 = 7057907) B7057907
theorem B3136847 : Blo 2089435 3136847 := bstep (se 1 (by rfl) ⟨2352635, by rfl⟩ : syracuseStep 3136847 = 4705271) B4705271
theorem B2091231 : Blo 2089435 2091231 := bstep (se 1 (by rfl) ⟨1568423, by rfl⟩ : syracuseStep 2091231 = 3136847) B3136847
theorem B3136853 : Blo 2089435 3136853 := bbase (se 11 (by rfl) ⟨2297, by rfl⟩ : syracuseStep 3136853 = 4595) (by norm_num)
theorem B2091235 : Blo 2089435 2091235 := bstep (se 1 (by rfl) ⟨1568426, by rfl⟩ : syracuseStep 2091235 = 3136853) B3136853
theorem B5024645 : Blo 2089435 5024645 := bbase (se 4 (by rfl) ⟨471060, by rfl⟩ : syracuseStep 5024645 = 942121) (by norm_num)
theorem B3349763 : Blo 2089435 3349763 := bstep (se 1 (by rfl) ⟨2512322, by rfl⟩ : syracuseStep 3349763 = 5024645) B5024645
theorem B2233175 : Blo 2089435 2233175 := bstep (se 1 (by rfl) ⟨1674881, by rfl⟩ : syracuseStep 2233175 = 3349763) B3349763
theorem B5955133 : Blo 2089435 5955133 := bstep (se 3 (by rfl) ⟨1116587, by rfl⟩ : syracuseStep 5955133 = 2233175) B2233175
theorem B7940177 : Blo 2089435 7940177 := bstep (se 2 (by rfl) ⟨2977566, by rfl⟩ : syracuseStep 7940177 = 5955133) B5955133
theorem B5293451 : Blo 2089435 5293451 := bstep (se 1 (by rfl) ⟨3970088, by rfl⟩ : syracuseStep 5293451 = 7940177) B7940177
theorem B3528967 : Blo 2089435 3528967 := bstep (se 1 (by rfl) ⟨2646725, by rfl⟩ : syracuseStep 3528967 = 5293451) B5293451
theorem B4705289 : Blo 2089435 4705289 := bstep (se 2 (by rfl) ⟨1764483, by rfl⟩ : syracuseStep 4705289 = 3528967) B3528967
theorem B3136859 : Blo 2089435 3136859 := bstep (se 1 (by rfl) ⟨2352644, by rfl⟩ : syracuseStep 3136859 = 4705289) B4705289
theorem B2091239 : Blo 2089435 2091239 := bstep (se 1 (by rfl) ⟨1568429, by rfl⟩ : syracuseStep 2091239 = 3136859) B3136859
theorem B2352649 : Blo 2089435 2352649 := bbase (se 2 (by rfl) ⟨882243, by rfl⟩ : syracuseStep 2352649 = 1764487) (by norm_num)
theorem B3136865 : Blo 2089435 3136865 := bstep (se 2 (by rfl) ⟨1176324, by rfl⟩ : syracuseStep 3136865 = 2352649) B2352649
theorem B2091243 : Blo 2089435 2091243 := bstep (se 1 (by rfl) ⟨1568432, by rfl⟩ : syracuseStep 2091243 = 3136865) B3136865
theorem B2148701 : Blo 2089435 2148701 := bbase (se 3 (by rfl) ⟨402881, by rfl⟩ : syracuseStep 2148701 = 805763) (by norm_num)
theorem B5729869 : Blo 2089435 5729869 := bstep (se 3 (by rfl) ⟨1074350, by rfl⟩ : syracuseStep 5729869 = 2148701) B2148701
theorem B30559301 : Blo 2089435 30559301 := bstep (se 4 (by rfl) ⟨2864934, by rfl⟩ : syracuseStep 30559301 = 5729869) B5729869
theorem B20372867 : Blo 2089435 20372867 := bstep (se 1 (by rfl) ⟨15279650, by rfl⟩ : syracuseStep 20372867 = 30559301) B30559301
theorem B13581911 : Blo 2089435 13581911 := bstep (se 1 (by rfl) ⟨10186433, by rfl⟩ : syracuseStep 13581911 = 20372867) B20372867
theorem B9054607 : Blo 2089435 9054607 := bstep (se 1 (by rfl) ⟨6790955, by rfl⟩ : syracuseStep 9054607 = 13581911) B13581911
theorem B12072809 : Blo 2089435 12072809 := bstep (se 2 (by rfl) ⟨4527303, by rfl⟩ : syracuseStep 12072809 = 9054607) B9054607
theorem B8048539 : Blo 2089435 8048539 := bstep (se 1 (by rfl) ⟨6036404, by rfl⟩ : syracuseStep 8048539 = 12072809) B12072809
theorem B10731385 : Blo 2089435 10731385 := bstep (se 2 (by rfl) ⟨4024269, by rfl⟩ : syracuseStep 10731385 = 8048539) B8048539
theorem B57234053 : Blo 2089435 57234053 := bstep (se 4 (by rfl) ⟨5365692, by rfl⟩ : syracuseStep 57234053 = 10731385) B10731385
theorem B38156035 : Blo 2089435 38156035 := bstep (se 1 (by rfl) ⟨28617026, by rfl⟩ : syracuseStep 38156035 = 57234053) B57234053
theorem B50874713 : Blo 2089435 50874713 := bstep (se 2 (by rfl) ⟨19078017, by rfl⟩ : syracuseStep 50874713 = 38156035) B38156035
theorem B33916475 : Blo 2089435 33916475 := bstep (se 1 (by rfl) ⟨25437356, by rfl⟩ : syracuseStep 33916475 = 50874713) B50874713
theorem B22610983 : Blo 2089435 22610983 := bstep (se 1 (by rfl) ⟨16958237, by rfl⟩ : syracuseStep 22610983 = 33916475) B33916475
theorem B30147977 : Blo 2089435 30147977 := bstep (se 2 (by rfl) ⟨11305491, by rfl⟩ : syracuseStep 30147977 = 22610983) B22610983
theorem B20098651 : Blo 2089435 20098651 := bstep (se 1 (by rfl) ⟨15073988, by rfl⟩ : syracuseStep 20098651 = 30147977) B30147977
theorem B26798201 : Blo 2089435 26798201 := bstep (se 2 (by rfl) ⟨10049325, by rfl⟩ : syracuseStep 26798201 = 20098651) B20098651
theorem B17865467 : Blo 2089435 17865467 := bstep (se 1 (by rfl) ⟨13399100, by rfl⟩ : syracuseStep 17865467 = 26798201) B26798201
theorem B11910311 : Blo 2089435 11910311 := bstep (se 1 (by rfl) ⟨8932733, by rfl⟩ : syracuseStep 11910311 = 17865467) B17865467
theorem B7940207 : Blo 2089435 7940207 := bstep (se 1 (by rfl) ⟨5955155, by rfl⟩ : syracuseStep 7940207 = 11910311) B11910311
theorem B5293471 : Blo 2089435 5293471 := bstep (se 1 (by rfl) ⟨3970103, by rfl⟩ : syracuseStep 5293471 = 7940207) B7940207
theorem B7057961 : Blo 2089435 7057961 := bstep (se 2 (by rfl) ⟨2646735, by rfl⟩ : syracuseStep 7057961 = 5293471) B5293471
theorem B4705307 : Blo 2089435 4705307 := bstep (se 1 (by rfl) ⟨3528980, by rfl⟩ : syracuseStep 4705307 = 7057961) B7057961
theorem B3136871 : Blo 2089435 3136871 := bstep (se 1 (by rfl) ⟨2352653, by rfl⟩ : syracuseStep 3136871 = 4705307) B4705307
theorem B2091247 : Blo 2089435 2091247 := bstep (se 1 (by rfl) ⟨1568435, by rfl⟩ : syracuseStep 2091247 = 3136871) B3136871
theorem B3136877 : Blo 2089435 3136877 := bbase (se 3 (by rfl) ⟨588164, by rfl⟩ : syracuseStep 3136877 = 1176329) (by norm_num)
theorem B2091251 : Blo 2089435 2091251 := bstep (se 1 (by rfl) ⟨1568438, by rfl⟩ : syracuseStep 2091251 = 3136877) B3136877
theorem B4705325 : Blo 2089435 4705325 := bbase (se 3 (by rfl) ⟨882248, by rfl⟩ : syracuseStep 4705325 = 1764497) (by norm_num)
theorem B3136883 : Blo 2089435 3136883 := bstep (se 1 (by rfl) ⟨2352662, by rfl⟩ : syracuseStep 3136883 = 4705325) B4705325
theorem B2091255 : Blo 2089435 2091255 := bstep (se 1 (by rfl) ⟨1568441, by rfl⟩ : syracuseStep 2091255 = 3136883) B3136883
theorem B5024693 : Blo 2089435 5024693 := bbase (se 5 (by rfl) ⟨235532, by rfl⟩ : syracuseStep 5024693 = 471065) (by norm_num)
theorem B13399181 : Blo 2089435 13399181 := bstep (se 3 (by rfl) ⟨2512346, by rfl⟩ : syracuseStep 13399181 = 5024693) B5024693
theorem B8932787 : Blo 2089435 8932787 := bstep (se 1 (by rfl) ⟨6699590, by rfl⟩ : syracuseStep 8932787 = 13399181) B13399181
theorem B5955191 : Blo 2089435 5955191 := bstep (se 1 (by rfl) ⟨4466393, by rfl⟩ : syracuseStep 5955191 = 8932787) B8932787
theorem B3970127 : Blo 2089435 3970127 := bstep (se 1 (by rfl) ⟨2977595, by rfl⟩ : syracuseStep 3970127 = 5955191) B5955191
theorem B2646751 : Blo 2089435 2646751 := bstep (se 1 (by rfl) ⟨1985063, by rfl⟩ : syracuseStep 2646751 = 3970127) B3970127
theorem B3529001 : Blo 2089435 3529001 := bstep (se 2 (by rfl) ⟨1323375, by rfl⟩ : syracuseStep 3529001 = 2646751) B2646751
theorem B2352667 : Blo 2089435 2352667 := bstep (se 1 (by rfl) ⟨1764500, by rfl⟩ : syracuseStep 2352667 = 3529001) B3529001
theorem B3136889 : Blo 2089435 3136889 := bstep (se 2 (by rfl) ⟨1176333, by rfl⟩ : syracuseStep 3136889 = 2352667) B2352667
theorem B2091259 : Blo 2089435 2091259 := bstep (se 1 (by rfl) ⟨1568444, by rfl⟩ : syracuseStep 2091259 = 3136889) B3136889
theorem B5024701 : Blo 2089435 5024701 := bbase (se 3 (by rfl) ⟨942131, by rfl⟩ : syracuseStep 5024701 = 1884263) (by norm_num)
theorem B6699601 : Blo 2089435 6699601 := bstep (se 2 (by rfl) ⟨2512350, by rfl⟩ : syracuseStep 6699601 = 5024701) B5024701
theorem B35731205 : Blo 2089435 35731205 := bstep (se 4 (by rfl) ⟨3349800, by rfl⟩ : syracuseStep 35731205 = 6699601) B6699601
theorem B23820803 : Blo 2089435 23820803 := bstep (se 1 (by rfl) ⟨17865602, by rfl⟩ : syracuseStep 23820803 = 35731205) B35731205
theorem B15880535 : Blo 2089435 15880535 := bstep (se 1 (by rfl) ⟨11910401, by rfl⟩ : syracuseStep 15880535 = 23820803) B23820803
theorem B10587023 : Blo 2089435 10587023 := bstep (se 1 (by rfl) ⟨7940267, by rfl⟩ : syracuseStep 10587023 = 15880535) B15880535
theorem B7058015 : Blo 2089435 7058015 := bstep (se 1 (by rfl) ⟨5293511, by rfl⟩ : syracuseStep 7058015 = 10587023) B10587023
theorem B4705343 : Blo 2089435 4705343 := bstep (se 1 (by rfl) ⟨3529007, by rfl⟩ : syracuseStep 4705343 = 7058015) B7058015
theorem B3136895 : Blo 2089435 3136895 := bstep (se 1 (by rfl) ⟨2352671, by rfl⟩ : syracuseStep 3136895 = 4705343) B4705343
theorem B2091263 : Blo 2089435 2091263 := bstep (se 1 (by rfl) ⟨1568447, by rfl⟩ : syracuseStep 2091263 = 3136895) B3136895
theorem B3136901 : Blo 2089435 3136901 := bbase (se 4 (by rfl) ⟨294084, by rfl⟩ : syracuseStep 3136901 = 588169) (by norm_num)
theorem B2091267 : Blo 2089435 2091267 := bstep (se 1 (by rfl) ⟨1568450, by rfl⟩ : syracuseStep 2091267 = 3136901) B3136901
theorem B3529021 : Blo 2089435 3529021 := bbase (se 3 (by rfl) ⟨661691, by rfl⟩ : syracuseStep 3529021 = 1323383) (by norm_num)
theorem B4705361 : Blo 2089435 4705361 := bstep (se 2 (by rfl) ⟨1764510, by rfl⟩ : syracuseStep 4705361 = 3529021) B3529021
theorem B3136907 : Blo 2089435 3136907 := bstep (se 1 (by rfl) ⟨2352680, by rfl⟩ : syracuseStep 3136907 = 4705361) B4705361
theorem B2091271 : Blo 2089435 2091271 := bstep (se 1 (by rfl) ⟨1568453, by rfl⟩ : syracuseStep 2091271 = 3136907) B3136907
theorem B2352685 : Blo 2089435 2352685 := bbase (se 3 (by rfl) ⟨441128, by rfl⟩ : syracuseStep 2352685 = 882257) (by norm_num)
theorem B3136913 : Blo 2089435 3136913 := bstep (se 2 (by rfl) ⟨1176342, by rfl⟩ : syracuseStep 3136913 = 2352685) B2352685
theorem B2091275 : Blo 2089435 2091275 := bstep (se 1 (by rfl) ⟨1568456, by rfl⟩ : syracuseStep 2091275 = 3136913) B3136913
theorem B7058069 : Blo 2089435 7058069 := bbase (se 6 (by rfl) ⟨165423, by rfl⟩ : syracuseStep 7058069 = 330847) (by norm_num)
theorem B4705379 : Blo 2089435 4705379 := bstep (se 1 (by rfl) ⟨3529034, by rfl⟩ : syracuseStep 4705379 = 7058069) B7058069
theorem B3136919 : Blo 2089435 3136919 := bstep (se 1 (by rfl) ⟨2352689, by rfl⟩ : syracuseStep 3136919 = 4705379) B4705379
theorem B2091279 : Blo 2089435 2091279 := bstep (se 1 (by rfl) ⟨1568459, by rfl⟩ : syracuseStep 2091279 = 3136919) B3136919
theorem B3136925 : Blo 2089435 3136925 := bbase (se 3 (by rfl) ⟨588173, by rfl⟩ : syracuseStep 3136925 = 1176347) (by norm_num)
theorem B2091283 : Blo 2089435 2091283 := bstep (se 1 (by rfl) ⟨1568462, by rfl⟩ : syracuseStep 2091283 = 3136925) B3136925
theorem B4705397 : Blo 2089435 4705397 := bbase (se 5 (by rfl) ⟨220565, by rfl⟩ : syracuseStep 4705397 = 441131) (by norm_num)
theorem B3136931 : Blo 2089435 3136931 := bstep (se 1 (by rfl) ⟨2352698, by rfl⟩ : syracuseStep 3136931 = 4705397) B4705397
theorem B2091287 : Blo 2089435 2091287 := bstep (se 1 (by rfl) ⟨1568465, by rfl⟩ : syracuseStep 2091287 = 3136931) B3136931
theorem B17865845 : Blo 2089435 17865845 := bbase (se 5 (by rfl) ⟨837461, by rfl⟩ : syracuseStep 17865845 = 1674923) (by norm_num)
theorem B11910563 : Blo 2089435 11910563 := bstep (se 1 (by rfl) ⟨8932922, by rfl⟩ : syracuseStep 11910563 = 17865845) B17865845
theorem B7940375 : Blo 2089435 7940375 := bstep (se 1 (by rfl) ⟨5955281, by rfl⟩ : syracuseStep 7940375 = 11910563) B11910563
theorem B5293583 : Blo 2089435 5293583 := bstep (se 1 (by rfl) ⟨3970187, by rfl⟩ : syracuseStep 5293583 = 7940375) B7940375
theorem B3529055 : Blo 2089435 3529055 := bstep (se 1 (by rfl) ⟨2646791, by rfl⟩ : syracuseStep 3529055 = 5293583) B5293583
theorem B2352703 : Blo 2089435 2352703 := bstep (se 1 (by rfl) ⟨1764527, by rfl⟩ : syracuseStep 2352703 = 3529055) B3529055
theorem B3136937 : Blo 2089435 3136937 := bstep (se 2 (by rfl) ⟨1176351, by rfl⟩ : syracuseStep 3136937 = 2352703) B2352703
theorem B2091291 : Blo 2089435 2091291 := bstep (se 1 (by rfl) ⟨1568468, by rfl⟩ : syracuseStep 2091291 = 3136937) B3136937
theorem B7940389 : Blo 2089435 7940389 := bbase (se 4 (by rfl) ⟨744411, by rfl⟩ : syracuseStep 7940389 = 1488823) (by norm_num)
theorem B10587185 : Blo 2089435 10587185 := bstep (se 2 (by rfl) ⟨3970194, by rfl⟩ : syracuseStep 10587185 = 7940389) B7940389
theorem B7058123 : Blo 2089435 7058123 := bstep (se 1 (by rfl) ⟨5293592, by rfl⟩ : syracuseStep 7058123 = 10587185) B10587185
theorem B4705415 : Blo 2089435 4705415 := bstep (se 1 (by rfl) ⟨3529061, by rfl⟩ : syracuseStep 4705415 = 7058123) B7058123
theorem B3136943 : Blo 2089435 3136943 := bstep (se 1 (by rfl) ⟨2352707, by rfl⟩ : syracuseStep 3136943 = 4705415) B4705415
theorem B2091295 : Blo 2089435 2091295 := bstep (se 1 (by rfl) ⟨1568471, by rfl⟩ : syracuseStep 2091295 = 3136943) B3136943
theorem B3136949 : Blo 2089435 3136949 := bbase (se 5 (by rfl) ⟨147044, by rfl⟩ : syracuseStep 3136949 = 294089) (by norm_num)
theorem B2091299 : Blo 2089435 2091299 := bstep (se 1 (by rfl) ⟨1568474, by rfl⟩ : syracuseStep 2091299 = 3136949) B3136949
theorem B5293613 : Blo 2089435 5293613 := bbase (se 3 (by rfl) ⟨992552, by rfl⟩ : syracuseStep 5293613 = 1985105) (by norm_num)
theorem B3529075 : Blo 2089435 3529075 := bstep (se 1 (by rfl) ⟨2646806, by rfl⟩ : syracuseStep 3529075 = 5293613) B5293613
theorem B4705433 : Blo 2089435 4705433 := bstep (se 2 (by rfl) ⟨1764537, by rfl⟩ : syracuseStep 4705433 = 3529075) B3529075
theorem B3136955 : Blo 2089435 3136955 := bstep (se 1 (by rfl) ⟨2352716, by rfl⟩ : syracuseStep 3136955 = 4705433) B4705433
theorem B2091303 : Blo 2089435 2091303 := bstep (se 1 (by rfl) ⟨1568477, by rfl⟩ : syracuseStep 2091303 = 3136955) B3136955
theorem B2352721 : Blo 2089435 2352721 := bbase (se 2 (by rfl) ⟨882270, by rfl⟩ : syracuseStep 2352721 = 1764541) (by norm_num)
theorem B3136961 : Blo 2089435 3136961 := bstep (se 2 (by rfl) ⟨1176360, by rfl⟩ : syracuseStep 3136961 = 2352721) B2352721
theorem B2091307 : Blo 2089435 2091307 := bstep (se 1 (by rfl) ⟨1568480, by rfl⟩ : syracuseStep 2091307 = 3136961) B3136961
theorem B2977669 : Blo 2089435 2977669 := bbase (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) (by norm_num)
theorem B3970225 : Blo 2089435 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B5293633 : Blo 2089435 5293633 := bstep (se 2 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 5293633 = 3970225) B3970225
theorem B7058177 : Blo 2089435 7058177 := bstep (se 2 (by rfl) ⟨2646816, by rfl⟩ : syracuseStep 7058177 = 5293633) B5293633
theorem B4705451 : Blo 2089435 4705451 := bstep (se 1 (by rfl) ⟨3529088, by rfl⟩ : syracuseStep 4705451 = 7058177) B7058177
theorem B3136967 : Blo 2089435 3136967 := bstep (se 1 (by rfl) ⟨2352725, by rfl⟩ : syracuseStep 3136967 = 4705451) B4705451
theorem B2091311 : Blo 2089435 2091311 := bstep (se 1 (by rfl) ⟨1568483, by rfl⟩ : syracuseStep 2091311 = 3136967) B3136967
theorem B3136973 : Blo 2089435 3136973 := bbase (se 3 (by rfl) ⟨588182, by rfl⟩ : syracuseStep 3136973 = 1176365) (by norm_num)
theorem B2091315 : Blo 2089435 2091315 := bstep (se 1 (by rfl) ⟨1568486, by rfl⟩ : syracuseStep 2091315 = 3136973) B3136973
theorem B4705469 : Blo 2089435 4705469 := bbase (se 3 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 4705469 = 1764551) (by norm_num)
theorem B3136979 : Blo 2089435 3136979 := bstep (se 1 (by rfl) ⟨2352734, by rfl⟩ : syracuseStep 3136979 = 4705469) B4705469
theorem B2091319 : Blo 2089435 2091319 := bstep (se 1 (by rfl) ⟨1568489, by rfl⟩ : syracuseStep 2091319 = 3136979) B3136979
theorem B3529109 : Blo 2089435 3529109 := bbase (se 6 (by rfl) ⟨82713, by rfl⟩ : syracuseStep 3529109 = 165427) (by norm_num)
theorem B2352739 : Blo 2089435 2352739 := bstep (se 1 (by rfl) ⟨1764554, by rfl⟩ : syracuseStep 2352739 = 3529109) B3529109
theorem B3136985 : Blo 2089435 3136985 := bstep (se 2 (by rfl) ⟨1176369, by rfl⟩ : syracuseStep 3136985 = 2352739) B2352739
theorem B2091323 : Blo 2089435 2091323 := bstep (se 1 (by rfl) ⟨1568492, by rfl⟩ : syracuseStep 2091323 = 3136985) B3136985
theorem B2119861 : Blo 2089435 2119861 := bbase (se 5 (by rfl) ⟨99368, by rfl⟩ : syracuseStep 2119861 = 198737) (by norm_num)
theorem B11305925 : Blo 2089435 11305925 := bstep (se 4 (by rfl) ⟨1059930, by rfl⟩ : syracuseStep 11305925 = 2119861) B2119861
theorem B7537283 : Blo 2089435 7537283 := bstep (se 1 (by rfl) ⟨5652962, by rfl⟩ : syracuseStep 7537283 = 11305925) B11305925
theorem B5024855 : Blo 2089435 5024855 := bstep (se 1 (by rfl) ⟨3768641, by rfl⟩ : syracuseStep 5024855 = 7537283) B7537283
theorem B13399613 : Blo 2089435 13399613 := bstep (se 3 (by rfl) ⟨2512427, by rfl⟩ : syracuseStep 13399613 = 5024855) B5024855
theorem B8933075 : Blo 2089435 8933075 := bstep (se 1 (by rfl) ⟨6699806, by rfl⟩ : syracuseStep 8933075 = 13399613) B13399613
theorem B5955383 : Blo 2089435 5955383 := bstep (se 1 (by rfl) ⟨4466537, by rfl⟩ : syracuseStep 5955383 = 8933075) B8933075
theorem B15881021 : Blo 2089435 15881021 := bstep (se 3 (by rfl) ⟨2977691, by rfl⟩ : syracuseStep 15881021 = 5955383) B5955383
theorem B10587347 : Blo 2089435 10587347 := bstep (se 1 (by rfl) ⟨7940510, by rfl⟩ : syracuseStep 10587347 = 15881021) B15881021
theorem B7058231 : Blo 2089435 7058231 := bstep (se 1 (by rfl) ⟨5293673, by rfl⟩ : syracuseStep 7058231 = 10587347) B10587347
theorem B4705487 : Blo 2089435 4705487 := bstep (se 1 (by rfl) ⟨3529115, by rfl⟩ : syracuseStep 4705487 = 7058231) B7058231
theorem B3136991 : Blo 2089435 3136991 := bstep (se 1 (by rfl) ⟨2352743, by rfl⟩ : syracuseStep 3136991 = 4705487) B4705487
theorem B2091327 : Blo 2089435 2091327 := bstep (se 1 (by rfl) ⟨1568495, by rfl⟩ : syracuseStep 2091327 = 3136991) B3136991
theorem B3136997 : Blo 2089435 3136997 := bbase (se 4 (by rfl) ⟨294093, by rfl⟩ : syracuseStep 3136997 = 588187) (by norm_num)
theorem B2091331 : Blo 2089435 2091331 := bstep (se 1 (by rfl) ⟨1568498, by rfl⟩ : syracuseStep 2091331 = 3136997) B3136997
theorem B8595173 : Blo 2089435 8595173 := bbase (se 4 (by rfl) ⟨805797, by rfl⟩ : syracuseStep 8595173 = 1611595) (by norm_num)
theorem B5730115 : Blo 2089435 5730115 := bstep (se 1 (by rfl) ⟨4297586, by rfl⟩ : syracuseStep 5730115 = 8595173) B8595173
theorem B7640153 : Blo 2089435 7640153 := bstep (se 2 (by rfl) ⟨2865057, by rfl⟩ : syracuseStep 7640153 = 5730115) B5730115
theorem B5093435 : Blo 2089435 5093435 := bstep (se 1 (by rfl) ⟨3820076, by rfl⟩ : syracuseStep 5093435 = 7640153) B7640153
theorem B3395623 : Blo 2089435 3395623 := bstep (se 1 (by rfl) ⟨2546717, by rfl⟩ : syracuseStep 3395623 = 5093435) B5093435
theorem B4527497 : Blo 2089435 4527497 := bstep (se 2 (by rfl) ⟨1697811, by rfl⟩ : syracuseStep 4527497 = 3395623) B3395623
theorem B3018331 : Blo 2089435 3018331 := bstep (se 1 (by rfl) ⟨2263748, by rfl⟩ : syracuseStep 3018331 = 4527497) B4527497
theorem B4024441 : Blo 2089435 4024441 := bstep (se 2 (by rfl) ⟨1509165, by rfl⟩ : syracuseStep 4024441 = 3018331) B3018331
theorem B5365921 : Blo 2089435 5365921 := bstep (se 2 (by rfl) ⟨2012220, by rfl⟩ : syracuseStep 5365921 = 4024441) B4024441
theorem B7154561 : Blo 2089435 7154561 := bstep (se 2 (by rfl) ⟨2682960, by rfl⟩ : syracuseStep 7154561 = 5365921) B5365921
theorem B4769707 : Blo 2089435 4769707 := bstep (se 1 (by rfl) ⟨3577280, by rfl⟩ : syracuseStep 4769707 = 7154561) B7154561
theorem B6359609 : Blo 2089435 6359609 := bstep (se 2 (by rfl) ⟨2384853, by rfl⟩ : syracuseStep 6359609 = 4769707) B4769707
theorem B4239739 : Blo 2089435 4239739 := bstep (se 1 (by rfl) ⟨3179804, by rfl⟩ : syracuseStep 4239739 = 6359609) B6359609
theorem B5652985 : Blo 2089435 5652985 := bstep (se 2 (by rfl) ⟨2119869, by rfl⟩ : syracuseStep 5652985 = 4239739) B4239739
theorem B7537313 : Blo 2089435 7537313 := bstep (se 2 (by rfl) ⟨2826492, by rfl⟩ : syracuseStep 7537313 = 5652985) B5652985
theorem B20099501 : Blo 2089435 20099501 := bstep (se 3 (by rfl) ⟨3768656, by rfl⟩ : syracuseStep 20099501 = 7537313) B7537313
theorem B13399667 : Blo 2089435 13399667 := bstep (se 1 (by rfl) ⟨10049750, by rfl⟩ : syracuseStep 13399667 = 20099501) B20099501
theorem B8933111 : Blo 2089435 8933111 := bstep (se 1 (by rfl) ⟨6699833, by rfl⟩ : syracuseStep 8933111 = 13399667) B13399667
theorem B5955407 : Blo 2089435 5955407 := bstep (se 1 (by rfl) ⟨4466555, by rfl⟩ : syracuseStep 5955407 = 8933111) B8933111
theorem B3970271 : Blo 2089435 3970271 := bstep (se 1 (by rfl) ⟨2977703, by rfl⟩ : syracuseStep 3970271 = 5955407) B5955407
theorem B2646847 : Blo 2089435 2646847 := bstep (se 1 (by rfl) ⟨1985135, by rfl⟩ : syracuseStep 2646847 = 3970271) B3970271
theorem B3529129 : Blo 2089435 3529129 := bstep (se 2 (by rfl) ⟨1323423, by rfl⟩ : syracuseStep 3529129 = 2646847) B2646847
theorem B4705505 : Blo 2089435 4705505 := bstep (se 2 (by rfl) ⟨1764564, by rfl⟩ : syracuseStep 4705505 = 3529129) B3529129
theorem B3137003 : Blo 2089435 3137003 := bstep (se 1 (by rfl) ⟨2352752, by rfl⟩ : syracuseStep 3137003 = 4705505) B4705505
theorem B2091335 : Blo 2089435 2091335 := bstep (se 1 (by rfl) ⟨1568501, by rfl⟩ : syracuseStep 2091335 = 3137003) B3137003
theorem B2352757 : Blo 2089435 2352757 := bbase (se 5 (by rfl) ⟨110285, by rfl⟩ : syracuseStep 2352757 = 220571) (by norm_num)
theorem B3137009 : Blo 2089435 3137009 := bstep (se 2 (by rfl) ⟨1176378, by rfl⟩ : syracuseStep 3137009 = 2352757) B2352757
theorem B2091339 : Blo 2089435 2091339 := bstep (se 1 (by rfl) ⟨1568504, by rfl⟩ : syracuseStep 2091339 = 3137009) B3137009
theorem B2646857 : Blo 2089435 2646857 := bbase (se 2 (by rfl) ⟨992571, by rfl⟩ : syracuseStep 2646857 = 1985143) (by norm_num)
theorem B7058285 : Blo 2089435 7058285 := bstep (se 3 (by rfl) ⟨1323428, by rfl⟩ : syracuseStep 7058285 = 2646857) B2646857
theorem B4705523 : Blo 2089435 4705523 := bstep (se 1 (by rfl) ⟨3529142, by rfl⟩ : syracuseStep 4705523 = 7058285) B7058285
theorem B3137015 : Blo 2089435 3137015 := bstep (se 1 (by rfl) ⟨2352761, by rfl⟩ : syracuseStep 3137015 = 4705523) B4705523
theorem B2091343 : Blo 2089435 2091343 := bstep (se 1 (by rfl) ⟨1568507, by rfl⟩ : syracuseStep 2091343 = 3137015) B3137015
theorem B3137021 : Blo 2089435 3137021 := bbase (se 3 (by rfl) ⟨588191, by rfl⟩ : syracuseStep 3137021 = 1176383) (by norm_num)
theorem B2091347 : Blo 2089435 2091347 := bstep (se 1 (by rfl) ⟨1568510, by rfl⟩ : syracuseStep 2091347 = 3137021) B3137021
theorem B4705541 : Blo 2089435 4705541 := bbase (se 4 (by rfl) ⟨441144, by rfl⟩ : syracuseStep 4705541 = 882289) (by norm_num)
theorem B3137027 : Blo 2089435 3137027 := bstep (se 1 (by rfl) ⟨2352770, by rfl⟩ : syracuseStep 3137027 = 4705541) B4705541
theorem B2091351 : Blo 2089435 2091351 := bstep (se 1 (by rfl) ⟨1568513, by rfl⟩ : syracuseStep 2091351 = 3137027) B3137027
theorem B3970309 : Blo 2089435 3970309 := bbase (se 4 (by rfl) ⟨372216, by rfl⟩ : syracuseStep 3970309 = 744433) (by norm_num)
theorem B5293745 : Blo 2089435 5293745 := bstep (se 2 (by rfl) ⟨1985154, by rfl⟩ : syracuseStep 5293745 = 3970309) B3970309
theorem B3529163 : Blo 2089435 3529163 := bstep (se 1 (by rfl) ⟨2646872, by rfl⟩ : syracuseStep 3529163 = 5293745) B5293745
theorem B2352775 : Blo 2089435 2352775 := bstep (se 1 (by rfl) ⟨1764581, by rfl⟩ : syracuseStep 2352775 = 3529163) B3529163
theorem B3137033 : Blo 2089435 3137033 := bstep (se 2 (by rfl) ⟨1176387, by rfl⟩ : syracuseStep 3137033 = 2352775) B2352775
theorem B2091355 : Blo 2089435 2091355 := bstep (se 1 (by rfl) ⟨1568516, by rfl⟩ : syracuseStep 2091355 = 3137033) B3137033
theorem B10587509 : Blo 2089435 10587509 := bbase (se 5 (by rfl) ⟨496289, by rfl⟩ : syracuseStep 10587509 = 992579) (by norm_num)
theorem B7058339 : Blo 2089435 7058339 := bstep (se 1 (by rfl) ⟨5293754, by rfl⟩ : syracuseStep 7058339 = 10587509) B10587509
theorem B4705559 : Blo 2089435 4705559 := bstep (se 1 (by rfl) ⟨3529169, by rfl⟩ : syracuseStep 4705559 = 7058339) B7058339
theorem B3137039 : Blo 2089435 3137039 := bstep (se 1 (by rfl) ⟨2352779, by rfl⟩ : syracuseStep 3137039 = 4705559) B4705559
theorem B2091359 : Blo 2089435 2091359 := bstep (se 1 (by rfl) ⟨1568519, by rfl⟩ : syracuseStep 2091359 = 3137039) B3137039
theorem B3137045 : Blo 2089435 3137045 := bbase (se 6 (by rfl) ⟨73524, by rfl⟩ : syracuseStep 3137045 = 147049) (by norm_num)
theorem B2091363 : Blo 2089435 2091363 := bstep (se 1 (by rfl) ⟨1568522, by rfl⟩ : syracuseStep 2091363 = 3137045) B3137045
theorem B38158229 : Blo 2089435 38158229 := bbase (se 6 (by rfl) ⟨894333, by rfl⟩ : syracuseStep 38158229 = 1788667) (by norm_num)
theorem B25438819 : Blo 2089435 25438819 := bstep (se 1 (by rfl) ⟨19079114, by rfl⟩ : syracuseStep 25438819 = 38158229) B38158229
theorem B33918425 : Blo 2089435 33918425 := bstep (se 2 (by rfl) ⟨12719409, by rfl⟩ : syracuseStep 33918425 = 25438819) B25438819
theorem B22612283 : Blo 2089435 22612283 := bstep (se 1 (by rfl) ⟨16959212, by rfl⟩ : syracuseStep 22612283 = 33918425) B33918425
theorem B15074855 : Blo 2089435 15074855 := bstep (se 1 (by rfl) ⟨11306141, by rfl⟩ : syracuseStep 15074855 = 22612283) B22612283
theorem B10049903 : Blo 2089435 10049903 := bstep (se 1 (by rfl) ⟨7537427, by rfl⟩ : syracuseStep 10049903 = 15074855) B15074855
theorem B6699935 : Blo 2089435 6699935 := bstep (se 1 (by rfl) ⟨5024951, by rfl⟩ : syracuseStep 6699935 = 10049903) B10049903
theorem B17866493 : Blo 2089435 17866493 := bstep (se 3 (by rfl) ⟨3349967, by rfl⟩ : syracuseStep 17866493 = 6699935) B6699935
theorem B11910995 : Blo 2089435 11910995 := bstep (se 1 (by rfl) ⟨8933246, by rfl⟩ : syracuseStep 11910995 = 17866493) B17866493
theorem B7940663 : Blo 2089435 7940663 := bstep (se 1 (by rfl) ⟨5955497, by rfl⟩ : syracuseStep 7940663 = 11910995) B11910995
theorem B5293775 : Blo 2089435 5293775 := bstep (se 1 (by rfl) ⟨3970331, by rfl⟩ : syracuseStep 5293775 = 7940663) B7940663
theorem B3529183 : Blo 2089435 3529183 := bstep (se 1 (by rfl) ⟨2646887, by rfl⟩ : syracuseStep 3529183 = 5293775) B5293775
theorem B4705577 : Blo 2089435 4705577 := bstep (se 2 (by rfl) ⟨1764591, by rfl⟩ : syracuseStep 4705577 = 3529183) B3529183
theorem B3137051 : Blo 2089435 3137051 := bstep (se 1 (by rfl) ⟨2352788, by rfl⟩ : syracuseStep 3137051 = 4705577) B4705577
theorem B2091367 : Blo 2089435 2091367 := bstep (se 1 (by rfl) ⟨1568525, by rfl⟩ : syracuseStep 2091367 = 3137051) B3137051
theorem B2352793 : Blo 2089435 2352793 := bbase (se 2 (by rfl) ⟨882297, by rfl⟩ : syracuseStep 2352793 = 1764595) (by norm_num)
theorem B3137057 : Blo 2089435 3137057 := bstep (se 2 (by rfl) ⟨1176396, by rfl⟩ : syracuseStep 3137057 = 2352793) B2352793
theorem B2091371 : Blo 2089435 2091371 := bstep (se 1 (by rfl) ⟨1568528, by rfl⟩ : syracuseStep 2091371 = 3137057) B3137057
theorem B7940693 : Blo 2089435 7940693 := bbase (se 8 (by rfl) ⟨46527, by rfl⟩ : syracuseStep 7940693 = 93055) (by norm_num)
theorem B5293795 : Blo 2089435 5293795 := bstep (se 1 (by rfl) ⟨3970346, by rfl⟩ : syracuseStep 5293795 = 7940693) B7940693
theorem B7058393 : Blo 2089435 7058393 := bstep (se 2 (by rfl) ⟨2646897, by rfl⟩ : syracuseStep 7058393 = 5293795) B5293795
theorem B4705595 : Blo 2089435 4705595 := bstep (se 1 (by rfl) ⟨3529196, by rfl⟩ : syracuseStep 4705595 = 7058393) B7058393
theorem B3137063 : Blo 2089435 3137063 := bstep (se 1 (by rfl) ⟨2352797, by rfl⟩ : syracuseStep 3137063 = 4705595) B4705595
theorem B2091375 : Blo 2089435 2091375 := bstep (se 1 (by rfl) ⟨1568531, by rfl⟩ : syracuseStep 2091375 = 3137063) B3137063
theorem B3137069 : Blo 2089435 3137069 := bbase (se 3 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 3137069 = 1176401) (by norm_num)
theorem B2091379 : Blo 2089435 2091379 := bstep (se 1 (by rfl) ⟨1568534, by rfl⟩ : syracuseStep 2091379 = 3137069) B3137069
theorem B4705613 : Blo 2089435 4705613 := bbase (se 3 (by rfl) ⟨882302, by rfl⟩ : syracuseStep 4705613 = 1764605) (by norm_num)
theorem B3137075 : Blo 2089435 3137075 := bstep (se 1 (by rfl) ⟨2352806, by rfl⟩ : syracuseStep 3137075 = 4705613) B4705613
theorem B2091383 : Blo 2089435 2091383 := bstep (se 1 (by rfl) ⟨1568537, by rfl⟩ : syracuseStep 2091383 = 3137075) B3137075
theorem B2646913 : Blo 2089435 2646913 := bbase (se 2 (by rfl) ⟨992592, by rfl⟩ : syracuseStep 2646913 = 1985185) (by norm_num)
theorem B3529217 : Blo 2089435 3529217 := bstep (se 2 (by rfl) ⟨1323456, by rfl⟩ : syracuseStep 3529217 = 2646913) B2646913
theorem B2352811 : Blo 2089435 2352811 := bstep (se 1 (by rfl) ⟨1764608, by rfl⟩ : syracuseStep 2352811 = 3529217) B3529217
theorem B3137081 : Blo 2089435 3137081 := bstep (se 2 (by rfl) ⟨1176405, by rfl⟩ : syracuseStep 3137081 = 2352811) B2352811
theorem B2091387 : Blo 2089435 2091387 := bstep (se 1 (by rfl) ⟨1568540, by rfl⟩ : syracuseStep 2091387 = 3137081) B3137081
theorem B2233337 : Blo 2089435 2233337 := bbase (se 2 (by rfl) ⟨837501, by rfl⟩ : syracuseStep 2233337 = 1675003) (by norm_num)
theorem B23822261 : Blo 2089435 23822261 := bstep (se 5 (by rfl) ⟨1116668, by rfl⟩ : syracuseStep 23822261 = 2233337) B2233337
theorem B15881507 : Blo 2089435 15881507 := bstep (se 1 (by rfl) ⟨11911130, by rfl⟩ : syracuseStep 15881507 = 23822261) B23822261
theorem B10587671 : Blo 2089435 10587671 := bstep (se 1 (by rfl) ⟨7940753, by rfl⟩ : syracuseStep 10587671 = 15881507) B15881507
theorem B7058447 : Blo 2089435 7058447 := bstep (se 1 (by rfl) ⟨5293835, by rfl⟩ : syracuseStep 7058447 = 10587671) B10587671
theorem B4705631 : Blo 2089435 4705631 := bstep (se 1 (by rfl) ⟨3529223, by rfl⟩ : syracuseStep 4705631 = 7058447) B7058447
theorem B3137087 : Blo 2089435 3137087 := bstep (se 1 (by rfl) ⟨2352815, by rfl⟩ : syracuseStep 3137087 = 4705631) B4705631
theorem B2091391 : Blo 2089435 2091391 := bstep (se 1 (by rfl) ⟨1568543, by rfl⟩ : syracuseStep 2091391 = 3137087) B3137087
theorem B3137093 : Blo 2089435 3137093 := bbase (se 4 (by rfl) ⟨294102, by rfl⟩ : syracuseStep 3137093 = 588205) (by norm_num)
theorem B2091395 : Blo 2089435 2091395 := bstep (se 1 (by rfl) ⟨1568546, by rfl⟩ : syracuseStep 2091395 = 3137093) B3137093
theorem B3529237 : Blo 2089435 3529237 := bbase (se 6 (by rfl) ⟨82716, by rfl⟩ : syracuseStep 3529237 = 165433) (by norm_num)
theorem B4705649 : Blo 2089435 4705649 := bstep (se 2 (by rfl) ⟨1764618, by rfl⟩ : syracuseStep 4705649 = 3529237) B3529237
theorem B3137099 : Blo 2089435 3137099 := bstep (se 1 (by rfl) ⟨2352824, by rfl⟩ : syracuseStep 3137099 = 4705649) B4705649
theorem B2091399 : Blo 2089435 2091399 := bstep (se 1 (by rfl) ⟨1568549, by rfl⟩ : syracuseStep 2091399 = 3137099) B3137099
theorem B2352829 : Blo 2089435 2352829 := bbase (se 3 (by rfl) ⟨441155, by rfl⟩ : syracuseStep 2352829 = 882311) (by norm_num)
theorem B3137105 : Blo 2089435 3137105 := bstep (se 2 (by rfl) ⟨1176414, by rfl⟩ : syracuseStep 3137105 = 2352829) B2352829
theorem B2091403 : Blo 2089435 2091403 := bstep (se 1 (by rfl) ⟨1568552, by rfl⟩ : syracuseStep 2091403 = 3137105) B3137105
theorem B7058501 : Blo 2089435 7058501 := bbase (se 4 (by rfl) ⟨661734, by rfl⟩ : syracuseStep 7058501 = 1323469) (by norm_num)
theorem B4705667 : Blo 2089435 4705667 := bstep (se 1 (by rfl) ⟨3529250, by rfl⟩ : syracuseStep 4705667 = 7058501) B7058501
theorem B3137111 : Blo 2089435 3137111 := bstep (se 1 (by rfl) ⟨2352833, by rfl⟩ : syracuseStep 3137111 = 4705667) B4705667
theorem B2091407 : Blo 2089435 2091407 := bstep (se 1 (by rfl) ⟨1568555, by rfl⟩ : syracuseStep 2091407 = 3137111) B3137111
theorem B3137117 : Blo 2089435 3137117 := bbase (se 3 (by rfl) ⟨588209, by rfl⟩ : syracuseStep 3137117 = 1176419) (by norm_num)
theorem B2091411 : Blo 2089435 2091411 := bstep (se 1 (by rfl) ⟨1568558, by rfl⟩ : syracuseStep 2091411 = 3137117) B3137117
theorem B4705685 : Blo 2089435 4705685 := bbase (se 6 (by rfl) ⟨110289, by rfl⟩ : syracuseStep 4705685 = 220579) (by norm_num)
theorem B3137123 : Blo 2089435 3137123 := bstep (se 1 (by rfl) ⟨2352842, by rfl⟩ : syracuseStep 3137123 = 4705685) B4705685
theorem B2091415 : Blo 2089435 2091415 := bstep (se 1 (by rfl) ⟨1568561, by rfl⟩ : syracuseStep 2091415 = 3137123) B3137123
theorem B9539797 : Blo 2089435 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B12719729 : Blo 2089435 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B8479819 : Blo 2089435 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B11306425 : Blo 2089435 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B15075233 : Blo 2089435 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B10050155 : Blo 2089435 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B6700103 : Blo 2089435 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B4466735 : Blo 2089435 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B2977823 : Blo 2089435 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B7940861 : Blo 2089435 7940861 := bstep (se 3 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 7940861 = 2977823) B2977823
theorem B5293907 : Blo 2089435 5293907 := bstep (se 1 (by rfl) ⟨3970430, by rfl⟩ : syracuseStep 5293907 = 7940861) B7940861
theorem B3529271 : Blo 2089435 3529271 := bstep (se 1 (by rfl) ⟨2646953, by rfl⟩ : syracuseStep 3529271 = 5293907) B5293907
theorem B2352847 : Blo 2089435 2352847 := bstep (se 1 (by rfl) ⟨1764635, by rfl⟩ : syracuseStep 2352847 = 3529271) B3529271
theorem B3137129 : Blo 2089435 3137129 := bstep (se 2 (by rfl) ⟨1176423, by rfl⟩ : syracuseStep 3137129 = 2352847) B2352847
theorem B2091419 : Blo 2089435 2091419 := bstep (se 1 (by rfl) ⟨1568564, by rfl⟩ : syracuseStep 2091419 = 3137129) B3137129
theorem B17191061 : Blo 2089435 17191061 := bbase (se 6 (by rfl) ⟨402915, by rfl⟩ : syracuseStep 17191061 = 805831) (by norm_num)
theorem B11460707 : Blo 2089435 11460707 := bstep (se 1 (by rfl) ⟨8595530, by rfl⟩ : syracuseStep 11460707 = 17191061) B17191061
theorem B7640471 : Blo 2089435 7640471 := bstep (se 1 (by rfl) ⟨5730353, by rfl⟩ : syracuseStep 7640471 = 11460707) B11460707
theorem B5093647 : Blo 2089435 5093647 := bstep (se 1 (by rfl) ⟨3820235, by rfl⟩ : syracuseStep 5093647 = 7640471) B7640471
theorem B27166117 : Blo 2089435 27166117 := bstep (se 4 (by rfl) ⟨2546823, by rfl⟩ : syracuseStep 27166117 = 5093647) B5093647
theorem B36221489 : Blo 2089435 36221489 := bstep (se 2 (by rfl) ⟨13583058, by rfl⟩ : syracuseStep 36221489 = 27166117) B27166117
theorem B24147659 : Blo 2089435 24147659 := bstep (se 1 (by rfl) ⟨18110744, by rfl⟩ : syracuseStep 24147659 = 36221489) B36221489
theorem B16098439 : Blo 2089435 16098439 := bstep (se 1 (by rfl) ⟨12073829, by rfl⟩ : syracuseStep 16098439 = 24147659) B24147659
theorem B21464585 : Blo 2089435 21464585 := bstep (se 2 (by rfl) ⟨8049219, by rfl⟩ : syracuseStep 21464585 = 16098439) B16098439
theorem B14309723 : Blo 2089435 14309723 := bstep (se 1 (by rfl) ⟨10732292, by rfl⟩ : syracuseStep 14309723 = 21464585) B21464585
theorem B9539815 : Blo 2089435 9539815 := bstep (se 1 (by rfl) ⟨7154861, by rfl⟩ : syracuseStep 9539815 = 14309723) B14309723
theorem B12719753 : Blo 2089435 12719753 := bstep (se 2 (by rfl) ⟨4769907, by rfl⟩ : syracuseStep 12719753 = 9539815) B9539815
theorem B8479835 : Blo 2089435 8479835 := bstep (se 1 (by rfl) ⟨6359876, by rfl⟩ : syracuseStep 8479835 = 12719753) B12719753
theorem B5653223 : Blo 2089435 5653223 := bstep (se 1 (by rfl) ⟨4239917, by rfl⟩ : syracuseStep 5653223 = 8479835) B8479835
theorem B3768815 : Blo 2089435 3768815 := bstep (se 1 (by rfl) ⟨2826611, by rfl⟩ : syracuseStep 3768815 = 5653223) B5653223
theorem B2512543 : Blo 2089435 2512543 := bstep (se 1 (by rfl) ⟨1884407, by rfl⟩ : syracuseStep 2512543 = 3768815) B3768815
theorem B3350057 : Blo 2089435 3350057 := bstep (se 2 (by rfl) ⟨1256271, by rfl⟩ : syracuseStep 3350057 = 2512543) B2512543
theorem B8933485 : Blo 2089435 8933485 := bstep (se 3 (by rfl) ⟨1675028, by rfl⟩ : syracuseStep 8933485 = 3350057) B3350057
theorem B11911313 : Blo 2089435 11911313 := bstep (se 2 (by rfl) ⟨4466742, by rfl⟩ : syracuseStep 11911313 = 8933485) B8933485
theorem B7940875 : Blo 2089435 7940875 := bstep (se 1 (by rfl) ⟨5955656, by rfl⟩ : syracuseStep 7940875 = 11911313) B11911313
theorem B10587833 : Blo 2089435 10587833 := bstep (se 2 (by rfl) ⟨3970437, by rfl⟩ : syracuseStep 10587833 = 7940875) B7940875
theorem B7058555 : Blo 2089435 7058555 := bstep (se 1 (by rfl) ⟨5293916, by rfl⟩ : syracuseStep 7058555 = 10587833) B10587833
theorem B4705703 : Blo 2089435 4705703 := bstep (se 1 (by rfl) ⟨3529277, by rfl⟩ : syracuseStep 4705703 = 7058555) B7058555
theorem B3137135 : Blo 2089435 3137135 := bstep (se 1 (by rfl) ⟨2352851, by rfl⟩ : syracuseStep 3137135 = 4705703) B4705703
theorem B2091423 : Blo 2089435 2091423 := bstep (se 1 (by rfl) ⟨1568567, by rfl⟩ : syracuseStep 2091423 = 3137135) B3137135
theorem B3137141 : Blo 2089435 3137141 := bbase (se 5 (by rfl) ⟨147053, by rfl⟩ : syracuseStep 3137141 = 294107) (by norm_num)
theorem B2091427 : Blo 2089435 2091427 := bstep (se 1 (by rfl) ⟨1568570, by rfl⟩ : syracuseStep 2091427 = 3137141) B3137141
theorem B3970453 : Blo 2089435 3970453 := bbase (se 6 (by rfl) ⟨93057, by rfl⟩ : syracuseStep 3970453 = 186115) (by norm_num)
theorem B5293937 : Blo 2089435 5293937 := bstep (se 2 (by rfl) ⟨1985226, by rfl⟩ : syracuseStep 5293937 = 3970453) B3970453
theorem B3529291 : Blo 2089435 3529291 := bstep (se 1 (by rfl) ⟨2646968, by rfl⟩ : syracuseStep 3529291 = 5293937) B5293937
theorem B4705721 : Blo 2089435 4705721 := bstep (se 2 (by rfl) ⟨1764645, by rfl⟩ : syracuseStep 4705721 = 3529291) B3529291
theorem B3137147 : Blo 2089435 3137147 := bstep (se 1 (by rfl) ⟨2352860, by rfl⟩ : syracuseStep 3137147 = 4705721) B4705721
theorem B2091431 : Blo 2089435 2091431 := bstep (se 1 (by rfl) ⟨1568573, by rfl⟩ : syracuseStep 2091431 = 3137147) B3137147
theorem B2352865 : Blo 2089435 2352865 := bbase (se 2 (by rfl) ⟨882324, by rfl⟩ : syracuseStep 2352865 = 1764649) (by norm_num)
theorem B3137153 : Blo 2089435 3137153 := bstep (se 2 (by rfl) ⟨1176432, by rfl⟩ : syracuseStep 3137153 = 2352865) B2352865
theorem B2091435 : Blo 2089435 2091435 := bstep (se 1 (by rfl) ⟨1568576, by rfl⟩ : syracuseStep 2091435 = 3137153) B3137153
theorem C0 (j : ℕ) (h1 : 522358 ≤ j) (h2 : j ≤ 522858) : Blo 2089435 (4 * j + 3) := by
  interval_cases j
  · exact B2089435
  · exact B2089439
  · exact B2089443
  · exact B2089447
  · exact B2089451
  · exact B2089455
  · exact B2089459
  · exact B2089463
  · exact B2089467
  · exact B2089471
  · exact B2089475
  · exact B2089479
  · exact B2089483
  · exact B2089487
  · exact B2089491
  · exact B2089495
  · exact B2089499
  · exact B2089503
  · exact B2089507
  · exact B2089511
  · exact B2089515
  · exact B2089519
  · exact B2089523
  · exact B2089527
  · exact B2089531
  · exact B2089535
  · exact B2089539
  · exact B2089543
  · exact B2089547
  · exact B2089551
  · exact B2089555
  · exact B2089559
  · exact B2089563
  · exact B2089567
  · exact B2089571
  · exact B2089575
  · exact B2089579
  · exact B2089583
  · exact B2089587
  · exact B2089591
  · exact B2089595
  · exact B2089599
  · exact B2089603
  · exact B2089607
  · exact B2089611
  · exact B2089615
  · exact B2089619
  · exact B2089623
  · exact B2089627
  · exact B2089631
  · exact B2089635
  · exact B2089639
  · exact B2089643
  · exact B2089647
  · exact B2089651
  · exact B2089655
  · exact B2089659
  · exact B2089663
  · exact B2089667
  · exact B2089671
  · exact B2089675
  · exact B2089679
  · exact B2089683
  · exact B2089687
  · exact B2089691
  · exact B2089695
  · exact B2089699
  · exact B2089703
  · exact B2089707
  · exact B2089711
  · exact B2089715
  · exact B2089719
  · exact B2089723
  · exact B2089727
  · exact B2089731
  · exact B2089735
  · exact B2089739
  · exact B2089743
  · exact B2089747
  · exact B2089751
  · exact B2089755
  · exact B2089759
  · exact B2089763
  · exact B2089767
  · exact B2089771
  · exact B2089775
  · exact B2089779
  · exact B2089783
  · exact B2089787
  · exact B2089791
  · exact B2089795
  · exact B2089799
  · exact B2089803
  · exact B2089807
  · exact B2089811
  · exact B2089815
  · exact B2089819
  · exact B2089823
  · exact B2089827
  · exact B2089831
  · exact B2089835
  · exact B2089839
  · exact B2089843
  · exact B2089847
  · exact B2089851
  · exact B2089855
  · exact B2089859
  · exact B2089863
  · exact B2089867
  · exact B2089871
  · exact B2089875
  · exact B2089879
  · exact B2089883
  · exact B2089887
  · exact B2089891
  · exact B2089895
  · exact B2089899
  · exact B2089903
  · exact B2089907
  · exact B2089911
  · exact B2089915
  · exact B2089919
  · exact B2089923
  · exact B2089927
  · exact B2089931
  · exact B2089935
  · exact B2089939
  · exact B2089943
  · exact B2089947
  · exact B2089951
  · exact B2089955
  · exact B2089959
  · exact B2089963
  · exact B2089967
  · exact B2089971
  · exact B2089975
  · exact B2089979
  · exact B2089983
  · exact B2089987
  · exact B2089991
  · exact B2089995
  · exact B2089999
  · exact B2090003
  · exact B2090007
  · exact B2090011
  · exact B2090015
  · exact B2090019
  · exact B2090023
  · exact B2090027
  · exact B2090031
  · exact B2090035
  · exact B2090039
  · exact B2090043
  · exact B2090047
  · exact B2090051
  · exact B2090055
  · exact B2090059
  · exact B2090063
  · exact B2090067
  · exact B2090071
  · exact B2090075
  · exact B2090079
  · exact B2090083
  · exact B2090087
  · exact B2090091
  · exact B2090095
  · exact B2090099
  · exact B2090103
  · exact B2090107
  · exact B2090111
  · exact B2090115
  · exact B2090119
  · exact B2090123
  · exact B2090127
  · exact B2090131
  · exact B2090135
  · exact B2090139
  · exact B2090143
  · exact B2090147
  · exact B2090151
  · exact B2090155
  · exact B2090159
  · exact B2090163
  · exact B2090167
  · exact B2090171
  · exact B2090175
  · exact B2090179
  · exact B2090183
  · exact B2090187
  · exact B2090191
  · exact B2090195
  · exact B2090199
  · exact B2090203
  · exact B2090207
  · exact B2090211
  · exact B2090215
  · exact B2090219
  · exact B2090223
  · exact B2090227
  · exact B2090231
  · exact B2090235
  · exact B2090239
  · exact B2090243
  · exact B2090247
  · exact B2090251
  · exact B2090255
  · exact B2090259
  · exact B2090263
  · exact B2090267
  · exact B2090271
  · exact B2090275
  · exact B2090279
  · exact B2090283
  · exact B2090287
  · exact B2090291
  · exact B2090295
  · exact B2090299
  · exact B2090303
  · exact B2090307
  · exact B2090311
  · exact B2090315
  · exact B2090319
  · exact B2090323
  · exact B2090327
  · exact B2090331
  · exact B2090335
  · exact B2090339
  · exact B2090343
  · exact B2090347
  · exact B2090351
  · exact B2090355
  · exact B2090359
  · exact B2090363
  · exact B2090367
  · exact B2090371
  · exact B2090375
  · exact B2090379
  · exact B2090383
  · exact B2090387
  · exact B2090391
  · exact B2090395
  · exact B2090399
  · exact B2090403
  · exact B2090407
  · exact B2090411
  · exact B2090415
  · exact B2090419
  · exact B2090423
  · exact B2090427
  · exact B2090431
  · exact B2090435
  · exact B2090439
  · exact B2090443
  · exact B2090447
  · exact B2090451
  · exact B2090455
  · exact B2090459
  · exact B2090463
  · exact B2090467
  · exact B2090471
  · exact B2090475
  · exact B2090479
  · exact B2090483
  · exact B2090487
  · exact B2090491
  · exact B2090495
  · exact B2090499
  · exact B2090503
  · exact B2090507
  · exact B2090511
  · exact B2090515
  · exact B2090519
  · exact B2090523
  · exact B2090527
  · exact B2090531
  · exact B2090535
  · exact B2090539
  · exact B2090543
  · exact B2090547
  · exact B2090551
  · exact B2090555
  · exact B2090559
  · exact B2090563
  · exact B2090567
  · exact B2090571
  · exact B2090575
  · exact B2090579
  · exact B2090583
  · exact B2090587
  · exact B2090591
  · exact B2090595
  · exact B2090599
  · exact B2090603
  · exact B2090607
  · exact B2090611
  · exact B2090615
  · exact B2090619
  · exact B2090623
  · exact B2090627
  · exact B2090631
  · exact B2090635
  · exact B2090639
  · exact B2090643
  · exact B2090647
  · exact B2090651
  · exact B2090655
  · exact B2090659
  · exact B2090663
  · exact B2090667
  · exact B2090671
  · exact B2090675
  · exact B2090679
  · exact B2090683
  · exact B2090687
  · exact B2090691
  · exact B2090695
  · exact B2090699
  · exact B2090703
  · exact B2090707
  · exact B2090711
  · exact B2090715
  · exact B2090719
  · exact B2090723
  · exact B2090727
  · exact B2090731
  · exact B2090735
  · exact B2090739
  · exact B2090743
  · exact B2090747
  · exact B2090751
  · exact B2090755
  · exact B2090759
  · exact B2090763
  · exact B2090767
  · exact B2090771
  · exact B2090775
  · exact B2090779
  · exact B2090783
  · exact B2090787
  · exact B2090791
  · exact B2090795
  · exact B2090799
  · exact B2090803
  · exact B2090807
  · exact B2090811
  · exact B2090815
  · exact B2090819
  · exact B2090823
  · exact B2090827
  · exact B2090831
  · exact B2090835
  · exact B2090839
  · exact B2090843
  · exact B2090847
  · exact B2090851
  · exact B2090855
  · exact B2090859
  · exact B2090863
  · exact B2090867
  · exact B2090871
  · exact B2090875
  · exact B2090879
  · exact B2090883
  · exact B2090887
  · exact B2090891
  · exact B2090895
  · exact B2090899
  · exact B2090903
  · exact B2090907
  · exact B2090911
  · exact B2090915
  · exact B2090919
  · exact B2090923
  · exact B2090927
  · exact B2090931
  · exact B2090935
  · exact B2090939
  · exact B2090943
  · exact B2090947
  · exact B2090951
  · exact B2090955
  · exact B2090959
  · exact B2090963
  · exact B2090967
  · exact B2090971
  · exact B2090975
  · exact B2090979
  · exact B2090983
  · exact B2090987
  · exact B2090991
  · exact B2090995
  · exact B2090999
  · exact B2091003
  · exact B2091007
  · exact B2091011
  · exact B2091015
  · exact B2091019
  · exact B2091023
  · exact B2091027
  · exact B2091031
  · exact B2091035
  · exact B2091039
  · exact B2091043
  · exact B2091047
  · exact B2091051
  · exact B2091055
  · exact B2091059
  · exact B2091063
  · exact B2091067
  · exact B2091071
  · exact B2091075
  · exact B2091079
  · exact B2091083
  · exact B2091087
  · exact B2091091
  · exact B2091095
  · exact B2091099
  · exact B2091103
  · exact B2091107
  · exact B2091111
  · exact B2091115
  · exact B2091119
  · exact B2091123
  · exact B2091127
  · exact B2091131
  · exact B2091135
  · exact B2091139
  · exact B2091143
  · exact B2091147
  · exact B2091151
  · exact B2091155
  · exact B2091159
  · exact B2091163
  · exact B2091167
  · exact B2091171
  · exact B2091175
  · exact B2091179
  · exact B2091183
  · exact B2091187
  · exact B2091191
  · exact B2091195
  · exact B2091199
  · exact B2091203
  · exact B2091207
  · exact B2091211
  · exact B2091215
  · exact B2091219
  · exact B2091223
  · exact B2091227
  · exact B2091231
  · exact B2091235
  · exact B2091239
  · exact B2091243
  · exact B2091247
  · exact B2091251
  · exact B2091255
  · exact B2091259
  · exact B2091263
  · exact B2091267
  · exact B2091271
  · exact B2091275
  · exact B2091279
  · exact B2091283
  · exact B2091287
  · exact B2091291
  · exact B2091295
  · exact B2091299
  · exact B2091303
  · exact B2091307
  · exact B2091311
  · exact B2091315
  · exact B2091319
  · exact B2091323
  · exact B2091327
  · exact B2091331
  · exact B2091335
  · exact B2091339
  · exact B2091343
  · exact B2091347
  · exact B2091351
  · exact B2091355
  · exact B2091359
  · exact B2091363
  · exact B2091367
  · exact B2091371
  · exact B2091375
  · exact B2091379
  · exact B2091383
  · exact B2091387
  · exact B2091391
  · exact B2091395
  · exact B2091399
  · exact B2091403
  · exact B2091407
  · exact B2091411
  · exact B2091415
  · exact B2091419
  · exact B2091423
  · exact B2091427
  · exact B2091431
  · exact B2091435
theorem solution (m : ℕ) (hlo : 2089435 ≤ m) (hhi : m ≤ 2091435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 522358 ≤ j := by omega
    have hj2 : j ≤ 522858 := by omega
    have hb : Blo 2089435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
