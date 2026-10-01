-- Prove2me | solution 1 for syracuse_descends_range_1965435_1967435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:56.709002+00:00
-- url     : https://prove2.me/submissions/9008f216-bb0c-4b5c-9ff0-a5c64f31d249

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

theorem B2487505 : Blo 1965435 2487505 := bbase (se 2 (by rfl) ⟨932814, by rfl⟩ : syracuseStep 2487505 = 1865629) (by norm_num)
theorem B3316673 : Blo 1965435 3316673 := bstep (se 2 (by rfl) ⟨1243752, by rfl⟩ : syracuseStep 3316673 = 2487505) B2487505
theorem B2211115 : Blo 1965435 2211115 := bstep (se 1 (by rfl) ⟨1658336, by rfl⟩ : syracuseStep 2211115 = 3316673) B3316673
theorem B2948153 : Blo 1965435 2948153 := bstep (se 2 (by rfl) ⟨1105557, by rfl⟩ : syracuseStep 2948153 = 2211115) B2211115
theorem B1965435 : Blo 1965435 1965435 := bstep (se 1 (by rfl) ⟨1474076, by rfl⟩ : syracuseStep 1965435 = 2948153) B2948153
theorem B3688741 : Blo 1965435 3688741 := bbase (se 4 (by rfl) ⟨345819, by rfl⟩ : syracuseStep 3688741 = 691639) (by norm_num)
theorem B4918321 : Blo 1965435 4918321 := bstep (se 2 (by rfl) ⟨1844370, by rfl⟩ : syracuseStep 4918321 = 3688741) B3688741
theorem B6557761 : Blo 1965435 6557761 := bstep (se 2 (by rfl) ⟨2459160, by rfl⟩ : syracuseStep 6557761 = 4918321) B4918321
theorem B8743681 : Blo 1965435 8743681 := bstep (se 2 (by rfl) ⟨3278880, by rfl⟩ : syracuseStep 8743681 = 6557761) B6557761
theorem B11658241 : Blo 1965435 11658241 := bstep (se 2 (by rfl) ⟨4371840, by rfl⟩ : syracuseStep 11658241 = 8743681) B8743681
theorem B15544321 : Blo 1965435 15544321 := bstep (se 2 (by rfl) ⟨5829120, by rfl⟩ : syracuseStep 15544321 = 11658241) B11658241
theorem B82903045 : Blo 1965435 82903045 := bstep (se 4 (by rfl) ⟨7772160, by rfl⟩ : syracuseStep 82903045 = 15544321) B15544321
theorem B110537393 : Blo 1965435 110537393 := bstep (se 2 (by rfl) ⟨41451522, by rfl⟩ : syracuseStep 110537393 = 82903045) B82903045
theorem B294766381 : Blo 1965435 294766381 := bstep (se 3 (by rfl) ⟨55268696, by rfl⟩ : syracuseStep 294766381 = 110537393) B110537393
theorem B393021841 : Blo 1965435 393021841 := bstep (se 2 (by rfl) ⟨147383190, by rfl⟩ : syracuseStep 393021841 = 294766381) B294766381
theorem B524029121 : Blo 1965435 524029121 := bstep (se 2 (by rfl) ⟨196510920, by rfl⟩ : syracuseStep 524029121 = 393021841) B393021841
theorem B349352747 : Blo 1965435 349352747 := bstep (se 1 (by rfl) ⟨262014560, by rfl⟩ : syracuseStep 349352747 = 524029121) B524029121
theorem B232901831 : Blo 1965435 232901831 := bstep (se 1 (by rfl) ⟨174676373, by rfl⟩ : syracuseStep 232901831 = 349352747) B349352747
theorem B155267887 : Blo 1965435 155267887 := bstep (se 1 (by rfl) ⟨116450915, by rfl⟩ : syracuseStep 155267887 = 232901831) B232901831
theorem B207023849 : Blo 1965435 207023849 := bstep (se 2 (by rfl) ⟨77633943, by rfl⟩ : syracuseStep 207023849 = 155267887) B155267887
theorem B138015899 : Blo 1965435 138015899 := bstep (se 1 (by rfl) ⟨103511924, by rfl⟩ : syracuseStep 138015899 = 207023849) B207023849
theorem B92010599 : Blo 1965435 92010599 := bstep (se 1 (by rfl) ⟨69007949, by rfl⟩ : syracuseStep 92010599 = 138015899) B138015899
theorem B61340399 : Blo 1965435 61340399 := bstep (se 1 (by rfl) ⟨46005299, by rfl⟩ : syracuseStep 61340399 = 92010599) B92010599
theorem B40893599 : Blo 1965435 40893599 := bstep (se 1 (by rfl) ⟨30670199, by rfl⟩ : syracuseStep 40893599 = 61340399) B61340399
theorem B109049597 : Blo 1965435 109049597 := bstep (se 3 (by rfl) ⟨20446799, by rfl⟩ : syracuseStep 109049597 = 40893599) B40893599
theorem B72699731 : Blo 1965435 72699731 := bstep (se 1 (by rfl) ⟨54524798, by rfl⟩ : syracuseStep 72699731 = 109049597) B109049597
theorem B48466487 : Blo 1965435 48466487 := bstep (se 1 (by rfl) ⟨36349865, by rfl⟩ : syracuseStep 48466487 = 72699731) B72699731
theorem B32310991 : Blo 1965435 32310991 := bstep (se 1 (by rfl) ⟨24233243, by rfl⟩ : syracuseStep 32310991 = 48466487) B48466487
theorem B43081321 : Blo 1965435 43081321 := bstep (se 2 (by rfl) ⟨16155495, by rfl⟩ : syracuseStep 43081321 = 32310991) B32310991
theorem B57441761 : Blo 1965435 57441761 := bstep (se 2 (by rfl) ⟨21540660, by rfl⟩ : syracuseStep 57441761 = 43081321) B43081321
theorem B38294507 : Blo 1965435 38294507 := bstep (se 1 (by rfl) ⟨28720880, by rfl⟩ : syracuseStep 38294507 = 57441761) B57441761
theorem B25529671 : Blo 1965435 25529671 := bstep (se 1 (by rfl) ⟨19147253, by rfl⟩ : syracuseStep 25529671 = 38294507) B38294507
theorem B34039561 : Blo 1965435 34039561 := bstep (se 2 (by rfl) ⟨12764835, by rfl⟩ : syracuseStep 34039561 = 25529671) B25529671
theorem B45386081 : Blo 1965435 45386081 := bstep (se 2 (by rfl) ⟨17019780, by rfl⟩ : syracuseStep 45386081 = 34039561) B34039561
theorem B30257387 : Blo 1965435 30257387 := bstep (se 1 (by rfl) ⟨22693040, by rfl⟩ : syracuseStep 30257387 = 45386081) B45386081
theorem B20171591 : Blo 1965435 20171591 := bstep (se 1 (by rfl) ⟨15128693, by rfl⟩ : syracuseStep 20171591 = 30257387) B30257387
theorem B13447727 : Blo 1965435 13447727 := bstep (se 1 (by rfl) ⟨10085795, by rfl⟩ : syracuseStep 13447727 = 20171591) B20171591
theorem B8965151 : Blo 1965435 8965151 := bstep (se 1 (by rfl) ⟨6723863, by rfl⟩ : syracuseStep 8965151 = 13447727) B13447727
theorem B5976767 : Blo 1965435 5976767 := bstep (se 1 (by rfl) ⟨4482575, by rfl⟩ : syracuseStep 5976767 = 8965151) B8965151
theorem B15938045 : Blo 1965435 15938045 := bstep (se 3 (by rfl) ⟨2988383, by rfl⟩ : syracuseStep 15938045 = 5976767) B5976767
theorem B10625363 : Blo 1965435 10625363 := bstep (se 1 (by rfl) ⟨7969022, by rfl⟩ : syracuseStep 10625363 = 15938045) B15938045
theorem B7083575 : Blo 1965435 7083575 := bstep (se 1 (by rfl) ⟨5312681, by rfl⟩ : syracuseStep 7083575 = 10625363) B10625363
theorem B4722383 : Blo 1965435 4722383 := bstep (se 1 (by rfl) ⟨3541787, by rfl⟩ : syracuseStep 4722383 = 7083575) B7083575
theorem B3148255 : Blo 1965435 3148255 := bstep (se 1 (by rfl) ⟨2361191, by rfl⟩ : syracuseStep 3148255 = 4722383) B4722383
theorem B4197673 : Blo 1965435 4197673 := bstep (se 2 (by rfl) ⟨1574127, by rfl⟩ : syracuseStep 4197673 = 3148255) B3148255
theorem B22387589 : Blo 1965435 22387589 := bstep (se 4 (by rfl) ⟨2098836, by rfl⟩ : syracuseStep 22387589 = 4197673) B4197673
theorem B14925059 : Blo 1965435 14925059 := bstep (se 1 (by rfl) ⟨11193794, by rfl⟩ : syracuseStep 14925059 = 22387589) B22387589
theorem B9950039 : Blo 1965435 9950039 := bstep (se 1 (by rfl) ⟨7462529, by rfl⟩ : syracuseStep 9950039 = 14925059) B14925059
theorem B6633359 : Blo 1965435 6633359 := bstep (se 1 (by rfl) ⟨4975019, by rfl⟩ : syracuseStep 6633359 = 9950039) B9950039
theorem B4422239 : Blo 1965435 4422239 := bstep (se 1 (by rfl) ⟨3316679, by rfl⟩ : syracuseStep 4422239 = 6633359) B6633359
theorem B2948159 : Blo 1965435 2948159 := bstep (se 1 (by rfl) ⟨2211119, by rfl⟩ : syracuseStep 2948159 = 4422239) B4422239
theorem B1965439 : Blo 1965435 1965439 := bstep (se 1 (by rfl) ⟨1474079, by rfl⟩ : syracuseStep 1965439 = 2948159) B2948159
theorem B2948165 : Blo 1965435 2948165 := bbase (se 4 (by rfl) ⟨276390, by rfl⟩ : syracuseStep 2948165 = 552781) (by norm_num)
theorem B1965443 : Blo 1965435 1965443 := bstep (se 1 (by rfl) ⟨1474082, by rfl⟩ : syracuseStep 1965443 = 2948165) B2948165
theorem B3316693 : Blo 1965435 3316693 := bbase (se 7 (by rfl) ⟨38867, by rfl⟩ : syracuseStep 3316693 = 77735) (by norm_num)
theorem B4422257 : Blo 1965435 4422257 := bstep (se 2 (by rfl) ⟨1658346, by rfl⟩ : syracuseStep 4422257 = 3316693) B3316693
theorem B2948171 : Blo 1965435 2948171 := bstep (se 1 (by rfl) ⟨2211128, by rfl⟩ : syracuseStep 2948171 = 4422257) B4422257
theorem B1965447 : Blo 1965435 1965447 := bstep (se 1 (by rfl) ⟨1474085, by rfl⟩ : syracuseStep 1965447 = 2948171) B2948171
theorem B2211133 : Blo 1965435 2211133 := bbase (se 3 (by rfl) ⟨414587, by rfl⟩ : syracuseStep 2211133 = 829175) (by norm_num)
theorem B2948177 : Blo 1965435 2948177 := bstep (se 2 (by rfl) ⟨1105566, by rfl⟩ : syracuseStep 2948177 = 2211133) B2211133
theorem B1965451 : Blo 1965435 1965451 := bstep (se 1 (by rfl) ⟨1474088, by rfl⟩ : syracuseStep 1965451 = 2948177) B2948177
theorem B6633413 : Blo 1965435 6633413 := bbase (se 4 (by rfl) ⟨621882, by rfl⟩ : syracuseStep 6633413 = 1243765) (by norm_num)
theorem B4422275 : Blo 1965435 4422275 := bstep (se 1 (by rfl) ⟨3316706, by rfl⟩ : syracuseStep 4422275 = 6633413) B6633413
theorem B2948183 : Blo 1965435 2948183 := bstep (se 1 (by rfl) ⟨2211137, by rfl⟩ : syracuseStep 2948183 = 4422275) B4422275
theorem B1965455 : Blo 1965435 1965455 := bstep (se 1 (by rfl) ⟨1474091, by rfl⟩ : syracuseStep 1965455 = 2948183) B2948183
theorem B2948189 : Blo 1965435 2948189 := bbase (se 3 (by rfl) ⟨552785, by rfl⟩ : syracuseStep 2948189 = 1105571) (by norm_num)
theorem B1965459 : Blo 1965435 1965459 := bstep (se 1 (by rfl) ⟨1474094, by rfl⟩ : syracuseStep 1965459 = 2948189) B2948189
theorem B4422293 : Blo 1965435 4422293 := bbase (se 6 (by rfl) ⟨103647, by rfl⟩ : syracuseStep 4422293 = 207295) (by norm_num)
theorem B2948195 : Blo 1965435 2948195 := bstep (se 1 (by rfl) ⟨2211146, by rfl⟩ : syracuseStep 2948195 = 4422293) B4422293
theorem B1965463 : Blo 1965435 1965463 := bstep (se 1 (by rfl) ⟨1474097, by rfl⟩ : syracuseStep 1965463 = 2948195) B2948195
theorem B3148301 : Blo 1965435 3148301 := bbase (se 3 (by rfl) ⟨590306, by rfl⟩ : syracuseStep 3148301 = 1180613) (by norm_num)
theorem B2098867 : Blo 1965435 2098867 := bstep (se 1 (by rfl) ⟨1574150, by rfl⟩ : syracuseStep 2098867 = 3148301) B3148301
theorem B2798489 : Blo 1965435 2798489 := bstep (se 2 (by rfl) ⟨1049433, by rfl⟩ : syracuseStep 2798489 = 2098867) B2098867
theorem B7462637 : Blo 1965435 7462637 := bstep (se 3 (by rfl) ⟨1399244, by rfl⟩ : syracuseStep 7462637 = 2798489) B2798489
theorem B4975091 : Blo 1965435 4975091 := bstep (se 1 (by rfl) ⟨3731318, by rfl⟩ : syracuseStep 4975091 = 7462637) B7462637
theorem B3316727 : Blo 1965435 3316727 := bstep (se 1 (by rfl) ⟨2487545, by rfl⟩ : syracuseStep 3316727 = 4975091) B4975091
theorem B2211151 : Blo 1965435 2211151 := bstep (se 1 (by rfl) ⟨1658363, by rfl⟩ : syracuseStep 2211151 = 3316727) B3316727
theorem B2948201 : Blo 1965435 2948201 := bstep (se 2 (by rfl) ⟨1105575, by rfl⟩ : syracuseStep 2948201 = 2211151) B2211151
theorem B1965467 : Blo 1965435 1965467 := bstep (se 1 (by rfl) ⟨1474100, by rfl⟩ : syracuseStep 1965467 = 2948201) B2948201
theorem B9573781 : Blo 1965435 9573781 := bbase (se 6 (by rfl) ⟨224385, by rfl⟩ : syracuseStep 9573781 = 448771) (by norm_num)
theorem B12765041 : Blo 1965435 12765041 := bstep (se 2 (by rfl) ⟨4786890, by rfl⟩ : syracuseStep 12765041 = 9573781) B9573781
theorem B8510027 : Blo 1965435 8510027 := bstep (se 1 (by rfl) ⟨6382520, by rfl⟩ : syracuseStep 8510027 = 12765041) B12765041
theorem B90773621 : Blo 1965435 90773621 := bstep (se 5 (by rfl) ⟨4255013, by rfl⟩ : syracuseStep 90773621 = 8510027) B8510027
theorem B60515747 : Blo 1965435 60515747 := bstep (se 1 (by rfl) ⟨45386810, by rfl⟩ : syracuseStep 60515747 = 90773621) B90773621
theorem B40343831 : Blo 1965435 40343831 := bstep (se 1 (by rfl) ⟨30257873, by rfl⟩ : syracuseStep 40343831 = 60515747) B60515747
theorem B26895887 : Blo 1965435 26895887 := bstep (se 1 (by rfl) ⟨20171915, by rfl⟩ : syracuseStep 26895887 = 40343831) B40343831
theorem B17930591 : Blo 1965435 17930591 := bstep (se 1 (by rfl) ⟨13447943, by rfl⟩ : syracuseStep 17930591 = 26895887) B26895887
theorem B11953727 : Blo 1965435 11953727 := bstep (se 1 (by rfl) ⟨8965295, by rfl⟩ : syracuseStep 11953727 = 17930591) B17930591
theorem B7969151 : Blo 1965435 7969151 := bstep (se 1 (by rfl) ⟨5976863, by rfl⟩ : syracuseStep 7969151 = 11953727) B11953727
theorem B21251069 : Blo 1965435 21251069 := bstep (se 3 (by rfl) ⟨3984575, by rfl⟩ : syracuseStep 21251069 = 7969151) B7969151
theorem B14167379 : Blo 1965435 14167379 := bstep (se 1 (by rfl) ⟨10625534, by rfl⟩ : syracuseStep 14167379 = 21251069) B21251069
theorem B9444919 : Blo 1965435 9444919 := bstep (se 1 (by rfl) ⟨7083689, by rfl⟩ : syracuseStep 9444919 = 14167379) B14167379
theorem B12593225 : Blo 1965435 12593225 := bstep (se 2 (by rfl) ⟨4722459, by rfl⟩ : syracuseStep 12593225 = 9444919) B9444919
theorem B8395483 : Blo 1965435 8395483 := bstep (se 1 (by rfl) ⟨6296612, by rfl⟩ : syracuseStep 8395483 = 12593225) B12593225
theorem B11193977 : Blo 1965435 11193977 := bstep (se 2 (by rfl) ⟨4197741, by rfl⟩ : syracuseStep 11193977 = 8395483) B8395483
theorem B7462651 : Blo 1965435 7462651 := bstep (se 1 (by rfl) ⟨5596988, by rfl⟩ : syracuseStep 7462651 = 11193977) B11193977
theorem B9950201 : Blo 1965435 9950201 := bstep (se 2 (by rfl) ⟨3731325, by rfl⟩ : syracuseStep 9950201 = 7462651) B7462651
theorem B6633467 : Blo 1965435 6633467 := bstep (se 1 (by rfl) ⟨4975100, by rfl⟩ : syracuseStep 6633467 = 9950201) B9950201
theorem B4422311 : Blo 1965435 4422311 := bstep (se 1 (by rfl) ⟨3316733, by rfl⟩ : syracuseStep 4422311 = 6633467) B6633467
theorem B2948207 : Blo 1965435 2948207 := bstep (se 1 (by rfl) ⟨2211155, by rfl⟩ : syracuseStep 2948207 = 4422311) B4422311
theorem B1965471 : Blo 1965435 1965471 := bstep (se 1 (by rfl) ⟨1474103, by rfl⟩ : syracuseStep 1965471 = 2948207) B2948207
theorem B2948213 : Blo 1965435 2948213 := bbase (se 5 (by rfl) ⟨138197, by rfl⟩ : syracuseStep 2948213 = 276395) (by norm_num)
theorem B1965475 : Blo 1965435 1965475 := bstep (se 1 (by rfl) ⟨1474106, by rfl⟩ : syracuseStep 1965475 = 2948213) B2948213
theorem B3731341 : Blo 1965435 3731341 := bbase (se 3 (by rfl) ⟨699626, by rfl⟩ : syracuseStep 3731341 = 1399253) (by norm_num)
theorem B4975121 : Blo 1965435 4975121 := bstep (se 2 (by rfl) ⟨1865670, by rfl⟩ : syracuseStep 4975121 = 3731341) B3731341
theorem B3316747 : Blo 1965435 3316747 := bstep (se 1 (by rfl) ⟨2487560, by rfl⟩ : syracuseStep 3316747 = 4975121) B4975121
theorem B4422329 : Blo 1965435 4422329 := bstep (se 2 (by rfl) ⟨1658373, by rfl⟩ : syracuseStep 4422329 = 3316747) B3316747
theorem B2948219 : Blo 1965435 2948219 := bstep (se 1 (by rfl) ⟨2211164, by rfl⟩ : syracuseStep 2948219 = 4422329) B4422329
theorem B1965479 : Blo 1965435 1965479 := bstep (se 1 (by rfl) ⟨1474109, by rfl⟩ : syracuseStep 1965479 = 2948219) B2948219
theorem B2211169 : Blo 1965435 2211169 := bbase (se 2 (by rfl) ⟨829188, by rfl⟩ : syracuseStep 2211169 = 1658377) (by norm_num)
theorem B2948225 : Blo 1965435 2948225 := bstep (se 2 (by rfl) ⟨1105584, by rfl⟩ : syracuseStep 2948225 = 2211169) B2211169
theorem B1965483 : Blo 1965435 1965483 := bstep (se 1 (by rfl) ⟨1474112, by rfl⟩ : syracuseStep 1965483 = 2948225) B2948225
theorem B4975141 : Blo 1965435 4975141 := bbase (se 4 (by rfl) ⟨466419, by rfl⟩ : syracuseStep 4975141 = 932839) (by norm_num)
theorem B6633521 : Blo 1965435 6633521 := bstep (se 2 (by rfl) ⟨2487570, by rfl⟩ : syracuseStep 6633521 = 4975141) B4975141
theorem B4422347 : Blo 1965435 4422347 := bstep (se 1 (by rfl) ⟨3316760, by rfl⟩ : syracuseStep 4422347 = 6633521) B6633521
theorem B2948231 : Blo 1965435 2948231 := bstep (se 1 (by rfl) ⟨2211173, by rfl⟩ : syracuseStep 2948231 = 4422347) B4422347
theorem B1965487 : Blo 1965435 1965487 := bstep (se 1 (by rfl) ⟨1474115, by rfl⟩ : syracuseStep 1965487 = 2948231) B2948231
theorem B2948237 : Blo 1965435 2948237 := bbase (se 3 (by rfl) ⟨552794, by rfl⟩ : syracuseStep 2948237 = 1105589) (by norm_num)
theorem B1965491 : Blo 1965435 1965491 := bstep (se 1 (by rfl) ⟨1474118, by rfl⟩ : syracuseStep 1965491 = 2948237) B2948237
theorem B4422365 : Blo 1965435 4422365 := bbase (se 3 (by rfl) ⟨829193, by rfl⟩ : syracuseStep 4422365 = 1658387) (by norm_num)
theorem B2948243 : Blo 1965435 2948243 := bstep (se 1 (by rfl) ⟨2211182, by rfl⟩ : syracuseStep 2948243 = 4422365) B4422365
theorem B1965495 : Blo 1965435 1965495 := bstep (se 1 (by rfl) ⟨1474121, by rfl⟩ : syracuseStep 1965495 = 2948243) B2948243
theorem B3316781 : Blo 1965435 3316781 := bbase (se 3 (by rfl) ⟨621896, by rfl⟩ : syracuseStep 3316781 = 1243793) (by norm_num)
theorem B2211187 : Blo 1965435 2211187 := bstep (se 1 (by rfl) ⟨1658390, by rfl⟩ : syracuseStep 2211187 = 3316781) B3316781
theorem B2948249 : Blo 1965435 2948249 := bstep (se 2 (by rfl) ⟨1105593, by rfl⟩ : syracuseStep 2948249 = 2211187) B2211187
theorem B1965499 : Blo 1965435 1965499 := bstep (se 1 (by rfl) ⟨1474124, by rfl⟩ : syracuseStep 1965499 = 2948249) B2948249
theorem B21251413 : Blo 1965435 21251413 := bbase (se 12 (by rfl) ⟨7782, by rfl⟩ : syracuseStep 21251413 = 15565) (by norm_num)
theorem B28335217 : Blo 1965435 28335217 := bstep (se 2 (by rfl) ⟨10625706, by rfl⟩ : syracuseStep 28335217 = 21251413) B21251413
theorem B37780289 : Blo 1965435 37780289 := bstep (se 2 (by rfl) ⟨14167608, by rfl⟩ : syracuseStep 37780289 = 28335217) B28335217
theorem B25186859 : Blo 1965435 25186859 := bstep (se 1 (by rfl) ⟨18890144, by rfl⟩ : syracuseStep 25186859 = 37780289) B37780289
theorem B16791239 : Blo 1965435 16791239 := bstep (se 1 (by rfl) ⟨12593429, by rfl⟩ : syracuseStep 16791239 = 25186859) B25186859
theorem B11194159 : Blo 1965435 11194159 := bstep (se 1 (by rfl) ⟨8395619, by rfl⟩ : syracuseStep 11194159 = 16791239) B16791239
theorem B14925545 : Blo 1965435 14925545 := bstep (se 2 (by rfl) ⟨5597079, by rfl⟩ : syracuseStep 14925545 = 11194159) B11194159
theorem B9950363 : Blo 1965435 9950363 := bstep (se 1 (by rfl) ⟨7462772, by rfl⟩ : syracuseStep 9950363 = 14925545) B14925545
theorem B6633575 : Blo 1965435 6633575 := bstep (se 1 (by rfl) ⟨4975181, by rfl⟩ : syracuseStep 6633575 = 9950363) B9950363
theorem B4422383 : Blo 1965435 4422383 := bstep (se 1 (by rfl) ⟨3316787, by rfl⟩ : syracuseStep 4422383 = 6633575) B6633575
theorem B2948255 : Blo 1965435 2948255 := bstep (se 1 (by rfl) ⟨2211191, by rfl⟩ : syracuseStep 2948255 = 4422383) B4422383
theorem B1965503 : Blo 1965435 1965503 := bstep (se 1 (by rfl) ⟨1474127, by rfl⟩ : syracuseStep 1965503 = 2948255) B2948255
theorem B2948261 : Blo 1965435 2948261 := bbase (se 4 (by rfl) ⟨276399, by rfl⟩ : syracuseStep 2948261 = 552799) (by norm_num)
theorem B1965507 : Blo 1965435 1965507 := bstep (se 1 (by rfl) ⟨1474130, by rfl⟩ : syracuseStep 1965507 = 2948261) B2948261
theorem B2487601 : Blo 1965435 2487601 := bbase (se 2 (by rfl) ⟨932850, by rfl⟩ : syracuseStep 2487601 = 1865701) (by norm_num)
theorem B3316801 : Blo 1965435 3316801 := bstep (se 2 (by rfl) ⟨1243800, by rfl⟩ : syracuseStep 3316801 = 2487601) B2487601
theorem B4422401 : Blo 1965435 4422401 := bstep (se 2 (by rfl) ⟨1658400, by rfl⟩ : syracuseStep 4422401 = 3316801) B3316801
theorem B2948267 : Blo 1965435 2948267 := bstep (se 1 (by rfl) ⟨2211200, by rfl⟩ : syracuseStep 2948267 = 4422401) B4422401
theorem B1965511 : Blo 1965435 1965511 := bstep (se 1 (by rfl) ⟨1474133, by rfl⟩ : syracuseStep 1965511 = 2948267) B2948267
theorem B2211205 : Blo 1965435 2211205 := bbase (se 4 (by rfl) ⟨207300, by rfl⟩ : syracuseStep 2211205 = 414601) (by norm_num)
theorem B2948273 : Blo 1965435 2948273 := bstep (se 2 (by rfl) ⟨1105602, by rfl⟩ : syracuseStep 2948273 = 2211205) B2211205
theorem B1965515 : Blo 1965435 1965515 := bstep (se 1 (by rfl) ⟨1474136, by rfl⟩ : syracuseStep 1965515 = 2948273) B2948273
theorem B4197845 : Blo 1965435 4197845 := bbase (se 7 (by rfl) ⟨49193, by rfl⟩ : syracuseStep 4197845 = 98387) (by norm_num)
theorem B2798563 : Blo 1965435 2798563 := bstep (se 1 (by rfl) ⟨2098922, by rfl⟩ : syracuseStep 2798563 = 4197845) B4197845
theorem B3731417 : Blo 1965435 3731417 := bstep (se 2 (by rfl) ⟨1399281, by rfl⟩ : syracuseStep 3731417 = 2798563) B2798563
theorem B2487611 : Blo 1965435 2487611 := bstep (se 1 (by rfl) ⟨1865708, by rfl⟩ : syracuseStep 2487611 = 3731417) B3731417
theorem B6633629 : Blo 1965435 6633629 := bstep (se 3 (by rfl) ⟨1243805, by rfl⟩ : syracuseStep 6633629 = 2487611) B2487611
theorem B4422419 : Blo 1965435 4422419 := bstep (se 1 (by rfl) ⟨3316814, by rfl⟩ : syracuseStep 4422419 = 6633629) B6633629
theorem B2948279 : Blo 1965435 2948279 := bstep (se 1 (by rfl) ⟨2211209, by rfl⟩ : syracuseStep 2948279 = 4422419) B4422419
theorem B1965519 : Blo 1965435 1965519 := bstep (se 1 (by rfl) ⟨1474139, by rfl⟩ : syracuseStep 1965519 = 2948279) B2948279
theorem B2948285 : Blo 1965435 2948285 := bbase (se 3 (by rfl) ⟨552803, by rfl⟩ : syracuseStep 2948285 = 1105607) (by norm_num)
theorem B1965523 : Blo 1965435 1965523 := bstep (se 1 (by rfl) ⟨1474142, by rfl⟩ : syracuseStep 1965523 = 2948285) B2948285
theorem B4422437 : Blo 1965435 4422437 := bbase (se 4 (by rfl) ⟨414603, by rfl⟩ : syracuseStep 4422437 = 829207) (by norm_num)
theorem B2948291 : Blo 1965435 2948291 := bstep (se 1 (by rfl) ⟨2211218, by rfl⟩ : syracuseStep 2948291 = 4422437) B4422437
theorem B1965527 : Blo 1965435 1965527 := bstep (se 1 (by rfl) ⟨1474145, by rfl⟩ : syracuseStep 1965527 = 2948291) B2948291
theorem B4975253 : Blo 1965435 4975253 := bbase (se 6 (by rfl) ⟨116607, by rfl⟩ : syracuseStep 4975253 = 233215) (by norm_num)
theorem B3316835 : Blo 1965435 3316835 := bstep (se 1 (by rfl) ⟨2487626, by rfl⟩ : syracuseStep 3316835 = 4975253) B4975253
theorem B2211223 : Blo 1965435 2211223 := bstep (se 1 (by rfl) ⟨1658417, by rfl⟩ : syracuseStep 2211223 = 3316835) B3316835
theorem B2948297 : Blo 1965435 2948297 := bstep (se 2 (by rfl) ⟨1105611, by rfl⟩ : syracuseStep 2948297 = 2211223) B2211223
theorem B1965531 : Blo 1965435 1965531 := bstep (se 1 (by rfl) ⟨1474148, by rfl⟩ : syracuseStep 1965531 = 2948297) B2948297
theorem B5977061 : Blo 1965435 5977061 := bbase (se 4 (by rfl) ⟨560349, by rfl⟩ : syracuseStep 5977061 = 1120699) (by norm_num)
theorem B3984707 : Blo 1965435 3984707 := bstep (se 1 (by rfl) ⟨2988530, by rfl⟩ : syracuseStep 3984707 = 5977061) B5977061
theorem B2656471 : Blo 1965435 2656471 := bstep (se 1 (by rfl) ⟨1992353, by rfl⟩ : syracuseStep 2656471 = 3984707) B3984707
theorem B3541961 : Blo 1965435 3541961 := bstep (se 2 (by rfl) ⟨1328235, by rfl⟩ : syracuseStep 3541961 = 2656471) B2656471
theorem B2361307 : Blo 1965435 2361307 := bstep (se 1 (by rfl) ⟨1770980, by rfl⟩ : syracuseStep 2361307 = 3541961) B3541961
theorem B3148409 : Blo 1965435 3148409 := bstep (se 2 (by rfl) ⟨1180653, by rfl⟩ : syracuseStep 3148409 = 2361307) B2361307
theorem B8395757 : Blo 1965435 8395757 := bstep (se 3 (by rfl) ⟨1574204, by rfl⟩ : syracuseStep 8395757 = 3148409) B3148409
theorem B5597171 : Blo 1965435 5597171 := bstep (se 1 (by rfl) ⟨4197878, by rfl⟩ : syracuseStep 5597171 = 8395757) B8395757
theorem B3731447 : Blo 1965435 3731447 := bstep (se 1 (by rfl) ⟨2798585, by rfl⟩ : syracuseStep 3731447 = 5597171) B5597171
theorem B9950525 : Blo 1965435 9950525 := bstep (se 3 (by rfl) ⟨1865723, by rfl⟩ : syracuseStep 9950525 = 3731447) B3731447
theorem B6633683 : Blo 1965435 6633683 := bstep (se 1 (by rfl) ⟨4975262, by rfl⟩ : syracuseStep 6633683 = 9950525) B9950525
theorem B4422455 : Blo 1965435 4422455 := bstep (se 1 (by rfl) ⟨3316841, by rfl⟩ : syracuseStep 4422455 = 6633683) B6633683
theorem B2948303 : Blo 1965435 2948303 := bstep (se 1 (by rfl) ⟨2211227, by rfl⟩ : syracuseStep 2948303 = 4422455) B4422455
theorem B1965535 : Blo 1965435 1965535 := bstep (se 1 (by rfl) ⟨1474151, by rfl⟩ : syracuseStep 1965535 = 2948303) B2948303
theorem B2948309 : Blo 1965435 2948309 := bbase (se 7 (by rfl) ⟨34550, by rfl⟩ : syracuseStep 2948309 = 69101) (by norm_num)
theorem B1965539 : Blo 1965435 1965539 := bstep (se 1 (by rfl) ⟨1474154, by rfl⟩ : syracuseStep 1965539 = 2948309) B2948309
theorem B2798597 : Blo 1965435 2798597 := bbase (se 4 (by rfl) ⟨262368, by rfl⟩ : syracuseStep 2798597 = 524737) (by norm_num)
theorem B7462925 : Blo 1965435 7462925 := bstep (se 3 (by rfl) ⟨1399298, by rfl⟩ : syracuseStep 7462925 = 2798597) B2798597
theorem B4975283 : Blo 1965435 4975283 := bstep (se 1 (by rfl) ⟨3731462, by rfl⟩ : syracuseStep 4975283 = 7462925) B7462925
theorem B3316855 : Blo 1965435 3316855 := bstep (se 1 (by rfl) ⟨2487641, by rfl⟩ : syracuseStep 3316855 = 4975283) B4975283
theorem B4422473 : Blo 1965435 4422473 := bstep (se 2 (by rfl) ⟨1658427, by rfl⟩ : syracuseStep 4422473 = 3316855) B3316855
theorem B2948315 : Blo 1965435 2948315 := bstep (se 1 (by rfl) ⟨2211236, by rfl⟩ : syracuseStep 2948315 = 4422473) B4422473
theorem B1965543 : Blo 1965435 1965543 := bstep (se 1 (by rfl) ⟨1474157, by rfl⟩ : syracuseStep 1965543 = 2948315) B2948315
theorem B2211241 : Blo 1965435 2211241 := bbase (se 2 (by rfl) ⟨829215, by rfl⟩ : syracuseStep 2211241 = 1658431) (by norm_num)
theorem B2948321 : Blo 1965435 2948321 := bstep (se 2 (by rfl) ⟨1105620, by rfl⟩ : syracuseStep 2948321 = 2211241) B2211241
theorem B1965547 : Blo 1965435 1965547 := bstep (se 1 (by rfl) ⟨1474160, by rfl⟩ : syracuseStep 1965547 = 2948321) B2948321
theorem B6296869 : Blo 1965435 6296869 := bbase (se 4 (by rfl) ⟨590331, by rfl⟩ : syracuseStep 6296869 = 1180663) (by norm_num)
theorem B8395825 : Blo 1965435 8395825 := bstep (se 2 (by rfl) ⟨3148434, by rfl⟩ : syracuseStep 8395825 = 6296869) B6296869
theorem B11194433 : Blo 1965435 11194433 := bstep (se 2 (by rfl) ⟨4197912, by rfl⟩ : syracuseStep 11194433 = 8395825) B8395825
theorem B7462955 : Blo 1965435 7462955 := bstep (se 1 (by rfl) ⟨5597216, by rfl⟩ : syracuseStep 7462955 = 11194433) B11194433
theorem B4975303 : Blo 1965435 4975303 := bstep (se 1 (by rfl) ⟨3731477, by rfl⟩ : syracuseStep 4975303 = 7462955) B7462955
theorem B6633737 : Blo 1965435 6633737 := bstep (se 2 (by rfl) ⟨2487651, by rfl⟩ : syracuseStep 6633737 = 4975303) B4975303
theorem B4422491 : Blo 1965435 4422491 := bstep (se 1 (by rfl) ⟨3316868, by rfl⟩ : syracuseStep 4422491 = 6633737) B6633737
theorem B2948327 : Blo 1965435 2948327 := bstep (se 1 (by rfl) ⟨2211245, by rfl⟩ : syracuseStep 2948327 = 4422491) B4422491
theorem B1965551 : Blo 1965435 1965551 := bstep (se 1 (by rfl) ⟨1474163, by rfl⟩ : syracuseStep 1965551 = 2948327) B2948327
theorem B2948333 : Blo 1965435 2948333 := bbase (se 3 (by rfl) ⟨552812, by rfl⟩ : syracuseStep 2948333 = 1105625) (by norm_num)
theorem B1965555 : Blo 1965435 1965555 := bstep (se 1 (by rfl) ⟨1474166, by rfl⟩ : syracuseStep 1965555 = 2948333) B2948333
theorem B4422509 : Blo 1965435 4422509 := bbase (se 3 (by rfl) ⟨829220, by rfl⟩ : syracuseStep 4422509 = 1658441) (by norm_num)
theorem B2948339 : Blo 1965435 2948339 := bstep (se 1 (by rfl) ⟨2211254, by rfl⟩ : syracuseStep 2948339 = 4422509) B4422509
theorem B1965559 : Blo 1965435 1965559 := bstep (se 1 (by rfl) ⟨1474169, by rfl⟩ : syracuseStep 1965559 = 2948339) B2948339
theorem B3731501 : Blo 1965435 3731501 := bbase (se 3 (by rfl) ⟨699656, by rfl⟩ : syracuseStep 3731501 = 1399313) (by norm_num)
theorem B2487667 : Blo 1965435 2487667 := bstep (se 1 (by rfl) ⟨1865750, by rfl⟩ : syracuseStep 2487667 = 3731501) B3731501
theorem B3316889 : Blo 1965435 3316889 := bstep (se 2 (by rfl) ⟨1243833, by rfl⟩ : syracuseStep 3316889 = 2487667) B2487667
theorem B2211259 : Blo 1965435 2211259 := bstep (se 1 (by rfl) ⟨1658444, by rfl⟩ : syracuseStep 2211259 = 3316889) B3316889
theorem B2948345 : Blo 1965435 2948345 := bstep (se 2 (by rfl) ⟨1105629, by rfl⟩ : syracuseStep 2948345 = 2211259) B2211259
theorem B1965563 : Blo 1965435 1965563 := bstep (se 1 (by rfl) ⟨1474172, by rfl⟩ : syracuseStep 1965563 = 2948345) B2948345
theorem B2241433 : Blo 1965435 2241433 := bbase (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) (by norm_num)
theorem B11954309 : Blo 1965435 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B31878157 : Blo 1965435 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B42504209 : Blo 1965435 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B28336139 : Blo 1965435 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B18890759 : Blo 1965435 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B50375357 : Blo 1965435 50375357 := bstep (se 3 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 50375357 = 18890759) B18890759
theorem B33583571 : Blo 1965435 33583571 := bstep (se 1 (by rfl) ⟨25187678, by rfl⟩ : syracuseStep 33583571 = 50375357) B50375357
theorem B22389047 : Blo 1965435 22389047 := bstep (se 1 (by rfl) ⟨16791785, by rfl⟩ : syracuseStep 22389047 = 33583571) B33583571
theorem B14926031 : Blo 1965435 14926031 := bstep (se 1 (by rfl) ⟨11194523, by rfl⟩ : syracuseStep 14926031 = 22389047) B22389047
theorem B9950687 : Blo 1965435 9950687 := bstep (se 1 (by rfl) ⟨7463015, by rfl⟩ : syracuseStep 9950687 = 14926031) B14926031
theorem B6633791 : Blo 1965435 6633791 := bstep (se 1 (by rfl) ⟨4975343, by rfl⟩ : syracuseStep 6633791 = 9950687) B9950687
theorem B4422527 : Blo 1965435 4422527 := bstep (se 1 (by rfl) ⟨3316895, by rfl⟩ : syracuseStep 4422527 = 6633791) B6633791
theorem B2948351 : Blo 1965435 2948351 := bstep (se 1 (by rfl) ⟨2211263, by rfl⟩ : syracuseStep 2948351 = 4422527) B4422527
theorem B1965567 : Blo 1965435 1965567 := bstep (se 1 (by rfl) ⟨1474175, by rfl⟩ : syracuseStep 1965567 = 2948351) B2948351
theorem B2948357 : Blo 1965435 2948357 := bbase (se 4 (by rfl) ⟨276408, by rfl⟩ : syracuseStep 2948357 = 552817) (by norm_num)
theorem B1965571 : Blo 1965435 1965571 := bstep (se 1 (by rfl) ⟨1474178, by rfl⟩ : syracuseStep 1965571 = 2948357) B2948357
theorem B3316909 : Blo 1965435 3316909 := bbase (se 3 (by rfl) ⟨621920, by rfl⟩ : syracuseStep 3316909 = 1243841) (by norm_num)
theorem B4422545 : Blo 1965435 4422545 := bstep (se 2 (by rfl) ⟨1658454, by rfl⟩ : syracuseStep 4422545 = 3316909) B3316909
theorem B2948363 : Blo 1965435 2948363 := bstep (se 1 (by rfl) ⟨2211272, by rfl⟩ : syracuseStep 2948363 = 4422545) B4422545
theorem B1965575 : Blo 1965435 1965575 := bstep (se 1 (by rfl) ⟨1474181, by rfl⟩ : syracuseStep 1965575 = 2948363) B2948363
theorem B2211277 : Blo 1965435 2211277 := bbase (se 3 (by rfl) ⟨414614, by rfl⟩ : syracuseStep 2211277 = 829229) (by norm_num)
theorem B2948369 : Blo 1965435 2948369 := bstep (se 2 (by rfl) ⟨1105638, by rfl⟩ : syracuseStep 2948369 = 2211277) B2211277
theorem B1965579 : Blo 1965435 1965579 := bstep (se 1 (by rfl) ⟨1474184, by rfl⟩ : syracuseStep 1965579 = 2948369) B2948369
theorem B6633845 : Blo 1965435 6633845 := bbase (se 5 (by rfl) ⟨310961, by rfl⟩ : syracuseStep 6633845 = 621923) (by norm_num)
theorem B4422563 : Blo 1965435 4422563 := bstep (se 1 (by rfl) ⟨3316922, by rfl⟩ : syracuseStep 4422563 = 6633845) B6633845
theorem B2948375 : Blo 1965435 2948375 := bstep (se 1 (by rfl) ⟨2211281, by rfl⟩ : syracuseStep 2948375 = 4422563) B4422563
theorem B1965583 : Blo 1965435 1965583 := bstep (se 1 (by rfl) ⟨1474187, by rfl⟩ : syracuseStep 1965583 = 2948375) B2948375
theorem B2948381 : Blo 1965435 2948381 := bbase (se 3 (by rfl) ⟨552821, by rfl⟩ : syracuseStep 2948381 = 1105643) (by norm_num)
theorem B1965587 : Blo 1965435 1965587 := bstep (se 1 (by rfl) ⟨1474190, by rfl⟩ : syracuseStep 1965587 = 2948381) B2948381
theorem B4422581 : Blo 1965435 4422581 := bbase (se 5 (by rfl) ⟨207308, by rfl⟩ : syracuseStep 4422581 = 414617) (by norm_num)
theorem B2948387 : Blo 1965435 2948387 := bstep (se 1 (by rfl) ⟨2211290, by rfl⟩ : syracuseStep 2948387 = 4422581) B4422581
theorem B1965591 : Blo 1965435 1965591 := bstep (se 1 (by rfl) ⟨1474193, by rfl⟩ : syracuseStep 1965591 = 2948387) B2948387
theorem B3542069 : Blo 1965435 3542069 := bbase (se 5 (by rfl) ⟨166034, by rfl⟩ : syracuseStep 3542069 = 332069) (by norm_num)
theorem B9445517 : Blo 1965435 9445517 := bstep (se 3 (by rfl) ⟨1771034, by rfl⟩ : syracuseStep 9445517 = 3542069) B3542069
theorem B6297011 : Blo 1965435 6297011 := bstep (se 1 (by rfl) ⟨4722758, by rfl⟩ : syracuseStep 6297011 = 9445517) B9445517
theorem B4198007 : Blo 1965435 4198007 := bstep (se 1 (by rfl) ⟨3148505, by rfl⟩ : syracuseStep 4198007 = 6297011) B6297011
theorem B11194685 : Blo 1965435 11194685 := bstep (se 3 (by rfl) ⟨2099003, by rfl⟩ : syracuseStep 11194685 = 4198007) B4198007
theorem B7463123 : Blo 1965435 7463123 := bstep (se 1 (by rfl) ⟨5597342, by rfl⟩ : syracuseStep 7463123 = 11194685) B11194685
theorem B4975415 : Blo 1965435 4975415 := bstep (se 1 (by rfl) ⟨3731561, by rfl⟩ : syracuseStep 4975415 = 7463123) B7463123
theorem B3316943 : Blo 1965435 3316943 := bstep (se 1 (by rfl) ⟨2487707, by rfl⟩ : syracuseStep 3316943 = 4975415) B4975415
theorem B2211295 : Blo 1965435 2211295 := bstep (se 1 (by rfl) ⟨1658471, by rfl⟩ : syracuseStep 2211295 = 3316943) B3316943
theorem B2948393 : Blo 1965435 2948393 := bstep (se 2 (by rfl) ⟨1105647, by rfl⟩ : syracuseStep 2948393 = 2211295) B2211295
theorem B1965595 : Blo 1965435 1965595 := bstep (se 1 (by rfl) ⟨1474196, by rfl⟩ : syracuseStep 1965595 = 2948393) B2948393
theorem B2875565 : Blo 1965435 2875565 := bbase (se 3 (by rfl) ⟨539168, by rfl⟩ : syracuseStep 2875565 = 1078337) (by norm_num)
theorem B7668173 : Blo 1965435 7668173 := bstep (se 3 (by rfl) ⟨1437782, by rfl⟩ : syracuseStep 7668173 = 2875565) B2875565
theorem B5112115 : Blo 1965435 5112115 := bstep (se 1 (by rfl) ⟨3834086, by rfl⟩ : syracuseStep 5112115 = 7668173) B7668173
theorem B27264613 : Blo 1965435 27264613 := bstep (se 4 (by rfl) ⟨2556057, by rfl⟩ : syracuseStep 27264613 = 5112115) B5112115
theorem B36352817 : Blo 1965435 36352817 := bstep (se 2 (by rfl) ⟨13632306, by rfl⟩ : syracuseStep 36352817 = 27264613) B27264613
theorem B24235211 : Blo 1965435 24235211 := bstep (se 1 (by rfl) ⟨18176408, by rfl⟩ : syracuseStep 24235211 = 36352817) B36352817
theorem B64627229 : Blo 1965435 64627229 := bstep (se 3 (by rfl) ⟨12117605, by rfl⟩ : syracuseStep 64627229 = 24235211) B24235211
theorem B43084819 : Blo 1965435 43084819 := bstep (se 1 (by rfl) ⟨32313614, by rfl⟩ : syracuseStep 43084819 = 64627229) B64627229
theorem B57446425 : Blo 1965435 57446425 := bstep (se 2 (by rfl) ⟨21542409, by rfl⟩ : syracuseStep 57446425 = 43084819) B43084819
theorem B76595233 : Blo 1965435 76595233 := bstep (se 2 (by rfl) ⟨28723212, by rfl⟩ : syracuseStep 76595233 = 57446425) B57446425
theorem B102126977 : Blo 1965435 102126977 := bstep (se 2 (by rfl) ⟨38297616, by rfl⟩ : syracuseStep 102126977 = 76595233) B76595233
theorem B68084651 : Blo 1965435 68084651 := bstep (se 1 (by rfl) ⟨51063488, by rfl⟩ : syracuseStep 68084651 = 102126977) B102126977
theorem B181559069 : Blo 1965435 181559069 := bstep (se 3 (by rfl) ⟨34042325, by rfl⟩ : syracuseStep 181559069 = 68084651) B68084651
theorem B121039379 : Blo 1965435 121039379 := bstep (se 1 (by rfl) ⟨90779534, by rfl⟩ : syracuseStep 121039379 = 181559069) B181559069
theorem B80692919 : Blo 1965435 80692919 := bstep (se 1 (by rfl) ⟨60519689, by rfl⟩ : syracuseStep 80692919 = 121039379) B121039379
theorem B53795279 : Blo 1965435 53795279 := bstep (se 1 (by rfl) ⟨40346459, by rfl⟩ : syracuseStep 53795279 = 80692919) B80692919
theorem B35863519 : Blo 1965435 35863519 := bstep (se 1 (by rfl) ⟨26897639, by rfl⟩ : syracuseStep 35863519 = 53795279) B53795279
theorem B47818025 : Blo 1965435 47818025 := bstep (se 2 (by rfl) ⟨17931759, by rfl⟩ : syracuseStep 47818025 = 35863519) B35863519
theorem B31878683 : Blo 1965435 31878683 := bstep (se 1 (by rfl) ⟨23909012, by rfl⟩ : syracuseStep 31878683 = 47818025) B47818025
theorem B21252455 : Blo 1965435 21252455 := bstep (se 1 (by rfl) ⟨15939341, by rfl⟩ : syracuseStep 21252455 = 31878683) B31878683
theorem B14168303 : Blo 1965435 14168303 := bstep (se 1 (by rfl) ⟨10626227, by rfl⟩ : syracuseStep 14168303 = 21252455) B21252455
theorem B9445535 : Blo 1965435 9445535 := bstep (se 1 (by rfl) ⟨7084151, by rfl⟩ : syracuseStep 9445535 = 14168303) B14168303
theorem B6297023 : Blo 1965435 6297023 := bstep (se 1 (by rfl) ⟨4722767, by rfl⟩ : syracuseStep 6297023 = 9445535) B9445535
theorem B4198015 : Blo 1965435 4198015 := bstep (se 1 (by rfl) ⟨3148511, by rfl⟩ : syracuseStep 4198015 = 6297023) B6297023
theorem B5597353 : Blo 1965435 5597353 := bstep (se 2 (by rfl) ⟨2099007, by rfl⟩ : syracuseStep 5597353 = 4198015) B4198015
theorem B7463137 : Blo 1965435 7463137 := bstep (se 2 (by rfl) ⟨2798676, by rfl⟩ : syracuseStep 7463137 = 5597353) B5597353
theorem B9950849 : Blo 1965435 9950849 := bstep (se 2 (by rfl) ⟨3731568, by rfl⟩ : syracuseStep 9950849 = 7463137) B7463137
theorem B6633899 : Blo 1965435 6633899 := bstep (se 1 (by rfl) ⟨4975424, by rfl⟩ : syracuseStep 6633899 = 9950849) B9950849
theorem B4422599 : Blo 1965435 4422599 := bstep (se 1 (by rfl) ⟨3316949, by rfl⟩ : syracuseStep 4422599 = 6633899) B6633899
theorem B2948399 : Blo 1965435 2948399 := bstep (se 1 (by rfl) ⟨2211299, by rfl⟩ : syracuseStep 2948399 = 4422599) B4422599
theorem B1965599 : Blo 1965435 1965599 := bstep (se 1 (by rfl) ⟨1474199, by rfl⟩ : syracuseStep 1965599 = 2948399) B2948399
theorem B2948405 : Blo 1965435 2948405 := bbase (se 5 (by rfl) ⟨138206, by rfl⟩ : syracuseStep 2948405 = 276413) (by norm_num)
theorem B1965603 : Blo 1965435 1965603 := bstep (se 1 (by rfl) ⟨1474202, by rfl⟩ : syracuseStep 1965603 = 2948405) B2948405
theorem B4975445 : Blo 1965435 4975445 := bbase (se 9 (by rfl) ⟨14576, by rfl⟩ : syracuseStep 4975445 = 29153) (by norm_num)
theorem B3316963 : Blo 1965435 3316963 := bstep (se 1 (by rfl) ⟨2487722, by rfl⟩ : syracuseStep 3316963 = 4975445) B4975445
theorem B4422617 : Blo 1965435 4422617 := bstep (se 2 (by rfl) ⟨1658481, by rfl⟩ : syracuseStep 4422617 = 3316963) B3316963
theorem B2948411 : Blo 1965435 2948411 := bstep (se 1 (by rfl) ⟨2211308, by rfl⟩ : syracuseStep 2948411 = 4422617) B4422617
theorem B1965607 : Blo 1965435 1965607 := bstep (se 1 (by rfl) ⟨1474205, by rfl⟩ : syracuseStep 1965607 = 2948411) B2948411
theorem B2211313 : Blo 1965435 2211313 := bbase (se 2 (by rfl) ⟨829242, by rfl⟩ : syracuseStep 2211313 = 1658485) (by norm_num)
theorem B2948417 : Blo 1965435 2948417 := bstep (se 2 (by rfl) ⟨1105656, by rfl⟩ : syracuseStep 2948417 = 2211313) B2211313
theorem B1965611 : Blo 1965435 1965611 := bstep (se 1 (by rfl) ⟨1474208, by rfl⟩ : syracuseStep 1965611 = 2948417) B2948417
theorem B3984869 : Blo 1965435 3984869 := bbase (se 4 (by rfl) ⟨373581, by rfl⟩ : syracuseStep 3984869 = 747163) (by norm_num)
theorem B2656579 : Blo 1965435 2656579 := bstep (se 1 (by rfl) ⟨1992434, by rfl⟩ : syracuseStep 2656579 = 3984869) B3984869
theorem B3542105 : Blo 1965435 3542105 := bstep (se 2 (by rfl) ⟨1328289, by rfl⟩ : syracuseStep 3542105 = 2656579) B2656579
theorem B2361403 : Blo 1965435 2361403 := bstep (se 1 (by rfl) ⟨1771052, by rfl⟩ : syracuseStep 2361403 = 3542105) B3542105
theorem B12594149 : Blo 1965435 12594149 := bstep (se 4 (by rfl) ⟨1180701, by rfl⟩ : syracuseStep 12594149 = 2361403) B2361403
theorem B8396099 : Blo 1965435 8396099 := bstep (se 1 (by rfl) ⟨6297074, by rfl⟩ : syracuseStep 8396099 = 12594149) B12594149
theorem B5597399 : Blo 1965435 5597399 := bstep (se 1 (by rfl) ⟨4198049, by rfl⟩ : syracuseStep 5597399 = 8396099) B8396099
theorem B3731599 : Blo 1965435 3731599 := bstep (se 1 (by rfl) ⟨2798699, by rfl⟩ : syracuseStep 3731599 = 5597399) B5597399
theorem B4975465 : Blo 1965435 4975465 := bstep (se 2 (by rfl) ⟨1865799, by rfl⟩ : syracuseStep 4975465 = 3731599) B3731599
theorem B6633953 : Blo 1965435 6633953 := bstep (se 2 (by rfl) ⟨2487732, by rfl⟩ : syracuseStep 6633953 = 4975465) B4975465
theorem B4422635 : Blo 1965435 4422635 := bstep (se 1 (by rfl) ⟨3316976, by rfl⟩ : syracuseStep 4422635 = 6633953) B6633953
theorem B2948423 : Blo 1965435 2948423 := bstep (se 1 (by rfl) ⟨2211317, by rfl⟩ : syracuseStep 2948423 = 4422635) B4422635
theorem B1965615 : Blo 1965435 1965615 := bstep (se 1 (by rfl) ⟨1474211, by rfl⟩ : syracuseStep 1965615 = 2948423) B2948423
theorem B2948429 : Blo 1965435 2948429 := bbase (se 3 (by rfl) ⟨552830, by rfl⟩ : syracuseStep 2948429 = 1105661) (by norm_num)
theorem B1965619 : Blo 1965435 1965619 := bstep (se 1 (by rfl) ⟨1474214, by rfl⟩ : syracuseStep 1965619 = 2948429) B2948429
theorem B4422653 : Blo 1965435 4422653 := bbase (se 3 (by rfl) ⟨829247, by rfl⟩ : syracuseStep 4422653 = 1658495) (by norm_num)
theorem B2948435 : Blo 1965435 2948435 := bstep (se 1 (by rfl) ⟨2211326, by rfl⟩ : syracuseStep 2948435 = 4422653) B4422653
theorem B1965623 : Blo 1965435 1965623 := bstep (se 1 (by rfl) ⟨1474217, by rfl⟩ : syracuseStep 1965623 = 2948435) B2948435
theorem B3316997 : Blo 1965435 3316997 := bbase (se 4 (by rfl) ⟨310968, by rfl⟩ : syracuseStep 3316997 = 621937) (by norm_num)
theorem B2211331 : Blo 1965435 2211331 := bstep (se 1 (by rfl) ⟨1658498, by rfl⟩ : syracuseStep 2211331 = 3316997) B3316997
theorem B2948441 : Blo 1965435 2948441 := bstep (se 2 (by rfl) ⟨1105665, by rfl⟩ : syracuseStep 2948441 = 2211331) B2211331
theorem B1965627 : Blo 1965435 1965627 := bstep (se 1 (by rfl) ⟨1474220, by rfl⟩ : syracuseStep 1965627 = 2948441) B2948441
theorem B14926517 : Blo 1965435 14926517 := bbase (se 5 (by rfl) ⟨699680, by rfl⟩ : syracuseStep 14926517 = 1399361) (by norm_num)
theorem B9951011 : Blo 1965435 9951011 := bstep (se 1 (by rfl) ⟨7463258, by rfl⟩ : syracuseStep 9951011 = 14926517) B14926517
theorem B6634007 : Blo 1965435 6634007 := bstep (se 1 (by rfl) ⟨4975505, by rfl⟩ : syracuseStep 6634007 = 9951011) B9951011
theorem B4422671 : Blo 1965435 4422671 := bstep (se 1 (by rfl) ⟨3317003, by rfl⟩ : syracuseStep 4422671 = 6634007) B6634007
theorem B2948447 : Blo 1965435 2948447 := bstep (se 1 (by rfl) ⟨2211335, by rfl⟩ : syracuseStep 2948447 = 4422671) B4422671
theorem B1965631 : Blo 1965435 1965631 := bstep (se 1 (by rfl) ⟨1474223, by rfl⟩ : syracuseStep 1965631 = 2948447) B2948447
theorem B2948453 : Blo 1965435 2948453 := bbase (se 4 (by rfl) ⟨276417, by rfl⟩ : syracuseStep 2948453 = 552835) (by norm_num)
theorem B1965635 : Blo 1965435 1965635 := bstep (se 1 (by rfl) ⟨1474226, by rfl⟩ : syracuseStep 1965635 = 2948453) B2948453
theorem B3731645 : Blo 1965435 3731645 := bbase (se 3 (by rfl) ⟨699683, by rfl⟩ : syracuseStep 3731645 = 1399367) (by norm_num)
theorem B2487763 : Blo 1965435 2487763 := bstep (se 1 (by rfl) ⟨1865822, by rfl⟩ : syracuseStep 2487763 = 3731645) B3731645
theorem B3317017 : Blo 1965435 3317017 := bstep (se 2 (by rfl) ⟨1243881, by rfl⟩ : syracuseStep 3317017 = 2487763) B2487763
theorem B4422689 : Blo 1965435 4422689 := bstep (se 2 (by rfl) ⟨1658508, by rfl⟩ : syracuseStep 4422689 = 3317017) B3317017
theorem B2948459 : Blo 1965435 2948459 := bstep (se 1 (by rfl) ⟨2211344, by rfl⟩ : syracuseStep 2948459 = 4422689) B4422689
theorem B1965639 : Blo 1965435 1965639 := bstep (se 1 (by rfl) ⟨1474229, by rfl⟩ : syracuseStep 1965639 = 2948459) B2948459
theorem B2211349 : Blo 1965435 2211349 := bbase (se 6 (by rfl) ⟨51828, by rfl⟩ : syracuseStep 2211349 = 103657) (by norm_num)
theorem B2948465 : Blo 1965435 2948465 := bstep (se 2 (by rfl) ⟨1105674, by rfl⟩ : syracuseStep 2948465 = 2211349) B2211349
theorem B1965643 : Blo 1965435 1965643 := bstep (se 1 (by rfl) ⟨1474232, by rfl⟩ : syracuseStep 1965643 = 2948465) B2948465
theorem B2487773 : Blo 1965435 2487773 := bbase (se 3 (by rfl) ⟨466457, by rfl⟩ : syracuseStep 2487773 = 932915) (by norm_num)
theorem B6634061 : Blo 1965435 6634061 := bstep (se 3 (by rfl) ⟨1243886, by rfl⟩ : syracuseStep 6634061 = 2487773) B2487773
theorem B4422707 : Blo 1965435 4422707 := bstep (se 1 (by rfl) ⟨3317030, by rfl⟩ : syracuseStep 4422707 = 6634061) B6634061
theorem B2948471 : Blo 1965435 2948471 := bstep (se 1 (by rfl) ⟨2211353, by rfl⟩ : syracuseStep 2948471 = 4422707) B4422707
theorem B1965647 : Blo 1965435 1965647 := bstep (se 1 (by rfl) ⟨1474235, by rfl⟩ : syracuseStep 1965647 = 2948471) B2948471
theorem B2948477 : Blo 1965435 2948477 := bbase (se 3 (by rfl) ⟨552839, by rfl⟩ : syracuseStep 2948477 = 1105679) (by norm_num)
theorem B1965651 : Blo 1965435 1965651 := bstep (se 1 (by rfl) ⟨1474238, by rfl⟩ : syracuseStep 1965651 = 2948477) B2948477
theorem B4422725 : Blo 1965435 4422725 := bbase (se 4 (by rfl) ⟨414630, by rfl⟩ : syracuseStep 4422725 = 829261) (by norm_num)
theorem B2948483 : Blo 1965435 2948483 := bstep (se 1 (by rfl) ⟨2211362, by rfl⟩ : syracuseStep 2948483 = 4422725) B4422725
theorem B1965655 : Blo 1965435 1965655 := bstep (se 1 (by rfl) ⟨1474241, by rfl⟩ : syracuseStep 1965655 = 2948483) B2948483
theorem B5597525 : Blo 1965435 5597525 := bbase (se 10 (by rfl) ⟨8199, by rfl⟩ : syracuseStep 5597525 = 16399) (by norm_num)
theorem B3731683 : Blo 1965435 3731683 := bstep (se 1 (by rfl) ⟨2798762, by rfl⟩ : syracuseStep 3731683 = 5597525) B5597525
theorem B4975577 : Blo 1965435 4975577 := bstep (se 2 (by rfl) ⟨1865841, by rfl⟩ : syracuseStep 4975577 = 3731683) B3731683
theorem B3317051 : Blo 1965435 3317051 := bstep (se 1 (by rfl) ⟨2487788, by rfl⟩ : syracuseStep 3317051 = 4975577) B4975577
theorem B2211367 : Blo 1965435 2211367 := bstep (se 1 (by rfl) ⟨1658525, by rfl⟩ : syracuseStep 2211367 = 3317051) B3317051
theorem B2948489 : Blo 1965435 2948489 := bstep (se 2 (by rfl) ⟨1105683, by rfl⟩ : syracuseStep 2948489 = 2211367) B2211367
theorem B1965659 : Blo 1965435 1965659 := bstep (se 1 (by rfl) ⟨1474244, by rfl⟩ : syracuseStep 1965659 = 2948489) B2948489
theorem B9951173 : Blo 1965435 9951173 := bbase (se 4 (by rfl) ⟨932922, by rfl⟩ : syracuseStep 9951173 = 1865845) (by norm_num)
theorem B6634115 : Blo 1965435 6634115 := bstep (se 1 (by rfl) ⟨4975586, by rfl⟩ : syracuseStep 6634115 = 9951173) B9951173
theorem B4422743 : Blo 1965435 4422743 := bstep (se 1 (by rfl) ⟨3317057, by rfl⟩ : syracuseStep 4422743 = 6634115) B6634115
theorem B2948495 : Blo 1965435 2948495 := bstep (se 1 (by rfl) ⟨2211371, by rfl⟩ : syracuseStep 2948495 = 4422743) B4422743
theorem B1965663 : Blo 1965435 1965663 := bstep (se 1 (by rfl) ⟨1474247, by rfl⟩ : syracuseStep 1965663 = 2948495) B2948495
theorem B2948501 : Blo 1965435 2948501 := bbase (se 6 (by rfl) ⟨69105, by rfl⟩ : syracuseStep 2948501 = 138211) (by norm_num)
theorem B1965667 : Blo 1965435 1965667 := bstep (se 1 (by rfl) ⟨1474250, by rfl⟩ : syracuseStep 1965667 = 2948501) B2948501
theorem B4722941 : Blo 1965435 4722941 := bbase (se 3 (by rfl) ⟨885551, by rfl⟩ : syracuseStep 4722941 = 1771103) (by norm_num)
theorem B3148627 : Blo 1965435 3148627 := bstep (se 1 (by rfl) ⟨2361470, by rfl⟩ : syracuseStep 3148627 = 4722941) B4722941
theorem B4198169 : Blo 1965435 4198169 := bstep (se 2 (by rfl) ⟨1574313, by rfl⟩ : syracuseStep 4198169 = 3148627) B3148627
theorem B11195117 : Blo 1965435 11195117 := bstep (se 3 (by rfl) ⟨2099084, by rfl⟩ : syracuseStep 11195117 = 4198169) B4198169
theorem B7463411 : Blo 1965435 7463411 := bstep (se 1 (by rfl) ⟨5597558, by rfl⟩ : syracuseStep 7463411 = 11195117) B11195117
theorem B4975607 : Blo 1965435 4975607 := bstep (se 1 (by rfl) ⟨3731705, by rfl⟩ : syracuseStep 4975607 = 7463411) B7463411
theorem B3317071 : Blo 1965435 3317071 := bstep (se 1 (by rfl) ⟨2487803, by rfl⟩ : syracuseStep 3317071 = 4975607) B4975607
theorem B4422761 : Blo 1965435 4422761 := bstep (se 2 (by rfl) ⟨1658535, by rfl⟩ : syracuseStep 4422761 = 3317071) B3317071
theorem B2948507 : Blo 1965435 2948507 := bstep (se 1 (by rfl) ⟨2211380, by rfl⟩ : syracuseStep 2948507 = 4422761) B4422761
theorem B1965671 : Blo 1965435 1965671 := bstep (se 1 (by rfl) ⟨1474253, by rfl⟩ : syracuseStep 1965671 = 2948507) B2948507
theorem B2211385 : Blo 1965435 2211385 := bbase (se 2 (by rfl) ⟨829269, by rfl⟩ : syracuseStep 2211385 = 1658539) (by norm_num)
theorem B2948513 : Blo 1965435 2948513 := bstep (se 2 (by rfl) ⟨1105692, by rfl⟩ : syracuseStep 2948513 = 2211385) B2211385
theorem B1965675 : Blo 1965435 1965675 := bstep (se 1 (by rfl) ⟨1474256, by rfl⟩ : syracuseStep 1965675 = 2948513) B2948513
theorem B2099093 : Blo 1965435 2099093 := bbase (se 6 (by rfl) ⟨49197, by rfl⟩ : syracuseStep 2099093 = 98395) (by norm_num)
theorem B5597581 : Blo 1965435 5597581 := bstep (se 3 (by rfl) ⟨1049546, by rfl⟩ : syracuseStep 5597581 = 2099093) B2099093
theorem B7463441 : Blo 1965435 7463441 := bstep (se 2 (by rfl) ⟨2798790, by rfl⟩ : syracuseStep 7463441 = 5597581) B5597581
theorem B4975627 : Blo 1965435 4975627 := bstep (se 1 (by rfl) ⟨3731720, by rfl⟩ : syracuseStep 4975627 = 7463441) B7463441
theorem B6634169 : Blo 1965435 6634169 := bstep (se 2 (by rfl) ⟨2487813, by rfl⟩ : syracuseStep 6634169 = 4975627) B4975627
theorem B4422779 : Blo 1965435 4422779 := bstep (se 1 (by rfl) ⟨3317084, by rfl⟩ : syracuseStep 4422779 = 6634169) B6634169
theorem B2948519 : Blo 1965435 2948519 := bstep (se 1 (by rfl) ⟨2211389, by rfl⟩ : syracuseStep 2948519 = 4422779) B4422779
theorem B1965679 : Blo 1965435 1965679 := bstep (se 1 (by rfl) ⟨1474259, by rfl⟩ : syracuseStep 1965679 = 2948519) B2948519
theorem B2948525 : Blo 1965435 2948525 := bbase (se 3 (by rfl) ⟨552848, by rfl⟩ : syracuseStep 2948525 = 1105697) (by norm_num)
theorem B1965683 : Blo 1965435 1965683 := bstep (se 1 (by rfl) ⟨1474262, by rfl⟩ : syracuseStep 1965683 = 2948525) B2948525
theorem B4422797 : Blo 1965435 4422797 := bbase (se 3 (by rfl) ⟨829274, by rfl⟩ : syracuseStep 4422797 = 1658549) (by norm_num)
theorem B2948531 : Blo 1965435 2948531 := bstep (se 1 (by rfl) ⟨2211398, by rfl⟩ : syracuseStep 2948531 = 4422797) B4422797
theorem B1965687 : Blo 1965435 1965687 := bstep (se 1 (by rfl) ⟨1474265, by rfl⟩ : syracuseStep 1965687 = 2948531) B2948531
theorem B2487829 : Blo 1965435 2487829 := bbase (se 6 (by rfl) ⟨58308, by rfl⟩ : syracuseStep 2487829 = 116617) (by norm_num)
theorem B3317105 : Blo 1965435 3317105 := bstep (se 2 (by rfl) ⟨1243914, by rfl⟩ : syracuseStep 3317105 = 2487829) B2487829
theorem B2211403 : Blo 1965435 2211403 := bstep (se 1 (by rfl) ⟨1658552, by rfl⟩ : syracuseStep 2211403 = 3317105) B3317105
theorem B2948537 : Blo 1965435 2948537 := bstep (se 2 (by rfl) ⟨1105701, by rfl⟩ : syracuseStep 2948537 = 2211403) B2211403
theorem B1965691 : Blo 1965435 1965691 := bstep (se 1 (by rfl) ⟨1474268, by rfl⟩ : syracuseStep 1965691 = 2948537) B2948537
theorem B14756885 : Blo 1965435 14756885 := bbase (se 6 (by rfl) ⟨345864, by rfl⟩ : syracuseStep 14756885 = 691729) (by norm_num)
theorem B157406773 : Blo 1965435 157406773 := bstep (se 5 (by rfl) ⟨7378442, by rfl⟩ : syracuseStep 157406773 = 14756885) B14756885
theorem B209875697 : Blo 1965435 209875697 := bstep (se 2 (by rfl) ⟨78703386, by rfl⟩ : syracuseStep 209875697 = 157406773) B157406773
theorem B139917131 : Blo 1965435 139917131 := bstep (se 1 (by rfl) ⟨104937848, by rfl⟩ : syracuseStep 139917131 = 209875697) B209875697
theorem B93278087 : Blo 1965435 93278087 := bstep (se 1 (by rfl) ⟨69958565, by rfl⟩ : syracuseStep 93278087 = 139917131) B139917131
theorem B62185391 : Blo 1965435 62185391 := bstep (se 1 (by rfl) ⟨46639043, by rfl⟩ : syracuseStep 62185391 = 93278087) B93278087
theorem B41456927 : Blo 1965435 41456927 := bstep (se 1 (by rfl) ⟨31092695, by rfl⟩ : syracuseStep 41456927 = 62185391) B62185391
theorem B27637951 : Blo 1965435 27637951 := bstep (se 1 (by rfl) ⟨20728463, by rfl⟩ : syracuseStep 27637951 = 41456927) B41456927
theorem B36850601 : Blo 1965435 36850601 := bstep (se 2 (by rfl) ⟨13818975, by rfl⟩ : syracuseStep 36850601 = 27637951) B27637951
theorem B24567067 : Blo 1965435 24567067 := bstep (se 1 (by rfl) ⟨18425300, by rfl⟩ : syracuseStep 24567067 = 36850601) B36850601
theorem B32756089 : Blo 1965435 32756089 := bstep (se 2 (by rfl) ⟨12283533, by rfl⟩ : syracuseStep 32756089 = 24567067) B24567067
theorem B43674785 : Blo 1965435 43674785 := bstep (se 2 (by rfl) ⟨16378044, by rfl⟩ : syracuseStep 43674785 = 32756089) B32756089
theorem B29116523 : Blo 1965435 29116523 := bstep (se 1 (by rfl) ⟨21837392, by rfl⟩ : syracuseStep 29116523 = 43674785) B43674785
theorem B19411015 : Blo 1965435 19411015 := bstep (se 1 (by rfl) ⟨14558261, by rfl⟩ : syracuseStep 19411015 = 29116523) B29116523
theorem B25881353 : Blo 1965435 25881353 := bstep (se 2 (by rfl) ⟨9705507, by rfl⟩ : syracuseStep 25881353 = 19411015) B19411015
theorem B17254235 : Blo 1965435 17254235 := bstep (se 1 (by rfl) ⟨12940676, by rfl⟩ : syracuseStep 17254235 = 25881353) B25881353
theorem B11502823 : Blo 1965435 11502823 := bstep (se 1 (by rfl) ⟨8627117, by rfl⟩ : syracuseStep 11502823 = 17254235) B17254235
theorem B15337097 : Blo 1965435 15337097 := bstep (se 2 (by rfl) ⟨5751411, by rfl⟩ : syracuseStep 15337097 = 11502823) B11502823
theorem B10224731 : Blo 1965435 10224731 := bstep (se 1 (by rfl) ⟨7668548, by rfl⟩ : syracuseStep 10224731 = 15337097) B15337097
theorem B6816487 : Blo 1965435 6816487 := bstep (se 1 (by rfl) ⟨5112365, by rfl⟩ : syracuseStep 6816487 = 10224731) B10224731
theorem B9088649 : Blo 1965435 9088649 := bstep (se 2 (by rfl) ⟨3408243, by rfl⟩ : syracuseStep 9088649 = 6816487) B6816487
theorem B6059099 : Blo 1965435 6059099 := bstep (se 1 (by rfl) ⟨4544324, by rfl⟩ : syracuseStep 6059099 = 9088649) B9088649
theorem B4039399 : Blo 1965435 4039399 := bstep (se 1 (by rfl) ⟨3029549, by rfl⟩ : syracuseStep 4039399 = 6059099) B6059099
theorem B5385865 : Blo 1965435 5385865 := bstep (se 2 (by rfl) ⟨2019699, by rfl⟩ : syracuseStep 5385865 = 4039399) B4039399
theorem B7181153 : Blo 1965435 7181153 := bstep (se 2 (by rfl) ⟨2692932, by rfl⟩ : syracuseStep 7181153 = 5385865) B5385865
theorem B4787435 : Blo 1965435 4787435 := bstep (se 1 (by rfl) ⟨3590576, by rfl⟩ : syracuseStep 4787435 = 7181153) B7181153
theorem B12766493 : Blo 1965435 12766493 := bstep (se 3 (by rfl) ⟨2393717, by rfl⟩ : syracuseStep 12766493 = 4787435) B4787435
theorem B34043981 : Blo 1965435 34043981 := bstep (se 3 (by rfl) ⟨6383246, by rfl⟩ : syracuseStep 34043981 = 12766493) B12766493
theorem B90783949 : Blo 1965435 90783949 := bstep (se 3 (by rfl) ⟨17021990, by rfl⟩ : syracuseStep 90783949 = 34043981) B34043981
theorem B121045265 : Blo 1965435 121045265 := bstep (se 2 (by rfl) ⟨45391974, by rfl⟩ : syracuseStep 121045265 = 90783949) B90783949
theorem B80696843 : Blo 1965435 80696843 := bstep (se 1 (by rfl) ⟨60522632, by rfl⟩ : syracuseStep 80696843 = 121045265) B121045265
theorem B53797895 : Blo 1965435 53797895 := bstep (se 1 (by rfl) ⟨40348421, by rfl⟩ : syracuseStep 53797895 = 80696843) B80696843
theorem B35865263 : Blo 1965435 35865263 := bstep (se 1 (by rfl) ⟨26898947, by rfl⟩ : syracuseStep 35865263 = 53797895) B53797895
theorem B23910175 : Blo 1965435 23910175 := bstep (se 1 (by rfl) ⟨17932631, by rfl⟩ : syracuseStep 23910175 = 35865263) B35865263
theorem B31880233 : Blo 1965435 31880233 := bstep (se 2 (by rfl) ⟨11955087, by rfl⟩ : syracuseStep 31880233 = 23910175) B23910175
theorem B42506977 : Blo 1965435 42506977 := bstep (se 2 (by rfl) ⟨15940116, by rfl⟩ : syracuseStep 42506977 = 31880233) B31880233
theorem B56675969 : Blo 1965435 56675969 := bstep (se 2 (by rfl) ⟨21253488, by rfl⟩ : syracuseStep 56675969 = 42506977) B42506977
theorem B37783979 : Blo 1965435 37783979 := bstep (se 1 (by rfl) ⟨28337984, by rfl⟩ : syracuseStep 37783979 = 56675969) B56675969
theorem B25189319 : Blo 1965435 25189319 := bstep (se 1 (by rfl) ⟨18891989, by rfl⟩ : syracuseStep 25189319 = 37783979) B37783979
theorem B16792879 : Blo 1965435 16792879 := bstep (se 1 (by rfl) ⟨12594659, by rfl⟩ : syracuseStep 16792879 = 25189319) B25189319
theorem B22390505 : Blo 1965435 22390505 := bstep (se 2 (by rfl) ⟨8396439, by rfl⟩ : syracuseStep 22390505 = 16792879) B16792879
theorem B14927003 : Blo 1965435 14927003 := bstep (se 1 (by rfl) ⟨11195252, by rfl⟩ : syracuseStep 14927003 = 22390505) B22390505
theorem B9951335 : Blo 1965435 9951335 := bstep (se 1 (by rfl) ⟨7463501, by rfl⟩ : syracuseStep 9951335 = 14927003) B14927003
theorem B6634223 : Blo 1965435 6634223 := bstep (se 1 (by rfl) ⟨4975667, by rfl⟩ : syracuseStep 6634223 = 9951335) B9951335
theorem B4422815 : Blo 1965435 4422815 := bstep (se 1 (by rfl) ⟨3317111, by rfl⟩ : syracuseStep 4422815 = 6634223) B6634223
theorem B2948543 : Blo 1965435 2948543 := bstep (se 1 (by rfl) ⟨2211407, by rfl⟩ : syracuseStep 2948543 = 4422815) B4422815
theorem B1965695 : Blo 1965435 1965695 := bstep (se 1 (by rfl) ⟨1474271, by rfl⟩ : syracuseStep 1965695 = 2948543) B2948543
theorem B2948549 : Blo 1965435 2948549 := bbase (se 4 (by rfl) ⟨276426, by rfl⟩ : syracuseStep 2948549 = 552853) (by norm_num)
theorem B1965699 : Blo 1965435 1965699 := bstep (se 1 (by rfl) ⟨1474274, by rfl⟩ : syracuseStep 1965699 = 2948549) B2948549
theorem B3317125 : Blo 1965435 3317125 := bbase (se 4 (by rfl) ⟨310980, by rfl⟩ : syracuseStep 3317125 = 621961) (by norm_num)
theorem B4422833 : Blo 1965435 4422833 := bstep (se 2 (by rfl) ⟨1658562, by rfl⟩ : syracuseStep 4422833 = 3317125) B3317125
theorem B2948555 : Blo 1965435 2948555 := bstep (se 1 (by rfl) ⟨2211416, by rfl⟩ : syracuseStep 2948555 = 4422833) B4422833
theorem B1965703 : Blo 1965435 1965703 := bstep (se 1 (by rfl) ⟨1474277, by rfl⟩ : syracuseStep 1965703 = 2948555) B2948555
theorem B2211421 : Blo 1965435 2211421 := bbase (se 3 (by rfl) ⟨414641, by rfl⟩ : syracuseStep 2211421 = 829283) (by norm_num)
theorem B2948561 : Blo 1965435 2948561 := bstep (se 2 (by rfl) ⟨1105710, by rfl⟩ : syracuseStep 2948561 = 2211421) B2211421
theorem B1965707 : Blo 1965435 1965707 := bstep (se 1 (by rfl) ⟨1474280, by rfl⟩ : syracuseStep 1965707 = 2948561) B2948561
theorem B6634277 : Blo 1965435 6634277 := bbase (se 4 (by rfl) ⟨621963, by rfl⟩ : syracuseStep 6634277 = 1243927) (by norm_num)
theorem B4422851 : Blo 1965435 4422851 := bstep (se 1 (by rfl) ⟨3317138, by rfl⟩ : syracuseStep 4422851 = 6634277) B6634277
theorem B2948567 : Blo 1965435 2948567 := bstep (se 1 (by rfl) ⟨2211425, by rfl⟩ : syracuseStep 2948567 = 4422851) B4422851
theorem B1965711 : Blo 1965435 1965711 := bstep (se 1 (by rfl) ⟨1474283, by rfl⟩ : syracuseStep 1965711 = 2948567) B2948567
theorem B2948573 : Blo 1965435 2948573 := bbase (se 3 (by rfl) ⟨552857, by rfl⟩ : syracuseStep 2948573 = 1105715) (by norm_num)
theorem B1965715 : Blo 1965435 1965715 := bstep (se 1 (by rfl) ⟨1474286, by rfl⟩ : syracuseStep 1965715 = 2948573) B2948573
theorem B4422869 : Blo 1965435 4422869 := bbase (se 7 (by rfl) ⟨51830, by rfl⟩ : syracuseStep 4422869 = 103661) (by norm_num)
theorem B2948579 : Blo 1965435 2948579 := bstep (se 1 (by rfl) ⟨2211434, by rfl⟩ : syracuseStep 2948579 = 4422869) B4422869
theorem B1965719 : Blo 1965435 1965719 := bstep (se 1 (by rfl) ⟨1474289, by rfl⟩ : syracuseStep 1965719 = 2948579) B2948579
theorem B2361533 : Blo 1965435 2361533 := bbase (se 3 (by rfl) ⟨442787, by rfl⟩ : syracuseStep 2361533 = 885575) (by norm_num)
theorem B6297421 : Blo 1965435 6297421 := bstep (se 3 (by rfl) ⟨1180766, by rfl⟩ : syracuseStep 6297421 = 2361533) B2361533
theorem B8396561 : Blo 1965435 8396561 := bstep (se 2 (by rfl) ⟨3148710, by rfl⟩ : syracuseStep 8396561 = 6297421) B6297421
theorem B5597707 : Blo 1965435 5597707 := bstep (se 1 (by rfl) ⟨4198280, by rfl⟩ : syracuseStep 5597707 = 8396561) B8396561
theorem B7463609 : Blo 1965435 7463609 := bstep (se 2 (by rfl) ⟨2798853, by rfl⟩ : syracuseStep 7463609 = 5597707) B5597707
theorem B4975739 : Blo 1965435 4975739 := bstep (se 1 (by rfl) ⟨3731804, by rfl⟩ : syracuseStep 4975739 = 7463609) B7463609
theorem B3317159 : Blo 1965435 3317159 := bstep (se 1 (by rfl) ⟨2487869, by rfl⟩ : syracuseStep 3317159 = 4975739) B4975739
theorem B2211439 : Blo 1965435 2211439 := bstep (se 1 (by rfl) ⟨1658579, by rfl⟩ : syracuseStep 2211439 = 3317159) B3317159
theorem B2948585 : Blo 1965435 2948585 := bstep (se 2 (by rfl) ⟨1105719, by rfl⟩ : syracuseStep 2948585 = 2211439) B2211439
theorem B1965723 : Blo 1965435 1965723 := bstep (se 1 (by rfl) ⟨1474292, by rfl⟩ : syracuseStep 1965723 = 2948585) B2948585
theorem B9446149 : Blo 1965435 9446149 := bbase (se 4 (by rfl) ⟨885576, by rfl⟩ : syracuseStep 9446149 = 1771153) (by norm_num)
theorem B12594865 : Blo 1965435 12594865 := bstep (se 2 (by rfl) ⟨4723074, by rfl⟩ : syracuseStep 12594865 = 9446149) B9446149
theorem B16793153 : Blo 1965435 16793153 := bstep (se 2 (by rfl) ⟨6297432, by rfl⟩ : syracuseStep 16793153 = 12594865) B12594865
theorem B11195435 : Blo 1965435 11195435 := bstep (se 1 (by rfl) ⟨8396576, by rfl⟩ : syracuseStep 11195435 = 16793153) B16793153
theorem B7463623 : Blo 1965435 7463623 := bstep (se 1 (by rfl) ⟨5597717, by rfl⟩ : syracuseStep 7463623 = 11195435) B11195435
theorem B9951497 : Blo 1965435 9951497 := bstep (se 2 (by rfl) ⟨3731811, by rfl⟩ : syracuseStep 9951497 = 7463623) B7463623
theorem B6634331 : Blo 1965435 6634331 := bstep (se 1 (by rfl) ⟨4975748, by rfl⟩ : syracuseStep 6634331 = 9951497) B9951497
theorem B4422887 : Blo 1965435 4422887 := bstep (se 1 (by rfl) ⟨3317165, by rfl⟩ : syracuseStep 4422887 = 6634331) B6634331
theorem B2948591 : Blo 1965435 2948591 := bstep (se 1 (by rfl) ⟨2211443, by rfl⟩ : syracuseStep 2948591 = 4422887) B4422887
theorem B1965727 : Blo 1965435 1965727 := bstep (se 1 (by rfl) ⟨1474295, by rfl⟩ : syracuseStep 1965727 = 2948591) B2948591
theorem B2948597 : Blo 1965435 2948597 := bbase (se 5 (by rfl) ⟨138215, by rfl⟩ : syracuseStep 2948597 = 276431) (by norm_num)
theorem B1965731 : Blo 1965435 1965731 := bstep (se 1 (by rfl) ⟨1474298, by rfl⟩ : syracuseStep 1965731 = 2948597) B2948597
theorem B2099153 : Blo 1965435 2099153 := bbase (se 2 (by rfl) ⟨787182, by rfl⟩ : syracuseStep 2099153 = 1574365) (by norm_num)
theorem B5597741 : Blo 1965435 5597741 := bstep (se 3 (by rfl) ⟨1049576, by rfl⟩ : syracuseStep 5597741 = 2099153) B2099153
theorem B3731827 : Blo 1965435 3731827 := bstep (se 1 (by rfl) ⟨2798870, by rfl⟩ : syracuseStep 3731827 = 5597741) B5597741
theorem B4975769 : Blo 1965435 4975769 := bstep (se 2 (by rfl) ⟨1865913, by rfl⟩ : syracuseStep 4975769 = 3731827) B3731827
theorem B3317179 : Blo 1965435 3317179 := bstep (se 1 (by rfl) ⟨2487884, by rfl⟩ : syracuseStep 3317179 = 4975769) B4975769
theorem B4422905 : Blo 1965435 4422905 := bstep (se 2 (by rfl) ⟨1658589, by rfl⟩ : syracuseStep 4422905 = 3317179) B3317179
theorem B2948603 : Blo 1965435 2948603 := bstep (se 1 (by rfl) ⟨2211452, by rfl⟩ : syracuseStep 2948603 = 4422905) B4422905
theorem B1965735 : Blo 1965435 1965735 := bstep (se 1 (by rfl) ⟨1474301, by rfl⟩ : syracuseStep 1965735 = 2948603) B2948603
theorem B2211457 : Blo 1965435 2211457 := bbase (se 2 (by rfl) ⟨829296, by rfl⟩ : syracuseStep 2211457 = 1658593) (by norm_num)
theorem B2948609 : Blo 1965435 2948609 := bstep (se 2 (by rfl) ⟨1105728, by rfl⟩ : syracuseStep 2948609 = 2211457) B2211457
theorem B1965739 : Blo 1965435 1965739 := bstep (se 1 (by rfl) ⟨1474304, by rfl⟩ : syracuseStep 1965739 = 2948609) B2948609
theorem B4975789 : Blo 1965435 4975789 := bbase (se 3 (by rfl) ⟨932960, by rfl⟩ : syracuseStep 4975789 = 1865921) (by norm_num)
theorem B6634385 : Blo 1965435 6634385 := bstep (se 2 (by rfl) ⟨2487894, by rfl⟩ : syracuseStep 6634385 = 4975789) B4975789
theorem B4422923 : Blo 1965435 4422923 := bstep (se 1 (by rfl) ⟨3317192, by rfl⟩ : syracuseStep 4422923 = 6634385) B6634385
theorem B2948615 : Blo 1965435 2948615 := bstep (se 1 (by rfl) ⟨2211461, by rfl⟩ : syracuseStep 2948615 = 4422923) B4422923
theorem B1965743 : Blo 1965435 1965743 := bstep (se 1 (by rfl) ⟨1474307, by rfl⟩ : syracuseStep 1965743 = 2948615) B2948615
theorem B2948621 : Blo 1965435 2948621 := bbase (se 3 (by rfl) ⟨552866, by rfl⟩ : syracuseStep 2948621 = 1105733) (by norm_num)
theorem B1965747 : Blo 1965435 1965747 := bstep (se 1 (by rfl) ⟨1474310, by rfl⟩ : syracuseStep 1965747 = 2948621) B2948621
theorem B4422941 : Blo 1965435 4422941 := bbase (se 3 (by rfl) ⟨829301, by rfl⟩ : syracuseStep 4422941 = 1658603) (by norm_num)
theorem B2948627 : Blo 1965435 2948627 := bstep (se 1 (by rfl) ⟨2211470, by rfl⟩ : syracuseStep 2948627 = 4422941) B4422941
theorem B1965751 : Blo 1965435 1965751 := bstep (se 1 (by rfl) ⟨1474313, by rfl⟩ : syracuseStep 1965751 = 2948627) B2948627
theorem B3317213 : Blo 1965435 3317213 := bbase (se 3 (by rfl) ⟨621977, by rfl⟩ : syracuseStep 3317213 = 1243955) (by norm_num)
theorem B2211475 : Blo 1965435 2211475 := bstep (se 1 (by rfl) ⟨1658606, by rfl⟩ : syracuseStep 2211475 = 3317213) B3317213
theorem B2948633 : Blo 1965435 2948633 := bstep (se 2 (by rfl) ⟨1105737, by rfl⟩ : syracuseStep 2948633 = 2211475) B2211475
theorem B1965755 : Blo 1965435 1965755 := bstep (se 1 (by rfl) ⟨1474316, by rfl⟩ : syracuseStep 1965755 = 2948633) B2948633
theorem B4255637 : Blo 1965435 4255637 := bbase (se 6 (by rfl) ⟨99741, by rfl⟩ : syracuseStep 4255637 = 199483) (by norm_num)
theorem B11348365 : Blo 1965435 11348365 := bstep (se 3 (by rfl) ⟨2127818, by rfl⟩ : syracuseStep 11348365 = 4255637) B4255637
theorem B15131153 : Blo 1965435 15131153 := bstep (se 2 (by rfl) ⟨5674182, by rfl⟩ : syracuseStep 15131153 = 11348365) B11348365
theorem B10087435 : Blo 1965435 10087435 := bstep (se 1 (by rfl) ⟨7565576, by rfl⟩ : syracuseStep 10087435 = 15131153) B15131153
theorem B53799653 : Blo 1965435 53799653 := bstep (se 4 (by rfl) ⟨5043717, by rfl⟩ : syracuseStep 53799653 = 10087435) B10087435
theorem B35866435 : Blo 1965435 35866435 := bstep (se 1 (by rfl) ⟨26899826, by rfl⟩ : syracuseStep 35866435 = 53799653) B53799653
theorem B47821913 : Blo 1965435 47821913 := bstep (se 2 (by rfl) ⟨17933217, by rfl⟩ : syracuseStep 47821913 = 35866435) B35866435
theorem B31881275 : Blo 1965435 31881275 := bstep (se 1 (by rfl) ⟨23910956, by rfl⟩ : syracuseStep 31881275 = 47821913) B47821913
theorem B21254183 : Blo 1965435 21254183 := bstep (se 1 (by rfl) ⟨15940637, by rfl⟩ : syracuseStep 21254183 = 31881275) B31881275
theorem B14169455 : Blo 1965435 14169455 := bstep (se 1 (by rfl) ⟨10627091, by rfl⟩ : syracuseStep 14169455 = 21254183) B21254183
theorem B9446303 : Blo 1965435 9446303 := bstep (se 1 (by rfl) ⟨7084727, by rfl⟩ : syracuseStep 9446303 = 14169455) B14169455
theorem B6297535 : Blo 1965435 6297535 := bstep (se 1 (by rfl) ⟨4723151, by rfl⟩ : syracuseStep 6297535 = 9446303) B9446303
theorem B8396713 : Blo 1965435 8396713 := bstep (se 2 (by rfl) ⟨3148767, by rfl⟩ : syracuseStep 8396713 = 6297535) B6297535
theorem B11195617 : Blo 1965435 11195617 := bstep (se 2 (by rfl) ⟨4198356, by rfl⟩ : syracuseStep 11195617 = 8396713) B8396713
theorem B14927489 : Blo 1965435 14927489 := bstep (se 2 (by rfl) ⟨5597808, by rfl⟩ : syracuseStep 14927489 = 11195617) B11195617
theorem B9951659 : Blo 1965435 9951659 := bstep (se 1 (by rfl) ⟨7463744, by rfl⟩ : syracuseStep 9951659 = 14927489) B14927489
theorem B6634439 : Blo 1965435 6634439 := bstep (se 1 (by rfl) ⟨4975829, by rfl⟩ : syracuseStep 6634439 = 9951659) B9951659
theorem B4422959 : Blo 1965435 4422959 := bstep (se 1 (by rfl) ⟨3317219, by rfl⟩ : syracuseStep 4422959 = 6634439) B6634439
theorem B2948639 : Blo 1965435 2948639 := bstep (se 1 (by rfl) ⟨2211479, by rfl⟩ : syracuseStep 2948639 = 4422959) B4422959
theorem B1965759 : Blo 1965435 1965759 := bstep (se 1 (by rfl) ⟨1474319, by rfl⟩ : syracuseStep 1965759 = 2948639) B2948639
theorem B2948645 : Blo 1965435 2948645 := bbase (se 4 (by rfl) ⟨276435, by rfl⟩ : syracuseStep 2948645 = 552871) (by norm_num)
theorem B1965763 : Blo 1965435 1965763 := bstep (se 1 (by rfl) ⟨1474322, by rfl⟩ : syracuseStep 1965763 = 2948645) B2948645
theorem B2487925 : Blo 1965435 2487925 := bbase (se 5 (by rfl) ⟨116621, by rfl⟩ : syracuseStep 2487925 = 233243) (by norm_num)
theorem B3317233 : Blo 1965435 3317233 := bstep (se 2 (by rfl) ⟨1243962, by rfl⟩ : syracuseStep 3317233 = 2487925) B2487925
theorem B4422977 : Blo 1965435 4422977 := bstep (se 2 (by rfl) ⟨1658616, by rfl⟩ : syracuseStep 4422977 = 3317233) B3317233
theorem B2948651 : Blo 1965435 2948651 := bstep (se 1 (by rfl) ⟨2211488, by rfl⟩ : syracuseStep 2948651 = 4422977) B4422977
theorem B1965767 : Blo 1965435 1965767 := bstep (se 1 (by rfl) ⟨1474325, by rfl⟩ : syracuseStep 1965767 = 2948651) B2948651
theorem B2211493 : Blo 1965435 2211493 := bbase (se 4 (by rfl) ⟨207327, by rfl⟩ : syracuseStep 2211493 = 414655) (by norm_num)
theorem B2948657 : Blo 1965435 2948657 := bstep (se 2 (by rfl) ⟨1105746, by rfl⟩ : syracuseStep 2948657 = 2211493) B2211493
theorem B1965771 : Blo 1965435 1965771 := bstep (se 1 (by rfl) ⟨1474328, by rfl⟩ : syracuseStep 1965771 = 2948657) B2948657
theorem B2303257 : Blo 1965435 2303257 := bbase (se 2 (by rfl) ⟨863721, by rfl⟩ : syracuseStep 2303257 = 1727443) (by norm_num)
theorem B49136149 : Blo 1965435 49136149 := bstep (se 6 (by rfl) ⟨1151628, by rfl⟩ : syracuseStep 49136149 = 2303257) B2303257
theorem B65514865 : Blo 1965435 65514865 := bstep (se 2 (by rfl) ⟨24568074, by rfl⟩ : syracuseStep 65514865 = 49136149) B49136149
theorem B87353153 : Blo 1965435 87353153 := bstep (se 2 (by rfl) ⟨32757432, by rfl⟩ : syracuseStep 87353153 = 65514865) B65514865
theorem B58235435 : Blo 1965435 58235435 := bstep (se 1 (by rfl) ⟨43676576, by rfl⟩ : syracuseStep 58235435 = 87353153) B87353153
theorem B38823623 : Blo 1965435 38823623 := bstep (se 1 (by rfl) ⟨29117717, by rfl⟩ : syracuseStep 38823623 = 58235435) B58235435
theorem B25882415 : Blo 1965435 25882415 := bstep (se 1 (by rfl) ⟨19411811, by rfl⟩ : syracuseStep 25882415 = 38823623) B38823623
theorem B17254943 : Blo 1965435 17254943 := bstep (se 1 (by rfl) ⟨12941207, by rfl⟩ : syracuseStep 17254943 = 25882415) B25882415
theorem B11503295 : Blo 1965435 11503295 := bstep (se 1 (by rfl) ⟨8627471, by rfl⟩ : syracuseStep 11503295 = 17254943) B17254943
theorem B7668863 : Blo 1965435 7668863 := bstep (se 1 (by rfl) ⟨5751647, by rfl⟩ : syracuseStep 7668863 = 11503295) B11503295
theorem B5112575 : Blo 1965435 5112575 := bstep (se 1 (by rfl) ⟨3834431, by rfl⟩ : syracuseStep 5112575 = 7668863) B7668863
theorem B3408383 : Blo 1965435 3408383 := bstep (se 1 (by rfl) ⟨2556287, by rfl⟩ : syracuseStep 3408383 = 5112575) B5112575
theorem B2272255 : Blo 1965435 2272255 := bstep (se 1 (by rfl) ⟨1704191, by rfl⟩ : syracuseStep 2272255 = 3408383) B3408383
theorem B48474773 : Blo 1965435 48474773 := bstep (se 6 (by rfl) ⟨1136127, by rfl⟩ : syracuseStep 48474773 = 2272255) B2272255
theorem B32316515 : Blo 1965435 32316515 := bstep (se 1 (by rfl) ⟨24237386, by rfl⟩ : syracuseStep 32316515 = 48474773) B48474773
theorem B21544343 : Blo 1965435 21544343 := bstep (se 1 (by rfl) ⟨16158257, by rfl⟩ : syracuseStep 21544343 = 32316515) B32316515
theorem B14362895 : Blo 1965435 14362895 := bstep (se 1 (by rfl) ⟨10772171, by rfl⟩ : syracuseStep 14362895 = 21544343) B21544343
theorem B9575263 : Blo 1965435 9575263 := bstep (se 1 (by rfl) ⟨7181447, by rfl⟩ : syracuseStep 9575263 = 14362895) B14362895
theorem B51068069 : Blo 1965435 51068069 := bstep (se 4 (by rfl) ⟨4787631, by rfl⟩ : syracuseStep 51068069 = 9575263) B9575263
theorem B34045379 : Blo 1965435 34045379 := bstep (se 1 (by rfl) ⟨25534034, by rfl⟩ : syracuseStep 34045379 = 51068069) B51068069
theorem B22696919 : Blo 1965435 22696919 := bstep (se 1 (by rfl) ⟨17022689, by rfl⟩ : syracuseStep 22696919 = 34045379) B34045379
theorem B15131279 : Blo 1965435 15131279 := bstep (se 1 (by rfl) ⟨11348459, by rfl⟩ : syracuseStep 15131279 = 22696919) B22696919
theorem B10087519 : Blo 1965435 10087519 := bstep (se 1 (by rfl) ⟨7565639, by rfl⟩ : syracuseStep 10087519 = 15131279) B15131279
theorem B13450025 : Blo 1965435 13450025 := bstep (se 2 (by rfl) ⟨5043759, by rfl⟩ : syracuseStep 13450025 = 10087519) B10087519
theorem B8966683 : Blo 1965435 8966683 := bstep (se 1 (by rfl) ⟨6725012, by rfl⟩ : syracuseStep 8966683 = 13450025) B13450025
theorem B47822309 : Blo 1965435 47822309 := bstep (se 4 (by rfl) ⟨4483341, by rfl⟩ : syracuseStep 47822309 = 8966683) B8966683
theorem B31881539 : Blo 1965435 31881539 := bstep (se 1 (by rfl) ⟨23911154, by rfl⟩ : syracuseStep 31881539 = 47822309) B47822309
theorem B21254359 : Blo 1965435 21254359 := bstep (se 1 (by rfl) ⟨15940769, by rfl⟩ : syracuseStep 21254359 = 31881539) B31881539
theorem B28339145 : Blo 1965435 28339145 := bstep (se 2 (by rfl) ⟨10627179, by rfl⟩ : syracuseStep 28339145 = 21254359) B21254359
theorem B18892763 : Blo 1965435 18892763 := bstep (se 1 (by rfl) ⟨14169572, by rfl⟩ : syracuseStep 18892763 = 28339145) B28339145
theorem B12595175 : Blo 1965435 12595175 := bstep (se 1 (by rfl) ⟨9446381, by rfl⟩ : syracuseStep 12595175 = 18892763) B18892763
theorem B8396783 : Blo 1965435 8396783 := bstep (se 1 (by rfl) ⟨6297587, by rfl⟩ : syracuseStep 8396783 = 12595175) B12595175
theorem B5597855 : Blo 1965435 5597855 := bstep (se 1 (by rfl) ⟨4198391, by rfl⟩ : syracuseStep 5597855 = 8396783) B8396783
theorem B3731903 : Blo 1965435 3731903 := bstep (se 1 (by rfl) ⟨2798927, by rfl⟩ : syracuseStep 3731903 = 5597855) B5597855
theorem B2487935 : Blo 1965435 2487935 := bstep (se 1 (by rfl) ⟨1865951, by rfl⟩ : syracuseStep 2487935 = 3731903) B3731903
theorem B6634493 : Blo 1965435 6634493 := bstep (se 3 (by rfl) ⟨1243967, by rfl⟩ : syracuseStep 6634493 = 2487935) B2487935
theorem B4422995 : Blo 1965435 4422995 := bstep (se 1 (by rfl) ⟨3317246, by rfl⟩ : syracuseStep 4422995 = 6634493) B6634493
theorem B2948663 : Blo 1965435 2948663 := bstep (se 1 (by rfl) ⟨2211497, by rfl⟩ : syracuseStep 2948663 = 4422995) B4422995
theorem B1965775 : Blo 1965435 1965775 := bstep (se 1 (by rfl) ⟨1474331, by rfl⟩ : syracuseStep 1965775 = 2948663) B2948663
theorem B2948669 : Blo 1965435 2948669 := bbase (se 3 (by rfl) ⟨552875, by rfl⟩ : syracuseStep 2948669 = 1105751) (by norm_num)
theorem B1965779 : Blo 1965435 1965779 := bstep (se 1 (by rfl) ⟨1474334, by rfl⟩ : syracuseStep 1965779 = 2948669) B2948669
theorem B4423013 : Blo 1965435 4423013 := bbase (se 4 (by rfl) ⟨414657, by rfl⟩ : syracuseStep 4423013 = 829315) (by norm_num)
theorem B2948675 : Blo 1965435 2948675 := bstep (se 1 (by rfl) ⟨2211506, by rfl⟩ : syracuseStep 2948675 = 4423013) B4423013
theorem B1965783 : Blo 1965435 1965783 := bstep (se 1 (by rfl) ⟨1474337, by rfl⟩ : syracuseStep 1965783 = 2948675) B2948675
theorem B4975901 : Blo 1965435 4975901 := bbase (se 3 (by rfl) ⟨932981, by rfl⟩ : syracuseStep 4975901 = 1865963) (by norm_num)
theorem B3317267 : Blo 1965435 3317267 := bstep (se 1 (by rfl) ⟨2487950, by rfl⟩ : syracuseStep 3317267 = 4975901) B4975901
theorem B2211511 : Blo 1965435 2211511 := bstep (se 1 (by rfl) ⟨1658633, by rfl⟩ : syracuseStep 2211511 = 3317267) B3317267
theorem B2948681 : Blo 1965435 2948681 := bstep (se 2 (by rfl) ⟨1105755, by rfl⟩ : syracuseStep 2948681 = 2211511) B2211511
theorem B1965787 : Blo 1965435 1965787 := bstep (se 1 (by rfl) ⟨1474340, by rfl⟩ : syracuseStep 1965787 = 2948681) B2948681
theorem B3731933 : Blo 1965435 3731933 := bbase (se 3 (by rfl) ⟨699737, by rfl⟩ : syracuseStep 3731933 = 1399475) (by norm_num)
theorem B9951821 : Blo 1965435 9951821 := bstep (se 3 (by rfl) ⟨1865966, by rfl⟩ : syracuseStep 9951821 = 3731933) B3731933
theorem B6634547 : Blo 1965435 6634547 := bstep (se 1 (by rfl) ⟨4975910, by rfl⟩ : syracuseStep 6634547 = 9951821) B9951821
theorem B4423031 : Blo 1965435 4423031 := bstep (se 1 (by rfl) ⟨3317273, by rfl⟩ : syracuseStep 4423031 = 6634547) B6634547
theorem B2948687 : Blo 1965435 2948687 := bstep (se 1 (by rfl) ⟨2211515, by rfl⟩ : syracuseStep 2948687 = 4423031) B4423031
theorem B1965791 : Blo 1965435 1965791 := bstep (se 1 (by rfl) ⟨1474343, by rfl⟩ : syracuseStep 1965791 = 2948687) B2948687
theorem B2948693 : Blo 1965435 2948693 := bbase (se 8 (by rfl) ⟨17277, by rfl⟩ : syracuseStep 2948693 = 34555) (by norm_num)
theorem B1965795 : Blo 1965435 1965795 := bstep (se 1 (by rfl) ⟨1474346, by rfl⟩ : syracuseStep 1965795 = 2948693) B2948693
theorem B8396885 : Blo 1965435 8396885 := bbase (se 8 (by rfl) ⟨49200, by rfl⟩ : syracuseStep 8396885 = 98401) (by norm_num)
theorem B5597923 : Blo 1965435 5597923 := bstep (se 1 (by rfl) ⟨4198442, by rfl⟩ : syracuseStep 5597923 = 8396885) B8396885
theorem B7463897 : Blo 1965435 7463897 := bstep (se 2 (by rfl) ⟨2798961, by rfl⟩ : syracuseStep 7463897 = 5597923) B5597923
theorem B4975931 : Blo 1965435 4975931 := bstep (se 1 (by rfl) ⟨3731948, by rfl⟩ : syracuseStep 4975931 = 7463897) B7463897
theorem B3317287 : Blo 1965435 3317287 := bstep (se 1 (by rfl) ⟨2487965, by rfl⟩ : syracuseStep 3317287 = 4975931) B4975931
theorem B4423049 : Blo 1965435 4423049 := bstep (se 2 (by rfl) ⟨1658643, by rfl⟩ : syracuseStep 4423049 = 3317287) B3317287
theorem B2948699 : Blo 1965435 2948699 := bstep (se 1 (by rfl) ⟨2211524, by rfl⟩ : syracuseStep 2948699 = 4423049) B4423049
theorem B1965799 : Blo 1965435 1965799 := bstep (se 1 (by rfl) ⟨1474349, by rfl⟩ : syracuseStep 1965799 = 2948699) B2948699
theorem B2211529 : Blo 1965435 2211529 := bbase (se 2 (by rfl) ⟨829323, by rfl⟩ : syracuseStep 2211529 = 1658647) (by norm_num)
theorem B2948705 : Blo 1965435 2948705 := bstep (se 2 (by rfl) ⟨1105764, by rfl⟩ : syracuseStep 2948705 = 2211529) B2211529
theorem B1965803 : Blo 1965435 1965803 := bstep (se 1 (by rfl) ⟨1474352, by rfl⟩ : syracuseStep 1965803 = 2948705) B2948705
theorem B7084901 : Blo 1965435 7084901 := bbase (se 4 (by rfl) ⟨664209, by rfl⟩ : syracuseStep 7084901 = 1328419) (by norm_num)
theorem B4723267 : Blo 1965435 4723267 := bstep (se 1 (by rfl) ⟨3542450, by rfl⟩ : syracuseStep 4723267 = 7084901) B7084901
theorem B6297689 : Blo 1965435 6297689 := bstep (se 2 (by rfl) ⟨2361633, by rfl⟩ : syracuseStep 6297689 = 4723267) B4723267
theorem B16793837 : Blo 1965435 16793837 := bstep (se 3 (by rfl) ⟨3148844, by rfl⟩ : syracuseStep 16793837 = 6297689) B6297689
theorem B11195891 : Blo 1965435 11195891 := bstep (se 1 (by rfl) ⟨8396918, by rfl⟩ : syracuseStep 11195891 = 16793837) B16793837
theorem B7463927 : Blo 1965435 7463927 := bstep (se 1 (by rfl) ⟨5597945, by rfl⟩ : syracuseStep 7463927 = 11195891) B11195891
theorem B4975951 : Blo 1965435 4975951 := bstep (se 1 (by rfl) ⟨3731963, by rfl⟩ : syracuseStep 4975951 = 7463927) B7463927
theorem B6634601 : Blo 1965435 6634601 := bstep (se 2 (by rfl) ⟨2487975, by rfl⟩ : syracuseStep 6634601 = 4975951) B4975951
theorem B4423067 : Blo 1965435 4423067 := bstep (se 1 (by rfl) ⟨3317300, by rfl⟩ : syracuseStep 4423067 = 6634601) B6634601
theorem B2948711 : Blo 1965435 2948711 := bstep (se 1 (by rfl) ⟨2211533, by rfl⟩ : syracuseStep 2948711 = 4423067) B4423067
theorem B1965807 : Blo 1965435 1965807 := bstep (se 1 (by rfl) ⟨1474355, by rfl⟩ : syracuseStep 1965807 = 2948711) B2948711
theorem B2948717 : Blo 1965435 2948717 := bbase (se 3 (by rfl) ⟨552884, by rfl⟩ : syracuseStep 2948717 = 1105769) (by norm_num)
theorem B1965811 : Blo 1965435 1965811 := bstep (se 1 (by rfl) ⟨1474358, by rfl⟩ : syracuseStep 1965811 = 2948717) B2948717
theorem B4423085 : Blo 1965435 4423085 := bbase (se 3 (by rfl) ⟨829328, by rfl⟩ : syracuseStep 4423085 = 1658657) (by norm_num)
theorem B2948723 : Blo 1965435 2948723 := bstep (se 1 (by rfl) ⟨2211542, by rfl⟩ : syracuseStep 2948723 = 4423085) B4423085
theorem B1965815 : Blo 1965435 1965815 := bstep (se 1 (by rfl) ⟨1474361, by rfl⟩ : syracuseStep 1965815 = 2948723) B2948723
theorem B2361649 : Blo 1965435 2361649 := bbase (se 2 (by rfl) ⟨885618, by rfl⟩ : syracuseStep 2361649 = 1771237) (by norm_num)
theorem B3148865 : Blo 1965435 3148865 := bstep (se 2 (by rfl) ⟨1180824, by rfl⟩ : syracuseStep 3148865 = 2361649) B2361649
theorem B2099243 : Blo 1965435 2099243 := bstep (se 1 (by rfl) ⟨1574432, by rfl⟩ : syracuseStep 2099243 = 3148865) B3148865
theorem B5597981 : Blo 1965435 5597981 := bstep (se 3 (by rfl) ⟨1049621, by rfl⟩ : syracuseStep 5597981 = 2099243) B2099243
theorem B3731987 : Blo 1965435 3731987 := bstep (se 1 (by rfl) ⟨2798990, by rfl⟩ : syracuseStep 3731987 = 5597981) B5597981
theorem B2487991 : Blo 1965435 2487991 := bstep (se 1 (by rfl) ⟨1865993, by rfl⟩ : syracuseStep 2487991 = 3731987) B3731987
theorem B3317321 : Blo 1965435 3317321 := bstep (se 2 (by rfl) ⟨1243995, by rfl⟩ : syracuseStep 3317321 = 2487991) B2487991
theorem B2211547 : Blo 1965435 2211547 := bstep (se 1 (by rfl) ⟨1658660, by rfl⟩ : syracuseStep 2211547 = 3317321) B3317321
theorem B2948729 : Blo 1965435 2948729 := bstep (se 2 (by rfl) ⟨1105773, by rfl⟩ : syracuseStep 2948729 = 2211547) B2211547
theorem B1965819 : Blo 1965435 1965819 := bstep (se 1 (by rfl) ⟨1474364, by rfl⟩ : syracuseStep 1965819 = 2948729) B2948729
theorem B21838805 : Blo 1965435 21838805 := bbase (se 7 (by rfl) ⟨255923, by rfl⟩ : syracuseStep 21838805 = 511847) (by norm_num)
theorem B14559203 : Blo 1965435 14559203 := bstep (se 1 (by rfl) ⟨10919402, by rfl⟩ : syracuseStep 14559203 = 21838805) B21838805
theorem B38824541 : Blo 1965435 38824541 := bstep (se 3 (by rfl) ⟨7279601, by rfl⟩ : syracuseStep 38824541 = 14559203) B14559203
theorem B25883027 : Blo 1965435 25883027 := bstep (se 1 (by rfl) ⟨19412270, by rfl⟩ : syracuseStep 25883027 = 38824541) B38824541
theorem B17255351 : Blo 1965435 17255351 := bstep (se 1 (by rfl) ⟨12941513, by rfl⟩ : syracuseStep 17255351 = 25883027) B25883027
theorem B11503567 : Blo 1965435 11503567 := bstep (se 1 (by rfl) ⟨8627675, by rfl⟩ : syracuseStep 11503567 = 17255351) B17255351
theorem B15338089 : Blo 1965435 15338089 := bstep (se 2 (by rfl) ⟨5751783, by rfl⟩ : syracuseStep 15338089 = 11503567) B11503567
theorem B20450785 : Blo 1965435 20450785 := bstep (se 2 (by rfl) ⟨7669044, by rfl⟩ : syracuseStep 20450785 = 15338089) B15338089
theorem B27267713 : Blo 1965435 27267713 := bstep (se 2 (by rfl) ⟨10225392, by rfl⟩ : syracuseStep 27267713 = 20450785) B20450785
theorem B18178475 : Blo 1965435 18178475 := bstep (se 1 (by rfl) ⟨13633856, by rfl⟩ : syracuseStep 18178475 = 27267713) B27267713
theorem B193903733 : Blo 1965435 193903733 := bstep (se 5 (by rfl) ⟨9089237, by rfl⟩ : syracuseStep 193903733 = 18178475) B18178475
theorem B129269155 : Blo 1965435 129269155 := bstep (se 1 (by rfl) ⟨96951866, by rfl⟩ : syracuseStep 129269155 = 193903733) B193903733
theorem B172358873 : Blo 1965435 172358873 := bstep (se 2 (by rfl) ⟨64634577, by rfl⟩ : syracuseStep 172358873 = 129269155) B129269155
theorem B114905915 : Blo 1965435 114905915 := bstep (se 1 (by rfl) ⟨86179436, by rfl⟩ : syracuseStep 114905915 = 172358873) B172358873
theorem B76603943 : Blo 1965435 76603943 := bstep (se 1 (by rfl) ⟨57452957, by rfl⟩ : syracuseStep 76603943 = 114905915) B114905915
theorem B51069295 : Blo 1965435 51069295 := bstep (se 1 (by rfl) ⟨38301971, by rfl⟩ : syracuseStep 51069295 = 76603943) B76603943
theorem B272369573 : Blo 1965435 272369573 := bstep (se 4 (by rfl) ⟨25534647, by rfl⟩ : syracuseStep 272369573 = 51069295) B51069295
theorem B181579715 : Blo 1965435 181579715 := bstep (se 1 (by rfl) ⟨136184786, by rfl⟩ : syracuseStep 181579715 = 272369573) B272369573
theorem B121053143 : Blo 1965435 121053143 := bstep (se 1 (by rfl) ⟨90789857, by rfl⟩ : syracuseStep 121053143 = 181579715) B181579715
theorem B80702095 : Blo 1965435 80702095 := bstep (se 1 (by rfl) ⟨60526571, by rfl⟩ : syracuseStep 80702095 = 121053143) B121053143
theorem B107602793 : Blo 1965435 107602793 := bstep (se 2 (by rfl) ⟨40351047, by rfl⟩ : syracuseStep 107602793 = 80702095) B80702095
theorem B71735195 : Blo 1965435 71735195 := bstep (se 1 (by rfl) ⟨53801396, by rfl⟩ : syracuseStep 71735195 = 107602793) B107602793
theorem B47823463 : Blo 1965435 47823463 := bstep (se 1 (by rfl) ⟨35867597, by rfl⟩ : syracuseStep 47823463 = 71735195) B71735195
theorem B63764617 : Blo 1965435 63764617 := bstep (se 2 (by rfl) ⟨23911731, by rfl⟩ : syracuseStep 63764617 = 47823463) B47823463
theorem B85019489 : Blo 1965435 85019489 := bstep (se 2 (by rfl) ⟨31882308, by rfl⟩ : syracuseStep 85019489 = 63764617) B63764617
theorem B56679659 : Blo 1965435 56679659 := bstep (se 1 (by rfl) ⟨42509744, by rfl⟩ : syracuseStep 56679659 = 85019489) B85019489
theorem B37786439 : Blo 1965435 37786439 := bstep (se 1 (by rfl) ⟨28339829, by rfl⟩ : syracuseStep 37786439 = 56679659) B56679659
theorem B25190959 : Blo 1965435 25190959 := bstep (se 1 (by rfl) ⟨18893219, by rfl⟩ : syracuseStep 25190959 = 37786439) B37786439
theorem B33587945 : Blo 1965435 33587945 := bstep (se 2 (by rfl) ⟨12595479, by rfl⟩ : syracuseStep 33587945 = 25190959) B25190959
theorem B22391963 : Blo 1965435 22391963 := bstep (se 1 (by rfl) ⟨16793972, by rfl⟩ : syracuseStep 22391963 = 33587945) B33587945
theorem B14927975 : Blo 1965435 14927975 := bstep (se 1 (by rfl) ⟨11195981, by rfl⟩ : syracuseStep 14927975 = 22391963) B22391963
theorem B9951983 : Blo 1965435 9951983 := bstep (se 1 (by rfl) ⟨7463987, by rfl⟩ : syracuseStep 9951983 = 14927975) B14927975
theorem B6634655 : Blo 1965435 6634655 := bstep (se 1 (by rfl) ⟨4975991, by rfl⟩ : syracuseStep 6634655 = 9951983) B9951983
theorem B4423103 : Blo 1965435 4423103 := bstep (se 1 (by rfl) ⟨3317327, by rfl⟩ : syracuseStep 4423103 = 6634655) B6634655
theorem B2948735 : Blo 1965435 2948735 := bstep (se 1 (by rfl) ⟨2211551, by rfl⟩ : syracuseStep 2948735 = 4423103) B4423103
theorem B1965823 : Blo 1965435 1965823 := bstep (se 1 (by rfl) ⟨1474367, by rfl⟩ : syracuseStep 1965823 = 2948735) B2948735
theorem B2948741 : Blo 1965435 2948741 := bbase (se 4 (by rfl) ⟨276444, by rfl⟩ : syracuseStep 2948741 = 552889) (by norm_num)
theorem B1965827 : Blo 1965435 1965827 := bstep (se 1 (by rfl) ⟨1474370, by rfl⟩ : syracuseStep 1965827 = 2948741) B2948741
theorem B3317341 : Blo 1965435 3317341 := bbase (se 3 (by rfl) ⟨622001, by rfl⟩ : syracuseStep 3317341 = 1244003) (by norm_num)
theorem B4423121 : Blo 1965435 4423121 := bstep (se 2 (by rfl) ⟨1658670, by rfl⟩ : syracuseStep 4423121 = 3317341) B3317341
theorem B2948747 : Blo 1965435 2948747 := bstep (se 1 (by rfl) ⟨2211560, by rfl⟩ : syracuseStep 2948747 = 4423121) B4423121
theorem B1965831 : Blo 1965435 1965831 := bstep (se 1 (by rfl) ⟨1474373, by rfl⟩ : syracuseStep 1965831 = 2948747) B2948747
theorem B2211565 : Blo 1965435 2211565 := bbase (se 3 (by rfl) ⟨414668, by rfl⟩ : syracuseStep 2211565 = 829337) (by norm_num)
theorem B2948753 : Blo 1965435 2948753 := bstep (se 2 (by rfl) ⟨1105782, by rfl⟩ : syracuseStep 2948753 = 2211565) B2211565
theorem B1965835 : Blo 1965435 1965835 := bstep (se 1 (by rfl) ⟨1474376, by rfl⟩ : syracuseStep 1965835 = 2948753) B2948753
theorem B6634709 : Blo 1965435 6634709 := bbase (se 7 (by rfl) ⟨77750, by rfl⟩ : syracuseStep 6634709 = 155501) (by norm_num)
theorem B4423139 : Blo 1965435 4423139 := bstep (se 1 (by rfl) ⟨3317354, by rfl⟩ : syracuseStep 4423139 = 6634709) B6634709
theorem B2948759 : Blo 1965435 2948759 := bstep (se 1 (by rfl) ⟨2211569, by rfl⟩ : syracuseStep 2948759 = 4423139) B4423139
theorem B1965839 : Blo 1965435 1965839 := bstep (se 1 (by rfl) ⟨1474379, by rfl⟩ : syracuseStep 1965839 = 2948759) B2948759
theorem B2948765 : Blo 1965435 2948765 := bbase (se 3 (by rfl) ⟨552893, by rfl⟩ : syracuseStep 2948765 = 1105787) (by norm_num)
theorem B1965843 : Blo 1965435 1965843 := bstep (se 1 (by rfl) ⟨1474382, by rfl⟩ : syracuseStep 1965843 = 2948765) B2948765
theorem B4423157 : Blo 1965435 4423157 := bbase (se 5 (by rfl) ⟨207335, by rfl⟩ : syracuseStep 4423157 = 414671) (by norm_num)
theorem B2948771 : Blo 1965435 2948771 := bstep (se 1 (by rfl) ⟨2211578, by rfl⟩ : syracuseStep 2948771 = 4423157) B4423157
theorem B1965847 : Blo 1965435 1965847 := bstep (se 1 (by rfl) ⟨1474385, by rfl⟩ : syracuseStep 1965847 = 2948771) B2948771
theorem B8967029 : Blo 1965435 8967029 := bbase (se 5 (by rfl) ⟨420329, by rfl⟩ : syracuseStep 8967029 = 840659) (by norm_num)
theorem B95648309 : Blo 1965435 95648309 := bstep (se 5 (by rfl) ⟨4483514, by rfl⟩ : syracuseStep 95648309 = 8967029) B8967029
theorem B63765539 : Blo 1965435 63765539 := bstep (se 1 (by rfl) ⟨47824154, by rfl⟩ : syracuseStep 63765539 = 95648309) B95648309
theorem B42510359 : Blo 1965435 42510359 := bstep (se 1 (by rfl) ⟨31882769, by rfl⟩ : syracuseStep 42510359 = 63765539) B63765539
theorem B28340239 : Blo 1965435 28340239 := bstep (se 1 (by rfl) ⟨21255179, by rfl⟩ : syracuseStep 28340239 = 42510359) B42510359
theorem B37786985 : Blo 1965435 37786985 := bstep (se 2 (by rfl) ⟨14170119, by rfl⟩ : syracuseStep 37786985 = 28340239) B28340239
theorem B25191323 : Blo 1965435 25191323 := bstep (se 1 (by rfl) ⟨18893492, by rfl⟩ : syracuseStep 25191323 = 37786985) B37786985
theorem B16794215 : Blo 1965435 16794215 := bstep (se 1 (by rfl) ⟨12595661, by rfl⟩ : syracuseStep 16794215 = 25191323) B25191323
theorem B11196143 : Blo 1965435 11196143 := bstep (se 1 (by rfl) ⟨8397107, by rfl⟩ : syracuseStep 11196143 = 16794215) B16794215
theorem B7464095 : Blo 1965435 7464095 := bstep (se 1 (by rfl) ⟨5598071, by rfl⟩ : syracuseStep 7464095 = 11196143) B11196143
theorem B4976063 : Blo 1965435 4976063 := bstep (se 1 (by rfl) ⟨3732047, by rfl⟩ : syracuseStep 4976063 = 7464095) B7464095
theorem B3317375 : Blo 1965435 3317375 := bstep (se 1 (by rfl) ⟨2488031, by rfl⟩ : syracuseStep 3317375 = 4976063) B4976063
theorem B2211583 : Blo 1965435 2211583 := bstep (se 1 (by rfl) ⟨1658687, by rfl⟩ : syracuseStep 2211583 = 3317375) B3317375
theorem B2948777 : Blo 1965435 2948777 := bstep (se 2 (by rfl) ⟨1105791, by rfl⟩ : syracuseStep 2948777 = 2211583) B2211583
theorem B1965851 : Blo 1965435 1965851 := bstep (se 1 (by rfl) ⟨1474388, by rfl⟩ : syracuseStep 1965851 = 2948777) B2948777
theorem B2099281 : Blo 1965435 2099281 := bbase (se 2 (by rfl) ⟨787230, by rfl⟩ : syracuseStep 2099281 = 1574461) (by norm_num)
theorem B2799041 : Blo 1965435 2799041 := bstep (se 2 (by rfl) ⟨1049640, by rfl⟩ : syracuseStep 2799041 = 2099281) B2099281
theorem B7464109 : Blo 1965435 7464109 := bstep (se 3 (by rfl) ⟨1399520, by rfl⟩ : syracuseStep 7464109 = 2799041) B2799041
theorem B9952145 : Blo 1965435 9952145 := bstep (se 2 (by rfl) ⟨3732054, by rfl⟩ : syracuseStep 9952145 = 7464109) B7464109
theorem B6634763 : Blo 1965435 6634763 := bstep (se 1 (by rfl) ⟨4976072, by rfl⟩ : syracuseStep 6634763 = 9952145) B9952145
theorem B4423175 : Blo 1965435 4423175 := bstep (se 1 (by rfl) ⟨3317381, by rfl⟩ : syracuseStep 4423175 = 6634763) B6634763
theorem B2948783 : Blo 1965435 2948783 := bstep (se 1 (by rfl) ⟨2211587, by rfl⟩ : syracuseStep 2948783 = 4423175) B4423175
theorem B1965855 : Blo 1965435 1965855 := bstep (se 1 (by rfl) ⟨1474391, by rfl⟩ : syracuseStep 1965855 = 2948783) B2948783
theorem B2948789 : Blo 1965435 2948789 := bbase (se 5 (by rfl) ⟨138224, by rfl⟩ : syracuseStep 2948789 = 276449) (by norm_num)
theorem B1965859 : Blo 1965435 1965859 := bstep (se 1 (by rfl) ⟨1474394, by rfl⟩ : syracuseStep 1965859 = 2948789) B2948789
theorem B4976093 : Blo 1965435 4976093 := bbase (se 3 (by rfl) ⟨933017, by rfl⟩ : syracuseStep 4976093 = 1866035) (by norm_num)
theorem B3317395 : Blo 1965435 3317395 := bstep (se 1 (by rfl) ⟨2488046, by rfl⟩ : syracuseStep 3317395 = 4976093) B4976093
theorem B4423193 : Blo 1965435 4423193 := bstep (se 2 (by rfl) ⟨1658697, by rfl⟩ : syracuseStep 4423193 = 3317395) B3317395
theorem B2948795 : Blo 1965435 2948795 := bstep (se 1 (by rfl) ⟨2211596, by rfl⟩ : syracuseStep 2948795 = 4423193) B4423193
theorem B1965863 : Blo 1965435 1965863 := bstep (se 1 (by rfl) ⟨1474397, by rfl⟩ : syracuseStep 1965863 = 2948795) B2948795
theorem B2211601 : Blo 1965435 2211601 := bbase (se 2 (by rfl) ⟨829350, by rfl⟩ : syracuseStep 2211601 = 1658701) (by norm_num)
theorem B2948801 : Blo 1965435 2948801 := bstep (se 2 (by rfl) ⟨1105800, by rfl⟩ : syracuseStep 2948801 = 2211601) B2211601
theorem B1965867 : Blo 1965435 1965867 := bstep (se 1 (by rfl) ⟨1474400, by rfl⟩ : syracuseStep 1965867 = 2948801) B2948801
theorem B3732085 : Blo 1965435 3732085 := bbase (se 5 (by rfl) ⟨174941, by rfl⟩ : syracuseStep 3732085 = 349883) (by norm_num)
theorem B4976113 : Blo 1965435 4976113 := bstep (se 2 (by rfl) ⟨1866042, by rfl⟩ : syracuseStep 4976113 = 3732085) B3732085
theorem B6634817 : Blo 1965435 6634817 := bstep (se 2 (by rfl) ⟨2488056, by rfl⟩ : syracuseStep 6634817 = 4976113) B4976113
theorem B4423211 : Blo 1965435 4423211 := bstep (se 1 (by rfl) ⟨3317408, by rfl⟩ : syracuseStep 4423211 = 6634817) B6634817
theorem B2948807 : Blo 1965435 2948807 := bstep (se 1 (by rfl) ⟨2211605, by rfl⟩ : syracuseStep 2948807 = 4423211) B4423211
theorem B1965871 : Blo 1965435 1965871 := bstep (se 1 (by rfl) ⟨1474403, by rfl⟩ : syracuseStep 1965871 = 2948807) B2948807
theorem B2948813 : Blo 1965435 2948813 := bbase (se 3 (by rfl) ⟨552902, by rfl⟩ : syracuseStep 2948813 = 1105805) (by norm_num)
theorem B1965875 : Blo 1965435 1965875 := bstep (se 1 (by rfl) ⟨1474406, by rfl⟩ : syracuseStep 1965875 = 2948813) B2948813
theorem B4423229 : Blo 1965435 4423229 := bbase (se 3 (by rfl) ⟨829355, by rfl⟩ : syracuseStep 4423229 = 1658711) (by norm_num)
theorem B2948819 : Blo 1965435 2948819 := bstep (se 1 (by rfl) ⟨2211614, by rfl⟩ : syracuseStep 2948819 = 4423229) B4423229
theorem B1965879 : Blo 1965435 1965879 := bstep (se 1 (by rfl) ⟨1474409, by rfl⟩ : syracuseStep 1965879 = 2948819) B2948819
theorem B3317429 : Blo 1965435 3317429 := bbase (se 5 (by rfl) ⟨155504, by rfl⟩ : syracuseStep 3317429 = 311009) (by norm_num)
theorem B2211619 : Blo 1965435 2211619 := bstep (se 1 (by rfl) ⟨1658714, by rfl⟩ : syracuseStep 2211619 = 3317429) B3317429
theorem B2948825 : Blo 1965435 2948825 := bstep (se 2 (by rfl) ⟨1105809, by rfl⟩ : syracuseStep 2948825 = 2211619) B2211619
theorem B1965883 : Blo 1965435 1965883 := bstep (se 1 (by rfl) ⟨1474412, by rfl⟩ : syracuseStep 1965883 = 2948825) B2948825
theorem B3148973 : Blo 1965435 3148973 := bbase (se 3 (by rfl) ⟨590432, by rfl⟩ : syracuseStep 3148973 = 1180865) (by norm_num)
theorem B2099315 : Blo 1965435 2099315 := bstep (se 1 (by rfl) ⟨1574486, by rfl⟩ : syracuseStep 2099315 = 3148973) B3148973
theorem B5598173 : Blo 1965435 5598173 := bstep (se 3 (by rfl) ⟨1049657, by rfl⟩ : syracuseStep 5598173 = 2099315) B2099315
theorem B14928461 : Blo 1965435 14928461 := bstep (se 3 (by rfl) ⟨2799086, by rfl⟩ : syracuseStep 14928461 = 5598173) B5598173
theorem B9952307 : Blo 1965435 9952307 := bstep (se 1 (by rfl) ⟨7464230, by rfl⟩ : syracuseStep 9952307 = 14928461) B14928461
theorem B6634871 : Blo 1965435 6634871 := bstep (se 1 (by rfl) ⟨4976153, by rfl⟩ : syracuseStep 6634871 = 9952307) B9952307
theorem B4423247 : Blo 1965435 4423247 := bstep (se 1 (by rfl) ⟨3317435, by rfl⟩ : syracuseStep 4423247 = 6634871) B6634871
theorem B2948831 : Blo 1965435 2948831 := bstep (se 1 (by rfl) ⟨2211623, by rfl⟩ : syracuseStep 2948831 = 4423247) B4423247
theorem B1965887 : Blo 1965435 1965887 := bstep (se 1 (by rfl) ⟨1474415, by rfl⟩ : syracuseStep 1965887 = 2948831) B2948831
theorem B2948837 : Blo 1965435 2948837 := bbase (se 4 (by rfl) ⟨276453, by rfl⟩ : syracuseStep 2948837 = 552907) (by norm_num)
theorem B1965891 : Blo 1965435 1965891 := bstep (se 1 (by rfl) ⟨1474418, by rfl⟩ : syracuseStep 1965891 = 2948837) B2948837
theorem B5598197 : Blo 1965435 5598197 := bbase (se 5 (by rfl) ⟨262415, by rfl⟩ : syracuseStep 5598197 = 524831) (by norm_num)
theorem B3732131 : Blo 1965435 3732131 := bstep (se 1 (by rfl) ⟨2799098, by rfl⟩ : syracuseStep 3732131 = 5598197) B5598197
theorem B2488087 : Blo 1965435 2488087 := bstep (se 1 (by rfl) ⟨1866065, by rfl⟩ : syracuseStep 2488087 = 3732131) B3732131
theorem B3317449 : Blo 1965435 3317449 := bstep (se 2 (by rfl) ⟨1244043, by rfl⟩ : syracuseStep 3317449 = 2488087) B2488087
theorem B4423265 : Blo 1965435 4423265 := bstep (se 2 (by rfl) ⟨1658724, by rfl⟩ : syracuseStep 4423265 = 3317449) B3317449
theorem B2948843 : Blo 1965435 2948843 := bstep (se 1 (by rfl) ⟨2211632, by rfl⟩ : syracuseStep 2948843 = 4423265) B4423265
theorem B1965895 : Blo 1965435 1965895 := bstep (se 1 (by rfl) ⟨1474421, by rfl⟩ : syracuseStep 1965895 = 2948843) B2948843
theorem B2211637 : Blo 1965435 2211637 := bbase (se 5 (by rfl) ⟨103670, by rfl⟩ : syracuseStep 2211637 = 207341) (by norm_num)
theorem B2948849 : Blo 1965435 2948849 := bstep (se 2 (by rfl) ⟨1105818, by rfl⟩ : syracuseStep 2948849 = 2211637) B2211637
theorem B1965899 : Blo 1965435 1965899 := bstep (se 1 (by rfl) ⟨1474424, by rfl⟩ : syracuseStep 1965899 = 2948849) B2948849
theorem B2488097 : Blo 1965435 2488097 := bbase (se 2 (by rfl) ⟨933036, by rfl⟩ : syracuseStep 2488097 = 1866073) (by norm_num)
theorem B6634925 : Blo 1965435 6634925 := bstep (se 3 (by rfl) ⟨1244048, by rfl⟩ : syracuseStep 6634925 = 2488097) B2488097
theorem B4423283 : Blo 1965435 4423283 := bstep (se 1 (by rfl) ⟨3317462, by rfl⟩ : syracuseStep 4423283 = 6634925) B6634925
theorem B2948855 : Blo 1965435 2948855 := bstep (se 1 (by rfl) ⟨2211641, by rfl⟩ : syracuseStep 2948855 = 4423283) B4423283
theorem B1965903 : Blo 1965435 1965903 := bstep (se 1 (by rfl) ⟨1474427, by rfl⟩ : syracuseStep 1965903 = 2948855) B2948855
theorem B2948861 : Blo 1965435 2948861 := bbase (se 3 (by rfl) ⟨552911, by rfl⟩ : syracuseStep 2948861 = 1105823) (by norm_num)
theorem B1965907 : Blo 1965435 1965907 := bstep (se 1 (by rfl) ⟨1474430, by rfl⟩ : syracuseStep 1965907 = 2948861) B2948861
theorem B4423301 : Blo 1965435 4423301 := bbase (se 4 (by rfl) ⟨414684, by rfl⟩ : syracuseStep 4423301 = 829369) (by norm_num)
theorem B2948867 : Blo 1965435 2948867 := bstep (se 1 (by rfl) ⟨2211650, by rfl⟩ : syracuseStep 2948867 = 4423301) B4423301
theorem B1965911 : Blo 1965435 1965911 := bstep (se 1 (by rfl) ⟨1474433, by rfl⟩ : syracuseStep 1965911 = 2948867) B2948867
theorem B6298037 : Blo 1965435 6298037 := bbase (se 5 (by rfl) ⟨295220, by rfl⟩ : syracuseStep 6298037 = 590441) (by norm_num)
theorem B4198691 : Blo 1965435 4198691 := bstep (se 1 (by rfl) ⟨3149018, by rfl⟩ : syracuseStep 4198691 = 6298037) B6298037
theorem B2799127 : Blo 1965435 2799127 := bstep (se 1 (by rfl) ⟨2099345, by rfl⟩ : syracuseStep 2799127 = 4198691) B4198691
theorem B3732169 : Blo 1965435 3732169 := bstep (se 2 (by rfl) ⟨1399563, by rfl⟩ : syracuseStep 3732169 = 2799127) B2799127
theorem B4976225 : Blo 1965435 4976225 := bstep (se 2 (by rfl) ⟨1866084, by rfl⟩ : syracuseStep 4976225 = 3732169) B3732169
theorem B3317483 : Blo 1965435 3317483 := bstep (se 1 (by rfl) ⟨2488112, by rfl⟩ : syracuseStep 3317483 = 4976225) B4976225
theorem B2211655 : Blo 1965435 2211655 := bstep (se 1 (by rfl) ⟨1658741, by rfl⟩ : syracuseStep 2211655 = 3317483) B3317483
theorem B2948873 : Blo 1965435 2948873 := bstep (se 2 (by rfl) ⟨1105827, by rfl⟩ : syracuseStep 2948873 = 2211655) B2211655
theorem B1965915 : Blo 1965435 1965915 := bstep (se 1 (by rfl) ⟨1474436, by rfl⟩ : syracuseStep 1965915 = 2948873) B2948873
theorem B9952469 : Blo 1965435 9952469 := bbase (se 7 (by rfl) ⟨116630, by rfl⟩ : syracuseStep 9952469 = 233261) (by norm_num)
theorem B6634979 : Blo 1965435 6634979 := bstep (se 1 (by rfl) ⟨4976234, by rfl⟩ : syracuseStep 6634979 = 9952469) B9952469
theorem B4423319 : Blo 1965435 4423319 := bstep (se 1 (by rfl) ⟨3317489, by rfl⟩ : syracuseStep 4423319 = 6634979) B6634979
theorem B2948879 : Blo 1965435 2948879 := bstep (se 1 (by rfl) ⟨2211659, by rfl⟩ : syracuseStep 2948879 = 4423319) B4423319
theorem B1965919 : Blo 1965435 1965919 := bstep (se 1 (by rfl) ⟨1474439, by rfl⟩ : syracuseStep 1965919 = 2948879) B2948879
theorem B2948885 : Blo 1965435 2948885 := bbase (se 6 (by rfl) ⟨69114, by rfl⟩ : syracuseStep 2948885 = 138229) (by norm_num)
theorem B1965923 : Blo 1965435 1965923 := bstep (se 1 (by rfl) ⟨1474442, by rfl⟩ : syracuseStep 1965923 = 2948885) B2948885
theorem B7479989 : Blo 1965435 7479989 := bbase (se 5 (by rfl) ⟨350624, by rfl⟩ : syracuseStep 7479989 = 701249) (by norm_num)
theorem B4986659 : Blo 1965435 4986659 := bstep (se 1 (by rfl) ⟨3739994, by rfl⟩ : syracuseStep 4986659 = 7479989) B7479989
theorem B3324439 : Blo 1965435 3324439 := bstep (se 1 (by rfl) ⟨2493329, by rfl⟩ : syracuseStep 3324439 = 4986659) B4986659
theorem B4432585 : Blo 1965435 4432585 := bstep (se 2 (by rfl) ⟨1662219, by rfl⟩ : syracuseStep 4432585 = 3324439) B3324439
theorem B94561813 : Blo 1965435 94561813 := bstep (se 6 (by rfl) ⟨2216292, by rfl⟩ : syracuseStep 94561813 = 4432585) B4432585
theorem B126082417 : Blo 1965435 126082417 := bstep (se 2 (by rfl) ⟨47280906, by rfl⟩ : syracuseStep 126082417 = 94561813) B94561813
theorem B168109889 : Blo 1965435 168109889 := bstep (se 2 (by rfl) ⟨63041208, by rfl⟩ : syracuseStep 168109889 = 126082417) B126082417
theorem B448293037 : Blo 1965435 448293037 := bstep (se 3 (by rfl) ⟨84054944, by rfl⟩ : syracuseStep 448293037 = 168109889) B168109889
theorem B597724049 : Blo 1965435 597724049 := bstep (se 2 (by rfl) ⟨224146518, by rfl⟩ : syracuseStep 597724049 = 448293037) B448293037
theorem B398482699 : Blo 1965435 398482699 := bstep (se 1 (by rfl) ⟨298862024, by rfl⟩ : syracuseStep 398482699 = 597724049) B597724049
theorem B531310265 : Blo 1965435 531310265 := bstep (se 2 (by rfl) ⟨199241349, by rfl⟩ : syracuseStep 531310265 = 398482699) B398482699
theorem B354206843 : Blo 1965435 354206843 := bstep (se 1 (by rfl) ⟨265655132, by rfl⟩ : syracuseStep 354206843 = 531310265) B531310265
theorem B236137895 : Blo 1965435 236137895 := bstep (se 1 (by rfl) ⟨177103421, by rfl⟩ : syracuseStep 236137895 = 354206843) B354206843
theorem B157425263 : Blo 1965435 157425263 := bstep (se 1 (by rfl) ⟨118068947, by rfl⟩ : syracuseStep 157425263 = 236137895) B236137895
theorem B104950175 : Blo 1965435 104950175 := bstep (se 1 (by rfl) ⟨78712631, by rfl⟩ : syracuseStep 104950175 = 157425263) B157425263
theorem B279867133 : Blo 1965435 279867133 := bstep (se 3 (by rfl) ⟨52475087, by rfl⟩ : syracuseStep 279867133 = 104950175) B104950175
theorem B373156177 : Blo 1965435 373156177 := bstep (se 2 (by rfl) ⟨139933566, by rfl⟩ : syracuseStep 373156177 = 279867133) B279867133
theorem B497541569 : Blo 1965435 497541569 := bstep (se 2 (by rfl) ⟨186578088, by rfl⟩ : syracuseStep 497541569 = 373156177) B373156177
theorem B1326777517 : Blo 1965435 1326777517 := bstep (se 3 (by rfl) ⟨248770784, by rfl⟩ : syracuseStep 1326777517 = 497541569) B497541569
theorem B1769036689 : Blo 1965435 1769036689 := bstep (se 2 (by rfl) ⟨663388758, by rfl⟩ : syracuseStep 1769036689 = 1326777517) B1326777517
theorem B9434862341 : Blo 1965435 9434862341 := bstep (se 4 (by rfl) ⟨884518344, by rfl⟩ : syracuseStep 9434862341 = 1769036689) B1769036689
theorem B6289908227 : Blo 1965435 6289908227 := bstep (se 1 (by rfl) ⟨4717431170, by rfl⟩ : syracuseStep 6289908227 = 9434862341) B9434862341
theorem B4193272151 : Blo 1965435 4193272151 := bstep (se 1 (by rfl) ⟨3144954113, by rfl⟩ : syracuseStep 4193272151 = 6289908227) B6289908227
theorem B2795514767 : Blo 1965435 2795514767 := bstep (se 1 (by rfl) ⟨2096636075, by rfl⟩ : syracuseStep 2795514767 = 4193272151) B4193272151
theorem B1863676511 : Blo 1965435 1863676511 := bstep (se 1 (by rfl) ⟨1397757383, by rfl⟩ : syracuseStep 1863676511 = 2795514767) B2795514767
theorem B1242451007 : Blo 1965435 1242451007 := bstep (se 1 (by rfl) ⟨931838255, by rfl⟩ : syracuseStep 1242451007 = 1863676511) B1863676511
theorem B828300671 : Blo 1965435 828300671 := bstep (se 1 (by rfl) ⟨621225503, by rfl⟩ : syracuseStep 828300671 = 1242451007) B1242451007
theorem B552200447 : Blo 1965435 552200447 := bstep (se 1 (by rfl) ⟨414150335, by rfl⟩ : syracuseStep 552200447 = 828300671) B828300671
theorem B1472534525 : Blo 1965435 1472534525 := bstep (se 3 (by rfl) ⟨276100223, by rfl⟩ : syracuseStep 1472534525 = 552200447) B552200447
theorem B3926758733 : Blo 1965435 3926758733 := bstep (se 3 (by rfl) ⟨736267262, by rfl⟩ : syracuseStep 3926758733 = 1472534525) B1472534525
theorem B2617839155 : Blo 1965435 2617839155 := bstep (se 1 (by rfl) ⟨1963379366, by rfl⟩ : syracuseStep 2617839155 = 3926758733) B3926758733
theorem B1745226103 : Blo 1965435 1745226103 := bstep (se 1 (by rfl) ⟨1308919577, by rfl⟩ : syracuseStep 1745226103 = 2617839155) B2617839155
theorem B2326968137 : Blo 1965435 2326968137 := bstep (se 2 (by rfl) ⟨872613051, by rfl⟩ : syracuseStep 2326968137 = 1745226103) B1745226103
theorem B1551312091 : Blo 1965435 1551312091 := bstep (se 1 (by rfl) ⟨1163484068, by rfl⟩ : syracuseStep 1551312091 = 2326968137) B2326968137
theorem B2068416121 : Blo 1965435 2068416121 := bstep (se 2 (by rfl) ⟨775656045, by rfl⟩ : syracuseStep 2068416121 = 1551312091) B1551312091
theorem B2757888161 : Blo 1965435 2757888161 := bstep (se 2 (by rfl) ⟨1034208060, by rfl⟩ : syracuseStep 2757888161 = 2068416121) B2068416121
theorem B1838592107 : Blo 1965435 1838592107 := bstep (se 1 (by rfl) ⟨1378944080, by rfl⟩ : syracuseStep 1838592107 = 2757888161) B2757888161
theorem B1225728071 : Blo 1965435 1225728071 := bstep (se 1 (by rfl) ⟨919296053, by rfl⟩ : syracuseStep 1225728071 = 1838592107) B1838592107
theorem B817152047 : Blo 1965435 817152047 := bstep (se 1 (by rfl) ⟨612864035, by rfl⟩ : syracuseStep 817152047 = 1225728071) B1225728071
theorem B544768031 : Blo 1965435 544768031 := bstep (se 1 (by rfl) ⟨408576023, by rfl⟩ : syracuseStep 544768031 = 817152047) B817152047
theorem B363178687 : Blo 1965435 363178687 := bstep (se 1 (by rfl) ⟨272384015, by rfl⟩ : syracuseStep 363178687 = 544768031) B544768031
theorem B484238249 : Blo 1965435 484238249 := bstep (se 2 (by rfl) ⟨181589343, by rfl⟩ : syracuseStep 484238249 = 363178687) B363178687
theorem B322825499 : Blo 1965435 322825499 := bstep (se 1 (by rfl) ⟨242119124, by rfl⟩ : syracuseStep 322825499 = 484238249) B484238249
theorem B215216999 : Blo 1965435 215216999 := bstep (se 1 (by rfl) ⟨161412749, by rfl⟩ : syracuseStep 215216999 = 322825499) B322825499
theorem B143477999 : Blo 1965435 143477999 := bstep (se 1 (by rfl) ⟨107608499, by rfl⟩ : syracuseStep 143477999 = 215216999) B215216999
theorem B95651999 : Blo 1965435 95651999 := bstep (se 1 (by rfl) ⟨71738999, by rfl⟩ : syracuseStep 95651999 = 143477999) B143477999
theorem B63767999 : Blo 1965435 63767999 := bstep (se 1 (by rfl) ⟨47825999, by rfl⟩ : syracuseStep 63767999 = 95651999) B95651999
theorem B42511999 : Blo 1965435 42511999 := bstep (se 1 (by rfl) ⟨31883999, by rfl⟩ : syracuseStep 42511999 = 63767999) B63767999
theorem B56682665 : Blo 1965435 56682665 := bstep (se 2 (by rfl) ⟨21255999, by rfl⟩ : syracuseStep 56682665 = 42511999) B42511999
theorem B37788443 : Blo 1965435 37788443 := bstep (se 1 (by rfl) ⟨28341332, by rfl⟩ : syracuseStep 37788443 = 56682665) B56682665
theorem B25192295 : Blo 1965435 25192295 := bstep (se 1 (by rfl) ⟨18894221, by rfl⟩ : syracuseStep 25192295 = 37788443) B37788443
theorem B16794863 : Blo 1965435 16794863 := bstep (se 1 (by rfl) ⟨12596147, by rfl⟩ : syracuseStep 16794863 = 25192295) B25192295
theorem B11196575 : Blo 1965435 11196575 := bstep (se 1 (by rfl) ⟨8397431, by rfl⟩ : syracuseStep 11196575 = 16794863) B16794863
theorem B7464383 : Blo 1965435 7464383 := bstep (se 1 (by rfl) ⟨5598287, by rfl⟩ : syracuseStep 7464383 = 11196575) B11196575
theorem B4976255 : Blo 1965435 4976255 := bstep (se 1 (by rfl) ⟨3732191, by rfl⟩ : syracuseStep 4976255 = 7464383) B7464383
theorem B3317503 : Blo 1965435 3317503 := bstep (se 1 (by rfl) ⟨2488127, by rfl⟩ : syracuseStep 3317503 = 4976255) B4976255
theorem B4423337 : Blo 1965435 4423337 := bstep (se 2 (by rfl) ⟨1658751, by rfl⟩ : syracuseStep 4423337 = 3317503) B3317503
theorem B2948891 : Blo 1965435 2948891 := bstep (se 1 (by rfl) ⟨2211668, by rfl⟩ : syracuseStep 2948891 = 4423337) B4423337
theorem B1965927 : Blo 1965435 1965927 := bstep (se 1 (by rfl) ⟨1474445, by rfl⟩ : syracuseStep 1965927 = 2948891) B2948891
theorem B2211673 : Blo 1965435 2211673 := bbase (se 2 (by rfl) ⟨829377, by rfl⟩ : syracuseStep 2211673 = 1658755) (by norm_num)
theorem B2948897 : Blo 1965435 2948897 := bstep (se 2 (by rfl) ⟨1105836, by rfl⟩ : syracuseStep 2948897 = 2211673) B2211673
theorem B1965931 : Blo 1965435 1965931 := bstep (se 1 (by rfl) ⟨1474448, by rfl⟩ : syracuseStep 1965931 = 2948897) B2948897
theorem B4198733 : Blo 1965435 4198733 := bbase (se 3 (by rfl) ⟨787262, by rfl⟩ : syracuseStep 4198733 = 1574525) (by norm_num)
theorem B2799155 : Blo 1965435 2799155 := bstep (se 1 (by rfl) ⟨2099366, by rfl⟩ : syracuseStep 2799155 = 4198733) B4198733
theorem B7464413 : Blo 1965435 7464413 := bstep (se 3 (by rfl) ⟨1399577, by rfl⟩ : syracuseStep 7464413 = 2799155) B2799155
theorem B4976275 : Blo 1965435 4976275 := bstep (se 1 (by rfl) ⟨3732206, by rfl⟩ : syracuseStep 4976275 = 7464413) B7464413
theorem B6635033 : Blo 1965435 6635033 := bstep (se 2 (by rfl) ⟨2488137, by rfl⟩ : syracuseStep 6635033 = 4976275) B4976275
theorem B4423355 : Blo 1965435 4423355 := bstep (se 1 (by rfl) ⟨3317516, by rfl⟩ : syracuseStep 4423355 = 6635033) B6635033
theorem B2948903 : Blo 1965435 2948903 := bstep (se 1 (by rfl) ⟨2211677, by rfl⟩ : syracuseStep 2948903 = 4423355) B4423355
theorem B1965935 : Blo 1965435 1965935 := bstep (se 1 (by rfl) ⟨1474451, by rfl⟩ : syracuseStep 1965935 = 2948903) B2948903
theorem B2948909 : Blo 1965435 2948909 := bbase (se 3 (by rfl) ⟨552920, by rfl⟩ : syracuseStep 2948909 = 1105841) (by norm_num)
theorem B1965939 : Blo 1965435 1965939 := bstep (se 1 (by rfl) ⟨1474454, by rfl⟩ : syracuseStep 1965939 = 2948909) B2948909
theorem B4423373 : Blo 1965435 4423373 := bbase (se 3 (by rfl) ⟨829382, by rfl⟩ : syracuseStep 4423373 = 1658765) (by norm_num)
theorem B2948915 : Blo 1965435 2948915 := bstep (se 1 (by rfl) ⟨2211686, by rfl⟩ : syracuseStep 2948915 = 4423373) B4423373
theorem B1965943 : Blo 1965435 1965943 := bstep (se 1 (by rfl) ⟨1474457, by rfl⟩ : syracuseStep 1965943 = 2948915) B2948915
theorem B2488153 : Blo 1965435 2488153 := bbase (se 2 (by rfl) ⟨933057, by rfl⟩ : syracuseStep 2488153 = 1866115) (by norm_num)
theorem B3317537 : Blo 1965435 3317537 := bstep (se 2 (by rfl) ⟨1244076, by rfl⟩ : syracuseStep 3317537 = 2488153) B2488153
theorem B2211691 : Blo 1965435 2211691 := bstep (se 1 (by rfl) ⟨1658768, by rfl⟩ : syracuseStep 2211691 = 3317537) B3317537
theorem B2948921 : Blo 1965435 2948921 := bstep (se 2 (by rfl) ⟨1105845, by rfl⟩ : syracuseStep 2948921 = 2211691) B2211691
theorem B1965947 : Blo 1965435 1965947 := bstep (se 1 (by rfl) ⟨1474460, by rfl⟩ : syracuseStep 1965947 = 2948921) B2948921
theorem B4723613 : Blo 1965435 4723613 := bbase (se 3 (by rfl) ⟨885677, by rfl⟩ : syracuseStep 4723613 = 1771355) (by norm_num)
theorem B3149075 : Blo 1965435 3149075 := bstep (se 1 (by rfl) ⟨2361806, by rfl⟩ : syracuseStep 3149075 = 4723613) B4723613
theorem B8397533 : Blo 1965435 8397533 := bstep (se 3 (by rfl) ⟨1574537, by rfl⟩ : syracuseStep 8397533 = 3149075) B3149075
theorem B22393421 : Blo 1965435 22393421 := bstep (se 3 (by rfl) ⟨4198766, by rfl⟩ : syracuseStep 22393421 = 8397533) B8397533
theorem B14928947 : Blo 1965435 14928947 := bstep (se 1 (by rfl) ⟨11196710, by rfl⟩ : syracuseStep 14928947 = 22393421) B22393421
theorem B9952631 : Blo 1965435 9952631 := bstep (se 1 (by rfl) ⟨7464473, by rfl⟩ : syracuseStep 9952631 = 14928947) B14928947
theorem B6635087 : Blo 1965435 6635087 := bstep (se 1 (by rfl) ⟨4976315, by rfl⟩ : syracuseStep 6635087 = 9952631) B9952631
theorem B4423391 : Blo 1965435 4423391 := bstep (se 1 (by rfl) ⟨3317543, by rfl⟩ : syracuseStep 4423391 = 6635087) B6635087
theorem B2948927 : Blo 1965435 2948927 := bstep (se 1 (by rfl) ⟨2211695, by rfl⟩ : syracuseStep 2948927 = 4423391) B4423391
theorem B1965951 : Blo 1965435 1965951 := bstep (se 1 (by rfl) ⟨1474463, by rfl⟩ : syracuseStep 1965951 = 2948927) B2948927
theorem B2948933 : Blo 1965435 2948933 := bbase (se 4 (by rfl) ⟨276462, by rfl⟩ : syracuseStep 2948933 = 552925) (by norm_num)
theorem B1965955 : Blo 1965435 1965955 := bstep (se 1 (by rfl) ⟨1474466, by rfl⟩ : syracuseStep 1965955 = 2948933) B2948933
theorem B3317557 : Blo 1965435 3317557 := bbase (se 5 (by rfl) ⟨155510, by rfl⟩ : syracuseStep 3317557 = 311021) (by norm_num)
theorem B4423409 : Blo 1965435 4423409 := bstep (se 2 (by rfl) ⟨1658778, by rfl⟩ : syracuseStep 4423409 = 3317557) B3317557
theorem B2948939 : Blo 1965435 2948939 := bstep (se 1 (by rfl) ⟨2211704, by rfl⟩ : syracuseStep 2948939 = 4423409) B4423409
theorem B1965959 : Blo 1965435 1965959 := bstep (se 1 (by rfl) ⟨1474469, by rfl⟩ : syracuseStep 1965959 = 2948939) B2948939
theorem B2211709 : Blo 1965435 2211709 := bbase (se 3 (by rfl) ⟨414695, by rfl⟩ : syracuseStep 2211709 = 829391) (by norm_num)
theorem B2948945 : Blo 1965435 2948945 := bstep (se 2 (by rfl) ⟨1105854, by rfl⟩ : syracuseStep 2948945 = 2211709) B2211709
theorem B1965963 : Blo 1965435 1965963 := bstep (se 1 (by rfl) ⟨1474472, by rfl⟩ : syracuseStep 1965963 = 2948945) B2948945
theorem B6635141 : Blo 1965435 6635141 := bbase (se 4 (by rfl) ⟨622044, by rfl⟩ : syracuseStep 6635141 = 1244089) (by norm_num)
theorem B4423427 : Blo 1965435 4423427 := bstep (se 1 (by rfl) ⟨3317570, by rfl⟩ : syracuseStep 4423427 = 6635141) B6635141
theorem B2948951 : Blo 1965435 2948951 := bstep (se 1 (by rfl) ⟨2211713, by rfl⟩ : syracuseStep 2948951 = 4423427) B4423427
theorem B1965967 : Blo 1965435 1965967 := bstep (se 1 (by rfl) ⟨1474475, by rfl⟩ : syracuseStep 1965967 = 2948951) B2948951
theorem B2948957 : Blo 1965435 2948957 := bbase (se 3 (by rfl) ⟨552929, by rfl⟩ : syracuseStep 2948957 = 1105859) (by norm_num)
theorem B1965971 : Blo 1965435 1965971 := bstep (se 1 (by rfl) ⟨1474478, by rfl⟩ : syracuseStep 1965971 = 2948957) B2948957
theorem B4423445 : Blo 1965435 4423445 := bbase (se 6 (by rfl) ⟨103674, by rfl⟩ : syracuseStep 4423445 = 207349) (by norm_num)
theorem B2948963 : Blo 1965435 2948963 := bstep (se 1 (by rfl) ⟨2211722, by rfl⟩ : syracuseStep 2948963 = 4423445) B4423445
theorem B1965975 : Blo 1965435 1965975 := bstep (se 1 (by rfl) ⟨1474481, by rfl⟩ : syracuseStep 1965975 = 2948963) B2948963
theorem B7464581 : Blo 1965435 7464581 := bbase (se 4 (by rfl) ⟨699804, by rfl⟩ : syracuseStep 7464581 = 1399609) (by norm_num)
theorem B4976387 : Blo 1965435 4976387 := bstep (se 1 (by rfl) ⟨3732290, by rfl⟩ : syracuseStep 4976387 = 7464581) B7464581
theorem B3317591 : Blo 1965435 3317591 := bstep (se 1 (by rfl) ⟨2488193, by rfl⟩ : syracuseStep 3317591 = 4976387) B4976387
theorem B2211727 : Blo 1965435 2211727 := bstep (se 1 (by rfl) ⟨1658795, by rfl⟩ : syracuseStep 2211727 = 3317591) B3317591
theorem B2948969 : Blo 1965435 2948969 := bstep (se 2 (by rfl) ⟨1105863, by rfl⟩ : syracuseStep 2948969 = 2211727) B2211727
theorem B1965979 : Blo 1965435 1965979 := bstep (se 1 (by rfl) ⟨1474484, by rfl⟩ : syracuseStep 1965979 = 2948969) B2948969
theorem B2361845 : Blo 1965435 2361845 := bbase (se 5 (by rfl) ⟨110711, by rfl⟩ : syracuseStep 2361845 = 221423) (by norm_num)
theorem B6298253 : Blo 1965435 6298253 := bstep (se 3 (by rfl) ⟨1180922, by rfl⟩ : syracuseStep 6298253 = 2361845) B2361845
theorem B4198835 : Blo 1965435 4198835 := bstep (se 1 (by rfl) ⟨3149126, by rfl⟩ : syracuseStep 4198835 = 6298253) B6298253
theorem B11196893 : Blo 1965435 11196893 := bstep (se 3 (by rfl) ⟨2099417, by rfl⟩ : syracuseStep 11196893 = 4198835) B4198835
theorem B7464595 : Blo 1965435 7464595 := bstep (se 1 (by rfl) ⟨5598446, by rfl⟩ : syracuseStep 7464595 = 11196893) B11196893
theorem B9952793 : Blo 1965435 9952793 := bstep (se 2 (by rfl) ⟨3732297, by rfl⟩ : syracuseStep 9952793 = 7464595) B7464595
theorem B6635195 : Blo 1965435 6635195 := bstep (se 1 (by rfl) ⟨4976396, by rfl⟩ : syracuseStep 6635195 = 9952793) B9952793
theorem B4423463 : Blo 1965435 4423463 := bstep (se 1 (by rfl) ⟨3317597, by rfl⟩ : syracuseStep 4423463 = 6635195) B6635195
theorem B2948975 : Blo 1965435 2948975 := bstep (se 1 (by rfl) ⟨2211731, by rfl⟩ : syracuseStep 2948975 = 4423463) B4423463
theorem B1965983 : Blo 1965435 1965983 := bstep (se 1 (by rfl) ⟨1474487, by rfl⟩ : syracuseStep 1965983 = 2948975) B2948975
theorem B2948981 : Blo 1965435 2948981 := bbase (se 5 (by rfl) ⟨138233, by rfl⟩ : syracuseStep 2948981 = 276467) (by norm_num)
theorem B1965987 : Blo 1965435 1965987 := bstep (se 1 (by rfl) ⟨1474490, by rfl⟩ : syracuseStep 1965987 = 2948981) B2948981
theorem B4198853 : Blo 1965435 4198853 := bbase (se 4 (by rfl) ⟨393642, by rfl⟩ : syracuseStep 4198853 = 787285) (by norm_num)
theorem B2799235 : Blo 1965435 2799235 := bstep (se 1 (by rfl) ⟨2099426, by rfl⟩ : syracuseStep 2799235 = 4198853) B4198853
theorem B3732313 : Blo 1965435 3732313 := bstep (se 2 (by rfl) ⟨1399617, by rfl⟩ : syracuseStep 3732313 = 2799235) B2799235
theorem B4976417 : Blo 1965435 4976417 := bstep (se 2 (by rfl) ⟨1866156, by rfl⟩ : syracuseStep 4976417 = 3732313) B3732313
theorem B3317611 : Blo 1965435 3317611 := bstep (se 1 (by rfl) ⟨2488208, by rfl⟩ : syracuseStep 3317611 = 4976417) B4976417
theorem B4423481 : Blo 1965435 4423481 := bstep (se 2 (by rfl) ⟨1658805, by rfl⟩ : syracuseStep 4423481 = 3317611) B3317611
theorem B2948987 : Blo 1965435 2948987 := bstep (se 1 (by rfl) ⟨2211740, by rfl⟩ : syracuseStep 2948987 = 4423481) B4423481
theorem B1965991 : Blo 1965435 1965991 := bstep (se 1 (by rfl) ⟨1474493, by rfl⟩ : syracuseStep 1965991 = 2948987) B2948987
theorem B2211745 : Blo 1965435 2211745 := bbase (se 2 (by rfl) ⟨829404, by rfl⟩ : syracuseStep 2211745 = 1658809) (by norm_num)
theorem B2948993 : Blo 1965435 2948993 := bstep (se 2 (by rfl) ⟨1105872, by rfl⟩ : syracuseStep 2948993 = 2211745) B2211745
theorem B1965995 : Blo 1965435 1965995 := bstep (se 1 (by rfl) ⟨1474496, by rfl⟩ : syracuseStep 1965995 = 2948993) B2948993
theorem B4976437 : Blo 1965435 4976437 := bbase (se 5 (by rfl) ⟨233270, by rfl⟩ : syracuseStep 4976437 = 466541) (by norm_num)
theorem B6635249 : Blo 1965435 6635249 := bstep (se 2 (by rfl) ⟨2488218, by rfl⟩ : syracuseStep 6635249 = 4976437) B4976437
theorem B4423499 : Blo 1965435 4423499 := bstep (se 1 (by rfl) ⟨3317624, by rfl⟩ : syracuseStep 4423499 = 6635249) B6635249
theorem B2948999 : Blo 1965435 2948999 := bstep (se 1 (by rfl) ⟨2211749, by rfl⟩ : syracuseStep 2948999 = 4423499) B4423499
theorem B1965999 : Blo 1965435 1965999 := bstep (se 1 (by rfl) ⟨1474499, by rfl⟩ : syracuseStep 1965999 = 2948999) B2948999
theorem B2949005 : Blo 1965435 2949005 := bbase (se 3 (by rfl) ⟨552938, by rfl⟩ : syracuseStep 2949005 = 1105877) (by norm_num)
theorem B1966003 : Blo 1965435 1966003 := bstep (se 1 (by rfl) ⟨1474502, by rfl⟩ : syracuseStep 1966003 = 2949005) B2949005
theorem B4423517 : Blo 1965435 4423517 := bbase (se 3 (by rfl) ⟨829409, by rfl⟩ : syracuseStep 4423517 = 1658819) (by norm_num)
theorem B2949011 : Blo 1965435 2949011 := bstep (se 1 (by rfl) ⟨2211758, by rfl⟩ : syracuseStep 2949011 = 4423517) B4423517
theorem B1966007 : Blo 1965435 1966007 := bstep (se 1 (by rfl) ⟨1474505, by rfl⟩ : syracuseStep 1966007 = 2949011) B2949011
theorem B3317645 : Blo 1965435 3317645 := bbase (se 3 (by rfl) ⟨622058, by rfl⟩ : syracuseStep 3317645 = 1244117) (by norm_num)
theorem B2211763 : Blo 1965435 2211763 := bstep (se 1 (by rfl) ⟨1658822, by rfl⟩ : syracuseStep 2211763 = 3317645) B3317645
theorem B2949017 : Blo 1965435 2949017 := bstep (se 2 (by rfl) ⟨1105881, by rfl⟩ : syracuseStep 2949017 = 2211763) B2211763
theorem B1966011 : Blo 1965435 1966011 := bstep (se 1 (by rfl) ⟨1474508, by rfl⟩ : syracuseStep 1966011 = 2949017) B2949017
theorem B13451669 : Blo 1965435 13451669 := bbase (se 6 (by rfl) ⟨315273, by rfl⟩ : syracuseStep 13451669 = 630547) (by norm_num)
theorem B8967779 : Blo 1965435 8967779 := bstep (se 1 (by rfl) ⟨6725834, by rfl⟩ : syracuseStep 8967779 = 13451669) B13451669
theorem B5978519 : Blo 1965435 5978519 := bstep (se 1 (by rfl) ⟨4483889, by rfl⟩ : syracuseStep 5978519 = 8967779) B8967779
theorem B3985679 : Blo 1965435 3985679 := bstep (se 1 (by rfl) ⟨2989259, by rfl⟩ : syracuseStep 3985679 = 5978519) B5978519
theorem B2657119 : Blo 1965435 2657119 := bstep (se 1 (by rfl) ⟨1992839, by rfl⟩ : syracuseStep 2657119 = 3985679) B3985679
theorem B3542825 : Blo 1965435 3542825 := bstep (se 2 (by rfl) ⟨1328559, by rfl⟩ : syracuseStep 3542825 = 2657119) B2657119
theorem B9447533 : Blo 1965435 9447533 := bstep (se 3 (by rfl) ⟨1771412, by rfl⟩ : syracuseStep 9447533 = 3542825) B3542825
theorem B6298355 : Blo 1965435 6298355 := bstep (se 1 (by rfl) ⟨4723766, by rfl⟩ : syracuseStep 6298355 = 9447533) B9447533
theorem B16795613 : Blo 1965435 16795613 := bstep (se 3 (by rfl) ⟨3149177, by rfl⟩ : syracuseStep 16795613 = 6298355) B6298355
theorem B11197075 : Blo 1965435 11197075 := bstep (se 1 (by rfl) ⟨8397806, by rfl⟩ : syracuseStep 11197075 = 16795613) B16795613
theorem B14929433 : Blo 1965435 14929433 := bstep (se 2 (by rfl) ⟨5598537, by rfl⟩ : syracuseStep 14929433 = 11197075) B11197075
theorem B9952955 : Blo 1965435 9952955 := bstep (se 1 (by rfl) ⟨7464716, by rfl⟩ : syracuseStep 9952955 = 14929433) B14929433
theorem B6635303 : Blo 1965435 6635303 := bstep (se 1 (by rfl) ⟨4976477, by rfl⟩ : syracuseStep 6635303 = 9952955) B9952955
theorem B4423535 : Blo 1965435 4423535 := bstep (se 1 (by rfl) ⟨3317651, by rfl⟩ : syracuseStep 4423535 = 6635303) B6635303
theorem B2949023 : Blo 1965435 2949023 := bstep (se 1 (by rfl) ⟨2211767, by rfl⟩ : syracuseStep 2949023 = 4423535) B4423535
theorem B1966015 : Blo 1965435 1966015 := bstep (se 1 (by rfl) ⟨1474511, by rfl⟩ : syracuseStep 1966015 = 2949023) B2949023
theorem B2949029 : Blo 1965435 2949029 := bbase (se 4 (by rfl) ⟨276471, by rfl⟩ : syracuseStep 2949029 = 552943) (by norm_num)
theorem B1966019 : Blo 1965435 1966019 := bstep (se 1 (by rfl) ⟨1474514, by rfl⟩ : syracuseStep 1966019 = 2949029) B2949029
theorem B2488249 : Blo 1965435 2488249 := bbase (se 2 (by rfl) ⟨933093, by rfl⟩ : syracuseStep 2488249 = 1866187) (by norm_num)
theorem B3317665 : Blo 1965435 3317665 := bstep (se 2 (by rfl) ⟨1244124, by rfl⟩ : syracuseStep 3317665 = 2488249) B2488249
theorem B4423553 : Blo 1965435 4423553 := bstep (se 2 (by rfl) ⟨1658832, by rfl⟩ : syracuseStep 4423553 = 3317665) B3317665
theorem B2949035 : Blo 1965435 2949035 := bstep (se 1 (by rfl) ⟨2211776, by rfl⟩ : syracuseStep 2949035 = 4423553) B4423553
theorem B1966023 : Blo 1965435 1966023 := bstep (se 1 (by rfl) ⟨1474517, by rfl⟩ : syracuseStep 1966023 = 2949035) B2949035
theorem B2211781 : Blo 1965435 2211781 := bbase (se 4 (by rfl) ⟨207354, by rfl⟩ : syracuseStep 2211781 = 414709) (by norm_num)
theorem B2949041 : Blo 1965435 2949041 := bstep (se 2 (by rfl) ⟨1105890, by rfl⟩ : syracuseStep 2949041 = 2211781) B2211781
theorem B1966027 : Blo 1965435 1966027 := bstep (se 1 (by rfl) ⟨1474520, by rfl⟩ : syracuseStep 1966027 = 2949041) B2949041
theorem B3732389 : Blo 1965435 3732389 := bbase (se 4 (by rfl) ⟨349911, by rfl⟩ : syracuseStep 3732389 = 699823) (by norm_num)
theorem B2488259 : Blo 1965435 2488259 := bstep (se 1 (by rfl) ⟨1866194, by rfl⟩ : syracuseStep 2488259 = 3732389) B3732389
theorem B6635357 : Blo 1965435 6635357 := bstep (se 3 (by rfl) ⟨1244129, by rfl⟩ : syracuseStep 6635357 = 2488259) B2488259
theorem B4423571 : Blo 1965435 4423571 := bstep (se 1 (by rfl) ⟨3317678, by rfl⟩ : syracuseStep 4423571 = 6635357) B6635357
theorem B2949047 : Blo 1965435 2949047 := bstep (se 1 (by rfl) ⟨2211785, by rfl⟩ : syracuseStep 2949047 = 4423571) B4423571
theorem B1966031 : Blo 1965435 1966031 := bstep (se 1 (by rfl) ⟨1474523, by rfl⟩ : syracuseStep 1966031 = 2949047) B2949047
theorem B2949053 : Blo 1965435 2949053 := bbase (se 3 (by rfl) ⟨552947, by rfl⟩ : syracuseStep 2949053 = 1105895) (by norm_num)
theorem B1966035 : Blo 1965435 1966035 := bstep (se 1 (by rfl) ⟨1474526, by rfl⟩ : syracuseStep 1966035 = 2949053) B2949053
theorem B4423589 : Blo 1965435 4423589 := bbase (se 4 (by rfl) ⟨414711, by rfl⟩ : syracuseStep 4423589 = 829423) (by norm_num)
theorem B2949059 : Blo 1965435 2949059 := bstep (se 1 (by rfl) ⟨2211794, by rfl⟩ : syracuseStep 2949059 = 4423589) B4423589
theorem B1966039 : Blo 1965435 1966039 := bstep (se 1 (by rfl) ⟨1474529, by rfl⟩ : syracuseStep 1966039 = 2949059) B2949059
theorem B4976549 : Blo 1965435 4976549 := bbase (se 4 (by rfl) ⟨466551, by rfl⟩ : syracuseStep 4976549 = 933103) (by norm_num)
theorem B3317699 : Blo 1965435 3317699 := bstep (se 1 (by rfl) ⟨2488274, by rfl⟩ : syracuseStep 3317699 = 4976549) B4976549
theorem B2211799 : Blo 1965435 2211799 := bstep (se 1 (by rfl) ⟨1658849, by rfl⟩ : syracuseStep 2211799 = 3317699) B3317699
theorem B2949065 : Blo 1965435 2949065 := bstep (se 2 (by rfl) ⟨1105899, by rfl⟩ : syracuseStep 2949065 = 2211799) B2211799
theorem B1966043 : Blo 1965435 1966043 := bstep (se 1 (by rfl) ⟨1474532, by rfl⟩ : syracuseStep 1966043 = 2949065) B2949065
theorem B5598629 : Blo 1965435 5598629 := bbase (se 4 (by rfl) ⟨524871, by rfl⟩ : syracuseStep 5598629 = 1049743) (by norm_num)
theorem B3732419 : Blo 1965435 3732419 := bstep (se 1 (by rfl) ⟨2799314, by rfl⟩ : syracuseStep 3732419 = 5598629) B5598629
theorem B9953117 : Blo 1965435 9953117 := bstep (se 3 (by rfl) ⟨1866209, by rfl⟩ : syracuseStep 9953117 = 3732419) B3732419
theorem B6635411 : Blo 1965435 6635411 := bstep (se 1 (by rfl) ⟨4976558, by rfl⟩ : syracuseStep 6635411 = 9953117) B9953117
theorem B4423607 : Blo 1965435 4423607 := bstep (se 1 (by rfl) ⟨3317705, by rfl⟩ : syracuseStep 4423607 = 6635411) B6635411
theorem B2949071 : Blo 1965435 2949071 := bstep (se 1 (by rfl) ⟨2211803, by rfl⟩ : syracuseStep 2949071 = 4423607) B4423607
theorem B1966047 : Blo 1965435 1966047 := bstep (se 1 (by rfl) ⟨1474535, by rfl⟩ : syracuseStep 1966047 = 2949071) B2949071
theorem B2949077 : Blo 1965435 2949077 := bbase (se 7 (by rfl) ⟨34559, by rfl⟩ : syracuseStep 2949077 = 69119) (by norm_num)
theorem B1966051 : Blo 1965435 1966051 := bstep (se 1 (by rfl) ⟨1474538, by rfl⟩ : syracuseStep 1966051 = 2949077) B2949077
theorem B7464869 : Blo 1965435 7464869 := bbase (se 4 (by rfl) ⟨699831, by rfl⟩ : syracuseStep 7464869 = 1399663) (by norm_num)
theorem B4976579 : Blo 1965435 4976579 := bstep (se 1 (by rfl) ⟨3732434, by rfl⟩ : syracuseStep 4976579 = 7464869) B7464869
theorem B3317719 : Blo 1965435 3317719 := bstep (se 1 (by rfl) ⟨2488289, by rfl⟩ : syracuseStep 3317719 = 4976579) B4976579
theorem B4423625 : Blo 1965435 4423625 := bstep (se 2 (by rfl) ⟨1658859, by rfl⟩ : syracuseStep 4423625 = 3317719) B3317719
theorem B2949083 : Blo 1965435 2949083 := bstep (se 1 (by rfl) ⟨2211812, by rfl⟩ : syracuseStep 2949083 = 4423625) B4423625
theorem B1966055 : Blo 1965435 1966055 := bstep (se 1 (by rfl) ⟨1474541, by rfl⟩ : syracuseStep 1966055 = 2949083) B2949083
theorem B2211817 : Blo 1965435 2211817 := bbase (se 2 (by rfl) ⟨829431, by rfl⟩ : syracuseStep 2211817 = 1658863) (by norm_num)
theorem B2949089 : Blo 1965435 2949089 := bstep (se 2 (by rfl) ⟨1105908, by rfl⟩ : syracuseStep 2949089 = 2211817) B2211817
theorem B1966059 : Blo 1965435 1966059 := bstep (se 1 (by rfl) ⟨1474544, by rfl⟩ : syracuseStep 1966059 = 2949089) B2949089
theorem B2989333 : Blo 1965435 2989333 := bbase (se 6 (by rfl) ⟨70062, by rfl⟩ : syracuseStep 2989333 = 140125) (by norm_num)
theorem B3985777 : Blo 1965435 3985777 := bstep (se 2 (by rfl) ⟨1494666, by rfl⟩ : syracuseStep 3985777 = 2989333) B2989333
theorem B5314369 : Blo 1965435 5314369 := bstep (se 2 (by rfl) ⟨1992888, by rfl⟩ : syracuseStep 5314369 = 3985777) B3985777
theorem B7085825 : Blo 1965435 7085825 := bstep (se 2 (by rfl) ⟨2657184, by rfl⟩ : syracuseStep 7085825 = 5314369) B5314369
theorem B4723883 : Blo 1965435 4723883 := bstep (se 1 (by rfl) ⟨3542912, by rfl⟩ : syracuseStep 4723883 = 7085825) B7085825
theorem B3149255 : Blo 1965435 3149255 := bstep (se 1 (by rfl) ⟨2361941, by rfl⟩ : syracuseStep 3149255 = 4723883) B4723883
theorem B2099503 : Blo 1965435 2099503 := bstep (se 1 (by rfl) ⟨1574627, by rfl⟩ : syracuseStep 2099503 = 3149255) B3149255
theorem B11197349 : Blo 1965435 11197349 := bstep (se 4 (by rfl) ⟨1049751, by rfl⟩ : syracuseStep 11197349 = 2099503) B2099503
theorem B7464899 : Blo 1965435 7464899 := bstep (se 1 (by rfl) ⟨5598674, by rfl⟩ : syracuseStep 7464899 = 11197349) B11197349
theorem B4976599 : Blo 1965435 4976599 := bstep (se 1 (by rfl) ⟨3732449, by rfl⟩ : syracuseStep 4976599 = 7464899) B7464899
theorem B6635465 : Blo 1965435 6635465 := bstep (se 2 (by rfl) ⟨2488299, by rfl⟩ : syracuseStep 6635465 = 4976599) B4976599
theorem B4423643 : Blo 1965435 4423643 := bstep (se 1 (by rfl) ⟨3317732, by rfl⟩ : syracuseStep 4423643 = 6635465) B6635465
theorem B2949095 : Blo 1965435 2949095 := bstep (se 1 (by rfl) ⟨2211821, by rfl⟩ : syracuseStep 2949095 = 4423643) B4423643
theorem B1966063 : Blo 1965435 1966063 := bstep (se 1 (by rfl) ⟨1474547, by rfl⟩ : syracuseStep 1966063 = 2949095) B2949095
theorem B2949101 : Blo 1965435 2949101 := bbase (se 3 (by rfl) ⟨552956, by rfl⟩ : syracuseStep 2949101 = 1105913) (by norm_num)
theorem B1966067 : Blo 1965435 1966067 := bstep (se 1 (by rfl) ⟨1474550, by rfl⟩ : syracuseStep 1966067 = 2949101) B2949101
theorem B4423661 : Blo 1965435 4423661 := bbase (se 3 (by rfl) ⟨829436, by rfl⟩ : syracuseStep 4423661 = 1658873) (by norm_num)
theorem B2949107 : Blo 1965435 2949107 := bstep (se 1 (by rfl) ⟨2211830, by rfl⟩ : syracuseStep 2949107 = 4423661) B4423661
theorem B1966071 : Blo 1965435 1966071 := bstep (se 1 (by rfl) ⟨1474553, by rfl⟩ : syracuseStep 1966071 = 2949107) B2949107
theorem B7971605 : Blo 1965435 7971605 := bbase (se 6 (by rfl) ⟨186834, by rfl⟩ : syracuseStep 7971605 = 373669) (by norm_num)
theorem B5314403 : Blo 1965435 5314403 := bstep (se 1 (by rfl) ⟨3985802, by rfl⟩ : syracuseStep 5314403 = 7971605) B7971605
theorem B3542935 : Blo 1965435 3542935 := bstep (se 1 (by rfl) ⟨2657201, by rfl⟩ : syracuseStep 3542935 = 5314403) B5314403
theorem B4723913 : Blo 1965435 4723913 := bstep (se 2 (by rfl) ⟨1771467, by rfl⟩ : syracuseStep 4723913 = 3542935) B3542935
theorem B3149275 : Blo 1965435 3149275 := bstep (se 1 (by rfl) ⟨2361956, by rfl⟩ : syracuseStep 3149275 = 4723913) B4723913
theorem B4199033 : Blo 1965435 4199033 := bstep (se 2 (by rfl) ⟨1574637, by rfl⟩ : syracuseStep 4199033 = 3149275) B3149275
theorem B2799355 : Blo 1965435 2799355 := bstep (se 1 (by rfl) ⟨2099516, by rfl⟩ : syracuseStep 2799355 = 4199033) B4199033
theorem B3732473 : Blo 1965435 3732473 := bstep (se 2 (by rfl) ⟨1399677, by rfl⟩ : syracuseStep 3732473 = 2799355) B2799355
theorem B2488315 : Blo 1965435 2488315 := bstep (se 1 (by rfl) ⟨1866236, by rfl⟩ : syracuseStep 2488315 = 3732473) B3732473
theorem B3317753 : Blo 1965435 3317753 := bstep (se 2 (by rfl) ⟨1244157, by rfl⟩ : syracuseStep 3317753 = 2488315) B2488315
theorem B2211835 : Blo 1965435 2211835 := bstep (se 1 (by rfl) ⟨1658876, by rfl⟩ : syracuseStep 2211835 = 3317753) B3317753
theorem B2949113 : Blo 1965435 2949113 := bstep (se 2 (by rfl) ⟨1105917, by rfl⟩ : syracuseStep 2949113 = 2211835) B2211835
theorem B1966075 : Blo 1965435 1966075 := bstep (se 1 (by rfl) ⟨1474556, by rfl⟩ : syracuseStep 1966075 = 2949113) B2949113
theorem B15340085 : Blo 1965435 15340085 := bbase (se 5 (by rfl) ⟨719066, by rfl⟩ : syracuseStep 15340085 = 1438133) (by norm_num)
theorem B163627573 : Blo 1965435 163627573 := bstep (se 5 (by rfl) ⟨7670042, by rfl⟩ : syracuseStep 163627573 = 15340085) B15340085
theorem B218170097 : Blo 1965435 218170097 := bstep (se 2 (by rfl) ⟨81813786, by rfl⟩ : syracuseStep 218170097 = 163627573) B163627573
theorem B145446731 : Blo 1965435 145446731 := bstep (se 1 (by rfl) ⟨109085048, by rfl⟩ : syracuseStep 145446731 = 218170097) B218170097
theorem B96964487 : Blo 1965435 96964487 := bstep (se 1 (by rfl) ⟨72723365, by rfl⟩ : syracuseStep 96964487 = 145446731) B145446731
theorem B64642991 : Blo 1965435 64642991 := bstep (se 1 (by rfl) ⟨48482243, by rfl⟩ : syracuseStep 64642991 = 96964487) B96964487
theorem B689525237 : Blo 1965435 689525237 := bstep (se 5 (by rfl) ⟨32321495, by rfl⟩ : syracuseStep 689525237 = 64642991) B64642991
theorem B1838733965 : Blo 1965435 1838733965 := bstep (se 3 (by rfl) ⟨344762618, by rfl⟩ : syracuseStep 1838733965 = 689525237) B689525237
theorem B1225822643 : Blo 1965435 1225822643 := bstep (se 1 (by rfl) ⟨919366982, by rfl⟩ : syracuseStep 1225822643 = 1838733965) B1838733965
theorem B817215095 : Blo 1965435 817215095 := bstep (se 1 (by rfl) ⟨612911321, by rfl⟩ : syracuseStep 817215095 = 1225822643) B1225822643
theorem B544810063 : Blo 1965435 544810063 := bstep (se 1 (by rfl) ⟨408607547, by rfl⟩ : syracuseStep 544810063 = 817215095) B817215095
theorem B726413417 : Blo 1965435 726413417 := bstep (se 2 (by rfl) ⟨272405031, by rfl⟩ : syracuseStep 726413417 = 544810063) B544810063
theorem B484275611 : Blo 1965435 484275611 := bstep (se 1 (by rfl) ⟨363206708, by rfl⟩ : syracuseStep 484275611 = 726413417) B726413417
theorem B1291401629 : Blo 1965435 1291401629 := bstep (se 3 (by rfl) ⟨242137805, by rfl⟩ : syracuseStep 1291401629 = 484275611) B484275611
theorem B860934419 : Blo 1965435 860934419 := bstep (se 1 (by rfl) ⟨645700814, by rfl⟩ : syracuseStep 860934419 = 1291401629) B1291401629
theorem B573956279 : Blo 1965435 573956279 := bstep (se 1 (by rfl) ⟨430467209, by rfl⟩ : syracuseStep 573956279 = 860934419) B860934419
theorem B382637519 : Blo 1965435 382637519 := bstep (se 1 (by rfl) ⟨286978139, by rfl⟩ : syracuseStep 382637519 = 573956279) B573956279
theorem B255091679 : Blo 1965435 255091679 := bstep (se 1 (by rfl) ⟨191318759, by rfl⟩ : syracuseStep 255091679 = 382637519) B382637519
theorem B170061119 : Blo 1965435 170061119 := bstep (se 1 (by rfl) ⟨127545839, by rfl⟩ : syracuseStep 170061119 = 255091679) B255091679
theorem B113374079 : Blo 1965435 113374079 := bstep (se 1 (by rfl) ⟨85030559, by rfl⟩ : syracuseStep 113374079 = 170061119) B170061119
theorem B75582719 : Blo 1965435 75582719 := bstep (se 1 (by rfl) ⟨56687039, by rfl⟩ : syracuseStep 75582719 = 113374079) B113374079
theorem B50388479 : Blo 1965435 50388479 := bstep (se 1 (by rfl) ⟨37791359, by rfl⟩ : syracuseStep 50388479 = 75582719) B75582719
theorem B33592319 : Blo 1965435 33592319 := bstep (se 1 (by rfl) ⟨25194239, by rfl⟩ : syracuseStep 33592319 = 50388479) B50388479
theorem B22394879 : Blo 1965435 22394879 := bstep (se 1 (by rfl) ⟨16796159, by rfl⟩ : syracuseStep 22394879 = 33592319) B33592319
theorem B14929919 : Blo 1965435 14929919 := bstep (se 1 (by rfl) ⟨11197439, by rfl⟩ : syracuseStep 14929919 = 22394879) B22394879
theorem B9953279 : Blo 1965435 9953279 := bstep (se 1 (by rfl) ⟨7464959, by rfl⟩ : syracuseStep 9953279 = 14929919) B14929919
theorem B6635519 : Blo 1965435 6635519 := bstep (se 1 (by rfl) ⟨4976639, by rfl⟩ : syracuseStep 6635519 = 9953279) B9953279
theorem B4423679 : Blo 1965435 4423679 := bstep (se 1 (by rfl) ⟨3317759, by rfl⟩ : syracuseStep 4423679 = 6635519) B6635519
theorem B2949119 : Blo 1965435 2949119 := bstep (se 1 (by rfl) ⟨2211839, by rfl⟩ : syracuseStep 2949119 = 4423679) B4423679
theorem B1966079 : Blo 1965435 1966079 := bstep (se 1 (by rfl) ⟨1474559, by rfl⟩ : syracuseStep 1966079 = 2949119) B2949119
theorem B2949125 : Blo 1965435 2949125 := bbase (se 4 (by rfl) ⟨276480, by rfl⟩ : syracuseStep 2949125 = 552961) (by norm_num)
theorem B1966083 : Blo 1965435 1966083 := bstep (se 1 (by rfl) ⟨1474562, by rfl⟩ : syracuseStep 1966083 = 2949125) B2949125
theorem B3317773 : Blo 1965435 3317773 := bbase (se 3 (by rfl) ⟨622082, by rfl⟩ : syracuseStep 3317773 = 1244165) (by norm_num)
theorem B4423697 : Blo 1965435 4423697 := bstep (se 2 (by rfl) ⟨1658886, by rfl⟩ : syracuseStep 4423697 = 3317773) B3317773
theorem B2949131 : Blo 1965435 2949131 := bstep (se 1 (by rfl) ⟨2211848, by rfl⟩ : syracuseStep 2949131 = 4423697) B4423697
theorem B1966087 : Blo 1965435 1966087 := bstep (se 1 (by rfl) ⟨1474565, by rfl⟩ : syracuseStep 1966087 = 2949131) B2949131
theorem B2211853 : Blo 1965435 2211853 := bbase (se 3 (by rfl) ⟨414722, by rfl⟩ : syracuseStep 2211853 = 829445) (by norm_num)
theorem B2949137 : Blo 1965435 2949137 := bstep (se 2 (by rfl) ⟨1105926, by rfl⟩ : syracuseStep 2949137 = 2211853) B2211853
theorem B1966091 : Blo 1965435 1966091 := bstep (se 1 (by rfl) ⟨1474568, by rfl⟩ : syracuseStep 1966091 = 2949137) B2949137
theorem B6635573 : Blo 1965435 6635573 := bbase (se 5 (by rfl) ⟨311042, by rfl⟩ : syracuseStep 6635573 = 622085) (by norm_num)
theorem B4423715 : Blo 1965435 4423715 := bstep (se 1 (by rfl) ⟨3317786, by rfl⟩ : syracuseStep 4423715 = 6635573) B6635573
theorem B2949143 : Blo 1965435 2949143 := bstep (se 1 (by rfl) ⟨2211857, by rfl⟩ : syracuseStep 2949143 = 4423715) B4423715
theorem B1966095 : Blo 1965435 1966095 := bstep (se 1 (by rfl) ⟨1474571, by rfl⟩ : syracuseStep 1966095 = 2949143) B2949143
theorem B2949149 : Blo 1965435 2949149 := bbase (se 3 (by rfl) ⟨552965, by rfl⟩ : syracuseStep 2949149 = 1105931) (by norm_num)
theorem B1966099 : Blo 1965435 1966099 := bstep (se 1 (by rfl) ⟨1474574, by rfl⟩ : syracuseStep 1966099 = 2949149) B2949149
theorem B4423733 : Blo 1965435 4423733 := bbase (se 5 (by rfl) ⟨207362, by rfl⟩ : syracuseStep 4423733 = 414725) (by norm_num)
theorem B2949155 : Blo 1965435 2949155 := bstep (se 1 (by rfl) ⟨2211866, by rfl⟩ : syracuseStep 2949155 = 4423733) B4423733
theorem B1966103 : Blo 1965435 1966103 := bstep (se 1 (by rfl) ⟨1474577, by rfl⟩ : syracuseStep 1966103 = 2949155) B2949155
theorem B7182661 : Blo 1965435 7182661 := bbase (se 4 (by rfl) ⟨673374, by rfl⟩ : syracuseStep 7182661 = 1346749) (by norm_num)
theorem B9576881 : Blo 1965435 9576881 := bstep (se 2 (by rfl) ⟨3591330, by rfl⟩ : syracuseStep 9576881 = 7182661) B7182661
theorem B6384587 : Blo 1965435 6384587 := bstep (se 1 (by rfl) ⟨4788440, by rfl⟩ : syracuseStep 6384587 = 9576881) B9576881
theorem B17025565 : Blo 1965435 17025565 := bstep (se 3 (by rfl) ⟨3192293, by rfl⟩ : syracuseStep 17025565 = 6384587) B6384587
theorem B22700753 : Blo 1965435 22700753 := bstep (se 2 (by rfl) ⟨8512782, by rfl⟩ : syracuseStep 22700753 = 17025565) B17025565
theorem B15133835 : Blo 1965435 15133835 := bstep (se 1 (by rfl) ⟨11350376, by rfl⟩ : syracuseStep 15133835 = 22700753) B22700753
theorem B40356893 : Blo 1965435 40356893 := bstep (se 3 (by rfl) ⟨7566917, by rfl⟩ : syracuseStep 40356893 = 15133835) B15133835
theorem B26904595 : Blo 1965435 26904595 := bstep (se 1 (by rfl) ⟨20178446, by rfl⟩ : syracuseStep 26904595 = 40356893) B40356893
theorem B35872793 : Blo 1965435 35872793 := bstep (se 2 (by rfl) ⟨13452297, by rfl⟩ : syracuseStep 35872793 = 26904595) B26904595
theorem B23915195 : Blo 1965435 23915195 := bstep (se 1 (by rfl) ⟨17936396, by rfl⟩ : syracuseStep 23915195 = 35872793) B35872793
theorem B15943463 : Blo 1965435 15943463 := bstep (se 1 (by rfl) ⟨11957597, by rfl⟩ : syracuseStep 15943463 = 23915195) B23915195
theorem B10628975 : Blo 1965435 10628975 := bstep (se 1 (by rfl) ⟨7971731, by rfl⟩ : syracuseStep 10628975 = 15943463) B15943463
theorem B7085983 : Blo 1965435 7085983 := bstep (se 1 (by rfl) ⟨5314487, by rfl⟩ : syracuseStep 7085983 = 10628975) B10628975
theorem B9447977 : Blo 1965435 9447977 := bstep (se 2 (by rfl) ⟨3542991, by rfl⟩ : syracuseStep 9447977 = 7085983) B7085983
theorem B6298651 : Blo 1965435 6298651 := bstep (se 1 (by rfl) ⟨4723988, by rfl⟩ : syracuseStep 6298651 = 9447977) B9447977
theorem B8398201 : Blo 1965435 8398201 := bstep (se 2 (by rfl) ⟨3149325, by rfl⟩ : syracuseStep 8398201 = 6298651) B6298651
theorem B11197601 : Blo 1965435 11197601 := bstep (se 2 (by rfl) ⟨4199100, by rfl⟩ : syracuseStep 11197601 = 8398201) B8398201
theorem B7465067 : Blo 1965435 7465067 := bstep (se 1 (by rfl) ⟨5598800, by rfl⟩ : syracuseStep 7465067 = 11197601) B11197601
theorem B4976711 : Blo 1965435 4976711 := bstep (se 1 (by rfl) ⟨3732533, by rfl⟩ : syracuseStep 4976711 = 7465067) B7465067
theorem B3317807 : Blo 1965435 3317807 := bstep (se 1 (by rfl) ⟨2488355, by rfl⟩ : syracuseStep 3317807 = 4976711) B4976711
theorem B2211871 : Blo 1965435 2211871 := bstep (se 1 (by rfl) ⟨1658903, by rfl⟩ : syracuseStep 2211871 = 3317807) B3317807
theorem B2949161 : Blo 1965435 2949161 := bstep (se 2 (by rfl) ⟨1105935, by rfl⟩ : syracuseStep 2949161 = 2211871) B2211871
theorem B1966107 : Blo 1965435 1966107 := bstep (se 1 (by rfl) ⟨1474580, by rfl⟩ : syracuseStep 1966107 = 2949161) B2949161
theorem B2989405 : Blo 1965435 2989405 := bbase (se 3 (by rfl) ⟨560513, by rfl⟩ : syracuseStep 2989405 = 1121027) (by norm_num)
theorem B15943493 : Blo 1965435 15943493 := bstep (se 4 (by rfl) ⟨1494702, by rfl⟩ : syracuseStep 15943493 = 2989405) B2989405
theorem B10628995 : Blo 1965435 10628995 := bstep (se 1 (by rfl) ⟨7971746, by rfl⟩ : syracuseStep 10628995 = 15943493) B15943493
theorem B14171993 : Blo 1965435 14171993 := bstep (se 2 (by rfl) ⟨5314497, by rfl⟩ : syracuseStep 14171993 = 10628995) B10628995
theorem B9447995 : Blo 1965435 9447995 := bstep (se 1 (by rfl) ⟨7085996, by rfl⟩ : syracuseStep 9447995 = 14171993) B14171993
theorem B6298663 : Blo 1965435 6298663 := bstep (se 1 (by rfl) ⟨4723997, by rfl⟩ : syracuseStep 6298663 = 9447995) B9447995
theorem B8398217 : Blo 1965435 8398217 := bstep (se 2 (by rfl) ⟨3149331, by rfl⟩ : syracuseStep 8398217 = 6298663) B6298663
theorem B5598811 : Blo 1965435 5598811 := bstep (se 1 (by rfl) ⟨4199108, by rfl⟩ : syracuseStep 5598811 = 8398217) B8398217
theorem B7465081 : Blo 1965435 7465081 := bstep (se 2 (by rfl) ⟨2799405, by rfl⟩ : syracuseStep 7465081 = 5598811) B5598811
theorem B9953441 : Blo 1965435 9953441 := bstep (se 2 (by rfl) ⟨3732540, by rfl⟩ : syracuseStep 9953441 = 7465081) B7465081
theorem B6635627 : Blo 1965435 6635627 := bstep (se 1 (by rfl) ⟨4976720, by rfl⟩ : syracuseStep 6635627 = 9953441) B9953441
theorem B4423751 : Blo 1965435 4423751 := bstep (se 1 (by rfl) ⟨3317813, by rfl⟩ : syracuseStep 4423751 = 6635627) B6635627
theorem B2949167 : Blo 1965435 2949167 := bstep (se 1 (by rfl) ⟨2211875, by rfl⟩ : syracuseStep 2949167 = 4423751) B4423751
theorem B1966111 : Blo 1965435 1966111 := bstep (se 1 (by rfl) ⟨1474583, by rfl⟩ : syracuseStep 1966111 = 2949167) B2949167
theorem B2949173 : Blo 1965435 2949173 := bbase (se 5 (by rfl) ⟨138242, by rfl⟩ : syracuseStep 2949173 = 276485) (by norm_num)
theorem B1966115 : Blo 1965435 1966115 := bstep (se 1 (by rfl) ⟨1474586, by rfl⟩ : syracuseStep 1966115 = 2949173) B2949173
theorem B4976741 : Blo 1965435 4976741 := bbase (se 4 (by rfl) ⟨466569, by rfl⟩ : syracuseStep 4976741 = 933139) (by norm_num)
theorem B3317827 : Blo 1965435 3317827 := bstep (se 1 (by rfl) ⟨2488370, by rfl⟩ : syracuseStep 3317827 = 4976741) B4976741
theorem B4423769 : Blo 1965435 4423769 := bstep (se 2 (by rfl) ⟨1658913, by rfl⟩ : syracuseStep 4423769 = 3317827) B3317827
theorem B2949179 : Blo 1965435 2949179 := bstep (se 1 (by rfl) ⟨2211884, by rfl⟩ : syracuseStep 2949179 = 4423769) B4423769
theorem B1966119 : Blo 1965435 1966119 := bstep (se 1 (by rfl) ⟨1474589, by rfl⟩ : syracuseStep 1966119 = 2949179) B2949179
theorem B2211889 : Blo 1965435 2211889 := bbase (se 2 (by rfl) ⟨829458, by rfl⟩ : syracuseStep 2211889 = 1658917) (by norm_num)
theorem B2949185 : Blo 1965435 2949185 := bstep (se 2 (by rfl) ⟨1105944, by rfl⟩ : syracuseStep 2949185 = 2211889) B2211889
theorem B1966123 : Blo 1965435 1966123 := bstep (se 1 (by rfl) ⟨1474592, by rfl⟩ : syracuseStep 1966123 = 2949185) B2949185
theorem B2394245 : Blo 1965435 2394245 := bbase (se 4 (by rfl) ⟨224460, by rfl⟩ : syracuseStep 2394245 = 448921) (by norm_num)
theorem B6384653 : Blo 1965435 6384653 := bstep (se 3 (by rfl) ⟨1197122, by rfl⟩ : syracuseStep 6384653 = 2394245) B2394245
theorem B4256435 : Blo 1965435 4256435 := bstep (se 1 (by rfl) ⟨3192326, by rfl⟩ : syracuseStep 4256435 = 6384653) B6384653
theorem B11350493 : Blo 1965435 11350493 := bstep (se 3 (by rfl) ⟨2128217, by rfl⟩ : syracuseStep 11350493 = 4256435) B4256435
theorem B7566995 : Blo 1965435 7566995 := bstep (se 1 (by rfl) ⟨5675246, by rfl⟩ : syracuseStep 7566995 = 11350493) B11350493
theorem B5044663 : Blo 1965435 5044663 := bstep (se 1 (by rfl) ⟨3783497, by rfl⟩ : syracuseStep 5044663 = 7566995) B7566995
theorem B26904869 : Blo 1965435 26904869 := bstep (se 4 (by rfl) ⟨2522331, by rfl⟩ : syracuseStep 26904869 = 5044663) B5044663
theorem B17936579 : Blo 1965435 17936579 := bstep (se 1 (by rfl) ⟨13452434, by rfl⟩ : syracuseStep 17936579 = 26904869) B26904869
theorem B11957719 : Blo 1965435 11957719 := bstep (se 1 (by rfl) ⟨8968289, by rfl⟩ : syracuseStep 11957719 = 17936579) B17936579
theorem B15943625 : Blo 1965435 15943625 := bstep (se 2 (by rfl) ⟨5978859, by rfl⟩ : syracuseStep 15943625 = 11957719) B11957719
theorem B10629083 : Blo 1965435 10629083 := bstep (se 1 (by rfl) ⟨7971812, by rfl⟩ : syracuseStep 10629083 = 15943625) B15943625
theorem B7086055 : Blo 1965435 7086055 := bstep (se 1 (by rfl) ⟨5314541, by rfl⟩ : syracuseStep 7086055 = 10629083) B10629083
theorem B9448073 : Blo 1965435 9448073 := bstep (se 2 (by rfl) ⟨3543027, by rfl⟩ : syracuseStep 9448073 = 7086055) B7086055
theorem B6298715 : Blo 1965435 6298715 := bstep (se 1 (by rfl) ⟨4724036, by rfl⟩ : syracuseStep 6298715 = 9448073) B9448073
theorem B4199143 : Blo 1965435 4199143 := bstep (se 1 (by rfl) ⟨3149357, by rfl⟩ : syracuseStep 4199143 = 6298715) B6298715
theorem B5598857 : Blo 1965435 5598857 := bstep (se 2 (by rfl) ⟨2099571, by rfl⟩ : syracuseStep 5598857 = 4199143) B4199143
theorem B3732571 : Blo 1965435 3732571 := bstep (se 1 (by rfl) ⟨2799428, by rfl⟩ : syracuseStep 3732571 = 5598857) B5598857
theorem B4976761 : Blo 1965435 4976761 := bstep (se 2 (by rfl) ⟨1866285, by rfl⟩ : syracuseStep 4976761 = 3732571) B3732571
theorem B6635681 : Blo 1965435 6635681 := bstep (se 2 (by rfl) ⟨2488380, by rfl⟩ : syracuseStep 6635681 = 4976761) B4976761
theorem B4423787 : Blo 1965435 4423787 := bstep (se 1 (by rfl) ⟨3317840, by rfl⟩ : syracuseStep 4423787 = 6635681) B6635681
theorem B2949191 : Blo 1965435 2949191 := bstep (se 1 (by rfl) ⟨2211893, by rfl⟩ : syracuseStep 2949191 = 4423787) B4423787
theorem B1966127 : Blo 1965435 1966127 := bstep (se 1 (by rfl) ⟨1474595, by rfl⟩ : syracuseStep 1966127 = 2949191) B2949191
theorem B2949197 : Blo 1965435 2949197 := bbase (se 3 (by rfl) ⟨552974, by rfl⟩ : syracuseStep 2949197 = 1105949) (by norm_num)
theorem B1966131 : Blo 1965435 1966131 := bstep (se 1 (by rfl) ⟨1474598, by rfl⟩ : syracuseStep 1966131 = 2949197) B2949197
theorem B4423805 : Blo 1965435 4423805 := bbase (se 3 (by rfl) ⟨829463, by rfl⟩ : syracuseStep 4423805 = 1658927) (by norm_num)
theorem B2949203 : Blo 1965435 2949203 := bstep (se 1 (by rfl) ⟨2211902, by rfl⟩ : syracuseStep 2949203 = 4423805) B4423805
theorem B1966135 : Blo 1965435 1966135 := bstep (se 1 (by rfl) ⟨1474601, by rfl⟩ : syracuseStep 1966135 = 2949203) B2949203
theorem B3317861 : Blo 1965435 3317861 := bbase (se 4 (by rfl) ⟨311049, by rfl⟩ : syracuseStep 3317861 = 622099) (by norm_num)
theorem B2211907 : Blo 1965435 2211907 := bstep (se 1 (by rfl) ⟨1658930, by rfl⟩ : syracuseStep 2211907 = 3317861) B3317861
theorem B2949209 : Blo 1965435 2949209 := bstep (se 2 (by rfl) ⟨1105953, by rfl⟩ : syracuseStep 2949209 = 2211907) B2211907
theorem B1966139 : Blo 1965435 1966139 := bstep (se 1 (by rfl) ⟨1474604, by rfl⟩ : syracuseStep 1966139 = 2949209) B2949209
theorem B2522353 : Blo 1965435 2522353 := bbase (se 2 (by rfl) ⟨945882, by rfl⟩ : syracuseStep 2522353 = 1891765) (by norm_num)
theorem B3363137 : Blo 1965435 3363137 := bstep (se 2 (by rfl) ⟨1261176, by rfl⟩ : syracuseStep 3363137 = 2522353) B2522353
theorem B2242091 : Blo 1965435 2242091 := bstep (se 1 (by rfl) ⟨1681568, by rfl⟩ : syracuseStep 2242091 = 3363137) B3363137
theorem B5978909 : Blo 1965435 5978909 := bstep (se 3 (by rfl) ⟨1121045, by rfl⟩ : syracuseStep 5978909 = 2242091) B2242091
theorem B3985939 : Blo 1965435 3985939 := bstep (se 1 (by rfl) ⟨2989454, by rfl⟩ : syracuseStep 3985939 = 5978909) B5978909
theorem B5314585 : Blo 1965435 5314585 := bstep (se 2 (by rfl) ⟨1992969, by rfl⟩ : syracuseStep 5314585 = 3985939) B3985939
theorem B7086113 : Blo 1965435 7086113 := bstep (se 2 (by rfl) ⟨2657292, by rfl⟩ : syracuseStep 7086113 = 5314585) B5314585
theorem B4724075 : Blo 1965435 4724075 := bstep (se 1 (by rfl) ⟨3543056, by rfl⟩ : syracuseStep 4724075 = 7086113) B7086113
theorem B3149383 : Blo 1965435 3149383 := bstep (se 1 (by rfl) ⟨2362037, by rfl⟩ : syracuseStep 3149383 = 4724075) B4724075
theorem B4199177 : Blo 1965435 4199177 := bstep (se 2 (by rfl) ⟨1574691, by rfl⟩ : syracuseStep 4199177 = 3149383) B3149383
theorem B2799451 : Blo 1965435 2799451 := bstep (se 1 (by rfl) ⟨2099588, by rfl⟩ : syracuseStep 2799451 = 4199177) B4199177
theorem B14930405 : Blo 1965435 14930405 := bstep (se 4 (by rfl) ⟨1399725, by rfl⟩ : syracuseStep 14930405 = 2799451) B2799451
theorem B9953603 : Blo 1965435 9953603 := bstep (se 1 (by rfl) ⟨7465202, by rfl⟩ : syracuseStep 9953603 = 14930405) B14930405
theorem B6635735 : Blo 1965435 6635735 := bstep (se 1 (by rfl) ⟨4976801, by rfl⟩ : syracuseStep 6635735 = 9953603) B9953603
theorem B4423823 : Blo 1965435 4423823 := bstep (se 1 (by rfl) ⟨3317867, by rfl⟩ : syracuseStep 4423823 = 6635735) B6635735
theorem B2949215 : Blo 1965435 2949215 := bstep (se 1 (by rfl) ⟨2211911, by rfl⟩ : syracuseStep 2949215 = 4423823) B4423823
theorem B1966143 : Blo 1965435 1966143 := bstep (se 1 (by rfl) ⟨1474607, by rfl⟩ : syracuseStep 1966143 = 2949215) B2949215
theorem B2949221 : Blo 1965435 2949221 := bbase (se 4 (by rfl) ⟨276489, by rfl⟩ : syracuseStep 2949221 = 552979) (by norm_num)
theorem B1966147 : Blo 1965435 1966147 := bstep (se 1 (by rfl) ⟨1474610, by rfl⟩ : syracuseStep 1966147 = 2949221) B2949221
theorem B15340661 : Blo 1965435 15340661 := bbase (se 5 (by rfl) ⟨719093, by rfl⟩ : syracuseStep 15340661 = 1438187) (by norm_num)
theorem B10227107 : Blo 1965435 10227107 := bstep (se 1 (by rfl) ⟨7670330, by rfl⟩ : syracuseStep 10227107 = 15340661) B15340661
theorem B27272285 : Blo 1965435 27272285 := bstep (se 3 (by rfl) ⟨5113553, by rfl⟩ : syracuseStep 27272285 = 10227107) B10227107
theorem B18181523 : Blo 1965435 18181523 := bstep (se 1 (by rfl) ⟨13636142, by rfl⟩ : syracuseStep 18181523 = 27272285) B27272285
theorem B12121015 : Blo 1965435 12121015 := bstep (se 1 (by rfl) ⟨9090761, by rfl⟩ : syracuseStep 12121015 = 18181523) B18181523
theorem B16161353 : Blo 1965435 16161353 := bstep (se 2 (by rfl) ⟨6060507, by rfl⟩ : syracuseStep 16161353 = 12121015) B12121015
theorem B10774235 : Blo 1965435 10774235 := bstep (se 1 (by rfl) ⟨8080676, by rfl⟩ : syracuseStep 10774235 = 16161353) B16161353
theorem B28731293 : Blo 1965435 28731293 := bstep (se 3 (by rfl) ⟨5387117, by rfl⟩ : syracuseStep 28731293 = 10774235) B10774235
theorem B19154195 : Blo 1965435 19154195 := bstep (se 1 (by rfl) ⟨14365646, by rfl⟩ : syracuseStep 19154195 = 28731293) B28731293
theorem B12769463 : Blo 1965435 12769463 := bstep (se 1 (by rfl) ⟨9577097, by rfl⟩ : syracuseStep 12769463 = 19154195) B19154195
theorem B8512975 : Blo 1965435 8512975 := bstep (se 1 (by rfl) ⟨6384731, by rfl⟩ : syracuseStep 8512975 = 12769463) B12769463
theorem B11350633 : Blo 1965435 11350633 := bstep (se 2 (by rfl) ⟨4256487, by rfl⟩ : syracuseStep 11350633 = 8512975) B8512975
theorem B15134177 : Blo 1965435 15134177 := bstep (se 2 (by rfl) ⟨5675316, by rfl⟩ : syracuseStep 15134177 = 11350633) B11350633
theorem B10089451 : Blo 1965435 10089451 := bstep (se 1 (by rfl) ⟨7567088, by rfl⟩ : syracuseStep 10089451 = 15134177) B15134177
theorem B53810405 : Blo 1965435 53810405 := bstep (se 4 (by rfl) ⟨5044725, by rfl⟩ : syracuseStep 53810405 = 10089451) B10089451
theorem B35873603 : Blo 1965435 35873603 := bstep (se 1 (by rfl) ⟨26905202, by rfl⟩ : syracuseStep 35873603 = 53810405) B53810405
theorem B23915735 : Blo 1965435 23915735 := bstep (se 1 (by rfl) ⟨17936801, by rfl⟩ : syracuseStep 23915735 = 35873603) B35873603
theorem B15943823 : Blo 1965435 15943823 := bstep (se 1 (by rfl) ⟨11957867, by rfl⟩ : syracuseStep 15943823 = 23915735) B23915735
theorem B10629215 : Blo 1965435 10629215 := bstep (se 1 (by rfl) ⟨7971911, by rfl⟩ : syracuseStep 10629215 = 15943823) B15943823
theorem B7086143 : Blo 1965435 7086143 := bstep (se 1 (by rfl) ⟨5314607, by rfl⟩ : syracuseStep 7086143 = 10629215) B10629215
theorem B4724095 : Blo 1965435 4724095 := bstep (se 1 (by rfl) ⟨3543071, by rfl⟩ : syracuseStep 4724095 = 7086143) B7086143
theorem B6298793 : Blo 1965435 6298793 := bstep (se 2 (by rfl) ⟨2362047, by rfl⟩ : syracuseStep 6298793 = 4724095) B4724095
theorem B4199195 : Blo 1965435 4199195 := bstep (se 1 (by rfl) ⟨3149396, by rfl⟩ : syracuseStep 4199195 = 6298793) B6298793
theorem B2799463 : Blo 1965435 2799463 := bstep (se 1 (by rfl) ⟨2099597, by rfl⟩ : syracuseStep 2799463 = 4199195) B4199195
theorem B3732617 : Blo 1965435 3732617 := bstep (se 2 (by rfl) ⟨1399731, by rfl⟩ : syracuseStep 3732617 = 2799463) B2799463
theorem B2488411 : Blo 1965435 2488411 := bstep (se 1 (by rfl) ⟨1866308, by rfl⟩ : syracuseStep 2488411 = 3732617) B3732617
theorem B3317881 : Blo 1965435 3317881 := bstep (se 2 (by rfl) ⟨1244205, by rfl⟩ : syracuseStep 3317881 = 2488411) B2488411
theorem B4423841 : Blo 1965435 4423841 := bstep (se 2 (by rfl) ⟨1658940, by rfl⟩ : syracuseStep 4423841 = 3317881) B3317881
theorem B2949227 : Blo 1965435 2949227 := bstep (se 1 (by rfl) ⟨2211920, by rfl⟩ : syracuseStep 2949227 = 4423841) B4423841
theorem B1966151 : Blo 1965435 1966151 := bstep (se 1 (by rfl) ⟨1474613, by rfl⟩ : syracuseStep 1966151 = 2949227) B2949227
theorem B2211925 : Blo 1965435 2211925 := bbase (se 8 (by rfl) ⟨12960, by rfl⟩ : syracuseStep 2211925 = 25921) (by norm_num)
theorem B2949233 : Blo 1965435 2949233 := bstep (se 2 (by rfl) ⟨1105962, by rfl⟩ : syracuseStep 2949233 = 2211925) B2211925
theorem B1966155 : Blo 1965435 1966155 := bstep (se 1 (by rfl) ⟨1474616, by rfl⟩ : syracuseStep 1966155 = 2949233) B2949233
theorem B2488421 : Blo 1965435 2488421 := bbase (se 4 (by rfl) ⟨233289, by rfl⟩ : syracuseStep 2488421 = 466579) (by norm_num)
theorem B6635789 : Blo 1965435 6635789 := bstep (se 3 (by rfl) ⟨1244210, by rfl⟩ : syracuseStep 6635789 = 2488421) B2488421
theorem B4423859 : Blo 1965435 4423859 := bstep (se 1 (by rfl) ⟨3317894, by rfl⟩ : syracuseStep 4423859 = 6635789) B6635789
theorem B2949239 : Blo 1965435 2949239 := bstep (se 1 (by rfl) ⟨2211929, by rfl⟩ : syracuseStep 2949239 = 4423859) B4423859
theorem B1966159 : Blo 1965435 1966159 := bstep (se 1 (by rfl) ⟨1474619, by rfl⟩ : syracuseStep 1966159 = 2949239) B2949239
theorem B2949245 : Blo 1965435 2949245 := bbase (se 3 (by rfl) ⟨552983, by rfl⟩ : syracuseStep 2949245 = 1105967) (by norm_num)
theorem B1966163 : Blo 1965435 1966163 := bstep (se 1 (by rfl) ⟨1474622, by rfl⟩ : syracuseStep 1966163 = 2949245) B2949245
theorem B4423877 : Blo 1965435 4423877 := bbase (se 4 (by rfl) ⟨414738, by rfl⟩ : syracuseStep 4423877 = 829477) (by norm_num)
theorem B2949251 : Blo 1965435 2949251 := bstep (se 1 (by rfl) ⟨2211938, by rfl⟩ : syracuseStep 2949251 = 4423877) B4423877
theorem B1966167 : Blo 1965435 1966167 := bstep (se 1 (by rfl) ⟨1474625, by rfl⟩ : syracuseStep 1966167 = 2949251) B2949251
theorem B5314661 : Blo 1965435 5314661 := bbase (se 4 (by rfl) ⟨498249, by rfl⟩ : syracuseStep 5314661 = 996499) (by norm_num)
theorem B3543107 : Blo 1965435 3543107 := bstep (se 1 (by rfl) ⟨2657330, by rfl⟩ : syracuseStep 3543107 = 5314661) B5314661
theorem B9448285 : Blo 1965435 9448285 := bstep (se 3 (by rfl) ⟨1771553, by rfl⟩ : syracuseStep 9448285 = 3543107) B3543107
theorem B12597713 : Blo 1965435 12597713 := bstep (se 2 (by rfl) ⟨4724142, by rfl⟩ : syracuseStep 12597713 = 9448285) B9448285
theorem B8398475 : Blo 1965435 8398475 := bstep (se 1 (by rfl) ⟨6298856, by rfl⟩ : syracuseStep 8398475 = 12597713) B12597713
theorem B5598983 : Blo 1965435 5598983 := bstep (se 1 (by rfl) ⟨4199237, by rfl⟩ : syracuseStep 5598983 = 8398475) B8398475
theorem B3732655 : Blo 1965435 3732655 := bstep (se 1 (by rfl) ⟨2799491, by rfl⟩ : syracuseStep 3732655 = 5598983) B5598983
theorem B4976873 : Blo 1965435 4976873 := bstep (se 2 (by rfl) ⟨1866327, by rfl⟩ : syracuseStep 4976873 = 3732655) B3732655
theorem B3317915 : Blo 1965435 3317915 := bstep (se 1 (by rfl) ⟨2488436, by rfl⟩ : syracuseStep 3317915 = 4976873) B4976873
theorem B2211943 : Blo 1965435 2211943 := bstep (se 1 (by rfl) ⟨1658957, by rfl⟩ : syracuseStep 2211943 = 3317915) B3317915
theorem B2949257 : Blo 1965435 2949257 := bstep (se 2 (by rfl) ⟨1105971, by rfl⟩ : syracuseStep 2949257 = 2211943) B2211943
theorem B1966171 : Blo 1965435 1966171 := bstep (se 1 (by rfl) ⟨1474628, by rfl⟩ : syracuseStep 1966171 = 2949257) B2949257
theorem B9953765 : Blo 1965435 9953765 := bbase (se 4 (by rfl) ⟨933165, by rfl⟩ : syracuseStep 9953765 = 1866331) (by norm_num)
theorem B6635843 : Blo 1965435 6635843 := bstep (se 1 (by rfl) ⟨4976882, by rfl⟩ : syracuseStep 6635843 = 9953765) B9953765
theorem B4423895 : Blo 1965435 4423895 := bstep (se 1 (by rfl) ⟨3317921, by rfl⟩ : syracuseStep 4423895 = 6635843) B6635843
theorem B2949263 : Blo 1965435 2949263 := bstep (se 1 (by rfl) ⟨2211947, by rfl⟩ : syracuseStep 2949263 = 4423895) B4423895
theorem B1966175 : Blo 1965435 1966175 := bstep (se 1 (by rfl) ⟨1474631, by rfl⟩ : syracuseStep 1966175 = 2949263) B2949263
theorem B2949269 : Blo 1965435 2949269 := bbase (se 6 (by rfl) ⟨69123, by rfl⟩ : syracuseStep 2949269 = 138247) (by norm_num)
theorem B1966179 : Blo 1965435 1966179 := bstep (se 1 (by rfl) ⟨1474634, by rfl⟩ : syracuseStep 1966179 = 2949269) B2949269
theorem B5314693 : Blo 1965435 5314693 := bbase (se 4 (by rfl) ⟨498252, by rfl⟩ : syracuseStep 5314693 = 996505) (by norm_num)
theorem B7086257 : Blo 1965435 7086257 := bstep (se 2 (by rfl) ⟨2657346, by rfl⟩ : syracuseStep 7086257 = 5314693) B5314693
theorem B4724171 : Blo 1965435 4724171 := bstep (se 1 (by rfl) ⟨3543128, by rfl⟩ : syracuseStep 4724171 = 7086257) B7086257
theorem B3149447 : Blo 1965435 3149447 := bstep (se 1 (by rfl) ⟨2362085, by rfl⟩ : syracuseStep 3149447 = 4724171) B4724171
theorem B8398525 : Blo 1965435 8398525 := bstep (se 3 (by rfl) ⟨1574723, by rfl⟩ : syracuseStep 8398525 = 3149447) B3149447
theorem B11198033 : Blo 1965435 11198033 := bstep (se 2 (by rfl) ⟨4199262, by rfl⟩ : syracuseStep 11198033 = 8398525) B8398525
theorem B7465355 : Blo 1965435 7465355 := bstep (se 1 (by rfl) ⟨5599016, by rfl⟩ : syracuseStep 7465355 = 11198033) B11198033
theorem B4976903 : Blo 1965435 4976903 := bstep (se 1 (by rfl) ⟨3732677, by rfl⟩ : syracuseStep 4976903 = 7465355) B7465355
theorem B3317935 : Blo 1965435 3317935 := bstep (se 1 (by rfl) ⟨2488451, by rfl⟩ : syracuseStep 3317935 = 4976903) B4976903
theorem B4423913 : Blo 1965435 4423913 := bstep (se 2 (by rfl) ⟨1658967, by rfl⟩ : syracuseStep 4423913 = 3317935) B3317935
theorem B2949275 : Blo 1965435 2949275 := bstep (se 1 (by rfl) ⟨2211956, by rfl⟩ : syracuseStep 2949275 = 4423913) B4423913
theorem B1966183 : Blo 1965435 1966183 := bstep (se 1 (by rfl) ⟨1474637, by rfl⟩ : syracuseStep 1966183 = 2949275) B2949275
theorem B2211961 : Blo 1965435 2211961 := bbase (se 2 (by rfl) ⟨829485, by rfl⟩ : syracuseStep 2211961 = 1658971) (by norm_num)
theorem B2949281 : Blo 1965435 2949281 := bstep (se 2 (by rfl) ⟨1105980, by rfl⟩ : syracuseStep 2949281 = 2211961) B2211961
theorem B1966187 : Blo 1965435 1966187 := bstep (se 1 (by rfl) ⟨1474640, by rfl⟩ : syracuseStep 1966187 = 2949281) B2949281
theorem B2242145 : Blo 1965435 2242145 := bbase (se 2 (by rfl) ⟨840804, by rfl⟩ : syracuseStep 2242145 = 1681609) (by norm_num)
theorem B5979053 : Blo 1965435 5979053 := bstep (se 3 (by rfl) ⟨1121072, by rfl⟩ : syracuseStep 5979053 = 2242145) B2242145
theorem B15944141 : Blo 1965435 15944141 := bstep (se 3 (by rfl) ⟨2989526, by rfl⟩ : syracuseStep 15944141 = 5979053) B5979053
theorem B42517709 : Blo 1965435 42517709 := bstep (se 3 (by rfl) ⟨7972070, by rfl⟩ : syracuseStep 42517709 = 15944141) B15944141
theorem B28345139 : Blo 1965435 28345139 := bstep (se 1 (by rfl) ⟨21258854, by rfl⟩ : syracuseStep 28345139 = 42517709) B42517709
theorem B18896759 : Blo 1965435 18896759 := bstep (se 1 (by rfl) ⟨14172569, by rfl⟩ : syracuseStep 18896759 = 28345139) B28345139
theorem B12597839 : Blo 1965435 12597839 := bstep (se 1 (by rfl) ⟨9448379, by rfl⟩ : syracuseStep 12597839 = 18896759) B18896759
theorem B8398559 : Blo 1965435 8398559 := bstep (se 1 (by rfl) ⟨6298919, by rfl⟩ : syracuseStep 8398559 = 12597839) B12597839
theorem B5599039 : Blo 1965435 5599039 := bstep (se 1 (by rfl) ⟨4199279, by rfl⟩ : syracuseStep 5599039 = 8398559) B8398559
theorem B7465385 : Blo 1965435 7465385 := bstep (se 2 (by rfl) ⟨2799519, by rfl⟩ : syracuseStep 7465385 = 5599039) B5599039
theorem B4976923 : Blo 1965435 4976923 := bstep (se 1 (by rfl) ⟨3732692, by rfl⟩ : syracuseStep 4976923 = 7465385) B7465385
theorem B6635897 : Blo 1965435 6635897 := bstep (se 2 (by rfl) ⟨2488461, by rfl⟩ : syracuseStep 6635897 = 4976923) B4976923
theorem B4423931 : Blo 1965435 4423931 := bstep (se 1 (by rfl) ⟨3317948, by rfl⟩ : syracuseStep 4423931 = 6635897) B6635897
theorem B2949287 : Blo 1965435 2949287 := bstep (se 1 (by rfl) ⟨2211965, by rfl⟩ : syracuseStep 2949287 = 4423931) B4423931
theorem B1966191 : Blo 1965435 1966191 := bstep (se 1 (by rfl) ⟨1474643, by rfl⟩ : syracuseStep 1966191 = 2949287) B2949287
theorem B2949293 : Blo 1965435 2949293 := bbase (se 3 (by rfl) ⟨552992, by rfl⟩ : syracuseStep 2949293 = 1105985) (by norm_num)
theorem B1966195 : Blo 1965435 1966195 := bstep (se 1 (by rfl) ⟨1474646, by rfl⟩ : syracuseStep 1966195 = 2949293) B2949293
theorem B4423949 : Blo 1965435 4423949 := bbase (se 3 (by rfl) ⟨829490, by rfl⟩ : syracuseStep 4423949 = 1658981) (by norm_num)
theorem B2949299 : Blo 1965435 2949299 := bstep (se 1 (by rfl) ⟨2211974, by rfl⟩ : syracuseStep 2949299 = 4423949) B4423949
theorem B1966199 : Blo 1965435 1966199 := bstep (se 1 (by rfl) ⟨1474649, by rfl⟩ : syracuseStep 1966199 = 2949299) B2949299
theorem B2488477 : Blo 1965435 2488477 := bbase (se 3 (by rfl) ⟨466589, by rfl⟩ : syracuseStep 2488477 = 933179) (by norm_num)
theorem B3317969 : Blo 1965435 3317969 := bstep (se 2 (by rfl) ⟨1244238, by rfl⟩ : syracuseStep 3317969 = 2488477) B2488477
theorem B2211979 : Blo 1965435 2211979 := bstep (se 1 (by rfl) ⟨1658984, by rfl⟩ : syracuseStep 2211979 = 3317969) B3317969
theorem B2949305 : Blo 1965435 2949305 := bstep (se 2 (by rfl) ⟨1105989, by rfl⟩ : syracuseStep 2949305 = 2211979) B2211979
theorem B1966203 : Blo 1965435 1966203 := bstep (se 1 (by rfl) ⟨1474652, by rfl⟩ : syracuseStep 1966203 = 2949305) B2949305
theorem B3149485 : Blo 1965435 3149485 := bbase (se 3 (by rfl) ⟨590528, by rfl⟩ : syracuseStep 3149485 = 1181057) (by norm_num)
theorem B16797253 : Blo 1965435 16797253 := bstep (se 4 (by rfl) ⟨1574742, by rfl⟩ : syracuseStep 16797253 = 3149485) B3149485
theorem B22396337 : Blo 1965435 22396337 := bstep (se 2 (by rfl) ⟨8398626, by rfl⟩ : syracuseStep 22396337 = 16797253) B16797253
theorem B14930891 : Blo 1965435 14930891 := bstep (se 1 (by rfl) ⟨11198168, by rfl⟩ : syracuseStep 14930891 = 22396337) B22396337
theorem B9953927 : Blo 1965435 9953927 := bstep (se 1 (by rfl) ⟨7465445, by rfl⟩ : syracuseStep 9953927 = 14930891) B14930891
theorem B6635951 : Blo 1965435 6635951 := bstep (se 1 (by rfl) ⟨4976963, by rfl⟩ : syracuseStep 6635951 = 9953927) B9953927
theorem B4423967 : Blo 1965435 4423967 := bstep (se 1 (by rfl) ⟨3317975, by rfl⟩ : syracuseStep 4423967 = 6635951) B6635951
theorem B2949311 : Blo 1965435 2949311 := bstep (se 1 (by rfl) ⟨2211983, by rfl⟩ : syracuseStep 2949311 = 4423967) B4423967
theorem B1966207 : Blo 1965435 1966207 := bstep (se 1 (by rfl) ⟨1474655, by rfl⟩ : syracuseStep 1966207 = 2949311) B2949311
theorem B2949317 : Blo 1965435 2949317 := bbase (se 4 (by rfl) ⟨276498, by rfl⟩ : syracuseStep 2949317 = 552997) (by norm_num)
theorem B1966211 : Blo 1965435 1966211 := bstep (se 1 (by rfl) ⟨1474658, by rfl⟩ : syracuseStep 1966211 = 2949317) B2949317
theorem B3317989 : Blo 1965435 3317989 := bbase (se 4 (by rfl) ⟨311061, by rfl⟩ : syracuseStep 3317989 = 622123) (by norm_num)
theorem B4423985 : Blo 1965435 4423985 := bstep (se 2 (by rfl) ⟨1658994, by rfl⟩ : syracuseStep 4423985 = 3317989) B3317989
theorem B2949323 : Blo 1965435 2949323 := bstep (se 1 (by rfl) ⟨2211992, by rfl⟩ : syracuseStep 2949323 = 4423985) B4423985
theorem B1966215 : Blo 1965435 1966215 := bstep (se 1 (by rfl) ⟨1474661, by rfl⟩ : syracuseStep 1966215 = 2949323) B2949323
theorem B2211997 : Blo 1965435 2211997 := bbase (se 3 (by rfl) ⟨414749, by rfl⟩ : syracuseStep 2211997 = 829499) (by norm_num)
theorem B2949329 : Blo 1965435 2949329 := bstep (se 2 (by rfl) ⟨1105998, by rfl⟩ : syracuseStep 2949329 = 2211997) B2211997
theorem B1966219 : Blo 1965435 1966219 := bstep (se 1 (by rfl) ⟨1474664, by rfl⟩ : syracuseStep 1966219 = 2949329) B2949329
theorem B6636005 : Blo 1965435 6636005 := bbase (se 4 (by rfl) ⟨622125, by rfl⟩ : syracuseStep 6636005 = 1244251) (by norm_num)
theorem B4424003 : Blo 1965435 4424003 := bstep (se 1 (by rfl) ⟨3318002, by rfl⟩ : syracuseStep 4424003 = 6636005) B6636005
theorem B2949335 : Blo 1965435 2949335 := bstep (se 1 (by rfl) ⟨2212001, by rfl⟩ : syracuseStep 2949335 = 4424003) B4424003
theorem B1966223 : Blo 1965435 1966223 := bstep (se 1 (by rfl) ⟨1474667, by rfl⟩ : syracuseStep 1966223 = 2949335) B2949335
theorem B2949341 : Blo 1965435 2949341 := bbase (se 3 (by rfl) ⟨553001, by rfl⟩ : syracuseStep 2949341 = 1106003) (by norm_num)
theorem B1966227 : Blo 1965435 1966227 := bstep (se 1 (by rfl) ⟨1474670, by rfl⟩ : syracuseStep 1966227 = 2949341) B2949341
theorem B4424021 : Blo 1965435 4424021 := bbase (se 10 (by rfl) ⟨6480, by rfl⟩ : syracuseStep 4424021 = 12961) (by norm_num)
theorem B2949347 : Blo 1965435 2949347 := bstep (se 1 (by rfl) ⟨2212010, by rfl⟩ : syracuseStep 2949347 = 4424021) B4424021
theorem B1966231 : Blo 1965435 1966231 := bstep (se 1 (by rfl) ⟨1474673, by rfl⟩ : syracuseStep 1966231 = 2949347) B2949347
theorem B12944245 : Blo 1965435 12944245 := bbase (se 5 (by rfl) ⟨606761, by rfl⟩ : syracuseStep 12944245 = 1213523) (by norm_num)
theorem B17258993 : Blo 1965435 17258993 := bstep (se 2 (by rfl) ⟨6472122, by rfl⟩ : syracuseStep 17258993 = 12944245) B12944245
theorem B11505995 : Blo 1965435 11505995 := bstep (se 1 (by rfl) ⟨8629496, by rfl⟩ : syracuseStep 11505995 = 17258993) B17258993
theorem B7670663 : Blo 1965435 7670663 := bstep (se 1 (by rfl) ⟨5752997, by rfl⟩ : syracuseStep 7670663 = 11505995) B11505995
theorem B5113775 : Blo 1965435 5113775 := bstep (se 1 (by rfl) ⟨3835331, by rfl⟩ : syracuseStep 5113775 = 7670663) B7670663
theorem B3409183 : Blo 1965435 3409183 := bstep (se 1 (by rfl) ⟨2556887, by rfl⟩ : syracuseStep 3409183 = 5113775) B5113775
theorem B4545577 : Blo 1965435 4545577 := bstep (se 2 (by rfl) ⟨1704591, by rfl⟩ : syracuseStep 4545577 = 3409183) B3409183
theorem B24243077 : Blo 1965435 24243077 := bstep (se 4 (by rfl) ⟨2272788, by rfl⟩ : syracuseStep 24243077 = 4545577) B4545577
theorem B16162051 : Blo 1965435 16162051 := bstep (se 1 (by rfl) ⟨12121538, by rfl⟩ : syracuseStep 16162051 = 24243077) B24243077
theorem B21549401 : Blo 1965435 21549401 := bstep (se 2 (by rfl) ⟨8081025, by rfl⟩ : syracuseStep 21549401 = 16162051) B16162051
theorem B14366267 : Blo 1965435 14366267 := bstep (se 1 (by rfl) ⟨10774700, by rfl⟩ : syracuseStep 14366267 = 21549401) B21549401
theorem B9577511 : Blo 1965435 9577511 := bstep (se 1 (by rfl) ⟨7183133, by rfl⟩ : syracuseStep 9577511 = 14366267) B14366267
theorem B6385007 : Blo 1965435 6385007 := bstep (se 1 (by rfl) ⟨4788755, by rfl⟩ : syracuseStep 6385007 = 9577511) B9577511
theorem B17026685 : Blo 1965435 17026685 := bstep (se 3 (by rfl) ⟨3192503, by rfl⟩ : syracuseStep 17026685 = 6385007) B6385007
theorem B11351123 : Blo 1965435 11351123 := bstep (se 1 (by rfl) ⟨8513342, by rfl⟩ : syracuseStep 11351123 = 17026685) B17026685
theorem B7567415 : Blo 1965435 7567415 := bstep (se 1 (by rfl) ⟨5675561, by rfl⟩ : syracuseStep 7567415 = 11351123) B11351123
theorem B5044943 : Blo 1965435 5044943 := bstep (se 1 (by rfl) ⟨3783707, by rfl⟩ : syracuseStep 5044943 = 7567415) B7567415
theorem B3363295 : Blo 1965435 3363295 := bstep (se 1 (by rfl) ⟨2522471, by rfl⟩ : syracuseStep 3363295 = 5044943) B5044943
theorem B4484393 : Blo 1965435 4484393 := bstep (se 2 (by rfl) ⟨1681647, by rfl⟩ : syracuseStep 4484393 = 3363295) B3363295
theorem B2989595 : Blo 1965435 2989595 := bstep (se 1 (by rfl) ⟨2242196, by rfl⟩ : syracuseStep 2989595 = 4484393) B4484393
theorem B7972253 : Blo 1965435 7972253 := bstep (se 3 (by rfl) ⟨1494797, by rfl⟩ : syracuseStep 7972253 = 2989595) B2989595
theorem B5314835 : Blo 1965435 5314835 := bstep (se 1 (by rfl) ⟨3986126, by rfl⟩ : syracuseStep 5314835 = 7972253) B7972253
theorem B3543223 : Blo 1965435 3543223 := bstep (se 1 (by rfl) ⟨2657417, by rfl⟩ : syracuseStep 3543223 = 5314835) B5314835
theorem B4724297 : Blo 1965435 4724297 := bstep (se 2 (by rfl) ⟨1771611, by rfl⟩ : syracuseStep 4724297 = 3543223) B3543223
theorem B3149531 : Blo 1965435 3149531 := bstep (se 1 (by rfl) ⟨2362148, by rfl⟩ : syracuseStep 3149531 = 4724297) B4724297
theorem B2099687 : Blo 1965435 2099687 := bstep (se 1 (by rfl) ⟨1574765, by rfl⟩ : syracuseStep 2099687 = 3149531) B3149531
theorem B5599165 : Blo 1965435 5599165 := bstep (se 3 (by rfl) ⟨1049843, by rfl⟩ : syracuseStep 5599165 = 2099687) B2099687
theorem B7465553 : Blo 1965435 7465553 := bstep (se 2 (by rfl) ⟨2799582, by rfl⟩ : syracuseStep 7465553 = 5599165) B5599165
theorem B4977035 : Blo 1965435 4977035 := bstep (se 1 (by rfl) ⟨3732776, by rfl⟩ : syracuseStep 4977035 = 7465553) B7465553
theorem B3318023 : Blo 1965435 3318023 := bstep (se 1 (by rfl) ⟨2488517, by rfl⟩ : syracuseStep 3318023 = 4977035) B4977035
theorem B2212015 : Blo 1965435 2212015 := bstep (se 1 (by rfl) ⟨1659011, by rfl⟩ : syracuseStep 2212015 = 3318023) B3318023
theorem B2949353 : Blo 1965435 2949353 := bstep (se 2 (by rfl) ⟨1106007, by rfl⟩ : syracuseStep 2949353 = 2212015) B2212015
theorem B1966235 : Blo 1965435 1966235 := bstep (se 1 (by rfl) ⟨1474676, by rfl⟩ : syracuseStep 1966235 = 2949353) B2949353
theorem B3030389 : Blo 1965435 3030389 := bbase (se 5 (by rfl) ⟨142049, by rfl⟩ : syracuseStep 3030389 = 284099) (by norm_num)
theorem B2020259 : Blo 1965435 2020259 := bstep (se 1 (by rfl) ⟨1515194, by rfl⟩ : syracuseStep 2020259 = 3030389) B3030389
theorem B5387357 : Blo 1965435 5387357 := bstep (se 3 (by rfl) ⟨1010129, by rfl⟩ : syracuseStep 5387357 = 2020259) B2020259
theorem B14366285 : Blo 1965435 14366285 := bstep (se 3 (by rfl) ⟨2693678, by rfl⟩ : syracuseStep 14366285 = 5387357) B5387357
theorem B9577523 : Blo 1965435 9577523 := bstep (se 1 (by rfl) ⟨7183142, by rfl⟩ : syracuseStep 9577523 = 14366285) B14366285
theorem B6385015 : Blo 1965435 6385015 := bstep (se 1 (by rfl) ⟨4788761, by rfl⟩ : syracuseStep 6385015 = 9577523) B9577523
theorem B8513353 : Blo 1965435 8513353 := bstep (se 2 (by rfl) ⟨3192507, by rfl⟩ : syracuseStep 8513353 = 6385015) B6385015
theorem B45404549 : Blo 1965435 45404549 := bstep (se 4 (by rfl) ⟨4256676, by rfl⟩ : syracuseStep 45404549 = 8513353) B8513353
theorem B30269699 : Blo 1965435 30269699 := bstep (se 1 (by rfl) ⟨22702274, by rfl⟩ : syracuseStep 30269699 = 45404549) B45404549
theorem B20179799 : Blo 1965435 20179799 := bstep (se 1 (by rfl) ⟨15134849, by rfl⟩ : syracuseStep 20179799 = 30269699) B30269699
theorem B13453199 : Blo 1965435 13453199 := bstep (se 1 (by rfl) ⟨10089899, by rfl⟩ : syracuseStep 13453199 = 20179799) B20179799
theorem B8968799 : Blo 1965435 8968799 := bstep (se 1 (by rfl) ⟨6726599, by rfl⟩ : syracuseStep 8968799 = 13453199) B13453199
theorem B5979199 : Blo 1965435 5979199 := bstep (se 1 (by rfl) ⟨4484399, by rfl⟩ : syracuseStep 5979199 = 8968799) B8968799
theorem B7972265 : Blo 1965435 7972265 := bstep (se 2 (by rfl) ⟨2989599, by rfl⟩ : syracuseStep 7972265 = 5979199) B5979199
theorem B5314843 : Blo 1965435 5314843 := bstep (se 1 (by rfl) ⟨3986132, by rfl⟩ : syracuseStep 5314843 = 7972265) B7972265
theorem B7086457 : Blo 1965435 7086457 := bstep (se 2 (by rfl) ⟨2657421, by rfl⟩ : syracuseStep 7086457 = 5314843) B5314843
theorem B37794437 : Blo 1965435 37794437 := bstep (se 4 (by rfl) ⟨3543228, by rfl⟩ : syracuseStep 37794437 = 7086457) B7086457
theorem B25196291 : Blo 1965435 25196291 := bstep (se 1 (by rfl) ⟨18897218, by rfl⟩ : syracuseStep 25196291 = 37794437) B37794437
theorem B16797527 : Blo 1965435 16797527 := bstep (se 1 (by rfl) ⟨12598145, by rfl⟩ : syracuseStep 16797527 = 25196291) B25196291
theorem B11198351 : Blo 1965435 11198351 := bstep (se 1 (by rfl) ⟨8398763, by rfl⟩ : syracuseStep 11198351 = 16797527) B16797527
theorem B7465567 : Blo 1965435 7465567 := bstep (se 1 (by rfl) ⟨5599175, by rfl⟩ : syracuseStep 7465567 = 11198351) B11198351
theorem B9954089 : Blo 1965435 9954089 := bstep (se 2 (by rfl) ⟨3732783, by rfl⟩ : syracuseStep 9954089 = 7465567) B7465567
theorem B6636059 : Blo 1965435 6636059 := bstep (se 1 (by rfl) ⟨4977044, by rfl⟩ : syracuseStep 6636059 = 9954089) B9954089
theorem B4424039 : Blo 1965435 4424039 := bstep (se 1 (by rfl) ⟨3318029, by rfl⟩ : syracuseStep 4424039 = 6636059) B6636059
theorem B2949359 : Blo 1965435 2949359 := bstep (se 1 (by rfl) ⟨2212019, by rfl⟩ : syracuseStep 2949359 = 4424039) B4424039
theorem B1966239 : Blo 1965435 1966239 := bstep (se 1 (by rfl) ⟨1474679, by rfl⟩ : syracuseStep 1966239 = 2949359) B2949359
theorem B2949365 : Blo 1965435 2949365 := bbase (se 5 (by rfl) ⟨138251, by rfl⟩ : syracuseStep 2949365 = 276503) (by norm_num)
theorem B1966243 : Blo 1965435 1966243 := bstep (se 1 (by rfl) ⟨1474682, by rfl⟩ : syracuseStep 1966243 = 2949365) B2949365
theorem B15944597 : Blo 1965435 15944597 := bbase (se 6 (by rfl) ⟨373701, by rfl⟩ : syracuseStep 15944597 = 747403) (by norm_num)
theorem B10629731 : Blo 1965435 10629731 := bstep (se 1 (by rfl) ⟨7972298, by rfl⟩ : syracuseStep 10629731 = 15944597) B15944597
theorem B28345949 : Blo 1965435 28345949 := bstep (se 3 (by rfl) ⟨5314865, by rfl⟩ : syracuseStep 28345949 = 10629731) B10629731
theorem B18897299 : Blo 1965435 18897299 := bstep (se 1 (by rfl) ⟨14172974, by rfl⟩ : syracuseStep 18897299 = 28345949) B28345949
theorem B12598199 : Blo 1965435 12598199 := bstep (se 1 (by rfl) ⟨9448649, by rfl⟩ : syracuseStep 12598199 = 18897299) B18897299
theorem B8398799 : Blo 1965435 8398799 := bstep (se 1 (by rfl) ⟨6299099, by rfl⟩ : syracuseStep 8398799 = 12598199) B12598199
theorem B5599199 : Blo 1965435 5599199 := bstep (se 1 (by rfl) ⟨4199399, by rfl⟩ : syracuseStep 5599199 = 8398799) B8398799
theorem B3732799 : Blo 1965435 3732799 := bstep (se 1 (by rfl) ⟨2799599, by rfl⟩ : syracuseStep 3732799 = 5599199) B5599199
theorem B4977065 : Blo 1965435 4977065 := bstep (se 2 (by rfl) ⟨1866399, by rfl⟩ : syracuseStep 4977065 = 3732799) B3732799
theorem B3318043 : Blo 1965435 3318043 := bstep (se 1 (by rfl) ⟨2488532, by rfl⟩ : syracuseStep 3318043 = 4977065) B4977065
theorem B4424057 : Blo 1965435 4424057 := bstep (se 2 (by rfl) ⟨1659021, by rfl⟩ : syracuseStep 4424057 = 3318043) B3318043
theorem B2949371 : Blo 1965435 2949371 := bstep (se 1 (by rfl) ⟨2212028, by rfl⟩ : syracuseStep 2949371 = 4424057) B4424057
theorem B1966247 : Blo 1965435 1966247 := bstep (se 1 (by rfl) ⟨1474685, by rfl⟩ : syracuseStep 1966247 = 2949371) B2949371
theorem B2212033 : Blo 1965435 2212033 := bbase (se 2 (by rfl) ⟨829512, by rfl⟩ : syracuseStep 2212033 = 1659025) (by norm_num)
theorem B2949377 : Blo 1965435 2949377 := bstep (se 2 (by rfl) ⟨1106016, by rfl⟩ : syracuseStep 2949377 = 2212033) B2212033
theorem B1966251 : Blo 1965435 1966251 := bstep (se 1 (by rfl) ⟨1474688, by rfl⟩ : syracuseStep 1966251 = 2949377) B2949377
theorem B4977085 : Blo 1965435 4977085 := bbase (se 3 (by rfl) ⟨933203, by rfl⟩ : syracuseStep 4977085 = 1866407) (by norm_num)
theorem B6636113 : Blo 1965435 6636113 := bstep (se 2 (by rfl) ⟨2488542, by rfl⟩ : syracuseStep 6636113 = 4977085) B4977085
theorem B4424075 : Blo 1965435 4424075 := bstep (se 1 (by rfl) ⟨3318056, by rfl⟩ : syracuseStep 4424075 = 6636113) B6636113
theorem B2949383 : Blo 1965435 2949383 := bstep (se 1 (by rfl) ⟨2212037, by rfl⟩ : syracuseStep 2949383 = 4424075) B4424075
theorem B1966255 : Blo 1965435 1966255 := bstep (se 1 (by rfl) ⟨1474691, by rfl⟩ : syracuseStep 1966255 = 2949383) B2949383
theorem B2949389 : Blo 1965435 2949389 := bbase (se 3 (by rfl) ⟨553010, by rfl⟩ : syracuseStep 2949389 = 1106021) (by norm_num)
theorem B1966259 : Blo 1965435 1966259 := bstep (se 1 (by rfl) ⟨1474694, by rfl⟩ : syracuseStep 1966259 = 2949389) B2949389
theorem B4424093 : Blo 1965435 4424093 := bbase (se 3 (by rfl) ⟨829517, by rfl⟩ : syracuseStep 4424093 = 1659035) (by norm_num)
theorem B2949395 : Blo 1965435 2949395 := bstep (se 1 (by rfl) ⟨2212046, by rfl⟩ : syracuseStep 2949395 = 4424093) B4424093
theorem B1966263 : Blo 1965435 1966263 := bstep (se 1 (by rfl) ⟨1474697, by rfl⟩ : syracuseStep 1966263 = 2949395) B2949395
theorem B3318077 : Blo 1965435 3318077 := bbase (se 3 (by rfl) ⟨622139, by rfl⟩ : syracuseStep 3318077 = 1244279) (by norm_num)
theorem B2212051 : Blo 1965435 2212051 := bstep (se 1 (by rfl) ⟨1659038, by rfl⟩ : syracuseStep 2212051 = 3318077) B3318077
theorem B2949401 : Blo 1965435 2949401 := bstep (se 2 (by rfl) ⟨1106025, by rfl⟩ : syracuseStep 2949401 = 2212051) B2212051
theorem B1966267 : Blo 1965435 1966267 := bstep (se 1 (by rfl) ⟨1474700, by rfl⟩ : syracuseStep 1966267 = 2949401) B2949401
theorem B2099725 : Blo 1965435 2099725 := bbase (se 3 (by rfl) ⟨393698, by rfl⟩ : syracuseStep 2099725 = 787397) (by norm_num)
theorem B11198533 : Blo 1965435 11198533 := bstep (se 4 (by rfl) ⟨1049862, by rfl⟩ : syracuseStep 11198533 = 2099725) B2099725
theorem B14931377 : Blo 1965435 14931377 := bstep (se 2 (by rfl) ⟨5599266, by rfl⟩ : syracuseStep 14931377 = 11198533) B11198533
theorem B9954251 : Blo 1965435 9954251 := bstep (se 1 (by rfl) ⟨7465688, by rfl⟩ : syracuseStep 9954251 = 14931377) B14931377
theorem B6636167 : Blo 1965435 6636167 := bstep (se 1 (by rfl) ⟨4977125, by rfl⟩ : syracuseStep 6636167 = 9954251) B9954251
theorem B4424111 : Blo 1965435 4424111 := bstep (se 1 (by rfl) ⟨3318083, by rfl⟩ : syracuseStep 4424111 = 6636167) B6636167
theorem B2949407 : Blo 1965435 2949407 := bstep (se 1 (by rfl) ⟨2212055, by rfl⟩ : syracuseStep 2949407 = 4424111) B4424111
theorem B1966271 : Blo 1965435 1966271 := bstep (se 1 (by rfl) ⟨1474703, by rfl⟩ : syracuseStep 1966271 = 2949407) B2949407
theorem B2949413 : Blo 1965435 2949413 := bbase (se 4 (by rfl) ⟨276507, by rfl⟩ : syracuseStep 2949413 = 553015) (by norm_num)
theorem B1966275 : Blo 1965435 1966275 := bstep (se 1 (by rfl) ⟨1474706, by rfl⟩ : syracuseStep 1966275 = 2949413) B2949413
theorem B2488573 : Blo 1965435 2488573 := bbase (se 3 (by rfl) ⟨466607, by rfl⟩ : syracuseStep 2488573 = 933215) (by norm_num)
theorem B3318097 : Blo 1965435 3318097 := bstep (se 2 (by rfl) ⟨1244286, by rfl⟩ : syracuseStep 3318097 = 2488573) B2488573
theorem B4424129 : Blo 1965435 4424129 := bstep (se 2 (by rfl) ⟨1659048, by rfl⟩ : syracuseStep 4424129 = 3318097) B3318097
theorem B2949419 : Blo 1965435 2949419 := bstep (se 1 (by rfl) ⟨2212064, by rfl⟩ : syracuseStep 2949419 = 4424129) B4424129
theorem B1966279 : Blo 1965435 1966279 := bstep (se 1 (by rfl) ⟨1474709, by rfl⟩ : syracuseStep 1966279 = 2949419) B2949419
theorem B2212069 : Blo 1965435 2212069 := bbase (se 4 (by rfl) ⟨207381, by rfl⟩ : syracuseStep 2212069 = 414763) (by norm_num)
theorem B2949425 : Blo 1965435 2949425 := bstep (se 2 (by rfl) ⟨1106034, by rfl⟩ : syracuseStep 2949425 = 2212069) B2212069
theorem B1966283 : Blo 1965435 1966283 := bstep (se 1 (by rfl) ⟨1474712, by rfl⟩ : syracuseStep 1966283 = 2949425) B2949425
theorem B4199485 : Blo 1965435 4199485 := bbase (se 3 (by rfl) ⟨787403, by rfl⟩ : syracuseStep 4199485 = 1574807) (by norm_num)
theorem B5599313 : Blo 1965435 5599313 := bstep (se 2 (by rfl) ⟨2099742, by rfl⟩ : syracuseStep 5599313 = 4199485) B4199485
theorem B3732875 : Blo 1965435 3732875 := bstep (se 1 (by rfl) ⟨2799656, by rfl⟩ : syracuseStep 3732875 = 5599313) B5599313
theorem B2488583 : Blo 1965435 2488583 := bstep (se 1 (by rfl) ⟨1866437, by rfl⟩ : syracuseStep 2488583 = 3732875) B3732875
theorem B6636221 : Blo 1965435 6636221 := bstep (se 3 (by rfl) ⟨1244291, by rfl⟩ : syracuseStep 6636221 = 2488583) B2488583
theorem B4424147 : Blo 1965435 4424147 := bstep (se 1 (by rfl) ⟨3318110, by rfl⟩ : syracuseStep 4424147 = 6636221) B6636221
theorem B2949431 : Blo 1965435 2949431 := bstep (se 1 (by rfl) ⟨2212073, by rfl⟩ : syracuseStep 2949431 = 4424147) B4424147
theorem B1966287 : Blo 1965435 1966287 := bstep (se 1 (by rfl) ⟨1474715, by rfl⟩ : syracuseStep 1966287 = 2949431) B2949431
theorem B2949437 : Blo 1965435 2949437 := bbase (se 3 (by rfl) ⟨553019, by rfl⟩ : syracuseStep 2949437 = 1106039) (by norm_num)
theorem B1966291 : Blo 1965435 1966291 := bstep (se 1 (by rfl) ⟨1474718, by rfl⟩ : syracuseStep 1966291 = 2949437) B2949437
theorem B4424165 : Blo 1965435 4424165 := bbase (se 4 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 4424165 = 829531) (by norm_num)
theorem B2949443 : Blo 1965435 2949443 := bstep (se 1 (by rfl) ⟨2212082, by rfl⟩ : syracuseStep 2949443 = 4424165) B4424165
theorem B1966295 : Blo 1965435 1966295 := bstep (se 1 (by rfl) ⟨1474721, by rfl⟩ : syracuseStep 1966295 = 2949443) B2949443
theorem B4977197 : Blo 1965435 4977197 := bbase (se 3 (by rfl) ⟨933224, by rfl⟩ : syracuseStep 4977197 = 1866449) (by norm_num)
theorem B3318131 : Blo 1965435 3318131 := bstep (se 1 (by rfl) ⟨2488598, by rfl⟩ : syracuseStep 3318131 = 4977197) B4977197
theorem B2212087 : Blo 1965435 2212087 := bstep (se 1 (by rfl) ⟨1659065, by rfl⟩ : syracuseStep 2212087 = 3318131) B3318131
theorem B2949449 : Blo 1965435 2949449 := bstep (se 2 (by rfl) ⟨1106043, by rfl⟩ : syracuseStep 2949449 = 2212087) B2212087
theorem B1966299 : Blo 1965435 1966299 := bstep (se 1 (by rfl) ⟨1474724, by rfl⟩ : syracuseStep 1966299 = 2949449) B2949449
theorem B8969093 : Blo 1965435 8969093 := bbase (se 4 (by rfl) ⟨840852, by rfl⟩ : syracuseStep 8969093 = 1681705) (by norm_num)
theorem B5979395 : Blo 1965435 5979395 := bstep (se 1 (by rfl) ⟨4484546, by rfl⟩ : syracuseStep 5979395 = 8969093) B8969093
theorem B3986263 : Blo 1965435 3986263 := bstep (se 1 (by rfl) ⟨2989697, by rfl⟩ : syracuseStep 3986263 = 5979395) B5979395
theorem B21260069 : Blo 1965435 21260069 := bstep (se 4 (by rfl) ⟨1993131, by rfl⟩ : syracuseStep 21260069 = 3986263) B3986263
theorem B14173379 : Blo 1965435 14173379 := bstep (se 1 (by rfl) ⟨10630034, by rfl⟩ : syracuseStep 14173379 = 21260069) B21260069
theorem B9448919 : Blo 1965435 9448919 := bstep (se 1 (by rfl) ⟨7086689, by rfl⟩ : syracuseStep 9448919 = 14173379) B14173379
theorem B6299279 : Blo 1965435 6299279 := bstep (se 1 (by rfl) ⟨4724459, by rfl⟩ : syracuseStep 6299279 = 9448919) B9448919
theorem B4199519 : Blo 1965435 4199519 := bstep (se 1 (by rfl) ⟨3149639, by rfl⟩ : syracuseStep 4199519 = 6299279) B6299279
theorem B2799679 : Blo 1965435 2799679 := bstep (se 1 (by rfl) ⟨2099759, by rfl⟩ : syracuseStep 2799679 = 4199519) B4199519
theorem B3732905 : Blo 1965435 3732905 := bstep (se 2 (by rfl) ⟨1399839, by rfl⟩ : syracuseStep 3732905 = 2799679) B2799679
theorem B9954413 : Blo 1965435 9954413 := bstep (se 3 (by rfl) ⟨1866452, by rfl⟩ : syracuseStep 9954413 = 3732905) B3732905
theorem B6636275 : Blo 1965435 6636275 := bstep (se 1 (by rfl) ⟨4977206, by rfl⟩ : syracuseStep 6636275 = 9954413) B9954413
theorem B4424183 : Blo 1965435 4424183 := bstep (se 1 (by rfl) ⟨3318137, by rfl⟩ : syracuseStep 4424183 = 6636275) B6636275
theorem B2949455 : Blo 1965435 2949455 := bstep (se 1 (by rfl) ⟨2212091, by rfl⟩ : syracuseStep 2949455 = 4424183) B4424183
theorem B1966303 : Blo 1965435 1966303 := bstep (se 1 (by rfl) ⟨1474727, by rfl⟩ : syracuseStep 1966303 = 2949455) B2949455
theorem B2949461 : Blo 1965435 2949461 := bbase (se 10 (by rfl) ⟨4320, by rfl⟩ : syracuseStep 2949461 = 8641) (by norm_num)
theorem B1966307 : Blo 1965435 1966307 := bstep (se 1 (by rfl) ⟨1474730, by rfl⟩ : syracuseStep 1966307 = 2949461) B2949461
theorem B5599381 : Blo 1965435 5599381 := bbase (se 6 (by rfl) ⟨131235, by rfl⟩ : syracuseStep 5599381 = 262471) (by norm_num)
theorem B7465841 : Blo 1965435 7465841 := bstep (se 2 (by rfl) ⟨2799690, by rfl⟩ : syracuseStep 7465841 = 5599381) B5599381
theorem B4977227 : Blo 1965435 4977227 := bstep (se 1 (by rfl) ⟨3732920, by rfl⟩ : syracuseStep 4977227 = 7465841) B7465841
theorem B3318151 : Blo 1965435 3318151 := bstep (se 1 (by rfl) ⟨2488613, by rfl⟩ : syracuseStep 3318151 = 4977227) B4977227
theorem B4424201 : Blo 1965435 4424201 := bstep (se 2 (by rfl) ⟨1659075, by rfl⟩ : syracuseStep 4424201 = 3318151) B3318151
theorem B2949467 : Blo 1965435 2949467 := bstep (se 1 (by rfl) ⟨2212100, by rfl⟩ : syracuseStep 2949467 = 4424201) B4424201
theorem B1966311 : Blo 1965435 1966311 := bstep (se 1 (by rfl) ⟨1474733, by rfl⟩ : syracuseStep 1966311 = 2949467) B2949467
theorem B2212105 : Blo 1965435 2212105 := bbase (se 2 (by rfl) ⟨829539, by rfl⟩ : syracuseStep 2212105 = 1659079) (by norm_num)
theorem B2949473 : Blo 1965435 2949473 := bstep (se 2 (by rfl) ⟨1106052, by rfl⟩ : syracuseStep 2949473 = 2212105) B2212105
theorem B1966315 : Blo 1965435 1966315 := bstep (se 1 (by rfl) ⟨1474736, by rfl⟩ : syracuseStep 1966315 = 2949473) B2949473
theorem B3543373 : Blo 1965435 3543373 := bbase (se 3 (by rfl) ⟨664382, by rfl⟩ : syracuseStep 3543373 = 1328765) (by norm_num)
theorem B4724497 : Blo 1965435 4724497 := bstep (se 2 (by rfl) ⟨1771686, by rfl⟩ : syracuseStep 4724497 = 3543373) B3543373
theorem B25197317 : Blo 1965435 25197317 := bstep (se 4 (by rfl) ⟨2362248, by rfl⟩ : syracuseStep 25197317 = 4724497) B4724497
theorem B16798211 : Blo 1965435 16798211 := bstep (se 1 (by rfl) ⟨12598658, by rfl⟩ : syracuseStep 16798211 = 25197317) B25197317
theorem B11198807 : Blo 1965435 11198807 := bstep (se 1 (by rfl) ⟨8399105, by rfl⟩ : syracuseStep 11198807 = 16798211) B16798211
theorem B7465871 : Blo 1965435 7465871 := bstep (se 1 (by rfl) ⟨5599403, by rfl⟩ : syracuseStep 7465871 = 11198807) B11198807
theorem B4977247 : Blo 1965435 4977247 := bstep (se 1 (by rfl) ⟨3732935, by rfl⟩ : syracuseStep 4977247 = 7465871) B7465871
theorem B6636329 : Blo 1965435 6636329 := bstep (se 2 (by rfl) ⟨2488623, by rfl⟩ : syracuseStep 6636329 = 4977247) B4977247
theorem B4424219 : Blo 1965435 4424219 := bstep (se 1 (by rfl) ⟨3318164, by rfl⟩ : syracuseStep 4424219 = 6636329) B6636329
theorem B2949479 : Blo 1965435 2949479 := bstep (se 1 (by rfl) ⟨2212109, by rfl⟩ : syracuseStep 2949479 = 4424219) B4424219
theorem B1966319 : Blo 1965435 1966319 := bstep (se 1 (by rfl) ⟨1474739, by rfl⟩ : syracuseStep 1966319 = 2949479) B2949479
theorem B2949485 : Blo 1965435 2949485 := bbase (se 3 (by rfl) ⟨553028, by rfl⟩ : syracuseStep 2949485 = 1106057) (by norm_num)
theorem B1966323 : Blo 1965435 1966323 := bstep (se 1 (by rfl) ⟨1474742, by rfl⟩ : syracuseStep 1966323 = 2949485) B2949485
theorem B4424237 : Blo 1965435 4424237 := bbase (se 3 (by rfl) ⟨829544, by rfl⟩ : syracuseStep 4424237 = 1659089) (by norm_num)
theorem B2949491 : Blo 1965435 2949491 := bstep (se 1 (by rfl) ⟨2212118, by rfl⟩ : syracuseStep 2949491 = 4424237) B4424237
theorem B1966327 : Blo 1965435 1966327 := bstep (se 1 (by rfl) ⟨1474745, by rfl⟩ : syracuseStep 1966327 = 2949491) B2949491
theorem B8969221 : Blo 1965435 8969221 := bbase (se 4 (by rfl) ⟨840864, by rfl⟩ : syracuseStep 8969221 = 1681729) (by norm_num)
theorem B11958961 : Blo 1965435 11958961 := bstep (se 2 (by rfl) ⟨4484610, by rfl⟩ : syracuseStep 11958961 = 8969221) B8969221
theorem B15945281 : Blo 1965435 15945281 := bstep (se 2 (by rfl) ⟨5979480, by rfl⟩ : syracuseStep 15945281 = 11958961) B11958961
theorem B10630187 : Blo 1965435 10630187 := bstep (se 1 (by rfl) ⟨7972640, by rfl⟩ : syracuseStep 10630187 = 15945281) B15945281
theorem B7086791 : Blo 1965435 7086791 := bstep (se 1 (by rfl) ⟨5315093, by rfl⟩ : syracuseStep 7086791 = 10630187) B10630187
theorem B18898109 : Blo 1965435 18898109 := bstep (se 3 (by rfl) ⟨3543395, by rfl⟩ : syracuseStep 18898109 = 7086791) B7086791
theorem B12598739 : Blo 1965435 12598739 := bstep (se 1 (by rfl) ⟨9449054, by rfl⟩ : syracuseStep 12598739 = 18898109) B18898109
theorem B8399159 : Blo 1965435 8399159 := bstep (se 1 (by rfl) ⟨6299369, by rfl⟩ : syracuseStep 8399159 = 12598739) B12598739
theorem B5599439 : Blo 1965435 5599439 := bstep (se 1 (by rfl) ⟨4199579, by rfl⟩ : syracuseStep 5599439 = 8399159) B8399159
theorem B3732959 : Blo 1965435 3732959 := bstep (se 1 (by rfl) ⟨2799719, by rfl⟩ : syracuseStep 3732959 = 5599439) B5599439
theorem B2488639 : Blo 1965435 2488639 := bstep (se 1 (by rfl) ⟨1866479, by rfl⟩ : syracuseStep 2488639 = 3732959) B3732959
theorem B3318185 : Blo 1965435 3318185 := bstep (se 2 (by rfl) ⟨1244319, by rfl⟩ : syracuseStep 3318185 = 2488639) B2488639
theorem B2212123 : Blo 1965435 2212123 := bstep (se 1 (by rfl) ⟨1659092, by rfl⟩ : syracuseStep 2212123 = 3318185) B3318185
theorem B2949497 : Blo 1965435 2949497 := bstep (se 2 (by rfl) ⟨1106061, by rfl⟩ : syracuseStep 2949497 = 2212123) B2212123
theorem B1966331 : Blo 1965435 1966331 := bstep (se 1 (by rfl) ⟨1474748, by rfl⟩ : syracuseStep 1966331 = 2949497) B2949497
theorem B33596693 : Blo 1965435 33596693 := bbase (se 6 (by rfl) ⟨787422, by rfl⟩ : syracuseStep 33596693 = 1574845) (by norm_num)
theorem B22397795 : Blo 1965435 22397795 := bstep (se 1 (by rfl) ⟨16798346, by rfl⟩ : syracuseStep 22397795 = 33596693) B33596693
theorem B14931863 : Blo 1965435 14931863 := bstep (se 1 (by rfl) ⟨11198897, by rfl⟩ : syracuseStep 14931863 = 22397795) B22397795
theorem B9954575 : Blo 1965435 9954575 := bstep (se 1 (by rfl) ⟨7465931, by rfl⟩ : syracuseStep 9954575 = 14931863) B14931863
theorem B6636383 : Blo 1965435 6636383 := bstep (se 1 (by rfl) ⟨4977287, by rfl⟩ : syracuseStep 6636383 = 9954575) B9954575
theorem B4424255 : Blo 1965435 4424255 := bstep (se 1 (by rfl) ⟨3318191, by rfl⟩ : syracuseStep 4424255 = 6636383) B6636383
theorem B2949503 : Blo 1965435 2949503 := bstep (se 1 (by rfl) ⟨2212127, by rfl⟩ : syracuseStep 2949503 = 4424255) B4424255
theorem B1966335 : Blo 1965435 1966335 := bstep (se 1 (by rfl) ⟨1474751, by rfl⟩ : syracuseStep 1966335 = 2949503) B2949503
theorem B2949509 : Blo 1965435 2949509 := bbase (se 4 (by rfl) ⟨276516, by rfl⟩ : syracuseStep 2949509 = 553033) (by norm_num)
theorem B1966339 : Blo 1965435 1966339 := bstep (se 1 (by rfl) ⟨1474754, by rfl⟩ : syracuseStep 1966339 = 2949509) B2949509
theorem B3318205 : Blo 1965435 3318205 := bbase (se 3 (by rfl) ⟨622163, by rfl⟩ : syracuseStep 3318205 = 1244327) (by norm_num)
theorem B4424273 : Blo 1965435 4424273 := bstep (se 2 (by rfl) ⟨1659102, by rfl⟩ : syracuseStep 4424273 = 3318205) B3318205
theorem B2949515 : Blo 1965435 2949515 := bstep (se 1 (by rfl) ⟨2212136, by rfl⟩ : syracuseStep 2949515 = 4424273) B4424273
theorem B1966343 : Blo 1965435 1966343 := bstep (se 1 (by rfl) ⟨1474757, by rfl⟩ : syracuseStep 1966343 = 2949515) B2949515
theorem B2212141 : Blo 1965435 2212141 := bbase (se 3 (by rfl) ⟨414776, by rfl⟩ : syracuseStep 2212141 = 829553) (by norm_num)
theorem B2949521 : Blo 1965435 2949521 := bstep (se 2 (by rfl) ⟨1106070, by rfl⟩ : syracuseStep 2949521 = 2212141) B2212141
theorem B1966347 : Blo 1965435 1966347 := bstep (se 1 (by rfl) ⟨1474760, by rfl⟩ : syracuseStep 1966347 = 2949521) B2949521
theorem B6636437 : Blo 1965435 6636437 := bbase (se 6 (by rfl) ⟨155541, by rfl⟩ : syracuseStep 6636437 = 311083) (by norm_num)
theorem B4424291 : Blo 1965435 4424291 := bstep (se 1 (by rfl) ⟨3318218, by rfl⟩ : syracuseStep 4424291 = 6636437) B6636437
theorem B2949527 : Blo 1965435 2949527 := bstep (se 1 (by rfl) ⟨2212145, by rfl⟩ : syracuseStep 2949527 = 4424291) B4424291
theorem B1966351 : Blo 1965435 1966351 := bstep (se 1 (by rfl) ⟨1474763, by rfl⟩ : syracuseStep 1966351 = 2949527) B2949527
theorem B2949533 : Blo 1965435 2949533 := bbase (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) (by norm_num)
theorem B1966355 : Blo 1965435 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B4424309 : Blo 1965435 4424309 := bbase (se 5 (by rfl) ⟨207389, by rfl⟩ : syracuseStep 4424309 = 414779) (by norm_num)
theorem B2949539 : Blo 1965435 2949539 := bstep (se 1 (by rfl) ⟨2212154, by rfl⟩ : syracuseStep 2949539 = 4424309) B4424309
theorem B1966359 : Blo 1965435 1966359 := bstep (se 1 (by rfl) ⟨1474769, by rfl⟩ : syracuseStep 1966359 = 2949539) B2949539
theorem B5045269 : Blo 1965435 5045269 := bbase (se 6 (by rfl) ⟨118248, by rfl⟩ : syracuseStep 5045269 = 236497) (by norm_num)
theorem B6727025 : Blo 1965435 6727025 := bstep (se 2 (by rfl) ⟨2522634, by rfl⟩ : syracuseStep 6727025 = 5045269) B5045269
theorem B4484683 : Blo 1965435 4484683 := bstep (se 1 (by rfl) ⟨3363512, by rfl⟩ : syracuseStep 4484683 = 6727025) B6727025
theorem B5979577 : Blo 1965435 5979577 := bstep (se 2 (by rfl) ⟨2242341, by rfl⟩ : syracuseStep 5979577 = 4484683) B4484683
theorem B7972769 : Blo 1965435 7972769 := bstep (se 2 (by rfl) ⟨2989788, by rfl⟩ : syracuseStep 7972769 = 5979577) B5979577
theorem B21260717 : Blo 1965435 21260717 := bstep (se 3 (by rfl) ⟨3986384, by rfl⟩ : syracuseStep 21260717 = 7972769) B7972769
theorem B14173811 : Blo 1965435 14173811 := bstep (se 1 (by rfl) ⟨10630358, by rfl⟩ : syracuseStep 14173811 = 21260717) B21260717
theorem B9449207 : Blo 1965435 9449207 := bstep (se 1 (by rfl) ⟨7086905, by rfl⟩ : syracuseStep 9449207 = 14173811) B14173811
theorem B6299471 : Blo 1965435 6299471 := bstep (se 1 (by rfl) ⟨4724603, by rfl⟩ : syracuseStep 6299471 = 9449207) B9449207
theorem B16798589 : Blo 1965435 16798589 := bstep (se 3 (by rfl) ⟨3149735, by rfl⟩ : syracuseStep 16798589 = 6299471) B6299471
theorem B11199059 : Blo 1965435 11199059 := bstep (se 1 (by rfl) ⟨8399294, by rfl⟩ : syracuseStep 11199059 = 16798589) B16798589
theorem B7466039 : Blo 1965435 7466039 := bstep (se 1 (by rfl) ⟨5599529, by rfl⟩ : syracuseStep 7466039 = 11199059) B11199059
theorem B4977359 : Blo 1965435 4977359 := bstep (se 1 (by rfl) ⟨3733019, by rfl⟩ : syracuseStep 4977359 = 7466039) B7466039
theorem B3318239 : Blo 1965435 3318239 := bstep (se 1 (by rfl) ⟨2488679, by rfl⟩ : syracuseStep 3318239 = 4977359) B4977359
theorem B2212159 : Blo 1965435 2212159 := bstep (se 1 (by rfl) ⟨1659119, by rfl⟩ : syracuseStep 2212159 = 3318239) B3318239
theorem B2949545 : Blo 1965435 2949545 := bstep (se 2 (by rfl) ⟨1106079, by rfl⟩ : syracuseStep 2949545 = 2212159) B2212159
theorem B1966363 : Blo 1965435 1966363 := bstep (se 1 (by rfl) ⟨1474772, by rfl⟩ : syracuseStep 1966363 = 2949545) B2949545
theorem B7466053 : Blo 1965435 7466053 := bbase (se 4 (by rfl) ⟨699942, by rfl⟩ : syracuseStep 7466053 = 1399885) (by norm_num)
theorem B9954737 : Blo 1965435 9954737 := bstep (se 2 (by rfl) ⟨3733026, by rfl⟩ : syracuseStep 9954737 = 7466053) B7466053
theorem B6636491 : Blo 1965435 6636491 := bstep (se 1 (by rfl) ⟨4977368, by rfl⟩ : syracuseStep 6636491 = 9954737) B9954737
theorem B4424327 : Blo 1965435 4424327 := bstep (se 1 (by rfl) ⟨3318245, by rfl⟩ : syracuseStep 4424327 = 6636491) B6636491
theorem B2949551 : Blo 1965435 2949551 := bstep (se 1 (by rfl) ⟨2212163, by rfl⟩ : syracuseStep 2949551 = 4424327) B4424327
theorem B1966367 : Blo 1965435 1966367 := bstep (se 1 (by rfl) ⟨1474775, by rfl⟩ : syracuseStep 1966367 = 2949551) B2949551
theorem B2949557 : Blo 1965435 2949557 := bbase (se 5 (by rfl) ⟨138260, by rfl⟩ : syracuseStep 2949557 = 276521) (by norm_num)
theorem B1966371 : Blo 1965435 1966371 := bstep (se 1 (by rfl) ⟨1474778, by rfl⟩ : syracuseStep 1966371 = 2949557) B2949557
theorem B4977389 : Blo 1965435 4977389 := bbase (se 3 (by rfl) ⟨933260, by rfl⟩ : syracuseStep 4977389 = 1866521) (by norm_num)
theorem B3318259 : Blo 1965435 3318259 := bstep (se 1 (by rfl) ⟨2488694, by rfl⟩ : syracuseStep 3318259 = 4977389) B4977389
theorem B4424345 : Blo 1965435 4424345 := bstep (se 2 (by rfl) ⟨1659129, by rfl⟩ : syracuseStep 4424345 = 3318259) B3318259
theorem B2949563 : Blo 1965435 2949563 := bstep (se 1 (by rfl) ⟨2212172, by rfl⟩ : syracuseStep 2949563 = 4424345) B4424345
theorem B1966375 : Blo 1965435 1966375 := bstep (se 1 (by rfl) ⟨1474781, by rfl⟩ : syracuseStep 1966375 = 2949563) B2949563
theorem B2212177 : Blo 1965435 2212177 := bbase (se 2 (by rfl) ⟨829566, by rfl⟩ : syracuseStep 2212177 = 1659133) (by norm_num)
theorem B2949569 : Blo 1965435 2949569 := bstep (se 2 (by rfl) ⟨1106088, by rfl⟩ : syracuseStep 2949569 = 2212177) B2212177
theorem B1966379 : Blo 1965435 1966379 := bstep (se 1 (by rfl) ⟨1474784, by rfl⟩ : syracuseStep 1966379 = 2949569) B2949569
theorem B2099845 : Blo 1965435 2099845 := bbase (se 4 (by rfl) ⟨196860, by rfl⟩ : syracuseStep 2099845 = 393721) (by norm_num)
theorem B2799793 : Blo 1965435 2799793 := bstep (se 2 (by rfl) ⟨1049922, by rfl⟩ : syracuseStep 2799793 = 2099845) B2099845
theorem B3733057 : Blo 1965435 3733057 := bstep (se 2 (by rfl) ⟨1399896, by rfl⟩ : syracuseStep 3733057 = 2799793) B2799793
theorem B4977409 : Blo 1965435 4977409 := bstep (se 2 (by rfl) ⟨1866528, by rfl⟩ : syracuseStep 4977409 = 3733057) B3733057
theorem B6636545 : Blo 1965435 6636545 := bstep (se 2 (by rfl) ⟨2488704, by rfl⟩ : syracuseStep 6636545 = 4977409) B4977409
theorem B4424363 : Blo 1965435 4424363 := bstep (se 1 (by rfl) ⟨3318272, by rfl⟩ : syracuseStep 4424363 = 6636545) B6636545
theorem B2949575 : Blo 1965435 2949575 := bstep (se 1 (by rfl) ⟨2212181, by rfl⟩ : syracuseStep 2949575 = 4424363) B4424363
theorem B1966383 : Blo 1965435 1966383 := bstep (se 1 (by rfl) ⟨1474787, by rfl⟩ : syracuseStep 1966383 = 2949575) B2949575
theorem B2949581 : Blo 1965435 2949581 := bbase (se 3 (by rfl) ⟨553046, by rfl⟩ : syracuseStep 2949581 = 1106093) (by norm_num)
theorem B1966387 : Blo 1965435 1966387 := bstep (se 1 (by rfl) ⟨1474790, by rfl⟩ : syracuseStep 1966387 = 2949581) B2949581
theorem B4424381 : Blo 1965435 4424381 := bbase (se 3 (by rfl) ⟨829571, by rfl⟩ : syracuseStep 4424381 = 1659143) (by norm_num)
theorem B2949587 : Blo 1965435 2949587 := bstep (se 1 (by rfl) ⟨2212190, by rfl⟩ : syracuseStep 2949587 = 4424381) B4424381
theorem B1966391 : Blo 1965435 1966391 := bstep (se 1 (by rfl) ⟨1474793, by rfl⟩ : syracuseStep 1966391 = 2949587) B2949587
theorem B3318293 : Blo 1965435 3318293 := bbase (se 6 (by rfl) ⟨77772, by rfl⟩ : syracuseStep 3318293 = 155545) (by norm_num)
theorem B2212195 : Blo 1965435 2212195 := bstep (se 1 (by rfl) ⟨1659146, by rfl⟩ : syracuseStep 2212195 = 3318293) B3318293
theorem B2949593 : Blo 1965435 2949593 := bstep (se 2 (by rfl) ⟨1106097, by rfl⟩ : syracuseStep 2949593 = 2212195) B2212195
theorem B1966395 : Blo 1965435 1966395 := bstep (se 1 (by rfl) ⟨1474796, by rfl⟩ : syracuseStep 1966395 = 2949593) B2949593
theorem B3543517 : Blo 1965435 3543517 := bbase (se 3 (by rfl) ⟨664409, by rfl⟩ : syracuseStep 3543517 = 1328819) (by norm_num)
theorem B18898757 : Blo 1965435 18898757 := bstep (se 4 (by rfl) ⟨1771758, by rfl⟩ : syracuseStep 18898757 = 3543517) B3543517
theorem B12599171 : Blo 1965435 12599171 := bstep (se 1 (by rfl) ⟨9449378, by rfl⟩ : syracuseStep 12599171 = 18898757) B18898757
theorem B8399447 : Blo 1965435 8399447 := bstep (se 1 (by rfl) ⟨6299585, by rfl⟩ : syracuseStep 8399447 = 12599171) B12599171
theorem B5599631 : Blo 1965435 5599631 := bstep (se 1 (by rfl) ⟨4199723, by rfl⟩ : syracuseStep 5599631 = 8399447) B8399447
theorem B14932349 : Blo 1965435 14932349 := bstep (se 3 (by rfl) ⟨2799815, by rfl⟩ : syracuseStep 14932349 = 5599631) B5599631
theorem B9954899 : Blo 1965435 9954899 := bstep (se 1 (by rfl) ⟨7466174, by rfl⟩ : syracuseStep 9954899 = 14932349) B14932349
theorem B6636599 : Blo 1965435 6636599 := bstep (se 1 (by rfl) ⟨4977449, by rfl⟩ : syracuseStep 6636599 = 9954899) B9954899
theorem B4424399 : Blo 1965435 4424399 := bstep (se 1 (by rfl) ⟨3318299, by rfl⟩ : syracuseStep 4424399 = 6636599) B6636599
theorem B2949599 : Blo 1965435 2949599 := bstep (se 1 (by rfl) ⟨2212199, by rfl⟩ : syracuseStep 2949599 = 4424399) B4424399
theorem B1966399 : Blo 1965435 1966399 := bstep (se 1 (by rfl) ⟨1474799, by rfl⟩ : syracuseStep 1966399 = 2949599) B2949599
theorem B2949605 : Blo 1965435 2949605 := bbase (se 4 (by rfl) ⟨276525, by rfl⟩ : syracuseStep 2949605 = 553051) (by norm_num)
theorem B1966403 : Blo 1965435 1966403 := bstep (se 1 (by rfl) ⟨1474802, by rfl⟩ : syracuseStep 1966403 = 2949605) B2949605
theorem B1993237 : Blo 1965435 1993237 := bbase (se 6 (by rfl) ⟨46716, by rfl⟩ : syracuseStep 1993237 = 93433) (by norm_num)
theorem B10630597 : Blo 1965435 10630597 := bstep (se 4 (by rfl) ⟨996618, by rfl⟩ : syracuseStep 10630597 = 1993237) B1993237
theorem B14174129 : Blo 1965435 14174129 := bstep (se 2 (by rfl) ⟨5315298, by rfl⟩ : syracuseStep 14174129 = 10630597) B10630597
theorem B9449419 : Blo 1965435 9449419 := bstep (se 1 (by rfl) ⟨7087064, by rfl⟩ : syracuseStep 9449419 = 14174129) B14174129
theorem B12599225 : Blo 1965435 12599225 := bstep (se 2 (by rfl) ⟨4724709, by rfl⟩ : syracuseStep 12599225 = 9449419) B9449419
theorem B8399483 : Blo 1965435 8399483 := bstep (se 1 (by rfl) ⟨6299612, by rfl⟩ : syracuseStep 8399483 = 12599225) B12599225
theorem B5599655 : Blo 1965435 5599655 := bstep (se 1 (by rfl) ⟨4199741, by rfl⟩ : syracuseStep 5599655 = 8399483) B8399483
theorem B3733103 : Blo 1965435 3733103 := bstep (se 1 (by rfl) ⟨2799827, by rfl⟩ : syracuseStep 3733103 = 5599655) B5599655
theorem B2488735 : Blo 1965435 2488735 := bstep (se 1 (by rfl) ⟨1866551, by rfl⟩ : syracuseStep 2488735 = 3733103) B3733103
theorem B3318313 : Blo 1965435 3318313 := bstep (se 2 (by rfl) ⟨1244367, by rfl⟩ : syracuseStep 3318313 = 2488735) B2488735
theorem B4424417 : Blo 1965435 4424417 := bstep (se 2 (by rfl) ⟨1659156, by rfl⟩ : syracuseStep 4424417 = 3318313) B3318313
theorem B2949611 : Blo 1965435 2949611 := bstep (se 1 (by rfl) ⟨2212208, by rfl⟩ : syracuseStep 2949611 = 4424417) B4424417
theorem B1966407 : Blo 1965435 1966407 := bstep (se 1 (by rfl) ⟨1474805, by rfl⟩ : syracuseStep 1966407 = 2949611) B2949611
theorem B2212213 : Blo 1965435 2212213 := bbase (se 5 (by rfl) ⟨103697, by rfl⟩ : syracuseStep 2212213 = 207395) (by norm_num)
theorem B2949617 : Blo 1965435 2949617 := bstep (se 2 (by rfl) ⟨1106106, by rfl⟩ : syracuseStep 2949617 = 2212213) B2212213
theorem B1966411 : Blo 1965435 1966411 := bstep (se 1 (by rfl) ⟨1474808, by rfl⟩ : syracuseStep 1966411 = 2949617) B2949617
theorem B2488745 : Blo 1965435 2488745 := bbase (se 2 (by rfl) ⟨933279, by rfl⟩ : syracuseStep 2488745 = 1866559) (by norm_num)
theorem B6636653 : Blo 1965435 6636653 := bstep (se 3 (by rfl) ⟨1244372, by rfl⟩ : syracuseStep 6636653 = 2488745) B2488745
theorem B4424435 : Blo 1965435 4424435 := bstep (se 1 (by rfl) ⟨3318326, by rfl⟩ : syracuseStep 4424435 = 6636653) B6636653
theorem B2949623 : Blo 1965435 2949623 := bstep (se 1 (by rfl) ⟨2212217, by rfl⟩ : syracuseStep 2949623 = 4424435) B4424435
theorem B1966415 : Blo 1965435 1966415 := bstep (se 1 (by rfl) ⟨1474811, by rfl⟩ : syracuseStep 1966415 = 2949623) B2949623
theorem B2949629 : Blo 1965435 2949629 := bbase (se 3 (by rfl) ⟨553055, by rfl⟩ : syracuseStep 2949629 = 1106111) (by norm_num)
theorem B1966419 : Blo 1965435 1966419 := bstep (se 1 (by rfl) ⟨1474814, by rfl⟩ : syracuseStep 1966419 = 2949629) B2949629
theorem B4424453 : Blo 1965435 4424453 := bbase (se 4 (by rfl) ⟨414792, by rfl⟩ : syracuseStep 4424453 = 829585) (by norm_num)
theorem B2949635 : Blo 1965435 2949635 := bstep (se 1 (by rfl) ⟨2212226, by rfl⟩ : syracuseStep 2949635 = 4424453) B4424453
theorem B1966423 : Blo 1965435 1966423 := bstep (se 1 (by rfl) ⟨1474817, by rfl⟩ : syracuseStep 1966423 = 2949635) B2949635
theorem B3733141 : Blo 1965435 3733141 := bbase (se 6 (by rfl) ⟨87495, by rfl⟩ : syracuseStep 3733141 = 174991) (by norm_num)
theorem B4977521 : Blo 1965435 4977521 := bstep (se 2 (by rfl) ⟨1866570, by rfl⟩ : syracuseStep 4977521 = 3733141) B3733141
theorem B3318347 : Blo 1965435 3318347 := bstep (se 1 (by rfl) ⟨2488760, by rfl⟩ : syracuseStep 3318347 = 4977521) B4977521
theorem B2212231 : Blo 1965435 2212231 := bstep (se 1 (by rfl) ⟨1659173, by rfl⟩ : syracuseStep 2212231 = 3318347) B3318347
theorem B2949641 : Blo 1965435 2949641 := bstep (se 2 (by rfl) ⟨1106115, by rfl⟩ : syracuseStep 2949641 = 2212231) B2212231
theorem B1966427 : Blo 1965435 1966427 := bstep (se 1 (by rfl) ⟨1474820, by rfl⟩ : syracuseStep 1966427 = 2949641) B2949641
theorem B9955061 : Blo 1965435 9955061 := bbase (se 5 (by rfl) ⟨466643, by rfl⟩ : syracuseStep 9955061 = 933287) (by norm_num)
theorem B6636707 : Blo 1965435 6636707 := bstep (se 1 (by rfl) ⟨4977530, by rfl⟩ : syracuseStep 6636707 = 9955061) B9955061
theorem B4424471 : Blo 1965435 4424471 := bstep (se 1 (by rfl) ⟨3318353, by rfl⟩ : syracuseStep 4424471 = 6636707) B6636707
theorem B2949647 : Blo 1965435 2949647 := bstep (se 1 (by rfl) ⟨2212235, by rfl⟩ : syracuseStep 2949647 = 4424471) B4424471
theorem B1966431 : Blo 1965435 1966431 := bstep (se 1 (by rfl) ⟨1474823, by rfl⟩ : syracuseStep 1966431 = 2949647) B2949647
theorem B2949653 : Blo 1965435 2949653 := bbase (se 6 (by rfl) ⟨69132, by rfl⟩ : syracuseStep 2949653 = 138265) (by norm_num)
theorem B1966435 : Blo 1965435 1966435 := bstep (se 1 (by rfl) ⟨1474826, by rfl⟩ : syracuseStep 1966435 = 2949653) B2949653
theorem B2362393 : Blo 1965435 2362393 := bbase (se 2 (by rfl) ⟨885897, by rfl⟩ : syracuseStep 2362393 = 1771795) (by norm_num)
theorem B3149857 : Blo 1965435 3149857 := bstep (se 2 (by rfl) ⟨1181196, by rfl⟩ : syracuseStep 3149857 = 2362393) B2362393
theorem B16799237 : Blo 1965435 16799237 := bstep (se 4 (by rfl) ⟨1574928, by rfl⟩ : syracuseStep 16799237 = 3149857) B3149857
theorem B11199491 : Blo 1965435 11199491 := bstep (se 1 (by rfl) ⟨8399618, by rfl⟩ : syracuseStep 11199491 = 16799237) B16799237
theorem B7466327 : Blo 1965435 7466327 := bstep (se 1 (by rfl) ⟨5599745, by rfl⟩ : syracuseStep 7466327 = 11199491) B11199491
theorem B4977551 : Blo 1965435 4977551 := bstep (se 1 (by rfl) ⟨3733163, by rfl⟩ : syracuseStep 4977551 = 7466327) B7466327
theorem B3318367 : Blo 1965435 3318367 := bstep (se 1 (by rfl) ⟨2488775, by rfl⟩ : syracuseStep 3318367 = 4977551) B4977551
theorem B4424489 : Blo 1965435 4424489 := bstep (se 2 (by rfl) ⟨1659183, by rfl⟩ : syracuseStep 4424489 = 3318367) B3318367
theorem B2949659 : Blo 1965435 2949659 := bstep (se 1 (by rfl) ⟨2212244, by rfl⟩ : syracuseStep 2949659 = 4424489) B4424489
theorem B1966439 : Blo 1965435 1966439 := bstep (se 1 (by rfl) ⟨1474829, by rfl⟩ : syracuseStep 1966439 = 2949659) B2949659
theorem B2212249 : Blo 1965435 2212249 := bbase (se 2 (by rfl) ⟨829593, by rfl⟩ : syracuseStep 2212249 = 1659187) (by norm_num)
theorem B2949665 : Blo 1965435 2949665 := bstep (se 2 (by rfl) ⟨1106124, by rfl⟩ : syracuseStep 2949665 = 2212249) B2212249
theorem B1966443 : Blo 1965435 1966443 := bstep (se 1 (by rfl) ⟨1474832, by rfl⟩ : syracuseStep 1966443 = 2949665) B2949665
theorem B7466357 : Blo 1965435 7466357 := bbase (se 5 (by rfl) ⟨349985, by rfl⟩ : syracuseStep 7466357 = 699971) (by norm_num)
theorem B4977571 : Blo 1965435 4977571 := bstep (se 1 (by rfl) ⟨3733178, by rfl⟩ : syracuseStep 4977571 = 7466357) B7466357
theorem B6636761 : Blo 1965435 6636761 := bstep (se 2 (by rfl) ⟨2488785, by rfl⟩ : syracuseStep 6636761 = 4977571) B4977571
theorem B4424507 : Blo 1965435 4424507 := bstep (se 1 (by rfl) ⟨3318380, by rfl⟩ : syracuseStep 4424507 = 6636761) B6636761
theorem B2949671 : Blo 1965435 2949671 := bstep (se 1 (by rfl) ⟨2212253, by rfl⟩ : syracuseStep 2949671 = 4424507) B4424507
theorem B1966447 : Blo 1965435 1966447 := bstep (se 1 (by rfl) ⟨1474835, by rfl⟩ : syracuseStep 1966447 = 2949671) B2949671
theorem B2949677 : Blo 1965435 2949677 := bbase (se 3 (by rfl) ⟨553064, by rfl⟩ : syracuseStep 2949677 = 1106129) (by norm_num)
theorem B1966451 : Blo 1965435 1966451 := bstep (se 1 (by rfl) ⟨1474838, by rfl⟩ : syracuseStep 1966451 = 2949677) B2949677
theorem B4424525 : Blo 1965435 4424525 := bbase (se 3 (by rfl) ⟨829598, by rfl⟩ : syracuseStep 4424525 = 1659197) (by norm_num)
theorem B2949683 : Blo 1965435 2949683 := bstep (se 1 (by rfl) ⟨2212262, by rfl⟩ : syracuseStep 2949683 = 4424525) B4424525
theorem B1966455 : Blo 1965435 1966455 := bstep (se 1 (by rfl) ⟨1474841, by rfl⟩ : syracuseStep 1966455 = 2949683) B2949683
theorem B2488801 : Blo 1965435 2488801 := bbase (se 2 (by rfl) ⟨933300, by rfl⟩ : syracuseStep 2488801 = 1866601) (by norm_num)
theorem B3318401 : Blo 1965435 3318401 := bstep (se 2 (by rfl) ⟨1244400, by rfl⟩ : syracuseStep 3318401 = 2488801) B2488801
theorem B2212267 : Blo 1965435 2212267 := bstep (se 1 (by rfl) ⟨1659200, by rfl⟩ : syracuseStep 2212267 = 3318401) B3318401
theorem B2949689 : Blo 1965435 2949689 := bstep (se 2 (by rfl) ⟨1106133, by rfl⟩ : syracuseStep 2949689 = 2212267) B2212267
theorem B1966459 : Blo 1965435 1966459 := bstep (se 1 (by rfl) ⟨1474844, by rfl⟩ : syracuseStep 1966459 = 2949689) B2949689
theorem B22399253 : Blo 1965435 22399253 := bbase (se 6 (by rfl) ⟨524982, by rfl⟩ : syracuseStep 22399253 = 1049965) (by norm_num)
theorem B14932835 : Blo 1965435 14932835 := bstep (se 1 (by rfl) ⟨11199626, by rfl⟩ : syracuseStep 14932835 = 22399253) B22399253
theorem B9955223 : Blo 1965435 9955223 := bstep (se 1 (by rfl) ⟨7466417, by rfl⟩ : syracuseStep 9955223 = 14932835) B14932835
theorem B6636815 : Blo 1965435 6636815 := bstep (se 1 (by rfl) ⟨4977611, by rfl⟩ : syracuseStep 6636815 = 9955223) B9955223
theorem B4424543 : Blo 1965435 4424543 := bstep (se 1 (by rfl) ⟨3318407, by rfl⟩ : syracuseStep 4424543 = 6636815) B6636815
theorem B2949695 : Blo 1965435 2949695 := bstep (se 1 (by rfl) ⟨2212271, by rfl⟩ : syracuseStep 2949695 = 4424543) B4424543
theorem B1966463 : Blo 1965435 1966463 := bstep (se 1 (by rfl) ⟨1474847, by rfl⟩ : syracuseStep 1966463 = 2949695) B2949695
theorem B2949701 : Blo 1965435 2949701 := bbase (se 4 (by rfl) ⟨276534, by rfl⟩ : syracuseStep 2949701 = 553069) (by norm_num)
theorem B1966467 : Blo 1965435 1966467 := bstep (se 1 (by rfl) ⟨1474850, by rfl⟩ : syracuseStep 1966467 = 2949701) B2949701
theorem B3318421 : Blo 1965435 3318421 := bbase (se 6 (by rfl) ⟨77775, by rfl⟩ : syracuseStep 3318421 = 155551) (by norm_num)
theorem B4424561 : Blo 1965435 4424561 := bstep (se 2 (by rfl) ⟨1659210, by rfl⟩ : syracuseStep 4424561 = 3318421) B3318421
theorem B2949707 : Blo 1965435 2949707 := bstep (se 1 (by rfl) ⟨2212280, by rfl⟩ : syracuseStep 2949707 = 4424561) B4424561
theorem B1966471 : Blo 1965435 1966471 := bstep (se 1 (by rfl) ⟨1474853, by rfl⟩ : syracuseStep 1966471 = 2949707) B2949707
theorem B2212285 : Blo 1965435 2212285 := bbase (se 3 (by rfl) ⟨414803, by rfl⟩ : syracuseStep 2212285 = 829607) (by norm_num)
theorem B2949713 : Blo 1965435 2949713 := bstep (se 2 (by rfl) ⟨1106142, by rfl⟩ : syracuseStep 2949713 = 2212285) B2212285
theorem B1966475 : Blo 1965435 1966475 := bstep (se 1 (by rfl) ⟨1474856, by rfl⟩ : syracuseStep 1966475 = 2949713) B2949713
theorem B6636869 : Blo 1965435 6636869 := bbase (se 4 (by rfl) ⟨622206, by rfl⟩ : syracuseStep 6636869 = 1244413) (by norm_num)
theorem B4424579 : Blo 1965435 4424579 := bstep (se 1 (by rfl) ⟨3318434, by rfl⟩ : syracuseStep 4424579 = 6636869) B6636869
theorem B2949719 : Blo 1965435 2949719 := bstep (se 1 (by rfl) ⟨2212289, by rfl⟩ : syracuseStep 2949719 = 4424579) B4424579
theorem B1966479 : Blo 1965435 1966479 := bstep (se 1 (by rfl) ⟨1474859, by rfl⟩ : syracuseStep 1966479 = 2949719) B2949719
theorem B2949725 : Blo 1965435 2949725 := bbase (se 3 (by rfl) ⟨553073, by rfl⟩ : syracuseStep 2949725 = 1106147) (by norm_num)
theorem B1966483 : Blo 1965435 1966483 := bstep (se 1 (by rfl) ⟨1474862, by rfl⟩ : syracuseStep 1966483 = 2949725) B2949725
theorem B4424597 : Blo 1965435 4424597 := bbase (se 6 (by rfl) ⟨103701, by rfl⟩ : syracuseStep 4424597 = 207403) (by norm_num)
theorem B2949731 : Blo 1965435 2949731 := bstep (se 1 (by rfl) ⟨2212298, by rfl⟩ : syracuseStep 2949731 = 4424597) B4424597
theorem B1966487 : Blo 1965435 1966487 := bstep (se 1 (by rfl) ⟨1474865, by rfl⟩ : syracuseStep 1966487 = 2949731) B2949731
theorem B3149941 : Blo 1965435 3149941 := bbase (se 5 (by rfl) ⟨147653, by rfl⟩ : syracuseStep 3149941 = 295307) (by norm_num)
theorem B4199921 : Blo 1965435 4199921 := bstep (se 2 (by rfl) ⟨1574970, by rfl⟩ : syracuseStep 4199921 = 3149941) B3149941
theorem B2799947 : Blo 1965435 2799947 := bstep (se 1 (by rfl) ⟨2099960, by rfl⟩ : syracuseStep 2799947 = 4199921) B4199921
theorem B7466525 : Blo 1965435 7466525 := bstep (se 3 (by rfl) ⟨1399973, by rfl⟩ : syracuseStep 7466525 = 2799947) B2799947
theorem B4977683 : Blo 1965435 4977683 := bstep (se 1 (by rfl) ⟨3733262, by rfl⟩ : syracuseStep 4977683 = 7466525) B7466525
theorem B3318455 : Blo 1965435 3318455 := bstep (se 1 (by rfl) ⟨2488841, by rfl⟩ : syracuseStep 3318455 = 4977683) B4977683
theorem B2212303 : Blo 1965435 2212303 := bstep (se 1 (by rfl) ⟨1659227, by rfl⟩ : syracuseStep 2212303 = 3318455) B3318455
theorem B2949737 : Blo 1965435 2949737 := bstep (se 2 (by rfl) ⟨1106151, by rfl⟩ : syracuseStep 2949737 = 2212303) B2212303
theorem B1966491 : Blo 1965435 1966491 := bstep (se 1 (by rfl) ⟨1474868, by rfl⟩ : syracuseStep 1966491 = 2949737) B2949737
theorem B6299893 : Blo 1965435 6299893 := bbase (se 5 (by rfl) ⟨295307, by rfl⟩ : syracuseStep 6299893 = 590615) (by norm_num)
theorem B8399857 : Blo 1965435 8399857 := bstep (se 2 (by rfl) ⟨3149946, by rfl⟩ : syracuseStep 8399857 = 6299893) B6299893
theorem B11199809 : Blo 1965435 11199809 := bstep (se 2 (by rfl) ⟨4199928, by rfl⟩ : syracuseStep 11199809 = 8399857) B8399857
theorem B7466539 : Blo 1965435 7466539 := bstep (se 1 (by rfl) ⟨5599904, by rfl⟩ : syracuseStep 7466539 = 11199809) B11199809
theorem B9955385 : Blo 1965435 9955385 := bstep (se 2 (by rfl) ⟨3733269, by rfl⟩ : syracuseStep 9955385 = 7466539) B7466539
theorem B6636923 : Blo 1965435 6636923 := bstep (se 1 (by rfl) ⟨4977692, by rfl⟩ : syracuseStep 6636923 = 9955385) B9955385
theorem B4424615 : Blo 1965435 4424615 := bstep (se 1 (by rfl) ⟨3318461, by rfl⟩ : syracuseStep 4424615 = 6636923) B6636923
theorem B2949743 : Blo 1965435 2949743 := bstep (se 1 (by rfl) ⟨2212307, by rfl⟩ : syracuseStep 2949743 = 4424615) B4424615
theorem B1966495 : Blo 1965435 1966495 := bstep (se 1 (by rfl) ⟨1474871, by rfl⟩ : syracuseStep 1966495 = 2949743) B2949743
theorem B2949749 : Blo 1965435 2949749 := bbase (se 5 (by rfl) ⟨138269, by rfl⟩ : syracuseStep 2949749 = 276539) (by norm_num)
theorem B1966499 : Blo 1965435 1966499 := bstep (se 1 (by rfl) ⟨1474874, by rfl⟩ : syracuseStep 1966499 = 2949749) B2949749
theorem B3733285 : Blo 1965435 3733285 := bbase (se 4 (by rfl) ⟨349995, by rfl⟩ : syracuseStep 3733285 = 699991) (by norm_num)
theorem B4977713 : Blo 1965435 4977713 := bstep (se 2 (by rfl) ⟨1866642, by rfl⟩ : syracuseStep 4977713 = 3733285) B3733285
theorem B3318475 : Blo 1965435 3318475 := bstep (se 1 (by rfl) ⟨2488856, by rfl⟩ : syracuseStep 3318475 = 4977713) B4977713
theorem B4424633 : Blo 1965435 4424633 := bstep (se 2 (by rfl) ⟨1659237, by rfl⟩ : syracuseStep 4424633 = 3318475) B3318475
theorem B2949755 : Blo 1965435 2949755 := bstep (se 1 (by rfl) ⟨2212316, by rfl⟩ : syracuseStep 2949755 = 4424633) B4424633
theorem B1966503 : Blo 1965435 1966503 := bstep (se 1 (by rfl) ⟨1474877, by rfl⟩ : syracuseStep 1966503 = 2949755) B2949755
theorem B2212321 : Blo 1965435 2212321 := bbase (se 2 (by rfl) ⟨829620, by rfl⟩ : syracuseStep 2212321 = 1659241) (by norm_num)
theorem B2949761 : Blo 1965435 2949761 := bstep (se 2 (by rfl) ⟨1106160, by rfl⟩ : syracuseStep 2949761 = 2212321) B2212321
theorem B1966507 : Blo 1965435 1966507 := bstep (se 1 (by rfl) ⟨1474880, by rfl⟩ : syracuseStep 1966507 = 2949761) B2949761
theorem B4977733 : Blo 1965435 4977733 := bbase (se 4 (by rfl) ⟨466662, by rfl⟩ : syracuseStep 4977733 = 933325) (by norm_num)
theorem B6636977 : Blo 1965435 6636977 := bstep (se 2 (by rfl) ⟨2488866, by rfl⟩ : syracuseStep 6636977 = 4977733) B4977733
theorem B4424651 : Blo 1965435 4424651 := bstep (se 1 (by rfl) ⟨3318488, by rfl⟩ : syracuseStep 4424651 = 6636977) B6636977
theorem B2949767 : Blo 1965435 2949767 := bstep (se 1 (by rfl) ⟨2212325, by rfl⟩ : syracuseStep 2949767 = 4424651) B4424651
theorem B1966511 : Blo 1965435 1966511 := bstep (se 1 (by rfl) ⟨1474883, by rfl⟩ : syracuseStep 1966511 = 2949767) B2949767
theorem B2949773 : Blo 1965435 2949773 := bbase (se 3 (by rfl) ⟨553082, by rfl⟩ : syracuseStep 2949773 = 1106165) (by norm_num)
theorem B1966515 : Blo 1965435 1966515 := bstep (se 1 (by rfl) ⟨1474886, by rfl⟩ : syracuseStep 1966515 = 2949773) B2949773
theorem B4424669 : Blo 1965435 4424669 := bbase (se 3 (by rfl) ⟨829625, by rfl⟩ : syracuseStep 4424669 = 1659251) (by norm_num)
theorem B2949779 : Blo 1965435 2949779 := bstep (se 1 (by rfl) ⟨2212334, by rfl⟩ : syracuseStep 2949779 = 4424669) B4424669
theorem B1966519 : Blo 1965435 1966519 := bstep (se 1 (by rfl) ⟨1474889, by rfl⟩ : syracuseStep 1966519 = 2949779) B2949779
theorem B3318509 : Blo 1965435 3318509 := bbase (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) (by norm_num)
theorem B2212339 : Blo 1965435 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B2949785 : Blo 1965435 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B1966523 : Blo 1965435 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B11960149 : Blo 1965435 11960149 := bbase (se 9 (by rfl) ⟨35039, by rfl⟩ : syracuseStep 11960149 = 70079) (by norm_num)
theorem B15946865 : Blo 1965435 15946865 := bstep (se 2 (by rfl) ⟨5980074, by rfl⟩ : syracuseStep 15946865 = 11960149) B11960149
theorem B10631243 : Blo 1965435 10631243 := bstep (se 1 (by rfl) ⟨7973432, by rfl⟩ : syracuseStep 10631243 = 15946865) B15946865
theorem B7087495 : Blo 1965435 7087495 := bstep (se 1 (by rfl) ⟨5315621, by rfl⟩ : syracuseStep 7087495 = 10631243) B10631243
theorem B9449993 : Blo 1965435 9449993 := bstep (se 2 (by rfl) ⟨3543747, by rfl⟩ : syracuseStep 9449993 = 7087495) B7087495
theorem B25199981 : Blo 1965435 25199981 := bstep (se 3 (by rfl) ⟨4724996, by rfl⟩ : syracuseStep 25199981 = 9449993) B9449993
theorem B16799987 : Blo 1965435 16799987 := bstep (se 1 (by rfl) ⟨12599990, by rfl⟩ : syracuseStep 16799987 = 25199981) B25199981
theorem B11199991 : Blo 1965435 11199991 := bstep (se 1 (by rfl) ⟨8399993, by rfl⟩ : syracuseStep 11199991 = 16799987) B16799987
theorem B14933321 : Blo 1965435 14933321 := bstep (se 2 (by rfl) ⟨5599995, by rfl⟩ : syracuseStep 14933321 = 11199991) B11199991
theorem B9955547 : Blo 1965435 9955547 := bstep (se 1 (by rfl) ⟨7466660, by rfl⟩ : syracuseStep 9955547 = 14933321) B14933321
theorem B6637031 : Blo 1965435 6637031 := bstep (se 1 (by rfl) ⟨4977773, by rfl⟩ : syracuseStep 6637031 = 9955547) B9955547
theorem B4424687 : Blo 1965435 4424687 := bstep (se 1 (by rfl) ⟨3318515, by rfl⟩ : syracuseStep 4424687 = 6637031) B6637031
theorem B2949791 : Blo 1965435 2949791 := bstep (se 1 (by rfl) ⟨2212343, by rfl⟩ : syracuseStep 2949791 = 4424687) B4424687
theorem B1966527 : Blo 1965435 1966527 := bstep (se 1 (by rfl) ⟨1474895, by rfl⟩ : syracuseStep 1966527 = 2949791) B2949791
theorem B2949797 : Blo 1965435 2949797 := bbase (se 4 (by rfl) ⟨276543, by rfl⟩ : syracuseStep 2949797 = 553087) (by norm_num)
theorem B1966531 : Blo 1965435 1966531 := bstep (se 1 (by rfl) ⟨1474898, by rfl⟩ : syracuseStep 1966531 = 2949797) B2949797
theorem B2488897 : Blo 1965435 2488897 := bbase (se 2 (by rfl) ⟨933336, by rfl⟩ : syracuseStep 2488897 = 1866673) (by norm_num)
theorem B3318529 : Blo 1965435 3318529 := bstep (se 2 (by rfl) ⟨1244448, by rfl⟩ : syracuseStep 3318529 = 2488897) B2488897
theorem B4424705 : Blo 1965435 4424705 := bstep (se 2 (by rfl) ⟨1659264, by rfl⟩ : syracuseStep 4424705 = 3318529) B3318529
theorem B2949803 : Blo 1965435 2949803 := bstep (se 1 (by rfl) ⟨2212352, by rfl⟩ : syracuseStep 2949803 = 4424705) B4424705
theorem B1966535 : Blo 1965435 1966535 := bstep (se 1 (by rfl) ⟨1474901, by rfl⟩ : syracuseStep 1966535 = 2949803) B2949803
theorem B2212357 : Blo 1965435 2212357 := bbase (se 4 (by rfl) ⟨207408, by rfl⟩ : syracuseStep 2212357 = 414817) (by norm_num)
theorem B2949809 : Blo 1965435 2949809 := bstep (se 2 (by rfl) ⟨1106178, by rfl⟩ : syracuseStep 2949809 = 2212357) B2212357
theorem B1966539 : Blo 1965435 1966539 := bstep (se 1 (by rfl) ⟨1474904, by rfl⟩ : syracuseStep 1966539 = 2949809) B2949809
theorem B2800021 : Blo 1965435 2800021 := bbase (se 6 (by rfl) ⟨65625, by rfl⟩ : syracuseStep 2800021 = 131251) (by norm_num)
theorem B3733361 : Blo 1965435 3733361 := bstep (se 2 (by rfl) ⟨1400010, by rfl⟩ : syracuseStep 3733361 = 2800021) B2800021
theorem B2488907 : Blo 1965435 2488907 := bstep (se 1 (by rfl) ⟨1866680, by rfl⟩ : syracuseStep 2488907 = 3733361) B3733361
theorem B6637085 : Blo 1965435 6637085 := bstep (se 3 (by rfl) ⟨1244453, by rfl⟩ : syracuseStep 6637085 = 2488907) B2488907
theorem B4424723 : Blo 1965435 4424723 := bstep (se 1 (by rfl) ⟨3318542, by rfl⟩ : syracuseStep 4424723 = 6637085) B6637085
theorem B2949815 : Blo 1965435 2949815 := bstep (se 1 (by rfl) ⟨2212361, by rfl⟩ : syracuseStep 2949815 = 4424723) B4424723
theorem B1966543 : Blo 1965435 1966543 := bstep (se 1 (by rfl) ⟨1474907, by rfl⟩ : syracuseStep 1966543 = 2949815) B2949815
theorem B2949821 : Blo 1965435 2949821 := bbase (se 3 (by rfl) ⟨553091, by rfl⟩ : syracuseStep 2949821 = 1106183) (by norm_num)
theorem B1966547 : Blo 1965435 1966547 := bstep (se 1 (by rfl) ⟨1474910, by rfl⟩ : syracuseStep 1966547 = 2949821) B2949821
theorem B4424741 : Blo 1965435 4424741 := bbase (se 4 (by rfl) ⟨414819, by rfl⟩ : syracuseStep 4424741 = 829639) (by norm_num)
theorem B2949827 : Blo 1965435 2949827 := bstep (se 1 (by rfl) ⟨2212370, by rfl⟩ : syracuseStep 2949827 = 4424741) B4424741
theorem B1966551 : Blo 1965435 1966551 := bstep (se 1 (by rfl) ⟨1474913, by rfl⟩ : syracuseStep 1966551 = 2949827) B2949827
theorem B4977845 : Blo 1965435 4977845 := bbase (se 5 (by rfl) ⟨233336, by rfl⟩ : syracuseStep 4977845 = 466673) (by norm_num)
theorem B3318563 : Blo 1965435 3318563 := bstep (se 1 (by rfl) ⟨2488922, by rfl⟩ : syracuseStep 3318563 = 4977845) B4977845
theorem B2212375 : Blo 1965435 2212375 := bstep (se 1 (by rfl) ⟨1659281, by rfl⟩ : syracuseStep 2212375 = 3318563) B3318563
theorem B2949833 : Blo 1965435 2949833 := bstep (se 2 (by rfl) ⟨1106187, by rfl⟩ : syracuseStep 2949833 = 2212375) B2212375
theorem B1966555 : Blo 1965435 1966555 := bstep (se 1 (by rfl) ⟨1474916, by rfl⟩ : syracuseStep 1966555 = 2949833) B2949833
theorem B2362537 : Blo 1965435 2362537 := bbase (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) (by norm_num)
theorem B12600197 : Blo 1965435 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B8400131 : Blo 1965435 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B5600087 : Blo 1965435 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B3733391 : Blo 1965435 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B9955709 : Blo 1965435 9955709 := bstep (se 3 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 9955709 = 3733391) B3733391
theorem B6637139 : Blo 1965435 6637139 := bstep (se 1 (by rfl) ⟨4977854, by rfl⟩ : syracuseStep 6637139 = 9955709) B9955709
theorem B4424759 : Blo 1965435 4424759 := bstep (se 1 (by rfl) ⟨3318569, by rfl⟩ : syracuseStep 4424759 = 6637139) B6637139
theorem B2949839 : Blo 1965435 2949839 := bstep (se 1 (by rfl) ⟨2212379, by rfl⟩ : syracuseStep 2949839 = 4424759) B4424759
theorem B1966559 : Blo 1965435 1966559 := bstep (se 1 (by rfl) ⟨1474919, by rfl⟩ : syracuseStep 1966559 = 2949839) B2949839
theorem B2949845 : Blo 1965435 2949845 := bbase (se 7 (by rfl) ⟨34568, by rfl⟩ : syracuseStep 2949845 = 69137) (by norm_num)
theorem B1966563 : Blo 1965435 1966563 := bstep (se 1 (by rfl) ⟨1474922, by rfl⟩ : syracuseStep 1966563 = 2949845) B2949845
theorem B3543821 : Blo 1965435 3543821 := bbase (se 3 (by rfl) ⟨664466, by rfl⟩ : syracuseStep 3543821 = 1328933) (by norm_num)
theorem B2362547 : Blo 1965435 2362547 := bstep (se 1 (by rfl) ⟨1771910, by rfl⟩ : syracuseStep 2362547 = 3543821) B3543821
theorem B6300125 : Blo 1965435 6300125 := bstep (se 3 (by rfl) ⟨1181273, by rfl⟩ : syracuseStep 6300125 = 2362547) B2362547
theorem B4200083 : Blo 1965435 4200083 := bstep (se 1 (by rfl) ⟨3150062, by rfl⟩ : syracuseStep 4200083 = 6300125) B6300125
theorem B2800055 : Blo 1965435 2800055 := bstep (se 1 (by rfl) ⟨2100041, by rfl⟩ : syracuseStep 2800055 = 4200083) B4200083
theorem B7466813 : Blo 1965435 7466813 := bstep (se 3 (by rfl) ⟨1400027, by rfl⟩ : syracuseStep 7466813 = 2800055) B2800055
theorem B4977875 : Blo 1965435 4977875 := bstep (se 1 (by rfl) ⟨3733406, by rfl⟩ : syracuseStep 4977875 = 7466813) B7466813
theorem B3318583 : Blo 1965435 3318583 := bstep (se 1 (by rfl) ⟨2488937, by rfl⟩ : syracuseStep 3318583 = 4977875) B4977875
theorem B4424777 : Blo 1965435 4424777 := bstep (se 2 (by rfl) ⟨1659291, by rfl⟩ : syracuseStep 4424777 = 3318583) B3318583
theorem B2949851 : Blo 1965435 2949851 := bstep (se 1 (by rfl) ⟨2212388, by rfl⟩ : syracuseStep 2949851 = 4424777) B4424777
theorem B1966567 : Blo 1965435 1966567 := bstep (se 1 (by rfl) ⟨1474925, by rfl⟩ : syracuseStep 1966567 = 2949851) B2949851
theorem B2212393 : Blo 1965435 2212393 := bbase (se 2 (by rfl) ⟨829647, by rfl⟩ : syracuseStep 2212393 = 1659295) (by norm_num)
theorem B2949857 : Blo 1965435 2949857 := bstep (se 2 (by rfl) ⟨1106196, by rfl⟩ : syracuseStep 2949857 = 2212393) B2212393
theorem B1966571 : Blo 1965435 1966571 := bstep (se 1 (by rfl) ⟨1474928, by rfl⟩ : syracuseStep 1966571 = 2949857) B2949857
theorem B4608389 : Blo 1965435 4608389 := bbase (se 4 (by rfl) ⟨432036, by rfl⟩ : syracuseStep 4608389 = 864073) (by norm_num)
theorem B3072259 : Blo 1965435 3072259 := bstep (se 1 (by rfl) ⟨2304194, by rfl⟩ : syracuseStep 3072259 = 4608389) B4608389
theorem B4096345 : Blo 1965435 4096345 := bstep (se 2 (by rfl) ⟨1536129, by rfl⟩ : syracuseStep 4096345 = 3072259) B3072259
theorem B5461793 : Blo 1965435 5461793 := bstep (se 2 (by rfl) ⟨2048172, by rfl⟩ : syracuseStep 5461793 = 4096345) B4096345
theorem B3641195 : Blo 1965435 3641195 := bstep (se 1 (by rfl) ⟨2730896, by rfl⟩ : syracuseStep 3641195 = 5461793) B5461793
theorem B2427463 : Blo 1965435 2427463 := bstep (se 1 (by rfl) ⟨1820597, by rfl⟩ : syracuseStep 2427463 = 3641195) B3641195
theorem B3236617 : Blo 1965435 3236617 := bstep (se 2 (by rfl) ⟨1213731, by rfl⟩ : syracuseStep 3236617 = 2427463) B2427463
theorem B4315489 : Blo 1965435 4315489 := bstep (se 2 (by rfl) ⟨1618308, by rfl⟩ : syracuseStep 4315489 = 3236617) B3236617
theorem B92063765 : Blo 1965435 92063765 := bstep (se 6 (by rfl) ⟨2157744, by rfl⟩ : syracuseStep 92063765 = 4315489) B4315489
theorem B61375843 : Blo 1965435 61375843 := bstep (se 1 (by rfl) ⟨46031882, by rfl⟩ : syracuseStep 61375843 = 92063765) B92063765
theorem B81834457 : Blo 1965435 81834457 := bstep (se 2 (by rfl) ⟨30687921, by rfl⟩ : syracuseStep 81834457 = 61375843) B61375843
theorem B109112609 : Blo 1965435 109112609 := bstep (se 2 (by rfl) ⟨40917228, by rfl⟩ : syracuseStep 109112609 = 81834457) B81834457
theorem B72741739 : Blo 1965435 72741739 := bstep (se 1 (by rfl) ⟨54556304, by rfl⟩ : syracuseStep 72741739 = 109112609) B109112609
theorem B96988985 : Blo 1965435 96988985 := bstep (se 2 (by rfl) ⟨36370869, by rfl⟩ : syracuseStep 96988985 = 72741739) B72741739
theorem B64659323 : Blo 1965435 64659323 := bstep (se 1 (by rfl) ⟨48494492, by rfl⟩ : syracuseStep 64659323 = 96988985) B96988985
theorem B43106215 : Blo 1965435 43106215 := bstep (se 1 (by rfl) ⟨32329661, by rfl⟩ : syracuseStep 43106215 = 64659323) B64659323
theorem B57474953 : Blo 1965435 57474953 := bstep (se 2 (by rfl) ⟨21553107, by rfl⟩ : syracuseStep 57474953 = 43106215) B43106215
theorem B38316635 : Blo 1965435 38316635 := bstep (se 1 (by rfl) ⟨28737476, by rfl⟩ : syracuseStep 38316635 = 57474953) B57474953
theorem B25544423 : Blo 1965435 25544423 := bstep (se 1 (by rfl) ⟨19158317, by rfl⟩ : syracuseStep 25544423 = 38316635) B38316635
theorem B17029615 : Blo 1965435 17029615 := bstep (se 1 (by rfl) ⟨12772211, by rfl⟩ : syracuseStep 17029615 = 25544423) B25544423
theorem B22706153 : Blo 1965435 22706153 := bstep (se 2 (by rfl) ⟨8514807, by rfl⟩ : syracuseStep 22706153 = 17029615) B17029615
theorem B15137435 : Blo 1965435 15137435 := bstep (se 1 (by rfl) ⟨11353076, by rfl⟩ : syracuseStep 15137435 = 22706153) B22706153
theorem B10091623 : Blo 1965435 10091623 := bstep (se 1 (by rfl) ⟨7568717, by rfl⟩ : syracuseStep 10091623 = 15137435) B15137435
theorem B13455497 : Blo 1965435 13455497 := bstep (se 2 (by rfl) ⟨5045811, by rfl⟩ : syracuseStep 13455497 = 10091623) B10091623
theorem B35881325 : Blo 1965435 35881325 := bstep (se 3 (by rfl) ⟨6727748, by rfl⟩ : syracuseStep 35881325 = 13455497) B13455497
theorem B23920883 : Blo 1965435 23920883 := bstep (se 1 (by rfl) ⟨17940662, by rfl⟩ : syracuseStep 23920883 = 35881325) B35881325
theorem B15947255 : Blo 1965435 15947255 := bstep (se 1 (by rfl) ⟨11960441, by rfl⟩ : syracuseStep 15947255 = 23920883) B23920883
theorem B10631503 : Blo 1965435 10631503 := bstep (se 1 (by rfl) ⟨7973627, by rfl⟩ : syracuseStep 10631503 = 15947255) B15947255
theorem B14175337 : Blo 1965435 14175337 := bstep (se 2 (by rfl) ⟨5315751, by rfl⟩ : syracuseStep 14175337 = 10631503) B10631503
theorem B18900449 : Blo 1965435 18900449 := bstep (se 2 (by rfl) ⟨7087668, by rfl⟩ : syracuseStep 18900449 = 14175337) B14175337
theorem B12600299 : Blo 1965435 12600299 := bstep (se 1 (by rfl) ⟨9450224, by rfl⟩ : syracuseStep 12600299 = 18900449) B18900449
theorem B8400199 : Blo 1965435 8400199 := bstep (se 1 (by rfl) ⟨6300149, by rfl⟩ : syracuseStep 8400199 = 12600299) B12600299
theorem B11200265 : Blo 1965435 11200265 := bstep (se 2 (by rfl) ⟨4200099, by rfl⟩ : syracuseStep 11200265 = 8400199) B8400199
theorem B7466843 : Blo 1965435 7466843 := bstep (se 1 (by rfl) ⟨5600132, by rfl⟩ : syracuseStep 7466843 = 11200265) B11200265
theorem B4977895 : Blo 1965435 4977895 := bstep (se 1 (by rfl) ⟨3733421, by rfl⟩ : syracuseStep 4977895 = 7466843) B7466843
theorem B6637193 : Blo 1965435 6637193 := bstep (se 2 (by rfl) ⟨2488947, by rfl⟩ : syracuseStep 6637193 = 4977895) B4977895
theorem B4424795 : Blo 1965435 4424795 := bstep (se 1 (by rfl) ⟨3318596, by rfl⟩ : syracuseStep 4424795 = 6637193) B6637193
theorem B2949863 : Blo 1965435 2949863 := bstep (se 1 (by rfl) ⟨2212397, by rfl⟩ : syracuseStep 2949863 = 4424795) B4424795
theorem B1966575 : Blo 1965435 1966575 := bstep (se 1 (by rfl) ⟨1474931, by rfl⟩ : syracuseStep 1966575 = 2949863) B2949863
theorem B2949869 : Blo 1965435 2949869 := bbase (se 3 (by rfl) ⟨553100, by rfl⟩ : syracuseStep 2949869 = 1106201) (by norm_num)
theorem B1966579 : Blo 1965435 1966579 := bstep (se 1 (by rfl) ⟨1474934, by rfl⟩ : syracuseStep 1966579 = 2949869) B2949869
theorem B4424813 : Blo 1965435 4424813 := bbase (se 3 (by rfl) ⟨829652, by rfl⟩ : syracuseStep 4424813 = 1659305) (by norm_num)
theorem B2949875 : Blo 1965435 2949875 := bstep (se 1 (by rfl) ⟨2212406, by rfl⟩ : syracuseStep 2949875 = 4424813) B4424813
theorem B1966583 : Blo 1965435 1966583 := bstep (se 1 (by rfl) ⟨1474937, by rfl⟩ : syracuseStep 1966583 = 2949875) B2949875
theorem B3733445 : Blo 1965435 3733445 := bbase (se 4 (by rfl) ⟨350010, by rfl⟩ : syracuseStep 3733445 = 700021) (by norm_num)
theorem B2488963 : Blo 1965435 2488963 := bstep (se 1 (by rfl) ⟨1866722, by rfl⟩ : syracuseStep 2488963 = 3733445) B3733445
theorem B3318617 : Blo 1965435 3318617 := bstep (se 2 (by rfl) ⟨1244481, by rfl⟩ : syracuseStep 3318617 = 2488963) B2488963
theorem B2212411 : Blo 1965435 2212411 := bstep (se 1 (by rfl) ⟨1659308, by rfl⟩ : syracuseStep 2212411 = 3318617) B3318617
theorem B2949881 : Blo 1965435 2949881 := bstep (se 2 (by rfl) ⟨1106205, by rfl⟩ : syracuseStep 2949881 = 2212411) B2212411
theorem B1966587 : Blo 1965435 1966587 := bstep (se 1 (by rfl) ⟨1474940, by rfl⟩ : syracuseStep 1966587 = 2949881) B2949881
theorem B4789621 : Blo 1965435 4789621 := bbase (se 5 (by rfl) ⟨224513, by rfl⟩ : syracuseStep 4789621 = 449027) (by norm_num)
theorem B6386161 : Blo 1965435 6386161 := bstep (se 2 (by rfl) ⟨2394810, by rfl⟩ : syracuseStep 6386161 = 4789621) B4789621
theorem B8514881 : Blo 1965435 8514881 := bstep (se 2 (by rfl) ⟨3193080, by rfl⟩ : syracuseStep 8514881 = 6386161) B6386161
theorem B5676587 : Blo 1965435 5676587 := bstep (se 1 (by rfl) ⟨4257440, by rfl⟩ : syracuseStep 5676587 = 8514881) B8514881
theorem B3784391 : Blo 1965435 3784391 := bstep (se 1 (by rfl) ⟨2838293, by rfl⟩ : syracuseStep 3784391 = 5676587) B5676587
theorem B2522927 : Blo 1965435 2522927 := bstep (se 1 (by rfl) ⟨1892195, by rfl⟩ : syracuseStep 2522927 = 3784391) B3784391
theorem B6727805 : Blo 1965435 6727805 := bstep (se 3 (by rfl) ⟨1261463, by rfl⟩ : syracuseStep 6727805 = 2522927) B2522927
theorem B4485203 : Blo 1965435 4485203 := bstep (se 1 (by rfl) ⟨3363902, by rfl⟩ : syracuseStep 4485203 = 6727805) B6727805
theorem B2990135 : Blo 1965435 2990135 := bstep (se 1 (by rfl) ⟨2242601, by rfl⟩ : syracuseStep 2990135 = 4485203) B4485203
theorem B1993423 : Blo 1965435 1993423 := bstep (se 1 (by rfl) ⟨1495067, by rfl⟩ : syracuseStep 1993423 = 2990135) B2990135
theorem B2657897 : Blo 1965435 2657897 := bstep (se 2 (by rfl) ⟨996711, by rfl⟩ : syracuseStep 2657897 = 1993423) B1993423
theorem B28350901 : Blo 1965435 28350901 := bstep (se 5 (by rfl) ⟨1328948, by rfl⟩ : syracuseStep 28350901 = 2657897) B2657897
theorem B37801201 : Blo 1965435 37801201 := bstep (se 2 (by rfl) ⟨14175450, by rfl⟩ : syracuseStep 37801201 = 28350901) B28350901
theorem B50401601 : Blo 1965435 50401601 := bstep (se 2 (by rfl) ⟨18900600, by rfl⟩ : syracuseStep 50401601 = 37801201) B37801201
theorem B33601067 : Blo 1965435 33601067 := bstep (se 1 (by rfl) ⟨25200800, by rfl⟩ : syracuseStep 33601067 = 50401601) B50401601
theorem B22400711 : Blo 1965435 22400711 := bstep (se 1 (by rfl) ⟨16800533, by rfl⟩ : syracuseStep 22400711 = 33601067) B33601067
theorem B14933807 : Blo 1965435 14933807 := bstep (se 1 (by rfl) ⟨11200355, by rfl⟩ : syracuseStep 14933807 = 22400711) B22400711
theorem B9955871 : Blo 1965435 9955871 := bstep (se 1 (by rfl) ⟨7466903, by rfl⟩ : syracuseStep 9955871 = 14933807) B14933807
theorem B6637247 : Blo 1965435 6637247 := bstep (se 1 (by rfl) ⟨4977935, by rfl⟩ : syracuseStep 6637247 = 9955871) B9955871
theorem B4424831 : Blo 1965435 4424831 := bstep (se 1 (by rfl) ⟨3318623, by rfl⟩ : syracuseStep 4424831 = 6637247) B6637247
theorem B2949887 : Blo 1965435 2949887 := bstep (se 1 (by rfl) ⟨2212415, by rfl⟩ : syracuseStep 2949887 = 4424831) B4424831
theorem B1966591 : Blo 1965435 1966591 := bstep (se 1 (by rfl) ⟨1474943, by rfl⟩ : syracuseStep 1966591 = 2949887) B2949887
theorem B2949893 : Blo 1965435 2949893 := bbase (se 4 (by rfl) ⟨276552, by rfl⟩ : syracuseStep 2949893 = 553105) (by norm_num)
theorem B1966595 : Blo 1965435 1966595 := bstep (se 1 (by rfl) ⟨1474946, by rfl⟩ : syracuseStep 1966595 = 2949893) B2949893
theorem B3318637 : Blo 1965435 3318637 := bbase (se 3 (by rfl) ⟨622244, by rfl⟩ : syracuseStep 3318637 = 1244489) (by norm_num)
theorem B4424849 : Blo 1965435 4424849 := bstep (se 2 (by rfl) ⟨1659318, by rfl⟩ : syracuseStep 4424849 = 3318637) B3318637
theorem B2949899 : Blo 1965435 2949899 := bstep (se 1 (by rfl) ⟨2212424, by rfl⟩ : syracuseStep 2949899 = 4424849) B4424849
theorem B1966599 : Blo 1965435 1966599 := bstep (se 1 (by rfl) ⟨1474949, by rfl⟩ : syracuseStep 1966599 = 2949899) B2949899
theorem B2212429 : Blo 1965435 2212429 := bbase (se 3 (by rfl) ⟨414830, by rfl⟩ : syracuseStep 2212429 = 829661) (by norm_num)
theorem B2949905 : Blo 1965435 2949905 := bstep (se 2 (by rfl) ⟨1106214, by rfl⟩ : syracuseStep 2949905 = 2212429) B2212429
theorem B1966603 : Blo 1965435 1966603 := bstep (se 1 (by rfl) ⟨1474952, by rfl⟩ : syracuseStep 1966603 = 2949905) B2949905
theorem B6637301 : Blo 1965435 6637301 := bbase (se 5 (by rfl) ⟨311123, by rfl⟩ : syracuseStep 6637301 = 622247) (by norm_num)
theorem B4424867 : Blo 1965435 4424867 := bstep (se 1 (by rfl) ⟨3318650, by rfl⟩ : syracuseStep 4424867 = 6637301) B6637301
theorem B2949911 : Blo 1965435 2949911 := bstep (se 1 (by rfl) ⟨2212433, by rfl⟩ : syracuseStep 2949911 = 4424867) B4424867
theorem B1966607 : Blo 1965435 1966607 := bstep (se 1 (by rfl) ⟨1474955, by rfl⟩ : syracuseStep 1966607 = 2949911) B2949911
theorem B2949917 : Blo 1965435 2949917 := bbase (se 3 (by rfl) ⟨553109, by rfl⟩ : syracuseStep 2949917 = 1106219) (by norm_num)
theorem B1966611 : Blo 1965435 1966611 := bstep (se 1 (by rfl) ⟨1474958, by rfl⟩ : syracuseStep 1966611 = 2949917) B2949917
theorem B4424885 : Blo 1965435 4424885 := bbase (se 5 (by rfl) ⟨207416, by rfl⟩ : syracuseStep 4424885 = 414833) (by norm_num)
theorem B2949923 : Blo 1965435 2949923 := bstep (se 1 (by rfl) ⟨2212442, by rfl⟩ : syracuseStep 2949923 = 4424885) B4424885
theorem B1966615 : Blo 1965435 1966615 := bstep (se 1 (by rfl) ⟨1474961, by rfl⟩ : syracuseStep 1966615 = 2949923) B2949923
theorem B2100097 : Blo 1965435 2100097 := bbase (se 2 (by rfl) ⟨787536, by rfl⟩ : syracuseStep 2100097 = 1575073) (by norm_num)
theorem B11200517 : Blo 1965435 11200517 := bstep (se 4 (by rfl) ⟨1050048, by rfl⟩ : syracuseStep 11200517 = 2100097) B2100097
theorem B7467011 : Blo 1965435 7467011 := bstep (se 1 (by rfl) ⟨5600258, by rfl⟩ : syracuseStep 7467011 = 11200517) B11200517
theorem B4978007 : Blo 1965435 4978007 := bstep (se 1 (by rfl) ⟨3733505, by rfl⟩ : syracuseStep 4978007 = 7467011) B7467011
theorem B3318671 : Blo 1965435 3318671 := bstep (se 1 (by rfl) ⟨2489003, by rfl⟩ : syracuseStep 3318671 = 4978007) B4978007
theorem B2212447 : Blo 1965435 2212447 := bstep (se 1 (by rfl) ⟨1659335, by rfl⟩ : syracuseStep 2212447 = 3318671) B3318671
theorem B2949929 : Blo 1965435 2949929 := bstep (se 2 (by rfl) ⟨1106223, by rfl⟩ : syracuseStep 2949929 = 2212447) B2212447
theorem B1966619 : Blo 1965435 1966619 := bstep (se 1 (by rfl) ⟨1474964, by rfl⟩ : syracuseStep 1966619 = 2949929) B2949929
theorem B2100101 : Blo 1965435 2100101 := bbase (se 4 (by rfl) ⟨196884, by rfl⟩ : syracuseStep 2100101 = 393769) (by norm_num)
theorem B5600269 : Blo 1965435 5600269 := bstep (se 3 (by rfl) ⟨1050050, by rfl⟩ : syracuseStep 5600269 = 2100101) B2100101
theorem B7467025 : Blo 1965435 7467025 := bstep (se 2 (by rfl) ⟨2800134, by rfl⟩ : syracuseStep 7467025 = 5600269) B5600269
theorem B9956033 : Blo 1965435 9956033 := bstep (se 2 (by rfl) ⟨3733512, by rfl⟩ : syracuseStep 9956033 = 7467025) B7467025
theorem B6637355 : Blo 1965435 6637355 := bstep (se 1 (by rfl) ⟨4978016, by rfl⟩ : syracuseStep 6637355 = 9956033) B9956033
theorem B4424903 : Blo 1965435 4424903 := bstep (se 1 (by rfl) ⟨3318677, by rfl⟩ : syracuseStep 4424903 = 6637355) B6637355
theorem B2949935 : Blo 1965435 2949935 := bstep (se 1 (by rfl) ⟨2212451, by rfl⟩ : syracuseStep 2949935 = 4424903) B4424903
theorem B1966623 : Blo 1965435 1966623 := bstep (se 1 (by rfl) ⟨1474967, by rfl⟩ : syracuseStep 1966623 = 2949935) B2949935
theorem B2949941 : Blo 1965435 2949941 := bbase (se 5 (by rfl) ⟨138278, by rfl⟩ : syracuseStep 2949941 = 276557) (by norm_num)
theorem B1966627 : Blo 1965435 1966627 := bstep (se 1 (by rfl) ⟨1474970, by rfl⟩ : syracuseStep 1966627 = 2949941) B2949941
theorem B4978037 : Blo 1965435 4978037 := bbase (se 5 (by rfl) ⟨233345, by rfl⟩ : syracuseStep 4978037 = 466691) (by norm_num)
theorem B3318691 : Blo 1965435 3318691 := bstep (se 1 (by rfl) ⟨2489018, by rfl⟩ : syracuseStep 3318691 = 4978037) B4978037
theorem B4424921 : Blo 1965435 4424921 := bstep (se 2 (by rfl) ⟨1659345, by rfl⟩ : syracuseStep 4424921 = 3318691) B3318691
theorem B2949947 : Blo 1965435 2949947 := bstep (se 1 (by rfl) ⟨2212460, by rfl⟩ : syracuseStep 2949947 = 4424921) B4424921
theorem B1966631 : Blo 1965435 1966631 := bstep (se 1 (by rfl) ⟨1474973, by rfl⟩ : syracuseStep 1966631 = 2949947) B2949947
theorem B2212465 : Blo 1965435 2212465 := bbase (se 2 (by rfl) ⟨829674, by rfl⟩ : syracuseStep 2212465 = 1659349) (by norm_num)
theorem B2949953 : Blo 1965435 2949953 := bstep (se 2 (by rfl) ⟨1106232, by rfl⟩ : syracuseStep 2949953 = 2212465) B2212465
theorem B1966635 : Blo 1965435 1966635 := bstep (se 1 (by rfl) ⟨1474976, by rfl⟩ : syracuseStep 1966635 = 2949953) B2949953
theorem B9450533 : Blo 1965435 9450533 := bbase (se 4 (by rfl) ⟨885987, by rfl⟩ : syracuseStep 9450533 = 1771975) (by norm_num)
theorem B6300355 : Blo 1965435 6300355 := bstep (se 1 (by rfl) ⟨4725266, by rfl⟩ : syracuseStep 6300355 = 9450533) B9450533
theorem B8400473 : Blo 1965435 8400473 := bstep (se 2 (by rfl) ⟨3150177, by rfl⟩ : syracuseStep 8400473 = 6300355) B6300355
theorem B5600315 : Blo 1965435 5600315 := bstep (se 1 (by rfl) ⟨4200236, by rfl⟩ : syracuseStep 5600315 = 8400473) B8400473
theorem B3733543 : Blo 1965435 3733543 := bstep (se 1 (by rfl) ⟨2800157, by rfl⟩ : syracuseStep 3733543 = 5600315) B5600315
theorem B4978057 : Blo 1965435 4978057 := bstep (se 2 (by rfl) ⟨1866771, by rfl⟩ : syracuseStep 4978057 = 3733543) B3733543
theorem B6637409 : Blo 1965435 6637409 := bstep (se 2 (by rfl) ⟨2489028, by rfl⟩ : syracuseStep 6637409 = 4978057) B4978057
theorem B4424939 : Blo 1965435 4424939 := bstep (se 1 (by rfl) ⟨3318704, by rfl⟩ : syracuseStep 4424939 = 6637409) B6637409
theorem B2949959 : Blo 1965435 2949959 := bstep (se 1 (by rfl) ⟨2212469, by rfl⟩ : syracuseStep 2949959 = 4424939) B4424939
theorem B1966639 : Blo 1965435 1966639 := bstep (se 1 (by rfl) ⟨1474979, by rfl⟩ : syracuseStep 1966639 = 2949959) B2949959
theorem B2949965 : Blo 1965435 2949965 := bbase (se 3 (by rfl) ⟨553118, by rfl⟩ : syracuseStep 2949965 = 1106237) (by norm_num)
theorem B1966643 : Blo 1965435 1966643 := bstep (se 1 (by rfl) ⟨1474982, by rfl⟩ : syracuseStep 1966643 = 2949965) B2949965
theorem B4424957 : Blo 1965435 4424957 := bbase (se 3 (by rfl) ⟨829679, by rfl⟩ : syracuseStep 4424957 = 1659359) (by norm_num)
theorem B2949971 : Blo 1965435 2949971 := bstep (se 1 (by rfl) ⟨2212478, by rfl⟩ : syracuseStep 2949971 = 4424957) B4424957
theorem B1966647 : Blo 1965435 1966647 := bstep (se 1 (by rfl) ⟨1474985, by rfl⟩ : syracuseStep 1966647 = 2949971) B2949971
theorem B3318725 : Blo 1965435 3318725 := bbase (se 4 (by rfl) ⟨311130, by rfl⟩ : syracuseStep 3318725 = 622261) (by norm_num)
theorem B2212483 : Blo 1965435 2212483 := bstep (se 1 (by rfl) ⟨1659362, by rfl⟩ : syracuseStep 2212483 = 3318725) B3318725
theorem B2949977 : Blo 1965435 2949977 := bstep (se 2 (by rfl) ⟨1106241, by rfl⟩ : syracuseStep 2949977 = 2212483) B2212483
theorem B1966651 : Blo 1965435 1966651 := bstep (se 1 (by rfl) ⟨1474988, by rfl⟩ : syracuseStep 1966651 = 2949977) B2949977
theorem B14934293 : Blo 1965435 14934293 := bbase (se 6 (by rfl) ⟨350022, by rfl⟩ : syracuseStep 14934293 = 700045) (by norm_num)
theorem B9956195 : Blo 1965435 9956195 := bstep (se 1 (by rfl) ⟨7467146, by rfl⟩ : syracuseStep 9956195 = 14934293) B14934293
theorem B6637463 : Blo 1965435 6637463 := bstep (se 1 (by rfl) ⟨4978097, by rfl⟩ : syracuseStep 6637463 = 9956195) B9956195
theorem B4424975 : Blo 1965435 4424975 := bstep (se 1 (by rfl) ⟨3318731, by rfl⟩ : syracuseStep 4424975 = 6637463) B6637463
theorem B2949983 : Blo 1965435 2949983 := bstep (se 1 (by rfl) ⟨2212487, by rfl⟩ : syracuseStep 2949983 = 4424975) B4424975
theorem B1966655 : Blo 1965435 1966655 := bstep (se 1 (by rfl) ⟨1474991, by rfl⟩ : syracuseStep 1966655 = 2949983) B2949983
theorem B2949989 : Blo 1965435 2949989 := bbase (se 4 (by rfl) ⟨276561, by rfl⟩ : syracuseStep 2949989 = 553123) (by norm_num)
theorem B1966659 : Blo 1965435 1966659 := bstep (se 1 (by rfl) ⟨1474994, by rfl⟩ : syracuseStep 1966659 = 2949989) B2949989
theorem B3733589 : Blo 1965435 3733589 := bbase (se 8 (by rfl) ⟨21876, by rfl⟩ : syracuseStep 3733589 = 43753) (by norm_num)
theorem B2489059 : Blo 1965435 2489059 := bstep (se 1 (by rfl) ⟨1866794, by rfl⟩ : syracuseStep 2489059 = 3733589) B3733589
theorem B3318745 : Blo 1965435 3318745 := bstep (se 2 (by rfl) ⟨1244529, by rfl⟩ : syracuseStep 3318745 = 2489059) B2489059
theorem B4424993 : Blo 1965435 4424993 := bstep (se 2 (by rfl) ⟨1659372, by rfl⟩ : syracuseStep 4424993 = 3318745) B3318745
theorem B2949995 : Blo 1965435 2949995 := bstep (se 1 (by rfl) ⟨2212496, by rfl⟩ : syracuseStep 2949995 = 4424993) B4424993
theorem B1966663 : Blo 1965435 1966663 := bstep (se 1 (by rfl) ⟨1474997, by rfl⟩ : syracuseStep 1966663 = 2949995) B2949995
theorem B2212501 : Blo 1965435 2212501 := bbase (se 6 (by rfl) ⟨51855, by rfl⟩ : syracuseStep 2212501 = 103711) (by norm_num)
theorem B2950001 : Blo 1965435 2950001 := bstep (se 2 (by rfl) ⟨1106250, by rfl⟩ : syracuseStep 2950001 = 2212501) B2212501
theorem B1966667 : Blo 1965435 1966667 := bstep (se 1 (by rfl) ⟨1475000, by rfl⟩ : syracuseStep 1966667 = 2950001) B2950001
theorem B2489069 : Blo 1965435 2489069 := bbase (se 3 (by rfl) ⟨466700, by rfl⟩ : syracuseStep 2489069 = 933401) (by norm_num)
theorem B6637517 : Blo 1965435 6637517 := bstep (se 3 (by rfl) ⟨1244534, by rfl⟩ : syracuseStep 6637517 = 2489069) B2489069
theorem B4425011 : Blo 1965435 4425011 := bstep (se 1 (by rfl) ⟨3318758, by rfl⟩ : syracuseStep 4425011 = 6637517) B6637517
theorem B2950007 : Blo 1965435 2950007 := bstep (se 1 (by rfl) ⟨2212505, by rfl⟩ : syracuseStep 2950007 = 4425011) B4425011
theorem B1966671 : Blo 1965435 1966671 := bstep (se 1 (by rfl) ⟨1475003, by rfl⟩ : syracuseStep 1966671 = 2950007) B2950007
theorem B2950013 : Blo 1965435 2950013 := bbase (se 3 (by rfl) ⟨553127, by rfl⟩ : syracuseStep 2950013 = 1106255) (by norm_num)
theorem B1966675 : Blo 1965435 1966675 := bstep (se 1 (by rfl) ⟨1475006, by rfl⟩ : syracuseStep 1966675 = 2950013) B2950013
theorem B4425029 : Blo 1965435 4425029 := bbase (se 4 (by rfl) ⟨414846, by rfl⟩ : syracuseStep 4425029 = 829693) (by norm_num)
theorem B2950019 : Blo 1965435 2950019 := bstep (se 1 (by rfl) ⟨2212514, by rfl⟩ : syracuseStep 2950019 = 4425029) B4425029
theorem B1966679 : Blo 1965435 1966679 := bstep (se 1 (by rfl) ⟨1475009, by rfl⟩ : syracuseStep 1966679 = 2950019) B2950019
theorem B4725373 : Blo 1965435 4725373 := bbase (se 3 (by rfl) ⟨886007, by rfl⟩ : syracuseStep 4725373 = 1772015) (by norm_num)
theorem B6300497 : Blo 1965435 6300497 := bstep (se 2 (by rfl) ⟨2362686, by rfl⟩ : syracuseStep 6300497 = 4725373) B4725373
theorem B4200331 : Blo 1965435 4200331 := bstep (se 1 (by rfl) ⟨3150248, by rfl⟩ : syracuseStep 4200331 = 6300497) B6300497
theorem B5600441 : Blo 1965435 5600441 := bstep (se 2 (by rfl) ⟨2100165, by rfl⟩ : syracuseStep 5600441 = 4200331) B4200331
theorem B3733627 : Blo 1965435 3733627 := bstep (se 1 (by rfl) ⟨2800220, by rfl⟩ : syracuseStep 3733627 = 5600441) B5600441
theorem B4978169 : Blo 1965435 4978169 := bstep (se 2 (by rfl) ⟨1866813, by rfl⟩ : syracuseStep 4978169 = 3733627) B3733627
theorem B3318779 : Blo 1965435 3318779 := bstep (se 1 (by rfl) ⟨2489084, by rfl⟩ : syracuseStep 3318779 = 4978169) B4978169
theorem B2212519 : Blo 1965435 2212519 := bstep (se 1 (by rfl) ⟨1659389, by rfl⟩ : syracuseStep 2212519 = 3318779) B3318779
theorem B2950025 : Blo 1965435 2950025 := bstep (se 2 (by rfl) ⟨1106259, by rfl⟩ : syracuseStep 2950025 = 2212519) B2212519
theorem B1966683 : Blo 1965435 1966683 := bstep (se 1 (by rfl) ⟨1475012, by rfl⟩ : syracuseStep 1966683 = 2950025) B2950025
theorem B9956357 : Blo 1965435 9956357 := bbase (se 4 (by rfl) ⟨933408, by rfl⟩ : syracuseStep 9956357 = 1866817) (by norm_num)
theorem B6637571 : Blo 1965435 6637571 := bstep (se 1 (by rfl) ⟨4978178, by rfl⟩ : syracuseStep 6637571 = 9956357) B9956357
theorem B4425047 : Blo 1965435 4425047 := bstep (se 1 (by rfl) ⟨3318785, by rfl⟩ : syracuseStep 4425047 = 6637571) B6637571
theorem B2950031 : Blo 1965435 2950031 := bstep (se 1 (by rfl) ⟨2212523, by rfl⟩ : syracuseStep 2950031 = 4425047) B4425047
theorem B1966687 : Blo 1965435 1966687 := bstep (se 1 (by rfl) ⟨1475015, by rfl⟩ : syracuseStep 1966687 = 2950031) B2950031
theorem B2950037 : Blo 1965435 2950037 := bbase (se 6 (by rfl) ⟨69141, by rfl⟩ : syracuseStep 2950037 = 138283) (by norm_num)
theorem B1966691 : Blo 1965435 1966691 := bstep (se 1 (by rfl) ⟨1475018, by rfl⟩ : syracuseStep 1966691 = 2950037) B2950037
theorem B11200949 : Blo 1965435 11200949 := bbase (se 5 (by rfl) ⟨525044, by rfl⟩ : syracuseStep 11200949 = 1050089) (by norm_num)
theorem B7467299 : Blo 1965435 7467299 := bstep (se 1 (by rfl) ⟨5600474, by rfl⟩ : syracuseStep 7467299 = 11200949) B11200949
theorem B4978199 : Blo 1965435 4978199 := bstep (se 1 (by rfl) ⟨3733649, by rfl⟩ : syracuseStep 4978199 = 7467299) B7467299
theorem B3318799 : Blo 1965435 3318799 := bstep (se 1 (by rfl) ⟨2489099, by rfl⟩ : syracuseStep 3318799 = 4978199) B4978199
theorem B4425065 : Blo 1965435 4425065 := bstep (se 2 (by rfl) ⟨1659399, by rfl⟩ : syracuseStep 4425065 = 3318799) B3318799
theorem B2950043 : Blo 1965435 2950043 := bstep (se 1 (by rfl) ⟨2212532, by rfl⟩ : syracuseStep 2950043 = 4425065) B4425065
theorem B1966695 : Blo 1965435 1966695 := bstep (se 1 (by rfl) ⟨1475021, by rfl⟩ : syracuseStep 1966695 = 2950043) B2950043
theorem B2212537 : Blo 1965435 2212537 := bbase (se 2 (by rfl) ⟨829701, by rfl⟩ : syracuseStep 2212537 = 1659403) (by norm_num)
theorem B2950049 : Blo 1965435 2950049 := bstep (se 2 (by rfl) ⟨1106268, by rfl⟩ : syracuseStep 2950049 = 2212537) B2212537
theorem B1966699 : Blo 1965435 1966699 := bstep (se 1 (by rfl) ⟨1475024, by rfl⟩ : syracuseStep 1966699 = 2950049) B2950049
theorem B4200373 : Blo 1965435 4200373 := bbase (se 5 (by rfl) ⟨196892, by rfl⟩ : syracuseStep 4200373 = 393785) (by norm_num)
theorem B5600497 : Blo 1965435 5600497 := bstep (se 2 (by rfl) ⟨2100186, by rfl⟩ : syracuseStep 5600497 = 4200373) B4200373
theorem B7467329 : Blo 1965435 7467329 := bstep (se 2 (by rfl) ⟨2800248, by rfl⟩ : syracuseStep 7467329 = 5600497) B5600497
theorem B4978219 : Blo 1965435 4978219 := bstep (se 1 (by rfl) ⟨3733664, by rfl⟩ : syracuseStep 4978219 = 7467329) B7467329
theorem B6637625 : Blo 1965435 6637625 := bstep (se 2 (by rfl) ⟨2489109, by rfl⟩ : syracuseStep 6637625 = 4978219) B4978219
theorem B4425083 : Blo 1965435 4425083 := bstep (se 1 (by rfl) ⟨3318812, by rfl⟩ : syracuseStep 4425083 = 6637625) B6637625
theorem B2950055 : Blo 1965435 2950055 := bstep (se 1 (by rfl) ⟨2212541, by rfl⟩ : syracuseStep 2950055 = 4425083) B4425083
theorem B1966703 : Blo 1965435 1966703 := bstep (se 1 (by rfl) ⟨1475027, by rfl⟩ : syracuseStep 1966703 = 2950055) B2950055
theorem B2950061 : Blo 1965435 2950061 := bbase (se 3 (by rfl) ⟨553136, by rfl⟩ : syracuseStep 2950061 = 1106273) (by norm_num)
theorem B1966707 : Blo 1965435 1966707 := bstep (se 1 (by rfl) ⟨1475030, by rfl⟩ : syracuseStep 1966707 = 2950061) B2950061
theorem B4425101 : Blo 1965435 4425101 := bbase (se 3 (by rfl) ⟨829706, by rfl⟩ : syracuseStep 4425101 = 1659413) (by norm_num)
theorem B2950067 : Blo 1965435 2950067 := bstep (se 1 (by rfl) ⟨2212550, by rfl⟩ : syracuseStep 2950067 = 4425101) B4425101
theorem B1966711 : Blo 1965435 1966711 := bstep (se 1 (by rfl) ⟨1475033, by rfl⟩ : syracuseStep 1966711 = 2950067) B2950067
theorem B2489125 : Blo 1965435 2489125 := bbase (se 4 (by rfl) ⟨233355, by rfl⟩ : syracuseStep 2489125 = 466711) (by norm_num)
theorem B3318833 : Blo 1965435 3318833 := bstep (se 2 (by rfl) ⟨1244562, by rfl⟩ : syracuseStep 3318833 = 2489125) B2489125
theorem B2212555 : Blo 1965435 2212555 := bstep (se 1 (by rfl) ⟨1659416, by rfl⟩ : syracuseStep 2212555 = 3318833) B3318833
theorem B2950073 : Blo 1965435 2950073 := bstep (se 2 (by rfl) ⟨1106277, by rfl⟩ : syracuseStep 2950073 = 2212555) B2212555
theorem B1966715 : Blo 1965435 1966715 := bstep (se 1 (by rfl) ⟨1475036, by rfl⟩ : syracuseStep 1966715 = 2950073) B2950073
theorem B34061717 : Blo 1965435 34061717 := bbase (se 6 (by rfl) ⟨798321, by rfl⟩ : syracuseStep 34061717 = 1596643) (by norm_num)
theorem B22707811 : Blo 1965435 22707811 := bstep (se 1 (by rfl) ⟨17030858, by rfl⟩ : syracuseStep 22707811 = 34061717) B34061717
theorem B30277081 : Blo 1965435 30277081 := bstep (se 2 (by rfl) ⟨11353905, by rfl⟩ : syracuseStep 30277081 = 22707811) B22707811
theorem B40369441 : Blo 1965435 40369441 := bstep (se 2 (by rfl) ⟨15138540, by rfl⟩ : syracuseStep 40369441 = 30277081) B30277081
theorem B53825921 : Blo 1965435 53825921 := bstep (se 2 (by rfl) ⟨20184720, by rfl⟩ : syracuseStep 53825921 = 40369441) B40369441
theorem B35883947 : Blo 1965435 35883947 := bstep (se 1 (by rfl) ⟨26912960, by rfl⟩ : syracuseStep 35883947 = 53825921) B53825921
theorem B23922631 : Blo 1965435 23922631 := bstep (se 1 (by rfl) ⟨17941973, by rfl⟩ : syracuseStep 23922631 = 35883947) B35883947
theorem B31896841 : Blo 1965435 31896841 := bstep (se 2 (by rfl) ⟨11961315, by rfl⟩ : syracuseStep 31896841 = 23922631) B23922631
theorem B42529121 : Blo 1965435 42529121 := bstep (se 2 (by rfl) ⟨15948420, by rfl⟩ : syracuseStep 42529121 = 31896841) B31896841
theorem B28352747 : Blo 1965435 28352747 := bstep (se 1 (by rfl) ⟨21264560, by rfl⟩ : syracuseStep 28352747 = 42529121) B42529121
theorem B18901831 : Blo 1965435 18901831 := bstep (se 1 (by rfl) ⟨14176373, by rfl⟩ : syracuseStep 18901831 = 28352747) B28352747
theorem B25202441 : Blo 1965435 25202441 := bstep (se 2 (by rfl) ⟨9450915, by rfl⟩ : syracuseStep 25202441 = 18901831) B18901831
theorem B16801627 : Blo 1965435 16801627 := bstep (se 1 (by rfl) ⟨12601220, by rfl⟩ : syracuseStep 16801627 = 25202441) B25202441
theorem B22402169 : Blo 1965435 22402169 := bstep (se 2 (by rfl) ⟨8400813, by rfl⟩ : syracuseStep 22402169 = 16801627) B16801627
theorem B14934779 : Blo 1965435 14934779 := bstep (se 1 (by rfl) ⟨11201084, by rfl⟩ : syracuseStep 14934779 = 22402169) B22402169
theorem B9956519 : Blo 1965435 9956519 := bstep (se 1 (by rfl) ⟨7467389, by rfl⟩ : syracuseStep 9956519 = 14934779) B14934779
theorem B6637679 : Blo 1965435 6637679 := bstep (se 1 (by rfl) ⟨4978259, by rfl⟩ : syracuseStep 6637679 = 9956519) B9956519
theorem B4425119 : Blo 1965435 4425119 := bstep (se 1 (by rfl) ⟨3318839, by rfl⟩ : syracuseStep 4425119 = 6637679) B6637679
theorem B2950079 : Blo 1965435 2950079 := bstep (se 1 (by rfl) ⟨2212559, by rfl⟩ : syracuseStep 2950079 = 4425119) B4425119
theorem B1966719 : Blo 1965435 1966719 := bstep (se 1 (by rfl) ⟨1475039, by rfl⟩ : syracuseStep 1966719 = 2950079) B2950079
theorem B2950085 : Blo 1965435 2950085 := bbase (se 4 (by rfl) ⟨276570, by rfl⟩ : syracuseStep 2950085 = 553141) (by norm_num)
theorem B1966723 : Blo 1965435 1966723 := bstep (se 1 (by rfl) ⟨1475042, by rfl⟩ : syracuseStep 1966723 = 2950085) B2950085
theorem B3318853 : Blo 1965435 3318853 := bbase (se 4 (by rfl) ⟨311142, by rfl⟩ : syracuseStep 3318853 = 622285) (by norm_num)
theorem B4425137 : Blo 1965435 4425137 := bstep (se 2 (by rfl) ⟨1659426, by rfl⟩ : syracuseStep 4425137 = 3318853) B3318853
theorem B2950091 : Blo 1965435 2950091 := bstep (se 1 (by rfl) ⟨2212568, by rfl⟩ : syracuseStep 2950091 = 4425137) B4425137
theorem B1966727 : Blo 1965435 1966727 := bstep (se 1 (by rfl) ⟨1475045, by rfl⟩ : syracuseStep 1966727 = 2950091) B2950091
theorem B2212573 : Blo 1965435 2212573 := bbase (se 3 (by rfl) ⟨414857, by rfl⟩ : syracuseStep 2212573 = 829715) (by norm_num)
theorem B2950097 : Blo 1965435 2950097 := bstep (se 2 (by rfl) ⟨1106286, by rfl⟩ : syracuseStep 2950097 = 2212573) B2212573
theorem B1966731 : Blo 1965435 1966731 := bstep (se 1 (by rfl) ⟨1475048, by rfl⟩ : syracuseStep 1966731 = 2950097) B2950097
theorem B6637733 : Blo 1965435 6637733 := bbase (se 4 (by rfl) ⟨622287, by rfl⟩ : syracuseStep 6637733 = 1244575) (by norm_num)
theorem B4425155 : Blo 1965435 4425155 := bstep (se 1 (by rfl) ⟨3318866, by rfl⟩ : syracuseStep 4425155 = 6637733) B6637733
theorem B2950103 : Blo 1965435 2950103 := bstep (se 1 (by rfl) ⟨2212577, by rfl⟩ : syracuseStep 2950103 = 4425155) B4425155
theorem B1966735 : Blo 1965435 1966735 := bstep (se 1 (by rfl) ⟨1475051, by rfl⟩ : syracuseStep 1966735 = 2950103) B2950103
theorem B2950109 : Blo 1965435 2950109 := bbase (se 3 (by rfl) ⟨553145, by rfl⟩ : syracuseStep 2950109 = 1106291) (by norm_num)
theorem B1966739 : Blo 1965435 1966739 := bstep (se 1 (by rfl) ⟨1475054, by rfl⟩ : syracuseStep 1966739 = 2950109) B2950109
theorem B4425173 : Blo 1965435 4425173 := bbase (se 7 (by rfl) ⟨51857, by rfl⟩ : syracuseStep 4425173 = 103715) (by norm_num)
theorem B2950115 : Blo 1965435 2950115 := bstep (se 1 (by rfl) ⟨2212586, by rfl⟩ : syracuseStep 2950115 = 4425173) B4425173
theorem B1966743 : Blo 1965435 1966743 := bstep (se 1 (by rfl) ⟨1475057, by rfl⟩ : syracuseStep 1966743 = 2950115) B2950115
theorem B2128889 : Blo 1965435 2128889 := bbase (se 2 (by rfl) ⟨798333, by rfl⟩ : syracuseStep 2128889 = 1596667) (by norm_num)
theorem B5677037 : Blo 1965435 5677037 := bstep (se 3 (by rfl) ⟨1064444, by rfl⟩ : syracuseStep 5677037 = 2128889) B2128889
theorem B3784691 : Blo 1965435 3784691 := bstep (se 1 (by rfl) ⟨2838518, by rfl⟩ : syracuseStep 3784691 = 5677037) B5677037
theorem B10092509 : Blo 1965435 10092509 := bstep (se 3 (by rfl) ⟨1892345, by rfl⟩ : syracuseStep 10092509 = 3784691) B3784691
theorem B6728339 : Blo 1965435 6728339 := bstep (se 1 (by rfl) ⟨5046254, by rfl⟩ : syracuseStep 6728339 = 10092509) B10092509
theorem B4485559 : Blo 1965435 4485559 := bstep (se 1 (by rfl) ⟨3364169, by rfl⟩ : syracuseStep 4485559 = 6728339) B6728339
theorem B5980745 : Blo 1965435 5980745 := bstep (se 2 (by rfl) ⟨2242779, by rfl⟩ : syracuseStep 5980745 = 4485559) B4485559
theorem B3987163 : Blo 1965435 3987163 := bstep (se 1 (by rfl) ⟨2990372, by rfl⟩ : syracuseStep 3987163 = 5980745) B5980745
theorem B21264869 : Blo 1965435 21264869 := bstep (se 4 (by rfl) ⟨1993581, by rfl⟩ : syracuseStep 21264869 = 3987163) B3987163
theorem B14176579 : Blo 1965435 14176579 := bstep (se 1 (by rfl) ⟨10632434, by rfl⟩ : syracuseStep 14176579 = 21264869) B21264869
theorem B18902105 : Blo 1965435 18902105 := bstep (se 2 (by rfl) ⟨7088289, by rfl⟩ : syracuseStep 18902105 = 14176579) B14176579
theorem B12601403 : Blo 1965435 12601403 := bstep (se 1 (by rfl) ⟨9451052, by rfl⟩ : syracuseStep 12601403 = 18902105) B18902105
theorem B8400935 : Blo 1965435 8400935 := bstep (se 1 (by rfl) ⟨6300701, by rfl⟩ : syracuseStep 8400935 = 12601403) B12601403
theorem B5600623 : Blo 1965435 5600623 := bstep (se 1 (by rfl) ⟨4200467, by rfl⟩ : syracuseStep 5600623 = 8400935) B8400935
theorem B7467497 : Blo 1965435 7467497 := bstep (se 2 (by rfl) ⟨2800311, by rfl⟩ : syracuseStep 7467497 = 5600623) B5600623
theorem B4978331 : Blo 1965435 4978331 := bstep (se 1 (by rfl) ⟨3733748, by rfl⟩ : syracuseStep 4978331 = 7467497) B7467497
theorem B3318887 : Blo 1965435 3318887 := bstep (se 1 (by rfl) ⟨2489165, by rfl⟩ : syracuseStep 3318887 = 4978331) B4978331
theorem B2212591 : Blo 1965435 2212591 := bstep (se 1 (by rfl) ⟨1659443, by rfl⟩ : syracuseStep 2212591 = 3318887) B3318887
theorem B2950121 : Blo 1965435 2950121 := bstep (se 2 (by rfl) ⟨1106295, by rfl⟩ : syracuseStep 2950121 = 2212591) B2212591
theorem B1966747 : Blo 1965435 1966747 := bstep (se 1 (by rfl) ⟨1475060, by rfl⟩ : syracuseStep 1966747 = 2950121) B2950121
theorem B27280597 : Blo 1965435 27280597 := bbase (se 7 (by rfl) ⟨319694, by rfl⟩ : syracuseStep 27280597 = 639389) (by norm_num)
theorem B36374129 : Blo 1965435 36374129 := bstep (se 2 (by rfl) ⟨13640298, by rfl⟩ : syracuseStep 36374129 = 27280597) B27280597
theorem B24249419 : Blo 1965435 24249419 := bstep (se 1 (by rfl) ⟨18187064, by rfl⟩ : syracuseStep 24249419 = 36374129) B36374129
theorem B16166279 : Blo 1965435 16166279 := bstep (se 1 (by rfl) ⟨12124709, by rfl⟩ : syracuseStep 16166279 = 24249419) B24249419
theorem B10777519 : Blo 1965435 10777519 := bstep (se 1 (by rfl) ⟨8083139, by rfl⟩ : syracuseStep 10777519 = 16166279) B16166279
theorem B57480101 : Blo 1965435 57480101 := bstep (se 4 (by rfl) ⟨5388759, by rfl⟩ : syracuseStep 57480101 = 10777519) B10777519
theorem B38320067 : Blo 1965435 38320067 := bstep (se 1 (by rfl) ⟨28740050, by rfl⟩ : syracuseStep 38320067 = 57480101) B57480101
theorem B25546711 : Blo 1965435 25546711 := bstep (se 1 (by rfl) ⟨19160033, by rfl⟩ : syracuseStep 25546711 = 38320067) B38320067
theorem B34062281 : Blo 1965435 34062281 := bstep (se 2 (by rfl) ⟨12773355, by rfl⟩ : syracuseStep 34062281 = 25546711) B25546711
theorem B22708187 : Blo 1965435 22708187 := bstep (se 1 (by rfl) ⟨17031140, by rfl⟩ : syracuseStep 22708187 = 34062281) B34062281
theorem B15138791 : Blo 1965435 15138791 := bstep (se 1 (by rfl) ⟨11354093, by rfl⟩ : syracuseStep 15138791 = 22708187) B22708187
theorem B10092527 : Blo 1965435 10092527 := bstep (se 1 (by rfl) ⟨7569395, by rfl⟩ : syracuseStep 10092527 = 15138791) B15138791
theorem B6728351 : Blo 1965435 6728351 := bstep (se 1 (by rfl) ⟨5046263, by rfl⟩ : syracuseStep 6728351 = 10092527) B10092527
theorem B17942269 : Blo 1965435 17942269 := bstep (se 3 (by rfl) ⟨3364175, by rfl⟩ : syracuseStep 17942269 = 6728351) B6728351
theorem B23923025 : Blo 1965435 23923025 := bstep (se 2 (by rfl) ⟨8971134, by rfl⟩ : syracuseStep 23923025 = 17942269) B17942269
theorem B15948683 : Blo 1965435 15948683 := bstep (se 1 (by rfl) ⟨11961512, by rfl⟩ : syracuseStep 15948683 = 23923025) B23923025
theorem B10632455 : Blo 1965435 10632455 := bstep (se 1 (by rfl) ⟨7974341, by rfl⟩ : syracuseStep 10632455 = 15948683) B15948683
theorem B7088303 : Blo 1965435 7088303 := bstep (se 1 (by rfl) ⟨5316227, by rfl⟩ : syracuseStep 7088303 = 10632455) B10632455
theorem B4725535 : Blo 1965435 4725535 := bstep (se 1 (by rfl) ⟨3544151, by rfl⟩ : syracuseStep 4725535 = 7088303) B7088303
theorem B6300713 : Blo 1965435 6300713 := bstep (se 2 (by rfl) ⟨2362767, by rfl⟩ : syracuseStep 6300713 = 4725535) B4725535
theorem B16801901 : Blo 1965435 16801901 := bstep (se 3 (by rfl) ⟨3150356, by rfl⟩ : syracuseStep 16801901 = 6300713) B6300713
theorem B11201267 : Blo 1965435 11201267 := bstep (se 1 (by rfl) ⟨8400950, by rfl⟩ : syracuseStep 11201267 = 16801901) B16801901
theorem B7467511 : Blo 1965435 7467511 := bstep (se 1 (by rfl) ⟨5600633, by rfl⟩ : syracuseStep 7467511 = 11201267) B11201267
theorem B9956681 : Blo 1965435 9956681 := bstep (se 2 (by rfl) ⟨3733755, by rfl⟩ : syracuseStep 9956681 = 7467511) B7467511
theorem B6637787 : Blo 1965435 6637787 := bstep (se 1 (by rfl) ⟨4978340, by rfl⟩ : syracuseStep 6637787 = 9956681) B9956681
theorem B4425191 : Blo 1965435 4425191 := bstep (se 1 (by rfl) ⟨3318893, by rfl⟩ : syracuseStep 4425191 = 6637787) B6637787
theorem B2950127 : Blo 1965435 2950127 := bstep (se 1 (by rfl) ⟨2212595, by rfl⟩ : syracuseStep 2950127 = 4425191) B4425191
theorem B1966751 : Blo 1965435 1966751 := bstep (se 1 (by rfl) ⟨1475063, by rfl⟩ : syracuseStep 1966751 = 2950127) B2950127
theorem B2950133 : Blo 1965435 2950133 := bbase (se 5 (by rfl) ⟨138287, by rfl⟩ : syracuseStep 2950133 = 276575) (by norm_num)
theorem B1966755 : Blo 1965435 1966755 := bstep (se 1 (by rfl) ⟨1475066, by rfl⟩ : syracuseStep 1966755 = 2950133) B2950133
theorem B4200493 : Blo 1965435 4200493 := bbase (se 3 (by rfl) ⟨787592, by rfl⟩ : syracuseStep 4200493 = 1575185) (by norm_num)
theorem B5600657 : Blo 1965435 5600657 := bstep (se 2 (by rfl) ⟨2100246, by rfl⟩ : syracuseStep 5600657 = 4200493) B4200493
theorem B3733771 : Blo 1965435 3733771 := bstep (se 1 (by rfl) ⟨2800328, by rfl⟩ : syracuseStep 3733771 = 5600657) B5600657
theorem B4978361 : Blo 1965435 4978361 := bstep (se 2 (by rfl) ⟨1866885, by rfl⟩ : syracuseStep 4978361 = 3733771) B3733771
theorem B3318907 : Blo 1965435 3318907 := bstep (se 1 (by rfl) ⟨2489180, by rfl⟩ : syracuseStep 3318907 = 4978361) B4978361
theorem B4425209 : Blo 1965435 4425209 := bstep (se 2 (by rfl) ⟨1659453, by rfl⟩ : syracuseStep 4425209 = 3318907) B3318907
theorem B2950139 : Blo 1965435 2950139 := bstep (se 1 (by rfl) ⟨2212604, by rfl⟩ : syracuseStep 2950139 = 4425209) B4425209
theorem B1966759 : Blo 1965435 1966759 := bstep (se 1 (by rfl) ⟨1475069, by rfl⟩ : syracuseStep 1966759 = 2950139) B2950139
theorem B2212609 : Blo 1965435 2212609 := bbase (se 2 (by rfl) ⟨829728, by rfl⟩ : syracuseStep 2212609 = 1659457) (by norm_num)
theorem B2950145 : Blo 1965435 2950145 := bstep (se 2 (by rfl) ⟨1106304, by rfl⟩ : syracuseStep 2950145 = 2212609) B2212609
theorem B1966763 : Blo 1965435 1966763 := bstep (se 1 (by rfl) ⟨1475072, by rfl⟩ : syracuseStep 1966763 = 2950145) B2950145
theorem B4978381 : Blo 1965435 4978381 := bbase (se 3 (by rfl) ⟨933446, by rfl⟩ : syracuseStep 4978381 = 1866893) (by norm_num)
theorem B6637841 : Blo 1965435 6637841 := bstep (se 2 (by rfl) ⟨2489190, by rfl⟩ : syracuseStep 6637841 = 4978381) B4978381
theorem B4425227 : Blo 1965435 4425227 := bstep (se 1 (by rfl) ⟨3318920, by rfl⟩ : syracuseStep 4425227 = 6637841) B6637841
theorem B2950151 : Blo 1965435 2950151 := bstep (se 1 (by rfl) ⟨2212613, by rfl⟩ : syracuseStep 2950151 = 4425227) B4425227
theorem B1966767 : Blo 1965435 1966767 := bstep (se 1 (by rfl) ⟨1475075, by rfl⟩ : syracuseStep 1966767 = 2950151) B2950151
theorem B2950157 : Blo 1965435 2950157 := bbase (se 3 (by rfl) ⟨553154, by rfl⟩ : syracuseStep 2950157 = 1106309) (by norm_num)
theorem B1966771 : Blo 1965435 1966771 := bstep (se 1 (by rfl) ⟨1475078, by rfl⟩ : syracuseStep 1966771 = 2950157) B2950157
theorem B4425245 : Blo 1965435 4425245 := bbase (se 3 (by rfl) ⟨829733, by rfl⟩ : syracuseStep 4425245 = 1659467) (by norm_num)
theorem B2950163 : Blo 1965435 2950163 := bstep (se 1 (by rfl) ⟨2212622, by rfl⟩ : syracuseStep 2950163 = 4425245) B4425245
theorem B1966775 : Blo 1965435 1966775 := bstep (se 1 (by rfl) ⟨1475081, by rfl⟩ : syracuseStep 1966775 = 2950163) B2950163
theorem B3318941 : Blo 1965435 3318941 := bbase (se 3 (by rfl) ⟨622301, by rfl⟩ : syracuseStep 3318941 = 1244603) (by norm_num)
theorem B2212627 : Blo 1965435 2212627 := bstep (se 1 (by rfl) ⟨1659470, by rfl⟩ : syracuseStep 2212627 = 3318941) B3318941
theorem B2950169 : Blo 1965435 2950169 := bstep (se 2 (by rfl) ⟨1106313, by rfl⟩ : syracuseStep 2950169 = 2212627) B2212627
theorem B1966779 : Blo 1965435 1966779 := bstep (se 1 (by rfl) ⟨1475084, by rfl⟩ : syracuseStep 1966779 = 2950169) B2950169
theorem B5115197 : Blo 1965435 5115197 := bbase (se 3 (by rfl) ⟨959099, by rfl⟩ : syracuseStep 5115197 = 1918199) (by norm_num)
theorem B13640525 : Blo 1965435 13640525 := bstep (se 3 (by rfl) ⟨2557598, by rfl⟩ : syracuseStep 13640525 = 5115197) B5115197
theorem B9093683 : Blo 1965435 9093683 := bstep (se 1 (by rfl) ⟨6820262, by rfl⟩ : syracuseStep 9093683 = 13640525) B13640525
theorem B6062455 : Blo 1965435 6062455 := bstep (se 1 (by rfl) ⟨4546841, by rfl⟩ : syracuseStep 6062455 = 9093683) B9093683
theorem B8083273 : Blo 1965435 8083273 := bstep (se 2 (by rfl) ⟨3031227, by rfl⟩ : syracuseStep 8083273 = 6062455) B6062455
theorem B10777697 : Blo 1965435 10777697 := bstep (se 2 (by rfl) ⟨4041636, by rfl⟩ : syracuseStep 10777697 = 8083273) B8083273
theorem B7185131 : Blo 1965435 7185131 := bstep (se 1 (by rfl) ⟨5388848, by rfl⟩ : syracuseStep 7185131 = 10777697) B10777697
theorem B4790087 : Blo 1965435 4790087 := bstep (se 1 (by rfl) ⟨3592565, by rfl⟩ : syracuseStep 4790087 = 7185131) B7185131
theorem B3193391 : Blo 1965435 3193391 := bstep (se 1 (by rfl) ⟨2395043, by rfl⟩ : syracuseStep 3193391 = 4790087) B4790087
theorem B2128927 : Blo 1965435 2128927 := bstep (se 1 (by rfl) ⟨1596695, by rfl⟩ : syracuseStep 2128927 = 3193391) B3193391
theorem B2838569 : Blo 1965435 2838569 := bstep (se 2 (by rfl) ⟨1064463, by rfl⟩ : syracuseStep 2838569 = 2128927) B2128927
theorem B30278069 : Blo 1965435 30278069 := bstep (se 5 (by rfl) ⟨1419284, by rfl⟩ : syracuseStep 30278069 = 2838569) B2838569
theorem B20185379 : Blo 1965435 20185379 := bstep (se 1 (by rfl) ⟨15139034, by rfl⟩ : syracuseStep 20185379 = 30278069) B30278069
theorem B13456919 : Blo 1965435 13456919 := bstep (se 1 (by rfl) ⟨10092689, by rfl⟩ : syracuseStep 13456919 = 20185379) B20185379
theorem B8971279 : Blo 1965435 8971279 := bstep (se 1 (by rfl) ⟨6728459, by rfl⟩ : syracuseStep 8971279 = 13456919) B13456919
theorem B47846821 : Blo 1965435 47846821 := bstep (se 4 (by rfl) ⟨4485639, by rfl⟩ : syracuseStep 47846821 = 8971279) B8971279
theorem B63795761 : Blo 1965435 63795761 := bstep (se 2 (by rfl) ⟨23923410, by rfl⟩ : syracuseStep 63795761 = 47846821) B47846821
theorem B42530507 : Blo 1965435 42530507 := bstep (se 1 (by rfl) ⟨31897880, by rfl⟩ : syracuseStep 42530507 = 63795761) B63795761
theorem B28353671 : Blo 1965435 28353671 := bstep (se 1 (by rfl) ⟨21265253, by rfl⟩ : syracuseStep 28353671 = 42530507) B42530507
theorem B18902447 : Blo 1965435 18902447 := bstep (se 1 (by rfl) ⟨14176835, by rfl⟩ : syracuseStep 18902447 = 28353671) B28353671
theorem B12601631 : Blo 1965435 12601631 := bstep (se 1 (by rfl) ⟨9451223, by rfl⟩ : syracuseStep 12601631 = 18902447) B18902447
theorem B8401087 : Blo 1965435 8401087 := bstep (se 1 (by rfl) ⟨6300815, by rfl⟩ : syracuseStep 8401087 = 12601631) B12601631
theorem B11201449 : Blo 1965435 11201449 := bstep (se 2 (by rfl) ⟨4200543, by rfl⟩ : syracuseStep 11201449 = 8401087) B8401087
theorem B14935265 : Blo 1965435 14935265 := bstep (se 2 (by rfl) ⟨5600724, by rfl⟩ : syracuseStep 14935265 = 11201449) B11201449
theorem B9956843 : Blo 1965435 9956843 := bstep (se 1 (by rfl) ⟨7467632, by rfl⟩ : syracuseStep 9956843 = 14935265) B14935265
theorem B6637895 : Blo 1965435 6637895 := bstep (se 1 (by rfl) ⟨4978421, by rfl⟩ : syracuseStep 6637895 = 9956843) B9956843
theorem B4425263 : Blo 1965435 4425263 := bstep (se 1 (by rfl) ⟨3318947, by rfl⟩ : syracuseStep 4425263 = 6637895) B6637895
theorem B2950175 : Blo 1965435 2950175 := bstep (se 1 (by rfl) ⟨2212631, by rfl⟩ : syracuseStep 2950175 = 4425263) B4425263
theorem B1966783 : Blo 1965435 1966783 := bstep (se 1 (by rfl) ⟨1475087, by rfl⟩ : syracuseStep 1966783 = 2950175) B2950175
theorem B2950181 : Blo 1965435 2950181 := bbase (se 4 (by rfl) ⟨276579, by rfl⟩ : syracuseStep 2950181 = 553159) (by norm_num)
theorem B1966787 : Blo 1965435 1966787 := bstep (se 1 (by rfl) ⟨1475090, by rfl⟩ : syracuseStep 1966787 = 2950181) B2950181
theorem B2489221 : Blo 1965435 2489221 := bbase (se 4 (by rfl) ⟨233364, by rfl⟩ : syracuseStep 2489221 = 466729) (by norm_num)
theorem B3318961 : Blo 1965435 3318961 := bstep (se 2 (by rfl) ⟨1244610, by rfl⟩ : syracuseStep 3318961 = 2489221) B2489221
theorem B4425281 : Blo 1965435 4425281 := bstep (se 2 (by rfl) ⟨1659480, by rfl⟩ : syracuseStep 4425281 = 3318961) B3318961
theorem B2950187 : Blo 1965435 2950187 := bstep (se 1 (by rfl) ⟨2212640, by rfl⟩ : syracuseStep 2950187 = 4425281) B4425281
theorem B1966791 : Blo 1965435 1966791 := bstep (se 1 (by rfl) ⟨1475093, by rfl⟩ : syracuseStep 1966791 = 2950187) B2950187
theorem B2212645 : Blo 1965435 2212645 := bbase (se 4 (by rfl) ⟨207435, by rfl⟩ : syracuseStep 2212645 = 414871) (by norm_num)
theorem B2950193 : Blo 1965435 2950193 := bstep (se 2 (by rfl) ⟨1106322, by rfl⟩ : syracuseStep 2950193 = 2212645) B2212645
theorem B1966795 : Blo 1965435 1966795 := bstep (se 1 (by rfl) ⟨1475096, by rfl⟩ : syracuseStep 1966795 = 2950193) B2950193
theorem B8401157 : Blo 1965435 8401157 := bbase (se 4 (by rfl) ⟨787608, by rfl⟩ : syracuseStep 8401157 = 1575217) (by norm_num)
theorem B5600771 : Blo 1965435 5600771 := bstep (se 1 (by rfl) ⟨4200578, by rfl⟩ : syracuseStep 5600771 = 8401157) B8401157
theorem B3733847 : Blo 1965435 3733847 := bstep (se 1 (by rfl) ⟨2800385, by rfl⟩ : syracuseStep 3733847 = 5600771) B5600771
theorem B2489231 : Blo 1965435 2489231 := bstep (se 1 (by rfl) ⟨1866923, by rfl⟩ : syracuseStep 2489231 = 3733847) B3733847
theorem B6637949 : Blo 1965435 6637949 := bstep (se 3 (by rfl) ⟨1244615, by rfl⟩ : syracuseStep 6637949 = 2489231) B2489231
theorem B4425299 : Blo 1965435 4425299 := bstep (se 1 (by rfl) ⟨3318974, by rfl⟩ : syracuseStep 4425299 = 6637949) B6637949
theorem B2950199 : Blo 1965435 2950199 := bstep (se 1 (by rfl) ⟨2212649, by rfl⟩ : syracuseStep 2950199 = 4425299) B4425299
theorem B1966799 : Blo 1965435 1966799 := bstep (se 1 (by rfl) ⟨1475099, by rfl⟩ : syracuseStep 1966799 = 2950199) B2950199
theorem B2950205 : Blo 1965435 2950205 := bbase (se 3 (by rfl) ⟨553163, by rfl⟩ : syracuseStep 2950205 = 1106327) (by norm_num)
theorem B1966803 : Blo 1965435 1966803 := bstep (se 1 (by rfl) ⟨1475102, by rfl⟩ : syracuseStep 1966803 = 2950205) B2950205
theorem B4425317 : Blo 1965435 4425317 := bbase (se 4 (by rfl) ⟨414873, by rfl⟩ : syracuseStep 4425317 = 829747) (by norm_num)
theorem B2950211 : Blo 1965435 2950211 := bstep (se 1 (by rfl) ⟨2212658, by rfl⟩ : syracuseStep 2950211 = 4425317) B4425317
theorem B1966807 : Blo 1965435 1966807 := bstep (se 1 (by rfl) ⟨1475105, by rfl⟩ : syracuseStep 1966807 = 2950211) B2950211
theorem B4978493 : Blo 1965435 4978493 := bbase (se 3 (by rfl) ⟨933467, by rfl⟩ : syracuseStep 4978493 = 1866935) (by norm_num)
theorem B3318995 : Blo 1965435 3318995 := bstep (se 1 (by rfl) ⟨2489246, by rfl⟩ : syracuseStep 3318995 = 4978493) B4978493
theorem B2212663 : Blo 1965435 2212663 := bstep (se 1 (by rfl) ⟨1659497, by rfl⟩ : syracuseStep 2212663 = 3318995) B3318995
theorem B2950217 : Blo 1965435 2950217 := bstep (se 2 (by rfl) ⟨1106331, by rfl⟩ : syracuseStep 2950217 = 2212663) B2212663
theorem B1966811 : Blo 1965435 1966811 := bstep (se 1 (by rfl) ⟨1475108, by rfl⟩ : syracuseStep 1966811 = 2950217) B2950217
theorem B3733877 : Blo 1965435 3733877 := bbase (se 5 (by rfl) ⟨175025, by rfl⟩ : syracuseStep 3733877 = 350051) (by norm_num)
theorem B9957005 : Blo 1965435 9957005 := bstep (se 3 (by rfl) ⟨1866938, by rfl⟩ : syracuseStep 9957005 = 3733877) B3733877
theorem B6638003 : Blo 1965435 6638003 := bstep (se 1 (by rfl) ⟨4978502, by rfl⟩ : syracuseStep 6638003 = 9957005) B9957005
theorem B4425335 : Blo 1965435 4425335 := bstep (se 1 (by rfl) ⟨3319001, by rfl⟩ : syracuseStep 4425335 = 6638003) B6638003
theorem B2950223 : Blo 1965435 2950223 := bstep (se 1 (by rfl) ⟨2212667, by rfl⟩ : syracuseStep 2950223 = 4425335) B4425335
theorem B1966815 : Blo 1965435 1966815 := bstep (se 1 (by rfl) ⟨1475111, by rfl⟩ : syracuseStep 1966815 = 2950223) B2950223
theorem B2950229 : Blo 1965435 2950229 := bbase (se 8 (by rfl) ⟨17286, by rfl⟩ : syracuseStep 2950229 = 34573) (by norm_num)
theorem B1966819 : Blo 1965435 1966819 := bstep (se 1 (by rfl) ⟨1475114, by rfl⟩ : syracuseStep 1966819 = 2950229) B2950229
theorem B3987317 : Blo 1965435 3987317 := bbase (se 5 (by rfl) ⟨186905, by rfl⟩ : syracuseStep 3987317 = 373811) (by norm_num)
theorem B10632845 : Blo 1965435 10632845 := bstep (se 3 (by rfl) ⟨1993658, by rfl⟩ : syracuseStep 10632845 = 3987317) B3987317
theorem B7088563 : Blo 1965435 7088563 := bstep (se 1 (by rfl) ⟨5316422, by rfl⟩ : syracuseStep 7088563 = 10632845) B10632845
theorem B9451417 : Blo 1965435 9451417 := bstep (se 2 (by rfl) ⟨3544281, by rfl⟩ : syracuseStep 9451417 = 7088563) B7088563
theorem B12601889 : Blo 1965435 12601889 := bstep (se 2 (by rfl) ⟨4725708, by rfl⟩ : syracuseStep 12601889 = 9451417) B9451417
theorem B8401259 : Blo 1965435 8401259 := bstep (se 1 (by rfl) ⟨6300944, by rfl⟩ : syracuseStep 8401259 = 12601889) B12601889
theorem B5600839 : Blo 1965435 5600839 := bstep (se 1 (by rfl) ⟨4200629, by rfl⟩ : syracuseStep 5600839 = 8401259) B8401259
theorem B7467785 : Blo 1965435 7467785 := bstep (se 2 (by rfl) ⟨2800419, by rfl⟩ : syracuseStep 7467785 = 5600839) B5600839
theorem B4978523 : Blo 1965435 4978523 := bstep (se 1 (by rfl) ⟨3733892, by rfl⟩ : syracuseStep 4978523 = 7467785) B7467785
theorem B3319015 : Blo 1965435 3319015 := bstep (se 1 (by rfl) ⟨2489261, by rfl⟩ : syracuseStep 3319015 = 4978523) B4978523
theorem B4425353 : Blo 1965435 4425353 := bstep (se 2 (by rfl) ⟨1659507, by rfl⟩ : syracuseStep 4425353 = 3319015) B3319015
theorem B2950235 : Blo 1965435 2950235 := bstep (se 1 (by rfl) ⟨2212676, by rfl⟩ : syracuseStep 2950235 = 4425353) B4425353
theorem B1966823 : Blo 1965435 1966823 := bstep (se 1 (by rfl) ⟨1475117, by rfl⟩ : syracuseStep 1966823 = 2950235) B2950235
theorem B2212681 : Blo 1965435 2212681 := bbase (se 2 (by rfl) ⟨829755, by rfl⟩ : syracuseStep 2212681 = 1659511) (by norm_num)
theorem B2950241 : Blo 1965435 2950241 := bstep (se 2 (by rfl) ⟨1106340, by rfl⟩ : syracuseStep 2950241 = 2212681) B2212681
theorem B1966827 : Blo 1965435 1966827 := bstep (se 1 (by rfl) ⟨1475120, by rfl⟩ : syracuseStep 1966827 = 2950241) B2950241
theorem B3031301 : Blo 1965435 3031301 := bbase (se 4 (by rfl) ⟨284184, by rfl⟩ : syracuseStep 3031301 = 568369) (by norm_num)
theorem B8083469 : Blo 1965435 8083469 := bstep (se 3 (by rfl) ⟨1515650, by rfl⟩ : syracuseStep 8083469 = 3031301) B3031301
theorem B5388979 : Blo 1965435 5388979 := bstep (se 1 (by rfl) ⟨4041734, by rfl⟩ : syracuseStep 5388979 = 8083469) B8083469
theorem B7185305 : Blo 1965435 7185305 := bstep (se 2 (by rfl) ⟨2694489, by rfl⟩ : syracuseStep 7185305 = 5388979) B5388979
theorem B19160813 : Blo 1965435 19160813 := bstep (se 3 (by rfl) ⟨3592652, by rfl⟩ : syracuseStep 19160813 = 7185305) B7185305
theorem B12773875 : Blo 1965435 12773875 := bstep (se 1 (by rfl) ⟨9580406, by rfl⟩ : syracuseStep 12773875 = 19160813) B19160813
theorem B17031833 : Blo 1965435 17031833 := bstep (se 2 (by rfl) ⟨6386937, by rfl⟩ : syracuseStep 17031833 = 12773875) B12773875
theorem B11354555 : Blo 1965435 11354555 := bstep (se 1 (by rfl) ⟨8515916, by rfl⟩ : syracuseStep 11354555 = 17031833) B17031833
theorem B7569703 : Blo 1965435 7569703 := bstep (se 1 (by rfl) ⟨5677277, by rfl⟩ : syracuseStep 7569703 = 11354555) B11354555
theorem B10092937 : Blo 1965435 10092937 := bstep (se 2 (by rfl) ⟨3784851, by rfl⟩ : syracuseStep 10092937 = 7569703) B7569703
theorem B13457249 : Blo 1965435 13457249 := bstep (se 2 (by rfl) ⟨5046468, by rfl⟩ : syracuseStep 13457249 = 10092937) B10092937
theorem B8971499 : Blo 1965435 8971499 := bstep (se 1 (by rfl) ⟨6728624, by rfl⟩ : syracuseStep 8971499 = 13457249) B13457249
theorem B23923997 : Blo 1965435 23923997 := bstep (se 3 (by rfl) ⟨4485749, by rfl⟩ : syracuseStep 23923997 = 8971499) B8971499
theorem B15949331 : Blo 1965435 15949331 := bstep (se 1 (by rfl) ⟨11961998, by rfl⟩ : syracuseStep 15949331 = 23923997) B23923997
theorem B10632887 : Blo 1965435 10632887 := bstep (se 1 (by rfl) ⟨7974665, by rfl⟩ : syracuseStep 10632887 = 15949331) B15949331
theorem B7088591 : Blo 1965435 7088591 := bstep (se 1 (by rfl) ⟨5316443, by rfl⟩ : syracuseStep 7088591 = 10632887) B10632887
theorem B18902909 : Blo 1965435 18902909 := bstep (se 3 (by rfl) ⟨3544295, by rfl⟩ : syracuseStep 18902909 = 7088591) B7088591
theorem B12601939 : Blo 1965435 12601939 := bstep (se 1 (by rfl) ⟨9451454, by rfl⟩ : syracuseStep 12601939 = 18902909) B18902909
theorem B16802585 : Blo 1965435 16802585 := bstep (se 2 (by rfl) ⟨6300969, by rfl⟩ : syracuseStep 16802585 = 12601939) B12601939
theorem B11201723 : Blo 1965435 11201723 := bstep (se 1 (by rfl) ⟨8401292, by rfl⟩ : syracuseStep 11201723 = 16802585) B16802585
theorem B7467815 : Blo 1965435 7467815 := bstep (se 1 (by rfl) ⟨5600861, by rfl⟩ : syracuseStep 7467815 = 11201723) B11201723
theorem B4978543 : Blo 1965435 4978543 := bstep (se 1 (by rfl) ⟨3733907, by rfl⟩ : syracuseStep 4978543 = 7467815) B7467815
theorem B6638057 : Blo 1965435 6638057 := bstep (se 2 (by rfl) ⟨2489271, by rfl⟩ : syracuseStep 6638057 = 4978543) B4978543
theorem B4425371 : Blo 1965435 4425371 := bstep (se 1 (by rfl) ⟨3319028, by rfl⟩ : syracuseStep 4425371 = 6638057) B6638057
theorem B2950247 : Blo 1965435 2950247 := bstep (se 1 (by rfl) ⟨2212685, by rfl⟩ : syracuseStep 2950247 = 4425371) B4425371
theorem B1966831 : Blo 1965435 1966831 := bstep (se 1 (by rfl) ⟨1475123, by rfl⟩ : syracuseStep 1966831 = 2950247) B2950247
theorem B2950253 : Blo 1965435 2950253 := bbase (se 3 (by rfl) ⟨553172, by rfl⟩ : syracuseStep 2950253 = 1106345) (by norm_num)
theorem B1966835 : Blo 1965435 1966835 := bstep (se 1 (by rfl) ⟨1475126, by rfl⟩ : syracuseStep 1966835 = 2950253) B2950253
theorem B4425389 : Blo 1965435 4425389 := bbase (se 3 (by rfl) ⟨829760, by rfl⟩ : syracuseStep 4425389 = 1659521) (by norm_num)
theorem B2950259 : Blo 1965435 2950259 := bstep (se 1 (by rfl) ⟨2212694, by rfl⟩ : syracuseStep 2950259 = 4425389) B4425389
theorem B1966839 : Blo 1965435 1966839 := bstep (se 1 (by rfl) ⟨1475129, by rfl⟩ : syracuseStep 1966839 = 2950259) B2950259
theorem B8515973 : Blo 1965435 8515973 := bbase (se 4 (by rfl) ⟨798372, by rfl⟩ : syracuseStep 8515973 = 1596745) (by norm_num)
theorem B22709261 : Blo 1965435 22709261 := bstep (se 3 (by rfl) ⟨4257986, by rfl⟩ : syracuseStep 22709261 = 8515973) B8515973
theorem B60558029 : Blo 1965435 60558029 := bstep (se 3 (by rfl) ⟨11354630, by rfl⟩ : syracuseStep 60558029 = 22709261) B22709261
theorem B40372019 : Blo 1965435 40372019 := bstep (se 1 (by rfl) ⟨30279014, by rfl⟩ : syracuseStep 40372019 = 60558029) B60558029
theorem B26914679 : Blo 1965435 26914679 := bstep (se 1 (by rfl) ⟨20186009, by rfl⟩ : syracuseStep 26914679 = 40372019) B40372019
theorem B17943119 : Blo 1965435 17943119 := bstep (se 1 (by rfl) ⟨13457339, by rfl⟩ : syracuseStep 17943119 = 26914679) B26914679
theorem B11962079 : Blo 1965435 11962079 := bstep (se 1 (by rfl) ⟨8971559, by rfl⟩ : syracuseStep 11962079 = 17943119) B17943119
theorem B7974719 : Blo 1965435 7974719 := bstep (se 1 (by rfl) ⟨5981039, by rfl⟩ : syracuseStep 7974719 = 11962079) B11962079
theorem B5316479 : Blo 1965435 5316479 := bstep (se 1 (by rfl) ⟨3987359, by rfl⟩ : syracuseStep 5316479 = 7974719) B7974719
theorem B3544319 : Blo 1965435 3544319 := bstep (se 1 (by rfl) ⟨2658239, by rfl⟩ : syracuseStep 3544319 = 5316479) B5316479
theorem B2362879 : Blo 1965435 2362879 := bstep (se 1 (by rfl) ⟨1772159, by rfl⟩ : syracuseStep 2362879 = 3544319) B3544319
theorem B3150505 : Blo 1965435 3150505 := bstep (se 2 (by rfl) ⟨1181439, by rfl⟩ : syracuseStep 3150505 = 2362879) B2362879
theorem B4200673 : Blo 1965435 4200673 := bstep (se 2 (by rfl) ⟨1575252, by rfl⟩ : syracuseStep 4200673 = 3150505) B3150505
theorem B5600897 : Blo 1965435 5600897 := bstep (se 2 (by rfl) ⟨2100336, by rfl⟩ : syracuseStep 5600897 = 4200673) B4200673
theorem B3733931 : Blo 1965435 3733931 := bstep (se 1 (by rfl) ⟨2800448, by rfl⟩ : syracuseStep 3733931 = 5600897) B5600897
theorem B2489287 : Blo 1965435 2489287 := bstep (se 1 (by rfl) ⟨1866965, by rfl⟩ : syracuseStep 2489287 = 3733931) B3733931
theorem B3319049 : Blo 1965435 3319049 := bstep (se 2 (by rfl) ⟨1244643, by rfl⟩ : syracuseStep 3319049 = 2489287) B2489287
theorem B2212699 : Blo 1965435 2212699 := bstep (se 1 (by rfl) ⟨1659524, by rfl⟩ : syracuseStep 2212699 = 3319049) B3319049
theorem B2950265 : Blo 1965435 2950265 := bstep (se 2 (by rfl) ⟨1106349, by rfl⟩ : syracuseStep 2950265 = 2212699) B2212699
theorem B1966843 : Blo 1965435 1966843 := bstep (se 1 (by rfl) ⟨1475132, by rfl⟩ : syracuseStep 1966843 = 2950265) B2950265
theorem B18903061 : Blo 1965435 18903061 := bbase (se 6 (by rfl) ⟨443040, by rfl⟩ : syracuseStep 18903061 = 886081) (by norm_num)
theorem B25204081 : Blo 1965435 25204081 := bstep (se 2 (by rfl) ⟨9451530, by rfl⟩ : syracuseStep 25204081 = 18903061) B18903061
theorem B33605441 : Blo 1965435 33605441 := bstep (se 2 (by rfl) ⟨12602040, by rfl⟩ : syracuseStep 33605441 = 25204081) B25204081
theorem B22403627 : Blo 1965435 22403627 := bstep (se 1 (by rfl) ⟨16802720, by rfl⟩ : syracuseStep 22403627 = 33605441) B33605441
theorem B14935751 : Blo 1965435 14935751 := bstep (se 1 (by rfl) ⟨11201813, by rfl⟩ : syracuseStep 14935751 = 22403627) B22403627
theorem B9957167 : Blo 1965435 9957167 := bstep (se 1 (by rfl) ⟨7467875, by rfl⟩ : syracuseStep 9957167 = 14935751) B14935751
theorem B6638111 : Blo 1965435 6638111 := bstep (se 1 (by rfl) ⟨4978583, by rfl⟩ : syracuseStep 6638111 = 9957167) B9957167
theorem B4425407 : Blo 1965435 4425407 := bstep (se 1 (by rfl) ⟨3319055, by rfl⟩ : syracuseStep 4425407 = 6638111) B6638111
theorem B2950271 : Blo 1965435 2950271 := bstep (se 1 (by rfl) ⟨2212703, by rfl⟩ : syracuseStep 2950271 = 4425407) B4425407
theorem B1966847 : Blo 1965435 1966847 := bstep (se 1 (by rfl) ⟨1475135, by rfl⟩ : syracuseStep 1966847 = 2950271) B2950271
theorem B2950277 : Blo 1965435 2950277 := bbase (se 4 (by rfl) ⟨276588, by rfl⟩ : syracuseStep 2950277 = 553177) (by norm_num)
theorem B1966851 : Blo 1965435 1966851 := bstep (se 1 (by rfl) ⟨1475138, by rfl⟩ : syracuseStep 1966851 = 2950277) B2950277
theorem B3319069 : Blo 1965435 3319069 := bbase (se 3 (by rfl) ⟨622325, by rfl⟩ : syracuseStep 3319069 = 1244651) (by norm_num)
theorem B4425425 : Blo 1965435 4425425 := bstep (se 2 (by rfl) ⟨1659534, by rfl⟩ : syracuseStep 4425425 = 3319069) B3319069
theorem B2950283 : Blo 1965435 2950283 := bstep (se 1 (by rfl) ⟨2212712, by rfl⟩ : syracuseStep 2950283 = 4425425) B4425425
theorem B1966855 : Blo 1965435 1966855 := bstep (se 1 (by rfl) ⟨1475141, by rfl⟩ : syracuseStep 1966855 = 2950283) B2950283
theorem B2212717 : Blo 1965435 2212717 := bbase (se 3 (by rfl) ⟨414884, by rfl⟩ : syracuseStep 2212717 = 829769) (by norm_num)
theorem B2950289 : Blo 1965435 2950289 := bstep (se 2 (by rfl) ⟨1106358, by rfl⟩ : syracuseStep 2950289 = 2212717) B2212717
theorem B1966859 : Blo 1965435 1966859 := bstep (se 1 (by rfl) ⟨1475144, by rfl⟩ : syracuseStep 1966859 = 2950289) B2950289
theorem B6638165 : Blo 1965435 6638165 := bbase (se 8 (by rfl) ⟨38895, by rfl⟩ : syracuseStep 6638165 = 77791) (by norm_num)
theorem B4425443 : Blo 1965435 4425443 := bstep (se 1 (by rfl) ⟨3319082, by rfl⟩ : syracuseStep 4425443 = 6638165) B6638165
theorem B2950295 : Blo 1965435 2950295 := bstep (se 1 (by rfl) ⟨2212721, by rfl⟩ : syracuseStep 2950295 = 4425443) B4425443
theorem B1966863 : Blo 1965435 1966863 := bstep (se 1 (by rfl) ⟨1475147, by rfl⟩ : syracuseStep 1966863 = 2950295) B2950295
theorem B2950301 : Blo 1965435 2950301 := bbase (se 3 (by rfl) ⟨553181, by rfl⟩ : syracuseStep 2950301 = 1106363) (by norm_num)
theorem B1966867 : Blo 1965435 1966867 := bstep (se 1 (by rfl) ⟨1475150, by rfl⟩ : syracuseStep 1966867 = 2950301) B2950301
theorem B4425461 : Blo 1965435 4425461 := bbase (se 5 (by rfl) ⟨207443, by rfl⟩ : syracuseStep 4425461 = 414887) (by norm_num)
theorem B2950307 : Blo 1965435 2950307 := bstep (se 1 (by rfl) ⟨2212730, by rfl⟩ : syracuseStep 2950307 = 4425461) B4425461
theorem B1966871 : Blo 1965435 1966871 := bstep (se 1 (by rfl) ⟨1475153, by rfl⟩ : syracuseStep 1966871 = 2950307) B2950307
theorem B6062741 : Blo 1965435 6062741 := bbase (se 6 (by rfl) ⟨142095, by rfl⟩ : syracuseStep 6062741 = 284191) (by norm_num)
theorem B4041827 : Blo 1965435 4041827 := bstep (se 1 (by rfl) ⟨3031370, by rfl⟩ : syracuseStep 4041827 = 6062741) B6062741
theorem B2694551 : Blo 1965435 2694551 := bstep (se 1 (by rfl) ⟨2020913, by rfl⟩ : syracuseStep 2694551 = 4041827) B4041827
theorem B7185469 : Blo 1965435 7185469 := bstep (se 3 (by rfl) ⟨1347275, by rfl⟩ : syracuseStep 7185469 = 2694551) B2694551
theorem B9580625 : Blo 1965435 9580625 := bstep (se 2 (by rfl) ⟨3592734, by rfl⟩ : syracuseStep 9580625 = 7185469) B7185469
theorem B6387083 : Blo 1965435 6387083 := bstep (se 1 (by rfl) ⟨4790312, by rfl⟩ : syracuseStep 6387083 = 9580625) B9580625
theorem B4258055 : Blo 1965435 4258055 := bstep (se 1 (by rfl) ⟨3193541, by rfl⟩ : syracuseStep 4258055 = 6387083) B6387083
theorem B11354813 : Blo 1965435 11354813 := bstep (se 3 (by rfl) ⟨2129027, by rfl⟩ : syracuseStep 11354813 = 4258055) B4258055
theorem B7569875 : Blo 1965435 7569875 := bstep (se 1 (by rfl) ⟨5677406, by rfl⟩ : syracuseStep 7569875 = 11354813) B11354813
theorem B5046583 : Blo 1965435 5046583 := bstep (se 1 (by rfl) ⟨3784937, by rfl⟩ : syracuseStep 5046583 = 7569875) B7569875
theorem B6728777 : Blo 1965435 6728777 := bstep (se 2 (by rfl) ⟨2523291, by rfl⟩ : syracuseStep 6728777 = 5046583) B5046583
theorem B4485851 : Blo 1965435 4485851 := bstep (se 1 (by rfl) ⟨3364388, by rfl⟩ : syracuseStep 4485851 = 6728777) B6728777
theorem B2990567 : Blo 1965435 2990567 := bstep (se 1 (by rfl) ⟨2242925, by rfl⟩ : syracuseStep 2990567 = 4485851) B4485851
theorem B7974845 : Blo 1965435 7974845 := bstep (se 3 (by rfl) ⟨1495283, by rfl⟩ : syracuseStep 7974845 = 2990567) B2990567
theorem B5316563 : Blo 1965435 5316563 := bstep (se 1 (by rfl) ⟨3987422, by rfl⟩ : syracuseStep 5316563 = 7974845) B7974845
theorem B14177501 : Blo 1965435 14177501 := bstep (se 3 (by rfl) ⟨2658281, by rfl⟩ : syracuseStep 14177501 = 5316563) B5316563
theorem B9451667 : Blo 1965435 9451667 := bstep (se 1 (by rfl) ⟨7088750, by rfl⟩ : syracuseStep 9451667 = 14177501) B14177501
theorem B25204445 : Blo 1965435 25204445 := bstep (se 3 (by rfl) ⟨4725833, by rfl⟩ : syracuseStep 25204445 = 9451667) B9451667
theorem B16802963 : Blo 1965435 16802963 := bstep (se 1 (by rfl) ⟨12602222, by rfl⟩ : syracuseStep 16802963 = 25204445) B25204445
theorem B11201975 : Blo 1965435 11201975 := bstep (se 1 (by rfl) ⟨8401481, by rfl⟩ : syracuseStep 11201975 = 16802963) B16802963
theorem B7467983 : Blo 1965435 7467983 := bstep (se 1 (by rfl) ⟨5600987, by rfl⟩ : syracuseStep 7467983 = 11201975) B11201975
theorem B4978655 : Blo 1965435 4978655 := bstep (se 1 (by rfl) ⟨3733991, by rfl⟩ : syracuseStep 4978655 = 7467983) B7467983
theorem B3319103 : Blo 1965435 3319103 := bstep (se 1 (by rfl) ⟨2489327, by rfl⟩ : syracuseStep 3319103 = 4978655) B4978655
theorem B2212735 : Blo 1965435 2212735 := bstep (se 1 (by rfl) ⟨1659551, by rfl⟩ : syracuseStep 2212735 = 3319103) B3319103
theorem B2950313 : Blo 1965435 2950313 := bstep (se 2 (by rfl) ⟨1106367, by rfl⟩ : syracuseStep 2950313 = 2212735) B2212735
theorem B1966875 : Blo 1965435 1966875 := bstep (se 1 (by rfl) ⟨1475156, by rfl⟩ : syracuseStep 1966875 = 2950313) B2950313
theorem B4200749 : Blo 1965435 4200749 := bbase (se 3 (by rfl) ⟨787640, by rfl⟩ : syracuseStep 4200749 = 1575281) (by norm_num)
theorem B2800499 : Blo 1965435 2800499 := bstep (se 1 (by rfl) ⟨2100374, by rfl⟩ : syracuseStep 2800499 = 4200749) B4200749
theorem B7467997 : Blo 1965435 7467997 := bstep (se 3 (by rfl) ⟨1400249, by rfl⟩ : syracuseStep 7467997 = 2800499) B2800499
theorem B9957329 : Blo 1965435 9957329 := bstep (se 2 (by rfl) ⟨3733998, by rfl⟩ : syracuseStep 9957329 = 7467997) B7467997
theorem B6638219 : Blo 1965435 6638219 := bstep (se 1 (by rfl) ⟨4978664, by rfl⟩ : syracuseStep 6638219 = 9957329) B9957329
theorem B4425479 : Blo 1965435 4425479 := bstep (se 1 (by rfl) ⟨3319109, by rfl⟩ : syracuseStep 4425479 = 6638219) B6638219
theorem B2950319 : Blo 1965435 2950319 := bstep (se 1 (by rfl) ⟨2212739, by rfl⟩ : syracuseStep 2950319 = 4425479) B4425479
theorem B1966879 : Blo 1965435 1966879 := bstep (se 1 (by rfl) ⟨1475159, by rfl⟩ : syracuseStep 1966879 = 2950319) B2950319
theorem B2950325 : Blo 1965435 2950325 := bbase (se 5 (by rfl) ⟨138296, by rfl⟩ : syracuseStep 2950325 = 276593) (by norm_num)
theorem B1966883 : Blo 1965435 1966883 := bstep (se 1 (by rfl) ⟨1475162, by rfl⟩ : syracuseStep 1966883 = 2950325) B2950325
theorem B4978685 : Blo 1965435 4978685 := bbase (se 3 (by rfl) ⟨933503, by rfl⟩ : syracuseStep 4978685 = 1867007) (by norm_num)
theorem B3319123 : Blo 1965435 3319123 := bstep (se 1 (by rfl) ⟨2489342, by rfl⟩ : syracuseStep 3319123 = 4978685) B4978685
theorem B4425497 : Blo 1965435 4425497 := bstep (se 2 (by rfl) ⟨1659561, by rfl⟩ : syracuseStep 4425497 = 3319123) B3319123
theorem B2950331 : Blo 1965435 2950331 := bstep (se 1 (by rfl) ⟨2212748, by rfl⟩ : syracuseStep 2950331 = 4425497) B4425497
theorem B1966887 : Blo 1965435 1966887 := bstep (se 1 (by rfl) ⟨1475165, by rfl⟩ : syracuseStep 1966887 = 2950331) B2950331
theorem B2212753 : Blo 1965435 2212753 := bbase (se 2 (by rfl) ⟨829782, by rfl⟩ : syracuseStep 2212753 = 1659565) (by norm_num)
theorem B2950337 : Blo 1965435 2950337 := bstep (se 2 (by rfl) ⟨1106376, by rfl⟩ : syracuseStep 2950337 = 2212753) B2212753
theorem B1966891 : Blo 1965435 1966891 := bstep (se 1 (by rfl) ⟨1475168, by rfl⟩ : syracuseStep 1966891 = 2950337) B2950337
theorem B3734029 : Blo 1965435 3734029 := bbase (se 3 (by rfl) ⟨700130, by rfl⟩ : syracuseStep 3734029 = 1400261) (by norm_num)
theorem B4978705 : Blo 1965435 4978705 := bstep (se 2 (by rfl) ⟨1867014, by rfl⟩ : syracuseStep 4978705 = 3734029) B3734029
theorem B6638273 : Blo 1965435 6638273 := bstep (se 2 (by rfl) ⟨2489352, by rfl⟩ : syracuseStep 6638273 = 4978705) B4978705
theorem B4425515 : Blo 1965435 4425515 := bstep (se 1 (by rfl) ⟨3319136, by rfl⟩ : syracuseStep 4425515 = 6638273) B6638273
theorem B2950343 : Blo 1965435 2950343 := bstep (se 1 (by rfl) ⟨2212757, by rfl⟩ : syracuseStep 2950343 = 4425515) B4425515
theorem B1966895 : Blo 1965435 1966895 := bstep (se 1 (by rfl) ⟨1475171, by rfl⟩ : syracuseStep 1966895 = 2950343) B2950343
theorem B2950349 : Blo 1965435 2950349 := bbase (se 3 (by rfl) ⟨553190, by rfl⟩ : syracuseStep 2950349 = 1106381) (by norm_num)
theorem B1966899 : Blo 1965435 1966899 := bstep (se 1 (by rfl) ⟨1475174, by rfl⟩ : syracuseStep 1966899 = 2950349) B2950349
theorem B4425533 : Blo 1965435 4425533 := bbase (se 3 (by rfl) ⟨829787, by rfl⟩ : syracuseStep 4425533 = 1659575) (by norm_num)
theorem B2950355 : Blo 1965435 2950355 := bstep (se 1 (by rfl) ⟨2212766, by rfl⟩ : syracuseStep 2950355 = 4425533) B4425533
theorem B1966903 : Blo 1965435 1966903 := bstep (se 1 (by rfl) ⟨1475177, by rfl⟩ : syracuseStep 1966903 = 2950355) B2950355
theorem B3319157 : Blo 1965435 3319157 := bbase (se 5 (by rfl) ⟨155585, by rfl⟩ : syracuseStep 3319157 = 311171) (by norm_num)
theorem B2212771 : Blo 1965435 2212771 := bstep (se 1 (by rfl) ⟨1659578, by rfl⟩ : syracuseStep 2212771 = 3319157) B3319157
theorem B2950361 : Blo 1965435 2950361 := bstep (se 2 (by rfl) ⟨1106385, by rfl⟩ : syracuseStep 2950361 = 2212771) B2212771
theorem B1966907 : Blo 1965435 1966907 := bstep (se 1 (by rfl) ⟨1475180, by rfl⟩ : syracuseStep 1966907 = 2950361) B2950361
theorem B3150613 : Blo 1965435 3150613 := bbase (se 6 (by rfl) ⟨73842, by rfl⟩ : syracuseStep 3150613 = 147685) (by norm_num)
theorem B4200817 : Blo 1965435 4200817 := bstep (se 2 (by rfl) ⟨1575306, by rfl⟩ : syracuseStep 4200817 = 3150613) B3150613
theorem B5601089 : Blo 1965435 5601089 := bstep (se 2 (by rfl) ⟨2100408, by rfl⟩ : syracuseStep 5601089 = 4200817) B4200817
theorem B14936237 : Blo 1965435 14936237 := bstep (se 3 (by rfl) ⟨2800544, by rfl⟩ : syracuseStep 14936237 = 5601089) B5601089
theorem B9957491 : Blo 1965435 9957491 := bstep (se 1 (by rfl) ⟨7468118, by rfl⟩ : syracuseStep 9957491 = 14936237) B14936237
theorem B6638327 : Blo 1965435 6638327 := bstep (se 1 (by rfl) ⟨4978745, by rfl⟩ : syracuseStep 6638327 = 9957491) B9957491
theorem B4425551 : Blo 1965435 4425551 := bstep (se 1 (by rfl) ⟨3319163, by rfl⟩ : syracuseStep 4425551 = 6638327) B6638327
theorem B2950367 : Blo 1965435 2950367 := bstep (se 1 (by rfl) ⟨2212775, by rfl⟩ : syracuseStep 2950367 = 4425551) B4425551
theorem B1966911 : Blo 1965435 1966911 := bstep (se 1 (by rfl) ⟨1475183, by rfl⟩ : syracuseStep 1966911 = 2950367) B2950367
theorem B2950373 : Blo 1965435 2950373 := bbase (se 4 (by rfl) ⟨276597, by rfl⟩ : syracuseStep 2950373 = 553195) (by norm_num)
theorem B1966915 : Blo 1965435 1966915 := bstep (se 1 (by rfl) ⟨1475186, by rfl⟩ : syracuseStep 1966915 = 2950373) B2950373
theorem B6301253 : Blo 1965435 6301253 := bbase (se 4 (by rfl) ⟨590742, by rfl⟩ : syracuseStep 6301253 = 1181485) (by norm_num)
theorem B4200835 : Blo 1965435 4200835 := bstep (se 1 (by rfl) ⟨3150626, by rfl⟩ : syracuseStep 4200835 = 6301253) B6301253
theorem B5601113 : Blo 1965435 5601113 := bstep (se 2 (by rfl) ⟨2100417, by rfl⟩ : syracuseStep 5601113 = 4200835) B4200835
theorem B3734075 : Blo 1965435 3734075 := bstep (se 1 (by rfl) ⟨2800556, by rfl⟩ : syracuseStep 3734075 = 5601113) B5601113
theorem B2489383 : Blo 1965435 2489383 := bstep (se 1 (by rfl) ⟨1867037, by rfl⟩ : syracuseStep 2489383 = 3734075) B3734075
theorem B3319177 : Blo 1965435 3319177 := bstep (se 2 (by rfl) ⟨1244691, by rfl⟩ : syracuseStep 3319177 = 2489383) B2489383
theorem B4425569 : Blo 1965435 4425569 := bstep (se 2 (by rfl) ⟨1659588, by rfl⟩ : syracuseStep 4425569 = 3319177) B3319177
theorem B2950379 : Blo 1965435 2950379 := bstep (se 1 (by rfl) ⟨2212784, by rfl⟩ : syracuseStep 2950379 = 4425569) B4425569
theorem B1966919 : Blo 1965435 1966919 := bstep (se 1 (by rfl) ⟨1475189, by rfl⟩ : syracuseStep 1966919 = 2950379) B2950379
theorem B2212789 : Blo 1965435 2212789 := bbase (se 5 (by rfl) ⟨103724, by rfl⟩ : syracuseStep 2212789 = 207449) (by norm_num)
theorem B2950385 : Blo 1965435 2950385 := bstep (se 2 (by rfl) ⟨1106394, by rfl⟩ : syracuseStep 2950385 = 2212789) B2212789
theorem B1966923 : Blo 1965435 1966923 := bstep (se 1 (by rfl) ⟨1475192, by rfl⟩ : syracuseStep 1966923 = 2950385) B2950385
theorem B2489393 : Blo 1965435 2489393 := bbase (se 2 (by rfl) ⟨933522, by rfl⟩ : syracuseStep 2489393 = 1867045) (by norm_num)
theorem B6638381 : Blo 1965435 6638381 := bstep (se 3 (by rfl) ⟨1244696, by rfl⟩ : syracuseStep 6638381 = 2489393) B2489393
theorem B4425587 : Blo 1965435 4425587 := bstep (se 1 (by rfl) ⟨3319190, by rfl⟩ : syracuseStep 4425587 = 6638381) B6638381
theorem B2950391 : Blo 1965435 2950391 := bstep (se 1 (by rfl) ⟨2212793, by rfl⟩ : syracuseStep 2950391 = 4425587) B4425587
theorem B1966927 : Blo 1965435 1966927 := bstep (se 1 (by rfl) ⟨1475195, by rfl⟩ : syracuseStep 1966927 = 2950391) B2950391
theorem B2950397 : Blo 1965435 2950397 := bbase (se 3 (by rfl) ⟨553199, by rfl⟩ : syracuseStep 2950397 = 1106399) (by norm_num)
theorem B1966931 : Blo 1965435 1966931 := bstep (se 1 (by rfl) ⟨1475198, by rfl⟩ : syracuseStep 1966931 = 2950397) B2950397
theorem B4425605 : Blo 1965435 4425605 := bbase (se 4 (by rfl) ⟨414900, by rfl⟩ : syracuseStep 4425605 = 829801) (by norm_num)
theorem B2950403 : Blo 1965435 2950403 := bstep (se 1 (by rfl) ⟨2212802, by rfl⟩ : syracuseStep 2950403 = 4425605) B4425605
theorem B1966935 : Blo 1965435 1966935 := bstep (se 1 (by rfl) ⟨1475201, by rfl⟩ : syracuseStep 1966935 = 2950403) B2950403
theorem B4725989 : Blo 1965435 4725989 := bbase (se 4 (by rfl) ⟨443061, by rfl⟩ : syracuseStep 4725989 = 886123) (by norm_num)
theorem B3150659 : Blo 1965435 3150659 := bstep (se 1 (by rfl) ⟨2362994, by rfl⟩ : syracuseStep 3150659 = 4725989) B4725989
theorem B2100439 : Blo 1965435 2100439 := bstep (se 1 (by rfl) ⟨1575329, by rfl⟩ : syracuseStep 2100439 = 3150659) B3150659
theorem B2800585 : Blo 1965435 2800585 := bstep (se 2 (by rfl) ⟨1050219, by rfl⟩ : syracuseStep 2800585 = 2100439) B2100439
theorem B3734113 : Blo 1965435 3734113 := bstep (se 2 (by rfl) ⟨1400292, by rfl⟩ : syracuseStep 3734113 = 2800585) B2800585
theorem B4978817 : Blo 1965435 4978817 := bstep (se 2 (by rfl) ⟨1867056, by rfl⟩ : syracuseStep 4978817 = 3734113) B3734113
theorem B3319211 : Blo 1965435 3319211 := bstep (se 1 (by rfl) ⟨2489408, by rfl⟩ : syracuseStep 3319211 = 4978817) B4978817
theorem B2212807 : Blo 1965435 2212807 := bstep (se 1 (by rfl) ⟨1659605, by rfl⟩ : syracuseStep 2212807 = 3319211) B3319211
theorem B2950409 : Blo 1965435 2950409 := bstep (se 2 (by rfl) ⟨1106403, by rfl⟩ : syracuseStep 2950409 = 2212807) B2212807
theorem B1966939 : Blo 1965435 1966939 := bstep (se 1 (by rfl) ⟨1475204, by rfl⟩ : syracuseStep 1966939 = 2950409) B2950409
theorem B9957653 : Blo 1965435 9957653 := bbase (se 6 (by rfl) ⟨233382, by rfl⟩ : syracuseStep 9957653 = 466765) (by norm_num)
theorem B6638435 : Blo 1965435 6638435 := bstep (se 1 (by rfl) ⟨4978826, by rfl⟩ : syracuseStep 6638435 = 9957653) B9957653
theorem B4425623 : Blo 1965435 4425623 := bstep (se 1 (by rfl) ⟨3319217, by rfl⟩ : syracuseStep 4425623 = 6638435) B6638435
theorem B2950415 : Blo 1965435 2950415 := bstep (se 1 (by rfl) ⟨2212811, by rfl⟩ : syracuseStep 2950415 = 4425623) B4425623
theorem B1966943 : Blo 1965435 1966943 := bstep (se 1 (by rfl) ⟨1475207, by rfl⟩ : syracuseStep 1966943 = 2950415) B2950415
theorem B2950421 : Blo 1965435 2950421 := bbase (se 6 (by rfl) ⟨69150, by rfl⟩ : syracuseStep 2950421 = 138301) (by norm_num)
theorem B1966947 : Blo 1965435 1966947 := bstep (se 1 (by rfl) ⟨1475210, by rfl⟩ : syracuseStep 1966947 = 2950421) B2950421
theorem B2158157 : Blo 1965435 2158157 := bbase (se 3 (by rfl) ⟨404654, by rfl⟩ : syracuseStep 2158157 = 809309) (by norm_num)
theorem B5755085 : Blo 1965435 5755085 := bstep (se 3 (by rfl) ⟨1079078, by rfl⟩ : syracuseStep 5755085 = 2158157) B2158157
theorem B3836723 : Blo 1965435 3836723 := bstep (se 1 (by rfl) ⟨2877542, by rfl⟩ : syracuseStep 3836723 = 5755085) B5755085
theorem B10231261 : Blo 1965435 10231261 := bstep (se 3 (by rfl) ⟨1918361, by rfl⟩ : syracuseStep 10231261 = 3836723) B3836723
theorem B54566725 : Blo 1965435 54566725 := bstep (se 4 (by rfl) ⟨5115630, by rfl⟩ : syracuseStep 54566725 = 10231261) B10231261
theorem B72755633 : Blo 1965435 72755633 := bstep (se 2 (by rfl) ⟨27283362, by rfl⟩ : syracuseStep 72755633 = 54566725) B54566725
theorem B48503755 : Blo 1965435 48503755 := bstep (se 1 (by rfl) ⟨36377816, by rfl⟩ : syracuseStep 48503755 = 72755633) B72755633
theorem B258686693 : Blo 1965435 258686693 := bstep (se 4 (by rfl) ⟨24251877, by rfl⟩ : syracuseStep 258686693 = 48503755) B48503755
theorem B172457795 : Blo 1965435 172457795 := bstep (se 1 (by rfl) ⟨129343346, by rfl⟩ : syracuseStep 172457795 = 258686693) B258686693
theorem B459887453 : Blo 1965435 459887453 := bstep (se 3 (by rfl) ⟨86228897, by rfl⟩ : syracuseStep 459887453 = 172457795) B172457795
theorem B306591635 : Blo 1965435 306591635 := bstep (se 1 (by rfl) ⟨229943726, by rfl⟩ : syracuseStep 306591635 = 459887453) B459887453
theorem B204394423 : Blo 1965435 204394423 := bstep (se 1 (by rfl) ⟨153295817, by rfl⟩ : syracuseStep 204394423 = 306591635) B306591635
theorem B272525897 : Blo 1965435 272525897 := bstep (se 2 (by rfl) ⟨102197211, by rfl⟩ : syracuseStep 272525897 = 204394423) B204394423
theorem B726735725 : Blo 1965435 726735725 := bstep (se 3 (by rfl) ⟨136262948, by rfl⟩ : syracuseStep 726735725 = 272525897) B272525897
theorem B484490483 : Blo 1965435 484490483 := bstep (se 1 (by rfl) ⟨363367862, by rfl⟩ : syracuseStep 484490483 = 726735725) B726735725
theorem B322993655 : Blo 1965435 322993655 := bstep (se 1 (by rfl) ⟨242245241, by rfl⟩ : syracuseStep 322993655 = 484490483) B484490483
theorem B215329103 : Blo 1965435 215329103 := bstep (se 1 (by rfl) ⟨161496827, by rfl⟩ : syracuseStep 215329103 = 322993655) B322993655
theorem B143552735 : Blo 1965435 143552735 := bstep (se 1 (by rfl) ⟨107664551, by rfl⟩ : syracuseStep 143552735 = 215329103) B215329103
theorem B95701823 : Blo 1965435 95701823 := bstep (se 1 (by rfl) ⟨71776367, by rfl⟩ : syracuseStep 95701823 = 143552735) B143552735
theorem B63801215 : Blo 1965435 63801215 := bstep (se 1 (by rfl) ⟨47850911, by rfl⟩ : syracuseStep 63801215 = 95701823) B95701823
theorem B42534143 : Blo 1965435 42534143 := bstep (se 1 (by rfl) ⟨31900607, by rfl⟩ : syracuseStep 42534143 = 63801215) B63801215
theorem B28356095 : Blo 1965435 28356095 := bstep (se 1 (by rfl) ⟨21267071, by rfl⟩ : syracuseStep 28356095 = 42534143) B42534143
theorem B18904063 : Blo 1965435 18904063 := bstep (se 1 (by rfl) ⟨14178047, by rfl⟩ : syracuseStep 18904063 = 28356095) B28356095
theorem B25205417 : Blo 1965435 25205417 := bstep (se 2 (by rfl) ⟨9452031, by rfl⟩ : syracuseStep 25205417 = 18904063) B18904063
theorem B16803611 : Blo 1965435 16803611 := bstep (se 1 (by rfl) ⟨12602708, by rfl⟩ : syracuseStep 16803611 = 25205417) B25205417
theorem B11202407 : Blo 1965435 11202407 := bstep (se 1 (by rfl) ⟨8401805, by rfl⟩ : syracuseStep 11202407 = 16803611) B16803611
theorem B7468271 : Blo 1965435 7468271 := bstep (se 1 (by rfl) ⟨5601203, by rfl⟩ : syracuseStep 7468271 = 11202407) B11202407
theorem B4978847 : Blo 1965435 4978847 := bstep (se 1 (by rfl) ⟨3734135, by rfl⟩ : syracuseStep 4978847 = 7468271) B7468271
theorem B3319231 : Blo 1965435 3319231 := bstep (se 1 (by rfl) ⟨2489423, by rfl⟩ : syracuseStep 3319231 = 4978847) B4978847
theorem B4425641 : Blo 1965435 4425641 := bstep (se 2 (by rfl) ⟨1659615, by rfl⟩ : syracuseStep 4425641 = 3319231) B3319231
theorem B2950427 : Blo 1965435 2950427 := bstep (se 1 (by rfl) ⟨2212820, by rfl⟩ : syracuseStep 2950427 = 4425641) B4425641
theorem B1966951 : Blo 1965435 1966951 := bstep (se 1 (by rfl) ⟨1475213, by rfl⟩ : syracuseStep 1966951 = 2950427) B2950427
theorem B2212825 : Blo 1965435 2212825 := bbase (se 2 (by rfl) ⟨829809, by rfl⟩ : syracuseStep 2212825 = 1659619) (by norm_num)
theorem B2950433 : Blo 1965435 2950433 := bstep (se 2 (by rfl) ⟨1106412, by rfl⟩ : syracuseStep 2950433 = 2212825) B2212825
theorem B1966955 : Blo 1965435 1966955 := bstep (se 1 (by rfl) ⟨1475216, by rfl⟩ : syracuseStep 1966955 = 2950433) B2950433
theorem B2800613 : Blo 1965435 2800613 := bbase (se 4 (by rfl) ⟨262557, by rfl⟩ : syracuseStep 2800613 = 525115) (by norm_num)
theorem B7468301 : Blo 1965435 7468301 := bstep (se 3 (by rfl) ⟨1400306, by rfl⟩ : syracuseStep 7468301 = 2800613) B2800613
theorem B4978867 : Blo 1965435 4978867 := bstep (se 1 (by rfl) ⟨3734150, by rfl⟩ : syracuseStep 4978867 = 7468301) B7468301
theorem B6638489 : Blo 1965435 6638489 := bstep (se 2 (by rfl) ⟨2489433, by rfl⟩ : syracuseStep 6638489 = 4978867) B4978867
theorem B4425659 : Blo 1965435 4425659 := bstep (se 1 (by rfl) ⟨3319244, by rfl⟩ : syracuseStep 4425659 = 6638489) B6638489
theorem B2950439 : Blo 1965435 2950439 := bstep (se 1 (by rfl) ⟨2212829, by rfl⟩ : syracuseStep 2950439 = 4425659) B4425659
theorem B1966959 : Blo 1965435 1966959 := bstep (se 1 (by rfl) ⟨1475219, by rfl⟩ : syracuseStep 1966959 = 2950439) B2950439
theorem B2950445 : Blo 1965435 2950445 := bbase (se 3 (by rfl) ⟨553208, by rfl⟩ : syracuseStep 2950445 = 1106417) (by norm_num)
theorem B1966963 : Blo 1965435 1966963 := bstep (se 1 (by rfl) ⟨1475222, by rfl⟩ : syracuseStep 1966963 = 2950445) B2950445
theorem B4425677 : Blo 1965435 4425677 := bbase (se 3 (by rfl) ⟨829814, by rfl⟩ : syracuseStep 4425677 = 1659629) (by norm_num)
theorem B2950451 : Blo 1965435 2950451 := bstep (se 1 (by rfl) ⟨2212838, by rfl⟩ : syracuseStep 2950451 = 4425677) B4425677
theorem B1966967 : Blo 1965435 1966967 := bstep (se 1 (by rfl) ⟨1475225, by rfl⟩ : syracuseStep 1966967 = 2950451) B2950451
theorem B2489449 : Blo 1965435 2489449 := bbase (se 2 (by rfl) ⟨933543, by rfl⟩ : syracuseStep 2489449 = 1867087) (by norm_num)
theorem B3319265 : Blo 1965435 3319265 := bstep (se 2 (by rfl) ⟨1244724, by rfl⟩ : syracuseStep 3319265 = 2489449) B2489449
theorem B2212843 : Blo 1965435 2212843 := bstep (se 1 (by rfl) ⟨1659632, by rfl⟩ : syracuseStep 2212843 = 3319265) B3319265
theorem B2950457 : Blo 1965435 2950457 := bstep (se 2 (by rfl) ⟨1106421, by rfl⟩ : syracuseStep 2950457 = 2212843) B2212843
theorem B1966971 : Blo 1965435 1966971 := bstep (se 1 (by rfl) ⟨1475228, by rfl⟩ : syracuseStep 1966971 = 2950457) B2950457
theorem B12949109 : Blo 1965435 12949109 := bbase (se 5 (by rfl) ⟨606989, by rfl⟩ : syracuseStep 12949109 = 1213979) (by norm_num)
theorem B8632739 : Blo 1965435 8632739 := bstep (se 1 (by rfl) ⟨6474554, by rfl⟩ : syracuseStep 8632739 = 12949109) B12949109
theorem B5755159 : Blo 1965435 5755159 := bstep (se 1 (by rfl) ⟨4316369, by rfl⟩ : syracuseStep 5755159 = 8632739) B8632739
theorem B7673545 : Blo 1965435 7673545 := bstep (se 2 (by rfl) ⟨2877579, by rfl⟩ : syracuseStep 7673545 = 5755159) B5755159
theorem B10231393 : Blo 1965435 10231393 := bstep (se 2 (by rfl) ⟨3836772, by rfl⟩ : syracuseStep 10231393 = 7673545) B7673545
theorem B13641857 : Blo 1965435 13641857 := bstep (se 2 (by rfl) ⟨5115696, by rfl⟩ : syracuseStep 13641857 = 10231393) B10231393
theorem B9094571 : Blo 1965435 9094571 := bstep (se 1 (by rfl) ⟨6820928, by rfl⟩ : syracuseStep 9094571 = 13641857) B13641857
theorem B6063047 : Blo 1965435 6063047 := bstep (se 1 (by rfl) ⟨4547285, by rfl⟩ : syracuseStep 6063047 = 9094571) B9094571
theorem B4042031 : Blo 1965435 4042031 := bstep (se 1 (by rfl) ⟨3031523, by rfl⟩ : syracuseStep 4042031 = 6063047) B6063047
theorem B43114997 : Blo 1965435 43114997 := bstep (se 5 (by rfl) ⟨2021015, by rfl⟩ : syracuseStep 43114997 = 4042031) B4042031
theorem B28743331 : Blo 1965435 28743331 := bstep (se 1 (by rfl) ⟨21557498, by rfl⟩ : syracuseStep 28743331 = 43114997) B43114997
theorem B38324441 : Blo 1965435 38324441 := bstep (se 2 (by rfl) ⟨14371665, by rfl⟩ : syracuseStep 38324441 = 28743331) B28743331
theorem B25549627 : Blo 1965435 25549627 := bstep (se 1 (by rfl) ⟨19162220, by rfl⟩ : syracuseStep 25549627 = 38324441) B38324441
theorem B34066169 : Blo 1965435 34066169 := bstep (se 2 (by rfl) ⟨12774813, by rfl⟩ : syracuseStep 34066169 = 25549627) B25549627
theorem B22710779 : Blo 1965435 22710779 := bstep (se 1 (by rfl) ⟨17033084, by rfl⟩ : syracuseStep 22710779 = 34066169) B34066169
theorem B15140519 : Blo 1965435 15140519 := bstep (se 1 (by rfl) ⟨11355389, by rfl⟩ : syracuseStep 15140519 = 22710779) B22710779
theorem B10093679 : Blo 1965435 10093679 := bstep (se 1 (by rfl) ⟨7570259, by rfl⟩ : syracuseStep 10093679 = 15140519) B15140519
theorem B6729119 : Blo 1965435 6729119 := bstep (se 1 (by rfl) ⟨5046839, by rfl⟩ : syracuseStep 6729119 = 10093679) B10093679
theorem B4486079 : Blo 1965435 4486079 := bstep (se 1 (by rfl) ⟨3364559, by rfl⟩ : syracuseStep 4486079 = 6729119) B6729119
theorem B2990719 : Blo 1965435 2990719 := bstep (se 1 (by rfl) ⟨2243039, by rfl⟩ : syracuseStep 2990719 = 4486079) B4486079
theorem B3987625 : Blo 1965435 3987625 := bstep (se 2 (by rfl) ⟨1495359, by rfl⟩ : syracuseStep 3987625 = 2990719) B2990719
theorem B5316833 : Blo 1965435 5316833 := bstep (se 2 (by rfl) ⟨1993812, by rfl⟩ : syracuseStep 5316833 = 3987625) B3987625
theorem B3544555 : Blo 1965435 3544555 := bstep (se 1 (by rfl) ⟨2658416, by rfl⟩ : syracuseStep 3544555 = 5316833) B5316833
theorem B4726073 : Blo 1965435 4726073 := bstep (se 2 (by rfl) ⟨1772277, by rfl⟩ : syracuseStep 4726073 = 3544555) B3544555
theorem B12602861 : Blo 1965435 12602861 := bstep (se 3 (by rfl) ⟨2363036, by rfl⟩ : syracuseStep 12602861 = 4726073) B4726073
theorem B8401907 : Blo 1965435 8401907 := bstep (se 1 (by rfl) ⟨6301430, by rfl⟩ : syracuseStep 8401907 = 12602861) B12602861
theorem B22405085 : Blo 1965435 22405085 := bstep (se 3 (by rfl) ⟨4200953, by rfl⟩ : syracuseStep 22405085 = 8401907) B8401907
theorem B14936723 : Blo 1965435 14936723 := bstep (se 1 (by rfl) ⟨11202542, by rfl⟩ : syracuseStep 14936723 = 22405085) B22405085
theorem B9957815 : Blo 1965435 9957815 := bstep (se 1 (by rfl) ⟨7468361, by rfl⟩ : syracuseStep 9957815 = 14936723) B14936723
theorem B6638543 : Blo 1965435 6638543 := bstep (se 1 (by rfl) ⟨4978907, by rfl⟩ : syracuseStep 6638543 = 9957815) B9957815
theorem B4425695 : Blo 1965435 4425695 := bstep (se 1 (by rfl) ⟨3319271, by rfl⟩ : syracuseStep 4425695 = 6638543) B6638543
theorem B2950463 : Blo 1965435 2950463 := bstep (se 1 (by rfl) ⟨2212847, by rfl⟩ : syracuseStep 2950463 = 4425695) B4425695
theorem B1966975 : Blo 1965435 1966975 := bstep (se 1 (by rfl) ⟨1475231, by rfl⟩ : syracuseStep 1966975 = 2950463) B2950463
theorem B2950469 : Blo 1965435 2950469 := bbase (se 4 (by rfl) ⟨276606, by rfl⟩ : syracuseStep 2950469 = 553213) (by norm_num)
theorem B1966979 : Blo 1965435 1966979 := bstep (se 1 (by rfl) ⟨1475234, by rfl⟩ : syracuseStep 1966979 = 2950469) B2950469
theorem B3319285 : Blo 1965435 3319285 := bbase (se 5 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 3319285 = 311183) (by norm_num)
theorem B4425713 : Blo 1965435 4425713 := bstep (se 2 (by rfl) ⟨1659642, by rfl⟩ : syracuseStep 4425713 = 3319285) B3319285
theorem B2950475 : Blo 1965435 2950475 := bstep (se 1 (by rfl) ⟨2212856, by rfl⟩ : syracuseStep 2950475 = 4425713) B4425713
theorem B1966983 : Blo 1965435 1966983 := bstep (se 1 (by rfl) ⟨1475237, by rfl⟩ : syracuseStep 1966983 = 2950475) B2950475
theorem B2212861 : Blo 1965435 2212861 := bbase (se 3 (by rfl) ⟨414911, by rfl⟩ : syracuseStep 2212861 = 829823) (by norm_num)
theorem B2950481 : Blo 1965435 2950481 := bstep (se 2 (by rfl) ⟨1106430, by rfl⟩ : syracuseStep 2950481 = 2212861) B2212861
theorem B1966987 : Blo 1965435 1966987 := bstep (se 1 (by rfl) ⟨1475240, by rfl⟩ : syracuseStep 1966987 = 2950481) B2950481
theorem B6638597 : Blo 1965435 6638597 := bbase (se 4 (by rfl) ⟨622368, by rfl⟩ : syracuseStep 6638597 = 1244737) (by norm_num)
theorem B4425731 : Blo 1965435 4425731 := bstep (se 1 (by rfl) ⟨3319298, by rfl⟩ : syracuseStep 4425731 = 6638597) B6638597
theorem B2950487 : Blo 1965435 2950487 := bstep (se 1 (by rfl) ⟨2212865, by rfl⟩ : syracuseStep 2950487 = 4425731) B4425731
theorem B1966991 : Blo 1965435 1966991 := bstep (se 1 (by rfl) ⟨1475243, by rfl⟩ : syracuseStep 1966991 = 2950487) B2950487
theorem B2950493 : Blo 1965435 2950493 := bbase (se 3 (by rfl) ⟨553217, by rfl⟩ : syracuseStep 2950493 = 1106435) (by norm_num)
theorem B1966995 : Blo 1965435 1966995 := bstep (se 1 (by rfl) ⟨1475246, by rfl⟩ : syracuseStep 1966995 = 2950493) B2950493
theorem B4425749 : Blo 1965435 4425749 := bbase (se 6 (by rfl) ⟨103728, by rfl⟩ : syracuseStep 4425749 = 207457) (by norm_num)
theorem B2950499 : Blo 1965435 2950499 := bstep (se 1 (by rfl) ⟨2212874, by rfl⟩ : syracuseStep 2950499 = 4425749) B4425749
theorem B1966999 : Blo 1965435 1966999 := bstep (se 1 (by rfl) ⟨1475249, by rfl⟩ : syracuseStep 1966999 = 2950499) B2950499
theorem B7468469 : Blo 1965435 7468469 := bbase (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) (by norm_num)
theorem B4978979 : Blo 1965435 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B3319319 : Blo 1965435 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B2212879 : Blo 1965435 2212879 := bstep (se 1 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 2212879 = 3319319) B3319319
theorem B2950505 : Blo 1965435 2950505 := bstep (se 2 (by rfl) ⟨1106439, by rfl⟩ : syracuseStep 2950505 = 2212879) B2212879
theorem B1967003 : Blo 1965435 1967003 := bstep (se 1 (by rfl) ⟨1475252, by rfl⟩ : syracuseStep 1967003 = 2950505) B2950505
theorem B7975381 : Blo 1965435 7975381 := bbase (se 7 (by rfl) ⟨93461, by rfl⟩ : syracuseStep 7975381 = 186923) (by norm_num)
theorem B10633841 : Blo 1965435 10633841 := bstep (se 2 (by rfl) ⟨3987690, by rfl⟩ : syracuseStep 10633841 = 7975381) B7975381
theorem B7089227 : Blo 1965435 7089227 := bstep (se 1 (by rfl) ⟨5316920, by rfl⟩ : syracuseStep 7089227 = 10633841) B10633841
theorem B4726151 : Blo 1965435 4726151 := bstep (se 1 (by rfl) ⟨3544613, by rfl⟩ : syracuseStep 4726151 = 7089227) B7089227
theorem B3150767 : Blo 1965435 3150767 := bstep (se 1 (by rfl) ⟨2363075, by rfl⟩ : syracuseStep 3150767 = 4726151) B4726151
theorem B2100511 : Blo 1965435 2100511 := bstep (se 1 (by rfl) ⟨1575383, by rfl⟩ : syracuseStep 2100511 = 3150767) B3150767
theorem B11202725 : Blo 1965435 11202725 := bstep (se 4 (by rfl) ⟨1050255, by rfl⟩ : syracuseStep 11202725 = 2100511) B2100511
theorem B7468483 : Blo 1965435 7468483 := bstep (se 1 (by rfl) ⟨5601362, by rfl⟩ : syracuseStep 7468483 = 11202725) B11202725
theorem B9957977 : Blo 1965435 9957977 := bstep (se 2 (by rfl) ⟨3734241, by rfl⟩ : syracuseStep 9957977 = 7468483) B7468483
theorem B6638651 : Blo 1965435 6638651 := bstep (se 1 (by rfl) ⟨4978988, by rfl⟩ : syracuseStep 6638651 = 9957977) B9957977
theorem B4425767 : Blo 1965435 4425767 := bstep (se 1 (by rfl) ⟨3319325, by rfl⟩ : syracuseStep 4425767 = 6638651) B6638651
theorem B2950511 : Blo 1965435 2950511 := bstep (se 1 (by rfl) ⟨2212883, by rfl⟩ : syracuseStep 2950511 = 4425767) B4425767
theorem B1967007 : Blo 1965435 1967007 := bstep (se 1 (by rfl) ⟨1475255, by rfl⟩ : syracuseStep 1967007 = 2950511) B2950511
theorem B2950517 : Blo 1965435 2950517 := bbase (se 5 (by rfl) ⟨138305, by rfl⟩ : syracuseStep 2950517 = 276611) (by norm_num)
theorem B1967011 : Blo 1965435 1967011 := bstep (se 1 (by rfl) ⟨1475258, by rfl⟩ : syracuseStep 1967011 = 2950517) B2950517
theorem B2800693 : Blo 1965435 2800693 := bbase (se 5 (by rfl) ⟨131282, by rfl⟩ : syracuseStep 2800693 = 262565) (by norm_num)
theorem B3734257 : Blo 1965435 3734257 := bstep (se 2 (by rfl) ⟨1400346, by rfl⟩ : syracuseStep 3734257 = 2800693) B2800693
theorem B4979009 : Blo 1965435 4979009 := bstep (se 2 (by rfl) ⟨1867128, by rfl⟩ : syracuseStep 4979009 = 3734257) B3734257
theorem B3319339 : Blo 1965435 3319339 := bstep (se 1 (by rfl) ⟨2489504, by rfl⟩ : syracuseStep 3319339 = 4979009) B4979009
theorem B4425785 : Blo 1965435 4425785 := bstep (se 2 (by rfl) ⟨1659669, by rfl⟩ : syracuseStep 4425785 = 3319339) B3319339
theorem B2950523 : Blo 1965435 2950523 := bstep (se 1 (by rfl) ⟨2212892, by rfl⟩ : syracuseStep 2950523 = 4425785) B4425785
theorem B1967015 : Blo 1965435 1967015 := bstep (se 1 (by rfl) ⟨1475261, by rfl⟩ : syracuseStep 1967015 = 2950523) B2950523
theorem B2212897 : Blo 1965435 2212897 := bbase (se 2 (by rfl) ⟨829836, by rfl⟩ : syracuseStep 2212897 = 1659673) (by norm_num)
theorem B2950529 : Blo 1965435 2950529 := bstep (se 2 (by rfl) ⟨1106448, by rfl⟩ : syracuseStep 2950529 = 2212897) B2212897
theorem B1967019 : Blo 1965435 1967019 := bstep (se 1 (by rfl) ⟨1475264, by rfl⟩ : syracuseStep 1967019 = 2950529) B2950529
theorem B4979029 : Blo 1965435 4979029 := bbase (se 10 (by rfl) ⟨7293, by rfl⟩ : syracuseStep 4979029 = 14587) (by norm_num)
theorem B6638705 : Blo 1965435 6638705 := bstep (se 2 (by rfl) ⟨2489514, by rfl⟩ : syracuseStep 6638705 = 4979029) B4979029
theorem B4425803 : Blo 1965435 4425803 := bstep (se 1 (by rfl) ⟨3319352, by rfl⟩ : syracuseStep 4425803 = 6638705) B6638705
theorem B2950535 : Blo 1965435 2950535 := bstep (se 1 (by rfl) ⟨2212901, by rfl⟩ : syracuseStep 2950535 = 4425803) B4425803
theorem B1967023 : Blo 1965435 1967023 := bstep (se 1 (by rfl) ⟨1475267, by rfl⟩ : syracuseStep 1967023 = 2950535) B2950535
theorem B2950541 : Blo 1965435 2950541 := bbase (se 3 (by rfl) ⟨553226, by rfl⟩ : syracuseStep 2950541 = 1106453) (by norm_num)
theorem B1967027 : Blo 1965435 1967027 := bstep (se 1 (by rfl) ⟨1475270, by rfl⟩ : syracuseStep 1967027 = 2950541) B2950541
theorem B4425821 : Blo 1965435 4425821 := bbase (se 3 (by rfl) ⟨829841, by rfl⟩ : syracuseStep 4425821 = 1659683) (by norm_num)
theorem B2950547 : Blo 1965435 2950547 := bstep (se 1 (by rfl) ⟨2212910, by rfl⟩ : syracuseStep 2950547 = 4425821) B4425821
theorem B1967031 : Blo 1965435 1967031 := bstep (se 1 (by rfl) ⟨1475273, by rfl⟩ : syracuseStep 1967031 = 2950547) B2950547
theorem B3319373 : Blo 1965435 3319373 := bbase (se 3 (by rfl) ⟨622382, by rfl⟩ : syracuseStep 3319373 = 1244765) (by norm_num)
theorem B2212915 : Blo 1965435 2212915 := bstep (se 1 (by rfl) ⟨1659686, by rfl⟩ : syracuseStep 2212915 = 3319373) B3319373
theorem B2950553 : Blo 1965435 2950553 := bstep (se 2 (by rfl) ⟨1106457, by rfl⟩ : syracuseStep 2950553 = 2212915) B2212915
theorem B1967035 : Blo 1965435 1967035 := bstep (se 1 (by rfl) ⟨1475276, by rfl⟩ : syracuseStep 1967035 = 2950553) B2950553
theorem B1993877 : Blo 1965435 1993877 := bbase (se 6 (by rfl) ⟨46731, by rfl⟩ : syracuseStep 1993877 = 93463) (by norm_num)
theorem B21268021 : Blo 1965435 21268021 := bstep (se 5 (by rfl) ⟨996938, by rfl⟩ : syracuseStep 21268021 = 1993877) B1993877
theorem B28357361 : Blo 1965435 28357361 := bstep (se 2 (by rfl) ⟨10634010, by rfl⟩ : syracuseStep 28357361 = 21268021) B21268021
theorem B18904907 : Blo 1965435 18904907 := bstep (se 1 (by rfl) ⟨14178680, by rfl⟩ : syracuseStep 18904907 = 28357361) B28357361
theorem B12603271 : Blo 1965435 12603271 := bstep (se 1 (by rfl) ⟨9452453, by rfl⟩ : syracuseStep 12603271 = 18904907) B18904907
theorem B16804361 : Blo 1965435 16804361 := bstep (se 2 (by rfl) ⟨6301635, by rfl⟩ : syracuseStep 16804361 = 12603271) B12603271
theorem B11202907 : Blo 1965435 11202907 := bstep (se 1 (by rfl) ⟨8402180, by rfl⟩ : syracuseStep 11202907 = 16804361) B16804361
theorem B14937209 : Blo 1965435 14937209 := bstep (se 2 (by rfl) ⟨5601453, by rfl⟩ : syracuseStep 14937209 = 11202907) B11202907
theorem B9958139 : Blo 1965435 9958139 := bstep (se 1 (by rfl) ⟨7468604, by rfl⟩ : syracuseStep 9958139 = 14937209) B14937209
theorem B6638759 : Blo 1965435 6638759 := bstep (se 1 (by rfl) ⟨4979069, by rfl⟩ : syracuseStep 6638759 = 9958139) B9958139
theorem B4425839 : Blo 1965435 4425839 := bstep (se 1 (by rfl) ⟨3319379, by rfl⟩ : syracuseStep 4425839 = 6638759) B6638759
theorem B2950559 : Blo 1965435 2950559 := bstep (se 1 (by rfl) ⟨2212919, by rfl⟩ : syracuseStep 2950559 = 4425839) B4425839
theorem B1967039 : Blo 1965435 1967039 := bstep (se 1 (by rfl) ⟨1475279, by rfl⟩ : syracuseStep 1967039 = 2950559) B2950559
theorem B2950565 : Blo 1965435 2950565 := bbase (se 4 (by rfl) ⟨276615, by rfl⟩ : syracuseStep 2950565 = 553231) (by norm_num)
theorem B1967043 : Blo 1965435 1967043 := bstep (se 1 (by rfl) ⟨1475282, by rfl⟩ : syracuseStep 1967043 = 2950565) B2950565
theorem B2489545 : Blo 1965435 2489545 := bbase (se 2 (by rfl) ⟨933579, by rfl⟩ : syracuseStep 2489545 = 1867159) (by norm_num)
theorem B3319393 : Blo 1965435 3319393 := bstep (se 2 (by rfl) ⟨1244772, by rfl⟩ : syracuseStep 3319393 = 2489545) B2489545
theorem B4425857 : Blo 1965435 4425857 := bstep (se 2 (by rfl) ⟨1659696, by rfl⟩ : syracuseStep 4425857 = 3319393) B3319393
theorem B2950571 : Blo 1965435 2950571 := bstep (se 1 (by rfl) ⟨2212928, by rfl⟩ : syracuseStep 2950571 = 4425857) B4425857
theorem B1967047 : Blo 1965435 1967047 := bstep (se 1 (by rfl) ⟨1475285, by rfl⟩ : syracuseStep 1967047 = 2950571) B2950571
theorem B2212933 : Blo 1965435 2212933 := bbase (se 4 (by rfl) ⟨207462, by rfl⟩ : syracuseStep 2212933 = 414925) (by norm_num)
theorem B2950577 : Blo 1965435 2950577 := bstep (se 2 (by rfl) ⟨1106466, by rfl⟩ : syracuseStep 2950577 = 2212933) B2212933
theorem B1967051 : Blo 1965435 1967051 := bstep (se 1 (by rfl) ⟨1475288, by rfl⟩ : syracuseStep 1967051 = 2950577) B2950577
theorem B3734333 : Blo 1965435 3734333 := bbase (se 3 (by rfl) ⟨700187, by rfl⟩ : syracuseStep 3734333 = 1400375) (by norm_num)
theorem B2489555 : Blo 1965435 2489555 := bstep (se 1 (by rfl) ⟨1867166, by rfl⟩ : syracuseStep 2489555 = 3734333) B3734333
theorem B6638813 : Blo 1965435 6638813 := bstep (se 3 (by rfl) ⟨1244777, by rfl⟩ : syracuseStep 6638813 = 2489555) B2489555
theorem B4425875 : Blo 1965435 4425875 := bstep (se 1 (by rfl) ⟨3319406, by rfl⟩ : syracuseStep 4425875 = 6638813) B6638813
theorem B2950583 : Blo 1965435 2950583 := bstep (se 1 (by rfl) ⟨2212937, by rfl⟩ : syracuseStep 2950583 = 4425875) B4425875
theorem B1967055 : Blo 1965435 1967055 := bstep (se 1 (by rfl) ⟨1475291, by rfl⟩ : syracuseStep 1967055 = 2950583) B2950583
theorem B2950589 : Blo 1965435 2950589 := bbase (se 3 (by rfl) ⟨553235, by rfl⟩ : syracuseStep 2950589 = 1106471) (by norm_num)
theorem B1967059 : Blo 1965435 1967059 := bstep (se 1 (by rfl) ⟨1475294, by rfl⟩ : syracuseStep 1967059 = 2950589) B2950589
theorem B4425893 : Blo 1965435 4425893 := bbase (se 4 (by rfl) ⟨414927, by rfl⟩ : syracuseStep 4425893 = 829855) (by norm_num)
theorem B2950595 : Blo 1965435 2950595 := bstep (se 1 (by rfl) ⟨2212946, by rfl⟩ : syracuseStep 2950595 = 4425893) B4425893
theorem B1967063 : Blo 1965435 1967063 := bstep (se 1 (by rfl) ⟨1475297, by rfl⟩ : syracuseStep 1967063 = 2950595) B2950595
theorem B4979141 : Blo 1965435 4979141 := bbase (se 4 (by rfl) ⟨466794, by rfl⟩ : syracuseStep 4979141 = 933589) (by norm_num)
theorem B3319427 : Blo 1965435 3319427 := bstep (se 1 (by rfl) ⟨2489570, by rfl⟩ : syracuseStep 3319427 = 4979141) B4979141
theorem B2212951 : Blo 1965435 2212951 := bstep (se 1 (by rfl) ⟨1659713, by rfl⟩ : syracuseStep 2212951 = 3319427) B3319427
theorem B2950601 : Blo 1965435 2950601 := bstep (se 2 (by rfl) ⟨1106475, by rfl⟩ : syracuseStep 2950601 = 2212951) B2212951
theorem B1967067 : Blo 1965435 1967067 := bstep (se 1 (by rfl) ⟨1475300, by rfl⟩ : syracuseStep 1967067 = 2950601) B2950601
theorem B5317093 : Blo 1965435 5317093 := bbase (se 4 (by rfl) ⟨498477, by rfl⟩ : syracuseStep 5317093 = 996955) (by norm_num)
theorem B7089457 : Blo 1965435 7089457 := bstep (se 2 (by rfl) ⟨2658546, by rfl⟩ : syracuseStep 7089457 = 5317093) B5317093
theorem B9452609 : Blo 1965435 9452609 := bstep (se 2 (by rfl) ⟨3544728, by rfl⟩ : syracuseStep 9452609 = 7089457) B7089457
theorem B6301739 : Blo 1965435 6301739 := bstep (se 1 (by rfl) ⟨4726304, by rfl⟩ : syracuseStep 6301739 = 9452609) B9452609
theorem B4201159 : Blo 1965435 4201159 := bstep (se 1 (by rfl) ⟨3150869, by rfl⟩ : syracuseStep 4201159 = 6301739) B6301739
theorem B5601545 : Blo 1965435 5601545 := bstep (se 2 (by rfl) ⟨2100579, by rfl⟩ : syracuseStep 5601545 = 4201159) B4201159
theorem B3734363 : Blo 1965435 3734363 := bstep (se 1 (by rfl) ⟨2800772, by rfl⟩ : syracuseStep 3734363 = 5601545) B5601545
theorem B9958301 : Blo 1965435 9958301 := bstep (se 3 (by rfl) ⟨1867181, by rfl⟩ : syracuseStep 9958301 = 3734363) B3734363
theorem B6638867 : Blo 1965435 6638867 := bstep (se 1 (by rfl) ⟨4979150, by rfl⟩ : syracuseStep 6638867 = 9958301) B9958301
theorem B4425911 : Blo 1965435 4425911 := bstep (se 1 (by rfl) ⟨3319433, by rfl⟩ : syracuseStep 4425911 = 6638867) B6638867
theorem B2950607 : Blo 1965435 2950607 := bstep (se 1 (by rfl) ⟨2212955, by rfl⟩ : syracuseStep 2950607 = 4425911) B4425911
theorem B1967071 : Blo 1965435 1967071 := bstep (se 1 (by rfl) ⟨1475303, by rfl⟩ : syracuseStep 1967071 = 2950607) B2950607
theorem B2950613 : Blo 1965435 2950613 := bbase (se 7 (by rfl) ⟨34577, by rfl⟩ : syracuseStep 2950613 = 69155) (by norm_num)
theorem B1967075 : Blo 1965435 1967075 := bstep (se 1 (by rfl) ⟨1475306, by rfl⟩ : syracuseStep 1967075 = 2950613) B2950613
theorem B7468757 : Blo 1965435 7468757 := bbase (se 7 (by rfl) ⟨87524, by rfl⟩ : syracuseStep 7468757 = 175049) (by norm_num)
theorem B4979171 : Blo 1965435 4979171 := bstep (se 1 (by rfl) ⟨3734378, by rfl⟩ : syracuseStep 4979171 = 7468757) B7468757
theorem B3319447 : Blo 1965435 3319447 := bstep (se 1 (by rfl) ⟨2489585, by rfl⟩ : syracuseStep 3319447 = 4979171) B4979171
theorem B4425929 : Blo 1965435 4425929 := bstep (se 2 (by rfl) ⟨1659723, by rfl⟩ : syracuseStep 4425929 = 3319447) B3319447
theorem B2950619 : Blo 1965435 2950619 := bstep (se 1 (by rfl) ⟨2212964, by rfl⟩ : syracuseStep 2950619 = 4425929) B4425929
theorem B1967079 : Blo 1965435 1967079 := bstep (se 1 (by rfl) ⟨1475309, by rfl⟩ : syracuseStep 1967079 = 2950619) B2950619
theorem B2212969 : Blo 1965435 2212969 := bbase (se 2 (by rfl) ⟨829863, by rfl⟩ : syracuseStep 2212969 = 1659727) (by norm_num)
theorem B2950625 : Blo 1965435 2950625 := bstep (se 2 (by rfl) ⟨1106484, by rfl⟩ : syracuseStep 2950625 = 2212969) B2212969
theorem B1967083 : Blo 1965435 1967083 := bstep (se 1 (by rfl) ⟨1475312, by rfl⟩ : syracuseStep 1967083 = 2950625) B2950625
theorem B2129257 : Blo 1965435 2129257 := bbase (se 2 (by rfl) ⟨798471, by rfl⟩ : syracuseStep 2129257 = 1596943) (by norm_num)
theorem B11356037 : Blo 1965435 11356037 := bstep (se 4 (by rfl) ⟨1064628, by rfl⟩ : syracuseStep 11356037 = 2129257) B2129257
theorem B7570691 : Blo 1965435 7570691 := bstep (se 1 (by rfl) ⟨5678018, by rfl⟩ : syracuseStep 7570691 = 11356037) B11356037
theorem B5047127 : Blo 1965435 5047127 := bstep (se 1 (by rfl) ⟨3785345, by rfl⟩ : syracuseStep 5047127 = 7570691) B7570691
theorem B3364751 : Blo 1965435 3364751 := bstep (se 1 (by rfl) ⟨2523563, by rfl⟩ : syracuseStep 3364751 = 5047127) B5047127
theorem B8972669 : Blo 1965435 8972669 := bstep (se 3 (by rfl) ⟨1682375, by rfl⟩ : syracuseStep 8972669 = 3364751) B3364751
theorem B5981779 : Blo 1965435 5981779 := bstep (se 1 (by rfl) ⟨4486334, by rfl⟩ : syracuseStep 5981779 = 8972669) B8972669
theorem B7975705 : Blo 1965435 7975705 := bstep (se 2 (by rfl) ⟨2990889, by rfl⟩ : syracuseStep 7975705 = 5981779) B5981779
theorem B10634273 : Blo 1965435 10634273 := bstep (se 2 (by rfl) ⟨3987852, by rfl⟩ : syracuseStep 10634273 = 7975705) B7975705
theorem B7089515 : Blo 1965435 7089515 := bstep (se 1 (by rfl) ⟨5317136, by rfl⟩ : syracuseStep 7089515 = 10634273) B10634273
theorem B4726343 : Blo 1965435 4726343 := bstep (se 1 (by rfl) ⟨3544757, by rfl⟩ : syracuseStep 4726343 = 7089515) B7089515
theorem B3150895 : Blo 1965435 3150895 := bstep (se 1 (by rfl) ⟨2363171, by rfl⟩ : syracuseStep 3150895 = 4726343) B4726343
theorem B4201193 : Blo 1965435 4201193 := bstep (se 2 (by rfl) ⟨1575447, by rfl⟩ : syracuseStep 4201193 = 3150895) B3150895
theorem B11203181 : Blo 1965435 11203181 := bstep (se 3 (by rfl) ⟨2100596, by rfl⟩ : syracuseStep 11203181 = 4201193) B4201193
theorem B7468787 : Blo 1965435 7468787 := bstep (se 1 (by rfl) ⟨5601590, by rfl⟩ : syracuseStep 7468787 = 11203181) B11203181
theorem B4979191 : Blo 1965435 4979191 := bstep (se 1 (by rfl) ⟨3734393, by rfl⟩ : syracuseStep 4979191 = 7468787) B7468787
theorem B6638921 : Blo 1965435 6638921 := bstep (se 2 (by rfl) ⟨2489595, by rfl⟩ : syracuseStep 6638921 = 4979191) B4979191
theorem B4425947 : Blo 1965435 4425947 := bstep (se 1 (by rfl) ⟨3319460, by rfl⟩ : syracuseStep 4425947 = 6638921) B6638921
theorem B2950631 : Blo 1965435 2950631 := bstep (se 1 (by rfl) ⟨2212973, by rfl⟩ : syracuseStep 2950631 = 4425947) B4425947
theorem B1967087 : Blo 1965435 1967087 := bstep (se 1 (by rfl) ⟨1475315, by rfl⟩ : syracuseStep 1967087 = 2950631) B2950631
theorem B2950637 : Blo 1965435 2950637 := bbase (se 3 (by rfl) ⟨553244, by rfl⟩ : syracuseStep 2950637 = 1106489) (by norm_num)
theorem B1967091 : Blo 1965435 1967091 := bstep (se 1 (by rfl) ⟨1475318, by rfl⟩ : syracuseStep 1967091 = 2950637) B2950637
theorem B4425965 : Blo 1965435 4425965 := bbase (se 3 (by rfl) ⟨829868, by rfl⟩ : syracuseStep 4425965 = 1659737) (by norm_num)
theorem B2950643 : Blo 1965435 2950643 := bstep (se 1 (by rfl) ⟨2212982, by rfl⟩ : syracuseStep 2950643 = 4425965) B4425965
theorem B1967095 : Blo 1965435 1967095 := bstep (se 1 (by rfl) ⟨1475321, by rfl⟩ : syracuseStep 1967095 = 2950643) B2950643
theorem B2800813 : Blo 1965435 2800813 := bbase (se 3 (by rfl) ⟨525152, by rfl⟩ : syracuseStep 2800813 = 1050305) (by norm_num)
theorem B3734417 : Blo 1965435 3734417 := bstep (se 2 (by rfl) ⟨1400406, by rfl⟩ : syracuseStep 3734417 = 2800813) B2800813
theorem B2489611 : Blo 1965435 2489611 := bstep (se 1 (by rfl) ⟨1867208, by rfl⟩ : syracuseStep 2489611 = 3734417) B3734417
theorem B3319481 : Blo 1965435 3319481 := bstep (se 2 (by rfl) ⟨1244805, by rfl⟩ : syracuseStep 3319481 = 2489611) B2489611
theorem B2212987 : Blo 1965435 2212987 := bstep (se 1 (by rfl) ⟨1659740, by rfl⟩ : syracuseStep 2212987 = 3319481) B3319481
theorem B2950649 : Blo 1965435 2950649 := bstep (se 2 (by rfl) ⟨1106493, by rfl⟩ : syracuseStep 2950649 = 2212987) B2212987
theorem B1967099 : Blo 1965435 1967099 := bstep (se 1 (by rfl) ⟨1475324, by rfl⟩ : syracuseStep 1967099 = 2950649) B2950649
theorem B2658589 : Blo 1965435 2658589 := bbase (se 3 (by rfl) ⟨498485, by rfl⟩ : syracuseStep 2658589 = 996971) (by norm_num)
theorem B14179141 : Blo 1965435 14179141 := bstep (se 4 (by rfl) ⟨1329294, by rfl⟩ : syracuseStep 14179141 = 2658589) B2658589
theorem B75622085 : Blo 1965435 75622085 := bstep (se 4 (by rfl) ⟨7089570, by rfl⟩ : syracuseStep 75622085 = 14179141) B14179141
theorem B50414723 : Blo 1965435 50414723 := bstep (se 1 (by rfl) ⟨37811042, by rfl⟩ : syracuseStep 50414723 = 75622085) B75622085
theorem B33609815 : Blo 1965435 33609815 := bstep (se 1 (by rfl) ⟨25207361, by rfl⟩ : syracuseStep 33609815 = 50414723) B50414723
theorem B22406543 : Blo 1965435 22406543 := bstep (se 1 (by rfl) ⟨16804907, by rfl⟩ : syracuseStep 22406543 = 33609815) B33609815
theorem B14937695 : Blo 1965435 14937695 := bstep (se 1 (by rfl) ⟨11203271, by rfl⟩ : syracuseStep 14937695 = 22406543) B22406543
theorem B9958463 : Blo 1965435 9958463 := bstep (se 1 (by rfl) ⟨7468847, by rfl⟩ : syracuseStep 9958463 = 14937695) B14937695
theorem B6638975 : Blo 1965435 6638975 := bstep (se 1 (by rfl) ⟨4979231, by rfl⟩ : syracuseStep 6638975 = 9958463) B9958463
theorem B4425983 : Blo 1965435 4425983 := bstep (se 1 (by rfl) ⟨3319487, by rfl⟩ : syracuseStep 4425983 = 6638975) B6638975
theorem B2950655 : Blo 1965435 2950655 := bstep (se 1 (by rfl) ⟨2212991, by rfl⟩ : syracuseStep 2950655 = 4425983) B4425983
theorem B1967103 : Blo 1965435 1967103 := bstep (se 1 (by rfl) ⟨1475327, by rfl⟩ : syracuseStep 1967103 = 2950655) B2950655
theorem B2950661 : Blo 1965435 2950661 := bbase (se 4 (by rfl) ⟨276624, by rfl⟩ : syracuseStep 2950661 = 553249) (by norm_num)
theorem B1967107 : Blo 1965435 1967107 := bstep (se 1 (by rfl) ⟨1475330, by rfl⟩ : syracuseStep 1967107 = 2950661) B2950661
theorem B3319501 : Blo 1965435 3319501 := bbase (se 3 (by rfl) ⟨622406, by rfl⟩ : syracuseStep 3319501 = 1244813) (by norm_num)
theorem B4426001 : Blo 1965435 4426001 := bstep (se 2 (by rfl) ⟨1659750, by rfl⟩ : syracuseStep 4426001 = 3319501) B3319501
theorem B2950667 : Blo 1965435 2950667 := bstep (se 1 (by rfl) ⟨2213000, by rfl⟩ : syracuseStep 2950667 = 4426001) B4426001
theorem B1967111 : Blo 1965435 1967111 := bstep (se 1 (by rfl) ⟨1475333, by rfl⟩ : syracuseStep 1967111 = 2950667) B2950667
theorem B2213005 : Blo 1965435 2213005 := bbase (se 3 (by rfl) ⟨414938, by rfl⟩ : syracuseStep 2213005 = 829877) (by norm_num)
theorem B2950673 : Blo 1965435 2950673 := bstep (se 2 (by rfl) ⟨1106502, by rfl⟩ : syracuseStep 2950673 = 2213005) B2213005
theorem B1967115 : Blo 1965435 1967115 := bstep (se 1 (by rfl) ⟨1475336, by rfl⟩ : syracuseStep 1967115 = 2950673) B2950673
theorem B6639029 : Blo 1965435 6639029 := bbase (se 5 (by rfl) ⟨311204, by rfl⟩ : syracuseStep 6639029 = 622409) (by norm_num)
theorem B4426019 : Blo 1965435 4426019 := bstep (se 1 (by rfl) ⟨3319514, by rfl⟩ : syracuseStep 4426019 = 6639029) B6639029
theorem B2950679 : Blo 1965435 2950679 := bstep (se 1 (by rfl) ⟨2213009, by rfl⟩ : syracuseStep 2950679 = 4426019) B4426019
theorem B1967119 : Blo 1965435 1967119 := bstep (se 1 (by rfl) ⟨1475339, by rfl⟩ : syracuseStep 1967119 = 2950679) B2950679
theorem B2950685 : Blo 1965435 2950685 := bbase (se 3 (by rfl) ⟨553253, by rfl⟩ : syracuseStep 2950685 = 1106507) (by norm_num)
theorem B1967123 : Blo 1965435 1967123 := bstep (se 1 (by rfl) ⟨1475342, by rfl⟩ : syracuseStep 1967123 = 2950685) B2950685
theorem B4426037 : Blo 1965435 4426037 := bbase (se 5 (by rfl) ⟨207470, by rfl⟩ : syracuseStep 4426037 = 414941) (by norm_num)
theorem B2950691 : Blo 1965435 2950691 := bstep (se 1 (by rfl) ⟨2213018, by rfl⟩ : syracuseStep 2950691 = 4426037) B4426037
theorem B1967127 : Blo 1965435 1967127 := bstep (se 1 (by rfl) ⟨1475345, by rfl⟩ : syracuseStep 1967127 = 2950691) B2950691
theorem B8972869 : Blo 1965435 8972869 := bbase (se 4 (by rfl) ⟨841206, by rfl⟩ : syracuseStep 8972869 = 1682413) (by norm_num)
theorem B11963825 : Blo 1965435 11963825 := bstep (se 2 (by rfl) ⟨4486434, by rfl⟩ : syracuseStep 11963825 = 8972869) B8972869
theorem B7975883 : Blo 1965435 7975883 := bstep (se 1 (by rfl) ⟨5981912, by rfl⟩ : syracuseStep 7975883 = 11963825) B11963825
theorem B5317255 : Blo 1965435 5317255 := bstep (se 1 (by rfl) ⟨3987941, by rfl⟩ : syracuseStep 5317255 = 7975883) B7975883
theorem B28358693 : Blo 1965435 28358693 := bstep (se 4 (by rfl) ⟨2658627, by rfl⟩ : syracuseStep 28358693 = 5317255) B5317255
theorem B18905795 : Blo 1965435 18905795 := bstep (se 1 (by rfl) ⟨14179346, by rfl⟩ : syracuseStep 18905795 = 28358693) B28358693
theorem B12603863 : Blo 1965435 12603863 := bstep (se 1 (by rfl) ⟨9452897, by rfl⟩ : syracuseStep 12603863 = 18905795) B18905795
theorem B8402575 : Blo 1965435 8402575 := bstep (se 1 (by rfl) ⟨6301931, by rfl⟩ : syracuseStep 8402575 = 12603863) B12603863
theorem B11203433 : Blo 1965435 11203433 := bstep (se 2 (by rfl) ⟨4201287, by rfl⟩ : syracuseStep 11203433 = 8402575) B8402575
theorem B7468955 : Blo 1965435 7468955 := bstep (se 1 (by rfl) ⟨5601716, by rfl⟩ : syracuseStep 7468955 = 11203433) B11203433
theorem B4979303 : Blo 1965435 4979303 := bstep (se 1 (by rfl) ⟨3734477, by rfl⟩ : syracuseStep 4979303 = 7468955) B7468955
theorem B3319535 : Blo 1965435 3319535 := bstep (se 1 (by rfl) ⟨2489651, by rfl⟩ : syracuseStep 3319535 = 4979303) B4979303
theorem B2213023 : Blo 1965435 2213023 := bstep (se 1 (by rfl) ⟨1659767, by rfl⟩ : syracuseStep 2213023 = 3319535) B3319535
theorem B2950697 : Blo 1965435 2950697 := bstep (se 2 (by rfl) ⟨1106511, by rfl⟩ : syracuseStep 2950697 = 2213023) B2213023
theorem B1967131 : Blo 1965435 1967131 := bstep (se 1 (by rfl) ⟨1475348, by rfl⟩ : syracuseStep 1967131 = 2950697) B2950697
theorem B4375613 : Blo 1965435 4375613 := bbase (se 3 (by rfl) ⟨820427, by rfl⟩ : syracuseStep 4375613 = 1640855) (by norm_num)
theorem B2917075 : Blo 1965435 2917075 := bstep (se 1 (by rfl) ⟨2187806, by rfl⟩ : syracuseStep 2917075 = 4375613) B4375613
theorem B3889433 : Blo 1965435 3889433 := bstep (se 2 (by rfl) ⟨1458537, by rfl⟩ : syracuseStep 3889433 = 2917075) B2917075
theorem B2592955 : Blo 1965435 2592955 := bstep (se 1 (by rfl) ⟨1944716, by rfl⟩ : syracuseStep 2592955 = 3889433) B3889433
theorem B3457273 : Blo 1965435 3457273 := bstep (se 2 (by rfl) ⟨1296477, by rfl⟩ : syracuseStep 3457273 = 2592955) B2592955
theorem B295020629 : Blo 1965435 295020629 := bstep (se 8 (by rfl) ⟨1728636, by rfl⟩ : syracuseStep 295020629 = 3457273) B3457273
theorem B196680419 : Blo 1965435 196680419 := bstep (se 1 (by rfl) ⟨147510314, by rfl⟩ : syracuseStep 196680419 = 295020629) B295020629
theorem B131120279 : Blo 1965435 131120279 := bstep (se 1 (by rfl) ⟨98340209, by rfl⟩ : syracuseStep 131120279 = 196680419) B196680419
theorem B87413519 : Blo 1965435 87413519 := bstep (se 1 (by rfl) ⟨65560139, by rfl⟩ : syracuseStep 87413519 = 131120279) B131120279
theorem B233102717 : Blo 1965435 233102717 := bstep (se 3 (by rfl) ⟨43706759, by rfl⟩ : syracuseStep 233102717 = 87413519) B87413519
theorem B155401811 : Blo 1965435 155401811 := bstep (se 1 (by rfl) ⟨116551358, by rfl⟩ : syracuseStep 155401811 = 233102717) B233102717
theorem B103601207 : Blo 1965435 103601207 := bstep (se 1 (by rfl) ⟨77700905, by rfl⟩ : syracuseStep 103601207 = 155401811) B155401811
theorem B276269885 : Blo 1965435 276269885 := bstep (se 3 (by rfl) ⟨51800603, by rfl⟩ : syracuseStep 276269885 = 103601207) B103601207
theorem B184179923 : Blo 1965435 184179923 := bstep (se 1 (by rfl) ⟨138134942, by rfl⟩ : syracuseStep 184179923 = 276269885) B276269885
theorem B122786615 : Blo 1965435 122786615 := bstep (se 1 (by rfl) ⟨92089961, by rfl⟩ : syracuseStep 122786615 = 184179923) B184179923
theorem B327430973 : Blo 1965435 327430973 := bstep (se 3 (by rfl) ⟨61393307, by rfl⟩ : syracuseStep 327430973 = 122786615) B122786615
theorem B218287315 : Blo 1965435 218287315 := bstep (se 1 (by rfl) ⟨163715486, by rfl⟩ : syracuseStep 218287315 = 327430973) B327430973
theorem B1164199013 : Blo 1965435 1164199013 := bstep (se 4 (by rfl) ⟨109143657, by rfl⟩ : syracuseStep 1164199013 = 218287315) B218287315
theorem B776132675 : Blo 1965435 776132675 := bstep (se 1 (by rfl) ⟨582099506, by rfl⟩ : syracuseStep 776132675 = 1164199013) B1164199013
theorem B517421783 : Blo 1965435 517421783 := bstep (se 1 (by rfl) ⟨388066337, by rfl⟩ : syracuseStep 517421783 = 776132675) B776132675
theorem B1379791421 : Blo 1965435 1379791421 := bstep (se 3 (by rfl) ⟨258710891, by rfl⟩ : syracuseStep 1379791421 = 517421783) B517421783
theorem B919860947 : Blo 1965435 919860947 := bstep (se 1 (by rfl) ⟨689895710, by rfl⟩ : syracuseStep 919860947 = 1379791421) B1379791421
theorem B613240631 : Blo 1965435 613240631 := bstep (se 1 (by rfl) ⟨459930473, by rfl⟩ : syracuseStep 613240631 = 919860947) B919860947
theorem B408827087 : Blo 1965435 408827087 := bstep (se 1 (by rfl) ⟨306620315, by rfl⟩ : syracuseStep 408827087 = 613240631) B613240631
theorem B272551391 : Blo 1965435 272551391 := bstep (se 1 (by rfl) ⟨204413543, by rfl⟩ : syracuseStep 272551391 = 408827087) B408827087
theorem B181700927 : Blo 1965435 181700927 := bstep (se 1 (by rfl) ⟨136275695, by rfl⟩ : syracuseStep 181700927 = 272551391) B272551391
theorem B121133951 : Blo 1965435 121133951 := bstep (se 1 (by rfl) ⟨90850463, by rfl⟩ : syracuseStep 121133951 = 181700927) B181700927
theorem B80755967 : Blo 1965435 80755967 := bstep (se 1 (by rfl) ⟨60566975, by rfl⟩ : syracuseStep 80755967 = 121133951) B121133951
theorem B53837311 : Blo 1965435 53837311 := bstep (se 1 (by rfl) ⟨40377983, by rfl⟩ : syracuseStep 53837311 = 80755967) B80755967
theorem B71783081 : Blo 1965435 71783081 := bstep (se 2 (by rfl) ⟨26918655, by rfl⟩ : syracuseStep 71783081 = 53837311) B53837311
theorem B47855387 : Blo 1965435 47855387 := bstep (se 1 (by rfl) ⟨35891540, by rfl⟩ : syracuseStep 47855387 = 71783081) B71783081
theorem B31903591 : Blo 1965435 31903591 := bstep (se 1 (by rfl) ⟨23927693, by rfl⟩ : syracuseStep 31903591 = 47855387) B47855387
theorem B42538121 : Blo 1965435 42538121 := bstep (se 2 (by rfl) ⟨15951795, by rfl⟩ : syracuseStep 42538121 = 31903591) B31903591
theorem B28358747 : Blo 1965435 28358747 := bstep (se 1 (by rfl) ⟨21269060, by rfl⟩ : syracuseStep 28358747 = 42538121) B42538121
theorem B18905831 : Blo 1965435 18905831 := bstep (se 1 (by rfl) ⟨14179373, by rfl⟩ : syracuseStep 18905831 = 28358747) B28358747
theorem B12603887 : Blo 1965435 12603887 := bstep (se 1 (by rfl) ⟨9452915, by rfl⟩ : syracuseStep 12603887 = 18905831) B18905831
theorem B8402591 : Blo 1965435 8402591 := bstep (se 1 (by rfl) ⟨6301943, by rfl⟩ : syracuseStep 8402591 = 12603887) B12603887
theorem B5601727 : Blo 1965435 5601727 := bstep (se 1 (by rfl) ⟨4201295, by rfl⟩ : syracuseStep 5601727 = 8402591) B8402591
theorem B7468969 : Blo 1965435 7468969 := bstep (se 2 (by rfl) ⟨2800863, by rfl⟩ : syracuseStep 7468969 = 5601727) B5601727
theorem B9958625 : Blo 1965435 9958625 := bstep (se 2 (by rfl) ⟨3734484, by rfl⟩ : syracuseStep 9958625 = 7468969) B7468969
theorem B6639083 : Blo 1965435 6639083 := bstep (se 1 (by rfl) ⟨4979312, by rfl⟩ : syracuseStep 6639083 = 9958625) B9958625
theorem B4426055 : Blo 1965435 4426055 := bstep (se 1 (by rfl) ⟨3319541, by rfl⟩ : syracuseStep 4426055 = 6639083) B6639083
theorem B2950703 : Blo 1965435 2950703 := bstep (se 1 (by rfl) ⟨2213027, by rfl⟩ : syracuseStep 2950703 = 4426055) B4426055
theorem B1967135 : Blo 1965435 1967135 := bstep (se 1 (by rfl) ⟨1475351, by rfl⟩ : syracuseStep 1967135 = 2950703) B2950703
theorem B2950709 : Blo 1965435 2950709 := bbase (se 5 (by rfl) ⟨138314, by rfl⟩ : syracuseStep 2950709 = 276629) (by norm_num)
theorem B1967139 : Blo 1965435 1967139 := bstep (se 1 (by rfl) ⟨1475354, by rfl⟩ : syracuseStep 1967139 = 2950709) B2950709
theorem B4979333 : Blo 1965435 4979333 := bbase (se 4 (by rfl) ⟨466812, by rfl⟩ : syracuseStep 4979333 = 933625) (by norm_num)
theorem B3319555 : Blo 1965435 3319555 := bstep (se 1 (by rfl) ⟨2489666, by rfl⟩ : syracuseStep 3319555 = 4979333) B4979333
theorem B4426073 : Blo 1965435 4426073 := bstep (se 2 (by rfl) ⟨1659777, by rfl⟩ : syracuseStep 4426073 = 3319555) B3319555
theorem B2950715 : Blo 1965435 2950715 := bstep (se 1 (by rfl) ⟨2213036, by rfl⟩ : syracuseStep 2950715 = 4426073) B4426073
theorem B1967143 : Blo 1965435 1967143 := bstep (se 1 (by rfl) ⟨1475357, by rfl⟩ : syracuseStep 1967143 = 2950715) B2950715
theorem B2213041 : Blo 1965435 2213041 := bbase (se 2 (by rfl) ⟨829890, by rfl⟩ : syracuseStep 2213041 = 1659781) (by norm_num)
theorem B2950721 : Blo 1965435 2950721 := bstep (se 2 (by rfl) ⟨1106520, by rfl⟩ : syracuseStep 2950721 = 2213041) B2213041
theorem B1967147 : Blo 1965435 1967147 := bstep (se 1 (by rfl) ⟨1475360, by rfl⟩ : syracuseStep 1967147 = 2950721) B2950721
theorem B2100665 : Blo 1965435 2100665 := bbase (se 2 (by rfl) ⟨787749, by rfl⟩ : syracuseStep 2100665 = 1575499) (by norm_num)
theorem B5601773 : Blo 1965435 5601773 := bstep (se 3 (by rfl) ⟨1050332, by rfl⟩ : syracuseStep 5601773 = 2100665) B2100665
theorem B3734515 : Blo 1965435 3734515 := bstep (se 1 (by rfl) ⟨2800886, by rfl⟩ : syracuseStep 3734515 = 5601773) B5601773
theorem B4979353 : Blo 1965435 4979353 := bstep (se 2 (by rfl) ⟨1867257, by rfl⟩ : syracuseStep 4979353 = 3734515) B3734515
theorem B6639137 : Blo 1965435 6639137 := bstep (se 2 (by rfl) ⟨2489676, by rfl⟩ : syracuseStep 6639137 = 4979353) B4979353
theorem B4426091 : Blo 1965435 4426091 := bstep (se 1 (by rfl) ⟨3319568, by rfl⟩ : syracuseStep 4426091 = 6639137) B6639137
theorem B2950727 : Blo 1965435 2950727 := bstep (se 1 (by rfl) ⟨2213045, by rfl⟩ : syracuseStep 2950727 = 4426091) B4426091
theorem B1967151 : Blo 1965435 1967151 := bstep (se 1 (by rfl) ⟨1475363, by rfl⟩ : syracuseStep 1967151 = 2950727) B2950727
theorem B2950733 : Blo 1965435 2950733 := bbase (se 3 (by rfl) ⟨553262, by rfl⟩ : syracuseStep 2950733 = 1106525) (by norm_num)
theorem B1967155 : Blo 1965435 1967155 := bstep (se 1 (by rfl) ⟨1475366, by rfl⟩ : syracuseStep 1967155 = 2950733) B2950733
theorem B4426109 : Blo 1965435 4426109 := bbase (se 3 (by rfl) ⟨829895, by rfl⟩ : syracuseStep 4426109 = 1659791) (by norm_num)
theorem B2950739 : Blo 1965435 2950739 := bstep (se 1 (by rfl) ⟨2213054, by rfl⟩ : syracuseStep 2950739 = 4426109) B4426109
theorem B1967159 : Blo 1965435 1967159 := bstep (se 1 (by rfl) ⟨1475369, by rfl⟩ : syracuseStep 1967159 = 2950739) B2950739
theorem B3319589 : Blo 1965435 3319589 := bbase (se 4 (by rfl) ⟨311211, by rfl⟩ : syracuseStep 3319589 = 622423) (by norm_num)
theorem B2213059 : Blo 1965435 2213059 := bstep (se 1 (by rfl) ⟨1659794, by rfl⟩ : syracuseStep 2213059 = 3319589) B3319589
theorem B2950745 : Blo 1965435 2950745 := bstep (se 2 (by rfl) ⟨1106529, by rfl⟩ : syracuseStep 2950745 = 2213059) B2213059
theorem B1967163 : Blo 1965435 1967163 := bstep (se 1 (by rfl) ⟨1475372, by rfl⟩ : syracuseStep 1967163 = 2950745) B2950745
theorem B2800909 : Blo 1965435 2800909 := bbase (se 3 (by rfl) ⟨525170, by rfl⟩ : syracuseStep 2800909 = 1050341) (by norm_num)
theorem B14938181 : Blo 1965435 14938181 := bstep (se 4 (by rfl) ⟨1400454, by rfl⟩ : syracuseStep 14938181 = 2800909) B2800909
theorem B9958787 : Blo 1965435 9958787 := bstep (se 1 (by rfl) ⟨7469090, by rfl⟩ : syracuseStep 9958787 = 14938181) B14938181
theorem B6639191 : Blo 1965435 6639191 := bstep (se 1 (by rfl) ⟨4979393, by rfl⟩ : syracuseStep 6639191 = 9958787) B9958787
theorem B4426127 : Blo 1965435 4426127 := bstep (se 1 (by rfl) ⟨3319595, by rfl⟩ : syracuseStep 4426127 = 6639191) B6639191
theorem B2950751 : Blo 1965435 2950751 := bstep (se 1 (by rfl) ⟨2213063, by rfl⟩ : syracuseStep 2950751 = 4426127) B4426127
theorem B1967167 : Blo 1965435 1967167 := bstep (se 1 (by rfl) ⟨1475375, by rfl⟩ : syracuseStep 1967167 = 2950751) B2950751
theorem B2950757 : Blo 1965435 2950757 := bbase (se 4 (by rfl) ⟨276633, by rfl⟩ : syracuseStep 2950757 = 553267) (by norm_num)
theorem B1967171 : Blo 1965435 1967171 := bstep (se 1 (by rfl) ⟨1475378, by rfl⟩ : syracuseStep 1967171 = 2950757) B2950757
theorem B3151037 : Blo 1965435 3151037 := bbase (se 3 (by rfl) ⟨590819, by rfl⟩ : syracuseStep 3151037 = 1181639) (by norm_num)
theorem B2100691 : Blo 1965435 2100691 := bstep (se 1 (by rfl) ⟨1575518, by rfl⟩ : syracuseStep 2100691 = 3151037) B3151037
theorem B2800921 : Blo 1965435 2800921 := bstep (se 2 (by rfl) ⟨1050345, by rfl⟩ : syracuseStep 2800921 = 2100691) B2100691
theorem B3734561 : Blo 1965435 3734561 := bstep (se 2 (by rfl) ⟨1400460, by rfl⟩ : syracuseStep 3734561 = 2800921) B2800921
theorem B2489707 : Blo 1965435 2489707 := bstep (se 1 (by rfl) ⟨1867280, by rfl⟩ : syracuseStep 2489707 = 3734561) B3734561
theorem B3319609 : Blo 1965435 3319609 := bstep (se 2 (by rfl) ⟨1244853, by rfl⟩ : syracuseStep 3319609 = 2489707) B2489707
theorem B4426145 : Blo 1965435 4426145 := bstep (se 2 (by rfl) ⟨1659804, by rfl⟩ : syracuseStep 4426145 = 3319609) B3319609
theorem B2950763 : Blo 1965435 2950763 := bstep (se 1 (by rfl) ⟨2213072, by rfl⟩ : syracuseStep 2950763 = 4426145) B4426145
theorem B1967175 : Blo 1965435 1967175 := bstep (se 1 (by rfl) ⟨1475381, by rfl⟩ : syracuseStep 1967175 = 2950763) B2950763
theorem B2213077 : Blo 1965435 2213077 := bbase (se 7 (by rfl) ⟨25934, by rfl⟩ : syracuseStep 2213077 = 51869) (by norm_num)
theorem B2950769 : Blo 1965435 2950769 := bstep (se 2 (by rfl) ⟨1106538, by rfl⟩ : syracuseStep 2950769 = 2213077) B2213077
theorem B1967179 : Blo 1965435 1967179 := bstep (se 1 (by rfl) ⟨1475384, by rfl⟩ : syracuseStep 1967179 = 2950769) B2950769
theorem B2489717 : Blo 1965435 2489717 := bbase (se 5 (by rfl) ⟨116705, by rfl⟩ : syracuseStep 2489717 = 233411) (by norm_num)
theorem B6639245 : Blo 1965435 6639245 := bstep (se 3 (by rfl) ⟨1244858, by rfl⟩ : syracuseStep 6639245 = 2489717) B2489717
theorem B4426163 : Blo 1965435 4426163 := bstep (se 1 (by rfl) ⟨3319622, by rfl⟩ : syracuseStep 4426163 = 6639245) B6639245
theorem B2950775 : Blo 1965435 2950775 := bstep (se 1 (by rfl) ⟨2213081, by rfl⟩ : syracuseStep 2950775 = 4426163) B4426163
theorem B1967183 : Blo 1965435 1967183 := bstep (se 1 (by rfl) ⟨1475387, by rfl⟩ : syracuseStep 1967183 = 2950775) B2950775
theorem B2950781 : Blo 1965435 2950781 := bbase (se 3 (by rfl) ⟨553271, by rfl⟩ : syracuseStep 2950781 = 1106543) (by norm_num)
theorem B1967187 : Blo 1965435 1967187 := bstep (se 1 (by rfl) ⟨1475390, by rfl⟩ : syracuseStep 1967187 = 2950781) B2950781
theorem B4426181 : Blo 1965435 4426181 := bbase (se 4 (by rfl) ⟨414954, by rfl⟩ : syracuseStep 4426181 = 829909) (by norm_num)
theorem B2950787 : Blo 1965435 2950787 := bstep (se 1 (by rfl) ⟨2213090, by rfl⟩ : syracuseStep 2950787 = 4426181) B4426181
theorem B1967191 : Blo 1965435 1967191 := bstep (se 1 (by rfl) ⟨1475393, by rfl⟩ : syracuseStep 1967191 = 2950787) B2950787
theorem B5317429 : Blo 1965435 5317429 := bbase (se 5 (by rfl) ⟨249254, by rfl⟩ : syracuseStep 5317429 = 498509) (by norm_num)
theorem B7089905 : Blo 1965435 7089905 := bstep (se 2 (by rfl) ⟨2658714, by rfl⟩ : syracuseStep 7089905 = 5317429) B5317429
theorem B4726603 : Blo 1965435 4726603 := bstep (se 1 (by rfl) ⟨3544952, by rfl⟩ : syracuseStep 4726603 = 7089905) B7089905
theorem B6302137 : Blo 1965435 6302137 := bstep (se 2 (by rfl) ⟨2363301, by rfl⟩ : syracuseStep 6302137 = 4726603) B4726603
theorem B8402849 : Blo 1965435 8402849 := bstep (se 2 (by rfl) ⟨3151068, by rfl⟩ : syracuseStep 8402849 = 6302137) B6302137
theorem B5601899 : Blo 1965435 5601899 := bstep (se 1 (by rfl) ⟨4201424, by rfl⟩ : syracuseStep 5601899 = 8402849) B8402849
theorem B3734599 : Blo 1965435 3734599 := bstep (se 1 (by rfl) ⟨2800949, by rfl⟩ : syracuseStep 3734599 = 5601899) B5601899
theorem B4979465 : Blo 1965435 4979465 := bstep (se 2 (by rfl) ⟨1867299, by rfl⟩ : syracuseStep 4979465 = 3734599) B3734599
theorem B3319643 : Blo 1965435 3319643 := bstep (se 1 (by rfl) ⟨2489732, by rfl⟩ : syracuseStep 3319643 = 4979465) B4979465
theorem B2213095 : Blo 1965435 2213095 := bstep (se 1 (by rfl) ⟨1659821, by rfl⟩ : syracuseStep 2213095 = 3319643) B3319643
theorem B2950793 : Blo 1965435 2950793 := bstep (se 2 (by rfl) ⟨1106547, by rfl⟩ : syracuseStep 2950793 = 2213095) B2213095
theorem B1967195 : Blo 1965435 1967195 := bstep (se 1 (by rfl) ⟨1475396, by rfl⟩ : syracuseStep 1967195 = 2950793) B2950793
theorem B9958949 : Blo 1965435 9958949 := bbase (se 4 (by rfl) ⟨933651, by rfl⟩ : syracuseStep 9958949 = 1867303) (by norm_num)
theorem B6639299 : Blo 1965435 6639299 := bstep (se 1 (by rfl) ⟨4979474, by rfl⟩ : syracuseStep 6639299 = 9958949) B9958949
theorem B4426199 : Blo 1965435 4426199 := bstep (se 1 (by rfl) ⟨3319649, by rfl⟩ : syracuseStep 4426199 = 6639299) B6639299
theorem B2950799 : Blo 1965435 2950799 := bstep (se 1 (by rfl) ⟨2213099, by rfl⟩ : syracuseStep 2950799 = 4426199) B4426199
theorem B1967199 : Blo 1965435 1967199 := bstep (se 1 (by rfl) ⟨1475399, by rfl⟩ : syracuseStep 1967199 = 2950799) B2950799
theorem B2950805 : Blo 1965435 2950805 := bbase (se 6 (by rfl) ⟨69159, by rfl⟩ : syracuseStep 2950805 = 138319) (by norm_num)
theorem B1967203 : Blo 1965435 1967203 := bstep (se 1 (by rfl) ⟨1475402, by rfl⟩ : syracuseStep 1967203 = 2950805) B2950805
theorem B4547821 : Blo 1965435 4547821 := bbase (se 3 (by rfl) ⟨852716, by rfl⟩ : syracuseStep 4547821 = 1705433) (by norm_num)
theorem B6063761 : Blo 1965435 6063761 := bstep (se 2 (by rfl) ⟨2273910, by rfl⟩ : syracuseStep 6063761 = 4547821) B4547821
theorem B16170029 : Blo 1965435 16170029 := bstep (se 3 (by rfl) ⟨3031880, by rfl⟩ : syracuseStep 16170029 = 6063761) B6063761
theorem B10780019 : Blo 1965435 10780019 := bstep (se 1 (by rfl) ⟨8085014, by rfl⟩ : syracuseStep 10780019 = 16170029) B16170029
theorem B7186679 : Blo 1965435 7186679 := bstep (se 1 (by rfl) ⟨5390009, by rfl⟩ : syracuseStep 7186679 = 10780019) B10780019
theorem B4791119 : Blo 1965435 4791119 := bstep (se 1 (by rfl) ⟨3593339, by rfl⟩ : syracuseStep 4791119 = 7186679) B7186679
theorem B51105269 : Blo 1965435 51105269 := bstep (se 5 (by rfl) ⟨2395559, by rfl⟩ : syracuseStep 51105269 = 4791119) B4791119
theorem B136280717 : Blo 1965435 136280717 := bstep (se 3 (by rfl) ⟨25552634, by rfl⟩ : syracuseStep 136280717 = 51105269) B51105269
theorem B90853811 : Blo 1965435 90853811 := bstep (se 1 (by rfl) ⟨68140358, by rfl⟩ : syracuseStep 90853811 = 136280717) B136280717
theorem B60569207 : Blo 1965435 60569207 := bstep (se 1 (by rfl) ⟨45426905, by rfl⟩ : syracuseStep 60569207 = 90853811) B90853811
theorem B40379471 : Blo 1965435 40379471 := bstep (se 1 (by rfl) ⟨30284603, by rfl⟩ : syracuseStep 40379471 = 60569207) B60569207
theorem B26919647 : Blo 1965435 26919647 := bstep (se 1 (by rfl) ⟨20189735, by rfl⟩ : syracuseStep 26919647 = 40379471) B40379471
theorem B17946431 : Blo 1965435 17946431 := bstep (se 1 (by rfl) ⟨13459823, by rfl⟩ : syracuseStep 17946431 = 26919647) B26919647
theorem B11964287 : Blo 1965435 11964287 := bstep (se 1 (by rfl) ⟨8973215, by rfl⟩ : syracuseStep 11964287 = 17946431) B17946431
theorem B7976191 : Blo 1965435 7976191 := bstep (se 1 (by rfl) ⟨5982143, by rfl⟩ : syracuseStep 7976191 = 11964287) B11964287
theorem B10634921 : Blo 1965435 10634921 := bstep (se 2 (by rfl) ⟨3988095, by rfl⟩ : syracuseStep 10634921 = 7976191) B7976191
theorem B7089947 : Blo 1965435 7089947 := bstep (se 1 (by rfl) ⟨5317460, by rfl⟩ : syracuseStep 7089947 = 10634921) B10634921
theorem B4726631 : Blo 1965435 4726631 := bstep (se 1 (by rfl) ⟨3544973, by rfl⟩ : syracuseStep 4726631 = 7089947) B7089947
theorem B12604349 : Blo 1965435 12604349 := bstep (se 3 (by rfl) ⟨2363315, by rfl⟩ : syracuseStep 12604349 = 4726631) B4726631
theorem B8402899 : Blo 1965435 8402899 := bstep (se 1 (by rfl) ⟨6302174, by rfl⟩ : syracuseStep 8402899 = 12604349) B12604349
theorem B11203865 : Blo 1965435 11203865 := bstep (se 2 (by rfl) ⟨4201449, by rfl⟩ : syracuseStep 11203865 = 8402899) B8402899
theorem B7469243 : Blo 1965435 7469243 := bstep (se 1 (by rfl) ⟨5601932, by rfl⟩ : syracuseStep 7469243 = 11203865) B11203865
theorem B4979495 : Blo 1965435 4979495 := bstep (se 1 (by rfl) ⟨3734621, by rfl⟩ : syracuseStep 4979495 = 7469243) B7469243
theorem B3319663 : Blo 1965435 3319663 := bstep (se 1 (by rfl) ⟨2489747, by rfl⟩ : syracuseStep 3319663 = 4979495) B4979495
theorem B4426217 : Blo 1965435 4426217 := bstep (se 2 (by rfl) ⟨1659831, by rfl⟩ : syracuseStep 4426217 = 3319663) B3319663
theorem B2950811 : Blo 1965435 2950811 := bstep (se 1 (by rfl) ⟨2213108, by rfl⟩ : syracuseStep 2950811 = 4426217) B4426217
theorem B1967207 : Blo 1965435 1967207 := bstep (se 1 (by rfl) ⟨1475405, by rfl⟩ : syracuseStep 1967207 = 2950811) B2950811
theorem B2213113 : Blo 1965435 2213113 := bbase (se 2 (by rfl) ⟨829917, by rfl⟩ : syracuseStep 2213113 = 1659835) (by norm_num)
theorem B2950817 : Blo 1965435 2950817 := bstep (se 2 (by rfl) ⟨1106556, by rfl⟩ : syracuseStep 2950817 = 2213113) B2213113
theorem B1967211 : Blo 1965435 1967211 := bstep (se 1 (by rfl) ⟨1475408, by rfl⟩ : syracuseStep 1967211 = 2950817) B2950817
theorem B8402933 : Blo 1965435 8402933 := bbase (se 5 (by rfl) ⟨393887, by rfl⟩ : syracuseStep 8402933 = 787775) (by norm_num)
theorem B5601955 : Blo 1965435 5601955 := bstep (se 1 (by rfl) ⟨4201466, by rfl⟩ : syracuseStep 5601955 = 8402933) B8402933
theorem B7469273 : Blo 1965435 7469273 := bstep (se 2 (by rfl) ⟨2800977, by rfl⟩ : syracuseStep 7469273 = 5601955) B5601955
theorem B4979515 : Blo 1965435 4979515 := bstep (se 1 (by rfl) ⟨3734636, by rfl⟩ : syracuseStep 4979515 = 7469273) B7469273
theorem B6639353 : Blo 1965435 6639353 := bstep (se 2 (by rfl) ⟨2489757, by rfl⟩ : syracuseStep 6639353 = 4979515) B4979515
theorem B4426235 : Blo 1965435 4426235 := bstep (se 1 (by rfl) ⟨3319676, by rfl⟩ : syracuseStep 4426235 = 6639353) B6639353
theorem B2950823 : Blo 1965435 2950823 := bstep (se 1 (by rfl) ⟨2213117, by rfl⟩ : syracuseStep 2950823 = 4426235) B4426235
theorem B1967215 : Blo 1965435 1967215 := bstep (se 1 (by rfl) ⟨1475411, by rfl⟩ : syracuseStep 1967215 = 2950823) B2950823
theorem B2950829 : Blo 1965435 2950829 := bbase (se 3 (by rfl) ⟨553280, by rfl⟩ : syracuseStep 2950829 = 1106561) (by norm_num)
theorem B1967219 : Blo 1965435 1967219 := bstep (se 1 (by rfl) ⟨1475414, by rfl⟩ : syracuseStep 1967219 = 2950829) B2950829
theorem B4426253 : Blo 1965435 4426253 := bbase (se 3 (by rfl) ⟨829922, by rfl⟩ : syracuseStep 4426253 = 1659845) (by norm_num)
theorem B2950835 : Blo 1965435 2950835 := bstep (se 1 (by rfl) ⟨2213126, by rfl⟩ : syracuseStep 2950835 = 4426253) B4426253
theorem B1967223 : Blo 1965435 1967223 := bstep (se 1 (by rfl) ⟨1475417, by rfl⟩ : syracuseStep 1967223 = 2950835) B2950835
theorem B2489773 : Blo 1965435 2489773 := bbase (se 3 (by rfl) ⟨466832, by rfl⟩ : syracuseStep 2489773 = 933665) (by norm_num)
theorem B3319697 : Blo 1965435 3319697 := bstep (se 2 (by rfl) ⟨1244886, by rfl⟩ : syracuseStep 3319697 = 2489773) B2489773
theorem B2213131 : Blo 1965435 2213131 := bstep (se 1 (by rfl) ⟨1659848, by rfl⟩ : syracuseStep 2213131 = 3319697) B3319697
theorem B2950841 : Blo 1965435 2950841 := bstep (se 2 (by rfl) ⟨1106565, by rfl⟩ : syracuseStep 2950841 = 2213131) B2213131
theorem B1967227 : Blo 1965435 1967227 := bstep (se 1 (by rfl) ⟨1475420, by rfl⟩ : syracuseStep 1967227 = 2950841) B2950841
theorem B12604501 : Blo 1965435 12604501 := bbase (se 8 (by rfl) ⟨73854, by rfl⟩ : syracuseStep 12604501 = 147709) (by norm_num)
theorem B16806001 : Blo 1965435 16806001 := bstep (se 2 (by rfl) ⟨6302250, by rfl⟩ : syracuseStep 16806001 = 12604501) B12604501
theorem B22408001 : Blo 1965435 22408001 := bstep (se 2 (by rfl) ⟨8403000, by rfl⟩ : syracuseStep 22408001 = 16806001) B16806001
theorem B14938667 : Blo 1965435 14938667 := bstep (se 1 (by rfl) ⟨11204000, by rfl⟩ : syracuseStep 14938667 = 22408001) B22408001
theorem B9959111 : Blo 1965435 9959111 := bstep (se 1 (by rfl) ⟨7469333, by rfl⟩ : syracuseStep 9959111 = 14938667) B14938667
theorem B6639407 : Blo 1965435 6639407 := bstep (se 1 (by rfl) ⟨4979555, by rfl⟩ : syracuseStep 6639407 = 9959111) B9959111
theorem B4426271 : Blo 1965435 4426271 := bstep (se 1 (by rfl) ⟨3319703, by rfl⟩ : syracuseStep 4426271 = 6639407) B6639407
theorem B2950847 : Blo 1965435 2950847 := bstep (se 1 (by rfl) ⟨2213135, by rfl⟩ : syracuseStep 2950847 = 4426271) B4426271
theorem B1967231 : Blo 1965435 1967231 := bstep (se 1 (by rfl) ⟨1475423, by rfl⟩ : syracuseStep 1967231 = 2950847) B2950847
theorem B2950853 : Blo 1965435 2950853 := bbase (se 4 (by rfl) ⟨276642, by rfl⟩ : syracuseStep 2950853 = 553285) (by norm_num)
theorem B1967235 : Blo 1965435 1967235 := bstep (se 1 (by rfl) ⟨1475426, by rfl⟩ : syracuseStep 1967235 = 2950853) B2950853
theorem B3319717 : Blo 1965435 3319717 := bbase (se 4 (by rfl) ⟨311223, by rfl⟩ : syracuseStep 3319717 = 622447) (by norm_num)
theorem B4426289 : Blo 1965435 4426289 := bstep (se 2 (by rfl) ⟨1659858, by rfl⟩ : syracuseStep 4426289 = 3319717) B3319717
theorem B2950859 : Blo 1965435 2950859 := bstep (se 1 (by rfl) ⟨2213144, by rfl⟩ : syracuseStep 2950859 = 4426289) B4426289
theorem B1967239 : Blo 1965435 1967239 := bstep (se 1 (by rfl) ⟨1475429, by rfl⟩ : syracuseStep 1967239 = 2950859) B2950859
theorem B2213149 : Blo 1965435 2213149 := bbase (se 3 (by rfl) ⟨414965, by rfl⟩ : syracuseStep 2213149 = 829931) (by norm_num)
theorem B2950865 : Blo 1965435 2950865 := bstep (se 2 (by rfl) ⟨1106574, by rfl⟩ : syracuseStep 2950865 = 2213149) B2213149
theorem B1967243 : Blo 1965435 1967243 := bstep (se 1 (by rfl) ⟨1475432, by rfl⟩ : syracuseStep 1967243 = 2950865) B2950865
theorem B6639461 : Blo 1965435 6639461 := bbase (se 4 (by rfl) ⟨622449, by rfl⟩ : syracuseStep 6639461 = 1244899) (by norm_num)
theorem B4426307 : Blo 1965435 4426307 := bstep (se 1 (by rfl) ⟨3319730, by rfl⟩ : syracuseStep 4426307 = 6639461) B6639461
theorem B2950871 : Blo 1965435 2950871 := bstep (se 1 (by rfl) ⟨2213153, by rfl⟩ : syracuseStep 2950871 = 4426307) B4426307
theorem B1967247 : Blo 1965435 1967247 := bstep (se 1 (by rfl) ⟨1475435, by rfl⟩ : syracuseStep 1967247 = 2950871) B2950871
theorem B2950877 : Blo 1965435 2950877 := bbase (se 3 (by rfl) ⟨553289, by rfl⟩ : syracuseStep 2950877 = 1106579) (by norm_num)
theorem B1967251 : Blo 1965435 1967251 := bstep (se 1 (by rfl) ⟨1475438, by rfl⟩ : syracuseStep 1967251 = 2950877) B2950877
theorem B4426325 : Blo 1965435 4426325 := bbase (se 8 (by rfl) ⟨25935, by rfl⟩ : syracuseStep 4426325 = 51871) (by norm_num)
theorem B2950883 : Blo 1965435 2950883 := bstep (se 1 (by rfl) ⟨2213162, by rfl⟩ : syracuseStep 2950883 = 4426325) B4426325
theorem B1967255 : Blo 1965435 1967255 := bstep (se 1 (by rfl) ⟨1475441, by rfl⟩ : syracuseStep 1967255 = 2950883) B2950883
theorem B4726757 : Blo 1965435 4726757 := bbase (se 4 (by rfl) ⟨443133, by rfl⟩ : syracuseStep 4726757 = 886267) (by norm_num)
theorem B3151171 : Blo 1965435 3151171 := bstep (se 1 (by rfl) ⟨2363378, by rfl⟩ : syracuseStep 3151171 = 4726757) B4726757
theorem B4201561 : Blo 1965435 4201561 := bstep (se 2 (by rfl) ⟨1575585, by rfl⟩ : syracuseStep 4201561 = 3151171) B3151171
theorem B5602081 : Blo 1965435 5602081 := bstep (se 2 (by rfl) ⟨2100780, by rfl⟩ : syracuseStep 5602081 = 4201561) B4201561
theorem B7469441 : Blo 1965435 7469441 := bstep (se 2 (by rfl) ⟨2801040, by rfl⟩ : syracuseStep 7469441 = 5602081) B5602081
theorem B4979627 : Blo 1965435 4979627 := bstep (se 1 (by rfl) ⟨3734720, by rfl⟩ : syracuseStep 4979627 = 7469441) B7469441
theorem B3319751 : Blo 1965435 3319751 := bstep (se 1 (by rfl) ⟨2489813, by rfl⟩ : syracuseStep 3319751 = 4979627) B4979627
theorem B2213167 : Blo 1965435 2213167 := bstep (se 1 (by rfl) ⟨1659875, by rfl⟩ : syracuseStep 2213167 = 3319751) B3319751
theorem B2950889 : Blo 1965435 2950889 := bstep (se 2 (by rfl) ⟨1106583, by rfl⟩ : syracuseStep 2950889 = 2213167) B2213167
theorem B1967259 : Blo 1965435 1967259 := bstep (se 1 (by rfl) ⟨1475444, by rfl⟩ : syracuseStep 1967259 = 2950889) B2950889
theorem B4726765 : Blo 1965435 4726765 := bbase (se 3 (by rfl) ⟨886268, by rfl⟩ : syracuseStep 4726765 = 1772537) (by norm_num)
theorem B25209413 : Blo 1965435 25209413 := bstep (se 4 (by rfl) ⟨2363382, by rfl⟩ : syracuseStep 25209413 = 4726765) B4726765
theorem B16806275 : Blo 1965435 16806275 := bstep (se 1 (by rfl) ⟨12604706, by rfl⟩ : syracuseStep 16806275 = 25209413) B25209413
theorem B11204183 : Blo 1965435 11204183 := bstep (se 1 (by rfl) ⟨8403137, by rfl⟩ : syracuseStep 11204183 = 16806275) B16806275
theorem B7469455 : Blo 1965435 7469455 := bstep (se 1 (by rfl) ⟨5602091, by rfl⟩ : syracuseStep 7469455 = 11204183) B11204183
theorem B9959273 : Blo 1965435 9959273 := bstep (se 2 (by rfl) ⟨3734727, by rfl⟩ : syracuseStep 9959273 = 7469455) B7469455
theorem B6639515 : Blo 1965435 6639515 := bstep (se 1 (by rfl) ⟨4979636, by rfl⟩ : syracuseStep 6639515 = 9959273) B9959273
theorem B4426343 : Blo 1965435 4426343 := bstep (se 1 (by rfl) ⟨3319757, by rfl⟩ : syracuseStep 4426343 = 6639515) B6639515
theorem B2950895 : Blo 1965435 2950895 := bstep (se 1 (by rfl) ⟨2213171, by rfl⟩ : syracuseStep 2950895 = 4426343) B4426343
theorem B1967263 : Blo 1965435 1967263 := bstep (se 1 (by rfl) ⟨1475447, by rfl⟩ : syracuseStep 1967263 = 2950895) B2950895
theorem B2950901 : Blo 1965435 2950901 := bbase (se 5 (by rfl) ⟨138323, by rfl⟩ : syracuseStep 2950901 = 276647) (by norm_num)
theorem B1967267 : Blo 1965435 1967267 := bstep (se 1 (by rfl) ⟨1475450, by rfl⟩ : syracuseStep 1967267 = 2950901) B2950901
theorem B8403173 : Blo 1965435 8403173 := bbase (se 4 (by rfl) ⟨787797, by rfl⟩ : syracuseStep 8403173 = 1575595) (by norm_num)
theorem B5602115 : Blo 1965435 5602115 := bstep (se 1 (by rfl) ⟨4201586, by rfl⟩ : syracuseStep 5602115 = 8403173) B8403173
theorem B3734743 : Blo 1965435 3734743 := bstep (se 1 (by rfl) ⟨2801057, by rfl⟩ : syracuseStep 3734743 = 5602115) B5602115
theorem B4979657 : Blo 1965435 4979657 := bstep (se 2 (by rfl) ⟨1867371, by rfl⟩ : syracuseStep 4979657 = 3734743) B3734743
theorem B3319771 : Blo 1965435 3319771 := bstep (se 1 (by rfl) ⟨2489828, by rfl⟩ : syracuseStep 3319771 = 4979657) B4979657
theorem B4426361 : Blo 1965435 4426361 := bstep (se 2 (by rfl) ⟨1659885, by rfl⟩ : syracuseStep 4426361 = 3319771) B3319771
theorem B2950907 : Blo 1965435 2950907 := bstep (se 1 (by rfl) ⟨2213180, by rfl⟩ : syracuseStep 2950907 = 4426361) B4426361
theorem B1967271 : Blo 1965435 1967271 := bstep (se 1 (by rfl) ⟨1475453, by rfl⟩ : syracuseStep 1967271 = 2950907) B2950907
theorem B2213185 : Blo 1965435 2213185 := bbase (se 2 (by rfl) ⟨829944, by rfl⟩ : syracuseStep 2213185 = 1659889) (by norm_num)
theorem B2950913 : Blo 1965435 2950913 := bstep (se 2 (by rfl) ⟨1106592, by rfl⟩ : syracuseStep 2950913 = 2213185) B2213185
theorem B1967275 : Blo 1965435 1967275 := bstep (se 1 (by rfl) ⟨1475456, by rfl⟩ : syracuseStep 1967275 = 2950913) B2950913
theorem B4979677 : Blo 1965435 4979677 := bbase (se 3 (by rfl) ⟨933689, by rfl⟩ : syracuseStep 4979677 = 1867379) (by norm_num)
theorem B6639569 : Blo 1965435 6639569 := bstep (se 2 (by rfl) ⟨2489838, by rfl⟩ : syracuseStep 6639569 = 4979677) B4979677
theorem B4426379 : Blo 1965435 4426379 := bstep (se 1 (by rfl) ⟨3319784, by rfl⟩ : syracuseStep 4426379 = 6639569) B6639569
theorem B2950919 : Blo 1965435 2950919 := bstep (se 1 (by rfl) ⟨2213189, by rfl⟩ : syracuseStep 2950919 = 4426379) B4426379
theorem B1967279 : Blo 1965435 1967279 := bstep (se 1 (by rfl) ⟨1475459, by rfl⟩ : syracuseStep 1967279 = 2950919) B2950919
theorem B2950925 : Blo 1965435 2950925 := bbase (se 3 (by rfl) ⟨553298, by rfl⟩ : syracuseStep 2950925 = 1106597) (by norm_num)
theorem B1967283 : Blo 1965435 1967283 := bstep (se 1 (by rfl) ⟨1475462, by rfl⟩ : syracuseStep 1967283 = 2950925) B2950925
theorem B4426397 : Blo 1965435 4426397 := bbase (se 3 (by rfl) ⟨829949, by rfl⟩ : syracuseStep 4426397 = 1659899) (by norm_num)
theorem B2950931 : Blo 1965435 2950931 := bstep (se 1 (by rfl) ⟨2213198, by rfl⟩ : syracuseStep 2950931 = 4426397) B4426397
theorem B1967287 : Blo 1965435 1967287 := bstep (se 1 (by rfl) ⟨1475465, by rfl⟩ : syracuseStep 1967287 = 2950931) B2950931
theorem B3319805 : Blo 1965435 3319805 := bbase (se 3 (by rfl) ⟨622463, by rfl⟩ : syracuseStep 3319805 = 1244927) (by norm_num)
theorem B2213203 : Blo 1965435 2213203 := bstep (se 1 (by rfl) ⟨1659902, by rfl⟩ : syracuseStep 2213203 = 3319805) B3319805
theorem B2950937 : Blo 1965435 2950937 := bstep (se 2 (by rfl) ⟨1106601, by rfl⟩ : syracuseStep 2950937 = 2213203) B2213203
theorem B1967291 : Blo 1965435 1967291 := bstep (se 1 (by rfl) ⟨1475468, by rfl⟩ : syracuseStep 1967291 = 2950937) B2950937
theorem B4201637 : Blo 1965435 4201637 := bbase (se 4 (by rfl) ⟨393903, by rfl⟩ : syracuseStep 4201637 = 787807) (by norm_num)
theorem B11204365 : Blo 1965435 11204365 := bstep (se 3 (by rfl) ⟨2100818, by rfl⟩ : syracuseStep 11204365 = 4201637) B4201637
theorem B14939153 : Blo 1965435 14939153 := bstep (se 2 (by rfl) ⟨5602182, by rfl⟩ : syracuseStep 14939153 = 11204365) B11204365
theorem B9959435 : Blo 1965435 9959435 := bstep (se 1 (by rfl) ⟨7469576, by rfl⟩ : syracuseStep 9959435 = 14939153) B14939153
theorem B6639623 : Blo 1965435 6639623 := bstep (se 1 (by rfl) ⟨4979717, by rfl⟩ : syracuseStep 6639623 = 9959435) B9959435
theorem B4426415 : Blo 1965435 4426415 := bstep (se 1 (by rfl) ⟨3319811, by rfl⟩ : syracuseStep 4426415 = 6639623) B6639623
theorem B2950943 : Blo 1965435 2950943 := bstep (se 1 (by rfl) ⟨2213207, by rfl⟩ : syracuseStep 2950943 = 4426415) B4426415
theorem B1967295 : Blo 1965435 1967295 := bstep (se 1 (by rfl) ⟨1475471, by rfl⟩ : syracuseStep 1967295 = 2950943) B2950943
theorem B2950949 : Blo 1965435 2950949 := bbase (se 4 (by rfl) ⟨276651, by rfl⟩ : syracuseStep 2950949 = 553303) (by norm_num)
theorem B1967299 : Blo 1965435 1967299 := bstep (se 1 (by rfl) ⟨1475474, by rfl⟩ : syracuseStep 1967299 = 2950949) B2950949
theorem B2489869 : Blo 1965435 2489869 := bbase (se 3 (by rfl) ⟨466850, by rfl⟩ : syracuseStep 2489869 = 933701) (by norm_num)
theorem B3319825 : Blo 1965435 3319825 := bstep (se 2 (by rfl) ⟨1244934, by rfl⟩ : syracuseStep 3319825 = 2489869) B2489869
theorem B4426433 : Blo 1965435 4426433 := bstep (se 2 (by rfl) ⟨1659912, by rfl⟩ : syracuseStep 4426433 = 3319825) B3319825
theorem B2950955 : Blo 1965435 2950955 := bstep (se 1 (by rfl) ⟨2213216, by rfl⟩ : syracuseStep 2950955 = 4426433) B4426433
theorem B1967303 : Blo 1965435 1967303 := bstep (se 1 (by rfl) ⟨1475477, by rfl⟩ : syracuseStep 1967303 = 2950955) B2950955
theorem B2213221 : Blo 1965435 2213221 := bbase (se 4 (by rfl) ⟨207489, by rfl⟩ : syracuseStep 2213221 = 414979) (by norm_num)
theorem B2950961 : Blo 1965435 2950961 := bstep (se 2 (by rfl) ⟨1106610, by rfl⟩ : syracuseStep 2950961 = 2213221) B2213221
theorem B1967307 : Blo 1965435 1967307 := bstep (se 1 (by rfl) ⟨1475480, by rfl⟩ : syracuseStep 1967307 = 2950961) B2950961
theorem B5602229 : Blo 1965435 5602229 := bbase (se 5 (by rfl) ⟨262604, by rfl⟩ : syracuseStep 5602229 = 525209) (by norm_num)
theorem B3734819 : Blo 1965435 3734819 := bstep (se 1 (by rfl) ⟨2801114, by rfl⟩ : syracuseStep 3734819 = 5602229) B5602229
theorem B2489879 : Blo 1965435 2489879 := bstep (se 1 (by rfl) ⟨1867409, by rfl⟩ : syracuseStep 2489879 = 3734819) B3734819
theorem B6639677 : Blo 1965435 6639677 := bstep (se 3 (by rfl) ⟨1244939, by rfl⟩ : syracuseStep 6639677 = 2489879) B2489879
theorem B4426451 : Blo 1965435 4426451 := bstep (se 1 (by rfl) ⟨3319838, by rfl⟩ : syracuseStep 4426451 = 6639677) B6639677
theorem B2950967 : Blo 1965435 2950967 := bstep (se 1 (by rfl) ⟨2213225, by rfl⟩ : syracuseStep 2950967 = 4426451) B4426451
theorem B1967311 : Blo 1965435 1967311 := bstep (se 1 (by rfl) ⟨1475483, by rfl⟩ : syracuseStep 1967311 = 2950967) B2950967
theorem B2950973 : Blo 1965435 2950973 := bbase (se 3 (by rfl) ⟨553307, by rfl⟩ : syracuseStep 2950973 = 1106615) (by norm_num)
theorem B1967315 : Blo 1965435 1967315 := bstep (se 1 (by rfl) ⟨1475486, by rfl⟩ : syracuseStep 1967315 = 2950973) B2950973
theorem B4426469 : Blo 1965435 4426469 := bbase (se 4 (by rfl) ⟨414981, by rfl⟩ : syracuseStep 4426469 = 829963) (by norm_num)
theorem B2950979 : Blo 1965435 2950979 := bstep (se 1 (by rfl) ⟨2213234, by rfl⟩ : syracuseStep 2950979 = 4426469) B4426469
theorem B1967319 : Blo 1965435 1967319 := bstep (se 1 (by rfl) ⟨1475489, by rfl⟩ : syracuseStep 1967319 = 2950979) B2950979
theorem B4979789 : Blo 1965435 4979789 := bbase (se 3 (by rfl) ⟨933710, by rfl⟩ : syracuseStep 4979789 = 1867421) (by norm_num)
theorem B3319859 : Blo 1965435 3319859 := bstep (se 1 (by rfl) ⟨2489894, by rfl⟩ : syracuseStep 3319859 = 4979789) B4979789
theorem B2213239 : Blo 1965435 2213239 := bstep (se 1 (by rfl) ⟨1659929, by rfl⟩ : syracuseStep 2213239 = 3319859) B3319859
theorem B2950985 : Blo 1965435 2950985 := bstep (se 2 (by rfl) ⟨1106619, by rfl⟩ : syracuseStep 2950985 = 2213239) B2213239
theorem B1967323 : Blo 1965435 1967323 := bstep (se 1 (by rfl) ⟨1475492, by rfl⟩ : syracuseStep 1967323 = 2950985) B2950985
theorem B2100853 : Blo 1965435 2100853 := bbase (se 5 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 2100853 = 196955) (by norm_num)
theorem B2801137 : Blo 1965435 2801137 := bstep (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) B2100853
theorem B3734849 : Blo 1965435 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B9959597 : Blo 1965435 9959597 := bstep (se 3 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 9959597 = 3734849) B3734849
theorem B6639731 : Blo 1965435 6639731 := bstep (se 1 (by rfl) ⟨4979798, by rfl⟩ : syracuseStep 6639731 = 9959597) B9959597
theorem B4426487 : Blo 1965435 4426487 := bstep (se 1 (by rfl) ⟨3319865, by rfl⟩ : syracuseStep 4426487 = 6639731) B6639731
theorem B2950991 : Blo 1965435 2950991 := bstep (se 1 (by rfl) ⟨2213243, by rfl⟩ : syracuseStep 2950991 = 4426487) B4426487
theorem B1967327 : Blo 1965435 1967327 := bstep (se 1 (by rfl) ⟨1475495, by rfl⟩ : syracuseStep 1967327 = 2950991) B2950991
theorem B2950997 : Blo 1965435 2950997 := bbase (se 9 (by rfl) ⟨8645, by rfl⟩ : syracuseStep 2950997 = 17291) (by norm_num)
theorem B1967331 : Blo 1965435 1967331 := bstep (se 1 (by rfl) ⟨1475498, by rfl⟩ : syracuseStep 1967331 = 2950997) B2950997
theorem B3642605 : Blo 1965435 3642605 := bbase (se 3 (by rfl) ⟨682988, by rfl⟩ : syracuseStep 3642605 = 1365977) (by norm_num)
theorem B2428403 : Blo 1965435 2428403 := bstep (se 1 (by rfl) ⟨1821302, by rfl⟩ : syracuseStep 2428403 = 3642605) B3642605
theorem B25902965 : Blo 1965435 25902965 := bstep (se 5 (by rfl) ⟨1214201, by rfl⟩ : syracuseStep 25902965 = 2428403) B2428403
theorem B17268643 : Blo 1965435 17268643 := bstep (se 1 (by rfl) ⟨12951482, by rfl⟩ : syracuseStep 17268643 = 25902965) B25902965
theorem B23024857 : Blo 1965435 23024857 := bstep (se 2 (by rfl) ⟨8634321, by rfl⟩ : syracuseStep 23024857 = 17268643) B17268643
theorem B30699809 : Blo 1965435 30699809 := bstep (se 2 (by rfl) ⟨11512428, by rfl⟩ : syracuseStep 30699809 = 23024857) B23024857
theorem B20466539 : Blo 1965435 20466539 := bstep (se 1 (by rfl) ⟨15349904, by rfl⟩ : syracuseStep 20466539 = 30699809) B30699809
theorem B13644359 : Blo 1965435 13644359 := bstep (se 1 (by rfl) ⟨10233269, by rfl⟩ : syracuseStep 13644359 = 20466539) B20466539
theorem B9096239 : Blo 1965435 9096239 := bstep (se 1 (by rfl) ⟨6822179, by rfl⟩ : syracuseStep 9096239 = 13644359) B13644359
theorem B6064159 : Blo 1965435 6064159 := bstep (se 1 (by rfl) ⟨4548119, by rfl⟩ : syracuseStep 6064159 = 9096239) B9096239
theorem B8085545 : Blo 1965435 8085545 := bstep (se 2 (by rfl) ⟨3032079, by rfl⟩ : syracuseStep 8085545 = 6064159) B6064159
theorem B5390363 : Blo 1965435 5390363 := bstep (se 1 (by rfl) ⟨4042772, by rfl⟩ : syracuseStep 5390363 = 8085545) B8085545
theorem B3593575 : Blo 1965435 3593575 := bstep (se 1 (by rfl) ⟨2695181, by rfl⟩ : syracuseStep 3593575 = 5390363) B5390363
theorem B4791433 : Blo 1965435 4791433 := bstep (se 2 (by rfl) ⟨1796787, by rfl⟩ : syracuseStep 4791433 = 3593575) B3593575
theorem B6388577 : Blo 1965435 6388577 := bstep (se 2 (by rfl) ⟨2395716, by rfl⟩ : syracuseStep 6388577 = 4791433) B4791433
theorem B4259051 : Blo 1965435 4259051 := bstep (se 1 (by rfl) ⟨3194288, by rfl⟩ : syracuseStep 4259051 = 6388577) B6388577
theorem B2839367 : Blo 1965435 2839367 := bstep (se 1 (by rfl) ⟨2129525, by rfl⟩ : syracuseStep 2839367 = 4259051) B4259051
theorem B7571645 : Blo 1965435 7571645 := bstep (se 3 (by rfl) ⟨1419683, by rfl⟩ : syracuseStep 7571645 = 2839367) B2839367
theorem B5047763 : Blo 1965435 5047763 := bstep (se 1 (by rfl) ⟨3785822, by rfl⟩ : syracuseStep 5047763 = 7571645) B7571645
theorem B13460701 : Blo 1965435 13460701 := bstep (se 3 (by rfl) ⟨2523881, by rfl⟩ : syracuseStep 13460701 = 5047763) B5047763
theorem B17947601 : Blo 1965435 17947601 := bstep (se 2 (by rfl) ⟨6730350, by rfl⟩ : syracuseStep 17947601 = 13460701) B13460701
theorem B11965067 : Blo 1965435 11965067 := bstep (se 1 (by rfl) ⟨8973800, by rfl⟩ : syracuseStep 11965067 = 17947601) B17947601
theorem B7976711 : Blo 1965435 7976711 := bstep (se 1 (by rfl) ⟨5982533, by rfl⟩ : syracuseStep 7976711 = 11965067) B11965067
theorem B5317807 : Blo 1965435 5317807 := bstep (se 1 (by rfl) ⟨3988355, by rfl⟩ : syracuseStep 5317807 = 7976711) B7976711
theorem B7090409 : Blo 1965435 7090409 := bstep (se 2 (by rfl) ⟨2658903, by rfl⟩ : syracuseStep 7090409 = 5317807) B5317807
theorem B4726939 : Blo 1965435 4726939 := bstep (se 1 (by rfl) ⟨3545204, by rfl⟩ : syracuseStep 4726939 = 7090409) B7090409
theorem B6302585 : Blo 1965435 6302585 := bstep (se 2 (by rfl) ⟨2363469, by rfl⟩ : syracuseStep 6302585 = 4726939) B4726939
theorem B4201723 : Blo 1965435 4201723 := bstep (se 1 (by rfl) ⟨3151292, by rfl⟩ : syracuseStep 4201723 = 6302585) B6302585
theorem B5602297 : Blo 1965435 5602297 := bstep (se 2 (by rfl) ⟨2100861, by rfl⟩ : syracuseStep 5602297 = 4201723) B4201723
theorem B7469729 : Blo 1965435 7469729 := bstep (se 2 (by rfl) ⟨2801148, by rfl⟩ : syracuseStep 7469729 = 5602297) B5602297
theorem B4979819 : Blo 1965435 4979819 := bstep (se 1 (by rfl) ⟨3734864, by rfl⟩ : syracuseStep 4979819 = 7469729) B7469729
theorem B3319879 : Blo 1965435 3319879 := bstep (se 1 (by rfl) ⟨2489909, by rfl⟩ : syracuseStep 3319879 = 4979819) B4979819
theorem B4426505 : Blo 1965435 4426505 := bstep (se 2 (by rfl) ⟨1659939, by rfl⟩ : syracuseStep 4426505 = 3319879) B3319879
theorem B2951003 : Blo 1965435 2951003 := bstep (se 1 (by rfl) ⟨2213252, by rfl⟩ : syracuseStep 2951003 = 4426505) B4426505
theorem B1967335 : Blo 1965435 1967335 := bstep (se 1 (by rfl) ⟨1475501, by rfl⟩ : syracuseStep 1967335 = 2951003) B2951003
theorem B2213257 : Blo 1965435 2213257 := bbase (se 2 (by rfl) ⟨829971, by rfl⟩ : syracuseStep 2213257 = 1659943) (by norm_num)
theorem B2951009 : Blo 1965435 2951009 := bstep (se 2 (by rfl) ⟨1106628, by rfl⟩ : syracuseStep 2951009 = 2213257) B2213257
theorem B1967339 : Blo 1965435 1967339 := bstep (se 1 (by rfl) ⟨1475504, by rfl⟩ : syracuseStep 1967339 = 2951009) B2951009
theorem B2129533 : Blo 1965435 2129533 := bbase (se 3 (by rfl) ⟨399287, by rfl⟩ : syracuseStep 2129533 = 798575) (by norm_num)
theorem B11357509 : Blo 1965435 11357509 := bstep (se 4 (by rfl) ⟨1064766, by rfl⟩ : syracuseStep 11357509 = 2129533) B2129533
theorem B15143345 : Blo 1965435 15143345 := bstep (se 2 (by rfl) ⟨5678754, by rfl⟩ : syracuseStep 15143345 = 11357509) B11357509
theorem B10095563 : Blo 1965435 10095563 := bstep (se 1 (by rfl) ⟨7571672, by rfl⟩ : syracuseStep 10095563 = 15143345) B15143345
theorem B26921501 : Blo 1965435 26921501 := bstep (se 3 (by rfl) ⟨5047781, by rfl⟩ : syracuseStep 26921501 = 10095563) B10095563
theorem B17947667 : Blo 1965435 17947667 := bstep (se 1 (by rfl) ⟨13460750, by rfl⟩ : syracuseStep 17947667 = 26921501) B26921501
theorem B47860445 : Blo 1965435 47860445 := bstep (se 3 (by rfl) ⟨8973833, by rfl⟩ : syracuseStep 47860445 = 17947667) B17947667
theorem B31906963 : Blo 1965435 31906963 := bstep (se 1 (by rfl) ⟨23930222, by rfl⟩ : syracuseStep 31906963 = 47860445) B47860445
theorem B42542617 : Blo 1965435 42542617 := bstep (se 2 (by rfl) ⟨15953481, by rfl⟩ : syracuseStep 42542617 = 31906963) B31906963
theorem B56723489 : Blo 1965435 56723489 := bstep (se 2 (by rfl) ⟨21271308, by rfl⟩ : syracuseStep 56723489 = 42542617) B42542617
theorem B37815659 : Blo 1965435 37815659 := bstep (se 1 (by rfl) ⟨28361744, by rfl⟩ : syracuseStep 37815659 = 56723489) B56723489
theorem B25210439 : Blo 1965435 25210439 := bstep (se 1 (by rfl) ⟨18907829, by rfl⟩ : syracuseStep 25210439 = 37815659) B37815659
theorem B16806959 : Blo 1965435 16806959 := bstep (se 1 (by rfl) ⟨12605219, by rfl⟩ : syracuseStep 16806959 = 25210439) B25210439
theorem B11204639 : Blo 1965435 11204639 := bstep (se 1 (by rfl) ⟨8403479, by rfl⟩ : syracuseStep 11204639 = 16806959) B16806959
theorem B7469759 : Blo 1965435 7469759 := bstep (se 1 (by rfl) ⟨5602319, by rfl⟩ : syracuseStep 7469759 = 11204639) B11204639
theorem B4979839 : Blo 1965435 4979839 := bstep (se 1 (by rfl) ⟨3734879, by rfl⟩ : syracuseStep 4979839 = 7469759) B7469759
theorem B6639785 : Blo 1965435 6639785 := bstep (se 2 (by rfl) ⟨2489919, by rfl⟩ : syracuseStep 6639785 = 4979839) B4979839
theorem B4426523 : Blo 1965435 4426523 := bstep (se 1 (by rfl) ⟨3319892, by rfl⟩ : syracuseStep 4426523 = 6639785) B6639785
theorem B2951015 : Blo 1965435 2951015 := bstep (se 1 (by rfl) ⟨2213261, by rfl⟩ : syracuseStep 2951015 = 4426523) B4426523
theorem B1967343 : Blo 1965435 1967343 := bstep (se 1 (by rfl) ⟨1475507, by rfl⟩ : syracuseStep 1967343 = 2951015) B2951015
theorem B2951021 : Blo 1965435 2951021 := bbase (se 3 (by rfl) ⟨553316, by rfl⟩ : syracuseStep 2951021 = 1106633) (by norm_num)
theorem B1967347 : Blo 1965435 1967347 := bstep (se 1 (by rfl) ⟨1475510, by rfl⟩ : syracuseStep 1967347 = 2951021) B2951021
theorem B4426541 : Blo 1965435 4426541 := bbase (se 3 (by rfl) ⟨829976, by rfl⟩ : syracuseStep 4426541 = 1659953) (by norm_num)
theorem B2951027 : Blo 1965435 2951027 := bstep (se 1 (by rfl) ⟨2213270, by rfl⟩ : syracuseStep 2951027 = 4426541) B4426541
theorem B1967351 : Blo 1965435 1967351 := bstep (se 1 (by rfl) ⟨1475513, by rfl⟩ : syracuseStep 1967351 = 2951027) B2951027
theorem B3151325 : Blo 1965435 3151325 := bbase (se 3 (by rfl) ⟨590873, by rfl⟩ : syracuseStep 3151325 = 1181747) (by norm_num)
theorem B8403533 : Blo 1965435 8403533 := bstep (se 3 (by rfl) ⟨1575662, by rfl⟩ : syracuseStep 8403533 = 3151325) B3151325
theorem B5602355 : Blo 1965435 5602355 := bstep (se 1 (by rfl) ⟨4201766, by rfl⟩ : syracuseStep 5602355 = 8403533) B8403533
theorem B3734903 : Blo 1965435 3734903 := bstep (se 1 (by rfl) ⟨2801177, by rfl⟩ : syracuseStep 3734903 = 5602355) B5602355
theorem B2489935 : Blo 1965435 2489935 := bstep (se 1 (by rfl) ⟨1867451, by rfl⟩ : syracuseStep 2489935 = 3734903) B3734903
theorem B3319913 : Blo 1965435 3319913 := bstep (se 2 (by rfl) ⟨1244967, by rfl⟩ : syracuseStep 3319913 = 2489935) B2489935
theorem B2213275 : Blo 1965435 2213275 := bstep (se 1 (by rfl) ⟨1659956, by rfl⟩ : syracuseStep 2213275 = 3319913) B3319913
theorem B2951033 : Blo 1965435 2951033 := bstep (se 2 (by rfl) ⟨1106637, by rfl⟩ : syracuseStep 2951033 = 2213275) B2213275
theorem B1967355 : Blo 1965435 1967355 := bstep (se 1 (by rfl) ⟨1475516, by rfl⟩ : syracuseStep 1967355 = 2951033) B2951033
theorem B17036405 : Blo 1965435 17036405 := bbase (se 5 (by rfl) ⟨798581, by rfl⟩ : syracuseStep 17036405 = 1597163) (by norm_num)
theorem B11357603 : Blo 1965435 11357603 := bstep (se 1 (by rfl) ⟨8518202, by rfl⟩ : syracuseStep 11357603 = 17036405) B17036405
theorem B7571735 : Blo 1965435 7571735 := bstep (se 1 (by rfl) ⟨5678801, by rfl⟩ : syracuseStep 7571735 = 11357603) B11357603
theorem B5047823 : Blo 1965435 5047823 := bstep (se 1 (by rfl) ⟨3785867, by rfl⟩ : syracuseStep 5047823 = 7571735) B7571735
theorem B3365215 : Blo 1965435 3365215 := bstep (se 1 (by rfl) ⟨2523911, by rfl⟩ : syracuseStep 3365215 = 5047823) B5047823
theorem B17947813 : Blo 1965435 17947813 := bstep (se 4 (by rfl) ⟨1682607, by rfl⟩ : syracuseStep 17947813 = 3365215) B3365215
theorem B23930417 : Blo 1965435 23930417 := bstep (se 2 (by rfl) ⟨8973906, by rfl⟩ : syracuseStep 23930417 = 17947813) B17947813
theorem B15953611 : Blo 1965435 15953611 := bstep (se 1 (by rfl) ⟨11965208, by rfl⟩ : syracuseStep 15953611 = 23930417) B23930417
theorem B21271481 : Blo 1965435 21271481 := bstep (se 2 (by rfl) ⟨7976805, by rfl⟩ : syracuseStep 21271481 = 15953611) B15953611
theorem B14180987 : Blo 1965435 14180987 := bstep (se 1 (by rfl) ⟨10635740, by rfl⟩ : syracuseStep 14180987 = 21271481) B21271481
theorem B9453991 : Blo 1965435 9453991 := bstep (se 1 (by rfl) ⟨7090493, by rfl⟩ : syracuseStep 9453991 = 14180987) B14180987
theorem B12605321 : Blo 1965435 12605321 := bstep (se 2 (by rfl) ⟨4726995, by rfl⟩ : syracuseStep 12605321 = 9453991) B9453991
theorem B33614189 : Blo 1965435 33614189 := bstep (se 3 (by rfl) ⟨6302660, by rfl⟩ : syracuseStep 33614189 = 12605321) B12605321
theorem B22409459 : Blo 1965435 22409459 := bstep (se 1 (by rfl) ⟨16807094, by rfl⟩ : syracuseStep 22409459 = 33614189) B33614189
theorem B14939639 : Blo 1965435 14939639 := bstep (se 1 (by rfl) ⟨11204729, by rfl⟩ : syracuseStep 14939639 = 22409459) B22409459
theorem B9959759 : Blo 1965435 9959759 := bstep (se 1 (by rfl) ⟨7469819, by rfl⟩ : syracuseStep 9959759 = 14939639) B14939639
theorem B6639839 : Blo 1965435 6639839 := bstep (se 1 (by rfl) ⟨4979879, by rfl⟩ : syracuseStep 6639839 = 9959759) B9959759
theorem B4426559 : Blo 1965435 4426559 := bstep (se 1 (by rfl) ⟨3319919, by rfl⟩ : syracuseStep 4426559 = 6639839) B6639839
theorem B2951039 : Blo 1965435 2951039 := bstep (se 1 (by rfl) ⟨2213279, by rfl⟩ : syracuseStep 2951039 = 4426559) B4426559
theorem B1967359 : Blo 1965435 1967359 := bstep (se 1 (by rfl) ⟨1475519, by rfl⟩ : syracuseStep 1967359 = 2951039) B2951039
theorem B2951045 : Blo 1965435 2951045 := bbase (se 4 (by rfl) ⟨276660, by rfl⟩ : syracuseStep 2951045 = 553321) (by norm_num)
theorem B1967363 : Blo 1965435 1967363 := bstep (se 1 (by rfl) ⟨1475522, by rfl⟩ : syracuseStep 1967363 = 2951045) B2951045
theorem B3319933 : Blo 1965435 3319933 := bbase (se 3 (by rfl) ⟨622487, by rfl⟩ : syracuseStep 3319933 = 1244975) (by norm_num)
theorem B4426577 : Blo 1965435 4426577 := bstep (se 2 (by rfl) ⟨1659966, by rfl⟩ : syracuseStep 4426577 = 3319933) B3319933
theorem B2951051 : Blo 1965435 2951051 := bstep (se 1 (by rfl) ⟨2213288, by rfl⟩ : syracuseStep 2951051 = 4426577) B4426577
theorem B1967367 : Blo 1965435 1967367 := bstep (se 1 (by rfl) ⟨1475525, by rfl⟩ : syracuseStep 1967367 = 2951051) B2951051
theorem B2213293 : Blo 1965435 2213293 := bbase (se 3 (by rfl) ⟨414992, by rfl⟩ : syracuseStep 2213293 = 829985) (by norm_num)
theorem B2951057 : Blo 1965435 2951057 := bstep (se 2 (by rfl) ⟨1106646, by rfl⟩ : syracuseStep 2951057 = 2213293) B2213293
theorem B1967371 : Blo 1965435 1967371 := bstep (se 1 (by rfl) ⟨1475528, by rfl⟩ : syracuseStep 1967371 = 2951057) B2951057
theorem B6639893 : Blo 1965435 6639893 := bbase (se 6 (by rfl) ⟨155622, by rfl⟩ : syracuseStep 6639893 = 311245) (by norm_num)
theorem B4426595 : Blo 1965435 4426595 := bstep (se 1 (by rfl) ⟨3319946, by rfl⟩ : syracuseStep 4426595 = 6639893) B6639893
theorem B2951063 : Blo 1965435 2951063 := bstep (se 1 (by rfl) ⟨2213297, by rfl⟩ : syracuseStep 2951063 = 4426595) B4426595
theorem B1967375 : Blo 1965435 1967375 := bstep (se 1 (by rfl) ⟨1475531, by rfl⟩ : syracuseStep 1967375 = 2951063) B2951063
theorem B2951069 : Blo 1965435 2951069 := bbase (se 3 (by rfl) ⟨553325, by rfl⟩ : syracuseStep 2951069 = 1106651) (by norm_num)
theorem B1967379 : Blo 1965435 1967379 := bstep (se 1 (by rfl) ⟨1475534, by rfl⟩ : syracuseStep 1967379 = 2951069) B2951069
theorem B4426613 : Blo 1965435 4426613 := bbase (se 5 (by rfl) ⟨207497, by rfl⟩ : syracuseStep 4426613 = 414995) (by norm_num)
theorem B2951075 : Blo 1965435 2951075 := bstep (se 1 (by rfl) ⟨2213306, by rfl⟩ : syracuseStep 2951075 = 4426613) B4426613
theorem B1967383 : Blo 1965435 1967383 := bstep (se 1 (by rfl) ⟨1475537, by rfl⟩ : syracuseStep 1967383 = 2951075) B2951075
theorem B4791557 : Blo 1965435 4791557 := bbase (se 4 (by rfl) ⟨449208, by rfl⟩ : syracuseStep 4791557 = 898417) (by norm_num)
theorem B12777485 : Blo 1965435 12777485 := bstep (se 3 (by rfl) ⟨2395778, by rfl⟩ : syracuseStep 12777485 = 4791557) B4791557
theorem B34073293 : Blo 1965435 34073293 := bstep (se 3 (by rfl) ⟨6388742, by rfl⟩ : syracuseStep 34073293 = 12777485) B12777485
theorem B45431057 : Blo 1965435 45431057 := bstep (se 2 (by rfl) ⟨17036646, by rfl⟩ : syracuseStep 45431057 = 34073293) B34073293
theorem B30287371 : Blo 1965435 30287371 := bstep (se 1 (by rfl) ⟨22715528, by rfl⟩ : syracuseStep 30287371 = 45431057) B45431057
theorem B40383161 : Blo 1965435 40383161 := bstep (se 2 (by rfl) ⟨15143685, by rfl⟩ : syracuseStep 40383161 = 30287371) B30287371
theorem B26922107 : Blo 1965435 26922107 := bstep (se 1 (by rfl) ⟨20191580, by rfl⟩ : syracuseStep 26922107 = 40383161) B40383161
theorem B17948071 : Blo 1965435 17948071 := bstep (se 1 (by rfl) ⟨13461053, by rfl⟩ : syracuseStep 17948071 = 26922107) B26922107
theorem B95723045 : Blo 1965435 95723045 := bstep (se 4 (by rfl) ⟨8974035, by rfl⟩ : syracuseStep 95723045 = 17948071) B17948071
theorem B63815363 : Blo 1965435 63815363 := bstep (se 1 (by rfl) ⟨47861522, by rfl⟩ : syracuseStep 63815363 = 95723045) B95723045
theorem B42543575 : Blo 1965435 42543575 := bstep (se 1 (by rfl) ⟨31907681, by rfl⟩ : syracuseStep 42543575 = 63815363) B63815363
theorem B28362383 : Blo 1965435 28362383 := bstep (se 1 (by rfl) ⟨21271787, by rfl⟩ : syracuseStep 28362383 = 42543575) B42543575
theorem B18908255 : Blo 1965435 18908255 := bstep (se 1 (by rfl) ⟨14181191, by rfl⟩ : syracuseStep 18908255 = 28362383) B28362383
theorem B12605503 : Blo 1965435 12605503 := bstep (se 1 (by rfl) ⟨9454127, by rfl⟩ : syracuseStep 12605503 = 18908255) B18908255
theorem B16807337 : Blo 1965435 16807337 := bstep (se 2 (by rfl) ⟨6302751, by rfl⟩ : syracuseStep 16807337 = 12605503) B12605503
theorem B11204891 : Blo 1965435 11204891 := bstep (se 1 (by rfl) ⟨8403668, by rfl⟩ : syracuseStep 11204891 = 16807337) B16807337
theorem B7469927 : Blo 1965435 7469927 := bstep (se 1 (by rfl) ⟨5602445, by rfl⟩ : syracuseStep 7469927 = 11204891) B11204891
theorem B4979951 : Blo 1965435 4979951 := bstep (se 1 (by rfl) ⟨3734963, by rfl⟩ : syracuseStep 4979951 = 7469927) B7469927
theorem B3319967 : Blo 1965435 3319967 := bstep (se 1 (by rfl) ⟨2489975, by rfl⟩ : syracuseStep 3319967 = 4979951) B4979951
theorem B2213311 : Blo 1965435 2213311 := bstep (se 1 (by rfl) ⟨1659983, by rfl⟩ : syracuseStep 2213311 = 3319967) B3319967
theorem B2951081 : Blo 1965435 2951081 := bstep (se 2 (by rfl) ⟨1106655, by rfl⟩ : syracuseStep 2951081 = 2213311) B2213311
theorem B1967387 : Blo 1965435 1967387 := bstep (se 1 (by rfl) ⟨1475540, by rfl⟩ : syracuseStep 1967387 = 2951081) B2951081
theorem B7469941 : Blo 1965435 7469941 := bbase (se 5 (by rfl) ⟨350153, by rfl⟩ : syracuseStep 7469941 = 700307) (by norm_num)
theorem B9959921 : Blo 1965435 9959921 := bstep (se 2 (by rfl) ⟨3734970, by rfl⟩ : syracuseStep 9959921 = 7469941) B7469941
theorem B6639947 : Blo 1965435 6639947 := bstep (se 1 (by rfl) ⟨4979960, by rfl⟩ : syracuseStep 6639947 = 9959921) B9959921
theorem B4426631 : Blo 1965435 4426631 := bstep (se 1 (by rfl) ⟨3319973, by rfl⟩ : syracuseStep 4426631 = 6639947) B6639947
theorem B2951087 : Blo 1965435 2951087 := bstep (se 1 (by rfl) ⟨2213315, by rfl⟩ : syracuseStep 2951087 = 4426631) B4426631
theorem B1967391 : Blo 1965435 1967391 := bstep (se 1 (by rfl) ⟨1475543, by rfl⟩ : syracuseStep 1967391 = 2951087) B2951087
theorem B2951093 : Blo 1965435 2951093 := bbase (se 5 (by rfl) ⟨138332, by rfl⟩ : syracuseStep 2951093 = 276665) (by norm_num)
theorem B1967395 : Blo 1965435 1967395 := bstep (se 1 (by rfl) ⟨1475546, by rfl⟩ : syracuseStep 1967395 = 2951093) B2951093
theorem B4979981 : Blo 1965435 4979981 := bbase (se 3 (by rfl) ⟨933746, by rfl⟩ : syracuseStep 4979981 = 1867493) (by norm_num)
theorem B3319987 : Blo 1965435 3319987 := bstep (se 1 (by rfl) ⟨2489990, by rfl⟩ : syracuseStep 3319987 = 4979981) B4979981
theorem B4426649 : Blo 1965435 4426649 := bstep (se 2 (by rfl) ⟨1659993, by rfl⟩ : syracuseStep 4426649 = 3319987) B3319987
theorem B2951099 : Blo 1965435 2951099 := bstep (se 1 (by rfl) ⟨2213324, by rfl⟩ : syracuseStep 2951099 = 4426649) B4426649
theorem B1967399 : Blo 1965435 1967399 := bstep (se 1 (by rfl) ⟨1475549, by rfl⟩ : syracuseStep 1967399 = 2951099) B2951099
theorem B2213329 : Blo 1965435 2213329 := bbase (se 2 (by rfl) ⟨829998, by rfl⟩ : syracuseStep 2213329 = 1659997) (by norm_num)
theorem B2951105 : Blo 1965435 2951105 := bstep (se 2 (by rfl) ⟨1106664, by rfl⟩ : syracuseStep 2951105 = 2213329) B2213329
theorem B1967403 : Blo 1965435 1967403 := bstep (se 1 (by rfl) ⟨1475552, by rfl⟩ : syracuseStep 1967403 = 2951105) B2951105
theorem B4201877 : Blo 1965435 4201877 := bbase (se 6 (by rfl) ⟨98481, by rfl⟩ : syracuseStep 4201877 = 196963) (by norm_num)
theorem B2801251 : Blo 1965435 2801251 := bstep (se 1 (by rfl) ⟨2100938, by rfl⟩ : syracuseStep 2801251 = 4201877) B4201877
theorem B3735001 : Blo 1965435 3735001 := bstep (se 2 (by rfl) ⟨1400625, by rfl⟩ : syracuseStep 3735001 = 2801251) B2801251
theorem B4980001 : Blo 1965435 4980001 := bstep (se 2 (by rfl) ⟨1867500, by rfl⟩ : syracuseStep 4980001 = 3735001) B3735001
theorem B6640001 : Blo 1965435 6640001 := bstep (se 2 (by rfl) ⟨2490000, by rfl⟩ : syracuseStep 6640001 = 4980001) B4980001
theorem B4426667 : Blo 1965435 4426667 := bstep (se 1 (by rfl) ⟨3320000, by rfl⟩ : syracuseStep 4426667 = 6640001) B6640001
theorem B2951111 : Blo 1965435 2951111 := bstep (se 1 (by rfl) ⟨2213333, by rfl⟩ : syracuseStep 2951111 = 4426667) B4426667
theorem B1967407 : Blo 1965435 1967407 := bstep (se 1 (by rfl) ⟨1475555, by rfl⟩ : syracuseStep 1967407 = 2951111) B2951111
theorem B2951117 : Blo 1965435 2951117 := bbase (se 3 (by rfl) ⟨553334, by rfl⟩ : syracuseStep 2951117 = 1106669) (by norm_num)
theorem B1967411 : Blo 1965435 1967411 := bstep (se 1 (by rfl) ⟨1475558, by rfl⟩ : syracuseStep 1967411 = 2951117) B2951117
theorem B4426685 : Blo 1965435 4426685 := bbase (se 3 (by rfl) ⟨830003, by rfl⟩ : syracuseStep 4426685 = 1660007) (by norm_num)
theorem B2951123 : Blo 1965435 2951123 := bstep (se 1 (by rfl) ⟨2213342, by rfl⟩ : syracuseStep 2951123 = 4426685) B4426685
theorem B1967415 : Blo 1965435 1967415 := bstep (se 1 (by rfl) ⟨1475561, by rfl⟩ : syracuseStep 1967415 = 2951123) B2951123
theorem B3320021 : Blo 1965435 3320021 := bbase (se 7 (by rfl) ⟨38906, by rfl⟩ : syracuseStep 3320021 = 77813) (by norm_num)
theorem B2213347 : Blo 1965435 2213347 := bstep (se 1 (by rfl) ⟨1660010, by rfl⟩ : syracuseStep 2213347 = 3320021) B3320021
theorem B2951129 : Blo 1965435 2951129 := bstep (se 2 (by rfl) ⟨1106673, by rfl⟩ : syracuseStep 2951129 = 2213347) B2213347
theorem B1967419 : Blo 1965435 1967419 := bstep (se 1 (by rfl) ⟨1475564, by rfl⟩ : syracuseStep 1967419 = 2951129) B2951129
theorem B4548325 : Blo 1965435 4548325 := bbase (se 4 (by rfl) ⟨426405, by rfl⟩ : syracuseStep 4548325 = 852811) (by norm_num)
theorem B6064433 : Blo 1965435 6064433 := bstep (se 2 (by rfl) ⟨2274162, by rfl⟩ : syracuseStep 6064433 = 4548325) B4548325
theorem B4042955 : Blo 1965435 4042955 := bstep (se 1 (by rfl) ⟨3032216, by rfl⟩ : syracuseStep 4042955 = 6064433) B6064433
theorem B2695303 : Blo 1965435 2695303 := bstep (se 1 (by rfl) ⟨2021477, by rfl⟩ : syracuseStep 2695303 = 4042955) B4042955
theorem B3593737 : Blo 1965435 3593737 := bstep (se 2 (by rfl) ⟨1347651, by rfl⟩ : syracuseStep 3593737 = 2695303) B2695303
theorem B4791649 : Blo 1965435 4791649 := bstep (se 2 (by rfl) ⟨1796868, by rfl⟩ : syracuseStep 4791649 = 3593737) B3593737
theorem B6388865 : Blo 1965435 6388865 := bstep (se 2 (by rfl) ⟨2395824, by rfl⟩ : syracuseStep 6388865 = 4791649) B4791649
theorem B4259243 : Blo 1965435 4259243 := bstep (se 1 (by rfl) ⟨3194432, by rfl⟩ : syracuseStep 4259243 = 6388865) B6388865
theorem B11357981 : Blo 1965435 11357981 := bstep (se 3 (by rfl) ⟨2129621, by rfl⟩ : syracuseStep 11357981 = 4259243) B4259243
theorem B7571987 : Blo 1965435 7571987 := bstep (se 1 (by rfl) ⟨5678990, by rfl⟩ : syracuseStep 7571987 = 11357981) B11357981
theorem B5047991 : Blo 1965435 5047991 := bstep (se 1 (by rfl) ⟨3785993, by rfl⟩ : syracuseStep 5047991 = 7571987) B7571987
theorem B3365327 : Blo 1965435 3365327 := bstep (se 1 (by rfl) ⟨2523995, by rfl⟩ : syracuseStep 3365327 = 5047991) B5047991
theorem B2243551 : Blo 1965435 2243551 := bstep (se 1 (by rfl) ⟨1682663, by rfl⟩ : syracuseStep 2243551 = 3365327) B3365327
theorem B2991401 : Blo 1965435 2991401 := bstep (se 2 (by rfl) ⟨1121775, by rfl⟩ : syracuseStep 2991401 = 2243551) B2243551
theorem B1994267 : Blo 1965435 1994267 := bstep (se 1 (by rfl) ⟨1495700, by rfl⟩ : syracuseStep 1994267 = 2991401) B2991401
theorem B5318045 : Blo 1965435 5318045 := bstep (se 3 (by rfl) ⟨997133, by rfl⟩ : syracuseStep 5318045 = 1994267) B1994267
theorem B3545363 : Blo 1965435 3545363 := bstep (se 1 (by rfl) ⟨2659022, by rfl⟩ : syracuseStep 3545363 = 5318045) B5318045
theorem B2363575 : Blo 1965435 2363575 := bstep (se 1 (by rfl) ⟨1772681, by rfl⟩ : syracuseStep 2363575 = 3545363) B3545363
theorem B3151433 : Blo 1965435 3151433 := bstep (se 2 (by rfl) ⟨1181787, by rfl⟩ : syracuseStep 3151433 = 2363575) B2363575
theorem B8403821 : Blo 1965435 8403821 := bstep (se 3 (by rfl) ⟨1575716, by rfl⟩ : syracuseStep 8403821 = 3151433) B3151433
theorem B5602547 : Blo 1965435 5602547 := bstep (se 1 (by rfl) ⟨4201910, by rfl⟩ : syracuseStep 5602547 = 8403821) B8403821
theorem B14940125 : Blo 1965435 14940125 := bstep (se 3 (by rfl) ⟨2801273, by rfl⟩ : syracuseStep 14940125 = 5602547) B5602547
theorem B9960083 : Blo 1965435 9960083 := bstep (se 1 (by rfl) ⟨7470062, by rfl⟩ : syracuseStep 9960083 = 14940125) B14940125
theorem B6640055 : Blo 1965435 6640055 := bstep (se 1 (by rfl) ⟨4980041, by rfl⟩ : syracuseStep 6640055 = 9960083) B9960083
theorem B4426703 : Blo 1965435 4426703 := bstep (se 1 (by rfl) ⟨3320027, by rfl⟩ : syracuseStep 4426703 = 6640055) B6640055
theorem B2951135 : Blo 1965435 2951135 := bstep (se 1 (by rfl) ⟨2213351, by rfl⟩ : syracuseStep 2951135 = 4426703) B4426703
theorem B1967423 : Blo 1965435 1967423 := bstep (se 1 (by rfl) ⟨1475567, by rfl⟩ : syracuseStep 1967423 = 2951135) B2951135
theorem B2951141 : Blo 1965435 2951141 := bbase (se 4 (by rfl) ⟨276669, by rfl⟩ : syracuseStep 2951141 = 553339) (by norm_num)
theorem B1967427 : Blo 1965435 1967427 := bstep (se 1 (by rfl) ⟨1475570, by rfl⟩ : syracuseStep 1967427 = 2951141) B2951141
theorem B2363585 : Blo 1965435 2363585 := bbase (se 2 (by rfl) ⟨886344, by rfl⟩ : syracuseStep 2363585 = 1772689) (by norm_num)
theorem B6302893 : Blo 1965435 6302893 := bstep (se 3 (by rfl) ⟨1181792, by rfl⟩ : syracuseStep 6302893 = 2363585) B2363585
theorem B8403857 : Blo 1965435 8403857 := bstep (se 2 (by rfl) ⟨3151446, by rfl⟩ : syracuseStep 8403857 = 6302893) B6302893
theorem B5602571 : Blo 1965435 5602571 := bstep (se 1 (by rfl) ⟨4201928, by rfl⟩ : syracuseStep 5602571 = 8403857) B8403857
theorem B3735047 : Blo 1965435 3735047 := bstep (se 1 (by rfl) ⟨2801285, by rfl⟩ : syracuseStep 3735047 = 5602571) B5602571
theorem B2490031 : Blo 1965435 2490031 := bstep (se 1 (by rfl) ⟨1867523, by rfl⟩ : syracuseStep 2490031 = 3735047) B3735047
theorem B3320041 : Blo 1965435 3320041 := bstep (se 2 (by rfl) ⟨1245015, by rfl⟩ : syracuseStep 3320041 = 2490031) B2490031
theorem B4426721 : Blo 1965435 4426721 := bstep (se 2 (by rfl) ⟨1660020, by rfl⟩ : syracuseStep 4426721 = 3320041) B3320041
theorem B2951147 : Blo 1965435 2951147 := bstep (se 1 (by rfl) ⟨2213360, by rfl⟩ : syracuseStep 2951147 = 4426721) B4426721
theorem B1967431 : Blo 1965435 1967431 := bstep (se 1 (by rfl) ⟨1475573, by rfl⟩ : syracuseStep 1967431 = 2951147) B2951147
theorem B2213365 : Blo 1965435 2213365 := bbase (se 5 (by rfl) ⟨103751, by rfl⟩ : syracuseStep 2213365 = 207503) (by norm_num)
theorem B2951153 : Blo 1965435 2951153 := bstep (se 2 (by rfl) ⟨1106682, by rfl⟩ : syracuseStep 2951153 = 2213365) B2213365
theorem B1967435 : Blo 1965435 1967435 := bstep (se 1 (by rfl) ⟨1475576, by rfl⟩ : syracuseStep 1967435 = 2951153) B2951153
theorem C0 (j : ℕ) (h1 : 491358 ≤ j) (h2 : j ≤ 491858) : Blo 1965435 (4 * j + 3) := by
  interval_cases j
  · exact B1965435
  · exact B1965439
  · exact B1965443
  · exact B1965447
  · exact B1965451
  · exact B1965455
  · exact B1965459
  · exact B1965463
  · exact B1965467
  · exact B1965471
  · exact B1965475
  · exact B1965479
  · exact B1965483
  · exact B1965487
  · exact B1965491
  · exact B1965495
  · exact B1965499
  · exact B1965503
  · exact B1965507
  · exact B1965511
  · exact B1965515
  · exact B1965519
  · exact B1965523
  · exact B1965527
  · exact B1965531
  · exact B1965535
  · exact B1965539
  · exact B1965543
  · exact B1965547
  · exact B1965551
  · exact B1965555
  · exact B1965559
  · exact B1965563
  · exact B1965567
  · exact B1965571
  · exact B1965575
  · exact B1965579
  · exact B1965583
  · exact B1965587
  · exact B1965591
  · exact B1965595
  · exact B1965599
  · exact B1965603
  · exact B1965607
  · exact B1965611
  · exact B1965615
  · exact B1965619
  · exact B1965623
  · exact B1965627
  · exact B1965631
  · exact B1965635
  · exact B1965639
  · exact B1965643
  · exact B1965647
  · exact B1965651
  · exact B1965655
  · exact B1965659
  · exact B1965663
  · exact B1965667
  · exact B1965671
  · exact B1965675
  · exact B1965679
  · exact B1965683
  · exact B1965687
  · exact B1965691
  · exact B1965695
  · exact B1965699
  · exact B1965703
  · exact B1965707
  · exact B1965711
  · exact B1965715
  · exact B1965719
  · exact B1965723
  · exact B1965727
  · exact B1965731
  · exact B1965735
  · exact B1965739
  · exact B1965743
  · exact B1965747
  · exact B1965751
  · exact B1965755
  · exact B1965759
  · exact B1965763
  · exact B1965767
  · exact B1965771
  · exact B1965775
  · exact B1965779
  · exact B1965783
  · exact B1965787
  · exact B1965791
  · exact B1965795
  · exact B1965799
  · exact B1965803
  · exact B1965807
  · exact B1965811
  · exact B1965815
  · exact B1965819
  · exact B1965823
  · exact B1965827
  · exact B1965831
  · exact B1965835
  · exact B1965839
  · exact B1965843
  · exact B1965847
  · exact B1965851
  · exact B1965855
  · exact B1965859
  · exact B1965863
  · exact B1965867
  · exact B1965871
  · exact B1965875
  · exact B1965879
  · exact B1965883
  · exact B1965887
  · exact B1965891
  · exact B1965895
  · exact B1965899
  · exact B1965903
  · exact B1965907
  · exact B1965911
  · exact B1965915
  · exact B1965919
  · exact B1965923
  · exact B1965927
  · exact B1965931
  · exact B1965935
  · exact B1965939
  · exact B1965943
  · exact B1965947
  · exact B1965951
  · exact B1965955
  · exact B1965959
  · exact B1965963
  · exact B1965967
  · exact B1965971
  · exact B1965975
  · exact B1965979
  · exact B1965983
  · exact B1965987
  · exact B1965991
  · exact B1965995
  · exact B1965999
  · exact B1966003
  · exact B1966007
  · exact B1966011
  · exact B1966015
  · exact B1966019
  · exact B1966023
  · exact B1966027
  · exact B1966031
  · exact B1966035
  · exact B1966039
  · exact B1966043
  · exact B1966047
  · exact B1966051
  · exact B1966055
  · exact B1966059
  · exact B1966063
  · exact B1966067
  · exact B1966071
  · exact B1966075
  · exact B1966079
  · exact B1966083
  · exact B1966087
  · exact B1966091
  · exact B1966095
  · exact B1966099
  · exact B1966103
  · exact B1966107
  · exact B1966111
  · exact B1966115
  · exact B1966119
  · exact B1966123
  · exact B1966127
  · exact B1966131
  · exact B1966135
  · exact B1966139
  · exact B1966143
  · exact B1966147
  · exact B1966151
  · exact B1966155
  · exact B1966159
  · exact B1966163
  · exact B1966167
  · exact B1966171
  · exact B1966175
  · exact B1966179
  · exact B1966183
  · exact B1966187
  · exact B1966191
  · exact B1966195
  · exact B1966199
  · exact B1966203
  · exact B1966207
  · exact B1966211
  · exact B1966215
  · exact B1966219
  · exact B1966223
  · exact B1966227
  · exact B1966231
  · exact B1966235
  · exact B1966239
  · exact B1966243
  · exact B1966247
  · exact B1966251
  · exact B1966255
  · exact B1966259
  · exact B1966263
  · exact B1966267
  · exact B1966271
  · exact B1966275
  · exact B1966279
  · exact B1966283
  · exact B1966287
  · exact B1966291
  · exact B1966295
  · exact B1966299
  · exact B1966303
  · exact B1966307
  · exact B1966311
  · exact B1966315
  · exact B1966319
  · exact B1966323
  · exact B1966327
  · exact B1966331
  · exact B1966335
  · exact B1966339
  · exact B1966343
  · exact B1966347
  · exact B1966351
  · exact B1966355
  · exact B1966359
  · exact B1966363
  · exact B1966367
  · exact B1966371
  · exact B1966375
  · exact B1966379
  · exact B1966383
  · exact B1966387
  · exact B1966391
  · exact B1966395
  · exact B1966399
  · exact B1966403
  · exact B1966407
  · exact B1966411
  · exact B1966415
  · exact B1966419
  · exact B1966423
  · exact B1966427
  · exact B1966431
  · exact B1966435
  · exact B1966439
  · exact B1966443
  · exact B1966447
  · exact B1966451
  · exact B1966455
  · exact B1966459
  · exact B1966463
  · exact B1966467
  · exact B1966471
  · exact B1966475
  · exact B1966479
  · exact B1966483
  · exact B1966487
  · exact B1966491
  · exact B1966495
  · exact B1966499
  · exact B1966503
  · exact B1966507
  · exact B1966511
  · exact B1966515
  · exact B1966519
  · exact B1966523
  · exact B1966527
  · exact B1966531
  · exact B1966535
  · exact B1966539
  · exact B1966543
  · exact B1966547
  · exact B1966551
  · exact B1966555
  · exact B1966559
  · exact B1966563
  · exact B1966567
  · exact B1966571
  · exact B1966575
  · exact B1966579
  · exact B1966583
  · exact B1966587
  · exact B1966591
  · exact B1966595
  · exact B1966599
  · exact B1966603
  · exact B1966607
  · exact B1966611
  · exact B1966615
  · exact B1966619
  · exact B1966623
  · exact B1966627
  · exact B1966631
  · exact B1966635
  · exact B1966639
  · exact B1966643
  · exact B1966647
  · exact B1966651
  · exact B1966655
  · exact B1966659
  · exact B1966663
  · exact B1966667
  · exact B1966671
  · exact B1966675
  · exact B1966679
  · exact B1966683
  · exact B1966687
  · exact B1966691
  · exact B1966695
  · exact B1966699
  · exact B1966703
  · exact B1966707
  · exact B1966711
  · exact B1966715
  · exact B1966719
  · exact B1966723
  · exact B1966727
  · exact B1966731
  · exact B1966735
  · exact B1966739
  · exact B1966743
  · exact B1966747
  · exact B1966751
  · exact B1966755
  · exact B1966759
  · exact B1966763
  · exact B1966767
  · exact B1966771
  · exact B1966775
  · exact B1966779
  · exact B1966783
  · exact B1966787
  · exact B1966791
  · exact B1966795
  · exact B1966799
  · exact B1966803
  · exact B1966807
  · exact B1966811
  · exact B1966815
  · exact B1966819
  · exact B1966823
  · exact B1966827
  · exact B1966831
  · exact B1966835
  · exact B1966839
  · exact B1966843
  · exact B1966847
  · exact B1966851
  · exact B1966855
  · exact B1966859
  · exact B1966863
  · exact B1966867
  · exact B1966871
  · exact B1966875
  · exact B1966879
  · exact B1966883
  · exact B1966887
  · exact B1966891
  · exact B1966895
  · exact B1966899
  · exact B1966903
  · exact B1966907
  · exact B1966911
  · exact B1966915
  · exact B1966919
  · exact B1966923
  · exact B1966927
  · exact B1966931
  · exact B1966935
  · exact B1966939
  · exact B1966943
  · exact B1966947
  · exact B1966951
  · exact B1966955
  · exact B1966959
  · exact B1966963
  · exact B1966967
  · exact B1966971
  · exact B1966975
  · exact B1966979
  · exact B1966983
  · exact B1966987
  · exact B1966991
  · exact B1966995
  · exact B1966999
  · exact B1967003
  · exact B1967007
  · exact B1967011
  · exact B1967015
  · exact B1967019
  · exact B1967023
  · exact B1967027
  · exact B1967031
  · exact B1967035
  · exact B1967039
  · exact B1967043
  · exact B1967047
  · exact B1967051
  · exact B1967055
  · exact B1967059
  · exact B1967063
  · exact B1967067
  · exact B1967071
  · exact B1967075
  · exact B1967079
  · exact B1967083
  · exact B1967087
  · exact B1967091
  · exact B1967095
  · exact B1967099
  · exact B1967103
  · exact B1967107
  · exact B1967111
  · exact B1967115
  · exact B1967119
  · exact B1967123
  · exact B1967127
  · exact B1967131
  · exact B1967135
  · exact B1967139
  · exact B1967143
  · exact B1967147
  · exact B1967151
  · exact B1967155
  · exact B1967159
  · exact B1967163
  · exact B1967167
  · exact B1967171
  · exact B1967175
  · exact B1967179
  · exact B1967183
  · exact B1967187
  · exact B1967191
  · exact B1967195
  · exact B1967199
  · exact B1967203
  · exact B1967207
  · exact B1967211
  · exact B1967215
  · exact B1967219
  · exact B1967223
  · exact B1967227
  · exact B1967231
  · exact B1967235
  · exact B1967239
  · exact B1967243
  · exact B1967247
  · exact B1967251
  · exact B1967255
  · exact B1967259
  · exact B1967263
  · exact B1967267
  · exact B1967271
  · exact B1967275
  · exact B1967279
  · exact B1967283
  · exact B1967287
  · exact B1967291
  · exact B1967295
  · exact B1967299
  · exact B1967303
  · exact B1967307
  · exact B1967311
  · exact B1967315
  · exact B1967319
  · exact B1967323
  · exact B1967327
  · exact B1967331
  · exact B1967335
  · exact B1967339
  · exact B1967343
  · exact B1967347
  · exact B1967351
  · exact B1967355
  · exact B1967359
  · exact B1967363
  · exact B1967367
  · exact B1967371
  · exact B1967375
  · exact B1967379
  · exact B1967383
  · exact B1967387
  · exact B1967391
  · exact B1967395
  · exact B1967399
  · exact B1967403
  · exact B1967407
  · exact B1967411
  · exact B1967415
  · exact B1967419
  · exact B1967423
  · exact B1967427
  · exact B1967431
  · exact B1967435
theorem solution (m : ℕ) (hlo : 1965435 ≤ m) (hhi : m ≤ 1967435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 491358 ≤ j := by omega
    have hj2 : j ≤ 491858 := by omega
    have hb : Blo 1965435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
